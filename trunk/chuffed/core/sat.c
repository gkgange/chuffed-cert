#include <cstdio>
#include <algorithm>
#include <cassert>
#include <chuffed/core/options.h>
#include <chuffed/core/engine.h>
#include <chuffed/core/sat.h>
#include <chuffed/core/propagator.h>
#include <chuffed/mip/mip.h>
#include <chuffed/parallel/parallel.h>

#define PRINT_ANALYSIS 0

SAT sat;

cassert(sizeof(Lit) == 4);
#ifndef LOGGING
cassert(sizeof(Clause) == 4);
#else
cassert(sizeof(Clause) == 12);
#endif
cassert(sizeof(WatchElem) == 8);
cassert(sizeof(Reason) == 8);

//---------
// inline methods



inline void SAT::insertVarOrder(int x) {
	if (!order_heap.inHeap(x) && flags[x].decidable) order_heap.insert(x);
}

inline void SAT::setConfl(Lit p, Lit q) {
#ifdef LOGGING
  if(short_confl->ident) {
    logging::del(short_confl);
  }
#endif
	(*short_confl)[0] = p;
	(*short_confl)[1] = q;
	confl = short_confl;
}

inline void SAT::untrailToPos(vec<Lit>& t, int p) {
	int dl = decisionLevel();

	for (int i = t.size(); i-- > p; ) {
		int x = var(t[i]);
		assigns[x] = toInt(l_Undef);
#if PHASE_SAVING
		if (so.phase_saving >= 1 || (so.phase_saving == 1 && dl >= l0))
			polarity[x] = sign(t[i]);
#endif
		insertVarOrder(x);
	}
	t.resize(p);
}

//---------
// main methods


SAT::SAT() :
		lit_sort(trailpos)
	, pushback_time(0)
	, trail(1)
	, qhead(1,0)
	, rtrail(1)
	, confl(NULL)
	, var_inc(1)
	, cla_inc(1)
	, order_heap(VarOrderLt(activity))
	, bin_clauses(0)
	, tern_clauses(0)
	, long_clauses(0)
	, learnt_clauses(0)
	, propagations(0)
	, back_jumps(0)
	, nrestarts(0)
	, next_simp_db(100000)
	, clauses_literals(0)
	, learnts_literals(0)
	, max_literals(0)
	, tot_literals(0)
	, avg_depth(100)
	, confl_rate(1000)
	, ll_time(wallClockTime())
	, ll_inc(1)
	, learnt_len_el(10)
	, learnt_len_occ(MAX_SHARE_LEN,learnt_len_el*1000/MAX_SHARE_LEN)
{
	newVar(); enqueue(Lit(0,1));
	newVar(); enqueue(Lit(1,0));
	temp_sc = (SClause*) malloc(TEMP_SC_LEN * sizeof(int));
	short_expl = (Clause*) malloc(sizeof(Clause) + 3 * sizeof(Lit));
	short_confl = (Clause*) malloc(sizeof(Clause) + 2 * sizeof(Lit));
	short_expl->clearFlags();
  short_expl->temp_expl = 1;
	short_confl->clearFlags();
	short_confl->sz = 2;
}

SAT::~SAT() {
	for (int i = 0; i < clauses.size(); i++) free(clauses[i]);
	for (int i = 0; i < learnts.size(); i++) free(learnts[i]);
}

void SAT::init() {
	orig_cutoff = nVars();
	ivseen.growTo(engine.vars.size(), false);
}

int SAT::newVar(int n, ChannelInfo ci) {
	int s = assigns.size();

	watches  .growBy(n);
	watches  .growBy(n);
	assigns  .growBy(n, toInt(l_Undef));
	reason   .growBy(n, NULL);
	trailpos .growBy(n, -1);
	seen     .growBy(n, 0);
	activity .growBy(n, 0);
	polarity .growBy(n, 1);
	flags    .growBy(n, 7);

	for (int i = 0; i < n; i++) {
		c_info.push(ci);
		ci.val++;
		insertVarOrder(s+i);
	}

	return s;
}

int SAT::getLazyVar(ChannelInfo ci) {
	int v;
	if (var_free_list.size()) {
		v = var_free_list.last();
		var_free_list.pop();
		fprintf(stderr, "reuse %d\n", v);
		assert(assigns[v] == toInt(l_Undef));
		assert(watches[2*v].size() == 0);
		assert(watches[2*v+1].size() == 0);
		assert(num_used[v] == 0);
		c_info[v] = ci;
		activity[v] = 0;
		polarity[v] = 1;
		flags[v] = 7;
	} else {
		v = newVar(1, ci);
		num_used.push(0);
	}
//	flags[v].setDecidable(false);
	return v;
}

void SAT::removeLazyVar(int v) {
	return;
	ChannelInfo& ci = c_info[v];
	assert(assigns[v] == toInt(l_Undef));
	assert(watches[2*v].size() == 0);
	assert(watches[2*v+1].size() == 0);
	fprintf(stderr, "free %d\n", v);
	var_free_list.push(v);
	if (ci.cons_type == 1) {
		((IntVarLL*) engine.vars[ci.cons_id])->freeLazyVar(ci.val);
	} else if (ci.cons_type == 2) {
		engine.propagators[ci.cons_id]->freeLazyVar(ci.val);
	} else NEVER;
}

// FIXME: Special case this.
void SAT::addClause(Lit p, Lit q) {
	if (value(p) == l_True || value(q) == l_True) return;
#ifndef LOGGING
	if (value(p) == l_False && value(q) == l_False) {
		assert(false);
		TL_FAIL();
	}
	if (value(p) == l_False) {
		assert(decisionLevel() == 0);
		enqueue(q);
		return;
	}
	if (value(q) == l_False) {
		assert(decisionLevel() == 0);
		enqueue(p);
		return;
	}
	bin_clauses++;
	watches[toInt(~p)].push(q);
	watches[toInt(~q)].push(p);
#else
  vec<Lit> ps; ps.push(p); ps.push(q);
  addClause(*Clause_new(ps), false);
#endif
}

void SAT::addClause(vec<Lit>& ps, bool one_watch) {
	int i, j;
#ifndef LOGGING
	for (i = j = 0; i < ps.size(); i++) {
		if (value(ps[i]) == l_True) return;
		if (value(ps[i]) == l_Undef) ps[j++] = ps[i];
	}
	ps.resize(j);
	if (ps.size() == 0) {
		assert(false);
		TL_FAIL();
	}
#else
  j = 0;
  for (i = 0; i < ps.size(); i++) {
    if(value(ps[i]) == l_True) return;
    if(value(ps[i]) == l_Undef) std::swap(ps[j++], ps[i]);
  }
  if(j == 0) {
    assert(false);
    TL_FAIL();
  }
#endif
	addClause(*Clause_new(ps), one_watch);
}

void SAT::addClause(Clause& c, bool one_watch) {
	assert(c.size() > 0);
	if (c.size() == 1) {
		assert(decisionLevel() == 0);
		if (DEBUG) fprintf(stderr, "warning: adding length 1 clause!\n");
		if (value(c[0]) == l_False) TL_FAIL();
		if (value(c[0]) == l_Undef) enqueue(c[0]);
		free(&c);
		return;
	}
	if (!c.learnt) {
		if (c.size() == 2) bin_clauses++;
		else if (c.size() == 3) tern_clauses++;
		else long_clauses++;
	}

	// Mark lazy lits which are used
	if (c.learnt) for (int i = 0; i < c.size(); i++) incVarUse(var(c[i]));

#ifndef LOGGING
	if (c.size() == 2) {
		if (!one_watch) watches[toInt(~c[0])].push(c[1]);
		watches[toInt(~c[1])].push(c[0]);
		if (!c.learnt) free(&c);
		return;
	}
#endif
	if (!one_watch) watches[toInt(~c[0])].push(&c);
	watches[toInt(~c[1])].push(&c);
	if (c.learnt) learnts_literals += c.size();
	else            clauses_literals += c.size();
	if (c.learnt) learnts.push(&c);
	else            clauses.push(&c);
}

void SAT::removeClause(Clause& c) {
#ifdef LOGGING
  assert(!c.temp_expl);
  if(c.ident) {
    logging::del(&c);
  }
#endif
	assert(c.size() > 1);
	watches[toInt(~c[0])].remove(&c);
	watches[toInt(~c[1])].remove(&c);
	if (c.learnt) learnts_literals -= c.size();
	else          clauses_literals -= c.size();

	if (c.learnt) for (int i = 0; i < c.size(); i++) decVarUse(var(c[i]));

	free(&c);
}

void SAT::topLevelCleanUp() {
  assert(decisionLevel() == 0);

#ifndef LOGGING
	for (int i = rtrail[0].size(); i-- > 0; ) free(rtrail[0][i]);
	rtrail[0].clear();
#endif

	for (int i = 0; i < trail[0].size(); i++) {
#ifndef LOGGING
        seen[var(trail[0][i])] = true;
#else
        logging::unit(trail[0][i]);
#endif
        trailpos[var(trail[0][i])] = -1;
  }

	if (so.sat_simplify && propagations >= next_simp_db) simplifyDB();

	trail[0].clear();
	qhead[0] = 0;

}

void SAT::simplifyDB() {
	int i, j;
	for (i = j = 0; i < learnts.size(); i++) {
		if (simplify(*learnts[i])) removeClause(*learnts[i]);
		else learnts[j++] = learnts[i];
	}
  learnts.resize(j);
	next_simp_db = propagations + clauses_literals + learnts_literals;
}

bool SAT::simplify(Clause& c) {
#ifdef LOGGING
  if(so.logging)
    assert(c.ident);
#endif
	if (value(c[0]) == l_True) return true;
	if (value(c[1]) == l_True) return true;
	int i, j;
	for (i = j = 2; i < c.size(); i++) {
#ifndef LOGGING
		if (value(c[i]) == l_True) return true;
		if (value(c[i]) == l_Undef) c[j++] = c[i];
#else
    if (value(c[i]) == l_True) {
      logging::antecedents.clear();
      return true;
    }
    if (value(c[i]) == l_Undef)
      c[j++] = c[i];
    else if(so.logging)
      logging::antecedents.push(logging::unit(~c[i]));
#endif
	}
	c.sz = j;
#ifdef LOGGING
  if(so.logging) {
    if(logging::antecedents.size() > 0) {
      logging::antecedents.push(c.ident);
      c.ident = 0;
      logging::resolve(&c);
      assert(logging::antecedents.size() == 0);
    }
  }
#endif
	return false;
}


// Use cases:
// enqueue from decision   , value(p) = u  , r = NULL , channel
// enqueue from analyze    , value(p) = u  , r != NULL, channel
// enqueue from unit prop  , value(p) = u  , r != NULL, channel

void SAT::enqueue(Lit p, Reason r) {
	assert(value(p) == l_Undef);
	int v = var(p);
	assigns [v] = toInt(lbool(!sign(p)));
	trailpos[v] = engine.trailPos();
	reason  [v] = r;
	trail.last().push(p);
	ChannelInfo& ci = c_info[v];
	if (ci.cons_type == 1) engine.vars[ci.cons_id]->channel(ci.val, ci.val_type, sign(p));
}

// enqueue from FD variable, value(p) = u/f, r = ?, don't channel

void SAT::cEnqueue(Lit p, Reason r) {
	assert(value(p) != l_True);
	int v = var(p);
	if (value(p) == l_False) {
		if (so.lazy) {
			if (r == NULL) {
				assert(decisionLevel() == 0);
				setConfl();
			} else {
				confl = getConfl(r, p);
				(*confl)[0] = p;
			}
		} else setConfl();
		return;
	}
	assigns [v] = toInt(lbool(!sign(p)));
	trailpos[v] = engine.trailPos();
	reason  [v] = r;
	trail.last().push(p);
}


void SAT::aEnqueue(Lit p, Reason r, int l) {
	assert(value(p) == l_Undef);
	int v = var(p);
	assigns [v] = toInt(lbool(!sign(p)));
	trailpos[v] = engine.trail_lim[l]-1;
	reason  [v] = r;
	trail[l].push(p);
}

void SAT::btToLevel(int level) {
  if (decisionLevel() <= level) return;

	for (int l = trail.size(); l-- > level+1; ) {
		untrailToPos(trail[l], 0);
		for (int i = rtrail[l].size(); i--; ) {
#ifdef LOGGING
      logging::del(rtrail[l][i]);
#endif
			free(rtrail[l][i]);
		}
	}
  trail.resize(level+1);
	qhead.resize(level+1);
	rtrail.resize(level+1);

	engine.btToLevel(level);
	if (so.mip) mip->btToLevel(level);

}

void SAT::btToPos(int sat_pos, int core_pos) {
	untrailToPos(trail.last(), sat_pos);
	engine.btToPos(core_pos);
}


// Propagator methods:

bool SAT::propagate() {
	int num_props = 0;

	int& qhead = this->qhead.last();
	vec<Lit>& trail = this->trail.last();

	while (qhead < trail.size()) {
		num_props++;

		Lit p = trail[qhead++];          // 'p' is enqueued fact to propagate.
		vec<WatchElem>& ws = watches[toInt(p)];

		if (ws.size() == 0) continue;

		WatchElem *i, *j, *end;

		for (i = j = ws, end = i + ws.size(); i != end; ) {
			WatchElem& we = *i;
			switch (we.d.type) {
			case 1: {
				// absorbed binary clause
				*j++ = *i++;
				Lit q = toLit(we.d.d2);
				switch (toInt(value(q))) {
					case 0: enqueue(q, ~p); break;
					case -1:
						setConfl(q, ~p);
						qhead = trail.size();
						while (i < end) *j++ = *i++;
						break;
					default:;
				}
				continue;
			}
			case 2: {
				// wake up FD propagator
				*j++ = *i++;
				engine.propagators[we.d.d2]->wakeup(we.d.d1, 0);
				continue;
			}
			default:
				Clause& c = *we.pt;
				i++;

				// Check if already satisfied
				if (value(c[0]) == l_True || value(c[1]) == l_True) {
					*j++ = &c;
					continue;
				}

				Lit false_lit = ~p;

				// Make sure the false literal is data[1]:
				if (c[0] == false_lit) c[0] = c[1], c[1] = false_lit;

				// Look for new watch:
				for (int k = 2; k < c.size(); k++)
					if (value(c[k]) != l_False) {
						c[1] = c[k]; c[k] = false_lit;
						watches[toInt(~c[1])].push(&c);
						goto FoundWatch;
					}

				// Did not find watch -- clause is unit under assignment:
				*j++ = &c;
				if (value(c[0]) == l_False) {
					confl = &c;
					qhead = trail.size();
					while (i < end)	*j++ = *i++;
				} else {
					enqueue(c[0], &c);
				}
				FoundWatch:;
			}
		}
		ws.shrink(i-j);
	}
	propagations += num_props;

	return (confl == NULL);
}

struct activity_lt { bool operator() (Clause* x, Clause* y) { return x->activity() < y->activity(); } };
void SAT::reduceDB() {
  int i, j;

	std::sort((Clause**) learnts, (Clause**) learnts + learnts.size(), activity_lt());

  for (i = j = 0; i < learnts.size()/2; i++) {
		if (!locked(*learnts[i])) removeClause(*learnts[i]);
		else learnts[j++] = learnts[i];
  }
  for (; i < learnts.size(); i++) {
		learnts[j++] = learnts[i];
  }
  learnts.resize(j);

	if (so.verbosity >= 1) printf("%% Pruned %d learnt clauses\n", i-j);
}

void SAT::printStats() {
	fprintf(stderr, "%d SAT variables\n", nVars());
	fprintf(stderr, "%d orig bin clauses\n", bin_clauses);
	fprintf(stderr, "%d orig tern clauses\n", tern_clauses);
	fprintf(stderr, "%d orig long clauses (avg. len. %.2f)\n", long_clauses, long_clauses ? (double) (clauses_literals - 3*tern_clauses) / long_clauses : 0);
	fprintf(stderr, "%d learnt clauses (avg. len. %.2f)\n", learnts.size(), learnts.size() ? (double) learnts_literals / learnts.size() : 0);
	fprintf(stderr, "%lld SAT propagations\n", propagations);
	fprintf(stderr, "%lld back jumps\n", back_jumps);
	fprintf(stderr, "%lld natural restarts\n", nrestarts);
	if (so.ldsb) fprintf(stderr, "%.2f pushback time\n", pushback_time);
}


//-----
// Branching methods

bool SAT::finished() {
	assert(so.vsids);
	while (!order_heap.empty()) {
		int x = order_heap[0];
		if (!assigns[x] && flags[x].decidable) return false;
		order_heap.removeMin();
	}
	return true;
}

DecInfo* SAT::branch() {
	if (!so.vsids) return NULL;

	assert(!order_heap.empty());

	int next = order_heap.removeMin();

	assert(!assigns[next]);
	assert(flags[next].decidable);

	return new DecInfo(NULL, 2*next+polarity[next]);
}

//-----
// Parallel methods

void SAT::updateShareParam() {
	so.share_param = 16;
/*
	double bmax = so.bandwidth / so.num_threads;
	double bsum = 0;
//	printf("Update share param\n");
	double factor = learnt_len_el * (ll_inc-0.5);
	for (int i = 0; i < MAX_SHARE_LEN; i++) {
		double lps = learnt_len_occ[i]/factor*i;
//		printf("%.3f, ", lps);
		if (bsum + lps > bmax) {
			so.share_param = i-1 + (bmax - bsum) / lps;
			if (so.share_param < 1) so.share_param = 1;
			return;
		}
		bsum += lps;
	}
	so.share_param = MAX_SHARE_LEN;
//	if (rand()%100 == 0) printf("share param = %.1f\n", so.share_param);
*/
}
