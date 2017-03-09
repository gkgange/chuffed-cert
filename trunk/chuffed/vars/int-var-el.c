#include <algorithm>
#include <chuffed/vars/int-var.h>
#include <chuffed/core/sat.h>

#include <chuffed/core/propagator.h>

IntVarEL::IntVarEL(const IntVar& other) :
		IntVar(other)
	, lit_min(INT_MIN)
	, lit_max(INT_MIN)
	, base_vlit(INT_MIN)
	, base_blit(INT_MIN)
	, uiv_no(-1) 
{
	initVals();
	initVLits();
	initBLits();
}

void IntVarEL::initVLits() {
	if (base_vlit != INT_MIN) return;
	initVals();
	if (lit_min == INT_MIN) { lit_min = min; lit_max = max; }

	base_vlit = 2*(sat.nVars()-lit_min);
	sat.newVar(lit_max-lit_min+1, ChannelInfo(var_id, 1, 0, lit_min));
	for (int i = lit_min; i <= lit_max; i++) {
		if (!indomain(i)) {
      sat.cEnqueue(getNELit(i), NULL);
#ifdef LOGGING
      sat.flags[var(getNELit(i))].no_log = true;
#endif
    }
	}
	if (isFixed()) {
    sat.cEnqueue(getEQLit(min), NULL);
#ifdef LOGGING
    sat.flags[var(getEQLit(min))].no_log = true;
#endif
  }
}

void IntVarEL::initBLits() {
	if (base_blit != INT_MIN) return;
	if (lit_min == INT_MIN) { lit_min = min; lit_max = max; }

	base_blit = 2*(sat.nVars()-lit_min)+1;
	sat.newVar(lit_max-lit_min+2, ChannelInfo(var_id, 1, 1, lit_min-1));
	for (int i = lit_min; i <= min; i++) {
    sat.cEnqueue(getGELit(i), NULL);
#ifdef LOGGING
    sat.flags[var(getGELit(i))].no_log = true;
#endif
  }
	for (int i = max; i <= lit_max; i++) {
    sat.cEnqueue(getLELit(i), NULL);
#ifdef LOGGING
    sat.flags[var(getLELit(i))].no_log = true;
#endif
  }
}

void IntVarEL::setVLearnable() {
	for (int i = lit_min; i <= lit_max; i++) {
		sat.flags[base_vlit/2+i].setLearnable(true);
		sat.flags[base_vlit/2+i].setUIPable(true);
	}
}

void IntVarEL::setBLearnable() {
	for (int i = lit_min; i <= lit_max+1; i++) {
		sat.flags[(base_blit-1)/2+i].setLearnable(true);
		sat.flags[(base_blit-1)/2+i].setUIPable(true);
	}
}

void IntVarEL::setVDecidable(bool b) {
	for (int i = lit_min; i <= lit_max; i++) {
		sat.flags[base_vlit/2+i].setDecidable(b);
	}
}

void IntVarEL::setBDecidable(bool b) {
	for (int i = lit_min; i <= lit_max+1; i++) {
		sat.flags[(base_blit-1)/2+i].setDecidable(b);
	}
}


Lit IntVarEL::getLit(int64_t v, int t) {
	if (v < lit_min) return toLit(1^(t&1));              // 1, 0, 1, 0
	if (v > lit_max) return toLit(((t-1)>>1)&1);     // 1, 0, 0, 1
	switch (t) {
		case 0: return getNELit(v);
		case 1: return getEQLit(v);
		case 2: return getGELit(v);
		case 3: return getLELit(v);
		default: NEVER;
	}
}

// Use when you've just set [x >= v]
inline void IntVarEL::channelMin(int v) {
	// Set [x >= v-1] to [x >= min+1] using [x >= i] \/ ![x >= v]
	// Set [x != v-1] to [x != min] using [x != i] \/ ![x >= v]
	Reason r(mk_reason(~getGELit(v)));
	for (int i = v-1; i > min; i--) {
		sat.cEnqueue(getGELit(i), r);
		if (vals[i]) sat.cEnqueue(getNELit(i), r);
	}
	assert(vals[min]);
	sat.cEnqueue(getNELit(min), r);
}

// Use when you've just set [x <= v]
inline void IntVarEL::channelMax(int v) {
	// Set [x <= v+1] to [x <= max-1] to using [x <= i] \/ ![x <= v]
	// Set [x != v+1] to [x != max] to using ![x = i] \/ ![x <= v]
	Reason r(mk_reason(~getLELit(v)));
	for (int i = v+1; i < max; i++) {
		sat.cEnqueue(getLELit(i), r);
		if (vals[i]) sat.cEnqueue(getNELit(i), r);
	}
	assert(vals[max]);
	sat.cEnqueue(getNELit(max), r);
}

// Use when you've just set [x = v]
inline void IntVarEL::channelFix(int v) {
	Reason r(mk_reason(getNELit(v)));
	if (min < v) {
		// Set [x >= v] using [x >= v] \/ ![x = v]
		sat.cEnqueue(getGELit(v), r);
		channelMin(v);
	}
	if (max > v) {
		// Set [x <= v] using [x <= v] \/ ![x = v]
		sat.cEnqueue(getLELit(v), r);
		channelMax(v);
	}
}

#if INT_DOMAIN_LIST
inline void IntVarEL::updateMin(int v, int i) {
	for (; v < i; ++v) {
		// Set [x >= v+1] using [x >= v+1] \/ [x <= v-1] \/ [x = v]
		Reason r(mk_reason(getLELit(v-1), getEQLit(v)));
		sat.cEnqueue(getGELit(v+1), r);
	}
	min = v; changes |= EVENT_C | EVENT_L;
}

inline void IntVarEL::updateMax(int v, int i) {
	for (; v > i; --v) {
		// Set [x <= v-1] using [x <= v-1] \/ [x >= v+1] \/ [x = v]
		Reason r(mk_reason(getGELit(v+1), getEQLit(v)));
		sat.cEnqueue(getLELit(v-1), r);
	}
	max = v; changes |= EVENT_C | EVENT_U;
}
#else
inline void IntVarEL::updateMin() {
	int v = min;
	while (!vals[v]) {
		// Set [x >= v+1] using [x >= v+1] \/ [x <= v-1] \/ [x = v]
		Reason r(mk_reason(getLELit(v-1), getEQLit(v)));
		sat.cEnqueue(getGELit(v+1), r);
		v++;
	}
	if (v > min) { min = v; changes |= EVENT_L; }
}

inline void IntVarEL::updateMax() {
	int v = max;
	while (!vals[v]) {
		// Set [x <= v-1] using [x <= v-1] \/ [x >= v+1] \/ [x = v]
		Reason r(mk_reason(getGELit(v+1), getEQLit(v)));
		sat.cEnqueue(getLELit(v-1), r);
		v--;
	}
	if (v < max) { max = v; changes |= EVENT_U; }
}
#endif

inline void IntVarEL::updateFixed() {
	if (isFixed()) {
		int v = min;
		// Set [x = v] using [x = v] \/ [x <= v-1] \/ [x >= v+1]
		Reason r(mk_reason(getLELit(v-1), getGELit(v+1)));
		sat.cEnqueue(getEQLit(v), r);
		changes |= EVENT_F;
	}
}

bool IntVarEL::setMin(int64_t v, Reason r, bool channel) {
	assert(setMinNotR(v));
	if (channel) sat.cEnqueue(getLit(v, 2), r);
	if (v > max) { assert(sat.confl); return false; }
	channelMin(v);
#if INT_DOMAIN_LIST
	int i;
	int j = vals_count;
	for (i = min; i < v; i = vals_list[2*i+1])
		--j;
	updateMin(v, i);
	vals_count = j;
#else
	min = v; changes |= EVENT_C | EVENT_L;
	updateMin();
#endif
	updateFixed();
	pushInQueue();
	return true;
}

bool IntVarEL::setMax(int64_t v, Reason r, bool channel) {
	assert(setMaxNotR(v));
	if (channel) sat.cEnqueue(getLit(v, 3), r);
	if (v < min) { assert(sat.confl); return false; }
	channelMax(v);
#if INT_DOMAIN_LIST
	int i;
	int j = vals_count;
	for (i = max; i > v; i = vals_list[2*i])
		--j;
	updateMax(v, i);
	vals_count = j;
#else
	max = v; changes |= EVENT_C | EVENT_U;
	updateMax();
#endif
	updateFixed();
	pushInQueue();
	return true;
}

bool IntVarEL::setVal(int64_t v, Reason r, bool channel) {
	assert(setValNotR(v));
	if (channel) sat.cEnqueue(getLit(v, 1), r);
	if (!indomain(v)) { assert(sat.confl); return false; }
	changes |= EVENT_C | EVENT_F;
	channelFix(v);
	if (min < v) { min = v; changes |= EVENT_L; }
	if (max > v) { max = v; changes |= EVENT_U; }
#if INT_DOMAIN_LIST
	vals_count = 1;
#endif
	pushInQueue();
	return true;
}

bool IntVarEL::remVal(int64_t v, Reason r, bool channel) {
	assert(remValNotR(v));
	assert(vals);
	if (channel) sat.cEnqueue(getLit(v, 0), r);
	if (isFixed()) { assert(sat.confl); return false; }
#if INT_DOMAIN_LIST
	if (v == min)
		updateMin(min, vals_list[2*min+1]);
	else if (v == max)
		updateMax(max, vals_list[2*max]);
	else {
		vals[v] = 0;
		vals_list[vals_list[2*v]*2+1] = vals_list[2*v+1];
		vals_list[vals_list[2*v+1]*2] = vals_list[2*v];
		changes |= EVENT_C;
	}
	--vals_count;
#else
	changes |= EVENT_C;
	vals[v] = 0;
	updateMin();
	updateMax();
#endif
	updateFixed();
	pushInQueue();
	return true;
}

Lit IntVarEL::createSetLit(vec<Lit>& head) {
	// lb, ub and holes, which together cause the conflict
	int lower_bound = lit_min;
	int upper_bound = lit_max;
	vec<int> holes;

	std::sort((Lit*) head, (Lit*) head + head.size());

	// process bounds lits first
	for (int i = 0; i < head.size(); i++) {
		ChannelInfo& ci = sat.c_info[var(head[i])];
		if (ci.val_type == 0) continue;
		int v = ci.val;
		if (sign(head[i])) {
			if (v < upper_bound) upper_bound = v;
		} else {
			if (v+1 > lower_bound) lower_bound = v+1;
		}
	}

	// process val lits
	for (int i = 0; i < head.size(); i++) {
		ChannelInfo& ci = sat.c_info[var(head[i])];
		if (ci.val_type == 1) continue;
		int v = ci.val;
		if (sign(head[i])) {
			if (v < lower_bound || v > upper_bound) continue;
			if (v == lower_bound) {
				lower_bound++; continue;
			}
			if (v == upper_bound) {
				upper_bound--; continue;
			}
			holes.push(v);
		} else {
			return getNELit(v);
		}
	}

	if (lower_bound > upper_bound) {
		printf("Domain wipeout??\n");
		assert(false);
	}

//	printf("lower_bound = %d, upper_bound = %d\n", lower_bound, upper_bound);
//	for (int i = 0; i < holes.size(); i++) printf("%d ", holes[i]); printf("\n");

	fflush(stdout);

	// Check cases where an original lit is sufficient

	if (lower_bound == lit_min && holes.size() == 0) {
		return getGELit(upper_bound+1);
	}
	if (upper_bound == lit_max && holes.size() == 0) {
		return getLELit(lower_bound-1);
	}

	// Create new lit that complements failure set

	Lit q = Lit(sat.getLazyVar(ci_null), true);
	sat.flags[var(q)].setUIPable(false);
	sat.flags[var(q)].setLearnable(false);

	vec<Lit> ps(2);
	ps[1] = ~q;

	if (lower_bound == lit_min) {
		// can use bounds lit for lower bound
		sat.addClause(getGELit(holes[0]), ~q);
		lower_bound = holes[0];
//		printf("GE: %d\n", holes[0]);
	}
	if (upper_bound == lit_max) {
		// can use bounds lit for upper bound
		sat.addClause(getLELit(holes.last()), ~q);
		upper_bound = holes.last();
//		printf("LE: %d\n", holes.last());
	}
	int j = 0;
	for (int i = lower_bound; i <= upper_bound; i++) {
		if (j < holes.size() && i == holes[j]) { j++; continue; }
		ps[0] = getNELit(i);
		sat.addClause(*Clause_new(ps), true);
//		printf("NE: %d\n", i);
	}

//	printf("New lit = %d\n", toInt(q));

	return q;
}



