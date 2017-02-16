#include <cstdlib>
#include <cstdio>
#include <vector>
#include <chuffed/support/vec.h>
#include <chuffed/core/sat-types.h>
#include <chuffed/core/logging.h>
#include <chuffed/core/sat.h>
#include <chuffed/primitives/primitives.h>

#define CHECK_LOG

namespace logging {
unsigned int active_item = 0;
unsigned int infer_count = 0;

static unsigned int active_hint;
vec<int> antecedents;
vec<int> temporaries;

static std::vector<std::string> ivar_idents = std::vector<std::string>();

FILE* log_file = stderr;
FILE* lit_file = stderr;

void init(void) {
  log_file = fopen("log.dres", "w");
  lit_file = fopen("log.lit","w");
}

void finalize(void) {
  // Output literal semantics   
  fprintf(lit_file, "1 [lit_True >= 1]\n");
  fprintf(lit_file, "2 [lit_True < 1]\n");
  for(int vi = 2; vi < sat.assigns.size(); vi++) {
    ChannelInfo& ci = sat.c_info[vi];
	  if (ci.cons_type == 1) {
      if(ci.cons_id >= ivar_idents.size()) {
        fprintf(stderr, "WARNING: variable %d has no name.\n", ci.cons_id);
        if(toLbool(sat.assigns[vi]) == l_True) {
          fprintf(lit_file, "%d [lit_True >= 1]\n", vi+1); 
        } else if(toLbool(sat.assigns[vi]) == l_False) {
            fprintf(lit_file, "%d [lit_True < 1]\n", vi+1);
        }
        continue;
      }
      fprintf(lit_file, "%d [%s %s %d]\n", vi+1, ivar_idents[ci.cons_id].c_str(), ci.val_type ? ">=" : "=", ci.val);
      // fprintf(lit_file, "%d [v%d %s %d]\n", vi, vi+1, ci.val_type ? ">=" : "=", ci.val);
    }
  }

  fclose(log_file);
  fclose(lit_file);
}

inline void set_hint(unsigned int hint) {
  if(hint != active_hint) {
    if(hint) {
      fprintf(log_file, "c %d\n", hint);
    } else {
      fprintf(log_file, "c -\n");
    }
    active_hint = hint;
  }
}

inline void log_lits(Clause* cl) {
  for(int ii = 0; ii < cl->size(); ii++) {
    Lit l((*cl)[ii]);
//    if(var(l) < 2)
//      continue;
    fprintf(log_file, "%s%d ", sign(l) ? "" : "-", var(l)+1);
  }
}

int intro(Clause* cl) {
  assert(!cl->temp_expl);
  if(cl->ident) {
    return cl->ident;
  }
  cl->ident = ++infer_count;

  set_hint(cl->origin);

  fprintf(log_file, "%d ", cl->ident);
  log_lits(cl);
  fprintf(log_file, "0 0\n");
  return cl->ident;
}

int infer(Lit l, Clause* cl) {
#ifdef CHECK_LOG
  assert(sat.value(l) != l_Undef);
  for(int ii = 1; ii < cl->size(); ii++) {
    assert(sat.value((*cl)[ii]) == l_False);
  }
#endif
  if(cl->temp_expl) {
    (*cl)[0] = l;
    cl->ident = ++infer_count;
    temporaries.push(cl->ident);
  } else if(cl->ident) {
#ifdef CHECK_LOG
    assert((*cl)[0] == l);
#endif
    return cl->ident;
  } else {
    cl->ident = ++infer_count;
  }
#ifdef CHECK_LOG
    assert((*cl)[0] == l);
#endif

  set_hint(cl->origin);

  fprintf(log_file, "%d ", cl->ident);
  log_lits(cl);
  fprintf(log_file, "0 0\n");
  return cl->ident;
}

int log_resolve(Clause* cl, vec<int>& antecedents) {
  cl->origin = 0;
  cl->ident = ++infer_count;

  fprintf(log_file, "%d ", cl->ident);
  log_lits(cl);
  fprintf(log_file, "0 ");
  for(int ii = 0; ii < antecedents.size(); ii++) {
    fprintf(log_file, "%d ", antecedents[ii]);
  }
  fprintf(log_file, "0\n");
  antecedents.clear();

  return cl->ident;
}

int resolve(Clause* cl) {
  int ident = log_resolve(cl, antecedents);

  for(int ii = 0; ii < temporaries.size(); ii++) {
    fprintf(log_file, "d %d\n", temporaries[ii]);
  }
  temporaries.clear();

  assert(antecedents.size() == 0);

  return ident;
}

void empty(vec<int>& antecedents) {
  fprintf(log_file, "%d 0 ", ++infer_count);
  for(int ii = 0; ii < antecedents.size(); ii++) {
    fprintf(log_file, "%d ", antecedents[ii]);
  }
  fprintf(log_file, "0\n");
}

void del(Clause* cl) {
  if(!cl->ident || cl->temp_expl)
    return;

  fprintf(log_file, "d %d\n", cl->ident);  
  cl->ident = 0;
}

inline Clause* unit_clause(Lit l) {
#ifdef CHECK_LOG
  assert(sat.value(l) == l_True);
#endif
  vec<Lit> ps; ps.push(l);
  Clause* r = Clause_new(ps);
  r->origin = 0;
  r->temp_expl = false;
  return r;
}

int unit(Lit l) {
#ifdef CHECK_LOG
  assert(sat.value(l) == l_True);
#endif

  Clause* r = sat.getExpl(l);
  if(!r) {
    r = unit_clause(l);
    sat.reason[var(l)] = r;
    return infer(l, r);
  } else if(r->size() > 1) {
    vec<int> ants;  
    ants.push(infer(l, r));
    for(int ii = 1; ii < r->size(); ii++) {
      ants.push(unit(~(*r)[ii]));
    }
    r = unit_clause(l);
    sat.reason[var(l)] = r;
    return log_resolve(r, ants);
  }
  return r->ident;
};

void bind_ivar(int ivar_id, const std::string& sym) {
  while(ivar_idents.size() <= ivar_id)
    ivar_idents.push_back("UNDEF");
  ivar_idents[ivar_id] = sym;
}

void bind_bvar(Lit l, const std::string& sym) {
  // Don't actually save; just write
  fprintf(lit_file, "%d [%s %s 1]\n", var(l)+1, sym.c_str(), sign(l) ? ">=" : "<");
}

const char* irt_string[] = {
	"=",    // IRT_EQ
	"!=",   // IRT_NE
	"<=",   // IRT_LE
	"<",    //IRT_LT
	">=",   // IRT_GE
	">"    // IRT_GT
};

void bind_atom(Lit l, IntVar* v, IntRelType r, int k) {
  if(sign(l)) {
    fprintf(lit_file, "%d [%s %s %d]\n", var(l)+1, ivar_idents[v->var_id].c_str(), irt_string[r], k);
  }  else {
    fprintf(lit_file, "%d [%s %s %d]\n", var(l)+1, ivar_idents[v->var_id].c_str(), irt_string[!r], k);
  }
}

};
