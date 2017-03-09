#include <cstdlib>
#include <cstdio>
#include <vector>
#include <chuffed/support/vec.h>
#include <chuffed/core/sat-types.h>
#include <chuffed/core/logging.h>
#include <chuffed/core/sat.h>
#include <chuffed/primitives/primitives.h>

// #define CHECK_LOG

namespace logging {
unsigned int active_item = 0;
unsigned int infer_count = 0;

static unsigned int active_hint = 0;
vec<int> antecedents;
vec<int> temporaries;

struct ivar_ident {
  ivar_ident() : is_bound(false), sym("") { }
  ivar_ident(std::string _sym) : is_bound(true), sym(_sym) { }
  ivar_ident(const ivar_ident& o) : is_bound(o.is_bound), sym(o.sym) { }
  
  ivar_ident& operator=(const ivar_ident& o) {
    is_bound = o.is_bound;
    sym = o.sym;
    return *this;
  }
    
  bool is_bound;
  std::string sym;
};

static std::vector<ivar_ident> ivar_idents = std::vector<ivar_ident>();

static bool ivar_is_bound(int var_id) {
  return var_id < ivar_idents.size() && ivar_idents[var_id].is_bound;
}
static bool ivar_is_bound(IntVar* v) {
  return ivar_is_bound(v->var_id);
}

struct binding {
  binding(const std::string& sym, Lit l)
    : ident(sym), kind(B_Lit), lit(toInt(l)) { }
  binding(const std::string& sym, IntVar* v)
    : ident(sym), kind(B_Ivar), var(v) { }

  enum BKind { B_Lit, B_Ivar };
  std::string ident;
  BKind kind;
  union {
    int lit;
    IntVar* var;
  };
  int value;
};
static bool has_model = false;
static std::vector<binding> bindings;

FILE* log_file = stderr;
FILE* lit_file = stderr;

void save_model(void) {
  if(!so.logging && !so.log_solution)
    return;
  has_model = true;
  for(unsigned int ii = 0; ii < bindings.size(); ii++) {
    binding& b(bindings[ii]);
    if(b.kind == binding::B_Lit) {
      assert(sat.value(toLit(b.lit)) != l_Undef);
      b.value = (sat.value(toLit(b.lit)) != l_False);
    } else {
      assert(b.var->isFixed());
      b.value = b.var->getVal();
    }
  }
}

void log_model(void) {
  if(!so.logging && !so.log_solution)
    return;
  if(!has_model)
    return; 

  FILE* sol_file = fopen(so.solfile, "w");
  
  fprintf(sol_file, "[lit_True = 1");
  for(unsigned int ii = 0; ii < bindings.size(); ii++) {
    fprintf(sol_file, ", %s = %d", bindings[ii].ident.c_str(), bindings[ii].value);
  }
  fprintf(sol_file, "]");
  fclose(sol_file); 
}

void init(void) {
  if(!so.logging)
    return;

  log_file = fopen(so.logfile, "w");
  lit_file = fopen(so.litfile,"w");
}

void finalize(void) {
  if(so.logging || so.log_solution)
    log_model();

  if(!so.logging)
    return;

  // Output literal semantics   
  fprintf(lit_file, "1 [lit_True >= 1]\n");
  fprintf(lit_file, "2 [lit_True < 1]\n");
  for(int vi = 2; vi < sat.assigns.size(); vi++) {
    ChannelInfo& ci = sat.c_info[vi];
	  if (ci.cons_type == 1) {
      if(!ivar_is_bound(ci.cons_id)) {
//        fprintf(stderr, "WARNING: variable %d has no name.\n", ci.cons_id);
        if(toLbool(sat.assigns[vi]) == l_False) {
          fprintf(lit_file, "%d [lit_True >= 1]\n", vi+1); 
        } else if(toLbool(sat.assigns[vi]) == l_True) {
            fprintf(lit_file, "%d [lit_True < 1]\n", vi+1);
        }
        continue;
      }
      fprintf(lit_file, "%d [%s %s %d]\n", vi+1, ivar_idents[ci.cons_id].sym.c_str(), ci.val_type ? ">" : "=", ci.val);
      // fprintf(lit_file, "%d [v%d %s %d]\n", vi, vi+1, ci.val_type ? ">=" : "=", ci.val);
    }
  }
  
  fclose(log_file);
  fclose(lit_file);
}

inline void set_hint(unsigned int hint) {
  if(hint != active_hint) {
    if(hint) {
      fprintf(log_file, "c c%d\n", hint);
    } else {
      fprintf(log_file, "c -\n");
    }
    active_hint = hint;
  }
}

inline void log_lits(Clause* cl) {
  if(!so.logging)
    return;

  for(int ii = 0; ii < cl->size(); ii++) {
    Lit l((*cl)[ii]);
//    if(sat.flags[var(l)].no_log)
//      continue;
    fprintf(log_file, "%s%d ", sign(l) ? "" : "-", var(l)+1);
  }
}

int intro(Clause* cl) {
  if(!so.logging)
    return INT_MAX;

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
  if(!so.logging)
    return INT_MAX;
#ifdef CHECK_LOG
  assert(sat.value(l) != l_Undef);
  for(int ii = 1; ii < cl->size(); ii++) {
    assert(sat.value((*cl)[ii]) == l_False);
  }
#endif
  if(cl->temp_expl) {
#if 0
    (*cl)[0] = l;
    cl->ident = ++infer_count;
    temporaries.push(cl->ident);
#else
    if(cl->ident) {
      if((*cl)[0] == l)
        return cl->ident;
      // fprintf(log_file, "d %d\n", cl->ident);
      temporaries.push(cl->ident);
    }
    (*cl)[0] = l;
    cl->ident = ++infer_count; 
#endif
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
  if(!so.logging) {
    antecedents.clear();
    return INT_MAX;
  }
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
  if(!so.logging) {
    antecedents.clear();
    return INT_MAX;
  }
  int ident = log_resolve(cl, antecedents);

  for(int ii = 0; ii < temporaries.size(); ii++) {
    fprintf(log_file, "d %d\n", temporaries[ii]);
  }
  temporaries.clear();

  assert(antecedents.size() == 0);

  return ident;
}

void empty(vec<int>& antecedents) {
  if(!so.logging)
    return;

  fprintf(log_file, "%d 0 ", ++infer_count);
  for(int ii = 0; ii < antecedents.size(); ii++) {
    fprintf(log_file, "%d ", antecedents[ii]);
  }
  fprintf(log_file, "0\n");
}

void del(Clause* cl) {
  if(!so.logging)
    return;
  /*
  if(!cl->ident || cl->temp_expl)
    return;
    */
  if(!cl->ident)
    return;

  // fprintf(log_file, "d %d\n", cl->ident);
  temporaries.push(cl->ident);
  cl->ident = 0;
}

inline Clause* unit_clause(Lit l) {
  if(!so.logging)
    return NULL;
#ifdef CHECK_LOG
  assert(sat.value(l) == l_True);
#endif
  vec<Lit> ps; ps.push(l);
  Clause* r = Clause_new(ps);
  if(sat.reason[var(l)].d.type == 3)
    r->origin = sat.reason[var(l)].d.d2;
  else
    r->origin = 0;
  r->temp_expl = false;
  return r;
}

int unit(Lit l) {
  if(!so.logging)
    return INT_MAX;
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

void push_unit(vec<int>& ants, Lit l) {
  if(!so.logging)
    return;
//  if(sat.flags[var(l)].no_log)
//    return;
#ifdef CHECK_LOG
  assert(sat.value(l) == l_True);
#endif
  ants.push(unit(l));
};


void bind_ivar(int ivar_id, const std::string& sym) {
  if(!so.logging && !so.log_solution)
    return;

  bindings.push_back(binding(sym, engine.vars[ivar_id]));

  if(!so.logging)
    return;

  while(ivar_idents.size() <= ivar_id)
    ivar_idents.push_back(ivar_ident());
  ivar_idents[ivar_id] = ivar_ident(sym);
}

void bind_bvar(Lit l, const std::string& sym) {
  if(!so.logging && !so.log_solution)
    return;
  bindings.push_back(binding(sym, l));

  if(!so.logging)
    return;
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

bool eval_irt(int x, IntRelType r, int k) {
  switch(r) {
    case IRT_EQ: return x == k;
    case IRT_NE: return x != k;
    case IRT_LE: return x <= k;
    case IRT_LT: return x < k;
    case IRT_GE: return x >= k;
    case IRT_GT: return x > k;
    default: NEVER;
  }
  return false;
}

void bind_atom(Lit l, IntVar* v, IntRelType r, int k) {
  if(!so.logging)
    return;
  if(!ivar_is_bound(v)) {
    assert(v->isFixed());
    bind_bool(l, eval_irt(v->getVal(), r, k));
    return;
  }

  if(sign(l)) {
    fprintf(lit_file, "%d [%s %s %d]\n", var(l)+1, ivar_idents[v->var_id].sym.c_str(), irt_string[r], k);
  }  else {
    fprintf(lit_file, "%d [%s %s %d]\n", var(l)+1, ivar_idents[v->var_id].sym.c_str(), irt_string[!r], k);
  }
}

void bind_bool(Lit l, bool b) {
  if(!so.logging)
    return;

  fprintf(lit_file, "%d [lit_True %s 1]\n", var(l)+1, sign(l)^b ? "<" : ">=");
}

};
