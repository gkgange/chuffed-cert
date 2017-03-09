#ifndef CHUFFED_LOGGING_H
#define CHUFFED_LOGGING_H

#include <string>
#include <chuffed/support/vec.h>

namespace logging {

extern unsigned int active_item;
extern unsigned int next_inf_id;

};

#include <chuffed/core/sat-types.h>

namespace logging {

extern vec<int> antecedents;

void init(void);

int intro(Clause* cl);
int infer(Lit l, Clause* cl);
void push_unit(vec<int>& ants, Lit l);
int unit(Lit l);
void empty(vec<int>& ants);
int resolve(Clause* cl);
void del(Clause* cl);

void save_model(void);

void finalize(void);

// Variable naming
void bind_ivar(int ivar_id, const std::string& symbol);
void bind_bvar(Lit l, const std::string& symbol);
void bind_bool(Lit l, bool b);
// void bind_atom(Lit l, int ivar_id, IntRelType r, int k);
};

#endif
