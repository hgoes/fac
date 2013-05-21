#include "Solver.h"
#include "CProof.h"

#include <iostream>

struct solver_t : public Solver {
};

extern "C" {

#include "CInterface.h"

  solver_t* solver_new() {
    return new solver_t();
  }
  void solver_add_proof_log(solver_t* self,
                            void (*root_fun)(const int* c,int size),
                            void (*chain_fun)(const int* cs,int size1,const int* xs,int size2),
                            void (*deleted_fun)(int c),
                            void (*done_fun)()) {
    CProofTraverser* trav = new CProofTraverser();
    trav->root_fun = root_fun;
    trav->chain_fun = chain_fun;
    trav->deleted_fun = deleted_fun;
    trav->done_fun = done_fun;
    Proof* proof = new Proof(*trav);
    self->proof = proof;
  }
  int solver_new_var(solver_t* self) {
    return self->newVar();
  }
  void solver_add_clause(solver_t* self,int* lits,int size) {
    vec<Lit> v((Lit*)lits,size);
    self->addClause(v);
    v.release();
  }
  bool solver_solve(solver_t* self) {
    return self->solve();
  }
  bool solver_solve_with(solver_t* self,int* assumps,int size) {
    vec<Lit> v((Lit*)assumps,size);
    bool res = self->solve(v);
    v.release();
    return res;
  }
  bool solver_ok(solver_t* self) {
    return self->okay();
  }
  int solver_get_model(solver_t* self,int** arr) {
    *arr = (int*)((lbool*)(self->model));
    return self->model.size();
  }
}
