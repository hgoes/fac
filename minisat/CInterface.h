#ifndef __CINTERFACE_H__
#define __CINTERFACE_H__

#include <stdbool.h>
#include "CTypes.h"

#ifdef __cplusplus
extern "C" {
#endif

  solver_t* solver_new();
  void solver_add_proof_log(solver_t* self,
                            void (*root_fun)(const lit_t* c,int size),
                            void (*chain_fun)(const int* cs,int size1,const int* xs,int size2),
                            void (*deleted_fun)(int c),
                            void (*done_fun)());
  int solver_new_var(solver_t* self);
  void solver_add_clause(solver_t* self,lit_t* lits,int size);
  bool solver_ok(solver_t* self);
  bool solver_solve(solver_t* self);
  bool solver_solve_with(solver_t* self,lit_t* assumps,int size);
  int solver_get_model(solver_t* self,int** arr);
#ifdef __cplusplus
}
#endif

#endif
