#ifndef __CPROOF_H__
#define __CPROOF_H__

#include "CTypes.h"
#include "Proof.h"

struct CProofTraverser : public ProofTraverser {
  void (*root_fun)(const int* c,int size);
  void (*chain_fun)(const int* cs,int size1,const int* xs,int size2);
  void (*deleted_fun)(int c);
  void (*done_fun)();
  void root(const vec<Lit>& c);
  void chain(const vec<ClauseId>& cs,const vec<Var>& xs);
  void deleted(ClauseId c);
  void done();
};

#endif
