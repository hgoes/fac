#include "CProof.h"

void CProofTraverser::root(const vec<Lit>& c) {
  root_fun((const lit_t*)(&*c),c.size());
}

void CProofTraverser::chain(const vec<ClauseId>& cs,const vec<Var>& xs) {
  chain_fun(&*cs,cs.size(),&*xs,xs.size());
}

void CProofTraverser::deleted(ClauseId c) {
  deleted_fun(c);
}

void CProofTraverser::done() {
  done_fun();
}


