Require Import ssreflect ssrbool ssrfun.
From MyNaturals Require Import naturals.

Lemma pair_induction (P : MyNat -> Prop) :
  P zero -> P one ->
  (forall n, P n -> P (succ n) -> P (succ (succ n))) ->
  forall n, P n.
Proof.
  move => H0 H1 Hstep n.
  enough (P n /\ P (succ n)) by easy.
  elim n; intuition.
Qed.
