Require Import ssreflect ssrbool ssrfun.
From MyNaturals Require Import naturals functions.

Section MyPrime.
Definition my_prime (p: MyNat): Prop :=
  (* Note: Incorrect definition *)
  forall (x y: MyNat), p = my_mul x y -> x = one \/ y = one.
End MyPrime.
