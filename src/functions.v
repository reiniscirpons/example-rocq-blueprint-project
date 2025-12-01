Require Import ssreflect ssrbool ssrfun.
From MyNaturals Require Import naturals.

Fixpoint my_add (n m: MyNat): MyNat :=
match n with
| zero => m
| succ n' => succ (my_add n' m)
end.

Lemma my_add_n_O {n: MyNat}: n = my_add n zero.
Proof.
  elim n => [|m H0] //=; by rewrite -H0.
Qed.

Lemma my_add_n_Sm {n m: MyNat}:
  succ (my_add n m) = my_add n (succ m).
Proof.
  elim n => [|x H]//=; by rewrite H.
Qed.

Lemma my_addC {n m: MyNat}: my_add n m = my_add m n.
Proof.
  elim n => [|x H0] //=.
    by exact: my_add_n_O.
  by rewrite -my_add_n_Sm H0.
Qed.
  

Fixpoint my_mul (n m: MyNat): MyNat :=
match n with
| zero => zero
| succ n' => my_add (my_mul n' m)  m
end.


Lemma my_mul_2n_nn {n: MyNat}: my_mul two n = my_add n n.
Proof.
  by [].
Qed.
