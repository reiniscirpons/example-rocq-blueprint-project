Require Import ssreflect ssrbool ssrfun.
From MyNaturals Require Import naturals functions.
From MyEven Require Import induction.

Section MyEven.

Definition even (n: MyNat): Prop :=
  exists m, n = my_mul two m.

Lemma even_SSn {n: MyNat}: even n -> even (succ (succ n)).
Proof.
  move => H; destruct H; rewrite H //=.
  rewrite my_add_n_Sm my_addC my_add_n_Sm -my_mul_2n_nn.
  by exists (succ x).
Qed.


Inductive evenI: MyNat -> Prop :=
| evenO: evenI zero
| evenSS: forall  {n: MyNat}, evenI n -> evenI (succ (succ n)).

Lemma evenI_SSn {n: MyNat}: evenI n <-> evenI (succ (succ n)).
Proof.
  apply conj => [/evenSS //=| H].
  inversion H; by exact H1.
Qed.
  
Fixpoint is_even (n: MyNat): bool :=
match n with
| zero => true
| succ n' => ~~ (is_even n')
end.


Lemma evenP {n: MyNat}: reflect (evenI n) (is_even n).
Proof.
  apply: (iffP idP); elim/pair_induction: n => [_ | H| n H0 _] //.
    by exact: evenO.
  move => /= H; apply/evenSS/H0/negbNE/H.
    by inversion H.
  move => /= H; inversion H. 
  by case: negPn => //; rewrite H0.
Qed.


Lemma evenE {n: MyNat}: even n <-> evenI n.
Proof.
  apply conj => [H|].
    apply /evenP; destruct H; rewrite H //=.
    elim x => [// | y H0]; rewrite -my_add_n_Sm //=; apply /negPn; by exact: H0.
  elim/pair_induction: n => [_ |H|n H0 H1 H2] //=.
    by exists zero => //=.
    by inversion H.
  by apply /even_SSn/H0/evenI_SSn/H2.
Qed.

Theorem main_theorem {n: MyNat}:
  (even n /\ evenI n /\ is_even n) \/
  (~even n /\ ~evenI n /\ ~~ is_even n).
Proof.
  move: (sumbool_of_bool (is_even n)) => H; case H => {}H; rewrite H //=.
    have: (evenI n) => [|H1].
      by apply (evenP H).
    left; apply conj.
      by apply evenE; exact H1.
    by apply conj => [|//=]; exact H1.
  have: ~ evenI n => [|H1].
    by apply negbT in H; move: H; apply contraNnot; exact: (introT evenP).
  right; apply conj.
    by apply (iffRLn evenE); exact: H1.
  by apply conj => [|//=]; exact H1.
Qed.

End MyEven.
