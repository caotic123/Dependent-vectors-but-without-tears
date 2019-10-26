From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Coq.Program.Equality.
Require Import Arith.
Require Import Notations.
Require Import Logic.


Ltac vector_leb_induction v' H := elim/vector_ind_with_leb : v'/H; intros.

Example len_decrescing : forall {y : nat} {n : nat}, (S y) <= n -> y <= n.
elim => y.
move => H; apply : le_0_n.
move => /= H' w d.
auto with arith.
Qed.

Theorem less_0_false : forall x, ~ S x <= 0. auto with arith. Qed.

Ltac strong_memorization k name := let H := fresh "HeqIden" in remember k as Iden; move : H; rename Iden into name.

Lemma _leb : forall x y, x < S y -> x < (S (S y)).
move => x y.
elim.
auto with arith.
move => H' H0 H1.
unfold "<" in *.
constructor; move => //.
Qed.

Lemma _leb' : forall x y, S x < S y -> x < y.
auto with arith.
Qed.

Lemma succ_eq_pred : forall n y, S n - S y = n - y.
    intros;elim/nat_double_ind : n/y.
    trivial.
    trivial.
    trivial.
Defined.

Lemma symmetry_nat : forall x y : nat, (x + y)%nat = (y + x)%nat.
intros.
elim/nat_double_ind : x/y.
move => n //.
move => n' //.
move => /= n m h.
  have : forall n y : nat, (n + S y) % nat = S ((n + y)%nat).
  intros.
  induction n0.
  simpl in *.
  trivial.
  simpl in *.
  rewrite <- IHn0.
  trivial.

intros.
do 2 ! rewrite (x _ _).
rewrite h.
trivial.
Qed.

