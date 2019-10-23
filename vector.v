 Require Import Arith.

From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Coq.Program.Equality.

Require Import Notations.
Require Import Logic.


Inductive vector (A : Type) : nat -> Type :=
  |insert : forall (n : nat), A -> vector A n -> vector A (S n)
  |empty : vector A 0.

Compute vector_ind.


Definition case0 {A} (P: vector A 0 -> Type) (H:P (empty A)) v:P v :=
match v with
  |empty _ => H
  |_ => fun devil => False_ind (@IDProp) devil 
end.

Definition rect (A : Type) (P:forall {n}, vector A (S n) -> Type)
 (bas: forall (a : A){n} (v' : vector A (S n)), P v')
 (rect: forall a {n} (v: vector A (S n)) , P v -> P (insert a v)) : 
   forall {n} (v: vector A (S n)), P v.
 refine (fix rectS_fix {n} (v: vector A (S n)) {struct v} : P _ v :=
 match v in (vector _ (S n)) return P _ v with
 |@insert _ 0 a v' =>
   (match v' in vector _ 0 with
     |@empty _ => bas a _ _
     |@insert _ l _ _ => _
   end)
 |@insert _ (S nn') a v1 => _
 |_ => fun devil => False_ind (@IDProp) devil 
 end).

exact idProp.
exact (rect a _ v1 (rectS_fix _ v1)).
Defined.

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

Ltac unfold_to_leb_definition := unfold ">" in *; unfold "<" in *.

Definition rect_leb (A : Type) (P:forall {n} {y}, vector A (S n) -> y < S n -> Type)
 (out_of_gas: forall a {n} (H : 0 < (S (S n))) (v: vector A (S n)), P (insert a v) H) 
 (min_length : forall a (H : 0 < 1) (v: vector A 0), P (insert a v) H) 
 (rect: forall a {n} {y} (H : S y < (S (S n))) (v: vector A (S n)), P v (_leb' H) -> P (insert a v) H) : 
   forall {n} {y} (H : y < S n) (v: vector A (S n)), P v H.
 refine (fix rectS_fix {n} {y} (H : y < S n) (v: vector A (S n)) {struct v} : P _ _ v H :=
 (match v in vector _ (S n) return (forall (H : y < S n),  P n _ v H) with
 |@insert _ 0 a v' =>
   (match v' in vector _ 0 with
     |@empty _ => _
     |@insert _ l _ _ => _
   end)
 |@insert _ (S nn') a v1 => _
 |_ => fun devil => False_ind (@IDProp) devil 
 end) _).

exact idProp.
intros.
destruct y.
(*that's the fun case*)
refine (min_length a H0 (empty A)).
  have : ~ S _ < 1.
    case.
    move => // h.
    unfold_to_leb_definition; apply le_not_lt in h.
    assert (2 <= 2).
    auto with arith.
    tauto.
    cbv; intros.
    apply le_S_n in H1; apply le_not_lt in H1.
    assert(0 < S (S n1)).
    auto with arith.
    auto.
intros; destruct (x _ H0).
intros; destruct y.
refine (out_of_gas a _ H0 v1).
  have : y < S nn'.
  auto with arith.
move => H1.
refine (rect a _ _ H0 v1 (rectS_fix _ _ (_leb' H0) v1)).
Defined.


Definition rect_vector : forall {A} (P:forall {n} {y}, y <= n -> vector A (S n) -> Prop)
 (rect: forall a {n} {y} (v: vector A (S n)) (H : S y <= S n),
   P (le_S_n _ _ H) v -> P H (insert a v)), 
  forall {n} {y} (v: vector A (S n)) (H : y <= n), P H v.
move => T P f.
refine (fix fixed_ind_cons_vec (n y : nat) (v : vector T (S n)) (H : y <= n) 
  := _).


Admitted.


Definition vector_ind_with_leb : forall (A : Type) (P : forall n y: nat, y <= n -> vector A n -> Prop),
       (forall (n : nat) (y : nat) (H : S y <= S n) (a : A) (v : vector A n),
        P n y (le_S_n _ _ H) v -> P (S n) (S y) H (insert a v)) ->
       (forall (n : nat) (H : 0 <= S n) (a : A) (v : vector A n),
         P (S n) 0 H (insert a v)) ->     
        (forall (H : 0 <= 0), P 0 0 H (empty A)) -> forall (n : nat) (y : nat) (Heq : y <= n) (v : vector A n), P n y Heq v.

have : forall n, 0 <= S n -> 0 <= n.
auto with arith.

move => P' A P H K K'.
refine ( fix Ffix (x : nat) (y : nat) (Heq : y <= x) (x0 : vector _ x) {struct x0} : 
       P x y Heq x0 := _).

destruct x0.
destruct y.

refine (K n Heq a _).
refine (H n _ Heq a _ (Ffix _ y _ x0)).
destruct y.
refine (K' Heq).
inversion Heq.
Show Proof.
Defined.

Ltac vector_leb_induction v' H := elim/vector_ind_with_leb : v'/H; intros.

Example len_decrescing : forall {y : nat} {n : nat}, (S y) <= n -> y <= n.
elim => y.
move => H; apply : le_0_n.
move => /= H' w d.
auto with arith.
Qed.

Example vectorBiggerThan1Empty : forall {A} {y : nat} {n : nat}
   (h : vector A 0), ~ (S y) <= 0.
intros.
cbv; move => d.
set absurd := (le_0_n (S y)).
apply le_not_gt in d.
auto with arith.
Qed.

Theorem less_0_false : forall x, ~ S x <= 0. auto with arith. Qed.

Fixpoint cut {A}{n}{y} (x : vector A n) (len : y <= n) : vector A y.
  destruct y.
  constructor.
  destruct x.
  refine (insert a (cut _ _ _ x _)).
  apply le_S_n in len.
  assumption.
  destruct (less_0_false len).
  Show Proof.
Defined.



Fixpoint set_value' {A}{n} (x : vector A (S n)) (u : nat) (v' : A) {struct x} : u < S n -> vector A (S n).
move => c'.
elim/rect_leb : x/c'.
intros.
refine (insert v' v).
intros.
refine (insert v' v).
intros.
refine (insert a (set_value' _ _ v _ v' (_leb' H))).
Defined.

Fixpoint get_value' {A}{n} (x : vector A (S n)) (u : nat) : u < S n -> A.
move => c'.
elim/rect_leb : x/c'.
intros; refine a.
intros; refine a.
intros; refine (get_value' _ _ v _ (_leb' H)).
Defined.

Fixpoint set_value {A}{n} (x : vector A n) (u : nat) (v' : A) {struct x} : vector A n :=
  match x with
    |insert a x => (if Nat.eqb n u then
      insert v' (set_value x u v') else insert a (set_value x u v'))
     |empty _ => empty A
 end.

Fixpoint get_value {A}{n} (x : vector A n) (u : nat) {struct x} : option A :=
  match x with
    |insert a x => (if Nat.eqb n u then
      Some a else (get_value x u))
     |empty _ => None
 end.

(*the induction scheme can lost some information, a "remember" tatic should solve this problem just use the induction before and pull over the arguments to intro*)

Ltac strong_memorization k name := let H := fresh "HeqIden" in remember k as Iden; move : H; rename Iden into name.

Fixpoint length {A}{n} (x : vector A n) :=
   match x with
     |insert _ x => S (length x)
     |empty _ => 0
   end.


Theorem sized_length_equal_length : forall {A} {n} (x : vector A n), length x = n.
move => A n; elim.
move => n0 a v H /=; rewrite H; move => //.
done.
Qed.


Fixpoint update_vector_correctly {A} n y v (x : vector A (S n)) (H : y < S n) : get_value' (set_value' x v H) H = v.
  intros.
  elim/rect_leb : x/H.
  intros; simpl in *; trivial.
  intros; elim/(@case0) : v0; simpl in *; trivial.
  intros; simpl; unfold ssr_have; trivial.
Qed.

  
