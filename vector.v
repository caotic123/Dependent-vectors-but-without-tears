 Require Import Arith.

From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Coq.Program.Equality.

Require Import Notations.
Require Import Logic.
Require Import List.

Inductive vector (A : Type) : nat -> Type :=
  |insert : forall (n : nat), A -> vector A n -> vector A (S n)
  |empty : vector A 0.

Definition case0 {A} (P: vector A 0 -> Type) (H:P (empty A)) v:P v :=
match v with
  |empty _ => H
  |_ => fun devil => False_ind (@IDProp) devil 
end.

Definition rect (A : Type) (P:forall {n}, vector A (S n) -> Type)
 (bas: forall (a : A), P (insert a (empty _)))
 (rect: forall a {n} (v: vector A (S n)) , P v -> P (insert a v)) : 
   forall {n} (v: vector A (S n)), P v.
 refine (fix rectS_fix {n} (v: vector A (S n)) {struct v} : P _ v :=
 match v in (vector _ (S n)) return P _ v with
 |@insert _ 0 a v' =>
   (match v' in vector _ 0 with
     |@empty _ => bas a
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

Fixpoint cut' {A}{n}{y} (x : vector A (S n)) (len : y < S n) : vector A y.
  elim/rect_leb : x/len.
  intros;exact (empty _).
  intros;exact (empty _).
  intros;refine (insert a (cut' _ _ _ v (_leb' H))).
  Show Proof.
Defined.

(*cut a n+1 position vector*)
Fixpoint cut_list {A}{n}{y} (x : vector A (S n)) (len : y < S n) : list A.
  elim/rect_leb : x/len.
  intros.
  exact nil.
  intros;exact nil.
  intros;refine (cons a (cut_list _ _ _ v (_leb' H))).
  Show Proof.
Defined.

Lemma succ_eq_pred : forall n y, S n - S y = n - y.
    intros;elim/nat_double_ind : n/y.
    trivial.
    trivial.
    trivial.
Defined.

Fixpoint drop {A}{n}{y} (x : vector A (S n)) (len : y < S n) : vector A ((S n) - y).
  elim/rect_leb : x/len.
  intros.
  simpl.
  exact (insert a v).
  intros.
  exact (insert a (empty _)).
  intros.
  set (drop _ _ _ v (_leb' H)).
  rewrite (succ_eq_pred _ _).
  exact v0.
  Show Proof.
Defined.

Fixpoint to_list a n (x : vector a n) : list a :=
  match x with
    | insert x x0 => cons x (to_list x0)
    | empty _ => nil 
  end.

Fixpoint drop_list {A}{n}{y} (x : vector A (S n)) (len : y < S n) : list A.
  elim/rect_leb : x/len.
  intros.
  simpl.
  exact (to_list v).
  intros.
  exact nil.
  intros.
  set (drop_list _ _ _ v (_leb' H)).
  exact l.
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

Definition head : forall (A : Type) (n : nat) (x : vector A (S n)), A.
  intros.
  elim/rect : x.
  intros; exact a.
  intros; exact a.
  Show Proof.
Defined.

Definition head' := 
(fun (A : Type) (n : nat) (x : vector A (S n)) =>
 (fun
    (h : forall a : A,
                (fun (n0 : nat) (_ : vector A (S n0)) => A) 0
                  (insert a (empty A))) => rect h (fun a n0 (_ : vector A (S n0)) (_ : A) => a) x) id).


Fixpoint last (A : Type) (n : nat) (x : vector A (S n)) {struct x} : A.
elim/rect : x.
intros; exact a.
intros;refine (last _ _ v).
Defined.

Theorem conservation_last : forall A n (v : vector A (S n)) a, last v = last (insert a v).
intros.
elim/rect : v.
intros; simpl in *; trivial.
intros;simpl in *;trivial.
Defined.

Definition tail : forall (A : Type) (n : nat) (x : vector A (S n)), vector A n.
 intros.
 refine (match x in (vector _ n) with 
           |insert x y => _
           |empty _ => _
         end).
  exact y.
  apply idProp.
  Defined.

Fixpoint take {A}{n}{y} (x : vector A (S n)) (len : y < S n) : vector A (S y).
  elim/rect_leb : x/len.
  intros;exact (insert a (empty _)).
  intros;exact (insert a (empty _)).
  intros;refine (insert a (take _ _ _ v (_leb' H))).
  Show Proof.
Defined.
(*the behavouir of take is different of cut, the "cut" of take remains the nth 
  element found, take [1, 2, 3] of 1 returns [1, 2] in other hand cut using the 
  same paremeters returns [1]*, besides that take always returns a non-empty vector
  and cut not) *)

Theorem head_is_a_cut {A} n y (x : vector A (S n)) (H : y < S n) : get_value' x H = last (take x H).
  intros.
  elim/rect_leb : x/H.
  intros; simpl in *; trivial.
  intros; elim/@case0 : v; trivial.
  intros; simpl in *;unfold ssr_have.
  assumption.
Qed.

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

Fixpoint concat {A} n n' (x : vector A n) (y : vector A n') {struct x}: vector A (n + n').
induction x.
refine (insert a (concat _ _ _ x y)).
exact y.
Show Proof.
Defined.


Lemma identy_length_vec : forall A n, vector A (n + 0) -> vector A n.
intros.
rewrite (symmetry_nat _) in X.
rewrite (plus_O_n _) in X.
exact X.
Defined.

Lemma identy_length_vec_inv : forall A n, vector A n -> vector A (n + 0).
intros.
rewrite (symmetry_nat _).
simpl.
exact X.
Defined.

Theorem length_identy_concat : forall A n (x : vector A n) (y : vector A 0),
   length (concat x y) = n.
intros.
induction x.
simpl in *;auto with arith.
elim/@case0 : y;trivial.
Qed.

Definition size := List.length.

Theorem length_to_list : forall a n (x : vector a n), size (to_list x) = n.
  intros.
  induction x.
  simpl; auto with arith.
  auto with arith.
Qed.

Definition caseS' {A} {n : nat} (v : vector A (S n)) : forall (P : vector A (S n) -> Type)
  (H : forall h t, P (insert h t)), P v :=
  match v with
  | insert h t => fun P H => H h t
  | _ => fun devil => False_rect (@IDProp) devil
  end.

Definition vector_2ind {A B} (P:forall {n}, vector A n -> vector B n -> Type)
  (bas : P (empty _) (empty _)) (rect : forall {n v2} {v1 : vector A n} , P v1 v2 -> 
    forall a b, P (insert a v1) (insert b v2)) : forall {n} (v1 : vector A n), forall v2 : vector B n, P v1 v2.

  refine (fix rect2_fix {n} (v1 : vector A n) {struct v1}: forall v2 : vector B n, P n v1 v2 :=
  match v1 with
  | empty _ => fun v2 => case0 bas v2
  | @insert  _ h1 n' t1 => fun v2 => _
  end).

elim/@caseS' : v2.
intros.
refine (rect h1 t t1 (rect2_fix h1 t1 t) n' h).
Defined.

Theorem _vec_to_list : forall a n (x : vector a n) (y : vector a n),
  (to_list x) = (to_list y) -> x = y.
  move => a n x y.
  elim/@vector_2ind : x/y.
  trivial.
  intros.
  simpl in *;injection H0.
  move => I c.
  apply H in I;rewrite I;rewrite c.
  trivial.
Qed.

Theorem injection_vec_to_list' : forall a n (x : vector a n) (y : vector a n),
  x = y -> (to_list x) = (to_list y).
  intros; move : H.
  elim/@vector_2ind : x/y.
  trivial.
  intros;rewrite H0;trivial.
Qed.

Definition ind2_vector (A : Type) (P:forall {n} {m}, vector A n -> vector A m -> Type)
(*induction for two vectors that non-necessarily have the same length
  you should notice that this induction doesn't fit well for all cases of
  theorems of double vectors, because it's always halts in the cases :
     (empty, empty)
     (insert _ _, empty) or
     (empty _, insert _ _)
  this should be okay for a comparasion proof for example, but not proofs that still perfoming recursion in thouse cases *)

 (bas0: P (empty _) (empty _))
 (cons2 : forall n m (x : vector A n) (y : vector A m) a a', P x y -> 
    P (insert a x) (insert a' y))
 (cons' : forall n (x : vector A n) a, P (insert a x) (empty _))
 (cons'1 : forall n (y : vector A n) a, P (empty _) (insert a y)) : 
    forall {n} (v: vector A n) {m} (v' : vector A m), P v v'.
 refine (fix v_fix {n} (v: vector A n) {struct v} : forall {m} 
  (v' : vector A m), P _ _ v v' := _).
destruct v.
intros.
destruct v'.
refine (cons2 _ _  v v' a a0 (v_fix _ v _ v')).
refine (cons' _ v a).
intros.
destruct v'.
refine (cons'1 _ v' a).
refine bas0.
Defined.

Theorem injection_len_to_list : forall a n n' (x : vector a n) (y : vector a n'),
  (to_list x) = (to_list y) -> n = n'.
  move => a n n' x y.
  elim/ind2_vector : x/y.
  trivial.
  intros; simpl in *. injection H0; move => I'; set (H I').
  auto with arith.
  intros; inversion H.
  intros; inversion H.
Qed.

Theorem take_always_returns_non_empty_vector :
   forall {A} n y (x : vector A (S n)) (x' : vector A 0) (H : y < S n), ~  to_list (take x H) = to_list x'.
move => a n y x; elim/@case0.
move : x; elim/rect.
move => a0 H.
move => H'.
set (injection_len_to_list H').
inversion e.
move => a0 n0 v H K' vec_absurd.
set (injection_len_to_list vec_absurd).
inversion e.
Qed.

Theorem head_is_take2 : forall a n (I : 0 < S n) (x : vector a (S n)), 
  head x = head (take x I).
intros.
elim/rect_leb : x/I.
trivial.
intros; elim/@case0 : v; trivial.
intros; trivial.
Qed.

Theorem empty_vec_identy_concat : forall A n (x : vector A n) (y : vector A 0),
   concat y x = x.
move => A n x y.
elim/@case0 : y.
simpl in *.
trivial.
Qed.

Theorem empty_vec_identy_concat' : forall A n (x : vector A n) (y : vector A 0),
   to_list (concat x y) = to_list x.
move => A n x y.
elim/@case0 : y.
induction x.
simpl in *.
rewrite IHx; trivial.
trivial.
Qed.


Theorem pred_injectivity : forall A (a : A) 
   n (v : vector A n) v' a', insert a v = insert a' v' -> v = v' \/ a = a'.

intros.
(*god wish that injection H will given a simply a = a' -> v = v', but 
  it returns a sigma type :( so, this way is the more easy to prove injectiviy of vectors*)

pose (let get_v A n (v' : vector A (S n)) :=
   match v' in (vector _ (S n)) return (vector _ n) with
     |insert a v => v
   end in get_v A n).

constructor.

apply (@eq_rect _ (insert a v) (fun x => v = (v0 x)) eq_refl (insert a' v') H).
Qed.

Export ListNotations.

Theorem cut_drop_vec' : forall a n y (v : vector a (S n)) (I : y < S n), to_list v = 
    (cut_list v I) ++ [(get_value' v I)] ++ (drop_list v I)  .

intros.
elim/rect_leb : v/I.
simpl; trivial.
intros.
elim/@case0 : v.
simpl; trivial.
intros;simpl in *; unfold ssr_have; rewrite H0; trivial.
Qed.

Theorem cut_drop_set_vec' : forall a n y x (v : vector a (S n)) (I : y < S n), to_list (set_value' v x I) = 
    (cut_list v I) ++ [x] ++ (drop_list v I)  .

intros.
replace [x] with [(get_value' (set_value' v x I) I)].

elim/rect_leb : v/I.
intros;simpl; trivial.
intros.
elim/@case0 : v; simpl; trivial.
intros;simpl in *; unfold ssr_have; rewrite H0; trivial.
set (@update_vector_correctly a _ _ x v I).
symmetry in e.
rewrite <- e.
trivial.
Qed.

Fixpoint to_vector {A} (x : list A) {struct x} : vector A (size x).
induction x.
refine (empty _).
refine (insert a (to_vector _ x)).
Defined.

Theorem to_list_vector : forall a n (v : vector a n) (P : forall n, vector a n -> Prop),
 to_list (to_vector (to_list v)) = to_list v.

intros.
induction n.
elim/@case0 : v.
trivial.
  have : forall v, to_list (to_vector (to_list v)) = to_list v.
  intros.
  induction v0.
  simpl.
  rewrite IHv0; trivial.
  trivial.
move => H'.
rewrite H'.
apply : eq_refl.
Qed.

(*Theorem to_list_holds : forall a n m v (x : vector a n) (y : vector a m) (P : forall n, vector a n -> Prop),
 (P _ x -> P _ y) -> P _ (insert v x) -> P _ (insert v' x).
*)

Theorem to_list_holds : forall a n m (x : vector a n) (y : vector a m) (P : forall n, vector a n -> Prop),
 to_list x = to_list y -> P _ (to_vector (to_list x)) -> P _ (to_vector (to_list y)).

intros.
move : H H0.
elim/@ind2_vector : x/y.
trivial.
intros.
injection H0.
intros.
set (H H2).
simpl in *.
rewrite <- H2.
rewrite <- H3.
assumption.

intros.
inversion H.
intros.
inversion H.
Show Proof.
Qed.

Theorem to_list_holds2 : forall a n (x : vector a n)
  (P : forall n, vector a n -> Prop), P _ (to_vector (to_list x)) -> P _ x.

intros.

pose (~ P (size (to_list x)) (to_vector (to_list x))).
unfold "~" in P0.
pose ((to_vector (to_list x))).
have : (vector a (size (to_list x))).
Admitted.

Theorem empty_vec_identy_list : forall A n (x : vector A n) (y : vector A 0),
   to_list (concat x y) = to_list x.

constructor.
elim/@case0 : y.
induction x.
simpl.
rewrite -> IHx.
unfold concat in *.
admit.
simpl.
unfold identy_length_vec.
unfold eq_rect_r.
unfold eq_rect.
admit.

elim/@case0 : y.
induction x.
simpl in *.
trivial.
trivial.

Admitted.






