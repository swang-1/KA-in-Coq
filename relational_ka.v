(* This file defines relational models and shows that they form a 
   Kleene algebra *)
Require Import theories.
Require Import facts.
From Coq Require Import Relations.
From Coq Require Import Bool.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Logic.PropExtensionality.

(* A relation over a type X takes in two values of type X and
   returns a Prop *)
Check relation.

(* Before constructing a kleene algebra over relational models, we need to 
   first define the various operations (union, composition, etc.) *)
Definition rel_union {X : Type} (R T : relation X) :=
  fun x y => R x y \/ T x y.

Definition rel_comp {X : Type} (R T : relation X) :=
  fun x y => exists z, R x z /\ T z y.

Definition rel_id (X : Type) : relation X :=
  fun x y => x = y.

Definition rel_null (X : Type) : relation X :=
  fun x y => False.

Fixpoint rel_pow {X : Type} (R : relation X) (n : nat) : relation X :=
  match n with
  | 0 => rel_id X
  | S n => rel_comp R (rel_pow R n)
  end.

Definition rel_star {X : Type} (R : relation X) :=
  fun x y => exists n, (rel_pow R n) x y.

(* Now can define a relational Kleene Algebra paremetrized by a type X.
   This represents the relational model of all relations over a set X. Note
   that this definition does not cover general relational models. Rather, the
   below defines the relational model consisting of ALL relations over a
   set X. *)
Definition relational_KA (X : Type) : kleene_algebra :=
  {|
    carrier := relation X ;
    sr_plus := rel_union ;
    sr_mul := rel_comp ;
    star := rel_star ;
    id := rel_id X ;
    null := rel_null X ; 
  |}.

Definition RKA (X : Type) := relational_KA X.

(* Below are the proofs that the necessary axioms hold. *)

(* Idempotent semiring axioms *)
Theorem rel_plus_assoc : forall (X : Type) (x y z : carrier (RKA X)), 
  x [+(RKA X)] (y [+(RKA X)] z) = (x [+RKA X] y) [+RKA X] z .
Proof.
  intros. unfold sr_plus. simpl. unfold rel_union. 
  repeat (apply functional_extensionality ; intros).
  apply propositional_extensionality. split ; apply or_assoc.
Qed.

Theorem rel_mul_assoc : forall (X : Type) (x y z : carrier (RKA X)),
  x [;(RKA X)] (y [;(RKA X)] z) = (x [;(RKA X)] y) [;(RKA X)] z.
Proof.
  intros. unfold sr_mul. simpl. unfold rel_comp.
  repeat (apply functional_extensionality ; intros).
  apply propositional_extensionality. split ; intros.
  - inversion H. destruct H0. inversion H1. destruct H2.
    exists x3. split. exists x2 ; easy. easy.
  - inversion H. destruct H0. inversion H0. destruct H2.
    exists x3. split. easy. exists x2. easy.
Qed.

Theorem rel_plus_comm : forall (X : Type) (x y : carrier (RKA X)),
  x [+(RKA X)] y = y [+(RKA X)] x.
Proof.
  intros. simpl. unfold rel_union.
  repeat (apply functional_extensionality ; intros).
  apply propositional_extensionality. split ; apply or_comm.
Qed.

Theorem rel_add_zero : forall (X : Type) (x : carrier (RKA X)),
  x [+(RKA X)] (null (RKA X)) = x.
Proof.
  intros. simpl. unfold rel_union. unfold rel_null. 
  repeat (apply functional_extensionality ; intros).
  apply propositional_extensionality. split ; intros.
  - destruct H. apply H. contradiction.
  - left. apply H.
Qed.

Theorem rel_idempotent : forall (X : Type) (x : carrier (RKA X)),
  x [+(RKA X)] x = x.
Proof.
  intros. simpl. unfold rel_union. 
  repeat (apply functional_extensionality ; intros).
  apply propositional_extensionality. split ; intros.
  - destruct H ; easy.
  - auto.
Qed.

Theorem rel_id_l : forall (X : Type) (x : carrier (RKA X)),
  ((id (RKA X)) [;(RKA X)] x) = x.
Proof.
  intros. simpl. unfold rel_comp. unfold rel_id.
  repeat (apply functional_extensionality ; intros).
  apply propositional_extensionality. split ; intros.
  - destruct H. destruct H. rewrite H. apply H0.
  - exists x0. split ; easy.
Qed.

Theorem rel_id_r : forall (X : Type) (x : carrier (RKA X)),
  (x [;(RKA X)] (id (RKA X))) = x.
Proof.
  intros. simpl. unfold rel_comp. unfold rel_id.
  repeat (apply functional_extensionality ; intros).
  apply propositional_extensionality. split ; intros.
  - inversion H. destruct H0. rewrite <- H1. apply H0.
  - exists x1. split ; easy.
Qed.

Theorem rel_null_l : forall (X : Type) (x : carrier (RKA X)),
  ((null (RKA X)) [;(RKA X)] x) = null (RKA X).
Proof.
  intros. simpl. unfold rel_comp. unfold rel_null.
  repeat (apply functional_extensionality ; intros).
  apply propositional_extensionality. split ; intros.
  - inversion H. destruct H0. apply H0.
  - contradiction.
Qed. 

Theorem rel_null_r : forall  (X : Type) (x : carrier (RKA X)),
  (x [;(RKA X)] (null (RKA X))) = null (RKA X).
Proof.
  intros. simpl. unfold rel_comp. unfold rel_null.
  repeat (apply functional_extensionality ; intros).
  apply propositional_extensionality. split ; intros.
  - inversion H. destruct H0. apply H1.
  - contradiction.
Qed.

Theorem rel_distr_l : forall (X : Type) (x y z : carrier (RKA X)), 
  (x [;(RKA X)] (y [+(RKA X)] z)) =  (x [;(RKA X)] y) [+(RKA X)] (x [;(RKA X)] z).
Proof.
  intros. simpl. unfold rel_comp. unfold rel_union.
  repeat (apply functional_extensionality ; intros).
  apply propositional_extensionality. split ; intros.
  - inversion H. destruct H0. destruct H1.
    + left. exists x2 ; easy.
    + right. exists x2 ; easy.
  - destruct H.
    + repeat destruct H. exists x2. split. easy. left ; easy.
    + repeat destruct H. exists x2. split. easy. right ; easy.
Qed. 

Theorem rel_distr_r : forall (X : Type) (x y z : carrier (RKA X)), 
  ((x [+(RKA X)] y) [;(RKA X)] z) =  (x [;(RKA X)] z) [+(RKA X)] (y [;(RKA X)] z).
Proof.
  intros. simpl. unfold rel_comp. unfold rel_union.
  repeat (apply functional_extensionality ; intros).
  apply propositional_extensionality. split ; intros.
  - repeat destruct H. 
    + left. exists x2. easy.
    + right. exists x2. easy.
  - destruct H.
    + repeat destruct H. exists x2. split. left. apply H. apply H0.
    + repeat destruct H. exists x2. split. right. apply H. apply H0.
Qed.

(* Star Axioms *)

(* A usefull lemma that says R <= T iff R is a subset of T *)
Lemma rel_le_inclusion : forall (X : Type) (R T : carrier (RKA X)),
  R [<= (RKA X)] T <-> inclusion X R T.
Proof.
  intros. split ; intros.
  - unfold inclusion. intros. unfold partial_order in H. rewrite <- H.
    simpl. unfold rel_union. left. apply H0.
  - unfold inclusion in H. unfold partial_order. simpl.
    repeat (apply functional_extensionality ; intros).
    apply propositional_extensionality. split ; intros.
    + unfold rel_union in H0. destruct H0. apply H. apply H0. apply H0.
    + unfold rel_union. right. apply H0.
Qed.

Theorem rel_star_1 : forall (X : Type) (x : carrier (RKA X)),
  (id (RKA X)) [+(RKA X)] (x [;(RKA X)] (x [*(RKA X)])) [<= (RKA X)] x [*(RKA X)].
Proof.
  intros. simpl. apply rel_le_inclusion. unfold inclusion. intros.
  unfold rel_union in H. unfold rel_star. destruct H.
  - exists 0. simpl. apply H.
  - unfold rel_comp in H. repeat destruct H. unfold rel_star in H0. destruct H0.
    exists (S x2). simpl. unfold rel_comp. exists x1. split ; easy.
Qed. 

Lemma rel_iter_x : forall (X : Type) (x : carrier (RKA X)) (n : nat),
  rel_comp (rel_pow x n) x = rel_comp x (rel_pow x n).
Proof.
  intros. repeat (apply functional_extensionality ; intros). 
  generalize dependent x0. generalize dependent x1. induction n.
  - simpl. specialize (rel_id_l X x) ; intros. simpl in H. rewrite H.
    specialize (rel_id_r X x) ; intros. simpl in H0. rewrite H0. reflexivity. 
  - intros. simpl. apply propositional_extensionality ; split ; intros.
    + specialize (rel_mul_assoc X x (rel_pow x n) x) ; intros. simpl in H0.
      rewrite <- H0 in H. inversion H. destruct H1. rewrite IHn in H2.
      exists x2. split ; easy.
    + inversion H. destruct H0. rewrite <- IHn in H1.
      specialize (rel_mul_assoc X x (rel_pow x n) x) ; intros. simpl in H2.
      rewrite <- H2. exists x2. split ; easy.
Qed. 

Theorem rel_star_2 : forall (X : Type) (x : carrier (RKA X)),
  (id (RKA X)) [+(RKA X)] ((x [*(RKA X)]) [;(RKA X)] x)  [<= (RKA X)] x [*(RKA X)].
Proof.
  intros. simpl. apply rel_le_inclusion. unfold inclusion ; intros.
  unfold rel_union in H. unfold rel_star. destruct H.
  - exists 0. simpl. apply H.
  - inversion H.  repeat destruct H0. exists (S x2). simpl. 
    rewrite <- rel_iter_x. exists x1. split ; easy.
Qed.

Lemma rel_transitive : forall (X : Type) (x y z : carrier (RKA X)),
  x [<= RKA X] y -> y [<= RKA X] z -> x [<= RKA X] z.
Proof.
  intros. apply rel_le_inclusion. apply rel_le_inclusion in H.
  apply rel_le_inclusion in H0. unfold inclusion in *. intros. 
  apply H0. apply H. apply H1.
Qed.

Lemma rel_mul_monotone_l : forall (X : Type) (x y z : carrier (RKA X)),
  x [<= RKA X] y -> z [;RKA X] x [<= RKA X] z [;RKA X] y.
Proof.
  intros. simpl. apply rel_le_inclusion. apply rel_le_inclusion in H.  
  unfold inclusion in *. intros. inversion H0. exists x1. split. apply H1.
  apply H. apply H1.
Qed.
  

Lemma star_3_helper : forall (X : Type) (a b x : carrier (RKA X)) (n : nat),
  b [+RKA X] (a [;RKA X] x) [<= (RKA X)] x  ->
  (rel_pow a (S n)) [; RKA X] b [<= (RKA X)] (a [;RKA X] x).
Proof.
  intros. induction n.
  - apply rel_le_inclusion. unfold inclusion. intros. simpl in H.
    specialize (rel_id_r X a) ; simpl ; intros.  simpl in H0. rewrite H1 in H0.
    destruct H0. exists x1. split. apply H0. apply rel_le_inclusion in H.
    unfold inclusion in H. apply H. left. apply H0.
  - assert (rel_pow a (S (S n)) [;RKA X] b = 
      a [;RKA X] rel_pow a (S n) [;RKA X] b).
      { simpl. reflexivity. } rewrite H0. clear H0. rewrite <- rel_mul_assoc.
    apply rel_transitive with (y := a [;RKA X] (a [;RKA X] x)).
      { apply rel_mul_monotone_l. apply IHn. }
    apply rel_mul_monotone_l. apply rel_le_inclusion. 
    apply rel_le_inclusion in H. unfold inclusion in *. intros. apply H.
    right. apply H0.
Qed.

Theorem rel_star_3 : forall (X : Type) (a b x : carrier (RKA X)),
  b [+(RKA X)] (a [;(RKA X)] x) [<= (RKA X)] x -> 
  (a [*(RKA X)]) [;(RKA X)] b [<= (RKA X)] x.
Proof.
  intros. simpl in *. apply rel_le_inclusion. apply rel_le_inclusion in H.
  unfold inclusion in *. intros. apply H. unfold rel_comp in H0.
  inversion H0. destruct H1. destruct H1. induction x2.
  - simpl in H1. destruct H1. left. easy.
  -  specialize (star_3_helper X a b x) ; intros.
     assert (b [+RKA X] (a [;RKA X] x) [ <= RKA X] x).
      { simpl. apply rel_le_inclusion. unfold inclusion. apply H. } 
     apply H3 with (n:=x2) in H4. right. apply rel_le_inclusion in H4.
     unfold inclusion in H4. apply H4. exists x1. split ; easy.
Qed. 

Lemma rel_mul_monotone_r : forall (X : Type) (x y z : carrier (RKA X)),
  x [<= RKA X] y -> x [;RKA X] z [<= RKA X] y [;RKA X] z.
Proof.
  intros. simpl. apply rel_le_inclusion. apply rel_le_inclusion in H.  
  unfold inclusion in *. intros. inversion H0. exists x1. split. apply H. 
  apply H1. apply H1.
Qed.

Lemma star_4_helper : forall (X : Type) (a b x : carrier (RKA X)) (n : nat),
  b [+RKA X] (x [;RKA X] a) [<= (RKA X)] x  ->
  (b [;RKA X] rel_pow a (S n)) [<= (RKA X)] (x [;RKA X] a).
Proof.
  intros. induction n.
  - apply rel_le_inclusion. unfold inclusion. intros. simpl in H.
    specialize (rel_id_r X a) ; simpl ; intros.  simpl in H0. rewrite H1 in H0.
    destruct H0. exists x1. split. apply rel_le_inclusion in H.
    unfold inclusion in H. apply H. left. apply H0. apply H0.
  - assert (b [;RKA X] rel_pow a (S (S n)) = 
      b [;RKA X] a [;RKA X] rel_pow a (S n)).
      { rewrite <- rel_mul_assoc. simpl. reflexivity. } rewrite H0. clear H0. 
    rewrite <- rel_mul_assoc. 
    assert (a [;RKA X] rel_pow a (S n) = rel_pow a (S n) [;RKA X] a).
      { assert (a [;RKA X] rel_pow a (S n) = rel_comp a (rel_pow a (S n))).
          { simpl. reflexivity. }
        assert (rel_pow a (S n) [;RKA X] a = rel_comp (rel_pow a (S n)) a).
          {  simpl. reflexivity. }
        rewrite H0. rewrite H1. rewrite <- rel_iter_x. reflexivity. }
    rewrite H0. rewrite rel_mul_assoc. 
    apply rel_transitive with (y := x [;RKA X] a [;RKA X] a).
      { apply rel_mul_monotone_r. apply IHn. }
    apply rel_mul_monotone_r. apply rel_le_inclusion. apply rel_le_inclusion in H.
    unfold inclusion in *. intros. apply H. right. apply H1.
Qed.

Theorem rel_star_4 : forall (X : Type) (a b x : carrier (RKA X)),
  b [+(RKA X)] (x [;(RKA X)] a) [<= (RKA X)] x -> 
  b [;(RKA X)] (a [*(RKA X)]) [<= (RKA X)] x.
Proof.
  intros. apply rel_le_inclusion. unfold inclusion. intros. simpl in H0.
  repeat destruct H0. destruct H1. induction x2.
  - simpl in H1. inversion H1. apply rel_le_inclusion in H. unfold inclusion in H.
    apply H. left. rewrite <- H2. apply H0.
  - specialize (star_4_helper X a b x x2). intros. specialize (H2 H). 
    apply rel_le_inclusion in H. unfold inclusion in H. apply H. right. 
    apply rel_le_inclusion in H2. unfold inclusion in H2. apply H2. simpl.
    exists x1. split. apply H0. simpl in H1. apply H1.
Qed.

Definition relational_KA_theory (X : Type) : kleene_algebra_theory (RKA X) :=
  {|
    (* Idempotent semiring axioms *)
    sr_plus_assoc := rel_plus_assoc X; 
    sr_mul_assoc := rel_mul_assoc X; 
    sr_plus_comm := rel_plus_comm X; 
    sr_add_zero := rel_add_zero X;
    sr_idempotent := rel_idempotent X;
    sr_id_l := rel_id_l X;
    sr_id_r := rel_id_r X; 
    sr_null_l := rel_null_l X; 
    sr_null_r := rel_null_r X;
    sr_distr_l := rel_distr_l X; 
    sr_distr_r := rel_distr_r X; 

    (* Star Axioms *)
    star_axiom_1 := rel_star_1 X; 
    star_axiom_2 := rel_star_2 X; 
    star_axiom_3 := rel_star_3 X; 
    star_axiom_4 := rel_star_4 X; 
  |}.

Definition RKAt (X : Type) := relational_KA_theory X.


