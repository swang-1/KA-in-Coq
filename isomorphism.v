Require Import theories.
Require Import facts.
Require Import relational_ka.
Require Import language_ka.
From Coq Require Import Strings.String.
From Coq Require Import Ensembles.
From Coq Require Import Relations.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Logic.PropExtensionality.

Definition surjective {A B : Type} (f : A -> B) :=
  forall (b : B), exists a, f a = b.

Definition injective {A B : Type} (f : A -> B) :=
  forall a1 a2, f a1 = f a2 -> a1 = a2.

Definition homomorphism {A B : kleene_algebra} (h : carrier A -> carrier B) :=
  forall a1 a2,
  h (null A) = null B /\
  h (id A) = id B /\
  h (a1 [+A] a2) = h (a1) [+B] h (a2) /\
  h (a1 [;A] a2) = h (a1) [;B] h (a2) /\
  h (a1 [*A]) = (h a1) [*B].

(* We can now prove that every language model is isomorphic to a relational 
   model. Note that we are 'cheating' since this formalization only 
   language models over the alphabet of all ascii characters rather than over
   an arbitrary finite alphabet. *)

Definition lang_to_rel (A : carrier LKA) : carrier (RKA string) :=
  fun x x' => exists y, A y /\ append x y = x'.

Lemma concat_empty_bidirectional : forall (s : string),
  append s EmptyString = append EmptyString s.
Proof.
  intros. induction s.
  - simpl. easy.
  - simpl. rewrite IHs. simpl. easy.
Qed.   

(* Lemma lang_to_rel_id : forall (A : carrier LKA),
  lang_to_rel () *)

Lemma lang_to_rel_mul : forall (a1 a2 : carrier LKA),
  lang_to_rel (a1 [;LKA] a2) = lang_to_rel a1 [;RKA string] lang_to_rel a2.
Proof.
  intros. simpl. unfold lang_to_rel.
  repeat (apply functional_extensionality ; intros). 
  apply propositional_extensionality. split ; intros.
  + inversion H as [s [H0 H1]]. unfold lang_comp in H0. 
    inversion H0 as [t [u [H2 [H3 H4]]]]. unfold rel_comp. 
    exists (append x t). split.
    * exists t. split ; easy.
    * exists u. split. apply H3. rewrite string_concat_assoc. rewrite <- H4.
      apply H1.
  + unfold rel_comp in H. inversion H as [s [[t [H0 H1]] [u [H2 H3]]]].
    exists (append t u). split.
    * unfold lang_comp. exists t. exists u. split ; easy.
    * rewrite <- string_concat_assoc. rewrite H1. apply H3.
Qed.

Lemma lang_to_rel_id : lang_to_rel (id LKA) = id (RKA string).
Proof.
  intros. simpl. unfold lang_to_rel.
  repeat (apply functional_extensionality ; intros). 
  apply propositional_extensionality. split ; intros.
  + inversion H as [s [H0 H1]]. unfold rel_id. inversion H0. 
    rewrite <- H1. rewrite <- H2. rewrite concat_empty_bidirectional. simpl.
    reflexivity.
  + inversion H. exists EmptyString. split. easy.
    rewrite concat_empty_bidirectional. simpl. reflexivity.
Qed.

Lemma lang_star_helper : forall (A : carrier LKA) (x y : string) (n : nat),
  (lang_to_rel (lang_pow A n)) x y <-> (rel_pow (lang_to_rel A) n) x y.
Proof.
  split. intros.
  - generalize dependent x. generalize dependent y. induction n.
    + intros. simpl in *. unfold rel_id. unfold lang_id in H. inversion H as [s [H0 H1]].
      inversion H0. rewrite <- H2 in H1. rewrite concat_empty_bidirectional in H1.
      simpl in H1. apply H1.
    + intros. simpl. simpl in H. inversion H as [s [H0 H1]]. 
      inversion H0 as [t [u [H2 [H3 H4]]]]. unfold rel_comp.
      exists (append x t). split.
      * unfold lang_to_rel. exists t. split ; easy.
      * apply IHn. unfold lang_to_rel. exists u. split. apply H3.
        rewrite string_concat_assoc. rewrite <- H4. apply H1.
  - intros. generalize dependent x. generalize dependent y. induction n.
    + intros. simpl in *. inversion H. unfold lang_to_rel. exists EmptyString.
      split. unfold lang_id. easy. rewrite concat_empty_bidirectional. simpl.
      reflexivity.
    + intros. simpl in H. inversion H as [s [H0 H1]]. simpl.
      specialize (lang_to_rel_mul A (lang_pow A n)). intros. simpl in H2.
      rewrite H2. exists s. split. apply H0. apply IHn. apply H1.
Qed.

(* Prooving that the lang_to_rel is a homomorphism *)
Theorem lang_to_rel_homomorphism : homomorphism lang_to_rel.
Proof.
  unfold homomorphism. intros. repeat (try split).
  - simpl. unfold lang_to_rel. 
    repeat (apply functional_extensionality ; intros). 
    apply propositional_extensionality. split ; intros.
    + inversion H as [s [H0 H1]]. contradiction.
    + unfold rel_null in H. contradiction.
  - apply lang_to_rel_id.
  - simpl. unfold lang_to_rel.
    repeat (apply functional_extensionality ; intros). 
    apply propositional_extensionality. split ; intros.
    + inversion H as [s [H0 H1]]. unfold rel_union.
      destruct H0.
      * left. exists x1. split ; easy.
      * right. exists x1. split ; easy.
    + destruct H. inversion H as [s [H0 H1]].
      * exists s. split. apply Union_introl. apply H0. apply H1.
      * inversion H as [s [H0 H1]]. exists s. split. apply Union_intror.
        apply H0. apply H1.
  -  apply lang_to_rel_mul.
  - simpl. 
    repeat (apply functional_extensionality ; intros). 
    apply propositional_extensionality. split ; intros.
    + inversion H as [s [H0 H1]]. unfold lang_star in H0. 
      inversion H0 as [n H2].  induction n.
      * intros. simpl in H2. inversion H2. exists 0. simpl. unfold rel_id.
        rewrite <- H1. rewrite <- H3. rewrite concat_empty_bidirectional.
        simpl. reflexivity.
      * intros. unfold rel_star. exists (S n). simpl. unfold rel_comp.  
        simpl in H2. inversion H2. inversion H3 as [y [H4 [H5 H6]]].
        exists (append x x1). split.
        -- unfold lang_to_rel. exists x1 ; split ; easy.
        -- apply lang_star_helper. unfold lang_to_rel. exists y. split.
            easy. rewrite string_concat_assoc. rewrite <- H6. apply H1.
    + inversion H as [n]. apply lang_star_helper in H0. unfold lang_to_rel.
      unfold lang_to_rel in H0. inversion H0 as [s [H1 H2]]. exists s.
      split. exists n. apply H1. apply H2.
Qed. 
      