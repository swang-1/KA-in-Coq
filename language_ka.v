Require Import theories.
Require Import facts.
From Coq Require Import Strings.String.
From Coq Require Import Ensembles.

Definition language := Ensemble string.

Definition lang_union (A B : language ):= Union string A B.

Definition lang_comp (A B : language) :=
  fun s => exists x y, A x /\ B y /\ s = append x y.

Definition lang_id := Singleton string (EmptyString).

Definition lang_null := Empty_set string.

Fixpoint lang_pow (A : language) (n : nat) :=
  match n with
  | 0 => lang_id
  | S x => lang_comp A (lang_pow A x)
  end.

Definition lang_star (A : language) := 
  fun s => exists n, (lang_pow A n) s.

Definition language_KA :=
  {|
    carrier := language ;
    sr_plus := Union string ;
    sr_mul := lang_comp ;
    star := lang_star ;
    id := Singleton string (EmptyString) ;
    null := Empty_set string ;
  |}.

Definition LKA := language_KA.

(* Below are the KA axioms for languages. Since the proofs are largely similar
   to those for relational algebras, most of the following proofs are 
   admitted. *)

(* Idempotent semiring axioms *)
Theorem lang_plus_assoc : forall (x y z : carrier LKA), 
  x [+LKA] (y [+LKA] z) = (x [+LKA] y) [+LKA] z.
Proof.
  intros. simpl. apply Extensionality_Ensembles. unfold Same_set.
  unfold Included. split ; intros.
  - destruct H. apply Union_introl. apply Union_introl. easy.
    destruct H. apply Union_introl. apply Union_intror. easy.
    apply Union_intror. easy.
  - destruct H. destruct H.
    apply Union_introl. easy.
    apply Union_intror. apply Union_introl. easy.
    apply Union_intror. apply Union_intror. easy.
Qed.

Lemma string_concat_assoc : forall (x y z : string),
  append (append x y) z = append x (append y z).
Proof.
  intros. induction x.
  - simpl. reflexivity.
  - simpl. rewrite IHx. reflexivity.
Qed.

Theorem lang_mul_assoc : forall (x y z : carrier LKA),
  x [;LKA] (y [;LKA] z) = (x [;LKA] y) [;LKA] z.
Proof.
  intros. simpl. apply Extensionality_Ensembles. unfold Same_set.
  unfold Included. split ; intros.
  - inversion H. inversion H0. destruct H1. inversion H2. inversion H3. inversion H5.
    unfold In. exists (append x1 x3). exists x4. split.
    + exists x1. exists x3. easy.
    + split. apply H6. rewrite string_concat_assoc. destruct H6. destruct H7.
      rewrite <- H8. apply H4.
  - inversion H. inversion H0. destruct H1. inversion H2. inversion H1.
    inversion H5. exists x3. exists (append x4 x2). split.
    + apply H6.
    + split. exists x4. exists x2. easy.
      rewrite <- string_concat_assoc. destruct H6. destruct H7. rewrite <- H8.
      apply H4.
Qed.

Theorem lang_plus_comm : forall (x y : carrier LKA),
  x [+LKA] y = y [+LKA] x.
Proof.
  intros. simpl. apply Extensionality_Ensembles. unfold Same_set.
  unfold Included. split ; intros ; destruct H;
  try (apply Union_intror; easy) ; try (apply Union_introl ; easy).
Qed. 

Theorem lang_add_zero : forall (x : carrier LKA),
  x [+LKA] (null LKA) = x.
Proof.
  Admitted.

Theorem lang_idempotent : forall (x : carrier LKA),
  x [+LKA] x = x.
Proof.
  Admitted.

Theorem lang_id_l : forall (x : carrier LKA),
  ((id LKA) [;LKA] x) = x.
Proof.
  Admitted.

Theorem lang_id_r : forall (x : carrier LKA),
  (x [;LKA] (id LKA)) = x.
Proof.
  Admitted.

Theorem lang_null_l : forall (x : carrier LKA),
  ((null LKA) [;LKA] x) = null LKA.
Proof.
  Admitted.

Theorem lang_null_r : forall (x : carrier LKA),
  (x [;LKA] (null LKA)) = null LKA.
Proof.
  Admitted.

Theorem lang_distr_l : forall (x y z : carrier LKA), 
  (x [;LKA] (y [+LKA] z)) =  (x [;LKA] y) [+LKA] (x [;LKA] z).
Proof.
  Admitted.

Theorem lang_distr_r : forall (x y z : carrier LKA), 
  ((x [+LKA] y) [;LKA] z) =  (x [;LKA] z) [+LKA] (y [;LKA] z).
Proof.
  Admitted.

(* Star Axioms *)
Theorem lang_star_1 : forall (x : carrier LKA),
  (id LKA) [+LKA] (x [;LKA] (x [*LKA])) [<= LKA] x [*LKA].
Proof.
  Admitted.

Theorem lang_star_2 : forall (x : carrier LKA),
  (id LKA) [+LKA] ((x [*LKA]) [;LKA] x)  [<= LKA] x [*LKA].
Proof.
  Admitted.

Theorem lang_star_3 : forall (a b x : carrier LKA),
  b [+LKA] (a [;LKA] x) [<= LKA] x -> (a [*LKA]) [;LKA] b [<= LKA] x.
Proof.
  Admitted.

Theorem lang_star_4 : forall (a b x : carrier LKA),
  b [+LKA] (x [;LKA] a) [<= LKA] x -> b [;LKA] (a [*LKA]) [<= LKA] x.
Proof.
  Admitted.

Definition language_KA_theory := 
  {|
    sr_plus_assoc := lang_plus_assoc ; 
    sr_mul_assoc := lang_mul_assoc ; 
    sr_plus_comm := lang_plus_comm ; 
    sr_add_zero := lang_add_zero ;
    sr_idempotent := lang_idempotent ;
    sr_id_l := lang_id_l ;
    sr_id_r := lang_id_r ; 
    sr_null_l := lang_null_l ; 
    sr_null_r := lang_null_r ;
    sr_distr_l := lang_distr_l ; 
    sr_distr_r := lang_distr_r ; 

    (* Star Axioms *)
    star_axiom_1 := lang_star_1 ; 
    star_axiom_2 := lang_star_2 ; 
    star_axiom_3 := lang_star_3 ; 
    star_axiom_4 := lang_star_4 ;
  |}.

Definition LKAt := language_KA_theory.

