Require Import theories.
From Coq Require Import Bool.

Definition Boolean_KA :=
{|
  carrier := bool ;
  sr_plus := orb ;
  sr_mul := andb ;
  star := fun _ => true ;
  null := false ;
  id := true ;
|}.

Definition BKA := Boolean_KA.

Lemma orb_idempotent : forall (b : carrier BKA),
  b || b = b.
Proof.
  intros. destruct b ; easy.
Qed.

Lemma bool_star_1 : forall (b : carrier BKA),
  (id BKA) [+BKA] (b [;BKA] (b[*BKA])) [<=BKA] b[*BKA].
Proof.
  intros. unfold partial_order. easy.
Qed.

Lemma bool_star_2 : forall (b : carrier BKA),
  (id BKA) [+BKA] ((b[*BKA]) [;BKA] b) [<=BKA] b[*BKA].
Proof.
  intros. unfold partial_order. easy.
Qed.

Lemma bool_star_3 : forall (a b x : carrier BKA),
  b [+BKA] (a [;BKA] x) [<= BKA] x -> (a [*BKA]) [;BKA] b [<= BKA] x.
Proof.
  intros. unfold partial_order in *. simpl. simpl in H. rewrite <- H.
  repeat rewrite orb_assoc.  rewrite orb_idempotent. reflexivity.
Qed.

Lemma bool_star_4 : forall (a b x : carrier BKA),
  b [+BKA] (x [;BKA] a) [<= BKA] x -> b [;BKA] (a [*BKA]) [<= BKA] x.
Proof.
  intros. unfold partial_order in *. simpl. simpl in H. rewrite <- H.
  repeat rewrite orb_assoc. rewrite andb_comm. rewrite orb_idempotent. 
  reflexivity.
Qed.

Lemma BKA_or_assoc : forall (x y z : carrier BKA),
  x [+BKA] (y [+BKA] z) = (x [+BKA] y) [+BKA] z.
Proof.
  intros. simpl. apply orb_assoc.
Qed.


Definition Boolean_KA_theory :=
{|
  (* Star Axioms *)
  star_axiom_1 := bool_star_1;
  star_axiom_2 := bool_star_2;
  star_axiom_3 := bool_star_3;
  star_axiom_4 := bool_star_4;

  (* Idempotent semiring axioms *)
  sr_plus_assoc := BKA_or_assoc;
  sr_mul_assoc := andb_assoc;
  sr_plus_comm := orb_comm;
  sr_add_zero := orb_false_r;
  sr_idempotent := orb_idempotent;
  sr_id_l := andb_true_l;
  sr_id_r := andb_true_r;
  sr_null_l := andb_false_l;
  sr_null_r := andb_false_r;
  sr_distr_l := andb_orb_distrib_r;
  sr_distr_r := andb_orb_distrib_l;
|}.