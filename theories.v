From Coq Require Import Setoid.

(* Let's first define a structure for a Kleene Algebra *)
Record kleene_algebra : Type := make_kleene_algebra 
{
  carrier : Type;
  sr_plus : carrier -> carrier -> carrier; 
  sr_mul : carrier -> carrier -> carrier;
  star : carrier -> carrier ;
  null : carrier;
  id : carrier
}.

Notation "x [+ ka ] y "  := ((sr_plus ka) x y) 
  (at level 40, left associativity).

(* To avoid confusion with the Kleene star [*] we instead use [;] to 
  denote multiplication. This also happens to align nicely with the notaion
  for relational composition for relational algebras. *)
Notation "x [; ka ] y "  := ((sr_mul ka) x y) 
  (at level 45, left associativity).

Notation " y [* ka ] "  := ((star ka) y) 
  (at level 50, left associativity).

(* Before defining the star axioms, we need to define the natural partial
   order for idempotent semirings: *)
Definition partial_order (KA : kleene_algebra) (x y : carrier KA) : Prop :=
  x [+ KA] y = y.

Notation "x [ <= ka ] y" := (partial_order ka x y) (at level 70, no associativity).

Record kleene_algebra_theory (ka : kleene_algebra) : Prop := make_kleene_algebra_theory 
{
  (* Idempotent semiring axioms *)
  sr_plus_assoc : forall (x y z : carrier ka), 
    x [+ka] (y [+ka] z) = (x [+ka] y) [+ka] z ;
  
  sr_mul_assoc : forall (x y z : carrier ka),
    x [;ka] (y [;ka] z) = (x [;ka] y) [;ka] z ;

  sr_plus_comm : forall (x y : carrier ka),
    x [+ka] y = y [+ka] x ;

  sr_add_zero : forall (x : carrier ka),
    x [+ka] (null ka) = x ;

  sr_idempotent : forall (x : carrier ka),
    x [+ka] x = x ;

  sr_id_l : forall (x : carrier ka),
    ((id ka) [;ka] x) = x;

  sr_id_r : forall (x : carrier ka),
    (x [;ka] (id ka)) = x;

  sr_null_l : forall (x : carrier ka),
    ((null ka) [;ka] x) = null ka;

  sr_null_r : forall (x : carrier ka),
    (x [;ka] (null ka)) = null ka;
  
  sr_distr_l : forall (x y z : carrier ka), 
    (x [;ka] (y [+ka] z)) =  (x [;ka] y) [+ka] (x [;ka] z);

  sr_distr_r : forall (x y z : carrier ka), 
    ((x [+ka] y) [;ka] z) =  (x [;ka] z) [+ka] (y [;ka] z);

  (* Star Axioms *)
  star_axiom_1 : forall (x : carrier ka),
    (id ka) [+ka] (x [;ka] (x [*ka])) [<= ka] x [*ka];

  star_axiom_2 : forall (x : carrier ka),
    (id ka) [+ka] ((x [*ka]) [;ka] x)  [<= ka] x [*ka];

  star_axiom_3 : forall (a b x : carrier ka),
    b [+ka] (a [;ka] x) [<= ka] x -> (a [*ka]) [;ka] b [<= ka] x;

  star_axiom_4 : forall (a b x : carrier ka),
    b [+ka] (x [;ka] a) [<= ka] x -> b [;ka] (a [*ka]) [<= ka] x; 
}.

(* Some useful properties *)

(* Partial Order *)
Theorem partial_order_reflexive : forall (KA : kleene_algebra)
  (KAt : kleene_algebra_theory KA) (x : carrier KA),
  x [<= KA] x.
Proof.
  intros. unfold partial_order. apply (sr_idempotent KA KAt).
Qed.

Theorem partial_order_antisymmetric : forall (KA : kleene_algebra)
  (KAt : kleene_algebra_theory KA) (x y : carrier KA),
  (x [<= KA] y) -> (y [<= KA] x) -> x = y.
Proof.
  intros. unfold partial_order in H. rewrite <- H0.
  rewrite (sr_plus_comm KA KAt). easy.
Qed.

Theorem partial_order_transitive : forall (KA : kleene_algebra)
  (KAt : kleene_algebra_theory KA) (x y z : carrier KA),
  (x [<= KA] y) -> (y [<= KA] z) -> x [<= KA] z.
Proof.
  intros. unfold partial_order in *. rewrite <- H0 at 1.
  rewrite (sr_plus_assoc KA KAt). rewrite H. easy.
Qed. 

(* Monotonicity *)
Theorem plus_monotone_r : forall (KA : kleene_algebra) 
  (KAt : kleene_algebra_theory KA) (x y z : carrier KA),
  x [<= KA] y -> x [+KA] z [<= KA] y [+KA] z.
Proof.
  intros. unfold partial_order in *. 
  rewrite <- (sr_plus_assoc KA KAt). 
  specialize (sr_plus_comm KA KAt z (y [+KA] z)). intros.
  rewrite H0. repeat rewrite (sr_plus_assoc KA KAt). rewrite H.
  rewrite <- (sr_plus_assoc KA KAt).
  rewrite (sr_idempotent KA KAt). reflexivity.
Qed.

Theorem plus_monotone_l : forall (KA : kleene_algebra) 
  (KAt : kleene_algebra_theory KA) (x y z : carrier KA),
  x [<= KA] y -> z [+KA] x [<= KA] z [+KA] y.
Proof.
  intros. unfold partial_order in *. rewrite <- (sr_plus_assoc KA KAt).
  specialize (sr_plus_comm KA KAt z y). intros.
  rewrite H0 at 1.
  assert (x [+KA] (y [+KA] z) = z [+KA] y).
    { rewrite (sr_plus_assoc KA KAt). rewrite H. apply (sr_plus_comm KA KAt). }
  rewrite H1. rewrite (sr_plus_assoc KA KAt). rewrite (sr_idempotent KA KAt).
  reflexivity.
Qed.

Theorem mul_monotone_r : forall (KA : kleene_algebra) 
  (KAt : kleene_algebra_theory KA) (x y z : carrier KA),
  x [<= KA] y -> x [;KA] z [<= KA] y [;KA] z.
Proof.
  intros. unfold partial_order in *. rewrite <- (sr_distr_r KA KAt).
  rewrite H. reflexivity.
Qed.

Theorem mul_monotone_l : forall (KA : kleene_algebra) 
  (KAt : kleene_algebra_theory KA) (x y z : carrier KA),
  x [<= KA] y -> z [;KA] x [<= KA] z [;KA] y.
Proof.
  intros. unfold partial_order in *. rewrite <- (sr_distr_l KA KAt).
  rewrite H. reflexivity.
Qed.

Theorem star_monotone : forall (KA : kleene_algebra) 
  (KAt : kleene_algebra_theory KA) (x y : carrier KA),
  x [<= KA] y -> (x [* KA]) [<= KA] (y [* KA]).
Proof.
  intros. assert (x [* KA] = x [*KA] [; KA] (id KA)).
    { rewrite (sr_id_r KA KAt). reflexivity. } 
  rewrite H0. apply (star_axiom_3 KA KAt).
  specialize (partial_order_transitive KA KAt 
                (id KA [+KA] (x [;KA] (y [*KA])))
                (id KA [+KA] (y [;KA] (y [*KA])))
                (y [*KA])). intros.
  apply H1.
  - apply (plus_monotone_l KA KAt). apply (mul_monotone_r KA KAt). apply H.
  - apply (star_axiom_1 KA KAt).
Qed.

(* Identities involving the star axioms *)

(* Strenghtening of the two equational star axioms*)
Theorem star_axiom_1_strong : forall (KA : kleene_algebra) 
  (KAt : kleene_algebra_theory KA) (x : carrier KA),
  (id KA) [+KA] (x [;KA] (x [*KA])) = x [*KA].
Proof.
  intros. apply (partial_order_antisymmetric KA KAt).
  - apply (star_axiom_1 KA KAt).
  - specialize (sr_id_r KA KAt (x [*KA])). intros. rewrite <- H at 1.
    apply (star_axiom_3 KA KAt). apply (plus_monotone_l KA KAt).
    apply (mul_monotone_l KA KAt). apply (star_axiom_1 KA KAt).
Qed.

Theorem star_axiom_2_strong : forall (KA : kleene_algebra) 
  (KAt : kleene_algebra_theory KA) (x : carrier KA),
  (id KA) [+KA] ((x [*KA]) [;KA] x) = x [*KA].
Proof. 
  intros. apply (partial_order_antisymmetric KA KAt).
  - apply (star_axiom_2 KA KAt).
  - specialize (sr_id_l KA KAt (x [*KA])). intros. rewrite <- H at 1.
    apply (star_axiom_4 KA KAt). apply (plus_monotone_l KA KAt).
    apply (mul_monotone_r KA KAt). apply (star_axiom_2 KA KAt).
Qed.

(* Useful consequences of the star axioms *)
Theorem id_le_star : forall (KA : kleene_algebra) 
  (KAt : kleene_algebra_theory KA) (x : carrier KA),
  id KA [<= KA] x [*KA].
Proof.
  intros. specialize (star_axiom_1_strong KA KAt x). intros. 
  unfold partial_order. rewrite <- H. rewrite (sr_plus_assoc KA KAt).
  rewrite (sr_idempotent KA KAt). reflexivity.
Qed.

Theorem x_le_star : forall (KA : kleene_algebra) 
  (KAt : kleene_algebra_theory KA) (x : carrier KA),
  x [<= KA] x [*KA].
Proof.
  intros. specialize (id_le_star KA KAt x). intros. 
  apply (mul_monotone_l KA KAt) with (z := x) in H. 
  rewrite (sr_id_r KA KAt) in H. 
  specialize (star_axiom_1_strong KA KAt x). intros. unfold partial_order in *.
  rewrite <- H0 at 1. rewrite (sr_plus_assoc KA KAt).
  specialize (sr_plus_comm KA KAt x (id KA)).
  intros. rewrite H1. rewrite <- (sr_plus_assoc KA KAt). rewrite H. apply H0.
Qed.

Theorem xstar_xstar_le_star : forall (KA : kleene_algebra) 
  (KAt : kleene_algebra_theory KA) (x : carrier KA),
  (x [*KA]) [;KA] (x [*KA]) [<= KA] x[*KA].
Proof.
  intros. apply (star_axiom_3 KA KAt).
  assert (x [;KA] (x[*KA]) [<= KA] x[*KA]).
    { specialize (partial_order_transitive KA KAt (x [;KA] (x[*KA]))
        ((id KA) [+KA] (x [;KA] (x[*KA]))) (x[*KA])). intros. apply H.
      - unfold partial_order. rewrite (sr_plus_comm KA KAt).
        rewrite <- (sr_plus_assoc KA KAt). rewrite (sr_idempotent KA KAt).
        reflexivity.
      - apply (star_axiom_1 KA KAt). }
  unfold partial_order in *. rewrite <- (sr_plus_assoc KA KAt). rewrite H.
  apply (sr_idempotent KA KAt).
Qed.

(* Equivalent formulations of the equational implications *)
Theorem star_3_alternate : forall (KA : kleene_algebra)
  (KAt : kleene_algebra_theory KA),
  (forall a b x : carrier KA,
  b [+KA] (a [;KA] x) [ <= KA] x -> (a [*KA]) [;KA] b [ <= KA] x) <->
  (forall a x, a [;KA] x [<= KA] x -> (a[*KA]) [;KA] x [<= KA] x).
Proof.
  intros. split.
  - intros. apply H. unfold partial_order in *. 
    rewrite <- (sr_plus_assoc KA KAt). rewrite H0. apply (sr_idempotent KA KAt).
  - intros. assert (b [<= KA] x).
      { unfold partial_order in *. rewrite <- H0. 
        repeat rewrite (sr_plus_assoc KA KAt). rewrite (sr_idempotent KA KAt).
        reflexivity. }
    assert (a [;KA] x [<= KA] x).
      {  unfold partial_order in *. rewrite <- H0 at 2.
         rewrite (sr_plus_assoc KA KAt). 
         specialize (sr_plus_comm KA KAt b (a [;KA] x)). intros. rewrite H2.
         rewrite (sr_plus_assoc KA KAt). rewrite (sr_idempotent KA KAt). 
         rewrite <- H2. apply H0. }
    apply (partial_order_transitive KA KAt ((a [*KA]) [;KA] b)
      ((a [*KA]) [;KA] x) x).
    + apply (mul_monotone_l KA KAt). apply H1.
    + apply H. apply H2.
Qed.

Theorem star_4_alternate : forall (KA : kleene_algebra)
  (KAt : kleene_algebra_theory KA),
  (forall a b x : carrier KA,
  b [+KA] (x [;KA] a) [ <= KA] x -> b [;KA] (a [*KA]) [ <= KA] x) <->
  (forall a x, x [;KA] a [<= KA] x -> x [;KA] (a[*KA]) [<= KA] x).
Proof.
  intros. split ; intros.
  - apply H. unfold partial_order in *. rewrite <- (sr_plus_assoc KA KAt).
    rewrite H0. apply (sr_idempotent KA KAt).
  - assert (b [<= KA] x).
    { unfold partial_order in *. rewrite <- H0. 
    repeat rewrite (sr_plus_assoc KA KAt). rewrite (sr_idempotent KA KAt).
    reflexivity. }
    assert (x [;KA] a [<= KA] x).
      {  unfold partial_order in *. rewrite <- H0 at 2.
        rewrite (sr_plus_assoc KA KAt). 
        specialize (sr_plus_comm KA KAt b (x [;KA] a)). intros. rewrite H2.
        rewrite (sr_plus_assoc KA KAt). rewrite (sr_idempotent KA KAt). 
        rewrite <- H2. apply H0. }
    apply (partial_order_transitive KA KAt (b [;KA] (a[*KA]))
      (x [;KA] (a[*KA])) x).
    + apply (mul_monotone_r KA KAt). apply H1.
    + apply H. apply H2.
Qed.






