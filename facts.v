(* This file contains proofs of some key facts about Kleene Algebras *)
From Coq Require Import Setoid.
Require Import theories.

Theorem double_star : forall (KA : kleene_algebra)
(KAt : kleene_algebra_theory KA) (x : carrier KA),
  x[*KA] = (x[*KA])[*KA].
Proof.
  intros. apply (partial_order_antisymmetric KA KAt).
  - assert (x[*KA] [<=KA] (id KA) [+KA] (x[*KA]) [+KA] 
      ((x[*KA])[;KA](x[*KA])[;KA]((x[*KA])[*KA]))).
      { unfold partial_order. repeat rewrite (sr_plus_assoc KA KAt).
        assert ((x [*KA]) [+KA] id KA [+KA] (x [*KA]) = (id KA) [+KA] (x[*KA])).
          { rewrite (sr_plus_comm KA KAt). rewrite (sr_plus_assoc KA KAt).
            rewrite (sr_idempotent KA KAt). rewrite (sr_plus_comm KA KAt). easy. }
        rewrite H. easy. }
    specialize (partial_order_transitive KA KAt (x [*KA])
      (id KA [+KA] (x [*KA]) [+KA] ((x [*KA]) [;KA] (x [*KA]) [;KA] 
      ((x [*KA]) [*KA]))) ((x [*KA]) [*KA])). intros.
    apply H0. apply H.
    specialize (sr_id_r KA KAt (x[*KA])). intros. rewrite <- H1 at 1.
    rewrite <- (sr_plus_assoc KA KAt). rewrite <- (sr_mul_assoc KA KAt). 
    rewrite <- (sr_distr_l KA KAt). rewrite (star_axiom_1_strong KA KAt).
    apply (star_axiom_1 KA KAt).
  - specialize (sr_id_r KA KAt ((x[*KA])[*KA])). intros. rewrite <- H. clear H.
    apply (star_axiom_3 KA KAt).
    remember (id KA [+KA] ((x [*KA]) [;KA] (x [*KA]))) as t1.
    assert (t1 [<= KA] (x[*KA]) [+KA] (x[*KA])).
      { apply (partial_order_transitive KA KAt) with 
         (y:= (id KA) [+KA] (x [;KA] (x[*KA])) [+KA] ((x [*KA]) [;KA] (x [*KA]))).
          - subst. unfold partial_order. rewrite (sr_plus_comm KA KAt).
            specialize (sr_plus_comm KA KAt (id KA) ((x [*KA]) [;KA] (x [*KA]))).
            intros. rewrite H. rewrite (sr_plus_assoc KA KAt).
            rewrite <- (sr_plus_assoc KA KAt). rewrite <- (sr_plus_assoc KA KAt).
            specialize (sr_plus_assoc KA KAt ((x [*KA]) [;KA] (x [*KA])) 
              ((x [*KA]) [;KA] (x [*KA])) (id KA)). intros. rewrite H0.
            rewrite (sr_idempotent KA KAt).  rewrite (sr_plus_comm KA KAt).
            clear H H0.
            specialize (sr_plus_assoc KA KAt (id KA) (id KA) (x [;KA] (x [*KA]))).
            intros. rewrite <- (sr_plus_assoc KA KAt). rewrite H. clear H.
            rewrite (sr_idempotent KA KAt). rewrite (sr_plus_comm KA KAt). easy.
          - rewrite (star_axiom_1_strong KA KAt). apply (plus_monotone_l KA KAt).
            apply (xstar_xstar_le_star KA KAt).
         }
  rewrite (sr_idempotent KA KAt) in H. apply H.
Qed.


Theorem sliding_rule : forall (KA : kleene_algebra) 
  (KAt : kleene_algebra_theory KA) (x y : carrier KA),
  ((x [;KA] y) [*KA]) [;KA] x = x [;KA] ((y [;KA] x)[*KA]).
Proof.
  intros. apply (partial_order_antisymmetric KA KAt).
  - apply (star_axiom_3 KA KAt). specialize (sr_id_r KA KAt x). intros.
    rewrite <- H at 1. rewrite <- (sr_mul_assoc KA KAt). 
    rewrite <- (sr_distr_l KA KAt). rewrite (sr_mul_assoc KA KAt).
    rewrite (star_axiom_1_strong KA KAt). apply (partial_order_reflexive KA KAt).
  - apply (star_axiom_4 KA KAt). specialize (sr_id_l KA KAt x). intros.
    rewrite <- H at 1. rewrite (sr_mul_assoc KA KAt).
    rewrite <- (sr_distr_r KA KAt). rewrite <- (sr_mul_assoc KA KAt).
     rewrite (star_axiom_2_strong KA KAt). apply (partial_order_reflexive KA KAt).
Qed.


Theorem denesting_rule : forall (KA : kleene_algebra)
  (KAt : kleene_algebra_theory KA) (x y : carrier KA),
  (x [+KA] y)[*KA] = (x[*KA]) [;KA] ((y [;KA] (x[*KA]))[*KA]).
Proof.
  intros. apply (partial_order_antisymmetric KA KAt).
  - specialize (sr_id_r KA KAt ((x [+KA] y)[*KA])). intros. rewrite <- H.
    clear H. apply (star_axiom_3 KA KAt). rewrite (sr_distr_r KA KAt).
    rewrite (sr_plus_assoc KA KAt).
    specialize (sr_plus_comm KA KAt (id KA) 
      (x [;KA] ((x [*KA]) [;KA] ((y [;KA] (x [*KA])) [*KA])))). intros.
    rewrite H. rewrite <- (sr_plus_assoc KA KAt).
    specialize (sr_mul_assoc KA KAt y (x[*KA]) ((y [;KA] (x [*KA])) [*KA])).
    intros. rewrite H0. clear H H0. rewrite (star_axiom_1_strong KA KAt).
    specialize (sr_id_l KA KAt (y [;KA] (x[*KA])[*KA])). intros.
    rewrite <- H at 2. rewrite (sr_mul_assoc KA KAt). 
    rewrite <- (sr_distr_r KA KAt). rewrite (sr_plus_comm KA KAt).
    rewrite (star_axiom_1_strong KA KAt). apply (partial_order_reflexive KA KAt).
  - assert (x [<= KA] x [+KA] y). { unfold partial_order. 
      rewrite (sr_plus_assoc KA KAt). rewrite (sr_idempotent KA KAt). easy. }
    assert (y [<= KA] x [+KA] y). { unfold partial_order. 
      rewrite (sr_plus_comm KA KAt). rewrite <- (sr_plus_assoc KA KAt).
      rewrite (sr_idempotent KA KAt). easy. }
    assert ((x [*KA]) [;KA] ((y [;KA] (x [*KA])) [*KA]) [<=KA] 
      ((x [+KA] y) [*KA]) [;KA] ((y [;KA] (x [*KA])) [*KA])).
      { apply (mul_monotone_r KA KAt). apply (star_monotone KA KAt). apply H. }
    apply (partial_order_transitive KA KAt) with 
      (y:=(x [+KA] y [*KA]) [;KA] (y [;KA] (x [*KA]) [*KA])). apply H1. clear H1.
    assert ((x [+KA] y [*KA]) [;KA] (y [;KA] (x [*KA]) [*KA]) [ <= KA]
      (x [+KA] y [*KA]) [;KA] ((x [+KA] y) [;KA] (x [*KA]) [*KA])).
      { apply (mul_monotone_l KA KAt). apply (star_monotone KA KAt).
        apply (mul_monotone_r KA KAt). apply H0. }
    apply (partial_order_transitive KA KAt) with (y :=
      (x [+KA] y [*KA]) [;KA] (x [+KA] y [;KA] (x [*KA]) [*KA])). apply H1.
    clear H1. assert ((x [+KA] y [*KA]) [;KA] ((x [+KA] y) [;KA] (x [*KA]) [*KA]) 
      [ <= KA] (x [+KA] y [*KA]) [;KA] (x [+KA] y [;KA] ((x [+KA] y) [*KA]) [*KA])).
      { apply (mul_monotone_l KA KAt). apply (star_monotone KA KAt).
        apply (mul_monotone_l KA KAt). apply (star_monotone KA KAt). apply H. }
    apply (partial_order_transitive KA KAt) with (y :=
      (x [+KA] y [*KA]) [;KA] ((x [+KA] y) [;KA] (x [+KA] y [*KA]) [*KA])).
    apply H1. clear H1. 
    assert ((x [+KA] y [*KA]) [;KA] ((x [+KA] y) [;KA] (x [+KA] y [*KA]) [*KA]) [ <=
      KA]((x [+KA] y) [*KA]) [;KA] (((id KA) [+KA] 
      ((x [+KA] y) [;KA] (x [+KA] y [*KA]))) [*KA])).
      { apply (mul_monotone_l KA KAt). 
        specialize (sr_add_zero KA KAt ((x [+KA] y) [;KA] (x [+KA] y [*KA]))).
        intros. rewrite (sr_plus_comm KA KAt) in H1. rewrite <- H1 at 1.
        apply (star_monotone KA KAt). apply (plus_monotone_r KA KAt). 
        unfold partial_order. rewrite (sr_plus_comm KA KAt). 
        apply (sr_add_zero KA KAt). }
    apply (partial_order_transitive KA KAt) with (y := 
      (x [+KA] y [*KA]) [;KA] (id KA [+KA] (x [+KA] y [;KA] (x [+KA] y [*KA])) [*KA])).
    apply H1. clear H1. rewrite (star_axiom_1_strong KA KAt).
    rewrite <- (double_star KA KAt). apply (xstar_xstar_le_star KA KAt).
Qed.


Theorem bisimulation_rule : forall (KA : kleene_algebra)
  (KAt : kleene_algebra_theory KA) (x y z : carrier KA),
  (x [;KA] y = y [;KA] z) -> ((x[*KA]) [;KA] y = y [;KA] (z[*KA])).
Proof.
  intros. apply (partial_order_antisymmetric KA KAt).
  - apply (star_axiom_3 KA KAt). 
    apply (partial_order_transitive KA KAt) with (y := 
      y [+KA] (y [;KA] z [;KA] (z[*KA]))).
    + rewrite (sr_mul_assoc KA KAt). rewrite H. 
      apply (partial_order_reflexive KA KAt).
    + specialize (sr_id_r KA KAt y). intros. rewrite <- H0 at 1.
      rewrite <- (sr_mul_assoc KA KAt). rewrite <- (sr_distr_l KA KAt).
      rewrite (star_axiom_1_strong KA KAt). apply (partial_order_reflexive KA KAt).
  - apply (star_axiom_4 KA KAt). 
    apply (partial_order_transitive KA KAt) with (y := 
      y [+KA] ((x [*KA]) [;KA] x [;KA] y)).
    + rewrite <- (sr_mul_assoc KA KAt). rewrite <- H.
      rewrite (sr_mul_assoc KA KAt). apply (partial_order_reflexive KA KAt).
    + specialize (sr_id_l KA KAt y). intros. rewrite <- H0 at 1.
      rewrite <- (sr_distr_r KA KAt). rewrite (star_axiom_2_strong KA KAt).
      apply (partial_order_reflexive KA KAt).
Qed.