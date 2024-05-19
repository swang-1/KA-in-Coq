(* This file contains proofs of some key facts about Kleene Algebras *)
From Coq Require Import Setoid.
Require Import theories.

Theorem double_star : forall (KA : kleene_algebra)
(KAt : kleene_algebra_theory KA) (x : carrier KA),
  x[*KA] = (x[*KA])[*KA].
Proof.
  intros. apply (partial_order_antisymmetric KA KAt).
  (* <= Direction *)
  - (* x* <= x* + xx*x* *)
    assert (x[*KA] [<=KA] (id KA) [+KA] (x[*KA]) [+KA] 
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
    
    (* = [1 + xx*]x* *)
    specialize (sr_id_r KA KAt (x[*KA])). intros. rewrite <- H1 at 1.
    rewrite <- (sr_plus_assoc KA KAt). rewrite <- (sr_mul_assoc KA KAt). 
    rewrite <- (sr_distr_l KA KAt). rewrite (star_axiom_1_strong KA KAt).
    
    (* <= x*x* *)
    apply (star_axiom_1 KA KAt).

  (* >= direction*)
  - (*Apply star axiom b + ac <= c -> a*b <= c with a = x, b = c = x* *)
    specialize (sr_id_r KA KAt ((x[*KA])[*KA])). intros. rewrite <- H. clear H.
    apply (star_axiom_3 KA KAt).
    remember (id KA [+KA] ((x [*KA]) [;KA] (x [*KA]))) as t1.

    (* 1 + x*x* <= x* + x* *)
    assert (t1 [<= KA] (x[*KA]) [+KA] (x[*KA])).
      { apply (partial_order_transitive KA KAt) with 
         (y:= (id KA) [+KA] (x [;KA] (x[*KA])) [+KA] ((x [*KA]) [;KA] (x [*KA]))).
          - (* 1 + x*x* <= 1 + xx* + x*x* *)
            subst. unfold partial_order. rewrite (sr_plus_comm KA KAt).
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
          
          - (* 1 + xx* + x*x* <= x* + x**)
            rewrite (star_axiom_1_strong KA KAt). apply (plus_monotone_l KA KAt).
            apply (xstar_xstar_le_star KA KAt).
         }
  rewrite (sr_idempotent KA KAt) in H. apply H.
Qed.

Theorem sliding_rule : forall (KA : kleene_algebra) 
  (KAt : kleene_algebra_theory KA) (x y : carrier KA),
  ((x [;KA] y) [*KA]) [;KA] x = x [;KA] ((y [;KA] x)[*KA]).
Proof.
  intros. apply (partial_order_antisymmetric KA KAt).
  (* <= direction *)
  - (* star rule b + ac <= c -> a^*b <= c with a = xy, b = x, c = x(yx)**)
    apply (star_axiom_3 KA KAt). 
    
    (* x + xyx(yx)* = x[1 + yx(yx)*] *)
    specialize (sr_id_r KA KAt x). intros.
    rewrite <- H at 1. rewrite <- (sr_mul_assoc KA KAt). 
    rewrite <- (sr_distr_l KA KAt). rewrite (sr_mul_assoc KA KAt).

    (* <= x(yx)* *)
    rewrite (star_axiom_1_strong KA KAt). apply (partial_order_reflexive KA KAt).

  - (* >= Direction. Symmetric to the previous direction *)
    apply (star_axiom_4 KA KAt). specialize (sr_id_l KA KAt x). intros.
    rewrite <- H at 1. rewrite (sr_mul_assoc KA KAt).
    rewrite <- (sr_distr_r KA KAt). rewrite <- (sr_mul_assoc KA KAt).
     rewrite (star_axiom_2_strong KA KAt). apply (partial_order_reflexive KA KAt).
Qed.


Theorem denesting_rule : forall (KA : kleene_algebra)
  (KAt : kleene_algebra_theory KA) (x y : carrier KA),
  (x [+KA] y)[*KA] = (x[*KA]) [;KA] ((y [;KA] (x[*KA]))[*KA]).
Proof.
  intros. apply (partial_order_antisymmetric KA KAt).

  (* <= Direction *)
  - (* star rule b + ac <= c -> a*b <= c with a = x + y, b = 1, c = x*(yx)* *)
    specialize (sr_id_r KA KAt ((x [+KA] y)[*KA])). intros. rewrite <- H.
    clear H. apply (star_axiom_3 KA KAt). 
    
    (* = 1 + xx*[yx*]* + yx*[yx*]* *)
    rewrite (sr_distr_r KA KAt). rewrite (sr_plus_assoc KA KAt).

    (* = xx*[yx*]* + 1 + yx*[yx*]* *)
    specialize (sr_plus_comm KA KAt (id KA) 
      (x [;KA] ((x [*KA]) [;KA] ((y [;KA] (x [*KA])) [*KA])))). intros.
    rewrite H. 
    
    (* = xx*[yx*]*  + [yx*]* *)
    rewrite <- (sr_plus_assoc KA KAt).
    specialize (sr_mul_assoc KA KAt y (x[*KA]) ((y [;KA] (x [*KA])) [*KA])).
    intros. rewrite H0. clear H H0. rewrite (star_axiom_1_strong KA KAt).

    (* = (xx* + 1)[yx*]* *)
    specialize (sr_id_l KA KAt (y [;KA] (x[*KA])[*KA])). intros.
    rewrite <- H at 2. rewrite (sr_mul_assoc KA KAt). 
    rewrite <- (sr_distr_r KA KAt). 
    
    (* = x*[yx*]* *)
    rewrite (sr_plus_comm KA KAt).
    rewrite (star_axiom_1_strong KA KAt). apply (partial_order_reflexive KA KAt).
 
  (* >= Direction*)
  - (* Replace x and y with x + y: x*[yx*]* <= (x + y)*[(x + y)(x + y)*]* *)
    assert (x [<= KA] x [+KA] y). { unfold partial_order. 
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
    
    (* = (x + y)*[1 + (x + y)(x + y)*] *)
    assert ((x [+KA] y [*KA]) [;KA] ((x [+KA] y) [;KA] (x [+KA] y [*KA]) [*KA]) [ <=
      KA]((x [+KA] y) [*KA]) [;KA] (((id KA) [+KA] 
      ((x [+KA] y) [;KA] (x [+KA] y [*KA]))) [*KA])).
      { apply (mul_monotone_l KA KAt). 
        specialize (sr_add_zero KA KAt ((x [+KA] y) [;KA] (x [+KA] y [*KA]))).
        intros. rewrite (sr_plus_comm KA KAt) in H1. rewrite <- H1 at 1.
        apply (star_monotone KA KAt). apply (plus_monotone_r KA KAt). 
        unfold partial_order. rewrite (sr_plus_comm KA KAt). 
        apply (sr_add_zero KA KAt). }
    
    (* <= (x + y)*(x + y)** *)
    apply (partial_order_transitive KA KAt) with (y := 
      (x [+KA] y [*KA]) [;KA] (id KA [+KA] (x [+KA] y [;KA] (x [+KA] y [*KA])) [*KA])).
    apply H1. clear H1. rewrite (star_axiom_1_strong KA KAt).

    (* = (x + y)*(x + y)* = (x + y)* *)
    rewrite <- (double_star KA KAt). apply (xstar_xstar_le_star KA KAt).
Qed.


Theorem bisimulation_rule : forall (KA : kleene_algebra)
  (KAt : kleene_algebra_theory KA) (x y z : carrier KA),
  (x [;KA] y = y [;KA] z) -> ((x[*KA]) [;KA] y = y [;KA] (z[*KA])).
Proof.
  intros. apply (partial_order_antisymmetric KA KAt).

  (* <= Direction *)
  - (* Star axiom b + ac <= c -> a*b <= c ith a = x, b = y, c = yz* *)
    apply (star_axiom_3 KA KAt). 
    apply (partial_order_transitive KA KAt) with (y := 
      y [+KA] (y [;KA] z [;KA] (z[*KA]))).
    
    (* y + xyz* <= y + yzz* *)
    + rewrite (sr_mul_assoc KA KAt). rewrite H. 
      apply (partial_order_reflexive KA KAt).

    (* = y[1 + zz*] = yz* *)
    + specialize (sr_id_r KA KAt y). intros. rewrite <- H0 at 1.
      rewrite <- (sr_mul_assoc KA KAt). rewrite <- (sr_distr_l KA KAt).
      rewrite (star_axiom_1_strong KA KAt). apply (partial_order_reflexive KA KAt).

  - (* >= Direction - symmetric to previous direction *)
    apply (star_axiom_4 KA KAt). 
    apply (partial_order_transitive KA KAt) with (y := 
      y [+KA] ((x [*KA]) [;KA] x [;KA] y)).
    + rewrite <- (sr_mul_assoc KA KAt). rewrite <- H.
      rewrite (sr_mul_assoc KA KAt). apply (partial_order_reflexive KA KAt).
    + specialize (sr_id_l KA KAt y). intros. rewrite <- H0 at 1.
      rewrite <- (sr_distr_r KA KAt). rewrite (star_axiom_2_strong KA KAt).
      apply (partial_order_reflexive KA KAt).
Qed.