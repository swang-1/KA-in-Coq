# A Formalization of Kleene Algebras in Coq

## Usage
The project was created using Coq 8.13.2. To build the project, just run `make`.

## Explanation of Files

### Basic Definitions
`theories.v` contains the basic definitions for Kleene Algebras. A Kleene algebra is defined as a record type: 
```coq
Record kleene_algebra : Type := make_kleene_algebra 
{
  carrier : Type;
  sr_plus : carrier -> carrier -> carrier; 
  sr_mul : carrier -> carrier -> carrier;
  star : carrier -> carrier ;
  null : carrier;
  id : carrier
}.
```
The semiring and star axioms are contained in a separate record type, `kleene_algebra_theory` that is parameterized on a Kleene algebra. Examples of instantiations of Kleene algebras can be found in `boolean_ka.v`,
`relational_ka.v`, and `language_ka.v`. This file also contains the definition for the natural partial order over semirings:
```coq
Definition partial_order (KA : kleene_algebra) (x y : carrier KA) : Prop :=
  x [+ KA] y = y.
```
where the notation `[ _ KA]` denotes the operation _ for the Kleene algebra `KA`. Lastly, `theories.v` contains proofs of key properties and equivalences in Kleene algebras such as monotonicity properties and
equivalent formulations of the star axioms. For example, we prove that the star axiom $b + ax \implies a^\ast b \le x$ can be equivalently written as $ax \le x \implies a^\ast x \le x$:
```Coq
Theorem star_3_alternate : forall (KA : kleene_algebra)
  (KAt : kleene_algebra_theory KA),
  (forall a b x : carrier KA,
  b [+KA] (a [;KA] x) [ <= KA] x -> (a [*KA]) [;KA] b [ <= KA] x) <->
  (forall a x, a [;KA] x [<= KA] x -> (a[*KA]) [;KA] x [<= KA] x).
Proof.
  ...
Qed.
```

### Proofs of Key Theorems

`facts.v` contains proofs of key theorems about Kleene algebras. Specifically, we prove the equality $x^\ast = x^{\ast\ast}$ as wells as the sliding, de-nesting, and bisimulation rules. For instance, the sliding rule is defined as follows:
```Coq
Theorem sliding_rule : forall (KA : kleene_algebra) 
  (KAt : kleene_algebra_theory KA) (x y : carrier KA),
  ((x [;KA] y) [*KA]) [;KA] x = x [;KA] ((y [;KA] x)[*KA]).
Proof.
  ...
Qed.
```

