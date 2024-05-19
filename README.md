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
The idempotent semiring and star axioms are contained in a separate record type, `kleene_algebra_theory`, parameterized on a Kleene algebra. Examples of instantiations of Kleene algebras can be found in `boolean_ka.v`,
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

### Examples of Kleene Algebras
`boolean_ka.v`, `relational_ka`, and `language_ka.v` define the boolean KA, KA over relational models, and KA over language models respectively.

#### Boolean Kleene Algebra
The simplest example is the boolean Kleene Algebra, $\langle \{0, 1\}, \lor, \land, \ast, 0, 1 \rangle$, where $\ast$ is defined as $b^\ast = 1$. Most of the semiring axioms are given by built-in theorem from the Coq Standard Library. However, some axioms, most notably the star axioms, require additional proof, though these proofs are trivial.

#### Relational Models
We define relational models using the built-in definitions for relations, where the type of a relation is given by `relation : (A : Type) -> A -> A -> Prop`. The union, composition, and star operations can be defined in a straightforward way. For example, the star operator is defined in terms of finite powers of a relation:
```Coq
Fixpoint rel_pow {X : Type} (R : relation X) (n : nat) : relation X :=
  match n with
  | 0 => rel_id X
  | S n => rel_comp R (rel_pow R n)
  end.

Definition rel_star {X : Type} (R : relation X) :=
  fun x y => exists n, (rel_pow R n) x y.
```
We can then define a relational Kleene algebra parametrized over a type $X$:
```Coq
Definition relational_KA (X : Type) : kleene_algebra :=
  {|
    carrier := relation X ;
    sr_plus := rel_union ;
    sr_mul := rel_comp ;
    star := rel_star ;
    id := rel_id X ;
    null := rel_null X ; 
  |}.
```
However, this definition given in `relational_ka` is limited in that it only defines the Kleene algebra consisting of ALL relations over a set $X$, whereas in the more general case, any subset of $2^{X \times X}$ forms a Kleene algebra. Proving that the star axioms hold is non-trivial and is described in more detail in "Challenges."

#### Language Models
Language models are defined using the built-in libraries for strings and Ensembles. The latter provides a way to describe sets as propositions. Hence, a language is given by the type
```Coq
Definition language := Ensemble string.
```
The operations for language models are defined very similarly to those of relational models. The instantiation of language models is:
```coq
Definition language_KA :=
  {|
    carrier := language ;
    sr_plus := Union string ;
    sr_mul := lang_comp ;
    star := lang_star ;
    id := Singleton string (EmptyString) ;
    null := Empty_set string ;
  |}.
```
Note that this formalization defines the language model over $\Sigma^\ast$ where $\Sigma$ is the alphabet containing all ascii characters. The proofs for the idempotent semiring and star axioms are admitted due to their similarity to the proofs for relational models.

### Morphisms Between Kleene Algebras

`isomorphism.v` demonstrates the ability to construct and prove properties about mappings between Kleene Algebras. We first define what it means for a function between two Kleene algebras to be a homomorphism:
```coq
Definition homomorphism {A B : kleene_algebra} (h : carrier A -> carrier B) :=
  forall a1 a2,
  h (null A) = null B /\
  h (id A) = id B /\
  h (a1 [+A] a2) = h (a1) [+B] h (a2) /\
  h (a1 [;A] a2) = h (a1) [;B] h (a2) /\
  h (a1 [*A]) = (h a1) [*B].
```
Then, consider the mapping
$$h(A) = \\{ (x, xy) \\,|\\, x \in \Sigma^\ast, y \in A \\}$$
In Coq, this function is written:
```coq
Definition lang_to_rel (A : carrier LKA) : carrier (RKA string) :=
  fun x x' => exists y, A y /\ append x y = x'.
```
This file contains the proof that `lang_to_rel` is a homomorphism. In the general case, this function is an isomorphism between $A$ and its image in $2^{\Sigma^\ast \times \Sigma^\ast}$. However, in this formalization, the co-domain of $h$ is the Kleene Algebra consisting of all relations of $2^{\Sigma^\ast \times \Sigma^\ast}$, so `lang_to_rel` is not surjective. 

### Challenges
Many challenges came with completing the above proofs in Coq. For example, since powers of relations are defined inductively with $R^{n + 1} = R; R^n$, we cannot rewrite $R^n; R$ as $R^{n + 1}$ in Coq without additional proof. This issue required the use of an additional lemma in the proof of the star axioms for relational algebras:
```coq
Lemma lang_star_helper : forall (A : carrier LKA) (x y : string) (n : nat),
  (lang_to_rel (lang_pow A n)) x y <-> (rel_pow (lang_to_rel A) n) x y.
Proof.
  ...
Qed.
```
Another challenge arose when proving that `lang_to_rel` is an isomorphism. As explained above, the way that language models and relational models were defined made it so that this function is not surjective. I was also unable to prove injectivity and I am unsure whether it is possible to prove injectivity of `lang_to_rel` constructively.

### Future Work
One avenue of future work is automation involving this formalization of Kleene algebra. One way of incorporating automation could be to create tactics that streamline equational reasoning. Rewriting equations is currently tedious and unwieldy due to needing to manually apply associativity and commutativity. For example, suppose that we have the assumption `y + z = a` and we want to rewrite the term `x + y + z`. In a pencil-and-paper proof, this rewriting is trivial, but in Coq, we need to first use associativity to rewrite the term as `x + (y + z)`. Hence, specialized tactics for rewriting using the basic semiring axioms and monotonicity properties can greatly streamline the proof-writing process.

At a higher level, there are many structures and properties related to Kleene algebras that are not formalized in this implementation which could account for much of the possible future work on this project. The most obvious candidate for formalization would be incorporating tests, which we could then extend to a guarded command language. This extension would allow us to create examples to demonstrate how KAT can be used to prove program correctness. Other concepts that could be formalized include star continuity, equivalence between Kleene algebras, and many more.

Lastly, the files in this implementation could easily be converted into a tutorial on Kleene algebra in the style of Software Foundations [https://softwarefoundations.cis.upenn.edu/]
