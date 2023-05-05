<!--
```agda
open import Cat.Displayed.Univalence.Thin
open import Cat.Prelude
```
-->

```agda
module Order.Base where
```

# Partially ordered sets

A **poset** (short for **p**artially **o**rdered set) is a \r{set}
equipped with a relation $x \le y$ which is reflexive, transitive and
antisymmetric. Put another way, a poset is a [univalent] \r{category}
having at most one morphism between each pair of elements.

For convenience reasons, we prefer _not_ to work with the category
generated by a poset: the category associated with a poset reifies a lot
of _redundant_ information, which is necessary when working with
$\hom$-sets, but not with $\hom$-props. Working with the generated
category is analogous to only ever working with locally discrete
bicategories: you _could_, but then you'd be hauling around a bunch of
redundant information.

[univalent]: Cat.Univalent.html

Another reason to define posets as their own concept, rather than as a
special case of categories, is using our pre-existing infrastructure for
constructing very convenient categories of sets-with-structure; In this
case, sets with "po" structure!

We start by defining the _predicate_ `is-partial-order`{.Agda} on a
relation $x \le y$. That it turns out to be a predicate is actually
slightly nontrivial: The first four components are manifestly
propositional, but the last component --- the witness of antisymmetry
--- could really gunk things up, since it has the potential to assign
loops! But, given any antisymmetric relation $x \le y$, the family

$$
(x, y) \mapsto (x \le y) \land (y \le x)
$$

is an identity system^[Together with the unique evidence that this is a
reflexive relation] on $A$; and, being a product of propositions, it's
also a proposition, so $A$ is automatically a set.

```agda
record is-partial-order {ℓ ℓ′} {A : Type ℓ}
          (_≤_ : A → A → Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  no-eta-equality
  field
    ≤-thin    : ∀ {x y} → is-prop (x ≤ y)
    ≤-refl    : ∀ {x} → x ≤ x
    ≤-trans   : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    ≤-antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y

  has-is-set : is-set A
  has-is-set =
    identity-system→hlevel 1
      {r = λ _ → ≤-refl , ≤-refl}
      (set-identity-system
        (λ a b → ×-is-hlevel 1 ≤-thin ≤-thin)
        (λ {a} {b} (p , q) → ≤-antisym {a} {b} p q))
      (λ a b → ×-is-hlevel 1 ≤-thin ≤-thin)
```

<!--
```agda
private unquoteDecl eqv = declare-record-iso eqv (quote is-partial-order)

is-partial-order-is-prop
  : ∀ {ℓ ℓ′} {A : Type ℓ} (R : A → A → Type ℓ′) → is-prop (is-partial-order R)
is-partial-order-is-prop {A = A} R x y = go x x y where
  go : is-partial-order R → is-prop (is-partial-order R)
  go x = Iso→is-hlevel 1 eqv (hlevel 1) where instance
    h-level-r : ∀ {x y} {n} → H-Level (R x y) (suc n)
    h-level-r = prop-instance (x .is-partial-order.≤-thin)

    h-level-a : H-Level A 2
    h-level-a = basic-instance 2 (is-partial-order.has-is-set x)
```
-->

A po structure on a set --- okay, that joke _is_ getting old --- is
given by tupling together the relation $x \le y$ together with a proof
that it is a partial order relation. Identity of poset structures is
thus determined by identity _of the relations_, since being a partial
order is a proposition.

```agda
record Poset-on {ℓ} ℓ′ (A : Type ℓ) : Type (ℓ ⊔ lsuc ℓ′) where
  no-eta-equality
  field
    _≤_          : A → A → Type ℓ′
    has-is-poset : is-partial-order _≤_
  open is-partial-order has-is-poset public
```

We set up the category of posets using our [machinery for displaying]
[univalent categories] over the category of sets. A map between posets
is called a **monotone map**: it's the decategorification of a functor.
We don't need preservation of identities _or_ preservation of
composites, since our "homs" are propositions!

[machinery for displaying]: Cat.Displayed.Univalence.Thin.html
[univalent categories]: Cat.Univalent.html

```agda
Poset-structure : ∀ ℓ ℓ′ → Thin-structure {ℓ = ℓ} (ℓ ⊔ ℓ′) (Poset-on ℓ′)
∣ Poset-structure ℓ ℓ′ .is-hom f P Q ∣ =
  ∀ x y → Poset-on._≤_ P x y → Poset-on._≤_ Q (f x) (f y)

Poset-structure ℓ ℓ′ .is-hom f P Q .is-tr =
  Π-is-hlevel³ 1 λ _ _ _ → Poset-on.≤-thin Q

Poset-structure ℓ ℓ′ .id-is-hom x y α = α
Poset-structure ℓ ℓ′ .∘-is-hom f g α β x y γ = α (g x) (g y) (β x y γ)
```

The last thing we have to prove is "uniqueness of identity maps": If we
have the identity being a monotone map $(a, t) \to (a, s)$ _and_ $(a, s)
\to (a, t)$ --- that is, we have $(x \le_s y) \leftrightarrow (x \le_t
y)$ --- then, by propositional extensionality, we have $\le_s = \le_t$.
Then, since equality of poset structures is controlled by equality of
the relations, we have $s = t$!

```agda
Poset-structure ℓ ℓ′ .id-hom-unique {s = s} {t = t} α β = q where
  module s = Poset-on s
  module t = Poset-on t
  open is-iso

  p : s._≤_ ≡ t._≤_
  p i x y = ua (prop-ext s.≤-thin t.≤-thin (α x y) (β x y)) i

  q : s ≡ t
  q i .Poset-on._≤_ = p i
  q i .Poset-on.has-is-poset = is-prop→pathp
    (λ i → is-partial-order-is-prop (p i))
    s.has-is-poset t.has-is-poset i
```

<!--
```agda
Posets : ∀ ℓ ℓ′ → Precategory (lsuc (ℓ ⊔ ℓ′)) (ℓ ⊔ ℓ′)
Posets ℓ ℓ′ = Structured-objects (Poset-structure ℓ ℓ′)

module Posets {ℓ ℓ′} = Precategory (Posets ℓ ℓ′)
Poset : (ℓ ℓ′ : Level) → Type (lsuc (ℓ ⊔ ℓ′))
Poset ℓ ℓ′ = Precategory.Ob (Posets ℓ ℓ′)

record make-poset {ℓ} ℓ′ (A : Type ℓ) : Type (ℓ ⊔ lsuc ℓ′) where
  no-eta-equality

  field
    rel     : A → A → Type ℓ′
    id      : ∀ {x} → rel x x
    thin    : ∀ {x y} → is-prop (rel x y)
    trans   : ∀ {x y z} → rel x y → rel y z → rel x z
    antisym : ∀ {x y} → rel x y → rel y x → x ≡ y

  to-poset-on : Poset-on ℓ′ A
  to-poset-on .Poset-on._≤_ = rel
  to-poset-on .Poset-on.has-is-poset .is-partial-order.≤-thin = thin
  to-poset-on .Poset-on.has-is-poset .is-partial-order.≤-refl = id
  to-poset-on .Poset-on.has-is-poset .is-partial-order.≤-trans = trans
  to-poset-on .Poset-on.has-is-poset .is-partial-order.≤-antisym = antisym

to-poset : ∀ {ℓ ℓ′} (A : Type ℓ) → make-poset ℓ′ A → Poset ℓ ℓ′
∣ to-poset A mk .fst ∣ = A
to-poset A mk .fst .is-tr = Poset-on.has-is-set (make-poset.to-poset-on mk)
to-poset A mk .snd = make-poset.to-poset-on mk
```
-->

The relationship between posets and (strict) categories is outlined in
the module [`Order.Cat`](Order.Cat.html). Very similarly to
categories, posets have a duality involution. In fact, under the
correspondence between posets and thin categories, these are the same
construction.

```agda
_^opp : ∀ {ℓ ℓ′} → Poset ℓ ℓ′ → Poset ℓ ℓ′
P ^opp = to-poset ⌞ P ⌟ λ where
    .make-poset.rel x y         → y ≤ x
    .make-poset.thin            → ≤-thin
    .make-poset.id              → ≤-refl
    .make-poset.trans f<g g<h   → ≤-trans g<h f<g
    .make-poset.antisym f<g g<f → ≤-antisym g<f f<g
  where open Poset-on (P .snd)
```