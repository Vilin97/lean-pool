/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.Antipodal

/-!
# Real projective space as an antipodal quotient

This file defines the first genuinely topological object in the library:

`RP n = S^n / (x ~ -x)`.

Implemented here:

* the antipodal equivalence relation on `Sphere n`;
* `RP n` as the quotient by that relation;
* the quotient projection `proj : Sphere n -> RP n` as a bundled continuous map;
* the quotient-map theorem for `proj`;
* descent of an odd map `f : Sphere n -> Sphere n` to `RP n -> RP n`;
* the basic commutative-square theorem, both pointwise and as a bundled
 continuous-map equality;
* a uniqueness theorem for the descended map;
* the fiber/relation API of `proj`: the membership criterion `proj_eq_iff`,
 the fiber `proj_fiber x = {x, -x}`, and the two-element cardinality of each
 fiber (`proj_fiber_ncard`, `proj_fiber_encard`, `proj_two_sheeted`). These
 depend only on the quotient relation, not on any covering-space machinery, so
 they live here next to the quotient rather than in `Covering.lean`.
-/

noncomputable section

namespace SphereOddDegree

/--
The antipodal relation on the sphere: `x ~ y` iff `x = y` or `x = -y`.
-/
def AntipodalRel {n : ℕ} (x y : Sphere n) : Prop :=
  x = y ∨ x = -y

/-- The antipodal relation is an equivalence relation. -/
instance AntipodalSetoid (n : ℕ) : Setoid (Sphere n) where
  r := AntipodalRel
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro x
      left
      rfl
    · intro x y hxy
      rcases hxy with hxy | hxy
      · left
        exact hxy.symm
      · right
        calc
          y = -(-y) := by simp
          _ = -x := by rw [← hxy]
    · intro x y z hxy hyz
      rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz
      · left
        exact hxy.trans hyz
      · right
        exact hxy.trans hyz
      · right
        calc
          x = -y := hxy
          _ = -z := by rw [hyz]
      · left
        calc
          x = -y := hxy
          _ = -(-z) := by rw [hyz]
          _ = z := by simp

/-- Real projective `n`-space, modeled as `S^n/(x ~ -x)`. -/
abbrev RP (n : ℕ) : Type :=
  Quotient (AntipodalSetoid n)

/-- The quotient projection `S^n -> RP n`. -/
def proj (n : ℕ) : C(Sphere n, RP n) where
  toFun := Quotient.mk'
  continuous_toFun := continuous_quotient_mk'

@[simp]
theorem proj_apply {n : ℕ} (x : Sphere n) :
    proj n x = Quotient.mk' x :=
  rfl

/-- The projection is a quotient map. -/
theorem proj_isQuotientMap (n : ℕ) :
    Topology.IsQuotientMap (proj n : Sphere n → RP n) := by
  exact isQuotientMap_quotient_mk'

/-- The projection identifies antipodal points. -/
theorem proj_neg {n : ℕ} (x : Sphere n) :
    proj n (-x) = proj n x := by
  exact Quotient.sound (Or.inr rfl)

/-- A symmetric version of `proj_neg`. -/
theorem proj_eq_proj_neg {n : ℕ} (x : Sphere n) :
    proj n x = proj n (-x) := by
  exact (proj_neg x).symm

/-! ### Deck transformations (informal sense)

A *deck transformation* of the double cover `proj n : S^n → RP n` is a
self-homeomorphism `φ` of `S^n` with `proj n ∘ φ = proj n`. Mathlib has no
standalone deck-transformation abstraction (no `DeckTransformation`/`deck`
declaration; only `IsCoveringMap` and the quotient-covering API built on
`MulAction`/`ProperlyDiscontinuousSMul`), so we record here only the two
elementary facts that the identity and the antipodal map are deck
transformations of `proj n`, in the bare `proj n ∘ φ = proj n` sense. No
abstract deck-transformation group is introduced. -/

/-- The antipodal map commutes with the projection: `proj n (antipodal n x) =
proj n x`. This is `proj_neg` phrased through the bundled antipodal map, and is
the pointwise statement that the antipodal map is a deck transformation of the
double cover `proj n`. -/
theorem proj_antipodal {n : ℕ} (x : Sphere n) :
    proj n (antipodal n x) = proj n x := by
  simpa using proj_neg x

/-- Bundled form of `proj_antipodal`: precomposing `proj n` with the antipodal
map recovers `proj n`. This is the deck-transformation identity
`proj n ∘ antipodal n = proj n` for the nontrivial deck transformation. -/
theorem proj_comp_antipodal (n : ℕ) :
    (proj n).comp (antipodal n) = proj n := by
  ext x
  exact proj_antipodal x

/-- The identity map is (trivially) a deck transformation of `proj n`:
`proj n ∘ id = proj n`. -/
theorem proj_comp_id (n : ℕ) :
    (proj n).comp (ContinuousMap.id (Sphere n)) = proj n :=
  rfl

/-! ### Induction, recursion, and extensionality

Every point of `RP n` is `proj n x` for some sphere point `x`. The following
lemmas package the standard `Quotient` boilerplate (`Quotient.inductionOn`,
`Quotient.inductionOn₂`, `funext`/`ContinuousMap.ext`) specialized to `proj n`,
so that downstream proofs can reason directly in terms of the projection rather
than the underlying `Quotient.mk'`. -/

/-- Induction principle for `RP n`: to prove a property of every point of
`RP n`, it suffices to prove it for every `proj n x`. -/
@[elab_as_elim]
theorem RP.ind {n : ℕ} {motive : RP n → Prop}
    (h : ∀ x : Sphere n, motive (proj n x)) (q : RP n) : motive q :=
  Quotient.inductionOn q h

/-- Binary induction principle for `RP n`: to prove a property of every pair of
points of `RP n`, it suffices to prove it for pairs `proj n x`, `proj n y`. -/
@[elab_as_elim]
theorem RP.ind₂ {n : ℕ} {motive : RP n → RP n → Prop}
    (h : ∀ x y : Sphere n, motive (proj n x) (proj n y)) (p q : RP n) :
    motive p q :=
  Quotient.inductionOn₂ p q h

/-- Every point of `RP n` is the image under `proj n` of some sphere point. -/
theorem RP.exists_rep {n : ℕ} (q : RP n) : ∃ x : Sphere n, proj n x = q :=
  Quotient.inductionOn q (fun x => ⟨x, rfl⟩)

/-- Extensionality for functions out of `RP n`: two functions agree if they
agree after precomposition with `proj n` (i.e. on all representatives). -/
theorem RP.funext {n : ℕ} {β : Sort*} {f g : RP n → β}
    (h : ∀ x : Sphere n, f (proj n x) = g (proj n x)) : f = g :=
  _root_.funext (RP.ind h)

/-- Extensionality for continuous maps out of `RP n`: two continuous maps are
equal if they agree on all representatives `proj n x`. Tagged `@[ext]`, so the
`ext` tactic reduces a goal `f = g` between maps `C(RP n, β)` directly to the
goal `f (proj n x) = g (proj n x)` on a representative `x : Sphere n`. -/
@[ext]
theorem RP.hom_ext {n : ℕ} {β : Type*} [TopologicalSpace β]
    {f g : C(RP n, β)} (h : ∀ x : Sphere n, f (proj n x) = g (proj n x)) :
    f = g :=
  ContinuousMap.ext (RP.ind h)

/-- The quotient projection is surjective. -/
theorem proj_surjective (n : ℕ) :
    Function.Surjective (proj n) :=
  RP.exists_rep

/-- Equality in `RP n` follows from the antipodal relation upstairs. -/
theorem proj_eq_of_antipodalRel
  {n : ℕ}
  {x y : Sphere n}
  (hxy : AntipodalRel x y) :
  proj n x = proj n y := by
  exact Quotient.sound hxy

/--
If two sphere points are related by the antipodal relation, then their images
under an odd map are again related.
-/
theorem antipodalRel_map_of_isOdd
  {n : ℕ}
  {f : C(Sphere n, Sphere n)}
  (hf : IsOddMap f)
  {x y : Sphere n}
  (hxy : AntipodalRel x y) :
  AntipodalRel (f x) (f y) := by
  rcases hxy with hxy | hxy
  · left
    exact congrArg f hxy
  · right
    calc
      f x = f (-y) := by rw [hxy]
      _ = -f y := hf y

/--
Map on projective space induced by an odd sphere self-map.

This is the formal version of the descent `f` to `bar f` along the quotient
`S^n -> RP n`.
-/
def inducedOnRP
  {n : ℕ}
  (f : C(Sphere n, Sphere n))
  (hf : IsOddMap f) :
  C(RP n, RP n) where
  toFun :=
    Quotient.lift
      (fun x : Sphere n => proj n (f x))
      (by
        intro x y hxy
        exact Quotient.sound (antipodalRel_map_of_isOdd hf hxy))
  continuous_toFun := by
    apply Continuous.quotient_lift
    exact (proj n).continuous.comp f.continuous

/-- Commutativity of the square defining the descended map, pointwise. -/
theorem inducedOnRP_comm
  {n : ℕ}
  (f : C(Sphere n, Sphere n))
  (hf : IsOddMap f) :
  ∀ x : Sphere n,
    inducedOnRP f hf (proj n x) = proj n (f x) := by
  intro x
  rfl

/-- The defining computation rule of the descended map, as a `simp` lemma:
`inducedOnRP f hf (proj n x) = proj n (f x)`. This is the single-point form of
`inducedOnRP_comm`, tagged `@[simp]` so that `simp` automatically pushes the
descended map through `proj n` to the odd map `f` upstairs. -/
theorem inducedOnRP_proj
  {n : ℕ}
  (f : C(Sphere n, Sphere n))
  (hf : IsOddMap f)
  (x : Sphere n) :
  inducedOnRP f hf (proj n x) = proj n (f x) :=
  rfl

/-- Commutativity of the square defining the descended map, as continuous maps. -/
theorem inducedOnRP_comp_proj
  {n : ℕ}
  (f : C(Sphere n, Sphere n))
  (hf : IsOddMap f) :
  (inducedOnRP f hf).comp (proj n) = (proj n).comp f := by
  ext x
  exact inducedOnRP_comm f hf x

/--
The descended map is uniquely determined by the pointwise commutative square.
-/
theorem inducedOnRP_unique
  {n : ℕ}
  {f : C(Sphere n, Sphere n)}
  (hf : IsOddMap f)
  {g : C(RP n, RP n)}
  (hg : ∀ x : Sphere n, g (proj n x) = proj n (f x)) :
  g = inducedOnRP f hf :=
  RP.hom_ext (fun x => (hg x).trans (inducedOnRP_comm f hf x).symm)

/--
The descended map is uniquely determined by the bundled commutative square.
-/
theorem inducedOnRP_unique_comp
  {n : ℕ}
  {f : C(Sphere n, Sphere n)}
  (hf : IsOddMap f)
  {g : C(RP n, RP n)}
  (hg : g.comp (proj n) = (proj n).comp f) :
  g = inducedOnRP f hf := by
  apply inducedOnRP_unique hf
  intro x
  have hfun := congrArg (fun h : C(Sphere n, RP n) => h x) hg
  simpa using hfun

/-- The descent of the identity odd map is the identity on `RP n`. -/
theorem inducedOnRP_id (n : ℕ) :
    inducedOnRP (ContinuousMap.id (Sphere n)) (isOddMap_id n)
      = ContinuousMap.id (RP n) := by
  symm
  apply inducedOnRP_unique (isOddMap_id n)
  intro x
  rfl

/-- Descent is functorial: it sends a composite of odd maps to the composite of
the descended maps. -/
theorem inducedOnRP_comp
    {n : ℕ}
    {f g : C(Sphere n, Sphere n)}
    (hf : IsOddMap f)
    (hg : IsOddMap g) :
    (inducedOnRP g hg).comp (inducedOnRP f hf)
      = inducedOnRP (g.comp f) (hg.comp hf) := by
  apply inducedOnRP_unique (hg.comp hf)
  intro x
  show (inducedOnRP g hg) ((inducedOnRP f hf) (proj n x)) = proj n (g (f x))
  rw [inducedOnRP_comm f hf x, inducedOnRP_comm g hg (f x)]

/-- The descended map depends only on the underlying odd map, not on the chosen
oddness proof: equal odd maps descend to equal maps on `RP n`. (Proof
irrelevance handles the oddness hypotheses, so only the equality `f = g` of the
maps matters.) -/
theorem inducedOnRP_congr
    {n : ℕ}
    {f g : C(Sphere n, Sphere n)}
    (hf : IsOddMap f)
    (hg : IsOddMap g)
    (h : f = g) :
    inducedOnRP f hf = inducedOnRP g hg := by
  subst h
  rfl

/-- The descent of the antipodal map is the identity on `RP n`: the nontrivial
deck transformation `antipodal n` becomes trivial after passing to the quotient,
since `proj n (-x) = proj n x`. This is the descent counterpart of
`proj_comp_antipodal`. -/
theorem inducedOnRP_antipodal (n : ℕ) :
    inducedOnRP (antipodal n) (isOddMap_antipodal n) = ContinuousMap.id (RP n) := by
  symm
  apply inducedOnRP_unique (isOddMap_antipodal n)
  intro x
  exact (proj_antipodal x).symm

/-- The descended map is surjective whenever the odd map it descends from is
surjective. (Surjectivity of `proj n` lets us lift any target point, and the
commuting square `inducedOnRP_comm` transports a preimage upstairs to a preimage
downstairs.) -/
theorem inducedOnRP_surjective
    {n : ℕ}
    {f : C(Sphere n, Sphere n)}
    (hf : IsOddMap f)
    (hsurj : Function.Surjective f) :
    Function.Surjective (inducedOnRP f hf) := by
  intro q
  obtain ⟨y, rfl⟩ := RP.exists_rep q
  obtain ⟨x, rfl⟩ := hsurj y
  exact ⟨proj n x, inducedOnRP_comm f hf x⟩

/-! ### Fibers of the projection

The fiber of `proj n` over `proj n x` is the antipodal pair `{x, -x}`, which
consists of two distinct points. These facts use only the quotient relation
(`Quotient.exact`/`Quotient.sound`, `proj_neg`) together with the sphere-level
fixed-point-free fact `ne_neg_self`; they require no covering-space machinery,
so they belong with the quotient definition rather than in `Covering.lean`. -/

/-- Two sphere points have the same image under `proj n` iff they are equal or
antipodal. This is the membership criterion for the fibers of the quotient
projection. -/
theorem proj_eq_iff {n : ℕ} {x y : Sphere n} :
    proj n y = proj n x ↔ y = x ∨ y = -x :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- Two sphere points have the same image under `proj n` iff they are related by
the antipodal relation. This is `proj_eq_iff` phrased through `AntipodalRel`,
the form that matches the `Setoid` underlying `RP n` (and the converse to
`proj_eq_of_antipodalRel`). -/
theorem proj_eq_iff_antipodalRel {n : ℕ} {x y : Sphere n} :
    proj n x = proj n y ↔ AntipodalRel x y :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- If two sphere points have the same image under `proj n`, then they are equal
or antipodal. -/
theorem eq_or_eq_neg_of_proj_eq {n : ℕ} {x y : Sphere n}
    (h : proj n y = proj n x) : y = x ∨ y = -x :=
  proj_eq_iff.mp h

/-- Membership criterion for the fiber of `proj n` over `proj n x`: a point `y`
lies in the fiber iff it equals `x` or its antipode `-x`. This is the `simp`-form
of `proj_eq_iff` phrased as fiber membership. -/
theorem mem_proj_fiber {n : ℕ} {x y : Sphere n} :
    y ∈ proj n ⁻¹' {proj n x} ↔ y = x ∨ y = -x := by
  rw [Set.mem_preimage, Set.mem_singleton_iff]
  exact proj_eq_iff

/-- The fiber of `proj n` over `proj n x` is exactly the antipodal pair
`{x, -x}`. -/
theorem proj_fiber {n : ℕ} (x : Sphere n) :
    proj n ⁻¹' {proj n x} = {x, -x} := by
  ext y
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_insert_iff]
  constructor
  · intro h
    rcases Quotient.exact h with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  · rintro (rfl | rfl)
    · rfl
    · exact proj_neg x

/-- The fiber of `proj n` over `proj n x` has exactly two elements (`Set.ncard`
version): the antipodal pair `{x, -x}` of two distinct points. -/
theorem proj_fiber_ncard {n : ℕ} (x : Sphere n) :
    (proj n ⁻¹' {proj n x}).ncard = 2 := by
  rw [proj_fiber x]
  exact Set.ncard_pair (ne_neg_self x)

/-- The fiber of `proj n` over `proj n x` has exactly two elements
(`Set.encard` version). -/
theorem proj_fiber_encard {n : ℕ} (x : Sphere n) :
    (proj n ⁻¹' {proj n x}).encard = 2 := by
  rw [proj_fiber x]
  exact Set.encard_pair (ne_neg_self x)

/-- Two-sheetedness of `proj n`, packaged: the fiber over `proj n x` is the
unordered pair `{x, -x}` of two distinct points. -/
theorem proj_two_sheeted {n : ℕ} (x : Sphere n) :
    x ≠ -x ∧ proj n ⁻¹' {proj n x} = {x, -x} :=
  ⟨ne_neg_self x, proj_fiber x⟩

/-- The fiber of `proj n` over `proj n x` is exactly the orbit of `x` under the
two deck transformations (the identity and the antipodal map): the pair
`{id x, antipodal n x} = {x, -x}`. This is `proj_fiber` phrased through the deck
transformations, making explicit that each fiber is a single deck-group orbit. -/
theorem proj_fiber_eq_deck_orbit {n : ℕ} (x : Sphere n) :
    proj n ⁻¹' {proj n x} =
      {ContinuousMap.id (Sphere n) x, antipodal n x} := by
  simpa using proj_fiber x

/-! ### Fibers over arbitrary points

The fiber lemmas above are phrased over `proj n x`, i.e. over a chosen
representative. Since `proj n` is surjective, the same facts hold over an
arbitrary point `q : RP n`: every fiber is the antipodal pair of some
representative and therefore has exactly two elements. These generalizations
still use only the quotient relation. -/

/-- The fiber of `proj n` over an arbitrary point `q : RP n` is the antipodal
pair `{x, -x}` of any representative `x` of `q`. -/
theorem proj_fiber_eq {n : ℕ} {q : RP n} {x : Sphere n} (hx : proj n x = q) :
    proj n ⁻¹' {q} = {x, -x} := by
  subst hx
  exact proj_fiber x

/-- Every fiber of `proj n` has exactly two elements (`Set.ncard` version). -/
theorem proj_fiber_ncard_eq_two {n : ℕ} (q : RP n) :
    (proj n ⁻¹' {q}).ncard = 2 := by
  obtain ⟨x, rfl⟩ := RP.exists_rep q
  exact proj_fiber_ncard x

/-- Every fiber of `proj n` has exactly two elements (`Set.encard` version). -/
theorem proj_fiber_encard_eq_two {n : ℕ} (q : RP n) :
    (proj n ⁻¹' {q}).encard = 2 := by
  obtain ⟨x, rfl⟩ := RP.exists_rep q
  exact proj_fiber_encard x

/-- Every fiber of `proj n` has exactly two elements (`Nat.card` version). -/
theorem proj_fiber_nat_card_eq_two {n : ℕ} (q : RP n) :
    Nat.card (proj n ⁻¹' {q}) = 2 := by
  rw [Nat.card_coe_set_eq]
  exact proj_fiber_ncard_eq_two q

/-- Every fiber of `proj n` is finite (it has exactly two elements). -/
theorem proj_fiber_finite {n : ℕ} (q : RP n) :
    (proj n ⁻¹' {q}).Finite :=
  Set.finite_of_encard_eq_coe (by rw [proj_fiber_encard_eq_two]; rfl)

/-- Fiber extensionality for `proj n`: two fibers coincide iff their base points
in `RP n` are equal. (One direction is `congrArg`; the other uses surjectivity of
`proj n`.) -/
theorem proj_preimage_singleton_eq_iff {n : ℕ} {q₁ q₂ : RP n} :
    proj n ⁻¹' {q₁} = proj n ⁻¹' {q₂} ↔ q₁ = q₂ := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  obtain ⟨x, rfl⟩ := RP.exists_rep q₁
  have hmem : x ∈ proj n ⁻¹' {q₂} := h ▸ Set.mem_preimage.mpr rfl
  exact (Set.mem_singleton_iff.mp (Set.mem_preimage.mp hmem))

/-! ### Action of the descended map on the fibers of the cover

The descended map `inducedOnRP f hf` is, by `inducedOnRP_comp_proj`, the unique
map making the square

```text
S^n --f--> S^n
 | |
proj proj
 ▼ ▼
RP^n -fbar-> RP^n
```

commute. The lemmas below extract from that square the *fiberwise* data that a
pullback-of-covers / monodromy-naturality argument consumes: the odd map `f`
carries the fiber over `q` into the fiber over `fbar q`
(`inducedOnRP_mapsTo_fiber`), the image of a whole fiber is exactly the target
fiber (`inducedOnRP_image_fiber`), and `f` is injective on each (two-element)
fiber (`inducedOnRP_injOn_fiber`). Together these say `f` restricts to a
bijection between the two-element fibers, which is precisely the
base-point-to-base-point compatibility the descended map needs to act on the
canonical double cover. These are pure quotient/point-set facts (they use only
`inducedOnRP_comm`, `proj_fiber`, and the oddness of `f`), so they live here
rather than in `Covering.lean`; no covering-space, classifying-map, or cohomology
machinery is involved. -/

/-- The descended map respects fibers: the odd map `f` carries the fiber over `q`
into the fiber over the descended image `inducedOnRP f hf q`. This is the
fiberwise form of the commuting square `inducedOnRP_comp_proj`, and the basic
input for treating `inducedOnRP f hf` as a map of the double cover by pullback. -/
theorem inducedOnRP_mapsTo_fiber {n : ℕ} (f : C(Sphere n, Sphere n)) (hf : IsOddMap f)
    (q : RP n) :
    Set.MapsTo f (proj n ⁻¹' {q}) (proj n ⁻¹' {inducedOnRP f hf q}) := by
  intro x hx
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
  rw [← hx]
  exact (inducedOnRP_comm f hf x).symm

/-- The image under the odd map `f` of the fiber over `proj n x` is exactly the
fiber over the descended image `inducedOnRP f hf (proj n x)`. Equivalently,
`f {x, -x} = {f x, -f x}`. This is the surjective-on-fibers half of the
statement that `f` restricts to a bijection between the two-element fibers. -/
theorem inducedOnRP_image_fiber {n : ℕ} (f : C(Sphere n, Sphere n)) (hf : IsOddMap f)
    (x : Sphere n) :
    f '' (proj n ⁻¹' {proj n x}) = proj n ⁻¹' {inducedOnRP f hf (proj n x)} := by
  rw [proj_fiber x, inducedOnRP_comm f hf x, proj_fiber (f x), Set.image_pair, hf x]

/-- The odd map `f` is injective on each (two-element) fiber of `proj n`: it
cannot identify the two antipodal points `x` and `-x`, since `f (-x) = -f x ≠
f x`. This is the injective-on-fibers half of the statement that `f` restricts
to a bijection between the two-element fibers. -/
theorem inducedOnRP_injOn_fiber {n : ℕ} (f : C(Sphere n, Sphere n)) (hf : IsOddMap f)
    (x : Sphere n) :
    Set.InjOn f (proj n ⁻¹' {proj n x}) := by
  rw [proj_fiber x]
  intro a ha b hb hab
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rfl
  · rw [hf _] at hab; exact absurd hab (ne_neg_self _)
  · rw [hf _] at hab; exact absurd hab.symm (ne_neg_self _)
  · rfl

/-- The odd map `f` restricts to a *bijection* between the two-element fibers of
the double cover: it maps the fiber over `q` bijectively onto the fiber over the
descended image `inducedOnRP f hf q`. This packages `inducedOnRP_mapsTo_fiber`,
`inducedOnRP_injOn_fiber`, and `inducedOnRP_image_fiber` into a single
`Set.BijOn`, the fiberwise statement that `inducedOnRP f hf` is a map of the
canonical double cover. -/
theorem inducedOnRP_bijOn_fiber {n : ℕ} (f : C(Sphere n, Sphere n)) (hf : IsOddMap f)
    (q : RP n) :
    Set.BijOn f (proj n ⁻¹' {q}) (proj n ⁻¹' {inducedOnRP f hf q}) := by
  obtain ⟨x, rfl⟩ := RP.exists_rep q
  exact ⟨inducedOnRP_mapsTo_fiber f hf (proj n x), inducedOnRP_injOn_fiber f hf x,
    (inducedOnRP_image_fiber f hf x).ge⟩

end SphereOddDegree
