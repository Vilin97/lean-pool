/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.Monodromy
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.InducedOnRPCohomology
public import Mathlib.GroupTheory.Perm.Sign
/-!
# The canonical `ZMod 2` monodromy class of the double cover `S^n → RP n`

toward the canonical degree-one class

```text
α ∈ H¹(RPⁿ; F₂)
```

associated with the double cover `proj n : S^n → RP n`.

## What is honestly constructed here

The covering / monodromy side of Route A is realised as a genuine, fully-proved
group homomorphism

```text
classifyingHom n x : FundamentalGroup (RP n) x →* Multiplicative (ZMod 2)
```

— the **monodromy classifying homomorphism** of the double cover. It is the
composite

```text
π₁(RP n, x) --projMonodromyHom--> Equiv.Perm (proj n ⁻¹' {x})
 --permToZMod2--> Multiplicative (ZMod 2)
```

where `projMonodromyHom` (from `Monodromy.lean`) is the genuine action of the
fundamental group on the two-element fibre, and `permToZMod2` is the parity
(`Equiv.Perm.sign` composed with `ℤˣ ≅ ZMod 2`) of a permutation of a finite
set. On the two-element fibre this parity records exactly whether a loop swaps
the two sheets of the cover, i.e. it *is* the classifying datum of the regular
`ZMod 2`-cover.

This homomorphism is the source datum from which `α` is obtained, in Route A, by
the **degree-one universal coefficient theorem**
`H¹(X; F₂) ≅ Hom(π₁(X)ᵃᵇ, F₂)`. That theorem is **absent** from the pinned
Mathlib, so an honest `α ∈ H¹(RPⁿ; F₂)` cannot yet be produced; this file
therefore stops exactly at the last formalized object before `α`, plus the
`H¹` target abbreviations, with **

## Monodromy → `ZMod 2`

* `intUnitsToZMod2` — the canonical isomorphism `ℤˣ →* Multiplicative (ZMod 2)`.
* `permToZMod2` — the parity homomorphism `Equiv.Perm α →* Multiplicative (ZMod 2)`
 for a finite `α`.
* `classifyingHom n x` — the monodromy classifying homomorphism
 `π₁(RP n, x) →* Multiplicative (ZMod 2)` of the double cover.

## Naturality under descended odd maps

* `classifyingHom_inducedOnRP_naturality` — the descended odd map `fbar` acts
 trivially on the classifying homomorphism:
 `classifyingHom n (fbar x) ∘ (π₁ map fbar) = classifyingHom n x`. This is the
 fundamental-group form of the eventual `fbar^*(α) = α`.
-/

@[expose] public section

noncomputable section

namespace SphereOddDegree

open CategoryTheory

/-! ## Target abbreviations: `H¹(RP n; F₂)` -/

/-- The genuine degree-one mod-2 singular cohomology object `H¹(RP n; F₂)` of
real projective space, which contains the canonical class `α`. -/
noncomputable abbrev rpH1ZMod2 (n : ℕ) : ModuleCat.{0} (ZMod 2) := rpCohomology n 1

/-- Verbose alias for `rpH1ZMod2`: the degree-one mod-2 cohomology of `RP n`. -/
noncomputable abbrev rpDegreeOneCohomology (n : ℕ) : ModuleCat.{0} (ZMod 2) :=
  rpCohomology n 1

/-! ## The parity homomorphism `Equiv.Perm α →* Multiplicative (ZMod 2)` -/

/-- The canonical group isomorphism `ℤˣ →* Multiplicative (ZMod 2)` sending the
trivial unit `1` to `0` and `-1` to `1`. Both groups are cyclic of order two;
this is the homomorphism underlying the `sign`-parity of a permutation. -/
def intUnitsToZMod2 : ℤˣ →* Multiplicative (ZMod 2) where
  toFun u := Multiplicative.ofAdd (if u = 1 then (0 : ZMod 2) else 1)
  map_one' := by simp
  map_mul' u v := by
    rcases Int.units_eq_one_or u with hu | hu <;>
      rcases Int.units_eq_one_or v with hv | hv <;>
      subst hu <;> subst hv <;> decide

@[simp] theorem intUnitsToZMod2_one : intUnitsToZMod2 1 = 1 := by decide

@[simp] theorem intUnitsToZMod2_neg_one :
    intUnitsToZMod2 (-1) = Multiplicative.ofAdd (1 : ZMod 2) := by decide

/-- The parity homomorphism of a permutation of a finite type, valued in
`Multiplicative (ZMod 2)`: it is `Equiv.Perm.sign` followed by the isomorphism
`ℤˣ ≅ Multiplicative (ZMod 2)`. For a two-element type this is an isomorphism
recording whether the permutation is the identity or the transposition. -/
noncomputable def permToZMod2 {α : Type*} [Finite α] :
    Equiv.Perm α →* Multiplicative (ZMod 2) :=
  letI := Fintype.ofFinite α
  letI := Classical.decEq α
  intUnitsToZMod2.comp Equiv.Perm.sign

/-- `permToZMod2` is invariant under transporting a permutation along an
equivalence of finite types (parity is a conjugation invariant). This is the
algebraic engine of the descended-map naturality of `classifyingHom`. -/
theorem permToZMod2_permCongr {α β : Type*} [Finite α] [Finite β]
    (e : α ≃ β) (p : Equiv.Perm α) :
    permToZMod2 (e.permCongr p) = permToZMod2 p := by
  classical
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  simp only [permToZMod2, MonoidHom.coe_comp, Function.comp_apply]
  rw [Equiv.Perm.sign_permCongr]

/-! ## Faithfulness of the parity character on a two-point fibre

On a *two-element* type the parity homomorphism `permToZMod2` is not merely a
homomorphism but a **bijection**: there are exactly two permutations of a
two-element set (the identity and the swap) and exactly two values in `ZMod 2`,
and parity distinguishes them. This is the canonical, choice-free identification
`Equiv.Perm α ≃* Multiplicative (ZMod 2)` for `Nat.card α = 2` underlying the
`ZMod 2`-valued monodromy character: it shows the character loses no information
about the two-sheet monodromy. -/

/-- The unit isomorphism `ℤˣ →* Multiplicative (ZMod 2)` is injective (indeed it
is an isomorphism of the two cyclic groups of order two). -/
theorem intUnitsToZMod2_injective : Function.Injective intUnitsToZMod2 := by
  intro u v h
  rcases Int.units_eq_one_or u with hu | hu <;> rcases Int.units_eq_one_or v with hv | hv <;>
    subst hu <;> subst hv <;> first | rfl | (exfalso; revert h; decide)

/-- A two-element type is exhausted by two distinct elements: there exist
`a ≠ b` such that every element equals `a` or `b`. -/
theorem card_two_elim {α : Type*} [Finite α] (h : Nat.card α = 2) :
    ∃ a b : α, a ≠ b ∧ ∀ x, x = a ∨ x = b := by
  classical
  let := Fintype.ofFinite α
  have hcard : (Finset.univ : Finset α).card = 2 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h
  obtain ⟨a, b, hab, huniv⟩ := Finset.card_eq_two.mp hcard
  refine ⟨a, b, hab, fun x => ?_⟩
  have : x ∈ ({a, b} : Finset α) := huniv ▸ Finset.mem_univ x
  simpa using this

/-- **Every permutation of a two-point set is either the identity or the swap.**
Phrased without `DecidableEq`: a permutation of a type with exactly two elements
is either the identity or fixed-point-free (and a fixed-point-free permutation of
a two-element set is exactly the transposition of its two elements). -/
theorem perm_two_eq_one_or_fixedpointfree {α : Type*} [Finite α] (h : Nat.card α = 2)
    (p : Equiv.Perm α) : p = 1 ∨ ∀ x, p x ≠ x := by
  classical
  obtain ⟨a, b, hab, hall⟩ := card_two_elim h
  rcases hall (p a) with ha | ha
  · left
    have hpb : p b = b := by
      rcases hall (p b) with hb | hb
      · exact absurd (p.injective (hb.trans ha.symm)) hab.symm
      · exact hb
    ext x
    rcases hall x with hx | hx <;> subst hx <;> simp [ha, hpb]
  · right
    have hpb : p b = a := by
      rcases hall (p b) with hb | hb
      · exact hb
      · exact absurd (p.injective (ha.trans hb.symm)) hab
    intro x
    rcases hall x with hx | hx <;> subst hx
    · rw [ha]; exact hab.symm
    · rw [hpb]; exact hab

/-- On a two-element type the parity homomorphism `permToZMod2` is injective. -/
theorem permToZMod2_injective {α : Type*} [Finite α] (h : Nat.card α = 2) :
    Function.Injective (permToZMod2 (α := α)) := by
  classical
  let := Fintype.ofFinite α
  have hcard : Fintype.card α = 2 := by rw [← Nat.card_eq_fintype_card]; exact h
  have hsign : Function.Bijective (Equiv.Perm.sign (α := α)) := by
    rw [Fintype.bijective_iff_surjective_and_card]
    have : Nontrivial α := by rw [← Fintype.one_lt_card_iff_nontrivial, hcard]; norm_num
    refine ⟨Equiv.Perm.sign_surjective α, ?_⟩
    rw [Fintype.card_perm, hcard]; decide
  change Function.Injective (intUnitsToZMod2 ∘ Equiv.Perm.sign)
  exact intUnitsToZMod2_injective.comp hsign.injective

/-- On a two-element type the parity character is trivial exactly on the identity
permutation: `permToZMod2 p = 1 ↔ p = 1`. -/
theorem permToZMod2_eq_one_iff {α : Type*} [Finite α] (h : Nat.card α = 2)
    (p : Equiv.Perm α) : permToZMod2 p = 1 ↔ p = 1 := by
  refine ⟨fun hp => permToZMod2_injective h ?_, fun hp => by rw [hp, map_one]⟩
  rw [hp, map_one]

/-- **The canonical identification of the two-point permutation group with
`ZMod 2`.** For a type `α` with exactly two elements, the parity homomorphism
`permToZMod2` is a group isomorphism `Equiv.Perm α ≃* Multiplicative (ZMod 2)`.
This is choice-free (no labelling of the two points is needed): it is the
canonical reason a `ZMod 2`-valued monodromy character exists for the double
cover, since each fibre of `proj n` is a two-element set. -/
noncomputable def permTwoMulEquivZMod2 {α : Type*} [Finite α] (h : Nat.card α = 2) :
    Equiv.Perm α ≃* Multiplicative (ZMod 2) := by
  classical
  letI := Fintype.ofFinite α
  refine MulEquiv.ofBijective (permToZMod2 (α := α)) ?_
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨permToZMod2_injective h, ?_⟩
  rw [Fintype.card_perm, ← Nat.card_eq_fintype_card, h]; decide

@[simp] theorem permTwoMulEquivZMod2_apply {α : Type*} [Finite α] (h : Nat.card α = 2)
    (p : Equiv.Perm α) : permTwoMulEquivZMod2 h p = permToZMod2 p := rfl

/-! ## The monodromy classifying homomorphism `π₁(RP n) →* ZMod 2` -/

/-- Every fibre of `proj n` is a finite type (it has two elements). -/
instance projFiberFinite (n : ℕ) (x : RP n) : Finite (proj n ⁻¹' {x}) :=
  (proj_fiber_finite x).to_subtype

/-- The **monodromy classifying homomorphism** of the double cover
`proj n : S^n → RP n`: the action of the fundamental group `π₁(RP n, x)` on the
two-element fibre over `x`, composed with the permutation parity into
`Multiplicative (ZMod 2)`. A loop maps to `1` iff its monodromy swaps the two
sheets of the cover.

This is the genuine covering-theoretic datum from which the canonical class
`α ∈ H¹(RP n; F₂)` is obtained, via a degree-one cohomological classifier `H¹(X; F₂) ≅ Hom(π₁(X)ᵃᵇ,
F₂)`. It is a proved homomorphism out of `π₁(RP n, x)`. -/
noncomputable def classifyingHom (n : ℕ) (x : RP n) :
    FundamentalGroup (RP n) x →* Multiplicative (ZMod 2) :=
  permToZMod2.comp (projMonodromyHom n x)

/-- The classifying homomorphism applied to a class is the parity of its
monodromy permutation on the fibre. -/
theorem classifyingHom_apply (n : ℕ) (x : RP n) (a : FundamentalGroup (RP n) x) :
    classifyingHom n x a =
      permToZMod2 (projMonodromyPerm n (FundamentalGroup.toPath a)) :=
  rfl

/-! ## The two-sheet dichotomy and faithfulness of the classifying character

Because every fibre of `proj n` has exactly two elements
(`proj_fiber_nat_card_eq_two`), the abstract two-point facts above apply to the
monodromy permutation of a loop: it either fixes both sheets (trivial monodromy)
or swaps them, and the `ZMod 2`-valued classifying character records exactly
this dichotomy with no loss of information. -/

/-- **Two-sheet dichotomy of the monodromy.** For a loop `γ` at `x`, the
monodromy permutation of the two-element fibre is either the identity (the loop
preserves both sheets of the cover) or fixed-point-free (the loop swaps the two
sheets). This is `perm_two_eq_one_or_fixedpointfree` applied to the fibre, whose
cardinality is two. -/
theorem projMonodromyPerm_eq_one_or_swaps (n : ℕ) {x : RP n}
    (γ : Path.Homotopic.Quotient x x) :
    projMonodromyPerm n γ = 1 ∨ ∀ e, projMonodromyPerm n γ e ≠ e :=
  perm_two_eq_one_or_fixedpointfree (proj_fiber_nat_card_eq_two x) (projMonodromyPerm n γ)

/-- **Faithfulness of the classifying character.** The classifying character is
trivial on a class `a` iff the monodromy permutation of its underlying loop is
the identity: the `ZMod 2` value loses no information about the two-sheet
monodromy. (This uses `permToZMod2_eq_one_iff` on the two-element fibre.) -/
theorem classifyingHom_eq_one_iff (n : ℕ) (x : RP n) (a : FundamentalGroup (RP n) x) :
    classifyingHom n x a = 1 ↔ projMonodromyHom n x a = 1 := by
  rw [classifyingHom, MonoidHom.comp_apply,
    permToZMod2_eq_one_iff (proj_fiber_nat_card_eq_two x)]

/-- The classifying character is *nontrivial* on a class `a` iff the monodromy of
its underlying loop swaps the two sheets, i.e. it is fixed-point-free on the
fibre. This is the loop-level meaning of `classifyingHom n x a ≠ 1`. -/
theorem classifyingHom_ne_one_iff (n : ℕ) (x : RP n) (a : FundamentalGroup (RP n) x) :
    classifyingHom n x a ≠ 1 ↔ ∀ e, projMonodromyPerm n (FundamentalGroup.toPath a) e ≠ e := by
  rw [Ne, classifyingHom_eq_one_iff, projMonodromyHom_apply]
  constructor
  · intro hne
    rcases projMonodromyPerm_eq_one_or_swaps n (FundamentalGroup.toPath a) with h1 | hfpf
    · exact absurd h1 hne
    · exact hfpf
  · intro hfpf hp
    have hne : Nonempty (proj n ⁻¹' {x}) :=
      (Nat.card_ne_zero.mp (by rw [proj_fiber_nat_card_eq_two]; norm_num)).1
    obtain ⟨e⟩ := hne
    exact hfpf e (by rw [hp]; rfl)

/-! ## Naturality of the classifying homomorphism under descended odd maps -/

/-- The fibrewise map `inducedOnRPFiberMap` of an odd map `f` is bijective: an
odd map restricts to a bijection between the two-element fibres of the double
cover. -/
theorem inducedOnRPFiberMap_bijective (n : ℕ) (f : C(Sphere n, Sphere n)) (hf : IsOddMap f)
    (q : RP n) : Function.Bijective (@inducedOnRPFiberMap n f hf q) := by
  refine ⟨fun x y hxy => Subtype.ext ?_, fun y => ?_⟩
  · exact (inducedOnRP_bijOn_fiber f hf q).injOn x.2 y.2
      (by simpa using Subtype.ext_iff.mp hxy)
  · obtain ⟨z, hz, hfz⟩ := (inducedOnRP_bijOn_fiber f hf q).surjOn y.2
    exact ⟨⟨z, hz⟩, Subtype.ext (by simpa using hfz)⟩

/-- The fibrewise map of an odd map `f`, packaged as an equivalence between the
two-element fibre over `q` and the fibre over the descended image
`inducedOnRP f hf q`. -/
noncomputable def inducedOnRPFiberEquiv (n : ℕ) (f : C(Sphere n, Sphere n)) (hf : IsOddMap f)
    (q : RP n) : (proj n ⁻¹' {q}) ≃ (proj n ⁻¹' {inducedOnRP f hf q}) :=
  Equiv.ofBijective _ (inducedOnRPFiberMap_bijective n f hf q)

@[simp] theorem inducedOnRPFiberEquiv_apply (n : ℕ) (f : C(Sphere n, Sphere n)) (hf : IsOddMap f)
    {q : RP n} (e : proj n ⁻¹' {q}) :
    inducedOnRPFiberEquiv n f hf q e = inducedOnRPFiberMap n f hf e := rfl

/-- The descended-loop monodromy permutation is the conjugate of the base-loop
monodromy permutation by the fibre equivalence of the odd map: for a loop `γ` at
`x`,
`projMonodromyPerm (γ.map fbar) = (fibreEquiv).permCongr (projMonodromyPerm γ)`. -/
theorem projMonodromyPerm_map_eq_permCongr (n : ℕ) (f : C(Sphere n, Sphere n)) (hf : IsOddMap f)
    {x : RP n} (γ : Path.Homotopic.Quotient x x) :
    projMonodromyPerm n (γ.map ⟨inducedOnRP f hf, (inducedOnRP f hf).continuous⟩)
      = (inducedOnRPFiberEquiv n f hf x).permCongr (projMonodromyPerm n γ) := by
  refine Equiv.ext fun y => ?_
  obtain ⟨z, rfl⟩ := (inducedOnRPFiberEquiv n f hf x).surjective y
  change projMonodromyPerm n (γ.map ⟨inducedOnRP f hf, (inducedOnRP f hf).continuous⟩)
      (inducedOnRPFiberMap n f hf z)
    = (inducedOnRPFiberEquiv n f hf x).permCongr (projMonodromyPerm n γ)
        (inducedOnRPFiberEquiv n f hf x z)
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, inducedOnRPFiberEquiv_apply]
  exact (inducedOnRPFiberMap_projMonodromyPerm n f hf γ z).symm

/-- **Naturality of the classifying homomorphism under a descended odd map.**
The descended odd map `fbar = inducedOnRP f hf` acts trivially on the monodromy
classifying homomorphism: precomposing the classifying homomorphism at `fbar x`
with the induced map on `π₁` recovers the classifying homomorphism at `x`,
```text
classifyingHom n (fbar x) ∘ (π₁ map fbar) = classifyingHom n x.
```
This is the fundamental-group form of the eventual cohomological identity
`fbar^*(α) = α`: the parity of a loop's monodromy is preserved by the descended
odd map, because `f` restricts to a bijection of fibres and parity is a
conjugation invariant. -/
theorem classifyingHom_inducedOnRP_naturality (n : ℕ) (f : C(Sphere n, Sphere n))
    (hf : IsOddMap f) (x : RP n) :
    (classifyingHom n (inducedOnRP f hf x)).comp
        (FundamentalGroup.map ⟨inducedOnRP f hf, (inducedOnRP f hf).continuous⟩ x)
      = classifyingHom n x := by
  refine MonoidHom.ext (fun a => ?_)
  rw [MonoidHom.comp_apply, classifyingHom_apply, classifyingHom_apply]
  change permToZMod2 (projMonodromyPerm n
      ((FundamentalGroup.toPath a).map ⟨inducedOnRP f hf, (inducedOnRP f hf).continuous⟩))
    = permToZMod2 (projMonodromyPerm n (FundamentalGroup.toPath a))
  rw [projMonodromyPerm_map_eq_permCongr n f hf]
  exact permToZMod2_permCongr (inducedOnRPFiberEquiv n f hf x) (projMonodromyPerm n a.toPath)

end SphereOddDegree
