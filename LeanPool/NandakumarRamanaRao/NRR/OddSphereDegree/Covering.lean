/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.RealProjectiveSpace
public import Mathlib.Topology.Covering.Quotient

/-!
# The antipodal quotient is a covering map

This file establishes that the projection `proj n : S^n → RP n` is a covering
map: the canonical double cover of real projective space by the sphere.

The argument uses the fact that the cyclic group
`DeckGroup = Multiplicative (ZMod 2)` acts freely and (because it is finite
acting on a Hausdorff space) properly discontinuously on the sphere by the
antipodal involution, whose orbit relation is exactly the relation defining
`RP n`. Mathlib's
`MulAction.isQuotientCoveringMap_of_properlyDiscontinuousSMul`
then yields that the quotient projection is a covering map.

## Main results

* `proj_isCoveringMap` — `proj n` is a covering map;
* `proj_isLocalHomeomorph` — hence a local homeomorphism;
* `proj_isCoveringMap_two_sheeted` — `proj n` is a covering map *and* every
 fiber has exactly two elements (the "canonical double cover" packaged).

These covering-theoretic statements are the only public declarations of this
file.

The purely quotient-relation facts about the fibers of `proj n` (the membership
criterion `proj_eq_iff`, the fiber `proj_fiber x = {x, -x}`, and its
two-element cardinality `proj_fiber_ncard`/`proj_fiber_encard`/`proj_two_sheeted`)
live in `RealProjectiveSpace.lean`, since they need no covering-space machinery.

## Implementation notes

`DeckGroup` is the order-two deck-transformation group of the cover. We model
it as `Multiplicative (ZMod 2)` so that it is a genuine (multiplicative) group
and `MulAction`/`IsCancelSMul` apply directly.

The antipodal deck action of `DeckGroup` on `Sphere n` is pure scaffolding: it
exists only to discharge, by typeclass search, the hypotheses of the Mathlib
quotient-covering lemma at the one call site below. Nothing outside this file
consumes it, so the action (`DeckGroup`, the `SMul`/`MulAction`/
`ContinuousConstSMul`/`IsCancelSMul` instances, their defining equations, and the
orbit criterion `proj_eq_iff_mem_orbit`) is kept *out of the public surface*:
the four typeclass facts are `local instance`s (so they never pollute global
typeclass resolution downstream), and the supporting `abbrev`/lemmas are
`private`. The genuinely covering-theoretic public API is exactly
`proj_isCoveringMap` and `proj_isLocalHomeomorph`.
-/

@[expose] public section

noncomputable section

namespace SphereOddDegree

/-! ### The antipodal deck-transformation action

The order-two group `DeckGroup` acts on `Sphere n` by the antipodal involution.
These `local instance`s supply exactly the hypotheses (`MulAction`,
`ContinuousConstSMul`, `IsCancelSMul`) that the Mathlib quotient-covering lemma
discharges by typeclass search. They are local to this file: the action is only
needed to invoke that lemma, and is not part of the covering API. -/

/-- The deck-transformation group of the double cover `S^n → RP n`: the
order-two group, modeled as `Multiplicative (ZMod 2)`, acting on the sphere by
the antipodal map. Internal scaffolding for `proj_isCoveringMap`. -/
private abbrev DeckGroup : Type := Multiplicative (ZMod 2)

/-- The antipodal action of `DeckGroup` on `S^n`: the nontrivial element
negates. -/
private local instance antipodalSMul (n : ℕ) : SMul DeckGroup (Sphere n) where
  smul g x := if Multiplicative.toAdd g = 0 then x else -x

/-- The defining equation of the antipodal `DeckGroup`-action. -/
private theorem antipodalSMul_def {n : ℕ} (g : DeckGroup) (x : Sphere n) :
    g • x = if Multiplicative.toAdd g = 0 then x else -x := rfl

private theorem antipodalSMul_one {n : ℕ} (x : Sphere n) :
    (1 : DeckGroup) • x = x := by
  change (if Multiplicative.toAdd (1 : DeckGroup) = 0 then x else -x) = x
  rfl

/-- The antipodal `DeckGroup`-action on `S^n`. -/
private local instance antipodalMulAction (n : ℕ) : MulAction DeckGroup (Sphere n) where
  one_smul := by exact antipodalSMul_one
  mul_smul := by
    intro x y b
    fin_cases x <;> fin_cases y <;> simp +decide [antipodalSMul_def]

/-- The antipodal action is by homeomorphisms (each element acts continuously). -/
private local instance antipodalContinuousConstSMul (n : ℕ) :
    ContinuousConstSMul DeckGroup (Sphere n) where
  continuous_const_smul := by
    intro g
    by_cases hg : Multiplicative.toAdd g = 0
    · have : (g • · : Sphere n → Sphere n) = id := by
        ext x
        simp [antipodalSMul_def, hg]
      rw [this]
      exact continuous_id
    · have : (g • · : Sphere n → Sphere n) = fun x => -x := by
        ext x
        simp [antipodalSMul_def, hg]
      rw [this]
      exact continuous_neg

/-- The antipodal action is free (cancellative): no point on the unit sphere is
fixed by the nontrivial element. -/
private local instance antipodalIsCancelSMul (n : ℕ) : IsCancelSMul DeckGroup (Sphere n) where
  left_cancel' := by
    intro a b c h
    fin_cases a <;> simp_all +decide
  right_cancel' := by
    intro a b c h
    fin_cases a <;> fin_cases b <;> simp_all? +decide [antipodalSMul_def] <;>
      first
        | exact absurd h (ne_neg_of_mem_unit_sphere ℝ c)
        | exact absurd h.symm (ne_neg_of_mem_unit_sphere ℝ c)

/-! ### The covering map -/

/-- Two sphere points have the same image in `RP n` iff they lie in the same
antipodal orbit; equivalently the orbit of `x` is `{x, -x}`. Internal: this is
the orbit-relation input to the Mathlib quotient-covering lemma. -/
private theorem proj_eq_iff_mem_orbit {n : ℕ} {x y : Sphere n} :
    proj n x = proj n y ↔ x ∈ MulAction.orbit DeckGroup y := by
  rw [proj_eq_iff_antipodalRel]
  constructor <;> intro h
  · rcases h with rfl | rfl
    · exact ⟨1, antipodalSMul_one x⟩
    · refine ⟨Multiplicative.ofAdd (1 : ZMod 2), ?_⟩
      dsimp
      have h1 : Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2)) = 1 := rfl
      have hne : (1 : ZMod 2) ≠ 0 := by decide
      rw [antipodalSMul_def, h1]
      simp [hne]
  · obtain ⟨g, hg⟩ := h
    dsimp at hg
    have hg_cases : ∀ g : DeckGroup, g = 1 ∨ g = Multiplicative.ofAdd (1 : ZMod 2) := by decide
    rcases hg_cases g with rfl | rfl
    · left
      rw [antipodalSMul_one] at hg
      exact hg.symm
    · right
      have h1 : Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2)) = 1 := rfl
      have hne : (1 : ZMod 2) ≠ 0 := by decide
      have : (Multiplicative.ofAdd (1 : ZMod 2)) • y = -y := by
        rw [antipodalSMul_def, h1]
        simp [hne]
      rw [this] at hg
      exact hg.symm

/-- The projection `proj n : S^n → RP n` is a covering map: the canonical double
cover of real projective space by the sphere. -/
theorem proj_isCoveringMap (n : ℕ) :
    IsCoveringMap (proj n : Sphere n → RP n) := by
  have h := (proj_isQuotientMap n).isQuotientCoveringMap_of_properlyDiscontinuousSMul
    (G := DeckGroup) (fun {e₁ e₂} => proj_eq_iff_mem_orbit)
  exact ((isQuotientCoveringMap_iff_isCoveringMap_and (proj n) DeckGroup).mp h).1

/-- The projection `proj n` is a local homeomorphism. -/
theorem proj_isLocalHomeomorph (n : ℕ) :
    IsLocalHomeomorph (proj n : Sphere n → RP n) :=
  (proj_isCoveringMap n).isLocalHomeomorph

/-! ### Local-homeomorphism consequences

The following are the standard consequences of `proj n` being a covering map /
local homeomorphism, specialised to the canonical double cover. -/

/-- `proj n` maps the neighborhood filter of `x` isomorphically onto the
neighborhood filter of `proj n x`: `(𝓝 x).map (proj n) = 𝓝 (proj n x)`. A direct
consequence of `proj n` being a local homeomorphism. -/
theorem proj_map_nhds_eq {n : ℕ} (x : Sphere n) :
    Filter.map (proj n) (nhds x) = nhds (proj n x) :=
  (proj_isLocalHomeomorph n).map_nhds_eq x

/-- `proj n` is locally injective: every point has a neighborhood on which the
projection is injective. A consequence of `proj n` being a local
homeomorphism. -/
theorem proj_isLocallyInjective (n : ℕ) :
    IsLocallyInjective (proj n : Sphere n → RP n) :=
  (proj_isLocalHomeomorph n).isLocallyInjective

/-- The fibers of the covering map `proj n` are discrete: each (two-element)
fiber `proj n ⁻¹' {q}` carries the discrete subspace topology. This is the
characteristic discreteness of fibers of a covering map; here it follows from
finiteness of the fiber in the Hausdorff sphere. -/
theorem proj_fiber_discreteTopology {n : ℕ} (q : RP n) :
    DiscreteTopology (proj n ⁻¹' {q} : Set (Sphere n)) :=
  have : Finite (proj n ⁻¹' {q} : Set (Sphere n)) := (proj_fiber_finite q).to_subtype
  inferInstance

/-- The projection `proj n : S^n → RP n` is a two-sheeted covering map: it is a
covering map and every fiber has exactly two elements. This packages the
covering-map property with the fiber-cardinality fact
(`proj_fiber_encard_eq_two`) into the single statement "canonical double
cover". -/
theorem proj_isCoveringMap_two_sheeted (n : ℕ) :
    IsCoveringMap (proj n : Sphere n → RP n) ∧
      ∀ q : RP n, (proj n ⁻¹' {q}).encard = 2 :=
  ⟨proj_isCoveringMap n, proj_fiber_encard_eq_two⟩

end SphereOddDegree
