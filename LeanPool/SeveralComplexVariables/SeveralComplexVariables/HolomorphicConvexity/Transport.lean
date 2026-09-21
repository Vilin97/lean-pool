/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Biholomorphic
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.HolomorphicConvexity.Hull

/-!
# Products and biholomorphic transport of holomorphic convexity

Products preserve holomorphic convexity. Biholomorphic maps transport relative hulls exactly and
preserve holomorphic convexity of their open source and target. These results are proved
directly from the hull definition and compactness; they do not depend on Cartan–Thullen.

References: [Range][Range1986] II §3.3; [Scheidemann][Scheidemann2005] §7.1;
[Jakóbczak–Jarnicki][JakobczakJarnicki2021] §2.7.

## Main results

`IsHolomorphicallyConvex.prod` is stability under products. `IsBiholomorphic.image_holomorphicHull`
transports relative hulls. `IsBiholomorphic.isHolomorphicallyConvex_iff` is invariance of
holomorphic convexity.

## References

* [P. Jakóbczak and M. Jarnicki, *Lectures on Holomorphic Functions of Several Complex
  Variables*][JakobczakJarnicki2021]
* [R. M. Range, *Holomorphic Functions and Integral Representations in Several Complex
  Variables*][Range1986]
* [V. Scheidemann, *Introduction to Complex Analysis in Several Variables*][Scheidemann2005]
-/

public section

open Set

namespace SeveralComplexVariables

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Products of holomorphically convex ambient sets are holomorphically convex. -/
theorem IsHolomorphicallyConvex.prod {U : Set E} {V : Set F}
    (hU : IsHolomorphicallyConvex U) (hV : IsHolomorphicallyConvex V) :
    IsHolomorphicallyConvex (U ×ˢ V) := by
  intro K hK hKU
  have hfst : MapsTo (Prod.fst : E × F → E) (U ×ˢ V) U := fun _ hz => hz.1
  have hsnd : MapsTo (Prod.snd : E × F → F) (U ×ˢ V) V := fun _ hz => hz.2
  apply isCompact_holomorphicHull_of_subset_compact
    ((hU _ (hK.image continuous_fst) (by rintro _ ⟨z, hz, rfl⟩; exact (hKU hz).1)).prod
      (hV _ (hK.image continuous_snd) (by rintro _ ⟨z, hz, rfl⟩; exact (hKU hz).2)))
  · rintro z ⟨hzU, hzV⟩
    exact ⟨hzU.1, hzV.1⟩
  · intro z hz
    exact ⟨mapsTo_holomorphicHull analyticOnNhd_fst hfst hz,
      mapsTo_holomorphicHull analyticOnNhd_snd hsnd hz⟩

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

/-- Biholomorphic maps transport relative holomorphic hulls exactly. -/
theorem IsBiholomorphic.image_holomorphicHull {e : OpenPartialHomeomorph E F}
    (he : IsBiholomorphic e) {K : Set E} (hK : K ⊆ e.source) :
    e '' holomorphicHull e.source K = holomorphicHull e.target (e '' K) := by
  let := FiniteDimensional.complete ℂ E
  let := FiniteDimensional.complete ℂ F
  have hf := he.1.analyticOnNhd_of_finiteDimensional e.open_source
  have hg := he.2.analyticOnNhd_of_finiteDimensional e.open_target
  have hback : e.symm '' (e '' K) = K := by
    ext x
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      simpa only [e.left_inv (hK hz)] using hz
    · intro hx
      exact ⟨e x, ⟨x, hx, rfl⟩, e.left_inv (hK hx)⟩
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact mapsTo_holomorphicHull hf (fun _ hx => e.map_source hx) hz
  · intro z hz
    have h := mapsTo_holomorphicHull hg (fun _ hx => e.map_target hx) hz
    rw [hback] at h
    exact ⟨e.symm z, h, e.right_inv hz.1⟩

/-- Holomorphic convexity passes from the target of a biholomorphism to its source. -/
theorem IsBiholomorphic.isHolomorphicallyConvex_source {e : OpenPartialHomeomorph E F}
    (he : IsBiholomorphic e) (hV : IsHolomorphicallyConvex e.target) :
    IsHolomorphicallyConvex e.source := by
  intro K hK hKU
  let := FiniteDimensional.complete ℂ E
  let := FiniteDimensional.complete ℂ F
  have hf := he.1.analyticOnNhd_of_finiteDimensional e.open_source
  have hg := he.2.analyticOnNhd_of_finiteDimensional e.open_target
  have himage : e '' K ⊆ e.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact e.map_source (hKU hz)
  have hc := hV _ (hK.image_of_continuousOn (hf.continuousOn.mono hKU)) himage
  apply isCompact_holomorphicHull_of_subset_compact
    (hc.image_of_continuousOn (hg.continuousOn.mono (holomorphicHull_subset _ _)))
  · rintro _ ⟨z, hz, rfl⟩
    exact e.map_target hz.1
  · intro z hz
    exact ⟨e z, mapsTo_holomorphicHull hf (fun _ hx => e.map_source hx) hz, e.left_inv hz.1⟩

/-- Holomorphic convexity is invariant under biholomorphic equivalence of open sets. -/
theorem IsBiholomorphic.isHolomorphicallyConvex_iff {e : OpenPartialHomeomorph E F}
    (he : IsBiholomorphic e) :
    IsHolomorphicallyConvex e.source ↔ IsHolomorphicallyConvex e.target :=
  ⟨fun h => he.symm.isHolomorphicallyConvex_source h,
    fun h => he.isHolomorphicallyConvex_source h⟩

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
