/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Probability.RegCoeffField.Endomorphisms

/-!
# The restriction σ-algebra on the carrier

The restriction σ-algebra `RestrictionSigmaR U hU` is the σ-algebra of carrier
events determined by the values of the field on the measurable set `U`: the
comap of the canonical carrier σ-algebra along the restriction endomorphism
`restrictReg U hU`.  It is the measurable local σ-algebra used in the explicit
pointwise-restriction law lane (see `Laws.lean`).

`RestrictionSigmaR` is coarser than the canonical carrier σ-algebra, and monotone
under set inclusion (with the `MeasurableSet` discipline that both restriction
maps be well defined, matching the D7-approved coarsening interface).  The
separation predicate `AreUnitSeparated` is the ambient sup-norm raw-set
predicate of `Homogenization.Probability.RandomField`, reused unchanged.

Reference: the paper (Armstrong–Kuusi–Loher, to appear).
-/

namespace Homogenization

open MeasureTheory

noncomputable section

variable {d : ℕ}
/-- The restriction σ-algebra on the carrier: the comap of the canonical carrier
σ-algebra along the restriction endomorphism `restrictReg U hU`. -/
def RestrictionSigmaR (U : Set (Vec d)) (hU : MeasurableSet U) :
    MeasurableSpace (RegCoeffField d) :=
  MeasurableSpace.comap (restrictReg U hU) inferInstance

/-- The restriction endomorphism is measurable from the restriction σ-algebra. -/
theorem measurable_restrictReg_restrictionSigmaR (U : Set (Vec d)) (hU : MeasurableSet U) :
    @Measurable _ _ (RestrictionSigmaR U hU) _ (restrictReg U hU) :=
  measurable_iff_comap_le.mpr le_rfl

/-- Point evaluation inside `U` remains observable for the restriction
σ-algebra: it factors through the restricted field. -/
theorem measurable_apply_entry_restrictionSigmaR_of_mem {U : Set (Vec d)}
    (hU : MeasurableSet U) {x : Vec d} (hx : x ∈ U) (i j : Fin d) :
    @Measurable (RegCoeffField d) ℝ (RestrictionSigmaR U hU) _
      (fun a : RegCoeffField d => a x i j) := by
  have hfactor : (fun a : RegCoeffField d => a x i j) =
      fun a => restrictReg U hU a x i j := by
    funext a
    rw [restrictReg_apply_entry, Set.indicator_of_mem hx]
  rw [hfactor]
  exact (measurable_apply_entry x i j).comp
    (measurable_restrictReg_restrictionSigmaR U hU)

/-- The restriction σ-algebra is coarser than the canonical carrier σ-algebra. -/
theorem restrictionSigmaR_le (U : Set (Vec d)) (hU : MeasurableSet U) :
    RestrictionSigmaR U hU ≤ instMeasurableSpaceRegCoeffField d :=
  measurable_iff_comap_le.mp (measurable_restrictReg U hU)

/-- Composition identity for nested restrictions: restricting to `V` and then to
`U ⊆ V` is the same as restricting to `U`. -/
theorem restrictReg_comp_restrictReg_of_subset {U V : Set (Vec d)}
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hUV : U ⊆ V) :
    restrictReg U hU ∘ restrictReg V hV = restrictReg U hU := by
  funext a
  apply RegCoeffField.ext
  intro x
  by_cases hx : x ∈ U
  · have hxV : x ∈ V := hUV hx
    simp only [Function.comp_apply, restrictReg_apply,
      Set.indicator_of_mem hx, Set.indicator_of_mem hxV]
  · simp only [Function.comp_apply, restrictReg_apply,
      Set.indicator_of_notMem hx]

/-- The `U`-restriction endomorphism is measurable from the coarser `V`-restriction
σ-algebra when `U ⊆ V`. -/
theorem measurable_restrictReg_restrictionSigmaR_of_subset {U V : Set (Vec d)}
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hUV : U ⊆ V) :
    @Measurable _ _ (RestrictionSigmaR V hV) _ (restrictReg U hU) := by
  simpa [restrictReg_comp_restrictReg_of_subset hU hV hUV, Function.comp] using
    (measurable_restrictReg U hU).comp (measurable_restrictReg_restrictionSigmaR V hV)

/-- **Monotonicity of the restriction σ-algebra under set inclusion.** -/
theorem RestrictionSigmaR_mono {U V : Set (Vec d)} (hU : MeasurableSet U)
    (hV : MeasurableSet V) (hUV : U ⊆ V) :
    RestrictionSigmaR U hU ≤ RestrictionSigmaR V hV := by
  simpa [RestrictionSigmaR] using
    measurable_iff_comap_le.mp
      (measurable_restrictReg_restrictionSigmaR_of_subset hU hV hUV)

end

end Homogenization
