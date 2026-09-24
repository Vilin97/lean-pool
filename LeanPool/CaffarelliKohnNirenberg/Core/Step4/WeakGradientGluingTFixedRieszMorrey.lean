/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTFixedForceMorrey
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientHGCloserCellsRieszMorrey

/-! # Morrey control of a windowed Riesz field

A completed-operator representative inherits the finite source Morrey
seminorm once the bounded spatial support and the full-time slice membership
are supplied by the fixed product restriction.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey CKN.Foundation.Euclidean

noncomputable section
namespace CKN.Core.Step4

/-- Product restriction supplies the bounded support and full-time slice
membership needed to transfer a source Morrey bound to its Riesz field. -/
theorem window_riesz_field_morrey_lt_top
    (j i : Fin 3) {κ : ℝ} (hκ : 0 < κ) (hκhi : κ ≤ 25 / 9)
    {F T : ParabolicPoint → ℝ} {x : Vec3} {r : ℝ} (hr : 0 < r)
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hF : AEMeasurable ((vec3Ball x r ×ˢ J).indicator F) volume)
    (hFs : ∀ᵐ s ∂volume.restrict J,
      MemLp (fun y => F (y, s)) (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hT : AEMeasurable T volume)
    (hident : ∀ᵐ s ∂volume, (fun y => T (y, s)) =ᵐ[volume]
      rieszSecondGradientExtensionOperator
        (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i)
        (fun y => (vec3Ball x r ×ˢ J).indicator F (y, s)))
    (hFnorm : morreyNorm (6 / 5 : ℝ) κ ((vec3Ball x r ×ˢ J).indicator F) < ⊤) :
    morreyNorm (6 / 5 : ℝ) κ T < ⊤ := by
  obtain ⟨L, hL⟩ := (CKN.Foundation.Parabolic.isCompact_closure_vec3Ball hr).isBounded.exists_norm_le
  apply pressure_riesz_morreyNorm_lt_top j i hκ hκhi hF
    (memLp_product_indicator_slices (isOpen_vec3Ball _ _).measurableSet hJ hFs)
    (L := L) ?_ hT hident hFnorm
  intro y s hy
  exact Set.indicator_of_notMem (fun h => (not_le.mpr hy) (hL y (subset_closure h.1))) F

end CKN.Core.Step4
