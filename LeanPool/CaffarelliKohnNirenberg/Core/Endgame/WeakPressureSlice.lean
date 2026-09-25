/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Potentials

/-! # Pressure slices with an actual weak gradient

The particular gradient is supplied as a measurable field with its weak
identity. Only the test functions are differentiated classically.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Endgame

private theorem integrableOn_mul_test
    {B : Set Vec3} (hB : IsOpen B) {f ψ : Vec3 → ℝ}
    (hf : LocallyIntegrableOn f B volume) (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hψB : tsupport ψ ⊆ B) :
    IntegrableOn (fun x => f x * ψ x) B volume := by
  have hm := hf.mul_continuousOn hψ.continuousOn hB.isLocallyClosed
  have hk := hm.integrableOn_compact_subset hψB hψc.isCompact
  have hg := hk.integrable_of_forall_notMem_eq_zero (by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero])
  exact hg.integrableOn

/-- Addition of locally integrable weak derivatives respects an a.e.
decomposition of the underlying pressure. -/
theorem weak_partial_deriv_of_ae_sum
    {B : Set Vec3} (hB : IsOpen B) {p P H gp gh : Vec3 → ℝ} {k : Fin 3}
    (hrep : p =ᵐ[volume.restrict B] P + H)
    (hP : HasWeakPartialDerivOn B k P gp)
    (hH : HasWeakPartialDerivOn B k H gh)
    (hPloc : LocallyIntegrableOn P B volume)
    (hHloc : LocallyIntegrableOn H B volume)
    (hgploc : LocallyIntegrableOn gp B volume)
    (hghloc : LocallyIntegrableOn gh B volume) :
    HasWeakPartialDerivOn B k p (gp + gh) := by
  intro ψ hψ hψc hψB
  have hd : Continuous (fun x => (fderiv ℝ ψ x) (basisVec k)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc : HasCompactSupport (fun x => (fderiv ℝ ψ x) (basisVec k)) :=
    hψc.mono' (subset_closure.trans
      (tsupport_fderiv_apply_subset ℝ (basisVec k)))
  have hdB : tsupport (fun x => (fderiv ℝ ψ x) (basisVec k)) ⊆ B :=
    (tsupport_fderiv_apply_subset ℝ (basisVec k)).trans hψB
  have hleft : (∫ x in B, p x * (fderiv ℝ ψ x) (basisVec k)) =
      ∫ x in B, (P x + H x) * (fderiv ℝ ψ x) (basisVec k) := by
    apply integral_congr_ae
    filter_upwards [hrep] with x hx
    rw [hx]
    rfl
  rw [hleft]
  simp_rw [Pi.add_apply, add_mul]
  rw [integral_add (integrableOn_mul_test hB hPloc hd hdc hdB)
      (integrableOn_mul_test hB hHloc hd hdc hdB),
    integral_add (integrableOn_mul_test hB hgploc hψ.continuous hψc hψB)
      (integrableOn_mul_test hB hghloc hψ.continuous hψc hψB),
    hP ψ hψ hψc hψB, hH ψ hψ hψc hψB]
  ring

/-- A whole-space weak pairing restricts to any open slice domain. -/
theorem weak_partial_deriv_on_of_global_pairing
    {B : Set Vec3} (hB : IsOpen B) {P D : Vec3 → ℝ} {k : Fin 3}
    (hweak : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∫ x, P x * spatialDeriv ψ k x) = -(∫ x, D x * ψ x)) :
    HasWeakPartialDerivOn B k P D := by
  have hglobal : HasWeakPartialDerivOn Set.univ k P D := by
    intro ψ hψ hψc _
    simpa only [Measure.restrict_univ, spatialDeriv] using hweak ψ hψ hψc
  exact hglobal.restrict hB (subset_univ B)

/-- The local pressure-gradient estimate consumes the selected weak field
directly, without identifying it with a classical derivative of a potential. -/
theorem pressure_slice_bound_of_weak_extension
    {B B' : Set Vec3} (hB : IsOpen B)
    {p P H D gh G : Vec3 → ℝ} {k : Fin 3} {ρ C : ℝ}
    (hrep : p =ᵐ[volume.restrict B] P + H)
    (hweak : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∫ x, P x * spatialDeriv ψ k x) = -(∫ x, D x * ψ x))
    (hH : HasWeakPartialDerivOn B k H gh)
    (hPloc : LocallyIntegrableOn P B volume)
    (hHloc : LocallyIntegrableOn H B volume)
    (hDloc : LocallyIntegrableOn D B volume)
    (hghloc : LocallyIntegrableOn gh B volume)
    (hD : eLpNorm D (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
      ENNReal.ofReal C * eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hgh : eLpNorm gh (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B') ≤
      ENNReal.ofReal C * ENNReal.ofReal (ρ ^ (-1 / 2 : ℝ)) *
        eLpNorm p (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict B)) :
    LocallyIntegrableOn (D + gh) B volume ∧
      HasWeakPartialDerivOn B k p (D + gh) ∧
      eLpNorm (D + gh) (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B') ≤
        ENNReal.ofReal C * (eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume +
          ENNReal.ofReal (ρ ^ (-1 / 2 : ℝ)) *
            eLpNorm p (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict B)) := by
  refine ⟨hDloc.add hghloc, weak_partial_deriv_of_ae_sum hB hrep
    (weak_partial_deriv_on_of_global_pairing hB hweak) hH hPloc hHloc hDloc hghloc, ?_⟩
  have hlocal := (eLpNorm_mono_measure D
    (Measure.restrict_le_self (s := B'))).trans hD
  have hsum := eLpNorm_add_le (f := D) (g := gh)
    (μ := volume.restrict B') (p := ENNReal.ofReal (6 / 5 : ℝ)) (by norm_num)
  simpa only [mul_add, mul_assoc] using hsum.trans (add_le_add hlocal hgh)

/-- A vector-valued weak extension supplies each scalar slice estimate;
local integrability of its coordinates follows from actual Lp membership. -/
theorem pressure_slice_bound_of_vector_weak_extension
    {B B' : Set Vec3} (hB : IsOpen B)
    {p P H gh G : Vec3 → ℝ} {D : Vec3 → Vec3} {k : Fin 3} {ρ C : ℝ}
    (hrep : p =ᵐ[volume.restrict B] P + H)
    (hweak : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∫ x, P x * spatialDeriv ψ k x) = -(∫ x, D x k * ψ x))
    (hH : HasWeakPartialDerivOn B k H gh)
    (hPloc : LocallyIntegrableOn P B volume)
    (hHloc : LocallyIntegrableOn H B volume)
    (hDmem : MemLp D (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hghloc : LocallyIntegrableOn gh B volume)
    (hD : eLpNorm D (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
      ENNReal.ofReal C * eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hgh : eLpNorm gh (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B') ≤
      ENNReal.ofReal C * ENNReal.ofReal (ρ ^ (-1 / 2 : ℝ)) *
        eLpNorm p (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict B)) :
    LocallyIntegrableOn (fun x => D x k + gh x) B volume ∧
      HasWeakPartialDerivOn B k p (fun x => D x k + gh x) ∧
      eLpNorm (fun x => D x k + gh x) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict B') ≤ ENNReal.ofReal C *
          (eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume +
            ENNReal.ofReal (ρ ^ (-1 / 2 : ℝ)) *
              eLpNorm p (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict B)) := by
  have hmeas : AEStronglyMeasurable (fun x => D x k) volume :=
    (ContinuousLinearMap.proj (R := ℝ) k).continuous.comp_aestronglyMeasurable
      hDmem.aestronglyMeasurable
  have hcomp : eLpNorm (fun x => D x k) (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
      eLpNorm D (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
    eLpNorm_mono_ae hmeas (Eventually.of_forall fun x => norm_le_pi_norm (D x) k)
  have hmem : MemLp (fun x => D x k) (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
    hcomp.trans_lt hDmem.eLpNorm_lt_top
  exact pressure_slice_bound_of_weak_extension hB hrep hweak hH hPloc hHloc
    ((hmem.locallyIntegrable (by norm_num)).locallyIntegrableOn B)
    hghloc (hcomp.trans hD) hgh

end CKN.Core.Endgame
