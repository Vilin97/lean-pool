/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolutionIntegrable

/-!
# Trivial Solution

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open Set
open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-!
# The identically zero suitable weak solution

The class `IsSuitableWeakSolutionIntegrable` (from `def:sws` in `paper/ckn.tex`) is a
conjunction of analytic hypotheses on the velocity `u`, its gradient `Du`, the
pressure `p`, and the forcing `f`.  This file certifies that the *identically
zero* data satisfies every hypothesis, so the class is inhabited and
quantified statements over it are not vacuous.
-/

private lemma spatialGradientSq_zero (z : ParabolicPoint) :
    spatialGradientSq (fun _ : ParabolicPoint => (0 : Vec3))
      (fun (_ : ParabolicPoint) (_ : Fin 3) => (0 : Vec3)) z = 0 := by
  unfold spatialGradientSq
  simp

private lemma hasWeakGradientOn_zero (U : Set (Fin 3 → ℝ)) (i : Fin 3) :
    HasWeakGradientOn U (fun _ => (0 : Vec3) i) (fun _ => (0 : Fin 3 → Vec3) i) := by
  have h := HasWeakGradientOn.of_contDiff (U := U) (f := fun _ : Fin 3 → ℝ => (0 : ℝ))
    (contDiff_const (𝕜 := ℝ))
  simpa [HasWeakGradientOn] using h

/-- The identically zero velocity, pressure, and forcing satisfy
  `IsSuitableWeakSolutionIntegrable`. -/
theorem isSuitableWeakSolutionIntegrable_zero {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    (hΩ : IsOpen Ω) (hI : IsOpen I) (hIc : OrdConnected I) (hq : 5 / 2 < q) :
    IsSuitableWeakSolutionIntegrable Ω I q (fun _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ => 0)
      := by
  refine ⟨hΩ, hI, hIc, hq, ?_, ?_, ?_, ?_, ?_⟩
  · -- localVecLp condition
    intro Ω' J hBox
    unfold localVecLp
    intro i
    unfold localLp
    simp
  · -- AEStronglyMeasurable + essSup + lintegral + MemLp conditions
    intro Ω' J hBox
    have hmeas_u : AEStronglyMeasurable (fun _ : ParabolicPoint => (0 : Vec3))
        (volume.restrict (spaceTimeSet Ω' J)) :=
      aestronglyMeasurable_const
    have hmeas_Du : AEStronglyMeasurable (fun (_ : ParabolicPoint) (_ : Fin 3) => (0 : Vec3))
        (volume.restrict (spaceTimeSet Ω' J)) :=
      aestronglyMeasurable_const
    have hmeas_p : AEStronglyMeasurable (fun _ : ParabolicPoint => (0 : ℝ))
        (volume.restrict (spaceTimeSet Ω' J)) :=
      aestronglyMeasurable_const
    have hmeas_f : AEStronglyMeasurable (fun _ : ParabolicPoint => (0 : Vec3))
        (volume.restrict (spaceTimeSet Ω' J)) :=
      aestronglyMeasurable_const
    have hessSup : essSup (fun (s : ℝ) => ∫⁻ x in Ω', ‖(0 : Vec3)‖ₑ ^ (2 : ℝ))
        (volume.restrict J) < ⊤ := by
      have h_int : (fun (s : ℝ) => ∫⁻ x in Ω', ‖(0 : Vec3)‖ₑ ^ (2 : ℝ)) = fun _ => (0 : ℝ≥0∞) := by
        ext s; simp
      rw [h_int]
      refine lt_of_le_of_lt (essSup_le_of_ae_le 0 ?_) ?_
      · filter_upwards with x; simp
      · simp
    have h_lintegral : (∫⁻ z in spaceTimeSet Ω' J,
        ‖(0 : ParabolicPoint → Vec3) z‖ₑ ^ (2 : ℝ) +
        ‖(fun (_ : ParabolicPoint) (_ : Fin 3) => (0 : Vec3)) z‖ₑ ^ (2 : ℝ)) < ⊤ := by
      have hzero : (∫⁻ z in spaceTimeSet Ω' J, (0 : ℝ≥0∞)) < ⊤ := by simp
      refine lt_of_eq_of_lt ?_ hzero
      symm
      refine lintegral_congr_ae ?_
      filter_upwards with z
      rw [show (fun (_ : Fin 3) => (0 : Vec3)) = (0 : Fin 3 → Vec3) from rfl, enorm_zero]
      simp [ENNReal.zero_rpow_of_pos (by norm_num : 0 < (2 : ℝ))]
    have h_memLp_p : MemLp (fun _ : ParabolicPoint => (0 : ℝ))
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (spaceTimeSet Ω' J)) := by
      simp
    have h_memLp_f : MemLp (fun _ : ParabolicPoint => (0 : Vec3))
        (ENNReal.ofReal q) (volume.restrict (spaceTimeSet Ω' J)) := by
      simp
    have h_weak_grad : ∀ (i : Fin 3), ∀ᵐ s ∂volume.restrict J,
        HasWeakGradientOn Ω' (fun x => (0 : Vec3) i) (fun x => (0 : Fin 3 → Vec3) i) := by
      intro i
      have h := hasWeakGradientOn_zero Ω' i
      refine ae_of_all _ (fun s => h)
    exact ⟨hmeas_u, hmeas_Du, hmeas_p, hmeas_f, hessSup, h_lintegral, h_memLp_p, h_memLp_f,
      h_weak_grad⟩
  · -- Test function integral (scalar ψ)
    intro ψ hψ
    let f (z : ParabolicPoint) := ∑ i : Fin 3, ((0 : Vec3) i) * spatialPartial ψ i z
    have h_int_val : ∫ z in spaceTimeSet Ω I, f z = 0 := by
      simp [f]
    exact ⟨by simp, h_int_val⟩
  · -- Test function integral (vector φ)
    intro φ hφ
    let S (z : ParabolicPoint) :=
      ∑ i : Fin 3, ∑ j : Fin 3,
        ((0 : Vec3) i) * ((0 : Vec3) j) * spatialPartial (fun w => φ w i) j z
    have h_int_val : ∫ z in spaceTimeSet Ω I,
        (-(∑ i : Fin 3, ((0 : Vec3) i) * timePartial (fun w => φ w i) z))
          - S z
          + ∑ i : Fin 3, ∑ j : Fin 3, ((0 : Fin 3 → Vec3) i j) *
            spatialPartial (fun w => φ w i) j z
          - ((0 : ParabolicPoint → ℝ) z) * ∑ i : Fin 3, spatialPartial (fun w => φ w i) i z
          - ∑ i : Fin 3, ((0 : Vec3) i) * φ z i = 0 := by
      simp [S]
    exact ⟨by simp, h_int_val⟩
  · -- Energy inequality
    intro ψ hψ hψ_nonneg
    have h_sgs_zero : ∀ z, spatialGradientSq (fun (_ : ParabolicPoint) => (0 : Vec3))
        (fun (_ : ParabolicPoint) (_ : Fin 3) => (0 : Vec3)) z = 0 :=
      spatialGradientSq_zero
    have h_norm_zero : vec3EuclideanNorm (0 : Vec3) = 0 := by
      simp [vec3EuclideanNorm]
    have hint1 : IntegrableOn (fun (z : ParabolicPoint) =>
      spatialGradientSq (fun (_ : ParabolicPoint) => (0 : Vec3))
        (fun (_ : ParabolicPoint) (_ : Fin 3) => (0 : Vec3)) z * ψ z) (tsupport ψ) volume := by
      simp [h_sgs_zero]
    have hint2 : IntegrableOn (fun (z : ParabolicPoint) =>
      (vec3EuclideanNorm ((0 : Vec3) : Vec3)) ^ 2 *
          (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z)
        + (((vec3EuclideanNorm ((0 : Vec3) : Vec3)) ^ 2 + 2 * ((0 : ParabolicPoint → ℝ) z)) *
            ∑ i : Fin 3, ((0 : Vec3) i) * spatialPartial ψ i z)
        + 2 * (∑ i : Fin 3, ((0 : Vec3) i) * ((0 : Vec3) i)) * ψ z) (tsupport ψ) volume := by
      simp [h_norm_zero]
    have h_ineq : 2 * ∫ z in spaceTimeSet Ω I,
        spatialGradientSq (fun (_ : ParabolicPoint) => (0 : Vec3))
          (fun (_ : ParabolicPoint) (_ : Fin 3) => (0 : Vec3)) z * ψ z ≤
        ∫ z in spaceTimeSet Ω I,
          (vec3EuclideanNorm ((0 : Vec3) : Vec3)) ^ 2 *
              (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z)
            + (((vec3EuclideanNorm ((0 : Vec3) : Vec3)) ^ 2 + 2 * ((0 : ParabolicPoint → ℝ) z)) *
                ∑ i : Fin 3, ((0 : Vec3) i) * spatialPartial ψ i z)
            + 2 * (∑ i : Fin 3, ((0 : Vec3) i) * ((0 : Vec3) i)) * ψ z := by
      have hL : (∫ z in spaceTimeSet Ω I,
        spatialGradientSq (fun (_ : ParabolicPoint) => (0 : Vec3))
          (fun (_ : ParabolicPoint) (_ : Fin 3) => (0 : Vec3)) z * ψ z) = 0 := by
        simp [h_sgs_zero]
      have hR : (∫ z in spaceTimeSet Ω I,
        (vec3EuclideanNorm ((0 : Vec3) : Vec3)) ^ 2 *
            (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z)
          + (((vec3EuclideanNorm ((0 : Vec3) : Vec3)) ^ 2 + 2 * ((0 : ParabolicPoint → ℝ) z)) *
              ∑ i : Fin 3, ((0 : Vec3) i) * spatialPartial ψ i z)
          + 2 * (∑ i : Fin 3, ((0 : Vec3) i) * ((0 : Vec3) i)) * ψ z) = 0 := by
        simp [h_norm_zero]
      rw [hL, hR]
      norm_num
    exact ⟨hint1, hint2, h_ineq⟩

end CKN
