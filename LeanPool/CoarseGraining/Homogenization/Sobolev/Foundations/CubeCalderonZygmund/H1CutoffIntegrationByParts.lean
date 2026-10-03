/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.QuantCutoffLowerH1
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.VectorFieldAndApex.WeakEquationHelpers

/-! # H1Cutoff Integration By Parts -/

@[expose] public section

namespace Homogenization

open scoped ENNReal BigOperators

noncomputable section

namespace CubeCalderonZygmund

private theorem memVectorL2_singleCoordinateH1Cutoff
    {d : ℕ} {U : Set (Vec d)} {r : Vec d → ℝ} (hr : MemScalarL2 U r)
    (j : Fin d) :
    MemVectorL2 U (fun x k => if k = j then r x else 0) := by
  classical
  apply MeasureTheory.MemLp.of_eval
  intro k
  by_cases hkj : k = j
  · subst k
    simpa using hr
  · rw [show (fun x : Vec d => if k = j then r x else 0) = fun _ => 0 by
      funext x
      simp [hkj]]
    exact MeasureTheory.MemLp.zero'

private theorem cutoff_integration_by_parts_coord
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (r v : H1Function U) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_compact : HasCompactSupport η)
    (hη_sub : tsupport η ⊆ U) (j : Fin d) :
    ∫ x in U, v x * r.grad x j * euclideanCoordDeriv j η x ∂MeasureTheory.volume =
      -∫ x in U, r x * v.grad x j * euclideanCoordDeriv j η x
        ∂MeasureTheory.volume -
        ∫ x in U, r x * v x * euclideanCoordSecondDeriv j j η x
          ∂MeasureTheory.volume := by
  let Dη : Vec d → ℝ := euclideanCoordDeriv j η
  let ψ : H10Function U :=
    v.mulContDiffHasCompactSupportToH10 hU
      (contDiff_euclideanCoordDeriv hη j)
      (hasCompactSupport_euclideanCoordDeriv hη_compact j)
      ((tsupport_euclideanCoordDeriv_subset_tsupport j η).trans hη_sub)
  have htest :
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ U →
        ∫ x in U,
            vecDot ((fun y k => if k = j then r y else 0) x)
              (euclideanGradient φ x) ∂MeasureTheory.volume =
          ∫ x in U, -r.grad x j * φ x ∂MeasureTheory.volume := by
    intro φ hφ hφ_compact hφ_sub
    have hrweak := r.hasWeakPartialDerivOn j φ hφ hφ_compact hφ_sub
    rw [← MeasureTheory.integral_neg] at hrweak
    simpa [vecDot, euclideanGradient, euclideanCoordDeriv] using hrweak
  have hweak := h10WeakEquationOn_of_contDiff_tests hU.isOpen
    (memVectorL2_singleCoordinateH1Cutoff r.memL2 j) (r.gradMemL2 j).neg htest ψ
  have hψfun : ψ.toH1Function.toFun = fun x => Dη x * v x := by
    simp [ψ, Dη]
  have hψgrad := WeakPoissonEquationOn.mulContDiffHasCompactSupportToH10_grad_ae v hU
    (contDiff_euclideanCoordDeriv hη j)
    (hasCompactSupport_euclideanCoordDeriv hη_compact j)
    ((tsupport_euclideanCoordDeriv_subset_tsupport j η).trans hη_sub)
  have hweak_expanded :
      ∫ x in U, r x *
          (Dη x * v.grad x j + v x * euclideanCoordSecondDeriv j j η x)
          ∂MeasureTheory.volume =
        ∫ x in U, -r.grad x j * (Dη x * v x)
          ∂MeasureTheory.volume := by
    rw [show
      (fun x => vecDot ((fun y k => if k = j then r y else 0) x)
        (ψ.toH1Function.grad x)) =
        fun x => r x * ψ.toH1Function.grad x j by
      funext x
      simp [vecDot]] at hweak
    rw [hψfun] at hweak
    have hleft :
        (fun x => r x * ψ.toH1Function.grad x j) =ᵐ[
          MeasureTheory.volume.restrict U]
        fun x => r x *
          (Dη x * v.grad x j + v x * euclideanCoordSecondDeriv j j η x) := by
      filter_upwards [hψgrad] with x hx
      simp only [Dη, euclideanCoordDeriv] at hx ⊢
      rw [hx]
      rfl
    rw [MeasureTheory.integral_congr_ae hleft] at hweak
    simpa [Dη, mul_comm, mul_left_comm, mul_assoc] using hweak
  have hDη_memL2 : MemScalarL2 U (fun x => Dη x * v x) := by
    exact
      WeakPoissonEquationOn.memScalarL2_mul_of_contDiff_hasCompactSupport_tsupport_subset
        (U := U) (V := U) hU.isOpen.measurableSet
        (contDiff_euclideanCoordDeriv hη j)
        (hasCompactSupport_euclideanCoordDeriv hη_compact j)
        ((tsupport_euclideanCoordDeriv_subset_tsupport j η).trans hη_sub)
        v.memL2
  have hDηgrad_memL2 : MemScalarL2 U (fun x => Dη x * v.grad x j) := by
    exact
      WeakPoissonEquationOn.memScalarL2_mul_of_contDiff_hasCompactSupport_tsupport_subset
        (U := U) (V := U) hU.isOpen.measurableSet
        (contDiff_euclideanCoordDeriv hη j)
        (hasCompactSupport_euclideanCoordDeriv hη_compact j)
        ((tsupport_euclideanCoordDeriv_subset_tsupport j η).trans hη_sub)
        (v.gradMemL2 j)
  have hsecond_memL2 :
      MemScalarL2 U (fun x => v x * euclideanCoordSecondDeriv j j η x) := by
    have hbase : MemScalarL2 U
        (fun x => euclideanCoordSecondDeriv j j η x * v x) :=
      WeakPoissonEquationOn.memScalarL2_mul_of_contDiff_hasCompactSupport_tsupport_subset
        (U := U) (V := U) hU.isOpen.measurableSet
        (contDiff_euclideanCoordSecondDeriv hη j j)
        (hasCompactSupport_euclideanCoordSecondDeriv hη_compact j j)
        ((tsupport_euclideanCoordSecondDeriv_subset_tsupport j j η).trans hη_sub)
        v.memL2
    simpa [mul_comm] using hbase
  have hfirst_int : MeasureTheory.IntegrableOn
      (fun x => r x * (Dη x * v.grad x j)) U :=
    r.memL2.integrable_mul hDηgrad_memL2
  have hsecond_int : MeasureTheory.IntegrableOn
      (fun x => r x * (v x * euclideanCoordSecondDeriv j j η x)) U :=
    r.memL2.integrable_mul hsecond_memL2
  have hsplit :
      ∫ x in U, r x *
          (Dη x * v.grad x j + v x * euclideanCoordSecondDeriv j j η x)
          ∂MeasureTheory.volume =
        ∫ x in U, r x * (Dη x * v.grad x j) ∂MeasureTheory.volume +
          ∫ x in U, r x * (v x * euclideanCoordSecondDeriv j j η x)
            ∂MeasureTheory.volume := by
    rw [show (fun x => r x *
        (Dη x * v.grad x j + v x * euclideanCoordSecondDeriv j j η x)) =
        fun x => r x * (Dη x * v.grad x j) +
          r x * (v x * euclideanCoordSecondDeriv j j η x) by
      funext x
      ring]
    exact MeasureTheory.integral_add hfirst_int hsecond_int
  have hright :
      ∫ x in U, -r.grad x j * (Dη x * v x) ∂MeasureTheory.volume =
        -∫ x in U, v x * r.grad x j * Dη x ∂MeasureTheory.volume := by
    rw [← MeasureTheory.integral_neg]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    ring
  have hfirst :
      ∫ x in U, r x * (Dη x * v.grad x j) ∂MeasureTheory.volume =
        ∫ x in U, r x * v.grad x j * Dη x ∂MeasureTheory.volume := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    ring
  have hsecond :
      ∫ x in U, r x * (v x * euclideanCoordSecondDeriv j j η x)
          ∂MeasureTheory.volume =
        ∫ x in U, r x * v x * euclideanCoordSecondDeriv j j η x
          ∂MeasureTheory.volume := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    ring
  dsimp only [Dη] at hweak_expanded hsplit hright hfirst hsecond
  linarith

/-- Integration by parts for two `H¹` functions after multiplying by a smooth
compactly supported cutoff.  Neither function is assumed to have zero trace. -/
theorem h1_cutoff_integration_by_parts
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (r v : H1Function U) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_compact : HasCompactSupport η)
    (hη_sub : tsupport η ⊆ U) :
    ∫ x in U, v x * vecDot (r.grad x) (euclideanGradient η x)
        ∂MeasureTheory.volume =
      -∫ x in U, r x * vecDot (v.grad x) (euclideanGradient η x)
        ∂MeasureTheory.volume -
        ∫ x in U, r x * v x * euclideanCoordLaplacian η x
          ∂MeasureTheory.volume := by
  have hleft_int : ∀ j : Fin d, MeasureTheory.IntegrableOn
      (fun x => v x * r.grad x j * euclideanCoordDeriv j η x) U := by
    intro j
    have hcut : MemScalarL2 U (fun x => euclideanCoordDeriv j η x * v x) :=
      WeakPoissonEquationOn.memScalarL2_mul_of_contDiff_hasCompactSupport_tsupport_subset
        (U := U) (V := U) hU.isOpen.measurableSet
        (contDiff_euclideanCoordDeriv hη j)
        (hasCompactSupport_euclideanCoordDeriv hη_compact j)
        ((tsupport_euclideanCoordDeriv_subset_tsupport j η).trans hη_sub)
        v.memL2
    change MeasureTheory.Integrable
      (fun x => v x * r.grad x j * euclideanCoordDeriv j η x)
      (MeasureTheory.volume.restrict U)
    convert (r.gradMemL2 j).integrable_mul hcut using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  have hmiddle_int : ∀ j : Fin d, MeasureTheory.IntegrableOn
      (fun x => r x * v.grad x j * euclideanCoordDeriv j η x) U := by
    intro j
    have hcut : MemScalarL2 U
        (fun x => euclideanCoordDeriv j η x * v.grad x j) :=
      WeakPoissonEquationOn.memScalarL2_mul_of_contDiff_hasCompactSupport_tsupport_subset
        (U := U) (V := U) hU.isOpen.measurableSet
        (contDiff_euclideanCoordDeriv hη j)
        (hasCompactSupport_euclideanCoordDeriv hη_compact j)
        ((tsupport_euclideanCoordDeriv_subset_tsupport j η).trans hη_sub)
        (v.gradMemL2 j)
    change MeasureTheory.Integrable
      (fun x => r x * v.grad x j * euclideanCoordDeriv j η x)
      (MeasureTheory.volume.restrict U)
    convert r.memL2.integrable_mul hcut using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  have hlast_int : ∀ j : Fin d, MeasureTheory.IntegrableOn
      (fun x => r x * v x * euclideanCoordSecondDeriv j j η x) U := by
    intro j
    have hcut : MemScalarL2 U
        (fun x => v x * euclideanCoordSecondDeriv j j η x) := by
      have hbase : MemScalarL2 U
          (fun x => euclideanCoordSecondDeriv j j η x * v x) :=
        WeakPoissonEquationOn.memScalarL2_mul_of_contDiff_hasCompactSupport_tsupport_subset
          (U := U) (V := U) hU.isOpen.measurableSet
          (contDiff_euclideanCoordSecondDeriv hη j j)
          (hasCompactSupport_euclideanCoordSecondDeriv hη_compact j j)
          ((tsupport_euclideanCoordSecondDeriv_subset_tsupport j j η).trans hη_sub)
          v.memL2
      simpa [mul_comm] using hbase
    change MeasureTheory.Integrable
      (fun x => r x * v x * euclideanCoordSecondDeriv j j η x)
      (MeasureTheory.volume.restrict U)
    convert r.memL2.integrable_mul hcut using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  have hleft_sum :
      ∫ x in U, v x * vecDot (r.grad x) (euclideanGradient η x)
          ∂MeasureTheory.volume =
        ∑ j : Fin d, ∫ x in U,
          v x * r.grad x j * euclideanCoordDeriv j η x ∂MeasureTheory.volume := by
    rw [show (fun x => v x * vecDot (r.grad x) (euclideanGradient η x)) =
        fun x => ∑ j : Fin d, v x * r.grad x j * euclideanCoordDeriv j η x by
      funext x
      simp only [vecDot, euclideanGradient, euclideanCoordDeriv]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring]
    rw [MeasureTheory.integral_finsetSum]
    intro j _
    exact hleft_int j
  have hmiddle_sum :
      ∫ x in U, r x * vecDot (v.grad x) (euclideanGradient η x)
          ∂MeasureTheory.volume =
        ∑ j : Fin d, ∫ x in U,
          r x * v.grad x j * euclideanCoordDeriv j η x ∂MeasureTheory.volume := by
    rw [show (fun x => r x * vecDot (v.grad x) (euclideanGradient η x)) =
        fun x => ∑ j : Fin d, r x * v.grad x j * euclideanCoordDeriv j η x by
      funext x
      simp only [vecDot, euclideanGradient, euclideanCoordDeriv]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring]
    rw [MeasureTheory.integral_finsetSum]
    intro j _
    exact hmiddle_int j
  have hlast_sum :
      ∫ x in U, r x * v x * euclideanCoordLaplacian η x
          ∂MeasureTheory.volume =
        ∑ j : Fin d, ∫ x in U,
          r x * v x * euclideanCoordSecondDeriv j j η x
            ∂MeasureTheory.volume := by
    rw [show (fun x => r x * v x * euclideanCoordLaplacian η x) =
        fun x => ∑ j : Fin d, r x * v x * euclideanCoordSecondDeriv j j η x by
      funext x
      simp only [euclideanCoordLaplacian]
      rw [Finset.mul_sum]]
    rw [MeasureTheory.integral_finsetSum]
    intro j _
    exact hlast_int j
  rw [hleft_sum, hmiddle_sum, hlast_sum]
  calc
    ∑ j : Fin d, ∫ x in U,
        v x * r.grad x j * euclideanCoordDeriv j η x ∂MeasureTheory.volume =
      ∑ j : Fin d,
        (-∫ x in U, r x * v.grad x j * euclideanCoordDeriv j η x
          ∂MeasureTheory.volume -
          ∫ x in U, r x * v x * euclideanCoordSecondDeriv j j η x
            ∂MeasureTheory.volume) := by
        apply Finset.sum_congr rfl
        intro j _
        exact cutoff_integration_by_parts_coord hU r v hη hη_compact hη_sub j
    _ = -(∑ j : Fin d, ∫ x in U,
          r x * v.grad x j * euclideanCoordDeriv j η x ∂MeasureTheory.volume) -
        ∑ j : Fin d, ∫ x in U,
          r x * v x * euclideanCoordSecondDeriv j j η x
            ∂MeasureTheory.volume := by
        rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]

end CubeCalderonZygmund

end

end Homogenization
