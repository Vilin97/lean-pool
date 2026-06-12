/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
import LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite1Dimd.Definitions
import Mathlib.MeasureTheory.Integral.Pi
import LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermitek.ImportedAnalyticInputs
import LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermitek.TrueLevelBasis
import LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermitek.BasisLocalization

/-! # ImportedAnalyticInputs -/



open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Hermite1DimdLEAN

/-- `oneDimLift`: one Dim Lift. -/
def oneDimLift (f : ℂ → ℂ) : CSpace 1 → ℂ := fun z => f (z 0)

private theorem sum_Icc_eq_sum_Fin {α : Type*} [AddCommMonoid α]
    (N L : ℕ) (hL : 1 ≤ L) (f : ℕ → α) :
    ∑ n ∈ Finset.Icc N (N + L - 1), f n =
      ∑ m : Fin L, f (N + m.1) := by
  symm
  apply Finset.sum_nbij (fun (m : Fin L) => N + m.val)
  · intro m _
    exact Finset.mem_Icc.mpr ⟨Nat.le_add_right N m.val, by omega⟩
  · intro a _ b _ hab
    exact Fin.ext (Nat.add_left_cancel hab)
  · intro n hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
    refine ⟨⟨n - N, by omega⟩, Finset.mem_univ _, ?_⟩
    change N + (n - N) = n
    omega
  · intro _ _
    rfl

private def bandCoeff (N L : ℕ) (c : Fin L → ℂ) : ℕ → ℂ :=
  fun n => if h : N ≤ n ∧ n < N + L then c ⟨n - N, by omega⟩ else 0

private theorem positiveBandEq (N L : ℕ) (hL : 1 ≤ L) (c : Fin L → ℂ) :
    HermiteLEAN.positiveTrigonometricPolynomial
        (HermiteLEAN.frequencyBand N L) (bandCoeff N L c) =
      bandLimitedPolynomial N L c := by
  ext t
  rw [HermiteLEAN.positiveTrigonometricPolynomial, HermiteLEAN.frequencyBand,
    sum_Icc_eq_sum_Fin N L hL]
  simp [bandLimitedPolynomial, bandCoeff]

private lemma circleL2NormSq_const_mul (a : ℂ) (P : Circle → ℂ) :
    circleL2NormSq (fun t => a * P t) = ‖a‖ ^ 2 * circleL2NormSq P := by
  unfold circleL2NormSq
  calc
    ∫ t, ‖a * P t‖ ^ 2 ∂AddCircle.haarAddCircle
        = ∫ t, (‖a‖ ^ 2) * ‖P t‖ ^ 2 ∂AddCircle.haarAddCircle := by
            apply integral_congr_ae
            filter_upwards with t
            simp
            ring
    _ = ‖a‖ ^ 2 * ∫ t, ‖P t‖ ^ 2 ∂AddCircle.haarAddCircle := by
          rw [MeasureTheory.integral_const_mul]

private lemma rho_mul_right (a u : ℂ) :
    rho a (a * u) = ‖a‖ * rho 1 u := by
  by_cases ha : a = 0
  · subst ha
    simp [rho]
  · have hnn : 0 ≤ ‖a‖ := norm_nonneg _
    rw [rho, rho]
    have h1 : a + a * u = a * (1 + u) := by
      ring
    rw [h1, norm_mul]
    calc
      |‖a‖ * ‖1 + u‖ - ‖a‖| = |‖a‖ * (‖1 + u‖ - 1)| := by
          ring_nf
      _ = ‖a‖ * |‖1 + u‖ - 1| := by
          rw [abs_mul, abs_of_nonneg hnn]
      _ = ‖a‖ * rho 1 u := by
          simp [rho]

private lemma measurableSet_oneDimAnnulus
    (j : ℕ) :
    MeasurableSet (productAnnulus (d := 1) (fun _ => j)) := by
  have hge :
      MeasurableSet {z : CSpace 1 | (j : ℝ) ≤ ‖z 0‖} := by
    exact measurableSet_le measurable_const
      (measurable_norm.comp (continuous_apply 0).measurable)
  have hlt :
      MeasurableSet {z : CSpace 1 | ‖z 0‖ < (j : ℝ) + 1} := by
    exact measurableSet_lt
      (measurable_norm.comp (continuous_apply 0).measurable) measurable_const
  simpa [productAnnulus, Set.setOf_forall, Set.setOf_and] using hge.inter hlt

private lemma measurableSet_complex_annulus
    (j : ℕ) :
    MeasurableSet (HermiteLEAN.annulus j) := by
  have hge : MeasurableSet {z : ℂ | (j : ℝ) ≤ ‖z‖} := by
    exact measurableSet_le measurable_const measurable_norm
  have hlt : MeasurableSet {z : ℂ | ‖z‖ < (j : ℝ) + 1} := by
    exact measurableSet_lt measurable_norm measurable_const
  simpa [HermiteLEAN.annulus, Set.setOf_and] using hge.inter hlt

private lemma integrable_oneDimPhi_cross_gaussian
    (k m n : ℕ) :
    Integrable
      (fun z : CSpace 1 => oneDimPhi k m (z 0) * conj (oneDimPhi k n (z 0)))
      (gaussianMeasure 1) := by
  change
    Integrable
      (fun z : CSpace 1 => HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)))
      (gaussianMeasure 1)
  rw [gaussianMeasure]
  rw [MeasureTheory.integrable_withDensity_iff_integrable_smul']
  · have hcross :
        Integrable
          (fun z : CSpace 1 =>
            HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)) *
              (Real.exp (-‖z 0‖ ^ 2) : ℂ)) := by
      have h :=
        (MeasureTheory.volume_preserving_funUnique (Fin 1) ℂ).integrable_comp_of_integrable
          (g := fun z : ℂ =>
            HermitekLEAN.Phi k m z * conj (HermitekLEAN.Phi k n z) *
              (Real.exp (-‖z‖ ^ 2) : ℂ))
          (HermitekLEAN.integrable_weightedCross k m n)
      refine h.congr ?_
      filter_upwards with z
      rfl
    have hsmul :
        Integrable
          (fun z : CSpace 1 =>
            Real.exp (-‖z 0‖ ^ 2) •
              (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)))) := by
      convert hcross using 1
      funext z
      simp [Algebra.smul_def, mul_left_comm, mul_comm]
    convert hsmul.const_mul (1 / Real.pi) using 1
    funext z
    have hnonneg : 0 ≤ π⁻¹ * rexp (-‖z 0‖ ^ 2) := by positivity
    simp only [gaussianDensity, pow_one, one_div, univ_unique, Fin.default_eq_zero, Fin.isValue,
      sum_singleton, hnonneg, ENNReal.toReal_ofReal, real_smul, ofReal_exp, ofReal_neg, ofReal_pow]
    have hleft :
        (π⁻¹ * rexp (-‖z 0‖ ^ 2)) •
            (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) =
          (((π⁻¹ * rexp (-‖z 0‖ ^ 2) : ℝ) : ℂ) *
            (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)))) := by
      simp [Algebra.smul_def]
    calc
      (π⁻¹ * rexp (-‖z 0‖ ^ 2)) •
          (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) =
        (((π⁻¹ * rexp (-‖z 0‖ ^ 2) : ℝ) : ℂ) *
          (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)))) := hleft
      _ = (↑π)⁻¹ * (cexp (-↑‖z 0‖ ^ 2) *
            (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)))) := by
          simp [mul_assoc, mul_left_comm]
  · change
      Measurable
        (fun z : CSpace 1 =>
          ENNReal.ofReal ((1 / Real.pi ^ 1) * Real.exp (-(∑ q : Fin 1, ‖z q‖ ^ 2))))
    fun_prop
  · simp

private theorem gaussianInner_oneDimPhi_eq_weightedInner
    (k m n : ℕ) :
    gaussianInner (d := 1) (oneDimLift (oneDimPhi k m)) (oneDimLift (oneDimPhi k n)) =
      HermitekLEAN.weightedInner (HermitekLEAN.Phi k m) (HermitekLEAN.Phi k n) := by
  change
    gaussianInner (d := 1) (fun z => HermitekLEAN.Phi k m (z 0))
      (fun z => HermitekLEAN.Phi k n (z 0)) =
      HermitekLEAN.weightedInner (HermitekLEAN.Phi k m) (HermitekLEAN.Phi k n)
  unfold gaussianInner HermitekLEAN.weightedInner HermiteLEAN.weightedInner
  rw [gaussianMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun z : CSpace 1 => ENNReal.ofReal (gaussianDensity 1 z)) by
      unfold gaussianDensity
      fun_prop)
    (show ∀ᵐ x : CSpace 1, ENNReal.ofReal (gaussianDensity 1 x) < ⊤ by
      filter_upwards with x
      simp)]
  have hEq :
      ∫ (x : CSpace 1),
          HermitekLEAN.Phi k m ((MeasurableEquiv.funUnique (Fin 1) ℂ) x) *
            ((Real.exp (-‖(MeasurableEquiv.funUnique (Fin 1) ℂ) x‖ ^ 2) : ℂ) *
              conj (HermitekLEAN.Phi k n ((MeasurableEquiv.funUnique (Fin 1) ℂ) x)))
            ∂(volume : Measure (CSpace 1)) =
        ∫ z : ℂ,
          HermitekLEAN.Phi k m z *
            ((Real.exp (-‖z‖ ^ 2) : ℂ) * conj (HermitekLEAN.Phi k n z))
            ∂(volume : Measure ℂ) := by
    let e : CSpace 1 ≃ᵐ ℂ := MeasurableEquiv.funUnique (Fin 1) ℂ
    have hEq0 :=
      ((MeasureTheory.volume_preserving_funUnique (Fin 1) ℂ).integral_comp'
        (f := e)
        (fun z : ℂ =>
          HermitekLEAN.Phi k m z *
            ((Real.exp (-‖z‖ ^ 2) : ℂ) * conj (HermitekLEAN.Phi k n z))))
    convert hEq0 using 1
  have hcomp :
        ∫ z : CSpace 1,
            HermitekLEAN.Phi k m (z 0) *
              ((Real.exp (-‖z 0‖ ^ 2) : ℂ) * conj (HermitekLEAN.Phi k n (z 0)))
              ∂(volume : Measure (CSpace 1)) =
          ∫ z : ℂ,
            HermitekLEAN.Phi k m z *
              ((Real.exp (-‖z‖ ^ 2) : ℂ) * conj (HermitekLEAN.Phi k n z))
              ∂(volume : Measure ℂ) := by
    convert hEq using 1
  calc
    ∫ z : CSpace 1,
        (ENNReal.ofReal (gaussianDensity 1 z)).toReal •
          (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)))
          ∂(volume : Measure (CSpace 1))
        =
      ∫ z : CSpace 1,
        ((1 / Real.pi : ℂ) *
          ((HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) *
            (Real.exp (-‖z 0‖ ^ 2) : ℂ))) ∂(volume : Measure (CSpace 1)) := by
          apply integral_congr_ae
          filter_upwards with z
          have hdens :
              (ENNReal.ofReal (gaussianDensity 1 z)).toReal =
                (1 / Real.pi) * Real.exp (-‖z 0‖ ^ 2) := by
            have hnonneg : 0 ≤ Real.pi⁻¹ * Real.exp (-‖z 0‖ ^ 2) := by
              positivity
            simp [gaussianDensity, hnonneg]
          rw [Algebra.smul_def, hdens]
          have hcast :
              (algebraMap ℝ ℂ) ((1 / Real.pi) * Real.exp (-‖z 0‖ ^ 2)) =
                ((1 / Real.pi : ℂ) * (Real.exp (-‖z 0‖ ^ 2) : ℂ)) := by
            simp
          calc
            (algebraMap ℝ ℂ) ((1 / Real.pi) * Real.exp (-‖z 0‖ ^ 2)) *
                (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)))
                =
              ((1 / Real.pi : ℂ) * (Real.exp (-‖z 0‖ ^ 2) : ℂ)) *
                (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) := by
                  rw [hcast]
            _ =
              (1 / Real.pi : ℂ) *
                ((HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) *
                  (Real.exp (-‖z 0‖ ^ 2) : ℂ)) := by
                    ring
    _ =
      (1 / Real.pi : ℂ) *
        ∫ z : CSpace 1,
          (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) *
            (Real.exp (-‖z 0‖ ^ 2) : ℂ) ∂(volume : Measure (CSpace 1)) := by
            have hconst :
                ∫ z : CSpace 1,
                  (1 / Real.pi : ℂ) *
                    ((HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) *
                      (Real.exp (-‖z 0‖ ^ 2) : ℂ)) =
                (1 / Real.pi : ℂ) *
                  ∫ z : CSpace 1,
                    (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) *
                      (Real.exp (-‖z 0‖ ^ 2) : ℂ) := by
                exact
                  (MeasureTheory.integral_const_mul
                    (μ := (volume : Measure (CSpace 1)))
                    (1 / Real.pi : ℂ)
                    (fun z : CSpace 1 =>
                      (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) *
                        (Real.exp (-‖z 0‖ ^ 2) : ℂ)))
            simpa using hconst
    _ = (1 / Real.pi : ℂ) *
        ∫ z : ℂ,
          (HermitekLEAN.Phi k m z * conj (HermitekLEAN.Phi k n z)) *
            (Real.exp (-‖z‖ ^ 2) : ℂ) ∂(volume : Measure ℂ) := by
          have hcomp' : ∫ z : CSpace 1,
              (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) *
                (Real.exp (-‖z 0‖ ^ 2) : ℂ) ∂(volume : Measure (CSpace 1)) =
              ∫ z : ℂ,
                (HermitekLEAN.Phi k m z * conj (HermitekLEAN.Phi k n z)) *
                  (Real.exp (-‖z‖ ^ 2) : ℂ) ∂(volume : Measure ℂ) := by
            have hleft :
                ∫ z : CSpace 1,
                  (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) *
                    (Real.exp (-‖z 0‖ ^ 2) : ℂ) ∂(volume : Measure (CSpace 1)) =
                  ∫ z : CSpace 1,
                    HermitekLEAN.Phi k m (z 0) *
                      ((Real.exp (-‖z 0‖ ^ 2) : ℂ) * conj (HermitekLEAN.Phi k n (z 0)))
                      ∂(volume : Measure (CSpace 1)) := by
                  apply integral_congr_ae
                  filter_upwards with z
                  ring
            have hright :
                ∫ z : ℂ,
                  (HermitekLEAN.Phi k m z * conj (HermitekLEAN.Phi k n z)) *
                    (Real.exp (-‖z‖ ^ 2) : ℂ) ∂(volume : Measure ℂ) =
                  ∫ z : ℂ,
                    HermitekLEAN.Phi k m z *
                      ((Real.exp (-‖z‖ ^ 2) : ℂ) * conj (HermitekLEAN.Phi k n z))
                      ∂(volume : Measure ℂ) := by
                  apply integral_congr_ae
                  filter_upwards with z
                  ring
            calc
              ∫ z : CSpace 1,
                  (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) *
                    (Real.exp (-‖z 0‖ ^ 2) : ℂ) ∂(volume : Measure (CSpace 1))
                  =
                ∫ z : CSpace 1,
                  HermitekLEAN.Phi k m (z 0) *
                    ((Real.exp (-‖z 0‖ ^ 2) : ℂ) * conj (HermitekLEAN.Phi k n (z 0)))
                    ∂(volume : Measure (CSpace 1)) := hleft
              _ = ∫ z : ℂ,
                    HermitekLEAN.Phi k m z *
                      ((Real.exp (-‖z‖ ^ 2) : ℂ) * conj (HermitekLEAN.Phi k n z))
                      ∂(volume : Measure ℂ) := hcomp
              _ =
                ∫ z : ℂ,
                  (HermitekLEAN.Phi k m z * conj (HermitekLEAN.Phi k n z)) *
                    (Real.exp (-‖z‖ ^ 2) : ℂ) ∂(volume : Measure ℂ) := hright.symm
          rw [hcomp']

private theorem annulusMass_oneDimPhi_eq_annulusIntegralSq
    (k n j : ℕ) :
    annulusMass (d := 1) (fun _ => j) (oneDimLift (oneDimPhi k n)) =
      HermitekLEAN.annulusIntegralSq (HermitekLEAN.Phi k n) j := by
  classical
  change
    annulusMass (d := 1) (fun _ => j) (fun z => HermitekLEAN.Phi k n (z 0)) =
      HermitekLEAN.annulusIntegralSq (HermitekLEAN.Phi k n) j
  unfold annulusMass HermitekLEAN.annulusIntegralSq HermiteLEAN.annulusIntegralSq
  rw [gaussianMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (show Measurable (fun z : CSpace 1 => ENNReal.ofReal (gaussianDensity 1 z)) by
        unfold gaussianDensity
        fun_prop)
      (show ∀ᵐ x : CSpace 1, ENNReal.ofReal (gaussianDensity 1 x) < ⊤ by
        filter_upwards with x
        simp)]
  calc
    ∫ z : CSpace 1,
        (ENNReal.ofReal (gaussianDensity 1 z)).toReal •
          (if z ∈ productAnnulus (d := 1) (fun _ => j) then ‖HermitekLEAN.Phi k n (z 0)‖ ^ 2 else 0)
          ∂(volume : Measure (CSpace 1))
        =
      ∫ z : CSpace 1,
        ((1 / Real.pi) * Real.exp (-‖z 0‖ ^ 2)) *
          (if z ∈ productAnnulus (d := 1) (fun _ => j) then ‖HermitekLEAN.Phi k n (z 0)‖ ^ 2 else 0)
          ∂(volume : Measure (CSpace 1)) := by
          apply integral_congr_ae
          filter_upwards with z
          have hdens :
              (ENNReal.ofReal (gaussianDensity 1 z)).toReal =
                (1 / Real.pi) * Real.exp (-‖z 0‖ ^ 2) := by
            have hnonneg : 0 ≤ Real.pi⁻¹ * Real.exp (-‖z 0‖ ^ 2) := by
              positivity
            simp [gaussianDensity, hnonneg]
          rw [hdens]
          simp [smul_eq_mul]
    _ =
      (1 / Real.pi) *
        ∫ z : CSpace 1,
          if z ∈ productAnnulus (d := 1) (fun _ => j) then
            ‖HermitekLEAN.Phi k n (z 0)‖ ^ 2 * Real.exp (-‖z 0‖ ^ 2)
          else 0 ∂(volume : Measure (CSpace 1)) := by
          have hrew :
              ∫ z : CSpace 1,
                ((1 / Real.pi) * Real.exp (-‖z 0‖ ^ 2)) *
                  (if z ∈ productAnnulus (d := 1) (fun _ => j) then ‖HermitekLEAN.Phi k n (z 0)‖ ^
                      2 else 0)
                  ∂(volume : Measure (CSpace 1)) =
              ∫ z : CSpace 1,
                (1 / Real.pi) *
                  (if z ∈ productAnnulus (d := 1) (fun _ => j) then
                    ‖HermitekLEAN.Phi k n (z 0)‖ ^ 2 * Real.exp (-‖z 0‖ ^ 2)
                  else 0) ∂(volume : Measure (CSpace 1)) := by
                apply integral_congr_ae
                filter_upwards with z
                by_cases hz : z ∈ productAnnulus (d := 1) (fun _ => j) <;> simp [hz,
                    mul_left_comm, mul_comm]
          have hconst :
              ∫ z : CSpace 1,
                (1 / Real.pi) *
                  (if z ∈ productAnnulus (d := 1) (fun _ => j) then
                    ‖HermitekLEAN.Phi k n (z 0)‖ ^ 2 * Real.exp (-‖z 0‖ ^ 2)
                  else 0) =
              (1 / Real.pi) *
                ∫ z : CSpace 1,
                  if z ∈ productAnnulus (d := 1) (fun _ => j) then
                    ‖HermitekLEAN.Phi k n (z 0)‖ ^ 2 * Real.exp (-‖z 0‖ ^ 2)
                  else 0 ∂(volume : Measure (CSpace 1)) := by
                exact
                  (MeasureTheory.integral_const_mul
                    (μ := (volume : Measure (CSpace 1)))
                    (1 / Real.pi)
                    (fun z : CSpace 1 =>
                      if z ∈ productAnnulus (d := 1) (fun _ => j) then
                        ‖HermitekLEAN.Phi k n (z 0)‖ ^ 2 * Real.exp (-‖z 0‖ ^ 2)
                      else 0))
          exact hrew.trans hconst
    _ =
      (1 / Real.pi) *
        ∫ z : ℂ,
          if z ∈ HermiteLEAN.annulus j then
            ‖HermitekLEAN.Phi k n z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
          else 0 ∂(volume : Measure ℂ) := by
          let e : CSpace 1 ≃ᵐ ℂ := MeasurableEquiv.funUnique (Fin 1) ℂ
          have hEq0 :=
            ((MeasureTheory.volume_preserving_funUnique (Fin 1) ℂ).integral_comp'
              (f := e)
              (fun z : ℂ =>
                if z ∈ HermiteLEAN.annulus j then
                  ‖HermitekLEAN.Phi k n z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
                else 0))
          have he : ∀ z : CSpace 1, e z = z 0 := fun _ => rfl
          have h := congrArg ((1 / Real.pi) * ·) hEq0
          simp only [productAnnulus, HermiteLEAN.annulus, he, Set.mem_setOf_eq,
            Fin.forall_fin_one, Nat.cast_add, Nat.cast_one] at h ⊢
          exact h
    _ =
      (1 / Real.pi) *
        ∫ z in HermiteLEAN.annulus j,
          ‖HermitekLEAN.Phi k n z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ∂(volume : Measure ℂ) := by
          congr 1
          show (∫ z : ℂ, if z ∈ HermiteLEAN.annulus j then
              ‖HermitekLEAN.Phi k n z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) else 0 ∂(volume : Measure ℂ)) =
            ∫ z in HermiteLEAN.annulus j,
              ‖HermitekLEAN.Phi k n z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ∂(volume : Measure ℂ)
          rw [show (∫ z in HermiteLEAN.annulus j,
              ‖HermitekLEAN.Phi k n z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ∂(volume : Measure ℂ)) =
            ∫ z : ℂ, Set.indicator (HermiteLEAN.annulus j)
              (fun z => ‖HermitekLEAN.Phi k n z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) z
              ∂(volume : Measure ℂ) by
                symm
                rw [MeasureTheory.integral_indicator (measurableSet_complex_annulus j)]]
          simp [Set.indicator]

private theorem gaussianInner_self
    {d : ℕ} (F : CSpace d → ℂ) :
    gaussianInner F F = ((gaussianL2NormSq F : ℝ) : ℂ) := by
  unfold gaussianInner gaussianL2NormSq
  have hfun :
      (fun z : CSpace d => F z * conj (F z)) =
        fun z : CSpace d => ((‖F z‖ ^ 2 : ℝ) : ℂ) := by
    funext z
    simpa using Complex.mul_conj' (F z)
  rw [hfun, integral_complex_ofReal]

private lemma integrable_oneDimBasis_cross
    (k : ℕ) (α β : MultiIndex 1) :
    Integrable
      (fun z : CSpace 1 =>
        oneDimLift (oneDimPhi k (α 0)) z * conj (oneDimLift (oneDimPhi k (β 0)) z))
      (gaussianMeasure 1) := by
  simpa [oneDimLift] using integrable_oneDimPhi_cross_gaussian k (α 0) (β 0)

private lemma gaussianInner_finite_sum_basis_one
    (k : ℕ) (β : MultiIndex 1)
    (s : Finset (MultiIndex 1)) (c : MultiIndex 1 → ℂ) :
    gaussianInner
        (fun z : CSpace 1 => Finset.sum s (fun α => c α * oneDimLift (oneDimPhi k (α 0)) z))
        (oneDimLift (oneDimPhi k (β 0))) =
      Finset.sum s
        (fun α =>
          c α *
            gaussianInner (d := 1) (oneDimLift (oneDimPhi k (α 0))) (oneDimLift (oneDimPhi k (β
                0)))) := by
  unfold gaussianInner
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl ?_
    intro α hα
    have hconst :
        (∫ z : CSpace 1,
            c α *
              (oneDimLift (oneDimPhi k (α 0)) z * conj (oneDimLift (oneDimPhi k (β 0)) z))
            ∂gaussianMeasure 1) =
          c α *
            ∫ z : CSpace 1,
              oneDimLift (oneDimPhi k (α 0)) z * conj (oneDimLift (oneDimPhi k (β 0)) z)
              ∂gaussianMeasure 1 := by
      simpa [mul_assoc] using
        (MeasureTheory.integral_const_mul (c α)
          (fun z : CSpace 1 =>
            oneDimLift (oneDimPhi k (α 0)) z * conj (oneDimLift (oneDimPhi k (β 0)) z)))
    rw [hconst]
  · intro α hα
    simpa [mul_assoc] using (integrable_oneDimBasis_cross k α β).const_mul (c α)

private lemma gaussianInner_finite_sum_one
    (k : ℕ)
    (s t : Finset (MultiIndex 1)) (a b : MultiIndex 1 → ℂ) :
    gaussianInner
        (fun z : CSpace 1 => Finset.sum s (fun α => a α * oneDimLift (oneDimPhi k (α 0)) z))
        (fun z : CSpace 1 => Finset.sum t (fun β => b β * oneDimLift (oneDimPhi k (β 0)) z)) =
      Finset.sum t
        (fun β =>
          conj (b β) *
            gaussianInner
              (fun z : CSpace 1 => Finset.sum s (fun α => a α * oneDimLift (oneDimPhi k (α 0)) z))
              (oneDimLift (oneDimPhi k (β 0)))) := by
  unfold gaussianInner
  have hfun :
      (fun z : CSpace 1 =>
        (Finset.sum s (fun α => a α * oneDimLift (oneDimPhi k (α 0)) z)) *
          conj (Finset.sum t (fun β => b β * oneDimLift (oneDimPhi k (β 0)) z))) =
        fun z : CSpace 1 =>
          Finset.sum t
            (fun β =>
              conj (b β) *
                ((Finset.sum s (fun α => a α * oneDimLift (oneDimPhi k (α 0)) z)) *
                  conj (oneDimLift (oneDimPhi k (β 0)) z))) := by
    funext z
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro β hβ
    simp [mul_assoc, mul_comm]
  rw [hfun, MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl ?_
    intro β hβ
    have hconst :
        (∫ z : CSpace 1,
            conj (b β) *
              ((Finset.sum s (fun α => a α * oneDimLift (oneDimPhi k (α 0)) z)) *
                conj (oneDimLift (oneDimPhi k (β 0)) z))
            ∂gaussianMeasure 1) =
          conj (b β) *
            ∫ z : CSpace 1,
              (Finset.sum s (fun α => a α * oneDimLift (oneDimPhi k (α 0)) z)) *
                conj (oneDimLift (oneDimPhi k (β 0)) z)
              ∂gaussianMeasure 1 := by
      simpa [mul_assoc] using
        (MeasureTheory.integral_const_mul (conj (b β))
          (fun z : CSpace 1 =>
            (Finset.sum s (fun α => a α * oneDimLift (oneDimPhi k (α 0)) z)) *
              conj (oneDimLift (oneDimPhi k (β 0)) z)))
    rw [hconst]
  · intro β hβ
    have hsumInt :
        Integrable
          (fun z : CSpace 1 =>
            (Finset.sum s (fun α => a α * oneDimLift (oneDimPhi k (α 0)) z)) *
              conj (oneDimLift (oneDimPhi k (β 0)) z))
          (gaussianMeasure 1) := by
      rw [show (fun z : CSpace 1 =>
          (Finset.sum s (fun α => a α * oneDimLift (oneDimPhi k (α 0)) z)) *
            conj (oneDimLift (oneDimPhi k (β 0)) z)) =
          fun z : CSpace 1 =>
            Finset.sum s
              (fun α => a α *
                (oneDimLift (oneDimPhi k (α 0)) z * conj (oneDimLift (oneDimPhi k (β 0)) z))) by
            funext z
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl ?_
            intro α hα
            ring]
      refine MeasureTheory.integrable_finsetSum _ (fun α hα => ?_)
      simpa [mul_assoc] using (integrable_oneDimBasis_cross k α β).const_mul (a α)
    simpa [mul_assoc] using hsumInt.const_mul (conj (b β))

/-!
# ImportedAnalyticInputs

Statement-only scaffold for the one-variable and abstract analytic inputs.
Scaffolding notes: `ScaffoldingNotes/Imported/analytic_inputs.md`.
-/

/-- Imported one-variable basis orthonormality at fixed true-Hermite level. -/
theorem oneVariableBasisOrthonormal
    (k m n : ℕ) :
    gaussianInner (d := 1) (oneDimLift (oneDimPhi k m)) (oneDimLift (oneDimPhi k n)) =
      if m = n then (1 : ℂ) else 0 := by
  /-
  Scaffolding guidance:
  re-export the frozen one-dimensional basis theorem under a stable name.
  Downstream files only use orthonormality and finite Parseval consequences.
  -/
  rw [gaussianInner_oneDimPhi_eq_weightedInner]
  simpa using (HermitekLEAN.phi_orthonormal (k := k) (m := m) (n := n))

/-- Imported one-variable Parseval statement for finite coefficient families. -/
theorem oneVariableFiniteParseval
    (k : ℕ) (G : FiniteHermiteSum 1) :
    hermiteNormSq (d := 1) (fun _ => k) G =
      Finset.sum G.support fun n => ‖G.coeff n‖ ^ 2 := by
  /-
  Scaffolding guidance:
  keep this finite and coefficient-facing; no closure language is needed by
  the higher-dimensional files.
  -/
  classical
  have heval :
      evalHermiteSum (fun _ => k) G =
        (fun z : CSpace 1 =>
          Finset.sum G.support (fun α => G.coeff α * oneDimLift (oneDimPhi k (α 0)) z)) := by
    funext z
    simp [evalHermiteSum, PhiKappaAlpha, oneDimLift]
  have hinner :
      gaussianInner (evalHermiteSum (fun _ => k) G) (evalHermiteSum (fun _ => k) G) =
        Finset.sum G.support fun α => G.coeff α * conj (G.coeff α) := by
    calc
      gaussianInner (evalHermiteSum (fun _ => k) G) (evalHermiteSum (fun _ => k) G) =
        gaussianInner
          (fun z : CSpace 1 =>
            Finset.sum G.support (fun α => G.coeff α * oneDimLift (oneDimPhi k (α 0)) z))
          (fun z : CSpace 1 =>
            Finset.sum G.support (fun α => G.coeff α * oneDimLift (oneDimPhi k (α 0)) z)) := by
              simpa using congrArg₂ gaussianInner heval heval
      _ = Finset.sum G.support
            (fun α => G.coeff α * conj (G.coeff α)) := by
        rw [gaussianInner_finite_sum_one (k := k) (s := G.support) (t := G.support)
          (a := G.coeff) (b := G.coeff)]
        calc
      Finset.sum G.support
        (fun β =>
          conj (G.coeff β) *
            gaussianInner
              (fun z =>
                Finset.sum G.support
                  (fun α => G.coeff α * oneDimLift (oneDimPhi k (α 0)) z))
              (oneDimLift (oneDimPhi k (β 0)))) =
        Finset.sum G.support
          (fun β =>
            conj (G.coeff β) *
            Finset.sum G.support
              (fun α =>
                G.coeff α *
                gaussianInner
                  (oneDimLift (oneDimPhi k (α 0)))
                  (oneDimLift (oneDimPhi k (β 0))))) := by
            refine Finset.sum_congr rfl ?_
            intro β hβ
            rw [gaussianInner_finite_sum_basis_one (k := k) (β := β)
              (s := G.support) (c := G.coeff)]
        _ =
          Finset.sum G.support (fun β => conj (G.coeff β) * G.coeff β) := by
            refine Finset.sum_congr rfl ?_
            intro β hβ
            rw [Finset.sum_eq_single β]
            · simp [oneVariableBasisOrthonormal]
            · intro α hα hne
              have hne0 : α 0 ≠ β 0 := by
                intro h0
                apply hne
                ext q
                fin_cases q
                simpa using h0
              simp [oneVariableBasisOrthonormal, hne0]
            · intro hnotin
              exact False.elim (hnotin hβ)
        _ = Finset.sum G.support (fun α => G.coeff α * conj (G.coeff α)) := by
            refine Finset.sum_congr rfl ?_
            intro α hα
            ring
  unfold hermiteNormSq
  have hsq :
      gaussianL2NormSq (evalHermiteSum (fun _ => k) G) =
        Finset.sum G.support fun α => ‖G.coeff α‖ ^ 2 := by
    apply Complex.ofReal_injective
    calc
      (((gaussianL2NormSq (evalHermiteSum (fun _ => k) G) : ℝ)) : ℂ)
          = gaussianInner (evalHermiteSum (fun _ => k) G) (evalHermiteSum (fun _ => k) G) := by
              symm
              exact gaussianInner_self (F := evalHermiteSum (fun _ => k) G)
      _ = Finset.sum G.support (fun α => G.coeff α * conj (G.coeff α)) := hinner
      _ = (((Finset.sum G.support fun α => ‖G.coeff α‖ ^ 2 : ℝ)) : ℂ) := by
            simp [Complex.mul_conj']
  exact hsq

/-- Imported one-variable localization estimate for `n ≥ 1`. -/
theorem oneVariableLocalization
    (k : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ n j : ℕ, 1 ≤ n →
        annulusMass (d := 1) (fun _ => j) (oneDimLift (oneDimPhi k n)) ≤
          C *
            Real.exp
              (-c *
                max (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0 ^ 2) := by
  /-
  Scaffolding guidance:
  the scaffold keeps the quantifier/hypothesis shape `n ≥ 1`.
  The imported theorem is existential in the localization constants and should
  not be silently strengthened.
  -/
  obtain ⟨C, c, hC, hc, hloc⟩ := HermitekLEAN.single_basis_localization k
  refine ⟨C, c, hC, hc, ?_⟩
  intro n j hn
  rw [annulusMass_oneDimPhi_eq_annulusIntegralSq]
  simpa [oneDimPhi, HermitekLEAN.posPart, HermiteLEAN.posPart] using hloc n j hn

private lemma zero_shift_exp_compare
    (k j : ℕ) (c0 : ℝ) (hc0 : 0 < c0) :
    Real.exp (-c0 * (posPart ((j : ℝ) - ((k + 5 : ℕ) : ℝ))) ^ 2) ≤
      Real.exp c0 *
        Real.exp (-((c0 / 4) * (posPart ((j : ℝ) - ((k + 4 : ℕ) : ℝ))) ^ 2)) := by
  by_cases hsmall : j ≤ k + 4
  · have hx : posPart ((j : ℝ) - ((k + 4 : ℕ) : ℝ)) = 0 := by
      apply max_eq_right
      exact sub_nonpos.mpr (by exact_mod_cast hsmall)
    have hy : posPart ((j : ℝ) - ((k + 5 : ℕ) : ℝ)) = 0 := by
      apply max_eq_right
      exact sub_nonpos.mpr (by exact_mod_cast Nat.le_trans hsmall (Nat.le_succ _))
    rw [hx, hy]
    simpa using (Real.one_le_exp_iff.mpr hc0.le)
  · have hbig : k + 5 ≤ j := by omega
    have hx :
        posPart ((j : ℝ) - ((k + 4 : ℕ) : ℝ)) =
          (j : ℝ) - ((k + 4 : ℕ) : ℝ) := by
      apply max_eq_left
      exact sub_nonneg.mpr (by exact_mod_cast Nat.le_trans (Nat.le_succ _) hbig)
    have hy :
        posPart ((j : ℝ) - ((k + 5 : ℕ) : ℝ)) =
          (j : ℝ) - ((k + 5 : ℕ) : ℝ) := by
      apply max_eq_left
      exact sub_nonneg.mpr (by exact_mod_cast hbig)
    have hrel :
        (j : ℝ) - ((k + 4 : ℕ) : ℝ) =
          ((j : ℝ) - ((k + 5 : ℕ) : ℝ)) + 1 := by
      norm_num [Nat.cast_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    rw [hx, hy, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    let y : ℝ := (j : ℝ) - ((k + 5 : ℕ) : ℝ)
    have hybound : 2 * y ≤ y ^ 2 + 1 := by
      nlinarith [sq_nonneg (y - 1)]
    have hsq : (y + 1) ^ 2 ≤ 4 * (y ^ 2 + 1) := by
      nlinarith
    have hsq' :
        ((j : ℝ) - ((k + 4 : ℕ) : ℝ)) ^ 2 ≤
          4 * (((j : ℝ) - ((k + 5 : ℕ) : ℝ)) ^ 2 + 1) := by
      rw [hrel]
      simpa [y] using hsq
    nlinarith [hc0, hsq']

/-- Imported positive-frequency circle estimate with frozen constant `144`. -/
theorem positiveFrequencyCircleEstimate
    (E : Finset ℕ) (b : ℕ → ℂ)
    (hpos : ∀ n ∈ E, 0 < n)
    (_hP : HasPositiveFrequencySupport (positiveFrequencyPolynomial E b) E) :
    circleL2NormSq (positiveFrequencyPolynomial E b) ≤
      144 * E.card * circleL2NormSq (fun t => rho 1 (positiveFrequencyPolynomial E b t)) := by
  /-
  Scaffolding guidance:
  this is the circle estimate used on low annuli. Keep the positive-frequency
  hypothesis explicit and keep the exact constant `144`.
  -/
  rw [show circleL2NormSq (positiveFrequencyPolynomial E b) =
      HermiteLEAN.circleL2Sq (HermiteLEAN.positiveTrigonometricPolynomial E b) by
      rfl]
  rw [show circleL2NormSq (fun t => rho 1 (positiveFrequencyPolynomial E b t)) =
      HermiteLEAN.circleRhoNormSq (HermiteLEAN.positiveTrigonometricPolynomial E b) by
      simp [circleL2NormSq, rho, positiveFrequencyPolynomial, HermiteLEAN.circleRhoNormSq,
        HermiteLEAN.positiveTrigonometricPolynomial, HermiteLEAN.rho, sq_abs]]
  simpa using
    HermitekLEAN.local_circle_estimate E
      (by
        intro n hn
        exact Nat.succ_le_of_lt (hpos n hn))
      b

/-- Imported high-frequency band estimate with frozen constants `32` and `1343`. -/
theorem highFrequencyBandEstimate
    (N L : ℕ) (c : Fin L → ℂ)
    (hgap : 1343 * L ^ 2 ≤ N ^ 2)
    (hP : HasBandlimitedSupport (bandLimitedPolynomial N L c) N L) :
    circleL2NormSq (bandLimitedPolynomial N L c) ≤
      32 * circleL2NormSq (fun t => rho 1 (bandLimitedPolynomial N L c t)) := by
  /-
  Scaffolding guidance:
  this is the band-limited estimate used after the degree-threshold argument.
  Preserve the exact constants and the separate support hypothesis.
  -/
  by_cases hL0 : L = 0
  · subst hL0
    simp only [circleL2NormSq, bandLimitedPolynomial, univ_eq_empty, Nat.cast_add, fourier_apply,
      fourier_add', natCast_zsmul, sum_empty, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, integral_zero, norm_eq_abs, sq_abs, integral_const,
      probReal_univ, smul_eq_mul, one_mul, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
    positivity
  · have hL : 1 ≤ L := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hL0)
    have hNsqpos : 0 < N ^ 2 := by
      have hpos : 0 < 1343 * L ^ 2 := by positivity
      exact lt_of_lt_of_le hpos hgap
    have hNpos : 0 < N := by
      exact Nat.pos_of_ne_zero (by intro hN0; rw [hN0] at hNsqpos; simp at hNsqpos)
    have hN : 1 ≤ N := Nat.succ_le_of_lt hNpos
    have hBandEq := positiveBandEq N L hL c
    calc
      circleL2NormSq (bandLimitedPolynomial N L c)
          = HermiteLEAN.circleL2Sq
              (HermiteLEAN.positiveTrigonometricPolynomial
                (HermiteLEAN.frequencyBand N L) (bandCoeff N L c)) := by
            rw [hBandEq]
            rfl
      _ ≤ 32 * HermiteLEAN.circleRhoNormSq
            (HermiteLEAN.positiveTrigonometricPolynomial
              (HermiteLEAN.frequencyBand N L) (bandCoeff N L c)) := by
            have hgap_real : 1343 * (L : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
              exact_mod_cast hgap
            simpa using
              HermitekLEAN.high_frequency_circle_estimate N L hN hL (bandCoeff N L c)
                hgap_real
      _ = 32 * circleL2NormSq (fun t => rho 1 (bandLimitedPolynomial N L c t)) := by
            rw [hBandEq]
            simp [circleL2NormSq, rho, HermiteLEAN.circleRhoNormSq, HermiteLEAN.rho,
              sq_abs]

/-- Project-owned upgrade of localization that now includes the zero mode. -/
theorem localizationIncludingZero
    (k : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ n j : ℕ,
        annulusMass (d := 1) (fun _ => j) (oneDimLift (oneDimPhi k n)) ≤
          C *
            Real.exp
              (-c *
                max (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0 ^ 2) := by
  /-
  Scaffolding guidance:
  derive the `n = 0` case directly from the explicit formula, then package
  the all-`n` statement for downstream reuse.
  -/
  obtain ⟨C1, c1, hC1, hc1, hloc1⟩ := oneVariableLocalization k
  obtain ⟨C0, c0, hC0, hc0, hloc0⟩ := HermitekLEAN.phi0_localization k
  let C : ℝ := max C1 (C0 * Real.exp c0)
  let c : ℝ := min c1 (c0 / 4)
  refine ⟨C, c, ?_, ?_, ?_⟩
  · dsimp [C]
    exact lt_of_lt_of_le hC1 (le_max_left _ _)
  · dsimp [c]
    have hc04 : 0 < c0 / 4 := by positivity
    exact lt_min hc1 hc04
  · intro n j
    by_cases hn : n = 0
    · subst hn
      have hexact :
          max (|((j : ℕ) : ℝ) - Real.sqrt ((0 : ℕ) : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0 =
            posPart ((j : ℝ) - ((k + 4 : ℕ) : ℝ)) := by
        simp [Real.sqrt_zero, posPart]
      have hexact_sq :
          max (|((j : ℕ) : ℝ) - Real.sqrt ((0 : ℕ) : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0 ^ 2 =
            (posPart ((j : ℝ) - ((k + 4 : ℕ) : ℝ))) ^ 2 := by
        exact congrArg (fun x : ℝ => x ^ 2) hexact
      rw [annulusMass_oneDimPhi_eq_annulusIntegralSq]
      have hphi0 :
          HermitekLEAN.annulusIntegralSq (HermitekLEAN.Phi k 0) j ≤
            C0 * Real.exp (-c0 * (posPart ((j : ℝ) - ((k + 5 : ℕ) : ℝ))) ^ 2) := by
        simpa [oneDimPhi, HermitekLEAN.phi0, HermitekLEAN.posPart, HermiteLEAN.posPart,
          _root_.posPart_def] using hloc0 j
      have hcompare := zero_shift_exp_compare k j c0 hc0
      have hCle : C0 * Real.exp c0 ≤ C := by
        dsimp [C]
        exact le_max_right _ _
      have hcle : c ≤ c0 / 4 := by
        dsimp [c]
        exact min_le_right _ _
      calc
        HermitekLEAN.annulusIntegralSq (HermitekLEAN.Phi k 0) j
            ≤ C0 * Real.exp (-c0 * (posPart ((j : ℝ) - ((k + 5 : ℕ) : ℝ))) ^ 2) := hphi0
        _ ≤ (C0 * Real.exp c0) *
              Real.exp (-((c0 / 4) * (posPart ((j : ℝ) - ((k + 4 : ℕ) : ℝ))) ^ 2)) := by
              have := mul_le_mul_of_nonneg_left hcompare (le_of_lt hC0)
              simpa [mul_assoc, mul_left_comm, mul_comm] using this
        _ ≤ C * Real.exp (-((c0 / 4) * (posPart ((j : ℝ) - ((k + 4 : ℕ) : ℝ))) ^ 2)) := by
              have hexp_nonneg :
                  0 ≤ Real.exp (-((c0 / 4) * (posPart ((j : ℝ) - ((k + 4 : ℕ) : ℝ))) ^ 2)) := by
                positivity
              exact mul_le_mul_of_nonneg_right hCle hexp_nonneg
        _ ≤ C * Real.exp (-(c * (posPart ((j : ℝ) - ((k + 4 : ℕ) : ℝ))) ^ 2)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              apply Real.exp_le_exp.mpr
              have hxnonneg :
                  0 ≤ (posPart ((j : ℝ) - ((k + 4 : ℕ) : ℝ))) ^ 2 := by positivity
              nlinarith
        _ = C * Real.exp (-c *
              max (|((j : ℕ) : ℝ) - Real.sqrt ((0 : ℕ) : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0 ^ 2) := by
              rw [hexact_sq]
              ring_nf
    · have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
      have hbase := hloc1 n j hn1
      have hCle : C1 ≤ C := by
        dsimp [C]
        exact le_max_left _ _
      have hcle : c ≤ c1 := by
        dsimp [c]
        exact min_le_left _ _
      calc
        annulusMass (d := 1) (fun _ => j) (oneDimLift (oneDimPhi k n))
            ≤ C1 *
              Real.exp
                (-c1 *
                  max (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0 ^ 2) := hbase
        _ ≤ C *
              Real.exp
                (-c1 *
                  max (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0 ^ 2) := by
              have hexp_nonneg :
                  0 ≤ Real.exp
                    (-c1 *
                      max (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0 ^ 2) := by
                positivity
              exact mul_le_mul_of_nonneg_right hCle hexp_nonneg
        _ ≤ C *
              Real.exp
                (-c *
                  max (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0 ^ 2) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              apply Real.exp_le_exp.mpr
              have hxnonneg :
                  0 ≤
                    max (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0 ^ 2 := by
                positivity
              nlinarith

/-- Scalar-rescaled positive-frequency estimate for an arbitrary background `a`. -/
theorem scaledPositiveFrequencyCircleEstimate
    (a : ℂ) (E : Finset ℕ) (P : Circle → ℂ)
    (hpos : ∀ n ∈ E, 0 < n)
    (hP : HasPositiveFrequencySupport P E) :
    circleL2NormSq P ≤ 144 * E.card * circleL2NormSq (fun t => rho a (P t)) := by
  /-
  Scaffolding guidance:
  normalize by `a` when `a ≠ 0`, and keep the `a = 0` branch separate.
  Export the final statement so later files do not redo the rescaling.
  -/
  by_cases ha : a = 0
  · subst ha
    rcases hP with ⟨b, rfl⟩
    by_cases hE : E = ∅
    · subst hE
      simp [positiveFrequencyPolynomial, circleL2NormSq, rho]
    · have hnonneg : 0 ≤ circleL2NormSq (positiveFrequencyPolynomial E b) := by
        unfold circleL2NormSq
        positivity
      have hcard : 0 < E.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hE)
      have hcardR : (0 : ℝ) < E.card := by
        exact_mod_cast hcard
      have honeR : (1 : ℝ) ≤ E.card := by
        exact_mod_cast (Nat.succ_le_of_lt hcard)
      have hfac : (1 : ℝ) ≤ 144 * (E.card : ℝ) := by
        nlinarith
      calc
        circleL2NormSq (positiveFrequencyPolynomial E b)
            = 1 * circleL2NormSq (positiveFrequencyPolynomial E b) := by ring
        _ ≤ 144 * E.card * circleL2NormSq (positiveFrequencyPolynomial E b) := by
              exact mul_le_mul_of_nonneg_right hfac hnonneg
        _ =
          144 * E.card *
            circleL2NormSq (fun t => rho 0 (positiveFrequencyPolynomial E b t)) := by
              simp [circleL2NormSq, rho]
  · rcases hP with ⟨b, rfl⟩
    let Q : Circle → ℂ := positiveFrequencyPolynomial E (fun n => a⁻¹ * b n)
    have hQ : HasPositiveFrequencySupport Q E := ⟨fun n => a⁻¹ * b n, rfl⟩
    have hbase :=
      positiveFrequencyCircleEstimate E (fun n => a⁻¹ * b n) hpos hQ
    have hbaseQ :
        circleL2NormSq Q ≤
          144 * E.card * circleL2NormSq (fun t => rho 1 (Q t)) := by
      simpa [Q] using hbase
    have hmulP : (fun t => a * Q t) = positiveFrequencyPolynomial E b := by
      funext t
      simp only [Q, positiveFrequencyPolynomial, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro n hn
      field_simp [ha]
    have hmulR : (fun t => rho a (a * Q t)) = fun t => ‖a‖ * rho 1 (Q t) := by
      funext t
      simp [rho_mul_right]
    rw [← hmulP]
    rw [circleL2NormSq_const_mul]
    have hconstR :
        circleL2NormSq (fun t => ‖a‖ * rho 1 (Q t)) =
          ‖a‖ ^ 2 * circleL2NormSq (fun t => rho 1 (Q t)) := by
      unfold circleL2NormSq
      calc
        ∫ t, ‖‖a‖ * rho 1 (Q t)‖ ^ 2 ∂AddCircle.haarAddCircle
            = ∫ t, (‖a‖ ^ 2) * ‖rho 1 (Q t)‖ ^ 2 ∂AddCircle.haarAddCircle := by
                apply integral_congr_ae
                filter_upwards with t
                have hrho_nn : 0 ≤ rho 1 (Q t) := by
                  exact abs_nonneg _
                have hnorm : ‖‖a‖ * rho 1 (Q t)‖ = ‖a‖ * rho 1 (Q t) := by
                  apply abs_of_nonneg
                  exact mul_nonneg (norm_nonneg _) hrho_nn
                rw [hnorm]
                have hrhonorm : ‖rho 1 (Q t)‖ = rho 1 (Q t) := by
                  simpa [Real.norm_eq_abs] using abs_of_nonneg hrho_nn
                rw [hrhonorm]
                ring
        _ = ‖a‖ ^ 2 * ∫ t, ‖rho 1 (Q t)‖ ^ 2 ∂AddCircle.haarAddCircle := by
              rw [MeasureTheory.integral_const_mul]
    calc
      ‖a‖ ^ 2 * circleL2NormSq Q ≤
          144 * E.card * (‖a‖ ^ 2 * circleL2NormSq (fun t => rho 1 (Q t))) := by
            have hscaled := mul_le_mul_of_nonneg_left hbaseQ (sq_nonneg ‖a‖)
            simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
      _ = 144 * E.card * circleL2NormSq (fun t => ‖a‖ * rho 1 (Q t)) := by
            rw [hconstR]
      _ = 144 * E.card * circleL2NormSq (fun t => rho a (a * Q t)) := by
            rw [hmulR]

/-- Scalar-rescaled high-frequency estimate for an arbitrary background `a`. -/
theorem scaledHighFrequencyBandEstimate
    (a : ℂ) (N L : ℕ) (P : Circle → ℂ)
    (hgap : 1343 * L ^ 2 ≤ N ^ 2)
    (hP : HasBandlimitedSupport P N L) :
    circleL2NormSq P ≤ 32 * circleL2NormSq (fun t => rho a (P t)) := by
  by_cases ha : a = 0
  · subst ha
    have hnonneg : 0 ≤ circleL2NormSq P := by
      unfold circleL2NormSq
      positivity
    calc
      circleL2NormSq P ≤ 32 * circleL2NormSq P := by
        nlinarith
      _ = 32 * circleL2NormSq (fun t => rho 0 (P t)) := by
        simp [circleL2NormSq, rho]
  · rcases hP with ⟨c, rfl⟩
    let Q : Circle → ℂ := bandLimitedPolynomial N L (fun m => a⁻¹ * c m)
    have hQ : HasBandlimitedSupport Q N L := ⟨fun m => a⁻¹ * c m, rfl⟩
    have hbase := highFrequencyBandEstimate N L (fun m => a⁻¹ * c m) hgap hQ
    have hbaseQ : circleL2NormSq Q ≤ 32 * circleL2NormSq (fun t => rho 1 (Q t)) := by
      simpa [Q] using hbase
    have hmulP : (fun t => a * Q t) = bandLimitedPolynomial N L c := by
      funext t
      simp only [Q, bandLimitedPolynomial, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro m hm
      field_simp [ha]
    have hmulR : (fun t => rho a (a * Q t)) = fun t => ‖a‖ * rho 1 (Q t) := by
      funext t
      simp [rho_mul_right]
    rw [← hmulP]
    rw [circleL2NormSq_const_mul]
    have hscaled :=
      mul_le_mul_of_nonneg_left hbase (sq_nonneg ‖a‖)
    have hconstR :
        circleL2NormSq (fun t => ‖a‖ * rho 1 (Q t)) =
          ‖a‖ ^ 2 * circleL2NormSq (fun t => rho 1 (Q t)) := by
      unfold circleL2NormSq
      calc
        ∫ t, ‖‖a‖ * rho 1 (Q t)‖ ^ 2 ∂AddCircle.haarAddCircle
            = ∫ t, (‖a‖ ^ 2) * ‖rho 1 (Q t)‖ ^ 2 ∂AddCircle.haarAddCircle := by
                apply integral_congr_ae
                filter_upwards with t
                have hrho_nn : 0 ≤ rho 1 (Q t) := by
                  exact abs_nonneg _
                have hnorm : ‖‖a‖ * rho 1 (Q t)‖ = ‖a‖ * rho 1 (Q t) := by
                  apply abs_of_nonneg
                  exact mul_nonneg (norm_nonneg _) hrho_nn
                rw [hnorm]
                have hrhonorm : ‖rho 1 (Q t)‖ = rho 1 (Q t) := by
                  simpa [Real.norm_eq_abs] using abs_of_nonneg hrho_nn
                rw [hrhonorm]
                ring
        _ = ‖a‖ ^ 2 * ∫ t, ‖rho 1 (Q t)‖ ^ 2 ∂AddCircle.haarAddCircle := by
              rw [MeasureTheory.integral_const_mul]
    calc
      ‖a‖ ^ 2 * circleL2NormSq Q ≤
          32 * (‖a‖ ^ 2 * circleL2NormSq (fun t => rho 1 (Q t))) := by
            exact mul_le_mul_of_nonneg_left hbaseQ (sq_nonneg ‖a‖) |>.trans_eq (by ring)
      _ = 32 * circleL2NormSq (fun t => ‖a‖ * rho 1 (Q t)) := by
            rw [hconstR]
      _ = 32 * circleL2NormSq (fun t => rho a (a * Q t)) := by
            rw [hmulR]

/-- One-variable angular factorization used in the annulus orthogonality argument. -/
private lemma oneVariableAngularFactorization_termwise
    (r t : ℝ) (k n j : ℕ) (hjk : j ≤ k) (hjn : j ≤ n) :
    (r : ℂ) ^ (k - j) *
      ((r : ℂ) ^ (n - j) *
        (Complex.exp (Complex.I * (t : ℂ)) ^ (n - j) *
          ((Nat.choose k j : ℂ) *
            ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ) *
              (Complex.exp (-(Complex.I * (t : ℂ))) ^ (k - j) *
                ((-1 : ℂ) ^ j * ((↑√↑k.factorial)⁻¹ * (↑√↑n.factorial)⁻¹))))))) =
    Complex.exp (Complex.I * (↑t * (↑n - ↑k))) *
      ((Nat.choose k j : ℂ) *
        ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ) *
          ((-1 : ℂ) ^ j * ((↑r : ℂ) ^ (n + k - j * 2) * ((↑√↑k.factorial)⁻¹ *
              (↑√↑n.factorial)⁻¹))))) := by
  have hrpow :
      (r : ℂ) ^ (k - j) * (r : ℂ) ^ (n - j) =
        (r : ℂ) ^ (n + k - j * 2) := by
    rw [← pow_add]
    have hpow : (k - j) + (n - j) = n + k - j * 2 := by
      omega
    rw [hpow]
  have hphase :
      Complex.exp (Complex.I * (t : ℂ)) ^ (n - j) *
          Complex.exp (-(Complex.I * (t : ℂ))) ^ (k - j) =
        Complex.exp (Complex.I * (↑t * (↑n - ↑k))) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    have hsub : (↑(n - j) : ℂ) - (↑(k - j) : ℂ) = (n : ℂ) - k := by
      norm_num [Nat.cast_sub hjn, Nat.cast_sub hjk]
    calc
      (↑(n - j) : ℂ) * (Complex.I * (t : ℂ)) + (↑(k - j) : ℂ) * (-(Complex.I * (t : ℂ)))
          = Complex.I * (t : ℂ) * ((↑(n - j) : ℂ) - (↑(k - j) : ℂ)) := by ring
      _ = Complex.I * (t : ℂ) * ((n : ℂ) - k) := by rw [hsub]
      _ = Complex.I * (↑t * (↑n - ↑k)) := by ring
  calc
    (r : ℂ) ^ (k - j) *
        ((r : ℂ) ^ (n - j) *
          (Complex.exp (Complex.I * (t : ℂ)) ^ (n - j) *
            ((Nat.choose k j : ℂ) *
              ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ) *
                (Complex.exp (-(Complex.I * (t : ℂ))) ^ (k - j) *
                  ((-1 : ℂ) ^ j * ((↑√↑k.factorial)⁻¹ * (↑√↑n.factorial)⁻¹))))))) =
      ((r : ℂ) ^ (k - j) * (r : ℂ) ^ (n - j)) *
        ((Complex.exp (Complex.I * (t : ℂ)) ^ (n - j) *
            Complex.exp (-(Complex.I * (t : ℂ))) ^ (k - j)) *
          ((Nat.choose k j : ℂ) *
            ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ) *
              ((-1 : ℂ) ^ j * ((↑√↑k.factorial)⁻¹ * (↑√↑n.factorial)⁻¹))))) := by
          ring
    _ =
      (↑r : ℂ) ^ (n + k - j * 2) *
        (Complex.exp (Complex.I * (↑t * (↑n - ↑k))) *
          ((Nat.choose k j : ℂ) *
            ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ) *
              ((-1 : ℂ) ^ j * ((↑√↑k.factorial)⁻¹ * (↑√↑n.factorial)⁻¹))))) := by
          rw [hrpow, hphase]
    _ =
      Complex.exp (Complex.I * (↑t * (↑n - ↑k))) *
        ((Nat.choose k j : ℂ) *
          ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ) *
            ((-1 : ℂ) ^ j * ((↑r : ℂ) ^ (n + k - j * 2) * ((↑√↑k.factorial)⁻¹ *
                (↑√↑n.factorial)⁻¹))))) := by
          ring

theorem oneVariableAngularFactorization
    (k n : ℕ) :
    ∃ radial : Polynomial ℝ,
      ∀ r t : ℝ,
        oneDimPhi k n ((r : ℂ) * Complex.exp (Complex.I * t)) =
          Complex.exp (Complex.I * ((((n : ℤ) - (k : ℤ)) : ℂ) * t)) *
            radial.eval₂ (algebraMap ℝ ℂ) r := by
  let radial : Polynomial ℝ :=
    Finset.sum (Finset.range (min k n + 1)) fun j =>
      Polynomial.monomial (n + k - j * 2)
        (((Nat.choose k j : ℝ) *
            ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ))) *
          (((-1 : ℝ) ^ j) *
            (((Real.sqrt (Nat.factorial k : ℝ))⁻¹) *
              ((Real.sqrt (Nat.factorial n : ℝ))⁻¹))))
  refine ⟨radial, ?_⟩
  intro r t
  have hnorm :
      (1 / (↑(Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ)) =
        ((↑(Real.sqrt (Nat.factorial k : ℝ)))⁻¹ *
          (↑(Real.sqrt (Nat.factorial n : ℝ)))⁻¹ : ℂ) := by
    have hnormR :
        (1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) =
          (Real.sqrt (Nat.factorial k : ℝ))⁻¹ *
            (Real.sqrt (Nat.factorial n : ℝ))⁻¹ := by
      rw [Real.sqrt_mul (show (0 : ℝ) ≤ Nat.factorial k by positivity)]
      field_simp
        [Real.sqrt_ne_zero'.2
          (by exact_mod_cast Nat.factorial_pos k : (0 : ℝ) < Nat.factorial k),
         Real.sqrt_ne_zero'.2
          (by exact_mod_cast Nat.factorial_pos n : (0 : ℝ) < Nat.factorial n)]
    exact_mod_cast hnormR
  have hstar_z :
      star ((r : ℂ) * Complex.exp (Complex.I * t)) =
        (r : ℂ) * Complex.exp (-(Complex.I * t)) := by
    calc
      star ((r : ℂ) * Complex.exp (Complex.I * t)) =
          star (r : ℂ) * star (Complex.exp (Complex.I * t)) := by
            simp
      _ = (r : ℂ) * star (Complex.exp (Complex.I * t)) := by simp
      _ = (r : ℂ) * Complex.exp (star (Complex.I * t)) := by
            simpa using
              congrArg (fun z : ℂ => (r : ℂ) * z) (Complex.exp_conj (Complex.I * t)).symm
      _ = (r : ℂ) * Complex.exp (-(Complex.I * t)) := by simp
  have hphaseCast :
      Complex.exp (Complex.I * ((((n : ℤ) - (k : ℤ)) : ℂ) * t)) =
        Complex.exp (Complex.I * (↑t * (↑n - ↑k))) := by
    congr 1
    calc
      Complex.I * ((((n : ℤ) - (k : ℤ)) : ℂ) * t) =
          Complex.I * (t : ℂ) * ((n : ℂ) - k) := by
            norm_num
            ring
      _ = Complex.I * (↑t * (↑n - ↑k)) := by ring
  unfold oneDimPhi
  rw [hphaseCast, hnorm, Finset.mul_sum]
  have hsum :
      Finset.sum (Finset.range (min k n + 1))
        (fun j =>
          ((↑(Real.sqrt (Nat.factorial k : ℝ)))⁻¹ *
              (↑(Real.sqrt (Nat.factorial n : ℝ)))⁻¹) *
            (((-1 : ℂ) ^ j * ↑(Nat.choose k j) *
                  (↑(Nat.factorial n) / ↑(Nat.factorial (n - j)))) *
              (((r : ℂ) * Complex.exp (Complex.I * ↑t)) ^ (n - j) *
                star ((r : ℂ) * Complex.exp (Complex.I * ↑t)) ^ (k - j)))) =
      Complex.exp (Complex.I * (↑t * (↑n - ↑k))) *
        Finset.sum (Finset.range (min k n + 1))
          (fun j =>
            ↑(Nat.choose k j) *
              (↑(Nat.factorial n) / ↑(Nat.factorial (n - j)) *
                ((-1 : ℂ) ^ j *
                  ((r : ℂ) ^ (n + k - j * 2) *
                    ((↑(Real.sqrt (Nat.factorial k : ℝ)))⁻¹ *
                      (↑(Real.sqrt (Nat.factorial n : ℝ)))⁻¹))))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjk : j ≤ k := by
      simp at hj
      omega
    have hjn : j ≤ n := by
      simp at hj
      omega
    rw [hstar_z, mul_pow, mul_pow]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      oneVariableAngularFactorization_termwise r t k n j hjk hjn
  have hsum' :
      Finset.sum (Finset.range (min k n + 1))
        (fun i =>
          ((↑(Real.sqrt (Nat.factorial k : ℝ)))⁻¹ *
                (↑(Real.sqrt (Nat.factorial n : ℝ)))⁻¹) *
              ((-1 : ℂ) ^ i * ↑(Nat.choose k i) *
                    (↑(Nat.factorial n) / ↑(Nat.factorial (n - i))) *
                  ((r : ℂ) * Complex.exp (Complex.I * ↑t)) ^ (n - i) *
                star ((r : ℂ) * Complex.exp (Complex.I * ↑t)) ^ (k - i))) =
      Complex.exp (Complex.I * (↑t * (↑n - ↑k))) *
        Finset.sum (Finset.range (min k n + 1))
          (fun j =>
            ↑(Nat.choose k j) *
              (↑(Nat.factorial n) / ↑(Nat.factorial (n - j)) *
                ((-1 : ℂ) ^ j *
                  ((r : ℂ) ^ (n + k - j * 2) *
                    ((↑(Real.sqrt (Nat.factorial k : ℝ)))⁻¹ *
                      (↑(Real.sqrt (Nat.factorial n : ℝ)))⁻¹))))) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hsum
  rw [hsum']
  congr 1
  simp [radial, Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial,
    mul_assoc, mul_left_comm, mul_comm]

/-- Gaussian density splits into first-coordinate and tail factors. -/
private lemma gaussianDensity_succ_split
    (d : ℕ) (z : CSpace (d + 1)) :
    gaussianDensity (d + 1) z =
      gaussianDensity 1 (fun _ : Fin 1 => z 0) *
        gaussianDensity d (fun q : Fin d => z (Fin.succ q)) := by
  unfold gaussianDensity
  rw [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_one]
  rw [pow_succ, neg_add, Real.exp_add]
  field_simp [Real.pi_pos.ne']

/-- Gaussian density factors pointwise into one-dimensional densities. -/
private lemma gaussianDensity_eq_prod
    (d : ℕ) (z : CSpace d) :
    gaussianDensity d z =
      ∏ q : Fin d, gaussianDensity 1 (fun _ : Fin 1 => z q) := by
  induction d with
  | zero =>
      simp [gaussianDensity]
  | succ d ih =>
      rw [gaussianDensity_succ_split]
      rw [ih]
      rw [Fin.prod_univ_succ]

private lemma integrable_weighted_coord_of_integrable_gaussian
    (f g : ℂ → ℂ)
    (hfg :
      Integrable
        (fun z : CSpace 1 => f (z 0) * conj (g (z 0)))
        (gaussianMeasure 1)) :
    Integrable
      (fun z : ℂ =>
        (((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) *
          (f z * conj (g z)))
      (volume : Measure ℂ) := by
  have hsmul :
      Integrable
        (fun z : CSpace 1 =>
          (ENNReal.ofReal (gaussianDensity 1 z)).toReal •
            (f (z 0) * conj (g (z 0))))
        (volume : Measure (CSpace 1)) := by
    rw [gaussianMeasure] at hfg
    exact
      (integrable_withDensity_iff_integrable_smul'
        (show Measurable (fun z : CSpace 1 => ENNReal.ofReal (gaussianDensity 1 z)) by
          unfold gaussianDensity
          fun_prop)
        (show ∀ᵐ x : CSpace 1, ENNReal.ofReal (gaussianDensity 1 x) < ⊤ by
          filter_upwards with x
          simp)).1 hfg
  let e : ℂ ≃ᵐ CSpace 1 := (MeasurableEquiv.funUnique (Fin 1) ℂ).symm
  have hcomp :
      Integrable
        (fun z : ℂ =>
          (ENNReal.ofReal (gaussianDensity 1 (e z))).toReal •
            (f ((e z) 0) * conj (g ((e z) 0))))
        (volume : Measure ℂ) := by
    have h :=
      (MeasureTheory.volume_preserving_funUnique (Fin 1) ℂ).symm.integrable_comp_of_integrable
        (g := fun z : CSpace 1 =>
          (ENNReal.ofReal (gaussianDensity 1 z)).toReal •
            (f (z 0) * conj (g (z 0))))
        hsmul
    refine h.congr ?_
    filter_upwards with z
    rfl
  convert hcomp using 1
  ext z
  have hdens :
      (ENNReal.ofReal (gaussianDensity 1 (e z))).toReal =
        (1 / Real.pi) * Real.exp (-‖z‖ ^ 2) := by
    have hnonneg' : 0 ≤ π⁻¹ * Real.exp (-‖z‖ ^ 2) := by
      positivity
    simpa [e, gaussianDensity] using (ENNReal.toReal_ofReal hnonneg')
  rw [hdens]
  simp [e, Algebra.smul_def, mul_assoc, mul_left_comm]

private theorem gaussianInner_oneDim_eq_weighted_coord
    (f g : ℂ → ℂ) :
    gaussianInner (d := 1) (fun z : CSpace 1 => f (z 0)) (fun z : CSpace 1 => g (z 0)) =
      ∫ z : ℂ,
        (((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) *
          (f z * conj (g z))
        ∂(volume : Measure ℂ) := by
  unfold gaussianInner
  rw [gaussianMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun z : CSpace 1 => ENNReal.ofReal (gaussianDensity 1 z)) by
      unfold gaussianDensity
      fun_prop)
    (show ∀ᵐ x : CSpace 1, ENNReal.ofReal (gaussianDensity 1 x) < ⊤ by
      filter_upwards with x
      simp)]
  let e : CSpace 1 ≃ᵐ ℂ := MeasurableEquiv.funUnique (Fin 1) ℂ
  have hEq :
      ∫ x : CSpace 1,
          (((1 / Real.pi) * Real.exp (-‖x 0‖ ^ 2) : ℝ) : ℂ) *
            (f (x 0) * conj (g (x 0)))
          ∂(volume : Measure (CSpace 1)) =
        ∫ z : ℂ,
          (((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) *
            (f z * conj (g z))
          ∂(volume : Measure ℂ) := by
    have hEq0 :=
      ((MeasureTheory.volume_preserving_funUnique (Fin 1) ℂ).integral_comp'
        (f := e)
        (fun z : ℂ =>
          (((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) *
            (f z * conj (g z))))
    convert hEq0 using 1
  calc
    ∫ z : CSpace 1,
        (ENNReal.ofReal (gaussianDensity 1 z)).toReal •
          (f (z 0) * conj (g (z 0)))
        ∂(volume : Measure (CSpace 1)) =
      ∫ z : CSpace 1,
        (((1 / Real.pi) * Real.exp (-‖z 0‖ ^ 2) : ℝ) : ℂ) *
          (f (z 0) * conj (g (z 0)))
        ∂(volume : Measure (CSpace 1)) := by
          apply integral_congr_ae
          filter_upwards with z
          have hnonneg : 0 ≤ π⁻¹ * Real.exp (-‖z 0‖ ^ 2) := by
            positivity
          have hdens :
              (ENNReal.ofReal (gaussianDensity 1 z)).toReal =
                (1 / Real.pi) * Real.exp (-‖z 0‖ ^ 2) := by
            simpa [gaussianDensity] using (ENNReal.toReal_ofReal hnonneg)
          rw [hdens]
          simp [Algebra.smul_def, mul_assoc, mul_left_comm]
    _ = ∫ z : ℂ,
        (((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) *
          (f z * conj (g z))
        ∂(volume : Measure ℂ) := hEq

private lemma density_prod_identity
    (d : ℕ) (F G : Fin d → ℂ → ℂ) (z : CSpace d) :
    (gaussianDensity d z : ℂ) *
        ((∏ q : Fin d, F q (z q)) * conj (∏ q : Fin d, G q (z q))) =
      ∏ q : Fin d,
        ((((1 / Real.pi) * Real.exp (-‖z q‖ ^ 2) : ℝ) : ℂ) *
          (F q (z q) * conj (G q (z q)))) := by
  rw [gaussianDensity_eq_prod]
  simp [gaussianDensity, Finset.prod_mul_distrib, mul_assoc, mul_left_comm]

/-- Tensor-product factorization over the Gaussian product measure. -/
theorem tensorGaussianFactorization
    (d : ℕ) (F G : Fin d → ℂ → ℂ)
    (hFG :
      ∀ q : Fin d,
        Integrable
            (fun z : CSpace 1 => F q (z 0) * conj (G q (z 0)))
            (gaussianMeasure 1)) :
    Integrable
        (fun z : CSpace d => ∏ q : Fin d, F q (z q) * conj (G q (z q)))
        (gaussianMeasure d) ∧
      gaussianInner (d := d) (fun z => ∏ q : Fin d, F q (z q)) (fun z => ∏ q : Fin d, G q (z q)) =
        ∏ q : Fin d,
          gaussianInner (d := 1) (fun z : CSpace 1 => F q (z 0)) (fun z : CSpace 1 => G q (z 0))
              := by
  have hcoord :
      ∀ q : Fin d,
        Integrable
          (fun z : ℂ =>
            (((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) *
              (F q z * conj (G q z)))
          (volume : Measure ℂ) := by
    intro q
    exact integrable_weighted_coord_of_integrable_gaussian (F q) (G q) (hFG q)
  have hprod_volume :
      Integrable
        (fun z : CSpace d =>
          ∏ q : Fin d,
            ((((1 / Real.pi) * Real.exp (-‖z q‖ ^ 2) : ℝ) : ℂ) *
              (F q (z q) * conj (G q (z q)))))
        (volume : Measure (CSpace d)) := by
    rw [MeasureTheory.volume_pi]
    exact MeasureTheory.Integrable.fintype_prod hcoord
  have hintegrable :
      Integrable
        (fun z : CSpace d => ∏ q : Fin d, F q (z q) * conj (G q (z q)))
        (gaussianMeasure d) := by
    rw [gaussianMeasure]
    rw [MeasureTheory.integrable_withDensity_iff_integrable_smul']
    · convert hprod_volume using 1
      funext z
      have hnonneg : 0 ≤ gaussianDensity d z := by
        unfold gaussianDensity
        positivity
      calc
        (((ENNReal.ofReal (gaussianDensity d z)).toReal : ℂ) *
            ∏ q : Fin d, F q (z q) * conj (G q (z q))) =
          (((ENNReal.ofReal (gaussianDensity d z)).toReal : ℂ) *
            ((∏ q : Fin d, F q (z q)) * conj (∏ q : Fin d, G q (z q)))) := by
              simp [Finset.prod_mul_distrib]
        _ = (gaussianDensity d z : ℂ) *
              ((∏ q : Fin d, F q (z q)) * conj (∏ q : Fin d, G q (z q))) := by
              rw [show (((ENNReal.ofReal (gaussianDensity d z)).toReal : ℂ)) =
                  gaussianDensity d z by
                simp [ENNReal.toReal_ofReal hnonneg]]
        _ = ∏ q : Fin d,
              ((((1 / Real.pi) * Real.exp (-‖z q‖ ^ 2) : ℝ) : ℂ) *
                (F q (z q) * conj (G q (z q)))) := density_prod_identity d F G z
    · unfold gaussianDensity
      fun_prop
    · filter_upwards with x
      simp
  constructor
  · exact hintegrable
  · unfold gaussianInner
    rw [gaussianMeasure]
    rw [integral_withDensity_eq_integral_toReal_smul
      (show Measurable (fun z : CSpace d => ENNReal.ofReal (gaussianDensity d z)) by
        unfold gaussianDensity
        fun_prop)
      (show ∀ᵐ x : CSpace d, ENNReal.ofReal (gaussianDensity d x) < ⊤ by
        filter_upwards with x
        simp)]
    calc
      ∫ z : CSpace d,
          (ENNReal.ofReal (gaussianDensity d z)).toReal •
            ((fun z => ∏ q : Fin d, F q (z q)) z *
              conj ((fun z => ∏ q : Fin d, G q (z q)) z))
          ∂(volume : Measure (CSpace d)) =
        ∫ z : CSpace d,
          (ENNReal.ofReal (gaussianDensity d z)).toReal •
            (∏ q : Fin d, F q (z q) * conj (G q (z q)))
          ∂(volume : Measure (CSpace d)) := by
            apply integral_congr_ae
            filter_upwards with z
            simp [Finset.prod_mul_distrib]
      _ =
        ∫ z : CSpace d,
          ∏ q : Fin d,
            ((((1 / Real.pi) * Real.exp (-‖z q‖ ^ 2) : ℝ) : ℂ) *
              (F q (z q) * conj (G q (z q))))
          ∂(volume : Measure (CSpace d)) := by
            apply integral_congr_ae
            filter_upwards with z
            have hnonneg : 0 ≤ gaussianDensity d z := by
              unfold gaussianDensity
              positivity
            calc
              (((ENNReal.ofReal (gaussianDensity d z)).toReal : ℂ) *
                  ∏ q : Fin d, F q (z q) * conj (G q (z q))) =
                (((ENNReal.ofReal (gaussianDensity d z)).toReal : ℂ) *
                  ((∏ q : Fin d, F q (z q)) * conj (∏ q : Fin d, G q (z q)))) := by
                    simp [Finset.prod_mul_distrib]
              _ = (gaussianDensity d z : ℂ) *
                    ((∏ q : Fin d, F q (z q)) * conj (∏ q : Fin d, G q (z q))) := by
                    rw [show (((ENNReal.ofReal (gaussianDensity d z)).toReal : ℂ)) =
                        gaussianDensity d z by
                      simp [ENNReal.toReal_ofReal hnonneg]]
              _ = ∏ q : Fin d,
                    ((((1 / Real.pi) * Real.exp (-‖z q‖ ^ 2) : ℝ) : ℂ) *
                      (F q (z q) * conj (G q (z q)))) := density_prod_identity d F G z
      _ =
        ∫ z : CSpace d,
          ∏ q : Fin d,
            ((((1 / Real.pi) * Real.exp (-‖z q‖ ^ 2) : ℝ) : ℂ) *
              (F q (z q) * conj (G q (z q))))
          ∂(volume : Measure (CSpace d)) := by
            rfl
      _ = ∫ z : CSpace d,
            ∏ q : Fin d,
              (fun q : Fin d => fun z : ℂ =>
                ((((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) *
                  (F q z * conj (G q z)))) q (z q)
            ∂(volume : Measure (CSpace d)) := by
              rfl
      _ = ∏ q : Fin d,
            ∫ z : ℂ,
              (((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) *
                (F q z * conj (G q z))
              ∂(volume : Measure ℂ) := by
              rw [MeasureTheory.volume_pi]
              exact
                MeasureTheory.integral_fintype_prod_eq_prod
                  (fun q : Fin d => fun z : ℂ =>
                    ((((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) *
                      (F q z * conj (G q z))))
      _ = ∏ q : Fin d,
            gaussianInner (d := 1) (fun z : CSpace 1 => F q (z 0))
              (fun z : CSpace 1 => G q (z 0)) := by
            apply Finset.prod_congr rfl
            intro q hq
            symm
            exact gaussianInner_oneDim_eq_weighted_coord (F q) (G q)

end Hermite1DimdLEAN
