/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderCoordinates
import LeanPool.NavierStokesAndEuler.Euler.Foundations.SobolevProducts
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.TransportDerivatives
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import LeanPool.NavierStokesAndEuler.Euler.Foundations.SobolevDerivativeNorm
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Actual derivative-word Sobolev norms on R³ × T and compact localizations. -/

@[expose] public section

noncomputable section

namespace EulerCylinderSobolev

open MeasureTheory EulerSobolev EulerSobolevProducts EulerSobolevDerivativeNorm
open EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
open EulerCylinderCoordinates
open scoped SchwartzMap ENNReal NNReal ContDiff Topology LineDeriv


/-- The four coordinate directions, with angle first and the spatial coordinates following. -/
noncomputable def standardDirection (i : Fin 4) : LiftTangent :=
  coordinateEquiv (EuclideanSpace.single i 1)

@[simp] theorem standardDirection_zero : standardDirection 0 = (0,1) := by
  apply Prod.ext
  · ext i
    simp [standardDirection]
  · simp [standardDirection]

@[simp] theorem standardDirection_succ (i : Fin 3) :
    standardDirection i.succ = (EuclideanSpace.single i 1, 0) := by
  apply Prod.ext
  · ext j
    simp [standardDirection]
  · simp [standardDirection]

variable (period : ℝ)

section Fields

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Ordered actual derivatives on the cylinder; the head is differentiated last. -/
noncomputable def iteratedFieldDerivative : {n : ℕ} → (Fin n → Fin 4) →
    (LiftDomain period → F) → LiftDomain period → F
  | 0, _, f => f
  | _n+1, w, f => fieldDerivative period (standardDirection (w 0))
      (iteratedFieldDerivative (Fin.tail w) f)

@[simp] theorem iteratedFieldDerivative_zero (w : Fin 0 → Fin 4) (f : LiftDomain period → F) :
    iteratedFieldDerivative period w f = f := rfl

@[simp] theorem iteratedFieldDerivative_succ {n : ℕ} (w : Fin (n + 1) → Fin 4)
    (f : LiftDomain period → F) :
    iteratedFieldDerivative period w f = fieldDerivative period (standardDirection (w 0))
      (iteratedFieldDerivative period (Fin.tail w) f) := rfl

/-- A concrete norm: the sum of L² norms of all ordered coordinate derivatives up to order `s`. -/
noncomputable def liftSobolevNorm (s : ℕ) (f : LiftDomain period → F)
    [Fact (0 < period)] : ℝ :=
  Finset.sum (Finset.range (s+1)) (fun n => ∑ w : Fin n → Fin 4,
    (eLpNorm (iteratedFieldDerivative period w f) 2 (liftMeasure period)).toReal)

theorem iteratedFieldDerivative_smooth {n : ℕ} (w : Fin n → Fin 4)
    (f : LiftDomain period → F) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (iteratedFieldDerivative period w f) x) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    exact fieldDerivative_smooth period _ _ (ih (Fin.tail w))

/-- The actual field lifted to Euclidean coordinates centered at a cylinder point. -/
noncomputable def euclideanLift (f : LiftDomain period → F) (x : LiftDomain period) : Domain 4 → F
    :=
  localFieldLift period f x ∘ coordinateEquiv

theorem euclideanLift_smooth (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    ContDiff ℝ ∞ (euclideanLift period f x) := (hf x).comp coordinateEquiv.contDiff

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem euclideanLift_zero (f : LiftDomain period → F) (x : LiftDomain period) :
    euclideanLift period f x 0 = f x := by
  change localFieldLift period f x (coordinateEquiv 0) = _
  rw [map_zero]
  simp [localFieldLift]

theorem euclideanLift_fieldDerivative (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (v z : Domain 4)
    (x : LiftDomain period) :
    euclideanLift period (fieldDerivative period (coordinateEquiv v) f) x z =
      fderiv ℝ (euclideanLift period f x) z v := by
  have hchain := ((hf x).differentiable (by simp) (coordinateEquiv z)).hasFDerivAt.comp z
    coordinateEquiv.hasFDerivAt
  rw [euclideanLift, localFieldLift_fieldDerivative]
  change fderiv ℝ (localFieldLift period f x) (coordinateEquiv z) (coordinateEquiv v) = _
  rw [show fderiv ℝ (euclideanLift period f x) z =
      (fderiv ℝ (localFieldLift period f x) (coordinateEquiv z)).comp
        coordinateEquiv.toContinuousLinearMap from hchain.fderiv]
  rfl

/-- The word derivative is exactly the corresponding coordinate entry of the Fréchet tensor. -/
theorem euclideanLift_iteratedFieldDerivative {n : ℕ} (w : Fin n → Fin 4)
    (f : LiftDomain period → F) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (x : LiftDomain period) (z : Domain 4) :
    euclideanLift period (iteratedFieldDerivative period w f) x z =
      iteratedFDeriv ℝ n (euclideanLift period f x) z
        (fun j => EuclideanSpace.single (w j) 1) := by
  induction n generalizing z with
  | zero => simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    rw [iteratedFieldDerivative_succ, standardDirection,
      euclideanLift_fieldDerivative _ _ (iteratedFieldDerivative_smooth period (Fin.tail w) f hf),
      iteratedFDeriv_succ_apply_left, ← fderiv_continuousMultilinear_apply_const_apply]
    · congr 2
      funext y
      exact ih (Fin.tail w) y
    · exact (euclideanLift_smooth period f hf x).differentiable_iteratedFDeriv
        (show (n : ℕ∞ω) < (∞ : ℕ∞ω) by exact_mod_cast ENat.natCast_lt_top n) z

/-- Tensor operator norms are controlled by the actual coordinate-word derivatives. -/
theorem euclideanLift_tensor_norm_le (n : ℕ) (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) (z : Domain 4) :
    ‖iteratedFDeriv ℝ n (euclideanLift period f x) z‖ ≤
      ∑ w : Fin n → Fin 4, ‖euclideanLift period (iteratedFieldDerivative period w f) x z‖ := by
  have h := multilinear_norm_le_coordinate_sum 4 n (iteratedFDeriv ℝ n (euclideanLift period f x) z)
  simpa only [euclideanLift_iteratedFieldDerivative period _ f hf] using h

/-- Sum of the norms of all coordinate words of one fixed order. -/
noncomputable def wordMagnitude (n : ℕ) (f : LiftDomain period → F) (x : LiftDomain period) : ℝ :=
  ∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative period w f x‖

theorem wordMagnitude_nonneg (n : ℕ) (f : LiftDomain period → F) (x : LiftDomain period) :
    0 ≤ wordMagnitude period n f x := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

/-- The sum of all coordinate derivative magnitudes through a given order. -/
noncomputable def totalMagnitude (s : ℕ) (f : LiftDomain period → F) (x : LiftDomain period) : ℝ :=
  Finset.sum (Finset.range (s+1)) (fun n => wordMagnitude period n f x)

theorem totalMagnitude_nonneg (s : ℕ) (f : LiftDomain period → F) (x : LiftDomain period) :
    0 ≤ totalMagnitude period s f x :=
  Finset.sum_nonneg (fun n _ => wordMagnitude_nonneg period n f x)

theorem wordMagnitude_le_total (s n : ℕ) (hn : n ≤ s) (f : LiftDomain period → F)
    (x : LiftDomain period) : wordMagnitude period n f x ≤ totalMagnitude period s f x :=
  Finset.single_le_sum (fun j _ => wordMagnitude_nonneg period j f x)
    (Finset.mem_range.2 (by omega))

end Fields

section Translations

variable [Fact (0 < period)]
variable {F : Type*} [NormedAddCommGroup F]

/-- Translation of an actual cylinder function. -/
noncomputable def translated (f : LiftDomain period → F) (x : LiftDomain period) :
    LiftDomain period → F := fun y => f (y + x)

theorem eLpNorm_translated (f : LiftDomain period → F)
    (hf : AEStronglyMeasurable f (liftMeasure period)) (x : LiftDomain period) :
    eLpNorm (translated period f x) 2 (liftMeasure period) = eLpNorm f 2 (liftMeasure period) :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_translation period x)

theorem memLp_translated (f : LiftDomain period → F)
    (hf : MemLp f 2 (liftMeasure period)) (x : LiftDomain period) :
    MemLp (translated period f x) 2 (liftMeasure period) :=
  hf.comp_measurePreserving (measurePreserving_translation period x)

variable [NormedSpace ℝ F]

omit [Fact (0 < period)] [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem euclideanLift_eq_translated_cover (f : LiftDomain period → F)
    (x : LiftDomain period) (z : Domain 4) :
    euclideanLift period f x z = translated period f x (euclideanCover period z) := by
  change f (x.1 + (coordinateEquiv z).1, x.2 + ((coordinateEquiv z).2 : AddCircle period)) =
    f ((coveringMap period (coordinateEquiv z)) + x)
  congr 1
  ext <;> simp [coveringMap, add_comm]

theorem wordMagnitude_memLp (n : ℕ) (f : LiftDomain period → F)
    (hf : ∀ w : Fin n → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) :
    MemLp (wordMagnitude period n f) 2 (liftMeasure period) :=
  memLp_finsetSum _ (fun w _ => (hf w).norm)

theorem eLpNorm_wordMagnitude_le (n : ℕ) (f : LiftDomain period → F)
    (hf : ∀ w : Fin n → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) :
    eLpNorm (wordMagnitude period n f) 2 (liftMeasure period) ≤
      ∑ w : Fin n → Fin 4, eLpNorm (iteratedFieldDerivative period w f) 2 (liftMeasure period) := by
  have he : wordMagnitude period n f = ∑ w : Fin n → Fin 4,
      (fun x => ‖iteratedFieldDerivative period w f x‖) := by
    funext x
    simp [wordMagnitude]
  rw [he]
  simpa only [eLpNorm_norm] using eLpNorm_sum_le
    (fun w (_ : w ∈ (Finset.univ : Finset (Fin n → Fin 4))) => (hf w).1.norm)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)

theorem totalMagnitude_memLp (s : ℕ) (f : LiftDomain period → F)
    (hf : ∀ n ≤ s, ∀ w : Fin n → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) :
    MemLp (totalMagnitude period s f) 2 (liftMeasure period) :=
  memLp_finsetSum _ (fun n hn => wordMagnitude_memLp period n f (hf n (by
      simpa using Finset.mem_range.1 hn)))

theorem totalMagnitude_L2_le (s : ℕ) (f : LiftDomain period → F)
    (hf : ∀ n ≤ s, ∀ w : Fin n → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) :
    ‖(totalMagnitude_memLp period s f hf).toLp (totalMagnitude period s f)‖ ≤
      liftSobolevNorm period s f := by
  have he : totalMagnitude period s f = ∑ n ∈ Finset.range (s+1), wordMagnitude period n f := by
    funext x
    simp [totalMagnitude]
  have hA : eLpNorm (totalMagnitude period s f) 2 (liftMeasure period) ≤
      ∑ n ∈ Finset.range (s+1), eLpNorm (wordMagnitude period n f) 2 (liftMeasure period) := by
    rw [he]
    exact eLpNorm_sum_le (fun n hn =>
      (wordMagnitude_memLp period n f (hf n (by
          simpa using Finset.mem_range.1 hn))).1) (by norm_num)
  have hB : (∑ n ∈ Finset.range (s+1), eLpNorm (wordMagnitude period n f) 2 (liftMeasure period)) ≤
      ∑ n ∈ Finset.range (s+1), ∑ w : Fin n → Fin 4,
        eLpNorm (iteratedFieldDerivative period w f) 2 (liftMeasure period) := by
    exact Finset.sum_le_sum (fun n hn => eLpNorm_wordMagnitude_le period n f
      (hf n (by simpa using Finset.mem_range.1 hn)))
  have hfin (n : ℕ) (hn : n ∈ Finset.range (s+1)) :
      (∑ w : Fin n → Fin 4, eLpNorm (iteratedFieldDerivative period w f) 2 (liftMeasure period)) ≠
          ⊤ :=
    ENNReal.sum_ne_top.2 (fun w _ => (hf n (by simpa using Finset.mem_range.1 hn) w).eLpNorm_ne_top)
  have hreal := ENNReal.toReal_mono (ENNReal.sum_ne_top.2 hfin) (hA.trans hB)
  rw [Lp.norm_toLp]
  convert hreal using 1
  rw [ENNReal.toReal_sum hfin]
  apply Finset.sum_congr rfl
  intro n hn
  exact (ENNReal.toReal_sum (fun w _ =>
    (hf n (by simpa using Finset.mem_range.1 hn) w).eLpNorm_ne_top)).symm

end Translations

variable [Fact (0 < period)]

/-- A fixed compact smooth localizer, supported in the chart neighborhood and equal to one at zero.
-/
noncomputable def localBump : ContDiffBump (0 : Domain 4) where
  rIn := period
  rOut := 2 * period
  rIn_pos := Fact.out
  rIn_lt_rOut := by have h : 0 < period := Fact.out; linarith

theorem localBump_smooth : ContDiff ℝ ∞ (localBump period) := (localBump period).contDiff

theorem localBump_zero : localBump period 0 = 1 :=
  (localBump period).one_of_mem_closedBall
    (by simpa [localBump] using (show 0 ≤ period from (Fact.out : 0 < period).le))

theorem localBump_support : tsupport (localBump period) ⊆ ({z : EulerSobolev.Domain 4 | |z 0| ≤ 2 *
    period}) := by
  rw [(localBump period).tsupport_eq]
  intro z hz
  have hnorm : ‖z‖ ≤ 2 * period := by simpa [localBump] using hz
  exact (PiLp.norm_apply_le z 0).trans hnorm

/-- The local bump regarded as a real Schwartz function. -/
noncomputable def bumpSchwartz : 𝓢(Domain 4, ℝ) :=
  (localBump period).hasCompactSupport.toSchwartzMap (localBump_smooth period)

/-- A finite, explicitly defined bound for each derivative of the fixed local bump. -/
noncomputable def bumpBound (j : ℕ) : NNReal :=
  ⟨SchwartzMap.seminorm ℝ 0 j (bumpSchwartz period), apply_nonneg _ _⟩

theorem localBump_derivative_bound (j : ℕ) (z : Domain 4) :
    ‖iteratedFDeriv ℝ j (localBump period) z‖ ≤ bumpBound period j :=
  SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ (bumpSchwartz period) j z

/-- Finite Leibniz coefficient controlling localization at derivative order `n`. -/
noncomputable def bumpCoefficient (n : ℕ) : NNReal :=
  Finset.sum (Finset.range (n+1)) (fun j => (n.choose j : ℝ≥0) * bumpBound period j)

/-- An actual compactly supported localization of an arbitrary smooth cylinder field. -/
noncomputable def localized (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) : 𝓢(Domain 4, ℂ) :=
  ((localBump period).hasCompactSupport.smul_right (f' := euclideanLift period f x)).toSchwartzMap
    ((localBump_smooth period).smul (euclideanLift_smooth period f hf x))

@[simp] theorem localized_apply (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) (z : Domain 4) :
    localized period f hf x z = localBump period z • euclideanLift period f x z := rfl

theorem localized_zero (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    localized period f hf x 0 = f x := by
  rw [localized_apply, localBump_zero, one_smul, euclideanLift_zero]

theorem localized_tsupport (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    tsupport (localized period f hf x) ⊆ ({z : EulerSobolev.Domain 4 | |z 0| ≤ 2 * period}) :=
  (tsupport_smul_subset_left (localBump period) (euclideanLift period f x)).trans
    (localBump_support period)

/-- The actual Leibniz rule controls every localized derivative by cylinder derivative words. -/
theorem localized_tensor_norm_le (n : ℕ) (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) (z : Domain 4) :
    ‖iteratedFDeriv ℝ n (localized period f hf x) z‖ ≤
      bumpCoefficient period n * translated period (totalMagnitude period n f) x
        (euclideanCover period z) := by
  have hA := norm_iteratedFDeriv_smul_le (localBump_smooth period)
    (euclideanLift_smooth period f hf x) z (by simp : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  apply hA.trans
  change (∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) *
    ‖iteratedFDeriv ℝ j (localBump period) z‖ *
      ‖iteratedFDeriv ℝ (n-j) (euclideanLift period f x) z‖) ≤ _
  have hB (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      ‖iteratedFDeriv ℝ (n-j) (euclideanLift period f x) z‖ ≤
        translated period (totalMagnitude period n f) x (euclideanCover period z) := by
    have hT := euclideanLift_tensor_norm_le period (n-j) f hf x z
    simp only [euclideanLift_eq_translated_cover, translated] at hT
    exact hT.trans (wordMagnitude_le_total period n (n-j) (by omega) f _)
  calc
    _ ≤ ∑ j ∈ Finset.range (n+1), ((n.choose j : ℝ) * bumpBound period j) *
        translated period (totalMagnitude period n f) x (euclideanCover period z) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (localBump_derivative_bound period j z) (Nat.cast_nonneg _))
        (hB j hj) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (bumpBound period j).coe_nonneg)
    _ = _ := by simp only [bumpCoefficient, NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_natCast,
      Finset.sum_mul]

/-- Each pure directional derivative of the localization has the same chart support. -/
theorem directional_localized_support (n : ℕ) (i : Fin 4) (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    Function.support (directional 4 n (EuclideanSpace.single i 1) (localized period f hf x)) ⊆
      ({z : EulerSobolev.Domain 4 | |z 0| ≤ 2 * period}) := by
  have he : (directional 4 n (EuclideanSpace.single i 1) (localized period f hf x) :
      Domain 4 → ℂ) = (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Domain 4) ℂ =>
        T (fun _ => EuclideanSpace.single i 1)) ∘ iteratedFDeriv ℝ n (localized period f hf x) := by
    funext z
    exact SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
  rw [he]
  exact subset_closure.trans ((tsupport_comp_subset (by simp) _).trans
    ((tsupport_iteratedFDeriv_subset n).trans (localized_tsupport period f hf x)))

/-- Every localized pure derivative is controlled by the actual cylinder derivative L² sum. -/
theorem localized_directional_L2_le (n : ℕ) (i : Fin 4) (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ n, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖(directional 4 n (EuclideanSpace.single i 1) (localized period f hf x)).toLp 2‖ ≤
      (bumpCoefficient period n : ℝ) * (6 : ℝ) ^ (1/2 : ℝ) * liftSobolevNorm period n f := by
  let q := totalMagnitude period n f
  have hq : MemLp q 2 (liftMeasure period) := totalMagnitude_memLp period n f hfL2
  have hqt := memLp_translated period q hq x
  have hb (z : Domain 4) :
      ‖directional 4 n (EuclideanSpace.single i 1) (localized period f hf x) z‖ ≤
        (bumpCoefficient period n : ℝ) * ‖translated period q x (euclideanCover period z)‖ := by
    rw [directional, SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
    have hA := (iteratedFDeriv ℝ n (localized period f hf x) z).le_opNorm
      (fun _ : Fin n => EuclideanSpace.single i (1 : ℝ))
    simp only [PiLp.norm_single, norm_one, Finset.prod_const_one, mul_one] at hA
    have hB := localized_tensor_norm_le period n f hf x z
    change _ ≤ (bumpCoefficient period n : ℝ) * ‖totalMagnitude period n f (_ + x)‖
    rw [Real.norm_of_nonneg (totalMagnitude_nonneg period n f _)]
    exact hA.trans hB
  have hA := localized_L2_le period (translated period q x) hqt
    (directional 4 n (EuclideanSpace.single i 1) (localized period f hf x))
    (directional_localized_support period n i f hf x) (bumpCoefficient period n) hb
  have hnorm : ‖hqt.toLp (translated period q x)‖ = ‖hq.toLp q‖ := by
    simp only [Lp.norm_toLp, eLpNorm_translated period q hq.1]
  rw [hnorm] at hA
  exact hA.trans (mul_le_mul_of_nonneg_left (totalMagnitude_L2_le period n f hfL2)
    (mul_nonneg (bumpCoefficient period n).coe_nonneg (Real.rpow_nonneg (by norm_num) _)))

theorem liftSobolevNorm_nonneg {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : ℕ) (f : LiftDomain period → F) : 0 ≤ liftSobolevNorm period s f :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg))

theorem liftSobolevNorm_mono {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s t : ℕ} (hst : s ≤ t) (f : LiftDomain period → F) :
    liftSobolevNorm period s f ≤ liftSobolevNorm period t f := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
  intro n _ _
  exact Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)

/-- A concrete finite embedding constant depending only on the circle period. -/
noncomputable def cylinderEmbeddingConstant : ℝ :=
  embeddingConstant 4 3 (by norm_num) * 25 * (6 : ℝ) ^ (1/2 : ℝ) *
    ((bumpCoefficient period 0 : ℝ) + (2 * Real.pi) ^ (-3 : ℤ) * 4 * bumpCoefficient period 3)

theorem cylinderEmbeddingConstant_nonneg : 0 ≤ cylinderEmbeddingConstant period := by
  unfold cylinderEmbeddingConstant
  have hc : 0 ≤ embeddingConstant 4 3 (by norm_num) := norm_nonneg _
  positivity

/-- Genuine H³ to L∞ embedding on R³ × T for arbitrary smooth fields with square-integrable
derivatives. -/
theorem cylinder_pointwise_le_H3 (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ 3, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖f x‖ ≤ cylinderEmbeddingConstant period * liftSobolevNorm period 3 f := by
  have hbase := localized_directional_L2_le period 0 0 f hf
    (fun j hj => hfL2 j (by omega)) x
  have he : directional 4 0 (EuclideanSpace.single 0 1) (localized period f hf x) =
      localized period f hf x := by ext z; simp [directional]
  rw [he] at hbase
  have hbase' := hbase.trans (mul_le_mul_of_nonneg_left
    (liftSobolevNorm_mono period (show 0 ≤ 3 by omega) f)
    (mul_nonneg (bumpCoefficient period 0).coe_nonneg (Real.rpow_nonneg (by norm_num) _)))
  have hthird : (∑ i : Fin 4,
      ‖(directional 4 3 (EuclideanSpace.single i 1) (localized period f hf x)).toLp 2‖) ≤
        4 * ((bumpCoefficient period 3 : ℝ) * (6 : ℝ) ^ (1/2 : ℝ) * liftSobolevNorm period 3 f) :=
            by
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) =>
      localized_directional_L2_le period 3 i f hf hfL2 x)
  have hA := pointwise_le_L2_third_derivatives (localized period f hf x) 0
  rw [localized_zero] at hA
  have hB := add_le_add hbase' (mul_le_mul_of_nonneg_left hthird
    (zpow_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi) (-3 : ℤ)))
  have hC := mul_le_mul_of_nonneg_left hB
    (mul_nonneg (show 0 ≤ embeddingConstant 4 3 (by
        norm_num) from norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 25))
  refine hA.trans (hC.trans_eq ?_)
  unfold cylinderEmbeddingConstant
  ring

section WordComposition
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [Fact (0 < period)] in
/-- Composing two actual derivative words gives a word of the combined length. -/
theorem iteratedFieldDerivative_comp_exists {m n : ℕ} (v : Fin n → Fin 4)
    (w : Fin m → Fin 4) (f : LiftDomain period → F) :
    ∃ u : Fin (m+n) → Fin 4, iteratedFieldDerivative period v
      (iteratedFieldDerivative period w f) = iteratedFieldDerivative period u f := by
  induction n with
  | zero => exact ⟨w, rfl⟩
  | succ n ih =>
    obtain ⟨u, hu⟩ := ih (Fin.tail v)
    refine ⟨Fin.cons (v 0) u, ?_⟩
    simp only [iteratedFieldDerivative_succ, Fin.cons_zero, Fin.tail_cons, hu]

theorem word_L2_le_liftSobolevNorm {s n : ℕ} (hn : n ≤ s) (w : Fin n → Fin 4)
    (f : LiftDomain period → F) :
    (eLpNorm (iteratedFieldDerivative period w f) 2 (liftMeasure period)).toReal ≤
      liftSobolevNorm period s f := by
  have hA : (eLpNorm (iteratedFieldDerivative period w f) 2 (liftMeasure period)).toReal ≤
      ∑ v : Fin n → Fin 4, (eLpNorm (iteratedFieldDerivative period v f) 2 (liftMeasure
          period)).toReal :=
    Finset.single_le_sum (f := fun v : Fin n → Fin 4 =>
      (eLpNorm (iteratedFieldDerivative period v f) 2 (liftMeasure period)).toReal)
      (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ w)
  have hB : (∑ v : Fin n → Fin 4,
      (eLpNorm (iteratedFieldDerivative period v f) 2 (liftMeasure period)).toReal) ≤
        liftSobolevNorm period s f :=
    Finset.single_le_sum (s := Finset.range (s+1)) (a := n)
      (f := fun j => ∑ v : Fin j → Fin 4,
        (eLpNorm (iteratedFieldDerivative period v f) 2 (liftMeasure period)).toReal)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg))
      (Finset.mem_range.2 (by omega))
  exact hA.trans hB

theorem word_memLp {s m n : ℕ} (h : m + n ≤ s) (v : Fin n → Fin 4) (w : Fin m → Fin 4)
    (f : LiftDomain period → F)
    (hfL2 : ∀ j ≤ s, ∀ u : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period u f) 2 (liftMeasure period)) :
    MemLp (iteratedFieldDerivative period v (iteratedFieldDerivative period w f)) 2
      (liftMeasure period) := by
  obtain ⟨u, hu⟩ := iteratedFieldDerivative_comp_exists period v w f
  rw [hu]
  exact hfL2 (m+n) h u

theorem word_H3_le_H6 {m : ℕ} (hm : m ≤ 3) (w : Fin m → Fin 4)
    (f : LiftDomain period → F) :
    liftSobolevNorm period 3 (iteratedFieldDerivative period w f) ≤
      85 * liftSobolevNorm period 6 f := by
  have hA : (∑ n ∈ Finset.range (3+1), ∑ v : Fin n → Fin 4,
      (eLpNorm (iteratedFieldDerivative period v (iteratedFieldDerivative period w f)) 2
        (liftMeasure period)).toReal) ≤
      ∑ n ∈ Finset.range (3+1), ∑ _v : Fin n → Fin 4, liftSobolevNorm period 6 f := by
    apply Finset.sum_le_sum
    intro n hn
    apply Finset.sum_le_sum
    intro v _
    obtain ⟨u, hu⟩ := iteratedFieldDerivative_comp_exists period v w f
    rw [hu]
    exact word_L2_le_liftSobolevNorm period (by have := Finset.mem_range.1 hn; omega) u f
  apply hA.trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  norm_num [Finset.sum_range_succ]
  ring

end WordComposition

/-- Uniform control of any derivative word of order at most three by the H⁶ norm. -/
theorem cylinder_word_pointwise_le_H6 {m : ℕ} (hm : m ≤ 3) (w : Fin m → Fin 4)
    (f : LiftDomain period → ℂ) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ 6, ∀ u : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period u f) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖iteratedFieldDerivative period w f x‖ ≤
      cylinderEmbeddingConstant period * (85 * liftSobolevNorm period 6 f) := by
  have hA := cylinder_pointwise_le_H3 period (iteratedFieldDerivative period w f)
    (iteratedFieldDerivative_smooth period w f hf)
    (fun j hj v => word_memLp period (by omega : m+j ≤ 6) v w f hfL2) x
  exact hA.trans (mul_le_mul_of_nonneg_left (word_H3_le_H6 period hm w f)
    (cylinderEmbeddingConstant_nonneg period))

end EulerCylinderSobolev
