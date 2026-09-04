/-
Copyright (c) 2024 Sidharth Hariharan and 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Sidharth Hariharan, Gareth Ma, Dean Cureton
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Meromorphic.Complex
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.UniformSpace.Uniformizable
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Foundations

Foundational test functions and the first saddle-point estimates.
-/

namespace CohnElkies


section

open Filter MeasureTheory
open scoped FourierTransform SchwartzMap Topology

/-- The Euclidean space used in ambient dimension `d`. -/
public
noncomputable abbrev Euclidean (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Complex Schwartz test functions in ambient dimension `d`. -/
public
noncomputable abbrev TestFunction (d : ℕ) := 𝓢(Euclidean d, ℂ)

private noncomputable def IsRealValued {d : ℕ} (f : TestFunction d) : Prop :=
  ∀ x : Euclidean d, (f x).im = 0

private noncomputable def IsRadial {d : ℕ} (f : TestFunction d) : Prop :=
  ∀ x y : Euclidean d, ‖x‖ = ‖y‖ → f x = f y

private structure Admissible (d : ℕ) where
  function : TestFunction d
  real : IsRealValued function
  radial : IsRadial function
  fourier_real : IsRealValued (𝓕 function)
  fourier_nonneg : ∀ ξ : Euclidean d, 0 ≤ ((𝓕 function) ξ).re
  fourier_zero_pos : 0 < ((𝓕 function) (0 : Euclidean d)).re
  outside_nonpos :
    ∀ x : Euclidean d, 1 ≤ ‖x‖ → (function x).re ≤ 0

/-- The analytic formula for the volume of the unit ball in dimension `d`. -/
public
noncomputable def unitBallVolume (d : ℕ) : ℝ :=
  Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1)

private theorem unitBallVolume_pos (d : ℕ) : 0 < unitBallVolume d := by
  unfold unitBallVolume
  exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _)
    (Real.Gamma_pos_of_pos (by positivity))

private noncomputable def quotient {d : ℕ} (f : Admissible d) : ℝ :=
  (f.function (0 : Euclidean d)).re /
    ((𝓕 f.function) (0 : Euclidean d)).re

private noncomputable def quotientSet (d : ℕ) : Set ℝ :=
  Set.range (quotient (d := d))

private noncomputable def linearProgram (d : ℕ) : ℝ :=
  unitBallVolume d / (2 : ℝ) ^ d * sInf (quotientSet d)

private theorem geometricFactor_pos (d : ℕ) :
    0 < unitBallVolume d / (2 : ℝ) ^ d := by
  exact div_pos (unitBallVolume_pos d) (by positivity)

private noncomputable def normalizedCost {d : ℕ} (f : Admissible d) : ℝ :=
  quotient f ^ ((d : ℝ)⁻¹) / Real.sqrt (d : ℝ)

private noncomputable def normalizedProgram (d : ℕ) : ℝ :=
  sInf (Set.range (normalizedCost (d := d)))

private noncomputable def criticalPackingBase : ℝ :=
  Real.sqrt (Real.exp 1 / (2 * Real.pi))

private noncomputable def criticalBinaryExponent : ℝ :=
  (1 / 2 : ℝ) * Real.logb 2 (2 * Real.pi / Real.exp 1)

private theorem criticalPackingBase_pos : 0 < criticalPackingBase := by
  unfold criticalPackingBase
  positivity

private noncomputable def SharpQuotientAsymptotic : Prop :=
  Tendsto normalizedProgram atTop (nhds Real.pi⁻¹)

private noncomputable def SharpLogAsymptotic : Prop :=
  Tendsto (fun d : ℕ => Real.log (linearProgram d) / (d : ℝ))
    atTop (nhds ((1 / 2 : ℝ) * Real.log (Real.exp 1 / (2 * Real.pi))))

private noncomputable def SharpPackingRootAsymptotic : Prop :=
  Tendsto (fun d : ℕ => (linearProgram d) ^ ((d : ℝ)⁻¹))
    atTop (nhds criticalPackingBase)

end

section

private noncomputable def shellWeight (ε : ℝ) : ℝ :=
  Real.exp (-(3 : ℝ) * ε * (ε⁻¹ ^ 3) / 8)

private noncomputable def plusPolynomial (ε : ℝ) (z : ℂ) : ℂ :=
  1 + z ^ 2 + ((ε / 4 : ℝ) : ℂ) + Complex.I * z * (1 + z ^ 2)

private noncomputable def minusPolynomial (ε : ℝ) (z : ℂ) : ℂ :=
  1 + z ^ 2 + ((ε / 4 : ℝ) : ℂ) - Complex.I * z * (1 + z ^ 2)

private theorem shellWeight_pos (ε : ℝ) : 0 < shellWeight ε := by
  exact Real.exp_pos _

private theorem plusPolynomial_imaginary (ε u : ℝ) :
    plusPolynomial ε (Complex.I * (u : ℂ)) =
      (((ε / 4) + (1 - u) ^ 2 * (1 + u) : ℝ) : ℂ) := by
  push_cast
  try dsimp [plusPolynomial]
  ring_nf
  simp only [Complex.I_sq, neg_mul, one_mul, Complex.I_pow_four]; push_cast; ring

private theorem minusPolynomial_imaginary (ε u : ℝ) :
    minusPolynomial ε (Complex.I * (u : ℂ)) =
      (((ε / 4) + (1 - u) * (1 + u) ^ 2 : ℝ) : ℂ) := by
  push_cast
  try dsimp [minusPolynomial]
  ring_nf
  simp only [Complex.I_sq, neg_mul, one_mul, sub_neg_eq_add, Complex.I_pow_four]; push_cast; ring

private theorem plusPolynomial_imaginary_re_pos {ε u : ℝ}
    (hε : 0 < ε) (hu : -1 < u) :
    0 < (plusPolynomial ε (Complex.I * (u : ℂ))).re := by
  have hs : 0 ≤ (1 - u) ^ 2 * (1 + u) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  rw [plusPolynomial_imaginary, Complex.ofReal_re]
  exact add_pos_of_pos_of_nonneg (div_pos hε four_pos) hs

private theorem minusPolynomial_imaginary_re_neg {ε u : ℝ}
    (hε : 0 < ε) (hu : 1 + ε / 4 ≤ u) :
    (minusPolynomial ε (Complex.I * (u : ℂ))).re < 0 := by
  rw [minusPolynomial_imaginary, Complex.ofReal_re]
  have huone : 1 ≤ u := by linarith
  have hs : (4 : ℝ) ≤ (1 + u) ^ 2 := by
    linarith [sq_nonneg (u - 1)]
  have ht : ε / 4 ≤ u - 1 := by linarith
  have hproduct : ε ≤ (u - 1) * (1 + u) ^ 2 := by
    calc
      ε = (ε / 4) * 4 := by ring
      _ ≤ (u - 1) * (1 + u) ^ 2 :=
        mul_le_mul ht hs (by norm_num) (by linarith)
  linarith

end

section

open MeasureTheory
open scoped FourierTransform

private noncomputable def mellinFrequency (ℓ : ℝ) (profile : ℝ → ℂ) (t : ℝ) : ℂ :=
  mellin profile ((ℓ : ℂ) - Complex.I * (t : ℂ))

private theorem mellinFrequency_eq_fourier
    (ℓ : ℝ) (profile : ℝ → ℂ) (t : ℝ) :
    mellinFrequency ℓ profile t =
      (𝓕 (fun u : ℝ =>
        Real.exp (-ℓ * u) • profile (Real.exp (-u))))
          (-t / (2 * Real.pi)) := by
  unfold mellinFrequency
  simpa only [neg_mul, Complex.real_smul, Complex.ofReal_exp, Complex.ofReal_neg,
    Complex.ofReal_mul,
    Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im,
      Complex.ofReal_im,
    mul_zero, sub_self, sub_zero, Complex.sub_im, Complex.mul_im, one_mul, zero_add,
      zero_sub] using!
    (mellin_eq_fourier profile
      (s := (ℓ : ℂ) - Complex.I * (t : ℂ)))

private noncomputable def mellinMultiplier (ℓ t : ℝ) : ℂ :=
  Complex.exp
      (Complex.I * (t : ℂ) * (Real.log Real.pi : ℂ)) *
    Complex.Gamma (((ℓ : ℂ) - Complex.I * (t : ℂ)) / 2) /
    Complex.Gamma (((ℓ : ℂ) + Complex.I * (t : ℂ)) / 2)

private theorem mellinDenominator_re_pos {ℓ : ℝ} (hℓ : 0 < ℓ) (t : ℝ) :
    0 < (((ℓ : ℂ) + Complex.I * (t : ℂ)) / 2).re := by
  simpa only [Complex.div_ofNat_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, zero_mul,
    Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero, Nat.ofNat_pos,
      div_pos_iff_of_pos_right] using! (half_pos hℓ)

private theorem mellinMultiplier_denominator_ne_zero
    {ℓ : ℝ} (hℓ : 0 < ℓ) (t : ℝ) :
    Complex.Gamma (((ℓ : ℂ) + Complex.I * (t : ℂ)) / 2) ≠ 0 :=
  Complex.Gamma_ne_zero_of_re_pos (mellinDenominator_re_pos hℓ t)

private theorem gamma_add_nat_eq_product (z : ℂ)
    (hz : ∀ j : ℕ, z + (j : ℂ) ≠ 0) (k : ℕ) :
    Complex.Gamma (z + (k : ℂ)) =
      Complex.Gamma z * ∏ j ∈ Finset.range k, (z + (j : ℂ)) := by
  induction k with
  | zero => simp only [CharP.cast_eq_zero, add_zero, Finset.range_zero, Finset.prod_empty, mul_one]
  | succ k ih =>
    rw [Nat.cast_succ, ← add_assoc,
      Complex.Gamma_add_one (z + (k : ℂ)) (hz k), ih,
      Finset.prod_range_succ]
    ring

private theorem integer_gamma_product (k : ℕ) {y : ℝ} (hy : y ≠ 0) :
    Complex.Gamma ((k : ℂ) + Complex.I * (y : ℂ) / 2) =
      Complex.Gamma (Complex.I * (y : ℂ) / 2) *
        ∏ j ∈ Finset.range k,
          ((j : ℂ) + Complex.I * (y : ℂ) / 2) := by
  let z : ℂ := Complex.I * (y : ℂ) / 2
  have hz : ∀ j : ℕ, z + (j : ℂ) ≠ 0 := by
    intro j hj
    have him := congrArg Complex.im hj
    try dsimp [z] at him
    norm_num at him
    exact hy (by linarith)
  simpa only [add_comm] using! gamma_add_nat_eq_product z hz k

private theorem half_integer_gamma_product (k : ℕ) (y : ℝ) :
    Complex.Gamma
        ((k : ℂ) + (1 / 2 : ℂ) + Complex.I * (y : ℂ) / 2) =
      Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (y : ℂ) / 2) *
        ∏ j ∈ Finset.range k,
          ((j : ℂ) + (1 / 2 : ℂ) + Complex.I * (y : ℂ) / 2) := by
  let z : ℂ := (1 / 2 : ℂ) + Complex.I * (y : ℂ) / 2
  have hz : ∀ j : ℕ, z + (j : ℂ) ≠ 0 := by
    intro j hj
    have hre := congrArg Complex.re hj
    try dsimp [z] at hre
    norm_num at hre
    have hjnonneg : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  simpa [z, add_comm, add_left_comm, add_assoc] using!
    gamma_add_nat_eq_product z hz k

end

section

open Filter MeasureTheory
open scoped FourierTransform SchwartzMap

private noncomputable def IsEven {d : ℕ} (f : TestFunction d) : Prop :=
  ∀ x : Euclidean d, f (-x) = f x

private theorem IsRadial.even {d : ℕ} {f : TestFunction d}
    (hf : IsRadial f) : IsEven f := by
  intro x
  exact hf (-x) x (by simp only [norm_neg])

private theorem fourierInv_apply_zero {d : ℕ} (f : TestFunction d) :
    (𝓕⁻ f : TestFunction d) (0 : Euclidean d) =
      ∫ x : Euclidean d, f x := by
  calc
    (𝓕⁻ f : TestFunction d) (0 : Euclidean d) =
        (𝓕⁻ (f : Euclidean d → ℂ)) (0 : Euclidean d) :=
      congrFun (SchwartzMap.fourierInv_coe f) 0
    _ = ∫ x : Euclidean d, f x := by
      rw [Real.fourierInv_eq]
      simp only [inner_zero_right, AddChar.map_zero_eq_one, one_smul]

private theorem admissible_zero_pos {d : ℕ} (f : Admissible d) :
    0 < (f.function (0 : Euclidean d)).re := by
  have hpositive : 0 < ∫ x : Euclidean d, ((𝓕 f.function) x).re := by
    exact integral_pos_of_integrable_nonneg_nonzero
      (Complex.continuous_re.comp (𝓕 f.function).continuous)
      (𝓕 f.function).integrable.re
      f.fourier_nonneg f.fourier_zero_pos.ne'
  have hinversion :
      (∫ x : Euclidean d, (𝓕 f.function) x) =
        f.function (0 : Euclidean d) := by
    have h := congrArg (fun g : TestFunction d => g (0 : Euclidean d))
      (show (𝓕⁻ (𝓕 f.function) : TestFunction d) = f.function from
        FourierTransform.fourierInv_fourier_eq f.function)
    simpa only [fourierInv_apply_zero] using! h
  calc
    (0 : ℝ) < (∫ x : Euclidean d, ((𝓕 f.function) x).re) := hpositive
    _ = (∫ x : Euclidean d, (𝓕 f.function) x).re :=
      integral_re (𝓕 f.function).integrable
    _ = (f.function (0 : Euclidean d)).re :=
      congrArg Complex.re hinversion

private theorem quotient_pos {d : ℕ} (f : Admissible d) : 0 < quotient f := by
  exact div_pos (admissible_zero_pos f) f.fourier_zero_pos

private theorem quotientSet_bddBelow (d : ℕ) : BddBelow (quotientSet d) := by
  refine ⟨0, ?_⟩
  rintro y ⟨f, rfl⟩
  exact (quotient_pos f).le

private theorem normalizedCost_nonneg {d : ℕ} (f : Admissible d) :
    0 ≤ normalizedCost f := by
  exact div_nonneg (Real.rpow_nonneg (quotient_pos f).le _)
    (Real.sqrt_nonneg _)

private theorem normalizedCostSet_bddBelow (d : ℕ) :
    BddBelow (Set.range (normalizedCost (d := d))) := by
  refine ⟨0, ?_⟩
  rintro y ⟨f, rfl⟩
  exact normalizedCost_nonneg f

private theorem fourier_sq_apply {d : ℕ} (f : TestFunction d) (x : Euclidean d) :
    ((𝓕 (𝓕 f) : TestFunction d) x) = f (-x) := by
  have hinv := congrArg (fun g : TestFunction d => g (-x))
    (show (𝓕⁻ (𝓕 f) : TestFunction d) = f from
      FourierTransform.fourierInv_fourier_eq f)
  have hchange :
      ((𝓕⁻ (𝓕 f) : TestFunction d) (-x)) =
        ((𝓕 (𝓕 f) : TestFunction d) x) := by
    calc
      ((𝓕⁻ (𝓕 f) : TestFunction d) (-x)) =
          (𝓕⁻ ((𝓕 f : TestFunction d) : Euclidean d → ℂ)) (-x) :=
        congrFun (SchwartzMap.fourierInv_coe (𝓕 f)) (-x)
      _ = (𝓕 ((𝓕 f : TestFunction d) : Euclidean d → ℂ)) x := by
        rw [Real.fourierInv_eq_fourier_neg]
        simp only [neg_neg]
      _ = ((𝓕 (𝓕 f) : TestFunction d) x) :=
        (congrFun (SchwartzMap.fourier_coe (𝓕 f)) x).symm
  exact hchange ▸ hinv

private theorem fourier_sq_of_radial {d : ℕ} (f : TestFunction d)
    (hf : IsRadial f) : (𝓕 (𝓕 f) : TestFunction d) = f := by
  ext x
  rw [fourier_sq_apply]
  exact hf.even x

private noncomputable def antiFourierPart {d : ℕ} (f : TestFunction d) : TestFunction d :=
  𝓕 f - f

private theorem fourier_antiFourierPart {d : ℕ} (f : TestFunction d)
    (hf : IsRadial f) :
    (𝓕 (antiFourierPart f) : TestFunction d) = -antiFourierPart f := by
  rw [antiFourierPart, sub_eq_add_neg, FourierTransform.fourier_add,
    FourierTransform.fourier_neg, fourier_sq_of_radial f hf]
  simp only [neg_add_rev, neg_neg]

private theorem antiFourierPart_zero {d : ℕ} (f : TestFunction d)
    (hbalance : (𝓕 f : TestFunction d) (0 : Euclidean d) = f 0) :
    antiFourierPart f (0 : Euclidean d) = 0 := by
  change (𝓕 f : TestFunction d) 0 - f 0 = 0
  exact sub_eq_zero.mpr hbalance

private theorem antiFourierPart_nonneg_of_signs {d : ℕ}
    (f : TestFunction d) (R : ℝ)
    (hfourier : ∀ x : Euclidean d, 0 ≤ ((𝓕 f) x).re)
    (houtside : ∀ x : Euclidean d, R ≤ ‖x‖ → (f x).re ≤ 0)
    (x : Euclidean d) (hx : R ≤ ‖x‖) :
    0 ≤ (antiFourierPart f x).re := by
  change 0 ≤ ((𝓕 f) x).re - (f x).re
  linarith [hfourier x, houtside x hx]

private structure AntiFourierWitness (d : ℕ) (R : ℝ) where
  function : TestFunction d
  real : IsRealValued function
  radial : IsRadial function
  nonzero : function ≠ 0
  anti_fourier : (𝓕 function : TestFunction d) = -function
  zero_value : function (0 : Euclidean d) = 0
  eventually_nonneg :
    ∀ x : Euclidean d, R ≤ ‖x‖ → 0 ≤ (function x).re

private noncomputable def UniformAntiFourierSignRadius : Prop :=
  ∀ c : ℝ, 0 < c → c < Real.pi⁻¹ →
    ∀ᶠ d : ℕ in atTop,
      IsEmpty (AntiFourierWitness d (c * Real.sqrt (d : ℝ)))

end

section

open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology RealInnerProductSpace ENNReal NNReal

private noncomputable def dilationEquiv (d : ℕ) (a : ℝ) (ha : a ≠ 0) :
    Euclidean d ≃L[ℝ] Euclidean d :=
  (LinearEquiv.smulOfNeZero ℝ (Euclidean d) a ha).toContinuousLinearEquiv

@[simp] private theorem dilationEquiv_apply (d : ℕ) (a : ℝ) (ha : a ≠ 0)
    (x : Euclidean d) : dilationEquiv d a ha x = a • x := by
  rfl

private noncomputable def dilate {d : ℕ} (f : TestFunction d) (a : ℝ) (ha : 0 < a) :
    TestFunction d :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (dilationEquiv d a ha.ne') f

@[simp] private theorem dilate_apply {d : ℕ} (f : TestFunction d)
    (a : ℝ) (ha : 0 < a) (x : Euclidean d) :
    dilate f a ha x = f (a • x) := by
  rfl

private theorem dilate_zero {d : ℕ} (f : TestFunction d)
    (a : ℝ) (ha : 0 < a) :
    dilate f a ha (0 : Euclidean d) = f 0 := by
  simp only [dilate_apply, smul_zero]

private theorem IsRealValued.dilate {d : ℕ} {f : TestFunction d}
    (hf : IsRealValued f) (a : ℝ) (ha : 0 < a) :
    IsRealValued (dilate f a ha) := by
  intro x
  exact hf (a • x)

private theorem IsRadial.dilate {d : ℕ} {f : TestFunction d}
    (hf : IsRadial f) (a : ℝ) (ha : 0 < a) :
    IsRadial (dilate f a ha) := by
  intro x y hxy
  apply hf
  simp only [ContinuousLinearEquiv.coe_coe, dilationEquiv_apply, norm_smul, Real.norm_eq_abs, hxy]

private theorem fourier_dilate_apply {d : ℕ} (f : TestFunction d)
    (a : ℝ) (ha : 0 < a) (ξ : Euclidean d) :
    ((𝓕 (dilate f a ha) : TestFunction d) ξ) =
      (a ^ d)⁻¹ • ((𝓕 f : TestFunction d) (a⁻¹ • ξ)) := by
  have hinner (x : Euclidean d) :
      @inner ℝ (Euclidean d) _ (a • x) (a⁻¹ • ξ) =
        @inner ℝ (Euclidean d) _ x ξ := by
    rw [real_inner_smul_left, real_inner_smul_right]
    field_simp
  calc
    ((𝓕 (dilate f a ha) : TestFunction d) ξ) =
        (𝓕 ((dilate f a ha : TestFunction d) : Euclidean d → ℂ)) ξ :=
      congrFun (SchwartzMap.fourier_coe (dilate f a ha)) ξ
    _ = ∫ x : Euclidean d,
          Complex.exp
            ((↑(-2 * Real.pi * @inner ℝ (Euclidean d) _ x ξ) : ℂ) * Complex.I) •
              f (a • x) := by
      rw [Real.fourier_eq']
      rfl
    _ = ∫ x : Euclidean d,
          (fun y : Euclidean d =>
            Complex.exp
              ((↑(-2 * Real.pi *
                @inner ℝ (Euclidean d) _ y (a⁻¹ • ξ)) : ℂ) * Complex.I) • f y)
            (a • x) := by
      congr 1
      funext x
      simp only [hinner x]
    _ = (a ^ d)⁻¹ •
          ∫ y : Euclidean d,
            Complex.exp
              ((↑(-2 * Real.pi *
                @inner ℝ (Euclidean d) _ y (a⁻¹ • ξ)) : ℂ) * Complex.I) • f y := by
      simpa only [neg_mul, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat,
        smul_eq_mul,
        Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow, finrank_euclideanSpace,
          Fintype.card_fin] using!
        (MeasureTheory.Measure.integral_comp_smul_of_nonneg
          (volume : Measure (Euclidean d))
          (fun y : Euclidean d =>
            Complex.exp
              ((↑(-2 * Real.pi *
                @inner ℝ (Euclidean d) _ y (a⁻¹ • ξ)) : ℂ) * Complex.I) • f y)
          a (hR := ha.le))
    _ = (a ^ d)⁻¹ • ((𝓕 f : TestFunction d) (a⁻¹ • ξ)) := by
      rw [← Real.fourier_eq']
      rw [SchwartzMap.fourier_coe]

private theorem fourier_dilate_zero {d : ℕ} (f : TestFunction d)
    (a : ℝ) (ha : 0 < a) :
    ((𝓕 (dilate f a ha) : TestFunction d) (0 : Euclidean d)) =
      (a ^ d)⁻¹ • ((𝓕 f : TestFunction d) (0 : Euclidean d)) := by
  simpa only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow,
    smul_zero] using! fourier_dilate_apply f a ha 0

private noncomputable def balancingScale {d : ℕ} (f : Admissible d) : ℝ :=
  (((𝓕 f.function : TestFunction d) (0 : Euclidean d)).re /
      (f.function (0 : Euclidean d)).re) ^ ((d : ℝ)⁻¹)

private theorem balancingScale_pos {d : ℕ} (f : Admissible d) :
    0 < balancingScale f := by
  unfold balancingScale
  exact Real.rpow_pos_of_pos
    (div_pos f.fourier_zero_pos (admissible_zero_pos f)) _

private theorem balancingScale_pow {d : ℕ} (f : Admissible d) (hd : 0 < d) :
    balancingScale f ^ d =
      ((𝓕 f.function : TestFunction d) (0 : Euclidean d)).re /
        (f.function (0 : Euclidean d)).re := by
  unfold balancingScale
  exact Real.rpow_inv_natCast_pow
    (div_pos f.fourier_zero_pos (admissible_zero_pos f)).le
    (Nat.ne_of_gt hd)

private theorem balancingScale_inv_eq_quotient_rpow {d : ℕ} (f : Admissible d) :
    (balancingScale f)⁻¹ = quotient f ^ ((d : ℝ)⁻¹) := by
  unfold balancingScale quotient
  rw [← Real.inv_rpow
    (div_pos f.fourier_zero_pos (admissible_zero_pos f)).le]
  rw [inv_div]

private theorem balancingScale_inv_eq_normalizedCost_mul_sqrt {d : ℕ}
    (f : Admissible d) (hd : 0 < d) :
    (balancingScale f)⁻¹ = normalizedCost f * Real.sqrt (d : ℝ) := by
  rw [balancingScale_inv_eq_quotient_rpow]
  unfold normalizedCost
  have hsqrt : Real.sqrt (d : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (by exact_mod_cast hd)).ne'
  field_simp

private noncomputable def balancedFunction {d : ℕ} (f : Admissible d) : TestFunction d :=
  dilate f.function (balancingScale f) (balancingScale_pos f)

@[simp] private theorem balancedFunction_apply {d : ℕ} (f : Admissible d)
    (x : Euclidean d) :
    balancedFunction f x = f.function (balancingScale f • x) := by
  rfl

private theorem balancedFunction_real {d : ℕ} (f : Admissible d) :
    IsRealValued (balancedFunction f) :=
  f.real.dilate (balancingScale f) (balancingScale_pos f)

private theorem balancedFunction_radial {d : ℕ} (f : Admissible d) :
    IsRadial (balancedFunction f) :=
  f.radial.dilate (balancingScale f) (balancingScale_pos f)

private theorem balancedFunction_fourier_real {d : ℕ} (f : Admissible d) :
    IsRealValued (𝓕 (balancedFunction f) : TestFunction d) := by
  intro ξ
  unfold balancedFunction
  rw [fourier_dilate_apply, Complex.smul_im,
    f.fourier_real ((balancingScale f)⁻¹ • ξ)]
  simp only [smul_eq_mul, mul_zero]

private theorem balancedFunction_fourier_nonneg {d : ℕ} (f : Admissible d)
    (ξ : Euclidean d) :
    0 ≤ ((𝓕 (balancedFunction f) : TestFunction d) ξ).re := by
  unfold balancedFunction
  rw [fourier_dilate_apply, Complex.smul_re]
  simpa only [smul_eq_mul] using!
    mul_nonneg
      (inv_nonneg.mpr (pow_nonneg (balancingScale_pos f).le d))
      (f.fourier_nonneg ((balancingScale f)⁻¹ • ξ))

private theorem balancedFunction_fourier_radial {d : ℕ} (f : Admissible d) :
    IsRadial (𝓕 (balancedFunction f) : TestFunction d) := by
  intro x y hxy
  let A : Euclidean d ≃ₗᵢ[ℝ] Euclidean d :=
    Submodule.reflection (ℝ ∙ (x - y))ᗮ
  have hA : A x = y := Submodule.reflection_sub hxy
  have hcomp :
      (balancedFunction f : Euclidean d → ℂ) ∘ A = balancedFunction f := by
    funext z
    exact balancedFunction_radial f (A z) z (A.norm_map z)
  change (𝓕 (balancedFunction f : Euclidean d → ℂ)) x =
    (𝓕 (balancedFunction f : Euclidean d → ℂ)) y
  calc
    (𝓕 (balancedFunction f : Euclidean d → ℂ)) x =
        (𝓕 ((balancedFunction f : Euclidean d → ℂ) ∘ A)) x := by
      rw [hcomp]
    _ = (𝓕 (balancedFunction f : Euclidean d → ℂ)) (A x) :=
      Real.fourier_comp_linearIsometry A
        (balancedFunction f : Euclidean d → ℂ) x
    _ = (𝓕 (balancedFunction f : Euclidean d → ℂ)) y := by rw [hA]

private theorem balancedFunction_fourier_zero {d : ℕ} (f : Admissible d)
    (hd : 0 < d) :
    ((𝓕 (balancedFunction f) : TestFunction d)
      (0 : Euclidean d)) = balancedFunction f 0 := by
  unfold balancedFunction
  rw [fourier_dilate_zero, balancingScale_pow f hd, dilate_zero]
  apply Complex.ext
  · rw [Complex.smul_re]
    change
      (((𝓕 f.function : TestFunction d) (0 : Euclidean d)).re /
        (f.function (0 : Euclidean d)).re)⁻¹ *
          ((𝓕 f.function : TestFunction d) (0 : Euclidean d)).re =
        (f.function (0 : Euclidean d)).re
    field_simp [f.fourier_zero_pos.ne', (admissible_zero_pos f).ne']
  · rw [Complex.smul_im]
    change
      (((𝓕 f.function : TestFunction d) (0 : Euclidean d)).re /
        (f.function (0 : Euclidean d)).re)⁻¹ *
          ((𝓕 f.function : TestFunction d) (0 : Euclidean d)).im =
        (f.function (0 : Euclidean d)).im
    rw [f.fourier_real, f.real]
    simp only [inv_div, mul_zero]

private theorem balancedFunction_outside_nonpos {d : ℕ} (f : Admissible d)
    (x : Euclidean d) (hx : (balancingScale f)⁻¹ ≤ ‖x‖) :
    (balancedFunction f x).re ≤ 0 := by
  apply f.outside_nonpos (balancingScale f • x)
  have h := mul_le_mul_of_nonneg_left hx (balancingScale_pos f).le
  rw [mul_inv_cancel₀ (balancingScale_pos f).ne'] at h
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (balancingScale_pos f), ge_iff_le] using! h

private noncomputable def balancedAntiFourierPart {d : ℕ} (f : Admissible d) : TestFunction d :=
  antiFourierPart (balancedFunction f)

private theorem fourier_balancedAntiFourierPart {d : ℕ} (f : Admissible d) :
    (𝓕 (balancedAntiFourierPart f) : TestFunction d) =
      -balancedAntiFourierPart f := by
  exact fourier_antiFourierPart (balancedFunction f)
    (balancedFunction_radial f)

private theorem balancedAntiFourierPart_zero {d : ℕ} (f : Admissible d)
    (hd : 0 < d) :
    balancedAntiFourierPart f (0 : Euclidean d) = 0 := by
  exact antiFourierPart_zero (balancedFunction f)
    (balancedFunction_fourier_zero f hd)

private theorem balancedAntiFourierPart_real {d : ℕ} (f : Admissible d) :
    IsRealValued (balancedAntiFourierPart f) := by
  intro x
  change (((𝓕 (balancedFunction f) : TestFunction d) x) -
    balancedFunction f x).im = 0
  rw [Complex.sub_im, balancedFunction_fourier_real f x,
    balancedFunction_real f x]
  norm_num

private theorem balancedAntiFourierPart_radial {d : ℕ} (f : Admissible d) :
    IsRadial (balancedAntiFourierPart f) := by
  intro x y hxy
  change
    ((𝓕 (balancedFunction f) : TestFunction d) x) -
        balancedFunction f x =
      ((𝓕 (balancedFunction f) : TestFunction d) y) -
        balancedFunction f y
  rw [balancedFunction_fourier_radial f x y hxy,
    balancedFunction_radial f x y hxy]

private theorem balancedAntiFourierPart_nonneg {d : ℕ} (f : Admissible d)
    (x : Euclidean d) (hx : (balancingScale f)⁻¹ ≤ ‖x‖) :
    0 ≤ (balancedAntiFourierPart f x).re := by
  exact antiFourierPart_nonneg_of_signs
    (balancedFunction f) ((balancingScale f)⁻¹)
    (balancedFunction_fourier_nonneg f)
    (balancedFunction_outside_nonpos f) x hx

private theorem balancedAntiFourierPart_eq_zero_iff {d : ℕ} (f : Admissible d) :
    balancedAntiFourierPart f = 0 ↔
      (𝓕 (balancedFunction f) : TestFunction d) = balancedFunction f := by
  change (𝓕 (balancedFunction f) : TestFunction d) -
    balancedFunction f = 0 ↔ _
  exact sub_eq_zero

private theorem balancedFunction_support_subset_of_anti_zero {d : ℕ}
    (f : Admissible d) (hzero : balancedAntiFourierPart f = 0) :
    Function.support (balancedFunction f : Euclidean d → ℂ) ⊆
      Metric.closedBall (0 : Euclidean d) (balancingScale f)⁻¹ := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hnot
  have hlarge : (balancingScale f)⁻¹ < ‖x‖ := lt_of_not_ge hnot
  have hself := (balancedAntiFourierPart_eq_zero_iff f).mp hzero
  have hnonneg : 0 ≤ (balancedFunction f x).re := by
    have hpoint :
        ((𝓕 (balancedFunction f) : TestFunction d) x) =
          balancedFunction f x :=
      congrArg (fun g : TestFunction d => g x) hself
    calc
      0 ≤ ((𝓕 (balancedFunction f) : TestFunction d) x).re :=
        balancedFunction_fourier_nonneg f x
      _ = (balancedFunction f x).re := congrArg Complex.re hpoint
  have hnonpos : (balancedFunction f x).re ≤ 0 :=
    balancedFunction_outside_nonpos f x hlarge.le
  have hre : (balancedFunction f x).re = 0 :=
    le_antisymm hnonpos hnonneg
  apply hx
  apply Complex.ext
  · simpa only [balancedFunction_apply, Complex.zero_re] using! hre
  · simpa only [balancedFunction_apply, Complex.zero_im] using! balancedFunction_real f x

private theorem balancedFunction_hasCompactSupport_of_anti_zero {d : ℕ}
    (f : Admissible d) (hzero : balancedAntiFourierPart f = 0) :
    HasCompactSupport (balancedFunction f : Euclidean d → ℂ) := by
  exact HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Euclidean d) (balancingScale f)⁻¹)
    (balancedFunction_support_subset_of_anti_zero f hzero)

private noncomputable def nonnegativeSchwartzDensity {d : ℕ} (g : TestFunction d)
    (hg : ∀ x : Euclidean d, 0 ≤ (g x).re) :
    Euclidean d → ℝ≥0 :=
  fun x => ⟨(g x).re, hg x⟩

private theorem nonnegativeSchwartzDensity_continuous {d : ℕ}
    (g : TestFunction d) (hg : ∀ x : Euclidean d, 0 ≤ (g x).re) :
    Continuous (nonnegativeSchwartzDensity g hg) := by
  exact (Complex.continuous_re.comp g.continuous).subtype_mk hg

private noncomputable def nonnegativeSchwartzMeasure {d : ℕ} (g : TestFunction d)
    (hg : ∀ x : Euclidean d, 0 ≤ (g x).re) :
    Measure (Euclidean d) :=
  (volume : Measure (Euclidean d)).withDensity
    (fun x => (nonnegativeSchwartzDensity g hg x : ℝ≥0∞))

private theorem integrableExpSet_nonnegativeSchwartzMeasure_eq_univ {d : ℕ}
    (g : TestFunction d) (hg : ∀ x : Euclidean d, 0 ≤ (g x).re)
    (hcompact : HasCompactSupport (g : Euclidean d → ℂ))
    (X : Euclidean d → ℝ) (hX : Continuous X) :
    ProbabilityTheory.integrableExpSet X
      (nonnegativeSchwartzMeasure g hg) = Set.univ := by
  ext t
  simp only [ProbabilityTheory.integrableExpSet, Set.mem_ofPred_eq,
    Set.mem_univ, iff_true]
  unfold nonnegativeSchwartzMeasure
  rw [integrable_withDensity_iff_integrable_smul
    (nonnegativeSchwartzDensity_continuous g hg).measurable]
  simp_rw [NNReal.smul_def, smul_eq_mul]
  have hrealcompact :
      HasCompactSupport (fun x : Euclidean d => (g x).re) := by
    change HasCompactSupport (Complex.re ∘
      (g : Euclidean d → ℂ))
    exact hcompact.comp_left (by simp only [Complex.zero_re])
  have hcontinuous :
      Continuous (fun x : Euclidean d =>
        (g x).re * Real.exp (t * X x)) := by
    exact (Complex.continuous_re.comp g.continuous).mul
      (Real.continuous_exp.comp (continuous_const.mul hX))
  exact hcontinuous.integrable_of_hasCompactSupport
    hrealcompact.mul_right

private theorem nonnegativeSchwartz_complexMGF_analytic {d : ℕ}
    (g : TestFunction d) (hg : ∀ x : Euclidean d, 0 ≤ (g x).re)
    (hcompact : HasCompactSupport (g : Euclidean d → ℂ))
    (X : Euclidean d → ℝ) (hX : Continuous X) :
    AnalyticOnNhd ℂ
      (ProbabilityTheory.complexMGF X
        (nonnegativeSchwartzMeasure g hg)) Set.univ := by
  have hset := integrableExpSet_nonnegativeSchwartzMeasure_eq_univ
    g hg hcompact X hX
  simpa only [hset, interior_univ, mem_univ, ofPred_true] using!
    (ProbabilityTheory.analyticOnNhd_complexMGF
      (X := X) (μ := nonnegativeSchwartzMeasure g hg))

private theorem nonnegativeSchwartz_complexMGF_mul_I {d : ℕ}
    (g : TestFunction d) (hreal : IsRealValued g)
    (hg : ∀ x : Euclidean d, 0 ≤ (g x).re)
    (e : Euclidean d) (t : ℝ) :
    ProbabilityTheory.complexMGF
        (fun x : Euclidean d =>
          -2 * Real.pi * @inner ℝ (Euclidean d) _ x e)
        (nonnegativeSchwartzMeasure g hg)
        ((t : ℂ) * Complex.I) =
      ((𝓕 g : TestFunction d) (t • e)) := by
  calc
    ProbabilityTheory.complexMGF
        (fun x : Euclidean d =>
          -2 * Real.pi * @inner ℝ (Euclidean d) _ x e)
        (nonnegativeSchwartzMeasure g hg)
        ((t : ℂ) * Complex.I) =
      ∫ x : Euclidean d,
        nonnegativeSchwartzDensity g hg x •
          Complex.exp
            (((t : ℂ) * Complex.I) *
              (↑(-2 * Real.pi *
                @inner ℝ (Euclidean d) _ x e) : ℂ)) := by
        unfold ProbabilityTheory.complexMGF nonnegativeSchwartzMeasure
        rw [integral_withDensity_eq_integral_smul
          (nonnegativeSchwartzDensity_continuous g hg).measurable]
    _ = (𝓕 (g : Euclidean d → ℂ)) (t • e) := by
      rw [Real.fourier_eq']
      apply integral_congr_ae
      filter_upwards [] with x
      have hvalue : (↑((g x).re) : ℂ) = g x := by
        apply Complex.ext
        · simp only [Complex.ofReal_re]
        · simpa only [Complex.ofReal_im] using! (hreal x).symm
      have hexponent :
          ((t : ℂ) * Complex.I) *
              (↑(-2 * Real.pi *
                @inner ℝ (Euclidean d) _ x e) : ℂ) =
            (↑(-2 * Real.pi *
              @inner ℝ (Euclidean d) _ x (t • e)) : ℂ) *
                Complex.I := by
        rw [real_inner_smul_right]
        push_cast
        ring
      rw [NNReal.smul_def, Complex.real_smul, hexponent]
      change (↑((g x).re) : ℂ) * _ = _ * g x
      rw [hvalue, mul_comm]
    _ = ((𝓕 g : TestFunction d) (t • e)) :=
      (congrFun (SchwartzMap.fourier_coe g) (t • e)).symm

private theorem analytic_eq_zero_of_imaginary_ray
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F Set.univ)
    (T : ℝ)
    (hvanish : ∀ t : ℝ, T < t → F ((t : ℂ) * Complex.I) = 0) :
    F = 0 := by
  let t₀ : ℝ := T + 1
  let z₀ : ℂ := (t₀ : ℂ) * Complex.I
  have hclosure :
      z₀ ∈ closure ({z : ℂ | F z = 0} \ {z₀}) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let u : ℝ := t₀ + ε / 2
    let z : ℂ := (u : ℂ) * Complex.I
    refine ⟨z, ⟨?_, ?_⟩, ?_⟩
    · apply hvanish u
      try dsimp [u, t₀]
      linarith
    · intro hz
      have hu : u = t₀ := by
        have him := congrArg Complex.im hz
        simpa [z, z₀] using! him
      try dsimp [u] at hu
      linarith
    · dsimp [z₀, z, u]
      rw [dist_eq_norm, ← sub_mul, ← Complex.ofReal_sub, norm_mul,
        Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
      rw [show t₀ - (t₀ + ε / 2) = -(ε / 2) by ring,
        abs_neg, abs_of_pos (half_pos hε)]
      exact half_lt_self hε
  have heq :=
    hF.eqOn_zero_of_preconnected_of_mem_closure
      isPreconnected_univ (Set.mem_univ z₀) hclosure
  funext z
  exact heq (Set.mem_univ z)

private theorem nonnegative_compact_fourier_fixed_eq_zero {d : ℕ}
    (hd : 0 < d) (g : TestFunction d)
    (hreal : IsRealValued g)
    (hg : ∀ x : Euclidean d, 0 ≤ (g x).re)
    (hcompact : HasCompactSupport (g : Euclidean d → ℂ))
    (hfixed : (𝓕 g : TestFunction d) = g) :
    g = 0 := by
  classical
  let : Nontrivial (Euclidean d) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (M := Euclidean d)
      (by simpa only [finrank_euclideanSpace, Fintype.card_fin] using! hd)
  obtain ⟨e, he⟩ :=
    exists_norm_eq (Euclidean d) (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨R, hR⟩ :=
    hcompact.isBounded.subset_closedBall (0 : Euclidean d)
  let X : Euclidean d → ℝ :=
    fun x => -2 * Real.pi * @inner ℝ (Euclidean d) _ x e
  have hX : Continuous X := by
    try dsimp [X]
    fun_prop
  let μ : Measure (Euclidean d) := nonnegativeSchwartzMeasure g hg
  let F : ℂ → ℂ := ProbabilityTheory.complexMGF X μ
  have hanalytic : AnalyticOnNhd ℂ F Set.univ := by
    try dsimp [F, μ]
    exact nonnegativeSchwartz_complexMGF_analytic g hg hcompact X hX
  have hvanish :
      ∀ t : ℝ, max R 0 < t → F ((t : ℂ) * Complex.I) = 0 := by
    intro t ht
    change
      ProbabilityTheory.complexMGF
          (fun x : Euclidean d =>
            -2 * Real.pi * @inner ℝ (Euclidean d) _ x e)
          (nonnegativeSchwartzMeasure g hg)
          ((t : ℂ) * Complex.I) = 0
    rw [nonnegativeSchwartz_complexMGF_mul_I g hreal hg e t,
      hfixed]
    by_contra hnonzero
    have hsupp :
        t • e ∈ Function.support (g : Euclidean d → ℂ) := by
      exact hnonzero
    have hbound : ‖t • e‖ ≤ R := by
      have hball := hR
        (subset_tsupport (g : Euclidean d → ℂ) hsupp)
      simpa only [Metric.mem_closedBall, dist_zero_right] using! hball
    have htpos : 0 < t := (le_max_right R 0).trans_lt ht
    have hnorm : ‖t • e‖ = t := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos, he, mul_one]
    rw [hnorm] at hbound
    exact (not_le_of_gt ((le_max_left R 0).trans_lt ht)) hbound
  have hFzero : F = 0 :=
    analytic_eq_zero_of_imaginary_ray F hanalytic (max R 0) hvanish
  have hFzero_at_zero : F 0 = 0 := by
    simpa only [Pi.zero_apply] using! congrFun hFzero (0 : ℂ)
  have hfourierzero :
      ((𝓕 g : TestFunction d) (0 : Euclidean d)) = 0 := by
    have hmomentzero :
        ProbabilityTheory.complexMGF
          (fun x : Euclidean d =>
            -2 * Real.pi * @inner ℝ (Euclidean d) _ x e)
          (nonnegativeSchwartzMeasure g hg) 0 = 0 := by
      exact hFzero_at_zero
    calc
      ((𝓕 g : TestFunction d) (0 : Euclidean d)) =
          ProbabilityTheory.complexMGF
            (fun x : Euclidean d =>
              -2 * Real.pi * @inner ℝ (Euclidean d) _ x e)
            (nonnegativeSchwartzMeasure g hg)
            ((0 : ℂ) * Complex.I) := by
        simpa only [neg_mul, zero_mul, zero_smul, Complex.ofReal_zero] using!
          (nonnegativeSchwartz_complexMGF_mul_I g hreal hg e 0).symm
      _ = 0 := by simpa only [neg_mul, zero_mul] using! hmomentzero
  have hfourier_integral :
      ((𝓕 g : TestFunction d) (0 : Euclidean d)) =
        ∫ x : Euclidean d, g x := by
    change (𝓕 (g : Euclidean d → ℂ)) 0 = _
    rw [Real.fourier_eq']
    simp only [neg_mul, inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, smul_eq_mul,
      one_mul]
  have hintegral :
      (∫ x : Euclidean d, (g x).re) = 0 := by
    calc
      (∫ x : Euclidean d, (g x).re) =
          (∫ x : Euclidean d, g x).re :=
        integral_re g.integrable
      _ = ((𝓕 g : TestFunction d) (0 : Euclidean d)).re := by
        rw [hfourier_integral]
      _ = 0 := by rw [hfourierzero]; rfl
  by_contra hnonzero
  have hreal_nonzero :
      (fun x : Euclidean d => (g x).re) ≠ 0 := by
    intro hzero
    apply hnonzero
    ext x
    apply Complex.ext
    · simpa only [zero_apply, Complex.zero_re, Pi.zero_apply] using! congrFun hzero x
    · simpa only [zero_apply, Complex.zero_im] using! hreal x
  obtain ⟨x, hx⟩ :
      ∃ x : Euclidean d, (g x).re ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hreal_nonzero
    funext x
    simpa only [Pi.zero_apply] using! hnone x
  have hpositive :
      0 < ∫ x : Euclidean d, (g x).re :=
    integral_pos_of_integrable_nonneg_nonzero
      (Complex.continuous_re.comp g.continuous)
      g.integrable.re hg hx
  exact (ne_of_gt hpositive) hintegral

private theorem balancedAntiFourierPart_ne_zero {d : ℕ}
    (f : Admissible d) (hd : 0 < d) :
    balancedAntiFourierPart f ≠ 0 := by
  intro hzero
  have hself := (balancedAntiFourierPart_eq_zero_iff f).mp hzero
  have hcompact := balancedFunction_hasCompactSupport_of_anti_zero f hzero
  have hnonneg :
      ∀ x : Euclidean d, 0 ≤ (balancedFunction f x).re := by
    intro x
    rw [← hself]
    exact balancedFunction_fourier_nonneg f x
  have hvanish :=
    nonnegative_compact_fourier_fixed_eq_zero hd
      (balancedFunction f) (balancedFunction_real f)
      hnonneg hcompact hself
  have horigin := congrArg
    (fun g : TestFunction d => (g (0 : Euclidean d)).re) hvanish
  have hpos : 0 < (balancedFunction f (0 : Euclidean d)).re := by
    simpa only [balancedFunction_apply, smul_zero] using! admissible_zero_pos f
  simpa only  using! hpos.ne' horigin

private noncomputable def AntiFourierWitness.monoRadius {d : ℕ} {R S : ℝ}
    (w : AntiFourierWitness d R) (hRS : R ≤ S) :
    AntiFourierWitness d S where
  function := w.function
  real := w.real
  radial := w.radial
  nonzero := w.nonzero
  anti_fourier := w.anti_fourier
  zero_value := w.zero_value
  eventually_nonneg := fun x hx =>
    w.eventually_nonneg x (hRS.trans hx)

private noncomputable def balancedAntiFourierWitness {d : ℕ} (f : Admissible d)
    (hd : 0 < d) :
    AntiFourierWitness d (balancingScale f)⁻¹ where
  function := balancedAntiFourierPart f
  real := balancedAntiFourierPart_real f
  radial := balancedAntiFourierPart_radial f
  nonzero := balancedAntiFourierPart_ne_zero f hd
  anti_fourier := fourier_balancedAntiFourierPart f
  zero_value := balancedAntiFourierPart_zero f hd
  eventually_nonneg := balancedAntiFourierPart_nonneg f

private theorem normalizedCost_ge_of_no_antiFourierWitness {d : ℕ}
    (f : Admissible d) (hd : 0 < d) (c : ℝ)
    (hno : IsEmpty (AntiFourierWitness d (c * Real.sqrt (d : ℝ)))) :
    c ≤ normalizedCost f := by
  by_contra hnot
  have hcost : normalizedCost f < c := lt_of_not_ge hnot
  have hradius :
      (balancingScale f)⁻¹ ≤ c * Real.sqrt (d : ℝ) := by
    rw [balancingScale_inv_eq_normalizedCost_mul_sqrt f hd]
    exact mul_le_mul_of_nonneg_right hcost.le (Real.sqrt_nonneg _)
  exact hno.false
    ((balancedAntiFourierWitness f hd).monoRadius hradius)

end

section

open MeasureTheory Metric
open scoped ENNReal

private theorem sqrt_pi_pow_eq_rpow (d : ℕ) :
    Real.sqrt Real.pi ^ d = Real.pi ^ ((d : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul Real.pi_nonneg]
  congr 1
  ring

private theorem volume_unitBall {d : ℕ} (hd : 0 < d) :
    volume (ball (0 : Euclidean d) (1 : ℝ)) =
      ENNReal.ofReal (unitBallVolume d) := by
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  simpa only [unitBallVolume, ENNReal.ofReal_one, Fintype.card_fin, one_pow, sqrt_pi_pow_eq_rpow,
    one_mul] using!
    (EuclideanSpace.volume_ball (Fin d) (0 : Euclidean d) (1 : ℝ))

private theorem unitBallVolume_even (k : ℕ) :
    unitBallVolume (2 * k) = Real.pi ^ k / (k.factorial : ℝ) := by
  unfold unitBallVolume
  have hhalf : ((↑(2 * k) : ℝ) / 2) = (k : ℝ) := by
    push_cast
    ring
  rw [hhalf, Real.rpow_natCast, Real.Gamma_nat_eq_factorial]

end

section

open Filter MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology ENNReal

private noncomputable def radialUnitDirection {d : ℕ} (hd : 0 < d) : Euclidean d :=
  (EuclideanSpace.basisFun (Fin d) ℝ) ⟨0, hd⟩

private theorem norm_radialUnitDirection {d : ℕ} (hd : 0 < d) :
    ‖radialUnitDirection hd‖ = 1 := by
  unfold radialUnitDirection
  exact (EuclideanSpace.basisFun (Fin d) ℝ).norm_eq_one _

private noncomputable def radialProfile {d : ℕ} (hd : 0 < d)
    (f : TestFunction d) (r : ℝ) : ℂ :=
  f (r • radialUnitDirection hd)

private theorem radialProfile_norm {d : ℕ} (hd : 0 < d)
    (f : TestFunction d) (hf : IsRadial f) (x : Euclidean d) :
    radialProfile hd f ‖x‖ = f x := by
  unfold radialProfile
  apply hf
  simp only [norm_smul, norm_norm, norm_radialUnitDirection hd, mul_one]

private theorem radialProfile_neg {d : ℕ} (hd : 0 < d)
    (f : TestFunction d) (hf : IsRadial f) (r : ℝ) :
    radialProfile hd f (-r) = radialProfile hd f r := by
  unfold radialProfile
  apply hf
  simp only [neg_smul, norm_neg, norm_smul, Real.norm_eq_abs, norm_radialUnitDirection hd, mul_one]

private theorem radialProfile_continuous {d : ℕ} (hd : 0 < d)
    (f : TestFunction d) :
    Continuous (radialProfile hd f) := by
  unfold radialProfile
  exact f.continuous.comp (continuous_id.smul continuous_const)

@[simp] private theorem radialProfile_zero {d : ℕ} (hd : 0 < d)
    (f : TestFunction d) :
    radialProfile hd f 0 = f (0 : Euclidean d) := by
  simp only [radialProfile, zero_smul]

private theorem radialProfile_real {d : ℕ} (hd : 0 < d)
    (f : TestFunction d) (hf : IsRealValued f) (r : ℝ) :
    (radialProfile hd f r).im = 0 :=
  hf (r • radialUnitDirection hd)

private theorem volume_real_unitBall {d : ℕ} (hd : 0 < d) :
    volume.real (ball (0 : Euclidean d) (1 : ℝ)) =
      unitBallVolume d := by
  change (volume (ball (0 : Euclidean d) (1 : ℝ))).toReal =
    unitBallVolume d
  rw [volume_unitBall hd, ENNReal.toReal_ofReal
    (unitBallVolume_pos d).le]

private noncomputable def radialSurfaceArea (d : ℕ) : ℝ :=
  (d : ℝ) * unitBallVolume d

private theorem radialSurfaceArea_pos {d : ℕ} (hd : 0 < d) :
    0 < radialSurfaceArea d := by
  unfold radialSurfaceArea
  exact mul_pos (by exact_mod_cast hd) (unitBallVolume_pos d)

private theorem integral_radialProfile_mul {d : ℕ} (hd : 0 < d)
    (f : TestFunction d) (hf : IsRadial f) (w : ℝ → ℂ) :
    (∫ x : Euclidean d, f x * w ‖x‖) =
      radialSurfaceArea d •
        ∫ r : ℝ in Ioi 0,
          r ^ (d - 1) • (radialProfile hd f r * w r) := by
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  calc
    (∫ x : Euclidean d, f x * w ‖x‖) =
        ∫ x : Euclidean d,
          radialProfile hd f ‖x‖ * w ‖x‖ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [radialProfile_norm hd f hf x]
    _ = radialSurfaceArea d •
          ∫ r : ℝ in Ioi 0,
            r ^ (d - 1) • (radialProfile hd f r * w r) := by
      simpa only [radialSurfaceArea, Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_mul,
        Complex.ofReal_natCast, mul_assoc, finrank_euclideanSpace, Fintype.card_fin,
          volume_real_unitBall hd,
        nsmul_eq_mul] using!
        (integral_fun_norm_addHaar
          (volume : Measure (Euclidean d))
          (fun r : ℝ => radialProfile hd f r * w r))

private theorem integral_radialProfile_cpow {d : ℕ} (hd : 0 < d)
    (f : TestFunction d) (hf : IsRadial f) (s : ℂ) :
    (∫ x : Euclidean d,
      f x * (‖x‖ : ℂ) ^ (s - (d : ℂ))) =
      radialSurfaceArea d • mellin (radialProfile hd f) s := by
  rw [integral_radialProfile_mul hd f hf
    (fun r : ℝ => (r : ℂ) ^ (s - (d : ℂ)))]
  congr 1
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hrzero : (r : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have hcast :
      (((r ^ (d - 1) : ℝ) : ℂ)) =
        (r : ℂ) ^ ((d - 1 : ℕ) : ℂ) := by
    rw [Complex.cpow_natCast]
    norm_cast
  have hexponent :
      (((d - 1 : ℕ) : ℂ)) + (s - (d : ℂ)) = s - 1 := by
    rw [Nat.cast_sub hd]
    norm_num
  change
    (((r ^ (d - 1) : ℝ) : ℂ)) *
      (radialProfile hd f r * (r : ℂ) ^ (s - (d : ℂ))) =
        (r : ℂ) ^ (s - 1) * radialProfile hd f r
  rw [hcast]
  have hpower :
      (r : ℂ) ^ ((d - 1 : ℕ) : ℂ) *
        (r : ℂ) ^ (s - (d : ℂ)) =
          (r : ℂ) ^ (s - 1) := by
    rw [← Complex.cpow_add _ _ hrzero, hexponent]
  calc
    (r : ℂ) ^ ((d - 1 : ℕ) : ℂ) *
        (radialProfile hd f r *
          (r : ℂ) ^ (s - (d : ℂ))) =
      ((r : ℂ) ^ ((d - 1 : ℕ) : ℂ) *
        (r : ℂ) ^ (s - (d : ℂ))) * radialProfile hd f r := by
          ring
    _ = (r : ℂ) ^ (s - 1) * radialProfile hd f r := by
          rw [hpower]

private noncomputable def radialMellinFrequency {d : ℕ} (hd : 0 < d)
    (f : TestFunction d) (t : ℝ) : ℂ :=
  mellinFrequency ((d : ℝ) / 2) (radialProfile hd f) t

private theorem radialMellinFrequency_eq_fourier {d : ℕ} (hd : 0 < d)
    (f : TestFunction d) (t : ℝ) :
    radialMellinFrequency hd f t =
      (𝓕 (fun u : ℝ =>
        Real.exp (-((d : ℝ) / 2) * u) •
          radialProfile hd f (Real.exp (-u))))
        (-t / (2 * Real.pi)) := by
  exact mellinFrequency_eq_fourier
    ((d : ℝ) / 2) (radialProfile hd f) t

end

section

open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology RealInnerProductSpace

private noncomputable def gaussianMellinWeight (d : ℕ) (a : ℝ) (x : Euclidean d) : ℂ :=
  Complex.exp (-((a : ℂ) * (‖x‖ : ℂ) ^ 2))

private theorem gaussianMellin_fourier_radial {d : ℕ} {f : TestFunction d}
    (hf : IsRadial f) : IsRadial (𝓕 f : TestFunction d) := by
  intro x y hxy
  let A : Euclidean d ≃ₗᵢ[ℝ] Euclidean d :=
    Submodule.reflection (ℝ ∙ (x - y))ᗮ
  have hA : A x = y := Submodule.reflection_sub hxy
  have hcomp : (f : Euclidean d → ℂ) ∘ A = f := by
    funext z
    exact hf (A z) z (A.norm_map z)
  change (𝓕 (f : Euclidean d → ℂ)) x =
    (𝓕 (f : Euclidean d → ℂ)) y
  calc
    (𝓕 (f : Euclidean d → ℂ)) x =
        (𝓕 ((f : Euclidean d → ℂ) ∘ A)) x := by rw [hcomp]
    _ = (𝓕 (f : Euclidean d → ℂ)) (A x) :=
      Real.fourier_comp_linearIsometry A (f : Euclidean d → ℂ) x
    _ = (𝓕 (f : Euclidean d → ℂ)) y := by rw [hA]

private theorem gaussianMellinWeight_integrable {d : ℕ}
    (a : ℝ) (ha : 0 < a) :
    Integrable (gaussianMellinWeight d a)
      (volume : Measure (Euclidean d)) := by
  have hcomplex : 0 < (a : ℂ).re := by
    simpa only [Complex.ofReal_re] using! ha
  simpa only [neg_mul, inner_zero_left, Complex.ofReal_zero, mul_zero, add_zero] using!
    (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (V := Euclidean d) hcomplex (0 : ℂ) (0 : Euclidean d))

private theorem fourier_gaussianMellinWeight {d : ℕ}
    (a : ℝ) (ha : 0 < a) (ξ : Euclidean d) :
    (𝓕 (gaussianMellinWeight d a) : Euclidean d → ℂ) ξ =
      ((Real.pi : ℂ) / (a : ℂ)) ^ ((d : ℂ) / 2) *
        Complex.exp
          (-((Real.pi : ℂ) ^ 2) * (‖ξ‖ : ℂ) ^ 2 / (a : ℂ)) := by
  have hcomplex : 0 < (a : ℂ).re := by
    simpa only [Complex.ofReal_re] using! ha
  simpa only [neg_mul, finrank_euclideanSpace, Fintype.card_fin] using!
    (fourier_gaussian_innerProductSpace (V := Euclidean d)
      hcomplex ξ)

private theorem fourier_gaussianMellin_pairing {d : ℕ}
    (f : TestFunction d) (a : ℝ) (ha : 0 < a) :
    (∫ ξ : Euclidean d,
      ((𝓕 f : TestFunction d) ξ) * gaussianMellinWeight d a ξ) =
      ∫ x : Euclidean d,
        f x *
          (((Real.pi : ℂ) / (a : ℂ)) ^ ((d : ℂ) / 2) *
            Complex.exp
              (-((Real.pi : ℂ) ^ 2) * (‖x‖ : ℂ) ^ 2 /
                (a : ℂ))) := by
  have hflip :
      (innerₗ (Euclidean d)).flip = innerₗ (Euclidean d) := by
    ext x y
    change
      @inner ℝ (Euclidean d) _ y x =
        @inner ℝ (Euclidean d) _ x y
    exact real_inner_comm x y
  calc
    (∫ ξ : Euclidean d,
      ((𝓕 f : TestFunction d) ξ) * gaussianMellinWeight d a ξ) =
        ∫ ξ : Euclidean d,
          (𝓕 (f : Euclidean d → ℂ)) ξ *
            gaussianMellinWeight d a ξ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      exact congrArg
        (fun z : ℂ => z * gaussianMellinWeight d a ξ)
        (congrFun (SchwartzMap.fourier_coe f) ξ)
    _ = ∫ x : Euclidean d,
          f x *
            (𝓕 (gaussianMellinWeight d a) :
              Euclidean d → ℂ) x := by
      simpa only [smul_eq_mul, hflip] using!
        (VectorFourier.integral_fourierIntegral_smul_eq_flip
          (L := innerₗ (Euclidean d))
          (μ := (volume : Measure (Euclidean d)))
          (ν := (volume : Measure (Euclidean d)))
          (f := (f : Euclidean d → ℂ))
          (g := gaussianMellinWeight d a)
          Real.continuous_fourierChar continuous_inner
          f.integrable (gaussianMellinWeight_integrable a ha))
    _ = ∫ x : Euclidean d,
          f x *
            (((Real.pi : ℂ) / (a : ℂ)) ^ ((d : ℂ) / 2) *
              Complex.exp
                (-((Real.pi : ℂ) ^ 2) * (‖x‖ : ℂ) ^ 2 /
                  (a : ℂ))) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [fourier_gaussianMellinWeight a ha x]

private theorem schwartz_mul_norm_cpow_integrable {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (z : ℂ)
    (hlower : -(d : ℝ) < z.re) (hupper : z.re ≤ 0) :
    Integrable
      (fun x : Euclidean d => f x * (‖x‖ : ℂ) ^ z)
      (volume : Measure (Euclidean d)) := by
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hpow : Measurable (fun x : Euclidean d => (‖x‖ : ℂ) ^ z) := by
    apply measurable_of_continuousOn_compl_singleton
      (0 : Euclidean d)
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hxzero : x ≠ 0 := by
      simpa only [mem_compl_iff, mem_singleton_iff] using! hx
    exact
      (Complex.continuousAt_ofReal_cpow_const ‖x‖ z
        (Or.inr (norm_ne_zero_iff.mpr hxzero))).comp
        continuous_norm.continuousAt
  have hmeas :
      AEStronglyMeasurable
        (fun x : Euclidean d => f x * (‖x‖ : ℂ) ^ z)
        (volume : Measure (Euclidean d)) :=
    (f.continuous.measurable.mul hpow).aestronglyMeasurable
  have hdim : 1 ≤ Module.finrank ℝ (Euclidean d) := by
    rw [finrank_euclideanSpace_fin]
    omega
  have hexponent :
      -z.re < (Module.finrank ℝ (Euclidean d) : ℝ) := by
    rw [finrank_euclideanSpace_fin]
    exact (neg_lt_of_neg_lt hlower)
  have hinner :
      IntegrableOn
        (fun x : Euclidean d => f x * (‖x‖ : ℂ) ^ z)
        (Metric.ball 0 1)
        (volume : Measure (Euclidean d)) := by
    apply MeasureTheory.integrableOn_ball_of_norm_le_rpow
      hdim hexponent (C := SchwartzMap.seminorm ℝ 0 0 f)
      (r := 1)
    · filter_upwards
        [ae_restrict_of_ae
          ((volume : Measure (Euclidean d)).ae_ne
            (0 : Euclidean d))] with x hx
      rw [norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos
          (norm_pos_iff.mpr hx), neg_neg]
      exact mul_le_mul_of_nonneg_right
        (SchwartzMap.norm_le_seminorm ℝ f x)
        (Real.rpow_nonneg (norm_nonneg x) z.re)
    · exact hmeas
  have houter :
      IntegrableOn
        (fun x : Euclidean d => f x * (‖x‖ : ℂ) ^ z)
        (Metric.ball (0 : Euclidean d) 1)ᶜ
        (volume : Measure (Euclidean d)) := by
    refine (f.integrable.norm.restrict).mono' hmeas.restrict ?_
    filter_upwards
      [ae_restrict_mem
        (Metric.isOpen_ball.measurableSet.compl)] with x hx
    have hnorm : 1 ≤ ‖x‖ := by
      have hnot : ¬ ‖x‖ < (1 : ℝ) := by
        simpa only [not_lt, mem_compl_iff, Metric.mem_ball, dist_zero_right] using! hx
      exact le_of_not_gt hnot
    rw [norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos
        (lt_of_lt_of_le zero_lt_one hnorm)]
    calc
      ‖f x‖ * ‖x‖ ^ z.re ≤ ‖f x‖ * 1 :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_one_of_one_le_of_nonpos hnorm hupper)
          (norm_nonneg _)
      _ = ‖f x‖ := mul_one _
  have hglobal := hinner.union houter
  rwa [union_compl_self, integrableOn_univ] at hglobal

private theorem gaussianMellinParameter_integrable
    (b : ℂ) (hb : 0 < b.re) (r : ℝ) (hr : 0 < r) :
    IntegrableOn
      (fun a : ℝ =>
        (a : ℂ) ^ (b - 1) *
          Complex.exp (-((r : ℂ) * (a : ℂ))))
      (Ioi 0) := by
  have hmeas :
      AEStronglyMeasurable
        (fun a : ℝ =>
          (a : ℂ) ^ (b - 1) *
            Complex.exp (-((r : ℂ) * (a : ℂ))))
        (volume.restrict (Ioi (0 : ℝ))) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply continuousOn_of_forall_continuousAt
    intro a ha
    apply
      (Complex.continuousAt_ofReal_cpow_const a (b - 1)
        (Or.inr (ne_of_gt ha))).mul
    fun_prop
  have hreal :
      IntegrableOn
        (fun a : ℝ =>
          a ^ (b.re - 1) * Real.exp (-(r * a)))
        (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using!
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := b.re - 1) (b := r)
        (by linarith) (by norm_num) hr)
  apply (integrable_norm_iff hmeas).mp
  apply hreal.congr_fun _ measurableSet_Ioi
  intro a ha
  try dsimp
  rw [norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos ha,
    Complex.norm_exp]
  simp only [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

private theorem gaussianMellinParameter_norm_integral
    (b : ℂ) (hb : 0 < b.re) (r : ℝ) (hr : 0 < r) :
    (∫ a : ℝ in Ioi 0,
      ‖(a : ℂ) ^ (b - 1) *
        Complex.exp (-((r : ℂ) * (a : ℂ)))‖) =
      (1 / r) ^ b.re * Real.Gamma b.re := by
  calc
    (∫ a : ℝ in Ioi 0,
      ‖(a : ℂ) ^ (b - 1) *
        Complex.exp (-((r : ℂ) * (a : ℂ)))‖) =
        ∫ a : ℝ in Ioi 0,
          a ^ (b.re - 1) * Real.exp (-(r * a)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro a ha
      try dsimp
      rw [norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos ha,
        Complex.norm_exp]
      simp only [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
    _ = (1 / r) ^ b.re * Real.Gamma b.re :=
      Real.integral_rpow_mul_exp_neg_mul_Ioi hb hr

private theorem gaussianMellin_inv_sq_rpow
    (r b : ℝ) (hr : 0 ≤ r) :
    (1 / r ^ 2) ^ b = r ^ (-(2 * b)) := by
  calc
    (1 / r ^ 2) ^ b = (r ^ 2) ^ (-b) := by
      rw [one_div, Real.rpow_neg_eq_inv_rpow]
    _ = r ^ ((2 : ℝ) * (-b)) := by
      simpa only [mul_neg, Nat.cast_ofNat] using! (Real.rpow_natCast_mul hr 2 (-b)).symm
    _ = r ^ (-(2 * b)) := by
      congr 1
      ring

private theorem gaussianMellin_inv_sq_cpow
    (r : ℝ) (hr : 0 ≤ r) (b : ℂ) :
    (1 / (((r ^ 2 : ℝ) : ℂ))) ^ b =
      (r : ℂ) ^ (-(2 * b)) := by
  calc
    (1 / (((r ^ 2 : ℝ) : ℂ))) ^ b =
        (((r ^ (-2 : ℝ) : ℝ) : ℂ)) ^ b := by
      rw [Real.rpow_neg hr, Real.rpow_two, Complex.ofReal_inv]
      simp only [one_div]
    _ = (r : ℂ) ^ (((-2 : ℝ) : ℂ) * b) :=
      (Complex.cpow_mul_ofReal_nonneg hr (-2) b).symm
    _ = (r : ℂ) ^ (-(2 * b)) := by
      congr 1
      push_cast
      ring

private theorem gaussianMellin_div_cpow
    (p a : ℝ) (hp : 0 < p) (ha : 0 < a) (b : ℂ) :
    ((p : ℂ) / (a : ℂ)) ^ b =
      (p : ℂ) ^ b * (a : ℂ) ^ (-b) := by
  have hinv :
      (((a⁻¹ : ℝ) : ℂ)) ^ b = (a : ℂ) ^ (-b) := by
    simpa only [Complex.ofReal_inv, Real.rpow_neg_one, Complex.ofReal_neg, Complex.ofReal_one,
      neg_mul,
      one_mul] using!
      (Complex.cpow_mul_ofReal_nonneg ha.le (-1) b).symm
  calc
    ((p : ℂ) / (a : ℂ)) ^ b =
        ((p : ℂ) * (((a⁻¹ : ℝ) : ℂ))) ^ b := by
      rw [Complex.ofReal_inv]
      rfl
    _ = (p : ℂ) ^ b * (((a⁻¹ : ℝ) : ℂ)) ^ b :=
      Complex.mul_cpow_ofReal_nonneg hp.le
        (inv_nonneg.mpr ha.le) b
    _ = (p : ℂ) ^ b * (a : ℂ) ^ (-b) := by
      rw [hinv]

private theorem gaussianMellin_pi_coefficient (b q : ℂ) :
    (Real.pi : ℂ) ^ q *
        (((Real.pi ^ 2 : ℝ) : ℂ) ^ (b - q)) =
      (Real.pi : ℂ) ^ (2 * b - q) := by
  have hsquare :
      (((Real.pi ^ 2 : ℝ) : ℂ) ^ (b - q)) =
        (Real.pi : ℂ) ^ (2 * (b - q)) := by
    simpa only [Complex.ofReal_pow, Real.rpow_ofNat, Complex.ofReal_ofNat] using!
      (Complex.cpow_mul_ofReal_nonneg Real.pi_pos.le
        (2 : ℝ) (b - q)).symm
  rw [hsquare,
    ← Complex.cpow_add _ _
      (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')]
  congr 1
  ring

private noncomputable def gaussianMellinMixture {d : ℕ}
    (f : TestFunction d) (b : ℂ)
    (x : Euclidean d) (a : ℝ) : ℂ :=
  f x *
    ((a : ℂ) ^ (b - 1) *
      Complex.exp (-((‖x‖ : ℂ) ^ 2 * (a : ℂ))))

private theorem gaussianMellinMixture_integrable {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (b : ℂ)
    (hb : 0 < b.re) (hbd : 2 * b.re < (d : ℝ)) :
    Integrable
      (Function.uncurry (gaussianMellinMixture f b))
      ((volume : Measure (Euclidean d)).prod
        (volume.restrict (Ioi (0 : ℝ)))) := by
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hpow : Measurable (fun a : ℝ => (a : ℂ) ^ (b - 1)) := by
    apply measurable_of_continuousOn_compl_singleton (0 : ℝ)
    apply continuousOn_of_forall_continuousAt
    intro a ha
    have hane : a ≠ 0 := by
      simpa only [mem_compl_iff, mem_singleton_iff] using! ha
    exact Complex.continuousAt_ofReal_cpow_const a (b - 1)
      (Or.inr hane)
  have hexp :
      Measurable
        (fun p : Euclidean d × ℝ =>
          Complex.exp
            (-((‖p.1‖ : ℂ) ^ 2 * (p.2 : ℂ)))) := by
    fun_prop
  have hmeas :
      AEStronglyMeasurable
        (Function.uncurry (gaussianMellinMixture f b))
        ((volume : Measure (Euclidean d)).prod
          (volume.restrict (Ioi (0 : ℝ)))) := by
    change
      AEStronglyMeasurable
        (fun p : Euclidean d × ℝ =>
          f p.1 *
            ((p.2 : ℂ) ^ (b - 1) *
              Complex.exp
                (-((‖p.1‖ : ℂ) ^ 2 * (p.2 : ℂ)))))
        _
    exact
      ((f.continuous.measurable.comp measurable_fst).mul
        ((hpow.comp measurable_snd).mul hexp)).aestronglyMeasurable
  apply (integrable_prod_iff hmeas).2
  constructor
  · filter_upwards
      [(volume : Measure (Euclidean d)).ae_ne
        (0 : Euclidean d)] with x hx
    have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hsquare : 0 < ‖x‖ ^ 2 := sq_pos_of_pos hnorm
    simpa only [gaussianMellinMixture, Complex.ofReal_pow] using!
      (gaussianMellinParameter_integrable b hb (‖x‖ ^ 2)
        hsquare).const_mul (f x)
  · have hnegative :
        -(d : ℝ) <
          ((-(2 * b.re) : ℝ) : ℂ).re := by
      simpa only [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.neg_re,
        Complex.mul_re,
        Complex.re_ofNat, Complex.ofReal_re, Complex.im_ofNat, Complex.ofReal_im, mul_zero,
          sub_zero, neg_lt_neg_iff] using! (show -(d : ℝ) < -(2 * b.re) by linarith)
    have hnonpositive :
        ((-(2 * b.re) : ℝ) : ℂ).re ≤ 0 := by
      simpa only [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.neg_re,
        Complex.mul_re,
        Complex.re_ofNat, Complex.ofReal_re, Complex.im_ofNat, Complex.ofReal_im, mul_zero,
          sub_zero, Left.neg_nonpos_iff,
        Nat.ofNat_pos, mul_nonneg_iff_of_pos_left] using! (show -(2 * b.re) ≤ 0 by linarith)
    have hrieszComplex :=
      schwartz_mul_norm_cpow_integrable hd f
        ((-(2 * b.re) : ℝ) : ℂ) hnegative hnonpositive
    have hriesz :
        Integrable
          (fun x : Euclidean d =>
            ‖f x‖ * ‖x‖ ^ (-(2 * b.re)))
          (volume : Measure (Euclidean d)) := by
      apply hrieszComplex.norm.congr
      filter_upwards
        [(volume : Measure (Euclidean d)).ae_ne
          (0 : Euclidean d)] with x hx
      rw [norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos
          (norm_pos_iff.mpr hx)]
      simp only [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.neg_re,
        Complex.mul_re,
        Complex.re_ofNat, Complex.ofReal_re, Complex.im_ofNat, Complex.ofReal_im, mul_zero,
          sub_zero]
    apply (hriesz.mul_const (Real.Gamma b.re)).congr
    filter_upwards
      [(volume : Measure (Euclidean d)).ae_ne
        (0 : Euclidean d)] with x hx
    have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hsquare : 0 < ‖x‖ ^ 2 := sq_pos_of_pos hnorm
    change
      (‖f x‖ * ‖x‖ ^ (-(2 * b.re))) * Real.Gamma b.re =
        ∫ a : ℝ in Ioi 0,
          ‖gaussianMellinMixture f b x a‖
    calc
      (‖f x‖ * ‖x‖ ^ (-(2 * b.re))) * Real.Gamma b.re =
          ‖f x‖ *
            ((1 / ‖x‖ ^ 2) ^ b.re * Real.Gamma b.re) := by
        rw [gaussianMellin_inv_sq_rpow ‖x‖ b.re
          (norm_nonneg x)]
        ring
      _ = ‖f x‖ *
          (∫ a : ℝ in Ioi 0,
            ‖(a : ℂ) ^ (b - 1) *
              Complex.exp
                (-(((‖x‖ ^ 2 : ℝ) : ℂ) * (a : ℂ)))‖) := by
        rw [gaussianMellinParameter_norm_integral
          b hb (‖x‖ ^ 2) hsquare]
      _ = ∫ a : ℝ in Ioi 0,
          ‖f x‖ *
            ‖(a : ℂ) ^ (b - 1) *
              Complex.exp
                (-(((‖x‖ ^ 2 : ℝ) : ℂ) * (a : ℂ)))‖ := by
        rw [integral_const_mul]
      _ = ∫ a : ℝ in Ioi 0,
          ‖gaussianMellinMixture f b x a‖ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro a _
        simp only [gaussianMellinMixture, norm_mul,
          Complex.ofReal_pow]

private theorem gaussianMellinMixture_fubini {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (b : ℂ)
    (hb : 0 < b.re) (hbd : 2 * b.re < (d : ℝ)) :
    (∫ x : Euclidean d,
      ∫ a : ℝ in Ioi 0, gaussianMellinMixture f b x a) =
      ∫ a : ℝ in Ioi 0,
        ∫ x : Euclidean d, gaussianMellinMixture f b x a := by
  exact integral_integral_swap
    (gaussianMellinMixture_integrable hd f b hb hbd)

private theorem gaussianMellinMixture_parameter_integral {d : ℕ}
    (f : TestFunction d) (b : ℂ) (hb : 0 < b.re)
    (x : Euclidean d) (hx : x ≠ 0) :
    (∫ a : ℝ in Ioi 0, gaussianMellinMixture f b x a) =
      f x *
        ((‖x‖ : ℂ) ^ (-(2 * b)) * Complex.Gamma b) := by
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hsquare : 0 < ‖x‖ ^ 2 := sq_pos_of_pos hnorm
  change
    (∫ a : ℝ in Ioi 0,
      f x *
        ((a : ℂ) ^ (b - 1) *
          Complex.exp (-((‖x‖ : ℂ) ^ 2 * (a : ℂ))))) = _
  rw [integral_const_mul]
  have hgamma :=
    Complex.integral_cpow_mul_exp_neg_mul_Ioi hb hsquare
  have hgamma' :
      (∫ a : ℝ in Ioi 0,
        (a : ℂ) ^ (b - 1) *
          Complex.exp (-((‖x‖ : ℂ) ^ 2 * (a : ℂ)))) =
        (1 / (((‖x‖ ^ 2 : ℝ) : ℂ))) ^ b *
          Complex.Gamma b := by
    simpa only [Complex.ofReal_pow] using! hgamma
  rw [hgamma',
    gaussianMellin_inv_sq_cpow ‖x‖ (norm_nonneg x) b]

private noncomputable def gaussianMellinPairingProfile {d : ℕ}
    (f : TestFunction d) (a : ℝ) : ℂ :=
  ∫ x : Euclidean d, f x * gaussianMellinWeight d a x

private theorem mellin_gaussianMellinPairingProfile {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (b : ℂ)
    (hb : 0 < b.re) (hbd : 2 * b.re < (d : ℝ)) :
    mellin (gaussianMellinPairingProfile f) b =
      Complex.Gamma b *
        (∫ x : Euclidean d,
          f x * (‖x‖ : ℂ) ^ (-(2 * b))) := by
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  unfold mellin
  simp only [smul_eq_mul]
  calc
    (∫ a : ℝ in Ioi 0,
      (a : ℂ) ^ (b - 1) * gaussianMellinPairingProfile f a) =
        ∫ a : ℝ in Ioi 0,
          ∫ x : Euclidean d, gaussianMellinMixture f b x a := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro a _
      try dsimp
      unfold gaussianMellinPairingProfile
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [gaussianMellinWeight, gaussianMellinMixture]
      have hexp :
          Complex.exp (-((a : ℂ) * (‖x‖ : ℂ) ^ 2)) =
            Complex.exp (-((‖x‖ : ℂ) ^ 2 * (a : ℂ))) := by
        congr 1
        ring
      rw [hexp]
      ring
    _ = ∫ x : Euclidean d,
          ∫ a : ℝ in Ioi 0,
            gaussianMellinMixture f b x a :=
      (gaussianMellinMixture_fubini hd f b hb hbd).symm
    _ = ∫ x : Euclidean d,
          f x *
            ((‖x‖ : ℂ) ^ (-(2 * b)) * Complex.Gamma b) := by
      apply integral_congr_ae
      filter_upwards
        [(volume : Measure (Euclidean d)).ae_ne
          (0 : Euclidean d)] with x hx
      exact gaussianMellinMixture_parameter_integral
        f b hb x hx
    _ = Complex.Gamma b *
          (∫ x : Euclidean d,
            f x * (‖x‖ : ℂ) ^ (-(2 * b))) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      ring

private theorem gaussianMellinPairingProfile_fourier {d : ℕ}
    (f : TestFunction d) (a : ℝ) (ha : 0 < a) :
    gaussianMellinPairingProfile (𝓕 f : TestFunction d) a =
      ((Real.pi : ℂ) / (a : ℂ)) ^ ((d : ℂ) / 2) *
        gaussianMellinPairingProfile f (Real.pi ^ 2 / a) := by
  unfold gaussianMellinPairingProfile
  rw [fourier_gaussianMellin_pairing f a ha,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  unfold gaussianMellinWeight
  push_cast
  have hexp :
      Complex.exp
          (-((Real.pi : ℂ) ^ 2) * (‖x‖ : ℂ) ^ 2 / (a : ℂ)) =
        Complex.exp
          (-((Real.pi : ℂ) ^ 2 / (a : ℂ) * (‖x‖ : ℂ) ^ 2)) := by
    congr 1
    ring
  rw [hexp]
  ring

private theorem mellin_gaussianMellinPairingProfile_fourier {d : ℕ}
    (f : TestFunction d) (b : ℂ) :
    mellin
        (gaussianMellinPairingProfile (𝓕 f : TestFunction d)) b =
      (Real.pi : ℂ) ^ ((d : ℂ) / 2) *
        (((Real.pi ^ 2 : ℝ) : ℂ) ^
          (b - (d : ℂ) / 2) *
            mellin (gaussianMellinPairingProfile f)
              ((d : ℂ) / 2 - b)) := by
  let q : ℂ := (d : ℂ) / 2
  let P : ℝ := Real.pi ^ 2
  have hP : 0 < P := by
    try dsimp [P]
    positivity
  have hrewrite :
      mellin
          (gaussianMellinPairingProfile
            (𝓕 f : TestFunction d)) b =
        mellin
          (fun a : ℝ =>
            (Real.pi : ℂ) ^ q •
              ((a : ℂ) ^ (-q) •
                gaussianMellinPairingProfile f (P * a⁻¹))) b := by
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro a ha
    simp only [smul_eq_mul]
    rw [gaussianMellinPairingProfile_fourier f a ha]
    change
      (a : ℂ) ^ (b - 1) *
          (((Real.pi : ℂ) / (a : ℂ)) ^ q *
            gaussianMellinPairingProfile f (P / a)) =
        (a : ℂ) ^ (b - 1) *
          ((Real.pi : ℂ) ^ q *
            ((a : ℂ) ^ (-q) *
              gaussianMellinPairingProfile f (P * a⁻¹)))
    rw [gaussianMellin_div_cpow Real.pi a Real.pi_pos ha q,
      div_eq_mul_inv]
    ring
  calc
    mellin
        (gaussianMellinPairingProfile
          (𝓕 f : TestFunction d)) b =
        mellin
          (fun a : ℝ =>
            (Real.pi : ℂ) ^ q •
              ((a : ℂ) ^ (-q) •
                gaussianMellinPairingProfile f (P * a⁻¹))) b :=
      hrewrite
    _ = (Real.pi : ℂ) ^ q *
          mellin
            (fun a : ℝ =>
              (a : ℂ) ^ (-q) •
                gaussianMellinPairingProfile f (P * a⁻¹)) b := by
      simpa only [smul_eq_mul] using!
        (mellin_const_smul
          (fun a : ℝ =>
            (a : ℂ) ^ (-q) •
              gaussianMellinPairingProfile f (P * a⁻¹))
          b ((Real.pi : ℂ) ^ q))
    _ = (Real.pi : ℂ) ^ q *
          mellin
            (fun a : ℝ =>
              gaussianMellinPairingProfile f (P * a⁻¹))
            (b - q) := by
      rw [mellin_cpow_smul]
      simp only [sub_eq_add_neg]
    _ = (Real.pi : ℂ) ^ q *
          mellin
            (fun a : ℝ => gaussianMellinPairingProfile f (P * a))
            (-(b - q)) := by
      rw [mellin_comp_inv
        (fun a : ℝ => gaussianMellinPairingProfile f (P * a))
        (b - q)]
    _ = (Real.pi : ℂ) ^ q *
          ((P : ℂ) ^ (b - q) *
            mellin (gaussianMellinPairingProfile f) (q - b)) := by
      rw [mellin_comp_mul_left
        (gaussianMellinPairingProfile f) (-(b - q)) hP]
      simp only [smul_eq_mul, neg_sub]
    _ = (Real.pi : ℂ) ^ ((d : ℂ) / 2) *
          (((Real.pi ^ 2 : ℝ) : ℂ) ^
            (b - (d : ℂ) / 2) *
              mellin (gaussianMellinPairingProfile f)
                ((d : ℂ) / 2 - b)) := by
      rfl

private theorem fourier_riesz_pairing {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (b : ℂ)
    (hb : 0 < b.re) (hbd : 2 * b.re < (d : ℝ)) :
    Complex.Gamma b *
        (∫ ξ : Euclidean d,
          (𝓕 f : TestFunction d) ξ *
            (‖ξ‖ : ℂ) ^ (-(2 * b))) =
      (Real.pi : ℂ) ^ ((d : ℂ) / 2) *
        (((Real.pi ^ 2 : ℝ) : ℂ) ^
          (b - (d : ℂ) / 2) *
            (Complex.Gamma ((d : ℂ) / 2 - b) *
              (∫ x : Euclidean d,
                f x *
                  (‖x‖ : ℂ) ^
                    (-(2 * ((d : ℂ) / 2 - b)))))) := by
  have hdual : 0 < (((d : ℂ) / 2 - b).re) := by
    norm_num
    linarith
  have hdual_dimension :
      2 * (((d : ℂ) / 2 - b).re) < (d : ℝ) := by
    norm_num
    linarith
  calc
    Complex.Gamma b *
        (∫ ξ : Euclidean d,
          (𝓕 f : TestFunction d) ξ *
            (‖ξ‖ : ℂ) ^ (-(2 * b))) =
          mellin
            (gaussianMellinPairingProfile
              (𝓕 f : TestFunction d)) b :=
      (mellin_gaussianMellinPairingProfile
        hd (𝓕 f : TestFunction d) b hb hbd).symm
    _ = (Real.pi : ℂ) ^ ((d : ℂ) / 2) *
          (((Real.pi ^ 2 : ℝ) : ℂ) ^
            (b - (d : ℂ) / 2) *
              mellin (gaussianMellinPairingProfile f)
                ((d : ℂ) / 2 - b)) :=
      mellin_gaussianMellinPairingProfile_fourier f b
    _ = (Real.pi : ℂ) ^ ((d : ℂ) / 2) *
          (((Real.pi ^ 2 : ℝ) : ℂ) ^
            (b - (d : ℂ) / 2) *
              (Complex.Gamma ((d : ℂ) / 2 - b) *
                (∫ x : Euclidean d,
                  f x *
                    (‖x‖ : ℂ) ^
                      (-(2 * ((d : ℂ) / 2 - b)))))) := by
      rw [mellin_gaussianMellinPairingProfile hd f
        ((d : ℂ) / 2 - b) hdual hdual_dimension]

private theorem fourier_riesz_pairing_strip {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (s : ℂ)
    (hs : 0 < s.re) (hsd : s.re < (d : ℝ)) :
    Complex.Gamma (((d : ℂ) - s) / 2) *
        (∫ ξ : Euclidean d,
          (𝓕 f : TestFunction d) ξ *
            (‖ξ‖ : ℂ) ^ (s - (d : ℂ))) =
      (Real.pi : ℂ) ^ ((d : ℂ) / 2 - s) *
        (Complex.Gamma (s / 2) *
          (∫ x : Euclidean d,
            f x * (‖x‖ : ℂ) ^ (-s))) := by
  let b : ℂ := ((d : ℂ) - s) / 2
  have hb : 0 < b.re := by
    try dsimp [b]
    norm_num
    linarith
  have hbd : 2 * b.re < (d : ℝ) := by
    try dsimp [b]
    norm_num
    linarith
  have hleft : -(2 * b) = s - (d : ℂ) := by
    try dsimp [b]
    ring
  have hdual : (d : ℂ) / 2 - b = s / 2 := by
    try dsimp [b]
    ring
  have hpi :
      2 * b - (d : ℂ) / 2 = (d : ℂ) / 2 - s := by
    try dsimp [b]
    ring
  have hright : -(2 * (s / 2)) = -s := by
    ring
  have h := fourier_riesz_pairing hd f b hb hbd
  rw [← mul_assoc] at h
  rw [gaussianMellin_pi_coefficient b ((d : ℂ) / 2),
    hleft, hdual, hpi, hright] at h
  simpa only [b] using! h

private theorem radial_fourier_mellin_strip {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (s : ℂ) (hs : 0 < s.re) (hsd : s.re < (d : ℝ)) :
    mellin (radialProfile hd (𝓕 f : TestFunction d)) s =
      ((Real.pi : ℂ) ^ ((d : ℂ) / 2 - s) *
        Complex.Gamma (s / 2) /
          Complex.Gamma (((d : ℂ) - s) / 2)) *
            mellin (radialProfile hd f) ((d : ℂ) - s) := by
  have hdual : 0 < ((((d : ℂ) - s) / 2).re) := by
    norm_num
    linarith
  have hgamma :
      Complex.Gamma (((d : ℂ) - s) / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hdual
  have hsurface : (radialSurfaceArea d : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (radialSurfaceArea_pos hd).ne'
  have hhat :=
    integral_radialProfile_cpow hd
      (𝓕 f : TestFunction d)
      (gaussianMellin_fourier_radial hf) s
  have hprimal :
      (∫ x : Euclidean d,
        f x * (‖x‖ : ℂ) ^ (-s)) =
        radialSurfaceArea d •
          mellin (radialProfile hd f) ((d : ℂ) - s) := by
    have hexponent :
        ((d : ℂ) - s) - (d : ℂ) = -s := by
      ring
    simpa only [hexponent] using!
      (integral_radialProfile_cpow hd f hf ((d : ℂ) - s))
  have h := fourier_riesz_pairing_strip hd f s hs hsd
  rw [hhat, hprimal] at h
  simp only [Complex.real_smul] at h
  have hcancel :
      Complex.Gamma (((d : ℂ) - s) / 2) *
          mellin (radialProfile hd (𝓕 f : TestFunction d)) s =
        (Real.pi : ℂ) ^ ((d : ℂ) / 2 - s) *
          (Complex.Gamma (s / 2) *
            mellin (radialProfile hd f) ((d : ℂ) - s)) := by
    apply mul_left_cancel₀ hsurface
    calc
      (radialSurfaceArea d : ℂ) *
          (Complex.Gamma (((d : ℂ) - s) / 2) *
            mellin (radialProfile hd (𝓕 f : TestFunction d)) s) =
          Complex.Gamma (((d : ℂ) - s) / 2) *
            ((radialSurfaceArea d : ℂ) *
              mellin (radialProfile hd (𝓕 f : TestFunction d)) s) := by
        ring
      _ = (Real.pi : ℂ) ^ ((d : ℂ) / 2 - s) *
            (Complex.Gamma (s / 2) *
              ((radialSurfaceArea d : ℂ) *
                mellin (radialProfile hd f) ((d : ℂ) - s))) := h
      _ = (radialSurfaceArea d : ℂ) *
            ((Real.pi : ℂ) ^ ((d : ℂ) / 2 - s) *
              (Complex.Gamma (s / 2) *
                mellin (radialProfile hd f) ((d : ℂ) - s))) := by
        ring
  calc
    mellin (radialProfile hd (𝓕 f : TestFunction d)) s =
        ((Real.pi : ℂ) ^ ((d : ℂ) / 2 - s) *
          (Complex.Gamma (s / 2) *
            mellin (radialProfile hd f) ((d : ℂ) - s))) /
            Complex.Gamma (((d : ℂ) - s) / 2) := by
      apply (eq_div_iff hgamma).2
      simpa only [mul_comm] using! hcancel
    _ = ((Real.pi : ℂ) ^ ((d : ℂ) / 2 - s) *
          Complex.Gamma (s / 2) /
            Complex.Gamma (((d : ℂ) - s) / 2)) *
              mellin (radialProfile hd f) ((d : ℂ) - s) := by
      ring

private theorem radialMellinMultiplier {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (t : ℝ) :
    radialMellinFrequency hd (𝓕 f : TestFunction d) t =
      mellinMultiplier ((d : ℝ) / 2) t *
        radialMellinFrequency hd f (-t) := by
  let q : ℂ := (d : ℂ) / 2
  let s : ℂ := q - Complex.I * (t : ℂ)
  have hs : 0 < s.re := by
    try dsimp [s, q]
    norm_num
    exact Nat.cast_pos.mpr hd
  have hsd : s.re < (d : ℝ) := by
    try dsimp [s, q]
    norm_num
    exact Nat.cast_pos.mpr hd
  have hphase :
      (Real.pi : ℂ) ^ ((d : ℂ) / 2 - s) =
        Complex.exp
          (Complex.I * (t : ℂ) *
            (Real.log Real.pi : ℂ)) := by
    have hexponent :
        (d : ℂ) / 2 - s = Complex.I * (t : ℂ) := by
      try dsimp [s, q]
      ring
    rw [hexponent,
      Complex.cpow_def_of_ne_zero
        (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'),
      ← Complex.ofReal_log Real.pi_pos.le]
    congr 1
    ring
  have hcomplement :
      (d : ℂ) - s = q + Complex.I * (t : ℂ) := by
    try dsimp [s, q]
    ring
  have h := radial_fourier_mellin_strip hd f hf s hs hsd
  rw [hphase, hcomplement] at h
  unfold radialMellinFrequency mellinFrequency mellinMultiplier
  simpa only [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat,
    Complex.ofReal_neg, mul_neg,
    sub_neg_eq_add] using! h

end

section

open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace Topology

private noncomputable def shellOscillation (B T : ℝ) : ℝ :=
  ∫ a in B..B + 1, (1 - Real.cos (a * T))

private theorem shellOscillation_eq_sinc (B T : ℝ) :
    shellOscillation B T =
      1 - Real.sinc (T / 2) * Real.cos ((B + 1 / 2) * T) := by
  unfold shellOscillation
  by_cases hT : T = 0
  · simp only [hT, mul_zero, Real.cos_zero, sub_self, intervalIntegral.integral_zero, zero_div,
    Real.sinc_zero,
      one_div, mul_one]
  · have hhalf : T / 2 ≠ 0 := by exact div_ne_zero hT (by norm_num)
    have hderiv (a : ℝ) :
        HasDerivAt (fun y : ℝ => y - Real.sin (y * T) / T)
          (1 - Real.cos (a * T)) a := by
      convert! (hasDerivAt_id a).sub
        (((Real.hasDerivAt_sin (a * T)).comp a
          ((hasDerivAt_id a).mul_const T)).div_const T) using 1
      field_simp
    have hint : IntervalIntegrable
        (fun a : ℝ => 1 - Real.cos (a * T)) volume B (B + 1) := by
      have hc : Continuous (fun a : ℝ => 1 - Real.cos (a * T)) := by
        fun_prop
      exact hc.intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun a _ => hderiv a) hint, Real.sinc_of_ne_zero hhalf]
    have hsin :
        Real.sin ((B + 1) * T) - Real.sin (B * T) =
          2 * Real.sin (T / 2) * Real.cos ((B + 1 / 2) * T) := by
      rw [Real.sin_sub_sin]
      congr 2 <;> congr 1 <;> ring
    field_simp
    ring_nf at hsin ⊢
    linarith

private theorem cos_le_quartic {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 * (5 / 96 : ℝ) := by
  have hbound := Real.cos_bound (show |x| ≤ 1 by simpa only [abs_of_nonneg hx0] using! hx1)
  rw [abs_of_nonneg hx0] at hbound
  linarith [(le_abs_self (Real.cos x - (1 - x ^ 2 / 2)))]

private theorem sin_le_quintic {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 96 := by
  have hpoly : Continuous
      (fun t : ℝ => 1 - t ^ 2 / 2 + t ^ 4 * (5 / 96 : ℝ)) := by
    fun_prop
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hx0
    (Real.continuous_cos.intervalIntegrable 0 x)
    (hpoly.intervalIntegrable 0 x)
    (fun t ht => cos_le_quartic ht.1 (ht.2.trans hx1))
  simp only [integral_cos, Real.sin_zero, sub_zero] at hmono
  have hderiv (t : ℝ) :
      HasDerivAt (fun y : ℝ => y - y ^ 3 / 6 + y ^ 5 / 96)
        (1 - t ^ 2 / 2 + t ^ 4 * (5 / 96 : ℝ)) t := by
    convert! ((hasDerivAt_id t).sub
      (((hasDerivAt_id t).pow 3).div_const 6)).add
      (((hasDerivAt_id t).pow 5).div_const 96) using 1; simp only [Nat.cast_ofNat, id,
        Nat.add_one_sub_one, mul_one]; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hderiv t) (hpoly.intervalIntegrable 0 x)] at hmono
  norm_num at hmono
  exact hmono

private theorem sin_le_linear_sub_cubic {x : ℝ}
    (hx0 : 0 ≤ x) (hxhalf : x ≤ (1 / 2 : ℝ)) :
    Real.sin x ≤ x - (4 / 25 : ℝ) * x ^ 3 := by
  have hx1 : x ≤ (1 : ℝ) := by linarith
  have hsin := sin_le_quintic hx0 hx1
  have hsq : x ^ 2 ≤ (1 / 4 : ℝ) := by
    linarith [mul_nonneg hx0 (sub_nonneg.mpr hxhalf)]
  have hcub : 0 ≤ x ^ 3 := pow_nonneg hx0 _
  have hfifth : x ^ 5 ≤ x ^ 3 / 4 := by
    have hprod := mul_nonneg hcub (sub_nonneg.mpr hsq)
    linarith [show x ^ 5 = x ^ 3 * x ^ 2 by ring]
  linarith

private theorem sinc_abs (x : ℝ) : Real.sinc |x| = Real.sinc x := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, Real.sinc_neg]

private theorem sinc_quadratic_gap_nonneg {x : ℝ}
    (hx0 : 0 ≤ x) (hxhalf : x ≤ (1 / 2 : ℝ)) :
    (4 / 25 : ℝ) * x ^ 2 ≤ 1 - |Real.sinc x| := by
  rcases hx0.eq_or_lt with rfl | hxpos
  · norm_num
  have hxpi : x ≤ Real.pi := by
    linarith [Real.pi_gt_three]
  have hsin0 : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hxpos.le hxpi
  rw [Real.sinc_of_ne_zero hxpos.ne',
    abs_of_nonneg (div_nonneg hsin0 hxpos.le)]
  have hsin := sin_le_linear_sub_cubic hxpos.le hxhalf
  have hfrac : Real.sin x / x ≤ 1 - (4 / 25 : ℝ) * x ^ 2 := by
    apply (div_le_iff₀ hxpos).2
    linarith
  linarith

private theorem abs_sinc_le_twentyfour_twentyfive {x : ℝ}
    (hx : (1 / 2 : ℝ) ≤ x) :
    |Real.sinc x| ≤ (24 / 25 : ℝ) := by
  have hxpos : 0 < x := by linarith
  have hhalf : Real.sin (1 / 2 : ℝ) ≤ (12 / 25 : ℝ) := by
    have h := sin_le_quintic (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h ⊢
    linarith
  by_cases hxpi : x ≤ Real.pi
  · have hsin0 := Real.sin_nonneg_of_nonneg_of_le_pi hxpos.le hxpi
    rw [Real.sinc_of_ne_zero hxpos.ne',
      abs_of_nonneg (div_nonneg hsin0 hxpos.le)]
    have hend :
        Real.sin (1 / 2 : ℝ) / (1 / 2 : ℝ) ≤ (24 / 25 : ℝ) := by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1 / 2)).2
      linarith
    rcases hx.eq_or_lt with heq | hlt
    · subst x
      exact hend
    · have hslope := strictConcaveOn_sin_Icc.secant_strict_mono
        (a := (0 : ℝ)) (x := (1 / 2 : ℝ)) (y := x)
        ⟨le_rfl, Real.pi_pos.le⟩
        ⟨by norm_num, by linarith [Real.pi_gt_three]⟩
        ⟨hxpos.le, hxpi⟩
        (by norm_num) hxpos.ne' hlt
      simp only [Real.sin_zero, sub_zero] at hslope
      exact hslope.le.trans hend
  · have hbig : Real.pi ≤ x := le_of_not_ge hxpi
    rw [Real.sinc_of_ne_zero hxpos.ne', abs_div,
      abs_of_nonneg hxpos.le]
    apply (div_le_iff₀ hxpos).2
    have hsin := Real.abs_sin_le_one x
    linarith [Real.pi_gt_three]

private theorem sinc_explicit (T : ℝ) :
    (1 / 25 : ℝ) * min (T ^ 2) 1 ≤
      1 - |Real.sinc (T / 2)| := by
  have hsinc : Real.sinc (T / 2) = Real.sinc (|T| / 2) := by
    rw [← sinc_abs (T / 2)]
    simp only [abs_div, Nat.abs_ofNat]
  by_cases hsmall : |T| ≤ 1
  · have hxhalf : |T| / 2 ≤ (1 / 2 : ℝ) := by linarith
    have hgap := sinc_quadratic_gap_nonneg
      (x := |T| / 2) (by positivity) hxhalf
    have hsq : T ^ 2 ≤ (1 : ℝ) := by
      have habsq : |T| ^ 2 ≤ (1 : ℝ) := by
        linarith [mul_nonneg (abs_nonneg T) (sub_nonneg.mpr hsmall)]
      simpa only [sq_abs] using! habsq
    have hscaled :
        (4 / 25 : ℝ) * (|T| / 2) ^ 2 =
          (1 / 25 : ℝ) * T ^ 2 := by
      rw [div_pow, sq_abs]
      ring
    rw [min_eq_left hsq, hsinc]
    rwa [← hscaled]
  · have hlarge : 1 ≤ |T| := le_of_not_ge hsmall
    have hsq : (1 : ℝ) ≤ T ^ 2 := by
      have habsq : (1 : ℝ) ≤ |T| ^ 2 := by
        linarith [sq_nonneg (|T| - 1)]
      simpa only [sq_abs] using! habsq
    have hgap := abs_sinc_le_twentyfour_twentyfive
      (x := |T| / 2) (by linarith)
    rw [min_eq_right hsq, hsinc]
    linarith

private theorem shellOscillation_lower_bound (B T : ℝ) :
    (1 / 25 : ℝ) * min (T ^ 2) 1 ≤ shellOscillation B T := by
  rw [shellOscillation_eq_sinc]
  have hcos := Real.abs_cos_le_one ((B + 1 / 2) * T)
  have hprod :
      Real.sinc (T / 2) * Real.cos ((B + 1 / 2) * T) ≤
        |Real.sinc (T / 2)| := by
    calc
      _ ≤ |Real.sinc (T / 2) * Real.cos ((B + 1 / 2) * T)| :=
        le_abs_self _
      _ = |Real.sinc (T / 2)| * |Real.cos ((B + 1 / 2) * T)| :=
        abs_mul _ _
      _ ≤ |Real.sinc (T / 2)| := by
        nlinarith [abs_nonneg (Real.sinc (T / 2))]
  linarith [sinc_explicit T]

private theorem cosh_ratio_lower {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    Real.exp (δ * a) / 2 ≤
      Real.cosh ((1 + δ) * a) / Real.cosh a := by
  apply (le_div_iff₀ (Real.cosh_pos a)).2
  rw [show (1 + δ) * a = a + δ * a by ring, Real.cosh_add]
  have hq : Real.exp (δ * a) / 2 ≤ Real.cosh (δ * a) := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-(δ * a))]
  calc
    Real.exp (δ * a) / 2 * Real.cosh a =
        Real.cosh a * (Real.exp (δ * a) / 2) := by ring
    _ ≤ Real.cosh a * Real.cosh (δ * a) := by
      exact mul_le_mul_of_nonneg_left hq (Real.cosh_pos a).le
    _ ≤ Real.cosh a * Real.cosh (δ * a) +
          Real.sinh a * Real.sinh (δ * a) := by
      apply le_add_of_nonneg_right
      exact mul_nonneg (Real.sinh_nonneg_iff.mpr ha)
        (Real.sinh_nonneg_iff.mpr (mul_nonneg hδ ha))

private theorem cosh_ratio_upper {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    Real.cosh ((1 + δ) * a) / Real.cosh a ≤ Real.exp (δ * a) := by
  apply (div_le_iff₀ (Real.cosh_pos a)).2
  rw [show (1 + δ) * a = a + δ * a by ring, Real.cosh_add]
  have hs : Real.sinh a ≤ Real.cosh a :=
    (Real.sinh_lt_cosh (x := a)).le
  have hq : 0 ≤ Real.sinh (δ * a) :=
    Real.sinh_nonneg_iff.mpr (mul_nonneg hδ ha)
  calc
    Real.cosh a * Real.cosh (δ * a) +
        Real.sinh a * Real.sinh (δ * a)
      ≤ Real.cosh a * Real.cosh (δ * a) +
          Real.cosh a * Real.sinh (δ * a) := by gcongr
    _ = Real.cosh a *
          (Real.cosh (δ * a) + Real.sinh (δ * a)) := by ring
    _ = Real.exp (δ * a) * Real.cosh a := by
      rw [Real.cosh_eq (δ * a), Real.sinh_eq (δ * a)]
      ring

private noncomputable def positiveShellDensity (ε a : ℝ) : ℝ :=
  shellWeight ε / Real.cosh a

private noncomputable def positiveShellDamping (ε ℓ δ T : ℝ) : ℝ :=
  ℓ * ∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
    positiveShellDensity ε a * Real.cosh ((1 + δ) * a) *
      (1 - Real.cos (a * T))

private theorem positiveShellDamping_lower_bound {ε ℓ δ T : ℝ}
    (hε : 0 < ε) (hℓ : 0 ≤ ℓ) (hδ : 0 ≤ δ) :
    ℓ / 50 * shellWeight ε *
        Real.exp (δ * (ε⁻¹ ^ 3)) * min (T ^ 2) 1 ≤
      positiveShellDamping ε ℓ δ T := by
  let B : ℝ := (ε⁻¹ ^ 3)
  let C : ℝ := shellWeight ε * Real.exp (δ * B) / 2
  have hB : 0 ≤ B := by
    try dsimp [B]
    positivity
  have hQ : 0 < shellWeight ε := shellWeight_pos ε
  have hC : 0 ≤ C := by
    try dsimp [C]
    positivity
  have hden : Continuous (fun a : ℝ => positiveShellDensity ε a) := by
    unfold positiveShellDensity
    exact continuous_const.div Real.continuous_cosh
      (fun a => (Real.cosh_pos a).ne')
  have hosc : Continuous (fun a : ℝ => 1 - Real.cos (a * T)) := by
    fun_prop
  have hleft : Continuous
      (fun a : ℝ => C * (1 - Real.cos (a * T))) :=
    continuous_const.mul hosc
  have hcosh : Continuous (fun a : ℝ => Real.cosh ((1 + δ) * a)) := by
    fun_prop
  have hright : Continuous
      (fun a : ℝ => positiveShellDensity ε a *
        Real.cosh ((1 + δ) * a) * (1 - Real.cos (a * T))) :=
    (hden.mul hcosh).mul hosc
  have hpoint : ∀ a ∈ Set.Icc B (B + 1),
      C * (1 - Real.cos (a * T)) ≤
        positiveShellDensity ε a * Real.cosh ((1 + δ) * a) *
          (1 - Real.cos (a * T)) := by
    intro a ha
    have ha0 : 0 ≤ a := hB.trans ha.1
    have he := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left ha.1 hδ)
    have hratio := cosh_ratio_lower ha0 hδ
    have hbase :
        C ≤ positiveShellDensity ε a * Real.cosh ((1 + δ) * a) := by
      try dsimp [C, positiveShellDensity]
      calc
        shellWeight ε * Real.exp (δ * B) / 2
          ≤ shellWeight ε * Real.exp (δ * a) / 2 := by gcongr
        _ ≤ shellWeight ε *
            (Real.cosh ((1 + δ) * a) / Real.cosh a) := by
          calc
            shellWeight ε * Real.exp (δ * a) / 2 =
              shellWeight ε * (Real.exp (δ * a) / 2) := by ring
            _ ≤ shellWeight ε *
              (Real.cosh ((1 + δ) * a) / Real.cosh a) := by
                exact mul_le_mul_of_nonneg_left hratio hQ.le
        _ = shellWeight ε / Real.cosh a *
              Real.cosh ((1 + δ) * a) := by ring
    exact mul_le_mul_of_nonneg_right hbase
      (sub_nonneg.mpr (Real.cos_le_one _))
  have hmono := intervalIntegral.integral_mono_on
    (μ := volume) (show B ≤ B + 1 by linarith)
    (hleft.intervalIntegrable _ _)
    (hright.intervalIntegrable _ _) hpoint
  have hleftIntegral :
      (∫ a in B..B + 1, C * (1 - Real.cos (a * T))) =
        C * shellOscillation B T := by
    rw [intervalIntegral.integral_const_mul]
    rfl
  rw [hleftIntegral] at hmono
  change ℓ / 50 * shellWeight ε * Real.exp (δ * B) *
      min (T ^ 2) 1 ≤
    ℓ * ∫ a in B..B + 1,
      positiveShellDensity ε a * Real.cosh ((1 + δ) * a) *
        (1 - Real.cos (a * T))
  calc
    ℓ / 50 * shellWeight ε * Real.exp (δ * B) * min (T ^ 2) 1 =
      ℓ * (C * ((1 / 25 : ℝ) * min (T ^ 2) 1)) := by
        try dsimp [C]
        ring
    _ ≤ ℓ * (C * shellOscillation B T) := by
      gcongr
      exact shellOscillation_lower_bound B T
    _ ≤ ℓ * ∫ a in B..B + 1,
        positiveShellDensity ε a * Real.cosh ((1 + δ) * a) *
          (1 - Real.cos (a * T)) := by
      gcongr

private noncomputable def positiveShellRadiusContribution (ε : ℝ) : ℝ :=
  ∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
    positiveShellDensity ε a * a *
      Real.sinh ((1 + ε / 4) * a)

private theorem positiveShellRadiusContribution_bounds {ε : ℝ} (hε : 0 < ε) :
    0 ≤ positiveShellRadiusContribution ε ∧
      positiveShellRadiusContribution ε ≤
        ((ε⁻¹ ^ 3) + 1) * shellWeight ε *
          Real.exp ((ε / 4) * ((ε⁻¹ ^ 3) + 1)) := by
  let B : ℝ := (ε⁻¹ ^ 3)
  let δ : ℝ := ε / 4
  let K : ℝ := (B + 1) * shellWeight ε * Real.exp (δ * (B + 1))
  have hB : 0 ≤ B := by
    try dsimp [B]
    positivity
  have hδ : 0 ≤ δ := by
    try dsimp [δ]
    positivity
  have hQ : 0 < shellWeight ε := shellWeight_pos ε
  have hden : Continuous (fun a : ℝ => positiveShellDensity ε a) := by
    unfold positiveShellDensity
    exact continuous_const.div Real.continuous_cosh
      (fun a => (Real.cosh_pos a).ne')
  have hright : Continuous
      (fun a : ℝ => positiveShellDensity ε a * a *
        Real.sinh ((1 + δ) * a)) := by
    have hsinh : Continuous (fun a : ℝ => Real.sinh ((1 + δ) * a)) := by
      fun_prop
    exact (hden.mul continuous_id).mul hsinh
  have hnonneg : ∀ a ∈ Set.Icc B (B + 1),
      0 ≤ positiveShellDensity ε a * a *
        Real.sinh ((1 + δ) * a) := by
    intro a ha
    have ha0 : 0 ≤ a := hB.trans ha.1
    have hden0 : 0 ≤ positiveShellDensity ε a := by
      unfold positiveShellDensity
      exact (div_pos hQ (Real.cosh_pos a)).le
    exact mul_nonneg (mul_nonneg hden0 ha0)
      (Real.sinh_nonneg_iff.mpr
        (mul_nonneg (by linarith : 0 ≤ 1 + δ) ha0))
  have hpoint : ∀ a ∈ Set.Icc B (B + 1),
      positiveShellDensity ε a * a * Real.sinh ((1 + δ) * a) ≤ K := by
    intro a ha
    have ha0 : 0 ≤ a := hB.trans ha.1
    have hden0 : 0 ≤ positiveShellDensity ε a := by
      unfold positiveShellDensity
      exact (div_pos hQ (Real.cosh_pos a)).le
    have hratio := cosh_ratio_upper ha0 hδ
    have he := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left ha.2 hδ)
    calc
      positiveShellDensity ε a * a * Real.sinh ((1 + δ) * a)
        ≤ positiveShellDensity ε a * a *
          Real.cosh ((1 + δ) * a) := by
            gcongr
            exact (Real.sinh_lt_cosh (x := (1 + δ) * a)).le
      _ = shellWeight ε * a *
          (Real.cosh ((1 + δ) * a) / Real.cosh a) := by
            unfold positiveShellDensity
            ring
      _ ≤ shellWeight ε * (B + 1) *
          Real.exp (δ * (B + 1)) := by
            gcongr
            · exact ha.2
            · exact hratio.trans he
      _ = K := by
            try dsimp [K]
            ring
  constructor
  · change 0 ≤ ∫ a in B..B + 1,
        positiveShellDensity ε a * a * Real.sinh ((1 + δ) * a)
    exact intervalIntegral.integral_nonneg (by linarith) hnonneg
  · change (∫ a in B..B + 1,
        positiveShellDensity ε a * a * Real.sinh ((1 + δ) * a)) ≤ K
    have hmono := intervalIntegral.integral_mono_on (μ := volume)
      (show B ≤ B + 1 by linarith)
      (hright.intervalIntegrable _ _)
      ((continuous_const : Continuous (fun _ : ℝ => K)).intervalIntegrable _ _)
      hpoint
    simpa only [ge_iff_le, intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul,
      one_mul] using! hmono

private noncomputable def shortShellDensity (ε a : ℝ) : ℝ :=
  -((1 - 10 * ε * (1 + a)) * Real.exp (-2 * a) /
    (2 * a ^ 2 * Real.cosh a))

private noncomputable def mellinShellPhase (ε : ℝ) (z : ℂ) : ℂ :=
  (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
    (shortShellDensity ε a : ℂ) *
      (Complex.cos ((a : ℂ) * z) - 1)) +
  (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
    (positiveShellDensity ε a : ℂ) *
      (Complex.cos ((a : ℂ) * z) - 1))

private theorem mellinShellPhase_neg (ε : ℝ) (z : ℂ) :
    mellinShellPhase ε (-z) = mellinShellPhase ε z := by
  unfold mellinShellPhase
  congr 1
  · apply intervalIntegral.integral_congr
    intro a _
    simp only [mul_neg, Complex.cos_neg]
  · apply intervalIntegral.integral_congr
    intro a _
    simp only [mul_neg, Complex.cos_neg]

private noncomputable def realOscillatoryShellPhase (ε t : ℝ) : ℝ :=
  (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
    shortShellDensity ε a * (Real.cos (a * t) - 1)) +
  (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
    positiveShellDensity ε a * (Real.cos (a * t) - 1))

private noncomputable def realHyperbolicShellPhase (ε u : ℝ) : ℝ :=
  (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
    shortShellDensity ε a * (Real.cosh (a * u) - 1)) +
  (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
    positiveShellDensity ε a * (Real.cosh (a * u) - 1))

private theorem mellinShellPhase_ofReal (ε t : ℝ) :
    mellinShellPhase ε (t : ℂ) =
      (realOscillatoryShellPhase ε t : ℂ) := by
  unfold mellinShellPhase realOscillatoryShellPhase
  push_cast
  congr 1
  · calc
      (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
        (shortShellDensity ε a : ℂ) *
          (Complex.cos ((a : ℂ) * (t : ℂ)) - 1)) =
          ∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
            (↑(shortShellDensity ε a *
              (Real.cos (a * t) - 1)) : ℂ) := by
              apply intervalIntegral.integral_congr
              intro a _
              try dsimp
              rw [show (a : ℂ) * (t : ℂ) =
                ((a * t : ℝ) : ℂ) by
                  push_cast
                  rfl,
                ← Complex.ofReal_cos]
              push_cast
              rfl
      _ = (↑(∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
            shortShellDensity ε a * (Real.cos (a * t) - 1)) : ℂ) :=
          intervalIntegral.integral_ofReal
  · calc
      (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
        (positiveShellDensity ε a : ℂ) *
          (Complex.cos ((a : ℂ) * (t : ℂ)) - 1)) =
          ∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
            (↑(positiveShellDensity ε a *
              (Real.cos (a * t) - 1)) : ℂ) := by
              apply intervalIntegral.integral_congr
              intro a _
              try dsimp
              rw [show (a : ℂ) * (t : ℂ) =
                ((a * t : ℝ) : ℂ) by
                  push_cast
                  rfl,
                ← Complex.ofReal_cos]
              push_cast
              rfl
      _ = (↑(∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
            positiveShellDensity ε a * (Real.cos (a * t) - 1)) : ℂ) :=
          intervalIntegral.integral_ofReal

private theorem mellinShellPhase_imaginary (ε u : ℝ) :
    mellinShellPhase ε (Complex.I * (u : ℂ)) =
      (realHyperbolicShellPhase ε u : ℂ) := by
  unfold mellinShellPhase realHyperbolicShellPhase
  push_cast
  congr 1
  · calc
      (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
        (shortShellDensity ε a : ℂ) *
          (Complex.cos ((a : ℂ) * (Complex.I * (u : ℂ))) - 1)) =
          ∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
            (↑(shortShellDensity ε a *
              (Real.cosh (a * u) - 1)) : ℂ) := by
              apply intervalIntegral.integral_congr
              intro a _
              try dsimp
              rw [show (a : ℂ) * (Complex.I * (u : ℂ)) =
                ((a * u : ℝ) : ℂ) * Complex.I by
                  push_cast
                  ring,
                Complex.cos_mul_I, ← Complex.ofReal_cosh]
              push_cast
              rfl
      _ = (↑(∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
            shortShellDensity ε a * (Real.cosh (a * u) - 1)) : ℂ) :=
          intervalIntegral.integral_ofReal
  · calc
      (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
        (positiveShellDensity ε a : ℂ) *
          (Complex.cos ((a : ℂ) * (Complex.I * (u : ℂ))) - 1)) =
          ∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
            (↑(positiveShellDensity ε a *
              (Real.cosh (a * u) - 1)) : ℂ) := by
              apply intervalIntegral.integral_congr
              intro a _
              try dsimp
              rw [show (a : ℂ) * (Complex.I * (u : ℂ)) =
                ((a * u : ℝ) : ℂ) * Complex.I by
                  push_cast
                  ring,
                Complex.cos_mul_I, ← Complex.ofReal_cosh]
              push_cast
              rfl
      _ = (↑(∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
            positiveShellDensity ε a * (Real.cosh (a * u) - 1)) : ℂ) :=
          intervalIntegral.integral_ofReal

private theorem realHyperbolicShellPhase_neg (ε u : ℝ) :
    realHyperbolicShellPhase ε (-u) =
      realHyperbolicShellPhase ε u := by
  unfold realHyperbolicShellPhase
  congr 1
  · apply intervalIntegral.integral_congr
    intro a _
    change
      shortShellDensity ε a * (Real.cosh (a * (-u)) - 1) =
        shortShellDensity ε a * (Real.cosh (a * u) - 1)
    rw [mul_neg, Real.cosh_neg]
  · apply intervalIntegral.integral_congr
    intro a _
    change
      positiveShellDensity ε a * (Real.cosh (a * (-u)) - 1) =
        positiveShellDensity ε a * (Real.cosh (a * u) - 1)
    rw [mul_neg, Real.cosh_neg]

private theorem positiveShellDensity_continuous (ε : ℝ) :
    Continuous (positiveShellDensity ε) := by
  unfold positiveShellDensity
  exact continuous_const.div Real.continuous_cosh
    (fun a => (Real.cosh_pos a).ne')

private theorem shortShellDensity_intervalIntegrable {ε : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    IntervalIntegrable (shortShellDensity ε) volume
      (ε ^ 3) (10 * Real.log (1 / ε)) := by
  have hn : Continuous (fun a : ℝ =>
      (1 - 10 * ε * (1 + a)) * Real.exp (-2 * a)) := by
    fun_prop
  have hd : Continuous (fun a : ℝ =>
      2 * a ^ 2 * Real.cosh a) := by
    fun_prop
  apply ContinuousOn.intervalIntegrable_of_Icc horder
  unfold shortShellDensity
  apply (hn.continuousOn.div hd.continuousOn ?_).neg
  intro a ha
  have hcutoff : 0 < (ε ^ 3) := by
    positivity
  have ha0 : 0 < a := hcutoff.trans_le ha.1
  positivity

private theorem shortShellOscillatoryIntegral_continuous {ε : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    Continuous (fun t : ℝ =>
      ∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
        shortShellDensity ε a * (Real.cos (a * t) - 1)) := by
  have hcutoff : 0 < (ε ^ 3) := by
    positivity
  let w : ℝ → ℝ := fun a =>
    shortShellDensity ε (max a (ε ^ 3))
  have hmax (a : ℝ) : 0 < max a (ε ^ 3) :=
    hcutoff.trans_le (le_max_right _ _)
  have hw : Continuous w := by
    have hn : Continuous (fun a : ℝ =>
        (1 - 10 * ε * (1 + (max a (ε ^ 3)))) *
          Real.exp (-2 * max a (ε ^ 3))) := by
      fun_prop
    have hd : Continuous (fun a : ℝ =>
        2 * (max a (ε ^ 3)) ^ 2 *
          Real.cosh (max a (ε ^ 3))) := by
      fun_prop
    try dsimp [w]
    unfold shortShellDensity
    exact (hn.div hd (fun a => by positivity [hmax a])).neg
  let F : ℝ → ℝ → ℝ := fun t a =>
    w a * (Real.cos (a * t) - 1)
  have hF : Continuous (Function.uncurry F) := by
    try dsimp [F, Function.uncurry]
    exact (hw.comp continuous_snd).mul (by fun_prop)
  have hparam : Continuous (fun t : ℝ =>
      ∫ a in Set.Icc (ε ^ 3) (10 * Real.log (1 / ε)), F t a) :=
    continuous_parametric_integral_of_continuous
      (μ := volume) hF isCompact_Icc
  have hident (t : ℝ) :
      (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
        shortShellDensity ε a * (Real.cos (a * t) - 1)) =
      (∫ a in Set.Icc (ε ^ 3) (10 * Real.log (1 / ε)), F t a) := by
    rw [intervalIntegral.integral_of_le horder,
      ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro a ha
    try dsimp [F, w]
    rw [max_eq_left ha.1]
  exact hparam.congr (fun t => (hident t).symm)

private theorem positiveShellOscillatoryIntegral_continuous (ε : ℝ) :
    Continuous (fun t : ℝ =>
      ∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
        positiveShellDensity ε a * (Real.cos (a * t) - 1)) := by
  let F : ℝ → ℝ → ℝ := fun t a =>
    positiveShellDensity ε a * (Real.cos (a * t) - 1)
  have hF : Continuous (Function.uncurry F) := by
    try dsimp [F, Function.uncurry]
    exact ((positiveShellDensity_continuous ε).comp continuous_snd).mul
      (by fun_prop)
  have hparam : Continuous (fun t : ℝ =>
      ∫ a in Set.Icc (ε⁻¹ ^ 3) ((ε⁻¹ ^ 3) + 1), F t a) :=
    continuous_parametric_integral_of_continuous
      (μ := volume) hF isCompact_Icc
  have horder : (ε⁻¹ ^ 3) ≤ (ε⁻¹ ^ 3) + 1 := by
    linarith
  have hident (t : ℝ) :
      (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
        positiveShellDensity ε a * (Real.cos (a * t) - 1)) =
      (∫ a in Set.Icc (ε⁻¹ ^ 3) ((ε⁻¹ ^ 3) + 1),
        F t a) := by
    rw [intervalIntegral.integral_of_le horder,
      ← integral_Icc_eq_integral_Ioc]
  exact hparam.congr (fun t => (hident t).symm)

private theorem realOscillatoryShellPhase_continuous {ε : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    Continuous (realOscillatoryShellPhase ε) := by
  unfold realOscillatoryShellPhase
  exact (shortShellOscillatoryIntegral_continuous hε horder).add
    (positiveShellOscillatoryIntegral_continuous ε)

private theorem complexShellInterval_continuous
    (w : ℝ → ℝ) (hw : Continuous w)
    {a b : ℝ} (hab : a ≤ b) :
    Continuous (fun z : ℂ =>
      ∫ x in a..b,
        (w x : ℂ) * (Complex.cos ((x : ℂ) * z) - 1)) := by
  let F : ℂ → ℝ → ℂ := fun z x =>
    (w x : ℂ) * (Complex.cos ((x : ℂ) * z) - 1)
  have hF : Continuous (Function.uncurry F) := by
    try dsimp [F, Function.uncurry]
    exact (Complex.continuous_ofReal.comp
      (hw.comp continuous_snd)).mul (by fun_prop)
  have hparam : Continuous
      (fun z : ℂ => ∫ x in Set.Icc a b, F z x) :=
    continuous_parametric_integral_of_continuous
      (μ := volume) hF isCompact_Icc
  have hident (z : ℂ) :
      (∫ x in a..b,
        (w x : ℂ) * (Complex.cos ((x : ℂ) * z) - 1)) =
        (∫ x in Set.Icc a b, F z x) := by
    rw [intervalIntegral.integral_of_le hab,
      ← integral_Icc_eq_integral_Ioc]
  exact hparam.congr (fun z => (hident z).symm)

private theorem complexShellInterval_differentiable
    (w : ℝ → ℝ) (hw : Continuous w)
    {a b : ℝ} (hab : a ≤ b) :
    Differentiable ℂ (fun z : ℂ =>
      ∫ x in a..b,
        (w x : ℂ) * (Complex.cos ((x : ℂ) * z) - 1)) := by
  let F : ℂ → ℝ → ℂ := fun z x =>
    (w x : ℂ) * (Complex.cos ((x : ℂ) * z) - 1)
  let F' : ℂ → ℝ → ℂ := fun z x =>
    (w x : ℂ) * (-(Complex.sin ((x : ℂ) * z)) * (x : ℂ))
  have hF (z : ℂ) : Continuous (F z) := by
    try dsimp [F]
    exact (Complex.continuous_ofReal.comp hw).mul (by fun_prop)
  have hF' (z : ℂ) : Continuous (F' z) := by
    try dsimp [F']
    exact (Complex.continuous_ofReal.comp hw).mul (by fun_prop)
  have hF'joint : Continuous (Function.uncurry F') := by
    try dsimp [F', Function.uncurry]
    exact (Complex.continuous_ofReal.comp
      (hw.comp continuous_snd)).mul (by fun_prop)
  have hderiv (x : ℝ) (z : ℂ) :
      HasDerivAt (fun u : ℂ => F u x) (F' z x) z := by
    have hlinear : HasDerivAt
        (fun u : ℂ => (x : ℂ) * u) (x : ℂ) z := by
      simpa only [id_eq, mul_one] using! (hasDerivAt_id z).const_mul (x : ℂ)
    have hcos := (Complex.hasDerivAt_cos
      ((x : ℂ) * z)).comp z hlinear
    simpa [F, F', mul_assoc] using!
      (hcos.sub_const (1 : ℂ)).const_mul (w x : ℂ)
  have hrewrite :
      (fun z : ℂ =>
        ∫ x in a..b,
          (w x : ℂ) * (Complex.cos ((x : ℂ) * z) - 1)) =
        (fun z : ℂ => ∫ x in Set.Icc a b, F z x) := by
    funext z
    rw [intervalIntegral.integral_of_le hab,
      ← integral_Icc_eq_integral_Ioc]
  rw [hrewrite]
  intro z₀
  have hcompact :
      IsCompact (Metric.closedBall z₀ 1 ×ˢ Set.Icc a b) :=
    (isCompact_closedBall z₀ 1).prod isCompact_Icc
  obtain ⟨C, hC⟩ :=
    hcompact.bddAbove_image hF'joint.norm.continuousOn
  have hbound : ∀ᵐ x ∂volume.restrict (Set.Icc a b),
      ∀ z ∈ Metric.ball z₀ 1, ‖F' z x‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    intro z hz
    have hpair :
        (z, x) ∈ Metric.closedBall z₀ 1 ×ˢ Set.Icc a b :=
      ⟨Metric.ball_subset_closedBall hz, hx⟩
    exact hC (Set.mem_image_of_mem
      (fun p : ℂ × ℝ => ‖F' p.1 p.2‖)
      hpair)
  have hmeas : ∀ᶠ z in 𝓝 z₀,
      AEStronglyMeasurable (F z)
        (volume.restrict (Set.Icc a b)) :=
    Eventually.of_forall (fun z => (hF z).aestronglyMeasurable)
  have hint : Integrable (F z₀)
      (volume.restrict (Set.Icc a b)) :=
    (hF z₀).integrableOn_Icc
  have hderivmeas : AEStronglyMeasurable (F' z₀)
      (volume.restrict (Set.Icc a b)) :=
    (hF' z₀).aestronglyMeasurable
  have hconstant : Integrable (fun _ : ℝ => C)
      (volume.restrict (Set.Icc a b)) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hdifferentiable : ∀ᵐ x ∂volume.restrict (Set.Icc a b),
      ∀ z ∈ Metric.ball z₀ 1,
        HasDerivAt (fun u : ℂ => F u x) (F' z x) z :=
    Eventually.of_forall (fun x z _ => hderiv x z)
  exact (_root_.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Icc a b))
    (s := Metric.ball z₀ 1) (bound := fun _ : ℝ => C)
    (Metric.ball_mem_nhds z₀ zero_lt_one)
    hmeas hint hderivmeas hbound hconstant
    hdifferentiable).2.differentiableAt

private theorem mellinShellPhase_continuous {ε : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    Continuous (mellinShellPhase ε) := by
  have hcutoff : 0 < (ε ^ 3) := by
    positivity
  let w : ℝ → ℝ := fun a =>
    shortShellDensity ε (max a (ε ^ 3))
  have hmax (a : ℝ) : 0 < max a (ε ^ 3) :=
    hcutoff.trans_le (le_max_right _ _)
  have hw : Continuous w := by
    have hn : Continuous (fun a : ℝ =>
        (1 - 10 * ε * (1 + (max a (ε ^ 3)))) *
          Real.exp (-2 * max a (ε ^ 3))) := by
      fun_prop
    have hd : Continuous (fun a : ℝ =>
        2 * (max a (ε ^ 3)) ^ 2 *
          Real.cosh (max a (ε ^ 3))) := by
      fun_prop
    try dsimp [w]
    unfold shortShellDensity
    exact (hn.div hd (fun a => by positivity [hmax a])).neg
  have hshort : Continuous (fun z : ℂ =>
      ∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
        (shortShellDensity ε a : ℂ) *
          (Complex.cos ((a : ℂ) * z) - 1)) := by
    apply (complexShellInterval_continuous w hw horder).congr
    intro z
    apply intervalIntegral.integral_congr
    intro a ha
    rw [uIcc_of_le horder] at ha
    try dsimp [w]
    rw [max_eq_left ha.1]
  have hremote : (ε⁻¹ ^ 3) ≤ (ε⁻¹ ^ 3) + 1 := by
    linarith
  have hpositive : Continuous (fun z : ℂ =>
      ∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
        (positiveShellDensity ε a : ℂ) *
          (Complex.cos ((a : ℂ) * z) - 1)) :=
    complexShellInterval_continuous (positiveShellDensity ε)
      (positiveShellDensity_continuous ε) hremote
  exact hshort.add hpositive

private theorem mellinShellPhase_differentiable {ε : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    Differentiable ℂ (mellinShellPhase ε) := by
  have hcutoff : 0 < (ε ^ 3) := by
    positivity
  let w : ℝ → ℝ := fun a =>
    shortShellDensity ε (max a (ε ^ 3))
  have hmax (a : ℝ) : 0 < max a (ε ^ 3) :=
    hcutoff.trans_le (le_max_right _ _)
  have hw : Continuous w := by
    have hn : Continuous (fun a : ℝ =>
        (1 - 10 * ε * (1 + (max a (ε ^ 3)))) *
          Real.exp (-2 * max a (ε ^ 3))) := by
      fun_prop
    have hd : Continuous (fun a : ℝ =>
        2 * (max a (ε ^ 3)) ^ 2 *
          Real.cosh (max a (ε ^ 3))) := by
      fun_prop
    try dsimp [w]
    unfold shortShellDensity
    exact (hn.div hd (fun a => by positivity [hmax a])).neg
  have hshort_eq :
      (fun z : ℂ =>
        ∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
          (shortShellDensity ε a : ℂ) *
            (Complex.cos ((a : ℂ) * z) - 1)) =
      (fun z : ℂ =>
        ∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
          (w a : ℂ) *
            (Complex.cos ((a : ℂ) * z) - 1)) := by
    funext z
    apply intervalIntegral.integral_congr
    intro a ha
    rw [uIcc_of_le horder] at ha
    try dsimp [w]
    rw [max_eq_left ha.1]
  have hshort : Differentiable ℂ (fun z : ℂ =>
      ∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
        (shortShellDensity ε a : ℂ) *
          (Complex.cos ((a : ℂ) * z) - 1)) := by
    rw [hshort_eq]
    exact complexShellInterval_differentiable w hw horder
  have hremote : (ε⁻¹ ^ 3) ≤ (ε⁻¹ ^ 3) + 1 := by
    linarith
  have hpositive : Differentiable ℂ (fun z : ℂ =>
      ∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
        (positiveShellDensity ε a : ℂ) *
          (Complex.cos ((a : ℂ) * z) - 1)) :=
    complexShellInterval_differentiable
      (positiveShellDensity ε)
      (positiveShellDensity_continuous ε) hremote
  exact hshort.add hpositive

private theorem mellinShellPhase_analyticOnNhd {ε : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    AnalyticOnNhd ℂ (mellinShellPhase ε) Set.univ :=
  Complex.analyticOnNhd_univ_iff_differentiable.mpr
    (mellinShellPhase_differentiable hε horder)

private noncomputable def saddleShellTotalVariation (ε : ℝ) : ℝ :=
  (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
    |shortShellDensity ε a|) +
  (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
    |positiveShellDensity ε a|)

private theorem abs_realOscillatoryShellPhase_le {ε : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) (t : ℝ) :
    |realOscillatoryShellPhase ε t| ≤
      2 * saddleShellTotalVariation ε := by
  have hcos (a : ℝ) : |Real.cos (a * t) - 1| ≤ 2 := by
    apply (abs_le).2
    constructor
    · linarith [Real.neg_one_le_cos (a * t)]
    · linarith [Real.cos_le_one (a * t)]
  have hosc : Continuous (fun a : ℝ => Real.cos (a * t) - 1) := by
    fun_prop
  have hs := shortShellDensity_intervalIntegrable hε horder
  have hp : IntervalIntegrable (positiveShellDensity ε) volume
      (ε⁻¹ ^ 3) ((ε⁻¹ ^ 3) + 1) :=
    (positiveShellDensity_continuous ε).intervalIntegrable
      (ε⁻¹ ^ 3) ((ε⁻¹ ^ 3) + 1)
  have hshort :
      |∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
        shortShellDensity ε a * (Real.cos (a * t) - 1)| ≤
          2 * ∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
            |shortShellDensity ε a| := by
    calc
      |∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
          shortShellDensity ε a * (Real.cos (a * t) - 1)|
        ≤ ∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
            |shortShellDensity ε a * (Real.cos (a * t) - 1)| :=
              intervalIntegral.abs_integral_le_integral_abs horder
      _ ≤ ∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
            2 * |shortShellDensity ε a| := by
              apply intervalIntegral.integral_mono_on horder
                (hs.mul_continuousOn hosc.continuousOn).abs
                (hs.abs.const_mul 2)
              intro a _
              rw [abs_mul]
              calc
                |shortShellDensity ε a| *
                    |Real.cos (a * t) - 1|
                  ≤ |shortShellDensity ε a| * 2 := by
                      gcongr
                      exact hcos a
                _ = 2 * |shortShellDensity ε a| := by ring
      _ = 2 * ∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
            |shortShellDensity ε a| := by
              rw [intervalIntegral.integral_const_mul]
  have hpositive :
      |∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
        positiveShellDensity ε a * (Real.cos (a * t) - 1)| ≤
          2 * ∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
            |positiveShellDensity ε a| := by
    have hB : (ε⁻¹ ^ 3) ≤ (ε⁻¹ ^ 3) + 1 := by
      linarith
    calc
      |∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
          positiveShellDensity ε a * (Real.cos (a * t) - 1)|
        ≤ ∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
            |positiveShellDensity ε a * (Real.cos (a * t) - 1)| :=
              intervalIntegral.abs_integral_le_integral_abs hB
      _ ≤ ∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
            2 * |positiveShellDensity ε a| := by
              apply intervalIntegral.integral_mono_on hB
                (hp.mul_continuousOn hosc.continuousOn).abs
                (hp.abs.const_mul 2)
              intro a _
              rw [abs_mul]
              calc
                |positiveShellDensity ε a| *
                    |Real.cos (a * t) - 1|
                  ≤ |positiveShellDensity ε a| * 2 := by
                      gcongr
                      exact hcos a
                _ = 2 * |positiveShellDensity ε a| := by ring
      _ = 2 * ∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
            |positiveShellDensity ε a| := by
              rw [intervalIntegral.integral_const_mul]
  unfold realOscillatoryShellPhase saddleShellTotalVariation
  calc
    |(∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
        shortShellDensity ε a * (Real.cos (a * t) - 1)) +
      (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
        positiveShellDensity ε a * (Real.cos (a * t) - 1))|
      ≤ |∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
          shortShellDensity ε a * (Real.cos (a * t) - 1)| +
        |∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
          positiveShellDensity ε a * (Real.cos (a * t) - 1)| :=
          abs_add_le _ _
    _ ≤ 2 * (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
          |shortShellDensity ε a|) +
        2 * (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
          |positiveShellDensity ε a|) :=
          add_le_add hshort hpositive
    _ = 2 * ((∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
          |shortShellDensity ε a|) +
        (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
          |positiveShellDensity ε a|)) := by ring

private theorem mellinShellPhase_real_conj (ε t : ℝ) :
    starRingEnd ℂ (mellinShellPhase ε (t : ℂ)) =
      mellinShellPhase ε (t : ℂ) := by
  rw [mellinShellPhase_ofReal]
  exact Complex.conj_ofReal _

private noncomputable def saddleEnvelope (ε ℓ t : ℝ) : ℂ :=
  Complex.exp
      (Complex.I * (t : ℂ) * (Real.log Real.pi : ℂ) / 2) *
    Complex.Gamma (((ℓ : ℂ) - Complex.I * (t : ℂ)) / 2) *
    Complex.exp ((ℓ : ℂ) *
      mellinShellPhase ε ((t : ℂ) / (ℓ : ℂ)))

private noncomputable def plusSaddleSpectrum (ε ℓ t : ℝ) : ℂ :=
  saddleEnvelope ε ℓ t *
    plusPolynomial ε ((t : ℂ) / (ℓ : ℂ))

private noncomputable def minusSaddleSpectrum (ε ℓ t : ℝ) : ℂ :=
  saddleEnvelope ε ℓ t *
    minusPolynomial ε ((t : ℂ) / (ℓ : ℂ))

private theorem saddleVerticalGamma_continuous {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Continuous (fun t : ℝ =>
      Complex.Gamma (((ℓ : ℂ) - Complex.I * (t : ℂ)) / 2)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let z : ℂ := ((ℓ : ℂ) - Complex.I * (t : ℂ)) / 2
  have hz : 0 < z.re := by
    try dsimp [z]
    simpa only [Complex.div_ofNat_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, zero_mul,
      Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, sub_zero, Nat.ofNat_pos,
        div_pos_iff_of_pos_right] using! half_pos hℓ
  have hpoles : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    norm_num at hre
    have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have harg : ContinuousAt
      (fun u : ℝ => ((ℓ : ℂ) - Complex.I * (u : ℂ)) / 2) t :=
    ((continuous_const.sub
      (Complex.continuous_ofReal.const_mul Complex.I)).div_const 2).continuousAt
  simpa only [Function.comp_def] using!
    (Complex.continuousAt_Gamma z hpoles).comp_of_eq harg (by rfl)

private theorem saddleShellPhase_continuous {ε : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) (ℓ : ℝ) :
    Continuous (fun t : ℝ =>
      mellinShellPhase ε ((t : ℂ) / (ℓ : ℂ))) := by
  have hreal : Continuous (fun t : ℝ =>
      realOscillatoryShellPhase ε (t / ℓ)) :=
    (realOscillatoryShellPhase_continuous hε horder).comp
      (by fun_prop)
  have hcomplex : Continuous (fun t : ℝ =>
      (realOscillatoryShellPhase ε (t / ℓ) : ℂ)) :=
    Complex.continuous_ofReal.comp hreal
  apply hcomplex.congr
  intro t
  rw [show (t : ℂ) / (ℓ : ℂ) = ((t / ℓ : ℝ) : ℂ) by
    push_cast
    rfl, mellinShellPhase_ofReal]

private theorem saddleEnvelope_continuous {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    Continuous (saddleEnvelope ε ℓ) := by
  have hunit : Continuous (fun t : ℝ =>
      Complex.exp
        (Complex.I * (t : ℂ) * (Real.log Real.pi : ℂ) / 2)) := by
    fun_prop
  have hgamma := saddleVerticalGamma_continuous hℓ
  have hphase : Continuous (fun t : ℝ =>
      Complex.exp ((ℓ : ℂ) *
        mellinShellPhase ε ((t : ℂ) / (ℓ : ℂ)))) :=
    Complex.continuous_exp.comp
      (continuous_const.mul (saddleShellPhase_continuous
        hε horder ℓ))
  exact (hunit.mul hgamma).mul hphase

private theorem plusSaddleSpectrum_continuous {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    Continuous (plusSaddleSpectrum ε ℓ) := by
  have hp : Continuous (fun t : ℝ =>
      plusPolynomial ε ((t : ℂ) / (ℓ : ℂ))) := by
    unfold plusPolynomial
    fun_prop
  exact (saddleEnvelope_continuous hε hℓ horder).mul hp

private theorem minusSaddleSpectrum_continuous {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    Continuous (minusSaddleSpectrum ε ℓ) := by
  have hp : Continuous (fun t : ℝ =>
      minusPolynomial ε ((t : ℂ) / (ℓ : ℂ))) := by
    unfold minusPolynomial
    fun_prop
  exact (saddleEnvelope_continuous hε hℓ horder).mul hp

private noncomputable def saddleOriginValue (ε ℓ : ℝ) : ℝ :=
  2 * Real.pi ^ (ℓ / 2) *
    Real.exp (ℓ * realHyperbolicShellPhase ε 1) * (ε / 4)

private theorem saddleOriginValue_pos {ε : ℝ} (hε : 0 < ε) (ℓ : ℝ) :
    0 < saddleOriginValue ε ℓ := by
  unfold saddleOriginValue
  positivity [div_pos hε four_pos, Real.pi_pos]

private noncomputable def saddleMellinEnvelope (ε ℓ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp
      (((ℓ : ℂ) - z) * (Real.log Real.pi : ℂ) / 2) *
    Complex.Gamma (z / 2) *
    Complex.exp ((ℓ : ℂ) *
      mellinShellPhase ε
        (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ)))

private noncomputable def plusSaddleMellinData (ε ℓ : ℝ) (z : ℂ) : ℂ :=
  saddleMellinEnvelope ε ℓ z *
    plusPolynomial ε
      (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ))

private noncomputable def minusSaddleMellinData (ε ℓ : ℝ) (z : ℂ) : ℂ :=
  saddleMellinEnvelope ε ℓ z *
    minusPolynomial ε
      (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ))

private noncomputable def saddleRegularMellinFactor (ε ℓ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp
      (((ℓ : ℂ) - z) * (Real.log Real.pi : ℂ) / 2) *
    Complex.exp ((ℓ : ℂ) *
      mellinShellPhase ε
        (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ)))

private noncomputable def plusSaddleRegularMellinFactor (ε ℓ : ℝ) (z : ℂ) : ℂ :=
  saddleRegularMellinFactor ε ℓ z *
    plusPolynomial ε
      (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ))

private noncomputable def minusSaddleRegularMellinFactor (ε ℓ : ℝ) (z : ℂ) : ℂ :=
  saddleRegularMellinFactor ε ℓ z *
    minusPolynomial ε
      (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ))

private theorem plusSaddleMellinData_eq_gamma_mul_regular
    (ε ℓ : ℝ) (z : ℂ) :
    plusSaddleMellinData ε ℓ z =
      Complex.Gamma (z / 2) *
        plusSaddleRegularMellinFactor ε ℓ z := by
  unfold plusSaddleMellinData saddleMellinEnvelope
    plusSaddleRegularMellinFactor saddleRegularMellinFactor
  ring

private theorem minusSaddleMellinData_eq_gamma_mul_regular
    (ε ℓ : ℝ) (z : ℂ) :
    minusSaddleMellinData ε ℓ z =
      Complex.Gamma (z / 2) *
        minusSaddleRegularMellinFactor ε ℓ z := by
  unfold minusSaddleMellinData saddleMellinEnvelope
    minusSaddleRegularMellinFactor saddleRegularMellinFactor
  ring

private theorem saddleRegularMellinFactor_continuous {ε : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) (ℓ : ℝ) :
    Continuous (saddleRegularMellinFactor ε ℓ) := by
  have hpi : Continuous (fun z : ℂ =>
      Complex.exp
        (((ℓ : ℂ) - z) * (Real.log Real.pi : ℂ) / 2)) := by
    fun_prop
  have harg : Continuous (fun z : ℂ =>
      Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ)) := by
    fun_prop
  have hphase : Continuous (fun z : ℂ =>
      Complex.exp ((ℓ : ℂ) *
        mellinShellPhase ε
          (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ)))) :=
    Complex.continuous_exp.comp
      (continuous_const.mul
        ((mellinShellPhase_continuous hε horder).comp harg))
  exact hpi.mul hphase

private theorem saddleRegularMellinFactor_differentiable {ε : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) (ℓ : ℝ) :
    Differentiable ℂ (saddleRegularMellinFactor ε ℓ) := by
  have hpi : Differentiable ℂ (fun z : ℂ =>
      Complex.exp
        (((ℓ : ℂ) - z) * (Real.log Real.pi : ℂ) / 2)) := by
    fun_prop
  have harg : Differentiable ℂ (fun z : ℂ =>
      Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ)) := by
    fun_prop
  have hphase : Differentiable ℂ (fun z : ℂ =>
      Complex.exp ((ℓ : ℂ) *
        mellinShellPhase ε
          (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ)))) :=
    Complex.differentiable_exp.comp
      (((mellinShellPhase_differentiable hε horder).comp
        harg).const_mul (ℓ : ℂ))
  exact hpi.mul hphase

private theorem plusSaddleRegularMellinFactor_differentiable {ε : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) (ℓ : ℝ) :
    Differentiable ℂ (plusSaddleRegularMellinFactor ε ℓ) := by
  have hp : Differentiable ℂ (fun z : ℂ =>
      plusPolynomial ε
        (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ))) := by
    unfold plusPolynomial
    fun_prop
  exact (saddleRegularMellinFactor_differentiable
    hε horder ℓ).mul hp

private theorem minusSaddleRegularMellinFactor_differentiable {ε : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) (ℓ : ℝ) :
    Differentiable ℂ (minusSaddleRegularMellinFactor ε ℓ) := by
  have hp : Differentiable ℂ (fun z : ℂ =>
      minusPolynomial ε
        (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ))) := by
    unfold minusPolynomial
    fun_prop
  exact (saddleRegularMellinFactor_differentiable
    hε horder ℓ).mul hp

private theorem plusSaddleRegularMellinFactor_analyticOnNhd {ε : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) (ℓ : ℝ) :
    AnalyticOnNhd ℂ (plusSaddleRegularMellinFactor ε ℓ) Set.univ :=
  Complex.analyticOnNhd_univ_iff_differentiable.mpr
    (plusSaddleRegularMellinFactor_differentiable hε horder ℓ)

private theorem minusSaddleRegularMellinFactor_analyticOnNhd {ε : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) (ℓ : ℝ) :
    AnalyticOnNhd ℂ (minusSaddleRegularMellinFactor ε ℓ) Set.univ :=
  Complex.analyticOnNhd_univ_iff_differentiable.mpr
    (minusSaddleRegularMellinFactor_differentiable hε horder ℓ)

private theorem saddleMellinGamma_meromorphic :
    Meromorphic (fun z : ℂ => Complex.Gamma (z / 2)) := by
  intro z
  have hg : MeromorphicAt Complex.Gamma (z / 2) :=
    Meromorphic.Gamma (z / 2)
  have ha : AnalyticAt ℂ (fun u : ℂ => u / 2) z := by
    fun_prop
  simpa only [Function.comp_def] using!
    (MeromorphicAt.comp_analyticAt
      (g := fun u : ℂ => u / 2) (x := z) hg ha)

private theorem plusSaddleMellinData_meromorphic {ε : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) (ℓ : ℝ) :
    Meromorphic (plusSaddleMellinData ε ℓ) := by
  have hregular : Meromorphic (plusSaddleRegularMellinFactor ε ℓ) :=
    meromorphicOn_univ.mp
      (plusSaddleRegularMellinFactor_analyticOnNhd
        hε horder ℓ).meromorphicOn
  have hproduct := saddleMellinGamma_meromorphic.mul hregular
  intro z
  rw [show plusSaddleMellinData ε ℓ =
      (fun w : ℂ => Complex.Gamma (w / 2) *
        plusSaddleRegularMellinFactor ε ℓ w) by
    funext w
    exact plusSaddleMellinData_eq_gamma_mul_regular ε ℓ w]
  exact hproduct z

private theorem minusSaddleMellinData_meromorphic {ε : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) (ℓ : ℝ) :
    Meromorphic (minusSaddleMellinData ε ℓ) := by
  have hregular : Meromorphic (minusSaddleRegularMellinFactor ε ℓ) :=
    meromorphicOn_univ.mp
      (minusSaddleRegularMellinFactor_analyticOnNhd
        hε horder ℓ).meromorphicOn
  have hproduct := saddleMellinGamma_meromorphic.mul hregular
  intro z
  rw [show minusSaddleMellinData ε ℓ =
      (fun w : ℂ => Complex.Gamma (w / 2) *
        minusSaddleRegularMellinFactor ε ℓ w) by
    funext w
    exact minusSaddleMellinData_eq_gamma_mul_regular ε ℓ w]
  exact hproduct z

private theorem saddleMellinGamma_differentiableAt_of_re_pos
    {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w / 2)) z := by
  have hhalf : 0 < (z / 2).re := by
    simpa only [Complex.div_ofNat_re, Nat.ofNat_pos, div_pos_iff_of_pos_right] using! half_pos hz
  have hg : DifferentiableAt ℂ Complex.Gamma (z / 2) :=
    Complex.differentiableAt_Gamma (z / 2) (by
      intro n hn
      have hnonpositive : (-(n : ℂ)).re ≤ 0 := by simp only [Complex.neg_re, Complex.natCast_re,
        Left.neg_nonpos_iff, Nat.cast_nonneg]
      exact (not_lt_of_ge hnonpositive) (hn ▸ hhalf))
  exact hg.comp z (by fun_prop)

private theorem saddleMellinGamma_differentiableOn_rightHalfPlane :
    DifferentiableOn ℂ
      (fun z : ℂ => Complex.Gamma (z / 2))
      {z : ℂ | 0 < z.re} := by
  intro z hz
  exact (saddleMellinGamma_differentiableAt_of_re_pos
    hz).differentiableWithinAt

private theorem plusSaddleMellinData_differentiableOn_rightHalfPlane
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) (ℓ : ℝ) :
    DifferentiableOn ℂ (plusSaddleMellinData ε ℓ)
      {z : ℂ | 0 < z.re} := by
  rw [show plusSaddleMellinData ε ℓ =
      (fun z : ℂ => Complex.Gamma (z / 2) *
        plusSaddleRegularMellinFactor ε ℓ z) by
    funext z
    exact plusSaddleMellinData_eq_gamma_mul_regular ε ℓ z]
  exact saddleMellinGamma_differentiableOn_rightHalfPlane.mul
    (plusSaddleRegularMellinFactor_differentiable
      hε horder ℓ).differentiableOn

private theorem minusSaddleMellinData_differentiableOn_rightHalfPlane
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) (ℓ : ℝ) :
    DifferentiableOn ℂ (minusSaddleMellinData ε ℓ)
      {z : ℂ | 0 < z.re} := by
  rw [show minusSaddleMellinData ε ℓ =
      (fun z : ℂ => Complex.Gamma (z / 2) *
        minusSaddleRegularMellinFactor ε ℓ z) by
    funext z
    exact minusSaddleMellinData_eq_gamma_mul_regular ε ℓ z]
  exact saddleMellinGamma_differentiableOn_rightHalfPlane.mul
    (minusSaddleRegularMellinFactor_differentiable
      hε horder ℓ).differentiableOn

private theorem saddleMellinShellArgument_zero {ℓ : ℝ}
    (hℓ : 0 < ℓ) :
    Complex.I * ((0 : ℂ) - (ℓ : ℂ)) / (ℓ : ℂ) =
      -Complex.I := by
  have hc : (ℓ : ℂ) ≠ 0 := by
    exact_mod_cast hℓ.ne'
  field_simp [hc]; ring

private theorem saddleMellinShellArgument_neg_even {ℓ : ℝ}
    (hℓ : 0 < ℓ) (n : ℕ) :
    Complex.I *
        ((-((2 * n : ℕ) : ℂ)) - (ℓ : ℂ)) / (ℓ : ℂ) =
      Complex.I *
        ((-(1 + 2 * (n : ℝ) / ℓ) : ℝ) : ℂ) := by
  have hc : (ℓ : ℂ) ≠ 0 := by
    exact_mod_cast hℓ.ne'
  push_cast
  field_simp [hc]; ring

private theorem mellinShellPhase_neg_I (ε : ℝ) :
    mellinShellPhase ε (-Complex.I) =
      (realHyperbolicShellPhase ε 1 : ℂ) := by
  calc
    mellinShellPhase ε (-Complex.I) =
        mellinShellPhase ε Complex.I :=
          mellinShellPhase_neg ε Complex.I
    _ = (realHyperbolicShellPhase ε 1 : ℂ) := by
          simpa only [Complex.ofReal_one, mul_one] using! mellinShellPhase_imaginary ε 1

private theorem plusPolynomial_neg_I (ε : ℝ) :
    plusPolynomial ε (-Complex.I) = ((ε / 4 : ℝ) : ℂ) := by
  simpa only [Complex.ofReal_neg, Complex.ofReal_one, mul_neg, mul_one, sub_neg_eq_add,
    add_neg_cancel,
    mul_zero, add_zero] using! plusPolynomial_imaginary ε (-1)

private theorem minusPolynomial_neg_I (ε : ℝ) :
    minusPolynomial ε (-Complex.I) = ((ε / 4 : ℝ) : ℂ) := by
  simpa only [Complex.ofReal_neg, Complex.ofReal_one, mul_neg, mul_one, sub_neg_eq_add,
    add_neg_cancel, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      add_zero] using! minusPolynomial_imaginary ε (-1)

private theorem saddleRegularMellinFactor_zero
    {ε ℓ : ℝ} (hℓ : 0 < ℓ) :
    saddleRegularMellinFactor ε ℓ 0 =
      ((Real.pi ^ (ℓ / 2) *
        Real.exp (ℓ * realHyperbolicShellPhase ε 1) : ℝ) : ℂ) := by
  have hpi :
      Complex.exp
        (((ℓ : ℂ) - (0 : ℂ)) *
          (Real.log Real.pi : ℂ) / 2) =
        ((Real.pi ^ (ℓ / 2) : ℝ) : ℂ) := by
    rw [Real.rpow_def_of_pos Real.pi_pos, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hphase :
      Complex.exp
        ((ℓ : ℂ) * mellinShellPhase ε (-Complex.I)) =
        (Real.exp
          (ℓ * realHyperbolicShellPhase ε 1) : ℂ) := by
    rw [mellinShellPhase_neg_I,
      ← Complex.ofReal_mul, ← Complex.ofReal_exp]
  unfold saddleRegularMellinFactor
  rw [saddleMellinShellArgument_zero hℓ, hpi, hphase,
    ← Complex.ofReal_mul]

private theorem saddleRegularMellinFactor_neg_even
    {ε ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) :
    saddleRegularMellinFactor ε ℓ (-((2 * n : ℕ) : ℂ)) =
      ((Real.pi ^ (ℓ / 2 + (n : ℝ)) *
        Real.exp
          (ℓ * realHyperbolicShellPhase ε
            (1 + 2 * (n : ℝ) / ℓ)) : ℝ) : ℂ) := by
  have hpi :
      Complex.exp
        (((ℓ : ℂ) - (-((2 * n : ℕ) : ℂ))) *
          (Real.log Real.pi : ℂ) / 2) =
        ((Real.pi ^ (ℓ / 2 + (n : ℝ)) : ℝ) : ℂ) := by
    rw [Real.rpow_def_of_pos Real.pi_pos, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hphase :
      Complex.exp
        ((ℓ : ℂ) * mellinShellPhase ε
          (Complex.I *
            ((-((2 * n : ℕ) : ℂ)) - (ℓ : ℂ)) / (ℓ : ℂ))) =
        (Real.exp
          (ℓ * realHyperbolicShellPhase ε
            (1 + 2 * (n : ℝ) / ℓ)) : ℂ) := by
    rw [saddleMellinShellArgument_neg_even hℓ n,
      mellinShellPhase_imaginary,
      realHyperbolicShellPhase_neg,
      ← Complex.ofReal_mul, ← Complex.ofReal_exp]
  unfold saddleRegularMellinFactor
  rw [hpi, hphase, ← Complex.ofReal_mul]

private theorem plusSaddleRegularMellinFactor_neg_even
    {ε ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) :
    plusSaddleRegularMellinFactor ε ℓ
        (-((2 * n : ℕ) : ℂ)) =
      ((Real.pi ^ (ℓ / 2 + (n : ℝ)) *
        Real.exp
          (ℓ * realHyperbolicShellPhase ε
            (1 + 2 * (n : ℝ) / ℓ)) : ℝ) : ℂ) *
        plusPolynomial ε
          (Complex.I *
            ((-(1 + 2 * (n : ℝ) / ℓ) : ℝ) : ℂ)) := by
  unfold plusSaddleRegularMellinFactor
  rw [saddleRegularMellinFactor_neg_even hℓ n,
    saddleMellinShellArgument_neg_even hℓ n]

private theorem two_mul_plusSaddleRegularMellinFactor_zero
    {ε ℓ : ℝ} (hℓ : 0 < ℓ) :
    (2 : ℂ) * plusSaddleRegularMellinFactor ε ℓ 0 =
      (saddleOriginValue ε ℓ : ℂ) := by
  unfold plusSaddleRegularMellinFactor saddleOriginValue
  rw [saddleRegularMellinFactor_zero hℓ,
    saddleMellinShellArgument_zero hℓ,
    plusPolynomial_neg_I]
  push_cast
  ring

private theorem two_mul_minusSaddleRegularMellinFactor_zero
    {ε ℓ : ℝ} (hℓ : 0 < ℓ) :
    (2 : ℂ) * minusSaddleRegularMellinFactor ε ℓ 0 =
      (saddleOriginValue ε ℓ : ℂ) := by
  unfold minusSaddleRegularMellinFactor saddleOriginValue
  rw [saddleRegularMellinFactor_zero hℓ,
    saddleMellinShellArgument_zero hℓ,
    minusPolynomial_neg_I]
  push_cast
  ring

private theorem complexGamma_residue_neg_nat (n : ℕ) :
    Tendsto (fun z : ℂ => (z + (n : ℂ)) * Complex.Gamma z)
      (𝓝[≠] (-(n : ℂ)))
      (𝓝 (((-1 : ℂ) ^ n) / (n.factorial : ℂ))) := by
  induction n with
  | zero =>
      simpa only [CharP.cast_eq_zero, add_zero, neg_zero, pow_zero, Nat.factorial_zero,
        Nat.cast_one, ne_eq,
        one_ne_zero, not_false_eq_true, div_self] using! Complex.tendsto_self_mul_Gamma_nhds_zero
  | succ n ih =>
      have hshift : Tendsto (fun z : ℂ => z + 1)
          (𝓝[≠] (-((n + 1 : ℕ) : ℂ)))
          (𝓝[≠] (-(n : ℂ))) := by
        rw [tendsto_nhdsWithin_iff]
        constructor
        · convert! ((tendsto_id.add_const (1 : ℂ)).mono_left
            nhdsWithin_le_nhds) using 1; simp only [Nat.cast_add, Nat.cast_one, neg_add_rev,
              neg_add_cancel_comm]
        · filter_upwards [self_mem_nhdsWithin] with z hz
          simp only [Set.mem_compl_iff,
            Set.mem_singleton_iff] at hz ⊢
          intro heq
          apply hz
          simp only [Nat.cast_add, Nat.cast_one]
          linear_combination heq
      have hnonzero : (-((n + 1 : ℕ) : ℂ)) ≠ 0 := by
        exact neg_ne_zero.mpr (by
          exact_mod_cast Nat.succ_ne_zero n)
      have hden : Tendsto (fun z : ℂ => z)
          (𝓝[≠] (-((n + 1 : ℕ) : ℂ)))
          (𝓝 (-((n + 1 : ℕ) : ℂ))) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have hquot := (ih.comp hshift).div hden hnonzero
      have hne : ∀ᶠ z in (𝓝[≠] (-((n + 1 : ℕ) : ℂ))),
          z ≠ (0 : ℂ) :=
        ((continuousAt_id :
          ContinuousAt (fun z : ℂ => z)
            (-((n + 1 : ℕ) : ℂ))).eventually_ne
              hnonzero).filter_mono nhdsWithin_le_nhds
      have htarget :
          (((-1 : ℂ) ^ n / (n.factorial : ℂ)) /
            (-((n + 1 : ℕ) : ℂ))) =
              ((-1 : ℂ) ^ (n + 1)) /
                ((n + 1).factorial : ℂ) := by
        have hn : ((n : ℂ) + 1) ≠ 0 := by
          exact_mod_cast Nat.succ_ne_zero n
        have hf : (n.factorial : ℂ) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero n
        rw [Nat.factorial_succ, Nat.cast_mul,
          Nat.cast_succ, pow_succ]
        field_simp [hn, hf]
      rw [← htarget]
      refine hquot.congr' ?_
      filter_upwards [hne] with z hz
      change
        ((z + 1 + (n : ℂ)) * Complex.Gamma (z + 1)) / z =
          (z + ((n + 1 : ℕ) : ℂ)) * Complex.Gamma z
      rw [Complex.Gamma_add_one z hz]
      simp only [Nat.cast_add, Nat.cast_one]
      field_simp [hz]; ring

private theorem saddleGamma_residue_neg_even (n : ℕ) :
    Tendsto
      (fun z : ℂ =>
        (z + ((2 * n : ℕ) : ℂ)) * Complex.Gamma (z / 2))
      (𝓝[≠] (-((2 * n : ℕ) : ℂ)))
      (𝓝 ((2 : ℂ) * (-1 : ℂ) ^ n / (n.factorial : ℂ))) := by
  have hscale : Tendsto (fun z : ℂ => z / 2)
      (𝓝[≠] (-((2 * n : ℕ) : ℂ)))
      (𝓝[≠] (-(n : ℂ))) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · convert! ((tendsto_id.div_const (2 : ℂ)).mono_left
        nhdsWithin_le_nhds) using 1; simp only [Nat.cast_mul, Nat.cast_ofNat,
          nhds_eq_nhds_iff]; ring
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [Set.mem_compl_iff,
        Set.mem_singleton_iff] at hz ⊢
      intro heq
      apply hz
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      linear_combination 2 * heq
  have hresidue :=
    ((complexGamma_residue_neg_nat n).comp hscale).const_mul
      (2 : ℂ)
  convert! hresidue using 1
  · funext z
    change
      (z + ((2 * n : ℕ) : ℂ)) * Complex.Gamma (z / 2) =
        2 * ((z / 2 + (n : ℂ)) * Complex.Gamma (z / 2))
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    ring
  · ring_nf

private theorem gamma_add_nat_eq_product_of_lt (z : ℂ) (k : ℕ)
    (hz : ∀ j : ℕ, j < k → z + (j : ℂ) ≠ 0) :
    Complex.Gamma (z + (k : ℂ)) =
      Complex.Gamma z *
        ∏ j ∈ Finset.range k, (z + (j : ℂ)) := by
  induction k generalizing z with
  | zero => simp only [CharP.cast_eq_zero, add_zero, Finset.range_zero, Finset.prod_empty, mul_one]
  | succ k ih =>
      have hprevious : ∀ j : ℕ, j < k → z + (j : ℂ) ≠ 0 := by
        intro j hj
        exact hz j (Nat.lt_succ_of_lt hj)
      have hlast : z + (k : ℂ) ≠ 0 :=
        hz k (Nat.lt_succ_self k)
      rw [Nat.cast_succ, ← add_assoc,
        Complex.Gamma_add_one (z + (k : ℂ)) hlast,
        ih z hprevious, Finset.prod_range_succ]
      ring

private noncomputable def saddlePoleStrip (n : ℕ) : Set ℂ :=
  {z : ℂ |
    -(2 * ((n : ℝ) + 1)) < z.re ∧
      z.re < -(2 * (n : ℝ)) + 1}

private theorem saddlePole_mem_strip (n : ℕ) :
    (-((2 * n : ℕ) : ℂ)) ∈ saddlePoleStrip n := by
  change
    -(2 * ((n : ℝ) + 1)) <
        (-((2 * n : ℕ) : ℂ)).re ∧
      (-((2 * n : ℕ) : ℂ)).re <
        -(2 * (n : ℝ)) + 1
  constructor <;>
    norm_num [Nat.cast_mul, Complex.mul_re]

private theorem isOpen_saddlePoleStrip (n : ℕ) :
    IsOpen (saddlePoleStrip n) := by
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

private noncomputable def saddlePoleLowerProduct (n : ℕ) (z : ℂ) : ℂ :=
  ∏ j ∈ Finset.range n, (z / 2 + (j : ℂ))

private theorem saddlePoleLowerProduct_ne_zero
    {n : ℕ} {z : ℂ} (hz : z ∈ saddlePoleStrip n) :
    saddlePoleLowerProduct n z ≠ 0 := by
  unfold saddlePoleLowerProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hjn : j < n := Finset.mem_range.mp hj
  have hjreal : (j : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hjn
  intro hzero
  have hre := congrArg Complex.re hzero
  norm_num at hre
  change
    -(2 * ((n : ℝ) + 1)) < z.re ∧
      z.re < -(2 * (n : ℝ)) + 1 at hz
  linarith

private noncomputable def saddleNthGammaPoleNumerator (n : ℕ) (z : ℂ) : ℂ :=
  (2 : ℂ) *
    Complex.Gamma (z / 2 + ((n + 1 : ℕ) : ℂ)) /
      saddlePoleLowerProduct n z

private theorem saddlePoleLowerProduct_differentiable (n : ℕ) :
    Differentiable ℂ (saddlePoleLowerProduct n) := by
  unfold saddlePoleLowerProduct
  fun_prop

private theorem saddleGamma_eq_nthPoleNumerator_div
    {n : ℕ} {z : ℂ}
    (hstrip : z ∈ saddlePoleStrip n)
    (hpole : z ≠ (-((2 * n : ℕ) : ℂ))) :
    Complex.Gamma (z / 2) =
      saddleNthGammaPoleNumerator n z /
        (z + ((2 * n : ℕ) : ℂ)) := by
  have hden : saddlePoleLowerProduct n z ≠ 0 :=
    saddlePoleLowerProduct_ne_zero hstrip
  have hterms :
      ∀ j : ℕ, j < n → z / 2 + (j : ℂ) ≠ 0 := by
    have hproduct :
        (∏ j ∈ Finset.range n,
          (z / 2 + (j : ℂ))) ≠ 0 := by
      simpa only [ne_eq, saddlePoleLowerProduct] using! hden
    intro j hj
    exact (Finset.prod_ne_zero_iff.mp hproduct)
      j (Finset.mem_range.mpr hj)
  have hfinite :
      ∀ j : ℕ, j < n + 1 →
        z / 2 + (j : ℂ) ≠ 0 := by
    intro j hj
    by_cases heq : j = n
    · subst j
      intro hzero
      apply hpole
      push_cast at hzero ⊢
      linear_combination 2 * hzero
    · exact hterms j (by omega)
  have hrec :=
    gamma_add_nat_eq_product_of_lt (z / 2)
      (n + 1) hfinite
  rw [Finset.prod_range_succ] at hrec
  have hcoordinate :
      z + ((2 * n : ℕ) : ℂ) ≠ 0 := by
    intro hzero
    apply hpole
    push_cast at hzero ⊢
    linear_combination hzero
  unfold saddleNthGammaPoleNumerator
  rw [hrec]
  change Complex.Gamma (z / 2) =
    2 *
      (Complex.Gamma (z / 2) *
        ((∏ j ∈ Finset.range n,
          (z / 2 + (j : ℂ))) *
          (z / 2 + (n : ℂ)))) /
      saddlePoleLowerProduct n z /
        (z + ((2 * n : ℕ) : ℂ))
  rw [show saddlePoleLowerProduct n z =
      ∏ j ∈ Finset.range n, (z / 2 + (j : ℂ)) by rfl]
  have hproduct :
      (∏ j ∈ Finset.range n,
        (z / 2 + (j : ℂ))) ≠ 0 := by
    simpa only [ne_eq, saddlePoleLowerProduct] using! hden
  have hcancel :
      2 *
        (Complex.Gamma (z / 2) *
          ((∏ j ∈ Finset.range n,
            (z / 2 + (j : ℂ))) *
            (z / 2 + (n : ℂ)))) /
          (∏ j ∈ Finset.range n,
            (z / 2 + (j : ℂ))) =
        2 * Complex.Gamma (z / 2) *
          (z / 2 + (n : ℂ)) := by
    calc
      _ =
          (2 * Complex.Gamma (z / 2) *
            (z / 2 + (n : ℂ))) *
              (∏ j ∈ Finset.range n,
                (z / 2 + (j : ℂ))) /
              (∏ j ∈ Finset.range n,
                (z / 2 + (j : ℂ))) := by
            congr 1
            ring
      _ = _ := mul_div_cancel_right₀ _ hproduct
  rw [hcancel]
  field_simp [hcoordinate]; push_cast; ring

private theorem saddleNthGammaPoleNumerator_differentiableOn (n : ℕ) :
    DifferentiableOn ℂ (saddleNthGammaPoleNumerator n)
      (saddlePoleStrip n) := by
  intro z hz
  have hpositive :
      0 < (z / 2 + ((n + 1 : ℕ) : ℂ)).re := by
    norm_num [Nat.cast_add]
    change
      -(2 * ((n : ℝ) + 1)) < z.re ∧
        z.re < -(2 * (n : ℝ)) + 1 at hz
    linarith [hz.1]
  have hgamma :
      DifferentiableAt ℂ Complex.Gamma
        (z / 2 + ((n + 1 : ℕ) : ℂ)) :=
    Complex.differentiableAt_Gamma _ (by
      intro m hm
      have hnonpositive : (-(m : ℂ)).re ≤ 0 := by simp only [Complex.neg_re, Complex.natCast_re,
        Left.neg_nonpos_iff, Nat.cast_nonneg]
      exact (not_lt_of_ge hnonpositive) (hm ▸ hpositive))
  have hcompose :
      DifferentiableAt ℂ
        (fun w : ℂ =>
          Complex.Gamma
            (w / 2 + ((n + 1 : ℕ) : ℂ))) z :=
    hgamma.comp z (by fun_prop)
  have hnumerator := hcompose.const_mul (2 : ℂ)
  have hdenominator := saddlePoleLowerProduct_differentiable n z
  exact (hnumerator.div hdenominator
    (saddlePoleLowerProduct_ne_zero hz)).differentiableWithinAt

private theorem saddleNthGammaPoleNumerator_at_pole (n : ℕ) :
    saddleNthGammaPoleNumerator n
        (-((2 * n : ℕ) : ℂ)) =
      (2 : ℂ) * (-1 : ℂ) ^ n / (n.factorial : ℂ) := by
  have hpole :
      (-((2 * n : ℕ) : ℂ)) ∈ saddlePoleStrip n :=
    saddlePole_mem_strip n
  have hanalytic :
      DifferentiableAt ℂ (saddleNthGammaPoleNumerator n)
        (-((2 * n : ℕ) : ℂ)) :=
    (saddleNthGammaPoleNumerator_differentiableOn n).differentiableAt
      ((isOpen_saddlePoleStrip n).mem_nhds hpole)
  have hcontinuous :
      Tendsto (saddleNthGammaPoleNumerator n)
        (𝓝[≠] (-((2 * n : ℕ) : ℂ)))
        (𝓝 (saddleNthGammaPoleNumerator n
          (-((2 * n : ℕ) : ℂ)))) :=
    hanalytic.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hstrip :
      ∀ᶠ z in (𝓝[≠] (-((2 * n : ℕ) : ℂ))),
        z ∈ saddlePoleStrip n :=
    nhdsWithin_le_nhds
      ((isOpen_saddlePoleStrip n).mem_nhds hpole)
  have heventual :
      (fun z : ℂ =>
        (z + ((2 * n : ℕ) : ℂ)) *
          Complex.Gamma (z / 2)) =ᶠ[𝓝[≠]
            (-((2 * n : ℕ) : ℂ))]
          saddleNthGammaPoleNumerator n := by
    filter_upwards [hstrip, self_mem_nhdsWithin]
      with z hz hne
    simp only [Set.mem_compl_iff,
      Set.mem_singleton_iff] at hne
    rw [saddleGamma_eq_nthPoleNumerator_div hz hne]
    have hcoordinate :
        z + ((2 * n : ℕ) : ℂ) ≠ 0 := by
      intro hzero
      apply hne
      linear_combination hzero
    rw [← mul_div_assoc]
    exact mul_div_cancel_left₀ _ hcoordinate
  exact (tendsto_nhds_unique_of_eventuallyEq
    (saddleGamma_residue_neg_even n)
    hcontinuous heventual).symm

private noncomputable def plusSaddleNthPoleNumerator
    (ε ℓ : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  saddleNthGammaPoleNumerator n z *
    plusSaddleRegularMellinFactor ε ℓ z

private noncomputable def minusSaddleNthPoleNumerator
    (ε ℓ : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  saddleNthGammaPoleNumerator n z *
    minusSaddleRegularMellinFactor ε ℓ z

private theorem plusSaddleNthPoleNumerator_differentiableOn
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) (n : ℕ) :
    DifferentiableOn ℂ (plusSaddleNthPoleNumerator ε ℓ n)
      (saddlePoleStrip n) := by
  unfold plusSaddleNthPoleNumerator
  exact (saddleNthGammaPoleNumerator_differentiableOn n).mul
    (plusSaddleRegularMellinFactor_differentiable
      hε horder ℓ).differentiableOn

private theorem minusSaddleNthPoleNumerator_differentiableOn
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) (n : ℕ) :
    DifferentiableOn ℂ (minusSaddleNthPoleNumerator ε ℓ n)
      (saddlePoleStrip n) := by
  unfold minusSaddleNthPoleNumerator
  exact (saddleNthGammaPoleNumerator_differentiableOn n).mul
    (minusSaddleRegularMellinFactor_differentiable
      hε horder ℓ).differentiableOn

private theorem plusSaddleMellinData_eq_nthPoleNumerator_div
    (ε ℓ : ℝ) {n : ℕ} {z : ℂ}
    (hstrip : z ∈ saddlePoleStrip n)
    (hpole : z ≠ (-((2 * n : ℕ) : ℂ))) :
    plusSaddleMellinData ε ℓ z =
      plusSaddleNthPoleNumerator ε ℓ n z /
        (z + ((2 * n : ℕ) : ℂ)) := by
  rw [plusSaddleMellinData_eq_gamma_mul_regular,
    saddleGamma_eq_nthPoleNumerator_div hstrip hpole]
  unfold plusSaddleNthPoleNumerator
  ring

private theorem minusSaddleMellinData_eq_nthPoleNumerator_div
    (ε ℓ : ℝ) {n : ℕ} {z : ℂ}
    (hstrip : z ∈ saddlePoleStrip n)
    (hpole : z ≠ (-((2 * n : ℕ) : ℂ))) :
    minusSaddleMellinData ε ℓ z =
      minusSaddleNthPoleNumerator ε ℓ n z /
        (z + ((2 * n : ℕ) : ℂ)) := by
  rw [minusSaddleMellinData_eq_gamma_mul_regular,
    saddleGamma_eq_nthPoleNumerator_div hstrip hpole]
  unfold minusSaddleNthPoleNumerator
  ring

private theorem plusSaddleNthPoleNumerator_at_pole
    (ε ℓ : ℝ) (n : ℕ) :
    plusSaddleNthPoleNumerator ε ℓ n
        (-((2 * n : ℕ) : ℂ)) =
      (2 : ℂ) * (-1 : ℂ) ^ n / (n.factorial : ℂ) *
        plusSaddleRegularMellinFactor ε ℓ
          (-((2 * n : ℕ) : ℂ)) := by
  unfold plusSaddleNthPoleNumerator
  rw [saddleNthGammaPoleNumerator_at_pole]

private theorem minusSaddleNthPoleNumerator_at_pole
    (ε ℓ : ℝ) (n : ℕ) :
    minusSaddleNthPoleNumerator ε ℓ n
        (-((2 * n : ℕ) : ℂ)) =
      (2 : ℂ) * (-1 : ℂ) ^ n / (n.factorial : ℂ) *
        minusSaddleRegularMellinFactor ε ℓ
          (-((2 * n : ℕ) : ℂ)) := by
  unfold minusSaddleNthPoleNumerator
  rw [saddleNthGammaPoleNumerator_at_pole]

private noncomputable def plusSaddlePoleResidue (ε ℓ : ℝ) (n : ℕ) : ℂ :=
  (2 : ℂ) * (-1 : ℂ) ^ n / (n.factorial : ℂ) *
    plusSaddleRegularMellinFactor ε ℓ
      (-((2 * n : ℕ) : ℂ))

private noncomputable def minusSaddlePoleResidue (ε ℓ : ℝ) (n : ℕ) : ℂ :=
  (2 : ℂ) * (-1 : ℂ) ^ n / (n.factorial : ℂ) *
    minusSaddleRegularMellinFactor ε ℓ
      (-((2 * n : ℕ) : ℂ))

private theorem plusSaddleNthPoleNumerator_poleResidue
    (ε ℓ : ℝ) (n : ℕ) :
    plusSaddleNthPoleNumerator ε ℓ n
        (-((2 * n : ℕ) : ℂ)) =
      plusSaddlePoleResidue ε ℓ n := by
  exact plusSaddleNthPoleNumerator_at_pole ε ℓ n

private theorem minusSaddleNthPoleNumerator_poleResidue
    (ε ℓ : ℝ) (n : ℕ) :
    minusSaddleNthPoleNumerator ε ℓ n
        (-((2 * n : ℕ) : ℂ)) =
      minusSaddlePoleResidue ε ℓ n := by
  exact minusSaddleNthPoleNumerator_at_pole ε ℓ n

private noncomputable def plusSaddleNthPoleRegularPart
    (ε ℓ : ℝ) (n : ℕ) : ℂ → ℂ :=
  dslope (plusSaddleNthPoleNumerator ε ℓ n)
    (-((2 * n : ℕ) : ℂ))

private noncomputable def minusSaddleNthPoleRegularPart
    (ε ℓ : ℝ) (n : ℕ) : ℂ → ℂ :=
  dslope (minusSaddleNthPoleNumerator ε ℓ n)
    (-((2 * n : ℕ) : ℂ))

private theorem plusSaddleNthPoleRegularPart_differentiableOn
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) (n : ℕ) :
    DifferentiableOn ℂ (plusSaddleNthPoleRegularPart ε ℓ n)
      (saddlePoleStrip n) := by
  unfold plusSaddleNthPoleRegularPart
  exact (Complex.differentiableOn_dslope
    ((isOpen_saddlePoleStrip n).mem_nhds
      (saddlePole_mem_strip n))).mpr
        (plusSaddleNthPoleNumerator_differentiableOn
          hε horder ℓ n)

private theorem minusSaddleNthPoleRegularPart_differentiableOn
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) (n : ℕ) :
    DifferentiableOn ℂ (minusSaddleNthPoleRegularPart ε ℓ n)
      (saddlePoleStrip n) := by
  unfold minusSaddleNthPoleRegularPart
  exact (Complex.differentiableOn_dslope
    ((isOpen_saddlePoleStrip n).mem_nhds
      (saddlePole_mem_strip n))).mpr
        (minusSaddleNthPoleNumerator_differentiableOn
          hε horder ℓ n)

private theorem plusSaddleMellinData_nthPole_decomposition
    (ε ℓ : ℝ) {n : ℕ} {z : ℂ}
    (hstrip : z ∈ saddlePoleStrip n)
    (hpole : z ≠ (-((2 * n : ℕ) : ℂ))) :
    plusSaddleMellinData ε ℓ z =
      plusSaddlePoleResidue ε ℓ n /
          (z + ((2 * n : ℕ) : ℂ)) +
        plusSaddleNthPoleRegularPart ε ℓ n z := by
  have hslope :
      (z + ((2 * n : ℕ) : ℂ)) *
          plusSaddleNthPoleRegularPart ε ℓ n z =
        plusSaddleNthPoleNumerator ε ℓ n z -
          plusSaddlePoleResidue ε ℓ n := by
    have hbase := sub_smul_dslope
      (plusSaddleNthPoleNumerator ε ℓ n)
        (-((2 * n : ℕ) : ℂ)) z
    rw [plusSaddleNthPoleNumerator_poleResidue
      ε ℓ n] at hbase
    simpa only [plusSaddleNthPoleRegularPart,
      sub_neg_eq_add, smul_eq_mul] using! hbase
  have hnumerator :
      plusSaddleNthPoleNumerator ε ℓ n z =
        plusSaddlePoleResidue ε ℓ n +
          (z + ((2 * n : ℕ) : ℂ)) *
            plusSaddleNthPoleRegularPart ε ℓ n z := by
    rw [hslope]
    ring
  rw [plusSaddleMellinData_eq_nthPoleNumerator_div
    ε ℓ hstrip hpole, hnumerator]
  have hcoordinate :
      z + ((2 * n : ℕ) : ℂ) ≠ 0 := by
    intro hzero
    apply hpole
    linear_combination hzero
  field_simp [hcoordinate]

private theorem minusSaddleMellinData_nthPole_decomposition
    (ε ℓ : ℝ) {n : ℕ} {z : ℂ}
    (hstrip : z ∈ saddlePoleStrip n)
    (hpole : z ≠ (-((2 * n : ℕ) : ℂ))) :
    minusSaddleMellinData ε ℓ z =
      minusSaddlePoleResidue ε ℓ n /
          (z + ((2 * n : ℕ) : ℂ)) +
        minusSaddleNthPoleRegularPart ε ℓ n z := by
  have hslope :
      (z + ((2 * n : ℕ) : ℂ)) *
          minusSaddleNthPoleRegularPart ε ℓ n z =
        minusSaddleNthPoleNumerator ε ℓ n z -
          minusSaddlePoleResidue ε ℓ n := by
    have hbase := sub_smul_dslope
      (minusSaddleNthPoleNumerator ε ℓ n)
        (-((2 * n : ℕ) : ℂ)) z
    rw [minusSaddleNthPoleNumerator_poleResidue
      ε ℓ n] at hbase
    simpa only [minusSaddleNthPoleRegularPart,
      sub_neg_eq_add, smul_eq_mul] using! hbase
  have hnumerator :
      minusSaddleNthPoleNumerator ε ℓ n z =
        minusSaddlePoleResidue ε ℓ n +
          (z + ((2 * n : ℕ) : ℂ)) *
            minusSaddleNthPoleRegularPart ε ℓ n z := by
    rw [hslope]
    ring
  rw [minusSaddleMellinData_eq_nthPoleNumerator_div
    ε ℓ hstrip hpole, hnumerator]
  have hcoordinate :
      z + ((2 * n : ℕ) : ℂ) ≠ 0 := by
    intro hzero
    apply hpole
    linear_combination hzero
  field_simp [hcoordinate]

private noncomputable def saddleFinitePoleHalfPlane (N : ℕ) : Set ℂ :=
  {z : ℂ | -(2 * ((N : ℝ) + 1)) < z.re}

private theorem saddlePole_mem_finiteHalfPlane_iff
    (N n : ℕ) :
    (-((2 * n : ℕ) : ℂ)) ∈
        saddleFinitePoleHalfPlane N ↔ n ≤ N := by
  change
    -(2 * ((N : ℝ) + 1)) <
      (-((2 * n : ℕ) : ℂ)).re ↔ n ≤ N
  norm_num [Nat.cast_mul, Complex.mul_re]
  constructor
  · intro hreal
    have hstrict : (n : ℝ) < (N : ℝ) + 1 := by
      linarith
    have hn : n < N + 1 := by
      exact_mod_cast hstrict
    omega
  · intro hn
    have hreal : (n : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hn
    linarith

private theorem saddleMellinGamma_differentiableAt_of_not_pole
    {z : ℂ}
    (hz : ∀ n : ℕ,
      z ≠ (-((2 * n : ℕ) : ℂ))) :
    DifferentiableAt ℂ
      (fun w : ℂ => Complex.Gamma (w / 2)) z := by
  have hhalf : ∀ n : ℕ, z / 2 ≠ -(n : ℂ) := by
    intro n hzero
    apply hz n
    push_cast at hzero ⊢
    linear_combination 2 * hzero
  exact (Complex.differentiableAt_Gamma (z / 2)
    hhalf).comp z (by fun_prop)

private theorem plusSaddleMellinData_differentiableAt_of_not_pole
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) {z : ℂ}
    (hz : ∀ n : ℕ,
      z ≠ (-((2 * n : ℕ) : ℂ))) :
    DifferentiableAt ℂ (plusSaddleMellinData ε ℓ) z := by
  rw [show plusSaddleMellinData ε ℓ =
      (fun w : ℂ => Complex.Gamma (w / 2) *
        plusSaddleRegularMellinFactor ε ℓ w) by
    funext w
    exact plusSaddleMellinData_eq_gamma_mul_regular ε ℓ w]
  exact (saddleMellinGamma_differentiableAt_of_not_pole hz).mul
    (plusSaddleRegularMellinFactor_differentiable
      hε horder ℓ z)

private theorem minusSaddleMellinData_differentiableAt_of_not_pole
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) {z : ℂ}
    (hz : ∀ n : ℕ,
      z ≠ (-((2 * n : ℕ) : ℂ))) :
    DifferentiableAt ℂ (minusSaddleMellinData ε ℓ) z := by
  rw [show minusSaddleMellinData ε ℓ =
      (fun w : ℂ => Complex.Gamma (w / 2) *
        minusSaddleRegularMellinFactor ε ℓ w) by
    funext w
    exact minusSaddleMellinData_eq_gamma_mul_regular ε ℓ w]
  exact (saddleMellinGamma_differentiableAt_of_not_pole hz).mul
    (minusSaddleRegularMellinFactor_differentiable
      hε horder ℓ z)

private noncomputable def plusSaddleFinitePoleSubtraction
    (ε ℓ : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  plusSaddleMellinData ε ℓ z -
    ∑ n ∈ Finset.range (N + 1),
      plusSaddlePoleResidue ε ℓ n /
        (z + ((2 * n : ℕ) : ℂ))

private noncomputable def minusSaddleFinitePoleSubtraction
    (ε ℓ : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  minusSaddleMellinData ε ℓ z -
    ∑ n ∈ Finset.range (N + 1),
      minusSaddlePoleResidue ε ℓ n /
        (z + ((2 * n : ℕ) : ℂ))

private theorem plusSaddleFinitePoleSubtraction_meromorphic
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) (N : ℕ) :
    Meromorphic (plusSaddleFinitePoleSubtraction ε ℓ N) := by
  have hsum : Meromorphic
      (fun z : ℂ =>
        ∑ n ∈ Finset.range (N + 1),
          plusSaddlePoleResidue ε ℓ n /
            (z + ((2 * n : ℕ) : ℂ))) := by
    intro z
    exact MeromorphicAt.fun_sum
      (fun n _ => by fun_prop)
  exact (plusSaddleMellinData_meromorphic
    hε horder ℓ).sub hsum

private theorem minusSaddleFinitePoleSubtraction_meromorphic
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) (N : ℕ) :
    Meromorphic (minusSaddleFinitePoleSubtraction ε ℓ N) := by
  have hsum : Meromorphic
      (fun z : ℂ =>
        ∑ n ∈ Finset.range (N + 1),
          minusSaddlePoleResidue ε ℓ n /
            (z + ((2 * n : ℕ) : ℂ))) := by
    intro z
    exact MeromorphicAt.fun_sum
      (fun n _ => by fun_prop)
  exact (minusSaddleMellinData_meromorphic
    hε horder ℓ).sub hsum

private noncomputable def plusSaddleFinitePoleRegularPart
    (ε ℓ : ℝ) (N : ℕ) : ℂ → ℂ :=
  toMeromorphicNFOn
    (plusSaddleFinitePoleSubtraction ε ℓ N)
      (saddleFinitePoleHalfPlane N)

private noncomputable def minusSaddleFinitePoleRegularPart
    (ε ℓ : ℝ) (N : ℕ) : ℂ → ℂ :=
  toMeromorphicNFOn
    (minusSaddleFinitePoleSubtraction ε ℓ N)
      (saddleFinitePoleHalfPlane N)

private theorem plusSaddleFinitePoleRegularPart_meromorphicNFOn
    (ε ℓ : ℝ) (N : ℕ) :
    MeromorphicNFOn
      (plusSaddleFinitePoleRegularPart ε ℓ N)
      (saddleFinitePoleHalfPlane N) := by
  unfold plusSaddleFinitePoleRegularPart
  exact meromorphicNFOn_toMeromorphicNFOn _ _

private theorem minusSaddleFinitePoleRegularPart_meromorphicNFOn
    (ε ℓ : ℝ) (N : ℕ) :
    MeromorphicNFOn
      (minusSaddleFinitePoleRegularPart ε ℓ N)
      (saddleFinitePoleHalfPlane N) := by
  unfold minusSaddleFinitePoleRegularPart
  exact meromorphicNFOn_toMeromorphicNFOn _ _

private theorem plusSaddleFinitePoleRegularPart_eq_on_punctured
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) (N : ℕ) {z : ℂ}
    (hz : z ∈ saddleFinitePoleHalfPlane N) :
    plusSaddleFinitePoleRegularPart ε ℓ N =ᶠ[𝓝[≠] z]
      plusSaddleFinitePoleSubtraction ε ℓ N := by
  unfold plusSaddleFinitePoleRegularPart
  exact (plusSaddleFinitePoleSubtraction_meromorphic
    hε horder ℓ N).meromorphicOn
      |>.toMeromorphicNFOn_eq_self_on_nhdsNE hz

private theorem minusSaddleFinitePoleRegularPart_eq_on_punctured
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) (N : ℕ) {z : ℂ}
    (hz : z ∈ saddleFinitePoleHalfPlane N) :
    minusSaddleFinitePoleRegularPart ε ℓ N =ᶠ[𝓝[≠] z]
      minusSaddleFinitePoleSubtraction ε ℓ N := by
  unfold minusSaddleFinitePoleRegularPart
  exact (minusSaddleFinitePoleSubtraction_meromorphic
    hε horder ℓ N).meromorphicOn
      |>.toMeromorphicNFOn_eq_self_on_nhdsNE hz

private theorem saddlePoleCoordinate_ne_zero_at_other
    {m n : ℕ} (hmn : m ≠ n) :
    -((2 * n : ℕ) : ℂ) +
      ((2 * m : ℕ) : ℂ) ≠ 0 := by
  intro hzero
  apply hmn
  have hreal := congrArg Complex.re hzero
  norm_num [Nat.cast_mul, Complex.mul_re] at hreal
  have heq : (m : ℝ) = (n : ℝ) := by
    linarith
  exact_mod_cast heq

private noncomputable def plusSaddleFinitePoleRemaining
    (ε ℓ : ℝ) (N n : ℕ) (z : ℂ) : ℂ :=
  ∑ m ∈ (Finset.range (N + 1)).erase n,
    plusSaddlePoleResidue ε ℓ m /
      (z + ((2 * m : ℕ) : ℂ))

private noncomputable def minusSaddleFinitePoleRemaining
    (ε ℓ : ℝ) (N n : ℕ) (z : ℂ) : ℂ :=
  ∑ m ∈ (Finset.range (N + 1)).erase n,
    minusSaddlePoleResidue ε ℓ m /
      (z + ((2 * m : ℕ) : ℂ))

private theorem plusSaddleFinitePoleRemaining_differentiableAt_pole
    (ε ℓ : ℝ) (N n : ℕ) :
    DifferentiableAt ℂ
      (plusSaddleFinitePoleRemaining ε ℓ N n)
      (-((2 * n : ℕ) : ℂ)) := by
  unfold plusSaddleFinitePoleRemaining
  apply DifferentiableAt.fun_sum
  intro m hm
  have hdistinct : m ≠ n :=
    (Finset.mem_erase.mp hm).1
  have hcoordinate :=
    saddlePoleCoordinate_ne_zero_at_other hdistinct
  have hconstant :
      DifferentiableAt ℂ
        (fun _ : ℂ => plusSaddlePoleResidue ε ℓ m)
          (-((2 * n : ℕ) : ℂ)) := by
    fun_prop
  have hdenominator :
      DifferentiableAt ℂ
        (fun z : ℂ => z + ((2 * m : ℕ) : ℂ))
          (-((2 * n : ℕ) : ℂ)) := by
    fun_prop
  exact hconstant.div hdenominator hcoordinate

private theorem minusSaddleFinitePoleRemaining_differentiableAt_pole
    (ε ℓ : ℝ) (N n : ℕ) :
    DifferentiableAt ℂ
      (minusSaddleFinitePoleRemaining ε ℓ N n)
      (-((2 * n : ℕ) : ℂ)) := by
  unfold minusSaddleFinitePoleRemaining
  apply DifferentiableAt.fun_sum
  intro m hm
  have hdistinct : m ≠ n :=
    (Finset.mem_erase.mp hm).1
  have hcoordinate :=
    saddlePoleCoordinate_ne_zero_at_other hdistinct
  have hconstant :
      DifferentiableAt ℂ
        (fun _ : ℂ => minusSaddlePoleResidue ε ℓ m)
          (-((2 * n : ℕ) : ℂ)) := by
    fun_prop
  have hdenominator :
      DifferentiableAt ℂ
        (fun z : ℂ => z + ((2 * m : ℕ) : ℂ))
          (-((2 * n : ℕ) : ℂ)) := by
    fun_prop
  exact hconstant.div hdenominator hcoordinate

private theorem plusSaddleFinitePoleSubtraction_differentiableAt_of_not_pole
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) (N : ℕ) {z : ℂ}
    (hz : ∀ n : ℕ,
      z ≠ (-((2 * n : ℕ) : ℂ))) :
    DifferentiableAt ℂ
      (plusSaddleFinitePoleSubtraction ε ℓ N) z := by
  unfold plusSaddleFinitePoleSubtraction
  apply (plusSaddleMellinData_differentiableAt_of_not_pole
    hε horder ℓ hz).sub
  apply DifferentiableAt.fun_sum
  intro n _
  have hcoordinate :
      z + ((2 * n : ℕ) : ℂ) ≠ 0 := by
    intro hzero
    apply hz n
    linear_combination hzero
  have hconstant :
      DifferentiableAt ℂ
        (fun _ : ℂ => plusSaddlePoleResidue ε ℓ n) z := by
    fun_prop
  have hdenominator :
      DifferentiableAt ℂ
        (fun w : ℂ => w + ((2 * n : ℕ) : ℂ)) z := by
    fun_prop
  exact hconstant.div hdenominator hcoordinate

private theorem minusSaddleFinitePoleSubtraction_differentiableAt_of_not_pole
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) (N : ℕ) {z : ℂ}
    (hz : ∀ n : ℕ,
      z ≠ (-((2 * n : ℕ) : ℂ))) :
    DifferentiableAt ℂ
      (minusSaddleFinitePoleSubtraction ε ℓ N) z := by
  unfold minusSaddleFinitePoleSubtraction
  apply (minusSaddleMellinData_differentiableAt_of_not_pole
    hε horder ℓ hz).sub
  apply DifferentiableAt.fun_sum
  intro n _
  have hcoordinate :
      z + ((2 * n : ℕ) : ℂ) ≠ 0 := by
    intro hzero
    apply hz n
    linear_combination hzero
  have hconstant :
      DifferentiableAt ℂ
        (fun _ : ℂ => minusSaddlePoleResidue ε ℓ n) z := by
    fun_prop
  have hdenominator :
      DifferentiableAt ℂ
        (fun w : ℂ => w + ((2 * n : ℕ) : ℂ)) z := by
    fun_prop
  exact hconstant.div hdenominator hcoordinate

private theorem plusSaddleFinitePoleSubtraction_eventually_eq_poleRegular
    (ε ℓ : ℝ) (N n : ℕ) (hn : n ≤ N) :
    plusSaddleFinitePoleSubtraction ε ℓ N =ᶠ[𝓝[≠]
      (-((2 * n : ℕ) : ℂ))]
        (fun z : ℂ =>
          plusSaddleNthPoleRegularPart ε ℓ n z -
            plusSaddleFinitePoleRemaining ε ℓ N n z) := by
  have hmem : n ∈ Finset.range (N + 1) :=
    Finset.mem_range.mpr (by omega)
  have hstrip :
      ∀ᶠ z in (𝓝[≠] (-((2 * n : ℕ) : ℂ))),
        z ∈ saddlePoleStrip n :=
    nhdsWithin_le_nhds
      ((isOpen_saddlePoleStrip n).mem_nhds
        (saddlePole_mem_strip n))
  filter_upwards [hstrip, self_mem_nhdsWithin]
    with z hz hne
  simp only [Set.mem_compl_iff,
    Set.mem_singleton_iff] at hne
  have hsum :
      (∑ m ∈ (Finset.range (N + 1)).erase n,
        plusSaddlePoleResidue ε ℓ m /
          (z + ((2 * m : ℕ) : ℂ))) +
        plusSaddlePoleResidue ε ℓ n /
          (z + ((2 * n : ℕ) : ℂ)) =
      ∑ m ∈ Finset.range (N + 1),
        plusSaddlePoleResidue ε ℓ m /
          (z + ((2 * m : ℕ) : ℂ)) :=
    (Finset.range (N + 1)).sum_erase_add
      (fun m : ℕ =>
        plusSaddlePoleResidue ε ℓ m /
          (z + ((2 * m : ℕ) : ℂ))) hmem
  unfold plusSaddleFinitePoleSubtraction
    plusSaddleFinitePoleRemaining
  rw [plusSaddleMellinData_nthPole_decomposition
    ε ℓ hz hne, ← hsum]
  ring

private theorem minusSaddleFinitePoleSubtraction_eventually_eq_poleRegular
    (ε ℓ : ℝ) (N n : ℕ) (hn : n ≤ N) :
    minusSaddleFinitePoleSubtraction ε ℓ N =ᶠ[𝓝[≠]
      (-((2 * n : ℕ) : ℂ))]
        (fun z : ℂ =>
          minusSaddleNthPoleRegularPart ε ℓ n z -
            minusSaddleFinitePoleRemaining ε ℓ N n z) := by
  have hmem : n ∈ Finset.range (N + 1) :=
    Finset.mem_range.mpr (by omega)
  have hstrip :
      ∀ᶠ z in (𝓝[≠] (-((2 * n : ℕ) : ℂ))),
        z ∈ saddlePoleStrip n :=
    nhdsWithin_le_nhds
      ((isOpen_saddlePoleStrip n).mem_nhds
        (saddlePole_mem_strip n))
  filter_upwards [hstrip, self_mem_nhdsWithin]
    with z hz hne
  simp only [Set.mem_compl_iff,
    Set.mem_singleton_iff] at hne
  have hsum :
      (∑ m ∈ (Finset.range (N + 1)).erase n,
        minusSaddlePoleResidue ε ℓ m /
          (z + ((2 * m : ℕ) : ℂ))) +
        minusSaddlePoleResidue ε ℓ n /
          (z + ((2 * n : ℕ) : ℂ)) =
      ∑ m ∈ Finset.range (N + 1),
        minusSaddlePoleResidue ε ℓ m /
          (z + ((2 * m : ℕ) : ℂ)) :=
    (Finset.range (N + 1)).sum_erase_add
      (fun m : ℕ =>
        minusSaddlePoleResidue ε ℓ m /
          (z + ((2 * m : ℕ) : ℂ))) hmem
  unfold minusSaddleFinitePoleSubtraction
    minusSaddleFinitePoleRemaining
  rw [minusSaddleMellinData_nthPole_decomposition
    ε ℓ hz hne, ← hsum]
  ring

private theorem plusSaddleFinitePoleSubtraction_tendsto_at_pole
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) (N n : ℕ) (hn : n ≤ N) :
    Tendsto (plusSaddleFinitePoleSubtraction ε ℓ N)
      (𝓝[≠] (-((2 * n : ℕ) : ℂ)))
      (𝓝 (plusSaddleNthPoleRegularPart ε ℓ n
          (-((2 * n : ℕ) : ℂ)) -
        plusSaddleFinitePoleRemaining ε ℓ N n
          (-((2 * n : ℕ) : ℂ)))) := by
  have hregular :
      DifferentiableAt ℂ
        (plusSaddleNthPoleRegularPart ε ℓ n)
          (-((2 * n : ℕ) : ℂ)) :=
    (plusSaddleNthPoleRegularPart_differentiableOn
      hε horder ℓ n).differentiableAt
        ((isOpen_saddlePoleStrip n).mem_nhds
          (saddlePole_mem_strip n))
  have hremaining :=
    plusSaddleFinitePoleRemaining_differentiableAt_pole
      ε ℓ N n
  have hlimit :
      Tendsto
        (fun z : ℂ =>
          plusSaddleNthPoleRegularPart ε ℓ n z -
            plusSaddleFinitePoleRemaining ε ℓ N n z)
        (𝓝[≠] (-((2 * n : ℕ) : ℂ)))
        (𝓝 (plusSaddleNthPoleRegularPart ε ℓ n
            (-((2 * n : ℕ) : ℂ)) -
          plusSaddleFinitePoleRemaining ε ℓ N n
            (-((2 * n : ℕ) : ℂ)))) :=
    (hregular.sub hremaining).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  exact hlimit.congr'
    (plusSaddleFinitePoleSubtraction_eventually_eq_poleRegular
      ε ℓ N n hn).symm

private theorem minusSaddleFinitePoleSubtraction_tendsto_at_pole
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) (N n : ℕ) (hn : n ≤ N) :
    Tendsto (minusSaddleFinitePoleSubtraction ε ℓ N)
      (𝓝[≠] (-((2 * n : ℕ) : ℂ)))
      (𝓝 (minusSaddleNthPoleRegularPart ε ℓ n
          (-((2 * n : ℕ) : ℂ)) -
        minusSaddleFinitePoleRemaining ε ℓ N n
          (-((2 * n : ℕ) : ℂ)))) := by
  have hregular :
      DifferentiableAt ℂ
        (minusSaddleNthPoleRegularPart ε ℓ n)
          (-((2 * n : ℕ) : ℂ)) :=
    (minusSaddleNthPoleRegularPart_differentiableOn
      hε horder ℓ n).differentiableAt
        ((isOpen_saddlePoleStrip n).mem_nhds
          (saddlePole_mem_strip n))
  have hremaining :=
    minusSaddleFinitePoleRemaining_differentiableAt_pole
      ε ℓ N n
  have hlimit :
      Tendsto
        (fun z : ℂ =>
          minusSaddleNthPoleRegularPart ε ℓ n z -
            minusSaddleFinitePoleRemaining ε ℓ N n z)
        (𝓝[≠] (-((2 * n : ℕ) : ℂ)))
        (𝓝 (minusSaddleNthPoleRegularPart ε ℓ n
            (-((2 * n : ℕ) : ℂ)) -
          minusSaddleFinitePoleRemaining ε ℓ N n
            (-((2 * n : ℕ) : ℂ)))) :=
    (hregular.sub hremaining).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  exact hlimit.congr'
    (minusSaddleFinitePoleSubtraction_eventually_eq_poleRegular
      ε ℓ N n hn).symm

private theorem plusSaddleFinitePoleSubtraction_tendsto_of_mem
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) (N : ℕ) {z : ℂ}
    (hz : z ∈ saddleFinitePoleHalfPlane N) :
    ∃ c : ℂ,
      Tendsto (plusSaddleFinitePoleSubtraction ε ℓ N)
        (𝓝[≠] z) (𝓝 c) := by
  by_cases hpole :
      ∃ n : ℕ, z = (-((2 * n : ℕ) : ℂ))
  · obtain ⟨n, hn⟩ := hpole
    subst z
    have hindex : n ≤ N :=
      (saddlePole_mem_finiteHalfPlane_iff N n).mp hz
    exact ⟨plusSaddleNthPoleRegularPart ε ℓ n
        (-((2 * n : ℕ) : ℂ)) -
      plusSaddleFinitePoleRemaining ε ℓ N n
        (-((2 * n : ℕ) : ℂ)),
      plusSaddleFinitePoleSubtraction_tendsto_at_pole
        hε horder ℓ N n hindex⟩
  · have hnot : ∀ n : ℕ,
        z ≠ (-((2 * n : ℕ) : ℂ)) := by
      intro n hn
      exact hpole ⟨n, hn⟩
    refine ⟨plusSaddleFinitePoleSubtraction ε ℓ N z,
      ?_⟩
    exact (plusSaddleFinitePoleSubtraction_differentiableAt_of_not_pole
      hε horder ℓ N hnot).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds

private theorem minusSaddleFinitePoleSubtraction_tendsto_of_mem
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) (N : ℕ) {z : ℂ}
    (hz : z ∈ saddleFinitePoleHalfPlane N) :
    ∃ c : ℂ,
      Tendsto (minusSaddleFinitePoleSubtraction ε ℓ N)
        (𝓝[≠] z) (𝓝 c) := by
  by_cases hpole :
      ∃ n : ℕ, z = (-((2 * n : ℕ) : ℂ))
  · obtain ⟨n, hn⟩ := hpole
    subst z
    have hindex : n ≤ N :=
      (saddlePole_mem_finiteHalfPlane_iff N n).mp hz
    exact ⟨minusSaddleNthPoleRegularPart ε ℓ n
        (-((2 * n : ℕ) : ℂ)) -
      minusSaddleFinitePoleRemaining ε ℓ N n
        (-((2 * n : ℕ) : ℂ)),
      minusSaddleFinitePoleSubtraction_tendsto_at_pole
        hε horder ℓ N n hindex⟩
  · have hnot : ∀ n : ℕ,
        z ≠ (-((2 * n : ℕ) : ℂ)) := by
      intro n hn
      exact hpole ⟨n, hn⟩
    refine ⟨minusSaddleFinitePoleSubtraction ε ℓ N z,
      ?_⟩
    exact (minusSaddleFinitePoleSubtraction_differentiableAt_of_not_pole
      hε horder ℓ N hnot).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds

private theorem plusSaddleFinitePoleRegularPart_analyticOnNhd
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) (N : ℕ) :
    AnalyticOnNhd ℂ
      (plusSaddleFinitePoleRegularPart ε ℓ N)
      (saddleFinitePoleHalfPlane N) := by
  intro z hz
  have hnormal :=
    plusSaddleFinitePoleRegularPart_meromorphicNFOn
      ε ℓ N hz
  obtain ⟨c, hlimit⟩ :=
    plusSaddleFinitePoleSubtraction_tendsto_of_mem
      hε horder ℓ N hz
  have hregular :
      Tendsto (plusSaddleFinitePoleRegularPart ε ℓ N)
        (𝓝[≠] z) (𝓝 c) :=
    hlimit.congr'
      (plusSaddleFinitePoleRegularPart_eq_on_punctured
        hε horder ℓ N hz).symm
  exact hnormal.meromorphicOrderAt_nonneg_iff_analyticAt.mp
    ((tendsto_nhds_iff_meromorphicOrderAt_nonneg
      hnormal.meromorphicAt).mp ⟨c, hregular⟩)

private theorem minusSaddleFinitePoleRegularPart_analyticOnNhd
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) (N : ℕ) :
    AnalyticOnNhd ℂ
      (minusSaddleFinitePoleRegularPart ε ℓ N)
      (saddleFinitePoleHalfPlane N) := by
  intro z hz
  have hnormal :=
    minusSaddleFinitePoleRegularPart_meromorphicNFOn
      ε ℓ N hz
  obtain ⟨c, hlimit⟩ :=
    minusSaddleFinitePoleSubtraction_tendsto_of_mem
      hε horder ℓ N hz
  have hregular :
      Tendsto (minusSaddleFinitePoleRegularPart ε ℓ N)
        (𝓝[≠] z) (𝓝 c) :=
    hlimit.congr'
      (minusSaddleFinitePoleRegularPart_eq_on_punctured
        hε horder ℓ N hz).symm
  exact hnormal.meromorphicOrderAt_nonneg_iff_analyticAt.mp
    ((tendsto_nhds_iff_meromorphicOrderAt_nonneg
      hnormal.meromorphicAt).mp ⟨c, hregular⟩)

private theorem plusSaddleFinitePoleRegularPart_eq_subtraction_of_not_pole
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) (N : ℕ) {z : ℂ}
    (hz : z ∈ saddleFinitePoleHalfPlane N)
    (hpole : ∀ n : ℕ,
      z ≠ (-((2 * n : ℕ) : ℂ))) :
    plusSaddleFinitePoleRegularPart ε ℓ N z =
      plusSaddleFinitePoleSubtraction ε ℓ N z := by
  have hregular :=
    (plusSaddleFinitePoleRegularPart_analyticOnNhd
      hε horder ℓ N z hz).continuousAt
  have hsubtraction :=
    (plusSaddleFinitePoleSubtraction_differentiableAt_of_not_pole
      hε horder ℓ N hpole).continuousAt
  have hpunctured :=
    plusSaddleFinitePoleRegularPart_eq_on_punctured
      hε horder ℓ N hz
  exact ((hregular.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    hsubtraction).mp hpunctured).eq_of_nhds

private theorem minusSaddleFinitePoleRegularPart_eq_subtraction_of_not_pole
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) (N : ℕ) {z : ℂ}
    (hz : z ∈ saddleFinitePoleHalfPlane N)
    (hpole : ∀ n : ℕ,
      z ≠ (-((2 * n : ℕ) : ℂ))) :
    minusSaddleFinitePoleRegularPart ε ℓ N z =
      minusSaddleFinitePoleSubtraction ε ℓ N z := by
  have hregular :=
    (minusSaddleFinitePoleRegularPart_analyticOnNhd
      hε horder ℓ N z hz).continuousAt
  have hsubtraction :=
    (minusSaddleFinitePoleSubtraction_differentiableAt_of_not_pole
      hε horder ℓ N hpole).continuousAt
  have hpunctured :=
    minusSaddleFinitePoleRegularPart_eq_on_punctured
      hε horder ℓ N hz
  exact ((hregular.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    hsubtraction).mp hpunctured).eq_of_nhds

private theorem plusSaddleFinitePoleRegularPart_differentiableOn
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) (N : ℕ) :
    DifferentiableOn ℂ
      (plusSaddleFinitePoleRegularPart ε ℓ N)
      (saddleFinitePoleHalfPlane N) :=
  (plusSaddleFinitePoleRegularPart_analyticOnNhd
    hε horder ℓ N).differentiableOn

private theorem minusSaddleFinitePoleRegularPart_differentiableOn
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) (N : ℕ) :
    DifferentiableOn ℂ
      (minusSaddleFinitePoleRegularPart ε ℓ N)
      (saddleFinitePoleHalfPlane N) :=
  (minusSaddleFinitePoleRegularPart_analyticOnNhd
    hε horder ℓ N).differentiableOn

private theorem saddleFinitePoleHalfPlane_reProdIm_subset
    {N : ℕ} {z w : ℂ}
    (hz : z ∈ saddleFinitePoleHalfPlane N)
    (hw : w ∈ saddleFinitePoleHalfPlane N) :
    ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) ⊆
      saddleFinitePoleHalfPlane N := by
  intro u hu
  have hre : u.re ∈ [[z.re, w.re]] :=
    (Complex.mem_reProdIm.mp hu).1
  change -(2 * ((N : ℝ) + 1)) < z.re at hz
  change -(2 * ((N : ℝ) + 1)) < w.re at hw
  change -(2 * ((N : ℝ) + 1)) < u.re
  rcases Set.mem_uIcc.mp hre with hleft | hright
  · exact hz.trans_le hleft.1
  · exact hw.trans_le hright.1

private noncomputable def saddleMellinInversePower (r : ℝ) (z : ℂ) : ℂ :=
  (r : ℂ) ^ (-z)

private theorem saddleMellinInversePower_differentiable
    {r : ℝ} (hr : 0 < r) :
    Differentiable ℂ (saddleMellinInversePower r) := by
  have hnonzero : (r : ℂ) ≠ 0 := by
    exact_mod_cast hr.ne'
  have hform :
      (fun z : ℂ => (r : ℂ) ^ (-z)) =
        (fun z : ℂ =>
          Complex.exp
            (Complex.log (r : ℂ) * (-z))) := by
    funext z
    exact Complex.cpow_def_of_ne_zero hnonzero (-z)
  change Differentiable ℂ
    (fun z : ℂ => (r : ℂ) ^ (-z))
  rw [hform]
  fun_prop

private noncomputable def saddleGaussianPoleSlope (z : ℂ) : ℂ :=
  dslope (fun w : ℂ => Complex.exp (w ^ 2)) 0 z

private theorem saddleGaussianPoleSlope_differentiable :
    Differentiable ℂ saddleGaussianPoleSlope := by
  have hgaussian :
      Differentiable ℂ
        (fun w : ℂ => Complex.exp (w ^ 2)) := by
    fun_prop
  unfold saddleGaussianPoleSlope
  exact differentiableOn_univ.mp
    ((Complex.differentiableOn_dslope
      (s := Set.univ) (c := (0 : ℂ))
      (show Set.univ ∈ 𝓝 (0 : ℂ) from univ_mem)).mpr
        hgaussian.differentiableOn)

private theorem saddleGaussianPoleSlope_mul (z : ℂ) :
    z * saddleGaussianPoleSlope z =
      Complex.exp (z ^ 2) - 1 := by
  have h := sub_smul_dslope
    (fun w : ℂ => Complex.exp (w ^ 2)) 0 z
  simpa only [saddleGaussianPoleSlope, sub_zero, smul_eq_mul, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true,
    zero_pow, Complex.exp_zero] using! h

private theorem saddleGaussianPoleSlope_eq_of_ne
    {z : ℂ} (hz : z ≠ 0) :
    saddleGaussianPoleSlope z =
      (Complex.exp (z ^ 2) - 1) / z := by
  apply (eq_div_iff hz).2
  simpa only [mul_comm] using! saddleGaussianPoleSlope_mul z

private noncomputable def saddleGaussianPoleRepresentative
    (n : ℕ) (z : ℂ) : ℂ :=
  Complex.exp ((z + ((2 * n : ℕ) : ℂ)) ^ 2) /
    (z + ((2 * n : ℕ) : ℂ))

private noncomputable def plusSaddleFiniteRapidPoleSubtraction
    (ε ℓ : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  plusSaddleMellinData ε ℓ z -
    ∑ n ∈ Finset.range (N + 1),
      plusSaddlePoleResidue ε ℓ n *
        saddleGaussianPoleRepresentative n z

private noncomputable def minusSaddleFiniteRapidPoleSubtraction
    (ε ℓ : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  minusSaddleMellinData ε ℓ z -
    ∑ n ∈ Finset.range (N + 1),
      minusSaddlePoleResidue ε ℓ n *
        saddleGaussianPoleRepresentative n z

private noncomputable def plusSaddleFiniteRapidPoleRegularPart
    (ε ℓ : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  plusSaddleFinitePoleRegularPart ε ℓ N z -
    ∑ n ∈ Finset.range (N + 1),
      plusSaddlePoleResidue ε ℓ n *
        saddleGaussianPoleSlope
          (z + ((2 * n : ℕ) : ℂ))

private noncomputable def minusSaddleFiniteRapidPoleRegularPart
    (ε ℓ : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  minusSaddleFinitePoleRegularPart ε ℓ N z -
    ∑ n ∈ Finset.range (N + 1),
      minusSaddlePoleResidue ε ℓ n *
        saddleGaussianPoleSlope
          (z + ((2 * n : ℕ) : ℂ))

private theorem plusSaddleFiniteRapidPoleRegularPart_differentiableOn
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) (N : ℕ) :
    DifferentiableOn ℂ
      (plusSaddleFiniteRapidPoleRegularPart ε ℓ N)
      (saddleFinitePoleHalfPlane N) := by
  unfold plusSaddleFiniteRapidPoleRegularPart
  apply (plusSaddleFinitePoleRegularPart_differentiableOn
    hε horder ℓ N).sub
  apply DifferentiableOn.fun_sum
  intro n _
  have hconstant : DifferentiableOn ℂ
      (fun _ : ℂ => plusSaddlePoleResidue ε ℓ n)
      (saddleFinitePoleHalfPlane N) := by
    fun_prop
  have hslope : Differentiable ℂ
      (fun z : ℂ => saddleGaussianPoleSlope
        (z + ((2 * n : ℕ) : ℂ))) :=
    saddleGaussianPoleSlope_differentiable.comp (by fun_prop)
  exact hconstant.mul hslope.differentiableOn

private theorem minusSaddleFiniteRapidPoleRegularPart_differentiableOn
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) (N : ℕ) :
    DifferentiableOn ℂ
      (minusSaddleFiniteRapidPoleRegularPart ε ℓ N)
      (saddleFinitePoleHalfPlane N) := by
  unfold minusSaddleFiniteRapidPoleRegularPart
  apply (minusSaddleFinitePoleRegularPart_differentiableOn
    hε horder ℓ N).sub
  apply DifferentiableOn.fun_sum
  intro n _
  have hconstant : DifferentiableOn ℂ
      (fun _ : ℂ => minusSaddlePoleResidue ε ℓ n)
      (saddleFinitePoleHalfPlane N) := by
    fun_prop
  have hslope : Differentiable ℂ
      (fun z : ℂ => saddleGaussianPoleSlope
        (z + ((2 * n : ℕ) : ℂ))) :=
    saddleGaussianPoleSlope_differentiable.comp (by fun_prop)
  exact hconstant.mul hslope.differentiableOn

private theorem plusSaddleFiniteRapidPoleRegularPart_eq_subtraction_of_not_pole
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) (N : ℕ) {z : ℂ}
    (hz : z ∈ saddleFinitePoleHalfPlane N)
    (hpole : ∀ n : ℕ,
      z ≠ (-((2 * n : ℕ) : ℂ))) :
    plusSaddleFiniteRapidPoleRegularPart ε ℓ N z =
      plusSaddleFiniteRapidPoleSubtraction ε ℓ N z := by
  unfold plusSaddleFiniteRapidPoleRegularPart
    plusSaddleFiniteRapidPoleSubtraction
  rw [plusSaddleFinitePoleRegularPart_eq_subtraction_of_not_pole
    hε horder ℓ N hz hpole]
  unfold plusSaddleFinitePoleSubtraction
  have hsum :
      (∑ n ∈ Finset.range (N + 1),
        plusSaddlePoleResidue ε ℓ n /
          (z + ((2 * n : ℕ) : ℂ))) +
      (∑ n ∈ Finset.range (N + 1),
        plusSaddlePoleResidue ε ℓ n *
          saddleGaussianPoleSlope
            (z + ((2 * n : ℕ) : ℂ))) =
      ∑ n ∈ Finset.range (N + 1),
        plusSaddlePoleResidue ε ℓ n *
          saddleGaussianPoleRepresentative n z := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    have hcoordinate :
        z + ((2 * n : ℕ) : ℂ) ≠ 0 := by
      intro hzero
      apply hpole n
      linear_combination hzero
    rw [saddleGaussianPoleSlope_eq_of_ne hcoordinate]
    unfold saddleGaussianPoleRepresentative
    field_simp [hcoordinate]
    ring
  linear_combination -hsum

private theorem minusSaddleFiniteRapidPoleRegularPart_eq_subtraction_of_not_pole
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) (N : ℕ) {z : ℂ}
    (hz : z ∈ saddleFinitePoleHalfPlane N)
    (hpole : ∀ n : ℕ,
      z ≠ (-((2 * n : ℕ) : ℂ))) :
    minusSaddleFiniteRapidPoleRegularPart ε ℓ N z =
      minusSaddleFiniteRapidPoleSubtraction ε ℓ N z := by
  unfold minusSaddleFiniteRapidPoleRegularPart
    minusSaddleFiniteRapidPoleSubtraction
  rw [minusSaddleFinitePoleRegularPart_eq_subtraction_of_not_pole
    hε horder ℓ N hz hpole]
  unfold minusSaddleFinitePoleSubtraction
  have hsum :
      (∑ n ∈ Finset.range (N + 1),
        minusSaddlePoleResidue ε ℓ n /
          (z + ((2 * n : ℕ) : ℂ))) +
      (∑ n ∈ Finset.range (N + 1),
        minusSaddlePoleResidue ε ℓ n *
          saddleGaussianPoleSlope
            (z + ((2 * n : ℕ) : ℂ))) =
      ∑ n ∈ Finset.range (N + 1),
        minusSaddlePoleResidue ε ℓ n *
          saddleGaussianPoleRepresentative n z := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    have hcoordinate :
        z + ((2 * n : ℕ) : ℂ) ≠ 0 := by
      intro hzero
      apply hpole n
      linear_combination hzero
    rw [saddleGaussianPoleSlope_eq_of_ne hcoordinate]
    unfold saddleGaussianPoleRepresentative
    field_simp [hcoordinate]
    ring
  linear_combination -hsum

private noncomputable def plusSaddleFiniteRapidContourIntegrand
    (ε ℓ : ℝ) (N : ℕ) (r : ℝ) (z : ℂ) : ℂ :=
  saddleMellinInversePower r z *
    plusSaddleFiniteRapidPoleRegularPart ε ℓ N z

private noncomputable def minusSaddleFiniteRapidContourIntegrand
    (ε ℓ : ℝ) (N : ℕ) (r : ℝ) (z : ℂ) : ℂ :=
  saddleMellinInversePower r z *
    minusSaddleFiniteRapidPoleRegularPart ε ℓ N z

private theorem plusSaddleFiniteRapidContourIntegrand_differentiableOn
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) (N : ℕ) {r : ℝ} (hr : 0 < r) :
    DifferentiableOn ℂ
      (plusSaddleFiniteRapidContourIntegrand ε ℓ N r)
      (saddleFinitePoleHalfPlane N) := by
  unfold plusSaddleFiniteRapidContourIntegrand
  exact (saddleMellinInversePower_differentiable hr).differentiableOn.mul
    (plusSaddleFiniteRapidPoleRegularPart_differentiableOn
      hε horder ℓ N)

private theorem minusSaddleFiniteRapidContourIntegrand_differentiableOn
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) (N : ℕ) {r : ℝ} (hr : 0 < r) :
    DifferentiableOn ℂ
      (minusSaddleFiniteRapidContourIntegrand ε ℓ N r)
      (saddleFinitePoleHalfPlane N) := by
  unfold minusSaddleFiniteRapidContourIntegrand
  exact (saddleMellinInversePower_differentiable hr).differentiableOn.mul
    (minusSaddleFiniteRapidPoleRegularPart_differentiableOn
      hε horder ℓ N)

private theorem plusSaddleFiniteRapidContourIntegrand_boundary_rectangle
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) (N : ℕ) {r : ℝ} (hr : 0 < r)
    (z w : ℂ)
    (hz : z ∈ saddleFinitePoleHalfPlane N)
    (hw : w ∈ saddleFinitePoleHalfPlane N) :
    (∫ x : ℝ in z.re..w.re,
      plusSaddleFiniteRapidContourIntegrand ε ℓ N r
        (x + z.im * Complex.I)) -
    (∫ x : ℝ in z.re..w.re,
      plusSaddleFiniteRapidContourIntegrand ε ℓ N r
        (x + w.im * Complex.I)) +
    Complex.I •
      (∫ y : ℝ in z.im..w.im,
        plusSaddleFiniteRapidContourIntegrand ε ℓ N r
          (w.re + y * Complex.I)) -
    Complex.I •
      (∫ y : ℝ in z.im..w.im,
        plusSaddleFiniteRapidContourIntegrand ε ℓ N r
          (z.re + y * Complex.I)) = 0 := by
  refine Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (plusSaddleFiniteRapidContourIntegrand ε ℓ N r) z w ?_
  exact (plusSaddleFiniteRapidContourIntegrand_differentiableOn
    hε horder ℓ N hr).mono
      (saddleFinitePoleHalfPlane_reProdIm_subset hz hw)

private theorem minusSaddleFiniteRapidContourIntegrand_boundary_rectangle
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) (N : ℕ) {r : ℝ} (hr : 0 < r)
    (z w : ℂ)
    (hz : z ∈ saddleFinitePoleHalfPlane N)
    (hw : w ∈ saddleFinitePoleHalfPlane N) :
    (∫ x : ℝ in z.re..w.re,
      minusSaddleFiniteRapidContourIntegrand ε ℓ N r
        (x + z.im * Complex.I)) -
    (∫ x : ℝ in z.re..w.re,
      minusSaddleFiniteRapidContourIntegrand ε ℓ N r
        (x + w.im * Complex.I)) +
    Complex.I •
      (∫ y : ℝ in z.im..w.im,
        minusSaddleFiniteRapidContourIntegrand ε ℓ N r
          (w.re + y * Complex.I)) -
    Complex.I •
      (∫ y : ℝ in z.im..w.im,
        minusSaddleFiniteRapidContourIntegrand ε ℓ N r
          (z.re + y * Complex.I)) = 0 := by
  refine Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (minusSaddleFiniteRapidContourIntegrand ε ℓ N r) z w ?_
  exact (minusSaddleFiniteRapidContourIntegrand_differentiableOn
    hε horder ℓ N hr).mono
      (saddleFinitePoleHalfPlane_reProdIm_subset hz hw)

private theorem saddleMellinEnvelope_vertical (ε ℓ t : ℝ) :
    saddleMellinEnvelope ε ℓ
      ((ℓ : ℂ) - Complex.I * (t : ℂ)) =
        saddleEnvelope ε ℓ t := by
  have hfrequency :
      Complex.I *
        (((ℓ : ℂ) - Complex.I * (t : ℂ)) - (ℓ : ℂ)) /
          (ℓ : ℂ) = (t : ℂ) / (ℓ : ℂ) := by
    congr 1
    ring_nf
    simp only [Complex.I_sq, neg_mul, one_mul, neg_neg]
  have hpi :
      (((ℓ : ℂ) - ((ℓ : ℂ) - Complex.I * (t : ℂ))) *
        (Real.log Real.pi : ℂ) / 2) =
        Complex.I * (t : ℂ) * (Real.log Real.pi : ℂ) / 2 := by
    ring
  unfold saddleMellinEnvelope saddleEnvelope
  rw [hfrequency, hpi]

private theorem plusSaddleMellinData_vertical (ε ℓ t : ℝ) :
    plusSaddleMellinData ε ℓ
      ((ℓ : ℂ) - Complex.I * (t : ℂ)) =
        plusSaddleSpectrum ε ℓ t := by
  have hfrequency :
      Complex.I *
        (((ℓ : ℂ) - Complex.I * (t : ℂ)) - (ℓ : ℂ)) /
          (ℓ : ℂ) = (t : ℂ) / (ℓ : ℂ) := by
    congr 1
    ring_nf
    simp only [Complex.I_sq, neg_mul, one_mul, neg_neg]
  unfold plusSaddleMellinData plusSaddleSpectrum
  rw [saddleMellinEnvelope_vertical, hfrequency]

private theorem minusSaddleMellinData_vertical (ε ℓ t : ℝ) :
    minusSaddleMellinData ε ℓ
      ((ℓ : ℂ) - Complex.I * (t : ℂ)) =
        minusSaddleSpectrum ε ℓ t := by
  have hfrequency :
      Complex.I *
        (((ℓ : ℂ) - Complex.I * (t : ℂ)) - (ℓ : ℂ)) /
          (ℓ : ℂ) = (t : ℂ) / (ℓ : ℂ) := by
    congr 1
    ring_nf
    simp only [Complex.I_sq, neg_mul, one_mul, neg_neg]
  unfold minusSaddleMellinData minusSaddleSpectrum
  rw [saddleMellinEnvelope_vertical, hfrequency]

private noncomputable def plusSaddleProfile (ε ℓ r : ℝ) : ℂ :=
  if r = 0 then (saddleOriginValue ε ℓ : ℂ)
  else mellinInv ℓ (plusSaddleMellinData ε ℓ) r

private noncomputable def minusSaddleProfile (ε ℓ r : ℝ) : ℂ :=
  if r = 0 then (saddleOriginValue ε ℓ : ℂ)
  else mellinInv ℓ (minusSaddleMellinData ε ℓ) r

private noncomputable def plusSaddleFunction (ε : ℝ) (d : ℕ) (x : Euclidean d) : ℂ :=
  plusSaddleProfile ε ((d : ℝ) / 2) ‖x‖

private noncomputable def minusSaddleFunction (ε : ℝ) (d : ℕ) (x : Euclidean d) : ℂ :=
  minusSaddleProfile ε ((d : ℝ) / 2) ‖x‖

private theorem plusSaddleFunction_radial (ε : ℝ) (d : ℕ)
    (x y : Euclidean d) (hxy : ‖x‖ = ‖y‖) :
    plusSaddleFunction ε d x = plusSaddleFunction ε d y := by
  simp only [plusSaddleFunction, hxy]

private theorem minusSaddleFunction_radial (ε : ℝ) (d : ℕ)
    (x y : Euclidean d) (hxy : ‖x‖ = ‖y‖) :
    minusSaddleFunction ε d x = minusSaddleFunction ε d y := by
  simp only [minusSaddleFunction, hxy]

@[simp] private theorem plusSaddleFunction_zero (ε : ℝ) (d : ℕ) :
    plusSaddleFunction ε d (0 : Euclidean d) =
      (saddleOriginValue ε ((d : ℝ) / 2) : ℂ) := by
  simp only [plusSaddleFunction, plusSaddleProfile, norm_zero, ↓reduceIte]

@[simp] private theorem minusSaddleFunction_zero (ε : ℝ) (d : ℕ) :
    minusSaddleFunction ε d (0 : Euclidean d) =
      (saddleOriginValue ε ((d : ℝ) / 2) : ℂ) := by
  simp only [minusSaddleFunction, minusSaddleProfile, norm_zero, ↓reduceIte]

private theorem saddleFunction_zero_pos {ε : ℝ} (hε : 0 < ε) (d : ℕ) :
    0 < (plusSaddleFunction ε d (0 : Euclidean d)).re ∧
      0 < (minusSaddleFunction ε d (0 : Euclidean d)).re := by
  constructor
  · simpa only [plusSaddleFunction_zero,
    Complex.ofReal_re] using! saddleOriginValue_pos hε ((d : ℝ) / 2)
  · simpa only [minusSaddleFunction_zero,
    Complex.ofReal_re] using! saddleOriginValue_pos hε ((d : ℝ) / 2)

private theorem minusPolynomial_neg (ε : ℝ) (z : ℂ) :
    minusPolynomial ε (-z) = plusPolynomial ε z := by
  unfold minusPolynomial plusPolynomial
  ring

private theorem plusPolynomial_conj (ε : ℝ) (z : ℂ) :
    starRingEnd ℂ (plusPolynomial ε z) =
      minusPolynomial ε (starRingEnd ℂ z) := by
  unfold plusPolynomial minusPolynomial
  simp only [map_add, map_mul, map_pow, map_one,
    Complex.conj_ofReal, Complex.conj_I]
  ring

private theorem minusPolynomial_conj (ε : ℝ) (z : ℂ) :
    starRingEnd ℂ (minusPolynomial ε z) =
      plusPolynomial ε (starRingEnd ℂ z) := by
  unfold minusPolynomial plusPolynomial
  simp only [map_add, map_sub, map_mul, map_pow, map_one,
    Complex.conj_ofReal, Complex.conj_I]
  ring

private theorem norm_plusPolynomial_le (ε : ℝ) (z : ℂ) :
    ‖plusPolynomial ε z‖ ≤
      (1 + |(ε / 4)|) * (1 + ‖z‖) ^ 3 := by
  have hz : 0 ≤ ‖z‖ := norm_nonneg _
  have hbase : ‖(1 : ℂ) + z ^ 2‖ ≤ 1 + ‖z‖ ^ 2 := by
    calc
      ‖(1 : ℂ) + z ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ 2‖ :=
        norm_add_le _ _
      _ = 1 + ‖z‖ ^ 2 := by simp only [norm_one, norm_pow]
  have hsq : 1 + ‖z‖ ^ 2 ≤ (1 + ‖z‖) ^ 2 := by
    linarith
  have hcube : (1 : ℝ) ≤ (1 + ‖z‖) ^ 3 :=
    one_le_pow₀ (by linarith)
  unfold plusPolynomial
  calc
    ‖1 + z ^ 2 + ((ε / 4 : ℝ) : ℂ) +
      Complex.I * z * (1 + z ^ 2)‖
      ≤ ‖1 + z ^ 2 + ((ε / 4 : ℝ) : ℂ)‖ +
          ‖Complex.I * z * (1 + z ^ 2)‖ :=
            norm_add_le _ _
    _ ≤ (1 + ‖z‖ ^ 2 + |(ε / 4)|) +
          ‖z‖ * (1 + ‖z‖ ^ 2) := by
            have hfirst :
                ‖1 + z ^ 2 + ((ε / 4 : ℝ) : ℂ)‖ ≤
                  1 + ‖z‖ ^ 2 + |(ε / 4)| := by
              calc
                ‖1 + z ^ 2 + ((ε / 4 : ℝ) : ℂ)‖ ≤
                    ‖1 + z ^ 2‖ + ‖((ε / 4 : ℝ) : ℂ)‖ :=
                      norm_add_le _ _
                _ ≤ 1 + ‖z‖ ^ 2 + |(ε / 4)| := by
                      simpa only [Complex.norm_real, Real.norm_eq_abs, add_le_add_iff_right,
                        add_le_add_iff_left] using! add_le_add_right hbase |(ε / 4)|
            have hsecond :
                ‖Complex.I * z * (1 + z ^ 2)‖ ≤
                  ‖z‖ * (1 + ‖z‖ ^ 2) := by
              rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
              gcongr
            exact add_le_add hfirst hsecond
    _ ≤ (1 + ‖z‖) ^ 2 + |(ε / 4)| +
          ‖z‖ * (1 + ‖z‖) ^ 2 := by
            gcongr
    _ = (1 + ‖z‖) ^ 3 + |(ε / 4)| := by ring
    _ ≤ (1 + |(ε / 4)|) * (1 + ‖z‖) ^ 3 := by
          linarith [mul_le_mul_of_nonneg_left hcube
            (abs_nonneg (ε / 4))]

private theorem norm_minusPolynomial_le (ε : ℝ) (z : ℂ) :
    ‖minusPolynomial ε z‖ ≤
      (1 + |(ε / 4)|) * (1 + ‖z‖) ^ 3 := by
  have h := norm_plusPolynomial_le ε (starRingEnd ℂ z)
  rw [RCLike.norm_conj] at h
  have hconj := plusPolynomial_conj ε (starRingEnd ℂ z)
  rw [Complex.conj_conj] at hconj
  rw [← hconj, RCLike.norm_conj]
  exact h

private theorem norm_complexGamma_le_realGamma {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral,
    Real.Gamma_eq_integral hz]
  calc
    ‖∫ x in Set.Ioi (0 : ℝ),
      (Real.exp (-x) : ℂ) * (x : ℂ) ^ (z - 1)‖
      ≤ ∫ x in Set.Ioi (0 : ℝ),
          ‖(Real.exp (-x) : ℂ) * (x : ℂ) ^ (z - 1)‖ :=
            norm_integral_le_integral_norm _
    _ = ∫ x in Set.Ioi (0 : ℝ),
          Real.exp (-x) * x ^ (z.re - 1) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro x hx
            try dsimp
            rw [norm_mul,
              Complex.norm_of_nonneg (Real.exp_pos (-x)).le,
              Complex.norm_cpow_eq_rpow_re_of_pos hx]
            simp only [Complex.sub_re, Complex.one_re]

private theorem complexGamma_vertical_polynomial_bound {z : ℂ}
    (hz : 0 < z.re) (k : ℕ) :
    |z.im| ^ k * ‖Complex.Gamma z‖ ≤
      Real.Gamma (z.re + k) := by
  have hnonzero : ∀ j : ℕ, z + (j : ℂ) ≠ 0 := by
    intro j hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hprod :
      |z.im| ^ k ≤
        ∏ j ∈ Finset.range k, ‖z + (j : ℂ)‖ := by
    simpa only [Finset.prod_const, Finset.card_range] using!
      (Finset.prod_le_prod
        (s := Finset.range k)
        (f := fun _ : ℕ => |z.im|)
        (g := fun j : ℕ => ‖z + (j : ℂ)‖)
        (fun _ _ => abs_nonneg _)
        (fun j _ => by
          simpa only [Complex.add_im, Complex.natCast_im,
            add_zero] using! Complex.abs_im_le_norm (z + (j : ℂ))))
  have hshift : 0 < (z + (k : ℂ)).re := by
    simpa only [Complex.add_re,
      Complex.natCast_re] using! add_pos_of_pos_of_nonneg hz (Nat.cast_nonneg k)
  calc
    |z.im| ^ k * ‖Complex.Gamma z‖ ≤
        (∏ j ∈ Finset.range k, ‖z + (j : ℂ)‖) *
          ‖Complex.Gamma z‖ := by
            gcongr
    _ = ‖Complex.Gamma z *
          ∏ j ∈ Finset.range k, (z + (j : ℂ))‖ := by
            rw [norm_mul, norm_prod]
            ring
    _ = ‖Complex.Gamma (z + (k : ℂ))‖ := by
            rw [gamma_add_nat_eq_product z hnonzero k]
    _ ≤ Real.Gamma (z.re + k) := by
            simpa only [Complex.add_re,
              Complex.natCast_re] using! norm_complexGamma_le_realGamma hshift

private theorem complexGamma_shifted_vertical_polynomial_bound
    {z : ℂ} (hz : z.im ≠ 0) (k : ℕ)
    (hshift : 0 < z.re + k) :
    |z.im| ^ k * ‖Complex.Gamma z‖ ≤
      Real.Gamma (z.re + k) := by
  have hnonzero : ∀ j : ℕ, z + (j : ℂ) ≠ 0 := by
    intro j hzero
    apply hz
    have him := congrArg Complex.im hzero
    simpa only [Complex.add_im, Complex.natCast_im, add_zero, Complex.zero_im] using! him
  have hprod :
      |z.im| ^ k ≤
        ∏ j ∈ Finset.range k, ‖z + (j : ℂ)‖ := by
    simpa only [Finset.prod_const, Finset.card_range] using!
      (Finset.prod_le_prod
        (s := Finset.range k)
        (f := fun _ : ℕ => |z.im|)
        (g := fun j : ℕ => ‖z + (j : ℂ)‖)
        (fun _ _ => abs_nonneg _)
        (fun j _ => by
          simpa only [Complex.add_im, Complex.natCast_im,
            add_zero] using! Complex.abs_im_le_norm (z + (j : ℂ))))
  have hpositive : 0 < (z + (k : ℂ)).re := by
    simpa only [Complex.add_re, Complex.natCast_re] using! hshift
  calc
    |z.im| ^ k * ‖Complex.Gamma z‖ ≤
        (∏ j ∈ Finset.range k, ‖z + (j : ℂ)‖) *
          ‖Complex.Gamma z‖ := by
            gcongr
    _ = ‖Complex.Gamma z *
          ∏ j ∈ Finset.range k, (z + (j : ℂ))‖ := by
            rw [norm_mul, norm_prod]
            ring
    _ = ‖Complex.Gamma (z + (k : ℂ))‖ := by
            rw [gamma_add_nat_eq_product z hnonzero k]
    _ ≤ Real.Gamma (z.re + k) := by
            simpa only [Complex.add_re,
              Complex.natCast_re] using! norm_complexGamma_le_realGamma hpositive

private theorem saddleGamma_shiftedLine_polynomial_bound
    (a : ℝ) {t : ℝ} (ht : 1 ≤ |t|)
    (k m : ℕ) (hshift : 0 < a / 2 + (k : ℝ)) :
    |t| ^ m *
        ‖Complex.Gamma
          (((a : ℂ) + (t : ℂ) * Complex.I) / 2)‖ ≤
      (2 : ℝ) ^ (k + m) *
        Real.Gamma (a / 2 + ((k + m : ℕ) : ℝ)) := by
  let z : ℂ :=
    ((a : ℂ) + (t : ℂ) * Complex.I) / 2
  have hre : z.re = a / 2 := by
    try dsimp [z]
    norm_num [Complex.mul_re, Complex.mul_im]
  have him : z.im = t / 2 := by
    try dsimp [z]
    norm_num [Complex.mul_re, Complex.mul_im]
  have htzero : t ≠ 0 := by
    intro hzero
    have himpossible : (1 : ℝ) ≤ 0 := by
      simpa only [hzero, abs_zero] using! ht
    norm_num at himpossible
  have hnonzero : z.im ≠ 0 := by
    rw [him]
    exact div_ne_zero htzero (by norm_num)
  have hpositive :
      0 < z.re + ((k + m : ℕ) : ℝ) := by
    rw [hre, Nat.cast_add]
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hgamma :
      (|t| / 2) ^ (k + m) *
          ‖Complex.Gamma z‖ ≤
        Real.Gamma
          (a / 2 + ((k + m : ℕ) : ℝ)) := by
    simpa only [Nat.cast_add, him, abs_div, Nat.abs_ofNat, hre] using!
      (complexGamma_shifted_vertical_polynomial_bound
        hnonzero (k + m) hpositive)
  have hpow : |t| ^ m ≤ |t| ^ (k + m) :=
    pow_le_pow_right₀ ht (by omega)
  change |t| ^ m * ‖Complex.Gamma z‖ ≤ _
  calc
    |t| ^ m * ‖Complex.Gamma z‖ ≤
        |t| ^ (k + m) * ‖Complex.Gamma z‖ := by
          gcongr
    _ = (2 : ℝ) ^ (k + m) *
          ((|t| / 2) ^ (k + m) *
            ‖Complex.Gamma z‖) := by
          rw [div_pow]
          field_simp
    _ ≤ (2 : ℝ) ^ (k + m) *
          Real.Gamma
            (a / 2 + ((k + m : ℕ) : ℝ)) := by
          gcongr

private theorem norm_complexCos_le_cosh_im (z : ℂ) :
    ‖Complex.cos z‖ ≤ Real.cosh z.im := by
  change
    ‖(Complex.exp (z * Complex.I) +
      Complex.exp (-z * Complex.I)) / 2‖ ≤ Real.cosh z.im
  calc
    ‖(Complex.exp (z * Complex.I) +
      Complex.exp (-z * Complex.I)) / 2‖ =
        ‖Complex.exp (z * Complex.I) +
          Complex.exp (-z * Complex.I)‖ / 2 := by
            rw [norm_div]
            norm_num
    _ ≤ (‖Complex.exp (z * Complex.I)‖ +
          ‖Complex.exp (-z * Complex.I)‖) / 2 := by
            gcongr
            exact norm_add_le _ _
    _ = Real.cosh z.im := by
          rw [Complex.norm_exp, Complex.norm_exp,
            Real.cosh_eq]
          simp only [Complex.mul_re, Complex.I_re, mul_zero, Complex.I_im, mul_one, zero_sub,
            neg_mul, Complex.neg_re,
            neg_neg, add_comm]

private noncomputable def saddleHorizontalShellVariation (ε H : ℝ) : ℝ :=
  (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
    |shortShellDensity ε a| * (Real.cosh (a * H) + 1)) +
  (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
    |positiveShellDensity ε a| * (Real.cosh (a * H) + 1))

private theorem saddleHorizontalShellVariation_mono
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    {H K : ℝ} (hH : 0 ≤ H) (hHK : H ≤ K) :
    saddleHorizontalShellVariation ε H ≤
      saddleHorizontalShellVariation ε K := by
  have hK : 0 ≤ K := hH.trans hHK
  have hcosH : Continuous
      (fun a : ℝ => Real.cosh (a * H) + 1) := by
    fun_prop
  have hcosK : Continuous
      (fun a : ℝ => Real.cosh (a * K) + 1) := by
    fun_prop
  have hcos (a : ℝ) :
      Real.cosh (a * H) ≤ Real.cosh (a * K) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_mul, abs_mul, abs_of_nonneg hH,
      abs_of_nonneg hK]
    exact mul_le_mul_of_nonneg_left hHK (abs_nonneg a)
  have hshort :
      (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
        |shortShellDensity ε a| *
          (Real.cosh (a * H) + 1)) ≤
      (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
        |shortShellDensity ε a| *
          (Real.cosh (a * K) + 1)) := by
    apply intervalIntegral.integral_mono_on horder
      ((shortShellDensity_intervalIntegrable hε horder).abs
        |>.mul_continuousOn hcosH.continuousOn)
      ((shortShellDensity_intervalIntegrable hε horder).abs
        |>.mul_continuousOn hcosK.continuousOn)
    intro a _
    gcongr
    exact hcos a
  have hB : (ε⁻¹ ^ 3) ≤ (ε⁻¹ ^ 3) + 1 := by
    linarith
  have hp : IntervalIntegrable (positiveShellDensity ε) volume
      (ε⁻¹ ^ 3) ((ε⁻¹ ^ 3) + 1) :=
    (positiveShellDensity_continuous ε).intervalIntegrable
      (ε⁻¹ ^ 3) ((ε⁻¹ ^ 3) + 1)
  have hpositive :
      (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
        |positiveShellDensity ε a| *
          (Real.cosh (a * H) + 1)) ≤
      (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
        |positiveShellDensity ε a| *
          (Real.cosh (a * K) + 1)) := by
    apply intervalIntegral.integral_mono_on hB
      (hp.abs.mul_continuousOn hcosH.continuousOn)
      (hp.abs.mul_continuousOn hcosK.continuousOn)
    intro a _
    gcongr
    exact hcos a
  exact add_le_add hshort hpositive

private theorem norm_mellinShellPhase_le_horizontalVariation
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    {z : ℂ} {H : ℝ} (hstrip : |z.im| ≤ H) :
    ‖mellinShellPhase ε z‖ ≤
      saddleHorizontalShellVariation ε H := by
  have hH : 0 ≤ H := (abs_nonneg z.im).trans hstrip
  have hcutoff : 0 < (ε ^ 3) := by
    positivity
  have hlocation : 0 < (ε⁻¹ ^ 3) := by
    positivity
  have hcosh : Continuous
      (fun a : ℝ => Real.cosh (a * H) + 1) := by
    fun_prop
  have hcos (a : ℝ) (ha : 0 ≤ a) :
      ‖Complex.cos ((a : ℂ) * z) - 1‖ ≤
        Real.cosh (a * H) + 1 := by
    have him :
        |((a : ℂ) * z).im| ≤ |a * H| := by
      simp only [Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, abs_mul,
        abs_of_nonneg ha, abs_of_nonneg hH]
      exact mul_le_mul_of_nonneg_left hstrip ha
    calc
      ‖Complex.cos ((a : ℂ) * z) - 1‖ ≤
          ‖Complex.cos ((a : ℂ) * z)‖ + ‖(1 : ℂ)‖ :=
            norm_sub_le _ _
      _ = ‖Complex.cos ((a : ℂ) * z)‖ + 1 := by
            norm_num
      _ ≤ Real.cosh ((a : ℂ) * z).im + 1 := by
            gcongr
            exact norm_complexCos_le_cosh_im ((a : ℂ) * z)
      _ ≤ Real.cosh (a * H) + 1 := by
            gcongr
            exact Real.cosh_le_cosh.mpr him
  have hshort :
      ‖∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
          (shortShellDensity ε a : ℂ) *
            (Complex.cos ((a : ℂ) * z) - 1)‖ ≤
        ∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
          |shortShellDensity ε a| *
            (Real.cosh (a * H) + 1) := by
    apply intervalIntegral.norm_integral_le_of_norm_le horder
    · exact Filter.Eventually.of_forall (fun a ha => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (hcos a (hcutoff.le.trans ha.1.le))
          (abs_nonneg (shortShellDensity ε a)))
    · exact (shortShellDensity_intervalIntegrable
        hε horder).abs.mul_continuousOn hcosh.continuousOn
  have hB : (ε⁻¹ ^ 3) ≤ (ε⁻¹ ^ 3) + 1 := by
    linarith
  have hpositive :
      ‖∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
          (positiveShellDensity ε a : ℂ) *
            (Complex.cos ((a : ℂ) * z) - 1)‖ ≤
        ∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
          |positiveShellDensity ε a| *
            (Real.cosh (a * H) + 1) := by
    apply intervalIntegral.norm_integral_le_of_norm_le hB
    · exact Filter.Eventually.of_forall (fun a ha => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (hcos a (hlocation.le.trans ha.1.le))
          (abs_nonneg (positiveShellDensity ε a)))
    · exact ((positiveShellDensity_continuous ε).intervalIntegrable
        (ε⁻¹ ^ 3) ((ε⁻¹ ^ 3) + 1)).abs.mul_continuousOn
          hcosh.continuousOn
  unfold mellinShellPhase saddleHorizontalShellVariation
  exact (norm_add_le _ _).trans (add_le_add hshort hpositive)

private theorem norm_saddleShellExponential_horizontal_le
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ) (z : ℂ) :
    ‖Complex.exp ((ℓ : ℂ) * mellinShellPhase ε z)‖ ≤
      Real.exp
        (|ℓ| * saddleHorizontalShellVariation ε |z.im|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    (((ℓ : ℂ) * mellinShellPhase ε z)).re ≤
        ‖(ℓ : ℂ) * mellinShellPhase ε z‖ :=
          Complex.re_le_norm _
    _ = |ℓ| * ‖mellinShellPhase ε z‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |ℓ| * saddleHorizontalShellVariation ε |z.im| := by
          gcongr
          exact norm_mellinShellPhase_le_horizontalVariation
            hε horder (le_refl |z.im|)

private theorem saddleMellinShellArgument_shiftedLine
    {ℓ : ℝ} (hℓ : 0 < ℓ) (a t : ℝ) :
    Complex.I *
      (((a : ℂ) + (t : ℂ) * Complex.I) -
        (ℓ : ℂ)) / (ℓ : ℂ) =
      ((-t / ℓ : ℝ) : ℂ) +
        Complex.I * (((a - ℓ) / ℓ : ℝ) : ℂ) := by
  have hnonzero : (ℓ : ℂ) ≠ 0 := by
    exact_mod_cast hℓ.ne'
  push_cast
  field_simp [hnonzero]
  ring_nf
  simp only [Complex.I_sq, neg_mul, one_mul]; ring

private theorem saddleMellinPiFactor_shiftedLine_norm
    (ℓ a t : ℝ) :
    ‖Complex.exp
      (((ℓ : ℂ) -
          ((a : ℂ) + (t : ℂ) * Complex.I)) *
        (Real.log Real.pi : ℂ) / 2)‖ =
      Real.exp ((ℓ - a) * Real.log Real.pi / 2) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.div_ofNat_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
    Complex.add_re,
    Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero,
      Complex.sub_im,
    Complex.add_im, Complex.mul_im, zero_add, zero_sub, sub_zero]

private theorem norm_saddleShellExponential_shiftedLine_le
    {ε ℓ : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (a t : ℝ) :
    ‖Complex.exp
      ((ℓ : ℂ) * mellinShellPhase ε
        (Complex.I *
          (((a : ℂ) + (t : ℂ) * Complex.I) -
            (ℓ : ℂ)) / (ℓ : ℂ)))‖ ≤
      Real.exp
        (ℓ * saddleHorizontalShellVariation ε
          |(a - ℓ) / ℓ|) := by
  calc
    _ ≤ Real.exp
        (|ℓ| * saddleHorizontalShellVariation ε
          |(Complex.I *
            (((a : ℂ) + (t : ℂ) * Complex.I) -
              (ℓ : ℂ)) / (ℓ : ℂ)).im|) :=
      norm_saddleShellExponential_horizontal_le
        hε horder ℓ _
    _ = _ := by
      rw [saddleMellinShellArgument_shiftedLine hℓ a t]
      simp only [abs_of_pos hℓ, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_sub,
        Complex.add_im,
        Complex.div_ofReal_im, Complex.neg_im, Complex.ofReal_im, neg_zero, zero_div,
          Complex.mul_im, Complex.I_re,
        Complex.sub_im, sub_self, mul_zero, Complex.I_im, Complex.div_ofReal_re, Complex.sub_re,
          Complex.ofReal_re, one_mul,
        zero_add]

private theorem saddleMellinShellArgument_shiftedLine_norm_le
    {ℓ : ℝ} (hℓ : 0 < ℓ) (a t : ℝ) :
    ‖Complex.I *
      (((a : ℂ) + (t : ℂ) * Complex.I) -
        (ℓ : ℂ)) / (ℓ : ℂ)‖ ≤
      |t| / ℓ + |(a - ℓ) / ℓ| := by
  rw [saddleMellinShellArgument_shiftedLine hℓ a t]
  calc
    ‖((-t / ℓ : ℝ) : ℂ) +
      Complex.I * (((a - ℓ) / ℓ : ℝ) : ℂ)‖ ≤
        ‖((-t / ℓ : ℝ) : ℂ)‖ +
          ‖Complex.I *
            (((a - ℓ) / ℓ : ℝ) : ℂ)‖ :=
      norm_add_le _ _
    _ = |t| / ℓ + |(a - ℓ) / ℓ| := by
      simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.norm_div, norm_neg,
        Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hℓ, Complex.ofReal_sub, Complex.norm_mul, Complex.norm_I,
          one_mul, abs_div,
        add_right_inj]
      rw [← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs]

private theorem saddleMellinShellArgument_shiftedLine_linear_le
    {ℓ : ℝ} (hℓ : 0 < ℓ)
    (a : ℝ) {t : ℝ} (ht : 1 ≤ |t|) :
    1 + ‖Complex.I *
      (((a : ℂ) + (t : ℂ) * Complex.I) -
        (ℓ : ℂ)) / (ℓ : ℂ)‖ ≤
      (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) * |t| := by
  have hargument :=
    saddleMellinShellArgument_shiftedLine_norm_le
      hℓ a t
  have hoffset := mul_le_mul_of_nonneg_left ht
    (abs_nonneg ((a - ℓ) / ℓ))
  calc
    _ ≤ 1 + (|t| / ℓ + |(a - ℓ) / ℓ|) := by
      gcongr
    _ ≤ |t| + |t| / ℓ +
          |(a - ℓ) / ℓ| * |t| := by
      linarith
    _ = _ := by
      rw [div_eq_mul_inv]
      ring

private theorem norm_plusPolynomial_shiftedLine_le
    {ε ℓ : ℝ} (hℓ : 0 < ℓ)
    (a : ℝ) {t : ℝ} (ht : 1 ≤ |t|) :
    ‖plusPolynomial ε
      (Complex.I *
        (((a : ℂ) + (t : ℂ) * Complex.I) -
          (ℓ : ℂ)) / (ℓ : ℂ))‖ ≤
      (1 + |(ε / 4)|) *
        (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) ^ 3 *
          |t| ^ 3 := by
  calc
    _ ≤ (1 + |(ε / 4)|) *
      (1 + ‖Complex.I *
        (((a : ℂ) + (t : ℂ) * Complex.I) -
          (ℓ : ℂ)) / (ℓ : ℂ)‖) ^ 3 :=
      norm_plusPolynomial_le ε _
    _ ≤ (1 + |(ε / 4)|) *
      ((1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) * |t|) ^ 3 := by
      gcongr
      exact saddleMellinShellArgument_shiftedLine_linear_le
        hℓ a ht
    _ = _ := by
      rw [mul_pow]
      ring

private theorem norm_minusPolynomial_shiftedLine_le
    {ε ℓ : ℝ} (hℓ : 0 < ℓ)
    (a : ℝ) {t : ℝ} (ht : 1 ≤ |t|) :
    ‖minusPolynomial ε
      (Complex.I *
        (((a : ℂ) + (t : ℂ) * Complex.I) -
          (ℓ : ℂ)) / (ℓ : ℂ))‖ ≤
      (1 + |(ε / 4)|) *
        (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) ^ 3 *
          |t| ^ 3 := by
  calc
    _ ≤ (1 + |(ε / 4)|) *
      (1 + ‖Complex.I *
        (((a : ℂ) + (t : ℂ) * Complex.I) -
          (ℓ : ℂ)) / (ℓ : ℂ)‖) ^ 3 :=
      norm_minusPolynomial_le ε _
    _ ≤ (1 + |(ε / 4)|) *
      ((1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) * |t|) ^ 3 := by
      gcongr
      exact saddleMellinShellArgument_shiftedLine_linear_le
        hℓ a ht
    _ = _ := by
      rw [mul_pow]
      ring

private noncomputable def saddleShiftedLineMajorant
    (ε ℓ a : ℝ) (k m : ℕ) : ℝ :=
  ((1 + |(ε / 4)|) *
      (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) ^ 3) *
    ((2 : ℝ) ^ (k + (m + 3)) *
      Real.Gamma
        (a / 2 + ((k + (m + 3) : ℕ) : ℝ))) *
    Real.exp ((ℓ - a) * Real.log Real.pi / 2) *
    Real.exp
      (ℓ * saddleHorizontalShellVariation ε
        |(a - ℓ) / ℓ|)

private theorem saddleShiftedLineMajorant_nonneg
    {ε ℓ a : ℝ} (hℓ : 0 < ℓ)
    (k m : ℕ) (hshift : 0 < a / 2 + (k : ℝ)) :
    0 ≤ saddleShiftedLineMajorant ε ℓ a k m := by
  have hgammaarg :
      0 < a / 2 + ((k + (m + 3) : ℕ) : ℝ) := by
    rw [Nat.cast_add]
    have hm : (0 : ℝ) ≤ ((m + 3 : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    linarith
  unfold saddleShiftedLineMajorant
  positivity [Real.Gamma_pos_of_pos hgammaarg]

private theorem plusSaddleMellinData_shiftedLine_polynomial_bound
    {ε ℓ : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (a : ℝ) {t : ℝ} (ht : 1 ≤ |t|)
    (k m : ℕ) (hshift : 0 < a / 2 + (k : ℝ)) :
    |t| ^ m *
      ‖plusSaddleMellinData ε ℓ
        ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      saddleShiftedLineMajorant ε ℓ a k m := by
  let z : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
  let q : ℂ :=
    Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ)
  let C : ℝ :=
    (1 + |(ε / 4)|) *
      (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) ^ 3
  let G : ℝ :=
    (2 : ℝ) ^ (k + (m + 3)) *
      Real.Gamma
        (a / 2 + ((k + (m + 3) : ℕ) : ℝ))
  have hC : 0 ≤ C := by
    try dsimp [C]
    positivity
  have hgammaarg :
      0 < a / 2 + ((k + (m + 3) : ℕ) : ℝ) := by
    rw [Nat.cast_add]
    have hm : (0 : ℝ) ≤ ((m + 3 : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    linarith
  have hG : 0 ≤ G := by
    try dsimp [G]
    positivity [Real.Gamma_pos_of_pos hgammaarg]
  have hgamma :
      |t| ^ (m + 3) *
          ‖Complex.Gamma (z / 2)‖ ≤ G := by
    simpa [z, G] using!
      (saddleGamma_shiftedLine_polynomial_bound
        a ht k (m + 3) hshift)
  have hpoly :
      ‖plusPolynomial ε q‖ ≤ C * |t| ^ 3 := by
    simpa only  using!
      (norm_plusPolynomial_shiftedLine_le
        (ε := ε) hℓ a ht)
  have hpi :
      ‖Complex.exp
        (((ℓ : ℂ) - z) *
          (Real.log Real.pi : ℂ) / 2)‖ =
        Real.exp ((ℓ - a) * Real.log Real.pi / 2) := by
    simpa only  using!
      saddleMellinPiFactor_shiftedLine_norm ℓ a t
  have hshell :
      ‖Complex.exp
        ((ℓ : ℂ) * mellinShellPhase ε q)‖ ≤
        Real.exp
          (ℓ * saddleHorizontalShellVariation ε
            |(a - ℓ) / ℓ|) := by
    simpa only  using!
      norm_saddleShellExponential_shiftedLine_le
        hε hℓ horder a t
  change |t| ^ m *
    ‖plusSaddleMellinData ε ℓ z‖ ≤ _
  calc
    |t| ^ m * ‖plusSaddleMellinData ε ℓ z‖ =
        |t| ^ m * ‖Complex.Gamma (z / 2)‖ *
          ‖Complex.exp
            (((ℓ : ℂ) - z) *
              (Real.log Real.pi : ℂ) / 2)‖ *
          ‖Complex.exp
            ((ℓ : ℂ) * mellinShellPhase ε q)‖ *
          ‖plusPolynomial ε q‖ := by
      unfold plusSaddleMellinData saddleMellinEnvelope
      try dsimp [q]
      rw [norm_mul, norm_mul, norm_mul]
      ring
    _ ≤ |t| ^ m * ‖Complex.Gamma (z / 2)‖ *
          ‖Complex.exp
            (((ℓ : ℂ) - z) *
              (Real.log Real.pi : ℂ) / 2)‖ *
          ‖Complex.exp
            ((ℓ : ℂ) * mellinShellPhase ε q)‖ *
            (C * |t| ^ 3) := by
      gcongr
    _ = C *
          (|t| ^ (m + 3) *
            ‖Complex.Gamma (z / 2)‖) *
          ‖Complex.exp
            (((ℓ : ℂ) - z) *
              (Real.log Real.pi : ℂ) / 2)‖ *
          ‖Complex.exp
            ((ℓ : ℂ) * mellinShellPhase ε q)‖ := by
      rw [pow_add]
      ring
    _ ≤ C * G *
          ‖Complex.exp
            (((ℓ : ℂ) - z) *
              (Real.log Real.pi : ℂ) / 2)‖ *
          ‖Complex.exp
            ((ℓ : ℂ) * mellinShellPhase ε q)‖ := by
      gcongr
    _ = C * G *
          Real.exp ((ℓ - a) * Real.log Real.pi / 2) *
          ‖Complex.exp
            ((ℓ : ℂ) * mellinShellPhase ε q)‖ := by
      rw [hpi]
    _ ≤ C * G *
          Real.exp ((ℓ - a) * Real.log Real.pi / 2) *
          Real.exp
            (ℓ * saddleHorizontalShellVariation ε
              |(a - ℓ) / ℓ|) := by
      gcongr
    _ = saddleShiftedLineMajorant ε ℓ a k m := by
      rfl

private theorem minusSaddleMellinData_shiftedLine_polynomial_bound
    {ε ℓ : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (a : ℝ) {t : ℝ} (ht : 1 ≤ |t|)
    (k m : ℕ) (hshift : 0 < a / 2 + (k : ℝ)) :
    |t| ^ m *
      ‖minusSaddleMellinData ε ℓ
        ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      saddleShiftedLineMajorant ε ℓ a k m := by
  let z : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
  let q : ℂ :=
    Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ)
  let C : ℝ :=
    (1 + |(ε / 4)|) *
      (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) ^ 3
  let G : ℝ :=
    (2 : ℝ) ^ (k + (m + 3)) *
      Real.Gamma
        (a / 2 + ((k + (m + 3) : ℕ) : ℝ))
  have hC : 0 ≤ C := by
    try dsimp [C]
    positivity
  have hgammaarg :
      0 < a / 2 + ((k + (m + 3) : ℕ) : ℝ) := by
    rw [Nat.cast_add]
    have hm : (0 : ℝ) ≤ ((m + 3 : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    linarith
  have hG : 0 ≤ G := by
    try dsimp [G]
    positivity [Real.Gamma_pos_of_pos hgammaarg]
  have hgamma :
      |t| ^ (m + 3) *
          ‖Complex.Gamma (z / 2)‖ ≤ G := by
    simpa [z, G] using!
      (saddleGamma_shiftedLine_polynomial_bound
        a ht k (m + 3) hshift)
  have hpoly :
      ‖minusPolynomial ε q‖ ≤ C * |t| ^ 3 := by
    simpa only  using!
      (norm_minusPolynomial_shiftedLine_le
        (ε := ε) hℓ a ht)
  have hpi :
      ‖Complex.exp
        (((ℓ : ℂ) - z) *
          (Real.log Real.pi : ℂ) / 2)‖ =
        Real.exp ((ℓ - a) * Real.log Real.pi / 2) := by
    simpa only  using!
      saddleMellinPiFactor_shiftedLine_norm ℓ a t
  have hshell :
      ‖Complex.exp
        ((ℓ : ℂ) * mellinShellPhase ε q)‖ ≤
        Real.exp
          (ℓ * saddleHorizontalShellVariation ε
            |(a - ℓ) / ℓ|) := by
    simpa only  using!
      norm_saddleShellExponential_shiftedLine_le
        hε hℓ horder a t
  change |t| ^ m *
    ‖minusSaddleMellinData ε ℓ z‖ ≤ _
  calc
    |t| ^ m * ‖minusSaddleMellinData ε ℓ z‖ =
        |t| ^ m * ‖Complex.Gamma (z / 2)‖ *
          ‖Complex.exp
            (((ℓ : ℂ) - z) *
              (Real.log Real.pi : ℂ) / 2)‖ *
          ‖Complex.exp
            ((ℓ : ℂ) * mellinShellPhase ε q)‖ *
          ‖minusPolynomial ε q‖ := by
      unfold minusSaddleMellinData saddleMellinEnvelope
      try dsimp [q]
      rw [norm_mul, norm_mul, norm_mul]
      ring
    _ ≤ |t| ^ m * ‖Complex.Gamma (z / 2)‖ *
          ‖Complex.exp
            (((ℓ : ℂ) - z) *
              (Real.log Real.pi : ℂ) / 2)‖ *
          ‖Complex.exp
            ((ℓ : ℂ) * mellinShellPhase ε q)‖ *
            (C * |t| ^ 3) := by
      gcongr
    _ = C *
          (|t| ^ (m + 3) *
            ‖Complex.Gamma (z / 2)‖) *
          ‖Complex.exp
            (((ℓ : ℂ) - z) *
              (Real.log Real.pi : ℂ) / 2)‖ *
          ‖Complex.exp
            ((ℓ : ℂ) * mellinShellPhase ε q)‖ := by
      rw [pow_add]
      ring
    _ ≤ C * G *
          ‖Complex.exp
            (((ℓ : ℂ) - z) *
              (Real.log Real.pi : ℂ) / 2)‖ *
          ‖Complex.exp
            ((ℓ : ℂ) * mellinShellPhase ε q)‖ := by
      gcongr
    _ = C * G *
          Real.exp ((ℓ - a) * Real.log Real.pi / 2) *
          ‖Complex.exp
            ((ℓ : ℂ) * mellinShellPhase ε q)‖ := by
      rw [hpi]
    _ ≤ C * G *
          Real.exp ((ℓ - a) * Real.log Real.pi / 2) *
          Real.exp
            (ℓ * saddleHorizontalShellVariation ε
              |(a - ℓ) / ℓ|) := by
      gcongr
    _ = saddleShiftedLineMajorant ε ℓ a k m := by
      rfl

private noncomputable def saddleHorizontalStripHeight (ℓ A B : ℝ) : ℝ :=
  max |(A - ℓ) / ℓ| |(B - ℓ) / ℓ|

private theorem saddleHorizontalStripHeight_bound
    {ℓ A B x : ℝ} (hℓ : 0 < ℓ)
    (hx : x ∈ Set.Icc A B) :
    |(x - ℓ) / ℓ| ≤ saddleHorizontalStripHeight ℓ A B := by
  have hleft : (A - ℓ) / ℓ ≤ (x - ℓ) / ℓ :=
    (div_le_div_iff_of_pos_right hℓ).2
      (sub_le_sub_right hx.1 ℓ)
  have hright : (x - ℓ) / ℓ ≤ (B - ℓ) / ℓ :=
    (div_le_div_iff_of_pos_right hℓ).2
      (sub_le_sub_right hx.2 ℓ)
  unfold saddleHorizontalStripHeight
  apply (abs_le).2
  constructor
  · calc
      -(max |(A - ℓ) / ℓ| |(B - ℓ) / ℓ|) ≤
          -|(A - ℓ) / ℓ| :=
        neg_le_neg (le_max_left _ _)
      _ ≤ (A - ℓ) / ℓ :=
        neg_abs_le _
      _ ≤ (x - ℓ) / ℓ := hleft
  · calc
      (x - ℓ) / ℓ ≤ (B - ℓ) / ℓ := hright
      _ ≤ |(B - ℓ) / ℓ| := le_abs_self _
      _ ≤ max |(A - ℓ) / ℓ| |(B - ℓ) / ℓ| :=
        le_max_right _ _

private noncomputable def saddleFixedStripMajorant
    (ε ℓ H a : ℝ) (k m : ℕ) : ℝ :=
  ((1 + |(ε / 4)|) *
      (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) ^ 3) *
    ((2 : ℝ) ^ (k + (m + 3)) *
      Real.Gamma
        (a / 2 + ((k + (m + 3) : ℕ) : ℝ))) *
    Real.exp ((ℓ - a) * Real.log Real.pi / 2) *
    Real.exp
      (ℓ * saddleHorizontalShellVariation ε H)

private theorem saddleShiftedLineMajorant_le_fixedStrip
    {ε ℓ a H : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hH : |(a - ℓ) / ℓ| ≤ H)
    (k m : ℕ) (hshift : 0 < a / 2 + (k : ℝ)) :
    saddleShiftedLineMajorant ε ℓ a k m ≤
      saddleFixedStripMajorant ε ℓ H a k m := by
  have hgammaarg :
      0 < a / 2 + ((k + (m + 3) : ℕ) : ℝ) := by
    rw [Nat.cast_add]
    have hm : (0 : ℝ) ≤ ((m + 3 : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    linarith
  have hgamma :
      0 ≤ Real.Gamma
        (a / 2 + ((k + (m + 3) : ℕ) : ℝ)) :=
    (Real.Gamma_pos_of_pos hgammaarg).le
  unfold saddleShiftedLineMajorant saddleFixedStripMajorant
  gcongr
  exact saddleHorizontalShellVariation_mono
    hε horder (abs_nonneg _) hH

private theorem saddleShiftedGamma_continuousOn
    {A B : ℝ} (k m : ℕ)
    (hshift : 0 < A / 2 + (k : ℝ)) :
    ContinuousOn
      (fun a : ℝ =>
        Real.Gamma
          (a / 2 + ((k + (m + 3) : ℕ) : ℝ)))
      (Set.Icc A B) := by
  have harg : ContinuousOn
      (fun a : ℝ =>
        a / 2 + ((k + (m + 3) : ℕ) : ℝ))
      (Set.Icc A B) :=
    ((continuous_id.div_const 2).add continuous_const).continuousOn
  apply Real.differentiableOn_Gamma_Ioi.continuousOn.comp
    harg
  intro a ha
  change 0 < a / 2 + ((k + (m + 3) : ℕ) : ℝ)
  have ha' : A / 2 ≤ a / 2 := by
    linarith [ha.1]
  rw [Nat.cast_add]
  have hm : (0 : ℝ) ≤ ((m + 3 : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  linarith

private theorem saddleFixedStripMajorant_continuousOn
    {A B : ℝ} (ε ℓ H : ℝ) (k m : ℕ)
    (hshift : 0 < A / 2 + (k : ℝ)) :
    ContinuousOn
      (fun a : ℝ => saddleFixedStripMajorant ε ℓ H a k m)
      (Set.Icc A B) := by
  have hpoly : ContinuousOn
      (fun a : ℝ =>
        (1 + |(ε / 4)|) *
          (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) ^ 3)
      (Set.Icc A B) :=
    (continuous_const.mul ((continuous_const.add
      ((continuous_id.sub continuous_const).div_const ℓ).abs).pow 3)).continuousOn
  have hgamma : ContinuousOn
      (fun a : ℝ =>
        (2 : ℝ) ^ (k + (m + 3)) *
          Real.Gamma
            (a / 2 + ((k + (m + 3) : ℕ) : ℝ)))
      (Set.Icc A B) :=
    continuousOn_const.mul
      (saddleShiftedGamma_continuousOn k m hshift)
  have hpi : ContinuousOn
      (fun a : ℝ =>
        Real.exp ((ℓ - a) * Real.log Real.pi / 2))
      (Set.Icc A B) :=
    (((continuous_const.sub continuous_id).mul
      continuous_const).div_const 2).rexp.continuousOn
  have hshell : ContinuousOn
      (fun _ : ℝ =>
        Real.exp
          (ℓ * saddleHorizontalShellVariation ε H))
      (Set.Icc A B) := continuousOn_const
  exact ((hpoly.mul hgamma).mul hpi).mul hshell

private theorem plusSaddleMellinData_horizontalStrip_polynomial_bound
    {ε ℓ : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    {A B : ℝ} (hAB : A ≤ B) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ Set.Icc A B, ∀ t : ℝ,
        1 ≤ |t| →
          |t| ^ m *
            ‖plusSaddleMellinData ε ℓ
              ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨k, hk⟩ := exists_nat_gt (-(A / 2))
  have hshiftA : 0 < A / 2 + (k : ℝ) := by
    linarith
  let H : ℝ := saddleHorizontalStripHeight ℓ A B
  have hcont : ContinuousOn
      (fun a : ℝ => saddleFixedStripMajorant ε ℓ H a k m)
      (Set.Icc A B) :=
    saddleFixedStripMajorant_continuousOn
      ε ℓ H k m hshiftA
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hcont
  have hAmem : A ∈ Set.Icc A B := ⟨le_rfl, hAB⟩
  have hAnonneg :
      0 ≤ saddleFixedStripMajorant ε ℓ H A k m := by
    have hgammaarg :
        0 < A / 2 + ((k + (m + 3) : ℕ) : ℝ) := by
      rw [Nat.cast_add]
      have hm : (0 : ℝ) ≤ ((m + 3 : ℕ) : ℝ) :=
        Nat.cast_nonneg _
      linarith
    unfold saddleFixedStripMajorant
    positivity [Real.Gamma_pos_of_pos hgammaarg]
  refine ⟨C, hAnonneg.trans
    (hC (Set.mem_image_of_mem _ hAmem)), ?_⟩
  intro a ha t ht
  have hshifta : 0 < a / 2 + (k : ℝ) := by
    linarith [ha.1]
  calc
    |t| ^ m *
        ‖plusSaddleMellinData ε ℓ
          ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      saddleShiftedLineMajorant ε ℓ a k m :=
        plusSaddleMellinData_shiftedLine_polynomial_bound
          hε hℓ horder a ht k m hshifta
    _ ≤ saddleFixedStripMajorant ε ℓ H a k m :=
      saddleShiftedLineMajorant_le_fixedStrip
        hε hℓ horder
        (saddleHorizontalStripHeight_bound hℓ ha)
        k m hshifta
    _ ≤ C := hC (Set.mem_image_of_mem _ ha)

private theorem minusSaddleMellinData_horizontalStrip_polynomial_bound
    {ε ℓ : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    {A B : ℝ} (hAB : A ≤ B) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ Set.Icc A B, ∀ t : ℝ,
        1 ≤ |t| →
          |t| ^ m *
            ‖minusSaddleMellinData ε ℓ
              ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨k, hk⟩ := exists_nat_gt (-(A / 2))
  have hshiftA : 0 < A / 2 + (k : ℝ) := by
    linarith
  let H : ℝ := saddleHorizontalStripHeight ℓ A B
  have hcont : ContinuousOn
      (fun a : ℝ => saddleFixedStripMajorant ε ℓ H a k m)
      (Set.Icc A B) :=
    saddleFixedStripMajorant_continuousOn
      ε ℓ H k m hshiftA
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hcont
  have hAmem : A ∈ Set.Icc A B := ⟨le_rfl, hAB⟩
  have hAnonneg :
      0 ≤ saddleFixedStripMajorant ε ℓ H A k m := by
    have hgammaarg :
        0 < A / 2 + ((k + (m + 3) : ℕ) : ℝ) := by
      rw [Nat.cast_add]
      have hm : (0 : ℝ) ≤ ((m + 3 : ℕ) : ℝ) :=
        Nat.cast_nonneg _
      linarith
    unfold saddleFixedStripMajorant
    positivity [Real.Gamma_pos_of_pos hgammaarg]
  refine ⟨C, hAnonneg.trans
    (hC (Set.mem_image_of_mem _ hAmem)), ?_⟩
  intro a ha t ht
  have hshifta : 0 < a / 2 + (k : ℝ) := by
    linarith [ha.1]
  calc
    |t| ^ m *
        ‖minusSaddleMellinData ε ℓ
          ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      saddleShiftedLineMajorant ε ℓ a k m :=
        minusSaddleMellinData_shiftedLine_polynomial_bound
          hε hℓ horder a ht k m hshifta
    _ ≤ saddleFixedStripMajorant ε ℓ H a k m :=
      saddleShiftedLineMajorant_le_fixedStrip
        hε hℓ horder
        (saddleHorizontalStripHeight_bound hℓ ha)
        k m hshifta
    _ ≤ C := hC (Set.mem_image_of_mem _ ha)

private theorem saddleEnvelope_conj (ε ℓ t : ℝ) :
    starRingEnd ℂ (saddleEnvelope ε ℓ t) =
      saddleEnvelope ε ℓ (-t) := by
  have harg :
      (t : ℂ) / (ℓ : ℂ) = ((t / ℓ : ℝ) : ℂ) := by
    push_cast
    rfl
  have hneg :
      ((-t : ℝ) : ℂ) / (ℓ : ℂ) =
        -((t : ℂ) / (ℓ : ℂ)) := by
    push_cast
    ring
  have hphase :
      starRingEnd ℂ (mellinShellPhase ε ((t : ℂ) / (ℓ : ℂ))) =
        mellinShellPhase ε (((-t : ℝ) : ℂ) / (ℓ : ℂ)) := by
    calc
      starRingEnd ℂ (mellinShellPhase ε ((t : ℂ) / (ℓ : ℂ))) =
          mellinShellPhase ε ((t : ℂ) / (ℓ : ℂ)) := by
            rw [harg, mellinShellPhase_real_conj]
      _ = mellinShellPhase ε (((-t : ℝ) : ℂ) / (ℓ : ℂ)) := by
            rw [hneg, mellinShellPhase_neg]
  unfold saddleEnvelope
  simp only [map_mul, ← Complex.exp_conj, ← Complex.Gamma_conj,
    map_div₀, map_sub, Complex.conj_ofReal, Complex.conj_I,
    map_ofNat]
  rw [hphase]
  push_cast
  congr 2 <;> congr 1 <;> ring

private theorem norm_saddleShellExponential_le {ε ℓ : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) (t : ℝ) :
    ‖Complex.exp
        ((ℓ : ℂ) * mellinShellPhase ε
          ((t : ℂ) / (ℓ : ℂ)))‖ ≤
      Real.exp (2 * |ℓ| * saddleShellTotalVariation ε) := by
  have harg :
      (t : ℂ) / (ℓ : ℂ) = ((t / ℓ : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [harg, mellinShellPhase_ofReal, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  apply Real.exp_le_exp.mpr
  calc
    ℓ * realOscillatoryShellPhase ε (t / ℓ)
      ≤ |ℓ * realOscillatoryShellPhase ε (t / ℓ)| :=
          le_abs_self _
    _ = |ℓ| * |realOscillatoryShellPhase ε (t / ℓ)| :=
          abs_mul _ _
    _ ≤ |ℓ| * (2 * saddleShellTotalVariation ε) := by
          gcongr
          exact abs_realOscillatoryShellPhase_le hε horder (t / ℓ)
    _ = 2 * |ℓ| * saddleShellTotalVariation ε := by ring

private theorem saddleEnvelope_vertical_polynomial_bound {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (t : ℝ) (k : ℕ) :
    |t| ^ k * ‖saddleEnvelope ε ℓ t‖ ≤
      (2 : ℝ) ^ k * Real.Gamma (ℓ / 2 + k) *
        Real.exp (2 * |ℓ| * saddleShellTotalVariation ε) := by
  let z : ℂ := ((ℓ : ℂ) - Complex.I * (t : ℂ)) / 2
  have hz : 0 < z.re := by
    try dsimp [z]
    simpa only [Complex.div_ofNat_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, zero_mul,
      Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, sub_zero, Nat.ofNat_pos,
        div_pos_iff_of_pos_right] using! half_pos hℓ
  have hgamma :
      (|t| / 2) ^ k * ‖Complex.Gamma z‖ ≤
        Real.Gamma (ℓ / 2 + k) := by
    simpa [z, abs_div] using!
      complexGamma_vertical_polynomial_bound hz k
  have hscaled :
      |t| ^ k * ‖Complex.Gamma z‖ ≤
        (2 : ℝ) ^ k * Real.Gamma (ℓ / 2 + k) := by
    calc
      |t| ^ k * ‖Complex.Gamma z‖ =
          (2 : ℝ) ^ k *
            ((|t| / 2) ^ k * ‖Complex.Gamma z‖) := by
              rw [div_pow]
              field_simp
      _ ≤ (2 : ℝ) ^ k * Real.Gamma (ℓ / 2 + k) := by
              gcongr
  have hunit :
      ‖Complex.exp
        (Complex.I * (t : ℂ) * (Real.log Real.pi : ℂ) / 2)‖ = 1 := by
    rw [Complex.norm_exp]
    simp only [Complex.div_ofNat_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul,
      Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_self, Complex.mul_im, one_mul, zero_add, zero_div,
        Real.exp_zero]
  calc
    |t| ^ k * ‖saddleEnvelope ε ℓ t‖ =
        (|t| ^ k * ‖Complex.Gamma z‖) *
          ‖Complex.exp ((ℓ : ℂ) *
            mellinShellPhase ε ((t : ℂ) / (ℓ : ℂ)))‖ := by
            unfold saddleEnvelope
            rw [norm_mul, norm_mul, hunit]
            try dsimp [z]
            ring
    _ ≤ ((2 : ℝ) ^ k * Real.Gamma (ℓ / 2 + k)) *
          Real.exp (2 * |ℓ| * saddleShellTotalVariation ε) := by
            gcongr
            exact norm_saddleShellExponential_le hε horder t

private theorem norm_plusPolynomial_scaled_le {ε ℓ t : ℝ}
    (hℓ : 0 < ℓ) (ht : 1 ≤ |t|) :
    ‖plusPolynomial ε ((t : ℂ) / (ℓ : ℂ))‖ ≤
      (1 + |(ε / 4)|) * (1 + ℓ⁻¹) ^ 3 * |t| ^ 3 := by
  have hnorm : ‖(t : ℂ) / (ℓ : ℂ)‖ = |t| / ℓ := by
    rw [norm_div]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hℓ]
  have hlinear :
      1 + |t| / ℓ ≤ (1 + ℓ⁻¹) * |t| := by
    rw [inv_eq_one_div]
    field_simp [hℓ.ne']
    nlinarith
  calc
    ‖plusPolynomial ε ((t : ℂ) / (ℓ : ℂ))‖
      ≤ (1 + |(ε / 4)|) *
        (1 + ‖(t : ℂ) / (ℓ : ℂ)‖) ^ 3 :=
          norm_plusPolynomial_le ε _
    _ = (1 + |(ε / 4)|) * (1 + |t| / ℓ) ^ 3 := by
          rw [hnorm]
    _ ≤ (1 + |(ε / 4)|) *
        ((1 + ℓ⁻¹) * |t|) ^ 3 := by
          gcongr
    _ = (1 + |(ε / 4)|) * (1 + ℓ⁻¹) ^ 3 * |t| ^ 3 := by
          ring

private theorem norm_minusPolynomial_scaled_le {ε ℓ t : ℝ}
    (hℓ : 0 < ℓ) (ht : 1 ≤ |t|) :
    ‖minusPolynomial ε ((t : ℂ) / (ℓ : ℂ))‖ ≤
      (1 + |(ε / 4)|) * (1 + ℓ⁻¹) ^ 3 * |t| ^ 3 := by
  have hnorm : ‖(t : ℂ) / (ℓ : ℂ)‖ = |t| / ℓ := by
    rw [norm_div]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hℓ]
  have hlinear :
      1 + |t| / ℓ ≤ (1 + ℓ⁻¹) * |t| := by
    rw [inv_eq_one_div]
    field_simp [hℓ.ne']
    nlinarith
  calc
    ‖minusPolynomial ε ((t : ℂ) / (ℓ : ℂ))‖
      ≤ (1 + |(ε / 4)|) *
        (1 + ‖(t : ℂ) / (ℓ : ℂ)‖) ^ 3 :=
          norm_minusPolynomial_le ε _
    _ = (1 + |(ε / 4)|) * (1 + |t| / ℓ) ^ 3 := by
          rw [hnorm]
    _ ≤ (1 + |(ε / 4)|) *
        ((1 + ℓ⁻¹) * |t|) ^ 3 := by
          gcongr
    _ = (1 + |(ε / 4)|) * (1 + ℓ⁻¹) ^ 3 * |t| ^ 3 := by
          ring

private theorem plusSaddleSpectrum_vertical_polynomial_bound {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    {t : ℝ} (ht : 1 ≤ |t|) (k : ℕ) :
    |t| ^ k * ‖plusSaddleSpectrum ε ℓ t‖ ≤
      ((1 + |(ε / 4)|) * (1 + ℓ⁻¹) ^ 3) *
        ((2 : ℝ) ^ (k + 3) *
          Real.Gamma (ℓ / 2 + (k + 3)) *
          Real.exp (2 * |ℓ| * saddleShellTotalVariation ε)) := by
  have hpoly := norm_plusPolynomial_scaled_le
    (ε := ε) hℓ ht
  have hgamma := saddleEnvelope_vertical_polynomial_bound
    hε hℓ horder t (k + 3)
  calc
    |t| ^ k * ‖plusSaddleSpectrum ε ℓ t‖ =
        |t| ^ k * ‖saddleEnvelope ε ℓ t‖ *
          ‖plusPolynomial ε ((t : ℂ) / (ℓ : ℂ))‖ := by
            unfold plusSaddleSpectrum
            rw [norm_mul]
            ring
    _ ≤ |t| ^ k * ‖saddleEnvelope ε ℓ t‖ *
          ((1 + |(ε / 4)|) * (1 + ℓ⁻¹) ^ 3 * |t| ^ 3) := by
            gcongr
    _ = ((1 + |(ε / 4)|) * (1 + ℓ⁻¹) ^ 3) *
          (|t| ^ (k + 3) * ‖saddleEnvelope ε ℓ t‖) := by
            rw [pow_add]
            ring
    _ ≤ ((1 + |(ε / 4)|) * (1 + ℓ⁻¹) ^ 3) *
        ((2 : ℝ) ^ (k + 3) *
          Real.Gamma (ℓ / 2 + (k + 3)) *
          Real.exp (2 * |ℓ| * saddleShellTotalVariation ε)) := by
            simpa only [Nat.cast_add, Nat.cast_ofNat] using!
              (mul_le_mul_of_nonneg_left hgamma
                (show 0 ≤ (1 + |(ε / 4)|) * (1 + ℓ⁻¹) ^ 3 by
                  positivity))

private theorem minusSaddleSpectrum_vertical_polynomial_bound {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    {t : ℝ} (ht : 1 ≤ |t|) (k : ℕ) :
    |t| ^ k * ‖minusSaddleSpectrum ε ℓ t‖ ≤
      ((1 + |(ε / 4)|) * (1 + ℓ⁻¹) ^ 3) *
        ((2 : ℝ) ^ (k + 3) *
          Real.Gamma (ℓ / 2 + (k + 3)) *
          Real.exp (2 * |ℓ| * saddleShellTotalVariation ε)) := by
  have hpoly := norm_minusPolynomial_scaled_le
    (ε := ε) hℓ ht
  have hgamma := saddleEnvelope_vertical_polynomial_bound
    hε hℓ horder t (k + 3)
  calc
    |t| ^ k * ‖minusSaddleSpectrum ε ℓ t‖ =
        |t| ^ k * ‖saddleEnvelope ε ℓ t‖ *
          ‖minusPolynomial ε ((t : ℂ) / (ℓ : ℂ))‖ := by
            unfold minusSaddleSpectrum
            rw [norm_mul]
            ring
    _ ≤ |t| ^ k * ‖saddleEnvelope ε ℓ t‖ *
          ((1 + |(ε / 4)|) * (1 + ℓ⁻¹) ^ 3 * |t| ^ 3) := by
            gcongr
    _ = ((1 + |(ε / 4)|) * (1 + ℓ⁻¹) ^ 3) *
          (|t| ^ (k + 3) * ‖saddleEnvelope ε ℓ t‖) := by
            rw [pow_add]
            ring
    _ ≤ ((1 + |(ε / 4)|) * (1 + ℓ⁻¹) ^ 3) *
        ((2 : ℝ) ^ (k + 3) *
          Real.Gamma (ℓ / 2 + (k + 3)) *
          Real.exp (2 * |ℓ| * saddleShellTotalVariation ε)) := by
            simpa only [Nat.cast_add, Nat.cast_ofNat] using!
              (mul_le_mul_of_nonneg_left hgamma
                (show 0 ≤ (1 + |(ε / 4)|) * (1 + ℓ⁻¹) ^ 3 by
                  positivity))

private theorem integrable_of_continuous_polynomial_decay
    {F : ℝ → ℂ} (hF : Continuous F)
    (hdecay : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, 1 ≤ |t| → |t| ^ j * ‖F t‖ ≤ C)
    (k : ℕ) : Integrable (fun t : ℝ => (t : ℂ) ^ k * F t) := by
  have hcompact : IsCompact (Set.Icc (-1 : ℝ) 1) :=
    isCompact_Icc
  obtain ⟨M, hM⟩ := hcompact.bddAbove_image hF.norm.continuousOn
  have hzero : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> norm_num
  have hMnonneg : 0 ≤ M :=
    (norm_nonneg (F 0)).trans
      (hM (Set.mem_image_of_mem (fun t : ℝ => ‖F t‖) hzero))
  obtain ⟨C, hC, htail⟩ := hdecay (k + 2)
  have hmajor : Integrable (fun t : ℝ =>
      (2 * (M + C)) * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul (2 * (M + C))
  have hmoment : Continuous (fun t : ℝ =>
      (t : ℂ) ^ k * F t) := by
    exact ((Complex.continuous_ofReal.comp continuous_id).pow k).mul hF
  apply hmajor.mono' hmoment.aestronglyMeasurable
  filter_upwards [] with t
  have hden : 0 < 1 + t ^ 2 := by positivity
  change ‖(t : ℂ) ^ k * F t‖ ≤
    2 * (M + C) / (1 + t ^ 2)
  apply (le_div_iff₀ hden).2
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  by_cases ht : |t| ≤ (1 : ℝ)
  · have htmem : t ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor
      · linarith [neg_abs_le t]
      · linarith [le_abs_self t]
    have hnorm : ‖F t‖ ≤ M :=
      hM (Set.mem_image_of_mem (fun u : ℝ => ‖F u‖) htmem)
    have hpow : |t| ^ k ≤ 1 :=
      pow_le_one₀ (abs_nonneg t) ht
    have hsquare : t ^ 2 ≤ 1 := by
      have habs : |t| ^ 2 ≤ (1 : ℝ) := by
        linarith [mul_nonneg (abs_nonneg t)
          (sub_nonneg.mpr ht)]
      simpa only [sq_abs] using! habs
    have hweighted : |t| ^ k * ‖F t‖ ≤ M := by
      calc
        |t| ^ k * ‖F t‖ ≤ 1 * ‖F t‖ := by
          gcongr
        _ = ‖F t‖ := one_mul _
        _ ≤ M := hnorm
    calc
      (|t| ^ k * ‖F t‖) * (1 + t ^ 2)
        ≤ M * 2 :=
          mul_le_mul hweighted (by linarith)
            (by positivity) hMnonneg
      _ ≤ 2 * (M + C) := by linarith
  · have htlarge : 1 ≤ |t| :=
      (lt_of_not_ge ht).le
    have hsquare : (1 : ℝ) ≤ t ^ 2 := by
      have habs : (1 : ℝ) ≤ |t| ^ 2 := by
        linarith [mul_nonneg (abs_nonneg t)
          (sub_nonneg.mpr htlarge)]
      simpa only [sq_abs] using! habs
    calc
      (|t| ^ k * ‖F t‖) * (1 + t ^ 2)
        ≤ (|t| ^ k * ‖F t‖) * (2 * t ^ 2) := by
          gcongr
          linarith
      _ = 2 * (|t| ^ (k + 2) * ‖F t‖) := by
          rw [pow_add, sq_abs]
          ring
      _ ≤ 2 * C := by
          gcongr
          exact htail t htlarge
      _ ≤ 2 * (M + C) := by
          linarith

private theorem saddleShiftedLine_ne_pole
    {a : ℝ}
    (hpole : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ))
    (t : ℝ) (n : ℕ) :
    (a : ℂ) + (t : ℂ) * Complex.I ≠
      (-((2 * n : ℕ) : ℂ)) := by
  intro heq
  apply hpole n
  have hre := congrArg Complex.re heq
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.neg_re,
      Complex.re_ofNat,
    Complex.natCast_re, Complex.im_ofNat, Complex.natCast_im, sub_zero] using! hre

private theorem plusSaddleMellinData_shiftedLine_continuous
    {ε a : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ)
    (hpole : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ)) :
    Continuous (fun t : ℝ =>
      plusSaddleMellinData ε ℓ
        ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hcomplex :
      DifferentiableAt ℂ (plusSaddleMellinData ε ℓ)
        ((a : ℂ) + (t : ℂ) * Complex.I) :=
    plusSaddleMellinData_differentiableAt_of_not_pole
      hε horder ℓ (saddleShiftedLine_ne_pole hpole t)
  have hline : ContinuousAt
      (fun u : ℝ => (a : ℂ) + (u : ℂ) * Complex.I) t :=
    (continuous_const.add
      (Complex.continuous_ofReal.mul_const Complex.I)).continuousAt
  simpa only [Function.comp_def] using!
    hcomplex.continuousAt.comp_of_eq hline (by rfl)

private theorem minusSaddleMellinData_shiftedLine_continuous
    {ε a : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ : ℝ)
    (hpole : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ)) :
    Continuous (fun t : ℝ =>
      minusSaddleMellinData ε ℓ
        ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hcomplex :
      DifferentiableAt ℂ (minusSaddleMellinData ε ℓ)
        ((a : ℂ) + (t : ℂ) * Complex.I) :=
    minusSaddleMellinData_differentiableAt_of_not_pole
      hε horder ℓ (saddleShiftedLine_ne_pole hpole t)
  have hline : ContinuousAt
      (fun u : ℝ => (a : ℂ) + (u : ℂ) * Complex.I) t :=
    (continuous_const.add
      (Complex.continuous_ofReal.mul_const Complex.I)).continuousAt
  simpa only [Function.comp_def] using!
    hcomplex.continuousAt.comp_of_eq hline (by rfl)

private theorem plusSaddleMellinData_shiftedLine_moment_integrable
    {ε ℓ a : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hpole : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ))
    (j : ℕ) :
    Integrable (fun t : ℝ =>
      (t : ℂ) ^ j * plusSaddleMellinData ε ℓ
        ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  apply integrable_of_continuous_polynomial_decay
    (plusSaddleMellinData_shiftedLine_continuous
      hε horder ℓ hpole)
  intro m
  obtain ⟨k, hk⟩ := exists_nat_gt (-(a / 2))
  have hshift : 0 < a / 2 + (k : ℝ) := by
    linarith
  refine ⟨saddleShiftedLineMajorant ε ℓ a k m,
    saddleShiftedLineMajorant_nonneg hℓ k m hshift, ?_⟩
  intro t ht
  exact plusSaddleMellinData_shiftedLine_polynomial_bound
    hε hℓ horder a ht k m hshift

private theorem minusSaddleMellinData_shiftedLine_moment_integrable
    {ε ℓ a : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hpole : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ))
    (j : ℕ) :
    Integrable (fun t : ℝ =>
      (t : ℂ) ^ j * minusSaddleMellinData ε ℓ
        ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  apply integrable_of_continuous_polynomial_decay
    (minusSaddleMellinData_shiftedLine_continuous
      hε horder ℓ hpole)
  intro m
  obtain ⟨k, hk⟩ := exists_nat_gt (-(a / 2))
  have hshift : 0 < a / 2 + (k : ℝ) := by
    linarith
  refine ⟨saddleShiftedLineMajorant ε ℓ a k m,
    saddleShiftedLineMajorant_nonneg hℓ k m hshift, ?_⟩
  intro t ht
  exact minusSaddleMellinData_shiftedLine_polynomial_bound
    hε hℓ horder a ht k m hshift

private theorem saddleMellinInversePower_shiftedLine_norm
    {r : ℝ} (hr : 0 < r) (a t : ℝ) :
    ‖saddleMellinInversePower r
      ((a : ℂ) + (t : ℂ) * Complex.I)‖ =
      r ^ (-a) := by
  unfold saddleMellinInversePower
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp only [neg_add_rev, Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, neg_zero, zero_add]

private theorem saddleMellinInversePower_shiftedLine_continuous
    {r : ℝ} (hr : 0 < r) (a : ℝ) :
    Continuous (fun t : ℝ =>
      saddleMellinInversePower r
        ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  exact (saddleMellinInversePower_differentiable hr).continuous.comp
    (by fun_prop)

private theorem plusSaddleMellinData_shiftedLine_weighted_moment_integrable
    {ε ℓ a r : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hpole : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ))
    (hr : 0 < r) (j : ℕ) :
    Integrable (fun t : ℝ =>
      saddleMellinInversePower r
        ((a : ℂ) + (t : ℂ) * Complex.I) *
        ((t : ℂ) ^ j * plusSaddleMellinData ε ℓ
          ((a : ℂ) + (t : ℂ) * Complex.I))) := by
  have hmoment :=
    plusSaddleMellinData_shiftedLine_moment_integrable
      hε hℓ horder hpole j
  have hweight :=
    saddleMellinInversePower_shiftedLine_continuous hr a
  apply (hmoment.norm.const_mul (r ^ (-a))).mono'
  · exact hweight.aestronglyMeasurable.mul
      hmoment.aestronglyMeasurable
  · filter_upwards [] with t
    rw [norm_mul, saddleMellinInversePower_shiftedLine_norm hr a t]

private theorem minusSaddleMellinData_shiftedLine_weighted_moment_integrable
    {ε ℓ a r : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hpole : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ))
    (hr : 0 < r) (j : ℕ) :
    Integrable (fun t : ℝ =>
      saddleMellinInversePower r
        ((a : ℂ) + (t : ℂ) * Complex.I) *
        ((t : ℂ) ^ j * minusSaddleMellinData ε ℓ
          ((a : ℂ) + (t : ℂ) * Complex.I))) := by
  have hmoment :=
    minusSaddleMellinData_shiftedLine_moment_integrable
      hε hℓ horder hpole j
  have hweight :=
    saddleMellinInversePower_shiftedLine_continuous hr a
  apply (hmoment.norm.const_mul (r ^ (-a))).mono'
  · exact hweight.aestronglyMeasurable.mul
      hmoment.aestronglyMeasurable
  · filter_upwards [] with t
    rw [norm_mul, saddleMellinInversePower_shiftedLine_norm hr a t]

private theorem plusSaddleMellinData_shiftedLine_weighted_integrable
    {ε ℓ a r : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hpole : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ))
    (hr : 0 < r) :
    Integrable (fun t : ℝ =>
      saddleMellinInversePower r
        ((a : ℂ) + (t : ℂ) * Complex.I) *
        plusSaddleMellinData ε ℓ
          ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  simpa only [pow_zero, one_mul] using!
    plusSaddleMellinData_shiftedLine_weighted_moment_integrable
      hε hℓ horder hpole hr 0

private theorem minusSaddleMellinData_shiftedLine_weighted_integrable
    {ε ℓ a r : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hpole : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ))
    (hr : 0 < r) :
    Integrable (fun t : ℝ =>
      saddleMellinInversePower r
        ((a : ℂ) + (t : ℂ) * Complex.I) *
        minusSaddleMellinData ε ℓ
          ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  simpa only [pow_zero, one_mul] using!
    minusSaddleMellinData_shiftedLine_weighted_moment_integrable
      hε hℓ horder hpole hr 0

private theorem saddleGaussianPoleRepresentative_shiftedLine_norm
    (a t : ℝ) (n : ℕ) :
    ‖saddleGaussianPoleRepresentative n
      ((a : ℂ) + (t : ℂ) * Complex.I)‖ =
      Real.exp
        ((a + ((2 * n : ℕ) : ℝ)) ^ 2 - t ^ 2) /
        ‖(a : ℂ) + (t : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ)‖ := by
  unfold saddleGaussianPoleRepresentative
  rw [norm_div, Complex.norm_exp]
  congr 1
  simp only [Nat.cast_mul, Nat.cast_ofNat, pow_two, Complex.mul_re, Complex.add_re,
    Complex.ofReal_re,
    Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero,
      Complex.re_ofNat,
    Complex.natCast_re, Complex.im_ofNat, Complex.natCast_im, sub_zero, Complex.add_im,
      Complex.mul_im, zero_add,
    zero_mul]

private theorem saddleGaussianPoleRepresentative_shiftedLine_continuous
    {a : ℝ} (n : ℕ)
    (ha : a ≠ -((2 * n : ℕ) : ℝ)) :
    Continuous (fun t : ℝ =>
      saddleGaussianPoleRepresentative n
        ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  have hline : Continuous
      (fun t : ℝ =>
        (a : ℂ) + (t : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ)) := by
    fun_prop
  have hnonzero : ∀ t : ℝ,
      (a : ℂ) + (t : ℂ) * Complex.I +
        ((2 * n : ℕ) : ℂ) ≠ 0 := by
    intro t hzero
    apply ha
    have hre := congrArg Complex.re hzero
    norm_num [Complex.mul_re] at hre
    push_cast
    linarith
  unfold saddleGaussianPoleRepresentative
  exact (Complex.continuous_exp.comp (hline.pow 2)).div
    hline hnonzero

private theorem saddleGaussianPoleRepresentative_shiftedLine_bound
    {a : ℝ} (n : ℕ)
    (ha : a ≠ -((2 * n : ℕ) : ℝ)) (t : ℝ) :
    ‖saddleGaussianPoleRepresentative n
      ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (Real.exp ((a + ((2 * n : ℕ) : ℝ)) ^ 2) /
          |a + ((2 * n : ℕ) : ℝ)|) *
        Real.exp (-t ^ 2) := by
  have hreal : a + ((2 * n : ℕ) : ℝ) ≠ 0 := by
    intro hzero
    apply ha
    linarith
  have habs : 0 < |a + ((2 * n : ℕ) : ℝ)| :=
    abs_pos.mpr hreal
  have hden :
      |a + ((2 * n : ℕ) : ℝ)| ≤
        ‖(a : ℂ) + (t : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ)‖ := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.re_ofNat,
        Complex.natCast_re,
      Complex.im_ofNat, Complex.natCast_im, sub_zero] using!
      (Complex.abs_re_le_norm
        ((a : ℂ) + (t : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ)))
  rw [saddleGaussianPoleRepresentative_shiftedLine_norm,
    sub_eq_add_neg, Real.exp_add]
  calc
    Real.exp ((a + ((2 * n : ℕ) : ℝ)) ^ 2) *
        Real.exp (-t ^ 2) /
        ‖(a : ℂ) + (t : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ)‖ ≤
      Real.exp ((a + ((2 * n : ℕ) : ℝ)) ^ 2) *
        Real.exp (-t ^ 2) /
          |a + ((2 * n : ℕ) : ℝ)| := by
        gcongr
    _ = (Real.exp ((a + ((2 * n : ℕ) : ℝ)) ^ 2) /
          |a + ((2 * n : ℕ) : ℝ)|) *
        Real.exp (-t ^ 2) := by
          ring

private theorem saddleGaussianPoleRepresentative_shiftedLine_integrable
    {a : ℝ} (n : ℕ)
    (ha : a ≠ -((2 * n : ℕ) : ℝ)) :
    Integrable (fun t : ℝ =>
      saddleGaussianPoleRepresentative n
        ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  have hgaussian : Integrable
      (fun t : ℝ => Real.exp (-t ^ 2)) := by
    simpa only [neg_mul, one_mul] using!
      (integrable_exp_neg_mul_sq (b := (1 : ℝ))
        (by norm_num : (0 : ℝ) < 1))
  let C : ℝ :=
    Real.exp ((a + ((2 * n : ℕ) : ℝ)) ^ 2) /
      |a + ((2 * n : ℕ) : ℝ)|
  apply (hgaussian.const_mul C).mono'
  · exact (saddleGaussianPoleRepresentative_shiftedLine_continuous
      n ha).aestronglyMeasurable
  · filter_upwards [] with t
    exact saddleGaussianPoleRepresentative_shiftedLine_bound
      n ha t

private theorem saddleGaussianPoleRepresentative_shiftedLine_weighted_integrable
    {a r : ℝ} (n : ℕ)
    (ha : a ≠ -((2 * n : ℕ) : ℝ))
    (hr : 0 < r) :
    Integrable (fun t : ℝ =>
      saddleMellinInversePower r
        ((a : ℂ) + (t : ℂ) * Complex.I) *
        saddleGaussianPoleRepresentative n
          ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  have hrepresentative :=
    saddleGaussianPoleRepresentative_shiftedLine_integrable
      n ha
  have hweight :=
    saddleMellinInversePower_shiftedLine_continuous hr a
  apply (hrepresentative.norm.const_mul (r ^ (-a))).mono'
  · exact hweight.aestronglyMeasurable.mul
      hrepresentative.aestronglyMeasurable
  · filter_upwards [] with t
    rw [norm_mul, saddleMellinInversePower_shiftedLine_norm hr a t]

private theorem plusSaddleFiniteRapidContourIntegrand_shiftedLine_integrable
    {ε ℓ a r : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (N : ℕ)
    (hhalf : -(2 * ((N : ℝ) + 1)) < a)
    (hpole : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ))
    (hr : 0 < r) :
    Integrable (fun t : ℝ =>
      plusSaddleFiniteRapidContourIntegrand ε ℓ N r
        ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  have hdata :=
    plusSaddleMellinData_shiftedLine_weighted_integrable
      hε hℓ horder hpole hr
  have hsum : Integrable (fun t : ℝ =>
      ∑ n ∈ Finset.range (N + 1),
        saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I) *
          (plusSaddlePoleResidue ε ℓ n *
            saddleGaussianPoleRepresentative n
              ((a : ℂ) + (t : ℂ) * Complex.I))) := by
    apply integrable_finsetSum
    intro n _
    have hterm :=
      (saddleGaussianPoleRepresentative_shiftedLine_weighted_integrable
        n (hpole n) hr).const_mul
          (plusSaddlePoleResidue ε ℓ n)
    exact hterm.congr
      (Filter.Eventually.of_forall (fun t => by ring))
  apply (hdata.sub hsum).congr
  filter_upwards [] with t
  have hz :
      (a : ℂ) + (t : ℂ) * Complex.I ∈
        saddleFinitePoleHalfPlane N := by
    change
      -(2 * ((N : ℝ) + 1)) <
        ((a : ℂ) + (t : ℂ) * Complex.I).re
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im,
      Complex.I_im, mul_one, sub_self, add_zero] using! hhalf
  unfold plusSaddleFiniteRapidContourIntegrand
  rw [plusSaddleFiniteRapidPoleRegularPart_eq_subtraction_of_not_pole
    hε horder ℓ N hz (saddleShiftedLine_ne_pole hpole t)]
  unfold plusSaddleFiniteRapidPoleSubtraction
  rw [mul_sub, Finset.mul_sum]
  rfl

private theorem minusSaddleFiniteRapidContourIntegrand_shiftedLine_integrable
    {ε ℓ a r : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (N : ℕ)
    (hhalf : -(2 * ((N : ℝ) + 1)) < a)
    (hpole : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ))
    (hr : 0 < r) :
    Integrable (fun t : ℝ =>
      minusSaddleFiniteRapidContourIntegrand ε ℓ N r
        ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  have hdata :=
    minusSaddleMellinData_shiftedLine_weighted_integrable
      hε hℓ horder hpole hr
  have hsum : Integrable (fun t : ℝ =>
      ∑ n ∈ Finset.range (N + 1),
        saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I) *
          (minusSaddlePoleResidue ε ℓ n *
            saddleGaussianPoleRepresentative n
              ((a : ℂ) + (t : ℂ) * Complex.I))) := by
    apply integrable_finsetSum
    intro n _
    have hterm :=
      (saddleGaussianPoleRepresentative_shiftedLine_weighted_integrable
        n (hpole n) hr).const_mul
          (minusSaddlePoleResidue ε ℓ n)
    exact hterm.congr
      (Filter.Eventually.of_forall (fun t => by ring))
  apply (hdata.sub hsum).congr
  filter_upwards [] with t
  have hz :
      (a : ℂ) + (t : ℂ) * Complex.I ∈
        saddleFinitePoleHalfPlane N := by
    change
      -(2 * ((N : ℝ) + 1)) <
        ((a : ℂ) + (t : ℂ) * Complex.I).re
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im,
      Complex.I_im, mul_one, sub_self, add_zero] using! hhalf
  unfold minusSaddleFiniteRapidContourIntegrand
  rw [minusSaddleFiniteRapidPoleRegularPart_eq_subtraction_of_not_pole
    hε horder ℓ N hz (saddleShiftedLine_ne_pole hpole t)]
  unfold minusSaddleFiniteRapidPoleSubtraction
  rw [mul_sub, Finset.mul_sum]
  rfl

private theorem saddleMellinInversePower_horizontalStrip_bounded
    {r A B : ℝ} (hr : 0 < r) (hAB : A ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ Set.Icc A B, ∀ t : ℝ,
        ‖saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  have hpower : Continuous
      (fun a : ℝ => r ^ (-a)) :=
    (Real.continuous_const_rpow hr.ne').comp
      (by fun_prop)
  obtain ⟨C, hC⟩ :=
    isCompact_Icc.bddAbove_image hpower.continuousOn
  have hAmem : A ∈ Set.Icc A B := ⟨le_rfl, hAB⟩
  have hnonneg : 0 ≤ C :=
    (Real.rpow_nonneg hr.le (-A)).trans
      (hC (Set.mem_image_of_mem _ hAmem))
  refine ⟨C, hnonneg, ?_⟩
  intro a ha t
  rw [saddleMellinInversePower_shiftedLine_norm hr a t]
  exact hC (Set.mem_image_of_mem _ ha)

private theorem plusSaddleMellinData_weighted_horizontalStrip_polynomial_bound
    {ε ℓ r : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hr : 0 < r)
    {A B : ℝ} (hAB : A ≤ B) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ Set.Icc A B, ∀ t : ℝ,
        1 ≤ |t| →
          |t| ^ m *
            ‖saddleMellinInversePower r
              ((a : ℂ) + (t : ℂ) * Complex.I) *
              plusSaddleMellinData ε ℓ
                ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨R, hR, hweight⟩ :=
    saddleMellinInversePower_horizontalStrip_bounded hr hAB
  obtain ⟨C, hC, hdata⟩ :=
    plusSaddleMellinData_horizontalStrip_polynomial_bound
      hε hℓ horder hAB m
  refine ⟨R * C, mul_nonneg hR hC, ?_⟩
  intro a ha t ht
  calc
    |t| ^ m *
        ‖saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I) *
          plusSaddleMellinData ε ℓ
            ((a : ℂ) + (t : ℂ) * Complex.I)‖ =
      ‖saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I)‖ *
        (|t| ^ m *
          ‖plusSaddleMellinData ε ℓ
            ((a : ℂ) + (t : ℂ) * Complex.I)‖) := by
        rw [norm_mul]
        ring
    _ ≤ R * C := by
      gcongr
      · exact hweight a ha t
      · exact hdata a ha t ht

private theorem minusSaddleMellinData_weighted_horizontalStrip_polynomial_bound
    {ε ℓ r : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hr : 0 < r)
    {A B : ℝ} (hAB : A ≤ B) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ Set.Icc A B, ∀ t : ℝ,
        1 ≤ |t| →
          |t| ^ m *
            ‖saddleMellinInversePower r
              ((a : ℂ) + (t : ℂ) * Complex.I) *
              minusSaddleMellinData ε ℓ
                ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨R, hR, hweight⟩ :=
    saddleMellinInversePower_horizontalStrip_bounded hr hAB
  obtain ⟨C, hC, hdata⟩ :=
    minusSaddleMellinData_horizontalStrip_polynomial_bound
      hε hℓ horder hAB m
  refine ⟨R * C, mul_nonneg hR hC, ?_⟩
  intro a ha t ht
  calc
    |t| ^ m *
        ‖saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I) *
          minusSaddleMellinData ε ℓ
            ((a : ℂ) + (t : ℂ) * Complex.I)‖ =
      ‖saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I)‖ *
        (|t| ^ m *
          ‖minusSaddleMellinData ε ℓ
            ((a : ℂ) + (t : ℂ) * Complex.I)‖) := by
        rw [norm_mul]
        ring
    _ ≤ R * C := by
      gcongr
      · exact hweight a ha t
      · exact hdata a ha t ht

private theorem saddleHorizontalIntegral_tendsto_zero
    {F : ℂ → ℂ} {A B C : ℝ}
    (hAB : A ≤ B)
    (hdecay : ∀ a ∈ Set.Icc A B, ∀ t : ℝ,
      1 ≤ |t| →
        |t| * ‖F ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C)
    (s : ℝ) (hs : |s| = 1) :
    Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          F ((a : ℂ) + ((s * T : ℝ) : ℂ) * Complex.I))
      Filter.atTop (𝓝 0) := by
  have hdiv : Tendsto
      (fun T : ℝ => C / T)
      Filter.atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hmajor : Tendsto
      (fun T : ℝ => C / T * |B - A|)
      Filter.atTop (𝓝 0) := by
    simpa only [zero_mul] using! hdiv.mul_const |B - A|
  apply squeeze_zero_norm' (a := fun T : ℝ =>
    C / T * |B - A|) ?_ hmajor
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro a ha
  rw [uIoc_of_le hAB] at ha
  have ha' : a ∈ Set.Icc A B := ⟨ha.1.le, ha.2⟩
  have habs : |s * T| = T := by
    rw [abs_mul, hs, one_mul, abs_of_nonneg hTpos.le]
  have htail := hdecay a ha' (s * T) (by rw [habs]; exact hT)
  rw [habs] at htail
  apply (le_div_iff₀ hTpos).2
  simpa only [Complex.ofReal_mul, mul_comm] using! htail

private theorem plusSaddleMellinData_weighted_horizontalIntegral_tendsto_zero
    {ε ℓ r : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hr : 0 < r)
    {A B : ℝ} (hAB : A ≤ B)
    (s : ℝ) (hs : |s| = 1) :
    Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          saddleMellinInversePower r
            ((a : ℂ) + ((s * T : ℝ) : ℂ) * Complex.I) *
            plusSaddleMellinData ε ℓ
              ((a : ℂ) + ((s * T : ℝ) : ℂ) * Complex.I))
      Filter.atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    plusSaddleMellinData_weighted_horizontalStrip_polynomial_bound
      hε hℓ horder hr hAB 1
  apply saddleHorizontalIntegral_tendsto_zero
    (F := fun z : ℂ =>
      saddleMellinInversePower r z *
        plusSaddleMellinData ε ℓ z)
    hAB (C := C) ?_ s hs
  simpa only [mem_Icc, Complex.norm_mul, and_imp, pow_one] using! hbound

private theorem minusSaddleMellinData_weighted_horizontalIntegral_tendsto_zero
    {ε ℓ r : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hr : 0 < r)
    {A B : ℝ} (hAB : A ≤ B)
    (s : ℝ) (hs : |s| = 1) :
    Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          saddleMellinInversePower r
            ((a : ℂ) + ((s * T : ℝ) : ℂ) * Complex.I) *
            minusSaddleMellinData ε ℓ
              ((a : ℂ) + ((s * T : ℝ) : ℂ) * Complex.I))
      Filter.atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    minusSaddleMellinData_weighted_horizontalStrip_polynomial_bound
      hε hℓ horder hr hAB 1
  apply saddleHorizontalIntegral_tendsto_zero
    (F := fun z : ℂ =>
      saddleMellinInversePower r z *
        minusSaddleMellinData ε ℓ z)
    hAB (C := C) ?_ s hs
  simpa only [mem_Icc, Complex.norm_mul, and_imp, pow_one] using! hbound

private theorem saddleGaussianPoleRepresentative_weighted_horizontalStrip_bound
    {r A B : ℝ} (hr : 0 < r) (hAB : A ≤ B)
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ Set.Icc A B, ∀ t : ℝ,
        1 ≤ |t| →
          |t| *
            ‖saddleMellinInversePower r
              ((a : ℂ) + (t : ℂ) * Complex.I) *
              saddleGaussianPoleRepresentative n
                ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  have hpower : Continuous
      (fun a : ℝ => r ^ (-a)) :=
    (Real.continuous_const_rpow hr.ne').comp
      (by fun_prop)
  have hgaussian : Continuous
      (fun a : ℝ =>
        Real.exp ((a + ((2 * n : ℕ) : ℝ)) ^ 2)) := by
    fun_prop
  have hcoefficient : Continuous
      (fun a : ℝ =>
        r ^ (-a) *
          Real.exp ((a + ((2 * n : ℕ) : ℝ)) ^ 2)) :=
    hpower.mul hgaussian
  obtain ⟨C, hC⟩ :=
    isCompact_Icc.bddAbove_image
      hcoefficient.continuousOn
  have hAmem : A ∈ Set.Icc A B := ⟨le_rfl, hAB⟩
  have hnonneg : 0 ≤ C :=
    (show 0 ≤ r ^ (-A) *
      Real.exp ((A + ((2 * n : ℕ) : ℝ)) ^ 2) by
        positivity).trans
          (hC (Set.mem_image_of_mem _ hAmem))
  refine ⟨C, hnonneg, ?_⟩
  intro a ha t ht
  have hden :
      |t| ≤
        ‖(a : ℂ) + (t : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ)‖ := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add,
        Complex.re_ofNat,
      Complex.natCast_im, Complex.im_ofNat, Complex.natCast_re, zero_mul] using!
      (Complex.abs_im_le_norm
        ((a : ℂ) + (t : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ)))
  have hdenpos :
      0 < ‖(a : ℂ) + (t : ℂ) * Complex.I +
        ((2 * n : ℕ) : ℂ)‖ :=
    (lt_of_lt_of_le zero_lt_one ht).trans_le hden
  have hfrac :
      |t| /
        ‖(a : ℂ) + (t : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ)‖ ≤ 1 :=
    (div_le_one hdenpos).2 hden
  have hexp : Real.exp (-t ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (sq_nonneg t))
  rw [norm_mul,
    saddleMellinInversePower_shiftedLine_norm hr a t,
    saddleGaussianPoleRepresentative_shiftedLine_norm,
    sub_eq_add_neg, Real.exp_add]
  calc
    |t| *
        (r ^ (-a) *
          (Real.exp ((a + ((2 * n : ℕ) : ℝ)) ^ 2) *
            Real.exp (-t ^ 2) /
            ‖(a : ℂ) + (t : ℂ) * Complex.I +
              ((2 * n : ℕ) : ℂ)‖)) =
      (r ^ (-a) *
        Real.exp ((a + ((2 * n : ℕ) : ℝ)) ^ 2)) *
        (Real.exp (-t ^ 2) *
          (|t| /
            ‖(a : ℂ) + (t : ℂ) * Complex.I +
              ((2 * n : ℕ) : ℂ)‖)) := by
        ring
    _ ≤ (r ^ (-a) *
        Real.exp ((a + ((2 * n : ℕ) : ℝ)) ^ 2)) * 1 := by
      apply mul_le_mul_of_nonneg_left
        (mul_le_one₀ hexp
          (div_nonneg (abs_nonneg t) (norm_nonneg _)) hfrac)
      positivity
    _ = r ^ (-a) *
        Real.exp ((a + ((2 * n : ℕ) : ℝ)) ^ 2) :=
      mul_one _
    _ ≤ C := hC (Set.mem_image_of_mem _ ha)

private theorem saddleFiniteGaussianPoleWeighted_horizontalStrip_bound
    {r A B : ℝ} (hr : 0 < r) (hAB : A ≤ B)
    (c : ℕ → ℂ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ Set.Icc A B, ∀ t : ℝ,
        1 ≤ |t| →
          |t| *
            ‖saddleMellinInversePower r
              ((a : ℂ) + (t : ℂ) * Complex.I) *
              (∑ n ∈ Finset.range (N + 1),
                c n * saddleGaussianPoleRepresentative n
                  ((a : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C := by
  choose G hG hbound using
    (fun n : ℕ =>
      saddleGaussianPoleRepresentative_weighted_horizontalStrip_bound
        hr hAB n)
  let C : ℝ :=
    ∑ n ∈ Finset.range (N + 1), ‖c n‖ * G n
  have hC : 0 ≤ C := by
    unfold C
    exact Finset.sum_nonneg
      (fun n _ => mul_nonneg (norm_nonneg _) (hG n))
  refine ⟨C, hC, ?_⟩
  intro a ha t ht
  let z : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
  change
    |t| *
      ‖saddleMellinInversePower r z *
        (∑ n ∈ Finset.range (N + 1),
          c n * saddleGaussianPoleRepresentative n z)‖ ≤ C
  calc
    |t| *
        ‖saddleMellinInversePower r z *
          (∑ n ∈ Finset.range (N + 1),
            c n * saddleGaussianPoleRepresentative n z)‖ =
      |t| *
        ‖∑ n ∈ Finset.range (N + 1),
          saddleMellinInversePower r z *
            (c n * saddleGaussianPoleRepresentative n z)‖ := by
        rw [Finset.mul_sum]
    _ ≤ |t| *
        ∑ n ∈ Finset.range (N + 1),
          ‖saddleMellinInversePower r z *
            (c n * saddleGaussianPoleRepresentative n z)‖ := by
        gcongr
        exact norm_sum_le _ _
    _ = ∑ n ∈ Finset.range (N + 1),
          ‖c n‖ *
            (|t| *
              ‖saddleMellinInversePower r z *
                saddleGaussianPoleRepresentative n z‖) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        rw [norm_mul, norm_mul, norm_mul]
        ring
    _ ≤ ∑ n ∈ Finset.range (N + 1),
          ‖c n‖ * G n := by
        apply Finset.sum_le_sum
        intro n _
        exact mul_le_mul_of_nonneg_left
          (by simpa only [Complex.norm_mul, z] using! hbound n a ha t ht)
          (norm_nonneg _)
    _ = C := rfl

/-- A nonzero Mellin frequency cannot coincide with a real gamma pole. -/
public
theorem saddleNonzeroFrequency_ne_pole
    (a : ℝ) {t : ℝ} (ht : t ≠ 0) (n : ℕ) :
    (a : ℂ) + (t : ℂ) * Complex.I ≠
      (-((2 * n : ℕ) : ℂ)) := by
  intro heq
  have him := congrArg Complex.im heq
  norm_num [Complex.mul_im] at him
  exact ht him

private theorem plusSaddleFiniteRapidContourIntegrand_horizontalStrip_bound
    {ε ℓ r A B : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hr : 0 < r) (N : ℕ)
    (hhalf : -(2 * ((N : ℝ) + 1)) < A)
    (hAB : A ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ Set.Icc A B, ∀ t : ℝ,
        1 ≤ |t| →
          |t| *
            ‖plusSaddleFiniteRapidContourIntegrand ε ℓ N r
              ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨D, hD, hdata⟩ :=
    plusSaddleMellinData_weighted_horizontalStrip_polynomial_bound
      hε hℓ horder hr hAB 1
  obtain ⟨G, hG, hgaussian⟩ :=
    saddleFiniteGaussianPoleWeighted_horizontalStrip_bound
      hr hAB (plusSaddlePoleResidue ε ℓ) N
  refine ⟨D + G, add_nonneg hD hG, ?_⟩
  intro a ha t ht
  have htne : t ≠ 0 := by
    intro hzero
    norm_num [hzero] at ht
  let z : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
  have hz : z ∈ saddleFinitePoleHalfPlane N := by
    change -(2 * ((N : ℝ) + 1)) < z.re
    try dsimp [z]
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im,
      mul_one, sub_self, add_zero] using! hhalf.trans_le ha.1
  have hpoles : ∀ n : ℕ,
      z ≠ (-((2 * n : ℕ) : ℂ)) := by
    intro n
    exact saddleNonzeroFrequency_ne_pole a htne n
  change
    |t| *
      ‖plusSaddleFiniteRapidContourIntegrand ε ℓ N r z‖ ≤
        D + G
  unfold plusSaddleFiniteRapidContourIntegrand
  rw [plusSaddleFiniteRapidPoleRegularPart_eq_subtraction_of_not_pole
    hε horder ℓ N hz hpoles]
  unfold plusSaddleFiniteRapidPoleSubtraction
  rw [mul_sub]
  calc
    |t| *
        ‖saddleMellinInversePower r z *
            plusSaddleMellinData ε ℓ z -
          saddleMellinInversePower r z *
            (∑ n ∈ Finset.range (N + 1),
              plusSaddlePoleResidue ε ℓ n *
                saddleGaussianPoleRepresentative n z)‖ ≤
      |t| *
        (‖saddleMellinInversePower r z *
            plusSaddleMellinData ε ℓ z‖ +
          ‖saddleMellinInversePower r z *
            (∑ n ∈ Finset.range (N + 1),
              plusSaddlePoleResidue ε ℓ n *
                saddleGaussianPoleRepresentative n z)‖) := by
        gcongr
        exact norm_sub_le _ _
    _ = |t| *
          ‖saddleMellinInversePower r z *
            plusSaddleMellinData ε ℓ z‖ +
        |t| *
          ‖saddleMellinInversePower r z *
            (∑ n ∈ Finset.range (N + 1),
              plusSaddlePoleResidue ε ℓ n *
                saddleGaussianPoleRepresentative n z)‖ := by
        ring
    _ ≤ D + G := by
      apply add_le_add
      · simpa only [Complex.norm_mul, pow_one, z] using! hdata a ha t ht
      · simpa only [Complex.norm_mul, z] using! hgaussian a ha t ht

private theorem minusSaddleFiniteRapidContourIntegrand_horizontalStrip_bound
    {ε ℓ r A B : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hr : 0 < r) (N : ℕ)
    (hhalf : -(2 * ((N : ℝ) + 1)) < A)
    (hAB : A ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ Set.Icc A B, ∀ t : ℝ,
        1 ≤ |t| →
          |t| *
            ‖minusSaddleFiniteRapidContourIntegrand ε ℓ N r
              ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨D, hD, hdata⟩ :=
    minusSaddleMellinData_weighted_horizontalStrip_polynomial_bound
      hε hℓ horder hr hAB 1
  obtain ⟨G, hG, hgaussian⟩ :=
    saddleFiniteGaussianPoleWeighted_horizontalStrip_bound
      hr hAB (minusSaddlePoleResidue ε ℓ) N
  refine ⟨D + G, add_nonneg hD hG, ?_⟩
  intro a ha t ht
  have htne : t ≠ 0 := by
    intro hzero
    norm_num [hzero] at ht
  let z : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
  have hz : z ∈ saddleFinitePoleHalfPlane N := by
    change -(2 * ((N : ℝ) + 1)) < z.re
    try dsimp [z]
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im,
      mul_one, sub_self, add_zero] using! hhalf.trans_le ha.1
  have hpoles : ∀ n : ℕ,
      z ≠ (-((2 * n : ℕ) : ℂ)) := by
    intro n
    exact saddleNonzeroFrequency_ne_pole a htne n
  change
    |t| *
      ‖minusSaddleFiniteRapidContourIntegrand ε ℓ N r z‖ ≤
        D + G
  unfold minusSaddleFiniteRapidContourIntegrand
  rw [minusSaddleFiniteRapidPoleRegularPart_eq_subtraction_of_not_pole
    hε horder ℓ N hz hpoles]
  unfold minusSaddleFiniteRapidPoleSubtraction
  rw [mul_sub]
  calc
    |t| *
        ‖saddleMellinInversePower r z *
            minusSaddleMellinData ε ℓ z -
          saddleMellinInversePower r z *
            (∑ n ∈ Finset.range (N + 1),
              minusSaddlePoleResidue ε ℓ n *
                saddleGaussianPoleRepresentative n z)‖ ≤
      |t| *
        (‖saddleMellinInversePower r z *
            minusSaddleMellinData ε ℓ z‖ +
          ‖saddleMellinInversePower r z *
            (∑ n ∈ Finset.range (N + 1),
              minusSaddlePoleResidue ε ℓ n *
                saddleGaussianPoleRepresentative n z)‖) := by
        gcongr
        exact norm_sub_le _ _
    _ = |t| *
          ‖saddleMellinInversePower r z *
            minusSaddleMellinData ε ℓ z‖ +
        |t| *
          ‖saddleMellinInversePower r z *
            (∑ n ∈ Finset.range (N + 1),
              minusSaddlePoleResidue ε ℓ n *
                saddleGaussianPoleRepresentative n z)‖ := by
        ring
    _ ≤ D + G := by
      apply add_le_add
      · simpa only [Complex.norm_mul, pow_one, z] using! hdata a ha t ht
      · simpa only [Complex.norm_mul, z] using! hgaussian a ha t ht

private theorem plusSaddleFiniteRapidContourIntegrand_horizontalIntegral_tendsto_zero
    {ε ℓ r A B : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hr : 0 < r) (N : ℕ)
    (hhalf : -(2 * ((N : ℝ) + 1)) < A)
    (hAB : A ≤ B)
    (s : ℝ) (hs : |s| = 1) :
    Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          plusSaddleFiniteRapidContourIntegrand ε ℓ N r
            ((a : ℂ) + ((s * T : ℝ) : ℂ) * Complex.I))
      Filter.atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    plusSaddleFiniteRapidContourIntegrand_horizontalStrip_bound
      hε hℓ horder hr N hhalf hAB
  exact saddleHorizontalIntegral_tendsto_zero
    (F := plusSaddleFiniteRapidContourIntegrand ε ℓ N r)
    hAB hbound s hs

private theorem minusSaddleFiniteRapidContourIntegrand_horizontalIntegral_tendsto_zero
    {ε ℓ r A B : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hr : 0 < r) (N : ℕ)
    (hhalf : -(2 * ((N : ℝ) + 1)) < A)
    (hAB : A ≤ B)
    (s : ℝ) (hs : |s| = 1) :
    Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          minusSaddleFiniteRapidContourIntegrand ε ℓ N r
            ((a : ℂ) + ((s * T : ℝ) : ℂ) * Complex.I))
      Filter.atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    minusSaddleFiniteRapidContourIntegrand_horizontalStrip_bound
      hε hℓ horder hr N hhalf hAB
  exact saddleHorizontalIntegral_tendsto_zero
    (F := minusSaddleFiniteRapidContourIntegrand ε ℓ N r)
    hAB hbound s hs

private noncomputable def saddleCauchyPolePrimitive (a t : ℝ) : ℂ :=
  (Real.arctan (t / a) : ℂ) -
    ((Real.log (a ^ 2 + t ^ 2) / 2 : ℝ) : ℂ) *
      Complex.I

private theorem saddleCauchyPolePrimitive_hasDerivAt
    {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    HasDerivAt (saddleCauchyPolePrimitive a)
      (((a : ℂ) + (t : ℂ) * Complex.I)⁻¹) t := by
  have hden : a ^ 2 + t ^ 2 ≠ 0 := by
    have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
    linarith [sq_nonneg t]
  have hatan : HasDerivAt
      (fun y : ℝ => Real.arctan (y / a))
      (a / (a ^ 2 + t ^ 2)) t := by
    convert! (Real.hasDerivAt_arctan (t / a)).comp t
      ((hasDerivAt_id t).div_const a) using 1
    field_simp [ha, hden]
  have hquadratic : HasDerivAt
      (fun y : ℝ => a ^ 2 + y ^ 2)
      (2 * t) t := by
    convert! ((hasDerivAt_id t).pow 2).const_add
      (a ^ 2) using 1; simp only [Nat.cast_ofNat, id, Nat.add_one_sub_one, pow_one, mul_one]
  have hlog : HasDerivAt
      (fun y : ℝ => Real.log (a ^ 2 + y ^ 2) / 2)
      (t / (a ^ 2 + t ^ 2)) t := by
    convert! ((Real.hasDerivAt_log hden).comp t
      hquadratic).div_const 2 using 1
    field_simp [hden]
  have hvalue :
      ((a / (a ^ 2 + t ^ 2) : ℝ) : ℂ) -
        ((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) *
          Complex.I =
      ((a : ℂ) + (t : ℂ) * Complex.I)⁻¹ := by
    have hz : (a : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
      intro hz
      apply ha
      have hre := congrArg Complex.re hz
      simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im,
        Complex.I_im, mul_one, sub_self, add_zero, Complex.zero_re] using! hre
    have hcden : ((a ^ 2 + t ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hden
    have hcden' : (a : ℂ) ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by
      simpa only [ne_eq, Complex.ofReal_add, Complex.ofReal_pow] using! hcden
    apply (mul_eq_one_iff_eq_inv₀ hz).mp
    push_cast
    field_simp [hcden', Complex.I_sq]; ring_nf; simp only [Complex.I_sq, mul_neg, mul_one,
      sub_neg_eq_add]
  rw [← hvalue]
  exact hatan.ofReal_comp.sub
    (hlog.ofReal_comp.mul_const Complex.I)

private theorem saddleCauchyPole_symmetric_intervalIntegral
    {a : ℝ} (ha : a ≠ 0) (T : ℝ) :
    (∫ t in -T..T,
      ((a : ℂ) + (t : ℂ) * Complex.I)⁻¹) =
      ((2 * Real.arctan (T / a) : ℝ) : ℂ) := by
  have hline : Continuous
      (fun t : ℝ => (a : ℂ) + (t : ℂ) * Complex.I) := by
    fun_prop
  have hnonzero : ∀ t : ℝ,
      (a : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro t hzero
    apply ha
    have hre := congrArg Complex.re hzero
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im,
      Complex.I_im, mul_one, sub_self, add_zero, Complex.zero_re] using! hre
  have hint : IntervalIntegrable
      (fun t : ℝ =>
        ((a : ℂ) + (t : ℂ) * Complex.I)⁻¹)
      volume (-T) T :=
    (hline.inv₀ hnonzero).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => saddleCauchyPolePrimitive_hasDerivAt ha t)
      hint]
  unfold saddleCauchyPolePrimitive
  simp only [Complex.ofReal_arctan, Complex.ofReal_div, pow_two, Complex.ofReal_ofNat, neg_div,
    Real.arctan_neg,
    Complex.ofReal_neg, mul_neg, neg_mul, neg_neg, sub_sub_sub_cancel_right, sub_neg_eq_add,
      Complex.ofReal_mul]; ring

private theorem saddleInfiniteRectangle_vertical_integral_eq
    {F : ℂ → ℂ} {A B : ℝ}
    (hA : Integrable
      (fun t : ℝ => F ((A : ℂ) + (t : ℂ) * Complex.I)))
    (hB : Integrable
      (fun t : ℝ => F ((B : ℂ) + (t : ℂ) * Complex.I)))
    (hlower : Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          F ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      Filter.atTop (𝓝 0))
    (hupper : Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          F ((a : ℂ) + (T : ℂ) * Complex.I))
      Filter.atTop (𝓝 0))
    (hrectangle : ∀ T : ℝ,
      (∫ a in A..B,
        F ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
      (∫ a in A..B,
        F ((a : ℂ) + (T : ℂ) * Complex.I)) +
      Complex.I *
        (∫ t in -T..T,
          F ((B : ℂ) + (t : ℂ) * Complex.I)) -
      Complex.I *
        (∫ t in -T..T,
          F ((A : ℂ) + (t : ℂ) * Complex.I)) = 0) :
    (∫ t : ℝ,
      F ((B : ℂ) + (t : ℂ) * Complex.I)) =
    (∫ t : ℝ,
      F ((A : ℂ) + (t : ℂ) * Complex.I)) := by
  have hright : Tendsto
      (fun T : ℝ =>
        ∫ t in -T..T,
          F ((B : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop
      (𝓝 (∫ t : ℝ,
        F ((B : ℂ) + (t : ℂ) * Complex.I))) :=
    intervalIntegral_tendsto_integral hB
      tendsto_neg_atTop_atBot tendsto_id
  have hleft : Tendsto
      (fun T : ℝ =>
        ∫ t in -T..T,
          F ((A : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop
      (𝓝 (∫ t : ℝ,
        F ((A : ℂ) + (t : ℂ) * Complex.I))) :=
    intervalIntegral_tendsto_integral hA
      tendsto_neg_atTop_atBot tendsto_id
  have hlimit : Tendsto
      (fun T : ℝ =>
        (∫ a in A..B,
          F ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
        (∫ a in A..B,
          F ((a : ℂ) + (T : ℂ) * Complex.I)) +
        Complex.I *
          (∫ t in -T..T,
            F ((B : ℂ) + (t : ℂ) * Complex.I)) -
        Complex.I *
          (∫ t in -T..T,
            F ((A : ℂ) + (t : ℂ) * Complex.I)))
      Filter.atTop
      (𝓝 (Complex.I *
        (∫ t : ℝ,
          F ((B : ℂ) + (t : ℂ) * Complex.I)) -
        Complex.I *
        (∫ t : ℝ,
          F ((A : ℂ) + (t : ℂ) * Complex.I)))) := by
    simpa only [Complex.ofReal_neg, neg_mul, sub_self, zero_add] using!
      (((hlower.sub hupper).add
        (tendsto_const_nhds.mul hright)).sub
          (tendsto_const_nhds.mul hleft))
  have hzero : Tendsto
      (fun T : ℝ =>
        (∫ a in A..B,
          F ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
        (∫ a in A..B,
          F ((a : ℂ) + (T : ℂ) * Complex.I)) +
        Complex.I *
          (∫ t in -T..T,
            F ((B : ℂ) + (t : ℂ) * Complex.I)) -
        Complex.I *
          (∫ t in -T..T,
            F ((A : ℂ) + (t : ℂ) * Complex.I)))
      Filter.atTop (𝓝 0) :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (0 : ℂ))
        Filter.atTop (𝓝 0)).congr'
          (Filter.Eventually.of_forall
            (fun T : ℝ => (hrectangle T).symm))
  have hidentity :
      Complex.I *
        ((∫ t : ℝ,
          F ((B : ℂ) + (t : ℂ) * Complex.I)) -
          (∫ t : ℝ,
            F ((A : ℂ) + (t : ℂ) * Complex.I))) = 0 := by
    simpa only [mul_sub] using!
      (tendsto_nhds_unique hlimit hzero)
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp hidentity).resolve_left
      Complex.I_ne_zero)

private theorem plusSaddleFiniteRapidContourIntegrand_vertical_integral_eq
    {ε ℓ r A B : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hr : 0 < r) (N : ℕ)
    (hhalf : -(2 * ((N : ℝ) + 1)) < A)
    (hAB : A ≤ B)
    (hApole : ∀ n : ℕ, A ≠ -((2 * n : ℕ) : ℝ))
    (hBpole : ∀ n : ℕ, B ≠ -((2 * n : ℕ) : ℝ)) :
    (∫ t : ℝ,
      plusSaddleFiniteRapidContourIntegrand ε ℓ N r
        ((B : ℂ) + (t : ℂ) * Complex.I)) =
    (∫ t : ℝ,
      plusSaddleFiniteRapidContourIntegrand ε ℓ N r
        ((A : ℂ) + (t : ℂ) * Complex.I)) := by
  have hhalfB : -(2 * ((N : ℝ) + 1)) < B :=
    hhalf.trans_le hAB
  have hleft :=
    plusSaddleFiniteRapidContourIntegrand_shiftedLine_integrable
      hε hℓ horder N hhalf hApole hr
  have hright :=
    plusSaddleFiniteRapidContourIntegrand_shiftedLine_integrable
      hε hℓ horder N hhalfB hBpole hr
  have hlower : Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          plusSaddleFiniteRapidContourIntegrand ε ℓ N r
            ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      Filter.atTop (𝓝 0) := by
    simpa only [Complex.ofReal_neg, neg_mul, one_mul] using!
      plusSaddleFiniteRapidContourIntegrand_horizontalIntegral_tendsto_zero
        hε hℓ horder hr N hhalf hAB
          (-1 : ℝ) (by norm_num)
  have hupper : Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          plusSaddleFiniteRapidContourIntegrand ε ℓ N r
            ((a : ℂ) + (T : ℂ) * Complex.I))
      Filter.atTop (𝓝 0) := by
    simpa only [one_mul] using!
      plusSaddleFiniteRapidContourIntegrand_horizontalIntegral_tendsto_zero
        hε hℓ horder hr N hhalf hAB
          (1 : ℝ) (by norm_num)
  apply saddleInfiniteRectangle_vertical_integral_eq
    hleft hright hlower hupper
  intro T
  let z : ℂ := (A : ℂ) + ((-T : ℝ) : ℂ) * Complex.I
  let w : ℂ := (B : ℂ) + (T : ℂ) * Complex.I
  have hz : z ∈ saddleFinitePoleHalfPlane N := by
    change -(2 * ((N : ℝ) + 1)) < z.re
    simpa [z, Complex.mul_re] using! hhalf
  have hw : w ∈ saddleFinitePoleHalfPlane N := by
    change -(2 * ((N : ℝ) + 1)) < w.re
    simpa [w, Complex.mul_re] using! hhalfB
  simpa [z, w, Complex.mul_re, Complex.mul_im,
    smul_eq_mul] using!
      plusSaddleFiniteRapidContourIntegrand_boundary_rectangle
        hε horder ℓ N hr z w hz hw

private theorem minusSaddleFiniteRapidContourIntegrand_vertical_integral_eq
    {ε ℓ r A B : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hr : 0 < r) (N : ℕ)
    (hhalf : -(2 * ((N : ℝ) + 1)) < A)
    (hAB : A ≤ B)
    (hApole : ∀ n : ℕ, A ≠ -((2 * n : ℕ) : ℝ))
    (hBpole : ∀ n : ℕ, B ≠ -((2 * n : ℕ) : ℝ)) :
    (∫ t : ℝ,
      minusSaddleFiniteRapidContourIntegrand ε ℓ N r
        ((B : ℂ) + (t : ℂ) * Complex.I)) =
    (∫ t : ℝ,
      minusSaddleFiniteRapidContourIntegrand ε ℓ N r
        ((A : ℂ) + (t : ℂ) * Complex.I)) := by
  have hhalfB : -(2 * ((N : ℝ) + 1)) < B :=
    hhalf.trans_le hAB
  have hleft :=
    minusSaddleFiniteRapidContourIntegrand_shiftedLine_integrable
      hε hℓ horder N hhalf hApole hr
  have hright :=
    minusSaddleFiniteRapidContourIntegrand_shiftedLine_integrable
      hε hℓ horder N hhalfB hBpole hr
  have hlower : Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          minusSaddleFiniteRapidContourIntegrand ε ℓ N r
            ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      Filter.atTop (𝓝 0) := by
    simpa only [Complex.ofReal_neg, neg_mul, one_mul] using!
      minusSaddleFiniteRapidContourIntegrand_horizontalIntegral_tendsto_zero
        hε hℓ horder hr N hhalf hAB
          (-1 : ℝ) (by norm_num)
  have hupper : Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          minusSaddleFiniteRapidContourIntegrand ε ℓ N r
            ((a : ℂ) + (T : ℂ) * Complex.I))
      Filter.atTop (𝓝 0) := by
    simpa only [one_mul] using!
      minusSaddleFiniteRapidContourIntegrand_horizontalIntegral_tendsto_zero
        hε hℓ horder hr N hhalf hAB
          (1 : ℝ) (by norm_num)
  apply saddleInfiniteRectangle_vertical_integral_eq
    hleft hright hlower hupper
  intro T
  let z : ℂ := (A : ℂ) + ((-T : ℝ) : ℂ) * Complex.I
  let w : ℂ := (B : ℂ) + (T : ℂ) * Complex.I
  have hz : z ∈ saddleFinitePoleHalfPlane N := by
    change -(2 * ((N : ℝ) + 1)) < z.re
    simpa [z, Complex.mul_re] using! hhalf
  have hw : w ∈ saddleFinitePoleHalfPlane N := by
    change -(2 * ((N : ℝ) + 1)) < w.re
    simpa [w, Complex.mul_re] using! hhalfB
  simpa [z, w, Complex.mul_re, Complex.mul_im,
    smul_eq_mul] using!
      minusSaddleFiniteRapidContourIntegrand_boundary_rectangle
        hε horder ℓ N hr z w hz hw

private theorem plusSaddleSpectrum_moment_integrable {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) (k : ℕ) :
    Integrable (fun t : ℝ =>
      (t : ℂ) ^ k * plusSaddleSpectrum ε ℓ t) := by
  apply integrable_of_continuous_polynomial_decay
    (plusSaddleSpectrum_continuous hε hℓ horder)
  intro j
  refine ⟨((1 + |(ε / 4)|) * (1 + ℓ⁻¹) ^ 3) *
    ((2 : ℝ) ^ (j + 3) *
      Real.Gamma (ℓ / 2 + (j + 3)) *
      Real.exp (2 * |ℓ| * saddleShellTotalVariation ε)), ?_, ?_⟩
  · have hgamma : 0 < Real.Gamma (ℓ / 2 + (j + 3)) :=
      Real.Gamma_pos_of_pos (by positivity)
    positivity
  · intro t ht
    exact plusSaddleSpectrum_vertical_polynomial_bound
      hε hℓ horder ht j

private theorem minusSaddleSpectrum_moment_integrable {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) (k : ℕ) :
    Integrable (fun t : ℝ =>
      (t : ℂ) ^ k * minusSaddleSpectrum ε ℓ t) := by
  apply integrable_of_continuous_polynomial_decay
    (minusSaddleSpectrum_continuous hε hℓ horder)
  intro j
  refine ⟨((1 + |(ε / 4)|) * (1 + ℓ⁻¹) ^ 3) *
    ((2 : ℝ) ^ (j + 3) *
      Real.Gamma (ℓ / 2 + (j + 3)) *
      Real.exp (2 * |ℓ| * saddleShellTotalVariation ε)), ?_, ?_⟩
  · have hgamma : 0 < Real.Gamma (ℓ / 2 + (j + 3)) :=
      Real.Gamma_pos_of_pos (by positivity)
    positivity
  · intro t ht
    exact minusSaddleSpectrum_vertical_polynomial_bound
      hε hℓ horder ht j

private theorem plusSaddleSpectrum_norm_moment_integrable {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) (k : ℕ) :
    Integrable (fun t : ℝ =>
      |t| ^ k * ‖plusSaddleSpectrum ε ℓ t‖) := by
  simpa only [Complex.norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] using!
      (plusSaddleSpectrum_moment_integrable
        hε hℓ horder k).norm

private theorem minusSaddleSpectrum_norm_moment_integrable {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) (k : ℕ) :
    Integrable (fun t : ℝ =>
      |t| ^ k * ‖minusSaddleSpectrum ε ℓ t‖) := by
  simpa only [Complex.norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] using!
      (minusSaddleSpectrum_moment_integrable
        hε hℓ horder k).norm

private noncomputable def plusSaddleFourierData (ε ℓ y : ℝ) : ℂ :=
  plusSaddleSpectrum ε ℓ (-(2 * Real.pi * y))

private noncomputable def minusSaddleFourierData (ε ℓ y : ℝ) : ℂ :=
  minusSaddleSpectrum ε ℓ (-(2 * Real.pi * y))

private theorem integrable_scaled_norm_moment
    {F : ℝ → ℂ} (hF : Continuous F)
    (hmom : ∀ j : ℕ,
      Integrable (fun t : ℝ => |t| ^ j * ‖F t‖))
    {c : ℝ} (hc : c ≠ 0) (hclarge : 1 ≤ |c|) (k : ℕ) :
    Integrable (fun y : ℝ => ‖y‖ ^ k * ‖F (c * y)‖) := by
  have hbase : Integrable (fun y : ℝ =>
      |c * y| ^ k * ‖F (c * y)‖) :=
    (hmom k).comp_mul_left' hc
  have hcomp : Continuous (fun y : ℝ => F (c * y)) :=
    hF.comp (by fun_prop)
  have hmeas : AEStronglyMeasurable
      (fun y : ℝ => |y| ^ k * ‖F (c * y)‖) :=
    ((continuous_abs.pow k).mul hcomp.norm).aestronglyMeasurable
  have hresult : Integrable
      (fun y : ℝ => |y| ^ k * ‖F (c * y)‖) := by
    apply hbase.mono' hmeas
    filter_upwards [] with y
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (pow_nonneg (abs_nonneg y) k)
        (norm_nonneg _))]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [abs_mul]
    gcongr
    calc
      |y| = 1 * |y| := by ring
      _ ≤ |c| * |y| := by gcongr
  simpa only [Real.norm_eq_abs] using! hresult

private theorem plusSaddleFourierData_norm_moment_integrable {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) (k : ℕ) :
    Integrable (fun y : ℝ =>
      ‖y‖ ^ k * ‖plusSaddleFourierData ε ℓ y‖) := by
  let c : ℝ := -(2 * Real.pi)
  have hc : c ≠ 0 := by
    try dsimp [c]
    exact neg_ne_zero.mpr
      (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hclarge : 1 ≤ |c| := by
    try dsimp [c]
    rw [abs_neg, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    linarith [Real.pi_gt_three]
  have h := integrable_scaled_norm_moment
    (plusSaddleSpectrum_continuous hε hℓ horder)
    (fun j => plusSaddleSpectrum_norm_moment_integrable
      hε hℓ horder j) hc hclarge k
  simpa [plusSaddleFourierData, c, neg_mul, mul_assoc] using! h

private theorem minusSaddleFourierData_norm_moment_integrable {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) (k : ℕ) :
    Integrable (fun y : ℝ =>
      ‖y‖ ^ k * ‖minusSaddleFourierData ε ℓ y‖) := by
  let c : ℝ := -(2 * Real.pi)
  have hc : c ≠ 0 := by
    try dsimp [c]
    exact neg_ne_zero.mpr
      (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hclarge : 1 ≤ |c| := by
    try dsimp [c]
    rw [abs_neg, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    linarith [Real.pi_gt_three]
  have h := integrable_scaled_norm_moment
    (minusSaddleSpectrum_continuous hε hℓ horder)
    (fun j => minusSaddleSpectrum_norm_moment_integrable
      hε hℓ horder j) hc hclarge k
  simpa [minusSaddleFourierData, c, neg_mul, mul_assoc] using! h

private theorem plusSaddleFourierData_fourier_contDiff {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    ContDiff ℝ ∞ (𝓕 (plusSaddleFourierData ε ℓ)) := by
  exact Real.contDiff_fourier (N := ⊤) (fun n _ =>
    plusSaddleFourierData_norm_moment_integrable
      hε hℓ horder n)

private theorem minusSaddleFourierData_fourier_contDiff {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    ContDiff ℝ ∞ (𝓕 (minusSaddleFourierData ε ℓ)) := by
  exact Real.contDiff_fourier (N := ⊤) (fun n _ =>
    minusSaddleFourierData_norm_moment_integrable
      hε hℓ horder n)

private theorem plusSaddleMellinData_fourier_vertical (ε ℓ y : ℝ) :
    plusSaddleMellinData ε ℓ
      ((ℓ : ℂ) + (2 * Real.pi * y : ℝ) * Complex.I) =
        plusSaddleFourierData ε ℓ y := by
  have harg :
      ((ℓ : ℂ) + (2 * Real.pi * y : ℝ) * Complex.I) =
        ((ℓ : ℂ) - Complex.I *
          ((-(2 * Real.pi * y) : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [harg, plusSaddleMellinData_vertical]
  rfl

private theorem minusSaddleMellinData_fourier_vertical (ε ℓ y : ℝ) :
    minusSaddleMellinData ε ℓ
      ((ℓ : ℂ) + (2 * Real.pi * y : ℝ) * Complex.I) =
        minusSaddleFourierData ε ℓ y := by
  have harg :
      ((ℓ : ℂ) + (2 * Real.pi * y : ℝ) * Complex.I) =
        ((ℓ : ℂ) - Complex.I *
          ((-(2 * Real.pi * y) : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [harg, minusSaddleMellinData_vertical]
  rfl

private theorem plusSaddleProfile_eq_fourier (ε ℓ : ℝ)
    {r : ℝ} (hr : 0 < r) :
    plusSaddleProfile ε ℓ r =
      (r ^ (-ℓ) : ℝ) *
        (𝓕 (plusSaddleFourierData ε ℓ)) (Real.log r) := by
  have hline : (fun y : ℝ =>
      plusSaddleMellinData ε ℓ
        ((ℓ : ℂ) + 2 * (Real.pi : ℂ) * (y : ℂ) * Complex.I)) =
        plusSaddleFourierData ε ℓ := by
    funext y
    simpa only [Complex.ofReal_mul,
      Complex.ofReal_ofNat] using! plusSaddleMellinData_fourier_vertical ε ℓ y
  unfold plusSaddleProfile
  rw [ite_eq_right hr.ne', mellinInv_eq_fourierInv ℓ
    (plusSaddleMellinData ε ℓ) hr, hline,
    Real.fourierInv_eq_fourier_neg]
  simp only [neg_neg, smul_eq_mul]
  have hpow :
      (r : ℂ) ^ (-(ℓ : ℂ)) = ((r ^ (-ℓ) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_neg] using! (Complex.ofReal_cpow hr.le (-ℓ)).symm
  rw [hpow]

private theorem minusSaddleProfile_eq_fourier (ε ℓ : ℝ)
    {r : ℝ} (hr : 0 < r) :
    minusSaddleProfile ε ℓ r =
      (r ^ (-ℓ) : ℝ) *
        (𝓕 (minusSaddleFourierData ε ℓ)) (Real.log r) := by
  have hline : (fun y : ℝ =>
      minusSaddleMellinData ε ℓ
        ((ℓ : ℂ) + 2 * (Real.pi : ℂ) * (y : ℂ) * Complex.I)) =
        minusSaddleFourierData ε ℓ := by
    funext y
    simpa only [Complex.ofReal_mul,
      Complex.ofReal_ofNat] using! minusSaddleMellinData_fourier_vertical ε ℓ y
  unfold minusSaddleProfile
  rw [ite_eq_right hr.ne', mellinInv_eq_fourierInv ℓ
    (minusSaddleMellinData ε ℓ) hr, hline,
    Real.fourierInv_eq_fourier_neg]
  simp only [neg_neg, smul_eq_mul]
  have hpow :
      (r : ℂ) ^ (-(ℓ : ℂ)) = ((r ^ (-ℓ) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_neg] using! (Complex.ofReal_cpow hr.le (-ℓ)).symm
  rw [hpow]

private theorem plusSaddleProfile_contDiffOn {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    ContDiffOn ℝ ∞ (plusSaddleProfile ε ℓ) (Set.Ioi 0) := by
  have hpow : ContDiffOn ℝ ∞
      (fun r : ℝ => r ^ (-ℓ)) (Set.Ioi 0) :=
    contDiff_id.contDiffOn.rpow_const_of_ne
      (fun r hr => (show 0 < r from hr).ne')
  have hweight : ContDiffOn ℝ ∞
      (fun r : ℝ => ((r ^ (-ℓ) : ℝ) : ℂ)) (Set.Ioi 0) :=
    Complex.ofRealCLM.contDiff.fun_comp_contDiffOn hpow
  have hlog : ContDiffOn ℝ ∞ Real.log (Set.Ioi 0) :=
    contDiff_id.contDiffOn.log
      (fun r hr => (show 0 < r from hr).ne')
  have hfourier : ContDiffOn ℝ ∞
      (fun r : ℝ =>
        (𝓕 (plusSaddleFourierData ε ℓ)) (Real.log r))
      (Set.Ioi 0) :=
    (plusSaddleFourierData_fourier_contDiff hε hℓ horder).fun_comp_contDiffOn hlog
  exact (hweight.mul hfourier).congr
    (fun r hr => (plusSaddleProfile_eq_fourier
      ε ℓ (show 0 < r from hr)))

private theorem minusSaddleProfile_contDiffOn {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    ContDiffOn ℝ ∞ (minusSaddleProfile ε ℓ) (Set.Ioi 0) := by
  have hpow : ContDiffOn ℝ ∞
      (fun r : ℝ => r ^ (-ℓ)) (Set.Ioi 0) :=
    contDiff_id.contDiffOn.rpow_const_of_ne
      (fun r hr => (show 0 < r from hr).ne')
  have hweight : ContDiffOn ℝ ∞
      (fun r : ℝ => ((r ^ (-ℓ) : ℝ) : ℂ)) (Set.Ioi 0) :=
    Complex.ofRealCLM.contDiff.fun_comp_contDiffOn hpow
  have hlog : ContDiffOn ℝ ∞ Real.log (Set.Ioi 0) :=
    contDiff_id.contDiffOn.log
      (fun r hr => (show 0 < r from hr).ne')
  have hfourier : ContDiffOn ℝ ∞
      (fun r : ℝ =>
        (𝓕 (minusSaddleFourierData ε ℓ)) (Real.log r))
      (Set.Ioi 0) :=
    (minusSaddleFourierData_fourier_contDiff hε hℓ horder).fun_comp_contDiffOn hlog
  exact (hweight.mul hfourier).congr
    (fun r hr => (minusSaddleProfile_eq_fourier
      ε ℓ (show 0 < r from hr)))

private theorem plusSaddleFunction_contDiffOn {ε : ℝ}
    (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    ContDiffOn ℝ ∞ (plusSaddleFunction ε d)
      ({0}ᶜ : Set (Euclidean d)) := by
  have hdimension : 0 < (d : ℝ) / 2 := by
    exact div_pos (by exact_mod_cast hd) (by norm_num)
  have hnorm : ContDiffOn ℝ ∞
      (fun x : Euclidean d => ‖x‖)
      ({0}ᶜ : Set (Euclidean d)) := by
    apply ContDiffOn.norm ℝ
    · exact contDiff_id.contDiffOn
    · intro x hx
      simpa only [Set.mem_compl_iff,
        Set.mem_singleton_iff] using! hx
  have hmaps : Set.MapsTo
      (fun x : Euclidean d => ‖x‖)
      ({0}ᶜ : Set (Euclidean d)) (Set.Ioi 0) := by
    intro x hx
    apply norm_pos_iff.mpr
    simpa only [Set.mem_compl_iff,
      Set.mem_singleton_iff] using! hx
  simpa only [plusSaddleFunction, Function.comp_apply] using!
    (plusSaddleProfile_contDiffOn
      hε hdimension horder).comp hnorm hmaps

private theorem minusSaddleFunction_contDiffOn {ε : ℝ}
    (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    ContDiffOn ℝ ∞ (minusSaddleFunction ε d)
      ({0}ᶜ : Set (Euclidean d)) := by
  have hdimension : 0 < (d : ℝ) / 2 := by
    exact div_pos (by exact_mod_cast hd) (by norm_num)
  have hnorm : ContDiffOn ℝ ∞
      (fun x : Euclidean d => ‖x‖)
      ({0}ᶜ : Set (Euclidean d)) := by
    apply ContDiffOn.norm ℝ
    · exact contDiff_id.contDiffOn
    · intro x hx
      simpa only [Set.mem_compl_iff,
        Set.mem_singleton_iff] using! hx
  have hmaps : Set.MapsTo
      (fun x : Euclidean d => ‖x‖)
      ({0}ᶜ : Set (Euclidean d)) (Set.Ioi 0) := by
    intro x hx
    apply norm_pos_iff.mpr
    simpa only [Set.mem_compl_iff,
      Set.mem_singleton_iff] using! hx
  simpa only [minusSaddleFunction, Function.comp_apply] using!
    (minusSaddleProfile_contDiffOn
      hε hdimension horder).comp hnorm hmaps

private theorem plusSaddleSpectrum_conj (ε ℓ t : ℝ) :
    starRingEnd ℂ (plusSaddleSpectrum ε ℓ t) =
      plusSaddleSpectrum ε ℓ (-t) := by
  unfold plusSaddleSpectrum
  rw [map_mul, saddleEnvelope_conj, plusPolynomial_conj]
  congr 1
  simp only [map_div₀, Complex.conj_ofReal]
  have hneg :
      ((-t : ℝ) : ℂ) / (ℓ : ℂ) =
        -((t : ℂ) / (ℓ : ℂ)) := by
    push_cast
    ring
  rw [hneg]
  simpa only [neg_neg] using!
    (minusPolynomial_neg ε (-((t : ℂ) / (ℓ : ℂ))))

private theorem minusSaddleSpectrum_conj (ε ℓ t : ℝ) :
    starRingEnd ℂ (minusSaddleSpectrum ε ℓ t) =
      minusSaddleSpectrum ε ℓ (-t) := by
  unfold minusSaddleSpectrum
  rw [map_mul, saddleEnvelope_conj, minusPolynomial_conj]
  congr 1
  simp only [map_div₀, Complex.conj_ofReal]
  have hneg :
      ((-t : ℝ) : ℂ) / (ℓ : ℂ) =
        -((t : ℂ) / (ℓ : ℂ)) := by
    push_cast
    ring
  rw [hneg]
  exact (minusPolynomial_neg ε ((t : ℂ) / (ℓ : ℂ))).symm

private theorem mellinInversePower_conj {r : ℝ} (hr : 0 < r)
    (σ t : ℝ) :
    starRingEnd ℂ
      ((r : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) =
        (r : ℂ) ^
          (-((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)) := by
  have harg : (r : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hr.le]
    exact Real.pi_ne_zero.symm
  have hpower :=
    (Complex.cpow_conj (r : ℂ)
      (-((σ : ℂ) + (t : ℂ) * Complex.I)) harg).symm
  simpa only [neg_add_rev, Complex.ofReal_neg, neg_mul, neg_neg, Complex.conj_ofReal, map_add,
    map_neg, map_mul,
    Complex.conj_I, mul_neg] using! hpower

private theorem mellinInv_real_of_hermitian (σ : ℝ) (F : ℂ → ℂ)
    (hF : ∀ t : ℝ,
      starRingEnd ℂ (F ((σ : ℂ) + (t : ℂ) * Complex.I)) =
        F ((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I))
    {r : ℝ} (hr : 0 < r) :
    (mellinInv σ F r).im = 0 := by
  let g : ℝ → ℂ := fun t =>
    (r : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) *
      F ((σ : ℂ) + (t : ℂ) * Complex.I)
  have hsym (t : ℝ) :
      starRingEnd ℂ (g t) = g (-t) := by
    try dsimp [g]
    rw [map_mul, mellinInversePower_conj hr σ t, hF t]
  have hintegral :
      starRingEnd ℂ (∫ t : ℝ, g t) = ∫ t : ℝ, g t := by
    calc
      starRingEnd ℂ (∫ t : ℝ, g t) =
          ∫ t : ℝ, starRingEnd ℂ (g t) :=
            (integral_conj (f := g)).symm
      _ = ∫ t : ℝ, g (-t) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with t
            exact hsym t
      _ = ∫ t : ℝ, g t := by
            rw [integral_neg_eq_self]
  have hrewrite :
      mellinInv σ F r =
        (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, g t := by
    unfold mellinInv
    simp only [g, smul_eq_mul]
  apply Complex.conj_eq_iff_im.mp
  rw [hrewrite]
  simp only [Complex.real_smul, map_mul, Complex.conj_ofReal,
    hintegral]

private theorem plusSaddleMellinData_conj_vertical (ε ℓ t : ℝ) :
    starRingEnd ℂ
      (plusSaddleMellinData ε ℓ
        ((ℓ : ℂ) + (t : ℂ) * Complex.I)) =
      plusSaddleMellinData ε ℓ
        ((ℓ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) := by
  have hleft :
      ((ℓ : ℂ) + (t : ℂ) * Complex.I) =
        ((ℓ : ℂ) - Complex.I * ((-t : ℝ) : ℂ)) := by
    push_cast
    ring
  have hright :
      ((ℓ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) =
        ((ℓ : ℂ) - Complex.I * (t : ℂ)) := by
    push_cast
    ring
  rw [hleft, plusSaddleMellinData_vertical,
    hright, plusSaddleMellinData_vertical]
  simpa only [neg_neg] using! plusSaddleSpectrum_conj ε ℓ (-t)

private theorem minusSaddleMellinData_conj_vertical (ε ℓ t : ℝ) :
    starRingEnd ℂ
      (minusSaddleMellinData ε ℓ
        ((ℓ : ℂ) + (t : ℂ) * Complex.I)) =
      minusSaddleMellinData ε ℓ
        ((ℓ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) := by
  have hleft :
      ((ℓ : ℂ) + (t : ℂ) * Complex.I) =
        ((ℓ : ℂ) - Complex.I * ((-t : ℝ) : ℂ)) := by
    push_cast
    ring
  have hright :
      ((ℓ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) =
        ((ℓ : ℂ) - Complex.I * (t : ℂ)) := by
    push_cast
    ring
  rw [hleft, minusSaddleMellinData_vertical,
    hright, minusSaddleMellinData_vertical]
  simpa only [neg_neg] using! minusSaddleSpectrum_conj ε ℓ (-t)

private theorem plusSaddleProfile_real (ε ℓ : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (plusSaddleProfile ε ℓ r).im = 0 := by
  by_cases hzero : r = 0
  · simp only [plusSaddleProfile, hzero, ↓reduceIte, Complex.ofReal_im]
  · have hpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hzero)
    simp only [plusSaddleProfile, ite_eq_right hzero]
    exact mellinInv_real_of_hermitian ℓ
      (plusSaddleMellinData ε ℓ)
      (plusSaddleMellinData_conj_vertical ε ℓ) hpos

private theorem minusSaddleProfile_real (ε ℓ : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (minusSaddleProfile ε ℓ r).im = 0 := by
  by_cases hzero : r = 0
  · simp only [minusSaddleProfile, hzero, ↓reduceIte, Complex.ofReal_im]
  · have hpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hzero)
    simp only [minusSaddleProfile, ite_eq_right hzero]
    exact mellinInv_real_of_hermitian ℓ
      (minusSaddleMellinData ε ℓ)
      (minusSaddleMellinData_conj_vertical ε ℓ) hpos

private theorem plusSaddleFunction_real (ε : ℝ) (d : ℕ)
    (x : Euclidean d) :
    (plusSaddleFunction ε d x).im = 0 := by
  exact plusSaddleProfile_real ε ((d : ℝ) / 2) (norm_nonneg x)

private theorem minusSaddleFunction_real (ε : ℝ) (d : ℕ)
    (x : Euclidean d) :
    (minusSaddleFunction ε d x).im = 0 := by
  exact minusSaddleProfile_real ε ((d : ℝ) / 2) (norm_nonneg x)

private theorem mellinMultiplier_mul_saddleEnvelope_neg
    {ε ℓ : ℝ} (hℓ : 0 < ℓ) (t : ℝ) :
    mellinMultiplier ℓ t * saddleEnvelope ε ℓ (-t) =
      saddleEnvelope ε ℓ t := by
  have hgamma := mellinMultiplier_denominator_ne_zero hℓ t
  have harg : ((-t : ℝ) : ℂ) / (ℓ : ℂ) =
      -((t : ℂ) / (ℓ : ℂ)) := by
    push_cast
    ring
  have hgammaarg :
      (((ℓ : ℂ) - Complex.I * ((-t : ℝ) : ℂ)) / 2) =
        (((ℓ : ℂ) + Complex.I * (t : ℂ)) / 2) := by
    push_cast
    ring
  have hphase :
      Complex.exp
          (Complex.I * (t : ℂ) * (Real.log Real.pi : ℂ)) *
        Complex.exp
          (Complex.I * ((-t : ℝ) : ℂ) *
            (Real.log Real.pi : ℂ) / 2) =
        Complex.exp
          (Complex.I * (t : ℂ) * (Real.log Real.pi : ℂ) / 2) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold mellinMultiplier saddleEnvelope
  rw [harg, mellinShellPhase_neg, hgammaarg]
  calc
    _ = (Complex.exp
          (Complex.I * (t : ℂ) * (Real.log Real.pi : ℂ)) *
        Complex.exp
          (Complex.I * ((-t : ℝ) : ℂ) *
            (Real.log Real.pi : ℂ) / 2)) *
        Complex.Gamma (((ℓ : ℂ) - Complex.I * (t : ℂ)) / 2) *
        Complex.exp ((ℓ : ℂ) *
          mellinShellPhase ε ((t : ℂ) / (ℓ : ℂ))) := by
      field_simp [hgamma]
    _ = _ := by rw [hphase]

private theorem mellinMultiplier_mul_minusSaddleSpectrum_neg
    {ε ℓ : ℝ} (hℓ : 0 < ℓ) (t : ℝ) :
    mellinMultiplier ℓ t * minusSaddleSpectrum ε ℓ (-t) =
      plusSaddleSpectrum ε ℓ t := by
  have harg : ((-t : ℝ) : ℂ) / (ℓ : ℂ) =
      -((t : ℂ) / (ℓ : ℂ)) := by
    push_cast
    ring
  unfold minusSaddleSpectrum plusSaddleSpectrum
  rw [harg, minusPolynomial_neg]
  rw [← mul_assoc, mellinMultiplier_mul_saddleEnvelope_neg hℓ t]

end
end CohnElkies
