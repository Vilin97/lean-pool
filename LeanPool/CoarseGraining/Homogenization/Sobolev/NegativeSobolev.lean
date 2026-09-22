/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.BoundedConvexDomain
import LeanPool.CoarseGraining.Homogenization.Sobolev.SmoothCompactSupport
import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.Normalized
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Normalized negative Sobolev seminorms

The two Chapter 1 dual seminorms use the normalized pairing prescribed by
RULING-0001.  The first test carrier is literally Mathlib's smooth compactly
supported test-function space; the second uses genuine weak `W^{1,p}`
witnesses with zero normalized average.
-/

namespace Homogenization

open scoped ENNReal

namespace NegativeSobolev

variable {d : ℕ} [NeZero d] {U : Set (Vec d)}
  (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)

/-- The positive-finite normalized domain induced by the public convex carrier. -/
noncomputable abbrev domain : BoundedMeasurableDomain d :=
  hU.toBoundedMeasurableDomain hne

/-- The literal `C_c^∞(U)` carrier for the zero-boundary dual seminorm. -/
abbrev SmoothTestFunction : Type _ := SmoothCompactSupportFunction hU.toOpens

/-- The exact normalized gradient seminorm imposed on smooth tests. -/
noncomputable def smoothTestSeminorm (p : ENNReal) (hp_one : 1 < p) (hp_top : p ≠ ∞)
    (φ : SmoothTestFunction hU) : ℝ :=
  BoundedMeasurableDomain.NormalizedW1pKernel.seminorm
    (domain hU hne) p (le_of_lt hp_one) hp_top
    (φ.toW1pFunction hU.toOpens p)

/-- The smooth tests in the unit normalized gradient-seminorm ball. -/
def SmoothTestAdmissible (p : ENNReal) (hp_one : 1 < p) (hp_top : p ≠ ∞)
    (φ : SmoothTestFunction hU) : Prop :=
  smoothTestSeminorm hU hne p hp_one hp_top φ ≤ 1

/-- A genuine weak `W^{1,p}(U)` witness with zero normalized average. -/
structure MeanZeroW1pTestFunction (p : ENNReal) where
  /-- The weak-Sobolev function used as a mean-zero test. -/
  toW1pFunction : W1pFunction U p
  normalizedIntegral_eq_zero :
    ∫ x, toW1pFunction.toFun x ∂(domain hU hne).normalizedVolume = 0

/-- The exact normalized gradient seminorm imposed on mean-zero tests. -/
noncomputable def meanZeroTestSeminorm (p : ENNReal) (hp_one : 1 < p) (hp_top : p ≠ ∞)
    (φ : MeanZeroW1pTestFunction hU hne p) : ℝ :=
  BoundedMeasurableDomain.NormalizedW1pKernel.seminorm
    (domain hU hne) p (le_of_lt hp_one) hp_top φ.toW1pFunction

/-- The mean-zero weak tests in the unit normalized gradient-seminorm ball. -/
def MeanZeroTestAdmissible (p : ENNReal) (hp_one : 1 < p) (hp_top : p ≠ ∞)
    (φ : MeanZeroW1pTestFunction hU hne p) : Prop :=
  meanZeroTestSeminorm hU hne p hp_one hp_top φ ≤ 1

omit [NeZero d] in
private theorem smoothTest_memLp_normalized (p : ENNReal) (φ : SmoothTestFunction hU) :
    MeasureTheory.MemLp (φ : Vec d → ℝ) p (domain hU hne).normalizedVolume := by
  refine ((domain hU hne).memLp_normalizedVolume_iff p _).mpr ?_
  change MeasureTheory.MemLp (φ : Vec d → ℝ) p (MeasureTheory.volume.restrict U)
  simpa only [SmoothCompactSupportFunction.toW1pFunction_toFun] using!
    (φ.toW1pFunction hU.toOpens p).memLp

omit [NeZero d] in
private theorem meanZeroTest_memLp_normalized (p : ENNReal)
    (φ : MeanZeroW1pTestFunction hU hne p) :
    MeasureTheory.MemLp φ.toW1pFunction.toFun p (domain hU hne).normalizedVolume := by
  refine ((domain hU hne).memLp_normalizedVolume_iff p _).mpr ?_
  change MeasureTheory.MemLp φ.toW1pFunction.toFun p (MeasureTheory.volume.restrict U)
  exact φ.toW1pFunction.memLp

omit [NeZero d] in
private theorem pairing_integrable (p : ENNReal) (hp_one : 1 < p)
    (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.conjExponent p) (domain hU hne).normalizedVolume)
    (g : Vec d → ℝ) (hg : MeasureTheory.MemLp g p (domain hU hne).normalizedVolume) :
    MeasureTheory.Integrable (fun x => f x * g x) (domain hU hne).normalizedVolume := by
  let : Fact (1 ≤ p) := ⟨le_of_lt hp_one⟩
  exact hf.integrable_mul hg

/-- The normalized pairing `fint_U f g`.  Product integrability is derived
from the two `MemLp` witnesses by Hölder, never supplied by the caller. -/
noncomputable def normalizedPairing (p : ENNReal) (hp_one : 1 < p)
    (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.conjExponent p) (domain hU hne).normalizedVolume)
    (g : Vec d → ℝ) (hg : MeasureTheory.MemLp g p (domain hU hne).normalizedVolume) : ℝ :=
  (domain hU hne).pairing f g
    (((domain hU hne).integrable_normalizedVolume_iff _).mp
      (pairing_integrable hU hne p hp_one f hf g hg))

/-- The normalized pairing against a literal smooth compactly supported test. -/
noncomputable def smoothPairing (p : ENNReal) (hp_one : 1 < p)
    (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.conjExponent p) (domain hU hne).normalizedVolume)
    (φ : SmoothTestFunction hU) : ℝ :=
  normalizedPairing hU hne p hp_one f hf φ (smoothTest_memLp_normalized hU hne p φ)

/-- The normalized pairing against a genuine mean-zero weak test. -/
noncomputable def meanZeroPairing (p : ENNReal) (hp_one : 1 < p)
    (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.conjExponent p) (domain hU hne).normalizedVolume)
    (φ : MeanZeroW1pTestFunction hU hne p) : ℝ :=
  normalizedPairing hU hne p hp_one f hf φ.toW1pFunction.toFun
    (meanZeroTest_memLp_normalized hU hne p φ)

/-- The signed Chapter 1 zero-boundary negative Sobolev seminorm. -/
noncomputable def smoothNegativeSobolevSeminorm (p : ENNReal) (hp_one : 1 < p)
    (hp_top : p ≠ ∞) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.conjExponent p) (domain hU hne).normalizedVolume) : ℝ≥0∞ :=
  ⨆ φ : {φ : SmoothTestFunction hU // SmoothTestAdmissible hU hne p hp_one hp_top φ},
    ENNReal.ofReal (smoothPairing hU hne p hp_one f hf φ.1)

/-- The signed Chapter 1 mean-zero negative Sobolev seminorm. -/
noncomputable def meanZeroNegativeSobolevSeminorm (p : ENNReal) (hp_one : 1 < p)
    (hp_top : p ≠ ∞) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.conjExponent p) (domain hU hne).normalizedVolume) : ℝ≥0∞ :=
  ⨆ φ : {φ : MeanZeroW1pTestFunction hU hne p //
      MeanZeroTestAdmissible hU hne p hp_one hp_top φ},
    ENNReal.ofReal (meanZeroPairing hU hne p hp_one f hf φ.1)

/-- The absolute-pairing form of the zero-boundary seminorm. -/
noncomputable def smoothNegativeSobolevAbsSeminorm (p : ENNReal) (hp_one : 1 < p)
    (hp_top : p ≠ ∞) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.conjExponent p) (domain hU hne).normalizedVolume) : ℝ≥0∞ :=
  ⨆ φ : {φ : SmoothTestFunction hU // SmoothTestAdmissible hU hne p hp_one hp_top φ},
    ENNReal.ofReal |smoothPairing hU hne p hp_one f hf φ.1|

/-- The absolute-pairing form of the mean-zero seminorm. -/
noncomputable def meanZeroNegativeSobolevAbsSeminorm (p : ENNReal) (hp_one : 1 < p)
    (hp_top : p ≠ ∞) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.conjExponent p) (domain hU hne).normalizedVolume) : ℝ≥0∞ :=
  ⨆ φ : {φ : MeanZeroW1pTestFunction hU hne p //
      MeanZeroTestAdmissible hU hne p hp_one hp_top φ},
    ENNReal.ofReal |meanZeroPairing hU hne p hp_one f hf φ.1|

/-! ## Transparent characterizations -/

theorem smoothNegativeSobolevSeminorm_eq_iSup (p : ENNReal) (hp_one : 1 < p)
    (hp_top : p ≠ ∞) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.conjExponent p) (domain hU hne).normalizedVolume) :
    smoothNegativeSobolevSeminorm hU hne p hp_one hp_top f hf =
      ⨆ φ : {φ : SmoothTestFunction hU // SmoothTestAdmissible hU hne p hp_one hp_top φ},
        ENNReal.ofReal (smoothPairing hU hne p hp_one f hf φ.1) :=
  rfl

theorem meanZeroNegativeSobolevSeminorm_eq_iSup (p : ENNReal) (hp_one : 1 < p)
    (hp_top : p ≠ ∞) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.conjExponent p) (domain hU hne).normalizedVolume) :
    meanZeroNegativeSobolevSeminorm hU hne p hp_one hp_top f hf =
      ⨆ φ : {φ : MeanZeroW1pTestFunction hU hne p //
          MeanZeroTestAdmissible hU hne p hp_one hp_top φ},
        ENNReal.ofReal (meanZeroPairing hU hne p hp_one f hf φ.1) :=
  rfl

theorem smoothNegativeSobolevAbsSeminorm_eq_iSup (p : ENNReal) (hp_one : 1 < p)
    (hp_top : p ≠ ∞) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.conjExponent p) (domain hU hne).normalizedVolume) :
    smoothNegativeSobolevAbsSeminorm hU hne p hp_one hp_top f hf =
      ⨆ φ : {φ : SmoothTestFunction hU // SmoothTestAdmissible hU hne p hp_one hp_top φ},
        ENNReal.ofReal |smoothPairing hU hne p hp_one f hf φ.1| :=
  rfl

theorem meanZeroNegativeSobolevAbsSeminorm_eq_iSup (p : ENNReal) (hp_one : 1 < p)
    (hp_top : p ≠ ∞) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.conjExponent p) (domain hU hne).normalizedVolume) :
    meanZeroNegativeSobolevAbsSeminorm hU hne p hp_one hp_top f hf =
      ⨆ φ : {φ : MeanZeroW1pTestFunction hU hne p //
          MeanZeroTestAdmissible hU hne p hp_one hp_top φ},
        ENNReal.ofReal |meanZeroPairing hU hne p hp_one f hf φ.1| :=
  rfl

/-! ## Test-class symmetry -/

private noncomputable def negW1pFunction {p : ENNReal} (u : W1pFunction U p) :
    W1pFunction U p :=
  { toFun := -u.toFun
    grad := -u.grad
    memLp := by simpa using u.memLp.neg
    gradMemLp := by
      intro i
      simpa only [Pi.neg_apply] using! (u.gradMemLp i).neg
    hasWeakGradient := by
      intro i φ hφ_smooth hφ_compact hφ_sub
      calc
        ∫ x in U, -u.toFun x * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume
            = -∫ x in U, u.toFun x * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume := by
                rw [← MeasureTheory.integral_neg]
                apply MeasureTheory.integral_congr_ae
                exact Filter.Eventually.of_forall fun x => by ring
        _ = ∫ x in U, u.grad x i * φ x ∂MeasureTheory.volume := by
              rw [u.hasWeakGradient i φ hφ_smooth hφ_compact hφ_sub]
              simp
        _ = -∫ x in U, (-u.grad x i) * φ x ∂MeasureTheory.volume := by
              rw [← MeasureTheory.integral_neg]
              apply MeasureTheory.integral_congr_ae
              exact Filter.Eventually.of_forall fun x => by ring }

private noncomputable def zeroW1pFunction (p : ENNReal) : W1pFunction U p :=
  { toFun := 0
    grad := 0
    memLp := by simp
    gradMemLp := by intro i; simp
    hasWeakGradient := by intro i φ hφ_smooth hφ_compact hφ_sub; simp }

private theorem normalizedW1pSeminorm_negW1pFunction {p : ENNReal}
    (hp_one : 1 < p) (hp_top : p ≠ ∞) (u : W1pFunction U p) :
    BoundedMeasurableDomain.NormalizedW1pKernel.seminorm
      (domain hU hne) p (le_of_lt hp_one) hp_top
      (negW1pFunction u) =
      BoundedMeasurableDomain.NormalizedW1pKernel.seminorm
        (domain hU hne) p (le_of_lt hp_one) hp_top u := by
  unfold BoundedMeasurableDomain.NormalizedW1pKernel.seminorm
  unfold BoundedMeasurableDomain.normalizedEuclideanLpNorm
  have hgrad :
      (fun x => euclideanNorm ((negW1pFunction u).grad x)) =
        fun x => euclideanNorm (u.grad x) := by
    funext x
    simp [negW1pFunction, euclideanNorm_neg]
  exact (domain hU hne).normalizedLpNorm_congr_ae p
    ((negW1pFunction u).gradEuclideanMemLp (domain hU hne) p)
    (u.gradEuclideanMemLp (domain hU hne) p)
    (Filter.Eventually.of_forall (congrFun hgrad))

private theorem smoothTestSeminorm_neg (p : ENNReal) (hp_one : 1 < p) (hp_top : p ≠ ∞)
    (φ : SmoothTestFunction hU) :
    smoothTestSeminorm hU hne p hp_one hp_top (-φ) =
      smoothTestSeminorm hU hne p hp_one hp_top φ := by
  unfold smoothTestSeminorm BoundedMeasurableDomain.NormalizedW1pKernel.seminorm
  unfold BoundedMeasurableDomain.normalizedEuclideanLpNorm
  have hgrad :
      (fun x => euclideanNorm (((-φ).toW1pFunction hU.toOpens p).grad x)) =
        fun x => euclideanNorm ((φ.toW1pFunction hU.toOpens p).grad x) := by
    funext x
    rw [SmoothCompactSupportFunction.toW1pFunction_grad,
      SmoothCompactSupportFunction.gradient_neg,
      SmoothCompactSupportFunction.toW1pFunction_grad]
    exact euclideanNorm_neg _
  simp only [hgrad]

/-- Zero belongs to the literal smooth test carrier. -/
noncomputable def smoothTestZero : SmoothTestFunction hU := 0

theorem smoothTestAdmissible_zero (p : ENNReal) (hp_one : 1 < p) (hp_top : p ≠ ∞) :
    SmoothTestAdmissible hU hne p hp_one hp_top (smoothTestZero hU) := by
  change smoothTestSeminorm hU hne p hp_one hp_top (0 : SmoothTestFunction hU) ≤ 1
  unfold smoothTestSeminorm BoundedMeasurableDomain.NormalizedW1pKernel.seminorm
  unfold BoundedMeasurableDomain.normalizedEuclideanLpNorm
  have hgrad : (0 : SmoothTestFunction hU).gradient = 0 := by
    ext x i
    change (fderiv ℝ (0 : Vec d → ℝ) x) (basisVec i) = 0
    simp
  simp [hgrad, BoundedMeasurableDomain.normalizedLpNorm,
    BoundedMeasurableDomain.normalizedLpFiniteENorm,
    BoundedMeasurableDomain.normalizedLpENorm,
    ne_of_gt (lt_trans zero_lt_one hp_one), hp_top]
  change (MeasureTheory.eLpNorm' (0 : Vec d → ℝ) p.toReal
    (domain hU hne).normalizedVolume).toReal ≤ 1
  rw [MeasureTheory.eLpNorm'_zero (ENNReal.toReal_pos
    (ne_of_gt (lt_trans zero_lt_one hp_one)) hp_top)]
  norm_num

theorem smoothTestAdmissible_neg (p : ENNReal) (hp_one : 1 < p) (hp_top : p ≠ ∞)
    {φ : SmoothTestFunction hU} (hφ : SmoothTestAdmissible hU hne p hp_one hp_top φ) :
    SmoothTestAdmissible hU hne p hp_one hp_top (-φ) := by
  change smoothTestSeminorm hU hne p hp_one hp_top (-φ) ≤ 1
  rw [smoothTestSeminorm_neg hU hne p hp_one hp_top]
  exact hφ

/-- Negation preserves genuine mean-zero weak tests. -/
noncomputable def MeanZeroW1pTestFunction.neg {p : ENNReal}
    (φ : MeanZeroW1pTestFunction hU hne p) : MeanZeroW1pTestFunction hU hne p where
  toW1pFunction := negW1pFunction φ.toW1pFunction
  normalizedIntegral_eq_zero := by
    change ∫ x, -φ.toW1pFunction.toFun x ∂(domain hU hne).normalizedVolume = 0
    rw [MeasureTheory.integral_neg, φ.normalizedIntegral_eq_zero, neg_zero]

theorem meanZeroTestSeminorm_neg (p : ENNReal) (hp_one : 1 < p) (hp_top : p ≠ ∞)
    (φ : MeanZeroW1pTestFunction hU hne p) :
    meanZeroTestSeminorm hU hne p hp_one hp_top φ.neg =
      meanZeroTestSeminorm hU hne p hp_one hp_top φ :=
  normalizedW1pSeminorm_negW1pFunction hU hne hp_one hp_top φ.toW1pFunction

/-- Zero belongs to the mean-zero weak test carrier. -/
noncomputable def MeanZeroW1pTestFunction.zero (p : ENNReal) :
    MeanZeroW1pTestFunction hU hne p where
  toW1pFunction := zeroW1pFunction p
  normalizedIntegral_eq_zero := by simp [zeroW1pFunction]

theorem meanZeroTestAdmissible_zero (p : ENNReal) (hp_one : 1 < p) (hp_top : p ≠ ∞) :
    MeanZeroTestAdmissible hU hne p hp_one hp_top
      (MeanZeroW1pTestFunction.zero hU hne p) := by
  change meanZeroTestSeminorm hU hne p hp_one hp_top
      (MeanZeroW1pTestFunction.zero hU hne p) ≤ 1
  simp [meanZeroTestSeminorm, MeanZeroW1pTestFunction.zero, zeroW1pFunction,
    BoundedMeasurableDomain.NormalizedW1pKernel.seminorm,
    BoundedMeasurableDomain.normalizedEuclideanLpNorm,
    BoundedMeasurableDomain.normalizedLpNorm,
    BoundedMeasurableDomain.normalizedLpFiniteENorm,
    BoundedMeasurableDomain.normalizedLpENorm,
    ne_of_gt (lt_trans zero_lt_one hp_one), hp_top]
  change (MeasureTheory.eLpNorm' (0 : Vec d → ℝ) p.toReal
    (domain hU hne).normalizedVolume).toReal ≤ 1
  rw [MeasureTheory.eLpNorm'_zero (ENNReal.toReal_pos
    (ne_of_gt (lt_trans zero_lt_one hp_one)) hp_top)]
  norm_num

theorem meanZeroTestAdmissible_neg (p : ENNReal) (hp_one : 1 < p) (hp_top : p ≠ ∞)
    {φ : MeanZeroW1pTestFunction hU hne p}
    (hφ : MeanZeroTestAdmissible hU hne p hp_one hp_top φ) :
    MeanZeroTestAdmissible hU hne p hp_one hp_top φ.neg := by
  change meanZeroTestSeminorm hU hne p hp_one hp_top φ.neg ≤ 1
  rw [meanZeroTestSeminorm_neg hU hne p hp_one hp_top]
  exact hφ

/-! ## Pairing symmetry and absolute-value characterizations -/

omit [NeZero d] in
theorem normalizedPairing_neg_right (p : ENNReal) (hp_one : 1 < p)
    (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.conjExponent p) (domain hU hne).normalizedVolume)
    (g : Vec d → ℝ) (hg : MeasureTheory.MemLp g p (domain hU hne).normalizedVolume) :
    normalizedPairing hU hne p hp_one f hf (-g) hg.neg =
      -normalizedPairing hU hne p hp_one f hf g hg := by
  unfold normalizedPairing BoundedMeasurableDomain.pairing BoundedMeasurableDomain.average
  rw [← MeasureTheory.integral_neg]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by simp only [Pi.neg_apply]; ring

omit [NeZero d] in
theorem smoothPairing_neg (p : ENNReal) (hp_one : 1 < p)
    (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.conjExponent p) (domain hU hne).normalizedVolume)
    (φ : SmoothTestFunction hU) :
    smoothPairing hU hne p hp_one f hf (-φ) =
      -smoothPairing hU hne p hp_one f hf φ := by
  unfold smoothPairing
  change normalizedPairing hU hne p hp_one f hf (-(φ : Vec d → ℝ)) _ =
    -normalizedPairing hU hne p hp_one f hf (φ : Vec d → ℝ) _
  exact normalizedPairing_neg_right hU hne p hp_one f hf (φ : Vec d → ℝ) _

omit [NeZero d] in
theorem meanZeroPairing_neg (p : ENNReal) (hp_one : 1 < p)
    (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.conjExponent p) (domain hU hne).normalizedVolume)
    (φ : MeanZeroW1pTestFunction hU hne p) :
    meanZeroPairing hU hne p hp_one f hf φ.neg =
      -meanZeroPairing hU hne p hp_one f hf φ := by
  unfold meanZeroPairing
  change normalizedPairing hU hne p hp_one f hf (-φ.toW1pFunction.toFun) _ =
    -normalizedPairing hU hne p hp_one f hf φ.toW1pFunction.toFun _
  exact normalizedPairing_neg_right hU hne p hp_one f hf φ.toW1pFunction.toFun _

private noncomputable def smoothAdmissibleNeg (p : ENNReal) (hp_one : 1 < p)
    (hp_top : p ≠ ∞)
    (φ : {φ : SmoothTestFunction hU // SmoothTestAdmissible hU hne p hp_one hp_top φ}) :
    {φ : SmoothTestFunction hU // SmoothTestAdmissible hU hne p hp_one hp_top φ} :=
  ⟨-φ.1, smoothTestAdmissible_neg hU hne p hp_one hp_top φ.2⟩

private noncomputable def meanZeroAdmissibleNeg (p : ENNReal) (hp_one : 1 < p)
    (hp_top : p ≠ ∞)
    (φ : {φ : MeanZeroW1pTestFunction hU hne p //
      MeanZeroTestAdmissible hU hne p hp_one hp_top φ}) :
    {φ : MeanZeroW1pTestFunction hU hne p //
      MeanZeroTestAdmissible hU hne p hp_one hp_top φ} :=
  ⟨φ.1.neg, meanZeroTestAdmissible_neg hU hne p hp_one hp_top φ.2⟩

private theorem iSup_ofReal_eq_iSup_ofReal_abs {α : Type*} (q : α → ℝ)
    (neg : α → α) (hneg : ∀ a, q (neg a) = -q a) :
    (⨆ a, ENNReal.ofReal (q a)) = ⨆ a, ENNReal.ofReal |q a| := by
  apply le_antisymm
  · refine iSup_le fun a => ?_
    exact (ENNReal.ofReal_le_ofReal (le_abs_self (q a))).trans (le_iSup (fun a =>
      ENNReal.ofReal |q a|) a)
  · refine iSup_le fun a => ?_
    by_cases ha : 0 ≤ q a
    · rw [abs_of_nonneg ha]
      exact le_iSup (fun a => ENNReal.ofReal (q a)) a
    · rw [abs_of_neg (lt_of_not_ge ha), ← hneg a]
      exact le_iSup (fun a => ENNReal.ofReal (q a)) (neg a)

theorem smoothNegativeSobolevSeminorm_eq_abs (p : ENNReal) (hp_one : 1 < p)
    (hp_top : p ≠ ∞) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.conjExponent p) (domain hU hne).normalizedVolume) :
    smoothNegativeSobolevSeminorm hU hne p hp_one hp_top f hf =
      smoothNegativeSobolevAbsSeminorm hU hne p hp_one hp_top f hf := by
  exact iSup_ofReal_eq_iSup_ofReal_abs
    (fun φ : {φ : SmoothTestFunction hU // SmoothTestAdmissible hU hne p hp_one hp_top φ} =>
      smoothPairing hU hne p hp_one f hf φ.1)
    (smoothAdmissibleNeg hU hne p hp_one hp_top)
    (fun φ => by
      change smoothPairing hU hne p hp_one f hf (-φ.1) =
        -smoothPairing hU hne p hp_one f hf φ.1
      exact smoothPairing_neg hU hne p hp_one f hf φ.1)

theorem meanZeroNegativeSobolevSeminorm_eq_abs (p : ENNReal) (hp_one : 1 < p)
    (hp_top : p ≠ ∞) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.conjExponent p) (domain hU hne).normalizedVolume) :
    meanZeroNegativeSobolevSeminorm hU hne p hp_one hp_top f hf =
      meanZeroNegativeSobolevAbsSeminorm hU hne p hp_one hp_top f hf := by
  exact iSup_ofReal_eq_iSup_ofReal_abs
    (fun φ : {φ : MeanZeroW1pTestFunction hU hne p //
      MeanZeroTestAdmissible hU hne p hp_one hp_top φ} =>
      meanZeroPairing hU hne p hp_one f hf φ.1)
    (meanZeroAdmissibleNeg hU hne p hp_one hp_top)
    (fun φ => by
      change meanZeroPairing hU hne p hp_one f hf φ.1.neg =
        -meanZeroPairing hU hne p hp_one f hf φ.1
      exact meanZeroPairing_neg hU hne p hp_one f hf φ.1)

/-! ## Almost-everywhere invariance -/

omit [NeZero d] in
theorem normalizedPairing_congr_ae (p : ENNReal) (hp_one : 1 < p)
    (f f' : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.conjExponent p) (domain hU hne).normalizedVolume)
    (hf' : MeasureTheory.MemLp f' (ENNReal.conjExponent p) (domain hU hne).normalizedVolume)
    (hff' : f =ᵐ[(domain hU hne).normalizedVolume] f')
    (g : Vec d → ℝ) (hg : MeasureTheory.MemLp g p (domain hU hne).normalizedVolume) :
    normalizedPairing hU hne p hp_one f hf g hg =
      normalizedPairing hU hne p hp_one f' hf' g hg := by
  unfold normalizedPairing BoundedMeasurableDomain.pairing BoundedMeasurableDomain.average
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hff'] with x hx
  rw [hx]

omit [NeZero d] in
theorem smoothPairing_congr_ae (p : ENNReal) (hp_one : 1 < p)
    (f f' : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.conjExponent p) (domain hU hne).normalizedVolume)
    (hf' : MeasureTheory.MemLp f' (ENNReal.conjExponent p) (domain hU hne).normalizedVolume)
    (hff' : f =ᵐ[(domain hU hne).normalizedVolume] f')
    (φ : SmoothTestFunction hU) :
    smoothPairing hU hne p hp_one f hf φ = smoothPairing hU hne p hp_one f' hf' φ := by
  unfold smoothPairing
  exact normalizedPairing_congr_ae hU hne p hp_one f f' hf hf' hff' φ _

omit [NeZero d] in
theorem meanZeroPairing_congr_ae (p : ENNReal) (hp_one : 1 < p)
    (f f' : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.conjExponent p) (domain hU hne).normalizedVolume)
    (hf' : MeasureTheory.MemLp f' (ENNReal.conjExponent p) (domain hU hne).normalizedVolume)
    (hff' : f =ᵐ[(domain hU hne).normalizedVolume] f')
    (φ : MeanZeroW1pTestFunction hU hne p) :
    meanZeroPairing hU hne p hp_one f hf φ = meanZeroPairing hU hne p hp_one f' hf' φ := by
  unfold meanZeroPairing
  exact normalizedPairing_congr_ae hU hne p hp_one f f' hf hf' hff' φ.toW1pFunction.toFun _

theorem smoothNegativeSobolevSeminorm_congr_ae (p : ENNReal) (hp_one : 1 < p)
    (hp_top : p ≠ ∞) (f f' : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.conjExponent p) (domain hU hne).normalizedVolume)
    (hf' : MeasureTheory.MemLp f' (ENNReal.conjExponent p) (domain hU hne).normalizedVolume)
    (hff' : f =ᵐ[(domain hU hne).normalizedVolume] f') :
    smoothNegativeSobolevSeminorm hU hne p hp_one hp_top f hf =
      smoothNegativeSobolevSeminorm hU hne p hp_one hp_top f' hf' := by
  unfold smoothNegativeSobolevSeminorm
  apply iSup_congr
  intro φ
  rw [smoothPairing_congr_ae hU hne p hp_one f f' hf hf' hff' φ.1]

theorem meanZeroNegativeSobolevSeminorm_congr_ae (p : ENNReal) (hp_one : 1 < p)
    (hp_top : p ≠ ∞) (f f' : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.conjExponent p) (domain hU hne).normalizedVolume)
    (hf' : MeasureTheory.MemLp f' (ENNReal.conjExponent p) (domain hU hne).normalizedVolume)
    (hff' : f =ᵐ[(domain hU hne).normalizedVolume] f') :
    meanZeroNegativeSobolevSeminorm hU hne p hp_one hp_top f hf =
      meanZeroNegativeSobolevSeminorm hU hne p hp_one hp_top f' hf' := by
  unfold meanZeroNegativeSobolevSeminorm
  apply iSup_congr
  intro φ
  rw [meanZeroPairing_congr_ae hU hne p hp_one f f' hf hf' hff' φ.1]

/-! ## The distinct `p = 2` aliases -/

/-- The normalized zero-boundary `H^{-1}` seminorm. -/
noncomputable abbrev smoothNegativeHMinusOneSeminorm (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.conjExponent (2 : ENNReal))
      (domain hU hne).normalizedVolume) : ℝ≥0∞ :=
  smoothNegativeSobolevSeminorm hU hne 2 (by norm_num) (by norm_num) f hf

/-- The normalized mean-zero `H^{-1}` seminorm. -/
noncomputable abbrev meanZeroNegativeHMinusOneSeminorm (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.conjExponent (2 : ENNReal))
      (domain hU hne).normalizedVolume) : ℝ≥0∞ :=
  meanZeroNegativeSobolevSeminorm hU hne 2 (by norm_num) (by norm_num) f hf

end NegativeSobolev

end Homogenization
