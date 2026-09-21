/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.ABK26.LocalCoarseGrainingAggregation
import LeanPool.CoarseGraining.Homogenization.Book.Ch03.ABK26.LocalCoarseGrainingDescendantWsp
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ExactOverlapEuclideanLpDisjointBridge

/-!
# Finite-`p` forcing aggregation for local coarse graining

This module isolates the source forcing term before it is combined with the
PDE or response estimates.  Its physical-scale index is written as `n - j`:
thus `j` is exactly the source depth below the prescribed scale `n`.
-/

namespace Homogenization
namespace Book
namespace Ch03
namespace ABK26

open scoped BigOperators ENNReal

noncomputable section

/-- The unrooted finite-`p` forcing aggregation.  At outer depth `j`, this
uses the normalized average of the legacy local positive `q = 2` seminorms
over cubes at physical scale `n - j`; the coefficient is the manuscript's
`3^((s₁-s) p j)`. -/
noncomputable def localCoarseGrainingForcingPowerEnergy {d : ℕ}
    (Q : TriadicCube d) (n : ℤ) (s1 s : FractionalOrder)
    (p : FiniteLpExponent) (g : Vec d → Vec d) : ℝ≥0∞ :=
  ∑' j : ℕ,
    ENNReal.ofReal
      (Real.rpow 3 (-(s.1 - s1.1) * p.exponent.toReal * (j : ℝ))) *
      descendantsAtScaleENNAverage Q (n - (j : ℤ)) (fun R =>
        (ENNReal.ofReal (cubeBesovPositiveVectorSeminormTwo R s.1 g)) ^
          p.exponent.toReal)

/-- The source normalized `ell^p` forcing aggregation, obtained by taking the
single outer finite-`p` root of `localCoarseGrainingForcingPowerEnergy`. -/
noncomputable def localCoarseGrainingForcingLp {d : ℕ}
    (Q : TriadicCube d) (n : ℤ) (s1 s : FractionalOrder)
    (p : FiniteLpExponent) (g : Vec d → Vec d) : ℝ≥0∞ :=
  (localCoarseGrainingForcingPowerEnergy Q n s1 s p g) ^
    (p.exponent.toReal)⁻¹

private theorem finiteLpExponent_toReal_pos (p : FiniteLpExponent) :
    0 < p.exponent.toReal :=
  ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne

private theorem overlapESeminorm_lt_top_of_memCubeEuclideanFullWsp
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (g : Vec d → Vec d)
    (hg : MemCubeEuclideanFullWsp Q s p g) :
    cubeEuclideanPositiveBesovOverlapESeminorm Q s p g < ∞ := by
  let F : CubeEuclideanLpField Q p :=
    { toField := g
      euclideanMemLp := hg.1 }
  have hcomparison := cubeEuclideanOverlap_le_dimensionConstant_mul_wsp Q s p F
  have hright : cubeEuclideanWspOverlapDimensionConstant d *
      cubeEuclideanWspESeminorm Q s p g < ∞ :=
    ENNReal.mul_lt_top (cubeEuclideanWspOverlapDimensionConstant_lt_top d)
      hg.2.eSeminorm_lt_top
  apply lt_of_le_of_lt ?_ hright
  simpa only [F] using hcomparison

/-- The exact-overlap source hypothesis also makes the internal disjoint
power energy finite.  This is the one permitted route from the localized
disjoint calculation back to the source-facing overlap carrier. -/
private theorem disjointPowerEnergy_lt_top_of_memCubeEuclideanFullWsp
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (g : Vec d → Vec d)
    (hg : MemCubeEuclideanFullWsp Q s p g) :
    cubeEuclideanPositiveBesovDisjointPowerEnergy Q s p g < ∞ := by
  have hov : cubeEuclideanPositiveBesovOverlapESeminorm Q s p g < ∞ :=
    overlapESeminorm_lt_top_of_memCubeEuclideanFullWsp Q s p g hg
  have hpow : cubeEuclideanPositiveBesovOverlapPowerEnergy Q s p g < ∞ := by
    rw [← cubeEuclideanPositiveBesovOverlapESeminorm_rpow_eq_powerEnergy]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hov.ne
  exact lt_of_le_of_lt
    (cubeEuclideanPositiveBesovDisjointPowerEnergy_le_overlap Q s p g)
    (lt_top_iff_ne_top.mpr
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num)) hpow.ne))

/-- Raising the rooted forcing carrier back to the finite exponent recovers
its literal unrooted physical-scale series. -/
theorem localCoarseGrainingForcingLp_rpow_eq_powerEnergy {d : ℕ}
    (Q : TriadicCube d) (n : ℤ) (s1 s : FractionalOrder)
    (p : FiniteLpExponent) (g : Vec d → Vec d) :
    (localCoarseGrainingForcingLp Q n s1 s p g) ^ p.exponent.toReal =
      localCoarseGrainingForcingPowerEnergy Q n s1 s p g := by
  unfold localCoarseGrainingForcingLp
  exact ENNReal.rpow_inv_rpow (finiteLpExponent_toReal_pos p).ne' _

private theorem localCoarseGrainingForcingLp_le_of_power_le {d : ℕ}
    (Q : TriadicCube d) (n : ℤ) (s1 s : FractionalOrder)
    (p : FiniteLpExponent) (g : Vec d → Vec d) (B : ℝ≥0∞)
    (hB : localCoarseGrainingForcingPowerEnergy Q n s1 s p g ≤
      B ^ p.exponent.toReal) :
    localCoarseGrainingForcingLp Q n s1 s p g ≤ B := by
  have hroot := ENNReal.rpow_le_rpow hB
    (inv_nonneg.mpr (finiteLpExponent_toReal_pos p).le)
  rw [← localCoarseGrainingForcingLp_rpow_eq_powerEnergy] at hroot
  rw [← ENNReal.rpow_mul,
    mul_inv_cancel₀ (finiteLpExponent_toReal_pos p).ne', ENNReal.rpow_one] at hroot
  calc
    localCoarseGrainingForcingLp Q n s1 s p g ≤
        (B ^ p.exponent.toReal) ^ (p.exponent.toReal)⁻¹ := hroot
    _ = B := by
      rw [← ENNReal.rpow_mul,
        mul_inv_cancel₀ (finiteLpExponent_toReal_pos p).ne', ENNReal.rpow_one]

/-! The next finite-sum estimate is the Hölder core of the local
`L²`-to-`Lᵖ` conversion.  It is deliberately stated before any cube geometry:
the cube-specific proof will instantiate `w` with the fractional-order gap
discount and `a` with local oscillation averages. -/

private theorem weighted_square_sum_rpow_le_of_two_lt
    {ι : Type*} (I : Finset ι) {p : ℝ} (hp : 2 < p)
    (a w : ι → ℝ) :
    (∑ i ∈ I, (w i * a i) ^ 2) ^ (p / 2) ≤
      ((∑ i ∈ I, (a i ^ 2) ^ (p / 2)) ^ (1 / (p / 2)) *
        (∑ i ∈ I, (w i ^ 2) ^ (p / (p - 2))) ^
          (1 / (p / (p - 2)))) ^ (p / 2) := by
  have hp_two_pos : 0 < p / 2 := by linarith
  have hp_pos : 0 < p := by linarith
  have hp_sub_pos : 0 < p - 2 := by linarith
  have hq_pos : 0 < p / (p - 2) := div_pos hp_pos hp_sub_pos
  have hholder : Real.HolderConjugate (p / 2) (p / (p - 2)) := by
    refine ⟨?_, hp_two_pos, hq_pos⟩
    field_simp [hp_two_pos.ne', hp_sub_pos.ne']
    linarith
  have hinner := Real.inner_le_Lp_mul_Lq_of_nonneg
    (s := I) (f := fun i => a i ^ 2) (g := fun i => w i ^ 2)
    hholder
    (fun i hi => sq_nonneg (a i))
    (fun i hi => sq_nonneg (w i))
  have hleft_nonneg : 0 ≤ ∑ i ∈ I, (w i * a i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hleft :
      (∑ i ∈ I, (w i * a i) ^ 2) =
        ∑ i ∈ I, (a i ^ 2) * (w i ^ 2) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  rw [← hleft] at hinner
  exact Real.rpow_le_rpow hleft_nonneg hinner hp_two_pos.le

private theorem weighted_square_sum_le_of_eq_two
    {ι : Type*} (I : Finset ι) (a w : ι → ℝ)
    (hw_nonneg : ∀ i ∈ I, 0 ≤ w i) (hw_one : ∀ i ∈ I, w i ≤ 1) :
    (∑ i ∈ I, (w i * a i) ^ 2) ^ ((2 : ℝ) / 2) ≤
      ∑ i ∈ I, a i ^ 2 := by
  rw [show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one]
  refine Finset.sum_le_sum fun i hi => ?_
  have hsq : (w i) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (w i), mul_self_le_mul_self (hw_nonneg i hi) (hw_one i hi)]
  calc
    (w i * a i) ^ 2 = (w i) ^ 2 * (a i) ^ 2 := by ring
    _ ≤ 1 * (a i) ^ 2 :=
      mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ = a i ^ 2 := by ring

/-- Finite partial square sums may be replaced termwise by their weighted
finite-`p` majorants before Hölder is applied.  This small wrapper keeps the
later cube proof from mixing its depth algebra with the generic finite-sum
argument. -/
private theorem finite_square_sum_rpow_le_weighted_of_sq_le
    {ι : Type*} (I : Finset ι) {r : ℝ} (hr : 2 < r)
    (D a w : ι → ℝ)
    (hterm : ∀ i ∈ I, D i ^ 2 ≤ (w i * a i) ^ 2) :
    (∑ i ∈ I, D i ^ 2) ^ (r / 2) ≤
      ((∑ i ∈ I, (a i ^ 2) ^ (r / 2)) ^ (1 / (r / 2)) *
        (∑ i ∈ I, (w i ^ 2) ^ (r / (r - 2))) ^
          (1 / (r / (r - 2)))) ^ (r / 2) := by
  have hsum : ∑ i ∈ I, D i ^ 2 ≤ ∑ i ∈ I, (w i * a i) ^ 2 := by
    exact Finset.sum_le_sum fun i hi => hterm i hi
  have hsum_nonneg : 0 ≤ ∑ i ∈ I, D i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  calc
    (∑ i ∈ I, D i ^ 2) ^ (r / 2) ≤
        (∑ i ∈ I, (w i * a i) ^ 2) ^ (r / 2) :=
      Real.rpow_le_rpow hsum_nonneg hsum (by linarith)
    _ ≤ ((∑ i ∈ I, (a i ^ 2) ^ (r / 2)) ^ (1 / (r / 2)) *
        (∑ i ∈ I, (w i ^ 2) ^ (r / (r - 2))) ^
          (1 / (r / (r - 2)))) ^ (r / 2) :=
      weighted_square_sum_rpow_le_of_two_lt I hr a w

/-- The finite Hölder weight is controlled by the elementary triadic
geometric tail.  This deliberately keeps the finite partial proof separate
from the eventual `tsum` passage. -/
private theorem finite_triadic_geometric_tail_le_inv_discount
    {delta : ℝ} (hdelta : 0 < delta) (N : ℕ) :
    ∑ j ∈ Finset.range (N + 1), Real.rpow 3 (-delta * (j : ℝ)) ≤
      (Book.Ch02.geometricDiscount delta 1)⁻¹ := by
  let x : ℝ := Real.rpow 3 (-delta)
  have hx_nonneg : 0 ≤ x := Real.rpow_nonneg (by norm_num) _
  have hx_lt_one : x < 1 := by
    dsimp [x]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith
  have hterm : ∀ j : ℕ, Real.rpow 3 (-delta * (j : ℝ)) = x ^ j := by
    intro j
    dsimp [x]
    calc
      Real.rpow 3 (-delta * (j : ℝ)) =
          Real.rpow 3 ((-delta) * (j : ℝ)) := rfl
      _ = Real.rpow (Real.rpow 3 (-delta)) (j : ℝ) := by
            exact Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _
      _ = (Real.rpow 3 (-delta)) ^ j := Real.rpow_natCast _ j
  rw [show (∑ j ∈ Finset.range (N + 1),
      Real.rpow 3 (-delta * (j : ℝ))) =
      ∑ j ∈ Finset.range (N + 1), x ^ j by
        apply Finset.sum_congr rfl
        intro j _
        exact hterm j]
  calc
    ∑ j ∈ Finset.range (N + 1), x ^ j ≤ ∑' j : ℕ, x ^ j :=
      (summable_geometric_of_lt_one hx_nonneg hx_lt_one).sum_le_tsum
        (Finset.range (N + 1)) (fun _ _ => pow_nonneg hx_nonneg _)
    _ = (1 - x)⁻¹ := tsum_geometric_of_lt_one hx_nonneg hx_lt_one
    _ = (Book.Ch02.geometricDiscount delta 1)⁻¹ := by
      congr 1
      dsimp [Book.Ch02.geometricDiscount, x]
      rw [show -delta * 1 = -delta by ring]

/-- The Hölder-conjugate finite weight is no larger than the same elementary
tail at exponent `2 delta`.  This is the uniform tail estimate behind the
strict `p > 2` branch. -/
private theorem finite_holder_weight_le_inv_discount
    {delta r : ℝ} (hdelta : 0 < delta) (hr : 2 < r) (N : ℕ) :
    ∑ j ∈ Finset.range (N + 1),
      ((Real.rpow 3 (-delta * (j : ℝ))) ^ 2) ^ (r / (r - 2)) ≤
      (Book.Ch02.geometricDiscount delta 1)⁻¹ := by
  have hr_sub : 0 < r - 2 := by linarith
  have hq : 1 ≤ r / (r - 2) := by
    apply (le_div_iff₀ hr_sub).2
    linarith
  have hterm : ∀ j : ℕ,
      ((Real.rpow 3 (-delta * (j : ℝ))) ^ 2) ^ (r / (r - 2)) ≤
        Real.rpow 3 (-delta * (j : ℝ)) := by
    intro j
    have hbase : 1 ≤ (3 : ℝ) := by norm_num
    have hpow_nonneg : 0 ≤ Real.rpow 3 (-delta * (j : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hsquare : (Real.rpow 3 (-delta * (j : ℝ))) ^ 2 =
        Real.rpow 3 (-2 * delta * (j : ℝ)) := by
      calc
        (Real.rpow 3 (-delta * (j : ℝ))) ^ 2 =
            Real.rpow (Real.rpow 3 (-delta * (j : ℝ))) (2 : ℝ) := by
              symm
              exact Real.rpow_natCast _ 2
        _ = Real.rpow 3 ((-delta * (j : ℝ)) * 2) :=
              (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _).symm
        _ = Real.rpow 3 (-2 * delta * (j : ℝ)) := by
              congr 1
              ring
    rw [hsquare]
    calc
      Real.rpow (Real.rpow 3 (-2 * delta * (j : ℝ))) (r / (r - 2)) =
          Real.rpow 3 ((-2 * delta * (j : ℝ)) * (r / (r - 2))) :=
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _).symm
      _ ≤ Real.rpow 3 (-delta * (j : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le hbase
        have hj : 0 ≤ (j : ℝ) := by positivity
        have hc : 0 ≤ delta * (j : ℝ) := by positivity
        have hq_nonneg : 0 ≤ r / (r - 2) := le_trans zero_le_one hq
        have htwoq : 1 ≤ 2 * (r / (r - 2)) := by nlinarith
        have hmul := mul_le_mul_of_nonneg_left htwoq hc
        have hneg := neg_le_neg hmul
        calc (-2 * delta * (j : ℝ)) * (r / (r - 2))
            = -(delta * (j : ℝ) * (2 * (r / (r - 2)))) := by ring
          _ ≤ -(delta * (j : ℝ) * 1) := hneg
          _ = -delta * (j : ℝ) := by ring
  calc
    ∑ j ∈ Finset.range (N + 1),
        ((Real.rpow 3 (-delta * (j : ℝ))) ^ 2) ^ (r / (r - 2)) ≤
      ∑ j ∈ Finset.range (N + 1), Real.rpow 3 (-delta * (j : ℝ)) :=
      Finset.sum_le_sum fun j _ => hterm j
    _ ≤ (Book.Ch02.geometricDiscount delta 1)⁻¹ :=
      finite_triadic_geometric_tail_le_inv_discount hdelta N

/-- After taking the outer finite-`p` root, the Hölder tail costs at most one
inverse fractional gap.  The constant is independent of the finite
exponent. -/
private theorem finite_holder_weight_rpow_le_five_mul_inv
    {delta r : ℝ} (hdelta : 0 < delta) (hdelta_le : delta ≤ 1)
    (hr : 2 < r) (N : ℕ) :
    Real.rpow
      (∑ j ∈ Finset.range (N + 1),
        ((Real.rpow 3 (-delta * (j : ℝ))) ^ 2) ^ (r / (r - 2)))
      ((r - 2) / (2 * r)) ≤ 5 * delta⁻¹ := by
  let D : ℝ := (Book.Ch02.geometricDiscount delta 1)⁻¹
  let T : ℝ := ∑ j ∈ Finset.range (N + 1),
    ((Real.rpow 3 (-delta * (j : ℝ))) ^ 2) ^ (r / (r - 2))
  have hT : T ≤ D := finite_holder_weight_le_inv_discount hdelta hr N
  have hr_pos : 0 < r := by linarith
  have hgamma_nonneg : 0 ≤ (r - 2) / (2 * r) :=
    div_nonneg (by linarith) (by positivity)
  have hgamma_le_one : (r - 2) / (2 * r) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * r)).2
    linarith
  have hD_one : 1 ≤ D := by
    have hzero := finite_triadic_geometric_tail_le_inv_discount hdelta 0
    dsimp [D]
    simpa using hzero
  have hroot : Real.rpow T ((r - 2) / (2 * r)) ≤
      Real.rpow D ((r - 2) / (2 * r)) :=
    Real.rpow_le_rpow
      (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (sq_nonneg _) _) hT hgamma_nonneg
  calc
    Real.rpow T ((r - 2) / (2 * r)) ≤
        Real.rpow D ((r - 2) / (2 * r)) := hroot
    _ ≤ D := by
      calc
        Real.rpow D ((r - 2) / (2 * r)) ≤ Real.rpow D 1 :=
          Real.rpow_le_rpow_of_exponent_le hD_one hgamma_le_one
        _ = D := Real.rpow_one D
    _ ≤ 5 * delta⁻¹ := by
      dsimp [D]
      exact Book.Ch02.inv_geometricDiscount_le_five_inv hdelta hdelta_le (by norm_num)

/-- The termwise root used to pass from a depthwise finite-`p` estimate to
the square-sum majorant required by finite Hölder. -/
private theorem sq_le_weighted_rpow_of_rpow_le
    {x w E r : ℝ} (hx : 0 ≤ x) (hw : 0 ≤ w) (hE : 0 ≤ E)
    (hr : 0 < r) (hpow : Real.rpow x r ≤ Real.rpow w r * E) :
    x ^ 2 ≤ (w * Real.rpow E (1 / r)) ^ 2 := by
  have hroot := Real.rpow_le_rpow (Real.rpow_nonneg hx r) hpow
    (by positivity : 0 ≤ 2 / r)
  have hleft : (x ^ r) ^ (2 / r) = x ^ 2 := by
    calc
      Real.rpow (Real.rpow x r) (2 / r) = Real.rpow x (r * (2 / r)) :=
        (Real.rpow_mul hx _ _).symm
      _ = Real.rpow x 2 := by
        congr 1
        field_simp [hr.ne']
      _ = x ^ 2 := Real.rpow_natCast x 2
  have hwroot : Real.rpow (Real.rpow w r) (2 / r) = w ^ 2 := by
    calc
      Real.rpow (Real.rpow w r) (2 / r) = Real.rpow w (r * (2 / r)) :=
        (Real.rpow_mul hw _ _).symm
      _ = Real.rpow w 2 := by
        congr 1
        field_simp [hr.ne']
      _ = w ^ 2 := Real.rpow_natCast w 2
  have hEroot : Real.rpow E (2 / r) = (Real.rpow E (1 / r)) ^ 2 := by
    calc
      Real.rpow E (2 / r) = Real.rpow E ((1 / r) * 2) := by
        congr 1
        ring
      _ = Real.rpow (Real.rpow E (1 / r)) 2 := Real.rpow_mul hE _ _
      _ = (Real.rpow E (1 / r)) ^ 2 := Real.rpow_natCast _ 2
  rw [hleft] at hroot
  calc
    x ^ 2 ≤ Real.rpow (Real.rpow w r * E) (2 / r) := hroot
    _ = Real.rpow (Real.rpow w r) (2 / r) * Real.rpow E (2 / r) := by
      exact Real.mul_rpow (Real.rpow_nonneg hw _) hE
    _ = (w * Real.rpow E (1 / r)) ^ 2 := by
      rw [hwroot, hEroot]
      ring

private theorem cubeLpNorm_two_le_eLpNorm_finite_of_memLp
    {d : ℕ} (Q : TriadicCube d) (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) ≤ p.exponent) (f : Vec d → Vec d)
    (hf : MeasureTheory.MemLp (fun x => HilbertVec.ofVec (f x)) p.exponent
      (normalizedCubeMeasure Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) f ≤
      (MeasureTheory.eLpNorm (fun x => HilbertVec.ofVec (f x)) p.exponent
        (normalizedCubeMeasure Q)).toReal := by
  let μ := normalizedCubeMeasure Q
  let : MeasureTheory.IsProbabilityMeasure μ := ⟨by simp [μ]⟩
  have hle : MeasureTheory.eLpNorm (fun x => HilbertVec.ofVec (f x)) 2 μ ≤
      MeasureTheory.eLpNorm (fun x => HilbertVec.ofVec (f x)) p.exponent μ :=
    MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le hp hf.aestronglyMeasurable
  have hcompare : MeasureTheory.eLpNorm f 2 μ ≤
      MeasureTheory.eLpNorm (fun x => HilbertVec.ofVec (f x)) 2 μ := by
    refine MeasureTheory.eLpNorm_mono_ae (Filter.Eventually.of_forall fun x => ?_)
    exact HilbertVec.norm_le_norm_ofVec (f x)
  have hall := hcompare.trans hle
  have htoReal := ENNReal.toReal_mono hf.2.ne hall
  simpa only [μ, cubeLpNorm] using htoReal

/-- The finite Euclidean carrier supplies the legacy normalized cube `L²`
membership used by the existing one-cube weak-flux theorem.  This is a
carrier conversion only: it does not make any pointwise choice of a
representative. -/
theorem MemCubeEuclideanFullWsp.memLpTwo {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    {g : Vec d → Vec d} (hp : (2 : ℝ≥0∞) ≤ p.exponent)
    (hg : MemCubeEuclideanFullWsp Q s p g) :
    MeasureTheory.MemLp g 2 (normalizedCubeMeasure Q) := by
  have htwo : MeasureTheory.MemLp (fun x => HilbertVec.ofVec (g x)) 2
      (normalizedCubeMeasure Q) :=
    hg.1.mono_exponent hp
  apply htwo.mono
  · have hmeas :=
      (HilbertVec.continuousLinearEquivVec d).continuous.comp_aestronglyMeasurable
        htwo.aestronglyMeasurable
    simpa only [Function.comp_apply, HilbertVec.continuousLinearEquivVec_apply,
      HilbertVec.toVec_ofVec] using hmeas
  · exact Filter.Eventually.of_forall fun x => HilbertVec.norm_le_norm_ofVec (g x)

/-- The finite Euclidean carrier remains locally integrable after subtracting
the ordinary cube average.  This is kept private because the public forcing
statement is formulated directly in terms of `g`. -/
private theorem memLp_hilbert_cubeFluctuationVec
    {d : ℕ} (R : TriadicCube d) (p : FiniteLpExponent) (g : Vec d → Vec d)
    (hg : MeasureTheory.MemLp (fun x => HilbertVec.ofVec (g x)) p.exponent
      (normalizedCubeMeasure R)) :
    MeasureTheory.MemLp
      (fun x => HilbertVec.ofVec (cubeFluctuationVec R g x)) p.exponent
      (normalizedCubeMeasure R) := by
  have hconst : MeasureTheory.MemLp
      (fun _ : Vec d => HilbertVec.ofVec (cubeAverageVec R g)) p.exponent
      (normalizedCubeMeasure R) :=
    MeasureTheory.memLp_const _
  simpa only [cubeFluctuationVec_apply, map_sub] using! hg.sub hconst

/-- A parent finite Euclidean `L^p` witness supplies the same witness on any
ordinary triadic descendant. -/
private theorem memLp_hilbert_cubeFluctuationVec_of_parent
    {d : ℕ} {Q R : TriadicCube d} (p : FiniteLpExponent) (g : Vec d → Vec d)
    (hg : MeasureTheory.MemLp (fun x => HilbertVec.ofVec (g x)) p.exponent
      (normalizedCubeMeasure Q))
    (hRQ : openCubeSet R ⊆ openCubeSet Q) :
    MeasureTheory.MemLp
      (fun x => HilbertVec.ofVec (cubeFluctuationVec R g x)) p.exponent
      (normalizedCubeMeasure R) := by
  let F : CubeEuclideanLpField Q p := ⟨g, hg⟩
  exact memLp_hilbert_cubeFluctuationVec R p g
    (by simpa only [F, CubeEuclideanLpField.restrictToSubcube_toField] using
      (F.restrictToSubcube hRQ).euclideanMemLp)

/-- Jensen's inequality for a finite ordinary-descendant average.  The
nonnegativity hypothesis is deliberately local to the finite sum, which is
the form needed before the forcing proof passes to `tsum`. -/
private theorem rpow_descendantsAverage_le_descendantsAverage_rpow
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) {ζ : ℝ}
    (hζ : 1 ≤ ζ) {F : TriadicCube d → ℝ}
    (hF_nonneg : ∀ R, R ∈ descendantsAtDepth Q j → 0 ≤ F R) :
    Real.rpow (descendantsAverage Q j F) ζ ≤
      descendantsAverage Q j (fun R => Real.rpow (F R) ζ) := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  let w : TriadicCube d → ℝ := fun _ => (D.card : ℝ)⁻¹
  have hD_nonempty : D.Nonempty := by
    simpa [D] using descendantsAtDepth_nonempty Q j
  have hcard_ne : (D.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hD_nonempty
  have hcard_pos : 0 < (D.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hD_nonempty
  have hw_nonneg : ∀ R ∈ D, 0 ≤ w R := by
    intro R _
    exact inv_nonneg.mpr hcard_pos.le
  have hw_sum : ∑ R ∈ D, w R = 1 := by
    simp [w, Finset.sum_const, nsmul_eq_mul, hcard_ne]
  have hmem : ∀ R ∈ D, F R ∈ Set.Ici (0 : ℝ) := by
    intro R hR
    exact hF_nonneg R (by simpa [D] using hR)
  have hJensen :=
    (convexOn_rpow hζ).map_sum_le
      (t := D) (w := w) (p := F) hw_nonneg hw_sum hmem
  have hleft :
      (fun x : ℝ => x ^ ζ) (∑ R ∈ D, w R • F R) =
        Real.rpow (descendantsAverage Q j F) ζ := by
    congr 1
    simp only [descendantsAverage, D, w, smul_eq_mul]
    rw [Finset.mul_sum]
  have hright :
      (∑ R ∈ D, w R • (fun x : ℝ => x ^ ζ) (F R)) =
        descendantsAverage Q j (fun R => Real.rpow (F R) ζ) := by
    simp only [descendantsAverage, D, w, smul_eq_mul, Real.rpow_eq_pow]
    rw [Finset.mul_sum]
  calc
    Real.rpow (descendantsAverage Q j F) ζ =
        (fun x : ℝ => x ^ ζ) (∑ R ∈ D, w R • F R) := hleft.symm
    _ ≤ ∑ R ∈ D, w R • (fun x : ℝ => x ^ ζ) (F R) := hJensen
    _ = descendantsAverage Q j (fun R => Real.rpow (F R) ζ) := hright

/-- Pointwise input for the depth-power bridge: on every descendant the
legacy normalized `L²` oscillation is bounded by the finite Euclidean
normalized `Lᵖ` oscillation. -/
private theorem cubeLpNorm_two_le_eLpNorm_finite_of_parent_descendant
    {d : ℕ} {Q R : TriadicCube d} (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) ≤ p.exponent) (g : Vec d → Vec d)
    (hg : MeasureTheory.MemLp (fun x => HilbertVec.ofVec (g x)) p.exponent
      (normalizedCubeMeasure Q))
    (hRQ : openCubeSet R ⊆ openCubeSet Q) :
    cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R g) ≤
      (MeasureTheory.eLpNorm
        (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
        (normalizedCubeMeasure R)).toReal := by
  simpa only [cubeFluctuationVec_apply] using
    cubeLpNorm_two_le_eLpNorm_finite_of_memLp R p hp (cubeFluctuationVec R g)
      (memLp_hilbert_cubeFluctuationVec_of_parent p g hg hRQ)

/-- The real normalized residual average at one ordinary descendant depth is
literally the `toReal` of the internal disjoint finite-`p` depth energy.
This is the conversion point at which the finite partial calculation enters
the `ENNReal` disjoint-energy lane. -/
private theorem disjointDepthPower_toReal_eq_descendantsAverage
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (p : FiniteLpExponent)
    (g : Vec d → Vec d)
    (hg : MeasureTheory.MemLp (fun x => HilbertVec.ofVec (g x)) p.exponent
      (normalizedCubeMeasure Q)) :
    (cubeEuclideanPositiveBesovDisjointDepthPower Q p g j).toReal =
      descendantsAverage Q j (fun R =>
        Real.rpow
          ((MeasureTheory.eLpNorm
            (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
            (normalizedCubeMeasure R)).toReal)
          p.exponent.toReal) := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  have hcard : (D.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr (by
      simpa [D] using descendantsAtDepth_nonempty Q j)
  have htop : ∀ R ∈ D,
      (MeasureTheory.eLpNorm
        (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
        (normalizedCubeMeasure R)) ^ p.exponent.toReal ≠ ∞ := by
    intro R hR
    have hres := memLp_hilbert_cubeFluctuationVec_of_parent p g hg
      (openCubeSet_subset_of_mem_descendantsAtDepth (by simpa [D] using hR))
    exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg
      hres.eLpNorm_lt_top.ne
  unfold cubeEuclideanPositiveBesovDisjointDepthPower
  change (((D.card : ℝ≥0∞)⁻¹ * D.attach.sum (fun R =>
      (MeasureTheory.eLpNorm
        (fun x => HilbertVec.ofVec (g x - cubeAverageVec R.1 g)) p.exponent
        (normalizedCubeMeasure R.1)) ^ p.exponent.toReal)).toReal) = _
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_sum (fun R _ => htop R.1 R.2)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ← ENNReal.toReal_rpow]
  rw [Finset.sum_attach D (fun R =>
    (MeasureTheory.eLpNorm
      (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
      (normalizedCubeMeasure R)).toReal ^ p.exponent.toReal)]
  simp only [descendantsAverage, D, Real.rpow_eq_pow]

/-- A finite initial portion of the physical-scale disjoint energy controls
the corresponding note-normalized finite residual sum.  This is the exact
physical-scale reindexing needed before descendant-average composition is
used in the forcing aggregation. -/
private theorem finite_noteResidualSum_le_scale_mul_disjointPowerEnergy
    {d : ℕ} (Q : TriadicCube d) (s2 : FractionalOrder) (N : ℕ)
    (p : FiniteLpExponent) (g : Vec d → Vec d)
    (hg : MeasureTheory.MemLp (fun x => HilbertVec.ofVec (g x)) p.exponent
      (normalizedCubeMeasure Q))
    (hfin : cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g < ∞) :
    ∑ j ∈ Finset.range (N + 1),
      Real.rpow 3 (s2.1 * p.exponent.toReal * (j : ℝ)) *
        descendantsAverage Q j (fun R =>
          Real.rpow
            ((MeasureTheory.eLpNorm
              (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
              (normalizedCubeMeasure R)).toReal)
            p.exponent.toReal) ≤
      Real.rpow 3 (s2.1 * p.exponent.toReal * (Q.scale : ℝ)) *
        (cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g).toReal := by
  let r : ℝ := p.exponent.toReal
  let E : ℝ≥0∞ := cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g
  let w : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal
    (Real.rpow 3 (-(s2.1 * r * ((Q.scale - (j : ℤ) : ℤ) : ℝ))) )
  let A : ℕ → ℝ≥0∞ := fun j => cubeEuclideanPositiveBesovDisjointDepthPower Q p g j
  have hsum : ∑ j ∈ Finset.range (N + 1), w j * A j ≤ E := by
    dsimp [E, w, A, cubeEuclideanPositiveBesovDisjointPowerEnergy]
    exact ENNReal.sum_le_tsum _
  have hreal : (∑ j ∈ Finset.range (N + 1), w j * A j).toReal ≤ E.toReal :=
    ENNReal.toReal_mono hfin.ne hsum
  have hsum_fin : ∑ j ∈ Finset.range (N + 1), w j * A j < ∞ :=
    lt_of_le_of_lt hsum hfin
  have hterm_top : ∀ j ∈ Finset.range (N + 1), w j * A j ≠ ∞ := by
    intro j hj
    apply lt_top_iff_ne_top.mp
    apply lt_of_le_of_lt (Finset.single_le_sum (fun _ _ => bot_le) hj)
    exact hsum_fin
  rw [ENNReal.toReal_sum hterm_top] at hreal
  have hweight_nonneg : 0 ≤ Real.rpow 3 (s2.1 * r * (Q.scale : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hconvert :
      (∑ j ∈ Finset.range (N + 1),
        Real.rpow 3 (s2.1 * r * (j : ℝ)) *
          descendantsAverage Q j (fun R =>
            Real.rpow
              ((MeasureTheory.eLpNorm
                (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
                (normalizedCubeMeasure R)).toReal)
              r)) =
        Real.rpow 3 (s2.1 * r * (Q.scale : ℝ)) *
          (∑ j ∈ Finset.range (N + 1), (w j * A j).toReal) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [ENNReal.toReal_mul, disjointDepthPower_toReal_eq_descendantsAverage Q j p g hg]
    dsimp [w]
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (by norm_num) _)]
    have h3 : 0 < (3 : ℝ) := by norm_num
    have hscale :
        Real.rpow 3 (s2.1 * r * (Q.scale : ℝ)) *
          Real.rpow 3 (-(s2.1 * r * ((Q.scale - (j : ℤ) : ℤ) : ℝ))) =
        Real.rpow 3 (s2.1 * r * (j : ℝ)) := by
      calc
        Real.rpow 3 (s2.1 * r * (Q.scale : ℝ)) *
            Real.rpow 3 (-(s2.1 * r * ((Q.scale - (j : ℤ) : ℤ) : ℝ))) =
          Real.rpow 3 (s2.1 * r * (Q.scale : ℝ) +
            -(s2.1 * r * ((Q.scale - (j : ℤ) : ℤ) : ℝ))) :=
          (Real.rpow_add h3 _ _).symm
        _ = Real.rpow 3 (s2.1 * r * (j : ℝ)) := by
          congr 1
          push_cast
          ring
    let B : ℝ := descendantsAverage Q j (fun R =>
      Real.rpow
        ((MeasureTheory.eLpNorm
          (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
          (normalizedCubeMeasure R)).toReal)
        r)
    let v : ℝ := Real.rpow 3 (-(s2.1 * r * ((Q.scale - (j : ℤ) : ℤ) : ℝ)))
    have hscale' : Real.rpow 3 (s2.1 * r * (j : ℝ)) * B =
        Real.rpow 3 (s2.1 * r * (Q.scale : ℝ)) *
          (v * B) := by
      dsimp [v]
      change Real.rpow 3 (s2.1 * r * (j : ℝ)) * B =
        Real.rpow 3 (s2.1 * r * (Q.scale : ℝ)) *
          (Real.rpow 3 (-(s2.1 * r * ((Q.scale - (j : ℤ) : ℤ) : ℝ))) * B)
      rw [← hscale]
      ring
    simpa [B, v, r, Real.rpow_eq_pow] using hscale'
  rw [hconvert]
  apply mul_le_mul_of_nonneg_left ?_ hweight_nonneg
  simpa only [E] using hreal

/-- The finite-`p` oscillation energy controls the legacy depthwise `L²`
energy before any infinite-depth supremum is taken.  Keeping this statement
at a fixed depth is what permits the forcing argument to pass to the old
`sSup` only after a uniform finite partial bound has been established. -/
private theorem cubeBesovPositiveVectorDepthAverage_rpow_le_descendantsAverage_eLpNorm
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) ≤ p.exponent) (g : Vec d → Vec d)
    (hpoint : ∀ R, R ∈ descendantsAtDepth Q j →
      cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R g) ≤
        (MeasureTheory.eLpNorm
          (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
          (normalizedCubeMeasure R)).toReal) :
    Real.rpow (cubeBesovPositiveVectorDepthAverage Q g j)
        (p.exponent.toReal / 2) ≤
      descendantsAverage Q j (fun R =>
        Real.rpow
          ((MeasureTheory.eLpNorm
            (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
            (normalizedCubeMeasure R)).toReal)
          p.exponent.toReal) := by
  let r : ℝ := p.exponent.toReal
  have hr_two : 2 ≤ r := by
    dsimp [r]
    exact ENNReal.toReal_mono p.lt_top.ne hp
  have hr_half_one : 1 ≤ r / 2 := by linarith
  have hnonneg : ∀ R, R ∈ descendantsAtDepth Q j →
      0 ≤ (cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R g)) ^ 2 := by
    intro R _
    exact sq_nonneg _
  have hJensen := rpow_descendantsAverage_le_descendantsAverage_rpow Q j
    hr_half_one (F := fun R =>
      (cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R g)) ^ 2) hnonneg
  unfold cubeBesovPositiveVectorDepthAverage
  calc
    Real.rpow
        (descendantsAverage Q j (fun R =>
          (cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R g)) ^ 2))
        (r / 2) ≤
        descendantsAverage Q j (fun R =>
          Real.rpow
            ((cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R g)) ^ 2)
            (r / 2)) := by
          simpa [r] using hJensen
    _ ≤ descendantsAverage Q j (fun R =>
          Real.rpow
            ((MeasureTheory.eLpNorm
              (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
              (normalizedCubeMeasure R)).toReal)
            r) := by
          refine descendantsAverage_le_descendantsAverage Q j ?_
          intro R hR
          have hRnonneg : 0 ≤ cubeLpNorm R (2 : ℝ≥0∞)
              (cubeFluctuationVec R g) := cubeLpNorm_nonneg R _ _
          have hbound := hpoint R hR
          have he_nonneg : 0 ≤
              (MeasureTheory.eLpNorm
                (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
                (normalizedCubeMeasure R)).toReal := ENNReal.toReal_nonneg
          have hsquare : (cubeLpNorm R (2 : ℝ≥0∞)
              (cubeFluctuationVec R g)) ^ 2 ≤
              ((MeasureTheory.eLpNorm
                (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
                (normalizedCubeMeasure R)).toReal) ^ 2 := by
            nlinarith
          have hpow := Real.rpow_le_rpow (sq_nonneg _ ) hsquare
            (by positivity : 0 ≤ r / 2)
          rw [← Real.rpow_natCast (x :=
            (MeasureTheory.eLpNorm
              (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
              (normalizedCubeMeasure R)).toReal) 2] at hpow
          rw [← Real.rpow_mul he_nonneg] at hpow
          have hpow' :
              Real.rpow
                ((cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R g)) ^ 2)
                (r / 2) ≤
              Real.rpow
                ((MeasureTheory.eLpNorm
                  (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
                  (normalizedCubeMeasure R)).toReal) r := by
            calc
              Real.rpow
                  ((cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R g)) ^ 2)
                  (r / 2) ≤
                  Real.rpow
                    ((MeasureTheory.eLpNorm
                      (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
                      (normalizedCubeMeasure R)).toReal) (2 * (r / 2)) := by
                        simpa [Real.rpow_eq_pow] using hpow
              _ = Real.rpow
                  ((MeasureTheory.eLpNorm
                    (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
                    (normalizedCubeMeasure R)).toReal) r := by
                      congr 1
                      ring
          simpa [sub_eq_add_neg, add_comm] using hpow'

/-- The preceding depthwise comparison with the finite Euclidean witness on
the parent cube.  This is the concrete input used for each summand of the
finite partial `q = 2` seminorm. -/
private theorem cubeBesovPositiveVectorDepthAverage_rpow_le_descendantsAverage_eLpNorm_of_memLp
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) ≤ p.exponent) (g : Vec d → Vec d)
    (hg : MeasureTheory.MemLp (fun x => HilbertVec.ofVec (g x)) p.exponent
      (normalizedCubeMeasure Q)) :
    Real.rpow (cubeBesovPositiveVectorDepthAverage Q g j)
        (p.exponent.toReal / 2) ≤
      descendantsAverage Q j (fun R =>
        Real.rpow
          ((MeasureTheory.eLpNorm
            (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
            (normalizedCubeMeasure R)).toReal)
          p.exponent.toReal) := by
  apply cubeBesovPositiveVectorDepthAverage_rpow_le_descendantsAverage_eLpNorm
    Q j p hp g
  intro R hR
  exact cubeLpNorm_two_le_eLpNorm_finite_of_parent_descendant p hp g hg
    (openCubeSet_subset_of_mem_descendantsAtDepth hR)

/-- After applying the finite exponent, a single legacy positive-Besov
depth is bounded by the corresponding normalized finite-`p` disjoint
oscillation average. -/
private theorem cubeBesovPositiveVectorDepthSeminorm_rpow_le_eLpNorm
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder) (j : ℕ)
    (p : FiniteLpExponent) (hp : (2 : ℝ≥0∞) ≤ p.exponent)
    (g : Vec d → Vec d)
    (hg : MeasureTheory.MemLp (fun x => HilbertVec.ofVec (g x)) p.exponent
      (normalizedCubeMeasure Q)) :
    Real.rpow (cubeBesovPositiveVectorDepthSeminorm Q s.1 g j)
        p.exponent.toReal ≤
      Real.rpow 3 (s.1 * p.exponent.toReal * (j : ℝ)) *
        descendantsAverage Q j (fun R =>
          Real.rpow
            ((MeasureTheory.eLpNorm
              (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
              (normalizedCubeMeasure R)).toReal)
            p.exponent.toReal) := by
  let r : ℝ := p.exponent.toReal
  let A : ℝ := cubeBesovPositiveVectorDepthAverage Q g j
  have hA : 0 ≤ A := cubeBesovPositiveVectorDepthAverage_nonneg Q g j
  have hthree : 0 ≤ (3 : ℝ) := by norm_num
  have hscale_nonneg : 0 ≤ Real.rpow 3 (s.1 * (j : ℝ)) :=
    Real.rpow_nonneg hthree _
  have hdepth :=
    cubeBesovPositiveVectorDepthAverage_rpow_le_descendantsAverage_eLpNorm_of_memLp
      Q j p hp g hg
  change Real.rpow (Real.rpow 3 (s.1 * (j : ℝ)) * Real.sqrt A) r ≤ _
  have hscale :
      Real.rpow (Real.rpow 3 (s.1 * (j : ℝ))) r =
        Real.rpow 3 (s.1 * r * (j : ℝ)) := by
    calc
      Real.rpow (Real.rpow 3 (s.1 * (j : ℝ))) r =
          Real.rpow 3 ((s.1 * (j : ℝ)) * r) :=
        (Real.rpow_mul hthree _ _).symm
      _ = Real.rpow 3 (s.1 * r * (j : ℝ)) := by
        congr 1
        ring
  calc
    Real.rpow (Real.rpow 3 (s.1 * (j : ℝ)) * Real.sqrt A) r =
        Real.rpow (Real.rpow 3 (s.1 * (j : ℝ))) r *
          Real.rpow (Real.sqrt A) r := by
            exact Real.mul_rpow hscale_nonneg (Real.sqrt_nonneg _)
    _ = Real.rpow 3 (s.1 * r * (j : ℝ)) * Real.rpow A (r / 2) := by
          rw [hscale, Real.sqrt_eq_rpow]
          congr 1
          calc
            Real.rpow (Real.rpow A (1 / 2)) r =
                Real.rpow A ((1 / 2) * r) :=
              (Real.rpow_mul hA _ _).symm
            _ = Real.rpow A (r / 2) := by
              congr 1
              ring
    _ ≤ Real.rpow 3 (s.1 * r * (j : ℝ)) *
        descendantsAverage Q j (fun R =>
          Real.rpow
            ((MeasureTheory.eLpNorm
              (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
              (normalizedCubeMeasure R)).toReal)
            r) :=
      mul_le_mul_of_nonneg_left (by simpa [A, r] using hdepth)
        (Real.rpow_nonneg hthree _)

/-- A fixed legacy depth is dominated by the fractional-gap weighted finite
`p` depth energy.  This is the precise termwise hypothesis consumed by the
finite partial Hölder estimate. -/
private theorem cubeBesovPositiveVectorDepthSeminorm_sq_le_weighted_eLpNorm
    {d : ℕ} (Q : TriadicCube d) (s s2 : FractionalOrder) (j : ℕ)
    (p : FiniteLpExponent) (hp : (2 : ℝ≥0∞) ≤ p.exponent)
    (g : Vec d → Vec d)
    (hg : MeasureTheory.MemLp (fun x => HilbertVec.ofVec (g x)) p.exponent
      (normalizedCubeMeasure Q)) :
    (cubeBesovPositiveVectorDepthSeminorm Q s.1 g j) ^ 2 ≤
      (Real.rpow 3 (-(s2.1 - s.1) * (j : ℝ)) *
        Real.rpow
          (Real.rpow 3 (s2.1 * p.exponent.toReal * (j : ℝ)) *
            descendantsAverage Q j (fun R =>
              Real.rpow
                ((MeasureTheory.eLpNorm
                  (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
                  (normalizedCubeMeasure R)).toReal)
                p.exponent.toReal))
          (1 / p.exponent.toReal)) ^ 2 := by
  let r : ℝ := p.exponent.toReal
  let A : ℝ := descendantsAverage Q j (fun R =>
    Real.rpow
      ((MeasureTheory.eLpNorm
        (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
        (normalizedCubeMeasure R)).toReal)
      p.exponent.toReal)
  let w : ℝ := Real.rpow 3 (-(s2.1 - s.1) * (j : ℝ))
  let E : ℝ := Real.rpow 3 (s2.1 * r * (j : ℝ)) * A
  have hr : 0 < r := finiteLpExponent_toReal_pos p
  have hthree : 0 < (3 : ℝ) := by norm_num
  have hw : 0 ≤ w := Real.rpow_nonneg hthree.le _
  have hA : 0 ≤ A := by
    dsimp [A]
    exact descendantsAverage_nonneg Q j _ fun R _ => Real.rpow_nonneg
      ENNReal.toReal_nonneg _
  have hE : 0 ≤ E := mul_nonneg (Real.rpow_nonneg hthree.le _) hA
  have hdepth := cubeBesovPositiveVectorDepthSeminorm_rpow_le_eLpNorm
    Q s j p hp g hg
  have hfactor :
      Real.rpow 3 (s.1 * r * (j : ℝ)) * A = Real.rpow w r * E := by
    dsimp [w, E]
    have hsum :
        Real.rpow 3 (-(s2.1 - s.1) * (j : ℝ) * r) *
            Real.rpow 3 (s2.1 * r * (j : ℝ)) =
          Real.rpow 3 (-(s2.1 - s.1) * (j : ℝ) * r +
            s2.1 * r * (j : ℝ)) :=
      (Real.rpow_add hthree _ _).symm
    have hpoww :
        Real.rpow (Real.rpow 3 (-(s2.1 - s.1) * (j : ℝ))) r =
          Real.rpow 3 (-(s2.1 - s.1) * (j : ℝ) * r) :=
      (Real.rpow_mul hthree.le _ _).symm
    calc
      Real.rpow 3 (s.1 * r * (j : ℝ)) * A =
          (Real.rpow 3 (-(s2.1 - s.1) * (j : ℝ) * r) *
            Real.rpow 3 (s2.1 * r * (j : ℝ))) * A := by
              rw [hsum]
              congr 1
              ring_nf
      _ = Real.rpow 3 (-(s2.1 - s.1) * (j : ℝ) * r) *
          (Real.rpow 3 (s2.1 * r * (j : ℝ)) * A) := by ring
      _ = Real.rpow (Real.rpow 3 (-(s2.1 - s.1) * (j : ℝ))) r *
          (Real.rpow 3 (s2.1 * r * (j : ℝ)) * A) := by
            rw [hpoww]
  apply sq_le_weighted_rpow_of_rpow_le
    (cubeBesovPositiveVectorDepthSeminorm_nonneg Q s.1 g j) hw hE hr
  rw [← hfactor]
  simpa [r] using! hdepth

/-- Finite legacy partial seminorms reduce to a weighted finite-`p` energy
sum.  The only remaining task in the global forcing proof is to bound the
explicit geometric weight sum and flatten the two descendant depths. -/
private theorem cubeBesovPositiveVectorPartialSeminormTwo_rpow_le_weighted_eLpNorm
    {d : ℕ} (Q : TriadicCube d) (s s2 : FractionalOrder) (N : ℕ)
    (p : FiniteLpExponent) (hp : (2 : ℝ≥0∞) < p.exponent)
    (g : Vec d → Vec d)
    (hg : MeasureTheory.MemLp (fun x => HilbertVec.ofVec (g x)) p.exponent
      (normalizedCubeMeasure Q)) :
    Real.rpow (cubeBesovPositiveVectorPartialSeminormTwo Q s.1 N g)
        p.exponent.toReal ≤
      ((∑ j ∈ Finset.range (N + 1),
          (Real.rpow
            (Real.rpow 3 (s2.1 * p.exponent.toReal * (j : ℝ)) *
              descendantsAverage Q j (fun R =>
                Real.rpow
                  ((MeasureTheory.eLpNorm
                    (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
                    (normalizedCubeMeasure R)).toReal)
                  p.exponent.toReal))
            (1 / p.exponent.toReal) ^ 2) ^
              (p.exponent.toReal / 2)) ^ (1 / (p.exponent.toReal / 2)) *
        (∑ j ∈ Finset.range (N + 1),
          ((Real.rpow 3 (-(s2.1 - s.1) * (j : ℝ))) ^ 2) ^
            (p.exponent.toReal / (p.exponent.toReal - 2))) ^
          (1 / (p.exponent.toReal / (p.exponent.toReal - 2)))) ^
        (p.exponent.toReal / 2) := by
  let r : ℝ := p.exponent.toReal
  let D : ℕ → ℝ := fun j => cubeBesovPositiveVectorDepthSeminorm Q s.1 g j
  let w : ℕ → ℝ := fun j => Real.rpow 3 (-(s2.1 - s.1) * (j : ℝ))
  let a : ℕ → ℝ := fun j =>
    Real.rpow
      (Real.rpow 3 (s2.1 * r * (j : ℝ)) *
        descendantsAverage Q j (fun R =>
          Real.rpow
            ((MeasureTheory.eLpNorm
              (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
              (normalizedCubeMeasure R)).toReal)
            r))
      (1 / r)
  have hr : 2 < r := by
    dsimp [r]
    exact (ENNReal.toReal_lt_toReal ENNReal.ofNat_ne_top p.lt_top.ne).2 hp
  have hterm : ∀ j ∈ Finset.range (N + 1), D j ^ 2 ≤ (w j * a j) ^ 2 := by
    intro j _
    exact cubeBesovPositiveVectorDepthSeminorm_sq_le_weighted_eLpNorm
      Q s s2 j p hp.le g hg
  have hpartial_nonneg : 0 ≤ cubeBesovPositiveVectorPartialSeminormTwo Q s.1 N g :=
    cubeBesovPositiveVectorPartialSeminormTwo_nonneg Q s.1 N g
  have hpower :
      Real.rpow (cubeBesovPositiveVectorPartialSeminormTwo Q s.1 N g) r =
        Real.rpow
          ((cubeBesovPositiveVectorPartialSeminormTwo Q s.1 N g) ^ 2) (r / 2) := by
    calc
      Real.rpow (cubeBesovPositiveVectorPartialSeminormTwo Q s.1 N g) r =
          Real.rpow (cubeBesovPositiveVectorPartialSeminormTwo Q s.1 N g)
            (2 * (r / 2)) := by
              congr 1
              ring
      _ = Real.rpow
          (Real.rpow (cubeBesovPositiveVectorPartialSeminormTwo Q s.1 N g) 2)
          (r / 2) := Real.rpow_mul hpartial_nonneg _ _
      _ = Real.rpow
          ((cubeBesovPositiveVectorPartialSeminormTwo Q s.1 N g) ^ 2) (r / 2) := by
            congr 1
            exact Real.rpow_natCast _ 2
  rw [hpower, sq_cubeBesovPositiveVectorPartialSeminormTwo]
  change Real.rpow (∑ j ∈ Finset.range (N + 1), D j ^ 2) (r / 2) ≤ _
  simpa [D, w, a, r] using
    finite_square_sum_rpow_le_weighted_of_sq_le
      (Finset.range (N + 1)) hr D a w hterm

/-- The endpoint `p = 2` finite partial estimate.  No Hölder tail is needed:
the larger fractional order controls each square-sum depth directly. -/
private theorem cubeBesovPositiveVectorPartialSeminormTwo_sq_le_eLpNorm_of_toReal_eq_two
    {d : ℕ} (Q : TriadicCube d) (s s2 : FractionalOrder) (hs : s.1 ≤ s2.1)
    (N : ℕ) (p : FiniteLpExponent) (hp2 : p.exponent.toReal = 2)
    (g : Vec d → Vec d)
    (hg : MeasureTheory.MemLp (fun x => HilbertVec.ofVec (g x)) p.exponent
      (normalizedCubeMeasure Q)) :
    (cubeBesovPositiveVectorPartialSeminormTwo Q s.1 N g) ^ 2 ≤
      ∑ j ∈ Finset.range (N + 1),
        Real.rpow 3 (s2.1 * 2 * (j : ℝ)) *
          descendantsAverage Q j (fun R =>
            Real.rpow
              ((MeasureTheory.eLpNorm
                (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
                (normalizedCubeMeasure R)).toReal)
              2) := by
  rw [sq_cubeBesovPositiveVectorPartialSeminormTwo]
  refine Finset.sum_le_sum ?_
  intro j _
  have hdepth := cubeBesovPositiveVectorDepthSeminorm_rpow_le_eLpNorm
    Q s j p (by
      apply (ENNReal.toReal_le_toReal ENNReal.ofNat_ne_top p.lt_top.ne).mp
      simp [hp2]) g hg
  have hA : 0 ≤ descendantsAverage Q j (fun R =>
      Real.rpow
        ((MeasureTheory.eLpNorm
          (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
          (normalizedCubeMeasure R)).toReal)
        2) :=
    descendantsAverage_nonneg Q j _ fun R _ => Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hweight : Real.rpow 3 (s.1 * 2 * (j : ℝ)) ≤
      Real.rpow 3 (s2.1 * 2 * (j : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    gcongr
  have hdepth' : (cubeBesovPositiveVectorDepthSeminorm Q s.1 g j) ^ 2 ≤
      Real.rpow 3 (s.1 * 2 * (j : ℝ)) *
        descendantsAverage Q j (fun R =>
          Real.rpow
            ((MeasureTheory.eLpNorm
              (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
              (normalizedCubeMeasure R)).toReal)
            2) := by
    simpa [hp2, Real.rpow_natCast] using hdepth
  exact hdepth'.trans (mul_le_mul_of_nonneg_right hweight hA)

/-- The algebraic form of the strict finite-`p` partial estimate after the
Hölder first factor has been collapsed.  Keeping this as a real statement
avoids any finiteness or `sSup` hypothesis at the source-facing interface. -/
private theorem partial_rpow_le_weighted_energy_mul_holder_tail
    {d : ℕ} (Q : TriadicCube d) (s s2 : FractionalOrder) (N : ℕ)
    (p : FiniteLpExponent) (hp : (2 : ℝ≥0∞) < p.exponent)
    (g : Vec d → Vec d)
    (hg : MeasureTheory.MemLp (fun x => HilbertVec.ofVec (g x)) p.exponent
      (normalizedCubeMeasure Q)) :
    Real.rpow (cubeBesovPositiveVectorPartialSeminormTwo Q s.1 N g)
        p.exponent.toReal ≤
      (∑ j ∈ Finset.range (N + 1),
        Real.rpow 3 (s2.1 * p.exponent.toReal * (j : ℝ)) *
          descendantsAverage Q j (fun R =>
            Real.rpow
              ((MeasureTheory.eLpNorm
                (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
                (normalizedCubeMeasure R)).toReal)
              p.exponent.toReal)) *
      Real.rpow
        (∑ j ∈ Finset.range (N + 1),
          ((Real.rpow 3 (-(s2.1 - s.1) * (j : ℝ))) ^ 2) ^
            (p.exponent.toReal / (p.exponent.toReal - 2)))
        ((p.exponent.toReal - 2) / 2) := by
  let r : ℝ := p.exponent.toReal
  let A : ℝ := ∑ j ∈ Finset.range (N + 1),
    Real.rpow 3 (s2.1 * r * (j : ℝ)) *
      descendantsAverage Q j (fun R =>
        Real.rpow
          ((MeasureTheory.eLpNorm
            (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
            (normalizedCubeMeasure R)).toReal)
          r)
  let T : ℝ := ∑ j ∈ Finset.range (N + 1),
    ((Real.rpow 3 (-(s2.1 - s.1) * (j : ℝ))) ^ 2) ^ (r / (r - 2))
  have hr : 2 < r := by
    dsimp [r]
    exact (ENNReal.toReal_lt_toReal ENNReal.ofNat_ne_top p.lt_top.ne).2 hp
  have hA : 0 ≤ A := by
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (descendantsAverage_nonneg Q j _ fun R _ =>
        Real.rpow_nonneg ENNReal.toReal_nonneg _)
  have hT : 0 ≤ T := by
    apply Finset.sum_nonneg
    intro j _
    exact Real.rpow_nonneg (sq_nonneg _) _
  have hmain := cubeBesovPositiveVectorPartialSeminormTwo_rpow_le_weighted_eLpNorm
    Q s s2 N p hp g hg
  have hfirst :
      (∑ j ∈ Finset.range (N + 1),
        (Real.rpow
          (Real.rpow 3 (s2.1 * r * (j : ℝ)) *
            descendantsAverage Q j (fun R =>
              Real.rpow
                ((MeasureTheory.eLpNorm
                  (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
                  (normalizedCubeMeasure R)).toReal)
                r))
          (1 / r) ^ 2) ^ (r / 2)) = A := by
    apply Finset.sum_congr rfl
    intro j _
    let x : ℝ := Real.rpow 3 (s2.1 * r * (j : ℝ)) *
      descendantsAverage Q j (fun R =>
        Real.rpow
          ((MeasureTheory.eLpNorm
            (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
            (normalizedCubeMeasure R)).toReal)
          r)
    have hx : 0 ≤ x := by
      dsimp [x]
      exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (descendantsAverage_nonneg Q j _ fun R _ =>
          Real.rpow_nonneg ENNReal.toReal_nonneg _)
    change ((Real.rpow x (1 / r)) ^ (2 : ℕ)) ^ (r / 2) = x
    calc
      ((Real.rpow x (1 / r)) ^ (2 : ℕ)) ^ (r / 2) =
          Real.rpow (Real.rpow x (1 / r)) (2 * (r / 2)) := by
            rw [← Real.rpow_natCast]
            exact (Real.rpow_mul (Real.rpow_nonneg hx _) _ _).symm
      _ = Real.rpow x ((1 / r) * (2 * (r / 2))) := by
        exact (Real.rpow_mul hx _ _).symm
      _ = x := by
        rw [show (1 / r) * (2 * (r / 2)) = 1 by field_simp [hr.ne']]
        exact Real.rpow_one x
  rw [show
      ((∑ j ∈ Finset.range (N + 1),
          (Real.rpow
            (Real.rpow 3 (s2.1 * r * (j : ℝ)) *
              descendantsAverage Q j (fun R =>
                Real.rpow
                  ((MeasureTheory.eLpNorm
                    (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
                    (normalizedCubeMeasure R)).toReal)
                  r))
            (1 / r) ^ 2) ^ (r / 2)) ^ (1 / (r / 2)) *
        (∑ j ∈ Finset.range (N + 1),
          ((Real.rpow 3 (-(s2.1 - s.1) * (j : ℝ))) ^ 2) ^
            (r / (r - 2))) ^ (1 / (r / (r - 2)))) ^ (r / 2) =
        A * Real.rpow T ((r - 2) / 2) by
      rw [hfirst]
      calc
        (A ^ (1 / (r / 2)) * T ^ (1 / (r / (r - 2)))) ^ (r / 2) =
            (A ^ (1 / (r / 2))) ^ (r / 2) *
              (T ^ (1 / (r / (r - 2)))) ^ (r / 2) := by
              exact Real.mul_rpow
                (Real.rpow_nonneg hA _) (Real.rpow_nonneg hT _)
        _ = A ^ ((1 / (r / 2)) * (r / 2)) *
              T ^ ((1 / (r / (r - 2)) * (r / 2))) := by
              rw [← Real.rpow_mul hA, ← Real.rpow_mul hT]
        _ = A * Real.rpow T ((r - 2) / 2) := by
              have htail : (1 / (r / (r - 2))) * (r / 2) = (r - 2) / 2 := by
                field_simp [hr.ne']
              have hfirstexp : (1 / (r / 2)) * (r / 2) = 1 := by
                field_simp [hr.ne']
              rw [hfirstexp, Real.rpow_one, htail]
              rfl
    ]
    at hmain
  simpa [A, T, r] using hmain

/-- Strict finite-`p` partial bridge in real form. -/
private theorem partial_le_five_mul_gap_inv_mul_scale_mul_disjoint_root_of_two_lt
    {d : ℕ} (Q : TriadicCube d) (s s2 : FractionalOrder)
    (hss2 : s.1 < s2.1) (N : ℕ) (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) < p.exponent) (g : Vec d → Vec d)
    (hg : MeasureTheory.MemLp (fun x => HilbertVec.ofVec (g x)) p.exponent
      (normalizedCubeMeasure Q))
    (hfin : cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g < ∞) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s.1 N g ≤
      (5 * (s2.1 - s.1)⁻¹) * Real.rpow 3 (s2.1 * (Q.scale : ℝ)) *
        Real.rpow (cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g).toReal
          (p.exponent.toReal)⁻¹ := by
  let r : ℝ := p.exponent.toReal
  let delta : ℝ := s2.1 - s.1
  let E : ℝ≥0∞ := cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g
  let S : ℝ := Real.rpow 3 (s2.1 * (Q.scale : ℝ))
  let C : ℝ := 5 * delta⁻¹
  let U : ℝ := E.toReal
  have hr : 2 < r := by
    dsimp [r]
    exact (ENNReal.toReal_lt_toReal ENNReal.ofNat_ne_top p.lt_top.ne).2 hp
  have hrpos : 0 < r := by linarith
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hdelta_le : delta ≤ 1 := by
    dsimp [delta]
    linarith [s2.2.2, s.2.1]
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hS_nonneg : 0 ≤ S := Real.rpow_nonneg (by norm_num) _
  have hU_nonneg : 0 ≤ U := ENNReal.toReal_nonneg
  have hP_nonneg : 0 ≤ cubeBesovPositiveVectorPartialSeminormTwo Q s.1 N g :=
    cubeBesovPositiveVectorPartialSeminormTwo_nonneg Q s.1 N g
  have hA := finite_noteResidualSum_le_scale_mul_disjointPowerEnergy
    Q s2 N p g hg hfin
  have hT := finite_holder_weight_rpow_le_five_mul_inv hdelta hdelta_le hr N
  have hpartial := partial_rpow_le_weighted_energy_mul_holder_tail
    Q s s2 N p hp g hg
  have hpower :
      Real.rpow (cubeBesovPositiveVectorPartialSeminormTwo Q s.1 N g) r ≤
        Real.rpow (C * S * Real.rpow U r⁻¹) r := by
    have hA' :
        ∑ j ∈ Finset.range (N + 1),
          Real.rpow 3 (s2.1 * r * (j : ℝ)) *
            descendantsAverage Q j (fun R =>
              Real.rpow
                ((MeasureTheory.eLpNorm
                  (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
                  (normalizedCubeMeasure R)).toReal)
                r) ≤ S ^ r * U := by
      rw [show S ^ r = Real.rpow 3 (s2.1 * r * (Q.scale : ℝ)) by
        dsimp [S]
        calc
          (Real.rpow 3 (s2.1 * (Q.scale : ℝ))) ^ r =
              Real.rpow 3 ((s2.1 * (Q.scale : ℝ)) * r) :=
            (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _).symm
          _ = Real.rpow 3 (s2.1 * r * (Q.scale : ℝ)) := by
            congr 1
            ring]
      simpa [U, E, r] using hA
    have htailpow :
        Real.rpow
          (∑ j ∈ Finset.range (N + 1),
            ((Real.rpow 3 (-delta * (j : ℝ))) ^ 2) ^ (r / (r - 2)))
          ((r - 2) / 2) ≤ C ^ r := by
      let T : ℝ := ∑ j ∈ Finset.range (N + 1),
        ((Real.rpow 3 (-delta * (j : ℝ))) ^ 2) ^ (r / (r - 2))
      have hroot : T ^ ((r - 2) / (2 * r)) ≤ C := by
        simpa [T, C] using hT
      have hroot_nonneg : 0 ≤ T ^ ((r - 2) / (2 * r)) :=
        Real.rpow_nonneg (by
          apply Finset.sum_nonneg
          intro j _
          exact Real.rpow_nonneg (sq_nonneg _) _) _
      have hCpow := Real.rpow_le_rpow hroot_nonneg hroot hrpos.le
      have hexp : ((r - 2) / (2 * r)) * r = (r - 2) / 2 := by
        field_simp [hr.ne']
      calc
        T ^ ((r - 2) / 2) = (T ^ ((r - 2) / (2 * r))) ^ r := by
          rw [← Real.rpow_mul]
          · congr 1
            exact hexp.symm
          · apply Finset.sum_nonneg
            intro j _
            exact Real.rpow_nonneg (sq_nonneg _) _
        _ ≤ C ^ r := hCpow
    have htail_nonneg : 0 ≤ Real.rpow
        (∑ j ∈ Finset.range (N + 1),
          ((Real.rpow 3 (-delta * (j : ℝ))) ^ 2) ^ (r / (r - 2)))
        ((r - 2) / 2) :=
      Real.rpow_nonneg (by
        apply Finset.sum_nonneg
        intro j _
        exact Real.rpow_nonneg (sq_nonneg _) _) _
    have hprod := mul_le_mul hA' htailpow htail_nonneg
      (mul_nonneg (Real.rpow_nonneg hS_nonneg _) hU_nonneg)
    have hcpow : 0 ≤ C ^ r := Real.rpow_nonneg hC_nonneg _
    calc
      Real.rpow (cubeBesovPositiveVectorPartialSeminormTwo Q s.1 N g) r ≤
          (∑ j ∈ Finset.range (N + 1),
            Real.rpow 3 (s2.1 * r * (j : ℝ)) *
              descendantsAverage Q j (fun R =>
                Real.rpow
                  ((MeasureTheory.eLpNorm
                    (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
                    (normalizedCubeMeasure R)).toReal)
                  r)) *
            Real.rpow
              (∑ j ∈ Finset.range (N + 1),
                ((Real.rpow 3 (-(s2.1 - s.1) * (j : ℝ))) ^ 2) ^
                  (r / (r - 2)))
              ((r - 2) / 2) := by
              simpa [r, delta] using hpartial
      _ ≤ (S ^ r * U) * C ^ r := hprod
      _ = Real.rpow (C * S * Real.rpow U r⁻¹) r := by
        symm
        calc
          Real.rpow (C * S * Real.rpow U r⁻¹) r =
              Real.rpow (C * S) r * Real.rpow (Real.rpow U r⁻¹) r :=
            Real.mul_rpow (mul_nonneg hC_nonneg hS_nonneg)
              (Real.rpow_nonneg hU_nonneg _)
          _ = (C ^ r * S ^ r) * Real.rpow (Real.rpow U r⁻¹) r := by
            exact congrArg (fun z : ℝ => z * Real.rpow (Real.rpow U r⁻¹) r)
              (Real.mul_rpow hC_nonneg hS_nonneg)
          _ = (C ^ r * S ^ r) * U := by
            congr 1
            calc
              Real.rpow (Real.rpow U r⁻¹) r = Real.rpow U (r⁻¹ * r) :=
                (Real.rpow_mul hU_nonneg _ _).symm
              _ = U := by
                have hinv : r⁻¹ * r = 1 := inv_mul_cancel₀ hrpos.ne'
                rw [hinv]
                exact Real.rpow_one U
          _ = S ^ r * U * C ^ r := by ring
  exact (Real.rpow_le_rpow_iff hP_nonneg
    (mul_nonneg (mul_nonneg hC_nonneg hS_nonneg)
      (Real.rpow_nonneg hU_nonneg _)) hrpos).mp hpower

/-- The endpoint `p = 2` finite-partial bridge, written with a square root
before the public finite-exponent notation is restored. -/
private theorem partial_le_five_mul_gap_inv_mul_scale_mul_disjoint_sqrt_of_toReal_eq_two
    {d : ℕ} (Q : TriadicCube d) (s s2 : FractionalOrder)
    (hss2 : s.1 < s2.1) (N : ℕ) (p : FiniteLpExponent)
    (hp2 : p.exponent.toReal = 2) (g : Vec d → Vec d)
    (hg : MeasureTheory.MemLp (fun x => HilbertVec.ofVec (g x)) p.exponent
      (normalizedCubeMeasure Q))
    (hfin : cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g < ∞) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s.1 N g ≤
      (5 * (s2.1 - s.1)⁻¹) * Real.rpow 3 (s2.1 * (Q.scale : ℝ)) *
        Real.sqrt (cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g).toReal := by
  let delta : ℝ := s2.1 - s.1
  let E : ℝ≥0∞ := cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g
  let S : ℝ := Real.rpow 3 (s2.1 * (Q.scale : ℝ))
  let C : ℝ := 5 * delta⁻¹
  let U : ℝ := E.toReal
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hdelta_le : delta ≤ 1 := by
    dsimp [delta]
    linarith [s2.2.2, s.2.1]
  have hC_nonneg : 0 ≤ C := by dsimp [C]; positivity
  have hC_one : 1 ≤ C := by
    have hinv : 1 ≤ delta⁻¹ := (one_le_inv₀ hdelta).2 hdelta_le
    dsimp [C]
    nlinarith
  have hS_nonneg : 0 ≤ S := Real.rpow_nonneg (by norm_num) _
  have hU_nonneg : 0 ≤ U := ENNReal.toReal_nonneg
  have hP_nonneg : 0 ≤ cubeBesovPositiveVectorPartialSeminormTwo Q s.1 N g :=
    cubeBesovPositiveVectorPartialSeminormTwo_nonneg Q s.1 N g
  have hbase := cubeBesovPositiveVectorPartialSeminormTwo_sq_le_eLpNorm_of_toReal_eq_two
    Q s s2 hss2.le N p hp2 g hg
  have henergy := finite_noteResidualSum_le_scale_mul_disjointPowerEnergy
    Q s2 N p g hg hfin
  have hbase' : (cubeBesovPositiveVectorPartialSeminormTwo Q s.1 N g) ^ 2 ≤ S ^ 2 * U := by
    calc
      (cubeBesovPositiveVectorPartialSeminormTwo Q s.1 N g) ^ 2 ≤
          ∑ j ∈ Finset.range (N + 1),
            Real.rpow 3 (s2.1 * 2 * (j : ℝ)) *
              descendantsAverage Q j (fun R =>
                Real.rpow
                  ((MeasureTheory.eLpNorm
                    (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
                    (normalizedCubeMeasure R)).toReal)
                  2) := hbase
      _ ≤ Real.rpow 3 (s2.1 * 2 * (Q.scale : ℝ)) * E.toReal := by
        simpa [hp2] using henergy
      _ = S ^ 2 * U := by
        dsimp [S, U]
        apply congrArg (fun x : ℝ => x * E.toReal)
        calc
          Real.rpow 3 (s2.1 * 2 * (Q.scale : ℝ)) =
              Real.rpow 3 ((s2.1 * (Q.scale : ℝ)) * 2) := by
            congr 1
            ring
          _ = Real.rpow (Real.rpow 3 (s2.1 * (Q.scale : ℝ))) 2 :=
            Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _
          _ = (Real.rpow 3 (s2.1 * (Q.scale : ℝ))) ^ 2 := by
            exact Real.rpow_natCast _ 2
  have hC_sq : 1 ≤ C ^ 2 := by nlinarith [sq_nonneg (C - 1)]
  have hSU_nonneg : 0 ≤ S ^ 2 * U := mul_nonneg (sq_nonneg S) hU_nonneg
  have hmiddle : S ^ 2 * U ≤ C ^ 2 * (S ^ 2 * U) := by
    simpa using mul_le_mul_of_nonneg_right hC_sq hSU_nonneg
  have hB_nonneg : 0 ≤ C * S * Real.sqrt U :=
    mul_nonneg (mul_nonneg hC_nonneg hS_nonneg) (Real.sqrt_nonneg _)
  apply (sq_le_sq₀ hP_nonneg hB_nonneg).mp
  calc
    (cubeBesovPositiveVectorPartialSeminormTwo Q s.1 N g) ^ 2 ≤ S ^ 2 * U := hbase'
    _ ≤ C ^ 2 * (S ^ 2 * U) := hmiddle
    _ = (C * S * Real.sqrt U) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hU_nonneg]
      ring

/-- Uniform finite-partial bridge, including the `p = 2` endpoint. -/
private theorem partial_le_five_mul_gap_inv_mul_scale_mul_disjoint_root
    {d : ℕ} (Q : TriadicCube d) (s s2 : FractionalOrder)
    (hss2 : s.1 < s2.1) (N : ℕ) (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) ≤ p.exponent) (g : Vec d → Vec d)
    (hg : MeasureTheory.MemLp (fun x => HilbertVec.ofVec (g x)) p.exponent
      (normalizedCubeMeasure Q))
    (hfin : cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g < ∞) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s.1 N g ≤
      (5 * (s2.1 - s.1)⁻¹) * Real.rpow 3 (s2.1 * (Q.scale : ℝ)) *
        Real.rpow (cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g).toReal
          (p.exponent.toReal)⁻¹ := by
  have hr : (2 : ℝ) ≤ p.exponent.toReal :=
    ENNReal.toReal_mono p.lt_top.ne hp
  rcases eq_or_lt_of_le hr with htwo | htwo
  · have hend := partial_le_five_mul_gap_inv_mul_scale_mul_disjoint_sqrt_of_toReal_eq_two
      Q s s2 hss2 N p htwo.symm g hg hfin
    convert hend using 1
    rw [Real.sqrt_eq_rpow, htwo.symm]
    norm_num
  · have hp' : (2 : ℝ≥0∞) < p.exponent := by
      apply (ENNReal.toReal_lt_toReal ENNReal.ofNat_ne_top p.lt_top.ne).mp
      simpa using htwo
    exact partial_le_five_mul_gap_inv_mul_scale_mul_disjoint_root_of_two_lt
      Q s s2 hss2 N p hp' g hg hfin

/-- The source-facing positive-Besov bridge from the legacy finite-`2`
seminorm to the internal disjoint finite-`p` energy.  No boundedness or
summability premise is exposed: the infinite-energy case is discharged in
`ENNReal`, and the finite case uses uniform finite partial bounds. -/
theorem cubeBesovPositiveVectorSeminormTwo_le_five_mul_gap_inv_mul_scale_mul_disjointRoot
    {d : ℕ} (Q : TriadicCube d) (s s2 : FractionalOrder)
    (hss2 : s.1 < s2.1) (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) ≤ p.exponent) (g : Vec d → Vec d)
    (hg : MeasureTheory.MemLp (fun x => HilbertVec.ofVec (g x)) p.exponent
      (normalizedCubeMeasure Q)) :
    ENNReal.ofReal (cubeBesovPositiveVectorSeminormTwo Q s.1 g) ≤
      (5 : ℝ≥0∞) * ENNReal.ofReal ((s2.1 - s.1)⁻¹) *
        ENNReal.ofReal (Real.rpow 3 (s2.1 * (Q.scale : ℝ))) *
        (cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g) ^
          (p.exponent.toReal)⁻¹ := by
  let E : ℝ≥0∞ := cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g
  let r : ℝ := p.exponent.toReal
  have hdelta : 0 < s2.1 - s.1 := by linarith
  have hr : 0 < r := finiteLpExponent_toReal_pos p
  by_cases hfin : E < ∞
  · have hreal : cubeBesovPositiveVectorSeminormTwo Q s.1 g ≤
        (5 * (s2.1 - s.1)⁻¹) * Real.rpow 3 (s2.1 * (Q.scale : ℝ)) *
          Real.rpow E.toReal r⁻¹ := by
      apply cubeBesovPositiveVectorSeminormTwo_le_of_partialBound Q s.1 g
      intro N
      exact partial_le_five_mul_gap_inv_mul_scale_mul_disjoint_root
        Q s s2 hss2 N p hp g hg (by simpa [E] using hfin)
    change ENNReal.ofReal (cubeBesovPositiveVectorSeminormTwo Q s.1 g) ≤
      (5 : ℝ≥0∞) * ENNReal.ofReal ((s2.1 - s.1)⁻¹) *
        ENNReal.ofReal (Real.rpow 3 (s2.1 * (Q.scale : ℝ))) * E ^ r⁻¹
    rw [← ENNReal.ofReal_toReal hfin.ne,
      ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (inv_nonneg.mpr hr.le)]
    rw [show (5 : ℝ≥0∞) = ENNReal.ofReal 5 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5),
      ← ENNReal.ofReal_mul (by positivity)]
    have hfrontreal : 0 ≤ 5 * (s2.1 - s.1)⁻¹ *
        Real.rpow 3 (s2.1 * (Q.scale : ℝ)) :=
      mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr hdelta.le))
        (Real.rpow_nonneg (by norm_num) _)
    rw [← ENNReal.ofReal_mul hfrontreal]
    exact ENNReal.ofReal_le_ofReal hreal
  · have htop : E = ∞ := top_unique (not_lt.mp hfin)
    have hfront : (5 : ℝ≥0∞) * ENNReal.ofReal ((s2.1 - s.1)⁻¹) *
        ENNReal.ofReal (Real.rpow 3 (s2.1 * (Q.scale : ℝ))) ≠ 0 := by
      have hinv : 0 < (s2.1 - s.1)⁻¹ := inv_pos.mpr hdelta
      have hscale : 0 < Real.rpow 3 (s2.1 * (Q.scale : ℝ)) :=
        Real.rpow_pos_of_pos (by norm_num) _
      positivity
    calc
      ENNReal.ofReal (cubeBesovPositiveVectorSeminormTwo Q s.1 g) ≤ ∞ := le_top
      _ = (5 : ℝ≥0∞) * ENNReal.ofReal ((s2.1 - s.1)⁻¹) *
          ENNReal.ofReal (Real.rpow 3 (s2.1 * (Q.scale : ℝ))) *
          (cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g) ^ r⁻¹ := by
            rw [← show E = cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g by rfl,
              htop, ENNReal.top_rpow_of_pos (inv_pos.mpr hr), ENNReal.mul_top hfront]

/-- The finite Euclidean source carrier makes the legacy finite partial
positive-Besov seminorms uniformly bounded.  The finite-energy conclusion is
derived from the source-facing full `W^{s₂,p}` hypothesis, rather than being
silently assumed as a bare `MemLp` consequence. -/
theorem cubeBesovPositiveVectorPartialSeminormTwo_bddAbove_of_memLp_finiteP
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (s s2 : FractionalOrder)
    (hss2 : s.1 < s2.1) (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) ≤ p.exponent) (g : Vec d → Vec d)
    (hgFull : MemCubeEuclideanFullWsp Q s2 p g) :
    BddAbove (Set.range fun N : ℕ =>
      cubeBesovPositiveVectorPartialSeminormTwo Q s.1 N g) := by
  let E : ℝ≥0∞ := cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g
  have hfin : E < ∞ :=
    disjointPowerEnergy_lt_top_of_memCubeEuclideanFullWsp Q s2 p g hgFull
  let B : ℝ := (5 * (s2.1 - s.1)⁻¹) *
    Real.rpow 3 (s2.1 * (Q.scale : ℝ)) *
    Real.rpow E.toReal (p.exponent.toReal)⁻¹
  refine ⟨B, ?_⟩
  rintro z ⟨N, rfl⟩
  exact partial_le_five_mul_gap_inv_mul_scale_mul_disjoint_root
    Q s s2 hss2 N p hp g hgFull.1 (by simpa [E] using hfin)

/-- The sharp strict-`p` finite partial estimate retains the Hölder tail
explicitly.  Unlike the public one-cube bridge above, this is kept internal:
the outer physical-scale summation combines this tail with its own geometric
discount before either loss is simplified. -/
private theorem partial_le_scale_mul_disjoint_root_mul_holderTail_of_two_lt
    {d : ℕ} (Q : TriadicCube d) (s s2 : FractionalOrder)
    (N : ℕ) (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) < p.exponent) (g : Vec d → Vec d)
    (hg : MeasureTheory.MemLp (fun x => HilbertVec.ofVec (g x)) p.exponent
      (normalizedCubeMeasure Q))
    (hfin : cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g < ∞) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s.1 N g ≤
      Real.rpow 3 (s2.1 * (Q.scale : ℝ)) *
        Real.rpow (cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g).toReal
          (p.exponent.toReal)⁻¹ *
        Real.rpow
          (∑ j ∈ Finset.range (N + 1),
            ((Real.rpow 3 (-(s2.1 - s.1) * (j : ℝ))) ^ 2) ^
              (p.exponent.toReal / (p.exponent.toReal - 2)))
          ((p.exponent.toReal - 2) / (2 * p.exponent.toReal)) := by
  let r : ℝ := p.exponent.toReal
  let E : ℝ≥0∞ := cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g
  let S : ℝ := Real.rpow 3 (s2.1 * (Q.scale : ℝ))
  let U : ℝ := E.toReal
  let T : ℝ := ∑ j ∈ Finset.range (N + 1),
    ((Real.rpow 3 (-(s2.1 - s.1) * (j : ℝ))) ^ 2) ^ (r / (r - 2))
  have hr : 2 < r := by
    dsimp [r]
    exact (ENNReal.toReal_lt_toReal ENNReal.ofNat_ne_top p.lt_top.ne).2 hp
  have hrpos : 0 < r := by linarith
  have hS : 0 ≤ S := Real.rpow_nonneg (by norm_num) _
  have hU : 0 ≤ U := ENNReal.toReal_nonneg
  have hT : 0 ≤ T := by
    apply Finset.sum_nonneg
    intro j _
    exact Real.rpow_nonneg (sq_nonneg _) _
  have hP : 0 ≤ cubeBesovPositiveVectorPartialSeminormTwo Q s.1 N g :=
    cubeBesovPositiveVectorPartialSeminormTwo_nonneg Q s.1 N g
  have henergy := finite_noteResidualSum_le_scale_mul_disjointPowerEnergy
    Q s2 N p g hg hfin
  have hpartial := partial_rpow_le_weighted_energy_mul_holder_tail
    Q s s2 N p hp g hg
  have hA :
      ∑ j ∈ Finset.range (N + 1),
        Real.rpow 3 (s2.1 * r * (j : ℝ)) *
          descendantsAverage Q j (fun R =>
            Real.rpow
              ((MeasureTheory.eLpNorm
                (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
                (normalizedCubeMeasure R)).toReal)
              r) ≤ S ^ r * U := by
    rw [show S ^ r = Real.rpow 3 (s2.1 * r * (Q.scale : ℝ)) by
      dsimp [S]
      calc
        (Real.rpow 3 (s2.1 * (Q.scale : ℝ))) ^ r =
            Real.rpow 3 ((s2.1 * (Q.scale : ℝ)) * r) :=
          (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _).symm
        _ = Real.rpow 3 (s2.1 * r * (Q.scale : ℝ)) := by
          congr 1
          ring]
    simpa [U, E, r] using henergy
  have hpower :
      Real.rpow (cubeBesovPositiveVectorPartialSeminormTwo Q s.1 N g) r ≤
        Real.rpow (S * Real.rpow U r⁻¹ * Real.rpow T ((r - 2) / (2 * r))) r := by
    have hprod := mul_le_mul hA (le_refl (Real.rpow T ((r - 2) / 2)))
      (Real.rpow_nonneg hT _) (mul_nonneg (Real.rpow_nonneg hS _) hU)
    calc
      Real.rpow (cubeBesovPositiveVectorPartialSeminormTwo Q s.1 N g) r ≤
          (∑ j ∈ Finset.range (N + 1),
            Real.rpow 3 (s2.1 * r * (j : ℝ)) *
              descendantsAverage Q j (fun R =>
                Real.rpow
                  ((MeasureTheory.eLpNorm
                    (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
                    (normalizedCubeMeasure R)).toReal)
                  r)) * Real.rpow T ((r - 2) / 2) := by
            simpa [T, r] using hpartial
      _ ≤ (S ^ r * U) * Real.rpow T ((r - 2) / 2) := hprod
      _ = Real.rpow (S * Real.rpow U r⁻¹ * Real.rpow T ((r - 2) / (2 * r))) r := by
        symm
        calc
          Real.rpow (S * Real.rpow U r⁻¹ * Real.rpow T ((r - 2) / (2 * r))) r =
              Real.rpow (S * Real.rpow U r⁻¹) r *
                Real.rpow (Real.rpow T ((r - 2) / (2 * r))) r :=
            Real.mul_rpow (mul_nonneg hS (Real.rpow_nonneg hU _))
              (Real.rpow_nonneg hT _)
          _ = (S ^ r * Real.rpow (Real.rpow U r⁻¹) r) *
                Real.rpow (Real.rpow T ((r - 2) / (2 * r))) r := by
              congr 1
              exact Real.mul_rpow hS (Real.rpow_nonneg hU _)
          _ = (S ^ r * U) * Real.rpow T ((r - 2) / 2) := by
              have hUexp : r⁻¹ * r = 1 := inv_mul_cancel₀ hrpos.ne'
              have hTexp : ((r - 2) / (2 * r)) * r = (r - 2) / 2 := by
                field_simp [hrpos.ne']
              have hUcalc : Real.rpow (Real.rpow U r⁻¹) r = U := by
                calc
                  Real.rpow (Real.rpow U r⁻¹) r = Real.rpow U (r⁻¹ * r) :=
                    (Real.rpow_mul hU _ _).symm
                  _ = U := by simp [hUexp]
              have hTcalc : Real.rpow (Real.rpow T ((r - 2) / (2 * r))) r =
                  Real.rpow T ((r - 2) / 2) := by
                calc
                  Real.rpow (Real.rpow T ((r - 2) / (2 * r))) r =
                      Real.rpow T (((r - 2) / (2 * r)) * r) :=
                    (Real.rpow_mul hT _ _).symm
                  _ = Real.rpow T ((r - 2) / 2) := by rw [hTexp]
              rw [hUcalc, hTcalc]
  exact (Real.rpow_le_rpow_iff hP
    (mul_nonneg (mul_nonneg hS (Real.rpow_nonneg hU _))
      (Real.rpow_nonneg hT _)) hrpos).mp hpower

/-- Uniform sharp strict-`p` bridge.  Its tail is deliberately left as the
geometric-discount expression: the forcing assembly later couples it to the
outer physical-scale tail, yielding the frozen single inverse-gap loss. -/
private theorem cubeBesovPositiveVectorSeminormTwo_le_scale_mul_disjoint_root_mul_holderTail_of_two_lt
    {d : ℕ} (Q : TriadicCube d) (s s2 : FractionalOrder)
    (hss2 : s.1 < s2.1) (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) < p.exponent) (g : Vec d → Vec d)
    (hg : MeasureTheory.MemLp (fun x => HilbertVec.ofVec (g x)) p.exponent
      (normalizedCubeMeasure Q))
    (hfin : cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g < ∞) :
    cubeBesovPositiveVectorSeminormTwo Q s.1 g ≤
      Real.rpow 3 (s2.1 * (Q.scale : ℝ)) *
        Real.rpow (cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g).toReal
          (p.exponent.toReal)⁻¹ *
        Real.rpow (Book.Ch02.geometricDiscount (s2.1 - s.1) 1)⁻¹
          ((p.exponent.toReal - 2) / (2 * p.exponent.toReal)) := by
  let r : ℝ := p.exponent.toReal
  let delta : ℝ := s2.1 - s.1
  let D : ℝ := (Book.Ch02.geometricDiscount delta 1)⁻¹
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hdelta_le : delta ≤ 1 := by
    dsimp [delta]
    linarith [s2.2.2, s.2.1]
  have hr : 2 < r := by
    dsimp [r]
    exact (ENNReal.toReal_lt_toReal ENNReal.ofNat_ne_top p.lt_top.ne).2 hp
  have hrpos : 0 < r := by linarith
  have hgamma : 0 ≤ (r - 2) / (2 * r) :=
    div_nonneg (by linarith) (by positivity)
  apply cubeBesovPositiveVectorSeminormTwo_le_of_partialBound Q s.1 g
  intro N
  have hpartial := partial_le_scale_mul_disjoint_root_mul_holderTail_of_two_lt
    Q s s2 N p hp g hg hfin
  have htail :
      ∑ j ∈ Finset.range (N + 1),
        ((Real.rpow 3 (-delta * (j : ℝ))) ^ 2) ^ (r / (r - 2)) ≤ D :=
    finite_holder_weight_le_inv_discount hdelta hr N
  have htailroot := Real.rpow_le_rpow
    (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (sq_nonneg _) _) htail hgamma
  calc
    cubeBesovPositiveVectorPartialSeminormTwo Q s.1 N g ≤
        Real.rpow 3 (s2.1 * (Q.scale : ℝ)) *
          Real.rpow (cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g).toReal r⁻¹ *
          Real.rpow
            (∑ j ∈ Finset.range (N + 1),
              ((Real.rpow 3 (-delta * (j : ℝ))) ^ 2) ^ (r / (r - 2)))
            ((r - 2) / (2 * r)) := by
              simpa [r, delta] using hpartial
    _ ≤ Real.rpow 3 (s2.1 * (Q.scale : ℝ)) *
          Real.rpow (cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g).toReal r⁻¹ *
          Real.rpow D ((r - 2) / (2 * r)) := by
            apply mul_le_mul_of_nonneg_left ?_
              (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
                (Real.rpow_nonneg ENNReal.toReal_nonneg _))
            simpa only [Real.rpow_eq_pow] using htailroot
    _ = Real.rpow 3 (s2.1 * (Q.scale : ℝ)) *
          Real.rpow (cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g).toReal
            (p.exponent.toReal)⁻¹ *
          Real.rpow (Book.Ch02.geometricDiscount (s2.1 - s.1) 1)⁻¹
            ((p.exponent.toReal - 2) / (2 * p.exponent.toReal)) := by
              rfl

/-- A normalized finite descendant average commutes with a nonnegative
countable depth sum.  This is the bookkeeping step used to expose the two
depth indices in the forcing calculation. -/
private theorem descendantsENNAverage_tsum_eq_tsum_descendantsENNAverage
    {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (F : TriadicCube d → ℕ → ℝ≥0∞) :
    descendantsENNAverage Q j (fun R => ∑' n : ℕ, F R n) =
      ∑' n : ℕ, descendantsENNAverage Q j (fun R => F R n) := by
  classical
  unfold descendantsENNAverage
  rw [show (∑ R ∈ descendantsAtDepth Q j, (fun R => ∑' n : ℕ, F R n) R) =
      ∑' n : ℕ, ∑ R ∈ descendantsAtDepth Q j, F R n by
    exact (Summable.tsum_finsetSum (fun R _ => ENNReal.summable)).symm]
  rw [← ENNReal.tsum_mul_left]

/-- The disjoint residual power average composes exactly across two
descendant depths. -/
private theorem descendantsENNAverage_disjointDepthPower_eq_disjointDepthPower_add
    {d : ℕ} (Q : TriadicCube d) (j n : ℕ)
    (p : FiniteLpExponent) (g : Vec d → Vec d) :
    descendantsENNAverage Q j
        (fun R => cubeEuclideanPositiveBesovDisjointDepthPower R p g n) =
      cubeEuclideanPositiveBesovDisjointDepthPower Q p g (j + n) := by
  let F : TriadicCube d → ℝ≥0∞ := fun R =>
    (MeasureTheory.eLpNorm
      (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
      (normalizedCubeMeasure R)) ^ p.exponent.toReal
  have hdepth (R : TriadicCube d) (k : ℕ) :
      cubeEuclideanPositiveBesovDisjointDepthPower R p g k =
        descendantsENNAverage R k F := by
    unfold cubeEuclideanPositiveBesovDisjointDepthPower descendantsENNAverage
    apply congrArg (fun z : ℝ≥0∞ => ((descendantsAtDepth R k).card : ℝ≥0∞)⁻¹ * z)
    exact Finset.sum_attach _ F
  rw [hdepth]
  simp_rw [hdepth]
  exact
    (descendantsENNAverage_add_eq_descendantsENNAverage_descendantsENNAverage
      Q j n F).symm

/-- Flatten the local disjoint energy of all depth-`j` descendants into the
single parent disjoint series.  This is the physical content behind the
two-index forcing sum; no overlap carrier is used here. -/
private theorem descendantsENNAverage_disjointPowerEnergy_eq_parentTail
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (s : FractionalOrder)
    (p : FiniteLpExponent) (g : Vec d → Vec d) :
    descendantsENNAverage Q j
        (fun R => cubeEuclideanPositiveBesovDisjointPowerEnergy R s p g) =
      ∑' n : ℕ,
        ENNReal.ofReal (Real.rpow 3
          (-(s.1 * p.exponent.toReal *
            (((Q.scale - ((j + n : ℕ) : ℤ) : ℤ) : ℝ))))) *
          cubeEuclideanPositiveBesovDisjointDepthPower Q p g (j + n) := by
  let weight : TriadicCube d → ℕ → ℝ≥0∞ := fun R n =>
    ENNReal.ofReal (Real.rpow 3
      (-(s.1 * p.exponent.toReal * (((R.scale - (n : ℤ) : ℤ) : ℝ)))))
  rw [show (fun R => cubeEuclideanPositiveBesovDisjointPowerEnergy R s p g) =
      (fun R => ∑' n : ℕ, weight R n *
        cubeEuclideanPositiveBesovDisjointDepthPower R p g n) by
        funext R
        rfl]
  rw [descendantsENNAverage_tsum_eq_tsum_descendantsENNAverage]
  apply tsum_congr
  intro n
  have hweight : ∀ R ∈ descendantsAtDepth Q j, weight R n = weight Q (j + n) := by
    intro R hR
    dsimp [weight]
    congr 2
    rw [scale_eq_sub_of_mem_descendantsAtDepth hR]
    push_cast
    ring
  calc
    descendantsENNAverage Q j (fun R =>
        weight R n * cubeEuclideanPositiveBesovDisjointDepthPower R p g n) =
        weight Q (j + n) * descendantsENNAverage Q j
          (fun R => cubeEuclideanPositiveBesovDisjointDepthPower R p g n) := by
            unfold descendantsENNAverage
            calc
              ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ *
                  ∑ R ∈ descendantsAtDepth Q j,
                    weight R n * cubeEuclideanPositiveBesovDisjointDepthPower R p g n =
                  ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ *
                    ∑ R ∈ descendantsAtDepth Q j,
                      weight Q (j + n) * cubeEuclideanPositiveBesovDisjointDepthPower R p g n := by
                        congr 1
                        apply Finset.sum_congr rfl
                        intro R hR
                        rw [hweight R hR]
              _ = weight Q (j + n) *
                  (((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ *
                    ∑ R ∈ descendantsAtDepth Q j,
                      cubeEuclideanPositiveBesovDisjointDepthPower R p g n) := by
                        calc
                          ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ *
                              (∑ R ∈ descendantsAtDepth Q j,
                                weight Q (j + n) *
                                  cubeEuclideanPositiveBesovDisjointDepthPower R p g n) =
                              ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ *
                                (weight Q (j + n) *
                                  ∑ R ∈ descendantsAtDepth Q j,
                                    cubeEuclideanPositiveBesovDisjointDepthPower R p g n) := by
                                      rw [← Finset.mul_sum]
                          _ = weight Q (j + n) *
                              (((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ *
                                ∑ R ∈ descendantsAtDepth Q j,
                                  cubeEuclideanPositiveBesovDisjointDepthPower R p g n) := by
                                    ring
    _ = weight Q (j + n) *
        cubeEuclideanPositiveBesovDisjointDepthPower Q p g (j + n) := by
          rw [descendantsENNAverage_disjointDepthPower_eq_disjointDepthPower_add]
    _ = ENNReal.ofReal (Real.rpow 3
          (-(s.1 * p.exponent.toReal *
            (((Q.scale - ((j + n : ℕ) : ℤ) : ℤ) : ℝ))))) *
          cubeEuclideanPositiveBesovDisjointDepthPower Q p g (j + n) := by
            rfl

/-- The sharp local bridge in power form.  The finite source carrier supplies
the needed local finiteness internally, so this statement exposes no local
regularity hypothesis to the eventual forcing theorem. -/
private theorem cubeBesovPositiveVectorSeminormTwo_rpow_le_sharp_local_energy_of_two_lt
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (s s2 : FractionalOrder)
    (hss2 : s.1 < s2.1) (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) < p.exponent) (g : Vec d → Vec d)
    (hg : MemCubeEuclideanFullWsp Q s2 p g) :
    (ENNReal.ofReal (cubeBesovPositiveVectorSeminormTwo Q s.1 g)) ^
        p.exponent.toReal ≤
      (ENNReal.ofReal
        (Real.rpow (Book.Ch02.geometricDiscount (s2.1 - s.1) 1)⁻¹
          ((p.exponent.toReal - 2) / (2 * p.exponent.toReal))) ^
          p.exponent.toReal) *
        ENNReal.ofReal (Real.rpow 3
          (s2.1 * p.exponent.toReal * (Q.scale : ℝ))) *
        cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g := by
  let E : ℝ≥0∞ := cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g
  let r : ℝ := p.exponent.toReal
  let T : ℝ := Real.rpow (Book.Ch02.geometricDiscount (s2.1 - s.1) 1)⁻¹
    ((r - 2) / (2 * r))
  let S : ℝ := Real.rpow 3 (s2.1 * (Q.scale : ℝ))
  let U : ℝ := E.toReal
  have hr : 0 < r := by
    dsimp [r]
    exact finiteLpExponent_toReal_pos p
  have hfin : E < ∞ :=
    disjointPowerEnergy_lt_top_of_memCubeEuclideanFullWsp Q s2 p g hg
  have hB := cubeBesovPositiveVectorSeminormTwo_le_scale_mul_disjoint_root_mul_holderTail_of_two_lt
    Q s s2 hss2 p hp g hg.1 (by simpa [E] using hfin)
  have hS : 0 ≤ S := Real.rpow_nonneg (by norm_num) _
  have hU : 0 ≤ U := ENNReal.toReal_nonneg
  have hT : 0 ≤ T := Real.rpow_nonneg
    (inv_nonneg.mpr (Book.Ch02.book_geometricDiscount_pos (by linarith)).le) _
  have hreal : Real.rpow (S * Real.rpow U r⁻¹ * T) r =
      Real.rpow T r * Real.rpow 3 (s2.1 * r * (Q.scale : ℝ)) * U := by
    have hUcalc : Real.rpow (Real.rpow U r⁻¹) r = U := by
      calc
        Real.rpow (Real.rpow U r⁻¹) r = Real.rpow U (r⁻¹ * r) :=
          (Real.rpow_mul hU _ _).symm
        _ = U := by
          have hmul : r⁻¹ * r = 1 := inv_mul_cancel₀ hr.ne'
          simp [hmul]
    have hScalc : Real.rpow S r =
        Real.rpow 3 (s2.1 * r * (Q.scale : ℝ)) := by
      dsimp [S]
      calc
        Real.rpow (Real.rpow 3 (s2.1 * (Q.scale : ℝ))) r =
            Real.rpow 3 ((s2.1 * (Q.scale : ℝ)) * r) :=
              (Real.rpow_mul (by norm_num) _ _).symm
        _ = Real.rpow 3 (s2.1 * r * (Q.scale : ℝ)) := by
              congr 1
              ring
    calc
      Real.rpow (S * Real.rpow U r⁻¹ * T) r =
          Real.rpow (S * Real.rpow U r⁻¹) r * Real.rpow T r :=
            Real.mul_rpow (mul_nonneg hS (Real.rpow_nonneg hU _)) hT
      _ = (Real.rpow S r * Real.rpow (Real.rpow U r⁻¹) r) * Real.rpow T r := by
            congr 1
            exact Real.mul_rpow hS (Real.rpow_nonneg hU _)
      _ = Real.rpow S r * U * Real.rpow T r := by
            rw [hUcalc]
      _ = Real.rpow T r * Real.rpow 3 (s2.1 * r * (Q.scale : ℝ)) * U := by
            rw [hScalc]
            ring
  have hpower := ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hB) hr.le
  change (ENNReal.ofReal (cubeBesovPositiveVectorSeminormTwo Q s.1 g)) ^ r ≤ _
  calc
    (ENNReal.ofReal (cubeBesovPositiveVectorSeminormTwo Q s.1 g)) ^ r ≤
        (ENNReal.ofReal (S * Real.rpow U r⁻¹ * T)) ^ r := by
          simpa [E, S, T, U, r] using hpower
    _ = ENNReal.ofReal (Real.rpow (S * Real.rpow U r⁻¹ * T) r) :=
      ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (mul_nonneg hS
        (Real.rpow_nonneg hU _)) hT) hr.le
    _ = ENNReal.ofReal (Real.rpow T r *
          Real.rpow 3 (s2.1 * r * (Q.scale : ℝ)) * U) := by rw [hreal]
    _ = (ENNReal.ofReal T ^ r) *
          ENNReal.ofReal (Real.rpow 3 (s2.1 * r * (Q.scale : ℝ))) * E := by
      have hX : 0 ≤ Real.rpow 3 (s2.1 * r * (Q.scale : ℝ)) :=
        Real.rpow_nonneg (by norm_num) _
      have hsplit : ENNReal.ofReal (Real.rpow T r *
          Real.rpow 3 (s2.1 * r * (Q.scale : ℝ)) * U) =
          ENNReal.ofReal (Real.rpow T r) *
            ENNReal.ofReal (Real.rpow 3 (s2.1 * r * (Q.scale : ℝ))) *
              ENNReal.ofReal U := by
        calc
          ENNReal.ofReal (Real.rpow T r *
              Real.rpow 3 (s2.1 * r * (Q.scale : ℝ)) * U) =
              ENNReal.ofReal
                ((Real.rpow T r * Real.rpow 3 (s2.1 * r * (Q.scale : ℝ))) * U) := by
                  congr 1
          _ = ENNReal.ofReal (Real.rpow T r *
                Real.rpow 3 (s2.1 * r * (Q.scale : ℝ))) * ENNReal.ofReal U :=
              ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hT _) hX)
          _ = (ENNReal.ofReal (Real.rpow T r) *
                ENNReal.ofReal (Real.rpow 3 (s2.1 * r * (Q.scale : ℝ)))) *
                ENNReal.ofReal U := by
                  exact congrArg (fun z : ℝ≥0∞ => z * ENNReal.ofReal U)
                    (ENNReal.ofReal_mul (Real.rpow_nonneg hT _))
          _ = ENNReal.ofReal (Real.rpow T r) *
                ENNReal.ofReal (Real.rpow 3 (s2.1 * r * (Q.scale : ℝ))) *
                  ENNReal.ofReal U := by ring
      calc
        ENNReal.ofReal (Real.rpow T r *
            Real.rpow 3 (s2.1 * r * (Q.scale : ℝ)) * U) =
            ENNReal.ofReal (Real.rpow T r) *
              ENNReal.ofReal (Real.rpow 3 (s2.1 * r * (Q.scale : ℝ))) *
                ENNReal.ofReal U := hsplit
        _ = ENNReal.ofReal T ^ r *
              ENNReal.ofReal (Real.rpow 3 (s2.1 * r * (Q.scale : ℝ))) *
                ENNReal.ofReal U := by
                  exact congrArg (fun z : ℝ≥0∞ =>
                    z * ENNReal.ofReal (Real.rpow 3 (s2.1 * r * (Q.scale : ℝ))) *
                      ENNReal.ofReal U)
                    (ENNReal.ofReal_rpow_of_nonneg hT hr.le).symm
        _ = ENNReal.ofReal T ^ r *
              ENNReal.ofReal (Real.rpow 3 (s2.1 * r * (Q.scale : ℝ))) * E := by
                  rw [← ENNReal.ofReal_toReal hfin.ne]

private theorem descendantsENNAverage_mul_left {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (c : ℝ≥0∞) (F : TriadicCube d → ℝ≥0∞) :
    descendantsENNAverage Q j (fun R => c * F R) =
      c * descendantsENNAverage Q j F := by
  unfold descendantsENNAverage
  rw [← Finset.mul_sum]
  ring

/-- One outer physical scale of the strict finite-`p` forcing calculation is
controlled by the sharp local disjoint energy.  The remaining proof sums this
inequality and uses the preceding exact flattening identity. -/
private theorem descendantsAtScale_sharp_local_forcing_power_le_of_two_lt
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (j : ℕ) (s s2 : FractionalOrder) (hss2 : s.1 < s2.1)
    (p : FiniteLpExponent) (hp : (2 : ℝ≥0∞) < p.exponent)
    (g : Vec d → Vec d) (hg : MemCubeEuclideanFullWsp Q s2 p g) :
    descendantsAtScaleENNAverage Q (n - (j : ℤ)) (fun R =>
        (ENNReal.ofReal (cubeBesovPositiveVectorSeminormTwo R s.1 g)) ^
          p.exponent.toReal) ≤
      (ENNReal.ofReal
        (Real.rpow (Book.Ch02.geometricDiscount (s2.1 - s.1) 1)⁻¹
          ((p.exponent.toReal - 2) / (2 * p.exponent.toReal))) ^
          p.exponent.toReal) *
        ENNReal.ofReal (Real.rpow 3
          (s2.1 * p.exponent.toReal * ((n - (j : ℤ) : ℤ) : ℝ))) *
        descendantsAtScaleENNAverage Q (n - (j : ℤ))
          (fun R => cubeEuclideanPositiveBesovDisjointPowerEnergy R s2 p g) := by
  have hnj : n - (j : ℤ) ≤ Q.scale := by omega
  have hpoint : ∀ R ∈ descendantsAtScale Q (n - (j : ℤ)),
      (ENNReal.ofReal (cubeBesovPositiveVectorSeminormTwo R s.1 g)) ^
          p.exponent.toReal ≤
        (ENNReal.ofReal
          (Real.rpow (Book.Ch02.geometricDiscount (s2.1 - s.1) 1)⁻¹
            ((p.exponent.toReal - 2) / (2 * p.exponent.toReal))) ^
            p.exponent.toReal) *
          ENNReal.ofReal (Real.rpow 3
            (s2.1 * p.exponent.toReal * ((n - (j : ℤ) : ℤ) : ℝ))) *
          cubeEuclideanPositiveBesovDisjointPowerEnergy R s2 p g := by
    intro R hRmem
    have hgR := MemCubeEuclideanFullWsp.onDescendant hnj hRmem hg
    have hlocal := cubeBesovPositiveVectorSeminormTwo_rpow_le_sharp_local_energy_of_two_lt
      R s s2 hss2 p hp g hgR
    rw [scale_eq_of_mem_descendantsAtScale hRmem] at hlocal
    exact hlocal
  rw [descendantsAtScaleENNAverage_eq_descendantsENNAverage Q (n - (j : ℤ)) hnj,
    descendantsAtScaleENNAverage_eq_descendantsENNAverage Q (n - (j : ℤ)) hnj]
  calc
    descendantsENNAverage Q (Int.toNat (Q.scale - (n - (j : ℤ)))) (fun R =>
        (ENNReal.ofReal (cubeBesovPositiveVectorSeminormTwo R s.1 g)) ^
          p.exponent.toReal) ≤
        descendantsENNAverage Q (Int.toNat (Q.scale - (n - (j : ℤ)))) (fun R =>
          (ENNReal.ofReal
            (Real.rpow (Book.Ch02.geometricDiscount (s2.1 - s.1) 1)⁻¹
              ((p.exponent.toReal - 2) / (2 * p.exponent.toReal))) ^
              p.exponent.toReal) *
            ENNReal.ofReal (Real.rpow 3
              (s2.1 * p.exponent.toReal * ((n - (j : ℤ) : ℤ) : ℝ))) *
            cubeEuclideanPositiveBesovDisjointPowerEnergy R s2 p g) := by
              unfold descendantsENNAverage
              apply mul_le_mul_right
              apply Finset.sum_le_sum
              intro R hR
              apply hpoint
              rw [descendantsAtScale_eq_descendantsAtDepth Q hnj]
              exact hR
    _ = (ENNReal.ofReal
          (Real.rpow (Book.Ch02.geometricDiscount (s2.1 - s.1) 1)⁻¹
            ((p.exponent.toReal - 2) / (2 * p.exponent.toReal))) ^
            p.exponent.toReal) *
          ENNReal.ofReal (Real.rpow 3
            (s2.1 * p.exponent.toReal * ((n - (j : ℤ) : ℤ) : ℝ))) *
          descendantsENNAverage Q (Int.toNat (Q.scale - (n - (j : ℤ))) )
            (fun R => cubeEuclideanPositiveBesovDisjointPowerEnergy R s2 p g) := by
              rw [show (fun R =>
                (ENNReal.ofReal
                  (Real.rpow (Book.Ch02.geometricDiscount (s2.1 - s.1) 1)⁻¹
                    ((p.exponent.toReal - 2) / (2 * p.exponent.toReal))) ^
                    p.exponent.toReal) *
                  ENNReal.ofReal (Real.rpow 3
                    (s2.1 * p.exponent.toReal * ((n - (j : ℤ) : ℤ) : ℝ))) *
                  cubeEuclideanPositiveBesovDisjointPowerEnergy R s2 p g) =
                (fun R =>
                  ((ENNReal.ofReal
                    (Real.rpow (Book.Ch02.geometricDiscount (s2.1 - s.1) 1)⁻¹
                      ((p.exponent.toReal - 2) / (2 * p.exponent.toReal))) ^
                      p.exponent.toReal) *
                    ENNReal.ofReal (Real.rpow 3
                      (s2.1 * p.exponent.toReal * ((n - (j : ℤ) : ℤ) : ℝ)))) *
                    cubeEuclideanPositiveBesovDisjointPowerEnergy R s2 p g) by
                      funext R
                      ring,
                descendantsENNAverage_mul_left]

/-- A nonnegative shifted tail is bounded by the complete series. -/
private theorem ENNReal_tsum_nat_add_le (E : ℕ → ℝ≥0∞) (j : ℕ) :
    ∑' l : ℕ, E (j + l) ≤ ∑' m : ℕ, E m := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro N
  calc
    ∑ l ∈ Finset.range N, E (j + l) ≤ ∑ m ∈ Finset.range (j + N), E m := by
      rw [Finset.sum_range_add]
      exact le_add_of_nonneg_left bot_le
    _ ≤ ∑' m : ℕ, E m := ENNReal.sum_le_tsum _

/-- The triangular double series arising from local descendant energies is
bounded by the product of its geometric outer tail and its complete parent
energy series. -/
private theorem ENNReal_tsum_mul_shifted_tsum_le
    (w E : ℕ → ℝ≥0∞) :
    ∑' j : ℕ, w j * ∑' l : ℕ, E (j + l) ≤
      (∑' j : ℕ, w j) * ∑' m : ℕ, E m := by
  calc
    ∑' j : ℕ, w j * ∑' l : ℕ, E (j + l) ≤
        ∑' j : ℕ, w j * ∑' m : ℕ, E m := by
          apply ENNReal.tsum_le_tsum
          intro j
          exact mul_le_mul_right (ENNReal_tsum_nat_add_le E j) _
    _ = (∑' j : ℕ, w j) * ∑' m : ℕ, E m := ENNReal.tsum_mul_right

private theorem physicalScaleDepth_add {d : ℕ} (Q : TriadicCube d)
    (n : ℤ) (hn : n ≤ Q.scale) (j : ℕ) :
    Int.toNat (Q.scale - (n - (j : ℤ))) = Int.toNat (Q.scale - n) + j := by
  have h0 : 0 ≤ Q.scale - n := by omega
  have hj : 0 ≤ (j : ℤ) := by positivity
  rw [show Q.scale - (n - (j : ℤ)) = (Q.scale - n) + j by ring,
    Int.toNat_add h0 hj]
  simp

/-- At the Hilbert endpoint the local conversion has no Hölder-tail loss.
This is kept in power form because it is used only in the final two-level
forcing aggregation. -/
private theorem cubeBesovPositiveVectorSeminormTwo_sq_le_scale_sq_mul_disjoint_of_toReal_eq_two
    {d : ℕ} (Q : TriadicCube d) (s s2 : FractionalOrder)
    (hss2 : s.1 < s2.1) (p : FiniteLpExponent)
    (hp2 : p.exponent.toReal = 2) (g : Vec d → Vec d)
    (hg : MeasureTheory.MemLp (fun x => HilbertVec.ofVec (g x)) p.exponent
      (normalizedCubeMeasure Q))
    (hfin : cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g < ∞) :
    (cubeBesovPositiveVectorSeminormTwo Q s.1 g) ^ 2 ≤
      (Real.rpow 3 (s2.1 * (Q.scale : ℝ))) ^ 2 *
        (cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g).toReal := by
  let E : ℝ≥0∞ := cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g
  let S : ℝ := Real.rpow 3 (s2.1 * (Q.scale : ℝ))
  have hS_nonneg : 0 ≤ S := Real.rpow_nonneg (by norm_num) _
  have hE_nonneg : 0 ≤ E.toReal := ENNReal.toReal_nonneg
  have hpartial : ∀ N : ℕ,
      cubeBesovPositiveVectorPartialSeminormTwo Q s.1 N g ≤ S * Real.sqrt E.toReal := by
    intro N
    have hbase := cubeBesovPositiveVectorPartialSeminormTwo_sq_le_eLpNorm_of_toReal_eq_two
      Q s s2 hss2.le N p hp2 g hg
    have henergy := finite_noteResidualSum_le_scale_mul_disjointPowerEnergy
      Q s2 N p g hg hfin
    apply (sq_le_sq₀
      (cubeBesovPositiveVectorPartialSeminormTwo_nonneg Q s.1 N g)
      (mul_nonneg hS_nonneg (Real.sqrt_nonneg _))).mp
    calc
      (cubeBesovPositiveVectorPartialSeminormTwo Q s.1 N g) ^ 2 ≤
          ∑ j ∈ Finset.range (N + 1),
            Real.rpow 3 (s2.1 * 2 * (j : ℝ)) *
              descendantsAverage Q j (fun R =>
                Real.rpow
                  ((MeasureTheory.eLpNorm
                    (fun x => HilbertVec.ofVec (g x - cubeAverageVec R g)) p.exponent
                    (normalizedCubeMeasure R)).toReal) 2) := hbase
      _ ≤ Real.rpow 3 (s2.1 * 2 * (Q.scale : ℝ)) * E.toReal := by
        simpa [hp2, E] using henergy
      _ = (S * Real.sqrt E.toReal) ^ 2 := by
        dsimp [S]
        rw [mul_pow, Real.sq_sqrt hE_nonneg]
        congr 1
        calc
          Real.rpow 3 (s2.1 * 2 * (Q.scale : ℝ)) =
              Real.rpow 3 ((s2.1 * (Q.scale : ℝ)) * 2) := by congr 1; ring
          _ = (Real.rpow 3 (s2.1 * (Q.scale : ℝ))) ^ 2 := by
            calc
              Real.rpow 3 ((s2.1 * (Q.scale : ℝ)) * 2) =
                  Real.rpow (Real.rpow 3 (s2.1 * (Q.scale : ℝ))) (2 : ℝ) :=
                Real.rpow_mul (x := (3 : ℝ)) (by norm_num)
                  (s2.1 * (Q.scale : ℝ)) (2 : ℝ)
              _ = (Real.rpow 3 (s2.1 * (Q.scale : ℝ))) ^ (2 : ℕ) :=
                Real.rpow_natCast _ 2
  have hfull := cubeBesovPositiveVectorSeminormTwo_le_of_partialBound Q s.1 g hpartial
  have hBdd : BddAbove (Set.range fun N : ℕ =>
      cubeBesovPositiveVectorPartialSeminormTwo Q s.1 N g) :=
    ⟨S * Real.sqrt E.toReal, by rintro _ ⟨N, rfl⟩; exact hpartial N⟩
  have hfull_nonneg : 0 ≤ cubeBesovPositiveVectorSeminormTwo Q s.1 g :=
    (cubeBesovPositiveVectorPartialSeminormTwo_nonneg Q s.1 0 g).trans
      (by
        unfold cubeBesovPositiveVectorSeminormTwo
        exact le_csSup hBdd ⟨0, rfl⟩)
  calc
    (cubeBesovPositiveVectorSeminormTwo Q s.1 g) ^ 2 ≤
        (S * Real.sqrt E.toReal) ^ 2 :=
      (sq_le_sq₀ hfull_nonneg (mul_nonneg hS_nonneg (Real.sqrt_nonneg _))).mpr hfull
    _ = S ^ 2 * E.toReal := by rw [mul_pow, Real.sq_sqrt hE_nonneg]

/-- ENNReal power version of the exact Hilbert-endpoint local conversion. -/
private theorem cubeBesovPositiveVectorSeminormTwo_rpow_le_sharp_local_energy_of_toReal_eq_two
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (s s2 : FractionalOrder)
    (hss2 : s.1 < s2.1) (p : FiniteLpExponent)
    (hp2 : p.exponent.toReal = 2) (g : Vec d → Vec d)
    (hg : MemCubeEuclideanFullWsp Q s2 p g) :
    (ENNReal.ofReal (cubeBesovPositiveVectorSeminormTwo Q s.1 g)) ^
        p.exponent.toReal ≤
      ENNReal.ofReal (Real.rpow 3
        (s2.1 * p.exponent.toReal * (Q.scale : ℝ))) *
        cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g := by
  let E : ℝ≥0∞ := cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g
  have hfin : E < ∞ :=
    disjointPowerEnergy_lt_top_of_memCubeEuclideanFullWsp Q s2 p g hg
  have hpENN : (2 : ℝ≥0∞) ≤ p.exponent := by
    apply (ENNReal.toReal_le_toReal ENNReal.ofNat_ne_top p.lt_top.ne).mp
    simp [hp2]
  have hBdd := cubeBesovPositiveVectorPartialSeminormTwo_bddAbove_of_memLp_finiteP
    Q s s2 hss2 p hpENN g hg
  have hfull_nonneg : 0 ≤ cubeBesovPositiveVectorSeminormTwo Q s.1 g :=
    (cubeBesovPositiveVectorPartialSeminormTwo_nonneg Q s.1 0 g).trans
      (by
        unfold cubeBesovPositiveVectorSeminormTwo
        exact le_csSup hBdd ⟨0, rfl⟩)
  have hreal := cubeBesovPositiveVectorSeminormTwo_sq_le_scale_sq_mul_disjoint_of_toReal_eq_two
    Q s s2 hss2 p hp2 g hg.1 (by simp [E, hfin])
  rw [hp2]
  change (ENNReal.ofReal (cubeBesovPositiveVectorSeminormTwo Q s.1 g)) ^ 2 ≤ _
  rw [show (2 : ℝ) = (2 : ℕ) by norm_num, ENNReal.rpow_natCast]
  change (ENNReal.ofReal (cubeBesovPositiveVectorSeminormTwo Q s.1 g)) ^ 2 ≤
    ENNReal.ofReal (Real.rpow 3 (s2.1 * 2 * (Q.scale : ℝ))) * E
  rw [← ENNReal.ofReal_toReal hfin.ne]
  have hscale : 0 ≤ Real.rpow 3 (s2.1 * 2 * (Q.scale : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  rw [← ENNReal.ofReal_mul hscale]
  rw [← ENNReal.ofReal_pow hfull_nonneg 2]
  apply ENNReal.ofReal_le_ofReal
  calc
    (cubeBesovPositiveVectorSeminormTwo Q s.1 g) ^ 2 ≤
        (Real.rpow 3 (s2.1 * (Q.scale : ℝ))) ^ 2 * E.toReal := by
          simpa [E] using hreal
    _ = Real.rpow 3 (s2.1 * 2 * (Q.scale : ℝ)) * E.toReal := by
      congr 1
      calc
        (Real.rpow 3 (s2.1 * (Q.scale : ℝ))) ^ 2 =
            Real.rpow 3 ((s2.1 * (Q.scale : ℝ)) * 2) := by
              calc
                (Real.rpow 3 (s2.1 * (Q.scale : ℝ))) ^ (2 : ℕ) =
                    Real.rpow (Real.rpow 3 (s2.1 * (Q.scale : ℝ))) (2 : ℝ) :=
                  (Real.rpow_natCast _ 2).symm
                _ = Real.rpow 3 ((s2.1 * (Q.scale : ℝ)) * 2) :=
                  (Real.rpow_mul (x := (3 : ℝ)) (by norm_num)
                    (s2.1 * (Q.scale : ℝ)) (2 : ℝ)).symm
        _ = Real.rpow 3 (s2.1 * 2 * (Q.scale : ℝ)) := by congr 1; ring

/-- The endpoint local estimate averaged over one physical outer scale. -/
private theorem descendantsAtScale_sharp_local_forcing_power_le_of_toReal_eq_two
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (j : ℕ) (s s2 : FractionalOrder) (hss2 : s.1 < s2.1)
    (p : FiniteLpExponent) (hp2 : p.exponent.toReal = 2)
    (g : Vec d → Vec d) (hg : MemCubeEuclideanFullWsp Q s2 p g) :
    descendantsAtScaleENNAverage Q (n - (j : ℤ)) (fun R =>
        (ENNReal.ofReal (cubeBesovPositiveVectorSeminormTwo R s.1 g)) ^
          p.exponent.toReal) ≤
      ENNReal.ofReal (Real.rpow 3
          (s2.1 * p.exponent.toReal * ((n - (j : ℤ) : ℤ) : ℝ))) *
        descendantsAtScaleENNAverage Q (n - (j : ℤ))
          (fun R => cubeEuclideanPositiveBesovDisjointPowerEnergy R s2 p g) := by
  have hnj : n - (j : ℤ) ≤ Q.scale := by omega
  have hpoint : ∀ R ∈ descendantsAtScale Q (n - (j : ℤ)),
      (ENNReal.ofReal (cubeBesovPositiveVectorSeminormTwo R s.1 g)) ^
          p.exponent.toReal ≤
        ENNReal.ofReal (Real.rpow 3
          (s2.1 * p.exponent.toReal * ((n - (j : ℤ) : ℤ) : ℝ))) *
          cubeEuclideanPositiveBesovDisjointPowerEnergy R s2 p g := by
    intro R hRmem
    have hgR := MemCubeEuclideanFullWsp.onDescendant hnj hRmem hg
    have hlocal := cubeBesovPositiveVectorSeminormTwo_rpow_le_sharp_local_energy_of_toReal_eq_two
      R s s2 hss2 p hp2 g hgR
    rw [scale_eq_of_mem_descendantsAtScale hRmem] at hlocal
    exact hlocal
  rw [descendantsAtScaleENNAverage_eq_descendantsENNAverage Q (n - (j : ℤ)) hnj,
    descendantsAtScaleENNAverage_eq_descendantsENNAverage Q (n - (j : ℤ)) hnj]
  calc
    descendantsENNAverage Q (Int.toNat (Q.scale - (n - (j : ℤ)))) (fun R =>
        (ENNReal.ofReal (cubeBesovPositiveVectorSeminormTwo R s.1 g)) ^
          p.exponent.toReal) ≤
        descendantsENNAverage Q (Int.toNat (Q.scale - (n - (j : ℤ)))) (fun R =>
          ENNReal.ofReal (Real.rpow 3
            (s2.1 * p.exponent.toReal * ((n - (j : ℤ) : ℤ) : ℝ))) *
            cubeEuclideanPositiveBesovDisjointPowerEnergy R s2 p g) := by
              unfold descendantsENNAverage
              apply mul_le_mul_right
              apply Finset.sum_le_sum
              intro R hR
              apply hpoint
              rw [descendantsAtScale_eq_descendantsAtDepth Q hnj]
              exact hR
    _ = ENNReal.ofReal (Real.rpow 3
          (s2.1 * p.exponent.toReal * ((n - (j : ℤ) : ℤ) : ℝ))) *
        descendantsENNAverage Q (Int.toNat (Q.scale - (n - (j : ℤ))))
          (fun R => cubeEuclideanPositiveBesovDisjointPowerEnergy R s2 p g) := by
            rw [descendantsENNAverage_mul_left]

/-- The retained local Hölder tail and the outer finite-`p` geometric tail
consume at most one inverse fractional gap together.  This is the scalar
estimate which prevents the two-level calculation from paying the gap twice. -/
private theorem sharp_two_level_discount_tail_le_five_mul_inv
    {delta r : ℝ} (hdelta : 0 < delta) (hdelta_le : delta ≤ 1)
    (hr : 2 ≤ r) :
    Real.rpow (Book.Ch02.geometricDiscount delta 1)⁻¹
        ((r - 2) / (2 * r)) *
      Real.rpow (Book.Ch02.geometricDiscount delta r) (-1 / r) ≤
        5 * delta⁻¹ := by
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hrone : 1 ≤ r := le_trans (by norm_num) hr
  let D : ℝ := Book.Ch02.geometricDiscount delta 1
  let Dr : ℝ := Book.Ch02.geometricDiscount delta r
  have hDpos : 0 < D := by
    dsimp [D]
    exact Book.Ch02.book_geometricDiscount_pos (by positivity)
  have hDrpos : 0 < Dr := by
    dsimp [Dr]
    exact Book.Ch02.book_geometricDiscount_pos (mul_pos hdelta hrpos)
  have hDleDr : D ≤ Dr := by
    dsimp [D, Dr, Book.Ch02.geometricDiscount]
    have hp : Real.rpow (3 : ℝ) (-delta * r) ≤ Real.rpow 3 (-delta * 1) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith
    exact sub_le_sub_left hp 1
  have hinv : Dr⁻¹ ≤ D⁻¹ := (inv_le_inv₀ hDrpos hDpos).2 hDleDr
  have houter : Real.rpow Dr (-1 / r) ≤ Real.rpow D⁻¹ (1 / r) := by
    have hrewrite : Real.rpow Dr (-1 / r) = Real.rpow Dr⁻¹ (1 / r) := by
      rw [show (-1 / r : ℝ) = -(1 / r) by ring]
      exact Real.rpow_neg_eq_inv_rpow _ _
    rw [hrewrite]
    exact Real.rpow_le_rpow (inv_nonneg.mpr hDrpos.le) hinv (by positivity)
  have hleft_nonneg : 0 ≤ Real.rpow D⁻¹ ((r - 2) / (2 * r)) :=
    Real.rpow_nonneg (inv_nonneg.mpr hDpos.le) _
  have hmult := mul_le_mul_of_nonneg_left houter hleft_nonneg
  have hexp : (r - 2) / (2 * r) + 1 / r = 1 / 2 := by
    field_simp [hrpos.ne']
    ring
  have hcombine :
      Real.rpow D⁻¹ ((r - 2) / (2 * r)) * Real.rpow D⁻¹ (1 / r) =
        Real.rpow D⁻¹ (1 / 2) := by
    rw [← hexp]
    exact (Real.rpow_add (inv_pos.mpr hDpos) _ _).symm
  have hroot_le : Real.rpow D⁻¹ (1 / 2) ≤ D⁻¹ := by
    have hDinv_one : 1 ≤ D⁻¹ := by
      have hDle : D ≤ 1 := by
        dsimp [D, Book.Ch02.geometricDiscount]
        have hpow : 0 ≤ Real.rpow (3 : ℝ) (-delta * 1) :=
          Real.rpow_nonneg (by norm_num) _
        exact sub_le_self 1 hpow
      exact (one_le_inv₀ hDpos).2 hDle
    calc
      Real.rpow D⁻¹ (1 / 2) ≤ Real.rpow D⁻¹ 1 :=
        Real.rpow_le_rpow_of_exponent_le hDinv_one (by norm_num)
      _ = D⁻¹ := Real.rpow_one _
  calc
    Real.rpow (Book.Ch02.geometricDiscount delta 1)⁻¹
          ((r - 2) / (2 * r)) *
        Real.rpow (Book.Ch02.geometricDiscount delta r) (-1 / r) =
        Real.rpow D⁻¹ ((r - 2) / (2 * r)) * Real.rpow Dr (-1 / r) := by rfl
    _ ≤ Real.rpow D⁻¹ ((r - 2) / (2 * r)) * Real.rpow D⁻¹ (1 / r) := hmult
    _ = Real.rpow D⁻¹ (1 / 2) := hcombine
    _ ≤ D⁻¹ := hroot_le
    _ ≤ 5 * delta⁻¹ := by
      dsimp [D]
      exact Book.Ch02.inv_geometricDiscount_le_five_inv hdelta hdelta_le (by norm_num)

/-- The exact exponent bookkeeping for one outer forcing scale. -/
private theorem outer_forcing_scale_factor_eq
    {s1 s s2 r n : ℝ} (j : ℕ) :
    ENNReal.ofReal (Real.rpow 3 (-(s - s1) * r * (j : ℝ))) *
      ENNReal.ofReal (Real.rpow 3 (s2 * r * (n - (j : ℝ)))) =
      ENNReal.ofReal (Real.rpow 3 (s2 * r * n)) *
        ENNReal.ofReal (Real.rpow 3 (-(s2 + s - s1) * r * (j : ℝ))) := by
  calc
    ENNReal.ofReal (Real.rpow 3 (-(s - s1) * r * (j : ℝ))) *
        ENNReal.ofReal (Real.rpow 3 (s2 * r * (n - (j : ℝ)))) =
        ENNReal.ofReal (Real.rpow 3 (-(s - s1) * r * (j : ℝ)) *
          Real.rpow 3 (s2 * r * (n - (j : ℝ)))) := by
            exact (ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)).symm
    _ = ENNReal.ofReal (Real.rpow 3
          (s2 * r * n + (-(s2 + s - s1) * r * (j : ℝ)))) := by
            congr 1
            rw [show s2 * r * n + (-(s2 + s - s1) * r * (j : ℝ)) =
                (-(s - s1) * r * (j : ℝ)) + s2 * r * (n - (j : ℝ)) by ring]
            simpa [Real.rpow_eq_pow] using
              (Real.rpow_add (x := (3 : ℝ)) (by norm_num)
                (-(s - s1) * r * (j : ℝ)) (s2 * r * (n - (j : ℝ)))).symm
    _ = ENNReal.ofReal (Real.rpow 3 (s2 * r * n) *
          Real.rpow 3 (-(s2 + s - s1) * r * (j : ℝ))) := by
            congr 1
            simpa [Real.rpow_eq_pow] using
              (Real.rpow_add (x := (3 : ℝ)) (by norm_num)
                (s2 * r * n) (-(s2 + s - s1) * r * (j : ℝ)))
    _ = ENNReal.ofReal (Real.rpow 3 (s2 * r * n)) *
      ENNReal.ofReal (Real.rpow 3 (-(s2 + s - s1) * r * (j : ℝ))) :=
      ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)

/-- Physical-scale form of the exact parent-tail flattening. -/
private theorem descendantsAtScale_disjointPowerEnergy_eq_shifted_parentTail
    {d : ℕ} (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (j : ℕ) (s : FractionalOrder) (p : FiniteLpExponent) (g : Vec d → Vec d) :
    descendantsAtScaleENNAverage Q (n - (j : ℤ))
        (fun R => cubeEuclideanPositiveBesovDisjointPowerEnergy R s p g) =
      ∑' l : ℕ,
        ENNReal.ofReal (Real.rpow 3
          (-(s.1 * p.exponent.toReal *
            (((Q.scale - ((Int.toNat (Q.scale - n) + (j + l) : ℕ) : ℤ) : ℤ) : ℝ))))) *
          cubeEuclideanPositiveBesovDisjointDepthPower Q p g
            (Int.toNat (Q.scale - n) + (j + l)) := by
  have hnj : n - (j : ℤ) ≤ Q.scale := by omega
  rw [descendantsAtScaleENNAverage_eq_descendantsENNAverage Q (n - (j : ℤ)) hnj,
    descendantsENNAverage_disjointPowerEnergy_eq_parentTail]
  apply tsum_congr
  intro l
  rw [physicalScaleDepth_add Q n hn j]
  simp only [Nat.add_assoc]

/-- The outer physical-scale tail is no larger than the geometric tail at
the actual fractional gap.  We keep this as an `ENNReal` statement so that
the final forcing proof need not reopen any real-to-extended-real coercions. -/
private theorem forcing_outer_tsum_le_discount
    {delta beta r : ℝ} (hdelta : 0 < delta) (hbeta : delta ≤ beta)
    (hr : 0 < r) :
    ∑' j : ℕ, ENNReal.ofReal (Real.rpow 3 (-beta * r * (j : ℝ))) ≤
      ENNReal.ofReal (Book.Ch02.geometricDiscount delta r)⁻¹ := by
  let x : ℝ≥0∞ := ENNReal.ofReal (Real.rpow 3 (-delta * r))
  have hx_nonneg : 0 ≤ Real.rpow 3 (-delta * r) :=
    Real.rpow_nonneg (by norm_num) _
  have hterm : ∀ j : ℕ,
      ENNReal.ofReal (Real.rpow 3 (-beta * r * (j : ℝ))) ≤ x ^ j := by
    intro j
    have hbase : (1 : ℝ) ≤ 3 := by norm_num
    have hj : 0 ≤ (j : ℝ) := by positivity
    have hexp : -beta * r * (j : ℝ) ≤ (-delta * r) * (j : ℝ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hbeta) (mul_nonneg hr.le hj)]
    have hreal : Real.rpow 3 (-beta * r * (j : ℝ)) ≤
        Real.rpow 3 ((-delta * r) * (j : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hbase hexp
    calc
      ENNReal.ofReal (Real.rpow 3 (-beta * r * (j : ℝ))) ≤
          ENNReal.ofReal (Real.rpow 3 ((-delta * r) * (j : ℝ))) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = x ^ j := by
        have hx : 0 ≤ Real.rpow (3 : ℝ) (-delta * r) :=
          Real.rpow_nonneg (by norm_num) _
        dsimp [x]
        rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
          Real.rpow_natCast]
        change ENNReal.ofReal ((Real.rpow 3 (-delta * r)) ^ j) =
          (ENNReal.ofReal (Real.rpow 3 (-delta * r))) ^ j
        exact ENNReal.ofReal_pow hx j
  calc
    ∑' j : ℕ, ENNReal.ofReal (Real.rpow 3 (-beta * r * (j : ℝ))) ≤
        ∑' j : ℕ, x ^ j := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (Book.Ch02.geometricDiscount delta r)⁻¹ := by
      rw [ENNReal.tsum_geometric]
      have hdisc : 0 < Book.Ch02.geometricDiscount delta r :=
        Book.Ch02.book_geometricDiscount_pos (mul_pos hdelta hr)
      rw [ENNReal.ofReal_inv_of_pos hdisc]
      congr 1
      simpa [x, Book.Ch02.geometricDiscount] using
        (ENNReal.ofReal_sub 1 hx_nonneg).symm

/-- Root the four nonnegative factors produced by the outer forcing series.
The first two already occur at the finite exponent, while the last two are
the geometric tail and the complete parent energy. -/
private theorem ENNReal_rpow_four_factor
    {A S T E : ℝ≥0∞} {r : ℝ} (hr : 0 < r) :
    (A ^ r * S ^ r * T * E) ^ r⁻¹ =
      A * S * T ^ r⁻¹ * E ^ r⁻¹ := by
  rw [show A ^ r * S ^ r * T * E = (A ^ r) * (S ^ r) * T * E by ring,
    ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hr.le),
    ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hr.le),
    ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hr.le)]
  rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    mul_inv_cancel₀ hr.ne', ENNReal.rpow_one]
  simp only [ENNReal.rpow_one]

/-- Assemble a one-level sharp forcing estimate over all physical scales.
The hypotheses deliberately expose only the internal retained-tail factor
`A`; the public theorem below supplies it in the strict and endpoint cases. -/
private theorem localCoarseGrainingForcingLp_le_of_sharp_local
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (s1 s s2 : FractionalOrder) (hs1s : s1.1 < s.1) (hss2 : s.1 < s2.1)
    (p : FiniteLpExponent) (hp : (2 : ℝ≥0∞) ≤ p.exponent)
    (g : Vec d → Vec d)
    (A : ℝ≥0∞)
    (hlocal : ∀ j : ℕ,
      descendantsAtScaleENNAverage Q (n - (j : ℤ)) (fun R =>
          (ENNReal.ofReal (cubeBesovPositiveVectorSeminormTwo R s.1 g)) ^
            p.exponent.toReal) ≤
        A ^ p.exponent.toReal *
          ENNReal.ofReal (Real.rpow 3
            (s2.1 * p.exponent.toReal * ((n - (j : ℤ) : ℤ) : ℝ))) *
          descendantsAtScaleENNAverage Q (n - (j : ℤ))
            (fun R => cubeEuclideanPositiveBesovDisjointPowerEnergy R s2 p g))
    (hA : A * ENNReal.ofReal
        (Real.rpow (Book.Ch02.geometricDiscount (s2.1 - s.1)
          p.exponent.toReal) (-1 / p.exponent.toReal)) ≤
        ENNReal.ofReal (5 * (s2.1 - s.1)⁻¹)) :
    localCoarseGrainingForcingLp Q n s1 s p g ≤
      (5 : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) *
        ENNReal.ofReal ((s2.1 - s.1)⁻¹) *
        ENNReal.ofReal (Real.rpow 3 (s2.1 * (n : ℝ))) *
        cubeEuclideanPositiveBesovOverlapESeminorm Q s2 p g := by
  let r : ℝ := p.exponent.toReal
  let delta : ℝ := s2.1 - s.1
  let beta : ℝ := s2.1 + s.1 - s1.1
  let S : ℝ≥0∞ := ENNReal.ofReal (Real.rpow 3 (s2.1 * (n : ℝ)))
  let E : ℝ≥0∞ := cubeEuclideanPositiveBesovDisjointPowerEnergy Q s2 p g
  let w : ℕ → ℝ≥0∞ := fun j =>
    ENNReal.ofReal (Real.rpow 3 (-beta * r * (j : ℝ)))
  let D : ℝ := Book.Ch02.geometricDiscount delta r
  have hr : 0 < r := finiteLpExponent_toReal_pos p
  have hr_two : 2 ≤ r := by
    dsimp [r]
    exact ENNReal.toReal_mono p.lt_top.ne hp
  have hdelta : 0 < delta := by
    dsimp [delta]
    linarith
  have hdelta_le : delta ≤ 1 := by
    dsimp [delta]
    have hs2_lt : s2.1 < 1 := s2.2.2
    have hs_nonneg : 0 ≤ s.1 := le_of_lt s.2.1
    linarith
  have hbeta : delta ≤ beta := by
    dsimp [delta, beta]
    have hspos : 0 < s.1 := s.2.1
    linarith
  have hDpos : 0 < D := by
    dsimp [D]
    exact Book.Ch02.book_geometricDiscount_pos (mul_pos hdelta hr)
  have htail : ∑' j : ℕ, w j ≤ ENNReal.ofReal D⁻¹ := by
    dsimp [w, D]
    exact forcing_outer_tsum_le_discount hdelta hbeta hr
  have htail_root : (∑' j : ℕ, w j) ^ r⁻¹ ≤
      ENNReal.ofReal (Real.rpow D (-1 / r)) := by
    calc
      (∑' j : ℕ, w j) ^ r⁻¹ ≤ (ENNReal.ofReal D⁻¹) ^ r⁻¹ :=
        ENNReal.rpow_le_rpow htail (inv_nonneg.mpr hr.le)
      _ = ENNReal.ofReal (Real.rpow D (-1 / r)) := by
        rw [ENNReal.ofReal_rpow_of_pos (inv_pos.mpr hDpos)]
        congr 1
        calc
          Real.rpow D⁻¹ r⁻¹ = Real.rpow (Real.rpow D (-1)) r⁻¹ := by
            congr 1
            exact (Real.rpow_neg_one D).symm
          _ = Real.rpow D ((-1 : ℝ) * r⁻¹) :=
            (Real.rpow_mul hDpos.le _ _).symm
          _ = Real.rpow D (-1 / r) := by
            congr 1
  have hlocal' : ∀ j : ℕ,
      descendantsAtScaleENNAverage Q (n - (j : ℤ)) (fun R =>
          (ENNReal.ofReal (cubeBesovPositiveVectorSeminormTwo R s.1 g)) ^ r) ≤
        A ^ r *
          ENNReal.ofReal (Real.rpow 3 (s2.1 * r * ((n : ℝ) - (j : ℝ)))) *
          descendantsAtScaleENNAverage Q (n - (j : ℤ))
            (fun R => cubeEuclideanPositiveBesovDisjointPowerEnergy R s2 p g) := by
    intro j
    simpa only [r, Int.cast_sub, Int.cast_natCast] using hlocal j
  have hS : S ^ r = ENNReal.ofReal (Real.rpow 3 (s2.1 * r * (n : ℝ))) := by
    dsimp [S]
    rw [ENNReal.ofReal_rpow_of_nonneg
      (Real.rpow_nonneg (by norm_num) _) hr.le]
    congr 1
    calc
      Real.rpow (Real.rpow 3 (s2.1 * (n : ℝ))) r =
          Real.rpow 3 ((s2.1 * (n : ℝ)) * r) :=
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _).symm
      _ = Real.rpow 3 (s2.1 * r * (n : ℝ)) := by
        congr 1
        ring
  let h0 : ℕ := Int.toNat (Q.scale - n)
  let G : ℕ → ℝ≥0∞ := fun m =>
    ENNReal.ofReal (Real.rpow 3
      (-(s2.1 * r * (((Q.scale - ((m : ℕ) : ℤ) : ℤ) : ℝ))))) *
      cubeEuclideanPositiveBesovDisjointDepthPower Q p g m
  let F : ℕ → ℝ≥0∞ := fun m => G (h0 + m)
  have hparent (j : ℕ) :
      descendantsAtScaleENNAverage Q (n - (j : ℤ))
        (fun R => cubeEuclideanPositiveBesovDisjointPowerEnergy R s2 p g) =
      ∑' l : ℕ, F (j + l) := by
    rw [descendantsAtScale_disjointPowerEnergy_eq_shifted_parentTail Q n hn j s2 p g]
  have hF_tail : ∑' m : ℕ, F m ≤ E := by
    calc
      ∑' m : ℕ, F m = ∑' m : ℕ, G (h0 + m) := by rfl
      _ ≤ ∑' m : ℕ, G m := ENNReal_tsum_nat_add_le G h0
      _ = E := by
        dsimp [G, E]
        rfl
  have hseries :
      ∑' j : ℕ, w j *
        descendantsAtScaleENNAverage Q (n - (j : ℤ))
          (fun R => cubeEuclideanPositiveBesovDisjointPowerEnergy R s2 p g) ≤
        (∑' j : ℕ, w j) * E := by
    calc
      ∑' j : ℕ, w j *
          descendantsAtScaleENNAverage Q (n - (j : ℤ))
            (fun R => cubeEuclideanPositiveBesovDisjointPowerEnergy R s2 p g) =
          ∑' j : ℕ, w j * ∑' l : ℕ, F (j + l) := by
            apply tsum_congr
            intro j
            rw [hparent]
      _ ≤ (∑' j : ℕ, w j) * ∑' m : ℕ, F m :=
        ENNReal_tsum_mul_shifted_tsum_le w F
      _ ≤ (∑' j : ℕ, w j) * E :=
        mul_le_mul_right hF_tail _
  have hpower : localCoarseGrainingForcingPowerEnergy Q n s1 s p g ≤
      A ^ r * S ^ r * (∑' j : ℕ, w j) * E := by
    unfold localCoarseGrainingForcingPowerEnergy
    calc
      ∑' j : ℕ, ENNReal.ofReal
          (Real.rpow 3 (-(s.1 - s1.1) * r * (j : ℝ))) *
          descendantsAtScaleENNAverage Q (n - (j : ℤ)) (fun R =>
            (ENNReal.ofReal (cubeBesovPositiveVectorSeminormTwo R s.1 g)) ^ r) ≤
          ∑' j : ℕ, ENNReal.ofReal
            (Real.rpow 3 (-(s.1 - s1.1) * r * (j : ℝ))) *
            (A ^ r * ENNReal.ofReal
              (Real.rpow 3 (s2.1 * r * ((n : ℝ) - (j : ℝ)))) *
              descendantsAtScaleENNAverage Q (n - (j : ℤ))
                (fun R => cubeEuclideanPositiveBesovDisjointPowerEnergy R s2 p g)) := by
              apply ENNReal.tsum_le_tsum
              intro j
              exact mul_le_mul_right (hlocal' j) _
      _ = ∑' j : ℕ, A ^ r * S ^ r * w j *
          descendantsAtScaleENNAverage Q (n - (j : ℤ))
            (fun R => cubeEuclideanPositiveBesovDisjointPowerEnergy R s2 p g) := by
              apply tsum_congr
              intro j
              calc
                _ = A ^ r *
                    (ENNReal.ofReal (Real.rpow 3
                      (-(s.1 - s1.1) * r * (j : ℝ))) *
                    ENNReal.ofReal (Real.rpow 3
                      (s2.1 * r * ((n : ℝ) - (j : ℝ))))) *
                    descendantsAtScaleENNAverage Q (n - (j : ℤ))
                      (fun R => cubeEuclideanPositiveBesovDisjointPowerEnergy R s2 p g) := by
                        ring
                _ = A ^ r *
                    (ENNReal.ofReal (Real.rpow 3 (s2.1 * r * (n : ℝ))) * w j) *
                    descendantsAtScaleENNAverage Q (n - (j : ℤ))
                      (fun R => cubeEuclideanPositiveBesovDisjointPowerEnergy R s2 p g) := by
                        rw [outer_forcing_scale_factor_eq (s1 := s1.1) (s := s.1)
                          (s2 := s2.1) (r := r) (n := (n : ℝ)) j]
                _ = A ^ r * S ^ r * w j *
                    descendantsAtScaleENNAverage Q (n - (j : ℤ))
                      (fun R => cubeEuclideanPositiveBesovDisjointPowerEnergy R s2 p g) := by
                        rw [← hS]
                        ring
      _ = A ^ r * S ^ r * ∑' j : ℕ, w j *
          descendantsAtScaleENNAverage Q (n - (j : ℤ))
            (fun R => cubeEuclideanPositiveBesovDisjointPowerEnergy R s2 p g) := by
              rw [show (fun j : ℕ =>
                A ^ r * S ^ r * w j *
                  descendantsAtScaleENNAverage Q (n - (j : ℤ))
                    (fun R => cubeEuclideanPositiveBesovDisjointPowerEnergy R s2 p g)) =
                  (fun j : ℕ => A ^ r * S ^ r *
                    (w j * descendantsAtScaleENNAverage Q (n - (j : ℤ))
                      (fun R => cubeEuclideanPositiveBesovDisjointPowerEnergy R s2 p g))) by
                        funext j
                        ring,
                ENNReal.tsum_mul_left]
      _ ≤ A ^ r * S ^ r * ((∑' j : ℕ, w j) * E) := by
              calc
                A ^ r * S ^ r * ∑' j : ℕ, w j *
                    descendantsAtScaleENNAverage Q (n - (j : ℤ))
                      (fun R => cubeEuclideanPositiveBesovDisjointPowerEnergy R s2 p g) =
                    (A ^ r * S ^ r) *
                      (∑' j : ℕ, w j *
                        descendantsAtScaleENNAverage Q (n - (j : ℤ))
                          (fun R => cubeEuclideanPositiveBesovDisjointPowerEnergy R s2 p g)) := by
                            ring
                _ ≤ (A ^ r * S ^ r) * ((∑' j : ℕ, w j) * E) :=
                  mul_le_mul_right hseries _
                _ = A ^ r * S ^ r * ((∑' j : ℕ, w j) * E) := by ring
      _ = A ^ r * S ^ r * (∑' j : ℕ, w j) * E := by ring
  have hroot := ENNReal.rpow_le_rpow hpower (inv_nonneg.mpr hr.le)
  have hLp : localCoarseGrainingForcingLp Q n s1 s p g ^ r =
      localCoarseGrainingForcingPowerEnergy Q n s1 s p g := by
    simpa only [r] using localCoarseGrainingForcingLp_rpow_eq_powerEnergy Q n s1 s p g
  rw [← hLp, ← ENNReal.rpow_mul, mul_inv_cancel₀ hr.ne', ENNReal.rpow_one] at hroot
  rw [ENNReal_rpow_four_factor hr] at hroot
  have hAE : A * (∑' j : ℕ, w j) ^ r⁻¹ ≤
      ENNReal.ofReal (5 * delta⁻¹) := by
    calc
      A * (∑' j : ℕ, w j) ^ r⁻¹ ≤
          A * ENNReal.ofReal (Real.rpow D (-1 / r)) :=
        mul_le_mul_right htail_root _
      _ ≤ ENNReal.ofReal (5 * delta⁻¹) := by
        simpa only [delta, r, D] using hA
  have hEroot := cubeEuclideanPositiveBesovDisjointPowerEnergy_root_le_overlap
    Q s2 p hp g
  calc
    localCoarseGrainingForcingLp Q n s1 s p g ≤
        A * S * (∑' j : ℕ, w j) ^ r⁻¹ * E ^ r⁻¹ := hroot
    _ = (A * (∑' j : ℕ, w j) ^ r⁻¹) * S * E ^ r⁻¹ := by
      ac_rfl
    _ ≤ ENNReal.ofReal (5 * delta⁻¹) * S * E ^ r⁻¹ := by
      gcongr
    _ ≤ ENNReal.ofReal (5 * delta⁻¹) * S *
        ((3 ^ d : ℝ≥0∞) * cubeEuclideanPositiveBesovOverlapESeminorm Q s2 p g) := by
      gcongr
    _ = (5 : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) *
        ENNReal.ofReal (delta⁻¹) * S *
        cubeEuclideanPositiveBesovOverlapESeminorm Q s2 p g := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)]
      rw [ENNReal.ofReal_ofNat 5]
      norm_num
      ac_rfl
    _ = (5 : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) *
        ENNReal.ofReal ((s2.1 - s.1)⁻¹) *
        ENNReal.ofReal (Real.rpow 3 (s2.1 * (n : ℝ))) *
        cubeEuclideanPositiveBesovOverlapESeminorm Q s2 p g := by
      rfl

/-- The global finite-`p` forcing aggregation has exactly one inverse
fractional gap.  The calculation is internalized through disjoint descendant
energies, then returned to the source-facing exact-overlap seminorm. -/
theorem localCoarseGrainingForcingLp_le_five_mul_gap_inv_mul_scale_mul_overlap
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (s1 s s2 : FractionalOrder) (hs1s : s1.1 < s.1) (hss2 : s.1 < s2.1)
    (p : FiniteLpExponent) (hp : (2 : ℝ≥0∞) ≤ p.exponent)
    (g : Vec d → Vec d) (hg : MemCubeEuclideanFullWsp Q s2 p g) :
    localCoarseGrainingForcingLp Q n s1 s p g ≤
      (5 : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) *
        ENNReal.ofReal ((s2.1 - s.1)⁻¹) *
        ENNReal.ofReal (Real.rpow 3 (s2.1 * (n : ℝ))) *
        cubeEuclideanPositiveBesovOverlapESeminorm Q s2 p g := by
  let r : ℝ := p.exponent.toReal
  let delta : ℝ := s2.1 - s.1
  have hr : (2 : ℝ) ≤ r := by
    dsimp [r]
    exact ENNReal.toReal_mono p.lt_top.ne hp
  have hdelta : 0 < delta := by
    dsimp [delta]
    linarith
  have hdelta_le : delta ≤ 1 := by
    dsimp [delta]
    have hs2_lt : s2.1 < 1 := s2.2.2
    have hs_nonneg : 0 ≤ s.1 := le_of_lt s.2.1
    linarith
  rcases eq_or_lt_of_le hr with htwo | htwo
  · have hlocal : ∀ j : ℕ,
        descendantsAtScaleENNAverage Q (n - (j : ℤ)) (fun R =>
            (ENNReal.ofReal (cubeBesovPositiveVectorSeminormTwo R s.1 g)) ^
              p.exponent.toReal) ≤
          (1 : ℝ≥0∞) ^ p.exponent.toReal *
            ENNReal.ofReal (Real.rpow 3
              (s2.1 * p.exponent.toReal * ((n - (j : ℤ) : ℤ) : ℝ))) *
            descendantsAtScaleENNAverage Q (n - (j : ℤ))
              (fun R => cubeEuclideanPositiveBesovDisjointPowerEnergy R s2 p g) := by
      intro j
      simpa using descendantsAtScale_sharp_local_forcing_power_le_of_toReal_eq_two
        Q n hn j s s2 hss2 p htwo.symm g hg
    have hscalar := sharp_two_level_discount_tail_le_five_mul_inv
      hdelta hdelta_le hr
    have hA : (1 : ℝ≥0∞) * ENNReal.ofReal
        (Real.rpow (Book.Ch02.geometricDiscount delta r) (-1 / r)) ≤
        ENNReal.ofReal (5 * delta⁻¹) := by
      rw [one_mul]
      apply ENNReal.ofReal_le_ofReal
      simpa [htwo.symm] using hscalar
    simpa only [delta, r] using
      localCoarseGrainingForcingLp_le_of_sharp_local Q n hn s1 s s2 hs1s hss2
        p hp g 1 hlocal hA
  · have hp' : (2 : ℝ≥0∞) < p.exponent := by
      apply (ENNReal.toReal_lt_toReal ENNReal.ofNat_ne_top p.lt_top.ne).mp
      simpa [r] using htwo
    let A : ℝ≥0∞ := ENNReal.ofReal
      (Real.rpow (Book.Ch02.geometricDiscount delta 1)⁻¹
        ((r - 2) / (2 * r)))
    have hlocal : ∀ j : ℕ,
        descendantsAtScaleENNAverage Q (n - (j : ℤ)) (fun R =>
            (ENNReal.ofReal (cubeBesovPositiveVectorSeminormTwo R s.1 g)) ^
              p.exponent.toReal) ≤
          A ^ p.exponent.toReal *
            ENNReal.ofReal (Real.rpow 3
              (s2.1 * p.exponent.toReal * ((n - (j : ℤ) : ℤ) : ℝ))) *
            descendantsAtScaleENNAverage Q (n - (j : ℤ))
              (fun R => cubeEuclideanPositiveBesovDisjointPowerEnergy R s2 p g) := by
      intro j
      simpa only [A, delta, r] using
        descendantsAtScale_sharp_local_forcing_power_le_of_two_lt
          Q n hn j s s2 hss2 p hp' g hg
    have hscalar := sharp_two_level_discount_tail_le_five_mul_inv
      hdelta hdelta_le hr
    have hA : A * ENNReal.ofReal
        (Real.rpow (Book.Ch02.geometricDiscount delta r) (-1 / r)) ≤
        ENNReal.ofReal (5 * delta⁻¹) := by
      change ENNReal.ofReal
          (Real.rpow (Book.Ch02.geometricDiscount delta 1)⁻¹
            ((r - 2) / (2 * r))) * ENNReal.ofReal
          (Real.rpow (Book.Ch02.geometricDiscount delta r) (-1 / r)) ≤ _
      have hbase : 0 ≤ (Book.Ch02.geometricDiscount delta 1)⁻¹ :=
        inv_nonneg.mpr (Book.Ch02.book_geometricDiscount_pos
          (mul_pos hdelta (by positivity))).le
      have hx : 0 ≤ Real.rpow (Book.Ch02.geometricDiscount delta 1)⁻¹
          ((r - 2) / (2 * r)) := Real.rpow_nonneg hbase _
      rw [← ENNReal.ofReal_mul hx]
      exact ENNReal.ofReal_le_ofReal hscalar
    simpa only [delta, r] using
      localCoarseGrainingForcingLp_le_of_sharp_local Q n hn s1 s s2 hs1s hss2
        p hp g A hlocal hA




end

end ABK26
end Ch03
end Book
end Homogenization
