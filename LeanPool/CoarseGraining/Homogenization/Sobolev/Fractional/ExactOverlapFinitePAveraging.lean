/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.AveragingGradient
public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.AveragingGradientExplicit
public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.AveragingResidual
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ConvexApproxGagliardoSmoothing
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ExactOverlapEuclideanLpComparison
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.CubeVector

/-!
# Finite-`p` synchronized overlap averaging

This module packages the concrete smooth overlap average simultaneously as an
`H¹` and a finite-`W¹ᵖ` vector field.  The two witnesses have literally the
same field and the same coordinate derivative matrix.  The remaining
one-depth estimates are stated against the direct Euclidean overlap energy,
so later Calderón--Zygmund interpolation can use them without introducing a
separate `K`-functional carrier.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The rooted direct Euclidean overlap energy at one depth.  Its `p`-th
power is exactly the unweighted `j` summand in
`cubeEuclideanPositiveBesovOverlapESeminorm`. -/
noncomputable def cubeEuclideanPositiveBesovOverlapDepthENorm {d : ℕ}
    (Q : TriadicCube d) (p : FiniteLpExponent) (F : Vec d → Vec d) (j : ℕ) : ℝ≥0∞ :=
  (((ScalarOverlap.centersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
    (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S =>
      (eLpNorm
        (fun x => HilbertVec.ofVec (F x - ScalarOverlap.cubeAverageVec S.1 F))
        p.exponent (ScalarOverlap.normalizedCubeMeasure S.1)) ^ p.exponent.toReal)) ^
    (p.exponent.toReal)⁻¹

/-- Nonnegativity of the rooted one-depth Euclidean overlap energy. -/
theorem cubeEuclideanPositiveBesovOverlapDepthENorm_nonneg {d : ℕ}
    (Q : TriadicCube d) (p : FiniteLpExponent) (F : Vec d → Vec d) (j : ℕ) :
    0 ≤ cubeEuclideanPositiveBesovOverlapDepthENorm Q p F j :=
  bot_le

/-- Raising the rooted depth energy to `p` recovers its unrooted finite
overlap average exactly. -/
theorem cubeEuclideanPositiveBesovOverlapDepthENorm_rpow {d : ℕ}
    (Q : TriadicCube d) (p : FiniteLpExponent) (F : Vec d → Vec d) (j : ℕ) :
    (cubeEuclideanPositiveBesovOverlapDepthENorm Q p F j) ^ p.exponent.toReal =
      ((ScalarOverlap.centersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
        (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S =>
          (eLpNorm
            (fun x => HilbertVec.ofVec (F x - ScalarOverlap.cubeAverageVec S.1 F))
            p.exponent (ScalarOverlap.normalizedCubeMeasure S.1)) ^ p.exponent.toReal) := by
  unfold cubeEuclideanPositiveBesovOverlapDepthENorm
  rw [ENNReal.rpow_inv_rpow]
  exact ENNReal.toReal_pos (zero_lt_one.trans p.one_lt).ne' p.lt_top.ne |>.ne'

/-- The complete overlap energy is the weighted sum of the rooted depth
energies.  This is the precise connection used by the later one-level
Calderón--Zygmund estimate. -/
theorem cubeEuclideanPositiveBesovOverlapPowerEnergy_eq_tsum_depthENorm {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : Vec d → Vec d) :
    cubeEuclideanPositiveBesovOverlapPowerEnergy Q s p F =
      ∑' j : ℕ,
        ENNReal.ofReal
            (Real.rpow 3
              (-(s.1 * p.exponent.toReal *
                (((Q.scale - (j : ℤ) : ℤ) : ℝ))))) *
          (cubeEuclideanPositiveBesovOverlapDepthENorm Q p F j) ^
            p.exponent.toReal := by
  unfold cubeEuclideanPositiveBesovOverlapPowerEnergy
  apply tsum_congr
  intro j
  rw [cubeEuclideanPositiveBesovOverlapDepthENorm_rpow]
  rw [mul_assoc]

/-- The powered overlap fluctuation is measurable on the parent cube whenever
the input has the corresponding local finite-`p` membership. -/
private theorem aemeasurable_overlapCubeHilbertResidualIndicator_of_memLp
    {d : ℕ} {Q S : TriadicCube d} {j : ℕ} {h : Vec d → Vec d}
    (p : FiniteLpExponent) (hS : S ∈ ScalarOverlap.centersAtDepth Q j)
    (hh : MemLp (fun y => HilbertVec.ofVec (h y)) p.exponent
      (ScalarOverlap.normalizedCubeMeasure S)) :
    AEMeasurable
      ((ScalarOverlap.cubeSet S).indicator
        (fun y : Vec d =>
          ‖HilbertVec.ofVec (h y - ScalarOverlap.cubeAverageVec S h)‖ₑ ^
            p.exponent.toReal))
      (volume.restrict (cubeSet Q)) := by
  let μS : Measure (Vec d) := volume.restrict (ScalarOverlap.cubeSet S)
  have hcoeff : ENNReal.ofReal ((ScalarOverlap.cubeVolume S)⁻¹) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.2
      (inv_pos.mpr (ScalarOverlap.cubeVolume_pos S))
  have hh_vol : AEMeasurable (fun y => HilbertVec.ofVec (h y)) μS := by
    have hh_norm : AEMeasurable (fun y => HilbertVec.ofVec (h y))
        (ScalarOverlap.normalizedCubeMeasure S) :=
      hh.1.aemeasurable
    simpa [μS, ScalarOverlap.normalizedCubeMeasure, ScalarOverlap.cubeMeasure] using
      (aemeasurable_smul_measure_iff
        (μ := volume.restrict (ScalarOverlap.cubeSet S))
        (f := fun y => HilbertVec.ofVec (h y)) hcoeff).1 hh_norm
  have hmap : Measurable (fun v : HilbertVec d =>
      ‖v - HilbertVec.ofVec (ScalarOverlap.cubeAverageVec S h)‖ₑ ^
        p.exponent.toReal) := by
    fun_prop
  have hbase : AEMeasurable
      (fun y : Vec d =>
        ‖HilbertVec.ofVec (h y - ScalarOverlap.cubeAverageVec S h)‖ₑ ^
          p.exponent.toReal) μS := by
    simpa only [map_sub] using! hmap.comp_aemeasurable hh_vol
  have hsubset : ScalarOverlap.cubeSet S ⊆ cubeSet Q :=
    ScalarOverlap.cubeSet_subset_cubeSet_of_mem_centersAtDepth hS
  refine (aemeasurable_indicator_iff (ScalarOverlap.measurableSet_cubeSet S)).2 ?_
  rwa [Measure.restrict_restrict_of_subset hsubset]

/-- The finite concave power-sum estimate used only in the subquadratic branch
of the private square-lift argument. -/
private theorem ennreal_rpow_finset_sum_le_sum_rpow {ι : Type*}
    (s : Finset ι) (a : ι → ℝ≥0∞) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (s.sum a) ^ r ≤ s.sum (fun i => (a i) ^ r) := by
  induction s using Finset.cons_induction with
  | empty =>
      simp only [Finset.sum_empty, ENNReal.zero_rpow_of_pos hr0]
      exact le_rfl
  | cons x s hx ih =>
      rw [Finset.sum_cons, Finset.sum_cons]
      calc
        (a x + s.sum a) ^ r ≤ (a x) ^ r + (s.sum a) ^ r :=
          ENNReal.rpow_add_le_add_rpow _ _ hr0.le hr1
        _ ≤ (a x) ^ r + s.sum (fun i => (a i) ^ r) :=
          by simpa [add_comm] using add_le_add_left ih ((a x) ^ r)

private theorem enorm_sq_eq_ofReal_sq (z : ℝ) :
    ‖z‖ₑ ^ (2 : ℕ) = ENNReal.ofReal (z ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg z), sq_abs]

private theorem hilbertMat_norm_sq_eq_sum_sq {d : ℕ} (A : HilbertMat d) :
    ‖A‖ ^ 2 = ∑ i : Fin d, ∑ k : Fin d, A i k ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, HilbertMat.inner_def]
  simp only [pow_two]

private theorem enorm_rpow_eq_ofReal_norm_sq_rpow {E : Type*}
    [NormedAddCommGroup E] (v : E) {q : ℝ} :
    ‖v‖ₑ ^ q = (ENNReal.ofReal (‖v‖ ^ 2)) ^ (q / 2) := by
  rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  congr 1
  ring

/-- Private scalar square-lift for the overlap-average derivative.  The
subquadratic and superquadratic finite-center estimates are separated only
inside this proof. -/
private theorem enorm_rpow_euclideanCoordDeriv_averagingField_coord_le
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d) (p : FiniteLpExponent)
    {x : Vec d} (hx : x ∈ openCubeSet Q) (i k : Fin d) :
    ‖euclideanCoordDeriv k (fun y : Vec d => P.averagingField h y i) x‖ₑ ^
        p.exponent.toReal ≤
      (ENNReal.ofReal ((3 ^ d : ℝ) *
        (P.coordDerivConstant / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2)) ^
          (p.exponent.toReal / 2) *
        (if p.exponent.toReal ≤ 2 then 1 else
          (3 ^ d : ℝ≥0∞) ^
            (p.exponent.toReal / 2 - 1)) *
        (ScalarOverlap.centersAtDepth Q j).sum (fun S =>
          (ScalarOverlap.cubeSet S).indicator (fun y : Vec d =>
            ‖HilbertVec.ofVec (h y - ScalarOverlap.cubeAverageVec S h)‖ₑ ^
              p.exponent.toReal) x) := by
  classical
  let r : ℝ := p.exponent.toReal / 2
  let a : TriadicCube d → ℝ≥0∞ := fun S =>
    (ScalarOverlap.cubeSet S).indicator (fun y : Vec d =>
      ENNReal.ofReal ((h y i - ScalarOverlap.cubeAverageVec S h i) ^ 2)) x
  let K : ℝ≥0∞ := ENNReal.ofReal ((3 ^ d : ℝ) *
    (P.coordDerivConstant / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2)
  let D : Finset (TriadicCube d) := ScalarOverlap.centersAtDepth Q j
  let A : Finset (TriadicCube d) := overlapCentersAtDepthContaining Q j x
  have hp_pos : 0 < p.exponent.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans p.one_lt).ne' p.lt_top.ne
  have hr_pos : 0 < r := by dsimp [r]; positivity
  have hsq : ENNReal.ofReal
      ((euclideanCoordDeriv k (fun y : Vec d => P.averagingField h y i) x) ^ 2) ≤
      K * D.sum a := by
    simpa [K, D, a] using!
      P.ofReal_euclideanCoordDeriv_averagingField_coord_sq_le h hx i k
  have hpower := ENNReal.rpow_le_rpow hsq hr_pos.le
  have hactive_sum : D.sum a = A.sum a := by
    symm
    apply Finset.sum_subset
    · intro S hS
      exact (mem_overlapCentersAtDepthContaining_iff.mp hS).1
    · intro S hSD hSnot
      have hxS : x ∉ ScalarOverlap.cubeSet S := by
        intro hxS
        exact hSnot (mem_overlapCentersAtDepthContaining_iff.mpr ⟨hSD, hxS⟩)
      simp [Set.indicator_of_notMem hxS]
  have hsum : (D.sum a) ^ r ≤
      (if p.exponent.toReal ≤ 2 then 1 else
        (3 ^ d : ℝ≥0∞) ^ (r - 1)) *
      D.sum (fun S => (a S) ^ r) := by
    by_cases hp_two : p.exponent.toReal ≤ 2
    · rw [if_pos hp_two, one_mul]
      calc
        (D.sum a) ^ r = (A.sum a) ^ r := by rw [hactive_sum]
        _ ≤ A.sum (fun S => (a S) ^ r) :=
          ennreal_rpow_finset_sum_le_sum_rpow A a hr_pos (by
            dsimp [r]
            linarith)
        _ ≤ D.sum (fun S => (a S) ^ r) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro S hS
            exact (mem_overlapCentersAtDepthContaining_iff.mp hS).1
          · intro S _hS _hnot
            exact bot_le
    · rw [if_neg hp_two]
      have hr_one : 1 ≤ r := by dsimp [r]; linarith
      have hactive := ENNReal.rpow_sum_le_const_mul_sum_rpow (s := A) (f := a) hr_one
      have hcard : (A.card : ℝ≥0∞) ≤ (3 ^ d : ℝ≥0∞) := by
        exact_mod_cast overlapCentersAtDepthContaining_card_le_pow Q j x
      have hpow_nonneg : 0 ≤ r - 1 := sub_nonneg.mpr hr_one
      have hcard_rpow : (A.card : ℝ≥0∞) ^ (r - 1) ≤
          (3 ^ d : ℝ≥0∞) ^ (r - 1) :=
        ENNReal.rpow_le_rpow hcard hpow_nonneg
      have hsum_mono : A.sum (fun S => (a S) ^ r) ≤ D.sum (fun S => (a S) ^ r) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro S hS
          exact (mem_overlapCentersAtDepthContaining_iff.mp hS).1
        · intro S _hS _hnot
          exact bot_le
      calc
        (D.sum a) ^ r = (A.sum a) ^ r := by rw [hactive_sum]
        _ ≤ (A.card : ℝ≥0∞) ^ (r - 1) * A.sum (fun S => (a S) ^ r) := hactive
        _ ≤ (3 ^ d : ℝ≥0∞) ^ (r - 1) * A.sum (fun S => (a S) ^ r) :=
          mul_le_mul_left hcard_rpow _
        _ ≤ (3 ^ d : ℝ≥0∞) ^ (r - 1) * D.sum (fun S => (a S) ^ r) :=
          mul_le_mul_right hsum_mono ((3 ^ d : ℝ≥0∞) ^ (r - 1))
  have hterm : ∀ S ∈ ScalarOverlap.centersAtDepth Q j,
      (a S) ^ r ≤
        (ScalarOverlap.cubeSet S).indicator (fun y : Vec d =>
          ‖HilbertVec.ofVec (h y - ScalarOverlap.cubeAverageVec S h)‖ₑ ^
            p.exponent.toReal) x := by
    intro S _hS
    by_cases hxS : x ∈ ScalarOverlap.cubeSet S
    · dsimp [a]
      rw [Set.indicator_of_mem hxS, Set.indicator_of_mem hxS]
      have hscalar : ENNReal.ofReal
          ((h x i - ScalarOverlap.cubeAverageVec S h i) ^ 2) =
          ‖h x i - ScalarOverlap.cubeAverageVec S h i‖ₑ ^ (2 : ℕ) := by
        exact (enorm_sq_eq_ofReal_sq _).symm
      have hr : (2 : ℝ) * r = p.exponent.toReal := by dsimp [r]; ring
      calc
        (ENNReal.ofReal ((h x i - ScalarOverlap.cubeAverageVec S h i) ^ 2)) ^ r =
            ‖h x i - ScalarOverlap.cubeAverageVec S h i‖ₑ ^ p.exponent.toReal := by
              rw [hscalar, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
              exact congrArg (fun z : ℝ =>
                ‖h x i - ScalarOverlap.cubeAverageVec S h i‖ₑ ^ z) hr
        _ ≤ ‖HilbertVec.ofVec (h x - ScalarOverlap.cubeAverageVec S h)‖ₑ ^
            p.exponent.toReal :=
          ENNReal.rpow_le_rpow
            (by
              rw [Real.enorm_eq_ofReal_abs, ← ofReal_norm]
              exact ENNReal.ofReal_le_ofReal (by
                simpa [Pi.sub_apply, euclideanNorm_eq_norm_ofVec] using
                  (abs_coordinate_le_euclideanNorm
                    (h x - ScalarOverlap.cubeAverageVec S h) i)))
            ENNReal.toReal_nonneg
    · dsimp [a]
      rw [Set.indicator_of_notMem hxS, Set.indicator_of_notMem hxS]
      simp [ENNReal.zero_rpow_of_pos hr_pos]
  have hleft : ‖euclideanCoordDeriv k (fun y : Vec d => P.averagingField h y i) x‖ₑ ^
      p.exponent.toReal =
      (ENNReal.ofReal
        ((euclideanCoordDeriv k (fun y : Vec d => P.averagingField h y i) x) ^ 2)) ^ r := by
    calc
      ‖euclideanCoordDeriv k (fun y : Vec d => P.averagingField h y i) x‖ₑ ^
          p.exponent.toReal =
          (‖euclideanCoordDeriv k (fun y : Vec d => P.averagingField h y i) x‖ₑ ^
            (2 : ℝ)) ^ r := by
              rw [← ENNReal.rpow_mul]
              congr 1
              dsimp [r]
              ring
      _ = (ENNReal.ofReal
          ((euclideanCoordDeriv k (fun y : Vec d => P.averagingField h y i) x) ^ 2)) ^ r := by
            congr 1
            norm_num
            exact enorm_sq_eq_ofReal_sq _
  rw [hleft]
  calc
    (ENNReal.ofReal
      ((euclideanCoordDeriv k (fun y : Vec d => P.averagingField h y i) x) ^ 2)) ^ r ≤
    (K * D.sum a) ^ r := hpower
    _ = K ^ r * (D.sum a) ^ r :=
      ENNReal.mul_rpow_of_nonneg _ _ hr_pos.le
    _ ≤ K ^ r *
          ((if p.exponent.toReal ≤ 2 then 1 else
          (3 ^ d : ℝ≥0∞) ^ (r - 1)) *
          D.sum (fun S => (a S) ^ r)) := by
      exact mul_le_mul_right hsum (K ^ r)
    _ ≤ K ^ r *
          ((if p.exponent.toReal ≤ 2 then 1 else
          (3 ^ d : ℝ≥0∞) ^ (r - 1)) *
          D.sum (fun S =>
            (ScalarOverlap.cubeSet S).indicator (fun y : Vec d =>
              ‖HilbertVec.ofVec (h y - ScalarOverlap.cubeAverageVec S h)‖ₑ ^
                p.exponent.toReal) x)) := by
      apply mul_le_mul_right
      apply mul_le_mul_right
      apply Finset.sum_le_sum
      intro S hS
      exact hterm S hS
    _ = _ := by simp [K, D, r, mul_assoc]

private theorem enorm_rpow_averagingField_jacobian_le
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d) (p : FiniteLpExponent)
    {x : Vec d} (hx : x ∈ openCubeSet Q) :
    ‖HilbertMat.ofMat (fun i k =>
      euclideanCoordDeriv k (fun y : Vec d => P.averagingField h y i) x)‖ₑ ^
        p.exponent.toReal ≤
      (if p.exponent.toReal ≤ 2 then 1 else
        (Fintype.card (Fin d × Fin d) : ℝ≥0∞) ^ (p.exponent.toReal / 2 - 1)) *
      (Fintype.card (Fin d × Fin d) : ℝ≥0∞) *
      (ENNReal.ofReal ((3 ^ d : ℝ) *
        (P.coordDerivConstant / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2)) ^
          (p.exponent.toReal / 2) *
      (if p.exponent.toReal ≤ 2 then 1 else
        (3 ^ d : ℝ≥0∞) ^ (p.exponent.toReal / 2 - 1)) *
      (ScalarOverlap.centersAtDepth Q j).sum (fun S =>
        (ScalarOverlap.cubeSet S).indicator (fun y : Vec d =>
          ‖HilbertVec.ofVec (h y - ScalarOverlap.cubeAverageVec S h)‖ₑ ^
            p.exponent.toReal) x) := by
  classical
  let G : Mat d := fun i k =>
    euclideanCoordDeriv k (fun y : Vec d => P.averagingField h y i) x
  let r : ℝ := p.exponent.toReal / 2
  let E : Fin d × Fin d → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (G z.1 z.2 ^ 2)
  let F : ℝ≥0∞ := (ScalarOverlap.centersAtDepth Q j).sum (fun S =>
    (ScalarOverlap.cubeSet S).indicator (fun y : Vec d =>
      ‖HilbertVec.ofVec (h y - ScalarOverlap.cubeAverageVec S h)‖ₑ ^
        p.exponent.toReal) x)
  let B : ℝ≥0∞ :=
    (ENNReal.ofReal ((3 ^ d : ℝ) *
      (P.coordDerivConstant / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2)) ^ r *
      (if p.exponent.toReal ≤ 2 then 1 else
        (3 ^ d : ℝ≥0∞) ^ (r - 1))
  have hp_pos : 0 < p.exponent.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans p.one_lt).ne' p.lt_top.ne
  have hr_pos : 0 < r := by dsimp [r]; positivity
  have hE : ∀ z : Fin d × Fin d, (E z) ^ r ≤ B * F := by
    intro z
    change (ENNReal.ofReal (G z.1 z.2 ^ 2)) ^ r ≤ B * F
    have heq : (ENNReal.ofReal (G z.1 z.2 ^ 2)) ^ r =
        ‖G z.1 z.2‖ₑ ^ p.exponent.toReal := by
      rw [(enorm_sq_eq_ofReal_sq _).symm, ← ENNReal.rpow_natCast,
        ← ENNReal.rpow_mul]
      exact congrArg (fun t : ℝ => ‖G z.1 z.2‖ₑ ^ t) (by
        dsimp [r]
        ring)
    rw [heq]
    simpa [F, B, G, r] using
      enorm_rpow_euclideanCoordDeriv_averagingField_coord_le P h p hx z.1 z.2
  have hmatrix_sq : ENNReal.ofReal
      (‖HilbertMat.ofMat G‖ ^ 2) = ∑ z : Fin d × Fin d, E z := by
    rw [hilbertMat_norm_sq_eq_sum_sq]
    change ENNReal.ofReal (∑ i : Fin d, ∑ k : Fin d, G i k ^ 2) = _
    rw [ENNReal.ofReal_sum_of_nonneg]
    · rw [show (Finset.univ : Finset (Fin d × Fin d)) =
        (Finset.univ : Finset (Fin d)) ×ˢ Finset.univ by
          ext z
          simp,
        Finset.sum_product]
      apply Finset.sum_congr rfl
      intro i _
      rw [ENNReal.ofReal_sum_of_nonneg]
      · intro k _
        exact sq_nonneg _
    · intro i _
      exact Finset.sum_nonneg fun k _ => sq_nonneg _
  have hsum_rpow : (∑ z : Fin d × Fin d, E z) ^ r ≤
      (if p.exponent.toReal ≤ 2 then 1 else
        (Fintype.card (Fin d × Fin d) : ℝ≥0∞) ^ (r - 1)) *
      ∑ z : Fin d × Fin d, (E z) ^ r := by
    by_cases hp_two : p.exponent.toReal ≤ 2
    · rw [if_pos hp_two, one_mul]
      exact ennreal_rpow_finset_sum_le_sum_rpow Finset.univ E hr_pos (by
        dsimp [r]
        linarith)
    · rw [if_neg hp_two]
      apply ENNReal.rpow_sum_le_const_mul_sum_rpow
      dsimp [r]
      linarith
  have hsum_entries : ∑ z : Fin d × Fin d, (E z) ^ r ≤
      (Fintype.card (Fin d × Fin d) : ℝ≥0∞) * (B * F) := by
    calc
      ∑ z : Fin d × Fin d, (E z) ^ r ≤ ∑ _z : Fin d × Fin d, B * F := by
        apply Finset.sum_le_sum
        intro z _
        exact hE z
      _ = (Fintype.card (Fin d × Fin d) : ℝ≥0∞) * (B * F) := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hleft : ‖HilbertMat.ofMat G‖ₑ ^ p.exponent.toReal =
      (ENNReal.ofReal (‖HilbertMat.ofMat G‖ ^ 2)) ^ r := by
    simpa [r] using
      enorm_rpow_eq_ofReal_norm_sq_rpow
        (HilbertMat.ofMat G) (q := p.exponent.toReal)
  rw [hleft, hmatrix_sq]
  calc
    (∑ z : Fin d × Fin d, E z) ^ r ≤
        (if p.exponent.toReal ≤ 2 then 1 else
          (Fintype.card (Fin d × Fin d) : ℝ≥0∞) ^ (r - 1)) *
          ∑ z : Fin d × Fin d, (E z) ^ r := hsum_rpow
    _ ≤ (if p.exponent.toReal ≤ 2 then 1 else
          (Fintype.card (Fin d × Fin d) : ℝ≥0∞) ^ (r - 1)) *
        ((Fintype.card (Fin d × Fin d) : ℝ≥0∞) * (B * F)) := by
      exact mul_le_mul_right hsum_entries _
    _ = _ := by simp [B, F, r, mul_assoc]

/-- Weighted Jensen for the concrete partition, with the weights then absorbed
by their overlap-cube supports. -/
private theorem enorm_rpow_sub_averagingField_le_sum_overlap_indicator
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d) (p : FiniteLpExponent)
    {x : Vec d} (hx : x ∈ openCubeSet Q) :
    ‖HilbertVec.ofVec (h x - P.averagingField h x)‖ₑ ^ p.exponent.toReal ≤
      (ScalarOverlap.centersAtDepth Q j).sum (fun S =>
        (ScalarOverlap.cubeSet S).indicator
          (fun y : Vec d =>
            ‖HilbertVec.ofVec (h y - ScalarOverlap.cubeAverageVec S h)‖ₑ ^
              p.exponent.toReal) x) := by
  classical
  let D : Finset (TriadicCube d) := ScalarOverlap.centersAtDepth Q j
  let w : TriadicCube d → ℝ := fun S => P.weight S x
  let F : TriadicCube d → HilbertVec d := fun S =>
    HilbertVec.ofVec (h x - ScalarOverlap.cubeAverageVec S h)
  have hvec : h x - P.averagingField h x =
      D.sum (fun S => w S • (h x - ScalarOverlap.cubeAverageVec S h)) := by
    funext i
    simpa [D, w, Pi.smul_apply, Finset.sum_apply] using!
      P.sub_averagingField_apply_eq_sum_weighted_overlap_fluctuation h hx i
  have hres : HilbertVec.ofVec (h x - P.averagingField h x) =
      D.sum (fun S => w S • F S) := by
    change (HilbertVec.ofVecL d) (h x - P.averagingField h x) = _
    rw [hvec, map_sum]
    simp only [map_smul, HilbertVec.ofVecL_apply, F]
  have hw_nonneg : ∀ S ∈ D, 0 ≤ w S := by
    intro S hS
    exact P.nonneg (by simpa [D] using! hS) hx
  have hw_sum : ∑ S ∈ D, w S = 1 := by
    simpa [D, w] using! P.sum_eq_one hx
  have hp_one : 1 ≤ p.exponent.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono p.lt_top.ne p.one_lt.le
  have hp_nonneg : 0 ≤ p.exponent.toReal :=
    le_trans zero_le_one hp_one
  have hJensen :=
    (convexOn_norm_rpow hp_one).map_sum_le
      (t := D) (w := w) (p := F) hw_nonneg hw_sum
      (fun S _hS => Set.mem_univ (F S))
  have hreal : ‖HilbertVec.ofVec (h x - P.averagingField h x)‖ ^
      p.exponent.toReal ≤
      D.sum (fun S => w S * ‖F S‖ ^ p.exponent.toReal) := by
    simpa [hres, smul_eq_mul] using hJensen
  have hterm_nonneg : ∀ S ∈ D, 0 ≤ w S * ‖F S‖ ^ p.exponent.toReal := by
    intro S hS
    exact mul_nonneg (hw_nonneg S hS) (Real.rpow_nonneg (norm_nonneg _) _)
  have hweighted :
      ENNReal.ofReal
          (‖HilbertVec.ofVec (h x - P.averagingField h x)‖ ^
            p.exponent.toReal) ≤
        D.sum (fun S => ENNReal.ofReal (w S * ‖F S‖ ^ p.exponent.toReal)) := by
    rw [← ENNReal.ofReal_sum_of_nonneg hterm_nonneg]
    exact ENNReal.ofReal_le_ofReal hreal
  have hterm_le : ∀ S ∈ D,
      ENNReal.ofReal (w S * ‖F S‖ ^ p.exponent.toReal) ≤
        (ScalarOverlap.cubeSet S).indicator
          (fun y : Vec d =>
            ‖HilbertVec.ofVec (h y - ScalarOverlap.cubeAverageVec S h)‖ₑ ^
              p.exponent.toReal) x := by
    intro S hS
    by_cases hxS : x ∈ ScalarOverlap.cubeSet S
    · rw [Set.indicator_of_mem hxS]
      rw [ENNReal.ofReal_mul (hw_nonneg S hS)]
      change ENNReal.ofReal (w S) * ENNReal.ofReal (‖F S‖ ^ p.exponent.toReal) ≤
        ‖F S‖ₑ ^ p.exponent.toReal
      rw [← ofReal_norm (F S),
        ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp_nonneg]
      have hw : ENNReal.ofReal (w S) ≤ 1 := by
        simpa [w] using ENNReal.ofReal_le_ofReal
          (P.weight_le_one_of_mem_openCubeSet (by simpa [D] using! hS) hx)
      calc
        ENNReal.ofReal (w S) * ENNReal.ofReal ‖F S‖ ^ p.exponent.toReal ≤
            1 * ENNReal.ofReal ‖F S‖ ^ p.exponent.toReal :=
          mul_le_mul_left hw (ENNReal.ofReal ‖F S‖ ^ p.exponent.toReal)
        _ = ENNReal.ofReal ‖F S‖ ^ p.exponent.toReal := one_mul _
    · have hw_zero : w S = 0 := by
        apply Classical.byContradiction
        intro hne
        have hmem : x ∈ openOverlapCubeSet S :=
          P.support_subset (by simpa [D] using! hS) hx hne
        exact hxS (openOverlapCubeSet_subset_overlapCubeSet S hmem)
      simp [hw_zero, hxS]
  have hleft :
      ENNReal.ofReal
          (‖HilbertVec.ofVec (h x - P.averagingField h x)‖ ^
            p.exponent.toReal) =
        ‖HilbertVec.ofVec (h x - P.averagingField h x)‖ₑ ^ p.exponent.toReal := by
    rw [← ofReal_norm,
      ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp_nonneg]
  rw [← hleft]
  exact hweighted.trans (Finset.sum_le_sum fun S hS => hterm_le S hS)

/-- Parent-cube finite-`p` membership restricts to every retained overlap
cube, including for the Euclidean Hilbert realization of a vector field. -/
private theorem memLp_hilbert_overlap_of_memLp {d : ℕ}
    {Q : TriadicCube d} {p : ℝ≥0∞} {h : Vec d → Vec d}
    (hh : MemLp (fun x => HilbertVec.ofVec (h x)) p (normalizedCubeMeasure Q))
    {j : ℕ} {S : TriadicCube d} (hS : S ∈ ScalarOverlap.centersAtDepth Q j) :
    MemLp (fun x => HilbertVec.ofVec (h x)) p
      (ScalarOverlap.normalizedCubeMeasure S) := by
  have hsub : ScalarOverlap.cubeSet S ⊆ cubeSet Q :=
    ScalarOverlap.cubeSet_subset_cubeSet_of_mem_centersAtDepth hS
  have hdom : ScalarOverlap.normalizedCubeMeasure S ≤
      (ENNReal.ofReal (ScalarOverlap.cubeVolume S)⁻¹ *
        ENNReal.ofReal (cubeVolume Q)) • normalizedCubeMeasure Q := by
    rw [ScalarOverlap.normalizedCubeMeasure, normalizedCubeMeasure, smul_smul]
    have hvolQ : (0 : ℝ) < cubeVolume Q := cubeVolume_pos Q
    have hcancel : ENNReal.ofReal (ScalarOverlap.cubeVolume S)⁻¹ *
        ENNReal.ofReal (cubeVolume Q) * ENNReal.ofReal (cubeVolume Q)⁻¹ =
          ENNReal.ofReal (ScalarOverlap.cubeVolume S)⁻¹ := by
      rw [mul_assoc, ← ENNReal.ofReal_mul hvolQ.le,
        mul_inv_cancel₀ hvolQ.ne', ENNReal.ofReal_one, mul_one]
    rw [hcancel]
    refine Measure.le_iff'.2 fun A => ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    refine mul_le_mul_right ?_ _
    rw [ScalarOverlap.cubeMeasure, cubeMeasure]
    exact Measure.le_iff'.1 (Measure.restrict_mono hsub le_rfl) A
  have hfin : (ENNReal.ofReal (ScalarOverlap.cubeVolume S)⁻¹ *
      ENNReal.ofReal (cubeVolume Q)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  exact ((hh.smul_measure hfin).mono_measure hdom)

/-- The powered finite-`p` residual of the concrete average is controlled by
the direct Euclidean overlap energy at the same depth. -/
theorem lintegral_enorm_rpow_sub_averagingField_le_overlapDepthENorm_rpow
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d) (p : FiniteLpExponent)
    (hh : MemLp (fun x => HilbertVec.ofVec (h x)) p.exponent
      (normalizedCubeMeasure Q)) :
    ∫⁻ x, ‖HilbertVec.ofVec (h x - P.averagingField h x)‖ₑ ^ p.exponent.toReal
        ∂ normalizedCubeMeasure Q ≤
      (3 ^ d : ℝ≥0∞) *
        (cubeEuclideanPositiveBesovOverlapDepthENorm Q p h j) ^ p.exponent.toReal := by
  classical
  let Fsum : Vec d → ℝ≥0∞ := fun x =>
    (ScalarOverlap.centersAtDepth Q j).sum (fun S =>
      (ScalarOverlap.cubeSet S).indicator
        (fun y : Vec d =>
          ‖HilbertVec.ofVec (h y - ScalarOverlap.cubeAverageVec S h)‖ₑ ^
            p.exponent.toReal) x)
  have hpoint :
      (fun x => ‖HilbertVec.ofVec (h x - P.averagingField h x)‖ₑ ^
        p.exponent.toReal) ≤ᵐ[normalizedCubeMeasure Q] fun x => Fsum x := by
    filter_upwards [ae_openCubeSet_normalizedCubeMeasure Q] with x hx
    simpa [Fsum] using
      enorm_rpow_sub_averagingField_le_sum_overlap_indicator P h p hx
  have hoverlap : ∫⁻ x, Fsum x ∂ normalizedCubeMeasure Q ≤
      (3 ^ d : ℝ≥0∞) *
        (((ScalarOverlap.centersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
          (ScalarOverlap.centersAtDepth Q j).sum (fun S =>
            ∫⁻ x,
              ‖HilbertVec.ofVec (h x - ScalarOverlap.cubeAverageVec S h)‖ₑ ^
                p.exponent.toReal ∂ ScalarOverlap.normalizedCubeMeasure S)) := by
    simpa [Fsum] using!
      overlapCentersAtDepth_lintegral_sum_indicator_normalizedCubeMeasure_le
        (Q := Q) (j := j)
        (f := fun S x =>
          ‖HilbertVec.ofVec (h x - ScalarOverlap.cubeAverageVec S h)‖ₑ ^
            p.exponent.toReal)
        (fun S hS =>
          aemeasurable_overlapCubeHilbertResidualIndicator_of_memLp p hS
            (memLp_hilbert_overlap_of_memLp hh hS))
  calc
    ∫⁻ x, ‖HilbertVec.ofVec (h x - P.averagingField h x)‖ₑ ^ p.exponent.toReal
        ∂ normalizedCubeMeasure Q ≤
        ∫⁻ x, Fsum x ∂ normalizedCubeMeasure Q :=
      lintegral_mono_ae hpoint
    _ ≤ (3 ^ d : ℝ≥0∞) *
        (((ScalarOverlap.centersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
          (ScalarOverlap.centersAtDepth Q j).sum (fun S =>
            ∫⁻ x,
              ‖HilbertVec.ofVec (h x - ScalarOverlap.cubeAverageVec S h)‖ₑ ^
                p.exponent.toReal ∂ ScalarOverlap.normalizedCubeMeasure S)) := hoverlap
    _ = (3 ^ d : ℝ≥0∞) *
        (cubeEuclideanPositiveBesovOverlapDepthENorm Q p h j) ^ p.exponent.toReal := by
      rw [cubeEuclideanPositiveBesovOverlapDepthENorm_rpow]
      congr 2
      symm
      calc
        (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S =>
            (eLpNorm
              (fun x => HilbertVec.ofVec
                (h x - ScalarOverlap.cubeAverageVec S.1 h))
              p.exponent (ScalarOverlap.normalizedCubeMeasure S.1)) ^
              p.exponent.toReal) =
            (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S =>
              ∫⁻ x,
                ‖HilbertVec.ofVec
                  (h x - ScalarOverlap.cubeAverageVec S.1 h)‖ₑ ^
                    p.exponent.toReal ∂ ScalarOverlap.normalizedCubeMeasure S.1) := by
              apply Finset.sum_congr rfl
              intro S _hS
              rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
                (zero_lt_one.trans p.one_lt).ne' p.lt_top.ne,
                ← ENNReal.rpow_mul]
              have hp : p.exponent.toReal ≠ 0 :=
                ENNReal.toReal_pos (zero_lt_one.trans p.one_lt).ne' p.lt_top.ne |>.ne'
              rw [one_div, inv_mul_cancel₀ hp, ENNReal.rpow_one]
        _ = (ScalarOverlap.centersAtDepth Q j).sum (fun S =>
            ∫⁻ x,
              ‖HilbertVec.ofVec (h x - ScalarOverlap.cubeAverageVec S h)‖ₑ ^
                p.exponent.toReal ∂ ScalarOverlap.normalizedCubeMeasure S) :=
          Finset.sum_attach (ScalarOverlap.centersAtDepth Q j) (fun S =>
            ∫⁻ x,
              ‖HilbertVec.ofVec (h x - ScalarOverlap.cubeAverageVec S h)‖ₑ ^
                p.exponent.toReal ∂ ScalarOverlap.normalizedCubeMeasure S)

namespace SmoothOverlapPartition

/-- The concrete smooth overlap average as a finite-`W^{1,p}` vector field.
It intentionally reuses the field formula of `averagingCompetitor`; only the
Sobolev witness changes. -/
noncomputable def averagingCompetitorW1p {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d) (p : FiniteLpExponent) :
    CubeVectorW1pFunction Q p where
  coord := fun i =>
    W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain (p := p.exponent)
      (isOpenBoundedConvexDomain_openCubeSet Q)
      (P.contDiff_averagingField_coord h i)

@[simp] theorem averagingCompetitorW1p_toField_apply {d : ℕ}
    {Q : TriadicCube d} {j : ℕ} (P : SmoothOverlapPartition Q j)
    (h : Vec d → Vec d) (p : FiniteLpExponent) (x : Vec d) (i : Fin d) :
    (P.averagingCompetitorW1p h p).toField x i = P.averagingField h x i :=
  rfl

@[simp] theorem averagingCompetitorW1p_jacobian_apply {d : ℕ}
    {Q : TriadicCube d} {j : ℕ} (P : SmoothOverlapPartition Q j)
    (h : Vec d → Vec d) (p : FiniteLpExponent) (x : Vec d) (i k : Fin d) :
    (P.averagingCompetitorW1p h p).jacobian x i k =
      euclideanCoordDeriv k (fun y => P.averagingField h y i) x :=
  rfl

/-- The Hilbert and finite-`p` overlap-average witnesses are synchronized at
the field level. -/
theorem averagingCompetitors_toField_eq {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d) (p : FiniteLpExponent) :
    (P.averagingCompetitor h).toField = (P.averagingCompetitorW1p h p).toField := by
  funext x i
  rfl

/-- The Hilbert and finite-`p` overlap-average witnesses are synchronized at
the derivative level. -/
theorem averagingCompetitors_grad_eq {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d) (p : FiniteLpExponent)
    (x : Vec d) (i k : Fin d) :
    ((P.averagingCompetitor h).coord i).grad x k =
      (P.averagingCompetitorW1p h p).jacobian x i k := by
  rfl

/-- Pointwise finite-`p` Jacobian control for the concrete overlap-average
formula.  The finite-center and finite-matrix losses are dimension-only. -/
theorem enorm_rpow_averagingCompetitorW1p_jacobian_le {d : ℕ}
    {Q : TriadicCube d} {j : ℕ} (P : SmoothOverlapPartition Q j)
    (h : Vec d → Vec d) (p : FiniteLpExponent) {x : Vec d}
    (hx : x ∈ openCubeSet Q) :
    ‖HilbertMat.ofMat ((P.averagingCompetitorW1p h p).jacobian x)‖ₑ ^
        p.exponent.toReal ≤
      (if p.exponent.toReal ≤ 2 then 1 else
        (Fintype.card (Fin d × Fin d) : ℝ≥0∞) ^ (p.exponent.toReal / 2 - 1)) *
      (Fintype.card (Fin d × Fin d) : ℝ≥0∞) *
      (ENNReal.ofReal ((3 ^ d : ℝ) *
        (P.coordDerivConstant / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2)) ^
          (p.exponent.toReal / 2) *
      (if p.exponent.toReal ≤ 2 then 1 else
        (3 ^ d : ℝ≥0∞) ^ (p.exponent.toReal / 2 - 1)) *
      (ScalarOverlap.centersAtDepth Q j).sum (fun S =>
        (ScalarOverlap.cubeSet S).indicator (fun y : Vec d =>
          ‖HilbertVec.ofVec (h y - ScalarOverlap.cubeAverageVec S h)‖ₑ ^
            p.exponent.toReal) x) := by
  simpa only [averagingCompetitorW1p_jacobian_apply] using!
    enorm_rpow_averagingField_jacobian_le P h p hx

/-- Powered normalized finite-`p` Jacobian estimate for the overlap-average
competitor.  The only overlap loss is the dimension-only bounded-overlap
constant; in particular no depth-cardinality appears. -/
theorem lintegral_enorm_rpow_averagingCompetitorW1p_jacobian_le_depthENorm
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d) (p : FiniteLpExponent)
    (hh : MemLp (fun x => HilbertVec.ofVec (h x)) p.exponent
      (normalizedCubeMeasure Q)) :
    ∫⁻ x,
        ‖HilbertMat.ofMat ((P.averagingCompetitorW1p h p).jacobian x)‖ₑ ^
          p.exponent.toReal ∂ normalizedCubeMeasure Q ≤
      (if p.exponent.toReal ≤ 2 then 1 else
        (Fintype.card (Fin d × Fin d) : ℝ≥0∞) ^ (p.exponent.toReal / 2 - 1)) *
      (Fintype.card (Fin d × Fin d) : ℝ≥0∞) *
      (ENNReal.ofReal ((3 ^ d : ℝ) *
        (P.coordDerivConstant / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2)) ^
          (p.exponent.toReal / 2) *
      (if p.exponent.toReal ≤ 2 then 1 else
        (3 ^ d : ℝ≥0∞) ^ (p.exponent.toReal / 2 - 1)) *
      (3 ^ d : ℝ≥0∞) *
      (cubeEuclideanPositiveBesovOverlapDepthENorm Q p h j) ^ p.exponent.toReal := by
  let C : ℝ≥0∞ :=
    (if p.exponent.toReal ≤ 2 then 1 else
      (Fintype.card (Fin d × Fin d) : ℝ≥0∞) ^ (p.exponent.toReal / 2 - 1)) *
    (Fintype.card (Fin d × Fin d) : ℝ≥0∞) *
    (ENNReal.ofReal ((3 ^ d : ℝ) *
      (P.coordDerivConstant / (cubeScaleFactor Q / (3 : ℝ) ^ j)) ^ 2)) ^
        (p.exponent.toReal / 2) *
    (if p.exponent.toReal ≤ 2 then 1 else
      (3 ^ d : ℝ≥0∞) ^ (p.exponent.toReal / 2 - 1))
  let F : Vec d → ℝ≥0∞ := fun x =>
    (ScalarOverlap.centersAtDepth Q j).sum (fun S =>
      (ScalarOverlap.cubeSet S).indicator (fun y : Vec d =>
        ‖HilbertVec.ofVec (h y - ScalarOverlap.cubeAverageVec S h)‖ₑ ^
          p.exponent.toReal) x)
  have hpoint :
      (fun x => ‖HilbertMat.ofMat ((P.averagingCompetitorW1p h p).jacobian x)‖ₑ ^
        p.exponent.toReal) ≤ᵐ[normalizedCubeMeasure Q] fun x => C * F x := by
    filter_upwards [ae_openCubeSet_normalizedCubeMeasure Q] with x hx
    simpa [C, F] using P.enorm_rpow_averagingCompetitorW1p_jacobian_le h p hx
  have hoverlap : ∫⁻ x, F x ∂ normalizedCubeMeasure Q ≤
      (3 ^ d : ℝ≥0∞) *
        (cubeEuclideanPositiveBesovOverlapDepthENorm Q p h j) ^ p.exponent.toReal := by
    calc
      ∫⁻ x, F x ∂ normalizedCubeMeasure Q ≤
          (3 ^ d : ℝ≥0∞) *
            (((ScalarOverlap.centersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
              (ScalarOverlap.centersAtDepth Q j).sum (fun S =>
                ∫⁻ x,
                  ‖HilbertVec.ofVec (h x - ScalarOverlap.cubeAverageVec S h)‖ₑ ^
                    p.exponent.toReal ∂ ScalarOverlap.normalizedCubeMeasure S)) := by
            simpa [F] using!
              overlapCentersAtDepth_lintegral_sum_indicator_normalizedCubeMeasure_le
                (Q := Q) (j := j)
                (f := fun S x =>
                  ‖HilbertVec.ofVec (h x - ScalarOverlap.cubeAverageVec S h)‖ₑ ^
                    p.exponent.toReal)
                (fun S hS =>
                  aemeasurable_overlapCubeHilbertResidualIndicator_of_memLp p hS
                    (memLp_hilbert_overlap_of_memLp hh hS))
      _ = (3 ^ d : ℝ≥0∞) *
          (cubeEuclideanPositiveBesovOverlapDepthENorm Q p h j) ^ p.exponent.toReal := by
            rw [cubeEuclideanPositiveBesovOverlapDepthENorm_rpow]
            congr 2
            symm
            calc
              (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S =>
                  (eLpNorm
                    (fun x => HilbertVec.ofVec
                      (h x - ScalarOverlap.cubeAverageVec S.1 h))
                    p.exponent (ScalarOverlap.normalizedCubeMeasure S.1)) ^
                    p.exponent.toReal) =
                  (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S =>
                    ∫⁻ x,
                      ‖HilbertVec.ofVec
                        (h x - ScalarOverlap.cubeAverageVec S.1 h)‖ₑ ^
                          p.exponent.toReal ∂ ScalarOverlap.normalizedCubeMeasure S.1) := by
                    apply Finset.sum_congr rfl
                    intro S _hS
                    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
                      (zero_lt_one.trans p.one_lt).ne' p.lt_top.ne,
                      ← ENNReal.rpow_mul]
                    have hp : p.exponent.toReal ≠ 0 :=
                      ENNReal.toReal_pos (zero_lt_one.trans p.one_lt).ne' p.lt_top.ne |>.ne'
                    rw [one_div, inv_mul_cancel₀ hp, ENNReal.rpow_one]
              _ = (ScalarOverlap.centersAtDepth Q j).sum (fun S =>
                  ∫⁻ x,
                    ‖HilbertVec.ofVec (h x - ScalarOverlap.cubeAverageVec S h)‖ₑ ^
                      p.exponent.toReal ∂ ScalarOverlap.normalizedCubeMeasure S) :=
                Finset.sum_attach (ScalarOverlap.centersAtDepth Q j) (fun S =>
                  ∫⁻ x,
                    ‖HilbertVec.ofVec (h x - ScalarOverlap.cubeAverageVec S h)‖ₑ ^
                      p.exponent.toReal ∂ ScalarOverlap.normalizedCubeMeasure S)
  have hC_ne_top : C ≠ ∞ := by
    by_cases hp_two : p.exponent.toReal ≤ 2
    · simp only [C, if_pos hp_two, one_mul, mul_one]
      apply ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      apply ENNReal.rpow_ne_top_of_nonneg
      · positivity
      · exact ENNReal.ofReal_ne_top
    · simp only [C, if_neg hp_two]
      apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · apply ENNReal.mul_ne_top
          · apply ENNReal.rpow_ne_top_of_nonneg
            linarith
            exact ENNReal.natCast_ne_top _
          · exact ENNReal.natCast_ne_top _
        · apply ENNReal.rpow_ne_top_of_nonneg
          positivity
          exact ENNReal.ofReal_ne_top
      · apply ENNReal.rpow_ne_top_of_nonneg
        linarith
        exact ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  calc
    ∫⁻ x,
        ‖HilbertMat.ofMat ((P.averagingCompetitorW1p h p).jacobian x)‖ₑ ^
          p.exponent.toReal ∂ normalizedCubeMeasure Q ≤
        ∫⁻ x, C * F x ∂ normalizedCubeMeasure Q :=
      lintegral_mono_ae hpoint
    _ ≤ C * ∫⁻ x, F x ∂ normalizedCubeMeasure Q :=
      (lintegral_const_mul' C F hC_ne_top).le
    _ ≤ C * ((3 ^ d : ℝ≥0∞) *
        (cubeEuclideanPositiveBesovOverlapDepthENorm Q p h j) ^ p.exponent.toReal) :=
      mul_le_mul_right hoverlap C
    _ = _ := by simp [C, mul_assoc]

/-- Simultaneous Hilbert and finite-`p` witnesses for an input carrying both
integrability classes.  The membership assumptions are retained here because
the later residual estimates consume both witnesses from the same datum. -/
theorem exists_synchronized_averagingCompetitors {d : ℕ} {Q : TriadicCube d}
    {j : ℕ} (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d) (p : FiniteLpExponent)
    (_h2 : MemLp (fun x => HilbertVec.ofVec (h x)) 2 (normalizedCubeMeasure Q))
    (_hp : MemLp (fun x => HilbertVec.ofVec (h x)) p.exponent
      (normalizedCubeMeasure Q)) :
    ∃ G2 : CubeVectorH1Function Q, ∃ Gp : CubeVectorW1pFunction Q p,
      G2.toField = P.averagingField h ∧
        Gp.toField = P.averagingField h ∧
          ∀ x i k, (G2.coord i).grad x k = Gp.jacobian x i k := by
  refine ⟨P.averagingCompetitor h, P.averagingCompetitorW1p h p, rfl, rfl, ?_⟩
  intro x i k
  rfl

end SmoothOverlapPartition

end

end Homogenization
