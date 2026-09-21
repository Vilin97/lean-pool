/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch01.Theorems.DualToCircLoss.ProjectionTests

/-! # Finite Loss -/

namespace Homogenization
namespace Book
namespace Ch01
namespace Legacy

noncomputable section

open scoped BigOperators ENNReal

/-!
# Dual-to-circ finite loss

Legacy finite-truncation loss estimates for the totalized-real,
disjoint/componentwise compatibility lane.  They are not the exact `ENNReal`
overlap/dual/circ kernels.
-/

private theorem three_rpow_nonneg (x : ℝ) : 0 ≤ Real.rpow (3 : ℝ) x :=
  Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) x

private theorem cubeBesovNegativeVectorDepthAverage_eq_sum_sq_cubeLpNorm_projection_two {d : ℕ}
    (Q : Cube d) (F : Vec d → Vec d) (j : ℕ) :
    cubeBesovNegativeVectorDepthAverage Q F j =
      ∑ i : Fin d,
        (cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j (fun x => F x i))) ^ (2 : ℕ) := by
  unfold cubeBesovNegativeVectorDepthAverage
  calc
    descendantsAverage Q j (fun R => vecNormSq (cubeAverageVec R F))
        =
      descendantsAverage Q j
        (fun R => ∑ i : Fin d, (cubeAverage R (fun x => F x i)) ^ (2 : ℕ)) := by
          congr 1
          funext R
          simp [vecNormSq, vecDot, cubeAverageVec, pow_two]
    _ =
      ∑ i : Fin d,
        descendantsAverage Q j
          (fun R => (cubeAverage R (fun x => F x i)) ^ (2 : ℕ)) := by
          simpa using
            descendantsAverage_sum Q j Finset.univ
              (fun R i => (cubeAverage R (fun x => F x i)) ^ (2 : ℕ))
    _ =
      ∑ i : Fin d,
        (cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j (fun x => F x i))) ^ (2 : ℕ) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hscalar :=
            cubeBesovCircDepthAverage_eq_sq_cubeLpNorm_projection_two
              Q j (fun x => F x i)
          simpa [cubeBesovCircDepthAverage, Real.rpow_natCast, Real.norm_eq_abs,
            pow_two] using hscalar

private theorem cubeBesovNegativeVectorDepthSeminorm_le_sum_component_projection_l2 {d : ℕ}
    (Q : Cube d) (s : ℝ) (F : Vec d → Vec d) (j : ℕ) :
    cubeBesovNegativeVectorDepthSeminorm Q s F j ≤
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        ∑ i : Fin d,
          cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j (fun x => F x i)) := by
  have havg :=
    cubeBesovNegativeVectorDepthAverage_eq_sum_sq_cubeLpNorm_projection_two Q F j
  have hsqrt :
      Real.sqrt (cubeBesovNegativeVectorDepthAverage Q F j) ≤
        ∑ i : Fin d,
          cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j (fun x => F x i)) := by
    rw [havg]
    exact sqrt_sum_sq_le_sum Finset.univ
      (fun i => cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j (fun x => F x i)))
      (fun i hi => cubeLpNorm_nonneg Q (2 : ℝ≥0∞)
        (cubeProjection Q j (fun x => F x i)))
  unfold cubeBesovNegativeVectorDepthSeminorm
  exact mul_le_mul_of_nonneg_left hsqrt
    (three_rpow_nonneg _)

/-- Finite-depth coefficient in the lossy true-dual-to-circ comparison.  The
outer `j` sum is the negative Besov scale sum, and the inner `k` sum is the
positive test norm of the depth-`j` projection. -/
noncomputable def dualToCircFiniteLossCoefficient (s t : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1),
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      (1 + ∑ k ∈ Finset.range j, 2 * Real.rpow (3 : ℝ) (t * (k : ℝ)))

theorem dualToCircFiniteLossCoefficient_nonneg (s t : ℝ) (N : ℕ) :
    0 ≤ dualToCircFiniteLossCoefficient s t N := by
  unfold dualToCircFiniteLossCoefficient
  refine Finset.sum_nonneg ?_
  intro j hj
  exact mul_nonneg
    (three_rpow_nonneg _)
    (add_nonneg zero_le_one
      (Finset.sum_nonneg fun k hk =>
        mul_nonneg (by norm_num) (three_rpow_nonneg _)))

/-- Explicit geometric coefficient bounding the finite loss coefficients when
`0 < t < s`. -/
noncomputable def dualToCircGeometricLossCoefficient (s t : ℝ) : ℝ :=
  (1 - Real.rpow (3 : ℝ) (-s))⁻¹ +
    (2 * (1 - Real.rpow (3 : ℝ) (-t))⁻¹) *
      (1 - Real.rpow (3 : ℝ) (-(s - t)))⁻¹

private theorem sum_range_pow_sub_le_geom {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (j : ℕ) :
    (∑ k ∈ Finset.range j, r ^ (j - k)) ≤ (1 - r)⁻¹ := by
  have hreflect :
      (∑ k ∈ Finset.range j, r ^ (j - k)) =
        ∑ k ∈ Finset.range j, r ^ (k + 1) := by
    rw [← Finset.sum_range_reflect (fun m : ℕ => r ^ (m + 1)) j]
    refine Finset.sum_congr rfl ?_
    intro k hk
    congr 1
    have hklt : k < j := Finset.mem_range.mp hk
    omega
  calc
    (∑ k ∈ Finset.range j, r ^ (j - k))
        = ∑ k ∈ Finset.range j, r ^ (k + 1) := hreflect
    _ ≤ ∑ k ∈ Finset.range j, r ^ k := by
          refine Finset.sum_le_sum ?_
          intro k hk
          exact pow_le_pow_of_le_one hr0 hr1.le (Nat.le_succ k)
    _ ≤ (1 - r)⁻¹ := geom_sum_range_le_of_lt_one hr0 hr1

private theorem dualToCirc_inner_weighted_sum_le {s t : ℝ}
    (ht : 0 < t) (j : ℕ) :
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        (∑ k ∈ Finset.range j, 2 * Real.rpow (3 : ℝ) (t * (k : ℝ))) ≤
      2 * (1 - Real.rpow (3 : ℝ) (-t))⁻¹ *
        Real.rpow (3 : ℝ) (-(s - t) * (j : ℝ)) := by
  let r : ℝ := Real.rpow (3 : ℝ) (-t)
  let A : ℝ := Real.rpow (3 : ℝ) (-(s - t) * (j : ℝ))
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact three_rpow_nonneg _
  have hr1 : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3) (by linarith)
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact three_rpow_nonneg _
  have hsum_eq :
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          (∑ k ∈ Finset.range j, 2 * Real.rpow (3 : ℝ) (t * (k : ℝ))) =
        (2 * A) * ∑ k ∈ Finset.range j, r ^ (j - k) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hkj : k ≤ j := Nat.le_of_lt (Finset.mem_range.mp hk)
    have hterm :
        Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            (2 * Real.rpow (3 : ℝ) (t * (k : ℝ))) =
          (2 * Real.rpow (3 : ℝ) (-(s - t) * (j : ℝ))) *
            (Real.rpow (3 : ℝ) (-t)) ^ (j - k) := by
      have hpow :
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
              Real.rpow (3 : ℝ) (t * (k : ℝ)) =
            Real.rpow (3 : ℝ) (-(s - t) * (j : ℝ)) *
              Real.rpow (3 : ℝ) (-t * ((j - k : ℕ) : ℝ)) := by
        change ((3 : ℝ) ^ (-s * (j : ℝ))) *
              ((3 : ℝ) ^ (t * (k : ℝ))) =
            ((3 : ℝ) ^ (-(s - t) * (j : ℝ))) *
              ((3 : ℝ) ^ (-t * ((j - k : ℕ) : ℝ)))
        rw [← Real.rpow_add (by norm_num : 0 < (3 : ℝ)),
          ← Real.rpow_add (by norm_num : 0 < (3 : ℝ))]
        congr 1
        rw [Nat.cast_sub hkj]
        ring
      have hsub :
          Real.rpow (3 : ℝ) (-t * ((j - k : ℕ) : ℝ)) =
            (Real.rpow (3 : ℝ) (-t)) ^ (j - k) := by
        simpa using
          (Real.rpow_mul_natCast (by norm_num : 0 ≤ (3 : ℝ)) (-t) (j - k))
      calc
        Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            (2 * Real.rpow (3 : ℝ) (t * (k : ℝ)))
            = 2 * (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                Real.rpow (3 : ℝ) (t * (k : ℝ))) := by ring
        _ = 2 * (Real.rpow (3 : ℝ) (-(s - t) * (j : ℝ)) *
              Real.rpow (3 : ℝ) (-t * ((j - k : ℕ) : ℝ))) := by
              rw [hpow]
        _ = 2 * (Real.rpow (3 : ℝ) (-(s - t) * (j : ℝ)) *
              (Real.rpow (3 : ℝ) (-t)) ^ (j - k)) := by
              rw [hsub]
        _ = (2 * Real.rpow (3 : ℝ) (-(s - t) * (j : ℝ))) *
              (Real.rpow (3 : ℝ) (-t)) ^ (j - k) := by ring
    simpa [A, r] using hterm
  calc
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        (∑ k ∈ Finset.range j, 2 * Real.rpow (3 : ℝ) (t * (k : ℝ)))
        = (2 * A) * ∑ k ∈ Finset.range j, r ^ (j - k) := hsum_eq
    _ ≤ (2 * A) * (1 - r)⁻¹ := by
          exact mul_le_mul_of_nonneg_left
            (sum_range_pow_sub_le_geom hr0 hr1 j)
            (mul_nonneg (by norm_num) hA0)
    _ = 2 * (1 - Real.rpow (3 : ℝ) (-t))⁻¹ *
          Real.rpow (3 : ℝ) (-(s - t) * (j : ℝ)) := by
          dsimp [A, r]
          ring

theorem dualToCircFiniteLossCoefficient_le_geometric {s t : ℝ}
    (_hs : 0 < s) (ht : 0 < t) (hst : t < s) (N : ℕ) :
    dualToCircFiniteLossCoefficient s t N ≤
      dualToCircGeometricLossCoefficient s t := by
  let rs : ℝ := Real.rpow (3 : ℝ) (-s)
  let rt : ℝ := Real.rpow (3 : ℝ) (-t)
  let rho : ℝ := Real.rpow (3 : ℝ) (-(s - t))
  let K : ℝ := 2 * (1 - rt)⁻¹
  have hrs0 : 0 ≤ rs := by
    dsimp [rs]
    exact three_rpow_nonneg _
  have hrho0 : 0 ≤ rho := by
    dsimp [rho]
    exact three_rpow_nonneg _
  have hrs1 : rs < 1 := by
    dsimp [rs]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3) (by linarith)
  have hrt1 : rt < 1 := by
    dsimp [rt]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3) (by linarith)
  have hrho1 : rho < 1 := by
    dsimp [rho]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3) (by linarith)
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr (sub_nonneg.mpr hrt1.le))
  have hterm :
      ∀ j ∈ Finset.range (N + 1),
        Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            (1 + ∑ k ∈ Finset.range j,
              2 * Real.rpow (3 : ℝ) (t * (k : ℝ))) ≤
          rs ^ j + K * rho ^ j := by
    intro j hj
    have hrs_eq : Real.rpow (3 : ℝ) (-s * (j : ℝ)) = rs ^ j := by
      dsimp [rs]
      simpa using (Real.rpow_mul_natCast (by norm_num : 0 ≤ (3 : ℝ)) (-s) j)
    have hrho_eq :
        Real.rpow (3 : ℝ) (-(s - t) * (j : ℝ)) = rho ^ j := by
      dsimp [rho]
      simpa using
        (Real.rpow_mul_natCast (by norm_num : 0 ≤ (3 : ℝ)) (-(s - t)) j)
    have hinner := dualToCirc_inner_weighted_sum_le (s := s) (t := t) ht j
    calc
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
          (1 + ∑ k ∈ Finset.range j,
            2 * Real.rpow (3 : ℝ) (t * (k : ℝ)))
          = Real.rpow (3 : ℝ) (-s * (j : ℝ)) +
              Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
                (∑ k ∈ Finset.range j,
                  2 * Real.rpow (3 : ℝ) (t * (k : ℝ))) := by
              ring
      _ ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) +
            2 * (1 - Real.rpow (3 : ℝ) (-t))⁻¹ *
              Real.rpow (3 : ℝ) (-(s - t) * (j : ℝ)) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right hinner (Real.rpow (3 : ℝ) (-s * (j : ℝ)))
      _ = rs ^ j + K * rho ^ j := by
            rw [hrs_eq, hrho_eq]
  unfold dualToCircFiniteLossCoefficient
  calc
    ∑ j ∈ Finset.range (N + 1),
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        (1 + ∑ k ∈ Finset.range j, 2 * Real.rpow (3 : ℝ) (t * (k : ℝ)))
        ≤ ∑ j ∈ Finset.range (N + 1), (rs ^ j + K * rho ^ j) := by
          exact Finset.sum_le_sum hterm
    _ = (∑ j ∈ Finset.range (N + 1), rs ^ j) +
          K * (∑ j ∈ Finset.range (N + 1), rho ^ j) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (1 - rs)⁻¹ + K * (1 - rho)⁻¹ := by
          exact add_le_add
            (geom_sum_range_le_of_lt_one hrs0 hrs1)
            (mul_le_mul_of_nonneg_left
              (geom_sum_range_le_of_lt_one hrho0 hrho1) hK0)
    _ = dualToCircGeometricLossCoefficient s t := by
          dsimp [dualToCircGeometricLossCoefficient, rs, rt, rho, K]

/-- Half-exponent geometric loss with a simple note-style `s^{-2}` bound. -/
theorem dualToCircGeometricLossCoefficient_half_le_fiftyFive_inv_sq {s : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1) :
    dualToCircGeometricLossCoefficient s (s / 2) ≤ 55 * (s⁻¹) ^ (2 : ℕ) := by
  let X : ℝ := s⁻¹
  let A : ℝ := (1 - Real.rpow (3 : ℝ) (-s))⁻¹
  let B₁ : ℝ := (1 - Real.rpow (3 : ℝ) (-(s / 2)))⁻¹
  let B₂ : ℝ := (1 - Real.rpow (3 : ℝ) (-(s - s / 2)))⁻¹
  have hX_nonneg : 0 ≤ X := by
    dsimp [X]
    exact inv_nonneg.mpr hs.le
  have hX_ge_one : 1 ≤ X := by
    dsimp [X]
    exact (one_le_inv₀ hs).2 hs_le
  have hA : A ≤ 5 * X := by
    dsimp [A, X]
    exact Homogenization.inv_one_sub_rpow_three_neg_le_five_inv hs hs_le
  have hB₁ : B₁ ≤ 5 * X := by
    dsimp [B₁, X]
    simpa [neg_div] using
      Homogenization.inv_one_sub_rpow_three_neg_half_le_five_inv hs hs_le
  have hB₂ : B₂ ≤ 5 * X := by
    dsimp [B₂, X]
    have hrewrite : -(s - s / 2) = -s / 2 := by ring
    simpa [hrewrite] using
      Homogenization.inv_one_sub_rpow_three_neg_half_le_five_inv hs hs_le
  have hB₁_nonneg : 0 ≤ B₁ := by
    dsimp [B₁]
    have hr_lt :
        Real.rpow (3 : ℝ) (-(s / 2)) < 1 := by
      exact Real.rpow_lt_one_of_one_lt_of_neg
        (by norm_num : (1 : ℝ) < 3) (by nlinarith)
    exact inv_nonneg.mpr (sub_nonneg.mpr hr_lt.le)
  have hB₂_nonneg : 0 ≤ B₂ := by
    dsimp [B₂]
    have hr_lt :
        Real.rpow (3 : ℝ) (-(s - s / 2)) < 1 := by
      exact Real.rpow_lt_one_of_one_lt_of_neg
        (by norm_num : (1 : ℝ) < 3) (by nlinarith)
    exact inv_nonneg.mpr (sub_nonneg.mpr hr_lt.le)
  have hA_sq : A ≤ 5 * X ^ (2 : ℕ) := by
    nlinarith [hA, hX_nonneg, hX_ge_one]
  have hB_sq : (2 * B₁) * B₂ ≤ 50 * X ^ (2 : ℕ) := by
    nlinarith [hB₁, hB₂, hB₁_nonneg, hB₂_nonneg, hX_nonneg]
  unfold dualToCircGeometricLossCoefficient
  change A + (2 * B₁) * B₂ ≤ 55 * X ^ (2 : ℕ)
  nlinarith

/-- Half-exponent finite loss coefficient bounded by the explicit
`55 * s^{-2}` note-style loss. -/
theorem dualToCircFiniteLossCoefficient_half_le_fiftyFive_inv_sq
    {s : ℝ} (hs : 0 < s) (hs_le : s ≤ 1) (N : ℕ) :
    dualToCircFiniteLossCoefficient s (s / 2) N ≤ 55 * (s⁻¹) ^ (2 : ℕ) :=
  (dualToCircFiniteLossCoefficient_le_geometric hs (by nlinarith) (by nlinarith) N).trans
    (dualToCircGeometricLossCoefficient_half_le_fiftyFive_inv_sq hs hs_le)

/-- Componentwise vector-valued genuine dual negative Besov norm, normalized by
the parent cube scale, in the legacy totalized-real compatibility lane.  This
is distinct from the exact `ENNReal` overlap/dual/circ kernels. -/
noncomputable def normalizedDualNegativeBesovVectorNormTwo {d : ℕ}
    (Q : Cube d) (s : ℝ) (F : Vec d → Vec d) : ℝ :=
  cubeBesovScaleWeight s Q *
    ∑ i : Fin d,
      dualNegativeBesovNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
        (fun x => F x i)

theorem normalizedDualNegativeBesovVectorNormTwo_nonneg {d : ℕ}
    (Q : Cube d) (s : ℝ) (F : Vec d → Vec d) :
    0 ≤ normalizedDualNegativeBesovVectorNormTwo Q s F := by
  unfold normalizedDualNegativeBesovVectorNormTwo
  exact mul_nonneg
    (cubeBesovScaleWeight_nonneg s Q)
    (Finset.sum_nonneg fun i _ =>
      cubeBesovDualFullNorm_nonneg Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
        (fun x => F x i)
        cubeBesovConjExponent_two_ne_zero_dualToCirc
        cubeBesovConjExponent_two_ne_top_dualToCirc)

private theorem memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet_ch1 {d : ℕ}
    (Q : Cube d) {F : Vec d → Vec d}
    (hF : MemVectorL2 (cubeSet Q) F) :
    MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  have hfCube :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (MeasureTheory.volume.restrict (cubeSet Q)) := by
    simpa [MemVectorL2, volumeMeasureOn] using hF
  exact
    hfCube.of_measure_le_smul (c := ENNReal.ofReal ((cubeVolume Q)⁻¹))
      ENNReal.ofReal_ne_top (by rw [normalizedCubeMeasure, cubeMeasure])

theorem component_memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet_ch1 {d : ℕ}
    (Q : Cube d) {F : Vec d → Vec d}
    (hF : MemVectorL2 (cubeSet Q) F) :
    ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => F x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  intro i
  let π : Vec d →L[ℝ] ℝ := ContinuousLinearMap.proj i
  simpa [π, Function.comp_def, ContinuousLinearMap.proj_apply] using!
    π.comp_memLp' (memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet_ch1 Q hF)

theorem cubeBesovNegativeVectorPartialSeminormTwo_le_dualToCircFiniteLossCoefficient_mul_normalizedDual
    {d : ℕ} (Q : Cube d) (F : Vec d → Vec d) {s t : ℝ} (N : ℕ)
    (ht : 0 < t)
    (hF : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => F x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovNegativeVectorPartialSeminormTwo Q s N F ≤
      dualToCircFiniteLossCoefficient s t N *
        normalizedDualNegativeBesovVectorNormTwo Q t F := by
  have hpartial_one :
      cubeBesovNegativeVectorPartialSeminormTwo Q s N F ≤
        cubeBesovNegativeVectorPartialSeminorm Q s N F :=
    cubeBesovNegativeVectorPartialSeminormTwo_le_partialSeminorm Q s N F
  have hdepth :
      ∀ j ∈ Finset.range (N + 1),
        cubeBesovNegativeVectorDepthSeminorm Q s F j ≤
          (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            (1 + ∑ k ∈ Finset.range j, 2 * Real.rpow (3 : ℝ) (t * (k : ℝ)))) *
            normalizedDualNegativeBesovVectorNormTwo Q t F := by
    intro j hj
    have hproj :
        ∀ i : Fin d,
          cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j (fun x => F x i)) ≤
            cubeBesovDualFullNorm Q t (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => F x i) *
              cubeProjectionPositiveTestCoefficientTwo Q t j := by
      intro i
      exact cubeLpNorm_projection_le_dualFullNorm_mul_positiveTestCoefficient_two
        Q t j (fun x => F x i) ht (hF i)
    have hsum_proj :
        ∑ i : Fin d,
          cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j (fun x => F x i)) ≤
        cubeProjectionPositiveTestCoefficientTwo Q t j *
          ∑ i : Fin d,
            cubeBesovDualFullNorm Q t (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => F x i) := by
      calc
        ∑ i : Fin d,
          cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j (fun x => F x i))
            ≤
          ∑ i : Fin d,
            cubeBesovDualFullNorm Q t (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => F x i) *
              cubeProjectionPositiveTestCoefficientTwo Q t j := by
              exact Finset.sum_le_sum fun i hi => hproj i
        _ =
              cubeProjectionPositiveTestCoefficientTwo Q t j *
            ∑ i : Fin d,
              cubeBesovDualFullNorm Q t (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => F x i) := by
              rw [← Finset.sum_mul]
              ring
    have hcoeff_eq :
        cubeProjectionPositiveTestCoefficientTwo Q t j =
          cubeBesovScaleWeight t Q *
            (1 + ∑ k ∈ Finset.range j, 2 * Real.rpow (3 : ℝ) (t * (k : ℝ))) := by
      unfold cubeProjectionPositiveTestCoefficientTwo
      have hsum_factor :
          (∑ k ∈ Finset.range j,
            2 * cubeBesovScaleWeight t Q * Real.rpow (3 : ℝ) (t * (k : ℝ))) =
            cubeBesovScaleWeight t Q *
              (∑ k ∈ Finset.range j, 2 * Real.rpow (3 : ℝ) (t * (k : ℝ))) := by
        calc
          (∑ k ∈ Finset.range j,
            2 * cubeBesovScaleWeight t Q * Real.rpow (3 : ℝ) (t * (k : ℝ)))
              =
            ∑ k ∈ Finset.range j,
              cubeBesovScaleWeight t Q *
                (2 * Real.rpow (3 : ℝ) (t * (k : ℝ))) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              ring
          _ =
            cubeBesovScaleWeight t Q *
              (∑ k ∈ Finset.range j, 2 * Real.rpow (3 : ℝ) (t * (k : ℝ))) := by
              rw [← Finset.mul_sum (s := Finset.range j)
                (f := fun k : ℕ => 2 * Real.rpow (3 : ℝ) (t * (k : ℝ)))
                (a := cubeBesovScaleWeight t Q)]
      calc
        (∑ k ∈ Finset.range j,
            2 * cubeBesovScaleWeight t Q * Real.rpow (3 : ℝ) (t * (k : ℝ))) +
            cubeBesovScaleWeight t Q
            =
          cubeBesovScaleWeight t Q *
            (∑ k ∈ Finset.range j, 2 * Real.rpow (3 : ℝ) (t * (k : ℝ))) +
            cubeBesovScaleWeight t Q := by
              rw [hsum_factor]
        _ =
          cubeBesovScaleWeight t Q *
            (1 + ∑ k ∈ Finset.range j, 2 * Real.rpow (3 : ℝ) (t * (k : ℝ))) := by
              ring
    have hdepth_l2 :=
      cubeBesovNegativeVectorDepthSeminorm_le_sum_component_projection_l2 Q s F j
    calc
      cubeBesovNegativeVectorDepthSeminorm Q s F j
          ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
              ∑ i : Fin d,
                cubeLpNorm Q (2 : ℝ≥0∞)
                  (cubeProjection Q j (fun x => F x i)) := hdepth_l2
      _ ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            (cubeProjectionPositiveTestCoefficientTwo Q t j *
              ∑ i : Fin d,
                cubeBesovDualFullNorm Q t (2 : ℝ≥0∞) (2 : ℝ≥0∞)
                  (fun x => F x i)) := by
            exact mul_le_mul_of_nonneg_left hsum_proj
              (three_rpow_nonneg _)
      _ =
          (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            (1 + ∑ k ∈ Finset.range j, 2 * Real.rpow (3 : ℝ) (t * (k : ℝ)))) *
            normalizedDualNegativeBesovVectorNormTwo Q t F := by
            unfold normalizedDualNegativeBesovVectorNormTwo
            rw [hcoeff_eq]
            ring
  calc
    cubeBesovNegativeVectorPartialSeminormTwo Q s N F
        ≤ cubeBesovNegativeVectorPartialSeminorm Q s N F := hpartial_one
    _ = ∑ j ∈ Finset.range (N + 1),
          cubeBesovNegativeVectorDepthSeminorm Q s F j := by
          rfl
    _ ≤ ∑ j ∈ Finset.range (N + 1),
          (Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
            (1 + ∑ k ∈ Finset.range j, 2 * Real.rpow (3 : ℝ) (t * (k : ℝ)))) *
            normalizedDualNegativeBesovVectorNormTwo Q t F := by
          exact Finset.sum_le_sum hdepth
    _ =
        dualToCircFiniteLossCoefficient s t N *
          normalizedDualNegativeBesovVectorNormTwo Q t F := by
          unfold dualToCircFiniteLossCoefficient
          rw [Finset.sum_mul]

/--
Full-seminorm form of the proved scale-by-scale true-dual-to-circ comparison,
parametrized by any uniform bound on the finite loss coefficient.

The remaining scalar analytic work is to supply such a coefficient bound, for
example with `t = s / 2`, where the notes lose a power of `s⁻¹`.
-/
theorem cubeBesovNegativeVectorSeminormTwo_le_dualToCircCoefficientBound_mul_normalizedDual
    {d : ℕ} (Q : Cube d) (F : Vec d → Vec d) {s t C : ℝ}
    (ht : 0 < t)
    (hF : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => F x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hcoeff : ∀ N : ℕ, dualToCircFiniteLossCoefficient s t N ≤ C) :
    cubeBesovNegativeVectorSeminormTwo Q s F ≤
      C * normalizedDualNegativeBesovVectorNormTwo Q t F := by
  refine cubeBesovNegativeVectorSeminormTwo_le_of_partialBound Q s F ?_
  intro N
  have hpartial :
      cubeBesovNegativeVectorPartialSeminormTwo Q s N F ≤
        dualToCircFiniteLossCoefficient s t N *
          normalizedDualNegativeBesovVectorNormTwo Q t F :=
    cubeBesovNegativeVectorPartialSeminormTwo_le_dualToCircFiniteLossCoefficient_mul_normalizedDual
      Q F N ht hF
  exact hpartial.trans
    (mul_le_mul_of_nonneg_right (hcoeff N)
      (normalizedDualNegativeBesovVectorNormTwo_nonneg Q t F))

/-- Full finite-energy reverse comparison with the explicit geometric loss
coefficient. -/
theorem cubeBesovNegativeVectorSeminormTwo_le_dualToCircGeometricLossCoefficient_mul_normalizedDual
    {d : ℕ} (Q : Cube d) (F : Vec d → Vec d) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : t < s)
    (hF : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => F x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovNegativeVectorSeminormTwo Q s F ≤
      dualToCircGeometricLossCoefficient s t *
        normalizedDualNegativeBesovVectorNormTwo Q t F := by
  exact
    cubeBesovNegativeVectorSeminormTwo_le_dualToCircCoefficientBound_mul_normalizedDual
      Q F ht hF
      (fun N => dualToCircFiniteLossCoefficient_le_geometric hs ht hst N)

/-- Full finite-energy half-exponent reverse comparison with the explicit
`55 * s^{-2}` loss. -/
theorem cubeBesovNegativeVectorSeminormTwo_le_halfDual_fiftyFive_inv_sq
    {d : ℕ} (Q : Cube d) (F : Vec d → Vec d) {s : ℝ}
    (hs : 0 < s) (hs_lt : s < 1)
    (hF : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => F x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovNegativeVectorSeminormTwo Q s F ≤
      (55 * (s⁻¹) ^ (2 : ℕ)) *
        normalizedDualNegativeBesovVectorNormTwo Q (s / 2) F := by
  exact
    cubeBesovNegativeVectorSeminormTwo_le_dualToCircCoefficientBound_mul_normalizedDual
      Q F (by nlinarith) hF
      (fun N => dualToCircFiniteLossCoefficient_half_le_fiftyFive_inv_sq
        hs hs_lt.le N)

/-- Finite-energy half-exponent reverse comparison for fields supplied as
`L²` vector fields on the cube. -/
theorem cubeBesovNegativeVectorSeminormTwo_le_halfDual_fiftyFive_inv_sq_of_memVectorL2
    {d : ℕ} (Q : Cube d) (F : Vec d → Vec d) {s : ℝ}
    (hs : 0 < s) (hs_lt : s < 1)
    (hF : MemVectorL2 (cubeSet Q) F) :
    cubeBesovNegativeVectorSeminormTwo Q s F ≤
      (55 * (s⁻¹) ^ (2 : ℕ)) *
        normalizedDualNegativeBesovVectorNormTwo Q (s / 2) F :=
  cubeBesovNegativeVectorSeminormTwo_le_halfDual_fiftyFive_inv_sq
    Q F hs hs_lt
    (component_memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet_ch1 Q hF)

end

end Legacy
end Ch01
end Book
end Homogenization
