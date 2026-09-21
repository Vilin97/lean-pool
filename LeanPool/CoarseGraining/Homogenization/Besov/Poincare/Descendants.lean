/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.Poincare.Projection

/-! # Descendants -/

namespace Homogenization

open scoped BigOperators ENNReal

/-- Descendant-local analytic hypothesis where the local dual mean-zero
Poincare estimate is supplied against the finite projection of `g` on each
descendant cube at the exact depth that matches the multiscale corridor's
`M - j` indexing. -/
def CubeDescendantProjectedDualMeanZeroPoincareEstimate {d : ℕ} (Q : TriadicCube d)
    (C : ℝ) (u g : Vec d → ℝ) (M : ℕ) : Prop :=
  ∀ j ∈ Finset.range (M + 1), ∀ R ∈ descendantsAtDepth Q j,
    CubeDualMeanZeroPoincareEstimate R C u (cubeProjection R (M - j) g)

theorem CubeDescendantProjectedDualMeanZeroPoincareEstimate.to_localEstimate
    {d : ℕ} {Q : TriadicCube d} {C : ℝ} {u g : Vec d → ℝ} {M : ℕ}
    (hproj : CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C u g M)
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hC : 0 ≤ C) :
    CubeLocalMultiscalePoincareEstimate Q
      ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) u g M := by
  intro j hj R hR
  have hdual : CubeDualMeanZeroPoincareEstimate R C u (cubeProjection R (M - j) g) :=
    hproj j hj R hR
  have hprojMem :
      MeasureTheory.MemLp (cubeProjection R (M - j) g)
        (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
    cubeProjection_memLp R (M - j) (2 : ℝ≥0∞) g
  have htail :
      cubeBesovCircNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (cubeProjection R (M - j) g) ≤
        (3 / 2 : ℝ) *
          cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (M - j) g :=
    cubeBesovCircNorm_projection_le_three_halves_mul_cubeBesovCircPartialNorm_on_descendants_of_memLp
      (Q := Q) (u := g) (M := M) hg j hj R hR
  have hnote_nonneg : 0 ≤ C * (3 : ℝ) ^ ((d : ℝ) + 1) := by
    exact mul_nonneg hC (Real.rpow_nonneg (by positivity) _)
  calc
    cubeBesovOscillation R (2 : ℝ≥0∞) u
        ≤ C * (3 : ℝ) ^ ((d : ℝ) + 1) *
            cubeBesovCircNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (cubeProjection R (M - j) g) :=
          hdual.to_circNorm hprojMem hC
    _ ≤ C * (3 : ℝ) ^ ((d : ℝ) + 1) *
          ((3 / 2 : ℝ) *
            cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (M - j) g) := by
          exact mul_le_mul_of_nonneg_left htail hnote_nonneg
    _ = ((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (M - j) g := by
          ring

theorem CubeDescendantProjectedDualMeanZeroPoincareEstimate.to_input
    {d : ℕ} {Q : TriadicCube d} {C : ℝ} {u g : Vec d → ℝ} {M : ℕ}
    (hproj : CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C u g M)
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hC : 0 ≤ C) :
    CubeMultiscalePoincareInput Q
      (((3 / 2 : ℝ) * C * (3 : ℝ) ^ ((d : ℝ) + 1))) u g M := by
  exact (hproj.to_localEstimate hg hC).to_input

theorem cubeBesovCircDepthWeight_eq_of_mem_descendantsAtDepth {d : ℕ} {Q R : TriadicCube d}
    {j : ℕ} (hR : R ∈ descendantsAtDepth Q j) (s : ℝ) (n : ℕ) :
    cubeBesovCircDepthWeight R s n = cubeBesovCircDepthWeight Q s (j + n) := by
  have hbase :
      cubeScaleFactor R / (3 : ℝ) ^ n = cubeScaleFactor Q / (3 : ℝ) ^ (j + n) := by
    rw [cubeScaleFactor_eq_div_pow_of_mem_descendantsAtDepth hR]
    rw [pow_add]
    field_simp
  simp [cubeBesovCircDepthWeight, hbase]

theorem sq_cubeBesovCircDepthSeminorm_two {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (u : Vec d → ℝ) (j : ℕ) :
    (cubeBesovCircDepthSeminorm Q s (2 : ℝ≥0∞) u j) ^ 2 =
      (cubeBesovCircDepthWeight Q s j) ^ 2 * cubeBesovCircDepthAverage Q (2 : ℝ≥0∞) u j := by
  have hW : 0 ≤ cubeBesovCircDepthWeight Q s j := cubeBesovCircDepthWeight_nonneg Q s j
  have hA : 0 ≤ cubeBesovCircDepthAverage Q (2 : ℝ≥0∞) u j :=
    cubeBesovCircDepthAverage_nonneg Q (2 : ℝ≥0∞) u j
  calc
    (cubeBesovCircDepthSeminorm Q s (2 : ℝ≥0∞) u j) ^ 2
        = (cubeBesovCircDepthWeight Q s j *
            (cubeBesovCircDepthAverage Q (2 : ℝ≥0∞) u j) ^ (1 / ((2 : ℝ≥0∞).toReal))) ^ 2 := by
              simp [cubeBesovCircDepthSeminorm]
    _ = (cubeBesovCircDepthWeight Q s j) ^ 2 *
          ((cubeBesovCircDepthAverage Q (2 : ℝ≥0∞) u j) ^
            (1 / ((2 : ℝ≥0∞).toReal))) ^ 2 := by
          ring
    _ = (cubeBesovCircDepthWeight Q s j) ^ 2 * cubeBesovCircDepthAverage Q (2 : ℝ≥0∞) u j := by
          congr 1
          have htwo : ((2 : ℝ≥0∞).toReal : ℝ) = 2 := by norm_num
          rw [htwo]
          rw [← Real.rpow_natCast, ← Real.rpow_mul hA]
          norm_num

theorem descendantsAverage_sq_cubeBesovCircDepthSeminorm_eq_shifted {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → ℝ) (j n : ℕ) :
    descendantsAverage Q j (fun R => (cubeBesovCircDepthSeminorm R 1 (2 : ℝ≥0∞) u n) ^ 2) =
      (cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞) u (j + n)) ^ 2 := by
  calc
    descendantsAverage Q j (fun R => (cubeBesovCircDepthSeminorm R 1 (2 : ℝ≥0∞) u n) ^ 2)
        = descendantsAverage Q j
            (fun R =>
              (cubeBesovCircDepthWeight Q 1 (j + n)) ^ 2 *
                cubeBesovCircDepthAverage R (2 : ℝ≥0∞) u n) := by
              unfold descendantsAverage
              refine congrArg (fun t : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
              refine Finset.sum_congr rfl ?_
              intro R hR
              rw [sq_cubeBesovCircDepthSeminorm_two]
              rw [cubeBesovCircDepthWeight_eq_of_mem_descendantsAtDepth hR]
    _ = (cubeBesovCircDepthWeight Q 1 (j + n)) ^ 2 *
          descendantsAverage Q j (fun R => cubeBesovCircDepthAverage R (2 : ℝ≥0∞) u n) := by
          rw [descendantsAverage_mul_left Q j ((cubeBesovCircDepthWeight Q 1 (j + n)) ^ 2)
            (fun R => cubeBesovCircDepthAverage R (2 : ℝ≥0∞) u n)]
    _ = (cubeBesovCircDepthWeight Q 1 (j + n)) ^ 2 *
          cubeBesovCircDepthAverage Q (2 : ℝ≥0∞) u (j + n) := by
          rw [cubeBesovCircDepthAverage_add_eq_descendantsAverage_cubeBesovCircDepthAverage]
    _ = (cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞) u (j + n)) ^ 2 := by
          symm
          exact sq_cubeBesovCircDepthSeminorm_two Q 1 u (j + n)

theorem descendantsAverage_L2_sum_le_sum_descendantsAverage_L2 {d : ℕ} {ι : Type*}
    (Q : TriadicCube d) (j : ℕ) (s : Finset ι) (A : TriadicCube d → ι → ℝ)
    (hA : ∀ R ∈ descendantsAtDepth Q j, ∀ i ∈ s, 0 ≤ A R i) :
    (descendantsAverage Q j (fun R => (∑ i ∈ s, A R i) ^ 2)) ^ (1 / 2 : ℝ) ≤
      ∑ i ∈ s, (descendantsAverage Q j (fun R => (A R i) ^ 2)) ^ (1 / 2 : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [descendantsAverage]
  | @insert a s ha ih =>
      let D : Finset (TriadicCube d) := descendantsAtDepth Q j
      let c : ℝ := ((D.card : ℝ)⁻¹)
      have hc : 0 ≤ c := by
        dsimp [c]
        exact inv_nonneg.mpr (by positivity)
      have hsum_nonneg : ∀ R ∈ D, 0 ≤ ∑ i ∈ s, A R i := by
        intro R hR
        exact Finset.sum_nonneg fun i hi =>
          hA R (by simpa [D] using hR) i (Finset.mem_insert_of_mem hi)
      have hsum_sq_nonneg : 0 ≤ ∑ R ∈ D, (∑ i ∈ s, A R i) ^ 2 := by
        exact Finset.sum_nonneg fun R hR => sq_nonneg _
      have hsingle_sq_nonneg : 0 ≤ ∑ R ∈ D, (A R a) ^ 2 := by
        exact Finset.sum_nonneg fun R hR => sq_nonneg _
      have hinsert_sq_nonneg : 0 ≤ ∑ R ∈ D, (∑ i ∈ insert a s, A R i) ^ 2 := by
        exact Finset.sum_nonneg fun R hR => sq_nonneg _
      have hLp :
          (∑ R ∈ D, (A R a + ∑ i ∈ s, A R i) ^ 2) ^ (1 / 2 : ℝ) ≤
            (∑ R ∈ D, (A R a) ^ 2) ^ (1 / 2 : ℝ) +
              (∑ R ∈ D, (∑ i ∈ s, A R i) ^ 2) ^ (1 / 2 : ℝ) := by
        simpa using
          (Real.Lp_add_le_of_nonneg
            (s := D)
            (f := fun R => A R a)
            (g := fun R => ∑ i ∈ s, A R i)
            (p := (2 : ℝ))
            (by norm_num)
            (fun R hR => hA R (by simpa [D] using hR) a (by simp [ha]))
            hsum_nonneg)
      calc
        (descendantsAverage Q j (fun R => (∑ i ∈ insert a s, A R i) ^ 2)) ^ (1 / 2 : ℝ)
            = c ^ (1 / 2 : ℝ) * (∑ R ∈ D, (A R a + ∑ i ∈ s, A R i) ^ 2) ^ (1 / 2 : ℝ) := by
                have hmul :
                    (c * ∑ R ∈ D, (∑ i ∈ insert a s, A R i) ^ 2) ^ (1 / 2 : ℝ) =
                      c ^ (1 / 2 : ℝ) * (∑ R ∈ D, (∑ i ∈ insert a s, A R i) ^ 2) ^ (1 / 2 : ℝ) :=
                  Real.mul_rpow hc hinsert_sq_nonneg
                simpa [descendantsAverage, D, c, Finset.sum_insert, ha] using hmul
        _ ≤ c ^ (1 / 2 : ℝ) * (∑ R ∈ D, (A R a) ^ 2) ^ (1 / 2 : ℝ) +
              c ^ (1 / 2 : ℝ) * (∑ R ∈ D, (∑ i ∈ s, A R i) ^ 2) ^ (1 / 2 : ℝ) := by
              have hc_rpow : 0 ≤ c ^ (1 / 2 : ℝ) := Real.rpow_nonneg hc _
              have hmul := mul_le_mul_of_nonneg_left hLp hc_rpow
              simpa [mul_add] using hmul
        _ = (descendantsAverage Q j (fun R => (A R a) ^ 2)) ^ (1 / 2 : ℝ) +
              c ^ (1 / 2 : ℝ) * (∑ R ∈ D, (∑ i ∈ s, A R i) ^ 2) ^ (1 / 2 : ℝ) := by
              rw [← Real.mul_rpow hc hsingle_sq_nonneg]
              simp [descendantsAverage, D, c]
        _ = (descendantsAverage Q j (fun R => (A R a) ^ 2)) ^ (1 / 2 : ℝ) +
              (descendantsAverage Q j (fun R => (∑ i ∈ s, A R i) ^ 2)) ^ (1 / 2 : ℝ) := by
              rw [← Real.mul_rpow hc hsum_sq_nonneg]
              simp [descendantsAverage, D, c]
        _ ≤ (descendantsAverage Q j (fun R => (A R a) ^ 2)) ^ (1 / 2 : ℝ) +
              ∑ i ∈ s, (descendantsAverage Q j (fun R => (A R i) ^ 2)) ^ (1 / 2 : ℝ) := by
              exact add_le_add le_rfl
                (ih (fun R hR i hi => hA R hR i (Finset.mem_insert_of_mem hi)))
        _ = ∑ i ∈ insert a s, (descendantsAverage Q j (fun R => (A R i) ^ 2)) ^ (1 / 2 : ℝ) := by
              simp [Finset.sum_insert, ha]

theorem cubeBesovDepthSeminorm_two_le_sum_shifted_of_local_circ_bound {d : ℕ}
    (Q : TriadicCube d) (s C : ℝ) (u g : Vec d → ℝ) (j N : ℕ)
    (hC : 0 ≤ C)
    (hlocal : ∀ R ∈ descendantsAtDepth Q j,
      cubeBesovOscillation R (2 : ℝ≥0∞) u ≤
        C * ∑ n ∈ Finset.range (N + 1), cubeBesovCircDepthSeminorm R 1 (2 : ℝ≥0∞) g n) :
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j ≤
      C * cubeBesovDepthWeight Q s j *
        ∑ n ∈ Finset.range (N + 1), cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞) g (j + n) := by
  let S : TriadicCube d → ℝ := fun R =>
    ∑ n ∈ Finset.range (N + 1), cubeBesovCircDepthSeminorm R 1 (2 : ℝ≥0∞) g n
  have hS_nonneg : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ S R := by
    intro R hR
    exact Finset.sum_nonneg fun n hn =>
      cubeBesovCircDepthSeminorm_nonneg R 1 (2 : ℝ≥0∞) g n
  have hsq_bound :
      descendantsAverage Q j (fun R => (cubeBesovOscillation R (2 : ℝ≥0∞) u) ^ 2) ≤
        descendantsAverage Q j (fun R => (C * S R) ^ 2) := by
    refine descendantsAverage_le_descendantsAverage Q j ?_
    intro R hR
    have hosc_nonneg : 0 ≤ cubeBesovOscillation R (2 : ℝ≥0∞) u :=
      cubeBesovOscillation_nonneg R (2 : ℝ≥0∞) u
    have hCS_nonneg : 0 ≤ C * S R := mul_nonneg hC (hS_nonneg R hR)
    nlinarith [hlocal R hR, hosc_nonneg, hCS_nonneg]
  have hleft_nonneg :
      0 ≤ descendantsAverage Q j (fun R => (cubeBesovOscillation R (2 : ℝ≥0∞) u) ^ 2) := by
    exact descendantsAverage_nonneg Q j _ fun R hR => sq_nonneg _
  have hright_nonneg :
      0 ≤ descendantsAverage Q j (fun R => (C * S R) ^ 2) := by
    exact descendantsAverage_nonneg Q j _ fun R hR => sq_nonneg _
  have hroot_bound :
      (descendantsAverage Q j (fun R => (cubeBesovOscillation R (2 : ℝ≥0∞) u) ^ 2)) ^ (1 / 2 : ℝ) ≤
        (descendantsAverage Q j (fun R => (C * S R) ^ 2)) ^ (1 / 2 : ℝ) := by
    exact Real.rpow_le_rpow hleft_nonneg hsq_bound (by positivity)
  have hfactor :
      descendantsAverage Q j (fun R => (C * S R) ^ 2) =
        C ^ 2 * descendantsAverage Q j (fun R => (S R) ^ 2) := by
    calc
      descendantsAverage Q j (fun R => (C * S R) ^ 2)
          = descendantsAverage Q j (fun R => C ^ 2 * (S R) ^ 2) := by
              refine congrArg (descendantsAverage Q j) ?_
              funext R
              ring
      _ = C ^ 2 * descendantsAverage Q j (fun R => (S R) ^ 2) := by
            rw [descendantsAverage_mul_left Q j (C ^ 2) (fun R => (S R) ^ 2)]
  have hSsq_nonneg : 0 ≤ descendantsAverage Q j (fun R => (S R) ^ 2) := by
    exact descendantsAverage_nonneg Q j _ fun R hR => sq_nonneg _
  have hroot_factor :
      (descendantsAverage Q j (fun R => (C * S R) ^ 2)) ^ (1 / 2 : ℝ) =
        C * (descendantsAverage Q j (fun R => (S R) ^ 2)) ^ (1 / 2 : ℝ) := by
    rw [hfactor, Real.mul_rpow (sq_nonneg C) hSsq_nonneg]
    congr 1
    rw [sq_rpow_half_eq_of_nonneg hC]
  have hM :
      (descendantsAverage Q j (fun R => (S R) ^ 2)) ^ (1 / 2 : ℝ) ≤
        ∑ n ∈ Finset.range (N + 1),
          (descendantsAverage Q j
            (fun R => (cubeBesovCircDepthSeminorm R 1 (2 : ℝ≥0∞) g n) ^ 2)) ^ (1 / 2 : ℝ) := by
    exact descendantsAverage_L2_sum_le_sum_descendantsAverage_L2 Q j (Finset.range (N + 1))
      (fun R n => cubeBesovCircDepthSeminorm R 1 (2 : ℝ≥0∞) g n)
      (fun R hR n hn => cubeBesovCircDepthSeminorm_nonneg R 1 (2 : ℝ≥0∞) g n)
  have hshift :
      ∀ n ∈ Finset.range (N + 1),
        (descendantsAverage Q j
          (fun R => (cubeBesovCircDepthSeminorm R 1 (2 : ℝ≥0∞) g n) ^ 2)) ^ (1 / 2 : ℝ) =
            cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞) g (j + n) := by
    intro n hn
    have hnonneg : 0 ≤ cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞) g (j + n) :=
      cubeBesovCircDepthSeminorm_nonneg Q 1 (2 : ℝ≥0∞) g (j + n)
    rw [descendantsAverage_sq_cubeBesovCircDepthSeminorm_eq_shifted]
    exact sq_rpow_half_eq_of_nonneg hnonneg
  have hsum_reindex :
      ∑ n ∈ Finset.range (N + 1),
        (descendantsAverage Q j
          (fun R => (cubeBesovCircDepthSeminorm R 1 (2 : ℝ≥0∞) g n) ^ 2)) ^ (1 / 2 : ℝ)
        =
      ∑ n ∈ Finset.range (N + 1), cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞) g (j + n) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    exact hshift n hn
  have hweight_nonneg : 0 ≤ cubeBesovDepthWeight Q s j := cubeBesovDepthWeight_nonneg Q s j
  calc
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j
        = cubeBesovDepthWeight Q s j *
            (descendantsAverage Q j (fun R => (cubeBesovOscillation R (2 : ℝ≥0∞) u) ^ 2)) ^ (1 / 2 : ℝ) := by
              simp [cubeBesovDepthSeminorm, cubeBesovDepthAverage]
    _ ≤ cubeBesovDepthWeight Q s j *
          (descendantsAverage Q j (fun R => (C * S R) ^ 2)) ^ (1 / 2 : ℝ) := by
            gcongr
    _ = cubeBesovDepthWeight Q s j *
          (C * (descendantsAverage Q j (fun R => (S R) ^ 2)) ^ (1 / 2 : ℝ)) := by
            rw [hroot_factor]
    _ = C * cubeBesovDepthWeight Q s j *
          (descendantsAverage Q j (fun R => (S R) ^ 2)) ^ (1 / 2 : ℝ) := by
            ring
    _ ≤ C * cubeBesovDepthWeight Q s j *
          (∑ n ∈ Finset.range (N + 1),
            (descendantsAverage Q j
              (fun R => (cubeBesovCircDepthSeminorm R 1 (2 : ℝ≥0∞) g n) ^ 2)) ^ (1 / 2 : ℝ)) := by
            gcongr
    _ = C * cubeBesovDepthWeight Q s j *
          ∑ n ∈ Finset.range (N + 1), cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞) g (j + n) := by
            rw [hsum_reindex]

theorem shifted_cubeBesovCircDepthSum_le_cubeBesovCircPartialNorm_one {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (j N : ℕ) (u : Vec d → ℝ) :
    ∑ n ∈ Finset.range (N + 1), cubeBesovCircDepthSeminorm Q s p u (j + n) ≤
      cubeBesovCircPartialNorm Q s p (1 : ℝ≥0∞) (j + N) u := by
  have hsubset : Finset.Ico j (j + N + 1) ⊆ Finset.range (j + N + 1) := by
    intro n hn
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hn).2
  calc
    ∑ n ∈ Finset.range (N + 1), cubeBesovCircDepthSeminorm Q s p u (j + n)
        = Finset.sum (Finset.Ico j (j + N + 1)) (fun n => cubeBesovCircDepthSeminorm Q s p u n) := by
            simpa [Nat.add_assoc] using
              (Finset.sum_Ico_eq_sum_range
                (f := fun n => cubeBesovCircDepthSeminorm Q s p u n)
                (m := j) (n := j + N + 1)).symm
    _ ≤ Finset.sum (Finset.range (j + N + 1)) (fun n => cubeBesovCircDepthSeminorm Q s p u n) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
          intro n hn _
          exact cubeBesovCircDepthSeminorm_nonneg Q s p u n
    _ = cubeBesovCircPartialNorm Q s p (1 : ℝ≥0∞) (j + N) u := by
          symm
          rw [cubeBesovCircPartialNorm_one_eq_sum]


end Homogenization
