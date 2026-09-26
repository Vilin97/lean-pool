/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Besov.Poincare.HarmonicGradient.Descendants

/-! # Full Circ -/

@[expose] public section

namespace Homogenization

open scoped BigOperators ENNReal

variable {d : ℕ}

/-! # Full-Circ Vector Poincare Estimates -/

/-- A descendant full-dual vector Poincare estimate gives a descendant local
full-circ estimate after applying circ domination componentwise. -/
theorem CubeDescendantDualFullVectorPoincareEstimate.to_localFullCircEstimate
    {Q : TriadicCube d} {C : ℝ} {u : Vec d → ℝ} {G : Vec d → Vec d} {M : ℕ}
    (hfull : CubeDescendantDualFullVectorPoincareEstimate Q C u G M)
    (hG :
      ∀ i : Fin d,
        MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hC : 0 ≤ C) :
    CubeLocalFullCircPoincareVectorEstimate Q
      (C * (3 : ℝ) ^ ((d : ℝ) + 1)) u G M := by
  intro j hj R hR
  let K : ℝ := (3 : ℝ) ^ ((d : ℝ) + 1)
  have hdual := hfull j hj R hR
  have hGR :
      ∀ i : Fin d,
        MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞)
          (normalizedCubeMeasure R) := by
    intro i
    exact memLp_on_descendant_of_memLp (Q := Q) (R := R) (j := j) hR (hG i)
  have hconj_eq :
      cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq
        (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hcoord :
      ∀ i : Fin d,
        cubeBesovDualFullNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => G x i) ≤
          K * cubeBesovCircNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => G x i) := by
    intro i
    simpa [K] using
      cubeBesovDualFullNorm_le_note_constant_mul_cubeBesovCircNorm
        (Q := R) (s := 1) (p := (2 : ℝ≥0∞)) (q := (1 : ℝ≥0∞))
        (u := fun x => G x i)
        (by norm_num) (hGR i) (by norm_num) (by norm_num)
        (by intro htop; simp [hconj_eq] at htop) (by norm_num)
  have hsum :
      ∑ i : Fin d,
          cubeBesovDualFullNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => G x i) ≤
        ∑ i : Fin d,
          K * cubeBesovCircNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => G x i) := by
    exact Finset.sum_le_sum fun i _ => hcoord i
  calc
    cubeBesovOscillation R (2 : ℝ≥0∞) u
        ≤ C * ∑ i : Fin d,
            cubeBesovDualFullNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
              (fun x => G x i) := hdual
    _ ≤ C * ∑ i : Fin d,
          K * cubeBesovCircNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => G x i) := by
          exact mul_le_mul_of_nonneg_left hsum hC
    _ = (C * K) * ∑ i : Fin d,
          cubeBesovCircNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => G x i) := by
          rw [← Finset.mul_sum]
          ring
    _ = (C * (3 : ℝ) ^ ((d : ℝ) + 1)) * ∑ i : Fin d,
          cubeBesovCircNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => G x i) := by
          simp [K]

/-- For `q = 1`, finite circ partial norms increase to the full circ norm. -/
theorem tendsto_cubeBesovCircPartialNorm_one_succ_to_cubeBesovCircNorm
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ)
    (hBdd : BddAbove (cubeBesovCircNormValueSet Q s p (1 : ℝ≥0∞) u)) :
    Filter.Tendsto
      (fun N : ℕ => cubeBesovCircPartialNorm Q s p (1 : ℝ≥0∞) (N + 1) u)
      Filter.atTop
      (nhds (cubeBesovCircNorm Q s p (1 : ℝ≥0∞) u)) := by
  have hmono :
      Monotone
        (fun N : ℕ =>
          cubeBesovCircPartialNorm Q s p (1 : ℝ≥0∞) (N + 1) u) := by
    intro M N hMN
    exact cubeBesovCircPartialNorm_one_mono Q s p u (Nat.succ_le_succ hMN)
  have hbdd :
      BddAbove
        (Set.range
          fun N : ℕ =>
            cubeBesovCircPartialNorm Q s p (1 : ℝ≥0∞) (N + 1) u) := by
    rcases hBdd with ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro y hy
    rcases hy with ⟨N, rfl⟩
    exact hB ⟨N, by simp [cubeBesovCircNormEntry]⟩
  have ht := tendsto_atTop_ciSup hmono hbdd
  have hiSup_eq :
      (⨆ N : ℕ, cubeBesovCircPartialNorm Q s p (1 : ℝ≥0∞) (N + 1) u) =
        cubeBesovCircNorm Q s p (1 : ℝ≥0∞) u := by
    rw [cubeBesovCircNorm]
    unfold iSup
    congr 1
  rw [← hiSup_eq]
  exact ht

/-- Finite local circ partial sums, averaged over descendants and shifted to
the parent, are controlled by the full parent circ norm. -/
theorem cubeBesovDepthWeight_mul_L2_descendantsAverage_sum_components_circPartialNorm_le_sum_circNorm
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (G : Vec d → Vec d) (j N : ℕ)
    (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hG :
      ∀ i : Fin d,
        MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovDepthWeight Q s j *
        (descendantsAverage Q j
          (fun R =>
            (∑ i : Fin d,
              cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (N + 1)
                (fun x => G x i)) ^ 2)) ^ (1 / 2 : ℝ) ≤
      ∑ i : Fin d,
        cubeBesovCircNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => G x i) := by
  classical
  let I : Finset (Fin d × ℕ) :=
    (Finset.univ : Finset (Fin d)).product (Finset.range (N + 1 + 1))
  let S : TriadicCube d → ℝ := fun R =>
    ∑ p ∈ I,
      cubeBesovCircDepthSeminorm R 1 (2 : ℝ≥0∞) (fun x => G x p.1) p.2
  have hS_eq :
      ∀ R,
        (∑ i : Fin d,
          cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (N + 1)
            (fun x => G x i)) = S R := by
    intro R
    simp [S, I, cubeBesovCircPartialNorm_one_eq_sum, Finset.sum_product]
  have hM :
      (descendantsAverage Q j (fun R => (S R) ^ 2)) ^ (1 / 2 : ℝ) ≤
        ∑ p ∈ I,
          (descendantsAverage Q j
            (fun R =>
              (cubeBesovCircDepthSeminorm R 1 (2 : ℝ≥0∞)
                (fun x => G x p.1) p.2) ^ 2)) ^ (1 / 2 : ℝ) := by
    exact descendantsAverage_L2_sum_le_sum_descendantsAverage_L2 Q j I
      (fun R p =>
        cubeBesovCircDepthSeminorm R 1 (2 : ℝ≥0∞) (fun x => G x p.1) p.2)
      (fun R hR p hp =>
        cubeBesovCircDepthSeminorm_nonneg R 1 (2 : ℝ≥0∞) (fun x => G x p.1) p.2)
  have hshift :
      ∀ p ∈ I,
        (descendantsAverage Q j
          (fun R =>
            (cubeBesovCircDepthSeminorm R 1 (2 : ℝ≥0∞)
              (fun x => G x p.1) p.2) ^ 2)) ^ (1 / 2 : ℝ) =
          cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => G x p.1) (j + p.2) := by
    intro p hp
    have hnonneg :
        0 ≤ cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞)
          (fun x => G x p.1) (j + p.2) :=
      cubeBesovCircDepthSeminorm_nonneg Q 1 (2 : ℝ≥0∞) (fun x => G x p.1) (j + p.2)
    rw [descendantsAverage_sq_cubeBesovCircDepthSeminorm_eq_shifted]
    exact sq_rpow_half_eq_of_nonneg hnonneg
  have hsum_reindex :
      ∑ p ∈ I,
        (descendantsAverage Q j
          (fun R =>
            (cubeBesovCircDepthSeminorm R 1 (2 : ℝ≥0∞)
              (fun x => G x p.1) p.2) ^ 2)) ^ (1 / 2 : ℝ)
        =
      ∑ p ∈ I,
        cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => G x p.1) (j + p.2) := by
    refine Finset.sum_congr rfl ?_
    intro p hp
    exact hshift p hp
  have hweighted :
      cubeBesovDepthWeight Q s j *
        ∑ p ∈ I,
          cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => G x p.1) (j + p.2)
        =
      ∑ i : Fin d, ∑ n ∈ Finset.range (N + 1 + 1),
        ((3 : ℝ) ^ (-s)) ^ n *
          cubeBesovCircDepthSeminorm Q (1 - s) (2 : ℝ≥0∞)
            (fun x => G x i) (j + n) := by
    rw [Finset.mul_sum]
    simp [I, Finset.sum_product,
      cubeBesovDepthWeight_mul_cubeBesovCircDepthSeminorm_shift_eq_geom_mul]
  have hweight_nonneg : 0 ≤ cubeBesovDepthWeight Q s j :=
    cubeBesovDepthWeight_nonneg Q s j
  have hleft :
      cubeBesovDepthWeight Q s j *
          (descendantsAverage Q j
            (fun R =>
              (∑ i : Fin d,
                cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (N + 1)
                  (fun x => G x i)) ^ 2)) ^ (1 / 2 : ℝ) ≤
        cubeBesovDepthWeight Q s j *
          ∑ p ∈ I,
            cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => G x p.1) (j + p.2) := by
    rw [show descendantsAverage Q j
          (fun R =>
            (∑ i : Fin d,
              cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (N + 1)
                (fun x => G x i)) ^ 2) =
        descendantsAverage Q j (fun R => (S R) ^ 2) by
          congr 1
          funext R
          rw [hS_eq R]]
    exact mul_le_mul_of_nonneg_left (hM.trans_eq hsum_reindex) hweight_nonneg
  have hr_nonneg : 0 ≤ (3 : ℝ) ^ (-s) :=
    Real.rpow_nonneg (by positivity) _
  have hr_le_one : (3 : ℝ) ^ (-s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have htail :
      ∑ i : Fin d, ∑ n ∈ Finset.range (N + 1 + 1),
        ((3 : ℝ) ^ (-s)) ^ n *
          cubeBesovCircDepthSeminorm Q (1 - s) (2 : ℝ≥0∞)
            (fun x => G x i) (j + n) ≤
      ∑ i : Fin d,
        cubeBesovCircNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => G x i) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hweighted_le :
        ∑ n ∈ Finset.range (N + 1 + 1),
          ((3 : ℝ) ^ (-s)) ^ n *
            cubeBesovCircDepthSeminorm Q (1 - s) (2 : ℝ≥0∞)
              (fun x => G x i) (j + n) ≤
        ∑ n ∈ Finset.range (N + 1 + 1),
          cubeBesovCircDepthSeminorm Q (1 - s) (2 : ℝ≥0∞)
            (fun x => G x i) (j + n) := by
      refine Finset.sum_le_sum ?_
      intro n hn
      have hpow_le : ((3 : ℝ) ^ (-s)) ^ n ≤ 1 :=
        pow_le_one₀ hr_nonneg hr_le_one
      simpa using
        mul_le_mul_of_nonneg_right hpow_le
          (cubeBesovCircDepthSeminorm_nonneg Q (1 - s) (2 : ℝ≥0∞)
            (fun x => G x i) (j + n))
    have hshifted :
        ∑ n ∈ Finset.range (N + 1 + 1),
          cubeBesovCircDepthSeminorm Q (1 - s) (2 : ℝ≥0∞)
            (fun x => G x i) (j + n) ≤
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (j + (N + 1)) (fun x => G x i) :=
      shifted_cubeBesovCircDepthSum_le_cubeBesovCircPartialNorm_one
        Q (1 - s) (2 : ℝ≥0∞) j (N + 1) (fun x => G x i)
    have hBdd :
        BddAbove
          (cubeBesovCircNormValueSet Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => G x i)) :=
      cubeBesovCircNormValueSet_bddAbove_of_memLp
        Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => G x i)
        (by linarith) (hG i) (by norm_num) (by norm_num) (by norm_num)
    have hpartial_full :
        cubeBesovCircPartialNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (j + (N + 1)) (fun x => G x i) ≤
          cubeBesovCircNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => G x i) := by
      have hmono :=
        cubeBesovCircPartialNorm_one_mono Q (1 - s) (2 : ℝ≥0∞)
          (fun x => G x i) (Nat.le_succ (j + (N + 1)))
      have hle :=
        cubeBesovCircPartialNorm_le_cubeBesovCircNorm
          Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => G x i)
          (by norm_num) hBdd (j + (N + 1))
      exact hmono.trans hle
    exact hweighted_le.trans (hshifted.trans hpartial_full)
  calc
    cubeBesovDepthWeight Q s j *
        (descendantsAverage Q j
          (fun R =>
            (∑ i : Fin d,
              cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (N + 1)
                (fun x => G x i)) ^ 2)) ^ (1 / 2 : ℝ)
        ≤ cubeBesovDepthWeight Q s j *
          ∑ p ∈ I,
            cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => G x p.1)
              (j + p.2) := hleft
    _ = ∑ i : Fin d, ∑ n ∈ Finset.range (N + 1 + 1),
        ((3 : ℝ) ^ (-s)) ^ n *
          cubeBesovCircDepthSeminorm Q (1 - s) (2 : ℝ≥0∞)
            (fun x => G x i) (j + n) := hweighted
    _ ≤ ∑ i : Fin d,
        cubeBesovCircNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => G x i) := htail

/-- The finite local partial-sum averages converge to the corresponding full
local circ averages. -/
theorem tendsto_cubeBesovDepthWeight_mul_L2_descendantsAverage_sum_components_circPartialNorm_to_circNorm
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (G : Vec d → Vec d) (j : ℕ)
    (hG :
      ∀ i : Fin d,
        MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    Filter.Tendsto
      (fun N : ℕ =>
        cubeBesovDepthWeight Q s j *
          (descendantsAverage Q j
            (fun R =>
              (∑ i : Fin d,
                cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (N + 1)
                  (fun x => G x i)) ^ 2)) ^ (1 / 2 : ℝ))
      Filter.atTop
      (nhds
        (cubeBesovDepthWeight Q s j *
          (descendantsAverage Q j
            (fun R =>
              (∑ i : Fin d,
                cubeBesovCircNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                  (fun x => G x i)) ^ 2)) ^ (1 / 2 : ℝ))) := by
  have havg :
      Filter.Tendsto
        (fun N : ℕ =>
          descendantsAverage Q j
            (fun R =>
              (∑ i : Fin d,
                cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (N + 1)
                  (fun x => G x i)) ^ 2))
        Filter.atTop
        (nhds
          (descendantsAverage Q j
            (fun R =>
              (∑ i : Fin d,
                cubeBesovCircNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                  (fun x => G x i)) ^ 2))) := by
    unfold descendantsAverage
    refine Filter.Tendsto.const_mul _ ?_
    refine tendsto_finsetSum (descendantsAtDepth Q j) ?_
    intro R hR
    have hsum :
        Filter.Tendsto
          (fun N : ℕ =>
            ∑ i : Fin d,
              cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (N + 1)
                (fun x => G x i))
          Filter.atTop
          (nhds
            (∑ i : Fin d,
              cubeBesovCircNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                (fun x => G x i))) := by
      refine tendsto_finsetSum Finset.univ ?_
      intro i hi
      have hGR :
          MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞)
            (normalizedCubeMeasure R) :=
        memLp_on_descendant_of_memLp (Q := Q) (R := R) (j := j) hR (hG i)
      have hBdd :
          BddAbove
            (cubeBesovCircNormValueSet R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
              (fun x => G x i)) :=
        cubeBesovCircNormValueSet_bddAbove_of_memLp
          R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => G x i)
          (by norm_num) hGR (by norm_num) (by norm_num) (by norm_num)
      exact
        tendsto_cubeBesovCircPartialNorm_one_succ_to_cubeBesovCircNorm
          R 1 (2 : ℝ≥0∞) (fun x => G x i) hBdd
    simpa using hsum.pow 2
  have hroot :
      Filter.Tendsto
        (fun N : ℕ =>
          (descendantsAverage Q j
            (fun R =>
              (∑ i : Fin d,
                cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (N + 1)
                  (fun x => G x i)) ^ 2)) ^ (1 / 2 : ℝ))
        Filter.atTop
        (nhds
          ((descendantsAverage Q j
            (fun R =>
              (∑ i : Fin d,
                cubeBesovCircNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                  (fun x => G x i)) ^ 2)) ^ (1 / 2 : ℝ))) := by
    exact
      (Real.continuous_rpow_const (by norm_num : 0 ≤ (1 / 2 : ℝ))).tendsto _ |>.comp havg
  exact hroot.const_mul _

/-- The full local circ averages over descendants are controlled by the full
parent circ norm. -/
theorem cubeBesovDepthWeight_mul_L2_descendantsAverage_sum_components_circNorm_le_sum_circNorm
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (G : Vec d → Vec d) (j : ℕ)
    (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hG :
      ∀ i : Fin d,
        MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovDepthWeight Q s j *
        (descendantsAverage Q j
          (fun R =>
            (∑ i : Fin d,
              cubeBesovCircNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                (fun x => G x i)) ^ 2)) ^ (1 / 2 : ℝ) ≤
      ∑ i : Fin d,
        cubeBesovCircNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => G x i) := by
  have htend :=
    tendsto_cubeBesovDepthWeight_mul_L2_descendantsAverage_sum_components_circPartialNorm_to_circNorm
      Q s G j hG
  exact le_of_tendsto htend
    (Filter.Eventually.of_forall fun N =>
      cubeBesovDepthWeight_mul_L2_descendantsAverage_sum_components_circPartialNorm_le_sum_circNorm
        Q s G j N hs0 hs1 hG)

/-- Depthwise positive Besov control from a vector local full-circ Poincare
bound. -/
theorem cubeBesovDepthSeminorm_two_le_sum_circNorm_of_vector_local_full_circ_bound
    {d : ℕ} (Q : TriadicCube d) (s C : ℝ) (u : Vec d → ℝ) (G : Vec d → Vec d)
    (j : ℕ) (hs0 : 0 ≤ s) (hs1 : s < 1) (hC : 0 ≤ C)
    (hG :
      ∀ i : Fin d,
        MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hlocal : ∀ R ∈ descendantsAtDepth Q j,
      cubeBesovOscillation R (2 : ℝ≥0∞) u ≤
        C * ∑ i : Fin d,
          cubeBesovCircNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => G x i)) :
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j ≤
      C * ∑ i : Fin d,
        cubeBesovCircNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => G x i) := by
  let S : TriadicCube d → ℝ := fun R =>
    ∑ i : Fin d,
      cubeBesovCircNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => G x i)
  have hS_nonneg : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ S R := by
    intro R hR
    refine Finset.sum_nonneg ?_
    intro i hi
    have hGR :
        MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞)
          (normalizedCubeMeasure R) :=
      memLp_on_descendant_of_memLp (Q := Q) (R := R) (j := j) hR (hG i)
    have hBdd :
        BddAbove
          (cubeBesovCircNormValueSet R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => G x i)) :=
      cubeBesovCircNormValueSet_bddAbove_of_memLp
        R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => G x i)
        (by norm_num) hGR (by norm_num) (by norm_num) (by norm_num)
    exact cubeBesovCircNorm_nonneg R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => G x i) hBdd
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
  have hroot_bound :
      (descendantsAverage Q j (fun R => (cubeBesovOscillation R (2 : ℝ≥0∞) u) ^ 2)) ^
          (1 / 2 : ℝ) ≤
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
  have hweight_nonneg : 0 ≤ cubeBesovDepthWeight Q s j :=
    cubeBesovDepthWeight_nonneg Q s j
  have hfull :=
    cubeBesovDepthWeight_mul_L2_descendantsAverage_sum_components_circNorm_le_sum_circNorm
      Q s G j hs0 hs1 hG
  calc
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j
        = cubeBesovDepthWeight Q s j *
            (descendantsAverage Q j
              (fun R => (cubeBesovOscillation R (2 : ℝ≥0∞) u) ^ 2)) ^
              (1 / 2 : ℝ) := by
              simp [cubeBesovDepthSeminorm, cubeBesovDepthAverage]
    _ ≤ cubeBesovDepthWeight Q s j *
          (descendantsAverage Q j (fun R => (C * S R) ^ 2)) ^ (1 / 2 : ℝ) := by
            exact mul_le_mul_of_nonneg_left hroot_bound hweight_nonneg
    _ = C * (cubeBesovDepthWeight Q s j *
          (descendantsAverage Q j (fun R => (S R) ^ 2)) ^ (1 / 2 : ℝ)) := by
            rw [hroot_factor]
            ring
    _ ≤ C * ∑ i : Fin d,
        cubeBesovCircNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => G x i) := by
            exact mul_le_mul_of_nonneg_left hfull hC

/-- Finite-depth `q = ∞` positive Besov control from vector local full-circ
Poincare. -/
theorem CubeLocalFullCircPoincareVectorEstimate.partialSeminormTop_two_le_sum_circNorm
    {d : ℕ} {Q : TriadicCube d} {s C : ℝ} {u : Vec d → ℝ}
    {G : Vec d → Vec d} {M : ℕ}
    (hlocal : CubeLocalFullCircPoincareVectorEstimate Q C u G M)
    (hG :
      ∀ i : Fin d,
        MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hs0 : 0 ≤ s) (hs1 : s < 1) (hC : 0 ≤ C) :
    cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) M u ≤
      C * ∑ i : Fin d,
        cubeBesovCircNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => G x i) := by
  unfold cubeBesovPartialSeminormTop
  refine Finset.sup'_le (s := Finset.range (M + 1)) (H := ⟨0, by simp⟩)
    (f := fun j => cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j) ?_
  intro j hj
  exact
    cubeBesovDepthSeminorm_two_le_sum_circNorm_of_vector_local_full_circ_bound
      Q s C u G j hs0 hs1 hC hG (by
        intro R hR
        exact hlocal j hj R hR)

/-- Fluctuation form of the finite-depth full-circ Poincare-to-Besov bound. -/
theorem CubeLocalFullCircPoincareVectorEstimate.fluctuation_partialNormTop_two_le_sum_circNorm
    {d : ℕ} {Q : TriadicCube d} {s C : ℝ} {u : Vec d → ℝ}
    {G : Vec d → Vec d} {M : ℕ}
    (hlocal : CubeLocalFullCircPoincareVectorEstimate Q C (cubeFluctuation Q u) G M)
    (hG :
      ∀ i : Fin d,
        MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hs0 : 0 ≤ s) (hs1 : s < 1) (hC : 0 ≤ C) :
    cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M (cubeFluctuation Q u) ≤
      C * ∑ i : Fin d,
        cubeBesovCircNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => G x i) := by
  rw [cubeBesovPartialNormTop_eq_cubeBesovPartialSeminormTop_of_cubeAverage_eq_zero
    (Q := Q) (s := s) (p := (2 : ℝ≥0∞)) (N := M)
    (u := cubeFluctuation Q u) (cubeAverage_cubeFluctuation Q u)]
  exact hlocal.partialSeminormTop_two_le_sum_circNorm hG hs0 hs1 hC

end Homogenization
