/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.Duality.ProjectedPairing.Averages

/-! # Main Bounds -/

namespace Homogenization

open MeasureTheory.Measure
open scoped BigOperators ENNReal
theorem abs_cubeBesovPairing_projection_le_max_mul_cubeBesovPartialNorm_cubeBesovCircPartialNorm
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (f g : Vec d → ℝ) (N : ℕ)
    (hgInt : MeasureTheory.IntegrableOn g (cubeSet Q) MeasureTheory.volume)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞) (hpConjTop : cubeBesovConjExponent p ≠ ∞)
    (hq : 1 ≤ q) (hqTop : q ≠ ∞) (hqConjTop : cubeBesovConjExponent q ≠ ∞)
    (hf : ∀ j < N + 1, ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp (cubeFluctuation R f) p (normalizedCubeMeasure R))
    (hg : ∀ j < N + 1, ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp (cubeProjection Q (j + 1) g)
        (cubeBesovConjExponent p) (normalizedCubeMeasure R)) :
    |cubeBesovPairing Q f (cubeProjection Q (N + 1) g)| ≤
      max 1 ((3 : ℝ) ^ s) *
        cubeBesovPartialNorm Q s p q N f *
        cubeBesovCircPartialNorm Q s (cubeBesovConjExponent p) (cubeBesovConjExponent q) (N + 1) g := by
  let pConj : ℝ≥0∞ := cubeBesovConjExponent p
  let qConj : ℝ≥0∞ := cubeBesovConjExponent q
  let T : ℕ → ℝ := fun j =>
    cubeAverage Q (fun x => cubeProjection Q (j + 1) g x * cubeProjectionResidual Q j f x)
  let A : ℕ → ℝ := fun j => cubeBesovDepthSeminorm Q s p f j
  let B : ℕ → ℝ := fun j => cubeBesovCircDepthSeminorm Q s pConj g (j + 1)
  let K : ℝ := max 1 ((3 : ℝ) ^ s)
  let M : ℝ := cubeBesovScaleWeight s Q * ‖cubeAverage Q f‖
  let S : ℝ := cubeBesovPartialSeminorm Q s p q N f
  let C : ℝ := cubeBesovCircPartialNorm Q s pConj qConj (N + 1) g
  have hp0 : p ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hq0 : q ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hq)
  have hpConj0 : pConj ≠ 0 := by
    simpa [pConj] using cubeBesovConjExponent_ne_zero p
  have hqConj0 : qConj ≠ 0 := by
    simpa [qConj] using cubeBesovConjExponent_ne_zero q
  have hpConj_eq :
      cubeBesovCircDepthSeminorm Q s pConj g 0 =
        cubeBesovScaleWeight (-s) Q * ‖cubeAverage Q g‖ := by
    simpa [pConj] using
      cubeBesovCircDepthSeminorm_depth_zero_eq_scaleWeight_neg_mul_norm_cubeAverage
        (Q := Q) (s := s) (p := cubeBesovConjExponent p) (u := g) hpConj0 hpConjTop
  have hC_nonneg : 0 ≤ C := by
    simpa [C, pConj, qConj] using
      cubeBesovCircPartialNorm_nonneg Q s (cubeBesovConjExponent p) (cubeBesovConjExponent q) (N + 1) g
  have hM_nonneg : 0 ≤ M := by
    exact mul_nonneg (cubeBesovScaleWeight_nonneg s Q) (norm_nonneg _)
  have hS_nonneg : 0 ≤ S := by
    simpa [S] using cubeBesovPartialSeminorm_nonneg Q s p q N f
  have hK_nonneg : 0 ≤ K := by
    exact le_trans (by norm_num) (le_max_left 1 ((3 : ℝ) ^ s))
  have hK_ge_one : 1 ≤ K := le_max_left 1 ((3 : ℝ) ^ s)
  have hmean_le :
      |cubeAverage Q f * cubeAverage Q g| ≤ M * C := by
    have hdepth0_le :
        cubeBesovCircDepthSeminorm Q s pConj g 0 ≤ C := by
      simpa [C, pConj, qConj] using
        cubeBesovCircDepthSeminorm_zero_le_cubeBesovCircPartialNorm
          (Q := Q) (s := s) (p := pConj) (q := qConj) (N := N + 1) (u := g) hqConj0 hqConjTop
    calc
      |cubeAverage Q f * cubeAverage Q g|
          = ‖cubeAverage Q f‖ * ‖cubeAverage Q g‖ := by
              simp [abs_mul]
      _ = (cubeBesovScaleWeight s Q * cubeBesovScaleWeight (-s) Q) *
            (‖cubeAverage Q f‖ * ‖cubeAverage Q g‖) := by
              have hscale :
                  cubeBesovScaleWeight s Q * cubeBesovScaleWeight (-s) Q = 1 := by
                simpa [mul_comm] using cubeBesovScaleWeight_neg_mul_cubeBesovScaleWeight Q s
              rw [hscale, one_mul]
      _ = (cubeBesovScaleWeight s Q * ‖cubeAverage Q f‖) *
            (cubeBesovScaleWeight (-s) Q * ‖cubeAverage Q g‖) := by
              ring
      _ = M * cubeBesovCircDepthSeminorm Q s pConj g 0 := by
            rw [hpConj_eq]
      _ ≤ M * C := by
            exact mul_le_mul_of_nonneg_left hdepth0_le hM_nonneg
  have hterm :
      ∀ j < N + 1, |T j| ≤ K * (A j * B j) := by
    intro j hj
    have hAB_nonneg : 0 ≤ A j * B j := by
      exact mul_nonneg
        (by simpa [A] using cubeBesovDepthSeminorm_nonneg Q s p f j)
        (by simpa [B, pConj] using cubeBesovCircDepthSeminorm_nonneg Q s pConj g (j + 1))
    calc
      |T j|
          = |cubeAverage Q (fun x => cubeProjection Q (j + 1) g x * cubeProjectionResidual Q j f x)| := by
              simp [T]
      _ ≤ (3 : ℝ) ^ s * A j * B j := by
            simpa [A, B, pConj] using
              abs_cubeAverage_mul_projection_succ_projectionResidual_le_mul_cubeBesovDepthSeminorm
                (Q := Q) (s := s) (p := p) (f := f) (g := g) (j := j)
                hp hp0 hpTop hpConjTop
                (fun R hR => hf j hj R hR)
                (fun R hR => hg j hj R hR)
      _ = (3 : ℝ) ^ s * (A j * B j) := by
            ring
      _ ≤ K * (A j * B j) := by
            exact mul_le_mul_of_nonneg_right (le_max_right 1 ((3 : ℝ) ^ s)) hAB_nonneg
  have hsum_terms :
      Finset.sum (Finset.range (N + 1)) (fun j => |T j|) ≤
        K * Finset.sum (Finset.range (N + 1)) (fun j => A j * B j) := by
    calc
      Finset.sum (Finset.range (N + 1)) (fun j => |T j|)
          ≤ Finset.sum (Finset.range (N + 1)) (fun j => K * (A j * B j)) := by
              refine Finset.sum_le_sum ?_
              intro j hj
              exact hterm j (Finset.mem_range.mp hj)
      _ = K * Finset.sum (Finset.range (N + 1)) (fun j => A j * B j) := by
            rw [← Finset.mul_sum]
  let : ENNReal.HolderConjugate q qConj :=
    by simpa [qConj, cubeBesovConjExponent] using ENNReal.HolderConjugate.conjExponent hq
  let : ENNReal.HolderConjugate qConj q := inferInstance
  have hq_toReal_ge : 1 ≤ q.toReal := by
    simpa using ENNReal.toReal_mono hqTop hq
  have hq_ne_one : q ≠ 1 := by
    exact (ENNReal.HolderConjugate.ne_top_iff_ne_one (p := qConj) (q := q)).1
      (by simpa [qConj] using hqConjTop)
  have hq_toReal_ne_one : q.toReal ≠ 1 := by
    intro h
    exact hq_ne_one ((ENNReal.toReal_eq_one_iff q).mp h)
  have hq_toReal_gt : 1 < q.toReal := lt_of_le_of_ne hq_toReal_ge (Ne.symm hq_toReal_ne_one)
  have hdisc : Real.HolderConjugate q.toReal qConj.toReal :=
    ENNReal.HolderConjugate.toReal (p := q) (q := qConj) hq_toReal_gt
  have hholder :
      Finset.sum (Finset.range (N + 1)) (fun j => A j * B j) ≤
        (Finset.sum (Finset.range (N + 1)) (fun j => (A j) ^ q.toReal)) ^ (1 / q.toReal) *
          (Finset.sum (Finset.range (N + 1)) (fun j => (B j) ^ qConj.toReal)) ^
            (1 / qConj.toReal) := by
    exact Real.inner_le_Lp_mul_Lq_of_nonneg
      (s := Finset.range (N + 1)) (f := A) (g := B) hdisc
      (fun j _ => by simpa [A] using cubeBesovDepthSeminorm_nonneg Q s p f j)
      (fun j _ => by simpa [B, pConj] using cubeBesovCircDepthSeminorm_nonneg Q s pConj g (j + 1))
  have hshift_circ :
      (Finset.sum (Finset.range (N + 1)) (fun j => (B j) ^ qConj.toReal)) ^ (1 / qConj.toReal) ≤ C := by
    simpa [B, C, pConj, qConj] using
      shifted_cubeBesovCircPartialSeminorm_le_cubeBesovCircPartialNorm
        (Q := Q) (s := s) (p := pConj) (q := qConj) (N := N) (u := g) hqConj0 hqConjTop
  have hsum_le :
      Finset.sum (Finset.range (N + 1)) (fun j => |T j|) ≤ K * S * C := by
    calc
      Finset.sum (Finset.range (N + 1)) (fun j => |T j|)
          ≤ K * Finset.sum (Finset.range (N + 1)) (fun j => A j * B j) := hsum_terms
      _ ≤ K *
            ((Finset.sum (Finset.range (N + 1)) (fun j => (A j) ^ q.toReal)) ^ (1 / q.toReal) *
              (Finset.sum (Finset.range (N + 1)) (fun j => (B j) ^ qConj.toReal)) ^
                (1 / qConj.toReal)) := by
              exact mul_le_mul_of_nonneg_left hholder hK_nonneg
      _ = K * (S *
            (Finset.sum (Finset.range (N + 1)) (fun j => (B j) ^ qConj.toReal)) ^
              (1 / qConj.toReal)) := by
              rfl
      _ ≤ K * (S * C) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hshift_circ hS_nonneg) hK_nonneg
      _ = K * S * C := by
            ring
  have hdecomp :
      cubeBesovPairing Q f (cubeProjection Q (N + 1) g) =
        cubeAverage Q f * cubeAverage Q g +
          Finset.sum (Finset.range (N + 1)) T := by
    simpa [T] using
      cubeBesovPairing_projection_eq_cubeAverage_mul_cubeAverage_add_sum
        (Q := Q) (p := p) (f := f) (g := g) (N := N + 1) hgInt hf hg hp
  have habs :
      |cubeBesovPairing Q f (cubeProjection Q (N + 1) g)| ≤
        |cubeAverage Q f * cubeAverage Q g| +
          Finset.sum (Finset.range (N + 1)) (fun j => |T j|) := by
    rw [hdecomp]
    calc
      |cubeAverage Q f * cubeAverage Q g + Finset.sum (Finset.range (N + 1)) T|
          ≤ |cubeAverage Q f * cubeAverage Q g| +
              |Finset.sum (Finset.range (N + 1)) T| := by
                exact abs_add_le _ _
      _ ≤ |cubeAverage Q f * cubeAverage Q g| +
            Finset.sum (Finset.range (N + 1)) (fun j => |T j|) := by
              simpa using add_le_add_left
                (Finset.abs_sum_le_sum_abs T (Finset.range (N + 1)))
                (|cubeAverage Q f * cubeAverage Q g|)
  calc
    |cubeBesovPairing Q f (cubeProjection Q (N + 1) g)|
        ≤ |cubeAverage Q f * cubeAverage Q g| +
            Finset.sum (Finset.range (N + 1)) (fun j => |T j|) := habs
    _ ≤ M * C + K * S * C := add_le_add hmean_le hsum_le
    _ = (M + K * S) * C := by ring
    _ ≤ (K * (M + S)) * C := by
          refine mul_le_mul_of_nonneg_right ?_ hC_nonneg
          calc
            M + K * S ≤ K * M + K * S := by
              exact add_le_add
                (by
                  simpa [one_mul] using
                    (mul_le_mul_of_nonneg_right hK_ge_one hM_nonneg))
                le_rfl
            _ = K * (M + S) := by ring
    _ = K * cubeBesovPartialNorm Q s p q N f * C := by
          unfold M S cubeBesovPartialNorm
          ring
    _ = max 1 ((3 : ℝ) ^ s) *
          cubeBesovPartialNorm Q s p q N f *
          cubeBesovCircPartialNorm Q s (cubeBesovConjExponent p) (cubeBesovConjExponent q) (N + 1) g := by
            rfl

theorem abs_cubeBesovPairing_projection_le_max_mul_cubeBesovPartialNormTop_cubeBesovCircPartialNormOne
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (f g : Vec d → ℝ) (N : ℕ)
    (hgInt : MeasureTheory.IntegrableOn g (cubeSet Q) MeasureTheory.volume)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞) (hpConjTop : cubeBesovConjExponent p ≠ ∞)
    (hf : ∀ j < N + 1, ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp (cubeFluctuation R f) p (normalizedCubeMeasure R))
    (hg : ∀ j < N + 1, ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp (cubeProjection Q (j + 1) g)
        (cubeBesovConjExponent p) (normalizedCubeMeasure R)) :
    |cubeBesovPairing Q f (cubeProjection Q (N + 1) g)| ≤
      max 1 ((3 : ℝ) ^ s) *
        cubeBesovPartialNormTop Q s p N f *
        cubeBesovCircPartialNorm Q s (cubeBesovConjExponent p) 1 (N + 1) g := by
  let pConj : ℝ≥0∞ := cubeBesovConjExponent p
  let T : ℕ → ℝ := fun j =>
    cubeAverage Q (fun x => cubeProjection Q (j + 1) g x * cubeProjectionResidual Q j f x)
  let A : ℕ → ℝ := fun j => cubeBesovDepthSeminorm Q s p f j
  let B : ℕ → ℝ := fun j => cubeBesovCircDepthSeminorm Q s pConj g (j + 1)
  let K : ℝ := max 1 ((3 : ℝ) ^ s)
  let M : ℝ := cubeBesovScaleWeight s Q * ‖cubeAverage Q f‖
  let S : ℝ := cubeBesovPartialSeminormTop Q s p N f
  let C : ℝ := cubeBesovCircPartialNorm Q s pConj 1 (N + 1) g
  have hp0 : p ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpConj0 : pConj ≠ 0 := by
    simpa [pConj] using cubeBesovConjExponent_ne_zero p
  have hpConj_eq :
      cubeBesovCircDepthSeminorm Q s pConj g 0 =
        cubeBesovScaleWeight (-s) Q * ‖cubeAverage Q g‖ := by
    simpa [pConj] using
      cubeBesovCircDepthSeminorm_depth_zero_eq_scaleWeight_neg_mul_norm_cubeAverage
        (Q := Q) (s := s) (p := cubeBesovConjExponent p) (u := g) hpConj0 hpConjTop
  have hC_nonneg : 0 ≤ C := by
    simpa [C, pConj] using
      cubeBesovCircPartialNorm_nonneg Q s (cubeBesovConjExponent p) 1 (N + 1) g
  have hM_nonneg : 0 ≤ M := by
    exact mul_nonneg (cubeBesovScaleWeight_nonneg s Q) (norm_nonneg _)
  have hS_nonneg : 0 ≤ S := by
    simpa [S] using cubeBesovPartialSeminormTop_nonneg Q s p N f
  have hK_nonneg : 0 ≤ K := by
    exact le_trans (by norm_num) (le_max_left 1 ((3 : ℝ) ^ s))
  have hK_ge_one : 1 ≤ K := le_max_left 1 ((3 : ℝ) ^ s)
  have hmean_le :
      |cubeAverage Q f * cubeAverage Q g| ≤ M * C := by
    have hdepth0_le :
        cubeBesovCircDepthSeminorm Q s pConj g 0 ≤ C := by
      simpa [C, pConj] using
        cubeBesovCircDepthSeminorm_zero_le_cubeBesovCircPartialNorm
          (Q := Q) (s := s) (p := pConj) (q := (1 : ℝ≥0∞)) (N := N + 1) (u := g)
          (by norm_num) (by simp)
    calc
      |cubeAverage Q f * cubeAverage Q g|
          = ‖cubeAverage Q f‖ * ‖cubeAverage Q g‖ := by
              simp [abs_mul]
      _ = (cubeBesovScaleWeight s Q * cubeBesovScaleWeight (-s) Q) *
            (‖cubeAverage Q f‖ * ‖cubeAverage Q g‖) := by
              have hscale :
                  cubeBesovScaleWeight s Q * cubeBesovScaleWeight (-s) Q = 1 := by
                simpa [mul_comm] using cubeBesovScaleWeight_neg_mul_cubeBesovScaleWeight Q s
              rw [hscale, one_mul]
      _ = (cubeBesovScaleWeight s Q * ‖cubeAverage Q f‖) *
            (cubeBesovScaleWeight (-s) Q * ‖cubeAverage Q g‖) := by
              ring
      _ = M * cubeBesovCircDepthSeminorm Q s pConj g 0 := by
            rw [hpConj_eq]
      _ ≤ M * C := by
            exact mul_le_mul_of_nonneg_left hdepth0_le hM_nonneg
  have hterm :
      ∀ j < N + 1, |T j| ≤ K * (A j * B j) := by
    intro j hj
    have hAB_nonneg : 0 ≤ A j * B j := by
      exact mul_nonneg
        (by simpa [A] using cubeBesovDepthSeminorm_nonneg Q s p f j)
        (by simpa [B, pConj] using cubeBesovCircDepthSeminorm_nonneg Q s pConj g (j + 1))
    calc
      |T j|
          = |cubeAverage Q (fun x => cubeProjection Q (j + 1) g x * cubeProjectionResidual Q j f x)| := by
              simp [T]
      _ ≤ (3 : ℝ) ^ s * A j * B j := by
            simpa [A, B, pConj] using
              abs_cubeAverage_mul_projection_succ_projectionResidual_le_mul_cubeBesovDepthSeminorm
                (Q := Q) (s := s) (p := p) (f := f) (g := g) (j := j)
                hp hp0 hpTop hpConjTop
                (fun R hR => hf j hj R hR)
                (fun R hR => hg j hj R hR)
      _ = (3 : ℝ) ^ s * (A j * B j) := by
            ring
      _ ≤ K * (A j * B j) := by
            exact mul_le_mul_of_nonneg_right (le_max_right 1 ((3 : ℝ) ^ s)) hAB_nonneg
  have hsum_terms :
      Finset.sum (Finset.range (N + 1)) (fun j => |T j|) ≤
        K * Finset.sum (Finset.range (N + 1)) (fun j => A j * B j) := by
    calc
      Finset.sum (Finset.range (N + 1)) (fun j => |T j|)
          ≤ Finset.sum (Finset.range (N + 1)) (fun j => K * (A j * B j)) := by
              refine Finset.sum_le_sum ?_
              intro j hj
              exact hterm j (Finset.mem_range.mp hj)
      _ = K * Finset.sum (Finset.range (N + 1)) (fun j => A j * B j) := by
            rw [← Finset.mul_sum]
  have hsup :
      ∀ j < N + 1, A j ≤ S := by
    intro j hj
    exact Finset.le_sup' (s := Finset.range (N + 1)) (f := A) (Finset.mem_range.mpr hj)
  have hshift_circ :
      Finset.sum (Finset.range (N + 1)) B ≤ C := by
    simpa [B, C, pConj] using
      shifted_cubeBesovCircPartialSeminorm_le_cubeBesovCircPartialNorm
        (Q := Q) (s := s) (p := pConj) (q := (1 : ℝ≥0∞)) (N := N) (u := g)
        (by norm_num) (by simp)
  have hsum_le :
      Finset.sum (Finset.range (N + 1)) (fun j => |T j|) ≤ K * S * C := by
    have hsumAB :
        Finset.sum (Finset.range (N + 1)) (fun j => A j * B j) ≤
          S * Finset.sum (Finset.range (N + 1)) B := by
      calc
        Finset.sum (Finset.range (N + 1)) (fun j => A j * B j)
            ≤ Finset.sum (Finset.range (N + 1)) (fun j => S * B j) := by
                refine Finset.sum_le_sum ?_
                intro j hj
                exact mul_le_mul_of_nonneg_right
                  (hsup j (Finset.mem_range.mp hj))
                  (by simpa [B, pConj] using cubeBesovCircDepthSeminorm_nonneg Q s pConj g (j + 1))
        _ = S * Finset.sum (Finset.range (N + 1)) B := by
              rw [Finset.mul_sum]
    calc
      Finset.sum (Finset.range (N + 1)) (fun j => |T j|)
          ≤ K * Finset.sum (Finset.range (N + 1)) (fun j => A j * B j) := hsum_terms
      _ ≤ K * (S * Finset.sum (Finset.range (N + 1)) B) := by
            exact mul_le_mul_of_nonneg_left hsumAB hK_nonneg
      _ ≤ K * (S * C) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hshift_circ hS_nonneg) hK_nonneg
      _ = K * S * C := by
            ring
  have hdecomp :
      cubeBesovPairing Q f (cubeProjection Q (N + 1) g) =
        cubeAverage Q f * cubeAverage Q g +
          Finset.sum (Finset.range (N + 1)) T := by
    simpa [T] using
      cubeBesovPairing_projection_eq_cubeAverage_mul_cubeAverage_add_sum
        (Q := Q) (p := p) (f := f) (g := g) (N := N + 1) hgInt hf hg hp
  have habs :
      |cubeBesovPairing Q f (cubeProjection Q (N + 1) g)| ≤
        |cubeAverage Q f * cubeAverage Q g| +
          Finset.sum (Finset.range (N + 1)) (fun j => |T j|) := by
    rw [hdecomp]
    calc
      |cubeAverage Q f * cubeAverage Q g + Finset.sum (Finset.range (N + 1)) T|
          ≤ |cubeAverage Q f * cubeAverage Q g| +
              |Finset.sum (Finset.range (N + 1)) T| := by
                exact abs_add_le _ _
      _ ≤ |cubeAverage Q f * cubeAverage Q g| +
            Finset.sum (Finset.range (N + 1)) (fun j => |T j|) := by
              simpa using add_le_add_left
                (Finset.abs_sum_le_sum_abs T (Finset.range (N + 1)))
                (|cubeAverage Q f * cubeAverage Q g|)
  calc
    |cubeBesovPairing Q f (cubeProjection Q (N + 1) g)|
        ≤ |cubeAverage Q f * cubeAverage Q g| +
            Finset.sum (Finset.range (N + 1)) (fun j => |T j|) := habs
    _ ≤ M * C + K * S * C := add_le_add hmean_le hsum_le
    _ = (M + K * S) * C := by ring
    _ ≤ (K * (M + S)) * C := by
          refine mul_le_mul_of_nonneg_right ?_ hC_nonneg
          calc
            M + K * S ≤ K * M + K * S := by
              exact add_le_add
                (by
                  simpa [one_mul] using
                    (mul_le_mul_of_nonneg_right hK_ge_one hM_nonneg))
                le_rfl
            _ = K * (M + S) := by ring
    _ = K * cubeBesovPartialNormTop Q s p N f * C := by
          unfold M S cubeBesovPartialNormTop
          ring
    _ = max 1 ((3 : ℝ) ^ s) *
          cubeBesovPartialNormTop Q s p N f *
          cubeBesovCircPartialNorm Q s (cubeBesovConjExponent p) 1 (N + 1) g := by
            rfl

theorem abs_cubeBesovPairing_projection_le_max_mul_cubeBesovPartialNormOne_cubeBesovCircPartialNormTop
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (f g : Vec d → ℝ) (N : ℕ)
    (hgInt : MeasureTheory.IntegrableOn g (cubeSet Q) MeasureTheory.volume)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞) (hpConjTop : cubeBesovConjExponent p ≠ ∞)
    (hf : ∀ j < N + 1, ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp (cubeFluctuation R f) p (normalizedCubeMeasure R))
    (hg : ∀ j < N + 1, ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp (cubeProjection Q (j + 1) g)
        (cubeBesovConjExponent p) (normalizedCubeMeasure R)) :
    |cubeBesovPairing Q f (cubeProjection Q (N + 1) g)| ≤
      max 1 ((3 : ℝ) ^ s) *
        cubeBesovPartialNorm Q s p 1 N f *
        cubeBesovCircPartialNormTop Q s (cubeBesovConjExponent p) (N + 1) g := by
  let pConj : ℝ≥0∞ := cubeBesovConjExponent p
  let T : ℕ → ℝ := fun j =>
    cubeAverage Q (fun x => cubeProjection Q (j + 1) g x * cubeProjectionResidual Q j f x)
  let A : ℕ → ℝ := fun j => cubeBesovDepthSeminorm Q s p f j
  let B : ℕ → ℝ := fun j => cubeBesovCircDepthSeminorm Q s pConj g (j + 1)
  let K : ℝ := max 1 ((3 : ℝ) ^ s)
  let M : ℝ := cubeBesovScaleWeight s Q * ‖cubeAverage Q f‖
  let S : ℝ := cubeBesovPartialSeminorm Q s p 1 N f
  let C : ℝ := cubeBesovCircPartialNormTop Q s pConj (N + 1) g
  have hp0 : p ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpConj0 : pConj ≠ 0 := by
    simpa [pConj] using cubeBesovConjExponent_ne_zero p
  have hpConj_eq :
      cubeBesovCircDepthSeminorm Q s pConj g 0 =
        cubeBesovScaleWeight (-s) Q * ‖cubeAverage Q g‖ := by
    simpa [pConj] using
      cubeBesovCircDepthSeminorm_depth_zero_eq_scaleWeight_neg_mul_norm_cubeAverage
        (Q := Q) (s := s) (p := cubeBesovConjExponent p) (u := g) hpConj0 hpConjTop
  have hC_nonneg : 0 ≤ C := by
    simpa [C, pConj] using
      cubeBesovCircPartialNormTop_nonneg Q s (cubeBesovConjExponent p) (N + 1) g
  have hM_nonneg : 0 ≤ M := by
    exact mul_nonneg (cubeBesovScaleWeight_nonneg s Q) (norm_nonneg _)
  have hS_nonneg : 0 ≤ S := by
    simpa [S] using cubeBesovPartialSeminorm_nonneg Q s p 1 N f
  have hK_nonneg : 0 ≤ K := by
    exact le_trans (by norm_num) (le_max_left 1 ((3 : ℝ) ^ s))
  have hK_ge_one : 1 ≤ K := le_max_left 1 ((3 : ℝ) ^ s)
  have hmean_le :
      |cubeAverage Q f * cubeAverage Q g| ≤ M * C := by
    have hdepth0_le :
        cubeBesovCircDepthSeminorm Q s pConj g 0 ≤ C := by
      unfold C cubeBesovCircPartialNormTop cubeBesovCircPartialSeminormTop
      exact Finset.le_sup' (s := Finset.range (N + 2))
        (f := fun j => cubeBesovCircDepthSeminorm Q s pConj g j) (by simp)
    calc
      |cubeAverage Q f * cubeAverage Q g|
          = ‖cubeAverage Q f‖ * ‖cubeAverage Q g‖ := by
              simp [abs_mul]
      _ = (cubeBesovScaleWeight s Q * cubeBesovScaleWeight (-s) Q) *
            (‖cubeAverage Q f‖ * ‖cubeAverage Q g‖) := by
              have hscale :
                  cubeBesovScaleWeight s Q * cubeBesovScaleWeight (-s) Q = 1 := by
                simpa [mul_comm] using cubeBesovScaleWeight_neg_mul_cubeBesovScaleWeight Q s
              rw [hscale, one_mul]
      _ = (cubeBesovScaleWeight s Q * ‖cubeAverage Q f‖) *
            (cubeBesovScaleWeight (-s) Q * ‖cubeAverage Q g‖) := by
              ring
      _ = M * cubeBesovCircDepthSeminorm Q s pConj g 0 := by
            rw [hpConj_eq]
      _ ≤ M * C := by
            exact mul_le_mul_of_nonneg_left hdepth0_le hM_nonneg
  have hterm :
      ∀ j < N + 1, |T j| ≤ K * (A j * B j) := by
    intro j hj
    have hAB_nonneg : 0 ≤ A j * B j := by
      exact mul_nonneg
        (by simpa [A] using cubeBesovDepthSeminorm_nonneg Q s p f j)
        (by simpa [B, pConj] using cubeBesovCircDepthSeminorm_nonneg Q s pConj g (j + 1))
    calc
      |T j|
          = |cubeAverage Q (fun x => cubeProjection Q (j + 1) g x * cubeProjectionResidual Q j f x)| := by
              simp [T]
      _ ≤ (3 : ℝ) ^ s * A j * B j := by
            simpa [A, B, pConj] using
              abs_cubeAverage_mul_projection_succ_projectionResidual_le_mul_cubeBesovDepthSeminorm
                (Q := Q) (s := s) (p := p) (f := f) (g := g) (j := j)
                hp hp0 hpTop hpConjTop
                (fun R hR => hf j hj R hR)
                (fun R hR => hg j hj R hR)
      _ = (3 : ℝ) ^ s * (A j * B j) := by
            ring
      _ ≤ K * (A j * B j) := by
            exact mul_le_mul_of_nonneg_right (le_max_right 1 ((3 : ℝ) ^ s)) hAB_nonneg
  have hsum_terms :
      Finset.sum (Finset.range (N + 1)) (fun j => |T j|) ≤
        K * Finset.sum (Finset.range (N + 1)) (fun j => A j * B j) := by
    calc
      Finset.sum (Finset.range (N + 1)) (fun j => |T j|)
          ≤ Finset.sum (Finset.range (N + 1)) (fun j => K * (A j * B j)) := by
              refine Finset.sum_le_sum ?_
              intro j hj
              exact hterm j (Finset.mem_range.mp hj)
      _ = K * Finset.sum (Finset.range (N + 1)) (fun j => A j * B j) := by
            rw [← Finset.mul_sum]
  have hshift_circ :
      ∀ j < N + 1, B j ≤ C := by
    intro j hj
    unfold C cubeBesovCircPartialNormTop cubeBesovCircPartialSeminormTop
    exact Finset.le_sup' (s := Finset.range (N + 2))
      (f := fun k => cubeBesovCircDepthSeminorm Q s pConj g k)
      (Finset.mem_range.mpr (Nat.succ_lt_succ hj))
  have hsum_one :
      Finset.sum (Finset.range (N + 1)) A = S := by
    unfold S cubeBesovPartialSeminorm
    simp [A]
  have hsum_le :
      Finset.sum (Finset.range (N + 1)) (fun j => |T j|) ≤ K * S * C := by
    have hsumAB :
        Finset.sum (Finset.range (N + 1)) (fun j => A j * B j) ≤
          Finset.sum (Finset.range (N + 1)) A * C := by
      calc
        Finset.sum (Finset.range (N + 1)) (fun j => A j * B j)
            ≤ Finset.sum (Finset.range (N + 1)) (fun j => A j * C) := by
                refine Finset.sum_le_sum ?_
                intro j hj
                exact mul_le_mul_of_nonneg_left
                  (hshift_circ j (Finset.mem_range.mp hj))
                  (by simpa [A] using cubeBesovDepthSeminorm_nonneg Q s p f j)
        _ = Finset.sum (Finset.range (N + 1)) A * C := by
              rw [Finset.sum_mul]
    calc
      Finset.sum (Finset.range (N + 1)) (fun j => |T j|)
          ≤ K * Finset.sum (Finset.range (N + 1)) (fun j => A j * B j) := hsum_terms
      _ ≤ K * (Finset.sum (Finset.range (N + 1)) A * C) := by
            exact mul_le_mul_of_nonneg_left hsumAB hK_nonneg
      _ = K * S * C := by
            rw [hsum_one]
            ring
  have hdecomp :
      cubeBesovPairing Q f (cubeProjection Q (N + 1) g) =
        cubeAverage Q f * cubeAverage Q g +
          Finset.sum (Finset.range (N + 1)) T := by
    simpa [T] using
      cubeBesovPairing_projection_eq_cubeAverage_mul_cubeAverage_add_sum
        (Q := Q) (p := p) (f := f) (g := g) (N := N + 1) hgInt hf hg hp
  have habs :
      |cubeBesovPairing Q f (cubeProjection Q (N + 1) g)| ≤
        |cubeAverage Q f * cubeAverage Q g| +
          Finset.sum (Finset.range (N + 1)) (fun j => |T j|) := by
    rw [hdecomp]
    calc
      |cubeAverage Q f * cubeAverage Q g + Finset.sum (Finset.range (N + 1)) T|
          ≤ |cubeAverage Q f * cubeAverage Q g| +
              |Finset.sum (Finset.range (N + 1)) T| := by
                exact abs_add_le _ _
      _ ≤ |cubeAverage Q f * cubeAverage Q g| +
            Finset.sum (Finset.range (N + 1)) (fun j => |T j|) := by
              simpa using add_le_add_left
                (Finset.abs_sum_le_sum_abs T (Finset.range (N + 1)))
                (|cubeAverage Q f * cubeAverage Q g|)
  calc
    |cubeBesovPairing Q f (cubeProjection Q (N + 1) g)|
        ≤ |cubeAverage Q f * cubeAverage Q g| +
            Finset.sum (Finset.range (N + 1)) (fun j => |T j|) := habs
    _ ≤ M * C + K * S * C := add_le_add hmean_le hsum_le
    _ = (M + K * S) * C := by ring
    _ ≤ (K * (M + S)) * C := by
          refine mul_le_mul_of_nonneg_right ?_ hC_nonneg
          calc
            M + K * S ≤ K * M + K * S := by
              exact add_le_add
                (by
                  simpa [one_mul] using
                    (mul_le_mul_of_nonneg_right hK_ge_one hM_nonneg))
                le_rfl
            _ = K * (M + S) := by ring
    _ = K * cubeBesovPartialNorm Q s p 1 N f * C := by
          unfold M S cubeBesovPartialNorm
          ring
    _ = max 1 ((3 : ℝ) ^ s) *
          cubeBesovPartialNorm Q s p 1 N f *
          cubeBesovCircPartialNormTop Q s (cubeBesovConjExponent p) (N + 1) g := by
            rfl


end Homogenization
