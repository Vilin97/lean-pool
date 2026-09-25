/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Besov.Duality.Full
public import LeanPool.CoarseGraining.Homogenization.Besov.Duality.ProjectedPairing

/-! # Wrapper Comparison -/

@[expose] public section

namespace Homogenization

open MeasureTheory.Measure
open scoped BigOperators ENNReal

theorem cubeBesovDualPartialNorm_projection_le_max_mul_cubeBesovCircPartialNorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ)
    (huInt : MeasureTheory.IntegrableOn u (cubeSet Q) MeasureTheory.volume)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞) (hpConjTop : cubeBesovConjExponent p ≠ ∞)
    (hq : 1 ≤ q) (hqTop : q ≠ ∞) (hqConjTop : cubeBesovConjExponent q ≠ ∞) :
    cubeBesovDualPartialNorm Q s p q N (cubeProjection Q (N + 1) u) ≤
      max 1 ((3 : ℝ) ^ s) *
        cubeBesovCircPartialNorm Q s p q (N + 1) u := by
  let pConj : ℝ≥0∞ := cubeBesovConjExponent p
  let qConj : ℝ≥0∞ := cubeBesovConjExponent q
  have hpHolder : ENNReal.HolderConjugate p pConj := by
    simpa [pConj, cubeBesovConjExponent] using ENNReal.HolderConjugate.conjExponent hp
  let : ENNReal.HolderConjugate p pConj := hpHolder
  let : ENNReal.HolderConjugate pConj p := inferInstance
  have hqHolder : ENNReal.HolderConjugate q qConj := by
    simpa [qConj, cubeBesovConjExponent] using ENNReal.HolderConjugate.conjExponent hq
  let : ENNReal.HolderConjugate q qConj := hqHolder
  let : ENNReal.HolderConjugate qConj q := inferInstance
  have hpConj : 1 ≤ pConj := by
    simpa [pConj] using (ENNReal.HolderConjugate.one_le (p := pConj) (q := p))
  have hqConj : 1 ≤ qConj := by
    simpa [qConj] using (ENNReal.HolderConjugate.one_le (p := qConj) (q := q))
  have hpConj0 : pConj ≠ 0 := by
    simpa [pConj] using cubeBesovConjExponent_ne_zero p
  have hqConj0 : qConj ≠ 0 := by
    simpa [qConj] using cubeBesovConjExponent_ne_zero q
  have hpDouble : cubeBesovConjExponent pConj = p := by
    simpa [pConj, cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := pConj) (q := p))
  have hqDouble : cubeBesovConjExponent qConj = q := by
    simpa [qConj, cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := qConj) (q := q))
  have hpDoubleTop : cubeBesovConjExponent pConj ≠ ∞ := by
    simpa [hpDouble] using hpTop
  have hqDoubleTop : cubeBesovConjExponent qConj ≠ ∞ := by
    simpa [hqDouble] using hqTop
  have hCirc_nonneg : 0 ≤ cubeBesovCircPartialNorm Q s p q (N + 1) u := by
    exact cubeBesovCircPartialNorm_nonneg Q s p q (N + 1) u
  have hK_nonneg : 0 ≤ max 1 ((3 : ℝ) ^ s) := by
    exact le_trans (by norm_num) (le_max_left 1 ((3 : ℝ) ^ s))
  unfold cubeBesovDualPartialNorm
  refine csSup_le ?_ ?_
  · refine ⟨0, ?_⟩
    refine ⟨fun _ => (0 : ℝ), ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [cubeBesovDualTestNorm_of_conjExponent_ne_top Q s p q N (fun _ => (0 : ℝ)) hqConjTop]
        rw [cubeBesovPartialNorm_zero (Q := Q) (s := s) (p := pConj) (q := qConj) (N := N)
          hpConj0 hpConjTop hqConj0 hqConjTop]
        norm_num
      · simpa using cubeBesovDualLocalMemLp_const Q p N (0 : ℝ)
    · simp [cubeBesovPairing, cubeAverage_const]
  · intro r hr
    rcases hr with ⟨g, hg, rfl⟩
    have hgNorm : cubeBesovDualTestNorm Q s p q N g ≤ 1 := hg.norm_le_one
    have hgMem :
        ∀ j < N + 1, ∀ R ∈ descendantsAtDepth Q j,
          MeasureTheory.MemLp (cubeFluctuation R g) pConj (normalizedCubeMeasure R) := by
      intro j hj R hR
      simpa [pConj] using hg.memLp_admissible j hj R hR
    have huMem :
        ∀ j < N + 1, ∀ R ∈ descendantsAtDepth Q j,
          MeasureTheory.MemLp (cubeProjection Q (j + 1) u)
            (cubeBesovConjExponent pConj) (normalizedCubeMeasure R) := by
      intro j hj R hR
      simpa [hpDouble] using
        cubeProjection_succ_memLp_of_mem_descendantsAtDepth
          (Q := Q) (R := R) (j := j) p u hR
    have hgPosNorm :
        cubeBesovPartialNorm Q s pConj qConj N g ≤ 1 := by
      rw [cubeBesovDualTestNorm_of_conjExponent_ne_top Q s p q N g hqConjTop] at hgNorm
      simpa [pConj, qConj] using hgNorm
    have hpair :
        |cubeBesovPairing Q g (cubeProjection Q (N + 1) u)| ≤
          max 1 ((3 : ℝ) ^ s) *
            cubeBesovPartialNorm Q s pConj qConj N g *
            cubeBesovCircPartialNorm Q s p q (N + 1) u := by
      simpa [pConj, qConj, hpDouble, hqDouble] using
        abs_cubeBesovPairing_projection_le_max_mul_cubeBesovPartialNorm_cubeBesovCircPartialNorm
          (Q := Q) (s := s) (p := pConj) (q := qConj) (f := g) (g := u) (N := N)
          huInt hpConj hpConjTop hpDoubleTop hqConj hqConjTop hqDoubleTop hgMem huMem
    calc
      |cubeBesovPairing Q (cubeProjection Q (N + 1) u) g|
          = |cubeBesovPairing Q g (cubeProjection Q (N + 1) u)| := by
              simp [cubeBesovPairing, mul_comm]
      _ ≤ max 1 ((3 : ℝ) ^ s) *
            cubeBesovPartialNorm Q s pConj qConj N g *
            cubeBesovCircPartialNorm Q s p q (N + 1) u := hpair
      _ ≤ (max 1 ((3 : ℝ) ^ s) * 1) *
            cubeBesovCircPartialNorm Q s p q (N + 1) u := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hgPosNorm hK_nonneg) hCirc_nonneg
      _ = max 1 ((3 : ℝ) ^ s) *
            cubeBesovCircPartialNorm Q s p q (N + 1) u := by
              ring

theorem abs_cubeBesovPairing_projection_le_max_mul_cubeBesovCircPartialNorm_of_dual_test
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (u g : Vec d → ℝ)
    (huInt : MeasureTheory.IntegrableOn u (cubeSet Q) MeasureTheory.volume)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞) (hpConjTop : cubeBesovConjExponent p ≠ ∞)
    (hq : 1 ≤ q) (hqTop : q ≠ ∞) (hqConjTop : cubeBesovConjExponent q ≠ ∞)
    (hg : CubeBesovDualTest Q s p q N g) :
    |cubeBesovPairing Q (cubeProjection Q (N + 1) u) g| ≤
      max 1 ((3 : ℝ) ^ s) *
        cubeBesovCircPartialNorm Q s p q (N + 1) u := by
  let pConj : ℝ≥0∞ := cubeBesovConjExponent p
  let qConj : ℝ≥0∞ := cubeBesovConjExponent q
  have hpHolder : ENNReal.HolderConjugate p pConj := by
    simpa [pConj, cubeBesovConjExponent] using ENNReal.HolderConjugate.conjExponent hp
  let : ENNReal.HolderConjugate p pConj := hpHolder
  let : ENNReal.HolderConjugate pConj p := inferInstance
  have hqHolder : ENNReal.HolderConjugate q qConj := by
    simpa [qConj, cubeBesovConjExponent] using ENNReal.HolderConjugate.conjExponent hq
  let : ENNReal.HolderConjugate q qConj := hqHolder
  let : ENNReal.HolderConjugate qConj q := inferInstance
  have hpConj : 1 ≤ pConj := by
    simpa [pConj] using (ENNReal.HolderConjugate.one_le (p := pConj) (q := p))
  have hqConj : 1 ≤ qConj := by
    simpa [qConj] using (ENNReal.HolderConjugate.one_le (p := qConj) (q := q))
  have hpDouble : cubeBesovConjExponent pConj = p := by
    simpa [pConj, cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := pConj) (q := p))
  have hqDouble : cubeBesovConjExponent qConj = q := by
    simpa [qConj, cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := qConj) (q := q))
  have hpDoubleTop : cubeBesovConjExponent pConj ≠ ∞ := by
    simpa [hpDouble] using hpTop
  have hqDoubleTop : cubeBesovConjExponent qConj ≠ ∞ := by
    simpa [hqDouble] using hqTop
  have hCirc_nonneg : 0 ≤ cubeBesovCircPartialNorm Q s p q (N + 1) u := by
    exact cubeBesovCircPartialNorm_nonneg Q s p q (N + 1) u
  have hK_nonneg : 0 ≤ max 1 ((3 : ℝ) ^ s) := by
    exact le_trans (by norm_num) (le_max_left 1 ((3 : ℝ) ^ s))
  have hgNorm : cubeBesovDualTestNorm Q s p q N g ≤ 1 := hg.norm_le_one
  have hgMem :
      ∀ j < N + 1, ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp (cubeFluctuation R g) pConj (normalizedCubeMeasure R) := by
    intro j hj R hR
    simpa [pConj] using hg.memLp_admissible j hj R hR
  have huMem :
      ∀ j < N + 1, ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp (cubeProjection Q (j + 1) u)
          (cubeBesovConjExponent pConj) (normalizedCubeMeasure R) := by
    intro j hj R hR
    simpa [hpDouble] using
      cubeProjection_succ_memLp_of_mem_descendantsAtDepth
        (Q := Q) (R := R) (j := j) p u hR
  have hgPosNorm :
      cubeBesovPartialNorm Q s pConj qConj N g ≤ 1 := by
    rw [cubeBesovDualTestNorm_of_conjExponent_ne_top Q s p q N g hqConjTop] at hgNorm
    simpa [pConj, qConj] using hgNorm
  have hpair :
      |cubeBesovPairing Q g (cubeProjection Q (N + 1) u)| ≤
        max 1 ((3 : ℝ) ^ s) *
          cubeBesovPartialNorm Q s pConj qConj N g *
          cubeBesovCircPartialNorm Q s p q (N + 1) u := by
    simpa [pConj, qConj, hpDouble, hqDouble] using
      abs_cubeBesovPairing_projection_le_max_mul_cubeBesovPartialNorm_cubeBesovCircPartialNorm
        (Q := Q) (s := s) (p := pConj) (q := qConj) (f := g) (g := u) (N := N)
        huInt hpConj hpConjTop hpDoubleTop hqConj hqConjTop hqDoubleTop hgMem huMem
  calc
    |cubeBesovPairing Q (cubeProjection Q (N + 1) u) g|
        = |cubeBesovPairing Q g (cubeProjection Q (N + 1) u)| := by
            simp [cubeBesovPairing, mul_comm]
    _ ≤ max 1 ((3 : ℝ) ^ s) *
          cubeBesovPartialNorm Q s pConj qConj N g *
          cubeBesovCircPartialNorm Q s p q (N + 1) u := hpair
    _ ≤ (max 1 ((3 : ℝ) ^ s) * 1) *
          cubeBesovCircPartialNorm Q s p q (N + 1) u := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hgPosNorm hK_nonneg) hCirc_nonneg
    _ = max 1 ((3 : ℝ) ^ s) *
          cubeBesovCircPartialNorm Q s p q (N + 1) u := by
          ring

theorem abs_cubeBesovPairing_projection_le_max_mul_cubeBesovCircNormEntry_of_dual_test
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (u g : Vec d → ℝ)
    (huInt : MeasureTheory.IntegrableOn u (cubeSet Q) MeasureTheory.volume)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞) (hpConjTop : cubeBesovConjExponent p ≠ ∞)
    (hq : 1 ≤ q) (hg : CubeBesovDualTest Q s p q N g) :
    |cubeBesovPairing Q (cubeProjection Q (N + 1) u) g| ≤
      max 1 ((3 : ℝ) ^ s) * cubeBesovCircNormEntry Q s p q N u := by
  let pConj : ℝ≥0∞ := cubeBesovConjExponent p
  let qConj : ℝ≥0∞ := cubeBesovConjExponent q
  have hpHolder : ENNReal.HolderConjugate p pConj := by
    simpa [pConj, cubeBesovConjExponent] using ENNReal.HolderConjugate.conjExponent hp
  let : ENNReal.HolderConjugate p pConj := hpHolder
  let : ENNReal.HolderConjugate pConj p := inferInstance
  have hqHolder : ENNReal.HolderConjugate q qConj := by
    simpa [qConj, cubeBesovConjExponent] using ENNReal.HolderConjugate.conjExponent hq
  let : ENNReal.HolderConjugate q qConj := hqHolder
  let : ENNReal.HolderConjugate qConj q := inferInstance
  have hpConj : 1 ≤ pConj := by
    simpa [pConj] using (ENNReal.HolderConjugate.one_le (p := pConj) (q := p))
  have hpDouble : cubeBesovConjExponent pConj = p := by
    simpa [pConj, cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := pConj) (q := p))
  have hpDoubleTop : cubeBesovConjExponent pConj ≠ ∞ := by
    simpa [hpDouble] using hpTop
  have hK_nonneg : 0 ≤ max 1 ((3 : ℝ) ^ s) := by
    exact le_trans (by norm_num) (le_max_left 1 ((3 : ℝ) ^ s))
  have hgNorm : cubeBesovDualTestNorm Q s p q N g ≤ 1 := hg.norm_le_one
  have hgMem :
      ∀ j < N + 1, ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp (cubeFluctuation R g) pConj (normalizedCubeMeasure R) := by
    intro j hj R hR
    simpa [pConj] using hg.memLp_admissible j hj R hR
  have huMem :
      ∀ j < N + 1, ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp (cubeProjection Q (j + 1) u)
          (cubeBesovConjExponent pConj) (normalizedCubeMeasure R) := by
    intro j hj R hR
    simpa [hpDouble] using
      cubeProjection_succ_memLp_of_mem_descendantsAtDepth
        (Q := Q) (R := R) (j := j) p u hR
  by_cases hqTop : q = ∞
  · have hqConj_eq : qConj = 1 := by
      exact (ENNReal.HolderConjugate.eq_top_iff_eq_one (p := q) (q := qConj)).1 hqTop
    have hqConjTop : qConj ≠ ∞ := by
      simp [hqConj_eq]
    have hgPosNorm :
        cubeBesovPartialNorm Q s pConj 1 N g ≤ 1 := by
      rw [cubeBesovDualTestNorm_of_conjExponent_ne_top Q s p q N g hqConjTop] at hgNorm
      simpa [pConj, qConj, hqConj_eq] using hgNorm
    have hpair :
        |cubeBesovPairing Q g (cubeProjection Q (N + 1) u)| ≤
          max 1 ((3 : ℝ) ^ s) *
            cubeBesovPartialNorm Q s pConj 1 N g *
            cubeBesovCircPartialNormTop Q s p (N + 1) u := by
      simpa [pConj, hpDouble] using
        abs_cubeBesovPairing_projection_le_max_mul_cubeBesovPartialNormOne_cubeBesovCircPartialNormTop
          (Q := Q) (s := s) (p := pConj) (f := g) (g := u) (N := N)
          huInt hpConj hpConjTop hpDoubleTop hgMem huMem
    have hCirc_nonneg : 0 ≤ cubeBesovCircNormEntry Q s p q N u := by
      simpa [cubeBesovCircNormEntry, hqTop] using
        cubeBesovCircPartialNormTop_nonneg Q s p (N + 1) u
    calc
      |cubeBesovPairing Q (cubeProjection Q (N + 1) u) g|
          = |cubeBesovPairing Q g (cubeProjection Q (N + 1) u)| := by
              simp [cubeBesovPairing, mul_comm]
      _ ≤ max 1 ((3 : ℝ) ^ s) *
            cubeBesovPartialNorm Q s pConj 1 N g *
            cubeBesovCircPartialNormTop Q s p (N + 1) u := hpair
      _ ≤ (max 1 ((3 : ℝ) ^ s) * 1) * cubeBesovCircPartialNormTop Q s p (N + 1) u := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hgPosNorm hK_nonneg)
              (cubeBesovCircPartialNormTop_nonneg Q s p (N + 1) u)
      _ = max 1 ((3 : ℝ) ^ s) * cubeBesovCircNormEntry Q s p q N u := by
            simp [cubeBesovCircNormEntry, hqTop]
  · by_cases hqConjTop : qConj = ∞
    · have hqOne : q = 1 := by
        exact (ENNReal.HolderConjugate.eq_top_iff_eq_one (p := qConj) (q := q)).1 hqConjTop
      have hgPosNorm :
          cubeBesovPartialNormTop Q s pConj N g ≤ 1 := by
        rw [cubeBesovDualTestNorm_of_conjExponent_eq_top Q s p q N g hqConjTop] at hgNorm
        simpa [pConj] using hgNorm
      have hpair :
          |cubeBesovPairing Q g (cubeProjection Q (N + 1) u)| ≤
            max 1 ((3 : ℝ) ^ s) *
              cubeBesovPartialNormTop Q s pConj N g *
              cubeBesovCircPartialNorm Q s p 1 (N + 1) u := by
        simpa [pConj, hpDouble] using
          abs_cubeBesovPairing_projection_le_max_mul_cubeBesovPartialNormTop_cubeBesovCircPartialNormOne
            (Q := Q) (s := s) (p := pConj) (f := g) (g := u) (N := N)
            huInt hpConj hpConjTop hpDoubleTop hgMem huMem
      have hCirc_nonneg : 0 ≤ cubeBesovCircNormEntry Q s p q N u := by
        simpa [cubeBesovCircNormEntry, hqTop, hqOne] using
          cubeBesovCircPartialNorm_nonneg Q s p 1 (N + 1) u
      calc
        |cubeBesovPairing Q (cubeProjection Q (N + 1) u) g|
            = |cubeBesovPairing Q g (cubeProjection Q (N + 1) u)| := by
                simp [cubeBesovPairing, mul_comm]
        _ ≤ max 1 ((3 : ℝ) ^ s) *
              cubeBesovPartialNormTop Q s pConj N g *
              cubeBesovCircPartialNorm Q s p 1 (N + 1) u := hpair
        _ ≤ (max 1 ((3 : ℝ) ^ s) * 1) * cubeBesovCircPartialNorm Q s p 1 (N + 1) u := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hgPosNorm hK_nonneg)
                (cubeBesovCircPartialNorm_nonneg Q s p 1 (N + 1) u)
        _ = max 1 ((3 : ℝ) ^ s) * cubeBesovCircNormEntry Q s p q N u := by
              simp [cubeBesovCircNormEntry, hqOne]
    · have hqConj : 1 ≤ qConj := by
        simpa [qConj] using (ENNReal.HolderConjugate.one_le (p := qConj) (q := q))
      have hqDouble : cubeBesovConjExponent qConj = q := by
        simpa [qConj, cubeBesovConjExponent] using
          (ENNReal.HolderConjugate.conjExponent_eq (p := qConj) (q := q))
      have hqDoubleTop : cubeBesovConjExponent qConj ≠ ∞ := by
        simpa [hqDouble] using hqTop
      have hgPosNorm :
          cubeBesovPartialNorm Q s pConj qConj N g ≤ 1 := by
        rw [cubeBesovDualTestNorm_of_conjExponent_ne_top Q s p q N g hqConjTop] at hgNorm
        simpa [pConj, qConj] using hgNorm
      have hpair :
          |cubeBesovPairing Q g (cubeProjection Q (N + 1) u)| ≤
            max 1 ((3 : ℝ) ^ s) *
              cubeBesovPartialNorm Q s pConj qConj N g *
              cubeBesovCircPartialNorm Q s p q (N + 1) u := by
        simpa [pConj, qConj, hpDouble, hqDouble] using
          abs_cubeBesovPairing_projection_le_max_mul_cubeBesovPartialNorm_cubeBesovCircPartialNorm
            (Q := Q) (s := s) (p := pConj) (q := qConj) (f := g) (g := u) (N := N)
            huInt hpConj hpConjTop hpDoubleTop hqConj hqConjTop hqDoubleTop hgMem huMem
      have hCirc_nonneg : 0 ≤ cubeBesovCircNormEntry Q s p q N u := by
        simpa [cubeBesovCircNormEntry, hqTop] using
          cubeBesovCircPartialNorm_nonneg Q s p q (N + 1) u
      calc
        |cubeBesovPairing Q (cubeProjection Q (N + 1) u) g|
            = |cubeBesovPairing Q g (cubeProjection Q (N + 1) u)| := by
                simp [cubeBesovPairing, mul_comm]
        _ ≤ max 1 ((3 : ℝ) ^ s) *
              cubeBesovPartialNorm Q s pConj qConj N g *
              cubeBesovCircPartialNorm Q s p q (N + 1) u := hpair
        _ ≤ (max 1 ((3 : ℝ) ^ s) * 1) * cubeBesovCircPartialNorm Q s p q (N + 1) u := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hgPosNorm hK_nonneg)
                (cubeBesovCircPartialNorm_nonneg Q s p q (N + 1) u)
        _ = max 1 ((3 : ℝ) ^ s) * cubeBesovCircNormEntry Q s p q N u := by
              simp [cubeBesovCircNormEntry, hqTop]

theorem cubeBesovDualPartialSeminorm_projection_le_max_mul_cubeBesovCircPartialNorm
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ)
    (huInt : MeasureTheory.IntegrableOn u (cubeSet Q) MeasureTheory.volume)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞) (hpConjTop : cubeBesovConjExponent p ≠ ∞)
    (hq : 1 ≤ q) (hqTop : q ≠ ∞) (hqConjTop : cubeBesovConjExponent q ≠ ∞) :
    cubeBesovDualPartialSeminorm Q s p q N (cubeProjection Q (N + 1) u) ≤
      max 1 ((3 : ℝ) ^ s) *
        cubeBesovCircPartialNorm Q s p q (N + 1) u := by
  have hpConj0 : cubeBesovConjExponent p ≠ 0 := cubeBesovConjExponent_ne_zero p
  have hqConj0 : cubeBesovConjExponent q ≠ 0 := cubeBesovConjExponent_ne_zero q
  unfold cubeBesovDualPartialSeminorm
  refine csSup_le ?_ ?_
  · refine ⟨0, ?_⟩
    refine ⟨fun _ => (0 : ℝ), ?_, ?_⟩
    · refine ⟨?_, by simpa using cubeAverage_const Q (0 : ℝ), ?_⟩
      · rw [cubeBesovDualTestSeminorm_of_conjExponent_ne_top Q s p q N (fun _ => (0 : ℝ)) hqConjTop]
        rw [cubeBesovPartialSeminorm_zero (Q := Q) (s := s)
          (p := cubeBesovConjExponent p) (q := cubeBesovConjExponent q) (N := N)
          hpConj0 hpConjTop hqConj0 hqConjTop]
        norm_num
      · simpa using cubeBesovDualLocalMemLp_const Q p N (0 : ℝ)
    · simp [cubeBesovPairing, cubeAverage_const]
  · intro r hr
    rcases hr with ⟨g, hg, rfl⟩
    exact abs_cubeBesovPairing_projection_le_max_mul_cubeBesovCircPartialNorm_of_dual_test
      (Q := Q) (s := s) (p := p) (q := q) (N := N) (u := u) (g := g)
      huInt hp hpTop hpConjTop hq hqTop hqConjTop hg.to_dual_test


end Homogenization
