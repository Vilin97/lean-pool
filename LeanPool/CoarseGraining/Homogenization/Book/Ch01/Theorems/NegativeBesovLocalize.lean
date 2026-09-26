/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch01.Theorems.PositiveBesovLocalize
public import LeanPool.CoarseGraining.Homogenization.Besov.Duality.CaccioppoliBridge

/-! # Negative Besov Localize -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch01

noncomputable section

open scoped BigOperators ENNReal

/-!
# Legacy negative Besov localization scaffolding

This file records the legacy totalized/disjoint-real negative Besov
localization API retained for downstream compatibility.  The proof pairs a
parent mean-zero dual test against the descendants, applies the local full-dual
bound on each descendant, and closes with the positive Besov localization
estimate for the test.
-/

namespace Legacy

/-- Bound the mean-zero dual negative Besov seminorm by bounding its pairing
against every global mean-zero unit test. -/
theorem cubeBesovDualMeanZeroSeminorm_le_of_forall_meanZeroTest_pairing_le {d : ℕ}
    (Q : Cube d) (s : ℝ) (p q : ℝ≥0∞) (f : Vec d → ℝ) {B : ℝ}
    (hp0 : cubeBesovConjExponent p ≠ 0)
    (hpTop : cubeBesovConjExponent p ≠ ∞)
    (hB : ∀ g : Vec d → ℝ,
      CubeBesovDualMeanZeroTestGlobal Q s p q g →
        |cubeBesovPairing Q f g| ≤ B) :
    dualNegativeBesovSeminorm Q s p q f ≤ B := by
  unfold dualNegativeBesovSeminorm cubeBesovDualMeanZeroSeminorm
  refine csSup_le
    (cubeBesovDualMeanZeroSeminormValueSet_nonempty Q s p q f hp0 hpTop) ?_
  intro r hr
  rcases hr with ⟨g, hg, rfl⟩
  exact hB g hg

/-- Split a parent cube Besov pairing into the normalized average of descendant
pairings. -/
theorem cubeBesovPairing_eq_descendantsAverage_pairing_of_integrableOn {d : ℕ}
    (Q : Cube d) (j : ℕ) (f g : Vec d → ℝ)
    (hfg : MeasureTheory.IntegrableOn (fun x => f x * g x)
      (cubeSet Q) MeasureTheory.volume) :
    cubeBesovPairing Q f g =
      descendantsAverage Q j (fun R => cubeBesovPairing R f g) := by
  unfold cubeBesovPairing
  rw [cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
    Q j (fun x => f x * g x) hfg]

/-- Triangle-inequality form of the descendant pairing split. -/
theorem abs_cubeBesovPairing_le_descendantsAverage_abs_pairing_of_integrableOn {d : ℕ}
    (Q : Cube d) (j : ℕ) (f g : Vec d → ℝ)
    (hfg : MeasureTheory.IntegrableOn (fun x => f x * g x)
      (cubeSet Q) MeasureTheory.volume) :
    |cubeBesovPairing Q f g| ≤
      descendantsAverage Q j (fun R => |cubeBesovPairing R f g|) := by
  classical
  have hsplit := cubeBesovPairing_eq_descendantsAverage_pairing_of_integrableOn
    Q j f g hfg
  let D : Finset (Cube d) := descendantsAtDepth Q j
  let c : ℝ := (D.card : ℝ)⁻¹
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact inv_nonneg.mpr (by positivity)
  calc
    |cubeBesovPairing Q f g|
        = |descendantsAverage Q j (fun R => cubeBesovPairing R f g)| := by
            rw [hsplit]
    _ = |c * ∑ R ∈ D, cubeBesovPairing R f g| := by
          rfl
    _ = c * |∑ R ∈ D, cubeBesovPairing R f g| := by
          rw [abs_mul, abs_of_nonneg hc_nonneg]
    _ ≤ c * ∑ R ∈ D, |cubeBesovPairing R f g| := by
          exact mul_le_mul_of_nonneg_left
            (Finset.abs_sum_le_sum_abs (fun R => cubeBesovPairing R f g) D)
            hc_nonneg
    _ = descendantsAverage Q j (fun R => |cubeBesovPairing R f g|) := by
          rfl

/-- A global dual-test local `MemLp` hypothesis restricts to descendants. -/
theorem cubeBesovDualLocalMemLpGlobal_restrict_to_descendant {d : ℕ}
    {Q R : Cube d} {j : ℕ} {p : ℝ≥0∞} {g : Vec d → ℝ}
    (hg : CubeBesovDualLocalMemLpGlobal Q p g)
    (hR : R ∈ descendantsAtDepth Q j) :
    CubeBesovDualLocalMemLpGlobal R p g := by
  intro n S hS
  exact hg (j + n) S (mem_descendantsAtDepth_add hR hS)

theorem abs_cubeBesovPairing_le_mul_cubeBesovDualFullNorm_of_uniform_bound_two_two_of_nonneg
    {d : ℕ} (Q : Cube d) (s : ℝ) (u g : Vec d → ℝ) {B : ℝ}
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : 0 ≤ B)
    (hnorm : ∀ N : ℕ,
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N g ≤ B)
    (hmem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) g) :
    |cubeBesovPairing Q u g| ≤
      cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u * B := by
  let A : ℝ := cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u
  have hpConj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq
        (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact cubeBesovDualFullNorm_nonneg Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u
      (by rw [hpConj]; norm_num) (by rw [hpConj]; norm_num)
  change |cubeBesovPairing Q u g| ≤ A * B
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ : ℝ := ε / (A + 1)
  have hA1_pos : 0 < A + 1 := by linarith
  have hδ_pos : 0 < δ := div_pos hε hA1_pos
  have hBδ_pos : 0 < B + δ := add_pos_of_nonneg_of_pos hB hδ_pos
  have hnormδ :
      ∀ N : ℕ, cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N g ≤
        B + δ := by
    intro N
    exact (hnorm N).trans (le_add_of_nonneg_right hδ_pos.le)
  have hstrict :=
    abs_cubeBesovPairing_le_mul_cubeBesovDualFullNorm_of_uniform_bound_two_two
      Q s u g hs hu hBδ_pos hnormδ hmem
  have hAδ_le : A * δ ≤ ε := by
    have hratio : A / (A + 1) ≤ 1 := by
      exact (div_le_one hA1_pos).mpr (by linarith)
    calc
      A * δ = ε * (A / (A + 1)) := by
        dsimp [δ]
        field_simp [ne_of_gt hA1_pos]
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hratio hε.le
      _ = ε := by ring
  calc
    |cubeBesovPairing Q u g| ≤ A * (B + δ) := by
      simpa [A] using hstrict
    _ = A * B + A * δ := by ring
    _ ≤ A * B + ε := by linarith

/-- Local full-dual pairing bound with the Chapter 1 positive `q = 2` norm as
the test size. -/
theorem abs_cubeBesovPairing_le_dualNegativeBesovNorm_mul_positiveBesovNormTwo
    {d : ℕ} (Q : Cube d) (s : ℝ) (u g : Vec d → ℝ)
    (hs : 0 < s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        positiveBesovPartialNormTwo Q s (N + 1) g))
    (hmem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) g) :
    |cubeBesovPairing Q u g| ≤
      dualNegativeBesovNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) u *
        positiveBesovNormTwo Q s g := by
  have hB_nonneg : 0 ≤ positiveBesovNormTwo Q s g :=
    positiveBesovNormTwo_nonneg_of_bddAbove Q s g hBdd
  have hpConj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq
        (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hqConjTop : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
    rw [hpConj]
    norm_num
  have hnorm :
      ∀ N : ℕ,
        cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N g ≤
          positiveBesovNormTwo Q s g := by
    intro N
    rw [cubeBesovDualTestNorm_of_conjExponent_ne_top
      Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N g hqConjTop]
    have hpartial := positiveBesovPartialNormTwo_le_normTwo_of_bddAbove Q s g hBdd N
    simpa [positiveBesovPartialNormTwo, hpConj] using hpartial
  simpa [dualNegativeBesovNorm] using
    abs_cubeBesovPairing_le_mul_cubeBesovDualFullNorm_of_uniform_bound_two_two_of_nonneg
      Q s u g hs hu hB_nonneg hnorm hmem

private theorem integrableOn_mul_of_memLp_two_normalizedCubeMeasure {d : ℕ}
    (Q : Cube d) (f g : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    MeasureTheory.IntegrableOn (fun x => f x * g x)
      (cubeSet Q) MeasureTheory.volume := by
  have hint : MeasureTheory.Integrable (f * g) (normalizedCubeMeasure Q) := by
    exact hf.integrable_mul hg
  exact Homogenization.integrableOn_of_integrable_normalizedCubeMeasure Q
    (by simpa using! hint)

private theorem descendantsAverage_mul_le_sqrt_mul_sqrt {d : ℕ}
    (Q : Cube d) (j : ℕ) (A B : Cube d → ℝ)
    (hA : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ A R)
    (hB : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ B R) :
    descendantsAverage Q j (fun R => A R * B R) ≤
      Real.sqrt (descendantsAverage Q j (fun R => (A R) ^ 2)) *
        Real.sqrt (descendantsAverage Q j (fun R => (B R) ^ 2)) := by
  have hpq : Real.HolderConjugate (2 : ℝ) (2 : ℝ) := by
    refine ⟨?_, ?_, ?_⟩ <;> norm_num
  have h := descendantsAverage_mul_le_Lp_mul_Lq_of_nonneg Q j A B hpq hA hB
  simpa [Real.sqrt_eq_rpow, Real.rpow_natCast] using h

private theorem positiveBesovPartialNormTwo_bddAbove_of_meanZeroTestGlobal {d : ℕ}
    (Q : Cube d) (s : ℝ) (g : Vec d → ℝ)
    (hg : CubeBesovDualMeanZeroTestGlobal Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) g) :
    BddAbove (Set.range fun N : ℕ =>
      positiveBesovPartialNormTwo Q s (N + 1) g) := by
  have hpConj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq
        (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hqConjTop : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
    rw [hpConj]
    norm_num
  refine ⟨1, ?_⟩
  rintro x ⟨N, rfl⟩
  have hnorm :
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (N + 1) g ≤ 1 := by
    rw [cubeBesovDualTestNorm_eq_cubeBesovDualTestSeminorm_of_cubeAverage_eq_zero
      Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (N + 1) g hg.2.1]
    exact hg.1 (N + 1)
  rw [cubeBesovDualTestNorm_of_conjExponent_ne_top
    Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (N + 1) g hqConjTop] at hnorm
  simpa [positiveBesovPartialNormTwo, hpConj] using hnorm

private theorem positiveBesovNormTwo_le_one_of_meanZeroTestGlobal {d : ℕ}
    (Q : Cube d) (s : ℝ) (g : Vec d → ℝ)
    (hg : CubeBesovDualMeanZeroTestGlobal Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) g) :
    positiveBesovNormTwo Q s g ≤ 1 := by
  have hpConj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq
        (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hqConjTop : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
    rw [hpConj]
    norm_num
  unfold positiveBesovNormTwo
  refine csSup_le ?_ ?_
  · exact ⟨positiveBesovPartialNormTwo Q s 1 g, ⟨0, by simp [positiveBesovPartialNormTwo]⟩⟩
  · rintro x ⟨N, rfl⟩
    have hnorm :
        cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (N + 1) g ≤ 1 := by
      rw [cubeBesovDualTestNorm_eq_cubeBesovDualTestSeminorm_of_cubeAverage_eq_zero
        Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (N + 1) g hg.2.1]
      exact hg.1 (N + 1)
    rw [cubeBesovDualTestNorm_of_conjExponent_ne_top
      Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (N + 1) g hqConjTop] at hnorm
    simpa [positiveBesovPartialNormTwo, hpConj] using hnorm

private theorem positiveBesovPartialNormTwo_bddAbove_of_fullTest {d : ℕ}
    (Q : Cube d) (s : ℝ) (g : Vec d → ℝ)
    (hg : CubeBesovDualFullTest Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) g) :
    BddAbove (Set.range fun N : ℕ =>
      positiveBesovPartialNormTwo Q s (N + 1) g) := by
  have hpConj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq
        (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hqConjTop : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
    rw [hpConj]
    norm_num
  refine ⟨1, ?_⟩
  rintro x ⟨N, rfl⟩
  have hnorm :
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (N + 1) g ≤ 1 :=
    hg.1 (N + 1)
  rw [cubeBesovDualTestNorm_of_conjExponent_ne_top
    Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (N + 1) g hqConjTop] at hnorm
  simpa [positiveBesovPartialNormTwo, hpConj] using hnorm

private theorem positiveBesovNormTwo_le_one_of_fullTest {d : ℕ}
    (Q : Cube d) (s : ℝ) (g : Vec d → ℝ)
    (hg : CubeBesovDualFullTest Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) g) :
    positiveBesovNormTwo Q s g ≤ 1 := by
  have hpConj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq
        (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hqConjTop : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
    rw [hpConj]
    norm_num
  unfold positiveBesovNormTwo
  refine csSup_le ?_ ?_
  · exact ⟨positiveBesovPartialNormTwo Q s 1 g, ⟨0, by simp [positiveBesovPartialNormTwo]⟩⟩
  · rintro x ⟨N, rfl⟩
    have hnorm :
        cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (N + 1) g ≤ 1 :=
      hg.1 (N + 1)
    rw [cubeBesovDualTestNorm_of_conjExponent_ne_top
      Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (N + 1) g hqConjTop] at hnorm
    simpa [positiveBesovPartialNormTwo, hpConj] using hnorm

private theorem positiveBesovPartialNormTwo_bddAbove_of_parent_bddAbove {d : ℕ}
    {Q R : Cube d} {j : ℕ} (s : ℝ) (u : Vec d → ℝ)
    (hs : 0 ≤ s)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hR : R ∈ descendantsAtDepth Q j)
    (hParentBdd :
      BddAbove (Set.range fun N : ℕ =>
        positiveBesovPartialNormTwo Q s (N + 1) u)) :
    BddAbove (Set.range fun N : ℕ =>
      positiveBesovPartialNormTwo R s (N + 1) u) := by
  classical
  rcases hParentBdd with ⟨B, hB⟩
  have hB_nonneg : 0 ≤ B := by
    have hB0 : positiveBesovPartialNormTwo Q s (0 + 1) u ≤ B := hB ⟨0, rfl⟩
    exact (positiveBesovPartialNormTwo_nonneg Q s 1 u).trans hB0
  let D : Finset (Cube d) := descendantsAtDepth Q j
  let c : ℝ := Real.rpow (3 : ℝ) (-(s * (j : ℝ)))
  have hc_pos : 0 < c := by
    dsimp [c]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hc_nonneg : 0 ≤ c := hc_pos.le
  have hD_nonempty : D.Nonempty := by
    simpa [D] using descendantsAtDepth_nonempty Q j
  have hcard_pos : 0 < (D.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hD_nonempty
  have hcard_nonneg : 0 ≤ (D.card : ℝ) := le_of_lt hcard_pos
  refine ⟨c⁻¹ * Real.sqrt ((D.card : ℝ) * (2 * B) ^ 2), ?_⟩
  rintro x ⟨N, rfl⟩
  let F : Cube d → ℝ :=
    fun S => (c * positiveBesovPartialNormTwo S s (N + 1) u) ^ 2
  have hparent_le : positiveBesovPartialNormTwo Q s (j + (N + 1)) u ≤ B := by
    have hidx : j + (N + 1) = (j + N) + 1 := by omega
    rw [hidx]
    exact hB ⟨j + N, rfl⟩
  have hparent_nonneg : 0 ≤ positiveBesovPartialNormTwo Q s (j + (N + 1)) u :=
    positiveBesovPartialNormTwo_nonneg Q s (j + (N + 1)) u
  have hparent_sq_le :
      (2 * positiveBesovPartialNormTwo Q s (j + (N + 1)) u) ^ 2 ≤
        (2 * B) ^ 2 := by
    nlinarith
  have havg_le_parent :
      descendantsAverage Q j F ≤
        (2 * positiveBesovPartialNormTwo Q s (j + (N + 1)) u) ^ 2 := by
    dsimp [F, c]
    exact descendantsAverage_sq_scaled_positiveBesovPartialNormTwo_le Q s u j (N + 1) hs hu
  have havg_le_Bsq : descendantsAverage Q j F ≤ (2 * B) ^ 2 :=
    havg_le_parent.trans hparent_sq_le
  have hsum_le : (∑ S ∈ D, F S) ≤ (D.card : ℝ) * (2 * B) ^ 2 := by
    have hmul : (D.card : ℝ) * descendantsAverage Q j F ≤
        (D.card : ℝ) * (2 * B) ^ 2 :=
      mul_le_mul_of_nonneg_left havg_le_Bsq hcard_nonneg
    have hdesc : (D.card : ℝ) * descendantsAverage Q j F = ∑ S ∈ D, F S := by
      dsimp [descendantsAverage, D]
      field_simp [ne_of_gt hcard_pos]
    rwa [hdesc] at hmul
  have hterm_le_sum : F R ≤ ∑ S ∈ D, F S := by
    exact Finset.single_le_sum
      (fun S hS => sq_nonneg (c * positiveBesovPartialNormTwo S s (N + 1) u))
      (by simpa [D] using hR)
  have hterm_sq_le :
      (c * positiveBesovPartialNormTwo R s (N + 1) u) ^ 2 ≤
        (D.card : ℝ) * (2 * B) ^ 2 :=
    hterm_le_sum.trans hsum_le
  have hcx_le :
      c * positiveBesovPartialNormTwo R s (N + 1) u ≤
        Real.sqrt ((D.card : ℝ) * (2 * B) ^ 2) :=
    Real.le_sqrt_of_sq_le hterm_sq_le
  have hx_eq : positiveBesovPartialNormTwo R s (N + 1) u =
      c⁻¹ * (c * positiveBesovPartialNormTwo R s (N + 1) u) := by
    field_simp [hc_pos.ne']
  change positiveBesovPartialNormTwo R s (N + 1) u ≤
    c⁻¹ * Real.sqrt ((D.card : ℝ) * (2 * B) ^ 2)
  rw [hx_eq]
  exact mul_le_mul_of_nonneg_left hcx_le (inv_nonneg.mpr hc_nonneg)

private theorem negativeBesovLocalize_pairing_le_of_parent_test_bound {d : ℕ}
    (Q : Cube d) (s : ℝ) (f g : Vec d → ℝ) (j : ℕ)
    (hs : 0 < s)
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hgMem : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hParentBdd :
      BddAbove (Set.range fun N : ℕ =>
        positiveBesovPartialNormTwo Q s (N + 1) g))
    (hLocalMem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) g)
    (hParentPos_le_one : positiveBesovNormTwo Q s g ≤ 1) :
    |cubeBesovPairing Q f g| ≤
      negativeBesovLocalizeConstant d *
        Real.sqrt
          (descendantsAverage Q j fun R =>
            (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
              dualNegativeBesovNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f) ^ 2) := by
  classical
  let a : ℝ := Real.rpow (3 : ℝ) (s * (j : ℝ))
  let b : ℝ := Real.rpow (3 : ℝ) (-(s * (j : ℝ)))
  let negRms : ℝ :=
    Real.sqrt
      (descendantsAverage Q j fun R =>
        (a * dualNegativeBesovNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f) ^ 2)
  have hpConj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq
        (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hp0 : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ 0 := by
    rw [hpConj]
    norm_num
  have hpTop : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
    rw [hpConj]
    norm_num
  have ha_pos : 0 < a := by
    dsimp [a]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hb_pos : 0 < b := by
    dsimp [b]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hab : a * b = 1 := by
    dsimp [a, b]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    ring_nf
    norm_num
  have hfg :
      MeasureTheory.IntegrableOn (fun x => f x * g x)
        (cubeSet Q) MeasureTheory.volume :=
    integrableOn_mul_of_memLp_two_normalizedCubeMeasure Q f g hf hgMem
  have hLocalBdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          positiveBesovPartialNormTwo R s (N + 1) g) := by
    intro R hR
    exact positiveBesovPartialNormTwo_bddAbove_of_parent_bddAbove
      s g hs.le hgMem hR hParentBdd
  have hParentPos_nonneg : 0 ≤ positiveBesovNormTwo Q s g :=
    positiveBesovNormTwo_nonneg_of_bddAbove Q s g hParentBdd
  have hposSq :
      descendantsAverage Q j
          (fun R => (b * positiveBesovNormTwo R s g) ^ 2) ≤
        (2 * positiveBesovNormTwo Q s g) ^ 2 := by
    dsimp [b]
    exact descendantsAverage_sq_scaled_positiveBesovNormTwo_le
      Q s g j hs.le hgMem hParentBdd hLocalBdd
  have hposRms_le_two :
      Real.sqrt
          (descendantsAverage Q j
            (fun R => (b * positiveBesovNormTwo R s g) ^ 2)) ≤ 2 := by
    have htwo_parent_nonneg : 0 ≤ 2 * positiveBesovNormTwo Q s g := by
      nlinarith
    calc
      Real.sqrt
          (descendantsAverage Q j
            (fun R => (b * positiveBesovNormTwo R s g) ^ 2))
          ≤ Real.sqrt ((2 * positiveBesovNormTwo Q s g) ^ 2) :=
            Real.sqrt_le_sqrt hposSq
      _ = |2 * positiveBesovNormTwo Q s g| := by
            rw [Real.sqrt_sq_eq_abs]
      _ = 2 * positiveBesovNormTwo Q s g := by
            rw [abs_of_nonneg htwo_parent_nonneg]
      _ ≤ 2 := by
            nlinarith
  have havg_pair_scaled :
      descendantsAverage Q j (fun R => |cubeBesovPairing R f g|) ≤
        descendantsAverage Q j
          (fun R =>
            (a * dualNegativeBesovNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f) *
              (b * positiveBesovNormTwo R s g)) := by
    refine descendantsAverage_le_descendantsAverage Q j ?_
    intro R hR
    have hfR : MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
      memLp_on_descendant_of_memLp (Q := Q) (R := R) (j := j) hR hf
    have hPairR :
        |cubeBesovPairing R f g| ≤
          dualNegativeBesovNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f *
            positiveBesovNormTwo R s g :=
      abs_cubeBesovPairing_le_dualNegativeBesovNorm_mul_positiveBesovNormTwo
        R s f g hs hfR (hLocalBdd R hR)
        (cubeBesovDualLocalMemLpGlobal_restrict_to_descendant hLocalMem hR)
    calc
      |cubeBesovPairing R f g| ≤
          dualNegativeBesovNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f *
            positiveBesovNormTwo R s g := hPairR
      _ =
          (a * dualNegativeBesovNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f) *
            (b * positiveBesovNormTwo R s g) := by
            calc
              dualNegativeBesovNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f *
                  positiveBesovNormTwo R s g =
                (a * b) *
                  (dualNegativeBesovNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f *
                    positiveBesovNormTwo R s g) := by
                  rw [hab]
                  ring
              _ =
                (a * dualNegativeBesovNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f) *
                  (b * positiveBesovNormTwo R s g) := by
                  ring
  have hA_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ a * dualNegativeBesovNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f := by
    intro R _hR
    exact mul_nonneg ha_pos.le
      (by
        simpa [dualNegativeBesovNorm] using
          cubeBesovDualFullNorm_nonneg R s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f hp0 hpTop)
  have hB_nonneg :
      ∀ R ∈ descendantsAtDepth Q j, 0 ≤ b * positiveBesovNormTwo R s g := by
    intro R hR
    exact mul_nonneg hb_pos.le
      (positiveBesovNormTwo_nonneg_of_bddAbove R s g (hLocalBdd R hR))
  have hcauchy :
      descendantsAverage Q j
          (fun R =>
            (a * dualNegativeBesovNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f) *
              (b * positiveBesovNormTwo R s g)) ≤
        negRms *
          Real.sqrt
            (descendantsAverage Q j
              (fun R => (b * positiveBesovNormTwo R s g) ^ 2)) := by
    dsimp [negRms]
    exact descendantsAverage_mul_le_sqrt_mul_sqrt Q j
      (fun R => a * dualNegativeBesovNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f)
      (fun R => b * positiveBesovNormTwo R s g) hA_nonneg hB_nonneg
  have hsplit :=
    abs_cubeBesovPairing_le_descendantsAverage_abs_pairing_of_integrableOn
      Q j f g hfg
  have hnegRms_nonneg : 0 ≤ negRms := by
    dsimp [negRms]
    exact Real.sqrt_nonneg _
  calc
    |cubeBesovPairing Q f g|
        ≤ descendantsAverage Q j (fun R => |cubeBesovPairing R f g|) := hsplit
    _ ≤ descendantsAverage Q j
          (fun R =>
            (a * dualNegativeBesovNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f) *
              (b * positiveBesovNormTwo R s g)) := havg_pair_scaled
    _ ≤ negRms *
          Real.sqrt
            (descendantsAverage Q j
              (fun R => (b * positiveBesovNormTwo R s g) ^ 2)) := hcauchy
    _ ≤ negRms * 2 := by
          exact mul_le_mul_of_nonneg_left hposRms_le_two hnegRms_nonneg
    _ = negativeBesovLocalizeConstant d *
        Real.sqrt
          (descendantsAverage Q j fun R =>
            (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
              dualNegativeBesovNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f) ^ 2) := by
          dsimp [negRms, a, negativeBesovLocalizeConstant]
          ring

/-- Manuscript negative Besov localization, with the parent `L²` hypothesis
already converted to the normalized cube measure. -/
theorem negativeBesovLocalize_of_memLp {d : ℕ}
    (Q : Cube d) (s : ℝ) (f : Vec d → ℝ) (j : ℕ)
    (hs : 0 < s)
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    dualNegativeBesovSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f ≤
      negativeBesovLocalizeConstant d *
        Real.sqrt
          (descendantsAverage Q j fun R =>
            (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
              dualNegativeBesovNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f) ^ 2) := by
  have hpConj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq
        (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hp0 : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ 0 := by
    rw [hpConj]
    norm_num
  have hpTop : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
    rw [hpConj]
    norm_num
  refine cubeBesovDualMeanZeroSeminorm_le_of_forall_meanZeroTest_pairing_le
    Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f hp0 hpTop ?_
  intro g hg
  have hgMem : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa [hpConj] using hg.memLp
  have hParentBdd :
      BddAbove (Set.range fun N : ℕ =>
        positiveBesovPartialNormTwo Q s (N + 1) g) :=
    positiveBesovPartialNormTwo_bddAbove_of_meanZeroTestGlobal Q s g hg
  have hParentPos_le_one : positiveBesovNormTwo Q s g ≤ 1 :=
    positiveBesovNormTwo_le_one_of_meanZeroTestGlobal Q s g hg
  exact negativeBesovLocalize_pairing_le_of_parent_test_bound
    Q s f g j hs hf hgMem hParentBdd hg.2.2 hParentPos_le_one

/-- Full-dual companion to the negative Besov localization theorem, with the
parent `L²` hypothesis already converted to the normalized cube measure.

This is not the manuscript mean-zero statement, but it is the componentwise
form used by downstream vector genuine-dual consumers. -/
theorem negativeBesovFullLocalize_of_memLp {d : ℕ}
    (Q : Cube d) (s : ℝ) (f : Vec d → ℝ) (j : ℕ)
    (hs : 0 < s)
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    dualNegativeBesovNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f ≤
      negativeBesovLocalizeConstant d *
        Real.sqrt
          (descendantsAverage Q j fun R =>
            (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
              dualNegativeBesovNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f) ^ 2) := by
  have hpConj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq
        (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hp0 : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ 0 := by
    rw [hpConj]
    norm_num
  have hpTop : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
    rw [hpConj]
    norm_num
  refine cubeBesovDualFullNorm_le_of_forall_fullTest_pairing_le
    Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f hp0 hpTop ?_
  intro g hg
  have hgMem : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa [hpConj] using hg.memLp
  have hParentBdd :
      BddAbove (Set.range fun N : ℕ =>
        positiveBesovPartialNormTwo Q s (N + 1) g) :=
    positiveBesovPartialNormTwo_bddAbove_of_fullTest Q s g hg
  have hParentPos_le_one : positiveBesovNormTwo Q s g ≤ 1 :=
    positiveBesovNormTwo_le_one_of_fullTest Q s g hg
  exact negativeBesovLocalize_pairing_le_of_parent_test_bound
    Q s f g j hs hf hgMem hParentBdd hg.2 hParentPos_le_one

/-- Full-dual companion to `negativeBesovLocalize`, stated with the public
`MemScalarL2` hypothesis. -/
theorem negativeBesovFullLocalize {d : ℕ}
    (Q : Cube d) (s : ℝ) (f : Vec d → ℝ) (j : ℕ)
    (hs : 0 < s)
    (hf : MemScalarL2 (cubeSet Q) f) :
    dualNegativeBesovNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f ≤
      negativeBesovLocalizeConstant d *
        Real.sqrt
          (descendantsAverage Q j fun R =>
            (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
              dualNegativeBesovNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f) ^ 2) := by
  exact negativeBesovFullLocalize_of_memLp Q s f j hs
    (memLp_normalizedCubeMeasure_of_memScalarL2_cubeSet Q hf)

/-- Cube-general form of the negative Besov localization lemma. -/
theorem negativeBesovLocalize_cube {d : ℕ}
    (Q : Cube d) (s : ℝ) (f : Vec d → ℝ) (j : ℕ)
    (hs : 0 < s)
    (hf : MemScalarL2 (cubeSet Q) f) :
    dualNegativeBesovSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f ≤
      negativeBesovLocalizeConstant d *
        Real.sqrt
          (descendantsAverage Q j fun R =>
            (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
              dualNegativeBesovNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f) ^ 2) := by
  exact negativeBesovLocalize_of_memLp Q s f j hs
    (memLp_normalizedCubeMeasure_of_memScalarL2_cubeSet Q hf)

/-- Manuscript Lemma `l.Besov.negative.localize.function.spaces`.
The mean-zero dual negative Besov seminorm of `f` on the origin cube `⌈_m` is
bounded by the geometrically weighted root-mean-square of full local dual
negative Besov norms on each triadic descendant `z + ⌈_n` for `n ≤ m`. -/
theorem negativeBesovLocalize {d : ℕ} {s : ℝ} {m n : ℤ}
    (_hd : 1 ≤ d) (hs_pos : 0 < s) (_hs_lt_one : s < 1)
    (hnm : n ≤ m) (f : Vec d → ℝ)
    (hf : MemScalarL2 (cubeSet (originCube d m)) f) :
    dualNegativeBesovSeminorm (originCube d m) s
        (2 : ℝ≥0∞) (2 : ℝ≥0∞) f ≤
    negativeBesovLocalizeConstant d *
      Real.sqrt
        (descendantsAverage (originCube d m) (Int.toNat (m - n)) fun R =>
          (Real.rpow (3 : ℝ) ((-s) * ((n - m : ℤ) : ℝ)) *
            dualNegativeBesovNorm R s (2 : ℝ≥0∞) (2 : ℝ≥0∞) f) ^ 2) := by
  have hdepth_nonneg : 0 ≤ m - n := sub_nonneg.mpr hnm
  have hdepth_cast : ((Int.toNat (m - n) : ℕ) : ℝ) = ((m - n : ℤ) : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hdepth_nonneg)
  have hfactor :
      Real.rpow (3 : ℝ) (s * ((Int.toNat (m - n) : ℕ) : ℝ)) =
        Real.rpow (3 : ℝ) ((-s) * ((n - m : ℤ) : ℝ)) := by
    congr 1
    rw [hdepth_cast]
    norm_num
    ring
  rw [← hfactor]
  exact negativeBesovLocalize_cube (Q := originCube d m) (s := s) (f := f)
    (j := Int.toNat (m - n)) hs_pos hf

end Legacy

end

end Ch01
end Book
end Homogenization
