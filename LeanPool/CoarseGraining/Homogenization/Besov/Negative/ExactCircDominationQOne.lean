/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Besov.Duality.ProjectedPairing.MainBounds
public import LeanPool.CoarseGraining.Homogenization.Besov.Negative.ExactAggregationBridge
public import LeanPool.CoarseGraining.Homogenization.Besov.Negative.ExactExponentBridge
public import LeanPool.CoarseGraining.Homogenization.Besov.PositiveOverlapBridge

/-!
# Exact circ domination at the negative `q = 1` endpoint

This module proves the source-facing comparison between the exact dual
negative Besov kernel and the exact concrete circ kernel in the `q = 1`
branch.  All local integrability and finite-truncation premises are derived
inside the proof from the single parent `MemLp` certificate.
-/

@[expose] public section

namespace Homogenization

open scoped ENNReal Topology

private theorem exactOverlapTopNorm_eq_seminorm_of_root_mean_eq_zero
    {d : ℕ} (P : ExactOverlapTopParameters) (Q : TriadicCube d)
    (g : Vec d → ℝ) (hg : ExactOverlapIntegrable Q g)
    (hmean : exactOverlapRootMean Q g hg.root = 0) :
    exactOverlapTopNorm P Q g hg = exactOverlapTopSeminorm P Q g hg := by
  rw [exactOverlapTopNorm_eq, hmean]
  simp only [abs_zero, ENNReal.ofReal_zero, mul_zero, add_zero]

private theorem exactDualQOnePairing_le_exactCircFiniteSeminorm
    {d : ℕ} (P : ExactDualQOneParameters) (Q : TriadicCube d)
    (f g : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g
      (ENNReal.ofReal (exactDualConjExponent P.p))
      (Homogenization.normalizedCubeMeasure Q))
    (hgNorm : exactOverlapTopNorm P.positiveParameters Q g
      (exactDualOverlapIntegrable Q (exactDualConjExponent P.p)
        (exactDualConjExponent_one_le P.p P.p_one_lt) hg) ≤ 1) :
    exactDualPairingFromHolder Q P.p f g P.p_one_lt hf hg ≤
      (3 : ℝ≥0∞) ^ ((d : ℝ) + P.s) *
        exactCircFiniteSeminorm P.circParameters Q f
          (exactCircIntegrable_of_memLp Q P.p P.p_one_lt.le hf) := by
  let p' : ℝ := exactDualConjExponent P.p
  let K : ℝ := max 1 ((3 : ℝ) ^ P.s)
  let C : ℝ := (3 : ℝ) ^ ((d : ℝ) / p')
  let X : ℝ≥0∞ := exactCircFiniteSeminorm P.circParameters Q f
    (exactCircIntegrable_of_memLp Q P.p P.p_one_lt.le hf)
  have hp'_one : 1 ≤ p' := by
    exact exactDualConjExponent_one_le P.p P.p_one_lt
  have hp'_pos : 0 < p' := lt_of_lt_of_le zero_lt_one hp'_one
  have hp'_ofReal_one : 1 ≤ ENNReal.ofReal p' := by
    exact ENNReal.one_le_ofReal.mpr hp'_one
  have hp'_ofReal_top : ENNReal.ofReal p' ≠ ∞ := ENNReal.ofReal_ne_top
  have hp'_conj_top : cubeBesovConjExponent (ENNReal.ofReal p') ≠ ∞ := by
    rw [show p' = exactDualConjExponent P.p by rfl,
      cubeBesovConjExponent_exactDualConjExponent_eq_ofReal P.p P.p_one_lt]
    exact ENNReal.ofReal_ne_top
  have htargetInt : MeasureTheory.IntegrableOn f (cubeSet Q) MeasureTheory.volume :=
    integrableOn_of_integrable_normalizedCubeMeasure (Q := Q)
      (hf.integrable (ENNReal.one_le_ofReal.mpr P.p_one_lt.le))
  have hconv := tendsto_cubeBesovPairing_projection_left_of_memLp
    Q (ENNReal.ofReal P.p) f g hf
      (by
        simpa [cubeBesovConjExponent_ofReal_eq_exactDualConjExponent
          P.p P.p_one_lt] using hg)
      (ENNReal.one_le_ofReal.mpr P.p_one_lt.le) ENNReal.ofReal_ne_top
      (cubeBesovConjExponent_ofReal_ne_top P.p P.p_one_lt)
  have hconvAbs :
      Filter.Tendsto
        (fun n ↦ |cubeBesovPairing Q (cubeProjection Q (n + 1) f) g|)
        Filter.atTop (nhds |cubeBesovPairing Q f g|) := by
    simpa [Real.norm_eq_abs] using hconv.norm
  have hconvENNReal :
      Filter.Tendsto
        (fun n ↦ ENNReal.ofReal
          |cubeBesovPairing Q (cubeProjection Q (n + 1) f) g|)
        Filter.atTop (nhds (ENNReal.ofReal |cubeBesovPairing Q f g|)) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hconvAbs
  have hK_nonneg : 0 ≤ K := by
    exact zero_le_one.trans (le_max_left _ _)
  have hC_nonneg : 0 ≤ C := Real.rpow_nonneg (by norm_num) _
  have hCexp_nonneg : 0 ≤ (d : ℝ) / p' :=
    div_nonneg (Nat.cast_nonneg d) hp'_pos.le
  have hp'_toReal_pos : 0 < (ENNReal.ofReal p').toReal := by
    rw [ENNReal.toReal_ofReal hp'_pos.le]
    exact hp'_pos
  have hK_ofReal : ENNReal.ofReal K = max 1 ((3 : ℝ≥0∞) ^ P.s) := by
    dsimp only [K]
    rw [ENNReal.ofReal_max,
      ← ENNReal.ofReal_rpow_of_nonneg (by norm_num : 0 ≤ (3 : ℝ)) P.s_pos.le]
    norm_num
  have hC_ofReal : ENNReal.ofReal C = (3 : ℝ≥0∞) ^ ((d : ℝ) / p') := by
    dsimp only [C]
    rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num : 0 ≤ (3 : ℝ)) hCexp_nonneg]
    norm_num
  have hbound : ∀ n : ℕ,
      ENNReal.ofReal |cubeBesovPairing Q (cubeProjection Q (n + 1) f) g| ≤
        (3 : ℝ≥0∞) ^ ((d : ℝ) + P.s) * X := by
    intro n
    have hgFluct : ∀ j < n + 1, ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp (cubeFluctuation R g) (ENNReal.ofReal p')
          (Homogenization.normalizedCubeMeasure R) := by
      intro j _hj R hR
      exact cubeFluctuation_memLp_of_parent_memLp Q p' hg j R hR
    have hfProjection : ∀ j < n + 1, ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp (cubeProjection Q (j + 1) f)
          (cubeBesovConjExponent (ENNReal.ofReal p'))
          (Homogenization.normalizedCubeMeasure R) := by
      intro j _hj R hR
      rw [show p' = exactDualConjExponent P.p by rfl,
        cubeBesovConjExponent_exactDualConjExponent_eq_ofReal P.p P.p_one_lt]
      exact cubeProjection_memLp_of_parent_descendant Q P.p f (j + 1) j R hR
    have hpair :
        |cubeBesovPairing Q g (cubeProjection Q (n + 1) f)| ≤
          K * cubeBesovPartialNormTop Q P.s (ENNReal.ofReal p') n g *
            cubeBesovCircPartialNorm Q P.s (ENNReal.ofReal P.p) 1 (n + 1) f := by
      simpa [K, p',
        cubeBesovConjExponent_exactDualConjExponent_eq_ofReal P.p P.p_one_lt] using
        abs_cubeBesovPairing_projection_le_max_mul_cubeBesovPartialNormTop_cubeBesovCircPartialNormOne
          (Q := Q) (s := P.s) (p := ENNReal.ofReal p') (f := g) (g := f) (N := n)
          htargetInt hp'_ofReal_one hp'_ofReal_top hp'_conj_top hgFluct hfProjection
    have hoverlap :
        ENNReal.ofReal
          (cubeBesovOverlapPartialNormTop Q P.s (ENNReal.ofReal p') n g) ≤ 1 := by
      calc
        ENNReal.ofReal
            (cubeBesovOverlapPartialNormTop Q P.s (ENNReal.ofReal p') n g) ≤
            exactOverlapTopNorm P.positiveParameters Q g
              (exactDualOverlapIntegrable Q p' hp'_one hg) := by
                simpa [p', ExactDualQOneParameters.positiveParameters] using
                  exactAggregation_overlapPartialNormTop_le_exactOverlapTopNorm
                    P.positiveParameters Q g hg n
        _ ≤ 1 := by
          simpa [p'] using hgNorm
    have hdisjoint :
        ENNReal.ofReal (cubeBesovPartialNormTop Q P.s (ENNReal.ofReal p') n g) ≤
          (3 : ℝ≥0∞) ^ ((d : ℝ) / p') := by
      have hreal := cubeBesovPartialNormTop_le_three_rpow_mul_overlapPartialNormTop
        Q P.s hp'_toReal_pos n g
      calc
        ENNReal.ofReal (cubeBesovPartialNormTop Q P.s (ENNReal.ofReal p') n g) ≤
            ENNReal.ofReal
              (C * cubeBesovOverlapPartialNormTop Q P.s (ENNReal.ofReal p') n g) :=
          ENNReal.ofReal_le_ofReal (by
            simpa [C, ENNReal.toReal_ofReal hp'_pos.le] using hreal)
        _ = ENNReal.ofReal C * ENNReal.ofReal
              (cubeBesovOverlapPartialNormTop Q P.s (ENNReal.ofReal p') n g) := by
          rw [ENNReal.ofReal_mul hC_nonneg]
        _ ≤ ENNReal.ofReal C * 1 := mul_le_mul_right hoverlap _
        _ = (3 : ℝ≥0∞) ^ ((d : ℝ) / p') := by
          rw [hC_ofReal, mul_one]
    have hcirc :
        ENNReal.ofReal
          (cubeBesovCircPartialNorm Q P.s (ENNReal.ofReal P.p) 1 (n + 1) f) ≤ X := by
      simpa [X, ExactDualQOneParameters.circParameters] using
        exactAggregation_circPartialNorm_le_exactCircFiniteSeminorm
          P.circParameters Q f hf (n + 1)
    have hpair' :
        |cubeBesovPairing Q (cubeProjection Q (n + 1) f) g| ≤
          K * cubeBesovPartialNormTop Q P.s (ENNReal.ofReal p') n g *
            cubeBesovCircPartialNorm Q P.s (ENNReal.ofReal P.p) 1 (n + 1) f := by
      simpa [cubeBesovPairing_comm] using hpair
    have hA_nonneg :
        0 ≤ cubeBesovPartialNormTop Q P.s (ENNReal.ofReal p') n g :=
      cubeBesovPartialNormTop_nonneg Q P.s (ENNReal.ofReal p') n g
    have hB_nonneg :
        0 ≤ cubeBesovCircPartialNorm Q P.s (ENNReal.ofReal P.p) 1 (n + 1) f :=
      cubeBesovCircPartialNorm_nonneg Q P.s (ENNReal.ofReal P.p) 1 (n + 1) f
    calc
      ENNReal.ofReal |cubeBesovPairing Q (cubeProjection Q (n + 1) f) g| ≤
          ENNReal.ofReal
            (K * cubeBesovPartialNormTop Q P.s (ENNReal.ofReal p') n g *
              cubeBesovCircPartialNorm Q P.s (ENNReal.ofReal P.p) 1 (n + 1) f) :=
        ENNReal.ofReal_le_ofReal hpair'
      _ = (ENNReal.ofReal K *
            ENNReal.ofReal (cubeBesovPartialNormTop Q P.s (ENNReal.ofReal p') n g)) *
          ENNReal.ofReal
            (cubeBesovCircPartialNorm Q P.s (ENNReal.ofReal P.p) 1 (n + 1) f) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hK_nonneg hA_nonneg),
          ENNReal.ofReal_mul hK_nonneg]
      _ ≤ (max 1 ((3 : ℝ≥0∞) ^ P.s) *
            (3 : ℝ≥0∞) ^ ((d : ℝ) / p')) * X := by
        rw [hK_ofReal]
        exact mul_le_mul (mul_le_mul le_rfl hdisjoint bot_le bot_le) hcirc bot_le bot_le
      _ ≤ (3 : ℝ≥0∞) ^ ((d : ℝ) + P.s) * X := by
        exact mul_le_mul_left
          (exactCircLossCoefficientENNReal_rpow_le_source d P.s p'
            P.s_pos.le hp'_one) X
  have hlimit : ENNReal.ofReal |cubeBesovPairing Q f g| ≤
      (3 : ℝ≥0∞) ^ ((d : ℝ) + P.s) * X :=
    le_of_tendsto hconvENNReal (Filter.Eventually.of_forall hbound)
  simpa [exactDualPairingFromHolder_eq, X, cubeBesovPairing,
    cubeAverage_eq_integral_normalizedCubeMeasure] using hlimit

/-- At the negative `q = 1` endpoint, the exact hatted dual seminorm is
controlled by the exact finite-`q` circ seminorm with the manuscript loss.
The only analytic premise is the canonical parent `MemLp` certificate. -/
theorem exactDualQOneHattedSeminorm_le_exactCircFiniteSeminorm
    {d : ℕ} (P : ExactDualQOneParameters) (Q : TriadicCube d)
    (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) :
    exactDualQOneHattedSeminorm P Q f hf ≤
      (3 : ℝ≥0∞) ^ ((d : ℝ) + P.s) *
        exactCircFiniteSeminorm P.circParameters Q f
          (exactCircIntegrable_of_memLp Q P.p P.p_one_lt.le hf) := by
  rw [exactDualQOneHattedSeminorm_eq]
  refine iSup_le fun T ↦ ?_
  have hNorm : exactOverlapTopNorm P.positiveParameters Q T.g
      (exactDualOverlapIntegrable Q (exactDualConjExponent P.p)
        (exactDualConjExponent_one_le P.p P.p_one_lt) T.parentMemLp) ≤ 1 := by
    rw [exactOverlapTopNorm_eq_seminorm_of_root_mean_eq_zero
      P.positiveParameters Q T.g _ T.root_mean_zero]
    exact T.seminorm_le_one
  exact exactDualQOnePairing_le_exactCircFiniteSeminorm
    P Q f T.g hf T.parentMemLp hNorm

/-- At the negative `q = 1` endpoint, the exact full dual norm satisfies the
manuscript comparison, including its explicit depth-zero root term. -/
theorem exactDualQOneFullNorm_le_exactCircFiniteSeminorm_add_root
    {d : ℕ} (P : ExactDualQOneParameters) (Q : TriadicCube d)
    (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) :
    exactDualQOneFullNorm P Q f hf ≤
      (3 : ℝ≥0∞) ^ ((d : ℝ) + P.s) *
          exactCircFiniteSeminorm P.circParameters Q f
            (exactCircIntegrable_of_memLp Q P.p P.p_one_lt.le hf) +
        exactCircDepthWeight Q P.s 0 * ENNReal.ofReal |cubeAverage Q f| := by
  have hstrong : exactDualQOneFullNorm P Q f hf ≤
      (3 : ℝ≥0∞) ^ ((d : ℝ) + P.s) *
        exactCircFiniteSeminorm P.circParameters Q f
          (exactCircIntegrable_of_memLp Q P.p P.p_one_lt.le hf) := by
    rw [exactDualQOneFullNorm_eq]
    refine iSup_le fun T ↦ ?_
    exact exactDualQOnePairing_le_exactCircFiniteSeminorm
      P Q f T.g hf T.parentMemLp T.norm_le_one
  exact hstrong.trans (le_add_right le_rfl)

end Homogenization
