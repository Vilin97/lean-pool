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
# Exact circ domination at the negative `q = ∞` endpoint

This file proves the source-facing comparison between the exact dual-negative
endpoint and the exact concrete circ endpoint.  All finite projected-pairing
premises are derived internally from the parent `MemLp` certificates carried
by the exact definitions.
-/

@[expose] public section

namespace Homogenization

open scoped ENNReal Topology

private theorem exactDualTopPairing_le_exactCircTopSeminorm
    {d : ℕ} (P : ExactDualTopParameters) (Q : TriadicCube d)
    (f g : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g
      (ENNReal.ofReal (exactDualConjExponent P.p))
      (Homogenization.normalizedCubeMeasure Q))
    (hgNorm : exactOverlapFiniteNorm P.positiveParameters Q g
      (exactDualOverlapIntegrable Q (exactDualConjExponent P.p)
        (exactDualConjExponent_one_le P.p P.p_one_lt) hg) ≤ 1) :
    exactDualPairingFromHolder Q P.p f g P.p_one_lt hf hg ≤
      (3 : ℝ≥0∞) ^ ((d : ℝ) + P.s) *
        exactCircTopSeminorm P.circParameters Q f
          (exactCircIntegrable_of_memLp Q P.p P.p_one_lt.le hf) := by
  let p' : ℝ := exactDualConjExponent P.p
  let K : ℝ := max 1 ((3 : ℝ) ^ P.s)
  let C : ℝ := (3 : ℝ) ^ ((d : ℝ) / p')
  let B : ℝ≥0∞ :=
    (3 : ℝ≥0∞) ^ ((d : ℝ) + P.s) *
      exactCircTopSeminorm P.circParameters Q f
        (exactCircIntegrable_of_memLp Q P.p P.p_one_lt.le hf)
  have hp'_one_le : 1 ≤ p' := by
    exact exactDualConjExponent_one_le P.p P.p_one_lt
  have hp'_pos : 0 < p' := lt_of_lt_of_le zero_lt_one hp'_one_le
  have hp'_toReal : (ENNReal.ofReal p').toReal = p' := by
    exact ENNReal.toReal_ofReal (le_of_lt hp'_pos)
  have hfInt : MeasureTheory.IntegrableOn f (cubeSet Q) MeasureTheory.volume := by
    exact integrableOn_of_integrable_normalizedCubeMeasure (Q := Q)
      (hf.integrable (ENNReal.one_le_ofReal.mpr P.p_one_lt.le))
  have hpTarget : 1 ≤ ENNReal.ofReal P.p :=
    ENNReal.one_le_ofReal.mpr P.p_one_lt.le
  have hpTargetConjTop : cubeBesovConjExponent (ENNReal.ofReal P.p) ≠ ∞ :=
    cubeBesovConjExponent_ofReal_ne_top P.p P.p_one_lt
  have hpTest : 1 ≤ ENNReal.ofReal p' :=
    ENNReal.one_le_ofReal.mpr hp'_one_le
  have hpTestDouble : cubeBesovConjExponent (ENNReal.ofReal p') =
      ENNReal.ofReal P.p := by
    simpa only [p'] using
      cubeBesovConjExponent_exactDualConjExponent_eq_ofReal P.p P.p_one_lt
  have hpTestDoubleTop : cubeBesovConjExponent (ENNReal.ofReal p') ≠ ∞ := by
    rw [hpTestDouble]
    exact ENNReal.ofReal_ne_top
  have hgAsConjugate : MeasureTheory.MemLp g
      (cubeBesovConjExponent (ENNReal.ofReal P.p))
      (Homogenization.normalizedCubeMeasure Q) := by
    simpa only [cubeBesovConjExponent_ofReal_eq_exactDualConjExponent
      P.p P.p_one_lt, p'] using hg
  have hconv :=
    tendsto_cubeBesovPairing_projection_left_of_memLp
      Q (ENNReal.ofReal P.p) f g hf hgAsConjugate hpTarget ENNReal.ofReal_ne_top
        hpTargetConjTop
  have hconvAbs :
      Filter.Tendsto
        (fun n => |cubeBesovPairing Q (cubeProjection Q (n + 1) f) g|)
        Filter.atTop (nhds |cubeBesovPairing Q f g|) := by
    simpa only [Real.norm_eq_abs] using hconv.norm
  have hconvENN :
      Filter.Tendsto
        (fun n => ENNReal.ofReal
          |cubeBesovPairing Q (cubeProjection Q (n + 1) f) g|)
        Filter.atTop (nhds (ENNReal.ofReal |cubeBesovPairing Q f g|)) :=
    ENNReal.tendsto_ofReal hconvAbs
  have hbound : ∀ n : ℕ,
      ENNReal.ofReal |cubeBesovPairing Q (cubeProjection Q (n + 1) f) g| ≤ B := by
    intro n
    have hlocalG : ∀ j < n + 1, ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp (cubeFluctuation R g) (ENNReal.ofReal p')
          (normalizedCubeMeasure R) := by
      intro j _hj R hR
      exact cubeFluctuation_memLp_of_parent_memLp Q p' hg j R hR
    have hlocalF : ∀ j < n + 1, ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp (cubeProjection Q (j + 1) f)
          (cubeBesovConjExponent (ENNReal.ofReal p'))
          (normalizedCubeMeasure R) := by
      intro j _hj R hR
      rw [hpTestDouble]
      exact cubeProjection_memLp_of_parent_descendant Q P.p f (j + 1) j R hR
    have hpair :=
      abs_cubeBesovPairing_projection_le_max_mul_cubeBesovPartialNormOne_cubeBesovCircPartialNormTop
        (Q := Q) (s := P.s) (p := ENNReal.ofReal p') (f := g) (g := f) (N := n)
        hfInt hpTest ENNReal.ofReal_ne_top hpTestDoubleTop hlocalG hlocalF
    have hoverlapENN :
        ENNReal.ofReal
            (cubeBesovOverlapPartialNorm Q P.s (ENNReal.ofReal p') 1 n g) ≤
          exactOverlapFiniteNorm P.positiveParameters Q g
            (exactDualOverlapIntegrable Q (exactDualConjExponent P.p)
              (exactDualConjExponent_one_le P.p P.p_one_lt) hg) := by
      simpa only [ExactDualTopParameters.positiveParameters, p', ENNReal.ofReal_one] using
        exactAggregation_overlapPartialNorm_le_exactOverlapFiniteNorm
          P.positiveParameters Q g hg n
    have hoverlapLeOne :
        cubeBesovOverlapPartialNorm Q P.s (ENNReal.ofReal p') 1 n g ≤ 1 := by
      rw [← ENNReal.ofReal_le_one]
      exact hoverlapENN.trans hgNorm
    have hdisjoint :
        cubeBesovPartialNorm Q P.s (ENNReal.ofReal p') 1 n g ≤ C := by
      calc
        cubeBesovPartialNorm Q P.s (ENNReal.ofReal p') 1 n g ≤
            C * cubeBesovOverlapPartialNorm Q P.s (ENNReal.ofReal p') 1 n g := by
          simpa only [C, hp'_toReal] using
            cubeBesovPartialNorm_le_three_rpow_mul_overlapPartialNorm
              (p := ENNReal.ofReal p') (q := (1 : ℝ≥0∞)) Q P.s
                (by rw [hp'_toReal]; exact hp'_pos) (by norm_num) n g
        _ ≤ C * 1 := by
          exact mul_le_mul_of_nonneg_left hoverlapLeOne
            (Real.rpow_nonneg (by norm_num) _)
        _ = C := mul_one C
    have hK_nonneg : 0 ≤ K := by
      exact le_trans zero_le_one (le_max_left 1 ((3 : ℝ) ^ P.s))
    have hC_nonneg : 0 ≤ C := Real.rpow_nonneg (by norm_num) _
    have hlegacyCircNonneg :
        0 ≤ cubeBesovCircPartialNormTop Q P.s (ENNReal.ofReal P.p) (n + 1) f :=
      cubeBesovCircPartialNormTop_nonneg Q P.s (ENNReal.ofReal P.p) (n + 1) f
    have hpairReal :
        |cubeBesovPairing Q (cubeProjection Q (n + 1) f) g| ≤
          (K * C) * cubeBesovCircPartialNormTop Q P.s
            (ENNReal.ofReal P.p) (n + 1) f := by
      calc
        |cubeBesovPairing Q (cubeProjection Q (n + 1) f) g| =
            |cubeBesovPairing Q g (cubeProjection Q (n + 1) f)| := by
          simp only [cubeBesovPairing, mul_comm]
        _ ≤ K * cubeBesovPartialNorm Q P.s (ENNReal.ofReal p') 1 n g *
            cubeBesovCircPartialNormTop Q P.s
              (cubeBesovConjExponent (ENNReal.ofReal p')) (n + 1) f := by
          simpa only [K] using hpair
        _ = K * cubeBesovPartialNorm Q P.s (ENNReal.ofReal p') 1 n g *
            cubeBesovCircPartialNormTop Q P.s (ENNReal.ofReal P.p) (n + 1) f := by
          rw [hpTestDouble]
        _ ≤ (K * C) * cubeBesovCircPartialNormTop Q P.s
            (ENNReal.ofReal P.p) (n + 1) f := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hdisjoint hK_nonneg) hlegacyCircNonneg
    have hcircENN :
        ENNReal.ofReal
            (cubeBesovCircPartialNormTop Q P.s (ENNReal.ofReal P.p) (n + 1) f) ≤
          exactCircTopSeminorm P.circParameters Q f
            (exactCircIntegrable_of_memLp Q P.p P.p_one_lt.le hf) := by
      simpa only [ExactDualTopParameters.circParameters] using
        exactAggregation_circPartialNormTop_le_exactCircTopSeminorm
          P.circParameters Q f hf (n + 1)
    have hcoeff : ENNReal.ofReal (K * C) ≤
        ENNReal.ofReal ((3 : ℝ) ^ ((d : ℝ) + P.s)) := by
      simpa only [K, C, p'] using
        exactCircLossCoefficientENNReal_le_source d P.s
          (exactDualConjExponent P.p) P.s_pos.le hp'_one_le
    have hsource : ENNReal.ofReal ((3 : ℝ) ^ ((d : ℝ) + P.s)) =
        (3 : ℝ≥0∞) ^ ((d : ℝ) + P.s) := by
      rw [← ENNReal.ofReal_rpow_of_nonneg]
      · norm_num
      · norm_num
      · exact add_nonneg (Nat.cast_nonneg d) P.s_pos.le
    calc
      ENNReal.ofReal |cubeBesovPairing Q (cubeProjection Q (n + 1) f) g| ≤
          ENNReal.ofReal
            ((K * C) * cubeBesovCircPartialNormTop Q P.s
              (ENNReal.ofReal P.p) (n + 1) f) :=
        ENNReal.ofReal_le_ofReal hpairReal
      _ = ENNReal.ofReal (K * C) *
          ENNReal.ofReal
            (cubeBesovCircPartialNormTop Q P.s (ENNReal.ofReal P.p) (n + 1) f) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hK_nonneg hC_nonneg)]
      _ ≤ ENNReal.ofReal (K * C) *
          exactCircTopSeminorm P.circParameters Q f
            (exactCircIntegrable_of_memLp Q P.p P.p_one_lt.le hf) :=
        mul_le_mul_right hcircENN _
      _ ≤ ENNReal.ofReal ((3 : ℝ) ^ ((d : ℝ) + P.s)) *
          exactCircTopSeminorm P.circParameters Q f
            (exactCircIntegrable_of_memLp Q P.p P.p_one_lt.le hf) :=
        mul_le_mul_left hcoeff _
      _ = B := by rw [hsource]
  have hlimit : ENNReal.ofReal |cubeBesovPairing Q f g| ≤ B :=
    le_of_tendsto hconvENN (Filter.Eventually.of_forall hbound)
  calc
    exactDualPairingFromHolder Q P.p f g P.p_one_lt hf hg =
        ENNReal.ofReal |cubeBesovPairing Q f g| := by
      change exactDualNormalizedPairing Q f g _ = _
      exact exactDualNormalizedPairing_eq_of_cubeBesovPairing Q f g _
    _ ≤ B := hlimit

/-- The exact hatted negative `q = ∞` seminorm is bounded by the exact
concrete circ endpoint with the Chapter 1 coefficient. -/
theorem exactDualTopHattedSeminorm_le_exactCircTopSeminorm
    {d : ℕ} (P : ExactDualTopParameters) (Q : TriadicCube d)
    (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) :
    exactDualTopHattedSeminorm P Q f hf ≤
      (3 : ℝ≥0∞) ^ ((d : ℝ) + P.s) *
        exactCircTopSeminorm P.circParameters Q f
          (exactCircIntegrable_of_memLp Q P.p P.p_one_lt.le hf) := by
  rw [exactDualTopHattedSeminorm_eq]
  refine iSup_le fun T => ?_
  have hnorm : exactOverlapFiniteNorm P.positiveParameters Q T.g
      (exactDualOverlapIntegrable Q (exactDualConjExponent P.p)
        (exactDualConjExponent_one_le P.p P.p_one_lt) T.parentMemLp) ≤ 1 := by
    rw [exactOverlapFiniteNorm_eq, T.root_mean_zero]
    simpa only [abs_zero, ENNReal.ofReal_zero, mul_zero, add_zero] using T.seminorm_le_one
  exact exactDualTopPairing_le_exactCircTopSeminorm
    P Q f T.g hf T.parentMemLp hnorm

/-- The exact full negative `q = ∞` norm obeys the manuscript comparison.
The depth-zero circ term already controls the root contribution; the explicit
nonnegative source root term is retained in the stated right-hand side. -/
theorem exactDualTopFullNorm_le_exactCircTopSeminorm_add_root
    {d : ℕ} (P : ExactDualTopParameters) (Q : TriadicCube d)
    (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) :
    exactDualTopFullNorm P Q f hf ≤
      (3 : ℝ≥0∞) ^ ((d : ℝ) + P.s) *
          exactCircTopSeminorm P.circParameters Q f
            (exactCircIntegrable_of_memLp Q P.p P.p_one_lt.le hf) +
        exactCircDepthWeight Q P.s 0 * ENNReal.ofReal |cubeAverage Q f| := by
  rw [exactDualTopFullNorm_eq]
  calc
    (⨆ T : ExactDualTopFullTest P Q, T.pairing hf) ≤
        (3 : ℝ≥0∞) ^ ((d : ℝ) + P.s) *
          exactCircTopSeminorm P.circParameters Q f
            (exactCircIntegrable_of_memLp Q P.p P.p_one_lt.le hf) := by
      refine iSup_le fun T => ?_
      exact exactDualTopPairing_le_exactCircTopSeminorm
        P Q f T.g hf T.parentMemLp T.norm_le_one
    _ ≤ (3 : ℝ≥0∞) ^ ((d : ℝ) + P.s) *
          exactCircTopSeminorm P.circParameters Q f
            (exactCircIntegrable_of_memLp Q P.p P.p_one_lt.le hf) +
        exactCircDepthWeight Q P.s 0 * ENNReal.ofReal |cubeAverage Q f| :=
      le_add_of_nonneg_right bot_le

end Homogenization
