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
# Exact finite-interior dual-to-circ comparison

This module proves the Chapter 1 comparison for `1 < q < ∞` directly on the
exact extended-valued kernels.  All local integrability, finite truncation, and
projection-limit inputs are derived from the two parent `MemLp` certificates.
-/

@[expose] public section

namespace Homogenization

open scoped ENNReal Topology

private theorem exactDualFinitePairing_le_exactCircFiniteSeminorm
    {d : ℕ} (P : ExactDualFiniteParameters) (Q : TriadicCube d)
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
        exactCircFiniteSeminorm P.circParameters Q f
          (exactCircIntegrable_of_memLp Q P.p P.p_one_lt.le hf) := by
  let p' : ℝ := exactDualConjExponent P.p
  let q' : ℝ := exactDualConjExponent P.q
  let C : ℝ≥0∞ := exactCircFiniteSeminorm P.circParameters Q f
    (exactCircIntegrable_of_memLp Q P.p P.p_one_lt.le hf)
  have hp'_one_le : 1 ≤ p' := exactDualConjExponent_one_le P.p P.p_one_lt
  have hq'_one_le : 1 ≤ q' := exactDualConjExponent_one_le P.q P.q_one_lt
  have hp'_pos : 0 < p' := lt_of_lt_of_le zero_lt_one hp'_one_le
  have hq'_pos : 0 < q' := lt_of_lt_of_le zero_lt_one hq'_one_le
  have hp'_ofReal_one_le : 1 ≤ ENNReal.ofReal p' := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp'_one_le
  have hq'_ofReal_one_le : 1 ≤ ENNReal.ofReal q' := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq'_one_le
  have hp'_toReal_pos : 0 < (ENNReal.ofReal p').toReal := by
    rw [ENNReal.toReal_ofReal hp'_pos.le]
    exact hp'_pos
  have hq'_toReal_one_le : 1 ≤ (ENNReal.ofReal q').toReal := by
    rw [ENNReal.toReal_ofReal hq'_pos.le]
    exact hq'_one_le
  have hfInt : MeasureTheory.IntegrableOn f (cubeSet Q) MeasureTheory.volume :=
    integrableOn_of_integrable_normalizedCubeMeasure (Q := Q)
      (hf.integrable (ENNReal.one_le_ofReal.mpr P.p_one_lt.le))
  have hgLimit : MeasureTheory.MemLp g
      (cubeBesovConjExponent (ENNReal.ofReal P.p))
      (Homogenization.normalizedCubeMeasure Q) := by
    simpa [cubeBesovConjExponent_ofReal_eq_exactDualConjExponent P.p P.p_one_lt]
      using hg
  have hconv := tendsto_cubeBesovPairing_projection_left_of_memLp
    Q (ENNReal.ofReal P.p) f g hf hgLimit
      (by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal P.p_one_lt.le)
      ENNReal.ofReal_ne_top
      (by
        rw [cubeBesovConjExponent_ofReal_eq_exactDualConjExponent P.p P.p_one_lt]
        exact ENNReal.ofReal_ne_top)
  have hconvAbs : Filter.Tendsto
      (fun n => |cubeBesovPairing Q (cubeProjection Q (n + 1) f) g|)
      Filter.atTop (nhds |cubeBesovPairing Q f g|) := by
    simpa [Real.norm_eq_abs] using hconv.norm
  have hconvENN : Filter.Tendsto
      (fun n => ENNReal.ofReal
        |cubeBesovPairing Q (cubeProjection Q (n + 1) f) g|)
      Filter.atTop (nhds (ENNReal.ofReal |cubeBesovPairing Q f g|)) :=
    ENNReal.tendsto_ofReal hconvAbs
  have hbound : ∀ n : ℕ,
      ENNReal.ofReal |cubeBesovPairing Q (cubeProjection Q (n + 1) f) g| ≤
        (3 : ℝ≥0∞) ^ ((d : ℝ) + P.s) * C := by
    intro n
    have hgFluct : ∀ j < n + 1, ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp (cubeFluctuation R g) (ENNReal.ofReal p')
          (normalizedCubeMeasure R) := by
      intro j _hj R hR
      exact cubeFluctuation_memLp_of_parent_memLp Q p' hg j R hR
    have hfProj : ∀ j < n + 1, ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp (cubeProjection Q (j + 1) f)
          (cubeBesovConjExponent (ENNReal.ofReal p'))
          (normalizedCubeMeasure R) := by
      intro j _hj R hR
      rw [cubeBesovConjExponent_exactDualConjExponent_eq_ofReal P.p P.p_one_lt]
      exact cubeProjection_memLp_of_parent_descendant Q P.p f (j + 1) j R hR
    have hpair :
        |cubeBesovPairing Q g (cubeProjection Q (n + 1) f)| ≤
          max 1 ((3 : ℝ) ^ P.s) *
            cubeBesovPartialNorm Q P.s (ENNReal.ofReal p') (ENNReal.ofReal q') n g *
            cubeBesovCircPartialNorm Q P.s
              (cubeBesovConjExponent (ENNReal.ofReal p'))
              (cubeBesovConjExponent (ENNReal.ofReal q')) (n + 1) f := by
      exact
        abs_cubeBesovPairing_projection_le_max_mul_cubeBesovPartialNorm_cubeBesovCircPartialNorm
          Q P.s (ENNReal.ofReal p') (ENNReal.ofReal q') g f n hfInt
          hp'_ofReal_one_le ENNReal.ofReal_ne_top
          (by
            rw [cubeBesovConjExponent_exactDualConjExponent_eq_ofReal P.p P.p_one_lt]
            exact ENNReal.ofReal_ne_top)
          hq'_ofReal_one_le ENNReal.ofReal_ne_top
          (by
            rw [cubeBesovConjExponent_exactDualConjExponent_eq_ofReal P.q P.q_one_lt]
            exact ENNReal.ofReal_ne_top)
          hgFluct hfProj
    have hpos :
        cubeBesovPartialNorm Q P.s (ENNReal.ofReal p') (ENNReal.ofReal q') n g ≤
          (3 : ℝ) ^ ((d : ℝ) / p') *
            cubeBesovOverlapPartialNorm Q P.s (ENNReal.ofReal p')
              (ENNReal.ofReal q') n g := by
      convert cubeBesovPartialNorm_le_three_rpow_mul_overlapPartialNorm
        Q P.s hp'_toReal_pos hq'_toReal_one_le n g using 1
      rw [ENNReal.toReal_ofReal hp'_pos.le]
    have hover : ENNReal.ofReal
        (cubeBesovOverlapPartialNorm Q P.s (ENNReal.ofReal p')
          (ENNReal.ofReal q') n g) ≤ 1 := by
      calc
        ENNReal.ofReal
            (cubeBesovOverlapPartialNorm Q P.s (ENNReal.ofReal p')
              (ENNReal.ofReal q') n g) ≤
            exactOverlapFiniteNorm P.positiveParameters Q g
              (exactDualOverlapIntegrable Q p' hp'_one_le hg) := by
          simpa [p', q', ExactDualFiniteParameters.positiveParameters] using
            exactAggregation_overlapPartialNorm_le_exactOverlapFiniteNorm
              P.positiveParameters Q g hg n
        _ ≤ 1 := by simpa [p'] using hgNorm
    have hcirc : ENNReal.ofReal
        (cubeBesovCircPartialNorm Q P.s (ENNReal.ofReal P.p)
          (ENNReal.ofReal P.q) (n + 1) f) ≤ C := by
      simpa [C, ExactDualFiniteParameters.circParameters] using
        exactAggregation_circPartialNorm_le_exactCircFiniteSeminorm
          P.circParameters Q f hf (n + 1)
    have hposNonneg : 0 ≤
        cubeBesovPartialNorm Q P.s (ENNReal.ofReal p') (ENNReal.ofReal q') n g :=
      cubeBesovPartialNorm_nonneg Q P.s (ENNReal.ofReal p') (ENNReal.ofReal q') n g
    have hdepthExponentNonneg : 0 ≤ (d : ℝ) / p' :=
      div_nonneg (Nat.cast_nonneg d) hp'_pos.le
    have hposENN : ENNReal.ofReal
        (cubeBesovPartialNorm Q P.s (ENNReal.ofReal p') (ENNReal.ofReal q') n g) ≤
          (3 : ℝ≥0∞) ^ ((d : ℝ) / p') := by
      calc
        ENNReal.ofReal
            (cubeBesovPartialNorm Q P.s (ENNReal.ofReal p') (ENNReal.ofReal q') n g) ≤
            ENNReal.ofReal ((3 : ℝ) ^ ((d : ℝ) / p') *
              cubeBesovOverlapPartialNorm Q P.s (ENNReal.ofReal p')
                (ENNReal.ofReal q') n g) := ENNReal.ofReal_le_ofReal hpos
        _ = (3 : ℝ≥0∞) ^ ((d : ℝ) / p') *
              ENNReal.ofReal (cubeBesovOverlapPartialNorm Q P.s
                (ENNReal.ofReal p') (ENNReal.ofReal q') n g) := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
            ← ENNReal.ofReal_rpow_of_nonneg (by norm_num : 0 ≤ (3 : ℝ))
              hdepthExponentNonneg]
          norm_num
        _ ≤ (3 : ℝ≥0∞) ^ ((d : ℝ) / p') * 1 :=
          by gcongr
        _ = (3 : ℝ≥0∞) ^ ((d : ℝ) / p') := mul_one _
    have hKNonneg : 0 ≤ max 1 ((3 : ℝ) ^ P.s) :=
      le_trans (by norm_num) (le_max_left _ _)
    have hpairENN :
        ENNReal.ofReal |cubeBesovPairing Q (cubeProjection Q (n + 1) f) g| ≤
          max 1 ((3 : ℝ≥0∞) ^ P.s) *
            (3 : ℝ≥0∞) ^ ((d : ℝ) / p') * C := by
      calc
        ENNReal.ofReal |cubeBesovPairing Q (cubeProjection Q (n + 1) f) g| =
            ENNReal.ofReal |cubeBesovPairing Q g (cubeProjection Q (n + 1) f)| := by
          congr 2
          simp [cubeBesovPairing, mul_comm]
        _ ≤ ENNReal.ofReal
            (max 1 ((3 : ℝ) ^ P.s) *
              cubeBesovPartialNorm Q P.s (ENNReal.ofReal p') (ENNReal.ofReal q') n g *
              cubeBesovCircPartialNorm Q P.s
                (cubeBesovConjExponent (ENNReal.ofReal p'))
                (cubeBesovConjExponent (ENNReal.ofReal q')) (n + 1) f) :=
          ENNReal.ofReal_le_ofReal hpair
        _ = ENNReal.ofReal (max 1 ((3 : ℝ) ^ P.s)) *
              ENNReal.ofReal
                (cubeBesovPartialNorm Q P.s (ENNReal.ofReal p')
                  (ENNReal.ofReal q') n g) *
              ENNReal.ofReal
                (cubeBesovCircPartialNorm Q P.s (ENNReal.ofReal P.p)
                  (ENNReal.ofReal P.q) (n + 1) f) := by
          rw [cubeBesovConjExponent_exactDualConjExponent_eq_ofReal P.p P.p_one_lt,
            cubeBesovConjExponent_exactDualConjExponent_eq_ofReal P.q P.q_one_lt,
            ENNReal.ofReal_mul (mul_nonneg hKNonneg hposNonneg),
            ENNReal.ofReal_mul hKNonneg]
        _ ≤ ENNReal.ofReal (max 1 ((3 : ℝ) ^ P.s)) *
              (3 : ℝ≥0∞) ^ ((d : ℝ) / p') * C := by
          gcongr
        _ = max 1 ((3 : ℝ≥0∞) ^ P.s) *
              (3 : ℝ≥0∞) ^ ((d : ℝ) / p') * C := by
          rw [ENNReal.ofReal_max,
            ← ENNReal.ofReal_rpow_of_nonneg (by norm_num : 0 ≤ (3 : ℝ)) P.s_pos.le]
          norm_num
    calc
      ENNReal.ofReal |cubeBesovPairing Q (cubeProjection Q (n + 1) f) g| ≤
          max 1 ((3 : ℝ≥0∞) ^ P.s) *
            (3 : ℝ≥0∞) ^ ((d : ℝ) / p') * C := hpairENN
      _ ≤ (3 : ℝ≥0∞) ^ ((d : ℝ) + P.s) * C :=
        by
          gcongr
          exact exactCircLossCoefficientENNReal_rpow_le_source
            d P.s p' P.s_pos.le hp'_one_le
  have hlimit : ENNReal.ofReal |cubeBesovPairing Q f g| ≤
      (3 : ℝ≥0∞) ^ ((d : ℝ) + P.s) * C :=
    le_of_tendsto hconvENN (Filter.Eventually.of_forall hbound)
  rw [exactDualPairingFromHolder_eq]
  simpa [C, cubeBesovPairing, cubeAverage_eq_integral_normalizedCubeMeasure] using hlimit

/-- Exact finite-interior hatted dual seminorm is controlled by the exact
concrete circ seminorm with the manuscript coefficient. -/
theorem exactDualFiniteHattedSeminorm_le_exactCircFiniteSeminorm
    {d : ℕ} (P : ExactDualFiniteParameters) (Q : TriadicCube d)
    (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) :
    exactDualFiniteHattedSeminorm P Q f hf ≤
      (3 : ℝ≥0∞) ^ ((d : ℝ) + P.s) *
        exactCircFiniteSeminorm P.circParameters Q f
          (exactCircIntegrable_of_memLp Q P.p P.p_one_lt.le hf) := by
  rw [exactDualFiniteHattedSeminorm_eq]
  refine iSup_le ?_
  intro T
  apply exactDualFinitePairing_le_exactCircFiniteSeminorm P Q f T.g hf T.parentMemLp
  rw [exactOverlapFiniteNorm_eq, T.root_mean_zero]
  simpa using T.seminorm_le_one

/-- Exact finite-interior full dual norm is controlled by the exact concrete
circ seminorm, with the literal manuscript root term retained on the right. -/
theorem exactDualFiniteFullNorm_le_exactCircFiniteSeminorm_add_root
    {d : ℕ} (P : ExactDualFiniteParameters) (Q : TriadicCube d)
    (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) :
    exactDualFiniteFullNorm P Q f hf ≤
      (3 : ℝ≥0∞) ^ ((d : ℝ) + P.s) *
          exactCircFiniteSeminorm P.circParameters Q f
            (exactCircIntegrable_of_memLp Q P.p P.p_one_lt.le hf) +
        exactCircDepthWeight Q P.s 0 * ENNReal.ofReal |cubeAverage Q f| := by
  rw [exactDualFiniteFullNorm_eq]
  refine iSup_le ?_
  intro T
  exact (exactDualFinitePairing_le_exactCircFiniteSeminorm
    P Q f T.g hf T.parentMemLp T.norm_le_one).trans (le_add_right le_rfl)

end Homogenization
