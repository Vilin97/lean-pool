/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.CubeEmbedding.GagliardoNirenbergSobolev
import LeanPool.CoarseGraining.Homogenization.Sobolev.FiniteLpExponent

/-!
# Finite-`p` Gagliardo--Nirenberg--Sobolev on `Vec d`

This is the ambient compact-support form of the finite-exponent Sobolev
inequality.  The cube localization layer can use it without committing to a
particular formula for the critical exponent.
-/

namespace Homogenization

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

private theorem finiteLpExponent_toNNReal_coe (p : FiniteLpExponent) :
    ((p.exponent.toNNReal : ℝ≥0) : ℝ≥0∞) = p.exponent := by
  rw [ENNReal.coe_toNNReal p.lt_top.ne]

/-- Ambient finite-`p` Gagliardo--Nirenberg--Sobolev inequality, with the
Sobolev relation between `p` and `q` supplied exactly in real exponents. -/
theorem gns_contDiff_compactSupport_finiteLp
    {d : ℕ} (hd : 0 < d) (p q : FiniteLpExponent)
    (hp : p.exponent.toReal < d)
    (hpq : (q.exponent.toReal)⁻¹ = p.exponent.toReal⁻¹ - (d : ℝ)⁻¹)
    {u : Vec d → ℝ} (hu : ContDiff ℝ 1 u) (hcs : HasCompactSupport u) :
    eLpNorm u q.exponent (volume : Measure (Vec d))
      ≤ SNormLESNormFDerivOfEqConst ℝ (volume : Measure (Vec d)) p.exponent.toNNReal *
        eLpNorm (fderiv ℝ u) p.exponent (volume : Measure (Vec d)) := by
  have hfr : Module.finrank ℝ (Vec d) = d := finrank_vec d
  have hp_one : (1 : ℝ≥0) ≤ p.exponent.toNNReal := by
    rw [← ENNReal.coe_le_coe, finiteLpExponent_toNNReal_coe p]
    exact p.one_lt.le
  have hp_dim : p.exponent.toReal < Module.finrank ℝ (Vec d) := by
    rw [hfr]
    exact hp
  have hp_pos : 0 < p.exponent.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans p.one_lt)) p.lt_top.ne
  have hd_real : 0 < (Module.finrank ℝ (Vec d) : ℝ) := by
    rw [hfr]
    exact_mod_cast hd
  have hdim_real : 0 < (Module.finrank ℝ (Vec d) : ℝ) := by
    linarith [hd_real, hp_pos, hp_dim]
  have hdim : 0 < Module.finrank ℝ (Vec d) := by
    exact_mod_cast hdim_real
  have hpq' : ((q.exponent.toNNReal : ℝ≥0) : ℝ)⁻¹ =
      (p.exponent.toNNReal : ℝ)⁻¹ - (Module.finrank ℝ (Vec d) : ℝ)⁻¹ := by
    rw [hfr]
    simpa only [ENNReal.coe_toNNReal_eq_toReal] using hpq
  have hgns := eLpNorm_le_eLpNorm_fderiv_of_eq
    (μ := (volume : Measure (Vec d))) hu hcs (p := p.exponent.toNNReal)
    (p' := q.exponent.toNNReal) hp_one hdim hpq'
  simpa only [finiteLpExponent_toNNReal_coe p, finiteLpExponent_toNNReal_coe q] using hgns

end

end Homogenization
