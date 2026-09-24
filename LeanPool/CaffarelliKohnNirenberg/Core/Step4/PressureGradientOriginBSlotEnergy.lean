/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginBSlotEnergyTime

/-! # The whole-carrier pressure-gradient time mass of `prop:bootstrap`

The B slot of `prop:bootstrap` asks for the actual clipped `L^{6/5}` time mass
of the selected weak pressure gradient on the origin carrier `B_{R₁}`, measured
against the numerical coefficient

`(|C_CZ| + 1) * (|R₀| + |R₁| + |ε| + 1) * max 1 ((2R₁/(1-R₁)) ^ θ)`,

where `θ = 5 (1 - (6/5) / min ((1/τ + 8/25)⁻¹) q)`.  That coefficient carries
neither velocity nor gradient Morrey data, so the estimate has to come from the
`ε` data alone.

This file records the numerical fact that makes the coefficient usable: any
absolute mass below a threshold `Cstar` is paid by the coefficient once
`Cstar ≤ C_CZ`, on the whole admitted parameter range `5/2 < q`,
`25/3 ≤ τ ≤ 25`, `0 < R₁ < 3/4`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace CKN.Core.Step4

/-- Above an absolute Calderón–Zygmund threshold the B-slot coefficient of
`prop:bootstrap` pays any `ε`-linear mass whose absolute factor is below the
threshold. -/
theorem mass_le_bslot_coefficient
    {K : ℝ≥0∞} {Cstar C_CZ R₀ R₁ ε θ : ℝ} (hε : 0 ≤ ε)
    (hK : K ≤ ENNReal.ofReal Cstar) (hthr : Cstar ≤ C_CZ) :
    K * (ENNReal.ofReal ε + 1) ≤
      (ENNReal.ofReal (|C_CZ| + 1) * ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1)) *
        ENNReal.ofReal (max 1 ((2 * R₁ / (1 - R₁)) ^ θ)) := by
  have hKC : K ≤ ENNReal.ofReal (|C_CZ| + 1) := by
    refine hK.trans (ENNReal.ofReal_le_ofReal ?_)
    have h := le_abs_self C_CZ
    linarith only [hthr, h]
  have he : ENNReal.ofReal ε + 1 ≤ ENNReal.ofReal (|R₀| + |R₁| + |ε| + 1) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp,
      ← ENNReal.ofReal_add hε (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hεabs := le_abs_self ε
    have h₀ := abs_nonneg R₀
    have h₁ := abs_nonneg R₁
    linarith only [hεabs, h₀, h₁]
  have hinf : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (max 1 ((2 * R₁ / (1 - R₁)) ^ θ)) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  exact (mul_le_mul' hKC he).trans (le_mul_of_one_le_right' hinf)

end CKN.Core.Step4
