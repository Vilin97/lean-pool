/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyEnergyClassification

/-!
# The one-piece quadratic energy estimate

This is the elementary `TT*` consequence used in the direct quadratic
proof of the localized Krause--Lacey estimate. It deliberately makes no
Calderón--Zygmund, standard/nonstandard, packing, or Rademacher--Menshov
classification: a unit-window mass bound and a total local mass bound are
enough.

If a piece at physical length `R` has both bounds at size `M`, its squared
`L²` norm is `O(M/R)` times its `L¹` mass. Substituting
`M = A R 2^{-s}` gives the required `2^{-s}` gain.
-/

@[expose] public section

open Function MeasureTheory Set

namespace QuadraticCarleson
namespace KrauseLaceyBadScale


/-- A single localized positive quadratic piece has the direct energy bound
from a unit-window mass bound and a total local mass bound. -/
theorem localizedEnergy_le_of_localUnitMass_and_localMass
    (k : ℤ) (I : RealInterval) (hscale : I.length = (2 : ℝ) ^ (k + 2))
    {b : ℝ → ℂ} (hb : Integrable b) {M : ℝ} (_hM : 0 ≤ M)
    (hunit : ∀ x : ℝ, localUnitMass I b x ≤ M)
    (hmass : ∫ x in I.centralThird, ‖b x‖ ≤ M * I.length) :
    localizedEnergy k I b ≤
      (144 * positiveDyadicAmplitudeBound ^ 2 * M / I.length) *
        ∫ x in I.centralThird, ‖b x‖ := by
  let m : ℝ := ∫ x in I.centralThird, ‖b x‖
  let A : ℝ := 16 * positiveDyadicAmplitudeBound ^ 2 / I.length
  let B : ℝ := 128 * positiveDyadicAmplitudeBound ^ 2 / I.length ^ 2
  have hm : 0 ≤ m := integral_nonneg (fun _ ↦ norm_nonneg _)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity [I.length_pos]
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity [I.length_pos]
  have hwindow :
      (∫ x, ‖I.centralThird.indicator b x‖ * localUnitMass I b x) ≤ M * m := by
    calc
      _ ≤ ∫ x, M * ‖I.centralThird.indicator b x‖ := by
        apply integral_mono (integrable_mul_localUnitMass I hb)
          ((hb.indicator I.measurableSet_centralThird).norm.const_mul M)
        intro x
        exact (mul_le_mul_of_nonneg_left (hunit x) (norm_nonneg _)).trans_eq
          (mul_comm _ _)
      _ = M * m := by
        rw [integral_const_mul]
        simp only [m, norm_indicator_eq_indicator_norm,
          integral_indicator I.measurableSet_centralThird]
  have hnear : nearEnergy I b ≤ A * M * m := by
    unfold nearEnergy
    change A * (∫ x, ‖I.centralThird.indicator b x‖ * localUnitMass I b x) ≤ _
    exact (mul_le_mul_of_nonneg_left hwindow hA).trans_eq (by ring)
  have hfar : farEnergy I b ≤ B * M * I.length * m := by
    unfold farEnergy
    change B * m ^ 2 ≤ _
    calc
      B * m ^ 2 = B * (m * m) := by ring
      _ ≤ B * ((M * I.length) * m) := by
        gcongr
      _ = B * M * I.length * m := by ring
  calc
    localizedEnergy k I b ≤ nearEnergy I b + farEnergy I b :=
      localizedEnergy_le_near_add_far k I hscale hb
    _ ≤ A * M * m + B * M * I.length * m := add_le_add hnear hfar
    _ = (144 * positiveDyadicAmplitudeBound ^ 2 * M / I.length) * m := by
      dsimp [A, B]
      field_simp
      ring
    _ = _ := rfl

/-- The same estimate with the scale-gap substitution used in the direct
quadratic argument. Here the local mass constant is `A 2^(k+2-s)`, while
the output interval has length `2^(k+2)`. -/
theorem localizedEnergy_le_of_gap_localMass
    (k s : ℤ) (I : RealInterval) (hscale : I.length = (2 : ℝ) ^ (k + 2))
    {b : ℝ → ℂ} (hb : Integrable b) {A : ℝ} (hA : 0 ≤ A)
    (hunit : ∀ x : ℝ,
      localUnitMass I b x ≤ A * (2 : ℝ) ^ (k + 2 - s))
    (hmass : ∫ x in I.centralThird, ‖b x‖ ≤
      (A * (2 : ℝ) ^ (k + 2 - s)) * I.length) :
    localizedEnergy k I b ≤
      (144 * positiveDyadicAmplitudeBound ^ 2 * A * (2 : ℝ) ^ (-s)) *
        ∫ x in I.centralThird, ‖b x‖ := by
  let M : ℝ := A * (2 : ℝ) ^ (k + 2 - s)
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hmain := localizedEnergy_le_of_localUnitMass_and_localMass k I hscale hb hM
    (by simpa only [M] using hunit) (by simpa only [M] using hmass)
  have hratio : M / I.length = A * (2 : ℝ) ^ (-s) := by
    have hpow : (2 : ℝ) ^ (k + 2 - s) =
        (2 : ℝ) ^ (k + 2) * (2 : ℝ) ^ (-s) := by
      rw [show k + 2 - s = (k + 2) + (-s) by ring,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    dsimp [M]
    rw [hscale, hpow]
    field_simp
  calc
    localizedEnergy k I b ≤
        (144 * positiveDyadicAmplitudeBound ^ 2 * M / I.length) *
          ∫ x in I.centralThird, ‖b x‖ := hmain
    _ = _ := by
      rw [show 144 * positiveDyadicAmplitudeBound ^ 2 * M / I.length =
        144 * positiveDyadicAmplitudeBound ^ 2 * (M / I.length) by ring, hratio]
      ring


end KrauseLaceyBadScale
end QuadraticCarleson
