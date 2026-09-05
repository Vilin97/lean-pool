/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude
import LeanPool.KasamiCyclicAdditive.Assembly.GeometricChain
import LeanPool.KasamiCyclicAdditive.Assembly.ElementaryInputs
import LeanPool.KasamiCyclicAdditive.Assembly.CoefficientReduction
import LeanPool.KasamiCyclicAdditive.Counting.Average
import LeanPool.KasamiCyclicAdditive.Assembly.Normalization
import LeanPool.KasamiCyclicAdditive.MCM.PhaseFormula
import LeanPool.KasamiCyclicAdditive.MCM.ComplementTransport

/-!
# Reduction around the assembled Kasami chain

This module assembles the reduction around `kasami_conjecture_of_inputs`.
The count and average identities are derived in `Counting/Average.lean`, and the
normalization and Frobenius coefficient transport in `Normalization`, both
from the derivative-image half-size equation together with elementary
arithmetic. The theorems below are kept in their general hypothesis-taking
form, with convenience wrappers taking only the half-size equation (and, in
one case, also `DillonKashyapPhaseFormula`) supplied afterwards.
-/

namespace KasamiCyclicAdditive

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

/-- The factor `m` in `2^k+1=3m` is automatically nonzero. -/
theorem three_factor_ne_zero {k m : ℕ} (he : 2 ^ k + 1 = 3 * m) : m ≠ 0 := by
  have hp : 0 < 2 ^ k + 1 := by positivity
  rw [he] at hp
  omega

/-- The normalized slope theorem from the Dillon–Kashyap phase formula together
with the count and average identities.  The primitive additive character, the
inverse exponent `D`, the Walsh formula, and nonemptiness of `slopes K` are all
constructed internally. -/
theorem normalized_slope_of_phase_count_average {n k m : ℕ}
    (hn : 2 ≤ n) (hcard : Fintype.card K = 2 ^ n) (hkn : Nat.Coprime k n)
    (he : 2 ^ k + 1 = 3 * m) (hcop : Nat.Coprime m (2 ^ n - 1))
    (hphase : DillonKashyapPhaseFormula k (primitiveAddChar K))
    (hcount_formula : ∀ ρ : K, AdmissibleSlope ρ →
      (slopeTripleCount k ρ : ℝ) = (Fintype.card K : ℝ) ^ 2 / 8
        + (KasamiCyclicAdditive.Phase.phaseTripleSum
            (walshCoefficient k (primitiveAddChar K)) ρ (1 + ρ)).re /
            (Fintype.card K : ℝ))
    (havg : (∑ ρ ∈ slopes K, (slopeTripleCount k ρ : ℝ)) / ((slopes K).card : ℝ)
      = (Fintype.card K : ℝ) ^ 2 / 8) :
    ∀ ρ ∈ slopes K,
      (slopeTripleCount k ρ : ℝ) = (Fintype.card K : ℝ) ^ 2 / 8 := by
  have hψ : (primitiveAddChar K).IsPrimitive := primitiveAddChar_isPrimitive
  have hm : m ≠ 0 := three_factor_ne_zero he
  obtain ⟨D, hD, hmD⟩ := exists_inverse_exponent_units hn hcard hcop
  have hW : KasamiCyclicAdditive.Phase.WalshCharacterFormula (primitiveAddChar K) (2 ^ k + 1)
      (walshCoefficient k (primitiveAddChar K)) :=
    walshCharacterFormula_of_phase_formula hψ hphase
  have hne : (slopes K).Nonempty := slopes_nonempty_of_card_two_pow hn hcard
  exact kasami_conjecture_of_inputs hψ hcard hkn hm hD hmD he hcop hW hcount_formula havg hne


/-! ### Half-size/cardinality-only form

`phase_formula_from_half_size` (`MCM/PhaseFormula.lean`) supplies the phase
formula directly from the half-size cardinality and elementary MCM/Dickson
character algebra, so these theorems need no Dillon–Kashyap or Dillon–Dobbertin
input. -/

/-- The normalized slope theorem, half-size/cardinality-only form. -/
theorem normalized_slope_of_half_size {n k m : ℕ}
    (hkpos : 1 ≤ k) (hklt : k < n) (hk : Odd k) (hcard : Fintype.card K = 2 ^ n)
    (hkn : Nat.Coprime k n) (he : 2 ^ k + 1 = 3 * m) (hcop : Nat.Coprime m (2 ^ n - 1))
    (hhalf : 2 * (derivativeImage k K).card = Fintype.card K) :
    ∀ ρ ∈ slopes K,
      (slopeTripleCount k ρ : ℝ) = (Fintype.card K : ℝ) ^ 2 / 8 := by
  have hn : 2 ≤ n := by omega
  have hK2 : 2 < Fintype.card K := by
    rw [hcard]
    calc
      2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  exact normalized_slope_of_phase_count_average hn hcard hkn he hcop
    (phase_formula_from_half_size hklt hk hcard hkn he hcop hhalf)
    (walshTripleCountFormula_of_half_size hhalf)
    (slopeAverageFormula_of_half_size hhalf hK2)

/-- Coefficient form at `(k, v₁, v₂)` from half-size at the normalized parameter
`k0`, given coefficients `w1, w2` carrying the count to `k0`. -/
theorem coefficient_conjecture_of_half_size {n k k0 m : ℕ}
    (hkpos : 1 ≤ k0) (hklt : k0 < n) (hk : Odd k0) (hcard : Fintype.card K = 2 ^ n)
    (hkn0 : Nat.Coprime k0 n) (he : 2 ^ k0 + 1 = 3 * m) (hcop : Nat.Coprime m (2 ^ n - 1))
    (hhalf : 2 * (derivativeImage k0 K).card = Fintype.card K)
    {v₁ v₂ w1 w2 : K}
    (hw1 : w1 ≠ 0) (hw2 : w2 ≠ 0) (hwne : w1 ≠ w2)
    (hcount : coefficientTripleCount k v₁ v₂ = coefficientTripleCount k0 w1 w2) :
    coefficientTripleCount k v₁ v₂ = 2 ^ (2 * n - 3) := by
  have hn : 2 ≤ n := by omega
  have hslope := normalized_slope_of_half_size hkpos hklt hk hcard hkn0 he hcop hhalf
  exact coefficient_form_of_normalized_witness hn hcard hslope hw1 hw2 hwne hcount

/-- **The Kasami cyclic-additive coefficient conjecture, half-size-only form.**
The sole size input is the derivative-image half-size equation; the
Dillon–Kashyap phase formula is derived internally by
`phase_formula_from_half_size` of `MCM/PhaseFormula.lean`. -/
theorem kasami_conjecture_of_half_size {n k : ℕ}
    (hkpos : 1 ≤ k) (hklt : k < n) (hkn : Nat.Coprime k n)
    (hcard : Fintype.card K = 2 ^ n)
    (hhalf : 2 * (derivativeImage k K).card = Fintype.card K)
    {v₁ v₂ : K} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    coefficientTripleCount k v₁ v₂ = 2 ^ (2 * n - 3) := by
  obtain ⟨k0, m, w1, w2, _hk0, hkpos0, hklt0, hodd, hcop0, he, hcop,
      hhalf0, hw1, hw2, hwne, hcount⟩ :=
    normalize_with_count_transport hkpos hklt hkn hcard hhalf hv₁ hv₂ hne
  exact coefficient_conjecture_of_half_size hkpos0 hklt0 hodd hcard hcop0 he hcop
    hhalf0 hw1 hw2 hwne hcount

end KasamiCyclicAdditive
