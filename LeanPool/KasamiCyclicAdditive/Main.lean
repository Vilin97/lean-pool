/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.MCM.HalfSize
import LeanPool.KasamiCyclicAdditive.Assembly.Reduction
import LeanPool.KasamiCyclicAdditive.Statement.ParameterReduction

/-!
# The assembled theorem

The final assembly.  `Assembly/Reduction.lean` proves the conjecture from
the half-size cardinality at `k`;
`MCM/HalfSize.lean` proves the half-size fact itself from the MCM permutation
theorem.  Composing them leaves no mathematical hypothesis beyond those in the
normalized statement.

The literature statement does not assume `k < n`.  The final theorem below
derives `n ≥ 2` from the coefficient hypotheses, then reduces arbitrary `k`
coprime to `n` to `k % n` using the proved periodicity results in
`Statement/ParameterReduction.lean`.  Positivity of the normalized
representative is also derived, not assumed.
-/

namespace KasamiCyclicAdditive

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- Self-contained proof target for Carlet's Kasami cyclic-additive conjecture
in the normalized range `1 ≤ k < n`. -/
theorem carlet_kasami_cyclic_additive_core
    [CharP K 2]
    {n k : ℕ} (hkpos : 1 ≤ k) (hklt : k < n) (hkn : Nat.Coprime k n)
    (hcard : Fintype.card K = 2 ^ n)
    {v₁ v₂ : K} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
  coefficientTripleCount k v₁ v₂ = 2 ^ (2 * n - 3) :=
  kasami_conjecture_of_half_size hkpos hklt hkn hcard
    (kasami_half_size hkpos hklt hkn hcard) hv₁ hv₂ hne

/-- Literature form of the conjecture.  No range or positivity
hypothesis on `k` is needed at the statement surface: the remaining
hypotheses force `n ≥ 2`, and coprimality then makes `k % n` a positive
representative below `n`.  The coefficient count is invariant under this
reduction. -/
theorem carlet_kasami_cyclic_additive_literature
    [CharP K 2]
    {n k : ℕ} (hkn : Nat.Coprime k n)
    (hcard : Fintype.card K = 2 ^ n)
    {v₁ v₂ : K} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    coefficientTripleCount k v₁ v₂ = 2 ^ (2 * n - 3) := by
  have hn : 2 ≤ n :=
    extension_degree_at_least_two_of_coefficients hcard hv₁ hv₂ hne
  obtain ⟨hrpos, hrlt, hrcoprime⟩ := mod_parameter_admissible hn hkn
  rw [coefficientTripleCount_mod_degree (K := K) (n := n) (k := k) hcard]
  exact carlet_kasami_cyclic_additive_core
    hrpos hrlt hrcoprime hcard hv₁ hv₂ hne

end KasamiCyclicAdditive
