/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Assembly.ReductionSurjectivity

namespace Challenge

abbrev MarkoffNat :=
  {⟨x, y, z⟩ : ℕ × ℕ × ℕ | x ^ 2 + y ^ 2 + z ^ 2 = 3 * x * y * z}

abbrev MarkoffModp (p : ℕ) :=
  {⟨x, y, z⟩ : ZMod p × ZMod p × ZMod p | x ^ 2 + y ^ 2 + z ^ 2 = 3 * x * y * z}

abbrev markoffNatToModp (p : ℕ) : MarkoffNat → MarkoffModp p :=
  fun ⟨⟨x, y, z⟩, h⟩ ↦ ⟨⟨x, y, z⟩, by simpa using congrArg (fun n : ℕ ↦ (n : ZMod p)) h⟩

theorem markoff_reduction_surjective_of_large_prime :
    let p₀ := 35721 ^ 5 * 2 ^ 1547 * 32769 ^ 2 + 1
    ∀ (p : ℕ), p.Prime → p₀ ≤ p → Function.Surjective (markoffNatToModp p) := by
  dsimp only
  intro p hpPrime hp y
  obtain ⟨x, hx⟩ :=
    BGS.Markoff.reduction_surjective_of_explicitBound p hpPrime hp y
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact congrArg Subtype.val hx

end Challenge
