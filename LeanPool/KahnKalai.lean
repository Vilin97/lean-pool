/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Clemens Posch
-/

import LeanPool.KahnKalai.ParkPham

/-!
# Kahn–Kalai expectation-threshold theorem

Source: arxiv:2303.02144, doi:10.37236/12266, url:https://github.com/dcposch/kahn-kalai-lean
Authors: Dan Clemens Posch
Status: verified
Main declarations: `KahnKalai.covering_theorem`, `KahnKalai.park_pham`
Tags: probabilistic-combinatorics, random-structures, threshold-phenomena, set-systems
MSC: 05C80, 60C05
-/

namespace KahnKalai

/-- **Tran–Vu, Theorem 2.3.** If `H` is `ℓ`-bounded and
`f(H) ≥ 1/2 - 2^{-(ℓ+2)}`, then `⟨H⟩` contains at least a
`2/3 + 2^{-(ℓ+2)}` fraction of the `m_ℓ`-level. -/
theorem covering_theorem {α : Type*} [DecidableEq α] [Fintype α]
    (H : Finset (Finset α)) (ℓ : ℕ) (p : ℝ)
    (hℓ : ℓ ≤ Fintype.card α)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hb : IsBounded H ℓ)
    (hf : (1 : ℝ) / 2 - 1 / (2 : ℝ) ^ (ℓ + 2) ≤ coverCost p H) :
    ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ + 2)) *
        ((Fintype.card α).choose (coveringLevel p (Fintype.card α) ℓ) : ℝ) ≤
      (((generate H).filter
          (fun S => S.card = coveringLevel p (Fintype.card α) ℓ)).card : ℝ) :=
  covering_aux ℓ H p hℓ hp0 hp1 hb hf

/-- **Park–Pham / Kahn–Kalai** (Tran–Vu, Theorem 1.1). There is an absolute
constant `K` such that every `ℓ`-bounded family with `ℓ ≥ 2` satisfies
`p_c(F) ≤ K q(F) log₂ ℓ`. -/
theorem park_pham :
    ∃ K : ℝ, 0 < K ∧
      ∀ {α : Type} [DecidableEq α] [Fintype α]
        (F : Finset (Finset α)) (ℓ : ℕ),
        2 ≤ ℓ → IsBounded F ℓ →
        threshold F ≤ K * expectationThreshold F * Real.logb 2 (ℓ : ℝ) :=
  ⟨parkPhamK, parkPhamK_pos, park_pham_bound⟩

end KahnKalai
