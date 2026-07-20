/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Caleb L. Geiger
-/

import LeanPool.SingularModuli.QuadraticOrder.Prime.Inert
import LeanPool.SingularModuli.QuadraticOrder.Prime.Ramified

/-!
# Prime classification, part 5: the split case

**Thesis.** §3.2, Proposition 3.2.1 — the *split* branch: a rational prime `p`
splits in `O_d` (factors as a product of two distinct primes) exactly when the
Legendre symbol `(d/p) = 1`. Ideal-theoretically: `(p)` is radical but not
maximal.

**This file proves:**

* `prime_split_iff` — `(p)` radical ∧ ¬ maximal ↔ `(d/p) = 1`

This is the third branch of the prime-classification trichotomy, completing
`prime_inert_iff` (`Inert.lean`) and `prime_ramified_iff` (`Ramified.lean`).

**Divergence from thesis.** No new ideal-theory work: the proof is pure logical
composition of the inert and ramified iffs with the trichotomy
`legendreSym p d ∈ {-1, 0, 1}`. The "split = radical-but-not-maximal" framing
of the quotient `O/(p) ≅ 𝔽ₚ × 𝔽ₚ` is the Lean-idiomatic restatement of the
thesis's "p factors as two distinct primes".
-/

namespace QuadraticOrder

variable {d : ℤ} {p : ℕ}

/-- **Issue #7's split iff at the ideal level**: the ideal `(p)` is radical
but not maximal in `QuadraticOrder d` — equivalently, `(p)` factors as a
product of two distinct primes (the "split" case) — iff the Legendre symbol
`(d/p) = 1`. This is the remaining case of the prime-classification iff
trichotomy, complementing `prime_inert_iff` (`(d/p) = -1`) and
`prime_ramified_iff` (`(d/p) = 0`). The proof composes the latter two with
the trichotomy of `legendreSym p d ∈ {-1, 0, 1}`. -/
theorem prime_split_iff [Fact p.Prime] (hp2 : p ≠ 2)
    (hd : d % 4 = 0 ∨ d % 4 = 1) :
    ((Ideal.span {(p : QuadraticOrder d)}).IsRadical
        ∧ ¬ (Ideal.span {(p : QuadraticOrder d)}).IsMaximal)
      ↔ legendreSym p d = 1 := by
  constructor
  · rintro ⟨hrad, hnm⟩
    -- From `¬IsMaximal` and `prime_inert_iff`: `legendreSym p d ≠ -1`.
    have h_ne_neg : legendreSym p d ≠ -1 := fun heq =>
      hnm ((prime_inert_iff hp2 hd).mpr heq)
    -- From `IsRadical` and `prime_ramified_iff` + `legendreSym_eq_zero_iff_dvd`:
    -- `legendreSym p d ≠ 0`.
    have h_ne_zero : legendreSym p d ≠ 0 := fun heq =>
      (prime_ramified_iff hp2 hd).mpr
        (legendreSym_eq_zero_iff_dvd.mp heq) hrad
    -- Trichotomy of `legendreSym p d`: split on `(d : ZMod p) = 0`.
    by_cases h0 : (d : ZMod p) = 0
    · exact absurd ((legendreSym.eq_zero_iff p d).mpr h0) h_ne_zero
    · rcases legendreSym.eq_one_or_neg_one (p := p) h0 with hone | hnone
      · exact hone
      · exact absurd hnone h_ne_neg
  · intro h1
    have h_ne_neg : legendreSym p d ≠ -1 := by rw [h1]; decide
    have h_ne_zero : legendreSym p d ≠ 0 := by rw [h1]; decide
    refine ⟨?_, ?_⟩
    · -- `IsRadical`: contrapose via `prime_ramified_iff` and
      -- `legendreSym_eq_zero_iff_dvd`.
      by_contra hnr
      exact h_ne_zero
        (legendreSym_eq_zero_iff_dvd.mpr ((prime_ramified_iff hp2 hd).mp hnr))
    · -- `¬IsMaximal`: if `IsMaximal` then `prime_inert_iff` gives
      -- `legendreSym p d = -1`, contradicting `h_ne_neg`.
      exact fun hmax => h_ne_neg ((prime_inert_iff hp2 hd).mp hmax)

end QuadraticOrder
