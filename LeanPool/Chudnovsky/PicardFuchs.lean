/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/

import LeanPool.Chudnovsky.Clausen

/-!
# The Picard–Fuchs differential equation

This file covers chapter 7 of Milla's proof of the Chudnovsky formula (arXiv:1809.00533v6,
`120_PicardFuchs.tex`).

## Main definitions

* `Chudnovsky.SatisfiesPicardFuchs` : the predicate that a function `Ω : ℂ → ℂ` satisfies the
  Picard–Fuchs differential equation
  `d²Ω/dJ² + (1/J)·dΩ/dJ + (31J - 4)/(144·J²·(J-1)²)·Ω = 0`
  on a set `S ⊆ ℂ` (paper Thm. `picardfuchs`).

## Note

The Chudnovsky formula proof of this development follows PLAN A7's recommended alternative,
which bypasses the Picard–Fuchs equation entirely and proves the chapter-8 output
`E₄ = (₂F₁(1/12, 5/12; 1; 1/J))⁴` directly in `q`-space via Ramanujan's derivative identities
(`D E₂ = (E₂² - E₄)/12`, etc.) — see `Kummer.lean`. Consequently only the definition
`SatisfiesPicardFuchs` is used downstream (by `Kummer.lean`); the paper's chapter-7 existence
theorem for the periods is not needed on the main chain and is omitted here.
-/

noncomputable section

namespace Chudnovsky

open UpperHalfPlane Complex

/-- The **Picard–Fuchs differential equation** (paper Thm. `picardfuchs`):
`Ω` satisfies `d²Ω/dJ² + (1/J)·dΩ/dJ + (31J - 4)/(144·J²·(J-1)²)·Ω = 0` at every point of `S`. -/
def SatisfiesPicardFuchs (Ω : ℂ → ℂ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S,
    deriv (deriv Ω) z + 1 / z * deriv Ω z
      + (31 * z - 4) / (144 * z ^ 2 * (z - 1) ^ 2) * Ω z = 0

end Chudnovsky
