/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/

import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import LeanPool.Chudnovsky.Basic
import LeanPool.Chudnovsky.SingularModuli.Kronecker
import LeanPool.Chudnovsky.SingularModuli.Rationality
import LeanPool.Chudnovsky.SingularModuli.MasserA1

/-!
# Singular moduli at `τ₁₆₃`: the cited arithmetic inputs (Phase C)

Milla's paper (arXiv:1809.00533v6) does *not* prove the following three statements;
it cites them from the literature, and they are the main open risk of this
formalization (PLAN Phase C):

1. `isIntegral_j_τ₁₆₃` : `j(τ₁₆₃) = 1728·J(τ₁₆₃)` is an algebraic integer
   [Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Thm. II.6.1];
2. `j_τ₁₆₃_rational` : `j(τ₁₆₃)` has degree `h(-163) = 1` over `ℚ`, hence is rational
   [Silverman ATAEC II.4.3(b), together with `h(-163) = 1` from Buell,
   *Binary Quadratic Forms*];
3. `s₂_τ₁₆₃_rational` : `s₂(τ₁₆₃) ∈ ℚ(j(τ₁₆₃)) = ℚ`
   [Masser, *Elliptic Functions and Transcendence* (1975), Appendix A1, Thm. A1;
   Masser's `Ψ(τ)` is `(3/2)·s₂(τ)`].

Their combination `j_τ₁₆₃_integer` (a rational algebraic integer is an integer) is
what ch. 10 actually consumes, together with statement 3.

Everything else in the development (Phases A, B, D) can be completed with these as
explicit hypotheses, giving the intermediate milestone `chudnovsky_of_singular_moduli`
(PLAN Phase C).
-/

/-
Candidate proof routes, summarized from PLAN.md (Phase C):

1. Integrality of `j` at CM points: the classical modular-polynomial route.
   Build enough of the function-field theory of level-1 modular forms to construct
   `Φ_m ∈ ℤ[X, Y]` (q-expansion principle + elementary symmetric functions over the
   m-isogeny orbit), prove Kronecker's lemma (`Φ_m(X, X)` has unit leading coefficient
   for non-square `m`), and use the endomorphism `C·τ·L ⊆ L` of norm `m = A·C = 41` at
   `τ₁₆₃` to get `Φ₄₁(j(τ₁₆₃), j(τ₁₆₃)) = 0`. A serious standalone project, comparable
   in scale to Mathlib's existing `Δ`/`E₄`/`E₆` theory.

2. Rationality of `j(τ₁₆₃)`: `h(-163) = 1` is a finite reduced-binary-quadratic-forms
   computation (`decide`-able once form reduction is set up; small but absent from
   Mathlib). The hard part is "the conjugates of `j(τ)` are the `j(τ_Q)`" — the main
   theorem of complex multiplication; no shortcut is known within Milla's framework.

3. Rationality of `s₂(τ₁₆₃)`: Masser's own Appendix A1 proof is elliptic-function-
   theoretic (the same toolbox as the paper's Appendix B / `ComplexMult.lean`) but
   nontrivial; it needs its own outline pass before formalization.
-/

noncomputable section

namespace Chudnovsky

open Complex

/-- **Cited input 1** [Silverman ATAEC II.6.1]. The value of the `j`-invariant
`j = 1728·J` at the CM point `τ₁₆₃ = (1 + i√163)/2` is an algebraic integer. -/
theorem isIntegral_j_τ₁₆₃ : IsIntegral ℤ (1728 * J τ₁₆₃) := by
  haveI : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  haveI : NeZero (41 : ℕ) := ⟨by norm_num⟩
  obtain ⟨PhiZ, hPhi⟩ := exists_PhiZ_closed (m := 41)
  obtain ⟨i, hi⟩ := cm_coset_rel (m := 41) 0 (by norm_num)
  exact isIntegral_j_of_cm hPhi hi.symm

/-- **Cited input 2** [Silverman ATAEC II.4.3(b); Buell]. The degree of `j(τ₁₆₃)`
over `ℚ` is the class number `h(-163) = 1`, so `j(τ₁₆₃)` is rational. -/
theorem j_τ₁₆₃_rational : ∃ r : ℚ, 1728 * J τ₁₆₃ = (r : ℂ) :=
  j_τ₁₆₃_rational_of j_surjective isIntegral_j_τ₁₆₃

/-- **Cited input 3** [Masser 1975, Thm. A1]. Ramanujan's function `s₂` is rational
at `τ₁₆₃`: `s₂(τ) ∈ ℚ(j(τ))` at CM points, and here `ℚ(j(τ₁₆₃)) = ℚ`. -/
theorem s₂_τ₁₆₃_rational : ∃ r : ℚ, s₂ τ₁₆₃ = (r : ℂ) :=
  masser_s₂_rational

/-- Combination of `isIntegral_j_τ₁₆₃` and `j_τ₁₆₃_rational`: a rational algebraic
integer is an integer, so `j(τ₁₆₃) = 1728·J(τ₁₆₃) ∈ ℤ`. (Ch. 10 then pins it down to
`-640320³` using the numeric bounds of Phases A5/D1.) -/
theorem j_τ₁₆₃_integer : ∃ m : ℤ, 1728 * J τ₁₆₃ = (m : ℂ) := by
  obtain ⟨r, hr⟩ := j_τ₁₆₃_rational
  exact isInt_of_integral_of_rat isIntegral_j_τ₁₆₃ hr

end Chudnovsky
