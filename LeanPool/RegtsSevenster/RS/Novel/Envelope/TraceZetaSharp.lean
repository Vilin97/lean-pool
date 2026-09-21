/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Envelope.TraceZeta
import LeanPool.RegtsSevenster.RS.Novel.Envelope.HookConfinementSharp

/-!
# The trace-zeta theorem with the sharp threshold

The accompanying paper's Corollary A.2 in tower form, with the
appendix's own hypothesis on dimensions and its own threshold: for a
tower whose dimensions satisfy `finrank (E n) ≤ A ^ n`, and for
*every* integer `s > 2e√A`, the trace zeta function of every element
is `P/Q` with `P` and `Q` coprime, of constant term `1`, and of
degree at most `s − 1` (`traceZeta_rational_sharp`); equivalently the
power traces are a difference of power sums of two disjoint multisets
of nonzero complex numbers of sizes at most `s − 1`
(`traceZeta_superSpectrum_sharp`).

The appendix begins with a rigid symmetric ℂ-linear category and an
object `Z`, and derives the symmetric-group action on `Z ^ ⊗ n`, the
propagation of vanishing, the traces and the Frobenius identity from
the trace calculus.  A `FrobeniusTower` assumes exactly those as an
interface, and `ObjectTower.lean` constructs one from an arbitrary
category-and-object pair, so `traceZeta_rational_of_object` is Corollary A.2
in the appendix's own generality; the skein endomorphism algebras
instantiate the interface directly (`SkeinTower.lean`,
`BlockAssembly.lean`).

`TraceZeta.lean` proves the same conclusions over an arbitrary Schur
package with the side existentially quantified. The sharpness is in
the quantifier and the constant: every admissible side gives its own
degree bound,
and the threshold is stated in the growth constant itself.
-/

namespace RS

universe u

open scoped Polynomial PowerSeries

namespace FrobeniusTower

variable {E : ℕ → Type u}

/-- The hook-vanishing lemma at a given side above the threshold: the
Schur specialization of the power-trace sequence vanishes outside the
`(s − 1, s − 1)` hook.  This is `schur_vanishing_of_confinement` fed
the sharp confinement in place of the existential one. -/
private theorem schur_vanishing_sharp
    [∀ n, Ring (E n)] [∀ n, Algebra ℂ (E n)] {A : ℝ} {Alg : Type u}
    [Ring Alg] [Algebra ℂ Alg]
    [∀ n, Module.Finite ℂ (E n)]
    (T : FrobeniusTower schurPackage.{u} E A Alg) (g : Alg) {s : ℕ}
    (hs : 2 * Real.exp 1 * Real.sqrt A < s) :
    ∀ μ : YoungDiagram, ¬ IsInHook (s - 1) (s - 1) μ →
      diagramSchur μ (fun m => T.traceA (g ^ m)) = 0 :=
  T.schur_vanishing_of_confinement g
    (T.toPermTower.hook_confinement_sharp hs)

/-- **The trace-zeta theorem** (the accompanying paper, Corollary A.2,
in tower form).  For a tower whose dimensions are bounded by `A ^ n`,
and for every
integer `s > 2e√A`, the trace zeta function of every element of the
ambient algebra is rational, `ζ · Q = P`, with `P` and `Q` coprime
polynomials of constant term `1` and degree at most `s − 1`. -/
theorem traceZeta_rational_sharp
    [∀ n, Ring (E n)] [∀ n, Algebra ℂ (E n)] {A : ℝ} {Alg : Type u}
    [Ring Alg] [Algebra ℂ Alg]
    [∀ n, Module.Finite ℂ (E n)]
    (T : FrobeniusTower schurPackage.{u} E A Alg) (g : Alg) {s : ℕ}
    (hs : 2 * Real.exp 1 * Real.sqrt A < s) :
    ∃ Pp Qp : Polynomial ℂ,
      Pp.coeff 0 = 1 ∧ Qp.coeff 0 = 1 ∧
      Pp.natDegree ≤ s - 1 ∧ Qp.natDegree ≤ s - 1 ∧
      IsCoprime Pp Qp ∧
      traceZeta (fun m => T.traceA (g ^ m)) * ↑Qp =
        (↑Pp : PowerSeries ℂ) := by
  obtain ⟨Pp, Qp, hPc, hQc, hPd, hQd, hcop, hid⟩ :=
    newtonH_series_rational_of_hook_vanishing
      (schur_vanishing_sharp T g hs)
  exact ⟨Pp, Qp, hPc, hQc, hPd, hQd, hcop,
    by rw [traceZeta_eq_newtonH_series]; exact hid⟩

/-- **The reduced super-spectrum form of Corollary A.2**: for every integer
`s > 2e√A` the power traces are a difference of power sums of two
disjoint multisets of nonzero complex numbers, each of size at most
`s − 1`. -/
theorem traceZeta_superSpectrum_sharp
    [∀ n, Ring (E n)] [∀ n, Algebra ℂ (E n)] {A : ℝ} {Alg : Type u}
    [Ring Alg] [Algebra ℂ Alg]
    [∀ n, Module.Finite ℂ (E n)]
    (T : FrobeniusTower schurPackage.{u} E A Alg) (g : Alg) {s : ℕ}
    (hs : 2 * Real.exp 1 * Real.sqrt A < s) :
    ∃ alpha beta : Multiset ℂ,
      alpha.card ≤ s - 1 ∧ beta.card ≤ s - 1 ∧
      (∀ x ∈ alpha, x ≠ 0) ∧ (∀ x ∈ beta, x ≠ 0) ∧
      (∀ x ∈ alpha, x ∉ beta) ∧
      ∀ m : ℕ, 1 ≤ m →
        T.traceA (g ^ m) =
          (alpha.map (· ^ m)).sum - (beta.map (· ^ m)).sum :=
  superPowerSums_of_hook_vanishing
    (schur_vanishing_sharp T g hs)

end FrobeniusTower

end RS
