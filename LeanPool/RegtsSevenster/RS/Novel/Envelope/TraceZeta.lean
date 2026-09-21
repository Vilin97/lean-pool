/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Envelope.NilpotentTrace
import LeanPool.RegtsSevenster.RS.Classical.SymFun.ZetaRational
import LeanPool.RegtsSevenster.RS.Classical.SymFun.ZetaExp

/-!
# The quantitative trace-zeta theorem

In a Frobenius tower, the trace zeta function of every element is
rational with numerator and denominator degrees bounded by the hook
parameter.  This combines hook confinement (dead shapes outside a hook)
with the Frobenius identity (turning dead shapes into Schur vanishing)
and the rationality and reduced super-spectrum results from
`ZetaRational` and `HookVanishing`.

The side is existentially quantified here, and the package is arbitrary.
`TraceZetaSharp.lean` states the same conclusions in the appendix's
own generality: a real dimension bound and every side above
`2e√A`.

Unlike `NilpotentTrace`, no nilpotency hypothesis is needed: the
hook-vanishing half of the proof uses only the Frobenius identity and
hook confinement, both of which hold for every element.
-/

namespace RS

universe u

open scoped Polynomial PowerSeries

namespace FrobeniusTower

variable {P : SchurPackage.{u}} {E : ℕ → Type u}

/-- The hook-vanishing lemma for an arbitrary element of a Frobenius
tower: the Schur specialization of the power-trace sequence vanishes
outside the hook `hook_confinement` supplies. -/
private theorem schur_vanishing_of_frobenius
    [∀ n, Ring (E n)] [∀ n, Algebra ℂ (E n)] {A : ℝ} {Alg : Type u}
    [Ring Alg] [Algebra ℂ Alg]
    [∀ n, Module.Finite ℂ (E n)]
    (T : FrobeniusTower P E A Alg) (g : Alg) :
    ∃ s : ℕ, ∀ μ : YoungDiagram, ¬ IsInHook (s - 1) (s - 1) μ →
      diagramSchur μ (fun m => T.traceA (g ^ m)) = 0 :=
  let ⟨s, hconf⟩ := T.toPermTower.hook_confinement P
  ⟨s, T.schur_vanishing_of_confinement g hconf⟩

/-- **The trace-zeta theorem over an arbitrary Schur package**: in a
Frobenius tower, the trace zeta function of every element is rational
with numerator and denominator degrees bounded by the hook parameter
the package's growth field supplies. Corollary A.2 of the accompanying
paper, with its real growth constant and its threshold on every side, is
`traceZeta_rational_sharp` in `TraceZetaSharp.lean`. -/
theorem traceZeta_rational
    [∀ n, Ring (E n)] [∀ n, Algebra ℂ (E n)] {A : ℝ} {Alg : Type u}
    [Ring Alg] [Algebra ℂ Alg]
    [∀ n, Module.Finite ℂ (E n)]
    (T : FrobeniusTower P E A Alg) (g : Alg) :
    ∃ (s : ℕ) (Pp Qp : Polynomial ℂ),
      Pp.coeff 0 = 1 ∧ Qp.coeff 0 = 1 ∧
      Pp.natDegree ≤ s - 1 ∧ Qp.natDegree ≤ s - 1 ∧
      IsCoprime Pp Qp ∧
      traceZeta (fun m => T.traceA (g ^ m)) * ↑Qp = (↑Pp : PowerSeries ℂ) := by
  obtain ⟨s, hvan⟩ := schur_vanishing_of_frobenius T g
  obtain ⟨Pp, Qp, hPc, hQc, hPd, hQd, hcop, hid⟩ :=
    newtonH_series_rational_of_hook_vanishing hvan
  exact ⟨s, Pp, Qp, hPc, hQc, hPd, hQd, hcop,
    by rw [traceZeta_eq_newtonH_series]; exact hid⟩

/-- **The reduced super-spectrum corollary**: the trace sequence of every
element in a Frobenius tower is a difference of power sums of two
disjoint multisets of nonzero complex numbers of sizes at most
`s − 1`. -/
theorem traceZeta_superSpectrum
    [∀ n, Ring (E n)] [∀ n, Algebra ℂ (E n)] {A : ℝ} {Alg : Type u}
    [Ring Alg] [Algebra ℂ Alg]
    [∀ n, Module.Finite ℂ (E n)]
    (T : FrobeniusTower P E A Alg) (g : Alg) :
    ∃ (s : ℕ) (alpha beta : Multiset ℂ),
      alpha.card ≤ s - 1 ∧ beta.card ≤ s - 1 ∧
      (∀ x ∈ alpha, x ≠ 0) ∧ (∀ x ∈ beta, x ≠ 0) ∧
      (∀ x ∈ alpha, x ∉ beta) ∧
      ∀ m : ℕ, 1 ≤ m →
        T.traceA (g ^ m) =
          (alpha.map (· ^ m)).sum - (beta.map (· ^ m)).sum := by
  obtain ⟨s, hvan⟩ := schur_vanishing_of_frobenius T g
  obtain ⟨alpha, beta, ha, hb, hαnz, hβnz, hdisj, hps⟩ :=
    superPowerSums_of_hook_vanishing hvan
  exact ⟨s, alpha, beta, ha, hb, hαnz, hβnz, hdisj, hps⟩

end FrobeniusTower

end RS
