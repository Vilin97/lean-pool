/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Envelope.HookConfinement
import LeanPool.RegtsSevenster.RS.Classical.SymFun.HookVanishing

/-!
# The nilpotent-trace theorem

A `FrobeniusTower` is a `PermTower` together with an ambient algebra
`A`, trace functionals, tensor-power maps, and the Frobenius trace
identity `τ (rep (e μ) * pow g) = dim μ · s_μ[tr (g^·)]`.  The main
theorem: in such a tower every nilpotent element of `A` has trace
zero.

The proof composes the pieces already on the page: hook confinement
kills the idempotents of shapes outside a hook, the Frobenius
identity turns each death into vanishing of the Schur specialization
of the power-trace sequence, nilpotency makes that sequence
eventually zero, and the hook-vanishing engine
(`powerSums_zero_of_hook_and_eventually_zero`) then forces every
power trace — in particular the trace itself — to vanish.

The skein construction discharges the tower fields: `rep` is the
permutation action on strand bundles, `pow` the tensor power of an
endomorphism, and `frobenius` the categorical Frobenius formula.
-/

namespace RS

universe u

/-- A `PermTower` with an ambient algebra, traces, tensor-power
maps, and the Frobenius trace identity relative to a Schur
package. -/
structure FrobeniusTower (P : SchurPackage.{u}) (E : ℕ → Type u)
    [∀ n, Ring (E n)] [∀ n, Algebra ℂ (E n)] (A : ℝ)
    (Alg : Type u) [Ring Alg] [Algebra ℂ Alg] extends PermTower E A where
  /-- The trace on the ambient algebra. -/
  traceA : Alg →ₗ[ℂ] ℂ
  /-- The traces on the tower algebras. -/
  trace : ∀ n, E n →ₗ[ℂ] ℂ
  /-- The tensor-power maps. -/
  pow : ∀ n, Alg → E n
  /-- The Frobenius trace identity: the trace of a Young idempotent
  against a tensor power is the dimension times the Schur
  specialization of the power-trace sequence. -/
  frobenius : ∀ (μ : YoungDiagram) (g : Alg),
    trace μ.card (rep μ.card (P.e μ) * pow μ.card g) =
      (P.dim μ : ℂ) * diagramSchur μ (fun m => traceA (g ^ m))

namespace FrobeniusTower

variable {P : SchurPackage.{u}} {E : ℕ → Type u}

/-- **Schur vanishing from hook confinement**: if every shape alive in
the tower lies in the `(s − 1, s − 1)` hook, the Schur specialization
of the power-trace sequence vanishes on every shape outside it.  The
Frobenius identity turns a dead idempotent into a vanishing
specialization, and the block dimension is nonzero. -/
theorem schur_vanishing_of_confinement
    [∀ n, Ring (E n)] [∀ n, Algebra ℂ (E n)] {A : ℝ} {Alg : Type u}
    [Ring Alg] [Algebra ℂ Alg]
    (T : FrobeniusTower P E A Alg)
    (g : Alg) {s : ℕ}
    (hconf : ∀ μ : YoungDiagram, T.toPermTower.Alive P μ →
      IsInHook (s - 1) (s - 1) μ) :
    ∀ μ : YoungDiagram, ¬ IsInHook (s - 1) (s - 1) μ →
      diagramSchur μ (fun m => T.traceA (g ^ m)) = 0 := by
  intro μ hout
  have hdead : T.rep μ.card (P.e μ) = 0 :=
    not_not.mp (fun halive => hout (hconf μ halive))
  have hfrob := T.frobenius μ g
  rw [hdead, zero_mul, map_zero] at hfrob
  have hdim : (P.dim μ : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (P.dim_pos μ).ne'
  exact (mul_eq_zero.mp hfrob.symm).resolve_left hdim

/-- **The nilpotent-trace theorem**: in a Frobenius tower with
finite-dimensional levels, every nilpotent element of the ambient
algebra has trace zero. -/
theorem traceA_eq_zero_of_isNilpotent
    [∀ n, Ring (E n)] [∀ n, Algebra ℂ (E n)] {A : ℝ} {Alg : Type u}
    [Ring Alg] [Algebra ℂ Alg]
    [∀ n, Module.Finite ℂ (E n)]
    (T : FrobeniusTower P E A Alg) {g : Alg} (hg : IsNilpotent g) :
    T.traceA g = 0 := by
  obtain ⟨s, hconf⟩ := T.toPermTower.hook_confinement P
  set t : ℕ → ℂ := fun m => T.traceA (g ^ m) with ht
  -- ═══════ Schur vanishing outside the hook ═══════
  have hvan : ∀ μ : YoungDiagram, ¬ IsInHook (s - 1) (s - 1) μ →
      diagramSchur μ t = 0 := T.schur_vanishing_of_confinement g hconf
  -- ═══════ Eventual vanishing from nilpotency ═══════
  have hev : ∃ N₀ : ℕ, ∀ m, N₀ ≤ m → t m = 0 := by
    obtain ⟨N, hN⟩ := hg
    refine ⟨N, fun m hm => ?_⟩
    have hzero : g ^ m = 0 := by
      calc g ^ m = g ^ N * g ^ (m - N) := by
            rw [← pow_add]
            congr 1
            omega
        _ = 0 := by rw [hN, zero_mul]
    simp [ht, hzero]
  -- ═══════ The engine ═══════
  have := powerSums_zero_of_hook_and_eventually_zero
    hvan hev 1 le_rfl
  simpa [ht] using this

end FrobeniusTower

end RS
