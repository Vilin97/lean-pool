/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.CanonicalForms

/-!
# Compat: small `MForm` helpers needed by residue-theorem (candidates for canonical-forms)

Unit: residue-theorem (`docs/design/residue-theorem.md`). Per CONVENTIONS.md's Compat rule and
the task brief's file discipline, these three one-step corollaries of canonical-forms' frozen
quotient API live in a clearly-marked NEW file rather than editing `Jacobian/CanonicalForms/`:

* `RS.MForm.resAt_eq_zero_of_ord_nonneg` — residues vanish where the order is nonnegative
  (the §1.2 gap flagged in the residue-theorem design; `RS.resAt_of_order_nonneg` composed with
  the definition of `MForm.resAt`).
* `RS.MForm.finite_setOf_ord_neg` — the pole set of a meromorphic 1-form on a compact surface
  is finite (via the divisor's finite support; no connectedness needed).
* `RS.MForm.finite_support_resAt` — hence `resAt` has finite support.

Request filed in `docs/requests/canonical-forms.md`-spirit: these belong upstream eventually.
-/

open scoped ContDiff Manifold
open Set Filter Topology

noncomputable section

namespace RS.MForm

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The residue of a meromorphic 1-form vanishes at any point of nonnegative order. -/
theorem resAt_eq_zero_of_ord_nonneg {Θ : MForm X} {x : X} (h : 0 ≤ Θ.ord x) :
    Θ.resAt x = 0 := by
  obtain ⟨θ, rfl⟩ := exists_rep Θ
  have h' : 0 ≤ meromorphicOrderAt (θ.coeffAt x) (chartAt ℂ x x) := h
  exact RS.resAt_of_order_nonneg h'

/-- The pole set of a meromorphic 1-form on a compact surface is finite (via the divisor's
finite support; connectedness-free). -/
theorem finite_setOf_ord_neg [T1Space X] [T2Space X] [CompactSpace X] (Θ : MForm X) :
    {x : X | Θ.ord x < 0}.Finite := by
  apply Set.Finite.subset (Θ.divisor.finiteSupport isCompact_univ)
  intro y hy
  simp only [Set.mem_ofPred_eq] at hy
  simp only [Function.mem_support, ne_eq]
  intro hcon
  rw [divisor_apply, WithTop.untop₀_eq_zero] at hcon
  rcases hcon with hcon | hcon
  · rw [hcon] at hy
    exact absurd hy (lt_irrefl 0)
  · rw [hcon] at hy
    exact not_top_lt hy

/-- `MForm.resAt` has finite support on a compact surface. -/
theorem finite_support_resAt [T1Space X] [T2Space X] [CompactSpace X] (Θ : MForm X) :
    (Function.support fun x => Θ.resAt x).Finite := by
  apply Set.Finite.subset (finite_setOf_ord_neg Θ)
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hcon
  exact hx (resAt_eq_zero_of_ord_nonneg (not_lt.1 hcon))

end RS.MForm
