/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.JacobianConstruction.Periods

/-!
# `periodSubgroup` membership (Forster §21.2)

Unit: period-lattice-rank (`docs/design/period-lattice-rank.md` §6.1). `periodSubgroup X` is
*defined* (jacobian-construction, `Periods.lean`) as the `AddSubgroup.closure` of the range of
`periodVector (basis X)` over based loops at the fixed basepoint `Classical.arbitrary X`. Forster's
`Per(ω₁,…,ω_g)` is literally this range (periods are additive under loop concatenation, so the
range is already subgroup-closed); this file packages that range directly as an `AddSubgroup` and
shows it equals `periodSubgroup X`, which is what Stage C of `Discreteness.lean` needs: a lattice
element must come from a SINGLE based loop, not merely from the closure abstractly.

Main declarations: `RS.periodRange X`, `RS.periodSubgroup_eq_periodRange`,
`RS.mem_periodSubgroup_iff`.
-/

open scoped ContDiff Manifold

noncomputable section

namespace RS

variable (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The range of period vectors of based loops at `Classical.arbitrary X`, packaged directly as an
additive subgroup (Forster's `Per(ω₁,…,ω_g)`, §21.2). Subgroup-closed by the loop algebra
(`periodVector_refl/_trans/_symm`). -/
def periodRange : AddSubgroup (Fin (genus X) → ℂ) where
  carrier := Set.range fun γ : Path (Classical.arbitrary X) (Classical.arbitrary X) =>
    periodVector (basis X) γ
  zero_mem' := ⟨Path.refl _, periodVector_refl _⟩
  add_mem' := by
    rintro _ _ ⟨γ₁, rfl⟩ ⟨γ₂, rfl⟩
    exact ⟨γ₁.trans γ₂, periodVector_trans (basis X) γ₁ γ₂⟩
  neg_mem' := by
    rintro _ ⟨γ, rfl⟩
    exact ⟨γ.symm, periodVector_symm (basis X) γ⟩

/-- The closure defining `periodSubgroup` is redundant: the generating set is already a subgroup
(Forster's observation that `Per` is literally the range, not merely its span). -/
theorem periodSubgroup_eq_periodRange : periodSubgroup X = periodRange X :=
  AddSubgroup.closure_eq (periodRange X)

/-- A vector lies in the period subgroup iff it is the period vector of a SINGLE based loop. -/
theorem mem_periodSubgroup_iff {t : Fin (genus X) → ℂ} :
    t ∈ periodSubgroup X ↔ ∃ γ : Path (Classical.arbitrary X) (Classical.arbitrary X),
      periodVector (basis X) γ = t := by
  rw [periodSubgroup_eq_periodRange]
  exact Iff.rfl

end RS

end
