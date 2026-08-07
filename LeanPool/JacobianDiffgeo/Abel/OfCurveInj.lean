/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Abel.Sufficiency
import LeanPool.JacobianDiffgeo.Abel.UpgradeDischarge

/-!
# abel-theorem: the gated `ofCurve_inj` and final-assembly discharge (§4.4 D4)

Unit: abel-theorem. Namespace `Jacobian`. The challenge's `ofCurve_inj`
(`docs/Jacobian_challenge.lean:99`), assembled from `RS.Abel.genus_eq_zero_of_pathIntegral_mem`
(`Sufficiency.lean`) via the frozen ordering-resolution bridge
(`AddSubgroup.isClosed_of_discrete`, §1.3/§9 of the design, spike-verified).

Both theorems below are stated exactly at their design shape and type-check; `ofCurve_inj'`'s
PROOF calls `RS.Abel.genus_eq_zero_of_pathIntegral_mem`, so it inherits that theorem's one
remaining explicit hypothesis (`RS.Abel.WeakSolutionUpgrade X`, see `Sufficiency.lean`'s own
docstring for the precise account — the external `serre-duality-tails` blocker itself has
CLEARED) transitively, as an explicit hypothesis argument here too (no NEW hypothesis is
introduced in this file). `ofCurve_inj` is a one-line wrapper, discharged unconditionally the
moment `period-lattice-rank` registers `instance : DiscreteTopology (RS.periodSubgroup X)` AND
`WeakSolutionUpgrade X` is proved (see `Sufficiency.lean` for the precise remaining roadmap).
-/

open scoped ContDiff Manifold

namespace Jacobian

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **The challenge lemma, gated** on the literal (uncompleted) period subgroup's discreteness —
Forster 21.4(i) exactly, NOT the `.topologicalClosure` variant `jacobian-construction`'s other
gated instances use (§4.4 reconciles the two shapes; `period-lattice-rank` is expected to
register both, per the design's coordination note) — AND on `RS.Abel.WeakSolutionUpgrade X`
(`Sufficiency.lean`), the one remaining, precisely-isolated non-external hypothesis. -/
theorem ofCurve_inj' (hupgrade : RS.Abel.WeakSolutionUpgrade X) (P : X) (h : 0 < genus X)
    [DiscreteTopology (RS.periodSubgroup X)] :
    Function.Injective (ofCurve P) := by
  intro x y hxy
  by_contra hne
  -- The bridge: discreteness ⟹ closedness ⟹ `closure = self` (design §1.3/§9, spike-verified).
  have hclosed : IsClosed (RS.periodSubgroup X : Set (Fin (genus X) → ℂ)) :=
    AddSubgroup.isClosed_of_discrete
  have hclosure_eq : (RS.periodSubgroup X).topologicalClosure = RS.periodSubgroup X :=
    le_antisymm (AddSubgroup.topologicalClosure_minimal _ le_rfl hclosed)
      (AddSubgroup.le_topologicalClosure _)
  -- Unfold `hxy : ofCurve P x = ofCurve P y` down to membership in `(periodSubgroup X)
  -- .topologicalClosure`, then rewrite it to the literal `periodSubgroup X` via the bridge.
  have hxy' : (fun i => RS.pathIntegral (PathConnectedSpace.somePath P x) (RS.basis X i))
      - (fun i => RS.pathIntegral (PathConnectedSpace.somePath P y) (RS.basis X i))
      ∈ (RS.periodSubgroup X).topologicalClosure := by
    have := ULift.up.injEq .. |>.mp hxy
    rwa [QuotientAddGroup.eq_iff_sub_mem] at this
  rw [hclosure_eq] at hxy'
  -- `τ := (somePath P x).symm.trans (somePath P y) : Path x y` has exactly this period vector,
  -- negated (the same `pathIntegral_trans`/`_symm` algebra `ofCurve_eq_of_path` itself uses).
  set τ : Path x y :=
    (PathConnectedSpace.somePath P x).symm.trans (PathConnectedSpace.somePath P y) with hτ_def
  have hτ_eq : (fun i => RS.pathIntegral τ (RS.basis X i))
      = -((fun i => RS.pathIntegral (PathConnectedSpace.somePath P x) (RS.basis X i))
          - (fun i => RS.pathIntegral (PathConnectedSpace.somePath P y) (RS.basis X i))) := by
    funext i
    change RS.pathIntegral ((PathConnectedSpace.somePath P x).symm.trans
      (PathConnectedSpace.somePath P y)) (RS.basis X i) = _
    rw [RS.pathIntegral_trans, RS.pathIntegral_symm]
    simp only [Pi.neg_apply, Pi.sub_apply]
    ring
  have hmem : (fun i => RS.pathIntegral τ (RS.basis X i)) ∈ RS.periodSubgroup X := by
    rw [hτ_eq]; exact (RS.periodSubgroup X).neg_mem hxy'
  exact absurd (RS.Abel.genus_eq_zero_of_pathIntegral_mem hupgrade hne τ hmem) (by omega)

/-- **The literal challenge statement** (`docs/Jacobian_challenge.lean:99`), discharged the
moment `period-lattice-rank` registers `instance : DiscreteTopology (RS.periodSubgroup X)` for
the real period subgroup (Forster 21.4(i)) AND `RS.Abel.WeakSolutionUpgrade X` is proved. A
one-line wrapper, not new mathematics. -/
theorem ofCurve_inj_of_upgrade (hupgrade : RS.Abel.WeakSolutionUpgrade X) (P : X) (h : 0 < genus X)
    [DiscreteTopology (RS.periodSubgroup X)] :
    Function.Injective (ofCurve P) :=
  ofCurve_inj' hupgrade P h

/-- `ofCurve_inj'` with the `WeakSolutionUpgrade` hypothesis **discharged**
(`UpgradeDischarge.lean`): the only remaining gates are `period-lattice-rank`'s
`[DiscreteTopology (RS.periodSubgroup X)]` and `serre-duality-tails`'s single remaining
external fact (`Function.Surjective (tailToH1 0)`). -/
theorem ofCurve_inj_of_surjective' [DecidableEq X]
    (hsurj : Function.Surjective (RS.LaurentTail.tailToH1 (0 : RS.Divisor X)))
    (P : X) (h : 0 < genus X) [DiscreteTopology (RS.periodSubgroup X)] :
    Function.Injective (ofCurve P) :=
  ofCurve_inj' (RS.Abel.weakSolutionUpgrade_of_surjective hsurj) P h

/-- The literal challenge statement, gated on discreteness (`period-lattice-rank`'s job) and
the single `serre-duality-tails` fact only. -/
theorem ofCurve_inj_of_surjective [DecidableEq X]
    (hsurj : Function.Surjective (RS.LaurentTail.tailToH1 (0 : RS.Divisor X)))
    (P : X) (h : 0 < genus X) [DiscreteTopology (RS.periodSubgroup X)] :
    Function.Injective (ofCurve P) :=
  ofCurve_inj_of_surjective' hsurj P h

end Jacobian
