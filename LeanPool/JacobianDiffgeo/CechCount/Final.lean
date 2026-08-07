/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.CechCount.Count
import LeanPool.JacobianDiffgeo.Abel
import LeanPool.JacobianDiffgeo.PeriodLattice

/-!
# The final gate, closed: ungated exports (cechcount unit)

`Count.lean`'s `RS.cechCount` (`dim H¹(𝒪_X) ≤ genus X`) discharges — through the BUILT
equivalence `RS.Abel.tailToH1_zero_surjective_iff_finrank_le` — the single fact every remaining
gate of the project was reduced to. This file records the ungated finals:

* `RS.tailToH1_zero_surjective` — surjectivity of the Laurent-tail comparison at `D = 0`
  (the surjectivity half of Serre duality for `𝒪_X`).
* `RS.finrank_H1_zero_eq_genus` — `dim_ℂ H¹(X, 𝒪_X) = genus X` (the Čech identity the
  cech-h1-genus unit deferred).
* `RS.Abel.weakSolutionUpgrade_final : WeakSolutionUpgrade X` and
  `RS.Abel.weakSolutionUpgradeFinset_final` (via the built `…_of_surjective` discharges).
* `RS.discretenessHyp_final : RS.DiscretenessHyp X` — the period-lattice gate.
* The global instances `DiscreteTopology (RS.periodSubgroup X)`,
  `DiscreteTopology (RS.periodSubgroup X).topologicalClosure` and
  `IsZLattice ℝ (RS.periodSubgroup X).topologicalClosure.toIntSubmodule`
  (the exact recorded final-assembly shapes from `Jacobian/PeriodLattice.lean`).
* `RS.finrank_int_periodSubgroup_final` — the period lattice has `ℤ`-rank `2·genus X`.
* `Jacobian.ofCurve_inj` — the Abel–Jacobi map is injective for `0 < genus X`,
  with no remaining hypotheses (the challenge's `ofCurve_inj`, ungated).
-/

open scoped ContDiff Manifold


namespace RS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **The single remaining gate of the project, closed**: the Laurent-tail comparison map into
Čech `H¹` is surjective at `D = 0` (surjectivity half of Serre duality for `𝒪_X`), by
`RS.cechCount` through the built dimension-count equivalence. -/
theorem tailToH1_zero_surjective [DecidableEq X] :
    Function.Surjective (RS.LaurentTail.tailToH1 (0 : RS.Divisor X)) :=
  RS.Abel.tailToH1_zero_surjective_iff_finrank_le.mpr cechCount

/-- The Čech identity `dim_ℂ H¹(X, 𝒪_X) = genus X` (the fact the cech-h1-genus unit had to
defer), now unconditional. -/
theorem finrank_H1_zero_eq_genus :
    Module.finrank ℂ (RS.Cech.H1 (0 : RS.Divisor X)) = genus X := by
  classical
  have e1 := RS.LaurentTail.H1Tail.equivOfSurjective (0 : RS.Divisor X)
    tailToH1_zero_surjective
  rw [← e1.finrank_eq]
  exact RS.TailDuality.h1T_zero_eq_genus

namespace Abel

/-- **The weak-solution upgrade, ungated** (Forster §20's Abel-necessity input). -/
theorem weakSolutionUpgrade_final : RS.Abel.WeakSolutionUpgrade X := by
  classical
  exact RS.Abel.weakSolutionUpgrade_of_surjective tailToH1_zero_surjective

/-- **The Finset weak-solution upgrade, ungated** (the `k`-point Abel sufficiency input). -/
theorem weakSolutionUpgradeFinset_final {ι : Type*} [Fintype ι] :
    RS.Abel.WeakSolutionUpgradeFinset X ι := by
  classical
  exact RS.Abel.weakSolutionUpgradeFinset_of_surjective tailToH1_zero_surjective

end Abel

/-- **The period-lattice discreteness gate, discharged.** -/
theorem discretenessHyp_final : RS.DiscretenessHyp X := by
  classical
  intro S
  exact RS.Abel.weakSolutionUpgradeFinset_of_surjective tailToH1_zero_surjective

/-- The period subgroup is discrete (Forster 21.4), globally as an instance. -/
instance : DiscreteTopology (RS.periodSubgroup X) :=
  RS.discreteTopology_periodSubgroup discretenessHyp_final

/-- The recorded final-assembly instance (`Jacobian/PeriodLattice.lean` discharge shape). -/
instance : DiscreteTopology (RS.periodSubgroup X).topologicalClosure :=
  RS.discreteTopology_periodSubgroup_topologicalClosure discretenessHyp_final

/-- The recorded final-assembly instance (`Jacobian/PeriodLattice.lean` discharge shape): the
closed period subgroup is a genuine `ℤ`-lattice in `ℂ^g`. -/
instance : IsZLattice ℝ (RS.periodSubgroup X).topologicalClosure.toIntSubmodule :=
  RS.isZLattice_periodSubgroup_topologicalClosure discretenessHyp_final

/-- The period lattice has `ℤ`-rank `2·genus X` (Forster 21.4's "real basis of rank 2g"),
ungated. -/
theorem finrank_int_periodSubgroup_final :
    Module.finrank ℤ (RS.periodSubgroup X).topologicalClosure.toIntSubmodule = 2 * genus X :=
  RS.finrank_int_periodSubgroup discretenessHyp_final

end RS

namespace Jacobian

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **The Abel–Jacobi map is injective for positive genus** — the challenge's `ofCurve_inj`,
with every gate discharged (no upgrade hypothesis, no discreteness instance argument). -/
theorem ofCurve_inj (P : X) (h : 0 < genus X) :
    Function.Injective (Jacobian.ofCurve P) :=
  Jacobian.ofCurve_inj_of_upgrade RS.Abel.weakSolutionUpgrade_final P h

end Jacobian
