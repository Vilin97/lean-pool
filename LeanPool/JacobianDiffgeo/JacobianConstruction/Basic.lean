/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.JacobianConstruction.Periods
import LeanPool.JacobianDiffgeo.JacobianConstruction.ULift

/-!
# `Jac₀`, `Jacobian`, and the challenge instance assembly (CC9, §2–§9)

Unit: jacobian-construction. This is the unit's centerpiece file: it defines the challenge's
`Jacobian` type exactly at its root-level signature (`docs/Jacobian_challenge.lean:58-62`) via the
`ULift` shell (§2) around the honest `Type 0` quotient `Jac₀` (§3), and assembles every instance
that is available *now* (no hypotheses beyond the standing Riemann-surface ones) plus every
instance that is available *given* period-lattice-rank's discreteness/full-rank hooks — see the
LEDGER at the bottom of this file's docstring.

* `RS.Jac₀ X : Type` — `(Fin (genus X) → ℂ) ⧸ (periodSubgroup X).topologicalClosure`, an `abbrev`
  so that every `Torus.lean` instance for `V ⧸ L` (`V := Fin (genus X) → ℂ`,
  `L := (periodSubgroup X).topologicalClosure`) transfers to it by instance search alone.
* `Jacobian (X : Type u) [...] : Type u := ULift.{u} (RS.Jac₀ X)` — an `abbrev` for the same
  reason, at `ULift.lean`'s level.

## Instance ledger

| Instance | Available | Hypothesis |
|---|---|---|
| `AddCommGroup (Jacobian X)` | **now** | none |
| `TopologicalSpace (Jacobian X)` | **now** | none |
| `T2Space (Jacobian X)` | **now**, every genus incl. `g = 0` (§3, the closure trick) | none |
| `ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)` | gated | `[DiscreteTopology (periodSubgroup
X).topologicalClosure]` |
| `IsManifold 𝓘(ℂ, Fin (genus X) → ℂ) ω (Jacobian X)` | gated | same as above |
| `LieAddGroup 𝓘(ℂ, Fin (genus X) → ℂ) ω (Jacobian X)` | gated | same as above |
| `CompactSpace (Jacobian X)` | gated | the above *plus* `[IsZLattice ℝ (periodSubgroup
X).topologicalClosure.toIntSubmodule]` |

The gated instances are genuine (`Prop`-valued or data) instances with typeclass *hypotheses* —
not sorries. Once period-lattice-rank registers `DiscreteTopology (periodSubgroup
X).topologicalClosure`
(and, for compactness, the `IsZLattice` full-rank fact) as instances for the actual period
subgroup of a given `X`, Lean's instance search discharges all four automatically; nothing further
needs to change here.
-/

open scoped ContDiff Manifold

universe u

noncomputable section

namespace RS

variable (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The `Type 0` core of the Jacobian: the honest quotient construction, before the `ULift`
shell. An `abbrev` so every `Torus.lean` fact for `V ⧸ L` (instantiated at
`V := Fin (genus X) → ℂ`, `L := (periodSubgroup X).topologicalClosure`) applies to it directly,
via instance search / definitional unfolding, with no extra glue code. -/
abbrev Jac₀ : Type := (Fin (genus X) → ℂ) ⧸ (periodSubgroup X).topologicalClosure

/-- Bridge between `AddSubgroup`-level and `Submodule ℤ`-level discreteness (needed since
`Torus.compactSpace_torus` is stated for a `Submodule ℤ V`, while the `ChartedSpace`/`IsManifold`/
`LieAddGroup` hooks are stated for the `AddSubgroup` directly): the underlying carrier sets agree
(`AddSubgroup.coe_toIntSubmodule`), so the two subtypes are homeomorphic. -/
instance discreteTopology_toIntSubmodule {V : Type*} [NormedAddCommGroup V]
    (S : AddSubgroup V) [DiscreteTopology S] : DiscreteTopology S.toIntSubmodule := by
  have h : (S.toIntSubmodule : Set V) = (S : Set V) := AddSubgroup.coe_toIntSubmodule S
  exact (Homeomorph.setCongr h).discreteTopology_iff.2 ‹DiscreteTopology S›

end RS

/-- The Jacobian of a compact Riemann surface (`docs/Jacobian_challenge.lean:58-62`). Defined via
the `ULift` shell around `RS.Jac₀ X`, matching the challenge's universe-polymorphic signature
(`Jacobian` must have type `Type u` for *every* `u`, but the honest quotient construction only
ever lives in `Type 0` — see this unit's design doc §2). An `abbrev`, for the same
instance-transfer reason as `RS.Jac₀`. -/
abbrev Jacobian (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Type u := ULift.{u} (RS.Jac₀ X)

namespace Jacobian

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Unconditional instances (§3): no discreteness or rank input needed at all -/

instance : AddCommGroup (Jacobian X) := inferInstance

instance : TopologicalSpace (Jacobian X) := inferInstance

/-- Hausdorff for **every** `X`, including `genus X = 0` — the closure trick (§3), no
discreteness needed. -/
instance : T2Space (Jacobian X) := inferInstance

/-- Sanity check (design §12, R5): at genus `0`, `Fin (genus X) → ℂ = Fin 0 → ℂ` is the zero
module, so `Jacobian X` is (honestly, through the same generic construction, no special-cased
vacuous instance) a one-point space. -/
example (h : genus X = 0) : Subsingleton (Jacobian X) := by
  have hsub : Subsingleton (Fin (genus X) → ℂ) := by rw [h]; infer_instance
  have hsurj : Function.Surjective
      (fun z => ULift.up (QuotientAddGroup.mk z) : (Fin (genus X) → ℂ) → Jacobian X) := by
    intro q
    obtain ⟨z, hz⟩ := QuotientAddGroup.mk_surjective q.down
    exact ⟨z, ULift.ext _ _ hz⟩
  exact hsurj.subsingleton

/-! ### Gated instances (§4–§6): hooks for period-lattice-rank -/

instance instChartedSpace [DiscreteTopology (RS.periodSubgroup X).topologicalClosure] :
    ChartedSpace (Fin (genus X) → ℂ) (Jacobian X) := inferInstance

instance instIsManifold [DiscreteTopology (RS.periodSubgroup X).topologicalClosure] :
    IsManifold 𝓘(ℂ, Fin (genus X) → ℂ) ω (Jacobian X) := inferInstance

instance instLieAddGroup [DiscreteTopology (RS.periodSubgroup X).topologicalClosure] :
    LieAddGroup 𝓘(ℂ, Fin (genus X) → ℂ) ω (Jacobian X) := inferInstance

/-- Compactness needs the *full-rank* fact (`IsZLattice`) on top of discreteness. -/
instance instCompactSpace [DiscreteTopology (RS.periodSubgroup X).topologicalClosure]
    [IsZLattice ℝ (RS.periodSubgroup X).topologicalClosure.toIntSubmodule] :
    CompactSpace (Jacobian X) := by
  have := RS.discreteTopology_toIntSubmodule (RS.periodSubgroup X).topologicalClosure
  have : CompactSpace (RS.Jac₀ X) := by
    have h := RS.compactSpace_torus (RS.periodSubgroup X).topologicalClosure.toIntSubmodule
    rwa [AddSubgroup.toIntSubmodule_toAddSubgroup] at h
  infer_instance

end Jacobian

end
