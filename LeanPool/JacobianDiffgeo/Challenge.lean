/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Forms
import LeanPool.JacobianDiffgeo.GenusSphereHeadline
import LeanPool.JacobianDiffgeo.JacobianConstruction
import LeanPool.JacobianDiffgeo.JacFunctorial
import LeanPool.JacobianDiffgeo.ProperDegree
import LeanPool.JacobianDiffgeo.CechCount

/-!
# Jacobians — the assembled challenge API

Final assembly of Kevin Buzzard's AI challenge `docs/Jacobian_challenge.lean` (v0.4): every
placeholder of the gist is discharged by the development under `Jacobian/`, with zero axioms
beyond `propext`/`Classical.choice`/`Quot.sound`.

Most gist declarations already live at their gist names (root level / `Jacobian` namespace)
inside the units that built them; this file adds ONLY what was still missing — the root-level
`Jacobian.pushforward`/`Jacobian.pullback` functorial API (the built maps live at
`RS.Jacobian.*`) — and closes with a self-auditing `GistCheck` section containing one witness
per gist item.

## Item-by-item map (gist declaration → providing declaration)

* `genus` → `genus` (`Jacobian/Forms/Genus.lean`, root, gist signature verbatim).
* `genus_eq_zero_iff_homeo` → `genus_eq_zero_iff_homeo`
  (`Jacobian/GenusSphereHeadline/Basic.lean`, root, gist statement verbatim).
* `Jacobian` → `Jacobian` (`Jacobian/JacobianConstruction/Basic.lean`, root, `Type u → Type u`
  as the gist demands; an `abbrev` — `ULift` shell around the honest `Type 0` quotient).
* `instance : AddCommGroup/TopologicalSpace/T2Space (Jacobian X)` → unconditional instances in
  `Jacobian/JacobianConstruction/Basic.lean`.
* `instance : CompactSpace/ChartedSpace/IsManifold/LieAddGroup … (Jacobian X)` → the gated
  instances of `Jacobian/JacobianConstruction/Basic.lean`, whose gates
  (`DiscreteTopology (RS.periodSubgroup X).topologicalClosure`, `IsZLattice …`) are global
  instances since `Jacobian/CechCount/Final.lean`; all fire by `inferInstance` (see `GistCheck`).
* `Jacobian.ofCurve` → `Jacobian.ofCurve`; `Jacobian.ofCurve_self` → `Jacobian.ofCurve_self`
  (`Jacobian/JacobianConstruction/OfCurve.lean`, gist names/signatures).
* `Jacobian.ofCurve_contMDiff` → `Jacobian.ofCurve_contMDiff` (same file; carries one extra
  instance-implicit `[DiscreteTopology (RS.periodSubgroup X).topologicalClosure]`, globally
  discharged — every gist-shaped use elaborates verbatim).
* `Jacobian.ofCurve_inj` → `Jacobian.ofCurve_inj` (`Jacobian/CechCount/Final.lean`),
  the exact gist name and signature `(P : X) (h : 0 < genus X) : Function.Injective (ofCurve P)`,
  hypothesis-free (the development-time gated variant lives on as
  `Jacobian.ofCurve_inj_of_upgrade` in `Jacobian/Abel/OfCurveInj.lean`).
* `Jacobian.pushforward` → **defined below** (wrapper of `RS.Jacobian.pushforward`).
* `Jacobian.pushforward_contMDiff` → **below** (from `RS.Jacobian.pushforward_contMDiff`;
  its discreteness gates are global instances, so the gist statement holds unconditionally).
* `Jacobian.pushforward_id_apply` / `Jacobian.pushforward_comp_apply` → **below**.
* `Jacobian.pullback` → **below** (wrapper of `RS.Jacobian.pullback`).
* `Jacobian.pullback_contMDiff`, `Jacobian.pullback_id_apply`, `Jacobian.pullback_comp_apply`
  → **below**.
* `ContMDiff.degree` → `ContMDiff.degree` (`Jacobian/ProperDegree/ChallengeDegree.lean`, root,
  gist signature verbatim, `f` explicit).
* `Jacobian.pushforward_pullback` → **below** (from `RS.Jacobian.pushforward_pullback`).

## Universe convention (the one deviation from the gist's variable blocks)

The gist declares `{X Y Z : Type*}` — three independent universes. `Jacobian X` is the `ULift`
shell around a `Type 0` quotient, and the underlying `Jacobian.inducedHom` substrate demands
both surfaces in ONE `Type u`: instantiating any `Jacobian X`-to-`Jacobian Y` declaration at
distinct universes does not fail cleanly but sends the elaborator into a `ULift`/quotient defeq
grind (deterministic heartbeat timeout — documented in `Jacobian/JacFunctorial.lean`'s LEDGER
and re-verified during this assembly). The functorial declarations below therefore state their
surfaces in a single shared `universe u`. This only restricts universes; every statement is
otherwise the gist's, and the (overwhelmingly common) same-universe uses — including everything
in `Type 0` — elaborate verbatim.
-/

open scoped ContDiff -- for ω notation

open scoped Manifold -- for 𝓘 notation

namespace Jacobian

universe u

-- let X be a compact Riemann surface
variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

-- and Y another one, in the same universe (see the module docstring's universe convention)
variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

variable (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)

/-- The pushforward map between Jacobians associated to a map of the underlying curves. -/
noncomputable def pushforward (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian X →ₜ+ Jacobian Y :=
  RS.Jacobian.pushforward f hf

-- pushforward is holomorphic
theorem pushforward_contMDiff :
    ContMDiff 𝓘(ℂ, Fin (genus X) → ℂ) 𝓘(ℂ, Fin (genus Y) → ℂ) ω (pushforward f hf) :=
  RS.Jacobian.pushforward_contMDiff f hf

-- functoriality
lemma pushforward_id_apply (P : Jacobian X) : pushforward id contMDiff_id P = P :=
  RS.Jacobian.pushforward_id_apply P

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]

variable (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)

-- functoriality
lemma pushforward_comp_apply (P : Jacobian X) :
    pushforward (g ∘ f) (hg.comp hf) P = pushforward g hg (pushforward f hf P) :=
  RS.Jacobian.pushforward_comp_apply f hf g hg P

/-- Pullback map between Jacobians associated to a map of the underlying curves.
Equal to the zero map if the map on curves is constant. -/
noncomputable def pullback (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian Y →ₜ+ Jacobian X :=
  RS.Jacobian.pullback f hf

-- pullback is holomorphic
theorem pullback_contMDiff :
    ContMDiff 𝓘(ℂ, Fin (genus Y) → ℂ) 𝓘(ℂ, Fin (genus X) → ℂ) ω (pullback f hf) :=
  RS.Jacobian.pullback_contMDiff f hf

-- functoriality
lemma pullback_id_apply (P : Jacobian X) : pullback id contMDiff_id P = P :=
  RS.Jacobian.pullback_id_apply P

-- functoriality
lemma pullback_comp_apply (P : Jacobian Z) :
    pullback (g.comp f) (hg.comp hf) P = pullback f hf (pullback g hg P) :=
  RS.Jacobian.pullback_comp_apply f hf g hg P

-- `ContMDiff.degree` already exists at root with the exact gist signature
-- (`Jacobian/ProperDegree/ChallengeDegree.lean`).

lemma pushforward_pullback (P : Jacobian Y) :
    pushforward f hf (pullback f hf P) = (ContMDiff.degree f hf) • P :=
  RS.Jacobian.pushforward_pullback f hf P

end Jacobian

/-!
### `GistCheck` — self-audit

One witness per declaration of `docs/Jacobian_challenge.lean`, each stated in the gist's own
shape and discharged by the providing declaration. Single-surface items use the gist's
`Type*` variables verbatim; the multi-surface functorial items share one universe (see the
module docstring).
-/

section GistCheck

universe u

-- 1. `genus` (gist line 46)
noncomputable example (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : ℕ := genus X

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

-- 2. `genus_eq_zero_iff_homeo` (gist line 54)
example : genus X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
  genus_eq_zero_iff_homeo

-- 3. `Jacobian` (gist line 61): `Type u → Type u`
noncomputable example (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Type u := Jacobian X

-- 4.–10. the seven instances (gist lines 68–89), all firing by `inferInstance`
noncomputable example : AddCommGroup (Jacobian X) := inferInstance
noncomputable example : TopologicalSpace (Jacobian X) := inferInstance
example : T2Space (Jacobian X) := inferInstance
example : CompactSpace (Jacobian X) := inferInstance
noncomputable example : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X) := inferInstance
example : IsManifold 𝓘(ℂ, Fin (genus X) → ℂ) ω (Jacobian X) := inferInstance
example : LieAddGroup 𝓘(ℂ, Fin (genus X) → ℂ) ω (Jacobian X) := inferInstance

-- 11. `Jacobian.ofCurve` (gist line 92)
noncomputable example (P : X) : X → Jacobian X := Jacobian.ofCurve P

-- 12. `Jacobian.ofCurve_contMDiff` (gist line 94)
example (P : X) : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin (genus X) → ℂ) ω (Jacobian.ofCurve P) :=
  Jacobian.ofCurve_contMDiff P

-- 13. `Jacobian.ofCurve_self` (gist line 96)
example (P : X) : Jacobian.ofCurve P P = 0 := Jacobian.ofCurve_self P

-- 14. `Jacobian.ofCurve_inj` (gist line 99)
example (P : X) (h : 0 < genus X) : Function.Injective (Jacobian.ofCurve P) :=
  Jacobian.ofCurve_inj P h

-- 23. `ContMDiff.degree` (gist line 147) — cross-universe, `f` explicit, gist signature
noncomputable example {X' : Type*} {Y' : Type*} [TopologicalSpace X'] [T2Space X']
    [CompactSpace X'] [ConnectedSpace X'] [ChartedSpace ℂ X'] [IsManifold 𝓘(ℂ) ω X']
    [TopologicalSpace Y'] [T2Space Y'] [CompactSpace Y'] [ConnectedSpace Y']
    [ChartedSpace ℂ Y'] [IsManifold 𝓘(ℂ) ω Y']
    (f : X' → Y') (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ := ContMDiff.degree f hf

end GistCheck

section GistCheckFunctorial

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
variable (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)

-- 15. `Jacobian.pushforward` (gist line 107)
noncomputable example : Jacobian X →ₜ+ Jacobian Y := Jacobian.pushforward f hf

-- 16. `Jacobian.pushforward_contMDiff` (gist line 112)
example : ContMDiff 𝓘(ℂ, Fin (genus X) → ℂ) 𝓘(ℂ, Fin (genus Y) → ℂ) ω
    (Jacobian.pushforward f hf) :=
  Jacobian.pushforward_contMDiff f hf

-- 17. `Jacobian.pushforward_id_apply` (gist line 116)
example (P : Jacobian X) : Jacobian.pushforward id contMDiff_id P = P :=
  Jacobian.pushforward_id_apply P

-- 18. `Jacobian.pushforward_comp_apply` (gist line 124)
example (P : Jacobian X) :
    Jacobian.pushforward (g ∘ f) (hg.comp hf) P
      = Jacobian.pushforward g hg (Jacobian.pushforward f hf P) :=
  Jacobian.pushforward_comp_apply f hf g hg P

-- 19. `Jacobian.pullback` (gist line 130)
noncomputable example : Jacobian Y →ₜ+ Jacobian X := Jacobian.pullback f hf

-- 20. `Jacobian.pullback_contMDiff` (gist line 135)
example : ContMDiff 𝓘(ℂ, Fin (genus Y) → ℂ) 𝓘(ℂ, Fin (genus X) → ℂ) ω
    (Jacobian.pullback f hf) :=
  Jacobian.pullback_contMDiff f hf

-- 21. `Jacobian.pullback_id_apply` (gist line 139)
example (P : Jacobian X) : Jacobian.pullback id contMDiff_id P = P :=
  Jacobian.pullback_id_apply P

-- 22. `Jacobian.pullback_comp_apply` (gist line 142)
example (P : Jacobian Z) :
    Jacobian.pullback (g.comp f) (hg.comp hf) P
      = Jacobian.pullback f hf (Jacobian.pullback g hg P) :=
  Jacobian.pullback_comp_apply f hf g hg P

-- 24. `Jacobian.pushforward_pullback` (gist line 151)
example (P : Jacobian Y) :
    Jacobian.pushforward f hf (Jacobian.pullback f hf P) = (ContMDiff.degree f hf) • P :=
  Jacobian.pushforward_pullback f hf P

end GistCheckFunctorial
