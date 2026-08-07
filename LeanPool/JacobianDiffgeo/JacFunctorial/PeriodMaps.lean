/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.JacFunctorial.PullbackIntegral
import LeanPool.JacobianDiffgeo.JacobianConstruction

/-!
# Period-space plumbing and the pushforward map (jacobian-functoriality §8, pushforward half)

Unit: jacobian-functoriality. `RS.periodCoordEquiv` (the `dualMap`/`Basis.dualBasis.equivFun`
coordinatization of the ambient period space, spiked in `scratch_jfun.lean`), `pushforwardT`
(the induced `ℂ`-linear map on period spaces from `Form1.pullback`), and
`periodSubgroup_le_comap_pushforwardT` (`hT` for the pushforward direction — exact membership,
no closure/density needed, via `pathIntegral_pullback` + basepoint-flexible
`periodVector_mem_periodSubgroup`). Assembles `Jacobian.pushforward` via `Jacobian.inducedHom`.

**Scope note**: only the *pushforward* direction is built in this unit (see the root file's
LEDGER for the pullback-direction gap: `Form1.trace`'s branch-point analyticity and the
trace–path-integral relation are not completed, so `pullbackT`/`Jacobian.pullback`/
`pushforward_pullback` cannot be assembled here).
-/

open scoped ContDiff Manifold
open IsManifold Module

noncomputable section

namespace RS

universe u

variable (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The `dualMap`/`Basis.dualBasis.equivFun` coordinatization of the ambient period space: a
period vector `periodVector (basis X) γ` is exactly `pathIntegralₗ γ` read in `(basis X)`'s
dual-basis coordinates (§8.1, spiked in `scratch_jfun.lean`). -/
noncomputable def periodCoordEquiv : Module.Dual ℂ (RS.Form1 X) ≃ₗ[ℂ] (Fin (genus X) → ℂ) :=
  (RS.basis X).dualBasis.equivFun

omit [ConnectedSpace X] in
theorem periodCoordEquiv_apply (φ : Module.Dual ℂ (Form1 X)) (i : Fin (genus X)) :
    periodCoordEquiv X φ i = φ (basis X i) :=
  (basis X).dualBasis_equivFun φ i

variable {X}
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- The induced `ℂ`-linear map on period spaces, from `Form1.pullback f hf`'s `dualMap`
(contravariant: `Form1 Y →ₗ Form1 X` transposes to `Dual(Form1 X) →ₗ Dual(Form1 Y)`, exactly the
pushforward direction). -/
noncomputable def pushforwardT (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (genus X) → ℂ) →ₗ[ℂ] (Fin (genus Y) → ℂ) :=
  (periodCoordEquiv Y).toLinearMap ∘ₗ
    ((Form1.pullback f hf).dualMap ∘ₗ (periodCoordEquiv X).symm.toLinearMap)

omit [ConnectedSpace X] [ConnectedSpace Y] in
/-- The pushforward map on period vectors, computed at a based loop: `pushforwardT` sends the
period vector of `γ` to the period vector of its image loop `γ.map hf.continuous`
(`pathIntegral_pullback`'s naturality, transported through the coordinatization). -/
theorem pushforwardT_periodVector (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) {x : X}
    (γ : Path x x) :
    pushforwardT f hf (periodVector (basis X) γ) = periodVector (basis Y) (γ.map hf.continuous) :=
        by
  have hsymm : (periodCoordEquiv X).symm (periodVector (basis X) γ) = pathIntegralₗ γ := by
    apply (periodCoordEquiv X).injective
    rw [(periodCoordEquiv X).apply_symm_apply]
    funext j
    rw [periodCoordEquiv_apply]
    rfl
  funext i
  change periodCoordEquiv Y ((Form1.pullback f hf).dualMap
      ((periodCoordEquiv X).symm (periodVector (basis X) γ))) i = _
  rw [hsymm, periodCoordEquiv_apply, LinearMap.dualMap_apply]
  change pathIntegral γ (Form1.pullback f hf (basis Y i)) = periodVector (basis Y)
      (γ.map hf.continuous) i
  rw [pathIntegral_pullback hf γ (basis Y i)]
  rfl

/-- `hT` for the pushforward direction (§8.2 — exact containment, no closure/density needed). -/
theorem periodSubgroup_le_comap_pushforwardT (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    RS.periodSubgroup X ≤ (RS.periodSubgroup Y).topologicalClosure.comap
      (pushforwardT f hf).toAddMonoidHom := by
  rw [periodSubgroup, AddSubgroup.closure_le]
  rintro v ⟨γ, rfl⟩
  change pushforwardT f hf (periodVector (basis X) γ) ∈ (periodSubgroup Y).topologicalClosure
  rw [pushforwardT_periodVector]
  exact AddSubgroup.le_topologicalClosure (periodSubgroup Y)
    (periodVector_mem_periodSubgroup (γ.map hf.continuous))

section SameUniverse

/- **Universe warning** (hard-won): `Jacobian.inducedHom` (`JacobianConstruction/Functorial.lean`)
is declared for `X Y : Type u` in the SAME universe. Instantiating it with `X : Type*`/`Y : Type*`
(distinct universe metavariables) does not fail cleanly — the elaborator grinds through
`ULift`/quotient defeq for tens of minutes before hitting the heartbeat limit. Everything below
therefore fixes ONE universe `u` for both surfaces, matching `Functorial.lean`'s own convention.
(A cross-universe generalization is possible upstream — the two `ULift` shells can lift to
different universes — but is `jacobian-construction`'s call, not this unit's.) -/
variable {X' : Type u} [TopologicalSpace X'] [T2Space X'] [CompactSpace X'] [ConnectedSpace X']
  [ChartedSpace ℂ X'] [IsManifold 𝓘(ℂ) ω X']
variable {Y' : Type u} [TopologicalSpace Y'] [T2Space Y'] [CompactSpace Y'] [ConnectedSpace Y']
  [ChartedSpace ℂ Y'] [IsManifold 𝓘(ℂ) ω Y']

/-- **`Jacobian.pushforward` (§8.4)**: the pushforward map between Jacobians associated to a
holomorphic map of the underlying curves. -/
noncomputable def Jacobian.pushforward (f : X' → Y') (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian X' →ₜ+ Jacobian Y' :=
  Jacobian.inducedHom (periodSubgroup_le_comap_pushforwardT f hf)

end SameUniverse

end RS

end
