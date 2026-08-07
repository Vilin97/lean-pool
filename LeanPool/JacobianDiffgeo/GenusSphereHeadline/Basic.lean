/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.RiemannRoch
import LeanPool.JacobianDiffgeo.SphereTopology
import LeanPool.JacobianDiffgeo.ProperDegree

/-!
# genus-zero-headline (#30): `genus X = 0 ↔ X ≃ₜ S²`

Unit: genus-zero-headline (`clean_room_blueprint.md`, `docs/design/serre-duality-tails.md` §9.1's
"genus-0 single-simple-pole consequence" + `docs/design/proper-map-degree.md`'s own consumer
note). Assembles the two already-built halves:

* **Backward** (`X ≃ₜ S² ⇒ genus X = 0`): `RS.SphereTopology.genus_eq_zero_of_homeo_sphere`
  (`sphere-topology`, BUILT — pure topology: any space homeomorphic to the sphere is simply
  connected, hence has vanishing holomorphic 1-forms).
* **Forward** (`genus X = 0 ⇒ X ≃ₜ S²`): riemann-roch's `riemann_inequality` at `D := single P 1`
  under `genus X = 0` forces `l(single P 1) ≥ 2 > 1 = l(0)`, so `L(0) = span{1}` is a PROPER
  subspace of `L(single P 1)` (`SetLike.exists_of_lt`, the `CanonicalForms/Existence.lean`
  pattern) — any witness `φ` outside `L(0)` has `φ.ord ≥ -1` at `P`, `φ.ord ≥ 0` elsewhere
  (`mem_linSys_iff`), and `φ.ord P < 0` (else `φ` would be holomorphic everywhere, hence in
  `L(0) = span{1}` by `linSys_zero_eq_span_one`, contradiction); combined with `φ.ord P ≥ -1` this
  forces `φ.ord P = -1` exactly — a single simple pole, no other poles. `proper-map-degree`'s
  already-built `RS.homeoSphere_of_exists_simple_pole` closes it.

## Exports

* `RS.GenusSphereHeadline.exists_simple_pole_of_genus_eq_zero` — the forward-direction finisher.
* **`genus_eq_zero_iff_homeo`** (root level, `docs/Jacobian_challenge.lean:54-56` verbatim, same
  standing variables — a direct alias target for final assembly).
-/

open scoped ContDiff Manifold

namespace RS.GenusSphereHeadline

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [CompactSpace X] [ConnectedSpace X]

/-- **The forward-direction finisher**: `genus X = 0` produces a meromorphic function with
exactly one simple pole (order `-1` at some `P`) and no other poles (order `≥ 0` elsewhere) —
`RS.homeoSphere_of_exists_simple_pole`'s exact hypothesis shape. -/
theorem exists_simple_pole_of_genus_eq_zero (hg : genus X = 0) :
    ∃ (φ : RS.Mero X) (P : X), φ.ord P = -1 ∧ ∀ x, x ≠ P → 0 ≤ φ.ord x := by
  classical
  set P : X := Classical.arbitrary X with hP_def
  set D : RS.Divisor X := Function.locallyFinsuppWithin.single P (1 : ℤ) with hD_def
  have hDdeg : D.degree = 1 := by
    rw [hD_def]
    exact Function.locallyFinsuppWithin.degree_single P 1
  have hDnn : (0 : RS.Divisor X) ≤ D := by
    rw [hD_def]
    exact Function.locallyFinsuppWithin.single_nonneg.2 (by norm_num)
  have hri := RS.riemann_inequality D
  rw [hg, hDdeg] at hri
  have hl0 : RS.l (0 : RS.Divisor X) = 1 := RS.l_zero
  have hlDnat : 2 ≤ RS.l D := by
    have h2 : (2 : ℤ) ≤ (RS.l D : ℤ) := by push_cast at hri; omega
    exact_mod_cast h2
  have hle : RS.LinSys (0 : RS.Divisor X) ≤ RS.LinSys D := RS.linSys_mono hDnn
  have hne : RS.LinSys (0 : RS.Divisor X) ≠ RS.LinSys D := fun heq => by
    have hleq : RS.l (0 : RS.Divisor X) = RS.l D := by
      change Module.finrank ℂ (RS.LinSys (0 : RS.Divisor X)) = Module.finrank ℂ (RS.LinSys D)
      rw [heq]
    rw [hl0] at hleq
    omega
  obtain ⟨φ, hφD, hφ0⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  rw [RS.linSys_zero_eq_span_one] at hφ0
  have hreg0 : ∀ x, x ≠ P → 0 ≤ φ.ord x := by
    intro x hx
    have h := RS.mem_linSys_iff.mp hφD x
    have hDx : D x = 0 := by
      rw [hD_def, Function.locallyFinsuppWithin.single_apply, if_neg hx]
    rw [hDx] at h
    simpa using h
  have hPbound : ((-1 : ℤ) : WithTop ℤ) ≤ φ.ord P := by
    have h := RS.mem_linSys_iff.mp hφD P
    have hDP : D P = 1 := by
      rw [hD_def, Function.locallyFinsuppWithin.single_apply, if_pos rfl]
    rwa [hDP] at h
  have hPneg : φ.ord P < 0 := by
    by_contra hcon
    push Not at hcon
    have hmem0 : φ ∈ RS.LinSys (0 : RS.Divisor X) := by
      rw [RS.mem_linSys_iff]
      intro x
      by_cases hxP : x = P
      · subst hxP
        simpa using hcon
      · simpa using hreg0 x hxP
    rw [RS.linSys_zero_eq_span_one] at hmem0
    exact hφ0 hmem0
  have hPnetop : φ.ord P ≠ ⊤ := by
    intro htop
    rw [htop] at hPneg
    exact (not_lt.2 le_top) hPneg
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hPnetop
  have hk1 : (-1 : ℤ) ≤ k := by
    rw [← hk] at hPbound
    exact_mod_cast hPbound
  have hk2 : k < 0 := by
    rw [← hk] at hPneg
    exact_mod_cast hPneg
  have hkeq : k = -1 := by omega
  have hpole : φ.ord P = -1 := by
    rw [← hk, hkeq]
    norm_cast
  exact ⟨φ, P, hpole, hreg0⟩

end RS.GenusSphereHeadline

/-- **The headline** (`docs/Jacobian_challenge.lean:54-56`, verbatim, standing variables): a
compact Riemann surface has genus `0` iff it is homeomorphic to the sphere. -/
theorem genus_eq_zero_iff_homeo {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    genus X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) := by
  constructor
  · intro hg
    obtain ⟨φ, P, hpole, hreg⟩ := RS.GenusSphereHeadline.exists_simple_pole_of_genus_eq_zero hg
    exact RS.homeoSphere_of_exists_simple_pole φ P hpole hreg
  · exact RS.SphereTopology.genus_eq_zero_of_homeo_sphere
