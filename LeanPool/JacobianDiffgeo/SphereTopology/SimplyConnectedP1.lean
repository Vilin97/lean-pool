/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.ProjectiveLine
import LeanPool.JacobianDiffgeo.Path
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# `SimplyConnectedSpace (OnePoint ℂ)` (CC-sphere-topology, design §2)

Unit: sphere-topology (`docs/design/sphere-topology.md` §2). No van Kampen: `OnePoint ℂ`'s two
polar caps `{∞}ᶜ`/`{↑0}ᶜ` are each homeomorphic to `ℂ` (hence simply connected), and the
paths-and-integrals unit's loop-perturbation lemma `RS.Loop.exists_homotopic_avoiding` pushes any
based loop off whichever of `∞`/`↑0` is NOT its basepoint, landing it inside one of the two simply
connected caps.

**Note on `RS.Loop.exists_homotopic_avoiding`**: this file was written and compiled against that
lemma's *stated* signature while `Jacobian/Path/Perturb.lean` still carried one documented
placeholder step upstream (the general multi-chart induction, design risk R4 of
paths-and-integrals). That placeholder has since been resolved upstream (see `docs/build-log.md`,
"Perturb.lean FIXED"), so this file now consumes a fully proved lemma; nothing here needed to
change.

Main declarations:
* `RS.SphereTopology.isSimplyConnected_compl_infty`/`isSimplyConnected_compl_coeZero`.
* `instance : PathConnectedSpace (OnePoint ℂ)`.
* `RS.SphereTopology.simplyConnectedSpace_onePoint` (the headline instance).
* `RS.SphereTopology.simplyConnectedSpace_of_homeoOnePoint` (homeomorphism transfer).
* `RS.SphereTopology.simplyConnectedSpace_sphere` (the challenge sphere model).
-/

open scoped ContDiff Manifold OnePoint
open Set Topology OnePoint RS RS.P1

noncomputable section

namespace RS.SphereTopology

/-- Both "polar caps" of the two-chart atlas are simply connected: they are each homeomorphic to
`ℂ` (contractible), via the open embedding `(↑) : ℂ → OnePoint ℂ` for `{∞}ᶜ`. -/
theorem isSimplyConnected_compl_infty : IsSimplyConnected ({(∞ : OnePoint ℂ)}ᶜ) := by
  have hu : IsSimplyConnected (Set.univ : Set ℂ) :=
    (Homeomorph.Set.univ ℂ).toHomotopyEquiv.simplyConnectedSpace
  have him := (isOpenEmbedding_coe.isEmbedding.isSimplyConnected_image
    (s := (Set.univ : Set ℂ))).mpr hu
  rw [Set.image_univ] at him
  rwa [compl_infty]

/-- The other polar cap, `{↑0}ᶜ`, is simply connected too (feeds the `x = ∞` case of the
basepoint split), via `inversionHomeomorph` swapping `∞ ↔ ↑0`. -/
theorem isSimplyConnected_compl_coeZero :
    IsSimplyConnected ({((0 : ℂ) : OnePoint ℂ)}ᶜ) := by
  have heq : ({((0 : ℂ) : OnePoint ℂ)}ᶜ : Set (OnePoint ℂ)) =
      inversionHomeomorph ⁻¹' ({(∞ : OnePoint ℂ)}ᶜ) := by
    rw [Set.preimage_compl]
    congr 1
    ext p
    simp only [Set.mem_singleton_iff, Set.mem_preimage, inversionHomeomorph_apply,
      ← inversion_eq_infty_iff, eq_comm]
  rw [heq]
  exact (Homeomorph.isSimplyConnected_preimage inversionHomeomorph).mpr
      isSimplyConnected_compl_infty

/-- `OnePoint ℂ` is path connected (local path-connectedness transports through the two-chart
atlas from `ℂ`'s local convexity, combined with the existing `ConnectedSpace` instance). -/
instance : PathConnectedSpace (OnePoint ℂ) := by
  have : LocallyPathConnectedSpace (OnePoint ℂ) :=
    ChartedSpace.locallyPathConnectedSpace ℂ (OnePoint ℂ)
  exact PathConnectedSpace.of_locallyPathConnectedSpace

/-- **The headline of this file**: no van Kampen, no universal cover — assembled from the
perturbation lemma + the two polar-cap facts above. -/
instance simplyConnectedSpace_onePoint : SimplyConnectedSpace (OnePoint ℂ) := by
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨inferInstance, fun x γ => ?_⟩
  by_cases hx : x = (∞ : OnePoint ℂ)
  · subst hx
    obtain ⟨γ', hγγ', hdisj⟩ := RS.Loop.exists_homotopic_avoiding γ
      (S := ({((0 : ℂ) : OnePoint ℂ)} : Set (OnePoint ℂ))) (Set.finite_singleton _) (by simp)
    have hmem : ∀ t, γ' t ∈ ({((0 : ℂ) : OnePoint ℂ)}ᶜ : Set (OnePoint ℂ)) := fun t =>
      Set.disjoint_left.mp hdisj (Set.mem_range_self t)
    obtain ⟨F, -⟩ := (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp
      isSimplyConnected_compl_coeZero).2 _ γ' hmem
    exact hγγ'.trans ⟨F⟩
  · obtain ⟨γ', hγγ', hdisj⟩ := RS.Loop.exists_homotopic_avoiding γ
      (S := ({(∞ : OnePoint ℂ)} : Set (OnePoint ℂ))) (Set.finite_singleton _) (by simpa using hx)
    have hmem : ∀ t, γ' t ∈ ({(∞ : OnePoint ℂ)}ᶜ : Set (OnePoint ℂ)) := fun t =>
      Set.disjoint_left.mp hdisj (Set.mem_range_self t)
    obtain ⟨F, -⟩ := (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp
      isSimplyConnected_compl_infty).2 _ γ' hmem
    exact hγγ'.trans ⟨F⟩

/-- Homeomorphism transfer (generic; consumed by `Headline.lean` and anything producing
`X ≃ₜ OnePoint ℂ`). -/
theorem simplyConnectedSpace_of_homeoOnePoint {X : Type*} [TopologicalSpace X]
    (e : X ≃ₜ OnePoint ℂ) : SimplyConnectedSpace X :=
  e.toHomotopyEquiv.simplyConnectedSpace

/-- Same fact stated for the literal challenge sphere type, for convenience/reuse. -/
instance simplyConnectedSpace_sphere :
    SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  simplyConnectedSpace_of_homeoOnePoint RS.P1.homeoSphere.symm

end RS.SphereTopology
