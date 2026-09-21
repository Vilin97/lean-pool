/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Tactic
import LeanPool.NandakumarRamanaRao.NRR.ConvexBody

/-!
# `NRR.ConfigurationSpace` — configurations of distinct labelled sites

`Config n` is the subtype of injective maps `Fin n → Plane`. Its topology is induced by the point
map, and permutations act by precomposition with `σ.symm`. The action is continuous and free.
-/

open NRR

namespace NRR

/-- **Configuration space** of `n` distinct labelled points in the plane. -/
def Config (n : ℕ) : Type := {p : Fin n → E2 // Function.Injective p}

namespace Config

/-- The underlying point map of a configuration. -/
def pts {n : ℕ} (p : Config n) : Fin n → E2 := p.1

end Config

/-- **Metric on configuration space**: the metric induced by the point map `Config.pts` from
the finite product `Fin n → E2`.  Its associated topology is definitionally the same as the
subspace topology, since `Config.pts = Subtype.val`. -/
noncomputable instance (n : ℕ) : MetricSpace (Config n) :=
  MetricSpace.induced Config.pts (fun _ _ h => Subtype.ext h) inferInstance

namespace Config

/-- The metric topology on `Config n` is definitionally the topology induced by the point map
`Config.pts`; equivalently, the subspace topology from `Fin n → E2`. -/
theorem topology_eq_induced (n : ℕ) :
    (inferInstance : TopologicalSpace (Config n)) =
      TopologicalSpace.induced Config.pts inferInstance := rfl

/-- The underlying point map of a configuration, as a bundled function. Compatibility alias of
`Config.pts`. -/
def toFun {n : ℕ} (s : Config n) : Fin n → E2 := s.pts

@[simp] theorem toFun_apply {n : ℕ} (s : Config n) (i : Fin n) : s.toFun i = s.pts i := rfl

/-- The point map of a configuration is injective. -/
theorem injective {n : ℕ} (s : Config n) : Function.Injective s.pts := s.2

/-- **Injectivity accessor for a configuration.** A configuration `s : Config n` bundles a site
map `s.pts` together with a proof that it is injective; this exposes that proof under the name
`injective_pts`, matching the requested configuration API. -/
theorem injective_pts {n : ℕ} (s : Config n) : Function.Injective s.pts := s.2

/-- The projection `Config.pts` is continuous for the induced topology (the induced-topology
domain theorem). -/
theorem continuous_pts {n : ℕ} : Continuous fun s : Config n => s.pts :=
  continuous_induced_dom

/-- **Relabelling of a configuration.** For a permutation `σ : Equiv.Perm (Fin n)` and a
configuration `s : Config n`, the relabelled configuration `Config.relabel σ s` is obtained by
precomposing the point map with `σ.symm`, i.e. `(Config.relabel σ s).pts i = s.pts (σ.symm i)`.
This `σ.symm` convention is fixed for the remainder of the current development. -/
def relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Config n) : Config n :=
  ⟨fun i => s.pts (σ.symm i), s.injective_pts.comp σ.symm.injective⟩

@[simp] theorem relabel_pts {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Config n) (i : Fin n) :
    (relabel σ s).pts i = s.pts (σ.symm i) := rfl

@[simp] theorem relabel_one {n : ℕ} (s : Config n) : relabel 1 s = s := by
  apply Subtype.ext
  funext i
  rfl

theorem relabel_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (s : Config n) :
    relabel (σ * τ) s = relabel σ (relabel τ s) := by
  apply Subtype.ext
  funext i
  simp only [relabel, pts]
  rfl

/-- The `Sₙ`‑action `σ • s := Config.relabel σ s` on the configuration space, by relabelling
via precomposition with `σ.symm`. -/
instance permAction (n : ℕ) : MulAction (Equiv.Perm (Fin n)) (Config n) where
  smul σ s := relabel σ s
  one_smul s := relabel_one s
  mul_smul σ τ s := relabel_mul σ τ s

@[simp] theorem smul_def {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Config n) :
    σ • s = relabel σ s := rfl

/-- Relabelling is continuous for the topology induced by the point map. -/
theorem continuous_relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Continuous fun s : Config n => relabel σ s := by
  rw [continuous_induced_rng]
  exact continuous_pi fun i => (continuous_apply (σ.symm i)).comp continuous_pts

/-- **Freeness of relabelling.** If relabelling a configuration by `σ` leaves it unchanged,
then `σ` is the identity permutation. -/
theorem relabel_eq_self_imp {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Config n)
    (h : Config.relabel σ s = s) : σ = 1 := by
  have hpt : ∀ i, σ.symm i = i := by
    intro i
    have hi : s.pts (σ.symm i) = s.pts i := by
      rw [← relabel_pts σ s i, h]
    exact s.injective_pts hi
  apply Equiv.ext
  intro i
  show σ i = i
  rw [← hpt (σ i), Equiv.symm_apply_apply]

/-- **Freeness of relabelling, biconditional form.** Relabelling a configuration by `σ` leaves
it unchanged iff `σ` is the identity permutation. -/
theorem relabel_eq_self_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Config n) :
    Config.relabel σ s = s ↔ σ = 1 := by
  constructor
  · exact relabel_eq_self_imp σ s
  · rintro rfl
    exact relabel_one s

/-- **Freeness for the `MulAction`.** Wrapper over `Config.relabel_eq_self_imp`: if the
`Sₙ`‑action fixes a configuration then the permutation is the identity. -/
theorem smul_eq_self_imp {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Config n)
    (h : σ • s = s) : σ = 1 :=
  relabel_eq_self_imp σ s (by simpa [smul_def] using h)

/-- The `Sₙ`‑action on the configuration space is free. -/
theorem action_free (n : ℕ) {σ : Equiv.Perm (Fin n)} {p : Config n} (h : σ • p = p) : σ = 1 :=
  smul_eq_self_imp σ p h

/-- The `Sₙ`‑action is continuous (by homeomorphisms). -/
theorem continuous_smul (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Continuous (fun p : Config n => σ • p) := continuous_relabel σ

end Config

end NRR
