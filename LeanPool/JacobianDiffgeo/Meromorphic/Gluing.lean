/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Meromorphic.OrderEval

/-!
# Sheaf gluing for `MeroGermOn` (§6.6): the Čech `H⁰` engine

Unit: meromorphic-and-divisors (`docs/design/meromorphic-and-divisors.md` §4.4, proof plan §6.6).

* `MeroGermOn.exists_glue`: compatible germ classes on an open cover glue to a class on the
  union (via the canonical repaired representative `holoRepr`, whose pointwise rigidity —
  `evalAt_restrict` — makes the gluing elementary, no coherence lemma needed).
* `MeroGermOn.glue_unique`: the glued class is unique.
-/

open scoped ContDiff Manifold
open Set Filter Topology

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace MeroGermOn

theorem exists_glue {ι : Type*} {W : ι → Set X} (hW : ∀ i, IsOpen (W i))
    (φ : ∀ i, MeroGermOn X (W i))
    (hcompat : ∀ i j, restrict (Set.inter_subset_left (s := W i) (t := W j)) (φ i) =
      restrict (Set.inter_subset_right (s := W i) (t := W j)) (φ j)) :
    ∃ Φ : MeroGermOn X (⋃ i, W i), ∀ i, restrict (Set.subset_iUnion W i) Φ = φ i := by
  classical
  have hagree : ∀ i j x, x ∈ W i ∩ W j → (φ i).holoRepr x = (φ j).holoRepr x := by
    intro i j x hx
    have hIJ : IsOpen (W i ∩ W j) := (hW i).inter (hW j)
    have e1 := evalAt_restrict (Set.inter_subset_left (s := W i) (t := W j)) hIJ (hW i) hx (φ i)
    have e2 := evalAt_restrict (Set.inter_subset_right (s := W i) (t := W j)) hIJ (hW j) hx (φ j)
    change (φ i).evalAt x = (φ j).evalAt x
    rw [← e1, ← e2, hcompat i j]
  set F : X → ℂ := fun x => if h : ∃ k, x ∈ W k then (φ h.choose).holoRepr x else 0 with hF_def
  have hFeq : ∀ i x, x ∈ W i → F x = (φ i).holoRepr x := by
    intro i x hx
    have hex : ∃ k, x ∈ W k := ⟨i, hx⟩
    change (if h : ∃ k, x ∈ W k then (φ h.choose).holoRepr x else 0) = (φ i).holoRepr x
    rw [dif_pos hex]
    exact hagree hex.choose i x ⟨hex.choose_spec, hx⟩
  have hmerF : MeromorphicOnX F (⋃ i, W i) := by
    intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    have hWimem : W i ∈ 𝓝[≠] x := mem_nhdsWithin_of_mem_nhds ((hW i).mem_nhds hxi)
    have heq : (φ i).holoRepr =ᶠ[𝓝[≠] x] F :=
      Filter.eventuallyEq_of_mem hWimem (fun y hy => (hFeq i y hy).symm)
    exact MeromorphicAtX.congr ((meromorphicOnX_holoRepr (hW i) (φ i)) x hxi) heq
  refine ⟨mk F hmerF, fun i => ?_⟩
  rw [restrict_mk, ← mk_holoRepr (hW i) (φ i)]
  -- `mk_eq_mk` as an `iff` applied with `refine`: rewriting cannot match its pattern against
  -- the `mk` proof arguments produced above
  refine mk_eq_mk.mpr ?_
  rw [eventuallyEq_codiscreteWithin_iff_of_isOpen (hW i)]
  intro x hx
  exact Filter.eventuallyEq_of_mem (mem_nhdsWithin_of_mem_nhds ((hW i).mem_nhds hx))
    (fun y hy => hFeq i y hy)

theorem glue_unique {ι : Type*} {W : ι → Set X} (hW : ∀ i, IsOpen (W i))
    {Φ Ψ : MeroGermOn X (⋃ i, W i)}
    (h : ∀ i, restrict (Set.subset_iUnion W i) Φ = restrict (Set.subset_iUnion W i) Ψ) :
    Φ = Ψ := by
  have hUopen : IsOpen (⋃ i, W i) := isOpen_iUnion hW
  rw [← mk_holoRepr hUopen Φ, ← mk_holoRepr hUopen Ψ, mk_eq_mk,
    eventuallyEq_codiscreteWithin_iff_of_isOpen hUopen]
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  have e1 := holoRepr_restrict (Set.subset_iUnion W i) (hW i) hUopen Φ
  have e2 := holoRepr_restrict (Set.subset_iUnion W i) (hW i) hUopen Ψ
  have heqOn : Set.EqOn Φ.holoRepr Ψ.holoRepr (W i) := fun y hy => by
    rw [← e1 hy, ← e2 hy, h i]
  exact Filter.eventuallyEq_of_mem (mem_nhdsWithin_of_mem_nhds ((hW i).mem_nhds hxi)) heqOn

end MeroGermOn

end RS
