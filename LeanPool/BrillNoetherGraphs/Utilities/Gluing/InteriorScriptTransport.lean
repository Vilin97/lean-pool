/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Foundations.InducedSubgraph
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.StrongSeparator

/-!
# Transporting a local Dhar move out of an induced subgraph

A configuration picture is a firing script together with a proof that the
residual it leaves is effective.  Every picture in the library is written on
the *whole* graph, and that is why the library has no picture for a component
whose shape is understood but whose ambient graph is large: the arithmetic has
to be redone in the ambient graph.

This file removes that obstacle.  Fix a vertex set `A`.  Call a vertex
`Interior G A` when *every* ambient edge at it stays inside `A`; the vertices
of `A` that are not interior are its boundary.  The observation is:

> A firing script whose support consists of interior vertices acts on the
> ambient graph exactly as its restriction acts on the induced subgraph `G[A]`,
> and does nothing at all outside `A`.

Hence a local Dhar move performed inside `G[A]` -- subject only to the side
condition that the script vanish on the boundary of `A` -- proves the ambient
reachability statement, provided the ambient divisor is effective off `A`.
`reaches_of_induced_script` is that theorem.

## Why this is the gluing lemma

When `A` has a **single** boundary vertex `g`, the side condition costs
nothing: firing scripts matter only up to a constant, so any script may be
normalised to vanish at `g`.  That special case is exactly the vertex-wedge
delivery statement (`Utilities.OneVertexCut`, `winnable_vertexWedge_iff_exists_chipShift`),
and `reaches_of_induced_script_of_unique_boundary` states it in this language.

The general form is strictly stronger, and the strength is what pictures need:
`A` may have *any* number of boundary vertices, so the ambient graph need not
have a cut vertex at all.  A chip-free component sitting inside a
two-edge-connected ambient graph still localises, at the price of the boundary
vertices being frozen -- which, read as a divisor statement, says that a
boundary vertex may deliver into `A` only the chips it already carries.

## Layering

`Utilities` only, so every `LowGenus` configuration file may use it.
-/

namespace Utilities.Gluing

open Utilities.Certificate.StrongSeparator

universe u

variable {G : CFGraph.{u}}

/-! ## Interior vertices -/

/-- `v` is **interior** to `A` when every ambient edge at `v` has its other end
in `A`.  A script supported on interior vertices cannot be felt outside `A`. -/
def Interior (G : CFGraph.{u}) (A : Finset G.V) (v : G.V) : Prop :=
  ∀ w : G.V, w ∉ A → num_edges G v w = 0

/-- An interior vertex is invisible from outside `A`. -/
theorem num_edges_eq_zero_of_interior {A : Finset G.V} {u w : G.V}
    (hu : Interior G A u) (hw : w ∉ A) : num_edges G w u = 0 := by
  rw [num_edges_symmetric]
  exact hu w hw

/-! ## Extending a script from the induced subgraph -/

/-- Extend a script on `G[A]` by zero. -/
noncomputable def extendScript (G : CFGraph.{u}) (A : Finset G.V) (hA : A.Nonempty)
    (t : firing_script (inducedSubgraph G A hA)) : firing_script G :=
  fun v => if h : v ∈ A then t ⟨v, h⟩ else 0

@[simp] theorem extendScript_of_mem {A : Finset G.V} {hA : A.Nonempty}
    (t : firing_script (inducedSubgraph G A hA)) {v : G.V} (hv : v ∈ A) :
    extendScript G A hA t v = t ⟨v, hv⟩ := dif_pos hv

@[simp] theorem extendScript_of_not_mem {A : Finset G.V} {hA : A.Nonempty}
    (t : firing_script (inducedSubgraph G A hA)) {v : G.V} (hv : v ∉ A) :
    extendScript G A hA t v = 0 := dif_neg hv

/-- The script's support consists of interior vertices. -/
def SupportInterior {A : Finset G.V} {hA : A.Nonempty}
    (t : firing_script (inducedSubgraph G A hA)) : Prop :=
  ∀ x : (inducedSubgraph G A hA).V, t x ≠ 0 → Interior G A x.val

/-- The practical form of the side condition: name a finite set `B` containing
every non-interior vertex of `A`, and check that the script vanishes on it. -/
theorem supportInterior_of_vanishing_on_boundary {A : Finset G.V} {hA : A.Nonempty}
    {t : firing_script (inducedSubgraph G A hA)} (B : Finset G.V)
    (hB : ∀ x : (inducedSubgraph G A hA).V, x.val ∉ B → Interior G A x.val)
    (hVanish : ∀ x : (inducedSubgraph G A hA).V, x.val ∈ B → t x = 0) :
    SupportInterior t := by
  intro x hx
  by_cases hmem : x.val ∈ B
  · exact absurd (hVanish x hmem) hx
  · exact hB x hmem

/-! ## The transport computation -/

/-- Outside `A` the extended script does nothing. -/
theorem prin_extendScript_of_not_mem {A : Finset G.V} {hA : A.Nonempty}
    {t : firing_script (inducedSubgraph G A hA)} (ht : SupportInterior t)
    {v : G.V} (hv : v ∉ A) :
    prin G (extendScript G A hA t) v = 0 := by
  classical
  show (∑ u : G.V, (extendScript G A hA t u - extendScript G A hA t v)
      * (num_edges G v u : ℤ)) = 0
  rw [extendScript_of_not_mem t hv]
  refine Finset.sum_eq_zero fun u _ => ?_
  by_cases hu : u ∈ A
  · by_cases hzero : t ⟨u, hu⟩ = 0
    · rw [extendScript_of_mem t hu, hzero]
      ring
    · rw [num_edges_eq_zero_of_interior (ht ⟨u, hu⟩ hzero) hv]
      ring
  · rw [extendScript_of_not_mem t hu]
    ring

/-- Inside `A` the extended script acts exactly as it does on `G[A]`. -/
theorem prin_extendScript_of_mem {A : Finset G.V} {hA : A.Nonempty}
    {t : firing_script (inducedSubgraph G A hA)} (ht : SupportInterior t)
    {v : G.V} (hv : v ∈ A) :
    prin G (extendScript G A hA t) v =
      prin (inducedSubgraph G A hA) t ⟨v, hv⟩ := by
  classical
  show (∑ u : G.V, (extendScript G A hA t u - extendScript G A hA t v)
      * (num_edges G v u : ℤ))
    = ∑ x : (inducedSubgraph G A hA).V,
        (t x - t ⟨v, hv⟩) * (num_edges (inducedSubgraph G A hA) ⟨v, hv⟩ x : ℤ)
  -- The outside contributes nothing.
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset G.V)
    (fun u => u ∈ A)
    (fun u => (extendScript G A hA t u - extendScript G A hA t v)
      * (num_edges G v u : ℤ))
  have houtside : ∑ u ∈ Finset.univ.filter (fun u => ¬ u ∈ A),
      (extendScript G A hA t u - extendScript G A hA t v)
        * (num_edges G v u : ℤ) = 0 := by
    refine Finset.sum_eq_zero fun u hu => ?_
    have hu' : u ∉ A := (Finset.mem_filter.mp hu).2
    rw [extendScript_of_not_mem t hu', extendScript_of_mem t hv]
    by_cases hzero : t ⟨v, hv⟩ = 0
    · rw [hzero]; ring
    · rw [ht ⟨v, hv⟩ hzero u hu']
      ring
  rw [← hsplit, houtside, add_zero]
  -- Inside `A` the two sums agree termwise.
  have hinside : ∑ u ∈ Finset.univ.filter (fun u => u ∈ A),
      (extendScript G A hA t u - extendScript G A hA t v)
        * (num_edges G v u : ℤ)
    = ∑ u ∈ A, (extendScript G A hA t u - extendScript G A hA t v)
        * (num_edges G v u : ℤ) := by
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext u
    simp
  rw [hinside]
  rw [Finset.sum_subtype (p := fun u : G.V => u ∈ A) A (fun _ => Iff.rfl)
    (fun u => (extendScript G A hA t u - extendScript G A hA t v)
      * (num_edges G v u : ℤ))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [extendScript_of_mem t x.property, extendScript_of_mem t hv,
    num_edges_inducedSubgraph G A hA ⟨v, hv⟩ x]

/-! ## The transport theorem -/

/-- **A local Dhar move inside `G[A]` proves ambient reachability.**

The hypotheses are exactly three:

* the ambient divisor is effective away from `A` (nothing outside is spent);
* the target lies in `A`;
* the script is supported on interior vertices -- equivalently, it vanishes on
  the boundary of `A`.

Under them, an effective residual computed entirely inside the induced
subgraph `G[A]` is an effective ambient residual. -/
theorem reaches_of_induced_script {A : Finset G.V} (hA : A.Nonempty)
    {D : CFDiv G} (hOff : ∀ v : G.V, v ∉ A → 0 ≤ D v)
    {p : G.V} (hp : p ∈ A)
    {t : firing_script (inducedSubgraph G A hA)} (ht : SupportInterior t)
    (hEff : effective ((fun x : (inducedSubgraph G A hA).V => D x.val)
      - one_chip (⟨p, hp⟩ : (inducedSubgraph G A hA).V)
      + prin (inducedSubgraph G A hA) t)) :
    Reaches G D p := by
  classical
  refine ⟨D - one_chip p + prin G (extendScript G A hA t), ?_, ?_⟩
  · show effective (D - one_chip p + prin G (extendScript G A hA t))
    intro v
    by_cases hv : v ∈ A
    · have hchip : one_chip p v
          = one_chip (G := inducedSubgraph G A hA) ⟨p, hp⟩ ⟨v, hv⟩ := by
        show (if v = p then (1 : ℤ) else 0)
            = if (⟨v, hv⟩ : (inducedSubgraph G A hA).V) = ⟨p, hp⟩ then (1 : ℤ) else 0
        refine if_congr ?_ rfl rfl
        simp [Subtype.ext_iff]
      have := hEff ⟨v, hv⟩
      simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
      rw [prin_extendScript_of_mem ht hv, hchip]
      exact this
    · have hchip : one_chip p v = 0 := by
        have hvp : v ≠ p := by
          intro hvp
          exact hv (hvp ▸ hp)
        exact one_chip_apply_other p v hvp.symm
      simp only [Pi.add_apply, Pi.sub_apply]
      rw [prin_extendScript_of_not_mem ht hv, hchip]
      simpa using hOff v hv
  · exact linearEquiv_add_prin (D - one_chip p) (extendScript G A hA t)

/-! ## The one-boundary case: a vertex gluing, where the side condition is free -/

/-- **The vertex-gluing case.**  If `g` is the only vertex of `A` with an edge
leaving `A`, the interior side condition is free: normalise the script to
vanish at `g`.  This is the delivery statement for a one-vertex cut, and it
needs no hypothesis on the script at all. -/
theorem reaches_of_induced_script_of_unique_boundary {A : Finset G.V}
    (hA : A.Nonempty) {g : G.V} (hg : g ∈ A)
    (hBoundary : ∀ u : G.V, u ∈ A → u ≠ g → Interior G A u)
    {D : CFDiv G} (hOff : ∀ v : G.V, v ∉ A → 0 ≤ D v)
    {p : G.V} (hp : p ∈ A)
    (t : firing_script (inducedSubgraph G A hA))
    (hEff : effective ((fun x : (inducedSubgraph G A hA).V => D x.val)
      - one_chip (⟨p, hp⟩ : (inducedSubgraph G A hA).V)
      + prin (inducedSubgraph G A hA) t)) :
    Reaches G D p := by
  classical
  set c : ℤ := t ⟨g, hg⟩ with hc
  refine reaches_of_induced_script (t := fun x => t x - c) hA hOff hp ?_ ?_
  · intro x hx
    have hne : x ≠ ⟨g, hg⟩ := by
      intro hxg
      apply hx
      rw [hxg, hc]
      ring
    exact hBoundary x.val x.property fun hval => hne (Subtype.ext hval)
  · rwa [prin_sub_const (inducedSubgraph G A hA) t c]

end Utilities.Gluing
