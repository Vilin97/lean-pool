/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Exercise222
import LeanPool.DomainTheory.Neighborhood.FunctionSpace

/-!
# Exercise 3.27 (Scott 1981, PRG-19, §3) — `(𝒟₀ → 𝒟₁)` is a domain, via Exercise
2.22

(*For set theorists.*) Scott asks for *another* proof that the family of
approximable mappings
`f : 𝒟₀ → 𝒟₁` is isomorphic to a domain, "by employing the general argument of
Exercise 2.22"
(the abstract representation theorem: any family of sets closed under non-empty
intersections and
directed unions is inclusion-isomorphic to a domain).

The set-theoretic content: identify each approximable map `f` with its **graph**
`graph f = {(X, Y) ∣ X f Y} ⊆ 𝒫(Δ₀) × 𝒫(Δ₁)`, and let `C = {graph f}` be the
family of all such
graphs. Then

* `C` is closed under **non-empty intersections** — the pointwise *meet* `⋀ 𝒮` of
a family of
  approximable maps (relate `X` to `Y` iff every member does) is again
  approximable (`meetMap`);
* `C` is closed under **directed unions** — the *join* `⋁ 𝒮` of a directed family
(relate `X` to `Y`
  iff some member does) is again approximable, the consistency condition using
  directedness
  (`joinMap`).

So Exercise 2.22 (`reprIso`) re-presents `C` — hence, via `graph` and Theorem 3.10
(`funSpaceEquiv`),
the whole function space `|𝒟₀ → 𝒟₁|` — as the domain of a neighbourhood system,
*without* writing
down the step-set neighbourhoods of Definition 3.8 explicitly. This is exactly
Scott's "compare with
3.9/3.10" alternative.

**Axioms.** As flagged by Scott ("for set theorists"), this inherits
`Classical.choice` from
Exercise 2.22 and from the `graph`-inversion.
-/

namespace Domain.Neighborhood.Exercise327

open Domain.Neighborhood NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The **graph** of an approximable map, as a set of neighbourhood pairs. -/
def graph (f : ApproximableMap V₀ V₁) : Set (Set α × Set β) := {p | f.rel p.1 p.2}

@[simp] theorem mem_graph {f : ApproximableMap V₀ V₁} {p : Set α × Set β} :
    p ∈ graph f ↔ f.rel p.1 p.2 := Iff.rfl

theorem graph_injective : Function.Injective (graph (V₀ := V₀) (V₁ := V₁)) :=
  fun _ _ h => ApproximableMap.ext fun X Y => Set.ext_iff.mp h (X, Y)

/-- Scott's family `C`: all graphs of approximable maps `𝒟₀ → 𝒟₁`. -/
def C (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : Set (Set (Set α × Set β)) :=
  Set.range (graph (V₀ := V₀) (V₁ := V₁))

theorem C_nonempty : (C V₀ V₁).Nonempty :=
  ⟨graph (constMap V₀ V₁.bot), constMap V₀ V₁.bot, rfl⟩

/-! ### The meet of a non-empty family of maps. -/

/-- The pointwise **meet** `⋀ 𝒮` of a family of approximable maps (drawn from
`C`): `X (⋀𝒮) Y` iff
`(X, Y)` lies in every member of `𝒮`. -/
def meetMap (𝒮 : Set (Set (Set α × Set β))) (h𝒮 : 𝒮 ⊆ C V₀ V₁) (hne : 𝒮.Nonempty) :
    ApproximableMap V₀ V₁ where
  rel X Y := ∀ S ∈ 𝒮, (X, Y) ∈ S
  rel_dom := by
    intro X Y h
    obtain ⟨S, hS⟩ := hne; obtain ⟨f, rfl⟩ := h𝒮 hS
    exact f.rel_dom (h _ hS)
  rel_cod := by
    intro X Y h
    obtain ⟨S, hS⟩ := hne; obtain ⟨f, rfl⟩ := h𝒮 hS
    exact f.rel_cod (h _ hS)
  master_rel := by
    intro S hS; obtain ⟨f, rfl⟩ := h𝒮 hS; exact f.master_rel
  inter_right := by
    intro X Y Y' hY hY' S hS
    obtain ⟨f, rfl⟩ := h𝒮 hS
    exact f.inter_right (hY _ hS) (hY' _ hS)
  mono := by
    intro X X' Y Y' h hX'X hYY' hX' hY' S hS
    obtain ⟨f, rfl⟩ := h𝒮 hS
    exact f.mono (h _ hS) hX'X hYY' hX' hY'

theorem sInter_eq_graph_meetMap (𝒮 : Set (Set (Set α × Set β))) (h𝒮 : 𝒮 ⊆ C V₀ V₁)
    (hne : 𝒮.Nonempty) : ⋂₀ 𝒮 = graph (meetMap 𝒮 h𝒮 hne) := by
  ext p
  simp only [Set.mem_sInter, mem_graph]
  exact ⟨fun h S hS => h S hS, fun h S hS => h S hS⟩

/-- **Exercise 2.22 hypothesis (i).** `C` is closed under non-empty intersections. -/
theorem C_inter : ∀ 𝒮 : Set (Set (Set α × Set β)), 𝒮.Nonempty → 𝒮 ⊆ C V₀ V₁ → ⋂₀ 𝒮 ∈ C V₀ V₁ := by
  intro 𝒮 hne h𝒮
  rw [sInter_eq_graph_meetMap 𝒮 h𝒮 hne]
  exact ⟨meetMap 𝒮 h𝒮 hne, rfl⟩

/-! ### The join of a directed family of maps. -/

/-- The **join** `⋁ 𝒮` of a directed family of approximable maps: `X (⋁𝒮) Y` iff
`(X, Y)` lies in
some member. Directedness is what restores the intersectivity condition (ii). -/
def joinMap (𝒮 : Set (Set (Set α × Set β))) (h𝒮 : 𝒮 ⊆ C V₀ V₁) (hne : 𝒮.Nonempty)
    (hdir : DirectedOn (· ⊆ ·) 𝒮) : ApproximableMap V₀ V₁ where
  rel X Y := ∃ S ∈ 𝒮, (X, Y) ∈ S
  rel_dom := by rintro X Y ⟨S, hS, hp⟩; obtain ⟨f, rfl⟩ := h𝒮 hS; exact f.rel_dom hp
  rel_cod := by rintro X Y ⟨S, hS, hp⟩; obtain ⟨f, rfl⟩ := h𝒮 hS; exact f.rel_cod hp
  master_rel := by
    obtain ⟨S, hS⟩ := hne; obtain ⟨f, rfl⟩ := h𝒮 hS
    exact ⟨graph f, hS, f.master_rel⟩
  inter_right := by
    rintro X Y Y' ⟨S, hS, hp⟩ ⟨S', hS', hp'⟩
    obtain ⟨S₃, hS₃, hSS₃, hS'S₃⟩ := hdir S hS S' hS'
    obtain ⟨f, rfl⟩ := h𝒮 hS₃
    exact ⟨graph f, hS₃, f.inter_right (hSS₃ hp) (hS'S₃ hp')⟩
  mono := by
    rintro X X' Y Y' ⟨S, hS, hp⟩ hX'X hYY' hX' hY'
    obtain ⟨f, rfl⟩ := h𝒮 hS
    exact ⟨graph f, hS, f.mono hp hX'X hYY' hX' hY'⟩

theorem sUnion_eq_graph_joinMap (𝒮 : Set (Set (Set α × Set β))) (h𝒮 : 𝒮 ⊆ C V₀ V₁)
    (hne : 𝒮.Nonempty) (hdir : DirectedOn (· ⊆ ·) 𝒮) :
    ⋃₀ 𝒮 = graph (joinMap 𝒮 h𝒮 hne hdir) := by
  ext p
  simp only [Set.mem_sUnion, mem_graph]
  exact ⟨fun ⟨S, hS, hp⟩ => ⟨S, hS, hp⟩, fun ⟨S, hS, hp⟩ => ⟨S, hS, hp⟩⟩

/-- **Exercise 2.22 hypothesis (ii).** `C` is closed under directed unions. -/
theorem C_dir : ∀ 𝒮 : Set (Set (Set α × Set β)), 𝒮.Nonempty → 𝒮 ⊆ C V₀ V₁ →
    DirectedOn (· ⊆ ·) 𝒮 → ⋃₀ 𝒮 ∈ C V₀ V₁ := by
  intro 𝒮 hne h𝒮 hdir
  rw [sUnion_eq_graph_joinMap 𝒮 h𝒮 hne hdir]
  exact ⟨joinMap 𝒮 h𝒮 hne hdir, rfl⟩

/-! ### `C ≅ Hom(𝒟₀, 𝒟₁) ≅ |𝒟₀ → 𝒟₁|`. -/

/-- `graph` is an order-isomorphism of approximable maps (under `⊑`) onto the
family `C`
(under `⊆`). -/
noncomputable def graphEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap V₀ V₁ ≃o {X : Set (Set α × Set β) // X ∈ C V₀ V₁} where
  toFun f := ⟨graph f, f, rfl⟩
  invFun X := X.2.choose
  left_inv f := graph_injective (⟨graph f, f, rfl⟩ : {X // X ∈ C V₀ V₁}).2.choose_spec
  right_inv X := Subtype.ext X.2.choose_spec
  map_rel_iff' := by
    intro f g
    change graph f ⊆ graph g ↔ f ≤ g
    rw [ApproximableMap.le_iff]
    exact ⟨fun h X Y hf => h (a := (X, Y)) hf, fun h p hp => h p.1 p.2 hp⟩

/-! ### Exercise 3.27. -/

/-- **Exercise 3.27.** The function space `|𝒟₀ → 𝒟₁|` is (order-)isomorphic to the
domain
produced by
the *abstract* representation theorem (Exercise 2.22) applied to the family `C` of
graphs of
approximable maps. This re-proves that approximable mappings form a domain without
appealing to the
explicit step-set neighbourhood system of Definition 3.8 — composing Exercise
2.22's `reprIso` with
the graph isomorphism (`graphEquiv`) and Theorem 3.10 (`funSpaceEquiv`). -/
noncomputable def funSpaceReprIso (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    (Exercise222.reprSystem (C V₀ V₁) C_inter C_nonempty).Element ≃o (funSpace V₀ V₁).Element :=
  (Exercise222.reprIso (C V₀ V₁) C_inter C_nonempty C_dir).trans
    ((graphEquiv V₀ V₁).symm.trans (funSpaceEquiv V₀ V₁).symm)

end Domain.Neighborhood.Exercise327
