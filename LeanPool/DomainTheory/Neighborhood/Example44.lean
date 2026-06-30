/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Example23
import LeanPool.DomainTheory.Neighborhood.Theorem41

/-!
# Example 4.4 (Scott 1981, PRG-19, §4) — the domain `C` of binary sequences

Scott's domain `C` of *finite or infinite binary sequences* (pages 61–64), a
generalization of the
natural-number domain `N` of Example 4.3. Over the tokens `Σ* = List Bool`
(Scott's `Σ = {0,1}`,
`Λ = []`), recall the cones `cone σ = σΣ*` of Example 1.B. The system `C` adds the
*singletons*:

`C = {σΣ* ∣ σ ∈ Σ*} ∪ {{σ} ∣ σ ∈ Σ*}`.

The total elements correspond to finite or infinite sequences: `σ = ↑{σ}`
(`strElem σ`, the finite
sequence `σ` *completed*) and `σ⊥ = ↑σΣ*` (`strBot σ`, the partial element "starts
with `σ`"). `C`
is again nested-or-disjoint, so it is a neighbourhood system
(`ofNestedOrDisjoint`).

We equip `C` with the two **successors** `x ↦ 0x` and `x ↦ 1x` (`consMap false`,
`consMap true`),
prepending a bit, with their action on the finite/partial elements
(`consMap_strElem`,
`consMap_strBot`). As Scott's illustration that recursion now lives inside `|C|`,
we then define the
alternating sequence `a = 01a` as the least fixed point of `x ↦ 0(1x)` (`altElt`,
`altElt_eq`),
using the Fixed-point Theorem 4.1.

The remaining structure maps Scott lists for `⟨C, Λ, 0, 1, tail, empty, zero,
one⟩` — the
predecessor analogue `tail` (`tail(0x) = tail(1x) = x`, `tail(Λ) = ⊥`) and the
three tests
`empty, zero, one : C → T` — are exactly the parts Scott leaves as exercises ("It
is left to the
reader to show that **tail** exists as an approximable mapping"; "it is an
exercise to show these
are approximable", Exercise 4.19); they are out of scope for this module.

The data constructions (`C`, `consMap`) are **choice-free** (`#print axioms ⊆
{propext,
Quot.sound}`).
-/

namespace Domain.Neighborhood.Example44

open Domain.Neighborhood NeighborhoodSystem ApproximableMap ExampleB

/-! ### Prepending a bit: set-level lemmas (reused from Example 1.B). -/

/-- `σ{τ} = {στ}`: prepending `σ` to a singleton is the singleton of the
concatenation. -/
theorem prepend_singleton (σ τ : Str) : prepend σ {τ} = {σ ++ τ} := by
  ext w
  simp only [mem_prepend, Set.mem_singleton_iff]
  constructor
  · rintro ⟨t, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨τ, rfl, rfl⟩

/-- Prepending is monotone in its set argument. -/
theorem prepend_mono (σ : Str) {X X' : Set Str} (h : X' ⊆ X) : prepend σ X' ⊆ prepend σ X := by
  rintro w ⟨τ, hτ, rfl⟩
  exact ⟨τ, h hτ, rfl⟩

/-! ### The neighbourhood system `C`. -/

/-- Membership in `C`: a neighbourhood is a cone `σΣ*` or a singleton `{σ}`. -/
def memC (X : Set Str) : Prop := (∃ σ, X = cone σ) ∨ (∃ σ, X = {σ})

theorem memC_cone (σ : Str) : memC (cone σ) := Or.inl ⟨σ, rfl⟩

theorem memC_singleton (σ : Str) : memC ({σ} : Set Str) := Or.inr ⟨σ, rfl⟩

/-- `{τ} ⊆ σΣ*` iff `σ` is an initial segment of `τ`. -/
theorem singleton_subset_cone {σ τ : Str} : ({τ} : Set Str) ⊆ cone σ ↔ σ <+: τ := by
  rw [Set.singleton_subset_iff, mem_cone]

/-- A singleton and a cone are nested-or-disjoint. -/
theorem singleton_cone_nd (σ τ : Str) :
    ({τ} : Set Str) ⊆ cone σ ∨ cone σ ⊆ {τ} ∨ ({τ} : Set Str) ∩ cone σ = ∅ := by
  by_cases h : σ <+: τ
  · exact Or.inl (singleton_subset_cone.mpr h)
  · refine Or.inr (Or.inr ?_)
    ext w
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, mem_cone, Set.mem_empty_iff_false,
      iff_false, not_and]
    rintro rfl hτ
    exact h hτ

/-- Any two neighbourhoods of `C` are nested or disjoint. -/
theorem nestedOrDisjoint : NestedOrDisjoint memC := by
  rintro X Y (⟨σ, rfl⟩ | ⟨σ, rfl⟩) (⟨τ, rfl⟩ | ⟨τ, rfl⟩)
  · exact cone_trichotomy σ τ
  · rcases singleton_cone_nd σ τ with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (by rw [Set.inter_comm]; exact h))
  · rcases singleton_cone_nd τ σ with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · by_cases h : σ = τ
    · subst h; exact Or.inl (Set.Subset.refl _)
    · refine Or.inr (Or.inr ?_)
      ext w
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
        not_and]
      rintro rfl h2
      exact h h2

/-- **Example 4.4 (Scott 1981, PRG-19).** The neighbourhood system `C` of finite
or infinite binary
sequences on `Δ = Σ*`. -/
def C : NeighborhoodSystem Str :=
  NeighborhoodSystem.ofNestedOrDisjoint memC Set.univ (Or.inl ⟨[], cone_nil.symm⟩) nestedOrDisjoint
    (fun _ => Set.subset_univ _)

@[simp] theorem C_mem {X : Set Str} : C.mem X ↔ memC X := Iff.rfl

@[simp] theorem C_master : C.master = (Set.univ : Set Str) := rfl

/-! ### Elements of `C`: `σ` (total) and `σ⊥` (partial). -/

/-- Scott's partial element `σ⊥ = ↑σΣ*` ("the sequence starts with `σ`"). -/
def strBot (σ : Str) : C.Element := C.principal (memC_cone σ)

/-- Scott's total element `σ = ↑{σ}` (the finite sequence `σ`, completed). -/
def strElem (σ : Str) : C.Element := C.principal (memC_singleton σ)

/-! ### The successor maps `x ↦ bx`. -/

/-- Prepending the bit `b` (or, generally, a prefix `σ`) to a neighbourhood of `C`
lands back in
`C`: `σ(τΣ*) = (στ)Σ*` and `σ{τ} = {στ}`. -/
theorem memC_prepend (σ : Str) {X : Set Str} (hX : memC X) : memC (prepend σ X) := by
  rcases hX with ⟨ρ, rfl⟩ | ⟨ρ, rfl⟩
  · exact Or.inl ⟨σ ++ ρ, prepend_cone σ ρ⟩
  · exact Or.inr ⟨σ ++ ρ, prepend_singleton σ ρ⟩

/-- `σX ⊆ X` along the prefix order: a prepended neighbourhood is contained in any
neighbourhood it
refines. (Used only via `prepend_mono`; kept implicit.) -/
theorem prepend_subset_self : True := trivial

/-- **Example 4.4 — the successors `x ↦ bx`.** The approximable map prepending the
bit `b`:
`X (bx) Y ↔ bX ⊆ Y`. Approximable because `bX` is again a neighbourhood
(`memC_prepend`) and
prepending is monotone. -/
def consMap (b : Bool) : ApproximableMap C C where
  rel X Y := memC X ∧ memC Y ∧ prepend [b] X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := by
    refine ⟨Or.inl ⟨[], cone_nil.symm⟩, Or.inl ⟨[], cone_nil.symm⟩, ?_⟩
    exact Set.subset_univ _
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hsub⟩ ⟨_, hY', hsub'⟩
    have hsubInter : prepend [b] X ⊆ Y ∩ Y' := Set.subset_inter hsub hsub'
    have hZ : memC (prepend [b] X) := memC_prepend [b] hX
    exact ⟨hX, C.inter_mem hY hY' hZ hsubInter, hsubInter⟩
  mono := by
    rintro X X' Y Y' ⟨hX, hY, hsub⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', (prepend_mono [b] hX'X).trans (hsub.trans hYY')⟩

/-- `bx` on a partial element: `b(σ⊥) = (bσ)⊥`. -/
theorem consMap_strBot (b : Bool) (σ : Str) :
    (consMap b).toElementMap (strBot σ) = strBot (b :: σ) := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X', ⟨_, hXX'⟩, _, hY, hsub⟩
    refine ⟨hY, ?_⟩
    have hpre : prepend [b] (cone σ) ⊆ Y := (prepend_mono [b] hXX').trans hsub
    rwa [prepend_cone] at hpre
  · rintro ⟨hY, hsub⟩
    refine ⟨cone σ, ⟨memC_cone σ, subset_rfl⟩, memC_cone σ, hY, ?_⟩
    rw [prepend_cone]; exact hsub

/-- `bx` on a total element: `b(σ) = (bσ)` (prepend the bit to a finite sequence). -/
theorem consMap_strElem (b : Bool) (σ : Str) :
    (consMap b).toElementMap (strElem σ) = strElem (b :: σ) := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X', ⟨_, hXX'⟩, _, hY, hsub⟩
    refine ⟨hY, ?_⟩
    have hpre : prepend [b] {σ} ⊆ Y := (prepend_mono [b] hXX').trans hsub
    rwa [prepend_singleton] at hpre
  · rintro ⟨hY, hsub⟩
    refine ⟨{σ}, ⟨memC_singleton σ, subset_rfl⟩, memC_singleton σ, hY, ?_⟩
    rw [prepend_singleton]; exact hsub

/-! ### A fixed-point element: the alternating sequence `a = 01a`. -/

/-- **Example 4.4 — an element defined by a fixed-point equation.** Scott's `a =
01a`, the infinite
sequence that alternates `0`s and `1`s. We take the least fixed point of `x ↦
0(1x)`
(`= consMap 0 ∘ consMap 1`), which exists by the Fixed-point Theorem 4.1. -/
def altElt : C.Element := ((consMap false).comp (consMap true)).fixElement

/-- `a = 0(1a)`: `altElt` satisfies Scott's defining equation. -/
theorem altElt_eq : (consMap false).toElementMap ((consMap true).toElementMap altElt) = altElt := by
  have h := toElementMap_fixElement ((consMap false).comp (consMap true))
  rwa [toElementMap_comp] at h

end Domain.Neighborhood.Example44
