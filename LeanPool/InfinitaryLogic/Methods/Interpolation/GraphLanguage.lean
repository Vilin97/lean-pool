/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Lomega1omega.Operations
/-!
# Relationalization of a language: the graph language and its structures (Craig Layer 3, Unit 1)

The first gated unit of the functions→relations relationalization (audit §9b): the relationalized
language `graphLanguage L` — no function symbols, each `n`-ary function `f` replaced by an
`(n+1)`-ary **graph relation** `G_f` with intended meaning `G_f(xs, y) ↔ f(xs) = y` — its graph
expansion of an `L`-structure, and the σ-level embeddings of the original symbols into the graph
language's relation symbols.

The disjoint indexed constructors of `GraphRelation` keep base relations and function graphs apart
*definitionally*, which is exactly what makes the shared-vocabulary identity

  `relSym L F₁ R₁ ∩ relSym L F₂ R₂ = relSym L (F₁ ∩ F₂) (R₁ ∩ R₂)`

(the early correctness gate for the eventual sharp occurrence bound) a clean image/injectivity
computation.

## Contents

* `GraphRelation`, `graphLanguage`, `graphLanguage_isRelational`;
* `graphExpansion` (the `G_f(xs,y) ↔ f(xs)=y` structure) with `relMap_base`/`relMap_graph` simp
  lemmas;
* `baseRelSym`/`graphRelSym` σ-embeddings, their injectivity and cross-disjointness;
* `relSym` and the intersection identity `relSym_inter`.
-/

namespace FirstOrder.Language

open FirstOrder Structure

/-! ## The relationalized language -/

/-- Relation symbols of the relationalization of `L`: every base relation is kept at its arity,
and every `n`-ary function symbol becomes an `(n+1)`-ary graph relation.  The two constructors are
disjoint by construction. -/
inductive GraphRelation (L : Language.{0, 0}) : ℕ → Type
  | base : ∀ {n}, L.Relations n → GraphRelation L n
  | graph : ∀ {n}, L.Functions n → GraphRelation L (n + 1)

/-- The relationalization of `L`: **no** function symbols, relation symbols `GraphRelation L`.

Marked `@[reducible]` so that `(graphLanguage L).Relations n` unfolds to `GraphRelation L n` at
`implicit` transparency. The whole relationalization tower already treats the two as
interchangeable — `baseRelSym`/`graphRelSym` below take their codomain in `GraphRelation L n`
precisely so the constructors' injectivity and no-confusion lemmas apply directly, and the
companion `graphExpansion` is `@[reducible]` for the same reason. Since Lean 4.34 requires goals
to be type-correct at `implicit` transparency before `rw`/`simp` will act, that pre-existing
identification has to hold there too; otherwise every generic lemma about `graphLanguage`
formulas needs a specialized copy with the symbol spelled `GraphRelation.base`/`.graph`. This is
a direct structure literal with no proof content, so reducibility costs nothing. -/
@[reducible] def graphLanguage (L : Language.{0, 0}) : Language.{0, 0} where
  Functions _ := Empty
  Relations n := GraphRelation L n

instance graphLanguage_isRelational (L : Language.{0, 0}) : (graphLanguage L).IsRelational :=
  fun _ => inferInstanceAs (IsEmpty Empty)

variable {L : Language.{0, 0}}

/-! ## The graph expansion of an `L`-structure -/

/-- Realization of a graph-language relation symbol in the graph expansion of an `L`-structure:
base relations unchanged, and `G_f(xs, y)` reads `f(xs) = y` (the first `n` coordinates feed `f`,
the last is its value). -/
private def graphRelMap (M : Type) [L.Structure M] :
    ∀ {n : ℕ}, GraphRelation L n → (Fin n → M) → Prop
  | _, .base r, v => Structure.RelMap r v
  | _, .graph f, v => Structure.funMap f (Fin.init v) = v (Fin.last _)

/-- The **graph expansion** of an `L`-structure to a `graphLanguage L`-structure:
`G_f(xs, y) ↔ f(xs) = y`, base relations preserved, and no function symbols to interpret. -/
@[reducible] def graphExpansion (L : Language.{0, 0}) (M : Type) [L.Structure M] :
    (graphLanguage L).Structure M where
  funMap f _ := nomatch f
  RelMap := graphRelMap M

@[simp] theorem graphExpansion_relMap_base (M : Type) [L.Structure M] {n : ℕ}
    (r : L.Relations n) (v : Fin n → M) :
    (graphExpansion L M).RelMap (GraphRelation.base r) v ↔ Structure.RelMap r v := Iff.rfl

@[simp] theorem graphExpansion_relMap_graph (M : Type) [L.Structure M] {n : ℕ}
    (f : L.Functions n) (v : Fin (n + 1) → M) :
    (graphExpansion L M).RelMap (GraphRelation.graph f) v ↔
      (Structure.funMap f (Fin.init v) = v (Fin.last n)) := Iff.rfl

/-! ## σ-level embeddings of the original symbols -/

/-- Embed an original relation symbol as a base graph-language relation symbol. (Codomain uses
`GraphRelation L n`, definitionally `(graphLanguage L).Relations n`, so the constructor's
injectivity/no-confusion lemmas apply directly.) -/
def baseRelSym (L : Language.{0, 0}) :
    (Σ n, L.Relations n) → (Σ n, GraphRelation L n) :=
  fun p => ⟨p.1, GraphRelation.base p.2⟩

/-- Embed an original `n`-ary function symbol as its `(n+1)`-ary graph relation symbol. -/
def graphRelSym (L : Language.{0, 0}) :
    (Σ n, L.Functions n) → (Σ n, GraphRelation L n) :=
  fun p => ⟨p.1 + 1, GraphRelation.graph p.2⟩

theorem baseRelSym_injective : Function.Injective (baseRelSym L) := by
  rintro ⟨n, r⟩ ⟨n', r'⟩ h
  rw [baseRelSym, baseRelSym, Sigma.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  rw [heq_eq_eq, GraphRelation.base.injEq] at h2
  subst h2; rfl

theorem graphRelSym_injective : Function.Injective (graphRelSym L) := by
  rintro ⟨n, f⟩ ⟨n', f'⟩ h
  rw [graphRelSym, graphRelSym, Sigma.mk.injEq] at h
  obtain ⟨he, h2⟩ := h
  obtain rfl : n = n' := Nat.succ_injective he
  rw [heq_eq_eq, GraphRelation.graph.injEq] at h2
  subst h2; rfl

theorem baseRelSym_ne_graphRelSym (p : Σ n, L.Relations n) (q : Σ n, L.Functions n) :
    baseRelSym L p ≠ graphRelSym L q := by
  obtain ⟨pn, pr⟩ := p
  obtain ⟨qn, qf⟩ := q
  intro h
  rw [baseRelSym, graphRelSym, Sigma.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  rw [heq_eq_eq] at h2
  simp at h2

/-! Singleton preimages of the two embeddings — the Sigma-free interface the back-translation
occurrence calculus computes with. -/

theorem baseRelSym_preimage_base_singleton (p : Σ n, L.Relations n) :
    baseRelSym L ⁻¹' {baseRelSym L p} = {p} := by
  ext q
  simp [baseRelSym_injective.eq_iff]

theorem graphRelSym_preimage_graph_singleton (q : Σ n, L.Functions n) :
    graphRelSym L ⁻¹' {graphRelSym L q} = {q} := by
  ext p
  simp [graphRelSym_injective.eq_iff]

theorem graphRelSym_preimage_base_singleton (p : Σ n, L.Relations n) :
    graphRelSym L ⁻¹' {baseRelSym L p} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro q hq
  exact baseRelSym_ne_graphRelSym p q (Set.mem_singleton_iff.mp hq).symm

theorem baseRelSym_preimage_graph_singleton (q : Σ n, L.Functions n) :
    baseRelSym L ⁻¹' {graphRelSym L q} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro p hp
  exact baseRelSym_ne_graphRelSym p q (Set.mem_singleton_iff.mp hp)

/-! ## The relation-symbol set of the relationalization, and its intersection identity -/

/-- The relation symbols of the relationalization coming from a function-symbol set `F` and a
relation-symbol set `R`: base relations from `R`, graph relations from `F`. -/
def relSym (L : Language.{0, 0}) (F : Set (Σ n, L.Functions n)) (R : Set (Σ n, L.Relations n)) :
    Set (Σ n, GraphRelation L n) :=
  baseRelSym L '' R ∪ graphRelSym L '' F

private theorem baseRelSym_image_inter_graphRelSym_image (R : Set (Σ n, L.Relations n))
    (F : Set (Σ n, L.Functions n)) : baseRelSym L '' R ∩ graphRelSym L '' F = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨⟨p, _, rfl⟩, ⟨q, _, hq⟩⟩
  exact baseRelSym_ne_graphRelSym p q hq.symm

theorem graphRelSym_image_inter_baseRelSym_image (F : Set (Σ n, L.Functions n))
    (R : Set (Σ n, L.Relations n)) : graphRelSym L '' F ∩ baseRelSym L '' R = ∅ := by
  rw [Set.inter_comm]; exact baseRelSym_image_inter_graphRelSym_image R F

/-- **The shared-vocabulary identity** (Unit 1 correctness gate): the relation-symbol sets of two
relationalizations meet exactly in the relationalization of the shared symbols. -/
theorem relSym_inter (F₁ : Set (Σ n, L.Functions n)) (R₁ : Set (Σ n, L.Relations n))
    (F₂ : Set (Σ n, L.Functions n)) (R₂ : Set (Σ n, L.Relations n)) :
    relSym L F₁ R₁ ∩ relSym L F₂ R₂ = relSym L (F₁ ∩ F₂) (R₁ ∩ R₂) := by
  simp only [relSym]
  rw [Set.union_inter_distrib_right, Set.inter_union_distrib_left, Set.inter_union_distrib_left,
    baseRelSym_image_inter_graphRelSym_image, graphRelSym_image_inter_baseRelSym_image,
    Set.union_empty, Set.empty_union,
    ← Set.image_inter baseRelSym_injective, ← Set.image_inter graphRelSym_injective]

@[simp] theorem relSym_empty : relSym L ∅ ∅ = ∅ := by
  simp [relSym]

/-- `relSym` turns unions of symbol sets into unions — the algebra the exact occurrence
identity of the formula translation steps through at binary connectives. -/
theorem relSym_union (F₁ F₂ : Set (Σ n, L.Functions n)) (R₁ R₂ : Set (Σ n, L.Relations n)) :
    relSym L (F₁ ∪ F₂) (R₁ ∪ R₂) = relSym L F₁ R₁ ∪ relSym L F₂ R₂ := by
  simp only [relSym, Set.image_union]
  exact Set.union_union_union_comm _ _ _ _

/-- `relSym` commutes with indexed unions — the countable-connective step of the exact
occurrence identity. -/
theorem relSym_iUnion {ι : Sort*} (F : ι → Set (Σ n, L.Functions n))
    (R : ι → Set (Σ n, L.Relations n)) :
    relSym L (⋃ i, F i) (⋃ i, R i) = ⋃ i, relSym L (F i) (R i) := by
  simp only [relSym, Set.image_iUnion]
  exact (Set.iUnion_union_distrib _ _).symm

end FirstOrder.Language
