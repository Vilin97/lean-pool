/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Lemma615
import LeanPool.DomainTheory.Neighborhood.Proposition612
import Mathlib.Data.Fintype.Powerset

/-!
# Exercise 6.28 (Scott 1981, PRG-19, §6) — Plotkin's finite
Cantor–Schröder–Bernstein

> **EXERCISE 6.28.** (Suggested by G. Plotkin). Show that if `𝒟` and `ℰ` are
*finite* systems and
> `𝒟 ⊴ ℰ ⊴ 𝒟`, then `𝒟 ≅ ℰ`. Need the same be true of infinite systems?

Here `⊴` is Scott's *embeds-as-a-subdomain* relation of Lemma 6.15: `D ⊴ E` means
`D ≅ᴰ D'` for
some subdomain `D' ◁ E`.

## The argument

The whole proof rests on a single observation: **`D ⊴ E` already supplies an order
embedding of
element domains `|D| ↪o |E|`** (`Trianglelefteq.elementEmbedding`). Indeed,
unfolding `⊴` gives an
order isomorphism `e : |D| ≃o |D'|` onto a subdomain `D' ◁ E`, and Proposition
6.12 turns `D' ◁ E`
into a projection pair `i : D' → E`, `j : E → D'` with `j ∘ i = I`. The
element-wise map `i(·)` is
then an order embedding (`projElementEmbedding`): it is monotone
(`toElementMap_mono`), and `j(·)`
is a monotone left inverse, so `i(a) ⊑ i(b) → j(i(a)) ⊑ j(i(b)) → a ⊑ b`. Compose
with `e`.

For **finite** domains, mutual order embeddings force an isomorphism
(`orderIso_of_embeddings`): each embedding is injective, so the two finite element
types have equal
cardinality, whence either embedding is a bijection — a surjective
strictly-monotone map, i.e. an
order isomorphism. This is the finite Cantor–Schröder–Bernstein, and it is exactly
what Plotkin's
hint exploits. (The retraction structure of `⊴` is *stronger* than a mere
embedding, but the proof
only needs the embedding.)

"Finite system" is read faithfully as *finitely many neighbourhoods*
(`NeighborhoodSystem.IsFinite`); this yields `Finite |D|`
(`finite_element_of_isFinite`) because a
filter is pinned down by which of the finitely many neighbourhoods it contains.

**Need the same be true of infinite systems?** **No.** Plotkin's hint is the
finite cardinality
count above; it has no infinite analogue. Mutual *retracts* of dcpos need not be
isomorphic — the
analogue of Cantor–Schröder–Bernstein fails for the retraction preorder once the
domains are
infinite (a Eilenberg-swindle-style obstruction). Only the finite statement is
formalized here; the
infinite counterexample is recorded as prose, outside this file's scope.

Everything is **choice-free at the relational core** (`projElementEmbedding`,
`elementEmbedding` audit to `{propext, Quot.sound}`); the finite count
(`orderIso_of_embeddings`, hence the main theorems) uses `Classical.choice` —
genuinely
unavoidable, as it extracts a `Fintype` from `Finite` and a surjection's section.
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-! ## An order embedding `|D| ↪o |E|` from a projection pair / from `⊴` -/

/-- **The element-wise map of an injection `i` is an order embedding.** Given
approximable maps
`i : D → E`, `j : E → D` with `j ∘ i = I_D`, the map `x ↦ i(x)` on elements is an
order embedding
`|D| ↪o |E|`: monotone by `toElementMap_mono`, and order-reflecting because `j(·)`
is a monotone
left inverse (`j(i(x)) = x`). Choice-free. -/
def projElementEmbedding {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
    (i : ApproximableMap D E) (j : ApproximableMap E D) (hji : j.comp i = idMap D) :
    D.Element ↪o E.Element :=
  OrderEmbedding.ofMapLEIff i.toElementMap (by
    have hround : ∀ x : D.Element, j.toElementMap (i.toElementMap x) = x := by
      intro x; rw [← toElementMap_comp, hji, toElementMap_idMap]
    intro a b
    constructor
    · intro h
      have hjm := toElementMap_mono j h
      rwa [hround a, hround b] at hjm
    · intro h
      exact toElementMap_mono i h)

/-- **`D ⊴ E` yields an order embedding `|D| ↪o |E|`.** Unfold `⊴` to an iso `|D|
≅o |D'|` onto a
subdomain `D' ◁ E`, turn `D' ◁ E` into Proposition 6.12's projection pair, and
compose its
injection embedding with the iso. Choice-free. -/
theorem Trianglelefteq.elementEmbedding (h : D ⊴ E) :
    Nonempty (D.Element ↪o E.Element) := by
  obtain ⟨D', hsub, ⟨e⟩⟩ := h
  exact ⟨e.toOrderEmbedding.trans
    (projElementEmbedding hsub.inj hsub.proj hsub.proj_comp_inj)⟩

/-! ## Finite Cantor–Schröder–Bernstein for ordered types -/

/-- **Finite Cantor–Schröder–Bernstein (order version).** Mutual order embeddings
between two
*finite* ordered types yield an order isomorphism. The embeddings are injective,
so equal finite
cardinality forces `f` to be surjective; a surjective strictly-monotone map is an
order iso. Uses
`Classical.choice` (via `Fintype`/surjection-section). -/
theorem orderIso_of_embeddings {P Q : Type*} [PartialOrder P] [PartialOrder Q]
    [Finite P] [Finite Q] (f : P ↪o Q) (g : Q ↪o P) : Nonempty (P ≃o Q) := by
  classical
  obtain ⟨_⟩ := nonempty_fintype P
  obtain ⟨_⟩ := nonempty_fintype Q
  have hcard : Fintype.card P = Fintype.card Q :=
    le_antisymm (Fintype.card_le_of_injective f f.injective)
      (Fintype.card_le_of_injective g g.injective)
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨f.injective, hcard⟩
  exact ⟨{ toEquiv := Equiv.ofBijective f hbij, map_rel_iff' := f.map_rel_iff' }⟩

/-! ## Exercise 6.28 — the finite statement -/

/-- **Exercise 6.28 (core).** If `|D|` and `|E|` are finite and `D ⊴ E ⊴ D`, then
`D ≅ᴰ E`.
The two `⊴`s give mutual order embeddings of the (finite) element domains, and
`orderIso_of_embeddings` upgrades them to an isomorphism. -/
theorem isomorphic_of_trianglelefteq_both [Finite D.Element] [Finite E.Element]
    (h₁ : D ⊴ E) (h₂ : E ⊴ D) : D ≅ᴰ E := by
  obtain ⟨f⟩ := h₁.elementEmbedding
  obtain ⟨g⟩ := h₂.elementEmbedding
  exact orderIso_of_embeddings f g

/-! ## "Finite system" = finitely many neighbourhoods -/

/-- **A neighbourhood system is *finite*** when it has only finitely many
neighbourhoods. -/
def NeighborhoodSystem.IsFinite {α : Type*} (D : NeighborhoodSystem α) : Prop :=
  Finite {X : Set α // D.mem X}

/-- **A finite system has a finite element domain.** A filter `x : |D|` is
determined by which of
the (finitely many) neighbourhoods it contains, so `x ↦ {p | x.mem p.1}` injects
`|D|` into the
finite powerset `Set {X // D.mem X}`. -/
theorem finite_element_of_isFinite {α : Type*} {D : NeighborhoodSystem α} (h : D.IsFinite) :
    Finite D.Element := by
  haveI : Finite {X : Set α // D.mem X} := h
  apply Finite.of_injective
    (β := Set {X : Set α // D.mem X}) (fun x => {p | x.mem p.1})
  intro x y hxy
  apply Element.ext
  intro X
  by_cases hX : D.mem X
  · have := Set.ext_iff.mp hxy ⟨X, hX⟩
    simpa using this
  · exact ⟨fun hmem => absurd (x.sub hmem) hX, fun hmem => absurd (y.sub hmem) hX⟩

/-- **Exercise 6.28 (Scott 1981, PRG-19; suggested by G. Plotkin).** If `𝒟` and
`ℰ` are *finite*
neighbourhood systems with `𝒟 ⊴ ℰ` and `ℰ ⊴ 𝒟`, then `𝒟 ≅ ℰ`. -/
theorem isomorphic_of_finite_system (hD : D.IsFinite) (hE : E.IsFinite)
    (h₁ : D ⊴ E) (h₂ : E ⊴ D) : D ≅ᴰ E := by
  haveI := finite_element_of_isFinite hD
  haveI := finite_element_of_isFinite hE
  exact isomorphic_of_trianglelefteq_both h₁ h₂

end Domain.Neighborhood
