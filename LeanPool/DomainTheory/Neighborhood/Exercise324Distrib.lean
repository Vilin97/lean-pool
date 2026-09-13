/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import LeanPool.DomainTheory.Neighborhood.Product
public import LeanPool.DomainTheory.Neighborhood.Exercise318
import LeanPool.DomainTheory.Neighborhood.Exercise319Sum
import Mathlib.Order.BooleanAlgebra.Set

/-!
# Exercise 3.24(iii)(iv) (Scott 1981, PRG-19, §3) — sum/product "isomorphisms"
that are only maps

Scott's list of isomorphisms ends with two entries and the caveat *"If some of the
above are not
true, perhaps at least some mapping relationships can be established."* Parts
(iii) and (iv) are
exactly those: with Scott's **separated** sum `𝒟₀ + 𝒟₁` (a fresh bottom `Λ` glued
below two disjoint
copies), neither

* (iii) `𝒟₀ × (𝒟₁ + 𝒟₂) ≅ (𝒟₀ × 𝒟₁) + (𝒟₀ × 𝒟₂)`, nor
* (iv)  `(𝒟₀ + 𝒟₁) → 𝒟₂ ≅ (𝒟₀ → 𝒟₂) × (𝒟₁ → 𝒟₂)`

holds as a genuine isomorphism. (For (iv): `inᵢ(⊥)` lies strictly above the sum's
bottom, so a map
`h` is *not* recoverable from `h ∘ in₀` and `h ∘ in₁` — the value `h(⊥)` is free.
For (iii): the
left side has, for each `x ∈ |𝒟₀|`, an element `⟨x, ⊥⟩` incomparable to both
cones, which the right
side lacks.)

What *is* true are the canonical **mapping relationships**:

* **(iv)** the *copairing* `[a, b] : 𝒟₀ + 𝒟₁ → 𝒟₂` with `[a,b] ∘ inᵢ = a, b`
(`copair`,
  `copair_comp_inMap₀/₁`), exhibiting `(𝒟₀→𝒟₂) × (𝒟₁→𝒟₂)` as a **retract** of
  `(𝒟₀+𝒟₁) → 𝒟₂`
  (`copairProj_copair`); and
* **(iii)** the canonical *distribution* map
  `(𝒟₀ × 𝒟₁) + (𝒟₀ × 𝒟₂) → 𝒟₀ × (𝒟₁ + 𝒟₂)` (`distribMap`), `inᵢ⟨x, u⟩ ↦ ⟨x, inᵢ
  u⟩`.

The development re-uses Exercise 3.18's injections/projections and the structural
extraction lemmas of
Exercise 3.19.
-/

@[expose] public section

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-! ### (iv) — the copairing `[a, b] : 𝒟₀ + 𝒟₁ → 𝒟₂`. -/

/-- **Exercise 3.24(iv) (Scott 1981, PRG-19).** The *copairing* `[a, b] : 𝒟₀ + 𝒟₁
→ 𝒟₂`: a left copy
`0X` is routed through `a`, a right copy `1Y` through `b`, and the basepoint `Λ`
to `⊥` (so `Λ`
relates only to `Δ₂`). -/
def copair (a : ApproximableMap V₀ V₂) (b : ApproximableMap V₁ V₂) :
    ApproximableMap (sum V₀ V₁ h₀ h₁) V₂ where
  rel W Z := (sum V₀ V₁ h₀ h₁).mem W ∧ V₂.mem Z ∧
    (Z = V₂.master ∨
      (∃ X, W = inj₀ X ∧ a.rel X Z) ∨
      (∃ Y, W = inj₁ Y ∧ b.rel Y Z))
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(sum V₀ V₁ h₀ h₁).master_mem, V₂.master_mem, Or.inl rfl⟩
  inter_right := by
    rintro W Z Z' ⟨hW, _, hd⟩ ⟨_, _, hd'⟩
    have hmem : ∀ Z'' : Set γ,
        (Z'' = V₂.master ∨ (∃ X, W = inj₀ X ∧ a.rel X Z'') ∨ (∃ Y, W = inj₁ Y ∧ b.rel Y Z'')) →
        V₂.mem Z'' := by
      rintro Z'' (rfl | ⟨_, _, hf⟩ | ⟨_, _, hg⟩)
      · exact V₂.master_mem
      · exact a.rel_cod hf
      · exact b.rel_cod hg
    have key : Z ∩ Z' = V₂.master ∨ (∃ X, W = inj₀ X ∧ a.rel X (Z ∩ Z')) ∨
        (∃ Y, W = inj₁ Y ∧ b.rel Y (Z ∩ Z')) := by
      rcases hd with rfl | ⟨X, hWX, hf⟩ | ⟨Y, hWY, hg⟩
      · rw [Set.inter_eq_right.mpr (V₂.sub_master (hmem _ hd'))]; exact hd'
      · rcases hd' with rfl | ⟨X', hWX', hf'⟩ | ⟨Y', hWY', hg'⟩
        · rw [Set.inter_eq_left.mpr (V₂.sub_master (a.rel_cod hf))]
          exact Or.inr (Or.inl ⟨X, hWX, hf⟩)
        · obtain rfl : X = X' := inj₀_injective (hWX ▸ hWX')
          exact Or.inr (Or.inl ⟨X, hWX, a.inter_right hf hf'⟩)
        · exact absurd (hWX ▸ hWY' : (inj₀ X : Set _) = inj₁ Y')
            (fun h => not_inj₀_subset_inj₁ (h₀ X (a.rel_dom hf)) h.subset)
      · rcases hd' with rfl | ⟨X', hWX', hf'⟩ | ⟨Y', hWY', hg'⟩
        · rw [Set.inter_eq_left.mpr (V₂.sub_master (b.rel_cod hg))]
          exact Or.inr (Or.inr ⟨Y, hWY, hg⟩)
        · exact absurd (hWY ▸ hWX' : (inj₁ Y : Set _) = inj₀ X')
            (fun h => not_inj₁_subset_inj₀ (h₁ Y (b.rel_dom hg)) h.subset)
        · obtain rfl : Y = Y' := inj₁_injective (hWY ▸ hWY')
          exact Or.inr (Or.inr ⟨Y, hWY, b.inter_right hg hg'⟩)
    exact ⟨hW, hmem _ key, key⟩
  mono := by
    rintro W W₂ Z Z' ⟨_, _, hd⟩ hW₂W hZZ' hW₂ hZ'
    refine ⟨hW₂, hZ', ?_⟩
    rcases hd with rfl | ⟨X, rfl, hf⟩ | ⟨Y, rfl, hg⟩
    · left; exact Set.Subset.antisymm (V₂.sub_master hZ') hZZ'
    · obtain ⟨X₂, hX₂, rfl⟩ := mem_subset_inj₀ hW₂ hW₂W
      exact Or.inr (Or.inl ⟨X₂, rfl, a.mono hf (inj₀_subset_inj₀.mp hW₂W) hZZ' hX₂ hZ'⟩)
    · obtain ⟨Y₂, hY₂, rfl⟩ := mem_subset_inj₁ hW₂ hW₂W
      exact Or.inr (Or.inr ⟨Y₂, rfl, b.mono hg (inj₁_subset_inj₁.mp hW₂W) hZZ' hY₂ hZ'⟩)

@[simp] theorem copair_rel {a : ApproximableMap V₀ V₂} {b : ApproximableMap V₁ V₂}
    {W : Set (Option (α ⊕ β))} {Z : Set γ} :
    (copair (h₀ := h₀) (h₁ := h₁) a b).rel W Z ↔ (sum V₀ V₁ h₀ h₁).mem W ∧ V₂.mem Z ∧
      (Z = V₂.master ∨ (∃ X, W = inj₀ X ∧ a.rel X Z) ∨ (∃ Y, W = inj₁ Y ∧ b.rel Y Z)) := Iff.rfl

/-- **Exercise 3.24(iv) (Scott 1981, PRG-19).** `[a, b] ∘ in₀ = a`. -/
theorem copair_comp_inMap₀ (a : ApproximableMap V₀ V₂) (b : ApproximableMap V₁ V₂) :
    (copair (h₀ := h₀) (h₁ := h₁) a b).comp inMap₀ = a := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · rintro ⟨W, ⟨hX, _, hinj⟩, _, hZ, hd⟩
    rcases hd with rfl | ⟨X', hWX', hf⟩ | ⟨Y', hWY', hg⟩
    · exact a.rel_master hX
    · exact a.mono hf (inj₀_subset_inj₀.mp (hWX' ▸ hinj)) subset_rfl hX hZ
    · exact (not_inj₀_subset_inj₁ (h₀ X hX) (hWY' ▸ hinj)).elim
  · intro hf
    exact ⟨inj₀ X, ⟨a.rel_dom hf, Or.inr (Or.inl ⟨X, a.rel_dom hf, rfl⟩), subset_rfl⟩,
      Or.inr (Or.inl ⟨X, a.rel_dom hf, rfl⟩), a.rel_cod hf,
      Or.inr (Or.inl ⟨X, rfl, hf⟩)⟩

/-- **Exercise 3.24(iv) (Scott 1981, PRG-19).** `[a, b] ∘ in₁ = b`. -/
theorem copair_comp_inMap₁ (a : ApproximableMap V₀ V₂) (b : ApproximableMap V₁ V₂) :
    (copair (h₀ := h₀) (h₁ := h₁) a b).comp inMap₁ = b := by
  apply ApproximableMap.ext
  intro Y Z
  constructor
  · rintro ⟨W, ⟨hY, _, hinj⟩, _, hZ, hd⟩
    rcases hd with rfl | ⟨X', hWX', hf⟩ | ⟨Y', hWY', hg⟩
    · exact b.rel_master hY
    · exact (not_inj₁_subset_inj₀ (h₁ Y hY) (hWX' ▸ hinj)).elim
    · exact b.mono hg (inj₁_subset_inj₁.mp (hWY' ▸ hinj)) subset_rfl hY hZ
  · intro hg
    exact ⟨inj₁ Y, ⟨b.rel_dom hg, Or.inr (Or.inr ⟨Y, b.rel_dom hg, rfl⟩), subset_rfl⟩,
      Or.inr (Or.inr ⟨Y, b.rel_dom hg, rfl⟩), b.rel_cod hg,
      Or.inr (Or.inr ⟨Y, rfl, hg⟩)⟩

/-- The canonical comparison `Hom(𝒟₀+𝒟₁, 𝒟₂) → Hom(𝒟₀,𝒟₂) × Hom(𝒟₁,𝒟₂)`, `h ↦
(h∘in₀, h∘in₁)`. -/
def copairProj (h : ApproximableMap (sum V₀ V₁ h₀ h₁) V₂) :
    ApproximableMap V₀ V₂ × ApproximableMap V₁ V₂ :=
  (h.comp inMap₀, h.comp inMap₁)

/-- **Exercise 3.24(iv) (Scott 1981, PRG-19).** `(𝒟₀→𝒟₂) × (𝒟₁→𝒟₂)` is a
**retract** of
`(𝒟₀+𝒟₁) → 𝒟₂`: the copairing is a section of `h ↦ (h∘in₀, h∘in₁)`. (It is *not*
an isomorphism: the
value of a map on the basepoint `Λ` is not recoverable from its restrictions to
the two copies.) -/
theorem copairProj_copair (a : ApproximableMap V₀ V₂) (b : ApproximableMap V₁ V₂) :
    copairProj (h₀ := h₀) (h₁ := h₁) (copair a b) = (a, b) := by
  change ((copair (h₀ := h₀) (h₁ := h₁) a b).comp inMap₀,
        (copair (h₀ := h₀) (h₁ := h₁) a b).comp inMap₁) = (a, b)
  rw [copair_comp_inMap₀, copair_comp_inMap₁]

/-! ### (iii) — the canonical distribution map. -/

/-- A product neighbourhood over non-empty factors is non-empty. -/
theorem prod_mem_nonempty (hn₀ : ∀ X, V₀.mem X → X.Nonempty) (_hn₁ : ∀ Y, V₁.mem Y → Y.Nonempty)
    (W : Set (α ⊕ β)) (hW : (prod V₀ V₁).mem W) : W.Nonempty := by
  obtain ⟨X, Y, hX, _, rfl⟩ := hW
  obtain ⟨a, ha⟩ := hn₀ X hX
  exact ⟨Sum.inl a, mem_prodNbhd_inl.mpr ha⟩

/-- **Exercise 3.24(iii) (Scott 1981, PRG-19).** The canonical *distribution*
approximable map
`(𝒟₀ × 𝒟₁) + (𝒟₀ × 𝒟₂) → 𝒟₀ × (𝒟₁ + 𝒟₂)`, `inᵢ⟨x, u⟩ ↦ ⟨x, inᵢ u⟩`. (This
direction always exists;
the reverse map / isomorphism does not, since the left side has an element `⟨x,
⊥⟩` for each `x`.) -/
def distribMap (hn₀ : ∀ X, V₀.mem X → X.Nonempty) (hn₁ : ∀ Y, V₁.mem Y → Y.Nonempty)
    (hn₂ : ∀ Z, V₂.mem Z → Z.Nonempty) :
    ApproximableMap
      (sum (prod V₀ V₁) (prod V₀ V₂) (prod_mem_nonempty hn₀ hn₁) (prod_mem_nonempty hn₀ hn₂))
      (prod V₀ (sum V₁ V₂ hn₁ hn₂)) :=
  copair
    (paired (proj₀ V₀ V₁) ((inMap₀ (h₀ := hn₁) (h₁ := hn₂)).comp (proj₁ V₀ V₁)))
    (paired (proj₀ V₀ V₂) ((inMap₁ (h₀ := hn₁) (h₁ := hn₂)).comp (proj₁ V₀ V₂)))

end Domain.Neighborhood
