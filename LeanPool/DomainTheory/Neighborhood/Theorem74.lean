/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Definition72
import LeanPool.DomainTheory.Neighborhood.Exercise319
import LeanPool.DomainTheory.Neighborhood.Exercise319Sum

/-!
# Theorem 7.4 (Scott 1981, PRG-19, §7) — `+` and `×` preserve effective givenness

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19,
Lecture VII.

> **Theorem 7.4.** If `𝒟₀` and `𝒟₁` are effectively given, then so are `(𝒟₀ + 𝒟₁)`
and `(𝒟₀ × 𝒟₁)`.
> Moreover the combinators `inᵢ`, `outᵢ`, `projᵢ` are all computable; further, if
`f` and `g` are
> computable maps, then so are `f + g` and `f × g`.

**This file: the product (`×`) half.** Scott takes `𝒟₀ × 𝒟₁ = {Xₙ⁰ ∪ Xₘ¹ ∣ n, m}`
with a one-one
pairing function `r(n, m)` and `W_k = X⁰_{p(k)} ∪ X¹_{q(k)}`; we realize `r =
Nat.pair`,
`p = ·.unpair.1`, `q = ·.unpair.2`, and the project's `prodNbhd`/`prod` (over `α ⊕
β`,
`Product.lean`). The product is *uniform* (no tag analysis), so both of Scott's
relations decompose
into **conjunctions** of the components' relations under index reindexing, handled
entirely by the
choice-free closure layer of `Recursive.lean`
(`RecDecidable.and`/`.comp`/`.of_iff`):

* `prodPresentation`, `prod_isEffectivelyGiven` — the product is effectively
given;
* `proj₀_isComputable`, `proj₁_isComputable` — `(Xₙ⁰ ∪ Xₘ¹) projᵢ Z ↔ (component)
⊆ Z` is recursively
  *decidable* (a slice of `incl_computable`), hence r.e.;
* `paired_isComputable` — `⟨f, g⟩` is computable when `f, g` are (conjunction of
two r.e. relations);
* `prodMap_isComputable` — `f × g` is computable, via `f × g = ⟨f ∘ p₀, g ∘ p₁⟩`
(Exercise 3.19) and
  `comp_isComputable` (Proposition 7.3).

The sum (`+`) half — which needs tag analysis, hence a little more choice-free
recursion theory
(truncated subtraction, equality/disjunction deciders) — is in the companion
development.

Everything here is `⊆ {propext, Quot.sound}` (choice-free).
-/

namespace Domain.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ α' β' : Type*}

/-- The product representation is determined by its two components (the `↔` form
of
`prodNbhd_injective`). -/
theorem prodNbhd_eq_iff {X X' : Set α} {Y Y' : Set β} :
    prodNbhd X Y = prodNbhd X' Y' ↔ X = X' ∧ Y = Y' :=
  ⟨prodNbhd_injective, by rintro ⟨rfl, rfl⟩; rfl⟩

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Scott's `W_k = X⁰_{p(k)} ∪ X¹_{q(k)}` with `p = ·.unpair.1`, `q = ·.unpair.2`. -/
def prodEnum (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁) (t : ℕ) :
    Set (α ⊕ β) :=
  prodNbhd (P₀.X t.unpair.1) (P₁.X t.unpair.2)

@[simp] theorem prodEnum_apply (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)
    (t : ℕ) : prodEnum P₀ P₁ t = prodNbhd (P₀.X t.unpair.1) (P₁.X t.unpair.2) := rfl

/-- **Theorem 7.4 (Scott 1981, PRG-19) — `𝒟₀ × 𝒟₁` is effectively given.** The
presentation
`W_k = X⁰_{p k} ∪ X¹_{q k}`. Scott's 7.1(i) and (ii) each split, via
`prodNbhd_inter` /
`prodNbhd_subset_iff`, into the *conjunction* of the two factors' relations on the
projected
indices — recursively decidable by `RecDecidable.and`/`.comp`/`.of_iff`. -/
def prodPresentation (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁) :
    ComputablePresentation (prod V₀ V₁) where
  X := prodEnum P₀ P₁
  mem_X t := prod_mem_prodNbhd (P₀.mem_X _) (P₁.mem_X _)
  surj := by
    rintro Z ⟨X, Y, hX, hY, rfl⟩
    obtain ⟨n, rfl⟩ := P₀.surj hX
    obtain ⟨m, rfl⟩ := P₁.surj hY
    exact ⟨Nat.pair n m, by simp only [prodEnum_apply, unpair_pair_fst, unpair_pair_snd]⟩
  interEq_computable := by
    have hIE0 : RecDecidable (fun s => P₀.X s.unpair.1 ∩ P₀.X s.unpair.2.unpair.1
        = P₀.X s.unpair.2.unpair.2) := P₀.interEq_computable
    have hIE1 : RecDecidable (fun s => P₁.X s.unpair.1 ∩ P₁.X s.unpair.2.unpair.1
        = P₁.X s.unpair.2.unpair.2) := P₁.interEq_computable
    have hg0 : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.1
        (Nat.pair t.unpair.2.unpair.1.unpair.1 t.unpair.2.unpair.2.unpair.1)) :=
      (Nat.Primrec.left.comp Nat.Primrec.left).pair
        ((Nat.Primrec.left.comp (Nat.Primrec.left.comp Nat.Primrec.right)).pair
          (Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right)))
    have hg1 : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.2
        (Nat.pair t.unpair.2.unpair.1.unpair.2 t.unpair.2.unpair.2.unpair.2)) :=
      (Nat.Primrec.right.comp Nat.Primrec.left).pair
        ((Nat.Primrec.right.comp (Nat.Primrec.left.comp Nat.Primrec.right)).pair
          (Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right)))
    refine RecDecidable.of_iff (fun t => ?_) ((hIE0.comp hg0).and (hIE1.comp hg1))
    simp only [prodEnum_apply, unpair_pair_fst, unpair_pair_snd, prodNbhd_inter, prodNbhd_eq_iff]
  cons_computable := by
    have hC0 : RecDecidable (fun s => ∃ k, P₀.X k ⊆ P₀.X s.unpair.1 ∩ P₀.X s.unpair.2) :=
      P₀.cons_computable
    have hC1 : RecDecidable (fun s => ∃ k, P₁.X k ⊆ P₁.X s.unpair.1 ∩ P₁.X s.unpair.2) :=
      P₁.cons_computable
    have hh0 : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.1 t.unpair.2.unpair.1) :=
      (Nat.Primrec.left.comp Nat.Primrec.left).pair (Nat.Primrec.left.comp Nat.Primrec.right)
    have hh1 : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.2 t.unpair.2.unpair.2) :=
      (Nat.Primrec.right.comp Nat.Primrec.left).pair (Nat.Primrec.right.comp Nat.Primrec.right)
    refine RecDecidable.of_iff (fun t => ?_) ((hC0.comp hh0).and (hC1.comp hh1))
    simp only [prodEnum_apply, unpair_pair_fst, unpair_pair_snd, prodNbhd_inter,
      prodNbhd_subset_iff]
    constructor
    · rintro ⟨k, hk0, hk1⟩
      exact ⟨⟨k.unpair.1, hk0⟩, ⟨k.unpair.2, hk1⟩⟩
    · rintro ⟨⟨k0, hk0⟩, ⟨k1, hk1⟩⟩
      exact ⟨Nat.pair k0 k1, by simpa only [unpair_pair_fst] using hk0,
        by simpa only [unpair_pair_snd] using hk1⟩
  inter n m := Nat.pair (P₀.inter n.unpair.1 m.unpair.1) (P₁.inter n.unpair.2 m.unpair.2)
  inter_primrec := by
    have h0 : Nat.Primrec (fun t => P₀.inter t.unpair.1.unpair.1 t.unpair.2.unpair.1) :=
      (P₀.inter_primrec.comp ((Nat.Primrec.left.comp Nat.Primrec.left).pair
        (Nat.Primrec.left.comp Nat.Primrec.right))).of_eq fun t => by
          simp only [unpair_pair_fst, unpair_pair_snd]
    have h1 : Nat.Primrec (fun t => P₁.inter t.unpair.1.unpair.2 t.unpair.2.unpair.2) :=
      (P₁.inter_primrec.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair
        (Nat.Primrec.right.comp Nat.Primrec.right))).of_eq fun t => by
          simp only [unpair_pair_fst, unpair_pair_snd]
    exact h0.pair h1
  inter_spec := by
    rintro n m ⟨k, hk⟩
    simp only [prodEnum_apply, unpair_pair_fst, unpair_pair_snd] at hk ⊢
    rw [prodNbhd_inter] at hk ⊢
    obtain ⟨h0, h1⟩ := prodNbhd_subset_iff.mp hk
    rw [P₀.inter_spec ⟨_, h0⟩, P₁.inter_spec ⟨_, h1⟩]
  masterIdx := Nat.pair P₀.masterIdx P₁.masterIdx
  masterIdx_spec := by
    simp only [prodEnum_apply, unpair_pair_fst, unpair_pair_snd, P₀.masterIdx_spec,
      P₁.masterIdx_spec, prod_master]

@[simp] theorem prodPresentation_X (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)
    (t : ℕ) :
    (prodPresentation P₀ P₁).X t = prodNbhd (P₀.X t.unpair.1) (P₁.X t.unpair.2) := rfl

/-- **Theorem 7.4 (Scott 1981, PRG-19).** The product of effectively given domains
is effectively
given. -/
theorem prod_isEffectivelyGiven (h₀ : V₀.IsEffectivelyGiven) (h₁ : V₁.IsEffectivelyGiven) :
    (prod V₀ V₁).IsEffectivelyGiven := by
  obtain ⟨P₀⟩ := h₀; obtain ⟨P₁⟩ := h₁
  exact ⟨prodPresentation P₀ P₁⟩

/-- **Theorem 7.4 (Scott 1981, PRG-19) — `proj₀` is computable.** `(Xₙ⁰ ∪ Xₘ¹) p₀
X⁰_k ↔ Xₙ⁰ ⊆
X⁰_k`,
a recursive slice of `incl_computable`, hence r.e. -/
theorem proj₀_isComputable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁) :
    IsComputableMap (prodPresentation P₀ P₁) P₀ (proj₀ V₀ V₁) := by
  have hincl : RecDecidable (fun s => P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2) := P₀.incl_computable
  have hr : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.1 t.unpair.2) :=
    (Nat.Primrec.left.comp Nat.Primrec.left).pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun t => ?_) (hincl.comp hr)).re
  simp only [prodPresentation_X, proj₀_rel, inl_preimage_prodNbhd, unpair_pair_fst, unpair_pair_snd]
  exact ⟨fun h => h.2.2,
    fun h => ⟨prod_mem_prodNbhd (P₀.mem_X _) (P₁.mem_X _), P₀.mem_X _, h⟩⟩

/-- **Theorem 7.4 (Scott 1981, PRG-19) — `proj₁` is computable.** `(Xₙ⁰ ∪ Xₘ¹) p₁
X¹_k ↔ Xₘ¹ ⊆ X¹_k`
(Scott's worked example), a recursive slice of `incl_computable`. -/
theorem proj₁_isComputable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁) :
    IsComputableMap (prodPresentation P₀ P₁) P₁ (proj₁ V₀ V₁) := by
  have hincl : RecDecidable (fun s => P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2) := P₁.incl_computable
  have hr : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.2 t.unpair.2) :=
    (Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun t => ?_) (hincl.comp hr)).re
  simp only [prodPresentation_X, proj₁_rel, inr_preimage_prodNbhd, unpair_pair_fst, unpair_pair_snd]
  exact ⟨fun h => h.2.2,
    fun h => ⟨prod_mem_prodNbhd (P₀.mem_X _) (P₁.mem_X _), P₁.mem_X _, h⟩⟩

/-- **Theorem 7.4 (Scott 1981, PRG-19) — the paired map `⟨f, g⟩` is computable.**
`Zₙ ⟨f, g⟩ (X⁰_k ∪
X¹_l) ↔ Zₙ f X⁰_k ∧ Zₙ g X¹_l`, the conjunction of two r.e. relations. -/
theorem paired_isComputable {V₂ : NeighborhoodSystem γ}
    {P₂ : ComputablePresentation V₂} {P₀ : ComputablePresentation V₀}
    {P₁ : ComputablePresentation V₁} {a : ApproximableMap V₂ V₀} {b : ApproximableMap V₂ V₁}
    (ha : IsComputableMap P₂ P₀ a) (hb : IsComputableMap P₂ P₁ b) :
    IsComputableMap P₂ (prodPresentation P₀ P₁) (paired a b) := by
  have ha' : REPred (fun s => a.rel (P₂.X s.unpair.1) (P₀.X s.unpair.2)) := ha
  have hb' : REPred (fun s => b.rel (P₂.X s.unpair.1) (P₁.X s.unpair.2)) := hb
  have hra : Nat.Primrec (fun t => Nat.pair t.unpair.1 t.unpair.2.unpair.1) :=
    Nat.Primrec.left.pair (Nat.Primrec.left.comp Nat.Primrec.right)
  have hrb : Nat.Primrec (fun t => Nat.pair t.unpair.1 t.unpair.2.unpair.2) :=
    Nat.Primrec.left.pair (Nat.Primrec.right.comp Nat.Primrec.right)
  refine REPred.of_iff (fun t => ?_) ((ha'.comp hra).and (hb'.comp hrb))
  simp only [prodPresentation_X, paired_rel, inl_preimage_prodNbhd, inr_preimage_prodNbhd,
    unpair_pair_fst, unpair_pair_snd]
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩,
    fun h => ⟨prod_mem_prodNbhd (P₀.mem_X _) (P₁.mem_X _), h.1, h.2⟩⟩

/-- **Theorem 7.4 (Scott 1981, PRG-19) — the product functor `f × g` is
computable.** Using
`f × g = ⟨f ∘ p₀, g ∘ p₁⟩` (Exercise 3.19) together with computability of `projᵢ`
and `comp`
(Proposition 7.3). -/
theorem prodMap_isComputable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
    {P₀ : ComputablePresentation V₀} {P₁ : ComputablePresentation V₁}
    {P₀' : ComputablePresentation V₀'} {P₁' : ComputablePresentation V₁'}
    {f : ApproximableMap V₀ V₀'} {g : ApproximableMap V₁ V₁'}
    (hf : IsComputableMap P₀ P₀' f) (hg : IsComputableMap P₁ P₁' g) :
    IsComputableMap (prodPresentation P₀ P₁) (prodPresentation P₀' P₁') (prodMap f g) := by
  rw [prodMap]
  exact paired_isComputable (comp_isComputable (proj₀_isComputable P₀ P₁) hf)
    (comp_isComputable (proj₁_isComputable P₀ P₁) hg)

/-! ## The sum (`+`) half of Theorem 7.4

The sum `𝒟₀ + 𝒟₁` (`Exercise318.lean`, over `Option (α ⊕ β)`) has *three* kinds of
neighbourhood —
the master `{Λ}∪0Δ₀∪1Δ₁`, the left copies `0X`, the right copies `1Y` — so its
presentation deciders
require a genuine tag analysis (Scott: "the neighbourhood relations have to be
worked out in terms of
the indices … recursively enumerable relations … closure under conjunctions,
disjunctions, …"). We
enumerate with a `Nat.pair` tag: `tag 0 ↦ 0X⁰ₖ`, `tag 1 ↦ 1X¹ₖ`, `tag ≥ 2 ↦`
master. -/

/-- Choice-free three-way split of a tag `n ∈ {0, 1, ≥2}` (via `Nat.decEq`, not
classical `em`). -/
theorem tag_trichotomy (n : ℕ) : n = 0 ∨ n = 1 ∨ (n ≠ 0 ∧ n ≠ 1) := by
  rcases Nat.decEq n 0 with h | h
  · rcases Nat.decEq n 1 with h' | h'
    · exact Or.inr (Or.inr ⟨h, h'⟩)
    · exact Or.inr (Or.inl h')
  · exact Or.inl h

section Sum

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- Scott's `Z₀ = Δ, Z_{2n+1} = X⁰ₙ, Z_{2n+2} = X¹ₙ`, realized with a `Nat.pair`
tag: `tag = 0 ↦
0X⁰`,
`tag = 1 ↦ 1X¹`, else the master. -/
def sumEnum (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁) (t : ℕ) :
    Set (Option (α ⊕ β)) :=
  if t.unpair.1 = 0 then inj₀ (P₀.X t.unpair.2)
  else if t.unpair.1 = 1 then inj₁ (P₁.X t.unpair.2)
  else sumMaster V₀ V₁

variable {P₀ : ComputablePresentation V₀} {P₁ : ComputablePresentation V₁}

@[simp] theorem sumEnum_zero {t : ℕ} (h : t.unpair.1 = 0) :
    sumEnum P₀ P₁ t = inj₀ (P₀.X t.unpair.2) := by unfold sumEnum; rw [if_pos h]

@[simp] theorem sumEnum_one {t : ℕ} (h : t.unpair.1 = 1) :
    sumEnum P₀ P₁ t = inj₁ (P₁.X t.unpair.2) := by
  have h0 : t.unpair.1 ≠ 0 := by omega
  unfold sumEnum; rw [if_neg h0, if_pos h]

theorem sumEnum_master {t : ℕ} (h0 : t.unpair.1 ≠ 0) (h1 : t.unpair.1 ≠ 1) :
    sumEnum P₀ P₁ t = sumMaster V₀ V₁ := by unfold sumEnum; rw [if_neg h0, if_neg h1]

theorem sumEnum_mem (t : ℕ) : (sum V₀ V₁ h₀ h₁).mem (sumEnum P₀ P₁ t) := by
  unfold sumEnum
  split
  · exact Or.inr (Or.inl ⟨_, P₀.mem_X _, rfl⟩)
  · split
    · exact Or.inr (Or.inr ⟨_, P₁.mem_X _, rfl⟩)
    · exact Or.inl rfl

include h₀ h₁ in
theorem sumEnum_nonempty (t : ℕ) : (sumEnum P₀ P₁ t).Nonempty := by
  unfold sumEnum
  split
  · exact inj₀_nonempty (h₀ _ (P₀.mem_X _))
  · split
    · exact inj₁_nonempty (h₁ _ (P₁.mem_X _))
    · exact ⟨none, none_mem_sumMaster⟩

/-! ### Distinctness of the three neighbourhood kinds (uses non-emptiness). -/

theorem inj₀_eq_iff {A B : Set α} : (inj₀ A : Set (Option (α ⊕ β))) = inj₀ B ↔ A = B :=
  ⟨inj₀_injective, fun h => h ▸ rfl⟩

theorem inj₁_eq_iff {A B : Set β} : (inj₁ A : Set (Option (α ⊕ β))) = inj₁ B ↔ A = B :=
  ⟨inj₁_injective, fun h => h ▸ rfl⟩

theorem inj₀_ne_sumMaster {A : Set α} : (inj₀ A : Set (Option (α ⊕ β))) ≠ sumMaster V₀ V₁ :=
  fun h => none_mem_inj₀ (h.symm ▸ none_mem_sumMaster)

theorem inj₁_ne_sumMaster {B : Set β} : (inj₁ B : Set (Option (α ⊕ β))) ≠ sumMaster V₀ V₁ :=
  fun h => none_mem_inj₁ (h.symm ▸ none_mem_sumMaster)

theorem inj₀_ne_inj₁_of_nonempty {A : Set α} {B : Set β} (hB : B.Nonempty) :
    (inj₀ A : Set (Option (α ⊕ β))) ≠ inj₁ B := by
  rintro h; obtain ⟨b, hb⟩ := hB
  exact ir_mem_inj₀ (h.symm ▸ ir_mem_inj₁.mpr hb)

include h₁ in
/-- **Equality of two sum-neighbourhoods, in the indices.** Both master, or same
tag with equal
component. -/
theorem sumEnum_eq_iff (x y : ℕ) :
    sumEnum P₀ P₁ x = sumEnum P₀ P₁ y ↔
      ((x.unpair.1 ≠ 0 ∧ x.unpair.1 ≠ 1) ∧ (y.unpair.1 ≠ 0 ∧ y.unpair.1 ≠ 1))
        ∨ (((x.unpair.1 = 0 ∧ y.unpair.1 = 0) ∧ P₀.X x.unpair.2 = P₀.X y.unpair.2)
          ∨ ((x.unpair.1 = 1 ∧ y.unpair.1 = 1) ∧ P₁.X x.unpair.2 = P₁.X y.unpair.2)) := by
  rcases tag_trichotomy x.unpair.1 with hx | hx | ⟨hx0, hx1⟩ <;>
    rcases tag_trichotomy y.unpair.1 with hy | hy | ⟨hy0, hy1⟩
  · -- x0 y0
    rw [sumEnum_zero hx, sumEnum_zero hy, inj₀_eq_iff]
    constructor
    · intro he; exact Or.inr (Or.inl ⟨⟨hx, hy⟩, he⟩)
    · rintro (⟨⟨e1, e2⟩, _⟩ | ⟨_, he⟩ | ⟨⟨e1, e2⟩, _⟩)
      · exfalso; omega
      · exact he
      · exfalso; omega
  · -- x0 y1
    rw [sumEnum_zero hx, sumEnum_one hy]
    constructor
    · intro h; exact absurd h (inj₀_ne_inj₁_of_nonempty (h₁ _ (P₁.mem_X _)))
    · rintro (⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩) <;> exfalso <;> omega
  · -- x0 yM
    rw [sumEnum_zero hx, sumEnum_master hy0 hy1]
    constructor
    · intro h; exact absurd h inj₀_ne_sumMaster
    · rintro (⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩) <;> exfalso <;> omega
  · -- x1 y0
    rw [sumEnum_one hx, sumEnum_zero hy]
    constructor
    · intro h; exact absurd h.symm (inj₀_ne_inj₁_of_nonempty (h₁ _ (P₁.mem_X _)))
    · rintro (⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩) <;> exfalso <;> omega
  · -- x1 y1
    rw [sumEnum_one hx, sumEnum_one hy, inj₁_eq_iff]
    constructor
    · intro he; exact Or.inr (Or.inr ⟨⟨hx, hy⟩, he⟩)
    · rintro (⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩ | ⟨_, he⟩)
      · exfalso; omega
      · exfalso; omega
      · exact he
  · -- x1 yM
    rw [sumEnum_one hx, sumEnum_master hy0 hy1]
    constructor
    · intro h; exact absurd h inj₁_ne_sumMaster
    · rintro (⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩) <;> exfalso <;> omega
  · -- xM y0
    rw [sumEnum_master hx0 hx1, sumEnum_zero hy]
    constructor
    · intro h; exact absurd h.symm inj₀_ne_sumMaster
    · rintro (⟨⟨e1, e2⟩, ⟨e3, e4⟩⟩ | ⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩) <;> exfalso <;> omega
  · -- xM y1
    rw [sumEnum_master hx0 hx1, sumEnum_one hy]
    constructor
    · intro h; exact absurd h.symm inj₁_ne_sumMaster
    · rintro (⟨⟨e1, e2⟩, ⟨e3, e4⟩⟩ | ⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩) <;> exfalso <;> omega
  · -- xM yM
    rw [sumEnum_master hx0 hx1, sumEnum_master hy0 hy1]
    exact ⟨fun _ => Or.inl ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩, fun _ => rfl⟩

/-- Equality of two enumerated `𝒟₀`-neighbourhoods is recursively decidable
(antisymmetry of `⊆`,
decided by `incl_computable`). -/
theorem recDec_setEq₀ {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    RecDecidable (fun u => P₀.X (f u) = P₀.X (g u)) := by
  have hincl : RecDecidable (fun s => P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2) := P₀.incl_computable
  refine RecDecidable.of_iff (fun u => ?_) ((hincl.comp (hf.pair hg)).and (hincl.comp (hg.pair hf)))
  simp only [unpair_pair_fst, unpair_pair_snd]
  exact ⟨fun h => ⟨h.subset, h.symm.subset⟩, fun ⟨h1, h2⟩ => Set.Subset.antisymm h1 h2⟩

theorem recDec_setEq₁ {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    RecDecidable (fun u => P₁.X (f u) = P₁.X (g u)) := by
  have hincl : RecDecidable (fun s => P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2) := P₁.incl_computable
  refine RecDecidable.of_iff (fun u => ?_) ((hincl.comp (hf.pair hg)).and (hincl.comp (hg.pair hf)))
  simp only [unpair_pair_fst, unpair_pair_snd]
  exact ⟨fun h => ⟨h.subset, h.symm.subset⟩, fun ⟨h1, h2⟩ => Set.Subset.antisymm h1 h2⟩

include h₁ in
/-- **`sumEnum u.1 = sumEnum u.2` is recursively decidable** (the `of_iff`
translation of
`sumEnum_eq_iff` into the tag/component deciders). -/
theorem eqSEdec :
    RecDecidable (fun u => sumEnum P₀ P₁ u.unpair.1 = sumEnum P₀ P₁ u.unpair.2) := by
  have hX0 : RecDecidable (fun u => u.unpair.1.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 0)
  have hX1 : RecDecidable (fun u => u.unpair.1.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 1)
  have hY0 : RecDecidable (fun u => u.unpair.2.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 0)
  have hY1 : RecDecidable (fun u => u.unpair.2.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 1)
  have hE0 : RecDecidable (fun u => P₀.X u.unpair.1.unpair.2 = P₀.X u.unpair.2.unpair.2) :=
    recDec_setEq₀ (Nat.Primrec.right.comp Nat.Primrec.left) (
      Nat.Primrec.right.comp Nat.Primrec.right)
  have hE1 : RecDecidable (fun u => P₁.X u.unpair.1.unpair.2 = P₁.X u.unpair.2.unpair.2) :=
    recDec_setEq₁ (Nat.Primrec.right.comp Nat.Primrec.left) (
      Nat.Primrec.right.comp Nat.Primrec.right)
  exact RecDecidable.of_iff (fun u => sumEnum_eq_iff (h₁ := h₁) u.unpair.1 u.unpair.2)
    (((hX0.not.and hX1.not).and (hY0.not.and hY1.not)).or
      (((hX0.and hY0).and hE0).or ((hX1.and hY1).and hE1)))

/-- A nonempty left copy cannot equal a right copy. -/
theorem inj₀_eq_inj₁_elim {A : Set α} {B : Set β} (hA : A.Nonempty)
    (h : (inj₀ A : Set (Option (α ⊕ β))) = inj₁ B) : False := by
  obtain ⟨a, ha⟩ := hA; exact il_mem_inj₁ (h ▸ il_mem_inj₀.mpr ha)

/-- Every enumerated sum-neighbourhood lies under the master (no non-emptiness
needed). -/
theorem sumEnum_subset_sumMaster (n : ℕ) :
    sumEnum P₀ P₁ n ⊆ sumMaster V₀ V₁ := by
  unfold sumEnum
  split
  · exact inj₀_subset_sumMaster (P₀.mem_X _)
  · split
    · exact inj₁_subset_sumMaster (P₁.mem_X _)
    · exact subset_rfl

/-- `M ∩ Z = Z`: the master absorbs on the left. -/
theorem sumMaster_inter_sumEnum (m : ℕ) :
    sumMaster V₀ V₁ ∩ sumEnum P₀ P₁ m = sumEnum P₀ P₁ m :=
  Set.inter_eq_right.mpr (sumEnum_subset_sumMaster m)

/-- `Z ∩ M = Z`: the master absorbs on the right. -/
theorem sumEnum_inter_sumMaster (n : ℕ) :
    sumEnum P₀ P₁ n ∩ sumMaster V₀ V₁ = sumEnum P₀ P₁ n :=
  Set.inter_eq_left.mpr (sumEnum_subset_sumMaster n)

include h₀ h₁

/-- Decidability of the sum-presentation intersection equality relation. -/
theorem sumPresentation_interEq_computable :
    RecDecidable₃ (fun n m k => sumEnum P₀ P₁ n ∩ sumEnum P₀ P₁ m = sumEnum P₀ P₁ k) := by
  have hMK : RecDecidable (fun t => sumEnum P₀ P₁ t.unpair.2.unpair.1
      = sumEnum P₀ P₁ t.unpair.2.unpair.2) := by
    refine RecDecidable.of_iff (fun t => ?_) ((eqSEdec (P₀ := P₀) (P₁ := P₁) (h₁ := h₁)).comp
      ((Nat.Primrec.left.comp Nat.Primrec.right).pair (Nat.Primrec.right.comp Nat.Primrec.right)))
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hNK : RecDecidable (fun t => sumEnum P₀ P₁ t.unpair.1
      = sumEnum P₀ P₁ t.unpair.2.unpair.2) := by
    refine RecDecidable.of_iff (fun t => ?_) ((eqSEdec (P₀ := P₀) (P₁ := P₁) (h₁ := h₁)).comp
      (Nat.Primrec.left.pair (Nat.Primrec.right.comp Nat.Primrec.right)))
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hA0 : RecDecidable (fun t => t.unpair.1.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 0)
  have hA1 : RecDecidable (fun t => t.unpair.1.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 1)
  have hB0 : RecDecidable (fun t => t.unpair.2.unpair.1.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp (Nat.Primrec.left.comp Nat.Primrec.right))
      (Nat.Primrec.const 0)
  have hB1 : RecDecidable (fun t => t.unpair.2.unpair.1.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp (Nat.Primrec.left.comp Nat.Primrec.right))
      (Nat.Primrec.const 1)
  have hC0 : RecDecidable (fun t => t.unpair.2.unpair.2.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right))
      (Nat.Primrec.const 0)
  have hC1 : RecDecidable (fun t => t.unpair.2.unpair.2.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right))
      (Nat.Primrec.const 1)
  have hg : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.2
      (Nat.pair t.unpair.2.unpair.1.unpair.2 t.unpair.2.unpair.2.unpair.2)) :=
    (Nat.Primrec.right.comp Nat.Primrec.left).pair
      ((Nat.Primrec.right.comp (Nat.Primrec.left.comp Nat.Primrec.right)).pair
        (Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right)))
  have hIE0 : RecDecidable (fun t => P₀.X t.unpair.1.unpair.2 ∩ P₀.X t.unpair.2.unpair.1.unpair.2
      = P₀.X t.unpair.2.unpair.2.unpair.2) := by
    refine RecDecidable.of_iff (fun t => ?_) (P₀.interEq_computable.comp hg)
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hIE1 : RecDecidable (fun t => P₁.X t.unpair.1.unpair.2 ∩ P₁.X t.unpair.2.unpair.1.unpair.2
      = P₁.X t.unpair.2.unpair.2.unpair.2) := by
    refine RecDecidable.of_iff (fun t => ?_) (P₁.interEq_computable.comp hg)
    simp only [unpair_pair_fst, unpair_pair_snd]
  refine RecDecidable.of_iff (fun t => ?_)
    (((hA0.not.and hA1.not).and hMK).or
      (((hB0.not.and hB1.not).and hNK).or
        ((((hA0.and hB0).and hC0).and hIE0).or
          (((hA1.and hB1).and hC1).and hIE1))))
  dsimp only
  rcases tag_trichotomy t.unpair.1.unpair.1 with hna | hna | ⟨hna0, hna1⟩
  · rcases tag_trichotomy t.unpair.2.unpair.1.unpair.1 with hnb | hnb | ⟨hnb0, hnb1⟩
    · rw [sumEnum_zero hna, sumEnum_zero hnb, inj₀_inter]
      rcases tag_trichotomy t.unpair.2.unpair.2.unpair.1 with hnc | hnc | ⟨hnc0, hnc1⟩
      · rw [sumEnum_zero hnc, inj₀_eq_iff]
        constructor
        · intro h; exact Or.inr (Or.inr (Or.inl ⟨⟨⟨hna, hnb⟩, hnc⟩, h⟩))
        · rintro (⟨⟨e1, _⟩, _⟩ | ⟨⟨e1, _⟩, _⟩ | ⟨⟨⟨_, _⟩, _⟩, h⟩ | ⟨⟨⟨e1, _⟩, _⟩, _⟩)
          · exfalso; omega
          · exfalso; omega
          · exact h
          · exfalso; omega
      · rw [sumEnum_one hnc]
        constructor
        · intro h; exact absurd h (inj₀_ne_inj₁_of_nonempty (h₁ _ (P₁.mem_X _)))
        · rintro (⟨⟨e1, _⟩, _⟩ | ⟨⟨e1, _⟩, _⟩ | ⟨⟨⟨_, _⟩, e3⟩, _⟩ |
          ⟨⟨⟨e1, _⟩, _⟩, _⟩) <;> exfalso <;> omega
      · rw [sumEnum_master hnc0 hnc1]
        constructor
        · intro h; exact absurd h inj₀_ne_sumMaster
        · rintro (⟨⟨e1, _⟩, _⟩ | ⟨⟨e1, _⟩, _⟩ | ⟨⟨⟨_, _⟩, e3⟩, _⟩ |
          ⟨⟨⟨e1, _⟩, _⟩, _⟩) <;> exfalso <;> omega
    · rw [sumEnum_zero hna, sumEnum_one hnb, inj₀_inter_inj₁]
      constructor
      · intro h
        obtain ⟨x, hx⟩ := sumEnum_nonempty (h₀ := h₀) (h₁ := h₁) t.unpair.2.unpair.2
        rw [← h] at hx
        exact absurd hx (Set.notMem_empty x)
      · rintro (⟨⟨e1, _⟩, _⟩ | ⟨⟨_, e2⟩, _⟩ | ⟨⟨⟨_, e2⟩, _⟩, _⟩ |
        ⟨⟨⟨e1, _⟩, _⟩, _⟩) <;> exfalso <;> omega
    · rw [sumEnum_master hnb0 hnb1, sumEnum_inter_sumMaster]
      constructor
      · intro h; exact Or.inr (Or.inl ⟨⟨hnb0, hnb1⟩, h⟩)
      · rintro (⟨⟨e1, _⟩, _⟩ | ⟨_, h⟩ | ⟨⟨⟨_, e2⟩, _⟩, _⟩ | ⟨⟨⟨e1, _⟩, _⟩, _⟩)
        · exfalso; omega
        · exact h
        · exfalso; omega
        · exfalso; omega
  · rcases tag_trichotomy t.unpair.2.unpair.1.unpair.1 with hnb | hnb | ⟨hnb0, hnb1⟩
    · rw [sumEnum_one hna, sumEnum_zero hnb, Set.inter_comm, inj₀_inter_inj₁]
      constructor
      · intro h
        obtain ⟨x, hx⟩ := sumEnum_nonempty (h₀ := h₀) (h₁ := h₁) t.unpair.2.unpair.2
        rw [← h] at hx
        exact absurd hx (Set.notMem_empty x)
      · rintro (⟨⟨_, e2⟩, _⟩ | ⟨⟨e1, _⟩, _⟩ | ⟨⟨⟨e1, _⟩, _⟩, _⟩ |
        ⟨⟨⟨_, e2⟩, _⟩, _⟩) <;> exfalso <;> omega
    · rw [sumEnum_one hna, sumEnum_one hnb, inj₁_inter]
      rcases tag_trichotomy t.unpair.2.unpair.2.unpair.1 with hnc | hnc | ⟨hnc0, hnc1⟩
      · rw [sumEnum_zero hnc]
        constructor
        · intro h; exact (inj₀_eq_inj₁_elim (h₀ _ (P₀.mem_X _)) h.symm).elim
        · rintro (⟨⟨_, e2⟩, _⟩ | ⟨⟨_, e2⟩, _⟩ | ⟨⟨⟨e1, _⟩, _⟩, _⟩ |
          ⟨⟨⟨_, _⟩, e3⟩, _⟩) <;> exfalso <;> omega
      · rw [sumEnum_one hnc, inj₁_eq_iff]
        constructor
        · intro h; exact Or.inr (Or.inr (Or.inr ⟨⟨⟨hna, hnb⟩, hnc⟩, h⟩))
        · rintro (⟨⟨_, e2⟩, _⟩ | ⟨⟨_, e2⟩, _⟩ | ⟨⟨⟨e1, _⟩, _⟩, _⟩ | ⟨⟨⟨_, _⟩, _⟩, h⟩)
          · exfalso; omega
          · exfalso; omega
          · exfalso; omega
          · exact h
      · rw [sumEnum_master hnc0 hnc1]
        constructor
        · intro h; exact absurd h inj₁_ne_sumMaster
        · rintro (⟨⟨_, e2⟩, _⟩ | ⟨⟨_, e2⟩, _⟩ | ⟨⟨⟨e1, _⟩, _⟩, _⟩ |
          ⟨⟨⟨_, _⟩, e3⟩, _⟩) <;> exfalso <;> omega
    · rw [sumEnum_master hnb0 hnb1, sumEnum_inter_sumMaster]
      constructor
      · intro h; exact Or.inr (Or.inl ⟨⟨hnb0, hnb1⟩, h⟩)
      · rintro (⟨⟨_, e2⟩, _⟩ | ⟨_, h⟩ | ⟨⟨⟨_, e2⟩, _⟩, _⟩ | ⟨⟨⟨_, e2⟩, _⟩, _⟩)
        · exfalso; omega
        · exact h
        · exfalso; omega
        · exfalso; omega
  · rw [sumEnum_master hna0 hna1, sumMaster_inter_sumEnum]
    constructor
    · intro h; exact Or.inl ⟨⟨hna0, hna1⟩, h⟩
    · rintro (⟨_, h⟩ | ⟨⟨e1, e2⟩, h⟩ | ⟨⟨⟨e1, _⟩, _⟩, _⟩ | ⟨⟨⟨e1, _⟩, _⟩, _⟩)
      · exact h
      · rw [sumEnum_master e1 e2]; exact h
      · exfalso; omega
      · exfalso; omega

/-- Decidability of the sum-presentation consistency relation. -/
theorem sumPresentation_cons_computable :
    RecDecidable₂ (fun n m => ∃ k, sumEnum P₀ P₁ k ⊆ sumEnum P₀ P₁ n ∩ sumEnum P₀ P₁ m) := by
  have hA0 : RecDecidable (fun s => s.unpair.1.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 0)
  have hA1 : RecDecidable (fun s => s.unpair.1.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 1)
  have hB0 : RecDecidable (fun s => s.unpair.2.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 0)
  have hB1 : RecDecidable (fun s => s.unpair.2.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 1)
  have hgc : Nat.Primrec (fun s => Nat.pair s.unpair.1.unpair.2 s.unpair.2.unpair.2) :=
    (Nat.Primrec.right.comp Nat.Primrec.left).pair (Nat.Primrec.right.comp Nat.Primrec.right)
  have hC0 : RecDecidable (fun s =>
    ∃ k, P₀.X k ⊆ P₀.X s.unpair.1.unpair.2 ∩ P₀.X s.unpair.2.unpair.2)
      := by
    refine RecDecidable.of_iff (fun s => ?_) (P₀.cons_computable.comp hgc)
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hC1 : RecDecidable (fun s =>
    ∃ k, P₁.X k ⊆ P₁.X s.unpair.1.unpair.2 ∩ P₁.X s.unpair.2.unpair.2)
      := by
    refine RecDecidable.of_iff (fun s => ?_) (P₁.cons_computable.comp hgc)
    simp only [unpair_pair_fst, unpair_pair_snd]
  refine RecDecidable.of_iff (fun s => ?_)
    ((hA0.not.and hA1.not).or
      ((hB0.not.and hB1.not).or
        (((hA0.and hB0).and hC0).or ((hA1.and hB1).and hC1))))
  dsimp only
  rcases tag_trichotomy s.unpair.1.unpair.1 with hna | hna | ⟨hna0, hna1⟩
  · rcases tag_trichotomy s.unpair.2.unpair.1 with hnb | hnb | ⟨hnb0, hnb1⟩
    · rw [sumEnum_zero hna, sumEnum_zero hnb, inj₀_inter]
      constructor
      · rintro ⟨k, hk⟩
        obtain ⟨X₂, hX₂mem, hX₂eq⟩ := mem_subset_inj₀ (sumEnum_mem (h₀ := h₀) (h₁ := h₁) k) hk
        obtain ⟨j, hj⟩ := P₀.surj hX₂mem
        refine Or.inr (Or.inr (Or.inl ⟨⟨hna, hnb⟩, j, ?_⟩))
        rw [hj]
        rw [hX₂eq] at hk
        exact inj₀_subset_inj₀.mp hk
      · rintro (⟨e1, _⟩ | ⟨e1, _⟩ | ⟨⟨_, _⟩, j, hj⟩ | ⟨⟨e1, _⟩, _⟩)
        · exfalso; omega
        · exfalso; omega
        · refine ⟨Nat.pair 0 j, ?_⟩
          rw [sumEnum_zero (by rw [unpair_pair_fst]), unpair_pair_snd]
          exact inj₀_subset_inj₀.mpr hj
        · exfalso; omega
    · rw [sumEnum_zero hna, sumEnum_one hnb, inj₀_inter_inj₁]
      constructor
      · rintro ⟨k, hk⟩
        obtain ⟨x, hx⟩ := sumEnum_nonempty (h₀ := h₀) (h₁ := h₁) k
        exact absurd (hk hx) (Set.notMem_empty x)
      · rintro (⟨e1, _⟩ | ⟨_, e2⟩ | ⟨⟨_, e2⟩, _⟩ | ⟨⟨e1, _⟩, _⟩) <;> exfalso <;> omega
    · rw [sumEnum_master hnb0 hnb1, sumEnum_inter_sumMaster]
      exact ⟨fun _ => Or.inr (Or.inl ⟨hnb0, hnb1⟩), fun _ => ⟨s.unpair.1, subset_rfl⟩⟩
  · rcases tag_trichotomy s.unpair.2.unpair.1 with hnb | hnb | ⟨hnb0, hnb1⟩
    · rw [sumEnum_one hna, sumEnum_zero hnb, Set.inter_comm, inj₀_inter_inj₁]
      constructor
      · rintro ⟨k, hk⟩
        obtain ⟨x, hx⟩ := sumEnum_nonempty (h₀ := h₀) (h₁ := h₁) k
        exact absurd (hk hx) (Set.notMem_empty x)
      · rintro (⟨_, e2⟩ | ⟨e1, _⟩ | ⟨⟨e1, _⟩, _⟩ | ⟨⟨_, e2⟩, _⟩) <;> exfalso <;> omega
    · rw [sumEnum_one hna, sumEnum_one hnb, inj₁_inter]
      constructor
      · rintro ⟨k, hk⟩
        obtain ⟨Y₂, hY₂mem, hY₂eq⟩ := mem_subset_inj₁ (sumEnum_mem (h₀ := h₀) (h₁ := h₁) k) hk
        obtain ⟨j, hj⟩ := P₁.surj hY₂mem
        refine Or.inr (Or.inr (Or.inr ⟨⟨hna, hnb⟩, j, ?_⟩))
        rw [hj]
        rw [hY₂eq] at hk
        exact inj₁_subset_inj₁.mp hk
      · rintro (⟨_, e2⟩ | ⟨_, e2⟩ | ⟨⟨e1, _⟩, _⟩ | ⟨⟨_, _⟩, j, hj⟩)
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · refine ⟨Nat.pair 1 j, ?_⟩
          rw [sumEnum_one (by rw [unpair_pair_fst]), unpair_pair_snd]
          exact inj₁_subset_inj₁.mpr hj
    · rw [sumEnum_master hnb0 hnb1, sumEnum_inter_sumMaster]
      exact ⟨fun _ => Or.inr (Or.inl ⟨hnb0, hnb1⟩), fun _ => ⟨s.unpair.1, subset_rfl⟩⟩
  · rw [sumEnum_master hna0 hna1, sumMaster_inter_sumEnum]
    exact ⟨fun _ => Or.inl ⟨hna0, hna1⟩, fun _ => ⟨s.unpair.2, subset_rfl⟩⟩

/-- Primitive-recursive index chosen for sum intersections. -/
def sumInter (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁) (n m : ℕ) : ℕ :=
  selectFn (1 - (2 - n.unpair.1)) m
    (selectFn (1 - (2 - m.unpair.1)) n
      (selectFn (1 - n.unpair.1)
        (Nat.pair 0 (P₀.inter n.unpair.2 m.unpair.2))
        (Nat.pair 1 (P₁.inter n.unpair.2 m.unpair.2))))

omit h₀ h₁ in
/-- The sum-presentation intersection index is primitive recursive. -/
theorem sumInter_primrec :
    Nat.Primrec (fun t => sumInter P₀ P₁ t.unpair.1 t.unpair.2) := by
  have hnTag : Nat.Primrec (fun t => t.unpair.1.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.left
  have hmTag : Nat.Primrec (fun t => t.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hnIdx : Nat.Primrec (fun t => t.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.left
  have hmIdx : Nat.Primrec (fun t => t.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hP0 : Nat.Primrec (fun t => Nat.pair 0 (P₀.inter t.unpair.1.unpair.2 t.unpair.2.unpair.2)) :=
    (Nat.Primrec.const 0).pair ((P₀.inter_primrec.comp (hnIdx.pair hmIdx)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd])
  have hP1 : Nat.Primrec (fun t => Nat.pair 1 (P₁.inter t.unpair.1.unpair.2 t.unpair.2.unpair.2)) :=
    (Nat.Primrec.const 1).pair ((P₁.inter_primrec.comp (hnIdx.pair hmIdx)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd])
  have hcnMaster : Nat.Primrec (fun t => 1 - (2 - t.unpair.1.unpair.1)) :=
    primrec_sub₂ (Nat.Primrec.const 1) (primrec_sub₂ (Nat.Primrec.const 2) hnTag)
  have hcmMaster : Nat.Primrec (fun t => 1 - (2 - t.unpair.2.unpair.1)) :=
    primrec_sub₂ (Nat.Primrec.const 1) (primrec_sub₂ (Nat.Primrec.const 2) hmTag)
  have hcnZero : Nat.Primrec (fun t => 1 - t.unpair.1.unpair.1) :=
    primrec_sub₂ (Nat.Primrec.const 1) hnTag
  exact primrec_selectFn hcnMaster Nat.Primrec.right
    (primrec_selectFn hcmMaster Nat.Primrec.left
      (primrec_selectFn hcnZero hP0 hP1))

/-- The sum-presentation intersection index specifies the actual intersection when
consistent. -/
theorem sumInter_spec {n m : ℕ} (h : ∃ k, sumEnum P₀ P₁ k ⊆ sumEnum P₀ P₁ n ∩ sumEnum P₀ P₁ m) :
    sumEnum P₀ P₁ (sumInter P₀ P₁ n m) = sumEnum P₀ P₁ n ∩ sumEnum P₀ P₁ m := by
  rcases h with ⟨k, hk⟩
  unfold sumInter
  rcases tag_trichotomy n.unpair.1 with hna | hna | ⟨hna0, hna1⟩
  · rw [show 1 - (2 - n.unpair.1) = 0 by omega, selectFn_zero]
    rcases tag_trichotomy m.unpair.1 with hmb | hmb | ⟨hmb0, hmb1⟩
    · rw [show 1 - (2 - m.unpair.1) = 0 by omega, selectFn_zero,
        show 1 - n.unpair.1 = 1 by omega, selectFn_one,
        sumEnum_zero (by rw [unpair_pair_fst]), unpair_pair_snd,
        sumEnum_zero hna, sumEnum_zero hmb, inj₀_inter]
      rw [sumEnum_zero hna, sumEnum_zero hmb, inj₀_inter] at hk
      obtain ⟨X₂, hX₂mem, hX₂eq⟩ := mem_subset_inj₀ (sumEnum_mem (h₀ := h₀) (h₁ := h₁) k) hk
      obtain ⟨j, hj⟩ := P₀.surj hX₂mem
      rw [hX₂eq] at hk
      have hjsub : P₀.X j ⊆ P₀.X n.unpair.2 ∩ P₀.X m.unpair.2 := by
        rw [hj]; exact inj₀_subset_inj₀.mp hk
      rw [P₀.inter_spec ⟨j, hjsub⟩]
    · exfalso
      rw [sumEnum_zero hna, sumEnum_one hmb, inj₀_inter_inj₁] at hk
      obtain ⟨x, hx⟩ := sumEnum_nonempty (h₀ := h₀) (h₁ := h₁) k
      exact absurd (hk hx) (Set.notMem_empty x)
    · rw [show 1 - (2 - m.unpair.1) = 1 by omega, selectFn_one,
        sumEnum_master hmb0 hmb1, sumEnum_inter_sumMaster]
  · rw [show 1 - (2 - n.unpair.1) = 0 by omega, selectFn_zero]
    rcases tag_trichotomy m.unpair.1 with hmb | hmb | ⟨hmb0, hmb1⟩
    · exfalso
      rw [sumEnum_one hna, sumEnum_zero hmb, Set.inter_comm, inj₀_inter_inj₁] at hk
      obtain ⟨x, hx⟩ := sumEnum_nonempty (h₀ := h₀) (h₁ := h₁) k
      exact absurd (hk hx) (Set.notMem_empty x)
    · rw [show 1 - (2 - m.unpair.1) = 0 by omega, selectFn_zero,
        show 1 - n.unpair.1 = 0 by omega, selectFn_zero,
        sumEnum_one (by rw [unpair_pair_fst]), unpair_pair_snd,
        sumEnum_one hna, sumEnum_one hmb, inj₁_inter]
      rw [sumEnum_one hna, sumEnum_one hmb, inj₁_inter] at hk
      obtain ⟨Y₂, hY₂mem, hY₂eq⟩ := mem_subset_inj₁ (sumEnum_mem (h₀ := h₀) (h₁ := h₁) k) hk
      obtain ⟨j, hj⟩ := P₁.surj hY₂mem
      rw [hY₂eq] at hk
      have hjsub : P₁.X j ⊆ P₁.X n.unpair.2 ∩ P₁.X m.unpair.2 := by
        rw [hj]; exact inj₁_subset_inj₁.mp hk
      rw [P₁.inter_spec ⟨j, hjsub⟩]
    · rw [show 1 - (2 - m.unpair.1) = 1 by omega, selectFn_one,
        sumEnum_master hmb0 hmb1, sumEnum_inter_sumMaster]
  · rw [show 1 - (2 - n.unpair.1) = 1 by omega, selectFn_one,
      sumEnum_master hna0 hna1, sumMaster_inter_sumEnum]

/-- The master index of the sum presentation denotes the sum master. -/
theorem sumPresentation_masterIdx_spec :
    sumEnum P₀ P₁ (Nat.pair 2 0) = (sum V₀ V₁ h₀ h₁).master := by
  rw [sumEnum_master (by rw [unpair_pair_fst]; decide) (by rw [unpair_pair_fst]; decide)]
  rfl

/-- **Theorem 7.4 (Scott 1981, PRG-19) — `𝒟₀ + 𝒟₁` is effectively given.** The tag
enumeration
`Z (pair 0 n) = 0X⁰ₙ`, `Z (pair 1 n) = 1X¹ₙ`, `Z (pair (≥2) _) = M`. Scott's
7.1(i)/(ii) follow the
intersection table: master absorbs, `0X ∩ 0X' = 0(X∩X')` reduces to `𝒟₀`, `0X ∩ 1Y
= ∅` is
impossible (non-emptiness). The deciders are assembled from `eqSEdec`, the tag
deciders
(`natEq`/`not`/`and`/`or`), and the components' `interEq`/`cons`. -/
def sumPresentation (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁) :
    ComputablePresentation (sum V₀ V₁ h₀ h₁) where
  X := sumEnum P₀ P₁
  mem_X t := sumEnum_mem t
  surj := by
    rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩)
    · exact ⟨Nat.pair 2 0, sumEnum_master (by rw [unpair_pair_fst]; decide)
        (by rw [unpair_pair_fst]; decide)⟩
    · obtain ⟨n, rfl⟩ := P₀.surj hX
      exact ⟨Nat.pair 0 n, by rw [sumEnum_zero (by rw [unpair_pair_fst]), unpair_pair_snd]⟩
    · obtain ⟨n, rfl⟩ := P₁.surj hY
      exact ⟨Nat.pair 1 n, by rw [sumEnum_one (by rw [unpair_pair_fst]), unpair_pair_snd]⟩
  interEq_computable := sumPresentation_interEq_computable (h₀ := h₀) (h₁ := h₁)
    (P₀ := P₀) (P₁ := P₁)
  cons_computable := sumPresentation_cons_computable (h₀ := h₀) (h₁ := h₁)
    (P₀ := P₀) (P₁ := P₁)
  inter n m := sumInter P₀ P₁ n m
  inter_primrec := sumInter_primrec (P₀ := P₀) (P₁ := P₁)
  inter_spec := by
    intro n m h
    exact sumInter_spec (h₀ := h₀) (h₁ := h₁) (P₀ := P₀) (P₁ := P₁) h
  masterIdx := Nat.pair 2 0
  masterIdx_spec := sumPresentation_masterIdx_spec (P₀ := P₀) (P₁ := P₁)

/-- **Theorem 7.4 (Scott 1981, PRG-19).** The sum of effectively given domains is
effectively
given. -/
theorem sum_isEffectivelyGiven (g₀ : V₀.IsEffectivelyGiven) (g₁ : V₁.IsEffectivelyGiven) :
    (sum V₀ V₁ h₀ h₁).IsEffectivelyGiven := by
  obtain ⟨P₀⟩ := g₀; obtain ⟨P₁⟩ := g₁
  exact ⟨sumPresentation P₀ P₁⟩

@[simp] theorem sumPresentation_X (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)
    (t : ℕ) : (sumPresentation P₀ P₁ (h₀ := h₀) (h₁ := h₁)).X t = sumEnum P₀ P₁ t := by
  unfold sumPresentation
  rfl

/-- **Theorem 7.4 (Scott 1981, PRG-19) — `in₀` is computable.** `X⁰ₙ (in₀) Z_m ↔
0X⁰ₙ ⊆ Z_m`, which
tag-decodes to `(m = 0X⁰ ∧ X⁰ₙ ⊆ X⁰_{m.2}) ∨ (m = master)` (`m = 1X¹` is
impossible as `X⁰ₙ ≠ ∅`). -/
theorem inMap₀_isComputable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁) :
    IsComputableMap P₀ (sumPresentation P₀ P₁) (inMap₀ (h₀ := h₀) (h₁ := h₁)) := by
  have hincl : RecDecidable (fun s => P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2) := P₀.incl_computable
  have hmtag0 : RecDecidable (fun s => s.unpair.2.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 0)
  have hmtag1 : RecDecidable (fun s => s.unpair.2.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 1)
  have hincl0 : RecDecidable (fun s => P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2.unpair.2) :=
    RecDecidable.of_iff (fun s => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hincl.comp (Nat.Primrec.left.pair (Nat.Primrec.right.comp Nat.Primrec.right)))
  refine (RecDecidable.of_iff (fun s => ?_)
    ((hmtag0.and hincl0).or (hmtag0.not.and hmtag1.not))).re
  simp only [sumPresentation_X]
  rcases tag_trichotomy s.unpair.2.unpair.1 with hm | hm | ⟨hm0, hm1⟩
  · constructor
    · rintro ⟨_, _, hsub⟩
      rw [sumEnum_zero hm] at hsub
      exact Or.inl ⟨hm, inj₀_subset_inj₀.mp hsub⟩
    · rintro (⟨_, hsub⟩ | ⟨e1, _⟩)
      · refine ⟨P₀.mem_X _, sumEnum_mem _, ?_⟩
        rw [sumEnum_zero hm]; exact inj₀_subset_inj₀.mpr hsub
      · exfalso; omega
  · constructor
    · rintro ⟨_, _, hsub⟩
      rw [sumEnum_one hm] at hsub
      exact (not_inj₀_subset_inj₁ (h₀ _ (P₀.mem_X _)) hsub).elim
    · rintro (⟨e1, _⟩ | ⟨_, e2⟩) <;> exfalso <;> omega
  · constructor
    · intro _; exact Or.inr ⟨hm0, hm1⟩
    · intro _
      refine ⟨P₀.mem_X _, sumEnum_mem _, ?_⟩
      rw [sumEnum_master hm0 hm1]; exact inj₀_subset_sumMaster (P₀.mem_X _)

/-- **Theorem 7.4 (Scott 1981, PRG-19) — `in₁` is computable.** Symmetric to
`in₀`. -/
theorem inMap₁_isComputable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁) :
    IsComputableMap P₁ (sumPresentation P₀ P₁) (inMap₁ (h₀ := h₀) (h₁ := h₁)) := by
  have hincl : RecDecidable (fun s => P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2) := P₁.incl_computable
  have hmtag0 : RecDecidable (fun s => s.unpair.2.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 0)
  have hmtag1 : RecDecidable (fun s => s.unpair.2.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 1)
  have hincl1 : RecDecidable (fun s => P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2.unpair.2) :=
    RecDecidable.of_iff (fun s => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hincl.comp (Nat.Primrec.left.pair (Nat.Primrec.right.comp Nat.Primrec.right)))
  refine (RecDecidable.of_iff (fun s => ?_)
    ((hmtag1.and hincl1).or (hmtag0.not.and hmtag1.not))).re
  simp only [sumPresentation_X]
  rcases tag_trichotomy s.unpair.2.unpair.1 with hm | hm | ⟨hm0, hm1⟩
  · constructor
    · rintro ⟨_, _, hsub⟩
      rw [sumEnum_zero hm] at hsub
      exact (not_inj₁_subset_inj₀ (h₁ _ (P₁.mem_X _)) hsub).elim
    · rintro (⟨e1, _⟩ | ⟨_, e2⟩) <;> exfalso <;> omega
  · constructor
    · rintro ⟨_, _, hsub⟩
      rw [sumEnum_one hm] at hsub
      exact Or.inl ⟨hm, inj₁_subset_inj₁.mp hsub⟩
    · rintro (⟨_, hsub⟩ | ⟨e1, _⟩)
      · refine ⟨P₁.mem_X _, sumEnum_mem _, ?_⟩
        rw [sumEnum_one hm]; exact inj₁_subset_inj₁.mpr hsub
      · exfalso; omega
  · constructor
    · intro _; exact Or.inr ⟨hm0, hm1⟩
    · intro _
      refine ⟨P₁.mem_X _, sumEnum_mem _, ?_⟩
      rw [sumEnum_master hm0 hm1]; exact inj₁_subset_sumMaster (P₁.mem_X _)

/-- **Theorem 7.4 (Scott 1981, PRG-19) — `out₀` is computable.** `Z_n (out₀) X⁰_m
↔ leftPart Z_n ⊆
X⁰_m`; tag-decoded, `leftPart` is `X⁰_{n.2}` on a left copy and `Δ₀` on a right
copy/master, so the
relation is `incl` against either `n.2` or the master index `k₀` (`X⁰_{k₀} = Δ₀`). -/
theorem outMap₀_isComputable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁) :
    IsComputableMap (sumPresentation P₀ P₁) P₀ (outMap₀ (h₀ := h₀) (h₁ := h₁)) := by
  obtain ⟨k0, hk0⟩ := P₀.surj V₀.master_mem
  have hincl : RecDecidable (fun s => P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2) := P₀.incl_computable
  have hntag0 : RecDecidable (fun s => s.unpair.1.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 0)
  have hincl_left : RecDecidable (fun s => P₀.X s.unpair.1.unpair.2 ⊆ P₀.X s.unpair.2) :=
    RecDecidable.of_iff (fun s => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hincl.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right))
  have hincl_master : RecDecidable (fun s => P₀.X k0 ⊆ P₀.X s.unpair.2) :=
    RecDecidable.of_iff (fun s => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hincl.comp ((Nat.Primrec.const k0).pair Nat.Primrec.right))
  refine (RecDecidable.of_iff (fun s => ?_)
    ((hntag0.and hincl_left).or (hntag0.not.and hincl_master))).re
  simp only [sumPresentation_X]
  rcases tag_trichotomy s.unpair.1.unpair.1 with hn | hn | ⟨hn0, hn1⟩
  · constructor
    · rintro ⟨_, _, hsub⟩
      rw [sumEnum_zero hn, leftPart_inj₀] at hsub
      exact Or.inl ⟨hn, hsub⟩
    · rintro (⟨_, hsub⟩ | ⟨e1, _⟩)
      · refine ⟨sumEnum_mem _, P₀.mem_X _, ?_⟩
        rw [sumEnum_zero hn, leftPart_inj₀]; exact hsub
      · exfalso; omega
  · constructor
    · rintro ⟨_, _, hsub⟩
      rw [sumEnum_one hn, leftPart_inj₁ V₀ (h₁ _ (P₁.mem_X _))] at hsub
      refine Or.inr ⟨by omega, ?_⟩
      rw [hk0]; exact hsub
    · rintro (⟨e1, _⟩ | ⟨_, hsub⟩)
      · exfalso; omega
      · refine ⟨sumEnum_mem _, P₀.mem_X _, ?_⟩
        rw [sumEnum_one hn, leftPart_inj₁ V₀ (h₁ _ (P₁.mem_X _)), ← hk0]; exact hsub
  · constructor
    · rintro ⟨_, _, hsub⟩
      rw [sumEnum_master hn0 hn1, leftPart_sumMaster] at hsub
      refine Or.inr ⟨hn0, ?_⟩
      rw [hk0]; exact hsub
    · rintro (⟨e1, _⟩ | ⟨_, hsub⟩)
      · exfalso; omega
      · refine ⟨sumEnum_mem _, P₀.mem_X _, ?_⟩
        rw [sumEnum_master hn0 hn1, leftPart_sumMaster, ← hk0]; exact hsub

/-- **Theorem 7.4 (Scott 1981, PRG-19) — `out₁` is computable.** Symmetric to
`out₀` via
`rightPart`. -/
theorem outMap₁_isComputable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁) :
    IsComputableMap (sumPresentation P₀ P₁) P₁ (outMap₁ (h₀ := h₀) (h₁ := h₁)) := by
  obtain ⟨k1, hk1⟩ := P₁.surj V₁.master_mem
  have hincl : RecDecidable (fun s => P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2) := P₁.incl_computable
  have hntag1 : RecDecidable (fun s => s.unpair.1.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 1)
  have hincl_right : RecDecidable (fun s => P₁.X s.unpair.1.unpair.2 ⊆ P₁.X s.unpair.2) :=
    RecDecidable.of_iff (fun s => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hincl.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right))
  have hincl_master : RecDecidable (fun s => P₁.X k1 ⊆ P₁.X s.unpair.2) :=
    RecDecidable.of_iff (fun s => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hincl.comp ((Nat.Primrec.const k1).pair Nat.Primrec.right))
  refine (RecDecidable.of_iff (fun s => ?_)
    ((hntag1.and hincl_right).or (hntag1.not.and hincl_master))).re
  simp only [sumPresentation_X]
  rcases tag_trichotomy s.unpair.1.unpair.1 with hn | hn | ⟨hn0, hn1⟩
  · constructor
    · rintro ⟨_, _, hsub⟩
      rw [sumEnum_zero hn, rightPart_inj₀ V₁ (h₀ _ (P₀.mem_X _))] at hsub
      refine Or.inr ⟨by omega, ?_⟩
      rw [hk1]; exact hsub
    · rintro (⟨e1, _⟩ | ⟨_, hsub⟩)
      · exfalso; omega
      · refine ⟨sumEnum_mem _, P₁.mem_X _, ?_⟩
        rw [sumEnum_zero hn, rightPart_inj₀ V₁ (h₀ _ (P₀.mem_X _)), ← hk1]; exact hsub
  · constructor
    · rintro ⟨_, _, hsub⟩
      rw [sumEnum_one hn, rightPart_inj₁] at hsub
      exact Or.inl ⟨hn, hsub⟩
    · rintro (⟨_, hsub⟩ | ⟨e1, _⟩)
      · refine ⟨sumEnum_mem _, P₁.mem_X _, ?_⟩
        rw [sumEnum_one hn, rightPart_inj₁]; exact hsub
      · exfalso; omega
  · constructor
    · rintro ⟨_, _, hsub⟩
      rw [sumEnum_master hn0 hn1, rightPart_sumMaster] at hsub
      refine Or.inr ⟨hn1, ?_⟩
      rw [hk1]; exact hsub
    · rintro (⟨e1, _⟩ | ⟨_, hsub⟩)
      · exfalso; omega
      · refine ⟨sumEnum_mem _, P₁.mem_X _, ?_⟩
        rw [sumEnum_master hn0 hn1, rightPart_sumMaster, ← hk1]; exact hsub

/-- **Theorem 7.4 (Scott 1981, PRG-19) — `f + g` is computable.** Tag-decoding the
sum relation,
`Zₙ (f+g) W_m` holds iff `W_m` is the codomain master (decidable in `m`'s tag), or
both are left
copies (tag `0`) with `X⁰_{n.2} f Y⁰_{m.2}`, or both are right copies (tag `1`)
with
`X¹_{n.2} g Y¹_{m.2}`. The three disjuncts are r.e. (`REPred.or`): each copy case
conjoins a decidable
tag test with the reindexed r.e. relation of `f`/`g`. -/
theorem sumMap_isComputable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
    {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}
    (Q₀ : ComputablePresentation V₀') (Q₁ : ComputablePresentation V₁')
    {f : ApproximableMap V₀ V₀'} {g : ApproximableMap V₁ V₁'}
    (hf : IsComputableMap P₀ Q₀ f) (hg : IsComputableMap P₁ Q₁ g) :
    IsComputableMap (sumPresentation P₀ P₁ (h₀ := h₀) (h₁ := h₁))
      (sumPresentation Q₀ Q₁ (h₀ := h₀') (h₁ := h₁'))
      (sumMap (h₀ := h₀) (h₁ := h₁) (h₀' := h₀') (h₁' := h₁') f g) := by
  have hf' : REPred (fun u => f.rel (P₀.X u.unpair.1) (Q₀.X u.unpair.2)) := hf
  have hg' : REPred (fun u => g.rel (P₁.X u.unpair.1) (Q₁.X u.unpair.2)) := hg
  have hNtag0 : RecDecidable (fun s => s.unpair.1.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 0)
  have hNtag1 : RecDecidable (fun s => s.unpair.1.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 1)
  have hMtag0 : RecDecidable (fun s => s.unpair.2.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 0)
  have hMtag1 : RecDecidable (fun s => s.unpair.2.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 1)
  have hfr : REPred (fun s => f.rel (P₀.X s.unpair.1.unpair.2) (Q₀.X s.unpair.2.unpair.2)) :=
    REPred.of_iff (fun s => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hf'.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair
        (Nat.Primrec.right.comp Nat.Primrec.right)))
  have hgr : REPred (fun s => g.rel (P₁.X s.unpair.1.unpair.2) (Q₁.X s.unpair.2.unpair.2)) :=
    REPred.of_iff (fun s => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hg'.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair
        (Nat.Primrec.right.comp Nat.Primrec.right)))
  have hA : REPred (fun s => s.unpair.2.unpair.1 ≠ 0 ∧ s.unpair.2.unpair.1 ≠ 1) :=
    (hMtag0.not.and hMtag1.not).re
  have hB : REPred (fun s => (s.unpair.1.unpair.1 = 0 ∧ s.unpair.2.unpair.1 = 0)
      ∧ f.rel (P₀.X s.unpair.1.unpair.2) (Q₀.X s.unpair.2.unpair.2)) :=
    ((hNtag0.and hMtag0).re).and hfr
  have hC : REPred (fun s => (s.unpair.1.unpair.1 = 1 ∧ s.unpair.2.unpair.1 = 1)
      ∧ g.rel (P₁.X s.unpair.1.unpair.2) (Q₁.X s.unpair.2.unpair.2)) :=
    ((hNtag1.and hMtag1).re).and hgr
  refine REPred.of_iff (fun s => ?_) (hA.or (hB.or hC))
  simp only [sumPresentation_X]
  constructor
  · rintro ⟨_, _, hdisj⟩
    rcases hdisj with hM | ⟨X, Y', hWX, hWY, hfXY⟩ | ⟨Y, Y', hWY, hWY', hgYY⟩
    · left
      rcases tag_trichotomy s.unpair.2.unpair.1 with hm | hm | hm
      · rw [sumEnum_zero hm] at hM; exact absurd hM inj₀_ne_sumMaster
      · rw [sumEnum_one hm] at hM; exact absurd hM inj₁_ne_sumMaster
      · exact hm
    · right; left
      have ha : s.unpair.1.unpair.1 = 0 ∧ X = P₀.X s.unpair.1.unpair.2 := by
        rcases tag_trichotomy s.unpair.1.unpair.1 with hn | hn | ⟨h0, h1⟩
        · rw [sumEnum_zero hn] at hWX; exact ⟨hn, (inj₀_eq_iff.mp hWX).symm⟩
        · rw [sumEnum_one hn] at hWX
          exact absurd hWX.symm (inj₀_ne_inj₁_of_nonempty (h₁ _ (P₁.mem_X _)))
        · rw [sumEnum_master h0 h1] at hWX; exact absurd hWX.symm inj₀_ne_sumMaster
      have hb : s.unpair.2.unpair.1 = 0 ∧ Y' = Q₀.X s.unpair.2.unpair.2 := by
        rcases tag_trichotomy s.unpair.2.unpair.1 with hm | hm | ⟨h0, h1⟩
        · rw [sumEnum_zero hm] at hWY; exact ⟨hm, (inj₀_eq_iff.mp hWY).symm⟩
        · rw [sumEnum_one hm] at hWY
          exact absurd hWY.symm (inj₀_ne_inj₁_of_nonempty (h₁' _ (Q₁.mem_X _)))
        · rw [sumEnum_master h0 h1] at hWY; exact absurd hWY.symm inj₀_ne_sumMaster
      obtain ⟨ha0, hX⟩ := ha; obtain ⟨hb0, hY⟩ := hb
      subst hX; subst hY
      exact ⟨⟨ha0, hb0⟩, hfXY⟩
    · right; right
      have ha : s.unpair.1.unpair.1 = 1 ∧ Y = P₁.X s.unpair.1.unpair.2 := by
        rcases tag_trichotomy s.unpair.1.unpair.1 with hn | hn | ⟨h0, h1⟩
        · rw [sumEnum_zero hn] at hWY
          exact (inj₀_eq_inj₁_elim (h₀ _ (P₀.mem_X _)) hWY).elim
        · rw [sumEnum_one hn] at hWY; exact ⟨hn, (inj₁_eq_iff.mp hWY).symm⟩
        · rw [sumEnum_master h0 h1] at hWY; exact absurd hWY.symm inj₁_ne_sumMaster
      have hb : s.unpair.2.unpair.1 = 1 ∧ Y' = Q₁.X s.unpair.2.unpair.2 := by
        rcases tag_trichotomy s.unpair.2.unpair.1 with hm | hm | ⟨h0, h1⟩
        · rw [sumEnum_zero hm] at hWY'
          exact (inj₀_eq_inj₁_elim (h₀' _ (Q₀.mem_X _)) hWY').elim
        · rw [sumEnum_one hm] at hWY'; exact ⟨hm, (inj₁_eq_iff.mp hWY').symm⟩
        · rw [sumEnum_master h0 h1] at hWY'; exact absurd hWY'.symm inj₁_ne_sumMaster
      obtain ⟨ha1, hYeq⟩ := ha; obtain ⟨hb1, hY'eq⟩ := hb
      subst hYeq; subst hY'eq
      exact ⟨⟨ha1, hb1⟩, hgYY⟩
  · rintro (⟨hm0, hm1⟩ | ⟨⟨hn0, hm0⟩, hfXY⟩ | ⟨⟨hn1, hm1⟩, hgYY⟩)
    · exact ⟨sumEnum_mem _, sumEnum_mem _, Or.inl (sumEnum_master hm0 hm1)⟩
    · exact ⟨sumEnum_mem _, sumEnum_mem _,
        Or.inr (Or.inl ⟨_, _, sumEnum_zero hn0, sumEnum_zero hm0, hfXY⟩)⟩
    · exact ⟨sumEnum_mem _, sumEnum_mem _,
        Or.inr (Or.inr ⟨_, _, sumEnum_one hn1, sumEnum_one hm1, hgYY⟩)⟩

end Sum

end Domain.Neighborhood
