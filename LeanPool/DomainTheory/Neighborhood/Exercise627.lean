/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Exercise621
import LeanPool.DomainTheory.Neighborhood.Lemma615

/-!
# Exercise 6.27 (Scott 1981, PRG-19, §6) — which subsystem relations hold

> **EXERCISE 6.27.** Which of the following relationships are true:
> `(𝒟 ⊗ ℰ) ⊴ (𝒟 × ℰ)`;  `𝒟 ⊴ 𝒟 × ℰ`;
> `(𝒟 ⊕ ℰ) ⊴ (𝒟 + ℰ)`;  `𝒟 ⊴ 𝒟 ⊕ ℰ`;
> `(𝒟 →⊥ ℰ) ⊴ (𝒟 → ℰ)`;  `𝒟 ⊴ 𝒟 ⊗ ℰ` ?

Here `⊴` is Scott's *embeds-as-a-subdomain* relation of Lemma 6.15
(`Trianglelefteq`): `D ⊴ E`
means `D ≅ᴰ D'` for some `D' ◁ E`. We use the concrete `{0,1}*` constructions of
Exercises 6.19/6.21
(`sumTok`, `prodTok`, `oplusTok`, `otimesTok`) and the function spaces `funSpace`
/ `strictFun`.

**Answer.** The first five hold for all `𝒟, ℰ`; the last fails in general.

| relation | verdict | name |
| --- | --- | --- |
| `(𝒟 ⊗ ℰ) ⊴ (𝒟 × ℰ)` | **true** | `otimes_trianglelefteq_prod` (in fact
`otimesTok ◁ prodTok`) |
| `𝒟 ⊴ 𝒟 × ℰ` | **true** | `fst_trianglelefteq_prod` |
| `(𝒟 ⊕ ℰ) ⊴ (𝒟 + ℰ)` | **true** | `oplus_trianglelefteq_sum` (in fact `oplusTok ◁
sumTok`) |
| `𝒟 ⊴ 𝒟 ⊕ ℰ` | **true** | `inl_trianglelefteq_oplus` |
| `(𝒟 →⊥ ℰ) ⊴ (𝒟 → ℰ)` | **true** | `strictFun_trianglelefteq_funSpace` |
| `𝒟 ⊴ 𝒟 ⊗ ℰ` | **false in general** | `not_trianglelefteq_otimes_unit` |

The smash product collapses the bottom: pairing anything with `⊥_ℰ` is `⊥`. So `𝒟`
embeds in
`𝒟 ⊗ ℰ` only when `ℰ` contributes a (finite) non-bottom point; for the trivial `ℰ
= 𝟙` we have
`𝒟 ⊗ 𝟙 ≅ 𝟙`, refuting the universal claim.

All parts are **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`) except
`(4)`
(`inl_trianglelefteq_oplus`), whose `oplus_mem_leftN` decides the
genuinely-undecidable test
`X = Δ₀` over an arbitrary system and so depends on `Classical.choice`.
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap Domain.Neighborhood.Exercise619
open Domain.Neighborhood.Example62 Domain.Neighborhood.ExampleB
open Domain.Neighborhood.Exercise510

namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

/-! ## (1) `(𝒟 ⊗ ℰ) ◁ (𝒟 × ℰ)` — the smash is literally a subsystem of the product

The smash `otimesTok` has the *same* master `{Λ} ∪ 0Δ₀ ∪ 1Δ₁ = prodTokNbhd Δ₀ Δ₁`
and its proper
neighbourhoods `prodTokNbhd X Y` (with `X ≠ Δ₀`, `Y ≠ Δ₁`) are a sub-family of the
product's
neighbourhoods. The consistency clause is inherited because intersections stay off
the boundary. -/

theorem otimesTok_subsystem_prodTok (D₀ D₁ : NeighborhoodSystem Str) :
    otimesTok D₀ D₁ ◁ prodTok D₀ D₁ where
  master_eq := rfl
  sub := by
    rintro W (rfl | ⟨X, Y, hX, hY, -, -, rfl⟩)
    · exact ⟨D₀.master, D₁.master, D₀.master_mem, D₁.master_mem, rfl⟩
    · exact ⟨X, Y, hX, hY, rfl⟩
  inter_closed := by
    rintro W W' (rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩)
      (rfl | ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩) hInt
    · rw [Set.inter_self]; exact Or.inl rfl
    · rw [prodTokNbhd_inter, Set.inter_eq_right.mpr (D₀.sub_master hX'),
        Set.inter_eq_right.mpr (D₁.sub_master hY')]
      exact Or.inr ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
    · rw [Set.inter_comm, prodTokNbhd_inter, Set.inter_eq_right.mpr (D₀.sub_master hX),
        Set.inter_eq_right.mpr (D₁.sub_master hY)]
      exact Or.inr ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
    · rw [prodTokNbhd_inter] at hInt ⊢
      obtain ⟨A, B, hA, hB, heq⟩ := hInt
      obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective heq
      exact Or.inr ⟨X ∩ X', Y ∩ Y', hA, hB,
        inter_ne_of_ne_left (D₀.sub_master hX) hXne,
        inter_ne_of_ne_left (D₁.sub_master hY) hYne, rfl⟩

/-- **Exercise 6.27 (1).** `(𝒟 ⊗ ℰ) ⊴ (𝒟 × ℰ)`. -/
theorem otimes_trianglelefteq_prod (D₀ D₁ : NeighborhoodSystem Str) :
    otimesTok D₀ D₁ ⊴ prodTok D₀ D₁ :=
  (otimesTok_subsystem_prodTok D₀ D₁).trianglelefteq

/-! ## (2) `𝒟 ⊴ 𝒟 × ℰ` — first-factor projection pair

`𝒟` is not literally a subsystem of `𝒟 × ℰ` (the neighbourhoods have a different
shape), but it
embeds via the projection pair `i(X) = (X, ⊥)`, `j(W) = fst W`. Concretely we send
`X ∈ 𝒟` to the
product neighbourhood `prodTokNbhd X Δ₁` (pair `X` with all of `ℰ`); the
embedding/projection are the
two refinement relations against that neighbourhood, exactly as in Proposition
6.12. -/

/-- The injection `i : 𝒟 → 𝒟 × ℰ`: `X i W ↔ X ∈ 𝒟 ∧ W ∈ 𝒟×ℰ ∧ (X,Δ₁) ⊆ W`. -/
def fstInj (D₀ D₁ : NeighborhoodSystem Str) : ApproximableMap D₀ (prodTok D₀ D₁) where
  rel X W := D₀.mem X ∧ (prodTok D₀ D₁).mem W ∧ prodTokNbhd X D₁.master ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨D₀.master_mem, (prodTok D₀ D₁).master_mem, subset_rfl⟩
  inter_right := by
    rintro X W W' ⟨hX, hW, hsub⟩ ⟨_, hW', hsub'⟩
    exact ⟨hX, (prodTok D₀ D₁).inter_mem hW hW' (prodTok_mem_prodTokNbhd hX D₁.master_mem)
      (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' W W' ⟨_, _, hsub⟩ hX'X hWW' hX' hW'
    exact ⟨hX', hW', ((prodTokNbhd_subset_iff.mpr ⟨hX'X, subset_rfl⟩).trans hsub).trans hWW'⟩

/-- The projection `j : 𝒟 × ℰ → 𝒟`: `W j X ↔ W ∈ 𝒟×ℰ ∧ X ∈ 𝒟 ∧ W ⊆ (X,Δ₁)`. -/
def fstProj (D₀ D₁ : NeighborhoodSystem Str) : ApproximableMap (prodTok D₀ D₁) D₀ where
  rel W X := (prodTok D₀ D₁).mem W ∧ D₀.mem X ∧ W ⊆ prodTokNbhd X D₁.master
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(prodTok D₀ D₁).master_mem, D₀.master_mem, subset_rfl⟩
  inter_right := by
    rintro W X X' ⟨hW, hX, hsub⟩ ⟨_, hX', hsub'⟩
    obtain ⟨A, B, hA, hB, rfl⟩ := hW
    have hAX : A ⊆ X := (prodTokNbhd_subset_iff.mp hsub).1
    have hAX' : A ⊆ X' := (prodTokNbhd_subset_iff.mp hsub').1
    exact ⟨prodTok_mem_prodTokNbhd hA hB, D₀.inter_mem hX hX' hA (Set.subset_inter hAX hAX'),
      prodTokNbhd_subset_iff.mpr ⟨Set.subset_inter hAX hAX', D₁.sub_master hB⟩⟩
  mono := by
    rintro W W' X X' ⟨_, _, hsub⟩ hW'W hXX' hW' hX'
    exact ⟨hW', hX', hW'W.trans (hsub.trans (prodTokNbhd_subset_iff.mpr ⟨hXX', subset_rfl⟩))⟩

theorem fstProj_comp_fstInj (D₀ D₁ : NeighborhoodSystem Str) :
    (fstProj D₀ D₁).comp (fstInj D₀ D₁) = idMap D₀ := by
  apply ApproximableMap.ext
  intro X Z
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨W, ⟨hX, _, hsub⟩, _, hZ, hsub'⟩
    exact ⟨hX, hZ, (prodTokNbhd_subset_iff.mp (hsub.trans hsub')).1⟩
  · rintro ⟨hX, hZ, hXZ⟩
    exact ⟨prodTokNbhd Z D₁.master,
      ⟨hX, prodTok_mem_prodTokNbhd hZ D₁.master_mem,
        prodTokNbhd_subset_iff.mpr ⟨hXZ, subset_rfl⟩⟩,
      prodTok_mem_prodTokNbhd hZ D₁.master_mem, hZ, subset_rfl⟩

theorem fstInj_comp_fstProj_le (D₀ D₁ : NeighborhoodSystem Str) :
    (fstInj D₀ D₁).comp (fstProj D₀ D₁) ≤ idMap (prodTok D₀ D₁) := by
  intro W W' hr
  obtain ⟨X, ⟨hW, _, hsub⟩, _, hW', hsub'⟩ := hr
  exact ⟨hW, hW', hsub.trans hsub'⟩

/-- **Exercise 6.27 (2).** `𝒟 ⊴ 𝒟 × ℰ`. -/
theorem fst_trianglelefteq_prod (D₀ D₁ : NeighborhoodSystem Str) :
    D₀ ⊴ prodTok D₀ D₁ :=
  trianglelefteq_of_projectionPair (fstInj D₀ D₁) (fstProj D₀ D₁)
    (fstProj_comp_fstInj D₀ D₁) (fstInj_comp_fstProj_le D₀ D₁)

/-! ## (3) `(𝒟 ⊕ ℰ) ◁ (𝒟 + ℰ)` — the coalesced sum is literally a subsystem of the
sum

`oplusTok` drops the improper copies `0Δ₀`, `1Δ₁` of `sumTok`; what remains is a
sub-family, and
consistency is inherited (cross-tag intersections are empty, hence not
`sumTok`-neighbourhoods). -/

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem oplusTok_subsystem_sumTok (h₀ : ∀ X, D₀.mem X → X.Nonempty)
    (h₁ : ∀ Y, D₁.mem Y → Y.Nonempty) :
    oplusTok D₀ D₁ h₀ h₁ ◁ sumTok D₀ D₁ h₀ h₁ where
  master_eq := rfl
  sub := by
    rintro W (rfl | ⟨X, hX, -, rfl⟩ | ⟨Y, hY, -, rfl⟩)
    · exact Or.inl rfl
    · exact sumTok_mem_embF hX
    · exact sumTok_mem_embT hY
  inter_closed := by
    rintro W W' (rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩)
      (rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩) hInt
    · rw [Set.inter_self]; exact Or.inl rfl
    · rw [sumTokMaster_inter_embF hX']; exact oplusTok_mem_embF hX' hX'ne
    · rw [sumTokMaster_inter_embT hY']; exact oplusTok_mem_embT hY' hY'ne
    · rw [Set.inter_comm, sumTokMaster_inter_embF hX]; exact oplusTok_mem_embF hX hXne
    · rw [embBit_inter] at hInt ⊢
      exact oplusTok_mem_embF (sumTok_mem_embF_inv hInt)
        (inter_ne_of_ne_left (D₀.sub_master hX) hXne)
    · rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hInt
      exact absurd (sumTok_mem_nonempty hInt) Set.not_nonempty_empty
    · rw [Set.inter_comm, sumTokMaster_inter_embT hY]; exact oplusTok_mem_embT hY hYne
    · rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hInt
      exact absurd (sumTok_mem_nonempty hInt) Set.not_nonempty_empty
    · rw [embBit_inter] at hInt ⊢
      exact oplusTok_mem_embT (sumTok_mem_embT_inv hInt)
        (inter_ne_of_ne_left (D₁.sub_master hY) hYne)

/-- **Exercise 6.27 (3).** `(𝒟 ⊕ ℰ) ⊴ (𝒟 + ℰ)`. -/
theorem oplus_trianglelefteq_sum (h₀ : ∀ X, D₀.mem X → X.Nonempty)
    (h₁ : ∀ Y, D₁.mem Y → Y.Nonempty) :
    oplusTok D₀ D₁ h₀ h₁ ⊴ sumTok D₀ D₁ h₀ h₁ :=
  (oplusTok_subsystem_sumTok h₀ h₁).trianglelefteq

/-! ## (4) `𝒟 ⊴ 𝒟 ⊕ ℰ` — left-injection projection pair

Unlike the product, the coalesced sum *identifies* the two bottoms, so the
embedding of `𝒟` must
send `⊥_𝒟 = Δ₀` to the shared bottom `sumTokMaster` and a proper `X` to its left
copy `0X`. We
package this in `leftN X` (`= 0X` for proper `X`, `= sumTokMaster` for `X = Δ₀`).

Distinguishing the two cases is exactly the test `X = Δ₀`, which is undecidable
for an arbitrary
neighbourhood; consequently the single lemma `oplus_mem_leftN` — and only it —
uses `Classical.em`.
This is genuinely unavoidable at this level of generality (Scott's tokens are
concrete and decidable,
but we work over arbitrary `NeighborhoodSystem`s), so `inl_trianglelefteq_oplus`
depends on
`Classical.choice` (called out in the axiom audit). Every other part of Exercise
6.27 is choice-free. -/

/-- The left-copy generator: `0X` for proper `X`, the shared bottom `sumTokMaster`
for `X = Δ₀`. The
set-builder `{w ∣ w ∈ sumTokMaster ∧ X = Δ₀}` keeps the *definition* choice-free. -/
def leftN (D₀ D₁ : NeighborhoodSystem Str) (X : Set Str) : Set Str :=
  embBit false X ∪ {w | w ∈ sumTokMaster D₀ D₁ ∧ X = D₀.master}

theorem embF_subset_leftN {X : Set Str} : embBit false X ⊆ leftN D₀ D₁ X :=
  Set.subset_union_left

theorem leftN_master : leftN D₀ D₁ D₀.master = sumTokMaster D₀ D₁ := by
  apply Set.eq_of_subset_of_subset
  · rintro w (hw | ⟨hw, -⟩)
    · exact embF_subset_sumTokMaster D₀.master_mem hw
    · exact hw
  · exact fun w hw => Or.inr ⟨hw, rfl⟩

theorem leftN_proper {X : Set Str} (hne : X ≠ D₀.master) : leftN D₀ D₁ X = embBit false X := by
  apply Set.eq_of_subset_of_subset
  · rintro w (hw | ⟨-, hXm⟩)
    · exact hw
    · exact absurd hXm hne
  · exact embF_subset_leftN

theorem X_eq_master_of_nil_mem_leftN {X : Set Str} (h : ([] : Str) ∈ leftN D₀ D₁ X) :
    X = D₀.master := by
  rcases h with h | ⟨-, h⟩
  · exact absurd h nil_not_mem_embBit
  · exact h

theorem subset_of_embF_subset_leftN {A X : Set Str} (hA : A ⊆ D₀.master)
    (h : embBit false A ⊆ leftN D₀ D₁ X) : A ⊆ X := by
  intro σ hσ
  rcases h ⟨σ, rfl, hσ⟩ with ⟨w', hw', hw'X⟩ | ⟨-, hXm⟩
  · rw [List.cons.injEq] at hw'; rw [hw'.2]; exact hw'X
  · rw [hXm]; exact hA hσ

theorem X_eq_master_of_embT_subset_leftN {B X : Set Str} (hB : B.Nonempty)
    (h : embBit true B ⊆ leftN D₀ D₁ X) : X = D₀.master := by
  obtain ⟨σ, hσ⟩ := hB
  rcases h ⟨σ, rfl, hσ⟩ with ⟨w', hw', -⟩ | ⟨-, hXm⟩
  · rw [List.cons.injEq] at hw'; exact absurd hw'.1 (by decide)
  · exact hXm

theorem leftN_subset_iff {X X' : Set Str} (hX : D₀.mem X) (hX' : D₀.mem X') :
    leftN D₀ D₁ X ⊆ leftN D₀ D₁ X' ↔ X ⊆ X' := by
  constructor
  · intro h
    exact subset_of_embF_subset_leftN (D₀.sub_master hX) (embF_subset_leftN.trans h)
  · intro hXX'
    rintro w (⟨w', rfl, hw'⟩ | ⟨hw, hXm⟩)
    · exact embF_subset_leftN ⟨w', rfl, hXX' hw'⟩
    · exact Or.inr ⟨hw, Set.Subset.antisymm (D₀.sub_master hX') (hXm ▸ hXX')⟩

/-- The **only** classical step in Exercise 6.27: `leftN X` is an `𝒟 ⊕
ℰ`-neighbourhood. The proof
splits on the (undecidable for arbitrary `X`) test `X = Δ₀`. -/
theorem oplus_mem_leftN {X : Set Str} (hX : D₀.mem X) :
    (oplusTok D₀ D₁ h₀ h₁).mem (leftN D₀ D₁ X) := by
  by_cases h : X = D₀.master
  · rw [h, leftN_master]; exact (oplusTok D₀ D₁ h₀ h₁).master_mem
  · rw [leftN_proper h]; exact oplusTok_mem_embF hX h

/-- The injection `i : 𝒟 → 𝒟 ⊕ ℰ`: `X i W ↔ X ∈ 𝒟 ∧ W ∈ 𝒟⊕ℰ ∧ leftN X ⊆ W`. -/
def inlInj : ApproximableMap D₀ (oplusTok D₀ D₁ h₀ h₁) where
  rel X W := D₀.mem X ∧ (oplusTok D₀ D₁ h₀ h₁).mem W ∧ leftN D₀ D₁ X ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨D₀.master_mem, (oplusTok D₀ D₁ h₀ h₁).master_mem, leftN_master.le⟩
  inter_right := by
    rintro X W W' ⟨hX, hW, hsub⟩ ⟨_, hW', hsub'⟩
    exact ⟨hX, (oplusTok D₀ D₁ h₀ h₁).inter_mem hW hW' (oplus_mem_leftN hX)
      (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' W W' ⟨hX, _, hsub⟩ hX'X hWW' hX' hW'
    exact ⟨hX', hW', ((leftN_subset_iff hX' hX).mpr hX'X).trans (hsub.trans hWW')⟩

/-- The projection `j : 𝒟 ⊕ ℰ → 𝒟`: `W j X ↔ W ∈ 𝒟⊕ℰ ∧ X ∈ 𝒟 ∧ W ⊆ leftN X`. -/
def inlProj : ApproximableMap (oplusTok D₀ D₁ h₀ h₁) D₀ where
  rel W X := (oplusTok D₀ D₁ h₀ h₁).mem W ∧ D₀.mem X ∧ W ⊆ leftN D₀ D₁ X
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(oplusTok D₀ D₁ h₀ h₁).master_mem, D₀.master_mem, leftN_master.ge⟩
  inter_right := by
    rintro W X X' ⟨hW, hX, hsub⟩ ⟨_, hX', hsub'⟩
    rcases hW with rfl | ⟨A, hA, hAne, rfl⟩ | ⟨B, hB, hBne, rfl⟩
    · have hXm := X_eq_master_of_nil_mem_leftN (hsub nil_mem_sumTokMaster)
      have hX'm := X_eq_master_of_nil_mem_leftN (hsub' nil_mem_sumTokMaster)
      subst hXm; subst hX'm; rw [Set.inter_self]
      exact ⟨Or.inl rfl, D₀.master_mem, leftN_master.ge⟩
    · have hAX : A ⊆ X := subset_of_embF_subset_leftN (D₀.sub_master hA) hsub
      have hAX' : A ⊆ X' := subset_of_embF_subset_leftN (D₀.sub_master hA) hsub'
      exact ⟨oplusTok_mem_embF hA hAne, D₀.inter_mem hX hX' hA (Set.subset_inter hAX hAX'),
        (embBit_subset.mpr (Set.subset_inter hAX hAX')).trans embF_subset_leftN⟩
    · have hXm := X_eq_master_of_embT_subset_leftN (h₁ B hB) hsub
      have hX'm := X_eq_master_of_embT_subset_leftN (h₁ B hB) hsub'
      subst hXm; subst hX'm; rw [Set.inter_self]
      exact ⟨oplusTok_mem_embT hB hBne, D₀.master_mem, by
        rw [leftN_master]; exact embT_subset_sumTokMaster hB⟩
  mono := by
    rintro W W' X X' ⟨_, hX, hsub⟩ hW'W hXX' hW' hX'
    exact ⟨hW', hX', hW'W.trans (hsub.trans ((leftN_subset_iff hX hX').mpr hXX'))⟩

theorem inlProj_comp_inlInj :
    (inlProj (D₀ := D₀) (D₁ := D₁) (h₀ := h₀) (h₁ := h₁)).comp inlInj = idMap D₀ := by
  apply ApproximableMap.ext
  intro X Z
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨W, ⟨hX, _, hsub⟩, _, hZ, hsub'⟩
    exact ⟨hX, hZ, (leftN_subset_iff hX hZ).mp (hsub.trans hsub')⟩
  · rintro ⟨hX, hZ, hXZ⟩
    exact ⟨leftN D₀ D₁ X, ⟨hX, oplus_mem_leftN hX, subset_rfl⟩,
      oplus_mem_leftN hX, hZ, (leftN_subset_iff hX hZ).mpr hXZ⟩

theorem inlInj_comp_inlProj_le :
    (inlInj (D₀ := D₀) (D₁ := D₁) (h₀ := h₀) (h₁ := h₁)).comp inlProj
      ≤ idMap (oplusTok D₀ D₁ h₀ h₁) := by
  intro W W' hr
  obtain ⟨X, ⟨hW, _, hsub⟩, _, hW', hsub'⟩ := hr
  exact ⟨hW, hW', hsub.trans hsub'⟩

/-- **Exercise 6.27 (4).** `𝒟 ⊴ 𝒟 ⊕ ℰ`. (Uses `Classical.choice` via
`oplus_mem_leftN`.) -/
theorem inl_trianglelefteq_oplus :
    D₀ ⊴ oplusTok D₀ D₁ h₀ h₁ :=
  trianglelefteq_of_projectionPair inlInj inlProj inlProj_comp_inlInj inlInj_comp_inlProj_le

/-! ## (5) `(𝒟 →⊥ ℰ) ⊴ (𝒟 → ℰ)` — the strict maps embed in all maps

A strict map *is* an approximable map, so `𝒟 →⊥ ℰ` sits inside `𝒟 → ℰ` by
inclusion `i`, with the
*strictification* `j` (force `f(⊥) = ⊥`) as its retraction. `strictify f ⊑ f`
always, and on a strict
`f` strictification is the identity; this gives the projection-pair laws `j ∘ i =
id`,
`i ∘ j ⊑ id`. We work over **arbitrary** systems `V₀, V₁` (not just `Str`); the
construction is
choice-free. We realise `i, j` on principal inputs via `ofMono` of the
element-level inclusion /
strictification, then identify their element maps using the representations
`funSpaceEquiv`
(`|𝒟→ℰ| ≃ ApproximableMap`) and `strictFunEquiv` (`|𝒟→⊥ℰ| ≃ StrictMap`). -/

section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Strictification of a map** (on relations): keep `f` but force the master
input to the master
output. The resulting map is strict, lies below `f`, and is the identity on strict
maps. -/
def strictifyMap (g : ApproximableMap V₀ V₁) : ApproximableMap V₀ V₁ where
  rel X Y := g.rel X Y ∧ (X = V₀.master → Y = V₁.master)
  rel_dom h := g.rel_dom h.1
  rel_cod h := g.rel_cod h.1
  master_rel := ⟨g.master_rel, fun _ => rfl⟩
  inter_right := by
    rintro X Y Y' ⟨hg, hs⟩ ⟨hg', hs'⟩
    exact ⟨g.inter_right hg hg', fun hX => by rw [hs hX, hs' hX, Set.inter_self]⟩
  mono := by
    rintro X X' Y Y' ⟨hg, hs⟩ hX'X hYY' hX' hY'
    refine ⟨g.mono hg hX'X hYY' hX' hY', fun hX'm => ?_⟩
    have hX : V₀.mem X := g.rel_dom hg
    have hXm : X = V₀.master := Set.Subset.antisymm (V₀.sub_master hX) (hX'm ▸ hX'X)
    exact Set.Subset.antisymm (V₁.sub_master hY') ((hs hXm) ▸ hYY')

theorem strictifyMap_isStrict (g : ApproximableMap V₀ V₁) : IsStrict (strictifyMap g) :=
  fun _ h => h.2 rfl

theorem strictifyMap_le (g : ApproximableMap V₀ V₁) : strictifyMap g ≤ g := fun _ _ h => h.1

theorem strictifyMap_of_isStrict {f : ApproximableMap V₀ V₁} (hf : IsStrict f) :
    strictifyMap f = f := by
  apply ApproximableMap.ext
  intro X Y
  exact ⟨fun h => h.1, fun h => ⟨h, fun hXm => hf (hXm ▸ h)⟩⟩

/-- The strictification as an element of the *strict* function space's token type. -/
def strictify (g : ApproximableMap V₀ V₁) :
  StrictMap V₀ V₁ := ⟨strictifyMap g, strictifyMap_isStrict g⟩

/-- The four inverse identities of the two representation equivalences (defeq
unfoldings). -/
theorem toApproxMap_toFilter (g : ApproximableMap V₀ V₁) : toApproxMap (toFilter g) = g :=
  (funSpaceEquiv V₀ V₁).apply_symm_apply g

theorem toFilter_toApproxMap (ψ : (funSpace V₀ V₁).Element) : toFilter (toApproxMap ψ) = ψ :=
  (funSpaceEquiv V₀ V₁).symm_apply_apply ψ

theorem toStrictMap_toStrictFilter (g : StrictMap V₀ V₁) : toStrictMap (toStrictFilter g) = g :=
  (strictFunEquiv V₀ V₁).apply_symm_apply g

theorem toStrictFilter_toStrictMap (φ : (strictFun V₀ V₁).Element) :
    toStrictFilter (toStrictMap φ) = φ :=
  (strictFunEquiv V₀ V₁).symm_apply_apply φ

/-- Element-level inclusion `|𝒟 →⊥ ℰ| → |𝒟 → ℰ|`. -/
def incl (φ : (strictFun V₀ V₁).Element) : (funSpace V₀ V₁).Element :=
  toFilter (toStrictMap φ).1

/-- Element-level strictification `|𝒟 → ℰ| → |𝒟 →⊥ ℰ|`. -/
def strct (ψ : (funSpace V₀ V₁).Element) : (strictFun V₀ V₁).Element :=
  toStrictFilter (strictify (toApproxMap ψ))

theorem incl_mono : Monotone (incl (V₀ := V₀) (V₁ := V₁)) := by
  intro a b hab M hM
  obtain ⟨hMmem, haM⟩ := hM
  obtain ⟨⟨L, hL, rfl⟩, hne⟩ := hMmem
  refine ⟨⟨⟨L, hL, rfl⟩, hne⟩, ?_⟩
  intro p hp
  have hle : (toStrictMap a).1 ≤ (toStrictMap b).1 := (strictFunEquiv V₀ V₁).monotone hab
  exact hle p.1 p.2 (haM p hp)

theorem strct_mono : Monotone (strct (V₀ := V₀) (V₁ := V₁)) := by
  intro a b hab W hW
  obtain ⟨hWmem, haW⟩ := hW
  obtain ⟨⟨L, hL, rfl⟩, hne⟩ := hWmem
  refine ⟨⟨⟨L, hL, rfl⟩, hne⟩, ?_⟩
  intro p hp
  have hle : toApproxMap a ≤ toApproxMap b := (funSpaceEquiv V₀ V₁).monotone hab
  exact ⟨hle p.1 p.2 (haW p hp).1, (haW p hp).2⟩

/-- The inclusion `i : 𝒟 →⊥ ℰ ↪ 𝒟 → ℰ`. -/
def inclMap : ApproximableMap (strictFun V₀ V₁) (funSpace V₀ V₁) :=
  ofMono (fun _ hW => incl ((strictFun V₀ V₁).principal hW))
    (fun _ _ hW hW' hW'W => incl_mono (((strictFun V₀ V₁).principal_le_iff hW hW').mpr hW'W))

/-- The strictification retraction `j : 𝒟 → ℰ → 𝒟 →⊥ ℰ`. -/
def strctMap : ApproximableMap (funSpace V₀ V₁) (strictFun V₀ V₁) :=
  ofMono (fun _ hM => strct ((funSpace V₀ V₁).principal hM))
    (fun _ _ hM hM' hM'M => strct_mono (((funSpace V₀ V₁).principal_le_iff hM hM').mpr hM'M))

theorem toElementMap_inclMap (φ : (strictFun V₀ V₁).Element) :
    inclMap.toElementMap φ = incl φ := by
  apply Element.ext
  intro M
  constructor
  · rintro ⟨W, hφW, _, hincl⟩
    obtain ⟨hMmem, hg⟩ := hincl
    obtain ⟨⟨L, hL, rfl⟩, hne⟩ := hMmem
    refine ⟨⟨⟨L, hL, rfl⟩, hne⟩, ?_⟩
    intro p hp
    obtain ⟨hsstep, hWsub⟩ := toStrictMap_rel.mp (hg p hp)
    exact φ.up_mem hφW hsstep hWsub
  · rintro ⟨hMmem, hgφ⟩
    obtain ⟨⟨L, hL, rfl⟩, hne⟩ := hMmem
    have hφL : φ.mem (sstepFun L) :=
      (mem_sstepFun_iff φ hL).mpr (fun p hp => toStrictMap_rel.mp (hgφ p hp))
    refine ⟨sstepFun L, hφL, φ.sub hφL, ⟨⟨L, hL, rfl⟩, hne⟩, ?_⟩
    intro p hp
    exact ⟨φ.sub (toStrictMap_rel.mp (hgφ p hp)), fun f hf => hf p hp⟩

theorem toElementMap_strctMap (ψ : (funSpace V₀ V₁).Element) :
    strctMap.toElementMap ψ = strct ψ := by
  apply Element.ext
  intro W
  constructor
  · rintro ⟨M, hψM, _, hstrct⟩
    obtain ⟨hWmem, hg⟩ := hstrct
    obtain ⟨⟨L, hL, rfl⟩, hne⟩ := hWmem
    refine ⟨⟨⟨L, hL, rfl⟩, hne⟩, ?_⟩
    intro p hp
    obtain ⟨hstepmem, hMsub⟩ := (hg p hp).1
    exact ⟨ψ.up_mem hψM hstepmem hMsub, (hg p hp).2⟩
  · rintro ⟨hWmem, hgψ⟩
    obtain ⟨⟨L, hL, rfl⟩, hne⟩ := hWmem
    have hψL : ψ.mem (stepFun L) :=
      (mem_stepFun_iff ψ hL).mpr (fun p hp => (hgψ p hp).1)
    refine ⟨stepFun L, hψL, ψ.sub hψL, ⟨⟨L, hL, rfl⟩, hne⟩, ?_⟩
    intro p hp
    exact ⟨⟨ψ.sub (hgψ p hp).1, fun f hf => hf p hp⟩, (hgψ p hp).2⟩

theorem strct_incl (φ : (strictFun V₀ V₁).Element) : strct (incl φ) = φ := by
  change toStrictFilter (strictify (toApproxMap (toFilter (toStrictMap φ).1))) = φ
  rw [toApproxMap_toFilter,
    show strictify (toStrictMap φ).1 = toStrictMap φ from
      Subtype.ext (strictifyMap_of_isStrict (toStrictMap φ).2)]
  exact toStrictFilter_toStrictMap φ

theorem incl_strct_le (ψ : (funSpace V₀ V₁).Element) : incl (strct ψ) ≤ ψ := by
  have key : incl (strct ψ) = toFilter (strictifyMap (toApproxMap ψ)) := by
    change toFilter (toStrictMap (strct ψ)).1 = toFilter (strictifyMap (toApproxMap ψ))
    rw [show toStrictMap (strct ψ) = strictify (toApproxMap ψ) from toStrictMap_toStrictFilter _]
    rfl
  rw [key]
  conv_rhs => rw [← toFilter_toApproxMap ψ]
  exact (funSpaceEquiv V₀ V₁).symm.monotone (strictifyMap_le (toApproxMap ψ))

/-- Choice-free extensionality from agreement on principal inputs. Unlike
`ext_of_toElementMap`
(which splits on the undecidable `V₀.mem X`), both sides of the relation carry
domain membership via
`rel_dom`, so no case analysis — and hence no `Classical.choice` — is needed. -/
theorem ext_of_principal {γ δ : Type*} {W₀ : NeighborhoodSystem γ} {W₁ : NeighborhoodSystem δ}
    {f g : ApproximableMap W₀ W₁}
    (h : ∀ (X : Set γ) (hX : W₀.mem X),
      f.toElementMap (W₀.principal hX) = g.toElementMap (W₀.principal hX)) : f = g := by
  apply ApproximableMap.ext
  intro X Y
  constructor
  · intro hr
    have hX := f.rel_dom hr
    rw [g.rel_iff_mem_principal hX, ← h X hX, ← f.rel_iff_mem_principal hX]; exact hr
  · intro hr
    have hX := g.rel_dom hr
    rw [f.rel_iff_mem_principal hX, h X hX, ← g.rel_iff_mem_principal hX]; exact hr

theorem strctMap_comp_inclMap :
    (strctMap (V₀ := V₀) (V₁ := V₁)).comp inclMap = idMap (strictFun V₀ V₁) := by
  apply ext_of_principal
  intro X hX
  rw [toElementMap_comp, toElementMap_inclMap, toElementMap_strctMap, strct_incl,
    toElementMap_idMap]

theorem inclMap_comp_strctMap_le :
    (inclMap (V₀ := V₀) (V₁ := V₁)).comp strctMap ≤ idMap (funSpace V₀ V₁) := by
  rw [le_iff_toElementMap_le]
  intro ψ
  rw [toElementMap_comp, toElementMap_strctMap, toElementMap_inclMap, toElementMap_idMap]
  exact incl_strct_le ψ

/-- **Exercise 6.27 (5).** `(𝒟 →⊥ ℰ) ⊴ (𝒟 → ℰ)` for all `𝒟, ℰ` (choice-free). -/
theorem strictFun_trianglelefteq_funSpace (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    strictFun V₀ V₁ ⊴ funSpace V₀ V₁ :=
  trianglelefteq_of_projectionPair inclMap strctMap strctMap_comp_inclMap inclMap_comp_strctMap_le

end Part5

/-! ## (6) `𝒟 ⊴ 𝒟 ⊗ ℰ` is **false** in general

The smash product sends `(x, ⊥)` and `(⊥, y)` to the single bottom, so if `ℰ`
contributes no proper
neighbourhood the whole product collapses to its bottom. Concretely, for the
one-point unit `ℰ = 𝟙`
the system `𝒟 ⊗ 𝟙` has *only* its master as a neighbourhood, hence a one-point
element lattice; a
`𝒟` with two distinct points therefore cannot embed. This refutes the universal
claim. -/

/-- If a system's only neighbourhood is its master, its element lattice is a
single point (`⊥`). -/
theorem subsingleton_element_of_only_master {γ : Type*} {V : NeighborhoodSystem γ}
    (h : ∀ X, V.mem X → X = V.master) : Subsingleton V.Element := by
  refine ⟨fun x y => ?_⟩
  apply Element.ext
  intro X
  constructor
  · intro hx; have hXm := h X (x.sub hx); rw [hXm]; exact y.master_mem
  · intro hy; have hXm := h X (y.sub hy); rw [hXm]; exact x.master_mem

/-- A concrete two-point domain over `{0,1}*`: neighbourhoods `Set.univ` (`= ⊥`)
and `{[]}`. -/
def twoPt : NeighborhoodSystem Str where
  mem X := X = Set.univ ∨ X = {[]}
  master := Set.univ
  master_mem := Or.inl rfl
  sub_master := by
    rintro X (rfl | rfl)
    · exact subset_rfl
    · exact Set.subset_univ _
  inter_mem := by
    rintro X Y Z (rfl | rfl) (rfl | rfl) _ _
    · rw [Set.inter_self]; exact Or.inl rfl
    · rw [Set.univ_inter]; exact Or.inr rfl
    · rw [Set.inter_univ]; exact Or.inr rfl
    · rw [Set.inter_self]; exact Or.inr rfl

/-- The one-point unit domain `𝟙` over `{0,1}*` (only neighbourhood `{[]}`). -/
def unitPt : NeighborhoodSystem Str := (singletonSys ({[]} : Set Str) ⟨[], rfl⟩).sys

/-- With the unit second factor, the smash `twoPt ⊗ 𝟙` collapses to its master. -/
theorem otimes_unitPt_collapse :
    ∀ W, (otimesTok twoPt unitPt).mem W → W = (otimesTok twoPt unitPt).master := by
  rintro W (rfl | ⟨X, Y, _, hY, _, hYne, rfl⟩)
  · rfl
  · exact absurd hY hYne

/-- **Exercise 6.27 (6).** `𝒟 ⊴ 𝒟 ⊗ ℰ` does **not** hold for all `𝒟, ℰ`: take `𝒟`
two-point and
`ℰ = 𝟙`. Then `𝒟 ⊗ 𝟙` has a one-point element lattice while `𝒟` has two, so no
isomorphism onto a
subsystem can exist. -/
theorem not_trianglelefteq_otimes :
    ¬ (twoPt ⊴ otimesTok twoPt unitPt) := by
  rintro ⟨D', hsub, ⟨e⟩⟩
  have hD'only : ∀ X, D'.mem X → X = D'.master := by
    intro X hX
    rw [otimes_unitPt_collapse X (hsub.sub hX)]; exact hsub.master_eq.symm
  have hss : Subsingleton D'.Element := subsingleton_element_of_only_master hD'only
  have hPmem : twoPt.mem ({[]} : Set Str) := Or.inr rfl
  have hne : twoPt.principal hPmem ≠ twoPt.principal twoPt.master_mem := by
    intro heq
    have h1 : (twoPt.principal hPmem).mem ({[]} : Set Str) := ⟨hPmem, subset_rfl⟩
    rw [heq] at h1
    obtain ⟨-, h2⟩ := h1
    exact absurd (Set.mem_singleton_iff.mp (h2 (Set.mem_univ ([false] : Str))) :
      ([false] : Str) = []) (by decide)
  exact hne (e.injective (hss.allEq (e (twoPt.principal hPmem))
    (e (twoPt.principal twoPt.master_mem))))

end Exercise627

end Domain.Neighborhood
