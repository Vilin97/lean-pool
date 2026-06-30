/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Exercise318

/-!
# Exercise 3.19 (Scott 1981, PRG-19, §3) — the sum functor `f + g`

Given approximable mappings `f : 𝒟₀ → 𝒟₀'` and `g : 𝒟₁ → 𝒟₁'`, Scott's Exercise
3.19 also asks for the
*sum* mapping `f + g : 𝒟₀ + 𝒟₁ → 𝒟₀' + 𝒟₁'`, characterized (equations (iii), (iv))
by

* `out₀ ∘ (f + g) ∘ in₀ = f`, and
* `out₁ ∘ (f + g) ∘ in₁ = g`.

We build `f + g` (`sumMap`) directly as a relation between sum-neighbourhoods: it
routes the left copy
`0X` through `f` (to `0Y'`), the right copy `1Y` through `g` (to `1Y'`), and sends
everything to the
master neighbourhood `{Λ} ∪ 0Δ₀' ∪ 1Δ₁'`. The disjointness of the two tagged
copies (Exercise 3.18) is
exactly what makes this a well-defined approximable mapping — a left input can
never produce a
right-tagged output, so there is no cross-contamination through `g(⊥)`.

Scott also asks whether (iii), (iv) *uniquely* determine `f + g`: they do **not**,
because the behaviour
on the basepoint `Λ` (i.e. `(f + g)(⊥)`) is unconstrained; our choice sends `Λ` to
`Λ`.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
variable {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}

/-! ### Structural extraction lemmas for sum-neighbourhoods. -/

/-- A sum-neighbourhood contained in a *left* copy `0X` is itself a left copy
`0X₂` (the
basepoint and
the right copy are excluded, using non-emptiness). -/
theorem mem_subset_inj₀ {W : Set (Option (α ⊕ β))} {X : Set α}
    (hW : (sum V₀ V₁ h₀ h₁).mem W) (hsub : W ⊆ inj₀ X) :
    ∃ X₂, V₀.mem X₂ ∧ W = inj₀ X₂ := by
  rcases hW with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩
  · exact absurd (hsub none_mem_sumMaster) none_mem_inj₀
  · exact ⟨X₂, hX₂, rfl⟩
  · obtain ⟨b, hb⟩ := h₁ Y₂ hY₂
    exact absurd (hsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀

/-- A sum-neighbourhood contained in a *right* copy `1Y` is itself a right copy
`1Y₂`. -/
theorem mem_subset_inj₁ {W : Set (Option (α ⊕ β))} {Y : Set β}
    (hW : (sum V₀ V₁ h₀ h₁).mem W) (hsub : W ⊆ inj₁ Y) :
    ∃ Y₂, V₁.mem Y₂ ∧ W = inj₁ Y₂ := by
  rcases hW with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩
  · exact absurd (hsub none_mem_sumMaster) none_mem_inj₁
  · obtain ⟨a, ha⟩ := h₀ X₂ hX₂
    exact absurd (hsub (il_mem_inj₀.mpr ha)) il_mem_inj₁
  · exact ⟨Y₂, hY₂, rfl⟩

/-- A sum-neighbourhood that *contains* the master is the master. -/
theorem eq_sumMaster_of_subset {W : Set (Option (α ⊕ β))}
    (hW : (sum V₀ V₁ h₀ h₁).mem W) (hsub : sumMaster V₀ V₁ ⊆ W) :
    W = sumMaster V₀ V₁ :=
  Set.Subset.antisymm ((sum V₀ V₁ h₀ h₁).sub_master hW) hsub

/-- A nonempty left copy is never contained in a right copy. -/
theorem not_inj₀_subset_inj₁ {X : Set α} {Y : Set β} (hX : X.Nonempty)
    (hsub : (inj₀ X : Set (Option (α ⊕ β))) ⊆ inj₁ Y) : False := by
  obtain ⟨a, ha⟩ := hX
  exact il_mem_inj₁ (hsub (il_mem_inj₀.mpr ha))

/-- A nonempty right copy is never contained in a left copy. -/
theorem not_inj₁_subset_inj₀ {X : Set α} {Y : Set β} (hY : Y.Nonempty)
    (hsub : (inj₁ Y : Set (Option (α ⊕ β))) ⊆ inj₀ X) : False := by
  obtain ⟨b, hb⟩ := hY
  exact ir_mem_inj₀ (hsub (ir_mem_inj₁.mpr hb))

/-! ### The sum mapping `f + g`. -/

/-- **Exercise 3.19 (Scott 1981, PRG-19).** The *sum mapping* `f + g : 𝒟₀ + 𝒟₁ →
𝒟₀' + 𝒟₁'`. As a
relation between sum-neighbourhoods, `W (f+g) W'` holds iff `W'` is the codomain
master, or `W = 0X`
with `W' = 0Y'` and `X f Y'`, or `W = 1Y` with `W' = 1Y'` and `Y g Y'`. -/
def sumMap (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁') :
    ApproximableMap (sum V₀ V₁ h₀ h₁) (sum V₀' V₁' h₀' h₁') where
  rel W W' := (sum V₀ V₁ h₀ h₁).mem W ∧ (sum V₀' V₁' h₀' h₁').mem W' ∧
    (W' = sumMaster V₀' V₁' ∨
      (∃ X Y', W = inj₀ X ∧ W' = inj₀ Y' ∧ f.rel X Y') ∨
      (∃ Y Y', W = inj₁ Y ∧ W' = inj₁ Y' ∧ g.rel Y Y'))
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(sum V₀ V₁ h₀ h₁).master_mem, (sum V₀' V₁' h₀' h₁').master_mem, Or.inl rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ ⟨hW, hW'₁, hd₁⟩ ⟨_, hW'₂, hd₂⟩
    -- membership of any disjunction-satisfying set
    have hmem : ∀ W'' : Set (Option (α' ⊕ β')),
        (W'' = sumMaster V₀' V₁' ∨
          (∃ X Y', W = inj₀ X ∧ W'' = inj₀ Y' ∧ f.rel X Y') ∨
          (∃ Y Y', W = inj₁ Y ∧ W'' = inj₁ Y' ∧ g.rel Y Y')) →
          (sum V₀' V₁' h₀' h₁').mem W'' := by
      rintro W'' (rfl | ⟨_, Y', _, rfl, hf⟩ | ⟨_, Y', _, rfl, hg⟩)
      · exact (sum V₀' V₁' h₀' h₁').master_mem
      · exact Or.inr (Or.inl ⟨Y', f.rel_cod hf, rfl⟩)
      · exact Or.inr (Or.inr ⟨Y', g.rel_cod hg, rfl⟩)
    -- the disjunction is preserved by intersection
    have key : (W'₁ ∩ W'₂ = sumMaster V₀' V₁' ∨
        (∃ X Y', W = inj₀ X ∧ W'₁ ∩ W'₂ = inj₀ Y' ∧ f.rel X Y') ∨
        (∃ Y Y', W = inj₁ Y ∧ W'₁ ∩ W'₂ = inj₁ Y' ∧ g.rel Y Y')) := by
      rcases hd₁ with rfl | ⟨X, Y'₁, hWX₁, rfl, hf₁⟩ | ⟨Y, Y'₁, hWY₁, rfl, hg₁⟩
      · rw [Set.inter_eq_right.mpr
          (show W'₂ ⊆ sumMaster V₀' V₁' from (sum V₀' V₁' h₀' h₁').sub_master hW'₂)]
        exact hd₂
      · rcases hd₂ with rfl | ⟨X', Y'₂, hWX₂, rfl, hf₂⟩ | ⟨Y', Y'₂, hWY₂, rfl, hg₂⟩
        · rw [Set.inter_eq_left.mpr (inj₀_subset_sumMaster (f.rel_cod hf₁))]
          exact Or.inr (Or.inl ⟨X, Y'₁, hWX₁, rfl, hf₁⟩)
        · obtain rfl : X = X' := inj₀_injective (hWX₁.symm.trans hWX₂)
          rw [inj₀_inter]
          exact Or.inr (Or.inl ⟨X, Y'₁ ∩ Y'₂, hWX₁, rfl, f.inter_right hf₁ hf₂⟩)
        · exact absurd ((hWX₁.symm.trans hWY₂)) (fun h =>
            not_inj₀_subset_inj₁ (h₀ X (f.rel_dom hf₁)) h.subset)
      · rcases hd₂ with rfl | ⟨X', Y'₂, hWX₂, rfl, hf₂⟩ | ⟨Y', Y'₂, hWY₂, rfl, hg₂⟩
        · rw [Set.inter_eq_left.mpr (inj₁_subset_sumMaster (g.rel_cod hg₁))]
          exact Or.inr (Or.inr ⟨Y, Y'₁, hWY₁, rfl, hg₁⟩)
        · exact absurd ((hWY₁.symm.trans hWX₂)) (fun h =>
            not_inj₁_subset_inj₀ (h₁ Y (g.rel_dom hg₁)) h.subset)
        · obtain rfl : Y = Y' := inj₁_injective (hWY₁.symm.trans hWY₂)
          rw [inj₁_inter]
          exact Or.inr (Or.inr ⟨Y, Y'₁ ∩ Y'₂, hWY₁, rfl, g.inter_right hg₁ hg₂⟩)
    exact ⟨hW, hmem _ key, key⟩
  mono := by
    rintro W W₂ W' W'₂ ⟨hW, hW', hd⟩ hW₂W hW'W'₂ hW₂mem hW'₂mem
    refine ⟨hW₂mem, hW'₂mem, ?_⟩
    rcases hd with rfl | ⟨X, Y', rfl, rfl, hf⟩ | ⟨Y, Y', rfl, rfl, hg⟩
    · -- W' = master; W'₂ ⊇ master so W'₂ = master
      left; exact eq_sumMaster_of_subset hW'₂mem hW'W'₂
    · -- left copy: W₂ ⊆ 0X, W'₂ ⊇ 0Y'
      obtain ⟨X₂, hX₂, rfl⟩ := mem_subset_inj₀ hW₂mem hW₂W
      have hXX₂ : X₂ ⊆ X := inj₀_subset_inj₀.mp hW₂W
      rcases hW'₂mem with rfl | ⟨Y'₂, hY'₂, rfl⟩ | ⟨Z'₂, hZ'₂, rfl⟩
      · left; rfl
      · have hY'Y'₂ : Y' ⊆ Y'₂ := inj₀_subset_inj₀.mp hW'W'₂
        exact Or.inr (Or.inl ⟨X₂, Y'₂, rfl, rfl,
          f.mono hf hXX₂ hY'Y'₂ hX₂ hY'₂⟩)
      · exact (not_inj₀_subset_inj₁ (h₀' Y' (f.rel_cod hf)) hW'W'₂).elim
    · -- right copy: W₂ ⊆ 1Y, W'₂ ⊇ 1Y'
      obtain ⟨Y₂, hY₂, rfl⟩ := mem_subset_inj₁ hW₂mem hW₂W
      have hYY₂ : Y₂ ⊆ Y := inj₁_subset_inj₁.mp hW₂W
      rcases hW'₂mem with rfl | ⟨X'₂, hX'₂, rfl⟩ | ⟨Y'₂, hY'₂, rfl⟩
      · left; rfl
      · exact (not_inj₁_subset_inj₀ (h₁' Y' (g.rel_cod hg)) hW'W'₂).elim
      · have hY'Y'₂ : Y' ⊆ Y'₂ := inj₁_subset_inj₁.mp hW'W'₂
        exact Or.inr (Or.inr ⟨Y₂, Y'₂, rfl, rfl,
          g.mono hg hYY₂ hY'Y'₂ hY₂ hY'₂⟩)

/-! ### The defining identities (iii) and (iv). -/

/-- **Exercise 3.19(iii) (Scott 1981, PRG-19).** `out₀ ∘ (f + g) ∘ in₀ = f`. -/
theorem outMap₀_comp_sumMap_comp_inMap₀ (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁') :
    (outMap₀ (h₀ := h₀') (h₁ := h₁')).comp
      ((sumMap (h₀ := h₀) (h₁ := h₁) (h₀' := h₀') (h₁' := h₁') f g).comp
        (inMap₀ (h₀ := h₀) (h₁ := h₁))) = f := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · rintro ⟨W', ⟨W, ⟨hX, _, hinj⟩, hWmem, _, hd⟩, _, hZ, hleft⟩
    rcases hd with rfl | ⟨X₀, Y', hWX₀, rfl, hf⟩ | ⟨Y₀, Y', hWY₀, rfl, hg⟩
    · -- output master: leftPart = Δ₀', and Z ⊇ Δ₀' so Z = Δ₀'
      rw [leftPart_sumMaster] at hleft
      have : Z = V₀'.master := Set.Subset.antisymm (V₀'.sub_master hZ) hleft
      subst this
      exact f.mono f.master_rel (V₀.sub_master hX) subset_rfl hX V₀'.master_mem
    · -- output 0Y': X ⊆ X₀ and Y' ⊆ Z
      rw [leftPart_inj₀] at hleft
      have hXX₀ : X ⊆ X₀ := inj₀_subset_inj₀.mp (hWX₀ ▸ hinj)
      exact f.mono hf hXX₀ hleft hX hZ
    · -- impossible: in₀ forces 0X ⊆ W = 1Y₀
      exact (not_inj₀_subset_inj₁ (h₀ X hX) (hWY₀ ▸ hinj)).elim
  · intro hf
    refine ⟨inj₀ Z, ⟨inj₀ X, ⟨f.rel_dom hf, ?_, subset_rfl⟩, ?_, ?_, ?_⟩, ?_, f.rel_cod hf, ?_⟩
    · exact Or.inr (Or.inl ⟨X, f.rel_dom hf, rfl⟩)
    · exact Or.inr (Or.inl ⟨X, f.rel_dom hf, rfl⟩)
    · exact Or.inr (Or.inl ⟨Z, f.rel_cod hf, rfl⟩)
    · exact Or.inr (Or.inl ⟨X, Z, rfl, rfl, hf⟩)
    · exact Or.inr (Or.inl ⟨Z, f.rel_cod hf, rfl⟩)
    · exact (leftPart_inj₀ V₀' Z).subset

/-- **Exercise 3.19(iv) (Scott 1981, PRG-19).** `out₁ ∘ (f + g) ∘ in₁ = g`. -/
theorem outMap₁_comp_sumMap_comp_inMap₁ (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁') :
    (outMap₁ (h₀ := h₀') (h₁ := h₁')).comp
      ((sumMap (h₀ := h₀) (h₁ := h₁) (h₀' := h₀') (h₁' := h₁') f g).comp
        (inMap₁ (h₀ := h₀) (h₁ := h₁))) = g := by
  apply ApproximableMap.ext
  intro Y Z
  constructor
  · rintro ⟨W', ⟨W, ⟨hY, _, hinj⟩, hWmem, _, hd⟩, _, hZ, hright⟩
    rcases hd with rfl | ⟨X₀, Y', hWX₀, rfl, hf⟩ | ⟨Y₀, Y', hWY₀, rfl, hg⟩
    · rw [rightPart_sumMaster] at hright
      have : Z = V₁'.master := Set.Subset.antisymm (V₁'.sub_master hZ) hright
      subst this
      exact g.mono g.master_rel (V₁.sub_master hY) subset_rfl hY V₁'.master_mem
    · exact (not_inj₁_subset_inj₀ (h₁ Y hY) (hWX₀ ▸ hinj)).elim
    · rw [rightPart_inj₁] at hright
      have hYY₀ : Y ⊆ Y₀ := inj₁_subset_inj₁.mp (hWY₀ ▸ hinj)
      exact g.mono hg hYY₀ hright hY hZ
  · intro hg
    refine ⟨inj₁ Z, ⟨inj₁ Y, ⟨g.rel_dom hg, ?_, subset_rfl⟩, ?_, ?_, ?_⟩, ?_, g.rel_cod hg, ?_⟩
    · exact Or.inr (Or.inr ⟨Y, g.rel_dom hg, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y, g.rel_dom hg, rfl⟩)
    · exact Or.inr (Or.inr ⟨Z, g.rel_cod hg, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y, Z, rfl, rfl, hg⟩)
    · exact Or.inr (Or.inr ⟨Z, g.rel_cod hg, rfl⟩)
    · exact (rightPart_inj₁ V₁' Z).subset

end Domain.Neighborhood
