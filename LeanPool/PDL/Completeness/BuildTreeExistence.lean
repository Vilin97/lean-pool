/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

import LeanPool.PDL.Completeness.BuildTreeModel

/-! # From winning strategies to model graphs, part 3: the existence lemmas (Section 6.3)

This continues `Pdl/BuildTreeModel.lean`. Here we prove the existence lemmas
6.18, 6.19 and 6.20 that are needed for Theorem 6.21 (`strmg`).
-/

namespace PDL

/-! ## The loaded diamond existence lemma (Lemma 6.18) -/

/-- Version of `PreState.atomicLoadedStep` with the loaded diamond given in `π.wForms`. -/
lemma PreState.atomicLoadedStep_wForms {X} {bt : BuildTree [] X} (π : PreState bt) (mπ : Match bt)
    (hmπ : mπ.endSeq = π.val.getLast PreState.nonempty) {a : Nat} {ξ : AnyFormula}
    (h : (WhateverFormula.negLoad (~'⌊·a⌋ξ)) ∈ π.wForms) :
    ∃ (ρ : PreState bt) (mρ : Match bt),
      mρ.endSeq = ρ.val.getLast PreState.nonempty
      ∧ (mρ.btAt.2.2.size < mπ.btAt.2.2.size ∨ ∃ φ, ξ = AnyFormula.normal φ)
      ∧ bt.toModel.2.Rel a π.toW ρ.toW
      ∧ ρ.hasAnf (~''ξ) :=
  π.atomicLoadedStep mπ hmπ
    (Sequent.negLoad_mem_wForms_iff.mp (PreState.negLoad_atomic_mem_getLast h))

/-- The claim of Lemma 6.18 for a fixed program `α`, where the size of the sub-`BuildTree`
we are currently at (`mπ.btAt`) is bounded by `n`. This `n` is used for the inner induction.
Here `π` is the pre-state we start at and `mπ` is a `Match` witnessing where it ends,
and `ρ` is the pre-state we reach.
Note that we use `Rel` from `BuildTree.toModel` as the `R` to use `Modelgraphs.Q`. -/
def LoadedExistsB {X} (bt : BuildTree [] X) (α : Program) (n : ℕ) : Prop :=
  ∀ (π : PreState bt) (mπ : Match bt), mπ.endSeq = π.val.getLast PreState.nonempty →
    mπ.btAt.2.2.size ≤ n →
    ∀ ξ : AnyFormula, (WhateverFormula.negLoad (~'⌊α⌋ξ)) ∈ π.wForms →
    ∃ (ρ : PreState bt) (mρ : Match bt),
      mρ.endSeq = ρ.val.getLast PreState.nonempty
      ∧ (∀ χ, ξ = .loaded χ → mρ.btAt.2.2.size ≤ mπ.btAt.2.2.size)
      ∧ Modelgraphs.Q bt.toModel.2.Rel α π.toW ρ.toW
      ∧ ρ.hasAnf (~''ξ)

/-- Lemma 6.18 for the program `α`, without any bound on where we are in the `BuildTree`. -/
def LoadedExists {X} (bt : BuildTree [] X) (α : Program) : Prop := ∀ n, LoadedExistsB bt α n

/-- Iterating Lemma 6.18 along a list of programs. -/
lemma loadedChain {X} {bt : BuildTree [] X} : ∀ (γs : List Program),
    (∀ γ ∈ γs, LoadedExists bt γ) →
    ∀ (π : PreState bt) (mπ : Match bt), mπ.endSeq = π.val.getLast PreState.nonempty →
    ∀ ξ : AnyFormula, π.hasAnf (~''(AnyFormula.loadBoxes γs ξ)) →
    ∃ (ρ : PreState bt) (mρ : Match bt),
      mρ.endSeq = ρ.val.getLast PreState.nonempty
      ∧ (∀ χ, ξ = .loaded χ → mρ.btAt.2.2.size ≤ mπ.btAt.2.2.size)
      ∧ Qsteps bt.toModel.2.Rel γs π.toW ρ.toW
      ∧ ρ.hasAnf (~''ξ) := by
  intro γs
  induction γs
  case nil =>
    intro _ π mπ hmπ ξ hξ
    exact ⟨ π, mπ, hmπ, fun _ _ => le_refl _, by simp only [Qsteps]; exact ReflBEq.rfl
          , by simpa using! hξ ⟩
  case cons γ rest IH =>
    intro hall π mπ hmπ ξ hξ
    rw [AnyFormula.loadBoxes_cons, PreState.hasAnf_loaded_iff] at hξ
    obtain ⟨ρ0, m0, hm0, hsz0, hQ0, hanf0⟩ :=
      hall γ (by simp) (mπ.btAt.2.2.size) π mπ hmπ (le_refl _) _ hξ
    obtain ⟨ρ, mρ, hmρ, hsz1, hQ1, hanf1⟩ :=
      IH (fun γ' hγ' => hall γ' (by simp [hγ'])) ρ0 m0 hm0 ξ hanf0
    refine ⟨ρ, mρ, hmρ, ?_, ⟨ρ0.toW, hQ0, hQ1⟩, hanf1⟩
    intro χ hχ
    subst hχ
    exact le_trans (hsz1 χ rfl) (hsz0 (⌊⌊rest⌋⌋χ) AnyFormula.loadBoxes_loaded_eq_loaded_boxes)

/-- Lemma 6.18, the loaded diamond existence lemma.
If the loaded diamond `~'⌊α⌋ξ` occurs in the pre-state `π`, then there is a pre-state `ρ`
with `Q α (Λ⁻ π) (Λ⁻ ρ)` that has `~''ξ`. Moreover, if `ξ` is still loaded then `ρ` is
reached without going up in the `BuildTree`.
Note that the claim is abbreviated by `LoadedExists bt α`.
The proof is by an outer induction on the length of `α` and an inner induction on the size
of the sub-`BuildTree` we are at. -/
lemma PreState.loadedExists {X} {bt : BuildTree [] X} (α : Program) : LoadedExists bt α := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IHn =>
  intro π mπ hmπ hn ξ hload
  by_cases hatom : α.isAtomic
  · -- Base case: the atomic modal step.
    obtain ⟨a, rfl⟩ := Program.isAtomic_iff.mp hatom
    obtain ⟨ρ, mρ, hmρ, hsz, hrel, hanf⟩ := π.atomicLoadedStep_wForms mπ hmπ hload
    refine ⟨ρ, mρ, hmρ, ?_, hrel, hanf⟩
    rintro χ rfl
    rcases hsz with h | ⟨φ, hφ⟩
    · exact le_of_lt h
    · exact absurd hφ (by simp)
  · -- Inductive step: unfold the diamond.
    obtain ⟨⟨F, δ⟩, hFδ, hF, hδ⟩ := PreState.loadUnfold_of_nonAtom hatom hload
    simp only at hF hδ
    rcases hδdef : δ with _ | ⟨γ0, rest⟩
    · -- No steps to make: stay where we are.
      subst hδdef
      refine ⟨π, mπ, hmπ, fun _ _ => le_refl _, ?_, by simpa using hδ⟩
      exact cpHelpA _ α (F, []) hFδ _ _
        (PreState.qcombo_of_qsteps hF (by simp only [Qsteps]; exact ReflBEq.rfl))
    · -- The first program in `δ` is atomic, we make a modal step with it.
      subst hδdef
      obtain ⟨a, rfl⟩ : ∃ a, γ0 = (·a : Program) := by
        rcases Dset_mem_sequence α hFδ with h | ⟨a, δ', h⟩
        · simp at h
        · exact ⟨a, by simp_all⟩
      rw [AnyFormula.loadBoxes_cons, PreState.hasAnf_loaded_iff] at hδ
      obtain ⟨ρ0, m0, hm0, hsz0, hQ0, hanf0⟩ := π.atomicLoadedStep_wForms mπ hmπ hδ
      by_cases hstar : α.isStar
      · -- `α = ∗β`: chain, then use the inner induction hypothesis for `α` again.
        obtain ⟨β, hβ⟩ : ∃ β, α = (∗β) := by cases α <;> simp_all [Program.isStar]
        obtain ⟨δ0, hδ0, hδ0ne, hδeq⟩ :
            ∃ δ0, (F, δ0) ∈ Dset β ∧ δ0 ≠ [] ∧ (·a : Program) :: rest = δ0 ++ [∗β] := by
          have hFδ : (F, (·a : Program) :: rest) ∈ Dset (∗β) := hβ ▸ hFδ
          simp only [Dset, List.empty_eq, List.cons_union, List.nil_union, List.mem_insert_iff,
            Prod.mk.injEq, List.mem_flatten, List.mem_map, Prod.exists] at hFδ
          rcases hFδ with ⟨_, hc⟩ | ⟨l, ⟨F', δ', hδ', rfl⟩, hl⟩
          · exact absurd hc (by simp)
          · by_cases h : δ' = [] <;> simp only [h, ↓reduceIte, List.not_mem_nil, List.mem_cons,
            Prod.mk.injEq, or_false] at hl
            obtain ⟨hF', hl2⟩ := hl
            subst hF'
            exact ⟨δ', hδ', h, hl2⟩
        obtain ⟨δ0', rfl⟩ : ∃ δ0', δ0 = (·a : Program) :: δ0' := by
          cases δ0 with
          | nil => exact absurd rfl hδ0ne
          | cons c cs => exact ⟨cs, by simp_all⟩
        have hrest : rest = δ0' ++ [∗β] := by simpa using hδeq
        subst hrest
        -- strict decrease at the atomic step, since the rest is still loaded
        have hstrict : m0.btAt.2.2.size < mπ.btAt.2.2.size := by
          rcases hsz0 with h | ⟨φ, hφ⟩
          · exact h
          · exact absurd hφ (AnyFormula.loadBoxes_ne_normal (by simp))
        -- chain over the middle part
        have hmid : ∀ γ ∈ δ0', LoadedExists bt γ := by
          intro γ hγ
          have hle : lengthOfProgram γ ≤ lengthOfProgram β := by
            have := Dset_goes_down_prog β hδ0 (List.mem_cons_of_mem _ hγ)
            by_cases hb : β.isAtomic
            · rw [ite_eq_left hb] at this; exact le_of_eq (by rw [this])
            · rw [ite_eq_right hb] at this
              by_cases hb2 : β.isStar
              · rw [ite_eq_left hb2] at this; exact this
              · rw [ite_eq_right hb2] at this; omega
          have hlt : lengthOfProgram γ < lengthOfProgram α := by
            rw [hβ]; simp only [lengthOfProgram]; omega
          exact PreState.loadedExists γ
        rw [AnyFormula.loadBoxes_append] at hanf0
        obtain ⟨ρ1, m1, hm1, hsz1, hQ1, hanf1⟩ := loadedChain δ0' hmid ρ0 m0 hm0 _ hanf0
        have hsz1' : m1.btAt.2.2.size ≤ m0.btAt.2.2.size := by
          refine hsz1 (⌊∗β⌋ξ) ?_
          simp [AnyFormula.loadBoxes]
        -- inner induction hypothesis
        obtain ⟨ρ, mρ, hmρ, hsz2, hQ2, hanf2⟩ :=
          IHn (m1.btAt.2.2.size) (by omega) ρ1 m1 hm1 (le_refl _) ξ
            (by
              have h := hanf1
              simp only [AnyFormula.loadBoxes_cons, AnyFormula.boxes_nil,
                PreState.hasAnf_loaded_iff] at h
              rw [hβ]
              exact h)
        refine ⟨ρ, mρ, hmρ, fun χ hχ => le_trans (hsz2 χ hχ) (by omega), ?_, hanf2⟩
        refine cpHelpA _ α (F, (·a : Program) :: (δ0' ++ [∗β])) hFδ _ _ ?_
        refine PreState.qcombo_of_qsteps hF ?_
        refine ⟨ρ0.toW, hQ0, ?_⟩
        rw [Qsteps_append]
        exact ⟨ρ1.toW, hQ1, by rw [Qsteps_single, ← hβ]; exact hQ2⟩
      · -- `α` is neither atomic nor a star: all programs in `δ` are shorter than `α`.
        have hmid : ∀ γ ∈ rest, LoadedExists bt γ := by
          intro γ hγ
          have hlt : lengthOfProgram γ < lengthOfProgram α := by
            have := Dset_goes_down_prog α hFδ (List.mem_cons_of_mem _ hγ)
            rw [ite_eq_right hatom, ite_eq_right hstar] at this
            exact this
          exact PreState.loadedExists γ
        obtain ⟨ρ, mρ, hmρ, hsz1, hQ1, hanf1⟩ := loadedChain rest hmid ρ0 m0 hm0 ξ hanf0
        refine ⟨ρ, mρ, hmρ, ?_, ?_, hanf1⟩
        · rintro χ rfl
          refine le_trans (hsz1 χ rfl) ?_
          rcases hsz0 with h | ⟨φ, hφ⟩
          · exact le_of_lt h
          · exfalso
            rw [AnyFormula.loadBoxes_loaded_eq_loaded_boxes] at hφ
            simp at hφ
        · refine cpHelpA _ α (F, (·a : Program) :: rest) hFδ _ _ ?_
          exact PreState.qcombo_of_qsteps hF ⟨ρ0.toW, hQ0, hQ1⟩
termination_by lengthOfProgram α

/-- If `~'⌊α⌋φ` occurs in the pre-state `π` then there is a pre-state `ρ` reached from `π` by
`Q α` that contains `~''φ`. This is a consequence of Lemma 6.18 `PreState.loadedExists`, but
omits the bound-related claims used for induction loading.
Again note that we use `Rel` from `BuildTree.toModel` as the `R` to use `Modelgraphs.Q`. -/
lemma PreState.loadedDiamondExistence {X} {bt : BuildTree [] X} {α : Program} {φ : AnyFormula}
    {π : PreState bt} (h : (~'⌊α⌋φ : WhateverFormula) ∈ π.wForms) :
    ∃ ρ : PreState bt,
      @Modelgraphs.Q bt.toModel.1 bt.toModel.2.Rel α π.toW ρ.toW ∧ ρ.hasAnf (~''φ) := by
  obtain ⟨mπ, hmπ⟩ := π.exists_match_endSeq_eq_last
  obtain ⟨ρ, _, _, _, hQ, hanf⟩ :=
    PreState.loadedExists α (mπ.btAt.2.2.size) π mπ hmπ (le_refl _) φ h
  exact ⟨ρ, hQ, hanf⟩

/-! ## The free diamond existence lemma (Lemma 6.19)

To load a free diamond `~⌈·a⌉χ` with the rule `(L+)` we first have to make the sequent free
using `(L-)`, and on the way we may have to go to the companion of a free repeat. -/

/-- A sequent with fewer formulas on the two sides is not closed either.
(This is a general statement about sequents and would fit well in `Pdl/Sequent.lean`.) -/
lemma Sequent.not_closed_of_sub {L R L' R' : Finset Formula} {O O' : Olf}
    (hL : ∀ f ∈ L', f ∈ L) (hR : ∀ f ∈ R', f ∈ R) (h : ¬ Sequent.closed ⟨L, R, O⟩) :
    ¬ Sequent.closed ⟨L', R', O'⟩ := by
  simp only [Sequent.closed, Sequent.mem_def, Sequent.L_eq, Sequent.R_eq] at h ⊢
  grind

/-- Applying the rule `(L-)` to free the loaded formula: all formulas we had are kept. -/
lemma PdlRule.exists_freeStep {Z : Sequent} (hZ : Z.O ≠ none) :
    ∃ Y : Sequent, Nonempty (PdlRule Z Y) ∧ Y.O = none
      ∧ (∀ f ∈ Z.toFinset, f ∈ Y.toFinset) := by
  rcases Z with ⟨L, R, O⟩
  rcases O with _ | (⟨⟨χ⟩⟩ | ⟨⟨χ⟩⟩)
  · exact absurd rfl hZ
  · obtain ⟨δ, α, φ, rfl⟩ := LoadFormula.exists_loadMulti χ
    refine ⟨⟨L ∪ {~⌈⌈δ⌉⌉⌈α⌉φ}, R, none⟩, ⟨PdlRule.freeL rfl rfl⟩, rfl, ?_⟩
    intro f hf
    simp only [Sequent.toFinset, unload_loadMulti, negUnload, Finset.mem_union,
      Option.mem_toFinset, Option.map_some, Option.mem_def, Option.some.injEq, Sum.elim_inl,
      Finset.mem_singleton] at hf ⊢
    tauto
  · obtain ⟨δ, α, φ, rfl⟩ := LoadFormula.exists_loadMulti χ
    refine ⟨⟨L, R ∪ {~⌈⌈δ⌉⌉⌈α⌉φ}, none⟩, ⟨PdlRule.freeR rfl rfl⟩, rfl, ?_⟩
    intro f hf
    simp only [Sequent.toFinset, unload_loadMulti, negUnload, Finset.mem_union,
      Option.mem_toFinset, Option.map_some, Option.mem_def, Option.some.injEq, Sum.elim_inr,
      Finset.mem_singleton] at hf ⊢
    tauto

/-- Applying the rule `(L+)` to load a free diamond `~⌈·a⌉χ` maximally, using `boxesOf`. -/
lemma PdlRule.exists_loadStep {L R : Finset Formula} {a : Nat} {χ : Formula}
    (bas : Sequent.basic ⟨L, R, none⟩) (hmem : (~⌈·a⌉χ) ∈ L ∪ R) :
    ∃ Y : Sequent, Nonempty (PdlRule ⟨L, R, none⟩ Y) ∧ Y.basic
      ∧ NegLoadFormula.memSequent Y
          (~'⌊·a⌋(AnyFormula.loadBoxes (boxesOf χ).1 (boxesOf χ).2))
      ∧ (∀ g, g ≠ (~⌈·a⌉χ) → g ∈ L ∪ R → g ∈ Y.L ∪ Y.R) := by
  set γs := (boxesOf χ).1 with hγs
  set ψ := (boxesOf χ).2 with hψ
  have hχ : χ = ⌈⌈γs⌉⌉ψ := def_of_boxesOf_def rfl
  have hne : ((·a : Program) :: γs) ≠ [] := by simp
  set δ := ((·a : Program) :: γs).dropLast with hδ
  set α := ((·a : Program) :: γs).getLast hne with hα
  have hsplit : δ ++ [α] = (·a : Program) :: γs := List.dropLast_append_getLast hne
  have hform : (~⌈⌈δ⌉⌉⌈α⌉ψ) = (~⌈·a⌉χ) := by
    rw [hχ]
    simp only [Formula.neg.injEq]
    rw [← boxes_last, hsplit, Formula.boxes_cons]
  have hload : AnyFormula.loaded (loadMulti δ α ψ)
      = AnyFormula.loaded (⌊·a⌋(AnyFormula.loadBoxes γs ψ)) := by
    rw [loadMulti_eq_loadBoxes, hsplit, AnyFormula.loadBoxes_cons]
  have hload' : (⌊⌊δ⌋⌋⌊α⌋ψ) = (⌊·a⌋(AnyFormula.loadBoxes γs ψ)) := by
    simpa using! hload
  have hnonBox : ¬ ψ.isBox := boxesOf_output_not_isBox
  have hbasic : ∀ f ∈ L ∪ R, f.basic := by
    intro f hf
    exact bas.1 f (by simp only [Sequent.toFinset, Option.map_none, Option.toFinset_none,
      Finset.union_empty]; exact hf)
  have hunload_basic : (~ (⌊⌊δ⌋⌋⌊α⌋ψ).unload).basic := by
    rw [hload', AnyFormulaBoxBoxes_eq_FormulaBoxLoadBoxes_inside_unload,
      AnyFormula.loadBoxes_unload_eq_boxes, ← hχ]
    exact hbasic _ hmem
  rcases Finset.mem_union.mp hmem with hin | hin
  · refine ⟨⟨L.erase (~⌈·a⌉χ), R, some (Sum.inl (~'(⌊⌊δ⌋⌋⌊α⌋ψ)))⟩,
      ⟨PdlRule.loadL (hform ▸ hin) hnonBox (by rw [hform]) ⟩, ?_, ?_, ?_⟩
    · constructor
      · intro f hf
        simp only [Sequent.toFinset, Finset.mem_union, Option.mem_toFinset, Option.map_some,
          Option.mem_def, Option.some.injEq, Sum.elim_inl, negUnload] at hf
        rcases hf with (hf | hf) | hf
        · exact hbasic f (by simp [Finset.mem_of_mem_erase hf])
        · exact hbasic f (by simp [hf])
        · subst hf
          exact hunload_basic
      · exact Sequent.not_closed_of_sub (fun f hf => Finset.mem_of_mem_erase hf)
          (fun f hf => hf) bas.2
    · simp [hload']
    · intro g hg hgin
      simp only [Sequent.L_eq, Sequent.R_eq, Finset.mem_union] at *
      rcases hgin with hgin | hgin
      · exact Or.inl (Finset.mem_erase.mpr ⟨hg, hgin⟩)
      · exact Or.inr hgin
  · refine ⟨⟨L, R.erase (~⌈·a⌉χ), some (Sum.inr (~'(⌊⌊δ⌋⌋⌊α⌋ψ)))⟩,
      ⟨PdlRule.loadR (hform ▸ hin) hnonBox (by rw [hform])⟩, ?_, ?_, ?_⟩
    · constructor
      · intro f hf
        simp only [Sequent.toFinset, Finset.mem_union, Option.mem_toFinset, Option.map_some,
          Option.mem_def, Option.some.injEq, Sum.elim_inr, negUnload] at hf
        rcases hf with (hf | hf) | hf
        · exact hbasic f (by simp [hf])
        · exact hbasic f (by simp [Finset.mem_of_mem_erase hf])
        · subst hf
          exact hunload_basic
      · exact Sequent.not_closed_of_sub (fun f hf => hf)
          (fun f hf => Finset.mem_of_mem_erase hf) bas.2
    · simp [hload']
    · intro g hg hgin
      simp only [Sequent.L_eq, Sequent.R_eq, Finset.mem_union] at *
      rcases hgin with hgin | hgin
      · exact Or.inl hgin
      · exact Or.inr (Finset.mem_erase.mpr ⟨hg, hgin⟩)

/-- Getting to a `Match` at a *free* and *basic* sequent that is not a free repeat, keeping
all basic formulas we had. Preparation for the `(L+)` rule in Lemma 6.19. -/
lemma Match.exists_free_basic {X} {bt : BuildTree [] X} (m : Match bt) (bas : m.endSeq.basic) :
    ∃ m' : Match bt, m'.endSeq.basic ∧ m'.endSeq.O = none
      ∧ ¬ m'.btAt.2.2.isFreeRepeat
      ∧ (∀ f, f.basic → f ∈ m.endSeq.toFinset → f ∈ m'.endSeq.toFinset) := by
  obtain ⟨m0, hset0, nfr0⟩ := m.exists_setEqTo_not_freeRepeat
  have bas0 : m0.endSeq.basic := by rw [hset0]; exact bas
  have hsub0 : ∀ f ∈ m.endSeq.toFinset, f ∈ m0.endSeq.toFinset := by
    intro f hf
    rw [hset0]
    exact hf
  by_cases hO : m0.endSeq.O = none
  · exact ⟨m0, bas0, hO, nfr0, fun f _ hf => hsub0 f hf⟩
  · obtain ⟨Y, ⟨r⟩, hYO, hYsub⟩ := PdlRule.exists_freeStep hO
    obtain ⟨m1, hm1eq, _⟩ := m0.exists_step bas0 nfr0 r
    obtain ⟨m2, hset2, nfr2⟩ := m1.exists_setEqTo_not_freeRepeat
    obtain ⟨ρ, hhead, m3, hm3⟩ := m2.exists_preState_head_of_not_freeRepeat nfr2
    have hsub2 : ∀ f ∈ m0.endSeq.toFinset, f ∈ m2.endSeq.toFinset := by
      intro f hf
      rw [hset2, hm1eq]
      exact hYsub f hf
    have h2free : m2.endSeq.O = none := by rw [hset2, hm1eq]; exact hYO
    have h3bas : m3.endSeq.basic := by rw [hm3]; exact PreState.forms_last_basic
    have h3free : m3.endSeq.O = none := by
      rw [hm3]
      exact ρ.O_getLast_eq_none (by rw [hhead]; exact h2free)
    have h3keep : ∀ f, f.basic → f ∈ m2.endSeq.toFinset → f ∈ m3.endSeq.toFinset := by
      intro f hfb hf
      rw [hm3]
      refine PreState.mem_bothSides_getLast_of_basic hfb ?_
      refine PreState.mem_forms_of_mem (Z := m2.endSeq) ?_ hf
      rw [← hhead]
      exact List.head_mem _
    obtain ⟨m4, hset4, nfr4⟩ := m3.exists_setEqTo_not_freeRepeat
    refine ⟨m4, by rw [hset4]; exact h3bas, ?_, nfr4, ?_⟩
    · rw [hset4]; exact h3free
    · intro f hfb hf
      rw [hset4]
      exact h3keep f hfb (hsub2 f (hsub0 f hf))

/-- The modal step at the end of a `Match`, landing in a pre-state:
if we are at a basic sequent loaded with `~'⌊·a⌋ξ` then there is a pre-state that has `~''ξ`
and all `a`-successors of the boxes we had. -/
lemma Match.modalStepToPreState {X} {bt : BuildTree [] X} (m : Match bt) (bas : m.endSeq.basic)
    {a : Nat} {ξ : AnyFormula} (hload : NegLoadFormula.memSequent m.endSeq (~'⌊·a⌋ξ)) :
    ∃ ρ : PreState bt, ρ.hasAnf (~''ξ)
      ∧ ∀ f, (⌈·a⌉f) ∈ m.endSeq.L ∪ m.endSeq.R → f ∈ ρ.forms := by
  obtain ⟨m', _, hanf, hproj, _⟩ := m.atomicLoadedStep bas hload
  obtain ⟨ρ, Z, hZmem, hZset, _⟩ := m'.exists_preState_setEqTo
  refine ⟨ρ, ⟨Z, hZmem, by rw [hZset]; exact hanf⟩, ?_⟩
  intro f hf
  refine PreState.mem_forms_of_mem hZmem ?_
  rw [hZset]
  exact hproj f hf

/-- Lemma 6.19: If a free diamond `~⌈·a⌉χ` with an atomic program occurs in the pre-state
`π`, then there is an `a`-successor pre-state `ρ` of `π` that has `~''χ`, maximally loaded. -/
lemma PreState.freeAtomicStep {X} {bt : BuildTree [] X} (π : PreState bt) {a : Nat} {χ : Formula}
    (h : (~⌈·a⌉χ : WhateverFormula) ∈ π.wForms) :
    ∃ ρ : PreState bt, bt.toModel.2.Rel a π.toW ρ.toW
      ∧ ρ.hasAnf (~''(AnyFormula.loadBoxes (boxesOf χ).1 (boxesOf χ).2)) := by
  obtain ⟨mπ, hmπ⟩ := π.exists_match_endSeq_eq_last
  have bas : mπ.endSeq.basic := by rw [hmπ]; exact PreState.forms_last_basic
  have hkeepπ : ∀ f : Formula, f.basic → f ∈ π.forms → f ∈ mπ.endSeq.toFinset := by
    intro f hfb hf
    rw [hmπ]
    exact PreState.mem_bothSides_getLast_of_basic hfb hf
  obtain ⟨m1, bas1, hfree1, nfr1, hkeep1⟩ := mπ.exists_free_basic bas
  have hLR : ∀ f, f ∈ m1.endSeq.toFinset → f ∈ m1.endSeq.L ∪ m1.endSeq.R := by
    intro f hf
    rcases hE : m1.endSeq with ⟨L, R, O⟩
    rw [hE] at hf hfree1
    simp only [Sequent.O_eq] at hfree1
    subst hfree1
    simpa [Sequent.toFinset] using hf
  have hdiaπ : (~⌈·a⌉χ) ∈ π.forms := PreState.mem_forms_of_mem_wForms h
  have hdia : (~⌈·a⌉χ) ∈ m1.endSeq.L ∪ m1.endSeq.R :=
    hLR _ (hkeep1 _ (by simp [Formula.basic]) (hkeepπ _ (by simp [Formula.basic]) hdiaπ))
  obtain ⟨Y, ⟨r⟩, basY, hloadY, hboxY⟩ : ∃ Y : Sequent, Nonempty (PdlRule m1.endSeq Y) ∧ Y.basic
      ∧ NegLoadFormula.memSequent Y
          (~'⌊·a⌋(AnyFormula.loadBoxes (boxesOf χ).1 (boxesOf χ).2))
      ∧ (∀ g, g ≠ (~⌈·a⌉χ) → g ∈ m1.endSeq.L ∪ m1.endSeq.R → g ∈ Y.L ∪ Y.R) := by
    rcases hE : m1.endSeq with ⟨L, R, O⟩
    rw [hE] at bas1 hfree1 hdia
    simp only [Sequent.O_eq] at hfree1
    subst hfree1
    simp only [Sequent.L_eq, Sequent.R_eq] at hdia ⊢
    exact PdlRule.exists_loadStep bas1 hdia
  obtain ⟨m2, hm2eq, _⟩ := m1.exists_step bas1 nfr1 r
  obtain ⟨ρ, hanf, hproj⟩ :=
    m2.modalStepToPreState (by rw [hm2eq]; exact basY) (by rw [hm2eq]; exact hloadY)
  refine ⟨ρ, ⟨χ, hdiaπ, ?_⟩, hanf⟩
  intro f hf
  simp only [PreState.toW_val, Finset.mem_union, Finset.mem_singleton] at hf
  rcases hf with hf | rfl
  · have hboxπ : (⌈·a⌉f) ∈ π.forms := Finset.mem_projection.mp hf
    have hbox1 : (⌈·a⌉f) ∈ m1.endSeq.L ∪ m1.endSeq.R :=
      hLR _ (hkeep1 _ (by simp [Formula.basic]) (hkeepπ _ (by simp [Formula.basic]) hboxπ))
    exact hproj f (by rw [hm2eq]; exact hboxY _ (by simp) hbox1)
  · have hunl := PreState.mem_forms_of_hasAnf hanf
    rwa [AnyFormula.loadBoxes_unload_eq_boxes, ← def_of_boxesOf_def (φ := χ) rfl] at hunl

/-! ## The free diamond existence lemma (Lemma 6.20) -/

/-- Iterating Lemma 6.18 along a list of programs, formulated with `Qsteps`.
From a pre-state that has `~''(loadBoxes γs ξ)` we reach one that has `~''ξ`. -/
lemma PreState.chainFromLoadBoxes {X} {bt : BuildTree [] X} (γs : List Program) (ξ : AnyFormula)
    (π : PreState bt) (h : π.hasAnf (~''(AnyFormula.loadBoxes γs ξ))) :
    ∃ ρ : PreState bt, Qsteps bt.toModel.2.Rel γs π.toW ρ.toW ∧ ρ.hasAnf (~''ξ) := by
  obtain ⟨mπ, hmπ⟩ := π.exists_match_endSeq_eq_last
  obtain ⟨ρ, _, _, _, hQ, hanf⟩ :=
    loadedChain γs (fun γ _ => PreState.loadedExists γ) π mπ hmπ ξ h
  exact ⟨ρ, hQ, hanf⟩

/-- Combining Lemma 6.19 with Lemma 6.18: if the free diamond `~⌈·a⌉⌈⌈γs⌉⌉φ` is in the
pre-state `π`, then we can make the `·a` step and then follow `γs` to reach a pre-state
containing `~φ`. -/
lemma PreState.freeAtomicChain {X} {bt : BuildTree [] X} {π : PreState bt} {a : Nat}
    {γs : List Program} {φ : Formula}
    (h : (~⌈·a⌉(⌈⌈γs⌉⌉φ) : WhateverFormula) ∈ π.wForms) :
    ∃ ρ : PreState bt, Qsteps bt.toModel.2.Rel ((·a : Program) :: γs) π.toW ρ.toW
      ∧ (~φ) ∈ ρ.forms := by
  obtain ⟨ρ0, hrel, hanf0⟩ := π.freeAtomicStep h
  have hbo : boxesOf (⌈⌈γs⌉⌉φ) = (γs ++ (boxesOf φ).1, (boxesOf φ).2) := by
    refine boxesOf_def_of_def_of_nonBox ?_ boxesOf_output_not_isBox
    rw [boxes_append]
    congr 1
    exact def_of_boxesOf_def rfl
  rw [hbo] at hanf0
  simp only [AnyFormula.loadBoxes_append] at hanf0
  obtain ⟨ρ, hQ, hanf⟩ := PreState.chainFromLoadBoxes γs _ ρ0 hanf0
  refine ⟨ρ, ⟨ρ0.toW, hrel, hQ⟩, ?_⟩
  have hunl := PreState.mem_forms_of_hasAnf hanf
  rwa [AnyFormula.loadBoxes_unload_eq_boxes, ← def_of_boxesOf_def (φ := φ) rfl] at hunl

/-- The claim used to prove Lemma 6.20: if the free diamond `~⌈α⌉φ` occurs in the
pre-state `π`, then there is a pre-state `ρ` with `Q α (Λ⁻ π) (Λ⁻ ρ)` that contains `~φ`. -/
lemma PreState.freeExists {X} {bt : BuildTree [] X} (α : Program) {φ : Formula}
    {π : PreState bt} (h : (~⌈α⌉φ : WhateverFormula) ∈ π.wForms) :
    ∃ ρ : PreState bt,
      @Modelgraphs.Q bt.toModel.1 bt.toModel.2.Rel α π.toW ρ.toW ∧ (~φ) ∈ ρ.forms := by
  by_cases hatom : α.isAtomic
  · -- Atomic case, this is Lemma 6.19.
    obtain ⟨a, rfl⟩ := Program.isAtomic_iff.mp hatom
    obtain ⟨ρ, hQ, hmem⟩ := PreState.freeAtomicChain (γs := []) (by simpa using h)
    exact ⟨ρ, Qsteps_single.mp hQ, hmem⟩
  · -- Non-atomic case: unfold the diamond and then use Lemma 6.19 and Lemma 6.18.
    obtain ⟨⟨F, δ⟩, hFδ, hall⟩ := PreState.freeUnfoldDiaMem_of_nonAtom hatom h
    simp only [List.all_eq_true, decide_eq_true_eq] at hall
    have hF : ∀ f ∈ F, (f : WhateverFormula) ∈ π.wForms := fun f hf =>
      hall f (by simp [hf])
    have hbox : (~(Formula.boxes δ φ) : WhateverFormula) ∈ π.wForms :=
      hall _ (by simp)
    rcases Dset_mem_sequence α hFδ with rfl | ⟨a, γs, rfl⟩
    · -- No steps to make: stay where we are.
      refine ⟨π, cpHelpA _ α (F, []) hFδ _ _
        (PreState.qcombo_of_qsteps hF (by simp only [Qsteps]; exact ReflBEq.rfl)), ?_⟩
      exact PreState.mem_forms_of_mem_wForms (by simpa using hbox)
    · obtain ⟨ρ, hQ, hmem⟩ := PreState.freeAtomicChain (by simpa using hbox)
      exact ⟨ρ, cpHelpA _ α (F, (·a : Program) :: γs) hFδ _ _
        (PreState.qcombo_of_qsteps hF hQ), hmem⟩

/-- Induction loading for 6.20.
(Note that `ψ` may even be boxed here, because `PreState.freeExists` holds for all formulas.) -/
lemma freeDiamondExistenceInduction {X} {bt : BuildTree [] X}
    {ψ : Formula}
    {α} {ηs : List Program} {π : PreState bt} :
    (~⌈α⌉⌈⌈ηs⌉⌉ψ : WhateverFormula) ∈ π.wForms →
      ∃ π' : PreState bt,
        (~⌈⌈ηs⌉⌉ψ) ∈ π'.forms -- NOTE: may occur loaded or unloaded in Λ(π')
        ∧ @Modelgraphs.Q bt.toModel.1 bt.toModel.2.Rel α π π' := by
  intro in_forms
  obtain ⟨π', hQ, hmem⟩ := PreState.freeExists α in_forms
  exact ⟨π', hmem, hQ⟩

/-- Lemma 6.20: free diamond existence lemma for pre-states -/
lemma freeDiamondExistence {X} {bt : BuildTree [] X} {α} {φ : Formula} {π : PreState bt} :
  (~⌈α⌉φ : WhateverFormula) ∈ π.wForms → ∃ π' : PreState bt,
      ~φ ∈ π'.forms ∧ @Modelgraphs.Q bt.toModel.1 bt.toModel.2.Rel α π π' := by
  intro in_forms
  let ηs_ψ := boxesOf φ
  have := @freeDiamondExistenceInduction X bt ηs_ψ.2 α ηs_ψ.1 π ?in_forms
  case in_forms =>
    convert in_forms
    exact Eq.symm (def_of_boxesOf_def rfl)
  rcases this with ⟨π', in_π'_forms, α_rel⟩
  refine ⟨π', ?_, α_rel⟩
  · convert in_π'_forms
    exact def_of_boxesOf_def rfl

end PDL
