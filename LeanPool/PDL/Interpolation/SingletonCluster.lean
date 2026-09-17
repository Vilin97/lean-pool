/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

import LeanPool.PDL.Tableau
import LeanPool.PDL.Interpolation.Local

/-! ## Helper lemmas about vocabularies and interpolants -/

namespace PDL

open HasSat in
/-- Being an interpolant only depends on which formulas are in the two components. -/
lemma isPartInterpolant_of_mem_iff {Z Y : Sequent} {θ : Formula}
    (hl : ∀ f, f ∈ Z.left ↔ f ∈ Y.left) (hr : ∀ f, f ∈ Z.right ↔ f ∈ Y.right)
    (h : isPartInterpolant Y θ) : isPartInterpolant Z θ := by
  obtain ⟨hvoc, hL, hR⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have x_in := hvoc hx
    simp only [jvoc, Finset.mem_inter] at x_in ⊢
    have := fvoc_subset_of_mem_voc (fun f hf => ⟨f, (hl f).mpr hf, subset_rfl⟩) x_in.1
    have := fvoc_subset_of_mem_voc (fun f hf => ⟨f, (hr f).mpr hf, subset_rfl⟩) x_in.2
    grind
  · rw [Finset.ext hl]; exact hL
  · rw [Finset.ext hr]; exact hR

/-! ## Interpolants for PdlRules applied to free nodes

The only rule treated here is (L+), i.e. `loadL` and `loadR`.
-/

/-- Propagate a partial interpolant backwards through a PDL rule with a free source. -/
def freePdlRuleInterpolant {X Y} (r : PdlRule X Y) (Xfree : X.isFree) (θY : PartInterpolant Y)
    : PartInterpolant X := by
  rcases θY with ⟨θ, θ_ip_Y⟩
  cases r
  case loadL in_L notBox Y_def =>
    subst Y_def
    refine ⟨θ, isPartInterpolant_of_mem_iff ?_ ?_ θ_ip_Y⟩
    · intro f
      simp only [Sequent.left_eq, Olf.L_none, Finset.union_empty, Olf.L_inl, unload_boxes,
        LoadFormula.unload, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, ne_eq]
      grind
    · intro f
      simp only [Sequent.right_eq, Olf.R_none, Olf.R_inl, Finset.union_empty]
  case loadR in_R notBox Y_def =>
    subst Y_def
    refine ⟨θ, isPartInterpolant_of_mem_iff ?_ ?_ θ_ip_Y⟩
    · intro f
      simp only [Sequent.left_eq, Olf.L_none, Olf.L_inr, Finset.union_empty]
    · intro f
      simp only [Sequent.right_eq, Olf.R_none, Finset.union_empty, Olf.R_inr, unload_boxes,
        LoadFormula.unload, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, ne_eq]
      grind
  all_goals
    exfalso
    subst_eqs
    simp_all [Sequent.isFree, Sequent.isLoaded]


/-! ## Interpolants for PdlRules applied to loaded nodes

The rules treated here are (L-), i.e. `freeL` and `freeR`, and the modal rule (M), i.e.
`modL` and `modR`. This is the part of Lemma 9.1 in the paper that is about loaded nodes
which form a singleton cluster. -/


-- Reason: the many `simp` calls about `Finset` membership below are slow.
open HasSat in
/-- Interpolant for the modal rule (M) applied to a node loaded on the left.
The lists `Xl, Xr` are the two components of the premise and `Yl, Yr` those of the
conclusion, described by which formulas are in them.
The interpolant is `~⌈·A⌉(~θ)`, unless the projection of the right component is empty,
in which case the left component is unsatisfiable and we can use `⊥`. -/
lemma exists_itp_modL {A : Nat} {L R Xl Xr Yl Yr : Finset Formula} {ψ θ : Formula}
    (hXl : ∀ f, f ∈ Xl ↔ f ∈ L ∨ f = ~⌈·A⌉ψ)
    (hXr : ∀ f, f ∈ Xr ↔ f ∈ R)
    (hYl : ∀ f, f ∈ Yl ↔ f = ~ψ ∨ f ∈ L.pdlProjection A)
    (hYr : ∀ f, f ∈ Yr ↔ f ∈ R.pdlProjection A)
    (hvoc : θ.voc ⊆ Yl.pdlFvoc ∩ Yr.pdlFvoc)
    (hL : ¬ satisfiable ({~θ} ∪ Yl))
    (hR : ¬ satisfiable ({θ} ∪ Yr)) :
    ∃ ρ, ρ.voc ⊆ Xl.pdlFvoc ∩ Xr.pdlFvoc
       ∧ ¬ satisfiable ({~ρ} ∪ Xl) ∧ ¬ satisfiable ({ρ} ∪ Xr) := by
  -- Any state satisfying `Xl` has an `A`-successor satisfying `Yl`.
  have exists_succ : ∀ (W : Type) (M : KripkeModel W) (w : W), (∀ f ∈ Xl, evaluate M w f) →
      ∃ v, M.Rel A w v ∧ ∀ f ∈ Yl, evaluate M v f := by
    intro W M w hw
    have h1 : evaluate M w (~⌈·A⌉ψ) := hw _ ((hXl _).mpr (Or.inr rfl))
    simp only [evaluate, relate, not_forall] at h1
    obtain ⟨v, hv, hvψ⟩ := h1
    refine ⟨v, hv, ?_⟩
    intro f hf
    rcases (hYl f).mp hf with rfl | hf
    · simpa using hvψ
    · have := hw (⌈·A⌉f) ((hXl _).mpr (Or.inl (Finset.mem_projection.mp hf)))
      simp only [evaluate, relate] at this
      exact this v hv
  -- Successors of states satisfying `Xr` satisfy `Yr`.
  have succ_Yr : ∀ (W : Type) (M : KripkeModel W) (w v : W), (∀ f ∈ Xr, evaluate M w f) →
      M.Rel A w v → ∀ f ∈ Yr, evaluate M v f := by
    intro W M w v hw hwv f hf
    have := hw (⌈·A⌉f) ((hXr _).mpr (Finset.mem_projection.mp ((hYr f).mp hf)))
    simp only [evaluate, relate] at this
    exact this v hwv
  by_cases hemp : ∃ χ, χ ∈ R.pdlProjection A
  · -- The projection of the right component is non-empty, so `A` is in the joint vocabulary.
    obtain ⟨χ, hχ⟩ := hemp
    refine ⟨~⌈·A⌉(~θ), ?_, ?_, ?_⟩
    · have hYlXl : Yl.pdlFvoc ⊆ Xl.pdlFvoc := by
        apply fvoc_subset_of_mem_voc
        intro f hf
        rcases (hYl f).mp hf with rfl | hf
        · exact ⟨_, (hXl _).mpr (Or.inr rfl), by simp⟩
        · exact ⟨⌈·A⌉f, (hXl _).mpr (Or.inl (Finset.mem_projection.mp hf)), by simp⟩
      have hYrXr : Yr.pdlFvoc ⊆ Xr.pdlFvoc := by
        apply fvoc_subset_of_mem_voc
        intro f hf
        exact ⟨⌈·A⌉f, (hXr _).mpr (Finset.mem_projection.mp ((hYr f).mp hf)), by simp⟩
      have hA_l : (Sum.inr A : Sum Nat Nat) ∈ Xl.pdlFvoc :=
        Finset.mem_fvoc.mpr ⟨_, (hXl _).mpr (Or.inr rfl), by simp⟩
      have hA_r : (Sum.inr A : Sum Nat Nat) ∈ Xr.pdlFvoc :=
        Finset.mem_fvoc.mpr
          ⟨⌈·A⌉χ, (hXr _).mpr (Finset.mem_projection.mp hχ), by simp⟩
      intro x hx
      simp only [Formula.voc, Program.voc, Finset.mem_union, Finset.mem_singleton] at hx
      rcases hx with rfl | hx
      · exact Finset.mem_inter.mpr ⟨hA_l, hA_r⟩
      · have := hvoc hx
        rw [Finset.mem_inter] at this ⊢
        exact ⟨hYlXl this.1, hYrXr this.2⟩
    · rintro ⟨W, M, w, hw⟩
      have hXlw : ∀ f ∈ Xl, evaluate M w f := fun f hf => hw f (by simp_all)
      obtain ⟨v, hv, hvYl⟩ := exists_succ W M w hXlw
      have h1 : evaluate M w (~~⌈·A⌉(~θ)) := hw _ (by simp_all)
      simp only [evaluate, relate, not_not] at h1
      refine hL ⟨W, M, v, ?_⟩
      intro f hf
      simp only [Finset.singleton_union, Finset.mem_insert] at hf
      rcases hf with rfl | hf
      · exact h1 v hv
      · exact hvYl f hf
    · rintro ⟨W, M, w, hw⟩
      have hXrw : ∀ f ∈ Xr, evaluate M w f := fun f hf => hw f (by simp; tauto)
      have h1 : evaluate M w (~⌈·A⌉(~θ)) := hw _ (by simp)
      simp only [evaluate, relate, not_forall, not_not] at h1
      obtain ⟨v, hv, hvθ⟩ := h1
      refine hR ⟨W, M, v, ?_⟩
      intro f hf
      simp only [Finset.singleton_union, Finset.mem_insert] at hf
      rcases hf with rfl | hf
      · exact hvθ
      · exact succ_Yr W M w v hXrw hv f hf
  · -- The projection of the right component is empty, hence `Xl` is unsatisfiable.
    push Not at hemp
    have θ_unsat : ∀ (W : Type) (M : KripkeModel W) (w : W), ¬ evaluate M w θ := by
      intro W M w hw
      refine hR ⟨W, M, w, ?_⟩
      intro f hf
      simp only [Finset.singleton_union, Finset.mem_insert] at hf
      rcases hf with rfl | hf
      · exact hw
      · exact absurd ((hYr f).mp hf) (hemp f)
    have Xl_unsat : ¬ satisfiable Xl := by
      rintro ⟨W, M, w, hw⟩
      obtain ⟨v, -, hvYl⟩ := exists_succ W M w hw
      refine hL ⟨W, M, v, ?_⟩
      intro f hf
      simp only [Finset.singleton_union, Finset.mem_insert] at hf
      rcases hf with rfl | hf
      · exact θ_unsat W M v
      · exact hvYl f hf
    refine ⟨⊥, by simp, ?_, ?_⟩
    · rintro ⟨W, M, w, hw⟩
      exact Xl_unsat ⟨W, M, w, fun f hf => hw f (by simp_all)⟩
    · rintro ⟨W, M, w, hw⟩
      simp_all

-- Reason: the many `simp` calls about `Finset` membership below are slow.
open HasSat in
/-- Interpolant for the modal rule (M) applied to a node loaded on the right.
The interpolant is `⌈·A⌉θ`, unless the projection of the left component is empty,
in which case the right component is unsatisfiable and we can use `~⊥`. -/
lemma exists_itp_modR {A : Nat} {L R Xl Xr Yl Yr : Finset Formula} {ψ θ : Formula}
    (hXl : ∀ f, f ∈ Xl ↔ f ∈ L)
    (hXr : ∀ f, f ∈ Xr ↔ f ∈ R ∨ f = ~⌈·A⌉ψ)
    (hYl : ∀ f, f ∈ Yl ↔ f ∈ L.pdlProjection A)
    (hYr : ∀ f, f ∈ Yr ↔ f = ~ψ ∨ f ∈ R.pdlProjection A)
    (hvoc : θ.voc ⊆ Yl.pdlFvoc ∩ Yr.pdlFvoc)
    (hL : ¬ satisfiable ({~θ} ∪ Yl))
    (hR : ¬ satisfiable ({θ} ∪ Yr)) :
    ∃ ρ, ρ.voc ⊆ Xl.pdlFvoc ∩ Xr.pdlFvoc
       ∧ ¬ satisfiable ({~ρ} ∪ Xl) ∧ ¬ satisfiable ({ρ} ∪ Xr) := by
  -- Any state satisfying `Xr` has an `A`-successor satisfying `Yr`.
  have exists_succ : ∀ (W : Type) (M : KripkeModel W) (w : W), (∀ f ∈ Xr, evaluate M w f) →
      ∃ v, M.Rel A w v ∧ ∀ f ∈ Yr, evaluate M v f := by
    intro W M w hw
    have h1 : evaluate M w (~⌈·A⌉ψ) := hw _ ((hXr _).mpr (Or.inr rfl))
    simp only [evaluate, relate, not_forall] at h1
    obtain ⟨v, hv, hvψ⟩ := h1
    refine ⟨v, hv, ?_⟩
    intro f hf
    rcases (hYr f).mp hf with rfl | hf
    · simpa using hvψ
    · have := hw (⌈·A⌉f) ((hXr _).mpr (Or.inl (Finset.mem_projection.mp hf)))
      simp only [evaluate, relate] at this
      exact this v hv
  -- Successors of states satisfying `Xl` satisfy `Yl`.
  have succ_Yl : ∀ (W : Type) (M : KripkeModel W) (w v : W), (∀ f ∈ Xl, evaluate M w f) →
      M.Rel A w v → ∀ f ∈ Yl, evaluate M v f := by
    intro W M w v hw hwv f hf
    have := hw (⌈·A⌉f) ((hXl _).mpr (Finset.mem_projection.mp ((hYl f).mp hf)))
    simp only [evaluate, relate] at this
    exact this v hwv
  by_cases hemp : ∃ χ, χ ∈ L.pdlProjection A
  · -- The projection of the left component is non-empty, so `A` is in the joint vocabulary.
    obtain ⟨χ, hχ⟩ := hemp
    refine ⟨⌈·A⌉θ, ?_, ?_, ?_⟩
    · have hYlXl : Yl.pdlFvoc ⊆ Xl.pdlFvoc := by
        apply fvoc_subset_of_mem_voc
        intro f hf
        exact ⟨⌈·A⌉f, (hXl _).mpr (Finset.mem_projection.mp ((hYl f).mp hf)), by simp⟩
      have hYrXr : Yr.pdlFvoc ⊆ Xr.pdlFvoc := by
        apply fvoc_subset_of_mem_voc
        intro f hf
        rcases (hYr f).mp hf with rfl | hf
        · exact ⟨_, (hXr _).mpr (Or.inr rfl), by simp⟩
        · exact ⟨⌈·A⌉f, (hXr _).mpr (Or.inl (Finset.mem_projection.mp hf)), by simp⟩
      have hA_l : (Sum.inr A : Sum Nat Nat) ∈ Xl.pdlFvoc :=
        Finset.mem_fvoc.mpr
          ⟨⌈·A⌉χ, (hXl _).mpr (Finset.mem_projection.mp hχ), by simp⟩
      have hA_r : (Sum.inr A : Sum Nat Nat) ∈ Xr.pdlFvoc :=
        Finset.mem_fvoc.mpr ⟨_, (hXr _).mpr (Or.inr rfl), by simp⟩
      intro x hx
      simp only [Formula.voc, Program.voc, Finset.mem_union, Finset.mem_singleton] at hx
      rcases hx with rfl | hx
      · exact Finset.mem_inter.mpr ⟨hA_l, hA_r⟩
      · have := hvoc hx
        rw [Finset.mem_inter] at this ⊢
        exact ⟨hYlXl this.1, hYrXr this.2⟩
    · rintro ⟨W, M, w, hw⟩
      have hXlw : ∀ f ∈ Xl, evaluate M w f := fun f hf => hw f (by simp_all)
      have h1 : evaluate M w (~⌈·A⌉θ) := hw _ (by simp_all)
      simp only [evaluate, relate, not_forall] at h1
      obtain ⟨v, hv, hvθ⟩ := h1
      refine hL ⟨W, M, v, ?_⟩
      intro f hf
      simp only [Finset.singleton_union, Finset.mem_insert] at hf
      rcases hf with rfl | hf
      · simpa using hvθ
      · exact succ_Yl W M w v hXlw hv f hf
    · rintro ⟨W, M, w, hw⟩
      have hXrw : ∀ f ∈ Xr, evaluate M w f := fun f hf => hw f (by simp_all)
      obtain ⟨v, hv, hvYr⟩ := exists_succ W M w hXrw
      have h1 : evaluate M w (⌈·A⌉θ) := hw _ (by simp_all)
      simp only [evaluate, relate] at h1
      refine hR ⟨W, M, v, ?_⟩
      intro f hf
      simp only [Finset.singleton_union, Finset.mem_insert] at hf
      rcases hf with rfl | hf
      · exact h1 v hv
      · exact hvYr f hf
  · -- The projection of the left component is empty, hence `Xr` is unsatisfiable.
    push Not at hemp
    have θ_valid : ∀ (W : Type) (M : KripkeModel W) (w : W), evaluate M w θ := by
      intro W M w
      by_contra hw
      refine hL ⟨W, M, w, ?_⟩
      intro f hf
      simp only [Finset.singleton_union, Finset.mem_insert] at hf
      rcases hf with rfl | hf
      · simpa using hw
      · exact absurd ((hYl f).mp hf) (hemp f)
    have Xr_unsat : ¬ satisfiable Xr := by
      rintro ⟨W, M, w, hw⟩
      obtain ⟨v, -, hvYr⟩ := exists_succ W M w hw
      refine hR ⟨W, M, v, ?_⟩
      intro f hf
      simp only [Finset.singleton_union, Finset.mem_insert] at hf
      rcases hf with rfl | hf
      · exact θ_valid W M v
      · exact hvYr f hf
    refine ⟨~⊥, by simp, ?_, ?_⟩
    · rintro ⟨W, M, w, hw⟩
      simpa using hw (~~⊥) (by simp_all)
    · rintro ⟨W, M, w, hw⟩
      exact Xr_unsat ⟨W, M, w, fun f hf => hw f (by simp_all)⟩

/-- Given an interpolant for the conclusion of a `PdlRule` applied to a *loaded* sequent,
we get an interpolant for the premise. This is the loaded analogue of
`freePdlRuleInterpolant`, covering the rules (L-) and (M). -/
lemma loadedPdlRuleInterpolant {Z Y : Sequent} (r : PdlRule Z Y) (Zloaded : Z.isLoaded)
    (h : ∃ θ, isPartInterpolant Y θ) : ∃ ρ, isPartInterpolant Z ρ := by
  obtain ⟨θ, hvoc, hL, hR⟩ := h
  cases r
  case loadL L δ α φ R in_L notBox Y_def => exact absurd Zloaded (by simp [Sequent.isLoaded])
  case loadR L δ α φ R in_R notBox Y_def => exact absurd Zloaded (by simp [Sequent.isLoaded])
  case freeL L R δ α φ hX hY =>
    subst hX; subst hY
    refine ⟨θ, isPartInterpolant_of_mem_iff ?_ ?_ ⟨hvoc, hL, hR⟩⟩
    · intro f; simp [Sequent.left, Sequent.L, Sequent.O, Olf.L, unload_boxes,
        LoadFormula.unload]
    · intro f; simp [Sequent.right, Sequent.R, Sequent.O, Olf.R]
  case freeR L R δ α φ hX hY =>
    subst hX; subst hY
    refine ⟨θ, isPartInterpolant_of_mem_iff ?_ ?_ ⟨hvoc, hL, hR⟩⟩
    · intro f; simp [Sequent.left, Sequent.L, Sequent.O, Olf.L]
    · intro f; simp [Sequent.right, Sequent.R, Sequent.O, Olf.R, unload_boxes,
        LoadFormula.unload]
  case modL L R A ξ hX hY =>
    subst hX
    cases ξ
    case normal φ =>
      subst hY
      refine exists_itp_modL (A := A) (L := L) (R := R) (ψ := φ) (θ := θ) ?_ ?_ ?_ ?_ hvoc hL hR
      · intro f; simp [Sequent.left, Sequent.L, Sequent.O, Olf.L, LoadFormula.unload]; tauto
      · intro f; simp [Sequent.right, Sequent.R, Sequent.O, Olf.R]
      · intro f; simp [Sequent.left, Sequent.L, Sequent.O, Olf.L]
      · intro f; simp [Sequent.right, Sequent.R, Sequent.O, Olf.R]
    case loaded χ =>
      subst hY
      refine exists_itp_modL (A := A) (L := L) (R := R) (ψ := χ.unload) (θ := θ)
        ?_ ?_ ?_ ?_ hvoc hL hR
      · intro f; simp [Sequent.left, Sequent.L, Sequent.O, Olf.L, LoadFormula.unload]; tauto
      · intro f; simp [Sequent.right, Sequent.R, Sequent.O, Olf.R]
      · intro f; simp [Sequent.left, Sequent.L, Sequent.O, Olf.L]
      · intro f; simp [Sequent.right, Sequent.R, Sequent.O, Olf.R]
  case modR L R A ξ hX hY =>
    subst hX
    cases ξ
    case normal φ =>
      subst hY
      refine exists_itp_modR (A := A) (L := L) (R := R) (ψ := φ) (θ := θ) ?_ ?_ ?_ ?_ hvoc hL hR
      · intro f; simp [Sequent.left, Sequent.L, Sequent.O, Olf.L]
      · intro f; simp [Sequent.right, Sequent.R, Sequent.O, Olf.R, LoadFormula.unload]; tauto
      · intro f; simp [Sequent.left, Sequent.L, Sequent.O, Olf.L]
      · intro f; simp [Sequent.right, Sequent.R, Sequent.O, Olf.R]
    case loaded χ =>
      subst hY
      refine exists_itp_modR (A := A) (L := L) (R := R) (ψ := χ.unload) (θ := θ)
        ?_ ?_ ?_ ?_ hvoc hL hR
      · intro f; simp [Sequent.left, Sequent.L, Sequent.O, Olf.L]
      · intro f; simp [Sequent.right, Sequent.R, Sequent.O, Olf.R, LoadFormula.unload]; tauto
      · intro f; simp [Sequent.left, Sequent.L, Sequent.O, Olf.L]
      · intro f; simp [Sequent.right, Sequent.R, Sequent.O, Olf.R]

end PDL
