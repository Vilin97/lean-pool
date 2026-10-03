/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import LeanPool.PDL.Soundness
public import LeanPool.PDL.Completeness.BuildTreeExistence

/-! # Completeness Proof (Section 6.4) -/

public section

namespace PDL

open Lean4GlCoalgebras

open HasSat

/-- Theorem 6.21: If Builder has a winning strategy then there is a model graph.
Uses `BuildTree.toModel`. -/
theorem strmg (X : Sequent) (s : Strategy tableauGame Builder) (h : winning s (startPos X)) :
    ∃ (WS : Finset (Finset Formula)) (_ : ModelGraph WS),
      ∃ Z ∈ WS, X.toFinset ⊆ Z := by
  unfold startPos at h
  rcases posOf_for_startPos X with ⟨proPos, posOf_def⟩
  let bt := buildTree s (posOf_def ▸ h)
  let WS := bt.toModel.1
  let M := bt.toModel.2
  refine ⟨WS, ⟨M, ⟨?a, ?b, ?c, ?d⟩⟩, ?X_in⟩
  -- show the model graph properties
  case a =>
    rintro ⟨X, X_in⟩
    unfold WS BuildTree.toModel at X_in
    rcases Finset.mem_image.mp X_in with ⟨π, in_all, def_X⟩
    have := π.locConsSatBas -- using Lemma 6.16 for (i)
    simp_all [PreState.forms]
  -- "(b, c) will follow immediately from the definition"
  case b =>
    simp_all [M]
  case c =>
    intro X Y a φ X_a_Y aφ_in_X -- pick any ⌈a⌉φ
    simp only [M] at X_a_Y
    rcases X_a_Y with ⟨ψ, in_X, sub_Y⟩ -- relation was witnessed by ⌈a⌉ψ
    apply sub_Y -- show that φ is in projection
    simp_all only [Finset.union_singleton, Finset.mem_insert]
    right
    rw [Finset.mem_projection]
    exact aφ_in_X
  case d =>
    simp only [Subtype.exists, exists_and_right, Subtype.forall]
    intro w w_in α φ in_w
    -- "The main challenge" :-)
    -- Paper proof uses Lemmas 6.18 and 6.20 here, depending on loading.
    unfold WS BuildTree.toModel at w_in
    -- w must come from some pre-state:
    rcases Finset.mem_image.mp w_in with ⟨π, π_in, def_w⟩
    subst def_w
    -- unfold PreState.forms at in_w -- NO, use lemma to switch to wforms instead?
    rw [PreState.mem_forms_iff] at in_w
    rcases in_w with in_w|(⟨χ,χul_def,in_w⟩|⟨ψ,ψul_def,in_w⟩)
    · -- normal, use 6.20
      rcases freeDiamondExistence in_w with ⟨π', in_π'_forms, α_rel⟩
      refine ⟨π'.forms, ⟨?_, α_rel⟩, in_π'_forms⟩
      unfold WS
      simp only [BuildTree.toModel]
      exact Finset.mem_image.mpr bt.exists_mem_attach_forms_eq
    · -- loaded but not negated, cannot happen
      exfalso
      cases χ
      unfold LoadFormula.unload at χul_def
      grind
    · -- neg loaded, use 6.18
      rcases ψ with ⟨⟨α',χ⟩ ⟩
      simp only [negUnload, Formula.neg.injEq] at ψul_def
      obtain ⟨ρ, α_rel, hanf⟩ := PreState.loadedDiamondExistence in_w
      unfold WS
      simp only [BuildTree.toModel]
      refine ⟨ρ.forms, ⟨Finset.mem_image.mpr bt.exists_mem_attach_forms_eq, ?_⟩, ?_⟩
      · have : α = α' := by cases χ <;> grind [LoadFormula.unload]
        rw [this]
        exact α_rel
      · have : φ = χ.unload := by cases χ <;> grind [LoadFormula.unload, AnyFormula.unload]
        rw [this]
        exact PreState.mem_forms_of_hasAnf hanf
  case X_in =>
    unfold WS BuildTree.toModel
    -- Use that there must be some pre-state containing the root.
    rcases bt.collect_contains_root with ⟨π, π_in, X_in_π⟩
    refine ⟨PreState.forms ⟨π, π_in⟩,
      Finset.mem_image.mpr ⟨⟨π, π_in⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
    intro φ φ_in
    unfold PreState.forms
    simp only [mem_pathForms]
    use X

/-- Helper for `completeness`. Uses `gameP` and `strmg`. -/
lemma modelExistence {X} : consistent X →
    ∃ (WS : Finset (Finset Formula)) (_ : ModelGraph WS) (W : WS), X.toFinset ⊆ W :=
  by
  intro consX
  rcases gamedet tableauGame (startPos X) with ProverHasWinningS | BuilderHasWinningS
  · absurd consX
    rcases ProverHasWinningS with ⟨sP, winning_sP⟩
    simp_all only [inconsistent]
    rcases gameP _ (sP) winning_sP with ⟨t, _⟩ -- here we don't need the uniformity.
    exact ⟨t⟩
  · rcases BuilderHasWinningS with ⟨sB, winning_sB⟩
    rcases strmg X sB winning_sB with ⟨WS, mg, Z, Z_in_WS, X_sub_Z⟩
    exact ⟨WS, mg, ⟨Z, Z_in_WS⟩, X_sub_Z⟩

/-- If there is any tableau, then there is a uniform one.
Proven via `gameP` and used to show `interpolation`. -/
lemma Tableau.toUniformViaGame {X} (Xfree : X.isFree) (tab : Tableau .nil X) :
    ∃ u_tab : Tableau .nil X, u_tab.isUniform := by
  rcases gamedet tableauGame (startPos X) with ProverHasWinningS | BuilderHasWinningS
  · rcases ProverHasWinningS with ⟨sP, winning_sP⟩
    rcases gameP _ (sP) winning_sP with ⟨t, t_uni⟩
    refine ⟨t, ?_⟩
    simp_all only [isUniform]
    refine ⟨?_, ?_⟩
    · exact Tableau.IsUni.uniCore t_uni
    · have := Tableau.IsUni.flip t_uni -- flip it once more.
      exact Tableau.IsUni.uniCore this
  · rcases BuilderHasWinningS with ⟨sB, winning_sB⟩
    rcases strmg X sB winning_sB with ⟨WS, mg, Z, Z_in_WS, X_sub_Z⟩
    -- Nowe can contradict soundness here.
    have unsat := tableauThenNotSat tab Xfree .nil
    simp only [nodeAt_nil] at unsat
    absurd unsat
    use WS, mg.1
    simp only [Subtype.exists]
    use Z, Z_in_WS
    intro φ φ_in
    apply truthLemma
    grind

/-- Theorem 6.1 -/
theorem completeness : ∀ X, consistent X → satisfiable X :=
  by
  rintro ⟨L, R, O⟩ X_is_consistent
  have ⟨WS, M, w, h⟩ := modelExistence X_is_consistent
  use WS, M.val, w
  simp only [vDash.SemImplies] at *
  intro f f_in
  apply truthLemma M w f
  apply h
  aesop

theorem consIffSat : ∀ X, X.isFree → (consistent X ↔ satisfiable X) :=
  fun X X_isFree => ⟨completeness X, correctness X X_isFree⟩

theorem singletonConsIffSat : ∀ φ, consistent ({φ},{},none) ↔ satisfiable φ :=
  by
  intro φ
  have := consIffSat ⟨{φ}, {}, none⟩
  simp [this, HasSat.satisfiable, vDash.SemImplies, Sequent.toFinset]

end PDL
