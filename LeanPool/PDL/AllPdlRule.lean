/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import LeanPool.PDL.Tableau

/-! # Generating all possible PdlRule applications

Similar to `LocalTableau.all`, this is needed to define `BuildTree` as a finite tree.
-/

@[expose] public section

namespace PDL

/-- List of all `PdlRule`s applicable to `X`. Code is based on part of `theMoves`.
This is also similar to the definitions in `LocalAll.lean`. -/
def PdlRule.all (X : Sequent) : List (Σ Y, PdlRule X Y) :=
  match X with
  | ⟨L, R, none⟩ => -- (L+) if X is not loaded, choice of formula
        ((L.pdlSort).attach.map (fun -- Catch a negation and all boxes (≥ 1) after it to be loaded.
            | ⟨~φ, in_L⟩ => match bdef : boxesOf φ with
              | (δ@δ_def:(_::_), ψ) =>
                  have _in'' : (~⌈⌈δ.dropLast⌉⌉⌈δ.getLast (by simp_all)⌉ψ) ∈ L := by
                    rw [← boxes_last, @List.dropLast_append_getLast, δ_def,
                      ← def_of_boxesOf_def bdef]; simp_all
                  let Y :=  ( L.erase (~⌈⌈δ.dropLast⌉⌉⌈δ.getLast (by simp_all)⌉ψ), R
                            , some (Sum.inl (~'(⌊⌊δ.dropLast⌋⌋⌊δ.getLast (by simp_all)⌋ψ))) )
                  [ ⟨Y, PdlRule.loadL _in'' (nonBox_of_boxesOf_def bdef) rfl ⟩ ]
              | ([],_) => []
            | _ => [] )).flatten
        ++
        (R.pdlSort.attach.map (fun
            | ⟨~φ, in_R⟩ => match bdef : boxesOf φ with
                | (δ@δ_def:(_::_), ψ) =>
                  have _in'' : (~⌈⌈δ.dropLast⌉⌉⌈δ.getLast (by simp_all)⌉ψ) ∈ R := by
                    rw [← boxes_last, @List.dropLast_append_getLast, δ_def,
                      ← def_of_boxesOf_def bdef]; simp_all
                  let Y := ( L, R.erase (~⌈⌈δ.dropLast⌉⌉⌈δ.getLast (by simp_all)⌉ψ)
                      , some (Sum.inr (~'(⌊⌊δ.dropLast⌋⌋⌊δ.getLast (by simp_all)⌋ψ))))
                  [ ⟨ Y, .loadR _in'' (nonBox_of_boxesOf_def bdef) rfl ⟩ ]
                | ([],_) => []
            | _ => [] )).flatten
  | ⟨L, R, some (.inl (~'⌊·a⌋ξ))⟩ =>
          ( match ξ_def : ξ with -- (M) rule, deterministic:
          | .normal φ => [ ⟨ ⟨ _, _, none                ⟩, .modL rfl rfl ⟩ ]
          | .loaded χ => [ ⟨ ⟨ _, _, some (Sum.inl (~'χ))⟩, .modL rfl rfl ⟩ ] )
          ++ -- (L-) rule, deterministic:
          [ match ξsp_def : ξ.split with
          | ⟨δs, φ⟩ => match sp_def : splitLast δs with
            | none =>
              ⟨ (L ∪ {~(⌊·a⌋ξ).unload}, R, none)
              , by refine @PdlRule.freeL _ L R [] (·a) φ _ ?_ ?_ <;>
                  simp_all [nil_of_splitLast_none, AnyFormula.split_eq_nil_is_normal]⟩
            | some ⟨δs_, δ⟩ =>
              ⟨ (L ∪ {~(⌊·a⌋ξ).unload}, R, none)
              , by refine @PdlRule.freeL _ L R (·a :: δs_) δ φ _ ?_ ?_ <;>
                  simp [box_loadBoxes_append_eq_of_loaded_eq_loadBoxes, Formula.boxes_cons,
                    LoadFormula.split_splitLast_to_loadBoxes ξsp_def sp_def]⟩
          ]
  | ⟨L, R, some (.inr (~'⌊·a⌋ξ))⟩ =>
          ( match ξ_def : ξ with -- (M) rule, deterministic:
          | .normal φ => [ ⟨ ⟨ _, _, none                ⟩, .modR rfl rfl ⟩ ]
          | .loaded χ => [ ⟨ ⟨ _, _, some (Sum.inr (~'χ))⟩, .modR rfl rfl ⟩ ] )
          ++ -- (L-) rule, deterministic:
          [ match ξsp_def : ξ.split with
          | ⟨δs, φ⟩ => match sp_def : splitLast δs with
            | none =>
              ⟨ (L, R ∪ {~(⌊·a⌋ξ).unload}, none)
              , by refine @PdlRule.freeR _ L R [] (·a) φ _ ?_ ?_ <;>
                  simp_all [nil_of_splitLast_none, AnyFormula.split_eq_nil_is_normal]⟩
            | some ⟨δs_, δ⟩ =>
              ⟨ (L, R ∪ {~(⌊·a⌋ξ).unload}, none)
              , by refine @PdlRule.freeR _ L R (·a :: δs_) δ φ _ ?_ ?_ <;>
                  simp [box_loadBoxes_append_eq_of_loaded_eq_loadBoxes, Formula.boxes_cons,
                    LoadFormula.split_splitLast_to_loadBoxes ξsp_def sp_def]⟩
          ]
  | _ => []

/-- Specification that `PdlRule.all` is complete, almost: we demand `X.basic` here which is not
part of the `PdlRule` type, but demanded by `Tableau.pdl`.
-/
lemma PdlRule.all_spec {X Y} (bas : X.basic) (r : PdlRule X Y) : ⟨Y, r⟩ ∈ PdlRule.all X := by
  cases r_def : r
  case loadL L δs α φ R in_L notBox Y_def =>
    subst Y_def
    unfold PdlRule.all
    simp only [List.mem_append, List.mem_flatten, List.mem_map, List.mem_attach, true_and,
      Subtype.exists, Formula.mem_pdlSort, ↓existsAndEq]
    refine Or.inl ⟨_, in_L, ?_⟩
    simp only
    split
    next bdef =>
      simp only [List.mem_cons, Sigma.mk.injEq, List.not_mem_nil, or_false]
      constructor
      · convert rfl using 3
        · simp_all only [Formula.neg.injEq]
          rw [← @boxes_last, @List.dropLast_append_getLast]
          exact Eq.symm (def_of_boxesOf_def bdef)
        · simp only [Option.some.injEq, Sum.inl.injEq, NegLoadFormula.neg.injEq]
          have := defs_of_boxesOf_last_of_nonBox notBox δs α
          grind
      · have := defs_of_boxesOf_last_of_nonBox notBox δs α
        grind
    · exfalso; cases δs <;> simp_all [boxesOf]
  case loadR R δs α φ L in_R notBox Y_def =>
    subst Y_def
    unfold PdlRule.all
    simp only [List.mem_append, List.mem_flatten, List.mem_map, List.mem_attach, true_and,
      Subtype.exists, Formula.mem_pdlSort, ↓existsAndEq]
    refine Or.inr ⟨_, in_R, ?_⟩
    simp only
    split
    next bdef =>
      simp only [List.mem_cons, Sigma.mk.injEq, List.not_mem_nil, or_false]
      have := defs_of_boxesOf_last_of_nonBox notBox δs α
      constructor
      · convert rfl using 5
        · rw [← @boxes_last, @List.dropLast_append_getLast]
          exact Eq.symm (def_of_boxesOf_def bdef)
        · simp only [NegLoadFormula.neg.injEq]
          have := defs_of_boxesOf_last_of_nonBox notBox δs α
          grind
      · have := defs_of_boxesOf_last_of_nonBox notBox δs α
        grind
    · exfalso; cases δs <;> simp_all [boxesOf]
  case freeL L R δs α φ X_def Y_def =>
    subst X_def Y_def
    cases δs
    · rw! [Formula.boxes_nil, LoadFormula.boxes_nil]
      cases α_def : α <;> simp_all only [LoadFormula.boxes_nil, all, Finset.singleton_union,
        AnyFormula.split, LoadFormula.unload, List.cons_append, List.nil_append, List.mem_cons,
        Sigma.mk.injEq, Finset.union_singleton, List.not_mem_nil, or_false]
      case atom_prog a => aesop
      all_goals
        -- Here we need `bas` to disallow non-atomic freeL applications
        subst_eqs
        absurd bas
        simp only [Sequent.basic]
        rw [not_and_or]
        simp_all [Sequent.toFinset]
    case cons β βs =>
      rw! [Formula.boxes_cons, LoadFormula.boxes_cons]
      cases β_def : β <;> simp_all only [all, AnyFormula.split, LoadFormula.unload,
        List.cons_append, List.nil_append, List.mem_cons, Sigma.mk.injEq, Finset.union_singleton,
        List.not_mem_nil, or_false]
      case atom_prog a =>
        subst_eqs; split <;> simp_all only [Sigma.mk.injEq, Finset.union_singleton, unload_boxes,
          LoadFormula.unload, true_and] <;> right
        case h_1 spL_def => -- split non-empty into none is impossible
          absurd spL_def
          unfold LoadFormula.split
          cases βs <;> simp_all [splitLast, LoadFormula.boxes_cons]
        case h_2 k γs γ spL_def => -- tricky case
          have := splitLast_undo_of_some spL_def
          simp only at this
          simp only [LoadFormula.split_boxes_cons] at *
          rw [← List.concat_eq_append, ← List.concat_eq_append] at this
          have := List.of_concat_eq_concat this
          cases this
          subst_eqs
          rw! [unload_boxes, LoadFormula.unload]
          grind
      all_goals
        -- Here we need `bas` to disallow non-atomic freeL applications
        subst_eqs
        absurd bas
        simp only [Sequent.basic]
        rw [not_and_or]
        simp_all [Sequent.toFinset]
  case freeR L R δs α φ X_def Y_def =>
    -- COPY-PASTA from `freeL`.
    subst X_def Y_def
    cases δs
    · rw! [Formula.boxes_nil, LoadFormula.boxes_nil]
      cases α_def : α <;> simp_all only [LoadFormula.boxes_nil, all, Finset.singleton_union,
        AnyFormula.split, LoadFormula.unload, List.cons_append, List.nil_append, List.mem_cons,
        Sigma.mk.injEq, Finset.union_singleton, List.not_mem_nil, or_false]
      case atom_prog a => aesop
      all_goals
        -- Here we need `bas` to disallow non-atomic freeL applications
        subst_eqs
        absurd bas
        simp only [Sequent.basic]
        rw [not_and_or]
        simp_all [Sequent.toFinset]
    case cons β βs =>
      rw! [Formula.boxes_cons, LoadFormula.boxes_cons]
      cases β_def : β <;> simp_all only [all, AnyFormula.split, LoadFormula.unload,
        List.cons_append, List.nil_append, List.mem_cons, Sigma.mk.injEq, Finset.union_singleton,
        List.not_mem_nil, or_false]
      case atom_prog a =>
        subst_eqs; split <;> simp_all only [Sigma.mk.injEq, Finset.union_singleton, unload_boxes,
          LoadFormula.unload, true_and] <;> right
        case h_1 spL_def => -- split non-empty into none is impossible
          absurd spL_def
          unfold LoadFormula.split
          cases βs <;> simp_all [splitLast, LoadFormula.boxes_cons]
        case h_2 k γs γ spL_def => -- tricky case
          have := splitLast_undo_of_some spL_def
          simp only at this
          simp only [LoadFormula.split_boxes_cons] at *
          rw [← List.concat_eq_append, ← List.concat_eq_append] at this
          have := List.of_concat_eq_concat this
          cases this
          subst_eqs
          rw! [unload_boxes, LoadFormula.unload]
          grind
      all_goals
        -- Here we need `bas` to disallow non-atomic freeL applications
        subst_eqs
        absurd bas
        simp only [Sequent.basic]
        rw [not_and_or]
        simp_all [Sequent.toFinset]
  case modL L R a ξ X_def Y_def =>
    subst X_def Y_def
    cases ξ <;> simp_all [all]
  case modR L R a ξ X_def Y_def =>
    subst X_def Y_def
    cases ξ <;> simp_all [all]

end PDL
