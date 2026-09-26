/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import LeanPool.PDL.Distance
public import LeanPool.PDL.Local.Tableau

/-! # Local Lemmas for Soundness (part of Section 6) -/

public section

namespace PDL

/-- Formulas on the left of a sequent are in `Sequent.toFinset`. -/
lemma Sequent.mem_toFinset_of_mem_left {L R : Finset Formula} {O : Olf} {f : Formula}
    (h : f ∈ L) : f ∈ Sequent.toFinset (L, R, O) := by
  simp only [Sequent.toFinset, Finset.mem_union]
  tauto

/-- Formulas on the right of a sequent are in `Sequent.toFinset`. -/
lemma Sequent.mem_toFinset_of_mem_right {L R : Finset Formula} {O : Olf} {f : Formula}
    (h : f ∈ R) : f ∈ Sequent.toFinset (L, R, O) := by
  simp only [Sequent.toFinset, Finset.mem_union]
  tauto

/-- Helper to show that an end node of a child tableau is an end node of the whole tableau,
in the unfolded form of `endNodesOf` for `LocalTableau.byLocalRule`. -/
lemma mem_sup_endNodesOf {C : Finset Sequent} (next : (Y : Sequent) → Y ∈ C → LocalTableau Y)
    {Z} (Z_in : Z ∈ C) {Y} (h : Y ∈ endNodesOf (next Z Z_in)) :
    Y ∈ (C.attach.image (fun x => endNodesOf (next x.1 x.2))).sup id := by
  simp only [Finset.sup_image, Function.id_comp, Finset.mem_sup, Finset.mem_attach, true_and,
    Subtype.exists]
  exact ⟨Z, Z_in, h⟩

/-- An atomic loaded diamond cannot be the principal formula of a local rule, hence any
local rule application preserves it, and on the same side. -/
lemma LocalRuleApp.preserve_in_side_atomic (lra : LocalRuleApp) {α : Program} {ξ : AnyFormula}
    {side : Side} (α_atom : α.isAtomic)
    (h : (~''(⌊α⌋ξ)).inSide side lra.X) :
    ∀ Y ∈ lra.C, (~''(⌊α⌋ξ)).inSide side Y := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, rule, C, hC, precons⟩
  subst hC
  simp only [LocalRuleApp.X, AnyNegFormula.inSide] at h
  intro Y Y_in
  cases rule
  case oneSidedL ress' orule ress_def =>
    subst ress_def
    simp only [applyLocalRule, Finset.mem_image, exists_exists_and_eq_and] at Y_in
    rcases Y_in with ⟨res, res_in, rfl⟩
    cases side <;> simpa [AnyNegFormula.inSide] using h
  case oneSidedR ress' orule ress_def =>
    subst ress_def
    simp only [applyLocalRule, Finset.mem_image, exists_exists_and_eq_and] at Y_in
    rcases Y_in with ⟨res, res_in, rfl⟩
    cases side <;> simpa [AnyNegFormula.inSide] using h
  case LRnegL => simp at Y_in
  case LRnegR => simp at Y_in
  case loadedL ress' χ lrule ress_def =>
    exfalso
    have hO := precons.2.2
    simp only [Option.some_subseteq] at hO
    cases side
    · rw [← hO] at h
      simp only [Option.some.injEq, Sum.inl.injEq, NegLoadFormula.neg.injEq] at h
      subst h
      cases lrule with
      | dia notAtom => exact notAtom α_atom
      | dia' notAtom => exact notAtom α_atom
    · rw [← hO] at h
      simp at h
  case loadedR ress' χ lrule ress_def =>
    exfalso
    have hO := precons.2.2
    simp only [Option.some_subseteq] at hO
    cases side
    · rw [← hO] at h
      simp at h
    · rw [← hO] at h
      simp only [Option.some.injEq, Sum.inr.injEq, NegLoadFormula.neg.injEq] at h
      subst h
      cases lrule with
      | dia notAtom => exact notAtom α_atom
      | dia' notAtom => exact notAtom α_atom

/-- Helper for `loadedDiamondPaths`.
If `α` is atomic, and `~''(⌊α⌋ξ)` is in `X`, then for any local tableau `ltab` for `X`,
the same loaded diamond must still be in all `endNodesOf ltab`, on the same side. -/
theorem atomicLocalLoadedDiamond (α : Program) {X : Sequent}
  (ltab : LocalTableau X)
  (α_atom : α.isAtomic)
  (ξ : AnyFormula)
  {side : Side}
  (negLoad_in : (~''(⌊α⌋ξ)).inSide side X)
  : ∀ Y ∈ endNodesOf ltab, (~''(⌊α⌋ξ)).inSide side Y := by
  induction ltab
  case byLocalRule X lra X_def next IH =>
    intro Y Y_in
    rw [endNodesOf] at Y_in
    simp only [Finset.sup_image, Function.id_comp, Finset.mem_sup, Finset.mem_attach, true_and,
      Subtype.exists] at Y_in
    rcases Y_in with ⟨Z, Z_in, Y_in⟩
    exact IH Z Z_in (lra.preserve_in_side_atomic α_atom (by rwa [← X_def]) Z Z_in) Y Y_in
  case sim X bas =>
    intro Y Y_in
    simp only [endNodesOf, Finset.mem_singleton] at Y_in
    subst Y_in
    exact negLoad_in

@[simp]
lemma next_exists_avoid_def_l {B : Finset Sequent} (next : (Y : Sequent) → Y ∈ B → LocalTableau Y) :
    (∃ l, (∃ a, ∃ (h : a ∈ B), endNodesOf (next a h) = l) ∧ Y ∈ l)
    ↔ ∃ Z, ∃ Z_in : Z ∈ B, Y ∈ endNodesOf (next Z Z_in) := by
  constructor
  · rintro ⟨w, ⟨⟨w_1, ⟨w_2, h⟩⟩, right⟩⟩
    subst h
    exact ⟨_, _, right⟩
  · rintro ⟨Z, Z_in, Y_in⟩
    exact ⟨_, ⟨Z, Z_in, rfl⟩, Y_in⟩

lemma lra_preserves_free (lra : LocalRuleApp) (Z_in : Z ∈ lra.C) (X_free : lra.X.isFree) :
    Z.isFree := by
  -- We distinguish which rule was applied.
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, rule, C, hC, preconditionProof⟩
  unfold Sequent.isFree Sequent.isLoaded
  rcases Z with ⟨ZL, ZR, _|(nlf|nlf)⟩ <;> rcases O with (_|(nlf|nlf)) <;> simp_all only
    [LocalRuleApp.X,
    Sequent.none_isFree, applyLocalRule, Finset.mem_image, not_false_eq_true,
    Sequent.some_not_isFree, not_true_eq_false]
  all_goals
    cases rule
    case oneSidedR resNodes orule resNodes_def =>
      cases orule <;> simp_all only [Finset.empty_subset, Finset.singleton_subset_iff,
        Option.none_subseteq, and_true, true_and, Finset.image_empty, Finset.notMem_empty,
        Finset.sdiff_empty, Olf.change_none_none_new, false_and, exists_false,
        Finset.image_singleton, Finset.mem_singleton, exists_eq_left, Finset.union_empty,
        Finset.union_singleton, applyLocalRule, Finset.union_insert, Finset.image_insert,
        Finset.mem_insert, exists_eq_or_imp, ↓existsAndEq, List.pdlToFinFin, Finset.mem_image,
        List.mem_toFinset, List.mem_map, exists_exists_and_eq_and] <;> subst_eqs
      · cases Z_in <;> rename_i h <;> cases h
      · rcases Z_in with ⟨q, _, h⟩; cases h
      · rcases Z_in with ⟨q, _, h⟩; cases h
    case oneSidedL resNodes orule resNodes_def =>
      cases orule <;> simp_all only [Finset.singleton_subset_iff, Finset.empty_subset,
        Option.none_subseteq, and_self, and_true, Finset.image_empty, Finset.notMem_empty,
        Finset.sdiff_empty, Olf.change_none_none_new, false_and, exists_false,
        Finset.image_singleton, Finset.mem_singleton, exists_eq_left, Finset.union_singleton,
        Finset.union_empty, applyLocalRule, Finset.union_insert, Finset.image_insert,
        Finset.mem_insert, exists_eq_or_imp, ↓existsAndEq, true_and, List.pdlToFinFin,
        Finset.mem_image, List.mem_toFinset, List.mem_map, exists_exists_and_eq_and] <;> subst_eqs
      · cases Z_in <;> rename_i h <;> cases h
      · rcases Z_in with ⟨q, _, h⟩; cases h
      · rcases Z_in with ⟨q, _, h⟩; cases h
    all_goals
      simp_all

lemma endNodesOf_free_are_free {X Y} (ltX : LocalTableau X) (h : X.isFree)
    (Y_in : Y ∈ endNodesOf ltX) : Y.isFree := by
  induction ltX
  case byLocalRule X lra X_def next IH =>
    rcases X with ⟨L,R,O⟩
    simp_all only [LocalRuleApp.X, endNodesOf, Finset.sup_image, Function.id_comp, Finset.mem_sup,
      Finset.mem_attach, true_and, Subtype.exists]
    rcases Y_in with ⟨Z, Z_in_C, Y_in⟩
    apply IH Z Z_in_C ?_ Y_in
    -- remains to show that Z is free
    apply lra_preserves_free lra Z_in_C h
  case sim =>
    simp_all

/-- The leftNested diamond rule preserves a minimally chosen loaded path. -/
private theorem localLoadedDiamondList_leftNested {W : Type} {M : KripkeModel W} (φ : Formula)
  {side : Side}
  {v w : W} (w_nξ : (M, w) ⊨ ~''(AnyFormula.normal φ)) (α : Program) (αs : List Program)
  (v_αs_w : relateSeq M (α :: αs) v w) (L R : Finset Formula) (O : Olf) (C : Finset Sequent) (v_t
    : ∀ f ∈ Sequent.toFinset (L, R, O), evaluate M v f)
  (negLoad_in : (~''(AnyFormula.loaded (⌊α⌋AnyFormula.loadBoxes αs (AnyFormula.normal
    φ)))).inSide side (L, R, O))
  (no_other_loading :
    (Sequent.without (L, R, O) (~''(AnyFormula.loaded (⌊α⌋AnyFormula.loadBoxes αs
      (AnyFormula.normal φ))))).isFree)
  (u : W) (v_α_u : relate M α v u) (u_αs_w : relateSeq M αs u w)
  (u_picked_minimally : distanceList M v w (α :: αs) = distance M α v u + distanceList M u w αs)
    (F : List Formula)
  (δ : List Program) (in_D : (F, δ) ∈ Dset α) (same_dist : distanceList M v u δ = distance M α v u)
  (v_δ_u : relateSeq M δ v u) (v_F : ∀ f ∈ F, evaluate M v f) {α' : Program} {χ' : LoadFormula}
  (α'_not_atomic : ¬α'.isAtomic) (precons : ∅ ⊆ L ∧ ∅ ⊆ R ∧ some (Sum.inl (~'⌊α'⌋AnyFormula.loaded
    χ')) ⊆ O)
  (hC : C = applyLocalRule (LocalRule.loadedL (⌊α'⌋AnyFormula.loaded χ') (LoadRule.dia
    α'_not_atomic) rfl) (L, R, O))
  (next : ∀ Y, Y ∈ C → LocalTableau Y)
  (IH :
    ∀ (Y : Sequent) (a : Y ∈ C) {v w : W},
      (M, v) ⊨ Y →
        (M, w) ⊨ ~''(AnyFormula.normal φ) →
          ∀ (α : Program) (αs : List Program),
            relateSeq M (α :: αs) v w →
              (~''(AnyFormula.loaded (⌊α⌋AnyFormula.loadBoxes αs (AnyFormula.normal φ)))).inSide
                side Y →
                (Y.without (~''(AnyFormula.loaded (⌊α⌋AnyFormula.loadBoxes αs (AnyFormula.normal
                  φ))))).isFree →
                  ∃ Y_1 ∈ endNodesOf (next Y a),
                    (M, v) ⊨ Y_1 ∧
                      (Y_1.isFree ∨
                        ∃ F γ,
                          (~''(AnyFormula.loadBoxes γ (AnyFormula.normal φ))).inSide side Y_1 ∧
                            relateSeq M γ v w ∧
                              distanceList M v w γ = distanceList M v w (α :: αs) ∧
                                (M, v) ⊨ F ∧
                                  (F, γ) ∈ Dl (α :: αs) ∧
                                    (Y_1.without (~''(AnyFormula.loadBoxes γ (AnyFormula.normal
                                      φ)))).isFree)) :
  ∃ Y ∈ (Finset.image (fun x ↦ endNodesOf (next x.1 x.2)) C.attach).sup id,
    (M, v) ⊨ Y ∧
      (Y.isFree ∨
        ∃ F γ,
          (~''(AnyFormula.loadBoxes γ (AnyFormula.normal φ))).inSide side Y ∧
            relateSeq M γ v w ∧
              distanceList M v w γ = distanceList M v w (α :: αs) ∧
                (M, v) ⊨ F ∧
                  (F, γ) ∈ Dl (α :: αs) ∧
                    (Y.without (~''(AnyFormula.loadBoxes γ (AnyFormula.normal φ)))).isFree) := by
  -- The rule application has its own α' that must be α, and χ' must be ⌊αs⌋φ.
  have ⟨α_same, χ_def⟩ : α = α' ∧ χ' = (AnyFormula.loadBoxes αs (AnyFormula.normal φ)) := by
    simp only [AnyNegFormula.inSide] at negLoad_in
    have := precons.2.2
    simp only [Option.some_subseteq] at this
    rw [← this] at negLoad_in
    cases side <;> aesop
  subst α_same -- But cannot do `subst χ_def`.
  -- This F,δ pair is also used for one result in `B`:
  have in_C : (L ∪ F.toFinset, R, some (Sum.inl (~'⌊⌊δ⌋⌋χ'))) ∈ C := by
    simp only [applyLocalRule, Finset.sdiff_empty, List.pdlToFinFinOpt,
      unfoldDiamondLoaded, YsetLoad, List.map_map] at hC
    rw [hC]
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_map, Function.comp_apply,
      Prod.exists, Prod.mk.injEq, ↓existsAndEq, and_true, Option.map_some,
      Finset.union_empty, Olf.change_some, Option.some.injEq, Sum.inl.injEq,
      NegLoadFormula.neg.injEq, true_and]
    exact ⟨F, δ, in_D, rfl, rfl⟩
  cases δ
  case nil => -- δ is empty, is this the easy or the hard case?;-)
    simp only [relateSeq_nil] at v_δ_u v_F -- Here we have v = u.
    subst v_δ_u
    cases αs
    · exfalso; simp_all
    case cons new_α new_αs =>
      -- Let's prepare the IH application now.
      specialize @IH _ in_C v w ?_ w_nξ new_α new_αs u_αs_w ?_ ?_
      · intro f f_in; clear IH
        simp only [Sequent.toFinset, Finset.mem_union, List.mem_toFinset,
          Option.map_some, Sum.elim_inl, negUnload, unload_boxes, Formula.boxes_nil,
          Option.mem_toFinset, Option.mem_def, Option.some.injEq] at f_in
        rcases f_in with ((f_in|f_in)|f_in)|f_def
        · exact v_t f (Sequent.mem_toFinset_of_mem_left f_in)
        · exact v_F _ f_in
        · exact v_t f (Sequent.mem_toFinset_of_mem_right f_in)
        · subst f_def
          rw [loaded_eq_to_unload_eq χ' _ _ χ_def]
          simp only [evaluate, Formula.boxes_cons, not_forall]
          rcases u_αs_w with ⟨x, v_α_x, bla⟩
          use x, v_α_x; rw [evalBoxes]
          push Not; use w; tauto
      · clear IH next
        cases side <;> subst_eqs <;> simp_all [AnyNegFormula.inSide, LoadFormula.boxes]
      · clear IH next
        simp_all [Sequent.without, LoadFormula.boxes]
      -- Now actually get the IH result.
      rcases IH with ⟨ Y, Y_in, v_Y
                     , ( Y_free
                       | ⟨G, γs, in_Y, v_γs_w, dist_eq, v_G, in_Dl, Y_almost_free⟩ )⟩
      · refine ⟨Y, (mem_sup_endNodesOf _ in_C Y_in) , ⟨v_Y, Or.inl Y_free⟩⟩ -- free'n'easy
      · refine ⟨Y, (mem_sup_endNodesOf _ in_C Y_in) , ⟨v_Y, Or.inr ?_⟩⟩
        refine ⟨F ∪ G, γs, in_Y, v_γs_w, ?_, ?_, ?_, Y_almost_free⟩
        · rw [dist_eq]
          rw [u_picked_minimally]
          have : distance M α v v = 0 := by
            -- Here δ is [] and thus α can have distance 0
            rw [distance_list_nil_self] at same_dist
            exact same_dist.symm
          aesop
        · intro f f_in
          simp only [List.mem_union_iff] at f_in; cases f_in
          · apply v_F; assumption
          · apply v_G; assumption
        simp only [Dl, List.mem_flatMap, Prod.exists]
        refine ⟨_, _, in_D, ?_⟩
        simp only [↓reduceIte, List.mem_flatMap, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
          or_false, Prod.exists, exists_eq_right_right']
        refine ⟨G, in_Dl, rfl⟩
  case cons d δs =>
    -- A non-empty δ came from α, so we have not actually made the step to `u` yet.
    -- Again we prepare to use IH, but now for `d` and `δs ++ αs` instead.
    specialize @IH _ in_C v w ?_ w_nξ d (δs ++ αs) ?_ ?_ ?_
    · intro f f_in; clear IH
      simp only [Sequent.toFinset, Finset.mem_union, List.mem_toFinset,
        Option.map_some, Sum.elim_inl, negUnload, unload_boxes,
        Formula.boxes_cons, Option.mem_toFinset, Option.mem_def,
        Option.some.injEq] at f_in
      rcases f_in with ((f_in|f_in)|f_in)|f_def
      · exact v_t f (Sequent.mem_toFinset_of_mem_left f_in)
      · exact v_F _ f_in
      · exact v_t f (Sequent.mem_toFinset_of_mem_right f_in)
      · subst f_def
        simp only [evaluate, evalBoxes, not_forall,]
        rw [@relateSeq_cons] at v_δ_u
        rcases v_δ_u with ⟨x, v_d_x, x_δs_u⟩
        refine ⟨x, v_d_x, ⟨u, x_δs_u, ?_⟩⟩
        rw [loaded_eq_to_unload_eq χ' _ _ χ_def, evalBoxes]
        push Not; use w; tauto
    · simp_rw [relateSeq_cons, relateSeq_append]
      rw [relateSeq_cons] at v_δ_u
      rcases v_δ_u with ⟨x, v_d_x, x_δ_u⟩
      refine ⟨x, v_d_x, ⟨u, x_δ_u, u_αs_w⟩⟩
    · clear IH next
      cases side
      · simp only [AnyNegFormula.inSide]
        convert rfl
        apply box_loadBoxes_append_eq_of_loaded_eq_loadBoxes χ_def
      · simp_all [AnyNegFormula.inSide, LoadFormula.boxes]
    · exact Sequent.without_loadBoxes_isFree_of_eq_inl χ_def
    -- Now actually get the IH result.
    rcases IH with ⟨ Y, Y_in, v_Y
                   , ( Y_free
                     | ⟨G, γs, in_Y, v_γs_w, dist_eq, v_G, in_Dl, Y_almost_free⟩ )⟩
    · refine ⟨Y, (mem_sup_endNodesOf _ in_C Y_in) , ⟨v_Y, Or.inl Y_free⟩⟩ -- free'n'easy
    · refine ⟨Y, (mem_sup_endNodesOf _ in_C Y_in) , ⟨v_Y, Or.inr ?_⟩⟩
      refine ⟨F, _, in_Y, v_γs_w, ?_, v_F, ?_, Y_almost_free⟩
      · rw [dist_eq]
        -- was: TRICKY PROBLEM - how do we know that `u` is chosen to minimze distance?
        rw [← List.cons_append, u_picked_minimally] -- now we DO have that :-)
        rw [← same_dist, distance_list_append]
        apply iInf_of_min
        intro y
        -- Idea: y cannot provide a shorter distance than u.
        rw [same_dist, ← u_picked_minimally, distance_list_cons]
        apply le_add_of_le_add_right ?_ (distance_le_Hdistance in_D ?_)
        · exact iInf_le_iff.mpr fun b a => a y
        · simp only [vDash.SemImplies, evaluatePoint, conEval]; assumption
      have αs_nonEmpty : αs ≠ [] := by cases αs <;> simp_all
      simp only [Dl, List.mem_flatMap, Prod.exists] -- uses `αs_nonEmpty`
      refine ⟨F, d :: δs, in_D, ?_⟩
      simp only [reduceCtorEq, ↓reduceIte, List.cons_append, List.mem_cons, Prod.mk.injEq,
        true_and, List.not_mem_nil, or_false]
      -- Now show that `d` is atomic, because it resulted from `H α`.
      have ⟨a, d_atom⟩ : ∃ a, d = ((·a) : Program) := by
        have := Dset_mem_sequence α in_D
        rcases this with inl | ⟨a, ⟨δ, list_prop⟩⟩
        · exfalso; simp_all
        · refine ⟨a, by simp_all⟩
      subst d_atom
      -- Hence `Dl (d :: ...)` does not actually unfold anything.
      simp only [Dl_atomic_cons, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at in_Dl
      exact in_Dl.2

/-- The leftNormal diamond rule preserves a minimally chosen loaded path. -/
private theorem localLoadedDiamondList_leftNormal {W : Type} {M : KripkeModel W} (φ : Formula)
  {side : Side}
  {v w : W} (w_nξ : (M, w) ⊨ ~''(AnyFormula.normal φ)) (α : Program) (αs : List Program)
  (v_αs_w : relateSeq M (α :: αs) v w) (L R : Finset Formula) (O : Olf) (C : Finset Sequent) (v_t
    : ∀ f ∈ Sequent.toFinset (L, R, O), evaluate M v f)
  (negLoad_in : (~''(AnyFormula.loaded (⌊α⌋AnyFormula.loadBoxes αs (AnyFormula.normal
    φ)))).inSide side (L, R, O))
  (no_other_loading :
    (Sequent.without (L, R, O) (~''(AnyFormula.loaded (⌊α⌋AnyFormula.loadBoxes αs
      (AnyFormula.normal φ))))).isFree)
  (u : W) (v_α_u : relate M α v u) (u_αs_w : relateSeq M αs u w)
  (u_picked_minimally : distanceList M v w (α :: αs) = distance M α v u + distanceList M u w αs)
    (F : List Formula)
  (δ : List Program) (in_D : (F, δ) ∈ Dset α) (same_dist : distanceList M v u δ = distance M α v u)
  (v_δ_u : relateSeq M δ v u) (v_F : ∀ f ∈ F, evaluate M v f) {α' : Program} {φ' : Formula}
  (α'_not_atomic : ¬α'.isAtomic) (precons : ∅ ⊆ L ∧ ∅ ⊆ R ∧ some (Sum.inl (~'⌊α'⌋AnyFormula.normal
    φ')) ⊆ O)
  (hC : C = applyLocalRule (LocalRule.loadedL (⌊α'⌋AnyFormula.normal φ') (LoadRule.dia'
    α'_not_atomic) rfl) (L, R, O))
  (next : ∀ Y, Y ∈ C → LocalTableau Y)
  (IH :
    ∀ (Y : Sequent) (a : Y ∈ C) {v w : W},
      (M, v) ⊨ Y →
        (M, w) ⊨ ~''(AnyFormula.normal φ) →
          ∀ (α : Program) (αs : List Program),
            relateSeq M (α :: αs) v w →
              (~''(AnyFormula.loaded (⌊α⌋AnyFormula.loadBoxes αs (AnyFormula.normal φ)))).inSide
                side Y →
                (Y.without (~''(AnyFormula.loaded (⌊α⌋AnyFormula.loadBoxes αs (AnyFormula.normal
                  φ))))).isFree →
                  ∃ Y_1 ∈ endNodesOf (next Y a),
                    (M, v) ⊨ Y_1 ∧
                      (Y_1.isFree ∨
                        ∃ F γ,
                          (~''(AnyFormula.loadBoxes γ (AnyFormula.normal φ))).inSide side Y_1 ∧
                            relateSeq M γ v w ∧
                              distanceList M v w γ = distanceList M v w (α :: αs) ∧
                                (M, v) ⊨ F ∧
                                  (F, γ) ∈ Dl (α :: αs) ∧
                                    (Y_1.without (~''(AnyFormula.loadBoxes γ (AnyFormula.normal
                                      φ)))).isFree)) :
  ∃ Y ∈ (Finset.image (fun x ↦ endNodesOf (next x.1 x.2)) C.attach).sup id,
    (M, v) ⊨ Y ∧
      (Y.isFree ∨
        ∃ F γ,
          (~''(AnyFormula.loadBoxes γ (AnyFormula.normal φ))).inSide side Y ∧
            relateSeq M γ v w ∧
              distanceList M v w γ = distanceList M v w (α :: αs) ∧
                (M, v) ⊨ F ∧
                  (F, γ) ∈ Dl (α :: αs) ∧
                    (Y.without (~''(AnyFormula.loadBoxes γ (AnyFormula.normal φ)))).isFree) := by
  -- The rule application has its own α' that must be α,
  -- also has its own φ' that must be φ, (this is new/easier here)
  -- and αs must be [], there is no more χ.
  have ⟨α_same, φ_same, αs_empty⟩ : α = α' ∧ φ = φ' ∧ αs = [] := by
    simp only [AnyNegFormula.inSide] at negLoad_in
    have := precons.2.2
    simp only [Option.some_subseteq] at this
    rw [← this] at negLoad_in
    cases side
    · simp only [Option.some.injEq, Sum.inl.injEq, NegLoadFormula.neg.injEq,
      LoadFormula.box.injEq] at *
      rcases negLoad_in with ⟨α_same, φ_def⟩
      cases αs <;> simp_all
    · subst hC this
      simp_all only [Option.some.injEq, reduceCtorEq]
  -- It seems this is actually easier than the `dia` case, we can `subst` more here.
  subst α_same
  subst φ_same
  subst αs_empty
  simp only [relateSeq] at u_αs_w
  subst u_αs_w -- We now have u = w.
  -- Note: we now do `in_C` *after* distinguishing whether δ = [].
  simp only [Finset.sup_image, Function.id_comp, Finset.mem_sup, Finset.mem_attach, true_and,
    Subtype.exists, Dl_singleton]
  cases δ
  case nil => -- δ is empty, so we should have a free result?
    clear IH -- No IH needed because we reach a free node.
    simp only [relateSeq_nil] at v_δ_u v_F -- Here we have v = u.
    subst v_δ_u
    -- This F,δ pair is also used for one result in `C`:
    have in_C : (L ∪ (F.toFinset ∪ {~φ}), R, none) ∈ C := by
      clear next
      simp only [applyLocalRule, Finset.sdiff_empty, List.pdlToFinFinOpt,
        unfoldDiamondLoaded', YsetLoad', List.map_map] at hC
      rw [hC]
      simp only [Finset.union_singleton, Finset.union_insert, Finset.mem_image,
        List.mem_toFinset, List.mem_map, Function.comp_apply, Prod.exists, Prod.mk.injEq,
        ↓existsAndEq, and_true, Finset.union_empty, true_and]
      refine ⟨F, [], in_D, ?_, ?_⟩
      · simp
      · cases O <;> cases side
        all_goals
          simp only [relateSeq_singleton, Finset.empty_subset, Option.some_subseteq,
            reduceCtorEq, and_false, Option.some.injEq, true_and, AnyFormula.boxes_nil,
            Olf.change, Option.pdlOverwrite, AnyNegFormula.inSide, splitLast,
            Option.map_none] at *
        · rw [negLoad_in]; simp
        · subst hC; exfalso; aesop
    -- We do not know `Y` yet because ltab may continue after `(L ++ F ++ [~φ], R, none)`.
    -- So let's use localTableauTruth to find a free end node, similar to αs = [] case.
    have v_Z : (M, v) ⊨ (show Sequent from (L ∪ (F.toFinset ∪ {~φ}), R, none)) := by
      intro f f_in
      simp only [Sequent.toFinset, Finset.mem_union, List.mem_toFinset,
        Finset.mem_singleton, Option.map_none, Option.mem_toFinset, Option.mem_def,
        reduceCtorEq, or_false] at f_in
      rcases f_in with ((f_in|f_in|rfl)|f_in)
      · exact v_t f (Sequent.mem_toFinset_of_mem_left f_in)
      · exact v_F _ f_in
      · exact w_nξ
      · exact v_t f (Sequent.mem_toFinset_of_mem_right f_in)
    rcases (localTableauTruth (next _ in_C) M v).1 v_Z with ⟨Y, Y_in, v_Y⟩
    refine ⟨Y, ⟨_, in_C, Y_in⟩, ⟨v_Y, Or.inl ?Y_free⟩⟩
    apply endNodesOf_free_are_free (next _ in_C) ?_ Y_in
    simp
  case cons d δs =>
    rw [@relateSeq_cons] at v_δ_u
    rcases v_δ_u with ⟨x, v_d_x, x_δs_u⟩
    let δ_β := match h : splitLast (d :: δs) with
      | some this => this
      | none => by exfalso; simp_all [splitLast]
    have split_def : splitLast (d :: δs) = some δ_β := by rfl
    -- This F,δ pair is also used for one result in `C`:
    have in_C : (L ∪ F.toFinset, R, some (Sum.inl (~'loadMulti δ_β.1 δ_β.2 φ))) ∈ C := by
      simp only [applyLocalRule, Finset.sdiff_empty, List.pdlToFinFinOpt,
        unfoldDiamondLoaded', YsetLoad', List.map_map] at hC
      rw [hC]
      simp only [Finset.mem_image, List.mem_toFinset, List.mem_map, Function.comp_apply,
        Prod.exists, Prod.mk.injEq, ↓existsAndEq, and_true, Finset.union_empty, true_and]
      use F, (d :: δs), in_D
      rw [split_def]
      simp
    -- Rest based on non-empty δ case in `dia` above; changed to work with `loadMulti`.
    -- A non-empty δ came from α, so we have not actually made the step to `u` yet.
    -- Again we prepare to use IH, but now for `d` and `δs` instead.
    specialize @IH _ in_C v u ?_ w_nξ d δs ?_ ?_ ?_
    · intro f f_in; clear IH
      simp only [Sequent.toFinset, Finset.mem_union, List.mem_toFinset,
        Option.map_some, Sum.elim_inl, negUnload, unload_loadMulti,
        Option.mem_toFinset, Option.mem_def, Option.some.injEq] at f_in
      rcases f_in with ((f_in|f_in)|f_in)|f_def
      · exact v_t f (Sequent.mem_toFinset_of_mem_left f_in)
      · exact v_F _ f_in
      · exact v_t f (Sequent.mem_toFinset_of_mem_right f_in)
      · subst f_def
        rw [← @boxes_last, splitLast_undo_of_some split_def]
        simp only [evaluate, Formula.boxes_cons, evalBoxes, not_forall]
        refine ⟨x, v_d_x, ⟨u, x_δs_u, ?_⟩⟩
        exact w_nξ
    · simp_rw [relateSeq_cons]
      exact ⟨x, v_d_x, x_δs_u⟩
    · clear IH next
      cases side
      · simp only [AnyNegFormula.inSide, Option.some.injEq, Sum.inl.injEq,
        NegLoadFormula.neg.injEq]
        exact loadMulti_of_splitLast_cons split_def
      · exfalso
        simp_all [AnyNegFormula.inSide]
    · exact Sequent.without_loadMulti_isFree_of_splitLast_cons_inl split_def
    -- Now actually get the IH result.
    rcases IH with ⟨Y, Y_in, v_Y
                   , ( Y_free
                     | ⟨G, γs, in_Y, v_γs_w, dist_eq, v_G, in_Dl, Y_almost_free⟩ )⟩
    · refine ⟨Y, ⟨_, in_C, Y_in⟩ , ⟨v_Y, Or.inl Y_free⟩⟩ -- free'n'easy
    · refine ⟨Y, ⟨_, in_C, Y_in⟩ , ⟨v_Y, Or.inr ?_⟩⟩
      refine ⟨F, _, in_Y, v_γs_w, ?_, v_F, ?_, Y_almost_free⟩
      · rw [dist_eq,same_dist,distance_list_singleton]
      -- Now show that `d` is atomic, because it resulted from `H α`.
      have ⟨a, d_atom⟩ : ∃ a, d = ((·a) : Program) := by
        have := Dset_mem_sequence α in_D
        rcases this with inl | ⟨a, ⟨δ, list_prop⟩⟩
        · exfalso; simp_all
        · refine ⟨a, by simp_all⟩
      subst d_atom
      -- Hence `Dl (d :: ...)` does not actually unfold anything.
      simp only [Dl_atomic_cons, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at in_Dl
      rw [in_Dl.2]
      exact in_D

/-- The rightNested diamond rule preserves a minimally chosen loaded path. -/
private theorem localLoadedDiamondList_rightNested {W : Type} {M : KripkeModel W} (φ : Formula)
  {side : Side}
  {v w : W} (w_nξ : (M, w) ⊨ ~''(AnyFormula.normal φ)) (α : Program) (αs : List Program)
  (v_αs_w : relateSeq M (α :: αs) v w) (L R : Finset Formula) (O : Olf) (C : Finset Sequent) (v_t
    : ∀ f ∈ Sequent.toFinset (L, R, O), evaluate M v f)
  (negLoad_in : (~''(AnyFormula.loaded (⌊α⌋AnyFormula.loadBoxes αs (AnyFormula.normal
    φ)))).inSide side (L, R, O))
  (no_other_loading :
    (Sequent.without (L, R, O) (~''(AnyFormula.loaded (⌊α⌋AnyFormula.loadBoxes αs
      (AnyFormula.normal φ))))).isFree)
  (u : W) (v_α_u : relate M α v u) (u_αs_w : relateSeq M αs u w)
  (u_picked_minimally : distanceList M v w (α :: αs) = distance M α v u + distanceList M u w αs)
    (F : List Formula)
  (δ : List Program) (in_D : (F, δ) ∈ Dset α) (same_dist : distanceList M v u δ = distance M α v u)
  (v_δ_u : relateSeq M δ v u) (v_F : ∀ f ∈ F, evaluate M v f) {α' : Program} {χ' : LoadFormula}
  (α'_not_atomic : ¬α'.isAtomic) (precons : ∅ ⊆ L ∧ ∅ ⊆ R ∧ some (Sum.inr (~'⌊α'⌋AnyFormula.loaded
    χ')) ⊆ O)
  (hC : C = applyLocalRule (LocalRule.loadedR (⌊α'⌋AnyFormula.loaded χ') (LoadRule.dia
    α'_not_atomic) rfl) (L, R, O))
  (next : ∀ Y, Y ∈ C → LocalTableau Y)
  (IH :
    ∀ (Y : Sequent) (a : Y ∈ C) {v w : W},
      (M, v) ⊨ Y →
        (M, w) ⊨ ~''(AnyFormula.normal φ) →
          ∀ (α : Program) (αs : List Program),
            relateSeq M (α :: αs) v w →
              (~''(AnyFormula.loaded (⌊α⌋AnyFormula.loadBoxes αs (AnyFormula.normal φ)))).inSide
                side Y →
                (Y.without (~''(AnyFormula.loaded (⌊α⌋AnyFormula.loadBoxes αs (AnyFormula.normal
                  φ))))).isFree →
                  ∃ Y_1 ∈ endNodesOf (next Y a),
                    (M, v) ⊨ Y_1 ∧
                      (Y_1.isFree ∨
                        ∃ F γ,
                          (~''(AnyFormula.loadBoxes γ (AnyFormula.normal φ))).inSide side Y_1 ∧
                            relateSeq M γ v w ∧
                              distanceList M v w γ = distanceList M v w (α :: αs) ∧
                                (M, v) ⊨ F ∧
                                  (F, γ) ∈ Dl (α :: αs) ∧
                                    (Y_1.without (~''(AnyFormula.loadBoxes γ (AnyFormula.normal
                                      φ)))).isFree)) :
  ∃ Y ∈ (Finset.image (fun x ↦ endNodesOf (next x.1 x.2)) C.attach).sup id,
    (M, v) ⊨ Y ∧
      (Y.isFree ∨
        ∃ F γ,
          (~''(AnyFormula.loadBoxes γ (AnyFormula.normal φ))).inSide side Y ∧
            relateSeq M γ v w ∧
              distanceList M v w γ = distanceList M v w (α :: αs) ∧
                (M, v) ⊨ F ∧
                  (F, γ) ∈ Dl (α :: αs) ∧
                    (Y.without (~''(AnyFormula.loadBoxes γ (AnyFormula.normal φ)))).isFree) := by
  -- The rule application has its own α' that must be α, and χ' must be ⌊αs⌋φ.
  have ⟨α_same, χ_def⟩ : α = α' ∧ χ' = (AnyFormula.loadBoxes αs (AnyFormula.normal φ)) := by
    simp only [AnyNegFormula.inSide] at negLoad_in
    have := precons.2.2
    simp only [Option.some_subseteq] at this
    rw [← this] at negLoad_in
    cases side <;> aesop
  subst α_same -- But cannot do `subst χ_def`.
  -- This F,δ pair is also used for one result in `C`:
  have in_C : (L, R ∪ F.toFinset, some (Sum.inr (~'⌊⌊δ⌋⌋χ'))) ∈ C := by
    simp only [applyLocalRule, Finset.sdiff_empty, List.pdlToFinFinOpt,
      unfoldDiamondLoaded, YsetLoad, List.map_map] at hC
    rw [hC]
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_map, Function.comp_apply,
      Prod.exists, Prod.mk.injEq, ↓existsAndEq, and_true, Option.map_some,
      Finset.union_empty, Olf.change_some, Option.some.injEq, Sum.inr.injEq,
      NegLoadFormula.neg.injEq, true_and]
    exact ⟨F, δ, in_D, rfl, rfl⟩
  cases δ
  case nil => -- δ is empty, is this the easy or the hard case?;-)
    simp only [relateSeq_nil] at v_δ_u v_F -- Here we have v = u.
    subst v_δ_u
    cases αs
    · exfalso; simp_all
    case cons new_α new_αs =>
      -- Let's prepare the IH application now.
      specialize @IH _ in_C v w ?_ w_nξ new_α new_αs u_αs_w ?_ ?_
      · intro f f_in; clear IH
        simp only [Sequent.toFinset, Finset.mem_union, List.mem_toFinset,
          Option.map_some, Sum.elim_inr, negUnload,
          LoadFormula.boxes_nil,
          Option.mem_toFinset, Option.mem_def, Option.some.injEq] at f_in
        rcases f_in with (f_in|(f_in|f_in))|f_def
        · exact v_t f (Sequent.mem_toFinset_of_mem_left f_in)
        · exact v_t f (Sequent.mem_toFinset_of_mem_right f_in)
        · exact v_F _ f_in
        · subst f_def
          rw [loaded_eq_to_unload_eq χ' _ _ χ_def]
          simp only [evaluate, Formula.boxes_cons, not_forall]
          rcases u_αs_w with ⟨x, v_α_x, bla⟩
          use x, v_α_x; rw [evalBoxes]
          push Not; use w; tauto
      · clear IH next
        cases side <;> simp_all [AnyNegFormula.inSide, LoadFormula.boxes]
      · clear IH next
        simp_all [Sequent.without, LoadFormula.boxes]
      -- Now actually get the IH result.
      rcases IH with ⟨ Y, Y_in, v_Y
                     , ( Y_free
                       | ⟨G, γs, in_Y, v_γs_w, dist_eq, v_G, in_Dl, Y_almost_free⟩ )⟩
      · refine ⟨Y, (mem_sup_endNodesOf _ in_C Y_in) , ⟨v_Y, Or.inl Y_free⟩⟩ -- free'n'easy
      · -- Not fully sure here.
        refine ⟨Y, (mem_sup_endNodesOf _ in_C Y_in) , ⟨v_Y, Or.inr ?_⟩⟩
        refine ⟨F ∪ G, γs, in_Y, v_γs_w, ?_, ?_, ?_, Y_almost_free⟩
        · rw [dist_eq]
          rw [u_picked_minimally]
          have : distance M α v v = 0 := by
            -- Here δ is [] and thus α can have distance 0
            rw [distance_list_nil_self] at same_dist
            exact same_dist.symm
          aesop
        · intro f f_in
          simp only [List.mem_union_iff] at f_in; cases f_in
          · apply v_F; assumption
          · apply v_G; assumption
        simp only [Dl, List.mem_flatMap, Prod.exists]
        refine ⟨_, _, in_D, ?_⟩
        simp only [↓reduceIte, List.mem_flatMap, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
          or_false, Prod.exists, exists_eq_right_right']
        refine ⟨G, in_Dl, rfl⟩
  case cons d δs =>
    -- A non-empty δ came from α, so we have not actually made the step to `u` yet.
    -- Again we prepare to use IH, but now for `d` and `δs ++ αs` instead.
    specialize @IH _ in_C v w ?_ w_nξ d (δs ++ αs) ?_ ?_ ?_
    · intro f f_in
      simp only [Sequent.toFinset, Finset.mem_union, List.mem_toFinset,
        Option.map_some, Sum.elim_inr, negUnload, unload_boxes,
        Formula.boxes_cons, Option.mem_toFinset, Option.mem_def,
        Option.some.injEq] at f_in
      rcases f_in with (f_in|f_in|f_in)|f_def
      · exact v_t f (Sequent.mem_toFinset_of_mem_left f_in)
      · exact v_t f (Sequent.mem_toFinset_of_mem_right f_in)
      · exact v_F _ f_in
      · subst f_def
        simp only [evaluate, evalBoxes, not_forall]
        rw [@relateSeq_cons] at v_δ_u
        rcases v_δ_u with ⟨x, v_d_x, x_δs_u⟩
        refine ⟨x, v_d_x, ⟨u, x_δs_u, ?_⟩⟩
        rw [loaded_eq_to_unload_eq χ' _ _ χ_def, evalBoxes]
        push Not; use w; tauto
    · simp_rw [relateSeq_cons, relateSeq_append]
      rw [relateSeq_cons] at v_δ_u
      rcases v_δ_u with ⟨x, v_d_x, x_δ_u⟩
      refine ⟨x, v_d_x, ⟨u, x_δ_u, u_αs_w⟩⟩
    · clear IH next
      cases side
      · exfalso
        simp_all [AnyNegFormula.inSide, LoadFormula.boxes]
      · simp only [AnyNegFormula.inSide]
        convert rfl
        apply box_loadBoxes_append_eq_of_loaded_eq_loadBoxes χ_def
    · exact Sequent.without_loadBoxes_isFree_of_eq_inr χ_def
    -- Now actually get the IH result.
    rcases IH with ⟨ Y, Y_in, v_Y
                   , ( Y_free
                     | ⟨G, γs, in_Y, v_γs_w, dist_eq, v_G, in_Dl, Y_almost_free⟩ )⟩
    · refine ⟨Y, (mem_sup_endNodesOf _ in_C Y_in) , ⟨v_Y, Or.inl Y_free⟩⟩ -- free'n'easy
    · refine ⟨Y, (mem_sup_endNodesOf _ in_C Y_in) , ⟨v_Y, Or.inr ?_⟩⟩
      refine ⟨F, _, in_Y, v_γs_w, ?_, v_F, ?_, Y_almost_free⟩
      · rw [dist_eq]
        -- was: TRICKY PROBLEM - how do we know that `u` is chosen to minimze distance?
        rw [← List.cons_append, u_picked_minimally] -- now we DO have that :-)
        rw [← same_dist, distance_list_append]
        apply iInf_of_min
        intro y
        -- Idea: y cannot provide a shorter distance than u.
        rw [same_dist, ← u_picked_minimally, distance_list_cons]
        apply le_add_of_le_add_right ?_ (distance_le_Hdistance in_D ?_)
        · exact iInf_le_iff.mpr fun b a => a y
        · simp only [vDash.SemImplies, evaluatePoint, conEval]; assumption
      have αs_nonEmpty : αs ≠ [] := by cases αs <;> simp_all
      simp only [Dl, List.mem_flatMap, Prod.exists] -- uses `αs_nonEmpty`
      refine ⟨F, d :: δs, in_D, ?_⟩
      simp only [reduceCtorEq, ↓reduceIte, List.cons_append, List.mem_cons, Prod.mk.injEq,
        true_and, List.not_mem_nil, or_false]
      -- Now show that `d` is atomic, because it resulted from `H α`.
      have ⟨a, d_atom⟩ : ∃ a, d = ((·a) : Program) := by
        have := Dset_mem_sequence α in_D
        rcases this with inl | ⟨a, ⟨δ, list_prop⟩⟩
        · exfalso; simp_all
        · refine ⟨a, by simp_all⟩
      subst d_atom
      -- Hence `Dl (d :: ...)` does not actually unfold anything.
      simp only [Dl_atomic_cons, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at in_Dl
      exact in_Dl.2

/-- The rightNormal diamond rule preserves a minimally chosen loaded path. -/
private theorem localLoadedDiamondList_rightNormal {W : Type} {M : KripkeModel W} (φ : Formula)
  {side : Side}
  {v w : W} (w_nξ : (M, w) ⊨ ~''(AnyFormula.normal φ)) (α : Program) (αs : List Program)
  (v_αs_w : relateSeq M (α :: αs) v w) (L R : Finset Formula) (O : Olf) (C : Finset Sequent) (v_t
    : ∀ f ∈ Sequent.toFinset (L, R, O), evaluate M v f)
  (negLoad_in : (~''(AnyFormula.loaded (⌊α⌋AnyFormula.loadBoxes αs (AnyFormula.normal
    φ)))).inSide side (L, R, O))
  (no_other_loading :
    (Sequent.without (L, R, O) (~''(AnyFormula.loaded (⌊α⌋AnyFormula.loadBoxes αs
      (AnyFormula.normal φ))))).isFree)
  (u : W) (v_α_u : relate M α v u) (u_αs_w : relateSeq M αs u w)
  (u_picked_minimally : distanceList M v w (α :: αs) = distance M α v u + distanceList M u w αs)
    (F : List Formula)
  (δ : List Program) (in_D : (F, δ) ∈ Dset α) (same_dist : distanceList M v u δ = distance M α v u)
  (v_δ_u : relateSeq M δ v u) (v_F : ∀ f ∈ F, evaluate M v f) {α' : Program} {φ' : Formula}
  (α'_not_atomic : ¬α'.isAtomic) (precons : ∅ ⊆ L ∧ ∅ ⊆ R ∧ some (Sum.inr (~'⌊α'⌋AnyFormula.normal
    φ')) ⊆ O)
  (hC : C = applyLocalRule (LocalRule.loadedR (⌊α'⌋AnyFormula.normal φ') (LoadRule.dia'
    α'_not_atomic) rfl) (L, R, O))
  (next : ∀ Y, Y ∈ C → LocalTableau Y)
  (IH :
    ∀ (Y : Sequent) (a : Y ∈ C) {v w : W},
      (M, v) ⊨ Y →
        (M, w) ⊨ ~''(AnyFormula.normal φ) →
          ∀ (α : Program) (αs : List Program),
            relateSeq M (α :: αs) v w →
              (~''(AnyFormula.loaded (⌊α⌋AnyFormula.loadBoxes αs (AnyFormula.normal φ)))).inSide
                side Y →
                (Y.without (~''(AnyFormula.loaded (⌊α⌋AnyFormula.loadBoxes αs (AnyFormula.normal
                  φ))))).isFree →
                  ∃ Y_1 ∈ endNodesOf (next Y a),
                    (M, v) ⊨ Y_1 ∧
                      (Y_1.isFree ∨
                        ∃ F γ,
                          (~''(AnyFormula.loadBoxes γ (AnyFormula.normal φ))).inSide side Y_1 ∧
                            relateSeq M γ v w ∧
                              distanceList M v w γ = distanceList M v w (α :: αs) ∧
                                (M, v) ⊨ F ∧
                                  (F, γ) ∈ Dl (α :: αs) ∧
                                    (Y_1.without (~''(AnyFormula.loadBoxes γ (AnyFormula.normal
                                      φ)))).isFree)) :
  ∃ Y ∈ (Finset.image (fun x ↦ endNodesOf (next x.1 x.2)) C.attach).sup id,
    (M, v) ⊨ Y ∧
      (Y.isFree ∨
        ∃ F γ,
          (~''(AnyFormula.loadBoxes γ (AnyFormula.normal φ))).inSide side Y ∧
            relateSeq M γ v w ∧
              distanceList M v w γ = distanceList M v w (α :: αs) ∧
                (M, v) ⊨ F ∧
                  (F, γ) ∈ Dl (α :: αs) ∧
                    (Y.without (~''(AnyFormula.loadBoxes γ (AnyFormula.normal φ)))).isFree) := by
  -- The rule application has its own α' that must be α,
  -- also has its own φ' that must be φ, (this is new/easier here)
  -- and αs must be [], there is no more χ.
  have ⟨α_same, φ_same, αs_empty⟩ : α = α' ∧ φ = φ' ∧ αs = [] := by
    simp only [AnyNegFormula.inSide] at negLoad_in
    have := precons.2.2
    simp only [Option.some_subseteq] at this
    rw [← this] at negLoad_in
    cases side
    · subst this
      simp_all
    · simp only [Option.some.injEq, Sum.inr.injEq, NegLoadFormula.neg.injEq,
      LoadFormula.box.injEq] at negLoad_in
      rcases negLoad_in with ⟨α_same, φ_def⟩
      cases αs <;> simp_all
  -- It seems this is actually easier than the `dia` case, we can `subst` more here.
  subst α_same
  subst φ_same
  subst αs_empty
  simp only [relateSeq] at u_αs_w
  subst u_αs_w -- We now have u = w.
  -- Note: we now do `in_C` *after* distinguishing whether δ = [].
  simp only [Dl_singleton]
  cases δ
  case nil => -- δ is empty, so we should have a free result?
    simp only [relateSeq_nil] at v_δ_u v_F -- Here we have v = u.
    subst v_δ_u
    -- This F,δ pair is also used for one result in `C`:
    have in_C : (L, R ∪ (F.toFinset ∪ {~φ}), none) ∈ C := by
      clear IH next
      simp only [applyLocalRule, Finset.sdiff_empty, List.pdlToFinFinOpt,
        unfoldDiamondLoaded', YsetLoad', List.map_map] at hC
      rw [hC]
      simp only [Finset.union_singleton, Finset.union_insert, Finset.mem_image,
        List.mem_toFinset, List.mem_map, Function.comp_apply, Prod.exists, Prod.mk.injEq,
        ↓existsAndEq, and_true, Finset.union_empty, true_and]
      refine ⟨F, [], in_D, ?_, ?_⟩
      · simp
      · cases O <;> cases side
        all_goals
          simp only [relateSeq_singleton, Finset.empty_subset, Option.some_subseteq,
            reduceCtorEq, and_false, Option.some.injEq, true_and, AnyFormula.boxes_nil,
            Olf.change, Option.pdlOverwrite, AnyNegFormula.inSide, splitLast,
            Option.map_none] at *
        · subst hC; exfalso; aesop
        · rw [negLoad_in]; simp
    -- No IH needed because we reach a free node.
    clear IH
    -- We do not know `Y` yet because ltab may continue after `(L, R ∪ F ∪ {~φ}, none)`.
    -- So let's use localTableauTruth to find a free end node, similar to αs = [] case.
    have v_Z : (M, v) ⊨ (show Sequent from (L, R ∪ (F.toFinset ∪ {~φ}), none)) := by
      intro f f_in
      simp only [Sequent.toFinset, Finset.mem_union, List.mem_toFinset,
        Finset.mem_singleton, Option.map_none, Option.mem_toFinset, Option.mem_def,
        reduceCtorEq, or_false] at f_in
      rcases f_in with (f_in|f_in|f_in|rfl)
      · exact v_t f (Sequent.mem_toFinset_of_mem_left f_in)
      · exact v_t f (Sequent.mem_toFinset_of_mem_right f_in)
      · exact v_F _ f_in
      · exact w_nξ
    rcases (localTableauTruth (next _ in_C) M v).1 v_Z with ⟨Y, Y_in, v_Y⟩
    refine ⟨Y, mem_sup_endNodesOf _ in_C Y_in, ⟨v_Y, Or.inl ?_⟩⟩
    apply endNodesOf_free_are_free (next _ in_C) ?_ Y_in
    simp
  case cons d δs =>
    rw [@relateSeq_cons] at v_δ_u
    rcases v_δ_u with ⟨x, v_d_x, x_δs_u⟩
    let δ_β := match h : splitLast (d :: δs) with
      | some this => this
      | none => by exfalso; simp_all [splitLast]
    have split_def : splitLast (d :: δs) = some δ_β := by rfl
    -- This F,δ pair is also used for one result in `B`:
    have in_C : (L, R ∪ F.toFinset, some (Sum.inr (~'loadMulti δ_β.1 δ_β.2 φ))) ∈ C := by
      simp only [applyLocalRule, Finset.sdiff_empty, List.pdlToFinFinOpt,
        unfoldDiamondLoaded', YsetLoad', List.map_map] at hC
      rw [hC]
      simp only [Finset.mem_image, List.mem_toFinset, List.mem_map, Function.comp_apply,
        Prod.exists, Prod.mk.injEq, ↓existsAndEq, and_true, Finset.union_empty, true_and]
      use F, (d :: δs), in_D
      rw [split_def]
      simp
    -- Rest based on non-empty δ case in `dia` above; changed to work with `loadMulti`.
    -- A non-empty δ came from α, so we have not actually made the step to `u` yet.
    -- Again we prepare to use IH, but now for `d` and `δs` instead.
    specialize @IH _ in_C v u ?_ w_nξ d δs ?_ ?_ ?_
    · intro f f_in; clear IH next
      simp only [Sequent.toFinset, Finset.mem_union, List.mem_toFinset,
        Option.map_some, Sum.elim_inr, negUnload, unload_loadMulti,
        Option.mem_toFinset, Option.mem_def,
        Option.some.injEq] at f_in
      rcases f_in with (f_in|f_in|f_in)|f_def
      · exact v_t f (Sequent.mem_toFinset_of_mem_left f_in)
      · exact v_t f (Sequent.mem_toFinset_of_mem_right f_in)
      · exact v_F _ f_in
      · subst f_def
        rw [← @boxes_last, splitLast_undo_of_some split_def]
        simp only [evaluate, Formula.boxes_cons, evalBoxes, not_forall]
        refine ⟨x, v_d_x, ⟨u, x_δs_u, ?_⟩⟩
        exact w_nξ
    · simp_rw [relateSeq_cons]
      exact ⟨x, v_d_x, x_δs_u⟩
    · clear IH next
      cases side
      · exfalso
        simp_all [AnyNegFormula.inSide]
      · simp only [AnyNegFormula.inSide, Option.some.injEq,
        Sum.inr.injEq, NegLoadFormula.neg.injEq]
        exact loadMulti_of_splitLast_cons split_def
    · exact Sequent.without_loadMulti_isFree_of_splitLast_cons_inr split_def
    -- Now actually get the IH result.
    rcases IH with ⟨Y, Y_in, v_Y
                   , ( Y_free
                     | ⟨G, γs, in_Y, v_γs_w, dist_eq, v_G, in_Dl, Y_almost_free⟩ )⟩
    · refine ⟨Y, (mem_sup_endNodesOf _ in_C Y_in) , ⟨v_Y, Or.inl Y_free⟩⟩ -- free'n'easy
    · refine ⟨Y, (mem_sup_endNodesOf _ in_C Y_in) , ⟨v_Y, Or.inr ?_⟩⟩
      refine ⟨F, _, in_Y, v_γs_w, ?_, v_F, ?_, Y_almost_free⟩
      · rw [dist_eq,same_dist,distance_list_singleton]
      -- Now show that `d` is atomic, because it resulted from `H α`.
      have ⟨a, d_atom⟩ : ∃ a, d = ((·a) : Program) := by
        have := Dset_mem_sequence α in_D
        rcases this with inl | ⟨a, ⟨δ, list_prop⟩⟩
        · exfalso; simp_all
        · refine ⟨a, by simp_all⟩
      subst d_atom
      -- Hence `Dl (d :: ...)` does not actually unfold anything.
      simp only [Dl_atomic_cons, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
        or_false] at in_Dl
      rw [in_Dl.2]
      exact in_D

/-- Helper to deal with local tableau in `loadedDiamondPaths`.
Takes a *list* of programs and φ, i.e. we want access to all loaded boxes. -/
theorem localLoadedDiamondList (αs : List Program) {X : Sequent}
  (ltab : LocalTableau X)
  {W} {M : KripkeModel W} {v w : W}
  (v_αs_w : relateSeq M αs v w)
  (v_t : (M, v) ⊨ X)
  (φ : Formula) -- must not be loaded
  {side : Side}
  (negLoad_in : (~''(AnyFormula.loadBoxes αs φ)).inSide side X)
  (no_other_loading : (X.without (~''(AnyFormula.loadBoxes αs φ))).isFree)
  (w_nξ : (M, w) ⊨ ~''φ)
  : ∃ Y ∈ endNodesOf ltab, (M,v) ⊨ Y ∧
    (   Y.isFree -- means we left cluster
      ∨ ( ∃ (F : List Formula) (γ : List Program),
            ( (~''(AnyFormula.loadBoxes γ φ)).inSide side Y
            ∧ relateSeq M γ v w
            ∧ distanceList M v w γ = distanceList M v w αs
            ∧ (M,v) ⊨ F
            ∧ (F,γ) ∈ Dl αs -- "F,γ is a result from unfolding the αs"
            ∧ (Y.without (~''(AnyFormula.loadBoxes γ φ))).isFree
            )
        )
    ) := by
  cases αs
  case nil => -- We can pick any end node.
    simp_all only [relateSeq_nil, AnyFormula.boxes_nil, Sequent.without_normal_isFree_iff_isFree]
    rcases (localTableauTruth ltab M w).1 v_t with ⟨Y, Y_in, w_Y⟩
    refine ⟨Y, Y_in, w_Y, Or.inl ?_⟩
    apply endNodesOf_free_are_free ltab no_other_loading Y_in
  case cons α αs =>
    induction ltab generalizing α αs v w
    -- the generalizing `αs` here makes things really slow. use recursion instead?
    case byLocalRule X lra X_def next IH => -- X B lra next IH =>
      subst X_def
      -- Soundness and invertibility of the local rule:
      have locRulTru := @localRuleTruth lra W M
      rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, rule, C, hC, precons⟩
      simp only [AnyFormula.loadBoxes_cons, LocalRuleApp.X,
        endNodesOf.eq_1] at *
      -- We distinguish which rule was applied.
      cases rule
      -- Rules not affecting the loaded formula are easy by using the IH.
      case oneSidedL YS orule YS_def =>
        simp_all only [applyLocalRule, Finset.sdiff_empty, Finset.mem_image,
          exists_exists_and_eq_and, Finset.union_empty, Olf.change_old_none_none,
          forall_exists_index, forall_and_index, Finset.sup_image, Function.id_comp,
          Finset.mem_sup, Finset.mem_attach, true_and, Subtype.exists] -- uses locRulTru
        rcases v_t with ⟨res, res_in, v_⟩
        specialize IH _ res res_in rfl v_ w_nξ _ _ v_αs_w
          (by cases side <;> simp_all [AnyNegFormula.inSide])
          (by apply Sequent.without_loaded_in_side_isFree _ _ side; clear IH
              cases side
              all_goals
                simp only [AnyNegFormula.inSide]
                simp only [AnyNegFormula.inSide] at negLoad_in
                exact negLoad_in)
        rcases IH with ⟨Y, Y_in, v_Y⟩
        use Y
        simp_all only [and_self, and_true]
        use (L \ Lcond ∪ res, R, O)
        simp_all only [exists_prop, and_true]
        grind
      case oneSidedR YS orule YS_def => -- analogous to oneSidedL
        simp_all only [applyLocalRule, Finset.sdiff_empty, Finset.mem_image,
          exists_exists_and_eq_and, Finset.union_empty, Olf.change_old_none_none,
          forall_exists_index, forall_and_index, Finset.sup_image, Function.id_comp,
          Finset.mem_sup, Finset.mem_attach, true_and, Subtype.exists] -- uses locRulTru
        rcases v_t with ⟨res, res_in, v_⟩
        specialize IH _ res res_in rfl v_ w_nξ _ _ v_αs_w
          (by cases side <;> simp_all [AnyNegFormula.inSide])
          (by apply Sequent.without_loaded_in_side_isFree _ _ side; clear IH
              cases side
              all_goals
                simp only [AnyNegFormula.inSide]
                simp only [AnyNegFormula.inSide] at negLoad_in
                exact negLoad_in)
        rcases IH with ⟨Y, Y_in, v_Y⟩
        use Y
        simp_all only [and_self, and_true]
        use (L, R \ Rcond ∪ res, O)
        simp_all only [exists_prop, and_true]
        grind
      case LRnegL φ =>
        simp_all
      case LRnegR =>
        simp_all
      case loadedL outputs χ lrule resNodes_def =>
        subst resNodes_def
        -- Instead of localRuleTruth ...
        clear locRulTru
        -- Note: using `relateSeq_cons` here was too weak.
        -- We also need the info that `u` is picked minimally / witnesses the distance.
        have := exists_same_distance_of_relateSeq_cons v_αs_w
        rcases this with ⟨u, v_α_u, u_αs_w, u_picked_minimally⟩
        -- Previously here we used `existsDiamondDset` to imitate the relation `v_α_u`.
        -- have from_H := @existsDiamondDset W M α _ _ v_α_u
        -- Now we use `rel_existsD_dist` to also get the same distance.
        have from_H := rel_existsD_dist v_α_u
        rcases from_H with ⟨⟨F,δ⟩, in_D, v_F, same_dist⟩
        simp only [] at same_dist
        have v_δ_u : relateSeq M δ v u := by
          rw [← distance_list_iff_relate_Seq]
          rw [same_dist, dist_iff_rel]
          exact v_α_u
        simp only [conEval] at v_F
        cases lrule -- dia or dia' annoyance;-)
        case dia α' χ' α'_not_atomic =>
          exact localLoadedDiamondList_leftNested φ w_nξ α αs v_αs_w L R O C
            v_t negLoad_in no_other_loading u v_α_u u_αs_w u_picked_minimally F δ in_D
            same_dist v_δ_u v_F α'_not_atomic precons hC next IH
        case dia' α' φ' α'_not_atomic => -- only *somewhat* analogous to `dia` case.
          exact localLoadedDiamondList_leftNormal φ w_nξ α αs v_αs_w L R O C
            v_t negLoad_in no_other_loading u v_α_u u_αs_w u_picked_minimally F δ in_D
            same_dist v_δ_u v_F α'_not_atomic precons hC next IH
      case loadedR outputs χ lrule resNodes_def => -- COPY-PASTA from loadedL, modulo `side`
        subst resNodes_def
        -- Instead of localRuleTruth ...
        clear locRulTru
        -- Note: using `relateSeq_cons` here was too weak.
        -- We also need the info that `u` is picked minimally / witnesses the distance.
        have := exists_same_distance_of_relateSeq_cons v_αs_w
        rcases this with ⟨u, v_α_u, u_αs_w, u_picked_minimally⟩
        -- Previously here we used `existsDiamondDset` to imitate the relation `v_α_u`.
        -- have from_H := @existsDiamondDset W M α _ _ v_α_u
        -- Now we use `rel_existsD_dist` to also get the same distance.
        have from_H := rel_existsD_dist v_α_u
        rcases from_H with ⟨⟨F,δ⟩, in_D, v_F, same_dist⟩
        simp only [] at same_dist
        have v_δ_u : relateSeq M δ v u := by
          rw [← distance_list_iff_relate_Seq]
          rw [same_dist, dist_iff_rel]
          exact v_α_u
        simp only [conEval] at v_F
        cases lrule -- dia or dia' annoyance;-)
        case dia α' χ' α'_not_atomic =>
          exact localLoadedDiamondList_rightNested φ w_nξ α αs v_αs_w L R O C
            v_t negLoad_in no_other_loading u v_α_u u_αs_w u_picked_minimally F δ in_D
            same_dist v_δ_u v_F α'_not_atomic precons hC next IH
        case dia' α' φ' α'_not_atomic => -- only *somewhat* analogous to `dia` case.
          exact localLoadedDiamondList_rightNormal φ w_nξ α αs v_αs_w L R O C
            v_t negLoad_in no_other_loading u v_α_u u_αs_w u_picked_minimally F δ in_D
            same_dist v_δ_u v_F α'_not_atomic precons hC next IH
    case sim X X_isBasic =>
      clear no_other_loading
      -- If `X` is basic then `α` must be atomic.
      have : α.isAtomic := by
        refine Sequent.isAtomic_of_basic_of_negLoad_mem_wForms
          (ξ := AnyFormula.loadBoxes αs (AnyFormula.normal φ)) X_isBasic ?_
        rcases X with ⟨L,R,O⟩
        unfold AnyNegFormula.inSide at negLoad_in
        rw [Sequent.mem_wForms_negLoad_iff]
        cases side <;> simp_all
      rw [Program.isAtomic_iff] at this
      rcases this with ⟨a, α_def⟩
      subst α_def
      -- We can use X itself as the end node.
      refine ⟨X, ?_, v_t, Or.inr ⟨[], ·a :: αs, negLoad_in,  ?_,  ?_,  ?_⟩ ⟩ <;> simp_all only
        [AnyFormula.loadBoxes_cons,
        endNodesOf, Finset.mem_singleton, Dl_atomic_cons, List.mem_cons, List.not_mem_nil,
        or_false, true_and]
      exact ⟨by simp [vDash.SemImplies], Sequent.without_loaded_in_side_isFree X _ side negLoad_in⟩

end PDL
