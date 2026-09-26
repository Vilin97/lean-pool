/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import LeanPool.PDL.Local.Tableau

/-! # Interpolants preserved by local tableau rules -/

public section

namespace PDL

open HasSat

/-! ## Partition Interpolants -/

/-- The vocabulary and two inconsistency conditions defining a partial interpolant. -/
@[expose] def isPartInterpolant (X : Sequent) (θ : Formula) :=
  θ.voc ⊆ jvoc X ∧ (¬ satisfiable ({~θ} ∪ X.left) ∧ ¬ satisfiable ({θ} ∪ X.right))

/-- A formula equipped with the partial-interpolant conditions for a sequent. -/
def PartInterpolant (N : Sequent) := Subtype <| isPartInterpolant N

/-! ## Interpolants for local rules -/

lemma LoadRule.voc {ress} (lr : LoadRule (~'χ) ress) : lfovocFin ress ⊆ χ.voc := by
  intro x x_in
  unfold lfovocFin at x_in
  simp only [Finset.mem_sup, Finset.mem_union, Prod.exists] at x_in
  rcases x_in with ⟨fs, onlf, in_ress, x_in_V⟩
  cases lr
  case dia α χ notAtom =>
    have unfvoc := @unfoldDiamond_voc x α χ.unload
    rw [← unfoldDiamondLoaded_eq α χ] at unfvoc
    simp only [List.pdlToFinFinOpt, List.mem_toFinset, List.mem_map, Prod.mk.injEq,
      Prod.exists] at in_ress
    rcases in_ress with ⟨gs, o, in_ress, def_fs, def_onlf⟩
    subst def_fs def_onlf
    specialize @unfvoc (pairUnload (gs, o)) (by simp only [List.mem_map]; use (gs,o))
    rcases o with _ | ⟨⟨lf⟩⟩  <;> simp only [Finset.pdlFvoc, Vocab.fromFinset, Finset.sup_image,
      Function.id_comp, Finset.mem_sup, List.mem_toFinset, onlfvoc, Finset.notMem_empty, or_false,
      LoadFormula.voc, LoadFormula.unload, Formula.voc.eq_5, Finset.mem_union, NegLoadFormula.voc,
      negUnload, Formula.voc.eq_3] at *
    · rcases x_in_V with ⟨f, f_in_fs, x_in⟩
      specialize unfvoc f_in_fs
      aesop
    · simp [pairUnload] at unfvoc
      rcases x_in_V with ⟨f, f_in_fs, x_in⟩|_ <;> aesop
  case dia' α φ notAtom =>
    have unfvoc := @unfoldDiamond_voc x α φ
    rw [← unfoldDiamondLoaded'_eq α φ] at unfvoc
    simp only [List.pdlToFinFinOpt, List.mem_toFinset, List.mem_map, Prod.mk.injEq,
      Prod.exists] at in_ress
    rcases in_ress with ⟨gs, o, in_ress, def_fs, def_onlf⟩
    subst def_fs def_onlf
    specialize @unfvoc (pairUnload (gs, o)) (by simp only [List.mem_map]; use (gs,o))
    rcases o with _ | ⟨⟨lf⟩⟩  <;> simp only [Finset.pdlFvoc, Vocab.fromFinset, Finset.sup_image,
      Function.id_comp, Finset.mem_sup, List.mem_toFinset, onlfvoc, Finset.notMem_empty, or_false,
      LoadFormula.voc, LoadFormula.unload, Formula.voc.eq_5, Finset.mem_union, NegLoadFormula.voc,
      negUnload, Formula.voc.eq_3] at *
    · rcases x_in_V with ⟨f, f_in_fs, x_in⟩
      specialize unfvoc f_in_fs
      aesop
    · simp [pairUnload] at unfvoc
      rcases x_in_V with ⟨f, f_in_fs, x_in⟩|_ <;> aesop

theorem localRule_does_not_increase_vocab_L {Cond B}
    (rule : LocalRule Cond B) :
    ∀ res ∈ B, res.left.pdlFvoc ⊆ Cond.left.pdlFvoc := by
  rcases Cond with ⟨Lcond, Rcond, Ocond⟩
  intro res res_in_B x x_in_res
  cases rule
  case oneSidedL ress orule B_def =>
    subst B_def
    simp only [Finset.mem_image] at res_in_B
    rcases res_in_B with ⟨L, L_in, def_res⟩
    subst def_res
    simp only [Finset.pdlFvoc, Vocab.fromFinset, Sequent.left_eq, Olf.L_none, Finset.union_empty,
      Finset.sup_image, Function.id_comp, Finset.mem_sup] at *
    rcases x_in_res with ⟨ψ, ψ_in, x_in_voc_ψ⟩
    cases orule
    case nCo => aesop
    case box α φ α_notAt => have := unfoldBox_voc_fin L_in ψ_in x_in_voc_ψ; simp_all
    case dia => have := unfoldDiamond_voc_fin L_in ψ_in x_in_voc_ψ; simp_all
    all_goals aesop
  case loadedL ress χ lrule B_def =>
    subst B_def
    simp only [Finset.mem_image, Prod.exists] at res_in_B
    rcases res_in_B with ⟨L, lnf, in_ress, def_res⟩
    subst def_res
    have hsub := lrule.voc
    have goal_iff : x ∈ (Sequent.left (∅, ∅, some (Sum.inl (~'χ)))).pdlFvoc ↔ x ∈ χ.voc := by
      simp [Sequent.left, Olf.L]
    rw [goal_iff]
    apply hsub
    unfold lfovocFin
    simp only [Finset.mem_sup, Finset.mem_union, Prod.exists]
    refine ⟨L, lnf, in_ress, ?_⟩
    simp only [Sequent.left_eq, Finset.fvoc_union, Finset.mem_union] at x_in_res
    rcases x_in_res with h | h
    · exact Or.inl h
    · right
      rcases lnf with _ | ⟨lf⟩
      · simp [Olf.L] at h
      · simpa [Olf.L, onlfvoc] using h
  -- other cases are all trivial (as in Bml)
  all_goals
    aesop

theorem localRule_does_not_increase_vocab_R {Cond} (rule : LocalRule Cond B) :
    ∀ res ∈ B, res.right.pdlFvoc ⊆ Cond.right.pdlFvoc := by
  rcases Cond with ⟨Lcond, Rcond, Ocond⟩
  intro res res_in_B x x_in_res
  cases rule
  case oneSidedR ress orule B_def =>
    subst B_def
    simp only [Finset.mem_image] at res_in_B
    rcases res_in_B with ⟨L, L_in, def_res⟩
    subst def_res
    simp only [Finset.pdlFvoc, Vocab.fromFinset, Sequent.right_eq, Olf.R_none, Finset.union_empty,
      Finset.sup_image, Function.id_comp, Finset.mem_sup] at *
    rcases x_in_res with ⟨ψ, ψ_in, x_in_voc_ψ⟩
    cases orule
    case nCo => aesop
    case box α φ α_notAt => have := unfoldBox_voc_fin L_in ψ_in x_in_voc_ψ; simp_all
    case dia => have := unfoldDiamond_voc_fin L_in ψ_in x_in_voc_ψ; simp_all
    all_goals aesop
  case loadedR ress χ lrule B_def =>
    subst B_def
    simp only [Finset.mem_image, Prod.exists] at res_in_B
    rcases res_in_B with ⟨L, lnf, in_ress, def_res⟩
    subst def_res
    have hsub := lrule.voc
    have goal_iff : x ∈ (Sequent.right (∅, ∅, some (Sum.inr (~'χ)))).pdlFvoc ↔ x ∈ χ.voc := by
      simp [Sequent.right, Olf.R]
    rw [goal_iff]
    apply hsub
    unfold lfovocFin
    simp only [Finset.mem_sup, Finset.mem_union, Prod.exists]
    refine ⟨L, lnf, in_ress, ?_⟩
    simp only [Sequent.right_eq, Finset.fvoc_union, Finset.mem_union] at x_in_res
    rcases x_in_res with h | h
    · exact Or.inl h
    · right
      rcases lnf with _ | ⟨lf⟩
      · simp [Olf.R] at h
      · simpa [Olf.R, onlfvoc] using h
  -- other cases are all trivial (as in Bml)
  all_goals
    aesop

theorem localRuleApp_does_not_increase_jvoc (lra : LocalRuleApp) :
    ∀ Y ∈ lra.C, jvoc Y ⊆ jvoc lra.X := by
  match lra with
  | @LocalRuleApp.mk L R O Lcond Rcond Ocond ress lrule C hC preconditionProof =>
    subst hC
    rintro ⟨cL, cR, cO⟩ C_in
    simp only [applyLocalRule, Finset.mem_image] at C_in
    rcases C_in with ⟨⟨Lres, Rres, Ores⟩, res_in, def_c⟩
    simp only at def_c
    cases def_c
    have Lsub := localRule_does_not_increase_vocab_L lrule _ res_in
    have Rsub := localRule_does_not_increase_vocab_R lrule _ res_in
    simp only [Sequent.left_eq, Sequent.right_eq] at Lsub Rsub
    apply jvoc_sub_of_voc_sub
    · -- left
      have hcond : ∀ y ∈ (Lcond ∪ Ocond.L).pdlFvoc, y ∈ L.pdlFvoc ∨ y ∈ O.L.pdlFvoc := by
        intro y hy
        rw [Finset.fvoc_union, Finset.mem_union] at hy
        rcases hy with h | h
        · exact Or.inl (Finset.fvoc_mono preconditionProof.1 h)
        · exact Or.inr (Finset.fvoc_mono (Olf.L_subset_of_subset preconditionProof.2.2) h)
      have hres : ∀ y ∈ (Lres ∪ Ores.L).pdlFvoc, y ∈ L.pdlFvoc ∨ y ∈ O.L.pdlFvoc :=
        fun y hy => hcond y (Lsub hy)
      intro x x_in
      simp only [LocalRuleApp.X, Sequent.left_eq, Finset.fvoc_union,
        Finset.mem_union] at x_in ⊢
      rcases x_in with (h | h) | h
      · exact Or.inl (Finset.fvoc_mono Finset.sdiff_subset h)
      · exact hres x (by rw [Finset.fvoc_union, Finset.mem_union]; exact Or.inl h)
      · rcases Ores with _ | z
        · refine Or.inr (Finset.fvoc_mono ?_ h)
          simpa only [Olf.change, Option.pdlOverwrite] using Olf.L_sdiff_subset
        · rw [Olf.change_some] at h
          exact hres x (by rw [Finset.fvoc_union, Finset.mem_union]; exact Or.inr h)
    · -- right, analogous to the left
      have hcond : ∀ y ∈ (Rcond ∪ Ocond.R).pdlFvoc, y ∈ R.pdlFvoc ∨ y ∈ O.R.pdlFvoc := by
        intro y hy
        rw [Finset.fvoc_union, Finset.mem_union] at hy
        rcases hy with h | h
        · exact Or.inl (Finset.fvoc_mono preconditionProof.2.1 h)
        · exact Or.inr (Finset.fvoc_mono (Olf.R_subset_of_subset preconditionProof.2.2) h)
      have hres : ∀ y ∈ (Rres ∪ Ores.R).pdlFvoc, y ∈ R.pdlFvoc ∨ y ∈ O.R.pdlFvoc :=
        fun y hy => hcond y (Rsub hy)
      intro x x_in
      simp only [LocalRuleApp.X, Sequent.right_eq, Finset.fvoc_union,
        Finset.mem_union] at x_in ⊢
      rcases x_in with (h | h) | h
      · exact Or.inl (Finset.fvoc_mono Finset.sdiff_subset h)
      · exact hres x (by rw [Finset.fvoc_union, Finset.mem_union]; exact Or.inl h)
      · rcases Ores with _ | z
        · refine Or.inr (Finset.fvoc_mono ?_ h)
          simpa only [Olf.change, Option.pdlOverwrite] using Olf.R_sdiff_subset
        · rw [Olf.change_some] at h
          exact hres x (by rw [Finset.fvoc_union, Finset.mem_union]; exact Or.inr h)

/-- Vocabulary control depends only on the child interpolants and the rule's
vocabulary bound, independently of which side is loaded. -/
private theorem childInterpolant_voc {C : Finset Sequent} {X : Sequent}
    (subθs : ∀ c ∈ C, PartInterpolant c) (hC : ∀ Y ∈ C, jvoc Y ⊆ jvoc X)
    {φ : Formula}
    (hφ : φ ∈ (Finset.image (fun c ↦ (subθs c.1 c.2).1) C.attach).pdlSort) :
    φ.voc ⊆ jvoc X := by
  rw [Formula.mem_pdlSort] at hφ
  simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hφ
  rcases hφ with ⟨Y, hY, rfl⟩
  exact fun _ hn => hC Y hY ((subθs Y hY).prop.1 hn)

private theorem satisfiable_neg_dis_union {X I : Finset Formula}
    (h : satisfiable ({~ dis I.pdlSort} ∪ X)) :
    satisfiable (X ∪ I.image Formula.neg) := by
  rcases h with ⟨W, M, w, hw⟩
  refine ⟨W, M, w, ?_⟩
  have hdis : ¬ evaluate M w (dis I.pdlSort) := hw (~ dis I.pdlSort) (by simp)
  rw [disEval] at hdis
  push Not at hdis
  intro φ hφ
  rcases Finset.mem_union.mp hφ with hφ | hφ
  · exact hw φ (Finset.mem_union_right _ hφ)
  · rcases Finset.mem_image.mp hφ with ⟨θ, hθ, rfl⟩
    exact hdis θ (Formula.mem_pdlSort.mpr hθ)

private theorem satisfiable_con_union {X I : Finset Formula}
    (h : satisfiable ({con I.pdlSort} ∪ X)) : satisfiable (X ∪ I) := by
  rcases h with ⟨W, M, w, hw⟩
  refine ⟨W, M, w, ?_⟩
  have hcon : evaluate M w (con I.pdlSort) := hw _ (by simp)
  rw [conEval] at hcon
  intro φ hφ
  rcases Finset.mem_union.mp hφ with hφ | hφ
  · exact hw φ (Finset.mem_union_right _ hφ)
  · exact hcon φ (Formula.mem_pdlSort.mpr hφ)

/-- Maehara interpolation for a oneSidedL local rule. -/
theorem localInterpolantStep_oneSidedL (L R : Finset Formula) (o : Olf) (Lcond : Finset
  Formula)
  (ress_1 C : Finset Sequent) {ress : Finset (Finset Formula)} (orule : OneSidedLocalRule Lcond
    ress)
  (rule : LocalRule (Lcond, ∅, none) ress_1) (hC : C = applyLocalRule rule (L, R, o))
  (precondProof : Lcond ⊆ L ∧ ∅ ⊆ R ∧ none ⊆ o)
  (subθs : ∀ c ∈ C, PartInterpolant c)
  (YS_def : ress_1 = Finset.image (fun res ↦ (res, ∅, none)) ress)
  (def_rule : rule = LocalRule.oneSidedL orule YS_def) :
  let interSet := Finset.image (fun c ↦ (subθs c.1 c.2).1) C.attach;
  isPartInterpolant
    ({ L := L, R := R, O := o, Lcond := Lcond, ress := ress_1,
        lr := LocalRule.oneSidedL orule YS_def, C := C, hC := hC,
        preconditionProof := precondProof } : LocalRuleApp).X
    (dis interSet.pdlSort) := by
  intro interSet
  refine ⟨?_, ?_, ?_⟩
  · intro n n_in_inter
    rw [in_voc_dis] at n_in_inter
    rcases n_in_inter with ⟨φ, φ_in, n_in_voc_φ⟩
    exact childInterpolant_voc subθs (localRuleApp_does_not_increase_jvoc
      ({ L := L, R := R, O := o, Lcond := Lcond, ress := ress_1,
          lr := LocalRule.oneSidedL orule YS_def, C := C, hC := hC,
          preconditionProof := precondProof } : LocalRuleApp)) φ_in n_in_voc_φ
  · rintro nInter_L_sat
    have LI_sat := satisfiable_neg_dis_union nInter_L_sat
    have := oneSidedL_sat_down ⟨L,R,o⟩ precondProof.1 orule YS_def LI_sat
    rcases this with ⟨⟨L', R', o'⟩, c_in, W, M, w, w_⟩
    have c_in' : ((L', R', o') : Sequent) ∈ C := hC ▸ def_rule ▸ c_in
    refine (subθs ⟨L', R', o'⟩ c_in').2.2.1 ⟨W, M, w, ?_⟩ -- given IP property
    intro φ φ_in
    rcases Finset.mem_union.mp φ_in with h | h
    · rw [Finset.mem_singleton] at h
      subst h
      refine w_ _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, ?_, rfl⟩))
      simp only [interSet, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
      exact ⟨(L', R', o'), c_in', rfl⟩
    · exact w_ φ (Finset.mem_union_left _ h)
  · rintro ⟨W, M, w, w_⟩
    have w_dis : evaluate M w (dis interSet.pdlSort) := w_ _ (by simp)
    rw [disEval] at w_dis
    rcases w_dis with ⟨θi, θi_in, w_θi⟩
    rw [Formula.mem_pdlSort] at θi_in
    simp only [interSet, Finset.mem_image, Finset.mem_attach, true_and,
      Subtype.exists] at θi_in
    rcases θi_in with ⟨c, c_in, def_θi⟩
    have same_R : c.right = Sequent.right (L,R,o) :=
      @oneSidedL_preserves_right (L,R,o) _ precondProof.1 _ orule _ YS_def c (hC ▸ c_in)
    refine (subθs c (hC ▸ c_in)).2.2.2 ⟨W, M, w, ?_⟩ -- given IP property
    intro φ φ_in
    rcases Finset.mem_union.mp φ_in with h | h
    · rw [Finset.mem_singleton] at h
      subst h
      rw [def_θi]
      exact w_θi
    · rw [same_R] at h
      exact w_ φ (Finset.mem_union_right _ h)

/-- Maehara interpolation for a oneSidedR local rule. -/
theorem localInterpolantStep_oneSidedR (L R : Finset Formula) (o : Olf) (Rcond : Finset
  Formula)
  (ress_1 C : Finset Sequent) {ress : Finset (Finset Formula)} (orule : OneSidedLocalRule Rcond
    ress)
  (rule : LocalRule (∅, Rcond, none) ress_1) (hC : C = applyLocalRule rule (L, R, o))
  (precondProof : ∅ ⊆ L ∧ Rcond ⊆ R ∧ none ⊆ o)
  (subθs : ∀ c ∈ C, PartInterpolant c)
  (YS_def : ress_1 = Finset.image (fun res ↦ (∅, res, none)) ress)
  (def_rule : rule = LocalRule.oneSidedR orule YS_def) :
  let interSet := Finset.image (fun c ↦ (subθs c.1 c.2).1) C.attach;
  isPartInterpolant
    ({ L := L, R := R, O := o, Rcond := Rcond, ress := ress_1,
        lr := LocalRule.oneSidedR orule YS_def, C := C, hC := hC,
        preconditionProof := precondProof } : LocalRuleApp).X
    (con interSet.pdlSort) := by
  intro interSet
  refine ⟨?_, ?_, ?_⟩
  · intro n n_in_inter
    rw [in_voc_con] at n_in_inter
    rcases n_in_inter with ⟨φ, φ_in, n_in_voc_φ⟩
    exact childInterpolant_voc subθs (localRuleApp_does_not_increase_jvoc
      ({ L := L, R := R, O := o, Rcond := Rcond, ress := ress_1,
          lr := LocalRule.oneSidedR orule YS_def, C := C, hC := hC,
          preconditionProof := precondProof } : LocalRuleApp)) φ_in n_in_voc_φ
  · rintro ⟨W, M, w, w_⟩
    have w_ncon : ¬ evaluate M w (con interSet.pdlSort) :=
      w_ (~ con interSet.pdlSort) (by simp)
    rw [conEval] at w_ncon
    push Not at w_ncon
    rcases w_ncon with ⟨θi, θi_in, w_nθi⟩
    rw [Formula.mem_pdlSort] at θi_in
    simp only [interSet, Finset.mem_image, Finset.mem_attach, true_and,
      Subtype.exists] at θi_in
    rcases θi_in with ⟨c, c_in, def_θi⟩
    have same_L : c.left = Sequent.left (L,R,o) :=
      @oneSidedR_preserves_left (L,R,o) _ precondProof.2.1 _ orule _ YS_def c (hC ▸ c_in)
    refine (subθs c (hC ▸ c_in)).2.2.1 ⟨W, M, w, ?_⟩
    intro φ φ_in
    rcases Finset.mem_union.mp φ_in with h | h
    · rw [Finset.mem_singleton] at h
      subst h
      rw [def_θi]
      exact w_nθi
    · rw [same_L] at h
      exact w_ φ (Finset.mem_union_right _ h)
  · rintro inter_R_sat
    have RI_sat := satisfiable_con_union inter_R_sat
    have := oneSidedR_sat_down ⟨L,R,o⟩ precondProof.2.1 orule YS_def RI_sat
    rcases this with ⟨⟨L', R', o'⟩, c_in, W, M, w, w_⟩
    have c_in' : ((L', R', o') : Sequent) ∈ C := hC ▸ def_rule ▸ c_in
    refine (subθs ⟨L', R', o'⟩ c_in').2.2.2 ⟨W, M, w, ?_⟩ -- given IP property
    intro φ φ_in
    rcases Finset.mem_union.mp φ_in with h | h
    · rw [Finset.mem_singleton] at h
      subst h
      refine w_ _ (Finset.mem_union_right _ ?_)
      simp only [interSet, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
      exact ⟨(L', R', o'), c_in', rfl⟩
    · exact w_ φ (Finset.mem_union_left _ h)

/-- Maehara interpolation for a loadedL local rule. -/
theorem localInterpolantStep_loadedL (L R : Finset Formula) (o : Olf) (ress_1 C : Finset
  Sequent)
  {ress : Finset (Finset Formula × Option NegLoadFormula)} (χ : LoadFormula) (lrule : LoadRule
    (~'χ) ress)
  (rule : LocalRule (∅, ∅, some (Sum.inl (~'χ))) ress_1) (hC : C = applyLocalRule rule (L, R, o))
  (precondProof : ∅ ⊆ L ∧ ∅ ⊆ R ∧ some (Sum.inl (~'χ)) ⊆ o)
  (subθs : ∀ c ∈ C, PartInterpolant c)
  (YS_def :
    ress_1 =
      Finset.image
        (fun x ↦
          match x with
          | (X, o) => (X, ∅, Option.map Sum.inl o))
        ress)
  (def_rule : rule = LocalRule.loadedL χ lrule YS_def) :
  let interSet := Finset.image (fun c ↦ (subθs c.1 c.2).1) C.attach;
  Sequent.O (L, R, o) = some (Sum.inl (~'χ)) →
    isPartInterpolant
      ({ L := L, R := R, O := o, Ocond := some (Sum.inl (~'χ)), ress := ress_1, lr :=
        LocalRule.loadedL χ lrule YS_def,
          C := C, hC := hC, preconditionProof := precondProof } : LocalRuleApp).X
      (dis interSet.pdlSort) := by
  intro interSet O_is_some
  refine ⟨?_, ?_, ?_⟩
  · intro n n_in_inter
    rw [in_voc_dis] at n_in_inter
    rcases n_in_inter with ⟨φ, φ_in, n_in_voc_φ⟩
    exact childInterpolant_voc subθs (localRuleApp_does_not_increase_jvoc
      ({ L := L, R := R, O := o, Ocond := some (Sum.inl (~'χ)), ress := ress_1, lr :=
          LocalRule.loadedL χ lrule YS_def,
          C := C, hC := hC, preconditionProof := precondProof } : LocalRuleApp)) φ_in n_in_voc_φ
  · rintro nInter_L_sat
    have LI_sat := satisfiable_neg_dis_union nInter_L_sat
    have := loadedL_sat_down ⟨L,R,o⟩ χ O_is_some lrule YS_def LI_sat
    rcases this with ⟨⟨L', R', o'⟩, c_in, W, M, w, w_⟩
    have c_in' : ((L', R', o') : Sequent) ∈ C := hC ▸ def_rule ▸ c_in
    refine (subθs ⟨L', R', o'⟩ c_in').2.2.1 ⟨W, M, w, ?_⟩ -- given IP property
    intro φ φ_in
    rcases Finset.mem_union.mp φ_in with h | h
    · rw [Finset.mem_singleton] at h
      subst h
      refine w_ _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, ?_, rfl⟩))
      simp only [interSet, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
      exact ⟨(L', R', o'), c_in', rfl⟩
    · exact w_ φ (Finset.mem_union_left _ h)
  · rintro ⟨W, M, w, w_⟩
    have w_dis : evaluate M w (dis interSet.pdlSort) := w_ _ (by simp)
    rw [disEval] at w_dis
    rcases w_dis with ⟨θi, θi_in, w_θi⟩
    rw [Formula.mem_pdlSort] at θi_in
    simp only [interSet, Finset.mem_image, Finset.mem_attach, true_and,
      Subtype.exists] at θi_in
    rcases θi_in with ⟨c, c_in, def_θi⟩
    have same_R : c.right = Sequent.right (L,R,o) :=
      @loadedL_preserves_right ⟨L,R,o⟩ χ O_is_some ress lrule _ YS_def c (hC ▸ c_in)
    refine (subθs c c_in).2.2.2 ⟨W, M, w, ?_⟩ -- given IP property
    intro φ φ_in
    rcases Finset.mem_union.mp φ_in with h | h
    · rw [Finset.mem_singleton] at h
      subst h
      rw [def_θi]
      exact w_θi
    · rw [same_R] at h
      exact w_ φ (Finset.mem_union_right _ h)

/-- Maehara interpolation for a loadedR local rule. -/
theorem localInterpolantStep_loadedR (L R : Finset Formula) (o : Olf) (ress_1 C : Finset
  Sequent)
  {ress : Finset (Finset Formula × Option NegLoadFormula)} (χ : LoadFormula) (lrule : LoadRule
    (~'χ) ress)
  (rule : LocalRule (∅, ∅, some (Sum.inr (~'χ))) ress_1) (hC : C = applyLocalRule rule (L, R, o))
  (precondProof : ∅ ⊆ L ∧ ∅ ⊆ R ∧ some (Sum.inr (~'χ)) ⊆ o)
  (subθs : ∀ c ∈ C, PartInterpolant c)
  (YS_def :
    ress_1 =
      Finset.image
        (fun x ↦
          match x with
          | (X, o) => (∅, X, Option.map Sum.inr o))
        ress)
  (def_rule : rule = LocalRule.loadedR χ lrule YS_def) :
  let interSet := Finset.image (fun c ↦ (subθs c.1 c.2).1) C.attach;
  Sequent.O (L, R, o) = some (Sum.inr (~'χ)) →
    isPartInterpolant
      ({ L := L, R := R, O := o, Ocond := some (Sum.inr (~'χ)), ress := ress_1, lr :=
        LocalRule.loadedR χ lrule YS_def,
          C := C, hC := hC, preconditionProof := precondProof } : LocalRuleApp).X
      (con interSet.pdlSort) := by
  intro interSet O_is_some
  refine ⟨?_, ?_, ?_⟩
  · intro n n_in_inter
    rw [in_voc_con] at n_in_inter
    rcases n_in_inter with ⟨φ, φ_in, n_in_voc_φ⟩
    exact childInterpolant_voc subθs (localRuleApp_does_not_increase_jvoc
      ({ L := L, R := R, O := o, Ocond := some (Sum.inr (~'χ)), ress := ress_1, lr :=
          LocalRule.loadedR χ lrule YS_def,
          C := C, hC := hC, preconditionProof := precondProof } : LocalRuleApp)) φ_in n_in_voc_φ
  · rintro ⟨W, M, w, w_⟩
    have w_ncon : ¬ evaluate M w (con interSet.pdlSort) :=
      w_ (~ con interSet.pdlSort) (by simp)
    rw [conEval] at w_ncon
    push Not at w_ncon
    rcases w_ncon with ⟨θi, θi_in, w_nθi⟩
    rw [Formula.mem_pdlSort] at θi_in
    simp only [interSet, Finset.mem_image, Finset.mem_attach, true_and,
      Subtype.exists] at θi_in
    rcases θi_in with ⟨c, c_in, def_θi⟩
    have same_L : c.left = Sequent.left (L,R,o) :=
      @loadedR_preserves_left (L,R,o) χ O_is_some ress lrule _ YS_def c (hC ▸ c_in)
    refine (subθs c c_in).2.2.1 ⟨W, M, w, ?_⟩
    intro φ φ_in
    rcases Finset.mem_union.mp φ_in with h | h
    · rw [Finset.mem_singleton] at h
      subst h
      rw [def_θi]
      exact w_nθi
    · rw [same_L] at h
      exact w_ φ (Finset.mem_union_right _ h)
  · rintro inter_R_sat
    have RI_sat := satisfiable_con_union inter_R_sat
    have := loadedR_sat_down ⟨L,R,o⟩ χ O_is_some lrule YS_def RI_sat
    rcases this with ⟨⟨L', R', o'⟩, c_in, W, M, w, w_⟩
    have c_in' : ((L', R', o') : Sequent) ∈ C := hC ▸ def_rule ▸ c_in
    refine (subθs ⟨L', R', o'⟩ c_in').2.2.2 ⟨W, M, w, ?_⟩ -- given IP property
    intro φ φ_in
    rcases Finset.mem_union.mp φ_in with h | h
    · rw [Finset.mem_singleton] at h
      subst h
      refine w_ _ (Finset.mem_union_right _ ?_)
      simp only [interSet, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
      exact ⟨(L', R', o'), c_in', rfl⟩
    · exact w_ φ (Finset.mem_union_left _ h)

/-- Maehara's method for single-step *local* rule applications.
This covers easy cases without any loaded path repeats.
We do *not* use `localRuleTruth` to prove this,
but the more specific lemmas `oneSidedL_sat_down` and `oneSidedL_sat_down`. -/
def localInterpolantStep (lra : LocalRuleApp)
    (subθs : ∀ c ∈ lra.C, PartInterpolant c)
    : PartInterpolant lra.X := by
  -- UNPACKING TERMS
  rcases lra with ⟨L, R, o, Lcond, Rcond, Ocond, ress, rule, C, hC, precondProof⟩
  -- DISTINCTION ON LOCALRULE USED
  cases def_rule : rule
  case oneSidedL ress orule YS_def => -- rule applied in first component L
    let interSet : Finset Formula := C.attach.image <| fun c => (subθs c.1 c.2).1
    exact ⟨dis interSet.pdlSort, localInterpolantStep_oneSidedL
      L R o _ _ C orule rule hC precondProof subθs YS_def def_rule⟩
  case oneSidedR ress orule YS_def => -- rule applied in second component R
    -- Only somewhat analogous to oneSidedL. Part 2 and 3 are flipped around in a way.
    let interSet : Finset Formula := C.attach.image <| fun c => (subθs c.1 c.2).1
    exact ⟨con interSet.pdlSort, localInterpolantStep_oneSidedR
      L R o _ _ C orule rule hC precondProof subθs YS_def def_rule⟩
  case LRnegL φ =>
    use φ
    simp only [LocalRuleApp.X]
    refine ⟨?_, ?_, ?_⟩
    · intro n n_in_φ
      refine Finset.mem_inter.mpr ⟨?_, ?_⟩
      · exact Finset.mem_fvoc.mpr
          ⟨φ, Finset.mem_union_left _ (precondProof.1 (Finset.mem_singleton_self φ)), n_in_φ⟩
      · exact Finset.mem_fvoc.mpr
          ⟨~φ, Finset.mem_union_left _ (precondProof.2.1 (Finset.mem_singleton_self _)), n_in_φ⟩
    · rintro ⟨W, M, w, w_⟩
      have h1 : evaluate M w (~φ) :=
        w_ (~φ) (Finset.mem_union_left _ (Finset.mem_singleton_self _))
      have h2 : evaluate M w φ :=
        w_ φ (Finset.mem_union_right _
          (Finset.mem_union_left _ (precondProof.1 (Finset.mem_singleton_self φ))))
      simp only [evaluate] at h1
      exact h1 h2
    · rintro ⟨W, M, w, w_⟩
      have h1 : evaluate M w φ :=
        w_ φ (Finset.mem_union_left _ (Finset.mem_singleton_self _))
      have h2 : evaluate M w (~φ) :=
        w_ (~φ) (Finset.mem_union_right _
          (Finset.mem_union_left _ (precondProof.2.1 (Finset.mem_singleton_self _))))
      simp only [evaluate] at h2
      exact h2 h1
  case LRnegR φ =>
    use ~φ
    simp only [LocalRuleApp.X]
    refine ⟨?_, ?_, ?_⟩
    · intro n n_in_φ
      simp only [Formula.voc] at n_in_φ
      refine Finset.mem_inter.mpr ⟨?_, ?_⟩
      · exact Finset.mem_fvoc.mpr
          ⟨~φ, Finset.mem_union_left _ (precondProof.1 (Finset.mem_singleton_self _)), n_in_φ⟩
      · exact Finset.mem_fvoc.mpr
          ⟨φ, Finset.mem_union_left _ (precondProof.2.1 (Finset.mem_singleton_self φ)), n_in_φ⟩
    · rintro ⟨W, M, w, w_⟩
      have h1 : evaluate M w (~~φ) :=
        w_ (~~φ) (Finset.mem_union_left _ (Finset.mem_singleton_self _))
      have h2 : evaluate M w (~φ) :=
        w_ (~φ) (Finset.mem_union_right _
          (Finset.mem_union_left _ (precondProof.1 (Finset.mem_singleton_self _))))
      simp only [evaluate] at h1 h2
      exact h1 h2
    · rintro ⟨W, M, w, w_⟩
      have h1 : evaluate M w (~φ) :=
        w_ (~φ) (Finset.mem_union_left _ (Finset.mem_singleton_self _))
      have h2 : evaluate M w φ :=
        w_ φ (Finset.mem_union_right _
          (Finset.mem_union_left _ (precondProof.2.1 (Finset.mem_singleton_self φ))))
      simp only [evaluate] at h1
      exact h1 h2
  case loadedL ress χ lrule YS_def =>
    -- similar to oneSidedL case
    let interSet : Finset Formula := C.attach.image <| fun c => (subθs c.1 c.2).1
    have O_is_some : Sequent.O (L, R, o) = some (Sum.inl (~'χ)) := by
        have := precondProof.2.2; simp at this; simp only [Sequent.O_eq]; exact this.symm
    exact ⟨dis interSet.pdlSort, localInterpolantStep_loadedL
      L R o _ C χ lrule rule hC precondProof subθs YS_def def_rule O_is_some⟩
  case loadedR ress χ lrule YS_def =>
    -- based on oneSidedR case
    let interSet : Finset Formula := C.attach.image <| fun c => (subθs c.1 c.2).1
    have O_is_some : Sequent.O (L, R, o) = some (Sum.inr (~'χ)) := by
      have := precondProof.2.2; simp at this; simp only [Sequent.O_eq]; exact this.symm
    exact ⟨con interSet.pdlSort, localInterpolantStep_loadedR
      L R o _ C χ lrule rule hC precondProof subθs YS_def def_rule O_is_some⟩
/-! ## Interpolants for Local Tableau -/

/-- Propagate interpolants from the end nodes through a local tableau. -/
def LocalTableau.interpolant (ltX : LocalTableau X)
    (endθs : ∀ Y ∈ endNodesOf ltX, PartInterpolant Y)
    : PartInterpolant X := by
  cases ltX
  case byLocalRule lra nexts X_def =>
    subst X_def
    apply localInterpolantStep lra
    intro Y Y_in
    have IH := LocalTableau.interpolant (nexts Y Y_in)
    exact IH (fun Z Z_in_end => endθs _ (endNodeOfChild_to_endNode lra nexts rfl Y_in Z_in_end))
  case sim Xbas =>
    apply endθs X
    simp [endNodesOf]

end PDL
