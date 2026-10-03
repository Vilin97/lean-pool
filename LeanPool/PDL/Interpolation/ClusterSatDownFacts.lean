/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import LeanPool.PDL.Interpolation.Uniformity

/-! # The facts about a proper cluster used for Lemma 10.7

This file proves the four fields of `LoadedCluster.SatDownFacts` from `Pdl.ClusterSatDown`,
i.e. everything that the proof of Lemma 10.7 assumes about the cluster `C` and the steps
`stepOf Δ` of its quasi-tableau:

* `rightLoaded`: all `Δ ∈ Λ₂[C]` are loaded on the right (Lemma 9.4 (a)),
* `stepLT`: at a non-basic `Δ ∈ Λ₂[C]` the successors are strictly smaller in the
  Dershowitz-Manna ordering `ltSequent` used for the termination of local tableaux,
* `basicStep`: the modal step at a basic `Δ ∈ Λ₂[C]` (Lemma 9.7 (e)),
* `nonBasicStep`: the local step at a non-basic `Δ ∈ Λ₂[C]`, with the witness distance
  preserved — the local invertibility of the rules together with Lemma 10.5 (h).

The main result is `LoadedCluster.satDownFacts`. Its only hypothesis is Lemma 9.7 (d),
i.e. that `C^R_Δ` is non-empty for `Δ ∈ Λ₂[C]`, which in `Pdl.ClusterInterpolation` is
`LoadedCluster.exists_right_of_proper`.

We import `Pdl.Uniformity` and not `Pdl.ClusterInterpolation`, because the latter is where
`LoadedCluster.satDownFacts` gets used; the helper lemmas about right rules that we need
are the copies in the `Uniformity` namespace.
-/

public section

namespace PDL

/-! ## Splitting a boxed loaded formula -/

/-- Prefixing a loaded formula with boxes prefixes its `split`. -/
lemma LoadFormula.boxes_split (δ : List Program) (χ : LoadFormula) :
    (⌊⌊δ⌋⌋χ).split = (δ ++ χ.split.1, χ.split.2) := by
  induction δ with
  | nil => simp [LoadFormula.boxes_nil]
  | cons α δ ih => rw [LoadFormula.boxes_cons]; simp [ih]

/-! ## Right rules applied to the right component only

A local rule that acts on the right component can also be applied to the sequent with an
empty left component. This is `LocalRuleApp.toContext` from `Pdl.Uniformity`, and it lets
us transfer both the decrease in the Dershowitz-Manna ordering and the local invertibility
from the whole sequent to its right component. -/

namespace LocalRuleApp

/-- The results of a local rule acting on the right have an empty left component. -/
lemma left_nil_of_mem_ress {lra : LocalRuleApp} (h : lra.isRightRule) :
    ∀ Z ∈ lra.ress, Z.1 = ∅ := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  simp only at h ⊢
  cases lr
  case oneSidedR ress' orule YS_def =>
    subst YS_def
    rintro Z hZ
    simp only [Finset.mem_image] at hZ
    obtain ⟨res, -, rfl⟩ := hZ
    rfl
  case loadedR χ lrule YS_def =>
    subst YS_def
    rintro Z hZ
    simp only [Finset.mem_image] at hZ
    obtain ⟨⟨F, o⟩, -, rfl⟩ := hZ
    rfl
  all_goals
    simp [LocalRuleApp.isRightRule, LocalRule.isRightRule] at h

/-- If the premise of a right rule has an empty left component then so have all
conclusions. -/
lemma C_left_nil {lra : LocalRuleApp} (h : lra.isRightRule) (hL : lra.L = ∅) :
    ∀ Y ∈ lra.C, Y.1 = ∅ := by
  intro Y hY
  rw [lra.hC] at hY
  simp only [applyLocalRule, Finset.mem_image] at hY
  obtain ⟨⟨Ln, Rn, On⟩, hmem, rfl⟩ := hY
  have hn := left_nil_of_mem_ress h _ hmem
  simp only at hn
  simp [hL, hn]

/-- The rule application `lra`, applied to the right component of its premise only. -/
def rightOnlyApp (lra : LocalRuleApp) : LocalRuleApp :=
  lra.toContext lra.X.rightOnly

@[simp]
lemma rightOnlyApp_isRightRule (lra : LocalRuleApp) :
    lra.rightOnlyApp.isRightRule = lra.isRightRule :=
  lra.toContext_isRightRule _

lemma rightOnlyApp_X {lra : LocalRuleApp} (h : lra.isRightRule) :
    lra.rightOnlyApp.X = lra.X.rightOnly :=
  lra.toContext_rightOnly_X rfl h

lemma rightOnlyApp_C {lra : LocalRuleApp} (h : lra.isRightRule) :
    lra.rightOnlyApp.C = lra.C.image Sequent.rightOnly := by
  have hr : lra.rightOnlyApp.isRightRule := by simpa [rightOnlyApp] using h
  have hX := rightOnlyApp_X h
  have h1 : lra.rightOnlyApp.C.image Sequent.rightOnly = lra.C.image Sequent.rightOnly :=
    Uniformity.map_rightOnly_C_eq (lra.toContext_sameRuleAs _) (by rw [hX]; rfl)
  rw [← h1]
  have hL : lra.rightOnlyApp.L = ∅ := congrArg (fun Y => Y.1) hX
  refine ((Finset.image_congr ?_).trans (Finset.image_id)).symm
  intro Y hY
  have hY1 := C_left_nil hr hL Y hY
  rcases Y with ⟨L, R, O⟩
  simp only at hY1
  simp [Sequent.rightOnly, hY1]

/-- The right components of the conclusions of a right rule are strictly smaller than the
right component of the premise, in the Dershowitz-Manna ordering. -/
lemma rightOnly_lt_Sequent {lra : LocalRuleApp} (h : lra.isRightRule) :
    ∀ Y ∈ lra.C, ltSequent Y.rightOnly lra.X.rightOnly := by
  intro Y hY
  have hdm := localRuleApp.decreases_DM lra.rightOnlyApp Y.rightOnly
    (by rw [rightOnlyApp_C h]; exact Finset.mem_image_of_mem _ hY)
  rwa [rightOnlyApp_X h] at hdm

end LocalRuleApp

/-! ## Satisfaction of a sequent with an empty left component -/

lemma models_iff_right {W : Type} {M : KripkeModel W} {w : W} {X : Sequent}
    (hL : X.left = ∅) : (M, w) ⊨ X ↔ ∀ φ ∈ X.right, evaluate M w φ := by
  rcases X with ⟨L, R, O⟩
  simp only [Sequent.left_eq, Finset.union_eq_empty] at hL
  obtain ⟨rfl, hO⟩ := hL
  simp only [vDash.SemImplies, Sequent.right_eq, Finset.mem_union]
  rcases O with _ | (o | o) <;>
    simp only [Olf.L, Sequent.toFinset, Finset.empty_union, Option.map_none, Option.toFinset_none,
      Finset.union_empty, Olf.R, Finset.notMem_empty, or_false, Finset.singleton_ne_empty,
      Option.map_some, Sum.elim_inr, negUnload, Option.toFinset_some, Finset.union_singleton,
      Finset.mem_insert, forall_eq_or_imp, evaluate, Finset.mem_singleton] at hO ⊢
  constructor
  · rintro ⟨h1, h2⟩ φ (hφ | rfl)
    · exact h2 φ hφ
    · exact h1
  · intro h
    exact ⟨h _ (Or.inr rfl), fun a ha => h a (Or.inl ha)⟩

/-! ## The local step, with the witness distance

This is the heart of the case `k(x) = 3` with `Δ_x` not basic in the proof of Lemma 10.7:
when a right local rule is applied to a sequent that holds at `v`, one of the conclusions
holds at `v` *with the same witness distance*. If the rule acts on an unloaded formula then
the loaded formula, and hence the witness distance, is unchanged. If it acts on the loaded
formula then the rule is `(◇)₂` and the claim is Lemma 10.5 (h),
`existsD_of_true_diamond`. -/

/-- The witness distance, computed from the split of the loaded formula. -/
lemma witDist_eq_of_loadedSplit {W : Type} {M : KripkeModel W} {v : W} {Δ : Sequent}
    {γ : List Program} {ψ : Formula} (h : Δ.loadedSplit = (γ, ψ)) :
    witDist M v Δ = ⨅ w : {w : W // evaluate M w (~ψ)}, distanceList M v w γ := by
  unfold witDist Sequent.loadedFma Sequent.loadedProgs
  rw [h]

lemma LocalRuleApp.rightRule_sat_witDist {lra : LocalRuleApp} (hr : lra.isRightRule)
    {W : Type} {M : KripkeModel W} {v : W}
    (hv : ∀ φ ∈ lra.X.right, evaluate M v φ) :
    ∃ Y ∈ lra.C, (∀ φ ∈ Y.right, evaluate M v φ) ∧ witDist M v Y = witDist M v lra.X := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  simp only [LocalRuleApp.X, Sequent.right_eq] at hv hr ⊢
  cases lr
  case oneSidedR ress' orule YS_def =>
    -- An unloaded rule: the loaded formula, and hence the witness distance, is unchanged,
    -- and one of the conclusions holds at `v` by the invertibility of the rule.
    subst YS_def
    subst hC
    have hcon : evaluate M v (con Rcond.pdlSort) :=
      conEval.mpr (fun f hf =>
        hv f (Finset.mem_union_left _ (pre.2.1 (Formula.mem_pdlSort.mp hf))))
    have hdis := (oneSidedLocalRuleTruth orule W M v).mp hcon
    rw [Finset.disconEval] at hdis
    obtain ⟨res, hres, hresv⟩ := hdis
    refine ⟨(L \ ∅ ∪ ∅, R \ Rcond ∪ res, Olf.change O none none), ?_, ?_, ?_⟩
    · simp only [applyLocalRule, Finset.image_image, Finset.mem_image, Function.comp_apply]
      exact ⟨res, hres, rfl⟩
    · intro f hf
      simp only [Sequent.right_eq, Finset.mem_union, Olf.change_old_none_none] at hf
      rcases hf with (hf | hf) | hf
      · exact hv f (Finset.mem_union_left _ (Finset.sdiff_subset hf))
      · exact hresv f hf
      · exact hv f (Finset.mem_union_right _ hf)
    · rw [Olf.change_old_none_none]
      exact witDist_congr (by rcases O with _ | (o | o) <;> rfl)
  case loadedR χ lrule YS_def =>
    -- The loaded diamond rule: this is Lemma 10.5 (h).
    subst YS_def
    subst hC
    have hO : some (Sum.inr (~'χ)) = O := Option.some_subseteq.mp pre.2.2
    subst hO
    have hχ : evaluate M v (~χ.unload) := hv _ (by simp)
    rw [LoadFormula.unload_eq_boxes_split] at hχ
    cases lrule
    case dia α χ' notAtom =>
      simp only [LoadFormula.split, AnyFormula.split] at hχ
      obtain ⟨⟨F, δ⟩, hFD, hFv, hbox, hdist⟩ :=
        existsD_of_true_diamond α χ'.split.1 χ'.split.2 hχ
      simp only at hFv hbox hdist
      refine ⟨(L \ ∅ ∪ ∅, R \ ∅ ∪ F.toFinset, some (Sum.inr (~'(⌊⌊δ⌋⌋χ')))), ?_, ?_, ?_⟩
      · have hmem : (F.toFinset, (some (~'(⌊⌊δ⌋⌋χ')) : Option NegLoadFormula))
            ∈ (unfoldDiamondLoaded α χ').pdlToFinFinOpt := by
          simp only [List.pdlToFinFinOpt, List.mem_toFinset, unfoldDiamondLoaded]
          refine List.mem_map.mpr ⟨(F, some (~'(⌊⌊δ⌋⌋χ'))), ?_, rfl⟩
          exact List.mem_map.mpr ⟨(F, δ), hFD, rfl⟩
        simp only [applyLocalRule]
        refine Finset.mem_image.mpr
          ⟨(∅, F.toFinset, some (Sum.inr (~'(⌊⌊δ⌋⌋χ')))), ?_, ?_⟩
        · exact Finset.mem_image.mpr ⟨_, hmem, rfl⟩
        · simp [Olf.change]
      · intro f hf
        simp only [Sequent.right_eq, Finset.mem_union, Olf.R_inr, Finset.mem_singleton,
          List.mem_toFinset] at hf
        rcases hf with (hf | hf) | hf
        · exact hv f (Finset.mem_union_left _ (Finset.sdiff_subset hf))
        · exact conEval.mp hFv f hf
        · subst hf
          rw [LoadFormula.unload_eq_boxes_split, LoadFormula.boxes_split, boxes_append]
          exact hbox
      · rw [witDist_eq_of_loadedSplit (γ := δ ++ χ'.split.1) (ψ := χ'.split.2)
            (by simp [Sequent.loadedSplit, LoadFormula.boxes_split]),
          witDist_eq_of_loadedSplit (γ := α :: χ'.split.1) (ψ := χ'.split.2)
            (by simp [Sequent.loadedSplit])]
        exact hdist
    case dia' α φ notAtom =>
      simp only [LoadFormula.split, AnyFormula.split] at hχ
      obtain ⟨⟨F, δ⟩, hFD, hFv, hbox, hdist⟩ := existsD_of_true_diamond α [] φ hχ
      simp only [Formula.boxes_nil, List.append_nil] at hFv hbox hdist
      rcases hsl : splitLast δ with _ | ⟨δ0, β⟩
      · -- The rule unloads: the conclusion is free and both distances are `0`.
        have hδ : δ = [] := by
          rcases δ with _ | ⟨x, xs⟩
          · rfl
          · simp [splitLast] at hsl
        subst hδ
        have hφ : evaluate M v (~φ) := by simpa using hbox
        refine ⟨(L \ ∅ ∪ ∅, R \ ∅ ∪ (F ∪ [~φ]).toFinset, none), ?_, ?_, ?_⟩
        · have hmem : ((F ∪ [~φ]).toFinset, (none : Option NegLoadFormula))
              ∈ (unfoldDiamondLoaded' α φ).pdlToFinFinOpt := by
            simp only [List.pdlToFinFinOpt, List.mem_toFinset, unfoldDiamondLoaded']
            refine List.mem_map.mpr ⟨(F ∪ [~φ], none), ?_, rfl⟩
            exact List.mem_map.mpr ⟨(F, []), hFD, by simp [YsetLoad']⟩
          simp only [applyLocalRule]
          refine Finset.mem_image.mpr
            ⟨(∅, (F ∪ [~φ]).toFinset, none), ?_, ?_⟩
          · exact Finset.mem_image.mpr ⟨_, hmem, rfl⟩
          · simp [Olf.change]
        · intro f hf
          simp only [Sequent.right_eq, Finset.mem_union, Olf.R_none, Finset.union_empty,
            List.mem_toFinset, List.mem_union_iff, List.mem_singleton] at hf
          rcases hf with hf | (hf | hf)
          · exact hv f (Finset.mem_union_left _ (Finset.sdiff_subset hf))
          · exact conEval.mp hFv f hf
          · exact hf ▸ hφ
        · rw [witDist_eq_of_loadedSplit (γ := ([] : List Program)) (ψ := (⊥ : Formula))
              (by simp [Sequent.loadedSplit]),
            witDist_eq_of_loadedSplit (γ := [α]) (ψ := φ) (by simp [Sequent.loadedSplit])]
          rw [← hdist]
          refine le_antisymm ?_ zero_le |>.trans (le_antisymm zero_le ?_)
          · exact le_of_le_of_eq (iInf_le _ (⟨v, by simp⟩ :
              {w : W // evaluate M w (~(⊥ : Formula))})) distance_list_nil_self
          · exact le_of_le_of_eq (iInf_le _ (⟨v, hφ⟩ : {w : W // evaluate M w (~φ)}))
              distance_list_nil_self
      · have hδ : δ0 ++ [β] = δ := splitLast_undo_of_some hsl
        refine ⟨(L \ ∅ ∪ ∅, R \ ∅ ∪ F.toFinset, some (Sum.inr (~'(loadMulti δ0 β φ)))),
          ?_, ?_, ?_⟩
        · have hmem : (F.toFinset, (some (~'(loadMulti δ0 β φ)) : Option NegLoadFormula))
              ∈ (unfoldDiamondLoaded' α φ).pdlToFinFinOpt := by
            simp only [List.pdlToFinFinOpt, List.mem_toFinset, unfoldDiamondLoaded']
            refine List.mem_map.mpr ⟨(F, some (~'(loadMulti δ0 β φ))), ?_, rfl⟩
            exact List.mem_map.mpr ⟨(F, δ), hFD, by simp [YsetLoad', hsl]⟩
          simp only [applyLocalRule]
          refine Finset.mem_image.mpr
            ⟨(∅, F.toFinset, some (Sum.inr (~'(loadMulti δ0 β φ)))), ?_, ?_⟩
          · exact Finset.mem_image.mpr ⟨_, hmem, rfl⟩
          · simp [Olf.change]
        · intro f hf
          simp only [Sequent.right_eq, Finset.mem_union, Olf.R_inr, Finset.mem_singleton,
            List.mem_toFinset] at hf
          rcases hf with (hf | hf) | hf
          · exact hv f (Finset.mem_union_left _ (Finset.sdiff_subset hf))
          · exact conEval.mp hFv f hf
          · subst hf
            rw [unload_loadMulti]
            rw [← hδ, boxes_append] at hbox
            simpa using hbox
        · rw [witDist_eq_of_loadedSplit (γ := δ0 ++ [β]) (ψ := φ)
              (by simp [Sequent.loadedSplit, loadMulti_split]),
            witDist_eq_of_loadedSplit (γ := [α]) (ψ := φ) (by simp [Sequent.loadedSplit])]
          rw [hδ]
          exact hdist
  all_goals simp [LocalRuleApp.isRightRule, LocalRule.isRightRule] at hr

/-! ## The four fields -/

namespace LoadedCluster

variable {X : Sequent} {tab : Tableau .nil X}

/-- Every label in `Λ₂[C]` is loaded on the right, i.e. Lemma 9.4 (a). -/
lemma isRightLoaded_of_mem_lambdaTwo (C : LoadedCluster tab) {Δ : Sequent}
    (hΔ : Δ ∈ C.lambdaTwo) : Δ.isRightLoaded := by
  simp only [lambdaTwo, Finset.mem_image, List.mem_toFinset] at hΔ
  obtain ⟨f, hf, rfl⟩ := hΔ
  have h := Uniformity.isRight_of_memFine C ((C.mem_fineCL f).mp hf)
  rcases hh : f.label.2.2 with _ | (o | o) <;> rw [hh] at h <;> simp at h
  exact ⟨o, by simp [Sequent.O, Sequent.rightOnly, hh]⟩

/-- If a right rule is applied at some node with right component `Δ`, then the steps
`stepOf Δ` are the right components of the conclusions of the local rule applied there.

Note that `stepOf` is a list while `LocalRuleApp.C` is a `Finset`, so we compare with
`lra.C.toList`, matching `FinePathIn.lraOpt_spec`. -/
lemma exists_lra_stepOf (C : LoadedCluster tab) {Δ : Sequent}
    (hne : C.nodesWithFineRight Δ ≠ []) (hb : ¬ Δ.basic) :
    ∃ lra : LocalRuleApp, lra.isRightRule ∧ lra.X.rightOnly = Δ ∧
      C.stepOf Δ = lra.C.image Sequent.rightOnly := by
  unfold stepOf
  cases hh : (C.nodesWithFineRight Δ).head? with
  | none => exact absurd (List.head?_eq_none_iff.mp hh) hne
  | some f =>
    have hf := List.mem_of_mem_head? hh
    simp only [nodesWithFineRight, nodesWithFine, List.mem_filter, decide_eq_true_eq] at hf
    obtain ⟨⟨hf_CL, hf_lab⟩, hf_right⟩ := hf
    have hfb : ¬ f.label.basic := fun h => hb (hf_lab ▸ Uniformity.basic_rightOnly h)
    obtain ⟨lra, hlra, hright⟩ :=
      (Uniformity.lra_or_basic_of_usesRightRule f hf_right).resolve_right hfb
    obtain ⟨hX, hC⟩ := f.lraOpt_spec hlra
    refine ⟨lra, hright, by rw [← hX, hf_lab], ?_⟩
    rw [← hC, Finset.image_image]
    rfl

/-- The `stepLT` field: at a non-basic `Δ ∈ Λ₂[C]` the step of the quasi-tableau
strictly decreases the Dershowitz-Manna ordering. -/
lemma stepOf_lt_Sequent (C : LoadedCluster tab) :
    ∀ Δ ∈ C.lambdaTwo, ¬ Δ.basic → ∀ Y ∈ C.stepOf Δ, ltSequent Y Δ := by
  intro Δ _ hb Y hY
  by_cases hne : C.nodesWithFineRight Δ = []
  · exfalso
    unfold stepOf at hY
    rw [List.head?_eq_none_iff.mpr hne] at hY
    simp at hY
  · obtain ⟨lra, hright, hX, hstep⟩ := C.exists_lra_stepOf hne hb
    simp only [hstep, Finset.mem_image] at hY
    obtain ⟨Z, hZ, rfl⟩ := hY
    rw [← hX]
    refine LocalRuleApp.rightOnly_lt_Sequent hright Z (Finset.mem_toList.mp ?_)
    simp_all

/-- The `basicStep` field: the modal step at a basic `Δ ∈ Λ₂[C]`. -/
lemma basicStep_of (C : LoadedCluster tab)
    (hER : ∀ Δ ∈ C.lambdaTwo, C.nodesWithFineRight Δ ≠ []) :
    ∀ Δ ∈ C.lambdaTwo, Δ.basic → ∃ (A : Nat) (Y : Sequent),
      C.stepOf Δ = {Y}
      ∧ Δ.loadedProg = (·A : Program)
      ∧ Δ.loadedProgs = (·A : Program) :: Y.loadedProgs
      ∧ Y.loadedFma = Δ.loadedFma
      ∧ ∀ (W : Type) (M : KripkeModel W) (w v : W), (∀ φ ∈ Δ.right, evaluate M w φ) →
          relate M (·A : Program) w v → evaluate M v (~⌈⌈Y.loadedProgs⌉⌉Y.loadedFma) →
          ∀ φ ∈ Y.right, evaluate M v φ := by
  intro Δ hΔ hb
  cases hh : (C.nodesWithFineRight Δ).head? with
  | none => exact absurd (List.head?_eq_none_iff.mp hh) (hER Δ hΔ)
  | some f =>
    have hf := List.mem_of_mem_head? hh
    obtain ⟨A, ξ, hAξ, g, hg, hglab⟩ := Uniformity.basicModalStep C hb hf
    have hf' := hf
    simp only [nodesWithFineRight, nodesWithFine, List.mem_filter, decide_eq_true_eq] at hf'
    obtain ⟨⟨hf_CL, hf_lab⟩, hf_right⟩ := hf'
    obtain ⟨c, hc, hcmf⟩ := C.exists_child_memFine_of_not_isLrep ((C.mem_fineCL f).mp hf_CL)
      (f.not_isLrep_base_of_usesRightRule hf_right)
    simp only [hg, Finset.mem_singleton] at hc
    subst hc
    have hgR : c.label.2.2.isRight := Uniformity.isRight_of_memFine C hcmf
    -- The child stays in the cluster, so it is loaded, i.e. `ξ` is a loaded formula.
    obtain ⟨χ, rfl⟩ : ∃ χ, ξ = AnyFormula.loaded χ := by
      rcases ξ with φ | χ
      · exfalso
        have hnone : c.label.2.2 = none := by
          have := congrArg (fun Z => Z.2.2) hglab
          simpa [Sequent.rightOnly, Uniformity.modRChildRight] using this
        rw [hnone] at hgR
        simp at hgR
      · exact ⟨χ, rfl⟩
    refine ⟨A, Uniformity.modRChildRight A (AnyFormula.loaded χ) Δ.2.1, ?_, ?_, ?_, ?_, ?_⟩
    · unfold stepOf
      rw [hh]
      simp [hg, hglab]
    · rcases hD : Δ with ⟨L, R, O⟩
      rw [hD] at hAξ
      simp only at hAξ
      subst hAξ
      rfl
    · rcases hD : Δ with ⟨L, R, O⟩
      rw [hD] at hAξ
      simp only at hAξ
      subst hAξ
      simp [Sequent.loadedProgs, Sequent.loadedSplit, Uniformity.modRChildRight]
    · rcases hD : Δ with ⟨L, R, O⟩
      rw [hD] at hAξ
      simp only at hAξ
      subst hAξ
      simp [Sequent.loadedFma, Sequent.loadedSplit, Uniformity.modRChildRight]
    · intro W M w v hw hrel hload φ hφ
      simp only [Uniformity.modRChildRight, Sequent.right_eq, Olf.R_inr, Finset.mem_union,
        Finset.mem_singleton] at hφ
      rcases hφ with hφ | hφ
      · have hbox : (⌈·A⌉φ) ∈ Δ.2.1 := Finset.mem_projection.mp hφ
        have := hw _ (Finset.mem_union_left _ hbox)
        exact this v hrel
      · subst hφ
        rw [LoadFormula.unload_eq_boxes_split]
        simpa [Sequent.loadedProgs, Sequent.loadedFma, Sequent.loadedSplit,
          Uniformity.modRChildRight] using hload

/-- The `nonBasicStep` field: the local step at a non-basic `Δ ∈ Λ₂[C]`. -/
lemma nonBasicStep_of (C : LoadedCluster tab)
    (hER : ∀ Δ ∈ C.lambdaTwo, C.nodesWithFineRight Δ ≠ []) :
    ∀ Δ ∈ C.lambdaTwo, ¬ Δ.basic → ∀ (W : Type) (M : KripkeModel W) (v : W),
      (∀ φ ∈ Δ.right, evaluate M v φ) →
      ∃ i, ∃ hi : i < (C.stepOfL Δ).length,
        (∀ φ ∈ ((C.stepOfL Δ)[i]'hi).right, evaluate M v φ)
        ∧ witDist M v ((C.stepOfL Δ)[i]'hi) = witDist M v Δ := by
  intro Δ hΔ hb W M v hv
  obtain ⟨lra, hright, hX, hstep⟩ := C.exists_lra_stepOf (hER Δ hΔ) hb
  have hX' : lra.rightOnlyApp.X = Δ := by
    rw [LocalRuleApp.rightOnlyApp_X hright, hX]
  have hC' : ∀ Y ∈ lra.rightOnlyApp.C, Y ∈ C.stepOf Δ := by
    intro Y hY
    rw [LocalRuleApp.rightOnlyApp_C hright, Finset.mem_image] at hY
    obtain ⟨Z, hZ, rfl⟩ := hY
    rw [hstep]
    exact Finset.mem_image_of_mem _ hZ
  have hr' : lra.rightOnlyApp.isRightRule := by
    rw [LocalRuleApp.rightOnlyApp_isRightRule]; exact hright
  obtain ⟨Y, hY, hYsat, hYwd⟩ :=
    LocalRuleApp.rightRule_sat_witDist hr' (by rw [hX']; exact hv)
  have hYL : Y ∈ C.stepOfL Δ := by
    have := hC' Y hY
    simpa [stepOfL] using this
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hYL
  refine ⟨i, hi, ?_, ?_⟩
  · rw [heq]; exact hYsat
  · rw [heq, hYwd, hX']

/-- All facts of `SatDownFacts`, from Lemma 9.7 (d). -/
theorem satDownFacts (C : LoadedCluster tab)
    (hER : ∀ Δ ∈ C.lambdaTwo, C.nodesWithFineRight Δ ≠ []) : C.SatDownFacts where
  rightLoaded := fun _ hΔ => C.isRightLoaded_of_mem_lambdaTwo hΔ
  stepLT := C.stepOf_lt_Sequent
  basicStep := C.basicStep_of hER
  nonBasicStep := C.nonBasicStep_of hER

end LoadedCluster

end PDL
