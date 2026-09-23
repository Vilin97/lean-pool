/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import Mathlib.Tactic.Linarith

public import LeanPool.PDL.Substitution
public import LeanPool.PDL.Star

/-! # Local Diamond Unfolding (Section 3.2 and 3.3) -/

@[expose] public section

namespace PDL

/-! ## Diamonds: Dset, Y and Φ_⋄ -/

/-- Unfold a given program into combinations of test formulas and lists of programs,
assuming the program is used inside a diamond. -/
def Dset : Program → List (List Formula × List Program)
| ·a => [ ([], [·a]) ]
| ?'τ => [ ([τ], []) ]
| α ⋓ β => Dset α ∪ Dset β
| α;'β => (Dset α).flatMap (fun ⟨F,δ⟩ =>
            if δ = []
              then ((Dset β).map (fun ⟨G,δ'⟩ => [⟨F ∪ G, δ'⟩])).flatten
              else [⟨F, δ ++ [β]⟩])
| ∗α => [ (∅,[]) ] ∪ ((Dset α).map (fun (F,δ) => if δ = [] then [] else [(F, δ ++ [∗α])])).flatten

/-- Like `Dset`, but applied to a whole list of programs.
This is used to deal with loaded diamonds. -/
def Dl : List Program → List (List Formula × List Program)
| [] => [([],[])]
| [α] => Dset α
| α :: rest => (Dset α).flatMap (fun ⟨F,δ⟩ => -- inspired by `;` case of `H`
            if δ = []
              then ((Dl rest).flatMap (fun ⟨G,δ'⟩ => [⟨F ∪ G, δ'⟩]))
              else [⟨F, δ ++ rest⟩])

@[simp]
lemma Dl_singleton : Dl [α] = Dset α := by simp [Dl]

@[simp]
lemma Dl_atomic_cons {αs} : Dl (·a :: αs) =  [ ([], ((·a : Program) :: αs)) ] := by
  unfold Dl
  cases αs <;> simp_all [Dset]

theorem relateSeq_Dset_imp_relate {X : List Formula} {δ : List Program}
  : (X, δ) ∈ Dset α → (M, w) ⊨ con X →  relateSeq M δ w v → relate M α w v :=
  let me := (evaluate M w <| con ·)
  let mr := (relateSeq M · w v)
  fun in_D ev rel => match α with
  | ·_ =>
    let hδ := congr_arg mr (Prod.eq_iff_fst_eq_snd_eq.mp (List.eq_of_mem_singleton in_D)).2
    relateSeq_singleton.mp (cast hδ rel)
  | ?'_ =>
    let ⟨hX, hδ⟩ := Prod.eq_iff_fst_eq_snd_eq.mp <| List.eq_of_mem_singleton in_D
    ⟨hδ.subst (motive := mr) rel, hX.subst (motive := me) ev⟩
  | _⋓_ => (List.mem_union_iff.mp in_D).elim
    (.inl <| relateSeq_Dset_imp_relate · ev rel)
    (.inr <| relateSeq_Dset_imp_relate · ev rel)
  | _;'_ =>
    let ⟨⟨_, δα⟩, in_Dα, h⟩ := List.exists_of_mem_flatMap in_D
    if c : δα = []
      then
        let h := (ite_eq_left c).subst h
        let ⟨_, in_Dβ, h⟩ := List.exists_of_mem_flatMap h
        let ⟨hX, hδ⟩ := Prod.eq_iff_fst_eq_snd_eq.mp <| List.eq_of_mem_singleton <| h
        let relα := c.symm.subst (motive := (relateSeq _ · _ _)) <| relateSeq_nil.mpr rfl
        let relβ := hδ.subst (motive := mr) rel
        let ev := hX.subst (motive := me) ev
        let evα := conEval.mpr (List.forall_mem_union.mp <| conEval.mp ev).1
        let evβ := conEval.mpr (List.forall_mem_union.mp <| conEval.mp ev).2
        ⟨w, relateSeq_Dset_imp_relate in_Dα evα relα, relateSeq_Dset_imp_relate in_Dβ evβ relβ⟩
      else
        let h := (ite_eq_right c).subst h
        let ⟨hX, hδ⟩ := Prod.eq_iff_fst_eq_snd_eq.mp <| List.eq_of_mem_singleton <| h
        let ⟨u, relα, relβ⟩ :=  relateSeq_append.mp <| hδ.subst (motive := mr) rel
        let evα := hX.subst (motive := me) ev
        ⟨u, relateSeq_Dset_imp_relate in_Dα evα relα, relateSeq_singleton.mp relβ⟩
  | ∗_ =>
    (List.mem_union_iff.mp in_D).elim (
      let ⟨_, hδ⟩ := Prod.eq_iff_fst_eq_snd_eq.mp <| List.eq_of_mem_singleton ·
      (relateSeq_nil.mp <| hδ.subst (motive := mr) rel) ▸ .refl
    ) (
      let ⟨_, in_Dα, h⟩ := List.exists_of_mem_flatMap ·
      let ⟨_, h⟩ := List.mem_ite_nil_left.mp h
      let ⟨hX, hδ⟩ := Prod.eq_iff_fst_eq_snd_eq.mp <| List.eq_of_mem_singleton h
      let evα := hX.subst (motive := me) ev
      let ⟨_, relα, relαS⟩ :=  relateSeq_append.mp <| hδ.subst (motive := mr) rel
      let relα := relateSeq_Dset_imp_relate in_Dα evα relα
      let relαS := relateSeq_singleton.mp relαS
      .head relα relαS
    )

/-- A test formula coming from `Dset` comes from a test in the given program. -/
theorem Dset_mem_test α φ {Fs δ} (in_D : ⟨Fs, δ⟩ ∈ Dset α) (φ_in_Fs : φ ∈ Fs) :
    ∃ τ, ∃ (_ : τ ∈ testsOfProgram α), φ = τ := by
  cases α
  case atom_prog =>
    simp_all only [Dset, List.mem_singleton, Prod.mk.injEq, testsOfProgram, List.not_mem_nil,
      IsEmpty.exists_iff, exists_const]
  case union α β =>
    simp_all only [Dset, List.mem_union_iff, testsOfProgram, List.mem_append, exists_prop,
      exists_eq_right']
    rcases in_D with in_Dα | in_Dβ
    · have IHα := Dset_mem_test α φ in_Dα φ_in_Fs
      aesop
    · have IHβ := Dset_mem_test β φ in_Dβ φ_in_Fs
      aesop
  case sequence α β =>
    simp_all only [Dset, List.mem_flatMap, Prod.exists, testsOfProgram, List.mem_append,
      exists_prop, exists_eq_right']
    rcases in_D with ⟨Fs', δ', in_Dα, in_l⟩
    by_cases δ' = []
    · simp_all only [↓reduceIte, List.mem_flatten, List.mem_map, Prod.exists, ↓existsAndEq,
        and_true, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, exists_eq_right_right']
      subst_eqs
      rcases in_l with ⟨Fs'', in_D_β, Fs_def⟩
      subst Fs_def
      simp_all only [List.mem_union_iff]
      rcases φ_in_Fs with φ_in_Fs' | φ_in_Fs''
      · have IHβ := Dset_mem_test α φ in_Dα φ_in_Fs'
        aesop
      · have IHβ := Dset_mem_test β φ in_D_β φ_in_Fs''
        aesop
    · simp_all only [ite_false, List.mem_singleton, Prod.mk.injEq]
      cases in_l
      subst_eqs
      have IHα := Dset_mem_test α φ in_Dα φ_in_Fs
      aesop
  case star β =>
    simp_all only [Dset, List.empty_eq, List.cons_union, List.nil_union, List.mem_insert_iff,
      Prod.mk.injEq, List.mem_flatten, List.mem_map, Prod.exists, testsOfProgram, exists_prop,
      exists_eq_right']
    rcases in_D with both_nil | ⟨l, ⟨Fs', δ', in_Dβ, def_l⟩, in_l⟩
    · exfalso; aesop
    · by_cases δ' = []
      · subst_eqs
        simp_all only [List.nil_append, ite_true, List.not_mem_nil]
      · subst def_l
        simp_all only [ite_false, List.mem_singleton, Prod.mk.injEq]
        cases in_l
        subst_eqs
        have IHβ := Dset_mem_test β φ in_Dβ φ_in_Fs
        aesop
  case test τ =>
    simp_all [Dset, testsOfProgram]

/-- A list of programs coming from `H` is either empty or starts with an atom. -/
theorem Dset_mem_sequence α {Fs δ} (in_D : ⟨Fs, δ⟩ ∈ Dset α) :
    δ = [] ∨ ∃ a δ', δ = (·a : Program) :: δ' := by
  cases α
  case atom_prog =>
    simp_all [Dset]
  case union α β =>
    simp_all only [Dset, List.mem_union_iff]
    rcases in_D with in_Dα | in_Dβ
    · have IHα := Dset_mem_sequence α in_Dα
      aesop
    · have IHβ := Dset_mem_sequence β in_Dβ
      aesop
  case sequence α β =>
    simp_all only [Dset, List.mem_flatMap, Prod.exists]
    rcases in_D with ⟨Fs', δ', in_Dα, Fs_in⟩
    by_cases δ' = []
    · simp_all only [↓reduceIte, List.mem_flatten, List.mem_map, Prod.exists, ↓existsAndEq,
        and_true, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, exists_eq_right_right']
      rcases Fs_in with ⟨Fs'', Fs''_in, Fs_def⟩
      subst Fs_def
      have IHβ := Dset_mem_sequence β Fs''_in
      aesop
    · have IHα := Dset_mem_sequence α in_Dα
      aesop
  case star β =>
    simp_all only [Dset, List.empty_eq, List.cons_union, List.nil_union, List.mem_insert_iff,
      Prod.mk.injEq, List.mem_flatten, List.mem_map, Prod.exists]
    rcases in_D with ⟨Fs_nil, δ_nil⟩ | ⟨l, ⟨Fs', δ', in_Dβ, def_l⟩ , in_l⟩
    · subst_eqs
      aesop
    · subst def_l
      by_cases δ' = []
      · aesop
      · have IHβ := Dset_mem_sequence β in_Dβ
        aesop
  case test τ =>
    simp_all [Dset]

theorem keepFreshDset {x} α : x ∉ α.voc → ∀ F δ, (F,δ) ∈ Dset α → x ∉ F.pdlFvoc ∧ x ∉ δ.pdlPvoc :=
  by
  intro x_notin F δ Fδ_in_D
  cases α
  all_goals
    simp only [Program.voc, Finset.mem_singleton, Dset, List.mem_cons, Prod.mk.injEq,
      List.not_mem_nil, or_false, List.pdlFvoc, Vocab.fromList, Finset.mem_sup, List.mem_toFinset,
      List.mem_map, id_eq, exists_exists_and_eq_and, not_exists, not_and, List.pdlPvoc,
      Finset.mem_union, not_or, List.mem_flatMap, Prod.exists, List.mem_union_iff, List.empty_eq,
      List.cons_union, List.nil_union, List.mem_flatten, ↓existsAndEq, and_true,
      List.mem_ite_nil_left, List.nil_eq, List.append_eq_nil_iff, List.cons_ne_self, and_false,
      or_self, exists_const, not_false_eq_true, List.insert_of_not_mem, true_and] at *
  case atom_prog a =>
    cases Fδ_in_D
    subst_eqs
    simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, List.mem_cons, or_false,
      forall_eq, Program.voc, Finset.mem_singleton, true_and]
    assumption
  case test =>
    cases Fδ_in_D
    subst_eqs
    aesop
  case sequence α β =>
    rcases Fδ_in_D with ⟨F', δ', Fδ'_in, Fδ_in_l⟩
    cases em (δ' = [])
    · simp_all only [↓reduceIte, List.mem_flatten, List.mem_map, Prod.exists, ↓existsAndEq,
        and_true, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, exists_eq_right_right']
      subst_eqs
      have IHα := keepFreshDset α x_notin.1 F' [] Fδ'_in
      simp_all only [List.pdlFvoc, Vocab.fromList, Finset.mem_sup, List.mem_toFinset, List.mem_map,
        id_eq, exists_exists_and_eq_and, not_exists, not_and, List.pdlPvoc, List.map_nil,
        List.toFinset_nil, Finset.sup_empty, Finset.bot_eq_empty, Finset.notMem_empty,
        not_false_eq_true, and_true]
      rcases Fδ_in_l with ⟨a', _in_Dβ, F_def⟩
      subst_eqs
      have IHβ := keepFreshDset β x_notin.2 a' δ _in_Dβ
      aesop
    · have := keepFreshDset α x_notin.1 F' δ' Fδ'_in
      simp_all
      grind
  case union α β =>
    cases Fδ_in_D
    · have IHα := keepFreshDset α x_notin.1 F δ
      simp_all
    · have IHβ := keepFreshDset β x_notin.2 F δ
      simp_all
  case star α =>
    cases Fδ_in_D
    · simp_all
    case inr hyp =>
      rcases hyp with ⟨δ', Fδ'_in_D, δ_not_nil, δ_def⟩
      have IHα := keepFreshDset α x_notin F δ' Fδ'_in_D
      subst δ_def
      simp_all
      aesop

/-- This is used by `PreState.loadedExists` -/
theorem Dset_goes_down_prog (α : Program) {Fs δ} (in_D : (Fs, δ) ∈ Dset α) {γ} (in_δ : γ ∈ δ) :
  (if α.isAtomic then γ = α else if α.isStar
    then lengthOfProgram γ ≤ lengthOfProgram α
    else lengthOfProgram γ < lengthOfProgram α) := by
  cases α
  · simp_all [Dset, Program.isAtomic]
  case sequence α β =>
    simp only [Program.isAtomic, Bool.false_eq_true, ↓reduceIte, Program.isStar, lengthOfProgram]
    simp only [Dset, List.mem_flatMap, Prod.exists] at in_D
    rcases in_D with ⟨Fs', δ', Fs'_in, Fs_in⟩
    by_cases δ' = []
    · subst_eqs
      simp_all only [↓reduceIte, List.mem_flatten, List.mem_map, Prod.exists, ↓existsAndEq,
        and_true, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, exists_eq_right_right']
      rcases Fs_in with ⟨Fs'', Fs''_in, Fs_def⟩
      subst_eqs
      have IHβ := Dset_goes_down_prog β Fs''_in in_δ
      cases β
      all_goals
        simp_all [Dset, lengthOfProgram, Program.isAtomic, Program.isStar]
        try linarith
    · simp_all only [ite_false, List.mem_singleton, Prod.mk.injEq, List.mem_append]
      rcases in_δ with bla | γ_eq_β
      · have IHα := Dset_goes_down_prog α Fs'_in bla
        cases α
        all_goals
          simp_all [Dset, lengthOfProgram, Program.isAtomic, Program.isStar]
          try linarith
      · subst γ_eq_β
        linarith
  case union α β =>
    simp only [Program.isAtomic, Bool.false_eq_true, ↓reduceIte, Program.isStar, lengthOfProgram]
    simp only [Dset, List.mem_union_iff] at in_D
    rcases in_D with hyp | hyp
    · have IHα := Dset_goes_down_prog α hyp in_δ
      by_cases α.isAtomic <;> by_cases α.isStar <;> simp_all <;> linarith
    · have IHβ := Dset_goes_down_prog β hyp in_δ
      by_cases β.isAtomic <;> by_cases β.isStar <;> simp_all <;> linarith
  case star α =>
    simp only [Program.isAtomic, Bool.false_eq_true, ↓reduceIte, Program.isStar, lengthOfProgram]
    simp only [Dset, List.empty_eq, List.cons_union, List.nil_union, List.mem_insert_iff,
      Prod.mk.injEq, List.mem_flatten, List.mem_map, Prod.exists] at in_D
    rcases in_D with _ | ⟨l, ⟨Fs', δ', in_D', def_l⟩, in_l⟩
    · simp_all only [List.not_mem_nil]
    · subst def_l
      by_cases δ' = []
      · simp_all
      · simp_all only [ite_false, List.mem_singleton, Prod.mk.injEq, List.mem_append]
        cases in_l
        subst_eqs
        rcases in_δ with hyp | hyp
        · have IHα := Dset_goes_down_prog α in_D' hyp
          by_cases α.isAtomic <;> by_cases α.isStar <;> simp_all <;> linarith
        · subst hyp
          simp [lengthOfProgram]
  case test τ =>
    simp_all [Dset]

/-- An intermediate step to define `unfoldDiamond`. This is not used in the paper. -/
def Yset : (List Formula × List Program) → Formula → List Formula
| ⟨F, δ⟩, φ => F ∪ [ ~ Formula.boxes δ φ ]

/-- Φ_◇(α,ψ) -/
def unfoldDiamond (α : Program) (φ : Formula) : List (List Formula) :=
  (Dset α).map (fun Fδ => Yset Fδ φ)

/-- Where formulas in the diamond unfolding can come from. Inspired by unfoldBoxContent. -/
theorem unfoldDiamondContent α ψ :
    ∀ X ∈ (unfoldDiamond α ψ),
    ∀ φ ∈ X,
        (  (φ = (~ψ))
         ∨ (∃ τ ∈ testsOfProgram α, φ = τ)
         ∨ (∃ (a : Nat), ∃ δ, φ = (~⌈·a⌉⌈⌈δ⌉⌉ψ)))
    := by
  intro X X_in φ φ_in_X
  simp only [unfoldDiamond, Yset, List.mem_map, Prod.exists] at X_in
  rcases X_in with ⟨Fs, δ, in_D, def_X⟩
  subst def_X
  simp only [List.mem_union_iff, List.mem_cons, List.not_mem_nil, or_false] at φ_in_X
  rcases φ_in_X with φ_in_Fs | φ_def
  · -- φ is in F so it must be a test
    right
    left
    have := Dset_mem_test α φ in_D φ_in_Fs
    rcases this with ⟨τ, τ_in, φ_def⟩
    use τ
  · -- φ is made from some δ from Dset α
    have := Dset_mem_sequence α in_D
    aesop

theorem unfoldDiamond_voc {x α φ} {L} (L_in : L ∈ unfoldDiamond α φ) {ψ} (ψ_in : ψ ∈ L)
    (x_in_voc_ψ : x ∈ ψ.voc) : x ∈ α.voc ∨ x ∈ φ.voc := by
  simp only [unfoldDiamond, Yset, List.mem_map, Prod.exists] at L_in
  rcases L_in with ⟨Fs, δ, in_D, def_L⟩
  subst def_L
  simp only [List.mem_union_iff, List.mem_cons, List.not_mem_nil, or_false] at ψ_in
  cases ψ_in
  case inl hyp =>
    left
    have := Dset_mem_test α ψ in_D hyp
    rcases this with ⟨τ, τ_in, ψ_def⟩
    subst ψ_def
    exact testsOfProgram.voc α τ_in x_in_voc_ψ
  case inr ψ_def =>
    have := Dset_mem_sequence
    subst ψ_def
    simp only [Formula.voc, Formula.voc_boxes, Finset.mem_union] at x_in_voc_ψ
    cases x_in_voc_ψ
    case inl hyp =>
      left
      rw [Vocab.fromListProgram_map_iff] at *
      rcases hyp with ⟨α', α'_in, x_in⟩
      by_contra hyp
      have := (keepFreshDset α hyp Fs δ in_D).2
      unfold List.pdlPvoc at this
      rw [Vocab.fromListProgram_map_iff] at this
      push Not at this
      specialize this _ α'_in
      tauto
    · right
      assumption

/-- `Finset` version of `unfoldDiamond_voc`. -/
theorem unfoldDiamond_voc_fin {x α φ} {X : Finset Formula}
    (X_in : X ∈ (unfoldDiamond α φ).pdlToFinFin)
    {ψ} (ψ_in : ψ ∈ X) (x_in_voc_ψ : x ∈ ψ.voc) : x ∈ α.voc ∨ x ∈ φ.voc := by
  simp only [List.pdlToFinFin, List.mem_toFinset, List.mem_map] at X_in
  rcases X_in with ⟨L, L_in, rfl⟩
  exact unfoldDiamond_voc L_in (List.mem_toFinset.mp ψ_in) x_in_voc_ψ

theorem guardToStarDiamond (x : Nat)
    (x_notin_beta : Sum.inl x ∉ β.voc)
    (beta_equiv : (~⌈β⌉~·x) ≡ (((·x) ⋀ σ0) ⋁ σ1))
    (repl_imp_rho : replInF x ρ σ1 ⊨ ρ)
    (notPsi_imp_rho : (~ψ) ⊨ ρ)
  : (~⌈(∗β)⌉ψ) ⊨ ρ:= by
  intro W M
  have claim : ∀ u v, (M,v) ⊨ ρ → relate M β u v → (M,u) ⊨ ρ := by
    intro u v v_rho u_β_v
    have u_ : (M,u) ⊨ (~⌈β⌉~ρ) := by
      simp only [Formula.or, vDash.SemImplies, evaluatePoint, evaluate, not_forall,
         not_not] at *
      use v
    have u_2 : (M, u) ⊨ (ρ ⋀ replInF x ρ σ0) ⋁ (replInF x ρ σ1) := by
      have repl_equiv := repl_in_F_equiv x ρ beta_equiv
      simp only [replInF, beq_self_eq_true, reduceIte, Formula.or] at repl_equiv
      have nox : replInP x ρ β = β := repl_in_P_non_occ_eq x_notin_beta
      rw [nox] at repl_equiv
      rw [equiv_iff _ _ repl_equiv] at u_
      simp [vDash.SemImplies, evaluatePoint, semImpliesLists] at *
      tauto
    simp only [vDash.SemImplies, Formula.or, evaluatePoint, evaluate] at u_2
    rw [← @or_iff_not_and_not] at u_2
    specialize repl_imp_rho W M u
    aesop
  -- It remains to show the goal using claim.
  intro w hyp
  simp only [Formula.or, List.mem_singleton, forall_eq, evaluate, relate, not_forall,
    exists_prop] at *
  rcases hyp with ⟨v, w_bS_v, v_Psi⟩
  induction w_bS_v using Relation.ReflTransGen.head_induction_on
  case refl =>
    specialize notPsi_imp_rho W M v
    simp_all
  case head u1 u2 u1_b_u2 _ IH =>
    specialize claim u1 u2
    specialize notPsi_imp_rho W M u1
    simp [vDash.SemImplies, evaluatePoint, semImpliesLists] at *
    simp_all

private theorem helper : ∀ (p : List Formula × List Program → Formula) X,
        (∃ f ∈ List.map p X, evaluate M w f)
      ↔ (∃ Fδ ∈ X, evaluate M w (p Fδ)) := by aesop

/-- A model of the unfolded diamond-star formula reaches a counterexample to the box. -/
private theorem localDiamondTruth_star_reverse (β : Program) (ψ : Formula)
    (IHβ : ∀ ψ, (~⌈β⌉ψ) ≡ dis ((Dset β).map (fun Fδ => con (Yset Fδ ψ)))) :
    ∀ W (M : KripkeModel W) w, evaluate M w (dis ((Dset (∗β)).map (fun Fδ => con (Yset Fδ ψ)))) →
      evaluate M w (~⌈∗β⌉ψ) := by
  let ρ := dis ((Dset (∗β)).map (fun Fδ => con (Yset Fδ ψ)))
  change ∀ W (M : KripkeModel W) w, evaluate M w ρ → evaluate M w (~⌈∗β⌉ψ)
  -- Note that we are switching model now.
  intro W M w
  unfold ρ
  rw [disEval, helper]
  rintro ⟨⟨Fs,δ⟩, ⟨Fδ_in, w_Con⟩⟩
  rw [conEval] at w_Con
  simp only [Dset, List.empty_eq, List.cons_union, List.nil_union, List.mem_flatten,
    List.mem_map, Prod.exists, ↓existsAndEq, and_true, List.mem_ite_nil_left, List.mem_cons,
    Prod.mk.injEq, List.nil_eq, List.append_eq_nil_iff, List.cons_ne_self, and_false,
    List.not_mem_nil, or_self, exists_const, not_false_eq_true, List.insert_of_not_mem,
    or_false, true_and] at Fδ_in
  cases Fδ_in
  case inl hyp =>
    cases hyp
    subst_eqs
    simp_all only [Yset, Formula.boxes_nil, List.nil_union, List.mem_cons, List.not_mem_nil,
      or_false, evaluate, forall_eq, relate, not_forall]
    use w
  case inr hyp =>
    have : ∃ γ, δ = γ ++ [∗β] ∧ γ ≠ [] ∧ (Fs,γ) ∈ Dset β := by aesop
    rcases this with ⟨γ, ⟨δ_def, _, Fγ_in⟩⟩
    subst δ_def
    simp only [Yset, List.mem_union_iff, List.mem_singleton] at w_Con
    suffices evaluate M w (~⌈β⌉⌈∗β⌉ψ) by
      simp only [ne_eq, List.append_cancel_right_eq, exists_eq_right_right', evaluate, relate,
        not_forall] at *
      rcases this with ⟨v, ⟨w_β_v, ⟨u, ⟨v_Sβ_u, u_nPsi⟩⟩⟩⟩
      refine ⟨u, ?_, u_nPsi⟩
      exact Relation.ReflTransGen.head w_β_v v_Sβ_u
    have IHβ := IHβ (⌈∗β⌉ψ) W M w
    rw [disEval, helper] at IHβ
    rw [IHβ]
    refine ⟨⟨Fs, γ⟩, ⟨Fγ_in, ?_⟩⟩
    simp_all [conEval, Yset, boxes_append]

/-- Diamond-star unfolding follows from the unfolding for its body. -/
private theorem localDiamondTruth_star (β : Program) (ψ : Formula)
    (IHβ : ∀ ψ, (~⌈β⌉ψ) ≡ dis ((Dset β).map (fun Fδ => con (Yset Fδ ψ)))) :
    (~⌈∗β⌉ψ) ≡ dis ((Dset (∗β)).map (fun Fδ => con (Yset Fδ ψ))) := by
  intro W M w
  let ρ := dis ((Dset (∗β)).map (fun Fδ => con (Yset Fδ ψ)))
  -- "then our goal will be ..."
  suffices goal : (~⌈∗β⌉ψ) ≡ ρ by
    have := @equiv_iff _ _ goal W M w
    simp only [vDash.SemImplies, evaluatePoint] at this
    rw [this]
  -- right to left, done first because we use it for the other direction
  have right_to_left_claim : ∀ W (M : KripkeModel W) w,
      evaluate M w ρ → evaluate M w (~⌈∗β⌉ψ) := localDiamondTruth_star_reverse β ψ IHβ
  -- switch model again
  clear W M w; intro W M w
  constructor
  · -- left to right, done second in notes
    -- NOTE: Here is why we switched from `Char` to `Nat` for atomic propositions.
    -- Char was finite so we could not get fresh variables. Now we can :-)
    -- An alternative idea to solve this would have been to refactor everything
    -- to allow different types, but that seemed harder and not (yet?!) needed.
    let x : Nat := freshVarProg β
    have x_not_in : Sum.inl x ∉ β.voc := by apply freshVarProg_is_fresh
    -- NOTE the use of ⊥ below - matters for rhs-to-lhs in first Lemma condition.
    let σ0 : Formula := dis <|
      (Dset β).map (fun (F,δ) => if δ = [] then con F else ⊥)
    let σ1 : Formula := dis <|
      ((Dset β).map (fun (F,δ) => if δ ≠ [] then con ((~ ⌈⌈δ⌉⌉(~(·x : Formula))) :: F) else ⊥))
    -- Now we use the previous Lemma:
    have := @guardToStarDiamond β σ0 σ1 ρ ψ x x_not_in
    simp only [vDash.SemImplies, semImpliesLists, List.mem_singleton, forall_eq] at this
    apply this <;> (clear this W M w; intro W M w) -- Switching model again.
    · -- Use IH to show first Lemma condition:
      have IHβ := IHβ (~·x) W M w
      rw [disEval,helper] at IHβ
      rw [IHβ]
      clear IHβ
      constructor
      · rintro ⟨⟨Fs, δ⟩, Fδ_in, w_⟩
        simp only [evaluate, Formula.or]
        rw [← or_iff_not_and_not]
        cases em (δ = [])
        · subst_eqs
          simp only [Yset, Formula.boxes_nil, conEval, List.mem_union_iff, List.mem_cons,
            List.not_mem_nil, or_false] at w_
          left
          unfold σ0
          simp_all only [evaluate, relate, not_forall]
          rw [disEval, helper]
          constructor
          · have := w_ (~~·x)
            simp only [or_true, evaluate, not_not, forall_const] at this
            exact this
          · use (Fs, [])
            simp_all only [exists_prop, ↓reduceIte, true_and]
            rw [conEval]
            intro f f_in
            apply w_
            left
            exact f_in
        · simp only [Yset, conEval, List.mem_union_iff, List.mem_cons, List.not_mem_nil,
          or_false] at w_
          right
          unfold σ1
          simp_all only [evaluate, relate, not_forall,  ne_eq, ite_not]
          rw [disEval, helper]
          use (Fs, δ)
          simp_all only [exists_prop, ↓reduceIte, true_and]
          rw [conEval]
          intro f f_in
          apply w_ f
          simp at f_in
          tauto
      · intro rhs
        simp only [evaluate, Formula.or] at rhs
        rw [← or_iff_not_and_not] at rhs
        cases rhs
        case inl hyp =>
          unfold σ0 at hyp
          simp only [] at hyp
          rw [disEval, helper] at hyp
          rcases hyp with ⟨w_x, ⟨⟨Fs,δ⟩, w_⟩⟩
          use (Fs,δ)
          simp only [Yset, conEval, List.mem_union_iff, List.mem_cons, List.not_mem_nil, or_false]
          constructor
          · exact w_.1
          · cases em (δ = [])
            case inl δ_is_empty =>
              subst δ_is_empty
              simp_all only [evaluate, relate, not_forall,  ↓reduceIte,
                conEval, Formula.boxes_nil]
              intro f f_in
              cases f_in
              · apply w_.2; assumption
              · subst_eqs; simp only [evaluate, not_not]; assumption
            case inr δ_notEmpty => exfalso; simp_all
              -- this case works because we used ⊥ above!
        case inr hyp =>
          unfold σ1 at hyp
          simp only [ne_eq, ite_not] at hyp
          rw [disEval, helper] at hyp
          rcases hyp with ⟨⟨Fs,δ⟩, ⟨Fδ_in, w_⟩⟩
          use ⟨Fs,δ⟩
          simp only [evaluate, relate, not_forall,  Yset, conEval,
            List.mem_union_iff, List.mem_cons, List.not_mem_nil, or_false] at *
          -- hmm
          constructor
          · exact Fδ_in
          · cases em (δ = [])
            case inl _ => exfalso; simp_all
              -- this case works because we used ⊥ above!
            case inr δ_notEmpty =>
              simp_all only [↓reduceIte, conEval, List.mem_cons, forall_eq_or_imp, evaluate]
              intro f f_in
              cases f_in
              · apply w_.2; assumption
              · subst_eqs; simp only [evaluate]; exact w_.1
    · -- Lemma condition that is done last in notes.
      unfold σ1
      simp only [ne_eq, Bot.bot, ite_not]
      have : (replInF x ρ (dis ((Dset β).map
        (fun Fδ => if Fδ.2 = [] then Formula.bottom else con ((~⌈⌈Fδ.2⌉⌉~·x) :: Fδ.1)) ))) =
          (dis ((Dset β).map (fun Fδ => if Fδ.2 = [] then Formula.bottom
                                                  else con ((~⌈⌈Fδ.2⌉⌉~ρ) :: Fδ.1)))) := by
        suffices (replInF x ρ (dis ((Dset β).map
          (fun Fδ => if Fδ.2 = [] then Formula.bottom else con ((~⌈⌈Fδ.2⌉⌉~·x) :: Fδ.1)) ))) =
            ((dis ((Dset β).map
              (fun Fδ => if Fδ.2 = [] then replInF x ρ Formula.bottom
                                      else replInF x ρ (con ((~⌈⌈Fδ.2⌉⌉~·x) :: Fδ.1)) )))) by
          rw [this]
          simp only [replInF, Bot.bot]
          -- use that x not in β and thus also not in any element of H β
          have myFresh := keepFreshDset β x_not_in
          apply listEq_to_disEq
          rw [List.map_inj_left]
          intro Fδ Fδ_in_Dβ
          cases em (Fδ.2 = [])
          · simp_all
          · simp_all only [evaluate, relate, not_forall, exists_prop, replInF, Bot.bot,
              ite_false]
            rw [repl_in_con]
            simp only [List.map_cons, replInF]
            apply listEq_to_conEq
            simp only [List.cons.injEq, Formula.neg.injEq]
            constructor
            · exact repl_in_boxes_non_occ_eq_neg _ ((myFresh _ _ (Fδ_in_Dβ)).2)
            · exact repl_in_list_non_occ_eq _ ((myFresh _ _ (Fδ_in_Dβ)).1)
        -- remains to push replInF through dis and map
        convert repl_in_disMap x ρ (Dset β) (fun Fδ => Fδ.2 = [])
          (fun Fδ => (con ((~⌈⌈Fδ.2⌉⌉~·x) :: Fδ.1)))
        simp [replInF, Bot.bot]
      rw [this, disEval, helper]
      clear this
      rintro ⟨⟨Fs,δ⟩, ⟨Fδ_in, repl_w_⟩⟩
      cases em (δ = [])
      case inl hyp =>
        subst hyp
        simp_all
      case inr hyp =>
        simp only [hyp, ↓reduceIte] at repl_w_
        rw [conEval] at repl_w_
        have := repl_w_ (~⌈⌈δ⌉⌉~ρ) (by simp)
        simp only [evaluate, evalBoxes, not_forall,  not_not] at this
        rcases this with ⟨v, w_ρ_v, v_ρ⟩ -- used for v_notStarβψ below!
        -- We now do bottom-up what the notes do, first reasoning "at w" then "at v"
        unfold ρ
        simp_all only [evaluate, relate, not_forall, List.mem_cons, con,
          forall_eq_or_imp, Yset, Dset, List.empty_eq, List.cons_union, List.nil_union,
          List.mem_flatten, List.mem_map, Prod.exists, ↓existsAndEq, and_true,
          List.mem_ite_nil_left, Prod.mk.injEq, List.nil_eq, List.append_eq_nil_iff,
          List.cons_ne_self, and_false, List.not_mem_nil, or_self, exists_const,
          not_false_eq_true, List.insert_of_not_mem, List.map_cons, Formula.boxes_nil,
          List.map_flatten, List.map_map, disEval, Function.comp_apply, or_false,
          exists_eq_or_imp]
        right
        use Fs, δ
        simp_all only [exists_prop, not_false_eq_true, and_self, conEval, List.mem_union_iff,
          List.mem_cons, List.not_mem_nil, or_false, true_and]
        rintro f (f_in_F|f_def)
        · exact repl_w_.2 f f_in_F
        · subst f_def
          simp only [evaluate, boxes_append, Formula.boxes_cons, Formula.boxes_nil, evalBoxes,
            relate, not_forall, exists_prop]
          have v_notStarβψ := right_to_left_claim W M v v_ρ
          exact ⟨v, ⟨w_ρ_v, v_notStarβψ⟩⟩
    · -- Second Lemma condition
      intro w_nPsi
      unfold ρ
      rw [disEval, helper]
      simp only [Dset, List.empty_eq, List.cons_union, List.nil_union, List.mem_flatten,
        List.mem_map, Prod.exists, ↓existsAndEq, and_true, List.mem_ite_nil_left, List.mem_cons,
        Prod.mk.injEq, List.nil_eq, List.append_eq_nil_iff, List.cons_ne_self, and_false,
        List.not_mem_nil, or_self, exists_const, not_false_eq_true, List.insert_of_not_mem,
        or_false, Yset, conEval, List.mem_union_iff, exists_eq_or_imp, Formula.boxes_nil,
        false_or, forall_eq, evaluate]
      left
      simp only [evaluate] at w_nPsi
      exact w_nPsi
  · apply right_to_left_claim -- done above

theorem localDiamondTruth γ ψ : (~⌈γ⌉ψ) ≡ dis ( (Dset γ).map (fun Fδ => con (Yset Fδ ψ)) ) := by
  intro W M w
  cases γ
  case atom_prog a =>
    simp [Dset, Yset]
  case test τ =>
    simp only [evaluate, relate, and_imp, forall_eq', Classical.not_imp, Yset, Dset,
      List.map_cons, Formula.boxes_nil, List.cons_union, List.nil_union, List.map_nil, dis.eq_2]
    rw [conEval]
    simp
  case union α β =>
    -- "This case is straightforward"
    have IHα := localDiamondTruth α ψ W M w
    have IHβ := localDiamondTruth β ψ W M w
    simp [evaluate, Dset, Yset, disEval] at *
    grind
  case sequence α β =>
    -- "This case follows from the following computation"
    have : evaluate M w (~⌈α;'β⌉ψ) ↔ evaluate M w (~⌈α⌉⌈β⌉ψ) := by aesop
    rw [this]
    clear this
    have IHα := localDiamondTruth α (⌈β⌉ψ) W M w
    rw [IHα]
    clear IHα
    rw [disEval]
    rw [disEval]
    rw [helper, helper]
    constructor
    -- downwards direction in notes:
    · rintro ⟨⟨Fs,δ⟩, ⟨Fδ_in, w_Con⟩⟩
      cases em (δ = [])
      case inl δ_is_empty => -- tricky case where we actually need the IH for β
        subst δ_is_empty
        have claim : ∃ Gγ ∈ Dset β, evaluate M w (con (Yset Gγ ψ)) := by
          rw [conEval] at w_Con
          simp only [Yset, Formula.boxes_nil, List.mem_union_iff, List.mem_cons, List.not_mem_nil,
            or_false] at w_Con
          have := w_Con (~⌈β⌉ψ)
          simp only [or_true, forall_true_left] at this
          have IHβ := localDiamondTruth β ψ W M w
          rw [IHβ] at this
          rw [disEval, helper] at this
          exact this
        rcases claim with ⟨⟨Gs,γ⟩, Gsγ_in, claim⟩
        unfold Dset
        use ⟨Fs ∪ Gs, γ⟩
        constructor
        · simp only [List.mem_flatMap, Prod.exists]
          use Fs, []
          grind
        · simp only [Yset, conEval, List.mem_union_iff, List.mem_singleton] at *
          intro f f_in
          specialize w_Con f
          specialize claim f
          tauto
      case inr δ_not_empty => -- the easy case?
        unfold Dset
        use ⟨Fs, δ ++ [β]⟩
        constructor
        · simp
          grind
        · simp only [Yset, conEval, List.mem_union_iff, List.mem_cons, List.not_mem_nil, or_false,
          boxes_append, Formula.boxes_cons, Formula.boxes_nil] at *
          intro f f_in
          apply w_Con
          tauto
    -- upwards direction in notes:
    · rintro ⟨⟨Fs,δ⟩, ⟨Fδ_in, w_Con⟩⟩ -- ⟨⟨l, ⟨⟨a, b, ⟨ab_in, def_l⟩⟩, f_in_l⟩⟩, w_f⟩⟩
      simp only [Dset, List.mem_flatMap, Prod.exists] at Fδ_in
      rcases Fδ_in with ⟨Gs, γ, Gγ_in, Fδ_in⟩
      cases em (γ = [])
      case inl δ_is_empty => -- tricky case where we actually need the IH for β
        subst δ_is_empty
        simp only [↓reduceIte, List.mem_flatten, List.mem_map, Prod.exists, ↓existsAndEq,
          and_true, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false,
          exists_eq_right_right'] at Fδ_in
        rcases Fδ_in with ⟨Hs, _in_Dβ, Fs_def⟩
        subst Fs_def
        simp only [Prod.exists]
        use Gs, [], Gγ_in
        simp only [Yset, Formula.boxes_nil]
        · simp only [conEval, List.mem_union_iff, List.mem_cons, List.not_mem_nil, or_false]
          intro f f_in
          cases f_in
          case inl f_in =>
            rw [conEval] at w_Con
            simp only [Yset, List.mem_union_iff, List.mem_cons, List.not_mem_nil, or_false] at *
            specialize w_Con f
            tauto
          case inr f_def =>
            subst f_def
            have IHβ := localDiamondTruth β ψ W M w
            rw [IHβ, disEval, helper]
            clear IHβ
            use ⟨Hs,δ⟩, _in_Dβ
            rw [conEval]
            rw [conEval] at w_Con
            simp only [Yset, List.mem_union_iff, List.mem_cons, List.not_mem_nil, or_false] at *
            intro f
            specialize w_Con f
            tauto
      case inr δ_not_empty => -- the easy case
        simp_all only [↓reduceIte, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false,
          Prod.exists]
        cases Fδ_in
        subst_eqs
        simp_all only [Yset, boxes_append, Formula.boxes_cons, Formula.boxes_nil, conEval,
          List.mem_union_iff, List.mem_cons, List.not_mem_nil, or_false]
        use Fs, γ
  case star β =>
    exact localDiamondTruth_star β ψ (localDiamondTruth β) W M w

/-- Helper function to trick "List.Chain r" to use a different r at each step. -/
def pairRel (M : KripkeModel W) : (Program × W) → (Program × W) → Prop
| (_, v), (α, w) => relate M α v w

-- use later for Modelgraphs
theorem relateSeq_toChain' {M} {δ} {v w : W} : relateSeq M δ v w → δ ≠ [] →
    ∃ (l : List W), l.length + 1 = δ.length ∧
    List.IsChain (pairRel M) (List.zip ((?'⊤) :: δ) (v :: l ++ [w]) ) := by
  induction δ generalizing v w
  case nil =>
    simp [relateSeq]
  case cons e δ IH =>
    cases em (δ = [])
    case inl δ_eq_empty =>
      subst δ_eq_empty
      intro _
      simp_all [pairRel]
    case inr δ_notEmpty =>
      simp only [relateSeq]
      rintro ⟨u, v_d_u, u_δ_w⟩ _
      specialize IH u_δ_w δ_notEmpty
      rcases IH with ⟨l, l_def, lchain⟩
      use (u :: l)
      constructor
      · simp_all
      · simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, List.cons_append,
        List.zip_cons_cons, List.isChain_cons_cons, pairRel, true_and]
        apply List.IsChain.cons
        · have := List.IsChain.tail lchain
          simp_all
        · cases l <;> cases δ
          all_goals simp_all [pairRel]

theorem existsDiamondDset (v_γ_w : relate M γ v w) :
    ∃ Fδ ∈ Dset γ, (M,v) ⊨ Fδ.1 ∧ relateSeq M Fδ.2 v w := by
  cases γ
  case atom_prog =>
    simp only [relate, Dset, List.mem_cons, List.not_mem_nil, or_false, vDash.SemImplies,
      exists_eq_left, IsEmpty.forall_iff, implies_true, relateSeq, exists_eq_right, true_and] at *
    exact v_γ_w
  case test τ =>
    simp [Dset, relateSeq] at *
    aesop
  case union α β =>
    simp only [relate, Dset, List.mem_union_iff, Prod.exists] at *
    cases v_γ_w
    case inl hyp =>
      have IHα := existsDiamondDset hyp
      aesop
    case inr hyp =>
      have IHβ := existsDiamondDset hyp
      aesop
  case sequence α β =>
    simp only [relate] at v_γ_w
    rcases v_γ_w with ⟨u, v_α_u, u_β_w⟩
    have IHα := existsDiamondDset v_α_u
    simp only [Prod.exists] at IHα
    rcases IHα with ⟨Fs, δ, ⟨Fδ_in, u_Fs, v_δ_u⟩⟩
    cases em (δ = [])
    case inl hyp =>
      subst hyp
      simp only [relateSeq] at v_δ_u -- we have v = u
      subst v_δ_u
      have IHβ := existsDiamondDset u_β_w
      simp only [Prod.exists] at IHβ
      rcases IHβ with ⟨Gs, η, ⟨Gη_in, v_Gs, v_η_w⟩⟩
      refine ⟨ ⟨Fs ∪ Gs, η⟩, ⟨?_, ?_, v_η_w⟩ ⟩
      · simp_all [Dset]
        grind
      · intro f f_in
        simp only [List.mem_union_iff] at f_in
        cases f_in
        · specialize u_Fs f (by assumption)
          assumption
        · apply v_Gs f
          assumption
    case inr hyp =>
      refine ⟨⟨Fs, δ ++ [β]⟩, ⟨?_, ?_, ?_⟩⟩
      · grind [Dset]
      · intro f f_in
        simp only [] at f_in
        specialize u_Fs f f_in
        assumption
      · simp only [relateSeq_append, relateSeq_singleton]
        use u
  case star β =>
    simp only [relate] at v_γ_w
    have := ReflTransGen.cases_tail_eq_neq v_γ_w
    cases this
    · subst_eqs
      use ⟨∅, []⟩
      simp [Dset, relateSeq, vDash.SemImplies]
    case inr hyp =>
      rcases hyp with ⟨_, ⟨v1, v_neq_v1, v_β_v1, v1_βS_w⟩⟩
      have IHβ := existsDiamondDset v_β_v1
      rcases IHβ with ⟨⟨Fs,δ⟩, Fδ_in, v_Fs, v_δ_v1⟩
      use ⟨Fs, δ ++ [∗β]⟩
      constructor
      · simp only [ne_eq, Dset, List.empty_eq, List.cons_union, List.nil_union, List.mem_flatten,
        List.mem_map, Prod.exists, ↓existsAndEq, and_true, List.mem_ite_nil_left, List.mem_cons,
        Prod.mk.injEq, List.nil_eq, List.append_eq_nil_iff, List.cons_ne_self, and_false,
        List.not_mem_nil, or_self, exists_const, not_false_eq_true, List.insert_of_not_mem,
        List.append_cancel_right_eq, or_false, exists_eq_right_right', false_or] at *
        have claim : δ ≠ [] := by
          by_contra hyp
          subst_eqs
          simp only [relateSeq] at v_δ_v1
          tauto
        grind
      · constructor
        · intro f f_in
          simp only [] at f_in
          exact v_Fs f f_in
        · rw [relateSeq_append]
          use v1
          simp [relateSeq] at *
          tauto

/-! ## Loaded Diamonds (Section 3.3)

The `Option` is used here because unfolding of tests can lead to free nodes.
-/

/-- Attach a residual program sequence to an already loaded continuation. -/
def YsetLoad : (List Formula × List Program) → LoadFormula → (List Formula × Option NegLoadFormula)
| ⟨F, δ⟩, χ => ⟨F , ~' (LoadFormula.boxes δ χ)⟩

/-- Load a residual sequence over an ordinary formula, or unload it when the sequence is empty. -/
def YsetLoad' : (List Formula × List Program) → Formula → (List Formula × Option NegLoadFormula)
| ⟨F, δ⟩, φ => match splitLast δ with
    | none => ⟨F ∪ [~φ], none⟩
    | some (δ, β) => ⟨F , ~' (loadMulti δ β φ)⟩

/-- Loaded unfolding for ~'⌊α⌋(χ : LoadFormula) -/
def unfoldDiamondLoaded (α : Program) (χ : LoadFormula) :
    List (List Formula × Option NegLoadFormula) :=
  (Dset α).map (fun Fδ => YsetLoad Fδ χ)

/-- Loaded unfolding for ~'⌊α⌋(φ : Formula) -/
def unfoldDiamondLoaded' (α : Program) (φ : Formula) :
    List (List Formula × Option NegLoadFormula) :=
  (Dset α).map (fun Fδ => YsetLoad' Fδ φ)

/-- Merge an optional loaded formula into a list of ordinary formulas by unloading it. -/
def pairUnload : List Formula × Option NegLoadFormula → List Formula
| (xs, none) => xs
| (xs, some nlf) => xs ∪ [negUnload nlf]

/-- Merge an optional loaded formula into a finset of ordinary formulas by unloading it. -/
def pairUnloadSet : Finset Formula × Option NegLoadFormula → Finset Formula
| (xs, none) => xs
| (xs, some nlf) => xs ∪ {negUnload nlf}

theorem unfoldDiamondLoaded_eq α χ :
    (unfoldDiamondLoaded α χ).map pairUnload = unfoldDiamond α χ.unload := by
  simp [unfoldDiamondLoaded, unfoldDiamond, YsetLoad, Yset, pairUnload]

theorem unfoldDiamondLoaded'_eq α φ :
    (unfoldDiamondLoaded' α φ).map pairUnload = unfoldDiamond α φ := by
  simp only [unfoldDiamondLoaded', YsetLoad', List.map_map, unfoldDiamond, Yset,
    List.map_inj_left, Function.comp_apply, pairUnload, negUnload, Prod.forall]
  intro F δ in_D
  cases δ
  · simp
  case cons x xs =>
    simp only [splitLast_cons_eq_some, unload_loadMulti, Formula.boxes_cons]
    have := (@boxes_append (x :: xs).dropLast [(x :: xs).getLast (List.cons_ne_nil x xs)] φ).symm
    simp only [Formula.boxes_cons, Formula.boxes_nil] at this
    rw [this]
    rw [List.dropLast_append_getLast]
    simp_all

end PDL
