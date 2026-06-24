/-
Copyright (c) 2026 Madeleine Gignoux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madeleine Gignoux
-/

import LeanPool.Lean4GlCoalgebras.Pdl.Game
import LeanPool.Lean4GlCoalgebras.Split.Proof

/-! ## The GL-split game.

Builder-Prover game for constructive counter-models/proofs. Builder gets a rule application `R` and
plays an applicable sequent `Γ` in order to construct a counter-model. Prover get a sequent `Γ`
and plays rule applications `R` in order to construct a proof.
-/

namespace Lean4GlCoalgebras

namespace Split

/-- Auxiliary declaration used in the GL coalgebra development. -/
abbrev Builder := Player.A
/-- Auxiliary declaration used in the GL coalgebra development. -/
abbrev Prover := Player.B

-- `ruleApps` performs a large exhaustive case split over split formulas.
/-- The available rule applications for a sequent `Γ`. -/
def SplitSequent.ruleApps (Γ : SplitSequent) : Finset RuleApp :=
  let f : SplitFormula → Option RuleApp := fun φ ↦
    if φ_in : φ ∈ Γ then match φ with
    | Sum.inl ⊤ => RuleApp.topₗ Γ φ_in
    | Sum.inr ⊤ => RuleApp.topᵣ Γ φ_in
    | Sum.inl (at n) =>
      if nφ_in : Sum.inl (na n) ∈ Γ then RuleApp.axₗₗ Γ n ⟨φ_in, nφ_in⟩ else
      if nφ_in : Sum.inr (na n) ∈ Γ then RuleApp.axₗᵣ Γ n ⟨φ_in, nφ_in⟩ else none
    | Sum.inr (at n) =>
      if nφ_in : Sum.inl (na n) ∈ Γ then RuleApp.axᵣₗ Γ n ⟨φ_in, nφ_in⟩ else
      if nφ_in : Sum.inr (na n) ∈ Γ then RuleApp.axᵣᵣ Γ n ⟨φ_in, nφ_in⟩ else none
    | Sum.inl (ψ & χ) => RuleApp.andₗ Γ ψ χ φ_in
    | Sum.inr (ψ & χ) => RuleApp.andᵣ Γ ψ χ φ_in
    | Sum.inl (ψ v χ) => RuleApp.orₗ Γ ψ χ φ_in
    | Sum.inr (ψ v χ) => RuleApp.orᵣ Γ ψ χ φ_in
    | Sum.inl (□ ψ) => RuleApp.boxₗ Γ ψ φ_in
    | Sum.inr (□ ψ) => RuleApp.boxᵣ Γ ψ φ_in
    | _ => none
    else none
  Finset.filterMap f Γ (by
    intro φ ψ r φ_f ψ_f
    let source : RuleApp → SplitFormula := fun
      | RuleApp.topₗ _ _ => Sum.inl ⊤
      | RuleApp.topᵣ _ _ => Sum.inr ⊤
      | RuleApp.axₗₗ _ n _ => Sum.inl (at n)
      | RuleApp.axₗᵣ _ n _ => Sum.inl (at n)
      | RuleApp.axᵣₗ _ n _ => Sum.inr (at n)
      | RuleApp.axᵣᵣ _ n _ => Sum.inr (at n)
      | RuleApp.andₗ _ A B _ => Sum.inl (A & B)
      | RuleApp.andᵣ _ A B _ => Sum.inr (A & B)
      | RuleApp.orₗ _ A B _ => Sum.inl (A v B)
      | RuleApp.orᵣ _ A B _ => Sum.inr (A v B)
      | RuleApp.boxₗ _ A _ => Sum.inl (□ A)
      | RuleApp.boxᵣ _ A _ => Sum.inr (□ A)
    have source_eq : ∀ {θ : SplitFormula} {R : RuleApp}, f θ = some R → θ = source R := by
      intro θ R h
      rcases θ with θ | θ <;> cases θ <;>
        simp only [Option.dite_none_right_eq_some, Option.some.injEq, dite_eq_ite, ite_self,
          reduceCtorEq, f] at h
      all_goals
        rcases h with ⟨_, hR⟩
        try split_ifs at hR
        all_goals
          cases hR
          rfl
    exact (source_eq φ_f).trans (source_eq ψ_f).symm)

/-- The sequents possible after a rule application `R`. -/
def RuleApp.splitSequents (R : RuleApp) : Finset SplitSequent := match R with
  | RuleApp.topₗ _ _ => ∅
  | RuleApp.topᵣ _ _ => ∅
  | RuleApp.axₗₗ _ _ _ => ∅
  | RuleApp.axₗᵣ _ _ _ => ∅
  | RuleApp.axᵣₗ _ _ _ => ∅
  | RuleApp.axᵣᵣ _ _ _ => ∅
  | RuleApp.andₗ Δ φ ψ _ =>
      {(Δ \ {Sum.inl (φ & ψ)}) ∪ {Sum.inl φ},
        (Δ \ {Sum.inl (φ & ψ)}) ∪ {Sum.inl ψ}}
  | RuleApp.andᵣ Δ φ ψ _ =>
      {(Δ \ {Sum.inr (φ & ψ)}) ∪ {Sum.inr φ},
        (Δ \ {Sum.inr (φ & ψ)}) ∪ {Sum.inr ψ}}
  | RuleApp.orₗ Δ φ ψ _ => {(Δ \ {Sum.inl (φ v ψ)}) ∪ {Sum.inl φ, Sum.inl ψ}}
  | RuleApp.orᵣ Δ φ ψ _ => {(Δ \ {Sum.inr (φ v ψ)}) ∪ {Sum.inr φ, Sum.inr ψ}}
  | RuleApp.boxₗ Δ φ _ => {(Δ \ {Sum.inl (□ φ)}).D ∪ {Sum.inl φ}}
  | RuleApp.boxᵣ Δ φ _ => {(Δ \ {Sum.inr (□ φ)}).D ∪ {Sum.inr φ}}

/-- Note: the game stores the history of which rule applications have come prior. -/
abbrev GamePos := (SplitSequent ⊕ RuleApp) × List SplitSequent × List RuleApp

/-- Auxiliary declaration used in the GL coalgebra development. -/
inductive Move : GamePos → GamePos → Prop
  | prover {R Rs Γ Γs} :
      R ∈ SplitSequent.ruleApps Γ →
      Move ⟨Sum.inl Γ, Γs, Rs⟩ ⟨Sum.inr R, Γ :: Γs, Rs⟩
  | builder {R Rs Γ Γs} :
      Γ ∈ R.splitSequents →
      Γ ∉ Γs →
      Move ⟨Sum.inr R, Γs, Rs⟩ ⟨Sum.inl Γ, Γs, R :: Rs⟩

-- The FL-closure induction performs a large case split over split rule applications.
/-- Given two consecutive Prover moves, the latter move is in the FL closure of the prior. -/
theorem move_move_in_FL {g1 g2 : GamePos} (h1 : (g1.1.isLeft)) (h3 : (g2.1.isLeft))
    (g1_g2 : Relation.ReflTransGen (Relation.Comp Move Move) g1 g2) :
    g2.1.getLeft h3 ∈ (g1.1.getLeft h1).FL.powerset := by
  simp only [Finset.mem_powerset]
  induction g1_g2
  case refl => exact SplitSequent.FL_refl
  case tail g2 g3 g1_g2 g2_g3 ih =>
    have g2_g3 := by simpa [Relation.Comp] using g2_g3
    rcases g2_g3 with ⟨Γ', Γs', Rs', g2_g, g_g3⟩ | ⟨R', Γs', Rs', g2_g, g_g3⟩
    · rcases g3 with ⟨Γ'' | R'', Γs'', Rs''⟩ <;> simp at h3
      cases g_g3
    · rcases g3 with ⟨Γ'' | R'', Γs'', Rs''⟩ <;> simp at h3
      cases g_g3
      rcases g2 with ⟨Γ | R, Γs, Rs⟩ <;> cases g2_g
      simp_all only [Sum.isLeft_inl, Sum.getLeft_inl, List.mem_cons]
      specialize ih trivial
      rename_i Γ''_R' R'_Γ _
      have ih := SplitSequent.FL_mon ih
      have ih := by simpa [SplitSequent.FL_idem] using ih
      apply trans ?_ ih
      rcases R' <;>
        simp only [RuleApp.splitSequents, Finset.mem_singleton, Finset.notMem_empty,
          Finset.mem_insert] at Γ''_R'
      case orₗ Δ φ ψ in_Δ =>
        subst Γ''_R'
        have R'_Γ := by simpa [SplitSequent.ruleApps] using R'_Γ
        rcases R'_Γ with R'_Γ | R'_Γ
        · have ⟨φ, φ_in, h⟩ := R'_Γ
          rcases φ <;> simp at h <;> try grind
          simp only [h.1, SplitSequent.FL, Finset.subset_iff,
            Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion,
            Finset.mem_sdiff, Finset.mem_insert]
          intro χ χ_cases
          rcases χ_cases with h | h | h <;> subst_eqs
          · exact ⟨χ, h.1, SplitFormula.FL_refl⟩
          · exact ⟨Sum.inl (φ v ψ), in_Δ, by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
          · exact ⟨Sum.inl (φ v ψ), in_Δ, by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
        · have ⟨φ, φ_in, h⟩ := R'_Γ
          rcases φ <;> simp at h; grind
      case orᵣ Δ φ ψ in_Δ =>
        subst Γ''_R'
        have R'_Γ := by simpa [SplitSequent.ruleApps] using R'_Γ
        rcases R'_Γ with R'_Γ | R'_Γ
        · have ⟨φ, φ_in, h⟩ := R'_Γ
          rcases φ <;> simp at h; grind
        · have ⟨φ, φ_in, h⟩ := R'_Γ
          rcases φ <;> simp at h <;> try grind
          simp only [h.1, SplitSequent.FL, Finset.subset_iff,
            Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion,
            Finset.mem_sdiff, Finset.mem_insert]
          intro χ χ_cases
          rcases χ_cases with h | h | h <;> subst_eqs
          · exact ⟨χ, h.1, SplitFormula.FL_refl⟩
          · exact ⟨Sum.inr (φ v ψ), in_Δ, by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
          · exact ⟨Sum.inr (φ v ψ), in_Δ, by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
      case andₗ Δ φ ψ in_Δ =>
        rcases Γ''_R' with l | l <;> subst l
        all_goals
          have R'_Γ := by simpa [SplitSequent.ruleApps] using R'_Γ
          rcases R'_Γ with R'_Γ | R'_Γ
          · have ⟨φ, φ_in, h⟩ := R'_Γ
            rcases φ <;> simp at h <;> try grind
            simp only [h.1, SplitSequent.FL, Finset.subset_iff,
              Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion,
              Finset.mem_sdiff]
            intro χ χ_cases
            rcases χ_cases with h | h <;> subst_eqs
            · exact ⟨χ, h.1, SplitFormula.FL_refl⟩
            · exact ⟨Sum.inl (φ & ψ), in_Δ, by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
          · have ⟨φ, φ_in, h⟩ := R'_Γ
            rcases φ <;> simp at h; grind
      case andᵣ Δ φ ψ in_Δ =>
        rcases Γ''_R' with l | l <;> subst l
        all_goals
          have R'_Γ := by simpa [SplitSequent.ruleApps] using R'_Γ
          rcases R'_Γ with R'_Γ | R'_Γ
          · have ⟨φ, φ_in, h⟩ := R'_Γ
            rcases φ <;>
              simp only [Option.some.injEq, reduceCtorEq] at h
            grind
          · have ⟨φ, φ_in, h⟩ := R'_Γ
            rcases φ <;>
              simp only [Option.some.injEq, RuleApp.andᵣ.injEq, reduceCtorEq] at h <;>
                try grind
            simp only [h.1, SplitSequent.FL, Finset.subset_iff,
              Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion,
              Finset.mem_sdiff]
            intro χ χ_cases
            rcases χ_cases with h | h <;> subst_eqs
            · exact ⟨χ, h.1, SplitFormula.FL_refl⟩
            · exact ⟨Sum.inr (φ & ψ), in_Δ, by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
      case boxₗ Δ φ in_Δ =>
        subst Γ''_R'
        have R'_Γ := by simpa [SplitSequent.ruleApps] using R'_Γ
        rcases R'_Γ with R'_Γ | R'_Γ
        · have ⟨φ, φ_in, h⟩ := R'_Γ
          rcases φ <;> simp at h <;> try grind
          simp only [SplitSequent.D, Bool.decide_eq_true, Finset.union_singleton,
            SplitSequent.FL, h.1, Finset.subset_iff, Finset.mem_insert, Finset.mem_union,
            Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_filterMap,
            Sum.exists, Sum.inl.injEq, reduceCtorEq, not_false_eq_true, and_true,
            Finset.mem_biUnion, forall_eq_or_imp, Sum.forall, SplitSequent.opUnDi_eqₗₗ,
            exists_eq_right, SplitSequent.opUnDi_eqᵣₗ, and_false, exists_const, or_false,
            SplitSequent.opUnDi_eqₗᵣ, SplitSequent.opUnDi_eqᵣᵣ, false_or]
          refine
            ⟨Or.inl
              ⟨_, h.1 ▸ φ_in, by simp [SplitFormula.FL, h.2, SplitFormula.FL_refl]⟩,
              ?_, ?_⟩
          · intro χ χ_cases
            rcases χ_cases with h | h <;> subst_eqs
            · left
              exact ⟨χ, h.1.1, SplitFormula.FL_refl⟩
            · left
              exact ⟨◇ χ, h, by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
          · intro χ χ_cases
            rcases χ_cases with h | h <;> subst_eqs
            · right
              exact ⟨χ, h.1, SplitFormula.FL_refl⟩
            · right
              exact ⟨◇ χ, h, by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
        · have ⟨φ, φ_in, h⟩ := R'_Γ
          rcases φ <;> simp at h; grind
      case boxᵣ Δ φ in_Δ =>
        subst Γ''_R'
        have R'_Γ := by simpa [SplitSequent.ruleApps] using R'_Γ
        rcases R'_Γ with R'_Γ | R'_Γ
        · have ⟨φ, φ_in, h⟩ := R'_Γ
          rcases φ <;> simp at h; grind
        · have ⟨φ, φ_in, h⟩ := R'_Γ
          rcases φ <;> simp at h <;> try grind
          simp only [SplitSequent.D, Bool.decide_eq_true, Finset.union_singleton,
            SplitSequent.FL, h.1, Finset.subset_iff, Finset.mem_insert, Finset.mem_union,
            Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_filterMap,
            Sum.exists, reduceCtorEq, not_false_eq_true, and_true, Sum.inr.injEq,
            Finset.mem_biUnion, forall_eq_or_imp, Sum.forall, SplitSequent.opUnDi_eqₗₗ,
            exists_eq_right, SplitSequent.opUnDi_eqᵣₗ, and_false, exists_const, or_false,
            SplitSequent.opUnDi_eqₗᵣ, SplitSequent.opUnDi_eqᵣᵣ, false_or]
          refine
            ⟨Or.inr
              ⟨_, h.1 ▸ φ_in, by simp [SplitFormula.FL, h.2, SplitFormula.FL_refl]⟩,
              ?_, ?_⟩
          · intro χ χ_cases
            rcases χ_cases with h | h <;> subst_eqs
            · left
              exact ⟨χ, h.1, SplitFormula.FL_refl⟩
            · left
              exact ⟨◇ χ, h, by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
          · intro χ χ_cases
            rcases χ_cases with h|h <;> subst_eqs
            · right
              exact ⟨χ, h.1.1, SplitFormula.FL_refl⟩
            · right
              exact ⟨◇ χ, h, by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩

/- This is the main helper for showing there is no infinite chain, we do it 'from prover'
because that is where the FL properties are more readily available, but in fact it could
be from prover or builder. -/
lemma no_inf_chain_from_prover (g : ℕ → GamePos)
    (g_rel : ∀ (n : ℕ), Function.swap Move (g (n + 1)) (g n))
    (h : (g 0).1.isLeft) : False := by
  rcases g0_def : g 0 with ⟨Γ | R, Γs, Rs⟩ <;>
    simp only [g0_def, Sum.isLeft_inl, Sum.isLeft_inr, Bool.false_eq_true] at h
  have f_helper : ∀ n, (g (2 * n)).1.isLeft = true := by
    intro n
    induction n
    case zero => simp [g0_def]
    case succ k ih =>
      rcases g2k_def : g (2 * k) with ⟨Γ | R, Γs, Rs⟩ <;>
        simp_all only [Sum.isLeft_inl, Sum.isLeft_inr, Bool.false_eq_true]
      rcases g2k1_def : g (2 * k + 1) with ⟨Γ | R, Γs, Rs⟩
      · exfalso
        have := g_rel (2 * k)
        rw [g2k_def, g2k1_def] at this
        cases this
      · have := g_rel (2 * k)
        rw [g2k_def, g2k1_def] at this
        cases this
        rcases g2k2_def : g (2 * (k + 1)) with ⟨Γ | R, Γs, Rs⟩ <;>
          simp only [Sum.isLeft_inl, Sum.isLeft_inr, Bool.false_eq_true]
        have := g_rel (2 * k + 1)
        have h : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
        rw [g2k1_def, h, g2k2_def] at this
        cases this
  let f : ℕ → SplitSequent := fun n ↦ (g (2 * n)).1.getLeft (f_helper n)
  have g0_gn : ∀ n, Relation.ReflTransGen Move (g 0) (g n) := by
    intro n
    induction n
    case zero => exact Relation.ReflTransGen.refl
    case succ n ih => apply Relation.ReflTransGen.tail ih (g_rel n)
  have f_prop : ∀ n, f n ∈ Γ.FL.powerset := by
    intro n
    have := @move_move_in_FL (g 0) (g (2 * n)) (f_helper 0) (f_helper n) (by
      induction n
      case zero =>
        simpa only [mul_zero] using Relation.ReflTransGen.refl
      case succ n ih =>
        apply Relation.ReflTransGen.tail ih
        refine ⟨g (2 * n + 1), g_rel (2 * n), ?_⟩
        have := g_rel (2 * n + 1)
        have this := by simpa [Function.swap] using this
        grind)
    unfold f
    simp only [g0_def] at this
    exact this
  let sequents : (n : ℕ) → List SplitSequent := Nat.rec [] (fun n ih => f n :: ih)
  have seq_prop : ∀ n, sequents n ++ Γs = (g (2 * n)).2.1 := by
    intro n
    induction n
    case zero => simp [sequents, g0_def]
    case succ k ih =>
      unfold sequents f at *
      have := f_helper k
      rcases g2k_def : g (2 * k) with ⟨Γ | R, Γs, Rs⟩ <;>
        simp_all only [Finset.mem_powerset, Sum.isLeft_inl, Sum.getLeft_inl,
          List.cons_append, Sum.isLeft_inr, Bool.false_eq_true]
      · rcases g2k1_def : g (2 * k + 1) with ⟨Γ | R, Γs, Rs⟩
        · exfalso
          have := g_rel (2 * k)
          rw [g2k_def, g2k1_def] at this
          cases this
        · have := g_rel (2 * k)
          rw [g2k_def, g2k1_def] at this
          cases this
          rcases g2k2_def : g (2 * (k + 1)) with ⟨Γ | R, Γs, Rs⟩
          · have := g_rel (2 * k + 1)
            have h : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
            rw [g2k1_def, h, g2k2_def] at this
            cases this
            simp
          · have := g_rel (2 * k + 1)
            have h : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
            rw [g2k1_def, h, g2k2_def] at this
            cases this
  have seq_prop2 : ∀ n m, n < m → f n ∈ sequents m := by
    intro n m n_m
    induction m
    case zero => simp at n_m
    case succ m ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 n_m with lt | eq
      · simp_all [sequents]
      · subst eq
        simp [sequents]
  have inf : Infinite {Δ // Δ ∈ Γ.FL.powerset} := by
    apply Infinite.of_injective (fun n ↦ ⟨f n, f_prop n⟩)
    intro n1 n2 hyp
    rcases Nat.lt_trichotomy n1 n2 with lt | eq | gt
    · exfalso
      have in_seq := seq_prop2 _ _ lt
      have := g_rel (2 * n2 - 1)
      rcases g2k2_def : g (2 * n2) with ⟨Γ | R, Γs, Rs⟩ <;> try grind
      have h : 2 * n2 - 1 + 1 = 2 * n2 := by grind
      rw [h, g2k2_def] at this
      rcases g2k21_def : g (2 * n2 - 1) with ⟨Γ | R, Γs, Rs⟩
      · rw [g2k21_def] at this
        cases this
      · rw [g2k21_def] at this
        cases this
        case builder not_in =>
          apply not_in
          have h : f n2 = Γ := by unfold f; simp [g2k2_def]
          have := seq_prop n2
          have hyp := by simpa using hyp
          have this := by simpa [g2k2_def] using this
          simp [← this, ← h, ← hyp, in_seq]
    · exact eq
    · exfalso
      have in_seq := seq_prop2 _ _ gt
      have := g_rel (2 * n1 - 1)
      rcases g2k2_def : g (2 * n1) with ⟨Γ | R, Γs, Rs⟩ <;> try grind
      have h : 2 * n1 - 1 + 1 = 2 * n1 := by grind
      rw [h, g2k2_def] at this
      rcases g2k21_def : g (2 * n1 - 1) with ⟨Γ | R, Γs, Rs⟩
      · rw [g2k21_def] at this
        cases this
      · rw [g2k21_def] at this
        cases this
        case builder not_in =>
          apply not_in
          have h : f n1 = Γ := by unfold f; simp [g2k2_def]
          have := seq_prop n1
          have hyp := by simpa using hyp
          have this := by simpa [g2k2_def] using this
          simp [← this, ← h, hyp, in_seq]
  apply inf.not_finite
  apply Set.finite_coe_iff.1
  apply Finset.finite_toSet

/-- The game is converse well-founded. -/
lemma matches_finite : WellFounded (Function.swap Move) := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  by_contra hyp
  have hyp := by simpa using hyp
  rcases hyp with ⟨g, g_rel⟩
  simp only [Function.swap] at g_rel
  rcases g0_def : g 0 with ⟨Γ | R, Γs, Rs⟩
  · apply no_inf_chain_from_prover g g_rel (by simp_all)
  · have := g_rel 0
    rcases g1_def : g 1 with ⟨Γ | R, Γs, Rs⟩
    · simp only [g0_def, zero_add, g1_def] at this
      cases this
      apply no_inf_chain_from_prover (fun n ↦ g (n + 1)) (fun n ↦ g_rel (n + 1)) (by simp_all)
    · simp only [g0_def, zero_add, g1_def] at this
      cases this

/-- Auxiliary declaration used in the GL coalgebra development. -/
@[reducible]
def coalgebraGame : Game where
  Pos := GamePos -- = (SplitSequent ⊕ RuleApp) × List SplitSequent × List RuleApp
  turn
    | ⟨Sum.inl _, _, _⟩ => Prover -- picks RuleApp
    | ⟨Sum.inr _, _, _⟩ => Builder -- picks SplitSequent
  moves
    | ⟨Sum.inl Γ, Γs, Rs⟩ =>
        Finset.map
          ⟨fun R ↦ ⟨Sum.inr R, Γ :: Γs, Rs⟩, by
            intro r1 r2
            simp⟩
          (SplitSequent.ruleApps Γ)
    | ⟨Sum.inr R, Γs, Rs⟩ =>
        Finset.filterMap
          (fun Γ ↦ if Γ ∈ Γs then none else some ⟨Sum.inl Γ, Γs, R :: Rs⟩)
          R.splitSequents
          (by grind)
  wf := ⟨fun x y ↦ Move y x, matches_finite⟩
  move_rel := by
    intro ⟨info, Γs, Rs⟩ ⟨info', Γs', Rs'⟩ hyp
    rcases info with Γ | R
    · simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Prod.mk.injEq] at hyp
      have ⟨R, R_prop, eq1, eq2, eq3⟩ := hyp
      subst_eqs
      simp only
      exact Move.prover R_prop
    · simp only [Finset.mem_filterMap, Option.ite_none_left_eq_some, Option.some.injEq,
        Prod.mk.injEq] at hyp
      have ⟨Γ, Γ_prop, nin, eq1, eq2, eq3⟩ := hyp
      subst_eqs
      simp only
      exact Move.builder Γ_prop nin

/-- Move relation and being in the set of game moves are equivalent. -/
theorem move_iff_in_moves {g g' : coalgebraGame.Pos} :
    Move g g' ↔ g' ∈ coalgebraGame.moves g := by
  constructor
  · intro g_g'
    unfold Game.moves
    simp only
    cases g_g'
    case prover R Rs Γ Γs R_mem =>
      exact (Finset.mem_map).mpr ⟨R, R_mem, rfl⟩
    case builder R Rs Γ Γs Γ_mem Γ_not_mem =>
      exact (Finset.mem_filterMap _).mpr
        ⟨Γ, Γ_mem, by simp [Γ_not_mem]⟩
  · intro in_moves
    exact @coalgebraGame.move_rel g g' in_moves

/-- Auxiliary declaration used in the GL coalgebra development. -/
abbrev startPos (Γ : SplitSequent) : GamePos := ⟨Sum.inl Γ, [], []⟩

end Split
end Lean4GlCoalgebras
