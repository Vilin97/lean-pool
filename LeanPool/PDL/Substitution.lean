/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import LeanPool.PDL.Discon

/-!
# Substitution and Helper Lemmas

The lemmas here are mostly from Sections 2.1 and 2.2.
-/

@[expose] public section

namespace PDL

/-! ## Single-step replacing -/

mutual
  /-- Replace atomic proposition `x` by `ψ` in a formula. -/
  @[simp]
  def replInF (x : Nat) (ψ : Formula) : Formula → Formula
    | ⊥ => ⊥
    | ·c => if c == x then ψ else ·c
    | ~φ => ~ replInF x ψ φ
    | φ1⋀φ2 => (replInF x ψ) φ1 ⋀ (replInF x ψ) φ2
    | ⌈α⌉ φ => ⌈replInP x ψ α⌉ (replInF x ψ φ)
  /-- Replace atomic proposition `x` by `ψ` in a program. -/
  @[simp]
  def replInP (x : Nat) (ψ : Formula) : Program → Program
    | ·c => ·c
    | α;'β  => (replInP x ψ α) ;' (replInP x ψ β)
    | α⋓β  => (replInP x ψ α) ⋓ (replInP x ψ β)
    | ∗α  => ∗(replInP x ψ α)
    | ?'φ  => ?' (replInF x ψ φ)
end

-- Reopen namespaces after mutual blocks to keep source-based declaration audits aligned.
end PDL

namespace PDL

theorem repl_in_con : replInF x ψ (con l) = con (l.map (replInF x ψ)) := by
  cases l
  · simp [Top.top, Bot.bot]
  case cons φ1 l =>
    cases l
    · simp
    case cons φ2 l =>
      simp only [con, replInF, List.map_cons, Formula.and.injEq, true_and]
      apply repl_in_con

theorem repl_in_or : replInF x ψ (φ1 ⋁ φ2) = replInF x ψ φ1 ⋁ replInF x ψ φ2 := by
  simp

theorem repl_in_dis : replInF x ψ (dis l) = dis (l.map (replInF x ψ)) := by
  cases l
  · simp
  case cons φ1 l =>
    cases l
    · simp
    case cons φ2 l =>
      simp only [dis, Formula.or, replInF, List.map_cons, Formula.neg.injEq, Formula.and.injEq,
        true_and]
      apply repl_in_dis

mutual
theorem repl_in_F_non_occ_eq {x φ ρ} :
    (Sum.inl x) ∉ φ.voc → replInF x ρ φ = φ := by
  intro x_notin_phi
  cases φ
  case bottom => simp [Bot.bot]
  case atom_prop c =>
    simp only [replInF, beq_iff_eq, ite_eq_right_iff]
    intro c_is_x; simp only [Formula.voc, Finset.mem_singleton, Sum.inl.injEq] at *; subst_eqs;
      tauto
  case neg φ0 =>
    simp only [Formula.voc, replInF, Formula.neg.injEq] at *
    apply repl_in_F_non_occ_eq; tauto
  case and φ1 φ2 =>
    simp only [Formula.voc, Finset.mem_union, not_or, replInF, Formula.and.injEq] at *
    constructor <;> (apply repl_in_F_non_occ_eq ; tauto)
  case box α φ0 =>
    simp only [Formula.voc, Finset.mem_union, not_or, replInF, Formula.box.injEq] at *
    constructor
    · apply repl_in_P_non_occ_eq; tauto
    · apply repl_in_F_non_occ_eq; tauto

theorem repl_in_P_non_occ_eq {x α ρ} :
    (Sum.inl x) ∉ α.voc → replInP x ρ α = α := by
  intro x_notin_alpha
  cases α
  all_goals simp only [Program.voc, Finset.mem_singleton, reduceCtorEq, not_false_eq_true,
    replInP, Finset.mem_union, not_or, Program.sequence.injEq, Program.union.injEq,
    Program.star.injEq, Program.test.injEq] at *
  case sequence β γ =>
    constructor <;> (apply repl_in_P_non_occ_eq; tauto)
  case union β γ =>
    constructor <;> (apply repl_in_P_non_occ_eq; tauto)
  case star β =>
    apply repl_in_P_non_occ_eq; tauto
  case test φ =>
    apply repl_in_F_non_occ_eq; tauto
end

end PDL

namespace PDL

theorem repl_in_boxes_non_occ_eq_neg (δ : List Program) :
    (Sum.inl x) ∉ Vocab.fromList (δ.map Program.voc) → replInF x ψ (⌈⌈δ⌉⌉~·x) = ⌈⌈δ⌉⌉~ψ := by
  intro nonOcc
  induction δ
  · simp
  case cons α δ IH =>
    simp only [Formula.boxes, List.foldr_cons, replInF, Formula.box.injEq]
    constructor
    · apply repl_in_P_non_occ_eq
      simp_all [Vocab.fromList]
    · apply IH
      clear IH
      simp_all [Vocab.fromList]

theorem repl_in_boxes_non_occ_eq_pos (δ : List Program) :
    (Sum.inl x) ∉ Vocab.fromList (δ.map Program.voc) → replInF x ψ (⌈⌈δ⌉⌉·x) = ⌈⌈δ⌉⌉ψ := by
  intro nonOcc
  induction δ
  · simp
  case cons α δ IH =>
    simp only [Formula.boxes, List.foldr_cons, replInF, Formula.box.injEq]
    constructor
    · apply repl_in_P_non_occ_eq
      simp_all [Vocab.fromList]
    · apply IH
      clear IH
      simp_all [Vocab.fromList]

theorem repl_in_list_non_occ_eq (F : List Formula) :
     (Sum.inl x) ∉ Vocab.fromList (F.map Formula.voc) → F.map (replInF x ρ) = F := by
  intro nonOcc
  induction F
  · simp
  case cons φ F IH =>
    simp only [List.map_cons, List.cons.injEq]
    constructor
    · apply repl_in_F_non_occ_eq
      simp only [Vocab.fromList, Finset.mem_sup, List.mem_toFinset, List.mem_map, id_eq,
        exists_exists_and_eq_and, not_exists, not_and, List.map_cons, List.toFinset_cons,
        Finset.sup_insert, Finset.sup_eq_union', Finset.mem_union, not_or] at *
      exact nonOcc.left
    · apply IH
      clear IH
      simp_all [Vocab.fromList]

mutual
lemma repl_in_F_voc_def p φ ψ :
    (replInF p φ ψ).voc = (ψ.voc \ {Sum.inl p}) ∪ (if Sum.inl p ∈ ψ.voc then φ.voc else {}) := by
  cases ψ <;> simp only [replInF, Formula.voc, Finset.empty_sdiff, Finset.notMem_empty,
    ↓reduceIte, Finset.union_idempotent, beq_iff_eq, Finset.mem_singleton, Sum.inl.injEq,
    Finset.mem_union]
  case atom_prop q => by_cases q = p <;> aesop
  case neg => apply repl_in_F_voc_def
  case and ψ1 ψ2 =>
    ext x
    have := repl_in_F_voc_def p φ ψ1
    have := repl_in_F_voc_def p φ ψ2
    aesop
  case box α ψ =>
    ext x
    have := repl_in_F_voc_def p φ ψ
    have := repl_in_P_voc_def p φ α
    aesop

lemma repl_in_P_voc_def p φ α :
    (replInP p φ α).voc = (α.voc \ {Sum.inl p}) ∪ (if Sum.inl p ∈ α.voc then φ.voc else {}) := by
  cases α <;> simp only [replInP, Program.voc, Finset.mem_singleton, reduceCtorEq, ↓reduceIte,
    Finset.union_empty, Finset.mem_union]
  case atom_prog =>
    rfl
  case sequence α β =>
    ext x
    have := repl_in_P_voc_def p φ α
    have := repl_in_P_voc_def p φ β
    aesop
  case union α β =>
    ext x
    have := repl_in_P_voc_def p φ α
    have := repl_in_P_voc_def p φ β
    aesop
  case test τ =>
    ext x
    have := repl_in_F_voc_def p φ τ
    simp_all only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
    grind
  case star α =>
    ext x
    have := repl_in_P_voc_def p φ α
    simp_all only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
    grind
end

end PDL

namespace PDL

/-- Overwrite the valuation of `x` with the current value of `ψ` in a model. -/
def replInModel (x : Nat) (ψ : Formula) : KripkeModel W → KripkeModel W
| M@⟨V,R⟩ => ⟨fun w c => if c == x then (M,w) ⊨ ψ else V w c,R⟩

mutual
theorem repl_in_model_sat_iff x ψ φ {W} (M : KripkeModel W) (w : W) :
    (M, w) ⊨ replInF x ψ φ ↔ (replInModel x ψ M, w) ⊨ φ := by
  cases φ
  case bottom =>
    simp [evaluatePoint, vDash.SemImplies]
  case atom_prop c =>
    simp [evaluatePoint, vDash.SemImplies, evaluate, replInModel]
    aesop
  case neg φ =>
    have IH := repl_in_model_sat_iff x ψ φ M w
    simp [evaluatePoint, vDash.SemImplies] at *
    tauto
  case and φ1 φ2 =>
    have IH1 := repl_in_model_sat_iff x ψ φ1 M w
    have IH2 := repl_in_model_sat_iff x ψ φ2 M w
    simp only [vDash.SemImplies, evaluatePoint, replInF, evaluate] at *
    rw [IH1, IH2]
  case box α φ =>
    have IHα := repl_in_model_rel_iff x ψ α M w
    simp only [vDash.SemImplies, evaluatePoint, replInF, evaluate] at *
    constructor
    all_goals
      intro hyp v rel
      have IHφ := repl_in_model_sat_iff x ψ φ M v
      specialize IHα v
      specialize hyp v
      tauto

theorem repl_in_model_rel_iff x ψ α {W} (M : KripkeModel W) (w v : W) :
    relate M (replInP x ψ α) w v ↔ relate (replInModel x ψ M) α w v := by
  cases α
  case atom_prog a =>
    simp [replInModel]
  case sequence α β =>
    have IHα := repl_in_model_rel_iff x ψ α M
    have IHβ := repl_in_model_rel_iff x ψ β M
    simp_all only [replInP, relate]
  case union α β =>
    have IHα := repl_in_model_rel_iff x ψ α M
    have IHβ := repl_in_model_rel_iff x ψ β M
    simp_all only [replInP, relate]
  case star α =>
    have IHα := repl_in_model_rel_iff x ψ α M
    simp_all only [replInP, relate]
    constructor
    all_goals
      apply Relation.ReflTransGen.mono
      intro w v
      rw [IHα w v]
  case test φ =>
    have IHφ := repl_in_model_sat_iff x ψ φ M v
    simp only [replInP, relate, and_congr_right_iff] at *
    intro w_is_v
    subst w_is_v
    exact IHφ
end

end PDL

namespace PDL

theorem repl_in_F_equiv x ψ :
    (φ1 ≡ φ2) → (replInF x ψ φ1) ≡ (replInF x ψ φ2) := by
  intro hyp W M w
  have claim1 := repl_in_model_sat_iff x ψ φ1 M w
  have claim2 := repl_in_model_sat_iff x ψ φ2 M w
  simp only [evaluatePoint, vDash.SemImplies] at *
  rw [claim1]
  rw [claim2]
  have := @equiv_iff φ1 φ2 hyp W (replInModel x ψ M) w
  simp only [evaluatePoint, vDash.SemImplies] at *
  exact this

theorem repl_in_P_equiv x ψ :
    (α1 ≡ᵣ α2) → (replInP x ψ α1) ≡ᵣ (replInP x ψ α2) := by
  intro hyp W M w v
  have claim1 := repl_in_model_rel_iff x ψ α1 M w v
  have claim2 := repl_in_model_rel_iff x ψ α2 M w v
  rw [claim1]
  rw [claim2]
  apply hyp

theorem repl_in_disMap x ρ (L : List α) (p : α → Prop) (f : α → Formula) [DecidablePred p] :
    replInF x ρ (dis (L.map (fun Fδ => if p Fδ then Formula.bottom else f Fδ))) =
    dis (L.map (fun Fδ => if p Fδ then Formula.bottom else replInF x ρ (f Fδ))) := by
  rw [repl_in_dis, listEq_to_disEq]
  simp only [List.map_map]
  aesop

/-! ## Cancellation of replacements -/

mutual
/-- Replacing `p` with a fresh `q` and then replacing `q` by `p` results in the same formula. -/
@[simp]
lemma repl_in_F_cancel_via_non_occ φ p q : Sum.inl q ∉ φ.voc →
    replInF q (·p) (replInF p (·q) φ) = φ := by
  intro q_not_in_ψ
  cases φ <;> simp_all only [Formula.voc, Finset.notMem_empty, not_false_eq_true, replInF,
    Bot.bot, Finset.mem_singleton, Sum.inl.injEq, beq_iff_eq, Formula.neg.injEq, Finset.mem_union,
    not_or, Formula.and.injEq, Formula.box.injEq]
  case atom_prop q =>
    by_cases q = p <;> aesop
  case neg φ =>
    have := repl_in_F_cancel_via_non_occ φ p q
    aesop
  case and φ1 φ2 =>
    have := repl_in_F_cancel_via_non_occ φ1 p q
    have := repl_in_F_cancel_via_non_occ φ2 p q
    aesop
  case box α φ =>
    have := repl_in_F_cancel_via_non_occ φ p q
    have := repl_in_P_cancel_via_non_occ α p q
    aesop
/-- Replacing `p` with a fresh `q` and then replacing `q` by `p` results in the same program. -/
lemma repl_in_P_cancel_via_non_occ α p q : Sum.inl q ∉ α.voc →
    replInP q (·p) (replInP p (·q) α) = α := by
  intro q_not_in_α
  cases α <;> simp_all only [Program.voc, Finset.mem_singleton, reduceCtorEq, not_false_eq_true,
    replInP, Finset.mem_union, not_or, Program.sequence.injEq, Program.union.injEq,
    Program.star.injEq, Program.test.injEq]
  case sequence α1 α2 =>
    have := repl_in_P_cancel_via_non_occ α1 p q
    have := repl_in_P_cancel_via_non_occ α2 p q
    aesop
  case union α1 α2 =>
    have := repl_in_P_cancel_via_non_occ α1 p q
    have := repl_in_P_cancel_via_non_occ α2 p q
    aesop
  case test τ =>
    have := repl_in_F_cancel_via_non_occ τ p q
    aesop
  case star α =>
    have := repl_in_P_cancel_via_non_occ α p q
    aesop
end

end PDL

namespace PDL

/-! ## Replacement of atoms in tautologies -/

/-- Replacing an atom in a tautology results in a tautology. -/
lemma taut_repl φ p q :
    tautology φ → tautology (replInF p (·q) φ) := by
  intro taut_φ W M w
  have := repl_in_model_sat_iff p (·q) φ M w
  simp only [vDash.SemImplies, evaluatePoint] at this
  rw [this]
  apply taut_φ

/-- A special case of `taut_repl` for the proof of `beth`. -/
lemma non_occ_taut_then_taut_repl_in_imp (φ ψ : Formula) (p q : ℕ) :
    Sum.inl p ∉ ψ.voc → tautology (φ ↣ ψ) → tautology (replInF p (·q) φ ↣ ψ) := by
  intro p_not_in_ψ taut_imp W M w
  simp only [evaluate, not_and, not_not]
  intro w_φ
  have := taut_repl _ p q taut_imp W M w
  clear taut_imp
  simp only [replInF, evaluate, not_and, not_not] at this
  specialize this w_φ
  clear w_φ
  rw [repl_in_F_non_occ_eq] at this <;> assumption

/-- Another special case of `taut_repl` for the proof of `beth`. -/
lemma non_occ_taut_then_taut_imp_repl_in (φ ψ : Formula) (p q : ℕ) :
    Sum.inl p ∉ ψ.voc → tautology (ψ ↣ φ) → tautology (ψ ↣ replInF p (·q) φ) := by
  intro p_not_in_ψ taut_imp W M w
  simp only [evaluate, not_and, not_not]
  intro w_ψ
  have := taut_repl _ p q taut_imp W M w
  clear taut_imp
  simp only [replInF, evaluate, not_and, not_not] at this
  apply this
  rw [repl_in_F_non_occ_eq] <;> assumption

/-! ## Simultaneous Substitutions -/

/-- A substitution assigning a formula to each atomic proposition. -/
abbrev Substitution := Nat → Formula

mutual
  /-- Apply substitution `σ` to formula `φ`. -/
  @[simp]
  def substInF (σ : Substitution) : (φ : Formula) → Formula
    | ⊥ => ⊥
    | ·c => σ c
    | ~φ => ~(substInF σ φ)
    | φ1⋀φ2 => (substInF σ) φ1 ⋀ (substInF σ) φ2
    | ⌈α⌉ φ => ⌈substInP σ α⌉ (substInF σ φ)
  /-- Apply substitution `σ` to program `α`. -/
  @[simp]
  def substInP (σ : Substitution) : (α : Program) → Program
    | ·c => ·c
    | α;'β  => (substInP σ α) ;' (substInP σ β)
    | α⋓β  => (substInP σ α) ⋓ (substInP σ β)
    | ∗α  => ∗(substInP σ α)
    | ?'φ  => ?' (substInF σ φ)
end

end PDL

namespace PDL

/-- Overwrite the valuation in `M` with the substitution `σ`. -/
def substInModel (σ : Substitution) : (M : KripkeModel W) → KripkeModel W
| M@⟨_, R⟩ => ⟨fun w c => (M,w) ⊨ σ c, R⟩

mutual
theorem substitutionLemma σ φ {W} (M : KripkeModel W) (w : W) :
    (M, w) ⊨ substInF σ φ ↔ (substInModel σ M, w) ⊨ φ := by
  cases φ
  case bottom =>
    simp [evaluatePoint, vDash.SemImplies]
  case atom_prop c =>
    simp [evaluatePoint, vDash.SemImplies, evaluate, substInModel]
  case neg φ =>
    have IH := substitutionLemma σ φ M w
    simp [evaluatePoint, vDash.SemImplies] at *
    tauto
  case and φ1 φ2 =>
    have IH1 := substitutionLemma σ φ1 M w
    have IH2 := substitutionLemma σ φ2 M w
    simp only [vDash.SemImplies, evaluatePoint, substInF, evaluate] at *
    rw [IH1, IH2]
  case box α φ =>
    have IHα := substitutionLemmaRel σ α M w
    simp only [vDash.SemImplies, evaluatePoint, substInF, evaluate] at *
    constructor
    all_goals
      intro hyp v rel
      have IHφ := substitutionLemma σ φ M v
      specialize IHα v
      specialize hyp v
      tauto

theorem substitutionLemmaRel (σ : Substitution) α {W} (M : KripkeModel W) (w v : W) :
    relate M (substInP σ α) w v ↔ relate (substInModel σ M) α w v := by
  cases α
  case atom_prog a =>
    simp [substInModel]
  case sequence α β =>
    have IHα := substitutionLemmaRel σ α M
    have IHβ := substitutionLemmaRel σ β M
    simp_all only [substInP, relate]
  case union α β =>
    have IHα := substitutionLemmaRel σ α M
    have IHβ := substitutionLemmaRel σ β M
    simp_all only [substInP, relate]
  case star α =>
    have IHα := substitutionLemmaRel σ α M
    simp_all only [substInP, relate]
    constructor
    all_goals
      apply Relation.ReflTransGen.mono
      intro w v
      rw [IHα w v]
  case test φ =>
    have IHφ := substitutionLemma σ φ M v
    simp only [substInP, relate, and_congr_right_iff] at *
    intro w_is_v
    subst w_is_v
    exact IHφ
end

end PDL

namespace PDL

/-! ## Semantic Equivalents

The following does *not* hold in general, because `frm` might be sneaky:
`theorem wrong_equiv_repl φ1 φ2 (h : φ1 ≡ φ2) (frm : Formula → Formula) : frm φ1 ≡ frm φ2 := by ...`
-/

/-- A true instance of `wrong_equiv_repl`, here we replaced `frm` with a special case. -/
theorem equiv_con {φ1 φ2} (h : φ1 ≡ φ2) ψ :
    φ1 ⋀ ψ ≡ φ2 ⋀ ψ := by
  intro W M w
  specialize h W M w
  simp_all

end PDL
