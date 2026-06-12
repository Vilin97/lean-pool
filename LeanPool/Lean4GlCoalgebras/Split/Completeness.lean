/-
Copyright (c) 2026 Madeleine Gignoux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madeleine Gignoux
-/

import LeanPool.Lean4GlCoalgebras.Split.Soundness
import LeanPool.Lean4GlCoalgebras.Split.Game

/-! ## Prover winning the GL-split game builds a GL-split proof.

If Prover has a winning strategy in the game starting from `Γ`, then there is a proof
of `Γ`, proven in `prover_win_builds_proof`; all other definitions and proofs in this
file are helpers. -/

namespace Lean4GlCoalgebras

namespace Split

private lemma left_diamond_mem_D_of_ne {Γ : SplitSequent} {φ : Formula} {χ : SplitFormula}
    (h : Sum.inl (◇φ) ∈ Γ) (hne : Sum.inl (◇φ) ≠ χ) :
    Sum.inl (◇φ) ∈ (Γ \ {χ}).D := by
  simp [SplitSequent.D, SplitFormula.isDiamond, h, hne]

private lemma right_diamond_mem_D_of_ne {Γ : SplitSequent} {φ : Formula} {χ : SplitFormula}
    (h : Sum.inr (◇φ) ∈ Γ) (hne : Sum.inr (◇φ) ≠ χ) :
    Sum.inr (◇φ) ∈ (Γ \ {χ}).D := by
  simp [SplitSequent.D, SplitFormula.isDiamond, h, hne]

private lemma left_unDi_mem_D_of_ne {Γ : SplitSequent} {φ : Formula} {χ : SplitFormula}
    (h : Sum.inl (◇φ) ∈ Γ) (hne : Sum.inl (◇φ) ≠ χ) :
    Sum.inl φ ∈ (Γ \ {χ}).D := by
  rw [SplitSequent.D]
  apply Finset.mem_union.mpr
  right
  simp only [Finset.mem_filterMap]
  use Sum.inl (◇φ)
  constructor
  · simp [h, hne]
  · simp [SplitFormula.opUnDi]

private lemma right_unDi_mem_D_of_ne {Γ : SplitSequent} {φ : Formula} {χ : SplitFormula}
    (h : Sum.inr (◇φ) ∈ Γ) (hne : Sum.inr (◇φ) ≠ χ) :
    Sum.inr φ ∈ (Γ \ {χ}).D := by
  rw [SplitSequent.D]
  apply Finset.mem_union.mpr
  right
  simp only [Finset.mem_filterMap]
  use Sum.inr (◇φ)
  constructor
  · simp [h, hne]
  · simp [SplitFormula.opUnDi]

/-- Rewinding the history one step to get previous move. -/
def rewindHistoryOneStep
    (g : coalgebraGame.Pos)
    (h :
      coalgebraGame.turn g = Prover ∧ g.2.2 ≠ ∅ ∨
        coalgebraGame.turn g = Builder ∧ g.2.1 ≠ ∅) : coalgebraGame.Pos :=
  match g with
  | ⟨Sum.inl Γ, Γs, Rs⟩ =>
      ⟨Sum.inr (Rs.head (by
        rcases h with h | h
        · exact h.2
        · cases h.1)), Γs, Rs.tail⟩
  | ⟨Sum.inr R, Γs, Rs⟩ =>
      ⟨Sum.inl (Γs.head (by
        rcases h with h | h
        · cases h.1
        · exact h.2)), Γs.tail, Rs⟩

lemma rewind_history_one_step_of_move {q g : coalgebraGame.Pos} (mv : Move q g)
    (h : coalgebraGame.turn g = Prover ∧ g.2.2 ≠ ∅ ∨
      coalgebraGame.turn g = Builder ∧ g.2.1 ≠ ∅) :
    rewindHistoryOneStep g h = q := by
  cases mv <;> simp [rewindHistoryOneStep]

/-- Rewinding the history one step is still in the cone of the game. -/
lemma rewind_history_one_step_in_cone {Γ} (g : coalgebraGame.Pos)
    (h :
      coalgebraGame.turn g = Prover ∧ g.2.2 ≠ ∅ ∨
        coalgebraGame.turn g = Builder ∧ g.2.1 ≠ ∅)
    (strat : Strategy coalgebraGame Prover) (in_cone : inMyCone strat (startPos Γ) g) :
    inMyCone strat (startPos Γ) (rewindHistoryOneStep g h) := by
  cases in_cone
  case nil =>
    rcases h with h | h
    · exact (h.2 rfl).elim
    · cases h.1
  case myStep q q_in_cone q_has_moves P_turn_q =>
    rw [rewind_history_one_step_of_move
      (move_iff_in_moves.2 (strat q P_turn_q q_has_moves).2) h]
    exact q_in_cone
  case oStep q q_in_cone B_turn_q g_in_moves_q =>
    rw [rewind_history_one_step_of_move (move_iff_in_moves.2 g_in_moves_q) h]
    exact q_in_cone

/-- Rewinding the history `n` steps. -/
def rewindHistory
    (g : coalgebraGame.Pos)
    (n : Fin
      ((if coalgebraGame.turn g = Prover then
          min (2 * g.2.1.length + 1) (2 * g.2.2.length)
        else
          min (2 * g.2.1.length) (2 * g.2.2.length + 1)) + 1)) :
    coalgebraGame.Pos :=
  match n_def : n.1 with
    | 0 => g
    | m + 1 => rewindHistory (rewindHistoryOneStep g (by
      rcases g with ⟨Γ | R, Γs, Rs⟩
      · left
        constructor
        · rfl
        · intro hRs
          subst hRs
          have n_lt := n.2
          change n.1 < min (2 * Γs.length + 1) (2 * ([] : List RuleApp).length) + 1 at n_lt
          simp only [List.length_nil, mul_zero] at n_lt
          omega
      · right
        constructor
        · rfl
        · intro hΓs
          subst hΓs
          have n_lt := n.2
          change n.1 < min (2 * ([] : List SplitSequent).length) (2 * Rs.length + 1) + 1 at n_lt
          simp only [List.length_nil, mul_zero] at n_lt
          omega)) ⟨m, by
            have ⟨n_val, n_prop⟩ := n
            simp_all only [Nat.lt_add_one_iff, ge_iff_le]
            rcases g with ⟨Γ | R, Γs, Rs⟩ <;>
              simp_all only [rewindHistoryOneStep, reduceCtorEq, ↓reduceIte,
                List.length_tail, le_inf_iff]
            · have hm : n_val = m + 1 := by simpa using n_def
              change n_val < min (2 * Γs.length + 1) (2 * Rs.length) + 1 at n_prop
              constructor <;> omega
            · change m ≤ min (2 * (Γs.length - 1) + 1) (2 * Rs.length)
              have hm : n_val = m + 1 := by simpa using n_def
              change n_val < min (2 * Γs.length) (2 * Rs.length + 1) + 1 at n_prop
              omega⟩
termination_by n.1
decreasing_by
  omega

/-- Rewinding the history `n` steps is still in the cone of the game. -/
lemma rewind_history_in_cone {Γ} (g : coalgebraGame.Pos)
    (n : Fin
      ((if coalgebraGame.turn g = Prover then
          min (2 * g.2.1.length + 1) (2 * g.2.2.length)
        else
          min (2 * g.2.1.length) (2 * g.2.2.length + 1)) + 1))
    (strat : Strategy coalgebraGame Prover) (in_cone : inMyCone strat (startPos Γ) g) :
    inMyCone strat (startPos Γ) (rewindHistory g n) := by
  unfold rewindHistory
  split
  · exact in_cone
  · apply rewind_history_in_cone
    apply rewind_history_one_step_in_cone
    exact in_cone

@[simp]
lemma rewind_history_zero (g : coalgebraGame.Pos) : rewindHistory g 0 = g := by
  simp [rewindHistory]

/-- This is the type of the coalgebra we will use to build the proof of `Γ`. -/
def proof_type (Γ : SplitSequent) (strat : Strategy coalgebraGame Prover) :=
 {g // inMyCone strat (startPos Γ) g ∧ coalgebraGame.turn g = Builder}

/-- Auxiliary declaration used in the GL coalgebra development. -/
def builderRuleApp (g : coalgebraGame.Pos) (h : coalgebraGame.turn g = Builder) :
    RuleApp := match g with
  | ⟨Sum.inr R, _, _⟩ => R
  | ⟨Sum.inl _, _, _⟩ => False.elim (by
    change Prover = Builder at h
    cases h)

/-- Defines the premise when we do not have a repeat. -/
def nextNext {Γ Δ : SplitSequent} {strat : Strategy coalgebraGame Prover}
    (g : proof_type Γ strat)
    (h : winning strat (startPos Γ)) (nrep : Δ ∉ g.1.2.1)
    (pos : Δ ∈ (builderRuleApp g.1 g.2.2).splitSequents) : proof_type Γ strat :=
  let next : GamePos := ⟨Sum.inl <| Δ, g.1.2.1, builderRuleApp g.1 g.2.2 :: g.1.2.2⟩
  have P_next : coalgebraGame.turn next = Prover := by
    unfold Game.turn next
    simp
  have next_in_moves : next ∈ coalgebraGame.moves g.1 := by
    rcases g with ⟨⟨Γ | R, Γs, Rs⟩, _, b_move⟩
    · change Prover = Builder at b_move
      cases b_move
    · unfold next
      dsimp [coalgebraGame]
      exact (Finset.mem_filterMap _).mpr
        ⟨Δ, by simpa [builderRuleApp] using pos, by simp [nrep]; rfl⟩
  have still_winning_next : winning strat next := by
    have g_winning := winning_of_in_cone_winning g.2.1 h
    exact @winning_of_whatever_other_move Prover coalgebraGame strat g.1 g.2.2 g_winning
      ⟨next, next_in_moves⟩
  have P_has_moves_next : (coalgebraGame.moves next).Nonempty :=
    winning_has_moves P_next still_winning_next
  let nextNext := strat next P_next P_has_moves_next
  have B_next_next : coalgebraGame.turn nextNext.1 = Builder := by
    have next_next_in_moves := nextNext.2
    unfold next Game.Pos.moves Game.moves at next_next_in_moves
    dsimp [coalgebraGame] at next_next_in_moves
    rcases (Finset.mem_map).mp next_next_in_moves with ⟨R, _, hR⟩
    rw [← hR]
    rfl
  have next_next_in_cone : inMyCone strat (startPos Γ) nextNext := by
    have := @inMyCone.oStep _ _ strat _ _ _ g.2.1 g.2.2 next_in_moves
    exact inMyCone.myStep this P_has_moves_next P_next
  ⟨nextNext, next_next_in_cone, B_next_next⟩

/-- The sequent at the premise defined by `nextNext` is the sequent `Δ` which we expect. -/
lemma next_next_cor {Γ Δ : SplitSequent} {strat : Strategy coalgebraGame Prover}
    (g : proof_type Γ strat) (h : winning strat (startPos Γ)) (nrep : Δ ∉ g.1.2.1)
    (pos : Δ ∈ (builderRuleApp g.1 g.2.2).splitSequents) :
    f (builderRuleApp (nextNext g h nrep pos).1 (nextNext g h nrep pos).2.2) = Δ := by
  let next : GamePos := ⟨Sum.inl <| Δ, g.1.2.1, builderRuleApp g.1 g.2.2 :: g.1.2.2⟩
  have P_next : coalgebraGame.turn next = Prover := by
    unfold Game.turn next
    simp
  have next_in_moves : next ∈ coalgebraGame.moves g.1 := by
    rcases g with ⟨⟨Γ | R, Γs, Rs⟩, _, b_move⟩
    · change Prover = Builder at b_move
      cases b_move
    · unfold next
      dsimp [coalgebraGame]
      exact (Finset.mem_filterMap _).mpr
        ⟨Δ, by simpa [builderRuleApp] using pos, by simp [nrep]; rfl⟩
  have still_winning_next : winning strat next := by
    have g_winning := winning_of_in_cone_winning g.2.1 h
    exact @winning_of_whatever_other_move Prover coalgebraGame strat g.1 g.2.2 g_winning
      ⟨next, next_in_moves⟩
  have P_has_moves_next : (coalgebraGame.moves next).Nonempty :=
    winning_has_moves P_next still_winning_next
  let next_next' := strat next P_next P_has_moves_next
  have B_next_next : coalgebraGame.turn next_next'.1 = Builder := by
    have next_next_in_moves := next_next'.2
    unfold next Game.Pos.moves Game.moves at next_next_in_moves
    dsimp [coalgebraGame] at next_next_in_moves
    rcases (Finset.mem_map).mp next_next_in_moves with ⟨R, _, hR⟩
    rw [← hR]
    rfl
  have next_next_in_cone : inMyCone strat (startPos Γ) next_next' := by
    have := @inMyCone.oStep _ _ strat _ _ _ g.2.1 g.2.2 next_in_moves
    exact inMyCone.myStep this P_has_moves_next P_next
  have h : next_next'.1 = (nextNext g h nrep pos).1 := by grind [nextNext]
  simp only [← h]
  have next_next_in_moves := next_next'.2
  unfold next Game.Pos.moves Game.moves coalgebraGame at next_next_in_moves
  simp only [Finset.mem_map] at next_next_in_moves
  have ⟨R, R_prop, R_eq⟩ := next_next_in_moves
  simp at R_eq
  simp only [←R_eq]
  simp only [builderRuleApp]
  simp only [SplitSequent.ruleApps, Finset.mem_filterMap, Option.dite_none_right_eq_some,
    and_exists_self, Sum.exists] at R_prop
  rcases R_prop with R_prop | R_prop
  all_goals
    have ⟨φ, φ_in, φ_prop⟩ := R_prop
    cases φ <;> simp at φ_prop <;> try grind [f]

/-- Comparison of rule app history length and sequent history length. -/
lemma history_length_in_cone {Γ : SplitSequent} (strat : Strategy coalgebraGame Prover)
    (g : coalgebraGame.Pos) (in_cone : inMyCone strat (startPos Γ) g) :
    (coalgebraGame.turn g = Prover → g.2.1.length = g.2.2.length) ∧
      (coalgebraGame.turn g = Builder → g.2.1.length = g.2.2.length + 1) := by
    induction in_cone
    case nil =>
      constructor
      · intro _
        rfl
      · intro h
        change Prover = Builder at h
        cases h
    case myStep q q_in_cone q_has_moves p_turn_q ih =>
      rcases hnext : strat q p_turn_q q_has_moves with ⟨next, next_mem⟩
      have mv : Move q next := move_iff_in_moves.2 next_mem
      cases mv
      case prover R Rs Δ Δs _ =>
        constructor
        · intro hturn
          change Builder = Prover at hturn
          cases hturn
        · intro _
          have hlen := ih.1 p_turn_q
          simpa [coalgebraGame] using congrArg Nat.succ hlen
      case builder =>
        change Builder = Prover at p_turn_q
        cases p_turn_q
    case oStep q r q_in_cone b_turn_q in_moves ih =>
      have mv : Move q r := move_iff_in_moves.2 in_moves
      cases mv
      case prover =>
        change Prover = Builder at b_turn_q
        cases b_turn_q
      case builder =>
        constructor
        · intro _
          have hlen := ih.2 b_turn_q
          simpa [coalgebraGame] using hlen
        · intro hturn
          change Prover = Builder at hturn
          cases hturn

/-- Defines the premise when we do not have a repeat. -/
def repPos {Γ Δ : SplitSequent} {strat : Strategy coalgebraGame Prover} (g : proof_type Γ strat)
 (rep : Δ ∈ g.1.2.1) : coalgebraGame.Pos :=
  let n := Fin.find _ (List.mem_iff_get.1 rep)
  rewindHistory g.1 ⟨2 * n.1, by
    have := (history_length_in_cone strat g.1 g.2.1).2 g.2.2
    unfold instMinNat min minOfLe
    simp [g.2.2]
    split <;> try grind⟩

/-- Rewinding the game one step changes the player. -/
lemma rewind_turn_one_step {g n h1 h2} :
    coalgebraGame.turn (rewindHistory g ⟨n + 1, h1⟩) =
      other (coalgebraGame.turn (rewindHistory g ⟨n, h2⟩)) := by
  cases n
  case zero =>
    rcases g with ⟨Γ | R, Γs, Rs⟩
    · simp [rewindHistory, rewindHistoryOneStep]
      rfl
    · simp [rewindHistory, rewindHistoryOneStep]
      rfl
  case succ n =>
    unfold rewindHistory
    exact @rewind_turn_one_step (rewindHistoryOneStep g _) n _ _

/-- Rewinding an even number of moves is the same players turn, rewinding an odd number is other
    players turn. -/
lemma rewind_turn {g n} :
    if Even n.1 then
      coalgebraGame.turn (rewindHistory g n) = coalgebraGame.turn g
    else
      coalgebraGame.turn (rewindHistory g n) = other (coalgebraGame.turn g) := by
  induction n using Fin.induction
  case zero => simp
  case succ k ih =>
    have ⟨k_val, k_prop⟩ := k
    simp only [Fin.val_succ, Fin.val_castSucc] at ih ⊢
    by_cases hk : Even k_val
    · have h : ¬ Even (k_val + 1) := by grind
      simp only [h, hk, if_false, if_true] at ih ⊢
      simp only [← ih]
      exact rewind_turn_one_step
    · have h : Even (k_val + 1) := by grind
      simp only [h, hk, if_true, if_false] at ih ⊢
      have ih := congrArg other ih
      simp at ih
      simp only [← ih]
      exact rewind_turn_one_step

/-- The sequent at the one step rewind can be found in the history. -/
lemma f_of_mem_ruleApps {Γ : SplitSequent} {R : RuleApp} (h : R ∈ SplitSequent.ruleApps Γ) :
    f R = Γ := by
  simp only [SplitSequent.ruleApps, Finset.mem_filterMap, Option.dite_none_right_eq_some,
    and_exists_self, Sum.exists] at h
  rcases h with h | h
  all_goals
    rcases h with ⟨φ, φ_in, hR⟩
    rcases φ <;> simp at hR <;> grind [f]

lemma ruleApp_topl_mem {Γ : SplitSequent} (h : Sum.inl ⊤ ∈ Γ) :
    RuleApp.topₗ Γ h ∈ SplitSequent.ruleApps Γ := by
  simp only [SplitSequent.ruleApps, Finset.mem_filterMap, Option.dite_none_right_eq_some,
    and_exists_self, Sum.exists]
  exact Or.inl ⟨⊤, h, by simp⟩

lemma ruleApp_topr_mem {Γ : SplitSequent} (h : Sum.inr ⊤ ∈ Γ) :
    RuleApp.topᵣ Γ h ∈ SplitSequent.ruleApps Γ := by
  simp only [SplitSequent.ruleApps, Finset.mem_filterMap, Option.dite_none_right_eq_some,
    and_exists_self, Sum.exists]
  exact Or.inr ⟨⊤, h, by simp⟩

lemma ruleApp_axll_mem {Γ : SplitSequent} {n : Nat}
    (h : Sum.inl (at n) ∈ Γ ∧ Sum.inl (na n) ∈ Γ) :
    RuleApp.axₗₗ Γ n h ∈ SplitSequent.ruleApps Γ := by
  simp only [SplitSequent.ruleApps, Finset.mem_filterMap, Option.dite_none_right_eq_some,
    and_exists_self, Sum.exists]
  exact Or.inl ⟨at n, h.1, by simp [h.2]⟩

lemma ruleApp_axlr_mem {Γ : SplitSequent} {n : Nat}
    (h : Sum.inl (at n) ∈ Γ ∧ Sum.inr (na n) ∈ Γ) (h_left : Sum.inl (na n) ∉ Γ) :
    RuleApp.axₗᵣ Γ n h ∈ SplitSequent.ruleApps Γ := by
  simp only [SplitSequent.ruleApps, Finset.mem_filterMap, Option.dite_none_right_eq_some,
    and_exists_self, Sum.exists]
  exact Or.inl ⟨at n, h.1, by simp [h_left, h.2]⟩

lemma ruleApp_axrl_mem {Γ : SplitSequent} {n : Nat}
    (h : Sum.inr (at n) ∈ Γ ∧ Sum.inl (na n) ∈ Γ) :
    RuleApp.axᵣₗ Γ n h ∈ SplitSequent.ruleApps Γ := by
  simp only [SplitSequent.ruleApps, Finset.mem_filterMap, Option.dite_none_right_eq_some,
    and_exists_self, Sum.exists]
  exact Or.inr ⟨at n, h.1, by simp [h.2]⟩

lemma ruleApp_axrr_mem {Γ : SplitSequent} {n : Nat}
    (h : Sum.inr (at n) ∈ Γ ∧ Sum.inr (na n) ∈ Γ) (h_left : Sum.inl (na n) ∉ Γ) :
    RuleApp.axᵣᵣ Γ n h ∈ SplitSequent.ruleApps Γ := by
  simp only [SplitSequent.ruleApps, Finset.mem_filterMap, Option.dite_none_right_eq_some,
    and_exists_self, Sum.exists]
  exact Or.inr ⟨at n, h.1, by simp [h_left, h.2]⟩

lemma ruleApp_andl_mem {Γ : SplitSequent} {φ ψ : Formula}
    (h : Sum.inl (φ&ψ) ∈ Γ) :
    RuleApp.andₗ Γ φ ψ h ∈ SplitSequent.ruleApps Γ := by
  simp only [SplitSequent.ruleApps, Finset.mem_filterMap, Option.dite_none_right_eq_some,
    and_exists_self, Sum.exists]
  exact Or.inl ⟨φ&ψ, h, by simp⟩

lemma ruleApp_andr_mem {Γ : SplitSequent} {φ ψ : Formula}
    (h : Sum.inr (φ&ψ) ∈ Γ) :
    RuleApp.andᵣ Γ φ ψ h ∈ SplitSequent.ruleApps Γ := by
  simp only [SplitSequent.ruleApps, Finset.mem_filterMap, Option.dite_none_right_eq_some,
    and_exists_self, Sum.exists]
  exact Or.inr ⟨φ&ψ, h, by simp⟩

lemma ruleApp_orl_mem {Γ : SplitSequent} {φ ψ : Formula}
    (h : Sum.inl (φ v ψ) ∈ Γ) :
    RuleApp.orₗ Γ φ ψ h ∈ SplitSequent.ruleApps Γ := by
  simp only [SplitSequent.ruleApps, Finset.mem_filterMap, Option.dite_none_right_eq_some,
    and_exists_self, Sum.exists]
  exact Or.inl ⟨φ v ψ, h, by simp⟩

lemma ruleApp_orr_mem {Γ : SplitSequent} {φ ψ : Formula}
    (h : Sum.inr (φ v ψ) ∈ Γ) :
    RuleApp.orᵣ Γ φ ψ h ∈ SplitSequent.ruleApps Γ := by
  simp only [SplitSequent.ruleApps, Finset.mem_filterMap, Option.dite_none_right_eq_some,
    and_exists_self, Sum.exists]
  exact Or.inr ⟨φ v ψ, h, by simp⟩

lemma ruleApp_boxl_mem {Γ : SplitSequent} {φ : Formula}
    (h : Sum.inl (□φ) ∈ Γ) :
    RuleApp.boxₗ Γ φ h ∈ SplitSequent.ruleApps Γ := by
  simp only [SplitSequent.ruleApps, Finset.mem_filterMap, Option.dite_none_right_eq_some,
    and_exists_self, Sum.exists]
  exact Or.inl ⟨□φ, h, by simp⟩

lemma ruleApp_boxr_mem {Γ : SplitSequent} {φ : Formula}
    (h : Sum.inr (□φ) ∈ Γ) :
    RuleApp.boxᵣ Γ φ h ∈ SplitSequent.ruleApps Γ := by
  simp only [SplitSequent.ruleApps, Finset.mem_filterMap, Option.dite_none_right_eq_some,
    and_exists_self, Sum.exists]
  exact Or.inr ⟨□φ, h, by simp⟩

lemma rewind_history_one_step_correspondence {Γ g} (strat : Strategy coalgebraGame Prover)
  {h0 h1 h2} (in_cone : inMyCone strat (startPos Γ) g)
  : f (builderRuleApp (rewindHistoryOneStep g h0) h1) = g.2.1[0]'h2 := by
  cases in_cone <;> try simp at h2
  case myStep q q_in_cone q_has_moves P_turn_q =>
    have mv : Move q (strat q P_turn_q q_has_moves).1 :=
      move_iff_in_moves.2 (strat q P_turn_q q_has_moves).2
    rw [rewind_history_one_step_of_move mv h0] at h1
    rw [P_turn_q] at h1
    cases h1
  case oStep q q_in_cone B_turn_q g_in_moves_q =>
    have mv_qg : Move q g := move_iff_in_moves.2 g_in_moves_q
    have rew := rewind_history_one_step_of_move mv_qg h0
    simp only [rew]
    cases q_in_cone
    case nil =>
      change Prover = Builder at B_turn_q
      cases B_turn_q
    case myStep q' q_in_cone' q_has_moves' P_turn_q' =>
      have q_mem := (strat q' P_turn_q' q_has_moves').2
      rcases q' with ⟨Δ0 | R0, Δs, Rs⟩
      · unfold Game.Pos.moves Game.moves at q_mem
        dsimp [coalgebraGame] at q_mem
        rcases (Finset.mem_map).mp q_mem with ⟨R, R_mem, hR⟩
        simp only [← hR] at g_in_moves_q ⊢
        rcases (Finset.mem_filterMap _).mp g_in_moves_q with ⟨Δ', _, hΔ'⟩
        by_cases hmem : Δ' ∈ Δ0 :: Δs
        · simp [hmem] at hΔ'
        · simp only [hmem] at hΔ'
          simp only [if_false] at hΔ'
          cases hΔ'
          simp only [builderRuleApp, List.getElem_cons_zero]
          exact f_of_mem_ruleApps R_mem
      · change Builder = Prover at P_turn_q'
        cases P_turn_q'
    case oStep q' q_in_cone' B_turn_q' g_in_moves_q' =>
      have mv_q'q := move_iff_in_moves.2 g_in_moves_q'
      cases mv_q'q
      case prover =>
        change Prover = Builder at B_turn_q'
        cases B_turn_q'
      case builder =>
        change Prover = Builder at B_turn_q
        cases B_turn_q

/-- The rule application at a builder position in the cone points to the head sequent. -/
lemma builder_RuleApp_head_of_in_cone {Γ g} (strat : Strategy coalgebraGame Prover)
    (in_cone : inMyCone strat (startPos Γ) g) (h : coalgebraGame.turn g = Builder)
    (h2 : 0 < g.2.1.length) : f (builderRuleApp g h) = g.2.1[0]'h2 := by
  cases in_cone
  case nil =>
    change Prover = Builder at h
    cases h
  case myStep q q_in_cone q_has_moves P_turn_q =>
    have q_mem := (strat q P_turn_q q_has_moves).2
    rcases q with ⟨Δ0 | R0, Δs, Rs⟩
    · unfold Game.Pos.moves Game.moves at q_mem
      dsimp [coalgebraGame] at q_mem
      rcases (Finset.mem_map).mp q_mem with ⟨R, R_mem, hR⟩
      simp only [← hR]
      exact f_of_mem_ruleApps R_mem
    · change Builder = Prover at P_turn_q
      cases P_turn_q
  case oStep q q_in_cone B_turn_q in_moves =>
    exfalso
    have mv := move_iff_in_moves.2 in_moves
    cases mv
    case prover =>
      change Prover = Builder at B_turn_q
      cases B_turn_q
    case builder =>
      change Prover = Builder at h
      cases h

/-- The sequent at the `n` step rewind can be found in the history. -/
lemma rewind_history_correspondence_aux (Γ) (info : SplitSequent ⊕ RuleApp)
  (Γs : List SplitSequent) (Rs : List RuleApp) (strat : Strategy coalgebraGame Prover)
    (n) (h2 h3 h4 h6) (in_cone : inMyCone strat (startPos Γ) ⟨info, Γs, Rs⟩)
    : (∀ b_turn_g : coalgebraGame.turn ⟨info, Γs, Rs⟩ = Builder,
        f (builderRuleApp (rewindHistory ⟨info, Γs, Rs⟩ ⟨2 * n, h3⟩)
          (by
              have turn_eq := @rewind_turn ⟨info, Γs, Rs⟩ ⟨2 * n, h3⟩
              simpa [b_turn_g] using turn_eq)) = Γs[n]'h6)
    ∧ (∀ p_turn_q : coalgebraGame.turn ⟨info, Γs, Rs⟩ = Prover,
        f (builderRuleApp (rewindHistory ⟨info, Γs, Rs⟩ ⟨2 * n + 1, h4⟩)
          (by
              have turn_eq := @rewind_turn ⟨info, Γs, Rs⟩ ⟨2 * n + 1, h4⟩
              simpa [p_turn_q] using turn_eq)) = Γs[n]'h2)
    := by
  have rewind_one_step_in_cone :=
    fun h ↦ rewind_history_one_step_in_cone ⟨info, Γs, Rs⟩ h strat in_cone
  have length := history_length_in_cone strat ⟨info, Γs, Rs⟩ in_cone
  · cases n
    case zero =>
      by_cases coalgebraGame.turn ⟨info, Γs, Rs⟩ = Prover
      case pos h =>
        constructor
        · intro b_turn_g
          rw [h] at b_turn_g
          cases b_turn_g
        · intro _p_turn_q
          suffices f (builderRuleApp (rewindHistoryOneStep ⟨info, Γs, Rs⟩ _) _) = Γs[0] by
            simpa [rewindHistory, h] using this
          exact rewind_history_one_step_correspondence strat in_cone
      case neg h =>
        have h_builder : coalgebraGame.turn ⟨info, Γs, Rs⟩ = Builder := by
          simpa using h
        constructor
        · intro _b_turn_g
          simpa only [mul_zero, Fin.zero_eta, rewind_history_zero, zero_add] using
            builder_RuleApp_head_of_in_cone strat in_cone h_builder h6
        · intro p_turn_q
          rw [h_builder] at p_turn_q
          cases p_turn_q
    case succ n =>
      rcases info with Γ' | R
      · have := @rewind_turn ⟨Sum.inl Γ', Γs, Rs⟩ ⟨2 * (n + 1) + 1, h4⟩
        unfold rewindHistory
        simp only [reduceCtorEq, IsEmpty.forall_iff, true_and]
        have for_termination_1 : Γs.length + Rs.tail.length < Γs.length + Rs.length := by
          cases Rs_def : Rs with
          | nil =>
              have hturn : coalgebraGame.turn (Sum.inl Γ', Γs, Rs) = Prover := rfl
              rw [hturn] at h4
              simp [Rs_def] at h4
          | cons head tail =>
              simp
        intro p_turn_q
        have Rs_ne : Rs ≠ [] := by
          intro hRs
          cases Rs <;> simp_all
        let Rprev := Rs.head Rs_ne
        have rec_h4 :
            2 * (n + 1) + 1 < min (2 * Γs.length) (2 * Rs.tail.length + 1) + 1 := by
          change n + 1 < Γs.length at h2
          cases Rs with
          | nil => simp at for_termination_1
          | cons R Rs =>
              have hlen : Γs.length = (R :: Rs).length := length.1 rfl
              simp only [List.length_cons] at hlen
              rw [hlen]
              simp
              omega
        have rec_h3 :
            2 * (n + 1) < min (2 * Γs.length) (2 * Rs.tail.length + 1) + 1 := by
          omega
        have rec_cone : inMyCone strat (startPos Γ) (Sum.inr Rprev, Γs, Rs.tail) := by
          have := rewind_one_step_in_cone (Or.inl ⟨rfl, Rs_ne⟩)
          simpa [rewindHistoryOneStep, Rprev] using this
        exact (rewind_history_correspondence_aux Γ (Sum.inr Rprev) Γs Rs.tail strat
          (n + 1) h2 (by simpa using rec_h3) (by simpa using rec_h4) h6 rec_cone).1 rfl
      · have h : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
        simp only [h]
        simp only [reduceCtorEq, if_false, IsEmpty.forall_iff, and_true] at h3 h4 ⊢
        unfold rewindHistory
        have for_termination_2 : Γs.tail.length + Rs.length < Γs.length + Rs.length := by
          cases Γs_def : Γs
          · simp_all
          · grind
        intro b_turn_g
        have Γs_ne : Γs ≠ [] := by
          intro hΓs
          cases Γs <;> simp_all
        let Γprev := Γs.head Γs_ne
        have rec_h2 : n < Γs.tail.length := by
          cases Γs with
          | nil => simp at Γs_ne
          | cons Γ' Γs => simpa using h2
        have rec_h4 :
            2 * n < min (2 * Γs.tail.length + 1) (2 * Rs.length) := by
          cases Γs with
          | nil => simp at Γs_ne
          | cons Γ' Γs =>
              have h4' :
                  2 * (n + 1) + 1 <
                    min (2 * (Γ' :: Γs).length) (2 * Rs.length + 1) + 1 := by
                simpa using h4
              have hlen : (Γ' :: Γs).length = Rs.length + 1 := length.2 rfl
              simp only [List.length_cons, List.tail_cons] at hlen h4' ⊢
              rw [hlen] at h4'
              omega
        have rec_h3 :
            2 * n ≤ min (2 * Γs.tail.length + 1) (2 * Rs.length) := by
          exact Nat.le_of_lt rec_h4
        have rec_cone : inMyCone strat (startPos Γ) (Sum.inl Γprev, Γs.tail, Rs) := by
          have := rewind_one_step_in_cone (Or.inr ⟨rfl, Γs_ne⟩)
          simpa [rewindHistoryOneStep, Γprev] using this
        change f (builderRuleApp
          (rewindHistory (Sum.inl Γprev, Γs.tail, Rs) ⟨2 * n + 1, Nat.succ_lt_succ rec_h4⟩) _) =
            Γs[n + 1]
        simpa [Γprev] using
          (rewind_history_correspondence_aux Γ (Sum.inl Γprev) Γs.tail Rs strat
            n rec_h2
            (by exact Nat.lt_succ_of_le rec_h3)
            (by exact Nat.succ_lt_succ rec_h4)
            rec_h2 rec_cone).2 rfl
termination_by Γs.length + Rs.length
decreasing_by
  all_goals assumption

/-- The sequent at the `n` step rewind can be found in the history. -/
lemma rewind_history_correspondence (Γ g) (strat : Strategy coalgebraGame Prover)
  (n) (h2 h3 h4 h6) (in_cone : inMyCone strat (startPos Γ) g)
  : (∀ b_turn_g : coalgebraGame.turn g = Builder,
      f (builderRuleApp (rewindHistory g ⟨2 * n, h3⟩)
        (by
          have turn_eq := @rewind_turn g ⟨2 * n, h3⟩
          simpa [b_turn_g] using turn_eq)) = g.2.1[n]'h6)
  ∧ (∀ p_turn_q : coalgebraGame.turn g = Prover,
      f (builderRuleApp (rewindHistory g ⟨2 * n + 1, h4⟩)
        (by
          have turn_eq := @rewind_turn g ⟨2 * n + 1, h4⟩
          simpa [p_turn_q] using turn_eq)) = g.2.1[n]'h2) := by
  rcases g with ⟨info, Γs, Rs⟩
  exact rewind_history_correspondence_aux Γ info Γs Rs strat n h2 h3 h4 h6 in_cone

/-- Defines the premise when we have a repeat. -/
def repNext (Γ : SplitSequent) {Δ : SplitSequent} {strat : Strategy coalgebraGame Prover}
  (g : proof_type Γ strat) (rep : Δ ∈ g.1.2.1) : (proof_type Γ strat) :=
  ⟨repPos g rep,
   rewind_history_in_cone g.1 ⟨(2 * (Fin.find _ (List.mem_iff_get.1 rep)).1), _⟩ strat g.2.1,
    by
      have := @rewind_turn g.1 ⟨(2 * (Fin.find _ (List.mem_iff_get.1 rep)).1), by
        have length := history_length_in_cone strat g.1 g.2.1
        have hlen := length.2 g.2.2
        have hfind := (Fin.find _ (List.mem_iff_get.1 rep)).2
        simp only [g.2.2, reduceCtorEq, if_false]
        omega⟩
      simp only [g.2.2, Nat.even_mul, even_two, true_or, if_true] at this
      convert this⟩

/-- The sequent at the premise defined by `repNext` is the sequent `Δ` which we expect. -/
lemma rep_next_cor (Γ : SplitSequent) {Δ : SplitSequent} {strat : Strategy coalgebraGame Prover}
  (g : proof_type Γ strat) (rep : Δ ∈ g.1.2.1) :
  f (builderRuleApp (repNext Γ g rep).1 (repNext Γ g rep).2.2) = Δ := by
  have Δ_eq := Fin.find_spec (List.mem_iff_get.1 rep)
  conv =>
  · congr
    · skip
    · rw [←Δ_eq]
  let n := Fin.find _ (List.mem_iff_get.1 rep)
  simp only [repNext, repPos, List.get_eq_getElem, Fin.val_find]
  convert
    (rewind_history_correspondence Γ g.1 strat
      (Fin.find _ (List.mem_iff_get.1 rep)).1 _ _ _ _ g.2.1).1 _ <;>
      try simp_all <;>
      try grind
  · have length := history_length_in_cone strat g.1 g.2.1
    simp [g.2.2] at *
    grind
  · have length := history_length_in_cone strat g.1 g.2.1
    simp [g.2.2] at *
    grind

/-- A left game position is a Prover turn, so it cannot be a Builder turn. -/
private lemma left_turn_not_builder {Γ : SplitSequent} {Γs : List SplitSequent}
    {Rs : List RuleApp} : coalgebraGame.turn (Sum.inl Γ, Γs, Rs) ≠ Builder := by
  intro h
  change Prover = Builder at h
  cases h

/-- Define the list of premises from a Builder move. -/
def builderMovePremises {Γ : SplitSequent} {strat : Strategy coalgebraGame Prover}
    (g : proof_type Γ strat)
    (h : winning strat (startPos Γ)) : List (proof_type Γ strat) := match g_def : g with
  | ⟨⟨Sum.inl _, _, _⟩, x, y⟩ => False.elim (left_turn_not_builder y)
  | ⟨⟨Sum.inr R, Γs, Rs⟩, _⟩ =>
    match R with
      | RuleApp.topₗ _ _ => []
      | RuleApp.topᵣ _ _ => []
      | RuleApp.axₗₗ _ _ _ => []
      | RuleApp.axₗᵣ _ _ _ => []
      | RuleApp.axᵣₗ _ _ _ => []
      | RuleApp.axᵣᵣ _ _ _ => []
      | RuleApp.orₗ Δ φ1 φ2 φ_in =>
        if rep : (Δ \ {Sum.inl (φ1 v φ2)}) ∪ {Sum.inl φ1, Sum.inl φ2} ∈ Γs
          then [repNext Γ g (by convert rep; grind)]
          else
            [nextNext g h
              (by convert rep; grind)
              (by subst g_def; simp [RuleApp.splitSequents, builderRuleApp])]
      | RuleApp.orᵣ Δ φ1 φ2 φ_in =>
        if rep : (Δ \ {Sum.inr (φ1 v φ2)}) ∪ {Sum.inr φ1, Sum.inr φ2} ∈ Γs
          then [repNext Γ g (by convert rep; grind)]
          else
            [nextNext g h
              (by convert rep; grind)
              (by subst g_def; simp [RuleApp.splitSequents, builderRuleApp])]
      | RuleApp.andₗ Δ φ1 φ2 φ_in =>
        if rep1 : (Δ \ {Sum.inl (φ1 & φ2)}) ∪ {Sum.inl φ1} ∈ Γs
          then
            if rep2 : (Δ \ {Sum.inl (φ1 & φ2)}) ∪ {Sum.inl φ2} ∈ Γs
              then [repNext Γ g (by convert rep1; grind), repNext Γ g (by convert rep2; grind)]
              else
                [repNext Γ g (by convert rep1; grind),
                  nextNext g h
                    (by convert rep2; grind)
                    (by subst g_def; simp [RuleApp.splitSequents, builderRuleApp])]
          else
            if rep2 : (Δ \ {Sum.inl (φ1 & φ2)}) ∪ {Sum.inl φ2} ∈ Γs
              then
                [nextNext g h
                  (by convert rep1; grind)
                  (by subst g_def; simp [RuleApp.splitSequents, builderRuleApp]),
                 repNext Γ g (by convert rep2; grind)]
              else
                [nextNext g h
                  (by convert rep1; grind)
                  (by subst g_def; simp [RuleApp.splitSequents, builderRuleApp]),
                 nextNext g h
                  (by convert rep2; grind)
                  (by subst g_def; simp [RuleApp.splitSequents, builderRuleApp])]
      | RuleApp.andᵣ Δ φ1 φ2 φ_in =>
        if rep1 : (Δ \ {Sum.inr (φ1 & φ2)}) ∪ {Sum.inr φ1} ∈ Γs
          then
            if rep2 : (Δ \ {Sum.inr (φ1 & φ2)}) ∪ {Sum.inr φ2} ∈ Γs
              then [repNext Γ g (by convert rep1; grind), repNext Γ g (by convert rep2; grind)]
              else
                [repNext Γ g (by convert rep1; grind),
                 nextNext g h
                  (by convert rep2; grind)
                  (by subst g_def; simp [RuleApp.splitSequents, builderRuleApp])]
          else
            if rep2 : (Δ \ {Sum.inr (φ1 & φ2)}) ∪ {Sum.inr φ2} ∈ Γs
              then
                [nextNext g h
                  (by convert rep1; grind)
                  (by subst g_def; simp [RuleApp.splitSequents, builderRuleApp]),
                 repNext Γ g (by convert rep2; grind)]
              else
                [nextNext g h
                  (by convert rep1; grind)
                  (by subst g_def; simp [RuleApp.splitSequents, builderRuleApp]),
                 nextNext g h
                  (by convert rep2; grind)
                  (by subst g_def; simp [RuleApp.splitSequents, builderRuleApp])]
      | RuleApp.boxₗ Δ φ φ_in =>
        if rep : (Δ \ {Sum.inl (□φ)}).D ∪ {Sum.inl φ} ∈ Γs
          then [repNext Γ g (by convert rep; grind)]
          else
            [nextNext g h
              (by convert rep; grind)
              (by subst g_def; simp [RuleApp.splitSequents, builderRuleApp])]
      | RuleApp.boxᵣ Δ φ φ_in =>
        if rep : (Δ \ {Sum.inr (□φ)}).D ∪ {Sum.inr φ} ∈ Γs
          then [repNext Γ g (by convert rep; grind)]
          else
            [nextNext g h
              (by convert rep; grind)
              (by subst g_def; simp [RuleApp.splitSequents, builderRuleApp])]

/-- The game starts from a Prover turn. -/
private lemma start_pos_turn_prover (Γ : SplitSequent) :
    coalgebraGame.turn (startPos Γ) = Prover := rfl

/-- The proof object extracted from a Prover winning strategy. -/
private def prover_win_proof {Γ : SplitSequent} (strat : Strategy coalgebraGame Prover)
    (h : winning strat (startPos Γ)) : Proof where
  X := proof_type Γ strat
  α g := ⟨builderRuleApp g.1 g.2.2, builderMovePremises g h⟩
  step := by  -- scary!!!!
      intro g
      rcases g_def : g with ⟨⟨Γ | R, Γs, Rs⟩, in_cone, b_move⟩
      · change Prover = Builder at b_move
        cases b_move
      · subst g_def
        simp only [r, builderRuleApp]
        cases R
        case andₗ Δ φ1 φ2 φ_in =>
          let current : proof_type Γ strat :=
            ⟨⟨Sum.inr (RuleApp.andₗ Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩
          simp only [p, builderMovePremises, List.map_eq_cons_iff, ↓existsAndEq,
            List.map_eq_nil_iff, true_and, and_true]
          by_cases Δ \ {Sum.inl (φ1 & φ2)} ∪ {Sum.inl φ1} ∈ Γs
          case pos rep1 =>
            by_cases Δ \ {Sum.inl (φ1 & φ2)} ∪ {Sum.inl φ2} ∈ Γs
            case pos rep2 =>
              simp only [rep1, rep2, ↓reduceDIte, List.cons.injEq, and_true,
                ↓existsAndEq, true_and, repNext, fₙ_alternate]
              constructor
              · exact rep_next_cor Γ current (by dsimp [current]; exact rep1)
              · exact rep_next_cor Γ current (by dsimp [current]; exact rep2)
            case neg nrep2 =>
              simp only [rep1, nrep2, ↓reduceDIte, List.cons.injEq, and_true,
                ↓existsAndEq, true_and, repNext, fₙ_alternate]
              constructor
              · exact rep_next_cor Γ current (by dsimp [current]; exact rep1)
              · exact next_next_cor current h nrep2
                  (by
                    dsimp [current, builderRuleApp]
                    simp [RuleApp.splitSequents])
          case neg nrep1 =>
            by_cases Δ \ {Sum.inl (φ1 & φ2)} ∪ {Sum.inl φ2} ∈ Γs
            case pos rep2 =>
              simp only [nrep1, rep2, ↓reduceDIte, List.cons.injEq, and_true,
                ↓existsAndEq, true_and, repNext, fₙ_alternate]
              constructor
              · exact next_next_cor current h nrep1
                  (by
                    dsimp [current, builderRuleApp]
                    simp [RuleApp.splitSequents])
              · exact rep_next_cor Γ current (by dsimp [current]; exact rep2)
            case neg nrep2 =>
              simp only [nrep1, nrep2, ↓reduceDIte, List.cons.injEq, and_true,
                ↓existsAndEq, true_and, fₙ_alternate]
              constructor
              · exact next_next_cor current h nrep1
                  (by
                    dsimp [current, builderRuleApp]
                    simp [RuleApp.splitSequents])
              · exact next_next_cor current h nrep2
                  (by
                    dsimp [current, builderRuleApp]
                    simp [RuleApp.splitSequents])
        case andᵣ Δ φ1 φ2 φ_in =>
          let current : proof_type Γ strat :=
            ⟨⟨Sum.inr (RuleApp.andᵣ Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩
          simp only [p, builderMovePremises, List.map_eq_cons_iff, ↓existsAndEq,
            List.map_eq_nil_iff, true_and, and_true]
          by_cases Δ \ {Sum.inr (φ1 & φ2)} ∪ {Sum.inr φ1} ∈ Γs
          case pos rep1 =>
            by_cases Δ \ {Sum.inr (φ1 & φ2)} ∪ {Sum.inr φ2} ∈ Γs
            case pos rep2 =>
              simp only [rep1, rep2, ↓reduceDIte, List.cons.injEq, and_true,
                ↓existsAndEq, true_and, repNext, fₙ_alternate]
              constructor
              · exact rep_next_cor Γ current (by dsimp [current]; exact rep1)
              · exact rep_next_cor Γ current (by dsimp [current]; exact rep2)
            case neg nrep2 =>
              simp only [rep1, nrep2, ↓reduceDIte, List.cons.injEq, and_true,
                ↓existsAndEq, true_and, repNext, fₙ_alternate]
              constructor
              · exact rep_next_cor Γ current (by dsimp [current]; exact rep1)
              · exact next_next_cor current h nrep2
                  (by
                    dsimp [current, builderRuleApp]
                    simp [RuleApp.splitSequents])
          case neg nrep1 =>
            by_cases Δ \ {Sum.inr (φ1 & φ2)} ∪ {Sum.inr φ2} ∈ Γs
            case pos rep2 =>
              simp only [nrep1, rep2, ↓reduceDIte, List.cons.injEq, and_true,
                ↓existsAndEq, true_and, repNext, fₙ_alternate]
              constructor
              · exact next_next_cor current h nrep1
                  (by
                    dsimp [current, builderRuleApp]
                    simp [RuleApp.splitSequents])
              · exact rep_next_cor Γ current (by dsimp [current]; exact rep2)
            case neg nrep2 =>
              simp only [nrep1, nrep2, ↓reduceDIte, List.cons.injEq, and_true,
                ↓existsAndEq, true_and, fₙ_alternate]
              constructor
              · exact next_next_cor current h nrep1
                  (by
                    dsimp [current, builderRuleApp]
                    simp [RuleApp.splitSequents])
              · exact next_next_cor current h nrep2
                  (by
                    dsimp [current, builderRuleApp]
                    simp [RuleApp.splitSequents])
        case orₗ Δ φ1 φ2 φ_in =>
          let current : proof_type Γ strat :=
            ⟨⟨Sum.inr (RuleApp.orₗ Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩
          simp only [p, builderMovePremises, List.map_eq_singleton_iff]
          by_cases Δ \ {Sum.inl (φ1 v φ2)} ∪ {Sum.inl φ1, Sum.inl φ2} ∈ Γs
          case pos rep =>
            simp only [rep, ↓reduceDIte, List.cons.injEq, and_true, exists_eq_left']
            simp only [repNext]
            exact rep_next_cor Γ current (by dsimp [current]; exact rep)
          case neg nrep =>
            simp only [nrep, ↓reduceDIte, List.cons.injEq, and_true, exists_eq_left']
            simp only [nextNext, fₙ_alternate]
            exact next_next_cor current h nrep
              (by
                dsimp [current, builderRuleApp]
                simp [RuleApp.splitSequents])
        case orᵣ Δ φ1 φ2 φ_in =>
          let current : proof_type Γ strat :=
            ⟨⟨Sum.inr (RuleApp.orᵣ Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩
          simp only [p, builderMovePremises, List.map_eq_singleton_iff]
          by_cases Δ \ {Sum.inr (φ1 v φ2)} ∪ {Sum.inr φ1, Sum.inr φ2} ∈ Γs
          case pos rep =>
            simp only [rep, ↓reduceDIte, List.cons.injEq, and_true, exists_eq_left']
            simp only [repNext]
            exact rep_next_cor Γ current (by dsimp [current]; exact rep)
          case neg nrep =>
            simp only [nrep, ↓reduceDIte, List.cons.injEq, and_true, exists_eq_left']
            simp only [nextNext, fₙ_alternate]
            exact next_next_cor current h nrep
              (by
                dsimp [current, builderRuleApp]
                simp [RuleApp.splitSequents])
        case boxₗ Δ φ1 φ_in =>
          let current : proof_type Γ strat :=
            ⟨⟨Sum.inr (RuleApp.boxₗ Δ φ1 φ_in), Γs, Rs⟩, in_cone, b_move⟩
          simp only [p, builderMovePremises, List.map_eq_singleton_iff]
          by_cases (Δ \ {Sum.inl (□φ1)}).D ∪ {Sum.inl φ1} ∈ Γs
          case pos rep =>
            simp only [rep, ↓reduceDIte, List.cons.injEq, and_true, exists_eq_left']
            simp only [repNext]
            exact rep_next_cor Γ current (by dsimp [current]; exact rep)
          case neg nrep =>
            simp only [nrep, ↓reduceDIte, List.cons.injEq, and_true, exists_eq_left']
            simp only [nextNext, fₙ_alternate]
            exact next_next_cor current h nrep
              (by
                dsimp [current, builderRuleApp]
                simp [RuleApp.splitSequents])
        case boxᵣ Δ φ1 φ_in =>
          let current : proof_type Γ strat :=
            ⟨⟨Sum.inr (RuleApp.boxᵣ Δ φ1 φ_in), Γs, Rs⟩, in_cone, b_move⟩
          simp only [p, builderMovePremises, List.map_eq_singleton_iff]
          by_cases (Δ \ {Sum.inr (□φ1)}).D ∪ {Sum.inr φ1} ∈ Γs
          case pos rep =>
            simp only [rep, ↓reduceDIte, List.cons.injEq, and_true, exists_eq_left']
            simp only [repNext]
            exact rep_next_cor Γ current (by dsimp [current]; exact rep)
          case neg nrep =>
            simp only [nrep, ↓reduceDIte, List.cons.injEq, and_true, exists_eq_left']
            simp only [nextNext, fₙ_alternate]
            exact next_next_cor current h nrep
              (by
                dsimp [current, builderRuleApp]
                simp [RuleApp.splitSequents])
        all_goals
          simp only [p, builderMovePremises]
          rfl

/-- If Prover has a winning strategy in the game from `Γ`, then there is a proof of `Γ`. -/
theorem prover_win_builds_proof {Γ : SplitSequent} (strat : Strategy coalgebraGame Prover)
    (h : winning strat (startPos Γ)) : SplitSequent.isTrue Γ := by
  use prover_win_proof strat h
  have turn_P : coalgebraGame.turn (startPos Γ) = Prover := start_pos_turn_prover Γ
  let next_move := strat (startPos Γ) turn_P (winning_has_moves turn_P h)
  have turn_next_move_B : coalgebraGame.turn next_move.1 = Builder := by
    have next_move_in_moves := next_move.2
    unfold Game.Pos.moves Game.moves at next_move_in_moves
    dsimp [coalgebraGame] at next_move_in_moves
    rcases (Finset.mem_map).mp next_move_in_moves with ⟨R, _, hR⟩
    rw [← hR]
    rfl
  have next_in_cone : inMyCone strat (startPos Γ) next_move.1 := by
    apply inMyCone.myStep
    exact inMyCone.nil
  use ⟨next_move, next_in_cone, turn_next_move_B⟩
  rcases next_move with ⟨⟨Γ' | R, Γs, Rs⟩, in_moves⟩
  · unfold Game.Pos.moves Game.moves at in_moves
    dsimp [coalgebraGame] at in_moves
    rcases (Finset.mem_map).mp in_moves with ⟨R, _, hR⟩
    cases hR
  · unfold Game.Pos.moves Game.moves at in_moves
    dsimp [coalgebraGame] at in_moves
    rcases (Finset.mem_map).mp in_moves with ⟨R', in_rule, hR⟩
    have hR_eq : R' = R := by
      injection hR with hinfo _hhistories
      exact Sum.inr.inj hinfo
    change f R = Γ
    exact f_of_mem_ruleApps (by simpa [hR_eq] using in_rule)

/-! ## Builder winning the GL-split game builds a GL-model.

If Builder has a winning strategy in the game starting from `Γ`, then there is a proof
of `Γ`, proven in `builder_win_builds_model`, all other definitions and proofs in this
file are helpers. -/

/-- Auxiliary declaration used in the GL coalgebra development. -/
def afterBox (g : coalgebraGame.Pos) : Prop := match g with
  | ⟨Sum.inl _, _, R :: _⟩ => R.isBox
  | _ => false

/-- Auxiliary declaration used in the GL coalgebra development. -/
def isBox (g : coalgebraGame.Pos) : Prop := match g with
  | ⟨Sum.inr R, _, _⟩ => R.isBox
  | _ => false

/-- Auxiliary declaration used in the GL coalgebra development. -/
def nonBoxMove : coalgebraGame.Pos → coalgebraGame.Pos → Prop :=
  fun x y ↦ Move x y ∧ ¬ isBox y

/-- Auxiliary declaration used in the GL coalgebra development. -/
structure MaximalPath (Γ : SplitSequent) (strat : Strategy coalgebraGame Builder) where
  /-- Auxiliary declaration used in the GL coalgebra development. -/
  list : List coalgebraGame.Pos
  ne : list ≠ []
  chain : List.IsChain nonBoxMove list
  max : ¬ ∃ z, nonBoxMove (list.getLast ne) z
  head_cases : afterBox (list.head ne) ∨ list.head ne = startPos Γ
  in_cone : ∀ x ∈ list, inMyCone strat (startPos Γ) x

/-- Auxiliary declaration used in the GL coalgebra development. -/
@[simp]
def MaximalPath.last {Γ : SplitSequent}
    {strat : Strategy coalgebraGame Builder} :
    MaximalPath Γ strat → coalgebraGame.Pos :=
  fun π => π.list.getLast π.ne

/-- Auxiliary declaration used in the GL coalgebra development. -/
@[simp]
def MaximalPath.first {Γ : SplitSequent}
    {strat : Strategy coalgebraGame Builder} :
    MaximalPath Γ strat → coalgebraGame.Pos :=
  fun π => π.list.head π.ne

lemma maximal_path_starts_in_prover_turn {Γ : SplitSequent}
    {strat : Strategy coalgebraGame Builder} (π : MaximalPath Γ strat) :
  coalgebraGame.turn π.first = Prover := by
    match first_def : π.first with
    | ⟨Sum.inl Γ, Γs, Rs⟩ => rfl
    | ⟨Sum.inr R, Γs, Rs⟩ =>
      exfalso
      rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
      simp at first_def
      rcases head_cases with after | root
      · simp [first_def, afterBox] at after
      · simp [first_def] at root
        grind

lemma maximal_path_ends_in_prover_turn {Γ : SplitSequent}
    {strat : Strategy coalgebraGame Builder} (h : winning strat (startPos Γ))
    (π : MaximalPath Γ strat) :
  coalgebraGame.turn π.last = Prover := by
    match last_def : π.last with
    | ⟨Sum.inl Γ, Γs, Rs⟩ => rfl
    | ⟨Sum.inr R, Γs, Rs⟩ =>
      exfalso
      rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
      apply max
      have is_winning : winning strat ⟨Sum.inr R, Γs, Rs⟩ := winning_of_in_cone_winning (by
        simp only [MaximalPath.last] at last_def
        rw [← last_def]
        exact in_cone (π.getLast ne) (List.getLast_mem ne)) h
      have B_turn : coalgebraGame.turn ⟨Sum.inr R, Γs, Rs⟩ = Builder := by rfl
      have has_moves := winning_has_moves B_turn is_winning
      let z := strat ⟨Sum.inr R, Γs, Rs⟩ B_turn has_moves
      refine ⟨z.1, ?_, ?_⟩
      · apply move_iff_in_moves.2
        simp only [MaximalPath.last] at last_def
        rw [last_def]
        exact z.2
      · have ⟨z, z_in⟩ := z
        unfold Game.Pos.moves Game.moves at z_in
        simp only [Finset.mem_filterMap] at z_in
        rcases z_in with ⟨Γ, _Γ_R, z_eq⟩
        by_cases Γ_mem : Γ ∈ Γs
        · simp only [Γ_mem, if_true] at z_eq
          cases z_eq
        · simp only [Γ_mem, if_false, Option.some.injEq] at z_eq
          cases z_eq
          simp [isBox]

open Classical in
/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def makePathFrom
    (strat : Strategy coalgebraGame Builder) (g : coalgebraGame.Pos) :
    List coalgebraGame.Pos :=
  match g_def : g with
  | ⟨Sum.inl Γ, Γs, Rs⟩ =>
      if exists_non_box_move : ∃ g', nonBoxMove g g' then
        ⟨Sum.inl Γ, Γs, Rs⟩ :: makePathFrom strat exists_non_box_move.choose
      else [⟨Sum.inl Γ, Γs, Rs⟩]
  | ⟨Sum.inr R, Γs, Rs⟩ =>
      if exists_non_box_move : ∃ g', nonBoxMove g g' then
        ⟨Sum.inr R, Γs, Rs⟩ ::
          makePathFrom strat
            (strat ⟨Sum.inr R, Γs, Rs⟩
              (by rfl)
              ⟨exists_non_box_move.choose,
                move_iff_in_moves.1 (g_def ▸ exists_non_box_move.choose_spec.1)⟩)
      else [⟨Sum.inr R, Γs, Rs⟩]
termination_by
  coalgebraGame.wf.2.wrap g
decreasing_by
  · apply coalgebraGame.move_rel
    exact move_iff_in_moves.1 (g_def ▸ exists_non_box_move.choose_spec.1)
  · apply coalgebraGame.move_rel
    exact (strat (Sum.inr R, Γs, Rs) (by rfl)
      ⟨exists_non_box_move.choose,
        move_iff_in_moves.1 (g_def ▸ exists_non_box_move.choose_spec.1)⟩).2

lemma make_path_from_is_nonempty (strat : Strategy coalgebraGame Builder) (g : coalgebraGame.Pos)
  : ¬ makePathFrom strat g = ∅ := by
  unfold makePathFrom
  simp
  split <;> split <;> simp

lemma make_path_from_head (strat : Strategy coalgebraGame Builder) (g : coalgebraGame.Pos)
  : (makePathFrom strat g).head (make_path_from_is_nonempty strat g) = g := by
  unfold makePathFrom
  split <;> split <;> simp_all

lemma make_path_from_head? (strat : Strategy coalgebraGame Builder) (g : coalgebraGame.Pos)
  : (makePathFrom strat g).head? = some g := by
  unfold makePathFrom
  split <;> split <;> simp_all

lemma make_path_from_is_chain (strat : Strategy coalgebraGame Builder) (g : coalgebraGame.Pos)
  : List.IsChain nonBoxMove (makePathFrom strat g) :=
  open Classical in
  match g_def : g with
  | ⟨Sum.inl Γ, Γs, Rs⟩ => if exists_non_box_move : ∃ g', nonBoxMove g g'
    then by
      subst g
      simp only [makePathFrom, exists_non_box_move, ↓reduceDIte]
      apply List.IsChain.cons
      · apply make_path_from_is_chain strat
      · simp only [Option.mem_def]
        intro g g_in
        have := make_path_from_head? strat (exists_non_box_move.choose)
        simp only [this, Option.some.injEq] at g_in
        subst g_in
        exact exists_non_box_move.choose_spec
    else by simp_all [makePathFrom]
  | ⟨Sum.inr R, Γs, Rs⟩ => if exists_non_box_move : ∃ g', nonBoxMove g g'
    then by
      subst g
      simp only [makePathFrom, exists_non_box_move, ↓reduceDIte]
      apply List.IsChain.cons
      · apply make_path_from_is_chain strat
      · simp only [Option.mem_def]
        intro g g_in
        have in_moves := (strat (Sum.inr R, Γs, Rs) (by rfl)
          ⟨exists_non_box_move.choose,
            move_iff_in_moves.1 exists_non_box_move.choose_spec.1⟩).2
        have := make_path_from_head? strat
          (strat (Sum.inr R, Γs, Rs) (by rfl)
            ⟨exists_non_box_move.choose,
              move_iff_in_moves.1 exists_non_box_move.choose_spec.1⟩)
        simp only [this, Option.some.injEq] at g_in
        rw [←g_in]
        constructor
        · exact move_iff_in_moves.2 in_moves
        · simp only [Game.Pos.moves, Game.moves] at in_moves
          rcases (Finset.mem_filterMap _).mp in_moves with ⟨Γ, _Γ_R, move_eq⟩
          by_cases hmem : Γ ∈ Γs
          · simp [hmem] at move_eq
          · simp [hmem] at move_eq
            have strat_eq :
                (strat (Sum.inr R, Γs, Rs) (by rfl)
                    ⟨exists_non_box_move.choose,
                      move_iff_in_moves.1 exists_non_box_move.choose_spec.1⟩).1 =
                  (Sum.inl Γ, Γs, R :: Rs) :=
              move_eq.symm
            rw [strat_eq]
            simp [isBox]
    else by simp_all [makePathFrom]
termination_by
  coalgebraGame.wf.2.wrap g
decreasing_by
  · apply coalgebraGame.move_rel
    exact move_iff_in_moves.1 (g_def ▸ exists_non_box_move.choose_spec.1)
  · apply coalgebraGame.move_rel
    exact (strat (Sum.inr R, Γs, Rs) (by rfl)
      ⟨exists_non_box_move.choose,
        move_iff_in_moves.1 (g_def ▸ exists_non_box_move.choose_spec.1)⟩).2

lemma make_path_is_max (strat : Strategy coalgebraGame Builder) (g : coalgebraGame.Pos) :
    ¬ ∃ g',
      nonBoxMove ((makePathFrom strat g).getLast (make_path_from_is_nonempty strat g)) g' :=
  open Classical in
  match g_def : g with
  | ⟨Sum.inl Γ, Γs, Rs⟩ => if exists_non_box_move : ∃ g', nonBoxMove g g'
    then by
      simp_all only [makePathFrom, ↓reduceDIte]
      convert make_path_is_max strat exists_non_box_move.choose using 4
      simp [List.getLast_cons (make_path_from_is_nonempty strat exists_non_box_move.choose)]
    else by simp_all [makePathFrom]
  | ⟨Sum.inr R, Γs, Rs⟩ => if exists_non_box_move : ∃ g', nonBoxMove g g'
    then by
      simp_all only [makePathFrom, ↓reduceDIte]
      convert
        make_path_is_max strat
          ((strat ⟨Sum.inr R, Γs, Rs⟩
            (by rfl)
            ⟨exists_non_box_move.choose,
              move_iff_in_moves.1 (g_def ▸ exists_non_box_move.choose_spec.1)⟩))
        using 4
      simp [
        List.getLast_cons (make_path_from_is_nonempty strat
          ((strat ⟨Sum.inr R, Γs, Rs⟩
            (by rfl)
            ⟨exists_non_box_move.choose,
              move_iff_in_moves.1 (g_def ▸ exists_non_box_move.choose_spec.1)⟩)))]
    else by simp_all [makePathFrom]
termination_by
  coalgebraGame.wf.2.wrap g
decreasing_by
  · apply coalgebraGame.move_rel
    exact move_iff_in_moves.1 (g_def ▸ exists_non_box_move.choose_spec.1)
  · apply coalgebraGame.move_rel
    exact (strat (Sum.inr R, Γs, Rs) (by rfl)
      ⟨exists_non_box_move.choose,
        move_iff_in_moves.1 (g_def ▸ exists_non_box_move.choose_spec.1)⟩).2

lemma make_path_is_in_cone (Δ : SplitSequent) (strat : Strategy coalgebraGame Builder)
    (g : coalgebraGame.Pos) (in_cone : inMyCone strat (startPos Δ) g)
    (h : winning strat (startPos Δ)) :
    ∀ i, inMyCone strat (startPos Δ) ((makePathFrom strat g).get i) := by
  intro ⟨i_val, i_prop⟩
  cases i_val
  case zero =>
    convert in_cone using 1
    have := make_path_from_head strat g
    grind
  case succ i =>
    rcases g with ⟨Γ | R, Γs, Rs⟩
    · by_cases exists_non_box_move : ∃ g', nonBoxMove ⟨Sum.inl Γ, Γs, Rs⟩ g'
      · simp only [makePathFrom, exists_non_box_move, ↓reduceDIte,
          List.get_eq_getElem, List.getElem_cons_succ]
        simp [makePathFrom] at i_prop
        apply make_path_is_in_cone Δ strat exists_non_box_move.choose ?_ h ⟨i, by grind⟩
        exact inMyCone.oStep in_cone (by rfl)
          (move_iff_in_moves.1 exists_non_box_move.choose_spec.1)
      · simp [makePathFrom, exists_non_box_move] at i_prop
    · by_cases exists_non_box_move : ∃ g', nonBoxMove ⟨Sum.inr R, Γs, Rs⟩ g'
      · simp only [makePathFrom, exists_non_box_move, ↓reduceDIte,
          List.get_eq_getElem, List.getElem_cons_succ]
        simp only [makePathFrom, exists_non_box_move, ↓reduceDIte, List.length_cons,
          Nat.succ_lt_succ_iff] at i_prop
        apply make_path_is_in_cone Δ strat _ ?_ h ⟨i, i_prop⟩
        apply inMyCone.myStep in_cone
      · simp [makePathFrom, exists_non_box_move] at i_prop

lemma always_exists_maximal_path_from_root_or_after (Γ : SplitSequent)
    (strat : Strategy coalgebraGame Builder) (h : winning strat (startPos Γ))
    (g : coalgebraGame.Pos) (in_cone : inMyCone strat (startPos Γ) g)
    (head_cases : afterBox g ∨ g = startPos Γ) :
    ∃ π : MaximalPath Γ strat, π.first = g := by
  use {
    list := makePathFrom strat g
    ne := make_path_from_is_nonempty strat g
    chain := make_path_from_is_chain strat g
    max := make_path_is_max strat g
    head_cases := by
      have := make_path_from_head strat g
      rw [this]
      exact head_cases
    in_cone := by
      intro g' g'_in
      have ⟨i, i_eq⟩ := List.mem_iff_get.1 g'_in
      subst i_eq
      exact make_path_is_in_cone Γ strat g in_cone h i}
  exact make_path_from_head strat g

/-- Auxiliary declaration used in the GL coalgebra development. -/
def proverSplitSequent (g : coalgebraGame.Pos) (h : coalgebraGame.turn g = Prover) := match g with
  | ⟨Sum.inl Γ, Γs, Rs⟩ => Γ
  | ⟨Sum.inr R, Γ :: Γs, Rs⟩ => False.elim (by change Builder = Prover at h; cases h)

/-- Recovers the prover sequent from an explicitly identified prover game position. -/
lemma prover_SplitSequent_eq_of_inl {g : coalgebraGame.Pos}
    {h : coalgebraGame.turn g = Prover} {Γ Γs Rs}
    (hg : (Sum.inl Γ, Γs, Rs) = g) :
    proverSplitSequent g h = Γ := by
  cases hg
  rfl

/-- Auxiliary declaration used in the GL coalgebra development. -/
def firstSplitSequent {Γ : SplitSequent} {strat : Strategy coalgebraGame Builder}
  : MaximalPath Γ strat → SplitSequent := fun π ↦
  proverSplitSequent π.first (maximal_path_starts_in_prover_turn π)

lemma first_SplitSequent_eq_of_first
    {Γ : SplitSequent} {strat : Strategy coalgebraGame Builder}
    (π : MaximalPath Γ strat) {Δ Δs Rs}
    (hfirst : π.first = (Sum.inl Δ, Δs, Rs)) :
    firstSplitSequent π = Δ := by
  rcases π with ⟨list, ne, chain, max, head_cases, in_cone⟩
  unfold MaximalPath.first at hfirst
  unfold firstSplitSequent
  unfold MaximalPath.first
  cases list with
  | nil =>
    contradiction
  | cons x xs =>
    simp only [List.head_cons] at hfirst
    rcases x with ⟨Δ' | R, Δs', Rs'⟩
    · injection hfirst with hinfo hrest
      exact Sum.inl.inj hinfo
    · cases hfirst

/-- Auxiliary declaration used in the GL coalgebra development. -/
def lastSplitSequent {Γ : SplitSequent} {strat : Strategy coalgebraGame Builder}
    (h : winning strat (startPos Γ)) :
    MaximalPath Γ strat → SplitSequent := fun π ↦
  proverSplitSequent π.last (maximal_path_ends_in_prover_turn h π)

/-- Two maximal paths are related if two steps in the game can connect tail to head. -/
def pathRelation (Γ : SplitSequent) (strat : Strategy coalgebraGame Builder)
    (π₁ π₂ : MaximalPath Γ strat) :=
  (Relation.Comp Move Move) π₁.last π₂.first

-- Interesting for MathLib?
lemma Relation.TransGen.swap_eq_swap_rel {α : Type} (r : α → α → Prop) :
  Function.swap (Relation.TransGen r) = Relation.TransGen (Function.swap r) := by
  ext x y
  constructor
  all_goals
    intro mp
    induction mp
    case single x y_x => exact Relation.TransGen.single y_x
    case tail x z y_x x_z ih => exact Relation.TransGen.head x_z ih

lemma maximal_path_refl_trans_gen (as) (ne : as ≠ [])
    (chain : List.IsChain nonBoxMove as) :
    Relation.ReflTransGen Move (as.head ne) (as.getLast ne) := by
  induction chain
  case nil => simp at ne
  case singleton g =>
    simp only [List.head_cons, List.getLast_singleton]
    exact Relation.ReflTransGen.refl
  case cons_cons g g' gs g_g' gs_chain ih =>
    simp only [List.head_cons, ne_eq, reduceCtorEq, not_false_eq_true] at ih
    exact Relation.ReflTransGen.head g_g'.1 (ih trivial)

/-- Builds the Kripke counter-model from a Builder winning strategy. -/
def gameBModel (Γ : SplitSequent) {strat : Strategy coalgebraGame Builder}
    (h : winning strat (startPos Γ)) :
    Model (MaximalPath Γ strat) where
  V π n := at n ∉ (lastSplitSequent h π).toSequent
  R := Relation.TransGen (pathRelation Γ strat)
  trans := fun {_ _ _} hxy hyz => Relation.TransGen.trans hxy hyz
  con_wf := by
    simp only [Relation.TransGen.swap_eq_swap_rel]
    apply WellFounded.transGen
    let instFunLike : FunLike Unit (MaximalPath Γ strat) GamePos := by exact {
      coe := fun u π ↦ π.first
      coe_injective' := by intro u w; grind}
    have instRelHome :
        RelHomClass Unit (Function.swap (pathRelation Γ strat))
          (Relation.TransGen (Function.swap Move)) := by
      exact {
        map_rel := by
          intro f ρ π π_ρ
          change Relation.TransGen (Function.swap Move) ρ.first π.first
          simp only [←Relation.TransGen.swap_eq_swap_rel, Function.swap]
          simp only [Function.swap, pathRelation, Relation.Comp] at π_ρ
          rcases π_def : π with ⟨π_under, ne, chain⟩
          have π_rel := maximal_path_refl_trans_gen π_under ne chain
          simp only [MaximalPath.first]
          apply Relation.TransGen.trans_right π_rel
          have ⟨y, ⟨x_y, y_z⟩⟩ := π_ρ
          apply Relation.TransGen.tail (Relation.TransGen.single ?_) y_z
          · convert x_y
            simp [π_def]}
    -- using RelHomClass.wellFounded feels like overkill, but it works.
    apply @RelHomClass.wellFounded _ _
      (Function.swap (pathRelation Γ strat))
      (Relation.TransGen (Function.swap Move)) Unit instFunLike instRelHome ()
      (WellFounded.transGen coalgebraGame.wf.2)

lemma move_from_last_implies_box {Γ : SplitSequent}
    {strat : Strategy coalgebraGame Builder} (π : MaximalPath Γ strat) :
    ∀ x, Move π.last x → isBox x := by
  intro x π_x
  by_contra h
  rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
  apply max
  refine ⟨x, ⟨π_x, h⟩⟩

lemma diamond_in_of_move_move_diamond_in
  {x z} (hx hz) (x_z : (Relation.Comp Move Move) x z) :
    ∀ φ,
      ◇ φ ∈ (proverSplitSequent x hx).toSequent →
        ◇ φ ∈ (proverSplitSequent z hz).toSequent := by
  simp only [Relation.Comp] at x_z
  have ⟨y, x_y, y_z⟩ := x_z
  rcases x with ⟨Γ | R, Γs, Rs⟩ <;> try (change Builder = Prover at hx; cases hx)
  rcases x_y
  case prover R R_Γ =>
  rcases y_z
  case builder Γ' Γ'_R nrep =>
  simp only [proverSplitSequent]
  intro φ φ_in
  simp only [SplitSequent.ruleApps, Finset.mem_filterMap, Option.dite_none_right_eq_some,
    and_exists_self, Sum.exists] at R_Γ
  rcases R_Γ with ⟨ψ, ψ_in, eq⟩ | ⟨ψ, ψ_in, eq⟩
  all_goals
    cases ψ <;> try grind [RuleApp.splitSequents, SplitSequent.toSequent]
    case box =>
      simp only [Option.some.injEq] at eq
      subst eq
      simp only [RuleApp.splitSequents, Finset.union_singleton, Finset.mem_singleton] at Γ'_R
      subst Γ'_R
      simp only [SplitSequent.toSequent, Finset.mem_image, Sum.exists, Sum.elim_inl,
        id_eq, exists_eq_right, Sum.elim_inr]
      simp only [SplitSequent.toSequent, Finset.mem_image, Sum.exists, Sum.elim_inl,
        id_eq, exists_eq_right, Sum.elim_inr] at φ_in
      rcases φ_in with φ_in | φ_in
      · left
        exact Finset.mem_insert.mpr (Or.inr (left_diamond_mem_D_of_ne φ_in (by simp)))
      · right
        exact Finset.mem_insert.mpr (Or.inr (right_diamond_mem_D_of_ne φ_in (by simp)))

lemma diamond_in_last_of_diamond_in_first {Γ : SplitSequent}
    {strat : Strategy coalgebraGame Builder} (h : winning strat (startPos Γ)) :
    ∀ π : MaximalPath Γ strat, ∀ φ (i : ℕ) (lt : i < π.list.length) helper (ps),
      ◇ φ ∈
          (proverSplitSequent
            ((π.list)[π.list.length - i - 1]'helper) ps).toSequent →
        ◇ φ ∈ (lastSplitSequent h π).toSequent := by
  intro π φ i lt helper ps φ_in
  cases i
  case zero =>
    convert φ_in
    simp [lastSplitSequent, List.getLast_eq_getElem]
  case succ i =>
    cases i
    case zero =>
      exfalso
      have P_turn_last := maximal_path_ends_in_prover_turn h π
      have eq : π.list.length - (0 + 1) - 1 = π.list.length - 2 := by omega
      have eq2 : π.list.length - (0 + 1) - 1 + 1 = π.list.length - 1 := by omega
      have eq3 : π.list.length - 1 - 1 = π.list.length - 2 := by omega
      rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
      have length_gt_one : π.length > 1 := by
        simp at lt
        grind
      have u₁_last := List.IsChain.getElem chain (π.length - (0 + 1) - 1) (by omega)
      have helper : π[π.length - 1]'(by omega) = π.getLast ne := by grind
      simp_all only [zero_add, MaximalPath.last]
      rcases u₁_def : π[π.length - 2] with ⟨Γ | R, Γs, Rs⟩
      · simp_all only
        have u₁_last := move_iff_in_moves.1 u₁_last.1
        rcases (Finset.mem_map).mp u₁_last with ⟨R, _Γ_R, eq⟩
        rw [←eq] at P_turn_last
        change Builder = Prover at P_turn_last
        cases P_turn_last
      · simp only [zero_add] at ps
        have helper : ¬ coalgebraGame.turn ⟨Sum.inr R, Γs, Rs⟩ = Prover := by
          change ¬ Builder = Prover
          intro h
          cases h
        apply helper
        convert ps
        convert Eq.symm u₁_def
    case succ i =>
      rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
      have ne_zero : π.length ≠ 0 := by grind
      have length_gt_two : π.length > 2 := by
        simp at lt
        grind
      have eq3 : π.length - (i + 1 + 1) - 1 = π.length - i - 3 := by omega
      have eq2 : π.length - (i + 1 + 1) - 1 + 1 = π.length - i - 2 := by simp_all; omega
      have y_u₁ := List.IsChain.getElem chain (π.length - (i + 1 + 1) - 1) (by omega)
      have u₁_u₂ := List.IsChain.getElem chain (π.length - (i + 1 + 1) - 1 + 1) (by omega)
      have P_turn_u₂ : coalgebraGame.turn π[π.length - (i + 1 + 1) - 1 + 1 + 1] = Prover := by
        simp at ps
        rcases u₁_def : π[π.length - (i + 1 + 1) - 1 + 1] with ⟨Γ | R, Γs, Rs⟩
        · have := move_iff_in_moves.1 y_u₁.1
          exfalso
          rcases y_def : π[π.length - (i + 1 + 1) - 1] with ⟨Γ | R, Γs, Rs⟩
          · rw [u₁_def, y_def] at this
            rcases (Finset.mem_map).mp this with ⟨R, _R_Γ, move_eq⟩
            cases move_eq
          · simp [y_def] at ps
        · have := move_iff_in_moves.1 u₁_u₂.1
          rw [u₁_def] at this
          rcases (Finset.mem_filterMap _).mp this with ⟨Γ, _Γ_R, move_eq⟩
          by_cases hmem : Γ ∈ Γs
          · simp [hmem] at move_eq
          · simp [hmem] at move_eq
            have u₂_def :
                π[π.length - (i + 1 + 1) - 1 + 1 + 1] =
                  (Sum.inl Γ, Γs, R :: Rs) :=
              move_eq.symm
            rw [u₂_def]
            rfl
      have := diamond_in_of_move_move_diamond_in ps P_turn_u₂
        ⟨_, ⟨y_u₁.1, u₁_u₂.1⟩⟩ φ φ_in
      refine diamond_in_last_of_diamond_in_first h
        ⟨π, ne, chain, max, head_cases, in_cone⟩ φ i (by grind) (by grind) ?_ ?_
      · change coalgebraGame.turn π[π.length - i - 1] = Prover
        convert P_turn_u₂ using 3
        grind
      · convert diamond_in_of_move_move_diamond_in _ _
          ⟨_, ⟨y_u₁.1, u₁_u₂.1⟩⟩ φ φ_in using 3
        any_goals simp
        · grind
        · exact P_turn_u₂

lemma formula_in_successor_of_diamond_formula_in {Γ : SplitSequent}
    {strat : Strategy coalgebraGame Builder} (h : winning strat (startPos Γ))
    {π ρ : MaximalPath Γ strat} (π_ρ : pathRelation Γ strat π ρ) :
    ∀ φ,
      ◇ φ ∈ (lastSplitSequent h π).toSequent →
        φ ∈ (firstSplitSequent ρ).toSequent := by
  intro φ diφ_in
  simp only [pathRelation, Relation.Comp] at π_ρ
  have ⟨y, x_y, y_z⟩ := π_ρ
  have hx := maximal_path_ends_in_prover_turn h π
  rcases last_def : π.last with ⟨Γ | R, Γs, Rs⟩ <;>
    try (rw [last_def] at hx; change Builder = Prover at hx; cases hx)
  simp only [last_def] at x_y
  simp only [lastSplitSequent, last_def] at diφ_in
  simp only [proverSplitSequent] at diφ_in
  have := move_iff_in_moves.1 x_y
  rcases (Finset.mem_map).mp this with ⟨R, R_Γ, y_def⟩
  subst y_def
  have := move_iff_in_moves.1 y_z
  rcases (Finset.mem_filterMap _).mp this with ⟨Γ', Γ'_R, first_def⟩
  by_cases nrep : Γ' ∈ Γ :: Γs
  · simp [nrep] at first_def
  · simp [nrep] at first_def
    have first_def' : ρ.first = (Sum.inl Γ', Γ :: Γs, R :: Rs) :=
      first_def.symm
    rw [first_SplitSequent_eq_of_first ρ first_def']
    have R_mem := R_Γ
    have R_f : f R = Γ := f_of_mem_ruleApps R_mem
    have R_box : R.isBox := by
      rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
      simp only [not_exists] at max
      have := max (Sum.inr R, Γ :: Γs, Rs)
      simp only [nonBoxMove, isBox, not_and, not_not] at this
      apply this
      convert x_y
    cases R <;> simp [RuleApp.isBox] at R_box
    all_goals
      simp only [f] at R_f
      cases R_f
      simp only [RuleApp.splitSequents, Finset.union_singleton, Finset.mem_singleton] at Γ'_R
      subst Γ'_R
      simp only [SplitSequent.toSequent, Finset.mem_image, Sum.exists, Sum.elim_inl,
        id_eq, exists_eq_right, Sum.elim_inr]
      simp only [SplitSequent.toSequent, Finset.mem_image, Sum.exists, Sum.elim_inl,
        id_eq, exists_eq_right, Sum.elim_inr] at diφ_in
      rcases diφ_in with diφ_in | diφ_in
      · left
        exact Finset.mem_insert.mpr (Or.inr (left_unDi_mem_D_of_ne diφ_in (by simp)))
      · right
        exact Finset.mem_insert.mpr (Or.inr (right_unDi_mem_D_of_ne diφ_in (by simp)))

lemma diamond_in_path_of_diamond_formula_in {Γ : SplitSequent}
    {strat : Strategy coalgebraGame Builder} (h : winning strat (startPos Γ))
    {π ρ : MaximalPath Γ strat} (π_ρ : Relation.TransGen (pathRelation Γ strat) π ρ) :
    ∀ φ,
      ◇ φ ∈ (lastSplitSequent h π).toSequent →
        ◇ φ ∈ (firstSplitSequent ρ).toSequent := by
  intro φ φ_in
  induction π_ρ
  case single ρ π_ρ =>
    exact diamond_in_of_move_move_diamond_in
      (maximal_path_ends_in_prover_turn h π) (maximal_path_starts_in_prover_turn ρ)
      π_ρ φ φ_in
  case tail γ _ _ rel ih =>
    apply diamond_in_of_move_move_diamond_in
      (maximal_path_ends_in_prover_turn h _) (maximal_path_starts_in_prover_turn _)
      rel φ
    apply diamond_in_last_of_diamond_in_first h _ φ (γ.list.length - 1)
    · rcases γ with ⟨ρ, ne, chain, max, head_cases, in_cone⟩
      simp
      grind
    · convert ih
      simp only [firstSplitSequent, MaximalPath.first]
      have : 0 < γ.list.length := by have := γ.ne; grind
      congr
      rw [←List.getElem_zero_eq_head]
      · congr
        grind
      · grind
    · rcases γ with ⟨ρ, ne, chain, max, head_cases, in_cone⟩
      simp
      grind
    · convert (maximal_path_starts_in_prover_turn γ)
      simp only [MaximalPath.first]
      have : 0 < γ.list.length := by have := γ.ne; grind
      rw [←List.getElem_zero_eq_head]
      · congr
        grind
      · grind

lemma formula_in_path_of_diamond_formula_in {Γ : SplitSequent}
    {strat : Strategy coalgebraGame Builder} (h : winning strat (startPos Γ))
    {π ρ : MaximalPath Γ strat} (π_ρ : Relation.TransGen (pathRelation Γ strat) π ρ) :
    ∀ φ,
      ◇ φ ∈ (lastSplitSequent h π).toSequent →
        φ ∈ (firstSplitSequent ρ).toSequent := by
  intro φ φ_in
  cases π_ρ
  case single π_ρ => exact formula_in_successor_of_diamond_formula_in h π_ρ φ φ_in
  case tail γ π_γ γ_ρ =>
    have φ_in_γ := diamond_in_path_of_diamond_formula_in h π_γ φ φ_in
    apply formula_in_successor_of_diamond_formula_in h γ_ρ φ ?_
    apply diamond_in_last_of_diamond_in_first h γ φ (γ.list.length - 1)
    · rcases γ with ⟨ρ, ne, chain, max, head_cases, in_cone⟩
      simp
      grind
    · convert φ_in_γ
      simp only [firstSplitSequent, MaximalPath.first]
      have : 0 < γ.list.length := by have := γ.ne; grind
      congr
      rw [←List.getElem_zero_eq_head]
      · congr
        grind
      · grind
    · rcases γ with ⟨ρ, ne, chain, max, head_cases, in_cone⟩
      simp
      grind
    · convert (maximal_path_starts_in_prover_turn γ)
      simp only [MaximalPath.first]
      have : 0 < γ.list.length := by have := γ.ne; grind
      rw [←List.getElem_zero_eq_head]
      · congr
        grind
      · grind

/-- A terminal split rule application cannot be available at the last node of a
Builder-winning path. -/
lemma no_terminal_rule_app_at_last {Δ : SplitSequent}
    {strat : Strategy coalgebraGame Builder}
    (h : winning strat (startPos Δ)) (π : MaximalPath Δ strat) (R : RuleApp)
    (R_in : R ∈ SplitSequent.ruleApps (lastSplitSequent h π))
    (R_empty : R.splitSequents = ∅) :
    False := by
  have P_turn_y : coalgebraGame.turn π.last = Prover := maximal_path_ends_in_prover_turn h π
  rcases last_def : π.last with ⟨Γ' | R', Γs', Rs'⟩ <;>
    try (rw [last_def] at P_turn_y; change Builder = Prover at P_turn_y; cases P_turn_y)
  have eq : Γ' = lastSplitSequent h π := by
    unfold lastSplitSequent
    simp only [last_def]
    simp [proverSplitSequent]
  subst eq
  have in_cone : inMyCone strat (startPos Δ) π.last := by
    rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
    apply in_cone
    simp
  let next_move : GamePos := ⟨Sum.inr R, (lastSplitSequent h π) :: Γs', Rs'⟩
  have B_turn_next : coalgebraGame.turn next_move = Builder := by
    unfold Game.turn next_move
    simp
  have next_in_moves : next_move ∈ coalgebraGame.moves π.last := by
    simp only [last_def]
    unfold next_move
    apply move_iff_in_moves.1
    apply Move.prover
    exact R_in
  have still_winning_next : winning strat next_move :=
    winning_of_in_cone_winning
      (inMyCone.oStep in_cone (maximal_path_ends_in_prover_turn h π) next_in_moves) h
  have has_moves := winning_has_moves B_turn_next still_winning_next
  unfold Game.moves next_move at has_moves
  simp [R_empty] at has_moves

/-- A non-box split rule application cannot extend the last node of a maximal path. -/
lemma no_nonbox_rule_app_at_last {Δ : SplitSequent}
    {strat : Strategy coalgebraGame Builder}
    (h : winning strat (startPos Δ)) (π : MaximalPath Δ strat) (R : RuleApp)
    (R_in : R ∈ SplitSequent.ruleApps (lastSplitSequent h π)) (R_nonbox : ¬ R.isBox) :
    False := by
  have P_turn_y : coalgebraGame.turn π.last = Prover := maximal_path_ends_in_prover_turn h π
  rcases last_def : π.last with ⟨Γ' | R', Γs', Rs'⟩ <;>
    try (rw [last_def] at P_turn_y; change Builder = Prover at P_turn_y; cases P_turn_y)
  have eq : Γ' = lastSplitSequent h π := by
    unfold lastSplitSequent
    simp only [last_def]
    simp [proverSplitSequent]
  subst eq
  let next_move : GamePos := ⟨Sum.inr R, (lastSplitSequent h π) :: Γs', Rs'⟩
  have next_in_moves : next_move ∈ coalgebraGame.moves π.last := by
    simp only [last_def]
    unfold next_move
    apply move_iff_in_moves.1
    apply Move.prover
    exact R_in
  rcases π with ⟨π, ne, chain, max⟩
  apply max
  refine ⟨next_move, ?_, ?_⟩
  · exact move_iff_in_moves.2 next_in_moves
  · unfold next_move
    simpa [isBox] using R_nonbox

/-- The final reverse index points to a valid element of a nonempty maximal path. -/
private lemma maximal_path_last_reverse_index_lt {Γ : SplitSequent}
    {strat : Strategy coalgebraGame Builder}
    (π : MaximalPath Γ strat) : π.list.length - 1 < π.list.length := by
  rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
  simp
  grind

/-- The final reverse index lands at the first node of a nonempty maximal path. -/
private lemma maximal_path_first_reverse_index_lt {Γ : SplitSequent}
    {strat : Strategy coalgebraGame Builder}
    (π : MaximalPath Γ strat) :
    π.list.length - (π.list.length - 1) - 1 < π.list.length := by
  have length_pos : 0 < π.list.length := by
    have := π.ne
    grind
  omega

/-- The first node, addressed by the final reverse index, is a Prover turn. -/
private lemma maximal_path_first_reverse_index_turn {Γ : SplitSequent}
    {strat : Strategy coalgebraGame Builder}
    (π : MaximalPath Γ strat) :
    coalgebraGame.turn
      (π.list[π.list.length - (π.list.length - 1) - 1]'
        (maximal_path_first_reverse_index_lt π)) = Prover := by
  have idx_zero : π.list.length - (π.list.length - 1) - 1 = 0 := by
    have length_pos : 0 < π.list.length := by
      have := π.ne
      grind
    omega
  convert (maximal_path_starts_in_prover_turn π)
  simp only [MaximalPath.first, idx_zero]
  rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
  cases π with
  | nil => contradiction
  | cons x xs => cases x; rfl

/-- Convert first-sequent membership to membership at the final reverse index. -/
private lemma first_split_sequent_mem_at_reverse_index {Γ : SplitSequent}
    {strat : Strategy coalgebraGame Builder}
    (π : MaximalPath Γ strat) {φ : SplitFormula} :
    φ ∈ firstSplitSequent π →
    φ ∈ proverSplitSequent
      (π.list[π.list.length - (π.list.length - 1) - 1]'
        (maximal_path_first_reverse_index_lt π))
      (maximal_path_first_reverse_index_turn π) := by
  intro φ_in
  have idx_zero : π.list.length - (π.list.length - 1) - 1 = 0 := by
    have length_pos : 0 < π.list.length := by
      have := π.ne
      grind
    omega
  convert φ_in
  simp only [firstSplitSequent, MaximalPath.first, idx_zero]
  rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
  cases π with
  | nil => contradiction
  | cons x xs => cases x; simp [proverSplitSequent]

/-- A left box formula at the last node produces a related maximal path from its premise. -/
private lemma box_successor_path_of_last_left_box {Δ : SplitSequent}
    {strat : Strategy coalgebraGame Builder}
    (h : winning strat (startPos Δ)) (π : MaximalPath Δ strat) {φ : Formula}
    (box_in : Sum.inl (□φ) ∈ lastSplitSequent h π) :
    ∃ ρ : MaximalPath Δ strat,
      Relation.TransGen (pathRelation Δ strat) π ρ ∧
        (Sum.inl φ ∈ firstSplitSequent ρ ∨ Sum.inr φ ∈ firstSplitSequent ρ) := by
  have P_turn_y : coalgebraGame.turn π.last = Prover := maximal_path_ends_in_prover_turn h π
  rcases last_def : π.last with ⟨Γ' | R', Γs', Rs'⟩ <;>
    try (rw [last_def] at P_turn_y; change Builder = Prover at P_turn_y; cases P_turn_y)
  have eq : Γ' = lastSplitSequent h π := by
    unfold lastSplitSequent
    simp only [last_def]
    simp [proverSplitSequent]
  subst eq
  have in_cone : inMyCone strat (startPos Δ) π.last := by
    rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
    apply in_cone
    simp
  let next_move : coalgebraGame.Pos :=
    ⟨Sum.inr (RuleApp.boxₗ (lastSplitSequent h π) φ box_in),
      (lastSplitSequent h π) :: Γs', Rs'⟩
  have move_last_next : Move π.last next_move := by
    unfold next_move
    simp only [last_def]
    apply Move.prover
    exact ruleApp_boxl_mem box_in
  have B_turn_next : coalgebraGame.turn next_move = Builder := by rfl
  have next_in_moves : next_move ∈ coalgebraGame.moves π.last :=
    move_iff_in_moves.1 move_last_next
  have next_in_cone : inMyCone strat (startPos Δ) next_move :=
    inMyCone.oStep in_cone (by simpa [last_def] using P_turn_y) next_in_moves
  have B_turn_winning : winning strat next_move := winning_of_in_cone_winning next_in_cone h
  let next_next_move := strat next_move B_turn_next (winning_has_moves B_turn_next B_turn_winning)
  rcases next_next_move_def : next_next_move with ⟨nextNext, next_next_mem⟩
  have move_next_next : Move next_move nextNext := move_iff_in_moves.2 next_next_mem
  have next_next_in_cone : inMyCone strat (startPos Δ) nextNext := by
    simpa [next_next_move, next_next_move_def] using
      (inMyCone.myStep next_in_cone
        (winning_has_moves B_turn_next B_turn_winning) B_turn_next)
  have after_box_next_next : afterBox nextNext := by
    have move_next_next' := move_next_next
    unfold next_move at move_next_next'
    cases move_next_next'
    simp [afterBox, RuleApp.isBox]
  have ⟨ρ, ρ_def⟩ :=
    always_exists_maximal_path_from_root_or_after Δ strat h nextNext next_next_in_cone
      (Or.inl after_box_next_next)
  refine ⟨ρ, ?_, ?_⟩
  · apply Relation.TransGen.single
    simp only [pathRelation, Relation.Comp]
    exact ⟨next_move, move_last_next, ρ_def ▸ move_next_next⟩
  · have hφ : φ ∈ (firstSplitSequent ρ).toSequent := by
      have move_next_next' := move_next_next
      unfold next_move at move_next_next'
      cases move_next_next'
      case builder Γ_mem Γ_not_mem =>
        simp only [RuleApp.splitSequents, Finset.mem_singleton] at Γ_mem
        subst Γ_mem
        rw [first_SplitSequent_eq_of_first ρ ρ_def]
        simp [SplitSequent.toSequent, SplitSequent.D]
    simpa [SplitSequent.toSequent] using hφ

/-- A right box formula at the last node produces a related maximal path from its premise. -/
private lemma box_successor_path_of_last_right_box {Δ : SplitSequent}
    {strat : Strategy coalgebraGame Builder}
    (h : winning strat (startPos Δ)) (π : MaximalPath Δ strat) {φ : Formula}
    (box_in : Sum.inr (□φ) ∈ lastSplitSequent h π) :
    ∃ ρ : MaximalPath Δ strat,
      Relation.TransGen (pathRelation Δ strat) π ρ ∧
        (Sum.inl φ ∈ firstSplitSequent ρ ∨ Sum.inr φ ∈ firstSplitSequent ρ) := by
  have P_turn_y : coalgebraGame.turn π.last = Prover := maximal_path_ends_in_prover_turn h π
  rcases last_def : π.last with ⟨Γ' | R', Γs', Rs'⟩ <;>
    try (rw [last_def] at P_turn_y; change Builder = Prover at P_turn_y; cases P_turn_y)
  have eq : Γ' = lastSplitSequent h π := by
    unfold lastSplitSequent
    simp only [last_def]
    simp [proverSplitSequent]
  subst eq
  have in_cone : inMyCone strat (startPos Δ) π.last := by
    rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
    apply in_cone
    simp
  let next_move : coalgebraGame.Pos :=
    ⟨Sum.inr (RuleApp.boxᵣ (lastSplitSequent h π) φ box_in),
      (lastSplitSequent h π) :: Γs', Rs'⟩
  have move_last_next : Move π.last next_move := by
    unfold next_move
    simp only [last_def]
    apply Move.prover
    exact ruleApp_boxr_mem box_in
  have B_turn_next : coalgebraGame.turn next_move = Builder := by rfl
  have next_in_moves : next_move ∈ coalgebraGame.moves π.last :=
    move_iff_in_moves.1 move_last_next
  have next_in_cone : inMyCone strat (startPos Δ) next_move :=
    inMyCone.oStep in_cone (by simpa [last_def] using P_turn_y) next_in_moves
  have B_turn_winning : winning strat next_move := winning_of_in_cone_winning next_in_cone h
  let next_next_move := strat next_move B_turn_next (winning_has_moves B_turn_next B_turn_winning)
  rcases next_next_move_def : next_next_move with ⟨nextNext, next_next_mem⟩
  have move_next_next : Move next_move nextNext := move_iff_in_moves.2 next_next_mem
  have next_next_in_cone : inMyCone strat (startPos Δ) nextNext := by
    simpa [next_next_move, next_next_move_def] using
      (inMyCone.myStep next_in_cone
        (winning_has_moves B_turn_next B_turn_winning) B_turn_next)
  have after_box_next_next : afterBox nextNext := by
    have move_next_next' := move_next_next
    unfold next_move at move_next_next'
    cases move_next_next'
    simp [afterBox, RuleApp.isBox]
  have ⟨ρ, ρ_def⟩ :=
    always_exists_maximal_path_from_root_or_after Δ strat h nextNext next_next_in_cone
      (Or.inl after_box_next_next)
  refine ⟨ρ, ?_, ?_⟩
  · apply Relation.TransGen.single
    simp only [pathRelation, Relation.Comp]
    exact ⟨next_move, move_last_next, ρ_def ▸ move_next_next⟩
  · have hφ : φ ∈ (firstSplitSequent ρ).toSequent := by
      have move_next_next' := move_next_next
      unfold next_move at move_next_next'
      cases move_next_next'
      case builder Γ_mem Γ_not_mem =>
        simp only [RuleApp.splitSequents, Finset.mem_singleton] at Γ_mem
        subst Γ_mem
        rw [first_SplitSequent_eq_of_first ρ ρ_def]
        simp [SplitSequent.toSequent, SplitSequent.D]
    simpa [SplitSequent.toSequent] using hφ

/-- The penultimate node of a non-box maximal path cannot also be a Prover turn. -/
private lemma no_penultimate_prover_turn {Δ : SplitSequent}
    {strat : Strategy coalgebraGame Builder}
    (h : winning strat (startPos Δ)) (π : MaximalPath Δ strat)
    (lt : 1 < π.list.length) helper
    (ps : coalgebraGame.turn (π.list[π.list.length - (0 + 1) - 1]'helper) = Prover) :
    False := by
  have P_turn_last := maximal_path_ends_in_prover_turn h π
  have eq : π.list.length - (0 + 1) - 1 = π.list.length - 2 := by omega
  have eq2 : π.list.length - (0 + 1) - 1 + 1 = π.list.length - 1 := by omega
  rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
  have length_gt_one : π.length > 1 := by simpa using lt
  have u₁_last := List.IsChain.getElem chain (π.length - (0 + 1) - 1) (by omega)
  have helper_last : π[π.length - 1]'(by omega) = π.getLast ne := by grind
  have u₁_last' : nonBoxMove π[π.length - 2] (π.getLast ne) := by
    convert u₁_last using 1
    · simpa [eq2] using helper_last.symm
  rcases u₁_def : π[π.length - 2] with ⟨Γ | R, Γs, Rs⟩
  · have u₁_last_mem := move_iff_in_moves.1 u₁_last'.1
    rw [u₁_def] at u₁_last_mem
    change π.getLast ne ∈
      Finset.map ⟨fun R ↦ (Sum.inr R, Γ :: Γs, Rs), by intro r1 r2; simp⟩
        (SplitSequent.ruleApps Γ) at u₁_last_mem
    rcases (Finset.mem_map).mp u₁_last_mem with ⟨R, _R_Γ, last_eq⟩
    have P_turn_last' : coalgebraGame.turn (π.getLast ne) = Prover := by
      simpa [MaximalPath.last] using P_turn_last
    rw [←last_eq] at P_turn_last'
    change Builder = Prover at P_turn_last'
    cases P_turn_last'
  · have ps' : coalgebraGame.turn (Sum.inr R, Γs, Rs) = Prover := by
      simp [eq, u₁_def] at ps
    change Builder = Prover at ps'
    cases ps'

mutual

/-- If Builder wins, no formula in the sequents at Prover positions evaluates to true. -/
lemma builder_win_strong {Δ : SplitSequent}
    (strat : Strategy coalgebraGame Builder) (h : winning strat (startPos Δ))
    (π : MaximalPath Δ strat) (φ) (i : ℕ) (lt : i < π.list.length) helper (ps) :
    Sum.inl φ ∈ proverSplitSequent ((π.list)[π.list.length - i - 1]'helper) ps ∨
      Sum.inr φ ∈ proverSplitSequent ((π.list)[π.list.length - i - 1]'helper) ps →
    ¬ evaluate (gameBModel Δ h, π) φ := by
  intro φ_in
  rcases φ_in with φ_in | φ_in
  · match h_i : i with
    | 0 =>
      exact builder_win_strong_left_zero strat h π φ i h_i (by simpa [h_i] using lt)
        (by simpa [h_i] using helper) (by simpa [h_i] using ps)
        (no_terminal_rule_app_at_last h π) (no_nonbox_rule_app_at_last h π)
        (by simpa [h_i] using φ_in)
    | Nat.succ j =>
      exact builder_win_strong_left_succ strat h π φ i j h_i (by simpa [h_i] using lt)
        (by simpa [h_i] using helper) (by simpa [h_i] using ps)
        (by simpa [h_i] using φ_in)
  · match h_i : i with
    | 0 =>
      exact builder_win_strong_right_zero strat h π φ i h_i (by simpa [h_i] using lt)
        (by simpa [h_i] using helper) (by simpa [h_i] using ps)
        (no_terminal_rule_app_at_last h π) (no_nonbox_rule_app_at_last h π)
        (by simpa [h_i] using φ_in)
    | Nat.succ j =>
      exact builder_win_strong_right_succ strat h π φ i j h_i (by simpa [h_i] using lt)
        (by simpa [h_i] using helper) (by simpa [h_i] using ps)
        (by simpa [h_i] using φ_in)
termination_by (φ.length, i, 4)
decreasing_by
  all_goals
    apply Prod.Lex.right
    first
    | apply Prod.Lex.left; omega
    | rw [h_i]; apply Prod.Lex.right; omega

/-- Left-side last-node case for `builder_win_strong`. -/
lemma builder_win_strong_left_zero {Δ : SplitSequent}
    (strat : Strategy coalgebraGame Builder) (h : winning strat (startPos Δ))
    (π : MaximalPath Δ strat) (φ) (i : ℕ) (h_i : i = 0) (lt : i < π.list.length)
    helper (ps)
    (noTerminal :
      ∀ R, R ∈ SplitSequent.ruleApps (lastSplitSequent h π) →
        R.splitSequents = ∅ → False)
    (noNonbox :
      ∀ R, R ∈ SplitSequent.ruleApps (lastSplitSequent h π) →
        ¬R.isBox → False) :
    Sum.inl φ ∈ proverSplitSequent ((π.list)[π.list.length - i - 1]'helper) ps →
    ¬ evaluate (gameBModel Δ h, π) φ := by
  subst i
  intro φ_in
  have φ_in' : Sum.inl φ ∈ lastSplitSequent h π := by
    convert φ_in
    simp [lastSplitSequent]
    congr
    grind
  cases φ
  case bottom => simp_all
  case top =>
    simp only [evaluate, not_true_eq_false]
    exact noTerminal
      (RuleApp.topₗ (lastSplitSequent h π) φ_in')
      (ruleApp_topl_mem φ_in') (by simp [RuleApp.splitSequents])
  case atom n =>
    simp only [evaluate, gameBModel, SplitSequent.toSequent, Finset.mem_image, Sum.exists,
      Sum.elim_inl, id_eq, exists_eq_right, Sum.elim_inr, Decidable.not_not]
    exact Or.inl φ_in'
  case negAtom n =>
    simp only [evaluate, gameBModel, SplitSequent.toSequent, Finset.mem_image, Sum.exists,
      Sum.elim_inl, id_eq, exists_eq_right, Sum.elim_inr, not_or, not_and,
      Decidable.not_not, Classical.not_imp]
    constructor
    · intro nφ_in
      exact noTerminal
        (RuleApp.axₗₗ (lastSplitSequent h π) n ⟨nφ_in, φ_in'⟩)
        (ruleApp_axll_mem ⟨nφ_in, φ_in'⟩)
        (by simp [RuleApp.splitSequents])
    · intro nφ_in
      exact noTerminal
        (RuleApp.axᵣₗ (lastSplitSequent h π) n ⟨nφ_in, φ_in'⟩)
        (ruleApp_axrl_mem ⟨nφ_in, φ_in'⟩)
        (by simp [RuleApp.splitSequents])
  case or φ1 φ2 => -- then we will make a move
    exfalso
    exact noNonbox
      (RuleApp.orₗ (lastSplitSequent h π) φ1 φ2 φ_in')
      (ruleApp_orl_mem φ_in') (by simp [RuleApp.isBox])
  case and φ1 φ2  => -- then we will make a move
    exfalso
    exact noNonbox
      (RuleApp.andₗ (lastSplitSequent h π) φ1 φ2 φ_in')
      (ruleApp_andl_mem φ_in') (by simp [RuleApp.isBox])
  case diamond φ =>
    simp only [evaluate, not_exists, not_and]
    intro ρ π_ρ
    exact builder_win_strong strat h ρ φ (ρ.list.length - 1)
      (maximal_path_last_reverse_index_lt ρ)
      (maximal_path_first_reverse_index_lt ρ)
      (maximal_path_first_reverse_index_turn ρ)
      (by
        have φ_in_2 :
            Sum.inl φ ∈ firstSplitSequent ρ ∨
              Sum.inr φ ∈ firstSplitSequent ρ := by
          have hφ : φ ∈ (firstSplitSequent ρ).toSequent :=
            formula_in_path_of_diamond_formula_in h π_ρ φ
              (by simp [SplitSequent.toSequent, φ_in'])
          simpa [SplitSequent.toSequent] using hφ
        rcases φ_in_2 with hleft | hright
        · exact Or.inl (first_split_sequent_mem_at_reverse_index ρ hleft)
        · exact Or.inr (first_split_sequent_mem_at_reverse_index ρ hright))
  case box φ =>
    simp only [evaluate, not_forall]
    have ⟨ρ, ρ_def, first_mem⟩ := box_successor_path_of_last_left_box h π φ_in'
    refine ⟨ρ, ?_, ?_⟩
    · simpa [gameBModel] using ρ_def
    · exact builder_win_strong strat h ρ φ (ρ.list.length - 1)
        (maximal_path_last_reverse_index_lt ρ)
        (maximal_path_first_reverse_index_lt ρ)
        (maximal_path_first_reverse_index_turn ρ)
        (by
          rcases first_mem with hleft | hright
          · exact Or.inl (first_split_sequent_mem_at_reverse_index ρ hleft)
          · exact Or.inr (first_split_sequent_mem_at_reverse_index ρ hright))
termination_by (φ.length, i, 3)
decreasing_by
  all_goals
    apply Prod.Lex.left
    simp [Formula.length]

/-- Left-side successor case for `builder_win_strong`. -/
lemma builder_win_strong_left_succ {Δ : SplitSequent}
    (strat : Strategy coalgebraGame Builder) (h : winning strat (startPos Δ))
    (π : MaximalPath Δ strat) (φ) (j i : ℕ) (h_j : j = i + 1)
    (lt : j < π.list.length) helper (ps) :
    Sum.inl φ ∈ proverSplitSequent ((π.list)[π.list.length - j - 1]'helper) ps →
    ¬ evaluate (gameBModel Δ h, π) φ := by
  subst j
  intro φ_in
  match h_i : i with
  | 0 =>
    exfalso
    exact no_penultimate_prover_turn h π (by simpa using lt) helper ps
  | Nat.succ i =>
    rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
    have ne_zero : π.length ≠ 0 := by grind
    have length_gt_two : π.length > 2 := by
      simp at lt
      grind
    have eq3 : π.length - (i + 1 + 1) - 1 = π.length - i - 3 := by omega
    have eq2 : π.length - (i + 1 + 1) - 1 + 1 = π.length - i - 2 := by
      have lt' : i + 1 + 1 < π.length := by
        simpa using lt
      omega
    have y_u₁ := List.IsChain.getElem chain (π.length - (i + 1 + 1) - 1) (by omega)
    have raw_u₁_u₂ := List.IsChain.getElem chain (π.length - (i + 1 + 1) - 1 + 1) (by omega)
    have no_box_u₁ := y_u₁.2
    simp only [Nat.succ_eq_add_one] at φ_in
    rcases y_def : π[π.length - (i + 1 + 1) - 1] with ⟨Γ | R, Γs, Rs⟩ <;>
      simp [y_def] at ps
    simp only [y_def] at φ_in
    simp only [y_def] at y_u₁
    have y_u₁_mem := move_iff_in_moves.1 y_u₁.1
    unfold Game.Pos.moves Game.moves at y_u₁_mem
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at y_u₁_mem
    rcases y_u₁_mem with ⟨R, R_Γ, u₁_def⟩
    have move_u₁_u₂ :
        nonBoxMove (Sum.inr R, Γ :: Γs, Rs)
          (π[π.length - (i + 1 + 1) - 1 + 1 + 1]'(by grind)) := by
      convert raw_u₁_u₂ -- dont understand why simp or rw doesn't do this
    have u₁_u₂_mem := move_iff_in_moves.1 move_u₁_u₂.1
    unfold Game.Pos.moves Game.moves at u₁_u₂_mem
    simp only [List.mem_cons, Finset.mem_filterMap, Option.ite_none_left_eq_some, not_or,
      Option.some.injEq] at u₁_u₂_mem
    rcases u₁_u₂_mem with ⟨Γ', Γ'_R, no_rep, u₂_def⟩
    have P_turn_u₂ : coalgebraGame.turn (Sum.inl Γ', Γ :: Γs, R :: Rs) = Prover := by rfl
    have eq : π.length - i - 1 = π.length - (i + 1 + 1) - 1 + 1 + 1 := by
      simp_all
      omega
    have P_turn : coalgebraGame.turn π[π.length - i - 1] = Prover := by
      convert P_turn_u₂
      convert Eq.symm u₂_def using 2
    have i_lt : i < π.length := by
      have lt' : i + 1 + 1 < π.length := by
        simpa using lt
      omega
    have helper_i : π.length - i - 1 < π.length := by omega
    simp only [←eq] at u₂_def
    have eq_helper : proverSplitSequent π[π.length - i - 1] P_turn = Γ' :=
      prover_SplitSequent_eq_of_inl u₂_def
    by_cases Sum.inl φ ∈ Γ'
    case pos φ_in =>
      exact builder_win_strong strat h ⟨π, ne, chain, max, head_cases, in_cone⟩ φ i i_lt
        helper_i P_turn (Or.inl (by simpa [eq_helper] using φ_in))
    case neg nφ_in =>
      cases R <;>
        simp only [RuleApp.splitSequents, Finset.notMem_empty, Finset.union_insert,
          Finset.union_singleton, Finset.mem_insert, Finset.mem_singleton] at Γ'_R
      case andₗ source A B source_mem =>
        have ⟨eq1, eq2⟩ : φ = (A & B) ∧ Γ = source := by
          have Γ_eq : Γ = source := by
            simpa [f] using (f_of_mem_ruleApps R_Γ).symm
          have φ_in_Γ : Sum.inl φ ∈ Γ := by
            simpa [proverSplitSequent] using φ_in
          have φ_eq : φ = (A & B) := by
            by_contra neφ
            apply nφ_in
            rcases Γ'_R with hΓ' | hΓ' <;> rw [hΓ']
            all_goals
              simp [←Γ_eq, φ_in_Γ, neφ]
          exact ⟨φ_eq, Γ_eq⟩
        subst eq1 eq2
        simp only [evaluate, not_and_or]
        rcases Γ'_R with eq | eq <;> subst eq
        · left
          apply builder_win_strong strat h
            ⟨π, ne, chain, max, head_cases, in_cone⟩ A i i_lt helper_i P_turn
          rw [eq_helper]
          left
          simp
        · right
          apply builder_win_strong strat h
            ⟨π, ne, chain, max, head_cases, in_cone⟩ B i i_lt helper_i P_turn
          rw [eq_helper]
          left
          simp
      case andᵣ source A B source_mem =>
        exfalso
        have Γ_eq : Γ = source := by
          simpa [f] using (f_of_mem_ruleApps R_Γ).symm
        have φ_in_Γ : Sum.inl φ ∈ Γ := by
          simpa [proverSplitSequent] using φ_in
        rcases Γ'_R with Γ'_R | Γ'_R <;> subst Γ'_R
        all_goals
          apply nφ_in
          simp [←Γ_eq, φ_in_Γ]
      case orₗ source A B source_mem =>
        have ⟨eq1, eq2⟩ : φ = (A v B) ∧ Γ = source := by
          have Γ_eq : Γ = source := by
            simpa [f] using (f_of_mem_ruleApps R_Γ).symm
          have φ_in_Γ : Sum.inl φ ∈ Γ := by
            simpa [proverSplitSequent] using φ_in
          have φ_eq : φ = (A v B) := by
            by_contra neφ
            apply nφ_in
            rw [Γ'_R]
            simp [←Γ_eq, φ_in_Γ, neφ]
          exact ⟨φ_eq, Γ_eq⟩
        subst eq1 eq2 Γ'_R
        simp only [evaluate, not_or]
        constructor
        · apply builder_win_strong strat h
            ⟨π, ne, chain, max, head_cases, in_cone⟩ A i i_lt helper_i P_turn
          rw [eq_helper]
          left
          simp
        · apply builder_win_strong strat h
            ⟨π, ne, chain, max, head_cases, in_cone⟩ B i i_lt helper_i P_turn
          rw [eq_helper]
          left
          simp
      case orᵣ source A B source_mem =>
        exfalso
        have Γ_eq : Γ = source := by
          simpa [f] using (f_of_mem_ruleApps R_Γ).symm
        have φ_in_Γ : Sum.inl φ ∈ Γ := by
          simpa [proverSplitSequent] using φ_in
        subst Γ'_R
        apply nφ_in
        simp [←Γ_eq, φ_in_Γ]
      case boxₗ source A source_mem =>
        exfalso
        apply no_box_u₁
        rw [←u₁_def]
        simp [isBox, RuleApp.isBox]
      case boxᵣ source A source_mem => --
        exfalso
        apply no_box_u₁
        rw [←u₁_def]
        simp [isBox, RuleApp.isBox]
termination_by (φ.length, i + 1, 3)
decreasing_by
  all_goals
    first
    | apply Prod.Lex.left; simp; done
    | apply Prod.Lex.left; rw [eq1]; simp [Formula.length]; omega
    | apply Prod.Lex.right; apply Prod.Lex.left; omega

/-- Right-side last-node case for `builder_win_strong`. -/
lemma builder_win_strong_right_zero {Δ : SplitSequent}
    (strat : Strategy coalgebraGame Builder) (h : winning strat (startPos Δ))
    (π : MaximalPath Δ strat) (φ) (i : ℕ) (h_i : i = 0) (lt : i < π.list.length)
    helper (ps)
    (noTerminal :
      ∀ R, R ∈ SplitSequent.ruleApps (lastSplitSequent h π) →
        R.splitSequents = ∅ → False)
    (noNonbox :
      ∀ R, R ∈ SplitSequent.ruleApps (lastSplitSequent h π) →
        ¬R.isBox → False) :
    Sum.inr φ ∈ proverSplitSequent ((π.list)[π.list.length - i - 1]'helper) ps →
    ¬ evaluate (gameBModel Δ h, π) φ := by
  subst i
  intro φ_in
  have φ_in' : Sum.inr φ ∈ lastSplitSequent h π := by
    convert φ_in
    simp [lastSplitSequent]
    congr
    grind
  cases φ
  case bottom => simp_all
  case top =>
    simp only [evaluate, not_true_eq_false]
    exact noTerminal
      (RuleApp.topᵣ (lastSplitSequent h π) φ_in')
      (ruleApp_topr_mem φ_in') (by simp [RuleApp.splitSequents])
  case atom n =>
    simp only [evaluate, gameBModel, SplitSequent.toSequent, Finset.mem_image, Sum.exists,
      Sum.elim_inl, id_eq, exists_eq_right, Sum.elim_inr, Decidable.not_not]
    exact Or.inr φ_in'
  case negAtom n =>
    simp only [evaluate, gameBModel, SplitSequent.toSequent, Finset.mem_image, Sum.exists,
      Sum.elim_inl, id_eq, exists_eq_right, Sum.elim_inr, not_or, not_and,
      Decidable.not_not, Classical.not_imp]
    constructor
    · intro nφ_in
      by_cases φ_in'' : Sum.inl (na n) ∈ lastSplitSequent h π
      · exact noTerminal
          (RuleApp.axₗₗ (lastSplitSequent h π) n ⟨nφ_in, φ_in''⟩)
          (ruleApp_axll_mem ⟨nφ_in, φ_in''⟩)
          (by simp [RuleApp.splitSequents])
      · exact noTerminal
          (RuleApp.axₗᵣ (lastSplitSequent h π) n ⟨nφ_in, φ_in'⟩)
          (ruleApp_axlr_mem ⟨nφ_in, φ_in'⟩ φ_in'')
          (by simp [RuleApp.splitSequents])
    · intro nφ_in
      by_cases φ_in'' : Sum.inl (na n) ∈ lastSplitSequent h π
      · exact noTerminal
          (RuleApp.axᵣₗ (lastSplitSequent h π) n ⟨nφ_in, φ_in''⟩)
          (ruleApp_axrl_mem ⟨nφ_in, φ_in''⟩)
          (by simp [RuleApp.splitSequents])
      · exact noTerminal
          (RuleApp.axᵣᵣ (lastSplitSequent h π) n ⟨nφ_in, φ_in'⟩)
          (ruleApp_axrr_mem ⟨nφ_in, φ_in'⟩ φ_in'')
          (by simp [RuleApp.splitSequents])
  case or φ1 φ2 => -- then we will make a move
    exfalso
    exact noNonbox
      (RuleApp.orᵣ (lastSplitSequent h π) φ1 φ2 φ_in')
      (ruleApp_orr_mem φ_in') (by simp [RuleApp.isBox])
  case and φ1 φ2  => -- then we will make a move
    exfalso
    exact noNonbox
      (RuleApp.andᵣ (lastSplitSequent h π) φ1 φ2 φ_in')
      (ruleApp_andr_mem φ_in') (by simp [RuleApp.isBox])
  case diamond φ =>
    simp only [evaluate, not_exists, not_and]
    intro ρ π_ρ
    exact builder_win_strong strat h ρ φ (ρ.list.length - 1)
      (maximal_path_last_reverse_index_lt ρ)
      (maximal_path_first_reverse_index_lt ρ)
      (maximal_path_first_reverse_index_turn ρ)
      (by
        have φ_in_2 :
            Sum.inl φ ∈ firstSplitSequent ρ ∨ Sum.inr φ ∈ firstSplitSequent ρ := by
          have hφ : φ ∈ (firstSplitSequent ρ).toSequent :=
            formula_in_path_of_diamond_formula_in h π_ρ φ
              (by simp [SplitSequent.toSequent, φ_in'])
          simpa [SplitSequent.toSequent] using hφ
        rcases φ_in_2 with hleft | hright
        · exact Or.inl (first_split_sequent_mem_at_reverse_index ρ hleft)
        · exact Or.inr (first_split_sequent_mem_at_reverse_index ρ hright))
  case box φ =>
    simp only [evaluate, not_forall]
    have ⟨ρ, ρ_def, first_mem⟩ := box_successor_path_of_last_right_box h π φ_in'
    refine ⟨ρ, ?_, ?_⟩
    · simpa [gameBModel] using ρ_def
    · exact builder_win_strong strat h ρ φ (ρ.list.length - 1)
        (maximal_path_last_reverse_index_lt ρ)
        (maximal_path_first_reverse_index_lt ρ)
        (maximal_path_first_reverse_index_turn ρ)
        (by
          rcases first_mem with hleft | hright
          · exact Or.inl (first_split_sequent_mem_at_reverse_index ρ hleft)
          · exact Or.inr (first_split_sequent_mem_at_reverse_index ρ hright))
termination_by (φ.length, i, 3)
decreasing_by
  all_goals
    apply Prod.Lex.left
    simp [Formula.length]

/-- Right-side successor case for `builder_win_strong`. -/
lemma builder_win_strong_right_succ {Δ : SplitSequent}
    (strat : Strategy coalgebraGame Builder) (h : winning strat (startPos Δ))
    (π : MaximalPath Δ strat) (φ) (j i : ℕ) (h_j : j = i + 1)
    (lt : j < π.list.length) helper (ps) :
    Sum.inr φ ∈ proverSplitSequent ((π.list)[π.list.length - j - 1]'helper) ps →
    ¬ evaluate (gameBModel Δ h, π) φ := by
  subst j
  intro φ_in
  match h_i : i with
  | 0 =>
    exfalso
    exact no_penultimate_prover_turn h π (by simpa using lt) helper ps
  | Nat.succ i =>
    rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
    have ne_zero : π.length ≠ 0 := by grind
    have length_gt_two : π.length > 2 := by
      simp at lt
      grind
    have eq3 : π.length - (i + 1 + 1) - 1 = π.length - i - 3 := by omega
    have eq2 : π.length - (i + 1 + 1) - 1 + 1 = π.length - i - 2 := by
      have lt' : i + 1 + 1 < π.length := by
        simpa using lt
      omega
    have y_u₁ := List.IsChain.getElem chain (π.length - (i + 1 + 1) - 1) (by omega)
    have raw_u₁_u₂ := List.IsChain.getElem chain (π.length - (i + 1 + 1) - 1 + 1) (by omega)
    have no_box_u₁ := y_u₁.2
    simp only [Nat.succ_eq_add_one] at φ_in
    rcases y_def : π[π.length - (i + 1 + 1) - 1] with ⟨Γ | R, Γs, Rs⟩ <;>
      simp [y_def] at ps
    simp only [y_def] at φ_in
    simp only [y_def] at y_u₁
    have y_u₁_mem := move_iff_in_moves.1 y_u₁.1
    unfold Game.Pos.moves Game.moves at y_u₁_mem
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at y_u₁_mem
    rcases y_u₁_mem with ⟨R, R_Γ, u₁_def⟩
    have move_u₁_u₂ :
        nonBoxMove (Sum.inr R, Γ :: Γs, Rs)
          (π[π.length - (i + 1 + 1) - 1 + 1 + 1]'(by grind)) := by
      convert raw_u₁_u₂ -- dont understand why simp or rw doesn't do this
    have u₁_u₂_mem := move_iff_in_moves.1 move_u₁_u₂.1
    unfold Game.Pos.moves Game.moves at u₁_u₂_mem
    simp only [List.mem_cons, Finset.mem_filterMap, Option.ite_none_left_eq_some, not_or,
      Option.some.injEq] at u₁_u₂_mem
    rcases u₁_u₂_mem with ⟨Γ', Γ'_R, no_rep, u₂_def⟩
    have P_turn_u₂ : coalgebraGame.turn (Sum.inl Γ', Γ :: Γs, R :: Rs) = Prover := by rfl
    have eq : π.length - i - 1 = π.length - (i + 1 + 1) - 1 + 1 + 1 := by
      simp_all
      omega
    have P_turn : coalgebraGame.turn π[π.length - i - 1] = Prover := by
      convert P_turn_u₂
      convert Eq.symm u₂_def using 2
    have i_lt : i < π.length := by
      have lt' : i + 1 + 1 < π.length := by
        simpa using lt
      omega
    have helper_i : π.length - i - 1 < π.length := by omega
    simp only [←eq] at u₂_def
    have eq_helper : proverSplitSequent π[π.length - i - 1] P_turn = Γ' :=
      prover_SplitSequent_eq_of_inl u₂_def
    by_cases Sum.inr φ ∈ Γ'
    case pos φ_in =>
      exact builder_win_strong strat h ⟨π, ne, chain, max, head_cases, in_cone⟩ φ i i_lt
        helper_i P_turn (Or.inr (by simpa [eq_helper] using φ_in))
    case neg nφ_in =>
      cases R <;>
        simp only [RuleApp.splitSequents, Finset.notMem_empty, Finset.union_insert,
          Finset.union_singleton, Finset.mem_insert, Finset.mem_singleton] at Γ'_R
      case andᵣ source A B source_mem =>
        have eq1 : φ = (A & B) := by
          have R_f := f_of_mem_ruleApps R_Γ
          simp [f] at R_f
          have φ_in_Γ : Sum.inr φ ∈ Γ := by
            simpa [proverSplitSequent] using φ_in
          by_contra neφ
          apply nφ_in
          rcases Γ'_R with hΓ' | hΓ' <;> rw [hΓ']
          all_goals
            simp [R_f, φ_in_Γ, neφ]
        subst eq1
        simp only [evaluate, not_and_or]
        rcases Γ'_R with eq | eq <;> subst eq
        · left
          apply builder_win_strong strat h
            ⟨π, ne, chain, max, head_cases, in_cone⟩ A i i_lt helper_i P_turn
          rw [eq_helper]
          right
          simp
        · right
          apply builder_win_strong strat h
            ⟨π, ne, chain, max, head_cases, in_cone⟩ B i i_lt helper_i P_turn
          rw [eq_helper]
          right
          simp
      case andₗ source A B source_mem =>
        exfalso
        have R_f := f_of_mem_ruleApps R_Γ
        simp [f] at R_f
        have φ_in_Γ : Sum.inr φ ∈ Γ := by
          simpa [proverSplitSequent] using φ_in
        rcases Γ'_R with Γ'_R | Γ'_R <;> subst Γ'_R
        all_goals
          apply nφ_in
          simp [R_f, φ_in_Γ]
      case orᵣ source A B source_mem =>
        have eq1 : φ = (A v B) := by
          have R_f := f_of_mem_ruleApps R_Γ
          simp [f] at R_f
          have φ_in_Γ : Sum.inr φ ∈ Γ := by
            simpa [proverSplitSequent] using φ_in
          by_contra neφ
          apply nφ_in
          rw [Γ'_R]
          simp [R_f, φ_in_Γ, neφ]
        subst eq1 Γ'_R
        simp only [evaluate, not_or]
        constructor
        · apply builder_win_strong strat h
            ⟨π, ne, chain, max, head_cases, in_cone⟩ A i i_lt helper_i P_turn
          rw [eq_helper]
          right
          simp
        · apply builder_win_strong strat h
            ⟨π, ne, chain, max, head_cases, in_cone⟩ B i i_lt helper_i P_turn
          rw [eq_helper]
          right
          simp
      case orₗ source A B source_mem =>
        exfalso
        have R_f := f_of_mem_ruleApps R_Γ
        simp [f] at R_f
        have φ_in_Γ : Sum.inr φ ∈ Γ := by
          simpa [proverSplitSequent] using φ_in
        subst Γ'_R
        apply nφ_in
        simp [R_f, φ_in_Γ]
      case boxₗ source A source_mem =>
        exfalso
        apply no_box_u₁
        rw [←u₁_def]
        simp [isBox, RuleApp.isBox]
      case boxᵣ source A source_mem =>
        exfalso
        apply no_box_u₁
        rw [←u₁_def]
        simp [isBox, RuleApp.isBox]
termination_by (φ.length, i + 1, 3)
decreasing_by
  all_goals
    first
    | apply Prod.Lex.left; simp; done
    | apply Prod.Lex.left; rw [eq1]; simp [Formula.length]; omega
    | apply Prod.Lex.right; apply Prod.Lex.left; omega

end

/-- If Builder wins, there exists a counter-model. -/
theorem _root_.Lean4GlCoalgebras.Split.builder_win_builds_model {Γ : SplitSequent}
    (strat : Strategy coalgebraGame Builder) (h : winning strat (startPos Γ)) :
    ¬ (⊨ Γ) := by
    simp only [SplitSequent.isValid, evaluateSSeq, Sum.exists, not_forall, not_or,
      not_exists, not_and]
    use MaximalPath Γ strat
    use gameBModel Γ h
    have ⟨π, π_head_eq⟩ :=
      always_exists_maximal_path_from_root_or_after Γ strat h (startPos Γ)
        inMyCone.nil (Or.inr rfl)
    use π
    constructor
    all_goals
      intro φ φ_in
      apply builder_win_strong strat h π φ (π.list.length - 1) ?_ ?_ ?_ ?_
      · rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
        simp
        grind
      · rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
        simp
        grind
      · rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
        have h : (π[π.length - (π.length - 1) - 1]'(by grind)) = π.head ne := by
          grind
        simp only [h]
        simp only [MaximalPath.first] at π_head_eq
        rw [π_head_eq]
        rfl
      · rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
        have h : (π[π.length - (π.length - 1) - 1]'(by grind)) = π.head ne := by
          grind
        simp only [h]
        simp only [MaximalPath.first] at π_head_eq
        simp [π_head_eq]
        simp [proverSplitSequent, φ_in]

/-- Completeness! Comes as a corrolary of `gamedet`, `prover_win_builds_proof`, and
    `builder_win_builds_model`. -/
theorem _root_.Lean4GlCoalgebras.Split.completeness
    (Γ : SplitSequent) : ⊨ Γ → SplitSequent.isTrue Γ := by
  intro Γ_sat
  rcases gamedet coalgebraGame (startPos Γ) with builder_wins | prover_wins
  · have ⟨strat, h⟩ := builder_wins
    have nΓ_sat := builder_win_builds_model strat h
    exfalso
    exact nΓ_sat Γ_sat
  · have ⟨strat, h⟩ := prover_wins
    exact prover_win_builds_proof strat h

/-- Corollary of `completeness`, used in Interpolants.lean. -/
lemma _root_.Lean4GlCoalgebras.Split.equiv_iff_sem_equiv
    {φ ψ : Formula} : semEquiv φ ψ ↔ (φ ≅ ψ) := by
  constructor
  · intro mp
    simp [semEquiv] at mp
    unfold equiv
    constructor
    · apply completeness
      simp_all [Formula.isValid, SplitSequent.isValid, evaluateSSeq]
    · apply completeness
      simp_all [Formula.isValid, SplitSequent.isValid, evaluateSSeq]
      grind
  · intro ⟨mpp1, mpp2⟩
    simp [semEquiv]
    simp [Formula.isValid]
    have := soundness {Sum.inl (~ψ), Sum.inr φ} mpp1
    have := soundness {Sum.inr (ψ), Sum.inl (~φ)} mpp2
    simp_all [SplitSequent.isValid, evaluateSSeq]
    grind

lemma _root_.Lean4GlCoalgebras.Split.single_preserves_equiv (n : Nat) (φ ψ χ : Formula)
    (equiv : φ ≅ ψ) :
    single n χ φ ≅ single n χ ψ :=
  equiv_iff_sem_equiv.1 <| @single_preserves_sem_equiv n χ φ ψ (equiv_iff_sem_equiv.2 equiv)

end Split
end Lean4GlCoalgebras
