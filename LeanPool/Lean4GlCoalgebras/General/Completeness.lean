/-
Copyright (c) 2026 Madeleine Gignoux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madeleine Gignoux
-/

import LeanPool.Lean4GlCoalgebras.General.Game
import LeanPool.Lean4GlCoalgebras.General.Soundness

/-! ## Prover winning the GL-game builds a GL-proof.

If Prover has a winning strategy in the game starting from `Γ`, then there is a proof of `Γ`,
proven in `prover_win_builds_proof`, all other definitions and proofs in this file are helpers. -/

namespace Lean4GlCoalgebras

private lemma unDi_mem_D_of_ne {Γ : Sequent} {φ χ : Formula}
    (h : ◇φ ∈ Γ) (hne : ◇φ ≠ χ) :
    φ ∈ (Γ \ {χ}).D := by
  rw [Sequent.D]
  apply Finset.mem_union.mpr
  right
  simp only [Finset.mem_filterMap]
  use ◇φ
  constructor
  · simp [h, hne]
  · simp [Formula.opUnDi]

/-- Rewinding the history one step to get previous move. -/
def rewindHistoryOneStep (g : coalgebraGame.Pos)
    (h : coalgebraGame.turn g = Prover ∧ g.2.2 ≠ ∅ ∨
      coalgebraGame.turn g = Builder ∧ g.2.1 ≠ ∅) :
    coalgebraGame.Pos :=
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
  (h : coalgebraGame.turn g = Prover ∧ g.2.2 ≠ ∅ ∨
    coalgebraGame.turn g = Builder ∧ g.2.1 ≠ ∅)
  (strat : Strategy coalgebraGame Prover) (in_cone : inMyCone strat (startPos Γ) g)
  : inMyCone strat (startPos Γ) (rewindHistoryOneStep g h) := by
  cases in_cone
  case nil =>
    rcases h with ⟨_, hne⟩ | ⟨hturn, _⟩
    · exact False.elim (hne rfl)
    · cases hturn
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
  (n : Fin ((if coalgebraGame.turn g = Prover then min (2 * g.2.1.length + 1) (2 * g.2.2.length)
             else min (2 * g.2.1.length) (2 * g.2.2.length + 1)) + 1)) : coalgebraGame.Pos :=
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
          change n.1 < min (2 * ([] : List Sequent).length) (2 * Rs.length + 1) + 1 at n_lt
          simp only [List.length_nil, mul_zero] at n_lt
          omega)) ⟨m, by
            have ⟨n_val, n_prop⟩ := n
            simp_all only [Nat.lt_add_one_iff, ge_iff_le]
            rcases g with ⟨Γ | R, Γs, Rs⟩ <;> simp_all only [rewindHistoryOneStep,
              reduceCtorEq, ↓reduceIte, List.length_tail, le_inf_iff]
            · have hm : n_val = m + 1 := by simpa using n_def
              change n_val < min (2 * Γs.length + 1) (2 * Rs.length) + 1 at n_prop
              constructor <;> omega
            · have hm : n_val = m + 1 := by simpa using n_def
              change n_val < min (2 * Γs.length) (2 * Rs.length + 1) + 1 at n_prop
              change m ≤ min (2 * (Γs.length - 1) + 1) (2 * Rs.length)
              omega⟩
termination_by n.1
decreasing_by
  omega

/-- Rewinding the history `n` steps is still in the cone of the game. -/
lemma rewind_history_in_cone {Γ} (g : coalgebraGame.Pos)
  (n : Fin ((if coalgebraGame.turn g = Prover then min (2 * g.2.1.length + 1) (2 * g.2.2.length)
             else min (2 * g.2.1.length) (2 * g.2.2.length + 1)) + 1))
  (strat : Strategy coalgebraGame Prover) (in_cone : inMyCone strat (startPos Γ) g) :
    inMyCone strat (startPos Γ) (rewindHistory g n) := by
  unfold rewindHistory
  split
  · exact in_cone
  · apply rewind_history_in_cone
    apply rewind_history_one_step_in_cone
    exact in_cone

@[simp] lemma rewind_history_zero (g : coalgebraGame.Pos) : rewindHistory g 0 = g := by
  simp [rewindHistory]

/-- This is the type of the coalgebra we will use to build the proof of `Γ`. -/
def proof_type (Γ : Sequent) (strat : Strategy coalgebraGame Prover) :=
 {g // inMyCone strat (startPos Γ) g ∧ coalgebraGame.turn g = Builder}

/-- Auxiliary declaration used in the GL coalgebra development. -/
def builderRuleApp (g : coalgebraGame.Pos) (h : coalgebraGame.turn g = Builder) : RuleApp :=
  match g with
  | ⟨Sum.inr R, _, _⟩ => R
  | ⟨Sum.inl _, _, _⟩ => False.elim (by
    change Prover = Builder at h
    cases h)

/-- Defines the premise when we do not have a repeat. -/
def nextNext {Γ Δ : Sequent} {strat : Strategy coalgebraGame Prover} (g : proof_type Γ strat)
  (h : winning strat (startPos Γ)) (nrep : Δ ∉ g.1.2.1)
  (pos : Δ ∈ (builderRuleApp g.1 g.2.2).sequents) : proof_type Γ strat :=
  let next : GamePos := ⟨Sum.inl <| Δ, g.1.2.1, builderRuleApp g.1 g.2.2 :: g.1.2.2⟩
  have P_next : coalgebraGame.turn next = Prover := by unfold Game.turn next; simp
  have next_in_moves : next ∈ coalgebraGame.moves g.1 := by
    rcases g with ⟨⟨Γ | R, Γs, Rs⟩, _, b_move⟩
    · change Prover = Builder at b_move
      cases b_move
    · unfold next
      change Δ ∉ Γs at nrep
      change Δ ∈ R.sequents at pos
      dsimp [coalgebraGame]
      exact (Finset.mem_filterMap _).mpr ⟨Δ, pos, by simp [nrep]; rfl⟩
  have still_winning_next : winning strat next := by
    have g_winning := winning_of_in_cone_winning g.2.1 h
    exact @winning_of_whatever_other_move Prover coalgebraGame strat g.1 g.2.2
      g_winning ⟨next, next_in_moves⟩
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
  have next_next_in_cone : inMyCone strat (Sum.inl Γ, [], []) nextNext := by
    have := @inMyCone.oStep _ _ strat _ _ _ g.2.1 g.2.2 next_in_moves
    exact inMyCone.myStep this P_has_moves_next P_next
  ⟨nextNext, next_next_in_cone, B_next_next⟩

/-- The sequent at the premise defined by `nextNext` is the sequent `Δ` which we expect. -/
lemma next_next_cor {Γ Δ : Sequent} {strat : Strategy coalgebraGame Prover}
    (g : proof_type Γ strat)
  (h : winning strat (startPos Γ)) (nrep : Δ ∉ g.1.2.1)
  (pos : Δ ∈ (builderRuleApp g.1 g.2.2).sequents) :
  f (builderRuleApp (nextNext g h nrep pos).1 (nextNext g h nrep pos).2.2) = Δ := by
  let next : GamePos := ⟨Sum.inl <| Δ, g.1.2.1, builderRuleApp g.1 g.2.2 :: g.1.2.2⟩
  have P_next : coalgebraGame.turn next = Prover := by unfold Game.turn next; simp
  have next_in_moves : next ∈ coalgebraGame.moves g.1 := by
    rcases g with ⟨⟨Γ | R, Γs, Rs⟩, _, b_move⟩
    · change Prover = Builder at b_move
      cases b_move
    · unfold next
      change Δ ∉ Γs at nrep
      change Δ ∈ R.sequents at pos
      dsimp [coalgebraGame]
      exact (Finset.mem_filterMap _).mpr ⟨Δ, pos, by simp [nrep]; rfl⟩
  have still_winning_next : winning strat next := by
    have g_winning := winning_of_in_cone_winning g.2.1 h
    exact @winning_of_whatever_other_move Prover coalgebraGame strat g.1 g.2.2
      g_winning ⟨next, next_in_moves⟩
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
  have next_next_in_cone : inMyCone strat (Sum.inl Γ, [], []) next_next' := by
    have := @inMyCone.oStep _ _ strat _ _ _ g.2.1 g.2.2 next_in_moves
    exact inMyCone.myStep this P_has_moves_next P_next
  have h : next_next'.1 = (nextNext g h nrep pos).1 := by grind [nextNext]
  simp only [← h]
  have next_next_in_moves := next_next'.2
  unfold next Game.Pos.moves Game.moves coalgebraGame at next_next_in_moves
  simp only [Finset.mem_map] at next_next_in_moves
  have ⟨R, R_prop, R_eq⟩ := next_next_in_moves
  dsimp at R_eq
  simp only [← R_eq]
  simp only [builderRuleApp]
  simp only [Sequent.ruleApps, Finset.mem_filterMap, Option.dite_none_right_eq_some,
    and_exists_self] at R_prop
  have ⟨φ, φ_in, φ_prop⟩ := R_prop
  cases φ <;> simp only [reduceCtorEq, Option.some.injEq,
    Option.dite_none_right_eq_some] at φ_prop
  case atom =>
    have ⟨_, φ_prop⟩ := φ_prop
    subst φ_prop
    simp [f]
  all_goals
    subst φ_prop
    simp [f]

/-- Comparison of rule app history length and sequent history length. -/
lemma history_length_in_cone {Γ : Sequent} (strat : Strategy coalgebraGame Prover)
  (g : coalgebraGame.Pos)
  (in_cone : inMyCone strat (startPos Γ) g) :
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
def repPos {Γ Δ : Sequent} {strat : Strategy coalgebraGame Prover} (g : proof_type Γ strat)
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
    if Even n.1 then coalgebraGame.turn (rewindHistory g n) = coalgebraGame.turn g
    else coalgebraGame.turn (rewindHistory g n) = other (coalgebraGame.turn g) := by
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
lemma f_of_mem_ruleApps {Γ : Sequent} {R : RuleApp} (h : R ∈ Γ.ruleApps) : f R = Γ := by
  simp only [Sequent.ruleApps, Finset.mem_filterMap, Option.dite_none_right_eq_some,
    and_exists_self] at h
  rcases h with ⟨φ, φ_in, hR⟩
  cases φ <;> simp only [reduceCtorEq, Option.some.injEq,
    Option.dite_none_right_eq_some] at hR
  case atom =>
    rcases hR with ⟨_, hR⟩
    subst hR
    simp [f]
  all_goals
    subst hR
    simp [f]

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
        simp only [← hR, Function.Embedding.coeFn_mk] at g_in_moves_q ⊢
        rcases (Finset.mem_filterMap _).mp g_in_moves_q with ⟨Δ', _, hΔ'⟩
        by_cases hmem : Δ' ∈ Δ0 :: Δs
        · simp only [hmem, ↓reduceIte, reduceCtorEq] at hΔ'
        · simp only [hmem, ↓reduceIte, Option.some.injEq] at hΔ'
          cases hΔ'
          simp only [List.getElem_cons_zero]
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
      simp only [← hR, Function.Embedding.coeFn_mk]
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
lemma rewind_history_correspondence_aux (Γ) (info : Sequent ⊕ RuleApp)
  (Γs : List Sequent) (Rs : List RuleApp) (strat : Strategy coalgebraGame Prover)
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
def repNext (Γ : Sequent) {Δ : Sequent} {strat : Strategy coalgebraGame Prover}
  (g : proof_type Γ strat) (rep : Δ ∈ g.1.2.1) : (proof_type Γ strat) :=
  ⟨repPos g rep,
   rewind_history_in_cone g.1 ⟨(2 * (Fin.find _ (List.mem_iff_get.1 rep)).1), _⟩ strat g.2.1,
    by
      have hbound :
          2 * (Fin.find _ (List.mem_iff_get.1 rep)).1 <
            (if coalgebraGame.turn g.1 = Prover then
              min (2 * g.1.2.1.length + 1) (2 * g.1.2.2.length)
            else
              min (2 * g.1.2.1.length) (2 * g.1.2.2.length + 1)) + 1 := by
        have length := history_length_in_cone strat g.1 g.2.1
        have hlen := length.2 g.2.2
        have hfind := (Fin.find _ (List.mem_iff_get.1 rep)).2
        simp only [g.2.2, reduceCtorEq, if_false]
        omega
      have turn := @rewind_turn g.1 ⟨(2 * (Fin.find _ (List.mem_iff_get.1 rep)).1), hbound⟩
      simp only [g.2.2, Nat.even_mul, even_two, true_or, if_true] at turn
      convert turn⟩

/-- The sequent at the premise defined by `repNext` is the sequent `Δ` which we expect. -/
lemma rep_next_cor (Γ : Sequent) {Δ : Sequent} {strat : Strategy coalgebraGame Prover}
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
    simp only [g.2.2, reduceCtorEq, if_false] at *
    have := Fin.find_spec (List.mem_iff_get.1 rep)
    grind
  · have length := history_length_in_cone strat g.1 g.2.1
    simp only [g.2.2, reduceCtorEq, if_false, gt_iff_lt] at *
    have := Fin.find_spec (List.mem_iff_get.1 rep)
    grind

/-- Define the list of premises from a Builder move. -/
def builderMovePremises {Γ : Sequent} {strat : Strategy coalgebraGame Prover}
    (g : proof_type Γ strat) (h : winning strat (startPos Γ)) :
    List (proof_type Γ strat) := match g_def : g with
  | ⟨⟨Sum.inl _, _, _⟩, x, y⟩ => False.elim (by unfold Game.turn at y; simp at y)
  | ⟨⟨Sum.inr R, Γs, Rs⟩, _⟩ =>
    match R with
      | RuleApp.top _ _ => []
      | RuleApp.ax _ _ _ => []
      | RuleApp.or Δ φ1 φ2 φ_in =>
        if rep : (Δ \ {φ1 v φ2}) ∪ {φ1, φ2} ∈ Γs
          then [repNext Γ g (by convert rep; grind)]
              else
                [nextNext g h (by convert rep; grind)
                  (by subst g_def; simp [RuleApp.sequents, builderRuleApp])]
      | RuleApp.and Δ φ1 φ2 φ_in =>
        if rep1 : (Δ \ {φ1 & φ2}) ∪ {φ1} ∈ Γs
          then
            if rep2 : (Δ \ {φ1 & φ2}) ∪ {φ2} ∈ Γs
              then
                [repNext Γ g (by convert rep1; grind),
                  repNext Γ g (by convert rep2; grind)]
              else
                [repNext Γ g (by convert rep1; grind),
                  nextNext g h (by convert rep2; grind)
                    (by subst g_def; simp [RuleApp.sequents, builderRuleApp])]
          else
            if rep2 : (Δ \ {φ1 & φ2}) ∪ {φ2} ∈ Γs
              then
                [nextNext g h (by convert rep1; grind)
                    (by subst g_def; simp [RuleApp.sequents, builderRuleApp]),
                  repNext Γ g (by convert rep2; grind)]
              else
                [nextNext g h (by convert rep1; grind)
                    (by subst g_def; simp [RuleApp.sequents, builderRuleApp]),
                  nextNext g h (by convert rep2; grind)
                    (by subst g_def; simp [RuleApp.sequents, builderRuleApp])]
      | RuleApp.box Δ φ φ_in =>
        if rep : (Δ \ {□φ}).D ∪ {φ} ∈ Γs
          then [repNext Γ g (by convert rep; grind)]
          else
            [nextNext g h (by convert rep; grind)
              (by subst g_def; simp [RuleApp.sequents, builderRuleApp])]

/-- If Prover has a winning strategy in the game starting from `Γ`, then there is a proof
of `Γ! -/
theorem prover_win_builds_proof {Γ : Sequent} (strat : Strategy coalgebraGame Prover)
    (h : winning strat (startPos Γ)) : ⊢ Γ := by
  use {
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
        · simp only [p, builderMovePremises]
        · simp only [p, builderMovePremises]
        case and Δ φ1 φ2 φ_in =>
          simp only [p, builderMovePremises, List.map_eq_cons_iff, ↓existsAndEq,
            List.map_eq_nil_iff, true_and, and_true]
          by_cases Δ \ {φ1 & φ2} ∪ {φ1} ∈ Γs
          case pos rep1 =>
            by_cases Δ \ {φ1 & φ2} ∪ {φ2} ∈ Γs
            case pos rep2 =>
              simp only [rep1, rep2, ↓reduceDIte, List.cons.injEq, and_true,
                ↓existsAndEq, true_and, repNext, fₙ_alternate]
              constructor
              · exact rep_next_cor Γ
                  ⟨⟨Sum.inr (RuleApp.and Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩
                  (by simp only [rep1])
              · exact rep_next_cor Γ
                  ⟨⟨Sum.inr (RuleApp.and Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩
                  (by simp only [rep2])
            case neg nrep2 =>
              simp only [rep1, nrep2, ↓reduceDIte, List.cons.injEq, and_true,
                ↓existsAndEq, true_and, repNext, fₙ_alternate]
              constructor
              · exact rep_next_cor Γ
                  ⟨⟨Sum.inr (RuleApp.and Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩
                  (by simp only [rep1])
              · exact next_next_cor
                  ⟨⟨Sum.inr (RuleApp.and Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h
                  nrep2
                  (by simp [RuleApp.sequents, builderRuleApp])
          case neg nrep1 =>
            by_cases Δ \ {φ1 & φ2} ∪ {φ2} ∈ Γs
            case pos rep2 =>
              simp only [nrep1, rep2, ↓reduceDIte, List.cons.injEq, and_true,
                ↓existsAndEq, true_and, repNext, fₙ_alternate]
              constructor
              · exact next_next_cor
                  ⟨⟨Sum.inr (RuleApp.and Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h
                  nrep1
                  (by simp [RuleApp.sequents, builderRuleApp])
              · exact rep_next_cor Γ
                  ⟨⟨Sum.inr (RuleApp.and Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩
                  (by simp only [rep2])
            case neg nrep2 =>
              simp only [nrep1, nrep2, ↓reduceDIte, List.cons.injEq, and_true,
                ↓existsAndEq, true_and, fₙ_alternate]
              constructor
              · exact next_next_cor
                  ⟨⟨Sum.inr (RuleApp.and Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h
                  nrep1
                  (by simp [RuleApp.sequents, builderRuleApp])
              · exact next_next_cor
                  ⟨⟨Sum.inr (RuleApp.and Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h
                  nrep2
                  (by simp [RuleApp.sequents, builderRuleApp])
        case or Δ φ1 φ2 φ_in =>
          simp only [p, builderMovePremises, List.map_eq_singleton_iff]
          by_cases Δ \ {φ1 v φ2} ∪ {φ1, φ2} ∈ Γs
          case pos rep =>
            simp only [rep, ↓reduceDIte, List.cons.injEq, and_true, exists_eq_left']
            simp only [repNext]
            exact rep_next_cor Γ
              ⟨⟨Sum.inr (RuleApp.or Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩
              (by simp only [rep])
          case neg nrep =>
            simp only [nrep, ↓reduceDIte, List.cons.injEq, and_true, exists_eq_left']
            simp only [nextNext, fₙ_alternate]
            exact next_next_cor
              ⟨⟨Sum.inr (RuleApp.or Δ φ1 φ2 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h
              nrep
              (by simp [RuleApp.sequents, builderRuleApp])
        case box Δ φ1 φ_in =>
          simp only [p, builderMovePremises, List.map_eq_singleton_iff]
          by_cases (Δ \ {□φ1}).D ∪ {φ1} ∈ Γs
          case pos rep =>
            simp only [rep, ↓reduceDIte, List.cons.injEq, and_true, exists_eq_left']
            simp only [repNext]
            exact rep_next_cor Γ
              ⟨⟨Sum.inr (RuleApp.box Δ φ1 φ_in), Γs, Rs⟩, in_cone, b_move⟩
              (by simp only [rep])
          case neg nrep =>
            simp only [nrep, ↓reduceDIte, List.cons.injEq, and_true, exists_eq_left']
            simp only [nextNext, fₙ_alternate]
            exact next_next_cor
              ⟨⟨Sum.inr (RuleApp.box Δ φ1 φ_in), Γs, Rs⟩, in_cone, b_move⟩ h
              nrep
              (by simp [RuleApp.sequents, builderRuleApp])}
  have turn_P : coalgebraGame.turn (startPos Γ) = Prover := rfl
  let next_move := strat (startPos Γ) turn_P (winning_has_moves turn_P h)
  have turn_next_move_B : coalgebraGame.turn next_move.1 = Builder := by
    have next_move_in_moves := next_move.2
    unfold Game.Pos.moves Game.moves at next_move_in_moves
    dsimp [coalgebraGame] at next_move_in_moves
    rcases (Finset.mem_map).mp next_move_in_moves with ⟨R, _, hR⟩
    rw [← hR]
    rfl
  have next_in_cone : inMyCone strat (Sum.inl Γ, [], []) next_move.1 := by
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
    simp only [r, builderRuleApp]
    have hR_eq : R' = R := by
      injection hR with hinfo _hhistories
      exact Sum.inr.inj hinfo
    exact f_of_mem_ruleApps (by simpa [hR_eq] using in_rule)


/-! ## Builder winning the GL-game builds a GL-countermodel.

If Builder has a winning strategy in the game starting from `Γ`, then there is a proof of `Γ`,
proven in `builder_win_builds_model`, all other definitions and proofs in this file are helpers. -/

/-! # Maximal Paths. -/

/-- Predicate on moves in the game necessary for quantifying maximal paths. -/
def afterBox (g : coalgebraGame.Pos) : Prop := match g with
  | ⟨Sum.inl _, _, R :: _⟩ => R.isBox
  | _ => false

/-- Predicate on moves in the game necessary for quantifying maximal paths. -/
def isBox (g : coalgebraGame.Pos) : Prop := match g with
  | ⟨Sum.inr R, _, _⟩ => R.isBox
  | _ => false

/-- Relation on moves in the game necessary for quantifying maximal paths. -/
def nonBoxMove : coalgebraGame.Pos → coalgebraGame.Pos → Prop :=
  fun x y ↦ Move x y ∧ ¬ isBox y

/-- The type of a maximal path in the game. -/
structure MaximalPath (Γ : Sequent) (strat : Strategy coalgebraGame Builder) where
  /-- Auxiliary declaration used in the GL coalgebra development. -/
  list : List coalgebraGame.Pos
  ne : list ≠ []
  chain : List.IsChain nonBoxMove list
  max : ¬ ∃ z, nonBoxMove (list.getLast ne) z
  head_cases : afterBox (list.head ne) ∨ list.head ne = (startPos Γ)
  in_cone : ∀ x ∈ list, inMyCone strat (startPos Γ) x

/-- Auxiliary declaration used in the GL coalgebra development. -/
@[simp]
def MaximalPath.last {Γ : Sequent} {strat : Strategy coalgebraGame Builder} :
    MaximalPath Γ strat → coalgebraGame.Pos :=
  fun π => π.list.getLast π.ne

/-- Auxiliary declaration used in the GL coalgebra development. -/
@[simp]
def MaximalPath.first {Γ : Sequent} {strat : Strategy coalgebraGame Builder} :
    MaximalPath Γ strat → coalgebraGame.Pos :=
  fun π => π.list.head π.ne

/-- Maximal paths always start from a move which is Prover's turn. -/
lemma maximal_path_starts_in_prover_turn {Γ : Sequent} {strat : Strategy coalgebraGame Builder}
  (π : MaximalPath Γ strat) :
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

/-- Maximal paths always end in a move which is Prover's turn. -/
lemma maximal_path_ends_in_prover_turn {Γ : Sequent} {strat : Strategy coalgebraGame Builder}
  (h : winning strat (startPos Γ)) (π : MaximalPath Γ strat) :
  coalgebraGame.turn π.last = Prover := by
  match last_def : π.last with
  | ⟨Sum.inl Γ, Γs, Rs⟩ => rfl
  | ⟨Sum.inr R, Γs, Rs⟩ =>
    exfalso
    rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
    apply max
    have is_winning : winning strat ⟨Sum.inr R, Γs, Rs⟩ := winning_of_in_cone_winning (by
      change π.getLast ne = (Sum.inr R, Γs, Rs) at last_def
      rw [←last_def]
      apply in_cone
      simp) h
    have B_turn : coalgebraGame.turn ⟨Sum.inr R, Γs, Rs⟩ = Builder := by rfl
    have has_moves := winning_has_moves B_turn is_winning
    let z := strat ⟨Sum.inr R, Γs, Rs⟩ B_turn has_moves
    refine ⟨z.1, ?_, ?_⟩
    · apply move_iff_in_moves.2
      change π.getLast ne = (Sum.inr R, Γs, Rs) at last_def
      rw [last_def]
      exact z.2
    · have ⟨z, z_in⟩ := z
      unfold Game.Pos.moves Game.moves at z_in
      rcases (by simpa [-SetLike.coe_mem] using z_in) with
        ⟨Γ, _Γ_R, _Γ_not_mem, z_eq⟩
      cases z_eq
      simp [isBox]


open Classical in
/-- If Builder is winning, there is always a maximal path. -/
noncomputable def makePathFrom (strat : Strategy coalgebraGame Builder)
    (g : coalgebraGame.Pos) : List coalgebraGame.Pos :=
  match g_def : g with
  | ⟨Sum.inl Γ, Γs, Rs⟩ => if exists_non_box_move : ∃ g', nonBoxMove g g'
    then ⟨Sum.inl Γ, Γs, Rs⟩ :: makePathFrom strat exists_non_box_move.choose
    else [⟨Sum.inl Γ, Γs, Rs⟩]
  | ⟨Sum.inr R, Γs, Rs⟩ => if exists_non_box_move : ∃ g', nonBoxMove g g'
    then ⟨Sum.inr R, Γs, Rs⟩ :: makePathFrom strat (strat ⟨Sum.inr R, Γs, Rs⟩
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

/-- If Builder is winning, the List from `makePathFrom` is nonempty. -/
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

/-- If Builder is winning, the List from `makePathFrom` is a chain. -/
lemma make_path_from_is_chain (strat : Strategy coalgebraGame Builder) (g : coalgebraGame.Pos)
  : List.IsChain nonBoxMove (makePathFrom strat g) :=
  open Classical in
  match g_def : g with
  | ⟨Sum.inl Γ, Γs, Rs⟩ => if exists_non_box_move : ∃ g', nonBoxMove g g'
    then by
      subst g_def
      simp only [makePathFrom, exists_non_box_move, ↓reduceDIte]
      apply List.IsChain.cons
      · apply make_path_from_is_chain strat
      · simp only [Option.mem_def]
        intro g g_in
        have := make_path_from_head? strat (exists_non_box_move.choose)
        have hsome : some exists_non_box_move.choose = some g := by
          rw [← this]
          exact g_in
        injection hsome with h
        subst h
        exact exists_non_box_move.choose_spec
    else by simp_all [makePathFrom]
  | ⟨Sum.inr R, Γs, Rs⟩ => if exists_non_box_move : ∃ g', nonBoxMove g g'
    then by
      subst g_def
      simp only [makePathFrom, exists_non_box_move, ↓reduceDIte]
      apply List.IsChain.cons
      · apply make_path_from_is_chain strat
      · simp only [Option.mem_def]
        intro g g_in
        have in_moves := (strat (Sum.inr R, Γs, Rs) (by rfl)
          ⟨exists_non_box_move.choose,
            move_iff_in_moves.1 exists_non_box_move.choose_spec.1⟩).2
        have := make_path_from_head? strat (strat (Sum.inr R, Γs, Rs) (by rfl)
          ⟨exists_non_box_move.choose,
            move_iff_in_moves.1 exists_non_box_move.choose_spec.1⟩)
        have hsome := Eq.trans this.symm g_in
        injection hsome with h
        rw [← h]
        constructor
        · exact move_iff_in_moves.2 in_moves
        · simp only [Game.Pos.moves] at in_moves
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

/-- If Builder is winning, the List from `makePathFrom` is maximal. -/
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
      convert make_path_is_max strat
        ((strat ⟨Sum.inr R, Γs, Rs⟩ (by rfl)
          ⟨exists_non_box_move.choose,
            move_iff_in_moves.1 (g_def ▸ exists_non_box_move.choose_spec.1)⟩)) using 4
      simp [List.getLast_cons (make_path_from_is_nonempty strat
        ((strat ⟨Sum.inr R, Γs, Rs⟩ (by rfl)
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

/-- If Builder is winning, every move in the list from `makePathFrom` is in the cone. -/
lemma make_path_is_in_cone (Δ : Sequent) (strat : Strategy coalgebraGame Builder)
    (g : coalgebraGame.Pos) (in_cone : inMyCone strat (Sum.inl Δ, [], []) g)
    (h : winning strat ⟨Sum.inl Δ, [], []⟩) :
    ∀ i, inMyCone strat (Sum.inl Δ, [], []) ((makePathFrom strat g).get i) := by
  intro ⟨i_val, i_prop⟩
  cases i_val
  case zero =>
    convert in_cone using 1
    have := make_path_from_head strat g
    grind
  case succ i =>
    rcases g with ⟨Γ | R, Γs, Rs⟩
    · by_cases exists_non_box_move : ∃ g', nonBoxMove ⟨Sum.inl Γ, Γs, Rs⟩ g'
      · simp_all only [List.get_eq_getElem, makePathFrom, ↓reduceDIte, List.getElem_cons_succ]
        simp [makePathFrom] at i_prop
        apply make_path_is_in_cone Δ strat exists_non_box_move.choose ?_ h ⟨i, by grind⟩
        exact inMyCone.oStep in_cone (by rfl)
          (move_iff_in_moves.1 exists_non_box_move.choose_spec.1)
      · simp [makePathFrom, exists_non_box_move] at i_prop
    · by_cases exists_non_box_move : ∃ g', nonBoxMove ⟨Sum.inr R, Γs, Rs⟩ g'
      · simp_all only [List.get_eq_getElem, makePathFrom, ↓reduceDIte, List.getElem_cons_succ]
        simp only [makePathFrom, exists_non_box_move, ↓reduceDIte, List.length_cons,
          Nat.lt_add_one_iff, Nat.add_one_le_iff] at i_prop
        apply make_path_is_in_cone Δ strat _ ?_ h ⟨i, i_prop⟩
        apply inMyCone.myStep in_cone
      · simp [makePathFrom, exists_non_box_move] at i_prop

/-- If Builder is winning, the starting move or any move after a box move has a maximal path. -/
lemma always_exists_maximal_path_from_root_or_after (Γ : Sequent)
    (strat : Strategy coalgebraGame Builder) (h : winning strat (startPos Γ))
    (g : coalgebraGame.Pos) (in_cone : inMyCone strat (startPos Γ) g)
    (head_cases : afterBox g ∨ g = (startPos Γ)) :
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

/-- Given a prover move, find the underlying sequent. -/
def proverSequent (g : coalgebraGame.Pos) (h : coalgebraGame.turn g = Prover) := match g with
  | ⟨Sum.inl Γ, Γs, Rs⟩ => Γ
  | ⟨Sum.inr R, Γ :: Γs, Rs⟩ => False.elim (by
    change Builder = Prover at h
    cases h)

/-- Auxiliary declaration used in the GL coalgebra development. -/
def firstSequent {Γ : Sequent} {strat : Strategy coalgebraGame Builder} :
  MaximalPath Γ strat → Sequent :=
  fun π ↦ proverSequent π.first (maximal_path_starts_in_prover_turn π)

lemma first_sequent_eq_of_first
    {Γ : Sequent} {strat : Strategy coalgebraGame Builder}
    (π : MaximalPath Γ strat) {Δ Δs Rs}
    (hfirst : π.first = (Sum.inl Δ, Δs, Rs)) :
    firstSequent π = Δ := by
  rcases π with ⟨list, ne, chain, max, head_cases, in_cone⟩
  unfold MaximalPath.first at hfirst
  unfold firstSequent
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
def lastSequent {Γ : Sequent} {strat : Strategy coalgebraGame Builder}
    (h : winning strat (startPos Γ)) :
    MaximalPath Γ strat → Sequent :=
  fun π ↦ proverSequent π.last (maximal_path_ends_in_prover_turn h π)

/-- Two maximal paths are related if two steps in the game can connect tail to head. -/
def pathRelation (Γ : Sequent) (strat : Strategy coalgebraGame Builder)
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

lemma maximal_path_refl_trans_gen (as) (ne : as ≠ []) (chain : List.IsChain nonBoxMove as) :
  Relation.ReflTransGen Move (as.head ne) (as.getLast ne) := by
  induction chain
  case nil => simp at ne
  case singleton g =>
    simp only [List.head_cons, List.getLast_singleton]
    exact Relation.ReflTransGen.refl
  case cons_cons g g' gs g_g' gs_chain ih =>
  exact Relation.ReflTransGen.head g_g'.1 (ih (by simp))

/-- The definition of the GL-model `(M,R,V)` we will use as the countermodel. `M, R, V` are all
    defined as expected (except `R` is transtive), transitivity is immediate, and converse
    well-foundedness follow from well-foundedness of the game. -/
def gameBModel (Γ : Sequent) {strat : Strategy coalgebraGame Builder}
    (h : winning strat (startPos Γ)) : Model (MaximalPath Γ strat) where
  V π n := at n ∉ lastSequent h π
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
          (Relation.TransGen (Function.swap Move)) := by exact {
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
    apply @RelHomClass.wellFounded _ _ (Function.swap (pathRelation Γ strat))
      (Relation.TransGen (Function.swap Move)) Unit instFunLike instRelHome ()
      (WellFounded.transGen coalgebraGame.wf.2)
-- using RelHomClass.wellFounded feels like overkill, but it works.

lemma move_from_last_implies_box {Γ : Sequent} {strat : Strategy coalgebraGame Builder}
    (π : MaximalPath Γ strat) :
    ∀ x, Move π.last x → isBox x := by
  intro x π_x
  by_contra h
  rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
  apply max
  refine ⟨x, ⟨π_x, h⟩⟩

/-- Helper for `◇` case of `builder_win_strong`. -/
lemma diamond_in_of_move_move_diamond_in {x z} (hx hz)
    (x_z : (Relation.Comp Move Move) x z) :
    ∀ φ, ◇ φ ∈ proverSequent x hx → ◇ φ ∈ proverSequent z hz := by
  simp only [Relation.Comp] at x_z
  have ⟨y, x_y, y_z⟩ := x_z
  rcases x with ⟨Γ | R, Γs, Rs⟩ <;> try (change Builder = Prover at hx; cases hx)
  rcases x_y
  case prover R R_Γ =>
  rcases y_z
  case builder Γ' Γ'_R nrep =>
  simp only [proverSequent]
  intro φ φ_in
  simp only [Sequent.ruleApps, Finset.mem_filterMap, Option.dite_none_right_eq_some,
    and_exists_self] at R_Γ
  have ⟨ψ, ψ_in, eq⟩ := R_Γ
  cases ψ
  case bottom =>
    simp only [reduceCtorEq] at eq
  case top =>
    simp only [Option.some.injEq] at eq
    subst eq
    simp only [RuleApp.sequents, Finset.notMem_empty] at Γ'_R
  case atom =>
    simp only [Option.dite_none_right_eq_some] at eq
    have ⟨nψ_in, eq⟩ := eq
    simp only [Option.some.injEq] at eq
    subst eq
    simp only [RuleApp.sequents, Finset.notMem_empty] at Γ'_R
  case negAtom =>
    simp only [reduceCtorEq] at eq
  case and =>
    simp only [Option.some.injEq] at eq
    subst eq
    simp only [RuleApp.sequents, Finset.mem_insert, Finset.mem_singleton] at Γ'_R
    rcases Γ'_R with Γ'_R | Γ'_R
    all_goals
    subst Γ'_R
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton, reduceCtorEq,
      not_false_eq_true, and_true]
    left
    exact φ_in
  case or =>
    simp only [Option.some.injEq] at eq
    subst eq
    simp only [RuleApp.sequents, Finset.mem_singleton] at Γ'_R
    subst Γ'_R
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton,
      reduceCtorEq, not_false_eq_true, and_true]
    left
    exact φ_in
  case box =>
    simp only [Option.some.injEq] at eq
    subst eq
    simp only [RuleApp.sequents, Finset.mem_singleton] at Γ'_R
    subst Γ'_R
    simp only [Sequent.D, Finset.mem_union, Finset.mem_filter, Bool.decide_eq_true,
      Formula.isDiamond, Finset.mem_sdiff, Finset.mem_singleton,
      reduceCtorEq, not_false_eq_true, and_true]
    left
    left
    exact φ_in
  case diamond =>
    simp only [reduceCtorEq] at eq

/-- Helper for `◇` case of `builder_win_strong`. -/
lemma diamond_in_last_of_diamond_in_first {Γ : Sequent} {strat : Strategy coalgebraGame Builder}
  (h : winning strat (startPos Γ)) :
  ∀ π : MaximalPath Γ strat, ∀ φ (i : ℕ) (lt : i < π.list.length) helper (ps),
    ◇ φ ∈ proverSequent ((π.list)[π.list.length - i - 1]'helper) ps →
      ◇ φ ∈ lastSequent h π := by
  intro π φ i lt helper ps φ_in
  cases i
  case zero =>
    convert φ_in
    simp [lastSequent, List.getLast_eq_getElem]
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
      have eq2 : π.length - (i + 1 + 1) - 1 + 1 = π.length - i - 2 := by
        simp_all
        omega
      have y_u₁ := List.IsChain.getElem chain (π.length - (i + 1 + 1) - 1) (by omega)
      have u₁_u₂ :=
        List.IsChain.getElem chain (π.length - (i + 1 + 1) - 1 + 1) (by omega)
      have P_turn_u₂ :
          coalgebraGame.turn π[π.length - (i + 1 + 1) - 1 + 1 + 1] = Prover := by
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
      · convert P_turn_u₂ using 3
        grind
      · convert diamond_in_of_move_move_diamond_in _ _
          ⟨_, ⟨y_u₁.1, u₁_u₂.1⟩⟩ φ φ_in using 3
        · simp
          grind
        · exact P_turn_u₂

/-- Helper for `◇` case of `builder_win_strong`. -/
lemma formula_in_successor_of_diamond_formula_in {Γ : Sequent}
    {strat : Strategy coalgebraGame Builder} (h : winning strat (startPos Γ))
    {π ρ : MaximalPath Γ strat} (π_ρ : pathRelation Γ strat π ρ) :
    ∀ φ, ◇ φ ∈ lastSequent h π → φ ∈ firstSequent ρ := by
  intro φ diφ_in
  simp only [pathRelation, Relation.Comp] at π_ρ
  have ⟨y, x_y, y_z⟩ := π_ρ
  have hx := maximal_path_ends_in_prover_turn h π
  rcases last_def : π.last with ⟨Γ | R, Γs, Rs⟩ <;>
    try (rw [last_def] at hx; change Builder = Prover at hx; cases hx)
  simp only [last_def] at x_y
  simp only [lastSequent, last_def] at diφ_in
  simp only [proverSequent] at diφ_in
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
    simp only [firstSequent, first_def']
    simp only [proverSequent]
    have R_mem := R_Γ
    have R_f : f R = Γ := f_of_mem_ruleApps R_mem
    have R_box : R.isBox := by
      rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
      simp only [not_exists] at max
      have := max (Sum.inr R, Γ :: Γs, Rs)
      simp only [nonBoxMove, isBox, Bool.not_eq_true, not_and, Bool.not_eq_false] at this
      apply this
      convert x_y
    cases R <;> simp [RuleApp.isBox] at R_box
    rename_i Δ ψ ψ_in
    simp only [f] at R_f
    cases R_f
    simp only [RuleApp.sequents, Finset.union_singleton, Finset.mem_singleton] at Γ'_R
    subst Γ'_R
    exact Finset.mem_insert.mpr (Or.inr (unDi_mem_D_of_ne diφ_in (by simp)))

/-- Helper for `◇` case of `builder_win_strong`. -/
lemma diamond_in_path_of_diamond_formula_in {Γ : Sequent}
    {strat : Strategy coalgebraGame Builder} (h : winning strat (startPos Γ))
    {π ρ : MaximalPath Γ strat} (π_ρ : Relation.TransGen (pathRelation Γ strat) π ρ) :
    ∀ φ, ◇ φ ∈ lastSequent h π → ◇ φ ∈ firstSequent ρ := by
  intro φ φ_in
  induction π_ρ
  case single ρ π_ρ =>
    exact diamond_in_of_move_move_diamond_in
      (maximal_path_ends_in_prover_turn h π) (maximal_path_starts_in_prover_turn ρ)
      π_ρ φ φ_in
  case tail γ _ _ rel ih =>
    apply diamond_in_of_move_move_diamond_in
      (maximal_path_ends_in_prover_turn h _) (maximal_path_starts_in_prover_turn _) rel φ
    apply diamond_in_last_of_diamond_in_first h _ φ (γ.list.length - 1)
    · rcases γ with ⟨ρ, ne, chain, max, head_cases, in_cone⟩
      simp
      grind
    · convert ih
      simp only [firstSequent, MaximalPath.first]
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

/-- Helper for `◇` case of `builder_win_strong`. -/
lemma formula_in_path_of_diamond_formula_in {Γ : Sequent}
    {strat : Strategy coalgebraGame Builder} (h : winning strat (startPos Γ))
    {π ρ : MaximalPath Γ strat} (π_ρ : Relation.TransGen (pathRelation Γ strat) π ρ) :
    ∀ φ, ◇ φ ∈ lastSequent h π → φ ∈ firstSequent ρ := by
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
      simp only [firstSequent, MaximalPath.first]
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

/-- A terminal rule application cannot be available at the last node of a Builder-winning path. -/
private lemma no_terminal_rule_app_at_last {Δ : Sequent} {strat : Strategy coalgebraGame Builder}
  (h : winning strat (startPos Δ)) (π : MaximalPath Δ strat) (R : RuleApp)
  (R_in : R ∈ (lastSequent h π).ruleApps) (R_empty : R.sequents = ∅) : False := by
  have P_turn_y : coalgebraGame.turn π.last = Prover :=
    maximal_path_ends_in_prover_turn h π
  rcases last_def : π.last with ⟨Γ' | R', Γs', Rs'⟩ <;>
    try (rw [last_def] at P_turn_y; change Builder = Prover at P_turn_y; cases P_turn_y)
  have eq : Γ' = lastSequent h π := by
    unfold lastSequent
    simp only [last_def]
    simp [proverSequent]
  subst eq
  have in_cone : inMyCone strat (startPos Δ) π.last := by
    rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
    apply in_cone
    simp
  let next_move : GamePos := ⟨Sum.inr R, (lastSequent h π) :: Γs', Rs'⟩
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

/-- A non-box rule application cannot extend the last node of a maximal path. -/
private lemma no_nonbox_rule_app_at_last {Δ : Sequent} {strat : Strategy coalgebraGame Builder}
  (h : winning strat (startPos Δ)) (π : MaximalPath Δ strat) (R : RuleApp)
  (R_in : R ∈ (lastSequent h π).ruleApps) (R_nonbox : ¬ R.isBox) : False := by
  have P_turn_y : coalgebraGame.turn π.last = Prover :=
    maximal_path_ends_in_prover_turn h π
  rcases last_def : π.last with ⟨Γ' | R', Γs', Rs'⟩ <;>
    try (rw [last_def] at P_turn_y; change Builder = Prover at P_turn_y; cases P_turn_y)
  have eq : Γ' = lastSequent h π := by
    unfold lastSequent
    simp only [last_def]
    simp [proverSequent]
  subst eq
  let next_move : GamePos := ⟨Sum.inr R, (lastSequent h π) :: Γs', Rs'⟩
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
private lemma maximal_path_last_reverse_index_lt {Γ : Sequent}
    {strat : Strategy coalgebraGame Builder}
    (π : MaximalPath Γ strat) : π.list.length - 1 < π.list.length := by
  rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
  simp
  grind

/-- The final reverse index lands at the first node of a nonempty maximal path. -/
private lemma maximal_path_first_reverse_index_lt {Γ : Sequent}
    {strat : Strategy coalgebraGame Builder}
    (π : MaximalPath Γ strat) : π.list.length - (π.list.length - 1) - 1 < π.list.length := by
  have length_pos : 0 < π.list.length := by
    have := π.ne
    grind
  omega

/-- The first node, addressed by the final reverse index, is a Prover turn. -/
private lemma maximal_path_first_reverse_index_turn {Γ : Sequent}
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

/-- Convert membership in the first sequent to membership at the final reverse index. -/
private lemma first_sequent_mem_at_reverse_index {Γ : Sequent}
    {strat : Strategy coalgebraGame Builder}
    (π : MaximalPath Γ strat) {φ : Formula} :
    φ ∈ firstSequent π →
    φ ∈ proverSequent
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
  simp only [firstSequent, MaximalPath.first, idx_zero]
  rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
  cases π with
  | nil => contradiction
  | cons x xs => cases x; simp [proverSequent]

/-- A box formula at the last node produces a related maximal path starting with its premise. -/
private lemma box_successor_path_of_last_box {Δ : Sequent} {strat : Strategy coalgebraGame Builder}
    (h : winning strat (startPos Δ)) (π : MaximalPath Δ strat) {φ : Formula}
    (box_in : □φ ∈ lastSequent h π) :
    ∃ ρ : MaximalPath Δ strat,
      Relation.TransGen (pathRelation Δ strat) π ρ ∧ φ ∈ firstSequent ρ := by
  have P_turn_y : coalgebraGame.turn π.last = Prover :=
    maximal_path_ends_in_prover_turn h π
  rcases last_def : π.last with ⟨Γ' | R', Γs', Rs'⟩ <;>
    try (rw [last_def] at P_turn_y; change Builder = Prover at P_turn_y; cases P_turn_y)
  have eq : Γ' = lastSequent h π := by
    unfold lastSequent
    simp only [last_def]
    simp [proverSequent]
  subst eq
  have in_cone : inMyCone strat (startPos Δ) π.last := by
    rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
    apply in_cone
    simp
  let next_move : coalgebraGame.Pos :=
    ⟨Sum.inr (RuleApp.box (lastSequent h π) φ box_in),
      (lastSequent h π) :: Γs', Rs'⟩
  have move_last_next : Move π.last next_move := by
    unfold next_move
    simp only [last_def]
    apply Move.prover
    simp only [Sequent.ruleApps, Finset.mem_filterMap, Option.dite_none_right_eq_some,
      and_exists_self]
    refine ⟨□ φ, box_in, by simp⟩
  have B_turn_next : coalgebraGame.turn next_move = Builder := by rfl
  have next_in_moves : next_move ∈ coalgebraGame.moves π.last :=
    move_iff_in_moves.1 move_last_next
  have next_in_cone : inMyCone strat (startPos Δ) next_move :=
    inMyCone.oStep in_cone (by simpa [last_def] using P_turn_y) next_in_moves
  have B_turn_winning : winning strat next_move := winning_of_in_cone_winning next_in_cone h
  let next_next_move :=
    strat next_move B_turn_next (winning_has_moves B_turn_next B_turn_winning)
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
  · have move_next_next' := move_next_next
    unfold next_move at move_next_next'
    cases move_next_next'
    case builder Γ_mem Γ_not_mem =>
      simp only [RuleApp.sequents, Finset.union_singleton, Finset.mem_singleton] at Γ_mem
      subst Γ_mem
      rw [first_sequent_eq_of_first ρ ρ_def]
      simp

/-- The penultimate node of a non-box maximal path cannot also be a Prover turn. -/
private lemma no_penultimate_prover_turn {Δ : Sequent} {strat : Strategy coalgebraGame Builder}
    (h : winning strat (startPos Δ)) (π : MaximalPath Δ strat)
    (lt : 1 < π.list.length) helper
    (ps : coalgebraGame.turn (π.list[π.list.length - (0 + 1) - 1]'helper) = Prover) :
    False := by
  have P_turn_last := maximal_path_ends_in_prover_turn h π
  have eq : π.list.length - (0 + 1) - 1 = π.list.length - 2 := by omega
  have eq2 : π.list.length - (0 + 1) - 1 + 1 = π.list.length - 1 := by omega
  rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
  have length_gt_one : π.length > 1 := by simpa using lt
  have u₁_last :=
    List.IsChain.getElem chain (π.length - (0 + 1) - 1) (by omega)
  have helper_last : π[π.length - 1]'(by omega) = π.getLast ne := by grind
  have u₁_last' : nonBoxMove π[π.length - 2] (π.getLast ne) := by
    convert u₁_last using 1
    · simpa [eq2] using helper_last.symm
  rcases u₁_def : π[π.length - 2] with ⟨Γ | R, Γs, Rs⟩
  · have u₁_last_mem := move_iff_in_moves.1 u₁_last'.1
    rw [u₁_def] at u₁_last_mem
    change π.getLast ne ∈
      Finset.map ⟨fun R ↦ (Sum.inr R, Γ :: Γs, Rs), by intro r1 r2; simp⟩
        (Sequent.ruleApps Γ) at u₁_last_mem
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

/-- If Builder has a winning strategy, then for any maximal path π, if `φ` appears in `π` then
    the model `gameBModel` which we previously defined will falsify `φ` at `π`. -/
lemma builder_win_strong {Δ : Sequent} (strat : Strategy coalgebraGame Builder)
    (h : winning strat ⟨Sum.inl Δ, [], []⟩) (π : MaximalPath Δ strat) (φ)
    (i : ℕ) (lt : i < π.list.length) helper (ps) :
    φ ∈ proverSequent ((π.list)[π.list.length - i - 1]'helper) ps →
      ¬ evaluate (gameBModel Δ h, π) φ := by
  intro φ_in
  cases i
  case zero =>
    have is_last : π.list[π.list.length - 0 - 1] = π.last := by simp; grind
    simp_all only
    have P_turn_y : coalgebraGame.turn π.last = Prover := maximal_path_ends_in_prover_turn h π
    rcases last_def : π.last with ⟨Γ' | R', Γs', Rs'⟩ <;>
      try (rw [last_def] at P_turn_y; change Builder = Prover at P_turn_y; cases P_turn_y)
    have eq : Γ' = lastSequent h π := by
      unfold lastSequent
      simp only [last_def]
      simp [proverSequent]
    subst eq
    have in_cone : inMyCone strat ⟨Sum.inl Δ, [], []⟩ π.last := by
      rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
      apply in_cone
      simp
    cases φ
    case bottom => simp_all
    case top =>
      exfalso
      exact no_terminal_rule_app_at_last h π (RuleApp.top (lastSequent h π) φ_in)
        (by
          simp only [Sequent.ruleApps, Finset.mem_filterMap, Option.dite_none_right_eq_some,
            and_exists_self]
          exact ⟨⊤, φ_in, by simp⟩)
        (by simp [RuleApp.sequents])
    case atom n =>
      have φ_in' : at n ∈ lastSequent h π := by
        unfold lastSequent
        simpa using φ_in
      simpa [gameBModel] using φ_in'
    case negAtom n =>
      simp only [evaluate, not_not]
      intro nφ_in
      exact no_terminal_rule_app_at_last h π
        (RuleApp.ax (lastSequent h π) n ⟨nφ_in, φ_in⟩)
        (by
          simp only [Sequent.ruleApps, Finset.mem_filterMap, Option.dite_none_right_eq_some,
            and_exists_self]
          exact ⟨at n, nφ_in, by
            simp only [Option.dite_none_right_eq_some, exists_prop, and_true]
            exact φ_in⟩)
        (by simp [RuleApp.sequents])
    case or φ1 φ2 =>
      exfalso
      exact no_nonbox_rule_app_at_last h π
        (RuleApp.or (lastSequent h π) φ1 φ2 φ_in)
        (by
          simp only [Sequent.ruleApps, Finset.mem_filterMap, Option.dite_none_right_eq_some,
            and_exists_self]
          exact ⟨φ1 v φ2, φ_in, by simp⟩)
        (by simp [RuleApp.isBox])
    case and φ1 φ2 =>
      exfalso
      exact no_nonbox_rule_app_at_last h π
        (RuleApp.and (lastSequent h π) φ1 φ2 φ_in)
        (by
          simp only [Sequent.ruleApps, Finset.mem_filterMap, Option.dite_none_right_eq_some,
            and_exists_self]
          exact ⟨φ1 & φ2, φ_in, by simp⟩)
        (by simp [RuleApp.isBox])
    case diamond φ =>
      simp only [evaluate, not_exists, not_and]
      intro ρ π_ρ
      exact builder_win_strong strat h ρ φ (ρ.list.length - 1)
        (maximal_path_last_reverse_index_lt ρ) (maximal_path_first_reverse_index_lt ρ)
        (maximal_path_first_reverse_index_turn ρ)
        (first_sequent_mem_at_reverse_index ρ
          (formula_in_path_of_diamond_formula_in h π_ρ φ φ_in))
    case box φ =>
      simp only [evaluate, not_forall]
      have ⟨ρ, ρ_def, first_mem⟩ := box_successor_path_of_last_box h π φ_in
      refine ⟨ρ, ?_, ?_⟩
      · simpa [gameBModel] using ρ_def
      · exact builder_win_strong strat h ρ φ (ρ.list.length - 1)
          (maximal_path_last_reverse_index_lt ρ) (maximal_path_first_reverse_index_lt ρ)
          (maximal_path_first_reverse_index_turn ρ)
          (first_sequent_mem_at_reverse_index ρ first_mem)
  case succ i =>
    cases i
    case zero =>
      exfalso
      exact no_penultimate_prover_turn h π (by simpa using lt) helper ps
    case succ i =>
      rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
      have ne_zero : π.length ≠ 0 := by grind
      have length_gt_two : π.length > 2 := by simp at lt; grind
      have eq3 : π.length - (i + 1 + 1) - 1 = π.length - i - 3 := by omega
      have eq2 : π.length - (i + 1 + 1) - 1 + 1 = π.length - i - 2 := by simp_all; omega
      have y_u₁ := List.IsChain.getElem chain (π.length - (i + 1 + 1) - 1) (by omega)
      have u₁_u₂ := List.IsChain.getElem chain (π.length - (i + 1 + 1) - 1 + 1) (by omega)
      have no_box_u₁ := y_u₁.2
      simp only at φ_in
      rcases y_def : π[π.length - (i + 1 + 1) - 1] with ⟨Γ | R, Γs, Rs⟩ <;>
        simp [y_def] at ps
      simp only [y_def] at φ_in
      simp only [y_def] at y_u₁
      have y_u₁_mem := move_iff_in_moves.1 y_u₁.1
      change π[π.length - (i + 1 + 1) - 1 + 1] ∈
        Finset.map ⟨fun R ↦ (Sum.inr R, Γ :: Γs, Rs), by intro r1 r2; simp⟩
          (Sequent.ruleApps Γ) at y_u₁_mem
      rcases (Finset.mem_map).mp y_u₁_mem with ⟨R, R_Γ, u₁_def⟩
      have u₁_u₂ :
          nonBoxMove (Sum.inr R, Γ :: Γs, Rs)
            (π[π.length - (i + 1 + 1) - 1 + 1 + 1]'(by grind)) := by
        convert u₁_u₂ -- dont understand why simp or rw doesn't do this
      have u₁_u₂_mem := move_iff_in_moves.1 u₁_u₂.1
      change π[π.length - (i + 1 + 1) - 1 + 1 + 1] ∈
        Finset.filterMap
          (fun Γ' ↦ if Γ' ∈ Γ :: Γs then none else some (Sum.inl Γ', Γ :: Γs, R :: Rs))
          R.sequents (by grind) at u₁_u₂_mem
      rcases (Finset.mem_filterMap _).mp u₁_u₂_mem with ⟨Γ', Γ'_R, u₂_def⟩
      have no_rep : Γ' ∉ Γ :: Γs := by
        by_contra hmem
        simp [hmem] at u₂_def
      simp only [no_rep, ↓reduceIte, Option.some.injEq] at u₂_def
      have u₂_def : (Sum.inl Γ', Γ :: Γs, R :: Rs) =
          π[π.length - (i + 1 + 1) - 1 + 1 + 1] :=
        u₂_def
      have P_turn_u₂ : coalgebraGame.turn (Sum.inl Γ', Γ :: Γs, R :: Rs) = Prover := rfl
      have eq : π.length - i - 1 = π.length - (i + 1 + 1) - 1 + 1 + 1 := by omega
      have P_turn : coalgebraGame.turn π[π.length - i - 1] = Prover := by
        convert P_turn_u₂
        calc
          π[π.length - i - 1] = π[π.length - (i + 1 + 1) - 1 + 1 + 1] := by grind
          _ = (Sum.inl Γ', Γ :: Γs, R :: Rs) := Eq.symm u₂_def
      simp [←eq] at u₂_def
      have eq_helper : proverSequent π[π.length - i - 1] P_turn = Γ' := by
        grind [proverSequent]
      by_cases φ ∈ Γ'
      case pos φ_in =>
        exact builder_win_strong strat h ⟨π, ne, chain, max, head_cases, in_cone⟩
          φ i (by grind) (by grind) P_turn (eq_helper ▸ φ_in)
      case neg nφ_in =>
        cases R <;>
          simp only [RuleApp.sequents, Finset.mem_insert, Finset.mem_singleton,
            Finset.notMem_empty] at Γ'_R
        case and Δ ψ₁ ψ₂ in_Δ _ =>
          have ⟨eq1, eq2⟩ : φ = (ψ₁ & ψ₂) ∧ Γ = Δ := by
            rcases Γ'_R with eq | eq <;> subst eq
            all_goals
            simp only [Sequent.ruleApps, Finset.mem_filterMap,
              Option.dite_none_right_eq_some, and_exists_self] at R_Γ
            have ⟨χ, χ_in, eq⟩ := R_Γ
            cases χ <;> simp at eq
            simp only [eq, and_true]
            by_contra ne
            apply nφ_in
            simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
            refine Or.inl ⟨?_, ne⟩
            convert φ_in
            simp [proverSequent, eq]
          subst eq1 eq2; simp only [evaluate, not_and_or]
          rcases Γ'_R with eq | eq <;> subst eq
          · left
            exact builder_win_strong strat h ⟨π, ne, chain, max, head_cases, in_cone⟩
              ψ₁ i (by grind) (by grind) P_turn (by simp [eq_helper])
          · right
            exact builder_win_strong strat h ⟨π, ne, chain, max, head_cases, in_cone⟩
              ψ₂ i (by grind) (by grind) P_turn (by simp [eq_helper])
        case or Δ ψ₁ ψ₂ in_Δ _ =>
          have ⟨eq1, eq2⟩ : φ = (ψ₁ v ψ₂) ∧ Γ = Δ := by
            subst Γ'_R
            simp only [Sequent.ruleApps, Finset.mem_filterMap,
              Option.dite_none_right_eq_some, and_exists_self] at R_Γ
            have ⟨χ, χ_in, eq⟩ := R_Γ
            cases χ <;> simp at eq
            simp only [eq, and_true]
            by_contra ne
            apply nφ_in
            simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
            refine Or.inl ⟨?_, ne⟩
            convert φ_in
            simp [proverSequent, eq]
          subst eq1 eq2 Γ'_R; simp only [evaluate, not_or]
          constructor
          · exact builder_win_strong strat h ⟨π, ne, chain, max, head_cases, in_cone⟩
              ψ₁ i (by grind) (by grind) P_turn (by simp [eq_helper])
          · exact builder_win_strong strat h ⟨π, ne, chain, max, head_cases, in_cone⟩
              ψ₂ i (by grind) (by grind) P_turn (by simp [eq_helper])
        case box Δ ψ ψ_in _ =>
          exfalso; apply no_box_u₁
          have h : isBox ⟨Sum.inr (RuleApp.box Δ ψ ψ_in), Γ :: Γs, Rs⟩ := by
            simp [isBox, RuleApp.isBox]
          convert h
          exact Eq.symm u₁_def
termination_by (φ.length, i)
decreasing_by
  · subst_eqs; apply Prod.Lex.left; simp [Formula.length]
  · subst_eqs; apply Prod.Lex.left; simp [Formula.length]
  · subst_eqs; apply Prod.Lex.right; omega
  · apply Prod.Lex.left; rw [eq1]; simp [Formula.length]; omega
  · apply Prod.Lex.left; rw [eq1]; simp [Formula.length]; omega
  · apply Prod.Lex.left; rw [eq1]; simp [Formula.length]; omega
  · apply Prod.Lex.left; rw [eq1]; simp [Formula.length]; omega

/-- If Builder has a winning strategy in the game starting from `Γ`, then there is a
countermodel of `Γ! -/
theorem builder_win_builds_model {Γ : Sequent}
  (strat : Strategy coalgebraGame Builder) (h : winning strat (startPos Γ)) : ¬ (⊨ Γ) := by
  simp only [Sequent.isValid, evaluateSeq, not_forall, not_exists, not_and]
  use MaximalPath Γ strat
  use gameBModel Γ h
  have ⟨π, π_head_eq⟩ :=
    always_exists_maximal_path_from_root_or_after Γ strat h (startPos Γ) inMyCone.nil
      (Or.inr rfl)
  use π
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
    rw [h]
    change π.head ne = (Sum.inl Γ, [], []) at π_head_eq
    rw [π_head_eq]
    rfl
  · rcases π with ⟨π, ne, chain, max, head_cases, in_cone⟩
    have h : (π[π.length - (π.length - 1) - 1]'(by grind)) = π.head ne := by
      grind
    simp [h]
    simp at π_head_eq
    simp [π_head_eq]
    simp [proverSequent, φ_in]

/-- Completeness! Comes as a corrolary of `gamedet`, `prover_win_builds_proof`, and
    `builder_win_builds_model`. -/
theorem completeness (Γ : Sequent) : ⊨ Γ → ⊢ Γ := by
  intro Γ_sat
  rcases gamedet coalgebraGame (startPos Γ) with builder_wins | prover_wins
  · have ⟨strat, h⟩ := builder_wins
    have nΓ_sat := builder_win_builds_model strat h
    exfalso
    exact nΓ_sat Γ_sat
  · have ⟨strat, h⟩ := prover_wins
    exact prover_win_builds_proof strat h
end Lean4GlCoalgebras
