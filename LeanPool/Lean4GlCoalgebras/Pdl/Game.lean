/-
Copyright (c) 2026 Madeleine Gignoux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madeleine Gignoux
-/

import Mathlib.Data.Finset.Basic

/-! # A General Theory for Determined Two-player Games

Nothing here is specific about PDL, but we give a general
definition of games and show that one of the two players
must have a winning strategy: `gamedet` at the end.

-/

namespace Lean4GlCoalgebras

/-! ## Games -/

/-- Two players, `A` and `B`. -/
inductive Player : Type
| A : Player
| B : Player
deriving DecidableEq

open Player

theorem Player.ne_A_iff_eq_B {p} : p ≠ A ↔ p = B := by cases p <;> simp

theorem Player.ne_B_iff_eq_A {p} : p ≠ B ↔ p = A := by cases p <;> simp

theorem Player.not_eq_iff_eq_other {p} : (¬ p = A) ↔ p = B := by cases p <;> simp

theorem Player.not_eq_B_iff_eq_A {p} : (¬ p = B) ↔ p = A := by cases p <;> simp

theorem Player.eq_A_or_eq_B {p} : p = A ∨ p = B := by cases p <;> simp

/-- Auxiliary declaration used in the GL coalgebra development. -/
def other : Player → Player
| A => B
| B => A

@[simp]
theorem other_A_eq_B : other A = B := by simp [other]

@[simp]
theorem other_B_eq_A : other B = A := by simp [other]

@[simp]
theorem Player.not_eq_i_eq_other {p i} : (¬ p = i) ↔ p = other i := by cases p <;> cases i <;> simp

theorem Player.not_eq_other_eq_i {p i} : (¬ p = other i) ↔ p = i := by cases p <;> cases i <;> simp

@[simp]
theorem Player.not_i_eq_other {i} : ¬ i = other i := by cases i <;> simp

@[simp]
theorem Player.not_other_i_eq_i {i} : ¬ other i = i := by cases i <;> simp

@[simp]
theorem other_other {i} : other (other i) = i := by cases i <;> simp [other]

/-- Two-player game with
- perfect information
- sequential moves (i.e. only one player moves at each position)
- finitely many moves at each step (aka finitely branching)
- a well-founded relation to ensure that the game ends.
-/
class Game where
  /-- Positions in the game. -/
  Pos : Type
  /-- Whose turn is it? -/
  turn : Pos → Player
  /-- What are the available moves? -/
  moves : Pos → Finset Pos
  /-- A wellfounded relation on positions. -/
  wf : WellFoundedRelation Pos
  /-- Every move goes a step down in the relation. -/
  move_rel : ∀ (p next : Pos), next ∈ moves p → wf.rel next p

/-- This seems a bit hacky, but makes `termination_by (p : g.Pos)` work in `winner` and elsewhere.
If the instance causes trouble, change to `termination_by g.wf.2.wrap p` via `WellFounded.wrap`. -/
instance {g : Game} : WellFoundedRelation Game.Pos := g.wf

/-- Allow notation `p.moves` for `g.moves p`. -/
abbrev Game.Pos.moves {g : Game} : g.Pos → Finset g.Pos := Game.moves

/-- If the bound bound is zero then there are no more moves. -/
lemma Game.no_moves_of_no_rel {g : Game} {p : g.Pos}
    (no_rel : ∀ q, ¬ g.wf.rel q p) : g.moves p = ∅ := by
  suffices ¬ (g.moves p).Nonempty by simp_all
  by_contra hyp
  rcases Finset.Nonempty.exists_mem hyp with ⟨q, q_in⟩
  have := g.move_rel _ q q_in
  simp_all

instance {g : Game} : LT g.Pos := ⟨fun p q => g.wf.rel q p⟩

/-! ## Strategies -/

/-- A strategy in `g` for `i`, whenever it is `i`'s turn, chooses a move, if there are any. -/
def Strategy (g : Game) (i : Player) : Type :=
  ∀ p : g.Pos, g.turn p = i → p.moves.Nonempty → p.moves

/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def chooseMove {g : Game} {p : g.Pos} : p.moves.Nonempty → p.moves :=
  Classical.choice ∘ Set.Nonempty.to_subtype

/-- There is always some strategy. -/
instance Strategy.instNonempty {g i} : Nonempty (Strategy g i) := ⟨fun _ _ => chooseMove⟩

/-- Winner of a game, if the given strategies are used.
A player loses iff it is their turn and there are no moves.
A player wins if the opponent loses. -/
def winner {i} {g : Game} (sI : Strategy g i) (sJ : Strategy g (other i)) (p : g.Pos) : Player :=
  if h1 : (g.moves p).Nonempty
    then if h2 : g.turn p = i --
      then winner sI sJ (sI p h2 h1)
      else winner sI sJ (sJ p (by cases i <;> simp_all) h1)
    else other (g.turn p) -- no more moves, the other player wins
termination_by
  p
decreasing_by
  all_goals
    apply g.move_rel; simp

/-- A strategy is winning at `p` if it wins against all strategies of the other player. -/
def winning {g : Game} {i : Player} (sI : Strategy g i) (p : g.Pos) : Prop :=
  ∀ sJ : Strategy g (other i), winner sI sJ p = i

/-! ## Good positions -/

/-- Auxiliary declaration used in the GL coalgebra development. -/
def good {g : Game} (i : Player) (p : g.Pos) : Prop :=
    (g.turn p = i       ∧ ∃ (q : g.Pos) (_ : q ∈ p.moves), good i q)
  ∨ (g.turn p = other i ∧ ∀ (q : g.Pos) (_ : q ∈ p.moves), good i q)
termination_by p
decreasing_by all_goals apply g.move_rel _ _; assumption

theorem good_is_surviving {i} {g : Game} {p : g.Pos} :
    good i p → g.turn p = i → p.moves.Nonempty := by
  intro W turn
  unfold good at W
  apply (Or.resolve_right · (not_and_of_not_left _ <| not_eq_other_eq_i.mpr turn)) at W
  match W with | ⟨_, ⟨q, ⟨h, _⟩⟩⟩ => exact ⟨q,h⟩

theorem good_or_other {g : Game} (p : g.Pos) : good (g.turn p) p ∨ good (other (g.turn p)) p := by
  apply WellFounded.induction g.wf.2 p
  intro r IH
  by_cases ∃ q ∈ r.moves, good (g.turn r) q
  case pos E =>
    apply Or.inl
    unfold good
    apply Or.inl
    simpa only [exists_prop, true_and] using E
  case neg A =>
    apply Or.inr
    unfold good
    refine Or.inr (And.intro other_other.symm ?_)
    intro q h
    specialize IH q (g.move_rel _ _ h)
    by_cases g.turn r = g.turn q <;> simp_all

theorem good_A_or_B {g : Game} (p : g.Pos) : good A p ∨ good B p := by
  have det := good_or_other p
  cases i : g.turn p <;> cases det <;> simp_all

/-- Auxiliary declaration used in the GL coalgebra development. -/
noncomputable def goodStrat (i : Player) : Strategy g i := fun p turn nempty =>
  have := Classical.dec
  if W : good i p
    then by
      unfold good at W
      have E := And.right <| W.resolve_right (not_and_of_not_left _ <| not_eq_other_eq_i.mpr turn)
      exact ⟨E.choose, E.choose_spec.choose⟩
    else chooseMove nempty

/-! ## Cones -/

/-- The cone of all positions reachable from `p` assuming that `i` plays `sI`. -/
inductive inMyCone {i} {g : Game} (sI : Strategy g i) (p : g.Pos) : g.Pos → Prop
| nil : inMyCone sI p p
| myStep {q} : inMyCone sI p q → (has_moves : q.moves.Nonempty) → (h : g.turn q = i)
                → inMyCone sI p (sI q h has_moves)
| oStep {q r} : inMyCone sI p q → g.turn q = other i → r ∈ g.moves q → inMyCone sI p r

theorem inMyCone_trans {g i} {p q r : g.Pos} {s : Strategy g i} :
    inMyCone s p q → inMyCone s q r → inMyCone s p r :=
  fun a b => by induction b with
  | nil => assumption
  | myStep _ _ _ ih => exact .myStep ih ..
  | oStep a turn h ih => exact .oStep ih turn h

/-- The cone of the `goodStrat` stays inside `good` positions. -/
theorem good_cone {i} {g : Game} {p r : g.Pos} (W : good i p) (h : inMyCone (goodStrat i) p r) :
    good i r := by
  induction h with
  | nil => exact W
  | oStep _ turn h ih =>
    unfold good at ih
    exact (ih.resolve_left (not_and_of_not_left _ <| not_eq_i_eq_other.mpr turn)).right _ h
  | @myStep q a nempty turn ih =>
    unfold goodStrat
    by_cases hq : good i q
    · simp only [hq, ↓reduceDIte]
      unfold good at hq
      have E := And.right <| hq.resolve_right (not_and_of_not_left _ <| not_eq_other_eq_i.mpr turn)
      exact E.choose_spec.choose_spec
    · simp only [hq, ↓reduceDIte]
      contradiction

/-! ## Zermelo's Theorem -/

theorem surviving_is_winning {g i p} {sI : Strategy g i}
    (surv : ∀ q, inMyCone sI p q → g.turn q = i → q.moves.Nonempty)
    : winning sI p :=
  fun sJ => by
    unfold winner
    split
    case isFalse empty =>
      by_contra turn
      apply (not_eq_other_eq_i.mp ∘ Ne.symm) at turn
      exact empty (surv _ .nil turn.symm)
    split
    · exact surviving_is_winning (surv · ∘ inMyCone_trans (.myStep .nil _ _)) _
    next _ turn =>
      exact surviving_is_winning
        (surv · ∘ inMyCone_trans (.oStep .nil (not_eq_i_eq_other.mp turn) <| Subtype.mem _)) _
termination_by p
decreasing_by all_goals apply g.move_rel; exact Subtype.mem _

theorem good_strat_winning {g : Game} {i} {p : g.Pos} (W : good i p) : winning (goodStrat i) p :=
  surviving_is_winning fun _ => good_is_surviving ∘ (good_cone W)

/--
[Zermelo's Theorem](https://en.wikipedia.org/wiki/Zermelo%27s_theorem_(game_theory)):
In every `Game` position one of the two players has a winning strategy.
-/
theorem gamedet (g : Game) (p : g.Pos) :
    (∃ s : Strategy g A, winning s p) ∨ (∃ s : Strategy g B, winning s p) := Or.imp
    (⟨goodStrat A, good_strat_winning ·⟩)
    (⟨goodStrat B, good_strat_winning ·⟩)
    <| good_A_or_B p

/-! ## Additional Helper Theorems -/

lemma winning_has_moves {i g} {sI : Strategy g i} {p : g.Pos}
    (h : g.turn p = i) (sI_wins_p : winning sI p) :
    (g.moves p).Nonempty := by
  specialize sI_wins_p (Classical.choice Strategy.instNonempty)
  unfold winner at sI_wins_p
  by_contra hyp
  simp_all

lemma winning_of_winning_move {i g} {sI : Strategy g i} {p : g.Pos}
    (h : g.turn p = i) (sI_wins_p : winning sI p) :
    winning sI (sI p h (winning_has_moves h sI_wins_p)).val := by
  intro sJ
  have := winning_has_moves h sI_wins_p
  specialize sI_wins_p sJ
  unfold winner at sI_wins_p
  simp_all

lemma game_wf_rel_of_cone {i g} {p r : g.Pos} (sI : Strategy g i) (r_in : inMyCone sI p r) :
    Relation.ReflTransGen g.wf.rel r p := by
  induction r_in
  · exact Relation.ReflTransGen.refl
  case myStep q q_in q_has_moves turn IH =>
    apply Relation.ReflTransGen.head _ IH
    apply g.move_rel
    simp
  case oStep IH =>
    apply Relation.ReflTransGen.head _ IH
    apply g.move_rel
    assumption

lemma not_in_cone_of_move {i g} {p q : g.Pos} (q_in : q ∈ g.moves p) (sI : Strategy g i) :
    ¬ @inMyCone _ g sI q p := by
  intro hyp
  have claim : Relation.TransGen g.wf.rel p p := by
    have m_to_p := g.move_rel _ q q_in
    have := game_wf_rel_of_cone _ hyp
    rw [Relation.reflTransGen_iff_eq_or_transGen] at this
    cases this
    · subst_eqs
      absurd m_to_p
      exact WellFoundedRelation.asymmetric m_to_p
    · apply Relation.TransGen.trans _ (Relation.TransGen.single m_to_p)
      aesop
  absurd claim
  exact Std.Irrefl.irrefl p

lemma same_winner_of_same_in_cone {i g} {sI : Strategy g i} {sJ sJ' : Strategy g (other i)}
    {p : g.Pos}
    (same_cone : ∀ r, inMyCone sJ p r → sJ r = sJ' r)
    : winner sI sJ p = winner sI sJ' p := by
  by_cases p_has_moves : (Game.moves p).Nonempty
  · by_cases turn : Game.turn p = i
    · conv_lhs => unfold winner; rw [dif_pos p_has_moves, dif_pos turn]
      conv_rhs => unfold winner; rw [dif_pos p_has_moves, dif_pos turn]
      apply same_winner_of_same_in_cone
      intro r r_in
      apply same_cone r
      apply @inMyCone_trans g (other i) p (sI p turn p_has_moves) r sJ ?_ r_in
      apply @inMyCone.oStep (other i) g sJ _ p _ inMyCone.nil (by simp_all) (by simp)
    · have other_turn : Game.turn p = other i := Player.not_eq_i_eq_other.mp turn
      conv_lhs => unfold winner; rw [dif_pos p_has_moves, dif_neg turn]
      conv_rhs => unfold winner; rw [dif_pos p_has_moves, dif_neg turn]
      have := @same_winner_of_same_in_cone _ g sI sJ sJ' (sJ' p other_turn p_has_moves).val ?_
      · convert this using 2
        rw [same_cone p inMyCone.nil]
      · intro r r_in
        apply same_cone r
        apply @inMyCone_trans g (other i) p (sJ' p other_turn p_has_moves) r sJ ?_ r_in
        have : (sJ p other_turn p_has_moves) = (sJ' p other_turn p_has_moves) := by
          rw [same_cone p .nil]
        rw [← this]
        apply @inMyCone.myStep _ g sJ _ p inMyCone.nil
  · conv_lhs => unfold winner; rw [dif_neg p_has_moves]
    conv_rhs => unfold winner; rw [dif_neg p_has_moves]
termination_by p
decreasing_by all_goals apply g.move_rel; exact Subtype.mem _

/-- Helper for `gameP_general`. -/
theorem winning_of_whatever_other_move {i g} {sI : Strategy g i}
    {p : g.Pos} (h : g.turn p = other i) (sI_wins_p : winning sI p) (m : g.moves p)
    : winning sI m.val := by
  have : DecidableEq g.Pos := by exact Classical.typeDecidableEq Game.Pos
  unfold winning
  intro sJ
  let sJ_m : Strategy g (other i) := fun npos npos_Bui_turn nonE =>
    -- At `p` we use the given `m`, otherwise d othe same as `sJ`.
    if same_p : npos = p then same_p ▸ m else  sJ _ npos_Bui_turn nonE
  specialize sI_wins_p sJ_m
  unfold sJ_m winner at sI_wins_p
  have : (Game.moves p).Nonempty := ⟨m.1,m.2⟩
  have : ¬ Game.turn p = i := by aesop
  have sI_wins_p := by simpa [*] using sI_wins_p
  convert sI_wins_p using 1 -- because rw [← sI_wins_p] does not work
  apply same_winner_of_same_in_cone
  -- Remains to show that sJ and sJ_m will agree on all remaining moves.
  -- In those lemmas we also use use the well-founded order, not used so far.
  intro r r_in
  have : r ≠ p := by
    intro hyp
    subst hyp
    absurd r_in
    exact not_in_cone_of_move m.2 sJ
  aesop

lemma winning_of_in_cone_winning {g : Game} {i : Player} {p q : g.Pos} {sI : Strategy g i}
    (in_cone : inMyCone sI p q) (h : winning sI p) : winning sI q := by
  induction in_cone
  case nil => exact h
  case myStep q q_in_cone has_moves my_turn ih =>
    apply winning_of_winning_move
    exact ih
  case oStep q q' q_in_cone o_turn in_moves ih =>
    exact @winning_of_whatever_other_move i g sI q o_turn ih ⟨q', in_moves⟩
end Lean4GlCoalgebras
