/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies, Tomasz Maciosowski, Violeta Hernández Palacios
-/
module

public import LeanPool.MisereGames.Form
public import LeanPool.MisereGames.Mathlib.NatOrdinal

/-!
Misere combinatorial games.
-/

namespace MisereGames

/-!
# Birthdays of games

There are two related but distinct notions of a birthday within combinatorial
game theory. One is the birthday of an `GameForm`, which represents the "step"
at which it is constructed; the *day* on which it is *born*. This is sometimes
called the *formal birthday* of a game (see [Siegel, Definition 1.27 on p.
61][siegel:CombinatorialGameTheory:2013]).

It can be defined recursively as the least ordinal strictly larger than the
birthdays of its Left and Right options.

The birthday of an `GameForm` can also be understood as the depth of its game
tree.
-/

open NatOrdinal Order Set

universe u

public section

namespace Form

open Form

variable {G : Type (u + 1)} [g_form : Form G]

/--
The birthday of a form is inductively defined as the least ordinal strictly
larger than the birthdays of its options. It may be thought as the "step" in
which the given game is constructed.
-/
@[expose]
noncomputable def birthday (x : G) : NatOrdinal.{u + 1} :=
  ⨆ y : {y // IsOption y x}, Order.succ (birthday y)
termination_by x
decreasing_by form_wf

theorem lt_birthday_iff' {x : G} {o : NatOrdinal} : o < birthday x ↔
    ∃ y, IsOption y x ∧ o ≤ birthday y := by
  rw [birthday, NatOrdinal.lt_iSup_iff]
  simp only [succ_eq_add_one, lt_add_one_iff, Subtype.exists, exists_prop]

theorem birthday_le_iff' {x : G} {o : NatOrdinal} : birthday x ≤ o ↔
    ∀ y, IsOption y x → birthday y < o := by
  simpa using lt_birthday_iff'.not

theorem lt_birthday_iff {x : G} {o : NatOrdinal} : o < birthday x ↔
    (∃ y ∈ moves .left x, o ≤ birthday y) ∨ (∃ y ∈ moves .right x, o ≤ birthday y) := by
  simp [lt_birthday_iff', IsOption.iff_mem_union, or_and_right, exists_or]

theorem birthday_le_iff {x : G} {o : NatOrdinal} : birthday x ≤ o ↔
    (∀ y ∈ moves .left x, birthday y < o) ∧ (∀ y ∈ moves .right x, birthday y < o) := by
  simpa using lt_birthday_iff.not

theorem birthday_eq_max (x : G) : birthday x =
    max (⨆ y : moves .left x, succ (birthday y.1)) (⨆ y : moves .right x, succ (birthday y.1)) := by
  apply eq_of_forall_lt_iff
  simp only [lt_birthday_iff, succ_eq_add_one, lt_sup_iff, NatOrdinal.lt_iSup_iff, lt_add_one_iff,
             Subtype.exists, exists_prop, implies_true]

@[aesop safe apply]
theorem birthday_lt_of_mem_moves {p : Player} {x y : G} (hy : y ∈ moves p x) :
    birthday y < birthday x :=
  lt_birthday_iff'.2 ⟨y, .of_mem_moves hy, le_rfl⟩

theorem birthday_lt_of_isOption {x y : G} (hy : IsOption y x) : birthday y < birthday x :=
  lt_birthday_iff'.2 ⟨y, hy, le_rfl⟩

theorem birthday_lt_of_subposition {x y : G} (hy : Subposition y x) :
    birthday y < birthday x := by
  cases hy with
  | single h => exact birthday_lt_of_isOption h
  | tail IH h => exact (birthday_lt_of_subposition IH).trans (birthday_lt_of_isOption h)
termination_by x
decreasing_by form_wf

@[simp]
theorem birthday_neg (x : G) : birthday (-x) = birthday x := by
  refine eq_of_forall_lt_iff fun y ↦ ?_
  rw [lt_birthday_iff, lt_birthday_iff]
  rw [exists_moves_neg, exists_moves_neg, or_comm]
  congr! 3
  all_goals
    dsimp; rw [and_congr_right]
    intro h
    rw [birthday_neg]
termination_by x
decreasing_by form_wf

@[simp]
theorem birthday_add (g h : G) : birthday (g + h) = birthday g + birthday h := by
  refine eq_of_forall_lt_iff fun o ↦ ?_
  simp only [lt_birthday_iff, moves_add, mem_union, mem_image, or_and_right,
             exists_or, ↓existsAndEq, and_true, lt_add_iff, or_or_or_comm]
  congr! 2
  all_goals
    constructor
    · rintro ⟨z, hz, hz'⟩
      refine ⟨_, ⟨z, hz, le_rfl⟩, ?_⟩
      rwa [← birthday_add]
    · rintro ⟨a, ⟨⟨z, hz, hz'⟩, ha⟩⟩
      use z, hz
      rw [birthday_add]
      apply ha.trans
      first | exact add_le_add_left hz' _ | exact add_le_add_right hz' _
termination_by (g, h)
decreasing_by form_wf

theorem birthday_add_lt_left {g' g h : G} (hlt : birthday g' < birthday g) :
    birthday g' + birthday h < birthday g + birthday h := by
  gcongr

theorem birthday_add_lt_right {g h' h : G} (hlt : birthday h' < birthday h) :
    birthday g + birthday h' < birthday g + birthday h := by
  gcongr

@[simp]
theorem birthday_ofSets (s t : Set G) [Small.{u} s] [Small.{u} t] :
    birthday !{s | t} = max (sSup (succ ∘ birthday '' s)) (sSup (succ ∘ birthday '' t)) := by
  rw [birthday_eq_max]
  rw [leftMoves_ofSets, rightMoves_ofSets]
  simp only [iSup, succ_eq_add_one, Function.comp_apply, image_eq_range]

@[simp]
theorem birthday_ofSets_const (s : Set G) [Small.{u} s] :
    birthday !{fun _ ↦ s} = sSup (succ ∘ birthday '' s) := by
  rw [ofSets_eq_ofSets_cases, birthday_ofSets]
  exact max_eq_left le_rfl

@[simp]
theorem birthday_zero : birthday (0 : G) = 0 := by
  unfold birthday
  simp [iSup_eq_zero_iff]

@[simp]
theorem birthday_one : birthday (1 : G) = 1 := by simp [one_def]

@[simp]
theorem birthday_natCast (n : ℕ) : birthday (n : G) = n := by
  induction n with
  | zero => simp only [Nat.cast_zero, birthday_zero]
  | succ k ih => simpa only [Nat.cast_add, Nat.cast_one, birthday_add, birthday_one, add_left_inj]

@[simp]
theorem birthday_ofNat (n : ℕ) [n.AtLeastTwo] : birthday (ofNat(n) : G) = n := by
  simp only [OfNat.ofNat, birthday_natCast]

@[simp]
theorem birthday_intCast (k : ℤ) : birthday (k : G) = k.natAbs := by
  match k with
  | Int.ofNat n => simp
  | Int.negSucc n => simpa using add_comm (G := NatOrdinal) 1 n

open Lean Meta Elab Tactic

/-- Add birthday inequalities from move hypotheses, then simplify birthday arithmetic. -/
elab (name := gameformBirthday) "gameform_birthday" : tactic => do
  Lean.Elab.Tactic.withMainContext do
    -- TODO: Also generate proofs from IsOption g' g and Subposition g' g
    -- From (g' ∈ moves p g) generate proofs for (birthday g' < birthday g)
    let lctx ← getLCtx
    for h in lctx do
      if h.isImplementationDetail then continue
      let type ← instantiateMVars h.type
      if type.isAppOfArity ``Membership.mem 5 then
        let args := type.getAppArgs
        let collection := args[3]!
        if collection.getAppFn.isConstOf `Moves.moves then
          let birthdayName ← mkFreshUserName `h
          let birthdayProof ← mkAppM `Form.birthday_lt_of_mem_moves #[h.toExpr]
          liftMetaTactic fun goalId => do
            let newGoalId ← goalId.assert birthdayName (← inferType birthdayProof) birthdayProof
            let (_, birthdayProofId) ← newGoalId.intro1P
            return [birthdayProofId]
  Lean.Elab.Tactic.withMainContext do
    evalTactic (← `(tactic| try simp only [Form.birthday_neg, Form.birthday_add] at *))
    evalTactic (← `(tactic| try simp))
    evalTactic (← `(tactic| try omega))

end Form

end

end MisereGames
