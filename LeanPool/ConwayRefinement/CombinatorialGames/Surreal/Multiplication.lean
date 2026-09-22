/-
Copyright (c) 2024 Theodore Hwa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison, Violeta Hernández Palacios, Junyan Xu, Theodore Hwa
-/
module

public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Basic

import Mathlib.Logic.Hydra
import Mathlib.Tactic.Abel

/-!
# Surreal multiplication

In this file, we show that multiplication of surreal numbers is well-defined, and thus the surreal
numbers form a linear ordered commutative ring. This is Theorem 8 in [Conway2001], or Theorem 3.8 in
[SchleicherStoll].

An inductive argument proves the following three main theorems:

* P1: being numeric is closed under multiplication,
* P2: multiplying a numeric pregame by equivalent numeric pregames results in equivalent pregames,
* P3: the product of two positive numeric pregames is positive (`mul_pos`).

P1 allows us to define multiplication as an operation on numeric pregames, P2 says that this is
well-defined as an operation on the quotient by `IGame.Equiv`, namely the surreal numbers, and P3 is
an axiom that needs to be satisfied for the surreals to be a `OrderedRing`.

We follow the proof in [SchleicherStoll], except that we use the well-foundedness of the hydra
relation `CutExpand` on `Multiset IGame` instead of the argument based on a depth function in the
paper. As in said argument, P3 is proven by proxy of an auxiliary P4, which states that for
`x₁ < x₂` and `y`, then `x₁ * y + x₂ * a < x₁ * a + x₂ * y` when `a ∈ yᴸ`, and
`x₁ * b + x₂ * y < x₁ * y + x₂ * b` when `b ∈ yᴿ`.

## Reducing casework

This argument is very casework heavy in a way that's difficult to automate. For instance, in P1, we
have to prove four different inequalities of the form
`a ∈ (x * y)ᴸ → b ∈ (x * y)ᴿ → a < b`, and depending on what form the options of
`x * y` take, we have to apply different instantiations of the inductive hypothesis.

To greatly simplify things, we work uniquely in terms of left options, which we achieve by rewriting
`a ∈ xᴿ` as `-a ∈ (-x)ᴸ`. We then show that our distinct lemmas and inductive
hypotheses are invariant under the appropriate sign changes. In the P1 example, this makes it so
that one case (`mulOption_lt_of_lt`) is enough to conclude the others (`mulOption_lt`), and the same
goes for the other parts of the proof.

Note also that we express all inequalities in terms of `ConwayGame` instead of `IGame`; this
allows us to
make use of `abel` and all of the theorems on `OrderedAddCommGroup`.
-/

universe u

open ConwayGame IGame Relation WellFounded

/-- A characterization of left moves of `x * y` in terms only of left moves. -/
private lemma forall_leftMoves_mul' {P : IGame → Prop} {x y : IGame} :
    (∀ a ∈ (x * y)ᴸ, P a) ↔
      (∀ a ∈ xᴸ, ∀ b ∈ yᴸ, P (mulOption x y a b)) ∧
      (∀ a ∈ (-x)ᴸ, ∀ b ∈ (-y)ᴸ, P (mulOption (-x) (-y) a b)) := by
  rw [forall_moves_mul]
  simp [mulOption_neg]

/-- A characterization of right moves of `x * y` in terms only of left moves. -/
private lemma forall_rightMoves_mul' {P : IGame → Prop} {x y : IGame} :
    (∀ a ∈ (x * y)ᴿ, P a) ↔
      (∀ a ∈ xᴸ, ∀ b ∈ (-y)ᴸ, P (-mulOption x (-y) a b)) ∧
      (∀ a ∈ (-x)ᴸ, ∀ b ∈ yᴸ, P (-mulOption (-x) y a b)) := by
  rw [forall_moves_mul]
  simp [mulOption_neg_right, mulOption_neg_left]

/-! ### Predicates P1 – P4 -/

/-- `P1 x y a b c d` means that `mulOption x y a b < mulOption x y c d`. This is the general form
of the statements needed to prove that `x * y` is numeric. -/
private def P1 (x y a b c d : IGame) :=
  ConwayGame.mk (mulOption x y a b) < ConwayGame.mk (mulOption x y c d)

/-- `P2 x₁ x₂ y` states that if `x₁ ≈ x₂`, then `x₁ * y ≈ x₂ * y`. The RHS is stated in terms of
`ConwayGame.mk` for rewriting convenience. -/
private def P2 (x₁ x₂ y : IGame) := x₁ ≈ x₂ → ConwayGame.mk (x₁ * y) = ConwayGame.mk (x₂ * y)

/-- `P3 x₁ x₂ y₁ y₂` states that `x₁ * y₂ + x₂ * y₁ < x₁ * y₁ + x₂ * y₂`. Using distributivity, this
is equivalent to `(x₁ - x₂) * (y₁ - y₂) > 0`. -/
private def P3 (x₁ x₂ y₁ y₂ : IGame) :=
  ConwayGame.mk (x₁ * y₂) + ConwayGame.mk (x₂ * y₁) <
    ConwayGame.mk (x₁ * y₁) + ConwayGame.mk (x₂ * y₂)

/-- `P4 x₁ x₂ y` states that if `x₁ < x₂`, then `P3 x₁ x₂ a y` when `a ∈ yᴸ`, and
`P3 x₁ x₂ b y` when `b ∈ yᴿ`.

Note that we instead write this second part as `P3 x₁ x₂ b (-y)` when `b ∈ (-y)ᴸ`. See the
module docstring for an explanation. -/
private def P4 (x₁ x₂ y : IGame) :=
  x₁ < x₂ → (∀ a ∈ yᴸ, P3 x₁ x₂ a y) ∧ (∀ b ∈ (-y)ᴸ, P3 x₁ x₂ b (-y))

/-- The conjunction of `P2` and `P4`. Both statements have the same amount of arguments and satisfy
similar symmetry properties, so we can slightly simplify the argument by merging them. -/
private def P24 (x₁ x₂ y : IGame) : Prop := P2 x₁ x₂ y ∧ P4 x₁ x₂ y

variable {x x₁ x₂ x₃ x' y y₁ y₂ y₃ y' a b c d : IGame.{u}}

/-! #### Symmetry properties of P1 – P4 -/

private lemma P3_comm : P3 x₁ x₂ y₁ y₂ ↔ P3 y₁ y₂ x₁ x₂ := by
  simp [P3, add_comm, mul_comm]

private lemma P3.trans (h₁ : P3 x₁ x₂ y₁ y₂) (h₂ : P3 x₂ x₃ y₁ y₂) : P3 x₁ x₃ y₁ y₂ := by
  rw [P3, ← add_lt_add_iff_left (ConwayGame.mk (x₂ * y₁) + ConwayGame.mk (x₂ * y₂))]
  convert add_lt_add h₁ h₂ using 1 <;> abel

private lemma P3_neg : P3 (-x₂) (-x₁) y₁ y₂ ↔ P3 x₁ x₂ y₁ y₂ := by
  simp_rw [P3, neg_mul, ConwayGame.mk_neg]
  rw [← _root_.neg_lt_neg_iff]
  abel_nf

private lemma P2_neg_left : P2 (-x₂) (-x₁) y ↔ P2 x₁ x₂ y := by
  simp [P2, AntisymmRel, eq_comm]

private lemma P2_neg_right : P2 x₁ x₂ (-y) ↔ P2 x₁ x₂ y := by
  simp [P2]

private lemma P4_neg_left : P4 (-x₂) (-x₁) y ↔P4 x₁ x₂ y  := by
  simp_rw [P4, IGame.neg_lt_neg_iff, P3_neg]

private lemma P4_neg_right : P4 x₁ x₂ (-y) ↔ P4 x₁ x₂ y := by
  rw [P4, P4, neg_neg, and_comm]

private lemma P24_neg_left : P24 (-x₂) (-x₁) y ↔ P24 x₁ x₂ y := by
  rw [P24, P24, P2_neg_left, P4_neg_left]
private lemma P24_neg_right : P24 x₁ x₂ (-y) ↔ P24 x₁ x₂ y := by
  rw [P24, P24, P2_neg_right, P4_neg_right]

/-! ### Inductive setup -/

/-- The type of lists of arguments for `P1`, `P2`, and `P4`. -/
private inductive Args : Type (u + 1)
  | P1 (x y : IGame.{u}) : Args
  | P24 (x₁ x₂ y : IGame.{u}) : Args

/-- The multiset associated to a list of arguments. -/
private def Args.toMultiset : Args → Multiset IGame
  | (Args.P1 x y) => {x, y}
  | (Args.P24 x₁ x₂ y) => {x₁, x₂, y}

@[simp] private lemma Args.toMultiset_P1 {x y} : (Args.P1 x y).toMultiset = {x, y} := rfl
@[simp] private lemma Args.toMultiset_P24 {x₁ x₂ y} : (Args.P24 x₁ x₂ y).toMultiset = {x₁, x₂, y} :=
  rfl

/-- A list of arguments is numeric if all the arguments are. -/
private def Args.Numeric (a : Args) := ∀ x ∈ a.toMultiset, x.Numeric

private lemma Args.numeric_P1 {x y} : (Args.P1 x y).Numeric ↔ x.Numeric ∧ y.Numeric := by
  simp [Args.Numeric, Args.toMultiset]

private lemma Args.numeric_P24 {x₁ x₂ y} :
    (Args.P24 x₁ x₂ y).Numeric ↔ x₁.Numeric ∧ x₂.Numeric ∧ y.Numeric := by
  simp [Args.Numeric, Args.toMultiset]

/-- The well-founded relation specifying when a list of game arguments is considered simpler than
another: `ArgsRel a₁ a₂` is true if `a₁`, considered as a multiset, can be obtained from `a₂` by
repeatedly removing a game from `a₂` and adding back one or two options of the game.

See also `WellFounded.CutExpand`. -/
private def ArgsRel :=
  InvImage (TransGen <| CutExpand fun x y => ∃ p, x ∈ y.moves p) Args.toMultiset

/-- `ArgsRel` is well-founded. -/
private lemma argsRel_wf : WellFounded ArgsRel :=
  InvImage.wf _ (Subrelation.wf (fun h => h.elim fun _ => Subposition.of_mem_moves)
    subposition_wf).cutExpand.transGen
instance : WellFounded ArgsRel := argsRel_wf

/-- The property that all arguments are numeric is leftward-closed under `ArgsRel`. -/
private lemma ArgsRel.numeric_closed {a' a} : ArgsRel a' a → a.Numeric → a'.Numeric :=
  TransGen.closed' <| @cutExpand_closed _ _
    ⟨fun _ h => (h.elim fun _ => Subposition.of_mem_moves).irrefl⟩ _ fun h h' ↦
      h'.subposition (h.elim fun _ => Subposition.of_mem_moves)

/-- The statement that we will show by induction for all `Numeric` args, using the well-founded
relation `ArgsRel`.

The inductive hypothesis in the proof will be `∀ a', ArgsRel a' a → P124 a`. -/
private def P124 : Args → Prop
  | (Args.P1 x y) => Numeric (x * y)
  | (Args.P24 x₁ x₂ y) => P24 x₁ x₂ y

/-! ### P1 follows from the inductive hypothesis -/

private lemma numeric_move_mul_of_IH {p : Player} (IH : ∀ a, ArgsRel a (Args.P1 x y) → P124 a)
    (h : x' ∈ x.moves p) : (x' * y).Numeric :=
  IH (Args.P1 x' y) (TransGen.single <| cutExpand_pair_left ⟨p, h⟩)

private lemma numeric_mul_move_of_IH {p : Player} (IH : ∀ a, ArgsRel a (Args.P1 x y) → P124 a)
    (h : y' ∈ y.moves p) : (x * y').Numeric :=
  IH (Args.P1 x y') (TransGen.single <| cutExpand_pair_right ⟨p, h⟩)

private lemma numeric_move_mul_move_of_IH {p q : Player}
    (IH : ∀ a, ArgsRel a (Args.P1 x y) → P124 a)
    (hx : x' ∈ x.moves p) (hy : y' ∈ y.moves q) : (x' * y').Numeric :=
  IH (Args.P1 x' y')
    ((TransGen.single (cutExpand_pair_right ⟨q, hy⟩)).tail (cutExpand_pair_left ⟨p, hx⟩))

/-- A specialization of the inductive hypothesis used to prove `P1`. -/
private def IH1 (x y : IGame) : Prop :=
  ∀ ⦃p q x₁ x₂ y'⦄, x₁ ∈ x.moves p → x₂ ∈ x.moves q → (y' = y ∨ ∃ u, y' ∈ y.moves u) → P24 x₁ x₂ y'

/-- `IH1 x y` follows from the inductive hypothesis for `P1 x y`. -/
private lemma IH1_of_IH (IH : ∀ a, ArgsRel a (Args.P1 x y) → P124 a) : IH1 x y := by
  rintro p q x₁ x₂ y' h₁ h₂ (rfl | hy) <;> apply IH (.P24 ..)
  on_goal 2 => refine .tail ?_ (cutExpand_pair_right hy)
  all_goals exact .single (cutExpand_double_left ⟨p, h₁⟩ ⟨q, h₂⟩)

/-- `IH1 y x` follows from the inductive hypothesis for `P1 x y`. -/
private lemma IH1_swap_of_IH (IH : ∀ a, ArgsRel a (Args.P1 x y) → P124 a) : IH1 y x :=
  IH1_of_IH <| by
  simpa [-Multiset.insert_eq_cons, ArgsRel, InvImage, Multiset.pair_comm] using IH

private lemma IH1_neg_left : IH1 x y → IH1 (-x) y := by
  intro h p q x₁ x₂ y' h₁ h₂ hy
  rw [moves_neg] at h₁ h₂
  exact P24_neg_left.1 (h h₂ h₁ hy)

private lemma IH1_neg_right : IH1 x y → IH1 x (-y) := by
  intro h p q x₁ x₂ y' h₁ h₂ hy
  rw [← P24_neg_right]
  apply h h₁ h₂
  simpa [neg_eq_iff_eq_neg, or_comm] using hy

private lemma P1_of_equiv (he : x₁ ≈ x₃) (h₁ : P2 x₁ x₃ y₁) (h₃ : P2 x₁ x₃ y₃)
    (h3 : P3 x₁ x₂ y₂ y₃) :
    P1 x₂ y₁ x₁ y₂ x₃ y₃ := by
  rw [P1, mk_mulOption, mk_mulOption, ← h₁ he, ← h₃ he, sub_lt_sub_iff]
  convert add_lt_add_left h3 (.mk (x₁ * y₁)) using 1 <;> abel

private lemma P1_of_P3 (h₁ : P3 x₃ x₂ y₂ y₃) (h₂ : P3 x₁ x₃ y₂ y₁) : P1 x₂ y₁ x₁ y₂ x₃ y₃ := by
  rw [P1, mk_mulOption, mk_mulOption, sub_lt_sub_iff, ← add_lt_add_iff_left (.mk (x₃ * y₂))]
  convert add_lt_add h₁ h₂ using 1 <;> abel

private lemma P3_of_IH1 [Numeric y] (ihyx : IH1 y x)
    (ha : a ∈ xᴸ) (hb : b ∈ yᴸ) (hd : d ∈ (-y)ᴸ) : P3 a x b (-d) := by
  rw [P3_comm]
  rw [moves_neg] at hd
  refine ((ihyx hb hd (.inl rfl)).2 ?_).1 a ha
  exact Numeric.left_lt_right hb hd

private lemma P24_of_IH1 (ihxy : IH1 x y) (ha : a ∈ xᴸ) (hb : b ∈ xᴸ) : P24 a b y :=
  ihxy ha hb (Or.inl rfl)

private lemma mulOption_lt_iff_P1 :
    ConwayGame.mk (mulOption x y a b) < -ConwayGame.mk (mulOption x (-y) c d) ↔
      P1 x y a b c (-d) := by
  simp [P1, mulOption, sub_eq_add_neg, add_comm]

private lemma mulOption_lt_of_lt [Numeric y] (ihxy : IH1 x y) (ihyx : IH1 y x) {a b c d} (h : a < c)
    (ha : a ∈ xᴸ) (hb : b ∈ yᴸ) (hc : c ∈ xᴸ) (hd : d ∈ (-y)ᴸ) :
    ConwayGame.mk (mulOption x y a b) < -ConwayGame.mk (mulOption x (-y) c d) := by
  rw [mulOption_lt_iff_P1]
  exact P1_of_P3 (P3_of_IH1 ihyx hc hb hd) <| ((P24_of_IH1 ihxy ha hc).2 h).1 b hb

private lemma mulOption_lt [Numeric x] [Numeric y] (ihxy : IH1 x y) (ihyx : IH1 y x) {a b c d}
    (ha : a ∈ xᴸ) (hb : b ∈ yᴸ) (hc : c ∈ xᴸ) (hd : d ∈ (-y)ᴸ) :
    ConwayGame.mk (mulOption x y a b) < -ConwayGame.mk (mulOption x (-y) c d) := by
  numeric
  obtain (h | h | h) := Numeric.lt_or_equiv_or_gt a c
  · exact mulOption_lt_of_lt ihxy ihyx h ha hb hc hd
  · exact mulOption_lt_iff_P1.2 (P1_of_equiv h (P24_of_IH1 ihxy ha hc).1
      (ihxy ha hc <| .inr ⟨right, by simpa using hd⟩).1 <| P3_of_IH1 ihyx ha hb hd)
  · rw [← neg_neg y] at hb
    simpa [lt_neg] using mulOption_lt_of_lt (IH1_neg_right ihxy) (IH1_neg_left ihyx) h hc hd ha hb

/-- `P1` follows from the induction hypothesis. -/
private lemma P1_of_IH (IH : ∀ a, ArgsRel a (Args.P1 x y) → P124 a) [Numeric x] [Numeric y] :
    (x * y).Numeric := by
  have ihxy := IH1_of_IH IH
  have ihyx := IH1_swap_of_IH IH
  have ihxyn := IH1_neg_left (IH1_neg_right ihxy)
  have ihyxn := IH1_neg_left (IH1_neg_right ihyx)
  refine .mk ?_ ?_
  · simp_rw [forall_leftMoves_mul', forall_rightMoves_mul']
    constructor <;> intro a ha b hb <;> constructor <;> intro c hc d hd
    · exact mulOption_lt ihxy ihyx ha hb hc hd
    · simpa [mulOption_comm, ← mk_lt_mk] using mulOption_lt ihyx ihxy hb ha hd hc
    · rw [← neg_neg x] at hc
      simpa [mulOption_comm, ← mk_lt_mk] using mulOption_lt ihyxn ihxyn hb ha hd hc
    · rw [← neg_neg y] at hd
      simpa [← mk_lt_mk] using mulOption_lt ihxyn ihyxn ha hb hc hd
  · intro p
    simp only [moves_mul, moves_mul, mulOption, Set.mem_image, Prod.exists,
      forall_exists_index, and_imp]
    rintro _ a b (⟨ha, hb⟩ | ⟨ha, hb⟩) rfl
    all_goals
      have := numeric_move_mul_of_IH IH ha
      have := numeric_mul_move_of_IH IH hb
      have := numeric_move_mul_move_of_IH IH ha hb
      infer_instance

/-! ### P2 follows from the inductive hypothesis -/

private lemma numeric_of_IH (IH : ∀ a, ArgsRel a (Args.P24 x₁ x₂ y) → P124 a) :
    (x₁ * y).Numeric ∧ (x₂ * y).Numeric := by
  constructor <;> refine IH (.P1 ..) (.single ?_)
  · exact (cutExpand_add_right {y}).2 <| (cutExpand_add_left {x₁}).2 cutExpand_zero
  · exact (cutExpand_add_right {x₂, y}).2 cutExpand_zero

/-- A specialization of the inductive hypothesis used to prove `P2` and `P4`. -/
private def IH24 (x₁ x₂ y : IGame) : Prop :=
  ∀ ⦃p z⦄,
    (z ∈ x₁.moves p → P24 z x₂ y) ∧
    (z ∈ x₂.moves p → P24 x₁ z y) ∧
    (z ∈ y.moves p → P24 x₁ x₂ z)

/-- A specialization of the induction hypothesis used to prove `P4`. -/
private def IH4 (x₁ x₂ y : IGame) : Prop :=
  ∀ ⦃p q z w⦄, w ∈ y.moves p → (z ∈ x₁.moves q → P2 z x₂ w) ∧ (z ∈ x₂.moves q → P2 x₁ z w)

/-- `IH24 x₁ x₂ y` follows from the inductive hypothesis for `P24 x₁ x₂ y`. -/
private lemma IH24_of_IH (IH : ∀ a, ArgsRel a (Args.P24 x₁ x₂ y) → P124 a) : IH24 x₁ x₂ y := by
  rw [IH24]
  refine fun p z ↦ ⟨?_, ?_, ?_⟩ <;> refine fun h ↦ IH (.P24 ..) (.single ?_)
  · exact (cutExpand_add_right {y}).2 (cutExpand_pair_left ⟨p, h⟩)
  · exact (cutExpand_add_left {x₁}).2 (cutExpand_pair_left ⟨p, h⟩)
  · exact (cutExpand_add_left {x₁}).2 (cutExpand_pair_right ⟨p, h⟩)

/-- `IH24 x₂ x₁ y` follows from the inductive hypothesis for `P24 x₁ x₂ y`. -/
private lemma IH24_swap_of_IH (IH : ∀ a, ArgsRel a (Args.P24 x₁ x₂ y) → P124 a) : IH24 x₂ x₁ y := by
  apply IH24_of_IH
  convert IH using 2
  dsimp [ArgsRel, InvImage, Multiset.insert_eq_cons, ← Multiset.singleton_add]
  abel_nf

/-- `IH4 x₁ x₂ y` follows from the inductive hypothesis for `P24 x₁ x₂ y`. -/
private lemma IH4_of_IH (IH : ∀ a, ArgsRel a (Args.P24 x₁ x₂ y) → P124 a) : IH4 x₁ x₂ y := by
  refine fun p q a b h ↦ ⟨?_, ?_⟩ <;>
    refine fun h' ↦ (IH (.P24 ..) <| (TransGen.single ?_).tail <|
      (cutExpand_add_left {x₁}).2 <| cutExpand_pair_right ⟨p, h⟩).1
  · exact (cutExpand_add_right {b}).2 <| cutExpand_pair_left ⟨q, h'⟩
  · exact (cutExpand_add_right {b}).2 <| cutExpand_pair_right ⟨q, h'⟩

private lemma IH24_neg : IH24 x₁ x₂ y → IH24 (-x₂) (-x₁) y ∧ IH24 x₁ x₂ (-y) := by
  simp_rw [IH24, P24_neg_right, moves_neg]
  refine fun h ↦ ⟨fun p z ↦ ⟨?_, ?_, ?_⟩,
    fun p z ↦ ⟨(@h p z).1, (@h p z).2.1, P24_neg_right.1 ∘ (@h (-p) (-z)).2.2⟩⟩
  all_goals
    rw [← P24_neg_left]
    simp only [neg_neg]
  · exact (@h (-p) (-z)).2.1
  · exact (@h (-p) (-z)).1
  · exact (@h p z).2.2

private lemma IH4_neg : IH4 x₁ x₂ y → IH4 (-x₂) (-x₁) y ∧ IH4 x₁ x₂ (-y) := by
  simp_rw [IH4, moves_neg, Set.mem_neg]
  refine fun h ↦ ⟨fun p q z w h' ↦ ?_, fun p q z w h' ↦ ?_⟩
  · convert (h h').symm using 2 <;> rw [← P2_neg_left, neg_neg]
  · convert h h' using 2 <;> rw [P2_neg_right]

private lemma mulOption_lt_mul_of_equiv [Numeric x₁] (h : IH24 x₁ x₂ y) (he : x₁ ≈ x₂)
    (hi : a ∈ x₁ᴸ) (hj : b ∈ yᴸ) :
    ConwayGame.mk (mulOption x₁ y a b) < ConwayGame.mk (x₂ * y) := by
  convert sub_lt_iff_lt_add'.2 (((h.1 hi).2 _).1 b hj) using 1
  · rw [← (h.2.2 hj).1 he]
    rfl
  · grw [← he]
    exact Numeric.left_lt hi

private lemma mul_right_le_of_equiv [Numeric x₁] [Numeric x₂]
    (ih₁₂ : IH24 x₁ x₂ y) (ih₂₁ : IH24 x₂ x₁ y) (he : x₁ ≈ x₂) : x₁ * y ≤ x₂ * y := by
  have he' := neg_equiv_neg_iff.2 he
  rw [IGame.le_iff_forall_lf]
  simp_rw [← ConwayGame.mk_le_mk]
  constructor
  · rw [forall_leftMoves_mul']
    constructor <;> intro a ha b hb
    · exact (mulOption_lt_mul_of_equiv ih₁₂ he ha hb).not_ge
    · simpa using (mulOption_lt_mul_of_equiv (IH24_neg <| (IH24_neg ih₂₁).1).2 he' ha hb).not_ge
  · rw [forall_rightMoves_mul']
    constructor <;> intro a ha b hb
    · simpa [neg_le] using (mulOption_lt_mul_of_equiv (IH24_neg ih₂₁).2 he.symm ha hb).not_ge
    · simpa [neg_le] using (mulOption_lt_mul_of_equiv (IH24_neg ih₁₂).1 he'.symm ha hb).not_ge

/-- `P2` follows from the induction hypothesis. -/
private lemma P2_of_IH (IH : ∀ a, ArgsRel a (Args.P24 x₁ x₂ y) → P124 a) [Numeric x₁] [Numeric x₂]
    (he : x₁ ≈ x₂) : x₁ * y ≈ x₂ * y :=
  ⟨mul_right_le_of_equiv (IH24_of_IH IH) (IH24_swap_of_IH IH) he,
    mul_right_le_of_equiv (IH24_swap_of_IH IH) (IH24_of_IH IH) he.symm⟩

/-! ### P4 follows from the inductive hypothesis -/

private lemma mulOption_lt_mul_iff_P3 : mulOption x y a b < x * y ↔ P3 a x b y :=
  @sub_lt_iff_lt_add' ConwayGame _ _ _ (.mk _) (.mk _) (.mk _)

/-- A specialization of the induction hypothesis used to prove `P3`. -/
private def IH3 (x₁ x' x₂ y₁ y₂ : IGame) : Prop :=
  P2 x₁ x' y₁ ∧ P2 x₁ x' y₂ ∧ P3 x' x₂ y₁ y₂ ∧ (x₁ < x' → P3 x₁ x' y₁ y₂)

/-- `IH3` follows from the induction hypothesis for `P24 x₁ x₂ y`. -/
private lemma IH3_of_IH (ih24 : IH24 x₁ x₂ y) (ih4 : IH4 x₁ x₂ y)
    (hi : a ∈ x₂ᴸ) (hb : b ∈ yᴸ) (hl : mulOption x₂ y a b < x₂ * y) :
    IH3 x₁ a x₂ b y :=
  have h24 := ih24.2.1 hi
  ⟨(ih4 hb).2 hi, h24.1,
    mulOption_lt_mul_iff_P3.1 hl, fun l ↦ (h24.2 l).1 b hb⟩

private lemma P3_of_le_left {y₁ y₂} (i) (h : IH3 x₁ i x₂ y₁ y₂) (hl : x₁ ≤ i) : P3 x₁ x₂ y₁ y₂ := by
  obtain (hl | he) := le_iff_lt_or_antisymmRel.1 hl
  · exact (h.2.2.2 hl).trans h.2.2.1
  · rw [P3, h.1 he, h.2.1 he]
    exact h.2.2.1

/-- P3 follows from `IH3`, so P4 (with `y₁` a left option of `y₂`) follows from the induction
hypothesis. -/
private lemma P3_of_IH3 {y₁ y₂} (h : ∀ i ∈ x₂ᴸ, IH3 x₁ i x₂ y₁ y₂)
    (hs : ∀ i ∈ (-x₁)ᴸ, IH3 (-x₂) i (-x₁) y₁ y₂) (hl : x₁ < x₂) : P3 x₁ x₂ y₁ y₂ := by
  obtain (⟨i, hi, hi'⟩ | ⟨i, hi, hi'⟩) := lf_iff_exists_le.1 hl.not_ge
  · exact P3_of_le_left i (h i hi) hi'
  · refine P3_neg.1 <| P3_of_le_left _ (hs (-i) ?_) ?_ <;> simpa

/-- `P4` follows from the induction hypothesis. -/
private lemma P4_of_IH (IH : ∀ a, ArgsRel a (.P24 x₁ x₂ y) → P124 a) : P4 x₁ x₂ y := by
  have h₁₂ := IH24_of_IH IH
  have h4 := IH4_of_IH IH
  obtain ⟨h₁₂x, h₁₂y⟩ := IH24_neg h₁₂
  obtain ⟨h4x, h4y⟩ := IH4_neg h4
  have := (IH24_neg h₁₂y).1
  have := (IH4_neg h4y).1
  obtain ⟨hn₁, hn₂⟩ := numeric_of_IH IH
  have : (-x₁ * y).Numeric := by simpa
  have : (-x₁ * -y).Numeric := by simpa
  have : (x₂ * -y).Numeric := by simpa
  refine fun hl ↦ ⟨?_, ?_⟩ <;>
    refine fun a ha ↦ P3_of_IH3 ?_ ?_ hl <;>
    intro b hb <;>
    apply IH3_of_IH
  assumption'
  all_goals
    exact Numeric.left_lt (mulOption_mem_moves_mul hb ha)

/-- We tie everything together to complete the induction. -/
private theorem main (a : Args) : a.Numeric → P124 a := by
  apply argsRel_wf.induction a
  intro a IH ha
  replace ih : ∀ a', ArgsRel a' a → P124 a' := fun a' hr ↦ IH a' hr (hr.numeric_closed ha)
  cases a with
  | P1 x y =>
    obtain ⟨_, _⟩ := Args.numeric_P1.1 ha
    exact P1_of_IH ih
  | P24 x₁ x₂ y =>
    obtain ⟨_, _, _⟩ := Args.numeric_P24.1 ha
    constructor
    · exact (ConwayGame.mk_eq <| P2_of_IH ih ·)
    · exact P4_of_IH ih

private lemma main_P24 (x₁ x₂ y : IGame) [hx₁ : Numeric x₁] [hx₂ : Numeric x₂] [hy : Numeric y] :
    P24 x₁ x₂ y :=
  main _ <| Args.numeric_P24.mpr ⟨hx₁, hx₂, hy⟩

/-- One additional inductive argument proves `P3`. -/
private lemma P3_of_lt_of_lt {x₁ x₂ y₁ y₂} [Numeric x₁] [Numeric x₂] [Numeric y₁] [Numeric y₂]
    (hx : x₁ < x₂) (hy : y₁ < y₂) : P3 x₁ x₂ y₁ y₂ := by
  refine P3_of_IH3 ?_ ?_ hx
  all_goals
    intro i hi
    numeric
    refine ⟨(main_P24 ..).1, (main_P24 ..).1, P3_comm.2 ?_, fun h ↦ ?_⟩
  · exact ((main_P24 y₁ y₂ x₂).2 hy).1 _ hi
  · exact P3_of_lt_of_lt h hy
  · exact ((main_P24 y₁ y₂ x₁).2 hy).2 _ hi
  · rw [IGame.neg_lt] at h
    rw [← P3_neg, neg_neg]
    exact P3_of_lt_of_lt h hy
termination_by (x₁, x₂)
decreasing_by all_goals (try rw [moves_neg] at *); igame_wf

/-! ### Instances and corollaries -/

public section

namespace IGame.Numeric

variable {x x₁ x₂ y y₁ y₂ : IGame}

instance mul (x y : IGame) [hx : Numeric x] [hy : Numeric y] : Numeric (x * y) :=
  main _ <| Args.numeric_P1.mpr ⟨hx, hy⟩

protected instance mulOption (x y a b : IGame) [Numeric x] [Numeric y] [Numeric a] [Numeric b] :
    Numeric (mulOption x y a b) :=
  .sub ..

theorem mul_congr_left [Numeric x₁] [Numeric x₂] [Numeric y] (he : x₁ ≈ x₂) : x₁ * y ≈ x₂ * y :=
  ConwayGame.mk_eq_mk.1 ((main_P24 ..).1 he)

theorem mul_congr_right [Numeric x] [Numeric y₁] [Numeric y₂] (he : y₁ ≈ y₂) : x * y₁ ≈ x * y₂ := by
  rw [mul_comm, mul_comm x]; exact Numeric.mul_congr_left he

theorem mul_congr [Numeric x₁] [Numeric x₂] [Numeric y₁] [Numeric y₂]
    (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ * y₁ ≈ x₂ * y₂ :=
  (mul_congr_left hx).trans (mul_congr_right hy)

protected theorem mul_pos [Numeric x₁] [Numeric x₂] (h₁ : 0 < x₁) (h₂ : 0 < x₂) : 0 < x₁ * x₂ := by
  simpa [P3, ← mk_lt_mk] using P3_of_lt_of_lt h₁ h₂

end IGame.Numeric

namespace Surreal

noncomputable instance : CommRing Surreal where
  mul := Quotient.map₂ (fun a b ↦ ⟨a.1 * b.1, inferInstance⟩) fun _ _ h _ _ ↦ Numeric.mul_congr h
  zero_mul := by rintro ⟨x⟩; change mk (0 * x) = mk 0; simp_rw [zero_mul]
  mul_zero := by rintro ⟨x⟩; change mk (x * 0) = mk 0; simp_rw [mul_zero]
  one_mul := by rintro ⟨x⟩; change mk (1 * x) = mk x; simp_rw [one_mul]
  mul_one := by rintro ⟨x⟩; change mk (x * 1) = mk x; simp_rw [mul_one]
  left_distrib := by rintro ⟨x⟩ ⟨y⟩ ⟨z⟩; exact mk_eq (mul_add_equiv ..)
  right_distrib := by rintro ⟨x⟩ ⟨y⟩ ⟨z⟩; exact mk_eq (add_mul_equiv ..)
  mul_comm := by rintro ⟨x⟩ ⟨y⟩; change mk (x * y) = mk (y * x); simp_rw [mul_comm]
  mul_assoc := by rintro ⟨x⟩ ⟨y⟩ ⟨z⟩; exact mk_eq (mul_assoc_equiv ..)

instance : IsStrictOrderedRing Surreal :=
  .of_mul_pos (by rintro ⟨x⟩ ⟨y⟩; exact Numeric.mul_pos)

@[simp]
theorem mk_mul (x y : IGame) [Numeric x] [Numeric y] :
    Surreal.mk (x * y) = Surreal.mk x * Surreal.mk y :=
  rfl

end Surreal

namespace IGame.Numeric

protected theorem mul_neg_of_pos_of_neg {x y : IGame} [Numeric x] [Numeric y]
    (hx : 0 < x) (hy : y < 0) : x * y < 0 :=
  @mul_neg_of_pos_of_neg Surreal _ (.mk x) (.mk y) _ _ hx hy

protected theorem mul_neg_of_neg_of_pos {x y : IGame} [Numeric x] [Numeric y]
    (hx : x < 0) (hy : 0 < y) : x * y < 0 :=
  @mul_neg_of_neg_of_pos Surreal _ (.mk x) (.mk y) _ _ hx hy

protected theorem mul_pos_of_neg_of_neg {x y : IGame} [Numeric x] [Numeric y]
    (hx : x < 0) (hy : y < 0) : 0 < x * y :=
  @mul_pos_of_neg_of_neg Surreal _ _ _ _ _ _ (.mk x) (.mk y) hx hy

protected theorem mul_nonneg {x y : IGame} [Numeric x] [Numeric y]
    (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y :=
  @mul_nonneg Surreal _ (.mk x) (.mk y) _ _ hx hy

protected theorem mul_nonpos_of_nonneg_of_nonpos {x y : IGame} [Numeric x] [Numeric y]
    (hx : 0 ≤ x) (hy : y ≤ 0) : x * y ≤ 0 :=
  @mul_nonpos_of_nonneg_of_nonpos Surreal _ (.mk x) (.mk y) _ _ hx hy

protected theorem mul_nonpos_of_nonpos_of_nonneg {x y : IGame} [Numeric x] [Numeric y]
    (hx : x ≤ 0) (hy : 0 ≤ y) : x * y ≤ 0 :=
  @mul_nonpos_of_nonpos_of_nonneg Surreal _ (.mk x) (.mk y) _ _ hx hy

protected theorem mul_nonneg_of_nonpos_of_nonpos {x y : IGame} [Numeric x] [Numeric y]
    (hx : x ≤ 0) (hy : y ≤ 0) : 0 ≤ x * y :=
  @mul_nonneg_of_nonpos_of_nonpos Surreal _ _ (.mk x) (.mk y) _ _ _ _ hx hy

protected theorem mul_left_cancel {x y z : IGame} [Numeric x] [Numeric y] [Numeric z]
    (hx : ¬ x ≈ 0) (h : x * y ≈ x * z) : y ≈ z := by
  rw [← Surreal.mk_eq_mk] at *
  exact mul_left_cancel₀ hx h

protected theorem mul_right_cancel {x y z : IGame} [Numeric x] [Numeric y] [Numeric z]
    (hx : ¬ x ≈ 0) (h : y * x ≈ z * x) : y ≈ z := by
  rw [← Surreal.mk_eq_mk] at *
  exact mul_right_cancel₀ hx h

@[simp]
protected theorem mul_le_mul_iff_left {x y z : IGame} [Numeric x] [Numeric y] [Numeric z]
    (hx : 0 < x) : y * x ≤ z * x ↔ y ≤ z :=
  mul_le_mul_iff_left₀ (a := Surreal.mk x) (b := Surreal.mk y) (c := Surreal.mk z) hx

@[simp]
protected theorem mul_le_mul_iff_right {x y z : IGame} [Numeric x] [Numeric y] [Numeric z]
    (hx : 0 < x) : x * y ≤ x * z ↔ y ≤ z :=
  mul_le_mul_iff_right₀ (a := Surreal.mk x) (b := Surreal.mk y) (c := Surreal.mk z) hx

@[simp]
protected theorem mul_lt_mul_iff_left {x y z : IGame} [Numeric x] [Numeric y] [Numeric z]
    (hx : 0 < x) : y * x < z * x ↔ y < z :=
  mul_lt_mul_iff_left₀ (a := Surreal.mk x) (b := Surreal.mk y) (c := Surreal.mk z) hx

@[simp]
protected theorem mul_lt_mul_iff_right {x y z : IGame} [Numeric x] [Numeric y] [Numeric z]
    (hx : 0 < x) : x * y < x * z ↔ y < z :=
  mul_lt_mul_iff_right₀ (a := Surreal.mk x) (b := Surreal.mk y) (c := Surreal.mk z) hx

@[simp]
protected theorem mul_le_mul_left_of_neg {x y z : IGame} [Numeric x] [Numeric y] [Numeric z]
    (hz : z < 0) : z * x ≤ z * y ↔ y ≤ x :=
  mul_le_mul_left_of_neg (a := Surreal.mk x) (b := Surreal.mk y) (c := Surreal.mk z) hz

@[simp]
protected theorem mul_le_mul_right_of_neg {x y z : IGame} [Numeric x] [Numeric y] [Numeric z]
    (hz : z < 0) : x * z ≤ y * z ↔ y ≤ x :=
  mul_le_mul_right_of_neg (a := Surreal.mk x) (b := Surreal.mk y) (c := Surreal.mk z) hz

@[simp]
protected theorem mul_lt_mul_left_of_neg {x y z : IGame} [Numeric x] [Numeric y] [Numeric z]
    (hz : z < 0) : z * x < z * y ↔ y < x :=
  mul_lt_mul_left_of_neg (a := Surreal.mk x) (b := Surreal.mk y) (c := Surreal.mk z) hz

@[simp]
protected theorem mul_lt_mul_right_of_neg {x y z : IGame} [Numeric x] [Numeric y] [Numeric z]
    (hz : z < 0) : x * z < y * z ↔ y < x :=
  mul_lt_mul_right_of_neg (a := Surreal.mk x) (b := Surreal.mk y) (c := Surreal.mk z) hz

protected theorem mul_le_mul {a b c d : IGame} [Numeric a] [Numeric b] [Numeric c] [Numeric d] :
    a ≤ b → c ≤ d → 0 ≤ c → 0 ≤ b → a * c ≤ b * d :=
  mul_le_mul (a := Surreal.mk a) (b := Surreal.mk b) (c := Surreal.mk c) (d := Surreal.mk d)

protected theorem mul_lt_mul {a b c d : IGame} [Numeric a] [Numeric b] [Numeric c] [Numeric d] :
    a < b → c ≤ d → 0 < c → 0 ≤ b → a * c < b * d :=
  mul_lt_mul (a := Surreal.mk a) (b := Surreal.mk b) (c := Surreal.mk c) (d := Surreal.mk d)

@[simp]
protected theorem mul_pos_iff_of_pos_left {a b : IGame} [Numeric a] [Numeric b] :
    0 < a → (0 < a * b ↔ 0 < b) :=
  mul_pos_iff_of_pos_left (a := Surreal.mk a) (b := Surreal.mk b)

@[simp]
protected theorem mul_pos_iff_of_pos_right {a b : IGame} [Numeric a] [Numeric b] :
    0 < b → (0 < a * b ↔ 0 < a) :=
  mul_pos_iff_of_pos_right (a := Surreal.mk a) (b := Surreal.mk b)

theorem mul_equiv_zero {x y : IGame} [Numeric x] [Numeric y] : x * y ≈ 0 ↔ x ≈ 0 ∨ y ≈ 0 := by
  repeat rw [← Surreal.mk_eq_mk]
  exact @mul_eq_zero Surreal _ _ (.mk x) (.mk y)

theorem mulOption_congr₁ {x₁ x₂ y a b : IGame}
    [Numeric x₁] [Numeric x₂] [Numeric y] [Numeric a] [Numeric b] (he : x₁ ≈ x₂) :
    mulOption x₁ y a b ≈ mulOption x₂ y a b := by
  simp_all [← Surreal.mk_eq_mk, mulOption]

theorem mulOption_congr₂ {x y₁ y₂ a b : IGame}
    [Numeric x] [Numeric y₁] [Numeric y₂] [Numeric a] [Numeric b] (he : y₁ ≈ y₂) :
    mulOption x y₁ a b ≈ mulOption x y₂ a b := by
  simp_all [← Surreal.mk_eq_mk, mulOption]

theorem mulOption_congr₃ {x y a₁ a₂ b : IGame}
    [Numeric x] [Numeric y] [Numeric a₁] [Numeric a₂] [Numeric b] (he : a₁ ≈ a₂) :
    mulOption x y a₁ b ≈ mulOption x y a₂ b := by
  simp_all [← Surreal.mk_eq_mk, mulOption]

theorem mulOption_congr₄ {x y a b₁ b₂ : IGame}
    [Numeric x] [Numeric y] [Numeric a] [Numeric b₁] [Numeric b₂] (he : b₁ ≈ b₂) :
    mulOption x y a b₁ ≈ mulOption x y a b₂ := by
  simp_all [← Surreal.mk_eq_mk, mulOption]

end IGame.Numeric
end
