/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Copyright (c) 2025 Aaron Liu. All rights reserved.
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Copyright (c) 2025 Yuyang Zhao. All rights reserved.
Copyright (c) 2024 Theodore Hwa. All rights reserved.
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov, Aaron Liu, Apurva Nakade, Fox Thomson, František Silváši,
Isabel Longbottom, Junyan Xu, Kim Morrison, Mario Carneiro, Reid Barton, Theodore Hwa,
Violeta Hernández Palacios, Yuyang Zhao
-/
/-
Adapted and modified from the Apache-2.0-licensed CombinatorialGames library:
https://github.com/vihdzp/combinatorial-games
The inlined source modules are named below.
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Logic.Small.Defs
import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.QPF.Univariate.Basic
import Mathlib.Logic.Small.Set
import Mathlib.Logic.Relation
import Mathlib.Order.SetNotation
public import Mathlib.Algebra.Group.Pointwise.Set.Small
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Order.Comparable
import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Logic.Hydra
import Mathlib.Order.GameAdd
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Tactic.Assert
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Tactic.Abel
import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Algebra.Order.Ring.Defs

/-!
# A minimal concrete construction of surreal numbers

This file inlines the numeric-game quotient, addition, and multiplication needed to state
Conway's refinement conjecture without importing CombinatorialGames. The construction is adapted
from the Apache-2.0 CombinatorialGames library. General birthdays, ordinal games, division,
and the complete lattice of surreal cuts are deliberately omitted.
-/

namespace ConwayRefinement.Standalone.InlineSurreal

/-! ## Inlined from `CombinatorialGames.Game.Player` -/

/-!
# Type of players

This file implements the two-element type of players (`Left`, `Right`), alongside other basic
notational machinery to be used within game theory.
-/

@[expose] public section

universe u_inline_0

/-! ### Players -/

/-- Either the Left or Right player. -/
@[aesop safe cases, grind cases]
inductive Player where
  /-- The Left player. -/
  | left  : Player
  /-- The Right player. -/
  | right : Player
deriving DecidableEq, Fintype, Inhabited

namespace Player

/-- Specify a function `Player → α` from its two outputs. -/
@[simp]
abbrev cases {α : Sort*} (l r : α) : Player → α
  | left => l
  | right => r

lemma apply_cases {α β : Sort*} (f : α → β) (l r : α) (p : Player) :
    f (cases l r p) = cases (f l) (f r) p := by
  cases p <;> rfl

@[simp]
theorem cases_inj {α : Sort*} {l₁ r₁ l₂ r₂ : α} :
    cases l₁ r₁ = cases l₂ r₂ ↔ l₁ = l₂ ∧ r₁ = r₂ :=
  ⟨fun h ↦ ⟨congr($h left), congr($h right)⟩, fun ⟨hl, hr⟩ ↦ hl ▸ hr ▸ rfl⟩

theorem const_of_left_eq_right {α : Sort*} {f : Player → α} (hf : f left = f right) :
    ∀ p q, f p = f q
  | left, left | right, right => rfl
  | left, right => hf
  | right, left => hf.symm

theorem const_of_left_eq_right' {f : Player → Prop} (hf : f left ↔ f right) (p q) : f p ↔ f q :=
  (const_of_left_eq_right hf.eq ..).to_iff

@[simp]
protected lemma «forall» {p : Player → Prop} :
    (∀ x, p x) ↔ p left ∧ p right :=
  ⟨fun h ↦ ⟨h left, h right⟩, fun ⟨hl, hr⟩ ↦ fun | left => hl | right => hr⟩

@[simp]
protected lemma «exists» {p : Player → Prop} :
    (∃ x, p x) ↔ p left ∨ p right :=
  ⟨fun | ⟨left, h⟩ => .inl h | ⟨right, h⟩ => .inr h, fun | .inl h | .inr h => ⟨_, h⟩⟩

instance : Neg Player where
  neg := cases right left

@[simp, grind =] lemma neg_left : -left = right := rfl
@[simp, grind =] lemma neg_right : -right = left := rfl
@[simp] theorem eq_neg : ∀ {p q : Player}, p = -q ↔ p ≠ q := by decide
@[simp] theorem neg_eq : ∀ {p q : Player}, -p = q ↔ p ≠ q := by decide
theorem ne_neg : ∀ {p q : Player}, p ≠ -q ↔ p = q := by decide
theorem neg_ne : ∀ {p q : Player}, -p ≠ q ↔ p = q := by decide
theorem neg_ne_self : ∀ (p : Player), -p ≠ p := by decide
theorem self_ne_neg : ∀ (p : Player), p ≠ -p := by decide

instance : InvolutiveNeg Player where
  neg_neg := by decide

/--
The multiplication of `Player`s is used to state the lemmas about the multiplication of
combinatorial games, such as `IGame.mulOption_mem_moves_mul`.
-/
instance : Mul Player where mul
  | left, p => p
  | right, p => -p

@[simp, grind =] lemma left_mul (p : Player) : left * p = p := rfl
@[simp, grind =] lemma right_mul (p : Player) : right * p = -p := rfl
@[simp, grind =] lemma mul_left : ∀ p, p * left = p := by decide
@[simp, grind =] lemma mul_right : ∀ p, p * right = -p := by decide
@[simp, grind =] lemma mul_self : ∀ p, p * p = left := by decide

instance : HasDistribNeg Player where
  neg_mul := by decide
  mul_neg := by decide

instance : CommGroup Player where
  one := left
  inv := id
  mul_assoc := by decide
  mul_comm := by decide
  one_mul := by decide
  mul_one := by decide
  inv_mul_cancel := by decide

@[simp, grind =] lemma one_eq_left : 1 = left := rfl
@[simp, grind =] lemma inv_eq_self (p : Player) : p⁻¹ = p := rfl

end Player

open Player

/-! ### OfSets -/

/--
Type class for the `ofSets` operation.
Used to implement the `!{st}` and `!{s | t}` syntax.
-/
class OfSets (α : Type (u_inline_0 + 1)) (Valid : outParam ((Player → Set α) → Prop)) where
  /-- Construct a combinatorial game from its left and right sets. -/
  ofSets (st : Player → Set α) (h : Valid st) [Small.{u_inline_0} (st left)]
    [Small.{u_inline_0} (st right)] : α
export OfSets (ofSets)

@[inherit_doc OfSets.ofSets]
macro "!{" st:term "}'" h:term:max : term => `(OfSets.ofSets $st $h)

@[inherit_doc OfSets.ofSets]
macro "!{" s:term " | " t:term "}'" h:term:max : term => `(!{Player.cases $s $t}'$h)

/-- A tactic which attempts to automatically solve goals which appear on `OfSets`. -/
macro "ofSetsTactic" : tactic =>
  `(tactic| first
    | done
    | trivial
    | assumption
    | aesop
    | fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
where `h` is a proof that sets are valid"
   )

@[inherit_doc OfSets.ofSets]
macro:max "!{" st:term "}" : term => `(!{$st}'(by ofSetsTactic))

@[inherit_doc OfSets.ofSets]
macro:max "!{" s:term " | " t:term "}" : term => `(!{$s | $t}'(by ofSetsTactic))

recommended_spelling "ofSets" for "!{st}'h" in [ofSets, «term!{_}'_»]
recommended_spelling "ofSets" for "!{s | t}'h" in [ofSets, «term!{_|_}'_»]
recommended_spelling "ofSets" for "!{st}" in [ofSets, «term!{_}»]
recommended_spelling "ofSets" for "!{s | t}" in [ofSets, «term!{_|_}»]

open Lean PrettyPrinter Delaborator SubExpr in
/-- Delaborates `ofSets (Player.cases s t)` to `!{s | t}` and `ofSets st` to `!{st}`. -/
@[app_delab OfSets.ofSets]
meta def delabOfSets : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity' ``OfSets.ofSets 7
  withNaryArg 3 do
    let e ← getExpr
    if e.isAppOfArity' ``Player.cases 3 then
      let s ← withNaryArg 1 delab
      let t ← withNaryArg 2 delab
      `(!{$s | $t})
    else
      let st ← delab
      `(!{$st})

theorem ofSets_eq_ofSets_cases {α} {Valid : (Player → Set α) → Prop} [OfSets α Valid]
    (st : Player → Set α) (h : Valid st) [Small (st left)] [Small (st right)] :
    !{st} = !{st left | st right}'(by convert h; aesop) := by
  congr; ext1 p; cases p <;> rfl

end

/-! ## Inlined from `CombinatorialGames.Game.Functor` -/

/-!
# Game functor

The type of games `IGame` is an inductive type, with a single constructor `ofSets` taking in two
small sets of games (one for each player) and outputting a new game. This suggests the definition:

```
inductive IGame : Type (u_inline_1 + 1)
  | ofSets (st : Player → Set IGame) [∀ p, Small.{u_inline_1} (st p)] : IGame.{u_inline_1}
```

However, the kernel does not accept this, as `Set IGame = IGame → Prop` contains a non-positive
occurence of `IGame` (see [counterexamples.org](https://counterexamples.org/strict-positivity.html)
for an explanation of what this is and why it's disallowed). We can get around this technical
limitation using the machinery of `QPF`s (quotients of polynomial functors). We define a functor
`GameFunctor` by

```
def GameFunctor (α : Type (u_inline_1 + 1)) : Type (u_inline_1 + 1) :=
  {st : Player → Set α // Small.{u_inline_1} (st left) ∧ Small.{u_inline_1} (st right)}
```

We can prove that this is a `QPF`, which then allows us to build its initial algebra through
`QPF.Fix`, which is exactly the inductive type `IGame`. As a bonus, we're able to describe the
coinductive type of loopy games `LGame` as the final coalgebra `QPF.Cofix` of the exact same
functor.
-/

universe u_inline_1

@[expose] public section

/-! ### Game Functor -/

/-- The functor from a type into the subtype of small pairs of sets in that type.

This is the quotient of a polynomial functor. The type `IGame` of well-founded games is defined as
the initial algebra of that `QPF`, while the type `LGame` of loopy games is defined as its final
coalgebra.

In other words, `IGame` and `LGame` have the following descriptions (which don't work verbatim due
to various Lean limitations):

```
inductive IGame : Type (u_inline_1 + 1)
  | ofSets (st : Player → Set IGame) [∀ p, Small.{u_inline_1} (st p)] : IGame.{u_inline_1}

coinductive LGame : Type (u_inline_1 + 1)
  | ofSets (st : Player → Set IGame) [∀ p, Small.{u_inline_1} (st p)] : LGame.{u_inline_1}
```
-/
def GameFunctor (α : Type (u_inline_1 + 1)) : Type (u_inline_1 + 1) :=
  {s : Player → Set α // ∀ p, Small.{u_inline_1} (s p)}

namespace GameFunctor

@[ext]
theorem ext {α : Type (u_inline_1 + 1)} {x y : GameFunctor α} : x.1 = y.1 → x = y :=
  Subtype.ext

instance {α : Type (u_inline_1 + 1)} (x : GameFunctor α) (p : Player) :
    Small.{u_inline_1} (x.1 p) := x.2 p

instance : Functor GameFunctor where
  map f s := ⟨(f '' s.1 ·), fun _ ↦ by infer_instance⟩

theorem map_def {α β} (f : α → β) (s : GameFunctor α) :
    f <$> s = ⟨(f '' s.1 ·), fun _ ↦ by infer_instance⟩ :=
  rfl
noncomputable instance : QPF GameFunctor where
  P := ⟨Player → Type u_inline_1, fun x ↦ Σ p, PLift (x p)⟩
  abs x := ⟨fun p ↦ Set.range (x.2 ∘ .mk p ∘ PLift.up), fun _ ↦ by infer_instance⟩
  repr x := ⟨fun p ↦ Shrink (x.1 p), Sigma.rec (fun _ y ↦ ((equivShrink _).symm y.1).1)⟩
  abs_repr x := by ext; simp [← (equivShrink _).exists_congr_right]
  abs_map f := by intro ⟨x, f⟩; ext; simp [PFunctor.map, map_def]

end GameFunctor

/-! ## Inlined from `CombinatorialGames.Mathlib.Small` -/

/-!
# Tree with small sets of branches is small
-/

universe u_inline_2

public section

open Set

variable {α : Type*} (r : α → α → Prop) [H : ∀ x, Small.{u_inline_2} {y // r x y}]

private def level (x : α) : ℕ → Set α
  | 0 => {x}
  | n + 1 => ⋃₀ ((fun x ↦ {y | r x y}) '' level x n)

private theorem small_level (x : α) : ∀ n, Small.{u_inline_2} (level r x n)
  | 0 => small_single _
  | n + 1 => by
    refine @small_sUnion _ _ ?_ ?_
    · have := small_level x n
      exact small_image ..
    · simp_all

private theorem small_sUnion_level (x : α) : Small.{u_inline_2} (⋃₀ range (level r x)) := by
  refine @small_sUnion _ _ ?_ ?_
  · exact small_range ..
  · simp [small_level]

instance small_transGen (x : α) : Small.{u_inline_2} {y // Relation.TransGen r x y} := by
  refine @small_subset _ _ _ (fun y hy ↦ ?_) (small_sUnion_level r x)
  simp_rw [mem_sUnion, mem_range, exists_exists_eq_and]
  induction hy with
  | single =>
    use 1
    simpa [level]
  | tail hy hr IH =>
    obtain ⟨n, hn⟩ := IH
    use n + 1
    simpa [level] using ⟨_, hn, hr⟩

instance small_transGen' [∀ x, Small.{u_inline_2} {y // r y x}] (x : α) :
    Small.{u_inline_2} {y // Relation.TransGen r y x} := by
  simp_rw [← Relation.transGen_swap (r := r)]
  infer_instance

instance small_reflTransGen (x : α) : Small.{u_inline_2} {y // Relation.ReflTransGen r x y} := by
  simp_rw [Relation.reflTransGen_iff_eq_or_transGen]
  exact @small_insert _ _ _ (small_transGen ..)

instance small_reflTransGen' [∀ x, Small.{u_inline_2} {y // r y x}] (x : α) :
    Small.{u_inline_2} {y // Relation.ReflTransGen r y x} := by
  simp_rw [← Relation.reflTransGen_swap (r := r)]
  infer_instance

/-! ## Inlined from `CombinatorialGames.Tactic.Register` -/



/-! ## Inlined from `CombinatorialGames.Game.IGame` -/

/-!
# Combinatorial (pre-)games

The basic theory of combinatorial games, following Conway's book `On Numbers and Games`.

In ZFC, games are built inductively out of two other sets of games, representing the options for two
players Left and Right. In Lean, we instead define the type of games `IGame` as arising from two
`Small` sets of games, with notation `!{s | t}`. A `u_inline_4`-small type `α : Type v`
is one that is equivalent to some `β : Type u_inline_4`, and the distinction between small and
large types in a given universe closely mimics the ZFC distinction between sets and proper classes.

This definition requires some amount of setup, since Lean's inductive types aren't powerful enough
to express this on their own. See the docstring on `GameFunctor` for more information.

We are also interested in further quotients of `IGame`. The quotient of games under equivalence
`x ≈ y ↔ x ≤ y ∧ y ≤ x`, which in the literature is often what is meant by a "combinatorial game",
is defined as `Game` in `CombinatorialGames.Game.Basic`. The surreal numbers `Surreal` are defined
as a quotient (of a subtype) of games in `CombinatorialGames.Surreal.Basic`.

## Conway induction

Most constructions within game theory, and as such, many proofs within it, are done by structural
induction. Structural induction on games is sometimes called "Conway induction".

The most straightforward way to employ Conway induction is by using the termination checker, with
the auxiliary `igame_wf` tactic. This uses `solve_by_elim` to search the context for proofs of the
form `y ∈ xᴸ` or `y ∈ xᴿ`, which prove termination. Alternatively, you can use
the explicit recursion principles `IGame.ofSetsRecOn` or `IGame.moveRecOn`.

## Order properties

Pregames have both a `≤` and a `<` relation, satisfying the properties of a `Preorder`. The relation
`0 < x` means that `x` can always be won by Left, while `0 ≤ x` means that `x` can be won by Left as
the second player. Likewise, `x < 0` means that `x` can always be won by Right, while `x ≤ 0` means
that `x` can be won by Right as the second player.

Note that we don't actually prove these characterizations. Indeed, in Conway's setup, combinatorial
game theory can be done entirely without the concept of a strategy. For instance, `IGame.zero_le`
implies that if `0 ≤ x`, then any move by Right satisfies `¬ x ≤ 0`, and `IGame.zero_lf` implies
that if `¬ x ≤ 0`, then some move by Left satisfies `0 ≤ x`. The strategy is thus already encoded
within these game relations.

For convenience, we define notation `x ⧏ y` (pronounced "less or fuzzy") for `¬ y ≤ x`, notation
`x ‖ y` for `¬ x ≤ y ∧ ¬ y ≤ x`, and notation `x ≈ y` for `x ≤ y ∧ y ≤ x`.

You can prove most (simple) inequalities on concrete games through the `game_cmp` tactic, which
repeatedly unfolds the definition of `≤` and applies `simp` until it solves the goal.

## Algebraic structures

Most of the usual arithmetic operations can be defined for games. Addition is defined for
`x = !{s₁ | t₁}` and `y = !{s₂ | t₂}` by `x + y = !{s₁ + y, x + s₂ | t₁ + y, x + t₂}`. Negation is
defined by `-!{s | t} = !{-t | -s}`.

The order structures interact in the expected way with arithmetic. In particular, `Game` is an
`OrderedAddCommGroup`. Meanwhile, `IGame` satisfies the slightly weaker axioms of a
`SubtractionCommMonoid`, since the equation `x - x = 0` is only true up to equivalence.
-/

theorem _root_.Relation.transGen_iff_exists {α : Type*} {r : α → α → Prop} {x y : α} :
    Relation.TransGen r x y ↔ ∃ z, r z y ∧ (x = z ∨ Relation.TransGen r x z) := by
  rw [Relation.transGen_iff]
  simp [and_or_left, exists_or, and_comm]

universe u_inline_4

open Set Pointwise

-- Computations can be performed through the `game_cmp` tactic.
public noncomputable section

/-! ### Game moves -/

/-- Well-founded games up to identity.

`IGame` uses the set-theoretic notion of equality on games, meaning that two `IGame`s are equal
exactly when their left and right sets of options are.

This is not the same equivalence as used broadly in combinatorial game theory literature, as a game
like `{0, 1 | 0}` is not *identical* to `{1 | 0}`, despite being equivalent. However, many theorems
can be proven over the 'identical' equivalence relation, and the literature may occasionally
specifically use the 'identical' equivalence relation for this reason. The quotient `Game` of games
up to equality is defined in `CombinatorialGames.Game.Basic`.

More precisely, `IGame` is the inductive type for the single constructor

```
  | ofSets (s t : Set IGame.{u_inline_4}) [Small.{u_inline_4} s]
      [Small.{u_inline_4} t] : IGame.{u_inline_4}
```

(though for technical reasons it's not literally defined as such). A consequence of this is that
there is no infinite line of play. See `LGame` for a definition of loopy games. -/
def IGame : Type (u_inline_4 + 1) :=
  QPF.Fix GameFunctor

namespace IGame
export Player (left right)

/-- Construct an `IGame` from its left and right sets.

This function is regrettably noncomputable. Among other issues, sets simply do not carry data in
Lean. To perform computations on `IGame` we can instead make use of the `game_cmp` tactic. -/
@[no_expose]
instance : OfSets IGame fun _ ↦ True where
  ofSets st _ := QPF.Fix.mk ⟨st, by rintro (_ | _) <;> assumption⟩

/-- The set of moves of the game. -/
def moves (p : Player) (x : IGame.{u_inline_4}) : Set IGame.{u_inline_4} := x.dest.1 p

/-- The set of left moves of the game. -/
scoped notation:max x:max "ᴸ" => moves left x

/-- The set of right moves of the game. -/
scoped notation:max x:max "ᴿ" => moves right x

instance (p : Player) (x : IGame.{u_inline_4}) : Small.{u_inline_4} (x.moves p) := x.dest.2 p

@[simp]
theorem moves_ofSets (p) (st : Player → Set IGame) [Small.{u_inline_4} (st left)]
    [Small.{u_inline_4} (st right)] :
    !{st}.moves p = st p := by
  dsimp [ofSets]; ext; rw [moves, QPF.Fix.dest_mk]

@[simp]
theorem ofSets_moves (x : IGame) : !{x.moves} = x := x.mk_dest


theorem leftMoves_ofSets (s t : Set IGame) [Small.{u_inline_4} s] [Small.{u_inline_4} t] :
    !{s | t}ᴸ = s :=
  moves_ofSets ..


theorem rightMoves_ofSets (s t : Set IGame) [Small.{u_inline_4} s] [Small.{u_inline_4} t] :
    !{s | t}ᴿ = t :=
  moves_ofSets ..

@[simp]
theorem ofSets_leftMoves_rightMoves (x : IGame) : !{xᴸ | xᴿ} = x := by
  convert x.ofSets_moves with p
  cases p <;> rfl

/-- Two `IGame`s are equal when their move sets are.

For the weaker but more common notion of equivalence where `x = y` if `x ≤ y` and `y ≤ x`,
use `Game`. -/
@[ext]
theorem ext {x y : IGame.{u_inline_4}} (h : ∀ p, x.moves p = y.moves p) :
    x = y := by
  rw [← ofSets_moves x, ← ofSets_moves y]
  simp_rw [funext h]

@[simp]
theorem ofSets_inj' {st₁ st₂ : Player → Set IGame}
    [Small (st₁ left)] [Small (st₁ right)] [Small (st₂ left)] [Small (st₂ right)] :
    !{st₁} = !{st₂} ↔ st₁ = st₂ := by
  simp_rw [IGame.ext_iff, moves_ofSets, funext_iff]

theorem ofSets_inj {s₁ s₂ t₁ t₂ : Set IGame} [Small s₁] [Small s₂] [Small t₁] [Small t₂] :
    !{s₁ | t₁} = !{s₂ | t₂} ↔ s₁ = s₂ ∧ t₁ = t₂ := by
  simp

/-- A (proper) subposition is any game reachable a nonempty sequence of
(not necessarily alternating) left and right moves. -/
def Subposition : IGame → IGame → Prop :=
  Relation.TransGen fun x y => x ∈ ⋃ p, y.moves p

@[aesop unsafe apply 50%]
theorem Subposition.of_mem_moves {p} {x y : IGame} (h : x ∈ y.moves p) : Subposition x y :=
  Relation.TransGen.single (Set.mem_iUnion_of_mem p h)

theorem Subposition.trans {x y z : IGame} (h₁ : Subposition x y) (h₂ : Subposition y z) :
    Subposition x z :=
  Relation.TransGen.trans h₁ h₂

instance : IsTrans _ Subposition := inferInstanceAs (IsTrans _ (Relation.TransGen _))

/-- The set of games reachable from a given game is small. -/
instance small_setOf_subposition (x : IGame.{u_inline_4}) :
    Small.{u_inline_4} {y | Subposition y x} :=
  small_transGen' _ x

/-- A variant of `small_setOf_subposition` in simp-normal form -/
instance small_subtype_subposition (x : IGame.{u_inline_4}) :
    Small.{u_inline_4} {y // Subposition y x} :=
  small_transGen' _ x

theorem subposition_wf : WellFounded Subposition := by
  refine ⟨fun x => Acc.transGen ?_⟩
  apply QPF.Fix.ind
  unfold moves
  rintro _ ⟨⟨st, hst⟩, rfl⟩
  constructor
  rintro y hy
  rw [QPF.Fix.dest_mk, mem_iUnion] at hy
  obtain ⟨_, ⟨_, h⟩, _, rfl⟩ := hy
  exact h

-- We make no use of `IGame`'s definition from a `QPF` after this point.
attribute [irreducible] IGame

instance : IsWellFounded _ Subposition := ⟨subposition_wf⟩
instance : WellFoundedRelation IGame := ⟨Subposition, instIsWellFoundedSubposition.wf⟩

theorem Subposition.irrefl (x : IGame) : ¬Subposition x x := _root_.irrefl x

theorem self_notMem_moves (p : Player) (x : IGame) : x ∉ x.moves p :=
  fun hx ↦ Subposition.irrefl x (.of_mem_moves hx)

/-- `WSubposition x y` means that `x` is reachable from `y` by a sequence of moves.
It is the non-strict version of `Subposition`. -/
def WSubposition (x y : IGame) : Prop := x = y ∨ Subposition x y

theorem wsubposition_iff_eq_or_subposition {x y : IGame} :
    WSubposition x y ↔ x = y ∨ Subposition x y := .rfl

theorem subposition_iff_exists {x y : IGame} : Subposition x y ↔
    ∃ p, ∃ z ∈ y.moves p, WSubposition x z := by
  unfold WSubposition Subposition
  rw [Relation.transGen_iff_exists]
  simp_rw [mem_iUnion, ← exists_and_right, and_or_left]
  exact exists_comm

/-- The set of games reachable from a given game is small. -/
instance small_setOf_wsubposition (x : IGame.{u_inline_4}) :
    Small.{u_inline_4} {y | WSubposition y x} :=
  small_insert x {y | Subposition y x}

/-- A variant of `small_setOf_wsubposition` in simp-normal form -/
instance small_subtype_wsubposition (x : IGame.{u_inline_4}) :
    Small.{u_inline_4} {y // WSubposition y x} :=
  small_insert x {y | Subposition y x}

@[simp, refl] theorem WSubposition.refl (x : IGame) : WSubposition x x := .inl rfl
theorem WSubposition.rfl {x : IGame} : WSubposition x x := .refl x
theorem wsubposition_of_eq {x y : IGame} (hxy : x = y) : WSubposition x y := hxy ▸ .rfl

theorem wsubposition_of_subposition {x y : IGame} (h : Subposition x y) :
    WSubposition x y := .inr h

alias Subposition.wsubposition := wsubposition_of_subposition

theorem subposition_of_wsubposition_of_subposition {x y z : IGame}
    (hxy : WSubposition x y) (hyz : Subposition y z) : Subposition x z := by
  obtain rfl | hxy := hxy
  · exact hyz
  · exact hxy.trans hyz

theorem subposition_of_subposition_of_wsubposition {x y z : IGame}
    (hxy : Subposition x y) (hyz : WSubposition y z) : Subposition x z := by
  obtain rfl | hyz := hyz
  · exact hxy
  · exact hxy.trans hyz

alias WSubposition.trans_subposition := subposition_of_wsubposition_of_subposition
alias Subposition.trans_wsubposition' := subposition_of_wsubposition_of_subposition
alias Subposition.trans_wsubposition := subposition_of_subposition_of_wsubposition
alias WSubposition.trans_subposition' := subposition_of_subposition_of_wsubposition

@[trans] theorem wsubposition_trans {x y z : IGame}
    (hxy : WSubposition x y) (hyz : WSubposition y z) : WSubposition x z := by
  obtain rfl | hyz := hyz
  · exact hxy
  · exact (hxy.trans_subposition hyz).wsubposition

alias WSubposition.trans := wsubposition_trans

instance : Trans Subposition Subposition Subposition := ⟨Subposition.trans⟩
instance : Trans WSubposition Subposition Subposition := ⟨WSubposition.trans_subposition⟩
instance : Trans Subposition WSubposition Subposition := ⟨Subposition.trans_wsubposition⟩
instance : Trans WSubposition WSubposition WSubposition := ⟨WSubposition.trans⟩

theorem not_subposition_of_wsubposition {x y : IGame} (hxy : WSubposition x y) :
    ¬Subposition y x := fun hyx => Subposition.irrefl x (hxy.trans_subposition hyx)

theorem not_wsubposition_of_subposition {x y : IGame} (hxy : Subposition x y) :
    ¬WSubposition y x := fun hyx => Subposition.irrefl x (hxy.trans_wsubposition hyx)

alias WSubposition.not_subposition := not_subposition_of_wsubposition
alias Subposition.not_wsubposition := not_wsubposition_of_subposition

theorem wsubposition_antisymm {x y : IGame}
    (hxy : WSubposition x y) (hyx : WSubposition y x) : x = y :=
  hxy.resolve_right fun h => Subposition.irrefl x (h.trans_wsubposition hyx)

alias WSubposition.antisymm := wsubposition_antisymm

theorem wsubposition_antisymm_iff {x y : IGame} : x = y ↔ WSubposition x y ∧ WSubposition y x :=
  ⟨fun h => h ▸ ⟨.rfl, .rfl⟩, fun h => h.1.antisymm h.2⟩

theorem subposition_of_wsubposition_of_ne {x y : IGame} (hw : WSubposition x y) (hne : x ≠ y) :
    Subposition x y := hw.resolve_left hne

theorem subposition_of_wsubposition_not_wsubposition {x y : IGame}
    (hxy : WSubposition x y) (hyx : ¬WSubposition y x) : Subposition x y :=
  hxy.resolve_left fun h => hyx (wsubposition_of_eq h.symm)

theorem subposition_iff_wsubposition_not_wsubposition {x y : IGame} :
    Subposition x y ↔ WSubposition x y ∧ ¬WSubposition y x :=
  ⟨fun hxy => ⟨hxy.wsubposition, hxy.not_wsubposition⟩,
    fun h => subposition_of_wsubposition_not_wsubposition h.1 h.2⟩

theorem WSubposition.of_mem_moves {p : Player} {x y : IGame} (hxy : x ∈ y.moves p) :
    WSubposition x y := (Subposition.of_mem_moves hxy).wsubposition

/-- **Conway recursion**: build data for a game by recursively building it on its
left and right sets. You rarely need to use this explicitly, as the termination checker will handle
things for you.

See `ofSetsRecOn` for an alternate form. -/
@[elab_as_elim]
def moveRecOn {motive : IGame → Sort*} (x)
    (ind : Π x, (Π p, Π y ∈ x.moves p, motive y) → motive x) :
    motive x :=
  subposition_wf.recursion x fun x IH ↦ ind x (fun _ _ h ↦ IH _ (.of_mem_moves h))

theorem moveRecOn_eq {motive : IGame → Sort*} (x)
    (ind : Π x, (Π p, Π y ∈ x.moves p, motive y) → motive x) :
    moveRecOn x ind = ind x (fun _ y _ ↦ moveRecOn y ind) :=
  subposition_wf.fix_eq ..

/-- **Conway recursion**: build data for a game by recursively building it on its
left and right sets. You rarely need to use this explicitly, as the termination checker will handle
things for you.

See `moveRecOn` for an alternate form. -/
@[elab_as_elim]
def ofSetsRecOn {motive : IGame.{u_inline_4} → Sort*} (x)
    (ofSets : Π (s t : Set IGame) [Small s] [Small t],
      (Π x ∈ s, motive x) → (Π x ∈ t, motive x) → motive !{s | t}) :
    motive x :=
  cast (by simp) <| moveRecOn (motive := fun x ↦ motive !{xᴸ | xᴿ}) x
    fun x IH ↦ ofSets _ _
      (fun y hy ↦ cast (by simp) (IH left y hy)) (fun y hy ↦ cast (by simp) (IH right y hy))

@[simp]
theorem ofSetsRecOn_ofSets {motive : IGame.{u_inline_4} → Sort*}
    (s t : Set IGame) [Small.{u_inline_4} s] [Small.{u_inline_4} t]
    (ofSets : Π (s t : Set IGame) [Small s] [Small t],
      (Π x ∈ s, motive x) → (Π x ∈ t, motive x) → motive !{s | t}) :
    ofSetsRecOn !{s | t} ofSets =
      ofSets _ _ (fun y _ ↦ ofSetsRecOn y ofSets) (fun y _ ↦ ofSetsRecOn y ofSets) := by
  rw [ofSetsRecOn, cast_eq_iff_heq, moveRecOn_eq]
  simp_rw [ofSetsRecOn]
  congr! <;> simp_all

/-- Discharges proof obligations of the form `⊢ Subposition ..` arising in termination proofs
of definitions using well-founded recursion on `IGame`. -/
macro "igame_wf" config:Lean.Parser.Tactic.optConfig : tactic =>
  `(tactic| all_goals solve_by_elim $config
    [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
    Subposition.of_mem_moves, Subposition.trans, Subtype.prop] )

/-! ### Basic games -/

/-- The game `0 = !{∅ | ∅}`. -/
instance : Zero IGame := ⟨!{fun _ ↦ ∅}⟩

theorem zero_def : (0 : IGame) = !{fun _ ↦ ∅} := rfl

@[simp] theorem moves_zero (p : Player) : moves p 0 = ∅ := moves_ofSets ..

instance : Inhabited IGame := ⟨0⟩

/-- The game `1 = !{{0} | ∅}`. -/
instance : One IGame := ⟨!{{0} | ∅}⟩

theorem one_def : (1 : IGame) = !{{0} | ∅} := rfl

@[simp] theorem leftMoves_one : 1ᴸ = {0} := leftMoves_ofSets ..
@[simp] theorem rightMoves_one : 1ᴿ = ∅ := rightMoves_ofSets ..

/-! ### Order relations -/

/-- The less or equal relation on games.

If `0 ≤ x`, then Left can win `x` as the second player. `x ≤ y` means that `0 ≤ y - x`. -/
@[no_expose]
instance : LE IGame where
  le := Sym2.GameAdd.recursion subposition_wf fun x y le ↦
    (∀ z (h : z ∈ xᴸ), ¬le y z (Sym2.GameAdd.snd_fst (.of_mem_moves h))) ∧
    (∀ z (h : z ∈ yᴿ), ¬le z x (Sym2.GameAdd.fst_snd (.of_mem_moves h)))

/-- The less or fuzzy relation on games. `x ⧏ y` is notation for `¬ y ≤ x`.

If `0 ⧏ x`, then Left can win `x` as the first player. `x ⧏ y` means that `0 ⧏ y - x`. -/
notation:50 x:50 " ⧏ " y:50 => ¬ y ≤ x
recommended_spelling "lf" for "⧏" in [«term_⧏_»]

/-- Definition of `x ≤ y` on games, in terms of `⧏`. -/
theorem le_iff_forall_lf {x y : IGame} :
    x ≤ y ↔ (∀ z ∈ xᴸ, z ⧏ y) ∧ (∀ z ∈ yᴿ, x ⧏ z) :=
  propext_iff.1 <| Sym2.GameAdd.recursion_eq ..

/-- Definition of `x ⧏ y` on games, in terms of `≤`. -/
theorem lf_iff_exists_le {x y : IGame} :
    x ⧏ y ↔ (∃ z ∈ yᴸ, x ≤ z) ∨ (∃ z ∈ xᴿ, z ≤ y) := by
  simpa [not_and_or, -not_and] using le_iff_forall_lf.not

/-- The definition of `0 ≤ x` on games, in terms of `0 ⧏`. -/
theorem zero_le {x : IGame} : 0 ≤ x ↔ ∀ y ∈ xᴿ, 0 ⧏ y := by
  rw [le_iff_forall_lf]; simp

/-- The definition of `x ≤ 0` on games, in terms of `⧏ 0`. -/
theorem le_zero {x : IGame} : x ≤ 0 ↔ ∀ y ∈ xᴸ, y ⧏ 0 := by
  rw [le_iff_forall_lf]; simp

/-- The definition of `0 ⧏ x` on games, in terms of `0 ≤`. -/
theorem zero_lf {x : IGame} : 0 ⧏ x ↔ ∃ y ∈ xᴸ, 0 ≤ y := by
  rw [lf_iff_exists_le]; simp

/-- The definition of `x ⧏ 0` on games, in terms of `≤ 0`. -/
theorem lf_zero {x : IGame} : x ⧏ 0 ↔ ∃ y ∈ xᴿ, y ≤ 0 := by
  rw [lf_iff_exists_le]; simp

/-- The definition of `x ≤ y` on games, in terms of `≤` two moves later.

Note that it's often more convenient to use `le_iff_forall_lf`, which only unfolds the definition by
one step. -/
theorem le_def {x y : IGame} : x ≤ y ↔
    (∀ a ∈ xᴸ, (∃ b ∈ yᴸ, a ≤ b) ∨ (∃ b ∈ aᴿ, b ≤ y)) ∧
    (∀ a ∈ yᴿ, (∃ b ∈ aᴸ, x ≤ b) ∨ (∃ b ∈ xᴿ, b ≤ a)) := by
  rw [le_iff_forall_lf]
  congr! 2 <;> rw [lf_iff_exists_le]

/-- The definition of `x ⧏ y` on games, in terms of `⧏` two moves later.

Note that it's often more convenient to use `lf_iff_exists_le`, which only unfolds the definition by
one step. -/
theorem lf_def {x y : IGame} : x ⧏ y ↔
    (∃ a ∈ yᴸ, (∀ b ∈ xᴸ, b ⧏ a) ∧ (∀ b ∈ aᴿ, x ⧏ b)) ∨
    (∃ a ∈ xᴿ, (∀ b ∈ aᴸ, b ⧏ y) ∧ (∀ b ∈ yᴿ, a ⧏ b)) := by
  rw [lf_iff_exists_le]
  congr! <;> rw [le_iff_forall_lf]

theorem left_lf_of_le {x y z : IGame} (h : x ≤ y) (h' : z ∈ xᴸ) : z ⧏ y :=
  (le_iff_forall_lf.1 h).1 z h'

theorem lf_right_of_le {x y z : IGame} (h : x ≤ y) (h' : z ∈ yᴿ) : x ⧏ z :=
  (le_iff_forall_lf.1 h).2 z h'

theorem lf_of_le_left {x y z : IGame} (h : x ≤ z) (h' : z ∈ yᴸ) : x ⧏ y :=
  lf_iff_exists_le.2 <| Or.inl ⟨z, h', h⟩

theorem lf_of_right_le {x y z : IGame} (h : z ≤ y) (h' : z ∈ xᴿ) : x ⧏ y :=
  lf_iff_exists_le.2 <| Or.inr ⟨z, h', h⟩

private theorem le_rfl' {x : IGame} : x ≤ x := by
  rw [le_iff_forall_lf]
  constructor <;> intro y hy
  exacts [lf_of_le_left le_rfl' hy, lf_of_right_le le_rfl' hy]
termination_by x
decreasing_by igame_wf

private theorem le_trans' {x y z : IGame} (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z := by
  rw [le_iff_forall_lf]
  constructor <;> intro a ha h₃
  exacts [left_lf_of_le h₁ ha (le_trans' h₂ h₃), lf_right_of_le h₂ ha (le_trans' h₃ h₁)]
termination_by subposition_wf.cutExpand.wrap {x, y, z}
decreasing_by
  on_goal 1 => convert! Relation.cutExpand_add_single {y, z} (Subposition.of_mem_moves ha)
  on_goal 2 => convert Relation.cutExpand_single_add (Subposition.of_mem_moves ha) {x, y}
  all_goals simp [← Multiset.singleton_add, add_comm, add_assoc, WellFounded.wrap]

instance : Preorder IGame where
  le_refl _ := private le_rfl'
  le_trans x y z := private le_trans'

theorem left_lf {x y : IGame} (h : y ∈ xᴸ) : y ⧏ x :=
  lf_of_le_left le_rfl h

theorem lf_right {x y : IGame} (h : y ∈ xᴿ) : x ⧏ y :=
  lf_of_right_le le_rfl h

theorem le_of_forall_moves_right_lf {x y : IGame}
    (hx : ∀ z ∈ yᴿ, x ⧏ z) (hl : ∀ z ∈ xᴸ, ∃ w ∈ yᴸ, z ≤ w) : x ≤ y := by
  refine le_iff_forall_lf.2 ⟨fun z hz ↦ ?_, hx⟩
  obtain ⟨w, hw, hw'⟩ := hl z hz
  exact mt hw'.trans' (left_lf hw)

theorem le_of_forall_moves_left_lf {x y : IGame}
    (hx : ∀ z ∈ yᴸ, z ⧏ x) (hr : ∀ z ∈ xᴿ, ∃ w ∈ yᴿ, w ≤ z) : y ≤ x := by
  refine le_iff_forall_lf.2 ⟨hx, fun z hz ↦ ?_⟩
  obtain ⟨w, hw, hw'⟩ := hr z hz
  exact mt hw'.trans (lf_right hw)

/-- The equivalence relation `x ≈ y` means that `x ≤ y` and `y ≤ x`. This is notation for
`AntisymmRel (⬝ ≤ ⬝) x y`. -/
infix:50 " ≈ " => AntisymmRel (· ≤ ·)
recommended_spelling "equiv" for "≈" in [«term_≈_»]

/-- The "fuzzy" relation `x ‖ y` means that `x ⧏ y` and `y ⧏ x`. This is notation for
`IncompRel (⬝ ≤ ⬝) x y`. -/
notation:50 x:50 " ‖ " y:50 => IncompRel (· ≤ ·) x y
recommended_spelling "fuzzy" for "‖" in [«term_‖_»]

open Lean PrettyPrinter Delaborator SubExpr Qq in
/-- Delaborates `AntisymmRel (· ≤ ·) x y` into `x ≈ y`. -/
@[delab app.AntisymmRel]
meta def delabEquiv : Delab := do
  try
    let_expr f@AntisymmRel α r _ _ := ← getExpr | failure
    have u_inline_4 := f.constLevels![0]!
    have α : Q(Type u_inline_4) := α
    have r : Q($α → $α → Prop) := r
    let le ← synthInstanceQ q(LE $α)
    _ ← assertDefEqQ q(($le).le) q($r)
    let x ← withNaryArg 2 delab
    let y ← withNaryArg 3 delab
    let stx : Term ← do
      let info ← Lean.MonadRef.mkInfoFromRefPos
      pure {
        raw := Lean.Syntax.node3 info
          ``ConwayRefinement.Standalone.InlineSurreal.IGame.«term_≈_» x.raw
          (Lean.Syntax.atom info "≈") y.raw
      }
    annotateGoToSyntaxDef stx
  catch _ => failure -- fail over to the default delaborator

open Lean PrettyPrinter Delaborator SubExpr Qq in
/-- Delaborates `IncompRel (· ≤ ·) x y` into `x ‖ y`. -/
@[delab app.IncompRel]
meta def delabFuzzy : Delab := do
  try
    let_expr f@IncompRel α r _ _ := ← getExpr | failure
    have u_inline_4 := f.constLevels![0]!
    have α : Q(Type u_inline_4) := α
    have r : Q($α → $α → Prop) := r
    let le ← synthInstanceQ q(LE $α)
    _ ← assertDefEqQ q(($le).le) q($r)
    let x ← withNaryArg 2 delab
    let y ← withNaryArg 3 delab
    let stx : Term ← do
      let info ← Lean.MonadRef.mkInfoFromRefPos
      pure {
        raw := Lean.Syntax.node3 info
          ``ConwayRefinement.Standalone.InlineSurreal.IGame.«term_‖_» x.raw
          (Lean.Syntax.atom info "‖") y.raw
      }
    annotateGoToSyntaxDef stx
  catch _ => failure -- fail over to the default delaborator

theorem equiv_of_forall_lf {x y : IGame}
    (hl₁ : ∀ a ∈ xᴸ, a ⧏ y) (hr₁ : ∀ a ∈ xᴿ, y ⧏ a)
    (hl₂ : ∀ b ∈ yᴸ, b ⧏ x) (hr₂ : ∀ b ∈ yᴿ, x ⧏ b) : x ≈ y := by
  constructor <;> refine le_iff_forall_lf.2 ⟨?_, ?_⟩ <;> assumption

theorem equiv_of_exists_le {x y : IGame}
    (hl₁ : ∀ a ∈ xᴸ, ∃ b ∈ yᴸ, a ≤ b) (hr₁ : ∀ a ∈ xᴿ, ∃ b ∈ yᴿ, b ≤ a)
    (hl₂ : ∀ b ∈ yᴸ, ∃ a ∈ xᴸ, b ≤ a) (hr₂ : ∀ b ∈ yᴿ, ∃ a ∈ xᴿ, a ≤ b) : x ≈ y := by
  apply equiv_of_forall_lf <;> simp +contextual [hl₁, hl₂, hr₁, hr₂, lf_iff_exists_le]

theorem equiv_of_exists {x y : IGame}
    (hl₁ : ∀ a ∈ xᴸ, ∃ b ∈ yᴸ, a ≈ b) (hr₁ : ∀ a ∈ xᴿ, ∃ b ∈ yᴿ, a ≈ b)
    (hl₂ : ∀ b ∈ yᴸ, ∃ a ∈ xᴸ, a ≈ b) (hr₂ : ∀ b ∈ yᴿ, ∃ a ∈ xᴿ, a ≈ b) : x ≈ y := by
  apply equiv_of_exists_le <;> grind [AntisymmRel]

@[simp]
protected theorem zero_lt_one : (0 : IGame) < 1 := by
  rw [lt_iff_le_not_ge, le_iff_forall_lf, le_iff_forall_lf]
  simp

instance : ZeroLEOneClass IGame where
  zero_le_one := IGame.zero_lt_one.le

/-! ### Negation -/

private def neg' (x : IGame) : IGame :=
  !{range fun y : xᴿ ↦ neg' y.1 | range fun y : xᴸ ↦ neg' y.1}
termination_by x
decreasing_by igame_wf

#adaptation_note /-- noncomputable is now needed -/ in
/-- The negative of a game is defined by `-!{s | t} = !{-t | -s}`. -/
@[no_expose]
noncomputable instance : Neg IGame where
  neg := neg'

private theorem neg_ofSets'' (s t : Set IGame) [Small s] [Small t] :
    -!{s | t} = !{Neg.neg '' t | Neg.neg '' s} := by
  change neg' _ = _
  rw [neg']
  simp [Neg.neg, Set.ext_iff]

instance : InvolutiveNeg IGame where
  neg_neg x := by
    refine ofSetsRecOn x ?_
    aesop (add simp [neg_ofSets''])

@[simp]
theorem neg_ofSets (s t : Set IGame) [Small s] [Small t] : -!{s | t} = !{-t | -s} := by
  simp_rw [neg_ofSets'', Set.image_neg_eq_neg]

theorem neg_ofSets' (st : Player → Set IGame) [Small (st left)] [Small (st right)] :
    -!{st} = !{fun p ↦ -st (-p)} := by
  rw [ofSets_eq_ofSets_cases, ofSets_eq_ofSets_cases fun _ ↦ -_, neg_ofSets]
  rfl

@[simp]
theorem neg_ofSets_const (s : Set IGame) [Small s] :
    -!{fun _ ↦ s} = !{fun _ ↦ -s} := by
  simp [neg_ofSets']

instance : NegZeroClass IGame where
  neg_zero := by simp [zero_def]

theorem neg_eq (x : IGame) : -x = !{-xᴿ | -xᴸ} := by
  rw [← neg_ofSets, ofSets_leftMoves_rightMoves]

theorem neg_eq' (x : IGame) : -x = !{fun p ↦ -x.moves (-p)} := by
  rw [neg_eq, ofSets_eq_ofSets_cases (fun _ ↦ -_)]; rfl

@[simp]
theorem moves_neg (p : Player) (x : IGame) :
    (-x).moves p = -x.moves (-p) := by
  rw [neg_eq', moves_ofSets]


theorem forall_moves_neg {P : IGame → Prop} {p : Player} {x : IGame} :
    (∀ y ∈ (-x).moves p, P y) ↔ (∀ y ∈ x.moves (-p), P (-y)) := by
  simp


theorem exists_moves_neg {P : IGame → Prop} {p : Player} {x : IGame} :
    (∃ y ∈ (-x).moves p, P y) ↔ (∃ y ∈ x.moves (-p), P (-y)) := by
  simp

@[simp]
protected theorem neg_le_neg_iff {x y : IGame} : -x ≤ -y ↔ y ≤ x := by
  induction x, y using Sym2.GameAdd.recursion subposition_wf with | _ x y IH
  rw [le_iff_forall_lf, le_iff_forall_lf, and_comm, forall_moves_neg, forall_moves_neg]
  dsimp
  congr! 3 with z hz z hz
  · rw [IH _ _ (Sym2.GameAdd.fst_snd (.of_mem_moves hz))]
  · rw [IH _ _ (Sym2.GameAdd.snd_fst (.of_mem_moves hz))]

protected theorem neg_le {x y : IGame} : -x ≤ y ↔ -y ≤ x := by
  simpa using @IGame.neg_le_neg_iff x (-y)
protected theorem le_neg {x y : IGame} : x ≤ -y ↔ y ≤ -x := by
  simpa using @IGame.neg_le_neg_iff (-x) y

@[simp]
protected theorem neg_lt_neg_iff {x y : IGame} : -x < -y ↔ y < x := by
  simp [lt_iff_le_not_ge]

protected theorem neg_lt {x y : IGame} : -x < y ↔ -y < x := by
  simpa using @IGame.neg_lt_neg_iff x (-y)
protected theorem lt_neg {x y : IGame} : x < -y ↔ y < -x := by
  simpa using @IGame.neg_lt_neg_iff (-x) y

@[simp]
theorem neg_equiv_neg_iff {x y : IGame} : -x ≈ -y ↔ x ≈ y := by
  simp [AntisymmRel, and_comm]

theorem neg_equiv {x y : IGame} : -x ≈ y ↔ x ≈ -y := by
  simpa using @neg_equiv_neg_iff x (-y)

alias ⟨_, neg_congr⟩ := neg_equiv_neg_iff

@[simp]
theorem neg_fuzzy_neg_iff {x y : IGame} : -x ‖ -y ↔ x ‖ y := by
  simp [IncompRel, and_comm]

theorem neg_fuzzy {x y : IGame} : -x ‖ y ↔ x ‖ -y := by
  simpa using @neg_fuzzy_neg_iff x (-y)

@[simp] theorem neg_le_zero {x : IGame} : -x ≤ 0 ↔ 0 ≤ x := by simpa using @IGame.neg_le x 0
@[simp] theorem zero_le_neg {x : IGame} : 0 ≤ -x ↔ x ≤ 0 := by simpa using @IGame.le_neg 0 x
@[simp] theorem neg_lt_zero {x : IGame} : -x < 0 ↔ 0 < x := by simpa using @IGame.neg_lt x 0
@[simp] theorem zero_lt_neg {x : IGame} : 0 < -x ↔ x < 0 := by simpa using @IGame.lt_neg 0 x

@[simp] theorem neg_equiv_zero {x : IGame} : -x ≈ 0 ↔ x ≈ 0 := by
  simpa using @IGame.neg_equiv_neg_iff x 0
@[simp] theorem zero_equiv_neg {x : IGame} : 0 ≈ -x ↔ 0 ≈ x := by
  simpa using @IGame.neg_equiv_neg_iff 0 x

@[simp] theorem neg_fuzzy_zero {x : IGame} : -x ‖ 0 ↔ x ‖ 0 := by
  simpa using @IGame.neg_fuzzy_neg_iff x 0
@[simp] theorem zero_fuzzy_neg {x : IGame} : 0 ‖ -x ↔ 0 ‖ x := by
  simpa using @IGame.neg_fuzzy_neg_iff 0 x

/-! ### Addition and subtraction -/

private def add' (x y : IGame) : IGame :=
  !{(range fun z : xᴸ ↦ add' z y) ∪ (range fun z : yᴸ ↦ add' x z) |
    (range fun z : xᴿ ↦ add' z y) ∪ (range fun z : yᴿ ↦ add' x z)}
termination_by (x, y)
decreasing_by igame_wf

#adaptation_note /-- noncomputable is now needed -/ in
/-- The sum of `x = !{s₁ | t₁}` and `y = !{s₂ | t₂}` is `!{s₁ + y, x + s₂ | t₁ + y, x + t₂}`. -/
@[no_expose]
noncomputable instance : Add IGame where
  add := add'

theorem add_eq (x y : IGame) : x + y =
    !{(· + y) '' xᴸ ∪ (x + ·) '' yᴸ | (· + y) '' xᴿ ∪ (x + ·) '' yᴿ} := by
  change add' _ _ = _
  rw [add']
  simp [HAdd.hAdd, Add.add, Set.ext_iff]

theorem add_eq' (x y : IGame) : x + y =
    !{fun p ↦ (· + y) '' x.moves p ∪ (x + ·) '' y.moves p} := by
  rw [add_eq, ofSets_eq_ofSets_cases (fun _ ↦ _ ∪ _)]

theorem ofSets_add_ofSets
    (s₁ t₁ s₂ t₂ : Set IGame) [Small s₁] [Small t₁] [Small s₂] [Small t₂] :
    !{s₁ | t₁} + !{s₂ | t₂} =
      !{(· + !{s₂ | t₂}) '' s₁ ∪ (!{s₁ | t₁} + ·) '' s₂ |
        (· + !{s₂ | t₂}) '' t₁ ∪ (!{s₁ | t₁} + ·) '' t₂} := by
  rw [add_eq]
  simp

theorem ofSets_add_ofSets' (st₁ st₂ : Player → Set IGame)
    [Small (st₁ left)] [Small (st₂ left)] [Small (st₁ right)] [Small (st₂ right)] :
    !{st₁} + !{st₂} =
      !{fun p ↦ (· + !{st₂}) '' st₁ p ∪ (!{st₁} + ·) '' st₂ p} := by
  rw [ofSets_eq_ofSets_cases, ofSets_eq_ofSets_cases st₂, ofSets_eq_ofSets_cases (fun _ ↦ _ ∪ _),
    ofSets_add_ofSets]

@[simp]
theorem moves_add (p : Player) (x y : IGame) :
    (x + y).moves p = (· + y) '' x.moves p ∪ (x + ·) '' y.moves p := by
  rw [add_eq', moves_ofSets]

theorem add_left_mem_moves_add {p : Player} {x y : IGame} (h : x ∈ y.moves p) (z : IGame) :
    z + x ∈ (z + y).moves p := by
  rw [moves_add]; right; use x

theorem add_right_mem_moves_add {p : Player} {x y : IGame} (h : x ∈ y.moves p) (z : IGame) :
    x + z ∈ (y + z).moves p := by
  rw [moves_add]; left; use x


theorem forall_moves_add {p : Player} {P : IGame → Prop} {x y : IGame} :
    (∀ a ∈ (x + y).moves p, P a) ↔
      (∀ a ∈ x.moves p, P (a + y)) ∧ (∀ b ∈ y.moves p, P (x + b)) := by
  aesop


theorem exists_moves_add {p : Player} {P : IGame → Prop} {x y : IGame} :
    (∃ a ∈ (x + y).moves p, P a) ↔
      (∃ a ∈ x.moves p, P (a + y)) ∨ (∃ b ∈ y.moves p, P (x + b)) := by
  aesop

@[simp]
theorem add_eq_zero_iff {x y : IGame} : x + y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor <;> simp_all [IGame.ext_iff]

private theorem add_zero' (x : IGame) : x + 0 = x := by
  refine moveRecOn x ?_
  aesop

private theorem add_comm' (x y : IGame) : x + y = y + x := by
  ext
  simp only [moves_add, mem_union, mem_image, or_comm]
  congr! 3 <;>
  · refine and_congr_right_iff.2 fun h ↦ ?_
    rw [add_comm']
termination_by (x, y)
decreasing_by igame_wf

private theorem add_assoc' (x y z : IGame) : x + y + z = x + (y + z) := by
  ext1
  simp only [moves_add, image_union, image_image, union_assoc]
  refine congrArg₂ _ ?_ (congrArg₂ _ ?_ ?_) <;>
  · ext
    congr! 2
    rw [add_assoc']
termination_by (x, y, z)
decreasing_by igame_wf

instance : AddCommMonoid IGame where
  add_zero := private add_zero'
  zero_add _ := private add_comm' .. ▸ add_zero' _
  add_comm := private add_comm'
  add_assoc := private add_assoc'
  nsmul := nsmulRec

/-- The subtraction of `x` and `y` is defined as `x + (-y)`. -/
instance : SubNegMonoid IGame where
  zsmul := zsmulRec

@[simp]
theorem moves_sub (p : Player) (x y : IGame) :
    (x - y).moves p = (· - y) '' x.moves p ∪ (x + ·) '' (-y.moves (-p)) := by
  simp [sub_eq_add_neg]

theorem sub_left_mem_moves_sub {p : Player} {x y : IGame} (h : x ∈ y.moves p) (z : IGame) :
    z - x ∈ (z - y).moves (-p) := by
  apply add_left_mem_moves_add; simpa

theorem sub_left_mem_moves_sub_neg {p : Player} {x y : IGame} (h : x ∈ y.moves (-p)) (z : IGame) :
    z - x ∈ (z - y).moves p := by
  apply add_left_mem_moves_add; simpa

theorem sub_right_mem_moves_sub {p : Player} {x y : IGame} (h : x ∈ y.moves p) (z : IGame) :
    x - z ∈ (y - z).moves p :=
  add_right_mem_moves_add h _

private theorem neg_add' (x y : IGame) : -(x + y) = -x + -y := by
  ext
  simp only [moves_neg, moves_add, union_neg, mem_union, mem_neg, mem_image, exists_neg_mem]
  congr! 3 <;>
  · refine and_congr_right_iff.2 fun _ ↦ ?_
    rw [← neg_inj, neg_add', neg_neg]
termination_by (x, y)
decreasing_by igame_wf

instance : SubtractionCommMonoid IGame where
  neg_neg := neg_neg
  neg_add_rev x y := by rw [neg_add', add_comm]
  neg_eq_of_add := by simp
  add_comm := add_comm

private theorem sub_self_le (x : IGame) : x - x ≤ 0 := by
  rw [le_zero, moves_sub]
  rintro _ (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
  · exact lf_of_right_le (sub_self_le y) (sub_left_mem_moves_sub hy y)
  · apply lf_of_right_le (sub_self_le (-y))
    rw [mem_neg] at hy
    rw [sub_neg_eq_add]
    exact add_right_mem_moves_add hy _
termination_by x
decreasing_by igame_wf

/-- The sum of a game and its negative is equivalent, though not necessarily identical to zero. -/
theorem sub_self_equiv (x : IGame) : x - x ≈ 0 := by
  rw [AntisymmRel, ← neg_le_zero, neg_sub, and_self]
  exact sub_self_le x

/-- The sum of a game and its negative is equivalent, though not necessarily identical to zero. -/
theorem neg_add_equiv (x : IGame) : -x + x ≈ 0 := by
  simpa [add_comm, sub_eq_add_neg] using sub_self_equiv x

private theorem add_le_add_left' {x y : IGame} (h : x ≤ y) (z : IGame) : z + x ≤ z + y := by
  rw [le_iff_forall_lf, moves_add, moves_add]
  refine ⟨?_, ?_⟩ <;> rintro a (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
  · exact lf_of_le_left (add_le_add_left' h a) (add_right_mem_moves_add ha y)
  · obtain (⟨b, hb, hb'⟩ | ⟨b, hb, hb'⟩) := lf_iff_exists_le.1 (left_lf_of_le h ha)
    · exact lf_of_le_left (add_le_add_left' hb' z) (add_left_mem_moves_add hb z)
    · exact lf_of_right_le (add_le_add_left' hb' z) (add_left_mem_moves_add hb z)
  · exact lf_of_right_le (add_le_add_left' h a) (add_right_mem_moves_add ha x)
  · obtain (⟨b, hb, hb'⟩ | ⟨b, hb, hb'⟩) := lf_iff_exists_le.1 (lf_right_of_le h ha)
    · exact lf_of_le_left (add_le_add_left' hb' z) (add_left_mem_moves_add hb z)
    · exact lf_of_right_le (add_le_add_left' hb' z) (add_left_mem_moves_add hb z)
termination_by (x, y, z)
decreasing_by igame_wf (maxDepth := 8)

private theorem add_le_add_right' {x y : IGame} (h : x ≤ y) (z : IGame) : x + z ≤ y + z := by
  simpa [add_comm] using add_le_add_left' h z

instance : AddLeftMono IGame := ⟨fun x _ _ h ↦ add_le_add_left' h x⟩
instance : AddRightMono IGame := ⟨fun x _ _ h ↦ add_le_add_right' h x⟩

instance : AddLeftReflectLE IGame where
  le_of_add_le_add_left {x y} z h := by
    rw [← zero_add y, ← zero_add z]
    apply (add_le_add_left (neg_add_equiv x).ge y).trans
    rw [add_assoc]
    apply (add_le_add_right h (-x)).trans
    rw [← add_assoc]
    exact add_le_add_left (neg_add_equiv x).le z

instance : AddRightReflectLE IGame :=
  addRightReflectLE_of_addLeftReflectLE _

instance : AddLeftStrictMono IGame where
  elim x y z h := by
    apply lt_of_le_not_ge (add_le_add_right h.le x)
    contrapose! h
    exact (le_of_add_le_add_left h).not_gt

instance : AddRightStrictMono IGame :=
  addRightStrictMono_of_addLeftStrictMono _

instance : AddLeftReflectLT IGame where
  elim _ := by simp [lt_iff_le_not_ge]

instance : AddRightReflectLT IGame :=
  addRightReflectLT_of_addLeftReflectLT _

theorem add_congr {a b : IGame} (h₁ : a ≈ b) {c d : IGame} (h₂ : c ≈ d) : a + c ≈ b + d :=
  ⟨add_le_add h₁.1 h₂.1, add_le_add h₁.2 h₂.2⟩

theorem add_congr_left {a b c : IGame} (h : a ≈ b) : a + c ≈ b + c :=
  add_congr h .rfl

theorem add_congr_right {a b c : IGame} (h : a ≈ b) : c + a ≈ c + b :=
  add_congr .rfl h

@[simp]
theorem add_fuzzy_add_iff_left {a b c : IGame} : a + b ‖ a + c ↔ b ‖ c := by
  simp [IncompRel]

@[simp]
theorem add_fuzzy_add_iff_right {a b c : IGame} : b + a ‖ c + a ↔ b ‖ c := by
  simp [IncompRel]

theorem sub_congr {a b : IGame} (h₁ : a ≈ b) {c d : IGame} (h₂ : c ≈ d) : a - c ≈ b - d :=
  add_congr h₁ (neg_congr h₂)

theorem sub_congr_left {a b c : IGame} (h : a ≈ b) : a - c ≈ b - c :=
  sub_congr h .rfl

theorem sub_congr_right {a b c : IGame} (h : a ≈ b) : c - a ≈ c - b :=
  sub_congr .rfl h

/-- We define the `NatCast` instance as `↑0 = 0` and `↑(n + 1) = !{{↑n} | ∅}`.

Note that this is equivalent, but not identical, to the more common definition `↑n = !{Iio n | ∅}`.
For that, use `NatOrdinal.toIGame`. -/
instance : AddCommMonoidWithOne IGame where

/-- This version of the theorem is more convenient for the `game_cmp` tactic. -/
theorem leftMoves_natCast_succ' : ∀ n : ℕ, n.succᴸ = {(n : IGame)}
  | 0 => by simp
  | n + 1 => by
    rw [Nat.cast_succ, moves_add, leftMoves_natCast_succ']
    simp

@[simp 1100] -- This should trigger before `leftMoves_add`.
theorem leftMoves_natCast_succ (n : ℕ) : (n + 1)ᴸ = {(n : IGame)} :=
  leftMoves_natCast_succ' n

@[simp 1100] -- This should trigger before `rightMoves_add`.
theorem rightMoves_natCast : ∀ n : ℕ, nᴿ = ∅
  | 0 => by simp
  | n + 1 => by
    rw [Nat.cast_succ, moves_add, rightMoves_natCast]
    simp

@[simp 1100]
theorem leftMoves_ofNat (n : ℕ) [n.AtLeastTwo] : ofNat(n)ᴸ = {((n - 1 : ℕ) : IGame)} := by
  change nᴸ = _
  rw [← Nat.succ_pred (NeZero.out (n := n)), leftMoves_natCast_succ']
  simp

@[simp 1100]
theorem rightMoves_ofNat (n : ℕ) [n.AtLeastTwo] : ofNat(n)ᴿ = ∅ :=
  rightMoves_natCast n

theorem natCast_succ_eq (n : ℕ) : (n + 1 : IGame) = !{{(n : IGame)} | ∅} := by
  ext p; cases p <;> simp

/-- Every left option of a natural number is equal to a smaller natural number. -/
theorem eq_natCast_of_mem_leftMoves_natCast {n : ℕ} {x : IGame} (hx : x ∈ nᴸ) :
    ∃ m : ℕ, m < n ∧ m = x := by
  cases n with
  | zero => simp at hx
  | succ n =>
    use n
    simp_all

instance : IntCast IGame where
  intCast
  | .ofNat n => n
  | .negSucc n => -(n + 1)

@[simp, norm_cast] theorem intCast_nat (n : ℕ) : ((n : ℤ) : IGame) = n := rfl
@[simp] theorem intCast_ofNat (n : ℕ) : ((ofNat(n) : ℤ) : IGame) = n := rfl
@[simp] theorem intCast_negSucc (n : ℕ) : (Int.negSucc n : IGame) = -(n + 1) := rfl

@[norm_cast] theorem intCast_zero : ((0 : ℤ) : IGame) = 0 := rfl
@[norm_cast] theorem intCast_one : ((1 : ℤ) : IGame) = 1 := by simp

@[simp, norm_cast]
theorem intCast_neg (n : ℤ) : ((-n : ℤ) : IGame) = -(n : IGame) := by
  cases n with
  | ofNat n =>
    cases n with
    | zero => simp
    | succ n => rfl
  | negSucc n => exact (neg_neg _).symm

theorem eq_sub_one_of_mem_leftMoves_intCast {n : ℤ} {x : IGame} (hx : x ∈ nᴸ) :
    x = (n - 1 : ℤ) := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · cases n
    · simp at hx
    · rw [intCast_nat] at hx
      simp_all
  · simp at hx

theorem eq_add_one_of_mem_rightMoves_intCast {n : ℤ} {x : IGame} (hx : x ∈ nᴿ) :
    x = (n + 1 : ℤ) := by
  have : -x ∈ (-n : ℤ)ᴸ := by simpa
  rw [← neg_inj]
  simpa [← IGame.intCast_neg, add_comm, sub_eq_add_neg] using
    eq_sub_one_of_mem_leftMoves_intCast this

/-- Every left option of an integer is equal to a smaller integer. -/
theorem eq_intCast_of_mem_leftMoves_intCast {n : ℤ} {x : IGame} (hx : x ∈ nᴸ) :
    ∃ m : ℤ, m < n ∧ m = x := by
  use n - 1
  simp [eq_sub_one_of_mem_leftMoves_intCast hx]

/-- Every right option of an integer is equal to a larger integer. -/
theorem eq_intCast_of_mem_rightMoves_intCast {n : ℤ} {x : IGame} (hx : x ∈ nᴿ) :
    ∃ m : ℤ, n < m ∧ m = x := by
  use n + 1
  simp [eq_add_one_of_mem_rightMoves_intCast hx]

/-! ### Multiplication -/

attribute [aesop apply unsafe 50%] Prod.Lex.left Prod.Lex.right

private def mul' (x y : IGame) : IGame :=
  !{(range fun a : (xᴸ ×ˢ yᴸ ∪ xᴿ ×ˢ yᴿ :) ↦
    mul' a.1.1 y + mul' x a.1.2 - mul' a.1.1 a.1.2) |
  (range fun a : (xᴸ ×ˢ yᴿ ∪ xᴿ ×ˢ yᴸ :) ↦
    mul' a.1.1 y + mul' x a.1.2 - mul' a.1.1 a.1.2)}
termination_by (x, y)
decreasing_by all_goals aesop

#adaptation_note /-- noncomputable is now needed -/ in
/-- The product of `x = !{s₁ | t₁}` and `y = !{s₂ | t₂}` is
`!{a₁ * y + x * b₁ - a₁ * b₁ | a₂ * y + x * b₂ - a₂ * b₂}`, where `(a₁, b₁) ∈ s₁ ×ˢ s₂ ∪ t₁ ×ˢ t₂`
and `(a₂, b₂) ∈ s₁ ×ˢ t₂ ∪ t₁ ×ˢ s₂`.

Using `IGame.mulOption`, this can alternatively be written as
`x * y = !{mulOption x y a₁ b₁ | mulOption x y a₂ b₂}`. -/
@[no_expose]
noncomputable instance : Mul IGame where
  mul := mul'

/-- The general option of `x * y` looks like `a * y + x * b - a * b`, for `a` and `b` options of
`x` and `y`, respectively. -/
@[pp_nodot]
def mulOption (x y a b : IGame) : IGame :=
  a * y + x * b - a * b

theorem mul_eq (x y : IGame) : x * y =
    !{(fun a ↦ mulOption x y a.1 a.2) '' (xᴸ ×ˢ yᴸ ∪ xᴿ ×ˢ yᴿ) |
    (fun a ↦ mulOption x y a.1 a.2) '' (xᴸ ×ˢ yᴿ ∪ xᴿ ×ˢ yᴸ)} := by
  change mul' _ _ = _
  rw [mul']
  simp [mulOption, HMul.hMul, Mul.mul, Set.ext_iff]

theorem mul_eq' (x y : IGame) : x * y =
    !{fun p ↦ (fun a ↦ mulOption x y a.1 a.2) ''
      (xᴸ ×ˢ y.moves p ∪ xᴿ ×ˢ y.moves (-p))} := by
  rw [mul_eq, ofSets_eq_ofSets_cases (fun _ ↦ _ '' _)]; rfl

theorem ofSets_mul_ofSets (s₁ t₁ s₂ t₂ : Set IGame) [Small s₁] [Small t₁] [Small s₂] [Small t₂] :
    !{s₁ | t₁} * !{s₂ | t₂} =
      !{(fun a ↦ mulOption !{s₁ | t₁} !{s₂ | t₂} a.1 a.2) '' (s₁ ×ˢ s₂ ∪ t₁ ×ˢ t₂) |
      (fun a ↦ mulOption !{s₁ | t₁} !{s₂ | t₂} a.1 a.2) '' (s₁ ×ˢ t₂ ∪ t₁ ×ˢ s₂)} := by
  rw [mul_eq]
  simp

@[simp]
theorem moves_mul (p : Player) (x y : IGame) :
    (x * y).moves p = (fun a ↦ mulOption x y a.1 a.2) ''
      (xᴸ ×ˢ y.moves p ∪ xᴿ ×ˢ y.moves (-p)) := by
  rw [mul_eq', moves_ofSets]

@[simp]
theorem moves_mulOption (p : Player) (x y a b : IGame) :
    (mulOption x y a b).moves p = (a * y + x * b - a * b).moves p :=
  rfl

theorem mulOption_mem_moves_mul {px py : Player} {x y a b : IGame}
    (h₁ : a ∈ x.moves px) (h₂ : b ∈ y.moves py) : mulOption x y a b ∈ (x * y).moves (px * py) := by
  rw [moves_mul]; use (a, b); cases px <;> cases py <;> simp_all


theorem forall_moves_mul {p : Player} {P : IGame → Prop} {x y : IGame} :
    (∀ a ∈ (x * y).moves p, P a) ↔
      (∀ p', ∀ a ∈ x.moves p', ∀ b ∈ y.moves (p' * p), P (mulOption x y a b)) := by
  aesop


theorem exists_moves_mul {p : Player} {P : IGame → Prop} {x y : IGame} :
    (∃ a ∈ (x * y).moves p, P a) ↔
      (∃ p', ∃ a ∈ x.moves p', ∃ b ∈ y.moves (p' * p), P (mulOption x y a b)) := by
  aesop

private theorem zero_mul' (x : IGame) : 0 * x = 0 := by
  ext p; cases p <;> simp

private theorem one_mul' (x : IGame) : 1 * x = x := by
  refine moveRecOn x ?_
  aesop (add simp [mulOption, and_assoc, zero_mul'])

private theorem igameMulComm (x y : IGame) : x * y = y * x := by
  ext p
  simp only [moves_mul, mem_image, mem_prod, mem_union, Prod.exists]
  cases p; all_goals
    dsimp
    simp only [and_comm, or_comm]
    rw [exists_comm]
    congr! 4 with b a
    rw [and_congr_right_iff]
    rintro (⟨_, _⟩ | ⟨_, _⟩) <;>
      rw [mulOption, mulOption, igameMulComm x, igameMulComm _ y, add_comm, igameMulComm a b]
termination_by (x, y)
decreasing_by igame_wf

instance : CommMagma IGame where
  mul_comm := private igameMulComm

instance : MulZeroClass IGame where
  zero_mul := private zero_mul'
  mul_zero x := private igameMulComm .. ▸ zero_mul' x

instance : MulZeroOneClass IGame where
  one_mul := private one_mul'
  mul_one x := private igameMulComm .. ▸ one_mul' x

theorem mulOption_comm (x y a b : IGame) : mulOption x y a b = mulOption y x b a := by
  simp [mulOption, add_comm, mul_comm]

private theorem neg_mul' (x y : IGame) : -x * y = -(x * y) := by
  ext
  simp only [moves_mul, moves_neg, mem_image, mem_union, mem_prod, mem_neg, Prod.exists]
  rw [← (Equiv.neg _).exists_congr_right]
  dsimp only [Player.neg_left, Player.neg_right]
  simp only [Equiv.neg_apply, neg_neg, mulOption, or_comm]
  congr! 4
  rw [and_congr_right_iff]
  rintro (⟨_, _⟩ | ⟨_, _⟩)
  all_goals
    rw [← neg_inj, neg_mul', neg_mul', neg_mul']
    simp [sub_eq_add_neg, add_comm]
termination_by (x, y)
decreasing_by igame_wf

instance : HasDistribNeg IGame where
  neg_mul := private neg_mul'
  mul_neg _ _ := by rw [mul_comm, neg_mul', mul_comm]

theorem mulOption_neg_left (x y a b : IGame) : mulOption (-x) y a b = -mulOption x y (-a) b := by
  simp [mulOption, sub_eq_neg_add, add_comm]

theorem mulOption_neg_right (x y a b : IGame) : mulOption x (-y) a b = -mulOption x y a (-b) := by
  simp [mulOption, sub_eq_neg_add, add_comm]

theorem mulOption_neg (x y a b : IGame) : mulOption (-x) (-y) a b = mulOption x y (-a) (-b) := by
  simp [mulOption, sub_eq_neg_add, add_comm]

@[simp]
theorem mulOption_zero_left (x y a : IGame) : mulOption x y 0 a = x * a := by
  simp [mulOption]

@[simp]
theorem mulOption_zero_right (x y a : IGame) : mulOption x y a 0 = a * y := by
  simp [mulOption]

/-! Distributivity and associativity only hold up to equivalence; we prove this in
`CombinatorialGames.Game.Basic`. -/


end IGame
end

/-! ## Inlined from `CombinatorialGames.Tactic.AddInstances` -/

/-!
# Eagerly add instances

Many definitions in game theory are hereditary. For instance, all options of a `Numeric` game are
`Numeric`, all options of an `Impartial` game are `Impartial`, etc.

The definition `addInstances` provides a tactic which will eagerly apply all passed functions to all
of the hypotheses, creating new ones in the process. The intended usage of this is to, for instance,
apply `Numeric.of_mem_moves` to all hypotheses, and thus build all possible `Numeric` instances.
-/

open Lean Meta Elab Tactic

meta def instances (constants : Array Name) (goal : MVarId) : MetaM (Option MVarId) :=
  goal.withContext do
    let mut goal := goal
    for h in ← getLCtx do
      if h.isImplementationDetail then continue
      ⟨_, goal⟩ ← goal.assertHypotheses =<< constants.filterMapM fun c => do
        let hc ← try mkAppM c #[h.toExpr] catch _ => return none
        return some {
          userName := ← mkFreshUserName `inst
          type := ← inferType hc
          value := hc
        }
    return goal

/-- A tactic that eagerly adds instances by applying the functions in `constants` to every
hypothesis. -/
public meta def addInstances (constants : Array Name) : TacticM Unit :=
  liftMetaTactic1 (instances constants)

/-! ## Inlined from `CombinatorialGames.Game.Classes` -/

/-!
# Classes of games

This file collects multiple basic classes of games, so as to make them available on most files. We
develop their theory elsewhere.

## Dicotic games

A game is dicotic when every non-zero subposition has both left and right moves. The Lawnmower
theorem (proven in `CombinatorialGames.Game.Small`) shows that every dicotic game is small.

## Impartial games

We define an impartial game as one where every subposition is equivalent to its negative. This is a
weaker definition than that found in the literature (which requires equality, rather than
equivalence), but this is still strong enough to prove the Sprague--Grundy theorem, as well as
closure under the basic arithmetic operations of multiplication and division.

## Numeric games

A game is `Numeric` if all the Left options are strictly smaller than all the Right options, and all
those options are themselves numeric. In terms of combinatorial games, the numeric games have
"frozen"; you can only make your position worse by playing, and Left is some definite "number" of
moves ahead (or behind) Right.

## Short games

A combinatorial game is `Short` if it has only finitely many subpositions. In particular, this means
there is a finite set of moves at every point.

The `game_cmp` tactic supplies computation for short combinatorial games.
-/

universe u_inline_6

@[expose] public section

namespace IGame

/-! ### Numeric games -/

/-- A game `!{s | t}` is numeric if everything in `s` is less than everything in `t`, and all the
elements of these sets are also numeric.

The `Surreal` numbers are built as the quotient of numeric games under equivalence. -/
@[mk_iff numeric_def']
class inductive Numeric : IGame → Prop where
  | mk {x : IGame} : (∀ y ∈ xᴸ, ∀ z ∈ xᴿ, y < z) → (∀ p, ∀ y ∈ x.moves p, Numeric y) → Numeric x

theorem numeric_def {x : IGame} : Numeric x ↔
    (∀ y ∈ xᴸ, ∀ z ∈ xᴿ, y < z) ∧ (∀ p, ∀ y ∈ x.moves p, Numeric y) :=
  numeric_def' x

namespace Numeric
variable {x y z : IGame}

theorem left_lt_right [h : Numeric x] (hy : y ∈ xᴸ) (hz : z ∈ xᴿ) : y < z :=
  (numeric_def.1 h).1 y hy z hz

protected theorem of_mem_moves {p : Player} [h : Numeric x] (hy : y ∈ x.moves p) : Numeric y :=
  (numeric_def.1 h).2 p y hy

/-- `numeric` eagerly adds all possible `Numeric` hypotheses. -/
elab "numeric" : tactic =>
  addInstances <| .mk [`ConwayRefinement.Standalone.InlineSurreal.IGame.Numeric.of_mem_moves]

protected theorem subposition [Numeric x] (h : Subposition y x) : Numeric y := by
  induction x using IGame.moveRecOn generalizing ‹x.Numeric› with | ind x ih
  obtain ⟨p, z, hz, hy⟩ := subposition_iff_exists.1 h
  obtain rfl | hy := wsubposition_iff_eq_or_subposition.1 hy
  · exact .of_mem_moves hz
  · exact @ih p z hz (.of_mem_moves hz) hy

@[simp]
protected instance zero : Numeric 0 := by
  rw [numeric_def]; simp

@[simp]
protected instance one : Numeric 1 := by
  rw [numeric_def]; simp

protected instance subtype (x : Subtype Numeric) : Numeric x.1 := x.2
protected instance moves {x : IGame} [Numeric x] {p : Player} (y : x.moves p) : Numeric y :=
  .of_mem_moves y.2

protected theorem le_of_not_le {x y : IGame} [Numeric x] [Numeric y] : ¬ x ≤ y → y ≤ x := by
  rw [lf_iff_exists_le, le_iff_forall_lf]
  rintro (⟨z, hz, h⟩ | ⟨z, hz, h⟩) <;> constructor <;> intro a ha h'
  · numeric
    exact left_lf_of_le h' hz (Numeric.le_of_not_le (left_lf_of_le h ha))
  · exact (left_lt_right hz ha).not_ge (h'.trans h)
  · exact (left_lt_right ha hz).not_ge (h.trans h')
  · numeric
    exact lf_right_of_le h' hz (Numeric.le_of_not_le (lf_right_of_le h ha))
termination_by x
decreasing_by igame_wf

protected theorem le_total (x y : IGame) [Numeric x] [Numeric y] : x ≤ y ∨ y ≤ x := by
  rw [or_iff_not_imp_left]
  exact Numeric.le_of_not_le

protected theorem lt_of_not_ge [Numeric x] [Numeric y] (h : ¬ x ≤ y) : y < x :=
  (Numeric.le_of_not_le h).lt_of_not_ge h

@[simp]
protected theorem not_le [Numeric x] [Numeric y] : ¬ x ≤ y ↔ y < x :=
  ⟨Numeric.lt_of_not_ge, not_le_of_gt⟩

@[simp]
protected theorem not_lt [Numeric x] [Numeric y] : ¬ x < y ↔ y ≤ x :=
  not_iff_comm.1 Numeric.not_le

protected theorem le_or_gt (x y : IGame) [Numeric x] [Numeric y] : x ≤ y ∨ y < x := by
  rw [← Numeric.not_le]
  exact em _

protected theorem lt_or_ge (x y : IGame) [Numeric x] [Numeric y] : x < y ∨ y ≤ x := by
  rw [← Numeric.not_lt]
  exact em _

theorem not_fuzzy (x y : IGame) [Numeric x] [Numeric y] : ¬ x ‖ y := by
  simpa [not_incompRel_iff_symmGen, Relation.SymmGen] using Numeric.le_total x y

theorem lt_or_equiv_or_gt (x y : IGame) [Numeric x] [Numeric y] : x < y ∨ x ≈ y ∨ y < x := by
  simp_rw [← Numeric.not_le]; tauto

/-- To prove a game is numeric, it suffices to show the left options are less or fuzzy
to the right options. -/
theorem mk_of_lf (h₁ : ∀ y ∈ xᴸ, ∀ z ∈ xᴿ, y ⧏ z) (h₂ : ∀ p, ∀ y ∈ x.moves p, Numeric y) :
    Numeric x :=
  mk (fun y hy z hz ↦ (@Numeric.not_le z y (h₂ _ z hz) (h₂ _ y hy)).1 (h₁ y hy z hz)) h₂

theorem le_iff_forall_lt [Numeric x] [Numeric y] :
    x ≤ y ↔ (∀ z ∈ xᴸ, z < y) ∧ (∀ z ∈ yᴿ, x < z) := by
  rw [le_iff_forall_lf]
  congr! with z hz z hz <;> numeric <;> rw [Numeric.not_le]

theorem lt_iff_exists_le [Numeric x] [Numeric y] :
    x < y ↔ (∃ z ∈ yᴸ, x ≤ z) ∨ (∃ z ∈ xᴿ, z ≤ y) := by
  rw [← Numeric.not_le, lf_iff_exists_le]

theorem left_lt [Numeric x] (h : y ∈ xᴸ) : y < x := by
  numeric; simpa using left_lf h

theorem lt_right [Numeric x] (h : y ∈ xᴿ) : x < y := by
  numeric; simpa using lf_right h

protected instance neg (x : IGame) [Numeric x] : Numeric (-x) := by
  refine mk (fun y hy z hz ↦ ?_) ?_
  · rw [← IGame.neg_lt_neg_iff]
    apply @left_lt_right x <;> simp_all
  · simp_rw [forall_moves_neg]
    intro p y hy
    numeric
    simpa using Numeric.neg y
termination_by x
decreasing_by igame_wf

@[simp]
theorem neg_iff {x : IGame} : Numeric (-x) ↔ Numeric x :=
  ⟨fun _ ↦ by simpa using Numeric.neg (-x), fun _ ↦ Numeric.neg x⟩

protected instance add (x y : IGame) [Numeric x] [Numeric y] : Numeric (x + y) := by
  apply mk <;> simp only [moves_add, Set.mem_union, Set.mem_image]
  · rintro _ (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) _ (⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩)
    any_goals simpa using left_lt_right ha hb
    all_goals
      trans (x + y)
      · simpa using left_lt ha
      · simpa using lt_right hb
  · rintro p _ (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    all_goals numeric; exact Numeric.add ..
termination_by (x, y)
decreasing_by igame_wf

protected instance sub (x y : IGame) [Numeric x] [Numeric y] : Numeric (x - y) :=
  inferInstanceAs (Numeric (x + -y))

protected instance natCast : ∀ n : ℕ, Numeric n
  | 0 => inferInstanceAs (Numeric 0)
  | n + 1 => have := Numeric.natCast n; inferInstanceAs (Numeric (n + 1))

protected instance ofNat (n : ℕ) [n.AtLeastTwo] : Numeric ofNat(n) :=
  inferInstanceAs (Numeric n)

protected instance intCast : ∀ n : ℤ, Numeric n
  | .ofNat n => inferInstanceAs (Numeric n)
  | .negSucc n => inferInstanceAs (Numeric (-(n + 1)))

end Numeric


end IGame

/-! ## Inlined from `CombinatorialGames.Game.Basic` -/

/-!
# Combinatorial games

In this file we construct the quotient of games `IGame` under equivalence, and prove that it forms
an `OrderedAddCommGroup`. We take advantage of this structure to prove two particularly tedious
theorems on `IGame`, namely `IGame.mul_add_equiv` and `IGame.mul_assoc_equiv`.

It might be tempting to write `mk (x * y)` as `mk x * mk y`, but the latter is not well-defined, as
there exist `x₁ ≈ x₂` and `y₁ ≈ y₂` with `x₁ * y₁ ≉ x₂ * y₂`. See
`CombinatorialGames.Counterexamples.Multiplication` for a proof.
-/

universe u_inline_7

@[expose] public noncomputable section

open IGame Set Pointwise

/-- Games up to equivalence.

If `x` and `y` are combinatorial games (`IGame`), we say that `x ≈ y` when both `x ≤ y` and `y ≤ x`.
Broadly, this means neither player has a preference in playing either game, as a component of a
larger game. This is the standard meaning of `x = y` in the literature, though it is not a strict
equality, e.g. `{0, 1 | 0}` and `{1 | 0}` are equivalent, but not identical as the former has an
extra move for Left.

In particular, note that a `Game` has no well-defined notion of left and right options. This means
you should prefer `IGame` when analyzing specific games. -/
def Game : Type (u_inline_7 + 1) :=
  Antisymmetrization IGame (· ≤ ·)

namespace Game

/-- The quotient map from `IGame` into `Game`. -/
def mk (x : IGame) : Game := Quotient.mk _ x
theorem mk_eq_mk {x y : IGame} : mk x = mk y ↔ x ≈ y := Quotient.eq

alias ⟨_, mk_eq⟩ := mk_eq_mk

@[cases_eliminator]
theorem ind {motive : Game → Prop} (mk : ∀ y, motive (mk y)) (x : Game) : motive x :=
  Quotient.ind mk x

/-- Choose an element of the equivalence class using the axiom of choice. -/
@[no_expose] def out (x : Game) : IGame := Quotient.out x
@[simp] theorem out_eq (x : Game) : mk x.out = x := Quotient.out_eq x

theorem mk_out_equiv (x : IGame) : (mk x).out ≈ x := Quotient.mk_out (s := AntisymmRel.setoid ..) x
theorem equiv_mk_out (x : IGame) : x ≈ (mk x).out := (mk_out_equiv x).symm

/-- Construct a `Game` from its left and right sets.

Note that although this function is well-defined, this function isn't injective, nor do equivalence
classes in `Game` have a canonical representative. -/
instance : OfSets Game.{u_inline_7} fun _ ↦ True where
  ofSets st _ := mk !{fun p ↦ out '' (st p)}

theorem mk_ofSets' (st : Player → Set IGame.{u_inline_7})
    [Small.{u_inline_7} (st left)] [Small.{u_inline_7} (st right)] :
    mk !{st} = !{fun p ↦ mk '' st p} := by
  refine mk_eq <| IGame.equiv_of_exists ?_ ?_ ?_ ?_ <;>
    simpa using fun a ha ↦ ⟨a, ha, equiv_mk_out a⟩

@[simp]
theorem mk_ofSets (s t : Set IGame.{u_inline_7}) [Small.{u_inline_7} s] [Small.{u_inline_7} t] :
    mk !{s | t} = !{mk '' s | mk '' t} := by
  rw [mk_ofSets']
  simp_rw [Player.apply_cases]

private theorem ofSets_cases (s t : Set Game.{u_inline_7}) [Small.{u_inline_7} s]
    [Small.{u_inline_7} t] :
    !{s | t} = mk !{out '' s | out '' t} := by
  simp [mk_ofSets, image_image]

instance : Zero Game := ⟨mk 0⟩
instance : One Game := ⟨mk 1⟩
instance : Add Game := ⟨Quotient.map₂ _ @add_congr⟩
instance : Neg Game := ⟨Quotient.map _ @neg_congr⟩
instance : PartialOrder Game := inferInstanceAs (PartialOrder (Antisymmetrization ..))
instance : Inhabited Game := ⟨0⟩

instance : AddCommGroupWithOne Game where
  zero_add := by rintro ⟨x⟩; exact congr(mk $(zero_add _))
  add_zero := by rintro ⟨x⟩; exact congr(mk $(add_zero _))
  add_comm := by rintro ⟨x⟩ ⟨y⟩; exact congr(mk $(add_comm _ _))
  add_assoc := by rintro ⟨x⟩ ⟨y⟩ ⟨z⟩; exact congr(mk $(add_assoc _ _ _))
  neg_add_cancel := by rintro ⟨a⟩; exact mk_eq (neg_add_equiv _)
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : IsOrderedAddMonoid Game where
  add_le_add_left := by rintro ⟨a⟩ ⟨b⟩ h ⟨c⟩; exact add_le_add_left (α := IGame) h _

@[simp] theorem mk_zero : mk 0 = 0 := rfl
@[simp] theorem mk_one : mk 1 = 1 := rfl
@[simp] theorem mk_add (x y : IGame) : mk (x + y) = mk x + mk y := rfl
@[simp] theorem mk_neg (x : IGame) : mk (-x) = -mk x := rfl
@[simp] theorem mk_sub (x y : IGame) : mk (x - y) = mk x - mk y := rfl

theorem mk_mulOption (x y a b : IGame) :
    mk (mulOption x y a b) = mk (a * y) + mk (x * b) - mk (a * b) :=
  rfl

@[simp] theorem mk_le_mk {x y : IGame} : mk x ≤ mk y ↔ x ≤ y := .rfl
@[simp] theorem mk_lt_mk {x y : IGame} : mk x < mk y ↔ x < y := .rfl
@[simp] theorem mk_fuzzy_mk {x y : IGame} : mk x ‖ mk y ↔ x ‖ y := .rfl

@[simp, norm_cast]
theorem mk_natCast : ∀ n : ℕ, mk n = n
  | 0 => rfl
  | n + 1 => by rw [Nat.cast_add, Nat.cast_add, mk_add, mk_natCast]; rfl

@[simp, norm_cast]
theorem mk_intCast (n : ℤ) : mk n = n := by
  cases n <;> simp

theorem zero_def : (0 : Game) = !{fun _ ↦ ∅} := by apply (mk_ofSets' ..).trans; simp
theorem one_def : (1 : Game) = !{{0} | ∅} := by apply (mk_ofSets ..).trans; simp

instance : ZeroLEOneClass Game where
  zero_le_one := zero_le_one (α := IGame)

instance : NeZero (1 : Game) where
  out := by apply ne_of_gt; exact IGame.zero_lt_one

instance : Nontrivial Game := ⟨_, _, zero_ne_one⟩
instance : CharZero Game := AddMonoidWithOne.toCharZero

theorem mk_mul_add (x y z : IGame) : mk (x * (y + z)) = mk (x * y) + mk (x * z) := by
  rw [← mk_add, add_eq' (x * y), mul_eq']
  simp only [moves_add, moves_mul, prod_union, union_assoc, image_image, image_union, mk_ofSets']
  congr! 2
  ext p
  nth_rewrite 2 [union_left_comm]
  congrm _ ∈ ?_ ∪ (?_ ∪ (?_ ∪ ?_))
  all_goals
    ext
    simp only [mulOption, mk_sub, mk_add, mem_image, mem_prod, and_assoc, Prod.exists,
      exists_and_left, exists_exists_and_eq_and]
    iterate 2 (congr! 2; rw [and_congr_right_iff]; intros)
    congr! 1
    rw [mk_mul_add, mk_mul_add, mk_mul_add]
    abel
termination_by (x, y, z)
decreasing_by igame_wf

theorem mk_mul_sub (x y z : IGame) : mk (x * (y - z)) = mk (x * y) - mk (x * z) := by
  simpa [sub_eq_add_neg] using mk_mul_add x y (-z)

theorem mk_add_mul (x y z : IGame) : mk ((x + y) * z) = mk (x * z) + mk (y * z) := by
  rw [mul_comm, mk_mul_add, mul_comm, mul_comm z]

theorem mk_sub_mul (x y z : IGame) : mk ((x - y) * z) = mk (x * z) - mk (y * z) := by
  simpa [sub_eq_add_neg] using mk_add_mul x (-y) z

theorem mk_mul_assoc (x y z : IGame) : mk (x * y * z) = mk (x * (y * z)) := by
  induction x using IGame.ofSetsRecOn generalizing y z with | ofSets xL xR ihxl ihxr
  induction y using IGame.ofSetsRecOn generalizing z with | ofSets yL yR ihyl ihyr
  induction z using IGame.ofSetsRecOn with | ofSets zL zR ihzl ihzr
  simp_rw [ofSets_mul_ofSets, mk_ofSets, Set.image_union, Set.image_image, mk_mulOption,
    ← Set.image_union, ← ofSets_mul_ofSets,
    Set.prod_image_left, Set.prod_image_right, Set.union_prod, Set.prod_union,
    ← Equiv.prod_assoc_image, ← Set.image_union, Set.image_image, Equiv.prodAssoc_apply]
  have e1 : (xL ×ˢ yL) ×ˢ zL ∪ (xR ×ˢ yR) ×ˢ zL ∪ ((xL ×ˢ yR) ×ˢ zR ∪ (xR ×ˢ yL) ×ˢ zR) =
      (xL ×ˢ yL) ×ˢ zL ∪ (xL ×ˢ yR) ×ˢ zR ∪ ((xR ×ˢ yL) ×ˢ zR ∪ (xR ×ˢ yR) ×ˢ zL) := by
    ac_rfl
  have e2 : (xL ×ˢ yL) ×ˢ zR ∪ (xR ×ˢ yR) ×ˢ zR ∪ ((xL ×ˢ yR) ×ˢ zL ∪ (xR ×ˢ yL) ×ˢ zL) =
      (xL ×ˢ yL) ×ˢ zR ∪ (xL ×ˢ yR) ×ˢ zL ∪ ((xR ×ˢ yL) ×ˢ zL ∪ (xR ×ˢ yR) ×ˢ zR) := by
    ac_rfl
  simp only [e1, e2]
  congrm !{?_ | ?_} <;>
  · refine Set.image_congr fun ⟨⟨x, y⟩, z⟩ hxyz => ?_
    obtain ⟨hx, hy, hz⟩ : (x ∈ xL ∨ x ∈ xR) ∧ (y ∈ yL ∨ y ∈ yR) ∧ (z ∈ zL ∨ z ∈ zR) := by
      simp only [mem_union, mem_prod] at hxyz
      tauto
    simp only [mulOption, mk_sub_mul, mk_add_mul, mk_mul_sub, mk_mul_add,
      hx.elim (ihxl x) (ihxr x), hy.elim (ihyl y) (ihyr y), hz.elim (ihzl z) (ihzr z)]
    abel

theorem lf_ofSets_of_mem_left {s t : Set Game.{u_inline_7}} [Small.{u_inline_7} s]
    [Small.{u_inline_7} t] {x : Game.{u_inline_7}}
    (h : x ∈ s) : x ⧏ !{s | t} := by
  rw [ofSets_cases]
  have : x.out ∈ !{out '' s | out '' t}ᴸ := by simpa using mem_image_of_mem _ h
  simpa [← mk_le_mk] using left_lf this

theorem ofSets_lf_of_mem_right {s t : Set Game.{u_inline_7}} [Small.{u_inline_7} s]
    [Small.{u_inline_7} t] {x : Game.{u_inline_7}}
    (h : x ∈ t) : !{s | t} ⧏ x := by
  rw [ofSets_cases]
  have : x.out ∈ !{out '' s | out '' t}ᴿ := by simpa using mem_image_of_mem _ h
  simpa [← mk_le_mk] using lf_right this

end Game

namespace IGame

protected theorem sub_le_iff_le_add {x y z : IGame} : x - z ≤ y ↔ x ≤ y + z :=
  @sub_le_iff_le_add Game _ _ _ (.mk x) (.mk y) (.mk z)

protected theorem le_sub_iff_add_le {x y z : IGame} : x ≤ z - y ↔ x + y ≤ z :=
  @le_sub_iff_add_le Game _ _ _ (.mk x) (.mk y) (.mk z)

protected theorem sub_lt_iff_lt_add {x y z : IGame} : x - z < y ↔ x < y + z :=
  @sub_lt_iff_lt_add Game _ _ _ (.mk x) (.mk y) (.mk z)

protected theorem lt_sub_iff_add_lt {x y z : IGame} : x < z - y ↔ x + y < z :=
  @lt_sub_iff_add_lt Game _ _ _ (.mk x) (.mk y) (.mk z)

protected theorem sub_nonneg {x y : IGame} : 0 ≤ x - y ↔ y ≤ x :=
  @sub_nonneg Game _ _ _ (.mk x) (.mk y)

protected theorem sub_nonpos {x y : IGame} : x - y ≤ 0 ↔ x ≤ y :=
  @sub_nonpos Game _ _ _ (.mk x) (.mk y)

protected theorem sub_pos {x y : IGame} : 0 < x - y ↔ y < x :=
  @sub_pos Game _ _ _ (.mk x) (.mk y)

protected theorem sub_neg {x y : IGame} : x - y < 0 ↔ x < y :=
  @sub_neg Game _ _ _ (.mk x) (.mk y)

theorem mul_add_equiv (x y z : IGame) : x * (y + z) ≈ x * y + x * z :=
  Game.mk_eq_mk.1 (Game.mk_mul_add x y z)

theorem mul_sub_equiv (x y z : IGame) : x * (y - z) ≈ x * y - x * z :=
  Game.mk_eq_mk.1 (Game.mk_mul_sub x y z)

theorem add_mul_equiv (x y z : IGame) : (x + y) * z ≈ x * z + y * z :=
  Game.mk_eq_mk.1 (Game.mk_add_mul x y z)

theorem sub_mul_equiv (x y z : IGame) : (x - y) * z ≈ x * z - y * z :=
  Game.mk_eq_mk.1 (Game.mk_sub_mul x y z)

theorem mul_assoc_equiv (x y z : IGame) : x * y * z ≈ x * (y * z) :=
  Game.mk_eq_mk.1 (Game.mk_mul_assoc x y z)

@[simp, norm_cast]
theorem natCast_le {m n : ℕ} : (m : IGame) ≤ n ↔ m ≤ n := by
  simp [← Game.mk_le_mk]

@[simp, norm_cast]
theorem natCast_lt {m n : ℕ} : (m : IGame) < n ↔ m < n := by
  simp [← Game.mk_lt_mk]

@[simp]
theorem natCast_nonneg (n : ℕ) : 0 ≤ (n : IGame) :=
  natCast_le.2 n.zero_le

theorem natCast_strictMono : StrictMono ((↑) : ℕ → IGame) :=
  fun _ _ h ↦ natCast_lt.2 h

instance : CharZero IGame where
  cast_injective := natCast_strictMono.injective

@[simp, norm_cast]
theorem natCast_equiv {m n : ℕ} : (m : IGame) ≈ n ↔ m = n := by
  simp [AntisymmRel, le_antisymm_iff]

@[simp, norm_cast]
theorem intCast_le {m n : ℤ} : (m : IGame) ≤ n ↔ m ≤ n := by
  simp [← Game.mk_le_mk]

@[simp, norm_cast]
theorem intCast_lt {m n : ℤ} : (m : IGame) < n ↔ m < n := by
  simp [← Game.mk_lt_mk]

theorem intCast_strictMono : StrictMono ((↑) : ℤ → IGame) :=
  fun _ _ h ↦ intCast_lt.2 h

@[simp, norm_cast]
theorem intCast_inj {m n : ℤ} : (m : IGame) = n ↔ m = n :=
  intCast_strictMono.injective.eq_iff

@[simp, norm_cast]
theorem intCast_equiv {m n : ℤ} : (m : IGame) ≈ n ↔ m = n := by
  simp [AntisymmRel, le_antisymm_iff]

theorem intCast_add_equiv (m n : ℤ) : ((m + n : ℤ) : IGame) ≈ m + n := by
  simp [← Game.mk_eq_mk]

theorem intCast_sub_equiv (m n : ℤ) : ((m - n : ℤ) : IGame) ≈ m - n := by
  simp [← Game.mk_eq_mk]

@[simp, norm_cast]
theorem zero_lt_intCast {n : ℤ} : 0 < (n : IGame) ↔ 0 < n := by
  simpa using intCast_lt (m := 0)

@[simp, norm_cast]
theorem intCast_lt_zero {n : ℤ} : (n : IGame) < 0 ↔ n < 0 := by
  simpa using intCast_lt (n := 0)

@[simp, norm_cast]
theorem zero_le_intCast {n : ℤ} : 0 ≤ (n : IGame) ↔ 0 ≤ n := by
  simpa using intCast_le (m := 0)

@[simp, norm_cast]
theorem intCast_le_zero {n : ℤ} : (n : IGame) ≤ 0 ↔ n ≤ 0 := by
  simpa using intCast_le (n := 0)

end IGame
end

/-! ## Inlined from `CombinatorialGames.Surreal.Basic` -/

/-!
# Surreal numbers

The basic theory of surreal numbers, built on top of the theory of combinatorial (pre-)games. A
surreal number is defined as an equivalence class of numeric games.

Surreal numbers inherit the relations `≤` and `<` from games, and these relations satisfy the axioms
of a linear order. In fact, the surreals form a complete ordered field, containing a copy of the
reals, and much else besides!

## Algebraic operations

In this file, we show that the surreals form a linear ordered commutative group.

In `CombinatorialGames.Surreal.Multiplication`, we define multiplication and show that the surreals
form a linear ordered commutative ring. In `CombinatorialGames.Surreal.Division` we further show the
surreals are a field.
-/

universe u_inline_8

@[expose] public noncomputable section

/-! ### Simplicity theorem -/

namespace IGame

/-- `x` fits within `y` when `z ⧏ x` for every `z ∈ yᴸ`, and `x ⧏ z` for every
`z ∈ yᴿ`.

The simplicity theorem states that if a game fits a numeric game, but none of its options do, then
the games are equivalent. In particular, a numeric game is equivalent to the game of the least
birthday that fits in it -/
def Fits (x y : IGame) : Prop :=
  (∀ z ∈ yᴸ, z ⧏ x) ∧ (∀ z ∈ yᴿ, x ⧏ z)

theorem fits_of_equiv {x y : IGame} (h : x ≈ y) : Fits x y :=
  ⟨fun _ hz ↦ mt h.ge.trans (left_lf hz), fun _ hz ↦ mt h.le.trans' (lf_right hz) ⟩

alias AntisymmRel.Fits := fits_of_equiv

theorem Fits.refl (x : IGame) : x.Fits x :=
  fits_of_equiv .rfl

instance : Std.Refl Fits where
  refl := Fits.refl

theorem Fits.antisymm {x y : IGame} (h₁ : Fits x y) (h₂ : Fits y x) : x ≈ y := by
  rw [AntisymmRel, le_iff_forall_lf, le_iff_forall_lf]
  exact ⟨⟨h₂.1, h₁.2⟩, ⟨h₁.1, h₂.2⟩⟩

@[simp]
theorem fits_neg_iff {x y : IGame} : Fits (-x) (-y) ↔ Fits x y := by
  simp [Fits, and_comm]

alias ⟨_, Fits.neg⟩ := fits_neg_iff

theorem not_fits_iff {x y : IGame} :
    ¬ Fits x y ↔ (∃ z ∈ yᴸ, x ≤ z) ∨ (∃ z ∈ yᴿ, z ≤ x) := by
  rw [Fits, not_and_or]; simp

theorem Fits.congr {x y z : IGame} (h : x ≈ y) (hx : x.Fits z) : y.Fits z := by
  constructor <;> intro w hw <;> grw [← h]
  exacts [hx.1 w hw, hx.2 w hw]

theorem fits_congr {x y z : IGame} (h : x ≈ y) : x.Fits z ↔ y.Fits z :=
  ⟨.congr h, .congr h.symm⟩

/-- A variant of the **simplicity theorem** with hypotheses that are easier to show. -/
theorem Fits.equiv_of_forall_moves {x y : IGame} (hx : x.Fits y)
    (hl : ∀ z ∈ xᴸ, ∃ w ∈ yᴸ, z ≤ w) (hr : ∀ z ∈ xᴿ, ∃ w ∈ yᴿ, w ≤ z) : x ≈ y :=
  ⟨le_of_forall_moves_right_lf hx.2 hl, le_of_forall_moves_left_lf hx.1 hr⟩

/-- A variant of the **simplicity theorem**: if a numeric game `x` fits within a game `y`, but none
of its options do, then `x ≈ y`.

Note that under most circumstances, `Fits.equiv_of_forall_moves` is easier to use. -/
theorem Fits.equiv_of_forall_not_fits {x y : IGame} [Numeric x] (hx : x.Fits y)
    (h : ∀ p, ∀ z ∈ x.moves p, ¬ z.Fits y) : x ≈ y := by
  simp_rw [not_fits_iff] at h
  apply hx.equiv_of_forall_moves
  · refine fun z hz ↦ (h _ z hz).resolve_right ?_
    rintro ⟨w, hw, hwz⟩
    exact hx.2 w hw <| hwz.trans (Numeric.left_lt hz).le
  · refine fun z hz ↦ (h _ z hz).resolve_left ?_
    rintro ⟨w, hw, hwz⟩
    exact hx.1 w hw <| (Numeric.lt_right hz).le.trans hwz

/-- A specialization of the simplicity theorem to `0`. -/
@[simp]
theorem fits_zero_iff_equiv {x : IGame} : Fits 0 x ↔ x ≈ 0 :=
  ⟨fun hx ↦ (hx.equiv_of_forall_not_fits <| by simp).symm, fun h ↦ fits_of_equiv h.symm⟩

/-- A specialization of the simplicity theorem to `1`. -/
theorem equiv_one_of_fits {x : IGame} (hx : Fits 1 x) (h : ¬ x ≈ 0) : x ≈ 1 := by
  apply (hx.equiv_of_forall_not_fits _).symm
  simpa

end IGame

/-! ### Surreal numbers -/

open IGame

/-- The type of surreal numbers. These are the numeric games quotiented by the antisymmetrization
relation `x ≈ y ↔ x ≤ y ∧ y ≤ x`. In the quotient, the order becomes a total order. -/
def Surreal : Type (u_inline_8 + 1) :=
  Antisymmetrization (Subtype Numeric) (· ≤ ·)

namespace Surreal

/-- The quotient map from the subtype of numeric `IGame`s into `Game`. -/
def mk (x : IGame) [h : Numeric x] : Surreal := Quotient.mk _ ⟨x, h⟩
theorem mk_eq_mk {x y : IGame} [Numeric x] [Numeric y] : mk x = mk y ↔ x ≈ y := Quotient.eq

alias ⟨_, mk_eq⟩ := mk_eq_mk

@[cases_eliminator]
theorem ind {motive : Surreal → Prop} (mk : ∀ y [Numeric y], motive (mk y)) (x : Surreal) :
    motive x := Quotient.ind (fun h ↦ @mk _ h.2) x

/-- Choose an element of the equivalence class using the axiom of choice. -/
@[no_expose] def out (x : Surreal) : IGame := (Quotient.out x).1
@[simp] instance (x : Surreal) : Numeric x.out := (Quotient.out x).2
@[simp] theorem out_eq (x : Surreal) : mk x.out = x := Quotient.out_eq x

theorem mk_out_equiv (x : IGame) [h : Numeric x] : (mk x).out ≈ x :=
  Quotient.mk_out (s := AntisymmRel.setoid (Subtype _) (· ≤ ·)) ⟨x, h⟩

theorem equiv_mk_out (x : IGame) [Numeric x] : x ≈ (mk x).out :=
  (mk_out_equiv x).symm

instance : Zero Surreal := ⟨mk 0⟩
instance : One Surreal := ⟨mk 1⟩
instance : Inhabited Surreal := ⟨0⟩

instance : Add Surreal where
  add := Quotient.map₂ (fun a b ↦ ⟨a.1 + b.1, inferInstance⟩) fun _ _ h₁ _ _ h₂ ↦ add_congr h₁ h₂

instance : Neg Surreal where
  neg := Quotient.map (fun a ↦ ⟨-a.1, inferInstance⟩) fun _ _ ↦ neg_congr

instance : PartialOrder Surreal :=
  inferInstanceAs (PartialOrder (Antisymmetrization ..))

instance : LinearOrder Surreal where
  le_total := by rintro ⟨x⟩ ⟨y⟩; exact Numeric.le_total x y
  toDecidableLE := Classical.decRel _

instance : AddCommGroup Surreal where
  zero_add := by rintro ⟨x⟩; change mk (0 + x) = mk x; simp_rw [zero_add]
  add_zero := by rintro ⟨x⟩; change mk (x + 0) = mk x; simp_rw [add_zero]
  add_comm := by rintro ⟨x⟩ ⟨y⟩; change mk (x + y) = mk (y + x); simp_rw [add_comm]
  add_assoc := by rintro ⟨x⟩ ⟨y⟩ ⟨z⟩; change mk (x + y + z) = mk (x + (y + z)); simp_rw [add_assoc]
  neg_add_cancel := by rintro ⟨a⟩; exact mk_eq (neg_add_equiv _)
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : AddGroupWithOne Surreal where

instance : IsOrderedAddMonoid Surreal where
  add_le_add_left := by rintro ⟨a⟩ ⟨b⟩ h ⟨c⟩; exact add_le_add_left (α := IGame) h _

@[simp] theorem mk_zero : mk 0 = 0 := rfl
@[simp] theorem mk_one : mk 1 = 1 := rfl
@[simp] theorem mk_add (x y : IGame) [Numeric x] [Numeric y] : mk (x + y) = mk x + mk y := rfl
@[simp] theorem mk_neg (x : IGame) [Numeric x] : mk (-x) = -mk x := rfl
@[simp] theorem mk_sub (x y : IGame) [Numeric x] [Numeric y] : mk (x - y) = mk x - mk y := rfl

@[simp] theorem mk_le_mk {x y : IGame} [Numeric x] [Numeric y] : mk x ≤ mk y ↔ x ≤ y := Iff.rfl
@[simp] theorem mk_lt_mk {x y : IGame} [Numeric x] [Numeric y] : mk x < mk y ↔ x < y := Iff.rfl

@[simp]
theorem mk_natCast : ∀ n : ℕ, mk n = n
  | 0 => rfl
  | n + 1 => by simp_rw [Nat.cast_add_one, mk_add, mk_one, mk_natCast n]

@[simp]
theorem mk_intCast (n : ℤ) : mk n = n := by
  cases n <;> simp

instance : ZeroLEOneClass Surreal where
  zero_le_one := zero_le_one (α := IGame)

instance : NeZero (1 : Surreal) where
  out := by apply ne_of_gt; exact IGame.zero_lt_one

instance : Nontrivial Surreal :=
  ⟨_, _, zero_ne_one⟩

/-- Casts a `Surreal` number into a `Game`. -/
def toGame : Surreal ↪o Game where
  toFun := Quotient.lift (fun x ↦ .mk x) fun _ _ ↦ Game.mk_eq
  inj' x y := by
    cases x; cases y;
    change Game.mk _ = Game.mk _ → _
    simp [Game.mk_eq_mk, mk_eq_mk]
  map_rel_iff' := by rintro ⟨_⟩ ⟨_⟩; rfl

@[simp] theorem toGame_mk (x : IGame) [Numeric x] : toGame (mk x) = .mk x := rfl
@[simp] theorem toGame_zero : toGame 0 = 0 := rfl
@[simp] theorem toGame_one : toGame 1 = 1 := rfl

@[simp]
theorem gameMk_out (x : Surreal) : Game.mk x.out = x.toGame := by
  conv_rhs => rw [← out_eq x, toGame_mk]

theorem toGame_le_iff {a b : Surreal} : toGame a ≤ toGame b ↔ a ≤ b := by simp
theorem toGame_lt_iff {a b : Surreal} : toGame a < toGame b ↔ a < b := by simp
theorem toGame_inj {a b : Surreal} : toGame a = toGame b ↔ a = b := by simp

/-- `Surreal.toGame` as an `OrderAddMonoidHom` -/
@[simps]
def toGameAddHom : Surreal →+o Game where
  toFun := toGame
  map_zero' := rfl
  map_add' := by rintro ⟨_⟩ ⟨_⟩; rfl
  monotone' := toGame.monotone

@[simp]
theorem toGame_add (x y : Surreal) : toGame (x + y) = toGame x + toGame y :=
  toGameAddHom.map_add x y

@[simp]
theorem toGame_neg (x : Surreal) : toGame (-x) = -toGame x :=
  toGameAddHom.map_neg x

@[simp]
theorem toGame_sub (x y : Surreal) : toGame (x - y) = toGame x - toGame y :=
  toGameAddHom.map_sub x y

@[simp] theorem toGame_natCast (n : ℕ) : toGame n = n := map_natCast' toGameAddHom rfl n
@[simp] theorem toGame_intCast (n : ℤ) : toGame n = n := map_intCast' toGameAddHom rfl n

/-- Construct a `Surreal` from its left and right sets, and a proof that all elements from the left
set are less than all the elements of the right set.

Note that although this function is well-defined, this function isn't injective, nor do equivalence
classes in Surreal have a canonical representative. (Note however that every short numeric game has
a unique "canonical" form!) -/
instance : OfSets Surreal.{u_inline_8} (fun st ↦ ∀ x ∈ st left, ∀ y ∈ st right, x < y) where
  ofSets st H _ _ := by
    refine @mk !{fun p ↦ out '' st p} (.mk ?_ (by simp))
    rw [moves_ofSets, moves_ofSets]
    rintro - ⟨x, hx, rfl⟩ - ⟨y, hy, rfl⟩
    rw [← Surreal.mk_lt_mk, out_eq, out_eq]
    exact H x hx y hy

theorem toGame_ofSets' (st : Player → Set Surreal.{u_inline_8})
    [Small.{u_inline_8} (st left)] [Small.{u_inline_8} (st right)]
    {H : ∀ x ∈ st left, ∀ y ∈ st right, x < y} :
    toGame !{st} = !{fun p ↦ toGame '' st p} := by
  change toGame (@mk _ (_)) = _
  simp_rw [toGame_mk, Game.mk_ofSets', Set.image_image, gameMk_out]

@[simp]
theorem toGame_ofSets (s t : Set Surreal.{u_inline_8}) [Small.{u_inline_8} s] [Small.{u_inline_8} t]
    {H : ∀ x ∈ s, ∀ y ∈ t, x < y} :
    toGame !{s | t} = !{toGame '' s | toGame '' t} := by
  rw [toGame_ofSets']
  congr; aesop

theorem mk_ofSets' {st : Player → Set IGame.{u_inline_8}}
    [Small.{u_inline_8} (st left)] [Small.{u_inline_8} (st right)] {H : Numeric !{st}} :
    mk !{st} =
      !{fun p ↦ .range fun x : st p ↦ mk x (h := H.of_mem_moves (p := p) (by simp))}'
      (by have := @H.left_lt_right; aesop) := by
  change _ = @mk _ (_)
  simp_rw [← toGame_inj, toGame_mk, Game.mk_ofSets']
  congr; aesop

theorem mk_ofSets {s t : Set IGame.{u_inline_8}} [Small.{u_inline_8} s]
    [Small.{u_inline_8} t] {H : Numeric !{s | t}} :
    mk !{s | t} =
      !{.range fun x : s ↦ mk x (h := H.of_mem_moves (p := left) (by simp)) |
        .range fun x : t ↦ mk x (h := H.of_mem_moves (p := right) (by simp))}'
      (by have := @H.left_lt_right; aesop) := by
  rw [mk_ofSets']
  congr!; aesop

@[aesop apply unsafe]
theorem lt_ofSets_of_mem_left {s t : Set Surreal.{u_inline_8}} [Small.{u_inline_8} s]
    [Small.{u_inline_8} t]
    {H : ∀ x ∈ s, ∀ y ∈ t, x < y} {x : Surreal} (hx : x ∈ s) :
    x < !{s | t} := by
  rw [lt_iff_not_ge, ← toGame_le_iff, toGame_ofSets]
  exact Game.lf_ofSets_of_mem_left (Set.mem_image_of_mem _ hx)

@[aesop apply unsafe]
theorem ofSets_lt_of_mem_right {s t : Set Surreal.{u_inline_8}} [Small.{u_inline_8} s]
    [Small.{u_inline_8} t]
    {H : ∀ x ∈ s, ∀ y ∈ t, x < y} {x : Surreal} (hx : x ∈ t) :
    !{s | t} < x := by
  rw [lt_iff_not_ge, ← toGame_le_iff, toGame_ofSets]
  exact Game.ofSets_lf_of_mem_right (Set.mem_image_of_mem _ hx)

theorem zero_def : (0 : Surreal) = !{fun _ ↦ ∅} := by apply (mk_ofSets' ..).trans; congr!; simp
theorem one_def : (1 : Surreal) = !{{0} | ∅} := by apply (mk_ofSets ..).trans; congr! <;> aesop

instance : DenselyOrdered Surreal where
  dense a b hab := ⟨!{{a} | {b}},
    lt_ofSets_of_mem_left (Set.mem_singleton a), ofSets_lt_of_mem_right (Set.mem_singleton b)⟩

end Surreal
end

/-! ## Inlined from `CombinatorialGames.Surreal.Multiplication` -/

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

Note also that we express all inequalities in terms of `Game` instead of `IGame`; this allows us to
make use of `abel` and all of the theorems on `OrderedAddCommGroup`.
-/

universe u_inline_9

open Game IGame Relation WellFounded

/-- A characterization of left moves of `x * y` in terms only of left moves. -/
lemma forall_leftMoves_mul' {P : IGame → Prop} {x y : IGame} :
    (∀ a ∈ (x * y)ᴸ, P a) ↔
      (∀ a ∈ xᴸ, ∀ b ∈ yᴸ, P (mulOption x y a b)) ∧
      (∀ a ∈ (-x)ᴸ, ∀ b ∈ (-y)ᴸ, P (mulOption (-x) (-y) a b)) := by
  rw [forall_moves_mul]
  simp [mulOption_neg]

/-- A characterization of right moves of `x * y` in terms only of left moves. -/
lemma forall_rightMoves_mul' {P : IGame → Prop} {x y : IGame} :
    (∀ a ∈ (x * y)ᴿ, P a) ↔
      (∀ a ∈ xᴸ, ∀ b ∈ (-y)ᴸ, P (-mulOption x (-y) a b)) ∧
      (∀ a ∈ (-x)ᴸ, ∀ b ∈ yᴸ, P (-mulOption (-x) y a b)) := by
  rw [forall_moves_mul]
  simp [mulOption_neg_right, mulOption_neg_left]

/-! ### Predicates P1 – P4 -/

/-- `P1 x y a b c d` means that `mulOption x y a b < mulOption x y c d`. This is the general form
of the statements needed to prove that `x * y` is numeric. -/
def P1 (x y a b c d : IGame) := Game.mk (mulOption x y a b) < Game.mk (mulOption x y c d)

/-- `P2 x₁ x₂ y` states that if `x₁ ≈ x₂`, then `x₁ * y ≈ x₂ * y`. The RHS is stated in terms of
`Game.mk` for rewriting convenience. -/
def P2 (x₁ x₂ y : IGame) := x₁ ≈ x₂ → Game.mk (x₁ * y) = Game.mk (x₂ * y)

/-- `P3 x₁ x₂ y₁ y₂` states that `x₁ * y₂ + x₂ * y₁ < x₁ * y₁ + x₂ * y₂`. Using distributivity, this
is equivalent to `(x₁ - x₂) * (y₁ - y₂) > 0`. -/
def P3 (x₁ x₂ y₁ y₂ : IGame) :=
  Game.mk (x₁ * y₂) + Game.mk (x₂ * y₁) < Game.mk (x₁ * y₁) + Game.mk (x₂ * y₂)

/-- `P4 x₁ x₂ y` states that if `x₁ < x₂`, then `P3 x₁ x₂ a y` when `a ∈ yᴸ`, and
`P3 x₁ x₂ b y` when `b ∈ yᴿ`.

Note that we instead write this second part as `P3 x₁ x₂ b (-y)` when `b ∈ (-y)ᴸ`. See the
module docstring for an explanation. -/
def P4 (x₁ x₂ y : IGame) :=
  x₁ < x₂ → (∀ a ∈ yᴸ, P3 x₁ x₂ a y) ∧ (∀ b ∈ (-y)ᴸ, P3 x₁ x₂ b (-y))

/-- The conjunction of `P2` and `P4`. Both statements have the same amount of arguments and satisfy
similar symmetry properties, so we can slightly simplify the argument by merging them. -/
def P24 (x₁ x₂ y : IGame) : Prop := P2 x₁ x₂ y ∧ P4 x₁ x₂ y

variable {x x₁ x₂ x₃ x' y y₁ y₂ y₃ y' a b c d : IGame.{u_inline_9}}

/-! #### Symmetry properties of P1 – P4 -/

lemma P3_comm : P3 x₁ x₂ y₁ y₂ ↔ P3 y₁ y₂ x₁ x₂ := by
  simp [P3, add_comm, mul_comm]

lemma P3.trans (h₁ : P3 x₁ x₂ y₁ y₂) (h₂ : P3 x₂ x₃ y₁ y₂) : P3 x₁ x₃ y₁ y₂ := by
  rw [P3, ← add_lt_add_iff_left (Game.mk (x₂ * y₁) + Game.mk (x₂ * y₂))]
  convert add_lt_add h₁ h₂ using 1 <;> abel

lemma P3_neg : P3 (-x₂) (-x₁) y₁ y₂ ↔ P3 x₁ x₂ y₁ y₂ := by
  simp_rw [P3, neg_mul, Game.mk_neg]
  rw [← _root_.neg_lt_neg_iff]
  abel_nf

lemma P2_neg_left : P2 (-x₂) (-x₁) y ↔ P2 x₁ x₂ y := by
  simp [P2, AntisymmRel, eq_comm]

lemma P2_neg_right : P2 x₁ x₂ (-y) ↔ P2 x₁ x₂ y := by
  simp [P2]

lemma P4_neg_left : P4 (-x₂) (-x₁) y ↔P4 x₁ x₂ y  := by
  simp_rw [P4, IGame.neg_lt_neg_iff, P3_neg]

lemma P4_neg_right : P4 x₁ x₂ (-y) ↔ P4 x₁ x₂ y := by
  rw [P4, P4, neg_neg, and_comm]

lemma P24_neg_left : P24 (-x₂) (-x₁) y ↔ P24 x₁ x₂ y := by rw [P24, P24, P2_neg_left, P4_neg_left]
lemma P24_neg_right : P24 x₁ x₂ (-y) ↔ P24 x₁ x₂ y := by rw [P24, P24, P2_neg_right, P4_neg_right]

/-! ### Inductive setup -/

/-- The type of lists of arguments for `P1`, `P2`, and `P4`. -/
inductive Args : Type (u_inline_9 + 1)
  | P1 (x y : IGame.{u_inline_9}) : Args
  | P24 (x₁ x₂ y : IGame.{u_inline_9}) : Args

/-- The multiset associated to a list of arguments. -/
def Args.toMultiset : Args → Multiset IGame
  | (Args.P1 x y) => {x, y}
  | (Args.P24 x₁ x₂ y) => {x₁, x₂, y}

@[simp] lemma Args.toMultiset_P1 {x y} : (Args.P1 x y).toMultiset = {x, y} := rfl
@[simp] lemma Args.toMultiset_P24 {x₁ x₂ y} : (Args.P24 x₁ x₂ y).toMultiset = {x₁, x₂, y} := rfl

/-- A list of arguments is numeric if all the arguments are. -/
def Args.Numeric (a : Args) := ∀ x ∈ a.toMultiset, x.Numeric

lemma Args.numeric_P1 {x y} : (Args.P1 x y).Numeric ↔ x.Numeric ∧ y.Numeric := by
  simp [Args.Numeric, Args.toMultiset]

lemma Args.numeric_P24 {x₁ x₂ y} :
    (Args.P24 x₁ x₂ y).Numeric ↔ x₁.Numeric ∧ x₂.Numeric ∧ y.Numeric := by
  simp [Args.Numeric, Args.toMultiset]

/-- The well-founded relation specifying when a list of game arguments is considered simpler than
another: `ArgsRel a₁ a₂` is true if `a₁`, considered as a multiset, can be obtained from `a₂` by
repeatedly removing a game from `a₂` and adding back one or two options of the game.

See also `WellFounded.CutExpand`. -/
def ArgsRel :=
  InvImage (Relation.TransGen <| CutExpand fun x y => ∃ p, x ∈ y.moves p) Args.toMultiset

/-- `ArgsRel` is well-founded. -/
lemma argsRel_wf : WellFounded ArgsRel :=
  InvImage.wf _ (Subrelation.wf (fun h => h.elim fun _ => Subposition.of_mem_moves)
    subposition_wf).cutExpand.transGen
instance : IsWellFounded _ ArgsRel := ⟨argsRel_wf⟩

/-- The property that all arguments are numeric is leftward-closed under `ArgsRel`. -/
lemma ArgsRel.numeric_closed {a' a} : ArgsRel a' a → a.Numeric → a'.Numeric :=
  Relation.TransGen.closed' <| @cutExpand_closed _ _
    ⟨fun _ h => (h.elim fun _ => Subposition.of_mem_moves).irrefl⟩ _ fun h h' ↦
      h'.subposition (h.elim fun _ => Subposition.of_mem_moves)

/-- The statement that we will show by induction for all `Numeric` args, using the well-founded
relation `ArgsRel`.

The inductive hypothesis in the proof will be `∀ a', ArgsRel a' a → P124 a`. -/
def P124 : Args → Prop
  | (Args.P1 x y) => Numeric (x * y)
  | (Args.P24 x₁ x₂ y) => P24 x₁ x₂ y

/-! ### P1 follows from the inductive hypothesis -/

lemma numeric_move_mul_of_IH {p : Player} (IH : ∀ a, ArgsRel a (Args.P1 x y) → P124 a)
    (h : x' ∈ x.moves p) : (x' * y).Numeric :=
  IH (Args.P1 x' y) (Relation.TransGen.single <| cutExpand_pair_left ⟨p, h⟩)

lemma numeric_mul_move_of_IH {p : Player} (IH : ∀ a, ArgsRel a (Args.P1 x y) → P124 a)
    (h : y' ∈ y.moves p) : (x * y').Numeric :=
  IH (Args.P1 x y') (Relation.TransGen.single <| cutExpand_pair_right ⟨p, h⟩)

lemma numeric_move_mul_move_of_IH {p q : Player} (IH : ∀ a, ArgsRel a (Args.P1 x y) → P124 a)
    (hx : x' ∈ x.moves p) (hy : y' ∈ y.moves q) : (x' * y').Numeric :=
  IH (Args.P1 x' y')
    ((Relation.TransGen.single (cutExpand_pair_right ⟨q, hy⟩)).tail (cutExpand_pair_left ⟨p, hx⟩))

/-- A specialization of the inductive hypothesis used to prove `P1`. -/
def IH1 (x y : IGame) : Prop :=
  ∀ ⦃p q x₁ x₂ y'⦄, x₁ ∈ x.moves p → x₂ ∈ x.moves q →
    (y' = y ∨ ∃ u_inline_9, y' ∈ y.moves u_inline_9) → P24 x₁ x₂ y'

/-- `IH1 x y` follows from the inductive hypothesis for `P1 x y`. -/
lemma IH1_of_IH (IH : ∀ a, ArgsRel a (Args.P1 x y) → P124 a) : IH1 x y := by
  rintro p q x₁ x₂ y' h₁ h₂ (rfl | hy) <;> apply IH (.P24 ..)
  on_goal 2 => refine .tail ?_ (cutExpand_pair_right hy)
  all_goals exact .single (cutExpand_double_left ⟨p, h₁⟩ ⟨q, h₂⟩)

/-- `IH1 y x` follows from the inductive hypothesis for `P1 x y`. -/
lemma IH1_swap_of_IH (IH : ∀ a, ArgsRel a (Args.P1 x y) → P124 a) : IH1 y x := IH1_of_IH <| by
  simpa [-Multiset.insert_eq_cons, ArgsRel, InvImage, Multiset.pair_comm] using IH

lemma IH1_neg_left : IH1 x y → IH1 (-x) y := by
  intro h p q x₁ x₂ y' h₁ h₂ hy
  rw [moves_neg] at h₁ h₂
  exact P24_neg_left.1 (h h₂ h₁ hy)

lemma IH1_neg_right : IH1 x y → IH1 x (-y) := by
  intro h p q x₁ x₂ y' h₁ h₂ hy
  rw [← P24_neg_right]
  apply h h₁ h₂
  simpa [neg_eq_iff_eq_neg, or_comm] using hy

lemma P1_of_equiv (he : x₁ ≈ x₃) (h₁ : P2 x₁ x₃ y₁) (h₃ : P2 x₁ x₃ y₃) (h3 : P3 x₁ x₂ y₂ y₃) :
    P1 x₂ y₁ x₁ y₂ x₃ y₃ := by
  rw [P1, mk_mulOption, mk_mulOption, ← h₁ he, ← h₃ he, sub_lt_sub_iff]
  convert add_lt_add_left h3 (.mk (x₁ * y₁)) using 1 <;> abel

lemma P1_of_P3 (h₁ : P3 x₃ x₂ y₂ y₃) (h₂ : P3 x₁ x₃ y₂ y₁) : P1 x₂ y₁ x₁ y₂ x₃ y₃ := by
  rw [P1, mk_mulOption, mk_mulOption, sub_lt_sub_iff, ← add_lt_add_iff_left (.mk (x₃ * y₂))]
  convert add_lt_add h₁ h₂ using 1 <;> abel

lemma P3_of_IH1 [Numeric y] (ihyx : IH1 y x)
    (ha : a ∈ xᴸ) (hb : b ∈ yᴸ) (hd : d ∈ (-y)ᴸ) : P3 a x b (-d) := by
  rw [P3_comm]
  rw [moves_neg] at hd
  refine ((ihyx hb hd (.inl rfl)).2 ?_).1 a ha
  exact Numeric.left_lt_right hb hd

lemma P24_of_IH1 (ihxy : IH1 x y) (ha : a ∈ xᴸ) (hb : b ∈ xᴸ) : P24 a b y :=
  ihxy ha hb (Or.inl rfl)

lemma mulOption_lt_iff_P1 :
    Game.mk (mulOption x y a b) < -Game.mk (mulOption x (-y) c d) ↔ P1 x y a b c (-d) := by
  simp [P1, mulOption, sub_eq_add_neg, add_comm]

lemma mulOption_lt_of_lt [Numeric y] (ihxy : IH1 x y) (ihyx : IH1 y x) {a b c d} (h : a < c)
    (ha : a ∈ xᴸ) (hb : b ∈ yᴸ) (hc : c ∈ xᴸ) (hd : d ∈ (-y)ᴸ) :
    Game.mk (mulOption x y a b) < -Game.mk (mulOption x (-y) c d) := by
  rw [mulOption_lt_iff_P1]
  exact P1_of_P3 (P3_of_IH1 ihyx hc hb hd) <| ((P24_of_IH1 ihxy ha hc).2 h).1 b hb

lemma mulOption_lt [Numeric x] [Numeric y] (ihxy : IH1 x y) (ihyx : IH1 y x) {a b c d}
    (ha : a ∈ xᴸ) (hb : b ∈ yᴸ) (hc : c ∈ xᴸ) (hd : d ∈ (-y)ᴸ) :
    Game.mk (mulOption x y a b) < -Game.mk (mulOption x (-y) c d) := by
  numeric
  obtain (h | h | h) := Numeric.lt_or_equiv_or_gt a c
  · exact mulOption_lt_of_lt ihxy ihyx h ha hb hc hd
  · exact mulOption_lt_iff_P1.2 (P1_of_equiv h (P24_of_IH1 ihxy ha hc).1
      (ihxy ha hc <| .inr ⟨right, by simpa using hd⟩).1 <| P3_of_IH1 ihyx ha hb hd)
  · rw [← neg_neg y] at hb
    simpa [lt_neg] using mulOption_lt_of_lt (IH1_neg_right ihxy) (IH1_neg_left ihyx) h hc hd ha hb

/-- `P1` follows from the induction hypothesis. -/
lemma P1_of_IH (IH : ∀ a, ArgsRel a (Args.P1 x y) → P124 a) [Numeric x] [Numeric y] :
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

lemma numeric_of_IH (IH : ∀ a, ArgsRel a (Args.P24 x₁ x₂ y) → P124 a) :
    (x₁ * y).Numeric ∧ (x₂ * y).Numeric := by
  constructor <;> refine IH (.P1 ..) (.single ?_)
  · exact (cutExpand_add_right {y}).2 <| (cutExpand_add_left {x₁}).2 cutExpand_zero
  · exact (cutExpand_add_right {x₂, y}).2 cutExpand_zero

/-- A specialization of the inductive hypothesis used to prove `P2` and `P4`. -/
def IH24 (x₁ x₂ y : IGame) : Prop :=
  ∀ ⦃p z⦄,
    (z ∈ x₁.moves p → P24 z x₂ y) ∧
    (z ∈ x₂.moves p → P24 x₁ z y) ∧
    (z ∈ y.moves p → P24 x₁ x₂ z)

/-- A specialization of the induction hypothesis used to prove `P4`. -/
def IH4 (x₁ x₂ y : IGame) : Prop :=
  ∀ ⦃p q z w⦄, w ∈ y.moves p → (z ∈ x₁.moves q → P2 z x₂ w) ∧ (z ∈ x₂.moves q → P2 x₁ z w)

/-- `IH24 x₁ x₂ y` follows from the inductive hypothesis for `P24 x₁ x₂ y`. -/
lemma IH24_of_IH (IH : ∀ a, ArgsRel a (Args.P24 x₁ x₂ y) → P124 a) : IH24 x₁ x₂ y := by
  rw [IH24]
  refine fun p z ↦ ⟨?_, ?_, ?_⟩ <;> refine fun h ↦ IH (.P24 ..) (.single ?_)
  · exact (cutExpand_add_right {y}).2 (cutExpand_pair_left ⟨p, h⟩)
  · exact (cutExpand_add_left {x₁}).2 (cutExpand_pair_left ⟨p, h⟩)
  · exact (cutExpand_add_left {x₁}).2 (cutExpand_pair_right ⟨p, h⟩)

/-- `IH24 x₂ x₁ y` follows from the inductive hypothesis for `P24 x₁ x₂ y`. -/
lemma IH24_swap_of_IH (IH : ∀ a, ArgsRel a (Args.P24 x₁ x₂ y) → P124 a) : IH24 x₂ x₁ y := by
  apply IH24_of_IH
  convert IH using 2
  dsimp [ArgsRel, InvImage, Multiset.insert_eq_cons, ← Multiset.singleton_add]
  abel_nf

/-- `IH4 x₁ x₂ y` follows from the inductive hypothesis for `P24 x₁ x₂ y`. -/
lemma IH4_of_IH (IH : ∀ a, ArgsRel a (Args.P24 x₁ x₂ y) → P124 a) : IH4 x₁ x₂ y := by
  refine fun p q a b h ↦ ⟨?_, ?_⟩ <;>
    refine fun h' ↦ (IH (.P24 ..) <| (Relation.TransGen.single ?_).tail <|
      (cutExpand_add_left {x₁}).2 <| cutExpand_pair_right ⟨p, h⟩).1
  · exact (cutExpand_add_right {b}).2 <| cutExpand_pair_left ⟨q, h'⟩
  · exact (cutExpand_add_right {b}).2 <| cutExpand_pair_right ⟨q, h'⟩

lemma IH24_neg : IH24 x₁ x₂ y → IH24 (-x₂) (-x₁) y ∧ IH24 x₁ x₂ (-y) := by
  simp_rw [IH24, P24_neg_right, moves_neg]
  refine fun h ↦ ⟨fun p z ↦ ⟨?_, ?_, ?_⟩,
    fun p z ↦ ⟨(@h p z).1, (@h p z).2.1, P24_neg_right.1 ∘ (@h (-p) (-z)).2.2⟩⟩
  all_goals
    rw [← P24_neg_left]
    simp only [neg_neg]
  · exact (@h (-p) (-z)).2.1
  · exact (@h (-p) (-z)).1
  · exact (@h p z).2.2

lemma IH4_neg : IH4 x₁ x₂ y → IH4 (-x₂) (-x₁) y ∧ IH4 x₁ x₂ (-y) := by
  simp_rw [IH4, moves_neg, Set.mem_neg]
  refine fun h ↦ ⟨fun p q z w h' ↦ ?_, fun p q z w h' ↦ ?_⟩
  · convert (h h').symm using 2 <;> rw [← P2_neg_left, neg_neg]
  · convert h h' using 2 <;> rw [P2_neg_right]

lemma mulOption_lt_mul_of_equiv [Numeric x₁] (h : IH24 x₁ x₂ y) (he : x₁ ≈ x₂)
    (hi : a ∈ x₁ᴸ) (hj : b ∈ yᴸ) :
    Game.mk (mulOption x₁ y a b) < Game.mk (x₂ * y) := by
  convert sub_lt_iff_lt_add'.2 (((h.1 hi).2 _).1 b hj) using 1
  · rw [← (h.2.2 hj).1 he]
    rfl
  · grw [← he]
    exact Numeric.left_lt hi

lemma mul_right_le_of_equiv [Numeric x₁] [Numeric x₂]
    (ih₁₂ : IH24 x₁ x₂ y) (ih₂₁ : IH24 x₂ x₁ y) (he : x₁ ≈ x₂) : x₁ * y ≤ x₂ * y := by
  have he' := neg_equiv_neg_iff.2 he
  rw [IGame.le_iff_forall_lf]
  simp_rw [← Game.mk_le_mk]
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
lemma P2_of_IH (IH : ∀ a, ArgsRel a (Args.P24 x₁ x₂ y) → P124 a) [Numeric x₁] [Numeric x₂]
    (he : x₁ ≈ x₂) : x₁ * y ≈ x₂ * y :=
  ⟨mul_right_le_of_equiv (IH24_of_IH IH) (IH24_swap_of_IH IH) he,
    mul_right_le_of_equiv (IH24_swap_of_IH IH) (IH24_of_IH IH) he.symm⟩

/-! ### P4 follows from the inductive hypothesis -/

lemma mulOption_lt_mul_iff_P3 : mulOption x y a b < x * y ↔ P3 a x b y :=
  @sub_lt_iff_lt_add' Game _ _ _ (.mk _) (.mk _) (.mk _)

/-- A specialization of the induction hypothesis used to prove `P3`. -/
def IH3 (x₁ x' x₂ y₁ y₂ : IGame) : Prop :=
  P2 x₁ x' y₁ ∧ P2 x₁ x' y₂ ∧ P3 x' x₂ y₁ y₂ ∧ (x₁ < x' → P3 x₁ x' y₁ y₂)

/-- `IH3` follows from the induction hypothesis for `P24 x₁ x₂ y`. -/
lemma IH3_of_IH (ih24 : IH24 x₁ x₂ y) (ih4 : IH4 x₁ x₂ y)
    (hi : a ∈ x₂ᴸ) (hb : b ∈ yᴸ) (hl : mulOption x₂ y a b < x₂ * y) :
    IH3 x₁ a x₂ b y :=
  have h24 := ih24.2.1 hi
  ⟨(ih4 hb).2 hi, h24.1,
    mulOption_lt_mul_iff_P3.1 hl, fun l ↦ (h24.2 l).1 b hb⟩

lemma P3_of_le_left {y₁ y₂} (i) (h : IH3 x₁ i x₂ y₁ y₂) (hl : x₁ ≤ i) : P3 x₁ x₂ y₁ y₂ := by
  obtain (hl | he) := le_iff_lt_or_antisymmRel.1 hl
  · exact (h.2.2.2 hl).trans h.2.2.1
  · rw [P3, h.1 he, h.2.1 he]
    exact h.2.2.1

/-- P3 follows from `IH3`, so P4 (with `y₁` a left option of `y₂`) follows from the induction
hypothesis. -/
lemma P3_of_IH3 {y₁ y₂} (h : ∀ i ∈ x₂ᴸ, IH3 x₁ i x₂ y₁ y₂)
    (hs : ∀ i ∈ (-x₁)ᴸ, IH3 (-x₂) i (-x₁) y₁ y₂) (hl : x₁ < x₂) : P3 x₁ x₂ y₁ y₂ := by
  obtain (⟨i, hi, hi'⟩ | ⟨i, hi, hi'⟩) := lf_iff_exists_le.1 hl.not_ge
  · exact P3_of_le_left i (h i hi) hi'
  · refine P3_neg.1 <| P3_of_le_left _ (hs (-i) ?_) ?_ <;> simpa

/-- `P4` follows from the induction hypothesis. -/
lemma P4_of_IH (IH : ∀ a, ArgsRel a (.P24 x₁ x₂ y) → P124 a) : P4 x₁ x₂ y := by
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
theorem main (a : Args) : a.Numeric → P124 a := by
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
    · exact (Game.mk_eq <| P2_of_IH ih ·)
    · exact P4_of_IH ih

lemma main_P24 (x₁ x₂ y : IGame) [hx₁ : Numeric x₁] [hx₂ : Numeric x₂] [hy : Numeric y] :
    P24 x₁ x₂ y :=
  main _ <| Args.numeric_P24.mpr ⟨hx₁, hx₂, hy⟩

/-- One additional inductive argument proves `P3`. -/
lemma P3_of_lt_of_lt {x₁ x₂ y₁ y₂} [Numeric x₁] [Numeric x₂] [Numeric y₁] [Numeric y₂]
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
  Game.mk_eq_mk.1 ((main_P24 ..).1 he)

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


public noncomputable section

universe u

namespace Surreal

/-- The singleton Conway cut `{x - 1 | x + 1}`. -/
def singletonIntegerCut (x : Surreal.{u}) : Surreal.{u} :=
  !{{x - 1} | {x + 1}}' (by
    simp only [Set.mem_singleton_iff]
    rintro _ rfl _ rfl
    simp [sub_eq_add_neg])

/-- Conway's cut equation defining an omnific integer. -/
def IsConwayOmnificInteger (x : Surreal.{u}) : Prop :=
  x = singletonIntegerCut x

/-- Conway's refinement conjecture for the concretely defined surreal numbers. -/
def ConwayConjecture : Prop :=
  ∀ a b c d : Surreal.{u},
    IsConwayOmnificInteger a → IsConwayOmnificInteger b →
    IsConwayOmnificInteger c → IsConwayOmnificInteger d → a * b = c * d →
    ∃ e f g h : Surreal.{u},
      IsConwayOmnificInteger e ∧ IsConwayOmnificInteger f ∧
      IsConwayOmnificInteger g ∧ IsConwayOmnificInteger h ∧
      a = e * f ∧ b = g * h ∧ c = e * g ∧ d = f * h

end Surreal

end

end

end

end

end ConwayRefinement.Standalone.InlineSurreal
