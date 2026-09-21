/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Reid Barton, Mario Carneiro, Isabel Longbottom, Kim Morrison, Yuyang Zhao
-/
module

public import Batteries.Classes.RatCast
public import LeanPool.ConwayRefinement.CombinatorialGames.Game.Player
public meta import LeanPool.ConwayRefinement.CombinatorialGames.Tactic.Register
public import Mathlib.Algebra.Group.Pointwise.Set.Small
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Order.Comparable

import LeanPool.ConwayRefinement.CombinatorialGames.Game.Functor
import LeanPool.ConwayRefinement.CombinatorialGames.Mathlib.Small
import Mathlib.Lean.PrettyPrinter.Delaborator
import Mathlib.Logic.Hydra
import Mathlib.Order.GameAdd

/-!
# Combinatorial (pre-)games

The basic theory of combinatorial games, following Conway's book `On Numbers and Games`.

In ZFC, games are built inductively out of two other sets of games, representing the options for two
players Left and Right. In Lean, we instead define the type of games `IGame` as arising from two
`Small` sets of games, with notation `!{s | t}`. A `u`-small type `α : Type v`
is one that is equivalent to some `β : Type u`, and the distinction between small and large types in
a given universe closely mimics the ZFC distinction between sets and proper classes.

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

theorem Relation.transGen_iff_exists {α : Type*} {r : α → α → Prop} {x y : α} :
    Relation.TransGen r x y ↔ ∃ z, r z y ∧ (x = z ∨ TransGen r x z) := by
  rw [transGen_iff]
  simp [and_or_left, exists_or, and_comm]

universe u

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
  | ofSets (s t : Set IGame.{u}) [Small.{u} s] [Small.{u} t] : IGame.{u}
```

(though for technical reasons it's not literally defined as such). A consequence of this is that
there is no infinite line of play. See `LGame` for a definition of loopy games. -/
def IGame : Type (u + 1) :=
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
def moves (p : Player) (x : IGame.{u}) : Set IGame.{u} := x.dest.1 p

/-- The set of left moves of the game. -/
scoped notation:max x:max "ᴸ" => moves left x

/-- The set of right moves of the game. -/
scoped notation:max x:max "ᴿ" => moves right x

instance (p : Player) (x : IGame.{u}) : Small.{u} (x.moves p) := x.dest.2 p

@[simp, game_cmp]
theorem moves_ofSets (p) (st : Player → Set IGame) [Small.{u} (st left)] [Small.{u} (st right)] :
    !{st}.moves p = st p := by
  exact congrArg (fun s : GameFunctor IGame => s.val p)
    (QPF.Fix.dest_mk ⟨st, by rintro (_ | _) <;> assumption⟩)

@[simp]
theorem ofSets_moves (x : IGame) : !{x.moves} = x := x.mk_dest

@[game_cmp]
theorem leftMoves_ofSets (s t : Set IGame) [Small.{u} s] [Small.{u} t] : !{s | t}ᴸ = s :=
  moves_ofSets ..

@[game_cmp]
theorem rightMoves_ofSets (s t : Set IGame) [Small.{u} s] [Small.{u} t] : !{s | t}ᴿ = t :=
  moves_ofSets ..

@[simp]
theorem ofSets_leftMoves_rightMoves (x : IGame) : !{xᴸ | xᴿ} = x := by
  convert x.ofSets_moves with p
  cases p <;> rfl

/-- Two `IGame`s are equal when their move sets are.

For the weaker but more common notion of equivalence where `x = y` if `x ≤ y` and `y ≤ x`,
use `Game`. -/
@[ext]
theorem ext {x y : IGame.{u}} (h : ∀ p, x.moves p = y.moves p) :
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

@[aesop safe apply]
theorem Subposition.of_mem_moves {p} {x y : IGame} (h : x ∈ y.moves p) : Subposition x y :=
  Relation.TransGen.single (Set.mem_iUnion_of_mem p h)

theorem Subposition.trans {x y z : IGame} (h₁ : Subposition x y) (h₂ : Subposition y z) :
    Subposition x z :=
  Relation.TransGen.trans h₁ h₂

instance : IsTrans _ Subposition := inferInstanceAs (IsTrans _ (Relation.TransGen _))

/-- The set of games reachable from a given game is small. -/
instance small_setOf_subposition (x : IGame.{u}) : Small.{u} {y | Subposition y x} :=
  small_transGen' _ x

/-- A variant of `small_setOf_subposition` in simp-normal form -/
instance small_subtype_subposition (x : IGame.{u}) : Small.{u} {y // Subposition y x} :=
  small_transGen' _ x

theorem subposition_wf : WellFounded Subposition := by
  change WellFounded (Relation.TransGen fun (x y : QPF.Fix GameFunctor) =>
    x ∈ ⋃ p, (QPF.Fix.dest y).val p)
  refine ⟨fun x => Acc.transGen ?_⟩
  apply QPF.Fix.ind
  rintro _ ⟨⟨st, hst⟩, rfl⟩
  constructor
  rintro y hy
  rw [QPF.Fix.dest_mk] at hy
  change y ∈ ⋃ p, Subtype.val '' st p at hy
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hy
  obtain ⟨z, _, rfl⟩ := hp
  exact z.property

-- We make no use of `IGame`'s definition from a `QPF` after this point.
attribute [irreducible] IGame

instance : WellFounded Subposition := subposition_wf
instance : WellFoundedRelation IGame := ⟨Subposition, subposition_wf⟩

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
instance small_setOf_wsubposition (x : IGame.{u}) : Small.{u} {y | WSubposition y x} :=
  small_insert x {y | Subposition y x}

/-- A variant of `small_setOf_wsubposition` in simp-normal form -/
instance small_subtype_wsubposition (x : IGame.{u}) : Small.{u} {y // WSubposition y x} :=
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
def ofSetsRecOn {motive : IGame.{u} → Sort*} (x)
    (ofSets : Π (s t : Set IGame) [Small s] [Small t],
      (Π x ∈ s, motive x) → (Π x ∈ t, motive x) → motive !{s | t}) :
    motive x :=
  cast (by simp) <| moveRecOn (motive := fun x ↦ motive !{xᴸ | xᴿ}) x
    fun x IH ↦ ofSets _ _
      (fun y hy ↦ cast (by simp) (IH left y hy)) (fun y hy ↦ cast (by simp) (IH right y hy))

@[simp]
theorem ofSetsRecOn_ofSets {motive : IGame.{u} → Sort*}
    (s t : Set IGame) [Small.{u} s] [Small.{u} t]
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

@[simp, game_cmp] theorem moves_zero (p : Player) : moves p 0 = ∅ := moves_ofSets ..

instance : Inhabited IGame := ⟨0⟩

/-- The game `1 = !{{0} | ∅}`. -/
instance : One IGame := ⟨!{{0} | ∅}⟩

theorem one_def : (1 : IGame) = !{{0} | ∅} := rfl

@[simp, game_cmp] theorem leftMoves_one : 1ᴸ = {0} := leftMoves_ofSets ..
@[simp, game_cmp] theorem rightMoves_one : 1ᴿ = ∅ := rightMoves_ofSets ..

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
    have u := f.constLevels![0]!
    have α : Q(Type u) := α
    have r : Q($α → $α → Prop) := r
    let le ← synthInstanceQ q(LE $α)
    _ ← assertDefEqQ q(($le).le) q($r)
    let x ← withNaryArg 2 delab
    let y ← withNaryArg 3 delab
    let stx : Term ← do
      let info ← Lean.MonadRef.mkInfoFromRefPos
      pure {
        raw := Lean.Syntax.node3 info ``IGame.«term_≈_» x.raw (Lean.Syntax.atom info "≈") y.raw
      }
    annotateGoToSyntaxDef stx
  catch _ => failure -- fail over to the default delaborator

open Lean PrettyPrinter Delaborator SubExpr Qq in
/-- Delaborates `IncompRel (· ≤ ·) x y` into `x ‖ y`. -/
@[delab app.IncompRel]
meta def delabFuzzy : Delab := do
  try
    let_expr f@IncompRel α r _ _ := ← getExpr | failure
    have u := f.constLevels![0]!
    have α : Q(Type u) := α
    have r : Q($α → $α → Prop) := r
    let le ← synthInstanceQ q(LE $α)
    _ ← assertDefEqQ q(($le).le) q($r)
    let x ← withNaryArg 2 delab
    let y ← withNaryArg 3 delab
    let stx : Term ← do
      let info ← Lean.MonadRef.mkInfoFromRefPos
      pure {
        raw := Lean.Syntax.node3 info ``IGame.«term_‖_» x.raw (Lean.Syntax.atom info "‖") y.raw
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

@[game_cmp]
theorem forall_moves_neg {P : IGame → Prop} {p : Player} {x : IGame} :
    (∀ y ∈ (-x).moves p, P y) ↔ (∀ y ∈ x.moves (-p), P (-y)) := by
  simp

@[game_cmp]
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

@[game_cmp]
theorem forall_moves_add {p : Player} {P : IGame → Prop} {x y : IGame} :
    (∀ a ∈ (x + y).moves p, P a) ↔
      (∀ a ∈ x.moves p, P (a + y)) ∧ (∀ b ∈ y.moves p, P (x + b)) := by
  aesop

@[game_cmp]
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

-- TODO: [AddLeftMono α] [AddLeftReflectLE α] → AddLeftReflectLT α
instance : AddLeftReflectLT IGame where
  elim _ := by simp [lt_iff_le_not_ge]

instance : AddRightReflectLT IGame :=
  addRightReflectLT_of_addLeftReflectLT _

-- TODO: add the general versions of this to Mathlib

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
@[game_cmp]
theorem leftMoves_natCast_succ' : ∀ n : ℕ, n.succᴸ = {(n : IGame)}
  | 0 => by simp
  | n + 1 => by
    rw [Nat.cast_succ, moves_add, leftMoves_natCast_succ']
    simp

@[simp 1100] -- This should trigger before `leftMoves_add`.
theorem leftMoves_natCast_succ (n : ℕ) : (n + 1)ᴸ = {(n : IGame)} :=
  leftMoves_natCast_succ' n

@[simp 1100, game_cmp] -- This should trigger before `rightMoves_add`.
theorem rightMoves_natCast : ∀ n : ℕ, nᴿ = ∅
  | 0 => by simp
  | n + 1 => by
    rw [Nat.cast_succ, moves_add, rightMoves_natCast]
    simp

@[simp 1100, game_cmp]
theorem leftMoves_ofNat (n : ℕ) [n.AtLeastTwo] : ofNat(n)ᴸ = {((n - 1 : ℕ) : IGame)} := by
  change nᴸ = _
  rw [← Nat.succ_pred (NeZero.out (n := n)), leftMoves_natCast_succ']
  simp

@[simp 1100, game_cmp]
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

@[simp, game_cmp, norm_cast] theorem intCast_nat (n : ℕ) : ((n : ℤ) : IGame) = n := rfl
@[simp, game_cmp] theorem intCast_ofNat (n : ℕ) : ((ofNat(n) : ℤ) : IGame) = n := rfl
@[simp] theorem intCast_negSucc (n : ℕ) : (Int.negSucc n : IGame) = -(n + 1) := rfl

@[game_cmp, norm_cast] theorem intCast_zero : ((0 : ℤ) : IGame) = 0 := rfl
@[game_cmp, norm_cast] theorem intCast_one : ((1 : ℤ) : IGame) = 1 := by simp

@[simp, game_cmp, norm_cast]
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

-- TODO: upstream
attribute [aesop apply safe] Prod.Lex.left Prod.Lex.right

private def mul' (x y : IGame) : IGame :=
  !{(range fun a : (xᴸ ×ˢ yᴸ ∪ xᴿ ×ˢ yᴿ :) ↦
    mul' a.1.1 y + mul' x a.1.2 - mul' a.1.1 a.1.2) |
  (range fun a : (xᴸ ×ˢ yᴿ ∪ xᴿ ×ˢ yᴸ :) ↦
    mul' a.1.1 y + mul' x a.1.2 - mul' a.1.1 a.1.2)}
termination_by (x, y)
decreasing_by
  all_goals
    rcases a.property with h | h
    all_goals
      first
      | exact Prod.Lex.left _ _ (Subposition.of_mem_moves h.1)
      | exact Prod.Lex.right _ (Subposition.of_mem_moves h.2)

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
@[pp_nodot, game_cmp, expose]
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

@[game_cmp]
theorem forall_moves_mul {p : Player} {P : IGame → Prop} {x y : IGame} :
    (∀ a ∈ (x * y).moves p, P a) ↔
      (∀ p', ∀ a ∈ x.moves p', ∀ b ∈ y.moves (p' * p), P (mulOption x y a b)) := by
  aesop

@[game_cmp]
theorem exists_moves_mul {p : Player} {P : IGame → Prop} {x y : IGame} :
    (∃ a ∈ (x * y).moves p, P a) ↔
      (∃ p', ∃ a ∈ x.moves p', ∃ b ∈ y.moves (p' * p), P (mulOption x y a b)) := by
  aesop

private theorem zero_mul' (x : IGame) : 0 * x = 0 := by
  ext p; cases p <;> simp

private theorem one_mul' (x : IGame) : 1 * x = x := by
  refine moveRecOn x ?_
  aesop (add simp [mulOption, and_assoc, zero_mul'])

private theorem mul_comm' (x y : IGame) : x * y = y * x := by
  ext p
  simp only [moves_mul, mem_image, mem_prod, mem_union, Prod.exists]
  cases p; all_goals
    dsimp
    simp only [and_comm, or_comm]
    rw [exists_comm]
    congr! 4 with b a
    rw [and_congr_left_iff]
    rintro (⟨_, _⟩ | ⟨_, _⟩) <;>
      rw [mulOption, mulOption, mul_comm' x, mul_comm' _ y, add_comm, mul_comm' a b]
termination_by (x, y)
decreasing_by igame_wf

instance : CommMagma IGame where
  mul_comm := private mul_comm'

instance : MulZeroClass IGame where
  zero_mul := private zero_mul'
  mul_zero x := private mul_comm' .. ▸ zero_mul' x

instance : MulZeroOneClass IGame where
  one_mul := private one_mul'
  mul_one x := private mul_comm' .. ▸ one_mul' x

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

/-! ### Division -/

/-- An auxiliary inductive type to enumerate the options of `IGame.inv`. -/
private inductive InvTy (lr : Player → Type u) : Player → Type u
  | zero : InvTy lr left
  | mk (p₁ p₂) : (lr (-(p₁ * p₂))) → InvTy lr p₁ → InvTy lr p₂

private def InvTy.val' {x : IGame}
    (IH : ∀ p, Shrink {y ∈ x.moves p | 0 < y} → IGame) (b : Player) :
    InvTy (fun p ↦ Shrink {y ∈ x.moves p | 0 < y}) b → IGame
  | zero => 0
  | mk _ _ i j => (1 + ((equivShrink _).symm i - x) * val' IH _ j) * IH _ i

private def inv' (x : IGame.{u}) : IGame.{u} :=
  let IH (p) : Shrink {y ∈ x.moves p | 0 < y} → IGame :=
    fun x ↦ inv' (Subtype.val <| (equivShrink _).symm x)
  !{.range (InvTy.val' IH left) | .range (InvTy.val' IH right)}
termination_by x
decreasing_by exact .of_mem_moves ((equivShrink _).symm x).2.1

private abbrev InvTy.val (x : IGame) (b : Player)
    (i : InvTy (fun p ↦ Shrink {y ∈ x.moves p | 0 < y}) b) : IGame :=
  i.val' (fun _ ↦ inv' ∘ Subtype.val ∘ (equivShrink _).symm) b

/-- The inverse of a positive game `x = !{s | t}` is `!{s' | t'}`, where `s'` and `t'` are the
smallest sets such that `0 ∈ s'`, and such that `(1 + (z - x) * a) / z, (1 + (y - x) * b) / y ∈ s'`
and `(1 + (y - x) * a) / y, (1 + (z - x) * b) / z ∈ t'` for `y ∈ s` positive, `z ∈ t`, `a ∈ s'`, and
`b ∈ t'`.

If `x` is negative, we define `x⁻¹ = -(-x)⁻¹`. For any other game, we set `x⁻¹ = 0`.

If `x` is a non-zero numeric game, then `x * x⁻¹ ≈ 1`. The value of this function on any non-numeric
game should be treated as a junk value. -/
@[no_expose]
instance : Inv IGame where
  inv x := by classical exact if 0 < x then inv' x else if x < 0 then -inv' (-x) else 0

instance : Div IGame where
  div x y := x * y⁻¹

open Classical in
private theorem inv_eq'' {x : IGame} :
    x⁻¹ = if 0 < x then inv' x else if x < 0 then -inv' (-x) else 0 :=
  rfl

private theorem inv_eq {x : IGame.{u}} (hx : 0 < x) :
    x⁻¹ = !{.range (InvTy.val x left) | .range (InvTy.val x right)} := by
  rw [inv_eq'', ite_eq_left hx, inv']
  rfl

private theorem inv_eq' {x : IGame.{u}} (hx : 0 < x) :
    x⁻¹ = !{fun p ↦ .range (InvTy.val x p)} := by
  rw [inv_eq hx, ofSets_eq_ofSets_cases fun _ ↦ range _]

protected theorem div_eq_mul_inv (x y : IGame) : x / y = x * y⁻¹ := rfl

theorem inv_of_equiv_zero {x : IGame} (h : x ≈ 0) : x⁻¹ = 0 := by
  simp [inv_eq'', h.not_lt, h.not_gt]

@[simp] protected theorem inv_zero : (0 : IGame)⁻¹ = 0 := inv_of_equiv_zero .rfl
@[simp] protected theorem zero_div (x : IGame) : 0 / x = 0 := zero_mul _
@[simp] protected theorem neg_div (x y : IGame) : -x / y = -(x / y) := neg_mul ..

@[simp]
protected theorem inv_neg (x : IGame) : (-x)⁻¹ = -x⁻¹ := by
  rw [inv_eq'', inv_eq'']
  obtain h | h | h | h := lt_or_antisymmRel_or_gt_or_incompRel x 0
  repeat
    simp [h, h.asymm]
    simp [h.not_lt, h.not_gt]

/-- The general option of `x⁻¹` looks like `(1 + (y - x) * a) / y`, for `y` an option of `x`, and
`a` some other "earlier" option of `x⁻¹`. -/
@[pp_nodot, expose]
def invOption (x y a : IGame) : IGame :=
  (1 + (y - x) * a) / y

private theorem invOption_eq {x y a : IGame} (hy : 0 < y) :
    invOption x y a = (1 + (y - x) * a) * inv' y := by
  rw [invOption, IGame.div_eq_mul_inv, inv_eq'', ite_eq_left hy]

theorem zero_mem_leftMoves_inv {x : IGame} (hx : 0 < x) : 0 ∈ x⁻¹ᴸ := by
  rw [inv_eq hx, leftMoves_ofSets]
  exact ⟨InvTy.zero, rfl⟩

theorem inv_nonneg {x : IGame} (hx : 0 < x) : 0 ⧏ x⁻¹ :=
  left_lf (zero_mem_leftMoves_inv hx)
theorem invOption_mem_moves_inv {x y a : IGame} {p₁ p₂} (hx : 0 < x) (hy : 0 < y)
    (hyx : y ∈ x.moves (-(p₁ * p₂))) (ha : a ∈ x⁻¹.moves p₁) :
    invOption x y a ∈ x⁻¹.moves p₂ := by
  rw [inv_eq' hx, moves_ofSets] at *
  obtain ⟨i, rfl⟩ := ha
  use InvTy.mk _ _ (equivShrink _ ⟨_, (by simpa [mul_left_comm p₂]), hy⟩) i
  simp [InvTy.val, InvTy.val', invOption_eq hy]

private theorem invRec' {x : IGame.{u}} (hx : 0 < x)
    {P : ∀ p, ∀ y ∈ x⁻¹.moves p, Prop}
    (zero : P left 0 (zero_mem_leftMoves_inv hx))
    (mk : ∀ p₁ p₂, ∀ y (hy : 0 < y) (hyx : y ∈ x.moves (-(p₁ * p₂))), ∀ a (ha : a ∈ x⁻¹.moves p₁),
      P p₁ a ha → P p₂ _ (invOption_eq hy ▸ invOption_mem_moves_inv hx hy hyx ha)) :
    (∀ p y (hy : y ∈ x⁻¹.moves p), P p y hy) := by
  suffices ∀ p : Player, ∀ i, P p (InvTy.val x p i) (by cases p <;> simp [inv_eq hx]) by
    intro p y hy
    rw [inv_eq' hx, moves_ofSets] at hy
    obtain ⟨i, rfl⟩ := hy
    simpa using this p i
  intro b i
  induction i
  · simpa
  · apply mk
    · exact ((equivShrink {y ∈ _ | 0 < y}).symm _).2.2
    · exact ((equivShrink {y ∈ _ | 0 < y}).symm _).2.1
    · assumption

/-- An induction principle on left and right moves of `x⁻¹`. -/
theorem invRec {x : IGame} (hx : 0 < x)
    {P : ∀ p, ∀ y ∈ x⁻¹.moves p, Prop}
    (zero : P left 0 (zero_mem_leftMoves_inv hx))
    (mk : ∀ p₁ p₂, ∀ y (hy : 0 < y) (hyx : y ∈ x.moves (-(p₁ * p₂))), ∀ a (ha : a ∈ x⁻¹.moves p₁),
      P p₁ a ha → P p₂ _ (invOption_mem_moves_inv hx hy hyx ha)) :
    (∀ p y (hy : y ∈ x⁻¹.moves p), P p y hy) := by
  apply invRec' hx zero
  convert mk using 8 with _ _ _ ha
  simp_rw [invOption_eq ha]

instance : RatCast IGame where
  ratCast q := q.num / q.den

theorem ratCast_def (q : ℚ) : (q : IGame) = q.num / q.den := rfl

@[simp] theorem ratCast_zero : ((0 : ℚ) : IGame) = 0 := by simp [ratCast_def]
@[simp] theorem ratCast_neg (q : ℚ) : ((-q : ℚ) : IGame) = -(q : IGame) := by simp [ratCast_def]

end IGame
end
