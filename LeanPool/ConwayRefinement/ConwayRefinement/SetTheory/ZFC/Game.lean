/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.CombinatorialGames.Game.IGame
public import Mathlib.SetTheory.ZFC.Basic

/-!
# Games coded by ZFC sets

A game code is a Kuratowski ordered pair of sets of game codes, representing its left and right
options. This grammar is stated independently of `IGame`. Coding and decoding preserve literal
pregame equality, not just equality of game values.
-/

universe u

public noncomputable section

namespace ZFSet

/-- A well-founded game tree coded as an ordered pair of sets of game codes. -/
inductive IsGameCode : ZFSet.{u} → Prop
  | mk (L R : ZFSet.{u})
      (left : ∀ x ∈ L, IsGameCode x) (right : ∀ x ∈ R, IsGameCode x) :
      IsGameCode (pair L R)

/-- A game code has a left-option set and a right-option set of game codes. -/
theorem IsGameCode.exists_eq_pair {z : ZFSet.{u}} (h : IsGameCode z) :
    ∃ L R, z = pair L R ∧ (∀ x ∈ L, IsGameCode x) ∧ (∀ x ∈ R, IsGameCode x) := by
  cases h with
  | mk L R hL hR => exact ⟨L, R, rfl, hL, hR⟩

@[simp]
theorem isGameCode_pair_iff (L R : ZFSet.{u}) :
    IsGameCode (pair L R) ↔ (∀ x ∈ L, IsGameCode x) ∧ (∀ x ∈ R, IsGameCode x) := by
  constructor
  · intro h
    obtain ⟨L', R', heq, hL, hR⟩ := h.exists_eq_pair
    obtain ⟨rfl, rfl⟩ := pair_inj.1 heq
    exact ⟨hL, hR⟩
  · rintro ⟨hL, hR⟩
    exact .mk L R hL hR

/-- The ZFC sets satisfying the independent game-code grammar. -/
def GameCode : Type (u + 1) := {x : ZFSet.{u} // IsGameCode x}

namespace GameCode

/-- Make a game code from a ZFC set satisfying the grammar. -/
def mk (x : ZFSet.{u}) (h : IsGameCode x) : GameCode.{u} := ⟨x, h⟩

/-- The underlying ZFC set of a game code. -/
def val (x : GameCode.{u}) : ZFSet.{u} := x.1

instance : Coe GameCode.{u} ZFSet.{u} := ⟨val⟩

@[simp]
theorem coe_mk (x : ZFSet.{u}) (h : IsGameCode x) : (mk x h : ZFSet.{u}) = x := (rfl)

/-- Every game code satisfies its defining grammar. -/
theorem isGameCode (x : GameCode.{u}) : IsGameCode (x : ZFSet.{u}) := x.2

@[ext]
theorem ext {x y : GameCode.{u}} (h : (x : ZFSet.{u}) = (y : ZFSet.{u})) : x = y :=
  Subtype.ext h

@[simp]
theorem mk_coe (x : GameCode.{u}) : mk (x : ZFSet.{u}) x.isGameCode = x := by
  apply ext
  rfl

end GameCode
end ZFSet

namespace IGame

/-- Encode a game as an ordered pair of the ZFC sets of recursively encoded options. -/
def toZFSet (x : IGame.{u}) : ZFSet.{u} :=
  IGame.moveRecOn x fun z ih ↦
    ZFSet.pair (ZFSet.range fun y : z.moves left ↦ ih left y.1 y.2)
      (ZFSet.range fun y : z.moves right ↦ ih right y.1 y.2)

/-- The set of codes of a game's options for one player. -/
def optionsZFSet (p : Player) (x : IGame.{u}) : ZFSet.{u} :=
  ZFSet.range fun y : x.moves p ↦ toZFSet y.1

@[simp]
theorem mem_optionsZFSet {p : Player} {x : IGame.{u}} {z : ZFSet.{u}} :
    z ∈ optionsZFSet p x ↔ ∃ y ∈ x.moves p, toZFSet y = z := by
  simp [optionsZFSet]

/-- The code's first and second components encode the left and right options. -/
theorem toZFSet_eq_pair (x : IGame.{u}) :
    toZFSet x = ZFSet.pair (optionsZFSet left x) (optionsZFSet right x) := by
  rw [toZFSet, IGame.moveRecOn_eq]
  rfl

@[simp]
theorem toZFSet_ofSets (s t : Set IGame.{u}) [Small.{u} s] [Small.{u} t] :
    toZFSet !{s | t} = ZFSet.pair
      (ZFSet.range fun y : s ↦ toZFSet y.1) (ZFSet.range fun y : t ↦ toZFSet y.1) := by
  rw [toZFSet_eq_pair]
  apply congrArg₂ ZFSet.pair <;> apply ZFSet.ext <;> intro z <;>
    simp [mem_optionsZFSet]

@[simp]
theorem toZFSet_zero : toZFSet (0 : IGame.{u}) = ZFSet.pair ∅ ∅ := by
  rw [toZFSet_eq_pair]
  apply congrArg₂ ZFSet.pair <;> apply ZFSet.ext <;> intro z <;>
    simp

/-- Every encoded game satisfies the independent ZFC grammar. -/
theorem isGameCode_toZFSet (x : IGame.{u}) : ZFSet.IsGameCode (toZFSet x) := by
  induction x using IGame.moveRecOn with
  | ind x ih =>
    rw [toZFSet_eq_pair]
    apply ZFSet.IsGameCode.mk
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := mem_optionsZFSet.1 hz
      exact ih left y hy
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := mem_optionsZFSet.1 hz
      exact ih right y hy

/-- Coding distinguishes literal games, including their complete option sets. -/
theorem toZFSet_injective : Function.Injective (toZFSet.{u}) := by
  intro x
  induction x using IGame.moveRecOn with
  | ind x ih =>
    intro y h
    have hp : ∀ p, optionsZFSet p x = optionsZFSet p y := by
      rw [toZFSet_eq_pair x, toZFSet_eq_pair y, ZFSet.pair_inj] at h
      intro p
      cases p
      · exact h.1
      · exact h.2
    apply IGame.ext
    intro p
    ext a
    constructor
    · intro ha
      have hcode : toZFSet a ∈ optionsZFSet p y := by
        rw [← hp p]
        exact mem_optionsZFSet.2 ⟨a, ha, rfl⟩
      obtain ⟨b, hb, hab⟩ := mem_optionsZFSet.1 hcode
      exact (ih p a ha hab.symm) ▸ hb
    · intro ha
      have hcode : toZFSet a ∈ optionsZFSet p x := by
        rw [hp p]
        exact mem_optionsZFSet.2 ⟨a, ha, rfl⟩
      obtain ⟨b, hb, hab⟩ := mem_optionsZFSet.1 hcode
      exact (ih p b hb hab) ▸ hb

/-- Every set generated by the ZFC grammar is the code of a game. -/
theorem exists_toZFSet_eq_of_isGameCode {z : ZFSet.{u}} (hz : ZFSet.IsGameCode z) :
    ∃ x : IGame.{u}, toZFSet x = z := by
  induction hz with
  | mk L R _ _ ihL ihR =>
    let l : L → IGame.{u} := fun a ↦ Classical.choose (ihL a.1 a.2)
    let r : R → IGame.{u} := fun a ↦ Classical.choose (ihR a.1 a.2)
    have hl (a : L) : toZFSet (l a) = a.1 := Classical.choose_spec (ihL a.1 a.2)
    have hr (a : R) : toZFSet (r a) = a.1 := Classical.choose_spec (ihR a.1 a.2)
    refine ⟨!{Set.range l | Set.range r}, ?_⟩
    rw [toZFSet_eq_pair]
    apply congrArg₂ ZFSet.pair
    · apply ZFSet.ext
      intro z
      simp only [mem_optionsZFSet, moves_ofSets, Set.mem_range]
      constructor
      · rintro ⟨g, ⟨a, rfl⟩, h⟩
        rw [hl a] at h
        exact h ▸ a.2
      · intro h
        exact ⟨l ⟨z, h⟩, ⟨⟨z, h⟩, rfl⟩, hl ⟨z, h⟩⟩
    · apply ZFSet.ext
      intro z
      simp only [mem_optionsZFSet, moves_ofSets, Set.mem_range]
      constructor
      · rintro ⟨g, ⟨a, rfl⟩, h⟩
        rw [hr a] at h
        exact h ▸ a.2
      · intro h
        exact ⟨r ⟨z, h⟩, ⟨⟨z, h⟩, rfl⟩, hr ⟨z, h⟩⟩

/-- Literal games are equivalent to the ZFC sets satisfying the independent game-code grammar. -/
def zfSetEquiv : IGame.{u} ≃ ZFSet.GameCode.{u} where
  toFun x := ZFSet.GameCode.mk (toZFSet x) (isGameCode_toZFSet x)
  invFun z := Classical.choose (exists_toZFSet_eq_of_isGameCode z.isGameCode)
  left_inv x := toZFSet_injective
    (Classical.choose_spec (exists_toZFSet_eq_of_isGameCode (isGameCode_toZFSet x)))
  right_inv z := ZFSet.GameCode.ext
    (Classical.choose_spec (exists_toZFSet_eq_of_isGameCode z.isGameCode))

@[simp]
theorem coe_zfSetEquiv (x : IGame.{u}) : (zfSetEquiv x : ZFSet.{u}) = toZFSet x := (rfl)

@[simp]
theorem toZFSet_zfSetEquiv_symm (z : ZFSet.GameCode.{u}) :
    toZFSet (zfSetEquiv.symm z) = (z : ZFSet.{u}) :=
  Classical.choose_spec (exists_toZFSet_eq_of_isGameCode z.isGameCode)

@[simp]
theorem zfSetEquiv_symm_mk (x : IGame.{u}) :
    zfSetEquiv.symm (ZFSet.GameCode.mk (toZFSet x) (isGameCode_toZFSet x)) = x :=
  zfSetEquiv.symm_apply_apply x

end IGame
