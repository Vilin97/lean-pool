/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: V.Hernández Palacios, R.Barton, M.Carneiro, I.Longbottom, K.Morrison, A.Nakade, Y.Zhao
-/
module

/- Full upstream author names: Violeta Hernández Palacios, Reid Barton, Mario Carneiro, Isabel
Longbottom, Kim Morrison, Apurva Nakade, Yuyang Zhao. -/

public import LeanPool.ConwayRefinement.CombinatorialGames.Game.Classes
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs

import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Tactic.Abel

/-!
# Combinatorial games

In this file we construct the quotient of games `IGame` under equivalence, and prove that it forms
an `OrderedAddCommGroup`. We take advantage of this structure to prove two particularly tedious
theorems on `IGame`, namely `IGame.mul_add_equiv` and `IGame.mul_assoc_equiv`.

It might be tempting to write `mk (x * y)` as `mk x * mk y`, but the latter is not well-defined, as
there exist `x₁ ≈ x₂` and `y₁ ≈ y₂` with `x₁ * y₁ ≉ x₂ * y₂`. See
`CombinatorialGames.Counterexamples.Multiplication` for a proof.
-/

universe u

@[expose] public noncomputable section

open IGame Set Pointwise

/-- Games up to equivalence.

If `x` and `y` are combinatorial games (`IGame`), we say that `x ≈ y` when both `x ≤ y` and `y ≤ x`.
Broadly, this means neither player has a preference in playing either game, as a component of a
larger game. This is the standard meaning of `x = y` in the literature, though it is not a strict
equality, e.g. `{0, 1 | 0}` and `{1 | 0}` are equivalent, but not identical as the former has an
extra move for Left.

In particular, note that a `ConwayGame` has no well-defined notion of left and right options.
This means
you should prefer `IGame` when analyzing specific games. -/
def ConwayGame : Type (u + 1) :=
  Antisymmetrization IGame (· ≤ ·)

namespace ConwayGame

/-- The quotient map from `IGame` into `ConwayGame`. -/
def mk (x : IGame) : ConwayGame := Quotient.mk _ x
theorem mk_eq_mk {x y : IGame} : mk x = mk y ↔ x ≈ y := Quotient.eq

alias ⟨_, mk_eq⟩ := mk_eq_mk

@[cases_eliminator]
theorem ind {motive : ConwayGame → Prop} (mk : ∀ y, motive (mk y)) (x : ConwayGame) : motive x :=
  Quotient.ind mk x

/-- Choose an element of the equivalence class using the axiom of choice. -/
@[no_expose] def out (x : ConwayGame) : IGame := Quotient.out x
@[simp] theorem out_eq (x : ConwayGame) : mk x.out = x := Quotient.out_eq x

theorem mk_out_equiv (x : IGame) : (mk x).out ≈ x := Quotient.mk_out (s := AntisymmRel.setoid ..) x
theorem equiv_mk_out (x : IGame) : x ≈ (mk x).out := (mk_out_equiv x).symm

/-- Construct a `ConwayGame` from its left and right sets.

Note that although this function is well-defined, this function isn't injective, nor do equivalence
classes in `ConwayGame` have a canonical representative. -/
instance : OfSets ConwayGame.{u} fun _ ↦ True where
  ofSets st _ := mk !{fun p ↦ out '' (st p)}

theorem mk_ofSets' (st : Player → Set IGame.{u}) [Small.{u} (st left)] [Small.{u} (st right)] :
    mk !{st} = !{fun p ↦ mk '' st p} := by
  refine mk_eq <| IGame.equiv_of_exists ?_ ?_ ?_ ?_ <;>
    simpa using fun a ha ↦ ⟨a, ha, equiv_mk_out a⟩

@[simp]
theorem mk_ofSets (s t : Set IGame.{u}) [Small.{u} s] [Small.{u} t] :
    mk !{s | t} = !{mk '' s | mk '' t} := by
  rw [mk_ofSets']
  simp_rw [Player.apply_cases]

private theorem ofSets_cases (s t : Set ConwayGame.{u}) [Small.{u} s] [Small.{u} t] :
    !{s | t} = mk !{out '' s | out '' t} := by
  simp [mk_ofSets, image_image]

instance : Zero ConwayGame := ⟨mk 0⟩
instance : One ConwayGame := ⟨mk 1⟩
instance : Add ConwayGame := ⟨Quotient.map₂ _ @add_congr⟩
instance : Neg ConwayGame := ⟨Quotient.map _ @neg_congr⟩
instance : PartialOrder ConwayGame := inferInstanceAs (PartialOrder (Antisymmetrization ..))
instance : Inhabited ConwayGame := ⟨0⟩

instance : AddCommGroupWithOne ConwayGame where
  zero_add := by rintro ⟨x⟩; exact congr(mk $(zero_add _))
  add_zero := by rintro ⟨x⟩; exact congr(mk $(add_zero _))
  add_comm := by rintro ⟨x⟩ ⟨y⟩; exact congr(mk $(add_comm _ _))
  add_assoc := by rintro ⟨x⟩ ⟨y⟩ ⟨z⟩; exact congr(mk $(add_assoc _ _ _))
  neg_add_cancel := by rintro ⟨a⟩; exact mk_eq (neg_add_equiv _)
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : IsOrderedAddMonoid ConwayGame where
  add_le_add_left := by rintro ⟨a⟩ ⟨b⟩ h ⟨c⟩; exact add_le_add_left (α := IGame) h _

instance : RatCast ConwayGame where
  ratCast q := mk q

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

@[simp, norm_cast] theorem mk_ratCast (q : ℚ) : mk q = q := rfl
@[simp, norm_cast] theorem ratCast_neg (q : ℚ) : ((-q : ℚ) : ConwayGame) = -q := by
  simp [← mk_ratCast]

theorem zero_def : (0 : ConwayGame) = !{fun _ ↦ ∅} := by apply (mk_ofSets' ..).trans; simp
theorem one_def : (1 : ConwayGame) = !{{0} | ∅} := by apply (mk_ofSets ..).trans; simp

instance : ZeroLEOneClass ConwayGame where
  zero_le_one := zero_le_one (α := IGame)

instance : NeZero (1 : ConwayGame) where
  out := by apply ne_of_gt; exact IGame.zero_lt_one

instance : Nontrivial ConwayGame := ⟨_, _, zero_ne_one⟩
instance : CharZero ConwayGame := AddMonoidWithOne.toCharZero

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

theorem lf_ofSets_of_mem_left {s t : Set ConwayGame.{u}} [Small.{u} s] [Small.{u} t]
    {x : ConwayGame.{u}}
    (h : x ∈ s) : x ⧏ !{s | t} := by
  rw [ofSets_cases]
  have : x.out ∈ !{out '' s | out '' t}ᴸ := by simpa using mem_image_of_mem _ h
  simpa [← mk_le_mk] using left_lf this

theorem ofSets_lf_of_mem_right {s t : Set ConwayGame.{u}} [Small.{u} s] [Small.{u} t]
    {x : ConwayGame.{u}}
    (h : x ∈ t) : !{s | t} ⧏ x := by
  rw [ofSets_cases]
  have : x.out ∈ !{out '' s | out '' t}ᴿ := by simpa using mem_image_of_mem _ h
  simpa [← mk_le_mk] using lf_right this

end ConwayGame

namespace IGame

protected theorem sub_le_iff_le_add {x y z : IGame} : x - z ≤ y ↔ x ≤ y + z :=
  @sub_le_iff_le_add ConwayGame _ _ _ (.mk x) (.mk y) (.mk z)

protected theorem le_sub_iff_add_le {x y z : IGame} : x ≤ z - y ↔ x + y ≤ z :=
  @le_sub_iff_add_le ConwayGame _ _ _ (.mk x) (.mk y) (.mk z)

protected theorem sub_lt_iff_lt_add {x y z : IGame} : x - z < y ↔ x < y + z :=
  @sub_lt_iff_lt_add ConwayGame _ _ _ (.mk x) (.mk y) (.mk z)

protected theorem lt_sub_iff_add_lt {x y z : IGame} : x < z - y ↔ x + y < z :=
  @lt_sub_iff_add_lt ConwayGame _ _ _ (.mk x) (.mk y) (.mk z)

protected theorem sub_nonneg {x y : IGame} : 0 ≤ x - y ↔ y ≤ x :=
  @sub_nonneg ConwayGame _ _ _ (.mk x) (.mk y)

protected theorem sub_nonpos {x y : IGame} : x - y ≤ 0 ↔ x ≤ y :=
  @sub_nonpos ConwayGame _ _ _ (.mk x) (.mk y)

protected theorem sub_pos {x y : IGame} : 0 < x - y ↔ y < x :=
  @sub_pos ConwayGame _ _ _ (.mk x) (.mk y)

protected theorem sub_neg {x y : IGame} : x - y < 0 ↔ x < y :=
  @sub_neg ConwayGame _ _ _ (.mk x) (.mk y)

theorem mul_add_equiv (x y z : IGame) : x * (y + z) ≈ x * y + x * z :=
  ConwayGame.mk_eq_mk.1 (ConwayGame.mk_mul_add x y z)

theorem mul_sub_equiv (x y z : IGame) : x * (y - z) ≈ x * y - x * z :=
  ConwayGame.mk_eq_mk.1 (ConwayGame.mk_mul_sub x y z)

theorem add_mul_equiv (x y z : IGame) : (x + y) * z ≈ x * z + y * z :=
  ConwayGame.mk_eq_mk.1 (ConwayGame.mk_add_mul x y z)

theorem sub_mul_equiv (x y z : IGame) : (x - y) * z ≈ x * z - y * z :=
  ConwayGame.mk_eq_mk.1 (ConwayGame.mk_sub_mul x y z)

theorem mul_assoc_equiv (x y z : IGame) : x * y * z ≈ x * (y * z) :=
  ConwayGame.mk_eq_mk.1 (ConwayGame.mk_mul_assoc x y z)

@[simp, norm_cast]
theorem natCast_le {m n : ℕ} : (m : IGame) ≤ n ↔ m ≤ n := by
  simp [← ConwayGame.mk_le_mk]

@[simp, norm_cast]
theorem natCast_lt {m n : ℕ} : (m : IGame) < n ↔ m < n := by
  simp [← ConwayGame.mk_lt_mk]

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
  simp [← ConwayGame.mk_le_mk]

@[simp, norm_cast]
theorem intCast_lt {m n : ℤ} : (m : IGame) < n ↔ m < n := by
  simp [← ConwayGame.mk_lt_mk]

theorem intCast_strictMono : StrictMono ((↑) : ℤ → IGame) :=
  fun _ _ h ↦ intCast_lt.2 h

@[simp, norm_cast]
theorem intCast_inj {m n : ℤ} : (m : IGame) = n ↔ m = n :=
  intCast_strictMono.injective.eq_iff

@[simp, norm_cast]
theorem intCast_equiv {m n : ℤ} : (m : IGame) ≈ n ↔ m = n := by
  simp [AntisymmRel, le_antisymm_iff]

theorem intCast_add_equiv (m n : ℤ) : ((m + n : ℤ) : IGame) ≈ m + n := by
  simp [← ConwayGame.mk_eq_mk]

theorem intCast_sub_equiv (m n : ℤ) : ((m - n : ℤ) : IGame) ≈ m - n := by
  simp [← ConwayGame.mk_eq_mk]

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

namespace Impartial
variable (x y : IGame) [hx : Impartial x] [hy : Impartial y]

@[simp]
theorem neg_mk : -ConwayGame.mk x = ConwayGame.mk x :=
  ConwayGame.mk_eq (equiv_neg x).symm

@[simp]
theorem sub_mk (x : ConwayGame) : x - ConwayGame.mk y = x + ConwayGame.mk y := by
  rw [sub_eq_add_neg, neg_mk]

@[simp]
theorem mk_add_self : ConwayGame.mk x + ConwayGame.mk x = 0 := by
  rw [add_eq_zero_iff_neg_eq, neg_mk]

-- TODO: move these four lemmas earlier:

theorem add_self_equiv (x : IGame) [Impartial x] : x + x ≈ 0 :=
  ConwayGame.mk_eq_mk.1 (mk_add_self x)

variable {x y}

omit hx in
/-- This lemma doesn't require `x` to be impartial. -/
theorem equiv_iff_add_equiv_zero : x ≈ y ↔ x + y ≈ 0 := by
  rw [← ConwayGame.mk_eq_mk, ← ConwayGame.mk_eq_mk,
    ConwayGame.mk_add, ConwayGame.mk_zero,
    add_eq_zero_iff_eq_neg, neg_mk]

omit hy in
/-- This lemma doesn't require `y` to be impartial. -/
theorem equiv_iff_add_equiv_zero' : x ≈ y ↔ x + y ≈ 0 := by
  rw [antisymmRel_comm, add_comm, equiv_iff_add_equiv_zero]

theorem fuzzy_iff_add_fuzzy_zero : x ‖ y ↔ x + y ‖ 0 := by
  simpa using (@equiv_iff_add_equiv_zero x y).not

end Impartial
end IGame
end
