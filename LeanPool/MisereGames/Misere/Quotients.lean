/-
Copyright (c) 2026 Alfie Davies, Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies, Tomasz Maciosowski
-/
module

public import LeanPool.MisereGames.Misere.Universe
public import Mathlib.Algebra.Order.Monoid.Defs

/-!
Misere combinatorial games.
-/

namespace MisereGames

universe u

variable {G : Type (u + 1)} [Form G]

open Form
open Form.Misere.Outcome

public noncomputable section

/--
Restricted misère equality modulo `A`, as a setoid on `A`'s games.
-/
@[expose]
def MisereSetoid (A : G → Prop) : Setoid {g : G // A g} where
  r g h := (g : G) =m A (h : G)
  iseqv := ⟨fun _ _ _ => rfl, MisereEQ.symm, MisereEQ.trans⟩

/--
The games in `A` taken up to misère equality modulo `A`.
-/
@[expose]
def MisereQuotient (A : G → Prop) : Type (u + 1) :=
  Quotient (MisereSetoid A)

instance instSetoidSubtypeLeanPool (A : G → Prop) : Setoid {g : G // A g} :=
  MisereSetoid A

namespace Form.MisereQuotient

variable {A : G → Prop}

/--
The class of a game in the misère quotient.
-/
@[expose]
def mk (g : {g : G // A g}) : MisereQuotient A :=
  Quotient.mk (MisereSetoid A) g

/--
A chosen representative of a misère-quotient class.
-/
def out (x : MisereQuotient A) : {g : G // A g} :=
  Quotient.out x

theorem mk_eq_mk {g h : {g : G // A g}} : mk g = mk h ↔ (g : G) =m A (h : G) :=
  Quotient.eq

theorem sound {g h : {g : G // A g}} (hgh : MisereEQ A (g : G) (h : G)) : mk g = mk h :=
  Quotient.sound hgh

theorem exact {g h : {g : G // A g}} (hgh : mk g = mk h) : (g : G) =m A (h : G) :=
  Quotient.exact hgh

@[simp]
theorem mk_out (x : MisereQuotient A) : mk x.out = x :=
  Quotient.out_eq x

theorem out_equiv_self (g : {g : G // A g}) : ((mk g).out : G) =m A (g : G) :=
  Quotient.mk_out (s := MisereSetoid A) g

theorem add_misereEQ_add [ClosedUnderAdd A] {g g' h h' : G} (hh : A h) (hg' : A g')
    (hg : g =m A g') (hh' : h =m A h') : (g + h) =m A (g' + h') := by
  intro x hx
  have hhx : A (h + x) := ClosedUnderAdd.has_add _ _ hh hx
  have hgx : A (g' + x) := ClosedUnderAdd.has_add _ _ hg' hx
  calc
    MisereOutcome ((g + h) + x)
        = MisereOutcome (g + (h + x)) := by rw [add_assoc]
    _ = MisereOutcome (g' + (h + x)) := hg _ hhx
    _ = MisereOutcome (h + (g' + x)) := by
      simp only [add_left_comm]
    _ = MisereOutcome (h' + (g' + x)) := hh' _ hgx
    _ = MisereOutcome ((g' + h') + x) := by
      simp only [add_comm, add_left_comm]

theorem add_misereGE_add_right [ClosedUnderAdd A] {k : G} (hk : A k) {g h : G}
    (hgh : g ≥m A h) : MisereGE A (g + k) (h + k) := by
  intro x hx
  have hkx : A (k + x) := ClosedUnderAdd.has_add _ _ hk hx
  simpa only [add_assoc, add_comm, add_left_comm] using hgh (k + x) hkx

instance instAdd [ClosedUnderAdd A] : Add (MisereQuotient A) where
  add x y :=
    Quotient.liftOn₂ x y
      (fun g h => mk ⟨(g : G) + (h : G), ClosedUnderAdd.has_add _ _ g.2 h.2⟩)
      fun _ b a' _ hg hh => sound (add_misereEQ_add b.2 a'.2 hg hh)

@[simp]
theorem mk_add_mk [ClosedUnderAdd A] (g h : {g : G // A g}) :
    mk g + mk h = mk ⟨(g : G) + (h : G), ClosedUnderAdd.has_add _ _ g.2 h.2⟩ :=
  rfl

instance instAddCommSemigroup [ClosedUnderAdd A] : AddCommSemigroup (MisereQuotient A) where
  add_assoc x y z := by
    induction x using Quotient.inductionOn
    induction y using Quotient.inductionOn
    induction z using Quotient.inductionOn
    apply sound
    intro t ht
    simp only [add_assoc]
  add_comm x y := by
    induction x using Quotient.inductionOn
    induction y using Quotient.inductionOn
    apply sound
    intro t ht
    simp only [add_comm]

instance instZero [HasZero A] : Zero (MisereQuotient A) where
  zero := mk ⟨0, HasZero.has_zero⟩

@[simp]
theorem mk_zero [HasZero A] : mk (A := A) ⟨0, HasZero.has_zero⟩ = (0 : MisereQuotient A) :=
  rfl

instance instAddCommMonoid [HasZero A] [ClosedUnderAdd A] :
    AddCommMonoid (MisereQuotient A) where
  add_zero x := by
    induction x using Quotient.inductionOn
    apply sound
    intro t ht
    simp only [add_zero]
  zero_add x := by
    induction x using Quotient.inductionOn
    apply sound
    intro t ht
    simp only [zero_add]
  add_comm := add_comm
  add_assoc := add_assoc
  nsmul := nsmulRec

/--
The order on the quotient: `mk g ≤ mk h` exactly when `h ≥m A g`.
-/
instance instLE : LE (MisereQuotient A) where
  le x y :=
    Quotient.liftOn₂ x y (fun g h => (h : G) ≥m A (g : G)) fun g h g' h' hg hh => by
      change (g : G) =m A (g' : G) at hg
      change (h : G) =m A (h' : G) at hh
      apply propext
      constructor
      · intro hge
        exact misereGE_rw_left hh (misereGE_rw_right (MisereEQ.symm hg) hge)
      · intro hge
        exact misereGE_rw_left (MisereEQ.symm hh) (misereGE_rw_right hg hge)

theorem mk_le_mk (g h : {g : G // A g}) : mk g ≤ mk h ↔ (h : G) ≥m A (g : G) :=
  Iff.rfl

instance instPartialOrder : PartialOrder (MisereQuotient A) where
  le := (· ≤ ·)
  le_refl x := by
    induction x using Quotient.inductionOn
    exact MisereGE.refl _
  le_trans x y z hxy hyz := by
    induction x using Quotient.inductionOn
    induction y using Quotient.inductionOn
    induction z using Quotient.inductionOn
    exact MisereGE.trans hyz hxy
  le_antisymm x y hxy hyx := by
    induction x using Quotient.inductionOn
    induction y using Quotient.inductionOn
    exact sound (MisereEq.of_antisymm hyx hxy)

theorem out_le_out {a b : MisereQuotient A} :
    a ≤ b ↔ ((b.out : G) ≥m A (a.out : G)) := by
  conv_lhs => rw [← mk_out a, ← mk_out b]
  exact mk_le_mk _ _

instance instIsOrderedAddMonoid [HasZero A] [ClosedUnderAdd A] :
    IsOrderedAddMonoid (MisereQuotient A) where
  add_le_add_left x y hxy z := by
    induction x using Quotient.inductionOn
    induction y using Quotient.inductionOn
    induction z using Quotient.inductionOn with | h z =>
    change MisereGE A (_ + _) (_ + _)
    exact add_misereGE_add_right z.2 hxy

end Form.MisereQuotient

end

end MisereGames
