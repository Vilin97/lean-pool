/-
Copyright (c) 2026 the authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur F. Ramos, Ruy J. G. B. de Queiroz, Anjolina G. de Oliveira
-/
import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import LeanPool.NagataFactoriality.NagataFactoriality.Basic.Ring

/-!
# Divisibility

Supporting results for Nagata’s factoriality theorem.
-/

namespace NagataFactoriality

open scoped BigOperators

/-- The product of a finite list, defined recursively. -/
def listProd {α : Type*} [CommMonoid α] : List α → α
  | [] => 1
  | a :: as => a * listProd as

@[simp] theorem listProd_nil {α : Type*} [CommMonoid α] : listProd ([] : List α) = 1 := rfl

@[simp] theorem listProd_cons {α : Type*} [CommMonoid α] (a : α) (as : List α) :
    listProd (a :: as) = a * listProd as := rfl

theorem listProd_append {α : Type*} [CommMonoid α] (xs ys : List α) :
    listProd (xs ++ ys) = listProd xs * listProd ys := by
  induction xs with
  | nil => simp [listProd]
  | cons x xs ih => simp [listProd, ih, mul_assoc]

theorem dvd_refl {α : Type*} [CommMonoid α] (a : α) : a ∣ a := dvd_rfl

theorem dvd_trans {α : Type*} [CommMonoid α] {a b c : α} :
    a ∣ b → b ∣ c → a ∣ c := by
  intro hab hbc
  exact Dvd.dvd.trans hab hbc

theorem dvd_mul_of_dvd_left {α : Type*} [CommMonoid α] {a b c : α} :
    a ∣ b → a ∣ b * c := by
  intro h
  exact dvd_trans h (dvd_mul_right b c)

theorem dvd_mul_of_dvd_right {α : Type*} [CommMonoid α] {a b c : α} :
    a ∣ c → a ∣ b * c := by
  intro h
  exact dvd_trans h (dvd_mul_left c b)

theorem isUnit_one {α : Type*} [CommMonoid α] : IsUnit (1 : α) := _root_.isUnit_one

theorem isUnit_mul {α : Type*} [CommMonoid α] {a b : α} :
    IsUnit a → IsUnit b → IsUnit (a * b) := by
  intro ha hb
  exact ha.mul hb

theorem isUnit_of_dvd_one {α : Type*} [CommMonoid α] {a : α} (h : a ∣ 1) : IsUnit a :=
  _root_.isUnit_of_dvd_one h

theorem isUnit_ne_zero {α : Type*} [CommRing α] [IsDomain α] {a : α} (ha : IsUnit a) : a ≠ 0 :=
  ha.ne_zero

theorem associated_refl {α : Type*} [Monoid α] (a : α) : Associated a a := Associated.refl a

theorem associated_symm {α : Type*} [Monoid α] {a b : α} :
    Associated a b → Associated b a := Associated.symm

theorem associated_trans {α : Type*} [Monoid α] {a b c : α} :
    Associated a b → Associated b c → Associated a c := fun hab hbc => hab.trans hbc

theorem dvd_of_associated {α : Type*} [Monoid α] {a b : α} (h : Associated a b) : a ∣ b :=
  h.dvd

theorem prime_irreducible {α : Type*} [CommRing α] [IsDomain α] {p : α} (hp : Prime p) :
    Irreducible p :=
  hp.irreducible

theorem associated_of_irreducible_of_dvd {α : Type*} [CommRing α] {p q : α}
    (hp : Irreducible p) (hq : Irreducible q) (hdiv : p ∣ q) : Associated p q := by
  exact (hp.dvd_irreducible_iff_associated hq).mp hdiv

theorem prime_of_associated {α : Type*} [CommRing α] {p q : α}
    (hp : Prime p) (hassoc : Associated p q) : Prime q := by
  exact (hassoc.prime_iff).mp hp

end NagataFactoriality
