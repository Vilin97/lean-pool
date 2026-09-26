/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.CombinatorialGames.NatOrdinal.Pow
public import Mathlib.SetTheory.Ordinal.CantorNormalForm

/-!
# Finite Cantor coefficients of natural ordinals

The constant Cantor coefficient of an ordinal is the coefficient of `ω ^ 0` in its Cantor
normal form. For a natural ordinal, this coefficient is a natural number. This module defines it
as the remainder after ordinal division by `ω` and proves that this agrees with Mathlib's Cantor
normal form.

The complementary `limitPart` is divisible by `ω`. When `n` does not exceed the constant
coefficient, `removeNat a n` removes exactly `n` copies of the constant term; it is characterized
as the unique natural ordinal `b` satisfying `b + n = a`, where addition is Hessenberg addition.

The final estimate bounds a Hessenberg product of two ordinals of finite Cantor degree. These
elementary facts support finite-degree arguments built on the LM24 degree and graded-ring
machinery.
-/

universe u

public noncomputable section

namespace Ordinal.CNF

/-- The coefficient of `ω ^ 0` in the Cantor normal form of `a` is the remainder of `a` modulo
`ω`. -/
theorem coeff_omega0_zero (a : Ordinal.{u}) :
    coeff Ordinal.omega0 a 0 = a % Ordinal.omega0 := by
  refine Ordinal.CNF.rec Ordinal.omega0 ?_ (fun o ho IH ↦ ?_) a
  · simp
  by_cases he : Ordinal.log Ordinal.omega0 o = 0
  · have ho_lt : o < Ordinal.omega0 := by
      by_contra h
      have hlog := Ordinal.log_pos Ordinal.one_lt_omega0 ho (le_of_not_gt h)
      exact (ne_of_gt hlog) he
    have hmem : (0, o) ∈ Ordinal.CNF Ordinal.omega0 o := by
      rw [Ordinal.CNF.of_lt ho ho_lt]
      simp
    rw [coeff_of_mem_CNF hmem, Ordinal.mod_eq_of_lt ho_lt]
  · have hx : o / Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 o ≠ 0 :=
      (Ordinal.div_opow_log_pos Ordinal.omega0 ho).ne'
    have hcoeff := coeff_opow_mul_add
      (b := Ordinal.omega0) (e := Ordinal.log Ordinal.omega0 o)
      (x := o / Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 o)
      (y := o % Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 o)
      Ordinal.one_lt_omega0 hx
      (Ordinal.div_opow_log_lt o Ordinal.one_lt_omega0)
      (Ordinal.mod_lt o <| Ordinal.opow_ne_zero
        (Ordinal.log Ordinal.omega0 o) Ordinal.omega0_ne_zero)
    have hdecomp := Ordinal.div_add_mod o
      (Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 o)
    have hcoeff_zero :
        coeff Ordinal.omega0 o 0 =
          coeff Ordinal.omega0
            (o % Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 o) 0 := by
      calc
        coeff Ordinal.omega0 o 0 =
            coeff Ordinal.omega0
              (Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 o *
                  (o / Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 o) +
                o % Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 o) 0 :=
          congrArg (fun z ↦ coeff Ordinal.omega0 z 0) hdecomp.symm
        _ = coeff Ordinal.omega0
              (o % Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 o) 0 := by
          rw [hcoeff]
          simp [he]
    rw [hcoeff_zero, IH]
    apply Ordinal.mod_mod_of_dvd
    simpa using Ordinal.opow_dvd_opow Ordinal.omega0
      (Order.one_le_iff_ne_zero.mpr he)

end Ordinal.CNF

namespace NatOrdinal

/-- The coefficient of `ω ^ 0` in the Cantor normal form of a natural ordinal. -/
def constantCoeff (a : NatOrdinal.{u}) : ℕ :=
  Classical.choose <| Ordinal.lt_omega0.mp <|
    Ordinal.mod_lt a.val Ordinal.omega0_ne_zero

/-- The constant Cantor coefficient, coerced to an ordinal, is the remainder modulo `ω`. -/
@[simp]
theorem coe_constantCoeff (a : NatOrdinal.{u}) :
    (a.constantCoeff : Ordinal) = a.val % Ordinal.omega0 := by
  exact (Classical.choose_spec (Ordinal.lt_omega0.mp <|
    Ordinal.mod_lt a.val Ordinal.omega0_ne_zero)).symm

/-- `constantCoeff` agrees with Mathlib's coefficient at exponent zero in Cantor normal form. -/
theorem coe_constantCoeff_eq_CNF_coeff (a : NatOrdinal.{u}) :
    (a.constantCoeff : Ordinal) = Ordinal.CNF.coeff Ordinal.omega0 a.val 0 := by
  rw [coe_constantCoeff, Ordinal.CNF.coeff_omega0_zero]

@[simp]
theorem constantCoeff_zero : (0 : NatOrdinal.{u}).constantCoeff = 0 := by
  apply Nat.cast_injective (R := Ordinal)
  rw [coe_constantCoeff]
  simp

/-- The part of a natural ordinal whose constant Cantor coefficient is zero. -/
def limitPart (a : NatOrdinal.{u}) : NatOrdinal.{u} :=
  NatOrdinal.of (Ordinal.omega0 * (a.val / Ordinal.omega0))

/-- A natural ordinal is the Hessenberg sum of its limit part and constant coefficient. -/
theorem limitPart_add_constantCoeff (a : NatOrdinal.{u}) :
    a.limitPart + a.constantCoeff = a := by
  apply NatOrdinal.val.injective
  rw [limitPart, val_add_natCast, val_of, coe_constantCoeff]
  exact Ordinal.div_add_mod a.val Ordinal.omega0

/-- A natural ordinal is a successor prelimit exactly when its constant Cantor coefficient
vanishes. -/
theorem isSuccPrelimit_iff_constantCoeff_eq_zero (a : NatOrdinal.{u}) :
    Order.IsSuccPrelimit a ↔ a.constantCoeff = 0 := by
  change Order.IsSuccPrelimit a.val ↔ _
  rw [Ordinal.isSuccPrelimit_iff_omega0_dvd,
    Ordinal.dvd_iff_mod_eq_zero, ← coe_constantCoeff]
  norm_cast

/-- A positive power of `ω` has zero constant Cantor coefficient. -/
theorem constantCoeff_wpow {a : NatOrdinal.{u}} (ha : a ≠ 0) :
    (ω^ a).constantCoeff = 0 := by
  rw [← isSuccPrelimit_iff_constantCoeff_eq_zero]
  change Order.IsSuccPrelimit (ω^ a).val
  rw [NatOrdinal.val_wpow, Ordinal.isSuccPrelimit_iff_omega0_dvd]
  have hval : a.val ≠ 0 := by
    intro hval
    apply ha
    apply NatOrdinal.val.injective
    simpa using hval
  simpa only [Ordinal.opow_one] using
    Ordinal.opow_dvd_opow Ordinal.omega0
      (Order.one_le_iff_ne_zero.mpr hval)

/-- The Hessenberg sum of two successor prelimits is a successor prelimit. -/
theorem isSuccPrelimit_add {a b : NatOrdinal.{u}}
    (ha : Order.IsSuccPrelimit a) (hb : Order.IsSuccPrelimit b) :
    Order.IsSuccPrelimit (a + b) := by
  rw [Order.isSuccPrelimit_iff_succ_lt]
  intro c hc
  rcases NatOrdinal.lt_add_iff.mp hc with
    ⟨a', ha', hca⟩ | ⟨b', hb', hcb⟩
  · calc
      Order.succ c ≤ Order.succ (a' + b) := Order.succ_mono hca
      _ = (a' + b) + 1 := Order.succ_eq_add_one _
      _ = (a' + 1) + b := by ac_rfl
      _ < a + b := by
        simpa [add_comm] using add_lt_add_right (ha.add_one_lt ha') b
  · calc
      Order.succ c ≤ Order.succ (a + b') := Order.succ_mono hcb
      _ = (a + b') + 1 := Order.succ_eq_add_one _
      _ = a + (b' + 1) := by ac_rfl
      _ < a + b := by
        simpa [add_comm] using add_lt_add_left (hb.add_one_lt hb') a

/-- The limit part of a natural ordinal is a successor prelimit. -/
theorem isSuccPrelimit_limitPart (a : NatOrdinal.{u}) :
    Order.IsSuccPrelimit a.limitPart := by
  rw [isSuccPrelimit_iff_constantCoeff_eq_zero]
  apply Nat.cast_injective (R := Ordinal)
  rw [coe_constantCoeff, limitPart, val_of, Ordinal.mul_mod]
  simp

/-- Adding a finite natural ordinal adds it to the constant Cantor coefficient. -/
theorem constantCoeff_add_natCast (a : NatOrdinal.{u}) (n : ℕ) :
    (a + n).constantCoeff = a.constantCoeff + n := by
  apply Nat.cast_injective (R := Ordinal)
  rw [coe_constantCoeff, val_add_natCast, Nat.cast_add, coe_constantCoeff]
  nth_rw 1 [← Ordinal.div_add_mod a.val Ordinal.omega0]
  rw [add_assoc, Ordinal.mul_add_mod_self,
    Ordinal.mod_eq_of_lt
      (Ordinal.isSuccLimit_omega0.add_natCast_lt
        (Ordinal.mod_lt a.val Ordinal.omega0_ne_zero) n)]

/-- The constant Cantor coefficient of a finite natural ordinal is that natural number. -/
@[simp]
theorem constantCoeff_natCast (n : ℕ) :
    (n : NatOrdinal.{u}).constantCoeff = n := by
  simpa using constantCoeff_add_natCast (0 : NatOrdinal.{u}) n

/-- Hessenberg addition adds constant Cantor coefficients. -/
theorem constantCoeff_add (a b : NatOrdinal.{u}) :
    (a + b).constantCoeff = a.constantCoeff + b.constantCoeff := by
  have hbase : Order.IsSuccPrelimit (a.limitPart + b.limitPart) :=
    isSuccPrelimit_add (isSuccPrelimit_limitPart a) (isSuccPrelimit_limitPart b)
  have hzero : (a.limitPart + b.limitPart).constantCoeff = 0 :=
    (isSuccPrelimit_iff_constantCoeff_eq_zero _).mp hbase
  have hdecomp :
      a + b = (a.limitPart + b.limitPart) +
        (a.constantCoeff + b.constantCoeff : ℕ) := by
    calc
      a + b = (a.limitPart + a.constantCoeff) +
          (b.limitPart + b.constantCoeff) := by
        rw [limitPart_add_constantCoeff, limitPart_add_constantCoeff]
      _ = (a.limitPart + b.limitPart) +
          (a.constantCoeff + b.constantCoeff : ℕ) := by
        rw [Nat.cast_add]
        ac_rfl
  rw [hdecomp, constantCoeff_add_natCast, hzero, zero_add]

/-- Remove `n` copies of the constant Cantor term. This operation represents finite ordinal
predecessor only under the hypothesis `n ≤ a.constantCoeff`. -/
def removeNat (a : NatOrdinal.{u}) (n : ℕ) : NatOrdinal.{u} :=
  a.limitPart + (a.constantCoeff - n : ℕ)

/-- Removing `n` copies of the constant term subtracts `n` from the constant coefficient. -/
theorem constantCoeff_removeNat (a : NatOrdinal.{u}) (n : ℕ) :
    (a.removeNat n).constantCoeff = a.constantCoeff - n := by
  rw [removeNat, constantCoeff_add_natCast,
    (isSuccPrelimit_iff_constantCoeff_eq_zero _).mp
      (isSuccPrelimit_limitPart a), zero_add]

/-- If `n` does not exceed the constant coefficient, adding `n` after removing it recovers the
original natural ordinal. -/
theorem removeNat_add_natCast {a : NatOrdinal.{u}} {n : ℕ}
    (hn : n ≤ a.constantCoeff) : a.removeNat n + n = a := by
  rw [removeNat]
  calc
    a.limitPart + ↑(a.constantCoeff - n) + ↑n =
        a.limitPart + ↑((a.constantCoeff - n) + n) := by
      rw [Nat.cast_add]
      ac_rfl
    _ = a.limitPart + a.constantCoeff := by rw [Nat.sub_add_cancel hn]
    _ = a := limitPart_add_constantCoeff a

/-- Removing zero copies of the constant term leaves a natural ordinal unchanged. -/
@[simp]
theorem removeNat_zero (a : NatOrdinal.{u}) : a.removeNat 0 = a := by
  simpa using removeNat_add_natCast (a := a) (n := 0) (Nat.zero_le a.constantCoeff)

/-- Finite removal is the unique solution to addition by the removed natural ordinal. -/
theorem eq_removeNat_iff_add_natCast_eq {a eta : NatOrdinal.{u}} {n : ℕ}
    (hn : n ≤ a.constantCoeff) : eta = a.removeNat n ↔ eta + n = a := by
  constructor
  · rintro rfl
    exact removeNat_add_natCast hn
  · intro heta
    apply add_right_cancel (b := (n : NatOrdinal))
    rw [heta, removeNat_add_natCast hn]

/-- Removing a finite constant term from the left summand commutes with adding a right summand. -/
theorem removeNat_add_right (a b : NatOrdinal.{u}) {n : ℕ}
    (hn : n ≤ a.constantCoeff) :
    (a + b).removeNat n = a.removeNat n + b := by
  apply add_right_cancel (b := (n : NatOrdinal))
  rw [removeNat_add_natCast (hn.trans <| by
    rw [constantCoeff_add]
    exact Nat.le_add_right _ _)]
  symm
  calc
    a.removeNat n + b + n = a.removeNat n + n + b := by ac_rfl
    _ = a + b := by rw [removeNat_add_natCast hn]

/-- Finite predecessor in the left summand commutes with adding a right summand. -/
theorem removeOne_add_right (a b : NatOrdinal.{u}) (ha : 0 < a.constantCoeff) :
    (a + b).removeNat 1 = a.removeNat 1 + b :=
  removeNat_add_right a b ha

/-- If `a < ω ^ (p + 1)` and `b < ω ^ (q + 1)`, then their Hessenberg product is less than
`ω ^ (p + q + 1)`. -/
theorem mul_lt_wpow_natCast_add_one {a b : NatOrdinal.{u}} {p q : ℕ}
    (ha : a < ω^ ((p + 1 : ℕ) : NatOrdinal))
    (hb : b < ω^ ((q + 1 : ℕ) : NatOrdinal)) :
    a * b < ω^ ((p + q + 1 : ℕ) : NatOrdinal) := by
  have ha' : a < ω^ ((p : NatOrdinal) + 1) := by simpa using ha
  have hb' : b < ω^ ((q : NatOrdinal) + 1) := by simpa using hb
  obtain ⟨n, han⟩ := NatOrdinal.lt_wpow_add_one_iff.mp ha'
  obtain ⟨m, hbm⟩ := NatOrdinal.lt_wpow_add_one_iff.mp hb'
  by_cases haZero : a = 0
  · subst a
    simp
  by_cases hbZero : b = 0
  · subst b
    simp
  have hnZero : n ≠ 0 := by
    intro hn
    subst n
    simp at han
  have hboundPos : 0 < ω^ (p : NatOrdinal) * n := by
    apply mul_pos (NatOrdinal.wpow_pos _)
    exact_mod_cast Nat.pos_of_ne_zero hnZero
  have hproduct :
      a * b < (ω^ (p : NatOrdinal) * n) * (ω^ (q : NatOrdinal) * m) := by
    calc
      a * b < (ω^ (p : NatOrdinal) * n) * b :=
        mul_lt_mul_of_pos_right han (pos_iff_ne_zero.mpr hbZero)
      _ < (ω^ (p : NatOrdinal) * n) * (ω^ (q : NatOrdinal) * m) :=
        mul_lt_mul_of_pos_left hbm hboundPos
  have hrewrite :
      (ω^ (p : NatOrdinal) * n) * (ω^ (q : NatOrdinal) * m) =
        ω^ ((p + q : ℕ) : NatOrdinal) * (n * m) := by
    rw [Nat.cast_add, NatOrdinal.wpow_add]
    ac_rfl
  rw [hrewrite] at hproduct
  have hnext :
      ω^ ((p + q : ℕ) : NatOrdinal) * (n * m : ℕ) <
        ω^ ((p + q + 1 : ℕ) : NatOrdinal) := by
    apply NatOrdinal.wpow_mul_natCast_lt
    exact_mod_cast Nat.lt_succ_self (p + q)
  exact hproduct.trans (by simpa only [Nat.cast_mul] using hnext)

/-- The constant Cantor coefficient of an `r`-fold Hessenberg sum is `r` times the constant
Cantor coefficient. -/
theorem constantCoeff_nsmul (r : ℕ) (alpha : NatOrdinal.{u}) :
    (r • alpha).constantCoeff = r * alpha.constantCoeff := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [succ_nsmul, constantCoeff_add, ih, Nat.succ_mul]

/-- For a natural ordinal with positive constant Cantor coefficient, removing one constant term
from an `r`-fold Hessenberg sum removes it from a single summand. -/
theorem removeNat_one_nsmul {alpha : NatOrdinal.{u}}
    (halpha : 0 < alpha.constantCoeff) {r : ℕ} (hr : 1 ≤ r) :
    alpha.removeNat 1 + (r - 1) • alpha = (r • alpha).removeNat 1 := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hcc : 1 ≤ ((s + 1) • alpha).constantCoeff := by
    rw [constantCoeff_nsmul]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  rw [eq_removeNat_iff_add_natCast_eq hcc]
  have hsimp : s + 1 - 1 = s := by omega
  rw [hsimp]
  calc
    alpha.removeNat 1 + s • alpha + ((1 : ℕ) : NatOrdinal)
        = (alpha.removeNat 1 + ((1 : ℕ) : NatOrdinal)) + s • alpha := by ac_rfl
    _ = alpha + s • alpha := by rw [removeNat_add_natCast halpha]
    _ = (s + 1) • alpha := by rw [succ_nsmul, add_comm]

/-- Removing one constant term and then `j - 1` further ones removes `j` constant terms. -/
theorem removeNat_one_removeNat_pred {delta : NatOrdinal.{u}} {j : ℕ}
    (hjpos : 1 ≤ j) (hj : j ≤ delta.constantCoeff) :
    (delta.removeNat 1).removeNat (j - 1) = delta.removeNat j := by
  have hone : 1 ≤ delta.constantCoeff := hjpos.trans hj
  have hpred : j - 1 ≤ (delta.removeNat 1).constantCoeff := by
    rw [constantCoeff_removeNat]
    omega
  have hsplit : ((j : ℕ) : NatOrdinal) =
      ((j - 1 : ℕ) : NatOrdinal) + ((1 : ℕ) : NatOrdinal) := by
    rw [← Nat.cast_add]
    congr 1
    omega
  rw [eq_removeNat_iff_add_natCast_eq hj, hsplit, ← add_assoc,
    removeNat_add_natCast hpred, removeNat_add_natCast hone]

end NatOrdinal
