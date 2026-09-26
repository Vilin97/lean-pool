/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.CombinatorialGames.NatOrdinal.Pow
public import Mathlib.SetTheory.Ordinal.Exponential

import Mathlib.Algebra.Order.SuccPred
import Mathlib.SetTheory.Ordinal.Principal

/-!
# Leading Cantor exponent of an ordinal

For a nonzero ordinal `o`, LM24 defines its degree to be the largest ordinal `a` such that
`Ordinal.omega0 ^ a ≤ o`; equivalently, it is the leading exponent in the Cantor normal form of
`o`. The value at zero is `⊥`, representing LM24's `-∞` convention. We call the resulting
function `Ordinal.cantorDegree` to distinguish this invariant from unrelated notions of degree.

The codomain is `WithBot NatOrdinal`: the order comes from ordinals, while addition and
multiplication on non-bottom values are Hessenberg's natural operations. This is the convention of
LM24, Sections 1.5 and 2.2.

The transported function `NatOrdinal.cantorDegree` lets the same invariant interact directly with
the dependency's Hessenberg addition and multiplication. Its arithmetic theorems formalize LM24,
Fact 2.2.2.
-/

universe u v

public noncomputable section

namespace Ordinal

/-- The leading exponent in the Cantor normal form of a nonzero ordinal, and `⊥` at zero. -/
def cantorDegree (o : Ordinal.{u}) : WithBot NatOrdinal.{u} :=
  if o = 0 then ⊥ else (NatOrdinal.of (log ω o) : WithBot NatOrdinal)

@[simp]
theorem cantorDegree_zero : cantorDegree (0 : Ordinal.{u}) = ⊥ := by
  simp [cantorDegree]

/-- Away from zero, `cantorDegree` is the ordinal logarithm in base `ω`. -/
theorem cantorDegree_of_ne_zero {o : Ordinal.{u}} (ho : o ≠ 0) :
    cantorDegree o = NatOrdinal.of (log ω o) := by
  simp [cantorDegree, ho]

@[simp]
theorem cantorDegree_eq_bot {o : Ordinal.{u}} : cantorDegree o = ⊥ ↔ o = 0 := by
  by_cases ho : o = 0
  · simp [ho]
  · simp [cantorDegree, ho]

/-- This is LM24's maximum characterization of the leading Cantor exponent. -/
theorem coe_le_cantorDegree_iff {o a : Ordinal.{u}} (ho : o ≠ 0) :
    (NatOrdinal.of a : WithBot NatOrdinal) ≤ cantorDegree o ↔ ω ^ a ≤ o := by
  rw [cantorDegree_of_ne_zero ho, WithBot.coe_le_coe, NatOrdinal.of_le_iff]
  exact (opow_le_iff_le_log one_lt_omega0 ho).symm

theorem cantorDegree_mono : Monotone (cantorDegree : Ordinal.{u} → WithBot NatOrdinal) := by
  intro a b hab
  by_cases ha : a = 0
  · simp [ha]
  have hb : b ≠ 0 := by
    intro hb
    subst b
    exact ha (bot_unique hab)
  rw [cantorDegree_of_ne_zero ha, cantorDegree_of_ne_zero hb, WithBot.coe_le_coe,
    NatOrdinal.of_le_iff]
  exact log_mono_right ω hab

/-- An ordinal has degree zero exactly when it is nonzero and finite. -/
@[simp]
theorem cantorDegree_eq_zero {o : Ordinal.{u}} :
    cantorDegree o = (0 : WithBot NatOrdinal) ↔ o ≠ 0 ∧ o < ω := by
  by_cases ho : o = 0
  · simp [ho]
  rw [cantorDegree_of_ne_zero ho]
  have hzero : (0 : WithBot NatOrdinal) = ((0 : NatOrdinal) : WithBot NatOrdinal) := rfl
  rw [hzero, WithBot.coe_eq_coe, NatOrdinal.of_eq_zero]
  constructor
  · intro hlog
    refine ⟨ho, ?_⟩
    have hlt : o < ω ^ Order.succ (0 : Ordinal) := by
      simpa only [hlog] using lt_opow_succ_log_self one_lt_omega0 o
    simpa using hlt
  · exact fun h ↦ log_eq_zero h.2

@[simp]
theorem cantorDegree_one : cantorDegree (1 : Ordinal.{u}) = 0 := by
  rw [cantorDegree_of_ne_zero one_ne_zero, log_one_right]
  rfl

@[simp]
theorem cantorDegree_omega : cantorDegree (ω : Ordinal.{u}) = 1 := by
  have hlog : log ω ω = (1 : Ordinal) := by
    simpa only [opow_one] using log_opow one_lt_omega0 (1 : Ordinal)
  rw [cantorDegree_of_ne_zero omega0_ne_zero, hlog]
  rfl

/-- The ordinary ordinal sum `ω + ω` has degree one, not degree two. -/
theorem cantorDegree_omega_add_omega :
    cantorDegree ((ω : Ordinal.{u}) + ω) = 1 := by
  have htwo : (2 : Ordinal.{u}) ≠ 0 := by
    exact OfNat.ofNat_ne_zero 2
  have hlogTwo : log ω (2 : Ordinal.{u}) = 0 :=
    log_eq_zero (natCast_lt_omega0 2)
  have hlog : log ω (ω + ω) = (1 : Ordinal) := by
    simpa only [opow_one, Ordinal.mul_two, hlogTwo, add_zero] using
      log_opow_mul one_lt_omega0 1 htwo
  have hne : (ω : Ordinal.{u}) + ω ≠ 0 := fun h ↦
    omega0_ne_zero (eq_zero_of_add_right h)
  rw [cantorDegree_of_ne_zero hne, hlog]
  rfl

/-- The ordinal `ω²` has degree two. -/
theorem cantorDegree_omega_sq :
    cantorDegree ((ω : Ordinal.{u}) ^ (2 : Ordinal)) = 2 := by
  rw [cantorDegree_of_ne_zero (opow_ne_zero 2 omega0_ne_zero),
    log_opow one_lt_omega0]
  rfl

/-! ### Finite powers of `ω` and `ω ^ ω` across universes -/

/-- Universe lifting commutes with finite powers of `ω`. -/
theorem lift_omega0_opow_natCast (n : ℕ) :
    lift.{u, v} ((ω : Ordinal.{v}) ^ (n : Ordinal)) = (ω : Ordinal.{max u v}) ^ (n : Ordinal) := by
  rw [opow_natCast, opow_natCast]
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, lift_mul, ih]

/-- Universe lifting fixes `ω ^ ω`. -/
theorem lift_omega0_opow_omega0 :
    lift.{u, v} ((ω : Ordinal.{v}) ^ (ω : Ordinal.{v})) =
      (ω : Ordinal.{max u v}) ^ (ω : Ordinal.{max u v}) := by
  apply le_antisymm
  · apply le_of_forall_lt
    intro c hc
    obtain ⟨d, hd, rfl⟩ := lt_lift_iff.mp hc
    obtain ⟨m, hm, hdm⟩ := (lt_opow_of_isSuccLimit omega0_ne_zero isSuccLimit_omega0).mp hd
    obtain ⟨n, rfl⟩ := lt_omega0.mp hm
    calc
      lift.{u, v} d < lift.{u, v} ((ω : Ordinal.{v}) ^ (n : Ordinal)) := lift_lt.mpr hdm
      _ = (ω : Ordinal.{max u v}) ^ (n : Ordinal) := lift_omega0_opow_natCast n
      _ < ω ^ ω := (opow_lt_opow_iff_right one_lt_omega0).mpr (natCast_lt_omega0 n)
  · apply le_of_forall_lt
    intro c hc
    obtain ⟨m, hm, hcm⟩ := (lt_opow_of_isSuccLimit omega0_ne_zero isSuccLimit_omega0).mp hc
    obtain ⟨n, rfl⟩ := lt_omega0.mp hm
    calc
      c < (ω : Ordinal.{max u v}) ^ (n : Ordinal) := hcm
      _ = lift.{u, v} ((ω : Ordinal.{v}) ^ (n : Ordinal)) := (lift_omega0_opow_natCast n).symm
      _ ≤ lift.{u, v} ((ω : Ordinal.{v}) ^ (ω : Ordinal.{v})) :=
        lift_le.mpr ((opow_lt_opow_iff_right one_lt_omega0).mpr (natCast_lt_omega0 n)).le

/-- Finite powers of `ω` lie below `ω ^ ω`. -/
theorem omega0_opow_natCast_lt_omega0_opow_omega0 (n : ℕ) :
    (ω : Ordinal.{u}) ^ (n : Ordinal) < ω ^ ω :=
  (opow_lt_opow_iff_right one_lt_omega0).mpr (natCast_lt_omega0 n)

/-- One more than a finite power of `ω` still lies below `ω ^ ω`; this is the support order type
of a series with `ω ^ n` terms followed by one constant term. -/
theorem omega0_opow_natCast_add_one_lt_omega0_opow_omega0 (n : ℕ) :
    (ω : Ordinal.{u}) ^ (n : Ordinal) + 1 < ω ^ ω :=
  isPrincipal_add_omega0_opow ω (omega0_opow_natCast_lt_omega0_opow_omega0 n)
    (one_lt_opow.mpr ⟨one_lt_omega0, omega0_ne_zero⟩)

end Ordinal

namespace NatOrdinal

/-- The leading Cantor exponent of a natural ordinal, with value `⊥` at zero. -/
def cantorDegree (a : NatOrdinal.{u}) : WithBot NatOrdinal.{u} :=
  Ordinal.cantorDegree a.val

/-- `NatOrdinal.cantorDegree` is `Ordinal.cantorDegree` transported along `NatOrdinal.val`. -/
theorem cantorDegree_eq_ordinalCantorDegree (a : NatOrdinal.{u}) :
    cantorDegree a = Ordinal.cantorDegree a.val :=
  (rfl)

/-- Transporting an ordinal into `NatOrdinal` does not change its leading Cantor exponent. -/
@[simp]
theorem cantorDegree_of (a : Ordinal.{u}) :
    cantorDegree (of a) = Ordinal.cantorDegree a :=
  (rfl)

@[simp]
theorem cantorDegree_zero : cantorDegree (0 : NatOrdinal.{u}) = ⊥ := by
  rw [cantorDegree_eq_ordinalCantorDegree, val_zero, Ordinal.cantorDegree_zero]

@[simp]
theorem cantorDegree_eq_bot {a : NatOrdinal.{u}} : cantorDegree a = ⊥ ↔ a = 0 := by
  rw [cantorDegree_eq_ordinalCantorDegree, Ordinal.cantorDegree_eq_bot]
  exact val_eq_zero

/-- Away from zero, `NatOrdinal.cantorDegree` is the ordinal logarithm in base `ω`. -/
theorem cantorDegree_of_ne_zero {a : NatOrdinal.{u}} (ha : a ≠ 0) :
    cantorDegree a = (of (Ordinal.log Ordinal.omega0 a.val) : WithBot NatOrdinal) := by
  rw [cantorDegree_eq_ordinalCantorDegree, Ordinal.cantorDegree_of_ne_zero]
  exact val_ne_zero.mpr ha

/-- The leading Cantor exponent of `ω` raised to a natural ordinal is that ordinal. -/
@[simp]
theorem cantorDegree_wpow (a : NatOrdinal.{u}) :
    cantorDegree (ω^ a) = (a : WithBot NatOrdinal) := by
  rw [cantorDegree_of_ne_zero (wpow_ne_zero a), WithBot.coe_eq_coe,
    val_wpow, Ordinal.log_opow Ordinal.one_lt_omega0]
  exact of_val a

/-- An ordinal's leading Cantor exponent is at most `d` exactly when the ordinal lies below the
next power of `ω`. The statement includes the zero ordinal through the bottom convention. -/
theorem cantorDegree_le_coe_iff (a d : NatOrdinal.{u}) :
    cantorDegree a ≤ (d : WithBot NatOrdinal) ↔ a < ω^ (d + 1) := by
  by_cases ha : a = 0
  · simp [ha, wpow_pos]
  rw [cantorDegree_of_ne_zero ha, WithBot.coe_le_coe, of_le_iff,
    ← val.lt_iff_lt]
  simp only [val_wpow, val_add_one]
  rw [Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0
    (val_ne_zero.mpr ha), ← Order.succ_eq_add_one, Order.lt_succ_iff]

/-- An ordinal's leading Cantor exponent is strictly below `d` exactly when the ordinal lies
below `ω^d`. The statement includes the zero ordinal through the bottom convention. -/
theorem cantorDegree_lt_coe_iff (a d : NatOrdinal.{u}) :
    cantorDegree a < (d : WithBot NatOrdinal) ↔ a < ω^ d := by
  by_cases ha : a = 0
  · simp [ha, wpow_pos]
  rw [cantorDegree_of_ne_zero ha, WithBot.coe_lt_coe, of_lt_iff,
    ← val.lt_iff_lt]
  simp only [val_wpow]
  exact (Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0
    (val_ne_zero.mpr ha)).symm

/-- The degree of a Hessenberg sum is the maximum of the degrees. This is LM24, Fact 2.2.2(1),
with the equality noted parenthetically in the paper. -/
theorem cantorDegree_add (a b : NatOrdinal.{u}) :
    cantorDegree (a + b) = max (cantorDegree a) (cantorDegree b) := by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  obtain rfl | hb := eq_or_ne b 0
  · simp
  have hab : a + b ≠ 0 := by simp [ha, hb]
  rw [cantorDegree_of_ne_zero hab, cantorDegree_of_ne_zero ha,
    cantorDegree_of_ne_zero hb, ← WithBot.coe_max, WithBot.coe_eq_coe]
  let da : NatOrdinal := of (Ordinal.log Ordinal.omega0 a.val)
  let db : NatOrdinal := of (Ordinal.log Ordinal.omega0 b.val)
  change of (Ordinal.log Ordinal.omega0 (a + b).val) = max da db
  apply le_antisymm
  · rw [← Order.lt_succ_iff, Order.succ_eq_add_one]
    have ha_lt : a < ω^ (da + 1) := by
      apply val.lt_iff_lt.mp
      simp only [val_wpow, val_add_one, da, val_of]
      exact Ordinal.lt_opow_succ_log_self Ordinal.one_lt_omega0 a.val
    have hb_lt : b < ω^ (db + 1) := by
      apply val.lt_iff_lt.mp
      simp only [val_wpow, val_add_one, db, val_of]
      exact Ordinal.lt_opow_succ_log_self Ordinal.one_lt_omega0 b.val
    have ha_max : a < ω^ (max da db + 1) :=
      ha_lt.trans_le (wpow_le_wpow.mpr (add_le_add (le_max_left da db) le_rfl))
    have hb_max : b < ω^ (max da db + 1) :=
      hb_lt.trans_le (wpow_le_wpow.mpr (add_le_add (le_max_right da db) le_rfl))
    have hab_lt : a + b < ω^ (max da db + 1) := add_lt_wpow ha_max hb_max
    apply val.lt_iff_lt.mp
    apply (Ordinal.lt_opow_iff_log_lt' Ordinal.one_lt_omega0 (by simp)).mp
    simpa only [val_wpow] using val.lt_iff_lt.mpr hab_lt
  · apply max_le
    · exact of.monotone
        (Ordinal.log_mono_right Ordinal.omega0 (val.monotone le_add_right))
    · exact of.monotone
        (Ordinal.log_mono_right Ordinal.omega0 (val.monotone le_add_left))

/-- The degree of a Hessenberg sum is at most the maximum of the degrees. This is the inequality
printed as LM24, Fact 2.2.2(1). -/
theorem cantorDegree_add_le (a b : NatOrdinal.{u}) :
    cantorDegree (a + b) ≤ max (cantorDegree a) (cantorDegree b) :=
  (cantorDegree_add a b).le

/-- The degree of a Hessenberg product is the Hessenberg sum of the degrees. This is LM24,
Fact 2.2.2(2), including the paper's absorbing convention for `⊥`. -/
theorem cantorDegree_mul (a b : NatOrdinal.{u}) :
    cantorDegree (a * b) = cantorDegree a + cantorDegree b := by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  obtain rfl | hb := eq_or_ne b 0
  · simp
  have hab : a * b ≠ 0 :=
    (mul_pos (pos_iff_ne_zero.mpr ha) (pos_iff_ne_zero.mpr hb)).ne'
  rw [cantorDegree_of_ne_zero hab, cantorDegree_of_ne_zero ha,
    cantorDegree_of_ne_zero hb, ← WithBot.coe_add, WithBot.coe_eq_coe]
  let da : NatOrdinal := of (Ordinal.log Ordinal.omega0 a.val)
  let db : NatOrdinal := of (Ordinal.log Ordinal.omega0 b.val)
  change of (Ordinal.log Ordinal.omega0 (a * b).val) = da + db
  apply le_antisymm
  · rw [← Order.lt_succ_iff, Order.succ_eq_add_one]
    have ha_lt : a < ω^ (da + 1) := by
      apply val.lt_iff_lt.mp
      simp only [val_wpow, val_add_one, da, val_of]
      exact Ordinal.lt_opow_succ_log_self Ordinal.one_lt_omega0 a.val
    have hb_lt : b < ω^ (db + 1) := by
      apply val.lt_iff_lt.mp
      simp only [val_wpow, val_add_one, db, val_of]
      exact Ordinal.lt_opow_succ_log_self Ordinal.one_lt_omega0 b.val
    obtain ⟨n, han⟩ := lt_wpow_add_one_iff.mp ha_lt
    obtain ⟨m, hbm⟩ := lt_wpow_add_one_iff.mp hb_lt
    have hab_lt : a * b < ω^ (da + db + 1) := by
      calc
        a * b < (ω^ da * n) * (ω^ db * m) :=
          mul_lt_mul_of_pos han hbm (pos_iff_ne_zero.mpr ha)
            ((pos_iff_ne_zero.mpr hb).trans hbm)
        _ = ω^ (da + db) * ((n * m : ℕ) : NatOrdinal) := by
          rw [mul_mul_mul_comm, ← Nat.cast_mul, ← wpow_add]
        _ < ω^ (da + db + 1) := wpow_mul_natCast_lt (lt_add_one _) (n * m)
    apply val.lt_iff_lt.mp
    apply (Ordinal.lt_opow_iff_log_lt' Ordinal.one_lt_omega0 (by simp)).mp
    simpa only [val_wpow] using val.lt_iff_lt.mpr hab_lt
  · have hwa : ω^ da ≤ a := by
      apply val.le_iff_le.mp
      simp only [val_wpow, da, val_of]
      exact Ordinal.opow_log_le_self Ordinal.omega0 (val_ne_zero.mpr ha)
    have hwb : ω^ db ≤ b := by
      apply val.le_iff_le.mp
      simp only [val_wpow, db, val_of]
      exact Ordinal.opow_log_le_self Ordinal.omega0 (val_ne_zero.mpr hb)
    have hleading : ω^ (da + db) ≤ a * b := by
      rw [wpow_add]
      exact mul_le_mul hwa hwb bot_le bot_le
    apply val_le_iff.mp
    apply (Ordinal.opow_le_iff_le_log Ordinal.one_lt_omega0
      (val_ne_zero.mpr hab)).mp
    simpa only [val_wpow] using val.monotone hleading

end NatOrdinal
