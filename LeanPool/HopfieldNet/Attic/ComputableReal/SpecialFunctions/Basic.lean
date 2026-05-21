/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Mathlib.Data.Real.Sign
import Mathlib.Data.Real.ConjExponents
import LeanPool.HopfieldNet.Tools.ComputableReal.IsComputable

namespace IsComputable

instance instComputableOfScientific (m : ℕ) (b : Bool) (e : ℕ) :
    IsComputable (@OfScientific.ofScientific ℝ NNRatCast.toOfScientific m b e) :=
  ⟨(OfScientific.ofScientific m b e : ℚ),
    ComputableℝSeq.val_ratCast.trans (Rat.cast_ofScientific m b e)⟩

--Note that if `(x y : ℝ)` comes after `Decidable`, the compiler won't drop them
-- early enough in the compilation process, and this will fail as noncomputable.
instance instComputableDite (p : Prop) (x : p → ℝ) (y : ¬p → ℝ) [Decidable p]
    [hx : ∀ p, IsComputable (x p)] [hy : ∀ p, IsComputable (y p)]
    : IsComputable (dite p x y) :=
  if h : p then lift_eq (by simp [h]) (hx h) else lift_eq (by simp [h]) (hy h)

@[inline]
instance instComputableIte (p : Prop) (x y : ℝ) [Decidable p]
    [hx : IsComputable x] [hy : IsComputable y] : IsComputable (ite p x y) :=
  instComputableDite p _ _

@[inline]
noncomputable instance instComputableSign (x : ℝ) [hx : IsComputable x] : IsComputable (x.sign) :=
  ⟨hx.seq.sign,
    by
      rw [ComputableℝSeq.sign_sound, hx.prop]
      rcases lt_trichotomy x 0 with h|h|h
      · simp [Real.sign.eq_1, h]
      · simp [h]
      · simp [Real.sign.eq_1, h, not_lt_of_gt h]⟩

--TODO: This really should operate "directly" on the sequences, so that it doesn't
--require a comparison first. For instance, `max (√2 - √2) 0 < 1` will never terminate
--with this implementation.
instance instComputableMax (x y : ℝ) [hx : IsComputable x] [hy : IsComputable y] :
    IsComputable (max x y) :=
  lift_eq (x := ite (x ≤ y) ..) (by rw [max_def]; congr) inferInstance

instance instComputableMin (x y : ℝ) [hx : IsComputable x] [hy : IsComputable y] :
    IsComputable (min x y) :=
  lift_eq (x := ite (x ≤ y) ..) (by rw [min_def]; congr) inferInstance

--This ends up calling the same sequence twice (which leads to an exponential
--slowdown when many nested `abs` are present); would be good to write one that
--directly takes the abs of each interval. Also, never returns a value for
-- `abs (√2 - √2)`, for the same reasons as max.
instance instComputableAbs (x : ℝ) [hx : IsComputable x] : IsComputable |x| :=
  lift_eq (abs.eq_1 x).symm inferInstance

instance instComputableConjExponent (x : ℝ) [hx : IsComputable x] :
    IsComputable x.conjExponent :=
  lift_eq (Real.conjExponent.eq_1 x).symm inferInstance

--Again, the order of arguments matters: if the argument `xs` is moved after
-- `s`, then compilation breaks.
instance instComputableFinsetSum {ι : Type*} (xs : ι → ℝ) (s : Finset ι)
    [hxs : ∀ i, IsComputable (xs i)] : IsComputable (Finset.sum s xs) :=
  ⟨Finset.fold (· + ·) 0 (fun i ↦ (hxs i).seq) s,
     by
    rw [← Finset.sum_eq_fold]
    trans (∑ x ∈ s, (seq (xs x)).val)
    · --TODO: pull this out to be top-level theorems (that `.val` is an `AddMonoidHom`)
      exact map_sum (G := ComputableℝSeq →+ ℝ)
        ⟨⟨ComputableℝSeq.val, ComputableℝSeq.val_zero⟩, ComputableℝSeq.val_add⟩
        (fun x ↦ seq (xs x)) s
    · congr! with i hi
      exact (hxs i).prop
    ⟩

--We would like to have this for `Finset.prod` as well, but the analogous proof of that
--requires the fact that `ComputableℝSeq` multiplication is associative! Which we don't
--have at the moment.

end IsComputable

example :
    (10 / 9 : ℝ) < (15 / 2 ⊔ 3) ∧
    |(1 / 10) - (1 : ℝ)| < 1 ∧
    (if _ : 1 < 2 then 5 / 2 else 6 : ℝ) < 7 ∧
    (if [1,10].length = 2 then 5 else (10 / 7) : ℝ) / 7 < 1 ∧
    (3.5 : ℝ) < 4
    := by sorry
  --native_decide

example : (2 - 5 / 2 : ℝ).sign + 1 = 0 := by sorry
  --native_decide

example : |∑ x ∈ Finset.range 500, 1 / (x : ℝ) - 6.7908234| < 0.0000001 := by sorry
  --native_decide

/-
There's some very nasty behavior where the compiler may or may not compile something
computably, depending on the exact expression complexity.

This works:
#eval ((10 / 9 : ℝ) < (15 / 2 ⊔ 3) ∧
    |(1 / 10) - (1 : ℝ)| < 1 ∧
    (if _ : 1 < 2 then 5 / 2 else 6 : ℝ) < 7 ∧
    (if [1,10].length = 2 then 5 else (10 / 7) : ℝ) / 7 < 1 ∧
    (3.5 : ℝ) < 4)

This works:
#eval ((2 - 5 / 2 : ℝ).sign + 1 = 0)

But this doesn't:
#eval ((10 / 9 : ℝ) < (15 / 2 ⊔ 3) ∧
    |(1 / 10) - (1 : ℝ)| < 1 ∧
    (if _ : 1 < 2 then 5 / 2 else 6 : ℝ) < 7 ∧
    (if [1,10].length = 2 then 5 else (10 / 7) : ℝ) / 7 < 1 ∧
    (3.5 : ℝ) < 4 ∧
    (2 - 5 / 2 : ℝ).sign + 1 = 0)

-/
