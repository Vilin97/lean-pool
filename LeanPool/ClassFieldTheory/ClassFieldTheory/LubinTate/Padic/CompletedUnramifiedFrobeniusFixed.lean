/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.FieldTheory.Finite.Basic
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedUnramifiedField
/-!
# Fixed points of p-adic completed-unramified Frobenius

Witt Frobenius on `W(AlgebraicClosure (ZMod p))` has exactly the canonical
copy of `ℤ_[p]` as its fixed ring.  Passing to fraction fields shows that
the arithmetic Frobenius on the completed maximal-unramified coefficient
field has exactly the canonical copy of `ℚ_[p]` as its fixed field.

The fraction-field argument is integral: after writing a denominator as a
power of `p` times a unit, multiplication by that power of `p` puts a fixed
fraction back in the Witt ring.
-/

@[expose] public section

noncomputable
section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp

/-- The fixed ring of Witt Frobenius on the completed-unramified Witt
ring is the canonical image of the p-adic integers. -/
theorem padicCompletedUnramifiedWittRing_frobenius_fixed_iff
    (p : ℕ) [Fact p.Prime]
    (x : padicCompletedUnramifiedWittRing p) :
    WittVector.frobenius x = x ↔
      ∃ z : ℤ_[p],
        padicIntToCompletedUnramifiedWittRing p z = x := by
  constructor
  · intro hx
    have hcoeffPow (n : ℕ) :
        (x.coeff n) ^ p = x.coeff n := by
      rw [← WittVector.coeff_frobenius_charP]
      exact congrArg (fun y : padicCompletedUnramifiedWittRing p ↦ y.coeff n) hx
    have hcoeffInt (n : ℕ) :
        ∃ a : ℤ, (a : AlgebraicClosure (ZMod p)) = x.coeff n := by
      apply
        (mem_bot_iff_intCast p (AlgebraicClosure (ZMod p))).1
      exact
        (Subfield.mem_bot_iff_pow_eq_self
          (AlgebraicClosure (ZMod p)) p).2
          (hcoeffPow n)
    let c : ℕ → ℤ := fun n ↦ Classical.choose (hcoeffInt n)
    let y : WittVector p (ZMod p) :=
      WittVector.mk p (fun n ↦ (c n : ZMod p))
    refine ⟨WittVector.equiv p y, ?_⟩
    apply WittVector.ext
    intro n
    change
      (WittVector.map
          (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
          ((WittVector.equiv p).symm (WittVector.equiv p y))).coeff n =
        x.coeff n
    rw [WittVector.map_coeff, RingEquiv.symm_apply_apply]
    change
      algebraMap (ZMod p) (AlgebraicClosure (ZMod p))
          (c n : ZMod p) = x.coeff n
    calc
      _ = (c n : AlgebraicClosure (ZMod p)) := by
        simp only [map_intCast]
      _ = x.coeff n := by
        simpa only [c] using
          (Classical.choose_spec (hcoeffInt n))
  · rintro ⟨z, rfl⟩
    exact padicIntToCompletedUnramifiedWittRing_frobenius p z

/-- The fixed field of completed-unramified arithmetic Frobenius is the
canonical image of `ℚ_[p]`. -/
theorem padicCompletedUnramifiedFrobenius_fixed_iff
    (p : ℕ) [Fact p.Prime]
    (x : padicCompletedUnramifiedField p) :
    padicCompletedUnramifiedFrobenius p x = x ↔
      ∃ q : ℚ_[p],
        algebraMap ℚ_[p] (padicCompletedUnramifiedField p) q = x := by
  let W := padicCompletedUnramifiedWittRing p
  let E := padicCompletedUnramifiedField p
  let φ := padicCompletedUnramifiedFrobenius p
  constructor
  · intro hx
    obtain ⟨a, b, hb, hab⟩ :=
      IsFractionRing.div_surjective (A := W) x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    obtain ⟨m, u, hbu⟩ :=
      WittVector.exists_eq_pow_p_mul' b hb0
    let c : W := a * (u⁻¹ : Wˣ)
    have hpW : (p : W) ≠ 0 := by
      exact
        WittVector.p_nonzero p
          (AlgebraicClosure (ZMod p))
    have hpE :
        algebraMap W E ((p : W) ^ m) ≠ 0 := by
      simpa only [map_zero] using
        (IsFractionRing.injective W E).ne
          (pow_ne_zero m hpW)
    have huE :
        algebraMap W E (u : W) ≠ 0 := by
      simpa only [map_zero] using
        (IsFractionRing.injective W E).ne u.ne_zero
    have hbE :
        algebraMap W E b ≠ 0 := by
      simpa only [map_zero] using
        (IsFractionRing.injective W E).ne hb0
    have hclear :
        algebraMap W E c =
          algebraMap W E ((p : W) ^ m) * x := by
      rw [show
        algebraMap W E c =
            algebraMap W E a *
              (algebraMap W E (u : W))⁻¹ by
          simp only [c, map_mul, map_units_inv]]
      rw [← div_eq_mul_inv]
      apply (div_eq_iff huE).2
      have habMul :
          algebraMap W E a =
            x * algebraMap W E b :=
        (div_eq_iff hbE).1 hab
      rw [hbu, map_mul] at habMul
      calc
        algebraMap W E a =
            x *
              (algebraMap W E ((p : W) ^ m) *
                algebraMap W E (u : W)) :=
          habMul
        _ =
            (algebraMap W E ((p : W) ^ m) * x) *
              algebraMap W E (u : W) := by
          ac_rfl
    have hpBase :
        algebraMap W E (p : W) =
          algebraMap ℚ_[p] E (p : ℚ_[p]) := by
      calc
        algebraMap W E (p : W) =
            algebraMap W E
              (padicIntToCompletedUnramifiedWittRing p
                (p : ℤ_[p])) := by
          exact congrArg (algebraMap W E)
            (map_natCast
              (padicIntToCompletedUnramifiedWittRing p) p).symm
        _ =
            algebraMap ℚ_[p] E
              (algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p])) :=
          (padicCompletedUnramifiedField_algebraMap_padicInt
            p (p : ℤ_[p])).symm
        _ = algebraMap ℚ_[p] E (p : ℚ_[p]) := by
          exact congrArg (algebraMap ℚ_[p] E)
            (map_natCast (algebraMap ℤ_[p] ℚ_[p]) p)
    have hpowBridge :
        algebraMap W E ((p : W) ^ m) =
          (p : E) ^ m := by
      calc
        algebraMap W E ((p : W) ^ m) =
            (algebraMap W E (p : W)) ^ m :=
          map_pow (algebraMap W E) (p : W) m
        _ = (algebraMap ℚ_[p] E (p : ℚ_[p])) ^ m := by
          rw [hpBase]
        _ = (p : E) ^ m := by
          rw [map_natCast]
    have hpowFixed :
        φ (algebraMap W E ((p : W) ^ m)) =
          algebraMap W E ((p : W) ^ m) := by
      have hbase :
          algebraMap W E ((p : W) ^ m) =
            algebraMap ℚ_[p] E ((p : ℚ_[p]) ^ m) := by
        calc
          algebraMap W E ((p : W) ^ m) =
              (p : E) ^ m :=
            hpowBridge
          _ =
              algebraMap ℚ_[p] E ((p : ℚ_[p]) ^ m) := by
            rw [map_pow, map_natCast]
      rw [hbase]
      exact φ.commutes ((p : ℚ_[p]) ^ m)
    have hcFieldFixed :
        φ (algebraMap W E c) = algebraMap W E c := by
      rw [hclear, map_mul, hpowFixed, hx]
    have hcFixed : WittVector.frobenius c = c := by
      apply IsFractionRing.injective W E
      rw [← padicCompletedUnramifiedFrobenius_algebraMap_witt]
      exact hcFieldFixed
    obtain ⟨z, hz⟩ :=
      (padicCompletedUnramifiedWittRing_frobenius_fixed_iff
        p c).1 hcFixed
    refine
      ⟨algebraMap ℤ_[p] ℚ_[p] z / (p : ℚ_[p]) ^ m, ?_⟩
    rw [map_div₀ (algebraMap ℚ_[p] E),
      padicCompletedUnramifiedField_algebraMap_padicInt]
    simp only [map_pow, map_natCast]
    have hpE' : (p : E) ^ m ≠ 0 := by
      rw [← hpowBridge]
      exact hpE
    have hclear' :
        algebraMap W E c =
          (p : E) ^ m * x := by
      rw [← hpowBridge]
      exact hclear
    rw [hz]
    exact (div_eq_iff hpE').2 (by
      simpa only [mul_comm] using hclear')
  · rintro ⟨q, rfl⟩
    exact (padicCompletedUnramifiedFrobenius p).commutes q

end LubinTate

end
