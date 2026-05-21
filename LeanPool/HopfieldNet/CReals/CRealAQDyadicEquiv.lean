/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.CReals.CRealAQ
import LeanPool.HopfieldNet.CReals.CRealAQOrder

namespace Computable

open Classical

namespace CRealAQ

/-!
### Surjectivity of the dyadic backend

`CRealAQ Dyadic` is the quotient of dyadic representatives by extensional equality
in the ℚ-specification model.

The map `toCReal : CRealAQ Dyadic → CReal` is always injective. For `Dyadic` it is
also surjective: any ℚ-pre-real can be rounded into a dyadic representative (with
a constant slack `+2`) while preserving regularity.
-/

namespace DyadicSurj

/-- Absolute error for `Rat.toDyadic` on an arbitrary rational. -/
theorem abs_toRat_toDyadic_sub_le (q : ℚ) (n : Nat) :
    |(Rat.toDyadic q n).toRat - q| ≤ (1 : ℚ) / (2 ^ n) := by
  classical
  let y : Dyadic := Rat.toDyadic q n
  have hle : y.toRat ≤ q := by
    simpa [y] using Rat.toRat_toDyadic_le
  have hlt : q < y.toRat + Dyadic.ulp n := by
    simpa [y] using Rat.lt_toRat_toDyadic_add
  have h_nonneg : 0 ≤ q - y.toRat := sub_nonneg.mpr hle
  have h_le_ulp : q - y.toRat ≤ Dyadic.ulp n := by
    have : q - y.toRat < Dyadic.ulp n := by linarith
    exact le_of_lt this
  have habs : |y.toRat - q| = q - y.toRat := by
    rw [abs_sub_comm]
    exact abs_of_nonneg h_nonneg
  calc
    |y.toRat - q| = q - y.toRat := habs
    _ ≤ Dyadic.ulp n := h_le_ulp
    _ = (1 : ℚ) / (2 ^ n) := by
      simpa [Dyadic.ulp]

/-- Round a ℚ-pre-real into a dyadic representative (with slack `+2`). -/
def repOfPre (x : CReal.Pre) : CRealRep Dyadic where
  approx := fun n => Rat.toDyadic (x.approx (n + 2)) (n + 2)
  is_regular := by
    intro n m hnm
    -- triangle inequality around the original rational approximants
    set a : ℚ := (Rat.toDyadic (x.approx (n + 2)) (n + 2)).toRat
    set b : ℚ := (Rat.toDyadic (x.approx (m + 2)) (m + 2)).toRat
    set xn : ℚ := x.approx (n + 2)
    set xm : ℚ := x.approx (m + 2)
    have hn_round : |a - xn| ≤ (1 : ℚ) / (2 ^ (n + 2)) := by
      simpa [a, xn, abs_sub_comm] using
        abs_toRat_toDyadic_sub_le (q := x.approx (n + 2)) (n := n + 2)
    have hm_round : |xm - b| ≤ (1 : ℚ) / (2 ^ (m + 2)) := by
      have := abs_toRat_toDyadic_sub_le (q := x.approx (m + 2)) (n := m + 2)
      simpa [b, xm, abs_sub_comm] using this
    have hmid : |xn - xm| ≤ (1 : ℚ) / (2 ^ (n + 2)) := by
      have hnm' : n + 2 ≤ m + 2 := Nat.add_le_add_right hnm 2
      simpa [xn, xm] using x.is_regular (n + 2) (m + 2) hnm'
    have hab : |a - b| ≤ |a - xn| + |xn - xm| + |xm - b| := by
      have h1 : |a - b| ≤ |a - xn| + |xn - b| := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (abs_sub_le a xn b)
      have h2 : |xn - b| ≤ |xn - xm| + |xm - b| := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (abs_sub_le xn xm b)
      linarith
    have h_pow_mon : (1 : ℚ) / (2 ^ (m + 2)) ≤ (1 : ℚ) / (2 ^ (n + 2)) := by
      have hnm' : n + 2 ≤ m + 2 := Nat.add_le_add_right hnm 2
      have hpow : (2 : ℚ) ^ (n + 2) ≤ (2 : ℚ) ^ (m + 2) := pow_le_pow_of_le_left (by norm_num) hnm'
      have hpos : (0 : ℚ) < (2 : ℚ) ^ (n + 2) := pow_pos (by norm_num) _
      have := one_div_le_one_div_of_le hpos hpow
      simpa [one_div, div_eq_mul_inv] using this
    have hm_round' : |xm - b| ≤ (1 : ℚ) / (2 ^ (n + 2)) := hm_round.trans h_pow_mon
    have hR : |a - xn| + |xn - xm| + |xm - b|
        ≤ (1 : ℚ) / (2 ^ (n + 2)) + (1 : ℚ) / (2 ^ (n + 2)) + (1 : ℚ) / (2 ^ (n + 2)) := by
      linarith [hn_round, hmid, hm_round']
    have h3 : (1 : ℚ) / (2 ^ (n + 2)) + (1 : ℚ) / (2 ^ (n + 2)) + (1 : ℚ) / (2 ^ (n + 2))
        ≤ (1 : ℚ) / (2 ^ n) := by
      have hcoeff : (3 : ℚ) / 4 ≤ 1 := by norm_num
      have hpos : 0 ≤ (1 : ℚ) / (2 ^ n) := by
        have hpow : (0 : ℚ) < (2 : ℚ) ^ n := pow_pos (by norm_num) _
        exact le_of_lt (div_pos (show (0 : ℚ) < 1 by norm_num) hpow)
      have : (1 : ℚ) / (2 ^ (n + 2)) = (1 : ℚ) / (2 ^ n) / 4 := by
        simp [pow_add, pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      simp [this]
      nlinarith [hcoeff, hpos]
    have : |a - b| ≤ (1 : ℚ) / (2 ^ n) := hab.trans (le_trans hR h3)
    simpa [a, b, xn, xm] using this

/-- The dyadic rounding representative denotes the original ℚ-pre-real. -/
theorem repOfPre_toPre_equiv (x : CReal.Pre) : (repOfPre x).toPre ≈ x := by
  intro n
  -- compare at index `n+1`
  set a : ℚ := (repOfPre x).toPre.approx (n + 1)
  set b : ℚ := x.approx (n + 1)
  set c : ℚ := x.approx (n + 3)
  have h_round : |a - c| ≤ (1 : ℚ) / (2 ^ (n + 3)) := by
    simpa [repOfPre, CRealRep.toPre, a, c] using
      abs_toRat_toDyadic_sub_le (q := x.approx (n + 3)) (n := n + 3)
  have h_reg : |c - b| ≤ (1 : ℚ) / (2 ^ (n + 1)) := by
    have := x.is_regular (n + 1) (n + 3) (by omega)
    simpa [b, c] using this
  have h_tri : |a - b| ≤ |a - c| + |c - b| := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (abs_sub_le a c b)
  have h_close : (1 : ℚ) / (2 ^ (n + 3)) + (1 : ℚ) / (2 ^ (n + 1)) ≤ (1 : ℚ) / (2 ^ n) := by
    nlinarith
  have : |a - b| ≤ (1 : ℚ) / (2 ^ n) := (h_tri.trans (by linarith [h_round, h_reg])).trans h_close
  simpa [CReal.Pre.Equiv, a, b] using this

end DyadicSurj

open DyadicSurj

/-- `toCReal` is surjective for the dyadic backend. -/
theorem toCReal_surjective_dyadic : Function.Surjective (toCReal (AQ := Dyadic)) := by
  intro r
  refine Quotient.inductionOn r (fun x => ?_) r
  refine ⟨(Quotient.mk _ (DyadicSurj.repOfPre x) : CRealAQ Dyadic), ?_⟩
  -- `toCReal` of the representative is `⟦(repOfPre x).toPre⟧`.
  -- This equals `⟦x⟧` because `repOfPre_toPre_equiv`.
  change (Quotient.mk _ (CRealRep.toPre (DyadicSurj.repOfPre x))) = Quotient.mk _ x
  exact Quotient.sound (DyadicSurj.repOfPre_toPre_equiv (x := x))

/-- Equivalence between `CRealAQ Dyadic` and the spec quotient `CReal`. -/
noncomputable def equivCRealDyadic : CRealAQ Dyadic ≃ CReal :=
  Equiv.ofBijective (toCReal (AQ := Dyadic))
    ⟨toCReal_injective (AQ := Dyadic), toCReal_surjective_dyadic⟩

/-- `toCReal` bundled as a ring homomorphism. -/
noncomputable def toCRealRingHom : CRealAQ Dyadic →+* CReal where
  toFun := toCReal (AQ := Dyadic)
  map_zero' := by
    simpa using (toCReal_zero (AQ := Dyadic))
  map_one' := by
    simpa using (toCReal_one (AQ := Dyadic))
  map_add' := by
    intro a b
    simpa using (toCReal_add (AQ := Dyadic) a b)
  map_mul' := by
    intro a b
    simpa using (toCReal_mul (AQ := Dyadic) a b)

/-- Ring equivalence between `CRealAQ Dyadic` and the spec quotient `CReal`. -/
noncomputable def ringEquivCRealDyadic : CRealAQ Dyadic ≃+* CReal := by
  classical
  refine RingEquiv.ofBijective (toCRealRingHom) ?_
  exact ⟨toCReal_injective (AQ := Dyadic), toCReal_surjective_dyadic⟩

end CRealAQ

end Computable
