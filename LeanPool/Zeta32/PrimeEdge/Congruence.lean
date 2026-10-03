/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.PrimeEdge.Reference
public import LeanPool.Zeta32.PrimeEdge.Distribution
public import LeanPool.Zeta32.PrimeEdge.LocalShape
public import LeanPool.Zeta32.PrimeEdge.Valuation

/-! **S4**: entrywise congruence `G ≡ Ref` with excess `1/2`, the determinant
congruence `det G ≡ det Ref (mod p^{Σπ+1})`, and the scaled congruence
`p^{-Σπ} det(T)^2 · Q_{p-1} ≡ (unit) (mod p)`. No `sorry` in this file. -/

public section

open Polynomial
open scoped BigOperators
namespace Zeta32.PrimeEdge

open Zeta32.Arith.Local

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
lemma VG_of_not_dvd_den {r : ℚ} (hden : ¬ p ∣ r.den) : VG p r 0 := by
  right
  rw [padicValRat, padicValNat.eq_zero_of_not_dvd hden]
  simp

omit hp in
lemma VG_of_unit {q : ℚ} (hq : padicValRat p q = 0) : VG p q 0 := by
  right; rw [hq]; simp

theorem G_GV (hp7 : 7 ≤ p) {r : ℚ} (hr : VG p r 0) (a c : Idx p) :
    GV p (G r p a c) (rho p a + rho p c) :=
  entry_GV (by omega) hr a c _ (fun d _ => rho_add_le_discExp a c d)

theorem Ref_GV (hp7 : 7 ≤ p) (w : ℕ → ℚ) (hw : ∀ b < p, w b ≠ 0 ∧ padicValRat p (w b) = 0)
    (a c : Idx p) : GV p (Ref p w a c) (rho p a + rho p c) := by
  unfold Ref
  rw [Matrix.of_apply]
  split_ifs with h
  · apply GV.C
    rw [rho_add_of_same a c h]
    have h1 := VG.primePow (p := p) (colBase p a.1.val + a.2.val + c.2.val)
    have h2 := VG_of_unit (hw a.1.val a.1.isLt).2
    have hi := a.2.isLt
    have hk : c.2.val < mult p a.1.val := by
      have := c.2.isLt
      have hm : mult p c.1.val = mult p a.1.val := by rw [h]
      omega
    have h3 := blockMoment_VG hp7 a.1.val (a.2.val + c.2.val) (by omega)
    have := (h1.mul h2).mul h3
    simpa using this
  · exact GV.zero _

/-- **S4-entry.** `G_{ac} - Ref_{ac}` has excess `≥ 1/2` over `ρ_a + ρ_c`. -/
theorem G_sub_Ref_GV (hp7 : 7 ≤ p) {r : ℚ} (hr : VG p r 0) (w : ℕ → ℚ)
    (hsame : ∀ a c : Idx p, a.1 = c.1 →
        VG p ((p : ℚ) ^ (-2 : ℤ) * discLocal r (p - 1) p a.1.val (Aent p a c) -
            (p : ℚ) ^ (colBase p a.1.val + a.2.val + c.2.val) * w a.1.val *
              blockMoment p a.1.val (a.2.val + c.2.val))
          (rho p a + rho p c + 1))
    (a c : Idx p) : GV p (G r p a c - Ref p w a c) (rho p a + rho p c + 1/2) := by
  have hp5 : 5 ≤ p := by omega
  by_cases h : a.1 = c.1
  · have hRef : Ref p w a c = C ((p : ℚ) ^ (colBase p a.1.val + a.2.val + c.2.val) * w a.1.val *
        blockMoment p a.1.val (a.2.val + c.2.val)) := by
      unfold Ref; rw [Matrix.of_apply, ite_eq_left h]
    rw [hRef, G_apply]
    refine GV_Lfun_sub_C ?_ ((slope_VG hp5 r a c).mono (by linarith))
    set β := rho p a + rho p c
    have hdist := distribution_trunc (n := p - 1) (by omega) (five_mul_lt_sq hp5) hr
      (Adm_Aent hp5 a c) (Aent_natDegree hp5 a c) (β + 2)
      (entExp_hβ hp5 a c β (fun d _ => rho_add_le_discExp a c d))
    have hb : a.1.val ∈ Finset.range p := Finset.mem_range.mpr a.1.isLt
    have hsplit : (p : ℚ) ^ (-2 : ℤ) * ∑ d ∈ Finset.range p, discLocal r (p - 1) p d (Aent p a c) =
        (p : ℚ) ^ (-2 : ℤ) * discLocal r (p - 1) p a.1.val (Aent p a c) +
          ∑ d ∈ (Finset.range p).erase a.1.val,
            (p : ℚ) ^ (-2 : ℤ) * discLocal r (p - 1) p d (Aent p a c) := by
      rw [← Finset.add_sum_erase _ _ hb, mul_add, Finset.mul_sum]
    have hother : VG p (∑ d ∈ (Finset.range p).erase a.1.val,
        (p : ℚ) ^ (-2 : ℤ) * discLocal r (p - 1) p d (Aent p a c)) (β + 1) := by
      refine VG.sum _ fun d hd => ?_
      rw [Finset.mem_erase, Finset.mem_range] at hd
      exact disc_other_class hp7 hr a c h d hd.2 hd.1
    rw [show β + 2 - 1 = β + 1 by ring] at hdist
    have htot := (hdist.add (hsame a c h)).add hother
    have h' := htot.mono (s := β + 1/2) (by linarith)
    convert h' using 1
    rw [hsplit]
    ring
  · have hRef : Ref p w a c = 0 := by
      unfold Ref; rw [Matrix.of_apply, ite_eq_right h]
    rw [hRef, sub_zero]
    exact cross_VG (by omega) hr a c h

lemma rho_sum (p : ℕ) : ∑ a : Idx p, rho p a + ∑ a : Idx p, rho p a = (levelSum p : ℚ) := by
  unfold rho levelSum
  push_cast
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- **S4.** The scaled congruence: `s · Q_{p-1} ≡ c (mod p)` with `c` a `p`-adic unit. -/
theorem scaled_Q_congruence (r : ℚ) (hp7 : 7 ≤ p) (hE : p ∉ exceptional) (hden : ¬ p ∣ r.den) :
    ∃ s c : ℚ, s ≠ 0 ∧ c ≠ 0 ∧ padicValRat p c = 0 ∧
      GV p (C s * Zeta32.Q r (p - 1) - C c) 1 := by
  have hp5 : 5 ≤ p := by omega
  have hr : VG p r 0 := VG_of_not_dvd_den hden
  obtain ⟨w, hw, hsame⟩ := disc_same_class hp7 hr
  have hd := det_sub_GV (G r p) (Ref p w) (rho p) (rho p) (1/2) (G_GV hp7 hr) (Ref_GV hp7 w hw)
    (G_sub_Ref_GV hp7 hr w hsame)
  rw [rho_sum p, G_det r hp5, Ref_det w] at hd
  have hd1 : GV p (C (basisDet p hp5 ^ 2) * Zeta32.Q r (p - 1) -
      C ((p : ℚ) ^ levelSum p * refUnit p w)) ((levelSum p : ℚ) + 1) :=
    fun k => VG.round_half (levelSum p) (hd k)
  have hs := GV.C_mul (VG.primePow (p := p) (-levelSum p)) hd1
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  obtain ⟨hT0, _⟩ := basisDet_unit (p := p) hp5
  obtain ⟨hu0, hu⟩ := refUnit_unit hp7 hE w hw
  refine ⟨(p : ℚ) ^ (-levelSum p) * basisDet p hp5 ^ 2, refUnit p w,
    mul_ne_zero (zpow_ne_zero _ hp0) (pow_ne_zero _ hT0), hu0, hu, ?_⟩
  have he : C ((p : ℚ) ^ (-levelSum p)) * (C (basisDet p hp5 ^ 2) * Zeta32.Q r (p - 1) -
      C ((p : ℚ) ^ levelSum p * refUnit p w)) =
      C ((p : ℚ) ^ (-levelSum p) * basisDet p hp5 ^ 2) * Zeta32.Q r (p - 1) - C (refUnit p w) := by
    have h1 : (p : ℚ) ^ (-levelSum p) * ((p : ℚ) ^ levelSum p * refUnit p w) = refUnit p w := by
      rw [← mul_assoc, ← zpow_add₀ hp0, neg_add_cancel, zpow_zero, one_mul]
    rw [mul_sub, ← mul_assoc, ← C_mul, ← C_mul, h1]
  rw [he] at hs
  refine hs.mono (le_of_eq ?_)
  push_cast
  ring

end Zeta32.PrimeEdge

end
