/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.PrimeEdge.Dist.Split
public import LeanPool.Zeta32.PrimeEdge.Dist.Val

/-! The distribution formula on one simple pole `D_{5n} / (t + j)`.

* `dl_near` : on the disc `b = j mod p` the pole is near: `dl = p^{-1} V^loc(1/(u + ⌊j/p⌋))`;
* `dl_far` : on the other discs it is far: `dl = V^loc(trunc (near(u) / ((j - b) + p u)))`;
* `VG_far` : the far value is `p`-integral (Tate coefficients `v ≥ e`, von Staudt). -/

public section

open Polynomial
open scoped BigOperators
namespace Zeta32.PrimeEdge

open Zeta32.Arith.Local

noncomputable section

/-- `D_S / (t + j)`. -/
def Ej (M : Finset ℕ) (j : ℕ) : ℚ[X] := ∏ m' ∈ M.erase j, (X + C (m' : ℚ))

lemma Ej_mul {M : Finset ℕ} {j : ℕ} (hj : j ∈ M) : Ej M j * (X + C (j : ℚ)) = mprod M := by
  rw [Ej, mprod, ← Finset.mul_prod_erase M _ hj, mul_comm]

lemma natDegree_Ej (M : Finset ℕ) (j : ℕ) : (Ej M j).natDegree = (M.erase j).card := by
  unfold Ej
  rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_add_C _]
  simp only [natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one]

lemma sum_ite_Ej (M : Finset ℕ) {j : ℕ} (hj : j ∈ M) :
    ∑ m ∈ M, C (if m = j then (1 : ℚ) else 0) * ∏ m' ∈ M.erase m, (X + C (m' : ℚ)) = Ej M j := by
  rw [Finset.sum_eq_single j]
  · simp [Ej]
  · intro m _ hm; simp [hm]
  · intro h; exact absurd hj h

lemma locValue_Ej (s : ℚ) {M : Finset ℕ} {j : ℕ} (hj : j ∈ M) :
    locValue s (Ej M j) M = locPole s j := by
  have h := locValue_pf s M 0 (fun m => if m = j then 1 else 0)
  rw [zero_mul, zero_add, sum_ite_Ej M hj, dist_locPoly_zero, zero_add] at h
  rw [h, Finset.sum_eq_single j]
  · simp
  · intro m _ hm; simp [hm]
  · intro h'; exact absurd hj h'

lemma Ej_comp_mul {M : Finset ℕ} {j : ℕ} (hj : j ∈ M) (p b : ℕ) :
    (Ej M j).comp (C (p : ℚ) * X - C (b : ℚ)) * (C ((j : ℚ) - b) + C (p : ℚ) * X) =
      (mprod M).comp (C (p : ℚ) * X - C (b : ℚ)) := by
  rw [← Ej_mul hj, mul_comp]
  congr 1
  simp only [add_comp, X_comp, C_comp, C_sub]
  ring

/-- The inverse of `w + q u` in `ℚ[[u]]`. -/
lemma inv_lin (w q : ℚ) (hw : w ≠ 0) :
    ((C w + C q * X : ℚ[X]) : PowerSeries ℚ)⁻¹ = PowerSeries.mk fun e => (-q) ^ e / w ^ (e + 1)
      := by
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by rw [Polynomial.constantCoeff_coe]; simp [hw])]
  ext k
  simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X, mul_add,
    ← mul_assoc, map_add]
  rcases k with _ | k
  · rw [PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mul_C, PowerSeries.coeff_mk,
      PowerSeries.coeff_one, ite_eq_left rfl]
    field_simp; simp
  · rw [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_C,
      PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_one, ite_eq_right (by omega)]
    rw [pow_succ, pow_succ]
    field_simp
    ring

/-- **Far pole** on the disc `b`. -/
theorem dl_far {p : ℕ} (hp : 0 < p) (r : ℚ) (n b : ℕ) (hb : b < p) {j : ℕ}
    (hj : j ∈ Finset.Icc 1 (5 * n)) (hjb : j % p ≠ b) :
    dl r n p b (Ej (Finset.Icc 1 (5 * n)) j) =
      locValue (r * p) (PowerSeries.trunc (truncOrder n)
        ((mprod (nearSet n p b) : PowerSeries ℚ) *
          ((C ((j : ℚ) - b) + C (p : ℚ) * X : ℚ[X]) : PowerSeries ℚ)⁻¹)) (nearSet n p b) := by
  set M := Finset.Icc 1 (5 * n)
  set Lw : ℚ[X] := C ((j : ℚ) - b) + C (p : ℚ) * X with hLwdef
  set ℓ := (M.filter (fun j => j % p = b)).card with hℓ
  have hw : (j : ℚ) - b ≠ 0 := by
    intro h
    have : j = b := by exact_mod_cast sub_eq_zero.mp h
    exact hjb (by rw [this]; exact Nat.mod_eq_of_lt hb)
  have hLw : (Lw : PowerSeries ℚ) * (Lw : PowerSeries ℚ)⁻¹ = 1 :=
    ps_mul_inv (by simp [Lw, hw])
  have hF := ps_mul_inv (farS_coeff_zero_ne hb M)
  have hcomp := Ej_comp_mul hj p b
  rw [comp_mprod hp b M] at hcomp
  have hps : (((Ej M j).comp (C (p : ℚ) * X - C (b : ℚ)) : ℚ[X]) : PowerSeries ℚ) *
      (farS p b M : PowerSeries ℚ)⁻¹ =
      PowerSeries.C ((p : ℚ) ^ ℓ) * ((mprod (nearS p b M) : PowerSeries ℚ) * (Lw : PowerSeries
        ℚ)⁻¹) := by
    calc _ = (((Ej M j).comp (C (p : ℚ) * X - C (b : ℚ)) : ℚ[X]) : PowerSeries ℚ) *
          ((Lw : PowerSeries ℚ) * (Lw : PowerSeries ℚ)⁻¹) * (farS p b M : PowerSeries ℚ)⁻¹ := by
          rw [hLw, mul_one]
      _ = ((((Ej M j).comp (C (p : ℚ) * X - C (b : ℚ)) * Lw : ℚ[X]) : PowerSeries ℚ)) *
          (Lw : PowerSeries ℚ)⁻¹ * (farS p b M : PowerSeries ℚ)⁻¹ := by
          rw [Polynomial.coe_mul]; ring
      _ = (((C ((p : ℚ) ^ ℓ) * mprod (nearS p b M) * farS p b M : ℚ[X]) : PowerSeries ℚ)) *
          (Lw : PowerSeries ℚ)⁻¹ * (farS p b M : PowerSeries ℚ)⁻¹ := by rw [hcomp]
      _ = PowerSeries.C ((p : ℚ) ^ ℓ) * ((mprod (nearS p b M) : PowerSeries ℚ) *
          (Lw : PowerSeries ℚ)⁻¹) * ((farS p b M : PowerSeries ℚ) *
          (farS p b M : PowerSeries ℚ)⁻¹) := by
          rw [Polynomial.coe_mul, Polynomial.coe_mul, Polynomial.coe_C]; ring
      _ = _ := by rw [hF, mul_one]
  unfold dl
  rw [nearSet_eq, farProd_eq, hps, PowerSeries.trunc_C_mul, dist_locValue_C_mul, card_nearS hp,
    ← hℓ,
    ← mul_assoc, zpow_neg, zpow_natCast,
    inv_mul_cancel₀ (pow_ne_zero _ (by exact_mod_cast hp.ne')), one_mul]

/-- **Near pole** on the disc `j mod p`. -/
theorem dl_near {p : ℕ} (hp : 0 < p) (r : ℚ) (n : ℕ) {j : ℕ} (hj : j ∈ Finset.Icc 1 (5 * n)) :
    dl r n p (j % p) (Ej (Finset.Icc 1 (5 * n)) j) = (p : ℚ)⁻¹ * locPole (r * p) (j / p) := by
  set M := Finset.Icc 1 (5 * n)
  set b := j % p with hbdef
  have hb : b < p := Nat.mod_lt j hp
  set mj := (j - b) / p with hmjdef
  set ℓ := (M.filter (fun j => j % p = b)).card with hℓ
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hmj : mj ∈ nearS p b M :=
    Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, rfl⟩, rfl⟩
  have hcast : (j : ℚ) = p * mj + b := cast_eq_near hp rfl
  have hlin : C ((j : ℚ) - b) + C (p : ℚ) * X = C (p : ℚ) * (X + C (mj : ℚ)) := by
    rw [hcast, show (p : ℚ) * mj + b - b = p * mj by ring, C_mul]; ring
  have hcomp := Ej_comp_mul hj p b
  rw [comp_mprod hp b M, hlin, ← Ej_mul hmj] at hcomp
  have hcomp2 : (X + C (mj : ℚ)) * ((Ej M j).comp (C (p : ℚ) * X - C (b : ℚ)) * C (p : ℚ)) =
      (X + C (mj : ℚ)) * (C ((p : ℚ) ^ ℓ) * Ej (nearS p b M) mj * farS p b M) := by
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at hcomp
    rw [← hcomp]; ring
  have hcomp3 := mul_left_cancel₀ (monic_X_add_C (mj : ℚ)).ne_zero hcomp2
  have hEj : (Ej M j).comp (C (p : ℚ) * X - C (b : ℚ)) =
      C ((p : ℚ) ^ ℓ * (p : ℚ)⁻¹) * Ej (nearS p b M) mj * farS p b M := by
    calc _ = (Ej M j).comp (C (p : ℚ) * X - C (b : ℚ)) * C (p : ℚ) * C (p : ℚ)⁻¹ := by
          rw [mul_assoc, ← C_mul, mul_inv_cancel₀ hpq, C_1, mul_one]
      _ = _ := by rw [hcomp3, C_mul]; ring
  have hF := ps_mul_inv (farS_coeff_zero_ne hb M)
  have hps : (((Ej M j).comp (C (p : ℚ) * X - C (b : ℚ)) : ℚ[X]) : PowerSeries ℚ) *
      (farS p b M : PowerSeries ℚ)⁻¹ =
      ((C ((p : ℚ) ^ ℓ * (p : ℚ)⁻¹) * Ej (nearS p b M) mj : ℚ[X]) : PowerSeries ℚ) := by
    rw [hEj, Polynomial.coe_mul, Polynomial.coe_mul, mul_assoc, hF, mul_one]
  have hdeg : (C ((p : ℚ) ^ ℓ * (p : ℚ)⁻¹) * Ej (nearS p b M) mj).natDegree < truncOrder n := by
    refine lt_of_le_of_lt (natDegree_C_mul_le _ _) ?_
    rw [natDegree_Ej]
    have h1 := Finset.card_erase_lt_of_mem hmj
    have h2 : (nearS p b M).card ≤ 5 * n := by
      have := card_nearSet_le hp n b
      rwa [nearSet_eq] at this
    unfold truncOrder
    omega
  unfold dl
  rw [nearSet_eq, farProd_eq, hps, PowerSeries.trunc_coe_eq_self hdeg, dist_locValue_C_mul,
    locValue_Ej _ hmj, card_nearS hp, ← hℓ, hmjdef, sub_div_eq hp rfl, zpow_neg, zpow_natCast]
  field_simp

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Far values are integral.** -/
theorem VG_far {s : ℚ} (hs : VG p s 1) (near : Finset ℕ) (hnear : ∀ m ∈ near, m < p) (N : ℕ)
    (hN : near.card + 1 ≤ N) {w : ℚ} (hw0 : w ≠ 0) (hw : VG p w⁻¹ 0) :
    VG p (locValue s (PowerSeries.trunc N ((mprod near : PowerSeries ℚ) *
      ((C w + C (p : ℚ) * X : ℚ[X]) : PowerSeries ℚ)⁻¹)) near) 0 := by
  set T := mprod near with hTdef
  set ψ := ((C w + C (p : ℚ) * X : ℚ[X]) : PowerSeries ℚ)⁻¹ with hψdef
  have hψv : ∀ e : ℕ, VG p (PowerSeries.coeff e ψ) e := by
    intro e
    rw [hψdef, inv_lin _ _ hw0, PowerSeries.coeff_mk, div_eq_mul_inv, ← inv_pow]
    have h1 : VG p ((-(p : ℚ)) ^ e) e := by
      have := ((VG.primePow (p := p) 1).neg).pow e
      simpa using this
    have h2 := hw.pow (e + 1)
    have := h1.mul h2
    simpa using this
  set g := PowerSeries.trunc N ψ with hgdef
  have hg : ∀ e : ℕ, VG p (g.coeff e) e := by
    intro e
    rw [hgdef, PowerSeries.coeff_trunc]
    split_ifs
    · exact hψv e
    · exact VG.zero _
  have hTint : GV p T 0 := by
    rw [hTdef, mprod]
    have := GV.prod (p := p) near (f := fun m => X + C (m : ℚ)) (r := fun _ => 0)
      (fun m _ => by
        have := (GV.X (p := p)).add (GV.C (VG.natCast (p := p) m))
        simpa using this)
    simpa using this
  set F := PowerSeries.trunc N ((T : PowerSeries ℚ) * ψ) with hFdef
  set H := T * g - F with hHdef
  have hH : GV p H ((N : ℚ) - near.card) := by
    intro k
    rw [hHdef, coeff_sub, hFdef, PowerSeries.coeff_trunc]
    split_ifs with hk
    · have : (T * g).coeff k = PowerSeries.coeff k ((T : PowerSeries ℚ) * ψ) := by
        rw [PowerSeries.coeff_mul, Polynomial.coeff_mul]
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [Polynomial.coeff_coe, hgdef, PowerSeries.coeff_trunc, ite_eq_left]
        rw [Finset.mem_antidiagonal] at hx
        omega
      rw [this, sub_self]; exact VG.zero _
    · rw [sub_zero, Polynomial.coeff_mul]
      refine VG.sum _ fun x hx => ?_
      rw [Finset.mem_antidiagonal] at hx
      by_cases h1 : x.1 ≤ near.card
      · have := (hTint x.1).mul (hg x.2)
        refine this.mono ?_
        have h2 : (N : ℚ) ≤ k := by exact_mod_cast (not_lt.mp hk)
        have h3 : (x.1 : ℚ) + x.2 = k := by exact_mod_cast hx
        have h4 : (x.1 : ℚ) ≤ near.card := by exact_mod_cast h1
        linarith
      · rw [coeff_eq_zero_of_natDegree_lt (by rw [hTdef, natDegree_mprod]; omega), zero_mul]
        exact VG.zero _
  have hdec : F = g * mprod near + C (-1) * H := by
    rw [hHdef, hTdef, C_neg, C_1]; ring
  rw [hdec, dist_locValue_add, dist_locValue_C_mul, locValue_mul_mprod]
  refine VG.add (VG_locPoly_tate hs hg) ?_
  have h1 := VG_locValue (hs.mono (by norm_num)) near hnear hH
  have h2 := (VG.one (p := p)).neg.mul h1
  refine h2.mono ?_
  have : (near.card : ℚ) + 1 ≤ N := by exact_mod_cast hN
  linarith

end

end Zeta32.PrimeEdge

end
