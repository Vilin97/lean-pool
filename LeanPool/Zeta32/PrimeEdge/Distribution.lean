/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.PrimeEdge.Dist.Global
public import LeanPool.Zeta32.PrimeEdge.Dist.Far

/-! **S2b-1**: the proof notes, Lemma 1 / Corollary 2 (the p-adic distribution
formula for `U_r`), in the truncated rational form used by §6.

Exact statement behind it (in `ℚ_p`): `U_r(f) = p^{-2} Σ_{b<p} V_Y(g_b)` with `Y = p³X + C_p`,
`C_p ∈ p³ℤ_p`. Taking the `X`-free part, the difference between `(Lfun r n A).coeff 0` and
`p^{-2} Σ_b discLocal r n p b A` consists of
* the `-2 C_p` near-pole terms: valuation `≥ β + 1` (`v(C_p) ≥ 3`, near residues have Gauss
valuation
  `≥ e(-b) + [b = 0]`, near-pole denominators `∏ (m' - m)` are units since `m, m' < p`);
* the far-pole tails of degree `≥ truncOrder n = 10n + 2`: the coefficient of `u^e` in
  `dissectNum / farProd` has valuation `≥ e(-b) + [b=0] + e - (10n - 1)` and `V` loses at most `1`
  (von Staudt), so each tail term has valuation `≥ β`.
Hence the error has valuation `≥ β - 1`, one more than the size `β - 2` of the entry (`Lfun_GV`).

proof (files `Dist/*`). No `ℚ_p` constants are needed. Write
`t A = P · D_{5n} + ∑_j c_j D_{5n}/(t+j)` (`XA_pf`); both sides are linear in the numerator.
* On `P · D_{5n}` the formula is exact (`Err_poly`: multiplication theorem `Psi_eq`).
* On `D_{5n}/(t+j)`: the near disc `b = j mod p` gives `p^{-3} V^loc(1/(u+⌊j/p⌋))`, which
  cancels the `p`-divisible part of `H^{(3)}_j, H^{(2)}_j` (`VG_near_cancel`); every far disc
  gives a
  `p`-integral value (`VG_far`). So the error on one pole has valuation `≥ -2` (`VG_Err_Ej`).
* `v_p(c_j) ≥ β + 1` (`VG_res`, and `p ∣ j` when `j` is in the class `0`). -/

public section

open Polynomial
open scoped BigOperators
namespace Zeta32.PrimeEdge

open Zeta32.Arith.Local

variable {p : ℕ}

lemma nearS_lt [hp : Fact p.Prime] {n : ℕ} (hn : 5 * n < p ^ 2) (b : ℕ) :
    ∀ m ∈ nearSet n p b, m < p := by
  intro m hm
  rw [nearSet, Finset.mem_image] at hm
  obtain ⟨j, hj, rfl⟩ := hm
  rw [Finset.mem_filter, Finset.mem_Icc] at hj
  rw [Nat.div_lt_iff_lt_mul hp.out.pos]
  have : p ^ 2 = p * p := by ring
  omega

lemma VG_inv_sub [hp : Fact p.Prime] {j b : ℕ} (hb : b < p) (hjb : j % p ≠ b) :
    VG p ((j : ℚ) - b)⁻¹ 0 := by
  have hnd : ¬ (p : ℤ) ∣ ((j : ℤ) - b) := by
    intro h
    have h1 : ((j : ℤ) : ZMod p) = ((b : ℤ) : ZMod p) := (zmod_eq_iff_dvd (p := p)).mpr h
    have h2 : (j : ZMod p) = (b : ZMod p) := by exact_mod_cast h1
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hb] at h2
    exact hjb h2
  have hne : (j : ℚ) - b ≠ 0 := by
    intro h
    exact hnd (by rw [show (j : ℤ) - b = 0 by exact_mod_cast h]; exact dvd_zero _)
  refine (VG.inv (r := 0)  ?_).mono (by norm_num)
  rw [show ((j : ℚ) - b) = (((j : ℤ) - b : ℤ) : ℚ) by push_cast; ring,
    padicValRat_int_eq_zero hnd]
  simp

/-- The error on one simple pole has valuation `≥ -2`. -/
theorem VG_Err_Ej [hp : Fact p.Prime] {n : ℕ} (hn : 5 * n < p ^ 2) {r : ℚ} (hr : VG p r 0)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 (5 * n)) :
    VG p (Err r n p (Ej (Finset.Icc 1 (5 * n)) j)) (-2) := by
  have hp0 : 0 < p := hp.out.pos
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hs : VG p (r * p) 1 := by
    have := hr.mul (VG.primePow (p := p) 1)
    simpa using this
  have hjb : j % p ∈ Finset.range p := Finset.mem_range.mpr (Nat.mod_lt j hp0)
  unfold Err
  rw [locValue_Ej r hj, ← Finset.add_sum_erase _ _ hjb, dl_near hp0 r n hj]
  have hsplit : locPole r j - (p : ℚ) ^ (-2 : ℤ) * ((p : ℚ)⁻¹ * locPole (r * p) (j / p) +
      ∑ b ∈ (Finset.range p).erase (j % p), dl r n p b (Ej (Finset.Icc 1 (5 * n)) j)) =
      (locPole r j - ((p : ℚ) ^ 3)⁻¹ * locPole (r * p) (j / p)) -
        (p : ℚ) ^ (-2 : ℤ) *
          ∑ b ∈ (Finset.range p).erase (j % p), dl r n p b (Ej (Finset.Icc 1 (5 * n)) j) := by
    rw [zpow_neg, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
    field_simp
    ring
  rw [hsplit]
  refine VG.sub ((VG_near_cancel hr j).mono (by norm_num)) ?_
  have hsum : VG p (∑ b ∈ (Finset.range p).erase (j % p),
      dl r n p b (Ej (Finset.Icc 1 (5 * n)) j)) 0 := by
    refine VG.sum _ fun b hb => ?_
    rw [Finset.mem_erase, Finset.mem_range] at hb
    have hjb' : j % p ≠ b := fun h => hb.1 h.symm
    rw [dl_far hp0 r n b hb.2 hj hjb']
    have hw0 : (j : ℚ) - b ≠ 0 := by
      intro h
      have : j = b := by exact_mod_cast sub_eq_zero.mp h
      exact hjb' (by rw [this]; exact Nat.mod_eq_of_lt hb.2)
    refine VG_far hs (nearSet n p b) (nearS_lt hn b) (truncOrder n) ?_ hw0 (VG_inv_sub hb.2 hjb')
    have := card_nearSet_le hp0 n b
    unfold truncOrder
    omega
  have := (VG.primePow (p := p) (-2)).mul hsum
  simpa using this

/-- **S2b-1 (truncated distribution formula).** Hypotheses as in `Lfun_GV`. -/
theorem distribution_trunc [Fact p.Prime] {n : ℕ} (hn1 : 1 ≤ n)
    (hn : 5 * n < p ^ 2) {r : ℚ} (hr : VG p r 0) {A : ℚ[X]} {e : ZMod p → ℤ}
    (hA : Adm p A e) (hdeg : A.natDegree + 2 ≤ 10 * n) (β : ℚ)
    (hβ : ∀ γ : ZMod p,
      β ≤ (e γ : ℚ) + (if γ = 0 then 1 else 0) - (plc p (Pl5 n) γ).card) :
    VG p ((Lfun r n A).coeff 0 -
      (p : ℚ) ^ (-2 : ℤ) * ∑ b ∈ Finset.range p, discLocal r n p b A) (β - 1) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  set M := Finset.Icc 1 (5 * n) with hMdef
  have hE : (Lfun r n A).coeff 0 -
      (p : ℚ) ^ (-2 : ℤ) * ∑ b ∈ Finset.range p, discLocal r n p b A = Err r n p (X * A) := by
    rw [Lfun_coeff_zero]; rfl
  have hPdeg : (X * (A /ₘ mprod M) + C (∑ j ∈ M, resN A M j)).natDegree + 5 * n <
      truncOrder n := by
    have h1 : (X * (A /ₘ mprod M) + C (∑ j ∈ M, resN A M j)).natDegree ≤
        1 + (A.natDegree - 5 * n) := by
      refine (natDegree_add_le _ _).trans ?_
      rw [natDegree_C]
      simp only [max_le_iff, zero_le, and_true]
      refine natDegree_mul_le.trans ?_
      rw [natDegree_divByMonic _ (mprod_monic M), natDegree_mprod, hMdef, Nat.card_Icc]
      have := natDegree_X_le (R := ℚ)
      omega
    unfold truncOrder
    omega
  rw [hE, XA_pf A M, Err_add, Err_poly hp0 r n _ hPdeg, zero_add, Err_sum]
  refine VG.sum _ fun j hj => ?_
  rw [Err_C_mul]
  have hErr := VG_Err_Ej hn hr hj
  have hjpos : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hmem : -(j : ℤ) ∈ Pl5 n := Finset.mem_image.mpr ⟨j, hj, rfl⟩
  have hres := VG_res hA (Pl5 n) (sep_Pl5 hn) hmem
  have hrN : resN A M j = resP A (Pl5 n) (-(j : ℤ)) := (resP_Pl5 A n j).symm
  set γ : ZMod p := ((-(j : ℤ) : ℤ) : ZMod p) with hγ
  have hβγ := hβ γ
  have hc : VG p (-(j : ℚ) * resN A M j) (β + 1) := by
    rw [hrN]
    by_cases h0 : γ = 0
    · rw [ite_eq_left h0] at hβγ
      have hdvd : (p : ℤ) ∣ (j : ℤ) := by
        have : ((j : ℤ) : ZMod p) = 0 := by
          have := h0; rw [hγ, Int.cast_neg, neg_eq_zero] at this; exact this
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
      have hj1 : VG p (-(j : ℚ)) 1 := by
        have := (VG_int_one (p := p) hdvd).neg
        simpa using this
      refine (hj1.mul hres).mono ?_
      linarith
    · rw [ite_eq_right h0] at hβγ
      have hj0 : VG p (-(j : ℚ)) 0 := (VG.natCast (p := p) j).neg
      refine (hj0.mul hres).mono ?_
      linarith
  refine (hc.mul hErr).mono ?_
  linarith

end Zeta32.PrimeEdge

end
