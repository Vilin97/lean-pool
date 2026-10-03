/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.PrimeEdge.Disc.Scaled
public import LeanPool.Zeta32.PrimeEdge.Basis

/-! The factorization on a disc (`n = p - 1`): for `d < p`,
`dissectNum p d (Aent a c) = p^E u^E R(u)` with `R` scaled and `R(0)` a unit, where
* on another disc `d ≠ b` (`a, c` of class `b`): `E = 2 m_d + (1 if d = 0 else 4)`;
* on the own disc `b`: `E = E_b + i + k`, `E_b = 1` for `b = 0` and `4` otherwise, with `R`
  depending only on `b`.
Also: `farProd` is scaled with unit constant term, and the near sets for `n = p - 1`. -/

public section

open Polynomial
open scoped BigOperators
namespace Zeta32.PrimeEdge

open Zeta32.Arith.Local

variable {p : ℕ}

/-- The CRT basis vector without its own-class factor. -/
noncomputable def crt0 (p b : ℕ) : ℚ[X] :=
  ∏ b' ∈ (Finset.range p).erase b, (X + C (b' : ℚ)) ^ mult p b'

lemma crtBasis_eq (a : Idx p) :
    crtBasis p a = (X + C (a.1.val : ℚ)) ^ a.2.val * crt0 p a.1.val := rfl

/-- `φ_{b,0} φ_{b,0} D_{p-1}^4`. -/
noncomputable def B0 (p b : ℕ) : ℚ[X] := crt0 p b * crt0 p b * Zeta32.D (p - 1) ^ 4

/-- Exponent of the own disc. -/
def ownExp (b : ℕ) : ℕ := if b = 0 then 1 else 4

lemma good_crt0 [Fact p.Prime] {d : ℕ} (hd : d < p) (b : ℕ) :
    Good p d (crt0 p b) (if d ∈ (Finset.range p).erase b then mult p d else 0) := by
  unfold crt0
  have h := Good.prod (p := p) (d := d) ((Finset.range p).erase b)
    (f := fun b' => (X + C (b' : ℚ)) ^ mult p b')
    (E := fun b' => mult p b' * (if b' = d then 1 else 0))
    (fun b' hb' => Good.pow (Good.lin hd
      (Finset.mem_range.mp (Finset.mem_of_mem_erase hb'))) _)
  refine h.congr ?_
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']

lemma good_D [Fact p.Prime] {d : ℕ} (hd : d < p) :
    Good p d (Zeta32.D (p - 1)) (if d ∈ Finset.Icc 1 (p - 1) then 1 else 0) := by
  unfold Zeta32.D
  have h := Good.prod (p := p) (d := d) (Finset.Icc 1 (p - 1))
    (f := fun j => X + C (j : ℚ)) (E := fun j => if j = d then 1 else 0)
    (fun j hj => Good.lin hd (by rw [Finset.mem_Icc] at hj; omega))
  refine h.congr ?_
  rw [Finset.sum_ite_eq']

lemma good_pow_own [Fact p.Prime] {d b : ℕ} (hd : d < p) (hb : b < p) (i : ℕ) :
    Good p d ((X + C (b : ℚ)) ^ i) (i * if b = d then 1 else 0) :=
  Good.pow (Good.lin hd hb) i

/-- **Other disc.** -/
theorem good_other [Fact p.Prime] {d : ℕ} (hd : d < p) (a c : Idx p) (hac : a.1 = c.1)
    (hdb : d ≠ a.1.val) :
    Good p d (X * Aent p a c) (2 * mult p d + if d = 0 then 1 else 4) := by
  have hc : c.1.val = a.1.val := by rw [hac]
  have h := (Good.X_self hd).mul
    ((((good_pow_own hd a.1.isLt a.2.val).mul (good_crt0 hd a.1.val)).mul
      ((good_pow_own hd c.1.isLt c.2.val).mul (good_crt0 hd c.1.val))).mul
      ((good_D hd).pow 4))
  have hA : X * Aent p a c = X * ((X + C (a.1.val : ℚ)) ^ a.2.val * crt0 p a.1.val *
      ((X + C (c.1.val : ℚ)) ^ c.2.val * crt0 p c.1.val) * Zeta32.D (p - 1) ^ 4) := by
    unfold Aent; rw [crtBasis_eq, crtBasis_eq]
  rw [hA]
  refine h.congr ?_
  have h1 : a.1.val ≠ d := fun h => hdb h.symm
  have h2 : c.1.val ≠ d := by rw [hc]; exact h1
  have h3 : d ∈ (Finset.range p).erase a.1.val :=
    Finset.mem_erase.mpr ⟨hdb, Finset.mem_range.mpr hd⟩
  have h4 : d ∈ (Finset.range p).erase c.1.val := by rw [hc]; exact h3
  rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3, ite_eq_left h4]
  by_cases hd0 : d = 0
  · subst hd0
    have : (0 : ℕ) ∉ Finset.Icc 1 (p - 1) := by simp
    rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_right this]; ring
  · have : d ∈ Finset.Icc 1 (p - 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    rw [ite_eq_right (Ne.symm hd0), ite_eq_right hd0, ite_eq_left this]; ring

theorem good_B0 [Fact p.Prime] {b : ℕ} (hb : b < p) : Good p b (X * B0 p b) (ownExp b) := by
  have h := (Good.X_self hb).mul (((good_crt0 hb b).mul (good_crt0 hb b)).mul ((good_D hb).pow 4))
  unfold B0
  refine h.congr ?_
  have h0 : b ∉ (Finset.range p).erase b := Finset.notMem_erase b _
  rw [ite_eq_right h0]
  unfold ownExp
  by_cases hb0 : b = 0
  · subst hb0
    have : (0 : ℕ) ∉ Finset.Icc 1 (p - 1) := by simp
    rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_right this]
  · have : b ∈ Finset.Icc 1 (p - 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    rw [ite_eq_right (Ne.symm hb0), ite_eq_right hb0, ite_eq_left this]

/-- **Own disc.** The factor `R` depends only on the class `b`. -/
theorem dissect_same [Fact p.Prime] {b : ℕ} (hb : b < p) :
    ∃ R : ℚ[X], Scaled p R ∧ IsUnitV p (R.coeff 0) ∧ ∀ a c : Idx p, a.1.val = b → c.1.val = b →
      dissectNum p b (Aent p a c) =
        C ((p : ℚ) ^ (ownExp b + a.2.val + c.2.val)) * X ^ (ownExp b + a.2.val + c.2.val) * R := by
  obtain ⟨R, hR, hRs, hRu⟩ := good_B0 hb
  refine ⟨R, hRs, hRu, fun a c ha hc => ?_⟩
  have hA : X * Aent p a c = (X + C (b : ℚ)) ^ (a.2.val + c.2.val) * (X * B0 p b) := by
    unfold Aent B0
    rw [crtBasis_eq, crtBasis_eq]
    generalize a.2.val = i
    generalize c.2.val = k
    rw [ha, hc]; ring
  have hlin : (X + C (b : ℚ)).comp (C (p : ℚ) * X - C (b : ℚ)) = C (p : ℚ) * X := by
    simp [add_comp]
  unfold dissectNum
  rw [hA, mul_comp, hR, pow_comp, hlin, mul_pow, ← C_pow]
  simp only [pow_add, map_mul]
  ring

/-! ### Far poles -/

lemma farProd_scaled [Fact p.Prime] {n b : ℕ} (hb : b < p) :
    Scaled p (farProd n p b) ∧ IsUnitV p ((farProd n p b).coeff 0) := by
  have hu : ∀ j ∈ (Finset.Icc 1 (5 * n)).filter (fun j => j % p ≠ b), IsUnitV p ((j : ℚ) - b) :=
    fun j hj => isUnitV_sub (by rw [Nat.mod_eq_of_lt hb]; exact (Finset.mem_filter.mp hj).2)
  unfold farProd
  refine ⟨Scaled.prod _ fun j hj => Scaled.lin (hu j hj).VG, ?_⟩
  rw [coeff_zero_prod]
  refine IsUnitV.prod _ fun j hj => ?_
  rw [coeff_add, coeff_C_zero, coeff_C_mul, coeff_X_zero, mul_zero, add_zero]
  exact hu j hj

/-- The regular factor `R / farProd` as a power series. -/
lemma scaledPS_div [Fact p.Prime] {R F : ℚ[X]} (hR : Scaled p R) (hF : Scaled p F)
    (hF0 : IsUnitV p (F.coeff 0)) : ScaledPS p ((R : PowerSeries ℚ) * (F : PowerSeries ℚ)⁻¹) :=
  (ScaledPS.coe hR).mul ((ScaledPS.coe hF).inv (by rw [Polynomial.constantCoeff_coe]; exact hF0))

lemma coeff_zero_div (R F : ℚ[X]) :
    PowerSeries.coeff 0 ((R : PowerSeries ℚ) * (F : PowerSeries ℚ)⁻¹) = R.coeff 0 * (F.coeff
      0)⁻¹ := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, PowerSeries.constantCoeff_inv,
    Polynomial.constantCoeff_coe, Polynomial.constantCoeff_coe]

/-- The dissected series: `dissectNum / farProd = p^E u^E K(u)`. -/
lemma series_eq (R F : ℚ[X]) (E : ℕ) :
    ((C ((p : ℚ) ^ E) * X ^ E * R : ℚ[X]) : PowerSeries ℚ) * (F : PowerSeries ℚ)⁻¹ =
      PowerSeries.C ((p : ℚ) ^ E) * PowerSeries.X ^ E *
        ((R : PowerSeries ℚ) * (F : PowerSeries ℚ)⁻¹) := by
  rw [Polynomial.coe_mul, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow,
    Polynomial.coe_X]
  ring

/-! ### Near sets for `n = p - 1` -/

lemma mem_nearSet_iff {n b : ℕ} (hb : b < p) (m : ℕ) :
    m ∈ nearSet n p b ↔ 1 ≤ b + p * m ∧ b + p * m ≤ 5 * n := by
  unfold nearSet
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨j, ⟨hj, hjb⟩, rfl⟩
    have he := Nat.mod_add_div j p
    rw [hjb] at he
    have hq : (j - b) / p = j / p := by
      have hp0 : 0 < p := by omega
      rw [show j - b = p * (j / p) by omega, Nat.mul_div_cancel_left _ hp0]
    rw [hq, he]; exact hj
  · rintro ⟨h1, h2⟩
    have hp0 : 0 < p := by omega
    refine ⟨b + p * m, ⟨⟨h1, h2⟩, ?_⟩, ?_⟩
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
    · rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hp0]

lemma lt_five_of_mem_nearSet {b : ℕ} (hb : b < p) {m : ℕ} (hm : m ∈ nearSet (p - 1) p b) :
    m < 5 := by
  rw [mem_nearSet_iff hb] at hm
  by_contra h
  have := Nat.mul_le_mul_left p (show 5 ≤ m by omega)
  omega

lemma nearSet_subset {b : ℕ} (hb : b < p) : nearSet (p - 1) p b ⊆ Finset.range 5 :=
  fun _m hm => Finset.mem_range.mpr (lt_five_of_mem_nearSet hb hm)

lemma nearSet_zero (hp : 5 ≤ p) : nearSet (p - 1) p 0 = {1, 2, 3, 4} := by
  ext m
  constructor
  · intro hm
    have h5 := lt_five_of_mem_nearSet (by omega) hm
    rw [mem_nearSet_iff (by omega)] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton]
    interval_cases m <;> omega
  · intro hm
    rw [mem_nearSet_iff (by omega)]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> omega

lemma nearSet_low {b : ℕ} (hb1 : 1 ≤ b) (hb : b + 5 ≤ p) : nearSet (p - 1) p b = {0, 1, 2, 3, 4}
  := by
  ext m
  constructor
  · intro hm
    have h5 := lt_five_of_mem_nearSet (by omega) hm
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · intro hm
    rw [mem_nearSet_iff (by omega)]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> omega

lemma nearSet_high (hp : 5 ≤ p) {b : ℕ} (hb1 : 1 ≤ b) (hbp : b < p) (hb : p < b + 5) :
    nearSet (p - 1) p b = {0, 1, 2, 3} := by
  ext m
  constructor
  · intro hm
    have h5 := lt_five_of_mem_nearSet hbp hm
    rw [mem_nearSet_iff hbp] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton]
    interval_cases m <;> omega
  · intro hm
    rw [mem_nearSet_iff hbp]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> omega

end Zeta32.PrimeEdge

end
