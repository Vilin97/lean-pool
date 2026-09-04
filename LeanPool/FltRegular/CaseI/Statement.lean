/-
Copyright (c) 2026 FltRegular contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FltRegular contributors
-/

module

import Mathlib.NumberTheory.FLT.Three

import LeanPool.FltRegular.MayAssume.Lemmas
import LeanPool.FltRegular.NumberTheory.Cyclotomic.CaseI
import LeanPool.FltRegular.NumberTheory.Cyclotomic.CyclRat
public import LeanPool.FltRegular.NumberTheory.RegularPrimes

/-!
# The first case of Fermat's Last Theorem for regular primes

This file proves the first case of Fermat's Last Theorem for regular primes, reducing the final
statement to a normalized version and establishing the required cyclotomic ideal factorization.
-/

@[expose] public section

open Finset Nat IsCyclotomicExtension Ideal Polynomial Int Basis FltRegular.CaseI

open scoped NumberField

namespace FltRegular

variable {p : ℕ}

namespace CaseI

/-- Statement of case I with additional assumptions. -/
def SlightlyEasier : Prop :=
  ∀ ⦃a b c : ℤ⦄ {p : ℕ} [Fact p.Prime], IsRegularPrime p → 5 ≤ p →
    ({a, b, c} : Finset ℤ).gcd id = 1 → ¬a ≡ b [ZMOD p] → ¬↑p ∣ a * b * c →
    a ^ p + b ^ p ≠ c ^ p

/-- Statement of case I. -/
def Statement : Prop :=
  ∀ ⦃a b c : ℤ⦄ {p : ℕ} [Fact p.Prime], IsRegularPrime p → ¬↑p ∣ a * b * c →
    a ^ p + b ^ p ≠ c ^ p

/-- It suffices to prove Case I under the additional normalized hypotheses. -/
theorem may_assume : SlightlyEasier → Statement := by
  intro Heasy a b c p hpri hreg hI H
  have hodd : p ≠ 2 := by
    rintro rfl
    refine hI <| Dvd.dvd.mul_left ?_ _
    simp only [Nat.cast_ofNat, ← even_iff_two_dvd] at hI ⊢
    rw [Int.not_even_iff_odd] at hI
    rw [← Int.even_pow' two_ne_zero, ← H]
    exact (Odd.of_mul_left (Odd.of_mul_left hI)).pow.add_odd
      (Odd.of_mul_right (Odd.of_mul_left hI)).pow
  have hprod : a * b * c ≠ 0 := by
    intro h
    simp [h] at hI
  have hp5 : 5 ≤ p := by
    by_contra! habs
    have : 2 < p := Nat.lt_of_le_of_ne hpri.out.two_le hodd.symm
    interval_cases p
    · exact fermatLastTheoremFor_iff_int.1 fermatLastTheoremThree a b c
        (fun ha ↦ hprod <| by simp [ha]) (fun hb ↦ hprod <| by simp [hb])
        (fun hc ↦ hprod <| by simp [hc]) H
    · exact Nat.not_prime_mul one_lt_two.ne' one_lt_two.ne' hpri.out
  let d := ({a, b, c} : Finset ℤ).gcd id
  have hdiv : ¬↑p ∣ a / d * (b / d) * (c / d) := by
    contrapose! hI with hdiv
    have hadiv : d ∣ a := gcd_dvd (by simp)
    have hbdiv : d ∣ b := gcd_dvd (by simp)
    have hcdiv : d ∣ c := gcd_dvd (by simp)
    rw [← Int.ediv_mul_cancel hadiv, ← Int.ediv_mul_cancel hbdiv, ← Int.ediv_mul_cancel hcdiv]
    convert! dvd_mul_of_dvd_right hdiv (d * d * d) using 1
    grind
  rcases MayAssume.coprime H hprod with ⟨Hxyz, hunit, hprodxyx⟩
  obtain ⟨_, _, _, H1, H2, H3, _, H5⟩ :=
    a_not_cong_b hpri.out hp5 hprodxyx Hxyz hunit hdiv
  exact Heasy hreg hp5 H2 H3 H5 H1

end CaseI

/-- In a normalized Fermat solution, `a` and `b` are coprime. -/
theorem ab_coprime {a b c : ℤ} (H : a ^ p + b ^ p = c ^ p) (hpzero : p ≠ 0)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1) : IsCoprime a b := by
  rw [isCoprime_iff_gcd_eq_one]
  by_contra! h
  obtain ⟨q, hqpri, hq⟩ := exists_prime_and_dvd h
  replace hqpri : Prime (q : ℤ) := prime_iff_natAbs_prime.2 (by simp [hqpri])
  have haq : ↑q ∣ a := (Int.natCast_dvd_natCast.2 hq).trans (Int.gcd_dvd_left a b)
  have hbq : ↑q ∣ b := (Int.natCast_dvd_natCast.2 hq).trans (Int.gcd_dvd_right a b)
  have hcq : ↑q ∣ c :=
    hqpri.dvd_of_dvd_pow (H ▸ dvd_add (dvd_pow haq hpzero) (dvd_pow hbq hpzero))
  have Hq : ↑q ∣ ({a, b, c} : Finset ℤ).gcd id := by
    refine dvd_gcd fun x hx ↦ ?_
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with H | H | H <;> simpa [H]
  rw [hgcd] at Hq
  exact hqpri.not_isUnit (isUnit_of_dvd_one Hq)

private def caseICoeff (a b : ℤ) (k₁ k₂ : ℕ) : ℕ → ℤ := fun j ↦
  (if j = 0 then a else 0) + (if j = 1 then b else 0) -
    (if j = k₁ then a else 0) - (if j = k₂ then b else 0)

private theorem sum_caseICoeff {R : Type*} [Ring R] (hp : 1 < p) (a b : ℤ)
    (k₁ k₂ : Fin p) (ζ : R) :
    ∑ j : Fin p, caseICoeff a b k₁ k₂ j • ζ ^ (j : ℕ) =
      ↑a + ↑b * ζ - ↑a * ζ ^ (k₁ : ℕ) - ↑b * ζ ^ (k₂ : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ ↦ caseICoeff a b k₁ k₂ j • ζ ^ j) p]
  simp only [caseICoeff, add_smul, sub_smul, ite_smul, sum_add_distrib,
    sum_sub_distrib, sum_ite, Finset.range_filter_eq]
  simp [Nat.zero_lt_of_lt hp, hp, Fin.is_lt]

private theorem exists_caseICoeff_eq_zero (hp5 : 5 ≤ p) (a b : ℤ)
    (k₁ k₂ : Fin p) : ∃ j : Fin p, caseICoeff a b k₁ k₂ j = 0 := by
  let zero : Fin p := ⟨0, by omega⟩
  let one : Fin p := ⟨1, by omega⟩
  let s : Finset (Fin p) := {zero, one, k₁, k₂}
  have hs : s.card ≤ 4 := card_le_four
  have hslt : s.card < Fintype.card (Fin p) := by
    simpa using lt_of_le_of_lt hs hp5
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hslt
  refine ⟨j, ?_⟩
  simp only [s, mem_insert, mem_singleton, not_or] at hj
  have hj0 : (j : ℕ) ≠ 0 := fun h ↦ hj.1 (Fin.ext h)
  have hj1 : (j : ℕ) ≠ 1 := fun h ↦ hj.2.1 (Fin.ext (by simpa [one] using h))
  have hjk₁ : (j : ℕ) ≠ k₁ := fun h ↦ hj.2.2.1 (Fin.ext h)
  have hjk₂ : (j : ℕ) ≠ k₂ := fun h ↦ hj.2.2.2 (Fin.ext h)
  simp [caseICoeff, hj0, hj1, hjk₁, hjk₂]

local notation "K" => CyclotomicField p ℚ

local notation "R" => 𝓞 K

/-- A `p`-th-power principal ideal has a generator that is a unit times a `p`-th power. -/
theorem is_principal_aux {K' : Type*} [Field K'] [CharZero K'] [IsCyclotomicExtension {p} ℚ K']
    [Fintype (ClassGroup (𝓞 K'))]
    {a b : ℤ} {ζ : 𝓞 K'} (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K'))
    {I : Ideal (𝓞 K')} (hI : span ({↑a + ζ * ↑b} : Set (𝓞 K')) = I ^ p) :
    ∃ (u : (𝓞 K')ˣ) (α : 𝓞 K'), ↑u * α ^ p = ↑a + ζ * ↑b := by
  let : NumberField K' := IsCyclotomicExtension.numberField {p} ℚ K'
  obtain ⟨α, hα⟩ : I.IsPrincipal := by
    apply Ideal.IsPrincipal.of_isPrincipal_pow_of_coprime hreg
    exact ⟨⟨↑a + ζ * ↑b, by rw [submodule_span_eq, hI]⟩⟩
  replace hα := congr_arg (fun (J : Submodule _ _) ↦ J ^ p) hα
  simp only [← hI, submodule_span_eq, span_singleton_pow, span_singleton_eq_span_singleton] at hα
  obtain ⟨u, hu⟩ := hα
  refine ⟨u⁻¹, α, ?_⟩
  rw [← hu, mul_comm ((_ + ζ * _)), Units.inv_mul_cancel_left]

variable [hpri : Fact p.Prime]

local instance : NeZero p := ⟨hpri.out.ne_zero⟩

local instance : IsCyclotomicExtension {p} ℚ K :=
  CyclotomicField.isCyclotomicExtension p ℚ

local instance : IsCyclotomicExtension {p} ℤ R :=
  IsCyclotomicExtension.ringOfIntegers

/-- The cyclotomic ideal generated by `a + ζ * b` is a `p`-th power. -/
theorem exists_ideal {a b c : ℤ} (h5p : 5 ≤ p) (H : a ^ p + b ^ p = c ^ p)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (caseI : ¬↑p ∣ a * b * c) {ζ : R} (hζ : ζ ∈ nthRootsFinset p 1) :
    ∃ I, span ({a + ζ * b} : Set R) = I ^ p := by
  classical
  have H₁ := congr_arg (@Int.cast R _) H
  simp only [Int.cast_add, Int.cast_pow] at H₁
  have hζ' := (zeta_spec p ℚ K).toInteger_isPrimitiveRoot
  rw [hζ'.pow_add_pow_eq_prod_add_mul _ _ <|
    odd_iff.2 <| hpri.1.eq_two_or_odd.resolve_left fun h ↦ by simp [h] at h5p] at H₁
  replace H₁ := congr_arg (fun x ↦ span ({x} : Set R)) H₁
  simp only [← prod_span_singleton, ← span_singleton_pow] at H₁
  refine exists_eq_pow_of_mul_eq_pow_of_coprime (fun η₁ hη₁ η₂ hη₂ hη ↦ ?_) H₁ ζ
    hζ
  refine fltIdeals_coprime ?_ ?_ H (ab_coprime H hpri.out.ne_zero hgcd) hη₁ hη₂ hη caseI
  · exact hpri.out
  · exact h5p

/-- The cyclotomic factor `a + ζ * b` is a unit times a `p`-th power. -/
theorem is_principal {a b c : ℤ} {ζ : R} (hreg : IsRegularPrime p) (hp5 : 5 ≤ p)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1) (caseI : ¬↑p ∣ a * b * c)
    (H : a ^ p + b ^ p = c ^ p) (hζ : IsPrimitiveRoot ζ p) :
    ∃ (u : Rˣ) (α : R), ↑u * α ^ p = ↑a + ζ * ↑b := by
  replace hζ := hζ.mem_nthRootsFinset hpri.out.pos
  obtain ⟨I, hI⟩ := exists_ideal hp5 H hgcd caseI hζ
  exact is_principal_aux hreg hI

/-- Two exponents whose associated cyclotomic linear combination is divisible by `p`. -/
theorem ex_fin_div {a b c : ℤ} {ζ : R} (hp5 : 5 ≤ p) (hreg : IsRegularPrime p)
    (hζ : IsPrimitiveRoot ζ p) (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (caseI : ¬↑p ∣ a * b * c) (H : a ^ p + b ^ p = c ^ p) :
    ∃ k₁ k₂ : Fin p,
      k₂ ≡ k₁ - 1 [ZMOD p] ∧
        ↑p ∣ ↑a + ↑b * ζ - ↑a * ζ ^ (k₁ : ℕ) - ↑b * ζ ^ (k₂ : ℕ) := by
  let ζ' := (ζ : K)
  have hζ' : IsPrimitiveRoot ζ' p := IsPrimitiveRoot.coe_submonoidClass_iff.2 hζ
  let zetaUnit := (hζ'.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit
  have h : ζ = (zetaUnit : R) := by rfl
  have hP : p ≠ 2 := by
    intro hP
    rw [hP] at hp5
    contradiction
  obtain ⟨u, α, hu⟩ := is_principal hreg hp5 hgcd caseI H hζ
  rw [h, mul_comm _ (↑b : R), ← pow_one zetaUnit] at hu
  obtain ⟨k, hk⟩ := FltRegular.CaseI.exists_int_sum_eq_zero hζ' a b 1 hu.symm (by lia)
  simp only [zpow_one, zpow_neg, mem_span_singleton] at hk
  have hpcoe : (p : ℤ) ≠ 0 := by simp [hpri.out.ne_zero]
  have hζ_map : (algebraMap R K) ζ = ζ' := rfl
  refine ⟨⟨(2 * k % p).natAbs, ?_⟩, ⟨((2 * k - 1) % p).natAbs, ?_⟩, ?_, ?_⟩
  repeat'
    rw [← natAbs_natCast p]
    refine natAbs_lt_natAbs_of_nonneg_of_lt (emod_nonneg _ hpcoe) ?_
    rw [natAbs_natCast]
    exact emod_lt_of_pos _ (by simp [hpri.out.pos])
  · simp only [natAbs_of_nonneg (emod_nonneg _ hpcoe), ← ZMod.intCast_eq_intCast_iff,
      ZMod.intCast_mod, Int.cast_sub, Int.cast_mul, Int.cast_one]
  simp only [add_sub_assoc, sub_sub] at hk ⊢
  convert! hk using 3
  rw [mul_add, mul_comm (↑a : R), ← mul_assoc _ (↑b : R), mul_comm _ (↑b : R),
    mul_assoc (↑b : R)]
  congr 2
  · ext
    simp only [map_pow, NumberField.Units.coe_zpow, hζ_map]
    change ζ' ^ ↑(2 * k % ↑p).natAbs = ζ' ^ (2 * k)
    refine eq_of_div_eq_one ?_
    rw [← zpow_natCast, ← zpow_sub₀ (hζ'.ne_zero hpri.out.ne_zero), hζ'.zpow_eq_one_iff_dvd]
    simp only [natAbs_of_nonneg (emod_nonneg _ hpcoe), ← ZMod.intCast_zmod_eq_zero_iff_dvd,
      Int.cast_sub, ZMod.intCast_mod, Int.cast_mul, sub_self]
  · ext
    simp only [map_pow, _root_.map_mul, NumberField.Units.coe_zpow, map_units_inv, hζ_map]
    change ζ' ^ ↑((2 * k - 1) % ↑p).natAbs = ζ' ^ (2 * k) * ζ'⁻¹
    refine eq_of_div_eq_one ?_
    rw [← zpow_natCast, ← zpow_sub_one₀ (hζ'.ne_zero hpri.out.ne_zero), ←
      zpow_sub₀ (hζ'.ne_zero hpri.out.ne_zero), hζ'.zpow_eq_one_iff_dvd]
    simp only [natAbs_of_nonneg (emod_nonneg _ hpcoe), ← ZMod.intCast_zmod_eq_zero_iff_dvd,
      Int.cast_sub, ZMod.intCast_mod, Int.cast_mul, Int.cast_one, sub_self]

/-- Case I with additional assumptions. -/
theorem caseI_easier {a b c : ℤ} (hreg : IsRegularPrime p) (hp5 : 5 ≤ p)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1) (hab : ¬a ≡ b [ZMOD p])
    (caseI : ¬↑p ∣ a * b * c) :
    a ^ p + b ^ p ≠ c ^ p := by
  set ζ := zeta p ℤ R
  have hζ := zeta_spec p ℤ R
  intro H
  obtain ⟨k₁, k₂, hcong, hdiv⟩ := ex_fin_div hp5 hreg hζ hgcd caseI H
  have key :
      ↑(p : ℤ) ∣ ∑ j : Fin p, caseICoeff a b k₁ k₂ j • ζ ^ (j : ℕ) := by
    rw [sum_caseICoeff hpri.out.one_lt]
    exact hdiv
  have hall := dvd_coeff_cycl_integer hpri.out hζ
    (exists_caseICoeff_eq_zero hp5 a b k₁ k₂) key
  by_cases hk₁ : (k₁ : ℕ) = 0
  · have hk₂ : (k₂ : ℕ) ≠ 1 := by
      intro hk₂
      have hp2z : (p : ℤ) ∣ 2 := by
        rw [← Int.dvd_neg]
        simpa [hk₁, hk₂] using hcong.dvd
      have hp2 : p ∣ 2 := by exact_mod_cast hp2z
      have := Nat.le_of_dvd (by omega : 0 < 2) hp2
      omega
    have hb : (p : ℤ) ∣ b := by
      simpa [caseICoeff, hk₁, hk₂, Ne.symm hk₂] using hall ⟨1, by omega⟩
    exact caseI (Dvd.dvd.mul_right (Dvd.dvd.mul_left hb a) c)
  · by_cases hk₂ : (k₂ : ℕ) = 0
    · have habdvd : (p : ℤ) ∣ a - b := by
        simpa [caseICoeff, hk₁, Ne.symm hk₁, hk₂] using hall ⟨0, by omega⟩
      apply hab
      rw [Int.modEq_iff_dvd]
      simpa only [neg_sub] using Int.dvd_neg.mpr habdvd
    · have ha : (p : ℤ) ∣ a := by
        simpa [caseICoeff, hk₁, hk₂, Ne.symm hk₁, Ne.symm hk₂] using hall ⟨0, by omega⟩
      exact caseI (Dvd.dvd.mul_right (Dvd.dvd.mul_right ha b) c)

/-- Case I. -/
theorem caseI {a b c : ℤ} {p : ℕ} [Fact p.Prime] (hreg : IsRegularPrime p)
    (caseI : ¬↑p ∣ a * b * c) : a ^ p + b ^ p ≠ c ^ p :=
  FltRegular.CaseI.may_assume
    (fun _ _ _ _ _ hreg hp5 hunit hxy hI h ↦ caseI_easier hreg hp5 hunit hxy hI h) hreg caseI

end FltRegular
