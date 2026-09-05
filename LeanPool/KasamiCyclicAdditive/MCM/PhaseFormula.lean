/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude
import LeanPool.KasamiCyclicAdditive.Phase.CharacterSums
import LeanPool.KasamiCyclicAdditive.Counting.Definitions
import LeanPool.KasamiCyclicAdditive.Phase.DillonKashyapInterface
import LeanPool.KasamiCyclicAdditive.Phase.AdditiveCharacter
import LeanPool.KasamiCyclicAdditive.MCM.Fourier
import LeanPool.KasamiCyclicAdditive.MCM.Permutation
import LeanPool.KasamiCyclicAdditive.MCM.DicksonPhase
import LeanPool.KasamiCyclicAdditive.MCM.ComplementTransport

/-!
# The MCM/Dickson phase formula

Proves the Dillon--Kashyap phase formula `DillonKashyapPhaseFormula` directly
from the derivative-image half-size equation plus the MCM/Dickson identities —
no Dillon--Kashyap or Dillon--Dobbertin Fourier theorem is imported.
-/

open Finset Polynomial

namespace KasamiCyclicAdditive

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

section PhaseHelpers

omit [DecidableEq K] in
/-- Frobenius invariance of the Gauss sum in the source field. -/
private lemma gaussSum_sq_eq {psi : AddChar K ℂ} (hsq : ∀ x : K, psi (x ^ 2) = psi x)
    (chi : MulChar K ℂ) : gaussSum (chi ^ 2) psi = gaussSum chi psi := by
  have hb : Function.Bijective (fun x : K => x ^ 2) := by
    have h := (frobeniusEquiv K 2).bijective
    have hfun : (fun x : K => x ^ 2) = ⇑(frobenius K 2) := by
      funext x; rw [frobenius_def]
    rw [hfun]; exact h
  let e : K ≃ K := Equiv.ofBijective _ hb
  rw [gaussSum, gaussSum, ← e.sum_comp (fun x => chi x * psi x)]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hex : e x = x ^ 2 := rfl
  rw [hex, hsq, map_pow, pow_two, pow_two, MulChar.mul_apply]

omit [DecidableEq K] in
/-- Hence the Gauss sum is unchanged by any `2 ^ j`-power of the character. -/
private lemma gaussSum_pow_two_pow {psi : AddChar K ℂ} (hsq : ∀ x : K, psi (x ^ 2) = psi x) :
    ∀ (j : ℕ) (chi : MulChar K ℂ), gaussSum (chi ^ 2 ^ j) psi = gaussSum chi psi := by
  intro j
  induction j with
  | zero => intro chi; simp
  | succ j ih =>
      intro chi
      have hpow : chi ^ 2 ^ (j + 1) = (chi ^ 2) ^ 2 ^ j := by
        rw [← pow_mul, pow_succ, mul_comm]
      rw [hpow, ih, gaussSum_sq_eq hsq]

omit [DecidableEq K] [CharP K 2] in
/-- `|K|` is nonzero in `ℂ`. -/
private lemma cast_card_ne_zero : ((Fintype.card K : ℂ)) ≠ 0 := by
  simp

/-- A coprime power relation and an order divisibility bound force the element to be one. -/
lemma eq_one_of_pow_eq_one_of_coprime_order_dvd
    {G : Type*} [Monoid G] {x : G} {a N : ℕ}
    (hcop : Nat.Coprime a N) (hpow : x ^ a = 1) (hord : orderOf x ∣ N) :
    x = 1 := by
  have h1 : orderOf x ∣ a := orderOf_dvd_of_pow_eq_one hpow
  have h2 : Nat.Coprime (orderOf x) N := Nat.Coprime.coprime_dvd_left h1 hcop
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h2 hord)

omit [CharP K 2] in
/-- A character killed by an exponent coprime to `|Kˣ|` is principal. -/
private lemma mulChar_eq_one_of_coprime {chi : MulChar K ℂ} {a : ℕ}
    (hcop : Nat.Coprime a (Fintype.card Kˣ)) (h : chi ^ a = 1) : chi = 1 := by
  have hord : orderOf chi ∣ Fintype.card Kˣ :=
    orderOf_dvd_of_pow_eq_one (MulChar.pow_card_eq_one chi)
  exact eq_one_of_pow_eq_one_of_coprime_order_dvd hcop h hord

/-- The Delta-weighted character sum is `mcmCharSum + mcmTwistedCharSum`. -/
private lemma delta_sum_eq_A0_add_A1 {k : ℕ}
    (hhalf : 2 * (derivativeImage k K).card = Fintype.card K)
    {chi : MulChar K ℂ} (hchi : chi ≠ 1) :
    (∑ x : Kˣ, (if (x : K) ∈ derivativeImage k K then (1 : ℂ) else -1) * chi (x : K))
      = mcmCharSum k chi + mcmTwistedCharSum k (primitiveAddChar K) chi := by
  rw [KasamiCyclicAdditive.sum_units_eq_sum
    (fun x : K => (if x ∈ derivativeImage k K then (1 : ℂ) else -1) * chi x)
    (by simp [MulChar.map_zero chi])]
  have h1 : ∀ x : K, (if x ∈ derivativeImage k K then (1 : ℂ) else -1) * chi x
      = 2 * ((if x ∈ derivativeImage k K then (1 : ℂ) else 0) * chi x) - chi x := by
    intro x; split <;> ring
  simp_rw [h1]
  rw [Finset.sum_sub_distrib, MulChar.sum_eq_zero_of_ne_one hchi, sub_zero, ← Finset.mul_sum]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
  rw [mcm_halfspace_sum hhalf (fun x => chi x), mcmCharSum, mcmTwistedCharSum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

omit [DecidableEq K] [CharP K 2] in
/-- Coprimality forces a character power to be nontrivial outside the cubic case. -/
private lemma pow_two_pow_add_one_ne_one_of_cube_ne_one
    {n k m : ℕ}
    (hcard : Fintype.card K = 2 ^ n) (he : 2 ^ k + 1 = 3 * m)
    (hcop : Nat.Coprime m (2 ^ n - 1)) {chi : MulChar K ℂ} (hchi3 : chi ^ 3 ≠ 1) :
    chi ^ (2 ^ k + 1) ≠ 1 := by
  classical
  intro hcon
  apply hchi3
  rw [he, pow_mul] at hcon
  have hord : orderOf (chi ^ 3) ∣ Fintype.card Kˣ :=
    orderOf_dvd_of_pow_eq_one (MulChar.pow_card_eq_one (chi ^ 3))
  have hcardU : Fintype.card Kˣ = 2 ^ n - 1 := by
    rw [Fintype.card_units K, hcard]
  rw [hcardU] at hord
  exact eq_one_of_pow_eq_one_of_coprime_order_dvd hcop hcon hord

omit [Fintype K] [DecidableEq K] in
/-- In characteristic two, the cubic Dickson polynomial evaluates multiplicatively. -/
private lemma dickson_three_mulChar_eval (chi : MulChar K ℂ) (b : K) :
    chi ((dickson 1 1 3).eval b) = chi b * (chi ^ 2) (1 - b) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hev : (dickson (R := K) 1 1 3).eval b = b * (1 - b) ^ 2 := by
    rw [show (3 : ℕ) = 1 + 2 from rfl, dickson_add_two, show (1 : ℕ) + 1 = 2 from rfl,
      dickson_add_two, show (0 : ℕ) + 1 = 1 from rfl]
    simp only [dickson_zero, dickson_one, eval_sub, eval_mul, eval_X, eval_C, eval_ofNat,
      eval_one, Nat.cast_one]
    linear_combination (b ^ 2 - 2 * b) * h2
  rw [hev, map_mul, map_pow, pow_two, pow_two, MulChar.mul_apply]

omit [DecidableEq K] in
/-- The generic twisted MCM sum factors into three Gauss sums. -/
lemma mcmTwistedCharSum_eq_gaussSum_mul_gaussSum_div_gaussSum_of_generic
    {n k : ℕ} (hklt : k < n) (hcard : Fintype.card K = 2 ^ n) (hk : Odd k)
    (hkn : Nat.Coprime k n) {chi : MulChar K ℂ}
    (hchie : chi ^ (2 ^ k + 1) ≠ 1) (hchi3 : chi ^ 3 ≠ 1) :
    mcmTwistedCharSum k (primitiveAddChar K) chi =
      gaussSum chi (primitiveAddChar K) * gaussSum (chi ^ (2 ^ k + 1)) (primitiveAddChar K) /
        gaussSum (chi ^ 3) (primitiveAddChar K) := by
  classical
  have hprim : (primitiveAddChar K).IsPrimitive := primitiveAddChar_isPrimitive
  have hsq : ∀ x : K, primitiveAddChar K (x ^ 2) = primitiveAddChar K x :=
    primitiveAddChar_sq
  rw [mcmTwistedCharSum_eq_dickson hklt hcard hk _ hprim hsq chi hchie,
    sum_dickson_kasami_eq_three hcard hk hkn (fun x : K => chi x)]
  have hjac : ∑ b : K, chi ((dickson 1 1 3).eval b) = jacobiSum chi (chi ^ 2) := by
    rw [jacobiSum]
    exact Finset.sum_congr rfl fun b _ => dickson_three_mulChar_eval chi b
  have hchi3' : chi * chi ^ 2 = chi ^ 3 := by
    rw [show (3 : ℕ) = 1 + 2 from rfl, pow_add, pow_one]
  have hjac2 : jacobiSum chi (chi ^ 2) =
      gaussSum chi (primitiveAddChar K) * gaussSum chi (primitiveAddChar K) /
        gaussSum (chi ^ 3) (primitiveAddChar K) := by
    rw [jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum cast_card_ne_zero
      (by rw [hchi3']; exact hchi3) hprim, gaussSum_sq_eq hsq, hchi3']
  have hcardU : Fintype.card Kˣ = 2 ^ n - 1 := by
    rw [Fintype.card_units, hcard]
  have hoddU : Odd (Fintype.card Kˣ) := by
    rw [hcardU]
    refine Nat.Even.sub_odd Nat.one_le_two_pow ?_ odd_one
    exact Nat.even_pow.mpr ⟨even_iff_two_dvd.mpr dvd_rfl, by omega⟩
  have h2cop : Nat.Coprime 2 (Fintype.card Kˣ) := Nat.coprime_two_left.mpr hoddU
  have hr1 : chi ^ (2 ^ k) ≠ 1 := by
    intro h
    apply hchi3
    have hone : chi = 1 := mulChar_eq_one_of_coprime (Nat.Coprime.pow_left _ h2cop) h
    rw [hone]
    simp
  have hGr : gaussSum (chi ^ 2 ^ k) (primitiveAddChar K) =
      gaussSum chi (primitiveAddChar K) :=
    gaussSum_pow_two_pow hsq k chi
  have hGchi_ne : gaussSum chi (primitiveAddChar K) ≠ 0 :=
    gaussSum_ne_zero_of_primitive hprim chi
  have hGe_ne : gaussSum (chi ^ (2 ^ k + 1)) (primitiveAddChar K) ≠ 0 :=
    gaussSum_ne_zero_of_primitive hprim (chi ^ (2 ^ k + 1))
  have hinvr : gaussSum ((chi⁻¹) ^ 2 ^ k) (primitiveAddChar K) =
      (Fintype.card K : ℂ) / gaussSum chi (primitiveAddChar K) := by
    have h := KasamiCyclicAdditive.gaussSum_mul_inv hprim hr1
    rw [hGr] at h
    rw [inv_pow, eq_div_iff hGchi_ne, mul_comm]
    exact h
  have hinve : gaussSum ((chi⁻¹) ^ (2 ^ k + 1)) (primitiveAddChar K) =
      (Fintype.card K : ℂ) / gaussSum (chi ^ (2 ^ k + 1)) (primitiveAddChar K) := by
    have h := KasamiCyclicAdditive.gaussSum_mul_inv hprim hchie
    rw [inv_pow, eq_div_iff hGe_ne, mul_comm]
    exact h
  rw [hjac, hjac2, hinvr, hinve]
  field_simp

end PhaseHelpers

/-- The weighted character sum has the stated value for the principal character. -/
private lemma phase_formula_principal_case
    {k : ℕ} (hhalf : 2 * (derivativeImage k K).card = Fintype.card K) :
    (∑ x : Kˣ, (if (x : K) ∈ derivativeImage k K then (1 : ℂ) else -1) *
      (1 : MulChar K ℂ) (x : K)) =
      gaussSum (1 : MulChar K ℂ) (primitiveAddChar K) *
        gaussSum ((1 : MulChar K ℂ) ^ (2 ^ k + 1)) (primitiveAddChar K) /
          gaussSum ((1 : MulChar K ℂ) ^ 3) (primitiveAddChar K) := by
  have hprim : (primitiveAddChar K).IsPrimitive := primitiveAddChar_isPrimitive
  simp only [one_pow, gaussSum_principal hprim]
  rw [KasamiCyclicAdditive.sum_units_eq_sum
    (fun x : K => (if x ∈ derivativeImage k K then (1 : ℂ) else -1) *
      (1 : MulChar K ℂ) x)
    (by simp [MulChar.map_zero])]
  have h1 : ∀ x : K, (if x ∈ derivativeImage k K then (1 : ℂ) else -1) *
      (1 : MulChar K ℂ) x =
      (if x ∈ derivativeImage k K then (1 : ℂ) else -1) -
        (if x = 0 then (if x ∈ derivativeImage k K then (1 : ℂ) else -1) else 0) := by
    intro x
    by_cases hx : x = 0 <;>
      simp [hx, MulChar.one_apply, isUnit_iff_ne_zero, MulChar.map_nonunit]
  simp_rw [h1]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq']
  have hd : ∑ x : K, (if x ∈ derivativeImage k K then (1 : ℂ) else -1) = 0 := by
    have h2 : ∀ x : K, (if x ∈ derivativeImage k K then (1 : ℂ) else -1) =
        2 * (if x ∈ derivativeImage k K then (1 : ℂ) else 0) - 1 := by
      intro x
      split <;> ring
    simp_rw [h2]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_univ]
    have hcast : (2 : ℂ) * ((derivativeImage k K).card : ℂ) = (Fintype.card K : ℂ) := by
      exact_mod_cast congrArg (fun t : ℕ => (t : ℂ)) hhalf
    rw [hcast]
    ring
  rw [hd, ite_eq_left (Finset.mem_univ (0 : K)), ite_eq_left (zero_mem_derivativeImage k)]
  norm_num

/-- The weighted character sum has the stated value for a nonprincipal cubic character. -/
private lemma phase_formula_cubic_case
    {n k m : ℕ} (hklt : k < n) (hk : Odd k) (hcard : Fintype.card K = 2 ^ n)
    (hkn : Nat.Coprime k n) (he : 2 ^ k + 1 = 3 * m)
    (hhalf : 2 * (derivativeImage k K).card = Fintype.card K)
    {chi : MulChar K ℂ} (hchi : chi ≠ 1) (hchi3 : chi ^ 3 = 1) :
    (∑ x : Kˣ, (if (x : K) ∈ derivativeImage k K then (1 : ℂ) else -1) * chi (x : K)) =
      gaussSum chi (primitiveAddChar K) *
        gaussSum (chi ^ (2 ^ k + 1)) (primitiveAddChar K) /
          gaussSum (chi ^ 3) (primitiveAddChar K) := by
  have hprim : (primitiveAddChar K).IsPrimitive := primitiveAddChar_isPrimitive
  have hA0 : mcmCharSum k chi = 0 :=
    mcmCharSum_eq_zero_of_ne_one hklt hcard hk hkn chi hchi
  have he1 : chi ^ (2 ^ k + 1) = 1 := by
    rw [he, pow_mul, hchi3, one_pow]
  have hmcm : ∀ s : K, chi (mcmMap k s) = chi s :=
    cubic_mcm_apply hcard hk hkn chi hchi3
  have hA1 : mcmTwistedCharSum k (primitiveAddChar K) chi =
      gaussSum chi (primitiveAddChar K) := by
    rw [mcmTwistedCharSum, gaussSum]
    exact Finset.sum_congr rfl fun s _ => by rw [hmcm s]; ring
  rw [delta_sum_eq_A0_add_A1 hhalf hchi, hA0, hA1, he1, hchi3, gaussSum_principal hprim]
  norm_num

/-- The weighted character sum has the stated value for generic characters. -/
private lemma phase_formula_generic_case
    {n k m : ℕ} (hklt : k < n) (hk : Odd k) (hcard : Fintype.card K = 2 ^ n)
    (hkn : Nat.Coprime k n) (he : 2 ^ k + 1 = 3 * m)
    (hcop : Nat.Coprime m (2 ^ n - 1))
    (hhalf : 2 * (derivativeImage k K).card = Fintype.card K)
    {chi : MulChar K ℂ} (hchi : chi ≠ 1) (hchi3 : chi ^ 3 ≠ 1) :
    (∑ x : Kˣ, (if (x : K) ∈ derivativeImage k K then (1 : ℂ) else -1) * chi (x : K)) =
      gaussSum chi (primitiveAddChar K) *
        gaussSum (chi ^ (2 ^ k + 1)) (primitiveAddChar K) /
          gaussSum (chi ^ 3) (primitiveAddChar K) := by
  have hA0 : mcmCharSum k chi = 0 :=
    mcmCharSum_eq_zero_of_ne_one hklt hcard hk hkn chi hchi
  have hme : chi ^ (2 ^ k + 1) ≠ 1 :=
    pow_two_pow_add_one_ne_one_of_cube_ne_one hcard he hcop hchi3
  have hA1 :=
    mcmTwistedCharSum_eq_gaussSum_mul_gaussSum_div_gaussSum_of_generic
      hklt hcard hk hkn hme hchi3
  rw [delta_sum_eq_A0_add_A1 hhalf hchi, hA0, hA1, zero_add]

/-- **Phase formula.**  The Dillon--Kashyap phase formula
follows from the half-size packet plus the MCM/Dickson identities; no
Dillon--Kashyap or Dillon--Dobbertin Fourier theorem is imported.

`he` and `hcop` are the normalized arithmetic data.  They are what shows
`chi^(2^k+1) ≠ 1` for every character outside the principal and cubic
exceptional cases. -/
theorem phase_formula_from_half_size
    {n k m : ℕ} (hklt : k < n) (hk : Odd k)
    (hcard : Fintype.card K = 2 ^ n) (hkn : Nat.Coprime k n)
    (he : 2 ^ k + 1 = 3 * m) (hcop : Nat.Coprime m (2 ^ n - 1))
    (hhalf : 2 * (derivativeImage k K).card = Fintype.card K) :
    DillonKashyapPhaseFormula k (primitiveAddChar K) := by
  intro chi
  by_cases hchi : chi = 1
  · subst hchi
    exact phase_formula_principal_case hhalf
  by_cases hchi3 : chi ^ 3 = 1
  · exact phase_formula_cubic_case hklt hk hcard hkn he hhalf hchi hchi3
  · exact phase_formula_generic_case hklt hk hcard hkn he hcop hhalf hchi hchi3

end KasamiCyclicAdditive
