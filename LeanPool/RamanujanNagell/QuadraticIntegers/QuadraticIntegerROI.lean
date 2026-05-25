/-
Copyright (c) 2026 Barinder S. Banwait. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Barinder S. Banwait
-/

/-
Attribution: This file is essentially a port of the content of `RingOfIntegers.lean`
in the mathlib3 repository:
https://github.com/sacerdot/QuadraticIntegers/blob/main/QuadraticIntegers/RingOfIntegers.lean

by Brasca and Monticone. We include the `trace_and_norm` and `d_1` sections needed
to prove `ring_of_integers_neg7`. We are grateful to Riccardo Brasca for helping with
some parts of the formalization.
-/

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Tactic.ModCases
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.Qify
import Mathlib.Tactic

attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticInteger

open QuadraticAlgebra NumberField Set Polynomial Algebra Int IntermediateField

variable {d : ℤ}

local notation3 "K" => QuadraticAlgebra ℚ d 0

local notation3 "R" => QuadraticAlgebra ℤ d 0

variable [sf : Fact (Squarefree d)] [alt : d.natAbs.AtLeastTwo]

instance field : Fact (∀ (r : ℚ), r ^ 2 ≠ d + 0 * r) := by
  refine ⟨fun r h ↦ ?_⟩
  simp only [zero_mul, add_zero] at h
  have h' : IsSquare (d : ℚ) := ⟨r, by linarith [sq_abs r]⟩
  rw [Rat.isSquare_intCast_iff] at h'
  obtain ⟨s, hs⟩ := h'
  have hunit : IsUnit s := sf.1 s (dvd_of_eq hs.symm)
  rcases Int.isUnit_iff.mp hunit with rfl | rfl <;>
    simp only [one_mul, neg_mul, mul_neg, neg_neg] at hs <;>
    subst hs <;>
    exact absurd alt.1 (by norm_num)

@[simp]
lemma re_ratCast (q : ℚ) : (q : K).re = q := by
  have h1 : (q : K) = algebraMap ℚ K q := (eq_ratCast (algebraMap ℚ K) q).symm
  rw [h1, ← QuadraticAlgebra.C_eq_algebraMap, QuadraticAlgebra.re_C]

@[simp]
lemma im_ratCast (q : ℚ) : (q : K).im = 0 := by
  have h1 : (q : K) = algebraMap ℚ K q := (eq_ratCast (algebraMap ℚ K) q).symm
  rw [h1, ← QuadraticAlgebra.C_eq_algebraMap, QuadraticAlgebra.im_C]

lemma ratCast_eq_coe (q : ℚ) : (q : K) = QuadraticAlgebra.C q := by
  have h1 : (q : K) = algebraMap ℚ K q := (eq_ratCast (algebraMap ℚ K) q).symm
  rw [h1, ← QuadraticAlgebra.C_eq_algebraMap]

-- The IntCast ℤ → K goes through ℤ → ℚ → K (via Rat.cast), so re_intCast/im_intCast
-- (which are rfl for QuadraticAlgebra.intCast) don't apply directly.
-- We need versions for the composed cast.
@[simp]
lemma re_intCast_K (n : ℤ) : (↑n : K).re = ↑n := by
  show (↑n : K).re = (↑n : ℚ)
  rw [show (↑n : K) = (↑(↑n : ℚ) : K) from by push_cast; ring]
  exact re_ratCast _

@[simp]
lemma im_intCast_K (n : ℤ) : (↑n : K).im = 0 := by
  rw [show (↑n : K) = (↑(↑n : ℚ) : K) from by push_cast; ring]
  exact im_ratCast _

section trace_and_norm

variable {a b : ℚ}

local notation3 "z" => a + b • (ω : K)

lemma rational_iff : z ∈ range (algebraMap ℚ K) ↔ b = 0 := by
  simp only [mem_range]
  constructor
  · rintro ⟨y, hy⟩
    have h := congr_arg QuadraticAlgebra.im hy
    simp only [omega_im, im_add, im_smul, coe_algebraMap, im_coe, im_ratCast, smul_eq_mul,
               mul_one, zero_add] at h
    exact h.symm
  · rintro rfl; exact ⟨a, by simp⟩

lemma minpoly (hb : b ≠ 0) : minpoly ℚ z = X ^ 2 - C (2 * a) * X + C (a ^ 2 - d * b ^ 2) := by
  refine (minpoly.unique' _ _ (by monicity!) ?_ (fun q qdeg_lt_2 ↦ ?_)).symm
  · calc
      _ = z ^ 2 - 2 * a * z + (a ^ 2 - d * b ^ 2) := by simp
      _ = (b • (ω : K)) ^ 2 - d * b ^ 2 := by ring
      _ = b ^ 2 • ((ω : K) * (ω : K)) - d * b ^ 2 := by rw [smul_pow, pow_two ω]
      _ = 0 := by simp [omega_mul_omega_eq_add, Algebra.smul_def] ; ring
  · replace qdeg_lt_2 : q.degree ≤ 1 := by
      apply Order.le_of_lt_succ
      convert qdeg_lt_2; symm; compute_degree!
    rw [eq_X_add_C_of_degree_le_one qdeg_lt_2]
    refine imp_iff_or_not.1 (fun h ↦ ?_)
    simp only [map_add, map_mul, aeval_C, eq_ratCast, aeval_X] at h
    by_cases hcoe_one : (q.coeff 1 : K) = 0
    · simp_all
    replace h : z = - (q.coeff 0) / (q.coeff 1) := by grind [eq_div_iff]
    contrapose hb
    exact (rational_iff (a := a) (d := d)).1 ⟨-q.coeff 0 / q.coeff 1, by simp [h]⟩

lemma adjoin_z_eq_top (h : b ≠ 0) : ℚ⟮z⟯ = ⊤ := by
  apply (Field.primitive_element_iff_minpoly_natDegree_eq ℚ z).mpr
  rw [finrank_eq_two, minpoly h]
  compute_degree!

lemma trace : trace ℚ K z = 2 * a := by
  rcases eq_or_ne b 0 with rfl | h
  · simpa [finrank_eq_two] using trace_algebraMap (S := K) a
  · rw [trace_eq_finrank_mul_minpoly_nextCoeff ℚ z, minpoly h, adjoin_z_eq_top h]
    set p := X ^ 2 - C (2 * a) * X + C (a ^ 2 - d * b ^ 2) with hp_def
    have p_deg_2 : p.natDegree = 2 := by rw [hp_def]; compute_degree!
    rw [nextCoeff_of_natDegree_pos (p := p) (by grind)]
    simp only [IntermediateField.finrank_top, Nat.cast_one, p_deg_2, Nat.add_one_sub_one, mul_neg,
      one_mul]
    simp only [hp_def, map_mul, map_sub, map_pow, map_intCast, coeff_add, coeff_sub, coeff_X_pow,
      OfNat.one_ne_ofNat, ↓reduceIte, coeff_mul_X, mul_coeff_zero, coeff_C_zero, zero_sub,
      coeff_intCast_mul, neg_add_rev, neg_sub, neg_neg, add_eq_right]
    rw [← Polynomial.C_pow, ← Polynomial.C_pow, coeff_C, coeff_C]
    simp

lemma norm : norm ℚ z = a ^ 2 - d * b ^ 2 := by
    rcases eq_or_ne b 0 with rfl | h
    · simp only [zero_smul, add_zero]
      rw [show (↑a : K) = algebraMap ℚ K a from (eq_ratCast _ a).symm,
          Algebra.norm_algebraMap, finrank_eq_two]
      ring
    · let pb := PowerBasis.ofAdjoinEqTop' (IsIntegral.isIntegral z)
        (by simpa using adjoin_z_eq_top h)
      have : z = pb.gen := by simp [pb]
      rw [this, pb.norm_gen_eq_coeff_zero_minpoly, ← this, minpoly h, ← pb.finrank]
      simp [finrank_eq_two, coeff_zero_eq_eval_zero]

section integrality

lemma trace_int (hz : IsIntegral ℤ z) : ∃ (t : ℤ), t = 2 * a := by
  simpa [trace, IsIntegrallyClosed.isIntegral_iff] using isIntegral_trace (L := ℚ) hz

lemma a_half_int (hz : IsIntegral ℤ z) (ha : ¬(∃ (A : ℤ), A = a)) :
    ∃ (A : ℤ), A = a - 2⁻¹ := by
  obtain ⟨t, ht⟩ := trace_int hz
  refine ⟨(t - 1) / 2, ?_⟩
  obtain ⟨k, rfl⟩ : Odd t := by
    refine not_even_iff_odd.1 (fun ⟨n, hn⟩ ↦ ha ⟨t / 2, ?_⟩)
    rw [hn] at ht
    grind
  rw [cast_div ⟨k, by grind⟩ (by norm_num)]
  grind

lemma norm_int (hz : IsIntegral ℤ z) : ∃ (n : ℤ), n = a ^ 2 - d * b ^ 2 := by
  simpa [norm, IsIntegrallyClosed.isIntegral_iff] using isIntegral_norm ℚ hz

noncomputable def n (hz : IsIntegral ℤ z) := (norm_int hz).choose

lemma n_spec (hz : IsIntegral ℤ z) : n hz = a ^ 2 - d * b ^ 2 := (norm_int hz).choose_spec

lemma four_n (hz : IsIntegral ℤ z) : 4 * n hz = (2 * a)^2 - d * (2 * b) ^ 2 := by
  grind [n_spec]

lemma squarefree_mul {n : ℤ} {r : ℚ} (hn : Squarefree n) (hnr : ∃ (m : ℤ), n * r ^ 2 = m) :
    ∃ (t : ℤ), t = r := by
  rcases eq_or_ne r 0 with rfl | hr0
  · simp
  refine ⟨r.num, ?_⟩
  suffices IsUnit (r.den : ℤ) by
    rcases isUnit_iff.1 this with H | H
    · simpa using r.coe_int_num_of_den_eq_one (by grind)
    · grind
  refine hn _ ?_
  rw [← sq]
  obtain ⟨m, hm⟩ := hnr
  have hd : (r.den : ℚ)^2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr r.pos.ne')
  have hq : (n : ℚ) * r.num ^ 2 = (r.den : ℚ)^2 * m := by
    rw [← r.num_div_den, div_pow, mul_div_assoc'] at hm
    rw [div_eq_iff hd] at hm; linarith
  exact (r.isCoprime_num_den.symm.pow_right.pow_left).dvd_of_dvd_mul_right
    ⟨m, by exact_mod_cast hq⟩

lemma two_b_int (hz : IsIntegral ℤ z) : ∃ (B₂ : ℤ), B₂ = 2 * b := by
  obtain ⟨y, hy⟩ := trace_int hz
  exact squarefree_mul sf.out ⟨y ^ 2 - (4 * n hz), by push_cast; rw [hy]; linarith [four_n hz]⟩

lemma b_int_of_a_int (hz : IsIntegral ℤ z) (ha : ∃ (A : ℤ), A = a) : ∃ (B : ℤ), B = b := by
  obtain ⟨A, hA⟩ := ha
  exact squarefree_mul sf.out ⟨A ^ 2 - (n hz), by push_cast; rw [hA]; linarith [n_spec hz]⟩

end integrality

end trace_and_norm

section d_1

variable [h : Fact (d ≡ 1 [ZMOD 4])]

local notation3 "e" => (d - 1) / 4

omit sf alt in
lemma e_spec : 4 * e = d - 1 :=
  mul_ediv_cancel_of_emod_eq_zero <| emod_eq_emod_iff_emod_sub_eq_zero.mp h.1

local notation3 "S" => QuadraticAlgebra ℤ e 1

lemma algebra_S_K : ((1 + (ω : K)) / 2) * ((1 + ω) / 2) = e • 1 + 1 • ((1 + ω) / 2) :=
  calc (1 + (ω : K)) / 2 * ((1 + ω) / 2) = (1 + 2 * ω + ω * ω) / 4 := by ring
      _ = (1 + 2 * ω + (↑(4 * e + 1) : ℚ) • 1) / 4 := by simp [omega_mul_omega_eq_add, e_spec]
      _ = e • 1 + 1 • ((1 + ω) / 2) := by simp [Algebra.smul_def]; ring

private instance : Algebra S K := (lift ⟨(1 + ω) / 2, algebra_S_K⟩).toRingHom.toAlgebra

lemma algebraMap_S_K_omega : algebraMap S K ω = 2⁻¹ * (ω + 1) := by
  convert lift_symm_apply_coe _
  simp
  grind

lemma easy_incl_d_1 : IsIntegral ℤ (algebraMap S K ω) :=
  (IsIntegral.isIntegral ω).algebraMap

lemma d_1_int {a b : ℚ} (hz : IsIntegral ℤ (a + b • (ω : K))) (ha : ∃ (A : ℤ), A = a) :
    a + b • (ω : K) ∈ range (algebraMap S K) := by
  obtain ⟨B, rfl⟩ := b_int_of_a_int hz ha
  obtain ⟨A, rfl⟩ := ha
  rw [← RingHom.coe_range, cast_smul_eq_zsmul, zsmul_eq_mul]
  refine Subring.add_mem _ (by simp) (Subring.mul_mem _ (by simp) ⟨2 * ω - 1, ?_⟩)
  simp [map_ofNat, algebraMap_S_K_omega]

theorem d_1 : IsIntegralClosure S ℤ K := by
  refine ⟨fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h ↦ ?_, @fun ⟨a, b⟩ ↦ ⟨fun hz ↦ ?_, fun ⟨x, hx⟩ ↦ ?_⟩⟩
  · simp only [mk_eq_add_smul_omega, zsmul_eq_mul, map_add,
    map_intCast, map_mul] at h
    have hre := congr_arg QuadraticAlgebra.re h
    have him := congr_arg QuadraticAlgebra.im h
    simp only [algebraMap_S_K_omega, re_add, re_mul, omega_re, re_one,
      im_add, omega_im, im_one, im_mul, mul_one, mul_zero,
      zero_mul, zero_add, add_zero, map_intCast, re_intCast_K, im_intCast_K,
      ] at hre him
    have h2re : (2⁻¹ : K).re = (2 : ℚ)⁻¹ := by
      conv_lhs => rw [show (2⁻¹ : K) = (↑(2⁻¹ : ℚ) : K) from by push_cast; ring]
      exact re_ratCast _
    have h2im : (2⁻¹ : K).im = 0 := by
      conv_lhs => rw [show (2⁻¹ : K) = (↑(2⁻¹ : ℚ) : K) from by push_cast; ring]
      exact im_ratCast _
    rw [h2re, h2im] at hre him
    -- Simplify (algebraMap S K) ((algebraMap ℤ S) n) to (n : K)
    have hcast : ∀ n : ℤ, (algebraMap S K) ((algebraMap ℤ S) n) = (n : K) := by
      intro n
      rw [← IsScalarTower.algebraMap_apply]
      exact (eq_intCast _ n)
    rw [hcast a₁, hcast a₂] at hre him
    simp only [re_intCast_K, im_intCast_K, mul_zero, add_zero, zero_add] at hre him
    -- him : ↑b₁ * 2⁻¹ = ↑b₂ * 2⁻¹ in ℚ
    have hb : b₁ = b₂ := by
      exact_mod_cast mul_right_cancel₀ (show (2 : ℚ)⁻¹ ≠ 0 by norm_num) him
    have ha : a₁ = a₂ := by
      have hb' : (b₁ : ℚ) = b₂ := by exact_mod_cast hb
      exact_mod_cast show (a₁ : ℚ) = a₂ by linarith
    exact QuadraticAlgebra.ext ha hb
  · have key : (⟨a, b⟩ : K) = ↑a + b • (ω : K) := by
      rw [ratCast_eq_coe]
      exact mk_eq_add_smul_omega a b
    rw [key]
    by_cases ha : ∃ (A : ℤ), A = (a : ℚ)
    · exact d_1_int (key ▸ hz) ha
    · let z' := ↑a + b • (ω : K) - algebraMap S K ω
      have hz_conv : IsIntegral ℤ (↑a + b • (ω : K)) := key ▸ hz
      obtain ⟨A, hA⟩ := a_half_int hz_conv ha
      obtain ⟨B, hB⟩ := two_b_int hz_conv
      have hz' : IsIntegral ℤ z' := hz_conv.sub easy_incl_d_1
      rsuffices ⟨y, hy⟩ : ∃ y, (algebraMap S K) y = z'
      · exact ⟨y + ω, by simp [hy, z']⟩
      have H : z' = ↑(a - 2⁻¹) + (b - 2⁻¹) • (ω : K) := by
        simp [z', algebraMap_S_K_omega, Algebra.smul_def]
        grind
      rw [H] at hz' ⊢
      exact d_1_int hz' (a_half_int hz_conv ha)
  · exact hx ▸ (IsIntegral.isIntegral x).algebraMap

end d_1

end QuadraticInteger
