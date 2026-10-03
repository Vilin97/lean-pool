/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Arith.Local.Val
public import Mathlib.RingTheory.Polynomial.Content

/-! Determinant perturbation bound and primitive constant reduction.
Adapted from Li2Unified/Modular/Base/DetCongruence.lean and PrimitiveReduction.lean
(li2-light-certs-2026-09-29/repo-simplify), restated for `Zeta32.Arith.Local.VG/GV`. -/

public section

open Polynomial
open scoped BigOperators
namespace Zeta32.Arith.Local
variable {p : ℕ} [hp : Fact p.Prime]

lemma GV.prod_sub_prod {ι : Type*} (s : Finset ι) {F G : ι → ℚ[X]}
    {r : ι → ℚ} {δ : ℚ}
    (hF : ∀ i ∈ s, GV p (F i) (r i))
    (hG : ∀ i ∈ s, GV p (G i) (r i))
    (hFG : ∀ i ∈ s, GV p (F i - G i) (r i + δ)) :
    GV p ((∏ i ∈ s, F i) - ∏ i ∈ s, G i) ((∑ i ∈ s, r i) + δ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GV.zero (p := p) δ
  | insert a s ha ih =>
    have hFs := fun i hi => hF i (Finset.mem_insert_of_mem hi)
    have hGs := fun i hi => hG i (Finset.mem_insert_of_mem hi)
    have hFGs := fun i hi => hFG i (Finset.mem_insert_of_mem hi)
    have h1 := (hFG a (Finset.mem_insert_self _ _)).mul (GV.prod s hFs)
    have h2 := (hG a (Finset.mem_insert_self _ _)).mul (ih hFs hGs hFGs)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have he : F a * (∏ i ∈ s, F i) - G a * (∏ i ∈ s, G i) =
        (F a - G a) * (∏ i ∈ s, F i) +
          G a * ((∏ i ∈ s, F i) - ∏ i ∈ s, G i) := by ring
    rw [he]
    apply GV.add
    · convert h1 using 1; ring
    · convert h2 using 1; ring

theorem det_sub_GV {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : Matrix ι ι ℚ[X]) (ρ κ : ι → ℚ) (δ : ℚ)
    (hM : ∀ i j, GV p (M i j) (ρ i + κ j))
    (hN : ∀ i j, GV p (N i j) (ρ i + κ j))
    (hMN : ∀ i j, GV p (M i j - N i j) (ρ i + κ j + δ)) :
    GV p (M.det - N.det) ((∑ i, ρ i) + (∑ j, κ j) + δ) := by
  classical
  rw [Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
  apply GV.sum
  intro σ _
  have h := GV.prod_sub_prod Finset.univ
    (fun i _ => hM (σ i) i) (fun i _ => hN (σ i) i) (fun i _ => hMN (σ i) i)
  have he : (∑ i, (ρ (σ i) + κ i)) + δ = (∑ i, ρ i) + (∑ i, κ i) + δ := by
    rw [Finset.sum_add_distrib, Equiv.sum_comp σ ρ]
  rw [he] at h
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul, one_smul]
    exact h
  · simpa only [hs, Units.neg_smul, one_smul, neg_sub_neg, neg_sub] using h.neg

omit hp in
lemma VG.round_half {q : ℚ} (r : ℤ) (h : VG p q ((r : ℚ) + 1 / 2)) :
    VG p q ((r : ℚ) + 1) := by
  rcases h with h | h
  · exact Or.inl h
  right
  have ht : (r : ℚ) < padicValRat p q := by linarith
  have hi : r < padicValRat p q := by exact_mod_cast ht
  exact_mod_cast (Int.add_one_le_iff.mpr hi)

lemma primitive_exists_coeff_not_dvd (P : ℤ[X]) (hP : P.IsPrimitive) :
    ∃ k, ¬(p : ℤ) ∣ P.coeff k := by
  by_contra h
  push Not at h
  have hu := hP (p : ℤ) ((Polynomial.C_dvd_iff_dvd_coeff _ _).mpr h)
  exact (Nat.prime_iff_prime_int.mp hp.out).not_isUnit hu

theorem primitive_constant_reduction_of_dvd (P : ℤ[X]) (hP : P.IsPrimitive)
    (hdiv : ∀ k, k ≠ 0 → (p : ℤ) ∣ P.coeff k) :
    ∃ c : ZMod p, c ≠ 0 ∧ P.map (Int.castRingHom (ZMod p)) = C c := by
  have h0 : ¬(p : ℤ) ∣ P.coeff 0 := by
    intro h0
    obtain ⟨k, hk⟩ := primitive_exists_coeff_not_dvd (p := p) P hP
    by_cases he : k = 0
    · exact hk (by simpa only [he] using h0)
    · exact hk (hdiv k he)
  refine ⟨(P.coeff 0 : ZMod p), ?_, ?_⟩
  · exact fun h => h0 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  · ext k
    rw [coeff_map, coeff_C]
    by_cases hk : k = 0
    · subst k
      simp
    · rw [ite_eq_right hk]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hdiv k hk)

theorem primitive_constant_reduction_of_strict_min (P : ℤ[X]) (hP : P.IsPrimitive)
    (hmin : ∀ k, k ≠ 0 → P.coeff k ≠ 0 →
      padicValInt p (P.coeff 0) < padicValInt p (P.coeff k)) :
    ∃ c : ZMod p, c ≠ 0 ∧ P.map (Int.castRingHom (ZMod p)) = C c := by
  apply primitive_constant_reduction_of_dvd P hP
  intro k hk
  by_cases hz : P.coeff k = 0
  · rw [hz]
    exact dvd_zero _
  · have hv : 1 ≤ padicValInt p (P.coeff k) := by have := hmin k hk hz; omega
    simpa only [pow_one] using (padicValInt_dvd_iff (p := p) 1 (P.coeff k)).mpr (Or.inr hv)

lemma unit_of_VG_sub {q c : ℚ} (hc : c ≠ 0) (hcval : padicValRat p c = 0)
    (h : VG p (q - c) 1) : q ≠ 0 ∧ padicValRat p q = 0 := by
  have hq : q ≠ 0 := by
    intro hq
    rw [hq, zero_sub] at h
    rcases h with he | he
    · exact hc (neg_eq_zero.mp he)
    · rw [padicValRat.neg, hcval] at he
      norm_num at he
  refine ⟨hq, ?_⟩
  by_cases he : q - c = 0
  · rw [sub_eq_zero.mp he]
    exact hcval
  have hv := h.resolve_left he
  have hv' : padicValRat p c < padicValRat p (q - c) := by
    rw [hcval]
    have : (0 : ℚ) < (padicValRat p (q - c) : ℚ) := by linarith
    exact_mod_cast this
  have heq : c + (q - c) = q := by ring
  have hsum : c + (q - c) ≠ 0 := by rwa [heq]
  have ht := padicValRat.add_eq_of_lt (p := p) hsum hc he hv'
  rw [heq] at ht
  exact ht.trans hcval

theorem primitive_constant_reduction_of_scaled_congruence
    (P : ℤ[X]) (hP : P.IsPrimitive) (F : ℚ[X]) (d s c : ℚ)
    (hd : d ≠ 0) (hs : s ≠ 0)
    (hprop : P.map (Int.castRingHom ℚ) = C d * F)
    (hc : c ≠ 0) (hcval : padicValRat p c = 0)
    (hcong : GV p (C s * F - C c) 1) :
    ∃ cbar : ZMod p, cbar ≠ 0 ∧ P.map (Int.castRingHom (ZMod p)) = C cbar := by
  have hcoeff (k : ℕ) : (P.coeff k : ℚ) = d * F.coeff k := by
    have h := congrArg (fun f : ℚ[X] => f.coeff k) hprop
    simpa only [coeff_map, coeff_C_mul] using! h
  have hzero : VG p (s * F.coeff 0 - c) 1 := by
    simpa only [coeff_sub, coeff_C_mul, coeff_C_zero] using hcong 0
  obtain ⟨hz, hvz⟩ := unit_of_VG_sub hc hcval hzero
  have hF0 : F.coeff 0 ≠ 0 := fun h => hz (by rw [h, mul_zero])
  have hv0 := padicValRat.mul (p := p) hs hF0
  have hvP0 := padicValRat.mul (p := p) hd hF0
  rw [← hcoeff 0, padicValRat.of_int] at hvP0
  apply primitive_constant_reduction_of_strict_min P hP
  intro k hk hPk
  have hFk : F.coeff k ≠ 0 := by
    intro he
    have hh := hcoeff k
    rw [he, mul_zero] at hh
    exact hPk (by exact_mod_cast hh)
  have hvk : VG p (s * F.coeff k) 1 := by
    simpa only [coeff_sub, coeff_C_mul, coeff_C_of_ne_zero hk, sub_zero] using hcong k
  have hb := hvk.resolve_left (mul_ne_zero hs hFk)
  have hvk' := padicValRat.mul (p := p) hs hFk
  have hvPk := padicValRat.mul (p := p) hd hFk
  rw [← hcoeff k, padicValRat.of_int] at hvPk
  have hstrict : (padicValRat p (s * F.coeff 0) : ℚ) < padicValRat p (s * F.coeff k) := by
    rw [hvz]
    norm_num only [Int.cast_zero]
    linarith
  have hstrict' : padicValRat p (s * F.coeff 0) < padicValRat p (s * F.coeff k) := by
    exact_mod_cast hstrict
  rw [hv0, hvk'] at hstrict'
  omega

end Zeta32.Arith.Local

end
