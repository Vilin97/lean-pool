/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.PrimeEdge.Disc.Bernoulli
public import LeanPool.Zeta32.Arith.Local.PoleFun

/-! the proof notes, §2, Lemma 3 (local integrality) for the finite local functional
`locValue` of `Local.lean`: linearity in the numerator, the valuation of `locValue s (u^e) M` for
`M ⊆ {0,…,4}` (`≥ -1` always, `≥ 0` if `e ≤ |M| + 2p - 2`), the `s`-dependence
(`≥ 1` if `e ≤ |M| + p - 2`), and removal of a near pole at `0` against a factor `u`. -/

public section

open Polynomial
open scoped BigOperators
namespace Zeta32.PrimeEdge

open Zeta32.Arith.Local

variable {p : ℕ}

lemma nearPoly_monic (M : Finset ℕ) : (∏ m ∈ M, (X + C (m : ℚ))).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

lemma natDegree_nearPoly (M : Finset ℕ) : (∏ m ∈ M, (X + C (m : ℚ))).natDegree = M.card := by
  have h : ∀ i ∈ M, (X + C (i : ℚ)).natDegree = 1 := fun i _ => natDegree_X_add_C _
  rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_add_C _, Finset.sum_congr rfl h]
  simp

/-! ### Linearity -/

lemma locPoly_add (s : ℚ) (P Q : ℚ[X]) : locPoly s (P + Q) = locPoly s P + locPoly s Q := by
  exact locPoly_add_linear s P Q

lemma locPoly_smul (s c : ℚ) (P : ℚ[X]) : locPoly s (c • P) = c * locPoly s P := by
  simpa only [smul_eq_C_mul] using locPoly_C_mul_linear s c P

lemma locValue_add (s : ℚ) (S S' : ℚ[X]) (M : Finset ℕ) :
    locValue s (S + S') M = locValue s S M + locValue s S' M := by
  exact locValue_add_linear s S S' M

lemma locValue_smul (s c : ℚ) (S : ℚ[X]) (M : Finset ℕ) :
    locValue s (c • S) M = c * locValue s S M := by
  simpa only [smul_eq_C_mul] using locValue_C_mul_linear s c S M

lemma locValue_C_mul (s c : ℚ) (S : ℚ[X]) (M : Finset ℕ) :
    locValue s (C c * S) M = c * locValue s S M := by
  rw [← smul_eq_C_mul, locValue_smul]

lemma locValue_zero_left (s : ℚ) (M : Finset ℕ) : locValue s 0 M = 0 := by
  exact locValue_zero_linear s M

lemma locValue_sum (s : ℚ) (M : Finset ℕ) {ι : Type*} (t : Finset ι) (f : ι → ℚ[X]) :
    locValue s (∑ i ∈ t, f i) M = ∑ i ∈ t, locValue s (f i) M := by
  exact locValue_sum_linear s t f M

/-- `locValue` is the coefficientwise combination of its values on monomials. -/
lemma locValue_eq_sum (s : ℚ) (S : ℚ[X]) (M : Finset ℕ) {N : ℕ} (hN : S.natDegree < N) :
    locValue s S M = ∑ e ∈ Finset.range N, S.coeff e * locValue s (X ^ e) M := by
  conv_lhs => rw [S.as_sum_range_C_mul_X_pow' hN]
  rw [locValue_sum]
  exact Finset.sum_congr rfl fun e _ => locValue_C_mul _ _ _ _

/-! ### Integrality of the pieces -/

/-- `u^e /ₘ ∏ (u + m)` has integer coefficients. -/
lemma GV_X_pow_divByMonic (M : Finset ℕ) (e : ℕ) :
    GV p ((X : ℚ[X]) ^ e /ₘ ∏ m ∈ M, (X + C (m : ℚ))) 0 := by
  have hTZ : (∏ m ∈ M, (X + C (m : ℤ)) : ℤ[X]).Monic :=
    monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _
  have hmap : (∏ m ∈ M, (X + C (m : ℤ)) : ℤ[X]).map (Int.castRingHom ℚ) =
      ∏ m ∈ M, (X + C (m : ℚ)) := by
    rw [Polynomial.map_prod]; simp
  have hX : ((X : ℤ[X]) ^ e).map (Int.castRingHom ℚ) = X ^ e := by simp
  intro n
  rw [← hmap, ← hX, ← map_divByMonic _ hTZ, coeff_map, eq_intCast]
  exact VG.intCast _

lemma padicValRat_diff_eq_zero [Fact p.Prime] (hp : 5 ≤ p) {m m' : ℕ} (hm : m < 5) (hm' : m' < 5)
    (hne : m' ≠ m) : ((m' : ℚ) - m) ≠ 0 ∧ padicValRat p ((m' : ℚ) - m) = 0 := by
  have hcast : ((m' : ℚ) - m) = (((m' : ℤ) - m : ℤ) : ℚ) := by push_cast; ring
  refine ⟨by rw [hcast]; exact_mod_cast (by omega : (m' : ℤ) - m ≠ 0), ?_⟩
  rw [hcast]
  apply padicValRat_int_eq_zero
  intro hd
  have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
  omega

lemma prod_diff_unit [Fact p.Prime] (hp : 5 ≤ p) {M : Finset ℕ} (hM : M ⊆ Finset.range 5)
    {m : ℕ} (hm : m ∈ M) :
    (∏ m' ∈ M.erase m, ((m' : ℚ) - m)) ≠ 0 ∧
      padicValRat p (∏ m' ∈ M.erase m, ((m' : ℚ) - m)) = 0 := by
  have hm5 : m < 5 := Finset.mem_range.mp (hM hm)
  have hf : ∀ m' ∈ M.erase m, ((m' : ℚ) - m) ≠ 0 ∧ padicValRat p ((m' : ℚ) - m) = 0 :=
    fun m' hm' => padicValRat_diff_eq_zero hp hm5
      (Finset.mem_range.mp (hM (Finset.mem_of_mem_erase hm'))) (Finset.ne_of_mem_erase hm')
  refine ⟨Finset.prod_ne_zero_iff.mpr fun m' hm' => (hf m' hm').1, ?_⟩
  rw [padicValRat_finset_prod _ _ fun m' hm' => (hf m' hm').1]
  exact Finset.sum_eq_zero fun m' hm' => (hf m' hm').2

lemma VG_H_small [hp : Fact p.Prime] {m : ℕ} (hm : m < p) (e : ℕ) : VG p (Zeta32.H e m) 0 := by
  unfold Zeta32.H
  refine VG.sum _ fun a ha => ?_
  rw [Finset.mem_Icc] at ha
  have hv : padicValRat p ((a : ℚ) ^ e) = 0 := by
    rw [padicValRat.pow, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))]
    simp
  have := VG.inv (p := p) (q := (a : ℚ) ^ e)
    (r := 0) (by rw [hv]; simp)
  simpa [one_div] using this

lemma VG_locPole [Fact p.Prime] {s : ℚ} (hs : VG p s 1) {m : ℕ} (hm : m < p) :
    VG p (locPole s m) 0 := by
  unfold locPole
  refine (VG_two_mul (VG_H_small hm 3)).sub ?_
  have := (VG_two_mul hs).mul (VG_H_small hm 2)
  exact this.mono (by norm_num)

lemma VG_locPole_sub [Fact p.Prime] {s : ℚ} (hs : VG p s 1) {m : ℕ} (hm : m < p) :
    VG p (locPole s m - locPole 0 m) 1 := by
  have heq : locPole s m - locPole 0 m = -(2 * s * Zeta32.H 2 m) := by unfold locPole; ring
  rw [heq]
  have := (VG_two_mul hs).mul (VG_H_small hm 2)
  exact (by simpa using this : VG p (2 * s * Zeta32.H 2 m) 1).neg

/-- The residue coefficient `(-m)^e / ∏_{m' ≠ m} (m' - m)` is integral. -/
lemma VG_res_X_pow [Fact p.Prime] (hp : 5 ≤ p) {M : Finset ℕ} (hM : M ⊆ Finset.range 5)
    {m : ℕ} (hm : m ∈ M) (e : ℕ) :
    VG p (((X : ℚ[X]) ^ e).eval (-(m : ℚ)) / ∏ m' ∈ M.erase m, ((m' : ℚ) - m)) 0 := by
  obtain ⟨hne, hv⟩ := prod_diff_unit hp hM hm
  rw [div_eq_mul_inv, eval_pow, eval_X]
  have h1 : VG p ((-(m : ℚ)) ^ e) 0 := by
    have := ((VG.natCast (p := p) m).neg).pow e
    simpa using this
  have h2 : VG p (∏ m' ∈ M.erase m, ((m' : ℚ) - m))⁻¹ 0 := by
    have := VG.inv (p := p)  (r := 0) (by rw [hv]; simp)
    simpa using this
  simpa using h1.mul h2

lemma VG_locPoly_of {s : ℚ} [Fact p.Prime] {q : ℚ[X]} (hq : GV p q 0) {r : ℚ}
    (hb : ∀ j ∈ q.support, VG p (locMoment s j) r) : VG p (locPoly s q) r := by
  unfold locPoly Polynomial.sum
  exact VG.sum _ fun j hj => by simpa using (hq j).mul (hb j hj)

lemma natDegree_X_pow_divByMonic (M : Finset ℕ) (e : ℕ) :
    ((X : ℚ[X]) ^ e /ₘ ∏ m ∈ M, (X + C (m : ℚ))).natDegree = e - M.card := by
  rw [natDegree_divByMonic _ (nearPoly_monic M), natDegree_nearPoly, natDegree_X_pow]

lemma VG_locValue_res [Fact p.Prime] (hp : 5 ≤ p) {s : ℚ} (hs : VG p s 1) {M : Finset ℕ}
    (hM : M ⊆ Finset.range 5) (e : ℕ) :
    VG p (∑ m ∈ M, ((X : ℚ[X]) ^ e).eval (-(m : ℚ)) / (∏ m' ∈ M.erase m, ((m' : ℚ) - m)) *
      locPole s m) 0 := by
  refine VG.sum _ fun m hm => ?_
  have hmp : m < p := by have := Finset.mem_range.mp (hM hm); omega
  simpa using (VG_res_X_pow hp hM hm e).mul (VG_locPole hs hmp)

/-- **Lemma 3, monomial form, weak part**: `v_p(V(u^e / ∏ (u + m))) ≥ -1`. -/
theorem VG_locValue_X_pow [Fact p.Prime] (hp : 5 ≤ p) {s : ℚ} (hs : VG p s 1) {M : Finset ℕ}
    (hM : M ⊆ Finset.range 5) (e : ℕ) : VG p (locValue s (X ^ e) M) (-1) := by
  unfold locValue
  refine VG.add ?_ ((VG_locValue_res hp hs hM e).mono (by norm_num))
  exact VG_locPoly_of (GV_X_pow_divByMonic M e) fun j _ => VG_locMoment (by omega) hs j

/-- **Lemma 3, monomial form**: `V(u^e / ∏ (u + m))` is integral for `e ≤ |M| + 2p - 2`. -/
theorem VG_locValue_X_pow_zero [Fact p.Prime] (hp : 5 ≤ p) {s : ℚ} (hs : VG p s 1)
    {M : Finset ℕ} (hM : M ⊆ Finset.range 5) {e : ℕ} (he : e + 2 ≤ M.card + 2 * p) :
    VG p (locValue s (X ^ e) M) 0 := by
  unfold locValue
  refine VG.add ?_ (VG_locValue_res hp hs hM e)
  refine VG_locPoly_of (GV_X_pow_divByMonic M e) fun j hj => VG_locMoment_zero (by omega) hs ?_
  have h1 := le_natDegree_of_mem_supp j hj
  rw [natDegree_X_pow_divByMonic] at h1
  omega

/-- The `s`-dependence of `V(u^e / ∏ (u + m))` is `≡ 0 mod p` for `e ≤ |M| + p - 2`. -/
theorem VG_locValue_X_pow_sub [Fact p.Prime] (hp : 5 ≤ p) {s : ℚ} (hs : VG p s 1)
    {M : Finset ℕ} (hM : M ⊆ Finset.range 5) {e : ℕ} (he : e + 2 ≤ M.card + p) :
    VG p (locValue s (X ^ e) M - locValue 0 (X ^ e) M) 1 := by
  unfold locValue
  have hpoly : ∀ q : ℚ[X], locPoly s q - locPoly 0 q =
      ∑ j ∈ q.support, q.coeff j * (locMoment s j - locMoment 0 j) := fun q => by
    unfold locPoly Polynomial.sum
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hsplit : ∀ (a b c d : ℚ), (a + b) - (c + d) = (a - c) + (b - d) := fun _ _ _ _ => by ring
  rw [hsplit, hpoly, ← Finset.sum_sub_distrib]
  refine VG.add (VG.sum _ fun j hj => ?_) (VG.sum _ fun m hm => ?_)
  · have h1 := le_natDegree_of_mem_supp j hj
    rw [natDegree_X_pow_divByMonic] at h1
    have := (GV_X_pow_divByMonic (p := p) M e j).mul (VG_locMoment_sub (by omega) hs
      (e := j) (by omega))
    simpa using this
  · have hmp : m < p := by have := Finset.mem_range.mp (hM hm); omega
    rw [← mul_sub]
    simpa using (VG_res_X_pow hp hM hm e).mul (VG_locPole_sub hs hmp)

/-! ### A near pole at `0` against a factor `u` -/

lemma X_mul_divByMonic_X_mul {S T : ℚ[X]} (hT : T.Monic) : (X * S) /ₘ (X * T) = S /ₘ T := by
  have hXT : (X * T).Monic := monic_X.mul hT
  refine (div_modByMonic_unique (S /ₘ T) (X * (S %ₘ T)) hXT ⟨?_, ?_⟩).1
  · have := modByMonic_add_div S T
    calc X * (S %ₘ T) + X * T * (S /ₘ T) = X * (S %ₘ T + T * (S /ₘ T)) := by ring
      _ = X * S := by rw [this]
  · by_cases hr : S %ₘ T = 0
    · rw [hr, mul_zero, degree_zero, bot_lt_iff_ne_bot, Ne, degree_eq_bot]
      exact hXT.ne_zero
    · have hlt' : (S %ₘ T).natDegree < T.natDegree :=
        natDegree_lt_natDegree hr (degree_modByMonic_lt S hT)
      apply degree_lt_degree
      rw [natDegree_X_mul hr, Monic.natDegree_mul monic_X hT, natDegree_X]
      omega

theorem locValue_X_mul_insert_zero (s : ℚ) (S : ℚ[X]) {M : Finset ℕ} (h0 : 0 ∉ M) :
    locValue s (X * S) (insert 0 M) = locValue s S M := by
  unfold locValue
  have hT : ∏ m ∈ insert 0 M, (X + C (m : ℚ)) = X * ∏ m ∈ M, (X + C (m : ℚ)) := by
    rw [Finset.prod_insert h0]; simp
  rw [hT, X_mul_divByMonic_X_mul (nearPoly_monic M), Finset.sum_insert h0]
  simp only [eval_mul, eval_X, Nat.cast_zero, neg_zero, zero_mul, zero_div]
  rw [zero_add]
  congr 1
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : m ≠ 0 := fun h => h0 (h ▸ hm)
  have hmq : (-(m : ℚ)) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast hm0)
  rw [Finset.erase_insert_of_ne (Ne.symm hm0), Finset.prod_insert (fun h => h0
    (Finset.mem_of_mem_erase h))]
  rw [show ((0 : ℕ) : ℚ) - m = -(m : ℚ) by simp, mul_div_mul_left _ _ hmq]

end Zeta32.PrimeEdge

end
