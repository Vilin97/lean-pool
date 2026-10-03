/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang, Moritz Firsching
-/
module
public import LeanPool.Zeta32.PrimeEdge.Reduction
public import LeanPool.Zeta32.Criterion

/-! Adapted from the Li₂ light-certificate project and mo271/Zeta5; see NOTICE. -/

public section
open Polynomial
namespace Zeta32

lemma pow_mul_aeval_div_eq_cast {K : Type*} [Field K]
    (P : ℤ[X]) {d : ℕ} (hd : P.natDegree ≤ d) (a b : ℤ)
    (hb : (b : K) ≠ 0) :
    (b : K)^d * aeval ((a : K) / b) P =
      ((∑ k ∈ Finset.range (d+1), P.coeff k * a^k * b^(d-k) : ℤ) : K) := by
  have hlt : (P.map (algebraMap ℤ K)).natDegree < d+1 :=
    lt_of_le_of_lt natDegree_map_le (by omega)
  rw [aeval_def, eval₂_eq_eval_map, eval_eq_sum_range' hlt, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  have hpow : (b : K)^d = (b : K)^(d-k) * (b : K)^k := by
    rw [← pow_add]
    congr 1
    omega
  rw [coeff_map, hpow, div_pow]
  simp only [algebraMap_int_eq, eq_intCast]
  field_simp

theorem rational_nonzero_of_constant_reduction (P : ℤ[X]) (p : ℕ) [Fact p.Prime]
    (c : ZMod p) (hc : c ≠ 0)
    (hred : P.map (Int.castRingHom (ZMod p)) = C c)
    (q : ℚ) (hb : (q.den : ZMod p) ≠ 0) :
    aeval (q : ℝ) P ≠ 0 := by
  intro hz
  let d := P.natDegree
  let m : ℤ := ∑ k ∈ Finset.range (d+1), P.coeff k * q.num^k * (q.den : ℤ)^(d-k)
  have hmR := pow_mul_aeval_div_eq_intCast P (d := d) le_rfl q.num (q.den : ℤ)
    (by exact_mod_cast q.den_pos.ne')
  have heval : aeval ((q.num : ℝ) / (q.den : ℤ)) P = 0 := by
    simpa [Rat.cast_def, Int.cast_natCast] using hz
  have hm0 : m = 0 := by
    rw [heval, mul_zero] at hmR
    have : (m : ℝ) = 0 := hmR.symm
    exact_mod_cast this
  have hmZ := pow_mul_aeval_div_eq_cast (K := ZMod p) P (d := d) le_rfl
    q.num (q.den : ℤ) (by simpa using hb)
  have hz_eval : aeval ((q.num : ZMod p)/((q.den : ℤ) : ZMod p)) P = c := by
    rw [aeval_def, eval₂_eq_eval_map]
    change (P.map (Int.castRingHom (ZMod p))).eval _ = c
    rw [hred, eval_C]
  have hprod : (q.den : ZMod p)^d * c = 0 := by
    change ((q.den : ℤ) : ZMod p)^d *
      aeval ((q.num : ZMod p)/((q.den : ℤ) : ZMod p)) P = (m : ZMod p) at hmZ
    rw [hz_eval, hm0, Int.cast_zero, Int.cast_natCast] at hmZ
    exact hmZ
  exact mul_ne_zero (pow_ne_zero _ hb) hc hprod

end Zeta32
end
