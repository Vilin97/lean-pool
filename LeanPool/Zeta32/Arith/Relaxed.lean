/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Arith.Profiles
public import LeanPool.Zeta32.Arith.Relaxed.Basic
public import LeanPool.Zeta32.Arith.Relaxed.Columns

/-! the proof notes, §8.1, Lemma 8 (relaxed greedy): for a prime `p ≥ 7` with
`5n < p²` and `3p ≤ 7n`, if some allocation of the `3n` picks bounds every nonzero coefficient of
`Q r n` (`GreedyBound`, i.e. the proof notes, Lemma 4), then `cost ≤ n ψ(p/n) + 3/4`.
Steps: (i) `Relaxed.Basic.allocation_relaxation`; (ii) `Relaxed.Columns.sum_colVal(_sq)` and
`Relaxed.Basic.padicValRat_scale_one_level`; (iii)–(iv) the identity (8.1)+(8.2) in the combined
form `−norm_p − relax = n ψ(x) + E_p`, `E_p = (p − 12n − 8r₀ + 2s₀ − 1)/(4p)`; (v) `E_p < 3/4`. -/

public section
namespace Zeta32.Arith.Relaxed
open Zeta32

/-- Floor sum `Σ_{i<K} ⌊i/p⌋ = K q − p q (q+1)/2` for `K = q p + r`, `r < p`.
-- adapted from
-- dtq1997/li2-half-irrationality@d5d8206:Li2Unified/Modular/Base/MediumFloorSum.lean -/
lemma sum_range_div_block_real {p : ℕ} (hp : 0 < p) (q : ℕ) :
    (∑ i ∈ Finset.range (q*p), ((i/p : ℕ) : ℝ)) =
      (p : ℝ) * q * ((q : ℝ) - 1) / 2 := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      have hs : (∑ i ∈ Finset.range p, (((q*p+i)/p : ℕ) : ℝ)) = (p : ℝ) * q := by
        calc
          (∑ i ∈ Finset.range p, (((q*p+i)/p : ℕ) : ℝ)) =
              ∑ _i ∈ Finset.range p, (q : ℝ) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [show q*p+i = i+p*q by ring, Nat.add_mul_div_left _ _ hp,
              Nat.div_eq_of_lt (Finset.mem_range.mp hi), zero_add]
          _ = (p : ℝ) * q := by simp
      rw [hs]
      push_cast
      ring

lemma sum_range_div_real {p K q r : ℕ} (hp : 0 < p) (hr : r < p) (hK : K = q * p + r) :
    (∑ i ∈ Finset.range K, ((i/p : ℕ) : ℝ)) =
      (K : ℝ) * q - (p : ℝ) * q * ((q : ℝ)+1) / 2 := by
  rw [hK, Finset.sum_range_add, sum_range_div_block_real hp q]
  have hs : (∑ i ∈ Finset.range r, (((q*p+i)/p : ℕ) : ℝ)) = (r : ℝ) * q := by
    calc
      (∑ i ∈ Finset.range r, (((q*p+i)/p : ℕ) : ℝ)) =
          ∑ _i ∈ Finset.range r, (q : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hip : i < p := lt_trans (Finset.mem_range.mp hi) hr
        rw [show q*p+i = i+p*q by ring, Nat.add_mul_div_left _ _ hp,
          Nat.div_eq_of_lt hip, zero_add]
      _ = (r : ℝ) * q := by simp
  rw [hs]
  push_cast
  ring

/-- `v_p(scale n)` as a real number, one Legendre level. -/
lemma scale_val_real {p n : ℕ} (hp : p.Prime) (hsq : 5 * n < p ^ 2) :
    (((padicValRat p (scale n) : ℤ) : ℝ)) =
      (3*n : ℝ) * (((5*n)/p : ℕ) : ℝ) - (12*n : ℝ) * ((n/p : ℕ) : ℝ) -
        2 * ∑ i ∈ Finset.range (3*n), ((i/p : ℕ) : ℝ) := by
  rw [padicValRat_scale_one_level hp hsq]
  push_cast
  rfl

/-- `ψ(p/n)` through the residues `n mod p`, `5n mod p`, `3n mod p`. -/
lemma psiL_eq (n p : ℕ) (hp : 0 < p) :
    ArithSum.psiL ((p:ℝ)/(n:ℝ)) =
      let a : ℝ := ((n % p : ℕ) : ℝ) / p
      let b : ℝ := (((5*n) % p : ℕ) : ℝ) / p
      let g : ℝ := (((3*n) % p : ℕ) : ℝ) / p
      let m : ℝ := ((min (n % p) ((5*n) % p) : ℕ) : ℝ) / p
      6 + ((p:ℝ)/n)*g*(1-g) - 3*(4*a-b) + ((p:ℝ)/n)/4*(16*a + b - 8*m - (4*a-b)^2) := by
  have hpR : (0:ℝ) < p := by exact_mod_cast hp
  have h1 : Int.fract (1 / ((p:ℝ)/(n:ℝ))) = ((n % p : ℕ) : ℝ) / p := by
    rw [one_div_div]
    exact Int.fract_div_natCast_eq_div_natCast_mod
  have h5 : Int.fract (5 / ((p:ℝ)/(n:ℝ))) = (((5*n) % p : ℕ) : ℝ) / p := by
    rw [div_div_eq_mul_div, show (5:ℝ) * n = ((5*n : ℕ) : ℝ) by push_cast; ring]
    exact Int.fract_div_natCast_eq_div_natCast_mod
  have h3 : Int.fract (3 / ((p:ℝ)/(n:ℝ))) = (((3*n) % p : ℕ) : ℝ) / p := by
    rw [div_div_eq_mul_div, show (3:ℝ) * n = ((3*n : ℕ) : ℝ) by push_cast; ring]
    exact Int.fract_div_natCast_eq_div_natCast_mod
  have hm : min (((n % p : ℕ) : ℝ) / p) ((((5*n) % p : ℕ) : ℝ) / p) =
      ((min (n % p) ((5*n) % p) : ℕ) : ℝ) / p := by
    rw [min_div_div_right hpR.le, Nat.cast_min]
  unfold ArithSum.psiL
  simp only [h1, h5, h3, hm]

/-- The algebraic core of the proof notes, §8.1 (iii)–(v), over free real symbols with the relations
`n = pA + r₀`, `5n = pL + s₀`, `3n = pM + t₀`: identities (8.1), (8.2) and `E_p < 3/4`. -/
lemma relaxed_algebra (n p A L M r₀ s₀ t₀ μ cst alloc v : ℝ) (hp : 0 < p) (hn : 0 < n)
    (eA : n = p * A + r₀) (eL : 5 * n = p * L + s₀) (eM : 3 * n = p * M + t₀)
    (hs : s₀ < p) (hr : 0 ≤ r₀) (hcost : cst ≤ -(v + alloc))
    (hv : v = 3 * n * L - 12 * n * A - 2 * (3 * n * M - p * M * (M + 1) / 2))
    (hrelax : (3 * n) ^ 2 / p + 3 * n * ((p * (4 * A - L - 2) + 4 * r₀ - s₀ + 1) / p - 1) +
        (p * (4 * A - L - 2) + 4 * r₀ - s₀ + 1) ^ 2 / (4 * p) -
        (p * (4 * A - L - 2) ^ 2 + 2 * (4 * A - L - 2) * (4 * r₀ - s₀ + 1) +
          1 + 16 * r₀ + s₀ - 8 * μ) / 4 ≤ alloc) :
    cst ≤ n * (6 + (p/n)*(t₀/p)*(1-t₀/p) - 3*(4*(r₀/p)-s₀/p) +
          (p/n)/4*(16*(r₀/p) + s₀/p - 8*(μ/p) - (4*(r₀/p)-s₀/p)^2)) + 3/4 := by
  have hAe : A = (n - r₀) / p := by field_simp; linarith
  have hLe : L = (5 * n - s₀) / p := by field_simp; linarith
  have hMe : M = (3 * n - t₀) / p := by field_simp; linarith
  have key : -v - ((3 * n) ^ 2 / p + 3 * n * ((p * (4 * A - L - 2) + 4 * r₀ - s₀ + 1) / p - 1) +
        (p * (4 * A - L - 2) + 4 * r₀ - s₀ + 1) ^ 2 / (4 * p) -
        (p * (4 * A - L - 2) ^ 2 + 2 * (4 * A - L - 2) * (4 * r₀ - s₀ + 1) +
          1 + 16 * r₀ + s₀ - 8 * μ) / 4) =
      n * (6 + (p/n)*(t₀/p)*(1-t₀/p) - 3*(4*(r₀/p)-s₀/p) +
          (p/n)/4*(16*(r₀/p) + s₀/p - 8*(μ/p) - (4*(r₀/p)-s₀/p)^2)) +
        (p - 12 * n - 8 * r₀ + 2 * s₀ - 1) / (4 * p) := by
    rw [hv, hAe, hLe, hMe]
    field_simp
    ring
  have hE : (p - 12 * n - 8 * r₀ + 2 * s₀ - 1) / (4 * p) ≤ 3/4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- the proof notes, §8.1, Lemma 8 (per prime, relaxed greedy). -/
theorem relaxed_per_prime (r : ℚ) (n p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) (hsq : 5 * n < p ^ 2)
    (hQ : Q r n ≠ 0) (h73 : 3 * p ≤ 7 * n) (hG : GreedyBound r n p) :
    cost r n p ≤ n * ArithSum.psiL ((p:ℝ)/(n:ℝ)) + 3/4 := by
  have hp0 : 0 < p := hp.pos
  have hn0 : 0 < n := by omega
  have hpR : (0:ℝ) < p := by exact_mod_cast hp0
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  -- the allocation provided by `GreedyBound` (the proof notes, Lemma 4)
  have hcost := cost_le_of_scaled_greedy r n p hp hQ hG
  have hk : (∑ b ∈ Finset.range p, (Classical.choose hG) b) = 3*n :=
    (Classical.choose_spec hG).1
  -- (i) relaxation, (ii) column sums
  have hrelax := allocation_relaxation p (3*n) hp0 (colVal n p) (Classical.choose hG) hk
  rw [← allocCost_real, sum_colVal n p (n/p) ((5*n)/p) (n%p) ((5*n)%p) hp0 rfl rfl rfl rfl,
    sum_colVal_sq n p (n/p) ((5*n)/p) (n%p) ((5*n)%p) hp0 rfl rfl rfl rfl] at hrelax
  -- normalization, one Legendre level
  have hval := scale_val_real (n := n) hp hsq
  rw [sum_range_div_real (q := (3*n)/p) (r := (3*n)%p) hp0 (Nat.mod_lt _ hp0)
    (by rw [mul_comm ((3*n) / p) p]; exact (Nat.div_add_mod (3*n) p).symm)] at hval
  have eA : (n : ℝ) = (p : ℝ) * ((n/p : ℕ) : ℝ) + ((n%p : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod n p).symm
  have eL : 5 * (n : ℝ) = (p : ℝ) * (((5*n)/p : ℕ) : ℝ) + (((5*n)%p : ℕ) : ℝ) := by
    have := (Nat.div_add_mod (5*n) p).symm
    exact_mod_cast this
  have eM : 3 * (n : ℝ) = (p : ℝ) * (((3*n)/p : ℕ) : ℝ) + (((3*n)%p : ℕ) : ℝ) := by
    have := (Nat.div_add_mod (3*n) p).symm
    exact_mod_cast this
  have hs : ((((5*n)%p : ℕ)) : ℝ) < p := by exact_mod_cast Nat.mod_lt _ hp0
  have hr : (0:ℝ) ≤ ((n%p : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [psiL_eq n p hp0]
  have hc3 : (((3*n : ℕ)) : ℝ) = 3 * (n : ℝ) := by push_cast; ring
  rw [hc3] at hrelax hval
  exact relaxed_algebra (n : ℝ) p _ _ _ _ _ _ _ _ _ _ hpR hnR eA eL eM hs hr hcost hval hrelax

end Zeta32.Arith.Relaxed
end
