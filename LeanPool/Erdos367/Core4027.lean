/-
Copyright (c) 2026 Scott D. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott D. Hughes
-/

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.GrindInstances
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Aesop

/-! ## Definitions -/

open scoped BigOperators

namespace Core4027

/-- The `r`-full part of `m`: the product of `p ^ v_p(m)` over primes `p` with `v_p(m) ≥ r`. -/
def rFullPart (r m : ℕ) : ℕ :=
  (m.factorization.filter (fun p => r ≤ m.factorization p)).prod (fun p v => p ^ v)

/-- The constant `N = 2^14 * 3^4`. -/
def N : ℕ := 1327104

/-- `C(t) = t^4 + 42 t^2 + 72 t + 333`. -/
def Cpoly (t : ℕ) : ℕ := t^4 + 42*t^2 + 72*t + 333

/-- `G(t)`. -/
def Gpoly (t : ℕ) : ℕ :=
  t^9 + 108*t^7 + 216*t^6 + 4374*t^5 + 13608*t^4 + 99468*t^3 + 215784*t^2 + 998001*t + 1474200

/-- `H(t)`. -/
def Hpoly (t : ℕ) : ℕ :=
  t^15 + 198*t^13 + 432*t^12 + 16875*t^11 + 65448*t^10 + 893700*t^9 + 3965760*t^8
    + 32798439*t^7 + 132802416*t^6 + 770808150*t^5 + 2699107920*t^4 + 10666416717*t^3
    + 28403408808*t^2 + 78874347456*t + 150060252672

/-- `n = (G(t)/N)^3`. -/
def nn (t : ℕ) : ℕ := (Gpoly t / N) ^ 3

/-! ## The `rFullPart` factorization theory -/

theorem rFullPart_ne_zero (r M : ℕ) : rFullPart r M ≠ 0 := by
  unfold rFullPart
  apply Finsupp.prod_ne_zero_iff.mpr
  intro p hp
  have hsupp : p ∈ M.factorization.support := by
    have h := Finsupp.support_filter (p := fun p => r ≤ M.factorization p) (f := M.factorization)
    rw [h] at hp
    exact Finset.mem_of_mem_filter p hp
  have hp2 : p.Prime := Nat.prime_of_mem_primeFactors (by rwa [Nat.support_factorization] at hsupp)
  exact pow_ne_zero _ hp2.pos.ne'

/-- A perfect cube of a positive number is `3`-full: its `rFullPart 3` is itself. -/
theorem rFullPart_cube_eq (a : ℕ) (ha : 1 ≤ a) : rFullPart 3 (a^3) = a^3 := by
  unfold rFullPart
  have hne : a^3 ≠ 0 := by positivity
  have hfilter : (a^3).factorization.filter (fun p => 3 ≤ (a^3).factorization p)
      = (a^3).factorization := by
    apply Finsupp.ext
    intro p
    rw [Finsupp.filter_apply]
    by_cases hp : (a^3).factorization p = 0
    · simp
    · rw [if_pos]
      rw [Nat.factorization_pow] at hp ⊢
      simp only [Finsupp.smul_apply, smul_eq_mul] at hp ⊢
      omega
  rw [hfilter]
  exact Nat.prod_factorization_pow_eq_self hne

/-
The factorization of `rFullPart r M` at a prime `q`.
-/
theorem rFullPart_factorization (r M : ℕ) (q : ℕ) :
    (rFullPart r M).factorization q
      = if r ≤ M.factorization q then M.factorization q else 0 := by
  unfold rFullPart
  rw [Nat.prod_pow_factorization_eq_self]
  · rw [Finsupp.filter_apply]
  · intro p hp
    have hp_support : p ∈ M.factorization.support := Finset.mem_of_mem_filter p hp
    exact Nat.prime_of_mem_primeFactors (by
      rwa [Nat.support_factorization] at hp_support)

/-
If `d ^ 3 ∣ M` (and `M > 0`), then `d ^ 3 ∣ rFullPart 3 M`.
-/
theorem pow_dvd_rFullPart (M d : ℕ) (hM : 0 < M) (hd : d ^ 3 ∣ M) :
    d ^ 3 ∣ rFullPart 3 M := by
  rw [ ← Nat.factorization_le_iff_dvd ] at *;
  · intro q; by_cases hq : Nat.Prime q <;> simp_all +decide ;
    have := hd q; simp_all +decide [ rFullPart_factorization ] ;
    grind;
  · aesop;
  · positivity;
  · aesop;
  · exact rFullPart_ne_zero 3 M

/-! ## The key algebraic identity -/

theorem IDENT (t : ℕ) : Gpoly t ^ 3 + N ^ 3 = Hpoly t * Cpoly t ^ 3 := by
  unfold Gpoly Hpoly Cpoly N
  ring

/-! ## Polynomial congruence transfer -/

theorem Cpoly_modEq {a b M : ℕ} (h : a ≡ b [MOD M]) : Cpoly a ≡ Cpoly b [MOD M] := by
  unfold Cpoly; gcongr

theorem Gpoly_modEq {a b M : ℕ} (h : a ≡ b [MOD M]) : Gpoly a ≡ Gpoly b [MOD M] := by
  unfold Gpoly; gcongr

theorem Hpoly_modEq {a b M : ℕ} (h : a ≡ b [MOD M]) : Hpoly a ≡ Hpoly b [MOD M] := by
  unfold Hpoly; gcongr

/-! ## Concrete constant facts -/

theorem Gpoly_const_modN : Gpoly 23016 ≡ 0 [MOD N] := by
  unfold Gpoly N Nat.ModEq; norm_num

theorem Cpoly_const_mod2 : Cpoly 23016 % 2 = 1 := by
  unfold Cpoly; norm_num

theorem Cpoly_const_mod27 : Cpoly 23016 % 27 = 9 := by
  unfold Cpoly; norm_num

/-! ## Pure polynomial bounds -/

theorem Cpoly_gt (t : ℕ) : t^4 < Cpoly t := by
  exact lt_add_of_le_of_pos
    (Nat.le_add_right _ _ |> Nat.le_trans (Nat.le_add_right _ _))
    (by norm_num [ Cpoly ])

theorem Cpoly_cube_gt (t : ℕ) : t^12 < Cpoly t ^ 3 := by
  convert Nat.pow_lt_pow_left ( Cpoly_gt t ) three_ne_zero using 1; ring

theorem Gpoly_ge_const (t : ℕ) : 1474200 ≤ Gpoly t := by
  exact le_add_of_nonneg_left ( Nat.zero_le _ )

theorem Gpoly_div_pos (t : ℕ) : 1 ≤ Gpoly t / N := by
  exact Nat.div_pos
    (show N ≤ Gpoly t by exact le_trans ( by decide ) ( Gpoly_ge_const t ))
    (by decide)

theorem Gpoly_upper (t : ℕ) (ht : 1676 ≤ t) : Gpoly t ≤ 2 * t^9 := by
  unfold Gpoly
  nlinarith [Nat.pow_le_pow_left ht 2, Nat.pow_le_pow_left ht 3,
    Nat.pow_le_pow_left ht 4, Nat.pow_le_pow_left ht 5, Nat.pow_le_pow_left ht 6,
    Nat.pow_le_pow_left ht 7]

theorem Gpoly_cube_le (t : ℕ) (ht : 1676 ≤ t) : Gpoly t ^ 3 ≤ 8 * t^27 := by
  convert Nat.pow_le_pow_left ( Gpoly_upper t ht ) 3 using 1; ring

/-! ## T1 : `n` is `3`-full -/

theorem T1 (t : ℕ) : rFullPart 3 (nn t) = nn t := by
  unfold nn
  exact rFullPart_cube_eq _ (Gpoly_div_pos t)

/-! ## Main section: the prime-supply hypotheses -/

section
variable (s t₀ t : ℕ)
variable (hs : s.Prime) (hs6 : ¬ s ∣ 6)
variable (ht₀ : 1 ≤ t₀ ∧ t₀ ≤ N * s ^ 3)
variable (hcong : t₀ % N = 23016 % N)
variable (hH : s ^ 3 ∣ Hpoly t₀) (hC : ¬ s ∣ Cpoly t₀)
variable (ht : t = t₀ + N * s ^ 3)

include hcong ht in
theorem t_mod_N : t ≡ 23016 [MOD N] := by
  simp +decide [ *, Nat.ModEq, Nat.add_mod ]

include ht in
theorem t_mod_s3 : t ≡ t₀ [MOD s^3] := by
  norm_num [ ht, Nat.ModEq, Nat.add_mod, Nat.mul_mod ]

include ht in
theorem t_mod_s : t ≡ t₀ [MOD s] := by
  norm_num [ ht, Nat.ModEq, Nat.add_mod, Nat.mul_mod, Nat.pow_mod ]

include hH ht in
theorem hHt : s ^ 3 ∣ Hpoly t := by
  rw [ ← Nat.modEq_zero_iff_dvd ] at *; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ] ;
  simp_all +decide [ Hpoly ]

include hC ht in
theorem hCt : ¬ s ∣ Cpoly t := by
  rw [← ZMod.natCast_eq_zero_iff] at hC ⊢
  rw [ht]
  unfold Cpoly at *; simp_all +decide [ pow_succ, mul_assoc ]

include hcong ht in
theorem L1 : N ∣ Gpoly t := by
  have h_gt_mod : Gpoly t ≡ Gpoly 23016 [MOD N] :=
    Gpoly_modEq (t_mod_N s t₀ t hcong ht)
  exact (Nat.modEq_zero_iff_dvd).mp (h_gt_mod.trans Gpoly_const_modN)

include hcong ht in
theorem L2 : Cpoly t % 2 = 1 := by
  exact Cpoly_modEq (show t ≡ 23016 [MOD 2] by
    exact Nat.ModEq.of_dvd (by decide) (t_mod_N s t₀ t hcong ht))

include hcong ht in
theorem L3mod : Cpoly t % 27 = 9 := by
  rw [ ← Cpoly_const_mod27 ];
  rw [ ← Nat.mod_add_div t 27, ← Nat.mod_add_div 23016 27 ];
  norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Cpoly ]; ring_nf;
  rw [ ht ]; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hcong ];
  rw [ ← Nat.mod_mod_of_dvd t₀ ( by decide : 27 ∣ N ), hcong ]; norm_num [ N ];

include hcong ht in
theorem L3a : 9 ∣ Cpoly t := by
  have := L3mod s t₀ t hcong ht; omega;

include hcong ht in
theorem L3b : ¬ 27 ∣ Cpoly t := by
  rw [ Nat.dvd_iff_mod_eq_zero, L3mod s t₀ t hcong ht ]
  norm_num

include hs hs6 in
theorem hs_ge5 : 5 ≤ s := by
  contrapose! hs6; interval_cases s <;> trivial;

include ht in
theorem Ns3_le_t : N * s^3 ≤ t := by
  linarith

include ht ht₀ in
theorem t_le_2Ns3 : t ≤ 2 * (N * s ^ 3) := by
  linarith

include ht hs hs6 in
theorem t_big : 1676 ≤ t := by
  exact ht.symm ▸
    le_add_of_nonneg_of_le (Nat.zero_le _) (by
      exact le_trans (by decide)
        (Nat.mul_le_mul_left _
          (pow_le_pow_left' (show s ≥ 5 by
            contrapose! hs6
            interval_cases s <;> trivial) 3)))

include hcong ht in
theorem N3_mul_nn : N ^ 3 * nn t = Gpoly t ^ 3 := by
  rw [ nn ];
  rw [ ← mul_pow, Nat.mul_div_cancel' ( L1 s t₀ t hcong ht ) ]

include hcong ht in
theorem T0 : N ^ 3 * (nn t + 1) = Hpoly t * Cpoly t ^ 3 := by
  rw [ ← IDENT t, mul_add, mul_one ];
  rw [ ← N3_mul_nn ];
  exacts [ s, t₀, hcong, ht ]

include hcong ht in
theorem T0_div : nn t + 1 = Hpoly t * Cpoly t ^ 3 / N ^ 3 := by
  exact Eq.symm ( Nat.div_eq_of_eq_mul_left ( by decide ) ( by linarith [ T0 s t₀ t hcong ht ] ) )

include hcong ht in
theorem Ctil_eq : Cpoly t = 9 * (Cpoly t / 9) := by
  rw [ Nat.mul_div_cancel' ( show 9 ∣ Cpoly t from ?_ ) ];
  convert L3a s t₀ t hcong ht using 1

include hcong ht in
theorem Ctil_coprime6 : Nat.Coprime (Cpoly t / 9) 6 := by
  refine Nat.Coprime.symm ?_;
  refine Nat.coprime_of_dvd' ?_;
  intro k hk hk' hk''
  have := Nat.le_of_dvd ( by decide ) hk';
  interval_cases k <;> norm_num at *;
  · have := L2 ( s := s ) ( t₀ := t₀ ) ( t := t ) ( hcong := hcong ) ( ht := ht );
    exact absurd
      (Nat.mod_eq_zero_of_dvd
        (dvd_trans hk'' (Nat.div_dvd_of_dvd (show 9 ∣ Cpoly t from
          L3a (s := s) (t₀ := t₀) (t := t) (hcong := hcong) (ht := ht)))))
      (by omega)
  · exact absurd hk'' (by
      rw [Nat.dvd_div_iff_mul_dvd
        (show 9 ∣ Cpoly t from dvd_trans (by decide) (L3a s t₀ t hcong ht))]
      exact fun h => L3b s t₀ t hcong ht (dvd_trans (by decide) h))
  · exact (by decide : ¬ Nat.Prime 6) hk

include hC ht hs hcong in
theorem Ctil_coprime_s : Nat.Coprime (Cpoly t / 9) s := by
  -- By definition of $Ctil$, we know that $Ctil = Cpoly t / 9$.
  set Ctil := Cpoly t / 9 with hCtil_def
  have hCtil_dvd : Ctil ∣ Cpoly t := by
    exact Nat.div_dvd_of_dvd <| L3a _ _ t hcong ht
  have hCtil_not_dvd : ¬ s ∣ Ctil := by
    have := hCt s t₀ t hC ht; ( contrapose! this; );
    exact dvd_trans this hCtil_dvd
  have hCtil_coprime : Nat.Coprime s Ctil := by
    exact hs.coprime_iff_not_dvd.mpr hCtil_not_dvd
  exact hCtil_coprime.symm

include hs hs6 hcong ht hH hC in
theorem T2_dvd : ((Cpoly t / 9) * s)^3 ∣ nn t + 1 := by
  have h_div : (Cpoly t / 9)^3 ∣ nn t + 1 := by
    have h_div : (Cpoly t / 9)^3 ∣ N ^ 3 * (nn t + 1) := by
      rw [ show N ^ 3 * ( nn t + 1 ) = Hpoly t * Cpoly t ^ 3 from
        T0 s t₀ t hcong ht ];
      exact dvd_mul_of_dvd_right
        (pow_dvd_pow_of_dvd
          (Nat.div_dvd_of_dvd (show 9 ∣ Cpoly t from L3a s t₀ t hcong ht)) _)
        _;
    refine Nat.Coprime.dvd_of_dvd_mul_left ?_ h_div;
    apply_rules [ Nat.Coprime.pow, Nat.Coprime.symm ];
    have h_coprime : Nat.Coprime 6 (Cpoly t / 9) := by
      convert Ctil_coprime6 s t₀ t hcong ht |> Nat.Coprime.symm using 1;
    exact Nat.Coprime.mul_left
      (show Nat.Coprime ( 2 ^ 14 ) ( Cpoly t / 9 ) from
        Nat.Coprime.pow_left _ <| Nat.prime_two.coprime_iff_not_dvd.mpr fun h => by
          have := Nat.dvd_gcd ( by decide : 2 ∣ 6 ) h; simp_all +decide)
      (show Nat.Coprime ( 3 ^ 4 ) ( Cpoly t / 9 ) from
        Nat.Coprime.pow_left _ <| Nat.prime_three.coprime_iff_not_dvd.mpr fun h => by
          have := Nat.dvd_gcd ( by decide : 3 ∣ 6 ) h; simp_all +decide);
  have h_div_s : s ^ 3 ∣ nn t + 1 := by
    have h_div_s : s ^ 3 ∣ N ^ 3 * (nn t + 1) := by
      convert T0 s t₀ t hcong ht ▸ dvd_mul_of_dvd_left ( hHt s t₀ t hH ht ) _ using 1;
    refine Nat.Coprime.dvd_of_dvd_mul_left ?_ h_div_s;
    suffices ¬ s ∣ N by
      simpa +decide only [Nat.ofNat_pos, Nat.coprime_pow_right_iff,
        Nat.coprime_pow_left_iff] using
        hs.coprime_iff_not_dvd.mpr this
    rw [ show N = 2 ^ 14 * 3 ^ 4 by rfl ]
    exact fun h => hs6 <| by
      have := Nat.Prime.dvd_mul hs |>.1 h
      rcases this with (h | h) <;>
        have := Nat.Prime.dvd_of_dvd_pow hs h <;>
        (have := Nat.le_of_dvd ( by decide ) this; interval_cases s <;> trivial)
  convert Nat.Coprime.mul_dvd_of_dvd_of_dvd _ h_div h_div_s using 1;
  · ring;
  · apply_mod_cast Nat.Coprime.pow;
    exact Ctil_coprime_s (s := s) (t₀ := t₀) (t := t) (hs := hs)
      (hcong := hcong) (hC := hC) (ht := ht)

include hs hs6 hcong ht hH hC in
theorem T2 : ((Cpoly t / 9) * s)^3 ∣ rFullPart 3 (nn t + 1) := by
  apply pow_dvd_rFullPart;
  · positivity;
  · apply_rules [ T2_dvd ]

include hs hs6 hcong ht hH hC in
theorem B1_ge : ((Cpoly t / 9) * s)^3 ≤ rFullPart 3 (nn t + 1) := by
  refine Nat.le_of_dvd ?_ ?_;
  · exact Nat.pos_of_ne_zero ( rFullPart_ne_zero _ _ );
  · apply_rules [ T2 ]

include hs hs6 ht₀ hcong ht hH hC in
theorem T3 :
    8^13 * (1458 * N * (rFullPart 3 (nn t) * rFullPart 3 (nn t + 1)))^27
      > N^39 * (nn t)^40 := by
  -- From Fact (C), we have $P > n t^{13}$.
  have hP_gt : 1458 * N * ((nn t) * rFullPart 3 (nn t + 1)) > (nn t) * t^13 := by
    -- From Fact (C), we have $P > n t^{13}$. This follows from the bounds on $C'^3$ and $s^3$.
    have hP_gt : 729 * (Cpoly t / 9)^3 * (2 * N * s^3) ≥ t^13 + 1 := by
      have hP_gt : 729 * (Cpoly t / 9)^3 ≥ t^12 + 1 := by
        have hP_gt : 729 * (Cpoly t / 9)^3 = Cpoly t^3 := by
          rw [ ← Nat.mul_div_cancel' ( show 9 ∣ Cpoly t from L3a s t₀ t hcong ht ) ]; ring_nf;
          norm_num;
        exact hP_gt.symm ▸ Nat.succ_le_of_lt ( Cpoly_cube_gt t );
      nlinarith [ pow_pos
        (show 0 < t by
          linarith [show 0 < N * s ^ 3 by
            exact mul_pos ( by decide ) ( pow_pos hs.pos _ )])
        12 ];
    -- By Fact (B1_ge), we have $(Cpoly t / 9)^3 * s^3 \leq rFullPart 3 (nn t + 1)$.
    have h_B1_ge : (Cpoly t / 9)^3 * s^3 ≤ rFullPart 3 (nn t + 1) := by
      have h_B1_ge : (Cpoly t / 9 * s)^3 ≤ rFullPart 3 (nn t + 1) := by
        apply_rules [ B1_ge ];
      simpa only [ mul_pow ] using h_B1_ge;
    -- By combining the results from hP_gt and h_B1_ge, we get the desired inequality.
    have h_combined :
        1458 * N * (nn t * rFullPart 3 (nn t + 1)) ≥
          729 * (Cpoly t / 9)^3 * (2 * N * s^3) * nn t := by
      nlinarith [ show 0 ≤ N * nn t by positivity ];
    nlinarith [ show 0 < nn t from pow_pos ( Gpoly_div_pos t ) 3 ];
  -- From Fact (D), we have $N^3 n \leq 8 t^{27}$.
  have hN3n_le : N^3 * (nn t) ≤ 8 * t^27 := by
    -- By definition of $nn$, we know that $N^3 * nn t = Gpoly t ^ 3$.
    have hN3n_eq : N^3 * (nn t) = Gpoly t ^ 3 := by
      exact N3_mul_nn s t₀ t hcong ht
    exact hN3n_eq.symm ▸ Gpoly_cube_le t ( t_big s t₀ t hs hs6 ht );
  -- From Fact (C), we have $8^{13} P^{27} > 8^{13} (n t^{13})^{27}$.
  have h8P27_gt :
      8 ^ 13 * (1458 * N * ((nn t) * rFullPart 3 (nn t + 1))) ^ 27 >
        8 ^ 13 * ((nn t) * t ^ 13) ^ 27 := by
    gcongr;
  -- From Fact (D), we have $8^{13} (n t^{13})^{27} \geq n^{27} (N^3 n)^{13}$.
  have h8P27_ge : 8 ^ 13 * ((nn t) * t ^ 13) ^ 27 ≥ (nn t) ^ 27 * (N ^ 3 * (nn t)) ^ 13 := by
    have h8P27_ge : 8 ^ 13 * ((nn t) * t ^ 13) ^ 27 ≥ (nn t) ^ 27 * (8 * t ^ 27) ^ 13 := by
      ring_nf; norm_num;
    exact le_trans ( Nat.mul_le_mul_left _ ( Nat.pow_le_pow_left hN3n_le _ ) ) h8P27_ge;
  rw [ show rFullPart 3 ( nn t ) = nn t from T1 t ]; ring_nf at *; linarith;

end

end Core4027
