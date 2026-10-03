/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Arith.OuterEntryMain
public import LeanPool.Zeta5Irrational.Arith.InnerAlloc
import LeanPool.Zeta5Irrational.Arith.SmallPrimeF
import LeanPool.Zeta5Irrational.Arith.SmallPrimeTau
public import LeanPool.Zeta5Irrational.Legendre
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

/-! # The normalisation actually used

For every prime `p ≤ 2h` the local exponent `Lp n p` is one of the proved lower bounds for
`v_p^G(F_K)`:

* small primes `p M ≤ K`: the bound (3.12), `small_prime_bound`;
* inner range `K < pM`, `3p ≤ K`: `v_p(S_K) + ⌊2 ∑ wcap⌋` for the water-filling allocation
  (`inner_bound_cap`), when its side conditions hold;
* outer range `K < 3p`: `v_p(S_K) + ⌊2 ∑ w - r⌋` (`outer_bound`), when its side conditions hold;

falling back to (3.12) otherwise. The normaliser is `mN n = ∏_{p ≤ 2h} p^{-L_p}`, and
`integral_mN` proves `mN n · F_K ∈ ℤ[X]` for every `n ≥ 1`.
-/

public section

open Finset Polynomial

namespace Zeta5Irrational

/-- The cutoff `M` separating small primes from the inner range. -/
@[expose] def Mcut : ℕ :=
  400

/-- The small-prime exponent (3.12). -/
@[expose] noncomputable def Lsmall (n p : ℕ) : ℤ :=
  -(6 * (37 * n : ℕ) * (Nat.log p (200 * n) : ℤ) + (37 * n : ℕ) * (padicValNat p 24 : ℤ))

/-- The class offsets `β_c = 6 ℓ_N(c) - ℓ_K(c) - 4`. -/
@[expose] noncomputable def betaI (n p : ℕ) {m : ℕ} (c : Fin (m + 1)) : ℤ :=
  6 * (SX p (3 * n) (((c : ℕ) : ℤ) : ZMod p) : ℤ) - (SX p (40 * n) (((c : ℕ) : ℤ) : ZMod p) : ℤ) -
    4

/-- The water-filling parameters. -/
@[expose] def kloI (n p : ℕ) : ℤ :=
  -2 * ((40 * n / p : ℕ) : ℤ) - 6

/-- Upper admissible allocation level in the inner-prime range. -/
@[expose] def ktopI (n p : ℕ) : ℤ :=
  8 * ((40 * n / p : ℕ) : ℤ) + 20

/-- Rows reserved for the zero residue class in the inner allocation. -/
@[expose] def L0I (n p : ℕ) : ℕ :=
  3 * (40 * n / p) + 6

/-- The inner allocation. -/
@[expose] noncomputable def allocI (n p m : ℕ) : Fin (m + 1) → ℕ :=
  allocK (betaI n p (m := m)) (37 * n)
    (kfSel (betaI n p (m := m)) (37 * n) (L0I n p) (kloI n p) (ktopI n p))

/-- The side conditions of the inner bound. -/
@[expose] def InnerOK (n p : ℕ) : Prop :=
  ∃ _hm : 2 * (p / 2) + 1 = p,
    ∃ hm1 : 1 ≤ p / 2,
      5 ≤ p ∧
        Sep p (PlK (40 * n)) ∧
          40 * n < p ^ 2 ∧
            5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 < p ^ 2 ∧
              ∑ c, allocI n p (p / 2) c = 37 * n ∧
                tmin hm1 (allocI n p (p / 2)) (Bse p (40 * n) (3 * n)) ≤
                  2 * (allocI n p (p / 2) 0 : ℚ) + (Bse p (40 * n) (3 * n) 0 - 4) / 2

/-- The inner weight sum (for `m = p / 2`). -/
@[expose] noncomputable def WI (n p : ℕ) : ℚ :=
  if hm1 : 1 ≤ p / 2 then ∑ s, wcap hm1 (allocI n p (p / 2)) (Bse p (40 * n) (3 * n)) s else 0

/-- The side conditions of the outer bound. -/
@[expose] def OuterOK (n p : ℕ) : Prop :=
  2 * (p / 2) + 1 = p ∧ 7 ≤ p ∧ 40 * n < 3 * p ∧ 2 * (40 * n) < p ^ 2 ∧ 3 * n < p

/-- The outer weight sum minus the rank loss (for `m = p / 2`). -/
@[expose] noncomputable def WO (n p : ℕ) : ℚ :=
  if hpp : p.Prime then
    if hm : 2 * (p / 2) + 1 = p then
      haveI : Fact p.Prime := ⟨hpp⟩
      2 * ∑ c, ∑ i ∈ range (LoC hm n c), wO hm n c i -
        ((37 * n - ((2 * p + 22 * n - 3) - (37 * n - 1)) : ℕ) : ℚ)
    else 0
  else 0

open Classical in
/-- **The local exponent.** -/
@[expose] noncomputable def Lp (n p : ℕ) : ℤ :=
  if p * Mcut ≤ 40 * n then Lsmall n p
  else
    if 3 * p ≤ 40 * n then (if InnerOK n p then vSK n p + ⌊2 * WI n p⌋ else Lsmall n p)
    else (if OuterOK n p then vSK n p + ⌊WO n p⌋ else Lsmall n p)

/-- **The normaliser** `m_K = ∏_{p ≤ 2h} p^{-L_p}`. -/
@[expose] noncomputable def mN (n : ℕ) : ℚ :=
  ∏ p ∈ (range (2 * (37 * n) + 1)).filter Nat.Prime, (p : ℚ) ^ (-Lp n p)

lemma mN_pos (n : ℕ) : 0 < mN n := by
  unfold mN
  apply Finset.prod_pos
  intro p hp
  have : 0 < p := (Finset.mem_filter.mp hp).2.pos
  exact zpow_pos (by exact_mod_cast this) _

/-! ### Validity of the local exponents -/

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
lemma Sep_PlK {K : ℕ} (hK : 2 * K < p ^ 2) : Sep p (PlK K) := by
  intro r hr s hs hrs _ hdvd
  obtain ⟨j, hj, ε, hε, rfl⟩ := mem_PlK_iff hr
  obtain ⟨j', hj', ε', hε', rfl⟩ := mem_PlK_iff hs
  have h1 := Finset.mem_Icc.mp hj
  have h2 := Finset.mem_Icc.mp hj'
  have hlt : |ε * (j : ℤ) - ε' * j'| < (p : ℤ) ^ 2 := by
    rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl <;> rw [abs_lt] <;> constructor <;>
      nlinarith
  have := Int.eq_zero_of_abs_lt_dvd hdvd hlt
  exact hrs (by linarith)

lemma GV_F_of_Δ {n : ℕ} {r : ℚ} (h : GV p (Δ n) r) : GV p (F n) ((vSK n p : ℚ) + r) := by
  unfold F
  have hS : VG p (S n) (vSK n p) := by unfold vSK; right; exact le_refl _
  exact GV.C_mul hS h

lemma GV_F_Lsmall {n : ℕ} (hn : 1 ≤ n) : GV p (F n) (Lsmall n p) := by
  have := small_prime_bound (p := p) hn
  have e :
    ((Lsmall n p : ℤ) : ℚ) =
      -(6 * ((37 * n : ℕ) : ℚ) * (Nat.log p (200 * n) : ℚ) +
          ((37 * n : ℕ) : ℚ) * (padicValNat p 24 : ℚ)) := by
    simp only [Lsmall, Int.cast_neg, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
  rw [e]; exact this

lemma GV_F_inner {n : ℕ} (h : InnerOK n p) : GV p (F n) (vSK n p + ⌊2 * WI n p⌋) := by
  obtain ⟨hm, hm1, hp5, hsep, hK, hdeg, hsum, hZ⟩ := h
  have hΔ := inner_bound_cap hp5 hm hm1 n (allocI n p (p / 2)) hsum hsep hK hdeg hZ
  have hW : WI n p = ∑ s, wcap hm1 (allocI n p (p / 2)) (Bse p (40 * n) (3 * n)) s := by
    unfold WI; rw [dite_eq_left hm1]
  rw [← hW] at hΔ
  have := GV_F_of_Δ hΔ
  exact this.mono (by have := Int.floor_le (2 * WI n p); linarith)

lemma GV_F_outer {n : ℕ} (h : OuterOK n p) : GV p (F n) (vSK n p + ⌊WO n p⌋) := by
  obtain ⟨hm, hp7, hK3, hK, hpN⟩ := h
  have hΔ := outer_bound hm n hp7 hK3 hK hpN
  have hW :
    WO n p =
      2 * ∑ c, ∑ i ∈ range (LoC hm n c), wO hm n c i -
        ((37 * n - ((2 * p + 22 * n - 3) - (37 * n - 1)) : ℕ) : ℚ) :=
    by unfold WO; rw [dite_eq_left hp.out, dite_eq_left hm]
  rw [← hW] at hΔ
  have := GV_F_of_Δ hΔ
  exact this.mono (by have := Int.floor_le (WO n p); linarith)

/-- **Every local exponent is valid.** -/
theorem GV_F_Lp {n : ℕ} (hn : 1 ≤ n) : GV p (F n) (Lp n p) := by
  unfold Lp
  split_ifs with h1 h2 h3 h4
  · exact GV_F_Lsmall hn
  · exact_mod_cast GV_F_inner h3
  · exact GV_F_Lsmall hn
  · exact_mod_cast GV_F_outer h4
  · exact GV_F_Lsmall hn

/-! ### Integrality -/

lemma padicValNat_factorial_lt {k : ℕ} (hk : k < p) : padicValNat p k.factorial = 0 :=
  padicValNat.eq_zero_of_not_dvd
    (fun h => by have := (Nat.Prime.dvd_factorial hp.out).mp h; omega)

lemma vSK_big {n : ℕ} (hn : 1 ≤ n) (hbig : 2 * (37 * n) < p) : vSK n p = 0 := by
  have h := vS_eq (by omega : 0 < n) hp.out
  rw [h, padicValNat_factorial_lt (by omega), padicValNat_factorial_lt (by omega)]
  have h4 : padicValNat p 4 = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega)
  rw [h4,
    Finset.sum_eq_zero
      (fun i hi => by
        rw [padicValNat_factorial_lt (by have := Finset.mem_Icc.mp hi; omega)];
        rfl)]
  simp

lemma OuterOK_big {n : ℕ} (hn : 1 ≤ n) (hbig : 2 * (37 * n) < p) : OuterOK n p := by
  have hodd : 2 * (p / 2) + 1 = p := by
    have := hp.out.eq_one_or_self_of_dvd 2
    rcases Nat.even_or_odd p with ⟨k, hk⟩ | ⟨k, hk⟩
    · have := this ⟨k, by omega⟩; omega
    · omega
  refine ⟨hodd, by omega, by omega, by nlinarith, by omega⟩

lemma WO_big {n : ℕ} (hbig : 2 * (37 * n) < p) : 0 ≤ WO n p := by
  unfold WO
  rw [dite_eq_left hp.out]
  split_ifs with hm
  · have hsum : ∑ c, ∑ i ∈ range (LoC hm n c), wO hm n c i = 0 := by
      refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun i hi => ?_
      by_cases hc : c = 0
      · exfalso
        subst hc
        have hL : LoC hm n 0 = 0 := by
          unfold LoC tailC
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro j hj hj0
          have hj' := Finset.mem_Icc.mp hj
          have hd : p ∣ j := by exact_mod_cast (jc_eq_zero_iff hm j).mp hj0
          have := Nat.le_of_dvd (by omega) hd
          omega
        rw [hL] at hi; simp at hi
      · have hnb : nbC hm n c = 0 := by
          unfold nbC bigC
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro j hj
          have := Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1
          omega
        unfold wO
        rw [ite_eq_right hc, hnb, ite_eq_right (by omega)]
    rw [hsum, show 37 * n - ((2 * p + 22 * n - 3) - (37 * n - 1)) = 0 by omega]
    simp
  · exact le_refl _

lemma GV_F_big {n : ℕ} (hn : 1 ≤ n) (hbig : 2 * (37 * n) < p) : GV p (F n) 0 := by
  have h := GV_F_outer (OuterOK_big hn hbig)
  rw [vSK_big hn hbig] at h
  refine h.mono ?_
  have := WO_big (n := n) hbig
  have h0 : (0 : ℤ) ≤ ⌊WO n p⌋ := Int.floor_nonneg.mpr this
  have h0' : (0 : ℚ) ≤ (⌊WO n p⌋ : ℚ) := by exact_mod_cast h0
  push_cast
  linarith

omit hp in
lemma padicValRat_mN (n : ℕ) (p : ℕ) [Fact p.Prime] :
    padicValRat p (mN n) = if p ≤ 2 * (37 * n) then -Lp n p else 0 := by
  unfold mN
  rw [padicValRat_finset_prod _ _
      (fun q hq => by
        have := (Finset.mem_filter.mp hq).2.pos
        exact zpow_ne_zero _ (by exact_mod_cast this.ne'))]
  simp only [padicValRat.zpow, padicValRat.of_nat]
  have hval :
    ∀ q ∈ (range (2 * (37 * n) + 1)).filter Nat.Prime,
      (padicValNat p q : ℤ) = if q = p then 1 else 0 := by
    intro q hq
    have hq' : q.Prime := (Finset.mem_filter.mp hq).2
    have := Fact.mk hq'
    split_ifs with h
    · subst h; simp []
    · rw [padicValNat_primes (Ne.symm h)]; rfl
  rw [Finset.sum_congr rfl (fun q hq => by rw [hval q hq])]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  have hpp : (Fact.out : p.Prime) = (Fact.out : p.Prime) := rfl
  by_cases h : p ≤ 2 * (37 * n)
  · rw [ite_eq_left (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Fact.out⟩),
      ite_eq_left h]
  · rw [ite_eq_right
        (fun hm => h (by have := Finset.mem_range.mp (Finset.mem_filter.mp hm).1; omega)),
      ite_eq_right h]

/-- A rational number which is `p`-integral at every prime is an integer. -/
lemma rat_int_of_VG {q : ℚ} (h : ∀ p : ℕ, ∀ _ : Fact p.Prime, VG p q 0) : ∃ z : ℤ, q = z := by
  by_contra hne
  have hden : q.den ≠ 1 := fun h1 => hne ⟨q.num, (Rat.coe_int_num_of_den_eq_one h1).symm⟩
  set p := q.den.minFac with hpdef
  have hpp : p.Prime := Nat.minFac_prime hden
  have := Fact.mk hpp
  have hdvd : p ∣ q.den := Nat.minFac_dvd _
  rcases h p ‹_› with h0 | hv
  · exact hne ⟨0, by simp [h0]⟩
  · have hnum : ¬(p : ℤ) ∣ q.num := by
      intro hd
      have hc := q.reduced
      have : p ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd (Int.natCast_dvd.mp hd) hdvd
      rw [hc] at this
      exact hpp.one_lt.ne' (Nat.dvd_one.mp this)
    have h1 : padicValInt p q.num = 0 := padicValInt.eq_zero_of_not_dvd hnum
    have h2 : 1 ≤ padicValNat p q.den := one_le_padicValNat_of_dvd q.den_ne_zero hdvd
    have e : padicValRat p q = padicValInt p q.num - padicValNat p q.den := rfl
    have hlt : padicValRat p q < 0 := by rw [e, h1]; omega
    have : (padicValRat p q : ℚ) < 0 := by exact_mod_cast hlt
    linarith

/-- **Integrality** (Proposition 5.1 for the normaliser `mN`). -/
theorem integral_mN {n : ℕ} (hn : 1 ≤ n) :
    ∃ Q : ℤ[X], Q.map (Int.castRingHom ℚ) = C (mN n) * F n := by
  have hall : ∀ p : ℕ, ∀ _ : Fact p.Prime, GV p (C (mN n) * F n) 0 := by
    intro p _
    have hm : VG p (mN n) (if p ≤ 2 * (37 * n) then -Lp n p else 0 : ℤ) := by
      right;
      rw [padicValRat_mN]
    by_cases hbig : p ≤ 2 * (37 * n)
    · rw [ite_eq_left hbig] at hm
      have := GV.C_mul hm (GV_F_Lp (p := p) hn)
      refine this.mono ?_
      push_cast; linarith
    · rw [ite_eq_right hbig] at hm
      have := GV.C_mul hm (GV_F_big (p := p) hn (by omega))
      simpa using this
  have hcoef : ∀ k, ∃ z : ℤ, (C (mN n) * F n).coeff k = z := fun k =>
    rat_int_of_VG fun p hp => hall p hp k
  have hlift : C (mN n) * F n ∈ lifts (Int.castRingHom ℚ) := by
    rw [lifts_iff_coeff_lifts]
    intro k
    obtain ⟨z, hz⟩ := hcoef k
    exact ⟨z, by simp [hz]⟩
  obtain ⟨Q, hQ⟩ := hlift
  exact ⟨Q, hQ⟩

end Zeta5Irrational
