/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Legendre
import Mathlib.Tactic.ReduceModChar
import Mathlib.Data.Rat.Star
import Mathlib.Data.Int.Star
public import LeanPool.Zeta5Irrational.Growth.ClassData
public import LeanPool.Zeta5Irrational.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic

/-! # The inner range: a per-prime upper bound for `-L_p`

For `K/400 < p ≤ K/3` (and `n` large enough for the side conditions), every level `k` in
`[klo, ktop]` gives
`-L_p ≤ -2h q + 12h q' + 2 T(h) - h k + 2 ∑_{c=1}^m ψ(k, B + 6a'_c - a_c) + (k - klo) L₀ + 2B₀ + 1`,
with `q = ⌊K/p⌋`, `q' = ⌊N/p⌋`, `B = 12q' - 2q - 4`, the class counts `a_c, a'_c` of
`ClassSum`, and the layer-cake function `T`.
-/

public section

open Finset

namespace Zeta5Irrational

variable {p : ℕ} [hp : Fact p.Prime]

lemma sum_erase_zero_eq_Icc {m : ℕ} (F : ℕ → ℚ) :
    ∑ c ∈ (univ : Finset (Fin (m + 1))).erase 0, F c = ∑ c ∈ Icc 1 m, F c := by
  have h1 := Finset.add_sum_erase (univ : Finset (Fin (m + 1))) (fun c => F c) (Finset.mem_univ 0)
  rw [Fin.sum_univ_eq_sum_range (fun c => F c), Finset.sum_range_eq_add_Ico _ (by omega)] at h1
  simp only [Fin.val_zero] at h1
  have h2 : Ico 1 (m + 1) = Icc 1 m := by ext c; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
  rw [h2] at h1
  linarith

/-- `-v_p(S_K)` in the inner and outer ranges. -/
lemma neg_vSK_le {n : ℕ} (hn : 1 ≤ n) (_hp3 : 3 ≤ p) (hN : 3 * n < p ^ 2)
    (hH : 2 * (37 * n) < p ^ 2) (J : ℕ) (hJ : 2 * (37 * n) ≤ J * p) :
    -(vSK n p : ℝ) ≤
      -2 * (37 * n : ℕ) * ((40 * n / p : ℕ) : ℝ) + 12 * (37 * n : ℕ) * ((3 * n / p : ℕ) : ℝ) +
        2 * layer p J (37 * n : ℕ) := by
  have h := vS_eq (by omega : 0 < n) hp.out
  rw [h]
  have h1 := padicValNat_factorial_ge (p := p) (k := 40 * n)
  have h2 := padicValNat_factorial_small (p := p) (k := 3 * n) hN
  have h3 : ∀ i ∈ Icc 1 (37 * n - 1), padicValNat p (2 * i).factorial = 2 * i / p := fun i hi =>
    padicValNat_factorial_small (by have := (Finset.mem_Icc.mp hi).2; omega)
  have hsum : (((∑ i ∈ Icc 1 (37 * n - 1), 2 * i / p : ℕ)) : ℝ) ≤ layer p J (37 * n : ℕ) := by
    have := sum_floor_le_layer (p := p) J (37 * n) hJ
    rw [Finset.sum_range_eq_add_Ico _ (by omega)] at this
    have e2 : Ico 1 (37 * n) = Icc 1 (37 * n - 1) := by
      ext c;
      simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [e2] at this
    rw [Nat.cast_sum]
    simpa using this
  have hs :
    ∑ i ∈ Icc 1 (37 * n - 1), (padicValNat p (2 * i).factorial : ℤ) =
      ((∑ i ∈ Icc 1 (37 * n - 1), 2 * i / p : ℕ) : ℤ) :=
    by rw [Nat.cast_sum]; exact Finset.sum_congr rfl (fun i hi => by rw [h3 i hi])
  rw [hs, h2]
  generalize padicValNat p (40 * n).factorial = A at h1 ⊢
  generalize padicValNat p 4 = B
  generalize (∑ i ∈ Icc 1 (37 * n - 1), 2 * i / p) = Sg at hsum ⊢
  generalize 40 * n / p = q at h1 ⊢
  generalize 3 * n / p = q'
  have h1R : (q : ℝ) ≤ (A : ℝ) := by exact_mod_cast h1
  have hB : (0 : ℝ) ≤ (B : ℝ) := by positivity
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  push_cast at hsum ⊢
  nlinarith [mul_le_mul_of_nonneg_left h1R (show (0 : ℝ) ≤ 74 * n by positivity),
    mul_nonneg (show (0 : ℝ) ≤ 37 * n - 1 by linarith) hB]

/-- The zero-class deficit bound. -/
@[expose] noncomputable def Bmax (n p : ℕ) : ℝ :=
  max 0
      ((ktopI n p : ℝ) / 2 -
        ((5 + 12 * ((3 * n / p : ℕ) : ℝ) - 2 * ((40 * n / p : ℕ) : ℝ)) - 4) / 2) *
    (max 0
          ((ktopI n p : ℝ) / 2 -
            ((5 + 12 * ((3 * n / p : ℕ) : ℝ) - 2 * ((40 * n / p : ℕ) : ℝ)) - 4) / 2) /
        2 +
      1)

/-- The class function of the inner range. -/
@[expose] noncomputable def hIn (n p : ℕ) (k : ℤ) (a a' : ℕ) : ℝ :=
  (psiR k (12 * ((3 * n / p : ℕ) : ℤ) - 2 * ((40 * n / p : ℕ) : ℤ) - 4 + 6 * (a' : ℤ) - a) : ℝ)

section

variable {n : ℕ} (hn : 33 ≤ n) (hodd : 2 * (p / 2) + 1 = p) (hp7 : 7 ≤ p)
  (hsmall : ¬p * Mcut ≤ 40 * n) (hin : 3 * p ≤ 40 * n) (hsq : 2 * (40 * n) < p ^ 2)
  (hdeg : 5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 < p ^ 2)

include hodd in
lemma betaI_eq {c : ℕ} (hc1 : 1 ≤ c) (hcm : c ≤ p / 2) :
    betaI n p (m := p / 2) (⟨c, by omega⟩ : Fin (p / 2 + 1)) =
      12 * ((3 * n / p : ℕ) : ℤ) - 2 * ((40 * n / p : ℕ) : ℤ) - 4 +
          6 * (aCnt p (3 * n % p) c : ℤ) -
        aCnt p (40 * n % p) c := by
  unfold betaI
  simp only
  rw [SX_class hodd hc1 hcm, SX_class hodd hc1 hcm]
  push_cast; ring

include hodd hsmall in
omit hp in
lemma q_lt : 40 * n / p < 400 := by
  unfold Mcut at hsmall
  rw [not_le] at hsmall
  exact (Nat.div_lt_iff_lt_mul (by omega)).mpr (by linarith)

include hodd in
lemma klo_le_beta (c : Fin (p / 2 + 1)) (hc : c ≠ 0) : kloI n p ≤ betaI n p c := by
  have hc1 : 1 ≤ (c : ℕ) := by
    rcases Nat.eq_zero_or_pos (c : ℕ) with h | h
    · exact absurd (Fin.ext h) hc
    · exact h
  have hcm := Nat.lt_succ_iff.mp c.isLt
  have e := betaI_eq (n := n) hodd hc1 hcm
  simp only [Fin.eta] at e
  rw [e]
  unfold kloI aCnt
  generalize 3 * n / p = q' at *
  generalize 40 * n / p = q at *
  split_ifs <;> omega

include hodd in
lemma rowsK_klo : rowsK (betaI n p (m := p / 2)) (kloI n p) = 0 := by
  unfold rowsK
  refine Finset.sum_eq_zero fun c hc => ?_
  have := klo_le_beta (n := n) hodd c (Finset.mem_erase.mp hc).1
  unfold lrow; omega

lemma Bse_eq_beta (c : Fin (p / 2 + 1)) (hc : c ≠ 0) :
    Bse p (40 * n) (3 * n) (c : ℕ) = (betaI n p c : ℚ) + 4 := by
  have hc0 : (c : ℕ) ≠ 0 := fun h => hc (Fin.ext h)
  unfold Bse betaI
  rw [ite_eq_right hc0]
  push_cast; ring

lemma Bse_zero_eq :
    Bse p (40 * n) (3 * n) 0 = 5 + 12 * ((3 * n / p : ℕ) : ℚ) - 2 * ((40 * n / p : ℕ) : ℚ) := by
  unfold Bse
  simp only [ite_eq_left, Nat.cast_zero, Int.cast_zero]
  rw [SX_zero, SX_zero]
  push_cast; ring

include hn hodd hp7 hsmall hin hsq hdeg in
/-- The inner side conditions hold. -/
lemma innerOK_of : InnerOK n p := by
  have hm1 : 1 ≤ p / 2 := by omega
  set β := betaI n p (m := p / 2) with hβdef
  have hq := q_lt hodd hsmall
  have hlo : rowsK β (kloI n p) + L0I n p ≤ 37 * n := by rw [rowsK_klo hodd]; unfold L0I; omega
  set kf := kfSel β (37 * n) (L0I n p) (kloI n p) (ktopI n p) with hkf
  have hfeas : rowsK β kf + L0I n p ≤ 37 * n :=
    kfSel_feasible β (37 * n) (L0I n p) (kloI n p) (ktopI n p) hlo
  have hkfle : kf ≤ ktopI n p :=
    kfSel_le β (37 * n) (L0I n p) (kloI n p) (ktopI n p)
      (by unfold kloI ktopI; generalize 40 * n / p = q; omega)
  have hβ : ∀ c : Fin (p / 2 + 1), c ≠ 0 → Bse p (40 * n) (3 * n) (c : ℕ) = (β c : ℚ) + 4 :=
    fun c hc => Bse_eq_beta c hc
  refine ⟨hodd, hm1, by omega, Sep_PlK hsq, by nlinarith, hdeg, ?_, ?_⟩
  · exact sum_allocK β (37 * n) kf (by omega)
  · -- the zero-class condition
    have h1 := tmin_allocK_le hm1 (Bse p (40 * n) (3 * n)) β hβ (37 * n) kf
    have hA0 : allocI n p (p / 2) 0 = 37 * n - rowsK β kf := by
      unfold allocI allocK;
      rw [ite_eq_left rfl]
    have hL0 : L0I n p ≤ allocI n p (p / 2) 0 := by rw [hA0]; omega
    have hL0R : ((L0I n p : ℕ) : ℚ) ≤ (allocI n p (p / 2) 0 : ℚ) := by exact_mod_cast hL0
    rw [Bse_zero_eq]
    have hb1 : (β ⟨1, by omega⟩ : ℚ) ≤ 12 * ((3 * n / p : ℕ) : ℚ) + 8 := by
      have e := betaI_eq (n := n) hodd (c := 1) le_rfl (by omega)
      have : β ⟨1, by omega⟩ ≤ 12 * ((3 * n / p : ℕ) : ℤ) + 8 := by
        rw [hβdef, e]; unfold aCnt; generalize 3 * n / p = q' at *; generalize 40 * n / p = q at *
        split_ifs <;> omega
      have h' := (Int.cast_le (R := ℚ)).mpr this
      rw [Int.cast_add, Int.cast_mul, Int.cast_natCast] at h'
      norm_num at h'
      exact h'
    have hkfR : (kf : ℚ) ≤ ktopI n p := by exact_mod_cast hkfle
    unfold ktopI at hkfR
    unfold L0I at hL0R
    rw [Int.cast_add, Int.cast_mul, Int.cast_natCast] at hkfR
    norm_num at hkfR
    push_cast at hL0R
    refine h1.trans ?_
    rw [div_le_iff₀ (by norm_num : (0 : ℚ) < 2)]
    have hq0 : (0 : ℚ) ≤ ((40 * n / p : ℕ) : ℚ) := by positivity
    have hq0' : (0 : ℚ) ≤ ((3 * n / p : ℕ) : ℚ) := by positivity
    refine max_le ?_ ?_ <;> linarith

include hn hodd hp7 hsmall hin hsq hdeg in
/-- **The inner per-prime bound** (discrete form). -/
theorem inner_Lp_le (k : ℤ) (hk1 : kloI n p ≤ k) (hk2 : k ≤ ktopI n p) :
    -(Lp n p : ℝ) ≤
      -2 * (37 * n : ℕ) * ((40 * n / p : ℕ) : ℝ) + 12 * (37 * n : ℕ) * ((3 * n / p : ℕ) : ℝ) +
                  2 * layer p 1000 (37 * n : ℕ) -
                (37 * n : ℕ) * (k : ℝ) +
              2 * ∑ c ∈ Icc 1 (p / 2), hIn n p k (aCnt p (40 * n % p) c) (aCnt p (3 * n % p) c) +
            ((k - kloI n p : ℤ) : ℝ) * (L0I n p : ℝ) +
          2 * Bmax n p +
        1 := by
  have hm1 : 1 ≤ p / 2 := by omega
  have hOK := innerOK_of hn hodd hp7 hsmall hin hsq hdeg
  have hLp : Lp n p = vSK n p + ⌊2 * WI n p⌋ := by
    unfold Lp;
    rw [ite_eq_right hsmall, ite_eq_left hin, ite_eq_left hOK]
  have hq :=
    q_lt hodd
      hsmall
        -- `v_p(S_K)`
  have hv :=
    neg_vSK_le (p := p) (n := n) (by omega) (by omega) (by nlinarith) (by nlinarith) 1000
      (by
        unfold Mcut at hsmall; rw [not_le] at hsmall
        nlinarith)
        -- the allocation
  set β := betaI n p (m := p / 2) with hβdef
  have hlo : rowsK β (kloI n p) + L0I n p ≤ 37 * n := by rw [rowsK_klo hodd]; unfold L0I; omega
  set kf := kfSel β (37 * n) (L0I n p) (kloI n p) (ktopI n p) with hkf
  have hfeas : rowsK β kf + L0I n p ≤ 37 * n :=
    kfSel_feasible β (37 * n) (L0I n p) (kloI n p) (ktopI n p) hlo
  have hkfle : kf ≤ ktopI n p :=
    kfSel_le β (37 * n) (L0I n p) (kloI n p) (ktopI n p)
      (by unfold kloI ktopI; generalize 40 * n / p = q; omega)
  have hβ : ∀ c : Fin (p / 2 + 1), c ≠ 0 → Bse p (40 * n) (3 * n) (c : ℕ) = (β c : ℚ) + 4 :=
    fun c hc => Bse_eq_beta c hc
  have hW := sum_wcap_allocK hm1 (Bse p (40 * n) (3 * n)) β hβ (37 * n) kf (by omega)
  have hWI : WI n p = ∑ s, wcap hm1 (allocK β (37 * n) kf) (Bse p (40 * n) (3 * n)) s := by
    unfold WI; rw [dite_eq_left hm1]; rfl
  rw [← hWI] at hW
  have hPhi :=
    PhiK_le_kf β (37 * n) (L0I n p) (kloI n p) (ktopI n p) hlo hk1
      hk2
        -- `Φ(k)` as a class sum
  have hsumQ :
    ∑ c ∈ (univ : Finset (Fin (p / 2 + 1))).erase 0, psiR k (β c) =
      ∑ c ∈ Icc 1 (p / 2),
        psiR k
          (12 * ((3 * n / p : ℕ) : ℤ) - 2 * ((40 * n / p : ℕ) : ℤ) - 4 +
              6 * (aCnt p (3 * n % p) c : ℤ) -
            aCnt p (40 * n % p) c) := by
    have e :=
      sum_erase_zero_eq_Icc (m := p / 2)
        (fun c =>
          psiR k
            (6 * (SX p (3 * n) (((c : ℕ) : ℤ) : ZMod p) : ℤ) -
                (SX p (40 * n) (((c : ℕ) : ℤ) : ZMod p) : ℤ) -
              4))
    refine e.trans (Finset.sum_congr rfl fun c hc => ?_)
    have hc' := Finset.mem_Icc.mp hc
    have := betaI_eq (n := n) hodd hc'.1 hc'.2
    unfold betaI at this
    simp only at this ⊢
    rw [this]
  have hPhik :
    (PhiK β (37 * n) k : ℝ) =
      ((37 * n : ℕ) : ℝ) * k / 2 -
        ∑ c ∈ Icc 1 (p / 2), hIn n p k (aCnt p (40 * n % p) c) (aCnt p (3 * n % p) c) := by
    unfold PhiK
    rw [hsumQ]
    unfold hIn
    push_cast
    ring
      -- the zero-class deficit
  have hB0 :
    max 0 ((kf : ℚ) / 2 - (Bse p (40 * n) (3 * n) 0 - 4) / 2) *
        (max 0 ((kf : ℚ) / 2 - (Bse p (40 * n) (3 * n) 0 - 4) / 2) / 2 + 1) ≤
      (Bmax n p : ℝ) := by
    rw [Bse_zero_eq]
    unfold Bmax
    have hkR : ((kf : ℤ) : ℝ) ≤ ((ktopI n p : ℤ) : ℝ) := by exact_mod_cast hkfle
    push_cast
    generalize ((40 * n / p : ℕ) : ℝ) = qR
    generalize ((3 * n / p : ℕ) : ℝ) = qR'
    generalize ((ktopI n p : ℤ) : ℝ) = tR at hkR ⊢
    generalize ((kf : ℤ) : ℝ) = kR at hkR ⊢
    set D1 := max 0 (kR / 2 - (5 + 12 * qR' - 2 * qR - 4) / 2) with hD1
    set D2 := max 0 (tR / 2 - (5 + 12 * qR' - 2 * qR - 4) / 2) with hD2
    have h0 : 0 ≤ D1 := le_max_left _ _
    have h12 : D1 ≤ D2 := max_le_max (le_refl 0) (by linarith)
    nlinarith
  have hfl : ((⌊2 * WI n p⌋ : ℤ) : ℝ) ≥ 2 * (WI n p : ℝ) - 1 := by
    have := Int.lt_floor_add_one (2 * WI n p)
    have : ((2 * WI n p : ℚ) : ℝ) < ((⌊2 * WI n p⌋ : ℤ) : ℝ) + 1 := by exact_mod_cast this
    push_cast at this; linarith
  have hWR :
    ((PhiK β (37 * n) kf : ℚ) : ℝ) -
        ((max 0 ((kf : ℚ) / 2 - (Bse p (40 * n) (3 * n) 0 - 4) / 2) *
              (max 0 ((kf : ℚ) / 2 - (Bse p (40 * n) (3 * n) 0 - 4) / 2) / 2 + 1) :
            ℚ) :
          ℝ) ≤
      (WI n p : ℝ) :=
    by exact_mod_cast hW
  have hPR :
    ((PhiK β (37 * n) k : ℚ) : ℝ) ≤
      ((PhiK β (37 * n) kf : ℚ) : ℝ) + ((k - kloI n p : ℤ) : ℝ) * (L0I n p : ℝ) / 2 := by
    have := (Rat.cast_le (K := ℝ)).mpr hPhi
    push_cast at this ⊢
    linarith
  rw [hLp]
  push_cast
  rw [hPhik] at hPR
  push_cast at hWR hB0 hv hPR
  linarith

end

end Zeta5Irrational
