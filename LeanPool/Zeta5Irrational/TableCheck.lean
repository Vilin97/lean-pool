/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Potential
import LeanPool.Zeta5Irrational.Certificates
import LeanPool.Zeta5Irrational.EnergyConst
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic

/-! # Reduction of the potential inequality (6.2) to a finite check (Table 2)

For each interval `[l, r]` of the partition of `(0, 2]`, the inequality `2Uρ(t) - V(t) ≤ M₀` on
`[l, r]` follows from monotonicity of `Uρ` and `V` and one numerical inequality at the endpoints.
The tail `t ≥ 2` is handled by the elementary bound (6.8).
-/

public section

open Filter Topology Set Finset

namespace Zeta5Irrational

lemma aρ_one_lt_qm : aρ 1 < qm := by norm_num [aρ, table1]

lemma qp_lt_bρ_one : qp < bρ 1 := by norm_num [bρ, table1]

lemma aρ_one_pos : 0 < aρ 1 := by norm_num [aρ, table1]

/-- Intervals to the left of `a₁`: `Uρ` nonincreasing, `V` nonincreasing. -/
lemma check_left {l r U V : ℝ} (hlr : l ≤ r) (hr : r ≤ aρ 1) (hU : Uρ l ≤ U) (hV : V ≤ Vfield r)
    (hnum : 2 * U - V ≤ M0) : ∀ t, l ≤ t → t ≤ r → 0 < t → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t ht1 ht2 ht0
  have h1 : Uρ t ≤ Uρ l :=
    Uρ_antitoneOn (show l ∈ Iic (aρ 1) from hlr.trans hr) (show t ∈ Iic (aρ 1) from ht2.trans hr)
      ht1
  have h2 : Vfield r ≤ Vfield t :=
    Vfield_antitoneOn ⟨ht0, ht2.trans (hr.trans aρ_one_lt_qm.le)⟩
      ⟨ht0.trans_le ht2, hr.trans aρ_one_lt_qm.le⟩ ht2
  linarith

/-- Intervals to the right of `b₁`: `Uρ` nondecreasing, `V` nondecreasing. -/
lemma check_right {l r U V : ℝ} (hl : bρ 1 ≤ l) (hlr : l ≤ r) (hU : Uρ r ≤ U) (hV : V ≤ Vfield l)
    (hnum : 2 * U - V ≤ M0) : ∀ t, l ≤ t → t ≤ r → 0 < t → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t ht1 ht2 _
  have h1 : Uρ t ≤ Uρ r :=
    Uρ_monotoneOn (show t ∈ Ici (bρ 1) from hl.trans ht1) (show r ∈ Ici (bρ 1) from hl.trans hlr)
      ht2
  have h2 : Vfield l ≤ Vfield t :=
    Vfield_monotoneOn (show l ∈ Ici qp from qp_lt_bρ_one.le.trans hl)
      (show t ∈ Ici qp from qp_lt_bρ_one.le.trans (hl.trans ht1)) ht1
  linarith

/-- The constant value of `Uρ` on `[a₁, b₁]`. -/
noncomputable def Uρmid : ℝ :=
  ∑ j ∈ Icc 1 16, cρ j * Real.log ((bρ j - aρ j) / 4)

/-- The interval `[a₁, q₋]`. -/
lemma check_mid_left {U V : ℝ} (hU : Uρmid ≤ U) (hV : V ≤ Vfield qm) (hnum : 2 * U - V ≤ M0) :
    ∀ t, aρ 1 ≤ t → t ≤ qm → 0 < t → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t ht1 ht2 _
  have ht : t ∈ Icc (aρ 1) qm := ⟨ht1, ht2⟩
  have hqmb : qm ≤ bρ 1 := by norm_num [bρ, table1]
  rw [Uρ_of_mem ht.1 (ht.2.trans hqmb)]
  have h2 : Vfield qm ≤ Vfield t :=
    Vfield_antitoneOn ⟨aρ_one_pos.trans_le ht.1, ht.2⟩ ⟨by norm_num, le_rfl⟩ ht.2
  change 2 * Uρmid - Vfield t ≤ M0
  linarith

/-- The interval `[q₊, b₁]`. -/
lemma check_mid_right {U V : ℝ} (hU : Uρmid ≤ U) (hV : V ≤ Vfield qp) (hnum : 2 * U - V ≤ M0) :
    ∀ t, qp ≤ t → t ≤ bρ 1 → 0 < t → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t ht1 ht2 _
  have ht : t ∈ Icc qp (bρ 1) := ⟨ht1, ht2⟩
  rw [Uρ_of_mem ((aρ_one_lt_qm.le.trans (by norm_num)).trans ht.1) ht.2]
  have h2 : Vfield qp ≤ Vfield t :=
    Vfield_monotoneOn (Set.mem_Ici.mpr le_rfl) (show t ∈ Ici qp from ht.1) ht.1
  change 2 * Uρmid - Vfield t ≤ M0
  linarith

/-- The mixed lower bound for `V` on `[q₋, q₊]` (A.6):
`V(t) ≥ log(1+q₋) - 6α log(q₊ + α²) - 2 + 12α + 2√q₊ · P(√q₋)`. -/
lemma Vfield_ge_on_bracket {t : ℝ} (h1 : qm ≤ t) (h2 : t ≤ qp) :
    Real.log (1 + qm) - 6 * (3 / 40) * Real.log (qp + (3 / 40) ^ 2) - 2 + 12 * (3 / 40) +
        2 * Real.sqrt qp * Pfun (Real.sqrt qm) ≤
      Vfield t := by
  have ht : 0 < t := by
    have : (0 : ℝ) < qm := by norm_num
    linarith
  rw [Vfield_eq_Φ ht]
  unfold Φ
  have hs1 : Real.sqrt qm ≤ Real.sqrt t := Real.sqrt_le_sqrt h1
  have hs2 : Real.sqrt t ≤ Real.sqrt qp := Real.sqrt_le_sqrt h2
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hP : Pfun (Real.sqrt qm) ≤ Pfun (Real.sqrt t) :=
    Pfun_monotoneOn ⟨sqrt_qm_pos, sqrt_qm_le_y0⟩ ⟨hst, hs2.trans sqrt_qp_le_y0⟩ hs1
  have hPneg : Pfun (Real.sqrt qm) < 0 := Pfun_sqrt_qm_neg
  have hA : Real.log (1 + qm) ≤ Real.log (1 + Real.sqrt t ^ 2) := by
    rw [hsq];
    exact Real.log_le_log (by norm_num) (by linarith)
  have hB : Real.log (Real.sqrt t ^ 2 + (3 / 40) ^ 2) ≤ Real.log (qp + (3 / 40) ^ 2) := by
    rw [hsq]; exact Real.log_le_log (by positivity) (add_le_add h2 le_rfl)
  have hC1 : Real.sqrt qp * Pfun (Real.sqrt qm) ≤ Real.sqrt t * Pfun (Real.sqrt qm) :=
    mul_le_mul_of_nonpos_right hs2 hPneg.le
  have hC2 : Real.sqrt t * Pfun (Real.sqrt qm) ≤ Real.sqrt t * Pfun (Real.sqrt t) :=
    mul_le_mul_of_nonneg_left hP hst.le
  have hB' :
    -(6 * (3 / 40)) * Real.log (qp + (3 / 40) ^ 2) ≤
      -(6 * (3 / 40)) * Real.log (Real.sqrt t ^ 2 + (3 / 40) ^ 2) :=
    mul_le_mul_of_nonpos_left hB (by norm_num)
  have key :=
    add_le_add (add_le_add hA hB')
      (mul_le_mul_of_nonneg_left (hC1.trans hC2) (by norm_num : (0 : ℝ) ≤ 2))
  have e1 :
    Real.log (1 + qm) - 6 * (3 / 40) * Real.log (qp + (3 / 40) ^ 2) - 2 + 12 * (3 / 40) +
        2 * Real.sqrt qp * Pfun (Real.sqrt qm) =
      (Real.log (1 + qm) + -(6 * (3 / 40)) * Real.log (qp + (3 / 40) ^ 2) +
          2 * (Real.sqrt qp * Pfun (Real.sqrt qm))) +
        (-2 + 12 * (3 / 40)) :=
    by ring
  have e2 :
    Real.log (1 + Real.sqrt t ^ 2) - 6 * (3 / 40) * Real.log (Real.sqrt t ^ 2 + (3 / 40) ^ 2) -
            2 +
          12 * (3 / 40) +
        2 * Real.sqrt t * Pfun (Real.sqrt t) =
      (Real.log (1 + Real.sqrt t ^ 2) +
            -(6 * (3 / 40)) * Real.log (Real.sqrt t ^ 2 + (3 / 40) ^ 2) +
          2 * (Real.sqrt t * Pfun (Real.sqrt t))) +
        (-2 + 12 * (3 / 40)) :=
    by ring
  rw [e1, e2]
  exact add_le_add key le_rfl

/-- The interval `[q₋, q₊]`. -/
lemma check_mid {U V : ℝ} (hU : Uρmid ≤ U)
    (hV :
      V ≤
        Real.log (1 + qm) - 6 * (3 / 40) * Real.log (qp + (3 / 40) ^ 2) - 2 + 12 * (3 / 40) +
          2 * Real.sqrt qp * Pfun (Real.sqrt qm))
    (hnum : 2 * U - V ≤ M0) : ∀ t, qm ≤ t → t ≤ qp → 0 < t → 2 * Uρ t - Vfield t ≤ M0 := by
  intro t ht1 ht2 _
  have ht : t ∈ Icc qm qp := ⟨ht1, ht2⟩
  rw [Uρ_of_mem (aρ_one_lt_qm.le.trans ht.1) (ht.2.trans qp_lt_bρ_one.le)]
  have := Vfield_ge_on_bracket ht.1 ht.2
  change 2 * Uρmid - Vfield t ≤ M0
  linarith

/-! ### Wrappers for certified bounds -/

/-- Upper bound for `log r`, `r ≥ 1`, from a numerical bound on the truncated series. -/
lemma log_le_of_ge_one {r U : ℝ} (hr : 1 ≤ r) (m : ℕ)
    (hU :
      2 * ∑ k ∈ range m, (1 / (2 * (k : ℝ) + 1)) * ((r - 1) / (r + 1)) ^ (2 * k + 1) +
          2 * ((r - 1) / (r + 1)) ^ (2 * m + 1) / ((2 * m + 1) * (1 - ((r - 1) / (r + 1)) ^ 2)) ≤
        U) :
    Real.log r ≤ U :=
  (log_le_artanh hr m).trans hU

/-- Lower bound for `log r`, `r ≥ 1`. -/
lemma log_ge_of_ge_one {r L : ℝ} (hr : 1 ≤ r) (m : ℕ)
    (hL : L ≤ 2 * ∑ k ∈ range m, (1 / (2 * (k : ℝ) + 1)) * ((r - 1) / (r + 1)) ^ (2 * k + 1)) :
    L ≤ Real.log r :=
  hL.trans (log_ge_artanh hr m)

/-- Upper bound for `log w`, `0 < w ≤ 1`, via `log w = - log w⁻¹`. -/
lemma log_le_of_le_one {w L : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) (m : ℕ)
    (hL :
      L ≤ 2 * ∑ k ∈ range m, (1 / (2 * (k : ℝ) + 1)) * ((w⁻¹ - 1) / (w⁻¹ + 1)) ^ (2 * k + 1)) :
    Real.log w ≤ -L := by
  have h1 : 1 ≤ w⁻¹ := one_le_inv_iff₀.mpr ⟨hw, hw1⟩
  have := log_ge_of_ge_one h1 m hL
  rw [Real.log_inv] at this
  linarith

/-- Lower bound for `log w`, `0 < w ≤ 1`. -/
lemma log_ge_of_le_one {w U : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) (m : ℕ)
    (hU :
      2 * ∑ k ∈ range m, (1 / (2 * (k : ℝ) + 1)) * ((w⁻¹ - 1) / (w⁻¹ + 1)) ^ (2 * k + 1) +
          2 * ((w⁻¹ - 1) / (w⁻¹ + 1)) ^ (2 * m + 1) /
            ((2 * m + 1) * (1 - ((w⁻¹ - 1) / (w⁻¹ + 1)) ^ 2)) ≤
        U) :
    -U ≤ Real.log w := by
  have h1 : 1 ≤ w⁻¹ := one_le_inv_iff₀.mpr ⟨hw, hw1⟩
  have := log_le_of_ge_one h1 m hU
  rw [Real.log_inv] at this
  linarith

/-- `arctan z ≥ L` from a truncated alternating series, `0 ≤ z < 1`. -/
lemma arctan_ge_of_series {z L : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) (k : ℕ)
    (hL : L ≤ ∑ i ∈ range (2 * k), (-1 : ℝ) ^ i * (z ^ (2 * i + 1) / (2 * (i : ℝ) + 1))) :
    L ≤ Real.arctan z :=
  hL.trans (arctan_ge_partial hz0 hz1 k)

/-- `arctan z ≤ U` from a truncated alternating series, `0 ≤ z < 1`. -/
lemma arctan_le_of_series {z U : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) (k : ℕ)
    (hU : ∑ i ∈ range (2 * k + 1), (-1 : ℝ) ^ i * (z ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) ≤ U) :
    Real.arctan z ≤ U :=
  (arctan_le_partial hz0 hz1 k).trans hU

/--
Half-angle, lower bound: `2 L ≤ arctan z` if `L ≤ arctan (z / (1 + hi))` with `√(1+z²) ≤ hi`. -/
lemma arctan_ge_half {z hi L : ℝ} (hz : 0 ≤ z) (hhi : Real.sqrt (1 + z ^ 2) ≤ hi)
    (hL : L ≤ Real.arctan (z / (1 + hi))) : 2 * L ≤ Real.arctan z := by
  rw [arctan_eq_two_mul_arctan hz]
  have h : z / (1 + hi) ≤ z / (1 + Real.sqrt (1 + z ^ 2)) :=
    div_le_div_of_nonneg_left hz (by positivity) (by linarith)
  linarith [Real.arctan_strictMono.monotone h]

/--
Half-angle, upper bound: `arctan z ≤ 2 U` if `arctan (z / (1 + lo)) ≤ U` with `0 ≤ lo ≤ √(1+z²)`. -/
lemma arctan_le_half {z lo U : ℝ} (hz : 0 ≤ z) (hlo0 : 0 ≤ lo) (hlo : lo ≤ Real.sqrt (1 + z ^ 2))
    (hU : Real.arctan (z / (1 + lo)) ≤ U) : Real.arctan z ≤ 2 * U := by
  rw [arctan_eq_two_mul_arctan hz]
  have h : z / (1 + Real.sqrt (1 + z ^ 2)) ≤ z / (1 + lo) :=
    div_le_div_of_nonneg_left hz (by linarith) (by linarith)
  linarith [Real.arctan_strictMono.monotone h]

/-- Inversion, lower bound: `π/2 - U ≤ arctan z` if `arctan (1/z) ≤ U`, `z > 0`. -/
lemma arctan_ge_inv {z U : ℝ} (hz : 0 < z) (hU : Real.arctan (1 / z) ≤ U) :
    Real.pi / 2 - U ≤ Real.arctan z := by
  rw [one_div, Real.arctan_inv_of_pos hz] at hU
  linarith

/-- Inversion, upper bound: `arctan z ≤ π/2 - L` if `L ≤ arctan (1/z)`, `z > 0`. -/
lemma arctan_le_inv {z L : ℝ} (hz : 0 < z) (hL : L ≤ Real.arctan (1 / z)) :
    Real.arctan z ≤ Real.pi / 2 - L := by
  rw [one_div, Real.arctan_inv_of_pos hz] at hL
  linarith

/-- Monotonicity transfer for arctan with a rational enclosure of the argument. -/
lemma arctan_ge_of_le {x z L : ℝ} (hzx : z ≤ x) (hL : L ≤ Real.arctan z) : L ≤ Real.arctan x :=
  hL.trans (Real.arctan_strictMono.monotone hzx)

lemma arctan_le_of_ge {x z U : ℝ} (hxz : x ≤ z) (hU : Real.arctan z ≤ U) : Real.arctan x ≤ U :=
  (Real.arctan_strictMono.monotone hxz).trans hU

/-- The expanded form of `Uρ`. -/
lemma Uρ_expand (x : ℝ) :
    Uρ x =
      cρ 1 * Uω (aρ 1) (bρ 1) x + cρ 2 * Uω (aρ 2) (bρ 2) x + cρ 3 * Uω (aρ 3) (bρ 3) x +
                                cρ 4 * Uω (aρ 4) (bρ 4) x +
                              cρ 5 * Uω (aρ 5) (bρ 5) x +
                            cρ 6 * Uω (aρ 6) (bρ 6) x +
                          cρ 7 * Uω (aρ 7) (bρ 7) x +
                        cρ 8 * Uω (aρ 8) (bρ 8) x +
                      cρ 9 * Uω (aρ 9) (bρ 9) x +
                    cρ 10 * Uω (aρ 10) (bρ 10) x +
                  cρ 11 * Uω (aρ 11) (bρ 11) x +
                cρ 12 * Uω (aρ 12) (bρ 12) x +
              cρ 13 * Uω (aρ 13) (bρ 13) x +
            cρ 14 * Uω (aρ 14) (bρ 14) x +
          cρ 15 * Uω (aρ 15) (bρ 15) x +
        cρ 16 * Uω (aρ 16) (bρ 16) x := by
  unfold Uρ
  simp only [Finset.sum_Icc_succ_top (show 1 ≤ 16 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 15 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 14 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 13 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 12 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 11 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 10 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 9 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 8 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 7 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 6 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 5 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 4 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 3 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 2 by norm_num), Finset.Icc_self, Finset.sum_singleton]

/-- The same expansion of `Uρmid`. -/
lemma Uρmid_expand :
    Uρmid =
      cρ 1 * Real.log ((bρ 1 - aρ 1) / 4) + cρ 2 * Real.log ((bρ 2 - aρ 2) / 4) +
                                  cρ 3 * Real.log ((bρ 3 - aρ 3) / 4) +
                                cρ 4 * Real.log ((bρ 4 - aρ 4) / 4) +
                              cρ 5 * Real.log ((bρ 5 - aρ 5) / 4) +
                            cρ 6 * Real.log ((bρ 6 - aρ 6) / 4) +
                          cρ 7 * Real.log ((bρ 7 - aρ 7) / 4) +
                        cρ 8 * Real.log ((bρ 8 - aρ 8) / 4) +
                      cρ 9 * Real.log ((bρ 9 - aρ 9) / 4) +
                    cρ 10 * Real.log ((bρ 10 - aρ 10) / 4) +
                  cρ 11 * Real.log ((bρ 11 - aρ 11) / 4) +
                cρ 12 * Real.log ((bρ 12 - aρ 12) / 4) +
              cρ 13 * Real.log ((bρ 13 - aρ 13) / 4) +
            cρ 14 * Real.log ((bρ 14 - aρ 14) / 4) +
          cρ 15 * Real.log ((bρ 15 - aρ 15) / 4) +
        cρ 16 * Real.log ((bρ 16 - aρ 16) / 4) := by
  unfold Uρmid
  simp only [Finset.sum_Icc_succ_top (show 1 ≤ 16 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 15 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 14 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 13 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 12 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 11 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 10 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 9 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 8 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 7 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 6 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 5 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 4 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 3 by norm_num),
    Finset.sum_Icc_succ_top (show 1 ≤ 2 by norm_num), Finset.Icc_self, Finset.sum_singleton]

/-! ### Binary range reduction for logarithms -/

lemma log_le_of_split_pos {r r' U : ℝ} (k : ℕ) (hr : r = 2 ^ k * r') (hr' : 0 < r')
    (hU : Real.log r' ≤ U) : Real.log r ≤ k * Real.log 2 + U := by
  rw [hr, Real.log_mul (by positivity) hr'.ne', Real.log_pow]
  linarith

lemma log_ge_of_split_pos {r r' L : ℝ} (k : ℕ) (hr : r = 2 ^ k * r') (hr' : 0 < r')
    (hL : L ≤ Real.log r') : k * Real.log 2 + L ≤ Real.log r := by
  rw [hr, Real.log_mul (by positivity) hr'.ne', Real.log_pow]
  linarith

lemma log_le_of_split_neg {r r' U : ℝ} (k : ℕ) (hr : r = r' / 2 ^ k) (hr' : 0 < r')
    (hU : Real.log r' ≤ U) : Real.log r ≤ U - k * Real.log 2 := by
  rw [hr, Real.log_div hr'.ne' (by positivity), Real.log_pow]
  linarith

lemma log_ge_of_split_neg {r r' L : ℝ} (k : ℕ) (hr : r = r' / 2 ^ k) (hr' : 0 < r')
    (hL : L ≤ Real.log r') : L - k * Real.log 2 ≤ Real.log r := by
  rw [hr, Real.log_div hr'.ne' (by positivity), Real.log_pow]
  linarith

end Zeta5Irrational
