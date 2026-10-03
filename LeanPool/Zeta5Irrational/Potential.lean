/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Measure
public import LeanPool.Zeta5Irrational.Energy
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import LeanPool.Zeta5Irrational.Certificates
import LeanPool.Zeta5Irrational.PotentialV
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic

/-! # The potential of the comparison measure `ρ` (closed form) and the field `V`

* `Uω a b t` : the closed form (A.1) of the logarithmic potential of the arcsine measure on
  `[a, b]`;
* `Uρ t = ∑ⱼ cⱼ Uω aⱼ bⱼ t` for the sixteen intervals of Table 1;
* monotonicity of `Uω` (nonincreasing left of `[a,b]`, constant on it, nondecreasing right of it);
* the derivative of `V`: `V'(t) = P(√t)/√t` with `P(y) = π + arctan(1/y) - 6 arctan(α/y)`.
-/

public section

open Filter Topology Set Finset

namespace Zeta5Irrational

/-- The closed form (A.1) of the potential of the arcsine measure on `[a, b]`. -/
@[expose] noncomputable def Uω (a b t : ℝ) : ℝ :=
  if a ≤ t ∧ t ≤ b then Real.log ((b - a) / 4)
  else Real.log ((|t - (a + b) / 2| + Real.sqrt ((t - a) * (t - b))) / 2)

/-- The potential of `ρ`. -/
@[expose] noncomputable def Uρ (t : ℝ) : ℝ :=
  ∑ j ∈ Icc 1 16, cρ j * Uω (aρ j) (bρ j) t

lemma Uω_of_mem {a b t : ℝ} (h1 : a ≤ t) (h2 : t ≤ b) : Uω a b t = Real.log ((b - a) / 4) := by
  simp [Uω, h1, h2]

lemma Uω_of_ge {a b t : ℝ} (hab : a < b) (h : b ≤ t) :
    Uω a b t = Real.log ((t - (a + b) / 2 + Real.sqrt ((t - a) * (t - b))) / 2) := by
  rcases eq_or_lt_of_le h with rfl | h'
  · rw [Uω_of_mem hab.le le_rfl]
    simp only [sub_self, mul_zero, Real.sqrt_zero, add_zero]
    congr 1; ring
  · have : ¬(a ≤ t ∧ t ≤ b) := fun hh => absurd hh.2 (not_le.mpr h')
    simp only [Uω, this, ite_false]
    rw [abs_of_nonneg (by linarith)]

lemma Uω_of_le {a b t : ℝ} (hab : a < b) (h : t ≤ a) :
    Uω a b t = Real.log (((a + b) / 2 - t + Real.sqrt ((t - a) * (t - b))) / 2) := by
  rcases eq_or_lt_of_le h with rfl | h'
  · rw [Uω_of_mem le_rfl hab.le]
    simp only [sub_self, zero_mul, Real.sqrt_zero, add_zero]
    congr 1; ring
  · have : ¬(a ≤ t ∧ t ≤ b) := fun hh => absurd hh.1 (not_le.mpr h')
    simp only [Uω, this, ite_false]
    rw [abs_of_nonpos (by linarith), neg_sub]

/-- `Uω a b` is nondecreasing on `[b, ∞)`. -/
lemma Uω_monotoneOn_Ici {a b : ℝ} (hab : a < b) : MonotoneOn (Uω a b) (Ici b) := by
  intro x hx y hy hxy
  have hx' : b ≤ x := hx
  have hy' : b ≤ y := hy
  rw [Uω_of_ge hab hx', Uω_of_ge hab hy']
  have h1 : Real.sqrt ((x - a) * (x - b)) ≤ Real.sqrt ((y - a) * (y - b)) :=
    Real.sqrt_le_sqrt (mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith))
  have hpos : 0 < (x - (a + b) / 2 + Real.sqrt ((x - a) * (x - b))) / 2 := by
    have := Real.sqrt_nonneg ((x - a) * (x - b)); linarith
  refine Real.log_le_log hpos ?_
  linarith

/-- `Uω a b` is nonincreasing on `(-∞, a]`. -/
lemma Uω_antitoneOn_Iic {a b : ℝ} (hab : a < b) : AntitoneOn (Uω a b) (Iic a) := by
  intro x hx y hy hxy
  have hx' : x ≤ a := hx
  have hy' : y ≤ a := hy
  rw [Uω_of_le hab hx', Uω_of_le hab hy']
  have h1 : Real.sqrt ((y - a) * (y - b)) ≤ Real.sqrt ((x - a) * (x - b)) := by
    refine Real.sqrt_le_sqrt ?_
    have e1 : (y - a) * (y - b) = (a - y) * (b - y) := by ring
    have e2 : (x - a) * (x - b) = (a - x) * (b - x) := by ring
    rw [e1, e2]
    exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have hpos : 0 < ((a + b) / 2 - y + Real.sqrt ((y - a) * (y - b))) / 2 := by
    have := Real.sqrt_nonneg ((y - a) * (y - b)); linarith
  refine Real.log_le_log hpos ?_
  linarith

/-! ### The derivative of `V` -/

/-- `P(y) = π + arctan (1/y) - 6 arctan (α/y)`. -/
@[expose] noncomputable def Pfun (y : ℝ) : ℝ :=
  Real.pi + Real.arctan (1 / y) - 6 * Real.arctan ((3 / 40) / y)

/-- The closed form of `V` as a function of `y = √t`: `Φ(y) = V(y²)`. -/
@[expose] noncomputable def Φ (y : ℝ) : ℝ :=
  Real.log (1 + y ^ 2) - 6 * (3 / 40) * Real.log (y ^ 2 + (3 / 40) ^ 2) - 2 + 12 * (3 / 40) +
    2 * y * Pfun y

lemma Vfield_eq_Φ {t : ℝ} (ht : 0 < t) : Vfield t = Φ (Real.sqrt t) := by
  rw [Vfield_eq ht]
  unfold Φ Pfun
  rw [Real.sq_sqrt ht.le]

lemma hasDerivAt_Φ {y : ℝ} (hy : 0 < y) : HasDerivAt Φ (2 * Pfun y) y := by
  have h1 := ((hasDerivAt_pow 2 y).const_add (1 : ℝ)).log (by positivity : (1 : ℝ) + y ^ 2 ≠ 0)
  have h2 :=
    (((hasDerivAt_pow 2 y).add_const ((3 / 40 : ℝ) ^ 2)).log (by positivity)).const_mul
      (6 * (3 / 40 : ℝ))
  have h3 := (hasDerivAt_inv hy.ne').arctan
  have h4 := ((hasDerivAt_inv hy.ne').const_mul (3 / 40 : ℝ)).arctan
  have hP0 := ((hasDerivAt_const y Real.pi).add h3).sub (h4.const_mul 6)
  have hP : HasDerivAt Pfun _ y :=
    hP0.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => by
        simp only [Pfun, Pi.add_apply, Pi.sub_apply, div_eq_mul_inv, one_mul])
  have h5 := ((hasDerivAt_id y).const_mul (2 : ℝ)).mul hP
  have h := (((h1.sub h2).sub_const (2 : ℝ)).add_const (12 * (3 / 40 : ℝ))).add h5
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)).congr_deriv ?_
  · simp only [Φ, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id]
    try ring
  · unfold Pfun
    have hne1 : (1 : ℝ) + y ^ 2 ≠ 0 := by positivity
    have hne2 : y ^ 2 + (3 / 40 : ℝ) ^ 2 ≠ 0 := by positivity
    simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one, id]
    field_simp
    ring

/-- `Uω a b` is nonincreasing on `(-∞, b]` (constant on `[a, b]`). -/
lemma Uω_antitoneOn_Iic' {a b : ℝ} (hab : a < b) : AntitoneOn (Uω a b) (Iic b) := by
  intro x hx y hy hxy
  have hx' : x ≤ b := hx
  have hy' : y ≤ b := hy
  by_cases hya : y ≤ a
  · exact
      Uω_antitoneOn_Iic hab (show x ∈ Iic a from (hxy.trans hya)) (show y ∈ Iic a from hya) hxy
  · push Not at hya
    rw [Uω_of_mem hya.le hy']
    by_cases hxa : x ≤ a
    · have := Uω_antitoneOn_Iic hab (show x ∈ Iic a from hxa) (Set.mem_Iic.mpr le_rfl) hxa
      rwa [Uω_of_mem le_rfl hab.le] at this
    · push Not at hxa
      rw [Uω_of_mem hxa.le hx']

/-- `Uω a b` is nondecreasing on `[a, ∞)` (constant on `[a, b]`). -/
lemma Uω_monotoneOn_Ici' {a b : ℝ} (hab : a < b) : MonotoneOn (Uω a b) (Ici a) := by
  intro x hx y hy hxy
  have hx' : a ≤ x := hx
  have hy' : a ≤ y := hy
  by_cases hxb : b ≤ x
  · exact Uω_monotoneOn_Ici hab (show x ∈ Ici b from hxb) (show y ∈ Ici b from hxb.trans hxy) hxy
  · push Not at hxb
    rw [Uω_of_mem hx' hxb.le]
    by_cases hyb : b ≤ y
    · have := Uω_monotoneOn_Ici hab (Set.mem_Ici.mpr le_rfl) (show y ∈ Ici b from hyb) hyb
      rwa [Uω_of_mem hab.le le_rfl] at this
    · push Not at hyb
      rw [Uω_of_mem hy' hyb.le]

/-! ### Facts about Table 1 -/

lemma aρ_lt_bρ : ∀ j ∈ Finset.Icc 1 16, aρ j < bρ j := by
  intro j hj
  rw [Finset.mem_Icc] at hj
  obtain ⟨hj1, hj2⟩ := hj
  interval_cases j <;> norm_num [aρ, bρ, table1]

lemma cρ_pos : ∀ j ∈ Finset.Icc 1 16, 0 < cρ j := by
  intro j hj
  rw [Finset.mem_Icc] at hj
  obtain ⟨hj1, hj2⟩ := hj
  interval_cases j <;> norm_num [cρ, table1]

lemma aρ_one_le_bρ : ∀ j ∈ Finset.Icc 1 16, aρ 1 ≤ bρ j := by
  intro j hj
  rw [Finset.mem_Icc] at hj
  obtain ⟨hj1, hj2⟩ := hj
  interval_cases j <;> norm_num [aρ, bρ, table1]

lemma aρ_le_bρ_one : ∀ j ∈ Finset.Icc 1 16, aρ j ≤ bρ 1 := by
  intro j hj
  rw [Finset.mem_Icc] at hj
  obtain ⟨hj1, hj2⟩ := hj
  interval_cases j <;> norm_num [aρ, bρ, table1]

lemma aρ_le_aρ_one : ∀ j ∈ Finset.Icc 1 16, aρ j ≤ aρ 1 := by
  intro j hj
  rw [Finset.mem_Icc] at hj
  obtain ⟨hj1, hj2⟩ := hj
  interval_cases j <;> norm_num [aρ, bρ, table1]

lemma bρ_one_le_bρ : ∀ j ∈ Finset.Icc 1 16, bρ 1 ≤ bρ j := by
  intro j hj
  rw [Finset.mem_Icc] at hj
  obtain ⟨hj1, hj2⟩ := hj
  interval_cases j <;> norm_num [aρ, bρ, table1]

/-- `Uρ` is nonincreasing on `(-∞, a₁]`. -/
lemma Uρ_antitoneOn : AntitoneOn Uρ (Iic (aρ 1)) := by
  intro x hx y hy hxy
  unfold Uρ
  refine Finset.sum_le_sum fun j hj => ?_
  refine mul_le_mul_of_nonneg_left ?_ (cρ_pos j hj).le
  exact
    Uω_antitoneOn_Iic' (aρ_lt_bρ j hj)
      (show x ∈ Iic (bρ j) from (show x ≤ aρ 1 from hx).trans (aρ_one_le_bρ j hj))
      (show y ∈ Iic (bρ j) from (show y ≤ aρ 1 from hy).trans (aρ_one_le_bρ j hj)) hxy

/-- `Uρ` is nondecreasing on `[b₁, ∞)`. -/
lemma Uρ_monotoneOn : MonotoneOn Uρ (Ici (bρ 1)) := by
  intro x hx y hy hxy
  unfold Uρ
  refine Finset.sum_le_sum fun j hj => ?_
  refine mul_le_mul_of_nonneg_left ?_ (cρ_pos j hj).le
  exact
    Uω_monotoneOn_Ici' (aρ_lt_bρ j hj) (show x ∈ Ici (aρ j) from (aρ_le_bρ_one j hj).trans hx)
      (show y ∈ Ici (aρ j) from (aρ_le_bρ_one j hj).trans hy) hxy

/-- `Uρ` is constant on `[a₁, b₁]`. -/
lemma Uρ_of_mem {t : ℝ} (h1 : aρ 1 ≤ t) (h2 : t ≤ bρ 1) :
    Uρ t = ∑ j ∈ Icc 1 16, cρ j * Real.log ((bρ j - aρ j) / 4) := by
  unfold Uρ
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Uω_of_mem ((aρ_le_aρ_one j hj).trans h1) (h2.trans (bρ_one_le_bρ j hj))]

/-! ### Monotonicity of `P` and unimodality of `Φ` -/

lemma hasDerivAt_Pfun {y : ℝ} (hy : 0 < y) :
    HasDerivAt Pfun (-1 / (y ^ 2 + 1) + 6 * (3 / 40) / (y ^ 2 + (3 / 40) ^ 2)) y := by
  have h3 := (hasDerivAt_inv hy.ne').arctan
  have h4 := ((hasDerivAt_inv hy.ne').const_mul (3 / 40 : ℝ)).arctan
  have hP0 := ((hasDerivAt_const y Real.pi).add h3).sub (h4.const_mul 6)
  refine
    (hP0.congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun x => by
            simp only [Pfun, Pi.add_apply, Pi.sub_apply, div_eq_mul_inv, one_mul])).congr_deriv
      ?_
  have hne1 : y ^ 2 + (1 : ℝ) ≠ 0 := by positivity
  have hne2 : y ^ 2 + (3 / 40 : ℝ) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The turning point `y₀² = 711/880` of `P`. -/
noncomputable abbrev y0 : ℝ :=
  Real.sqrt (711 / 880)

lemma deriv_Pfun_nonneg {y : ℝ} (hy : 0 < y) (hy0 : y ≤ y0) :
    0 ≤ -1 / (y ^ 2 + 1) + 6 * (3 / 40) / (y ^ 2 + (3 / 40) ^ 2) := by
  have hy2 : y ^ 2 ≤ 711 / 880 := by
    have := Real.sqrt_le_sqrt (le_of_eq (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 711 / 880)).symm)
    calc
      y ^ 2 ≤ y0 ^ 2 := pow_le_pow_left₀ hy.le hy0 2
      _ = 711 / 880 := Real.sq_sqrt (by norm_num)
  rw [div_add_div _ _ (by positivity) (by positivity)]
  refine div_nonneg ?_ (by positivity)
  nlinarith

lemma deriv_Pfun_nonpos {y : ℝ} (hy0 : y0 ≤ y) :
    -1 / (y ^ 2 + 1) + 6 * (3 / 40) / (y ^ 2 + (3 / 40) ^ 2) ≤ 0 := by
  have hy2 : 711 / 880 ≤ y ^ 2 := by
    calc
      (711 / 880 : ℝ) = y0 ^ 2 := (Real.sq_sqrt (by norm_num)).symm
      _ ≤ y ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hy0 2
  rw [div_add_div _ _ (by positivity) (by positivity)]
  refine div_nonpos_of_nonpos_of_nonneg ?_ (by positivity)
  nlinarith

lemma Pfun_monotoneOn : MonotoneOn Pfun (Ioc 0 y0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioc 0 y0) ?_ ?_ ?_
  · intro y hy; exact (hasDerivAt_Pfun hy.1).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioc] at hy
    exact (hasDerivAt_Pfun hy.1).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Ioc] at hy
    rw [(hasDerivAt_Pfun hy.1).deriv]
    exact deriv_Pfun_nonneg hy.1 hy.2.le

lemma Pfun_antitoneOn : AntitoneOn Pfun (Ici y0) := by
  have hy0 : 0 < y0 := Real.sqrt_pos.mpr (by norm_num)
  refine antitoneOn_of_deriv_nonpos (convex_Ici y0) ?_ ?_ ?_
  · intro y hy; exact (hasDerivAt_Pfun (hy0.trans_le hy)).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ici] at hy
    exact (hasDerivAt_Pfun (hy0.trans hy)).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Ici] at hy
    rw [(hasDerivAt_Pfun (hy0.trans hy)).deriv]
    exact deriv_Pfun_nonpos (le_of_lt hy)

lemma arctan_le_self' {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  rcases hx.lt_or_eq with h | h
  · have ht : 0 < Real.arctan x := Real.arctan_pos.mpr h
    have := Real.lt_tan ht (Real.arctan_lt_pi_div_two x)
    rw [Real.tan_arctan] at this
    exact this.le
  · rw [← h, Real.arctan_zero]

lemma Pfun_pos_of_one_le {y : ℝ} (hy : 1 ≤ y) : 0 < Pfun y := by
  unfold Pfun
  have h1 : 0 ≤ Real.arctan (1 / y) := Real.arctan_nonneg.mpr (by positivity)
  have h2 : Real.arctan ((3 / 40) / y) ≤ (3 / 40) / y := arctan_le_self' (by positivity)
  have h3 : (3 / 40 : ℝ) / y ≤ 3 / 40 := by rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith [Real.pi_gt_three]

lemma Pfun_one_pos : 0 < Pfun 1 :=
  Pfun_pos_of_one_le le_rfl

/-- The bracket `[q₋, q₊]` of the paper (Appendix A.3). -/
noncomputable abbrev qm : ℝ :=
  59205077 / 10 ^ 10

/-- Upper rational endpoint of the bracket around the minimum of the external field. -/
noncomputable abbrev qp : ℝ :=
  59205079 / 10 ^ 10

lemma sqrt_qm_le_y0 : Real.sqrt qm ≤ y0 :=
  Real.sqrt_le_sqrt (by norm_num)

lemma sqrt_qp_le_y0 : Real.sqrt qp ≤ y0 :=
  Real.sqrt_le_sqrt (by norm_num)

lemma sqrt_qm_pos : 0 < Real.sqrt qm :=
  Real.sqrt_pos.mpr (by norm_num)

lemma sqrt_qp_pos : 0 < Real.sqrt qp :=
  Real.sqrt_pos.mpr (by norm_num)

/-- Numerical fact: `P(√q₋) < 0` (certified). -/
lemma Pfun_sqrt_qm_neg : Pfun (Real.sqrt qm) < 0 := by
  set s := Real.sqrt qm with hs
  have hs_pos : 0 < s := sqrt_qm_pos
  have hs_lo : (7694483543421 / 100000000000000 : ℝ) ≤ s :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi : s ≤ (60113152683 / 781250000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have h1 : Real.arctan (1 / s) = Real.pi / 2 - Real.arctan s := by
    rw [one_div, Real.arctan_inv_of_pos hs_pos]
  have hS2 :
    (76793521753675120919939711999 / 1000000000000000000000000000000 : ℝ) ≤
      ∑ i ∈ Finset.range (2 * 8),
        (-1 : ℝ) ^ i *
          ((7694483543421 / 100000000000000 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) :=
    by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have h2 :
    (76793521753675120919939711999 / 1000000000000000000000000000000 : ℝ) ≤ Real.arctan s :=
    hS2.trans
      ((arctan_ge_partial (by norm_num) (by norm_num) 8).trans
        (Real.arctan_strictMono.monotone hs_lo))
  have h3 :
    Real.arctan ((3 / 40) / (60113152683 / 781250000000 : ℝ)) ≤ Real.arctan ((3 / 40) / s) :=
    Real.arctan_strictMono.monotone (div_le_div_of_nonneg_left (by norm_num) hs_pos hs_hi)
  have h4 :
    Real.arctan ((3 / 40) / (60113152683 / 781250000000 : ℝ)) =
      2 *
        Real.arctan
          (((3 / 40) / (60113152683 / 781250000000 : ℝ)) /
            (1 + Real.sqrt (1 + ((3 / 40) / (60113152683 / 781250000000 : ℝ)) ^ 2))) :=
    arctan_eq_two_mul_arctan (by norm_num)
  have h5 :
    (1953125000000000000000000 / 4801949469571619658211011 : ℝ) ≤
      ((3 / 40) / (60113152683 / 781250000000 : ℝ)) /
        (1 + Real.sqrt (1 + ((3 / 40) / (60113152683 / 781250000000 : ℝ)) ^ 2)) := by
    have hsq :
      Real.sqrt (1 + ((3 / 40) / (60113152683 / 781250000000 : ℝ)) ^ 2) ≤
        (139645531231451 / 100000000000000 : ℝ) :=
      sqrt_le_of_sq_le (by norm_num) (by norm_num)
    rw [show
        (1953125000000000000000000 / 4801949469571619658211011 : ℝ) =
          ((3 / 40) / (60113152683 / 781250000000 : ℝ)) /
            (1 + (139645531231451 / 100000000000000 : ℝ))
        by norm_num]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have hS6 :
    (77259924705678505221464494407 / 200000000000000000000000000000 : ℝ) ≤
      ∑ i ∈ Finset.range (2 * 14),
        (-1 : ℝ) ^ i *
          ((1953125000000000000000000 / 4801949469571619658211011 : ℝ) ^ (2 * i + 1) /
            (2 * (i : ℝ) + 1)) :=
    by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have h6 :
    (77259924705678505221464494407 / 200000000000000000000000000000 : ℝ) ≤
      Real.arctan
        (((3 / 40) / (60113152683 / 781250000000 : ℝ)) /
          (1 + Real.sqrt (1 + ((3 / 40) / (60113152683 / 781250000000 : ℝ)) ^ 2))) :=
    hS6.trans
      ((arctan_ge_partial (by norm_num) (by norm_num) 14).trans
        (Real.arctan_strictMono.monotone h5))
  have hpi := Real.pi_lt_d20
  unfold Pfun
  rw [h1]
  linarith

/-- Numerical fact: `0 < P(√q₊)` (certified). -/
lemma Pfun_sqrt_qp_pos : 0 < Pfun (Real.sqrt qp) := by
  set s := Real.sqrt qp with hs
  have hs_pos : 0 < s := sqrt_qp_pos
  have hs_lo : (961810459173 / 12500000000000 : ℝ) ≤ s :=
    le_sqrt_of_sq_le (by norm_num) (by norm_num)
  have hs_hi : s ≤ (7694483673387 / 100000000000000 : ℝ) :=
    sqrt_le_of_sq_le (by norm_num) (by norm_num)
  have h1 : Real.arctan (1 / s) = Real.pi / 2 - Real.arctan s := by
    rw [one_div, Real.arctan_inv_of_pos hs_pos]
  have hS2 :
    ∑ i ∈ Finset.range (2 * 8 + 1),
        (-1 : ℝ) ^ i * ((7694483673387 / 100000000000000 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) ≤
      (76793523045685761842673943627 / 1000000000000000000000000000000 : ℝ) :=
    by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have h2 :
    Real.arctan s ≤ (76793523045685761842673943627 / 1000000000000000000000000000000 : ℝ) :=
    ((Real.arctan_strictMono.monotone hs_hi).trans
          (arctan_le_partial (by norm_num) (by norm_num) 8)).trans
      hS2
  have h3 :
    Real.arctan ((3 / 40) / s) ≤ Real.arctan ((3 / 40) / (961810459173 / 12500000000000 : ℝ)) :=
    Real.arctan_strictMono.monotone (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs_lo)
  have h4 :
    Real.arctan ((3 / 40) / (961810459173 / 12500000000000 : ℝ)) =
      2 *
        Real.arctan
          (((3 / 40) / (961810459173 / 12500000000000 : ℝ)) /
            (1 + Real.sqrt (1 + ((3 / 40) / (961810459173 / 12500000000000 : ℝ)) ^ 2))) :=
    arctan_eq_two_mul_arctan (by norm_num)
  have h5 :
    ((3 / 40) / (961810459173 / 12500000000000 : ℝ)) /
        (1 + Real.sqrt (1 + ((3 / 40) / (961810459173 / 12500000000000 : ℝ)) ^ 2)) ≤
      (7812500000000000000000000 / 19207798110603085910913171 : ℝ) := by
    have hsq :
      (34911382520581 / 25000000000000 : ℝ) ≤
        Real.sqrt (1 + ((3 / 40) / (961810459173 / 12500000000000 : ℝ)) ^ 2) :=
      le_sqrt_of_sq_le (by norm_num) (by norm_num)
    rw [show
        (7812500000000000000000000 / 19207798110603085910913171 : ℝ) =
          ((3 / 40) / (961810459173 / 12500000000000 : ℝ)) /
            (1 + (34911382520581 / 25000000000000 : ℝ))
        by norm_num]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hS6 :
    ∑ i ∈ Finset.range (2 * 14 + 1),
        (-1 : ℝ) ^ i *
          ((7812500000000000000000000 / 19207798110603085910913171 : ℝ) ^ (2 * i + 1) /
            (2 * (i : ℝ) + 1)) ≤
      (193149809653637591795814749669 / 500000000000000000000000000000 : ℝ) :=
    by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  have h6 :
    Real.arctan
        (((3 / 40) / (961810459173 / 12500000000000 : ℝ)) /
          (1 + Real.sqrt (1 + ((3 / 40) / (961810459173 / 12500000000000 : ℝ)) ^ 2))) ≤
      (193149809653637591795814749669 / 500000000000000000000000000000 : ℝ) :=
    ((Real.arctan_strictMono.monotone h5).trans
          (arctan_le_partial (by norm_num) (by norm_num) 14)).trans
      hS6
  have hpi := Real.pi_gt_d20
  unfold Pfun
  rw [h1]
  linarith

/-- `P ≤ 0` on `(0, √q₋]`. -/
lemma Pfun_nonpos {y : ℝ} (hy : 0 < y) (hy' : y ≤ Real.sqrt qm) : Pfun y ≤ 0 :=
  (Pfun_monotoneOn ⟨hy, hy'.trans sqrt_qm_le_y0⟩ ⟨sqrt_qm_pos, sqrt_qm_le_y0⟩ hy').trans
    Pfun_sqrt_qm_neg.le

/-- `0 ≤ P` on `[√q₊, ∞)`. -/
lemma Pfun_nonneg {y : ℝ} (hy : Real.sqrt qp ≤ y) : 0 ≤ Pfun y := by
  rcases le_or_gt y y0 with h | h
  · exact
      Pfun_sqrt_qp_pos.le.trans
        (Pfun_monotoneOn ⟨sqrt_qp_pos, sqrt_qp_le_y0⟩ ⟨sqrt_qp_pos.trans_le hy, h⟩ hy)
  · rcases le_or_gt y 1 with h1 | h1
    · have hy0 : y0 ≤ 1 := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp];
        exact Real.sqrt_le_sqrt (by norm_num)
      exact
        Pfun_one_pos.le.trans
          (Pfun_antitoneOn (show y ∈ Ici y0 from h.le) (show (1 : ℝ) ∈ Ici y0 from hy0) h1)
    · exact (Pfun_pos_of_one_le h1.le).le

/-- `Φ` is nonincreasing on `(0, √q₋]`. -/
lemma Φ_antitoneOn : AntitoneOn Φ (Ioc 0 (Real.sqrt qm)) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ioc _ _) ?_ ?_ ?_
  · intro y hy; exact (hasDerivAt_Φ hy.1).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioc] at hy
    exact (hasDerivAt_Φ hy.1).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Ioc] at hy
    rw [(hasDerivAt_Φ hy.1).deriv]
    linarith [Pfun_nonpos hy.1 hy.2.le]

/-- `Φ` is nondecreasing on `[√q₊, ∞)`. -/
lemma Φ_monotoneOn : MonotoneOn Φ (Ici (Real.sqrt qp)) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici _) ?_ ?_ ?_
  · intro y hy; exact (hasDerivAt_Φ (sqrt_qp_pos.trans_le hy)).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ici] at hy
    exact (hasDerivAt_Φ (sqrt_qp_pos.trans hy)).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Ici] at hy
    rw [(hasDerivAt_Φ (sqrt_qp_pos.trans hy)).deriv]
    linarith [Pfun_nonneg hy.le]

/-- `V` is nonincreasing on `(0, q₋]`. -/
lemma Vfield_antitoneOn : AntitoneOn Vfield (Ioc 0 qm) := by
  intro x hx y hy hxy
  rw [Vfield_eq_Φ hx.1, Vfield_eq_Φ hy.1]
  exact
    Φ_antitoneOn ⟨Real.sqrt_pos.mpr hx.1, Real.sqrt_le_sqrt hx.2⟩
      ⟨Real.sqrt_pos.mpr hy.1, Real.sqrt_le_sqrt hy.2⟩ (Real.sqrt_le_sqrt hxy)

/-- `V` is nondecreasing on `[q₊, ∞)`. -/
lemma Vfield_monotoneOn : MonotoneOn Vfield (Ici qp) := by
  intro x hx y hy hxy
  have hqp : (0 : ℝ) < qp := by norm_num
  rw [Vfield_eq_Φ (hqp.trans_le hx), Vfield_eq_Φ (hqp.trans_le hy)]
  exact Φ_monotoneOn (Real.sqrt_le_sqrt hx) (Real.sqrt_le_sqrt hy) (Real.sqrt_le_sqrt hxy)

end Zeta5Irrational
