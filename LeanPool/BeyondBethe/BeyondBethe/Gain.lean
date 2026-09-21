/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.Capacity
import LeanPool.BeyondBethe.BeyondBethe.Transfer
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

/-! # Gain -/

open scoped BigOperators

namespace BeyondBethe

/-- The row factor `ζ_i` from paper (47). -/
noncomputable def rowZeta
    {ι : Type*} [Fintype ι] (τ : ℝ) (p : ι → ℝ) : ℝ :=
  ∏ j, (p j) ^ (τ * p j)

theorem rowZeta_pos
    {ι : Type*} [Fintype ι]
    {τ : ℝ} {p : ι → ℝ} (hp : ∀ j, 0 < p j) :
    0 < rowZeta τ p := by
  rw [rowZeta]
  exact Finset.prod_pos fun j _ ↦ Real.rpow_pos_of_pos (hp j) _

theorem rowZeta_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {τ : ℝ} (hτ : 0 ≤ τ) {p : ι → ℝ}
    (hp : IsProbabilityVector p) :
    rowZeta τ p ≤ 1 := by
  rw [rowZeta]
  apply Finset.prod_le_one
  · intro j _
    exact Real.rpow_nonneg (hp.nonnegative j) _
  · intro j _
    exact Real.rpow_le_one (hp.nonnegative j) (hp.le_one j)
      (mul_nonneg hτ (hp.nonnegative j))

noncomputable def outsideMassTwo
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (a b : ι) : ℝ :=
  ∑ j ∈ (Finset.univ.erase a).erase b, p j

theorem outsideMassTwo_comm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (a b : ι) :
    outsideMassTwo p a b = outsideMassTwo p b a := by
  rw [outsideMassTwo, outsideMassTwo]
  congr 1
  ext j
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  tauto

theorem twoCore_add_outsideMassTwo
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℝ} (hp : IsProbabilityVector p)
    {a b : ι} (hab : a ≠ b) :
    p a + p b + outsideMassTwo p a b = 1 := by
  have ha : a ∈ (Finset.univ : Finset ι) := Finset.mem_univ a
  have hb : b ∈ (Finset.univ.erase a) := by simp [hab.symm]
  have htotal := hp.sum_eq_one
  rw [← Finset.sum_erase_add _ _ ha] at htotal
  rw [← Finset.sum_erase_add _ _ hb] at htotal
  rw [outsideMassTwo]
  linarith

theorem twoCore_add_outsideMassTwo_eq_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) {a b : ι} (hab : a ≠ b) :
    p a + p b + outsideMassTwo p a b = ∑ j, p j := by
  have ha : a ∈ (Finset.univ : Finset ι) := Finset.mem_univ a
  have hb : b ∈ (Finset.univ.erase a) := by simp [hab.symm]
  rw [← Finset.sum_erase_add _ _ ha, ← Finset.sum_erase_add _ _ hb,
    outsideMassTwo]
  ring

theorem outsideMassTwo_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℝ} (hp : IsProbabilityVector p) (a b : ι) :
    0 ≤ outsideMassTwo p a b := by
  rw [outsideMassTwo]
  exact Finset.sum_nonneg fun j _ ↦ hp.nonnegative j

theorem productExcept_eq_twoCore
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) {a b : ι} (hab : a ≠ b) :
    productExcept p a = (1 - p b) *
      ∏ j ∈ (Finset.univ.erase a).erase b, (1 - p j) := by
  rw [productExcept]
  exact (Finset.mul_prod_erase (Finset.univ.erase a) (fun j ↦ 1 - p j)
    (by simp [hab.symm])).symm

/-- The two upper bounds (45)--(46) used in the leakage argument. -/
theorem transferU_le_twoCore_ratio
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {τ : ℝ} (hτ : 0 ≤ τ) {p : ι → ℝ}
    (hp : IsInteriorProbabilityVector p) {a b : ι} (hab : a ≠ b) :
    transferU τ p a ≤
      p a / (p a + outsideMassTwo p a b * p b) := by
  let s : Finset ι := (Finset.univ.erase a).erase b
  let t := outsideMassTwo p a b
  have ht : 0 ≤ t := outsideMassTwo_nonneg hp.1 a b
  have hsum := twoCore_add_outsideMassTwo hp.1 hab
  have houtsideSum : ∑ j ∈ s, p j = t := rfl
  have hprodOutside : 1 - t ≤ ∏ j ∈ s, (1 - p j) := by
    apply one_sub_sum_le_prod_one_sub s p
    · intro j _
      exact hp.1.nonnegative j
    · rw [houtsideSum]
      linarith [hp.1.nonnegative a, hp.1.nonnegative b]
  have hbcomp : 0 < 1 - p b := sub_pos.mpr (hp.2 b).2
  have hdenIdentity :
      (1 - p b) * (1 - t) = p a + t * p b := by
    linarith
  have hdenLower : p a + t * p b ≤ productExcept p a := by
    rw [productExcept_eq_twoCore p hab, ← hdenIdentity]
    exact mul_le_mul_of_nonneg_left hprodOutside hbcomp.le
  have hdenPos : 0 < p a + t * p b :=
    add_pos_of_pos_of_nonneg (hp.2 a).1 (mul_nonneg ht (hp.1.nonnegative b))
  have hnum : (p a) ^ (1 + τ) ≤ p a := by
    have h := Real.rpow_le_rpow_of_exponent_ge'
      (hp.1.nonnegative a) (hp.2 a).2.le (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith : (1 : ℝ) ≤ 1 + τ)
    simpa using h
  rw [transferU]
  exact div_le_div₀ (hp.1.nonnegative a) hnum hdenPos hdenLower

/-- Scalar form of the leakage argument in paper (49)--(51). -/
theorem leakage_le_inv_sub_one
    {u xa xb t Ua Ub : ℝ}
    (hu : 0 < u) (hu1 : u ≤ 1)
    (hxa : 0 < xa) (hxb : 0 < xb) (ht : 0 ≤ t)
    (hUa : u ≤ Ua) (hUb : u ≤ Ub)
    (hUaUpper : Ua ≤ xa / (xa + t * xb))
    (hUbUpper : Ub ≤ xb / (xb + t * xa)) :
    t ≤ u⁻¹ - 1 := by
  have hdena : 0 < xa + t * xb := add_pos_of_pos_of_nonneg hxa (mul_nonneg ht hxb.le)
  have hdenb : 0 < xb + t * xa := add_pos_of_pos_of_nonneg hxb (mul_nonneg ht hxa.le)
  have ha := (hUa.trans hUaUpper)
  have hb := (hUb.trans hUbUpper)
  rw [le_div_iff₀ hdena] at ha
  rw [le_div_iff₀ hdenb] at hb
  have ha' : u * t * xb ≤ (1 - u) * xa := by nlinarith
  have hb' : u * t * xa ≤ (1 - u) * xb := by nlinarith
  have hleft0 : 0 ≤ u * t * xb := by positivity
  have hright0 : 0 ≤ (1 - u) * xa :=
    mul_nonneg (sub_nonneg.mpr hu1) hxa.le
  have hmul := mul_le_mul ha' hb' (by positivity) hright0
  have hsq : (u * t) ^ 2 ≤ (1 - u) ^ 2 := by
    have hxy : 0 < xa * xb := mul_pos hxa hxb
    apply le_of_mul_le_mul_right _ hxy
    calc
      (u * t) ^ 2 * (xa * xb) =
          (u * t * xb) * (u * t * xa) := by ring
      _ ≤ ((1 - u) * xa) * ((1 - u) * xb) := hmul
      _ = (1 - u) ^ 2 * (xa * xb) := by ring
  have hut : 0 ≤ u * t := mul_nonneg hu.le ht
  have hone : 0 ≤ 1 - u := sub_nonneg.mpr hu1
  have hutle : u * t ≤ 1 - u := by nlinarith
  calc
    t ≤ (1 - u) / u := (le_div_iff₀ hu).2 (by simpa [mul_comm] using hutle)
    _ = u⁻¹ - 1 := by field_simp

/-- Paper (47): two large core transfer coordinates force small mass outside
the two core columns. -/
theorem outsideMassTwo_le_inv_sub_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {τ u : ℝ} (hτ : 0 ≤ τ) (hu : 0 < u) (hu1 : u ≤ 1)
    {p : ι → ℝ} (hp : IsInteriorProbabilityVector p)
    {a b : ι} (hab : a ≠ b)
    (hUa : u ≤ transferU τ p a) (hUb : u ≤ transferU τ p b) :
    outsideMassTwo p a b ≤ u⁻¹ - 1 := by
  apply leakage_le_inv_sub_one hu hu1 (hp.2 a).1 (hp.2 b).1
    (outsideMassTwo_nonneg hp.1 a b) hUa hUb
  · exact transferU_le_twoCore_ratio hτ hp hab
  · have h := transferU_le_twoCore_ratio hτ hp hab.symm
    rw [outsideMassTwo_comm p b a] at h
    simpa [mul_comm] using h

theorem log_one_div_nonneg_of_pos_le_one
    {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    0 ≤ Real.log (1 / u) := by
  apply Real.log_nonneg
  exact (le_div_iff₀ hu).2 (by simpa using hu1)

theorem exp_neg_le_of_log_one_div_le
    {u κ : ℝ} (hu : 0 < u)
    (hcost : Real.log (1 / u) ≤ κ) :
    Real.exp (-κ) ≤ u := by
  have hlog : -κ ≤ Real.log u := by
    rw [one_div, Real.log_inv] at hcost
    linarith
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hu] at hexp
  exact hexp

noncomputable def fourCoreTransferCost
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ℝ) (X : Matrix ι ι ℝ) (r s a b : ι) : ℝ :=
  Real.log (1 / transferU τ (X r) a) +
    Real.log (1 / transferU τ (X r) b) +
    Real.log (1 / transferU τ (X s) a) +
    Real.log (1 / transferU τ (X s) b)

theorem fourCoreTransfer_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {τ κ : ℝ} (hτ : 0 ≤ τ)
    {X : Matrix ι ι ℝ} (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    {r s a b : ι}
    (hcost : fourCoreTransferCost τ X r s a b ≤ κ) :
    Real.exp (-κ) ≤ transferU τ (X r) a ∧
      Real.exp (-κ) ≤ transferU τ (X r) b ∧
      Real.exp (-κ) ≤ transferU τ (X s) a ∧
      Real.exp (-κ) ≤ transferU τ (X s) b := by
  have hpos : ∀ i j, 0 < transferU τ (X i) j :=
    fun i j ↦ transferU_pos (hXint i) j
  have hle : ∀ i j, transferU τ (X i) j ≤ 1 :=
    fun i j ↦ transferU_le_one hτ (hXint i) j
  have hnonneg : ∀ i j,
      0 ≤ Real.log (1 / transferU τ (X i) j) :=
    fun i j ↦ log_one_div_nonneg_of_pos_le_one (hpos i j) (hle i j)
  rw [fourCoreTransferCost] at hcost
  constructor
  · apply exp_neg_le_of_log_one_div_le (hpos r a)
    linarith [hnonneg r b, hnonneg s a, hnonneg s b]
  constructor
  · apply exp_neg_le_of_log_one_div_le (hpos r b)
    linarith [hnonneg r a, hnonneg s a, hnonneg s b]
  constructor
  · apply exp_neg_le_of_log_one_div_le (hpos s a)
    linarith [hnonneg r a, hnonneg r b, hnonneg s b]
  · apply exp_neg_le_of_log_one_div_le (hpos s b)
    linarith [hnonneg r a, hnonneg r b, hnonneg s a]

theorem outsideMassTwo_pairAlpha
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι ℝ) (r s a b : ι) :
    outsideMassTwo (pairAlpha X r s) a b =
      outsideMassTwo (X r) a b + outsideMassTwo (X s) a b := by
  rw [outsideMassTwo, outsideMassTwo, outsideMassTwo]
  simp_rw [pairAlpha, Finset.sum_add_distrib]

/-- Paper (48): a small four-entry transfer cost forces small two-row
leakage. -/
theorem pairOutsideMass_le_exp
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {τ κ : ℝ} (hτ : 0 ≤ τ) (hκ : 0 ≤ κ)
    {X : Matrix ι ι ℝ} (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    {r s a b : ι} (hab : a ≠ b)
    (hcost : fourCoreTransferCost τ X r s a b ≤ κ) :
    outsideMassTwo (pairAlpha X r s) a b ≤
      2 * (Real.exp κ - 1) := by
  have hcore := fourCoreTransfer_lower hτ hXint hcost
  have hu : 0 < Real.exp (-κ) := Real.exp_pos _
  have hu1 : Real.exp (-κ) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hr := outsideMassTwo_le_inv_sub_one hτ hu hu1 (hXint r)
    hab hcore.1 hcore.2.1
  have hs := outsideMassTwo_le_inv_sub_one hτ hu hu1 (hXint s)
    hab hcore.2.2.1 hcore.2.2.2
  rw [outsideMassTwo_pairAlpha]
  rw [show (Real.exp (-κ))⁻¹ = Real.exp κ by
    rw [Real.exp_neg, inv_inv]] at hr hs
  linarith

theorem productExcept_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℝ} (hp : IsProbabilityVector p) (j : ι) :
    productExcept p j ≤ 1 := by
  rw [productExcept]
  apply Finset.prod_le_one
  · intro k _
    exact sub_nonneg.mpr (hp.le_one k)
  · intro k _
    linarith [hp.nonnegative k]

/-- The denominator in `U_ij` is at most one, giving the first inequality in
paper (56). -/
theorem coordinate_rpow_le_transferU
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {τ : ℝ} {p : ι → ℝ} (hp : IsInteriorProbabilityVector p) (j : ι) :
    (p j) ^ (1 + τ) ≤ transferU τ p j := by
  have hdenPos := productExcept_pos hp j
  rw [transferU, le_div_iff₀ hdenPos]
  exact mul_le_of_le_one_right (Real.rpow_nonneg (hp.1.nonnegative j) _)
    (productExcept_le_one hp.1 j)

/-- The three kinds of two-column sets used by the capacity witness in paper
(53): the core set, a set using `a` and an outside column, or a set using `b`
and an outside column. -/
abbrev CapacityWitnessEdge (ι : Type*) := Unit ⊕ (ι ⊕ ι)

noncomputable def capacityWitnessMass
    {ι : Type*} (ρ δa δb : ℝ) (α : ι → ℝ) :
    CapacityWitnessEdge ι → ℝ
  | Sum.inl _ => 1 - ρ
  | Sum.inr (Sum.inl l) => δb / ρ * α l
  | Sum.inr (Sum.inr l) => δa / ρ * α l

theorem capacityWitness_sum
    {ι : Type*} [Fintype ι]
    {ρ δa δb : ℝ} {α : ι → ℝ}
    (hρ : 0 < ρ) (hδ : δa + δb = ρ)
    (hαsum : ∑ l, α l = ρ) :
    ∑ e, capacityWitnessMass ρ δa δb α e = 1 := by
  simp only [capacityWitnessMass, Fintype.sum_sum_type, Fintype.sum_unique]
  rw [← Finset.mul_sum, ← Finset.mul_sum, hαsum]
  field_simp
  linarith

theorem capacityWitness_nonnegative
    {ι : Type*} [Fintype ι]
    {ρ δa δb : ℝ} {α : ι → ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hδa : 0 ≤ δa) (hδb : 0 ≤ δb)
    (hα : ∀ l, 0 ≤ α l) :
    ∀ e, 0 ≤ capacityWitnessMass ρ δa δb α e := by
  intro e
  rcases e with _ | e
  · simp [capacityWitnessMass, sub_nonneg.mpr hρ1]
  · rcases e with l | l
    · exact mul_nonneg (div_nonneg hδb hρ.le) (hα l)
    · exact mul_nonneg (div_nonneg hδa hρ.le) (hα l)

/-- The witness has the prescribed marginal on every outside column. -/
theorem capacityWitness_outside_marginal
    {ι : Type*} {ρ δa δb : ℝ} {α : ι → ℝ}
    (hρ : 0 < ρ) (hδ : δa + δb = ρ) (l : ι) :
    capacityWitnessMass ρ δa δb α (Sum.inr (Sum.inl l)) +
      capacityWitnessMass ρ δa δb α (Sum.inr (Sum.inr l)) = α l := by
  simp only [capacityWitnessMass]
  field_simp
  rw [add_comm δb δa, hδ]
  ring

/-- The witness has the prescribed marginal on core column `a`. -/
theorem capacityWitness_coreA_marginal
    {ι : Type*} [Fintype ι]
    {ρ δa δb αa : ℝ} {α : ι → ℝ}
    (hρ : 0 < ρ) (hαsum : ∑ l, α l = ρ)
    (hδa : δa + αa = 1) (hδsum : δa + δb = ρ) :
    capacityWitnessMass ρ δa δb α (Sum.inl ()) +
      ∑ l, capacityWitnessMass ρ δa δb α (Sum.inr (Sum.inl l)) = αa := by
  simp only [capacityWitnessMass, ← Finset.mul_sum, hαsum]
  field_simp
  nlinarith

/-- The witness has the prescribed marginal on core column `b`. -/
theorem capacityWitness_coreB_marginal
    {ι : Type*} [Fintype ι]
    {ρ δa δb αb : ℝ} {α : ι → ℝ}
    (hρ : 0 < ρ) (hαsum : ∑ l, α l = ρ)
    (hδb : δb + αb = 1) (hδsum : δa + δb = ρ) :
    capacityWitnessMass ρ δa δb α (Sum.inl ()) +
      ∑ l, capacityWitnessMass ρ δa δb α (Sum.inr (Sum.inr l)) = αb := by
  simp only [capacityWitnessMass, ← Finset.mul_sum, hαsum]
  field_simp
  nlinarith

/-- Convexity estimate used in paper (56). -/
theorem two_neg_tau_mul_add_rpow_le
    {x y τ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hτ : 0 ≤ τ) :
    (2 : ℝ) ^ (-τ) * (x + y) ^ (1 + τ) ≤
      x ^ (1 + τ) + y ^ (1 + τ) := by
  have hconv := (convexOn_rpow (by linarith : (1 : ℝ) ≤ 1 + τ)).2
    (show x ∈ Set.Ici (0 : ℝ) from hx)
    (show y ∈ Set.Ici (0 : ℝ) from hy)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hjensen :
      ((x + y) / 2) ^ (1 + τ) ≤
        (x ^ (1 + τ) + y ^ (1 + τ)) / 2 := by
    change
      ((1 / 2 : ℝ) * x + (1 / 2 : ℝ) * y) ^ (1 + τ) ≤
        (1 / 2 : ℝ) * x ^ (1 + τ) + (1 / 2 : ℝ) * y ^ (1 + τ) at hconv
    convert hconv using 1 <;> ring_nf
  have hscaled := mul_le_mul_of_nonneg_left hjensen (by norm_num : (0 : ℝ) ≤ 2)
  have hleft :
      2 * ((x + y) / 2) ^ (1 + τ) =
        (2 : ℝ) ^ (-τ) * (x + y) ^ (1 + τ) := by
    rw [Real.div_rpow (add_nonneg hx hy) (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp [(Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) τ).ne']
  rw [hleft] at hscaled
  nlinarith

/-- Paper (56), including both the denominator estimate and the convexity
step. -/
theorem pairTransferSum_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {τ : ℝ} (hτ : 0 ≤ τ)
    {p q : ι → ℝ} (hp : IsInteriorProbabilityVector p)
    (hq : IsInteriorProbabilityVector q) (j : ι) :
    (2 : ℝ) ^ (-τ) * (p j + q j) ^ (1 + τ) ≤
      transferU τ p j + transferU τ q j := by
  exact (two_neg_tau_mul_add_rpow_le
    (hp.1.nonnegative j) (hq.1.nonnegative j) hτ).trans
      (add_le_add (coordinate_rpow_le_transferU hp j)
        (coordinate_rpow_le_transferU hq j))

/-- Exact cancellation of the two core deficit terms in paper (59)--(61). -/
theorem core_entropy_cancellation
    {δa δb ρ : ℝ} (hδa : 0 < δa) (hδb : 0 < δb)
    (hρ : 0 < ρ) (hsum : δa + δb = ρ) :
    δa * Real.log δa + δb * Real.log δb -
        δa * Real.log (δa / ρ) - δb * Real.log (δb / ρ) =
      ρ * Real.log ρ := by
  rw [Real.log_div hδa.ne' hρ.ne', Real.log_div hδb.ne' hρ.ne']
  rw [← hsum]
  ring

/-- Elementary outside-coordinate bound used below paper (61). -/
theorem neg_alpha_le_one_sub_mul_log
    {α : ℝ} (hα1 : α < 1) :
    -α ≤ (1 - α) * Real.log (1 - α) := by
  have hpos : 0 < 1 - α := sub_pos.mpr hα1
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have hmul := mul_le_mul_of_nonneg_left hlog hpos.le
  have hsimplify : (1 - α) * (1 - (1 - α)⁻¹) = -α := by
    field_simp
    ring
  rw [hsimplify] at hmul
  exact hmul

end BeyondBethe
