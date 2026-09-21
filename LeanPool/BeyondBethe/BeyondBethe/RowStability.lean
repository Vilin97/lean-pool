/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.Slack
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic

/-! # Row Stability -/

namespace BeyondBethe

/-- `b` occurs strictly between `a` and `c` in the ordering `π`. -/
def OrderBetween {n : ℕ} (π : Equiv.Perm (Fin n))
    (a b c : Fin n) : Prop :=
  (π.symm a < π.symm b ∧ π.symm b < π.symm c) ∨
    (π.symm c < π.symm b ∧ π.symm b < π.symm a)

instance instDecidableOrderBetween
    {n : ℕ} (π : Equiv.Perm (Fin n)) (a b c : Fin n) :
    Decidable (OrderBetween π a b c) := by
  unfold OrderBetween
  infer_instance

theorem one_middle_indicator
    {n : ℕ} (π : Equiv.Perm (Fin n))
    {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (if OrderBetween π j i k then (1 : ℝ) else 0) +
      (if OrderBetween π i j k then 1 else 0) +
      (if OrderBetween π i k j then 1 else 0) = 1 := by
  classical
  have hij' : π.symm i ≠ π.symm j := π.symm.injective.ne hij
  have hik' : π.symm i ≠ π.symm k := π.symm.injective.ne hik
  have hjk' : π.symm j ≠ π.symm k := π.symm.injective.ne hjk
  rcases lt_or_gt_of_ne hij' with hijlt | hjilt
  · rcases lt_or_gt_of_ne hjk' with hjklt | hkjlt
    · have hiklt := hijlt.trans hjklt
      have hjinot : ¬π.symm j < π.symm i := not_lt_of_ge hijlt.le
      have hknotj : ¬π.symm k < π.symm j := not_lt_of_ge hjklt.le
      have hknoti : ¬π.symm k < π.symm i := not_lt_of_ge hiklt.le
      simp [OrderBetween, hijlt, hjklt, hiklt, hjinot, hknotj, hknoti]
    · rcases lt_or_gt_of_ne hik' with hiklt | hkilt
      · have hikj := hiklt.trans hkjlt
        have hkinot : ¬π.symm k < π.symm i := not_lt_of_ge hiklt.le
        have hjnotk : ¬π.symm j < π.symm k := not_lt_of_ge hkjlt.le
        have hjnoti : ¬π.symm j < π.symm i := not_lt_of_ge hikj.le
        simp [OrderBetween, hiklt, hkjlt, hikj, hkinot, hjnotk, hjnoti]
      · have hkij := hkilt.trans hijlt
        have hinotk : ¬π.symm i < π.symm k := not_lt_of_ge hkilt.le
        have hjnoti : ¬π.symm j < π.symm i := not_lt_of_ge hijlt.le
        have hjnotk : ¬π.symm j < π.symm k := not_lt_of_ge hkij.le
        simp [OrderBetween, hkilt, hijlt, hkij, hinotk, hjnoti, hjnotk]
  · rcases lt_or_gt_of_ne hik' with hiklt | hkilt
    · have hjik := hjilt.trans hiklt
      have hinotj : ¬π.symm i < π.symm j := not_lt_of_ge hjilt.le
      have hknoti : ¬π.symm k < π.symm i := not_lt_of_ge hiklt.le
      have hknotj : ¬π.symm k < π.symm j := not_lt_of_ge hjik.le
      simp [OrderBetween, hjilt, hiklt, hjik, hinotj, hknoti, hknotj]
    · rcases lt_or_gt_of_ne hjk' with hjklt | hkjlt
      · have hjki := hjklt.trans hkilt
        have hknotj : ¬π.symm k < π.symm j := not_lt_of_ge hjklt.le
        have hinotk : ¬π.symm i < π.symm k := not_lt_of_ge hkilt.le
        have hinotj : ¬π.symm i < π.symm j := not_lt_of_ge hjki.le
        simp [OrderBetween, hjklt, hkilt, hjki, hknotj, hinotk, hinotj]
      · have hkji := hkjlt.trans hjilt
        have hjnotk : ¬π.symm j < π.symm k := not_lt_of_ge hkjlt.le
        have hinotj : ¬π.symm i < π.symm j := not_lt_of_ge hjilt.le
        have hinotk : ¬π.symm i < π.symm k := not_lt_of_ge hkji.le
        simp [OrderBetween, hkjlt, hjilt, hkji, hjnotk, hinotj, hinotk]

theorem orderBetween_trans_swap
    {n : ℕ} (π : Equiv.Perm (Fin n))
    {i j k : Fin n} (hik : i ≠ k) (hjk : j ≠ k) :
    OrderBetween (π.trans (Equiv.swap i j)) i j k ↔
      OrderBetween π j i k := by
  simp [OrderBetween, Equiv.trans_apply, Equiv.swap_apply_def, hik, hjk,
    Ne.symm hik, Ne.symm hjk]

/-- Uniform probability that the middle argument lies between the two
endpoints in a random ordering. -/
noncomputable def betweenProbability
    {n : ℕ} (a b c : Fin n) : ℝ := by
  classical
  exact uniformAverage (fun π : Equiv.Perm (Fin n) ↦
    if OrderBetween π a b c then 1 else 0)

theorem betweenProbability_endpoint_symm
    {n : ℕ} (a b c : Fin n) :
    betweenProbability a b c = betweenProbability c b a := by
  classical
  apply congrArg uniformAverage
  funext π
  apply if_congr
  · simp only [OrderBetween]
    tauto
  · rfl
  · rfl

theorem betweenProbability_swap_middle
    {n : ℕ} {i j k : Fin n} (hik : i ≠ k) (hjk : j ≠ k) :
    betweenProbability j i k = betweenProbability i j k := by
  classical
  let f : Equiv.Perm (Fin n) → ℝ := fun π ↦
    if OrderBetween π i j k then 1 else 0
  calc
    betweenProbability j i k =
        uniformAverage (fun π : Equiv.Perm (Fin n) ↦
          f (π.trans (Equiv.swap i j))) := by
      apply congrArg uniformAverage
      funext π
      simp only [f]
      exact if_congr (orderBetween_trans_swap π hik hjk).symm rfl rfl
    _ = uniformAverage f := uniformAverage_perm_trans f (Equiv.swap i j)
    _ = betweenProbability i j k := rfl

theorem betweenProbability_eq_one_third
    {n : ℕ} {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    betweenProbability j i k = 1 / 3 := by
  classical
  have hijSymm := betweenProbability_swap_middle (i := i) (j := j)
    (k := k) hik hjk
  have hjkSymm := betweenProbability_swap_middle (i := j) (j := k)
    (k := i) (Ne.symm hij) (Ne.symm hik)
  have hBC : betweenProbability i j k = betweenProbability i k j := by
    calc
      betweenProbability i j k = betweenProbability k j i :=
        betweenProbability_endpoint_symm i j k
      _ = betweenProbability j k i := hjkSymm
      _ = betweenProbability i k j :=
        betweenProbability_endpoint_symm j k i
  have hsum : betweenProbability j i k +
      betweenProbability i j k + betweenProbability i k j = 1 := by
    unfold betweenProbability uniformAverage
    rw [← add_div, ← add_div,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    simp_rw [one_middle_indicator _ hij hik hjk]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [Fintype.card_ne_zero]
  rw [hijSymm, ← hBC] at hsum
  linarith

/-- The three named points occur in this strict order. -/
def StrictTripleOrder {n : ℕ} (π : Equiv.Perm (Fin n))
    (a b c : Fin n) : Prop :=
  π.symm a < π.symm b ∧ π.symm b < π.symm c

instance instDecidableStrictTripleOrder
    {n : ℕ} (π : Equiv.Perm (Fin n)) (a b c : Fin n) :
    Decidable (StrictTripleOrder π a b c) := by
  unfold StrictTripleOrder
  infer_instance

noncomputable def tripleOrderProbability
    {n : ℕ} (a b c : Fin n) : ℝ := by
  classical
  exact uniformAverage (fun π : Equiv.Perm (Fin n) ↦
    if StrictTripleOrder π a b c then 1 else 0)

theorem strictTripleOrder_trans_swap_endpoints
    {n : ℕ} (π : Equiv.Perm (Fin n))
    {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) :
    StrictTripleOrder (π.trans (Equiv.swap a c)) a b c ↔
      StrictTripleOrder π c b a := by
  simp [StrictTripleOrder, Equiv.trans_apply, Equiv.swap_apply_def,
    hab, hbc, Ne.symm hab, Ne.symm hbc]

theorem tripleOrderProbability_reverse
    {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) :
    tripleOrderProbability a b c = tripleOrderProbability c b a := by
  classical
  let f : Equiv.Perm (Fin n) → ℝ := fun π ↦
    if StrictTripleOrder π a b c then 1 else 0
  let g : Equiv.Perm (Fin n) → ℝ := fun π ↦
    if StrictTripleOrder π c b a then 1 else 0
  calc
    tripleOrderProbability a b c = uniformAverage f := rfl
    _ = uniformAverage (fun π : Equiv.Perm (Fin n) ↦
          g (π.trans (Equiv.swap c a))) := by
      apply congrArg uniformAverage
      funext π
      exact if_congr
        (strictTripleOrder_trans_swap_endpoints π
          (a := c) (b := b) (c := a) (Ne.symm hbc) (Ne.symm hab)).symm
        rfl rfl
    _ = uniformAverage g := uniformAverage_perm_trans g (Equiv.swap c a)
    _ = tripleOrderProbability c b a := rfl

theorem betweenProbability_eq_tripleOrder_add_reverse
    {n : ℕ} (a b c : Fin n) :
    betweenProbability a b c =
      tripleOrderProbability a b c + tripleOrderProbability c b a := by
  classical
  rw [betweenProbability, tripleOrderProbability, tripleOrderProbability,
    ← uniformAverage_add]
  apply congrArg uniformAverage
  funext π
  simp only [OrderBetween, StrictTripleOrder]
  by_cases h₁ : π.symm a < π.symm b ∧ π.symm b < π.symm c
  · have hnot : ¬(π.symm c < π.symm b ∧ π.symm b < π.symm a) := by
      intro h
      exact lt_asymm h₁.1 h.2
    simp [h₁, hnot]
  · by_cases h₂ : π.symm c < π.symm b ∧ π.symm b < π.symm a
    · simp [h₁, h₂]
    · simp [h₁, h₂]

theorem tripleOrderProbability_eq_one_sixth
    {n : ℕ} {a b c : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    tripleOrderProbability a b c = 1 / 6 := by
  have hbetween := betweenProbability_eq_one_third
    (i := b) (j := a) (k := c) (Ne.symm hab) hbc hac
  rw [betweenProbability_eq_tripleOrder_add_reverse] at hbetween
  have hreverse := tripleOrderProbability_reverse hab hbc
  rw [← hreverse] at hbetween
  linarith

/-- Mass strictly before coordinate `i` in an ordering. -/
noncomputable def strictLeftMass
    {n : ℕ} (p : Fin n → ℝ) (π : Equiv.Perm (Fin n)) (i : Fin n) : ℝ :=
  ∑ j, if π.symm j < π.symm i then p j else 0

/-- Mass strictly after coordinate `i` in an ordering. -/
noncomputable def strictRightMass
    {n : ℕ} (p : Fin n → ℝ) (π : Equiv.Perm (Fin n)) (i : Fin n) : ℝ :=
  ∑ j, if π.symm i < π.symm j then p j else 0

theorem strictLeftMass_add_strictRightMass
    {n : ℕ} {p : Fin n → ℝ} (hp : IsProbabilityVector p)
    (π : Equiv.Perm (Fin n)) (i : Fin n) :
    strictLeftMass p π i + strictRightMass p π i = 1 - p i := by
  classical
  rw [strictLeftMass, strictRightMass, ← Finset.sum_add_distrib]
  have hterm : ∀ j : Fin n,
      (if π.symm j < π.symm i then p j else 0) +
          (if π.symm i < π.symm j then p j else 0) =
        if j = i then 0 else p j := by
    intro j
    by_cases hji : j = i
    · subst j
      simp
    · have hpos : π.symm j ≠ π.symm i := π.symm.injective.ne hji
      rcases lt_or_gt_of_ne hpos with hlt | hgt
      · simp [hji, hlt, not_lt_of_ge hlt.le]
      · simp [hji, hgt, not_lt_of_ge hgt.le]
  simp_rw [hterm]
  calc
    ∑ j : Fin n, (if j = i then 0 else p j) =
        ∑ j, (p j - if j = i then p j else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i <;> simp [hji]
    _ = (∑ j, p j) - ∑ j, (if j = i then p j else 0) := by
      rw [Finset.sum_sub_distrib]
    _ = 1 - p i := by rw [hp.sum_eq_one]; simp

theorem prefix_mul_suffix_eq_self_add_crossing
    {n : ℕ} {p : Fin n → ℝ} (hp : IsProbabilityVector p)
    (π : Equiv.Perm (Fin n)) (i : Fin n) :
    (p i + strictLeftMass p π i) *
        (p i + strictRightMass p π i) =
      p i + strictLeftMass p π i * strictRightMass p π i := by
  have hmass := strictLeftMass_add_strictRightMass hp π i
  calc
    (p i + strictLeftMass p π i) *
        (p i + strictRightMass p π i) =
      (p i) ^ 2 + p i *
        (strictLeftMass p π i + strictRightMass p π i) +
          strictLeftMass p π i * strictRightMass p π i := by ring
    _ = p i + strictLeftMass p π i * strictRightMass p π i := by
      rw [hmass]
      ring

/-- The product of the strict masses on the two sides of `i` is the total
weight of ordered pairs that straddle `i`. -/
theorem strictLeftMass_mul_strictRightMass
    {n : ℕ} (p : Fin n → ℝ) (π : Equiv.Perm (Fin n)) (i : Fin n) :
    strictLeftMass p π i * strictRightMass p π i =
      ∑ j, ∑ k, if StrictTripleOrder π j i k then p j * p k else 0 := by
  classical
  rw [strictLeftMass, strictRightMass, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold StrictTripleOrder
  by_cases hj : π.symm j < π.symm i
  · by_cases hk : π.symm i < π.symm k <;> simp [hj, hk]
  · simp [hj]

theorem uniformAverage_indicator_mul
    {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] (c : ℝ) :
    uniformAverage (fun x ↦ if P x then c else 0) =
      c * uniformAverage (fun x ↦ if P x then 1 else 0) := by
  rw [← uniformAverage_const_mul]
  apply congrArg uniformAverage
  funext x
  by_cases hx : P x <;> simp [hx]

theorem tripleOrderProbability_eq_zero_of_left_eq_middle
    {n : ℕ} (a c : Fin n) :
    tripleOrderProbability a a c = 0 := by
  classical
  rw [tripleOrderProbability]
  calc
    uniformAverage (fun π : Equiv.Perm (Fin n) ↦
        if StrictTripleOrder π a a c then 1 else 0) =
        uniformAverage (fun _ : Equiv.Perm (Fin n) ↦ 0) := by
      apply congrArg uniformAverage
      funext π
      simp [StrictTripleOrder]
    _ = 0 := uniformAverage_const 0

theorem tripleOrderProbability_eq_zero_of_middle_eq_right
    {n : ℕ} (a c : Fin n) :
    tripleOrderProbability a c c = 0 := by
  classical
  rw [tripleOrderProbability]
  calc
    uniformAverage (fun π : Equiv.Perm (Fin n) ↦
        if StrictTripleOrder π a c c then 1 else 0) =
        uniformAverage (fun _ : Equiv.Perm (Fin n) ↦ 0) := by
      apply congrArg uniformAverage
      funext π
      simp [StrictTripleOrder]
    _ = 0 := uniformAverage_const 0

theorem tripleOrderProbability_eq_zero_of_left_eq_right
    {n : ℕ} (a b : Fin n) :
    tripleOrderProbability a b a = 0 := by
  classical
  rw [tripleOrderProbability]
  calc
    uniformAverage (fun π : Equiv.Perm (Fin n) ↦
        if StrictTripleOrder π a b a then 1 else 0) =
        uniformAverage (fun _ : Equiv.Perm (Fin n) ↦ 0) := by
      apply congrArg uniformAverage
      funext π
      rw [if_neg]
      intro h
      exact lt_asymm h.1 h.2
    _ = 0 := uniformAverage_const 0

theorem tripleOrderProbability_cases
    {n : ℕ} (a b c : Fin n) :
    tripleOrderProbability a b c =
      if a ≠ b ∧ a ≠ c ∧ b ≠ c then 1 / 6 else 0 := by
  classical
  by_cases hab : a = b
  · subst b
    simp [tripleOrderProbability_eq_zero_of_left_eq_middle]
  · by_cases hac : a = c
    · subst c
      simp [hab, tripleOrderProbability_eq_zero_of_left_eq_right]
    · by_cases hbc : b = c
      · subst c
        simp [hab, tripleOrderProbability_eq_zero_of_middle_eq_right]
      · simp [hab, hac, hbc, tripleOrderProbability_eq_one_sixth hab hac hbc]

/-- Uniformly averaging the strict-left/strict-right product turns every
ordered pair of distinct coordinates away from `i` into a `1/6` contribution. -/
theorem average_strictLeftMass_mul_strictRightMass
    {n : ℕ} (p : Fin n → ℝ) (i : Fin n) :
    uniformAverage (fun π : Equiv.Perm (Fin n) ↦
        strictLeftMass p π i * strictRightMass p π i) =
      (1 / 6) * ∑ j, ∑ k,
        if j ≠ i ∧ j ≠ k ∧ i ≠ k then p j * p k else 0 := by
  classical
  calc
    uniformAverage (fun π : Equiv.Perm (Fin n) ↦
        strictLeftMass p π i * strictRightMass p π i) =
        uniformAverage (fun π : Equiv.Perm (Fin n) ↦
          ∑ j, ∑ k,
            if StrictTripleOrder π j i k then p j * p k else 0) :=
      congrArg uniformAverage (funext fun π ↦
        strictLeftMass_mul_strictRightMass p π i)
    _ = ∑ j, uniformAverage (fun π : Equiv.Perm (Fin n) ↦
          ∑ k, if StrictTripleOrder π j i k then p j * p k else 0) :=
      uniformAverage_sum _
    _ = ∑ j, ∑ k, uniformAverage (fun π : Equiv.Perm (Fin n) ↦
          if StrictTripleOrder π j i k then p j * p k else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      exact uniformAverage_sum _
    _ = ∑ j, ∑ k, (1 / 6) *
          (if j ≠ i ∧ j ≠ k ∧ i ≠ k then p j * p k else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      calc
        uniformAverage (fun π : Equiv.Perm (Fin n) ↦
            if StrictTripleOrder π j i k then p j * p k else 0) =
            p j * p k * tripleOrderProbability j i k :=
          uniformAverage_indicator_mul
            (fun π : Equiv.Perm (Fin n) ↦ StrictTripleOrder π j i k)
            (p j * p k)
        _ = p j * p k *
            (if j ≠ i ∧ j ≠ k ∧ i ≠ k then 1 / 6 else 0) := by
          rw [tripleOrderProbability_cases]
        _ = (1 / 6) *
            (if j ≠ i ∧ j ≠ k ∧ i ≠ k then p j * p k else 0) := by
          by_cases h : j ≠ i ∧ j ≠ k ∧ i ≠ k <;> simp [h] <;> ring
    _ = (1 / 6) * ∑ j, ∑ k,
          if j ≠ i ∧ j ≠ k ∧ i ≠ k then p j * p k else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]

theorem sum_ite_ne_eq_sum_sub
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ) (i : ι) :
    (∑ j, if j ≠ i then f j else 0) = (∑ j, f j) - f i := by
  calc
    (∑ j, if j ≠ i then f j else 0) =
        ∑ j, (f j - if j = i then f j else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i <;> simp [hji]
    _ = (∑ j, f j) - ∑ j, (if j = i then f j else 0) := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ j, f j) - f i := by simp

theorem sum_away_from_two
    {n : ℕ} {p : Fin n → ℝ} (hp : IsProbabilityVector p)
    {i j : Fin n} (hij : i ≠ j) :
    (∑ k, if i ≠ k ∧ j ≠ k then p k else 0) = 1 - p i - p j := by
  classical
  calc
    (∑ k, if i ≠ k ∧ j ≠ k then p k else 0) =
        ∑ k, (p k - (if k = i then p k else 0) -
          (if k = j then p k else 0)) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hki : k = i
      · subst k
        simp [hij]
      · by_cases hkj : k = j
        · subst k
          simp [hki]
        · simp [hki, hkj, Ne.symm hki, Ne.symm hkj]
    _ = (∑ k, p k) - ∑ k, (if k = i then p k else 0) -
          ∑ k, (if k = j then p k else 0) := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    _ = 1 - p i - p j := by rw [hp.sum_eq_one]; simp

theorem inner_ordered_distinct_products
    {n : ℕ} {p : Fin n → ℝ} (hp : IsProbabilityVector p)
    (i j : Fin n) :
    (∑ k, if j ≠ i ∧ j ≠ k ∧ i ≠ k then p j * p k else 0) =
      if j ≠ i then p j * (1 - p i - p j) else 0 := by
  classical
  by_cases hji : j = i
  · subst j
    simp
  · calc
      (∑ k, if j ≠ i ∧ j ≠ k ∧ i ≠ k then p j * p k else 0) =
          p j * ∑ k, if i ≠ k ∧ j ≠ k then p k else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        by_cases hjk : j = k
        · subst k
          simp
        · by_cases hik : i = k
          · subst k
            simp [hji]
          · simp [hji, hjk, hik, Ne.symm hjk, Ne.symm hik]
      _ = p j * (1 - p i - p j) := by
        rw [sum_away_from_two hp (Ne.symm hji)]
      _ = if j ≠ i then p j * (1 - p i - p j) else 0 := by simp [hji]

/-- The exact finite-sum identity behind the expected prefix--suffix moment. -/
theorem sum_ordered_distinct_products
    {n : ℕ} {p : Fin n → ℝ} (hp : IsProbabilityVector p) (i : Fin n) :
    (∑ j, ∑ k,
        if j ≠ i ∧ j ≠ k ∧ i ≠ k then p j * p k else 0) =
      (1 - p i) ^ 2 - ((∑ j, (p j) ^ 2) - (p i) ^ 2) := by
  classical
  calc
    (∑ j, ∑ k,
        if j ≠ i ∧ j ≠ k ∧ i ≠ k then p j * p k else 0) =
        ∑ j, if j ≠ i then p j * (1 - p i - p j) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      exact inner_ordered_distinct_products hp i j
    _ = ∑ j, ((if j ≠ i then p j else 0) * (1 - p i) -
          (if j ≠ i then (p j) ^ 2 else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i <;> simp [hji] <;> ring
    _ = (∑ j, if j ≠ i then p j else 0) * (1 - p i) -
          ∑ j, (if j ≠ i then (p j) ^ 2 else 0) := by
      rw [Finset.sum_sub_distrib, Finset.sum_mul]
    _ = ((∑ j, p j) - p i) * (1 - p i) -
          ((∑ j, (p j) ^ 2) - (p i) ^ 2) := by
      rw [sum_ite_ne_eq_sum_sub, sum_ite_ne_eq_sum_sub]
    _ = (1 - p i) ^ 2 - ((∑ j, (p j) ^ 2) - (p i) ^ 2) := by
      rw [hp.sum_eq_one]
      ring

/-- The expected product of the prefix and suffix masses at coordinate `i`. -/
noncomputable def orderingMoment
    {n : ℕ} (p : Fin n → ℝ) (i : Fin n) : ℝ :=
  uniformAverage (fun π : Equiv.Perm (Fin n) ↦
    (p i + strictLeftMass p π i) * (p i + strictRightMass p π i))

/-- Paper (31): the exact prefix--suffix moment identity. -/
theorem orderingMoment_eq
    {n : ℕ} {p : Fin n → ℝ} (hp : IsProbabilityVector p) (i : Fin n) :
    orderingMoment p i =
      (1 - ∑ j, (p j) ^ 2) / 6 + 2 / 3 * p i + 1 / 3 * (p i) ^ 2 := by
  classical
  calc
    orderingMoment p i = uniformAverage (fun π : Equiv.Perm (Fin n) ↦
        p i + strictLeftMass p π i * strictRightMass p π i) := by
      apply congrArg uniformAverage
      funext π
      exact prefix_mul_suffix_eq_self_add_crossing hp π i
    _ = uniformAverage (fun _ : Equiv.Perm (Fin n) ↦ p i) +
          uniformAverage (fun π : Equiv.Perm (Fin n) ↦
            strictLeftMass p π i * strictRightMass p π i) :=
      uniformAverage_add _ _
    _ = p i + (1 / 6) * ∑ j, ∑ k,
          if j ≠ i ∧ j ≠ k ∧ i ≠ k then p j * p k else 0 := by
      rw [uniformAverage_const,
        average_strictLeftMass_mul_strictRightMass]
    _ = p i + (1 / 6) *
          ((1 - p i) ^ 2 - ((∑ j, (p j) ^ 2) - (p i) ^ 2)) := by
      rw [sum_ordered_distinct_products hp]
    _ = (1 - ∑ j, (p j) ^ 2) / 6 +
          2 / 3 * p i + 1 / 3 * (p i) ^ 2 := by ring

/-- Jensen's inequality for the uniform average of logarithms. -/
theorem uniformAverage_log_le_log_uniformAverage
    {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (hf : ∀ x, 0 < f x) :
    uniformAverage (fun x ↦ Real.log (f x)) ≤
      Real.log (uniformAverage f) := by
  let N : ℝ := Fintype.card α
  have hN : 0 < N := by
    simpa [N] using (Nat.cast_pos.mpr (Fintype.card_pos : 0 < Fintype.card α) :
      (0 : ℝ) < Fintype.card α)
  have hweights : ∑ _x : α, (1 / N : ℝ) = 1 := by
    dsimp [N]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have h := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t := Finset.univ) (w := fun _ : α ↦ (1 / N : ℝ)) (p := f)
    (fun _ _ ↦ by positivity) hweights (fun x _ ↦ hf x)
  calc
    uniformAverage (fun x ↦ Real.log (f x)) =
        ∑ x, (1 / N) • Real.log (f x) := by
      rw [uniformAverage, div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      simp [N, smul_eq_mul]
      ring
    _ ≤ Real.log (∑ x, (1 / N) • f x) := h
    _ = Real.log (uniformAverage f) := by
      congr 1
      calc
        (∑ x, (1 / N) • f x) = (1 / N) * ∑ x, f x := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          simp [smul_eq_mul]
        _ = uniformAverage f := by
          simp [uniformAverage, N, div_eq_mul_inv]
          ring

theorem suffixMass_eq_self_add_strictRightMass
    {n : ℕ} (p : Fin n → ℝ) (π : Equiv.Perm (Fin n)) (i : Fin n) :
    suffixMass p π i = p i + strictRightMass p π i := by
  classical
  rw [suffixMass, strictRightMass]
  calc
    (∑ k, if π.symm i ≤ π.symm k then p k else 0) =
        ∑ k, ((if k = i then p k else 0) +
          (if π.symm i < π.symm k then p k else 0)) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hki : k = i
      · subst k
        simp
      · have hpos : π.symm i ≠ π.symm k :=
          π.symm.injective.ne (Ne.symm hki)
        rcases lt_or_gt_of_ne hpos with hlt | hgt
        · simp [hki, hlt, hlt.le]
        · have hnot : ¬π.symm i < π.symm k := not_lt_of_ge hgt.le
          simp [hki, hgt, not_le_of_gt hgt, hnot]
    _ = (∑ k, if k = i then p k else 0) +
          ∑ k, (if π.symm i < π.symm k then p k else 0) := by
      rw [Finset.sum_add_distrib]
    _ = p i + ∑ k, (if π.symm i < π.symm k then p k else 0) := by simp

/-- Reverse an ordering by reversing its positions. -/
def reverseOrdering {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n) :=
  Fin.revPerm.trans π

/-- Left composition by a fixed permutation is a bijection on orderings. -/
def permPreTransEquiv {n : ℕ} (τ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) where
  toFun π := τ.trans π
  invFun θ := τ.symm.trans θ
  left_inv π := by
    ext i
    simp [Equiv.trans_apply]
  right_inv θ := by
    ext i
    simp [Equiv.trans_apply]

theorem uniformAverage_perm_preTrans
    {n : ℕ} (f : Equiv.Perm (Fin n) → ℝ)
    (τ : Equiv.Perm (Fin n)) :
    uniformAverage (fun π : Equiv.Perm (Fin n) ↦ f (τ.trans π)) =
      uniformAverage f := by
  rw [uniformAverage, uniformAverage]
  congr 1
  exact (permPreTransEquiv τ).sum_comp f

theorem suffixMass_reverseOrdering
    {n : ℕ} (p : Fin n → ℝ) (π : Equiv.Perm (Fin n)) (i : Fin n) :
    suffixMass p (reverseOrdering π) i = p i + strictLeftMass p π i := by
  classical
  rw [suffixMass, strictLeftMass]
  calc
    (∑ k, if (reverseOrdering π).symm i ≤
          (reverseOrdering π).symm k then p k else 0) =
        ∑ k, ((if k = i then p k else 0) +
          (if π.symm k < π.symm i then p k else 0)) := by
      apply Finset.sum_congr rfl
      intro k _
      have hrev : (reverseOrdering π).symm i ≤
          (reverseOrdering π).symm k ↔ π.symm k ≤ π.symm i := by
        simp [reverseOrdering, Equiv.trans_apply, Fin.rev_le_rev]
      simp only [hrev]
      by_cases hki : k = i
      · subst k
        simp
      · have hpos : π.symm k ≠ π.symm i := π.symm.injective.ne hki
        rcases lt_or_gt_of_ne hpos with hlt | hgt
        · simp [hki, hlt, hlt.le]
        · have hnot : ¬π.symm k < π.symm i := not_lt_of_ge hgt.le
          simp [hki, hgt, not_le_of_gt hgt, hnot]
    _ = (∑ k, if k = i then p k else 0) +
          ∑ k, (if π.symm k < π.symm i then p k else 0) := by
      rw [Finset.sum_add_distrib]
    _ = p i + ∑ k, (if π.symm k < π.symm i then p k else 0) := by simp

theorem average_log_suffix_reverseOrdering
    {n : ℕ} (p : Fin n → ℝ) (i : Fin n) :
    uniformAverage (fun π : Equiv.Perm (Fin n) ↦
        Real.log (suffixMass p (reverseOrdering π) i)) =
      uniformAverage (fun π : Equiv.Perm (Fin n) ↦
        Real.log (suffixMass p π i)) := by
  exact uniformAverage_perm_preTrans
    (fun π : Equiv.Perm (Fin n) ↦ Real.log (suffixMass p π i))
    Fin.revPerm

/-- Pairing an ordering with its reversal rewrites the suffix log as half the
logarithm of the prefix--suffix product. -/
theorem average_log_suffix_symmetrized
    {n : ℕ} {p : Fin n → ℝ} (hp : IsStrictProbabilityVector p) (i : Fin n) :
    uniformAverage (fun π : Equiv.Perm (Fin n) ↦
        Real.log (suffixMass p π i)) =
      (1 / 2) * uniformAverage (fun π : Equiv.Perm (Fin n) ↦
        Real.log ((p i + strictLeftMass p π i) *
          (p i + strictRightMass p π i))) := by
  have hprefix : uniformAverage (fun π : Equiv.Perm (Fin n) ↦
      Real.log (p i + strictLeftMass p π i)) =
      uniformAverage (fun π : Equiv.Perm (Fin n) ↦
        Real.log (suffixMass p π i)) := by
    calc
      uniformAverage (fun π : Equiv.Perm (Fin n) ↦
          Real.log (p i + strictLeftMass p π i)) =
          uniformAverage (fun π : Equiv.Perm (Fin n) ↦
            Real.log (suffixMass p (reverseOrdering π) i)) := by
        apply congrArg uniformAverage
        funext π
        rw [suffixMass_reverseOrdering]
      _ = uniformAverage (fun π : Equiv.Perm (Fin n) ↦
          Real.log (suffixMass p π i)) :=
        average_log_suffix_reverseOrdering p i
  have hproduct : uniformAverage (fun π : Equiv.Perm (Fin n) ↦
      Real.log ((p i + strictLeftMass p π i) *
        (p i + strictRightMass p π i))) =
      uniformAverage (fun π : Equiv.Perm (Fin n) ↦
        Real.log (p i + strictLeftMass p π i)) +
      uniformAverage (fun π : Equiv.Perm (Fin n) ↦
        Real.log (suffixMass p π i)) := by
    calc
      uniformAverage (fun π : Equiv.Perm (Fin n) ↦
          Real.log ((p i + strictLeftMass p π i) *
            (p i + strictRightMass p π i))) =
          uniformAverage (fun π : Equiv.Perm (Fin n) ↦
            Real.log (p i + strictLeftMass p π i) +
              Real.log (suffixMass p π i)) := by
        apply congrArg uniformAverage
        funext π
        rw [suffixMass_eq_self_add_strictRightMass]
        exact Real.log_mul
          (by
            rw [← suffixMass_reverseOrdering]
            exact (suffixMass_pos hp.1 (hp.2 i) _).ne')
          (by
            rw [← suffixMass_eq_self_add_strictRightMass]
            exact (suffixMass_pos hp.1 (hp.2 i) _).ne')
      _ = _ := uniformAverage_add _ _
  rw [hproduct, hprefix]
  ring

theorem average_log_suffix_le_half_log_orderingMoment
    {n : ℕ} {p : Fin n → ℝ} (hp : IsStrictProbabilityVector p) (i : Fin n) :
    uniformAverage (fun π : Equiv.Perm (Fin n) ↦
        Real.log (suffixMass p π i)) ≤
      (1 / 2) * Real.log (orderingMoment p i) := by
  rw [average_log_suffix_symmetrized hp i]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact uniformAverage_log_le_log_uniformAverage _ (fun π ↦ by
    exact mul_pos
      (by
        rw [← suffixMass_reverseOrdering]
        exact suffixMass_pos hp.1 (hp.2 i) _)
      (by
        rw [← suffixMass_eq_self_add_strictRightMass]
        exact suffixMass_pos hp.1 (hp.2 i) _))

theorem uniformAverage_pos
    {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (hf : ∀ x, 0 < f x) :
    0 < uniformAverage f := by
  rw [uniformAverage]
  exact div_pos
    (Finset.sum_pos (fun x _ ↦ hf x) Finset.univ_nonempty)
    (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card α))

theorem orderingMoment_pos
    {n : ℕ} {p : Fin n → ℝ} (hp : IsStrictProbabilityVector p) (i : Fin n) :
    0 < orderingMoment p i := by
  apply uniformAverage_pos
  intro π
  exact mul_pos
    (by
      rw [← suffixMass_reverseOrdering]
      exact suffixMass_pos hp.1 (hp.2 i) _)
    (by
      rw [← suffixMass_eq_self_add_strictRightMass]
      exact suffixMass_pos hp.1 (hp.2 i) _)

/-- The tangent inequality for `log` at `1/2`. -/
theorem log_le_tangent_at_half {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ -Real.log 2 + 2 * x - 1 := by
  have h := Real.log_le_sub_one_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hx)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx.ne'] at h
  linarith

theorem rowT_le_moment_bound
    {n : ℕ} {p : Fin n → ℝ} (hp : IsStrictProbabilityVector p) :
    rowT p ≤ -1 / 2 * Real.log 2 +
      ∑ i, p i * orderingMoment p i - 1 / 2 := by
  calc
    rowT p = ∑ i, p i * uniformAverage
        (fun π : Equiv.Perm (Fin n) ↦ Real.log (suffixMass p π i)) :=
      rowT_eq_sum_mul_average_suffix p
    _ ≤ ∑ i, p i * ((1 / 2) * Real.log (orderingMoment p i)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (average_log_suffix_le_half_log_orderingMoment hp i)
        (hp.1.nonnegative i)
    _ ≤ ∑ i, p i * ((1 / 2) *
          (-Real.log 2 + 2 * orderingMoment p i - 1)) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hp.1.nonnegative i)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact log_le_tangent_at_half (orderingMoment_pos hp i)
    _ = ∑ i, (-1 / 2 * Real.log 2 * p i +
          p i * orderingMoment p i - 1 / 2 * p i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = -1 / 2 * Real.log 2 +
          ∑ i, p i * orderingMoment p i - 1 / 2 := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, hp.1.sum_eq_one]
      ring

theorem sum_mul_orderingMoment_eq
    {n : ℕ} {p : Fin n → ℝ} (hp : IsProbabilityVector p) :
    (∑ i, p i * orderingMoment p i) =
      1 / 6 + 1 / 2 * (∑ i, (p i) ^ 2) +
        1 / 3 * (∑ i, (p i) ^ 3) := by
  simp_rw [orderingMoment_eq hp]
  calc
    (∑ i, p i *
        ((1 - ∑ j, p j ^ 2) / 6 + 2 / 3 * p i + 1 / 3 * p i ^ 2)) =
        ∑ i, ((1 - ∑ j, p j ^ 2) / 6 * p i +
          2 / 3 * p i ^ 2 + 1 / 3 * p i ^ 3) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (1 - ∑ j, p j ^ 2) / 6 * (∑ i, p i) +
          2 / 3 * (∑ i, p i ^ 2) + 1 / 3 * (∑ i, p i ^ 3) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = 1 / 6 + 1 / 2 * (∑ i, p i ^ 2) +
          1 / 3 * (∑ i, p i ^ 3) := by
      rw [hp.sum_eq_one]
      ring

/-- The symmetrization, exact moment, Jensen, and tangent estimates combined. -/
theorem rowT_le_cubic_bound
    {n : ℕ} {p : Fin n → ℝ} (hp : IsStrictProbabilityVector p) :
    rowT p ≤ -1 / 2 * Real.log 2 - 1 / 3 +
      1 / 2 * (∑ i, (p i) ^ 2) + 1 / 3 * (∑ i, (p i) ^ 3) := by
  calc
    rowT p ≤ -1 / 2 * Real.log 2 +
        ∑ i, p i * orderingMoment p i - 1 / 2 :=
      rowT_le_moment_bound hp
    _ = -1 / 2 * Real.log 2 - 1 / 3 +
        1 / 2 * (∑ i, (p i) ^ 2) + 1 / 3 * (∑ i, (p i) ^ 3) := by
      rw [sum_mul_orderingMoment_eq hp.1]
      ring

/-- The separable function `F` in paper (35). -/
noncomputable def rowStabilityF (x : ℝ) : ℝ :=
  -(1 - x) * Real.log (1 - x) + x ^ 2 / 2 + x ^ 3 / 3

/-- The sharp value of the separable sum at a half--half vector. -/
noncomputable def rowStabilityC : ℝ :=
  Real.log 2 + 1 / 3

/-- The ratio `h(x)=F(x)/x` used to identify the equality case.  Only positive
arguments are used below. -/
noncomputable def rowStabilityH (x : ℝ) : ℝ :=
  rowStabilityF x / x

noncomputable def rowStabilityFPrime (x : ℝ) : ℝ :=
  Real.log (1 - x) + 1 + x + x ^ 2

noncomputable def rowStabilityHPrime (x : ℝ) : ℝ :=
  (Real.log (1 - x) + x + x ^ 2 / 2 + 2 * x ^ 3 / 3) / x ^ 2

theorem hasDerivAt_rowStabilityF
    {x : ℝ} (hx : x < 1) :
    HasDerivAt rowStabilityF (rowStabilityFPrime x) x := by
  have hlinear : HasDerivAt (fun y : ℝ ↦ -(1 - y)) 1 x := by
    convert! ((hasDerivAt_const x 1).sub (hasDerivAt_id x)).neg using 1 <;> ring
  have hlog : HasDerivAt (fun y : ℝ ↦ Real.log (1 - y))
      (-1 / (1 - x)) x := by
    simpa [Function.id_def] using
      ((hasDerivAt_const x 1).sub (hasDerivAt_id x)).log
        (by linarith : 1 - x ≠ 0)
  have hsq : HasDerivAt (fun y : ℝ ↦ y ^ 2 / 2) x x := by
    convert! (hasDerivAt_pow 2 x).div_const 2 using 1 <;> ring
  have hcub : HasDerivAt (fun y : ℝ ↦ y ^ 3 / 3) (x ^ 2) x := by
    convert! (hasDerivAt_pow 3 x).div_const 3 using 1 <;> ring
  have h := (hlinear.mul hlog).add hsq |>.add hcub
  unfold rowStabilityF rowStabilityFPrime
  convert! h using 1 <;>
    field_simp [show 1 - x ≠ 0 by linarith] <;> ring

theorem hasDerivAt_rowStabilityH
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt rowStabilityH (rowStabilityHPrime x) x := by
  have h := (hasDerivAt_rowStabilityF hx1).div (hasDerivAt_id x) hx0.ne'
  simp only [Function.id_def] at h
  unfold rowStabilityFPrime rowStabilityF at h
  unfold rowStabilityH rowStabilityHPrime rowStabilityF
  convert! h using 1 <;> field_simp [hx0.ne'] <;> ring

/-- An explicit Taylor lower bound for `log(1-x)`. -/
theorem log_one_sub_lower_eight
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -(x + x ^ 2 / 2 + x ^ 3 / 3 + x ^ 4 / 4 + x ^ 5 / 5 +
        x ^ 6 / 6 + x ^ 7 / 7 + x ^ 8 / 8) - x ^ 9 / (1 - x) ≤
      Real.log (1 - x) := by
  have habs := Real.abs_log_sub_add_sum_range_le
    (show |x| < 1 by simpa [abs_of_nonneg hx0]) 8
  have hneg := neg_le_of_abs_le habs
  rw [abs_of_nonneg hx0] at hneg
  norm_num [Finset.sum_range_succ] at hneg
  nlinarith

/-- On `[0,1/2]`, the numerator of `h'` has a uniform cubic lower bound. -/
theorem rowStabilityHPrime_numerator_lower
    {x : ℝ} (hx0 : 0 ≤ x) (hxHalf : x ≤ 1 / 2) :
    x ^ 3 / 12 ≤
      Real.log (1 - x) + x + x ^ 2 / 2 + 2 * x ^ 3 / 3 := by
  have hp (r : ℕ) : x ^ (3 + r) ≤ x ^ 3 * (1 / 2 : ℝ) ^ r := by
    rw [pow_add]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hx0 hxHalf r) (pow_nonneg hx0 3)
  have h4 : x ^ 4 ≤ x ^ 3 / 2 := by
    simpa [div_eq_mul_inv] using hp 1
  have h5 : x ^ 5 ≤ x ^ 3 / 4 := by
    convert hp 2 using 1 <;> norm_num <;> ring
  have h6 : x ^ 6 ≤ x ^ 3 / 8 := by
    convert hp 3 using 1 <;> norm_num <;> ring
  have h7 : x ^ 7 ≤ x ^ 3 / 16 := by
    convert hp 4 using 1 <;> norm_num <;> ring
  have h8 : x ^ 8 ≤ x ^ 3 / 32 := by
    convert hp 5 using 1 <;> norm_num <;> ring
  have h9 : x ^ 9 ≤ x ^ 3 / 64 := by
    convert hp 6 using 1 <;> norm_num <;> ring
  have hden : 0 < 1 - x := by linarith
  have hrem : x ^ 9 / (1 - x) ≤ x ^ 3 / 32 := by
    rw [div_le_iff₀ hden]
    have hs := mul_le_mul_of_nonneg_left
      (show (1 / 2 : ℝ) ≤ 1 - x by linarith) (pow_nonneg hx0 3)
    nlinarith
  have hlog := log_one_sub_lower_eight hx0 (by linarith : x < 1)
  have hneg : x ^ 4 / 4 + x ^ 5 / 5 + x ^ 6 / 6 +
      x ^ 7 / 7 + x ^ 8 / 8 + x ^ 9 / (1 - x) ≤ x ^ 3 / 4 := by
    nlinarith
  nlinarith

theorem rowStabilityHPrime_lower
    {x : ℝ} (hx0 : 0 < x) (hxHalf : x ≤ 1 / 2) :
    x / 12 ≤ rowStabilityHPrime x := by
  have hnum := rowStabilityHPrime_numerator_lower hx0.le hxHalf
  have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx0
  calc
    x / 12 = (x ^ 3 / 12) / x ^ 2 := by
      field_simp [hx0.ne'] <;> ring
    _ ≤ (Real.log (1 - x) + x + x ^ 2 / 2 + 2 * x ^ 3 / 3) / x ^ 2 :=
      (div_le_div_iff_of_pos_right hx2).2 hnum
    _ = rowStabilityHPrime x := rfl

theorem rowStabilityH_half : rowStabilityH (1 / 2) = rowStabilityC := by
  rw [rowStabilityH, rowStabilityF, rowStabilityC]
  have hhalf : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, hhalf, Real.log_inv]
  norm_num
  ring

theorem rowStabilityH_mono
    {x y : ℝ} (hx0 : 0 < x) (hxy : x ≤ y) (hyHalf : y ≤ 1 / 2) :
    rowStabilityH x ≤ rowStabilityH y := by
  have hmono : MonotoneOn rowStabilityH (Set.Icc x y) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc x y)
      (fun z hz ↦ (hasDerivAt_rowStabilityH
        (by linarith [hz.1]) (by linarith [hz.2, hyHalf])).continuousAt.continuousWithinAt)
      (fun z hz ↦ by
        have hz' : z ∈ Set.Ioo x y := by simpa only [interior_Icc] using hz
        exact (hasDerivAt_rowStabilityH
          (by linarith [hz'.1]) (by linarith [hz'.2, hyHalf])).hasDerivWithinAt)
      (fun z hz ↦ by
        have hz' : z ∈ Set.Ioo x y := by simpa only [interior_Icc] using hz
        have hprime := rowStabilityHPrime_lower (x := z)
          (by linarith [hz'.1]) (by linarith [hz'.2, hyHalf])
        exact (show 0 ≤ z / 12 by linarith [hz'.1, hx0]).trans hprime)
  exact hmono ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy

/-- A concrete version of the paper's fixedValue `c₁`. -/
theorem rowStabilityH_gap_to_half
    {x : ℝ} (hxQuarter : 1 / 4 ≤ x) (hxHalf : x ≤ 1 / 2) :
    (1 / 48) * (1 / 2 - x) ≤ rowStabilityC - rowStabilityH x := by
  let corrected : ℝ → ℝ := fun z ↦ rowStabilityH z - z / 48
  have hmono : MonotoneOn corrected (Set.Icc x (1 / 2)) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc x (1 / 2))
      (fun z hz ↦ ((hasDerivAt_rowStabilityH
        (by linarith [hz.1, hxQuarter]) (by linarith [hz.2])).sub
          ((hasDerivAt_id z).div_const 48)).continuousAt.continuousWithinAt)
      (fun z hz ↦ by
        have hz' : z ∈ Set.Ioo x (1 / 2) := by simpa only [interior_Icc] using hz
        exact ((hasDerivAt_rowStabilityH
          (by linarith [hz'.1, hxQuarter]) (by linarith [hz'.2])).sub
            ((hasDerivAt_id z).div_const 48)).hasDerivWithinAt)
      (fun z hz ↦ by
        have hz' : z ∈ Set.Ioo x (1 / 2) := by simpa only [interior_Icc] using hz
        have hprime := rowStabilityHPrime_lower (x := z)
          (by linarith [hz'.1, hxQuarter]) (by linarith [hz'.2])
        change 0 ≤ rowStabilityHPrime z - 1 / 48
        calc
          0 ≤ z / 12 - 1 / 48 := by
            linarith [show (1 / 4 : ℝ) ≤ z by linarith [hz'.1, hxQuarter]]
          _ ≤ rowStabilityHPrime z - 1 / 48 := sub_le_sub_right hprime _)
  have h := hmono ⟨le_rfl, hxHalf⟩ ⟨hxHalf, le_rfl⟩ hxHalf
  dsimp [corrected] at h
  rw [rowStabilityH_half] at h
  linarith

/-- A concrete version of the paper's fixedValue `c₂`. -/
theorem rowStabilityH_half_argument_gap
    {x : ℝ} (hxQuarter : 1 / 4 ≤ x) (hxHalf : x ≤ 1 / 2) :
    (1 / 1536 : ℝ) ≤ rowStabilityH x - rowStabilityH (x / 2) := by
  let corrected : ℝ → ℝ := fun z ↦ rowStabilityH z - z / 96
  have hx2pos : 0 < x / 2 := by linarith
  have hmono : MonotoneOn corrected (Set.Icc (x / 2) x) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (x / 2) x)
      (fun z hz ↦ ((hasDerivAt_rowStabilityH
        (by linarith [hz.1, hxQuarter]) (by linarith [hz.2, hxHalf])).sub
          ((hasDerivAt_id z).div_const 96)).continuousAt.continuousWithinAt)
      (fun z hz ↦ by
        have hz' : z ∈ Set.Ioo (x / 2) x := by simpa only [interior_Icc] using hz
        exact ((hasDerivAt_rowStabilityH
          (by linarith [hz'.1, hxQuarter])
          (by linarith [hz'.2, hxHalf])).sub
            ((hasDerivAt_id z).div_const 96)).hasDerivWithinAt)
      (fun z hz ↦ by
        have hz' : z ∈ Set.Ioo (x / 2) x := by simpa only [interior_Icc] using hz
        have hprime := rowStabilityHPrime_lower (x := z)
          (by linarith [hz'.1, hxQuarter]) (by linarith [hz'.2, hxHalf])
        change 0 ≤ rowStabilityHPrime z - 1 / 96
        calc
          0 ≤ z / 12 - 1 / 96 := by
            linarith [show (1 / 8 : ℝ) ≤ z by linarith [hz'.1, hxQuarter]]
          _ ≤ rowStabilityHPrime z - 1 / 96 := sub_le_sub_right hprime _)
  have h := hmono ⟨le_rfl, by linarith [hx2pos]⟩
    ⟨by linarith [hx2pos], le_rfl⟩ (by linarith [hx2pos])
  dsimp [corrected] at h
  linarith [hxQuarter]

/-- Two indices attaining respectively the largest and second-largest
coordinates of a finite vector. -/
theorem exists_two_largest_coordinates
    {n : ℕ} (hn : 2 ≤ n) (p : Fin n → ℝ) :
    ∃ a b : Fin n, a ≠ b ∧
      (∀ j, p j ≤ p a) ∧ (∀ j, j ≠ a → p j ≤ p b) := by
  classical
  have huniv : (Finset.univ : Finset (Fin n)).Nonempty := by
    exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ p huniv
  have hcard : 1 < Fintype.card (Fin n) := by
    simpa only [Fintype.card_fin] using (show 1 < n by omega)
  obtain ⟨c, hca⟩ := Fintype.exists_ne_of_one_lt_card hcard a
  have herase : (Finset.univ.erase a : Finset (Fin n)).Nonempty :=
    ⟨c, Finset.mem_erase.mpr ⟨hca, Finset.mem_univ c⟩⟩
  obtain ⟨b, hbmem, hb⟩ :=
    Finset.exists_max_image (Finset.univ.erase a) p herase
  refine ⟨a, b, ?_, fun j ↦ ha j (Finset.mem_univ j), ?_⟩
  · exact (Finset.mem_erase.mp hbmem).1.symm
  · intro j hja
    exact hb j (Finset.mem_erase.mpr ⟨hja, Finset.mem_univ j⟩)

/-- The half--half vector supported on two distinct coordinates. -/
noncomputable def halfHalfVector
    {n : ℕ} (a b : Fin n) (j : Fin n) : ℝ :=
  if j = a ∨ j = b then 1 / 2 else 0

noncomputable def halfHalfL1Distance
    {n : ℕ} (p : Fin n → ℝ) (a b : Fin n) : ℝ :=
  ∑ j, |p j - halfHalfVector a b j|

/-- Exact decomposition of the distance into the two distinguished-coordinate
errors and the mass outside them. -/
theorem halfHalfL1Distance_eq
    {n : ℕ} {p : Fin n → ℝ} (hp : IsProbabilityVector p)
    {a b : Fin n} (hab : a ≠ b) :
    halfHalfL1Distance p a b =
      |p a - 1 / 2| + |p b - 1 / 2| + (1 - p a - p b) := by
  classical
  rw [halfHalfL1Distance]
  calc
    (∑ j, |p j - halfHalfVector a b j|) =
        ∑ j, ((if j = a then |p a - 1 / 2| else 0) +
          (if j = b then |p b - 1 / 2| else 0) +
          (if j ≠ a ∧ j ≠ b then p j else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hja : j = a
      · subst j
        simp [halfHalfVector, hab]
      · by_cases hjb : j = b
        · subst j
          simp [halfHalfVector, hja]
        · simp [halfHalfVector, hja, hjb,
            abs_of_nonneg (hp.nonnegative j)]
    _ = |p a - 1 / 2| + |p b - 1 / 2| +
          ∑ j, (if j ≠ a ∧ j ≠ b then p j else 0) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp
    _ = |p a - 1 / 2| + |p b - 1 / 2| + (1 - p a - p b) := by
      congr 1
      have htail : (∑ j, if j ≠ a ∧ j ≠ b then p j else 0) =
          ∑ j, if a ≠ j ∧ b ≠ j then p j else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hja : j = a
        · subst j; simp
        · by_cases hjb : j = b
          · subst j; simp
          · simp [hja, hjb, Ne.symm hja, Ne.symm hjb]
      rw [htail, sum_away_from_two hp hab]

theorem halfHalfL1Distance_of_below_half
    {n : ℕ} {p : Fin n → ℝ} (hp : IsProbabilityVector p)
    {a b : Fin n} (hab : a ≠ b)
    (ha0 : 0 ≤ p a) (hb0 : 0 ≤ p b)
    (haHalf : p a ≤ 1 / 2) (hbHalf : p b ≤ 1 / 2) :
    halfHalfL1Distance p a b = 2 * (1 - p a - p b) := by
  classical
  rw [halfHalfL1Distance]
  calc
    (∑ j, |p j - halfHalfVector a b j|) =
        ∑ j, ((if j = a then 1 / 2 - p a else 0) +
          (if j = b then 1 / 2 - p b else 0) +
          (if j ≠ a ∧ j ≠ b then p j else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hja : j = a
      · subst j
        have hsign : p a - (2 : ℝ)⁻¹ ≤ 0 := by
          norm_num at haHalf ⊢
          exact haHalf
        simp [halfHalfVector, hab, abs_of_nonpos hsign]
      · by_cases hjb : j = b
        · subst j
          have hsign : p b - (2 : ℝ)⁻¹ ≤ 0 := by
            norm_num at hbHalf ⊢
            exact hbHalf
          simp [halfHalfVector, hja, abs_of_nonpos hsign]
        · simp [halfHalfVector, hja, hjb, abs_of_nonneg (hp.nonnegative j)]
    _ = (∑ j, if j = a then 1 / 2 - p a else 0) +
          (∑ j, if j = b then 1 / 2 - p b else 0) +
          ∑ j, (if j ≠ a ∧ j ≠ b then p j else 0) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = 2 * (1 - p a - p b) := by
      have htail : (∑ j, if j ≠ a ∧ j ≠ b then p j else 0) =
          ∑ j, if a ≠ j ∧ b ≠ j then p j else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hja : j = a
        · subst j
          simp
        · by_cases hjb : j = b
          · subst j
            simp
          · simp [hja, hjb, Ne.symm hja, Ne.symm hjb]
      rw [htail, sum_away_from_two hp hab]
      simp
      ring

theorem halfHalfL1Distance_of_above_half
    {n : ℕ} {p : Fin n → ℝ} (hp : IsProbabilityVector p)
    {a b : Fin n} (hab : a ≠ b)
    (haHalf : 1 / 2 ≤ p a) (hb0 : 0 ≤ p b) (hbHalf : p b ≤ 1 / 2) :
    halfHalfL1Distance p a b =
      2 * (p a - 1 / 2) + 2 * (1 - p a - p b) := by
  classical
  rw [halfHalfL1Distance]
  calc
    (∑ j, |p j - halfHalfVector a b j|) =
        ∑ j, ((if j = a then p a - 1 / 2 else 0) +
          (if j = b then 1 / 2 - p b else 0) +
          (if j ≠ a ∧ j ≠ b then p j else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hja : j = a
      · subst j
        have hsign : 0 ≤ p a - (2 : ℝ)⁻¹ := by
          norm_num at haHalf ⊢
          exact haHalf
        simp [halfHalfVector, hab, abs_of_nonneg hsign]
      · by_cases hjb : j = b
        · subst j
          have hsign : p b - (2 : ℝ)⁻¹ ≤ 0 := by
            norm_num at hbHalf ⊢
            exact hbHalf
          simp [halfHalfVector, hja, abs_of_nonpos hsign]
        · simp [halfHalfVector, hja, hjb, abs_of_nonneg (hp.nonnegative j)]
    _ = (∑ j, if j = a then p a - 1 / 2 else 0) +
          (∑ j, if j = b then 1 / 2 - p b else 0) +
          ∑ j, (if j ≠ a ∧ j ≠ b then p j else 0) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = 2 * (p a - 1 / 2) + 2 * (1 - p a - p b) := by
      have htail : (∑ j, if j ≠ a ∧ j ≠ b then p j else 0) =
          ∑ j, if a ≠ j ∧ b ≠ j then p j else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hja : j = a
        · subst j
          simp
        · by_cases hjb : j = b
          · subst j
            simp
          · simp [hja, hjb, Ne.symm hja, Ne.symm hjb]
      rw [htail, sum_away_from_two hp hab]
      simp
      ring

/-- A fourth root expressed using square roots, convenient for ordered-real
reasoning. -/
noncomputable def fourthRoot (x : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt x)

theorem fourthRoot_nonneg (x : ℝ) : 0 ≤ fourthRoot x :=
  Real.sqrt_nonneg _

theorem le_fourthRoot_of_pow_four_le
    {x d : ℝ} (hx : 0 ≤ x) (hd : 0 ≤ d) (hpow : x ^ 4 ≤ d) :
    x ≤ fourthRoot d := by
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have hxsq : x ^ 2 ≤ Real.sqrt d := by
    rw [Real.le_sqrt hx2 hd]
    convert hpow using 1 <;> ring
  rw [fourthRoot, Real.le_sqrt hx (Real.sqrt_nonneg d)]
  exact hxsq

theorem self_le_fourthRoot
    {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    d ≤ fourthRoot d := by
  apply le_fourthRoot_of_pow_four_le hd0 hd0
  have hd2 : d ^ 2 ≤ d := by nlinarith
  nlinarith [sq_nonneg (d ^ 2 - d)]

theorem sum_rowStabilityF_eq
    {n : ℕ} (p : Fin n → ℝ) :
    (∑ i, rowStabilityF (p i)) =
      -(∑ i, (1 - p i) * Real.log (1 - p i)) +
        1 / 2 * (∑ i, (p i) ^ 2) +
        1 / 3 * (∑ i, (p i) ^ 3) := by
  simp only [rowStabilityF]
  calc
    (∑ i, (-(1 - p i) * Real.log (1 - p i) +
        p i ^ 2 / 2 + p i ^ 3 / 3)) =
        ∑ i, (-(1 - p i) * Real.log (1 - p i) +
          1 / 2 * p i ^ 2 + 1 / 3 * p i ^ 3) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = -(∑ i, (1 - p i) * Real.log (1 - p i)) +
          1 / 2 * (∑ i, p i ^ 2) + 1 / 3 * (∑ i, p i ^ 3) := by
      simp_rw [neg_mul]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

theorem rowStabilityF_eq_mul_H {x : ℝ} (hx : 0 < x) :
    rowStabilityF x = x * rowStabilityH x := by
  rw [rowStabilityH]
  field_simp [hx.ne']

/-- The separable defect is the average, under `p`, of the coordinate gaps
`C-h(p_i)`. -/
theorem separableDefect_eq_sum_gap
    {n : ℕ} {p : Fin n → ℝ} (hp : IsStrictProbabilityVector p) :
    rowStabilityC - ∑ i, rowStabilityF (p i) =
      ∑ i, p i * (rowStabilityC - rowStabilityH (p i)) := by
  have hF : (∑ i, rowStabilityF (p i)) =
      ∑ i, p i * rowStabilityH (p i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact rowStabilityF_eq_mul_H (hp.2 i)
  calc
    rowStabilityC - ∑ i, rowStabilityF (p i) =
        rowStabilityC * (∑ i, p i) -
          ∑ i, p i * rowStabilityH (p i) := by
      rw [hF, hp.1.sum_eq_one]
      ring
    _ = ∑ i, p i * (rowStabilityC - rowStabilityH (p i)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

noncomputable def tailSeparableDefect
    {n : ℕ} (p : Fin n → ℝ) (a : Fin n) : ℝ :=
  rowStabilityF (1 - p a) -
    ∑ j, if j ≠ a then rowStabilityF (p j) else 0

theorem separableDefect_eq_head_add_tail
    {n : ℕ} (p : Fin n → ℝ) (a : Fin n) :
    rowStabilityC - ∑ i, rowStabilityF (p i) =
      (rowStabilityC - rowStabilityF (p a) - rowStabilityF (1 - p a)) +
        tailSeparableDefect p a := by
  rw [tailSeparableDefect, sum_ite_ne_eq_sum_sub]
  ring

theorem tailSeparableDefect_eq_sum_gap
    {n : ℕ} {p : Fin n → ℝ} (hp : IsStrictProbabilityVector p)
    {a b : Fin n} (hab : a ≠ b) :
    tailSeparableDefect p a =
      ∑ j, if j ≠ a then
        p j * (rowStabilityH (1 - p a) - rowStabilityH (p j)) else 0 := by
  have hpa1 : p a < 1 := by
    have hbpos := hp.2 b
    have hbmem : b ∈ (Finset.univ.erase a : Finset (Fin n)) :=
      Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩
    have hb_le : p b ≤ ∑ j ∈ Finset.univ.erase a, p j :=
      Finset.single_le_sum (fun j _ ↦ hp.1.nonnegative j) hbmem
    have htotal := Finset.sum_erase_add (s := Finset.univ) (f := p)
      (Finset.mem_univ a)
    rw [hp.1.sum_eq_one] at htotal
    linarith
  have htailSum : (∑ j, if j ≠ a then p j else 0) = 1 - p a := by
    rw [sum_ite_ne_eq_sum_sub, hp.1.sum_eq_one]
  rw [tailSeparableDefect, rowStabilityF_eq_mul_H (sub_pos.mpr hpa1)]
  have hFtail : (∑ j, if j ≠ a then rowStabilityF (p j) else 0) =
      ∑ j, if j ≠ a then p j * rowStabilityH (p j) else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hja : j = a
    · simp [hja]
    · simpa [hja] using rowStabilityF_eq_mul_H (hp.2 j)
  rw [hFtail, ← htailSum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hja : j = a <;> simp [hja] <;> ring

/-- Paper (34): the row deficit dominates a separable defect. -/
theorem rowDeficit_ge_separable
    {n : ℕ} {p : Fin n → ℝ} (hp : IsStrictProbabilityVector p) :
    rowStabilityC - ∑ i, rowStabilityF (p i) ≤ rowDeficit p := by
  have hT := rowT_le_cubic_bound hp
  rw [rowDeficit, rowCorrection]
  rw [sum_rowStabilityF_eq]
  unfold rowStabilityC
  linarith

/-- In the variable `u = 2a-1`, this is the separable row defect
`C-F(a)-F(1-a)` from the proof of paper Lemma 8. -/
noncomputable def bernoulliExcess (u : ℝ) : ℝ :=
  (1 + u) / 2 * Real.log (1 + u) +
    (1 - u) / 2 * Real.log (1 - u) - u ^ 2 / 2

theorem hasDerivAt_bernoulliExcess
    {u : ℝ} (huLeft : -1 < u) (huRight : u < 1) :
    HasDerivAt bernoulliExcess
      (1 / 2 * Real.log ((1 + u) / (1 - u)) - u) u := by
  have hp : HasDerivAt (fun x : ℝ ↦ (1 + x) / 2) (1 / 2) u := by
    convert! ((hasDerivAt_const u 1).add (hasDerivAt_id u)).div_const 2 using 1 <;>
      ring
  have hm : HasDerivAt (fun x : ℝ ↦ (1 - x) / 2) (-1 / 2) u := by
    convert! ((hasDerivAt_const u 1).sub (hasDerivAt_id u)).div_const 2 using 1 <;>
      ring
  have hlp : HasDerivAt (fun x : ℝ ↦ Real.log (1 + x))
      (1 / (1 + u)) u := by
    convert! ((hasDerivAt_const u 1).add (hasDerivAt_id u)).log (by
      simpa using (show (1 : ℝ) + u ≠ 0 by linarith)) using 1 <;>
      simp
  have hlm : HasDerivAt (fun x : ℝ ↦ Real.log (1 - x))
      (-1 / (1 - u)) u := by
    convert! ((hasDerivAt_const u 1).sub (hasDerivAt_id u)).log (by
      simpa using (show (1 : ℝ) - u ≠ 0 by linarith)) using 1 <;>
      simp
  have hsq : HasDerivAt (fun x : ℝ ↦ x ^ 2 / 2) u u := by
    convert! (hasDerivAt_pow 2 u).div_const 2 using 1 <;> ring
  have h := (hp.mul hlp).add (hm.mul hlm) |>.sub hsq
  unfold bernoulliExcess
  convert! h using 1
  rw [Real.log_div (by linarith : 1 + u ≠ 0) (by linarith : 1 - u ≠ 0)]
  field_simp [(show 1 + u ≠ 0 by linarith),
    (show 1 - u ≠ 0 by linarith)] <;> ring

/-- The first two terms in the power series for `artanh`. -/
theorem one_add_cube_third_le_artanh
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    u + u ^ 3 / 3 ≤ Real.artanh u := by
  have hseries := Real.sum_range_le_log_div hu0 hu1 2
  rw [← Real.artanh_eq_half_log (by exact ⟨by linarith, hu1.le⟩)] at hseries
  norm_num [Finset.sum_range_succ] at hseries ⊢
  simpa [pow_succ] using hseries

noncomputable def correctedBernoulliExcess (u : ℝ) : ℝ :=
  bernoulliExcess u - u ^ 4 / 12

theorem hasDerivAt_correctedBernoulliExcess
    {u : ℝ} (huLeft : -1 < u) (huRight : u < 1) :
    HasDerivAt correctedBernoulliExcess
      (Real.artanh u - u - u ^ 3 / 3) u := by
  have hpow : HasDerivAt (fun x : ℝ ↦ x ^ 4 / 12) (u ^ 3 / 3) u := by
    convert! (hasDerivAt_pow 4 u).div_const 12 using 1 <;> ring
  have h := (hasDerivAt_bernoulliExcess huLeft huRight).sub hpow
  unfold correctedBernoulliExcess
  convert! h using 1
  rw [Real.artanh_eq_half_log (by exact ⟨huLeft.le, huRight.le⟩)]

/-- Quartic separation from the half--half equality case, paper (37). -/
theorem bernoulliExcess_quartic
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    u ^ 4 / 12 ≤ bernoulliExcess u := by
  have hmono : MonotoneOn correctedBernoulliExcess (Set.Icc 0 u) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 u)
      (fun y hy ↦ (hasDerivAt_correctedBernoulliExcess
        (by linarith [hy.1]) (by linarith [hy.2])).continuousAt.continuousWithinAt)
      (fun y hy ↦ by
        have hy' : y ∈ Set.Ioo 0 u := by
          simpa only [interior_Icc] using hy
        exact (hasDerivAt_correctedBernoulliExcess
          (by linarith [hy'.1]) (by linarith [hy'.2, hu1])).hasDerivWithinAt)
      (fun y hy ↦ by
        have hy' : y ∈ Set.Ioo 0 u := by
          simpa only [interior_Icc] using hy
        have hy0 : 0 ≤ y := by
          exact hy'.1.le
        have hy1 : y < 1 := by
          have := hy'.2
          linarith
        linarith [one_add_cube_third_le_artanh hy0 hy1])
  have h := hmono (show 0 ∈ Set.Icc (0 : ℝ) u by exact ⟨le_rfl, hu0⟩)
    (show u ∈ Set.Icc (0 : ℝ) u by exact ⟨hu0, le_rfl⟩) hu0
  simpa [correctedBernoulliExcess, bernoulliExcess] using h

theorem row_defect_eq_bernoulliExcess
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    rowStabilityC - rowStabilityF a - rowStabilityF (1 - a) =
      bernoulliExcess (2 * a - 1) := by
  have h1a : 0 < 1 - a := sub_pos.mpr ha1
  have hplus : 1 + (2 * a - 1) = 2 * a := by ring
  have hminus : 1 - (2 * a - 1) = 2 * (1 - a) := by ring
  rw [rowStabilityC, rowStabilityF, rowStabilityF, bernoulliExcess,
    hplus, hminus,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ha0.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) h1a.ne']
  ring

/-- Paper (37), in the original largest-coordinate variable. -/
theorem row_defect_quartic
    {a : ℝ} (haHalf : 1 / 2 ≤ a) (ha1 : a < 1) :
    4 / 3 * (a - 1 / 2) ^ 4 ≤
      rowStabilityC - rowStabilityF a - rowStabilityF (1 - a) := by
  have ha0 : 0 < a := by linarith
  have hu0 : 0 ≤ 2 * a - 1 := by linarith
  have hu1 : 2 * a - 1 < 1 := by linarith
  rw [row_defect_eq_bernoulliExcess ha0 ha1]
  have h := bernoulliExcess_quartic hu0 hu1
  convert h using 1 <;> ring

theorem halfHalfVector_nonnegative
    {n : ℕ} (a b j : Fin n) : 0 ≤ halfHalfVector a b j := by
  rw [halfHalfVector]
  split_ifs <;> norm_num

theorem sum_halfHalfVector
    {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    (∑ j, halfHalfVector a b j) = 1 := by
  classical
  simp only [halfHalfVector]
  have hrewrite :
      (∑ j : Fin n, if j = a ∨ j = b then (1 / 2 : ℝ) else 0) =
        ∑ j : Fin n, ((if j = a then (1 / 2 : ℝ) else 0) +
          (if j = b then (1 / 2 : ℝ) else 0)) := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hja : j = a
    · subst j
      simp [hab]
    · by_cases hjb : j = b <;> simp [hja, hjb, Ne.symm hab]
  rw [hrewrite, Finset.sum_add_distrib]
  norm_num

/-- The total-variation diameter of the probability simplex, specialized to
the half--half comparison vector. -/
theorem halfHalfL1Distance_le_two
    {n : ℕ} {p : Fin n → ℝ} (hp : IsProbabilityVector p)
    {a b : Fin n} (hab : a ≠ b) :
    halfHalfL1Distance p a b ≤ 2 := by
  rw [halfHalfL1Distance]
  calc
    (∑ j, |p j - halfHalfVector a b j|) ≤
        ∑ j, (p j + halfHalfVector a b j) := by
      apply Finset.sum_le_sum
      intro j _
      calc
        |p j - halfHalfVector a b j| ≤
            |p j| + |halfHalfVector a b j| :=
          abs_sub (p j) (halfHalfVector a b j)
        _ = p j + halfHalfVector a b j := by
          rw [abs_of_nonneg (hp.nonnegative j),
            abs_of_nonneg (halfHalfVector_nonnegative a b j)]
    _ = 2 := by
      rw [Finset.sum_add_distrib, hp.sum_eq_one, sum_halfHalfVector hab]
      norm_num

theorem rowStabilityH_gap_nonnegative
    {x : ℝ} (hx0 : 0 < x) (hxHalf : x ≤ 1 / 2) :
    0 ≤ rowStabilityC - rowStabilityH x := by
  rw [← rowStabilityH_half]
  exact sub_nonneg.mpr (rowStabilityH_mono hx0 hxHalf le_rfl)

/-- Coordinates below `1/4` pay a fixed per-unit-mass separable cost. -/
theorem rowStabilityH_gap_of_lt_quarter
    {x : ℝ} (hx0 : 0 < x) (hxQuarter : x < 1 / 4) :
    (1 / 192 : ℝ) ≤ rowStabilityC - rowStabilityH x := by
  have hmono := rowStabilityH_mono hx0 hxQuarter.le
    (show (1 / 4 : ℝ) ≤ 1 / 2 by norm_num)
  have hgap := rowStabilityH_gap_to_half
    (x := (1 / 4 : ℝ)) le_rfl (by norm_num)
  norm_num at hgap
  linarith

theorem separableDefect_nonnegative_of_le_half
    {n : ℕ} {p : Fin n → ℝ} (hp : IsStrictProbabilityVector p)
    (hhalf : ∀ i, p i ≤ 1 / 2) :
    0 ≤ rowStabilityC - ∑ i, rowStabilityF (p i) := by
  rw [separableDefect_eq_sum_gap hp]
  exact Finset.sum_nonneg (fun i _ ↦
    mul_nonneg (hp.1.nonnegative i)
      (rowStabilityH_gap_nonnegative (hp.2 i) (hhalf i)))

theorem separableDefect_ge_of_max_lt_quarter
    {n : ℕ} {p : Fin n → ℝ} (hp : IsStrictProbabilityVector p)
    {a : Fin n} (hmax : ∀ j, p j ≤ p a) (haQuarter : p a < 1 / 4) :
    (1 / 192 : ℝ) ≤ rowStabilityC - ∑ i, rowStabilityF (p i) := by
  rw [separableDefect_eq_sum_gap hp]
  calc
    (1 / 192 : ℝ) = ∑ i, p i / 192 := by
      rw [← Finset.sum_div, hp.1.sum_eq_one]
    _ ≤ ∑ i, p i * (rowStabilityC - rowStabilityH (p i)) := by
      apply Finset.sum_le_sum
      intro i _
      have hgap := rowStabilityH_gap_of_lt_quarter (hp.2 i)
        (lt_of_le_of_lt (hmax i) haQuarter)
      have hmul := mul_le_mul_of_nonneg_left hgap (hp.1.nonnegative i)
      nlinarith

theorem separableDefect_ge_tail_below_quarter
    {n : ℕ} {p : Fin n → ℝ} (hp : IsStrictProbabilityVector p)
    {a b : Fin n} (hsecond : ∀ j, j ≠ a → p j ≤ p b)
    (haHalf : p a ≤ 1 / 2) (hbQuarter : p b < 1 / 4) :
    (1 - p a) / 192 ≤ rowStabilityC - ∑ i, rowStabilityF (p i) := by
  rw [separableDefect_eq_sum_gap hp]
  calc
    (1 - p a) / 192 = ∑ i, if i ≠ a then p i / 192 else 0 := by
      have hsum : (∑ i, if i ≠ a then p i else 0) = 1 - p a := by
        rw [sum_ite_ne_eq_sum_sub, hp.1.sum_eq_one]
      calc
        (1 - p a) / 192 =
            (∑ i, if i ≠ a then p i else 0) / 192 := by rw [hsum]
        _ = ∑ i, (if i ≠ a then p i else 0) / 192 := by
          simpa using (Finset.sum_div Finset.univ
            (fun i : Fin n ↦ if i ≠ a then p i else 0) (192 : ℝ))
        _ = ∑ i, if i ≠ a then p i / 192 else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hia : i = a <;> simp [hia]
    _ ≤ ∑ i, p i * (rowStabilityC - rowStabilityH (p i)) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hia : i = a
      · simp only [hia, ne_eq, not_true_eq_false, if_false]
        exact mul_nonneg (hp.1.nonnegative a)
          (rowStabilityH_gap_nonnegative (hp.2 a) haHalf)
      · have hgap := rowStabilityH_gap_of_lt_quarter (hp.2 i)
          (lt_of_le_of_lt (hsecond i hia) hbQuarter)
        have hmul := mul_le_mul_of_nonneg_left hgap (hp.1.nonnegative i)
        simpa [hia, div_eq_mul_inv] using hmul

theorem separableDefect_ge_two_coordinates
    {n : ℕ} {p : Fin n → ℝ} (hp : IsStrictProbabilityVector p)
    {a b : Fin n} (hab : a ≠ b) (hhalf : ∀ i, p i ≤ 1 / 2)
    (haQuarter : 1 / 4 ≤ p a) (hbQuarter : 1 / 4 ≤ p b) :
    (1 / 192 : ℝ) * (1 - p a - p b) ≤
      rowStabilityC - ∑ i, rowStabilityF (p i) := by
  let f : Fin n → ℝ := fun i ↦
    p i * (rowStabilityC - rowStabilityH (p i))
  have hfnon : ∀ i, 0 ≤ f i := fun i ↦
    mul_nonneg (hp.1.nonnegative i)
      (rowStabilityH_gap_nonnegative (hp.2 i) (hhalf i))
  have hcoord : ∀ {i : Fin n}, 1 / 4 ≤ p i →
      (1 / 192 : ℝ) * (1 / 2 - p i) ≤ f i := by
    intro i hiQuarter
    have hgap := rowStabilityH_gap_to_half hiQuarter (hhalf i)
    calc
      (1 / 192 : ℝ) * (1 / 2 - p i) =
          (1 / 4) * ((1 / 48) * (1 / 2 - p i)) := by ring
      _ ≤ p i * ((1 / 48) * (1 / 2 - p i)) :=
        mul_le_mul_of_nonneg_right hiQuarter
          (mul_nonneg (by norm_num) (sub_nonneg.mpr (hhalf i)))
      _ ≤ p i * (rowStabilityC - rowStabilityH (p i)) :=
        mul_le_mul_of_nonneg_left hgap (hp.1.nonnegative i)
      _ = f i := rfl
  have hbmem : b ∈ (Finset.univ.erase a : Finset (Fin n)) :=
    Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩
  have hb_le : f b ≤ ∑ i ∈ Finset.univ.erase a, f i :=
    Finset.single_le_sum (fun i _ ↦ hfnon i) hbmem
  have hdecomp := Finset.sum_erase_add (s := Finset.univ) (f := f)
    (Finset.mem_univ a)
  rw [separableDefect_eq_sum_gap hp]
  change (1 / 192 : ℝ) * (1 - p a - p b) ≤ ∑ i, f i
  have haLower := hcoord haQuarter
  have hbLower := hcoord hbQuarter
  nlinarith

/-- Quantitative stability when the largest coordinate is at most `1/2`.
The small-deficit hypothesis forces the two largest coordinates into the
interval `[1/4,1/2]`, where the explicit linear gap estimate applies. -/
theorem below_half_distance_le_rowDeficit
    {n : ℕ} {p : Fin n → ℝ} (hp : IsStrictProbabilityVector p)
    {a b : Fin n} (hab : a ≠ b)
    (hmax : ∀ j, p j ≤ p a) (hsecond : ∀ j, j ≠ a → p j ≤ p b)
    (haHalf : p a ≤ 1 / 2)
    (hsep : rowStabilityC - ∑ i, rowStabilityF (p i) ≤ rowDeficit p)
    (hdsmall : rowDeficit p < 1 / 768) :
    halfHalfL1Distance p a b ≤ 384 * rowDeficit p := by
  have hhalf : ∀ i, p i ≤ 1 / 2 := fun i ↦ (hmax i).trans haHalf
  have haQuarter : 1 / 4 ≤ p a := by
    by_contra h
    have hcost := separableDefect_ge_of_max_lt_quarter hp hmax
      (lt_of_not_ge h)
    linarith
  have hbQuarter : 1 / 4 ≤ p b := by
    by_contra h
    have hcost := separableDefect_ge_tail_below_quarter hp hsecond haHalf
      (lt_of_not_ge h)
    have htail : 1 / 2 ≤ 1 - p a := by linarith
    linarith
  have hcost := separableDefect_ge_two_coordinates hp hab hhalf
    haQuarter hbQuarter
  rw [halfHalfL1Distance_of_below_half hp.1 hab
    (hp.1.nonnegative a) (hp.1.nonnegative b) haHalf (hhalf b)]
  nlinarith

theorem coordinate_le_complement
    {n : ℕ} {p : Fin n → ℝ} (hp : IsProbabilityVector p)
    {a j : Fin n} (hja : j ≠ a) : p j ≤ 1 - p a := by
  have hjmem : j ∈ (Finset.univ.erase a : Finset (Fin n)) :=
    Finset.mem_erase.mpr ⟨hja, Finset.mem_univ j⟩
  have hjle : p j ≤ ∑ k ∈ Finset.univ.erase a, p k :=
    Finset.single_le_sum (fun k _ ↦ hp.nonnegative k) hjmem
  have htotal := Finset.sum_erase_add (s := Finset.univ) (f := p)
    (Finset.mem_univ a)
  rw [hp.sum_eq_one] at htotal
  linarith

theorem tailSeparableDefect_nonnegative
    {n : ℕ} {p : Fin n → ℝ} (hp : IsStrictProbabilityVector p)
    {a b : Fin n} (hab : a ≠ b) (haHalf : 1 / 2 ≤ p a) :
    0 ≤ tailSeparableDefect p a := by
  rw [tailSeparableDefect_eq_sum_gap hp hab]
  apply Finset.sum_nonneg
  intro j _
  by_cases hja : j = a
  · simp [hja]
  · have hmono := rowStabilityH_mono (hp.2 j)
      (coordinate_le_complement hp.1 hja)
      (show 1 - p a ≤ 1 / 2 by linarith)
    simpa [hja] using
      mul_nonneg (hp.1.nonnegative j) (sub_nonneg.mpr hmono)

theorem coordinate_le_outside_two
    {n : ℕ} {p : Fin n → ℝ} (hp : IsProbabilityVector p)
    {a b j : Fin n} (hab : a ≠ b) (hja : j ≠ a) (hjb : j ≠ b) :
    p j ≤ 1 - p a - p b := by
  have hterm : p j = if a ≠ j ∧ b ≠ j then p j else 0 := by
    simp [Ne.symm hja, Ne.symm hjb]
  rw [hterm, ← sum_away_from_two hp hab]
  exact Finset.single_le_sum
    (f := fun k ↦ if a ≠ k ∧ b ≠ k then p k else 0)
    (fun k _ ↦ by
      by_cases h : a ≠ k ∧ b ≠ k <;> simp [h, hp.nonnegative k])
    (Finset.mem_univ j)

/-- If the largest coordinate exceeds `1/2`, the tail's separable defect
controls the mass outside the two largest coordinates. -/
theorem tailSeparableDefect_ge_second_gap
    {n : ℕ} {p : Fin n → ℝ} (hp : IsStrictProbabilityVector p)
    {a b : Fin n} (hab : a ≠ b)
    (hsecond : ∀ j, j ≠ a → p j ≤ p b)
    (haHalf : 1 / 2 ≤ p a) (hqQuarter : 1 / 4 ≤ 1 - p a) :
    (1 - p a - p b) / 1536 ≤ tailSeparableDefect p a := by
  have hqHalf : 1 - p a ≤ 1 / 2 := by linarith
  have hgapHalf := rowStabilityH_half_argument_gap hqQuarter hqHalf
  rw [tailSeparableDefect_eq_sum_gap hp hab]
  by_cases hcase : 1 - p a - p b ≤ (1 - p a) / 2
  · calc
      (1 - p a - p b) / 1536 =
          ∑ j, if j ≠ a ∧ j ≠ b then p j / 1536 else 0 := by
        have hout : (∑ j, if a ≠ j ∧ b ≠ j then p j else 0) =
            1 - p a - p b := sum_away_from_two hp.1 hab
        have horient : (∑ j, if j ≠ a ∧ j ≠ b then p j else 0) =
            1 - p a - p b := by
          calc
            (∑ j, if j ≠ a ∧ j ≠ b then p j else 0) =
                ∑ j, if a ≠ j ∧ b ≠ j then p j else 0 := by
              apply Finset.sum_congr rfl
              intro j _
              by_cases hja : j = a
              · subst j; simp
              · by_cases hjb : j = b
                · subst j; simp
                · simp [hja, hjb, Ne.symm hja, Ne.symm hjb]
            _ = 1 - p a - p b := hout
        calc
          (1 - p a - p b) / 1536 =
              (∑ j, if j ≠ a ∧ j ≠ b then p j else 0) / 1536 := by
            rw [horient]
          _ = ∑ j, (if j ≠ a ∧ j ≠ b then p j else 0) / 1536 := by
            simpa using (Finset.sum_div Finset.univ
              (fun j : Fin n ↦ if j ≠ a ∧ j ≠ b then p j else 0) (1536 : ℝ))
          _ = ∑ j, if j ≠ a ∧ j ≠ b then p j / 1536 else 0 := by
            apply Finset.sum_congr rfl
            intro j _
            by_cases h : j ≠ a ∧ j ≠ b <;> simp [h]
      _ ≤ ∑ j, if j ≠ a then
          p j * (rowStabilityH (1 - p a) - rowStabilityH (p j)) else 0 := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hja : j = a
        · simp [hja]
        · by_cases hjb : j = b
          · subst j
            have hble := coordinate_le_complement hp.1 (Ne.symm hab)
            have hmono := rowStabilityH_mono (hp.2 b) hble hqHalf
            simpa [Ne.symm hab] using
              mul_nonneg (hp.1.nonnegative b) (sub_nonneg.mpr hmono)
          · have hpjHalf : p j ≤ (1 - p a) / 2 :=
              (coordinate_le_outside_two hp.1 hab hja hjb).trans hcase
            have hmono := rowStabilityH_mono (hp.2 j) hpjHalf
              (show (1 - p a) / 2 ≤ 1 / 2 by linarith)
            have hgap : (1 / 1536 : ℝ) ≤
                rowStabilityH (1 - p a) - rowStabilityH (p j) := by
              linarith
            have hmul := mul_le_mul_of_nonneg_left hgap (hp.1.nonnegative j)
            simpa [hja, hjb, div_eq_mul_inv] using hmul
  · have htailMass :
        (∑ j, if j ≠ a then p j else 0) = 1 - p a := by
        rw [sum_ite_ne_eq_sum_sub, hp.1.sum_eq_one]
    have hsumLower : (1 - p a) / 1536 ≤
        ∑ j, if j ≠ a then
          p j * (rowStabilityH (1 - p a) - rowStabilityH (p j)) else 0 := by
      calc
        (1 - p a) / 1536 =
            ∑ j, if j ≠ a then p j / 1536 else 0 := by
          calc
            (1 - p a) / 1536 =
                (∑ j, if j ≠ a then p j else 0) / 1536 := by
              rw [htailMass]
            _ = ∑ j, (if j ≠ a then p j else 0) / 1536 := by
              simpa using (Finset.sum_div Finset.univ
                (fun j : Fin n ↦ if j ≠ a then p j else 0) (1536 : ℝ))
            _ = ∑ j, if j ≠ a then p j / 1536 else 0 := by
              apply Finset.sum_congr rfl
              intro j _
              by_cases hja : j = a <;> simp [hja]
        _ ≤ ∑ j, if j ≠ a then
            p j * (rowStabilityH (1 - p a) - rowStabilityH (p j)) else 0 := by
          apply Finset.sum_le_sum
          intro j _
          by_cases hja : j = a
          · simp [hja]
          · have hpbHalf : p b ≤ (1 - p a) / 2 := by
              have hpb0 := hp.1.nonnegative b
              have := lt_of_not_ge hcase
              linarith
            have hpjHalf := (hsecond j hja).trans hpbHalf
            have hmono := rowStabilityH_mono (hp.2 j) hpjHalf
              (show (1 - p a) / 2 ≤ 1 / 2 by linarith)
            have hgap : (1 / 1536 : ℝ) ≤
                rowStabilityH (1 - p a) - rowStabilityH (p j) := by
              linarith
            have hmul := mul_le_mul_of_nonneg_left hgap (hp.1.nonnegative j)
            simpa [hja, div_eq_mul_inv] using hmul
    have htail_ge : 1 - p a - p b ≤ 1 - p a := by
      linarith [hp.1.nonnegative b]
    linarith

/-- Quantitative stability when the largest coordinate is at least `1/2`.
The quartic head gap controls its displacement from `1/2`, while the linear
tail gap controls the mass outside the two largest coordinates. -/
theorem above_half_distance_le_rowDeficit
    {n : ℕ} {p : Fin n → ℝ} (hp : IsStrictProbabilityVector p)
    {a b : Fin n} (hab : a ≠ b)
    (hsecond : ∀ j, j ≠ a → p j ≤ p b)
    (haHalf : 1 / 2 ≤ p a)
    (hsep : rowStabilityC - ∑ i, rowStabilityF (p i) ≤ rowDeficit p)
    (hdsmall : rowDeficit p < 1 / 768) :
    halfHalfL1Distance p a b ≤
      2 * fourthRoot (rowDeficit p) + 3072 * rowDeficit p := by
  have hpbq := coordinate_le_complement hp.1 (Ne.symm hab)
  have hpa1 : p a < 1 := by linarith [hp.2 b]
  have htailNonneg := tailSeparableDefect_nonnegative hp hab haHalf
  have hdecomp := separableDefect_eq_head_add_tail p a
  have hquart := row_defect_quartic haHalf hpa1
  have hhead_le : 4 / 3 * (p a - 1 / 2) ^ 4 ≤
      rowStabilityC - ∑ i, rowStabilityF (p i) := by
    linarith
  have hqQuarter : 1 / 4 ≤ 1 - p a := by
    by_contra h
    have hx : (1 / 4 : ℝ) ≤ p a - 1 / 2 := by
      linarith [lt_of_not_ge h]
    have hpow : (1 / 4 : ℝ) ^ 4 ≤ (p a - 1 / 2) ^ 4 :=
      pow_le_pow_left₀ (by norm_num) hx 4
    norm_num at hpow
    linarith
  have htailGap := tailSeparableDefect_ge_second_gap hp hab hsecond
    haHalf hqQuarter
  have htail_le : tailSeparableDefect p a ≤
      rowStabilityC - ∑ i, rowStabilityF (p i) := by
    have hhead0 : 0 ≤ 4 / 3 * (p a - 1 / 2) ^ 4 :=
      mul_nonneg (by norm_num) (pow_nonneg (by linarith) 4)
    linarith
  have houtside : 1 - p a - p b ≤ 1536 * rowDeficit p := by
    linarith
  have hpowD : (p a - 1 / 2) ^ 4 ≤ rowDeficit p := by
    have hxnon : 0 ≤ (p a - 1 / 2) ^ 4 := pow_nonneg (by linarith) 4
    nlinarith
  have hd0 : 0 ≤ rowDeficit p :=
    (pow_nonneg (by linarith : 0 ≤ p a - 1 / 2) 4).trans hpowD
  have hroot : p a - 1 / 2 ≤ fourthRoot (rowDeficit p) :=
    le_fourthRoot_of_pow_four_le (by linarith) hd0 hpowD
  have hbHalf : p b ≤ 1 / 2 := hpbq.trans (by linarith)
  rw [halfHalfL1Distance_of_above_half hp.1 hab haHalf
    (hp.1.nonnegative b) hbHalf]
  linarith

/-- A fully explicit, strict-support version of paper Lemma 8.  The sharp
one-row inequality is kept as an explicit argument for modularity and is
proved in `SourceAnariRezaeiList`; all stability and compactness arguments are
discharged here with the concrete fixedValue `3074`.  Strict support is exactly
the case used for rows of the Gibbs marginal matrix associated with a positive
input matrix. -/
theorem row_stability_explicit
    (hrow : AnariRezaeiRowInequality)
    {n : ℕ} (hn : 2 ≤ n) (p : Fin n → ℝ)
    (hp : IsStrictProbabilityVector p) :
    ∃ a b : Fin n, a ≠ b ∧
      halfHalfL1Distance p a b ≤ 3074 * fourthRoot (rowDeficit p) := by
  obtain ⟨a, b, hab, hmax, hsecond⟩ := exists_two_largest_coordinates hn p
  refine ⟨a, b, hab, ?_⟩
  have hd0 : 0 ≤ rowDeficit p := hrow hn p hp.1
  have hsep := rowDeficit_ge_separable hp
  by_cases hdsmall : rowDeficit p < 1 / 768
  · have hd1 : rowDeficit p ≤ 1 := by linarith
    have hdroot := self_le_fourthRoot hd0 hd1
    by_cases haHalf : p a ≤ 1 / 2
    · have hdist := below_half_distance_le_rowDeficit hp hab hmax hsecond
          haHalf hsep hdsmall
      nlinarith [fourthRoot_nonneg (rowDeficit p)]
    · have hdist := above_half_distance_le_rowDeficit hp hab hsecond
          (le_of_not_ge haHalf) hsep hdsmall
      nlinarith [fourthRoot_nonneg (rowDeficit p)]
  · have hdist := halfHalfL1Distance_le_two hp.1 hab
    have hdlarge : 1 / 768 ≤ rowDeficit p := le_of_not_gt hdsmall
    by_cases hd1 : rowDeficit p ≤ 1
    · have hdroot := self_le_fourthRoot hd0 hd1
      nlinarith
    · have hone : (1 : ℝ) ≤ fourthRoot (rowDeficit p) := by
        apply le_fourthRoot_of_pow_four_le (by norm_num) hd0
        norm_num
        exact le_of_not_ge hd1
      nlinarith

end BeyondBethe
