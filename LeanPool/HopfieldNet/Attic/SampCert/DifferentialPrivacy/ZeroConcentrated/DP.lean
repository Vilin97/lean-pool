/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Algebra.Group.Basic
import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.ZeroConcentrated.ConcentratedBound
import LeanPool.HopfieldNet.SampCert.SLang
import LeanPool.HopfieldNet.SampCert.Samplers.GaussianGen.Basic
import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Neighbours
import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Sensitivity
import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Generic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Integral
import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Pure.DP

import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Generic
import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Approximate.DP

/-!
# Zero Concentrated Differential Privacy

This file defines zero concentrated differential privacy (zCDP).
-/

open Classical

variable { T : Type }

noncomputable section

namespace SLang

/--
Inequality defining ``(ε^2)/2``-zCDP.

All ``ε``-DP mechanisms satisfy this bound (though not all mechanisms
satisfying this bound are ``ε``-DP).
-/
def zCDPBound (q : List T → PMF U) (ε : ℝ) : Prop :=
  ∀ α : ℝ, 1 < α → ∀ l₁ l₂ : List T, Neighbour l₁ l₂ →
  RenyiDivergence (q l₁) (q l₂) α ≤ ENNReal.ofReal ((1/2) * ε ^ 2 * α)

/--
All neighbouring queries are absolutely continuous
-/
def ACNeighbour (p : List T -> PMF  U) : Prop := ∀ l₁ l₂, Neighbour l₁ l₂ -> AbsCts (p l₁) (p l₂)

/--
The mechanism ``q`` is ``(ε^2)/2``-zCDP
-/
def zCDP (q : List T → PMF U) (ε : NNReal) : Prop := ACNeighbour q ∧ zCDPBound q ε

lemma zCDP_mono {m : List T -> PMF U} {ε₁ ε₂ : NNReal} (H : ε₁ ≤ ε₂) (Hε : zCDP m ε₁) : zCDP m ε₂ := by
  rcases Hε with ⟨ Hac , Hε ⟩
  rw [zCDP] at *
  apply And.intro
  · assumption
  · rw [zCDPBound] at *
    intro α Hα l₁ l₂ N
    apply (@le_trans _ _ _ (ENNReal.ofReal (1 / 2 * ↑ε₁ ^ 2 * α)) _ (Hε α Hα l₁ l₂ N))
    apply ENNReal.coe_mono
    refine (Real.toNNReal_le_toNNReal_iff ?a.hp).mpr ?a.a
    · apply mul_nonneg
      · apply mul_nonneg
        · simp
        · simp
      · linarith
    · repeat rw [mul_assoc]
      apply (mul_le_mul_iff_of_pos_left (by simp)).mpr
      apply (mul_le_mul_iff_of_pos_right (by linarith)).mpr
      apply pow_le_pow_left' H (OfNat.ofNat 2)

/--
Obtain an approximate DP bound from a zCDP bound, when ε > 0 and δ < 1
-/
lemma ApproximateDP_of_zCDP_pos_lt_one [Countable U] (m : Mechanism T U)
  (ε : ℝ) (Hε_pos : 0 < ε) (h : zCDPBound m ε) (Hm : ACNeighbour m) :
  ∀ δ : NNReal, (0 < (δ : ℝ)) -> ((δ : ℝ) < 1) -> DP' m (ε^2/2 + ε * (2*Real.log (1/δ))^(1/2 : ℝ)) δ := by
  have Hε : 0 ≤ ε := by exact le_of_lt Hε_pos
  intro δ Hδ0 Hδ1
  generalize Dε' : (ε^2/2 + ε * (2*Real.log (1/δ))^(1/2 : ℝ)) = ε'
  simp [zCDPBound] at h
  simp [DP']
  have Hε' : 0 ≤ ε' := by
    rw [<- Dε']
    apply add_nonneg
    · apply div_nonneg
      · apply sq_nonneg
      · simp
    · apply mul_nonneg
      · trivial
      · apply Real.rpow_nonneg
        apply mul_nonneg
        · simp
        · apply Real.log_nonneg
          apply one_le_one_div Hδ0
          exact le_of_lt Hδ1
  intros l₁ l₂ neighs S


  -- Different value of α from the paper, since our definition of ε-zCDP is their (1/2)ε^2-zCDP
  let α : Real := ((1 / ε) * (2*Real.log (1/δ))^(1/2 : ℝ)) + 1
  have Dα : α = (((1 / ε) * (2*Real.log (1/δ))^(1/2 : ℝ)) + 1 : ℝ) := by rfl
  have Hα : (1 < α) := by
    rw [Dα]
    conv =>
      lhs
      rw [<- zero_add 1]
    apply (add_lt_add_iff_right 1).mpr
    conv =>
      lhs
      rw [<- mul_zero 0]
    apply mul_lt_mul_of_nonneg_of_pos
    · apply one_div_pos.mpr
      trivial
    · apply Real.rpow_nonneg
      apply mul_nonneg
      · simp
      · apply Real.log_nonneg
        apply one_le_one_div Hδ0
        exact le_of_lt Hδ1
    · simp
    · apply Real.rpow_pos_of_pos
      apply Real.mul_pos
      · simp
      · apply Real.log_pos
        apply one_lt_one_div
        · apply Hδ0
        · trivial
  have Hα' : (0 < α.toEReal - 1) := by
    rw [EReal.coe_add]
    simp only [one_div, mul_neg, EReal.coe_mul, EReal.coe_one]
    rw [add_sub_assoc]
    have HZ : (1 - 1 : EReal) = 0 := by
      rw [← EReal.coe_one]
      rw [← EReal.coe_sub]
      simp
    rw [HZ]
    simp only [mul_neg, add_zero, gt_iff_lt]
    apply EReal.mul_pos
    · apply EReal.coe_pos.mpr
      exact inv_pos_of_pos Hε_pos
    · apply EReal.coe_pos.mpr
      apply Real.rpow_pos_of_pos
      apply Real.mul_pos
      · simp
      · apply Real.log_pos
        exact one_lt_inv Hδ0 Hδ1
  have HαSpecial : ENNReal.eexp (((α - 1)) * ENNReal.ofReal (2⁻¹ * ε ^ 2 * α)) ≤ ENNReal.ofReal (Real.exp ((α - 1) * ε')) * ↑δ := by
    apply Eq.le
    rw [Dα]
    -- Cancel 1 - 1
    conv =>
      enter [1, 1, 1]
      simp
      rw [add_sub_assoc]
      rw [← EReal.coe_one]
      rw [← EReal.coe_sub]
      simp
    conv =>
      enter [2, 1, 1, 1, 1]
      simp
    simp only [one_div, EReal.coe_ennreal_ofReal]
    repeat rw [← EReal.coe_mul]
    rw [ENNReal.eexp_ofReal]
    rw [ENNReal.ofReal]
    rw [ENNReal.ofReal]
    rw [← ENNReal.coe_mul]
    congr 1
    rw [<- @Real.toNNReal_coe δ]
    rw [<- Real.toNNReal_mul ?G1]
    case G1 => apply Real.exp_nonneg
    congr 1
    conv =>
      enter [2, 2]
      rw [<- @Real.exp_log (δ.toReal) Hδ0]
    conv =>
      enter [2]
      rw [<- Real.exp_add]
    congr 1
    simp only [Real.toNNReal_coe]
    rw [max_eq_left ?G5]
    case G5 =>
      apply mul_nonneg
      · apply mul_nonneg
        · simp
        · apply sq_nonneg
      · apply add_nonneg
        · apply mul_nonneg
          · apply inv_nonneg_of_nonneg
            trivial
          · apply Real.rpow_nonneg
            apply mul_nonneg
            · simp
            · apply Real.log_nonneg
              apply one_le_inv Hδ0
              exact le_of_lt Hδ1
        · simp
    rw [<- Dε']
    simp
    repeat rw [mul_add]


    have SC1 : 0 < -(2 * Real.log δ.toReal) := by
      simp
      apply mul_neg_of_pos_of_neg
      · simp
      · exact Real.log_neg Hδ0 Hδ1

    -- Cancel square roots
    conv =>
      congr
      · congr
        · skip
          rw [mul_comm]
          repeat rw [mul_assoc]
          enter [2, 2, 2]
          rw [mul_comm]
          rw [mul_assoc]
          enter [2]
          rw [<- Real.rpow_add SC1]
          rw [<- two_mul]
          simp
        · simp
      · enter [1, 2]
        repeat rw [mul_assoc]
        enter [2]
        rw [mul_comm]
        rw [mul_assoc]
        enter [2]
        rw [<- Real.rpow_add SC1]
        rw [<- two_mul]
        simp
    clear SC1

    have SC1 : ε ≠ 0 := by linarith
    conv =>
      congr
      · congr
        · enter [2]
          repeat rw [<- mul_assoc]
          enter [1]
          rw [sq]
          simp
          rw [mul_inv_cancel SC1]
        · rw [sq]
          rw [mul_comm]
          repeat rw [mul_assoc]
          enter [2, 2]
          repeat rw [<- mul_assoc]
          enter [1]
          rw [mul_inv_cancel SC1]
          skip
      · enter [1]
        congr
        · rw [division_def]
          rw [sq]
          repeat rw [mul_assoc]
          rw [mul_comm]
          rw [mul_assoc]
          enter [2]
          rw [mul_comm]
          repeat rw [<- mul_assoc]
          enter [1, 1]
          rw [inv_mul_cancel SC1]
          skip
        · repeat rw [<- mul_assoc]
          rw [inv_mul_cancel SC1]
          simp
    clear SC1
    simp

    -- Quality of life
    have R1 : (-(2 * Real.log δ.toReal)) = 2 * Real.log (1/δ.toReal) := by simp
    rw [R1]
    have R2 : (-Real.log δ.toReal) = Real.log (1/δ.toReal) := by simp
    rw [R2]
    generalize HD : Real.log (1 / δ.toReal) = D
    have HDnn : 0 ≤ D := by
      rw [<- HD]
      apply Real.log_nonneg
      apply one_le_one_div Hδ0
      exact le_of_lt Hδ1
    clear R1 R2

    -- Simplify more
    conv =>
      congr
      · rw [Real.mul_rpow (by simp) HDnn]
        enter [2]
        repeat rw [<- mul_assoc]
        enter [1]
        rw [mul_comm]
        rw [<- mul_assoc]
        enter [1]
        rw [<- Real.rpow_neg_one]
        rw [<- Real.rpow_add (by simp)]
      · rw [Real.mul_rpow (by simp) HDnn]
        enter [1, 1]
        rw [mul_comm]
        repeat rw [mul_assoc]
        enter [2]
        repeat rw [<- mul_assoc]
        enter [1]
        rw [<- Real.rpow_neg_one]
        rw [<- Real.rpow_add (by simp)]
        rw [add_comm]

    generalize HW : (2 : ℝ) ^ ((2 : ℝ) ^ (-(1 : ℝ)) + -(1 : ℝ) : ℝ) = W
    -- Cancel the ε * W * D terms
    conv =>
      enter [1]
      rw [add_comm]
      enter [1, 1]
      rw [mul_comm]
    conv =>
      enter [2, 1, 1]
      repeat rw [<- mul_assoc]
    rw [add_assoc]
    congr 1
    clear HW W

    -- Cancel the D terms
    rw [<- one_add_one_eq_two]
    rw [add_mul]
    rw [<- HD]
    simp


  -- Privacy loss random variable
  -- Move to RenyiDivergence file?
  let z (x : U) : EReal := ENNReal.elog ((m l₁ x) / (m l₂ x))
  have Hz (x : U) : z x = ENNReal.elog ((m l₁ x) / (m l₂ x)) := by rfl
  -- Instead of using an outer measure (like in PMF.toMeasure) I'll use a sum of Dirac measures,
  -- so we can turn the lintegral into a sum. The other wya might work too.
  let m1_measure_elt (u : U) : @MeasureTheory.Measure U ⊤ := m l₁ u • @MeasureTheory.Measure.dirac U ⊤ u
  let m1_measure : @MeasureTheory.Measure U ⊤ := MeasureTheory.Measure.sum m1_measure_elt
  have m1_measure_lintegral_sum (f : U -> ENNReal) :
       ∫⁻ (a : U), (f a) ∂m1_measure = ∑'(a : U), (m l₁ a * f a) := by
    rw [MeasureTheory.lintegral_sum_measure]
    apply tsum_congr
    intro u
    rw [MeasureTheory.lintegral_smul_measure]
    rw [@MeasureTheory.lintegral_dirac _]
  have m1_measure_eval (P : U -> Prop) :  m1_measure {x | P x} = ∑'(u : U), m l₁ u * if P u then 1 else 0 := by
    rw [MeasureTheory.Measure.sum_apply m1_measure_elt trivial]
    apply tsum_congr
    intro u
    rw [MeasureTheory.Measure.smul_apply]
    simp only [MeasurableSpace.measurableSet_top, MeasureTheory.Measure.dirac_apply', smul_eq_mul]
    rfl


  -- Separate the indicator function
  conv =>
    enter [1, 1, a]
    rw [<- mul_one ((m l₁) a)]
    rw [<- mul_zero ((m l₁) a)]
    rw [<- mul_ite]


  -- Multiply by indicator function for z
  have HK (x : U) : (1 : ENNReal) = (if (z x < ENNReal.ofReal ε') then 1 else 0) + (if (z x ≥ ENNReal.ofReal ε') then 1 else 0) := by
    split
    · simp
      rw [ite_eq_right_iff.mpr]
      · simp
      · intro
        exfalso
        rename_i h1 h2
        simp at h1
        have C : z x < z x := by exact gt_of_ge_of_gt h2 h1
        simp at C
    · simp
      rw [ite_eq_left_iff.mpr]
      simp
      apply le_of_not_lt
      trivial
  conv =>
    enter [1, 1, a]
    rw [<- mul_one (_ * _)]
    rw [mul_assoc]
    enter [2, 2]
    rw [HK a]
  clear HK

  -- Distribute
  conv =>
    enter [1, 1, a]
    rw [mul_add]
    rw [mul_add]
  rw [ENNReal.tsum_add]

  -- Bound right term above
  have HB :
      ∑' (a : U), (m l₁) a * ((if a ∈ S then 1 else 0) * if z a ≥ ENNReal.ofReal ε' then 1 else 0) ≤
      ∑' (a : U), (m l₁) a * (if z a ≥ ENNReal.ofReal ε' then 1 else 0) := by
    apply ENNReal.tsum_le_tsum
    intro x
    apply mul_le_mul'
    · rfl
    split
    · simp
    · simp
  apply (le_trans (add_le_add_left HB _))
  clear HB

  -- Bound right term above by Markov inequality
  --  Pr[Z > ε'] ≤ δ
  have HMarkov : (∑' (a : U), (m l₁) a * if z a ≥ ENNReal.ofReal ε' then 1 else 0) ≤ δ := by

    -- Markov inequality, specialized to discrete measure (m l₁)
    have HM :=
      @MeasureTheory.mul_meas_ge_le_lintegral₀ _ ⊤ m1_measure
        (fun (x : U) => ENNReal.eexp ((α - 1) * z x))
        ?HAEmeasurable
        (ENNReal.ofReal (Real.exp ((α - 1) * ε')))
    case HAEmeasurable => exact Measurable.aemeasurable fun ⦃t⦄ _ => trivial
    rw [m1_measure_lintegral_sum] at HM
    rw [m1_measure_eval] at HM

    -- Convert between equivalent indicator functions
    have H (u : U) D D' :
        (@ite _ (ENNReal.ofReal (Real.exp ((α - 1) * ε')) ≤ ENNReal.eexp ((↑α - 1) * z u)) D (1 : ENNReal) 0) =
        (@ite _ (z u ≥ ↑(ENNReal.ofReal ε')) D' (1 : ENNReal) 0) := by
      split
      · split
        · rfl
        · exfalso
          rename_i HK1 HK2
          apply HK2
          simp only [ge_iff_le]
          have HK1' : ((α - 1) * ε' ≤ (↑α - 1) * z u) := by exact ENNReal.eexp_mono_le.mpr HK1
          have HK1'' : ↑ε' ≤ z u  := by
            apply ENNReal.ereal_smul_le_left (α - 1) ?SC1 ?SC2 HK1'
            case SC1 => apply Hα'
            case SC2 => exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
          simp
          rw [max_eq_left]
          · trivial
          linarith
      · split
        · exfalso
          rename_i HK1 HK2
          apply HK1
          rw [ge_iff_le] at HK2
          -- apply ENNReal.eexp_mono_le.mp at HK2
          rw [<- ENNReal.eexp_ofReal]
          apply ENNReal.eexp_mono_le.mp
          simp
          refine ENNReal.ereal_le_smul_left (α.toEReal - OfNat.ofNat 1) Hα' ?G1 ?G2
          case G1 => exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
          simp only [EReal.coe_ennreal_ofReal] at HK2
          rw [max_eq_left] at HK2
          · trivial
          linarith
        · rfl
    conv at HM =>
      enter [1, 2, 1, u, 2]
      rw [H u]
    clear H

    -- Use the Markov inequality
    suffices ENNReal.ofReal (Real.exp ((α - 1) * ε')) * (∑' (a : U), (m l₁) a * if z a ≥ ↑(ENNReal.ofReal ε') then 1 else 0) ≤ ENNReal.ofReal (Real.exp ((α - 1) * ε')) * ↑δ by
      apply (ENNReal.mul_le_mul_left ?SC1 ?SC2).mp
      apply this
      case SC1 =>
        simp
        apply Real.exp_pos
      case SC2 => exact ENNReal.ofReal_ne_top
    apply (le_trans ?G1 _)
    case G1 => apply HM
    clear HM
    clear HM

    -- Rewrite z and simplify
    conv =>
      enter [1, 1, u]
      rw [Hz]
      rw [ENNReal.eexp_mul_nonneg (le_of_lt Hα') (by exact Ne.symm (ne_of_beq_false rfl))]
      simp

    -- Apply Renyi divergence inequality
    have h := h α Hα l₁ l₂ neighs
    rw [RenyiDivergence] at h
    apply (le_trans _ HαSpecial)

    -- After this point the bound should be as tight as it's going to get

    have H (u : U) : (m l₁) u * ((m l₁) u / (m l₂) u) ^ (α.toEReal - 1).toReal =
                     ((m l₁) u) ^ α * ((m l₂) u) ^ (1 - α) := by
      cases (Classical.em ((m l₂) u = 0))
      · rename_i HZ2
        have HZ1 : (m l₁ u = 0) := by exact Hm l₁ l₂ neighs u HZ2
        simp [HZ2, HZ1]
        left
        linarith
      · rw [division_def]
        rw [ENNReal.mul_rpow_of_ne_top ?G1 ?G3]
        case G1 => exact PMF.apply_ne_top (m l₁) u
        case G3 =>
          apply ENNReal.inv_ne_top.mpr
          trivial
        rw [<- mul_assoc]
        congr 1
        · conv =>
            enter [1, 1]
            rw [<- ENNReal.rpow_one ((m l₁) u)]
          rw [<- (ENNReal.rpow_add 1 _ ?G1 ?G3)]
          case G1 =>
            intro HK
            rename_i HK1
            apply HK1
            apply (Hm l₂ l₁ (Neighbour_symm l₁ l₂ neighs))
            trivial
          case G3 => exact PMF.apply_ne_top (m l₁) u
          congr 1
          exact add_eq_of_eq_sub' rfl
        · rw [<- ENNReal.rpow_neg_one]
          rw [← ENNReal.rpow_mul]
          congr
          simp
          rw [neg_eq_iff_add_eq_zero]
          rw [EReal.toReal_sub]
          all_goals (try simp)
          · exact ne_of_beq_false rfl
          · exact EReal.add_top_iff_ne_bot.mp rfl
    conv =>
      enter [1, 1, u]
      rw [H u]
    clear H
    rw [<- RenyiDivergence_def_exp _ _ Hα]
    apply ENNReal.eexp_mono_le.mp
    refine ENNReal.ereal_le_smul_left (↑α - 1) ?Hr1 ?Hr2 ?H
    case Hr1 => exact Hα'
    case Hr2 => exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
    rw [<- ENNReal.ofEReal_ofReal_toENNReal] at h
    apply ENNReal.ofEReal_le_mono_conv_nonneg at h
    · apply (le_trans h)
      rw [EReal.coe_mul]
      rw [ENNReal.ofReal_mul ?G1]
      case G1 =>
        apply mul_nonneg
        · simp
        · exact sq_nonneg ε
      rw [ENNReal.ofReal_mul ?G1]
      case G1 => simp
      rw [EReal.coe_mul]
      simp
      apply Eq.le
      congr 1
      · congr 1
        rw [← EReal.coe_pow]
        congr
        rw [max_eq_left]
        exact sq_nonneg ε
      · congr 1
        rw [max_eq_left]
        linarith
    · apply @RenyiDivergence_def_nonneg U ⊤ ?G1 _ (m l₁) (m l₂) (Hm l₁ l₂ neighs) _ Hα
      infer_instance
    · simp
      apply mul_nonneg
      · apply mul_nonneg
        · apply EReal.coe_nonneg.mpr
          apply inv_nonneg_of_nonneg
          exact zero_le_two
        · rw [sq]
          apply mul_nonneg <;> exact EReal.coe_nonneg.mpr Hε
      · apply EReal.coe_nonneg.mpr
        linarith
  apply (le_trans (add_le_add_left HMarkov _))
  clear HMarkov




  -- Bound left term above
  have HDP :
      ∑' (a : U), (m l₁) a * ((if a ∈ S then 1 else 0) * if z a < ENNReal.ofReal ε' then 1 else 0) ≤
      ENNReal.ofReal (Real.exp ε') * ∑' (a : U), (m l₂) a * (if a ∈ S then 1 else 0) := by
    -- Eliminate the indicator function
    rw [<- ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro u

    -- Eliminate edge case by absolute continuity
    cases (Classical.em ((m l₂) u = 0))
    · have Hz : (m l₁ u = 0) := by
        rename_i h
        exact Hm l₁ l₂ neighs u h
      simp_all
    rename_i hnz

    conv =>
      congr
      · rw [mul_comm]
        rw [mul_assoc]
      · rw [mul_comm]
        enter [1]
        rw [mul_comm]
    rw [mul_assoc]
    apply mul_le_mul'
    · rfl
    split <;> simp
    rename_i H
    rw [Hz] at H
    apply ENNReal.eexp_mono_lt.mp at H
    simp only [ENNReal.elog_eexp] at H
    rw [mul_comm]
    cases (Classical.em (DFunLike.coe (m l₂) u = ⊤))
    · simp_all
    rename_i Hnt
    apply (ENNReal.div_le_iff hnz Hnt).mp
    simp at H
    rw [max_eq_left ?G5] at H
    case G5 => linarith
    exact le_of_lt H
  apply (le_trans (add_le_add_right HDP _))
  clear HDP

  -- Conclude by simplification
  simp [add_comm]



/--
Obtain an approximate DP bound from a zCDP bound, when ε > 0
-/
lemma ApproximateDP_of_zCDP_pos [Countable U] (m : Mechanism T U)
    (ε : ℝ) (Hε_pos : 0 < ε) (h : zCDPBound m ε) (Hm : ACNeighbour m) :
    ∀ δ : NNReal, (0 < (δ : ℝ)) -> DP' m (ε^2/2 + ε * (2*Real.log (1/δ))^(1/2 : ℝ)) δ := by
  intro δ Hδ0
  cases (Classical.em (δ < 1))
  · intro Hδ1
    apply ApproximateDP_of_zCDP_pos_lt_one m ε Hε_pos h Hm δ Hδ0
    trivial
  · apply ApproximateDP_gt1
    apply le_of_not_lt
    trivial

/--
Obtain an approximate DP bound from a zCDP bound
-/
theorem ApproximateDP_of_zCDP [Countable U] (m : Mechanism T U)
    (ε : ℝ) (Hε : 0 ≤ ε) (h : zCDPBound m ε) (Hm : ACNeighbour m) :
    ∀ δ : NNReal, (0 < (δ : ℝ)) -> DP' m (ε^2/2 + ε * (2*Real.log (1/δ))^(1/2 : ℝ)) δ := by
  cases LE.le.lt_or_eq Hε
  · rename_i Hε
    intro δ a
    exact ApproximateDP_of_zCDP_pos m ε Hε h Hm δ a
  · rename_i Hε'
    intro δ Hδ
    rw [<- Hε']
    rw [<- Hε'] at h
    rw [zCDPBound] at h
    simp at *
    intro l₁ l₂ HN S
    have h := h 2 (by simp) l₁ l₂ HN
    rw [(@RenyiDivergence_aux_zero U ⊤ ?G1 _ (m l₁) (m l₂) 2 (by simp) ?G2).mpr h]
    case G1 => infer_instance
    case G2 => exact Hm l₁ l₂ HN
    simp

/--
zCDP is no weaker than approximate DP, up to a loss of parameters.
-/
lemma zCDP_ApproximateDP [Countable U] {m : Mechanism T U} :
    ∃ (degrade : (δ : NNReal) -> (ε' : NNReal) -> NNReal), ∀ (δ : NNReal) (_ : 0 < δ) (ε' : NNReal),
     (zCDP m (degrade δ ε') -> ApproximateDP m ε' δ) := by
  let degrade (δ : NNReal) (ε' : NNReal) : NNReal :=
    (√(2 * Real.log (1/δ) + 2 * ε') - √(2 * Real.log (1/δ))).toNNReal
  have HDdegrade δ ε' : degrade δ ε' = (√(2 * Real.log (1/δ) + 2 * ε') - √(2 * Real.log (1/δ))).toNNReal := by rfl
  exists degrade
  intro δ Hδ ε' ⟨ HN , HB ⟩

  cases Classical.em (1 ≤ δ)
  · rename_i Hδ1
    exact ApproximateDP_gt1 m (↑ε') Hδ1

  rename_i Hδ1
  rw [ApproximateDP]
  have R := ApproximateDP_of_zCDP m (degrade δ ε') (by simp) HB HN δ Hδ

  have Hdegrade : ((degrade δ ε') ^ 2) / 2 + (degrade δ ε') * (2 * Real.log (1 / δ))^(1/2 : ℝ) = ε' := by
    rw [HDdegrade]
    generalize HD : Real.log (1 / δ) = D
    have HDnn : 0 ≤ D := by
      rw [<- HD]
      apply Real.log_nonneg
      apply one_le_one_div Hδ
      exact le_of_not_ge Hδ1
    simp only [Real.coe_toNNReal']
    rw [max_eq_left ?G1]
    case G1 =>
      apply sub_nonneg_of_le
      apply Real.sqrt_le_sqrt
      simp
    rw [sub_sq']
    rw [Real.sq_sqrt ?G1]
    case G1 =>
      apply add_nonneg
      · simp
        trivial
      · simp
    rw [Real.sq_sqrt ?G1]
    case G1 =>
      simp
      trivial
    rw [← Real.sqrt_eq_rpow]
    rw [mul_sub_right_distrib]
    rw [<- sq]
    rw [Real.sq_sqrt ?G1]
    case G1 =>
      simp
      trivial
    generalize HW : √(2 * D + 2 * ↑ε') * √(2 * D) = W
    conv =>
      enter [1, 1, 1, 2]
      rw [mul_assoc]
      rw [HW]
    rw [sub_div]
    rw [add_div]
    rw [add_div]
    simp
    linarith
  rw [Hdegrade] at R
  trivial


/--
Pure DP bound implies absolute continuity
-/
lemma ACNeighbour_of_DP (ε : NNReal) (q : List T -> PMF U) (H : SLang.PureDP q ε) : ACNeighbour q := by
  unfold SLang.PureDP at H
  apply (SLang.event_eq_singleton q ε).mp at H
  intro l₁ l₂ HN x Hx2
  apply Classical.by_contradiction
  intro Hx1
  unfold SLang.DP_singleton at H
  have H' := H l₁ l₂ HN x
  rw [Hx2] at H'
  rw [ENNReal.div_zero Hx1] at H'
  simp at H'


/-
## Auxiliary definitions used in the proof of the (ε^2 / 2) bound
-/
section ofDP_bound
variable (ε : NNReal) (Hε : 0 < ε)
variable (p q : PMF U)
variable (Hqp : ∀ x, ENNReal.ofReal (Real.exp (-ε)) ≤ p x / q x )
variable (Hpq : ∀ x, (p x / q x ≤ ENNReal.ofReal (Real.exp ε)))
variable (Hac : AbsCts p q)


noncomputable def β (x : U) : ENNReal :=
  (ENNReal.ofReal (Real.exp ε) - (p x / q x)) / (ENNReal.ofReal (Real.exp (ε)) - ENNReal.ofReal (Real.exp (- ε)))

lemma β_le_one {x : U} : β ε p q x ≤ 1 := by
  unfold β
  apply ENNReal.div_le_of_le_mul
  simp
  rw [← tsub_le_iff_right]
  refine (ENNReal.sub_le_sub_iff_left ?h.h ?h.h').mpr ?h.a
  · apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    simp
  · simp
  · apply Hqp

lemma β_ne_top : β ε p q x ≠ ⊤ := by
  unfold β
  intro HK
  apply ENNReal.div_eq_top.mp at HK
  cases HK
  · rename_i HK
    rcases HK with ⟨ _ , HK' ⟩
    rw [<- ENNReal.ofReal_sub] at HK'
    · simp at HK'
      apply not_le.mpr Hε HK'
    · apply Real.exp_nonneg
  · rename_i HK
    rcases HK with ⟨ HK', _ ⟩
    apply ENNReal.sub_eq_top_iff.mp at HK'
    simp at HK'


lemma one_sub_β (x : U) : 1 - (β ε p q x : ENNReal) =
    ((p x / q x) - ENNReal.ofReal (Real.exp (-ε)) ) / (ENNReal.ofReal (Real.exp ε) - ENNReal.ofReal (Real.exp (-ε))) := by
  unfold β
  generalize HC : (p x / q x) = C
  generalize HD : (ENNReal.ofReal (Real.exp ε)) = D
  generalize HE : (ENNReal.ofReal (Real.exp (- ε))) = E
  have H1 : (D - E ≠ 0) := by
    rw [<- HD, <- HE]
    rw [<- ENNReal.ofReal_sub]
    · simp
      trivial
    · apply Real.exp_nonneg
  have H2 : (D - E ≠ ⊤) := by simp [<- HD, <- HE]
  apply (@ENNReal.mul_eq_mul_right _ _ (D - E) H1 H2).mp
  rw [ENNReal.sub_mul ?G1]
  case G1 =>
    intros
    trivial
  conv =>
    congr
    · rw [ENNReal.mul_comm_div]
      rw [ENNReal.div_eq_inv_mul]
    · rw [ENNReal.mul_comm_div]
      rw [ENNReal.div_eq_inv_mul]
  simp [ENNReal.inv_mul_cancel H1 H2]
  rw [tsub_tsub]
  rw [tsub_add_eq_tsub_tsub_swap]
  rw [ENNReal.sub_sub_cancel ?G1 ?G2]
  case G1 => simp [<- HD]
  case G2 =>
    rw [<- HD, <- HC]
    apply Hpq


lemma sub_one_β_ne_top : (1 - β ε p q x) ≠ ⊤ := by
  apply ENNReal.sub_ne_top
  simp


/--
Value of the random variable A
-/
noncomputable def A_val (b : Bool) : ENNReal :=
    match b with
    | false => ENNReal.ofReal (Real.exp (-ε))
    | true => ENNReal.ofReal (Real.exp (ε))

/--
Proability space underlying the random variable A
-/
noncomputable def A_pmf (x : U) : PMF Bool :=
  ⟨ fun b =>
        match b with
        | false => β ε p q x
        | true => 1 - β ε p q x,
    by
       simp [(Summable.hasSum_iff ENNReal.summable), tsum_bool, add_tsub_cancel_iff_le]
       apply β_le_one
       trivial ⟩

/--
Expectation for the random variable A at each point x
-/
lemma A_expectation (x : U) : ∑'(b : Bool), A_val ε b * A_pmf ε p q Hqp x b = p x / q x := by
  rw [tsum_bool]
  unfold A_pmf
  rw [A_val, A_val, DFunLike.coe, PMF.instFunLike]
  simp only []
  conv =>
    lhs
    congr
    · unfold β
    · rw [one_sub_β _ Hε _ _ Hpq]
  generalize HC : (p x / q x) = C
  generalize HD : (ENNReal.ofReal (Real.exp ε)) = D
  generalize HE : (ENNReal.ofReal (Real.exp (- ε))) = E
  have H1 : (D - E ≠ 0) := by
    rw [<- HD, <- HE]
    rw [<- ENNReal.ofReal_sub]
    · simp
      trivial
    · apply Real.exp_nonneg
  have H2 : (D - E ≠ ⊤) := by simp [<- HD, <- HE]
  apply (@ENNReal.mul_eq_mul_right _ _ (D - E) H1 H2).mp
  rw [add_mul]
  rw [division_def]
  rw [division_def]
  repeat rw [mul_assoc]
  simp [ENNReal.inv_mul_cancel H1 H2]
  rw [ENNReal.mul_sub ?G1]
  case G1 =>
    intros
    rw [<- HE]
    simp
  rw [ENNReal.mul_sub ?G1]
  case G1 =>
    intros
    rw [<- HD]
    simp
  rw [ENNReal.mul_sub ?G1]
  case G1 =>
    intros
    rw [<- HC]
    have Hac := Hac x
    intro HK
    apply ENNReal.div_eq_top.mp at HK
    cases HK
    · simp_all only [imp_false, not_true_eq_false]
    · rename_i HK'
      cases HK'
      apply PMF.apply_ne_top p x
      trivial

  conv =>
    enter [1, 2, 2]
    rw [mul_comm]

  -- Arithmetic
  -- ENNReal subtraction is difficult
  -- Handle ⊤ cases to convert to NNReal
  generalize HED : (E * D) = ED
  cases ED
  · exfalso
    apply ENNReal.mul_eq_top.mp at HED
    cases HED
    · rename_i h
      rcases h with ⟨ _ , h ⟩
      rw [<- HD] at h
      simp at h
    · exfalso
      rename_i h
      rcases h with ⟨ h , _ ⟩
      rw [<- HE] at h
      simp at h
  rename_i ED

  conv =>
    enter [1, 1, 2]
    rw [mul_comm]
  generalize HCE : (C * E) = CE
  cases CE
  · simp
    apply ENNReal.mul_eq_top.mp at HCE
    cases HCE
    · exfalso
      rename_i h
      rcases h with ⟨ _ , h ⟩
      rw [<- HE] at h
      simp at h
    · rename_i h
      rcases h with ⟨ h , _ ⟩
      exfalso
      rw [<- HC] at h
      apply ENNReal.div_eq_top.mp at h
      cases h
      · rename_i h'
        rcases h' with ⟨ h1, h2 ⟩
        apply h1
        apply Hac
        apply h2
      · rename_i h
        rcases h with ⟨ h, _ ⟩
        apply PMF.apply_ne_top p x h
  rename_i CE
  conv =>
    enter [1, 2, 1]
    rw [mul_comm]
  generalize HCD : (C * D) = CD
  cases CD
  · simp
  rename_i CD
  rw [ENNReal.ofNNReal]
  repeat rw [<- WithTop.coe_sub]
  repeat rw [<- WithTop.coe_add]
  congr

  -- Now convert to Real substraction
  repeat rw [NNReal.sub_def]
  rw [<- Real.toNNReal_add ?G1 ?G2]
  case G1 =>
    rw [sub_nonneg]
    apply (ENNReal.ofReal_le_ofReal_iff ?G3).mp
    case G3 => exact NNReal.zero_le_coe
    rw [ENNReal.ofReal, Real.toNNReal_coe, <- HCE]
    rw [ENNReal.ofReal, Real.toNNReal_coe, <- HED]
    rw [mul_comm]
    apply mul_le_mul'
    · rfl
    rw [<- HC, <- HD]
    apply Hpq
  case G2 =>
    rw [sub_nonneg]
    apply (ENNReal.ofReal_le_ofReal_iff ?G3).mp
    case G3 => exact NNReal.zero_le_coe
    rw [ENNReal.ofReal, Real.toNNReal_coe, <- HED]
    rw [ENNReal.ofReal, Real.toNNReal_coe, <- HCD]
    apply mul_le_mul'
    · rw [<- HE, <- HC]
      apply Hqp
    · rfl

  -- Real subtraction is easier
  congr 1
  linarith



/--
Jensen's inequality for the random variable A: real reduct
-/
lemma A_jensen_real {α : ℝ} (Hα : 1 < α) (x : U) :
    (∑'(b : Bool), (A_val ε b).toReal * (A_pmf ε p q Hqp x b).toReal) ^ α ≤ (∑'(b : Bool), ((A_val ε b).toReal)^α * (A_pmf ε p q Hqp x b).toReal) := by
  have HJensen := @ConvexOn.map_integral_le _ _ ⊤ _ _ _ _ _ (fun b => (A_val ε b).toReal) _
          (PMF.toMeasure.isProbabilityMeasure (A_pmf ε p q Hqp x))
          (@convexOn_rpow α (le_of_lt Hα))
          ?G1 ?G2 ?G3 ?G4 ?G5
  case G1 =>
    apply ContinuousOn.rpow
    · exact continuousOn_id' (Set.Ici 0)
    · exact continuousOn_const
    · intro _ _
      right
      linarith
  case G2 =>
    exact isClosed_Ici
  case G3 =>
    apply MeasureTheory.ae_of_all
    intro b
    cases b <;> simp
  case G4 => simp
  case G5 => apply MeasureTheory.Integrable.of_finite

  rw [PMF.integral_eq_tsum _ _ ?G4] at HJensen
  case G4 => simp
  rw [PMF.integral_eq_tsum _ _ ?G5] at HJensen
  case G5 => apply MeasureTheory.Integrable.of_finite

  simp at HJensen
  conv at HJensen =>
    congr
    · enter [1, 1, a]
      rw [mul_comm]
    · enter [1, a]
      rw [mul_comm]
  trivial


/--
Jensen's inequality for the random variable A
-/
lemma A_jensen {α : ℝ} (Hα : 1 < α) (x : U) :
    (∑'(b : Bool), A_val ε b * A_pmf ε p q Hqp x b) ^ α ≤ (∑'(b : Bool), (A_val ε b)^α * A_pmf ε p q Hqp x b) := by

  have SC1 (b : Bool) : A_val ε b ≠ ⊤ := by cases b <;> simp [A_val]
  have SC2 (b : Bool) : (A_pmf ε p q Hqp x) b ≠ ⊤ := by
    cases b <;> simp only [A_pmf, DFunLike.coe, PMF.instFunLike]
    · apply β_ne_top
      apply Hε
    · apply sub_one_β_ne_top

  apply (ENNReal.toReal_le_toReal ?G1 ?G2).mp
  case G1 =>
    apply ENNReal.rpow_ne_top_of_nonneg
    · linarith
    · rw [tsum_bool]
      apply ENNReal.add_ne_top.mpr
      apply And.intro
      · apply ENNReal.mul_ne_top
        · apply (SC1 false)
        · apply (SC2 false)
      · apply ENNReal.mul_ne_top
        · apply (SC1 true)
        · apply (SC2 true)
  case G2 =>
    rw [tsum_bool]
    apply ENNReal.add_ne_top.mpr
    apply And.intro
    · apply ENNReal.mul_ne_top
      · apply ENNReal.rpow_ne_top_of_nonneg
        · linarith
        apply (SC1 false)
      · apply (SC2 false)
    · apply ENNReal.mul_ne_top
      · apply ENNReal.rpow_ne_top_of_nonneg
        · linarith
        apply (SC1 true)
      · apply (SC2 true)
  rw [tsum_bool, tsum_bool]
  rw [← ENNReal.toReal_rpow]
  rw [ENNReal.toReal_add ?G1 ?G2]
  case G1 =>
    apply ENNReal.mul_ne_top
    · apply (SC1 false)
    · apply (SC2 false)
  case G2 =>
    apply ENNReal.mul_ne_top
    · apply (SC1 true)
    · apply (SC2 true)
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_add ?G1 ?G2]
  case G1 =>
    apply ENNReal.mul_ne_top
    · apply ENNReal.rpow_ne_top_of_nonneg
      · linarith
      apply (SC1 false)
    · apply (SC2 false)
  case G2 =>
    apply ENNReal.mul_ne_top
    · apply ENNReal.rpow_ne_top_of_nonneg
      · linarith
      apply (SC1 true)
    · apply (SC2 true)
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_mul]
  rw [← ENNReal.toReal_rpow]
  rw [← ENNReal.toReal_rpow]
  have HJR := A_jensen_real ε p q Hqp Hα x
  rw [tsum_bool, tsum_bool] at HJR
  trivial

noncomputable def B : PMF Bool := q >>= A_pmf ε p q Hqp

/--
Formula for B which shows up in the main derivation
-/
lemma B_eval_open (b : Bool) : B ε p q Hqp b = ∑'(x : U), A_pmf ε p q Hqp x b * q x := by
  unfold B
  simp
  apply tsum_congr
  intro
  rw [mul_comm]


/--
closed form for B false
-/
lemma B_eval_false : B ε p q Hqp false = (ENNReal.ofReal (Real.exp ε) - 1) / (ENNReal.ofReal (Real.exp ε) - ENNReal.ofReal (Real.exp (-ε))) := by
  have H1 : (1 - (B ε p q Hqp) false) = B ε p q Hqp true := by
    apply ENNReal.sub_eq_of_eq_add ?G1
    case G1 => apply PMF.apply_ne_top
    rw [<- PMF.tsum_coe (B ε p q Hqp)]
    rw [tsum_bool]
    rw [add_comm]

  suffices (ENNReal.ofReal (Real.exp (- ε)) * B ε p q Hqp false + ENNReal.ofReal (Real.exp ε) * (1 - B ε p q Hqp false) = 1) by
    conv =>
      enter [2, 1, 2]
      rw [<- this]

    -- Quality of life
    generalize HE1 : (Real.exp ε.toReal) = E1
    generalize HE2 : (Real.exp (-ε.toReal)) = E2
    generalize HB : DFunLike.coe (B ε p q Hqp) false = B

    -- Convert to Real types
    apply (ENNReal.toReal_eq_toReal ?G1 ?G2).mp
    case G1 =>
      rw [<- HB]
      apply PMF.apply_ne_top
    case G2 =>
      apply lt_top_iff_ne_top.mp
      apply ENNReal.div_lt_top
      · apply ENNReal.sub_ne_top
        apply ENNReal.ofReal_ne_top
      · intro HK
        rw [<- ENNReal.ofReal_sub _ ?G3] at HK
        case G3 =>
          rw [<- HE2]
          apply Real.exp_nonneg
        simp at HK
        rw [<- HE1, <- HE2] at HK
        apply Real.exp_le_exp.mp at HK
        simp at HK
        apply LE.le.not_lt at HK
        apply HK
        trivial
    rw [ENNReal.toReal_div]
    rw [<- ENNReal.ofReal_sub _ ?G1]
    case G1 =>
      rw [<- HE2]
      apply Real.exp_nonneg
    rw [ENNReal.toReal_ofReal ?G1]
    case G1 =>
      simp
      rw [<- HE2, <- HE1]
      apply Real.exp_le_exp.mpr
      simp
    rw [ENNReal.mul_sub ?G1]
    case G1 =>
      intros
      apply ENNReal.ofReal_ne_top
    have HHB : B = ENNReal.ofReal (ENNReal.toReal B) := by
      rw [ENNReal.ofReal_toReal]
      rw [<- HB]
      apply PMF.apply_ne_top
    rw [HHB]
    rw [<- ENNReal.ofReal_mul ?G1]
    case G1 =>
      rw [<- HE2]
      apply Real.exp_nonneg
    rw [<- ENNReal.ofReal_mul ?G1]
    case G1 =>
      rw [<- HE1]
      apply Real.exp_nonneg
    simp
    rw [<- ENNReal.ofReal_sub _ ?G1]
    case G1 =>
      apply mul_nonneg
      · rw [<- HE1]
        apply Real.exp_nonneg
      · apply ENNReal.toReal_nonneg

    have SC1 : 0 ≤ E1 - E1 * B.toReal := by
      simp
      conv =>
        rhs
        rw [<- mul_one E1]
      apply mul_le_mul
      · simp
      · rw [<- HB]
        apply ENNReal.ofReal_le_one.mp
        rw [ENNReal.ofReal_toReal ?G1]
        case G1 => apply PMF.apply_ne_top
        apply PMF.coe_le_one
      · apply ENNReal.toReal_nonneg
      · rw [<- HE1]
        apply Real.exp_nonneg
    have SC2 : 0 ≤ E2 * B.toReal + (E1 - E1 * B.toReal) := by
      apply add_nonneg
      · apply mul_nonneg
        · rw [<- HE2]
          apply Real.exp_nonneg
        · rw [<- HB]
          apply ENNReal.toReal_nonneg
      · apply SC1
    have SC3 : 0 ≤ E1 - (E2 * B.toReal + (E1 - E1 * B.toReal)) := by
      rw [tsub_add_eq_tsub_tsub_swap]
      rw [sub_nonneg]
      simp
      rw [<- HE2, <- HE1]
      apply mul_le_mul
      · apply Real.exp_le_exp.mpr
        simp
      · simp
      · apply ENNReal.toReal_nonneg
      · apply Real.exp_nonneg
    rw [<- ENNReal.ofReal_add ?G1 ?G2]
    case G1 =>
      apply mul_nonneg
      · rw [<- HE2]
        apply Real.exp_nonneg
      · apply ENNReal.toReal_nonneg
    case G2 => apply SC1
    rw [<- ENNReal.ofReal_sub _ ?G1]
    case G1 => apply SC2
    rw [ENNReal.toReal_ofReal ?G1]
    case G1 => apply SC3
    apply eq_div_of_mul_eq
    · apply sub_ne_zero.mpr
      symm
      apply LT.lt.ne
      rw [<- HE1, <- HE2]
      apply Real.exp_lt_exp.mpr
      simp
      trivial
    ring_nf

  suffices ∑'(x : U), (∑'(b : Bool), A_val ε b * A_pmf ε p q Hqp x b) * q x = 1 by
    conv at this =>
      enter [1, 1, x]
      rw [<- ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm] at this
    rw [tsum_bool] at this
    conv at this =>
      lhs
      congr
      · enter [1, a]
        rw [mul_assoc]
      · enter [1, a]
        rw [mul_assoc]
    rw [ENNReal.tsum_mul_left] at this
    rw [ENNReal.tsum_mul_left] at this
    rw [<- B_eval_open] at this
    rw [<- B_eval_open] at this
    conv =>
      rhs
      rw [<- this]
    congr

  conv =>
    enter [1, 1, x]
    rw [A_expectation _ Hε _ _ Hqp Hpq Hac]
  suffices ∑' (x : U), p x / q x * q x = ∑'(x : U), p x by
    rw [this]
    apply PMF.tsum_coe
  apply tsum_eq_tsum_of_ne_zero_bij (fun x => x.val)
  · simp [Function.Injective]
  · intro x Hx
    simp [Function.support] at Hx
    simp_all only [Subtype.range_coe_subtype, Function.mem_support, ne_eq, Set.mem_setOf_eq, not_false_eq_true]
  · simp [Function.support]
    intros x _
    rw [PMF_mul_mul_inv_eq_mul_cancel p q Hac x]



/--
closed form for B true
-/
lemma B_eval_true : B ε p q Hqp true = (1 - ENNReal.ofReal (Real.exp (- ε))) / (ENNReal.ofReal (Real.exp ε) - ENNReal.ofReal (Real.exp (-ε))):= by
  have H1 : (1 - (B ε p q Hqp) false) = B ε p q Hqp true := by
    apply ENNReal.sub_eq_of_eq_add ?G1
    case G1 => apply PMF.apply_ne_top
    rw [<- PMF.tsum_coe (B ε p q Hqp)]
    rw [tsum_bool]
    rw [add_comm]
  rw [<- H1]
  rw [B_eval_false] <;> try trivial

  -- Quality of life
  generalize HE1 : (Real.exp ε.toReal) = E1
  generalize HE2 : (Real.exp (-ε.toReal)) = E2

  apply (ENNReal.eq_div_iff ?G1 ?G2).mpr
  case G1 =>
    rw [<- ENNReal.ofReal_sub _ ?G3]
    case G3 =>
      rw [<- HE2]
      apply Real.exp_nonneg
    simp
    rw [<- HE2, <- HE1]
    apply Real.exp_lt_exp.mpr
    simp
    trivial
  case G2 =>
    rw [<- ENNReal.ofReal_sub _ ?G3]
    case G3 =>
      rw [<- HE2]
      apply Real.exp_nonneg
    simp
  rw [ENNReal.mul_sub ?G1]
  case G1 =>
    intros
    exact Ne.symm (ne_of_beq_false rfl)
  simp
  rw [division_def]
  rw [<- mul_assoc]
  conv =>
    enter [1, 2, 1]
    rw [mul_comm]
  rw [mul_assoc]
  rw [ENNReal.mul_inv_cancel ?G1 ?G2]
  case G1 =>
    rw [<- ENNReal.ofReal_sub _ ?G3]
    case G3 =>
      rw [<- HE2]
      apply Real.exp_nonneg
    simp
    rw [<- HE2, <- HE1]
    apply Real.exp_lt_exp.mpr
    simp
    trivial
  case G2 => exact Ne.symm (ne_of_beq_false rfl)
  simp

  rw [<- ENNReal.ofReal_sub _ ?G1]
  case G1 =>
    rw [<- HE2]
    apply Real.exp_nonneg
  have X : (1 : ENNReal) = (ENNReal.ofReal (1 : ℝ)) := by simp
  conv =>
    enter [1, 2, 2]
    rw [X]
  rw [<- ENNReal.ofReal_sub _ ?G1]
  case G1 => simp
  rw [<- ENNReal.ofReal_sub _ ?G1]
  case G1 =>
    simp
    rw [<- HE1]
    apply Real.one_le_exp
    apply NNReal.zero_le_coe
  congr 1
  simp
  rw [max_eq_left]
  rw [<- HE2]
  apply Real.exp_nonneg

end ofDP_bound


/-
## Prove trig inequality B.1
-/

section sinh_inequality

lemma lemma_cosh_add {w z : ℝ} : Real.cosh (w + z) = Real.cosh w * Real.cosh z * (1 + Real.tanh w * Real.tanh z) :=
  let L {a : ℝ} : Real.sinh a = Real.cosh a * Real.tanh a := by
    rw [Real.tanh_eq_sinh_div_cosh]
    rw [division_def, mul_comm, mul_assoc]
    rw [inv_mul_cancel]
    · simp
    · linarith [Real.cosh_pos a]
  calc Real.cosh (w + z)
    _ = Real.cosh w * Real.cosh z + Real.sinh w * Real.sinh z := Real.cosh_add w z
    _ = Real.cosh w * Real.cosh z + ((Real.cosh w * Real.tanh w) * (Real.cosh z * Real.tanh z)) := by rw [L, L]
    _ = Real.cosh w * Real.cosh z * (1 + Real.tanh w * Real.tanh z) := by linarith

variable (x y : ℝ)
variable (Hy : 0 ≤ y) (Hyx : y < x) (Hx : x ≤ 2)

noncomputable def C := 2 * Real.sinh ((x - y) / 2) * Real.cosh (x / 2) * Real.cosh (y / 2)

noncomputable def t := Real.tanh (x / 2) * Real.tanh (y / 2)

lemma lemma_sinh_sub : Real.sinh (x - y) = (C x y) * (1 - t x y) :=
  calc Real.sinh (x - y)
    _ = (Real.exp (x - y) - Real.exp (-(x-y))) / 2 := by
      rw [Real.sinh_eq]
    _ = ((Real.exp ((x - y) / 2) - (Real.exp (- ((x - y) / 2)))) * (Real.exp ((x - y) / 2) + (Real.exp (- ((x - y) / 2))))) / 2 := by
      congr 1
      ring_nf
      simp
      rw [← Real.exp_nsmul]
      rw [← Real.exp_nsmul]
      rw [nsmul_eq_mul]
      simp
      congr 2
      · ring_nf
      · ring_nf
    _ = 2 * Real.sinh ((x - y) / 2) * Real.cosh ((x - y) / 2) := by
      rw [Real.sinh_eq]
      rw [Real.cosh_eq]
      ring_nf
    _ = (C x y) * (1 - t x y) := by
      unfold C
      unfold t
      repeat rw [mul_assoc]
      congr 2
      have T1 : (1 - Real.tanh (x / 2) * Real.tanh (y / 2)) = (1 + Real.tanh (x / 2) * Real.tanh (-(y / 2))) := by
        rw [Real.tanh_neg (y / 2)]
        linarith
      have T2 : Real.cosh (y / 2) = Real.cosh (-(y / 2)) := by
        exact Eq.symm (Real.cosh_neg (y / 2))
      rw [T1, T2]
      clear T1 T2
      repeat rw [<- mul_assoc]
      rw [<- lemma_cosh_add]
      congr
      linarith

lemma lemma_sub_sinh : Real.sinh x - Real.sinh y = C x y * (1 + t x y) :=
  calc Real.sinh x - Real.sinh y
    _ = (Real.exp x - Real.exp (-x) - Real.exp y + Real.exp (-y)) / 2 := by
      simp [Real.sinh_eq, Real.sinh_eq]
      ring_nf
    _ = ((Real.exp ((x - y) / 2) - Real.exp (-((x - y) / 2))) * (Real.exp ((x + y) / 2) + Real.exp (-((x + y) / 2))) ) / 2:= by
      congr 1
      ring_nf
      simp [<- Real.exp_add]
      ring_nf
    _ = 2 * Real.sinh ((x - y)/2) * Real.cosh ((x+y)/2) := by
      rw [Real.sinh_eq, Real.cosh_eq]
      linarith
    _ = C x y * (1 + t x y) := by
      unfold C
      unfold t
      conv =>
        enter [1, 2, 1]
        rw [add_div]
      rw [lemma_cosh_add]
      linarith

lemma C_ne_zero : C x y ≠ 0 := by
  unfold C
  repeat apply mul_ne_zero
  · simp
  · apply Real.sinh_ne_zero.mpr
    linarith
  · linarith [Real.cosh_pos (x / 2)]
  · linarith [Real.cosh_pos (y / 2)]

lemma lemma_step_1 : (Real.sinh x - Real.sinh y) / Real.sinh (x - y) = (1 + t x y) / (1 - t x y) := by
  rw [lemma_sinh_sub]
  rw [lemma_sub_sinh]
  rw [mul_div_mul_comm]
  rw [div_self]
  · simp
  · apply C_ne_zero
    linarith

lemma t_nonneg : 0 ≤ t x y := by
  unfold t
  apply mul_nonneg
  · rw [Real.tanh_eq_sinh_div_cosh]
    apply div_nonneg
    · apply Real.sinh_nonneg_iff.mpr
      linarith
    · linarith [Real.cosh_pos (x / 2)]
  · rw [Real.tanh_eq_sinh_div_cosh]
    apply div_nonneg
    · apply Real.sinh_nonneg_iff.mpr
      linarith
    · linarith [Real.cosh_pos (y / 2)]


-- Upstream?
lemma tanh_lt_1 (w : ℝ) : Real.tanh w < 1 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  apply (div_lt_one ?hb).mpr
  · rw [Real.sinh_eq, Real.cosh_eq]
    apply div_lt_div_of_pos_right
    · linarith [Real.exp_pos (-w)]
    · simp
  · apply Real.cosh_pos

-- Upstream?
lemma tanh_nonneg {w : ℝ} (HW : 0 ≤ w) : 0 ≤ Real.tanh w := by
  rw [Real.tanh_eq_sinh_div_cosh]
  apply div_nonneg
  · exact Real.sinh_nonneg_iff.mpr HW
  · exact (LT.lt.le (Real.cosh_pos w))

lemma t_le_one : t x y < 1 := by
  unfold t
  conv =>
    enter [2]
    rw [<- mul_one 1]
  apply (mul_lt_mul'' (tanh_lt_1 (x / 2)) (tanh_lt_1 (y / 2)))
  · apply tanh_nonneg
    linarith
  · apply tanh_nonneg
    linarith


lemma lemma_step_2 (H : t x y ≤ Real.tanh (x * y / 4)) : (1 + t x y) / (1 - t x y) ≤ Real.exp (x * y / 2) := by
  apply div_le_of_nonneg_of_le_mul
  · linarith [t_le_one x y Hy Hyx]
  · apply Real.exp_nonneg
  rw [mul_sub]
  simp
  apply (add_le_add_iff_right (Real.exp (x * y / 2) * t x y)).mp
  rw [sub_add_cancel]
  apply (add_le_add_iff_left (-1)).mp
  repeat rw [<- add_assoc]
  rw [Ring.add_left_neg, zero_add]
  conv =>
    enter [1, 1]
    rw [<- one_mul (t x y)]
  rw [<- add_mul]
  apply (le_div_iff' ?G1).mp
  case G1 =>
    apply add_pos
    · simp
    · apply Real.exp_pos
  apply le_trans H
  apply Eq.le
  rw [Real.tanh_eq_sinh_div_cosh]
  rw [Real.sinh_eq, Real.cosh_eq]
  rw [div_div_div_comm]
  have R1 : (Real.exp (x * y / 4) - Real.exp (-(x * y / 4))) = (Real.exp (-(x * y / 4)) *  (Real.exp (x * y / 2) - 1)) := by
    rw [mul_sub]
    rw [<- Real.exp_add]
    simp
    linarith
  rw [R1]
  clear R1
  have R2 : (Real.exp (x * y / 4) + Real.exp (-(x * y / 4))) = (Real.exp (-(x * y / 4)) *(Real.exp (x * y / 2) + 1)) := by
    rw [mul_add]
    rw [<- Real.exp_add]
    simp
    linarith
  rw [R2]
  clear R2
  simp
  rw [mul_div_mul_comm]
  have R3 : Real.exp (-(x * y / 4)) / Real.exp (-(x * y / 4)) = 1 := by
    apply div_self
    apply Real.exp_ne_zero
  rw [R3]
  simp
  congr 1
  · linarith
  · linarith

lemma Differentiable.differentiable_tanh :  Differentiable ℝ Real.tanh := by
  conv =>
    enter [2, y]
    rw [Real.tanh_eq_sinh_div_cosh]
  apply Differentiable.div
  · apply Real.differentiable_sinh
  · apply Real.differentiable_cosh
  · intro z
    have _ := Real.cosh_pos z
    linarith

lemma Real.continuous_tanh : Continuous Real.tanh := by
  conv =>
    enter [1, y]
    rw [Real.tanh_eq_sinh_div_cosh]
  apply Continuous.div
  · apply Real.continuous_sinh
  · apply Real.continuous_cosh
  · intro z
    have _ := Real.cosh_pos z
    linarith

lemma deriv.deriv_tanh (x : ℝ) : deriv Real.tanh x = 1 / (Real.cosh x) ^ 2 := by
  have W : Real.tanh = fun z => Real.sinh z / Real.cosh z := by
    apply funext
    intro
    rw [Real.tanh_eq_sinh_div_cosh]
  conv =>
    enter [1, 1]
    rw [W]
  clear W
  rw [deriv_div ?G1 ?G2 ?G3]
  case G1 =>
    apply Differentiable.differentiableAt
    apply Real.differentiable_sinh
  case G2 =>
    apply Differentiable.differentiableAt
    apply Real.differentiable_cosh
  case G3 =>
    have _ := Real.cosh_pos x
    linarith
  congr 1
  rw [Real.deriv_sinh]
  rw [Real.deriv_cosh]
  rw [← Real.cosh_sub]
  simp

lemma tanh_lt_id_nonneg {x : ℝ} (Hx : 0 ≤ x) : Real.tanh x ≤ x := by
  let f (x : ℝ) := x - Real.tanh x
  suffices 0 * (x - 0) ≤ f x - f 0 by
    dsimp [f] at this
    simp at this
    trivial
  have Hdiff : DifferentiableOn ℝ f (interior (Set.Ici 0)) := by
    apply Differentiable.differentiableOn
    dsimp [f]
    apply Differentiable.sub
    · apply differentiable_id'
    · apply Differentiable.differentiable_tanh
  have Hcts : ContinuousOn f (Set.Ici 0) := by
    apply Continuous.continuousOn
    dsimp [f]
    apply Continuous.sub
    · apply continuous_id'
    · apply Real.continuous_tanh
  apply Convex.mul_sub_le_image_sub_of_le_deriv (convex_Ici 0)
  · trivial
  · trivial
  · simp
    intro y _
    dsimp [f]
    -- Calculate the derivative
    rw [deriv_sub ?G1 ?G2]
    case G1 =>
      apply Differentiable.differentiableAt
      apply differentiable_id'
    case G2 =>
      apply Differentiable.differentiableAt
      apply Differentiable.differentiable_tanh
    rw [deriv.deriv_tanh]
    simp
    apply inv_le_one_iff.mpr
    right
    apply (one_le_sq_iff _).mpr
    · apply Real.one_le_cosh
    · apply (LT.lt.le (Real.cosh_pos _))
  · simp
  · simp
    trivial
  · trivial



-- This proof is repetitive and can be cleaned up
lemma lemma_step_3 : Real.tanh (x / 2) * Real.tanh (y / 2) ≤ Real.tanh (x * y / 4) := by
  let f (z : ℝ) :=  Real.tanh (x * z / 4) - Real.tanh (x / 2) * Real.tanh (z / 2)
  suffices 0 ≤ f y by
    dsimp [f] at this
    linarith
  suffices 0 * (y - 0) ≤ f y - f 0 by
    dsimp [f] at this
    simp at this
    dsimp [f]
    simp
    trivial
  have Hdiff : DifferentiableOn ℝ f (interior (Set.Icc 0 2)) := by
    apply Differentiable.differentiableOn
    dsimp [f]
    apply Differentiable.add
    · have Hfunc : (fun y => Real.tanh (x * y / 4)) = ((fun (y : ℝ) => Real.tanh y) ∘ (fun (z : ℝ) => x * z / 4)) := by
        rw [Function.comp_def]
      rw [Hfunc]
      clear Hfunc
      apply Differentiable.comp
      · apply Differentiable.differentiable_tanh
      · apply Differentiable.mul_const
        apply Differentiable.const_mul
        apply differentiable_id'
    · apply Differentiable.neg
      apply Differentiable.const_mul
      have Hfunc : (fun y => Real.tanh (y / 2)) = ((fun (y : ℝ) => Real.tanh y) ∘ (fun (z : ℝ) => z / 2)) := by rw [Function.comp_def]
      rw [Hfunc]
      apply Differentiable.comp
      · apply Differentiable.differentiable_tanh
      · apply Differentiable.mul_const
        apply differentiable_id'

  -- Can't see a way to derive this from Hdiff but it might be out there
  have Hcts : ContinuousOn f (Set.Icc 0 2) := by
    apply Continuous.continuousOn
    dsimp [f]
    apply Continuous.add
    · have Hfunc : (fun y => Real.tanh (x * y / 4)) = ((fun (y : ℝ) => Real.tanh y) ∘ (fun (z : ℝ) => x * z / 4)) := by rw [Function.comp_def]
      rw [Hfunc]
      clear Hfunc
      apply Continuous.comp
      · apply Real.continuous_tanh
      · apply Continuous.mul
        · apply continuous_mul_left
        · apply continuous_const
    · apply Continuous.neg
      apply Continuous.mul
      · apply continuous_const
      · have Hfunc : (fun y => Real.tanh (y / 2)) = ((fun (y : ℝ) => Real.tanh y) ∘ (fun (z : ℝ) => z / 2)) := by rw [Function.comp_def]
        rw [Hfunc]
        apply Continuous.comp
        · apply Real.continuous_tanh
        · apply continuous_mul_right

  apply Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc 0 2)
  · trivial
  · trivial
  · simp
    intros z Hz0 _
    dsimp [f]
    have Hfunc_xz4 : (fun z => Real.tanh (x * z / 4)) = Real.tanh ∘ (fun z => x * z / 4) := by rw [Function.comp_def]
    have Hfunc_z2 : (fun z => Real.tanh (z / 2)) = Real.tanh ∘ (fun z => z / 2) := by rw [Function.comp_def]

    -- Rewrite f back into derivative bound
    rw [deriv_sub ?G1 ?G2]
    case G1 =>
      apply Differentiable.differentiableAt
      rw [Hfunc_xz4]
      apply Differentiable.comp
      · apply Differentiable.differentiable_tanh
      · apply Differentiable.mul_const
        apply Differentiable.const_mul
        apply differentiable_id'
    case G2 =>
      apply Differentiable.differentiableAt
      apply Differentiable.const_mul
      rw [Hfunc_z2]
      apply Differentiable.comp
      · apply Differentiable.differentiable_tanh
      · apply Differentiable.mul_const
        apply differentiable_id'
    rw [sub_nonneg]

    -- Compute derivatives
    simp
    rw [Hfunc_xz4]
    rw [Hfunc_z2]
    rw [deriv.comp _ ?G1 ?G2]
    case G1 =>
      apply Differentiable.differentiableAt
      apply Differentiable.differentiable_tanh
    case G2 =>
      apply Differentiable.differentiableAt
      apply Differentiable.mul_const
      apply differentiable_id'
    simp
    rw [deriv.comp _ ?G1 ?G2]
    case G1 =>
      apply Differentiable.differentiableAt
      apply Differentiable.differentiable_tanh
    case G2 =>
      apply Differentiable.differentiableAt
      apply Differentiable.mul_const
      apply Differentiable.const_mul
      apply differentiable_id'
    simp
    rw [deriv_const_mul _ ?G1]
    case G1 =>
      apply Differentiable.differentiableAt
      apply differentiable_id'
    simp
    rw [deriv.deriv_tanh]
    rw [deriv.deriv_tanh]

    -- Apply the tanh bound
    suffices ((x / 2) * (1 / Real.cosh (z / 2) ^ 2 * 2⁻¹) ≤ 1 / Real.cosh (x * z / 4) ^ 2 * (x / 4)) by
      apply (le_trans _ this)
      apply mul_le_mul
      · apply tanh_lt_id_nonneg
        linarith
      · apply Eq.le
        rfl
      · apply mul_nonneg
        · apply div_nonneg
          · simp
          · apply sq_nonneg
        · simp
      · linarith

    -- Simplify
    conv =>
      enter [1]
      rw [mul_comm]
      rw [mul_assoc]
      enter [2]
      rw [mul_comm]
      rw [<- division_def]
      rw [div_div]
    apply mul_le_mul
    · apply (div_le_div_left _ _ _).mpr
      · apply sq_le_sq'
        · apply (@le_trans _ _ _ 0)
          · apply neg_nonneg.mp
            simp
            apply (LT.lt.le (Real.cosh_pos _))
          · apply (LT.lt.le (Real.cosh_pos _))
        · apply Real.cosh_le_cosh.mpr
          apply abs_le_abs
          · apply (div_le_div_iff (by simp) (by simp)).mpr
            rw [mul_assoc]
            rw [mul_comm]
            rw [mul_assoc]
            apply mul_le_mul <;> linarith
          · apply (@le_trans _ _ _ 0)
            · apply neg_nonneg.mp
              simp
              apply div_nonneg
              · apply mul_nonneg
                · linarith
                · linarith
              · simp
            · linarith
      · simp
      · apply sq_pos_of_pos
        apply Real.cosh_pos
      · apply sq_pos_of_pos
        apply Real.cosh_pos
    · apply Eq.le
      congr
      linarith
    · apply div_nonneg <;> linarith
    · apply div_nonneg
      · linarith
      apply sq_nonneg
  · simp
  · simp
    apply And.intro <;> linarith
  · linarith


lemma sinh_inequality :
    (Real.sinh x - Real.sinh y) / Real.sinh (x - y) ≤ Real.exp (x * y / 2) := by
  -- Temp usage of hypothesis so Lean doesn't freak out
  have _ := Hy
  have _ := Hx
  rw [lemma_step_1 _ _ Hyx]
  apply (lemma_step_2 _ _ Hy Hyx)
  unfold t
  apply lemma_step_3 _ _ Hy Hyx Hx


end sinh_inequality

/--
Convert ε-DP bound to `(1/2)ε²`-zCDP bound

Note that `zCDPBound _ ε` corresponds to `(1/2)ε²`-zCDP (not `ε`-zCDP).
-/
lemma ofDP_bound (ε : NNReal) (q' : List T -> PMF U) (H : SLang.PureDP q' ε) : zCDPBound q' ε := by
  rw [zCDPBound]
  intro α Hα l₁ l₂ HN
  -- Special case: (εα/2 > 1)
  cases (Classical.em (ε * α > 2))
  · rename_i Hεα
    have H1 : RenyiDivergence (q' l₁) (q' l₂) α ≤ ENNReal.ofReal ε := by
      apply RenyiDivergence_le_MaxDivergence
      · trivial
      · intro x
        apply SLang.event_to_singleton at H
        rw [SLang.DP_singleton] at H
        apply (le_trans (H _ _ HN x))
        simp [ENNReal.toEReal]
    apply (le_trans H1)
    apply ENNReal.ofReal_le_ofReal_iff'.mpr
    left
    rw [sq]
    rw [mul_assoc]
    have H2 : (1 / 2 * (↑ε * 2)) ≤ (1 / 2 * (↑ε * ↑ε * α)) := by
      apply mul_le_mul
      · rfl
      · rw [mul_assoc]
        apply mul_le_mul
        · rfl
        · apply GT.gt.lt at Hεα
          apply LT.lt.le at Hεα
          assumption
        · simp
        · exact NNReal.zero_le_coe
      · apply mul_nonneg
        · exact NNReal.zero_le_coe
        · simp
      · simp
    linarith
  rename_i Hεα
  apply le_of_not_gt at Hεα

  -- Open RenyiDivergence
  rw [RenyiDivergence]
  rw [<- ENNReal.ofEReal_ofReal_toENNReal]
  apply ENNReal.ofEReal_le_mono

  -- Reduction to the nonzero case here
  have K1 : Function.support (fun (x : U) => DFunLike.coe (q' l₁) x ) ⊆ { u : U | q' l₁ u ≠ 0 } := by simp [Function.support]
  have Hp_pre := PMF.tsum_coe (q' l₁)
  rw [<- tsum_subtype_eq_of_support_subset K1 ] at Hp_pre
  simp only [Set.coe_setOf, Set.mem_setOf_eq] at Hp_pre
  have K2 : Function.support (fun (x : U) => DFunLike.coe (q' l₂) x ) ⊆ { u : U | q' l₁ u ≠ 0 } := by
    simp [Function.support]
    intro a Ha Hk
    apply Ha
    apply (ACNeighbour_of_DP _ _ H _ _ (Neighbour_symm _ _ HN))
    apply Hk
  have Hq_pre := PMF.tsum_coe (q' l₂)
  rw [<- tsum_subtype_eq_of_support_subset K2 ] at Hq_pre
  simp only [Set.coe_setOf, Set.mem_setOf_eq] at Hq_pre
  let U' : Type := { x // DFunLike.coe (q' l₁) x ≠ 0 }

  let p : PMF U' :=
    ⟨ fun u => (q' l₁) u,
      by
        rw [<- Hp_pre]
        apply Summable.hasSum
        exact ENNReal.summable ⟩
  let q : PMF U' :=
    ⟨ fun u => (q' l₂) u,
      by
        rw [<- Hq_pre]
        apply Summable.hasSum
        exact ENNReal.summable ⟩
  clear K1 K2

  have X : RenyiDivergence_def (q' l₁) (q' l₂) α =  RenyiDivergence_def p q α := by
    rw [RenyiDivergence_def]
    rw [RenyiDivergence_def]
    congr 2
    have K3 : Function.support (fun (x : U) =>  DFunLike.coe (q' l₁) x ^ α * DFunLike.coe (q' l₂) x ^ (OfNat.ofNat 1 - α)) ⊆ { u : U | q' l₁ u ≠ 0 } := by
      simp [Function.support]
      intro u H1 _ _ _ H5
      have H5 := H1 H5
      linarith
    rw [<- tsum_subtype_eq_of_support_subset K3]
    dsimp [p, q]
    rfl
  rw [X]
  clear X


  -- Change LHS to sum by monotonicity
  suffices ENNReal.eexp ((α - 1) * RenyiDivergence_def p q α) ≤ ENNReal.eexp ((α - 1) * Real.toEReal (1 / 2 * ↑ε ^ 2 * α)) by
    apply (ENNReal.ereal_smul_le_left (α - 1) ?G1 ?G2)
    case G1 =>
      rw [← EReal.coe_one]
      rw [<- EReal.coe_sub]
      apply EReal.coe_pos.mpr
      linarith
    case G2 => exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
    apply ENNReal.eexp_mono_le.mpr
    trivial
  rw [RenyiDivergence_def_exp _ _ Hα]


  -- Derive absolute continuity facts from the pure DP bound
  have Hacpq : AbsCts p q := by
    dsimp [p, q]
    simp [DFunLike.coe, PMF.instFunLike]
    intro u' Hu'
    rcases u' with ⟨ u'' , _ ⟩
    simp
    apply (ACNeighbour_of_DP _ _ H _ _ HN)
    trivial

  have Hacqp : AbsCts q p := by
    dsimp [p, q]
    simp [DFunLike.coe, PMF.instFunLike]
    intro u' Hu'
    rcases u' with ⟨ u'' , _ ⟩
    simp
    apply (ACNeighbour_of_DP _ _ H _ _ (Neighbour_symm _ _ HN))
    trivial

  have Hqp : ∀ (x : U'), ENNReal.ofReal (Real.exp (-↑ε)) ≤ p x / q x := by
    rw [SLang.PureDP] at H
    apply SLang.event_to_singleton at H
    suffices (∀ (x : U'), q x / p x ≤ ENNReal.ofReal (Real.exp ↑ε)) by
      intro x
      apply ENNReal.inv_le_inv.mp
      rw [<- ENNReal.ofReal_inv_of_pos ?G4]
      case G4 => apply Real.exp_pos
      rw [<- Real.exp_neg]
      simp
      apply (le_trans _ (this x))
      apply Eq.le

      apply (ENNReal.toReal_eq_toReal ?G4 ?G5).mp
      case G4 =>
        apply ENNReal.inv_ne_top.mpr
        apply ENNReal.div_ne_zero.mpr
        apply And.intro
        · dsimp [p]
          simp [DFunLike.coe, PMF.instFunLike]
          rcases x with ⟨ x', Hx' ⟩
          simp
          trivial
        · apply PMF.apply_ne_top
      case G5 =>
        intro HK
        apply ENNReal.div_eq_top.mp at HK
        cases HK
        · rename_i h
          rcases h with ⟨ h1 , h2 ⟩
          dsimp [p] at h2
          simp [DFunLike.coe, PMF.instFunLike] at h2
          rcases x with ⟨ x' , Hx' ⟩
          trivial
        · rename_i h
          rcases h with ⟨ h , _ ⟩
          apply (PMF.apply_ne_top _ _ h)
      rw [ENNReal.toReal_inv]
      repeat rw [ENNReal.toReal_div]
      rw [inv_div]
    intro x
    rcases x with ⟨ x' , _ ⟩
    apply (le_trans _ (H _ _ (Neighbour_symm _ _ HN) x'))
    simp [DFunLike.coe, PMF.instFunLike]

  have Hpq : ∀ (x : U'), p x / q x ≤ ENNReal.ofReal (Real.exp ↑ε) := by
    rw [SLang.PureDP] at H
    apply SLang.event_to_singleton at H
    intro x
    rcases x with ⟨ x' , _ ⟩
    apply (le_trans _ (H _ _ HN x'))
    simp [DFunLike.coe, PMF.instFunLike]

  -- Rewrite to conditional expectation
  rw [RenyiDivergenceExpectation _ _ Hα Hacpq]

  -- Rewrite to A
  -- Next step won't work with ε=0, must separate the case.
  cases (Classical.em (ε = 0))
  · -- Follows from the DP bound
    simp_all
    rw [SLang.PureDP] at H
    apply SLang.event_to_singleton at H
    rw [SLang.DP_singleton] at H
    have H := H l₁ l₂ HN
    simp at H
    apply (@le_trans _ _ _ (∑' (x : U'), 1 ^ α * q x))
    · apply ENNReal.tsum_le_tsum
      intro i
      apply (ENNReal.mul_le_mul_right ?G1 ?G2).mpr
      case G1 =>
        intro HK
        have HK' := Hacpq _ HK
        rcases i
        trivial
      case G2 => apply PMF.apply_ne_top
      apply ENNReal.rpow_le_rpow
      · exact Hpq i.val i.property
      · linarith
    · simp
  rename_i Hε'

  have Hε : 0 < ε := by exact pos_iff_ne_zero.mpr Hε'

  conv =>
    enter [1, 1, x]
    rw [<- A_expectation ε Hε p q Hqp Hpq Hacpq x]


  -- Apply Jensen's inequality
  apply (@le_trans _ _ _ (∑' (x : U'), (∑' (b : Bool), (A_val ε b)^α * (A_pmf ε p q Hqp x) b) * q x))
  · apply ENNReal.tsum_le_tsum
    intro a
    apply (ENNReal.mul_le_mul_right ?G1 ?G2).mpr
    case G1 =>
      have HK1 : p a ≠ 0 := by
        rcases a
        dsimp [p]
        simp [DFunLike.coe, PMF.instFunLike]
        trivial
      intro HK
      apply HK1
      apply Hacpq
      trivial
    case G2 => apply PMF.apply_ne_top
    apply A_jensen _ Hε _ _ _ Hα

  -- Exchange the summations
  conv =>
    enter [1, 1, x]
    rw [<- ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]

  -- Pull out constant from inner series
  -- Rewrite in terms of B
  -- Evaluate A_val and B to a closed form
  conv =>
    enter [1, 1, b, 1, u]
    rw [mul_assoc]
  conv =>
    enter [1, 1, b]
    rw [ENNReal.tsum_mul_left]
    rw [<- B_eval_open]
  rw [tsum_bool]

  rw [B_eval_false] <;> try trivial
  rw [B_eval_true] <;> try trivial
  simp only [A_val]


  -- Convert to real-valued inequality, simplify the left-hand side
  have SC0 : ENNReal.ofReal (Real.exp ↑ε) - ENNReal.ofReal (Real.exp (-↑ε)) ≠ 0 := by
    apply ne_of_gt
    simp
    apply ENNReal.ofReal_lt_ofReal_iff'.mpr
    apply And.intro
    · apply Real.exp_lt_exp.mpr
      simp
      trivial
    · apply Real.exp_pos
  have SC1 : ENNReal.ofReal (Real.exp (-↑ε)) ^ α * ((ENNReal.ofReal (Real.exp ↑ε) - 1) / (ENNReal.ofReal (Real.exp ↑ε) - ENNReal.ofReal (Real.exp (-↑ε)))) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.rpow_ne_top_of_nonneg
      · linarith
      · exact ENNReal.ofReal_ne_top
    apply lt_top_iff_ne_top.mp
    apply ENNReal.div_lt_top
    · exact Ne.symm (ne_of_beq_false rfl)
    · apply SC0
  have SC2 : ENNReal.ofReal (Real.exp ↑ε) ^ α * ((1 - ENNReal.ofReal (Real.exp (-↑ε))) / (ENNReal.ofReal (Real.exp ↑ε) - ENNReal.ofReal (Real.exp (-↑ε)))) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.rpow_ne_top_of_nonneg
      · linarith
      · exact ENNReal.ofReal_ne_top
    apply lt_top_iff_ne_top.mp
    apply ENNReal.div_lt_top
    · exact Ne.symm (ne_of_beq_false rfl)
    · apply SC0
  apply (ENNReal.toReal_le_toReal ?G1 ?G2).mp
  case G1 =>
    apply ENNReal.add_ne_top.mpr
    apply And.intro
    · trivial
    · trivial
  case G2 =>  exact Ne.symm (ne_of_beq_false rfl)

  simp
  rw [ENNReal.toReal_add ?G1 ?G2]
  case G1 => apply SC1
  case G2 => apply SC2
  clear SC0 SC1 SC2
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_div]
  rw [ENNReal.toReal_div]
  rw [← ENNReal.toReal_rpow]
  rw [← ENNReal.toReal_rpow]
  rw [ENNReal.toReal_ofReal ?G1]
  case G1 => apply Real.exp_nonneg
  rw [ENNReal.toReal_ofReal ?G1]
  case G1 => apply Real.exp_nonneg
  rw [ENNReal.toReal_sub_of_le ?G1 ?G2]
  case G1 =>
    apply ENNReal.one_le_ofReal.mpr
    apply Real.one_le_exp
    simp only [NNReal.zero_le_coe]
  case G2 => exact ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_sub_of_le ?G1 ?G2]
  case G1 =>
    apply ENNReal.ofReal_le_ofReal_iff'.mpr
    left
    apply Real.exp_le_exp.mpr
    simp
  case G2 => exact ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_sub_of_le ?G1 ?G2]
  case G1 =>
    apply ENNReal.ofReal_le_one.mpr
    apply Real.exp_le_one_iff.mpr
    simp
  case G2 => simp
  rw [ENNReal.toReal_ofReal ?G1]
  case G1 => apply Real.exp_nonneg
  rw [ENNReal.toReal_ofReal ?G1]
  case G1 => apply Real.exp_nonneg
  simp

  -- Combine the fractions
  rw [division_def]
  rw [division_def]
  repeat rw [<- mul_assoc]
  rw [<- add_mul]

  -- Distribute, rearrange
  rw [mul_sub]
  rw [mul_sub]
  simp only [mul_one]
  repeat rw [<- Real.exp_mul]
  repeat rw [<- Real.exp_add]

  -- Rewrite to apply sinh lemma (combine these steps)
  have X : (Real.exp (-ε.toReal * α + ε.toReal) - Real.exp (-ε.toReal * α) + (Real.exp (ε.toReal * α) - Real.exp (ε.toReal * α + -ε.toReal))) =
           (Real.exp (-ε.toReal * α + ε.toReal) - Real.exp (ε.toReal * α + -ε.toReal)) + ((Real.exp (ε.toReal * α) - Real.exp (-ε.toReal * α))) := by
    linarith
  rw [X]
  clear X
  have X : ε.toReal * α + -ε.toReal = (ε.toReal * (α - 1)) := by linarith
  rw [X]
  clear X
  have X : (-ε.toReal * α + ε.toReal) = -(ε.toReal * (α - 1)) := by linarith
  rw [X]
  clear X
  have X : (-ε.toReal * α) = -(ε.toReal * α) := by linarith
  rw [X]
  clear X
  have X : (Real.exp (-(ε.toReal * (α - OfNat.ofNat 1))) - Real.exp (ε.toReal * (α - OfNat.ofNat 1)) +
              (Real.exp (ε.toReal * α) - Real.exp (-(ε.toReal * α)))) =
           ((Real.exp (ε.toReal * α) - Real.exp (-(ε.toReal * α))) -
             (Real.exp (ε.toReal * (α - OfNat.ofNat 1)) - Real.exp (-(ε.toReal * (α - OfNat.ofNat 1))))) := by
    linarith
  rw [X]
  clear X

  have Hsinh (x : ℝ) : (Real.exp x - Real.exp (-x)) = 2 * Real.sinh x := by
    rw [Real.sinh_eq]
    linarith
  rw [Hsinh]
  rw [Hsinh]
  rw [Hsinh]
  have X : (OfNat.ofNat 2 * Real.sinh (ε.toReal * α) - OfNat.ofNat 2 * Real.sinh (ε.toReal * (α - OfNat.ofNat (OfNat.ofNat 1)))) * (OfNat.ofNat 2 * Real.sinh ε.toReal)⁻¹ =
           (Real.sinh (ε.toReal * α) - Real.sinh (ε.toReal * (α - OfNat.ofNat (OfNat.ofNat 1)))) * (Real.sinh ε.toReal)⁻¹ := by
    rw [mul_inv]
    repeat rw [<- mul_assoc]
    congr 1
    rw [mul_comm]
    rw [mul_sub]
    repeat rw [<- mul_assoc]
    rw [inv_mul_cancel ?G1]
    case G1 => simp
    simp
  rw [X]
  clear X
  rw [<- division_def]
  simp

  -- Apply the sinh inequality
  have W : ε.toReal = (ε.toReal * α) - ((ε.toReal * (α - 1))) := by linarith
  conv =>
    enter [1, 2]
    rw [W]
  clear W
  apply (le_trans (sinh_inequality _ _ ?G1 ?G2 ?G3))
  case G1 =>
    apply mul_nonneg
    · exact NNReal.zero_le_coe
    linarith
  case G2 =>
    apply (mul_lt_mul_of_pos_left)
    · exact sub_one_lt α
    · trivial
  case G3 => linarith

  -- Simplify the eexp
  rw [sq]
  rw [<- EReal.coe_mul]
  rw [<- sq]
  have X : (α.toEReal - OfNat.ofNat 1) = (α - 1 : ℝ).toEReal := by rfl
  rw [X]
  clear X
  rw [<- EReal.coe_mul]
  rw [<- EReal.coe_mul]
  rw [<- EReal.coe_mul]
  rw [ENNReal.eexp, Real.toEReal]
  simp
  rw [ENNReal.toReal_ofReal ?G1]
  case G1 => apply Real.exp_nonneg
  apply Eq.le
  congr 1
  linarith

/-
Convert ε-DP to `(1/2)ε²`-zCDP.

Note that `zCDPBound _ ε` corresponds to `(1/2)ε²`-zCDP (not `ε`-zCDP).
-/
lemma ofDP (ε : NNReal) (q : List T -> PMF U) (H : SLang.PureDP q ε) : zCDP q ε := by
  constructor
  · exact ACNeighbour_of_DP ε q H
  · exact ofDP_bound ε q H
