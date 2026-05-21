/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.Convex.Integral
import LeanPool.HopfieldNet.SampCert.Util.Log

/-! Renyi Divergence

This file defines the Renyi divergence, and equations for evaluating it.
-/


open Real ENNReal PMF Nat Int MeasureTheory Measure PMF
open Classical


/--
Simplified consequence of absolute continuity between PMF's.
-/
def AbsCts (p q : T -> ENNReal) : Prop := ∀ x : T, q x = 0 -> p x = 0


/--
All PMF's are absolutely continuous with respect to themselves.
-/
lemma AbsCts_refl (q : PMF T) : AbsCts q q  := by
  rw [AbsCts]
  simp

/--
Obtain simplified absolute continuity from the measure-theoretic version of absolute continuity in a discrete space.
-/
lemma PMF_AbsCts [MeasurableSpace T] [MeasurableSingletonClass T] (p q : PMF T) (H : AbsolutelyContinuous (PMF.toMeasure p) (PMF.toMeasure q)) : AbsCts p q := by
  rw [AbsolutelyContinuous] at H
  rw [AbsCts]
  intro x Hx
  have Hxm : q.toMeasure { x } = 0 := by
    rw [toMeasure]
    simp
    apply (toOuterMeasure_apply_eq_zero_iff q {x}).mpr
    exact Set.disjoint_singleton_right.mpr fun a => a Hx
  have H := H Hxm
  rw [toMeasure] at H
  simp at *
  have Hp : Disjoint p.support {x} := (toOuterMeasure_apply_eq_zero_iff p {x}).mp H
  simp at Hp
  assumption

lemma PMF_mul_mul_inv_eq_mul_cancel (p q : PMF T) (HA : AbsCts p q) (a : T) : (p a  / q a) * q a = p a := by
  apply mul_mul_inv_eq_mul_cancel
  · rw [AbsCts] at HA
    intro
    simp_all
  · simp
    have HK : (q a ≠ ⊤) := apply_ne_top q a
    simp_all only [ne_eq, not_false_eq_true]
    simp

variable {T : Type}

/--
Definition of the Renyi divergence as an EReal.
-/
noncomputable def RenyiDivergence_def (p q : PMF T) (α : ℝ) : EReal :=
  (α - 1)⁻¹  * (elog (∑' x : T, (p x)^α  * (q x)^(1 - α)))

/--
Rearrange the definition of ``RenyiDivergence_def`` to obtain an equation for the inner series.
-/
lemma RenyiDivergence_def_exp (p q : PMF T) {α : ℝ} (h : 1 < α) :
  eexp (((α - 1)) * RenyiDivergence_def p q α) = (∑' x : T, (p x)^α * (q x)^(1 - α)) := by
  rw [RenyiDivergence_def]
  rw [<- mul_assoc]
  have H1 : (α.toEReal - OfNat.ofNat 1) =  (α - OfNat.ofNat 1).toEReal := by
    rw [EReal.coe_sub]
    congr
  have H2 : ((α.toEReal - OfNat.ofNat 1) * (α - OfNat.ofNat 1)⁻¹.toEReal = 1) := by
    rw [H1]
    rw [← EReal.coe_mul]
    rw [mul_inv_cancel]
    · simp
    · linarith
  simp [H2]

/-
The Renyi divergence is monotonic in the value of its sum.
-/
--lemma RenyiDivergence_mono_sum (x y : ℝ) (α : ℝ) (h : 1 < α) : (Real.exp ((α - 1) * x)) ≤ (Real.exp ((α - 1) * y)) -> (x ≤ y) := by
--  intro H
--  apply le_of_mul_le_mul_left
--  · exact exp_le_exp.mp H
--  · linarith

/--
Renyi Divergence series written as a conditional expectation, conditioned on q.
-/
theorem RenyiDivergenceExpectation (p q : T → ENNReal) {α : ℝ} (h : 1 < α) (H : AbsCts p q) :
  (∑' x : T, (p x)^α  * (q x)^(1 - α)) = ∑' x: T, (p x / q x)^α  * (q x) := by
  congr 4
  ext x
  rw [AbsCts] at H
  generalize Hvq : q x = vq
  cases vq <;> try simp_all
  · linarith
  · rename_i vq'
    cases (Classical.em (vq' = 0))
    · -- q x = 0
      -- by abs. cty. p x = 0
      rename_i Hvq'
      have Hp : p x = 0 := by
        apply H
        simp [Hvq, Hvq']
      simp [Hp, Hvq', Hvq]
      left
      linarith
    · -- q x ∈ ℝ+
      rename_i Hvq'
      generalize Hvp : p x = vp
      cases vp
      · -- q x ∈ ℝ+, p x = ⊤
        rw [ENNReal.top_rpow_of_pos ?H]
        case H => linarith
        rw [top_mul']
        split
        · exfalso
          rename_i Hcont
          apply Hvq'
          have Hcont' : (vq' : ENNReal) = 0 ∧ 0 < (1-α) ∨ (vq' : ENNReal) = ⊤ ∧ (1-α)< 0 := by
            exact rpow_eq_zero_iff.mp Hcont
          cases Hcont'
          · simp_all only [some_eq_coe, none_eq_top, zero_ne_top]
          · simp_all only [some_eq_coe, none_eq_top, top_rpow_of_neg, coe_ne_top, sub_neg, and_true]
        · simp_all
          rw [top_rpow_def]
          split <;> try simp_all
          split <;> try simp_all
          · linarith
          · linarith
      · rename_i vp
        cases (Classical.em (vq' = 0))
        · -- q x ∈ ℝ+, p x = 0
          rename_i Hvp'
          simp_all
        · -- q x ∈ ℝ+, p x ∈ ℝ+
          rename_i Hvp'
          rw [ENNReal.rpow_sub]
          · rw [← ENNReal.mul_comm_div]
            rw [← ENNReal.div_rpow_of_nonneg]
            · rw [ENNReal.rpow_one]
            · apply le_of_lt (lt_trans Real.zero_lt_one h )
          · simp_all only [some_eq_coe, not_false_eq_true, ne_eq, coe_eq_zero]
          · simp_all only [some_eq_coe, not_false_eq_true, ne_eq, coe_ne_top]


/--
Renyi Divergence series written as a conditional expectation, conditioned on p.
-/
theorem RenyiDivergenceExpectation' (p q : PMF T) {α : ℝ} (h : 1 < α) :
    (∑' x : T, (p x)^α  * (q x)^(1 - α)) = ∑' x: T, (p x / q x)^(α - 1)  * (p x) := by

  have K1 : Function.support (fun x : T => (p x / q x)^(α - 1) * p x) ⊆ { t : T | p t ≠ 0 } := by
    simp [Function.support]
  rw [<- tsum_subtype_eq_of_support_subset K1]
  clear K1

  have K2 : Function.support (fun x : T => (p x)^α * (q x)^(1 - α)) ⊆ { t : T | p t ≠ 0 } := by
    simp [Function.support]
    intro a H0 _ _ _ H2
    suffices (α ≤ 0) by linarith
    apply H0
    apply H2
  rw [<- tsum_subtype_eq_of_support_subset K2]
  clear K2

  apply tsum_congr
  intro x
  rcases x with ⟨ x', Hx' ⟩
  simp
  rw [division_def]
  rw [mul_rpow_eq_ite]
  simp
  split
  · exfalso
    rename_i h
    rcases h with ⟨ _, h ⟩
    linarith
  · rw [mul_assoc]
    conv =>
      enter [2]
      rw [mul_comm]
      enter [1, 2]
      rw [<- ENNReal.rpow_one (p x')]
    rw [mul_assoc]
    rw [<- ENNReal.rpow_add _ _ ?G1 ?G2]
    case G1 =>
      simp at Hx'
      trivial
    case G2 => apply PMF.apply_ne_top
    rw [ENNReal.inv_rpow]
    rw [← ENNReal.rpow_neg]
    rw [mul_comm]
    congr
    · linarith
    · linarith

/-!
## Jensen's inequality
-/
section Jensen

variable {T : Type}
variable [t1 : MeasurableSpace T]
variable [t2 : MeasurableSingletonClass T]
variable [tcount : Countable T] -- New

variable {U V : Type}
variable [m2 : MeasurableSpace U]
variable [count : Countable U]
variable [disc : DiscreteMeasurableSpace U]
variable [Inhabited U]

lemma Integrable_rpow (f : T → ℝ) (nn : ∀ x : T, 0 ≤ f x) (μ : Measure T) (α : ENNReal) (mem : Memℒp f α μ) (h1 : α ≠ 0) (h2 : α ≠ ⊤)  :
  MeasureTheory.Integrable (fun x : T => (f x) ^ α.toReal) μ := by
  have X := @MeasureTheory.Memℒp.integrable_norm_rpow T ℝ t1 μ _ f α mem h1 h2
  revert X
  conv =>
    left
    left
    intro x
    rw [← norm_rpow_of_nonneg (nn x)]
  intro X
  simp [Integrable] at *
  constructor
  · cases X
    rename_i left right
    rw [@aestronglyMeasurable_iff_aemeasurable]
    apply AEMeasurable.pow_const
    simp [Memℒp] at mem
    cases mem
    rename_i left' right'
    rw [aestronglyMeasurable_iff_aemeasurable] at left'
    simp [left']
  · rw [← hasFiniteIntegral_norm_iff]
    simp [X]

-- MARKUSDE: This lemma is derivable from ``Renyi_Jensen_strict_real``, however it requires a reduction
-- to first eliminate all elements (t : T) where q t = 0 from the series.
/--
Jensen's inequality for the exponential applied to the real-valued function ``(⬝)^α``.
-/
theorem Renyi_Jensen_real (f : T → ℝ) (q : PMF T) (α : ℝ) (h : 1 < α) (h2 : ∀ x : T, 0 ≤ f x) (mem : Memℒp f (ENNReal.ofReal α) (PMF.toMeasure q)) :
  ((∑' x : T, (f x) * (q x).toReal)) ^ α ≤ (∑' x : T, (f x) ^ α * (q x).toReal) := by
  conv =>
    enter [1, 1, 1, x]
    rw [mul_comm]
    rw [← smul_eq_mul]
  conv =>
    enter [2, 1, x]
    rw [mul_comm]
    rw [← smul_eq_mul]
  rw [← PMF.integral_eq_tsum]
  rw [← PMF.integral_eq_tsum]

  have A := @convexOn_rpow α (le_of_lt h)
  have B : ContinuousOn (fun (x : ℝ) => x ^ α) (Set.Ici 0) := by
    apply ContinuousOn.rpow
    · exact continuousOn_id' (Set.Ici 0)
    · exact continuousOn_const
    · intro x h'
      simp at h'
      have OR : x = 0 ∨ 0 < x := by exact LE.le.eq_or_gt h'
      cases OR
      · rename_i h''
        subst h''
        right
        apply lt_trans zero_lt_one h
      · rename_i h''
        left
        by_contra
        rename_i h3
        subst h3
        simp at h''
  have C : @IsClosed ℝ UniformSpace.toTopologicalSpace (Set.Ici 0) := by
    exact isClosed_Ici
  have D := @ConvexOn.map_integral_le T ℝ t1 _ _ _ (PMF.toMeasure q) (Set.Ici 0) f (fun (x : ℝ) => x ^ α) (PMF.toMeasure.isProbabilityMeasure q) A B C
  simp at D
  apply D
  · exact MeasureTheory.ae_of_all (PMF.toMeasure q) h2
  · apply MeasureTheory.Memℒp.integrable _ mem
    rw [one_le_ofReal]
    apply le_of_lt h
  · rw [Function.comp_def]
    have X : ENNReal.ofReal α ≠ 0 := by
      simp
      apply lt_trans zero_lt_one h
    have Y : ENNReal.ofReal α ≠ ⊤ := by
      simp
    have Z := @Integrable_rpow T t1 f h2 (PMF.toMeasure q) (ENNReal.ofReal α) mem X Y
    rw [toReal_ofReal] at Z
    · exact Z
    · apply le_of_lt
      apply lt_trans zero_lt_one h
  · have X : ENNReal.ofReal α ≠ 0 := by
      simp
      apply lt_trans zero_lt_one h
    have Y : ENNReal.ofReal α ≠ ⊤ := by
      simp
    have Z := @Integrable_rpow T t1 f h2 (PMF.toMeasure q) (ENNReal.ofReal α) mem X Y
    rw [toReal_ofReal] at Z
    · exact Z
    · apply le_of_lt
      apply lt_trans zero_lt_one h
  · apply MeasureTheory.Memℒp.integrable _ mem
    rw [one_le_ofReal]
    apply le_of_lt h


/--
Strict version of Jensen't inequality applied to the function ``(⬝)^α``.
-/
theorem Renyi_Jensen_strict_real (f : T → ℝ) (q : PMF T) (α : ℝ) (h : 1 < α) (h2 : ∀ x : T, 0 ≤ f x) (mem : Memℒp f (ENNReal.ofReal α) (PMF.toMeasure q)) (HT_nz : ∀ t : T, q t ≠ 0):
  ((∑' x : T, (f x) * (q x).toReal)) ^ α < (∑' x : T, (f x) ^ α * (q x).toReal) ∨ (∀ x : T, f x = ∑' (x : T), (q x).toReal * f x) := by
  conv =>
    enter [1, 1, 1, 1, x]
    rw [mul_comm]
    rw [← smul_eq_mul]
  conv =>
    enter [1, 2, 1, x]
    rw [mul_comm]
    rw [← smul_eq_mul]
  rw [← PMF.integral_eq_tsum]
  rw [← PMF.integral_eq_tsum]

  have A := strictConvexOn_rpow h

  have B : ContinuousOn (fun (x : ℝ) => x ^ α) (Set.Ici 0) := by
    apply ContinuousOn.rpow
    · exact continuousOn_id' (Set.Ici 0)
    · exact continuousOn_const
    · intro x h'
      simp at h'
      have OR : x = 0 ∨ 0 < x := by exact LE.le.eq_or_gt h'
      cases OR
      · rename_i h''
        subst h''
        right
        apply lt_trans zero_lt_one h
      · rename_i h''
        left
        by_contra
        rename_i h3
        subst h3
        simp at h''
  have C : @IsClosed ℝ UniformSpace.toTopologicalSpace (Set.Ici 0) := by
    exact isClosed_Ici
  have D := @StrictConvexOn.ae_eq_const_or_map_average_lt  T ℝ t1 _ _ _ (PMF.toMeasure q) (Set.Ici 0) f (fun (x : ℝ) => x ^ α) ((PMF.toMeasure.isProbabilityMeasure q).toIsFiniteMeasure) A B C ?G1 ?G2 ?G3
  case G1 =>
    exact MeasureTheory.ae_of_all (PMF.toMeasure q) h2
  case G2 =>
    apply MeasureTheory.Memℒp.integrable _ mem
    rw [one_le_ofReal]
    apply le_of_lt h
  case G3 =>
    rw [Function.comp_def]
    have X : ENNReal.ofReal α ≠ 0 := by
      simp
      apply lt_trans zero_lt_one h
    have Y : ENNReal.ofReal α ≠ ⊤ := by
      simp
    have Z := @Integrable_rpow T t1 f h2 (PMF.toMeasure q) (ENNReal.ofReal α) mem X Y
    rw [toReal_ofReal] at Z
    · exact Z
    · apply le_of_lt
      apply lt_trans zero_lt_one h
  simp at D
  · cases D
    · rename_i HR
      right
      simp at HR
      -- Because T is discrete, almost-everywhere equality should become equality
      have HR' := @Filter.EventuallyEq.eventually _ _ (ae q.toMeasure) f (Function.const T (⨍ (x : T), f x ∂q.toMeasure)) HR
      simp [Filter.Eventually] at HR'
      -- The measure of the compliment of the set in HR' is zero
      simp [ae] at HR'
      rw [PMF.toMeasure_apply _ _ ?Hmeas] at HR'
      case Hmeas =>
        apply (@measurableSet_discrete _ _ ?DM)
        apply MeasurableSingletonClass.toDiscreteMeasurableSpace
      -- Sum is zero iff all elements are zero
      apply ENNReal.tsum_eq_zero.mp at HR'
      -- Indicator is zero when proposition is not true
      intro x
      have HR' := HR' x
      simp at HR'
      cases (Classical.em (f x = ⨍ (x : T), f x ∂q.toMeasure))
      · rename_i Heqx
        -- Rewrite the average
        rw [MeasureTheory.average] at Heqx
        rw [MeasureTheory.integral_countable'] at Heqx
        · simp at Heqx
          conv at Heqx =>
            rhs
            arg 1
            intro x
            rw [PMF.toMeasure_apply_singleton]
            · skip
            · apply measurableSet_singleton
          -- Interesting.... is this sum not just 1?
          simp at *
          apply Heqx
        · simp
          apply MeasureTheory.Memℒp.integrable _ mem
          have X : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
          rw [X]
          apply ofReal_le_ofReal_iff'.mpr
          left
          linarith
      · -- At type T, q x is never zero
        rename_i Hnex
        exfalso
        apply (HT_nz x)
        apply HR'
        apply Hnex
    · rename_i HR
      left
      rw [<- MeasureTheory.integral_average]
      rw [<- MeasureTheory.integral_average]
      simp
      rw [<- MeasureTheory.integral_average]
      rw [<- MeasureTheory.integral_average]
      simp
      apply HR
  · have X : ENNReal.ofReal α ≠ 0 := by
      simp
      apply lt_trans zero_lt_one h
    have Y : ENNReal.ofReal α ≠ ⊤ := by
      simp
    have Z := @Integrable_rpow T t1 f h2 (PMF.toMeasure q) (ENNReal.ofReal α) mem X Y
    rw [toReal_ofReal] at Z
    · exact Z
    · apply le_of_lt
      apply lt_trans zero_lt_one h
  · apply MeasureTheory.Memℒp.integrable _ mem
    rw [one_le_ofReal]
    apply le_of_lt h

end Jensen


/--
Quotient from the Real-valued Jenen's inequality applied to the series in the Renyi divergence.
-/
noncomputable def Renyi_Jensen_f (p q : PMF T) : T -> ℝ := (fun z => (p z / q z).toReal)

/--
Summand from the Renyi divergence equals a real-valued summand, except in a special case.
-/
lemma Renyi_Jensen_rw (p q : PMF T) {α : ℝ} (h : 1 < α) (H : AbsCts p q) (Hspecial : ∀ x : T, ¬(p x = ⊤ ∧ q x ≠ 0 ∧ q x ≠ ⊤)) (x : T) :
  (p x / q x)^α  * (q x) = ENNReal.ofReal (((Renyi_Jensen_f p q) x)^α * (q x).toReal) := by
  simp [Renyi_Jensen_f]
  rw [ENNReal.toReal_rpow]
  rw [<- ENNReal.toReal_mul]
  rw [ENNReal.ofReal_toReal]
  apply mul_ne_top
  · apply rpow_ne_top_of_nonneg
    · linarith
    · intro HK
      apply ENNReal.div_eq_top.mp at HK
      simp at HK
      rw [AbsCts] at H
      cases HK
      · rename_i HK
        rcases HK with ⟨ HK1, HK2 ⟩
        simp_all
      · rename_i HK
        rcases HK with ⟨ HK1, HK2 ⟩
        simp_all
        apply HK2
        apply (Hspecial)
        · apply HK1
        · intro Hcont1
          simp_all
  · exact apply_ne_top q x


-- MARKUSDE: I think it might be possible to use `Renyi_Jensen_strict_real` in this proof instead,
-- this would eliminate the need for `Renyi_Jensen_real`.
/--
Jensen's inquality applied to ENNReals, in the case that q is nonzero.
-/
lemma Renyi_Jensen_ENNReal_reduct [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T]
  (p q : PMF T) {α : ℝ} (h : 1 < α) (H : AbsCts p q) (Hq : ∀ t, q t ≠ 0) :
  (∑' x : T, (p x / q x) * q x) ^ α ≤ (∑' x : T, (p x / q x) ^ α * q x) := by
  have Hdiscr : DiscreteMeasurableSpace T := MeasurableSingletonClass.toDiscreteMeasurableSpace
  cases (Classical.em (∑' (a : T), (p a / q a) ^ α * q a ≠ ⊤))
  · rename_i Hnts
    cases (Classical.em (∀ x : T, ¬(p x = ⊤ ∧ q x ≠ 0 ∧ q x ≠ ⊤)))
    · -- Typical case
      rename_i Hspecial
      conv =>
        rhs
        arg 1
        intro x
        rw [Renyi_Jensen_rw p q h H Hspecial]
      rw [<- ENNReal.ofReal_tsum_of_nonneg ?Hnonneg ?Hsummable]
      case Hnonneg =>
        intro t
        apply mul_nonneg
        · refine rpow_nonneg ?ha.hx α
          simp [Renyi_Jensen_f]
        · exact toReal_nonneg
      case Hsummable =>
        conv =>
          congr
          intro x
          rw [Renyi_Jensen_f]
        conv =>
          arg 1
          intro x
          lhs
          rw [ENNReal.toReal_rpow]
        conv =>
          arg 1
          intro x
          rw [<- ENNReal.toReal_mul]
        apply ENNReal.summable_toReal
        assumption
      have HRJf_nonneg (a : T) : 0 <= Renyi_Jensen_f p q a := by apply toReal_nonneg
      have HRJf_nt (a : T) : p a / q a ≠ ⊤ := by
        intro HK
        have HK' : (p a ≠ 0 ∧ q a = 0 ∨ p a = ⊤ ∧ q a ≠ ⊤) := by exact div_eq_top.mp HK
        cases HK'
        · rename_i HK'
          rcases HK' with ⟨ HK1 , HK2 ⟩
          rw [AbsCts] at H
          simp_all only [ne_eq, not_and, Decidable.not_not, ENNReal.zero_div, zero_ne_top]
        · rename_i HK'
          rcases HK' with ⟨ HK1 , _ ⟩
          apply (Hspecial a)
          simp_all
      have Hsum_indicator (a : T) : ∑' (i : T), q i * Set.indicator {a} (fun x => 1) i = q a := by
        have Hfun : (fun (i : T) => q i * Set.indicator {a} (fun x => 1) i) = (fun (i : T) => if i = a then q a else 0) := by
          funext i
          rw [Set.indicator]
          split <;> simp <;> split <;> simp_all
        rw [Hfun]
        exact tsum_ite_eq a (q a)
      apply (le_trans ?G1 ?G2)
      case G2 =>
        apply (ofReal_le_ofReal ?Hle)
        case Hle =>
          apply Renyi_Jensen_real
          · apply h
          · simp [Renyi_Jensen_f]
          · simp [Memℒp]
            constructor
            · apply MeasureTheory.StronglyMeasurable.aestronglyMeasurable
              apply Measurable.stronglyMeasurable
              apply Measurable.ennreal_toReal
              conv =>
                right
                intro x
                rw [division_def]
              apply Measurable.mul
              · apply measurable_discrete
              · apply Measurable.inv
                apply measurable_discrete
            · simp [eLpNorm]
              split
              · simp
              · rename_i Hα
                simp [eLpNorm']
                rw [MeasureTheory.lintegral_countable']
                rw [toReal_ofReal (le_of_lt (lt_trans zero_lt_one h))]
                apply rpow_lt_top_of_nonneg
                · simp
                  apply le_of_not_ge Hα
                · conv =>
                    enter [1, 1, a, 1, 1]
                    rw [<- Real.toNNReal_eq_nnnorm_of_nonneg (HRJf_nonneg a)]
                    rw [Renyi_Jensen_f]
                    rw [<- ENNReal.ofReal.eq_1]
                    rw [ENNReal.ofReal_toReal (HRJf_nt a)]
                    rfl
                  conv =>
                    enter [1, 1, a, 2]
                    simp [toMeasure]
                    simp [PMF.toOuterMeasure]
                    rw [Hsum_indicator]
                  apply Hnts
      case G1 =>
        -- We need the latter fn to be summable or else it becomes zero and the inequality does not hold
        rw [<- ENNReal.ofReal_rpow_of_nonneg ?Harg ?Hα]
        case Harg =>
          apply tsum_nonneg
          intro i
          apply mul_nonneg
          · apply HRJf_nonneg
          · exact toReal_nonneg
        case Hα => linarith
        apply (ENNReal.rpow_le_rpow _ ?Hα')
        case Hα' => linarith
        conv =>
          rhs
          arg 1
          arg 1
          intro a
          rw [Renyi_Jensen_f]
          rw [<- ENNReal.toReal_mul]
        rw [<- ENNReal.tsum_toReal_eq]
        · rw [ENNReal.ofReal_toReal]
          conv =>
            enter [1, 1, a]
            rw [PMF_mul_mul_inv_eq_mul_cancel p q H]
          exact tsum_coe_ne_top p
        · intro a
          conv =>
            arg 1
            rw [PMF_mul_mul_inv_eq_mul_cancel p q H]
          exact apply_ne_top p a
    · -- Special case: There exists some element x0 with p x0 = ⊤ but q x0 ∈ ℝ+
      rename_i Hspecial
      simp at *
      rcases Hspecial with ⟨ x0, ⟨ H1, _, H3 ⟩⟩
      have HT1 : (∑' (x : T), p x / q x * q x) ^ α = ⊤ := by
        apply rpow_eq_top_iff.mpr
        right
        apply And.intro
        · apply ENNReal.tsum_eq_top_of_eq_top
          exists x0
          apply mul_eq_top.mpr
          right
          apply And.intro
          · apply div_eq_top.mpr
            simp_all
          · simp_all
        · linarith
      have HT2 : ∑' (x : T), (p x / q x) ^ α * q x = ⊤ := by
        apply ENNReal.tsum_eq_top_of_eq_top
        exists x0
        apply mul_eq_top.mpr
        right
        apply And.intro
        · apply rpow_eq_top_iff.mpr
          right
          apply And.intro
          · simp_all
            exact top_div_of_ne_top H3
          · simp_all
            linarith
        · simp_all
      rw [HT1, HT2]
  · rename_i HStop
    simp at *
    rw [HStop]
    exact OrderTop.le_top ((∑' (x : T), p x / q x * q x) ^ α)


/--
On types where q is nonzero, Jensen's inequality for the Renyi divergence sum is tight only for equal distributions.
-/
lemma Renyi_Jensen_ENNReal_converse_reduct [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T]
  (p q : PMF T) {α : ℝ} (h : 1 < α) (H : AbsCts p q) (Hq : ∀ t, q t ≠ 0)
  (Hsumeq : (∑' x : T, (p x / q x) * q x) ^ α = (∑' x : T, (p x / q x) ^ α * q x)) :
  (p = q) := by
  have Hdiscr : DiscreteMeasurableSpace T := MeasurableSingletonClass.toDiscreteMeasurableSpace
  cases (Classical.em (∑' (a : T), (p a / q a) ^ α * q a ≠ ⊤))
  · -- Preliminary stuff, basically the same as the forward case
    rename_i Hnts
    cases (Classical.em (∀ x : T, ¬(p x = ⊤ ∧ q x ≠ 0 ∧ q x ≠ ⊤)))
    · rename_i Hspecial
      conv at Hsumeq =>
        rhs
        arg 1
        intro x
        rw [Renyi_Jensen_rw p q h H Hspecial]
      rw [<- ENNReal.ofReal_tsum_of_nonneg ?Hnonneg ?Hsummable] at Hsumeq
      case Hnonneg =>
        intro t
        apply mul_nonneg
        · refine rpow_nonneg ?ha.hx α
          simp [Renyi_Jensen_f]
        · exact toReal_nonneg
      case Hsummable =>
        conv =>
          congr
          intro x
          rw [Renyi_Jensen_f]
        conv =>
          enter [1, x, 1]
          rw [ENNReal.toReal_rpow]
        conv =>
          enter [1, x]
          rw [<- ENNReal.toReal_mul]
        apply ENNReal.summable_toReal
        assumption
      have HRJf_nonneg (a : T) : 0 <= Renyi_Jensen_f p q a := by apply toReal_nonneg
      have HRJf_nt (a : T) : p a / q a ≠ ⊤ := by
        intro HK
        have HK' : (p a ≠ 0 ∧ q a = 0 ∨ p a = ⊤ ∧ q a ≠ ⊤) := by exact div_eq_top.mp HK
        cases HK'
        · rename_i HK'
          rcases HK' with ⟨ HK1 , HK2 ⟩
          rw [AbsCts] at H
          simp_all only [ne_eq, not_and, Decidable.not_not, ENNReal.zero_div, zero_ne_top]
        · rename_i HK'
          rcases HK' with ⟨ HK1 , _ ⟩
          apply (Hspecial a)
          simp_all
      have Hsum_indicator (a : T) : ∑' (i : T), q i * Set.indicator {a} (fun x => 1) i = q a := by
        have Hfun : (fun (i : T) => q i * Set.indicator {a} (fun x => 1) i) = (fun (i : T) => if i = a then q a else 0) := by
          funext i
          rw [Set.indicator]
          split <;> simp <;> split <;> simp_all
        rw [Hfun]
        exact tsum_ite_eq a (q a)

      -- Apply the converse lemma
      have Hieq := Renyi_Jensen_strict_real (Renyi_Jensen_f p q) q α h HRJf_nonneg ?GLp Hq
      case GLp =>
        -- ℒp bound (same as forward proof)
        simp [Memℒp]
        constructor
        · apply MeasureTheory.StronglyMeasurable.aestronglyMeasurable
          apply Measurable.stronglyMeasurable
          apply Measurable.ennreal_toReal
          conv =>
            right
            intro x
            rw [division_def]
          apply Measurable.mul
          · apply measurable_discrete
          · apply Measurable.inv
            apply measurable_discrete
        · simp [eLpNorm]
          split
          · simp
          · rename_i Hα
            simp [eLpNorm']
            rw [MeasureTheory.lintegral_countable']
            rw [toReal_ofReal (le_of_lt (lt_trans zero_lt_one h))]
            apply rpow_lt_top_of_nonneg
            · simp
              apply le_of_not_ge Hα
            · conv =>
                enter [1, 1, a, 1, 1]
                rw [<- Real.toNNReal_eq_nnnorm_of_nonneg (HRJf_nonneg a)]
                rw [Renyi_Jensen_f]
                rw [<- ENNReal.ofReal.eq_1]
                rw [ENNReal.ofReal_toReal (HRJf_nt a)]
                rfl
              conv =>
                enter [1, 1, a, 2]
                simp [toMeasure]
                simp [PMF.toOuterMeasure]
                rw [Hsum_indicator]
              apply Hnts
      cases Hieq
      · rename_i Hk
        exfalso
        have CG1 (z : T) : q z = 0 → p z = 0 := by apply H
        have CG2 (z : T) :  ¬(p z ≠ 0 ∧ q z = ⊤) := by
          simp
          intro
          apply PMF.apply_ne_top
        conv at Hk =>
          enter [1, 1, 1, z]
          rw [Renyi_Jensen_f]
          rw [<- ENNReal.toReal_mul]
          arg 1
          rw [division_def]
          rw [mul_mul_inv_eq_mul_cancel (CG1 z) (CG2 z)]
        clear CG1
        clear CG2

        -- Convert the LHS of Hsumeq to the ℝ-valued summand, and then contradict
        conv at Hsumeq =>
          enter [1, 1, 1, x]
          rw [division_def]
          rw [mul_assoc]
          rw [ENNReal.inv_mul_cancel]
          · skip
          · apply Hq
          · apply PMF.apply_ne_top
        simp at *
        rw [<- ENNReal.tsum_toReal_eq ?G1] at Hk
        case G1 =>
          intro
          apply PMF.apply_ne_top
        simp at *
        have Hone' : (1 : ENNReal).toReal = (1 : ℝ) := by simp
        rw [<- Hone'] at Hk
        rw [Hsumeq] at Hk
        clear Hone'
        rw [ENNReal.toReal_ofReal ?G1] at Hk
        case G1 =>
          apply tsum_nonneg
          intro i
          apply mul_nonneg
          · apply rpow_nonneg
            apply HRJf_nonneg
          · exact toReal_nonneg
        linarith
      · rename_i Hext
        -- RHS of Hext is 1, LHS is p/q
        apply PMF.ext
        intro x
        have Hext' := Hext x
        rw [Renyi_Jensen_f] at Hext'
        have CG1 (z : T) : q z = 0 → p z = 0 := by apply H
        have CG2 (z : T) :  ¬(p z ≠ 0 ∧ q z = ⊤) := by
          simp
          intro
          apply PMF.apply_ne_top
        conv at Hext' =>
          rhs
          arg 1
          intro z
          rw [Renyi_Jensen_f]
          rw [<- ENNReal.toReal_mul]
          arg 1
          rw [mul_comm]
          rw [division_def]
          rw [mul_mul_inv_eq_mul_cancel (CG1 z) (CG2 z)]
        clear CG1
        clear CG2
        rw [<- ENNReal.tsum_toReal_eq] at Hext'
        · rw [PMF.tsum_coe] at Hext'
          apply (@ENNReal.mul_eq_mul_right _ _ ((q x)⁻¹) ?G1 ?G2).mp
          case G1 =>
            simp
            apply PMF.apply_ne_top
          case G2 =>
            simp
            apply Hq
          rw [ENNReal.mul_inv_cancel ?G1 ?G2]
          case G1 => apply Hq
          case G2 => apply PMF.apply_ne_top
          apply (toReal_eq_toReal_iff' (HRJf_nt x) ?G3).mp
          case G3 => simp
          apply Hext'
        · intro
          apply PMF.apply_ne_top

    · -- Special case: There exists some element x0 with p x0 = ⊤ but q x0 ∈ ℝ+
      -- This means the sum in Hnts will actually be ⊤
      rename_i Hspecial
      exfalso
      apply Hnts
      apply ENNReal.tsum_eq_top_of_eq_top
      simp at Hspecial
      rcases Hspecial with ⟨ x , ⟨ Hx1, ⟨ Hx2 , Hx3 ⟩ ⟩ ⟩
      exists x
      apply mul_eq_top.mpr
      right
      apply And.intro
      · apply rpow_eq_top_iff.mpr
        right
        apply And.intro
        · apply div_eq_top.mpr
          right
          apply And.intro Hx1 Hx3
        · linarith
      · apply Hx2
  · -- One of the series is Top, so the other series is too
    rename_i Hlhs_top
    simp at Hlhs_top
    rw [Hlhs_top] at Hsumeq
    -- This series should actually be 1 by PMF
    conv at Hsumeq =>
      lhs
      arg 1
      arg 1
      intro x
      rw [PMF_mul_mul_inv_eq_mul_cancel p q H]
    conv at Hsumeq =>
      lhs
      arg 1
      rw [PMF.tsum_coe]
    simp at Hsumeq

/--
Restriction of the PMF f to the support of q.
-/
def reducedPMF_def (f q : PMF T) (x : { t : T // ¬q t = 0 }) : ENNReal := f x.val

/--
Restricted PMF has sum  1
-/
lemma reducedPMF_norm_acts (p q : PMF T) (H : AbsCts p q) : HasSum (reducedPMF_def p q) 1 := by
  have H1 : Summable (reducedPMF_def p q) := by exact ENNReal.summable
  have H2 := Summable.hasSum H1
  have H3 : (∑' (b : { t // q t ≠ 0 }), reducedPMF_def p q b) = 1 := by
    have K1 : Function.support (fun x => p x) ⊆ { t : T | q t ≠ 0 } := by
      rw [Function.support]
      simp
      intro a Hp Hcont
      rw [AbsCts] at H
      apply Hp
      apply H
      apply Hcont
    have S1 : ∑' (x : ↑{t | q t ≠ 0}), p ↑x = ∑' (x : T), p x := by
      apply tsum_subtype_eq_of_support_subset K1
    have T1 : ∑' (x : T), p x = 1 := by exact tsum_coe p
    rw [<- T1]
    rw [<- S1]
    simp
    rfl
  rw [<- H3]
  apply H2

/--
Restriction of the PMF f to the support of q
-/
noncomputable def reducedPMF {p q : PMF T} (H : AbsCts p q): PMF { t : T // ¬q t = 0 } :=
  ⟨ reducedPMF_def p q, reducedPMF_norm_acts p q H ⟩

/--
`reducedPMF` is nonzero everywhere
-/
lemma reducedPMF_pos {q : PMF T} (H : AbsCts q q) (a : T) (Ha : ¬q a = 0): (reducedPMF H) ⟨a, Ha⟩ ≠ 0 := by
  simp
  rw [reducedPMF]
  unfold reducedPMF_def
  rw [DFunLike.coe]
  rw [PMF.instFunLike]
  simp
  apply Ha

/--
Jensen's inquality for the Renyi divergence sum between absolutely continuous PMFs
-/
theorem Renyi_Jensen_ENNReal [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T] (p q : PMF T) {α : ℝ} (h : 1 < α) (Hac : AbsCts p q) :
  (∑' x : T, (p x / q x) * q x) ^ α ≤ (∑' x : T, (p x / q x) ^ α * q x) := by

  have K1 : Function.support (fun x : T => (p x / q x) * q x) ⊆ { t : T | q t ≠ 0 } := by simp [Function.support]
  have K2 : Function.support (fun x : T => (p x / q x)^α * q x) ⊆ { t : T | q t ≠ 0 } := by simp [Function.support]
  rw [<- tsum_subtype_eq_of_support_subset K1]
  rw [<- tsum_subtype_eq_of_support_subset K2]
  simp

  have Hq : AbsCts q q := AbsCts_refl q

  have B1 (x : { x // ¬q x = 0 }) : p ↑x / q ↑x * q ↑x = reducedPMF Hac x / reducedPMF Hq x * reducedPMF Hq x := by congr
  have B2 (x : { x // ¬q x = 0 }) : (p ↑x / q ↑x)^α * q ↑x = (reducedPMF Hac x / reducedPMF Hq x)^α * reducedPMF Hq x := by congr
  conv =>
    congr
    · enter [1, 1, x]
      rw [B1 x]
    · arg 1
      intro x
      rw [B2 x]

  clear B1
  clear B2
  clear K1
  clear K2

  apply Renyi_Jensen_ENNReal_reduct
  · apply h
  · rw [AbsCts]
    simp
    intro a Ha Hcont
    exfalso
    apply (reducedPMF_pos Hq a Ha Hcont)
  · intro t
    rcases t with ⟨ a , Ha ⟩
    apply (reducedPMF_pos Hq a Ha)

/--
Converse of Jensen's inquality for the Renyi divergence sum between absolutely continuous PMFs
-/
lemma  Renyi_Jensen_ENNReal_converse [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T]
  (p q : PMF T) {α : ℝ} (h : 1 < α) (H : AbsCts p q)
  (Hsumeq : (∑' x : T, (p x / q x) * q x) ^ α = (∑' x : T, (p x / q x) ^ α * q x)) :
  (p = q) := by

  have K1 : Function.support (fun x : T => (p x / q x) * q x) ⊆ { t : T | q t ≠ 0 } := by simp [Function.support]
  have K2 : Function.support (fun x : T => (p x / q x)^α * q x) ⊆ { t : T | q t ≠ 0 } := by simp [Function.support]
  rw [<- tsum_subtype_eq_of_support_subset K1] at Hsumeq
  rw [<- tsum_subtype_eq_of_support_subset K2] at Hsumeq
  simp at Hsumeq

  have Hq : AbsCts q q := AbsCts_refl q

  have B1 (x : { x // ¬q x = 0 }) : p ↑x / q ↑x * q ↑x = reducedPMF H x / reducedPMF Hq x * reducedPMF Hq x := by congr
  have B2 (x : { x // ¬q x = 0 }) : (p ↑x / q ↑x)^α * q ↑x = (reducedPMF H x / reducedPMF Hq x)^α * reducedPMF Hq x := by congr

  conv at Hsumeq =>
    congr
    · arg 1
      arg 1
      intro x
      rw [B1 x]
    · arg 1
      intro x
      rw [B2 x]

  clear B1
  clear B2
  clear K1
  clear K2

  have Hreduced : (reducedPMF H = reducedPMF Hq) := by
    apply (Renyi_Jensen_ENNReal_converse_reduct (reducedPMF H) (reducedPMF Hq) h)
    · intro t Ht
      exfalso
      rcases t with ⟨ a , Ha ⟩
      apply (reducedPMF_pos Hq a Ha)
      apply Ht
    · intro t
      rcases t with ⟨ a , Ha ⟩
      apply (reducedPMF_pos Hq a Ha)
    · apply Hsumeq

  apply PMF.ext
  intro x
  cases (Classical.em (q x = 0))
  · rename_i Hqz
    rw [Hqz]
    apply H
    apply Hqz
  · rename_i Hqnz
    have Hreduced' : reducedPMF H ⟨ x , Hqnz ⟩ = reducedPMF Hq ⟨ x , Hqnz ⟩ := by
      exact congrFun (congrArg DFunLike.coe Hreduced) ⟨ x , Hqnz ⟩
    repeat rw [DFunLike.coe] at Hreduced'
    repeat rw [PMF.instFunLike] at Hreduced'
    repeat rw [reducedPMF] at Hreduced'
    unfold reducedPMF_def at Hreduced'
    simp at Hreduced'
    assumption

/--
The ``EReal``-valued Renyi divergence is nonnegative.

Use this lemma to perform rewrites through the ``ENNReal.ofEReal`` in the
``ENNReal``-valued ``RenyiDivergence``
-/
theorem RenyiDivergence_def_nonneg [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T] (p q : PMF T) (Hpq : AbsCts p q) {α : ℝ} (Hα : 1 < α) :
  (0 ≤ RenyiDivergence_def p q α) := by
  have H1 : eexp (((α - 1)) * 0)  ≤ eexp ((α - 1) * RenyiDivergence_def p q α) := by
    rw [RenyiDivergence_def_exp p q Hα]
    rw [RenyiDivergenceExpectation p q Hα Hpq]
    simp
    apply (le_trans ?G1 (Renyi_Jensen_ENNReal p q Hα Hpq))
    have Hone : (∑' (x : T), p x / q x * q x) = 1 := by
      conv =>
        arg 1
        arg 1
        intro x
        rw [PMF_mul_mul_inv_eq_mul_cancel p q Hpq]
      exact tsum_coe p
    have Hle : (∑' (x : T), p x / q x * q x) ≤ (∑' (x : T), p x / q x * q x) ^ α := by
      apply ENNReal.le_rpow_self_of_one_le
      · rw [Hone]
      · linarith
    apply le_trans ?X Hle
    rw [Hone]
  apply eexp_mono_le.mpr at H1
  have Hone : (OfNat.ofNat 1 = Real.toEReal (1 : ℝ)) := by simp
  have Hzero : (OfNat.ofNat 0 = Real.toEReal (0 : ℝ)) := by simp

  apply ereal_smul_le_left (α.toEReal - OfNat.ofNat 1)
  · rw [Hone]
    rw [<- EReal.coe_sub]
    rw [Hzero]
    apply EReal.coe_lt_coe_iff.mpr
    exact sub_pos.mpr Hα
  · rw [Hone]
    rw [<- EReal.coe_sub]
    exact EReal.coe_lt_top (α - OfNat.ofNat 1)
  · assumption

/--
Renyi divergence between identical distributions is zero
-/
lemma RenyiDivergence_refl_zero (p : PMF T) {α : ℝ} (Hα : 1 < α) : (0 = RenyiDivergence_def p p α) := by
  have H1 : 1 = eexp ((α - 1) * RenyiDivergence_def p p α) := by
    rw [RenyiDivergence_def_exp p p Hα]
    rw [RenyiDivergenceExpectation p p Hα (AbsCts_refl p)]
    have HRW (x : T) : ((p.val x) / (p.val x)) ^α * p.val x = p.val x := by
      cases (Classical.em (p x = 0))
      · rename_i Hz
        simp [DFunLike.coe] at Hz
        simp [Hz]
      · rename_i Hnz
        rw [((@div_eq_one_iff (p.val x) (p.val x) ?GNZ) ?GNT).mpr rfl]
        case GNZ =>
          simp [DFunLike.coe] at Hnz
          simp
          apply Hnz
        case GNT =>
          have HltTop := PMF.apply_lt_top p x
          apply LT.lt.ne_top HltTop
        simp
    conv =>
      rhs
      arg 1
      intro x
      simp [DFunLike.coe]
      rw [HRW]
    rcases p with ⟨ p' , Hp' ⟩
    exact Eq.symm (HasSum.tsum_eq Hp')

  have Hone : (OfNat.ofNat 1 = Real.toEReal (1 : ℝ)) := by simp
  have Hzero : (OfNat.ofNat 0 = Real.toEReal (0 : ℝ)) := by simp
  apply ereal_smul_eq_left (α.toEReal - OfNat.ofNat 1)
  · rw [Hone]
    rw [<- EReal.coe_sub]
    rw [Hzero]
    apply EReal.coe_lt_coe_iff.mpr
    exact sub_pos.mpr Hα
  · rw [Hone]
    rw [<- EReal.coe_sub]
    exact EReal.coe_lt_top (α - OfNat.ofNat 1)
  apply eexp_injective
  rw [<- H1]
  simp

/--
Renyi divergence is zero if and only if the distributions are equal
-/
theorem RenyiDivergence_def_eq_0_iff [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T]
  (p q : PMF T) {α : ℝ} (Hα : 1 < α) (Hcts : AbsCts p q) :
  (RenyiDivergence_def p q α = 0) <-> (p = q) := by
  apply Iff.intro
  · intro Hrdeq
    apply Renyi_Jensen_ENNReal_converse
    · apply Hα
    · apply Hcts
    · have H1 : eexp (((α - 1)) * 0) = eexp ((α - 1) * RenyiDivergence_def p q α) := by rw [Hrdeq]
      simp at H1
      rw [RenyiDivergence_def_exp p q Hα] at H1
      rw [RenyiDivergenceExpectation p q Hα Hcts] at H1
      rw [<- H1]
      clear H1
      have CG1 (x : T) : DFunLike.coe q x = OfNat.ofNat 0 → DFunLike.coe p x = OfNat.ofNat 0 := by apply Hcts
      have CG2 (x : T) : ¬(DFunLike.coe p x ≠ OfNat.ofNat 0 ∧ DFunLike.coe q x = ⊤) := by
        simp
        intro
        apply PMF.apply_ne_top
      conv =>
        lhs
        arg 1
        arg 1
        intro x
        rw [division_def]
        rw [mul_mul_inv_eq_mul_cancel (CG1 x) (CG2 x)]
      simp
  · intro Hpq
    rw [Hpq]
    symm
    apply RenyiDivergence_refl_zero
    apply Hα

/--
The logarithm in the definition of the Renyi divergence is nonnegative.
-/
lemma RenyiDivergence_def_log_sum_nonneg [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T]
  (p q : PMF T) (Hac : AbsCts p q) {α : ℝ} (Hα : 1 < α ): (0 ≤ (elog (∑' x : T, (p x)^α  * (q x)^(1 - α)))) := by
  have Hrd := RenyiDivergence_def_nonneg p q Hac Hα
  rw [RenyiDivergence_def] at Hrd
  apply ofEReal_nonneg_scal_l at Hrd
  · assumption
  · apply inv_pos_of_pos
    linarith

/--
The ``ENNReal``-valued Renyi divergence between PMF's.
-/
noncomputable def RenyiDivergence (p q : PMF T) (α : ℝ) : ENNReal :=
  ENNReal.ofEReal (RenyiDivergence_def p q α)


/--
The Renyi divergence between absolutely continuous distributions is zero if and only if the
distributions are equal.
-/
theorem RenyiDivergence_aux_zero [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T]
  (p q : PMF T) {α : ℝ} (Hα : 1 < α) (Hac : AbsCts p q) : p = q <-> RenyiDivergence p q α = 0 := by
  apply Iff.intro
  · intro Heq
    rw [Heq]
    rw [RenyiDivergence]
    rw [<- RenyiDivergence_refl_zero _ Hα]
    simp
  · intro H
    apply (RenyiDivergence_def_eq_0_iff p q Hα Hac).mp
    symm
    rw [RenyiDivergence] at H
    have H' := RenyiDivergence_def_nonneg p q Hac Hα
    refine (ofEReal_nonneg_inj ?mpr.Hw H').mpr ?mpr.a
    · simp
    simp [H]

/--
Renyi divergence is bounded above by the Max Divergence ε

-/
lemma RenyiDivergence_le_MaxDivergence {p q : PMF T} {ε : ENNReal} {α : ℝ} (Hα : 1 < α)
    (Hmax_divergence : ∀ t : T, (p t / q t) ≤ ENNReal.eexp ε) :
    RenyiDivergence p q α ≤ ε := by
  rw [RenyiDivergence]
  conv =>
    rhs
    rw [<- @ofEReal_toENNReal ε]
  apply ofEReal_le_mono

  -- Rewrite to expectation conditioned on q
  apply (ENNReal.ereal_smul_le_left (α - 1) ?G1 ?G2)
  case G1 =>
    rw [← EReal.coe_one]
    rw [<- EReal.coe_sub]
    apply EReal.coe_pos.mpr
    linarith
  case G2 => exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
  apply ENNReal.eexp_mono_le.mpr
  rw [RenyiDivergence_def_exp p q Hα]
  rw [RenyiDivergenceExpectation' p q Hα]

  -- Pointwise bound
  have H : ∑' (x : T), (p x / q x) ^ (α - 1) * p x  ≤ ∑' (x : T), (eexp ε) ^ (α - 1) * p x  := by
    apply ENNReal.tsum_le_tsum
    intro x
    apply mul_le_mul
    · apply ENNReal.rpow_le_rpow (Hmax_divergence x)
      linarith
    · rfl
    · apply _root_.zero_le
    · apply _root_.zero_le
  apply (le_trans H)
  rw [ENNReal.tsum_mul_left]
  rw [tsum_coe]
  simp
  have H : eexp ε.toEReal ^ (α - OfNat.ofNat 1) = eexp (ε * (α - OfNat.ofNat 1)) := by
    rcases ε
    · simp
      rw [EReal.top_mul_of_pos ?G1]
      case G1 =>
        rw [← EReal.coe_one]
        rw [<- EReal.coe_sub]
        apply EReal.coe_pos.mpr
        linarith
      simp
      trivial
    simp
    rw [ENNReal.ofNNReal]
    rw [ENNReal.toEReal]
    simp
    rw [ENNReal.ofReal_rpow_of_pos ?G1]
    case G1 => apply exp_pos
    rw [<- Real.exp_mul]
    rfl
  rw [H]
  clear H

  apply eexp_mono_le.mp
  rw [mul_comm]
