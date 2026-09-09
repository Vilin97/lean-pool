/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Asymptotics.Lemmas

/-! Joint differentiation through uniformly bounded evaluation operators.
Strong continuity on the derivative vector suffices; operator-norm continuity
or differentiability of the whole family of evaluation maps is unnecessary. -/

@[expose] public section


noncomputable section

namespace EulerBoundedEvaluation

open Filter Asymptotics ContinuousLinearMap
open scoped Topology

variable {X H V : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem hasFDerivAt (E : X → H →L[ℝ] V) (C : ℝ) (hE : ∀ x, ‖E x‖ ≤ C)
    (u : ℝ → H) (u' : H) (t : ℝ) (x : X)
    (hu : HasDerivAt u u' t) (D : X →L[ℝ] V)
    (hx : HasFDerivAt (fun y => E y (u t)) D x)
    (hc : ContinuousAt (fun y => E y u') x) :
    HasFDerivAt (fun q : ℝ × X => E q.2 (u q.1))
      (((toSpanSingleton ℝ (E x u')).comp (fst ℝ ℝ X)) + D.comp (snd ℝ ℝ X)) (t,x) := by
  let l : Filter (ℝ × X) := 𝓝 (t,x)
  have htend : Tendsto (Prod.fst : ℝ × X → ℝ) l (𝓝 t) := continuous_fst.tendsto (t,x)
  have hxend : Tendsto (Prod.snd : ℝ × X → X) l (𝓝 x) := continuous_snd.tendsto (t,x)
  have hfst : (fun q : ℝ × X => q.1-t) =O[l] fun q => q-(t,x) := by
    apply IsBigO.of_bound 1
    exact Filter.Eventually.of_forall (fun q => by
      change ‖(q-(t,x)).1‖ ≤ 1*‖q-(t,x)‖
      rw [one_mul]
      exact norm_fst_le (q-(t,x)))
  have hsnd : (fun q : ℝ × X => q.2-x) =O[l] fun q => q-(t,x) := by
    apply IsBigO.of_bound 1
    exact Filter.Eventually.of_forall (fun q => by
      change ‖(q-(t,x)).2‖ ≤ 1*‖q-(t,x)‖
      rw [one_mul]
      exact norm_snd_le (q-(t,x)))
  have hr : (fun q : ℝ × X => u q.1-u t-(q.1-t) • u') =o[l] fun q => q-(t,x) :=
    (hu.isLittleO.comp_tendsto htend).trans_isBigO hfst
  have hbound : (fun q : ℝ × X => E q.2 (u q.1-u t-(q.1-t) • u')) =O[l]
      fun q => u q.1-u t-(q.1-t) • u' := by
    apply IsBigO.of_bound C
    exact Filter.Eventually.of_forall (fun q =>
      ((E q.2).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hE q.2) (norm_nonneg _)))
  have hfirst := hbound.trans_isLittleO hr
  have hcont : Tendsto (fun q : ℝ × X => E q.2 u'-E x u') l (𝓝 0) := by
    simpa only [sub_self,Function.comp_def] using
      (hc.tendsto.comp hxend).sub_const (E x u')
  have hsmall : (fun q : ℝ × X => E q.2 u'-E x u') =o[l] fun _ => (1 : ℝ) :=
    (isLittleO_one_iff ℝ).mpr hcont
  have hsecond : (fun q : ℝ × X => (q.1-t) • (E q.2 u'-E x u')) =o[l]
      fun q => q-(t,x) := by
    have h := (isBigO_refl (fun q : ℝ × X => q.1-t) l).smul_isLittleO hsmall
    simp only [smul_eq_mul,mul_one] at h
    exact h.trans_isBigO hfst
  have hthird : (fun q : ℝ × X => E q.2 (u t)-E x (u t)-D (q.2-x)) =o[l]
      fun q => q-(t,x) :=
    (hx.isLittleO.comp_tendsto hxend).trans_isBigO hsnd
  apply hasFDerivAt_iff_isLittleO.mpr
  apply ((hfirst.add hsecond).add hthird).congr_left
  intro q
  simp only [map_sub,map_smul,add_apply,comp_apply,toSpanSingleton_apply,coe_fst',coe_snd',smul_sub]
  module

end EulerBoundedEvaluation
