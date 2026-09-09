/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryRegularizedFlow
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryQuadraticControl
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerHigherEnergy

@[expose] public section

/-! Uniform energy bounds for the actual regularized flows. Symmetry
and translation commutation transfer the exact energy production to
the smoothed velocity, where the checked Euler cancellations apply. -/

noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
  EulerMeanClassical EulerVolterraConvolution Finset
open scoped ContDiff Topology

namespace SmoothingOperator

variable (S : SmoothingOperator)

theorem rhs_pairing (A : SmoothL2Field Space) {n : ℕ} (w : Fin n → Fin 3) :
    ⟪(wordField A w).toLp,(wordField (S.rhs A.toLp) w).toLp⟫_ℝ=
      ⟪(wordField (S.field A.toLp) w).toLp,
        (wordField (fieldNeg (advectionField (S.field A.toLp) (S.field A.toLp))) w).toLp⟫_ℝ := by
  simp only [rhs,wordField_neg,toLp_fieldNeg,inner_neg_right,field_word,← S.symmetric]

theorem rhs_energy (A : SmoothL2Field Space) (m : ℕ) (hm : 3 ≤ m)
    (M : ℝ) (hM : WordBound 3 M A) :
    integerEnergyProduction m A (S.rhs A.toLp) ≤ tameEnergyConstant m*M*wordEnergy m A := by
  let B := S.field A.toLp
  have he : fieldNeg (advectionField B B)=eulerRhs B (fieldSub B B) := by
    apply field_ext
    funext x
    simp only [fieldNeg_field,advectionField_field,eulerRhs_field,fieldSub_field,sub_self,sub_zero]
  have hp : (fieldSub B B).toLp ∈ gradientSpace := by
    rw [toLp_fieldSub,sub_self]
    exact gradientSpace.zero_mem
  have hb : B.toLp ∈ solenoidalSpace := by
    rw [field_toLp]
    exact S.solenoidal _
  have hx : integerEnergyProduction m A (S.rhs A.toLp)=
      integerEnergyProduction m B (eulerRhs B (fieldSub B B)) := by
    simp only [integerEnergyProduction,S.rhs_pairing,← he,B]
  rw [hx]
  apply (integer_energy_tame B (fieldSub B B) m hm M
    (S.field_wordBound A 3 M hM) (S.field_divergence A.toLp) hb hp).trans
  exact mul_le_mul_of_nonneg_left (S.field_energy_le A m)
    (mul_nonneg (tameEnergyConstant_nonneg m) (wordBound_nonneg hM))

end SmoothingOperator

namespace RegularizedEvolution

variable {S : SmoothingOperator} {T : ℝ} {hT : 0 ≤ T} (U : RegularizedEvolution S T hT)

def energy (m : ℕ) : C(Icc (0 : ℝ) T,ℝ) :=
  ⟨fun t => wordEnergy m (U.velocity t),wordEnergy_continuous U.velocity U.velocity_continuous m⟩

def energyDerivative (m : ℕ) (t : Icc (0 : ℝ) T) : ℝ :=
  integerEnergyProduction m (U.velocity t) (U.derivative t)

theorem energy_time (m : ℕ) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (U.energy m)) (U.energyDerivative m t) (Icc (0 : ℝ) T) t := by
  apply wordEnergy_hasDerivWithinAt T hT U.velocity U.derivative
    U.velocity_continuous U.derivative_continuous
  intro r hr x
  exact (U.pointwise_time ⟨r,hr.1.le,hr.2.le⟩ x).hasDerivAt (Icc_mem_nhds hr.1 hr.2)

theorem energy_tame (m : ℕ) (hm : 3 ≤ m) (M : ℝ) (t : Icc (0 : ℝ) T)
    (hM : WordBound 3 M (U.velocity t)) :
    U.energyDerivative m t ≤ tameEnergyConstant m*M*U.energy m t :=
  S.rhs_energy (U.velocity t) m hm M hM

theorem energy_quadratic (t : Icc (0 : ℝ) T) :
    U.energyDerivative 3 t ≤ tameEnergyConstant 3*(1+U.energy 3 t)^2 := by
  have h := U.energy_tame 3 (le_refl 3) _ t (wordBound_sqrt_energy 3 (U.velocity t))
  change U.energyDerivative 3 t ≤ tameEnergyConstant 3*Real.sqrt (U.energy 3 t)*U.energy 3 t at h
  apply h.trans
  have hx : 0 ≤ U.energy 3 t := wordEnergy_nonneg 3 _
  have hr : 0 ≤ Real.sqrt (U.energy 3 t) := Real.sqrt_nonneg _
  have hs := Real.sq_sqrt hx
  have hsq : Real.sqrt (U.energy 3 t)*U.energy 3 t ≤ (1+U.energy 3 t)^2 := by
    have hl : Real.sqrt (U.energy 3 t) ≤ 1+U.energy 3 t := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hl hx]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsq (tameEnergyConstant_nonneg 3)

theorem short_energy (hsmall : tameEnergyConstant 3*T ≤ (1+U.energy 3 ⟨0,le_rfl,hT⟩)⁻¹/2)
    (t : Icc (0 : ℝ) T) : U.energy 3 t ≤ 2*U.energy 3 ⟨0,le_rfl,hT⟩+1 := by
  have hp (r : ℝ) (hr : r ∈ Icc 0 T) : projIcc 0 T hT r=⟨r,hr⟩ := projIcc_of_mem hT hr
  have h := quadratic_energy_bound T (tameEnergyConstant 3) hT
    (extendPath T hT (U.energy 3)) (fun r => U.energyDerivative 3 (projIcc 0 T hT r))
    ((U.energy 3).continuous.comp continuous_projIcc).continuousOn
    (fun r _hr => wordEnergy_nonneg 3 (U.velocity (projIcc 0 T hT r)))
    (fun r hr => by simpa only [hp r hr] using U.energy_time 3 ⟨r,hr⟩)
    (fun r _hr => U.energy_quadratic (projIcc 0 T hT r)) (tameEnergyConstant_nonneg 3)
    (by simpa only [extendPath,hp 0 ⟨le_rfl,hT⟩] using hsmall) t t.property
  simpa only [extendPath,hp (t : ℝ) t.property,hp 0 ⟨le_rfl,hT⟩] using h

theorem energy_uniform (m : ℕ) (hm : 3 ≤ m) (M : ℝ)
    (hM : ∀ t, WordBound 3 M (U.velocity t)) (t : Icc (0 : ℝ) T) :
    wordEnergy m (U.velocity t) ≤ wordEnergy m (U.velocity ⟨0,le_rfl,hT⟩)*
      Real.exp (tameEnergyConstant m*M*T) := by
  have hd (r : ℝ) (hr : r ∈ Ico 0 T) :
      HasDerivWithinAt (extendPath T hT (U.energy m))
        (U.energyDerivative m (projIcc 0 T hT r)) (Icc 0 T) r := by
    simpa only [projIcc_of_mem hT (show r ∈ Icc 0 T from ⟨hr.1,hr.2.le⟩)] using
      U.energy_time m ⟨r,hr.1,hr.2.le⟩
  have he := linear_stability_within (extendPath T hT (U.energy m))
    (fun r => U.energyDerivative m (projIcc 0 T hT r)) (tameEnergyConstant m*M) T
    ((U.energy m).continuous.comp continuous_projIcc).continuousOn hd
    (fun r _hr => U.energy_tame m hm M (projIcc 0 T hT r) (hM _)) t t.property
  have hi : wordEnergy m (U.velocity t) ≤ wordEnergy m (U.velocity ⟨0,le_rfl,hT⟩)*
      Real.exp (tameEnergyConstant m*M*t) := by
    simpa only [extendPath,projIcc_of_mem hT t.property,
      projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩),energy,ContinuousMap.coe_mk]
        using he
  apply hi.trans
  apply mul_le_mul_of_nonneg_left _ (wordEnergy_nonneg m _)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left t.property.2
    (mul_nonneg (tameEnergyConstant_nonneg m) (wordBound_nonneg (hM t)))

end RegularizedEvolution

def regularizedTime (A : SmoothL2Field Space) : ℝ :=
  (2*(1+tameEnergyConstant 3)*(1+wordEnergy 3 A))⁻¹

theorem regularizedTime_pos (A : SmoothL2Field Space) : 0 < regularizedTime A := by
  have := tameEnergyConstant_nonneg 3
  have := wordEnergy_nonneg 3 A
  unfold regularizedTime
  positivity

def regularizedH3 (A : SmoothL2Field Space) : ℝ := Real.sqrt (2*wordEnergy 3 A+1)

theorem regularized_h3 (A : SmoothL2Field Space) {S : SmoothingOperator}
    (U : RegularizedEvolution S (regularizedTime A) (regularizedTime_pos A).le)
    (hinit : U.velocity ⟨0,le_rfl,(regularizedTime_pos A).le⟩=A)
    (t : Icc (0 : ℝ) (regularizedTime A)) : WordBound 3 (regularizedH3 A) (U.velocity t) := by
  have he : U.energy 3 ⟨0,le_rfl,(regularizedTime_pos A).le⟩=wordEnergy 3 A := congrArg (wordEnergy
    3) hinit
  have hc : 0 < 1+tameEnergyConstant 3 := by linarith [tameEnergyConstant_nonneg 3]
  have ha : 0 < 1+wordEnergy 3 A := by linarith [wordEnergy_nonneg 3 A]
  have hs : tameEnergyConstant 3*regularizedTime A ≤ (1+wordEnergy 3 A)⁻¹/2 := by
    calc
      _ ≤ (1+tameEnergyConstant 3)*regularizedTime A := by
        nlinarith [regularizedTime_pos A]
      _ = _ := by unfold regularizedTime; field_simp [hc.ne',ha.ne']
  have hu := U.short_energy (by simpa only [he] using hs) t
  rw [he] at hu
  intro n hn w
  exact (wordBound_sqrt_energy 3 (U.velocity t) n hn w).trans (Real.sqrt_le_sqrt hu)

theorem regularized_all_order (A : SmoothL2Field Space) (q : ℕ) :
    ∃ C : ℝ, ∀ (S : SmoothingOperator)
      (U : RegularizedEvolution S (regularizedTime A) (regularizedTime_pos A).le),
      U.velocity ⟨0,le_rfl,(regularizedTime_pos A).le⟩=A →
      ∀ t, tensorNorm q (U.velocity t) ≤ C := by
  let m := max 3 q
  refine ⟨wordCount q*Real.sqrt (wordEnergy m A*
    Real.exp (tameEnergyConstant m*regularizedH3 A*regularizedTime A)),?_⟩
  intro S U hinit t
  have hu := U.energy_uniform m (le_max_left 3 q) (regularizedH3 A)
    (regularized_h3 A U hinit) t
  rw [hinit] at hu
  apply tensorNorm_le_wordCount
  intro n hn w
  exact (wordBound_sqrt_energy m (U.velocity t) n (hn.trans (le_max_right 3 q)) w).trans
    (Real.sqrt_le_sqrt hu)

end EulerOrdinarySobolev
