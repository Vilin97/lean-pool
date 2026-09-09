/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryTameEnergy
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerL2Stability

@[expose] public section

/-! Every integer Sobolev order propagates on the same interval on which
the actual H³ norm is bounded. There is no order-dependent shortening
of time and no postulated energy differential inequality. -/

noncomputable section

namespace EulerOrdinarySobolev

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal
  EulerMeanClassical EulerVolterraConvolution Finset
open scoped ContDiff Topology

def wordCount (m : ℕ) : ℝ := ∑ n ∈ range (m+1), (3 : ℝ)^n

theorem wordCount_nonneg (m : ℕ) : 0 ≤ wordCount m := sum_nonneg (fun _ _ => by positivity)

theorem tensorNorm_le_wordCount (A : SmoothL2Field Space) (m : ℕ) (N : ℝ)
    (hN : WordBound m N A) : tensorNorm m A ≤ wordCount m*N := by
  calc
    _ ≤ ∑ n ∈ range (m+1), (3 : ℝ)^n*N := sum_le_sum
      (fun n hn => wordBound_jet_norm hN (by have := mem_range.mp hn; omega))
    _ = _ := by rw [← sum_mul]; rfl

theorem tensorNorm_le_energy (A : SmoothL2Field Space) (m : ℕ) :
    tensorNorm m A ≤ wordCount m*Real.sqrt (wordEnergy m A) :=
  tensorNorm_le_wordCount A m _ (wordBound_sqrt_energy m A)

namespace Evolution

variable {T : ℝ} {hT : 0 ≤ T}

def integerEnergyPath (U : Evolution T hT) (m : ℕ) : C(Icc (0 : ℝ) T,ℝ) :=
  ⟨fun t => wordEnergy m (U.velocity t),wordEnergy_continuous U.velocity U.velocity_continuous m⟩

def integerEnergyDerivative (U : Evolution T hT) (m : ℕ) (t : Icc (0 : ℝ) T) : ℝ :=
  integerEnergyProduction m (U.velocity t) (U.derivative t)

theorem derivative_eq_eulerRhs (U : Evolution T hT) (t : Icc (0 : ℝ) T) :
    U.derivative t=eulerRhs (U.velocity t) (U.pressureForce t) := by
  apply field_ext
  funext x
  rw [derivative_field,eulerRhs_field]

theorem integerEnergy_hasDerivWithinAt (U : Evolution T hT) (m : ℕ) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (U.integerEnergyPath m)) (U.integerEnergyDerivative m t)
      (Icc (0 : ℝ) T) t := by
  apply wordEnergy_hasDerivWithinAt T hT U.velocity U.derivative
    U.velocity_continuous U.derivative_continuous
  intro r hr x
  simpa only [derivative_field] using U.time_law r hr x

theorem integerEnergyDerivative_bound (U : Evolution T hT) (m : ℕ) (hm : 3 ≤ m)
    (M : ℝ) (hM : ∀ t, WordBound 3 M (U.velocity t)) (t : Icc (0 : ℝ) T) :
    U.integerEnergyDerivative m t ≤ tameEnergyConstant m*M*U.integerEnergyPath m t := by
  rw [integerEnergyDerivative,derivative_eq_eulerRhs]
  apply integer_energy_tame _ _ m hm M (hM t) _ (U.solenoidal t) (U.gradient t)
  exact solenoidal_representative_divergence _ (U.solenoidal t) _ (U.velocity t).smooth
    (U.velocity t).toLp_ae

theorem integer_energy_bound (U : Evolution T hT) (m : ℕ) (hm : 3 ≤ m)
    (M : ℝ) (hM : ∀ t, WordBound 3 M (U.velocity t)) (t : Icc (0 : ℝ) T) :
    wordEnergy m (U.velocity t) ≤ wordEnergy m (U.velocity ⟨0,le_rfl,hT⟩)*
      Real.exp (tameEnergyConstant m*M*t) := by
  have hd (r : ℝ) (hr : r ∈ Ico 0 T) :
      HasDerivWithinAt (extendPath T hT (U.integerEnergyPath m))
        (U.integerEnergyDerivative m (projIcc 0 T hT r)) (Icc 0 T) r := by
    have h := U.integerEnergy_hasDerivWithinAt m ⟨r,hr.1,hr.2.le⟩
    simpa only [projIcc_of_mem hT (show r ∈ Icc 0 T from ⟨hr.1,hr.2.le⟩)] using h
  have hb (r : ℝ) (hr : r ∈ Ico 0 T) :
      U.integerEnergyDerivative m (projIcc 0 T hT r) ≤
        (tameEnergyConstant m*M)*extendPath T hT (U.integerEnergyPath m) r :=
    U.integerEnergyDerivative_bound m hm M hM (projIcc 0 T hT r)
  have h := linear_stability_within (extendPath T hT (U.integerEnergyPath m))
    (fun r => U.integerEnergyDerivative m (projIcc 0 T hT r)) (tameEnergyConstant m*M) T
    ((U.integerEnergyPath m).continuous.comp continuous_projIcc).continuousOn hd hb t t.property
  simpa only [extendPath,projIcc_of_mem hT t.property,
    projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩),
    integerEnergyPath,ContinuousMap.coe_mk] using h

theorem integer_energy_uniform (U : Evolution T hT) (m : ℕ) (hm : 3 ≤ m)
    (M : ℝ) (hM : ∀ t, WordBound 3 M (U.velocity t)) (t : Icc (0 : ℝ) T) :
    wordEnergy m (U.velocity t) ≤ wordEnergy m (U.velocity ⟨0,le_rfl,hT⟩)*
      Real.exp (tameEnergyConstant m*M*T) := by
  apply (U.integer_energy_bound m hm M hM t).trans
  apply mul_le_mul_of_nonneg_left _ (wordEnergy_nonneg m _)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left t.property.2
    (mul_nonneg (tameEnergyConstant_nonneg m) (wordBound_nonneg (hM t)))

theorem tensorNorm_uniform (U : Evolution T hT) (m : ℕ) (hm : 3 ≤ m)
    (M : ℝ) (hM : ∀ t, WordBound 3 M (U.velocity t)) (t : Icc (0 : ℝ) T) :
    tensorNorm m (U.velocity t) ≤ wordCount m*
      Real.sqrt (wordEnergy m (U.velocity ⟨0,le_rfl,hT⟩)*Real.exp (tameEnergyConstant m*M*T)) :=
  (tensorNorm_le_energy _ m).trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (U.integer_energy_uniform m hm M hM t)) (wordCount_nonneg m))

theorem higher_energy_of_h3 (U : Evolution T hT) (m : ℕ) (hm : 3 ≤ m)
    (M : ℝ) (hM : ∀ t, tensorNorm 3 (U.velocity t) ≤ M) (t : Icc (0 : ℝ) T) :
    wordEnergy m (U.velocity t) ≤ wordEnergy m (U.velocity ⟨0,le_rfl,hT⟩)*
      Real.exp (tameEnergyConstant m*M*T) := by
  apply U.integer_energy_uniform m hm M _ t
  intro s n hn w
  exact (wordBound_tensorNorm 3 (U.velocity s) n hn w).trans (hM s)

end Evolution
end EulerOrdinarySobolev
