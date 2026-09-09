/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeIntegral
public import LeanPool.NavierStokesAndEuler.Euler.InitialTimePrimitive

@[expose] public section

/-! The actual continuous-time integral agrees with both Bochner primitive constructions. -/

noncomputable section

namespace EulerTimeContinuousPrimitive

open Set MeasureTheory ContinuousLinearMap EulerTimeLp EulerInitialTimePrimitive
  EulerTerminalTimePrimitive EulerVolterraConvolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (T : ℝ) (hT : 0 ≤ T)

theorem initialPrimitive_pathLp (f : C(Icc (0 : ℝ) T,E)) :
    initialPrimitive T hT (pathLp T hT f) = EulerContinuousTimeIntegral.integral T hT f := by
  apply ContinuousMap.ext
  intro t
  rw [initialPrimitive_apply,initialRealPrimitive_eq_integral]
  change (∫ s in (0 : ℝ)..(t : ℝ), zeroExtension T (pathLp T hT f) s) =
    ∫ s in (0 : ℝ)..(t : ℝ), extendPath T hT f s
  rw [intervalIntegral.integral_of_le t.property.1,intervalIntegral.integral_of_le t.property.1]
  apply integral_congr_ae
  have he := (zeroExtension_ae T (pathLp T hT f)).trans (pathLp_ae T hT f)
  exact ae_restrict_of_ae_restrict_of_subset
    (show Ioc (0 : ℝ) (t : ℝ) ⊆ Icc (0 : ℝ) T from
      fun s hs => ⟨hs.1.le,hs.2.trans t.property.2⟩) he

theorem initialTrace_pathLp (f : C(Icc (0 : ℝ) T,E)) :
    initialTrace T hT (pathLp T hT f) =
      -EulerContinuousTimeIntegral.integral T hT f ⟨T,hT,le_rfl⟩ := by
  have he := initialPrimitive_eq_terminal_sub T hT (pathLp T hT f) ⟨T,hT,le_rfl⟩
  rw [initialPrimitive_pathLp,terminalPrimitive_terminal,zero_sub] at he
  simpa only [neg_neg] using congrArg Neg.neg he.symm

theorem primitive_eq_path (p q : C(Icc (0 : ℝ) T,E))
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT p) (q t) (Icc (0 : ℝ) T) t)
    (hzero : p ⟨0,le_rfl,hT⟩ = 0) :
    initialPrimitive T hT (pathLp T hT q) = p := by
  rw [initialPrimitive_pathLp]
  apply ContinuousMap.ext
  intro t
  have he := EulerContinuousTimeIntegral.eq_initial_add_integral T hT q (extendPath T hT p) hd t
  simpa only [extendPath,projIcc_of_mem hT t.property,
    projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩),hzero,zero_add] using he.symm

theorem initialTrace_eq_zero (p q : C(Icc (0 : ℝ) T,E))
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT p) (q t) (Icc (0 : ℝ) T) t)
    (hzero : p ⟨0,le_rfl,hT⟩ = 0) (hterminal : p ⟨T,hT,le_rfl⟩ = 0) :
    initialTrace T hT (pathLp T hT q) = 0 := by
  have he := initialPrimitive_eq_terminal_sub T hT (pathLp T hT q) ⟨T,hT,le_rfl⟩
  rw [primitive_eq_path T hT p q hd hzero,hterminal,terminalPrimitive_terminal,zero_sub] at he
  exact neg_eq_zero.mp he.symm

theorem primitiveTimeLp_eq_pathLp (p q : C(Icc (0 : ℝ) T,E))
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT p) (q t) (Icc (0 : ℝ) T) t)
    (hzero : p ⟨0,le_rfl,hT⟩ = 0) (hterminal : p ⟨T,hT,le_rfl⟩ = 0) :
    primitiveTimeLp T hT (pathLp T hT q) = pathLp T hT p := by
  have hc : terminalPrimitive T hT (pathLp T hT q) = p := by
    apply ContinuousMap.ext
    intro t
    have he := initialPrimitive_eq_terminal_sub T hT (pathLp T hT q) t
    rw [primitive_eq_path T hT p q hd hzero,initialTrace_eq_zero T hT p q hd hzero hterminal,
      sub_zero] at he
    exact he.symm
  change pathLp T hT (terminalPrimitive T hT (pathLp T hT q)) = pathLp T hT p
  rw [hc]

omit [CompleteSpace E] [NormedSpace ℝ E] in
theorem pathLp_injective (hTpos : 0 < T) :
    Function.Injective (pathLp (E := E) T hT) := by
  intro p q he
  have hae : extendPath T hT p =ᵐ[timeMeasure T] extendPath T hT q :=
    (pathLp_ae T hT p).symm.trans (he ▸ pathLp_ae T hT q)
  have hfun := Measure.eqOn_Icc_of_ae_eq volume hTpos.ne hae
    (extendPath_continuous T hT p).continuousOn (extendPath_continuous T hT q).continuousOn
  apply ContinuousMap.ext
  intro t
  simpa only [extendPath,projIcc_of_mem hT t.property] using hfun t.property

end EulerTimeContinuousPrimitive
