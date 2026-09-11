/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! A continuous Banach-valued path has its strong time derivative once
that derivative is continuous and is verified through a separating family
of bounded linear observations. The proof reconstructs the actual Bochner
primitive and does not infer strong convergence from pointwise convergence. -/

@[expose] public section


noncomputable section

namespace EulerSeparatingTimeDerivative

open Set MeasureTheory EulerVolterraConvolution EulerContinuousTimeIntegral
open scoped Topology

variable {E F I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  (T : ℝ) (hT : 0 ≤ T) (f g : C(Icc (0 : ℝ) T, E))
  (L : I → E →L[ℝ] F)
  (hsep : Function.Injective (fun u : E => fun i : I => L i u))
  (hd : ∀ i t (ht : t ∈ Ioo 0 T),
    HasDerivAt (fun r => L i (extendPath T hT f r)) (L i (g ⟨t, ht.1.le, ht.2.le⟩)) t)

include hsep hd in
theorem eq_initial_add_integral (t : Icc (0 : ℝ) T) :
    f t = f ⟨0,le_rfl,hT⟩ + integral T hT g t := by
  apply hsep
  funext i
  change L i (f t) = L i (f ⟨0,le_rfl,hT⟩ + integral T hT g t)
  have hc : Continuous (fun r => L i (extendPath T hT f r)) :=
    (L i).continuous.comp (extendPath_continuous T hT f)
  have hg : Continuous (fun r => L i (extendPath T hT g r)) :=
    (L i).continuous.comp (extendPath_continuous T hT g)
  have hobs : L i (integral T hT g t) = L i (f t)-L i (f ⟨0,le_rfl,hT⟩) := by
    rw [integral_apply, realIntegral,
      ← (L i).intervalIntegral_comp_comm ((extendPath_continuous T hT g).intervalIntegrable 0 t)]
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.property.1
      hc.continuousOn (f' := fun r => L i (extendPath T hT g r))
      (fun r hr => by
        have hrT : r ∈ Ioo 0 T := ⟨hr.1,hr.2.trans_le t.property.2⟩
        simpa only [extendPath,projIcc_of_mem hT ⟨hrT.1.le,hrT.2.le⟩]
          using hd i r hrT)
      (hg.intervalIntegrable 0 t)
    simpa only [extendPath,projIcc_of_mem hT t.property,
      projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩)] using he
  rw [map_add,hobs]
  abel

include hsep hd in
theorem hasDerivWithinAt (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT f) (g t) (Icc (0 : ℝ) T) t := by
  have hp : HasDerivWithinAt
      (fun r => f ⟨0,le_rfl,hT⟩+realIntegral T hT g r) (g t) (Icc (0 : ℝ) T) t := by
    have hp := (realIntegral_hasDerivAt T hT g t).const_add (f ⟨0,le_rfl,hT⟩)
    rw [show extendPath T hT g t = g t from by
      simp only [extendPath,projIcc_of_mem hT t.property]] at hp
    exact hp.hasDerivWithinAt
  apply hp.congr_of_mem _ t.property
  intro r hr
  simpa only [extendPath,projIcc_of_mem hT hr,integral_apply] using
    eq_initial_add_integral T hT f g L hsep hd ⟨r,hr⟩

include hsep hd in
theorem hasDerivAt (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (extendPath T hT f) (g ⟨t,ht.1.le,ht.2.le⟩) t :=
  (hasDerivWithinAt T hT f g L hsep hd ⟨t,ht.1.le,ht.2.le⟩).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

end EulerSeparatingTimeDerivative
