/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.Examples.ShearFlowLocalData
public import LeanPool.CaffarelliKohnNirenberg.Setting.Examples.ShearFlowEnergy

/-!
# A nonzero suitable weak solution

The smooth decaying shear satisfies every clause of the suitable weak-solution
definition on all space and the time interval (0,1), with zero pressure and force.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic


namespace CKN

/-- The explicit decaying shear is a suitable weak solution with zero force. -/
theorem isSuitableWeakSolutionIntegrable_shearFlow :
    IsSuitableWeakSolutionIntegrable Set.univ (Ioo 0 1) 3
      shearFlow shearFlowGrad (fun _ => 0) (fun _ => 0) := by
  refine ⟨isOpen_univ, isOpen_Ioo, ordConnected_Ioo, by norm_num, ?_,
    shearFlow_localData, shearFlow_divergence, ?_, ?_⟩
  · intro Ω' J hbox i
    exact MemLp.zero
  · intro φ hφ
    simpa only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero] using
      shearFlow_momentum φ hφ
  · intro ψ hψ hnonneg
    obtain ⟨hgrad, henergy, heq⟩ := shearFlow_energyIdentity ψ hψ
    refine ⟨hgrad, ?_, ?_⟩
    · simpa only [Pi.zero_apply, mul_zero, add_zero, zero_mul, Finset.sum_const_zero] using henergy
    · simpa only [Pi.zero_apply, mul_zero, add_zero, zero_mul, Finset.sum_const_zero] using heq.le

end CKN
