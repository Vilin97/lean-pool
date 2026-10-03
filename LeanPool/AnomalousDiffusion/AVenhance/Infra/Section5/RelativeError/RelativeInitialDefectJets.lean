/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectTrace
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeAnalytic

/-! The positive-jet interface already used by relative_step supplies its
initial n=1 trace. No sup norm of the undifferentiated temperature enters. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section5.RelativeError
open AVenhance

/-- Initial n=1 trace from the actual positive temperature jet interface. -/
theorem relative_initial_trace_one_of_positive_jets
    {A r S : ℝ} {g : Vec 2 → ℝ} {T : ℝ → Vec 2 → ℝ}
    (hT0 : T 0 = g) (hJets : PositiveTemperatureJets A r S T) :
    ∀ i : Fin 2, Real.sqrt (l2NormSq (fun x => spaceGrad g x i)) ≤
      A * ((1 : ℕ).factorial : ℝ) * (A / r) ^ (1 : ℕ) * S := by
  intro i
  have h := hJets 1 (fun _ => i) (by omega) 0 ⟨le_rfl, zero_le_one⟩
  rw [hT0] at h
  simp only [iteratedFDeriv_one_apply, Nat.factorial_one, Nat.cast_one, mul_one,
    pow_one] at h ⊢
  change Real.sqrt (l2NormSq (fun x => fderiv ℝ g x (basisVec i))) ≤ _
  exact h.trans_eq (by ring)
end AVenhance.Infra.Section5.RelativeError
