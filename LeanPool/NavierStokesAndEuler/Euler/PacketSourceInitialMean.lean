/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedSourceProfiles
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceProfiles
import LeanPool.NavierStokesAndEuler.Euler.MeanPacketContract
import LeanPool.NavierStokesAndEuler.Euler.MeanPacketInitialZero

/-! All actual source mean profiles have the same localized initial
support. When L=0 every mean profile starts from zero. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketProfileRecursion

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)

section Joined

variable (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le))
  (primary : Profile) (hprimary : ProfileRegularity P M.T M.T_pos.le D.support primary)
  (hm : primary.mean = 0)

include hT hprimary hm

theorem joinedSource_mean_initial_support (p : ℕ) (θ : ℝ) :
    tsupport (fun x : Space => (joinedSourceProfiles P M D τ hτ hτT B primary p).mean (0,(x,θ))) ⊆
      {x : Space | ‖M.ℓ • x‖ ≤ 2} := by
  by_cases hp0 : p=0
  · subst p
    simp only [joinedSourceProfiles,profiles_zero]
    change tsupport (fun _ : Space => (0 : Space)) ⊆ _
    simp
  by_cases hp1 : p=1
  · subst p
    simp only [joinedSourceProfiles,profiles_one,hm]
    change tsupport (fun _ : Space => (0 : Space)) ⊆ _
    simp
  have hp : 2 ≤ p := by omega
  let h : Nonempty (EulerMeanPacketProvider.Forcing M
      (meanForce (joinedSourceOperators P M D τ hτ hτT B) p
        (joinedSourceProfiles P M D τ hτ hτT B primary))) :=
    ⟨joinedSourceMeanForcing P M D hT τ hτ hτT B primary hprimary p hp⟩
  unfold joinedSourceProfiles
  rw [profiles_step _ _ p hp]
  exact EulerMeanPacketProvider.meanSolve_initial_support M _ h θ

theorem joinedSource_mean_initial_zero (hL : M.L = 0) (p : ℕ) (x : Space) (θ : ℝ) :
    (joinedSourceProfiles P M D τ hτ hτT B primary p).mean (0,(x,θ)) = 0 := by
  by_cases hp0 : p=0
  · subst p
    simp only [joinedSourceProfiles,profiles_zero]
    rfl
  by_cases hp1 : p=1
  · subst p
    simp only [joinedSourceProfiles,profiles_one,hm,Pi.zero_apply]
  have hp : 2 ≤ p := by omega
  let h : Nonempty (EulerMeanPacketProvider.Forcing M
      (meanForce (joinedSourceOperators P M D τ hτ hτT B) p
        (joinedSourceProfiles P M D τ hτ hτT B primary))) :=
    ⟨joinedSourceMeanForcing P M D hT τ hτ hτT B primary hprimary p hp⟩
  unfold joinedSourceProfiles
  rw [profiles_step _ _ p hp]
  exact EulerMeanPacketProvider.meanSolve_zero_initial M hL _ h x θ

end Joined

section Forward

variable (I Iprimary : EulerTransversePacketProvider.InitialData P D)

include hT

theorem source_mean_initial_support (p : ℕ) (θ : ℝ) :
    tsupport (fun x : Space => (sourceProfiles P M D I Iprimary p).mean (0,(x,θ))) ⊆
      {x : Space | ‖M.ℓ • x‖ ≤ 2} := by
  by_cases hp0 : p=0
  · subst p
    simp only [sourceProfiles,profiles_zero]
    change tsupport (fun _ : Space => (0 : Space)) ⊆ _
    simp
  by_cases hp1 : p=1
  · subst p
    simp only [sourceProfiles,profiles_one]
    change tsupport (fun _ : Space => (0 : Space)) ⊆ _
    simp
  have hp : 2 ≤ p := by omega
  let h : Nonempty (EulerMeanPacketProvider.Forcing M
      (meanForce (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary))) :=
    ⟨sourceMeanForcing P M D hT I Iprimary p hp⟩
  unfold sourceProfiles
  rw [profiles_step _ _ p hp]
  exact EulerMeanPacketProvider.meanSolve_initial_support M _ h θ

theorem source_mean_initial_zero (hL : M.L = 0) (p : ℕ) (x : Space) (θ : ℝ) :
    (sourceProfiles P M D I Iprimary p).mean (0,(x,θ)) = 0 := by
  by_cases hp0 : p=0
  · subst p
    simp only [sourceProfiles,profiles_zero]
    rfl
  by_cases hp1 : p=1
  · subst p
    simp only [sourceProfiles,profiles_one]
    rfl
  have hp : 2 ≤ p := by omega
  let h : Nonempty (EulerMeanPacketProvider.Forcing M
      (meanForce (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary))) :=
    ⟨sourceMeanForcing P M D hT I Iprimary p hp⟩
  unfold sourceProfiles
  rw [profiles_step _ _ p hp]
  exact EulerMeanPacketProvider.meanSolve_zero_initial M hL _ h x θ

end Forward
end EulerPacketCylinderField
