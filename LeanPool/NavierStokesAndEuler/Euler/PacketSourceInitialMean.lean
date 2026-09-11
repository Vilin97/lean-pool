/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedSourceProfiles
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceProfiles
import LeanPool.NavierStokesAndEuler.Euler.MeanPacketContract
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketProvider
import LeanPool.NavierStokesAndEuler.Euler.MeanPacketConstraints

/-! All actual source mean profiles have the same localized initial
support. When L=0 every mean profile starts from zero. -/

section

/-! The actual localized mean initial condition vanishes when the source
boundary coefficient L is zero. -/

@[expose] public section

noncomputable section

namespace EulerMeanPacketProvider

open Set MeasureTheory EulerSmoothLimit EulerMeanSolenoidal EulerMeanBoundary
  EulerPacketProfileRecursion

namespace Forcing

variable {D : Data} {raw : VectorField} (G : Forcing D raw)

theorem vector_initial_zero (hL : D.L = 0) (x : Space) (θ : ℝ) :
    G.vector (0,(x,θ)) = 0 := by
  have h := G.initial_vector_ae θ
  have he : D.L • (boundaryOperator (scaledCutoff D.ℓ D.ℓ_pos))
      (G.solution.label 0 : L2) = 0 := by
    exact (congrArg (fun c : ℝ => c • (boundaryOperator (scaledCutoff D.ℓ D.ℓ_pos))
      (G.solution.label 0 : L2)) hL).trans (zero_smul ℝ _)
  rw [he] at h
  have hz : (fun y => G.vector (0,(y,θ))) =ᵐ[volume] (fun _ => (0 : Space)) :=
    h.trans (Lp.coeFn_zero Space 2 volume)
  have hc : Continuous (fun y => G.vector (0,(y,θ))) :=
    (G.vector_spatial_smooth 0).continuous.comp (continuous_id.prodMk continuous_const)
  exact congrFun (Measure.eq_of_ae_eq hz hc continuous_const) x

end Forcing

theorem meanSolve_zero_initial (D : Data) (hL : D.L = 0) (raw : VectorField)
    (h : Nonempty (Forcing D raw)) (x : Space) (θ : ℝ) :
    (meanSolve D raw).1 (0,(x,θ)) = 0 := by
  rw [meanSolve_of_admissible D raw h]
  exact (Classical.choice h).vector_initial_zero hL x θ

end EulerMeanPacketProvider

end
end

end

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
