/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitialFields
public import LeanPool.NavierStokesAndEuler.Euler.PhysicalL2Scaling
public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedSourceProfiles
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceProfiles
import LeanPool.NavierStokesAndEuler.Euler.MeanPacketContract
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketProvider
import LeanPool.NavierStokesAndEuler.Euler.MeanPacketConstraints

/-! Related estimates used together by the same construction modules. -/

section

/-! Common compact support for the two actual initial increments after
the physical spatial dilation. -/

@[expose] public section

noncomputable section

namespace EulerPhysicalL2Scaling

open Set EulerSmoothLimit

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [NormedSpace ℝ V] in
theorem support_in_ball_of_zero (f : Space → V) (R : ℝ)
    (hz : ∀ x, R < ‖x‖ → f x = 0) : tsupport f ⊆ Metric.closedBall 0 R := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall,dist_zero_right]
  by_contra h
  exact hx (hz x (lt_of_not_ge h))

theorem scale_support (ell : ℝ) (hell : 0 < ell) (f : Space → V) (R : ℝ)
    (hs : tsupport f ⊆ Metric.closedBall 0 R) :
    tsupport (scale ell f) ⊆ Metric.closedBall 0 (ell*R) := by
  apply support_in_ball_of_zero
  intro x hx
  have hn : ell⁻¹ • x ∉ tsupport f := by
    intro hm
    have hb := hs hm
    rw [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hell)] at hb
    have h := mul_le_mul_of_nonneg_left hb hell.le
    rw [← mul_assoc,mul_inv_cancel₀ hell.ne',one_mul] at h
    linarith
  exact congrArg (ell • ·) (image_eq_zero_of_notMem_tsupport hn) |>.trans (smul_zero ell)

end EulerPhysicalL2Scaling

namespace EulerPacketInitial

open Set EulerSmoothLimit EulerPacketProfileRecursion EulerPacketCylinderField
    EulerPhysicalL2Scaling

variable {P T : ℝ} [Fact (0 < P)] {hT : 0 ≤ T} {N : ℕ}
  {a : ℕ → Profile} {support : Set Space}

theorem high_scaled_support
    (G : ∀ i, i ≤ N → ProfileRegularity P T hT support (a i))
    (t : Icc (0 : ℝ) T) (κ k : ℝ) (m : Space)
    (ell : ℝ) (hell : 0 < ell) (R : ℝ) (hs : support ⊆ Metric.closedBall 0 R) :
    tsupport (scale ell (fun x => high N κ t a (t,(x,k*inner ℝ m x)))) ⊆
      Metric.closedBall 0 (ell*R) := by
  apply scale_support ell hell
  apply support_in_ball_of_zero
  intro x hx
  apply high_zero_outside G t κ t x _ (k*inner ℝ m x)
  intro hm
  have hb := hs hm
  rw [Metric.mem_closedBall,dist_zero_right] at hb
  linarith

theorem mean_scaled_support (κ k : ℝ) (m : Space) (ell : ℝ) (hell : 0 < ell)
    (a : ℕ → Profile)
    (hs : ∀ i, i ≤ N → ∀ θ, tsupport (fun x => (a i).mean (0, (x, θ))) ⊆
      {x : Space | ‖ell • x‖ ≤ 2}) :
    tsupport (scale ell (fun x => mean N κ 0 a (0,(x,k*inner ℝ m x)))) ⊆
      Metric.closedBall 0 2 := by
  apply support_in_ball_of_zero
  intro x hx
  have hz : mean N κ 0 a (0,(ell⁻¹ • x,k*inner ℝ m (ell⁻¹ • x))) = 0 := by
    apply mean_zero_outside 0 κ 0 a {y : Space | ‖ell • y‖ ≤ 2}
    · intro i hi y hy θ
      exact image_eq_zero_of_notMem_tsupport
        (f := fun x : Space => (a i).mean (0,(x,θ))) (fun hm => hy (hs i hi θ hm))
    · change ¬‖ell • (ell⁻¹ • x)‖ ≤ 2
      rw [smul_smul,mul_inv_cancel₀ hell.ne',one_smul]
      exact not_le.mpr hx
  change ell • mean N κ 0 a (0,(ell⁻¹ • x,k*inner ℝ m (ell⁻¹ • x))) = 0
  rw [hz,smul_zero]

end EulerPacketInitial

end
end

end

section

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

end
end

end
