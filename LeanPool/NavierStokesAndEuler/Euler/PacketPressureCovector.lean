/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPressureWitness
public import LeanPool.NavierStokesAndEuler.Euler.PacketGraphHessian
public import LeanPool.NavierStokesAndEuler.Euler.PacketRecursiveCancellation

@[expose] public section

/-! The genuine physical pressure gradient has a finite covector
expansion. The angular factor k shifts only the high-pressure series. -/

noncomputable section

namespace EulerPacketPressure

open Set Finset InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerPacketPointJets EulerPacketProfileRecursion EulerPacketCylinderField EulerFiniteGrades
  EulerPacketGraphHessian EulerGraphPullback
open scoped ContDiff

def angularPressure (m : Space) (p : ScalarField) : VectorField :=
  fun z => (pressureJet p z).2 angleDirection • m

def covector (k : ℝ) (m : Space) (p : ScalarField) : VectorField :=
  pressureGradient p + k • angularPressure m p

def covectorGrades (N : ℕ) (m : Space) (a : ℕ → Profile) : ℕ → VectorField :=
  assemble N (fun i => pressureGradient (a i).meanPressure+angularPressure m (a i).highPressure)
    (fun i => pressureGradient (a i).highPressure)

def gradientLinear : ScalarJet →ₗ[ℝ] Space where
  toFun J := (toDual ℝ Space).symm (J.2.comp spatialInjection)
  map_add' J K := by simp [add_comp]
  map_smul' c J := by simp [smul_comp]

theorem gradientLinear_jet (p : ScalarField) (z : Domain) :
    gradientLinear (pressureJet p z)=pressureGradient p z := rfl

theorem fieldSum_assemble {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (κ : ℝ) (u c : ℕ → Domain → E) (z : Domain) :
    fieldSum (N+1) κ (assemble N u c) z=fieldSum N κ u z+κ • fieldSum N κ c z := by
  have h := congrArg (fun f : Domain → E => f z) (evaluate_assemble N κ u c)
  simpa only [fieldSum,evaluate,Finset.sum_apply,Pi.smul_apply,Pi.add_apply] using h

theorem pressureJet_finite (N : ℕ) (κ : ℝ) (a : ℕ → Profile) (z : Domain)
    (hm : ∀ i ≤ N, DifferentiableAt ℝ (fun y => (a i).meanPressure (z.1,y)) z.2)
    (hh : ∀ i ≤ N, DifferentiableAt ℝ (fun y => (a i).highPressure (z.1,y)) z.2) :
    pressureJet (fieldSum (N+1) κ (assembledPressure N a)) z =
      evaluate N κ (fun i => pressureJet (a i).meanPressure z)+
        κ • evaluate N κ (fun i => pressureJet (a i).highPressure z) := by
  have hdiff : ∀ i ≤ N+1,
      DifferentiableAt ℝ (fun y => assembledPressure N a i (z.1,y)) z.2 :=
    fun i _ => spatialDifferentiable_assemble N i _ _ z hm hh
  rw [pressureJet_fieldSum (N+1) κ (assembledPressure N a) z hdiff]
  have he : (fun i => pressureJet (assembledPressure N a i) z) =
      assemble N (fun i => pressureJet (a i).meanPressure z)
        (fun i => pressureJet (a i).highPressure z) :=
    funext (fun i => pressureJet_assemble N i _ _ z hm hh)
  rw [he,evaluate_assemble]

theorem covector_finite (N : ℕ) (κ : ℝ) (hκ : κ ≠ 0) (m : Space)
    (a : ℕ → Profile) (z : Domain)
    (hm : ∀ i ≤ N, DifferentiableAt ℝ (fun y => (a i).meanPressure (z.1,y)) z.2)
    (hh : ∀ i ≤ N, DifferentiableAt ℝ (fun y => (a i).highPressure (z.1,y)) z.2)
    (hangle : ∀ i ≤ N, (pressureJet (a i).meanPressure z).2 angleDirection=0) :
    covector κ⁻¹ m (fieldSum (N+1) κ (assembledPressure N a)) z =
      fieldSum (N+1) κ (covectorGrades N m a) z := by
  have hz : fastPressure m (evaluate N κ (fun i => pressureJet (a i).meanPressure z))=0 := by
    rw [map_evaluate]
    unfold evaluate
    apply sum_eq_zero
    intro i hi
    simp only [fastPressure,LinearMap.coe_mk,AddHom.coe_mk,hangle i
      (by have := mem_range.mp hi; omega),zero_smul,smul_zero]
  change gradientLinear (pressureJet (fieldSum (N+1) κ (assembledPressure N a)) z)+
    κ⁻¹ • fastPressure m (pressureJet (fieldSum (N+1) κ (assembledPressure N a)) z)=_
  rw [pressureJet_finite N κ a z hm hh,map_add,map_smul,map_add,map_smul,hz,zero_add,
    smul_smul,inv_mul_cancel₀ hκ,one_smul]
  rw [covectorGrades,fieldSum_assemble]
  simp only [map_evaluate,fieldSum,evaluate_add,Pi.add_apply]
  change evaluate N κ (fun i => pressureGradient (a i).meanPressure z)+
      κ • evaluate N κ (fun i => pressureGradient (a i).highPressure z)+
      evaluate N κ (fun i => angularPressure m (a i).highPressure z)=
    (evaluate N κ (fun i => pressureGradient (a i).meanPressure z)+
      evaluate N κ (fun i => angularPressure m (a i).highPressure z))+
      κ • evaluate N κ (fun i => pressureGradient (a i).highPressure z)
  abel

theorem gradient_graph_covector (k : ℝ) (m : Space) (p : ScalarField) (t : ℝ) (x : Space)
    (hp : DifferentiableAt ℝ (fun z => p (t,z)) (graphMap k m x)) :
    gradient (fun y => p (t,(y,k*⟪m,y⟫_ℝ))) x = covector k m p (t,(x,k*⟪m,x⟫_ℝ)) := by
  have h := gradient_graph k m x hp
  simpa only [covector,angularPressure,Pi.add_apply,Pi.smul_apply,
    pressureGradient_eq_spatialDual,pressureJet_angle,smul_smul,spatialGradient,angularDerivative,
    graphMap_apply] using h

theorem gradient_physical_covector (k : ℝ) (m : Space) (p : ScalarField) (t : ℝ)
    (Y : Space → Space) (J : Space →L[ℝ] Space) (x : Space)
    (hY : HasFDerivAt Y J x)
    (hp : DifferentiableAt ℝ (fun z => p (t,z)) (graphMap k m (Y x))) :
    gradient (fun y => p (t,(Y y,k*⟪m,Y y⟫_ℝ))) x =
      J.adjoint (covector k m p (t,(Y x,k*⟪m,Y x⟫_ℝ))) := by
  have hg : DifferentiableAt ℝ (fun y => p (t,(y,k*⟪m,y⟫_ℝ))) (Y x) :=
    hp.comp (Y x) (graphMap k m).differentiableAt
  have h := EulerLagrangian.gradient_pullback (fun y => p (t,(y,k*⟪m,y⟫_ℝ))) Y J x hY hg
  rw [gradient_graph_covector k m p t (Y x) hp] at h
  exact h

end EulerPacketPressure
