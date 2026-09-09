/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftPressure
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketData
import LeanPool.NavierStokesAndEuler.Euler.Foundations.Lagrangian
import LeanPool.NavierStokesAndEuler.Euler.PacketContinuousInverse

/-! The signed pressure correction has a genuine scalar potential in
physical coordinates. Its gradient is exactly the inverse-transpose
reconstruction used in the quantitative correction estimates. -/

@[expose] public section


noncomputable section

namespace EulerAllOrderDriftCorrection

open Set EulerSmoothLimit EulerAllOrderCorrectionData EulerGraphPressurePotential
  EulerPacketInverseFlowGevrey
open scoped ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) (P : ℝ) [Fact (0 < P)]
  {A : Data P D.T} (B : Budget P D.T_pos A)

/-- Physical potential, given by `B.normalizedGraphPotential P k t ∘ Y t`. -/
def Budget.physicalPotential (k : ℝ) (Y : Icc (0 : ℝ) D.T → Space → Space)
    (t : Icc (0 : ℝ) D.T) : Space → ℝ :=
  B.normalizedGraphPotential P k t ∘ Y t

theorem Budget.physicalPotential_joint_continuous (k : ℝ)
    (Y : Icc (0 : ℝ) D.T → Space → Space)
    (hY : Continuous (Function.uncurry Y)) :
    Continuous (B.physicalPotential D P k Y).uncurry := by
  have hc : Continuous (fun z : Icc (0 : ℝ) D.T × Space => (z.1,Y z.1 z.2)) :=
    continuous_fst.prodMk hY
  have hp : Continuous ((B.normalizedGraphPotential P k).uncurry ∘
      (fun z : Icc (0 : ℝ) D.T × Space => (z.1,Y z.1 z.2))) :=
    (B.normalizedGraphPotential_joint_continuous P k).comp hc
  exact hp

variable (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hXY : ∀ t x, X t (Y t x) = x)
  (hY : Continuous (Function.uncurry Y))

include hX hXY hY in
theorem Budget.physicalPotential_smooth (k : ℝ) (hk : k * A.κ = 1)
    (t : Icc (0 : ℝ) D.T) :
    ContDiff ℝ ∞ (B.physicalPotential D P k Y t) :=
  (B.normalizedGraphPotential_smooth P k hk t).comp
    (continuousInverse_contDiff D X Y hX hXY hY t)

include hX hXY hY in
theorem Budget.physicalPotential_gradient (k : ℝ) (hk : k * A.κ = 1)
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    gradient (B.physicalPotential D P k Y t) x =
      A.κ • (D.FInv.field t (Y t x)).adjoint
        (B.pointPressure P t (cylinderGraph P k A.direction (Y t x))) := by
  rw [Budget.physicalPotential, EulerLagrangian.gradient_pullback _ _ _ _
    (continuousInverse_hasFDerivAt D X Y hX hXY hY t x)
    ((B.normalizedGraphPotential_smooth P k hk t).differentiable (by simp) (Y t x)),
    B.normalizedGraphPotential_gradient P k hk t (Y t x), map_smul]

include hX hXY hY in
theorem Budget.physicalPotential_gradient_jet (k : ℝ) (hk : k * A.κ = 1)
    (n : ℕ) (t : Icc (0 : ℝ) D.T) (x : Space) :
    iteratedFDeriv ℝ n (gradient (B.physicalPotential D P k Y t)) x =
      iteratedFDeriv ℝ n (fun y => A.κ • (D.FInv.field t (Y t y)).adjoint
        (B.pointPressure P t (cylinderGraph P k A.direction (Y t y)))) x := by
  congr 2
  funext y
  exact B.physicalPotential_gradient D P X Y hX hXY hY k hk t y

include hX hXY hY in
theorem Budget.physicalPotential_hessian_norm (k : ℝ) (hk : k * A.κ = 1)
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖fderiv ℝ (gradient (B.physicalPotential D P k Y t)) x‖ =
      ‖iteratedFDeriv ℝ 1 (fun y => A.κ • (D.FInv.field t (Y t y)).adjoint
        (B.pointPressure P t (cylinderGraph P k A.direction (Y t y)))) x‖ := by
  rw [← norm_iteratedFDeriv_one,
    B.physicalPotential_gradient_jet D P X Y hX hXY hY k hk 1 t x]

end EulerAllOrderDriftCorrection
