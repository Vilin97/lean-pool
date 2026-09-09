/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketData
import LeanPool.NavierStokesAndEuler.Euler.ContinuousInverseDerivative
import LeanPool.NavierStokesAndEuler.Euler.PacketInverseFlowContinuity
import LeanPool.NavierStokesAndEuler.Euler.PacketInverseFlowGevrey

/-! The actual inverse parent flow needs only continuity as an input.
Its differentiability, smooth spatial slices, and jointly continuous
spatial jets follow from the prescribed Jacobian and inverse identities. -/

@[expose] public section


noncomputable section

open scoped ContDiff

namespace EulerPacketInverseFlowGevrey

open Set EulerSmoothLimit EulerContinuousInverseDerivative

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U)
  (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hXY : ∀ t x, X t (Y t x) = x)
  (hY : Continuous (Function.uncurry Y))

include hX hXY hY in
theorem continuousInverse_hasFDerivAt (t : Icc (0 : ℝ) D.T) (x : Space) :
    HasFDerivAt (Y t) (D.FInv.field t (Y t x)) x :=
  hasFDerivAt_inverse (X t) (Y t) x (D.F.field t (Y t x)) (D.FInv.field t (Y t x))
    (hY.uncurry_left t).continuousAt (hX t (Y t x))
    (Filter.Eventually.of_forall (hXY t)) (D.inverse_left t (Y t x))

include hX hXY hY in
theorem continuousInverse_differentiable (t : Icc (0 : ℝ) D.T) :
    Differentiable ℝ (Y t) :=
  fun x => (continuousInverse_hasFDerivAt D X Y hX hXY hY t x).differentiableAt

include hX hXY hY in
theorem continuousInverse_contDiff (t : Icc (0 : ℝ) D.T) : ContDiff ℝ ∞ (Y t) :=
  inverseFlow_contDiff D X Y hX (continuousInverse_differentiable D X Y hX hXY hY) hXY t

include hX hXY hY in
theorem continuousInverse_jet_continuous (n : ℕ) :
    Continuous (fun p : Icc (0 : ℝ) D.T × Space =>
      iteratedFDeriv ℝ n (Y p.1) p.2) :=
  inverseFlow_jet_continuous D X Y hX
    (continuousInverse_differentiable D X Y hX hXY hY) hXY hY n

end EulerPacketInverseFlowGevrey
