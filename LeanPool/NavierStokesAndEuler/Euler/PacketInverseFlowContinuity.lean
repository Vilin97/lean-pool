/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketData
import LeanPool.NavierStokesAndEuler.Euler.InverseMapJetContinuity
import LeanPool.NavierStokesAndEuler.Euler.PacketInverseFlowGevrey

/-!
# Joint spatial-jet continuity for the prescribed inverse parent flow

The smooth bounded coefficient paths already carry genuine continuous
spatial jets.  Their evaluation, together with the actual inverse identity,
supplies all inverse-flow continuity hypotheses used by Sobolev transport.
-/

@[expose] public section


noncomputable section

open scoped ContDiff BoundedContinuousFunction

namespace EulerMeanCoefficients.SmoothCoefficientPath

open EulerSmoothLimit

theorem jet_joint_continuous {K V : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : SmoothCoefficientPath K V) (n : ℕ) :
    Continuous (fun p : K × Space =>
      iteratedFDeriv ℝ n (A.field p.1 : Space → V) p.2) := by
  have heq : (fun p : K × Space =>
      iteratedFDeriv ℝ n (A.field p.1 : Space → V) p.2) =
      fun p => A.jet n p.1 p.2 := by
    funext p
    exact (A.jet_eq n p.1 p.2).symm
  rw [heq]
  fun_prop

end EulerMeanCoefficients.SmoothCoefficientPath

namespace EulerPacketInverseFlowGevrey

open Set EulerSmoothLimit EulerGevreyComposition

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U)
  (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hY : ∀ t, Differentiable ℝ (Y t))
  (hXY : ∀ t x, X t (Y t x) = x)
  (hYjoint : Continuous (Function.uncurry Y))

include hX hY hXY hYjoint in
/-- Every spatial inverse-flow jet is jointly continuous in time and space,
derived from the original coefficient path and actual inverse relation. -/
theorem inverseFlow_jet_continuous (n : ℕ) :
    Continuous (fun p : Icc (0 : ℝ) D.T × Space =>
      iteratedFDeriv ℝ n (Y p.1) p.2) := by
  exact continuous_iteratedFDeriv_of_fderiv_eq_comp Y
    (fun t => (D.FInv.field t : Space → Space →L[ℝ] Space)) hYjoint hY
    D.FInv.smooth D.FInv.jet_joint_continuous
    (inverseFlow_fderiv D X Y hX hY hXY) n

end EulerPacketInverseFlowGevrey
