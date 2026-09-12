/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTermBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceOperators
import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientPathJets

/-! The nonlinear packet coefficient budget follows from the original spatial
jets of the inverse deformation and strain.  The transported unit normal uses
the same radius and amplitude. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerMeanCoefficients EulerPacketPointJets
  EulerPacketProfileRecursion EulerGevrey EulerTransverseBoundedFrame
open scoped ContDiff BoundedContinuousFunction

theorem MatrixCoefficient.path_eq_of_raw_eq {T : ℝ}
    {raw raw' : Domain → Space →L[ℝ] Space}
    (G : MatrixCoefficient T raw) (H : MatrixCoefficient T raw')
    (he : ∀ (t : Icc (0 : ℝ) T) x θ, raw (t, (x, θ)) = raw' (t, (x, θ))) :
    G.path = H.path := by
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro x
  exact (G.raw_eq t x 0).symm.trans ((he t x 0).trans (H.raw_eq t x 0))

theorem VectorCoefficient.path_eq_of_raw_eq {T : ℝ} {raw raw' : VectorField}
    (G : VectorCoefficient T raw) (H : VectorCoefficient T raw')
    (he : ∀ (t : Icc (0 : ℝ) T) x θ, raw (t, (x, θ)) = raw' (t, (x, θ))) :
    G.path = H.path := by
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro x
  exact (G.raw_eq t x 0).symm.trans ((he t x 0).trans (H.raw_eq t x 0))

/-- Changing the solver fields of the packet operators does not change the
coefficient budget when the three actual coefficients agree on the interval. -/
def CoefficientBudget.ofRawEq {P T : ℝ} {O O' : Operators}
    {G : CoefficientData P T O} (B : CoefficientBudget G)
    (H : CoefficientData P T O')
    (hi : ∀ (t : Icc (0 : ℝ) T) x θ,
      O.inverseFrame (t, (x, θ)) = O'.inverseFrame (t, (x, θ)))
    (hs : ∀ (t : Icc (0 : ℝ) T) x θ,
      O.strain (t, (x, θ)) = O'.strain (t, (x, θ)))
    (hn : ∀ (t : Icc (0 : ℝ) T) x θ,
      O.normal (t, (x, θ)) = O'.normal (t, (x, θ))) : CoefficientBudget H where
  Rc := B.Rc
  amplitude := B.amplitude
  Rc_nonneg := B.Rc_nonneg
  amplitude_nonneg := B.amplitude_nonneg
  inverse_bound n a := by
    rw [← G.inverse.path_eq_of_raw_eq H.inverse hi]
    exact B.inverse_bound n a
  strain_bound n a := by
    rw [← G.strain.path_eq_of_raw_eq H.strain hs]
    exact B.strain_bound n a
  normal_bound n a := by
    rw [← G.normal.path_eq_of_raw_eq H.normal hn]
    exact B.normal_bound n a

theorem MatrixCoefficient.changeTime_translation_bound {T T' : ℝ}
    {raw : Domain → Space →L[ℝ] Space} (G : MatrixCoefficient T raw)
    (h : T = T') (n : ℕ) (a : Space) (C : ℝ)
    (hb : ‖iteratedFDeriv ℝ n (translateCoefficientPath G.path) a‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (G.changeTime h).path) a‖ ≤ C := by
  subst T'
  exact hb

theorem VectorCoefficient.changeTime_translation_bound {T T' : ℝ}
    {raw : VectorField} (G : VectorCoefficient T raw)
    (h : T = T') (n : ℕ) (a : Space) (C : ℝ)
    (hb : ‖iteratedFDeriv ℝ n (translateCoefficientPath G.path) a‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (G.changeTime h).path) a‖ ≤ C := by
  subst T'
  exact hb

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U)
  (I : EulerTransversePacketProvider.InitialData P D) (hT : M.T = D.T)

/-- Uniform compact-time translation bounds for the literal source coefficients.
Only the original inverse-frame and strain jets are inputs; in particular the
normal has no independent bound and there is no loss in radius or amplitude. -/
def sourceCoefficientBudget (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hI : ∀ n t x,
      ‖iteratedFDeriv ℝ n (D.FInv.field t : Space → Space →L[ℝ] Space) x‖ ≤
        C * majorant Rc 0 n)
    (hM : ∀ n t x,
      ‖iteratedFDeriv ℝ n (D.M.field t : Space → Space →L[ℝ] Space) x‖ ≤
        C * majorant Rc 0 n) : CoefficientBudget (sourceCoefficientData P M D I hT) where
  Rc := Rc
  amplitude := C
  Rc_nonneg := hRc
  amplitude_nonneg := hC
  inverse_bound n a := by
    apply MatrixCoefficient.changeTime_translation_bound
    exact D.FInv.norm_iteratedFDeriv_translation_le n (C*majorant Rc 0 n)
      (mul_nonneg hC (majorant_nonneg Rc hRc 0 n)) (hI n) a
  strain_bound n a := by
    apply MatrixCoefficient.changeTime_translation_bound
    exact D.M.norm_iteratedFDeriv_translation_le n (C*majorant Rc 0 n)
      (mul_nonneg hC (majorant_nonneg Rc hRc 0 n)) (hM n) a
  normal_bound n a := by
    apply VectorCoefficient.changeTime_translation_bound
    exact D.normal.norm_iteratedFDeriv_translation_le n (C*majorant Rc 0 n)
      (mul_nonneg hC (majorant_nonneg Rc hRc 0 n))
      (fun t x => normalCoefficient_derivative_bound D.m₀ D.FInv D.m₀_unit n
        (C*majorant Rc 0 n) (hI n) t x) a

end EulerPacketCylinderField
