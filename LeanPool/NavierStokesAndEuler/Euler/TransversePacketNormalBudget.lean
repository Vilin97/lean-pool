/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketBudget
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCoefficientBounds

@[expose] public section

/-! Source-only coefficient budgets for the joined pressure, potential and corrector. -/

noncomputable section

namespace EulerTransversePacketJoin

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerTransversePacketProvider
  EulerTransversePacketProvider.Data EulerGevrey EulerParameterWordGevrey EulerTimeLpGramGevrey
  EulerTransverseBoundedFrame EulerTransverseForwardCoefficientGevrey EulerSourceCylinderTimeBounds
open scoped ContDiff BoundedContinuousFunction

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- Original inverse-deformation and strain jets, with one fixed inverse radius. -/
structure NormalBudget (D : Data U) (q : ℕ) (R : ℝ) where
  Rc : ℝ
  C : ℝ
  Ri : ℝ
  Rc_nonneg : 0 ≤ Rc
  C_nonneg : 0 ≤ C
  inverse_radius : 2*gramCost D.normalLower C 1*(Rc+1) ≤ Ri
  inverse_bound : ∀ n t x,
    ‖iteratedFDeriv ℝ n (D.FInv.field t : Space → Space →L[ℝ] Space) x‖ ≤ C*majorant Rc 0 n
  strain_bound : ∀ n t x,
    ‖iteratedFDeriv ℝ n (D.M.field t : Space → Space →L[ℝ] Space) x‖ ≤ C*majorant Rc 0 n
  radius : sobolevCoefficientRadius (Fin 4) (correctorCoefficientRadius Rc Ri) ≤ R

namespace NormalBudget

variable {D : Data U} {q : ℕ} {R : ℝ} (N : NormalBudget D q R)

theorem Ri_nonneg : 0 ≤ N.Ri :=
  (inverseRadius_bounds D.normalLower N.C N.Rc N.Ri D.normalLower_pos N.Rc_nonneg
    N.inverse_radius).1

def coefficientRadius : ℝ := correctorCoefficientRadius N.Rc N.Ri
def coefficientAmplitude : ℝ := correctorCoefficientAmplitude N.C N.Ri
def blockAmplitude : ℝ := sobolevCoefficientAmplitude (Fin 4) q N.coefficientRadius
  N.coefficientAmplitude

theorem coefficient_bounds :
    0 ≤ N.coefficientRadius ∧ 0 ≤ N.coefficientAmplitude ∧
    ∀ n a,
      ‖iteratedFDeriv ℝ n (translateCoefficientPath D.FInv.field) a‖ ≤
        N.coefficientAmplitude*majorant N.coefficientRadius 0 n ∧
      ‖iteratedFDeriv ℝ n (translateCoefficientPath D.inverseDerivative) a‖ ≤
        N.coefficientAmplitude*majorant N.coefficientRadius 0 n ∧
      ‖iteratedFDeriv ℝ n (translateCoefficientPath D.potentialCoefficientPath) a‖ ≤
        N.coefficientAmplitude*majorant N.coefficientRadius 0 n ∧
      ‖iteratedFDeriv ℝ n (translateCoefficientPath D.potentialDerivative) a‖ ≤
        N.coefficientAmplitude*majorant N.coefficientRadius 0 n :=
  D.corrector_coefficient_bounds N.Rc N.C N.Ri N.Rc_nonneg N.C_nonneg N.Ri_nonneg
    N.inverse_radius N.inverse_bound N.strain_bound

theorem blockAmplitude_nonneg : 0 ≤ N.blockAmplitude :=
  sobolevCoefficientAmplitude_nonneg q N.coefficientRadius N.coefficientAmplitude
    N.coefficient_bounds.1 N.coefficient_bounds.2.1

theorem normal_bound (n : ℕ) (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖iteratedFDeriv ℝ n (D.normal.field t : Space → Space) x‖ ≤ N.C*majorant N.Rc 0 n :=
  normalCoefficient_derivative_bound D.m₀ D.FInv D.m₀_unit n _ (N.inverse_bound n) t x

theorem pressure_radius : sobolevCoefficientRadius (Fin 4) (4*N.Ri) ≤ R := by
  apply le_trans _ N.radius
  unfold sobolevCoefficientRadius correctorCoefficientRadius
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
  apply mul_le_mul_of_nonneg_left _ (le_trans zero_le_one (le_max_left _ _))
  linarith [N.Rc_nonneg]

end NormalBudget

namespace Budget

variable [CompleteSpace U] {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)} {ι : Type*} [Fintype ι] {q : ℕ}
  (L : Budget D τ hτ hτT B ι q)

theorem velocityCost_nonneg : 0 ≤ L.velocityCost := by
  have hC := sobolevCoefficientAmplitude_nonneg (ι := ι) q L.Rc L.C₀ L.Rc_nonneg L.C₀_nonneg
  have ht := EulerFixedEvolutionSobolev.traceCost_nonneg τ hτ.le
  unfold velocityCost
  positivity

theorem derivativeCost_nonneg : 0 ≤ L.derivativeCost := by
  have hRi := (inverseRadius_bounds (D.tail τ hτ.le hτT).frameLower L.C₀ L.Rc L.Ri
    (D.tail τ hτ.le hτT).frameLower_pos L.Rc_nonneg L.forward_inverse).1
  have h0 := sobolevCoefficientAmplitude_nonneg (ι := ι) q L.Rc L.C₀ L.Rc_nonneg L.C₀_nonneg
  have h1 := sobolevCoefficientAmplitude_nonneg (ι := ι) q L.Rc L.C₁ L.Rc_nonneg L.C₁_nonneg
  have ht := EulerFixedEvolutionSobolev.traceCost_nonneg τ hτ.le
  have hb0 := sobolevCoefficientAmplitude_nonneg (ι := ι) q (4*L.Ri) L.C₀ (by positivity)
    L.C₀_nonneg
  have hb1 := sobolevCoefficientAmplitude_nonneg (ι := ι) q (4*L.Ri) L.C₁ (by positivity)
    L.C₁_nonneg
  have hC₀ := L.C₀_nonneg
  have hC₁ := L.C₁_nonneg
  have hbb := sobolevCoefficientAmplitude_nonneg (ι := ι) q (4*L.Ri) (18*L.Ri*L.C₀*L.C₁)
    (by positivity) (by positivity)
  have hbf := sobolevCoefficientAmplitude_nonneg (ι := ι) q (4*L.Ri) (3*L.Ri*L.C₀)
    (by positivity) (by positivity)
  unfold derivativeCost physicalCost coordinateCost
  positivity

def commonCost : ℝ := L.velocityCost+L.derivativeCost

theorem commonCost_nonneg : 0 ≤ L.commonCost := add_nonneg L.velocityCost_nonneg
  L.derivativeCost_nonneg
theorem velocityCost_le_common : L.velocityCost ≤ L.commonCost := le_add_of_nonneg_right
  L.derivativeCost_nonneg
theorem derivativeCost_le_common : L.derivativeCost ≤ L.commonCost := le_add_of_nonneg_left
  L.velocityCost_nonneg

end Budget
end EulerTransversePacketJoin
