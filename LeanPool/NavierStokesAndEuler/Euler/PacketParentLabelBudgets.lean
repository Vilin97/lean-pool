/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketParentLabelCoefficients
public import LeanPool.NavierStokesAndEuler.Euler.PacketParentNormalBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketParentMeanBudget
public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2CoefficientPath

@[expose] public section

/-! Concrete source budgets from (21), stated in the actual classical
physical-label H⁶ word norms of the displacement, velocity and acceleration.
No multiplier bound or inverse-solver estimate is an input. -/

noncomputable section

namespace EulerPacketParentLabelBounds

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerLpTranslation EulerMeanClassicalWordBounds EulerPacketCofactor EulerPacketPiola
  EulerGevrey
open scoped ContDiff BoundedContinuousFunction

/-- The individual component of the literal three-field bound in (21). -/
def HasLabelBound (K : ℝ) (A : SmoothL2Field Space) : Prop :=
  ∀ n, classicalBlockSize direction 6 A.toLp A.translation_contDiff n ≤
    K^(n+1)*(n.factorial : ℝ)^2

variable {J : Type*} [TopologicalSpace J] [CompactSpace J]

theorem coefficient_gradient_bound (F : SmoothCoefficientPath J EndSpace)
    (A : J → SmoothL2Field Space) (L : Space →L[ℝ] Space) (hL : ‖L‖ ≤ 1)
    (heq : ∀ t x, F.field t x = fderiv ℝ (A t).field (L x))
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ t, HasLabelBound K (A t))
    (n : ℕ) (t : J) (x : Space) :
    ‖iteratedFDeriv ℝ n (F.field t : Space → EndSpace) x‖ ≤
      gradientAmplitude K*majorant (coefficientRadius K) 0 n := by
  have he : (F.field t : Space → EndSpace) = fun y => fderiv ℝ (A t).field (L y) := funext (heq t)
  rw [he]
  exact source_gradient_bound (A t).toLp (A t).translation_contDiff (A t).field (A t).smooth
    (A t).toLp_ae K hK (hb t) L hL n x

theorem coefficient_deformation_bound (F : SmoothCoefficientPath J EndSpace)
    (A : J → SmoothL2Field Space) (L : Space →L[ℝ] Space) (hL : ‖L‖ ≤ 1)
    (heq : ∀ t x, F.field t x = ContinuousLinearMap.id ℝ Space+fderiv ℝ (A t).field (L x))
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ t, HasLabelBound K (A t))
    (n : ℕ) (t : J) (x : Space) :
    ‖iteratedFDeriv ℝ n (F.field t : Space → EndSpace) x‖ ≤
      frameAmplitude K*majorant (coefficientRadius K) 0 n := by
  have he : (F.field t : Space → EndSpace) =
      fun y => ContinuousLinearMap.id ℝ Space+fderiv ℝ (A t).field (L y) := funext (heq t)
  rw [he]
  exact source_deformation_bound (A t).toLp (A t).translation_contDiff (A t).field (A t).smooth
    (A t).toLp_ae K hK (hb t) L hL n x

end EulerPacketParentLabelBounds

namespace EulerPacketParentLabelBudgets

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerLpTranslation
  EulerPacketCofactor EulerPacketPiola EulerPacketParentLabelBounds
open scoped ContDiff BoundedContinuousFunction

/-- The full normal/pressure/corrector multiplier budget follows from the
actual parent displacement and velocity in physical initial labels. -/
def normalBudget {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (D : EulerTransversePacketProvider.Data U) (q : ℕ)
    (A V : Icc (0 : ℝ) D.T → SmoothL2Field Space)
    (ℓ K : ℝ) (hℓ : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1) (hK : 0 ≤ K)
    (hA : ∀ t, HasLabelBound K (A t)) (hV : ∀ t, HasLabelBound K (V t))
    (hF : ∀ t x, D.F.field t x = ContinuousLinearMap.id ℝ Space+fderiv ℝ (A t).field (ℓ • x))
    (hF₁ : ∀ t x, D.F₁.field t x = fderiv ℝ (V t).field (ℓ • x))
    (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1) :
    EulerTransversePacketJoin.NormalBudget D q
      (EulerPacketParentNormalBudget.radius (coefficientRadius K) (frameAmplitude K)
        (gradientAmplitude K)) :=
  EulerPacketParentNormalBudget.sourceNormalBudget D (coefficientRadius K) (frameAmplitude K)
    (gradientAmplitude K)
    (coefficientRadius_nonneg K) (frameAmplitude_nonneg K) (gradientAmplitude_nonneg K) hdet
    (coefficient_deformation_bound D.F A (ℓ • ContinuousLinearMap.id ℝ Space)
      (labelScaling_norm_le ℓ hℓ hℓ1) hF K hK hA)
    (coefficient_gradient_bound D.F₁ V (ℓ • ContinuousLinearMap.id ℝ Space)
      (labelScaling_norm_le ℓ hℓ hℓ1) hF₁ K hK hV) q

/-- The actual mean variational inverse budget is constructed from the
three literal parent fields in (21), det F=1, and the inverse time length. -/
def meanBudget (D : EulerMeanPacketProvider.Data) (q : ℕ)
    (A V W : Icc (0 : ℝ) D.T → SmoothL2Field Space)
    (Ti K : ℝ) (hT : D.T ≤ 1) (hTi : D.T⁻¹ ≤ Ti) (hK : 0 ≤ K)
    (hA : ∀ t, HasLabelBound K (A t)) (hV : ∀ t, HasLabelBound K (V t))
    (hW : ∀ t, HasLabelBound K (W t))
    (hF : ∀ t x, D.F.field t x = ContinuousLinearMap.id ℝ Space+fderiv ℝ (A t).field (D.ℓ • x))
    (hF₁ : ∀ t x, D.F₁.field t x = fderiv ℝ (V t).field (D.ℓ • x))
    (hF₂ : ∀ t x, D.F₂.field t x = fderiv ℝ (W t).field (D.ℓ • x))
    (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1) :
    EulerMeanPacketProvider.Budget D q
      (EulerPacketParentMeanBudget.radius q D.T Ti (coefficientRadius K)
        (frameAmplitude K) (gradientAmplitude K) (gradientAmplitude K) D.L) :=
  EulerPacketParentMeanBudget.sourceMeanBudget D q Ti (coefficientRadius K)
    (frameAmplitude K) (gradientAmplitude K) (gradientAmplitude K)
    hT hTi (coefficientRadius_lower K) (frameAmplitude_nonneg K) (gradientAmplitude_nonneg K)
    (gradientAmplitude_nonneg K) hdet
    (coefficient_deformation_bound D.F A (D.ℓ • ContinuousLinearMap.id ℝ Space)
      (labelScaling_norm_le D.ℓ D.ℓ_pos.le D.ℓ_le_one) hF K hK hA)
    (coefficient_gradient_bound D.F₁ V (D.ℓ • ContinuousLinearMap.id ℝ Space)
      (labelScaling_norm_le D.ℓ D.ℓ_pos.le D.ℓ_le_one) hF₁ K hK hV)
    (coefficient_gradient_bound D.F₂ W (D.ℓ • ContinuousLinearMap.id ℝ Space)
      (labelScaling_norm_le D.ℓ D.ℓ_pos.le D.ℓ_le_one) hF₂ K hK hW)

end EulerPacketParentLabelBudgets
