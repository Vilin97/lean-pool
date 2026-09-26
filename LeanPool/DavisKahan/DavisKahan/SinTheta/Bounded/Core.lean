/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.SinTheta.SpectralBridge
public import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.CanonicalRealView
public import LeanPool.DavisKahan.DavisKahan.SinTheta.FrameFactorization

/-!
# Bounded `sin Θ` problem data and angle identification

These are the parts of the bounded `sin Θ` development that consume no Sylvester
estimate: the residual and its adjoint block identity, the complementary
Sylvester equation, the exact orthogonal decomposition, and the directed sine
operator with its isometry and ideal-transport lemmas.

Keeping them apart from the endpoint theorems makes this file independent of
which engine supplies the Sylvester estimate.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

section Generic

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Residual of the trial map and trial block. -/
def generalResidual
    (A : E →L[𝕜] E) (X : F →L[𝕜] E)
    (A₀ : F →L[𝕜] F) : F →L[𝕜] E :=
  A ∘L X - X ∘L A₀

omit [CompleteSpace G] in
/-- Adjoint residual block identity used by the generalized theorem. -/
theorem adjoint_residual_block_identity
    {A : E →L[𝕜] E} {A₀ : F →L[𝕜] F}
    {Λ₁ : G →L[𝕜] G} {X : F →L[𝕜] E}
    {F₁ : G →L[𝕜] E}
    (hA : A.IsSymmetric) (hA₀ : A₀.IsSymmetric)
    (_hΛ₁ : Λ₁.IsSymmetric)
    (hIntertwine : A ∘L F₁ = F₁ ∘L Λ₁) :
    (generalResidual A X A₀).adjoint ∘L F₁ =
      (X.adjoint ∘L F₁) ∘L Λ₁ -
        A₀ ∘L (X.adjoint ∘L F₁) := by
  ext y
  refine ext_inner_right 𝕜 fun x => ?_
  have hInt : A (F₁ y) = F₁ (Λ₁ y) := by
    have h := congrArg (fun T : G →L[𝕜] E => T y) hIntertwine
    simpa only [ContinuousLinearMap.comp_apply] using h
  calc
    ⟪((generalResidual A X A₀).adjoint ∘L F₁) y, x⟫_𝕜
        = ⟪F₁ y, generalResidual A X A₀ x⟫_𝕜 := by
            rw [ContinuousLinearMap.comp_apply,
              (generalResidual A X A₀).adjoint_inner_left x (F₁ y)]
    _ = ⟪F₁ y, A (X x)⟫_𝕜 - ⟪F₁ y, X (A₀ x)⟫_𝕜 := by
          simp only [generalResidual, ContinuousLinearMap.comp_apply, sub_apply,
            inner_sub_right]
    _ = ⟪A (F₁ y), X x⟫_𝕜 - ⟪F₁ y, X (A₀ x)⟫_𝕜 := by
          exact congrArg
            (fun z : 𝕜 => z - ⟪F₁ y, X (A₀ x)⟫_𝕜)
            (hA (F₁ y) (X x)).symm
    _ = ⟪F₁ (Λ₁ y), X x⟫_𝕜 - ⟪F₁ y, X (A₀ x)⟫_𝕜 := by
          rw [hInt]
    _ = ⟪X.adjoint (F₁ (Λ₁ y)), x⟫_𝕜 -
          ⟪X.adjoint (F₁ y), A₀ x⟫_𝕜 := by
          rw [← X.adjoint_inner_left x (F₁ (Λ₁ y)),
            ← X.adjoint_inner_left (A₀ x) (F₁ y)]
    _ = ⟪X.adjoint (F₁ (Λ₁ y)), x⟫_𝕜 -
          ⟪A₀ (X.adjoint (F₁ y)), x⟫_𝕜 := by
          exact congrArg
            (fun z : 𝕜 => ⟪X.adjoint (F₁ (Λ₁ y)), x⟫_𝕜 - z)
            (hA₀ (X.adjoint (F₁ y)) x).symm
    _ = ⟪(((X.adjoint ∘L F₁) ∘L Λ₁ -
          A₀ ∘L (X.adjoint ∘L F₁)) y), x⟫_𝕜 := by
          simp only [ContinuousLinearMap.comp_apply, sub_apply, inner_sub_left]

omit [CompleteSpace G] in
/-- The same residual identity in the orientation consumed by the
Sylvester estimate. -/
theorem complementary_sylvester_equation
    {A : E →L[𝕜] E} {A₀ : F →L[𝕜] F}
    {Λ₁ : G →L[𝕜] G} {X : F →L[𝕜] E}
    {F₁ : G →L[𝕜] E}
    (hA : A.IsSymmetric) (hA₀ : A₀.IsSymmetric)
    (hΛ₁ : Λ₁.IsSymmetric)
    (hIntertwine : A ∘L F₁ = F₁ ∘L Λ₁) :
    A₀ ∘L (X.adjoint ∘L F₁) -
      (X.adjoint ∘L F₁) ∘L Λ₁ =
        -((generalResidual A X A₀).adjoint ∘L F₁) := by
  rw [adjoint_residual_block_identity hA hA₀ hΛ₁ hIntertwine]
  abel

/-- The desired exact space and its unwanted complement form an orthogonal
coordinate decomposition of the entire ambient Hilbert space. -/
structure OrthogonalExactDecomposition
    (F₀ : H →L[𝕜] E) (F₁ : G →L[𝕜] E) : Prop where
  isometry₀ : IsometricEmbedding F₀
  isometry₁ : IsometricEmbedding F₁
  orthogonal : F₀.adjoint ∘L F₁ = 0
  projection_sum :
    F₀ ∘L F₀.adjoint + F₁ ∘L F₁.adjoint =
      ContinuousLinearMap.id 𝕜 E

end Generic

section Complex

universe v

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Directed sine operator from the orthonormalized trial coordinates into the
orthogonal complement of the desired exact space. -/
noncomputable def directedSinThetaOperator
    (X : F →L[ℂ] E) (F₀ : H →L[ℂ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) : F →L[ℂ] E :=
  (ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L
    frameIsometry X hX hε

/-- The directed sine operator of an isometric trial map is the direct
orthogonal-complement block of that map. -/
theorem directedSinThetaOperator_eq_of_isometry
    (X : F →L[ℂ] E) (F₀ : H →L[ℂ] E)
    (hX : IsometricEmbedding X) :
    directedSinThetaOperator X F₀
        (lowerFrameBound_one_of_isometry hX) zero_lt_one =
      (ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L X := by
  unfold directedSinThetaOperator
  exact congrArg
    (fun U : F →L[ℂ] E =>
      (ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L U)
    (frameIsometry_eq_of_isometry X hX)

/-- Under a complete orthogonal exact decomposition, the complementary overlap
block and the directed sine operator have the same ideal membership and gauge. -/
theorem sinThetaBlock_mem_and_gauge_eq_directedSinThetaOperator
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, v} ℂ)
    
    (X : F →L[ℂ] E) (F₀ : H →L[ℂ] E) (F₁ : G →L[ℂ] E)
    {ε : ℝ} (hX : LowerFrameBound X ε) (hε : 0 < ε)
    (hdecomp : OrthogonalExactDecomposition F₀ F₁)
    (hblock : N.Mem (sinThetaBlock X F₁ hX hε)) :
    N.Mem (directedSinThetaOperator X F₀ hX hε) ∧
      N.gaugeReal (directedSinThetaOperator X F₀ hX hε) =
        N.gaugeReal (sinThetaBlock X F₁ hX hε) := by
  have hComplement :
      ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint =
        F₁ ∘L F₁.adjoint := by
    rw [← hdecomp.projection_sum]
    abel
  have hDirected :
      directedSinThetaOperator X F₀ hX hε =
        F₁ ∘L (sinThetaBlock X F₁ hX hε).adjoint := by
    unfold directedSinThetaOperator sinThetaBlock
    rw [hComplement, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
    exact ContinuousLinearMap.comp_assoc _ _ _
  have hblockAdj : N.Mem (sinThetaBlock X F₁ hX hε).adjoint :=
    N.adjoint_mem hblock
  have hDirectedMem :
      N.Mem (directedSinThetaOperator X F₀ hX hε) := by
    rw [hDirected]
    exact N.comp_left_mem F₁ hblockAdj
  have hF₁Norm : ‖F₁‖ ≤ 1 :=
    opNorm_le_one_of_isometry hdecomp.isometry₁
  have hForward :
      N.gaugeReal (directedSinThetaOperator X F₀ hX hε) ≤
        N.gaugeReal (sinThetaBlock X F₁ hX hε) := by
    rw [hDirected]
    calc
      N.gaugeReal (F₁ ∘L (sinThetaBlock X F₁ hX hε).adjoint)
          ≤ N.gaugeReal (sinThetaBlock X F₁ hX hε).adjoint :=
        N.gaugeReal_comp_left_le F₁ hblockAdj hF₁Norm
      _ = N.gaugeReal (sinThetaBlock X F₁ hX hε) :=
        N.gaugeReal_adjoint hblock
  have hF₁LeftInverse :
      F₁.adjoint ∘L F₁ = ContinuousLinearMap.id ℂ G :=
    adjoint_comp_self_eq_id_of_isometry hdecomp.isometry₁
  have hRecover :
      (sinThetaBlock X F₁ hX hε).adjoint =
        F₁.adjoint ∘L directedSinThetaOperator X F₀ hX hε := by
    calc
      (sinThetaBlock X F₁ hX hε).adjoint =
          ContinuousLinearMap.id ℂ G ∘L
            (sinThetaBlock X F₁ hX hε).adjoint := by simp
      _ = (F₁.adjoint ∘L F₁) ∘L
            (sinThetaBlock X F₁ hX hε).adjoint := by
          rw [hF₁LeftInverse]
      _ = F₁.adjoint ∘L
            (F₁ ∘L (sinThetaBlock X F₁ hX hε).adjoint) :=
          ContinuousLinearMap.comp_assoc _ _ _
      _ = F₁.adjoint ∘L directedSinThetaOperator X F₀ hX hε := by
          rw [hDirected]
  have hF₁AdjNorm : ‖F₁.adjoint‖ ≤ 1 := by
    simpa using hF₁Norm
  have hReverse :
      N.gaugeReal (sinThetaBlock X F₁ hX hε) ≤
        N.gaugeReal (directedSinThetaOperator X F₀ hX hε) := by
    rw [← N.gaugeReal_adjoint hblock, hRecover]
    exact N.gaugeReal_comp_left_le F₁.adjoint hDirectedMem hF₁AdjNorm
  exact ⟨hDirectedMem, le_antisymm hForward hReverse⟩

end Complex

section GenericExact

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- In the isometric case, the raw complementary overlap block and the
orthogonal-complement projection of the trial map have the same ideal gauge. -/
theorem isometricComplementaryBlock_mem_and_gauge_eq_directed
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    
    (X : F →L[𝕜] E) (F₀ : H →L[𝕜] E) (F₁ : G →L[𝕜] E)
    (_hX : IsometricEmbedding X)
    (hdecomp : OrthogonalExactDecomposition F₀ F₁)
    (hblock : N.Mem (X.adjoint ∘L F₁)) :
    N.Mem ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L X) ∧
      N.gaugeReal ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L X) =
        N.gaugeReal (X.adjoint ∘L F₁) := by
  have hComplement :
      ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint =
        F₁ ∘L F₁.adjoint := by
    rw [← hdecomp.projection_sum]
    abel
  let D : F →L[𝕜] E :=
    (ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L X
  have hDirected : D = F₁ ∘L (X.adjoint ∘L F₁).adjoint := by
    dsimp [D]
    rw [hComplement, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
    exact ContinuousLinearMap.comp_assoc _ _ _
  have hblockAdj : N.Mem (X.adjoint ∘L F₁).adjoint :=
    N.adjoint_mem hblock
  have hDirectedMem : N.Mem D := by
    rw [hDirected]
    exact N.comp_left_mem F₁ hblockAdj
  have hF₁Norm : ‖F₁‖ ≤ 1 :=
    opNorm_le_one_of_isometry hdecomp.isometry₁
  have hForward : N.gaugeReal D ≤ N.gaugeReal (X.adjoint ∘L F₁) := by
    rw [hDirected]
    calc
      N.gaugeReal (F₁ ∘L (X.adjoint ∘L F₁).adjoint)
          ≤ N.gaugeReal (X.adjoint ∘L F₁).adjoint :=
        N.gaugeReal_comp_left_le F₁ hblockAdj hF₁Norm
      _ = N.gaugeReal (X.adjoint ∘L F₁) := N.gaugeReal_adjoint hblock
  have hF₁LeftInverse :
      F₁.adjoint ∘L F₁ = ContinuousLinearMap.id 𝕜 G :=
    adjoint_comp_self_eq_id_of_isometry hdecomp.isometry₁
  have hRecover :
      (X.adjoint ∘L F₁).adjoint = F₁.adjoint ∘L D := by
    calc
      (X.adjoint ∘L F₁).adjoint =
          ContinuousLinearMap.id 𝕜 G ∘L (X.adjoint ∘L F₁).adjoint := by simp
      _ = (F₁.adjoint ∘L F₁) ∘L (X.adjoint ∘L F₁).adjoint := by
          rw [hF₁LeftInverse]
      _ = F₁.adjoint ∘L (F₁ ∘L (X.adjoint ∘L F₁).adjoint) :=
          ContinuousLinearMap.comp_assoc _ _ _
      _ = F₁.adjoint ∘L D := by rw [hDirected]
  have hF₁AdjNorm : ‖F₁.adjoint‖ ≤ 1 := by simpa using hF₁Norm
  have hReverse : N.gaugeReal (X.adjoint ∘L F₁) ≤ N.gaugeReal D := by
    rw [← N.gaugeReal_adjoint hblock, hRecover]
    exact N.gaugeReal_comp_left_le F₁.adjoint hDirectedMem hF₁AdjNorm
  exact ⟨hDirectedMem, le_antisymm hForward hReverse⟩

end GenericExact

end ExactSinTheta
end DavisKahan
end TauCeti
