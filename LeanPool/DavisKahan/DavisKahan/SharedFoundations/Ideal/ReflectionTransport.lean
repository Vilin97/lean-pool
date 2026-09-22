/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SharedFoundations.Ideal.TwoWayFactorization
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.CanonicalRealView
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.DoubleAngle

/-!
# Ideal transport through subspace reflections

The full absolute projector difference and a one-sided angle block have
different singular-value multiplicities in general.  The stable ideal object
for the directed theorem is the one-sided block.  Reflection converts the
block for the mirror subspace exactly into the one-sided double-angle block
(`directedSinBlock_reflected_eq_reflection_comp_sinTwo`), and a reflection is a
self-inverse contraction, so it changes neither ideal membership nor the gauge.

The companion file `TwoWayFactorization` proves the general two-way contraction
principle these use; this one supplies the reflection instance of it and the
double-angle consequence.
-/

namespace TauCeti
namespace DavisKahan
namespace SharedFoundations
namespace Ideal

open scoped InnerProductSpace
open ExactSinTheta
open DavisKahanExt
open TauCeti.DavisKahan

universe u

-- `𝕜` must live in the same universe `u` as `E`; see the note in
-- `TwoWayFactorization` on why a family closed under adjoints cannot keep the
-- two space universes independent.
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Directed sine block from `U` toward `W`. -/
noncomputable def directedSinBlock
    (U W : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [W.HasOrthogonalProjection] : E →L[𝕜] E :=
  Wᗮ.starProjection ∘L U.starProjection

omit [CompleteSpace E] in
/-- Left reflection is an involutive contraction factorization. -/
theorem reflection_left_twoWay
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] E) :
    V.reflectionOperator ∘L (V.reflectionOperator ∘L T) = T := by
  rw [← ContinuousLinearMap.comp_assoc, Submodule.reflectionOperator_involutive,
    ContinuousLinearMap.id_comp]

omit [CompleteSpace E] in
/-- Right reflection is an involutive contraction factorization. -/
theorem reflection_right_twoWay
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] E) :
    (T ∘L V.reflectionOperator) ∘L V.reflectionOperator = T := by
  rw [ContinuousLinearMap.comp_assoc, Submodule.reflectionOperator_involutive,
    ContinuousLinearMap.comp_id]

/-- Ideal membership is invariant under left reflection. -/
theorem SymmetricOperatorIdealFamily.mem_reflection_comp_iff
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, u} 𝕜)

    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] E) :
    N.Mem (V.reflectionOperator ∘L T) ↔ N.Mem T := by
  constructor
  · intro h
    rw [← reflection_left_twoWay V T]
    exact N.comp_left_mem (V.reflectionOperator) h
  · intro h
    exact N.comp_left_mem (V.reflectionOperator) h

/-- The ideal gauge is invariant under left reflection. -/
theorem SymmetricOperatorIdealFamily.gauge_reflection_comp
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, u} 𝕜)

    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    {T : E →L[𝕜] E} (hT : N.Mem T) :
    N.gaugeReal (V.reflectionOperator ∘L T) = N.gaugeReal T := by
  have hRT : N.Mem (V.reflectionOperator ∘L T) :=
    N.comp_left_mem (V.reflectionOperator) hT
  apply le_antisymm
  · exact N.gaugeReal_comp_left_le (V.reflectionOperator) hT
      (Submodule.norm_reflectionOperator_le_one V)
  · calc
      N.gaugeReal T =
          N.gaugeReal (V.reflectionOperator ∘L (V.reflectionOperator ∘L T)) :=
        congrArg (fun S : E →L[𝕜] E => N.gaugeReal S)
          (reflection_left_twoWay V T).symm
      _ ≤ N.gaugeReal (V.reflectionOperator ∘L T) :=
        N.gaugeReal_comp_left_le (V.reflectionOperator) hRT
          (Submodule.norm_reflectionOperator_le_one V)

/-- Ideal membership is invariant under right reflection. -/
theorem SymmetricOperatorIdealFamily.mem_comp_reflection_iff
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, u} 𝕜)

    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] E) :
    N.Mem (T ∘L V.reflectionOperator) ↔ N.Mem T := by
  constructor
  · intro h
    rw [← reflection_right_twoWay V T]
    exact N.comp_right_mem (V.reflectionOperator) h
  · intro h
    exact N.comp_right_mem (V.reflectionOperator) h

/-- The ideal gauge is invariant under right reflection. -/
theorem SymmetricOperatorIdealFamily.gauge_comp_reflection
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, u} 𝕜)

    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    {T : E →L[𝕜] E} (hT : N.Mem T) :
    N.gaugeReal (T ∘L V.reflectionOperator) = N.gaugeReal T := by
  have hTR : N.Mem (T ∘L V.reflectionOperator) :=
    N.comp_right_mem (V.reflectionOperator) hT
  apply le_antisymm
  · exact N.gaugeReal_comp_right_le (V.reflectionOperator) hT
      (Submodule.norm_reflectionOperator_le_one V)
  · calc
      N.gaugeReal T =
          N.gaugeReal ((T ∘L V.reflectionOperator) ∘L V.reflectionOperator) :=
        congrArg (fun S : E →L[𝕜] E => N.gaugeReal S)
          (reflection_right_twoWay V T).symm
      _ ≤ N.gaugeReal (T ∘L V.reflectionOperator) :=
        N.gaugeReal_comp_right_le (V.reflectionOperator) hTR
          (Submodule.norm_reflectionOperator_le_one V)

/-- Exact operator identity behind the directed ideal double-angle theorem. -/
theorem directedSinBlock_reflected_eq_reflection_comp_sinTwo
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    directedSinBlock U (reflectedSubspace V U) =
      V.reflectionOperator ∘L sinTwoAngleOperator U V := by
  unfold directedSinBlock
  rw [starProjection_orthogonal_reflectedSubspace]
  have hassoc :
      (V.reflectionOperator ∘L Uᗮ.starProjection ∘L V.reflectionOperator) ∘L
          U.starProjection =
        V.reflectionOperator ∘L
          (Uᗮ.starProjection ∘L V.reflectionOperator ∘L U.starProjection) := by
    ext x
    rfl
  rw [hassoc, complementary_comp_reflection_comp_projection]

/-- The directed mirror-angle block and the double-angle block have equivalent
membership and equal ideal gauge. -/
theorem SymmetricOperatorIdealFamily.directed_reflected_mem_iff_and_gauge_eq
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, u} 𝕜)

    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (N.Mem (directedSinBlock U (reflectedSubspace V U)) ↔
      N.Mem (sinTwoAngleOperator U V)) ∧
    (N.Mem (sinTwoAngleOperator U V) →
      N.gaugeReal (directedSinBlock U (reflectedSubspace V U)) =
        N.gaugeReal (sinTwoAngleOperator U V)) := by
  rw [directedSinBlock_reflected_eq_reflection_comp_sinTwo]
  constructor
  · exact SymmetricOperatorIdealFamily.mem_reflection_comp_iff N V
      (sinTwoAngleOperator U V)
  · intro h
    exact SymmetricOperatorIdealFamily.gauge_reflection_comp N V h

/-- Square-ideal version of the directed mirror-angle transport. -/
theorem DavisKahanExt.SymmetricNormIdeal.directed_reflected_mem_and_gauge_eq
    (I : DavisKahanExt.SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hT : I.mem (sinTwoAngleOperator U V)) :
    I.mem (directedSinBlock U (reflectedSubspace V U)) ∧
      I.gauge (directedSinBlock U (reflectedSubspace V U)) =
        I.gauge (sinTwoAngleOperator U V) := by
  let J : E →L[𝕜] E := ContinuousLinearMap.id 𝕜 E
  let R : E →L[𝕜] E := V.reflectionOperator
  have hforward : directedSinBlock U (reflectedSubspace V U) =
      R ∘L sinTwoAngleOperator U V ∘L J := by
    rw [ContinuousLinearMap.comp_id]
    exact directedSinBlock_reflected_eq_reflection_comp_sinTwo U V
  have hback : sinTwoAngleOperator U V =
      R ∘L directedSinBlock U (reflectedSubspace V U) ∘L J := by
    rw [ContinuousLinearMap.comp_id,
      directedSinBlock_reflected_eq_reflection_comp_sinTwo,
      ← ContinuousLinearMap.comp_assoc, Submodule.reflectionOperator_involutive,
      ContinuousLinearMap.id_comp]
  have hR : ‖R‖ ≤ 1 := Submodule.norm_reflectionOperator_le_one V
  have hJ : ‖J‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  exact SymmetricNormIdeal.mem_iff_and_gauge_eq_of_twoWayContractions I
    hback hforward hR hJ hR hJ hT

end Ideal
end SharedFoundations
end DavisKahan
end TauCeti
