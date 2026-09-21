/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section3AcuteDirectRotation
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section3Proposition32
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section3PrincipalSquareRoot
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section3Proposition34
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section3Proposition34Real
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section3Corollary31
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section3Proposition35
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section4
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section4Real

/-!
# Section 3 and Proposition 4.2 at the paper's separable ambient scope

Davis and Kahan work on a **separable** Hilbert space: "Let `H` be a separable
Hilbert space, real or complex; finite dimensionality is not assumed."  Under
this repository's rule (`ambient_scope_policy.separability`) a source-exact
façade carries that assumption, and the stronger arbitrary-Hilbert theorem is
retained and registered as the generalization it is.

Every declaration here is that wrapper and nothing else: same statement, one
extra ambient hypothesis, and the general theorem as the proof.  The general
theorems remain the mathematics; these are the source boundary.

Rows that stay `generalized`, with their reasons, are recorded in the policy
table rather than wrapped here.
-/

open TauCeti.DavisKahan.Sylvester
open TauCeti.DavisKahan.Angle

namespace TauCeti
namespace DavisKahan1970

open scoped InnerProductSpace ComplexOrder
open DavisKahan
open TauCeti.DavisKahan
open TauCeti.DavisKahanExt

noncomputable section

universe u v

/-! ### Proposition 3.1 -/

section Prop31

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal

variable (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- **Davis--Kahan 1970, Proposition 3.1, at the paper's separable ambient
scope.** -/
theorem proposition3_1_separable [TopologicalSpace.SeparableSpace H]
    (hacute : TauCeti.IsAcute U V) :
    acute_directRotation U V ∈ unitary (H →L[𝕜] H) ∧
      acute_directRotation U V * U.starProjection =
        V.starProjection * acute_directRotation U V ∧
      (U.starProjection * acute_directRotation U V * U.starProjection).IsPositive ∧
      (Uᗮ.starProjection * acute_directRotation U V * Uᗮ.starProjection).IsPositive ∧
      Uᗮ.starProjection * acute_directRotation U V * U.starProjection =
        -star (U.starProjection * acute_directRotation U V * Uᗮ.starProjection) ∧
      ∀ W : H →L[𝕜] H,
        W ∈ unitary (H →L[𝕜] H) →
        W * U.starProjection = V.starProjection * W →
        (U.starProjection * W * U.starProjection).IsPositive →
        (Uᗮ.starProjection * W * Uᗮ.starProjection).IsPositive →
        W = acute_directRotation U V :=
  proposition3_1 U V hacute

end Prop31

/-! ### Proposition 3.2 -/

section Prop32

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal

/-- **Davis--Kahan 1970, Proposition 3.2, existence half, at the paper's
separable ambient scope.** -/
theorem proposition3_2_exists_iff_crossedDefectsEquivalent_separable
    [TopologicalSpace.SeparableSpace H] :
    (∃ T : H →L[𝕜] H, IsDirectRotation U V T) ↔ CrossedDefectsEquivalent U V :=
  proposition3_2_exists_iff_crossedDefectsEquivalent U V

/-- **Davis--Kahan 1970, Proposition 3.2, non-uniqueness half, at the paper's
separable ambient scope.** -/
theorem proposition3_2_not_unique_separable [TopologicalSpace.SeparableSpace H]
    (hdefect : CrossedDefectsEquivalent U V) (hnonacute : ¬ TauCeti.IsAcute U V) :
    ∃ T₁ T₂ : H →L[𝕜] H,
      IsDirectRotation U V T₁ ∧ IsDirectRotation U V T₂ ∧ T₁ ≠ T₂ :=
  proposition3_2_not_unique U V hdefect hnonacute

end Prop32

/-! ### Proposition 3.5 and Corollary 3.2 -/

section Prop35

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal

/-- **Davis--Kahan 1970, Proposition 3.5, commutations, at the paper's separable
ambient scope.** -/
theorem proposition3_5_commutations_separable [TopologicalSpace.SeparableSpace H]
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    Commute (proposition3_5_angleOperator U V) (U.starProjection) ∧
      Commute (proposition3_5_angleOperator U V) (V.starProjection) ∧
      Commute (proposition3_5_angleOperator U V) (corollary3_2_nonacuteQuarterTurn U V J) ∧
      Commute (proposition3_5_angleOperator U V) (nonacuteDirectRotation U V J) :=
  proposition3_5_commutations U V J

/-- **Davis--Kahan 1970, Proposition 3.5, eigenvector angle, at the paper's
separable ambient scope.** -/
theorem proposition3_5_eigenvector_angle_separable [TopologicalSpace.SeparableSpace H]
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V)
    {x : H} (hx0 : x ≠ 0) {θ : ℝ}
    (hx : proposition3_5_angleOperator U V x = ((θ : ℝ) : 𝕜) • x) :
    TauCeti.vectorAngle 𝕜 x (nonacuteDirectRotation U V J x) = θ :=
  proposition3_5_eigenvector_angle U V J hx0 hx

/-- **Davis--Kahan 1970, Proposition 3.5, maximal fixed-cosine subspace, at the
paper's separable ambient scope.** -/
theorem proposition3_5_angleEigenspace_uniqueMaximal_separable [TopologicalSpace.SeparableSpace H]
    (hacute : TauCeti.IsAcute U V) {θ : ℝ}
    (hθ : Module.End.HasEigenvalue (proposition3_5_angleOperator U V).toLinearMap
      ((θ : ℝ) : 𝕜)) :
    IsPrintedFixedCosineReducingSubspace U V
        (proposition3_5_angleEigenspace U V θ) (Real.cos θ) ∧
      ∀ M : Submodule 𝕜 H,
        IsPrintedFixedCosineReducingSubspace U V M (Real.cos θ) →
          M ≤ proposition3_5_angleEigenspace U V θ :=
  proposition3_5_angleEigenspace_uniqueMaximal U V hacute hθ

/-- **Davis--Kahan 1970, Corollary 3.2, at the paper's separable ambient
scope.** -/
theorem corollary3_2_separable [TopologicalSpace.SeparableSpace H]
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    proposition3_5_angleOperator V U = proposition3_5_angleOperator U V ∧
      corollary3_2_nonacuteQuarterTurn V U (swapCrossedDefectEquiv U V J) =
        -corollary3_2_nonacuteQuarterTurn U V J ∧
      nonacuteDirectRotation V U (swapCrossedDefectEquiv U V J) =
        star (nonacuteDirectRotation U V J) :=
  corollary3_2 U V J

end Prop35

/-! ### Proposition 3.3 -/

section Prop33Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- **Davis--Kahan 1970, Proposition 3.3 over `ℂ`, forward half, at the paper's
separable ambient scope.** -/
theorem proposition3_3_complex_forward_separable [TopologicalSpace.SeparableSpace H]
    (T : H →L[ℂ] H)
    (hunitary : T ∈ unitary (H →L[ℂ] H))
    (hintertwines : T * U.starProjection = V.starProjection * T)
    (hsource_pos : (U.starProjection * T * U.starProjection).IsPositive)
    (hcomplement_pos : (Uᗮ.starProjection * T * Uᗮ.starProjection).IsPositive)
    (hcrossed : Uᗮ.starProjection * T * U.starProjection =
      -star (U.starProjection * T * Uᗮ.starProjection)) :
    IsPrincipalUnitarySquareRoot (spectraReflectionProduct U V) T :=
  proposition3_3_complex_forward U V T hunitary hintertwines hsource_pos
    hcomplement_pos hcrossed

/-- **Davis--Kahan 1970, Proposition 3.3 over `ℂ`, converse half, at the paper's
separable ambient scope.** -/
theorem proposition3_3_complex_converse_separable [TopologicalSpace.SeparableSpace H]
    (T : H →L[ℂ] H)
    (hroot : IsPrincipalUnitarySquareRoot (spectraReflectionProduct U V) T)
    (hcross : T '' (halmosSourceDefect U V : Set H) =
      (halmosTargetDefect U V : Set H)) :
    T ∈ unitary (H →L[ℂ] H) ∧
      T * U.starProjection = V.starProjection * T ∧
      (U.starProjection * T * U.starProjection).IsPositive ∧
      (Uᗮ.starProjection * T * Uᗮ.starProjection).IsPositive ∧
      Uᗮ.starProjection * T * U.starProjection =
        -star (U.starProjection * T * Uᗮ.starProjection) :=
  proposition3_3_complex_converse U V T hroot hcross

end Prop33Complex

section Prop33Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (U V : Submodule ℝ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- **Davis--Kahan 1970, Proposition 3.3 over `ℝ`, forward half, at the paper's
separable ambient scope.** -/
theorem proposition3_3_real_forward_separable [TopologicalSpace.SeparableSpace E]
    (T : E →L[ℝ] E)
    (hunitary : T ∈ unitary (E →L[ℝ] E))
    (hintertwines : T * U.starProjection = V.starProjection * T)
    (hsource_pos : (U.starProjection * T * U.starProjection).IsPositive)
    (hcomplement_pos : (Uᗮ.starProjection * T * Uᗮ.starProjection).IsPositive)
    (hcrossed : Uᗮ.starProjection * T * U.starProjection =
      -star (U.starProjection * T * Uᗮ.starProjection)) :
    IsRealPrincipalUnitarySquareRoot U V T :=
  proposition3_3_real_forward U V T hunitary hintertwines hsource_pos
    hcomplement_pos hcrossed

/-- **Davis--Kahan 1970, Proposition 3.3 over `ℝ`, converse half, at the paper's
separable ambient scope.** -/
theorem proposition3_3_real_converse_separable [TopologicalSpace.SeparableSpace E]
    (T : E →L[ℝ] E)
    (hroot : IsRealPrincipalUnitarySquareRoot U V T)
    (hcross : T '' (halmosSourceDefect U V : Set E) =
      (halmosTargetDefect U V : Set E)) :
    T ∈ unitary (E →L[ℝ] E) ∧
      T * U.starProjection = V.starProjection * T ∧
      (U.starProjection * T * U.starProjection).IsPositive ∧
      (Uᗮ.starProjection * T * Uᗮ.starProjection).IsPositive ∧
      Uᗮ.starProjection * T * U.starProjection =
        -star (U.starProjection * T * Uᗮ.starProjection) :=
  proposition3_3_real_converse U V T hroot hcross

end Prop33Real

/-! ### Proposition 3.4 -/

section Prop34Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Davis--Kahan 1970, Proposition 3.4 over `ℂ`, at the paper's separable
ambient scope.** -/
theorem proposition3_4_full_complex_separable [TopologicalSpace.SeparableSpace H]
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (W : H →L[ℂ] H)
    (hunitary : W ∈ unitary (H →L[ℂ] H))
    (hintertwines : W * U.starProjection = V.starProjection * W)
    (hcrossed : Uᗮ.starProjection * W * U.starProjection =
      -star (U.starProjection * W * Uᗮ.starProjection))
    (hsource_pos : (U.starProjection * W * U.starProjection).IsPositive)
    (hcomplement_pos : (Uᗮ.starProjection * W * Uᗮ.starProjection).IsPositive)
    (hcos : ∀ x ∈ U, ‖x‖ ^ 2 / 2 ≤ ‖V.starProjection x‖ ^ 2) :
    (W * W) ∈ unitary (H →L[ℂ] H) ∧
      (W * W) * (reflectedSubspace U V).starProjection =
        V.starProjection * (W * W) ∧
      ((reflectedSubspace U V).starProjection * (W * W) *
        (reflectedSubspace U V).starProjection).IsPositive ∧
      ((reflectedSubspace U V)ᗮ.starProjection * (W * W) *
        (reflectedSubspace U V)ᗮ.starProjection).IsPositive ∧
      (reflectedSubspace U V)ᗮ.starProjection * (W * W) *
          (reflectedSubspace U V).starProjection =
        -star ((reflectedSubspace U V).starProjection * (W * W) *
          (reflectedSubspace U V)ᗮ.starProjection) :=
  proposition3_4_full_complex U V W hunitary hintertwines hcrossed hsource_pos
    hcomplement_pos hcos

end Prop34Complex

section Prop34Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (U V : Submodule ℝ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- **Davis--Kahan 1970, Proposition 3.4 over `ℝ`, at the paper's separable
ambient scope.** -/
theorem proposition3_4_full_real_separable [TopologicalSpace.SeparableSpace E]
    (W : E →L[ℝ] E)
    (hunitary : W ∈ unitary (E →L[ℝ] E))
    (hintertwines : W * U.starProjection = V.starProjection * W)
    (hcrossed : Uᗮ.starProjection * W * U.starProjection =
      -star (U.starProjection * W * Uᗮ.starProjection))
    (hsource_pos : (U.starProjection * W * U.starProjection).IsPositive)
    (hcomplement_pos : (Uᗮ.starProjection * W * Uᗮ.starProjection).IsPositive)
    (hcos : ∀ x ∈ U, ‖x‖ ^ 2 / 2 ≤ ‖V.starProjection x‖ ^ 2) :
    (W * W) ∈ unitary (E →L[ℝ] E) ∧
      (W * W) * (reflectedSubspace U V).starProjection =
        V.starProjection * (W * W) ∧
      ((reflectedSubspace U V).starProjection * (W * W) *
        (reflectedSubspace U V).starProjection).IsPositive ∧
      ((reflectedSubspace U V)ᗮ.starProjection * (W * W) *
        (reflectedSubspace U V)ᗮ.starProjection).IsPositive ∧
      (reflectedSubspace U V)ᗮ.starProjection * (W * W) *
          (reflectedSubspace U V).starProjection =
        -star ((reflectedSubspace U V).starProjection * (W * W) *
          (reflectedSubspace U V)ᗮ.starProjection) :=
  proposition3_4_full_real U V W hunitary hintertwines hcrossed hsource_pos
    hcomplement_pos hcos

end Prop34Real

/-! ### Corollary 3.1, the defect-block classification -/

section Cor31

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Davis--Kahan 1970, Corollary 3.1's classification, at the paper's separable
ambient scope on both pairs.** -/
theorem corollary3_1_compact_defectBlock_sourceAngleList_classification_separable
    {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
    [TopologicalSpace.SeparableSpace H₁]
    {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
    [TopologicalSpace.SeparableSpace H₂]
    (W₁ X₁ : Submodule 𝕜 H₁) [W₁.HasOrthogonalProjection] [X₁.HasOrthogonalProjection]
    (W₂ X₂ : Submodule 𝕜 H₂) [W₂.HasOrthogonalProjection] [X₂.HasOrthogonalProjection]
    (hcompact₁ : IsCompactOperator
      (W₁.starProjection ∘L
        (ContinuousLinearMap.id 𝕜 H₁ - X₁.starProjection) ∘L
          W₁.starProjection))
    (hcompact₂ : IsCompactOperator
      (W₂.starProjection ∘L
        (ContinuousLinearMap.id 𝕜 H₂ - X₂.starProjection) ∘L
          W₂.starProjection)) :
    PairOfSubspacesUnitaryEquivalent W₁ X₁ W₂ X₂ ↔
      SameHalmosTrivialDimensions W₁ X₁ W₂ X₂ ∧
      compactAngleList (genericCosineBlock W₁ X₁ᗮ) =
        compactAngleList (genericCosineBlock W₂ X₂ᗮ) :=
  corollary3_1_compact_defectBlock_sourceAngleList_classification W₁ X₁ W₂ X₂
    hcompact₁ hcompact₂

end Cor31

/-! ### Proposition 4.2 -/

section Prop42

/-- **Davis--Kahan 1970, Proposition 4.2 over `ℂ`, at the paper's separable
ambient scope.** -/
theorem proposition4_2_compact_nonacute_separable {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (hcrossed : DavisKahan.CrossedDefectsEquivalent U V)
    {ι : Type v} (b : HilbertBasis ι ℂ U)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    (∑' n : ℕ, ENNReal.ofReal
        (Real.sin (TauCeti.principalAngleSequence U V n)) ^ 2) ≤
      ∑' i, ENNReal.ofReal
        (DavisKahan.Section4.displacementAngleSineSq W ((b i : U) : H)) :=
  proposition4_2_compact_nonacute U V hcompact hcrossed (ι := ι) b W hWunitary hWmap

/-- **Davis--Kahan 1970, Proposition 4.2 over `ℝ`, at the paper's separable
ambient scope.** -/
theorem proposition4_2_compact_nonacute_real_separable {E : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (hcrossed : DavisKahan.CrossedDefectsEquivalent U V)
    {ι : Type v} (b : HilbertBasis ι ℝ U) (W : E →L[ℝ] E)
    (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    (∑' n : ℕ, ENNReal.ofReal
        (Real.sin (TauCeti.principalAngleSequence U V n)) ^ 2) ≤
      ∑' i, ENNReal.ofReal
        (displacementAngleSineSqR W ((b i : U) : E)) :=
  proposition4_2_compact_nonacute_real U V hcompact hcrossed (ι := ι) b W hWunitary hWmap

end Prop42

end

end DavisKahan1970
end TauCeti
