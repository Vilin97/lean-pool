/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.TanTwoTheta.BoundedOffDiagonalOrderedGap
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-! # Bounded Off Diagonal Reverse Gap -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Reverse ordered-gap estimate for bounded off-diagonal perturbations

The sharp Riccati norm estimate is invariant under negating every block of the
self-adjoint block operator.  This converts the reverse spectral orientation

`restrictedSpectrum A Uᗮ + d <= restrictedSpectrum A U`

into the already-solved centered form-gap problem without changing the angular
coordinate.  Combining the forward and reverse branches closes the
`OrderedInternalGap` estimate whenever both complementary coordinate spaces
are nontrivial.  Degenerate subspaces remain a separate final leaf.
-/

namespace TauCeti
namespace DavisKahanExt


open DavisKahan.Foundation

open DavisKahan

open scoped InnerProductSpace

universe v

variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- Negate all four entries of bounded self-adjoint block data. -/
noncomputable def negBlockOperatorData
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1)) :
    BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1) where
  A0 := -B.A0
  A1 := -B.A1
  B01 := -B.B01
  B10 := -B.B10
  selfAdjoint0 := by
    intro x y
    simpa using congrArg Neg.neg (B.selfAdjoint0 x y)
  selfAdjoint1 := by
    intro x y
    simpa using congrArg Neg.neg (B.selfAdjoint1 x y)
  offDiagonalAdjoint := by
    intro x y
    simpa using congrArg Neg.neg (B.offDiagonalAdjoint x y)

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- Negating all block entries negates the Riccati defect. -/
theorem riccatiDefect_negBlockOperatorData
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (X : E0 →L[ℂ] E1) :
    riccatiDefect (negBlockOperatorData B) X = -riccatiDefect B X := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [riccatiDefect, negBlockOperatorData, ContinuousLinearMap.comp_apply,
    sub_apply, add_apply, neg_apply, map_neg]
  abel

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- The Riccati equation is invariant under simultaneous negation of every
block entry. -/
theorem solvesRiccati_negBlockOperatorData_iff
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (X : E0 →L[ℂ] E1) :
    SolvesRiccati (negBlockOperatorData B) X ↔ SolvesRiccati B X := by
  unfold SolvesRiccati
  rw [riccatiDefect_negBlockOperatorData]
  simp

/-- Sharp Riccati norm inequality for the reverse centered form orientation. -/
theorem sharp_riccati_norm_bound_of_reverse_form_gap
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {c d : ℝ} (hd0 : 0 ≤ d)
    (hA0 : ∀ z : E0,
      (c + d) * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A0 z, z⟫_ℂ)
    (hA1 : ∀ z : E1,
      RCLike.re ⟪B.A1 z, z⟫_ℂ ≤ c * ‖z‖ ^ 2)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    (hXc : ‖X‖ < 1) :
    d * ‖X‖ ≤ ‖B.B01‖ * (1 - ‖X‖ ^ 2) := by
  let c' : ℝ := -(c + d)
  have hneg0 : ∀ z : E0,
      RCLike.re ⟪(negBlockOperatorData B).A0 z, z⟫_ℂ ≤
        c' * ‖z‖ ^ 2 := by
    intro z
    have hz := hA0 z
    dsimp only [negBlockOperatorData, c']
    simp only [neg_apply, inner_neg_left, map_neg]
    nlinarith
  have hneg1 : ∀ z : E1,
      (c' + d) * ‖z‖ ^ 2 ≤
        RCLike.re ⟪(negBlockOperatorData B).A1 z, z⟫_ℂ := by
    intro z
    have hz := hA1 z
    dsimp only [negBlockOperatorData, c']
    simp only [neg_apply, inner_neg_left, map_neg]
    nlinarith
  have hXneg : SolvesRiccati (negBlockOperatorData B) X :=
    (solvesRiccati_negBlockOperatorData_iff B X).2 hX
  have hbound := sharp_riccati_norm_bound_of_form_gap
    (negBlockOperatorData B) hd0 hneg0 hneg1 hXneg hXc
  simpa [negBlockOperatorData] using hbound

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Sharp contractive Riccati inequality when the compressed spectra occur in
the reverse ordered half-lines. -/
theorem quarterAcuteAngularCoordinate_sharp_bound_of_reverse_spectral_halfLines
    (A H : E →L[ℂ] E)
    (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : ContinuousLinearMap.Reduces (A + H) V)
    (hoff : Submodule.IsOffDiagonal U H)
    {c d : ℝ} (hd : 0 < d)
    (hA0spec : spectrum ℝ (compressOperator U A) ⊆ Set.Ici (c + d))
    (hA1spec : spectrum ℝ (compressOperator Uᗮ A) ⊆ Set.Iic c)
    (hquarter : IsQuarterAcute U V) :
    d * ‖quarterAcuteAngularCoordinate U V hquarter‖ ≤
      ‖H‖ * (1 - ‖quarterAcuteAngularCoordinate U V hquarter‖ ^ 2) := by
  let : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  let : CompleteSpace (Uᗮ : Submodule ℂ E) :=
    (Uᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  have hAH : (A + H).IsSymmetric := by
    have h := hA.add hH
    rwa [← ContinuousLinearMap.toLinearMap_add] at h
  let B : BlockOperatorData (𝕜 := ℂ) (E0 := U) (E1 := Uᗮ) :=
    subspaceBlockOperatorData (A + H) U hAH
  let X : U →L[ℂ] Uᗮ := quarterAcuteAngularCoordinate U V hquarter
  have hsolve : SolvesRiccati B X := by
    simpa [B, X] using
      quarterAcuteAngularCoordinate_solvesRiccati A H hA hH U V hV hquarter
  have hB0 : B.A0 = compressOperator U A := by
    simpa [B] using
      subspaceBlockOperatorData_A0_add_offDiagonal A H U hAH hoff
  have hB1 : B.A1 = compressOperator Uᗮ A := by
    simpa [B] using
      subspaceBlockOperatorData_A1_add_offDiagonal A H U hAH hoff
  have hB01 : B.B01 =
      U.orthogonalProjectionOnto ∘L H ∘L Uᗮ.subtypeL := by
    simpa [B] using
      subspaceBlockOperatorData_B01_add_of_reduces A H U hAH hU
  have hB0form : ∀ z : U,
      (c + d) * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A0 z, z⟫_ℂ := by
    intro z
    rw [hB0]
    exact compressOperator_lowerFormBound_of_spectrum_subset_Ici
      A hA U hA0spec z
  have hB1form : ∀ z : Uᗮ,
      RCLike.re ⟪B.A1 z, z⟫_ℂ ≤ c * ‖z‖ ^ 2 := by
    intro z
    rw [hB1]
    exact compressOperator_upperFormBound_of_spectrum_subset_Iic
      A hA Uᗮ hA1spec z
  have hXcontractive : ‖X‖ < 1 := by
    simpa [X] using norm_quarterAcuteAngularCoordinate_lt_one U V hquarter
  have hsharp : d * ‖X‖ ≤ ‖B.B01‖ * (1 - ‖X‖ ^ 2) :=
    sharp_riccati_norm_bound_of_reverse_form_gap B hd.le hB0form hB1form
      hsolve hXcontractive
  have hcoupling : ‖B.B01‖ ≤ ‖H‖ := by
    rw [hB01]
    exact norm_upperRightSubspaceCompression_le U H
  have hfactor : 0 ≤ 1 - ‖X‖ ^ 2 := by
    nlinarith [norm_nonneg X, hXcontractive]
  calc
    d * ‖quarterAcuteAngularCoordinate U V hquarter‖ = d * ‖X‖ := by rfl
    _ ≤ ‖B.B01‖ * (1 - ‖X‖ ^ 2) := hsharp
    _ ≤ ‖H‖ * (1 - ‖X‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hcoupling hfactor
    _ = ‖H‖ *
        (1 - ‖quarterAcuteAngularCoordinate U V hquarter‖ ^ 2) := by rfl

/-- Sharp contractive Riccati inequality in the reverse ordered orientation. -/
theorem quarterAcuteAngularCoordinate_sharp_bound_of_reverse_orderedSpectraSeparated
    (A H : E →L[ℂ] E)
    (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] [Nontrivial Uᗮ]
    (hU : A.Reduces U) (hV : ContinuousLinearMap.Reduces (A + H) V)
    (hoff : Submodule.IsOffDiagonal U H)
    {d : ℝ} (hd : 0 < d)
    (hordered : OrderedSpectraSeparated A Uᗮ A U d)
    (hquarter : IsQuarterAcute U V) :
    d * ‖quarterAcuteAngularCoordinate U V hquarter‖ ≤
      ‖H‖ * (1 - ‖quarterAcuteAngularCoordinate U V hquarter‖ ^ 2) := by
  obtain ⟨c, hUchalf, hUhalf⟩ :=
    OrderedSpectraSeparated.exists_halfLine_center hordered
      (restrictedSpectrum_nonempty_of_invariant A hA Uᗮ hordered.1)
      (restrictedSpectrum_bddAbove_of_invariant A Uᗮ hordered.1)
  have hA0spec : spectrum ℝ (compressOperator U A) ⊆ Set.Ici (c + d) :=
    spectrum_real_compress_subset_Ici_of_restrictedSpectrum_subset_Ici
      A hA U hordered.2.1 hUhalf
  have hA1spec : spectrum ℝ (compressOperator Uᗮ A) ⊆ Set.Iic c :=
    spectrum_real_compress_subset_Iic_of_restrictedSpectrum_subset_Iic
      A hA Uᗮ hordered.1 hUchalf
  exact quarterAcuteAngularCoordinate_sharp_bound_of_reverse_spectral_halfLines
    A H hA hH U V hU hV hoff hd hA0spec hA1spec hquarter

/-- The sharp contractive Riccati inequality from either branch of an ordered
internal gap, assuming both coordinate spaces are nontrivial. -/
theorem quarterAcuteAngularCoordinate_sharp_bound_of_orderedInternalGap_nontrivial
    (A H : E →L[ℂ] E)
    (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] [Nontrivial U] [Nontrivial Uᗮ]
    (hU : A.Reduces U) (hV : ContinuousLinearMap.Reduces (A + H) V)
    (hoff : Submodule.IsOffDiagonal U H)
    {d : ℝ} (hd : 0 < d) (hgap : OrderedInternalGap A U d)
    (hquarter : IsQuarterAcute U V) :
    d * ‖quarterAcuteAngularCoordinate U V hquarter‖ ≤
      ‖H‖ * (1 - ‖quarterAcuteAngularCoordinate U V hquarter‖ ^ 2) := by
  rcases hgap with hforward | hreverse
  · exact quarterAcuteAngularCoordinate_sharp_bound_of_orderedSpectraSeparated
      A H hA hH U V hU hV hoff hd hforward hquarter
  · exact quarterAcuteAngularCoordinate_sharp_bound_of_reverse_orderedSpectraSeparated
      A H hA hH U V hU hV hoff hd hreverse hquarter

end DavisKahanExt
end TauCeti
