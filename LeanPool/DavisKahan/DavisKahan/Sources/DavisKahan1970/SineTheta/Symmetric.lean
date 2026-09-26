/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Lemma61
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.OperatorAngleBridge
public import
  LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.SubspaceSingularTransport
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.ReducingSubspace.RestrictionExtras
public import LeanPool.DavisKahan.DavisKahan.Sylvester.Unbounded.FormBoundedGap

/-! # Symmetric -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan Proposition 6.1: the symmetric sine theorem

This module follows the paper proof exactly.

1. Apply the one-sided sine theorem to the selected block of `A` and the
   complementary block of `B`.
2. Apply it again with `A` and `B` interchanged.
3. Use Lemma 6.1 to combine the two orthogonal cross blocks sharply.
4. Use Lemma 6.2 to contract the two corresponding perturbation blocks by the
   norm of `H = B - A`.
5. Identify the cross-block sum with the literal functional-calculus
   `sin Theta`.

No triangle estimate is used in the coupling step.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe v

open TauCeti.DavisKahanExt
open TauCeti.DavisKahan
open scoped TauCeti.CompleteSubspace

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Exact bounded inputs of Proposition 6.1.  The two gap hypotheses are the
paper's two applications of the original sine theorem. -/
structure SymmetricSinThetaProblem where
  /-- The first bounded symmetric operator in the complex comparison problem. -/
  A : E →L[ℂ] E
  /-- The second bounded symmetric operator in the complex comparison problem. -/
  B : E →L[ℂ] E
  selfAdjoint_A : A.IsSymmetric
  selfAdjoint_B : B.IsSymmetric
  /-- The chosen reducing subspace of the first operator. -/
  U : Submodule ℂ E
  /-- The chosen reducing subspace of the second operator. -/
  V : Submodule ℂ E
  proj_U : U.HasOrthogonalProjection
  proj_V : V.HasOrthogonalProjection
  reduces_A_U : A.Reduces U
  reduces_B_V : B.Reduces V
  /-- The common positive form gap for the two opposite subspace comparisons. -/
  gap : ℝ
  gap_pos : 0 < gap
  gap_U_to_Vperp : FormBoundedSylvesterGap
    (TauCeti.LinearPMap.reducingRestriction ((A.toLinearMap.toPMap ⊤)) U
      (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace A U reduces_A_U))
    (TauCeti.LinearPMap.reducingRestriction ((B.toLinearMap.toPMap ⊤)) Vᗮ
      (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace B V reduces_B_V).orthogonal)
    gap
  gap_V_to_Uperp : FormBoundedSylvesterGap
    (TauCeti.LinearPMap.reducingRestriction ((B.toLinearMap.toPMap ⊤)) V
      (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace B V reduces_B_V))
    (TauCeti.LinearPMap.reducingRestriction ((A.toLinearMap.toPMap ⊤)) Uᗮ
      (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace A U reduces_A_U).orthogonal)
    gap

attribute [instance] SymmetricSinThetaProblem.proj_U
attribute [instance] SymmetricSinThetaProblem.proj_V

namespace SymmetricSinThetaProblem

/-- The perturbation `H` of the paper. -/
def perturbation (P : SymmetricSinThetaProblem (E := E)) : E →L[ℂ] E :=
  P.B - P.A

/-- Internal data for the first directed application. -/
noncomputable def forwardData
    (P : SymmetricSinThetaProblem (E := E)) :
    UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := P.U) (G := P.Vᗮ) where
  A := (P.B.toLinearMap.toPMap ⊤)
  A₀ := TauCeti.LinearPMap.reducingRestriction ((P.A.toLinearMap.toPMap ⊤)) P.U
    (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.A P.U P.reduces_A_U)
  Λ₁ := TauCeti.LinearPMap.reducingRestriction ((P.B.toLinearMap.toPMap ⊤)) P.Vᗮ
    (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.B P.V P.reduces_B_V).orthogonal
  X := P.U.subtypeL
  F₁ := P.Vᗮ.subtypeL
  residual := P.perturbation ∘L P.U.subtypeL
  X_maps_domain := by intro x; simp
  F₁_maps_domain := by intro x; simp
  residual_eq := by
    intro x
    rfl
  intertwines :=
    PartialMap.reducingRestriction_inclusion_intertwines
      ((P.B.toLinearMap.toPMap ⊤)) P.Vᗮ
      (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.B P.V P.reduces_B_V).orthogonal

/-- Internal data for the reversed application. -/
noncomputable def reverseData
    (P : SymmetricSinThetaProblem (E := E)) :
    UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := P.V) (G := P.Uᗮ) where
  A := (P.A.toLinearMap.toPMap ⊤)
  A₀ := TauCeti.LinearPMap.reducingRestriction ((P.B.toLinearMap.toPMap ⊤)) P.V
    (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.B P.V P.reduces_B_V)
  Λ₁ := TauCeti.LinearPMap.reducingRestriction ((P.A.toLinearMap.toPMap ⊤)) P.Uᗮ
    (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.A P.U P.reduces_A_U).orthogonal
  X := P.V.subtypeL
  F₁ := P.Uᗮ.subtypeL
  residual := (-P.perturbation) ∘L P.V.subtypeL
  X_maps_domain := by intro x; simp
  F₁_maps_domain := by intro x; simp
  residual_eq := by
    intro x
    simp [perturbation]
    rfl
  intertwines :=
    PartialMap.reducingRestriction_inclusion_intertwines
      ((P.A.toLinearMap.toPMap ⊤)) P.Uᗮ
      (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.A P.U P.reduces_A_U).orthogonal

/-- The first exact cross-projection block. -/
def forwardSineBlock (P : SymmetricSinThetaProblem (E := E)) :
    E →L[ℂ] E :=
  P.Vᗮ.starProjection ∘L P.U.starProjection

/-- The reversed exact cross-projection block. -/
def reverseSineBlock (P : SymmetricSinThetaProblem (E := E)) :
    E →L[ℂ] E :=
  P.Uᗮ.starProjection ∘L P.V.starProjection

/-- The first projected perturbation block from the proof of Proposition 6.1. -/
def forwardResidualBlock (P : SymmetricSinThetaProblem (E := E)) :
    E →L[ℂ] E :=
  P.Vᗮ.starProjection ∘L P.perturbation ∘L P.U.starProjection

/-- The second projected perturbation block. -/
def reverseResidualBlock (P : SymmetricSinThetaProblem (E := E)) :
    E →L[ℂ] E :=
  P.V.starProjection ∘L P.perturbation ∘L P.Uᗮ.starProjection

/-- First one-sided estimate simultaneously for every finite Ky Fan gauge. -/
theorem forward_all_kyFan
    (P : SymmetricSinThetaProblem (E := E)) :
    ∀ k,
      P.gap * kyFanApproximationGauge k P.forwardSineBlock ≤
        kyFanApproximationGauge k P.forwardResidualBlock := by
  intro k
  by_cases hk0 : k = 0
  · subst k
    simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    let N := KyFanDominantIdealFamily.kyFan (𝕜 := ℂ) k hk
    let D := P.forwardData
    have hA0 : _root_.IsSelfAdjoint D.A₀ :=
      PartialMap.reducingRestriction_isSelfAdjoint
        ((P.A.toLinearMap.toPMap ⊤)) P.U
        (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.A P.U P.reduces_A_U)
        (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := P.A)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr P.selfAdjoint_A))
    have hL : _root_.IsSelfAdjoint D.Λ₁ :=
      PartialMap.reducingRestriction_isSelfAdjoint
        ((P.B.toLinearMap.toPMap ⊤)) P.Vᗮ
        (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.B P.V
          P.reduces_B_V).orthogonal
        (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := P.B)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr P.selfAdjoint_B))
    have hEq := unbounded_adjoint_residual_block_identity D
      (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := P.B)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr P.selfAdjoint_B)) hA0 hL
    have hraw := davisKahan1970_sylvester_complex N hA0 hL P.gap_pos
      P.gap_U_to_Vperp hEq
      (KyFanDominantIdealFamily.kyFan_mem (𝕜 := ℂ) k hk
        (-(D.residual.adjoint ∘L D.F₁)))
    -- The ambient transport lemma produces the *adjoint* orientation of each
    -- block, so both comparisons are heterogeneous and both pick up one
    -- adjoint step.  Ky Fan gauges are adjoint-invariant, so nothing is lost.
    have hsine : SameApproximationSingularSequence
        (P.U.starProjection ∘L P.Vᗮ.starProjection)
        (D.X.adjoint ∘L D.F₁) := by
      simpa [D, forwardData, Submodule.adjoint_subtypeL,
        Submodule.starProjection, ContinuousLinearMap.comp_assoc] using
        sameApproximationSingularValues_ambientSubspaceBlock
          P.Vᗮ P.U (D.X.adjoint ∘L D.F₁)
    have hsineAdj : P.forwardSineBlock =
        (P.U.starProjection ∘L P.Vᗮ.starProjection).adjoint := by
      rw [ContinuousLinearMap.adjoint_comp,
        (isSelfAdjoint_starProjection P.U).adjoint_eq,
        (isSelfAdjoint_starProjection P.Vᗮ).adjoint_eq]
      rfl
    have hres : SameApproximationSingularSequence
        (-P.forwardResidualBlock.adjoint)
        (-(D.residual.adjoint ∘L D.F₁)) := by
      simpa [D, forwardData, forwardResidualBlock, perturbation,
        Submodule.adjoint_subtypeL, Submodule.adjoint_orthogonalProjectionOnto,
        Submodule.starProjection,
        ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
        map_sub, map_neg] using
        sameApproximationSingularValues_ambientSubspaceBlock
          P.Vᗮ P.U (-(D.residual.adjoint ∘L D.F₁))
    have hgaugeSine : kyFanApproximationGauge k P.forwardSineBlock =
        kyFanApproximationGauge k (D.X.adjoint ∘L D.F₁) := by
      rw [hsineAdj, kyFanApproximationGauge_adjoint,
        hsine.kyFanApproximationGauge_eq k]
    have hgaugeRes : kyFanApproximationGauge k P.forwardResidualBlock =
        kyFanApproximationGauge k (-(D.residual.adjoint ∘L D.F₁)) := by
      rw [← kyFanApproximationGauge_adjoint k P.forwardResidualBlock,
        ← kyFanApproximationGauge_neg k P.forwardResidualBlock.adjoint,
        hres.kyFanApproximationGauge_eq k]
    simpa [N, KyFanDominantIdealFamily.kyFan_gauge,
      hgaugeSine, hgaugeRes] using hraw.2

/-- Reversed one-sided estimate simultaneously for every finite Ky Fan gauge. -/
theorem reverse_all_kyFan
    (P : SymmetricSinThetaProblem (E := E)) :
    ∀ k,
      P.gap * kyFanApproximationGauge k P.reverseSineBlock ≤
        kyFanApproximationGauge k P.reverseResidualBlock := by
  intro k
  by_cases hk0 : k = 0
  · subst k
    simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    let N := KyFanDominantIdealFamily.kyFan (𝕜 := ℂ) k hk
    let D := P.reverseData
    have hA0 : _root_.IsSelfAdjoint D.A₀ :=
      PartialMap.reducingRestriction_isSelfAdjoint
        ((P.B.toLinearMap.toPMap ⊤)) P.V
        (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.B P.V P.reduces_B_V)
        (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := P.B)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr P.selfAdjoint_B))
    have hL : _root_.IsSelfAdjoint D.Λ₁ :=
      PartialMap.reducingRestriction_isSelfAdjoint
        ((P.A.toLinearMap.toPMap ⊤)) P.Uᗮ
        (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.A P.U
          P.reduces_A_U).orthogonal
        (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := P.A)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr P.selfAdjoint_A))
    have hEq := unbounded_adjoint_residual_block_identity D
      (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := P.A)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr P.selfAdjoint_A)) hA0 hL
    have hraw := davisKahan1970_sylvester_complex N hA0 hL P.gap_pos
      P.gap_V_to_Uperp hEq
      (KyFanDominantIdealFamily.kyFan_mem (𝕜 := ℂ) k hk
        (-(D.residual.adjoint ∘L D.F₁)))
    -- Mirror of the forward case: the ambient transport lemma again produces
    -- the adjoint orientation, and Ky Fan gauges are adjoint-invariant.
    have hsine : SameApproximationSingularSequence
        (P.V.starProjection ∘L P.Uᗮ.starProjection)
        (D.X.adjoint ∘L D.F₁) := by
      simpa [D, reverseData, Submodule.adjoint_subtypeL,
        Submodule.starProjection, ContinuousLinearMap.comp_assoc] using
        sameApproximationSingularValues_ambientSubspaceBlock
          P.Uᗮ P.V (D.X.adjoint ∘L D.F₁)
    have hsineAdj : P.reverseSineBlock =
        (P.V.starProjection ∘L P.Uᗮ.starProjection).adjoint := by
      rw [ContinuousLinearMap.adjoint_comp,
        (isSelfAdjoint_starProjection P.V).adjoint_eq,
        (isSelfAdjoint_starProjection P.Uᗮ).adjoint_eq]
      rfl
    -- Here `A` and `B` are symmetric, so the ambient block comes out in the
    -- original orientation rather than the adjoint one.
    have hadjA : P.A.adjoint = P.A := P.selfAdjoint_A.isSelfAdjoint.adjoint_eq
    have hadjB : P.B.adjoint = P.B := P.selfAdjoint_B.isSelfAdjoint.adjoint_eq
    have hres : SameApproximationSingularSequence
        P.reverseResidualBlock
        (-(D.residual.adjoint ∘L D.F₁)) := by
      simpa [D, reverseData, reverseResidualBlock, perturbation, hadjA, hadjB,
        Submodule.adjoint_subtypeL, Submodule.adjoint_orthogonalProjectionOnto,
        Submodule.starProjection,
        ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
        map_sub, map_neg] using
        sameApproximationSingularValues_ambientSubspaceBlock
          P.Uᗮ P.V (-(D.residual.adjoint ∘L D.F₁))
    have hgaugeSine : kyFanApproximationGauge k P.reverseSineBlock =
        kyFanApproximationGauge k (D.X.adjoint ∘L D.F₁) := by
      rw [hsineAdj, kyFanApproximationGauge_adjoint,
        hsine.kyFanApproximationGauge_eq k]
    have hgaugeRes : kyFanApproximationGauge k P.reverseResidualBlock =
        kyFanApproximationGauge k (-(D.residual.adjoint ∘L D.F₁)) :=
      hres.kyFanApproximationGauge_eq k
    simpa [N, KyFanDominantIdealFamily.kyFan_gauge,
      hgaugeSine, hgaugeRes] using hraw.2

/-- Ky Fan form of the symmetric sine theorem, before universal Fan
 dominance. -/
theorem symmetric_all_kyFan
    (P : SymmetricSinThetaProblem (E := E)) :
    ∀ k,
      P.gap * kyFanApproximationGauge k
          (TauCeti.DavisKahan.Angle.sinAngleOperatorC P.U P.V) ≤
        kyFanApproximationGauge k P.perturbation := by
  intro k
  have hadjA : P.A.adjoint = P.A := P.selfAdjoint_A.isSelfAdjoint.adjoint_eq
  have hadjB : P.B.adjoint = P.B := P.selfAdjoint_B.isSelfAdjoint.adjoint_eq
  have hadjH : P.perturbation.adjoint = P.perturbation := by
    simp [perturbation, map_sub, hadjA, hadjB]
  have hUperp : P.Uᗮᗮ = P.U := Submodule.orthogonal_orthogonal P.U
  have hgapNorm : ‖((P.gap : ℝ) : ℂ)‖ = P.gap := by
    simp [abs_of_pos P.gap_pos]
  -- Lemma 6.1 is applied to the *scaled identity*, not to a scaled
  -- perturbation: the two one-sided estimates bound `gap` times a pure
  -- projection product, and `projectionBlock Ω Γ (gap • id)` is exactly
  -- `gap` times that product.  Feeding it `gap • H` would instead demand
  -- `gap * gauge (block H) ≤ gauge (block H)`, which is false for `gap > 1`.
  have hcombine := lemma61_all_kyFan P.Uᗮ P.V
    (((P.gap : ℝ) : ℂ) • ContinuousLinearMap.id ℂ E) (((P.gap : ℝ) : ℂ) • ContinuousLinearMap.id
      ℂ E)
    P.perturbation P.perturbation
    (fun j => by
      have hrev := P.reverse_all_kyFan j
      have hblockSine :
          projectionBlock P.Uᗮ P.V (((P.gap : ℝ) : ℂ) • ContinuousLinearMap.id ℂ E) =
            ((P.gap : ℝ) : ℂ) • P.reverseSineBlock := by
        ext x; simp [projectionBlock, reverseSineBlock]
      have hblockRes :
          projectionBlock P.Uᗮ P.V P.perturbation =
            P.reverseResidualBlock.adjoint := by
        simp [projectionBlock, reverseResidualBlock,
          ContinuousLinearMap.adjoint_comp, hadjH,
          (isSelfAdjoint_starProjection P.V).adjoint_eq,
          (isSelfAdjoint_starProjection P.Uᗮ).adjoint_eq,
          ContinuousLinearMap.comp_assoc]
      rw [hblockSine, hblockRes, kyFanApproximationGauge_smul,
        hgapNorm, kyFanApproximationGauge_adjoint]
      exact hrev)
    (fun j => by
      have hfwd := P.forward_all_kyFan j
      have hblockSine :
          projectionBlock P.Uᗮᗮ P.Vᗮ (((P.gap : ℝ) : ℂ) • ContinuousLinearMap.id ℂ E) =
            ((P.gap : ℝ) : ℂ) • P.forwardSineBlock.adjoint := by
        simp only [hUperp]
        ext x
        simp [projectionBlock, forwardSineBlock,
          ContinuousLinearMap.adjoint_comp,
          (isSelfAdjoint_starProjection P.U).adjoint_eq,
          (isSelfAdjoint_starProjection P.Vᗮ).adjoint_eq]
      have hblockRes :
          projectionBlock P.Uᗮᗮ P.Vᗮ P.perturbation =
            P.forwardResidualBlock.adjoint := by
        simp only [hUperp]
        simp [projectionBlock, forwardResidualBlock,
          ContinuousLinearMap.adjoint_comp, hadjH,
          (isSelfAdjoint_starProjection P.U).adjoint_eq,
          (isSelfAdjoint_starProjection P.Vᗮ).adjoint_eq,
          ContinuousLinearMap.comp_assoc]
      rw [hblockSine, hblockRes, kyFanApproximationGauge_smul,
        hgapNorm, kyFanApproximationGauge_adjoint,
        kyFanApproximationGauge_adjoint]
      exact hfwd) k
  have hsine := crossSineSum_same_literalSin P.U P.V
  have hres := diagonalPair_all_kyFan_le P.Uᗮ P.V P.perturbation k
  have hcross :
      projectionBlock P.Uᗮ P.V (((P.gap : ℝ) : ℂ) • ContinuousLinearMap.id ℂ E) +
          projectionBlock P.Uᗮᗮ P.Vᗮ
            (((P.gap : ℝ) : ℂ) • ContinuousLinearMap.id ℂ E) =
        ((P.gap : ℝ) : ℂ) • crossSineSum P.U P.V := by
    simp only [hUperp]
    ext x
    simp [projectionBlock, crossSineSum, smul_add]
  rw [hcross] at hcombine
  calc
    P.gap * kyFanApproximationGauge k
        (TauCeti.DavisKahan.Angle.sinAngleOperatorC P.U P.V) =
      kyFanApproximationGauge k
        (((P.gap : ℝ) : ℂ) • crossSineSum P.U P.V) := by
      rw [kyFanApproximationGauge_smul, hgapNorm,
        hsine.kyFanApproximationGauge_eq]
    _ ≤ kyFanApproximationGauge k
        (diagonalPair P.Uᗮ P.V P.perturbation) := hcombine
    _ ≤ kyFanApproximationGauge k P.perturbation := hres

/-- **Davis--Kahan 1970, Proposition 6.1**, for every normalized unitarily
invariant norm in the source sense. -/
theorem result_every_unitarilyInvariantNorm
    (P : SymmetricSinThetaProblem (E := E))
    (N : SymmetricNormingFunction) (hH : N.Mem P.perturbation) :
    N.Mem (TauCeti.DavisKahan.Angle.sinAngleOperatorC P.U P.V) ∧
      P.gap * N.gauge
          (TauCeti.DavisKahan.Angle.sinAngleOperatorC P.U P.V) ≤
        N.gauge P.perturbation :=
  N.mul_gauge_le_of_all_mul_kyFan_le P.gap_pos hH P.symmetric_all_kyFan

end SymmetricSinThetaProblem

end

end ExactSinTheta
end DavisKahan
end TauCeti
