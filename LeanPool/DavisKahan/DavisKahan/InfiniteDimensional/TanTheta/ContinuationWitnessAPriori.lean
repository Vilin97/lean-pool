/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.WitnessOffDiagonal
public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.TanTwoTheta.BoundedRiccatiShift

/-! # Continuation Witness APriori -/

@[expose] public section

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# A priori tangent control for a continuation-selected branch

This leaf converts the witness-selected ambient graph into the sharp bounded
Riccati estimate.  It is intentionally independent of the theorem that
constructs a witness from the final perturbation threshold: a witness, its
quantitative quarter-angle bound, off-diagonality, and ordered quadratic-form
bounds are explicit inputs.

The main result bounds the tangent of the maximal angle of the selected target
subspace by the perturbation norm divided by the ordered gap.  A later public
wrapper can supply the form bounds from the source spectral configuration and
supply the witness from sharp branch preservation.
-/

namespace TauCeti
namespace DavisKahanExt


open DavisKahan

open Set
open scoped InnerProductSpace

universe v

section CoordinateNorm

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- Compressing an ambient angular operator to `U → Uᗮ` preserves its operator
norm. -/
theorem norm_subspaceAngularCoordinate_eq
    (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (X : H →L[ℂ] H) (hX : IsAngularOperator U X) :
    ‖subspaceAngularCoordinate U X‖ = ‖X‖ := by
  let Y : U →L[ℂ] Uᗮ := subspaceAngularCoordinate U X
  apply le_antisymm
  · refine Y.opNorm_le_bound (norm_nonneg X) ?_
    intro u
    change ‖(((Y u : Uᗮ) : H))‖ ≤ ‖X‖ * ‖u‖
    rw [show (((Y u : Uᗮ) : H)) = X (u : H) from
      coe_subspaceAngularCoordinate_apply U X hX u]
    exact X.le_opNorm (u : H)
  · refine X.opNorm_le_bound (norm_nonneg Y) ?_
    intro x
    let u : U := U.orthogonalProjectionOnto x
    have hXP : X (U.starProjection x) = X x := by
      simpa only [ContinuousLinearMap.comp_apply] using
        ContinuousLinearMap.ext_iff.mp hX.1 x
    have hYu : (((Y u : Uᗮ) : H)) = X x := by
      calc
        (((Y u : Uᗮ) : H)) = X (u : H) :=
          coe_subspaceAngularCoordinate_apply U X hX u
        _ = X (U.starProjection x) := rfl
        _ = X x := hXP
    have hu_le : ‖u‖ ≤ ‖x‖ := by
      calc
        ‖u‖ ≤ ‖U.orthogonalProjectionOnto‖ * ‖x‖ :=
          U.orthogonalProjectionOnto.le_opNorm x
        _ ≤ 1 * ‖x‖ :=
          mul_le_mul_of_nonneg_right U.orthogonalProjectionOnto_norm_le
            (norm_nonneg x)
        _ = ‖x‖ := one_mul _
    calc
      ‖X x‖ = ‖Y u‖ := by
        change ‖X x‖ = ‖(((Y u : Uᗮ) : H))‖
        exact congrArg norm hYu.symm
      _ ≤ ‖Y‖ * ‖u‖ := Y.le_opNorm u
      _ ≤ ‖Y‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_left hu_le (norm_nonneg Y)

omit [CompleteSpace H] in
/-- A cross compression by two orthogonal-coordinate contractions cannot have
larger norm than the ambient operator. -/
theorem norm_orthogonal_cross_compression_le
    (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (V : H →L[ℂ] H) :
    ‖U.orthogonalProjectionOnto ∘L V ∘L Uᗮ.subtypeL‖ ≤ ‖V‖ := by
  let B : Uᗮ →L[ℂ] U :=
    U.orthogonalProjectionOnto ∘L V ∘L Uᗮ.subtypeL
  refine B.opNorm_le_bound (norm_nonneg V) ?_
  intro w
  change ‖U.orthogonalProjectionOnto (V (w : H))‖ ≤ ‖V‖ * ‖w‖
  calc
    ‖U.orthogonalProjectionOnto (V (w : H))‖ ≤
        ‖U.orthogonalProjectionOnto‖ * ‖V (w : H)‖ :=
      U.orthogonalProjectionOnto.le_opNorm (V (w : H))
    _ ≤ 1 * ‖V (w : H)‖ :=
      mul_le_mul_of_nonneg_right U.orthogonalProjectionOnto_norm_le
        (norm_nonneg (V (w : H)))
    _ = ‖V (w : H)‖ := one_mul _
    _ ≤ ‖V‖ * ‖w‖ := V.le_opNorm (w : H)

end CoordinateNorm

section WitnessAPriori

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {A V : H →L[ℂ] H} {s : Set ℝ}

namespace SpectralContinuationWitness

/-- The witness-selected angular operator satisfies the sharp contractive
Riccati inequality under an ordered quadratic-form gap on the source spectral
splitting. -/
theorem selectedEndpointAngularOperator_sharp_riccati_bound
    (C : SpectralContinuationWitness A V s)
    (hsmall : selectedBranchProjectionLipschitzConstant
      C.contour V C.margin < Real.sqrt 2 / 2)
    (hoff : Submodule.IsOffDiagonal C.sourceSelectedSpectralSubspace V)
    {c d : ℝ} (hd0 : 0 ≤ d)
    (hA0 : ∀ z : C.sourceSelectedSpectralSubspace,
      RCLike.re
          ⟪compressOperator C.sourceSelectedSpectralSubspace A z, z⟫_ℂ ≤
        c * ‖z‖ ^ 2)
    (hA1 : ∀ z : C.sourceSelectedSpectralSubspaceᗮ,
      (c + d) * ‖z‖ ^ 2 ≤
        RCLike.re
          ⟪compressOperator C.sourceSelectedSpectralSubspaceᗮ A z, z⟫_ℂ) :
    d * ‖C.selectedEndpointAngularOperator hsmall‖ ≤
      ‖V‖ * (1 - ‖C.selectedEndpointAngularOperator hsmall‖ ^ 2) := by
  let U := C.sourceSelectedSpectralSubspace
  let X : H →L[ℂ] H := C.selectedEndpointAngularOperator hsmall
  let Y : U →L[ℂ] Uᗮ := subspaceAngularCoordinate U X
  let B := subspaceBlockOperatorData (A + V) U
    C.targetSeparatingContour.selfAdjoint
  let : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  let : CompleteSpace (Uᗮ : Submodule ℂ H) :=
    (Uᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  have hXang : IsAngularOperator U X := by
    simpa only [U, X] using
      C.selectedEndpointAngularOperator_isAngularOperator hsmall
  have hnorm : ‖Y‖ = ‖X‖ := by
    simpa only [Y] using norm_subspaceAngularCoordinate_eq U X hXang
  have hYsolve : SolvesRiccati B Y := by
    simpa only [B, U, X, Y] using
      C.selectedEndpointAngularCoordinate_solvesRiccati hsmall
  have hYcontractive : ‖Y‖ < 1 := by
    rw [hnorm]
    simpa only [X] using C.norm_selectedEndpointAngularOperator_lt_one hsmall
  have hB0 : ∀ z : U,
      RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ c * ‖z‖ ^ 2 := by
    intro z
    rw [show B.A0 = compressOperator U A from by
      simpa only [B, U] using C.selectedEndpointBlockData_A0_eq hoff]
    simpa only [U] using hA0 z
  have hB1 : ∀ z : Uᗮ,
      (c + d) * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ := by
    intro z
    rw [show B.A1 = compressOperator Uᗮ A from by
      simpa only [B, U] using C.selectedEndpointBlockData_A1_eq hoff]
    simpa only [U] using hA1 z
  have hsharp := sharp_riccati_norm_bound_of_form_gap
    B hd0 hB0 hB1 hYsolve hYcontractive
  have hB01 : B.B01 =
      U.orthogonalProjectionOnto ∘L V ∘L Uᗮ.subtypeL := by
    simpa only [B, U] using C.selectedEndpointBlockData_B01_eq
  rw [hB01] at hsharp
  have hcross :
      ‖U.orthogonalProjectionOnto ∘L V ∘L Uᗮ.subtypeL‖ ≤ ‖V‖ :=
    norm_orthogonal_cross_compression_le U V
  have hfactor : 0 ≤ 1 - ‖Y‖ ^ 2 := by
    nlinarith [norm_nonneg Y]
  calc
    d * ‖C.selectedEndpointAngularOperator hsmall‖ = d * ‖Y‖ := by
      simpa only [X] using congrArg (fun r : ℝ => d * r) hnorm.symm
    _ ≤ ‖U.orthogonalProjectionOnto ∘L V ∘L Uᗮ.subtypeL‖ *
          (1 - ‖Y‖ ^ 2) := hsharp
    _ ≤ ‖V‖ * (1 - ‖Y‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hcross hfactor
    _ = ‖V‖ * (1 - ‖C.selectedEndpointAngularOperator hsmall‖ ^ 2) := by
      rw [hnorm]

/-- The selected angular operator obeys the elementary a priori tangent bound
`‖X‖ ≤ ‖V‖ / d`. -/
theorem norm_selectedEndpointAngularOperator_le_div
    (C : SpectralContinuationWitness A V s)
    (hsmall : selectedBranchProjectionLipschitzConstant
      C.contour V C.margin < Real.sqrt 2 / 2)
    (hoff : Submodule.IsOffDiagonal C.sourceSelectedSpectralSubspace V)
    {c d : ℝ} (hd : 0 < d)
    (hA0 : ∀ z : C.sourceSelectedSpectralSubspace,
      RCLike.re
          ⟪compressOperator C.sourceSelectedSpectralSubspace A z, z⟫_ℂ ≤
        c * ‖z‖ ^ 2)
    (hA1 : ∀ z : C.sourceSelectedSpectralSubspaceᗮ,
      (c + d) * ‖z‖ ^ 2 ≤
        RCLike.re
          ⟪compressOperator C.sourceSelectedSpectralSubspaceᗮ A z, z⟫_ℂ) :
    ‖C.selectedEndpointAngularOperator hsmall‖ ≤ ‖V‖ / d := by
  have hsharp := C.selectedEndpointAngularOperator_sharp_riccati_bound
    hsmall hoff hd.le hA0 hA1
  have hfactor_le :
      ‖V‖ * (1 - ‖C.selectedEndpointAngularOperator hsmall‖ ^ 2) ≤ ‖V‖ := by
    nlinarith [norm_nonneg V,
      sq_nonneg ‖C.selectedEndpointAngularOperator hsmall‖]
  apply (le_div_iff₀ hd).2
  rw [mul_comm]
  exact hsharp.trans hfactor_le

/-- Witness-level a priori tangent theorem.  The target selected spectral
subspace is the graph of the canonical angular operator, so its maximal-angle
tangent is bounded by `‖V‖ / d`. -/
theorem tan_maximalAngle_selectedSpectralSubspaces_le_div
    (C : SpectralContinuationWitness A V s)
    (hsmall : selectedBranchProjectionLipschitzConstant
      C.contour V C.margin < Real.sqrt 2 / 2)
    (hoff : Submodule.IsOffDiagonal C.sourceSelectedSpectralSubspace V)
    {c d : ℝ} (hd : 0 < d)
    (hA0 : ∀ z : C.sourceSelectedSpectralSubspace,
      RCLike.re
          ⟪compressOperator C.sourceSelectedSpectralSubspace A z, z⟫_ℂ ≤
        c * ‖z‖ ^ 2)
    (hA1 : ∀ z : C.sourceSelectedSpectralSubspaceᗮ,
      (c + d) * ‖z‖ ^ 2 ≤
        RCLike.re
          ⟪compressOperator C.sourceSelectedSpectralSubspaceᗮ A z, z⟫_ℂ) :
    Real.tan
        (maximalAngle C.sourceSelectedSpectralSubspace
          C.targetSelectedSpectralSubspace) ≤
      ‖V‖ / d := by
  have hgraphBound :
      Real.tan
          (maximalAngle C.sourceSelectedSpectralSubspace
            (graphSubspace C.sourceSelectedSpectralSubspace
              (C.selectedEndpointAngularOperator hsmall))) ≤
        ‖V‖ / d := by
    rw [tan_maximalAngle_eq_norm_angularOperator
      C.sourceSelectedSpectralSubspace
      (C.selectedEndpointAngularOperator hsmall)
      (C.selectedEndpointAngularOperator_isAngularOperator hsmall)]
    exact C.norm_selectedEndpointAngularOperator_le_div
      hsmall hoff hd hA0 hA1
  simpa only [C.graphSubspace_selectedEndpointAngularOperator hsmall] using
    hgraphBound

end SpectralContinuationWitness

end WitnessAPriori

end DavisKahanExt
end TauCeti
