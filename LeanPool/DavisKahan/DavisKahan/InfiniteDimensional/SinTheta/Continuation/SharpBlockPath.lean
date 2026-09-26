/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.SharpRadius
public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.WitnessOffDiagonal

/-! # Sharp Block Path -/

@[expose] public section

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Sharp continuation block data along the affine path

This leaf records the exact block structure of the affine path
`A + t H` relative to a reducing subspace of `A` when `H` is off-diagonal.
The diagonal blocks are independent of `t`; the two cross blocks are the
corresponding compressions of `(t : ℂ) • H`.  Their norms are bounded by
`t * ‖H‖` for `t ∈ [0,1]`.

These are the operator inputs for the sharp finite-gap spectral-enclosure
argument.  No spectral inclusion is claimed in this leaf.
-/

namespace TauCeti
namespace DavisKahanExt


open DavisKahan

open Set
open scoped InnerProductSpace

universe v

section OffDiagonalScaling

variable {Hspace : Type v} [NormedAddCommGroup Hspace]
  [InnerProductSpace ℂ Hspace]

/-- Off-diagonality is preserved by scalar multiplication. -/
theorem isOffDiagonal_smul
    (U : Submodule ℂ Hspace) [U.HasOrthogonalProjection]
    (K : Hspace →L[ℂ] Hspace) (hK : Submodule.IsOffDiagonal U K) (c : ℂ) :
    Submodule.IsOffDiagonal U (c • K) := by
  change U.diagonalPart K = 0 at hK
  change U.diagonalPart (c • K) = 0
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg (fun T : Hspace →L[ℂ] Hspace => T x) hK
  have hcx := congrArg (fun y : Hspace => c • y) hx
  simpa [Submodule.diagonalPart, ContinuousLinearMap.comp_apply] using hcx

/-- Compression between two orthogonal-coordinate spaces cannot increase the
operator norm. -/
theorem norm_orthogonalProjection_comp_subtype_le
    (U W : Submodule ℂ Hspace) [U.HasOrthogonalProjection]
    (K : Hspace →L[ℂ] Hspace) :
    ‖U.orthogonalProjectionOnto ∘L K ∘L W.subtypeL‖ ≤ ‖K‖ := by
  calc
    ‖U.orthogonalProjectionOnto ∘L K ∘L W.subtypeL‖ ≤
        ‖U.orthogonalProjectionOnto‖ * ‖K ∘L W.subtypeL‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖K ∘L W.subtypeL‖ :=
      mul_le_mul_of_nonneg_right U.orthogonalProjectionOnto_norm_le
        (norm_nonneg (K ∘L W.subtypeL))
    _ = ‖K ∘L W.subtypeL‖ := one_mul _
    _ ≤ ‖K‖ * ‖W.subtypeL‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖K‖ * 1 :=
      mul_le_mul_of_nonneg_left W.norm_subtypeL_le (norm_nonneg K)
    _ = ‖K‖ := mul_one _

end OffDiagonalScaling

section PathBlockData

variable {Hspace : Type v} [NormedAddCommGroup Hspace]
  [InnerProductSpace ℂ Hspace] [CompleteSpace Hspace]

/-- The selected diagonal block of the affine path is constant. -/
theorem operatorPath_subspaceBlockOperatorData_A0_eq
    (A K : Hspace →L[ℂ] Hspace)
    (U : Submodule ℂ Hspace) [U.HasOrthogonalProjection]
    (_hU : A.Reduces U) (hK : Submodule.IsOffDiagonal U K)
    (t : ℝ) (hpath : (operatorPath A K t).IsSymmetric) :
    (subspaceBlockOperatorData (operatorPath A K t) U hpath).A0 =
      compressOperator U A := by
  have hKt : Submodule.IsOffDiagonal U ((t : ℂ) • K) :=
    isOffDiagonal_smul U K hK (t : ℂ)
  unfold operatorPath
  exact subspaceBlockOperatorData_A0_add_offDiagonal
    A ((t : ℂ) • K) U hpath hKt

/-- The complementary diagonal block of the affine path is constant. -/
theorem operatorPath_subspaceBlockOperatorData_A1_eq
    (A K : Hspace →L[ℂ] Hspace)
    (U : Submodule ℂ Hspace) [U.HasOrthogonalProjection]
    (_hU : A.Reduces U) (hK : Submodule.IsOffDiagonal U K)
    (t : ℝ) (hpath : (operatorPath A K t).IsSymmetric) :
    (subspaceBlockOperatorData (operatorPath A K t) U hpath).A1 =
      compressOperator Uᗮ A := by
  have hKt : Submodule.IsOffDiagonal U ((t : ℂ) • K) :=
    isOffDiagonal_smul U K hK (t : ℂ)
  unfold operatorPath
  exact subspaceBlockOperatorData_A1_add_offDiagonal
    A ((t : ℂ) • K) U hpath hKt

/-- The upper-right path block is exactly the corresponding compression of the
scaled perturbation. -/
theorem operatorPath_subspaceBlockOperatorData_B01_eq
    (A K : Hspace →L[ℂ] Hspace)
    (U : Submodule ℂ Hspace) [U.HasOrthogonalProjection]
    (hU : A.Reduces U)
    (t : ℝ) (hpath : (operatorPath A K t).IsSymmetric) :
    (subspaceBlockOperatorData (operatorPath A K t) U hpath).B01 =
      U.orthogonalProjectionOnto ∘L ((t : ℂ) • K) ∘L Uᗮ.subtypeL := by
  unfold operatorPath
  exact subspaceBlockOperatorData_B01_add_of_reduces
    A ((t : ℂ) • K) U hpath hU

/-- The lower-left path block is exactly the corresponding compression of the
scaled perturbation. -/
theorem operatorPath_subspaceBlockOperatorData_B10_eq
    (A K : Hspace →L[ℂ] Hspace)
    (U : Submodule ℂ Hspace) [U.HasOrthogonalProjection]
    (hU : A.Reduces U)
    (t : ℝ) (hpath : (operatorPath A K t).IsSymmetric) :
    (subspaceBlockOperatorData (operatorPath A K t) U hpath).B10 =
      Uᗮ.orthogonalProjectionOnto ∘L ((t : ℂ) • K) ∘L U.subtypeL := by
  unfold operatorPath
  exact subspaceBlockOperatorData_B10_add_of_reduces
    A ((t : ℂ) • K) U hpath hU

/-- Uniform upper-right cross-block norm bound along the affine path. -/
theorem norm_operatorPath_subspaceBlockOperatorData_B01_le
    (A K : Hspace →L[ℂ] Hspace)
    (U : Submodule ℂ Hspace) [U.HasOrthogonalProjection]
    (hU : A.Reduces U)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hpath : (operatorPath A K t).IsSymmetric) :
    ‖(subspaceBlockOperatorData (operatorPath A K t) U hpath).B01‖ ≤
      t * ‖K‖ := by
  rw [operatorPath_subspaceBlockOperatorData_B01_eq A K U hU t hpath]
  calc
    ‖U.orthogonalProjectionOnto ∘L ((t : ℂ) • K) ∘L Uᗮ.subtypeL‖ ≤
        ‖(t : ℂ) • K‖ :=
      norm_orthogonalProjection_comp_subtype_le U Uᗮ ((t : ℂ) • K)
    _ = t * ‖K‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ht.1]

/-- Uniform lower-left cross-block norm bound along the affine path. -/
theorem norm_operatorPath_subspaceBlockOperatorData_B10_le
    (A K : Hspace →L[ℂ] Hspace)
    (U : Submodule ℂ Hspace) [U.HasOrthogonalProjection]
    (hU : A.Reduces U)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hpath : (operatorPath A K t).IsSymmetric) :
    ‖(subspaceBlockOperatorData (operatorPath A K t) U hpath).B10‖ ≤
      t * ‖K‖ := by
  rw [operatorPath_subspaceBlockOperatorData_B10_eq A K U hU t hpath]
  calc
    ‖Uᗮ.orthogonalProjectionOnto ∘L ((t : ℂ) • K) ∘L U.subtypeL‖ ≤
        ‖(t : ℂ) • K‖ :=
      norm_orthogonalProjection_comp_subtype_le Uᗮ U ((t : ℂ) • K)
    _ = t * ‖K‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ht.1]

end PathBlockData

end DavisKahanExt
end TauCeti
