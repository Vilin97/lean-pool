/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/

import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ComplexificationApproximation
import LeanPool.DavisKahan.DavisKahan.Sylvester.Spectrum

/-!
# Shifted diagonal blocks and cosine blocks of a subspace pair

For a bounded self-adjoint `A`, an orthogonally complemented `P`, and a second
subspace `Q`, this module names four ambient operators:

* `upperBlockShift A P α = P_{Pᗮ} (A - α) P_{Pᗮ}` -- the upper compression
  `A₁ - α`, extended by zero off `Pᗮ`;
* `lowerBlockShift A P α δ = P_P ((α + δ) - A) P_P` -- the lower compression
  `(α + δ) - A₀`, extended by zero off `P`;
* `cosineBlock P Q = P_{Qᗮ} P_{Pᗮ}` and `lowerCosineBlock P Q = P_Q P_P` -- the
  two cosine blocks, as ambient operators.

The lower pair is the image of the upper pair under `A ↦ -A`,
`α ↦ -(α + δ)`, the reflection exchanging the two sides of a spectral gap, which
is why the shift constant differs.

Everything here is form evaluation, self-adjointness, positivity, and the
sandwich positivity lemma `0 ≤ M → 0 ≤ D⋆ M D`.  None of it mentions a spectral
branch, a perturbation or an angle, so all of it is `RCLike`-generic.  The last
section records that each of the four blocks commutes with complexification,
which is what lets a real statement descend from its complex companion.
-/

namespace TauCeti
namespace DavisKahan

open scoped InnerProductSpace
open TauCeti.DavisKahan
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification
open TauCeti.DavisKahan.ExactSinTheta.ComplexificationApproximation

universe u v


section Generic

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- The unperturbed upper compression `A₁ - α`, extended by zero off `Pᗮ`. -/
noncomputable def upperBlockShift (A : H →L[𝕜] H) (P : Submodule 𝕜 H)
    [P.HasOrthogonalProjection] (alpha : ℝ) : H →L[𝕜] H :=
  Pᗮ.starProjection ∘L (A - (alpha : 𝕜) • ContinuousLinearMap.id 𝕜 H) ∘L
    Pᗮ.starProjection

/-- The cosine block `C₁`, as an ambient operator: `P_{Qᗮ} P_{Pᗮ}`. -/
noncomputable def cosineBlock (P Q : Submodule 𝕜 H)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection] : H →L[𝕜] H :=
  Qᗮ.starProjection ∘L Pᗮ.starProjection

/-- The unperturbed lower compression `(α + δ) - A₀`, extended by zero off `P`.

The shift constant is `α + δ`, not `α`: the lower clause is the image of the
upper one under `A ↦ -A`, `α ↦ -(α + δ)`, which is the reflection exchanging the
two sides of the printed gap. -/
noncomputable def lowerBlockShift (A : H →L[𝕜] H) (P : Submodule 𝕜 H)
    [P.HasOrthogonalProjection] (alpha delta : ℝ) : H →L[𝕜] H :=
  P.starProjection ∘L
    (((alpha + delta : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 H - A) ∘L P.starProjection

/-- The lower cosine block `C₀`, as an ambient operator: `P_Q P_P`. -/
noncomputable def lowerCosineBlock (P Q : Submodule 𝕜 H)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection] : H →L[𝕜] H :=
  Q.starProjection ∘L P.starProjection

/-- Evaluating the upper block shift: project to `Pᗮ`, shift by `α`, project
back. -/
theorem upperBlockShift_apply (A : H →L[𝕜] H) (P : Submodule 𝕜 H)
    [P.HasOrthogonalProjection] (alpha : ℝ) (x : H) :
    RCLike.re ⟪x, upperBlockShift A P alpha x⟫_𝕜 =
      RCLike.re ⟪Pᗮ.starProjection x, A (Pᗮ.starProjection x)⟫_𝕜 -
        alpha * ‖Pᗮ.starProjection x‖ ^ 2 := by
  have hself : ⟪x, upperBlockShift A P alpha x⟫_𝕜 =
      ⟪Pᗮ.starProjection x,
        (A - (alpha : 𝕜) • ContinuousLinearMap.id 𝕜 H) (Pᗮ.starProjection x)⟫_𝕜 := by
    show ⟪x, Pᗮ.starProjection ((A - (alpha : 𝕜) • ContinuousLinearMap.id 𝕜 H)
      (Pᗮ.starProjection x))⟫_𝕜 = _
    rw [← ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.isSelfAdjoint_iff'.mp (isSelfAdjoint_starProjection Pᗮ)]
  rw [hself]
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.id_apply, inner_sub_right, inner_smul_right, map_sub]
  have hnorm : RCLike.re ⟪Pᗮ.starProjection x, Pᗮ.starProjection x⟫_𝕜 =
      ‖Pᗮ.starProjection x‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := 𝕜) _
  have hs : RCLike.re ((alpha : 𝕜) *
      ⟪Pᗮ.starProjection x, Pᗮ.starProjection x⟫_𝕜) =
      alpha * ‖Pᗮ.starProjection x‖ ^ 2 := by
    rw [RCLike.re_ofReal_mul, hnorm]
  rw [hs]

/-- The real scalar shift is self-adjoint. -/
theorem adjoint_realShift (alpha : ℝ) :
    ContinuousLinearMap.adjoint ((alpha : 𝕜) • ContinuousLinearMap.id 𝕜 H) =
      (alpha : 𝕜) • ContinuousLinearMap.id 𝕜 H := by
  refine ContinuousLinearMap.ext fun y => ?_
  refine ext_inner_left 𝕜 fun z => ?_
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp only [smul_apply, ContinuousLinearMap.id_apply,
    inner_smul_left, inner_smul_right, RCLike.conj_ofReal]

/-- `upperBlockShift` is self-adjoint when `A` is: it is a projection sandwich of
the self-adjoint shift `A - α`. -/
theorem upperBlockShift_isSelfAdjoint (A : H →L[𝕜] H) (P : Submodule 𝕜 H)
    [P.HasOrthogonalProjection] (alpha : ℝ) (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (upperBlockShift A P alpha) := by
  have hP : ContinuousLinearMap.adjoint (Pᗮ : Submodule 𝕜 H).starProjection =
      (Pᗮ : Submodule 𝕜 H).starProjection :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp (isSelfAdjoint_starProjection _)
  have hB : ContinuousLinearMap.adjoint
      (A - (alpha : 𝕜) • ContinuousLinearMap.id 𝕜 H) =
      A - (alpha : 𝕜) • ContinuousLinearMap.id 𝕜 H := by
    rw [map_sub, adjoint_realShift, ContinuousLinearMap.isSelfAdjoint_iff'.mp hA]
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  show ContinuousLinearMap.adjoint (Pᗮ.starProjection ∘L
      (A - (alpha : 𝕜) • ContinuousLinearMap.id 𝕜 H) ∘L Pᗮ.starProjection) = _
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, hP, hB]
  simp [upperBlockShift, ContinuousLinearMap.comp_assoc]

/-- The unperturbed upper block is positive: on `Pᗮ` the form of `A` is at least
`α + δ`, so after subtracting `α` it is at least `δ ≥ 0`. -/
theorem upperBlockShift_nonneg (A : H →L[𝕜] H) (P : Submodule 𝕜 H)
    [P.HasOrthogonalProjection] {alpha delta : ℝ} (hdelta : 0 ≤ delta)
    (hA : IsSelfAdjoint A)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜) :
    (0 : H →L[𝕜] H) ≤ upperBlockShift A P alpha := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  refine ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (upperBlockShift_isSelfAdjoint A P alpha hA), fun x => ?_⟩
  have hmem : Pᗮ.starProjection x ∈ (Pᗮ : Submodule 𝕜 H) :=
    Submodule.starProjection_apply_mem _ x
  have hhigh := hPhigh _ hmem
  have hgoal : (upperBlockShift A P alpha).reApplyInnerSelf x =
      RCLike.re ⟪x, upperBlockShift A P alpha x⟫_𝕜 :=
    inner_re_symm (𝕜 := 𝕜) _ _
  have hswap : RCLike.re ⟪Pᗮ.starProjection x, A (Pᗮ.starProjection x)⟫_𝕜 =
      RCLike.re ⟪A (Pᗮ.starProjection x), Pᗮ.starProjection x⟫_𝕜 :=
    inner_re_symm (𝕜 := 𝕜) _ _
  rw [hgoal, upperBlockShift_apply, hswap]
  nlinarith [sq_nonneg ‖Pᗮ.starProjection x‖]

/-- Positivity is preserved by conjugation: `0 ≤ M` gives `0 ≤ D⋆ M D`. -/
theorem nonneg_adjoint_sandwich {M : H →L[𝕜] H} (hM : (0 : H →L[𝕜] H) ≤ M)
    (D : H →L[𝕜] H) :
    (0 : H →L[𝕜] H) ≤ ContinuousLinearMap.adjoint D ∘L M ∘L D := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  have hp := ((ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mp hM).conj_adjoint
    (ContinuousLinearMap.adjoint D)
  simpa only [ContinuousLinearMap.adjoint_adjoint] using hp

omit [CompleteSpace H] in
/-- The cosine block lands in `Qᗮ`, so `P_{Qᗮ}` fixes its image. -/
theorem starProjection_cosineBlock (P Q : Submodule 𝕜 H)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection] (x : H) :
    Qᗮ.starProjection (cosineBlock P Q x) = cosineBlock P Q x :=
  Submodule.starProjection_eq_self_iff.mpr
    (Submodule.starProjection_apply_mem _ _)

/-- Evaluating the lower block shift: project to `P`, subtract from `α + δ`,
project back. -/
theorem lowerBlockShift_apply (A : H →L[𝕜] H) (P : Submodule 𝕜 H)
    [P.HasOrthogonalProjection] (alpha delta : ℝ) (x : H) :
    RCLike.re ⟪x, lowerBlockShift A P alpha delta x⟫_𝕜 =
      (alpha + delta) * ‖P.starProjection x‖ ^ 2 -
        RCLike.re ⟪P.starProjection x, A (P.starProjection x)⟫_𝕜 := by
  have hself : ⟪x, lowerBlockShift A P alpha delta x⟫_𝕜 =
      ⟪P.starProjection x,
        (((alpha + delta : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 H - A)
          (P.starProjection x)⟫_𝕜 := by
    show ⟪x, P.starProjection ((((alpha + delta : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 H - A)
      (P.starProjection x))⟫_𝕜 = _
    rw [← ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.isSelfAdjoint_iff'.mp (isSelfAdjoint_starProjection P)]
  rw [hself]
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.id_apply, inner_sub_right, inner_smul_right, map_sub]
  have hnorm : RCLike.re ⟪P.starProjection x, P.starProjection x⟫_𝕜 =
      ‖P.starProjection x‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := 𝕜) _
  have hs : RCLike.re (((alpha + delta : ℝ) : 𝕜) *
      ⟪P.starProjection x, P.starProjection x⟫_𝕜) =
      (alpha + delta) * ‖P.starProjection x‖ ^ 2 := by
    rw [RCLike.re_ofReal_mul, hnorm]
  rw [hs]

/-- `lowerBlockShift` is self-adjoint when `A` is: it is a projection sandwich of
the self-adjoint shift `(α + δ) - A`. -/
theorem lowerBlockShift_isSelfAdjoint (A : H →L[𝕜] H) (P : Submodule 𝕜 H)
    [P.HasOrthogonalProjection] (alpha delta : ℝ) (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (lowerBlockShift A P alpha delta) := by
  have hP : ContinuousLinearMap.adjoint (P : Submodule 𝕜 H).starProjection =
      (P : Submodule 𝕜 H).starProjection :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp (isSelfAdjoint_starProjection _)
  have hB : ContinuousLinearMap.adjoint
      (((alpha + delta : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 H - A) =
      ((alpha + delta : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 H - A := by
    rw [map_sub, adjoint_realShift, ContinuousLinearMap.isSelfAdjoint_iff'.mp hA]
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  show ContinuousLinearMap.adjoint (P.starProjection ∘L
      (((alpha + delta : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 H - A) ∘L
        P.starProjection) = _
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, hP, hB]
  simp [lowerBlockShift, ContinuousLinearMap.comp_assoc]

/-- The unperturbed lower block is positive: on `P` the form of `A` is at most
`α`, so after subtracting it from `α + δ` at least `δ ≥ 0` is left. -/
theorem lowerBlockShift_nonneg (A : H →L[𝕜] H) (P : Submodule 𝕜 H)
    [P.HasOrthogonalProjection] {alpha delta : ℝ} (hdelta : 0 ≤ delta)
    (hA : IsSelfAdjoint A)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_𝕜 ≤ alpha * ‖x‖ ^ 2) :
    (0 : H →L[𝕜] H) ≤ lowerBlockShift A P alpha delta := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  refine ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (lowerBlockShift_isSelfAdjoint A P alpha delta hA), fun x => ?_⟩
  have hmem : P.starProjection x ∈ P := Submodule.starProjection_apply_mem _ x
  have hlow := hPlow _ hmem
  have hgoal : (lowerBlockShift A P alpha delta).reApplyInnerSelf x =
      RCLike.re ⟪x, lowerBlockShift A P alpha delta x⟫_𝕜 :=
    inner_re_symm (𝕜 := 𝕜) _ _
  have hswap : RCLike.re ⟪P.starProjection x, A (P.starProjection x)⟫_𝕜 =
      RCLike.re ⟪A (P.starProjection x), P.starProjection x⟫_𝕜 :=
    inner_re_symm (𝕜 := 𝕜) _ _
  rw [hgoal, lowerBlockShift_apply, hswap]
  nlinarith [sq_nonneg ‖P.starProjection x‖]

omit [CompleteSpace H] in
/-- The lower cosine block lands in `Q`, so `P_Q` fixes its image. -/
theorem starProjection_lowerCosineBlock (P Q : Submodule 𝕜 H)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection] (x : H) :
    Q.starProjection (lowerCosineBlock P Q x) = lowerCosineBlock P Q x :=
  Submodule.starProjection_eq_self_iff.mpr
    (Submodule.starProjection_apply_mem _ _)

end Generic

/-! ## Complexification

Each of the four ambient blocks commutes with `complexify`. -/

section Complexification

noncomputable section

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]


omit [CompleteSpace E] in
/-- The unperturbed upper block commutes with complexification. -/
theorem complexify_upperBlockShift (A : E →L[ℝ] E) (P : Submodule ℝ E)
    [P.HasOrthogonalProjection] (alpha : ℝ) :
    complexify (upperBlockShift A P alpha) =
      upperBlockShift (complexify A) (complexifySubmodule P) alpha := by
  simp only [upperBlockShift, complexify_comp, complexify_sub, complexify_real_smul,
    complexify_id, starProjection_complexifySubmodule_orthogonal,
    RCLike.ofReal_real_eq_id, id_eq]
  rfl

omit [CompleteSpace E] in
/-- The cosine block commutes with complexification. -/
theorem complexify_cosineBlock (P Q : Submodule ℝ E)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection] :
    complexify (cosineBlock P Q) =
      cosineBlock (complexifySubmodule P) (complexifySubmodule Q) := by
  simp only [cosineBlock, complexify_comp, starProjection_complexifySubmodule_orthogonal]

omit [CompleteSpace E] in
/-- The unperturbed lower block commutes with complexification. -/
theorem complexify_lowerBlockShift (A : E →L[ℝ] E) (P : Submodule ℝ E)
    [P.HasOrthogonalProjection] (alpha delta : ℝ) :
    complexify (lowerBlockShift A P alpha delta) =
      lowerBlockShift (complexify A) (complexifySubmodule P) alpha delta := by
  simp only [lowerBlockShift, complexify_comp, complexify_sub, complexify_real_smul,
    complexify_id, starProjection_complexifySubmodule,
    RCLike.ofReal_real_eq_id, id_eq]
  rfl

omit [CompleteSpace E] in
/-- The lower cosine block commutes with complexification. -/
theorem complexify_lowerCosineBlock (P Q : Submodule ℝ E)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection] :
    complexify (lowerCosineBlock P Q) =
      lowerCosineBlock (complexifySubmodule P) (complexifySubmodule Q) := by
  simp only [lowerCosineBlock, complexify_comp, starProjection_complexifySubmodule]

/-- The adjoint sandwich commutes with complexification. -/
theorem complexify_adjoint_sandwich (M D : E →L[ℝ] E) :
    complexify (ContinuousLinearMap.adjoint D ∘L M ∘L D) =
      ContinuousLinearMap.adjoint (complexify D) ∘L complexify M ∘L complexify D := by
  rw [complexify_comp, complexify_comp, complexify_adjoint]


end

end Complexification

end DavisKahan
end TauCeti
