/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Reflection
public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.DoubleAngle
public import LeanPool.DavisKahan.DavisKahan.DoubleAngle.UnboundedIdeal

/-! # Trial Reflection -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# The reflected system built from Davis--Kahan trial data

Section 7 of Davis--Kahan 1970 proves the `sin 2θ` theorem by reflecting through
the trial subspace.  When the ambient operator is bounded the reflected system is
just `J_V A J_V`.  When it is an unbounded self-adjoint closed operator that
expression is not available, but the *defect* still is, and it is bounded:

`D = J_V A J_V - A = -2 (X + X*)`,  `X = P_{Vᗮ} A P_V`,

and `X = P_{Vᗮ} R E₀*` depends only on the printed residual `R = A E₀ - E₀ A₀`
and not on `A`.  So the whole reflected system is manufactured from the trial
data `(V, A₀, R)` alone.

This module carries that construction and its two load-bearing facts, over any
`RCLike` scalar field:

* `reflectionDefect_trialOffDiagonalPart`: the defect of the off-diagonal part is
  `-2` times it;
* `trialReflection_intertwines`: `(A + D) J_V = J_V A` on `dom A`, which is the
  hypothesis the unbounded reflection estimate consumes.

The only analytic input is the symmetry of `A`, used once, in
`starProjection_apply_eq_trialCompression_adjoint`.
-/

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta

open scoped InnerProductSpace
open scoped TauCeti.CompleteSubspace

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

section TrialReflection

variable (V : Submodule 𝕜 H) [V.HasOrthogonalProjection]
  (M : V →L[𝕜] V) (R : V →L[𝕜] H)

/-- The bounded operator the trial data determines, namely `A P_V`.  It is
bounded because this specialization assumes both residual and trial operator
bounded. That is stronger than the source common-dense-domain setup, where the
trial operator may be unbounded. Only its off-diagonal residual block is needed
in the common-domain replacement. -/
def trialCompression : H →L[𝕜] H :=
  (R + V.subtypeL ∘L M) ∘L V.subtypeL.adjoint

/-- The single off-diagonal block `P_{Vᗮ} A P_V` of the trial data. -/
def trialOffDiagonalBlock : H →L[𝕜] H :=
  Vᗮ.starProjection ∘L trialCompression V M R ∘L V.starProjection

/-- The purely off-diagonal self-adjoint part of the trial data. -/
def trialOffDiagonalPart : H →L[𝕜] H :=
  trialOffDiagonalBlock V M R + (trialOffDiagonalBlock V M R).adjoint

end TrialReflection

section TrialAlgebra

variable {V : Submodule 𝕜 H} [V.HasOrthogonalProjection]
  {M : V →L[𝕜] V} {R : V →L[𝕜] H}

/-- The adjoint of the inclusion is the orthogonal projection, read in `H`. -/
theorem coe_subtypeL_adjoint_apply (x : H) :
    ((V.subtypeL.adjoint x : V) : H) = V.starProjection x := by
  rw [Submodule.adjoint_subtypeL]
  rfl

/-- `A P_V` is unchanged by a further projection: `T P_V = T`. -/
theorem trialCompression_comp_starProjection :
    trialCompression V M R ∘L V.starProjection = trialCompression V M R := by
  have hadj : V.subtypeL.adjoint ∘L V.starProjection = V.subtypeL.adjoint := by
    ext x
    simp only [Submodule.adjoint_subtypeL, ContinuousLinearMap.comp_apply]
    exact Submodule.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem x)
  unfold trialCompression
  rw [ContinuousLinearMap.comp_assoc, hadj]

omit [CompleteSpace H] in
/-- The complementary projection kills the trial subspace. -/
theorem complementProjection_comp_subtypeL :
    Vᗮ.starProjection ∘L (V.subtypeL : V →L[𝕜] H) = 0 := by
  ext v
  change Vᗮ.starProjection (v : H) = 0
  rw [Submodule.starProjection_orthogonal_apply,
    Submodule.starProjection_eq_self_iff.mpr v.property, sub_self]

/-- The off-diagonal block only sees the residual: `P_{Vᗮ} A P_V = P_{Vᗮ} R E₀*`.
This is the step that replaces the ambient operator by the printed residual. -/
theorem trialOffDiagonalBlock_eq :
    trialOffDiagonalBlock V M R =
      Vᗮ.starProjection ∘L R ∘L V.subtypeL.adjoint := by
  unfold trialOffDiagonalBlock
  rw [← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc,
    ContinuousLinearMap.comp_assoc (Vᗮ.starProjection) (trialCompression V M R)
      V.starProjection, trialCompression_comp_starProjection]
  unfold trialCompression
  ext x
  simp only [ContinuousLinearMap.comp_apply, add_apply, map_add]
  have h0 : Vᗮ.starProjection (V.subtypeL (M (V.subtypeL.adjoint x))) = 0 := by
    have := congrArg (fun L : V →L[𝕜] H => L (M (V.subtypeL.adjoint x)))
      (complementProjection_comp_subtypeL (V := V))
    simpa only [ContinuousLinearMap.comp_apply, zero_apply] using this
  rw [h0, add_zero]

/-- The trial off-diagonal part is self-adjoint. -/
theorem isSelfAdjoint_trialOffDiagonalPart :
    IsSelfAdjoint (trialOffDiagonalPart V M R) := by
  unfold trialOffDiagonalPart
  rw [IsSelfAdjoint, star_add, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint,
    add_comm]

/-- The adjoint of the off-diagonal block, in block form. -/
theorem trialOffDiagonalBlock_adjoint :
    (trialOffDiagonalBlock V M R).adjoint =
      V.starProjection ∘L (trialCompression V M R).adjoint ∘L
        Vᗮ.starProjection := by
  unfold trialOffDiagonalBlock
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    (isSelfAdjoint_starProjection V).adjoint_eq,
    (isSelfAdjoint_starProjection Vᗮ).adjoint_eq]
  rfl

/-- The projection onto `V` fixes the range of `T*`. -/
theorem starProjection_comp_trialCompression_adjoint :
    V.starProjection ∘L (trialCompression V M R).adjoint =
      (trialCompression V M R).adjoint := by
  have hsub : V.starProjection ∘L (V.subtypeL : V →L[𝕜] H) = V.subtypeL := by
    ext v
    change V.starProjection (v : H) = (v : H)
    exact Submodule.starProjection_eq_self_iff.mpr v.property
  unfold trialCompression
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ← ContinuousLinearMap.comp_assoc, hsub]

end TrialAlgebra

section TrialIntertwining

variable {V : Submodule 𝕜 H} [V.HasOrthogonalProjection]
  {M : V →L[𝕜] V} {R : V →L[𝕜] H}
  {A : H →ₗ.[𝕜] H}

/-- The trial subspace lies in the domain, so the projection of any vector does.
-/
theorem starProjection_mem_domain
    (hVdom : ∀ v : V, (v : H) ∈ A.domain) (x : H) :
    V.starProjection x ∈ A.domain := by
  have h := hVdom (V.subtypeL.adjoint x)
  rwa [coe_subtypeL_adjoint_apply] at h

/-- The trial data computes `A P_V`: this is the printed residual identity
`R = A E₀ - E₀ A₀` transported to the ambient space. -/
theorem apply_starProjection_eq_trialCompression
    (hVdom : ∀ v : V, (v : H) ∈ A.domain)
    (hres : ∀ v : V, A ⟨(v : H), hVdom v⟩ = R v + ((M v : V) : H))
    (x : H) :
    A ⟨V.starProjection x, starProjection_mem_domain hVdom x⟩ =
      trialCompression V M R x := by
  have hcoe : (⟨V.starProjection x, starProjection_mem_domain hVdom x⟩ : A.domain)
      = ⟨((V.subtypeL.adjoint x : V) : H), hVdom (V.subtypeL.adjoint x)⟩ := by
    apply Subtype.ext
    exact (coe_subtypeL_adjoint_apply (V := V) x).symm
  rw [hcoe, hres (V.subtypeL.adjoint x)]
  rfl

/-- **The adjoint identity.**  For a vector in the domain, projecting `A x` onto
the trial subspace is the same as applying the adjoint of `A P_V`.  This is the
only place the symmetry of the unbounded operator is used. -/
theorem starProjection_apply_eq_trialCompression_adjoint
    (hA : IsSelfAdjoint A)
    (hVdom : ∀ v : V, (v : H) ∈ A.domain)
    (hres : ∀ v : V, A ⟨(v : H), hVdom v⟩ = R v + ((M v : V) : H))
    (x : A.domain) :
    V.starProjection (A x) =
      (trialCompression V M R).adjoint (x : H) := by
  refine ext_inner_left 𝕜 fun y => ?_
  have hsym := (TauCeti.LinearPMap.isSymmetric_of_isSelfAdjoint hA)
    (⟨V.starProjection y, starProjection_mem_domain hVdom y⟩ : A.domain) x
  calc ⟪y, V.starProjection (A x)⟫_𝕜
      = ⟪V.starProjection y, A x⟫_𝕜 := by
        rw [← (isSelfAdjoint_starProjection V).adjoint_eq]
        rw [ContinuousLinearMap.adjoint_inner_left]
        rw [(isSelfAdjoint_starProjection V).adjoint_eq]
    _ = ⟪A (⟨V.starProjection y,
          starProjection_mem_domain hVdom y⟩ : A.domain), (x : H)⟫_𝕜 := hsym.symm
    _ = ⟪trialCompression V M R y, (x : H)⟫_𝕜 := by
        rw [apply_starProjection_eq_trialCompression hVdom hres y]
    _ = ⟪y, (trialCompression V M R).adjoint (x : H)⟫_𝕜 :=
        (ContinuousLinearMap.adjoint_inner_right _ _ _).symm

/-- `P_V T = T* P_V` on the whole space: the two ways of reading the diagonal
corner of `A` agree. -/
theorem starProjection_trialCompression_apply
    (hA : IsSelfAdjoint A)
    (hVdom : ∀ v : V, (v : H) ∈ A.domain)
    (hres : ∀ v : V, A ⟨(v : H), hVdom v⟩ = R v + ((M v : V) : H))
    (y : H) :
    V.starProjection (trialCompression V M R y) =
      (trialCompression V M R).adjoint (V.starProjection y) := by
  have h := starProjection_apply_eq_trialCompression_adjoint hA hVdom hres
    (⟨V.starProjection y, starProjection_mem_domain hVdom y⟩ : A.domain)
  rwa [apply_starProjection_eq_trialCompression hVdom hres y] at h

/-- The off-diagonal part reproduces the antisymmetric part of `A P_V`. -/
theorem trialOffDiagonalBlock_sub_adjoint_apply
    (hA : IsSelfAdjoint A)
    (hVdom : ∀ v : V, (v : H) ∈ A.domain)
    (hres : ∀ v : V, A ⟨(v : H), hVdom v⟩ = R v + ((M v : V) : H))
    (y : H) :
    trialOffDiagonalBlock V M R y - (trialOffDiagonalBlock V M R).adjoint y =
      trialCompression V M R y - (trialCompression V M R).adjoint y := by
  have hcomm := starProjection_trialCompression_apply hA hVdom hres y
  have hX : trialOffDiagonalBlock V M R y =
      trialCompression V M R y - V.starProjection (trialCompression V M R y) := by
    have h := congrArg (fun L : H →L[𝕜] H => L y)
      (trialCompression_comp_starProjection (V := V) (M := M) (R := R))
    simp only [ContinuousLinearMap.comp_apply] at h
    unfold trialOffDiagonalBlock
    simp only [ContinuousLinearMap.comp_apply, h,
      Submodule.starProjection_orthogonal_apply]
  have hXadj : (trialOffDiagonalBlock V M R).adjoint y =
      (trialCompression V M R).adjoint y -
        V.starProjection (trialCompression V M R y) := by
    have h1 : ∀ z : H, V.starProjection ((trialCompression V M R).adjoint z) =
        (trialCompression V M R).adjoint z := by
      intro z
      have h := congrArg (fun L : H →L[𝕜] H => L z)
        (starProjection_comp_trialCompression_adjoint (V := V) (M := M) (R := R))
      simpa only [ContinuousLinearMap.comp_apply] using h
    have hidem : ∀ z : H,
        V.starProjection (V.starProjection z) = V.starProjection z := fun z =>
      Submodule.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem z)
    rw [trialOffDiagonalBlock_adjoint]
    simp only [ContinuousLinearMap.comp_apply,
      Submodule.starProjection_orthogonal_apply, map_sub]
    rw [h1, ← hcomm, hidem]
  rw [hX, hXadj]
  abel

omit [CompleteSpace H] in
/-- Idempotence of an orthogonal projection, pointwise.  The submodule is
explicit: with it implicit, `rw` happily unifies it with `Vᗮ` and collapses the
wrong projection. -/
private theorem proj_proj (U : Submodule 𝕜 H) [U.HasOrthogonalProjection] (z : H) :
    U.starProjection (U.starProjection z) = U.starProjection z :=
  Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem z)

omit [CompleteSpace H] in
private theorem projPerp_proj (U : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    (z : H) : Uᗮ.starProjection (U.starProjection z) = 0 := by
  rw [Submodule.starProjection_orthogonal_apply, proj_proj, sub_self]

omit [CompleteSpace H] in
private theorem proj_projPerp (U : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    (z : H) : U.starProjection (Uᗮ.starProjection z) = 0 := by
  rw [Submodule.starProjection_orthogonal_apply, map_sub, proj_proj, sub_self]

private theorem trialOffDiagonalBlock_apply (z : H) :
    trialOffDiagonalBlock V M R z =
      Vᗮ.starProjection (trialCompression V M R (V.starProjection z)) := rfl

private theorem trialOffDiagonalBlock_adjoint_apply (z : H) :
    (trialOffDiagonalBlock V M R).adjoint z =
      V.starProjection ((trialCompression V M R).adjoint
        (Vᗮ.starProjection z)) := by
  rw [trialOffDiagonalBlock_adjoint]
  rfl

/-- The upper corner of the trial off-diagonal part is the block itself. -/
theorem trialOffDiagonalPart_upper :
    Vᗮ.starProjection ∘L trialOffDiagonalPart V M R ∘L V.starProjection =
      trialOffDiagonalBlock V M R := by
  ext z
  change Vᗮ.starProjection (trialOffDiagonalBlock V M R (V.starProjection z) +
      (trialOffDiagonalBlock V M R).adjoint (V.starProjection z)) =
    trialOffDiagonalBlock V M R z
  rw [trialOffDiagonalBlock_adjoint_apply, projPerp_proj V, map_zero, map_zero,
    add_zero, trialOffDiagonalBlock_apply (V.starProjection z), proj_proj V,
    trialOffDiagonalBlock_apply z, proj_proj Vᗮ]

/-- The lower corner of the trial off-diagonal part is the adjoint block. -/
theorem trialOffDiagonalPart_lower :
    V.starProjection ∘L trialOffDiagonalPart V M R ∘L Vᗮ.starProjection =
      (trialOffDiagonalBlock V M R).adjoint := by
  ext z
  change V.starProjection (trialOffDiagonalBlock V M R (Vᗮ.starProjection z) +
      (trialOffDiagonalBlock V M R).adjoint (Vᗮ.starProjection z)) =
    (trialOffDiagonalBlock V M R).adjoint z
  rw [trialOffDiagonalBlock_apply (Vᗮ.starProjection z), proj_projPerp V,
    map_zero, map_zero, zero_add,
    trialOffDiagonalBlock_adjoint_apply (Vᗮ.starProjection z), proj_proj Vᗮ,
    proj_proj V, trialOffDiagonalBlock_adjoint_apply z]

/-- The reflection defect of the trial off-diagonal part is `-2` times it: a
purely off-diagonal operator anticommutes with the reflection. -/
theorem reflectionDefect_trialOffDiagonalPart :
    reflectionDefect V (trialOffDiagonalPart V M R) =
      (-2 : 𝕜) • trialOffDiagonalPart V M R := by
  rw [reflectionDefect_eq_neg_two_smul_offdiag, trialOffDiagonalPart_upper,
    trialOffDiagonalPart_lower]
  rfl

/-- The reflection through the trial subspace preserves the domain. -/
theorem reflectionOperator_mem_domain
    (hVdom : ∀ v : V, (v : H) ∈ A.domain) (x : A.domain) :
    V.reflectionOperator (x : H) ∈ A.domain := by
  rw [Submodule.reflectionOperator_apply]
  exact A.domain.sub_mem (A.domain.smul_mem _ (starProjection_mem_domain hVdom _))
    x.property

/-- **The internal reflection bridge.**  The bounded operator
`D = -2 (X + X*)`, built from the trial data alone, implements the reflected
system on the whole domain: `(A + D) J_V = J_V A`.  This is what lets the
printed trial residual drive the reflection proof of the `sin 2Θ` theorem when
`A` is unbounded; the caller never sees `D`. -/
theorem trialReflection_intertwines
    (hA : IsSelfAdjoint A)
    (hVdom : ∀ v : V, (v : H) ∈ A.domain)
    (hres : ∀ v : V, A ⟨(v : H), hVdom v⟩ = R v + ((M v : V) : H))
    (x : A.domain) :
    (TauCeti.LinearPMap.addBounded A ((-2 : 𝕜) • trialOffDiagonalPart V M R))
        ⟨V.reflectionOperator (x : H), reflectionOperator_mem_domain hVdom x⟩ =
      V.reflectionOperator (A x) := by
  -- the reflected vector, as a domain element
  have hsplit :
      (⟨V.reflectionOperator (x : H), reflectionOperator_mem_domain hVdom x⟩ :
          A.domain) =
        (2 : 𝕜) • (⟨V.starProjection (x : H),
          starProjection_mem_domain hVdom (x : H)⟩ : A.domain) - x := by
    apply Subtype.ext
    simp [Submodule.reflectionOperator_apply V (x : H)]
  have hadd : (TauCeti.LinearPMap.addBounded A ((-2 : 𝕜) • trialOffDiagonalPart V M R))
        ⟨V.reflectionOperator (x : H), reflectionOperator_mem_domain hVdom x⟩ =
      A
          ⟨V.reflectionOperator (x : H), reflectionOperator_mem_domain hVdom x⟩ +
        ((-2 : 𝕜) • trialOffDiagonalPart V M R) (V.reflectionOperator (x : H)) :=
    rfl
  have h1 : A
        ⟨V.reflectionOperator (x : H), reflectionOperator_mem_domain hVdom x⟩ =
      (2 : 𝕜) • trialCompression V M R (x : H) - A x := by
    rw [hsplit, LinearPMap.map_sub, LinearPMap.map_smul,
      apply_starProjection_eq_trialCompression hVdom hres (x : H)]
  have h2 : V.reflectionOperator (A x) =
      (2 : 𝕜) • (trialCompression V M R).adjoint (x : H) - A x := by
    rw [Submodule.reflectionOperator_apply,
      starProjection_apply_eq_trialCompression_adjoint hA hVdom hres x]
  have hPrefl : V.starProjection (V.reflectionOperator (x : H)) =
      V.starProjection (x : H) := by
    rw [Submodule.reflectionOperator_apply, map_sub, map_smul, proj_proj V]
    module
  have hQrefl : Vᗮ.starProjection (V.reflectionOperator (x : H)) =
      -Vᗮ.starProjection (x : H) := by
    rw [Submodule.reflectionOperator_apply, map_sub, map_smul, projPerp_proj V]
    module
  have hXrefl : trialOffDiagonalBlock V M R (V.reflectionOperator (x : H)) =
      trialOffDiagonalBlock V M R (x : H) := by
    rw [trialOffDiagonalBlock_apply, hPrefl, ← trialOffDiagonalBlock_apply]
  have hXadjrefl :
      (trialOffDiagonalBlock V M R).adjoint (V.reflectionOperator (x : H)) =
        -(trialOffDiagonalBlock V M R).adjoint (x : H) := by
    rw [trialOffDiagonalBlock_adjoint_apply, hQrefl, map_neg, map_neg,
      ← trialOffDiagonalBlock_adjoint_apply]
  have hdefect : trialOffDiagonalPart V M R (V.reflectionOperator (x : H)) =
      trialCompression V M R (x : H) -
        (trialCompression V M R).adjoint (x : H) := by
    change trialOffDiagonalBlock V M R (V.reflectionOperator (x : H)) +
      (trialOffDiagonalBlock V M R).adjoint (V.reflectionOperator (x : H)) = _
    rw [hXrefl, hXadjrefl, ← sub_eq_add_neg,
      trialOffDiagonalBlock_sub_adjoint_apply hA hVdom hres (x : H)]
  have h3 : ((-2 : 𝕜) • trialOffDiagonalPart V M R)
        (V.reflectionOperator (x : H)) =
      (2 : 𝕜) • (trialCompression V M R).adjoint (x : H) -
        (2 : 𝕜) • trialCompression V M R (x : H) := by
    rw [smul_apply, hdefect]
    module
  rw [hadd, h1, h2, h3]
  module

end TrialIntertwining

end

end DavisKahan1970
end TauCeti
