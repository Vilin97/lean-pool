/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.PartialMap.UnitaryConjugation
public import LeanPool.DavisKahan.DavisKahan.SinTheta.SpectralProjection
public import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.OperatorAngleComplex
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Gap

/-! # Reflection Restriction -/

@[expose] public section

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Reflection transport for unbounded spectral restrictions

This module collects the reflection identities needed by the unbounded
sine-two-theta argument.  It includes the bounded double-angle geometry,
domain preservation for reflections through genuine spectral subspaces, and
the exact defect identity for a bounded perturbation.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan


open TauCeti.DavisKahan

universe u v

section ScalarGeneric

variable {𝕜 : Type u} [RCLike 𝕜]
variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Conjugation of a bounded operator by a linear isometry equivalence. -/
noncomputable def boundedUnitaryConjugate
    (W : H ≃ₗᵢ[𝕜] H) (A : H →L[𝕜] H) : H →L[𝕜] H :=
  W.toLinearIsometry.toContinuousLinearMap ∘L A ∘L
    W.symm.toLinearIsometry.toContinuousLinearMap

omit [CompleteSpace H] in
/-- The bounded unitary conjugate, unfolded. -/
@[simp] theorem boundedUnitaryConjugate_apply
    (W : H ≃ₗᵢ[𝕜] H) (A : H →L[𝕜] H) (x : H) :
    boundedUnitaryConjugate W A x = W (A (W.symm x)) := rfl

/-- Bounded unitary conjugation preserves self-adjointness. -/
theorem isSelfAdjoint_boundedUnitaryConjugate
    (W : H ≃ₗᵢ[𝕜] H) {A : H →L[𝕜] H} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (boundedUnitaryConjugate W A) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hA ⊢
  intro x y
  calc
    ⟪boundedUnitaryConjugate W A x, y⟫_𝕜 =
        ⟪W (A (W.symm x)), W (W.symm y)⟫_𝕜 := by
          rw [W.apply_symm_apply]
          rfl
    _ = ⟪A (W.symm x), W.symm y⟫_𝕜 := W.inner_map_map _ _
    _ = ⟪W.symm x, A (W.symm y)⟫_𝕜 := hA _ _
    _ = ⟪W (W.symm x), W (A (W.symm y))⟫_𝕜 :=
      (W.inner_map_map _ _).symm
    _ = ⟪x, boundedUnitaryConjugate W A y⟫_𝕜 := by
      rw [W.apply_symm_apply]
      rfl

omit [CompleteSpace H] in
/-- Orthogonal projection onto a unitary image is the conjugated original
projection. -/
theorem starProjection_map_unitary
    (U : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    (W : H ≃ₗᵢ[𝕜] H) :
    (U.map (W.toLinearEquiv : H →ₗ[𝕜] H)).starProjection =
      boundedUnitaryConjugate W U.starProjection := by
  ext x
  rw [Submodule.starProjection_map_apply]
  rfl

/-- The bounded residual produced by reflecting a perturbation. -/
noncomputable def reflectionPerturbation
    (V : Submodule 𝕜 H) [V.HasOrthogonalProjection]
    (E : H →L[𝕜] H) : H →L[𝕜] H :=
  E - boundedUnitaryConjugate V.reflection E

/-- The reflected perturbation is self-adjoint when the original perturbation
is self-adjoint. -/
theorem reflectionPerturbation_isSelfAdjoint
    (V : Submodule 𝕜 H) [V.HasOrthogonalProjection]
    (E : H →L[𝕜] H) (hE : E.IsSymmetric) :
    (reflectionPerturbation V E).IsSymmetric := by
  apply hE.sub
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (isSelfAdjoint_boundedUnitaryConjugate V.reflection
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hE))

omit [CompleteSpace H] in
/-- The reflected perturbation costs at most twice the original operator
norm. -/
theorem norm_reflectionPerturbation_le
    (V : Submodule 𝕜 H) [V.HasOrthogonalProjection]
    (E : H →L[𝕜] H) : ‖reflectionPerturbation V E‖ ≤ 2 * ‖E‖ := by
  have hconj : ‖boundedUnitaryConjugate V.reflection E‖ ≤ ‖E‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg E) fun x => ?_
    change ‖V.reflection (E (V.reflection.symm x))‖ ≤ ‖E‖ * ‖x‖
    rw [V.reflection.norm_map]
    calc
      ‖E (V.reflection.symm x)‖ ≤ ‖E‖ * ‖V.reflection.symm x‖ :=
        E.le_opNorm _
      _ = ‖E‖ * ‖x‖ := by rw [V.reflection.symm.norm_map]
  unfold reflectionPerturbation
  calc
    ‖E - boundedUnitaryConjugate V.reflection E‖ ≤
        ‖E‖ + ‖boundedUnitaryConjugate V.reflection E‖ := norm_sub_le _ _
    _ ≤ ‖E‖ + ‖E‖ := add_le_add (le_refl ‖E‖) hconj
    _ = 2 * ‖E‖ := by ring

/-! ## The reflected operator, identified as a unitary conjugate

The two facts a reflection argument establishes about `A + (E - J E J)` -- that
`J` preserves `dom A`, and that `(A + (E - J E J)) J = J A` there -- say exactly
that the perturbed operator *is* `J A J`.  Recording that as an equality of
partial maps is what lets the spectral vocabulary cross the reflection: reducing
subspaces, reducing restrictions and the form-bounded gap all transport through
`LinearPMap.unitaryConj`, and none of them transports through an intertwining
identity stated pointwise.

The hypotheses are the two lemmas the spectral development already proves --
`perturbedSpectralReflection_mem_domain` and
`add_reflectionPerturbation_intertwines` over `ℂ`, and their real siblings -- so
this lemma is scalar-generic even though those are not. -/

omit [CompleteSpace H] in
/-- **The reflected perturbation makes the operator the reflection conjugate.**

`J` is an involutive isometry, so preserving `dom A` in one direction preserves
it in both, and the pointwise intertwining then determines the action. -/
theorem addBounded_reflectionPerturbation_eq_unitaryConj
    {A : H →ₗ.[𝕜] H} (V : Submodule 𝕜 H) [V.HasOrthogonalProjection]
    (Eop : H →L[𝕜] H)
    (hmem : ∀ x : A.domain, V.reflectionOperator (x : H) ∈ A.domain)
    (hint : ∀ x : A.domain,
      (TauCeti.LinearPMap.addBounded A (reflectionPerturbation V Eop))
          ⟨V.reflectionOperator (x : H), hmem x⟩ =
        V.reflectionOperator (A x)) :
    TauCeti.LinearPMap.addBounded A (reflectionPerturbation V Eop) =
      TauCeti.LinearPMap.unitaryConj V.reflection A := by
  -- `V.reflection.symm = V.reflection` and `reflectionOperator = reflection` both hold
  -- definitionally, so the only content is that `J` preserves `dom A` in both
  -- directions and that the intertwining determines the action.
  have hrefl : ∀ y : H, V.reflectionOperator y = V.reflection y := fun _ => rfl
  have hmem' : ∀ y : H, y ∈ A.domain → V.reflection y ∈ A.domain := by
    intro y hy
    have h := hmem ⟨y, hy⟩
    rwa [hrefl] at h
  have hdomain : (TauCeti.LinearPMap.addBounded A
      (reflectionPerturbation V Eop)).domain =
      (TauCeti.LinearPMap.unitaryConj V.reflection A).domain := by
    ext y
    rw [TauCeti.LinearPMap.addBounded_domain,
      TauCeti.LinearPMap.mem_unitaryConj_domain_iff]
    refine ⟨fun hy => hmem' y hy, fun hy => ?_⟩
    have hy' : V.reflection y ∈ A.domain := hy
    have h := hmem' _ hy'
    rwa [V.reflection_reflection] at h
  refine _root_.LinearPMap.ext_iff.mpr ⟨hdomain, ?_⟩
  intro y hy hz
  have hJy : V.reflection y ∈ A.domain := hmem' y hy
  have hcongr : (⟨y, hy⟩ :
      (TauCeti.LinearPMap.addBounded A (reflectionPerturbation V Eop)).domain) =
      ⟨V.reflectionOperator (((⟨V.reflection y, hJy⟩ : A.domain)) : H),
        hmem ⟨V.reflection y, hJy⟩⟩ :=
    Subtype.ext (by
      change y = V.reflection (V.reflection y)
      exact (V.reflection_reflection y).symm)
  calc (TauCeti.LinearPMap.addBounded A (reflectionPerturbation V Eop)) ⟨y, hy⟩
      = (TauCeti.LinearPMap.addBounded A (reflectionPerturbation V Eop))
          ⟨V.reflectionOperator (((⟨V.reflection y, hJy⟩ : A.domain)) : H),
            hmem ⟨V.reflection y, hJy⟩⟩ := by rw [hcongr]
    _ = V.reflectionOperator (A ⟨V.reflection y, hJy⟩) :=
        hint ⟨V.reflection y, hJy⟩
    _ = (TauCeti.LinearPMap.unitaryConj V.reflection A) ⟨y, hz⟩ := rfl

omit [CompleteSpace H] in
/-- **The reflected perturbation intertwines whenever the reflection commutes with
`A + E` on the domain.**

`reflectionPerturbation V E = E − J E J` with `J = 2 P_V − 1`.  If `J` preserves
`dom A` and `A + E` commutes with `J` there -- which is what "`V` reduces `A + E`"
gives -- then `A + (E − J E J)` is the conjugate of `A` by `J`, so it carries
`J x` to `J (A x)`.

This is the scalar-generic core of `add_reflectionPerturbation_intertwines`, which
is the special case where `V` is a spectral subspace of `A + E` over `ℂ`.  Stated
from the commutation hypothesis directly so that a caller holding any reducing
subspace of the perturbed operator, spectral or not, can use it. -/
theorem addBounded_reflectionPerturbation_intertwines_of_commutes
    {A : H →ₗ.[𝕜] H} (E : H →L[𝕜] H)
    (V : Submodule 𝕜 H) [V.HasOrthogonalProjection]
    (hmem : ∀ x : A.domain, V.reflectionOperator (x : H) ∈ A.domain)
    (hcomm : ∀ x : A.domain,
      A ⟨V.reflectionOperator (x : H), hmem x⟩ + E (V.reflectionOperator (x : H)) =
        V.reflectionOperator (A x) + V.reflectionOperator (E (x : H)))
    (x : A.domain) :
    (TauCeti.LinearPMap.addBounded A (reflectionPerturbation V E))
        ⟨V.reflectionOperator (x : H), hmem x⟩ = V.reflectionOperator (A x) := by
  set J : H →L[𝕜] H := V.reflectionOperator with hJ
  have hreflection (y : H) : V.reflection y = J y := rfl
  have hJJ : J (J (x : H)) = (x : H) := by
    change V.reflection (V.reflection (x : H)) = (x : H)
    exact V.reflection_reflection (x : H)
  have hDapply : reflectionPerturbation V E (J (x : H)) =
      E (J (x : H)) - J (E (x : H)) := by
    calc
      reflectionPerturbation V E (J (x : H)) =
          E (J (x : H)) - V.reflection (E (V.reflection.symm (J (x : H)))) := rfl
      _ = E (J (x : H)) - V.reflection (E (V.reflection (J (x : H)))) := by
        rw [Submodule.reflection_symm]
      _ = E (J (x : H)) - J (E (J (J (x : H)))) := by
        rw [hreflection (J (x : H)), hreflection (E (J (J (x : H))))]
      _ = E (J (x : H)) - J (E (x : H)) := by rw [hJJ]
  calc
    (TauCeti.LinearPMap.addBounded A (reflectionPerturbation V E))
        ⟨J (x : H), hmem x⟩
        = A ⟨J (x : H), hmem x⟩ + reflectionPerturbation V E (J (x : H)) := rfl
    _ = A ⟨J (x : H), hmem x⟩ + (E (J (x : H)) - J (E (x : H))) := by rw [hDapply]
    _ = (A ⟨J (x : H), hmem x⟩ + E (J (x : H))) - J (E (x : H)) := by abel
    _ = (J (A x) + J (E (x : H))) - J (E (x : H)) := by rw [hcomm x]
    _ = J (A x) := add_sub_cancel_right _ _

end ScalarGeneric

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Reflection defect of a bounded operator. -/
noncomputable def boundedReflectionDefect
    (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    (A : H →L[ℂ] H) : H →L[ℂ] H :=
  V.reflectionOperator ∘L A ∘L V.reflectionOperator - A

omit [CompleteSpace H] in
/-- The reflection defect is minus twice the sum of the two off-diagonal
blocks. -/
theorem boundedReflectionDefect_eq_neg_two_smul_offdiag
    (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    (A : H →L[ℂ] H) :
    boundedReflectionDefect V A =
      (-2 : ℂ) • (Vᗮ.starProjection ∘L A ∘L V.starProjection +
        V.starProjection ∘L A ∘L Vᗮ.starProjection) := by
  ext x
  change V.reflectionOperator (A (V.reflectionOperator x)) - A x =
    (-2 : ℂ) • (Vᗮ.starProjection (A (V.starProjection x)) +
      V.starProjection (A (Vᗮ.starProjection x)))
  rw [Submodule.reflectionOperator_apply,
    Submodule.reflectionOperator_apply,
    Submodule.starProjection_orthogonal' V]
  simp only [map_sub, map_smul, sub_apply, one_apply_eq_self]
  module

/-- The two off-diagonal blocks are mutually adjoint for a self-adjoint
operator. -/
theorem reflectedOffdiag_adjoint
    (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) :
    (Vᗮ.starProjection ∘L A ∘L V.starProjection).adjoint =
      V.starProjection ∘L A ∘L Vᗮ.starProjection := by
  -- Left as a `rw` chain on purpose: `simp only` with this same list leaves the goal unsolved: at
  -- least one lemma here has to fire at one occurrence, in order, and simp's normal form loses the
  -- intermediate shape.
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ← ContinuousLinearMap.star_eq_adjoint,
    ← ContinuousLinearMap.star_eq_adjoint,
    ← ContinuousLinearMap.star_eq_adjoint,
    (isSelfAdjoint_starProjection V).star_eq,
    (isSelfAdjoint_starProjection Vᗮ).star_eq, hA.star_eq,
    ContinuousLinearMap.comp_assoc]

/-- Sharp norm estimate for the reflection defect of a self-adjoint bounded
operator. -/
theorem norm_boundedReflectionDefect_le_two_mul_norm_cross
    (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) :
    ‖boundedReflectionDefect V A‖ ≤
      2 * ‖Vᗮ.starProjection ∘L A ∘L V.starProjection‖ := by
  set T₁ : H →L[ℂ] H := Vᗮ.starProjection ∘L A ∘L V.starProjection
    with hT₁
  set T₂ : H →L[ℂ] H := V.starProjection ∘L A ∘L Vᗮ.starProjection
    with hT₂
  have hnormT₂ : ‖T₂‖ = ‖T₁‖ := by
    rw [hT₂, ← reflectedOffdiag_adjoint V hA,
      ← ContinuousLinearMap.star_eq_adjoint]
    exact norm_star _
  have hsum : ‖T₁ + T₂‖ ≤ ‖T₁‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => ?_
    have h1out : T₁ z ∈ Vᗮ := by
      rw [hT₁]
      exact Vᗮ.starProjection_apply_mem _
    have h2out : T₂ z ∈ V := by
      rw [hT₂]
      exact V.starProjection_apply_mem _
    have horth : ⟪T₂ z, T₁ z⟫_ℂ = 0 :=
      (Submodule.mem_orthogonal V _).mp h1out _ h2out
    have hpyth : ‖(T₁ + T₂) z‖ ^ 2 = ‖T₂ z‖ ^ 2 + ‖T₁ z‖ ^ 2 := by
      have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        (T₂ z) (T₁ z) horth
      have hadd : (T₁ + T₂) z = T₂ z + T₁ z := by
        rw [add_apply]
        abel
      rw [hadd, sq, sq, sq]
      linarith
    have hin1 : ‖T₁ z‖ ≤ ‖T₁‖ * ‖V.starProjection z‖ := by
      have hfac : T₁ z = T₁ (V.starProjection z) := by
        rw [hT₁]
        change Vᗮ.starProjection (A (V.starProjection z)) =
          Vᗮ.starProjection (A (V.starProjection (V.starProjection z)))
        rw [show V.starProjection (V.starProjection z) =
          V.starProjection z from
            Submodule.starProjection_eq_self_iff.mpr
              (V.starProjection_apply_mem z)]
      rw [hfac]
      exact T₁.le_opNorm _
    have hin2 : ‖T₂ z‖ ≤ ‖T₁‖ * ‖Vᗮ.starProjection z‖ := by
      have hfac : T₂ z = T₂ (Vᗮ.starProjection z) := by
        rw [hT₂]
        change V.starProjection (A (Vᗮ.starProjection z)) =
          V.starProjection (A (Vᗮ.starProjection (Vᗮ.starProjection z)))
        rw [show Vᗮ.starProjection (Vᗮ.starProjection z) =
          Vᗮ.starProjection z from
            Submodule.starProjection_eq_self_iff.mpr
              (Vᗮ.starProjection_apply_mem z)]
      rw [hfac]
      calc
        ‖T₂ (Vᗮ.starProjection z)‖ ≤
            ‖T₂‖ * ‖Vᗮ.starProjection z‖ := T₂.le_opNorm _
        _ = ‖T₁‖ * ‖Vᗮ.starProjection z‖ := by rw [hnormT₂]
    have hzdecomp : ‖z‖ ^ 2 =
        ‖V.starProjection z‖ ^ 2 + ‖Vᗮ.starProjection z‖ ^ 2 := by
      have horth' : ⟪V.starProjection z, Vᗮ.starProjection z⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal V _).mp
          (Vᗮ.starProjection_apply_mem z) _ (V.starProjection_apply_mem z)
      have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        (V.starProjection z) (Vᗮ.starProjection z) horth'
      rw [V.starProjection_add_starProjection_orthogonal z] at h
      rw [sq, sq, sq]
      linarith
    have hsq : ‖(T₁ + T₂) z‖ ^ 2 ≤ (‖T₁‖ * ‖z‖) ^ 2 := by
      rw [hpyth]
      have h1 := mul_self_le_mul_self (norm_nonneg (T₁ z)) hin1
      have h2 := mul_self_le_mul_self (norm_nonneg (T₂ z)) hin2
      have hkey : ‖T₂ z‖ ^ 2 + ‖T₁ z‖ ^ 2 ≤
          ‖T₁‖ ^ 2 * (‖V.starProjection z‖ ^ 2 +
            ‖Vᗮ.starProjection z‖ ^ 2) := by
        nlinarith [h1, h2]
      calc
        ‖T₂ z‖ ^ 2 + ‖T₁ z‖ ^ 2 ≤
            ‖T₁‖ ^ 2 * (‖V.starProjection z‖ ^ 2 +
              ‖Vᗮ.starProjection z‖ ^ 2) := hkey
        _ = (‖T₁‖ * ‖z‖) ^ 2 := by rw [← hzdecomp]; ring
    have hs := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg z))] at hs
  calc
    ‖boundedReflectionDefect V A‖ = ‖(-2 : ℂ) • (T₁ + T₂)‖ := by
      rw [boundedReflectionDefect_eq_neg_two_smul_offdiag]
    _ = 2 * ‖T₁ + T₂‖ := by
      rw [norm_smul]
      norm_num
    _ ≤ 2 * ‖T₁‖ := by linarith [hsum]

/-- The sum of the two off-diagonal blocks has exactly the norm of either
block when the middle operator is self-adjoint. -/
theorem norm_reflectedOffdiag_add_eq
    (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) :
    ‖Vᗮ.starProjection ∘L A ∘L V.starProjection +
        V.starProjection ∘L A ∘L Vᗮ.starProjection‖ =
      ‖Vᗮ.starProjection ∘L A ∘L V.starProjection‖ := by
  refine le_antisymm ?_ ?_
  · have h1 := norm_boundedReflectionDefect_le_two_mul_norm_cross V hA
    have h2 : ‖boundedReflectionDefect V A‖ =
        2 * ‖Vᗮ.starProjection ∘L A ∘L V.starProjection +
          V.starProjection ∘L A ∘L Vᗮ.starProjection‖ := by
      rw [boundedReflectionDefect_eq_neg_two_smul_offdiag, norm_smul]
      norm_num
    linarith
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => ?_
    have hVfix : V.starProjection (V.starProjection z) =
        V.starProjection z :=
      Submodule.starProjection_eq_self_iff.mpr
        (V.starProjection_apply_mem z)
    have hperp : Vᗮ.starProjection (V.starProjection z) = 0 := by
      rw [Submodule.starProjection_orthogonal' V, sub_apply,
        one_apply_eq_self, hVfix, sub_self]
    have hfact :
        (Vᗮ.starProjection ∘L A ∘L V.starProjection +
          V.starProjection ∘L A ∘L Vᗮ.starProjection)
            (V.starProjection z) =
          (Vᗮ.starProjection ∘L A ∘L V.starProjection) z := by
      change Vᗮ.starProjection (A (V.starProjection (V.starProjection z))) +
          V.starProjection (A (Vᗮ.starProjection (V.starProjection z))) =
        Vᗮ.starProjection (A (V.starProjection z))
      rw [hVfix, hperp, map_zero, map_zero, add_zero]
    calc
      ‖(Vᗮ.starProjection ∘L A ∘L V.starProjection) z‖ =
          ‖(Vᗮ.starProjection ∘L A ∘L V.starProjection +
            V.starProjection ∘L A ∘L Vᗮ.starProjection)
              (V.starProjection z)‖ := by rw [hfact]
      _ ≤ ‖Vᗮ.starProjection ∘L A ∘L V.starProjection +
            V.starProjection ∘L A ∘L Vᗮ.starProjection‖ *
            ‖V.starProjection z‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖Vᗮ.starProjection ∘L A ∘L V.starProjection +
            V.starProjection ∘L A ∘L Vᗮ.starProjection‖ * ‖z‖ :=
        mul_le_mul_of_nonneg_left (V.norm_starProjection_apply_le z)
          (norm_nonneg _)

omit [CompleteSpace H] in
/-- Bounded unitary conjugation preserves the operator norm. -/
theorem norm_boundedUnitaryConjugate
    (W : H ≃ₗᵢ[ℂ] H) (A : H →L[ℂ] H) :
    ‖boundedUnitaryConjugate W A‖ = ‖A‖ := by
  have hle : ‖boundedUnitaryConjugate W A‖ ≤ ‖A‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) fun x => ?_
    change ‖W (A (W.symm x))‖ ≤ ‖A‖ * ‖x‖
    rw [W.norm_map]
    calc
      ‖A (W.symm x)‖ ≤ ‖A‖ * ‖W.symm x‖ := A.le_opNorm _
      _ = ‖A‖ * ‖x‖ := by rw [W.symm.norm_map]
  have hdouble :
      boundedUnitaryConjugate W.symm (boundedUnitaryConjugate W A) = A := by
    ext x
    simp [boundedUnitaryConjugate_apply]
  have hback :
      ‖boundedUnitaryConjugate W.symm (boundedUnitaryConjugate W A)‖ ≤
        ‖boundedUnitaryConjugate W A‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _
      (norm_nonneg (boundedUnitaryConjugate W A)) fun x => ?_
    change ‖W.symm (boundedUnitaryConjugate W A (W x))‖ ≤
      ‖boundedUnitaryConjugate W A‖ * ‖x‖
    rw [W.symm.norm_map]
    calc
      ‖boundedUnitaryConjugate W A (W x)‖ ≤
          ‖boundedUnitaryConjugate W A‖ * ‖W x‖ :=
        (boundedUnitaryConjugate W A).le_opNorm _
      _ = ‖boundedUnitaryConjugate W A‖ * ‖x‖ := by rw [W.norm_map]
  rw [hdouble] at hback
  exact le_antisymm hle hback

omit [CompleteSpace H] in
/-- Directed projection gaps are invariant under simultaneous unitary
transport. -/
theorem directedGap_map_unitary
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (W : H ≃ₗᵢ[ℂ] H) :
    Submodule.directedProjectionGap
        (U.map (W.toLinearEquiv : H →ₗ[ℂ] H))
        (V.map (W.toLinearEquiv : H →ₗ[ℂ] H)) =
      U.directedProjectionGap V := by
  have hperpProjection :
      (V.map (W.toLinearEquiv : H →ₗ[ℂ] H))ᗮ.starProjection =
        boundedUnitaryConjugate W Vᗮ.starProjection := by
    ext x
    rw [Submodule.starProjection_orthogonal_apply,
      boundedUnitaryConjugate_apply,
      Submodule.starProjection_orthogonal_apply, map_sub,
      W.apply_symm_apply, Submodule.starProjection_map_apply]
  change ‖(V.map (W.toLinearEquiv : H →ₗ[ℂ] H))ᗮ.starProjection ∘L
      (U.map (W.toLinearEquiv : H →ₗ[ℂ] H)).starProjection‖ =
    ‖Vᗮ.starProjection ∘L U.starProjection‖
  rw [hperpProjection, starProjection_map_unitary]
  have hcomp :
      boundedUnitaryConjugate W Vᗮ.starProjection ∘L
          boundedUnitaryConjugate W U.starProjection =
        boundedUnitaryConjugate W
          (Vᗮ.starProjection ∘L U.starProjection) := by
    ext x
    simp [boundedUnitaryConjugate_apply]
  rw [hcomp, norm_boundedUnitaryConjugate]

omit [CompleteSpace H] in
/-- Applying the same reflection twice returns the original subspace. -/
theorem map_reflection_map_reflection
    (U V : Submodule ℂ H) [V.HasOrthogonalProjection] :
    (U.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).map
        (V.reflection.toLinearEquiv : H →ₗ[ℂ] H) = U := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hx
    refine ⟨V.reflection x, ?_, ?_⟩
    · exact ⟨x, hx, rfl⟩
    · exact V.reflection_reflection x

omit [CompleteSpace H] in
/-- The two directed gaps between a subspace and its reflected image are
equal. -/
theorem directedGap_reflection_symm
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.directedProjectionGap (U.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)) =
      Submodule.directedProjectionGap (U.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)) U := by
  have h := directedGap_map_unitary U
    (U.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)) V.reflection
  simpa only [map_reflection_map_reflection] using h.symm

/-- For a reflected pair, either directed gap already equals the full
projection gap. -/
theorem subspaceGap_eq_directedGap_reflection
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.projectionGap (U.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)) =
      U.directedProjectionGap (U.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)) := by
  let W := U.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)
  change ‖U.starProjection - W.starProjection‖ =
    ‖Wᗮ.starProjection ∘L U.starProjection‖
  rw [Submodule.norm_starProjection_sub_eq_max]
  rw [show (1 - W.starProjection : H →L[ℂ] H) = Wᗮ.starProjection from
      (Submodule.starProjection_orthogonal' W).symm,
    show (1 - U.starProjection : H →L[ℂ] H) = Uᗮ.starProjection from
      (Submodule.starProjection_orthogonal' U).symm]
  change max (U.directedProjectionGap W) (W.directedProjectionGap U) = U.directedProjectionGap W
  rw [← directedGap_reflection_symm U V, max_self]

omit [CompleteSpace H] in
/-- Conjugation by reflection carries the projection onto a subspace to the
projection onto its reflected image. -/
theorem starProjection_map_reflection
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (U.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection =
      boundedUnitaryConjugate V.reflection U.starProjection := by
  ext x
  rw [Submodule.starProjection_map_apply]
  rfl

omit [CompleteSpace H] in
/-- The projection gap to a reflected subspace is a reflection-defect norm. -/
theorem subspaceGap_map_reflection
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.projectionGap (U.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)) =
      ‖boundedReflectionDefect V U.starProjection‖ := by
  have hreflection :
      boundedUnitaryConjugate V.reflection U.starProjection =
        V.reflectionOperator ∘L U.starProjection ∘L
          V.reflectionOperator := by
    ext x
    change V.reflection (U.starProjection (V.reflection.symm x)) =
      V.reflectionOperator (U.starProjection (V.reflectionOperator x))
    rw [Submodule.reflection_symm]
    rfl
  have h : U.starProjection -
      (U.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection =
      -(boundedReflectionDefect V U.starProjection) := by
    rw [starProjection_map_reflection, hreflection]
    unfold boundedReflectionDefect
    abel
  change ‖U.starProjection -
      (U.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection‖ = _
  rw [h, norm_neg]

/-- The gap to the reflected image is exactly the norm of the complex
sine-two-angle operator. -/
theorem subspaceGap_map_reflection_eq_norm_sinTwoAngle
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.projectionGap (U.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)) =
      ‖directedSinTwoAngleOperatorC U V‖ := by
  rw [subspaceGap_map_reflection,
    boundedReflectionDefect_eq_neg_two_smul_offdiag, norm_smul,
    norm_reflectedOffdiag_add_eq V (isSelfAdjoint_starProjection U),
    norm_directedSinTwoAngleOperatorC]
  norm_num

/-- The orthogonal projection onto the complementary spectral range is the
projection onto the orthogonal complement of the selected one.

Stated at the level of projections rather than of subspaces.  Rewriting with
`selfAdjointSpectralSubspace_compl_eq_orthogonal` below under `starProjection`
gives "motive is not type correct", because `starProjection` takes a
`HasOrthogonalProjection` instance derived from the submodule; going through
the projections is what avoids that. -/
theorem starProjection_selfAdjointSpectralSubspace_compl
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (selfAdjointSpectralSubspace A hA Bᶜ hB.compl).starProjection =
      (selfAdjointSpectralSubspace A hA B hB)ᗮ.starProjection := by
  rw [← selfAdjointSpectralProjection_eq_starProjection A hA Bᶜ hB.compl,
    show selfAdjointSpectralProjection A hA Bᶜ hB.compl
        = ContinuousLinearMap.id ℂ H - selfAdjointSpectralProjection A hA B hB from
      (TauCeti.LinearPMap.spectralPVM hA).proj_compl B hB]
  rw [selfAdjointSpectralProjection_eq_starProjection A hA B hB]
  exact (Submodule.starProjection_orthogonal' _).symm

/-- The spectral range of a measurable complement is the orthogonal
complement of the original spectral range. -/
theorem selfAdjointSpectralSubspace_compl_eq_orthogonal
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    selfAdjointSpectralSubspace A hA Bᶜ hB.compl =
      (selfAdjointSpectralSubspace A hA B hB)ᗮ := by
  have hproj := starProjection_selfAdjointSpectralSubspace_compl A hA B hB
  apply le_antisymm
  · intro x hx
    apply Submodule.starProjection_eq_self_iff.mp
    rw [← hproj]
    exact Submodule.starProjection_eq_self_iff.mpr hx
  · intro x hx
    apply Submodule.starProjection_eq_self_iff.mp
    rw [hproj]
    exact Submodule.starProjection_eq_self_iff.mpr hx

/-- **A measurable spectral range reduces its own self-adjoint operator.**

Both projections preserve the domain because the spectral projection does
(`selfAdjointSpectralProjection_mem_domain`, applied to `B` and to `Bᶜ`), and
both summands are invariant because `A` maps a spectral range into itself
(`selfAdjointSpectralSubspace_compl_eq_orthogonal` identifies the complementary
range with the orthogonal complement).  This is the complex counterpart of
`RealSpectralRestriction.realSelfAdjointSpectralSubspace_reducing`. -/
theorem selfAdjointSpectralSubspace_reducing
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    TauCeti.LinearPMap.ReducesSubspace A (selfAdjointSpectralSubspace A hA B hB) := by
  have hcompl : selfAdjointSpectralSubspace A hA Bᶜ hB.compl =
      (selfAdjointSpectralSubspace A hA B hB)ᗮ :=
    selfAdjointSpectralSubspace_compl_eq_orthogonal A hA B hB
  refine TauCeti.LinearPMap.ReducesSubspace.of_components ?_ ?_ ?_ ?_
  · intro x
    rw [← selfAdjointSpectralProjection_eq_starProjection A hA B hB]
    exact selfAdjointSpectralProjection_mem_domain A hA hB x
  · intro x
    have hx := selfAdjointSpectralProjection_mem_domain A hA hB.compl x
    rw [selfAdjointSpectralProjection_eq_starProjection A hA Bᶜ hB.compl] at hx
    rwa [Submodule.starProjection_congr_apply hcompl] at hx
  · intro x hx
    exact selfAdjoint_maps_spectralSubspace A hA hB x hx
  · intro x hx
    rw [← hcompl] at hx ⊢
    exact selfAdjoint_maps_spectralSubspace A hA hB.compl x hx

/-- **The canonical spectral restriction is the reducing restriction.**

`selfAdjointSpectralRestriction` is `LinearPMap.specRestrict`, whose domain is
`A.domain` pulled back along the range inclusion and whose action is `A`; that is
the reducing restriction of `A` to the same subspace, on the nose.  The real
track defines its restriction as `reducingRestriction` directly, so this is the
bridge the complex track needs before a theorem stated over reducing
restrictions can consume a complex spectral gap hypothesis. -/
theorem selfAdjointSpectralRestriction_eq_reducingRestriction
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    selfAdjointSpectralRestriction A hA B hB =
      TauCeti.LinearPMap.reducingRestriction A (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace_reducing A hA B hB) := by
  refine _root_.LinearPMap.ext_iff.mpr ⟨rfl, ?_⟩
  intro x hx hy
  rfl

/-- Reflection through a genuine spectral range preserves the full domain of
the self-adjoint operator. -/
theorem spectralReflection_mem_domain
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B) (x : A.domain) :
    (selfAdjointSpectralSubspace A hA B hB).reflectionOperator (x : H) ∈
      A.domain := by
  let U := selfAdjointSpectralSubspace A hA B hB
  have hP : U.starProjection (x : H) ∈ A.domain := by
    rw [← selfAdjointSpectralProjection_eq_starProjection A hA B hB]
    exact selfAdjointSpectralProjection_mem_domain A hA hB x
  rw [Submodule.reflectionOperator_apply]
  exact A.domain.sub_mem (A.domain.smul_mem (2 : ℂ) hP) x.property

/-- Reflection through a genuine spectral range commutes with the
self-adjoint operator on its domain. -/
theorem selfAdjoint_apply_spectralReflection
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B) (x : A.domain) :
    A
        ⟨(selfAdjointSpectralSubspace A hA B hB).reflectionOperator (x : H),
          spectralReflection_mem_domain A hA B hB x⟩ =
      (selfAdjointSpectralSubspace A hA B hB).reflectionOperator
        (A x) := by
  let U := selfAdjointSpectralSubspace A hA B hB
  have hP : U.starProjection (x : H) ∈ A.domain := by
    rw [← selfAdjointSpectralProjection_eq_starProjection A hA B hB]
    exact selfAdjointSpectralProjection_mem_domain A hA hB x
  let px : A.domain := ⟨U.starProjection (x : H), hP⟩
  have hreflect :
      (⟨U.reflectionOperator (x : H),
        spectralReflection_mem_domain A hA B hB x⟩ : A.domain) =
        (2 : ℂ) • px - x := by
    apply Subtype.ext
    exact Submodule.reflectionOperator_apply U (x : H)
  have hproj :
      selfAdjointSpectralProjection A hA B hB = U.starProjection := by
    simpa [U] using
      selfAdjointSpectralProjection_eq_starProjection A hA B hB
  let qx : A.domain :=
    ⟨selfAdjointSpectralProjection A hA B hB (x : H),
      selfAdjointSpectralProjection_mem_domain A hA hB x⟩
  have hpx : px = qx := by
    apply Subtype.ext
    change U.starProjection (x : H) =
      selfAdjointSpectralProjection A hA B hB (x : H)
    rw [hproj]
  have hPcomm :
      A px = U.starProjection (A x) := by
    calc
      A px = A qx :=
        congrArg (fun y : A.domain => A y) hpx
      _ = selfAdjointSpectralProjection A hA B hB
          (A x) := by
        exact selfAdjoint_apply_spectralProjection A hA hB x
      _ = U.starProjection (A x) := by
        rw [hproj]
  rw [hreflect, LinearPMap.map_sub, LinearPMap.map_smul,
    Submodule.reflectionOperator_apply, hPcomm]

/-- For a perturbed operator `C = A + E`, reflection through a spectral range
of `C` preserves the original domain, because `C` and `A` have the same
domain. -/
theorem perturbedSpectralReflection_mem_domain
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (E : H →L[ℂ] H) (hE : E.IsSymmetric)
    (S : Set ℝ) (hS : MeasurableSet S) (x : A.domain) :
    (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A E)
      (addBounded_isSelfAdjoint A hA E hE) S hS).reflectionOperator (x : H) ∈
      A.domain := by
  let C := TauCeti.LinearPMap.addBounded A E
  let hC : IsSelfAdjoint C := addBounded_isSelfAdjoint A hA E hE
  let xc : C.domain := ⟨(x : H), by simp [C]⟩
  have h := spectralReflection_mem_domain C hC S hS xc
  simpa [C] using h

/-- The exact unbounded reflection-defect identity.  Reflecting `A` through a
spectral range of `A + E` is the same as adding the bounded operator
`E - J E J`. -/
theorem add_reflectionPerturbation_intertwines
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (E : H →L[ℂ] H) (hE : E.IsSymmetric)
    (S : Set ℝ) (hS : MeasurableSet S) (x : A.domain) :
    let C := TauCeti.LinearPMap.addBounded A E
    let hC : IsSelfAdjoint C := addBounded_isSelfAdjoint A hA E hE
    let V := selfAdjointSpectralSubspace C hC S hS
    let J := V.reflectionOperator
    let D := reflectionPerturbation V E
    (TauCeti.LinearPMap.addBounded A D)
        ⟨J (x : H), perturbedSpectralReflection_mem_domain
          A hA E hE S hS x⟩ = J (A x) := by
  dsimp only
  let C := TauCeti.LinearPMap.addBounded A E
  let hC : IsSelfAdjoint C := addBounded_isSelfAdjoint A hA E hE
  let V := selfAdjointSpectralSubspace C hC S hS
  let J := V.reflectionOperator
  let D := reflectionPerturbation V E
  have hJdomA : J (x : H) ∈ A.domain := by
    simpa [J, V, C] using
      perturbedSpectralReflection_mem_domain A hA E hE S hS x
  let xc : C.domain := ⟨(x : H), by simp [C]⟩
  have hcommC := selfAdjoint_apply_spectralReflection C hC S hS xc
  have hcomm :
      A ⟨J (x : H), hJdomA⟩ + E (J (x : H)) =
        J (A x + E (x : H)) := by
    calc
      A ⟨J (x : H), hJdomA⟩ + E (J (x : H)) =
          C
            ⟨J (x : H), spectralReflection_mem_domain C hC S hS xc⟩ := by
        rfl
      _ = J (C xc) := by
        simpa only [J, V] using hcommC
      _ = J (A x + E (x : H)) := by
        rfl
  have hJJ : J (J (x : H)) = (x : H) := by
    change V.reflection (V.reflection (x : H)) = (x : H)
    exact V.reflection_reflection (x : H)
  have hreflection (y : H) : V.reflection y = J y := rfl
  have hDapply : D (J (x : H)) = E (J (x : H)) - J (E (x : H)) := by
    calc
      D (J (x : H)) =
          E (J (x : H)) - V.reflection (E (V.reflection.symm (J (x : H)))) := by
        rfl
      _ = E (J (x : H)) - V.reflection (E (V.reflection (J (x : H)))) := by
        rw [Submodule.reflection_symm]
      _ = E (J (x : H)) - V.reflection (E (J (J (x : H)))) := by
        rw [hreflection (J (x : H))]
      _ = E (J (x : H)) - J (E (J (J (x : H)))) := by
        rw [hreflection (E (J (J (x : H))))]
      _ = E (J (x : H)) - J (E (x : H)) := by
        rw [hJJ]
  calc
    (TauCeti.LinearPMap.addBounded A D)
        ⟨J (x : H), perturbedSpectralReflection_mem_domain
          A hA E hE S hS x⟩ =
      A ⟨J (x : H), hJdomA⟩ + D (J (x : H)) := by
        rfl
    _ = A ⟨J (x : H), hJdomA⟩ +
        (E (J (x : H)) - J (E (x : H))) := by
      rw [hDapply]
    _ = (A ⟨J (x : H), hJdomA⟩ + E (J (x : H))) -
        J (E (x : H)) := by
      abel
    _ = J (A x + E (x : H)) - J (E (x : H)) := by
      rw [hcomm]
    _ = (J (A x) + J (E (x : H))) - J (E (x : H)) := by
      rw [map_add]
    _ = J (A x) := add_sub_cancel_right _ _

end DavisKahan
end TauCeti
