/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.DirectRotation.PrincipalPlanes
import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.Core.OperatorBlocks
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.CourantFischer
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.KyFan
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SandwichMajorization

/-!
# Fan dominance for the finite direct rotation

This file supplies the missing mathematics behind Davis--Kahan Section 4.
The argument has two distinct parts.

* For every scalar field `RCLike 𝕜`, the positive displacement square of the
  canonical direct rotation is weakly majorized by that of every unitary
  carrying `U` onto `V`.  The proof writes the canonical intertwiner as the
  competitor times a two-block pinching, applies the Fan--Hoffman inequality
  `lambda_i (Re A) <= sigma_i A`, and then uses pinching contraction.

The historical full-displacement short-rotation claim is not part of this
module.  As stated for arbitrary orthogonal competitors it is false even over
`ℝ`: with two equal principal angles, a multiplicity-space rotation combines
one zero rotation and one `2θ` rotation and has smaller trace displacement than
the plane-by-plane direct rotation.  The sound replacement is the unrestricted
pointwise and UI-norm minimality of the restricted displacement `(I-W)P_U`,
proved in `DirectRotation.PrincipalPlanes`.

No fictional principal-plane namespace is assumed.  All spectral data are
obtained from the modulus of the canonical intertwiner and ordinary
finite-dimensional Courant--Fischer theory.
-/

namespace TauCeti
namespace DavisKahan.FiniteDimensional

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Hermitian part `(A + A star) / 2`. -/
noncomputable def hermitianPart (A : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  (((2 : ℝ)⁻¹ : ℝ) : 𝕜) • (A + A.adjoint)

/-- Positive displacement square `(I - W star)(I - W)`. -/
noncomputable def displacementSquare (W : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  (LinearMap.id - W.adjoint) ∘ₗ (LinearMap.id - W)

/-- The Hermitian part, unfolded to `(A + A⋆)/2`. -/
@[simp] theorem hermitianPart_apply (A : E →ₗ[𝕜] E) (x : E) :
    hermitianPart A x = (((2 : ℝ)⁻¹ : ℝ) : 𝕜) • (A x + A.adjoint x) := by
  simp [hermitianPart]

/-- The Hermitian part is symmetric -- the property its name claims. -/
theorem hermitianPart_isSymmetric (A : E →ₗ[𝕜] E) :
    (hermitianPart A).IsSymmetric := by
  intro x y
  simp only [hermitianPart_apply, inner_smul_left, inner_smul_right,
    RCLike.conj_ofReal, inner_add_left, inner_add_right,
    LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right]
  ring

/-- The Hermitian part has the same real quadratic form as the original operator; the skew part
contributes nothing to `re ⟪A x, x⟫`. -/
theorem re_inner_hermitianPart (A : E →ₗ[𝕜] E) (x : E) :
    RCLike.re ⟪hermitianPart A x, x⟫_𝕜 = RCLike.re ⟪A x, x⟫_𝕜 := by
  have hconj : RCLike.re ⟪x, A x⟫_𝕜 = RCLike.re ⟪A x, x⟫_𝕜 := by
    rw [← inner_conj_symm (A x) x, RCLike.conj_re]
  simp only [hermitianPart_apply, inner_smul_left, RCLike.conj_ofReal,
    inner_add_left, LinearMap.adjoint_inner_left, RCLike.re_ofReal_mul,
    map_add, hconj]
  ring

/-- The displacement square `(1 - W)⋆(1 - W)` is positive, being a Gram operator. -/
theorem displacementSquare_positive (W : E →ₗ[𝕜] E) :
    (displacementSquare W).IsPositive := by
  have h := LinearMap.isPositive_adjoint_comp_self (LinearMap.id - W)
  have he : LinearMap.adjoint (LinearMap.id - W) =
      LinearMap.id - W.adjoint := by
    rw [map_sub, LinearMap.adjoint_id]
  rwa [he] at h

/-- Its quadratic form is the squared displacement `‖W x - x‖²`, which is what makes it the right
object to minimise over rotations. -/
theorem displacementSquare_apply_inner (W : E →ₗ[𝕜] E) (x : E) :
    RCLike.re ⟪displacementSquare W x, x⟫_𝕜 = ‖W x - x‖ ^ 2 := by
  have he : (LinearMap.id : E →ₗ[𝕜] E) - W.adjoint =
      LinearMap.adjoint (LinearMap.id - W) := by
    rw [map_sub, LinearMap.adjoint_id]
  -- `congr 2` peels past the norm and leaves the false `x - W x = W x - x`
  simp only [displacementSquare, LinearMap.comp_apply, he,
    LinearMap.adjoint_inner_left, inner_self_eq_norm_sq,
    LinearMap.sub_apply, LinearMap.id_apply, norm_sub_rev]

/-- For a *unitary* `W` the displacement square collapses to `2(1 - Re W)`.  This is the identity
that converts the minimisation into a statement about the Hermitian part alone. -/
theorem displacementSquare_unitary (W : E ≃ₗᵢ[𝕜] E) :
    displacementSquare W.toLinearMap =
      (2 : 𝕜) • (LinearMap.id - hermitianPart W.toLinearMap) := by
  ext x
  -- the inverse only cancels once `W.symm` is distributed over the difference
  have hcancel : W.symm.toLinearMap (W.toLinearMap x) = x := W.symm_apply_apply x
  simp only [displacementSquare, hermitianPart, LinearMap.comp_apply,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_apply, W.adjoint_toLinearMap_eq_symm, map_sub, hcancel]
  -- the two sides carry `2` and `(2 : ℝ)⁻¹` as unrelated scalar atoms
  match_scalars <;> ring

omit [FiniteDimensional 𝕜 E] in
/-- A unitary carrying `U` onto `V` intertwines their orthogonal projections. -/
theorem projection_intertwines_of_map_eq
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    W.toLinearMap ∘ₗ projection U = projection V ∘ₗ W.toLinearMap := by
  apply LinearMap.ext
  intro x
  rw [← U.starProjection_add_starProjection_orthogonal x]
  have hU : W (U.starProjection x) ∈ V := by
    rw [← hmap]
    exact ⟨U.starProjection x, U.starProjection_apply_mem x, rfl⟩
  have hperp : W (Uᗮ.starProjection x) ∈ Vᗮ := by
    intro v hv
    rw [← hmap] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    simp only [LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe]
    rw [W.inner_map_map]
    exact Submodule.inner_right_of_mem_orthogonal hu
      (Uᗮ.starProjection_apply_mem x)
  -- the goal carries `W.toLinearEquiv`; the membership facts carry `W`
  simp only [LinearMap.comp_apply, map_add,
    LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe]
  simp only [projection_apply_of_mem hU, projection_apply_of_mem_orthogonal hperp,
    add_zero, projection_apply_of_mem (U.starProjection_apply_mem x),
    projection_apply_of_mem_orthogonal (Uᗮ.starProjection_apply_mem x),
    map_zero, add_zero]

/-- The adjoint intertwining relation. -/
theorem adjoint_projection_intertwines_of_map_eq
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    W.symm.toLinearMap ∘ₗ projection V = projection U ∘ₗ W.symm.toLinearMap := by
  have h := congrArg LinearMap.adjoint
    (projection_intertwines_of_map_eq U V W hmap)
  simpa [LinearMap.adjoint_comp, projection_adjoint,
    W.adjoint_toLinearMap_eq_symm] using h.symm

/-- Multiplying the canonical intertwiner by a competing unitary on the left
produces the diagonal pinching of the competitor's adjoint. -/
theorem symm_comp_canonicalIntertwiner_eq_pinch
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    W.symm.toLinearMap ∘ₗ canonicalIntertwiner U V =
      pinch U W.symm.toLinearMap := by
  have hstar := adjoint_projection_intertwines_of_map_eq U V W hmap
  have hstarPerp := adjoint_projection_intertwines_of_map_eq Uᗮ Vᗮ W (by
    rw [Submodule.map_orthogonal_equiv, hmap])
  ext x
  simp only [canonicalIntertwiner, pinch, LinearMap.comp_apply,
    LinearMap.add_apply, map_add,
    LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe]
  rw [show W.symm (projection V (projection U x)) =
      projection U (W.symm (projection U x)) by
        simpa [LinearMap.comp_apply] using
          LinearMap.congr_fun hstar (projection U x)]
  rw [show W.symm (complementaryProjection V (complementaryProjection U x)) =
      complementaryProjection U (W.symm (complementaryProjection U x)) by
        simpa [complementaryProjection, LinearMap.comp_apply] using
          LinearMap.congr_fun hstarPerp (complementaryProjection U x)]

/-- The modulus of the pinched competitor is the modulus of the canonical
intertwiner. -/
theorem abs_pinch_competitor_eq_abs_canonicalIntertwiner
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    TauCeti.operatorAbs (pinch U W.symm.toLinearMap) =
      TauCeti.operatorAbs (canonicalIntertwiner U V) := by
  have hfactor := symm_comp_canonicalIntertwiner_eq_pinch U V W hmap
  have hgram :
      (pinch U W.symm.toLinearMap).adjoint ∘ₗ pinch U W.symm.toLinearMap =
        (canonicalIntertwiner U V).adjoint ∘ₗ canonicalIntertwiner U V := by
    rw [← hfactor, LinearMap.adjoint_comp, W.symm.adjoint_toLinearMap_eq_symm,
      LinearIsometryEquiv.symm_symm]
    ext x
    -- the composite is `W (W.symm _)`, so the cancellation is `apply_symm_apply`
    simp only [LinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearEquiv.coe_coe, LinearIsometryEquiv.apply_symm_apply]
  have hsq : TauCeti.operatorAbs (pinch U W.symm.toLinearMap) ∘ₗ
      TauCeti.operatorAbs (pinch U W.symm.toLinearMap) =
      (canonicalIntertwiner U V).adjoint ∘ₗ canonicalIntertwiner U V := by
    rw [TauCeti.operatorAbs, LinearMap.IsPositive.sqrt_mul_self]
    exact hgram
  exact LinearMap.IsPositive.sqrt_unique
    (LinearMap.isPositive_adjoint_comp_self (canonicalIntertwiner U V))
    (TauCeti.isPositive_operatorAbs _) hsq
/-- Fan--Hoffman pointwise inequality: every sorted eigenvalue of the Hermitian
part is bounded by the corresponding singular value. -/
theorem eigenvalues_hermitianPart_le_singularValues
    (A : E →ₗ[𝕜] E) (i : Fin (finrank 𝕜 E)) :
    (hermitianPart_isSymmetric A).eigenvalues rfl i ≤
      A.singularValues (i : ℕ) := by
  classical
  let H := hermitianPart A
  let C := TauCeti.operatorAbs A
  -- Use the Gram eigenbasis throughout: `operatorAbs A` is *defined* through it, so
  -- staying in it avoids an expensive cross-basis defeq.
  let b := A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl
  let tail := b.spanIndices (Set.Ici i)
  obtain ⟨L, hLdim, hLlow⟩ :=
    LinearMap.IsSymmetric.exists_submodule_forall_unit_eigenvalue_le_re_inner
      (hermitianPart_isSymmetric A) rfl i
  have htaildim : finrank 𝕜 tail = finrank 𝕜 E - (i : ℕ) := by
    dsimp [tail]
    rw [b.finrank_spanIndices_set, ← Fin.card_Ici i]
    congr 1
    ext j
    simp
  have hinter : L ⊓ tail ≠ ⊥ := by
    intro hbot
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq L tail
    rw [hbot, finrank_bot, add_zero, hLdim, htaildim] at hdim
    have hle : finrank 𝕜 (L ⊔ tail : Submodule 𝕜 E) ≤ finrank 𝕜 E :=
      Submodule.finrank_le _
    omega
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinter
  let x := (((‖z‖⁻¹ : ℝ) : 𝕜) • z)
  have hxL : x ∈ L := L.smul_mem _ hz.1
  have hxtail : x ∈ tail := tail.smul_mem _ hz.2
  have hxnorm : ‖x‖ = 1 := by
    dsimp [x]
    rw [norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz0)]
  have hCbound : ‖C x‖ ≤ A.singularValues (i : ℕ) := by
    -- the Gram eigenvalues are exactly the squared singular values
    -- the bound has to be ascribed, or it stays a metavariable in the rewrite
    have hgram : RCLike.re ⟪(LinearMap.adjoint A ∘ₗ A) x, x⟫_𝕜 ≤
        A.singularValues (i : ℕ) ^ 2 * ‖x‖ ^ 2 :=
      LinearMap.IsSymmetric.re_inner_apply_self_le_of_mem_spanIndices
        A.isSymmetric_adjoint_comp_self rfl
        (fun j hj => by
          rw [← A.sq_singularValues_fin rfl j]
          exact pow_le_pow_left₀ (A.singularValues_nonneg _)
            (A.singularValues_antitone hj) 2)
        hxtail
    have hAx : ‖A x‖ ^ 2 = RCLike.re ⟪(LinearMap.adjoint A ∘ₗ A) x, x⟫_𝕜 := by
      rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left,
        ← norm_sq_eq_re_inner (𝕜 := 𝕜)]
    have hsq : ‖A x‖ ^ 2 ≤ A.singularValues (i : ℕ) ^ 2 := by
      rw [hAx]
      calc RCLike.re ⟪(LinearMap.adjoint A ∘ₗ A) x, x⟫_𝕜
          ≤ A.singularValues (i : ℕ) ^ 2 * ‖x‖ ^ 2 := hgram
        _ = A.singularValues (i : ℕ) ^ 2 := by rw [hxnorm, one_pow, mul_one]
    change ‖TauCeti.operatorAbs A x‖ ≤ A.singularValues (i : ℕ)
    rw [TauCeti.norm_operatorAbs_apply]
    nlinarith [norm_nonneg (A x), A.singularValues_nonneg (i : ℕ), hsq]
  calc
    (hermitianPart_isSymmetric A).eigenvalues rfl i
        ≤ RCLike.re ⟪H x, x⟫_𝕜 := hLlow x hxL hxnorm
    _ = RCLike.re ⟪A x, x⟫_𝕜 := re_inner_hermitianPart A x
    _ ≤ ‖A x‖ * ‖x‖ :=
      (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
    _ = ‖C x‖ := by rw [hxnorm, mul_one, norm_operatorAbs_apply]
    _ ≤ A.singularValues (i : ℕ) := hCbound

/-- Pinching relative to `U + U orthogonal` is a contraction for every
unitarily invariant norm. -/
theorem uiNorm_pinch_le
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : E →ₗ[𝕜] E) : N (pinch U A) ≤ N A := by
  have hpinch : (2 : 𝕜) • pinch U A =
      A + U.reflection.toLinearMap ∘ₗ A ∘ₗ U.reflection.toLinearMap := by
    ext x
    -- with `Q = I - P` the identity is linear in the remaining atoms, so no
    -- idempotence is needed and `module` can finish
    -- both sides have to reach the same atom: the left keeps `projection U`
    -- while the reflection expands to `U.starProjection`
    have hQ : ∀ y : E, Uᗮ.starProjection y = y - U.starProjection y :=
      fun y => eq_sub_of_add_eq'
        (Submodule.starProjection_add_starProjection_orthogonal (K := U) y)
    simp only [pinch, complementaryProjection, projection,
      ContinuousLinearMap.coe_coe, LinearMap.add_apply, LinearMap.comp_apply,
      hQ, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearEquiv.coe_coe, Submodule.reflection_apply, two_smul,
      map_add, map_sub]
    module
  have htri := N.add_le A
    (U.reflection.toLinearMap ∘ₗ A ∘ₗ U.reflection.toLinearMap)
  have hinv : N (U.reflection.toLinearMap ∘ₗ A ∘ₗ U.reflection.toLinearMap) = N A := by
    rw [N.invariant_left, N.invariant_right]
  rw [← hpinch, N.smul_eq, RCLike.norm_ofNat, hinv] at htri
  linarith



/-- The Hermitian part of a pinched unitary is a contraction in quadratic
form, so `I - Re(pinch W)` is positive. -/
theorem LinearMap.IsPositive.of_hermitianPart_contraction
    (W : E ≃ₗᵢ[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] :
    (LinearMap.id - hermitianPart (pinch U W.toLinearMap)).IsPositive := by
  -- `IsPositive` is a conjunction, so the quadratic-form part must be opened
  refine ⟨(LinearMap.IsSymmetric.id (𝕜 := 𝕜) (E := E)).sub
    (hermitianPart_isSymmetric _), fun x => ?_⟩
  -- every orthogonal projector is a contraction
  have hcon : ∀ (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (y : E),
      ‖K.starProjection y‖ ≤ ‖y‖ := by
    intro K _ y
    calc ‖K.starProjection y‖ ≤ ‖K.starProjection‖ * ‖y‖ :=
          K.starProjection.le_opNorm y
      _ ≤ 1 * ‖y‖ :=
          mul_le_mul_of_nonneg_right K.starProjection_norm_le (norm_nonneg y)
      _ = ‖y‖ := one_mul _
  have hpinch : ‖pinch U W.toLinearMap x‖ ≤ ‖x‖ := by
    -- the two blocks land in `U` and `Uᗮ`, so both cross terms vanish
    have horthP : ⟪U.starProjection (W (U.starProjection x)),
        Uᗮ.starProjection (W (Uᗮ.starProjection x))⟫_𝕜 = 0 :=
      Submodule.inner_right_of_mem_orthogonal
        (U.starProjection_apply_mem _) (Uᗮ.starProjection_apply_mem _)
    have hsplit : ⟪U.starProjection x, Uᗮ.starProjection x⟫_𝕜 = 0 :=
      Submodule.inner_right_of_mem_orthogonal
        (U.starProjection_apply_mem _) (Uᗮ.starProjection_apply_mem _)
    have hx : ‖x‖ * ‖x‖ =
        ‖U.starProjection x‖ * ‖U.starProjection x‖ +
          ‖Uᗮ.starProjection x‖ * ‖Uᗮ.starProjection x‖ := by
      conv_lhs =>
        rw [← Submodule.starProjection_add_starProjection_orthogonal (K := U) x]
      exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hsplit
    have hpe : pinch U W.toLinearMap x =
        U.starProjection (W (U.starProjection x)) +
          Uᗮ.starProjection (W (Uᗮ.starProjection x)) := rfl
    have h1 := hcon U (W (U.starProjection x))
    have h2 := hcon Uᗮ (W (Uᗮ.starProjection x))
    rw [W.norm_map] at h1 h2
    have hsq : ‖pinch U W.toLinearMap x‖ * ‖pinch U W.toLinearMap x‖ ≤
        ‖x‖ * ‖x‖ := by
      rw [hpe, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horthP,
        hx]
      have hn1 := norm_nonneg (U.starProjection (W (U.starProjection x)))
      have hn2 := norm_nonneg (Uᗮ.starProjection (W (Uᗮ.starProjection x)))
      nlinarith [hn1, hn2, h1, h2]
    nlinarith [norm_nonneg (pinch U W.toLinearMap x), norm_nonneg x, hsq]
  have hre : RCLike.re ⟪hermitianPart (pinch U W.toLinearMap) x, x⟫_𝕜 ≤ ‖x‖ ^ 2 := by
    rw [re_inner_hermitianPart, sq]
    exact (RCLike.re_le_norm _).trans
      ((norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right hpinch (norm_nonneg x)))
  rw [LinearMap.sub_apply, LinearMap.id_apply, inner_sub_left, map_sub,
    inner_self_eq_norm_sq]
  linarith

/-- Ky Fan sums contract under two-block pinching. -/
theorem kyFanSum_pinch_le
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : E →ₗ[𝕜] E) (k : ℕ) :
    kyFanSum k (pinch U A) ≤ kyFanSum k A := by
  have hpinch : (((2 : ℝ) : 𝕜)) • pinch U A =
      A + U.reflection.toLinearMap ∘ₗ A ∘ₗ U.reflection.toLinearMap := by
    ext x
    have hQ : ∀ y : E, Uᗮ.starProjection y = y - U.starProjection y :=
      fun y => eq_sub_of_add_eq'
        (Submodule.starProjection_add_starProjection_orthogonal (K := U) y)
    simp only [pinch, complementaryProjection, projection,
      ContinuousLinearMap.coe_coe, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, hQ, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearEquiv.coe_coe, Submodule.reflection_apply, two_smul,
      map_add, map_sub]
    push_cast
    module
  have htri := kyFanSum_add_le k A
    (U.reflection.toLinearMap ∘ₗ A ∘ₗ U.reflection.toLinearMap)
  rw [← hpinch, kyFanSum_real_smul k (pinch U A) (by norm_num),
    kyFanSum_unitary_comp, kyFanSum_comp_unitary] at htri
  linarith

/-- Invertibility makes every finite singular value strictly positive. -/
theorem singularValues_pos_of_isUnit
    {A : E →ₗ[𝕜] E} (hA : IsUnit A)
    (i : Fin (finrank 𝕜 E)) : 0 < A.singularValues (i : ℕ) := by
  rw [A.singularValues_pos_iff_lt_finrank_range]
  have hrange : A.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact LinearMap.injective_iff_surjective.mp
      (LinearMap.ker_eq_bot.mp ((LinearMap.isUnit_iff_ker_eq_bot _).mp hA))
  rw [hrange, finrank_top]
  exact i.isLt

/-- Ky Fan sums of a positive `A = 2(I-C)` are the reversed affine eigenvalue
sums of the symmetric operator `C`.  This packages the index reversal caused by
the decreasing map `t |-> 2(1-t)`: the `i`th largest eigenvalue of `A` is
`2(1 - lambda_{n-1-i}(C))`. -/
theorem positive_affine_reverse_kyFanSum
    {C A : E →ₗ[𝕜] E} (hA : A.IsPositive) (hC : C.IsSymmetric)
    (hAC : A = (2 : 𝕜) • (LinearMap.id - C))
    (k : ℕ) :
    kyFanSum k A =
      ∑ i : Fin (min k (finrank 𝕜 E)),
        2 * (1 - hC.eigenvalues rfl
          (Fin.rev (Fin.castLE (min_le_right k (finrank 𝕜 E)) i))) := by
  classical
  let n := finrank 𝕜 E
  let b := hC.eigenvectorBasis rfl
  let br : OrthonormalBasis (Fin n) 𝕜 E := b.reindex Fin.revPerm
  have heig : ∀ i : Fin n, A (br i) =
      (((2 * (1 - hC.eigenvalues rfl (Fin.rev i)) : ℝ)) : 𝕜) • br i := by
    intro i
    rw [hAC]
    simp [br, b, hC.apply_eigenvectorBasis]
    -- the left carries an `ℕ`-smul and the right a scalar-field one
    match_scalars
    ring
  have hanti : Antitone (fun i : Fin n =>
      2 * (1 - hC.eigenvalues rfl (Fin.rev i))) := by
    intro i j hij
    have hrev : Fin.rev j ≤ Fin.rev i := Fin.rev_le_rev.mpr hij
    have hlam := hC.eigenvalues_antitone rfl hrev
    linarith
  have hAeig := LinearMap.IsSymmetric.eigenvalues_eq_of_eigenbasis hA.isSymmetric rfl br hanti heig
  have hrange : kyFanSum k A
      = ∑ i ∈ Finset.range (min k (finrank 𝕜 E)), A.singularValues i := by
    rw [kyFanSum_eq_sum_range]
    refine (Finset.sum_subset
      (fun i hi => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hi) (min_le_left _ _)))
      fun i hik hi => ?_).symm
    have h1 := Finset.mem_range.mp hik
    have h2 : ¬ i < min k (finrank 𝕜 E) := fun h => hi (Finset.mem_range.mpr h)
    exact A.singularValues_of_finrank_le (by omega)
  have hfun : ∀ i : Fin (min k (finrank 𝕜 E)),
      A.singularValues (i : ℕ) =
        2 * (1 - hC.eigenvalues rfl
          (Fin.rev (Fin.castLE (min_le_right k (finrank 𝕜 E)) i))) := by
    intro i
    have hi : (i : ℕ) < finrank 𝕜 E := lt_of_lt_of_le i.isLt (min_le_right _ _)
    rw [show A.singularValues (i : ℕ) =
        hA.isSymmetric.eigenvalues rfl ⟨(i : ℕ), hi⟩ from
      singularValues_of_isPositive hA ⟨(i : ℕ), hi⟩, hAeig]
    exact rfl
  rw [hrange, ← Fin.sum_univ_eq_sum_range
    (fun i => A.singularValues i) (min k (finrank 𝕜 E))]
  exact Fintype.sum_congr _ _ hfun

/-!
The historical short-rotation corollary (a `pi / 3` largest-angle bound forcing
UI-norm minimality of the full displacement `I - W`) is intentionally absent:
it is false for arbitrary competitors carrying `U` onto `V` (see
the 2026-07-21 repair note (Git history); a competitor may mix an
equal-angle multiplicity space and beat the direct rotation in trace norm at
every angle).  The valid arbitrary-UI endpoint is the restricted-displacement
theorem `uiNorm_restrictedDisplacement_le`, which needs no largest-angle
threshold (only the standing `IsAcute`).
The spectral-floor lemma that fed the historical corollary also relied on the
two-projection identity `‖P_U - P_V‖ = sin theta_max`, which is not yet in the
tree; both were removed with the corollary since nothing else consumes them.
-/

/-- The Hermitian part of the direct rotation is the canonical modulus:
`Re R = |S|`, the operator cosine. -/
theorem hermitianPart_directRotation (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    hermitianPart (directRotation U V hacute).toLinearMap =
      TauCeti.operatorAbs (canonicalIntertwiner U V) := by
  have htwo := two_smul_abs_canonicalIntertwiner U V hacute
  apply LinearMap.ext
  intro x
  have htwox := LinearMap.congr_fun htwo x
  simp only [LinearMap.smul_apply, LinearMap.add_apply] at htwox
  rw [hermitianPart_apply,
    (directRotation U V hacute).adjoint_toLinearMap_eq_symm, ← htwox,
    smul_smul]
  have h12 : ((((2 : ℝ)⁻¹ : ℝ)) : 𝕜) * (2 : 𝕜) = 1 := by
    push_cast
    norm_num
  rw [h12, one_smul]

/-- The positive displacement square of the direct rotation is the affine
image `2(I - |S|)` of the operator cosine. -/
theorem displacementSquare_directRotation (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    displacementSquare (directRotation U V hacute).toLinearMap =
      (2 : 𝕜) • (LinearMap.id - TauCeti.operatorAbs (canonicalIntertwiner U V)) := by
  rw [displacementSquare_unitary, hermitianPart_directRotation]

/-- Weak majorization of the positive displacement squares.  This is the
operator-theoretic core of Davis--Kahan Proposition 4.3. -/
theorem directRotation_displacementSquare_kyFan
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (W : E ≃ₗᵢ[𝕜] E)
    (hmap : U.map W.toLinearMap = V) (k : ℕ) :
    kyFanSum k (displacementSquare (directRotation U V hacute).toLinearMap) ≤
      kyFanSum k (displacementSquare W.toLinearMap) := by
  classical
  let S := canonicalIntertwiner U V
  let C := TauCeti.operatorAbs S
  let B := pinch U W.symm.toLinearMap
  let H := hermitianPart B
  let A0 := displacementSquare (directRotation U V hacute).toLinearMap
  let A1 := displacementSquare W.toLinearMap
  let P1 := pinch U A1
  have hCeq : TauCeti.operatorAbs B = C := by
    simpa [B, C, S] using
      abs_pinch_competitor_eq_abs_canonicalIntertwiner U V W hmap
  have hA0 : A0 = (2 : 𝕜) • (LinearMap.id - C) := by
    simp only [A0]
    exact displacementSquare_directRotation U V hacute
  have hBadj : (pinch U W.symm.toLinearMap).adjoint = pinch U W.toLinearMap := by
    rw [pinch, pinch, map_add]
    simp only [LinearMap.adjoint_comp, projection_adjoint, complementaryProjection,
      W.symm.adjoint_toLinearMap_eq_symm, LinearIsometryEquiv.symm_symm,
      LinearMap.comp_assoc]
  have hpinch_add : ∀ M N : E →ₗ[𝕜] E,
      pinch U (M + N) = pinch U M + pinch U N := by
    intro M N
    apply LinearMap.ext
    intro x
    simp only [pinch, LinearMap.add_apply, LinearMap.comp_apply, map_add]
    abel
  have hpinch_sub : ∀ M N : E →ₗ[𝕜] E,
      pinch U (M - N) = pinch U M - pinch U N := by
    intro M N
    apply LinearMap.ext
    intro x
    simp only [pinch, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.comp_apply, map_sub]
    abel
  have hpinch_smul : ∀ (c : 𝕜) (M : E →ₗ[𝕜] E),
      pinch U (c • M) = c • pinch U M := by
    intro c M
    apply LinearMap.ext
    intro x
    simp only [pinch, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, map_smul, smul_add]
  have hpinch_id : pinch U (LinearMap.id : E →ₗ[𝕜] E) = LinearMap.id := by
    apply LinearMap.ext
    intro x
    simp only [pinch, complementaryProjection, LinearMap.add_apply,
      LinearMap.comp_apply, LinearMap.id_apply]
    have h1 : projection U (projection U x) = projection U x :=
      projection_apply_of_mem (U.starProjection_apply_mem x)
    have h2 : projection Uᗮ (projection Uᗮ x) = projection Uᗮ x :=
      projection_apply_of_mem (Uᗮ.starProjection_apply_mem x)
    rw [h1, h2]
    exact U.starProjection_add_starProjection_orthogonal x
  have hP1 : P1 = (2 : 𝕜) • (LinearMap.id - H) := by
    have hA1' : A1 = (2 : 𝕜) • (LinearMap.id - hermitianPart W.toLinearMap) := by
      simp only [A1]
      rw [displacementSquare_unitary]
    have hW2 : hermitianPart W.toLinearMap =
        (((2 : ℝ)⁻¹ : ℝ) : 𝕜) • (W.toLinearMap + W.symm.toLinearMap) := by
      simp only [hermitianPart, W.adjoint_toLinearMap_eq_symm]
    have hHalf : H = (((2 : ℝ)⁻¹ : ℝ) : 𝕜) •
        (pinch U W.symm.toLinearMap + pinch U W.toLinearMap) := by
      simp only [H, B, hermitianPart, hBadj]
    simp only [P1]
    -- `hpinch_smul` appeared twice in the `rw` chain this replaced, once per
    -- occurrence; `simp only` reaches both in one pass.
    simp only [hA1', hpinch_smul, hpinch_sub, hpinch_id, hW2,
      hpinch_add, hHalf, add_comm (pinch U W.toLinearMap)]
  have hpositive0 : A0.IsPositive := displacementSquare_positive _
  have hA1pos : A1.IsPositive := displacementSquare_positive W.toLinearMap
  have hpositiveP : P1.IsPositive := by
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · simp only [P1, pinch, complementaryProjection, LinearMap.add_apply,
        LinearMap.comp_apply, inner_add_left, inner_add_right,
        projection_inner_left_eq_right]
      rw [hA1pos.isSymmetric (projection U x),
        hA1pos.isSymmetric (projection Uᗮ x),
        projection_inner_left_eq_right, projection_inner_left_eq_right]
    · simp only [P1, pinch, complementaryProjection, LinearMap.add_apply,
        LinearMap.comp_apply, inner_add_left, map_add,
        projection_inner_left_eq_right]
      exact add_nonneg (hA1pos.re_inner_nonneg_left _)
        (hA1pos.re_inner_nonneg_left _)
  have hprefix : ∀ j, kyFanSum j A0 ≤ kyFanSum j P1 := by
    intro j
    -- Diagonalize `C` and `H`.  The Fan--Hoffman inequality gives
    -- `lambda_i(H) <= lambda_i(C) = sigma_i(B)`.  Applying the decreasing
    -- affine map `t |-> 2(1-t)` reverses the index order, and summing the
    -- largest `j` transformed eigenvalues gives the desired prefix bound.
    have hlam : ∀ i : Fin (finrank 𝕜 E),
        (hermitianPart_isSymmetric B).eigenvalues rfl i ≤
          (isPositive_operatorAbs B).isSymmetric.eigenvalues rfl i := by
      intro i
      rw [congrFun (eigenvalues_operatorAbs B) i]
      exact eigenvalues_hermitianPart_le_singularValues B i
    have hA0eig := positive_affine_reverse_kyFanSum
      hpositive0 (isPositive_operatorAbs B).isSymmetric (by rw [hA0, hCeq]) j
    have hP1eig := positive_affine_reverse_kyFanSum
      hpositiveP (hermitianPart_isSymmetric B) hP1 j
    rw [hA0eig, hP1eig]
    exact Finset.sum_le_sum fun i _ => by
      have hi := hlam (Fin.rev (Fin.castLE (min_le_right j (finrank 𝕜 E)) i))
      linarith
  exact (hprefix k).trans (kyFanSum_pinch_le U A1 k)

/-- Every UI norm inherits the squared-displacement extremum. -/
theorem directRotation_displacementSquare_uiNorm
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (W : E ≃ₗᵢ[𝕜] E)
    (hmap : U.map W.toLinearMap = V) :
    N (displacementSquare (directRotation U V hacute).toLinearMap) ≤
      N (displacementSquare W.toLinearMap) :=
  N.apply_le_of_kyFanSum_le
    (directRotation_displacementSquare_kyFan U V hacute W hmap)

/-!
The corresponding full-displacement theorem is intentionally absent.  The
valid arbitrary-UI endpoint is `uiNorm_restrictedDisplacement_le`.
-/

end DavisKahan.FiniteDimensional
end TauCeti
