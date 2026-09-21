/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Fable 5
-/
import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.DirectRotation.Basic
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Singular.System

/-!
# Principal planes of an acute pair: definitions and rotation block

This file constructs the finite principal planes used in Davis--Kahan Section 4
without assuming a `FiniteTwoProjection` API.  The source vectors are the
nonzero right singular vectors of the directed sine block `P_{V orthogonal} P_U`;
with `s_i` the corresponding singular value, `c_i = sqrt (1-s_i^2)` and
`j_i = s_i^{-1} (R u_i - c_i u_i)`.  The family `(u_i, j_i)` is orthonormal, the
sines decrease and the cosines increase, and the direct rotation `R` acts on
each principal plane by the `2 x 2` block `[[c, -s], [s, c]]`.

This is the first of three topic modules split out of the former monolithic
`PrincipalPlanes.lean`; see also `PrincipalPlanes.Spectrum` (vanishing
directions and the spectrum of `I - R`) and `PrincipalPlanes.Variational`
(Davis's variational theorem for the restricted displacement).
-/

namespace TauCeti
namespace DavisKahan.FiniteDimensional

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The number of nonzero directed principal sines. -/
noncomputable def nontrivialAngleCount (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℕ :=
  finrank 𝕜 (sinThetaMap U V).range

/-- Cast a nontrivial-angle index into the ambient right singular basis. -/
noncomputable def nontrivialAngleIndex (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (i : Fin (nontrivialAngleCount U V)) : Fin (finrank 𝕜 E) :=
  Fin.castLE (LinearMap.finrank_range_le (sinThetaMap U V)) i

/-- Source principal vector. -/
noncomputable def principalSourceVector (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (i : Fin (nontrivialAngleCount U V)) : E :=
  rightSingularBasis (sinThetaMap U V) (nontrivialAngleIndex U V i)

/-- Sine attached to a nontrivial principal plane. -/
noncomputable def principalPlaneSine (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (i : Fin (nontrivialAngleCount U V)) : ℝ :=
  (sinThetaMap U V).singularValues (nontrivialAngleIndex U V i)

/-- Cosine attached to a nontrivial principal plane. -/
noncomputable def principalPlaneCosine (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (i : Fin (nontrivialAngleCount U V)) : ℝ :=
  Real.sqrt (1 - principalPlaneSine U V i ^ 2)

/-- Chord length `2 sin(theta_i/2)`. -/
noncomputable def principalPlaneChord (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (i : Fin (nontrivialAngleCount U V)) : ℝ :=
  Real.sqrt (2 * (1 - principalPlaneCosine U V i))

/-- **The chord is twice the sine of the half-angle**, which is what the name says
and what Davis--Kahan write.

This API carries a principal plane by its sine and cosine rather than by an angle,
so `principalPlaneChord` is defined as `√(2(1 - cos θ))`. Proposition 4.1 states
the minimal singular value as `2 sin(θ_k / 2)`. The two agree by the half-angle
identity, and this is that agreement: for any `θ` in `[0, π]` realising the
plane's sine and cosine, the chord is `2 sin(θ / 2)`.

Without it the identification of the compiled value with the printed one rests on
a docstring. -/
theorem principalPlaneChord_eq_two_mul_sin_half (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (i : Fin (nontrivialAngleCount U V)) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (hcos : Real.cos θ = principalPlaneCosine U V i) :
    principalPlaneChord U V i = 2 * Real.sin (θ / 2) := by
  have hpi : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  rw [Real.sin_half_eq_sqrt hθ0 (by linarith), hcos, principalPlaneChord]
  rw [show (2 : ℝ) * (1 - principalPlaneCosine U V i)
      = 2 ^ 2 * ((1 - principalPlaneCosine U V i) / 2) by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]

/-- The source-orthogonal partner of a principal source vector. -/
noncomputable def principalOrthogonalVector (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) : E :=
  (((principalPlaneSine U V i)⁻¹ : ℝ) : 𝕜) •
    (directRotation U V hacute (principalSourceVector U V i) -
      (principalPlaneCosine U V i : 𝕜) • principalSourceVector U V i)

/-- Nonzero singular values are strictly positive on the range-rank prefix. -/
theorem principalPlaneSine_pos
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (i : Fin (nontrivialAngleCount U V)) :
    0 < principalPlaneSine U V i := by
  rw [principalPlaneSine]
  exact (sinThetaMap U V).singularValues_pos_iff_lt_finrank_range.mpr i.isLt

/-- Directed principal sines are at most one. -/
theorem principalPlaneSine_le_one
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (i : Fin (nontrivialAngleCount U V)) :
    principalPlaneSine U V i ≤ 1 := by
  rw [principalPlaneSine]
  refine singularValues_le_one_of_contraction ?_ rfl (nontrivialAngleIndex U V i)
  intro x
  have h1 : ‖sinThetaMap U V x‖ ≤ ‖projection U x‖ :=
    Vᗮ.norm_starProjection_apply_le (projection U x)
  exact h1.trans (U.norm_starProjection_apply_le x)

/-- The source singular vector belongs to `U`. -/
theorem principalSourceVector_mem
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (_hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    principalSourceVector U V i ∈ U := by
  let A := sinThetaMap U V
  let p := nontrivialAngleIndex U V i
  let s := principalPlaneSine U V i
  have hs : s ≠ 0 := ne_of_gt (principalPlaneSine_pos U V i)
  have heig := adjointCompSelf_apply_rightSingularBasis A p
  have hUidem : ∀ y : E, projection U (projection U y) = projection U y := fun y =>
    Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem y)
  have hcVidem : ∀ y : E, complementaryProjection V (complementaryProjection V y)
      = complementaryProjection V y := fun y =>
    Submodule.starProjection_eq_self_iff.mpr (Vᗮ.starProjection_apply_mem y)
  have hcV : ∀ y : E, complementaryProjection V y = y - projection V y := fun y =>
    Submodule.starProjection_orthogonal_val y
  have hgram : A.adjoint ∘ₗ A =
      projection U - projection U ∘ₗ projection V ∘ₗ projection U := by
    have hAadj : A.adjoint = projection U ∘ₗ complementaryProjection V := by
      show (complementaryProjection V ∘ₗ projection U).adjoint
          = projection U ∘ₗ complementaryProjection V
      rw [LinearMap.adjoint_comp, projection_adjoint]
      congr 1
      simp [complementaryProjection]
    rw [hAadj]
    show (projection U ∘ₗ complementaryProjection V) ∘ₗ
        (complementaryProjection V ∘ₗ projection U) =
        projection U - projection U ∘ₗ projection V ∘ₗ projection U
    ext x
    simp only [LinearMap.comp_apply, LinearMap.sub_apply]
    rw [hcVidem (projection U x), hcV (projection U x), map_sub, hUidem x]
  rw [hgram] at heig
  simp only [LinearMap.sub_apply, LinearMap.comp_apply] at heig
  have hproj : projection U (principalSourceVector U V i) =
      principalSourceVector U V i := by
    have hc : ((s ^ 2 : ℝ) : 𝕜) ≠ 0 :=
      RCLike.ofReal_ne_zero.mpr (pow_ne_zero 2 hs)
    have key := congrArg (projection U) heig
    simp only [map_sub, map_smul, hUidem] at key
    rw [heig] at key
    exact (smul_right_injective E hc key).symm
  exact Submodule.starProjection_eq_self_iff.mp hproj

/-- The source principal vectors are orthonormal. -/
theorem orthonormal_principalSourceVector
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Orthonormal 𝕜 (principalSourceVector U V) := by
  exact (rightSingularBasis (sinThetaMap U V)).orthonormal.comp
    (nontrivialAngleIndex U V)
    (Fin.castLE_injective (LinearMap.finrank_range_le (sinThetaMap U V)))

/-- The source cosine has the expected Pythagorean identity. -/
theorem principalPlaneCosine_sq_add_sine_sq
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (i : Fin (nontrivialAngleCount U V)) :
    principalPlaneCosine U V i ^ 2 + principalPlaneSine U V i ^ 2 = 1 := by
  rw [principalPlaneCosine, Real.sq_sqrt]
  · ring
  · nlinarith [principalPlaneSine_pos U V i,
      principalPlaneSine_le_one U V i]

/-- Principal cosines are at most one. -/
theorem principalPlaneCosine_le_one
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (i : Fin (nontrivialAngleCount U V)) :
    principalPlaneCosine U V i ≤ 1 := by
  -- `principalPlaneCosine` is a function, not a fact; passing it as a hint
  -- leaves `nlinarith` with an unresolvable instance metavariable
  nlinarith [principalPlaneCosine_sq_add_sine_sq U V i,
    principalPlaneSine_pos U V i, Real.sqrt_nonneg (1 - principalPlaneSine U V i ^ 2),
    sq_nonneg (principalPlaneCosine U V i - 1),
    sq_nonneg (principalPlaneCosine U V i + 1)]

/-- Acuteness makes every principal-plane cosine strictly positive. -/
theorem principalPlaneCosine_pos
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    0 < principalPlaneCosine U V i := by
  rw [principalPlaneCosine, Real.sqrt_pos]
  have hu := principalSourceVector_mem U V hacute i
  have hnot : principalPlaneSine U V i ≠ 1 := by
    intro hs
    let u := principalSourceVector U V i
    have hu1 : ‖u‖ = 1 := (orthonormal_principalSourceVector U V).norm_eq_one i
    have hnorm := norm_apply_rightSingularBasis
      (sinThetaMap U V) (nontrivialAngleIndex U V i)
    have hzero : projection V u = 0 := by
      have hdecomp := Submodule.norm_sq_eq_add_norm_sq_starProjection u V
      have hsinNorm : ‖Vᗮ.starProjection u‖ = 1 := by
        have h : ‖sinThetaMap U V u‖ = principalPlaneSine U V i := hnorm
        rw [hs] at h
        rwa [sinThetaMap, LinearMap.comp_apply, projection_apply_of_mem hu] at h
      rw [hu1, hsinNorm] at hdecomp
      have hVsq : ‖V.starProjection u‖ ^ 2 = 0 := by nlinarith
      show V.starProjection u = 0
      exact norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num)).mp hVsq)
    exact (by
      have := hacute.1 u hu hzero
      exact one_ne_zero (hu1.symm.trans (by rw [this, norm_zero])))
  have hlt : principalPlaneSine U V i < 1 :=
    lt_of_le_of_ne (principalPlaneSine_le_one U V i) hnot
  nlinarith [principalPlaneSine_pos U V i, hlt]

/-- The positive modulus of the canonical intertwiner acts by the principal
cosine on the source vector. -/
theorem abs_canonicalIntertwiner_apply_principalSourceVector
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    TauCeti.operatorAbs (canonicalIntertwiner U V) (principalSourceVector U V i) =
      (principalPlaneCosine U V i : 𝕜) • principalSourceVector U V i := by
  have hu := principalSourceVector_mem U V hacute i
  have heig := adjointCompSelf_apply_rightSingularBasis (sinThetaMap U V)
    (nontrivialAngleIndex U V i)
  have hProjUu : projection U (principalSourceVector U V i) =
      principalSourceVector U V i := Submodule.starProjection_eq_self_iff.mpr hu
  have hcompUu : complementaryProjection U (principalSourceVector U V i) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff Uᗮ).mpr
      (U.le_orthogonal_orthogonal hu)
  have hUidem : ∀ y : E, projection U (projection U y) = projection U y := fun y =>
    Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem y)
  have hcVidem : ∀ y : E, complementaryProjection V (complementaryProjection V y)
      = complementaryProjection V y := fun y =>
    Submodule.starProjection_eq_self_iff.mpr (Vᗮ.starProjection_apply_mem y)
  have hcV : ∀ y : E, complementaryProjection V y = y - projection V y := fun y =>
    Submodule.starProjection_orthogonal_val y
  have hAgram : (sinThetaMap U V).adjoint ∘ₗ sinThetaMap U V =
      projection U - projection U ∘ₗ projection V ∘ₗ projection U := by
    have hAadj : (sinThetaMap U V).adjoint = projection U ∘ₗ complementaryProjection V := by
      rw [sinThetaMap, LinearMap.adjoint_comp, projection_adjoint]
      congr 1
      simp [complementaryProjection]
    rw [hAadj, sinThetaMap]
    ext x
    simp only [LinearMap.comp_apply, LinearMap.sub_apply]
    rw [hcVidem (projection U x), hcV (projection U x), map_sub, hUidem x]
  have hSu : ((canonicalIntertwiner U V).adjoint ∘ₗ canonicalIntertwiner U V)
        (principalSourceVector U V i) =
      projection U (projection V (principalSourceVector U V i)) := by
    rw [canonicalIntertwiner_adjoint_comp_self]
    simp only [LinearMap.add_apply, LinearMap.comp_apply, hProjUu, hcompUu,
      map_zero, add_zero]
  have hAu : ((sinThetaMap U V).adjoint ∘ₗ sinThetaMap U V)
        (principalSourceVector U V i) =
      principalSourceVector U V i -
        projection U (projection V (principalSourceVector U V i)) := by
    rw [hAgram]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, hProjUu]
  rw [show rightSingularBasis (sinThetaMap U V) (nontrivialAngleIndex U V i) =
    principalSourceVector U V i from rfl, hAu] at heig
  have hc0 : (0 : ℝ) ≤ principalPlaneCosine U V i := Real.sqrt_nonneg _
  have hsq : ((canonicalIntertwiner U V).adjoint ∘ₗ canonicalIntertwiner U V)
        (principalSourceVector U V i) =
      ((principalPlaneCosine U V i ^ 2 : ℝ) : 𝕜) • principalSourceVector U V i := by
    rw [hSu]
    have hcossq : (principalPlaneCosine U V i ^ 2 : ℝ) =
        1 - (sinThetaMap U V).singularValues (nontrivialAngleIndex U V i : ℕ) ^ 2 := by
      have hp := principalPlaneCosine_sq_add_sine_sq U V i
      simp only [principalPlaneSine] at hp
      linarith
    rw [hcossq, RCLike.ofReal_sub, RCLike.ofReal_one, sub_smul, one_smul, ← heig]
    abel
  have hpos := LinearMap.isPositive_adjoint_comp_self (canonicalIntertwiner U V)
  have hfc := TauCeti.selfAdjointFunctionalCalculus_apply_of_apply_eq_smul
    hpos.isSymmetric Real.sqrt hsq
  rw [TauCeti.selfAdjointFunctionalCalculus_sqrt hpos,
    Real.sqrt_sq hc0] at hfc
  exact hfc

/-- Every principal-plane cosine occurs in the singular-value multiset of the
canonical intertwiner.  The index is not the original sine index: principal
sines decrease while their complementary cosines increase. -/
theorem exists_canonicalIntertwiner_singularValue_eq_principalPlaneCosine
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    ∃ j : Fin (finrank 𝕜 E),
      (canonicalIntertwiner U V).singularValues (j : ℕ) =
        principalPlaneCosine U V i := by
  have hu1 : ‖principalSourceVector U V i‖ = 1 :=
    (orthonormal_principalSourceVector U V).norm_eq_one i
  have heigAbs := abs_canonicalIntertwiner_apply_principalSourceVector U V hacute i
  have hev : Module.End.HasEigenvalue (TauCeti.operatorAbs (canonicalIntertwiner U V))
      ((principalPlaneCosine U V i : ℝ) : 𝕜) := by
    apply Module.End.hasEigenvalue_of_hasEigenvector
      (x := principalSourceVector U V i)
    refine ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]; exact heigAbs
    · exact fun h => by simp [h] at hu1
  obtain ⟨j, hj⟩ :=
    (isPositive_operatorAbs (canonicalIntertwiner U V)).isSymmetric.exists_eigenvalues_eq rfl hev
  refine ⟨j, ?_⟩
  have hj' : (isPositive_operatorAbs (canonicalIntertwiner U V)).isSymmetric.eigenvalues rfl j
      = principalPlaneCosine U V i := by exact_mod_cast hj
  rw [← congrFun (eigenvalues_operatorAbs (canonicalIntertwiner U V)) j]
  exact hj'

/-- The direct rotation has the canonical cosine-sine action on a source
principal vector. -/
theorem directRotation_apply_principalSourceVector
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    directRotation U V hacute (principalSourceVector U V i) =
      (principalPlaneCosine U V i : 𝕜) • principalSourceVector U V i +
        (principalPlaneSine U V i : 𝕜) •
          principalOrthogonalVector U V hacute i := by
  rw [principalOrthogonalVector, smul_smul, ← RCLike.ofReal_mul,
    mul_inv_cancel₀ (ne_of_gt (principalPlaneSine_pos U V i)),
    RCLike.ofReal_one, one_smul]
  abel

/-- The orthogonal partner belongs to `U orthogonal`. -/
theorem principalOrthogonalVector_mem
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    principalOrthogonalVector U V hacute i ∈ Uᗮ := by
  rw [Submodule.mem_orthogonal']
  intro x hx
  have hu := principalSourceVector_mem U V hacute i
  have hcpos := principalPlaneCosine_pos U V hacute i
  have hcne : (principalPlaneCosine U V i : 𝕜) ≠ 0 := by exact_mod_cast ne_of_gt hcpos
  have hC := abs_canonicalIntertwiner_apply_principalSourceVector U V hacute i
  have hcompUu : complementaryProjection U (principalSourceVector U V i) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff Uᗮ).mpr
      (U.le_orthogonal_orthogonal hu)
  have hSpsv : canonicalIntertwiner U V (principalSourceVector U V i) =
      projection V (principalSourceVector U V i) := by
    simp only [canonicalIntertwiner, LinearMap.add_apply, LinearMap.comp_apply,
      projection_apply_of_mem hu, hcompUu, map_zero, add_zero]
  have hprojUprojV : projection U (projection V (principalSourceVector U V i)) =
      ((principalPlaneCosine U V i ^ 2 : ℝ) : 𝕜) • principalSourceVector U V i := by
    have h1 : ((canonicalIntertwiner U V).adjoint ∘ₗ canonicalIntertwiner U V)
          (principalSourceVector U V i) =
        projection U (projection V (principalSourceVector U V i)) := by
      rw [canonicalIntertwiner_adjoint_comp_self]
      simp only [LinearMap.add_apply, LinearMap.comp_apply,
        projection_apply_of_mem hu, hcompUu, map_zero, add_zero]
    have h2 : ((canonicalIntertwiner U V).adjoint ∘ₗ canonicalIntertwiner U V)
          (principalSourceVector U V i) =
        ((principalPlaneCosine U V i ^ 2 : ℝ) : 𝕜) • principalSourceVector U V i := by
      -- Left as a `rw` chain on purpose: `simp only` with this same list leaves the goal unsolved:
      -- at least one lemma here has to fire at one occurrence, in order, and simp's normal form
      -- loses the intermediate shape.
      rw [← operatorAbs_mul_self, LinearMap.comp_apply, hC, map_smul, hC, smul_smul,
        ← RCLike.ofReal_mul, ← sq]
    rw [← h1, h2]
  have hpolar : canonicalIntertwiner U V =
      (directRotation U V hacute).toLinearMap ∘ₗ
        TauCeti.operatorAbs (canonicalIntertwiner U V) := by
    rw [directRotation_toLinearMap]; exact polar_decomposition (canonicalIntertwiner U V)
  have hWpsv : projection V (principalSourceVector U V i) =
      (principalPlaneCosine U V i : 𝕜) •
        directRotation U V hacute (principalSourceVector U V i) := by
    have h := LinearMap.congr_fun hpolar (principalSourceVector U V i)
    simp only [LinearMap.comp_apply] at h
    rw [hC, map_smul, hSpsv] at h
    exact h
  have hdiag : projection U
      (directRotation U V hacute (principalSourceVector U V i)) =
      (principalPlaneCosine U V i : 𝕜) • principalSourceVector U V i := by
    have key := congrArg (projection U) hWpsv
    rw [map_smul, hprojUprojV] at key
    have key2 : (principalPlaneCosine U V i : 𝕜) •
          projection U (directRotation U V hacute (principalSourceVector U V i)) =
        (principalPlaneCosine U V i : 𝕜) •
          ((principalPlaneCosine U V i : 𝕜) • principalSourceVector U V i) := by
      rw [← key, smul_smul, ← RCLike.ofReal_mul, ← sq]
    exact smul_right_injective E hcne key2
  rw [principalOrthogonalVector, inner_smul_left, inner_sub_left, inner_smul_left,
    RCLike.conj_ofReal, RCLike.conj_ofReal]
  have hkey : ⟪directRotation U V hacute (principalSourceVector U V i), x⟫_𝕜 =
      (principalPlaneCosine U V i : 𝕜) * ⟪principalSourceVector U V i, x⟫_𝕜 := by
    have hx' : projection U x = x := projection_apply_of_mem hx
    calc ⟪directRotation U V hacute (principalSourceVector U V i), x⟫_𝕜
        = ⟪directRotation U V hacute (principalSourceVector U V i),
            projection U x⟫_𝕜 := by rw [hx']
      _ = ⟪projection U (directRotation U V hacute (principalSourceVector U V i)),
            x⟫_𝕜 := (projection_inner_left_eq_right U _ x).symm
      _ = ⟪(principalPlaneCosine U V i : 𝕜) • principalSourceVector U V i, x⟫_𝕜 := by
            rw [hdiag]
      _ = (principalPlaneCosine U V i : 𝕜) * ⟪principalSourceVector U V i, x⟫_𝕜 := by
            rw [inner_smul_left, RCLike.conj_ofReal]
  rw [hkey]; ring

/-- The `V`-projection of a principal source vector is the cosine multiple of
its direct-rotation image. -/
theorem projection_apply_principalSourceVector
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    projection V (principalSourceVector U V i) =
      (principalPlaneCosine U V i : 𝕜) •
        directRotation U V hacute (principalSourceVector U V i) := by
  have hu := principalSourceVector_mem U V hacute i
  have hC := abs_canonicalIntertwiner_apply_principalSourceVector U V hacute i
  have hcompUu : complementaryProjection U (principalSourceVector U V i) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff Uᗮ).mpr
      (U.le_orthogonal_orthogonal hu)
  have hSpsv : canonicalIntertwiner U V (principalSourceVector U V i) =
      projection V (principalSourceVector U V i) := by
    simp only [canonicalIntertwiner, LinearMap.add_apply, LinearMap.comp_apply,
      projection_apply_of_mem hu, hcompUu, map_zero, add_zero]
  have hpolar : canonicalIntertwiner U V =
      (directRotation U V hacute).toLinearMap ∘ₗ
        TauCeti.operatorAbs (canonicalIntertwiner U V) := by
    rw [directRotation_toLinearMap]; exact polar_decomposition (canonicalIntertwiner U V)
  have h := LinearMap.congr_fun hpolar (principalSourceVector U V i)
  simp only [LinearMap.comp_apply] at h
  rw [hC, map_smul, hSpsv] at h
  exact h

/-- The `U`-projection of the rotated source vector. -/
theorem projection_apply_directRotation_principalSourceVector
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    projection U (directRotation U V hacute (principalSourceVector U V i)) =
      (principalPlaneCosine U V i : 𝕜) • principalSourceVector U V i := by
  simp only [directRotation_apply_principalSourceVector U V hacute i, map_add, map_smul, map_smul,
    projection_apply_of_mem (principalSourceVector_mem U V hacute i),
    projection_apply_of_mem_orthogonal (principalOrthogonalVector_mem U V hacute i),
    smul_zero, add_zero]

/-- Principal orthogonal partners are orthonormal. -/
theorem orthonormal_principalOrthogonalVector
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    Orthonormal 𝕜 (principalOrthogonalVector U V hacute) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hu := orthonormal_iff_ite.mp (orthonormal_principalSourceVector U V) i j
  have hsi : principalPlaneSine U V i ≠ 0 := ne_of_gt (principalPlaneSine_pos U V i)
  have hsj : principalPlaneSine U V j ≠ 0 := ne_of_gt (principalPlaneSine_pos U V j)
  -- `⟪R uₐ, u_b⟫ = cₐ ⟪uₐ, u_b⟫` because the `U`-component of `R uₐ` is `cₐ uₐ`.
  have hdiag : ∀ a b : Fin (nontrivialAngleCount U V),
      ⟪directRotation U V hacute (principalSourceVector U V a),
        principalSourceVector U V b⟫_𝕜 =
      (principalPlaneCosine U V a : 𝕜) *
        ⟪principalSourceVector U V a, principalSourceVector U V b⟫_𝕜 := by
    intro a b
    calc ⟪directRotation U V hacute (principalSourceVector U V a),
          principalSourceVector U V b⟫_𝕜
        = ⟪directRotation U V hacute (principalSourceVector U V a),
            projection U (principalSourceVector U V b)⟫_𝕜 := by
          rw [projection_apply_of_mem (principalSourceVector_mem U V hacute b)]
      _ = ⟪projection U (directRotation U V hacute (principalSourceVector U V a)),
            principalSourceVector U V b⟫_𝕜 :=
          (projection_inner_left_eq_right U _ _).symm
      _ = _ := by
          rw [projection_apply_directRotation_principalSourceVector U V hacute a,
            inner_smul_left, RCLike.conj_ofReal]
  have hdiag' : ∀ a b : Fin (nontrivialAngleCount U V),
      ⟪principalSourceVector U V a,
        directRotation U V hacute (principalSourceVector U V b)⟫_𝕜 =
      (principalPlaneCosine U V b : 𝕜) *
        ⟪principalSourceVector U V a, principalSourceVector U V b⟫_𝕜 := by
    intro a b
    -- this chain already closes the goal by reflexivity
    rw [← inner_conj_symm, hdiag b a, map_mul, RCLike.conj_ofReal, inner_conj_symm]
  have hRR : ⟪directRotation U V hacute (principalSourceVector U V i),
      directRotation U V hacute (principalSourceVector U V j)⟫_𝕜 =
      ⟪principalSourceVector U V i, principalSourceVector U V j⟫_𝕜 :=
    (directRotation U V hacute).inner_map_map _ _
  simp only [principalOrthogonalVector, principalOrthogonalVector, inner_smul_left,
    inner_smul_right, RCLike.conj_ofReal, inner_sub_left, inner_sub_right,
    inner_sub_right, inner_smul_left, inner_smul_right, inner_smul_left,
    inner_smul_right, RCLike.conj_ofReal, hRR, hdiag i j,
    hdiag' i j, hu]
  split_ifs with hij
  · subst hij
    -- the surviving goal lives in `𝕜`; transport the Pythagorean identity
    -- across the cast and clear the nonzero sine
    have hpythK : ((principalPlaneCosine U V i : ℝ) : 𝕜) ^ 2 +
        ((principalPlaneSine U V i : ℝ) : 𝕜) ^ 2 = 1 := by
      have h := congrArg (fun r : ℝ => (r : 𝕜))
        (principalPlaneCosine_sq_add_sine_sq U V i)
      push_cast at h
      exact h
    have hsK : ((principalPlaneSine U V i : ℝ) : 𝕜) ≠ 0 :=
      RCLike.ofReal_ne_zero.mpr hsi
    push_cast
    field_simp
    linear_combination -hpythK
  · simp [mul_comm]

/-- The two vectors in distinct principal planes are mutually orthogonal. -/
theorem orthonormal_principalPlaneFamily
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    Orthonormal 𝕜 (fun p : Fin (nontrivialAngleCount U V) × Fin 2 =>
      if p.2 = 0 then principalSourceVector U V p.1
      else principalOrthogonalVector U V hacute p.1) := by
  rw [orthonormal_iff_ite]
  rintro ⟨p1, p2⟩ ⟨q1, q2⟩
  fin_cases p2 <;> fin_cases q2
  · simpa [Prod.ext_iff] using
      orthonormal_iff_ite.mp (orthonormal_principalSourceVector U V) p1 q1
  · have hp := principalSourceVector_mem U V hacute p1
    have hq := principalOrthogonalVector_mem U V hacute q1
    simp [Submodule.inner_right_of_mem_orthogonal hp hq, Prod.ext_iff]
  · have hp := principalOrthogonalVector_mem U V hacute p1
    have hq := principalSourceVector_mem U V hacute q1
    -- `fin_cases` leaves the index unreduced, so the `if` cannot be rewritten
    -- directly; discharge the inner product and let `simp` settle the branch
    have h0 : ⟪principalSourceVector U V q1,
        principalOrthogonalVector U V hacute p1⟫_𝕜 = 0 :=
      Submodule.inner_right_of_mem_orthogonal hq hp
    have h1 : ⟪principalOrthogonalVector U V hacute p1,
        principalSourceVector U V q1⟫_𝕜 = 0 := by
      rw [← inner_conj_symm, h0, map_zero]
    simp [h1, Prod.ext_iff]
  · simpa [Prod.ext_iff] using orthonormal_iff_ite.mp
      (orthonormal_principalOrthogonalVector U V hacute) p1 q1

/-- The inverse direct rotation acts on a source vector by the transposed
rotation block. -/
theorem directRotation_symm_apply_principalSourceVector
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    (directRotation U V hacute).symm (principalSourceVector U V i) =
      (principalPlaneCosine U V i : 𝕜) • principalSourceVector U V i -
        (principalPlaneSine U V i : 𝕜) • principalOrthogonalVector U V hacute i := by
  have htwo := LinearMap.congr_fun (two_smul_abs_canonicalIntertwiner U V hacute)
    (principalSourceVector U V i)
  have habs := abs_canonicalIntertwiner_apply_principalSourceVector U V hacute i
  have hRu := directRotation_apply_principalSourceVector U V hacute i
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv] at htwo
  rw [habs, hRu] at htwo
  -- `htwo : 2 • (c • u) = (c • u + s • j) + R.symm u`
  have h2 : (directRotation U V hacute).symm (principalSourceVector U V i) =
      (2 : 𝕜) • ((principalPlaneCosine U V i : 𝕜) • principalSourceVector U V i) -
        ((principalPlaneCosine U V i : 𝕜) • principalSourceVector U V i +
          (principalPlaneSine U V i : 𝕜) • principalOrthogonalVector U V hacute i) :=
    eq_sub_of_add_eq' htwo.symm
  rw [h2]
  module

/-- The direct rotation acts on the orthogonal partner by the second column of
its principal rotation block. -/
theorem directRotation_apply_principalOrthogonalVector
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    directRotation U V hacute (principalOrthogonalVector U V hacute i) =
      -(principalPlaneSine U V i : 𝕜) • principalSourceVector U V i +
        (principalPlaneCosine U V i : 𝕜) •
          principalOrthogonalVector U V hacute i := by
  have hsymm := directRotation_symm_apply_principalSourceVector U V hacute i
  have happ := congrArg (directRotation U V hacute) hsymm
  rw [LinearIsometryEquiv.apply_symm_apply, map_sub, map_smul, map_smul,
    directRotation_apply_principalSourceVector U V hacute i] at happ
  -- `happ : u = c • (c • u + s • j) - s • R j`
  have hs : ((principalPlaneSine U V i : ℝ) : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (ne_of_gt (principalPlaneSine_pos U V i))
  apply smul_right_injective E hs
  have h2 : (principalPlaneSine U V i : 𝕜) •
      directRotation U V hacute (principalOrthogonalVector U V hacute i) =
      (principalPlaneCosine U V i : 𝕜) •
        ((principalPlaneCosine U V i : 𝕜) • principalSourceVector U V i +
          (principalPlaneSine U V i : 𝕜) • principalOrthogonalVector U V hacute i) -
        principalSourceVector U V i := by
    rw [eq_sub_iff_add_eq, add_comm, ← eq_sub_iff_add_eq]
    exact happ
  -- `smul_right_injective` leaves both sides under an unreduced lambda
  beta_reduce
  rw [h2]
  have hpyth := principalPlaneCosine_sq_add_sine_sq U V i
  -- `match_scalars` leaves goals in `𝕜`, where no ordered-field tactic applies;
  -- the Pythagorean identity has to be transported across the cast
  have hpythK : ((principalPlaneCosine U V i : ℝ) : 𝕜) ^ 2 +
      ((principalPlaneSine U V i : ℝ) : 𝕜) ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ => (r : 𝕜)) hpyth
    push_cast at h
    exact h
  match_scalars
  · linear_combination hpythK
  · ring

/-- The inverse direct rotation acts on the orthogonal partner by the second
column of the transposed rotation block. -/
theorem directRotation_symm_apply_principalOrthogonalVector
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    (directRotation U V hacute).symm (principalOrthogonalVector U V hacute i) =
      (principalPlaneSine U V i : 𝕜) • principalSourceVector U V i +
        (principalPlaneCosine U V i : 𝕜) •
          principalOrthogonalVector U V hacute i := by
  have hRj := directRotation_apply_principalOrthogonalVector U V hacute i
  have happ := congrArg (directRotation U V hacute).symm hRj
  rw [LinearIsometryEquiv.symm_apply_apply, map_add, map_smul, map_smul,
    directRotation_symm_apply_principalSourceVector U V hacute i] at happ
  -- `happ : j = -s • (c • u - s • j) + c • R.symm j`
  have hc : ((principalPlaneCosine U V i : ℝ) : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (ne_of_gt (principalPlaneCosine_pos U V hacute i))
  apply smul_right_injective E hc
  have h2 : (principalPlaneCosine U V i : 𝕜) •
      (directRotation U V hacute).symm (principalOrthogonalVector U V hacute i) =
      principalOrthogonalVector U V hacute i -
        -(principalPlaneSine U V i : 𝕜) •
          ((principalPlaneCosine U V i : 𝕜) • principalSourceVector U V i -
            (principalPlaneSine U V i : 𝕜) •
              principalOrthogonalVector U V hacute i) := by
    -- `happ` is already in additive form; only the goal needs reshaping
    rw [eq_sub_iff_add_eq, add_comm]
    exact happ.symm
  beta_reduce
  rw [h2]
  have hpyth := principalPlaneCosine_sq_add_sine_sq U V i
  have hpythK : ((principalPlaneCosine U V i : ℝ) : 𝕜) ^ 2 +
      ((principalPlaneSine U V i : ℝ) : 𝕜) ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ => (r : 𝕜)) hpyth
    push_cast at h
    exact h
  match_scalars
  · linear_combination -hpythK
  · ring

/-- The positive modulus of the canonical intertwiner acts by the principal
cosine on the orthogonal partner as well. -/
theorem abs_canonicalIntertwiner_apply_principalOrthogonalVector
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (i : Fin (nontrivialAngleCount U V)) :
    TauCeti.operatorAbs (canonicalIntertwiner U V)
        (principalOrthogonalVector U V hacute i) =
      (principalPlaneCosine U V i : 𝕜) •
        principalOrthogonalVector U V hacute i := by
  have htwo := LinearMap.congr_fun (two_smul_abs_canonicalIntertwiner U V hacute)
    (principalOrthogonalVector U V hacute i)
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv] at htwo
  rw [directRotation_apply_principalOrthogonalVector U V hacute i,
    directRotation_symm_apply_principalOrthogonalVector U V hacute i] at htwo
  have h2 : (2 : 𝕜) • TauCeti.operatorAbs (canonicalIntertwiner U V)
      (principalOrthogonalVector U V hacute i) =
      (2 : 𝕜) • ((principalPlaneCosine U V i : 𝕜) •
        principalOrthogonalVector U V hacute i) := by
    rw [htwo]
    module
  exact smul_right_injective E (by norm_num : (2 : 𝕜) ≠ 0) h2

/-- Principal sines decrease with the index. -/
theorem principalPlaneSine_antitone
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Antitone (principalPlaneSine U V) := by
  intro i j hij
  exact (sinThetaMap U V).singularValues_antitone hij

/-- Principal cosines increase with the index. -/
theorem principalPlaneCosine_monotone
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Monotone (principalPlaneCosine U V) := by
  intro i j hij
  have hs : principalPlaneSine U V j ≤ principalPlaneSine U V i :=
    principalPlaneSine_antitone U V hij
  rw [principalPlaneCosine, principalPlaneCosine]
  apply Real.sqrt_le_sqrt
  nlinarith [principalPlaneSine_pos U V i, principalPlaneSine_pos U V j]

/-- Chord lengths decrease with the index. -/
theorem principalPlaneChord_antitone
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Antitone (principalPlaneChord U V) := by
  intro i j hij
  have hc : principalPlaneCosine U V i ≤ principalPlaneCosine U V j :=
    principalPlaneCosine_monotone U V hij
  rw [principalPlaneChord, principalPlaneChord]
  apply Real.sqrt_le_sqrt
  linarith

/-- Chord lengths are nonnegative. -/
theorem principalPlaneChord_nonneg
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (i : Fin (nontrivialAngleCount U V)) :
    0 ≤ principalPlaneChord U V i :=
  Real.sqrt_nonneg _

/-- The squared chord is `2 (1 - cos)`. -/
theorem principalPlaneChord_sq
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (i : Fin (nontrivialAngleCount U V)) :
    principalPlaneChord U V i ^ 2 = 2 * (1 - principalPlaneCosine U V i) := by
  rw [principalPlaneChord, Real.sq_sqrt]
  have := principalPlaneCosine_le_one U V i
  linarith
end DavisKahan.FiniteDimensional
end TauCeti
