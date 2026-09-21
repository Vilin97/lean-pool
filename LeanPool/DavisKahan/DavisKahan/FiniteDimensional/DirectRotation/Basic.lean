/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.AngleGeometry
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Polar.Decomposition
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SelfAdjointFunctionalCalculus

/-!
# Canonical finite direct rotation

For an acute pair of finite-dimensional subspaces, the canonical direct
rotation is the unitary polar factor of

`S = P_V P_U + P_{Vᗮ} P_{Uᗮ}`.

This global polar definition is equivalent to the blockwise Davis
intertwining-unitary construction, but exposes the identities needed in Part
III without a fictional principal-plane API.
-/

namespace TauCeti
namespace DavisKahan.FiniteDimensional

open scoped InnerProductSpace BigOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

omit [FiniteDimensional 𝕜 E] in
private theorem projection_comp_complementaryProjection (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] :
    projection U ∘ₗ complementaryProjection U = 0 := by
  apply LinearMap.ext
  intro x
  change U.starProjection (Uᗮ.starProjection x) = 0
  rw [Submodule.starProjection_apply_eq_zero_iff]
  exact Uᗮ.starProjection_apply_mem x

omit [FiniteDimensional 𝕜 E] in
private theorem complementaryProjection_comp_projection (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] :
    complementaryProjection U ∘ₗ projection U = 0 := by
  apply LinearMap.ext
  intro x
  change Uᗮ.starProjection (U.starProjection x) = 0
  rw [Submodule.starProjection_apply_eq_zero_iff]
  exact U.le_orthogonal_orthogonal (U.starProjection_apply_mem x)

omit [FiniteDimensional 𝕜 E] in
private theorem projection_comp_self (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] :
    projection U ∘ₗ projection U = projection U := by
  ext x
  exact Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x)

omit [FiniteDimensional 𝕜 E] in
private theorem complementaryProjection_comp_self (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] :
    complementaryProjection U ∘ₗ complementaryProjection U =
      complementaryProjection U := by
  simpa [complementaryProjection] using projection_comp_self (𝕜 := 𝕜) Uᗮ

omit [FiniteDimensional 𝕜 E] in
/-- The projection fixes vectors already in the subspace. -/
theorem projection_apply_of_mem {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    {x : E} (hx : x ∈ U) : projection U x = x :=
  Submodule.starProjection_eq_self_iff.mpr hx

omit [FiniteDimensional 𝕜 E] in
/-- The projection kills vectors in the orthogonal complement. -/
theorem projection_apply_of_mem_orthogonal {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] {x : E} (hx : x ∈ Uᗮ) : projection U x = 0 :=
  (Submodule.starProjection_apply_eq_zero_iff U).mpr hx

omit [FiniteDimensional 𝕜 E] in
/-- The projection is self-adjoint at the inner-product level. -/
theorem projection_inner_left_eq_right (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (u v : E) :
    ⟪projection U u, v⟫_𝕜 = ⟪u, projection U v⟫_𝕜 :=
  Submodule.inner_starProjection_left_eq_right U u v

/-- The canonical two-projection intertwiner. -/
noncomputable def canonicalIntertwiner (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  projection V ∘ₗ projection U +
    complementaryProjection V ∘ₗ complementaryProjection U

/-- The ordered product of the target and source reflections. -/
noncomputable def reflectionProduct (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E ≃ₗᵢ[𝕜] E :=
  U.reflection.trans V.reflection

omit [FiniteDimensional 𝕜 E] in
/-- The product of the two reflections, unfolded. -/
@[simp] theorem reflectionProduct_apply (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (x : E) :
    reflectionProduct U V x = V.reflection (U.reflection x) := rfl

omit [FiniteDimensional 𝕜 E] in
/-- `2S = I + J_V J_U`. -/
theorem two_smul_canonicalIntertwiner (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (2 : 𝕜) • canonicalIntertwiner U V =
      LinearMap.id + (reflectionProduct U V).toLinearMap := by
  ext x
  simp only [canonicalIntertwiner, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.id_apply, projection, complementaryProjection,
    ContinuousLinearMap.coe_coe, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv, reflectionProduct_apply,
    Submodule.reflection_apply, Submodule.starProjection_orthogonal_val,
    map_sub, map_nsmul]
  module

/-- The adjoint reverses the ordered pair. -/
theorem adjoint_canonicalIntertwiner (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (canonicalIntertwiner U V).adjoint = canonicalIntertwiner V U := by
  rw [canonicalIntertwiner, canonicalIntertwiner, map_add,
    LinearMap.adjoint_comp, LinearMap.adjoint_comp]
  simp only [complementaryProjection, projection_adjoint]

/-- Gram operator of the canonical intertwiner, displayed in source blocks. -/
theorem canonicalIntertwiner_adjoint_comp_self (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (canonicalIntertwiner U V).adjoint ∘ₗ canonicalIntertwiner U V =
      (projection U ∘ₗ projection V ∘ₗ projection U) +
        (complementaryProjection U ∘ₗ complementaryProjection V ∘ₗ
          complementaryProjection U) := by
  have hVV : ∀ y : E, projection V (projection V y) = projection V y := fun y =>
    Submodule.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem y)
  have hcVcV : ∀ y : E, complementaryProjection V (complementaryProjection V y) =
      complementaryProjection V y := fun y =>
    Submodule.starProjection_eq_self_iff.mpr (Vᗮ.starProjection_apply_mem y)
  have hVcV : ∀ y : E, projection V (complementaryProjection V y) = 0 := fun y =>
    (Submodule.starProjection_apply_eq_zero_iff V).mpr (Vᗮ.starProjection_apply_mem y)
  have hcVV : ∀ y : E, complementaryProjection V (projection V y) = 0 := fun y =>
    (Submodule.starProjection_apply_eq_zero_iff Vᗮ).mpr
      (V.le_orthogonal_orthogonal (V.starProjection_apply_mem y))
  rw [adjoint_canonicalIntertwiner]
  ext x
  simp only [canonicalIntertwiner, LinearMap.add_apply, LinearMap.comp_apply,
    map_add, hVV, hcVcV, hVcV, hcVV, map_zero, add_zero, zero_add]

/-- The Gram operator is block diagonal relative to `U`. -/
theorem projection_comm_canonicalIntertwiner_gram (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    projection U ∘ₗ ((canonicalIntertwiner U V).adjoint ∘ₗ
      canonicalIntertwiner U V) =
      ((canonicalIntertwiner U V).adjoint ∘ₗ canonicalIntertwiner U V) ∘ₗ
        projection U := by
  have hUU : ∀ y : E, projection U (projection U y) = projection U y := fun y =>
    Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem y)
  have hUcU : ∀ y : E, projection U (complementaryProjection U y) = 0 := fun y =>
    (Submodule.starProjection_apply_eq_zero_iff U).mpr (Uᗮ.starProjection_apply_mem y)
  have hcUU : ∀ y : E, complementaryProjection U (projection U y) = 0 := fun y =>
    (Submodule.starProjection_apply_eq_zero_iff Uᗮ).mpr
      (U.le_orthogonal_orthogonal (U.starProjection_apply_mem y))
  rw [canonicalIntertwiner_adjoint_comp_self]
  ext x
  simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add, hUU, hUcU, hcUU,
    map_zero, add_zero]

omit [FiniteDimensional 𝕜 E] in
/-- The canonical intertwiner sends source blocks to target blocks. -/
theorem canonicalIntertwiner_comp_projection (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    canonicalIntertwiner U V ∘ₗ projection U =
      projection V ∘ₗ canonicalIntertwiner U V := by
  have hUU : ∀ y : E, projection U (projection U y) = projection U y := fun y =>
    Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem y)
  have hcUU : ∀ y : E, complementaryProjection U (projection U y) = 0 := fun y =>
    (Submodule.starProjection_apply_eq_zero_iff Uᗮ).mpr
      (U.le_orthogonal_orthogonal (U.starProjection_apply_mem y))
  have hVV : ∀ y : E, projection V (projection V y) = projection V y := fun y =>
    Submodule.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem y)
  have hVcV : ∀ y : E, projection V (complementaryProjection V y) = 0 := fun y =>
    (Submodule.starProjection_apply_eq_zero_iff V).mpr (Vᗮ.starProjection_apply_mem y)
  ext x
  simp only [canonicalIntertwiner, LinearMap.comp_apply, LinearMap.add_apply,
    map_add, hUU, hcUU, hVV, hVcV, map_zero, add_zero]

omit [FiniteDimensional 𝕜 E] in
/-- Acuteness makes the canonical intertwiner injective. -/
theorem canonicalIntertwiner_injective_of_acute
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    Function.Injective (canonicalIntertwiner U V) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hVV : ∀ y : E, projection V (projection V y) = projection V y := fun y =>
    Submodule.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem y)
  have hcVcV : ∀ y : E, complementaryProjection V (complementaryProjection V y) =
      complementaryProjection V y := fun y =>
    Submodule.starProjection_eq_self_iff.mpr (Vᗮ.starProjection_apply_mem y)
  have hU : projection U x = 0 := by
    have hVproj := congrArg (projection V) hx
    have hcross : projection V (complementaryProjection V
        (complementaryProjection U x)) = 0 := by
      change V.starProjection (Vᗮ.starProjection
        (Uᗮ.starProjection x)) = 0
      rw [Submodule.starProjection_apply_eq_zero_iff]
      exact Vᗮ.starProjection_apply_mem _
    have hzero : projection V (projection U x) = 0 := by
      simpa [canonicalIntertwiner, LinearMap.add_apply, LinearMap.comp_apply,
        hcross, hVV] using hVproj
    exact hacute.1 (projection U x) (U.starProjection_apply_mem x) hzero
  have hUperp : complementaryProjection U x = 0 := by
    have hVperp := congrArg (complementaryProjection V) hx
    have hcross : complementaryProjection V (projection V (projection U x)) = 0 := by
      change Vᗮ.starProjection (V.starProjection (U.starProjection x)) = 0
      rw [Submodule.starProjection_apply_eq_zero_iff]
      exact V.le_orthogonal_orthogonal (V.starProjection_apply_mem _)
    have hzero : complementaryProjection V (complementaryProjection U x) = 0 := by
      simpa [canonicalIntertwiner, LinearMap.add_apply, LinearMap.comp_apply,
        hcross, hcVcV] using hVperp
    have hyV : complementaryProjection U x ∈ V := by
      have : complementaryProjection U x ∈ (Vᗮ)ᗮ :=
        (Submodule.starProjection_apply_eq_zero_iff Vᗮ).mp hzero
      simpa using this
    have hyU : projection U (complementaryProjection U x) = 0 := by
      change U.starProjection (Uᗮ.starProjection x) = 0
      rw [Submodule.starProjection_apply_eq_zero_iff]
      exact Uᗮ.starProjection_apply_mem x
    exact hacute.2 (complementaryProjection U x) hyV hyU
  calc
    x = projection U x + complementaryProjection U x := by
      symm
      exact U.starProjection_add_starProjection_orthogonal x
    _ = 0 := by rw [hU, hUperp, add_zero]

/-- Acuteness makes the canonical intertwiner invertible. -/
theorem canonicalIntertwiner_isUnit_of_acute
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) : IsUnit (canonicalIntertwiner U V) := by
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot]
  exact canonicalIntertwiner_injective_of_acute U V hacute

/-- The canonical intertwiner is normal for an acute pair. -/
theorem canonicalIntertwiner_normal_of_acute
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (_hacute : IsAcute U V) :
    (canonicalIntertwiner U V).adjoint ∘ₗ canonicalIntertwiner U V =
      canonicalIntertwiner U V ∘ₗ (canonicalIntertwiner U V).adjoint := by
  have hS := two_smul_canonicalIntertwiner U V
  have hSrev := two_smul_canonicalIntertwiner V U
  have hRrev : (reflectionProduct V U).toLinearMap
      = (reflectionProduct U V).symm.toLinearMap := by
    ext x; simp [reflectionProduct]
  rw [hRrev] at hSrev
  have hstar := adjoint_canonicalIntertwiner U V
  have hRR : (reflectionProduct U V).toLinearMap ∘ₗ
      (reflectionProduct U V).symm.toLinearMap = LinearMap.id := by
    ext x; simp []
  have hRR' : (reflectionProduct U V).symm.toLinearMap ∘ₗ
      (reflectionProduct U V).toLinearMap = LinearMap.id := by
    ext x; simp []
  have key : ((2 : 𝕜) • canonicalIntertwiner V U) ∘ₗ
        ((2 : 𝕜) • canonicalIntertwiner U V) =
      ((2 : 𝕜) • canonicalIntertwiner U V) ∘ₗ
        ((2 : 𝕜) • canonicalIntertwiner V U) := by
    rw [hS, hSrev]
    simp only [LinearMap.add_comp, LinearMap.comp_add, LinearMap.id_comp,
      LinearMap.comp_id, hRR, hRR']
    abel
  rw [hstar]
  apply LinearMap.ext
  intro x
  have h4 : ((2 : 𝕜) * (2 : 𝕜)) ≠ 0 := by norm_num
  apply smul_right_injective E h4
  have hkey := LinearMap.congr_fun key x
  simpa only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, smul_smul]
    using hkey

/-- The positive modulus of the intertwiner commutes with the source
projection. -/
theorem projection_comm_abs_canonicalIntertwiner
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    projection U ∘ₗ TauCeti.operatorAbs (canonicalIntertwiner U V) =
      TauCeti.operatorAbs (canonicalIntertwiner U V) ∘ₗ projection U := by
  exact TauCeti.sqrt_comm
    (LinearMap.isPositive_adjoint_comp_self (canonicalIntertwiner U V))
    (projection_comm_canonicalIntertwiner_gram U V)


omit [FiniteDimensional 𝕜 E] in
/-- If the two projections agree on a vector, the canonical intertwiner fixes
that vector. -/
theorem canonicalIntertwiner_apply_eq_self_of_projection_eq
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {x : E} (hx : projection U x = projection V x) :
    canonicalIntertwiner U V x = x := by
  have hp : projection V (projection V x) = projection V x :=
    Submodule.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem x)
  have hcU : ∀ y : E, complementaryProjection U y = y - projection U y := fun y =>
    Submodule.starProjection_orthogonal_val y
  have hcV : ∀ y : E, complementaryProjection V y = y - projection V y := fun y =>
    Submodule.starProjection_orthogonal_val y
  simp only [canonicalIntertwiner, LinearMap.add_apply, LinearMap.comp_apply,
    hcU, hcV, hx, map_sub, hp]
  module

/-- The adjoint canonical intertwiner also fixes a vector on which the two
projections agree. -/
theorem adjoint_canonicalIntertwiner_apply_eq_self_of_projection_eq
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {x : E} (hx : projection U x = projection V x) :
    (canonicalIntertwiner U V).adjoint x = x := by
  rw [adjoint_canonicalIntertwiner]
  exact canonicalIntertwiner_apply_eq_self_of_projection_eq V U hx.symm

/-- The positive cosine `|S|` fixes every zero-angle direction. -/
theorem abs_canonicalIntertwiner_apply_eq_self_of_projection_eq
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {x : E} (hx : projection U x = projection V x) :
    TauCeti.operatorAbs (canonicalIntertwiner U V) x = x := by
  let S := canonicalIntertwiner U V
  have hS : S x = x :=
    canonicalIntertwiner_apply_eq_self_of_projection_eq U V hx
  have hSstar : S.adjoint x = x :=
    adjoint_canonicalIntertwiner_apply_eq_self_of_projection_eq U V hx
  have hsq : (S.adjoint ∘ₗ S) x = ((1 : ℝ) : 𝕜) • x := by
    simp [LinearMap.comp_apply, hS, hSstar]
  have hpos := LinearMap.isPositive_adjoint_comp_self S
  have hfc := TauCeti.selfAdjointFunctionalCalculus_apply_of_apply_eq_smul
    hpos.isSymmetric Real.sqrt hsq
  rw [TauCeti.selfAdjointFunctionalCalculus_sqrt hpos, Real.sqrt_one] at hfc
  show hpos.sqrt x = x
  rw [hfc]
  simp

/-- The canonical direct rotation from `U` to `V`, defined as the unitary polar
factor of the canonical intertwiner. -/
noncomputable def directRotation (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) : E ≃ₗᵢ[𝕜] E :=
  polarUnitaryEquiv (canonicalIntertwiner_isUnit_of_acute U V hacute)

/-- The direct rotation, as a plain linear map. -/
@[simp] theorem directRotation_toLinearMap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap =
      polarFactor (canonicalIntertwiner U V) := rfl


/-- The direct rotation fixes every zero-angle direction. -/
theorem directRotation_apply_eq_self_of_projection_eq
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) {x : E}
    (hx : projection U x = projection V x) :
    directRotation U V hacute x = x := by
  let S := canonicalIntertwiner U V
  have hS : S x = x :=
    canonicalIntertwiner_apply_eq_self_of_projection_eq U V hx
  have hC : TauCeti.operatorAbs S x = x :=
    abs_canonicalIntertwiner_apply_eq_self_of_projection_eq U V hx
  have hpolar := LinearMap.congr_fun (polar_decomposition S) x
  rw [LinearMap.comp_apply, hC, hS] at hpolar
  -- hpolar : x = polarFactor S x
  have hgoal : (directRotation U V hacute).toLinearMap x = x := by
    rw [directRotation_toLinearMap]; exact hpolar.symm
  simpa only [LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv] using hgoal

/-- The canonical direct rotation commutes with its positive cosine factor. -/
theorem directRotation_comm_abs_canonicalIntertwiner
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap ∘ₗ
        TauCeti.operatorAbs (canonicalIntertwiner U V) =
      TauCeti.operatorAbs (canonicalIntertwiner U V) ∘ₗ
        (directRotation U V hacute).toLinearMap := by
  let S := canonicalIntertwiner U V
  let C := TauCeti.operatorAbs S
  let R := (directRotation U V hacute).toLinearMap
  have hSC : S ∘ₗ C = C ∘ₗ S :=
    operatorAbs_comm_of_normal (canonicalIntertwiner_normal_of_acute U V hacute)
  have hCinj : Function.Injective C := by
    rw [← LinearMap.ker_eq_bot, ker_operatorAbs,
      (LinearMap.isUnit_iff_ker_eq_bot _).mp
        (canonicalIntertwiner_isUnit_of_acute U V hacute)]
  have hCsurj : Function.Surjective C :=
    LinearMap.injective_iff_surjective.mp hCinj
  have hdecomp : S = R ∘ₗ C := by
    simpa [R, directRotation, S, C] using polar_decomposition S
  rw [hdecomp] at hSC
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := hCsurj x
  exact LinearMap.congr_fun hSC y

/-- **The modulus of the canonical intertwiner is surjective** on an acute pair.

Injective because the intertwiner is a unit and `operatorAbs` shares its kernel, then
injective-implies-surjective in finite dimensions.  Derived twice below. -/
private theorem abs_canonicalIntertwiner_surjective (U V : Submodule 𝕜 E)
    (hacute : IsAcute U V) :
    Function.Surjective (TauCeti.operatorAbs (canonicalIntertwiner U V)) := by
  have hCin : Function.Injective (TauCeti.operatorAbs (canonicalIntertwiner U V)) := by
    rw [← LinearMap.ker_eq_bot, ker_operatorAbs,
      (LinearMap.isUnit_iff_ker_eq_bot _).mp
        (canonicalIntertwiner_isUnit_of_acute U V hacute)]
  exact LinearMap.injective_iff_surjective.mp hCin

/-- The intertwining identity `W P_U = P_V W`. -/
theorem directRotation_comp_projection (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap ∘ₗ projection U =
      projection V ∘ₗ (directRotation U V hacute).toLinearMap := by
  let S := canonicalIntertwiner U V
  let C := TauCeti.operatorAbs S
  let W := (directRotation U V hacute).toLinearMap
  have hpolar : S = W ∘ₗ C := by
    simpa [S, C, W, directRotation] using
      polar_decomposition_of_isUnit (canonicalIntertwiner_isUnit_of_acute U V hacute)
  have hCP := projection_comm_abs_canonicalIntertwiner U V
  have hSP := canonicalIntertwiner_comp_projection U V
  have hCsurj : Function.Surjective C :=
    abs_canonicalIntertwiner_surjective U V hacute
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := hCsurj x
  have hCPy := LinearMap.congr_fun hCP y
  have hSPy := LinearMap.congr_fun hSP y
  have hpolar_y := LinearMap.congr_fun hpolar y
  have hpolar_Py := LinearMap.congr_fun hpolar (projection U y)
  calc
    W (projection U (C y)) = W (C (projection U y)) := by
      rw [show projection U (C y) = C (projection U y) by
        simpa [LinearMap.comp_apply] using hCPy]
    _ = S (projection U y) := by
      simpa [LinearMap.comp_apply] using hpolar_Py.symm
    _ = projection V (S y) := by
      simpa [LinearMap.comp_apply] using hSPy
    _ = projection V (W (C y)) := by
      have hWC : W (C y) = S y := by
        rw [← LinearMap.comp_apply]; exact hpolar_y.symm
      rw [hWC]


/-- The canonical intertwiner is the reflection product times its adjoint. -/
theorem canonicalIntertwiner_eq_reflectionProduct_comp_adjoint
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    canonicalIntertwiner U V =
      (reflectionProduct U V).toLinearMap ∘ₗ
        (canonicalIntertwiner U V).adjoint := by
  have hS := two_smul_canonicalIntertwiner U V
  have hSrev := two_smul_canonicalIntertwiner V U
  have hstar := adjoint_canonicalIntertwiner U V
  have hRrev : (reflectionProduct V U).toLinearMap =
      (reflectionProduct U V).symm.toLinearMap := by
    ext x
    simp [reflectionProduct]
  rw [hRrev] at hSrev
  have hRR : (reflectionProduct U V).toLinearMap ∘ₗ
      (reflectionProduct U V).symm.toLinearMap = LinearMap.id := by
    ext x; simp []
  have hSadj : (2 : 𝕜) • (canonicalIntertwiner U V).adjoint
      = LinearMap.id + (reflectionProduct U V).symm.toLinearMap := by
    rw [hstar]; exact hSrev
  have key : (2 : 𝕜) • canonicalIntertwiner U V
      = (2 : 𝕜) • ((reflectionProduct U V).toLinearMap ∘ₗ
          (canonicalIntertwiner U V).adjoint) := by
    rw [hS, ← LinearMap.comp_smul, hSadj, LinearMap.comp_add, LinearMap.comp_id,
      hRR]
    abel
  apply LinearMap.ext
  intro x
  apply smul_right_injective E (show (2 : 𝕜) ≠ 0 by norm_num)
  simpa only [LinearMap.smul_apply] using LinearMap.congr_fun key x

/-- The reflection product commutes with the Gram operator of the canonical
intertwiner. -/
theorem reflectionProduct_comm_canonicalIntertwiner_gram
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (reflectionProduct U V).toLinearMap ∘ₗ
        ((canonicalIntertwiner U V).adjoint ∘ₗ canonicalIntertwiner U V) =
      ((canonicalIntertwiner U V).adjoint ∘ₗ canonicalIntertwiner U V) ∘ₗ
        (reflectionProduct U V).toLinearMap := by
  have hS := two_smul_canonicalIntertwiner U V
  have hSrev := two_smul_canonicalIntertwiner V U
  have hstar := adjoint_canonicalIntertwiner U V
  have hRrev : (reflectionProduct V U).toLinearMap =
      (reflectionProduct U V).symm.toLinearMap := by
    ext x
    simp [reflectionProduct]
  rw [hRrev] at hSrev
  have hRR : (reflectionProduct U V).toLinearMap ∘ₗ
      (reflectionProduct U V).symm.toLinearMap = LinearMap.id := by
    ext x; simp []
  have hRR' : (reflectionProduct U V).symm.toLinearMap ∘ₗ
      (reflectionProduct U V).toLinearMap = LinearMap.id := by
    ext x; simp []
  have hSadj : (2 : 𝕜) • (canonicalIntertwiner U V).adjoint
      = LinearMap.id + (reflectionProduct U V).symm.toLinearMap := by
    rw [hstar]; exact hSrev
  have hGram : (4 : 𝕜) •
        ((canonicalIntertwiner U V).adjoint ∘ₗ canonicalIntertwiner U V) =
      (2 : 𝕜) • LinearMap.id + (reflectionProduct U V).toLinearMap
        + (reflectionProduct U V).symm.toLinearMap := by
    have hfac : (4 : 𝕜) •
          ((canonicalIntertwiner U V).adjoint ∘ₗ canonicalIntertwiner U V) =
        ((2 : 𝕜) • (canonicalIntertwiner U V).adjoint) ∘ₗ
          ((2 : 𝕜) • canonicalIntertwiner U V) := by
      rw [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul,
        show ((2 : 𝕜) * 2) = 4 by norm_num]
    rw [hfac, hSadj, hS]
    simp only [LinearMap.add_comp, LinearMap.comp_add, LinearMap.id_comp,
      LinearMap.comp_id, hRR']
    module
  have hcomm : (reflectionProduct U V).toLinearMap ∘ₗ
        ((4 : 𝕜) • ((canonicalIntertwiner U V).adjoint ∘ₗ canonicalIntertwiner U V)) =
      ((4 : 𝕜) • ((canonicalIntertwiner U V).adjoint ∘ₗ canonicalIntertwiner U V)) ∘ₗ
        (reflectionProduct U V).toLinearMap := by
    rw [hGram]
    simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_smul,
      LinearMap.smul_comp, LinearMap.comp_id, LinearMap.id_comp, hRR, hRR']
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun hcomm x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul] at hx
  apply smul_right_injective E (show (4 : 𝕜) ≠ 0 by norm_num)
  simpa only [LinearMap.comp_apply] using hx

/-- The reflection product commutes with the positive modulus of the canonical
intertwiner. -/
theorem reflectionProduct_comm_abs_canonicalIntertwiner
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (reflectionProduct U V).toLinearMap ∘ₗ
        TauCeti.operatorAbs (canonicalIntertwiner U V) =
      TauCeti.operatorAbs (canonicalIntertwiner U V) ∘ₗ
        (reflectionProduct U V).toLinearMap := by
  exact TauCeti.sqrt_comm
    (LinearMap.isPositive_adjoint_comp_self (canonicalIntertwiner U V))
    (reflectionProduct_comm_canonicalIntertwiner_gram U V)

/-- The square of the canonical direct rotation is the ordered product of the
reflections. -/
theorem directRotation_sq (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap ∘ₗ
        (directRotation U V hacute).toLinearMap =
      (reflectionProduct U V).toLinearMap := by
  let S := canonicalIntertwiner U V
  let C := TauCeti.operatorAbs S
  let W := (directRotation U V hacute).toLinearMap
  let R := (reflectionProduct U V).toLinearMap
  have hpolar : S = W ∘ₗ C := by
    simpa [S, C, W, directRotation] using
      polar_decomposition_of_isUnit
        (canonicalIntertwiner_isUnit_of_acute U V hacute)
  have hstar : S.adjoint = C ∘ₗ W.adjoint := by
    rw [hpolar, LinearMap.adjoint_comp, (isPositive_operatorAbs S).adjoint_eq]
  have hRSstar : S = R ∘ₗ S.adjoint := by
    simpa [S, R] using
      canonicalIntertwiner_eq_reflectionProduct_comp_adjoint U V
  have hWC : W ∘ₗ C = C ∘ₗ W :=
    directRotation_comm_abs_canonicalIntertwiner U V hacute
  have hWadj : W.adjoint = (directRotation U V hacute).symm.toLinearMap :=
    LinearIsometryEquiv.adjoint_toLinearMap_eq_symm (directRotation U V hacute)
  have hWadjW : W.adjoint ∘ₗ W = LinearMap.id := by
    rw [hWadj]
    ext z
    simp only [W, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.symm_apply_apply,
      LinearMap.id_apply]
  have hCsurj : Function.Surjective C :=
    abs_canonicalIntertwiner_surjective U V hacute
  -- `W ∘ₗ C = R ∘ₗ (C ∘ₗ W.adjoint)` from the reflection identity `S = R S⋆`.
  have hWCeq : W ∘ₗ C = R ∘ₗ (C ∘ₗ W.adjoint) := by
    rw [← hstar, ← hRSstar]; exact hpolar.symm
  -- Hence `(W ∘ₗ C) ∘ₗ W = R ∘ₗ C`.
  have hWCW : (W ∘ₗ C) ∘ₗ W = R ∘ₗ C := by
    rw [hWCeq, LinearMap.comp_assoc, LinearMap.comp_assoc, hWadjW,
      LinearMap.comp_id]
  -- `(W ∘ₗ W) ∘ₗ C = R ∘ₗ C`, using `W ∘ₗ C = C ∘ₗ W`.
  have hkey : (W ∘ₗ W) ∘ₗ C = R ∘ₗ C := by
    calc (W ∘ₗ W) ∘ₗ C
        = W ∘ₗ (C ∘ₗ W) := by rw [LinearMap.comp_assoc, ← hWC]
      _ = (W ∘ₗ C) ∘ₗ W := by rw [← LinearMap.comp_assoc]
      _ = R ∘ₗ C := hWCW
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := hCsurj x
  exact LinearMap.congr_fun hkey y

/-- The positive modulus is the real part of the direct rotation. -/
theorem two_smul_abs_canonicalIntertwiner
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (2 : 𝕜) • TauCeti.operatorAbs (canonicalIntertwiner U V) =
      (directRotation U V hacute).toLinearMap +
        (directRotation U V hacute).symm.toLinearMap := by
  let S := canonicalIntertwiner U V
  let C := TauCeti.operatorAbs S
  let W := (directRotation U V hacute).toLinearMap
  have hpolar : S = W ∘ₗ C := by
    simpa [S, C, W, directRotation] using
      polar_decomposition_of_isUnit
        (canonicalIntertwiner_isUnit_of_acute U V hacute)
  have htwo := two_smul_canonicalIntertwiner U V
  have hsq := directRotation_sq U V hacute
  have hWinj : Function.Injective W := by
    intro x y hxy
    change directRotation U V hacute x = directRotation U V hacute y at hxy
    exact (directRotation U V hacute).injective hxy
  apply LinearMap.ext
  intro x
  apply hWinj
  have hpolar_x := LinearMap.congr_fun hpolar x
  have htwo_x := LinearMap.congr_fun htwo x
  have hsq_x := LinearMap.congr_fun hsq x
  have hWsymm : (directRotation U V hacute).toLinearMap
      ((directRotation U V hacute).symm.toLinearMap x) = x := by
    simp only [LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.apply_symm_apply]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.comp_apply, W, C, S] at hpolar_x htwo_x hsq_x ⊢
  rw [map_smul, map_add, ← hpolar_x, htwo_x, hsq_x, hWsymm]
  abel

/-- The direct rotation maps `U` onto `V`. -/
theorem directRotation_map_eq (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    U.map (directRotation U V hacute).toLinearMap = V := by
  apply le_antisymm
  · rintro _ ⟨x, hxU, rfl⟩
    have h := LinearMap.congr_fun
      (directRotation_comp_projection U V hacute) x
    have hxproj : projection U x = x :=
      Submodule.starProjection_eq_self_iff.mpr hxU
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hxproj] at h
    exact Submodule.starProjection_eq_self_iff.mp h.symm
  · intro y hyV
    have hWsy : (directRotation U V hacute).toLinearMap
        ((directRotation U V hacute).symm y) = y := by
      simp only [LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
        LinearIsometryEquiv.apply_symm_apply]
    refine ⟨(directRotation U V hacute).symm y, ?_, hWsy⟩
    apply Submodule.starProjection_eq_self_iff.mp
    apply (directRotation U V hacute).injective
    rw [show (directRotation U V hacute) ((directRotation U V hacute).symm y) = y from
      (directRotation U V hacute).apply_symm_apply y]
    have h := LinearMap.congr_fun
      (directRotation_comp_projection U V hacute)
      ((directRotation U V hacute).symm y)
    have hyproj : projection V y = y :=
      Submodule.starProjection_eq_self_iff.mpr hyV
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hWsy, hyproj] at h
    exact h

end DavisKahan.FiniteDimensional
end TauCeti
