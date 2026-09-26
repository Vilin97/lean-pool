/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5, Jon Crall
-/
module

public import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.DirectRotation.QNorm

/-!
# The short-rotation full-displacement claim is false

This file certifies the refutation recorded in
the 2026-07-21 repair note (Git history): the transcribed
Davis--Kahan Proposition 4.4 — *"over a real space, if every principal angle
is at most `π/3` then the direct rotation minimizes every unitarily invariant
norm of the full displacement `I - W` over unitaries `W` carrying `U` onto
`V`"* — fails, already for the trace norm (`kyFanSum 4`) in `ℝ⁴`.

## The configuration

Take `U = span{e₀, e₁}` and the orthogonal competitor `W = ½·H` with

`H = !![1,-1,-1,-1; 1,1,1,-1; -1,-1,1,-1; 1,-1,1,1]`,

and let `V = W(U)`.  Both principal angles are `π/4 ≤ π/3` and the pair is
acute.  `W` restricted to the plane `M = span{m₀, m₁}`,
`m₀ = (e₀+e₂)/√2`, `m₁ = (e₁+e₃)/√2`, is a rotation by `π/2` and it fixes
`Mᗮ = span{m₂, m₃}` pointwise, so `σ(I-W) = (√2, √2, 0, 0)` and the trace
norm is `2√2`.

The canonical intertwiner satisfies `S⋆S = ½·I`, so `|S| = √½·I`,
`(I-R)⋆(I-R) = (2-√2)·I`, and the trace norm of `I-R` is
`4√(2-√2) ≈ 3.06 > 2√2 ≈ 2.83`.

The mechanism is multiplicity mixing: across two equal principal angles `θ`
the competitor spends `2θ` of rotation in a single plane and none in the
other, with trace displacement `4 sin θ < 8 sin(θ/2)`; no angle threshold
saves the full-displacement claim.  The valid Section 4 endpoints are the
restricted-displacement theorems (`uiNorm_restrictedDisplacement_le`) and
the displacement-square majorization
(`directRotation_displacementSquare_uiNorm`).
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan.FiniteDimensional
namespace ShortRotationCounterexample

open scoped InnerProductSpace
open Module (finrank)

section

/-- The ambient space `ℝ⁴`. -/
noncomputable abbrev E4 := EuclideanSpace ℝ (Fin 4)

/-- Standard basis vector. -/
noncomputable abbrev sv (i : Fin 4) : E4 := EuclideanSpace.single i 1

/-- The competitor matrix `½·H` with `H` a sign matrix of Hadamard type. -/
noncomputable def Wmat : Matrix (Fin 4) (Fin 4) ℝ :=
  (2⁻¹ : ℝ) • !![1, -1, -1, -1; 1, 1, 1, -1; -1, -1, 1, -1; 1, -1, 1, 1]

/-- The competitor as a linear map. -/
noncomputable def Wlin : E4 →ₗ[ℝ] E4 := Matrix.toEuclideanLin Wmat

/-- The inverse (transpose) as a linear map. -/
noncomputable def Wlin' : E4 →ₗ[ℝ] E4 := Matrix.toEuclideanLin Wmat.transpose

private theorem Wlin_apply (x : E4) (i : Fin 4) :
    Wlin x i = ∑ j, Wmat i j * x j := by
  simp [Wlin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

private theorem Wlin'_apply (x : E4) (i : Fin 4) :
    Wlin' x i = ∑ j, Wmat j i * x j := by
  simp [Wlin', Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply]

private theorem Wlin'_comp_Wlin : Wlin' ∘ₗ Wlin = LinearMap.id := by
  apply LinearMap.ext
  intro x
  ext i
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [Wlin'_apply]
  simp only [Wlin_apply]
  fin_cases i <;>
    simp [Wmat, Fin.sum_univ_four, Matrix.smul_apply] <;> ring

private theorem Wlin_comp_Wlin' : Wlin ∘ₗ Wlin' = LinearMap.id := by
  apply LinearMap.ext
  intro x
  ext i
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [Wlin_apply]
  simp only [Wlin'_apply]
  fin_cases i <;>
    simp [Wmat, Fin.sum_univ_four, Matrix.smul_apply] <;> ring

private theorem inner_Wlin_Wlin (x y : E4) : ⟪Wlin x, Wlin y⟫_ℝ = ⟪x, y⟫_ℝ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp only [Wlin_apply]
  simp only [Fin.sum_univ_four]
  simp [Wmat, Matrix.smul_apply]
  ring

/-- The competitor as a linear isometry equivalence. -/
noncomputable def Wequiv : E4 ≃ₗᵢ[ℝ] E4 :=
  (LinearEquiv.ofLinearMap Wlin Wlin'
    (by exact Wlin_comp_Wlin') (by exact Wlin'_comp_Wlin)).isometryOfInner
    (by intro x y; exact inner_Wlin_Wlin x y)

private theorem Wequiv_apply (x : E4) : Wequiv x = Wlin x := rfl

private theorem Wequiv_symm_apply (x : E4) : Wequiv.symm x = Wlin' x := rfl

private theorem Wequiv_toLinearMap : Wequiv.toLinearMap = Wlin := rfl

private theorem Wlin_adjoint : LinearMap.adjoint Wlin = Wlin' :=
  Wequiv.adjoint_toLinearMap_eq_symm

/-- The source subspace `span{e₀, e₁}`. -/
noncomputable def U4 : Submodule ℝ E4 := Submodule.span ℝ {sv 0, sv 1}

/-- The target subspace `W(U)`. -/
noncomputable def V4 : Submodule ℝ E4 := U4.map Wequiv.toLinearMap

private theorem mem_U4 {x : E4} (hx : x ∈ U4) : x = x 0 • sv 0 + x 1 • sv 1 := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  ext i
  fin_cases i <;> simp [sv]

private theorem coord_eq_zero_of_mem_U4 {x : E4} (hx : x ∈ U4) :
    x 2 = 0 ∧ x 3 = 0 := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  constructor <;> simp [sv]

private theorem projection_U4_apply (x : E4) :
    projection U4 x = x 0 • sv 0 + x 1 • sv 1 := by
  change U4.starProjection x = _
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact add_mem
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · rw [Submodule.mem_orthogonal]
    intro u hu
    rw [mem_U4 hu]
    simp [sv, inner_add_left, inner_sub_right, real_inner_smul_left,
      EuclideanSpace.inner_single_left]

private theorem projection_U4_coord (x : E4) (i : Fin 4) :
    projection U4 x i = if i = 0 then x 0 else if i = 1 then x 1 else 0 := by
  rw [projection_U4_apply]
  fin_cases i <;> simp [sv]

private theorem projection_V4_apply (x : E4) :
    projection V4 x = Wequiv (projection U4 (Wequiv.symm x)) := by
  have h := projection_intertwines_of_map_eq U4 V4 Wequiv rfl
  have hx := LinearMap.congr_fun h (Wequiv.symm x)
  simp only [LinearMap.comp_apply] at hx
  have hWW : Wequiv.toLinearMap (Wequiv.symm x) = x := by
    change Wequiv (Wequiv.symm x) = x
    exact Wequiv.apply_symm_apply x
  rw [hWW] at hx
  exact hx.symm

/-- Coordinates of the target projection:
`P_V x = ½ (x₀+x₃, x₁-x₂, x₂-x₁, x₀+x₃)`. -/
theorem projection_V4_coord (x : E4) (i : Fin 4) :
    projection V4 x i =
      if i = 0 then (x 0 + x 3) / 2 else
      if i = 1 then (x 1 - x 2) / 2 else
      if i = 2 then (x 2 - x 1) / 2 else (x 0 + x 3) / 2 := by
  rw [projection_V4_apply, Wequiv_apply, Wequiv_symm_apply, Wlin_apply]
  simp only [projection_U4_coord, Wlin'_apply]
  fin_cases i <;>
    simp [Wmat, Fin.sum_univ_four, Matrix.smul_apply] <;> ring

/-- The inner product against a mapped basis vector. -/
theorem inner_Wlin_sv0 (x : E4) :
    ⟪Wlin (sv 0), x⟫_ℝ = (x 0 + x 1 - x 2 + x 3) / 2 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Wlin_apply]
  simp [sv, Wmat, PiLp.single_apply, Fin.sum_univ_four,
    Matrix.smul_apply]
  ring

private theorem inner_Wlin_sv1 (x : E4) :
    ⟪Wlin (sv 1), x⟫_ℝ = (-x 0 + x 1 - x 2 - x 3) / 2 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Wlin_apply]
  simp [sv, Wmat, PiLp.single_apply, Fin.sum_univ_four,
    Matrix.smul_apply]
  ring

/-- The pair is acute. -/
theorem acute : IsAcute U4 V4 := by
  constructor
  · intro x hxU h0
    have hxperp : x ∈ V4ᗮ :=
      (Submodule.starProjection_apply_eq_zero_iff V4).mp h0
    rw [Submodule.mem_orthogonal] at hxperp
    have h1 : ⟪Wlin (sv 0), x⟫_ℝ = 0 :=
      hxperp _ ⟨sv 0, Submodule.subset_span (by simp), rfl⟩
    have h2 : ⟪Wlin (sv 1), x⟫_ℝ = 0 :=
      hxperp _ ⟨sv 1, Submodule.subset_span (by simp), rfl⟩
    rw [inner_Wlin_sv0] at h1
    rw [inner_Wlin_sv1] at h2
    obtain ⟨hx2, hx3⟩ := coord_eq_zero_of_mem_U4 hxU
    have hx0 : x 0 = 0 := by rw [hx2, hx3] at h1 h2; linarith
    have hx1 : x 1 = 0 := by rw [hx2, hx3] at h1 h2; linarith
    rw [mem_U4 hxU, hx0, hx1]
    simp
  · intro y hyV h0
    obtain ⟨z, hzU, rfl⟩ := hyV
    have hyperp : Wequiv.toLinearMap z ∈ U4ᗮ :=
      (Submodule.starProjection_apply_eq_zero_iff U4).mp h0
    rw [Submodule.mem_orthogonal] at hyperp
    have h1 : ⟪sv 0, Wequiv.toLinearMap z⟫_ℝ = 0 :=
      hyperp _ (Submodule.subset_span (by simp))
    have h2 : ⟪sv 1, Wequiv.toLinearMap z⟫_ℝ = 0 :=
      hyperp _ (Submodule.subset_span (by simp))
    obtain ⟨hz2, hz3⟩ := coord_eq_zero_of_mem_U4 hzU
    rw [show Wequiv.toLinearMap z = Wlin z from rfl] at h1 h2 ⊢
    rw [sv, EuclideanSpace.inner_single_left] at h1 h2
    rw [Wlin_apply] at h1 h2
    simp only [Fin.sum_univ_four, conj_trivial, one_mul] at h1 h2
    have hz0 : z 0 = 0 := by
      simp only [Wmat, Matrix.smul_apply] at h1 h2
      norm_num [hz2, hz3] at h1 h2
      linarith
    have hz1 : z 1 = 0 := by
      simp only [Wmat, Matrix.smul_apply] at h1 h2
      norm_num [hz2, hz3] at h1 h2
      linarith
    rw [show z = 0 from by rw [mem_U4 hzU, hz0, hz1]; simp]
    simp

/-- The Gram operator of the canonical intertwiner is `½·I`: both principal
angles are `π/4`, so `S⋆S = cos²(π/4)·I = ½·I` on the whole space. -/
theorem gram_canonicalIntertwiner :
    (canonicalIntertwiner U4 V4).adjoint ∘ₗ canonicalIntertwiner U4 V4 =
      (2⁻¹ : ℝ) • LinearMap.id := by
  rw [canonicalIntertwiner_adjoint_comp_self]
  apply LinearMap.ext
  intro x
  ext i
  have hcU : ∀ y : E4, complementaryProjection U4 y = y - projection U4 y :=
    fun y => Submodule.starProjection_orthogonal_val y
  have hcV : ∀ y : E4, complementaryProjection V4 y = y - projection V4 y :=
    fun y => Submodule.starProjection_orthogonal_val y
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply, hcU, hcV, map_sub]
  fin_cases i <;>
    simp [projection_U4_coord, projection_V4_coord] <;> ring

/-- The operator cosine is the scalar `√½`. -/
theorem abs_canonicalIntertwiner_eq :
    TauCeti.operatorAbs (canonicalIntertwiner U4 V4) =
      Real.sqrt 2⁻¹ • LinearMap.id := by
  have hpos : (Real.sqrt 2⁻¹ • (LinearMap.id : E4 →ₗ[ℝ] E4)).IsPositive := by
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · simp only [LinearMap.smul_apply, LinearMap.id_apply]
      rw [real_inner_smul_left, real_inner_smul_right]
    · simp only [LinearMap.smul_apply, LinearMap.id_apply]
      rw [real_inner_smul_left]
      have := real_inner_self_nonneg (x := x)
      have := Real.sqrt_nonneg (2⁻¹ : ℝ)
      simp
  have hsq : (Real.sqrt 2⁻¹ • (LinearMap.id : E4 →ₗ[ℝ] E4)) ∘ₗ
      (Real.sqrt 2⁻¹ • LinearMap.id) =
      (canonicalIntertwiner U4 V4).adjoint ∘ₗ canonicalIntertwiner U4 V4 := by
    rw [gram_canonicalIntertwiner]
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
      smul_smul]
    rw [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2⁻¹)]
  exact ((LinearMap.isPositive_adjoint_comp_self _).sqrt_unique hpos hsq).symm

private theorem sqrt_two_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 :=
  Real.mul_self_sqrt (by norm_num)

private theorem sqrt_half_eq : Real.sqrt 2⁻¹ = Real.sqrt 2 / 2 := by
  rw [Real.sqrt_inv]
  have h0 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  exact (Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)).symm

/-- The displacement square of the direct rotation is the scalar `2-√2`. -/
theorem displacementSquare_R :
    displacementSquare (directRotation U4 V4 acute).toLinearMap =
      (2 - Real.sqrt 2) • LinearMap.id := by
  rw [displacementSquare_directRotation U4 V4 acute, abs_canonicalIntertwiner_eq]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply,
    smul_sub, smul_smul]
  rw [sqrt_half_eq]
  match_scalars
  ring

/-- The Gram operator of the direct displacement `I - R`. -/
theorem gram_displacement_R :
    LinearMap.adjoint (LinearMap.id -
        (directRotation U4 V4 acute).toLinearMap) ∘ₗ
      (LinearMap.id - (directRotation U4 V4 acute).toLinearMap) =
      (2 - Real.sqrt 2) • LinearMap.id := by
  rw [map_sub, LinearMap.adjoint_id, ← displacementSquare_R]
  rfl

private theorem two_sub_sqrt_two_nonneg : (0:ℝ) ≤ 2 - Real.sqrt 2 := by
  nlinarith [sqrt_two_mul_self, Real.sqrt_nonneg 2]

/-- Every singular value of `I - R` is the constant chord `√(2-√2)`. -/
theorem singularValues_displacement_R (j : Fin 4) :
    (LinearMap.id -
        (directRotation U4 V4 acute).toLinearMap).singularValues (j : ℕ) =
      Real.sqrt (2 - Real.sqrt 2) := by
  set D := LinearMap.id - (directRotation U4 V4 acute).toLinearMap with hD
  have hfr : finrank ℝ E4 = 4 := finrank_euclideanSpace_fin
  have heig := LinearMap.IsSymmetric.eigenvalues_eq_of_eigenbasis D.isSymmetric_adjoint_comp_self hfr
    (EuclideanSpace.basisFun (Fin 4) ℝ)
    (μ := fun _ => 2 - Real.sqrt 2) (fun _ _ _ => le_rfl)
    (fun i => by
      rw [show LinearMap.adjoint D ∘ₗ D = (2 - Real.sqrt 2) • LinearMap.id from
        gram_displacement_R]
      simp)
  rw [D.singularValues_of_lt hfr j.isLt, congrFun heig ⟨(j : ℕ), j.isLt⟩]

/-- The trace norm of the direct displacement is `4√(2-√2)`. -/
theorem kyFanSum_displacement_R :
    kyFanSum 4 (LinearMap.id - (directRotation U4 V4 acute).toLinearMap) =
      4 * Real.sqrt (2 - Real.sqrt 2) := by
  rw [kyFanSum_eq_sum_fin, Fin.sum_univ_four]
  rw [singularValues_displacement_R 0, singularValues_displacement_R 1,
    singularValues_displacement_R 2, singularValues_displacement_R 3]
  ring

/-! ### The competitor side: `σ(I-W) = (√2, √2, 0, 0)` -/

/-- The rotation-plane orthonormal family `(m₀, m₁, m₀', m₁')`. -/
noncomputable def mv : Fin 4 → E4 :=
  ![(Real.sqrt 2)⁻¹ • (sv 0 + sv 2), (Real.sqrt 2)⁻¹ • (sv 1 + sv 3),
    (Real.sqrt 2)⁻¹ • (sv 0 - sv 2), (Real.sqrt 2)⁻¹ • (sv 1 - sv 3)]

private theorem orthonormal_mv : Orthonormal ℝ mv := by
  have h2 := sqrt_two_mul_self
  have h0 : Real.sqrt 2 ≠ 0 := by positivity
  have hh : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 2⁻¹ := by
    field_simp
    linarith [h2]
  constructor
  · intro i
    have key : ∀ v : E4, ⟪v, v⟫_ℝ = 1 → ‖v‖ = 1 := by
      intro v hv
      have hsq : ‖v‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, hv]
      nlinarith [norm_nonneg v]
    fin_cases i <;>
      refine key _ ?_ <;>
      · simp only [mv,
          PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
          Fin.sum_univ_four]
        simp [sv]
        nlinarith [hh]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | simp [mv, sv, inner_add_left, inner_add_right,
          inner_sub_right, real_inner_smul_right,
          EuclideanSpace.inner_single_right,
          hh]

/-- The family as an orthonormal basis. -/
noncomputable def mbasis : OrthonormalBasis (Fin 4) ℝ E4 :=
  (basisOfLinearIndependentOfCardEqFinrank (b := mv) (by exact orthonormal_mv.linearIndependent)
    (by simp [])).toOrthonormalBasis
    (by
      rw [coe_basisOfLinearIndependentOfCardEqFinrank]
      exact orthonormal_mv)

private theorem mbasis_coe (i : Fin 4) : mbasis i = mv i := by
  rw [mbasis]
  rw [show ⇑((basisOfLinearIndependentOfCardEqFinrank
      orthonormal_mv.linearIndependent
      (by simp [])).toOrthonormalBasis _) =
    ⇑(basisOfLinearIndependentOfCardEqFinrank
      orthonormal_mv.linearIndependent
      (by simp [])) from
    Module.Basis.coe_toOrthonormalBasis _ _,
    coe_basisOfLinearIndependentOfCardEqFinrank]

/-- `W` rotates the plane `(m₀, m₁)` by a quarter turn. -/
theorem Wlin_mv0 : Wlin (mv 0) = mv 1 := by
  ext i
  simp only [mv]
  rw [show (![(Real.sqrt 2)⁻¹ • (sv 0 + sv 2), (Real.sqrt 2)⁻¹ • (sv 1 + sv 3),
    (Real.sqrt 2)⁻¹ • (sv 0 - sv 2), (Real.sqrt 2)⁻¹ • (sv 1 - sv 3)] :
      Fin 4 → E4) 0 = (Real.sqrt 2)⁻¹ • (sv 0 + sv 2) from rfl]
  rw [map_smul]
  rw [show Wlin (sv 0 + sv 2) = Wlin (sv 0) + Wlin (sv 2) from map_add _ _ _]
  fin_cases i <;>
    simp [Wlin_apply, Wmat, sv, PiLp.single_apply,
      Matrix.smul_apply] <;> ring

private theorem Wlin_mv1 : Wlin (mv 1) = -mv 0 := by
  ext i
  simp only [mv]
  rw [show (![(Real.sqrt 2)⁻¹ • (sv 0 + sv 2), (Real.sqrt 2)⁻¹ • (sv 1 + sv 3),
    (Real.sqrt 2)⁻¹ • (sv 0 - sv 2), (Real.sqrt 2)⁻¹ • (sv 1 - sv 3)] :
      Fin 4 → E4) 1 = (Real.sqrt 2)⁻¹ • (sv 1 + sv 3) from rfl]
  rw [map_smul]
  fin_cases i <;>
    simp [Wlin_apply, Wmat, sv, PiLp.single_apply,
      Matrix.smul_apply] <;> ring

private theorem Wlin_mv2 : Wlin (mv 2) = mv 2 := by
  ext i
  simp only [mv]
  rw [show (![(Real.sqrt 2)⁻¹ • (sv 0 + sv 2), (Real.sqrt 2)⁻¹ • (sv 1 + sv 3),
    (Real.sqrt 2)⁻¹ • (sv 0 - sv 2), (Real.sqrt 2)⁻¹ • (sv 1 - sv 3)] :
      Fin 4 → E4) 2 = (Real.sqrt 2)⁻¹ • (sv 0 - sv 2) from rfl]
  rw [map_smul]
  fin_cases i <;>
    simp [Wlin_apply, Wmat, sv, PiLp.single_apply,
      Matrix.smul_apply] <;> ring

private theorem Wlin_mv3 : Wlin (mv 3) = mv 3 := by
  ext i
  simp only [mv]
  rw [show (![(Real.sqrt 2)⁻¹ • (sv 0 + sv 2), (Real.sqrt 2)⁻¹ • (sv 1 + sv 3),
    (Real.sqrt 2)⁻¹ • (sv 0 - sv 2), (Real.sqrt 2)⁻¹ • (sv 1 - sv 3)] :
      Fin 4 → E4) 3 = (Real.sqrt 2)⁻¹ • (sv 1 - sv 3) from rfl]
  rw [map_smul]
  fin_cases i <;>
    simp [Wlin_apply, Wmat, sv, PiLp.single_apply,
      Matrix.smul_apply] <;> ring

private theorem Wlin'_mv0 : Wlin' (mv 0) = -mv 1 := by
  have h : Wlin' (Wlin (mv 1)) = mv 1 := LinearMap.congr_fun Wlin'_comp_Wlin _
  rw [Wlin_mv1, map_neg] at h
  exact neg_eq_iff_eq_neg.mp h

private theorem Wlin'_mv1 : Wlin' (mv 1) = mv 0 := by
  have h : Wlin' (Wlin (mv 0)) = mv 0 := LinearMap.congr_fun Wlin'_comp_Wlin _
  rw [Wlin_mv0] at h
  exact h

private theorem Wlin'_mv2 : Wlin' (mv 2) = mv 2 := by
  have h : Wlin' (Wlin (mv 2)) = mv 2 := LinearMap.congr_fun Wlin'_comp_Wlin _
  rw [Wlin_mv2] at h
  exact h

private theorem Wlin'_mv3 : Wlin' (mv 3) = mv 3 := by
  have h : Wlin' (Wlin (mv 3)) = mv 3 := LinearMap.congr_fun Wlin'_comp_Wlin _
  rw [Wlin_mv3] at h
  exact h

/-- The Gram operator of `I - W` acts diagonally on the rotation basis with
values `(2, 2, 0, 0)`; stated one basis vector at a time so every index is a
literal. -/
theorem gram_displacement_W_mv0 :
    (LinearMap.adjoint (LinearMap.id - Wlin) ∘ₗ (LinearMap.id - Wlin))
        (mbasis 0) = (2 : ℝ) • mbasis 0 := by
  rw [map_sub, LinearMap.adjoint_id, Wlin_adjoint]
  simp only [mbasis_coe, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.id_apply, map_sub, Wlin_mv0, Wlin'_mv0, Wlin'_mv1]
  module

private theorem gram_displacement_W_mv1 :
    (LinearMap.adjoint (LinearMap.id - Wlin) ∘ₗ (LinearMap.id - Wlin))
        (mbasis 1) = (2 : ℝ) • mbasis 1 := by
  rw [map_sub, LinearMap.adjoint_id, Wlin_adjoint]
  simp only [mbasis_coe, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.id_apply, map_sub, Wlin_mv1, Wlin'_mv1, Wlin'_mv0, map_neg]
  module

private theorem gram_displacement_W_mv2 :
    (LinearMap.adjoint (LinearMap.id - Wlin) ∘ₗ (LinearMap.id - Wlin))
        (mbasis 2) = (0 : ℝ) • mbasis 2 := by
  rw [map_sub, LinearMap.adjoint_id, Wlin_adjoint]
  simp only [mbasis_coe, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.id_apply, map_sub, Wlin_mv2, Wlin'_mv2]
  module

private theorem gram_displacement_W_mv3 :
    (LinearMap.adjoint (LinearMap.id - Wlin) ∘ₗ (LinearMap.id - Wlin))
        (mbasis 3) = (0 : ℝ) • mbasis 3 := by
  rw [map_sub, LinearMap.adjoint_id, Wlin_adjoint]
  simp only [mbasis_coe, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.id_apply, map_sub, Wlin_mv3, Wlin'_mv3]
  module

private theorem gram_displacement_W_apply (i : Fin 4) :
    (LinearMap.adjoint (LinearMap.id - Wlin) ∘ₗ (LinearMap.id - Wlin))
        (mbasis i) =
      ((![2, 2, 0, 0] : Fin 4 → ℝ) i) • mbasis i := by
  fin_cases i
  · exact gram_displacement_W_mv0
  · exact gram_displacement_W_mv1
  · exact gram_displacement_W_mv2
  · exact gram_displacement_W_mv3

private theorem antitone_two_two_zero_zero :
    Antitone (![2, 2, 0, 0] : Fin 4 → ℝ) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- Singular values of the competitor displacement. -/
theorem singularValues_displacement_W (j : Fin 4) :
    (LinearMap.id - Wlin).singularValues (j : ℕ) =
      Real.sqrt ((![2, 2, 0, 0] : Fin 4 → ℝ) j) := by
  set D := LinearMap.id - Wlin with hD
  have hfr : finrank ℝ E4 = 4 := finrank_euclideanSpace_fin
  have heig := LinearMap.IsSymmetric.eigenvalues_eq_of_eigenbasis
    D.isSymmetric_adjoint_comp_self hfr mbasis
    (μ := ![2, 2, 0, 0]) antitone_two_two_zero_zero
    (fun i => gram_displacement_W_apply i)
  rw [D.singularValues_of_lt hfr j.isLt, congrFun heig ⟨(j : ℕ), j.isLt⟩]

/-- The trace norm of the competitor displacement is `2√2`. -/
theorem kyFanSum_displacement_W :
    kyFanSum 4 (LinearMap.id - Wlin) = 2 * Real.sqrt 2 := by
  rw [kyFanSum_eq_sum_fin, Fin.sum_univ_four]
  simp only [singularValues_displacement_W 0, singularValues_displacement_W 1,
    singularValues_displacement_W 2, singularValues_displacement_W 3,
    show ((![2, 2, 0, 0] : Fin 4 → ℝ) 2) = 0 from rfl,
    show ((![2, 2, 0, 0] : Fin 4 → ℝ) 3) = 0 from rfl,
    show ((![2, 2, 0, 0] : Fin 4 → ℝ) 0) = 2 from rfl,
    show ((![2, 2, 0, 0] : Fin 4 → ℝ) 1) = 2 from rfl,
    Real.sqrt_zero]
  ring

/-! ### The printed equation (4.3) fails on the same witness

For the equal-angle configuration the two Davis--Kahan principal planes may be
chosen as `span{e₀,e₃}` and `span{e₁,e₂}`.  If `K = I - W` and `Ω₁, Ω₂` are
the corresponding orthogonal projections, the printed proof of Proposition 4.4
uses the inequality

`kyFanSum 4 K ≥ kyFanSum 2 (K ∘ Ω₁) + kyFanSum 2 (K ∘ Ω₂)`.

The declarations below certify the opposite strict inequality: each block has
Ky Fan two sum `2`, while the full displacement has Ky Fan four sum `2√2`.
This localizes the source-proof defect independently of the theorem-level
refutation below. -/

/-- The first principal plane used to test Davis--Kahan equation (4.3). -/
noncomputable def omega1 : Submodule ℝ E4 := Submodule.span ℝ {sv 0, sv 3}

/-- The second principal plane used to test Davis--Kahan equation (4.3). -/
noncomputable def omega2 : Submodule ℝ E4 := Submodule.span ℝ {sv 1, sv 2}

private theorem mem_omega1 {x : E4} (hx : x ∈ omega1) :
    x = x 0 • sv 0 + x 3 • sv 3 := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  ext i
  fin_cases i <;> simp [sv]

private theorem mem_omega2 {x : E4} (hx : x ∈ omega2) :
    x = x 1 • sv 1 + x 2 • sv 2 := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  ext i
  fin_cases i <;> simp [sv]

private theorem projection_omega1_apply (x : E4) :
    projection omega1 x = x 0 • sv 0 + x 3 • sv 3 := by
  change omega1.starProjection x = _
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact add_mem
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · rw [Submodule.mem_orthogonal]
    intro u hu
    rw [mem_omega1 hu]
    simp [sv, inner_add_left, inner_sub_right, real_inner_smul_left,
      EuclideanSpace.inner_single_left]

private theorem projection_omega2_apply (x : E4) :
    projection omega2 x = x 1 • sv 1 + x 2 • sv 2 := by
  change omega2.starProjection x = _
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact add_mem
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · rw [Submodule.mem_orthogonal]
    intro u hu
    rw [mem_omega2 hu]
    simp [sv, inner_add_left, inner_sub_right, real_inner_smul_left,
      EuclideanSpace.inner_single_left]

private theorem projection_omega1_coord (x : E4) (i : Fin 4) :
    projection omega1 x i =
      if i = 0 then x 0 else if i = 3 then x 3 else 0 := by
  rw [projection_omega1_apply]
  fin_cases i <;> simp [sv]

private theorem projection_omega2_coord (x : E4) (i : Fin 4) :
    projection omega2 x i =
      if i = 1 then x 1 else if i = 2 then x 2 else 0 := by
  rw [projection_omega2_apply]
  fin_cases i <;> simp [sv]

/-- The first block `K Ω₁` from the printed equation (4.3), for `K = I-W`. -/
noncomputable def equation43Block1 : E4 →ₗ[ℝ] E4 :=
  (LinearMap.id - Wlin) ∘ₗ projection omega1

/-- The second block `K Ω₂` from the printed equation (4.3), for `K = I-W`. -/
noncomputable def equation43Block2 : E4 →ₗ[ℝ] E4 :=
  (LinearMap.id - Wlin) ∘ₗ projection omega2

private theorem gram_equation43Block1 :
    LinearMap.adjoint equation43Block1 ∘ₗ equation43Block1 =
      projection omega1 := by
  apply LinearMap.ext
  intro x
  ext i
  rw [equation43Block1, LinearMap.adjoint_comp, projection_adjoint,
    map_sub, LinearMap.adjoint_id, Wlin_adjoint]
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
  fin_cases i <;>
    simp [projection_omega1_coord, Wlin_apply, Wlin'_apply, Wmat,
      Fin.sum_univ_four, Matrix.smul_apply] <;> ring

private theorem gram_equation43Block2 :
    LinearMap.adjoint equation43Block2 ∘ₗ equation43Block2 =
      projection omega2 := by
  apply LinearMap.ext
  intro x
  ext i
  rw [equation43Block2, LinearMap.adjoint_comp, projection_adjoint,
    map_sub, LinearMap.adjoint_id, Wlin_adjoint]
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
  fin_cases i <;>
    simp [projection_omega2_coord, Wlin_apply, Wlin'_apply, Wmat,
      Fin.sum_univ_four, Matrix.smul_apply] <;> ring

private noncomputable def omega1Basis : OrthonormalBasis (Fin 4) ℝ E4 :=
  (EuclideanSpace.basisFun (Fin 4) ℝ).reindex (Equiv.swap (1 : Fin 4) 3)

private noncomputable def omega2Basis : OrthonormalBasis (Fin 4) ℝ E4 :=
  omega1Basis.reindex Fin.revPerm

private theorem omega1Basis_projection (i : Fin 4) :
    projection omega1 (omega1Basis i) =
      ((![1, 1, 0, 0] : Fin 4 → ℝ) i) • omega1Basis i := by
  have hswap0 : (Equiv.swap (1 : Fin 4) 3) 0 = 0 := by decide
  have hswap1 : (Equiv.swap (1 : Fin 4) 3) 1 = 3 := by decide
  have hswap2 : (Equiv.swap (1 : Fin 4) 3) 2 = 2 := by decide
  have hswap3 : (Equiv.swap (1 : Fin 4) 3) 3 = 1 := by decide
  fin_cases i <;>
    ext j <;> fin_cases j <;>
    simp [omega1Basis, projection_omega1_coord,
      EuclideanSpace.basisFun_apply, hswap0, hswap1, hswap2, hswap3]

private theorem omega2Basis_projection (i : Fin 4) :
    projection omega2 (omega2Basis i) =
      ((![1, 1, 0, 0] : Fin 4 → ℝ) i) • omega2Basis i := by
  have hswap0 : (Equiv.swap (1 : Fin 4) 3) 0 = 0 := by decide
  have hswap1 : (Equiv.swap (1 : Fin 4) 3) 1 = 3 := by decide
  have hswap2 : (Equiv.swap (1 : Fin 4) 3) 2 = 2 := by decide
  have hswap3 : (Equiv.swap (1 : Fin 4) 3) 3 = 1 := by decide
  fin_cases i <;>
    ext j <;> fin_cases j <;>
    simp [omega2Basis, omega1Basis, projection_omega2_coord,
      EuclideanSpace.basisFun_apply, hswap0, hswap1, hswap2, hswap3]

private theorem antitone_one_one_zero_zero :
    Antitone (![1, 1, 0, 0] : Fin 4 → ℝ) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private theorem singularValues_equation43Block1 (j : Fin 4) :
    equation43Block1.singularValues (j : ℕ) =
      Real.sqrt ((![1, 1, 0, 0] : Fin 4 → ℝ) j) := by
  have hfr : finrank ℝ E4 = 4 := finrank_euclideanSpace_fin
  have heig := LinearMap.IsSymmetric.eigenvalues_eq_of_eigenbasis
    equation43Block1.isSymmetric_adjoint_comp_self hfr omega1Basis
    (μ := ![1, 1, 0, 0]) antitone_one_one_zero_zero
    (fun i => by rw [gram_equation43Block1]; exact omega1Basis_projection i)
  rw [equation43Block1.singularValues_of_lt hfr j.isLt,
    congrFun heig ⟨(j : ℕ), j.isLt⟩]

private theorem singularValues_equation43Block2 (j : Fin 4) :
    equation43Block2.singularValues (j : ℕ) =
      Real.sqrt ((![1, 1, 0, 0] : Fin 4 → ℝ) j) := by
  have hfr : finrank ℝ E4 = 4 := finrank_euclideanSpace_fin
  have heig := LinearMap.IsSymmetric.eigenvalues_eq_of_eigenbasis
    equation43Block2.isSymmetric_adjoint_comp_self hfr omega2Basis
    (μ := ![1, 1, 0, 0]) antitone_one_one_zero_zero
    (fun i => by rw [gram_equation43Block2]; exact omega2Basis_projection i)
  rw [equation43Block2.singularValues_of_lt hfr j.isLt,
    congrFun heig ⟨(j : ℕ), j.isLt⟩]

/-- The first principal-plane block in equation (4.3) has Ky Fan two sum `2`. -/
theorem kyFanSum_equation43Block1 : kyFanSum 2 equation43Block1 = 2 := by
  have h0 : equation43Block1.singularValues 0 = 1 := by
    simpa using singularValues_equation43Block1 (0 : Fin 4)
  have h1 : equation43Block1.singularValues 1 = 1 := by
    simpa using singularValues_equation43Block1 (1 : Fin 4)
  rw [kyFanSum_eq_sum_fin, Fin.sum_univ_two]
  change equation43Block1.singularValues 0 +
      equation43Block1.singularValues 1 = 2
  rw [h0, h1]
  norm_num

/-- The second principal-plane block in equation (4.3) has Ky Fan two sum `2`. -/
theorem kyFanSum_equation43Block2 : kyFanSum 2 equation43Block2 = 2 := by
  have h0 : equation43Block2.singularValues 0 = 1 := by
    simpa using singularValues_equation43Block2 (0 : Fin 4)
  have h1 : equation43Block2.singularValues 1 = 1 := by
    simpa using singularValues_equation43Block2 (1 : Fin 4)
  rw [kyFanSum_eq_sum_fin, Fin.sum_univ_two]
  change equation43Block2.singularValues 0 +
      equation43Block2.singularValues 1 = 2
  rw [h0, h1]
  norm_num

/-- **Davis--Kahan 1970, equation (4.3), is false in the generality used in the
proof of Proposition 4.4.**  For the same `ℝ⁴` witness as the proposition-level
counterexample, the global Ky Fan four sum is `2√2`, whereas the two Ky Fan two
principal-plane terms sum to `4`; hence the printed lower bound points in the
wrong direction on this admissible configuration. -/
theorem davisKahanEquation4_3_refuted :
    kyFanSum 4 (LinearMap.id - Wlin) <
      kyFanSum 2 equation43Block1 + kyFanSum 2 equation43Block2 := by
  rw [kyFanSum_displacement_W, kyFanSum_equation43Block1,
    kyFanSum_equation43Block2]
  have hsqrt : Real.sqrt 2 < 2 := by
    nlinarith [sqrt_two_mul_self, Real.sqrt_nonneg 2]
  nlinarith

/-! ### The principal angles are `π/4` -/

/-- The Gram operator of the directed sine map acts diagonally on the standard
basis with values `(½, ½, 0, 0)`. -/
theorem gram_sinThetaMap_apply (i : Fin 4) :
    ((sinThetaMap U4 V4).adjoint ∘ₗ sinThetaMap U4 V4)
        (EuclideanSpace.basisFun (Fin 4) ℝ i) =
      ((![2⁻¹, 2⁻¹, 0, 0] : Fin 4 → ℝ) i) •
        EuclideanSpace.basisFun (Fin 4) ℝ i := by
  have hAadj : (sinThetaMap U4 V4).adjoint =
      projection U4 ∘ₗ complementaryProjection V4 := by
    rw [sinThetaMap, LinearMap.adjoint_comp, projection_adjoint]
    congr 1
    simp [complementaryProjection]
  rw [hAadj, sinThetaMap]
  have hcV : ∀ y : E4, complementaryProjection V4 y = y - projection V4 y :=
    fun y => Submodule.starProjection_orthogonal_val y
  apply PiLp.ext
  intro k
  simp only [LinearMap.comp_apply, hcV, map_sub]
  fin_cases i <;> fin_cases k <;>
    simp [projection_U4_coord, projection_V4_coord,
      EuclideanSpace.basisFun_apply] <;> ring

private theorem antitone_half_half_zero_zero :
    Antitone (![2⁻¹, 2⁻¹, 0, 0] : Fin 4 → ℝ) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- The largest principal sine is `√½`. -/
theorem principalSines_zero : principalSines U4 V4 0 = Real.sqrt 2⁻¹ := by
  have hfr : finrank ℝ E4 = 4 := finrank_euclideanSpace_fin
  have heig := LinearMap.IsSymmetric.eigenvalues_eq_of_eigenbasis
    (sinThetaMap U4 V4).isSymmetric_adjoint_comp_self hfr
    (EuclideanSpace.basisFun (Fin 4) ℝ)
    (μ := ![2⁻¹, 2⁻¹, 0, 0]) antitone_half_half_zero_zero
    (fun i => gram_sinThetaMap_apply i)
  rw [principalSines]
  rw [(sinThetaMap U4 V4).singularValues_of_lt hfr (by norm_num : 0 < 4),
    congrFun heig ⟨0, by norm_num⟩]
  norm_num

/-- Both principal angles are `π/4 ≤ π/3`. -/
theorem principalAngle_le : principalAngles U4 V4 0 ≤ Real.pi / 3 := by
  rw [principalAngles, Finsupp.mapRange_apply, principalSines_zero]
  have hval : Real.sqrt 2⁻¹ = Real.sin (Real.pi / 4) := by
    rw [Real.sin_pi_div_four, sqrt_half_eq]
  rw [hval, Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
  linarith [Real.pi_pos]

/-! ### The refutation -/

/-- The competitor beats the direct rotation in trace norm. -/
theorem kyFanSum_lt :
    kyFanSum 4 (LinearMap.id - Wequiv.toLinearMap) <
      kyFanSum 4 (LinearMap.id -
        (directRotation U4 V4 acute).toLinearMap) := by
  rw [Wequiv_toLinearMap, kyFanSum_displacement_W, kyFanSum_displacement_R]
  have h2 := sqrt_two_mul_self
  have hs2 : Real.sqrt 2 < 3 / 2 := by
    nlinarith [Real.sqrt_nonneg 2]
  have hchord : Real.sqrt (2 - Real.sqrt 2) *
      Real.sqrt (2 - Real.sqrt 2) = 2 - Real.sqrt 2 :=
    Real.mul_self_sqrt two_sub_sqrt_two_nonneg
  have hsq : (2 * Real.sqrt 2) ^ 2 < (4 * Real.sqrt (2 - Real.sqrt 2)) ^ 2 := by
    nlinarith [h2, hchord, hs2]
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq

end

end ShortRotationCounterexample

open ShortRotationCounterexample in
/-- **The transcribed short-rotation Proposition 4.4 is false.**  There is an
acute pair of subspaces of `ℝ⁴` whose principal angles are all at most `π/3`
together with a unitary competitor carrying `U` onto `V` whose full
displacement `I - W` has strictly smaller trace norm (`kyFanSum 4`) than the
direct rotation's — so no unitarily invariant norm minimality of the full
displacement can hold under a largest-angle hypothesis.  The valid endpoints
are `uiNorm_restrictedDisplacement_le` (restricted displacement, no angle
hypothesis) and `directRotation_displacementSquare_uiNorm` (displacement
square). -/
theorem shortRotation_fullDisplacement_refuted :
    ∃ (U V : Submodule ℝ (EuclideanSpace ℝ (Fin 4)))
      (hacute : IsAcute U V)
      (W : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)),
      U.map W.toLinearMap = V ∧
      principalAngles U V 0 ≤ Real.pi / 3 ∧
      kyFanSum 4 (LinearMap.id - W.toLinearMap) <
        kyFanSum 4 (LinearMap.id - (directRotation U V hacute).toLinearMap) :=
  ⟨U4, V4, acute, Wequiv, rfl, principalAngle_le, kyFanSum_lt⟩

/-! ### The source claim as a single proposition

`shortRotation_fullDisplacement_refuted` exhibits a competitor beating the
direct rotation in one particular unitarily invariant norm.  To refute the
source claim *as stated* — "for every unitarily invariant norm" — that Ky Fan
sum must be presented as an inhabitant of `UnitarilyInvariantSeminorm`, which is
what `UnitarilyInvariantSeminorm.kyFan _ |>` supplies. -/

/-- **The transcribed Davis--Kahan Proposition 4.4**, in the finite-dimensional
specialization: over a real inner-product space, if the largest principal angle
is at most `π/3`, then the direct rotation minimizes *every* unitarily
invariant norm of the full displacement `1 - V`, over unitaries `V` carrying
`U` onto `V`.

This is a `Prop`-valued definition rather than a theorem because the assertion
is false; see `not_davisKahanProposition4_4_Finite`.  The `IsAcute` hypothesis
is not an extra mathematical restriction: `Θ ≤ π/3` already excludes a right
principal angle, and acuteness is what the direct-rotation constructor
consumes. -/
def DavisKahanProposition4Point4Finite : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (_hshort : principalAngles U V 0 ≤ Real.pi / 3)
    (W : E ≃ₗᵢ[ℝ] E)
    (_hmap : U.map W.toLinearMap = V)
    (N : UnitarilyInvariantSeminorm ℝ E E),
      N (LinearMap.id - (directRotation U V hacute).toLinearMap) ≤
        N (LinearMap.id - W.toLinearMap)

open ShortRotationCounterexample in
/-- **The transcribed Proposition 4.4 is false**, in the "every unitarily
invariant norm" form in which the source states it.  The witnessing norm is the
trace norm of `ℝ⁴`, presented as the bundled unitarily invariant norm
`(UnitarilyInvariantSeminorm.kyFan 4)`, whose underlying
function is `kyFanSum 4`.

Stated at universe `0`, where the witness `EuclideanSpace ℝ (Fin 4)` lives.
Lean cannot quantify over universes, so `¬ P.{0}` is the strongest available
refutation of the universe-polymorphic `P`; and since a polymorphic `P` holds
only if it holds at every universe, refuting `P.{0}` refutes `P`. -/
theorem not_davisKahanProposition4_4_Finite :
    ¬ DavisKahanProposition4Point4Finite.{0} := by
  intro h
  have hN := h E4 U4 V4 acute principalAngle_le Wequiv rfl
    (UnitarilyInvariantSeminorm.kyFan (𝕜 := ℝ) (E := E4) (F := E4) 4)
  have hle : kyFanSum 4 (LinearMap.id - (directRotation U4 V4 acute).toLinearMap) ≤
      kyFanSum 4 (LinearMap.id - Wequiv.toLinearMap) := by
    simpa only [UnitarilyInvariantSeminorm.kyFan_apply] using hN
  exact absurd hle (not_le.mpr kyFanSum_lt)

open ShortRotationCounterexample in
/-- **The trace norm is not a `Q`-norm.**  Read in the other direction, the
counterexample separates the two norm classes: `directRotation_fullDisplacement_qnorm`
holds for every `Q`-norm without a largest-angle threshold, so any norm violating
full-displacement minimality — as `kyFanSum 4` does on `ℝ⁴` — cannot be one.

This is the formal counterpart of the classical fact that the Schatten `Q`-norms
are exactly those with `2 ≤ p ≤ ∞`: the trace norm is the `p = 1` endpoint. -/
theorem kyFan_not_isQNorm :
    ¬ IsQNorm (UnitarilyInvariantSeminorm.kyFan
      (𝕜 := ℝ) (E := E4) (F := E4) 4) := by
  intro hQ
  have hle := directRotation_fullDisplacement_qnorm _ hQ U4 V4 acute Wequiv rfl
  have hle' : kyFanSum 4 (LinearMap.id - (directRotation U4 V4 acute).toLinearMap) ≤
      kyFanSum 4 (LinearMap.id - Wequiv.toLinearMap) := by
    simpa only [UnitarilyInvariantSeminorm.kyFan_apply] using hle
  exact absurd hle' (not_le.mpr kyFanSum_lt)

end DavisKahan.FiniteDimensional
end TauCeti
