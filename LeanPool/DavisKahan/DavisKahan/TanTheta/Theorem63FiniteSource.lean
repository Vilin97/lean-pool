/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem
import LeanPool.DavisKahan.DavisKahan.Sylvester.Spectrum
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.KyFanOrthonormal
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtFiniteRank
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.FiniteSourceSingularSystem
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.DiagonalOperator
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Singular.Subspace
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SpectralOrder

/-! # Theorem63Finite Source -/

open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Theorem 6.3 with finite trial coordinates

The literal theorem is stated in a separable Hilbert space and assumes

`dim X(E₀) < dim X(F₀)`.

Because every infinite-dimensional closed subspace of a separable Hilbert
space has the same countable Hilbert dimension, the smaller coordinate space
`X(E₀)` is finite-dimensional.  The ambient Hilbert space and the wanted and
unwanted exact spectral subspaces may still be infinite-dimensional.

This module closes precisely that gap.  It generalizes the already compiled
finite-dimensional singular-vector proof in
`FiniteDimensional/TanTheta/RitzResidual.lean` from a finite ambient space to
an arbitrary complete ambient Hilbert space while retaining a finite trial
coordinate space.  Approximation numbers replace the finite rectangular norm
surface, so Fan dominance promotes the Ky Fan inequalities to every supported
unitarily invariant ideal gauge.

The theorem is directed: it controls the tangent associated with
`P_{Vᗮ}|_Z`.  It does not assert symmetric acuteness of the unequal-dimensional
pair `Z,V`.
-/

open scoped InnerProductSpace BigOperators

namespace TauCeti

open TauCeti
namespace DavisKahan
namespace TanTheta

open ExactSinTheta
open Module (finrank)

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The directed sine block from finite trial coordinates into the unwanted
exact subspace. -/
noncomputable def theorem63DirectedSineBlock
    (Z V : Submodule ℂ H) 
    [V.HasOrthogonalProjection] : Z →L[ℂ] H :=
  Vᗮ.starProjection ∘L Z.subtypeL

/-- The Rayleigh--Ritz compression to the finite trial subspace. -/
noncomputable def theorem63Compression
    (T : H →L[ℂ] H) (Z : Submodule ℂ H)
    [Z.HasOrthogonalProjection] : Z →L[ℂ] Z :=
  Z.orthogonalProjectionOnto ∘L T ∘L Z.subtypeL

/-- The Rayleigh--Ritz residual of the finite trial subspace. -/
noncomputable def theorem63Residual
    (T : H →L[ℂ] H) (Z : Submodule ℂ H)
    [Z.HasOrthogonalProjection] : Z →L[ℂ] H :=
  T ∘L Z.subtypeL - Z.subtypeL ∘L theorem63Compression T Z

omit [CompleteSpace H] in
/-- The residual is the complementary projection of the ambient action. -/
theorem theorem63Residual_eq_complementaryProjection
    (T : H →L[ℂ] H) (Z : Submodule ℂ H)
    [Z.HasOrthogonalProjection] :
    theorem63Residual T Z = Zᗮ.starProjection ∘L T ∘L Z.subtypeL := by
  apply ContinuousLinearMap.ext
  intro z
  change T (z : H) -
      (Z.orthogonalProjectionOnto (T (z : H)) : H) =
    Zᗮ.starProjection (T (z : H))
  rw [Submodule.starProjection_orthogonal_apply]
  rfl

omit [CompleteSpace H] in
/-- Every Ritz residual vector is orthogonal to the trial subspace. -/
theorem theorem63Residual_apply_mem_orthogonal
    (T : H →L[ℂ] H) (Z : Submodule ℂ H)
    [Z.HasOrthogonalProjection] (z : Z) :
    theorem63Residual T Z z ∈ Zᗮ := by
  rw [theorem63Residual_eq_complementaryProjection]
  exact Zᗮ.starProjection_apply_mem _

omit [CompleteSpace H] in
/-- The projected residual satisfies the source Sylvester identity. -/
theorem theorem63_sylvester_identity
    (T : H →L[ℂ] H) (V Z : Submodule ℂ H)
    [V.HasOrthogonalProjection] [Z.HasOrthogonalProjection]
    (hV : T.Reduces V) :
    T ∘L theorem63DirectedSineBlock Z V -
        theorem63DirectedSineBlock Z V ∘L theorem63Compression T Z =
      Vᗮ.starProjection ∘L theorem63Residual T Z := by
  apply ContinuousLinearMap.ext
  intro z
  change T (Vᗮ.starProjection (z : H)) -
      Vᗮ.starProjection
        (theorem63Compression T Z z : H) =
    Vᗮ.starProjection
      (T (z : H) - (theorem63Compression T Z z : H))
  rw [map_sub]
  congr 1
  exact (ContinuousLinearMap.starProjection_apply_comm_of_reduces
    T Vᗮ (hV.orthogonalComplement) (z : H)).symm

omit [CompleteSpace H] in
/-- The directed sine block is a contraction. -/
theorem theorem63DirectedSineBlock_apply_norm_le
    (Z V : Submodule ℂ H) 
    [V.HasOrthogonalProjection] (z : Z) :
    ‖theorem63DirectedSineBlock Z V z‖ ≤ ‖z‖ := by
  calc
    ‖theorem63DirectedSineBlock Z V z‖ =
        ‖Vᗮ.starProjection (z : H)‖ := rfl
    _ ≤ ‖(z : H)‖ := Vᗮ.norm_starProjection_apply_le _
    _ = ‖z‖ := rfl

omit [CompleteSpace H] in
/-- The finite-source singular values of the directed sine block are at most
one. -/
theorem theorem63_singularValues_sine_le_one
    (Z V : Submodule ℂ H) [Z.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] [FiniteDimensional ℂ Z]
    (i : Fin (finrank ℂ Z)) :
    finiteSourceSingularValue (theorem63DirectedSineBlock Z V) i ≤ 1 := by
  exact finiteSourceSingularValue_le_one_of_contraction
    (theorem63DirectedSineBlock Z V)
    (theorem63DirectedSineBlock_apply_norm_le Z V) i

omit [CompleteSpace H] in
/-- The source spectral placement forces the directed cosine projection to be
injective.  This is the unequal-dimensional, directed replacement for the
false symmetric `IsUniformlyAcute Z V` claim. -/
theorem theorem63_directed_transverse_of_form_gap
    (T : H →L[ℂ] H) (_hT : T.IsSymmetric)
    (V Z : Submodule ℂ H) [V.HasOrthogonalProjection]
    [Z.HasOrthogonalProjection] (_hV : T.Reduces V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : Z,
      RCLike.re ⟪theorem63Compression T Z z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ) :
    Function.Injective (V.orthogonalProjectionOnto ∘L Z.subtypeL) := by
  intro x y hxy
  have hproj : V.starProjection (((x - y : Z) : H)) = 0 := by
    have hp := congrArg Subtype.val hxy
    change V.starProjection (x : H) = V.starProjection (y : H) at hp
    simpa [map_sub] using sub_eq_zero.mpr hp
  have hperp : ((x - y : Z) : H) ∈ Vᗮ :=
    (Submodule.starProjection_apply_eq_zero_iff V).mp hproj
  have hupper := hCompressionUpper (x - y)
  have hlower := hUnwantedLower ((x - y : Z) : H) hperp
  have hcomp :
      RCLike.re ⟪theorem63Compression T Z (x - y), x - y⟫_ℂ =
        RCLike.re ⟪T ((x - y : Z) : H), ((x - y : Z) : H)⟫_ℂ := by
    change RCLike.re
      ⟪Z.orthogonalProjectionOnto (T ((x - y : Z) : H)), x - y⟫_ℂ = _
    rw [Submodule.coe_inner, Submodule.coe_orthogonalProjectionOnto_apply,
      Z.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (x - y).2]
  have hnorm : ‖((x - y : Z) : H)‖ = ‖x - y‖ := rfl
  rw [← hcomp, hnorm] at hlower
  have hzero : x - y = 0 := by
    by_contra hne
    have hn : 0 < ‖x - y‖ := norm_pos_iff.mpr hne
    nlinarith [sq_pos_of_pos hn]
  exact sub_eq_zero.mp hzero

omit [CompleteSpace H] in
/-- Under the source gap every directed sine singular value is strictly below
one, so the tangent has no pole. -/
theorem theorem63_singularValues_sine_lt_one
    (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (V Z : Submodule ℂ H) [V.HasOrthogonalProjection]
    [Z.HasOrthogonalProjection] [FiniteDimensional ℂ Z]
    (hV : T.Reduces V) {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : Z,
      RCLike.re ⟪theorem63Compression T Z z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ)
    (i : Fin (finrank ℂ Z)) :
    finiteSourceSingularValue (theorem63DirectedSineBlock Z V) i < 1 := by
  let S := theorem63DirectedSineBlock Z V
  let v := finiteSourceRightSingularBasis S i
  have hle : finiteSourceSingularValue S i ≤ 1 :=
    theorem63_singularValues_sine_le_one Z V i
  by_contra hlt
  have hsigma : finiteSourceSingularValue S i = 1 :=
    le_antisymm hle (not_lt.mp hlt)
  have hvnorm : ‖v‖ = 1 := (finiteSourceRightSingularBasis S).orthonormal.norm_eq_one i
  have hSnorm : ‖S v‖ = 1 := by
    rw [norm_apply_finiteSourceRightSingularBasis, hsigma]
  have hperpnorm : ‖Vᗮ.starProjection (v : H)‖ = 1 := hSnorm
  have hpyth := Submodule.norm_sq_eq_add_norm_sq_starProjection (v : H) V
  have hvambient : ‖(v : H)‖ = 1 := hvnorm
  have hprojnorm : ‖V.starProjection (v : H)‖ = 0 := by
    rw [hvambient, hperpnorm] at hpyth
    nlinarith [norm_nonneg (V.starProjection (v : H))]
  have hprojzero : V.starProjection (v : H) = 0 := norm_eq_zero.mp hprojnorm
  have hinj := theorem63_directed_transverse_of_form_gap
    T hT V Z hV hdelta hCompressionUpper hUnwantedLower
  have hvzero : v = 0 := by
    apply hinj
    apply Subtype.ext
    change V.starProjection (v : H) = V.starProjection (0 : H)
    simpa using hprojzero
  exact (finiteSourceRightSingularBasis S).orthonormal.ne_zero i hvzero

omit [CompleteSpace H] in
/-- **A left singular vector of the directed sine block lies in `Vᗮ`.**

Its range is contained there.  Derived twice below, the copies differing only in
indentation. -/
private theorem finiteSourceLeftSingularVector_mem_orthogonal
    (Z V : Submodule ℂ H) 
    [V.HasOrthogonalProjection] [FiniteDimensional ℂ Z]
    (i : Fin (finrank ℂ Z)) :
    finiteSourceLeftSingularVector (theorem63DirectedSineBlock Z V) i ∈ Vᗮ := by
  have hyRange :
      finiteSourceLeftSingularVector (theorem63DirectedSineBlock Z V) i ∈
        (theorem63DirectedSineBlock Z V).range :=
    finiteSourceLeftSingularVector_mem_range (theorem63DirectedSineBlock Z V) i
  rcases hyRange with ⟨x, hx⟩
  rw [← hx]
  exact Vᗮ.starProjection_apply_mem ((x : Z) : H)

/-- The subtype adjoint acts on a nonzero directed-sine left singular vector
by the corresponding singular relation. -/
theorem theorem63_subtypeAdjoint_apply_finiteSourceLeftSingularVector
    (Z V : Submodule ℂ H) [Z.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] [FiniteDimensional ℂ Z]
    {i : Fin (finrank ℂ Z)}
    (hi : finiteSourceSingularValue (theorem63DirectedSineBlock Z V) i ≠ 0) :
    Z.subtypeL.adjoint
        (finiteSourceLeftSingularVector
          (theorem63DirectedSineBlock Z V) i) =
      (((finiteSourceSingularValue (theorem63DirectedSineBlock Z V) i : ℝ) : ℂ) •
        finiteSourceRightSingularBasis
          (theorem63DirectedSineBlock Z V) i) := by
  let S := theorem63DirectedSineBlock Z V
  let y := finiteSourceLeftSingularVector S i
  have hSadj : S.adjoint y = ((finiteSourceSingularValue S i : ℝ) : ℂ) •
      finiteSourceRightSingularBasis S i := adjoint_apply_finiteSourceLeftSingularVector S hi
  have hyVperp : y ∈ Vᗮ :=
    finiteSourceLeftSingularVector_mem_orthogonal Z V i
  apply ext_inner_right ℂ
  intro z
  calc
    ⟪Z.subtypeL.adjoint y, z⟫_ℂ = ⟪y, (z : H)⟫_ℂ :=
      ContinuousLinearMap.adjoint_inner_left Z.subtypeL z y
    _ = ⟪y, Vᗮ.starProjection (z : H)⟫_ℂ := by
      rw [← Vᗮ.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.mpr hyVperp]
    _ = ⟪S.adjoint y, z⟫_ℂ := by
      change ⟪y, S z⟫_ℂ = ⟪S.adjoint y, z⟫_ℂ
      exact (ContinuousLinearMap.adjoint_inner_left S z y).symm
    _ = ⟪((finiteSourceSingularValue S i : ℝ) : ℂ) •
          finiteSourceRightSingularBasis S i, z⟫_ℂ := by rw [hSadj]

/-- The normalized residual-side witness associated with one directed sine
singular vector. -/
noncomputable def theorem63ResidualWitness
    (Z V : Submodule ℂ H) 
    [V.HasOrthogonalProjection] [FiniteDimensional ℂ Z]
    (i : Fin (finrank ℂ Z)) : H :=
  let S := theorem63DirectedSineBlock Z V
  let sigma := finiteSourceSingularValue S i
  let v := finiteSourceRightSingularBasis S i
  if sigma = 0 then (v : H) else
    (((Real.sqrt (1 - sigma ^ 2) : ℝ) : ℂ)⁻¹) •
      (finiteSourceLeftSingularVector S i - ((sigma : ℝ) : ℂ) • (v : H))

/-- **Adjoint transfer along a real singular relation**, for a continuous linear
map.

If `Z⋆ y = σ • v` with `σ` real, testing `Z w` against `y` is testing `w` against
`v`, scaled by `σ`.  `orthonormal_theorem63ResidualWitness` below proves
instances of this **three times** — twice at `⟪v_i, yj⟫` in two branches, once
mirrored at `⟪yi, v_j⟫`.

`RitzResidual.lean` carries the `LinearMap` twin of this pair, for the same
reason and in the same shape; the two developments are analogous rather than
textually identical, which is why no textual check pairs them.  See
`{lane:DK-LONGPROOF-7}`. -/
theorem inner_apply_right_of_adjointL_eq_smul {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    {Z : K →L[ℂ] H} {y : H} {v : K} {σ : ℝ}
    (h : ContinuousLinearMap.adjoint Z y = ((σ : ℝ) : ℂ) • v) (w : K) :
    ⟪Z w, y⟫_ℂ = ((σ : ℝ) : ℂ) * ⟪w, v⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, h, inner_smul_right]

/-- The mirrored form, with the singular vector on the left.  `σ` being real is
what makes the conjugate disappear. -/
theorem inner_apply_left_of_adjointL_eq_smul {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    {Z : K →L[ℂ] H} {y : H} {v : K} {σ : ℝ}
    (h : ContinuousLinearMap.adjoint Z y = ((σ : ℝ) : ℂ) • v) (w : K) :
    ⟪y, Z w⟫_ℂ = ((σ : ℝ) : ℂ) * ⟪v, w⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_left, h, inner_smul_left,
    Complex.conj_ofReal]

/-- The residual witnesses form an orthonormal family once the source gap has
excluded the tangent pole. -/
theorem orthonormal_theorem63ResidualWitness
    (Z V : Submodule ℂ H) [V.HasOrthogonalProjection]
    [Z.HasOrthogonalProjection] [FiniteDimensional ℂ Z]
    (hlt : ∀ i, finiteSourceSingularValue (theorem63DirectedSineBlock Z V) i < 1) :
    Orthonormal ℂ (theorem63ResidualWitness Z V) := by
  classical
  let S := theorem63DirectedSineBlock Z V
  rw [orthonormal_iff_ite]
  intro i j
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    let sigma := finiteSourceSingularValue S i
    let v := finiteSourceRightSingularBasis S i
    have hvv : ⟪(v : H), (v : H)⟫_ℂ = 1 := by
      change ⟪v, v⟫_ℂ = 1
      simp [v]
    by_cases hsigma : sigma = 0
    · have hw : theorem63ResidualWitness Z V i = (v : H) := by
        simp [theorem63ResidualWitness, S, sigma, v, hsigma]
      rw [hw]
      exact hvv
    · let y := finiteSourceLeftSingularVector S i
      have hZadj : Z.subtypeL.adjoint y =
          ((sigma : ℝ) : ℂ) • v := by
        simpa [S, sigma, v, y] using
          theorem63_subtypeAdjoint_apply_finiteSourceLeftSingularVector Z V hsigma
      have hyy : ⟪y, y⟫_ℂ = 1 := by
        simpa [y] using
          (orthonormal_iff_ite.mp
            (orthonormal_finiteSourceLeftSingularVector_subtype S)
            ⟨i, hsigma⟩ ⟨i, hsigma⟩)
      have hZv_y : ⟪(v : H), y⟫_ℂ = ((sigma : ℝ) : ℂ) := by
        calc
          ⟪(v : H), y⟫_ℂ = ⟪v, Z.subtypeL.adjoint y⟫_ℂ :=
            (ContinuousLinearMap.adjoint_inner_right Z.subtypeL v y).symm
          _ = ⟪v, ((sigma : ℝ) : ℂ) • v⟫_ℂ := by rw [hZadj]
          _ = ((sigma : ℝ) : ℂ) := by
            rw [inner_smul_right]
            simp [v]
      have hy_Zv : ⟪y, (v : H)⟫_ℂ = ((sigma : ℝ) : ℂ) := by
        calc
          ⟪y, (v : H)⟫_ℂ = ⟪Z.subtypeL.adjoint y, v⟫_ℂ :=
            (ContinuousLinearMap.adjoint_inner_left Z.subtypeL v y).symm
          _ = ⟪((sigma : ℝ) : ℂ) • v, v⟫_ℂ := by rw [hZadj]
          _ = ((sigma : ℝ) : ℂ) := by
            rw [inner_smul_left, Complex.conj_ofReal]
            simp [v]
      have hsigma_nonneg : 0 ≤ sigma := finiteSourceSingularValue_nonneg S i
      have hsigma_lt : sigma < 1 := hlt i
      have hraw :
          ⟪y - ((sigma : ℝ) : ℂ) • (v : H),
            y - ((sigma : ℝ) : ℂ) • (v : H)⟫_ℂ =
              (((1 - sigma ^ 2 : ℝ) : ℂ)) := by
        simp only [inner_sub_left, inner_sub_right, inner_smul_left,
          inner_smul_right, Complex.conj_ofReal, hyy, hZv_y, hy_Zv, hvv]
        push_cast
        ring
      let c := Real.sqrt (1 - sigma ^ 2)
      have hcpos : 0 < c := by
        dsimp [c]
        exact Real.sqrt_pos.2 (by nlinarith)
      have hcne : c ≠ 0 := ne_of_gt hcpos
      have hw : theorem63ResidualWitness Z V i =
          ((((c : ℝ) : ℂ)⁻¹) •
            (y - ((sigma : ℝ) : ℂ) • (v : H))) := by
        simp [theorem63ResidualWitness, S, sigma, v, y, c, hsigma]
      have hc_sq : c ^ 2 = 1 - sigma ^ 2 := by
        dsimp [c]
        rw [Real.sq_sqrt (by nlinarith)]
      have hnormalize : c⁻¹ * (c⁻¹ * (1 - sigma ^ 2)) = 1 := by
        rw [← hc_sq]
        field_simp [hcne]
      rw [hw]
      simp only [inner_smul_left, inner_smul_right, map_inv₀,
        Complex.conj_ofReal, hraw]
      exact_mod_cast hnormalize
  · rw [ite_eq_right hij]
    let sigma_i := finiteSourceSingularValue S i
    let sigma_j := finiteSourceSingularValue S j
    let v_i := finiteSourceRightSingularBasis S i
    let v_j := finiteSourceRightSingularBasis S j
    have hvv : ⟪v_i, v_j⟫_ℂ = 0 := by
      simp [v_i, v_j, hij,
        orthonormal_iff_ite.mp (finiteSourceRightSingularBasis S).orthonormal i j]
    have hZZ : ⟪(v_i : H), (v_j : H)⟫_ℂ = 0 := by
      simpa [Submodule.coe_inner] using hvv
    by_cases hi : sigma_i = 0
    · have hwi : theorem63ResidualWitness Z V i = (v_i : H) := by
        simp [theorem63ResidualWitness, S, sigma_i, v_i, hi]
      by_cases hj : sigma_j = 0
      · have hwj : theorem63ResidualWitness Z V j = (v_j : H) := by
          simp [theorem63ResidualWitness, S, sigma_j, v_j, hj]
        rw [hwi, hwj, hZZ]
      · let yj := finiteSourceLeftSingularVector S j
        have hZadjj : Z.subtypeL.adjoint yj =
            ((sigma_j : ℝ) : ℂ) • v_j := by
          simpa [S, sigma_j, v_j, yj] using
            theorem63_subtypeAdjoint_apply_finiteSourceLeftSingularVector Z V hj
        have hvi_yj :
            ⟪(v_i : H), yj⟫_ℂ =
              ((sigma_j : ℝ) : ℂ) * ⟪v_i, v_j⟫_ℂ :=
          inner_apply_right_of_adjointL_eq_smul hZadjj v_i
        have hraw :
            ⟪(v_i : H),
              yj - ((sigma_j : ℝ) : ℂ) • (v_j : H)⟫_ℂ = 0 := by
          rw [inner_sub_right, inner_smul_right, hvi_yj, hZZ, hvv]
          ring
        let cj := Real.sqrt (1 - sigma_j ^ 2)
        have hwj : theorem63ResidualWitness Z V j =
            ((((cj : ℝ) : ℂ)⁻¹) •
              (yj - ((sigma_j : ℝ) : ℂ) • (v_j : H))) := by
          simp [theorem63ResidualWitness, S, sigma_j, v_j, yj, cj, hj]
        rw [hwi, hwj, inner_smul_right, hraw, mul_zero]
    · let yi := finiteSourceLeftSingularVector S i
      have hZadji : Z.subtypeL.adjoint yi =
          ((sigma_i : ℝ) : ℂ) • v_i := by
        simpa [S, sigma_i, v_i, yi] using
          theorem63_subtypeAdjoint_apply_finiteSourceLeftSingularVector Z V hi
      by_cases hj : sigma_j = 0
      · have hyi_vj :
            ⟪yi, (v_j : H)⟫_ℂ =
              ((sigma_i : ℝ) : ℂ) * ⟪v_i, v_j⟫_ℂ := by
          calc
            ⟪yi, (v_j : H)⟫_ℂ = ⟪Z.subtypeL.adjoint yi, v_j⟫_ℂ :=
              (ContinuousLinearMap.adjoint_inner_left Z.subtypeL v_j yi).symm
            _ = ⟪((sigma_i : ℝ) : ℂ) • v_i, v_j⟫_ℂ := by rw [hZadji]
            _ = _ := by rw [inner_smul_left, Complex.conj_ofReal]
        have hraw :
            ⟪yi - ((sigma_i : ℝ) : ℂ) • (v_i : H),
              (v_j : H)⟫_ℂ = 0 := by
          rw [inner_sub_left, inner_smul_left, Complex.conj_ofReal,
            hyi_vj, hZZ, hvv]
          ring
        let ci := Real.sqrt (1 - sigma_i ^ 2)
        have hwi : theorem63ResidualWitness Z V i =
            ((((ci : ℝ) : ℂ)⁻¹) •
              (yi - ((sigma_i : ℝ) : ℂ) • (v_i : H))) := by
          simp [theorem63ResidualWitness, S, sigma_i, v_i, yi, ci, hi]
        have hwj : theorem63ResidualWitness Z V j = (v_j : H) := by
          simp [theorem63ResidualWitness, S, sigma_j, v_j, hj]
        rw [hwi, hwj, inner_smul_left, hraw, mul_zero]
      · let yj := finiteSourceLeftSingularVector S j
        have hZadjj : Z.subtypeL.adjoint yj =
            ((sigma_j : ℝ) : ℂ) • v_j := by
          simpa [S, sigma_j, v_j, yj] using
            theorem63_subtypeAdjoint_apply_finiteSourceLeftSingularVector Z V hj
        have hyy : ⟪yi, yj⟫_ℂ = 0 := by
          simpa [yi, yj, hij] using
            (orthonormal_iff_ite.mp
              (orthonormal_finiteSourceLeftSingularVector_subtype S)
              ⟨i, hi⟩ ⟨j, hj⟩)
        have hyi_vj :
            ⟪yi, (v_j : H)⟫_ℂ =
              ((sigma_i : ℝ) : ℂ) * ⟪v_i, v_j⟫_ℂ :=
          inner_apply_left_of_adjointL_eq_smul hZadji v_j
        have hvi_yj :
            ⟪(v_i : H), yj⟫_ℂ =
              ((sigma_j : ℝ) : ℂ) * ⟪v_i, v_j⟫_ℂ :=
          inner_apply_right_of_adjointL_eq_smul hZadjj v_i
        have hraw :
            ⟪yi - ((sigma_i : ℝ) : ℂ) • (v_i : H),
              yj - ((sigma_j : ℝ) : ℂ) • (v_j : H)⟫_ℂ = 0 := by
          simp only [inner_sub_left, inner_sub_right, inner_smul_left,
            inner_smul_right, Complex.conj_ofReal,
            hyy, hyi_vj, hvi_yj, hZZ, hvv]
          ring
        let ci := Real.sqrt (1 - sigma_i ^ 2)
        let cj := Real.sqrt (1 - sigma_j ^ 2)
        have hwi : theorem63ResidualWitness Z V i =
            ((((ci : ℝ) : ℂ)⁻¹) •
              (yi - ((sigma_i : ℝ) : ℂ) • (v_i : H))) := by
          simp [theorem63ResidualWitness, S, sigma_i, v_i, yi, ci, hi]
        have hwj : theorem63ResidualWitness Z V j =
            ((((cj : ℝ) : ℂ)⁻¹) •
              (yj - ((sigma_j : ℝ) : ℂ) • (v_j : H))) := by
          simp [theorem63ResidualWitness, S, sigma_j, v_j, yj, cj, hj]
        simp only [hwi, hwj, inner_smul_left, inner_smul_right,
          hraw, mul_zero]

/-- Approximation-number formulation of the paper's instruction that
`tan Θ₀` have singular values `tan θ_j`, where the directed sine singular
values are `sin θ_j`. -/
def HasTheorem63DirectedTangentApproximationNumbers
    (Z V : Submodule ℂ H) 
    [V.HasOrthogonalProjection] 
    (tanTheta0 : Z →L[ℂ] H) : Prop :=
  ∀ n, approximationSingularValue n tanTheta0 =
    Real.tan (Real.arcsin
      (approximationSingularValue n (theorem63DirectedSineBlock Z V)))

/-- **The scalar estimate corresponding to equation (6.6), over abstract trial-block
data.**

`M` is the compression, `R` the residual, and `X` the *crossed action* — the ambient
operator applied to `P_{Vᗮ} z`.  Splitting `X` off from the ambient operator is what lets
an unbounded self-adjoint operator use this estimate: `P_{Vᗮ} z` lies in the operator
domain whenever the trial space does and `V` is a spectral subspace, so the crossed
quadratic form is available even though the operator itself is unbounded on `Vᗮ`.

The two form hypotheses are the paper's: the compression is bounded above by `α`, and
the crossed form is bounded below by `α + δ`. -/
theorem theorem63ResidualWitness_scalar_of_data
    (V Z : Submodule ℂ H) [V.HasOrthogonalProjection]
    [Z.HasOrthogonalProjection] [FiniteDimensional ℂ Z]
    {alpha delta : ℝ}
    (M : Z →L[ℂ] Z) (R : Z →L[ℂ] H) (X : Z →L[ℂ] H)
    (hMupper : ∀ z : Z, RCLike.re ⟪M z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hcross : ∀ z : Z, (alpha + delta) * ‖Vᗮ.starProjection ((z : Z) : H)‖ ^ 2 ≤
      RCLike.re ⟪Vᗮ.starProjection ((z : Z) : H), X z⟫_ℂ)
    (hRorth : ∀ z z' : Z, ⟪R z, ((z' : Z) : H)⟫_ℂ = 0)
    (hsyl : ∀ z : Z, X z - theorem63DirectedSineBlock Z V (M z) =
      Vᗮ.starProjection (R z))
    (hlt : ∀ i, finiteSourceSingularValue (theorem63DirectedSineBlock Z V) i < 1)
    (tanTheta0 : Z →L[ℂ] H)
    (htan : HasTheorem63DirectedTangentApproximationNumbers Z V tanTheta0)
    (i : Fin (finrank ℂ Z)) :
    delta * approximationSingularValue i tanTheta0 ≤
      RCLike.re ⟪theorem63ResidualWitness Z V i,
        R (finiteSourceRightSingularBasis
            (theorem63DirectedSineBlock Z V) i)⟫_ℂ := by
  let S := theorem63DirectedSineBlock Z V
  let sigma := finiteSourceSingularValue S i
  let v := finiteSourceRightSingularBasis S i
  have hvnorm : ‖v‖ = 1 := (finiteSourceRightSingularBasis S).orthonormal.norm_eq_one i
  have hsigma_nonneg : 0 ≤ sigma := finiteSourceSingularValue_nonneg S i
  have hsigma_lt : sigma < 1 := hlt i
  have hcpos : 0 < Real.sqrt (1 - sigma ^ 2) :=
    Real.sqrt_pos.2 (by nlinarith)
  have hSapprox : approximationSingularValue i
      (theorem63DirectedSineBlock Z V) = sigma := by
    simpa [S, sigma] using approximationSingularValue_eq_finiteSourceSingularValue S i
  have htan_i : approximationSingularValue i tanTheta0 =
      sigma / Real.sqrt (1 - sigma ^ 2) := by
    rw [htan i, hSapprox, Real.tan_arcsin]
  -- The residual is orthogonal to the trial space, in both slots.
  have hZorth : ⟪(v : H), R v⟫_ℂ = 0 := by
    have h := hRorth v v
    rw [← inner_conj_symm, h, map_zero]
  by_cases hsigma_zero : sigma = 0
  · have hwitness : theorem63ResidualWitness Z V i = (v : H) := by
      simp [theorem63ResidualWitness, S, sigma, v, hsigma_zero]
    rw [htan_i, hsigma_zero, zero_div, mul_zero, hwitness, hZorth]
    simp
  · have hsigma_pos : 0 < sigma := lt_of_le_of_ne hsigma_nonneg (Ne.symm hsigma_zero)
    let y := finiteSourceLeftSingularVector S i
    have hynorm : ‖y‖ = 1 := by
      simpa [y] using
        (orthonormal_finiteSourceLeftSingularVector_subtype S).norm_eq_one
          ⟨i, hsigma_zero⟩
    have hSv : S v = ((sigma : ℝ) : ℂ) • y := by
      simpa [S, sigma, v, y] using
        apply_finiteSourceRightSingularBasis_eq_smul_leftSingularVector S i
    have hSadj : S.adjoint y = ((sigma : ℝ) : ℂ) • v := by
      simpa [S, sigma, v, y] using
        adjoint_apply_finiteSourceLeftSingularVector S hsigma_zero
    have hyVperp : y ∈ Vᗮ :=
      finiteSourceLeftSingularVector_mem_orthogonal Z V i
    -- `P_{Vᗮ} v` is the sine block applied to `v`, i.e. `sigma • y`.
    have hproj_v : Vᗮ.starProjection ((v : Z) : H) = ((sigma : ℝ) : ℂ) • y := by
      have h : Vᗮ.starProjection ((v : Z) : H) = S v := rfl
      rw [h, hSv]
    -- The crossed form bound, divided by `sigma`.
    have hXlower : (alpha + delta) * sigma ≤ RCLike.re ⟪y, X v⟫_ℂ := by
      have h := hcross v
      rw [hproj_v] at h
      have hnorm : ‖((sigma : ℝ) : ℂ) • y‖ = sigma := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hsigma_nonneg, hynorm, mul_one]
      have hinner : RCLike.re ⟪((sigma : ℝ) : ℂ) • y, X v⟫_ℂ =
          sigma * RCLike.re ⟪y, X v⟫_ℂ := by
        rw [inner_smul_left, Complex.conj_ofReal]
        simp only [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero]
      rw [hnorm, hinner] at h
      refine le_of_mul_le_mul_right ?_ hsigma_pos
      nlinarith [h]
    -- The compression form bound at the unit vector `v`.
    have hMv : RCLike.re ⟪M v, v⟫_ℂ ≤ alpha := by
      have h := hMupper v
      rwa [hvnorm, one_pow, mul_one] at h
    -- Pair the witness against the residual through the Sylvester identity.
    have hright : ⟪y, Vᗮ.starProjection (R v)⟫_ℂ = ⟪y, R v⟫_ℂ := by
      rw [← Vᗮ.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.mpr hyVperp]
    have hSM : ⟪y, S (M v)⟫_ℂ = ((sigma : ℝ) : ℂ) * ⟪v, M v⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_left S (M v) y, hSadj,
        inner_smul_left, Complex.conj_ofReal]
    have hsplit : ⟪y, R v⟫_ℂ = ⟪y, X v⟫_ℂ - ((sigma : ℝ) : ℂ) * ⟪v, M v⟫_ℂ := by
      have h := congrArg (fun w : H => ⟪y, w⟫_ℂ) (hsyl v)
      simp only [inner_sub_right] at h
      rw [hright] at h
      rw [← h, hSM]
    have hMre : RCLike.re ⟪v, M v⟫_ℂ = RCLike.re ⟪M v, v⟫_ℂ := by
      rw [← inner_conj_symm, RCLike.conj_re]
    have hpair_lower : delta * sigma ≤ RCLike.re ⟪y, R v⟫_ℂ := by
      have hre : RCLike.re ⟪y, R v⟫_ℂ =
          RCLike.re ⟪y, X v⟫_ℂ - sigma * RCLike.re ⟪v, M v⟫_ℂ := by
        rw [hsplit]
        simp only [RCLike.re_to_complex, Complex.sub_re, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [hre, hMre]
      nlinarith [hXlower, hMv, hsigma_pos]
    -- Rescale to the normalized witness.
    have hraw :
        RCLike.re ⟪y - ((sigma : ℝ) : ℂ) • (v : H), R v⟫_ℂ =
          RCLike.re ⟪y, R v⟫_ℂ := by
      have hc :
          ⟪y - ((sigma : ℝ) : ℂ) • (v : H), R v⟫_ℂ = ⟪y, R v⟫_ℂ := by
        rw [inner_sub_left, inner_smul_left, Complex.conj_ofReal,
          hZorth, mul_zero, sub_zero]
      exact congrArg RCLike.re hc
    let c := Real.sqrt (1 - sigma ^ 2)
    have hcpos' : 0 < c := by simpa [c] using hcpos
    have hscale :
        RCLike.re ⟪((((c : ℝ) : ℂ)⁻¹) •
            (y - ((sigma : ℝ) : ℂ) • (v : H))), R v⟫_ℂ =
          RCLike.re ⟪y, R v⟫_ℂ / c := by
      calc
        RCLike.re ⟪((((c : ℝ) : ℂ)⁻¹) •
            (y - ((sigma : ℝ) : ℂ) • (v : H))), R v⟫_ℂ =
            c⁻¹ * RCLike.re
              ⟪y - ((sigma : ℝ) : ℂ) • (v : H), R v⟫_ℂ := by
                rw [inner_smul_left, map_inv₀, Complex.conj_ofReal,
                  ← Complex.ofReal_inv]
                change
                  (((c⁻¹ : ℝ) : ℂ) *
                    ⟪y - ((sigma : ℝ) : ℂ) • (v : H), R v⟫_ℂ).re =
                    c⁻¹ *
                      (⟪y - ((sigma : ℝ) : ℂ) • (v : H), R v⟫_ℂ).re
                simp only [Complex.mul_re, Complex.ofReal_re,
                  Complex.ofReal_im, zero_mul, sub_zero]
        _ = c⁻¹ * RCLike.re ⟪y, R v⟫_ℂ := by rw [hraw]
        _ = RCLike.re ⟪y, R v⟫_ℂ / c := by
          simp [div_eq_mul_inv, mul_comm]
    rw [htan_i]
    change delta * (sigma / c) ≤
      RCLike.re ⟪
        (if sigma = 0 then (v : H) else
          ((((c : ℝ) : ℂ)⁻¹) •
            (y - ((sigma : ℝ) : ℂ) • (v : H)))), R v⟫_ℂ
    rw [ite_eq_right hsigma_zero, hscale]
    simpa [div_eq_mul_inv, mul_assoc] using
      (div_le_div_iff_of_pos_right hcpos').2 hpair_lower

/-- The scalar estimate corresponding to equation (6.6). -/
theorem theorem63ResidualWitness_scalar
    (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (V Z : Submodule ℂ H) [V.HasOrthogonalProjection]
    [Z.HasOrthogonalProjection] [FiniteDimensional ℂ Z]
    (hV : T.Reduces V) {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : Z,
      RCLike.re ⟪theorem63Compression T Z z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ)
    (tanTheta0 : Z →L[ℂ] H)
    (htan : HasTheorem63DirectedTangentApproximationNumbers Z V tanTheta0)
    (i : Fin (finrank ℂ Z)) :
    delta * approximationSingularValue i tanTheta0 ≤
      RCLike.re ⟪theorem63ResidualWitness Z V i,
        theorem63Residual T Z
          (finiteSourceRightSingularBasis
            (theorem63DirectedSineBlock Z V) i)⟫_ℂ := by
  refine theorem63ResidualWitness_scalar_of_data V Z
    (theorem63Compression T Z) (theorem63Residual T Z)
    (T ∘L Vᗮ.starProjection ∘L Z.subtypeL)
    hCompressionUpper ?_ ?_ ?_
    (fun i => theorem63_singularValues_sine_lt_one T hT V Z hV hdelta
      hCompressionUpper hUnwantedLower i) tanTheta0 htan i
  · -- the crossed form bound, from the lower bound on `Vᗮ`
    intro z
    have hmem : Vᗮ.starProjection ((z : Z) : H) ∈ Vᗮ :=
      Vᗮ.starProjection_apply_mem _
    have h := hUnwantedLower _ hmem
    have hre : RCLike.re ⟪Vᗮ.starProjection ((z : Z) : H),
        (T ∘L Vᗮ.starProjection ∘L Z.subtypeL) z⟫_ℂ =
        RCLike.re ⟪T (Vᗮ.starProjection ((z : Z) : H)),
          Vᗮ.starProjection ((z : Z) : H)⟫_ℂ := by
      change RCLike.re ⟪Vᗮ.starProjection ((z : Z) : H),
        T (Vᗮ.starProjection ((z : Z) : H))⟫_ℂ = _
      rw [← inner_conj_symm, RCLike.conj_re]
    rw [hre]
    exact h
  · -- residual orthogonality
    intro z z'
    exact Submodule.inner_left_of_mem_orthogonal z'.2
      (theorem63Residual_apply_mem_orthogonal T Z z)
  · -- the Sylvester identity, in data form
    intro z
    have h := congrArg (fun L : Z →L[ℂ] H => L z)
      (theorem63_sylvester_identity T V Z hV)
    simp only [sub_apply, ContinuousLinearMap.comp_apply] at h
    exact h


/-- Ky Fan domination up to the finite trial-space dimension. -/
private theorem theorem6_3_kyFan_core_of_le_finrank
    (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (V Z : Submodule ℂ H) [V.HasOrthogonalProjection]
    [Z.HasOrthogonalProjection] [FiniteDimensional ℂ Z]
    (hV : T.Reduces V) {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : Z,
      RCLike.re ⟪theorem63Compression T Z z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ)
    (tanTheta0 : Z →L[ℂ] H)
    (htan : HasTheorem63DirectedTangentApproximationNumbers Z V tanTheta0)
    {k : ℕ} (hk : k ≤ finrank ℂ Z) :
    delta * kyFanApproximationGauge k tanTheta0 ≤
      kyFanApproximationGauge k (theorem63Residual T Z) := by
  let castIndex : Fin k → Fin (finrank ℂ Z) := fun i => Fin.castLE hk i
  have huFull := orthonormal_theorem63ResidualWitness Z V
    (fun i => theorem63_singularValues_sine_lt_one T hT V Z hV hdelta
      hCompressionUpper hUnwantedLower i)
  have hu : Orthonormal ℂ
      (fun i : Fin k => theorem63ResidualWitness Z V (castIndex i)) := by
    rw [orthonormal_iff_ite]
    intro i j
    simpa [castIndex] using
      (orthonormal_iff_ite.mp huFull (castIndex i) (castIndex j))
  have hv : Orthonormal ℂ
      (fun i : Fin k =>
        (finiteSourceRightSingularBasis
          (theorem63DirectedSineBlock Z V) (castIndex i) : Z)) := by
    rw [orthonormal_iff_ite]
    intro i j
    simpa [castIndex] using
      (orthonormal_iff_ite.mp
        (finiteSourceRightSingularBasis
          (theorem63DirectedSineBlock Z V)).orthonormal
        (castIndex i) (castIndex j))
  have hsum := sum_le_kyFanApproximationGauge_of_orthonormal
    (theorem63Residual T Z) hu hv
    (fun i => theorem63ResidualWitness_scalar
      T hT V Z hV hdelta hCompressionUpper hUnwantedLower
      tanTheta0 htan (castIndex i))
  unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge at hsum ⊢
  rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
  simpa [castIndex, approximationSingularValue] using hsum

/-- A bounded operator with finite-dimensional domain has no approximation
singular values beyond that domain dimension. -/
theorem kyFanApproximationGauge_eq_finrank_of_finrank_le
    {E F : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [FiniteDimensional ℂ E]
    (A : E →L[ℂ] F) {k : ℕ} (hk : finrank ℂ E ≤ k) :
    kyFanApproximationGauge k A =
      kyFanApproximationGauge (finrank ℂ E) A := by
  let d := finrank ℂ E
  have hrank : A.rank ≤ (d : Cardinal) := by
    calc
      A.rank ≤ Module.rank ℂ E := LinearMap.rank_le_domain _
      _ = (d : Cardinal) := by
        rw [← Module.finrank_eq_rank' ℂ E]
  unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
  rw [← Finset.sum_range_add_sum_Ico _ hk]
  apply add_eq_left.mpr
  apply Finset.sum_eq_zero
  intro n hn
  have hdn : d ≤ n := Finset.mem_Ico.mp hn |>.1
  exact approximationSingularValue_eq_zero_of_rank_le_nat hrank hdn

/-- The source Ky Fan inequalities for all prefixes. -/
theorem theorem6_3_all_kyFan_core
    (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (V Z : Submodule ℂ H) [V.HasOrthogonalProjection]
    [Z.HasOrthogonalProjection] [FiniteDimensional ℂ Z]
    (hV : T.Reduces V) {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : Z,
      RCLike.re ⟪theorem63Compression T Z z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ)
    (tanTheta0 : Z →L[ℂ] H)
    (htan : HasTheorem63DirectedTangentApproximationNumbers Z V tanTheta0) :
    ∀ k, delta * kyFanApproximationGauge k tanTheta0 ≤
      kyFanApproximationGauge k (theorem63Residual T Z) := by
  intro k
  by_cases hk : k ≤ finrank ℂ Z
  · exact theorem6_3_kyFan_core_of_le_finrank T hT V Z hV hdelta
      hCompressionUpper hUnwantedLower tanTheta0 htan hk
  · have hdk : finrank ℂ Z ≤ k := Nat.le_of_not_ge hk
    rw [kyFanApproximationGauge_eq_finrank_of_finrank_le tanTheta0 hdk,
      kyFanApproximationGauge_eq_finrank_of_finrank_le
        (theorem63Residual T Z) hdk]
    exact theorem6_3_kyFan_core_of_le_finrank T hT V Z hV hdelta
      hCompressionUpper hUnwantedLower tanTheta0 htan le_rfl

/-- **Davis--Kahan 1970, Theorem 6.3, source-faithful bounded form.**

The trial coordinate space is finite-dimensional, while the ambient Hilbert
space and the exact spectral subspace may be infinite-dimensional.  The
conclusion holds for every approximation-number ideal family satisfying Fan
dominance. -/
theorem theorem6_3_generalizedTanTheta_of_formBounds
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (V Z : Submodule ℂ H) [V.HasOrthogonalProjection]
    [Z.HasOrthogonalProjection] [FiniteDimensional ℂ Z]
    (hV : T.Reduces V)
    (_hStrictDimension : Module.rank ℂ Z < Module.rank ℂ V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : Z,
      RCLike.re ⟪theorem63Compression T Z z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ)
    (tanTheta0 : Z →L[ℂ] H)
    (htan : HasTheorem63DirectedTangentApproximationNumbers Z V tanTheta0)
    (hResidual : N.Mem
      (theorem63Residual T Z)) :
    N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤
        N.gauge (theorem63Residual T Z) := by
  exact mem_and_scaled_gauge_le_of_all_scaled_kyFan_le
    N.toFanDominantIdealFamily hdelta hResidual
      (theorem6_3_all_kyFan_core T hT V Z hV hdelta
        hCompressionUpper hUnwantedLower tanTheta0 htan)

/-- **Davis--Kahan 1970, Theorem 6.3, bounded source-effective spectral form.**

The spectrum of the Ritz compression is contained in `[beta, alpha]`; the
spectrum of the restriction to the unwanted exact subspace is contained in
`[alpha + delta, ∞)`.  The finite-dimensional trial-coordinate typeclass
records the effective content of the paper's strict Hilbert-dimension
assumption under its global separability convention.  The separate strict-rank
hypothesis preserves that source condition explicitly; no symmetric acuteness
is inferred from it. -/
theorem theorem6_3_generalizedTanTheta_ideal
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (V Z : Submodule ℂ H) [V.HasOrthogonalProjection]
    [Z.HasOrthogonalProjection] [FiniteDimensional ℂ Z]
    (hV : T.Reduces V)
    (hStrictDimension : Module.rank ℂ Z < Module.rank ℂ V)
    {beta alpha delta : ℝ} (_hbetaalpha : beta ≤ alpha)
    (hdelta : 0 < delta)
    (hCompressionSpectrum :
      spectrum ℝ (theorem63Compression T Z) ⊆ Set.Icc beta alpha)
    (hUnwantedSpectrum :
      spectrum ℝ (T.restrict (hV.orthogonalComplement).1) ⊆
        Set.Ici (alpha + delta))
    (tanTheta0 : Z →L[ℂ] H)
    (htan : HasTheorem63DirectedTangentApproximationNumbers Z V tanTheta0)
    (hResidual : N.Mem
      (theorem63Residual T Z)) :
    N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤
        N.gauge (theorem63Residual T Z) := by
  have hTsa : IsSelfAdjoint T :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT
  have hMsa : IsSelfAdjoint (theorem63Compression T Z) := by
    simpa [theorem63Compression, DavisKahan.Sylvester.compressOperator] using
      DavisKahan.Sylvester.isSelfAdjoint_compressOperator hTsa Z
  have hCompressionUpper : ∀ z : Z,
      RCLike.re ⟪theorem63Compression T Z z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2 := by
    intro z
    apply SpectralOrder.re_inner_le_of_spectrum_subset_Iic
      (theorem63Compression T Z) hMsa
    · intro r hr
      exact (hCompressionSpectrum hr).2
  have hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ := by
    intro y hy
    exact SpectralOrder.le_re_inner_on_subspace_of_restriction_spectrum_subset_Ici
      hT (hV.orthogonalComplement).1 hUnwantedSpectrum hy
  exact theorem6_3_generalizedTanTheta_of_formBounds N T hT V Z hV
    hStrictDimension hdelta hCompressionUpper hUnwantedLower tanTheta0 htan
    hResidual


/-- Historical scratch proposition used while the Ky Fan root was open. -/
def Theorem63KyFanCore
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] 
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] 
    (delta : ℝ) (tanTheta0 residual : E →L[ℂ] F) : Prop :=
  ∀ k, delta * ExactSinTheta.kyFanApproximationGauge k tanTheta0 ≤
    ExactSinTheta.kyFanApproximationGauge k residual

/-- Fan-dominance promotion retained at its historical scratch name. -/
theorem theorem6_3_ideal_of_kyFan_core
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    {delta : ℝ} (hdelta : 0 < delta)
    {tanTheta0 residual : E →L[ℂ] F}
    (hResidual : N.Mem residual)
    (hcore : Theorem63KyFanCore delta tanTheta0 residual) :
    N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤
        N.gauge residual :=
  ExactSinTheta.mem_and_scaled_gauge_le_of_all_scaled_kyFan_le
    N.toFanDominantIdealFamily hdelta hResidual hcore

/-! ### A directed tangent representative exists

`HasTheorem63DirectedTangentApproximationNumbers` is a hypothesis of every
statement above, and until now nothing produced a value for it.  In that state
Theorem 6.3 reads "*if* a tan-Θ representative exists then the bound holds",
which is weaker than what Davis and Kahan assert — the printed theorem is about
a representative they take for granted.

This section supplies the producer, so the conditional is discharged.

The representative is diagonal in the right singular basis of the sine block,
with entries `tan (arcsin sᵢ)`.  Two facts make that work: the singular values
of a diagonal operator with antitone nonnegative diagonal are the diagonal
itself, and `t ↦ tan (arcsin t) = t / √(1 - t²)` is increasing on `[0, 1)`, so
the entries inherit the sine block's ordering.

Finiteness of the entries needs `sᵢ < 1`, and that is **not an extra
hypothesis**: `theorem63_singularValues_sine_lt_one` already derives it from the
source gap, i.e. from exactly the `hCompressionUpper` and `hUnwantedLower` that
Theorem 6.3 assumes anyway.  So `theorem6_3_all_kyFan_core_directedTangent`
below carries no hypothesis the printed theorem does not. -/

section DirectedTangentExistence

variable (Z V : Submodule ℂ H) [Z.HasOrthogonalProjection]
  [V.HasOrthogonalProjection] [FiniteDimensional ℂ Z]

/-- The diagonal entries of the directed tangent: tangents of the directed
angles, read off from the sine block's singular values. -/
noncomputable def theorem63DirectedTangentDiagonal
    (i : Fin (finrank ℂ Z)) : ℝ :=
  Real.tan (Real.arcsin
    (finiteSourceSingularValue (theorem63DirectedSineBlock Z V) i))

/-- **A directed tangent representative**, diagonal in the right singular basis
of the sine block. -/
noncomputable def theorem63DirectedTangent : Z →L[ℂ] H :=
  Z.subtypeL ∘L
    (diagOp (finiteSourceRightSingularBasis (theorem63DirectedSineBlock Z V))
      (theorem63DirectedTangentDiagonal Z V)).toContinuousLinearMap

omit [CompleteSpace H] [FiniteDimensional ℂ ↥Z] in
/-- Composing with the inclusion of the trial space does not move approximation
singular values: the inclusion is an isometry with a norm-one left inverse. -/
theorem approximationSingularValue_subtypeL_comp_complex
    (A : Z →L[ℂ] Z) (k : ℕ) :
    approximationSingularValue k (Z.subtypeL ∘L A) =
      approximationSingularValue k A := by
  have hmem : ∀ x : Z, (Z.subtypeL ∘L A) x ∈ Z := fun x => (A x).property
  have hcomp : Z.orthogonalProjectionOnto ∘L (Z.subtypeL ∘L A) = A := by
    ext x
    change Z.starProjection ((A x : H)) = ((A x : H))
    exact Submodule.starProjection_eq_self_iff.mpr (A x).property
  calc
    approximationSingularValue k (Z.subtypeL ∘L A) =
        approximationSingularValue k
          (Z.orthogonalProjectionOnto ∘L (Z.subtypeL ∘L A)) :=
      (approximationSingularValue_orthogonalProjectionOnto_comp_eq Z
        (Z.subtypeL ∘L A) hmem k).symm
    _ = approximationSingularValue k A := by rw [hcomp]

omit [Z.HasOrthogonalProjection] in
/-- Above the dimension of the trial space every approximation singular value of
a map out of it vanishes. -/
theorem approximationSingularValue_eq_zero_of_finrank_le_complex
    (A : Z →L[ℂ] H) {k : ℕ} (hk : finrank ℂ Z ≤ k) :
    approximationSingularValue k A = 0 := by
  refine approximationSingularValue_eq_zero_of_rank_le_nat
    (r := finrank ℂ Z) ?_ hk
  calc (A : Z →ₗ[ℂ] H).rank ≤ Module.rank ℂ Z := LinearMap.rank_le_domain _
    _ = ((finrank ℂ Z : ℕ) : Cardinal) := (Module.finrank_eq_rank ℂ Z).symm

/-- **The directed tangent has the approximation numbers Theorem 6.3 asks
for.**

With this, `theorem6_3_all_kyFan_core` and its ideal-gauge consequences are
unconditional: a representative is exhibited, not assumed. -/
theorem hasTheorem63DirectedTangentApproximationNumbers_theorem63DirectedTangent
    (hlt : ∀ i, finiteSourceSingularValue
      (theorem63DirectedSineBlock Z V) i < 1) :
    HasTheorem63DirectedTangentApproximationNumbers Z V
      (theorem63DirectedTangent Z V) := by
  have hsB : ∀ i : Fin (finrank ℂ Z),
      approximationSingularValue (i : ℕ) (theorem63DirectedSineBlock Z V) =
        finiteSourceSingularValue (theorem63DirectedSineBlock Z V) i := fun i =>
    approximationSingularValue_eq_finiteSourceSingularValue _ i
  have hs0 : ∀ i, 0 ≤ finiteSourceSingularValue
      (theorem63DirectedSineBlock Z V) i := fun i =>
    finiteSourceSingularValue_nonneg _ i
  have hs1 : ∀ i, finiteSourceSingularValue
      (theorem63DirectedSineBlock Z V) i < 1 := hlt
  have hteq : ∀ i, theorem63DirectedTangentDiagonal Z V i =
      finiteSourceSingularValue (theorem63DirectedSineBlock Z V) i /
        Real.sqrt (1 - finiteSourceSingularValue
          (theorem63DirectedSineBlock Z V) i ^ 2) := fun i => by
    rw [theorem63DirectedTangentDiagonal, Real.tan_arcsin]
  have hsqrtpos : ∀ i, 0 < Real.sqrt (1 - finiteSourceSingularValue
      (theorem63DirectedSineBlock Z V) i ^ 2) := fun i =>
    Real.sqrt_pos.2 (by nlinarith [hs0 i, hs1 i])
  have ht0 : ∀ i, 0 ≤ theorem63DirectedTangentDiagonal Z V i := fun i => by
    rw [hteq i]
    exact div_nonneg (hs0 i) (Real.sqrt_nonneg _)
  have hsanti : Antitone (finiteSourceSingularValue
      (theorem63DirectedSineBlock Z V)) := by
    intro i j hij
    rw [← hsB i, ← hsB j]
    exact approximationSingularValue_antitone _ (by exact_mod_cast hij)
  have htanti : Antitone (theorem63DirectedTangentDiagonal Z V) := by
    intro i j hij
    have hsji := hsanti hij
    rw [hteq i, hteq j, div_le_div_iff₀ (hsqrtpos j) (hsqrtpos i)]
    have hroot : Real.sqrt (1 - finiteSourceSingularValue
          (theorem63DirectedSineBlock Z V) i ^ 2) ≤
        Real.sqrt (1 - finiteSourceSingularValue
          (theorem63DirectedSineBlock Z V) j ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith [hs0 j, hs0 i])
    exact mul_le_mul hsji hroot (Real.sqrt_nonneg _) (hs0 i)
  intro k
  by_cases hk : k < finrank ℂ Z
  · have hkfin : ((⟨k, hk⟩ : Fin (finrank ℂ Z)) : ℕ) = k := rfl
    have hrhs : Real.tan (Real.arcsin (approximationSingularValue k
        (theorem63DirectedSineBlock Z V))) =
        theorem63DirectedTangentDiagonal Z V ⟨k, hk⟩ := by
      rw [show approximationSingularValue k (theorem63DirectedSineBlock Z V) =
          finiteSourceSingularValue (theorem63DirectedSineBlock Z V) ⟨k, hk⟩
        from hsB ⟨k, hk⟩, theorem63DirectedTangentDiagonal]
    rw [hrhs]
    calc
      approximationSingularValue k (theorem63DirectedTangent Z V) =
          approximationSingularValue k
            (diagOp (finiteSourceRightSingularBasis
              (theorem63DirectedSineBlock Z V))
              (theorem63DirectedTangentDiagonal Z V)).toContinuousLinearMap :=
        approximationSingularValue_subtypeL_comp_complex Z _ k
      _ = (diagOp (finiteSourceRightSingularBasis
            (theorem63DirectedSineBlock Z V))
            (theorem63DirectedTangentDiagonal Z V)).singularValues k :=
        approximationSingularValue_eq_singularValues _ k
      _ = theorem63DirectedTangentDiagonal Z V ⟨k, hk⟩ := by
        simpa only [hkfin] using
          singularValues_diagOp (𝕜 := ℂ) (E := Z) (n := finrank ℂ Z) rfl
            (finiteSourceRightSingularBasis (theorem63DirectedSineBlock Z V))
            htanti ht0 ⟨k, hk⟩
  · have hkge : finrank ℂ Z ≤ k := Nat.le_of_not_lt hk
    rw [approximationSingularValue_eq_zero_of_finrank_le_complex Z
      (theorem63DirectedTangent Z V) hkge,
      approximationSingularValue_eq_zero_of_finrank_le_complex Z
        (theorem63DirectedSineBlock Z V) hkge]
    simp

/-- **Theorem 6.3, unconditionally.**

The same Ky Fan inequality as `theorem6_3_all_kyFan_core`, with **no** hypothesis
about a tangent representative and no hypothesis the printed theorem does not
have: the representative this section constructs is used, and the `sᵢ < 1` it
needs comes from the source gap through
`theorem63_singularValues_sine_lt_one`.

This is the form the Section 2 tangent theorem consumes. -/
theorem theorem6_3_all_kyFan_core_directedTangent
    (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (hV : T.Reduces V) {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : Z,
      RCLike.re ⟪theorem63Compression T Z z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ) :
    ∀ k, delta * kyFanApproximationGauge k (theorem63DirectedTangent Z V) ≤
      kyFanApproximationGauge k (theorem63Residual T Z) :=
  theorem6_3_all_kyFan_core T hT V Z hV hdelta hCompressionUpper hUnwantedLower
    (theorem63DirectedTangent Z V)
    (hasTheorem63DirectedTangentApproximationNumbers_theorem63DirectedTangent
      Z V fun i => theorem63_singularValues_sine_lt_one T hT V Z hV hdelta
        hCompressionUpper hUnwantedLower i)

/-- **Theorem 6.3 at ideal-gauge scope, unconditionally.**

`theorem6_3_generalizedTanTheta_ideal` with the tangent representative
supplied rather than assumed.  Every hypothesis here is one Davis and Kahan
state. -/
theorem theorem6_3_generalizedTanTheta_ideal_directedTangent
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (hV : T.Reduces V)
    (hStrictDimension : Module.rank ℂ Z < Module.rank ℂ V)
    {beta alpha delta : ℝ} (hbetaalpha : beta ≤ alpha) (hdelta : 0 < delta)
    (hCompressionSpectrum :
      spectrum ℝ (theorem63Compression T Z) ⊆ Set.Icc beta alpha)
    (hUnwantedSpectrum :
      spectrum ℝ (T.restrict (hV.orthogonalComplement).1) ⊆
        Set.Ici (alpha + delta))
    (hResidual : N.Mem (theorem63Residual T Z)) :
    N.Mem (theorem63DirectedTangent Z V) ∧
      delta * N.gauge (theorem63DirectedTangent Z V) ≤
        N.gauge (theorem63Residual T Z) := by
  have hTsa : IsSelfAdjoint T :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT
  have hMsa : IsSelfAdjoint (theorem63Compression T Z) := by
    simpa [theorem63Compression, DavisKahan.Sylvester.compressOperator] using
      DavisKahan.Sylvester.isSelfAdjoint_compressOperator hTsa Z
  have hCompressionUpper : ∀ z : Z,
      RCLike.re ⟪theorem63Compression T Z z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2 := by
    intro z
    refine SpectralOrder.re_inner_le_of_spectrum_subset_Iic
      (theorem63Compression T Z) hMsa ?_ z
    intro r hr
    exact (hCompressionSpectrum hr).2
  have hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ := fun y hy =>
    SpectralOrder.le_re_inner_on_subspace_of_restriction_spectrum_subset_Ici
      hT (hV.orthogonalComplement).1 hUnwantedSpectrum hy
  exact theorem6_3_generalizedTanTheta_ideal N T hT V Z hV
    hStrictDimension hbetaalpha hdelta hCompressionSpectrum hUnwantedSpectrum
    (theorem63DirectedTangent Z V)
    (hasTheorem63DirectedTangentApproximationNumbers_theorem63DirectedTangent
      Z V fun i => theorem63_singularValues_sine_lt_one T hT V Z hV hdelta
        hCompressionUpper hUnwantedLower i)
    hResidual

/-! ### Dropping the dimension comparison

Davis and Kahan's `dim X(E₀) < dim X(F₀)` does exactly one job in the printed
argument: under the paper's global separability convention it forces the trial
coordinate space to be finite-dimensional, because every infinite-dimensional
closed subspace of a separable space has the same Hilbert dimension.  Here
finite-dimensionality of `Z` is an explicit instance, so the comparison carries
no further content — and Lean has been saying so all along, since
`theorem6_3_generalizedTanTheta_of_formBounds` binds it as `_hStrictDimension`
and never uses it.

Dropping it is exactly what **Section 2's** tangent theorem needs: that theorem
is about a pair of subspaces of *equal* rank, which the strict inequality
excludes, so it cannot be obtained by specialising a statement that assumes
`rank Z < rank V`. -/

/-- **Theorem 6.3 with no dimension comparison — the equal-rank form.**

Every hypothesis is a form bound or a spectral separation; nothing compares the
ranks of `Z` and `V`, so this applies to the equal-rank pairs of Section 2. -/
theorem theorem6_3_generalizedTanTheta_of_formBounds_equalRank
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (hV : T.Reduces V) {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : Z,
      RCLike.re ⟪theorem63Compression T Z z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ)
    (hResidual : N.Mem (theorem63Residual T Z)) :
    N.Mem (theorem63DirectedTangent Z V) ∧
      delta * N.gauge (theorem63DirectedTangent Z V) ≤
        N.gauge (theorem63Residual T Z) :=
  ExactSinTheta.mem_and_scaled_gauge_le_of_all_scaled_kyFan_le N.toFanDominantIdealFamily hdelta hResidual
    (theorem6_3_all_kyFan_core_directedTangent Z V T hT hV hdelta
      hCompressionUpper hUnwantedLower)

/-- **Theorem 6.3 at equal rank, in the source's spectral form.**

The Ritz compression's spectrum lies in `[β, α]` and the unwanted restriction's
in `[α + δ, ∞)`; the conclusion is the ideal-gauge tangent bound for the
representative this file constructs.  No dimension comparison, no assumed
tangent representative — this is the Section 2 tangent theorem's residual half
at arbitrary unitarily invariant ideal-gauge scope. -/
theorem theorem6_3_generalizedTanTheta_equalRank_spectral
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    (T : H →L[ℂ] H) (hT : T.IsSymmetric) (hV : T.Reduces V)
    {beta alpha delta : ℝ} (_hbetaalpha : beta ≤ alpha) (hdelta : 0 < delta)
    (hCompressionSpectrum :
      spectrum ℝ (theorem63Compression T Z) ⊆ Set.Icc beta alpha)
    (hUnwantedSpectrum :
      spectrum ℝ (T.restrict (hV.orthogonalComplement).1) ⊆
        Set.Ici (alpha + delta))
    (hResidual : N.Mem (theorem63Residual T Z)) :
    N.Mem (theorem63DirectedTangent Z V) ∧
      delta * N.gauge (theorem63DirectedTangent Z V) ≤
        N.gauge (theorem63Residual T Z) := by
  have hTsa : IsSelfAdjoint T :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT
  have hMsa : IsSelfAdjoint (theorem63Compression T Z) := by
    simpa [theorem63Compression, DavisKahan.Sylvester.compressOperator] using
      DavisKahan.Sylvester.isSelfAdjoint_compressOperator hTsa Z
  have hCompressionUpper : ∀ z : Z,
      RCLike.re ⟪theorem63Compression T Z z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2 := by
    intro z
    refine SpectralOrder.re_inner_le_of_spectrum_subset_Iic
      (theorem63Compression T Z) hMsa ?_ z
    intro r hr
    exact (hCompressionSpectrum hr).2
  have hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ := fun y hy =>
    SpectralOrder.le_re_inner_on_subspace_of_restriction_spectrum_subset_Ici
      hT (hV.orthogonalComplement).1 hUnwantedSpectrum hy
  exact theorem6_3_generalizedTanTheta_of_formBounds_equalRank Z V N T hT hV
    hdelta hCompressionUpper hUnwantedLower hResidual

end DirectedTangentExistence

end TanTheta
end DavisKahan
end TauCeti
