/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/

import LeanPool.DavisKahan.DavisKahan.TanTheta.Theorem63FiniteSource
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.AngleIdentity
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Polar.CFCBridge
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.PrincipalAngles.Equisingular
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! # Theorem63Directed Angle Bridge -/

open TauCeti.DavisKahan.Angle


/-!
# Identifying the Theorem 6.3 tangent with the paper's directed angle

`theorem63DirectedTangent` was constructed in the right singular basis of the
directed sine block, with diagonal entries `tan (arcsin sigma_i)`.  The source
paper angle `directedAngleBlockC Z V` is defined independently, by
continuous functional calculus from the positive cosine overlap.

This file proves that these are the same operator on the trial coordinates.
More precisely, once the source gap has excluded `sigma_i = 1`,

`theorem63DirectedTangent Z V =
  Z.subtypeL ∘L cfc Real.tan (directedAngleBlockC Z V)`.

This is the semantic bridge needed by the ambient `tan Theta` half of the
Davis--Kahan theorem: the singular-basis representative used by Theorem 6.3 is
not merely equisingular with the paper tangent; it is the paper's literal
directed functional-calculus tangent followed by the canonical inclusion.
-/

open scoped InnerProductSpace BigOperators

namespace TauCeti
namespace DavisKahan
namespace TanTheta

open ExactSinTheta
open Module (finrank)
open scoped TauCeti.CompleteSubspace

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The bounded endomorphisms of a projected coordinate subspace form the
C-star algebra used by Mathlib's continuous functional calculus. -/
noncomputable local instance instCStarAlgebraSubspaceCoordinateDirectedAngleBridge
    (W : Submodule ℂ H) [W.HasOrthogonalProjection] :
    CStarAlgebra (W →L[ℂ] W) :=
  inferInstance

/-! ## A finite-dimensional CFC eigenvector bridge

Tau Ceti's finite self-adjoint functional calculus evaluates arbitrary real
functions on an eigenbasis, whereas Mathlib's `cfc` asks only for continuity on
the spectrum.  The existing bridge in `Polar.Decomposition` assumes global
continuity.  Here we need `tan`, which is only continuous on the pole-free
spectrum, so we record the same bridge at its natural `ContinuousOn` strength.
-/

private theorem selfAdjointFunctionalCalculus_toContinuousLinearMap_eq_cfc_of_continuousOn
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [FiniteDimensional ℂ K] [CompleteSpace K]
    {T : K →ₗ[ℂ] K} (hT : T.IsSymmetric) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ T.toContinuousLinearMap)) :
    (selfAdjointFunctionalCalculus hT f).toContinuousLinearMap =
      cfc f T.toContinuousLinearMap := by
  have ha : IsSelfAdjoint T.toContinuousLinearMap :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT
  have hcont : Continuous (calculusStarAlgHom hT) :=
    AddMonoidHomClass.continuous_of_bound (calculusStarAlgHom hT) 1 fun g => by
      rw [one_mul]
      exact norm_calculusStarAlgHom_le hT g
  have hhom : cfcHom ha = calculusStarAlgHom hT :=
    cfcHom_eq_of_continuous_of_map_id ha _ hcont (calculusStarAlgHom_id hT)
  rw [cfc_apply f T.toContinuousLinearMap ha hf, hhom]
  have key :
      (selfAdjointFunctionalCalculus hT
        (extendSymbol (⟨_, hf.domRestrict⟩ :
          C(spectrum ℝ T.toContinuousLinearMap, ℝ)))).toContinuousLinearMap =
        (selfAdjointFunctionalCalculus hT f).toContinuousLinearMap := by
    congr 1
    refine selfAdjointFunctionalCalculus_congr hT fun i => ?_
    rw [extendSymbol_apply_of_mem _
      (eigenvalues_mem_spectrum_toContinuousLinearMap hT i)]
    rfl
  exact key.symm

private theorem cfc_apply_of_apply_eq_smul_finite
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [FiniteDimensional ℂ K] [CompleteSpace K]
    {T : K →L[ℂ] K} (hT : IsSelfAdjoint T) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ T))
    {x : K} {lam : ℝ} (hx : T x = ((lam : ℝ) : ℂ) • x) :
    cfc f T x = ((f lam : ℝ) : ℂ) • x := by
  have hsym : T.toLinearMap.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  have hbridge :=
    selfAdjointFunctionalCalculus_toContinuousLinearMap_eq_cfc_of_continuousOn
      hsym f hf
  have hTroundtrip : T.toLinearMap.toContinuousLinearMap = T := by
    ext y
    rfl
  rw [hTroundtrip] at hbridge
  have happ := congrArg (fun S : K →L[ℂ] K => S x) hbridge
  rw [← happ]
  exact selfAdjointFunctionalCalculus_apply_of_apply_eq_smul hsym f hx

section

variable (Z V : Submodule ℂ H) [Z.HasOrthogonalProjection]
  [V.HasOrthogonalProjection] [FiniteDimensional ℂ Z]

private abbrev directedSine : Z →L[ℂ] H :=
  theorem63DirectedSineBlock Z V

private abbrev coordinateSine : Z →L[ℂ] Vᗮ :=
  sineBlockC Z V

private abbrev coordinateSineModulus : Z →L[ℂ] Z :=
  sineBlockModulusC Z V

/-- The ambient directed sine block is the coordinate sine block followed by
inclusion of `V-perp`. -/
private theorem subtypeL_comp_adjoint_subtypeL
    (W : Submodule ℂ H) [W.HasOrthogonalProjection] :
    W.subtypeL ∘L W.subtypeL.adjoint = W.starProjection := by
  rw [Submodule.adjoint_subtypeL]
  rfl

omit [FiniteDimensional ℂ ↥Z] in
omit [Z.HasOrthogonalProjection] in
private theorem directedSine_eq_subtype_comp_coordinateSine :
    directedSine Z V = Vᗮ.subtypeL ∘L coordinateSine Z V := by
  rw [directedSine, coordinateSine, theorem63DirectedSineBlock, sineBlockC,
    ← ContinuousLinearMap.comp_assoc, subtypeL_comp_adjoint_subtypeL]

/-- Inclusion of `V-perp` is isometric on the range of the coordinate sine
block, in the exact Gram form used by the modulus argument. -/
private theorem adjoint_subtypeL_comp_subtypeL
    (W : Submodule ℂ H) [W.HasOrthogonalProjection] :
    W.subtypeL.adjoint ∘L W.subtypeL = ContinuousLinearMap.id ℂ W := by
  ext x
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    Submodule.adjoint_subtypeL, Submodule.subtypeL_apply]
  exact congrArg (fun z : W => (z : H))
    (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x)

omit [FiniteDimensional ℂ ↥Z] in
omit [Z.HasOrthogonalProjection] in
private theorem subtype_adjoint_comp_subtype_comp_coordinateSine :
    Vᗮ.subtypeL.adjoint ∘L Vᗮ.subtypeL ∘L coordinateSine Z V =
      coordinateSine Z V := by
  rw [← ContinuousLinearMap.comp_assoc,
    adjoint_subtypeL_comp_subtypeL, ContinuousLinearMap.id_comp]

omit [FiniteDimensional ℂ ↥Z] in
/-- Hence the ambient directed sine and the coordinate sine have exactly the
same Gram operator on `Z`. -/
private theorem directedSine_gram_eq_coordinateSine_gram :
    (directedSine Z V).adjoint ∘L directedSine Z V =
      (coordinateSine Z V).adjoint ∘L coordinateSine Z V := by
  rw [directedSine_eq_subtype_comp_coordinateSine Z V]
  exact gram_comp_left_of_adjoint_comp_self_comp
    (subtype_adjoint_comp_subtype_comp_coordinateSine Z V)

/-- The positive coordinate sine modulus acts on the finite-source right
singular basis by the corresponding directed sine singular value. -/
private theorem coordinateSineModulus_apply_rightSingularBasis
    (i : Fin (finrank ℂ Z)) :
    coordinateSineModulus Z V
        (finiteSourceRightSingularBasis (directedSine Z V) i) =
      ((finiteSourceSingularValue (directedSine Z V) i : ℝ) : ℂ) •
        finiteSourceRightSingularBasis (directedSine Z V) i := by
  let S := directedSine Z V
  let B := coordinateSine Z V
  let M := coordinateSineModulus Z V
  let b := finiteSourceRightSingularBasis S
  let sigma := finiteSourceSingularValue S i
  have hgram : S.adjoint ∘L S = B.adjoint ∘L B := by
    simpa [S, B] using directedSine_gram_eq_coordinateSine_gram Z V
  have hSgram :
      (S.adjoint ∘L S) (b i) =
        (((sigma : ℝ) : ℂ) * ((sigma : ℝ) : ℂ)) • b i := by
    by_cases hsigma : sigma = 0
    · have hSz : S (b i) = 0 := by
        simpa [S, b, sigma] using
          apply_finiteSourceRightSingularBasis_eq_zero_of_singularValue_eq_zero
            S hsigma
      simp [hSz, hsigma]
    · have hS :=
        apply_finiteSourceRightSingularBasis_eq_smul_leftSingularVector S i
      have hSadj := adjoint_apply_finiteSourceLeftSingularVector S hsigma
      rw [ContinuousLinearMap.comp_apply, hS, map_smul, hSadj, smul_smul]
  have hBgram :
      (B.adjoint ∘L B) (b i) =
        (((sigma : ℝ) : ℂ) * ((sigma : ℝ) : ℂ)) • b i := by
    rw [← hgram]
    exact hSgram
  have hM_sq :
      M (M (b i)) =
        (((sigma : ℝ) : ℂ) * ((sigma : ℝ) : ℂ)) • b i := by
    have hmod := ContinuousLinearMap.modulus_mul_self B
    change (M * M) (b i) = _
    rw [show M = ContinuousLinearMap.modulus B by rfl, hmod]
    exact hBgram
  have hMnonneg : (0 : Z →L[ℂ] Z) ≤ M := by
    exact ContinuousLinearMap.modulus_nonneg B
  have hMpos : (M : Z →ₗ[ℂ] Z).IsPositive :=
    ((ContinuousLinearMap.nonneg_iff_isPositive (f := M)).mp hMnonneg).toLinearMap
  have hsigma0 : 0 ≤ sigma := finiteSourceSingularValue_nonneg S i
  have hroot := LinearMap.IsPositive.apply_eq_smul_of_apply_apply_eq_smul
    hMpos hsigma0 hM_sq
  simpa [S, M, b, sigma] using hroot

/-- The source-directed angle acts on the same right singular basis by
`arcsin sigma_i`. -/
private theorem sourceDirectedAngle_apply_rightSingularBasis
    (i : Fin (finrank ℂ Z)) :
    directedAngleBlockC Z V
        (finiteSourceRightSingularBasis (directedSine Z V) i) =
      ((Real.arcsin (finiteSourceSingularValue (directedSine Z V) i) : ℝ) : ℂ) •
        finiteSourceRightSingularBasis (directedSine Z V) i := by
  let M := coordinateSineModulus Z V
  let b := finiteSourceRightSingularBasis (directedSine Z V)
  let sigma := finiteSourceSingularValue (directedSine Z V) i
  have hMsa : IsSelfAdjoint M := ContinuousLinearMap.modulus_isSelfAdjoint _
  have hMeig : M (b i) = ((sigma : ℝ) : ℂ) • b i := by
    simpa [M, b, sigma] using
      coordinateSineModulus_apply_rightSingularBasis Z V i
  rw [sourceDirectedAngleC_eq_arcsin_sineModulus Z V]
  exact cfc_apply_of_apply_eq_smul_finite hMsa Real.arcsin
    Real.continuous_arcsin.continuousOn hMeig

omit [FiniteDimensional ℂ ↥Z] in
omit [Z.HasOrthogonalProjection] in
/-- The ambient-coordinate and subspace-coordinate sine blocks have the same
operator norm. -/
private theorem norm_directedSine_eq_norm_coordinateSine :
    ‖directedSine Z V‖ = ‖coordinateSine Z V‖ := by
  have hnorm : ∀ z : Z, ‖directedSine Z V z‖ = ‖coordinateSine Z V z‖ := by
    intro z
    rw [directedSine_eq_subtype_comp_coordinateSine Z V,
      ContinuousLinearMap.comp_apply]
    rfl
  apply le_antisymm
  · refine (directedSine Z V).opNorm_le_bound
      (norm_nonneg (coordinateSine Z V)) fun z => ?_
    rw [hnorm z]
    exact (coordinateSine Z V).le_opNorm z
  · refine (coordinateSine Z V).opNorm_le_bound
      (norm_nonneg (directedSine Z V)) fun z => ?_
    rw [← hnorm z]
    exact (directedSine Z V).le_opNorm z

omit [Z.HasOrthogonalProjection] in
/-- If every finite-source directed sine singular value is strictly below one,
then the whole directed sine block has norm strictly below one.  The zero
coordinate-space case is handled by the vanishing of all approximation
numbers above the source dimension. -/
private theorem norm_directedSine_lt_one_of_all_singular_lt_one
    (hlt : ∀ i, finiteSourceSingularValue (directedSine Z V) i < 1) :
    ‖directedSine Z V‖ < 1 := by
  by_cases hpos : 0 < finrank ℂ Z
  · let i0 : Fin (finrank ℂ Z) := ⟨0, hpos⟩
    have h0 := hlt i0
    have happrox :=
      approximationSingularValue_eq_finiteSourceSingularValue
        (directedSine Z V) i0
    have hi0 : (i0 : ℕ) = 0 := rfl
    rw [hi0, approximationSingularValue_zero] at happrox
    rw [happrox]
    exact h0
  · have hzero : finrank ℂ Z ≤ 0 := Nat.le_zero.mpr (Nat.eq_zero_of_not_pos hpos)
    have happrox := approximationSingularValue_eq_zero_of_finrank_le_complex
      Z (directedSine Z V) hzero
    rw [approximationSingularValue_zero] at happrox
    rw [happrox]
    norm_num

/-- The same pole exclusion holds for the positive coordinate sine modulus. -/
private theorem norm_coordinateSineModulus_lt_one_of_all_singular_lt_one
    (hlt : ∀ i, finiteSourceSingularValue (directedSine Z V) i < 1) :
    ‖coordinateSineModulus Z V‖ < 1 := by
  have hS := norm_directedSine_lt_one_of_all_singular_lt_one Z V hlt
  have hSB := norm_directedSine_eq_norm_coordinateSine Z V
  change ‖ContinuousLinearMap.modulus (coordinateSine Z V)‖ < 1
  rw [ContinuousLinearMap.norm_modulus, ← hSB]
  exact hS

/-- Under the same no-pole hypothesis, every spectral value of the literal
source angle lies strictly below `pi/2`. -/
private theorem spectrum_sourceDirectedAngle_lt_pi_div_two
    (hlt : ∀ i, finiteSourceSingularValue (directedSine Z V) i < 1)
    {t : ℝ} (ht : t ∈ spectrum ℝ (directedAngleBlockC Z V)) :
    0 ≤ t ∧ t < Real.pi / 2 := by
  let M := coordinateSineModulus Z V
  have hMsa : IsSelfAdjoint M := ContinuousLinearMap.modulus_isSelfAdjoint _
  have hMnorm : ‖M‖ < 1 := by
    simpa [M] using
      norm_coordinateSineModulus_lt_one_of_all_singular_lt_one Z V hlt
  rw [sourceDirectedAngleC_eq_arcsin_sineModulus Z V,
    cfc_map_spectrum (R := ℝ) Real.arcsin M hMsa
      Real.continuous_arcsin.continuousOn] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  have hs0 : 0 ≤ s :=
    spectrum_nonneg_of_nonneg
      (ContinuousLinearMap.modulus_nonneg (coordinateSine Z V)) hs
  have hnorm : |s| ≤ ‖M‖ * ‖(1 : Z →L[ℂ] Z)‖ :=
    spectrum.norm_le_norm_mul_of_mem hs
  have hone : ‖(1 : Z →L[ℂ] Z)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hslt : s < 1 := by
    have habs : |s| ≤ ‖M‖ := by
      refine hnorm.trans ?_
      calc
        ‖M‖ * ‖(1 : Z →L[ℂ] Z)‖ ≤ ‖M‖ * 1 :=
          mul_le_mul_of_nonneg_left hone (norm_nonneg _)
        _ = ‖M‖ := mul_one _
    have hsle : s ≤ ‖M‖ := (le_abs_self s).trans habs
    linarith
  exact ⟨Real.arcsin_nonneg.mpr hs0, Real.arcsin_lt_pi_div_two.mpr hslt⟩

/-- `tan` is continuous on the spectrum of the literal source angle whenever
Theorem 6.3's directed sine singular values stay below one. -/
private theorem continuousOn_tan_sourceDirectedAngle
    (hlt : ∀ i, finiteSourceSingularValue (directedSine Z V) i < 1) :
    ContinuousOn Real.tan (spectrum ℝ (directedAngleBlockC Z V)) := by
  exact Real.continuousOn_tan.mono (by
    intro t ht
    have h := spectrum_sourceDirectedAngle_lt_pi_div_two Z V hlt ht
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, h.1], h.2⟩))

/-- **M12 coordinate identity.**  The diagonal coordinate operator hidden
inside `theorem63DirectedTangent` is exactly `tan` of the source-defined
Davis--Kahan directed angle. -/
theorem theorem63DirectedTangentCoordinate_eq_cfcTan_sourceDirectedAngle
    (hlt : ∀ i, finiteSourceSingularValue
      (theorem63DirectedSineBlock Z V) i < 1) :
    (diagOp (finiteSourceRightSingularBasis (theorem63DirectedSineBlock Z V))
      (theorem63DirectedTangentDiagonal Z V)).toContinuousLinearMap =
      cfc Real.tan (directedAngleBlockC Z V) := by
  let S := directedSine Z V
  let b := finiteSourceRightSingularBasis S
  let A := directedAngleBlockC Z V
  have hAsa : IsSelfAdjoint A := by
    exact cfc_predicate Real.arccos (cosineBlockModulusC Z V)
  have htan : ContinuousOn Real.tan (spectrum ℝ A) := by
    simpa [A, S, directedSine] using continuousOn_tan_sourceDirectedAngle Z V hlt
  have hlin :
      diagOp b (theorem63DirectedTangentDiagonal Z V) =
        (cfc Real.tan A).toLinearMap := by
    apply b.toBasis.ext
    intro i
    rw [OrthonormalBasis.coe_toBasis]
    have hAeig : A (b i) =
        ((Real.arcsin (finiteSourceSingularValue S i) : ℝ) : ℂ) • b i := by
      simpa [A, b, S] using sourceDirectedAngle_apply_rightSingularBasis Z V i
    have hcfceig : cfc Real.tan A (b i) =
        ((Real.tan (Real.arcsin (finiteSourceSingularValue S i)) : ℝ) : ℂ) • b i :=
      cfc_apply_of_apply_eq_smul_finite hAsa Real.tan htan hAeig
    rw [diagOp_apply_basis]
    change (((theorem63DirectedTangentDiagonal Z V i : ℝ) : ℂ) • b i) =
      cfc Real.tan A (b i)
    simpa [theorem63DirectedTangentDiagonal, S, directedSine] using hcfceig.symm
  apply ContinuousLinearMap.ext
  intro x
  simpa using LinearMap.congr_fun hlin x

/-- **M12 main identity.**  The Theorem 6.3 directed tangent representative is
literally the paper's source-directed `cfc tan Theta_0`, followed by inclusion
of the trial coordinates into the ambient Hilbert space. -/
theorem theorem63DirectedTangent_eq_subtype_comp_cfcTan_sourceDirectedAngle
    (hlt : ∀ i, finiteSourceSingularValue
      (theorem63DirectedSineBlock Z V) i < 1) :
    theorem63DirectedTangent Z V =
      Z.subtypeL ∘L cfc Real.tan (directedAngleBlockC Z V) := by
  rw [theorem63DirectedTangent,
    theorem63DirectedTangentCoordinate_eq_cfcTan_sourceDirectedAngle Z V hlt]

/-- Source-gap specialization: no hypothesis beyond the hypotheses already used
by Theorem 6.3 is needed for the directed-tangent identification. -/
theorem theorem63DirectedTangent_eq_subtype_comp_cfcTan_sourceDirectedAngle_of_form_gap
    (T : H →L[ℂ] H) (hT : T.IsSymmetric) (hV : T.Reduces V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : Z,
      RCLike.re ⟪theorem63Compression T Z z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ) :
    theorem63DirectedTangent Z V =
      Z.subtypeL ∘L cfc Real.tan (directedAngleBlockC Z V) := by
  apply theorem63DirectedTangent_eq_subtype_comp_cfcTan_sourceDirectedAngle Z V
  exact theorem63_singularValues_sine_lt_one
    T hT V Z hV hdelta hCompressionUpper hUnwantedLower

end

end
end TanTheta
end DavisKahan
end TauCeti
