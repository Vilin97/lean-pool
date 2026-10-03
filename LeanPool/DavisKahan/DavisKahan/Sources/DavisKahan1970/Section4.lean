/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.DirectRotation
public import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.DirectRotation.ShortRotationCounterexample
public import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.RestrictedDisplacementExtremal
public import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.DisplacementSquareExtremal
public import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.BasisAngleEnergy
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.CompactSpectralDecomposition
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.VectorAngle
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.Family.GramGauge

/-! # Section4 -/

@[expose] public section

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Section 4: extremal properties of the direct rotation

Source-numbered names for the Section 4 results.  Section 4 inherits the
matched-crossed-defect and compact-angle hypotheses of Theorem 3.1 and
Corollary 3.1.  The source statements use infinite angle sequences and
orthonormal bases; finite-dimensional aliases remain available as
specializations.

The arbitrary-dimensional complex API provides the approximation-number form
of Proposition 4.1 for both the canonical acute direct rotation and a chosen
matched-defect completion.  Proposition 4.2 uses the approximation-number
principal-sine sequence of `P_{Vᗮ}|_U`, so its extended-real sum includes the
case where the source right-hand side is infinite.  `Section4Real.lean` provides
the corresponding real Proposition 4.2 statement and the established real
Section 4 endpoints.

Proposition 4.4 is represented by its compiled counterexample, as required by
the repository's source-coverage convention for a false printed claim.
-/

namespace TauCeti
namespace DavisKahan1970


/-! ## Proposition 4.1 -/

/-- **Davis--Kahan 1970, Proposition 4.1.**  Every singular value of the displacement
restricted to the source subspace is minimized by the direct rotation, over all isometries
carrying `U` onto `V`. -/
alias proposition4_1 := DavisKahan.FiniteDimensional.singularValues_restrictedDisplacement_le

/-- The direct rotation's restricted-displacement singular values, identified: the
principal-plane chords, and zero past the last nontrivial angle.  This is the value the
minimum in `proposition4_1` takes. -/
alias proposition4_1_directRotationValues :=
  DavisKahan.FiniteDimensional.singularValues_restrictedDisplacement_directRotation

/-! ## Corollary 4.1 -/

/-- **Davis--Kahan 1970, Corollary 4.1.**  Singular-value domination passes to every
unitarily invariant norm of the restricted displacement. -/
alias corollary4_1 := DavisKahan.FiniteDimensional.uiNorm_restrictedDisplacement_le

/-- Corollary 4.1 read as a minimality statement about the direct rotation. -/
alias corollary4_1_minimizer :=
  DavisKahan.FiniteDimensional.directRotation_minimizes_restrictedDisplacement_uiNorm

/-! ## Proposition 4.3 -/

/-- **Davis--Kahan 1970, Proposition 4.3, Ky Fan root.**  The prefix sums of the singular
values of the squared displacement `(1 − W)⋆(1 − W)` are minimized by the direct rotation.

Ky Fan level is the honest scope: the *individual* singular values are **not** dominated.
Pointwise domination would imply Proposition 4.4, which this repository refutes.  The
refuting configuration is recorded with the stable theorem, in the module docstring of
`DavisKahan/Geometry/Polar/DisplacementSquareExtremal.lean`. -/
alias proposition4_3_kyFan := DavisKahan.FiniteDimensional.directRotation_displacementSquare_kyFan

/-- **Davis--Kahan 1970, Proposition 4.3.**  Every unitarily invariant norm of the squared
displacement is minimized by the direct rotation. -/
alias proposition4_3 := DavisKahan.FiniteDimensional.directRotation_displacementSquare_uiNorm

/-- Proposition 4.3 read as a minimality statement about the direct rotation. -/
alias proposition4_3_minimizer :=
  DavisKahan.FiniteDimensional.directRotation_minimizes_displacementSquare_uiNorm

/-! ## Infinite-dimensional source forms

The aliases above are finite-dimensional specializations.  The declarations
below carry the arbitrary-dimensional source variables. -/

/-- **Davis--Kahan 1970, Proposition 4.1, acute arbitrary-dimensional form.**
For every unitary `W` carrying `U` onto `V`, every approximation number of the
restricted displacement is bounded below by the canonical acute direct
rotation.  The chosen-defect declaration below carries the full nonacute scope
of the paper. -/
alias proposition4_1_infiniteDimensional :=
  DavisKahan.Section4.proposition4_1_approximationNumbers


/-- **Proposition 4.1 at the nonacute compact scope inherited from Corollary
3.1.**  A crossed-defect isometry selects the direct rotation when `π/2`
principal-angle blocks are present. -/
alias proposition4_1_infiniteDimensional_nonacute :=
  DavisKahan.Section4.proposition4_1_nonacute_approximationNumbers

section Proposition41VectorForm

open scoped InnerProductSpace
open DavisKahan.ExactSinTheta
open TauCeti.ApproximationNumber

universe v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **Davis--Kahan 1970, Proposition 4.1, first formulation.**

At the compact scope inherited from Section 3, every unitary `W` carrying `U` onto `V`
admits an orthonormal family of source vectors, indexed by the nonzero principal-angle list,
whose displacement angles dominate the corresponding principal angles.  Zero principal angles
are absent from the index subtype because their asserted lower bound is automatic.

The vectors are the compact Gram singular vectors of `P_{Vᗮ}|_U`.  Thus this declaration is
the printed orthonormal-vector formulation, independently of the approximation-number
minimality formulation above. -/
theorem proposition4_1_compact_orthonormalVectors_complex
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    ∃ v : {n : ℕ // 0 < TauCeti.principalSineSequence U V n} → U,
      Orthonormal ℂ v ∧ ∀ n : {n : ℕ // 0 < TauCeti.principalSineSequence U V n},
        TauCeti.principalAngleSequence U V (n : ℕ) ≤
          TauCeti.vectorAngle ℂ (v n : H) (W (v n : H)) := by
  let _ : CompleteSpace U :=
    (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe
  let T : U →L[ℂ] H := TauCeti.principalSineOperator U V
  let A : U →L[ℂ] U := gramOperator T
  have hAc : IsCompactOperator A := hcompact.clm_comp T.adjoint
  have hAs : IsSelfAdjoint A := by
    exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (ContinuousLinearMap.isPositive_adjoint_comp_self T).isSymmetric
  have hApos : ∀ x, 0 ≤ RCLike.re ⟪A x, x⟫_ℂ :=
    fun x => (ContinuousLinearMap.isPositive_adjoint_comp_self T).re_inner_nonneg_left x
  have hseq (n : ℕ) : A.approximationNumber n =
      TauCeti.principalSineSequence U V n ^ 2 := by
    simpa only [A, T, TauCeti.principalSineSequence] using
      (TauCeti.ApproximationNumber.approximationNumber_gramOperator_complex T n)
  let e : {n : ℕ // 0 < TauCeti.principalSineSequence U V n} ≃
      {n : ℕ // 0 < A.approximationNumber n} :=
    { toFun := fun n => ⟨n, by rw [hseq]; nlinarith [n.2]⟩
      invFun := fun n => ⟨n, by
        have hn := n.2
        rw [hseq] at hn
        nlinarith [TauCeti.principalSineSequence_nonneg U V n]⟩
      left_inv := fun n => Subtype.ext rfl
      right_inv := fun n => Subtype.ext rfl }
  let v : {n : ℕ // 0 < TauCeti.principalSineSequence U V n} → U := fun n =>
    TauCeti.positiveApproximationEigenvector hAc hAs hApos (e n) (e n).2
  have hvon : Orthonormal ℂ v := by
    change Orthonormal ℂ
      ((fun n : {n : ℕ // 0 < A.approximationNumber n} =>
        TauCeti.positiveApproximationEigenvector hAc hAs hApos n n.2) ∘ e)
    exact (TauCeti.orthonormal_positiveApproximationEigenvector hAc hAs hApos).comp
      e e.injective
  refine ⟨v, hvon, fun n => ?_⟩
  let x : U := v n
  let s : ℝ := TauCeti.principalSineSequence U V n
  have hxnorm : ‖x‖ = 1 := hvon.1 n
  have hAx := TauCeti.apply_positiveApproximationEigenvector hAc hAs hApos
    (e n) (e n).2
  have hTx : ‖T x‖ = s := by
    have hen : ((e n : {n : ℕ // 0 < A.approximationNumber n}) : ℕ) = (n : ℕ) := rfl
    have hnormsq : ‖T x‖ ^ 2 = s ^ 2 := by
      calc
        ‖T x‖ ^ 2 = RCLike.re ⟪A x, x⟫_ℂ := by
          simpa only [A, gramOperator] using
            ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left T x
        _ = s ^ 2 := by
          rw [hAx, inner_smul_left, RCLike.conj_ofReal,
            RCLike.re_ofReal_mul, inner_self_eq_norm_sq, hxnorm, one_pow]
          rw [hseq, hen]
          simp only [s, mul_one]
    nlinarith [norm_nonneg (T x), n.2]
  have hproj : ‖DavisKahan.Section4.sourceCosine U V x‖ =
      Real.cos (TauCeti.principalAngleSequence U V n) := by
    have hpy := V.norm_sq_eq_add_norm_sq_starProjection (x : H)
    have hC := DavisKahan.Section4.norm_sourceCosine_eq_norm_targetProjection U V x
    have hsin := TauCeti.sin_principalAngleSequence U V n
    have htrig := Real.sin_sq_add_cos_sq (TauCeti.principalAngleSequence U V n)
    have hcos0 : 0 ≤ Real.cos (TauCeti.principalAngleSequence U V n) :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        ((neg_nonpos_of_nonneg Real.pi_div_two_pos.le).trans
          (TauCeti.principalAngleSequence_nonneg U V n))
        (TauCeti.principalAngleSequence_le_pi_div_two U V n)
    have hTdef : ‖T x‖ = ‖Vᗮ.starProjection (x : H)‖ := by
      dsimp only [T]
      rw [TauCeti.principalSineOperator_apply]
    have hxnormH : ‖(x : H)‖ = 1 := hxnorm
    rw [hxnormH, one_pow, ← hTdef, hTx] at hpy
    change 1 = ‖V.starProjection (x : H)‖ ^ 2 + s ^ 2 at hpy
    dsimp only [s] at hpy
    rw [hC]
    rw [hsin] at htrig
    rw [← sq_eq_sq₀ (norm_nonneg _) hcos0]
    nlinarith [hpy, htrig]
  have hinner := DavisKahan.Section4.competitor_real_inner_le_sourceCosine_norm
    U V W hWunitary hWmap x
  rw [hxnorm, mul_one, hproj] at hinner
  apply TauCeti.le_vectorAngle_of_unit_norm_of_re_inner_le_cos
  · exact hxnorm
  · exact Unitary.norm_map (⟨W, hWunitary⟩ : unitary (H →L[ℂ] H)) (x : H) |>.trans hxnorm
  · exact TauCeti.principalAngleSequence_nonneg U V n
  · exact (TauCeti.principalAngleSequence_le_pi_div_two U V n).trans
      (by linarith [Real.pi_pos])
  · exact hinner

end Proposition41VectorForm

section ExactCompactNonacute

open scoped InnerProductSpace
open DavisKahan.ExactSinTheta (KyFanDominantIdealFamily)

universe v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]


/-- The directed sine and positive source cosine satisfy the Pythagorean
identity on source coordinates. -/
theorem principalSineOperator_norm_sq_eq_one_sub_sourceCosine_norm_sq
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (x : U) :
    ‖TauCeti.principalSineOperator U V x‖ ^ 2 =
      ‖x‖ ^ 2 - ‖DavisKahan.Section4.sourceCosine U V x‖ ^ 2 := by
  have hpy := V.norm_sq_eq_add_norm_sq_starProjection (x : H)
  have hC := DavisKahan.Section4.norm_sourceCosine_eq_norm_targetProjection U V x
  rw [TauCeti.principalSineOperator_apply, hC]
  have hxnorm : ‖(x : H)‖ = ‖x‖ := rfl
  rw [hxnorm] at hpy
  nlinarith

/-- **The exact singular-value value in Proposition 4.1 at the inherited
compact, matched-defect scope.**  The direct rotation realizes the principal
chord `2 sin(theta_n / 2)` at every approximation-number index. -/
theorem proposition4_1_compact_nonacute_directRotationValues_complex
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (_hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℂ]
      DavisKahan.halmosTargetDefect U V)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W)
    (n : ℕ) :
    (ContinuousLinearMap.approximationNumber
        ((1 - DavisKahan.nonacuteDirectRotation U V J) ∘L
          U.starProjection) n : Real) =
      2 * Real.sin (TauCeti.principalAngleSequence U V n / 2) := by
  let _ : CompleteSpace U :=
    (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe
  let A : U →L[ℂ] H := DavisKahan.Section4.sourceRestrictedDisplacement U
    (DavisKahan.nonacuteDirectRotation U V J)
  let S : U →L[ℂ] H := TauCeti.principalSineOperator U V
  have hcut :=
    (DavisKahan.Section4.proposition4_1_nonacuteCosineDisplacementData
      U V J W hWunitary hWmap).approximationNumber_direct_cosineCutoff_eq_sine
      (S := S)
      (principalSineOperator_norm_sq_eq_one_sub_sourceCosine_norm_sq U V) n
  have hDseq := DavisKahan.Section4.sourceRestrictedDisplacement_sameApproximationSingularSequence
    U (DavisKahan.nonacuteDirectRotation U V J) n
  let a : Real := (A.approximationNumber n : Real)
  let theta : Real := TauCeti.principalAngleSequence U V n
  let shalf : Real := Real.sin (theta / 2)
  have hcos : Real.cos theta =
      Real.sqrt (1 - (TauCeti.principalSineSequence U V n) ^ 2) := by
    dsimp only [theta, TauCeti.principalAngleSequence]
    rw [Real.cos_arcsin]
  have hcosApprox : Real.cos theta =
      Real.sqrt (1 - ((TauCeti.principalSineOperator U V).approximationNumber n : Real) ^ 2) := by
    simpa only [TauCeti.principalSineSequence] using hcos
  have hcutCos : 1 - a ^ 2 / 2 = Real.cos theta := by
    simpa only [a, A, S] using hcut.trans hcosApprox.symm
  have hdouble : Real.cos theta = 1 - 2 * shalf ^ 2 := by
    have htrig := Real.sin_sq_add_cos_sq (theta / 2)
    dsimp only [shalf]
    calc
      Real.cos theta = Real.cos (theta / 2 + theta / 2) := by congr 1; ring
      _ = Real.cos (theta / 2) * Real.cos (theta / 2) -
          Real.sin (theta / 2) * Real.sin (theta / 2) := by rw [Real.cos_add]
      _ = 1 - 2 * Real.sin (theta / 2) ^ 2 := by nlinarith
  have haSq : a ^ 2 = (2 * shalf) ^ 2 := by
    rw [hdouble] at hcutCos
    nlinarith
  have htheta0 : 0 <= theta := TauCeti.principalAngleSequence_nonneg U V n
  have hthetaPi : theta <= Real.pi :=
    (TauCeti.principalAngleSequence_le_pi_div_two U V n).trans (by linarith [Real.pi_pos])
  have hshalf0 : 0 <= shalf := by
    dsimp only [shalf]
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have ha0 : 0 <= a := by
    dsimp only [a]
    exact A.approximationNumber_nonneg n
  have ha : a = 2 * shalf := (sq_eq_sq₀ ha0 (mul_nonneg (by norm_num) hshalf0)).1 haSq
  change (ContinuousLinearMap.approximationNumber
      ((1 - DavisKahan.nonacuteDirectRotation U V J) ∘L U.starProjection) n : Real) = _
  have hD : ContinuousLinearMap.approximationNumber
      ((1 - DavisKahan.nonacuteDirectRotation U V J) ∘L U.starProjection) n =
      A.approximationNumber n := by
    simpa only [A] using hDseq
  rw [hD]
  simpa only [a, shalf, theta] using ha

/-- **Proposition 4.1 with both printed formulations and the inherited compact,
matched-defect scope in one declaration.** -/
theorem proposition4_1_compact_nonacute_complex
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℂ]
      DavisKahan.halmosTargetDefect U V)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    (∃ v : {n : ℕ // 0 < TauCeti.principalSineSequence U V n} → U,
      Orthonormal ℂ v ∧
        ∀ n : {n : ℕ // 0 < TauCeti.principalSineSequence U V n},
          TauCeti.principalAngleSequence U V (n : ℕ) ≤
            TauCeti.vectorAngle ℂ (v n : H) (W (v n : H))) ∧
      (∀ n : ℕ,
        (ContinuousLinearMap.approximationNumber
            ((1 - DavisKahan.nonacuteDirectRotation U V J) ∘L
              U.starProjection) n : Real) =
          2 * Real.sin (TauCeti.principalAngleSequence U V n / 2)) ∧
      ∀ n : ℕ,
        ContinuousLinearMap.approximationNumber
            ((1 - DavisKahan.nonacuteDirectRotation U V J) ∘L
              U.starProjection) n ≤
          ContinuousLinearMap.approximationNumber
            ((1 - W) ∘L U.starProjection) n := by
  refine ⟨proposition4_1_compact_orthonormalVectors_complex U V hcompact W hWunitary hWmap,
    ?_, fun n => ?_⟩
  · exact proposition4_1_compact_nonacute_directRotationValues_complex
      U V hcompact J W hWunitary hWmap
  · exact DavisKahan.Section4.proposition4_1_nonacute_restrictedDisplacement_approximationNumbers
      U V J W hWunitary hWmap n

/-- **Corollary 4.1 at the inherited compact, matched-defect scope.** -/
theorem corollary4_1_compact_nonacute_complex
    (N : DavisKahan.ExactSinTheta.FanDominantIdealFamily (𝕜 := ℂ))
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (_hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℂ]
      DavisKahan.halmosTargetDefect U V)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W)
    (hWmem : N.Mem ((1 - W) ∘L U.starProjection)) :
    N.Mem ((1 - DavisKahan.nonacuteDirectRotation U V J) ∘L U.starProjection) ∧
      N.gauge ((1 - DavisKahan.nonacuteDirectRotation U V J) ∘L
          U.starProjection) ≤
        N.gauge ((1 - W) ∘L U.starProjection) :=
  DavisKahan.Section4.restrictedDisplacement_idealGauge_le N
    (DavisKahan.Section4.nonacute_restrictedDisplacementDominance
      U V J W hWunitary hWmap) hWmem

end ExactCompactNonacute

section Corollary4_1Infinite

open DavisKahan.ExactSinTheta (KyFanDominantIdealFamily)

universe v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **Davis--Kahan 1970, Corollary 4.1 at the matched-crossed-defect scope.**
Approximation-number minimality of a chosen direct rotation promotes to every
Ky-Fan-dominant unitarily invariant ideal gauge. -/
theorem corollary4_1_infiniteDimensional_nonacute
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℂ]
      DavisKahan.halmosTargetDefect U V)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W)
    (hWmem : N.Mem ((1 - W) ∘L U.starProjection)) :
    N.Mem ((1 - DavisKahan.nonacuteDirectRotation
          U V J) ∘L U.starProjection) ∧
      N.gauge ((1 - DavisKahan.nonacuteDirectRotation
          U V J) ∘L U.starProjection) ≤
        N.gauge ((1 - W) ∘L U.starProjection) :=
  DavisKahan.Section4.restrictedDisplacement_idealGauge_le N
    (DavisKahan.Section4.nonacute_restrictedDisplacementDominance
      U V J W hWunitary hWmap) hWmem

/-- **Davis--Kahan 1970, Corollary 4.1 at the acute arbitrary-dimensional scope.**
For a uniformly acute pair the canonical direct rotation is the minimizer, and its
approximation-number minimality promotes to every Ky-Fan-dominant unitarily invariant
ideal gauge.  Membership in the ideal is concluded rather than assumed, matching
`corollary4_1_real`; `corollary4_1_infiniteDimensional_nonacute` carries the same
statement at the matched-crossed-defect scope the paper inherits from Corollary 3.1. -/
theorem corollary4_1_infiniteDimensional
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : DavisKahan.IsUniformlyAcute U V)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W)
    (hWmem : N.Mem ((1 - W) ∘L U.starProjection)) :
    N.Mem ((1 - DavisKahan.spectraDirectRotation
          U V hacute) ∘L U.starProjection) ∧
      N.gauge ((1 - DavisKahan.spectraDirectRotation
          U V hacute) ∘L U.starProjection) ≤
        N.gauge ((1 - W) ∘L U.starProjection) :=
  DavisKahan.Section4.restrictedDisplacement_idealGauge_le N
    (DavisKahan.Section4.infinite_restrictedDisplacementDominance
      U V hacute W hWunitary hWmap) hWmem

end Corollary4_1Infinite

/-- **Davis--Kahan 1970, Proposition 4.2, at the printed infinite-dimensional
scope.**  The principal sines are the approximation numbers of
`P_{Vᗮ}|_U`; the extended-real sum includes the case where the printed right
side is infinite. -/
alias proposition4_2_infiniteDimensional :=
  DavisKahan.Section4.tsum_displacementAngleSineSq_ge_tsum_sq_sin_principalAngleSequence

section Proposition42SourceScope

universe u4

variable {H : Type u4} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Davis--Kahan 1970, Proposition 4.2, carrying the Section 4 setup it is
printed under.**

Section 4 opens, inside the Proposition 4.1 block, by fixing the
compact/classification setup: the principal sine operator is compact, and every
unitary carrying `Uℋ` onto `Vℋ` factors as `V = UZ` with the principal angles
ordered.  Proposition 4.2 is printed under that setup and does not restate it.

`proposition4_2_infiniteDimensional` proves the inequality without either
hypothesis, which is a stronger and correct theorem but not, by this
repository's contract, automatically an exact witness for the printed one.  This
wrapper is the source-shaped statement: it carries the inherited hypotheses
exactly as Section 4 imposes them, and discharges them by invoking the stronger
result, which needs neither.

**The crossed-defect hypothesis is a proposition, not an isometry.**  Section 4
inherits the *condition* under which the direct rotation exists; the identifying
isometry is something Theorem 3.1 produces from it, not something a caller
supplies.  `CrossedDefectsEquivalent` is that condition -- `Nonempty` of the
isometry -- and taking it instead of a chosen `J` keeps proof data out of the
public statement.  Corrected 2026-09-05 after a source-first review.

Keeping both is deliberate.  The reusable theorem stays as strong as it is, and
the canonical source endpoint stays faithful to what Davis and Kahan printed. -/
theorem proposition4_2_compact_nonacute
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (_hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (_hcrossed : DavisKahan.CrossedDefectsEquivalent U V)
    {ι : Type u4} (b : HilbertBasis ι ℂ U)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    (∑' n : ℕ, ENNReal.ofReal
        (Real.sin (TauCeti.principalAngleSequence U V n)) ^ 2) ≤
      ∑' i, ENNReal.ofReal
        (DavisKahan.Section4.displacementAngleSineSq W ((b i : U) : H)) :=
  DavisKahan.Section4.tsum_displacementAngleSineSq_ge_tsum_sq_sin_principalAngleSequence
    U V b W hWunitary hWmap

end Proposition42SourceScope

/-- **Davis--Kahan 1970, Proposition 4.3, at the printed scope.**  In an arbitrary complex
Hilbert space, the Ky Fan prefix sums of `(1 − W)⋆(1 − W)` are minimized by the direct
rotation, over all unitaries `W` carrying `U` onto `V`.

Ky Fan level is the honest scope here for the same reason as in `proposition4_3_kyFan`:
pointwise domination of the individual singular values would imply Proposition 4.4, which
this repository refutes. -/
alias proposition4_3_infiniteDimensional :=
  DavisKahan.Section4.proposition4_3_squaredDisplacement_kyFan

/-- **Davis--Kahan 1970, Proposition 4.3 at the compact matched-crossed-defect scope.**
The chosen defect equivalence selects the paper direct rotation on the right-angle blocks. -/
alias proposition4_3_infiniteDimensional_nonacute :=
  DavisKahan.Section4.proposition4_3_nonacute_squaredDisplacement_kyFan

/-! ### Proposition 4.3 and unitarily invariant gauges

The alias above stops at Ky Fan, which is where its proof stops.  The printed
clause is about every unitarily invariant norm, and in infinite dimensions the
carrier of that phrase is an arbitrary Ky-Fan-dominant symmetric operator ideal
family, exactly as for Corollary 4.1.  The promotion is
`FanDominantIdealFamily.majorization_mem_and_gauge_le`, whose hypothesis is
the Ky Fan domination this alias supplies.

Fan dominance constrains the prefix sums of the approximation numbers.  This is
the source quantity used by the unitarily invariant gauge statement and is
consistent with the compiled Proposition 4.4 counterexample. -/

section IdealGauge

open DavisKahan (IsUniformlyAcute)
open DavisKahan (spectraDirectRotation)
open DavisKahan.ExactSinTheta (KyFanDominantIdealFamily)

universe v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **Davis--Kahan 1970, Proposition 4.3, at the printed scope, for every
unitarily invariant norm.**

In an arbitrary complex Hilbert space, for every Ky-Fan-dominant symmetric ideal
family of operators, the squared full displacement `(1 − W)⋆(1 − W)` of the
direct rotation lies in the ideal and its gauge is least among all unitaries `W`
carrying `U` onto `V`.  Membership of the minimizer is **concluded**, not
assumed; only the competitor is assumed to lie in the ideal.

This is `proposition4_3_infiniteDimensional` promoted through
`FanDominantIdealFamily.majorization_mem_and_gauge_le`.  The promotion consumes
Ky Fan prefix sums only: no pointwise approximation-number domination is claimed
here, and none is true. -/
theorem proposition4_3_infiniteDimensional_idealGauge
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsUniformlyAcute U V) (W : H →L[ℂ] H)
    (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W)
    (hWmem : N.Mem ((1 - star W) * (1 - W))) :
    N.Mem ((1 - star (spectraDirectRotation U V hacute)) *
        (1 - spectraDirectRotation U V hacute)) ∧
      N.gauge ((1 - star (spectraDirectRotation U V hacute)) *
          (1 - spectraDirectRotation U V hacute)) ≤
        N.gauge ((1 - star W) * (1 - W)) :=
  N.majorization_mem_and_gauge_le hWmem
    (proposition4_3_infiniteDimensional U V hacute W hWunitary hWmap)

/-- Proposition 4.3 promoted from Ky Fan sums to every ideal gauge at the full
matched-crossed-defect scope inherited by Section 4. -/
theorem proposition4_3_infiniteDimensional_nonacute_idealGauge
    (N : DavisKahan.ExactSinTheta.FanDominantIdealFamily (𝕜 := ℂ))
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℂ]
      DavisKahan.halmosTargetDefect U V)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W)
    (hWmem : N.Mem ((1 - star W) * (1 - W))) :
    N.Mem ((1 - star (DavisKahan.nonacuteDirectRotation U V J)) *
        (1 - DavisKahan.nonacuteDirectRotation U V J)) ∧
      N.gauge ((1 - star (DavisKahan.nonacuteDirectRotation U V J)) *
          (1 - DavisKahan.nonacuteDirectRotation U V J)) ≤
        N.gauge ((1 - star W) * (1 - W)) :=
  N.majorization_mem_and_gauge_le hWmem
    (proposition4_3_infiniteDimensional_nonacute U V J W hWunitary hWmap)

/-- **Proposition 4.3 at the inherited compact, matched-defect source scope.**
The compactness hypothesis records the paper's Section 3 setting; the Ky Fan proof is valid
without it. -/
theorem proposition4_3_compact_nonacute_idealGauge
    (N : DavisKahan.ExactSinTheta.FanDominantIdealFamily (𝕜 := ℂ))
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (_hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℂ]
      DavisKahan.halmosTargetDefect U V)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W)
    (hWmem : N.Mem ((1 - star W) * (1 - W))) :
    N.Mem ((1 - star (DavisKahan.nonacuteDirectRotation U V J)) *
        (1 - DavisKahan.nonacuteDirectRotation U V J)) ∧
      N.gauge ((1 - star (DavisKahan.nonacuteDirectRotation U V J)) *
          (1 - DavisKahan.nonacuteDirectRotation U V J)) ≤
        N.gauge ((1 - star W) * (1 - W)) :=
  proposition4_3_infiniteDimensional_nonacute_idealGauge
    N U V J W hWunitary hWmap hWmem

end IdealGauge

/-! ## The two full-displacement consequences the source draws from Proposition 4.3

Immediately after Proposition 4.3 the source observes that whenever a norm of `1 − V` is the
square root of a unitarily invariant norm of `(1 − V⋆)(1 − V)`, the proposition also makes
`1 − V` itself minimal; and it names the operator norm and the Hilbert--Schmidt (square) norm
as two such norms.  It warns in the same breath that an *arbitrary* unitarily invariant norm
of `1 − V` need not be minimized by the direct rotation — that failure is Proposition 4.4,
which this repository refutes as printed and repairs in `QNorm.lean`.

These are conclusions the source draws, not conjectures it leaves open, so they are stated
here at the scope Section 4 actually inherits: an arbitrary complex Hilbert space with the
matched-crossed-defect completion of Theorem 3.1 and Corollary 3.1, and therefore **no**
acuteness hypothesis.  The acute and finite-dimensional forms are strictly weaker and do not
stand in for them.

Both come from the same identity, `aₙ(X⋆X) = aₙ(X)²`, read at the two ends of the Schatten
scale: at `p = ∞` it is the C⋆-identity `‖X⋆X‖ = ‖X‖²`, and at `p = 1` it is
`‖X⋆X‖₁ = ‖X‖_HS²`.  Both are `TauCeti.ApproximationNumber` results and neither mentions
Davis--Kahan. -/

section FullDisplacement

open DavisKahan (spectraDirectRotation)
open TauCeti.ApproximationNumber (gramOperator norm_gramOperator nuclearENorm_gramOperator)

universe v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The squared full displacement is the Gram operator of the full displacement.

`(1 − W⋆)(1 − W)` is how Proposition 4.3 spells it and `gramOperator (1 − W)` is how the
approximation-number layer spells it; this is the one-line bridge between them. -/
theorem displacementSquare_eq_gramOperator (W : H →L[ℂ] H) :
    (1 - star W) * (1 - W) = gramOperator (1 - W) := by
  rw [show (1 : H →L[ℂ] H) - star W = star (1 - W) by rw [star_sub, star_one]]
  rfl

/-- **Davis--Kahan 1970, the operator-norm consequence of Proposition 4.3**, at the
matched-crossed-defect scope Section 4 inherits.

`‖1 − U‖ ≤ ‖1 − W‖` for every unitary `W` carrying `U` onto `V`: the operator norm of the
*full* displacement, not only of its square, is minimized by the direct rotation.

The operator norm is the first Ky Fan gauge, so the single Ky Fan level `k = 1` of
Proposition 4.3 already carries this; the C⋆-identity `‖X⋆X‖ = ‖X‖²` then removes the
square.  No unitarily invariant norm beyond the operator norm is claimed, and by
Proposition 4.4 none is available in general. -/
theorem Proposition4_3_infiniteDimensional_nonacute_fullDisplacement_opNorm
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℂ]
      DavisKahan.halmosTargetDefect U V)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    ‖1 - DavisKahan.nonacuteDirectRotation U V J‖ ≤ ‖1 - W‖ := by
  have hk := proposition4_3_infiniteDimensional_nonacute U V J W hWunitary hWmap 1
  rw [displacementSquare_eq_gramOperator, displacementSquare_eq_gramOperator] at hk
  simp only [TauCeti.ApproximationNumber.kyFanApproximationGauge_eq_kyFanGauge,
    ContinuousLinearMap.kyFanGauge_one, norm_gramOperator] at hk
  exact le_of_sq_le_sq hk (norm_nonneg _)

/-- **Davis--Kahan 1970, the Hilbert--Schmidt consequence of Proposition 4.3**, at the
matched-crossed-defect scope Section 4 inherits.

`‖1 − U‖_HS ≤ ‖1 − W‖_HS`, the source's "square norm" half of the same observation.

Stated in `ℝ≥0∞`, so there is no Hilbert--Schmidt hypothesis on the competitor: when `1 − W`
fails to be Hilbert--Schmidt the right side is `∞` and the bound is vacuous, exactly as the
source's convention that a result is vacuous when its norms do not exist.

Where the operator norm needed one Ky Fan level, this needs all of them: the nuclear norm is
the supremum of the Ky Fan gauges, and `‖X⋆X‖₁ = ‖X‖_HS²`. -/
theorem Proposition4_3_infiniteDimensional_nonacute_fullDisplacement_hilbertSchmidt
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℂ]
      DavisKahan.halmosTargetDefect U V)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W) :
    (1 - DavisKahan.nonacuteDirectRotation U V J).hilbertSchmidtENorm ≤
      (1 - W).hilbertSchmidtENorm := by
  have hnuc : (gramOperator (1 - DavisKahan.nonacuteDirectRotation U V J)).nuclearENorm ≤
      (gramOperator (1 - W)).nuclearENorm := by
    rw [ContinuousLinearMap.nuclearENorm_eq_iSup_kyFanGauge,
      ContinuousLinearMap.nuclearENorm_eq_iSup_kyFanGauge]
    refine iSup_mono fun k => ENNReal.ofReal_le_ofReal ?_
    have hk := proposition4_3_infiniteDimensional_nonacute U V J W hWunitary hWmap k
    rw [displacementSquare_eq_gramOperator, displacementSquare_eq_gramOperator] at hk
    simpa only [TauCeti.ApproximationNumber.kyFanApproximationGauge_eq_kyFanGauge] using hk
  rw [nuclearENorm_gramOperator, nuclearENorm_gramOperator] at hnuc
  rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_natCast _ 2] at hnuc
  exact (ENNReal.rpow_le_rpow_iff (by norm_num)).mp hnuc

end FullDisplacement


/-! ## Proposition 4.4: source-facing names for the printed statement and its refutation

The printed statement, its refutation and the witnessing pair are declared in
`DavisKahan/FiniteDimensional/DirectRotation/ShortRotationCounterexample.lean`, their natural
home next to the `ℝ⁴` construction.  A census row registers all three, and a registered source
witness should be reachable under `TauCeti.DavisKahan1970`; these aliases give them that name.
Finding F6.4 of the 2026-09-04 hostile review. -/

/-- **Davis--Kahan 1970, Proposition 4.4 exactly as printed**, as a `Prop`: over every real
finite-dimensional space, every acute pair with first principal angle at most `π/3`, every
unitary carrying one subspace onto the other and every unitarily invariant seminorm, the direct
rotation minimizes the full displacement.  It is a definition rather than a theorem because it
is false. -/
alias proposition4Point4PrintedStatement :=
  DavisKahan.FiniteDimensional.DavisKahanProposition4Point4Finite

/-- **Proposition 4.4 is false as printed.**  The source-facing name for
`DavisKahan.FiniteDimensional.not_davisKahanProposition4_4_Finite`. -/
alias proposition4_4_refuted :=
  DavisKahan.FiniteDimensional.not_davisKahanProposition4_4_Finite

/-- **The `ℝ⁴` witness behind the refutation**: an acute pair with both principal angles `π/4`
and a unitary whose full displacement has strictly smaller trace norm than the direct
rotation's.  The source-facing name for
`DavisKahan.FiniteDimensional.shortRotation_fullDisplacement_refuted`. -/
alias proposition4_4_refutingPair :=
  DavisKahan.FiniteDimensional.shortRotation_fullDisplacement_refuted

end DavisKahan1970
end TauCeti
