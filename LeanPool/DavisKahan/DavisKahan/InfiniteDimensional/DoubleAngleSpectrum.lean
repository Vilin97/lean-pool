/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import LeanPool.DavisKahan.DavisKahan.Sylvester.Spectrum
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.CanonicalRealView
import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.OperatorAngleComplex
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.DoubleAngle

/-! # Double Angle Spectrum -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# The `sin 2Θ` theorem through the compression spectrum

The `sin 2Θ` scaffold in `DoubleAngle.lean` is stated over the blocked
operator-angle ladder.  This module proves the complex version by the
reflection argument instead: with
`J` the reflection through `V`, the conjugate `J A J` is self-adjoint, is
reduced by the reflected subspace `J U` with the *same* genuine compression
spectra (unitary conjugation transport), so the symmetric two-sided
genuine-spectrum `sin Θ` theorem applies to the pair `(A, J A J)` and gives
`d * subspaceGap U (J U) ≤ ‖J A J - A‖ ≤ 2 ‖B - A‖`.  The subspace gap to
the reflected image is exactly the operator norm of `sin 2Θ(U, V)`.

Supporting API, upstream candidates:

* `ContinuousLinearEquiv.conjContinuousAlgEquiv`: conjugation by a continuous linear
  equivalence as an algebra equivalence of endomorphism algebras;
* `conjByIsometryEquiv` and its transport laws for self-adjointness,
  reducing subspaces, orthogonal projections, compressions, and spectra.
-/

namespace TauCeti
namespace DavisKahanExt

open TauCeti.DavisKahan.ExactSinTheta


-- `reflectionDefect` and its lemmas live in `TauCeti.DavisKahan`
-- (`DavisKahan/BoundedOperator/Reflection.lean`); `DoubleAngle.lean` used to carry a verbatim
-- copy inside this namespace, so consumers resolved them without an `open`.
open DavisKahan

open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

section IsometryConjugation

/-- Conjugation of a bounded operator by a linear isometry equivalence. -/
noncomputable def conjByIsometryEquiv (W : E ≃ₗᵢ[ℂ] E) (A : E →L[ℂ] E) :
    E →L[ℂ] E :=
  W.toLinearIsometry.toContinuousLinearMap ∘L A ∘L
    W.symm.toLinearIsometry.toContinuousLinearMap

omit [CompleteSpace E] in
/-- Conjugation by a linear isometry equivalence acts pointwise as `W ∘ A ∘ W.symm`. -/
@[simp] theorem conjByIsometryEquiv_apply (W : E ≃ₗᵢ[ℂ] E) (A : E →L[ℂ] E)
    (x : E) : conjByIsometryEquiv W A x = W (A (W.symm x)) := rfl

/-- Conjugation preserves self-adjointness. -/
theorem isSelfAdjoint_conjByIsometryEquiv (W : E ≃ₗᵢ[ℂ] E)
    {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (conjByIsometryEquiv W A) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hA ⊢
  intro x y
  calc ⟪(conjByIsometryEquiv W A) x, y⟫_ℂ
      = ⟪W (A (W.symm x)), W (W.symm y)⟫_ℂ := by
        rw [W.apply_symm_apply]
        rfl
    _ = ⟪A (W.symm x), W.symm y⟫_ℂ := W.inner_map_map _ _
    _ = ⟪W.symm x, A (W.symm y)⟫_ℂ := hA _ _
    _ = ⟪W (W.symm x), W (A (W.symm y))⟫_ℂ := (W.inner_map_map _ _).symm
    _ = ⟪x, (conjByIsometryEquiv W A) y⟫_ℂ := by
        rw [W.apply_symm_apply]
        rfl

omit [CompleteSpace E] in
/-- Conjugation transports reducing subspaces to the image subspace. -/
theorem _root_.ContinuousLinearMap.Reduces.map_isometryEquiv {A : E →L[ℂ] E} {U : Submodule ℂ E}
    (hU : A.Reduces U) (W : E ≃ₗᵢ[ℂ] E) :
    ContinuousLinearMap.Reduces (conjByIsometryEquiv W A)
      (U.map (W.toLinearEquiv : E →ₗ[ℂ] E)) := by
  constructor
  · rintro x ⟨y, hy, rfl⟩
    refine ⟨A y, hU.1 y hy, ?_⟩
    have h : conjByIsometryEquiv W A (W y) = W (A y) := by
      change W (A (W.symm (W y))) = W (A y)
      rw [W.symm_apply_apply]
    exact h.symm
  · intro x hx
    rw [← Submodule.map_orthogonal_equiv] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [← Submodule.map_orthogonal_equiv]
    refine ⟨A y, hU.2 y hy, ?_⟩
    have h : conjByIsometryEquiv W A (W y) = W (A y) := by
      change W (A (W.symm (W y))) = W (A y)
      rw [W.symm_apply_apply]
    exact h.symm

/-- The isometric restriction of `W` from a subspace onto its image. -/
noncomputable def submoduleMapIsometry (W : E ≃ₗᵢ[ℂ] E) (U : Submodule ℂ E) :
    U ≃ₗᵢ[ℂ] (U.map (W.toLinearEquiv : E →ₗ[ℂ] E)) where
  toLinearEquiv := W.toLinearEquiv.submoduleMap U
  norm_map' x := by
    have h1 : ((W.toLinearEquiv.submoduleMap U x :
        U.map (W.toLinearEquiv : E →ₗ[ℂ] E)) : E) = W (x : E) := rfl
    rw [show ‖W.toLinearEquiv.submoduleMap U x‖ =
        ‖((W.toLinearEquiv.submoduleMap U x :
          U.map (W.toLinearEquiv : E →ₗ[ℂ] E)) : E)‖ from rfl, h1,
      W.norm_map]
    rfl

omit [CompleteSpace E] in
/-- The isometry onto the image submodule acts by `W` on underlying vectors. -/
@[simp] theorem submoduleMapIsometry_coe_apply (W : E ≃ₗᵢ[ℂ] E)
    (U : Submodule ℂ E) (x : U) :
    ((submoduleMapIsometry W U x : U.map (W.toLinearEquiv : E →ₗ[ℂ] E)) :
      E) = W (x : E) := rfl

omit [CompleteSpace E] in
/-- Its inverse acts by `W.symm` on underlying vectors. -/
@[simp] theorem submoduleMapIsometry_symm_coe_apply (W : E ≃ₗᵢ[ℂ] E)
    (U : Submodule ℂ E) (x : U.map (W.toLinearEquiv : E →ₗ[ℂ] E)) :
    (((submoduleMapIsometry W U).symm x : U) : E) = W.symm (x : E) := rfl

omit [CompleteSpace E] in
/-- Conjugation transports compressions along the restricted isometry. -/
theorem compressOperator_map (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (A : E →L[ℂ] E) (W : E ≃ₗᵢ[ℂ] E) :
    compressOperator (U.map (W.toLinearEquiv : E →ₗ[ℂ] E))
        (conjByIsometryEquiv W A) =
      (submoduleMapIsometry W U).toContinuousLinearEquiv.conjContinuousAlgEquiv.toAlgEquiv
        (compressOperator U A) := by
  ext x
  have hL : ((compressOperator (U.map (W.toLinearEquiv : E →ₗ[ℂ] E))
      (conjByIsometryEquiv W A) x :
        U.map (W.toLinearEquiv : E →ₗ[ℂ] E)) : E) =
      (U.map (W.toLinearEquiv : E →ₗ[ℂ] E)).starProjection
        ((conjByIsometryEquiv W A) (x : E)) := rfl
  have hR : (((submoduleMapIsometry W U).toContinuousLinearEquiv.conjContinuousAlgEquiv.toAlgEquiv
      (compressOperator U A) x :
        U.map (W.toLinearEquiv : E →ₗ[ℂ] E)) : E) =
      W (U.starProjection (A (W.symm (x : E)))) := rfl
  rw [hL, hR, Submodule.starProjection_map_apply]
  have hc : W.symm ((conjByIsometryEquiv W A) (x : E)) =
      A (W.symm (x : E)) := by
    change W.symm (W (A (W.symm (x : E)))) = A (W.symm (x : E))
    rw [W.symm_apply_apply]
  rw [hc]

end IsometryConjugation

section SpectrumTransport

omit [CompleteSpace E] in
/-- Spectra of compressions are invariant under equality of the subspace. -/
theorem spectrum_compressOperator_congr {S T : Submodule ℂ E}
    [S.HasOrthogonalProjection] [T.HasOrthogonalProjection] (h : S = T)
    (A : E →L[ℂ] E) :
    spectrum ℝ (compressOperator S A) = spectrum ℝ (compressOperator T A) := by
  subst h
  rfl

omit [CompleteSpace E] in
/-- **Spectrum transport for conjugated compressions.**  The real spectrum
of the compression of the conjugate to the image subspace equals the real
spectrum of the original compression. -/
theorem spectrum_compressOperator_map (U : Submodule ℂ E)
    [U.HasOrthogonalProjection] (A : E →L[ℂ] E) (W : E ≃ₗᵢ[ℂ] E) :
    spectrum ℝ (compressOperator (U.map (W.toLinearEquiv : E →ₗ[ℂ] E))
        (conjByIsometryEquiv W A)) =
      spectrum ℝ (compressOperator U A) := by
  rw [compressOperator_map]
  let e := (submoduleMapIsometry W U).toContinuousLinearEquiv.conjContinuousAlgEquiv
  exact AlgEquiv.spectrum_eq (e.toAlgEquiv.restrictScalars ℝ) _

end SpectrumTransport

section SinTwoTheta

variable {𝕜 : Type*}

omit [CompleteSpace E] in
/-- The repo reflection operator agrees with Mathlib's reflection isometry. -/
theorem reflectionOperator_eq_reflection (V : Submodule ℂ E)
    [V.HasOrthogonalProjection] (x : E) :
    (V.reflectionOperator : E →L[ℂ] E) x = V.reflection x := by
  simp [Submodule.reflectionOperator_apply, Submodule.reflection_apply, two_smul]

omit [CompleteSpace E] in
/-- Conjugation by the reflection through `V` differs from the identity by
the reflection defect. -/
theorem conjByReflection_sub_eq_reflectionDefect (V : Submodule ℂ E)
    [V.HasOrthogonalProjection] (A : E →L[ℂ] E) :
    conjByIsometryEquiv V.reflection A - A = reflectionDefect V A := by
  unfold reflectionDefect
  ext x
  change V.reflection (A (V.reflection.symm x)) - A x =
    V.reflectionOperator (A (V.reflectionOperator x)) - A x
  rw [reflectionOperator_eq_reflection, reflectionOperator_eq_reflection,
    Submodule.reflection_symm]

/-- **The reflection-defect core of the `sin 2Θ` theorem.**  For a
self-adjoint `A` with a genuine internal spectral configuration at the
reducing subspace `U` and *any* closed `V`,
`d * subspaceGap U (J_V U) ≤ ‖J_V A J_V - A‖`.  Both the reduced-comparison
and the residual forms of the `sin 2Θ` theorem factor through this
estimate. -/
theorem sinTwoTheta_spectrum_defect
    {A : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hUspec' : ∀ x ∈ spectrum ℝ (compressOperator Uᗮ A),
      x ≤ a - d ∨ b + d ≤ x) :
    d * U.projectionGap
        (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E)) ≤
      ‖reflectionDefect V A‖ := by
  have hÃsa : IsSelfAdjoint (conjByIsometryEquiv V.reflection A) :=
    isSelfAdjoint_conjByIsometryEquiv V.reflection hA
  have hUtildered : ContinuousLinearMap.Reduces (conjByIsometryEquiv V.reflection A)
      (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E)) :=
    hU.map_isometryEquiv V.reflection
  have htrans1 : spectrum ℝ (compressOperator
      (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E))
      (conjByIsometryEquiv V.reflection A)) =
      spectrum ℝ (compressOperator U A) :=
    spectrum_compressOperator_map U A V.reflection
  have hperp : Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E) =
      (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E))ᗮ :=
    Submodule.map_orthogonal_equiv U V.reflection
  have htrans2 : spectrum ℝ (compressOperator
      (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E))ᗮ
      (conjByIsometryEquiv V.reflection A)) =
      spectrum ℝ (compressOperator Uᗮ A) :=
    (spectrum_compressOperator_congr hperp.symm _).trans
      (spectrum_compressOperator_map Uᗮ A V.reflection)
  have h := sinTheta_spectrum_symmetric hA hÃsa hU hUtildered hd hab hab
    hUspec
    (by rw [htrans2]; exact hUspec')
    (by rw [htrans1]; exact hUspec)
    hUspec'
  have hdefect : conjByIsometryEquiv V.reflection A - A =
      reflectionDefect V A :=
    conjByReflection_sub_eq_reflectionDefect V A
  calc d * U.projectionGap
        (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E))
      ≤ ‖conjByIsometryEquiv V.reflection A - A‖ := h
    _ = ‖reflectionDefect V A‖ := by rw [hdefect]

/-- **The genuine-spectrum `sin 2Θ` theorem** (reflection form).  For a
self-adjoint `A` with a genuine internal spectral configuration at the
reducing subspace `U` — compression to `U` in `[a, b]`, compression to
`Uᗮ` outside `(a - d, b + d)` — and any `B` reduced by `V`,
`d * subspaceGap U (J_V U) ≤ 2 ‖B - A‖`, where `J_V U` is the image of `U`
under the reflection through `V`.  The gap to the reflected image is the
operator norm of `sin 2Θ(U, V)`. -/
theorem sinTwoTheta_spectrum
    {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hUspec' : ∀ x ∈ spectrum ℝ (compressOperator Uᗮ A),
      x ≤ a - d ∨ b + d ≤ x) :
    d * U.projectionGap
        (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E)) ≤
      2 * ‖B - A‖ := by
  calc d * U.projectionGap
        (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E))
      ≤ ‖reflectionDefect V A‖ :=
        sinTwoTheta_spectrum_defect hA hU hd hab hUspec hUspec'
    _ ≤ 2 * ‖A - B‖ := norm_reflectionDefect_le_two_mul A B V hV
    _ = 2 * ‖B - A‖ := by rw [norm_sub_rev]

/-- The `sin 2Θ` theorem phrased through the complex sine-angle operator:
`d * ‖sin Θ(U, J_V U)‖ ≤ 2 ‖B - A‖`, and `Θ(U, J_V U) = 2 Θ(U, V)` is the
double-angle content of the reflected pair. -/
theorem sinTwoTheta_spectrum_sinAngle
    {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hUspec' : ∀ x ∈ spectrum ℝ (compressOperator Uᗮ A),
      x ≤ a - d ∨ b + d ≤ x) :
    d * ‖sinAngleOperatorC U
        (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E))‖ ≤
      2 * ‖B - A‖ := by
  rw [norm_sinAngleOperatorC]
  exact sinTwoTheta_spectrum hA hU hV hd hab hUspec hUspec'

section IdealScope


/-- **The genuine-spectrum `sin 2Θ` theorem at unitary-invariant ideal
scope** (directed form).  Under the genuine internal configuration of `A`
at `U` and with `B - A` in the rectangular symmetric ideal family, the
directed cross block to the reflected image `J_V U` lies in the family with
`d · gauge (P_{(J_V U)ᗮ} P_U) ≤ 2 · gauge (B - A)`. -/
theorem sinTwoTheta_spectrum_gauge
    (N : TauCeti.SymmetricOperatorIdealFamily ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hUspec' : ∀ x ∈ spectrum ℝ (compressOperator Uᗮ A),
      x ≤ a - d ∨ b + d ≤ x)
    (hMem : N.Mem (B - A)) :
    N.Mem ((U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E))ᗮ.starProjection
        ∘L U.starProjection) ∧
      d * N.gaugeReal
        ((U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E))ᗮ.starProjection
          ∘L U.starProjection) ≤
      2 * N.gaugeReal (B - A) := by
  have hÃsa : IsSelfAdjoint (conjByIsometryEquiv V.reflection A) :=
    isSelfAdjoint_conjByIsometryEquiv V.reflection hA
  have hUtildered : ContinuousLinearMap.Reduces (conjByIsometryEquiv V.reflection A)
      (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E)) :=
    hU.map_isometryEquiv V.reflection
  have hperp : Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E) =
      (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E))ᗮ :=
    Submodule.map_orthogonal_equiv U V.reflection
  have htrans2 : spectrum ℝ (compressOperator
      (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E))ᗮ
      (conjByIsometryEquiv V.reflection A)) =
      spectrum ℝ (compressOperator Uᗮ A) :=
    (spectrum_compressOperator_congr hperp.symm _).trans
      (spectrum_compressOperator_map Uᗮ A V.reflection)
  -- the defect is in the ideal with gauge at most `2 · gauge (B - A)`
  have hMemAB : N.Mem (A - B) := by
    rw [show A - B = -(B - A) from by abel]
    exact N.neg_mem hMem
  have hdefect2 : conjByIsometryEquiv V.reflection A - A =
      V.reflectionOperator ∘L (A - B) ∘L V.reflectionOperator - (A - B) := by
    rw [conjByReflection_sub_eq_reflectionDefect,
      reflectionDefect_eq_perturbationDefect A B V hV]
  have hMemConj : N.Mem
      (V.reflectionOperator ∘L (A - B) ∘L V.reflectionOperator) :=
    N.comp_mem _ _ hMemAB
  have hMemD : N.Mem (conjByIsometryEquiv V.reflection A - A) := by
    rw [hdefect2]
    exact N.sub_mem hMemConj hMemAB
  have hgaugeAB : N.gaugeReal (A - B) = N.gaugeReal (B - A) := by
    rw [show A - B = -(B - A) from by abel]
    exact N.gaugeReal_neg hMem
  have hgaugeD : N.gaugeReal (conjByIsometryEquiv V.reflection A - A) ≤
      2 * N.gaugeReal (B - A) := by
    rw [hdefect2]
    have h1 : N.gaugeReal
        (V.reflectionOperator ∘L (A - B) ∘L V.reflectionOperator - (A - B))
        ≤ N.gaugeReal
            (V.reflectionOperator ∘L (A - B) ∘L V.reflectionOperator) +
          N.gaugeReal (A - B) := N.gaugeReal_sub_le hMemConj hMemAB
    have h2 : N.gaugeReal
        (V.reflectionOperator ∘L (A - B) ∘L V.reflectionOperator) ≤
        N.gaugeReal (A - B) :=
      N.gaugeReal_comp_le_of_contractions _ _ hMemAB
        (Submodule.norm_reflectionOperator_le_one V)
        (Submodule.norm_reflectionOperator_le_one V)
    rw [hgaugeAB] at h1 h2
    linarith
  have hmain := sinTheta_spectrum_gauge N hA hÃsa hU hUtildered hd hab
    hUspec (by rw [htrans2]; exact hUspec') hMemD
  exact ⟨hmain.1, hmain.2.trans hgaugeD⟩

end IdealScope

section ResidualSinTwoTheta

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **The residual `sin 2Θ` theorem** at genuine-spectrum scope.  Let `A`
be self-adjoint with a genuine internal spectral configuration at the
reducing subspace `U` — compression to `U` in `[a, b]`, compression to
`Uᗮ` outside `(a - d, b + d)` — and let the trial subspace `V` be the
(closed) range of an isometric embedding `X` with residual
`R = A X - X M` for an arbitrary comparison operator `M` on the trial
space.  Then `d * subspaceGap U (J_V U) ≤ 2 ‖R‖`: the gap to the
reflected image — the norm of `sin 2Θ(U, V)` — is controlled by the
residual alone, with no reduction hypothesis on the comparison pair. -/
theorem sinTwoTheta_spectrum_residual
    {A : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hUspec' : ∀ x ∈ spectrum ℝ (compressOperator Uᗮ A),
      x ≤ a - d ∨ b + d ≤ x)
    {X : F →L[ℂ] E} (hX : DavisKahan.IsometricEmbedding X)
    (hmem : ∀ u, X u ∈ V) (hsurj : ∀ v ∈ V, ∃ u, X u = v)
    (M : F →L[ℂ] F) :
    d * U.projectionGap
        (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E)) ≤
      2 * ‖A ∘L X - X ∘L M‖ := by
  have hcross := norm_cross_le_norm_residual hX A M hmem hsurj
  calc d * U.projectionGap
        (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E))
      ≤ ‖reflectionDefect V A‖ :=
        sinTwoTheta_spectrum_defect hA hU hd hab hUspec hUspec'
    _ ≤ 2 * ‖Vᗮ.starProjection ∘L A ∘L V.starProjection‖ :=
        norm_reflectionDefect_le_two_mul_norm_cross V hA
    _ ≤ 2 * ‖A ∘L X - X ∘L M‖ := by linarith

end ResidualSinTwoTheta

section SinTwoThetaIdentification

/-- The sum of the two off-diagonal blocks has exactly the norm of one
block: `≤` is the orthogonal-splitting estimate behind the sharp defect
bound, and `≥` holds because the sum restricts to the first block on
`V`. -/
theorem norm_offdiag_add_eq (V : Submodule ℂ E) [V.HasOrthogonalProjection]
    {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) :
    ‖Vᗮ.starProjection ∘L A ∘L V.starProjection +
        V.starProjection ∘L A ∘L Vᗮ.starProjection‖ =
      ‖Vᗮ.starProjection ∘L A ∘L V.starProjection‖ := by
  refine le_antisymm ?_ ?_
  · have h1 := norm_reflectionDefect_le_two_mul_norm_cross V hA
    have h2 : ‖reflectionDefect V A‖ =
        2 * ‖Vᗮ.starProjection ∘L A ∘L V.starProjection +
          V.starProjection ∘L A ∘L Vᗮ.starProjection‖ := by
      rw [reflectionDefect_eq_neg_two_smul_offdiag, norm_smul]
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
    have hfact : (Vᗮ.starProjection ∘L A ∘L V.starProjection +
        V.starProjection ∘L A ∘L Vᗮ.starProjection)
          (V.starProjection z) =
        (Vᗮ.starProjection ∘L A ∘L V.starProjection) z := by
      change Vᗮ.starProjection (A (V.starProjection (V.starProjection z))) +
          V.starProjection (A (Vᗮ.starProjection (V.starProjection z))) =
        Vᗮ.starProjection (A (V.starProjection z))
      rw [hVfix, hperp, map_zero, map_zero, add_zero]
    calc ‖(Vᗮ.starProjection ∘L A ∘L V.starProjection) z‖
        = ‖(Vᗮ.starProjection ∘L A ∘L V.starProjection +
            V.starProjection ∘L A ∘L Vᗮ.starProjection)
              (V.starProjection z)‖ := by rw [hfact]
      _ ≤ ‖Vᗮ.starProjection ∘L A ∘L V.starProjection +
            V.starProjection ∘L A ∘L Vᗮ.starProjection‖ *
            ‖V.starProjection z‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖Vᗮ.starProjection ∘L A ∘L V.starProjection +
            V.starProjection ∘L A ∘L Vᗮ.starProjection‖ * ‖z‖ :=
          mul_le_mul_of_nonneg_left (V.norm_starProjection_apply_le z)
            (norm_nonneg _)

omit [CompleteSpace E] in
/-- Conjugation by the reflection through `V` carries the projection onto
`U` to the projection onto the reflected image. -/
theorem starProjection_map_reflection (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E)).starProjection =
      conjByIsometryEquiv V.reflection U.starProjection := by
  ext x
  rw [Submodule.starProjection_map_apply]
  rfl

omit [CompleteSpace E] in
/-- The gap to the reflected image is the norm of the reflection defect
of the projection: `subspaceGap U (J_V U) = ‖J_V P_U J_V - P_U‖`. -/
theorem subspaceGap_map_reflection (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.projectionGap (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E)) =
      ‖reflectionDefect V U.starProjection‖ := by
  have h : U.starProjection -
      (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E)).starProjection =
      -(reflectionDefect V U.starProjection) := by
    rw [starProjection_map_reflection,
      ← conjByReflection_sub_eq_reflectionDefect]
    abel
  change ‖U.starProjection -
      (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E)).starProjection‖ = _
  rw [h, norm_neg]

/-- **The double-angle identification.**  The gap to the reflected image
is exactly the norm of the double-angle sine operator:
`subspaceGap U (J_V U) = ‖sin 2Θ(U, V)‖`.  Both sides equal
`2 ‖P_{Vᗮ} P_U P_V‖`: the left through the off-diagonal decomposition of
the reflection defect of `P_U`, the right through the C⋆-composition
norm identities. -/
theorem subspaceGap_map_reflection_eq_norm_sinTwoAngle
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.projectionGap (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E)) =
      ‖directedSinTwoAngleOperatorC U V‖ := by
  rw [subspaceGap_map_reflection,
    reflectionDefect_eq_neg_two_smul_offdiag, norm_smul,
    norm_offdiag_add_eq V (isSelfAdjoint_starProjection U),
    norm_directedSinTwoAngleOperatorC]
  norm_num

/-- **The genuine-spectrum `sin 2Θ` theorem, exact operator form.**
For self-adjoint `A` with the genuine internal spectral configuration at
the reducing subspace `U` and any `B` reduced by `V`,
`d * ‖sin 2Θ(U, V)‖ ≤ 2 ‖B - A‖` — the double-angle sine operator is the
functional-calculus `2 sin Θ cos Θ` of the pair `(U, V)`. -/
theorem sinTwoTheta_spectrum_operator
    {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hUspec' : ∀ x ∈ spectrum ℝ (compressOperator Uᗮ A),
      x ≤ a - d ∨ b + d ≤ x) :
    d * ‖directedSinTwoAngleOperatorC U V‖ ≤ 2 * ‖B - A‖ := by
  rw [← subspaceGap_map_reflection_eq_norm_sinTwoAngle]
  exact sinTwoTheta_spectrum hA hU hV hd hab hUspec hUspec'

/-- **The residual `sin 2Θ` theorem, exact operator form.**
`d * ‖sin 2Θ(U, V)‖ ≤ 2 ‖A X - X M‖` for the trial subspace
`V = range X` and an arbitrary comparison operator `M` on the trial
space. -/
theorem sinTwoTheta_spectrum_residual_operator
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {A : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hUspec' : ∀ x ∈ spectrum ℝ (compressOperator Uᗮ A),
      x ≤ a - d ∨ b + d ≤ x)
    {X : F →L[ℂ] E} (hX : DavisKahan.IsometricEmbedding X)
    (hmem : ∀ u, X u ∈ V) (hsurj : ∀ v ∈ V, ∃ u, X u = v)
    (M : F →L[ℂ] F) :
    d * ‖directedSinTwoAngleOperatorC U V‖ ≤ 2 * ‖A ∘L X - X ∘L M‖ := by
  rw [← subspaceGap_map_reflection_eq_norm_sinTwoAngle]
  exact sinTwoTheta_spectrum_residual hA hU hd hab hUspec hUspec'
    hX hmem hsurj M

end SinTwoThetaIdentification

end SinTwoTheta

end DavisKahanExt
end TauCeti
