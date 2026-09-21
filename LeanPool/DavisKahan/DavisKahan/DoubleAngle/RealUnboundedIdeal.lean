/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.UnboundedIdeal
import LeanPool.DavisKahan.DavisKahan.SinTheta.Real.Unbounded
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Real.SpectralRestriction

/-! # Real Unbounded Ideal -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# The directed `sin 2Θ` theorem over a **real** Hilbert space

Standing assumption 1 of Davis--Kahan 1970 is that the Hilbert space is "real or
complex".  The ambient (whole-space) half of the Section 2 `sin 2Θ` theorem,
`δ ‖sin 2Θ‖ ≤ 2‖H‖`, is available over the reals in
`Sources/DavisKahan1970/AmbientReal.lean`.  This module supplies the other
printed conclusion, the **directed** half `δ ‖sin 2Θ₀‖ ≤ 2‖R‖`, over a real
Hilbert space, for an unbounded self-adjoint closed operator and its genuine
spectral subspaces, and for every real Ky-Fan-dominant unitarily invariant ideal
family.

## Why this is proved natively and not transported

The complex directed endpoints
(`sinTwoTheta_reflectionResidual_gauge_of_spectrum_gap` and its perturbation
form) are stated for a `KyFanDominantIdealFamily (𝕜 := ℂ)`, a scalar-fixed
class with no gauge transport across complexification, and their spectral
hypotheses are phrased through `TauCeti.LinearPMap.spectrum`, which only exists
over `ℂ`.  Both obstructions disappear if the argument is run over the reals
directly: the reflection geometry, the rectangular ideal interface, and the
bounded-perturbation residual packaging are all scalar-generic, and the real
unbounded `sin Θ` theorem `sinTheta_unbounded_real` already carries the
Sylvester gap in the scalar-generic `FormBoundedSylvesterGap` form.

Accordingly the gap hypothesis here is `FormBoundedSylvesterGap` between the two
real spectral restrictions.  That predicate covers all three of the source's
separation configurations — the interval/exterior one over `realSpectrum`, and
both ordered half-line configurations as operator-form bounds — and it is the
weaker of this tree's two spellings of spectral separation
(`DavisKahan/Sylvester/Gap.lean`).  It is a *different* spelling from the
complex statements' `TauCeti.LinearPMap.SemiboundedBelow`/`TauCeti.LinearPMap.SemiboundedAbove` pair together with
resolvent-set avoidance, not a translation of it, because the latter cannot be
written over `ℝ` at all.

## Main results

* `TauCeti.DavisKahan.sinTheta_addBounded_gauge_real_isometric`
* `TauCeti.DavisKahan.sinTwoTheta_reflectionResidual_gauge_real`

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: standing assumption 1, the Section
  2 `sin 2Θ` theorem, and its Section 7 reflection proof, equations
  (7.1)--(7.5).
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan

open TauCeti.DavisKahanExt

open TauCeti.DavisKahan.ExactSinTheta


open TauCeti.DavisKahan
open TauCeti.DavisKahan.RealSpectralRestriction

noncomputable section

universe v

variable {E F G : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

/-! ## The real bounded-perturbation `sin Θ` estimate at ideal-gauge scope -/

/-- Real ideal-gauge counterpart of
`sinTheta_addBounded_gauge_of_spectrum_gap_isometric`.  If the bounded
perturbation belongs to a real Ky-Fan-dominant unitarily invariant ideal family,
then the isometric overlap block belongs to the same family with the sharp
constant-one gap estimate.

The gap is the scalar-generic form-bounded Sylvester predicate rather than the
`ℂ`-only resolvent-set separation, which is what makes the statement available
over `ℝ` at all. -/
theorem sinTheta_addBounded_gauge_real_isometric
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (V : E →L[ℝ] E) (hV : V.IsSymmetric)
    (A₀ : F →ₗ.[ℝ] F) (hA₀ : IsSelfAdjoint A₀)
    (Λ₁ : G →ₗ.[ℝ] G) (hΛ₁ : IsSelfAdjoint Λ₁)
    (X : F →L[ℝ] E) (F₁ : G →L[ℝ] E)
    (hXdom : ∀ x : A₀.domain, X (x : F) ∈ A.domain)
    (hXintertwines : ∀ x : A₀.domain,
      A ⟨X (x : F), hXdom x⟩ = X (A₀ x))
    (hF₁dom : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain)
    (hF₁intertwines : ∀ y : Λ₁.domain,
      (TauCeti.LinearPMap.addBounded A V) ⟨F₁ (y : G), hF₁dom y⟩ =
        F₁ (Λ₁ y))
    (hXiso : IsometricEmbedding X) (hF₁iso : IsometricEmbedding F₁)
    {δ : ℝ} (hδ : 0 < δ) (hgap : FormBoundedSylvesterGap A₀ Λ₁ δ)
    (hVmem : N.Mem V) :
    N.Mem (X.adjoint ∘L F₁) ∧
      δ * N.gauge (X.adjoint ∘L F₁) ≤ N.gauge V := by
  let D := boundedPerturbationSinThetaData A V A₀ Λ₁ X F₁
    hXdom hXintertwines hF₁dom hF₁intertwines
  have hD : _root_.IsSelfAdjoint D.A := by
    change _root_.IsSelfAdjoint (TauCeti.LinearPMap.addBounded A V)
    exact addBounded_isSelfAdjoint A hA V hV
  have hXnorm : ‖X‖ ≤ 1 := opNorm_le_one_of_isometry hXiso
  have hResMem : N.Mem D.residual := by
    change N.Mem (V ∘L X)
    exact N.toSymmetricOperatorIdealFamily.comp_right_mem X hVmem
  have hraw := sinTheta_unbounded_real N D hD hA₀ hΛ₁ hXiso hF₁iso hδ hgap hResMem
  have hResGauge : N.gauge D.residual ≤ N.gauge V := by
    change N.gauge (V ∘L X) ≤ N.gauge V
    exact N.toSymmetricOperatorIdealFamily.gaugeReal_comp_right_le X hVmem hXnorm
  exact ⟨hraw.1, hraw.2.trans hResGauge⟩

/-- **Block form of the real ideal-gauge bounded-perturbation sine-theta
estimate.**  The right-hand side is the single block of the perturbation between
the two coordinate spaces, before it is contracted back to the whole
perturbation.  The sharp directed residual `sin 2Theta_0` estimate needs it at
this stage. -/
theorem sinTheta_addBounded_gauge_real_block
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (V : E →L[ℝ] E) (hV : V.IsSymmetric)
    (A₀ : F →ₗ.[ℝ] F) (hA₀ : IsSelfAdjoint A₀)
    (Λ₁ : G →ₗ.[ℝ] G) (hΛ₁ : IsSelfAdjoint Λ₁)
    (X : F →L[ℝ] E) (F₁ : G →L[ℝ] E)
    (hXdom : ∀ x : A₀.domain, X (x : F) ∈ A.domain)
    (hXintertwines : ∀ x : A₀.domain,
      A ⟨X (x : F), hXdom x⟩ = X (A₀ x))
    (hF₁dom : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain)
    (hF₁intertwines : ∀ y : Λ₁.domain,
      (TauCeti.LinearPMap.addBounded A V) ⟨F₁ (y : G), hF₁dom y⟩ =
        F₁ (Λ₁ y))
    (hF₁iso : IsometricEmbedding F₁)
    {δ : ℝ} (hδ : 0 < δ) (hgap : FormBoundedSylvesterGap A₀ Λ₁ δ)
    (hVmem : N.Mem V) :
    N.Mem (X.adjoint ∘L F₁) ∧
      δ * N.gauge (X.adjoint ∘L F₁) ≤ N.gauge ((V ∘L X).adjoint ∘L F₁) := by
  let D := boundedPerturbationSinThetaData A V A₀ Λ₁ X F₁
    hXdom hXintertwines hF₁dom hF₁intertwines
  have hD : _root_.IsSelfAdjoint D.A := by
    change _root_.IsSelfAdjoint (TauCeti.LinearPMap.addBounded A V)
    exact addBounded_isSelfAdjoint A hA V hV
  have hResMem : N.Mem D.residual := by
    change N.Mem (V ∘L X)
    exact N.toSymmetricOperatorIdealFamily.comp_right_mem X hVmem
  exact sinTheta_unbounded_real_block N D hD hA₀ hΛ₁ hF₁iso hδ hgap hResMem

/-! ## The real directed `sin 2Θ` theorem -/

section SinTwoTheta

variable (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
  (S : Set ℝ) (hS : MeasurableSet S)

/-- The orthogonal projection onto the complementary real spectral range is the
projection onto the orthogonal complement of the selected one.  Stated at the
level of projections rather than of subspaces, because rewriting the subspace
under `starProjection` produces an ill-typed motive. -/
theorem starProjection_realSelfAdjointSpectralSubspace_compl :
    (realSelfAdjointSpectralSubspace A hA Sᶜ hS.compl).starProjection =
      (realSelfAdjointSpectralSubspace A hA S hS)ᗮ.starProjection := by
  rw [← realSelfAdjointSpectralProjection_eq_starProjection A hA Sᶜ hS.compl,
    realSelfAdjointSpectralProjection_compl A hA S hS,
    realSelfAdjointSpectralProjection_eq_starProjection A hA S hS,
    Submodule.starProjection_orthogonal]

/-- **Davis--Kahan 1970, the directed `sin 2Θ` theorem over a REAL Hilbert
space, reflection-residual form, at every real Ky-Fan-dominant unitarily
invariant ideal gauge.**

`A` is an unbounded self-adjoint closed operator on a real Hilbert space, `U` is
its genuine spectral subspace for the measurable set `S`, `V` is an arbitrary
closed subspace, and `R` is a bounded self-adjoint operator implementing the
mirrored system on the whole domain of `A`.  Then the canonical reflected
overlap block — the source's `sin 2Θ₀` — lies in the ideal and satisfies
`δ ‖sin 2Θ₀‖ ≤ ‖R‖`.

There is no dimension hypothesis and no compactness hypothesis; membership in
the ideal is *concluded*, exactly as in the complex statement. -/
theorem sinTwoTheta_reflectionResidual_block_gauge_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (R : E →L[ℝ] E) (hR : R.IsSymmetric)
    (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (realSelfAdjointSpectralRestriction A hA S hS)
      (realSelfAdjointSpectralRestriction A hA Sᶜ hS.compl) δ)
    (hJdom : ∀ x : A.domain, V.reflectionOperator (x : E) ∈ A.domain)
    (hJintertwines : ∀ x : A.domain,
      (TauCeti.LinearPMap.addBounded A R)
          ⟨V.reflectionOperator (x : E), hJdom x⟩ =
        V.reflectionOperator (A x))
    (hRmem : N.Mem R) :
    N.Mem (sinTwoThetaIdealBlock
        (realSelfAdjointSpectralSubspace A hA S hS) V) ∧
      δ * N.gauge (sinTwoThetaIdealBlock
        (realSelfAdjointSpectralSubspace A hA S hS) V) ≤
        N.gauge ((realSelfAdjointSpectralSubspace A hA S hS).starProjection ∘L R ∘L
          ((realSelfAdjointSpectralSubspace A hA S hS)ᗮ.map
            (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection) := by
  set U := realSelfAdjointSpectralSubspace A hA S hS with hU
  set Uc := realSelfAdjointSpectralSubspace A hA Sᶜ hS.compl with hUc
  set A₀ := realSelfAdjointSpectralRestriction A hA S hS with hA₀def
  set Λ := realSelfAdjointSpectralRestriction A hA Sᶜ hS.compl with hΛdef
  set J : E →L[ℝ] E := V.reflectionOperator with hJ
  set X : U →L[ℝ] E := U.subtypeL with hX
  set F₁ : Uc →L[ℝ] E := J ∘L Uc.subtypeL with hF₁
  -- domain and intertwining data for the exact block
  have hXdom : ∀ x : A₀.domain, X (x : U) ∈ A.domain :=
    realSelfAdjointSpectralRestriction_inclusion_mem_domain A hA S hS
  have hXint : ∀ x : A₀.domain,
      A ⟨X (x : U), hXdom x⟩ = X (A₀ x) :=
    realSelfAdjointSpectralRestriction_inclusion_intertwines A hA S hS
  -- domain and intertwining data for the reflected complementary block
  have hUcdom : ∀ y : Λ.domain, ((y : Uc) : E) ∈ A.domain :=
    realSelfAdjointSpectralRestriction_inclusion_mem_domain A hA Sᶜ hS.compl
  have hF₁dom : ∀ y : Λ.domain, F₁ (y : Uc) ∈ A.domain := fun y =>
    hJdom ⟨((y : Uc) : E), hUcdom y⟩
  have hF₁int : ∀ y : Λ.domain,
      (TauCeti.LinearPMap.addBounded A R) ⟨F₁ (y : Uc), hF₁dom y⟩ =
        F₁ (Λ y) := by
    intro y
    have hAy : A ⟨((y : Uc) : E), hUcdom y⟩ =
        ((Λ y : Uc) : E) := by
      exact realSelfAdjointSpectralRestriction_inclusion_intertwines
        A hA Sᶜ hS.compl y
    calc
      (TauCeti.LinearPMap.addBounded A R) ⟨F₁ (y : Uc), hF₁dom y⟩
          = J (A ⟨((y : Uc) : E), hUcdom y⟩) :=
            hJintertwines ⟨((y : Uc) : E), hUcdom y⟩
      _ = J ((Λ y : Uc) : E) := congrArg J hAy
      _ = F₁ (Λ y) := rfl
  have hXiso : IsometricEmbedding X := fun _ => rfl
  have hF₁iso : IsometricEmbedding F₁ :=
    isometricEmbedding_reflection_comp V (fun _ => rfl)
  have hraw := sinTheta_addBounded_gauge_real_block N A hA R hR
    A₀ (realSelfAdjointSpectralRestriction_isSelfAdjoint A hA S hS)
    Λ (realSelfAdjointSpectralRestriction_isSelfAdjoint A hA Sᶜ hS.compl)
    X F₁ hXdom hXint hF₁dom hF₁int hF₁iso hδ hgap hRmem
  -- the reflected complementary projection, read through the ambient reflection
  have hFproj : F₁ ∘L F₁.adjoint =
      (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection := by
    rw [starProjection_map_unitary Uᗮ V.reflection,
      ← starProjection_realSelfAdjointSpectralSubspace_compl A hA S hS]
    refine ContinuousLinearMap.ext fun x => ?_
    have hUcU : Uc.subtypeL ∘L Uc.subtypeL.adjoint = Uc.starProjection := by
      refine ContinuousLinearMap.ext fun z => ?_
      rw [Submodule.adjoint_subtypeL]
      rfl
    have hadj : F₁.adjoint = Uc.subtypeL.adjoint ∘L J := by
      rw [hF₁, ContinuousLinearMap.adjoint_comp, hJ,
        adjoint_reflectionOperator V]
    have hsymm : V.reflection.symm = V.reflection := V.reflection_symm
    change J (Uc.subtypeL (F₁.adjoint x)) = _
    rw [hadj]
    change J (Uc.subtypeL (Uc.subtypeL.adjoint (J x))) = _
    rw [show Uc.subtypeL (Uc.subtypeL.adjoint (J x)) =
        (Uc.subtypeL ∘L Uc.subtypeL.adjoint) (J x) from rfl, hUcU]
    change J (Uc.starProjection (J x)) =
      V.reflection (Uc.starProjection (V.reflection.symm x))
    rw [hsymm]
    rfl
  have hambient := projectionProduct_mem_and_gauge_le_isometric
    N.toSymmetricOperatorIdealFamily U
    (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)) F₁ hF₁iso hFproj hraw.1
  -- contract the rectangular block to the ambient one
  have hF₁adjF₁ : F₁.adjoint ∘L F₁ = ContinuousLinearMap.id ℝ Uc := by
    have hUcadj : Uc.subtypeL.adjoint ∘L Uc.subtypeL = ContinuousLinearMap.id ℝ Uc := by
      ext v
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        Submodule.adjoint_subtypeL, Submodule.subtypeL_apply]
      exact congrArg (fun z : Uc => (z : E))
        (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self v)
    have hJJ : (J ∘L J : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E :=
      Submodule.reflectionOperator_involutive V
    calc F₁.adjoint ∘L F₁
        = (Uc.subtypeL.adjoint ∘L J.adjoint) ∘L (J ∘L Uc.subtypeL) := by
          rw [hF₁, ContinuousLinearMap.adjoint_comp]
      _ = Uc.subtypeL.adjoint ∘L (J ∘L J) ∘L Uc.subtypeL := by
          rw [hJ, adjoint_reflectionOperator V]
          rfl
      _ = Uc.subtypeL.adjoint ∘L Uc.subtypeL := by
          rw [hJJ, ContinuousLinearMap.id_comp]
      _ = ContinuousLinearMap.id ℝ Uc := hUcadj
  have hPF : (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection ∘L F₁
      = F₁ := by
    rw [← hFproj, ContinuousLinearMap.comp_assoc, hF₁adjF₁,
      ContinuousLinearMap.comp_id]
  have hPX : X.adjoint ∘L U.starProjection = X.adjoint := by
    rw [hX]
    ext x
    rw [ContinuousLinearMap.comp_apply, Submodule.adjoint_subtypeL,
      Submodule.coe_orthogonalProjectionOnto_apply,
      Submodule.coe_orthogonalProjectionOnto_apply]
    exact Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x)
  have hRadj : R.adjoint = R :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hR
  have hfac : (R ∘L X).adjoint ∘L F₁ =
      X.adjoint ∘L (U.starProjection ∘L R ∘L
        (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection) ∘L F₁ := by
    rw [ContinuousLinearMap.adjoint_comp, hRadj]
    calc X.adjoint ∘L R ∘L F₁
        = (X.adjoint ∘L U.starProjection) ∘L R ∘L
            ((Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection ∘L
              F₁) := by rw [hPX, hPF]
      _ = X.adjoint ∘L (U.starProjection ∘L R ∘L
            (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection) ∘L
            F₁ := rfl
  have hMid : N.Mem (U.starProjection ∘L R ∘L
      (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection) :=
    N.toSymmetricOperatorIdealFamily.comp_mem U.starProjection
      (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection hRmem
  have hcontract : N.gauge ((R ∘L X).adjoint ∘L F₁) ≤
      N.gauge (U.starProjection ∘L R ∘L
        (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection) := by
    rw [hfac]
    have hXadjNorm : ‖X.adjoint‖ ≤ 1 := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact opNorm_le_one_of_isometry hXiso
    exact N.toSymmetricOperatorIdealFamily.gaugeReal_comp_le_of_contractions
      X.adjoint F₁ hMid hXadjNorm (opNorm_le_one_of_isometry hF₁iso)
  refine ⟨hambient.1, ?_⟩
  calc
    δ * N.gauge (sinTwoThetaIdealBlock U V) ≤ δ * N.gauge (X.adjoint ∘L F₁) :=
      mul_le_mul_of_nonneg_left hambient.2 hδ.le
    _ ≤ N.gauge ((R ∘L X).adjoint ∘L F₁) := hraw.2
    _ ≤ N.gauge (U.starProjection ∘L R ∘L
        (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection) := hcontract

/-- **Davis--Kahan 1970, the directed `sin 2Theta` theorem over a REAL Hilbert
space, reflection-residual form.**  The block form above with the block
contracted back to the whole reflection residual. -/
theorem sinTwoTheta_reflectionResidual_gauge_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (R : E →L[ℝ] E) (hR : R.IsSymmetric)
    (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (realSelfAdjointSpectralRestriction A hA S hS)
      (realSelfAdjointSpectralRestriction A hA Sᶜ hS.compl) δ)
    (hJdom : ∀ x : A.domain, V.reflectionOperator (x : E) ∈ A.domain)
    (hJintertwines : ∀ x : A.domain,
      (TauCeti.LinearPMap.addBounded A R)
          ⟨V.reflectionOperator (x : E), hJdom x⟩ =
        V.reflectionOperator (A x))
    (hRmem : N.Mem R) :
    N.Mem (sinTwoThetaIdealBlock
        (realSelfAdjointSpectralSubspace A hA S hS) V) ∧
      δ * N.gauge (sinTwoThetaIdealBlock
        (realSelfAdjointSpectralSubspace A hA S hS) V) ≤ N.gauge R := by
  obtain ⟨hmem, hle⟩ := sinTwoTheta_reflectionResidual_block_gauge_real
    A hA S hS N R hR V hδ hgap hJdom hJintertwines hRmem
  refine ⟨hmem, hle.trans ?_⟩
  exact N.toSymmetricOperatorIdealFamily.gaugeReal_comp_le_of_contractions
    (realSelfAdjointSpectralSubspace A hA S hS).starProjection
    ((realSelfAdjointSpectralSubspace A hA S hS)ᗮ.map
      (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection hRmem
    (Submodule.starProjection_norm_le _) (Submodule.starProjection_norm_le _)


section SinTwoThetaReducingReal

/-- A subspace admitting an orthogonal projection inside a complete ambient
space is itself complete. -/
local instance instCompleteSpaceCoeRealUnboundedIdealReducing
    (W : Submodule ℝ E) [W.HasOrthogonalProjection] : CompleteSpace W :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection W).completeSpace_coe

/-- **Davis--Kahan 1970, the directed `sin 2Θ` theorem over a real Hilbert
space, reflection-residual block form, at an arbitrary reducing subspace.**

The real mirror of
`sinTwoTheta_reflectionResidual_block_gauge_of_formGap_reducing`: the
gap-carrying subspace `U` need only reduce `A` and is not required to be
spectral, which is the source's own hypothesis.  `V` is the reflecting subspace
and reduces nothing. -/
theorem sinTwoTheta_reflectionResidual_block_gauge_reducing_real
    {A : E →ₗ.[ℝ] E} (hA : IsSelfAdjoint A)
    {U : Submodule ℝ E} [U.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (R : E →L[ℝ] E) (hR : R.IsSymmetric)
    (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hred)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hred.orthogonal) δ)
    (hJdom : ∀ x : A.domain, V.reflectionOperator (x : E) ∈ A.domain)
    (hJintertwines : ∀ x : A.domain,
      (TauCeti.LinearPMap.addBounded A R)
          ⟨V.reflectionOperator (x : E), hJdom x⟩ =
        V.reflectionOperator (A x))
    (hRmem : N.Mem R) :
    N.Mem (sinTwoThetaIdealBlock U V) ∧
      δ * N.gauge (sinTwoThetaIdealBlock U V) ≤
        N.gauge (U.starProjection ∘L R ∘L
          (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection) := by
  set Uc := (Uᗮ : Submodule ℝ E) with hUc
  set A₀ := TauCeti.LinearPMap.reducingRestriction A U hred with hA₀def
  set Λ := TauCeti.LinearPMap.reducingRestriction A Uᗮ hred.orthogonal with hΛdef
  set J : E →L[ℝ] E := V.reflectionOperator with hJ
  set X : U →L[ℝ] E := U.subtypeL with hX
  set F₁ : Uc →L[ℝ] E := J ∘L Uc.subtypeL with hF₁
  -- domain and intertwining data for the exact block
  have hXdom : ∀ x : A₀.domain, X (x : U) ∈ A.domain := fun x =>
    (TauCeti.LinearPMap.mem_reducingRestriction_domain_iff A U hred _).mp x.2
  have hXint : ∀ x : A₀.domain,
      A ⟨X (x : U), hXdom x⟩ = X (A₀ x) := fun x =>
    (TauCeti.LinearPMap.coe_reducingRestriction_apply A U hred (x : U)
      (hXdom x)).symm
  -- domain and intertwining data for the reflected complementary block
  have hUcdom : ∀ y : Λ.domain, ((y : Uc) : E) ∈ A.domain := fun y =>
    (TauCeti.LinearPMap.mem_reducingRestriction_domain_iff A Uᗮ hred.orthogonal
      _).mp y.2
  have hF₁dom : ∀ y : Λ.domain, F₁ (y : Uc) ∈ A.domain := fun y =>
    hJdom ⟨((y : Uc) : E), hUcdom y⟩
  have hF₁int : ∀ y : Λ.domain,
      (TauCeti.LinearPMap.addBounded A R) ⟨F₁ (y : Uc), hF₁dom y⟩ =
        F₁ (Λ y) := by
    intro y
    have hAy : A ⟨((y : Uc) : E), hUcdom y⟩ =
        ((Λ y : Uc) : E) :=
      (TauCeti.LinearPMap.coe_reducingRestriction_apply A Uᗮ hred.orthogonal
        (y : Uc) (hUcdom y)).symm
    calc
      (TauCeti.LinearPMap.addBounded A R) ⟨F₁ (y : Uc), hF₁dom y⟩
          = J (A ⟨((y : Uc) : E), hUcdom y⟩) :=
            hJintertwines ⟨((y : Uc) : E), hUcdom y⟩
      _ = J ((Λ y : Uc) : E) := congrArg J hAy
      _ = F₁ (Λ y) := rfl
  have hXiso : IsometricEmbedding X := fun _ => rfl
  have hF₁iso : IsometricEmbedding F₁ :=
    isometricEmbedding_reflection_comp V (fun _ => rfl)
  have hraw := sinTheta_addBounded_gauge_real_block N A hA R hR
    A₀ (TauCeti.LinearPMap.reducingRestriction_isSelfAdjoint A U hred
      hA.dense_domain hA)
    Λ (TauCeti.LinearPMap.reducingRestriction_isSelfAdjoint A Uᗮ hred.orthogonal
      hA.dense_domain hA)
    X F₁ hXdom hXint hF₁dom hF₁int hF₁iso hδ hgap hRmem
  -- the reflected complementary projection, read through the ambient reflection
  have hFproj : F₁ ∘L F₁.adjoint =
      (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection := by
    rw [starProjection_map_unitary Uᗮ V.reflection]
    refine ContinuousLinearMap.ext fun x => ?_
    have hUcU : Uc.subtypeL ∘L Uc.subtypeL.adjoint = Uc.starProjection := by
      refine ContinuousLinearMap.ext fun z => ?_
      rw [Submodule.adjoint_subtypeL]
      rfl
    have hadj : F₁.adjoint = Uc.subtypeL.adjoint ∘L J := by
      rw [hF₁, ContinuousLinearMap.adjoint_comp, hJ,
        adjoint_reflectionOperator V]
    have hsymm : V.reflection.symm = V.reflection := V.reflection_symm
    change J (Uc.subtypeL (F₁.adjoint x)) = _
    rw [hadj]
    change J (Uc.subtypeL (Uc.subtypeL.adjoint (J x))) = _
    rw [show Uc.subtypeL (Uc.subtypeL.adjoint (J x)) =
        (Uc.subtypeL ∘L Uc.subtypeL.adjoint) (J x) from rfl, hUcU]
    change J (Uc.starProjection (J x)) =
      V.reflection (Uc.starProjection (V.reflection.symm x))
    rw [hsymm]
    rfl
  have hambient := projectionProduct_mem_and_gauge_le_isometric
    N.toSymmetricOperatorIdealFamily U
    (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)) F₁ hF₁iso hFproj hraw.1
  -- contract the rectangular block to the ambient one
  have hF₁adjF₁ : F₁.adjoint ∘L F₁ = ContinuousLinearMap.id ℝ Uc := by
    have hUcadj : Uc.subtypeL.adjoint ∘L Uc.subtypeL = ContinuousLinearMap.id ℝ Uc := by
      ext v
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        Submodule.adjoint_subtypeL, Submodule.subtypeL_apply]
      exact congrArg (fun z : Uc => (z : E))
        (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self v)
    have hJJ : (J ∘L J : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E :=
      Submodule.reflectionOperator_involutive V
    calc F₁.adjoint ∘L F₁
        = (Uc.subtypeL.adjoint ∘L J.adjoint) ∘L (J ∘L Uc.subtypeL) := by
          rw [hF₁, ContinuousLinearMap.adjoint_comp]
      _ = Uc.subtypeL.adjoint ∘L (J ∘L J) ∘L Uc.subtypeL := by
          rw [hJ, adjoint_reflectionOperator V]
          rfl
      _ = Uc.subtypeL.adjoint ∘L Uc.subtypeL := by
          rw [hJJ, ContinuousLinearMap.id_comp]
      _ = ContinuousLinearMap.id ℝ Uc := hUcadj
  have hPF : (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection ∘L F₁
      = F₁ := by
    rw [← hFproj, ContinuousLinearMap.comp_assoc, hF₁adjF₁,
      ContinuousLinearMap.comp_id]
  have hPX : X.adjoint ∘L U.starProjection = X.adjoint := by
    rw [hX]
    ext x
    rw [ContinuousLinearMap.comp_apply, Submodule.adjoint_subtypeL,
      Submodule.coe_orthogonalProjectionOnto_apply,
      Submodule.coe_orthogonalProjectionOnto_apply]
    exact Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x)
  have hRadj : R.adjoint = R :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hR
  have hfac : (R ∘L X).adjoint ∘L F₁ =
      X.adjoint ∘L (U.starProjection ∘L R ∘L
        (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection) ∘L F₁ := by
    rw [ContinuousLinearMap.adjoint_comp, hRadj]
    calc X.adjoint ∘L R ∘L F₁
        = (X.adjoint ∘L U.starProjection) ∘L R ∘L
            ((Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection ∘L
              F₁) := by rw [hPX, hPF]
      _ = X.adjoint ∘L (U.starProjection ∘L R ∘L
            (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection) ∘L
            F₁ := rfl
  have hMid : N.Mem (U.starProjection ∘L R ∘L
      (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection) :=
    N.toSymmetricOperatorIdealFamily.comp_mem U.starProjection
      (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection hRmem
  have hcontract : N.gauge ((R ∘L X).adjoint ∘L F₁) ≤
      N.gauge (U.starProjection ∘L R ∘L
        (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection) := by
    rw [hfac]
    have hXadjNorm : ‖X.adjoint‖ ≤ 1 := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact opNorm_le_one_of_isometry hXiso
    exact N.toSymmetricOperatorIdealFamily.gaugeReal_comp_le_of_contractions
      X.adjoint F₁ hMid hXadjNorm (opNorm_le_one_of_isometry hF₁iso)
  refine ⟨hambient.1, ?_⟩
  calc
    δ * N.gauge (sinTwoThetaIdealBlock U V) ≤ δ * N.gauge (X.adjoint ∘L F₁) :=
      mul_le_mul_of_nonneg_left hambient.2 hδ.le
    _ ≤ N.gauge ((R ∘L X).adjoint ∘L F₁) := hraw.2
    _ ≤ N.gauge (U.starProjection ∘L R ∘L
        (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection) := hcontract

end SinTwoThetaReducingReal

end SinTwoTheta

/-! ## Real reflection through a genuine spectral range

The three lemmas below are the real-scalar counterparts of
`spectralReflection_mem_domain`, `selfAdjoint_apply_spectralReflection` and
`add_reflectionPerturbation_intertwines`.  They are what turns the
reflection-residual theorem above into the paper's bounded-perturbation
statement, and they are proved from the real spectral descent rather than from
the complex spectral measure. -/

section Perturbation

variable (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)

/-- Reflection through a genuine real spectral range preserves the full domain
of the self-adjoint operator. -/
theorem realSpectralReflection_mem_domain
    (S : Set ℝ) (hS : MeasurableSet S) (x : A.domain) :
    (realSelfAdjointSpectralSubspace A hA S hS).reflectionOperator (x : E) ∈
      A.domain := by
  have hP : (realSelfAdjointSpectralSubspace A hA S hS).starProjection (x : E)
      ∈ A.domain := by
    rw [← realSelfAdjointSpectralProjection_eq_starProjection A hA S hS]
    exact realSelfAdjointSpectralProjection_mem_domain A hA hS x
  rw [Submodule.reflectionOperator_apply]
  exact A.domain.sub_mem (A.domain.smul_mem (2 : ℝ) hP) x.property

/-- Reflection through a genuine real spectral range commutes with the
self-adjoint operator on its domain. -/
theorem realSelfAdjoint_apply_spectralReflection
    (S : Set ℝ) (hS : MeasurableSet S) (x : A.domain) :
    A
        ⟨(realSelfAdjointSpectralSubspace A hA S hS).reflectionOperator (x : E),
          realSpectralReflection_mem_domain A hA S hS x⟩ =
      (realSelfAdjointSpectralSubspace A hA S hS).reflectionOperator
        (A x) := by
  set U := realSelfAdjointSpectralSubspace A hA S hS with hUdef
  have hproj : realSelfAdjointSpectralProjection A hA S hS = U.starProjection :=
    realSelfAdjointSpectralProjection_eq_starProjection A hA S hS
  have hP : U.starProjection (x : E) ∈ A.domain := by
    rw [← hproj]
    exact realSelfAdjointSpectralProjection_mem_domain A hA hS x
  let px : A.domain := ⟨U.starProjection (x : E), hP⟩
  have hreflect :
      (⟨U.reflectionOperator (x : E),
        realSpectralReflection_mem_domain A hA S hS x⟩ : A.domain) =
        (2 : ℝ) • px - x :=
    Subtype.ext (Submodule.reflectionOperator_apply U (x : E))
  let qx : A.domain :=
    ⟨realSelfAdjointSpectralProjection A hA S hS (x : E),
      realSelfAdjointSpectralProjection_mem_domain A hA hS x⟩
  have hpx : px = qx := by
    apply Subtype.ext
    change U.starProjection (x : E) =
      realSelfAdjointSpectralProjection A hA S hS (x : E)
    rw [hproj]
  have hPcomm : A px = U.starProjection (A x) := by
    calc
      A px = A qx :=
        congrArg (fun y : A.domain => A y) hpx
      _ = realSelfAdjointSpectralProjection A hA S hS (A x) :=
        realSelfAdjoint_apply_spectralProjection A hA hS x
      _ = U.starProjection (A x) := by rw [hproj]
  rw [hreflect, LinearPMap.map_sub, LinearPMap.map_smul,
    Submodule.reflectionOperator_apply, hPcomm]

variable (Eop : E →L[ℝ] E) (hEop : Eop.IsSymmetric)

/-- For a perturbed real operator `A + E`, reflection through a spectral range
of the perturbed operator preserves the original domain, because the two
operators have the same domain. -/
theorem realPerturbedSpectralReflection_mem_domain
    (S : Set ℝ) (hS : MeasurableSet S) (x : A.domain) :
    (realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
      (addBounded_isSelfAdjoint A hA Eop hEop) S hS).reflectionOperator
        (x : E) ∈ A.domain := by
  let C := TauCeti.LinearPMap.addBounded A Eop
  let hC : IsSelfAdjoint C := addBounded_isSelfAdjoint A hA Eop hEop
  let xc : C.domain := ⟨(x : E), x.property⟩
  exact realSpectralReflection_mem_domain C hC S hS xc

/-- The exact unbounded real reflection-defect identity.  Reflecting `A`
through a spectral range of `A + E` is the same as adding the bounded operator
`E - J E J`. -/
theorem real_add_reflectionPerturbation_intertwines
    (S : Set ℝ) (hS : MeasurableSet S) (x : A.domain) :
    (TauCeti.LinearPMap.addBounded A (reflectionPerturbation
        (realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (addBounded_isSelfAdjoint A hA Eop hEop) S hS) Eop))
        ⟨(realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
            (addBounded_isSelfAdjoint A hA Eop hEop) S hS).reflectionOperator
              (x : E),
          realPerturbedSpectralReflection_mem_domain A hA Eop hEop S hS x⟩ =
      (realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
        (addBounded_isSelfAdjoint A hA Eop hEop) S hS).reflectionOperator
          (A x) := by
  set C := TauCeti.LinearPMap.addBounded A Eop with hCdef
  set hC : IsSelfAdjoint C := addBounded_isSelfAdjoint A hA Eop hEop with hCsa
  set V := realSelfAdjointSpectralSubspace C hC S hS with hVdef
  set J : E →L[ℝ] E := V.reflectionOperator with hJdef
  set D : E →L[ℝ] E := reflectionPerturbation V Eop with hDdef
  have hJdomA : J (x : E) ∈ A.domain :=
    realPerturbedSpectralReflection_mem_domain A hA Eop hEop S hS x
  let xc : C.domain := ⟨(x : E), x.property⟩
  have hcommC := realSelfAdjoint_apply_spectralReflection C hC S hS xc
  have hcomm :
      A ⟨J (x : E), hJdomA⟩ + Eop (J (x : E)) =
        J (A x + Eop (x : E)) := by
    calc
      A ⟨J (x : E), hJdomA⟩ + Eop (J (x : E)) =
          C
            ⟨J (x : E), realSpectralReflection_mem_domain C hC S hS xc⟩ := rfl
      _ = J (C xc) := hcommC
      _ = J (A x + Eop (x : E)) := rfl
  have hJJ : J (J (x : E)) = (x : E) := V.reflection_reflection (x : E)
  have hreflection (y : E) : V.reflection y = J y := rfl
  have hDapply : D (J (x : E)) = Eop (J (x : E)) - J (Eop (x : E)) := by
    calc
      D (J (x : E)) =
          Eop (J (x : E)) -
            V.reflection (Eop (V.reflection.symm (J (x : E)))) := rfl
      _ = Eop (J (x : E)) - V.reflection (Eop (V.reflection (J (x : E)))) := by
        rw [Submodule.reflection_symm]
      _ = Eop (J (x : E)) - V.reflection (Eop (J (J (x : E)))) := by
        rw [hreflection (J (x : E))]
      _ = Eop (J (x : E)) - J (Eop (J (J (x : E)))) := by
        rw [hreflection (Eop (J (J (x : E))))]
      _ = Eop (J (x : E)) - J (Eop (x : E)) := by rw [hJJ]
  calc
    (TauCeti.LinearPMap.addBounded A D)
        ⟨J (x : E), realPerturbedSpectralReflection_mem_domain
          A hA Eop hEop S hS x⟩ =
      A ⟨J (x : E), hJdomA⟩ + D (J (x : E)) := rfl
    _ = A ⟨J (x : E), hJdomA⟩ +
        (Eop (J (x : E)) - J (Eop (x : E))) := by rw [hDapply]
    _ = (A ⟨J (x : E), hJdomA⟩ + Eop (J (x : E))) -
        J (Eop (x : E)) := by abel
    _ = J (A x + Eop (x : E)) - J (Eop (x : E)) := by rw [hcomm]
    _ = (J (A x) + J (Eop (x : E))) - J (Eop (x : E)) := by
      rw [map_add]
    _ = J (A x) := add_sub_cancel_right _ _

/-- **Davis--Kahan 1970, the directed `sin 2Θ` theorem over a REAL Hilbert
space, bounded-perturbation form, at every real Ky-Fan-dominant unitarily
invariant ideal gauge**: `δ ‖sin 2Θ₀‖ ≤ 2 ‖E‖`, with the paper's sharp factor
two.

`A` is an unbounded self-adjoint closed operator on a real Hilbert space, `E` a
bounded self-adjoint perturbation, and the two subspaces are genuine real
spectral subspaces of `A` and of `A + E` for prescribed measurable spectral
sets.  There is no dimension hypothesis and no compactness hypothesis;
membership in the ideal is *concluded*. -/
theorem sinTwoTheta_addBounded_gauge_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (S T : Set ℝ) (hS : MeasurableSet S) (hT : MeasurableSet T)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (realSelfAdjointSpectralRestriction A hA S hS)
      (realSelfAdjointSpectralRestriction A hA Sᶜ hS.compl) δ)
    (hEmem : N.Mem Eop) :
    N.Mem (sinTwoThetaIdealBlock
        (realSelfAdjointSpectralSubspace A hA S hS)
        (realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (addBounded_isSelfAdjoint A hA Eop hEop) T hT)) ∧
      δ * N.gauge (sinTwoThetaIdealBlock
        (realSelfAdjointSpectralSubspace A hA S hS)
        (realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (addBounded_isSelfAdjoint A hA Eop hEop) T hT)) ≤
        2 * N.gauge Eop := by
  set V := realSelfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
    (addBounded_isSelfAdjoint A hA Eop hEop) T hT with hVdef
  set D : E →L[ℝ] E := reflectionPerturbation V Eop with hDdef
  have hD : D.IsSymmetric := reflectionPerturbation_isSelfAdjoint V Eop hEop
  have hDideal := reflectionPerturbation_mem_and_gauge_le
    N.toSymmetricOperatorIdealFamily V Eop hEmem
  have hmain := sinTwoTheta_reflectionResidual_gauge_real A hA S hS N D hD V hδ hgap
    (realPerturbedSpectralReflection_mem_domain A hA Eop hEop T hT)
    (real_add_reflectionPerturbation_intertwines A hA Eop hEop T hT)
    hDideal.1
  exact ⟨hmain.1, hmain.2.trans hDideal.2⟩

end Perturbation

end

end DavisKahan
end TauCeti
