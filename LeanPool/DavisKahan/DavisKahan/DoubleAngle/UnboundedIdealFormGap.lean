/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.UnboundedIdeal
import LeanPool.DavisKahan.DavisKahan.SinTheta.Unbounded.FormBoundedGap

/-! # Unbounded Ideal Form Gap -/

open TauCeti.DavisKahan.Sylvester

/-!
# The complex directed `sin 2Θ` theorem at the full source gap

`DavisKahan/DoubleAngle/UnboundedIdeal.lean` proves the complex directed
`sin 2Θ` estimate under the *spectrum gap*: the selected spectral restriction is
semibounded between two finite numbers `β ≤ α`, and the complementary
restriction's spectrum avoids `(β − δ, α + δ)`.  That is a bounded interval and
its exterior.  Davis and Kahan allow the separating interval to be half-infinite,
and the real track already covers all three configurations through
`FormBoundedSylvesterGap`.

This module closes that scope difference over `ℂ`, and it does so by adopting the
**real** track's proof architecture rather than by generalizing the complex
single-angle centre/radius engine.

## Why the architecture, and not the old engine

The spectrum-gap proof reaches its single-angle input through
`sinTheta_unbounded_gauge`, whose analytic core consumes the separating interval
as `TwoSidedShiftedInverseBound Λ₁ ((α+β)/2) ((α−β)/2 + δ)` — a centre and a
radius.  A half-infinite interval has neither, so that route cannot be widened
without replacing its analytic core.

It does not have to be.  `sinTheta_unbounded_complex` already proves the complex
single-angle theorem at the full `FormBoundedSylvesterGap`, through the direct
spectral Sylvester engine.  What was missing was only the packaging between it
and the reflection geometry: the block form of that estimate, its
bounded-perturbation adapter, and the reflected exact system.  All three are
supplied here, mirroring `DavisKahan/DoubleAngle/RealUnboundedIdeal.lean`.

The reflection geometry also gets simpler in the process.  The spectrum-gap proof
must conjugate the complementary restriction `Λ` by the reflection, because its
hypothesis is about `Λ`'s *spectrum* and the reflected system's complement lives
in `Uᗮ.map J_V`.  A `FormBoundedSylvesterGap` between `A₀` and `Λ` needs no such
transport: the reflection goes into the coordinate map `F₁ = J_V ∘ Uᶜ.subtypeL`
instead, exactly as in the real proof.

## Main results

* `TauCeti.DavisKahan.sinTheta_addBounded_gauge_complex_block_of_formGap`
* `TauCeti.DavisKahan.sinTwoTheta_reflectionResidual_block_gauge_of_formGap`
* `TauCeti.DavisKahan.sinTwoTheta_reflectionResidual_gauge_of_formGap`
* `TauCeti.DavisKahan.sinTwoTheta_addBounded_gauge_of_formGap`

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: the Section 2 `sin 2Θ` theorem and
  its Section 7 reflection proof, equations (7.1)--(7.5).
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan

open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta

noncomputable section

universe v

variable {H F G : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-! ## The complex bounded-perturbation `sin Θ` estimate at the full gap -/

/-- **Block form of the complex ideal-gauge bounded-perturbation sine-theta
estimate, at the full form-bounded Sylvester gap.**

The right-hand side is the single block of the perturbation between the two
coordinate spaces, before it is contracted back to the whole perturbation.  The
sharp directed residual `sin 2Theta_0` estimate needs it at this stage.

The complex mirror of `sinTheta_addBounded_gauge_real_block`, and the full-gap
counterpart of `sinTheta_addBounded_gauge_block_of_spectrum_gap`. -/
theorem sinTheta_addBounded_gauge_complex_block_of_formGap
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (V : H →L[ℂ] H) (hV : V.IsSymmetric)
    (A₀ : F →ₗ.[ℂ] F) (hA₀ : IsSelfAdjoint A₀)
    (Λ₁ : G →ₗ.[ℂ] G) (hΛ₁ : IsSelfAdjoint Λ₁)
    (X : F →L[ℂ] H) (F₁ : G →L[ℂ] H)
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
  exact sinTheta_unbounded_complex_block N D hD hA₀ hΛ₁ hF₁iso hδ hgap hResMem

/-! ## The complex directed `sin 2Θ` theorem at the full gap -/

section SinTwoTheta

variable (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
  (B : Set ℝ) (hB : MeasurableSet B)

/-- **Davis--Kahan 1970, the directed `sin 2Θ` theorem over a complex Hilbert
space, reflection-residual form, at the full form-bounded Sylvester gap.**

`A` is an unbounded self-adjoint closed operator, `U` is its genuine spectral
subspace for the measurable set `B`, `V` is an arbitrary closed subspace, and
`R` is a bounded self-adjoint operator implementing the mirrored system on the
whole domain of `A`.  Then the canonical reflected overlap block — the source's
`sin 2Θ₀` — lies in the ideal and satisfies `δ ‖sin 2Θ₀‖ ≤ ‖R‖`.

The gap is the scalar-generic form-bounded predicate, so all three of the
source's separation configurations are covered, the two half-infinite ones
included.  `sinTwoTheta_reflectionResidual_block_gauge_of_spectrum_gap` is the
same estimate under the bounded-interval hypotheses. -/
theorem sinTwoTheta_reflectionResidual_block_gauge_of_formGap
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (R : H →L[ℂ] H) (hR : R.IsSymmetric)
    (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (selfAdjointSpectralRestriction A hA B hB)
      (selfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hJdom : ∀ x : A.domain, V.reflectionOperator (x : H) ∈ A.domain)
    (hJintertwines : ∀ x : A.domain,
      (TauCeti.LinearPMap.addBounded A R)
          ⟨V.reflectionOperator (x : H), hJdom x⟩ =
        V.reflectionOperator (A x))
    (hRmem : N.Mem R) :
    N.Mem (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB) V) ∧
      δ * N.gauge (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB) V) ≤
        N.gauge ((selfAdjointSpectralSubspace A hA B hB).starProjection ∘L R ∘L
          ((selfAdjointSpectralSubspace A hA B hB)ᗮ.map
            (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection) := by
  set U := selfAdjointSpectralSubspace A hA B hB with hU
  set Uc := selfAdjointSpectralSubspace A hA Bᶜ hB.compl with hUc
  set A₀ := selfAdjointSpectralRestriction A hA B hB with hA₀def
  set Λ := selfAdjointSpectralRestriction A hA Bᶜ hB.compl with hΛdef
  set J : H →L[ℂ] H := V.reflectionOperator with hJ
  set X : U →L[ℂ] H := U.subtypeL with hX
  set F₁ : Uc →L[ℂ] H := J ∘L Uc.subtypeL with hF₁
  -- domain and intertwining data for the exact block
  have hXdom : ∀ x : A₀.domain, X (x : U) ∈ A.domain :=
    selfAdjointSpectralRestriction_inclusion_mem_domain A hA B hB
  have hXint : ∀ x : A₀.domain,
      A ⟨X (x : U), hXdom x⟩ = X (A₀ x) :=
    selfAdjointSpectralRestriction_inclusion_intertwines A hA B hB
  -- domain and intertwining data for the reflected complementary block
  have hUcdom : ∀ y : Λ.domain, ((y : Uc) : H) ∈ A.domain :=
    selfAdjointSpectralRestriction_inclusion_mem_domain A hA Bᶜ hB.compl
  have hF₁dom : ∀ y : Λ.domain, F₁ (y : Uc) ∈ A.domain := fun y =>
    hJdom ⟨((y : Uc) : H), hUcdom y⟩
  have hF₁int : ∀ y : Λ.domain,
      (TauCeti.LinearPMap.addBounded A R) ⟨F₁ (y : Uc), hF₁dom y⟩ =
        F₁ (Λ y) := by
    intro y
    have hAy : A ⟨((y : Uc) : H), hUcdom y⟩ = ((Λ y : Uc) : H) :=
      selfAdjointSpectralRestriction_inclusion_intertwines A hA Bᶜ hB.compl y
    calc
      (TauCeti.LinearPMap.addBounded A R) ⟨F₁ (y : Uc), hF₁dom y⟩
          = J (A ⟨((y : Uc) : H), hUcdom y⟩) :=
            hJintertwines ⟨((y : Uc) : H), hUcdom y⟩
      _ = J ((Λ y : Uc) : H) := congrArg J hAy
      _ = F₁ (Λ y) := rfl
  have hXiso : IsometricEmbedding X := fun _ => rfl
  have hF₁iso : IsometricEmbedding F₁ :=
    isometricEmbedding_reflection_comp V (fun _ => rfl)
  have hraw := sinTheta_addBounded_gauge_complex_block_of_formGap N A hA R hR
    A₀ (selfAdjointSpectralRestriction_isSelfAdjoint A hA B hB)
    Λ (selfAdjointSpectralRestriction_isSelfAdjoint A hA Bᶜ hB.compl)
    X F₁ hXdom hXint hF₁dom hF₁int hF₁iso hδ hgap hRmem
  -- the reflected complementary projection, read through the ambient reflection
  have hFproj : F₁ ∘L F₁.adjoint =
      (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection := by
    rw [starProjection_map_unitary Uᗮ V.reflection,
      ← starProjection_selfAdjointSpectralSubspace_compl A hA B hB]
    refine ContinuousLinearMap.ext fun x => ?_
    have hUcU : Uc.subtypeL ∘L Uc.subtypeL.adjoint = Uc.starProjection := by
      refine ContinuousLinearMap.ext fun z => ?_
      rw [Submodule.adjoint_subtypeL]
      rfl
    have hadj : F₁.adjoint = Uc.subtypeL.adjoint ∘L J := by
      rw [hF₁, ContinuousLinearMap.adjoint_comp, hJ, adjoint_reflectionOperator V]
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
    (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)) F₁ hF₁iso hFproj hraw.1
  -- contract the rectangular block to the ambient one
  have hF₁adjF₁ : F₁.adjoint ∘L F₁ = ContinuousLinearMap.id ℂ Uc := by
    have hUcadj : Uc.subtypeL.adjoint ∘L Uc.subtypeL = ContinuousLinearMap.id ℂ Uc := by
      ext v
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        Submodule.adjoint_subtypeL, Submodule.subtypeL_apply]
      exact congrArg (fun z : Uc => (z : H))
        (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self v)
    have hJJ : (J ∘L J : H →L[ℂ] H) = ContinuousLinearMap.id ℂ H :=
      Submodule.reflectionOperator_involutive V
    calc F₁.adjoint ∘L F₁
        = (Uc.subtypeL.adjoint ∘L J.adjoint) ∘L (J ∘L Uc.subtypeL) := by
          rw [hF₁, ContinuousLinearMap.adjoint_comp]
      _ = Uc.subtypeL.adjoint ∘L (J ∘L J) ∘L Uc.subtypeL := by
          rw [hJ, adjoint_reflectionOperator V]
          rfl
      _ = Uc.subtypeL.adjoint ∘L Uc.subtypeL := by
          rw [hJJ, ContinuousLinearMap.id_comp]
      _ = ContinuousLinearMap.id ℂ Uc := hUcadj
  have hPF : (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection ∘L F₁
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
        (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection) ∘L F₁ := by
    rw [ContinuousLinearMap.adjoint_comp, hRadj]
    calc X.adjoint ∘L R ∘L F₁
        = (X.adjoint ∘L U.starProjection) ∘L R ∘L
            ((Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection ∘L
              F₁) := by rw [hPX, hPF]
      _ = X.adjoint ∘L (U.starProjection ∘L R ∘L
            (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection) ∘L
            F₁ := rfl
  have hMid : N.Mem (U.starProjection ∘L R ∘L
      (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection) :=
    N.toSymmetricOperatorIdealFamily.comp_mem U.starProjection
      (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection hRmem
  have hcontract : N.gauge ((R ∘L X).adjoint ∘L F₁) ≤
      N.gauge (U.starProjection ∘L R ∘L
        (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection) := by
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
        (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection) := hcontract

/-- **Davis--Kahan 1970, the directed `sin 2Θ` theorem over a complex Hilbert
space, reflection-residual form, at the full form-bounded Sylvester gap.**  The
block form above with the block contracted back to the whole reflection
residual. -/
theorem sinTwoTheta_reflectionResidual_gauge_of_formGap
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (R : H →L[ℂ] H) (hR : R.IsSymmetric)
    (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (selfAdjointSpectralRestriction A hA B hB)
      (selfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hJdom : ∀ x : A.domain, V.reflectionOperator (x : H) ∈ A.domain)
    (hJintertwines : ∀ x : A.domain,
      (TauCeti.LinearPMap.addBounded A R)
          ⟨V.reflectionOperator (x : H), hJdom x⟩ =
        V.reflectionOperator (A x))
    (hRmem : N.Mem R) :
    N.Mem (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB) V) ∧
      δ * N.gauge (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB) V) ≤ N.gauge R := by
  obtain ⟨hmem, hle⟩ := sinTwoTheta_reflectionResidual_block_gauge_of_formGap
    A hA B hB N R hR V hδ hgap hJdom hJintertwines hRmem
  refine ⟨hmem, hle.trans ?_⟩
  exact N.toSymmetricOperatorIdealFamily.gaugeReal_comp_le_of_contractions
    (selfAdjointSpectralSubspace A hA B hB).starProjection
    ((selfAdjointSpectralSubspace A hA B hB)ᗮ.map
      (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection hRmem
    (Submodule.starProjection_norm_le _)
    (Submodule.starProjection_norm_le _)

end SinTwoTheta

section SinTwoThetaReducing

/-- A subspace admitting an orthogonal projection inside a complete ambient
space is itself complete. -/
local instance instCompleteSpaceCoeUnboundedIdealFormGapReducing
    (W : Submodule ℂ H) [W.HasOrthogonalProjection] : CompleteSpace W :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection W).completeSpace_coe

/-- **Davis--Kahan 1970, the directed `sin 2Θ` theorem over a complex Hilbert
space, reflection-residual block form, at an arbitrary reducing subspace.**

The same estimate as `sinTwoTheta_reflectionResidual_block_gauge_of_formGap`
with the spectral *selection* of the gap-carrying subspace removed: `U` is any
subspace reducing `A`, and the separation is the form-bounded Sylvester gap
between its two reducing restrictions.  `V` is the reflecting subspace and is not
assumed to reduce anything.  Section 1 of the source says in as many words that
neither projector is assumed spectral; what is assumed is that the decomposition
reduces the operator and that the two blocks are separated.

The proof is the spectral one.  Only three ingredients were spectral -- the
inclusion's domain membership, its intertwining, and the identification of the
complementary projector -- and each has a reducing analogue: the first two are
`LinearPMap.mem_reducingRestriction_domain_iff` and
`LinearPMap.coe_reducingRestriction_apply`, and the third is literal, because
the complement here *is* `Uᗮ`. -/
theorem sinTwoTheta_reflectionResidual_block_gauge_of_formGap_reducing
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {U : Submodule ℂ H} [U.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (R : H →L[ℂ] H) (hR : R.IsSymmetric)
    (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hred)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hred.orthogonal) δ)
    (hJdom : ∀ x : A.domain, V.reflectionOperator (x : H) ∈ A.domain)
    (hJintertwines : ∀ x : A.domain,
      (TauCeti.LinearPMap.addBounded A R)
          ⟨V.reflectionOperator (x : H), hJdom x⟩ =
        V.reflectionOperator (A x))
    (hRmem : N.Mem R) :
    N.Mem (sinTwoThetaIdealBlock U V) ∧
      δ * N.gauge (sinTwoThetaIdealBlock U V) ≤
        N.gauge (U.starProjection ∘L R ∘L
          (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection) := by
  set Uc := (Uᗮ : Submodule ℂ H) with hUc
  set A₀ := TauCeti.LinearPMap.reducingRestriction A U hred with hA₀def
  set Λ := TauCeti.LinearPMap.reducingRestriction A Uᗮ hred.orthogonal with hΛdef
  set J : H →L[ℂ] H := V.reflectionOperator with hJ
  set X : U →L[ℂ] H := U.subtypeL with hX
  set F₁ : Uc →L[ℂ] H := J ∘L Uc.subtypeL with hF₁
  -- domain and intertwining data for the exact block
  have hXdom : ∀ x : A₀.domain, X (x : U) ∈ A.domain := fun x =>
    (TauCeti.LinearPMap.mem_reducingRestriction_domain_iff A U hred _).mp x.2
  have hXint : ∀ x : A₀.domain,
      A ⟨X (x : U), hXdom x⟩ = X (A₀ x) := fun x =>
    (TauCeti.LinearPMap.coe_reducingRestriction_apply A U hred (x : U)
      (hXdom x)).symm
  -- domain and intertwining data for the reflected complementary block
  have hUcdom : ∀ y : Λ.domain, ((y : Uc) : H) ∈ A.domain := fun y =>
    (TauCeti.LinearPMap.mem_reducingRestriction_domain_iff A Uᗮ hred.orthogonal
      _).mp y.2
  have hF₁dom : ∀ y : Λ.domain, F₁ (y : Uc) ∈ A.domain := fun y =>
    hJdom ⟨((y : Uc) : H), hUcdom y⟩
  have hF₁int : ∀ y : Λ.domain,
      (TauCeti.LinearPMap.addBounded A R) ⟨F₁ (y : Uc), hF₁dom y⟩ =
        F₁ (Λ y) := by
    intro y
    have hAy : A ⟨((y : Uc) : H), hUcdom y⟩ = ((Λ y : Uc) : H) :=
      (TauCeti.LinearPMap.coe_reducingRestriction_apply A Uᗮ hred.orthogonal
        (y : Uc) (hUcdom y)).symm
    calc
      (TauCeti.LinearPMap.addBounded A R) ⟨F₁ (y : Uc), hF₁dom y⟩
          = J (A ⟨((y : Uc) : H), hUcdom y⟩) :=
            hJintertwines ⟨((y : Uc) : H), hUcdom y⟩
      _ = J ((Λ y : Uc) : H) := congrArg J hAy
      _ = F₁ (Λ y) := rfl
  have hXiso : IsometricEmbedding X := fun _ => rfl
  have hF₁iso : IsometricEmbedding F₁ :=
    isometricEmbedding_reflection_comp V (fun _ => rfl)
  have hraw := sinTheta_addBounded_gauge_complex_block_of_formGap N A hA R hR
    A₀ (TauCeti.LinearPMap.reducingRestriction_isSelfAdjoint A U hred
      hA.dense_domain hA)
    Λ (TauCeti.LinearPMap.reducingRestriction_isSelfAdjoint A Uᗮ hred.orthogonal
      hA.dense_domain hA)
    X F₁ hXdom hXint hF₁dom hF₁int hF₁iso hδ hgap hRmem
  -- the reflected complementary projection, read through the ambient reflection
  have hFproj : F₁ ∘L F₁.adjoint =
      (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection := by
    rw [starProjection_map_unitary Uᗮ V.reflection]
    refine ContinuousLinearMap.ext fun x => ?_
    have hUcU : Uc.subtypeL ∘L Uc.subtypeL.adjoint = Uc.starProjection := by
      refine ContinuousLinearMap.ext fun z => ?_
      rw [Submodule.adjoint_subtypeL]
      rfl
    have hadj : F₁.adjoint = Uc.subtypeL.adjoint ∘L J := by
      rw [hF₁, ContinuousLinearMap.adjoint_comp, hJ, adjoint_reflectionOperator V]
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
    (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)) F₁ hF₁iso hFproj hraw.1
  -- contract the rectangular block to the ambient one
  have hF₁adjF₁ : F₁.adjoint ∘L F₁ = ContinuousLinearMap.id ℂ Uc := by
    have hUcadj : Uc.subtypeL.adjoint ∘L Uc.subtypeL = ContinuousLinearMap.id ℂ Uc := by
      ext v
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        Submodule.adjoint_subtypeL, Submodule.subtypeL_apply]
      exact congrArg (fun z : Uc => (z : H))
        (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self v)
    have hJJ : (J ∘L J : H →L[ℂ] H) = ContinuousLinearMap.id ℂ H :=
      Submodule.reflectionOperator_involutive V
    calc F₁.adjoint ∘L F₁
        = (Uc.subtypeL.adjoint ∘L J.adjoint) ∘L (J ∘L Uc.subtypeL) := by
          rw [hF₁, ContinuousLinearMap.adjoint_comp]
      _ = Uc.subtypeL.adjoint ∘L (J ∘L J) ∘L Uc.subtypeL := by
          rw [hJ, adjoint_reflectionOperator V]
          rfl
      _ = Uc.subtypeL.adjoint ∘L Uc.subtypeL := by
          rw [hJJ, ContinuousLinearMap.id_comp]
      _ = ContinuousLinearMap.id ℂ Uc := hUcadj
  have hPF : (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection ∘L F₁
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
        (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection) ∘L F₁ := by
    rw [ContinuousLinearMap.adjoint_comp, hRadj]
    calc X.adjoint ∘L R ∘L F₁
        = (X.adjoint ∘L U.starProjection) ∘L R ∘L
            ((Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection ∘L
              F₁) := by rw [hPX, hPF]
      _ = X.adjoint ∘L (U.starProjection ∘L R ∘L
            (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection) ∘L
            F₁ := rfl
  have hMid : N.Mem (U.starProjection ∘L R ∘L
      (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection) :=
    N.toSymmetricOperatorIdealFamily.comp_mem U.starProjection
      (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection hRmem
  have hcontract : N.gauge ((R ∘L X).adjoint ∘L F₁) ≤
      N.gauge (U.starProjection ∘L R ∘L
        (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection) := by
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
        (Uᗮ.map (V.reflection.toLinearEquiv : H →ₗ[ℂ] H)).starProjection) := hcontract


end SinTwoThetaReducing

/-- **Davis--Kahan 1970, the directed `sin 2Θ` theorem over a complex Hilbert
space, bounded-perturbation form, at the full form-bounded Sylvester gap**:
`δ ‖sin 2Θ₀‖ ≤ 2 ‖E‖`, with the paper's sharp factor two.

The full-gap counterpart of `sinTwoTheta_addBounded_gauge_of_spectrum_gap`, and
the complex mirror of `sinTwoTheta_addBounded_gauge_real`. -/
theorem sinTwoTheta_addBounded_gauge_of_formGap
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (Eop : H →L[ℂ] H) (hEop : Eop.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (selfAdjointSpectralRestriction A hA B hB)
      (selfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hEmem : N.Mem Eop) :
    N.Mem (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ∧
      δ * N.gauge (sinTwoThetaIdealBlock
        (selfAdjointSpectralSubspace A hA B hB)
        (selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ≤
        2 * N.gauge Eop := by
  set V := selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
    (addBounded_isSelfAdjoint A hA Eop hEop) S hS with hVdef
  set D : H →L[ℂ] H := reflectionPerturbation V Eop with hDdef
  have hD : D.IsSymmetric := reflectionPerturbation_isSelfAdjoint V Eop hEop
  have hDideal := reflectionPerturbation_mem_and_gauge_le
    N.toSymmetricOperatorIdealFamily V Eop hEmem
  have hmain := sinTwoTheta_reflectionResidual_gauge_of_formGap A hA B hB N D hD V hδ hgap
    (perturbedSpectralReflection_mem_domain A hA Eop hEop S hS)
    (add_reflectionPerturbation_intertwines A hA Eop hEop S hS)
    hDideal.1
  exact ⟨hmain.1, hmain.2.trans hDideal.2⟩

end

end DavisKahan
end TauCeti
