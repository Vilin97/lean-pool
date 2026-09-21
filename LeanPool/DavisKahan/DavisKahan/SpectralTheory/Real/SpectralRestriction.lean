/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.PartialMap.Complexification
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Complexification.FunctionalCalculus
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Complexification.Subspace
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.ReducingSubspace.Restriction
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.SpectralRestrictionOperator

/-! # Spectral Restriction -/

open TauCeti.DavisKahan.Sylvester

/-!
# Real spectral projections and restrictions by complexification

For a self-adjoint closed operator on a real Hilbert space, this module obtains
its measurable spectral projections from the canonical spectral measure of the
complexified operator.  The key point is that the complexified operator is
real with respect to the canonical conjugation.  Resolvent uniqueness implies
that its spectral measure is fixed by conjugation, so every spectral projection
descends to a bounded real orthogonal projection.

The closed operator on a selected real spectral range is then constructed by
the scalar-generic reducing-restriction API.  Thus the spectral bridge owns
only the genuinely spectral descent; domain density, graph closedness,
self-adjointness, and inclusion intertwining are supplied by the generic core.
-/

open scoped InnerProductSpace ComplexConjugate

namespace TauCeti
namespace DavisKahan
namespace RealSpectralRestriction


open ExactSinTheta
open ExactSinTheta.PartialMapComplexification
open TauCeti.RealComplexification
-- the namespace is split across the two libraries: `Basic` is in `ForTauCeti`, `Subspace` here
open TauCeti.DavisKahan.Foundation.RealComplexification

noncomputable section

universe v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Local notation keeps the ambient real space syntactically visible at every
use site; an abbreviation here would turn `E` into an uninferable implicit
argument in several PVM declarations. -/
local notation "Eℂ" => RealComplexification E
/-- Conjugate a projection-valued measure by the canonical real-structure
conjugation. -/
noncomputable def conjugatePVM (P : TauCeti.ProjValMeasure Eℂ) :
    TauCeti.ProjValMeasure Eℂ where
  proj B hB := conjugateOperator (P.proj B hB)
  diag z := P.diag (conjugation z)
  diag_finite z := P.diag_finite (conjugation z)
  inner_proj B hB z := by
    rw [conjugateOperator_apply, inner_conjugation_right]
    calc
      ⟪P.proj B hB (conjugation z), conjugation z⟫_ℂ =
          starRingEnd ℂ
            ⟪conjugation z, P.proj B hB (conjugation z)⟫_ℂ := by
        rw [inner_conj_symm]
      _ = (((P.diag (conjugation z)) B).toReal : ℂ) := by
        rw [P.inner_proj, Complex.conj_ofReal]
  proj_univ := by
    rw [P.proj_univ]
    exact conjugateOperator_one
  proj_inter B₁ B₂ hB₁ hB₂ := by
    rw [← conjugateOperator_mul, P.proj_inter]

/-- Conjugating a PVM conjugates each of its projections. -/
@[simp]
theorem conjugatePVM_proj (P : TauCeti.ProjValMeasure Eℂ)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (conjugatePVM P).proj B hB = conjugateOperator (P.proj B hB) :=
  rfl

/-- Conjugating a PVM conjugates each of its diagonal measures. -/
@[simp]
theorem conjugatePVM_diag (P : TauCeti.ProjValMeasure Eℂ) (z : Eℂ) :
    (conjugatePVM P).diag z = P.diag (conjugation z) :=
  rfl

/-- Conjugation preserves the coordinatewise complexified operator domain. -/
def conjugationDomain (A : E →ₗ.[ℝ] E)
    (z : (PartialMapComplexification.complexify A).domain) :
    (PartialMapComplexification.complexify A).domain :=
  ⟨conjugation (z : Eℂ), by
    rw [PartialMapComplexification.mem_complexify_domain_iff]
    simpa using
      (PartialMapComplexification.mem_complexify_domain_iff A z).mp z.property⟩

omit [CompleteSpace E] in
/-- The conjugation domain, unfolded to the underlying vector. -/
@[simp]
theorem conjugationDomain_coe (A : E →ₗ.[ℝ] E)
    (z : (PartialMapComplexification.complexify A).domain) :
    ((conjugationDomain A z :
      (PartialMapComplexification.complexify A).domain) : Eℂ) =
      conjugation (z : Eℂ) :=
  rfl

omit [CompleteSpace E] in
/-- The complexified closed operator commutes with canonical conjugation on its
operator domain. -/
theorem complexify_apply_conjugationDomain (A : E →ₗ.[ℝ] E)
    (z : (PartialMapComplexification.complexify A).domain) :
    (PartialMapComplexification.complexify A)
        (conjugationDomain A z) =
      conjugation
        ((PartialMapComplexification.complexify A) z) := by
  refine RealComplexification.ext ?_ ?_
  · rw [PartialMapComplexification.complexify_apply_re,
      RealComplexification.re_conj,
      PartialMapComplexification.complexify_apply_re]
    exact PartialMapComplexification.toLinearMap_congr rfl
  · rw [PartialMapComplexification.complexify_apply_im,
      RealComplexification.im_conj,
      PartialMapComplexification.complexify_apply_im]
    refine (PartialMapComplexification.toLinearMap_congr ?_).trans (map_neg _ _)
    simp [conjugationDomain]

/-- Resolvents of a complexified real self-adjoint operator, in the native
`TauCeti` sense, are exchanged by canonical conjugation and conjugation of the
spectral parameter. -/
theorem conjugateOperator_tauCetiResolvent
    (A : E →ₗ.[ℝ] E) (_hA : IsSelfAdjoint A)
    {z : ℂ} (_hz : z.im ≠ 0)
    (hzr : z ∈ TauCeti.LinearPMap.resolventSet
      (PartialMapComplexification.complexify A))
    (hzbr : (starRingEnd ℂ) z ∈ TauCeti.LinearPMap.resolventSet
      (PartialMapComplexification.complexify A)) :
    conjugateOperator (TauCeti.LinearPMap.resolvent
        (PartialMapComplexification.complexify A) z)
      = TauCeti.LinearPMap.resolvent
          (PartialMapComplexification.complexify A) ((starRingEnd ℂ) z) := by
  apply ContinuousLinearMap.ext
  intro ξ
  set Aℂ := (PartialMapComplexification.complexify A) with hAc
  set r : Eℂ := TauCeti.LinearPMap.resolvent Aℂ z (conjugation ξ) with hr
  have hrdom : r ∈ Aℂ.domain :=
    TauCeti.LinearPMap.resolvent_mem_domain hzr (conjugation ξ)
  have hsolve : z • r - Aℂ ⟨r, hrdom⟩ = conjugation ξ :=
    TauCeti.LinearPMap.smul_sub_apply_resolvent hzr (conjugation ξ)
  set jr : Aℂ.domain := conjugationDomain A ⟨r, hrdom⟩ with hjr
  have happ : Aℂ jr = conjugation (Aℂ ⟨r, hrdom⟩) :=
    complexify_apply_conjugationDomain A ⟨r, hrdom⟩
  have hjsolve : (starRingEnd ℂ) z • (jr : Eℂ) - Aℂ jr = ξ := by
    have h1 : (starRingEnd ℂ) z • (jr : Eℂ) - Aℂ jr
        = conjugation (z • r - Aℂ ⟨r, hrdom⟩) := by
      rw [map_sub, conjugation_complex_smul, ← happ]
      rfl
    rw [h1, hsolve, conjugation_involutive]
  have hleft := TauCeti.LinearPMap.resolvent_smul_sub_apply hzbr jr
  rw [hjsolve] at hleft
  change conjugation (TauCeti.LinearPMap.resolvent Aℂ z (conjugation ξ)) = _
  exact hleft.symm

/-- The Cayley transform of a complexified real self-adjoint operator is sent to
its adjoint by canonical conjugation. -/
theorem conjugateOperator_cayley (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A) :
    conjugateOperator (TauCeti.LinearPMap.cayley
        (PartialMapComplexification.isSelfAdjoint_complexify hA))
      = star (TauCeti.LinearPMap.cayley
          (PartialMapComplexification.isSelfAdjoint_complexify hA)) := by
  set hAℂ := PartialMapComplexification.isSelfAdjoint_complexify hA with hhAc
  have hni := TauCeti.LinearPMap.negI_mem_resolventSet hAℂ
  have hi := TauCeti.LinearPMap.I_mem_resolventSet hAℂ
  have hconjI : ((starRingEnd ℂ) (-Complex.I)) ∈ TauCeti.LinearPMap.resolventSet
      (PartialMapComplexification.complexify A) := by simpa using hi
  have hkey : conjugateOperator
      (TauCeti.LinearPMap.resolvent
        (PartialMapComplexification.complexify A) (-Complex.I))
      = ContinuousLinearMap.adjoint
        (TauCeti.LinearPMap.resolvent
          (PartialMapComplexification.complexify A) (-Complex.I)) := by
    rw [conjugateOperator_tauCetiResolvent A hA (by simp) hni hconjI,
      TauCeti.LinearPMap.adjoint_resolvent hAℂ hni hconjI]
  simp only [TauCeti.LinearPMap.cayley, conjugateOperator_add, conjugateOperator_one,
    conjugateOperator_complex_smul, hkey, star_add, star_one, star_smul,
    ContinuousLinearMap.star_eq_adjoint]
  rfl

/-- **Canonical conjugation conjugates the symbol.**  If a normal operator on a
complexification satisfies `J U J = U⋆`, then `J Φ(f) J = Φ(f⋆)` for its
continuous functional calculus.  The map `f ↦ J Φ(f⋆) J` is a continuous unital
`⋆`-algebra homomorphism — conjugate-linear twice is linear — sending the
coordinate function to `J U⋆ J = U`, so uniqueness of the continuous functional
calculus identifies it with `Φ`. -/
theorem conjugateOperator_cfcHom {U : Eℂ →L[ℂ] Eℂ} (hU : IsStarNormal U)
    (hUc : conjugateOperator U = star U) (f : C(spectrum ℂ U, ℂ)) :
    conjugateOperator (cfcHom hU f) = cfcHom hU (star f) := by
  let Ψ : C(spectrum ℂ U, ℂ) →⋆ₐ[ℂ] (Eℂ →L[ℂ] Eℂ) :=
    { toFun := fun g => conjugateOperator (cfcHom hU (star g))
      map_one' := by rw [star_one, map_one, conjugateOperator_one]
      map_mul' := fun g h => by
        rw [star_mul', map_mul, conjugateOperator_mul]
      map_zero' := by rw [star_zero, map_zero, conjugateOperator_zero]
      map_add' := fun g h => by rw [star_add, map_add, conjugateOperator_add]
      commutes' := fun c => by
        simp only [Algebra.algebraMap_eq_smul_one, star_smul, star_one, map_smul, map_one,
          conjugateOperator_complex_smul, conjugateOperator_one,
          Algebra.algebraMap_eq_smul_one]
        congr 1
        simp
      map_star' := fun g => by
        change conjugateOperator (cfcHom hU (star (star g)))
          = star (conjugateOperator (cfcHom hU (star g)))
        rw [star_star, ContinuousLinearMap.star_eq_adjoint,
          ← conjugateOperator_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
          ← map_star, star_star] }
  have hdist : ∀ g h : C(spectrum ℂ U, ℂ), dist (star g) (star h) ≤ dist g h := by
    intro g h
    refine (ContinuousMap.dist_le dist_nonneg).mpr fun x => ?_
    have hx : dist ((star g) x) ((star h) x) = dist (g x) (h x) := by
      simp only [ContinuousMap.star_apply, Complex.dist_eq, ← star_sub, norm_star]
    rw [hx]
    exact ContinuousMap.dist_apply_le_dist x
  have hstarcont : Continuous (star : C(spectrum ℂ U, ℂ) → C(spectrum ℂ U, ℂ)) := by
    refine (Isometry.of_dist_eq fun g h => le_antisymm (hdist g h) ?_).continuous
    simpa only [star_star] using hdist (star g) (star h)
  have hcont : Continuous Ψ :=
    continuous_conjugateOperatorHom.comp ((cfcHom_continuous hU).comp hstarcont)
  have hid : Ψ ((ContinuousMap.id ℂ).restrict (spectrum ℂ U)) = U := by
    change conjugateOperator (cfcHom hU (star ((ContinuousMap.id ℂ).restrict _))) = U
    rw [map_star, cfcHom_id hU, ← hUc, conjugateOperator_involutive]
  have heq : cfcHom hU = Ψ := cfcHom_eq_of_continuous_of_map_id hU Ψ hcont hid
  have happ : cfcHom hU (star f) = conjugateOperator (cfcHom hU (star (star f))) :=
    DFunLike.congr_fun heq (star f)
  rw [star_star] at happ
  exact happ.symm

/-- The diagonal spectral measures of the Cayley transform are conjugation
invariant: real symbols have conjugation-invariant calculus images. -/
theorem diagMeasure_conjugation (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A) (η : Eℂ) :
    TauCeti.BorelCalculus.diagMeasure (TauCeti.LinearPMap.isStarNormal_cayley
        (PartialMapComplexification.isSelfAdjoint_complexify hA)) (conjugation η)
      = TauCeti.BorelCalculus.diagMeasure (TauCeti.LinearPMap.isStarNormal_cayley
          (PartialMapComplexification.isSelfAdjoint_complexify hA)) η := by
  have hUc := conjugateOperator_cayley A hA
  refine TauCeti.BorelCalculus.diagMeasure_congr _ (DFunLike.ext _ _ fun g => ?_)
  change (⟪conjugation η, cfcHom _ (TauCeti.BorelCalculus.ofRealLM g.toContinuousMap)
      (conjugation η)⟫_ℂ).re
    = (⟪η, cfcHom _ (TauCeti.BorelCalculus.ofRealLM g.toContinuousMap) η⟫_ℂ).re
  set T := cfcHom (TauCeti.LinearPMap.isStarNormal_cayley
    (PartialMapComplexification.isSelfAdjoint_complexify hA))
    (TauCeti.BorelCalculus.ofRealLM g.toContinuousMap) with hT
  have hfix : conjugateOperator T = T := by
    rw [hT, conjugateOperator_cfcHom _ hUc, TauCeti.BorelCalculus.star_ofRealLM]
  have hstep : ⟪conjugation η, T (conjugation η)⟫_ℂ = ⟪T η, η⟫_ℂ := by
    have h1 : T (conjugation η) = conjugation (conjugateOperator T η) := by
      rw [conjugateOperator_apply, conjugation_involutive]
    rw [h1, hfix, inner_conjugation]
  rw [hstep, ← inner_conj_symm]
  simp

/-- **Spectral projections of a complexified real operator are conjugation
invariant.**  Conjugation permutes the four polarisation points (`k ↔ -k`) and
fixes the diagonal measures; since indicator symbols are real, the four
integrals are real and the polarisation sum is its own conjugate. -/
theorem conjugateOperator_specProjection (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    conjugateOperator (TauCeti.LinearPMap.specProjection
        (PartialMapComplexification.isSelfAdjoint_complexify hA) S hS)
      = TauCeti.LinearPMap.specProjection
          (PartialMapComplexification.isSelfAdjoint_complexify hA) S hS := by
  set hAℂ := PartialMapComplexification.isSelfAdjoint_complexify hA with hhAc
  set hU := TauCeti.LinearPMap.isStarNormal_cayley hAℂ with hhU
  set κ := TauCeti.LinearPMap.cayleyInv hAℂ with hκ
  have hSm : MeasurableSet (κ ⁻¹' S) := TauCeti.LinearPMap.measurable_cayleyInv hAℂ hS
  set ind : _root_.spectrum ℂ (TauCeti.LinearPMap.cayley hAℂ) → ℂ :=
    (κ ⁻¹' S).indicator (fun _ => (1 : ℂ)) with hind
  -- the four polarisation integrals are real
  have hIreal : ∀ η : Eℂ,
      (starRingEnd ℂ) (∫ w, ind w ∂(TauCeti.BorelCalculus.diagMeasure hU η))
        = ∫ w, ind w ∂(TauCeti.BorelCalculus.diagMeasure hU η) := by
    intro η
    rw [hind, MeasureTheory.integral_indicator_const _ hSm]
    simp
  refine ContinuousLinearMap.ext fun ξ => ext_inner_left ℂ fun ψ => ?_
  -- Left as a `rw` chain on purpose: `simp only` with this same list fails to synthesize an
  -- instance that `rw` obtains from the rewritten form; simp normalises before the instance
  -- argument is determined.
  -- The four unfolding steps that used to be spelled as bare definition names
  -- (`specProjection`, `spectralPVM`, `toProjValMeasure_proj`, `specProj`) are now the single
  -- `specProjection_eq_borelCalculus`: `rw` with a definition name needs that definition's
  -- equation theorems, which are no longer generated for these module-system definitions.
  rw [conjugateOperator_apply, inner_conjugation_right, ← inner_conj_symm,
    TauCeti.LinearPMap.specProjection_eq_borelCalculus hAℂ S hS,
    TauCeti.BorelCalculus.inner_borelCalculus, TauCeti.BorelCalculus.inner_borelCalculus]
  -- move the conjugation through the four diagonal measures
  have h1 : conjugation ξ + conjugation ψ = conjugation (ξ + ψ) := (map_add _ _ _).symm
  have h2 : conjugation ξ + Complex.I • conjugation ψ
      = conjugation (ξ - Complex.I • ψ) := by
    rw [map_sub, conjugation_complex_smul, Complex.conj_I]
    module
  have h3 : conjugation ξ - conjugation ψ = conjugation (ξ - ψ) := (map_sub _ _ _).symm
  have h4 : conjugation ξ - Complex.I • conjugation ψ
      = conjugation (ξ + Complex.I • ψ) := by
    rw [map_add, conjugation_complex_smul, Complex.conj_I]
    module
  -- The `rw` chain this replaced listed `pair` twice and `diagMeasure_conjugation` four
  -- times, once per occurrence; `simp only` reaches them all in one pass.
  simp only [TauCeti.BorelCalculus.pair, h1, h2, h3, h4, diagMeasure_conjugation A hA]
  have e1 := hIreal (ξ + ψ)
  have e2 := hIreal (ξ + Complex.I • ψ)
  have e3 := hIreal (ξ - ψ)
  have e4 := hIreal (ξ - Complex.I • ψ)
  simp only [map_mul, map_sub, map_add, map_one, map_div₀, Complex.conj_I,
    Complex.conj_ofNat]
  rw [e1, e2, e3, e4]
  ring

/-- The spectral PVM of a complexified real self-adjoint operator is fixed by
canonical conjugation.  A PVM is determined by its diagonal measures, and those
are conjugation invariant. -/
theorem conjugatePVM_spectralPVM
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A) :
    conjugatePVM
        (TauCeti.LinearPMap.spectralPVM
          (PartialMapComplexification.isSelfAdjoint_complexify hA)) =
      TauCeti.LinearPMap.spectralPVM
        (PartialMapComplexification.isSelfAdjoint_complexify hA) :=
  TauCeti.ProjValMeasure.ext_of_diag fun ξ =>
    congrArg (MeasureTheory.Measure.map (TauCeti.LinearPMap.cayleyInv
      (PartialMapComplexification.isSelfAdjoint_complexify hA)))
      (diagMeasure_conjugation A hA ξ)

/-- Every measurable spectral projection of a complexified real self-adjoint
operator is fixed by canonical conjugation. -/
theorem conjugateOperator_selfAdjointSpectralProjection
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    conjugateOperator
        (selfAdjointSpectralProjection
          (PartialMapComplexification.complexify A)
          (PartialMapComplexification.isSelfAdjoint_complexify hA) S hS) =
      selfAdjointSpectralProjection
        (PartialMapComplexification.complexify A)
        (PartialMapComplexification.isSelfAdjoint_complexify hA) S hS := by
  exact conjugateOperator_specProjection A hA S hS

/-- The canonical real spectral projection, obtained by descending the complex
spectral projection of the complexified operator. -/
noncomputable def realSelfAdjointSpectralProjection
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S) : E →L[ℝ] E :=
  realPartOperator
    (selfAdjointSpectralProjection
      (PartialMapComplexification.complexify A)
      (PartialMapComplexification.isSelfAdjoint_complexify hA) S hS)

/-- Complexification of the descended real projection recovers the canonical
complex spectral projection. -/
theorem complexify_realSelfAdjointSpectralProjection
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    RealComplexification.complexify
        (realSelfAdjointSpectralProjection A hA S hS) =
      selfAdjointSpectralProjection
        (PartialMapComplexification.complexify A)
        (PartialMapComplexification.isSelfAdjoint_complexify hA) S hS := by
  exact complexify_realPartOperator
    (conjugateOperator_selfAdjointSpectralProjection A hA S hS)

/-- The real spectral projection acts on the real copy exactly as the complex
spectral projection. -/
theorem selfAdjointSpectralProjection_ofReal
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S) (x : E) :
    selfAdjointSpectralProjection
        (PartialMapComplexification.complexify A)
        (PartialMapComplexification.isSelfAdjoint_complexify hA) S hS
        (ofReal x) =
      ofReal (realSelfAdjointSpectralProjection A hA S hS x) := by
  rw [← complexify_realSelfAdjointSpectralProjection A hA S hS]
  simp

/-- The descended real spectral projection is idempotent. -/
theorem realSelfAdjointSpectralProjection_idem
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    realSelfAdjointSpectralProjection A hA S hS *
        realSelfAdjointSpectralProjection A hA S hS =
      realSelfAdjointSpectralProjection A hA S hS := by
  change realSelfAdjointSpectralProjection A hA S hS ∘L
      realSelfAdjointSpectralProjection A hA S hS =
    realSelfAdjointSpectralProjection A hA S hS
  apply RealComplexification.complexify_injective
  rw [RealComplexification.complexify_comp,
    complexify_realSelfAdjointSpectralProjection]
  change selfAdjointSpectralProjection
      (PartialMapComplexification.complexify A)
      (PartialMapComplexification.isSelfAdjoint_complexify hA) S hS *
    selfAdjointSpectralProjection
      (PartialMapComplexification.complexify A)
      (PartialMapComplexification.isSelfAdjoint_complexify hA) S hS = _
  exact (TauCeti.LinearPMap.spectralPVM
    (PartialMapComplexification.isSelfAdjoint_complexify hA)).proj_idem S hS

/-- The descended real spectral projection is self-adjoint. -/
theorem realSelfAdjointSpectralProjection_isSelfAdjoint
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    IsSelfAdjoint (realSelfAdjointSpectralProjection A hA S hS) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  apply RealComplexification.complexify_injective
  rw [TauCeti.RealComplexification.complexify_adjoint,
    complexify_realSelfAdjointSpectralProjection]
  exact (TauCeti.LinearPMap.spectralPVM
    (PartialMapComplexification.isSelfAdjoint_complexify hA)).isSelfAdjoint_proj S hS
    |>.adjoint_eq

/-- The real spectral range. -/
noncomputable def realSelfAdjointSpectralSubspace
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S) : Submodule ℝ E :=
  (realSelfAdjointSpectralProjection A hA S hS).range

/-- The real self-adjoint spectral subspace is the range of its spectral projection. -/
@[simp]
theorem realSelfAdjointSpectralSubspace_eq_range
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    realSelfAdjointSpectralSubspace A hA S hS =
      (realSelfAdjointSpectralProjection A hA S hS).range :=
  rfl

/-- It is complete, being the range of an idempotent bounded operator. -/
noncomputable instance realSelfAdjointSpectralSubspace_completeSpace
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    CompleteSpace (realSelfAdjointSpectralSubspace A hA S hS) := by
  change CompleteSpace (realSelfAdjointSpectralProjection A hA S hS).range
  exact (ContinuousLinearMap.IsIdempotentElem.isClosed_range
    (realSelfAdjointSpectralProjection_idem A hA S hS)).completeSpace_coe

/-- It is orthogonally complemented, so the operator reduces to it. -/
noncomputable instance realSelfAdjointSpectralSubspace_hasOrthogonalProjection
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    (realSelfAdjointSpectralSubspace A hA S hS).HasOrthogonalProjection := by
  change (realSelfAdjointSpectralProjection A hA S hS).range.HasOrthogonalProjection
  exact ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range
    (show IsIdempotentElem (realSelfAdjointSpectralProjection A hA S hS) from
      realSelfAdjointSpectralProjection_idem A hA S hS)

/-- Every projected vector belongs to the descended real spectral range. -/
theorem realSelfAdjointSpectralProjection_mem_subspace
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S) (x : E) :
    realSelfAdjointSpectralProjection A hA S hS x ∈
      realSelfAdjointSpectralSubspace A hA S hS :=
  ⟨x, rfl⟩

/-- A vector in the descended real spectral range is fixed by the projection. -/
theorem realSelfAdjointSpectralProjection_eq_self_of_mem
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S) {x : E}
    (hx : x ∈ realSelfAdjointSpectralSubspace A hA S hS) :
    realSelfAdjointSpectralProjection A hA S hS x = x := by
  rcases hx with ⟨y, rfl⟩
  change realSelfAdjointSpectralProjection A hA S hS
      (realSelfAdjointSpectralProjection A hA S hS y) =
    realSelfAdjointSpectralProjection A hA S hS y
  simpa only [mul_apply_eq_comp] using congrArg
    (fun T : E →L[ℝ] E => T y)
    (realSelfAdjointSpectralProjection_idem A hA S hS)

/-- The descended spectral projection is the orthogonal projection onto its
real range. -/
theorem realSelfAdjointSpectralProjection_eq_starProjection
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    realSelfAdjointSpectralProjection A hA S hS =
      (realSelfAdjointSpectralSubspace A hA S hS).starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact realSelfAdjointSpectralProjection_mem_subspace A hA S hS x
  · intro y hy
    have hyfix := realSelfAdjointSpectralProjection_eq_self_of_mem
      A hA S hS hy
    rw [← hyfix]
    have hadj := ContinuousLinearMap.adjoint_inner_right
      (realSelfAdjointSpectralProjection A hA S hS)
      (x - realSelfAdjointSpectralProjection A hA S hS x) y
    rw [(realSelfAdjointSpectralProjection_isSelfAdjoint A hA S hS).adjoint_eq] at hadj
    rw [hadj, map_sub,
      realSelfAdjointSpectralProjection_eq_self_of_mem A hA S hS
        (realSelfAdjointSpectralProjection_mem_subspace A hA S hS x),
      sub_self, inner_zero_left]

/-- The complexification of the descended real spectral range is exactly the
canonical complex spectral range of the complexified operator.  This is the
consistency theorem that rules out an arbitrary or underspecified real descent. -/
theorem complexifySubmodule_realSelfAdjointSpectralSubspace
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    complexifySubmodule (realSelfAdjointSpectralSubspace A hA S hS) =
      selfAdjointSpectralSubspace
        (PartialMapComplexification.complexify A)
        (PartialMapComplexification.isSelfAdjoint_complexify hA) S hS := by
  ext z
  rw [← Submodule.starProjection_eq_self_iff,
    ← Submodule.starProjection_eq_self_iff]
  rw [starProjection_complexifySubmodule,
    ← realSelfAdjointSpectralProjection_eq_starProjection,
    complexify_realSelfAdjointSpectralProjection,
    ← selfAdjointSpectralProjection_eq_starProjection]

/-- Complementation of measurable sets becomes orthogonal complementation of
real spectral ranges. -/
theorem realSelfAdjointSpectralProjection_compl
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    realSelfAdjointSpectralProjection A hA Sᶜ hS.compl =
      ContinuousLinearMap.id ℝ E -
        realSelfAdjointSpectralProjection A hA S hS := by
  apply RealComplexification.complexify_injective
  rw [complexify_realSelfAdjointSpectralProjection,
    RealComplexification.complexify_sub,
    RealComplexification.complexify_id,
    complexify_realSelfAdjointSpectralProjection]
  exact (TauCeti.LinearPMap.spectralPVM
    (PartialMapComplexification.isSelfAdjoint_complexify hA)).proj_compl S hS

/-- The range selected by the complement set is the orthogonal complement of
the selected real spectral range. -/
theorem realSelfAdjointSpectralSubspace_compl
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    realSelfAdjointSpectralSubspace A hA Sᶜ hS.compl =
      (realSelfAdjointSpectralSubspace A hA S hS)ᗮ := by
  apply Submodule.ext
  intro x
  rw [← Submodule.starProjection_eq_self_iff,
    ← Submodule.starProjection_eq_self_iff]
  rw [← realSelfAdjointSpectralProjection_eq_starProjection,
    realSelfAdjointSpectralProjection_compl,
    Submodule.starProjection_orthogonal,
    ← realSelfAdjointSpectralProjection_eq_starProjection]

omit [CompleteSpace E] in
/-- The real copy of a domain vector has the expected underlying vector. -/
private theorem coe_ofRealDomain (A : E →ₗ.[ℝ] E) (x : A.domain) :
    ((PartialMapComplexification.ofRealDomain A x :
      (PartialMapComplexification.complexify A).domain) : Eℂ) =
      ofReal (x : E) :=
  rfl

/-- The real spectral projection preserves the original real operator domain. -/
theorem realSelfAdjointSpectralProjection_mem_domain
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    {S : Set ℝ} (hS : MeasurableSet S) (x : A.domain) :
    realSelfAdjointSpectralProjection A hA S hS (x : E) ∈ A.domain := by
  have hproj := selfAdjointSpectralProjection_mem_domain
    (PartialMapComplexification.complexify A)
    (PartialMapComplexification.isSelfAdjoint_complexify hA) hS
    (PartialMapComplexification.ofRealDomain A x)
  rw [PartialMapComplexification.mem_complexify_domain_iff] at hproj
  have hre := hproj.1
  rw [coe_ofRealDomain A x, selfAdjointSpectralProjection_ofReal,
    re_ofReal] at hre
  exact hre

/-- The real operator commutes with its descended spectral projections on the
full operator domain. -/
theorem realSelfAdjoint_apply_spectralProjection
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    {S : Set ℝ} (hS : MeasurableSet S) (x : A.domain) :
    A
        ⟨realSelfAdjointSpectralProjection A hA S hS (x : E),
          realSelfAdjointSpectralProjection_mem_domain A hA hS x⟩ =
      realSelfAdjointSpectralProjection A hA S hS (A x) := by
  have hcomm := selfAdjoint_apply_spectralProjection
    (PartialMapComplexification.complexify A)
    (PartialMapComplexification.isSelfAdjoint_complexify hA) hS
    (PartialMapComplexification.ofRealDomain A x)
  have hre := congrArg re hcomm
  rw [PartialMapComplexification.complexify_apply_re,
    PartialMapComplexification.complexify_apply_ofReal,
    selfAdjointSpectralProjection_ofReal A hA S hS, re_ofReal] at hre
  refine Eq.trans ?_ hre
  refine PartialMapComplexification.toLinearMap_congr ?_
  show realSelfAdjointSpectralProjection A hA S hS (x : E) =
    re (selfAdjointSpectralProjection
      (PartialMapComplexification.complexify A)
      (PartialMapComplexification.isSelfAdjoint_complexify hA) S hS
      (ofReal (x : E)))
  rw [selfAdjointSpectralProjection_ofReal A hA S hS, re_ofReal]

/-- The real spectral range reduces the original real self-adjoint operator. -/
theorem realSelfAdjointSpectralSubspace_reducing
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    TauCeti.LinearPMap.ReducesSubspace A
      (realSelfAdjointSpectralSubspace A hA S hS) := by
  let U := realSelfAdjointSpectralSubspace A hA S hS
  let Uc := realSelfAdjointSpectralSubspace A hA Sᶜ hS.compl
  have hUc : Uc = Uᗮ := realSelfAdjointSpectralSubspace_compl A hA S hS
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    rw [← realSelfAdjointSpectralProjection_eq_starProjection]
    exact realSelfAdjointSpectralProjection_mem_domain A hA hS x
  · intro x
    have hx := realSelfAdjointSpectralProjection_mem_domain A hA hS.compl x
    rw [realSelfAdjointSpectralProjection_eq_starProjection,
      Submodule.starProjection_congr_apply hUc] at hx
    exact hx
  · intro x hx
    rw [← Submodule.starProjection_eq_self_iff] at hx ⊢
    rw [← realSelfAdjointSpectralProjection_eq_starProjection] at hx ⊢
    have hcomm := realSelfAdjoint_apply_spectralProjection A hA hS x
    have hsub :
        (⟨realSelfAdjointSpectralProjection A hA S hS (x : E),
          realSelfAdjointSpectralProjection_mem_domain A hA hS x⟩ : A.domain) = x :=
      Subtype.ext hx
    simpa [hsub] using hcomm.symm
  · intro x hx
    rw [← hUc] at hx ⊢
    rw [← Submodule.starProjection_eq_self_iff] at hx ⊢
    rw [← realSelfAdjointSpectralProjection_eq_starProjection] at hx ⊢
    have hcomm := realSelfAdjoint_apply_spectralProjection A hA hS.compl x
    have hsub :
        (⟨realSelfAdjointSpectralProjection A hA Sᶜ hS.compl (x : E),
          realSelfAdjointSpectralProjection_mem_domain A hA hS.compl x⟩ : A.domain) = x :=
      Subtype.ext hx
    simpa [hsub] using hcomm.symm

/-- Canonical inclusion of a real spectral range. -/
noncomputable def realSelfAdjointSpectralSubspaceInclusion
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    realSelfAdjointSpectralSubspace A hA S hS →L[ℝ] E :=
  TauCeti.DavisKahanExt.PartialMap.reducingSubspaceInclusion
    (realSelfAdjointSpectralSubspace A hA S hS)

/-- The real spectral-range inclusion is isometric. -/
theorem realSelfAdjointSpectralSubspaceInclusion_isometric
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    IsometricEmbedding
      (realSelfAdjointSpectralSubspaceInclusion A hA S hS) :=
  TauCeti.DavisKahanExt.PartialMap.reducingSubspaceInclusion_isometric _

/-- Canonical real closed restriction to a measurable spectral range. -/
noncomputable def realSelfAdjointSpectralRestriction
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    realSelfAdjointSpectralSubspace A hA S hS →ₗ.[ℝ]
      realSelfAdjointSpectralSubspace A hA S hS :=
  TauCeti.LinearPMap.reducingRestriction A
    (realSelfAdjointSpectralSubspace A hA S hS)
    (realSelfAdjointSpectralSubspace_reducing A hA S hS)

/-- The canonical real spectral restriction is self-adjoint. -/
theorem realSelfAdjointSpectralRestriction_isSelfAdjoint
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    _root_.IsSelfAdjoint (realSelfAdjointSpectralRestriction A hA S hS) := by
  exact TauCeti.DavisKahanExt.PartialMap.reducingRestriction_isSelfAdjoint
    A (realSelfAdjointSpectralSubspace A hA S hS)
    (realSelfAdjointSpectralSubspace_reducing A hA S hS) hA

/-- The real spectral inclusion maps the restricted domain into the ambient
operator domain. -/
theorem realSelfAdjointSpectralRestriction_inclusion_mem_domain
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S)
    (x : (realSelfAdjointSpectralRestriction A hA S hS).domain) :
    realSelfAdjointSpectralSubspaceInclusion A hA S hS
        (x : realSelfAdjointSpectralSubspace A hA S hS) ∈ A.domain := by
  exact TauCeti.DavisKahanExt.PartialMap.reducingRestriction_inclusion_mem_domain
    A (realSelfAdjointSpectralSubspace A hA S hS)
    (realSelfAdjointSpectralSubspace_reducing A hA S hS) x

/-- The real spectral inclusion intertwines the restricted and ambient closed
operators. -/
theorem realSelfAdjointSpectralRestriction_inclusion_intertwines
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    (S : Set ℝ) (hS : MeasurableSet S)
    (x : (realSelfAdjointSpectralRestriction A hA S hS).domain) :
    A
        ⟨realSelfAdjointSpectralSubspaceInclusion A hA S hS
            (x : realSelfAdjointSpectralSubspace A hA S hS),
          realSelfAdjointSpectralRestriction_inclusion_mem_domain
            A hA S hS x⟩ =
      realSelfAdjointSpectralSubspaceInclusion A hA S hS
        ((realSelfAdjointSpectralRestriction A hA S hS) x) := by
  exact TauCeti.DavisKahanExt.PartialMap.reducingRestriction_inclusion_intertwines
    A (realSelfAdjointSpectralSubspace A hA S hS)
    (realSelfAdjointSpectralSubspace_reducing A hA S hS) x

end
end RealSpectralRestriction
end DavisKahan
end TauCeti
