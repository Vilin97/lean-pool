/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.RealUnboundedIdeal
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.TrialReflection
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.ReflectedDefectDoubling
import
  LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.SubspaceSingularTransport
import
  LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.HeterogeneousRepresentative
import
  LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNormLaws

/-! # Sin Two Theta Unbounded Directed Residual Real -/

open TauCeti.DavisKahan.Sylvester

/-!
# The unbounded directed half of the `sin 2Θ` theorem over a REAL Hilbert space

> **Theorem (the `sin 2θ` theorem).**  Assume there is an interval `[β,α]` and a
> `δ > 0` such that the spectrum of `Λ₀` lies entirely in `[β,α]` while that of
> `Λ₁` lies entirely outside of `]β-δ, α+δ[`.  Then for every unitary-invariant
> norm, `δ‖sin 2Θ₀‖ ≤ 2‖R‖` and `δ‖sin 2Θ‖ ≤ 2‖H‖`.

Standing assumption 1 of Davis--Kahan 1970 is that the Hilbert space is "real or
complex".  `SinTwoThetaUnboundedDirectedResidual.lean` proves the directed
conclusion `δ N(sin 2Θ₀) ≤ 2 N(R)` at the printed trial residual

`R = A E₀ - E₀ A₀`   (equation 1.8)

for an unbounded self-adjoint `A` over a complex Hilbert space.  This module is
its real-scalar sibling, proved natively.

## Why native and not by complexification

Transporting the complex endpoint would change the object being estimated: the
statement would carry the complexified residual and the complexified spectral
subspaces, and the printed real conclusion would then be a corollary only up to
further transport hypotheses.  Every ingredient of the complex proof is either
scalar-generic already — the trial-reflection bridge
(`SineTheta/TrialReflection.lean`), the sharp doubling identity
(`SineTheta/ReflectedDefectDoubling.lean`), the rectangular ideal interface, and
the extension-by-zero singular-value transport — or has a maintained real
counterpart, namely `sinTwoTheta_reflectionResidual_block_gauge_real`.  So the
real assembly is the same five steps as the complex one, instantiated at `ℝ`.

## The one deliberate difference from the complex statement

The complex spectral-separation hypotheses are `TauCeti.LinearPMap.SemiboundedBelow`/
`TauCeti.LinearPMap.SemiboundedAbove` for the exact block together with resolvent-set avoidance for
the complementary block, and the latter is stated through
`TauCeti.LinearPMap.spectrum`, which exists over `ℂ` only.  The maintained real
tree instead carries the scalar-generic `FormBoundedSylvesterGap`, which covers
all three of the source's separation configurations — the printed
interval/exterior one over `realSpectrum`, and both ordered half-line ones — and
is the *weaker* of the tree's two spellings of separation.  A theorem stated
over it is therefore the stronger theorem, exactly as on the complex side, where
the printed spectral containment likewise implies the hypotheses used.

`sinTwoTheta_directed_unboundedResidual_blockRepresentative_intervalExterior_symmetricNorming_real`
restates the endpoint at the printed interval/exterior separation itself, so the
source hypothesis is visible without unfolding the gap predicate.
-/

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.RealSpectralRestriction

open scoped InnerProductSpace
open scoped TauCeti.CompleteSubspace

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

section MainEstimate

variable {V : Submodule ℝ E} [V.HasOrthogonalProjection]
  {M : V →L[ℝ] V} {R : V →L[ℝ] E}
  {A : E →ₗ.[ℝ] E}

/-- **Davis--Kahan 1970, the directed half of the `sin 2Θ` theorem for an
unbounded self-adjoint operator over a REAL Hilbert space, Ky Fan form.**

`A` is the (possibly unbounded) self-adjoint operator whose reducing subspace is
the exact one, `V` is the trial subspace, `M` is the trial operator `A₀`, and `R`
is the printed residual `R = A E₀ - E₀ A₀`.  The conclusion is

`δ · kyFan_k (sin 2Θ₀) ≤ 2 · kyFan_k R`

with the printed factor two. -/
theorem sinTwoTheta_directed_unboundedResidual_blockRepresentative_kyFan_real
    (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hVdom : ∀ v : V, (v : E) ∈ A.domain)
    (hres : ∀ v : V, A ⟨(v : E), hVdom v⟩ = R v + ((M v : V) : E))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (realSelfAdjointSpectralRestriction A hA B hB)
      (realSelfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ) :
    ∀ k : ℕ,
      δ * kyFanApproximationGauge k
          (sinTwoThetaIdealBlock (realSelfAdjointSpectralSubspace A hA B hB) V) ≤
        2 * kyFanApproximationGauge k R := by
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  have hSsa : IsSelfAdjoint (trialOffDiagonalPart V M R) :=
    isSelfAdjoint_trialOffDiagonalPart
  have hDsa' : IsSelfAdjoint ((-2 : ℝ) • trialOffDiagonalPart V M R) := by
    rw [IsSelfAdjoint, star_smul, hSsa.star_eq]
    norm_num
  have hDsa : ((-2 : ℝ) • trialOffDiagonalPart V M R).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hDsa'
  have hraw := sinTwoTheta_reflectionResidual_block_gauge_real A hA B hB
    (KyFanDominantIdealFamily.kyFan (𝕜 := ℝ) k hk)
    ((-2 : ℝ) • trialOffDiagonalPart V M R) hDsa V hδ hgap
    (reflectionOperator_mem_domain hVdom)
    (trialReflection_intertwines hA hVdom hres)
    (KyFanDominantIdealFamily.kyFan_mem (𝕜 := ℝ) k hk _)
  rw [KyFanDominantIdealFamily.kyFan_gauge,
    KyFanDominantIdealFamily.kyFan_gauge] at hraw
  -- flip the block to the orientation of the doubling identity
  have hflip : kyFanApproximationGauge k
        ((realSelfAdjointSpectralSubspace A hA B hB).starProjection ∘L
          ((-2 : ℝ) • trialOffDiagonalPart V M R) ∘L
          ((realSelfAdjointSpectralSubspace A hA B hB)ᗮ.map
            (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection) =
      kyFanApproximationGauge k
        (((realSelfAdjointSpectralSubspace A hA B hB)ᗮ.map
            (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection ∘L
          ((-2 : ℝ) • trialOffDiagonalPart V M R) ∘L
          (realSelfAdjointSpectralSubspace A hA B hB).starProjection) := by
    rw [← kyFanApproximationGauge_adjoint]
    congr 1
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      (isSelfAdjoint_starProjection _).adjoint_eq,
      (isSelfAdjoint_starProjection _).adjoint_eq,
      ContinuousLinearMap.isSelfAdjoint_iff'.mp hDsa']
    rfl
  -- the sharp factor two, from the scalar-generic doubling identity
  have hdouble := kyFan_reflectionDefectBlock_le_two_mul hSsa
    (realSelfAdjointSpectralSubspace A hA B hB) V k
  rw [reflectionDefect_trialOffDiagonalPart, trialOffDiagonalPart_upper] at hdouble
  -- the cross block factors through the printed trial residual
  have hblockR : kyFanApproximationGauge k (trialOffDiagonalBlock V M R) ≤
      kyFanApproximationGauge k R := by
    rw [trialOffDiagonalBlock_eq]
    refine (kyFanApproximationGauge_comp_le k Vᗮ.starProjection R
      V.subtypeL.adjoint).trans ?_
    have hQ : ‖(Vᗮ.starProjection : E →L[ℝ] E)‖ ≤ 1 := Submodule.starProjection_norm_le _
    have hI : ‖(V.subtypeL.adjoint : E →L[ℝ] V)‖ ≤ 1 := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact opNorm_le_one_of_isometry (fun _ => rfl)
    have hnn : 0 ≤ kyFanApproximationGauge k R := kyFanApproximationGauge_nonneg k R
    calc ‖(Vᗮ.starProjection : E →L[ℝ] E)‖ * kyFanApproximationGauge k R *
          ‖(V.subtypeL.adjoint : E →L[ℝ] V)‖
        ≤ 1 * kyFanApproximationGauge k R * 1 := by gcongr
      _ = kyFanApproximationGauge k R := by ring
  calc δ * kyFanApproximationGauge k
        (sinTwoThetaIdealBlock (realSelfAdjointSpectralSubspace A hA B hB) V)
      ≤ kyFanApproximationGauge k
          ((realSelfAdjointSpectralSubspace A hA B hB).starProjection ∘L
            ((-2 : ℝ) • trialOffDiagonalPart V M R) ∘L
            ((realSelfAdjointSpectralSubspace A hA B hB)ᗮ.map
              (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection) := hraw.2
    _ = kyFanApproximationGauge k
          (((realSelfAdjointSpectralSubspace A hA B hB)ᗮ.map
              (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection ∘L
            ((-2 : ℝ) • trialOffDiagonalPart V M R) ∘L
            (realSelfAdjointSpectralSubspace A hA B hB).starProjection) := hflip
    _ ≤ 2 * kyFanApproximationGauge k (trialOffDiagonalBlock V M R) := hdouble
    _ ≤ 2 * kyFanApproximationGauge k R := by gcongr

/-- **Davis--Kahan 1970, the directed half of the `sin 2Θ` theorem for an
unbounded self-adjoint operator over a REAL Hilbert space, at every source
unitarily invariant norm.**

This is the printed Section 2 directed conclusion over the real scalars:

`δ N(sin 2Θ₀) ≤ 2 N(R)`,  `R = A E₀ - E₀ A₀`,

for every `SymmetricNormingFunction`, with the printed spectral separation, the
printed residual, the printed factor two, and no hypothesis beyond the printed
ones: `A` self-adjoint and possibly unbounded, the trial subspace inside its
domain, and the residual bounded — which is exactly the source's own requirement
for a useful unbounded conclusion.

The reflected system is built internally from the trial data; no reflection
residual appears in the statement. -/
theorem sinTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hVdom : ∀ v : V, (v : E) ∈ A.domain)
    (hres : ∀ v : V, A ⟨(v : E), hVdom v⟩ = R v + ((M v : V) : E))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (realSelfAdjointSpectralRestriction A hA B hB)
      (realSelfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hRmem : N.Mem R) :
    N.Mem (sinTwoThetaIdealBlock (realSelfAdjointSpectralSubspace A hA B hB) V) ∧
      δ * N.gauge
          (sinTwoThetaIdealBlock (realSelfAdjointSpectralSubspace A hA B hB) V) ≤
        2 * N.gauge R := by
  let R0 : E →L[ℝ] E := R ∘L V.subtypeL.adjoint
  have hsameR : SameApproximationSingularSequence R0 R :=
    sameApproximationSingularValues_extendDomainByZero V R
  have htransport := hsameR.normingMem_iff_and_gauge_eq N
  have hMem0 : N.Mem R0 := htransport.1.mpr hRmem
  have hgauge : N.gauge R0 = N.gauge R := htransport.2
  have htwo : ‖(2 : ℝ)‖ = 2 := by norm_num
  have hscaled : ∀ k : ℕ,
      δ * kyFanApproximationGauge k
          (sinTwoThetaIdealBlock (realSelfAdjointSpectralSubspace A hA B hB) V) ≤
        kyFanApproximationGauge k ((2 : ℝ) • R0) := by
    intro k
    rw [kyFanApproximationGauge_smul, htwo, hsameR.kyFanApproximationGauge_eq k]
    exact sinTwoTheta_directed_unboundedResidual_blockRepresentative_kyFan_real hA B hB hVdom hres
      hδ hgap k
  have hMem2 : N.Mem ((2 : ℝ) • R0) := by
    intro htop
    rw [N.extendedGauge_smul, htwo] at htop
    rcases ENNReal.mul_eq_top.mp htop with ⟨_, h⟩ | ⟨h, _⟩
    · exact hMem0 h
    · exact absurd h (by simp)
  obtain ⟨hmem, hle⟩ := N.mul_gauge_le_of_all_mul_kyFan_le hδ hMem2 hscaled
  refine ⟨hmem, ?_⟩
  rw [N.gauge_smul _ hMem0, htwo, hgauge] at hle
  exact hle

/-- The real directed endpoint restated at the **printed** separation
hypothesis: the exact block has real spectrum inside `[β,α]` and the
complementary block has real spectrum outside `]β-δ, α+δ[`. -/
theorem
  sinTwoTheta_directed_unboundedResidual_blockRepresentative_intervalExterior_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hVdom : ∀ v : V, (v : E) ∈ A.domain)
    (hres : ∀ v : V, A ⟨(v : E), hVdom v⟩ = R v + ((M v : V) : E))
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : RealSpectrumIntervalExteriorGap
      (realSelfAdjointSpectralRestriction A hA B hB)
      (realSelfAdjointSpectralRestriction A hA Bᶜ hB.compl) β α δ)
    (hRmem : N.Mem R) :
    N.Mem (sinTwoThetaIdealBlock (realSelfAdjointSpectralSubspace A hA B hB) V) ∧
      δ * N.gauge
          (sinTwoThetaIdealBlock (realSelfAdjointSpectralSubspace A hA B hB) V) ≤
        2 * N.gauge R :=
  sinTwoTheta_directed_unboundedResidual_blockRepresentative_symmetricNorming_real N hA B hB
    hVdom hres hδ
    (FormBoundedSylvesterGap.intervalExterior hβα hgap) hRmem

/-! ### The same two estimates at an arbitrary reducing subspace, over `ℝ`

The real mirror of the reducing endpoints in
`SinTwoThetaUnboundedDirectedResidual.lean`. -/

/-- **Davis--Kahan 1970, the directed half of the `sin 2Θ` theorem for an
unbounded self-adjoint operator over a REAL Hilbert space, Ky Fan form, at an
arbitrary reducing subspace.**

`δ · kyFan_k (sin 2Θ₀) ≤ 2 · kyFan_k R` with the printed factor two, and with
`hred` about `U`, the gap-carrying subspace, rather than about the trial subspace
`V`, which is assumed only to lie inside `dom A`. -/
theorem sinTwoTheta_directed_unboundedResidual_blockRepresentative_reducing_kyFan_real
    (hA : IsSelfAdjoint A)
    {U : Submodule ℝ E} [U.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hVdom : ∀ v : V, (v : E) ∈ A.domain)
    (hres : ∀ v : V, A ⟨(v : E), hVdom v⟩ = R v + ((M v : V) : E))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hred)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hred.orthogonal) δ) :
    ∀ k : ℕ,
      δ * kyFanApproximationGauge k
          (sinTwoThetaIdealBlock U V) ≤
        2 * kyFanApproximationGauge k R := by
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  have hSsa : IsSelfAdjoint (trialOffDiagonalPart V M R) :=
    isSelfAdjoint_trialOffDiagonalPart
  have hDsa' : IsSelfAdjoint ((-2 : ℝ) • trialOffDiagonalPart V M R) := by
    rw [IsSelfAdjoint, star_smul, hSsa.star_eq]
    norm_num
  have hDsa : ((-2 : ℝ) • trialOffDiagonalPart V M R).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hDsa'
  have hraw := sinTwoTheta_reflectionResidual_block_gauge_reducing_real hA hred
    (KyFanDominantIdealFamily.kyFan (𝕜 := ℝ) k hk)
    ((-2 : ℝ) • trialOffDiagonalPart V M R) hDsa V hδ hgap
    (reflectionOperator_mem_domain hVdom)
    (trialReflection_intertwines hA hVdom hres)
    (KyFanDominantIdealFamily.kyFan_mem (𝕜 := ℝ) k hk _)
  rw [KyFanDominantIdealFamily.kyFan_gauge,
    KyFanDominantIdealFamily.kyFan_gauge] at hraw
  -- flip the block to the orientation of the doubling identity
  have hflip : kyFanApproximationGauge k
        (U.starProjection ∘L
          ((-2 : ℝ) • trialOffDiagonalPart V M R) ∘L
          (Uᗮ.map
            (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection) =
      kyFanApproximationGauge k
        ((Uᗮ.map
            (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection ∘L
          ((-2 : ℝ) • trialOffDiagonalPart V M R) ∘L
          U.starProjection) := by
    rw [← kyFanApproximationGauge_adjoint]
    congr 1
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      (isSelfAdjoint_starProjection _).adjoint_eq,
      (isSelfAdjoint_starProjection _).adjoint_eq,
      ContinuousLinearMap.isSelfAdjoint_iff'.mp hDsa']
    rfl
  -- the sharp factor two, from the scalar-generic doubling identity
  have hdouble := kyFan_reflectionDefectBlock_le_two_mul hSsa
    U V k
  rw [reflectionDefect_trialOffDiagonalPart, trialOffDiagonalPart_upper] at hdouble
  -- the cross block factors through the printed trial residual
  have hblockR : kyFanApproximationGauge k (trialOffDiagonalBlock V M R) ≤
      kyFanApproximationGauge k R := by
    rw [trialOffDiagonalBlock_eq]
    refine (kyFanApproximationGauge_comp_le k Vᗮ.starProjection R
      V.subtypeL.adjoint).trans ?_
    have hQ : ‖(Vᗮ.starProjection : E →L[ℝ] E)‖ ≤ 1 := Submodule.starProjection_norm_le _
    have hI : ‖(V.subtypeL.adjoint : E →L[ℝ] V)‖ ≤ 1 := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact opNorm_le_one_of_isometry (fun _ => rfl)
    have hnn : 0 ≤ kyFanApproximationGauge k R := kyFanApproximationGauge_nonneg k R
    calc ‖(Vᗮ.starProjection : E →L[ℝ] E)‖ * kyFanApproximationGauge k R *
          ‖(V.subtypeL.adjoint : E →L[ℝ] V)‖
        ≤ 1 * kyFanApproximationGauge k R * 1 := by gcongr
      _ = kyFanApproximationGauge k R := by ring
  calc δ * kyFanApproximationGauge k
        (sinTwoThetaIdealBlock U V)
      ≤ kyFanApproximationGauge k
          (U.starProjection ∘L
            ((-2 : ℝ) • trialOffDiagonalPart V M R) ∘L
            (Uᗮ.map
              (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection) := hraw.2
    _ = kyFanApproximationGauge k
          ((Uᗮ.map
              (V.reflection.toLinearEquiv : E →ₗ[ℝ] E)).starProjection ∘L
            ((-2 : ℝ) • trialOffDiagonalPart V M R) ∘L
            U.starProjection) := hflip
    _ ≤ 2 * kyFanApproximationGauge k (trialOffDiagonalBlock V M R) := hdouble
    _ ≤ 2 * kyFanApproximationGauge k R := by gcongr


/-- **Davis--Kahan 1970, the directed half of the `sin 2Θ` theorem for an
unbounded self-adjoint operator over a REAL Hilbert space, at every source
unitarily invariant norm and at an arbitrary reducing subspace.**

`δ N(sin 2Θ₀) ≤ 2 N(R)` with the printed residual and the printed factor two.
`hred` is about `U`, the gap-carrying subspace, which is not required to be a
spectral projector; the trial subspace `V` is assumed only to lie inside `dom A`.

The conclusion is on the proof's own block;
`sinTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_real` restates it
on the paper's trial-side angle. -/
theorem sinTwoTheta_directed_unboundedResidual_blockRepresentative_reducing_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (hA : IsSelfAdjoint A)
    {U : Submodule ℝ E} [U.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hVdom : ∀ v : V, (v : E) ∈ A.domain)
    (hres : ∀ v : V, A ⟨(v : E), hVdom v⟩ = R v + ((M v : V) : E))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A U hred)
      (TauCeti.LinearPMap.reducingRestriction A Uᗮ hred.orthogonal) δ)
    (hRmem : N.Mem R) :
    N.Mem (sinTwoThetaIdealBlock U V) ∧
      δ * N.gauge
          (sinTwoThetaIdealBlock U V) ≤
        2 * N.gauge R := by
  let R0 : E →L[ℝ] E := R ∘L V.subtypeL.adjoint
  have hsameR : SameApproximationSingularSequence R0 R :=
    sameApproximationSingularValues_extendDomainByZero V R
  have htransport := hsameR.normingMem_iff_and_gauge_eq N
  have hMem0 : N.Mem R0 := htransport.1.mpr hRmem
  have hgauge : N.gauge R0 = N.gauge R := htransport.2
  have htwo : ‖(2 : ℝ)‖ = 2 := by norm_num
  have hscaled : ∀ k : ℕ,
      δ * kyFanApproximationGauge k
          (sinTwoThetaIdealBlock U V) ≤
        kyFanApproximationGauge k ((2 : ℝ) • R0) := by
    intro k
    rw [kyFanApproximationGauge_smul, htwo, hsameR.kyFanApproximationGauge_eq k]
    exact sinTwoTheta_directed_unboundedResidual_blockRepresentative_reducing_kyFan_real
      hA hred hVdom hres hδ hgap k
  have hMem2 : N.Mem ((2 : ℝ) • R0) := by
    intro htop
    rw [N.extendedGauge_smul, htwo] at htop
    rcases ENNReal.mul_eq_top.mp htop with ⟨_, h⟩ | ⟨h, _⟩
    · exact hMem0 h
    · exact absurd h (by simp)
  obtain ⟨hmem, hle⟩ := N.mul_gauge_le_of_all_mul_kyFan_le hδ hMem2 hscaled
  refine ⟨hmem, ?_⟩
  rw [N.gauge_smul _ hMem0, htwo, hgauge] at hle
  exact hle


end MainEstimate

end

end DavisKahan1970
end TauCeti
