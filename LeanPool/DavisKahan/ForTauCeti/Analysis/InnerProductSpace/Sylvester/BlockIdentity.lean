/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Generator
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralCutOperator

/-!
# The Sylvester operator on a spectral block

On a block cut out by spectral projections of the two generators, the Sylvester
operator is a scalar plus two small corrections:

`𝒮 Z - (λ - α) Z = (A - λ)|_block ∘ Z - Z ∘ (B - α)|_block`

and both corrections are *bounded* operators of norm at most the block radius
(`specCutOp`).  That is what turns the pointwise Sylvester equation into a
Hilbert–Schmidt estimate: the ideal properties of the energy need bounded
factors, which the pointwise form does not provide.

## Why the identity needs a density argument

`generator_sylvesterGroup_apply` supplies `(𝒮 Z) x = A (Z x) - Z (B x)` only for
`x` in the domain of `B` — that is all an unbounded generator can give.  The
statement wanted is between bounded operators on all of `F`.  Both sides are
continuous and the domain is dense, so `ContinuousLinearMap.ext_on` closes the
gap.

The one step that is not formal: `Z (B x) = Z (B (Q x))`, which holds because
`Z = Z ∘ Q` and `Q` intertwines `B` (`specProjection_apply_domain`).  Without
the intertwining the two sides differ by `Z ((1 - Q) B x)`, which is not small.

## Sources

The block form of the Sylvester operator, and its use to reduce a spectral-gap
estimate to one block at a time, follow Bhatia--Davis--McIntosh; see
`prose/distilled_literature/BhatiaDavisMcIntosh1983_spectral_subspaces_sylvester.tex`.

## Provenance

*New.*

Moved from
`ForTauCeti/Analysis/InnerProductSpace/SylvesterBlockIdentity.lean` to
`ForTauCeti/Analysis/InnerProductSpace/Sylvester/BlockIdentity.lean`.  The `Sylvester/`
directory already held `Basic`, `Interval`, `SpectralDistance` and `Internal/`, while
six siblings of the same family used a flat `Sylvester*` prefix in the directory above;
one family now has one convention.  Path change and import repoint only — no statement,
signature, proof, attribute, declaration name or namespace changed.
-/

@[expose] public section

open scoped InnerProductSpace
open TauCeti.OneParameterUnitaryGroup (generator)

namespace TauCeti
namespace HilbertSchmidt

variable {ι : Type*} {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The Sylvester operator on a spectral block.**  Both correction terms are
bounded by the block radii, so this converts the pointwise Sylvester equation
into something the Hilbert–Schmidt ideal properties can consume.

The self-adjointness proofs are taken as *arguments*, together with the
identifications `generator U = A` and `generator V = B`, rather than being
manufactured internally from `isSelfAdjoint_generator`.  That is deliberate: the
consumer has a given `hA : IsSelfAdjoint A` and works with projections of `A`,
and `isSelfAdjoint_generator U` proves a different proposition — equal only
across `generator U = A`.  Since `specProjection` takes the proof as an
argument, manufacturing it here would push a dependent rewrite through every
projection, domain membership and cut operator at the call site.  Taking it as a
hypothesis does the transport once, here. -/
theorem sylvester_block_identity
    (U : TauCeti.OneParameterUnitaryGroup E) (V : TauCeti.OneParameterUnitaryGroup F)
    (b : HilbertBasis ι ℂ F)
    {A : E →ₗ.[ℂ] E} {Bop : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint Bop)
    (hUA : generator U = A) (hVB : generator V = Bop)
    {SA SB : Set ℝ} (hSA : MeasurableSet SA) (hSB : MeasurableSet SB)
    {MA lam rA : ℝ} (hbndA : ∀ s ∈ SA, |s| ≤ MA) (hrA : 0 ≤ rA)
    (hcrA : ∀ s ∈ SA, |s - lam| ≤ rA)
    {MB alp rB : ℝ} (hbndB : ∀ s ∈ SB, |s| ≤ MB) (hrB : 0 ≤ rB)
    (hcrB : ∀ s ∈ SB, |s - alp| ≤ rB)
    (z : (generator (sylvesterGroup U V b)).domain)
    (hZP : (TauCeti.LinearPMap.specProjection hA SA hSA).comp
        (ofLp b (z : lp (fun _ : ι => E) 2)) = ofLp b (z : lp (fun _ : ι => E) 2))
    (hZQ : (ofLp b (z : lp (fun _ : ι => E) 2)).comp
        (TauCeti.LinearPMap.specProjection hB SB hSB)
        = ofLp b (z : lp (fun _ : ι => E) 2)) :
    ofLp b (generator (sylvesterGroup U V b) z)
        - ((lam : ℂ) - (alp : ℂ)) • ofLp b (z : lp (fun _ : ι => E) 2)
      = (TauCeti.LinearPMap.specCutOp hA SA hSA hrA hcrA).comp
          (ofLp b (z : lp (fun _ : ι => E) 2))
        - (ofLp b (z : lp (fun _ : ι => E) 2)).comp
          (TauCeti.LinearPMap.specCutOp hB SB hSB hrB hcrB) := by
  set Z := ofLp b (z : lp (fun _ : ι => E) 2) with hZ
  set P := TauCeti.LinearPMap.specProjection hA SA hSA with hP
  set Q := TauCeti.LinearPMap.specProjection hB SB hSB with hQ
  have hdomV : (generator V).domain = Bop.domain := congrArg LinearPMap.domain hVB
  have hdense : Dense ((generator V).domain : Set F) := by
    rw [hdomV]; exact hB.dense_domain
  refine ContinuousLinearMap.ext_on (R₁ := ℂ) (s := ((generator V).domain : Set F))
    (by rwa [Submodule.span_eq]) ?_
  intro x hx
  have hx' : x ∈ Bop.domain := (le_of_eq hdomV) hx
  obtain ⟨hmem, heq⟩ := generator_sylvesterGroup_apply U V b z ⟨x, hx⟩
  -- the left factor
  have hZx : Z x ∈ TauCeti.LinearPMap.specRange hA SA hSA := by
    rw [TauCeti.LinearPMap.mem_specRange_iff]
    have := congrArg (fun T : F →L[ℂ] E => T x) hZP
    simpa [hP] using this
  have hZxdom : Z x ∈ A.domain :=
    TauCeti.LinearPMap.mem_domain_of_mem_specRange_of_bounded hA SA hSA hbndA hZx
  have hleft : TauCeti.LinearPMap.specCutOp hA SA hSA hrA hcrA (Z x)
      = A ⟨Z x, hZxdom⟩ - (lam : ℂ) • Z x :=
    TauCeti.LinearPMap.specCutOp_apply hA SA hSA hbndA hrA hcrA hZx hZxdom
  -- transport the generator values across the identifications
  have hUval : generator U ⟨Z x, hmem⟩ = A ⟨Z x, hZxdom⟩ :=
    (LinearPMap.ext_iff.mp hUA).2 (x := Z x) (hf := hmem) (hg := hZxdom)
  have hVval : generator V ⟨x, hx⟩ = Bop ⟨x, hx'⟩ :=
    (LinearPMap.ext_iff.mp hVB).2 (x := x) (hf := hx) (hg := hx')
  -- the right factor, valid at every vector
  obtain ⟨hQx, hright⟩ :=
    TauCeti.LinearPMap.specProjection_apply_sub_smul hB SB hSB hbndB hrB hcrB x
  have hQint : Bop ⟨Q x, TauCeti.LinearPMap.specProjection_mem_domain hB SB hSB ⟨x, hx'⟩⟩
      = Q (Bop ⟨x, hx'⟩) :=
    TauCeti.LinearPMap.specProjection_apply_domain hB SB hSB ⟨x, hx'⟩
  have hZQx : ∀ y : F, Z (Q y) = Z y := by
    intro y
    have := congrArg (fun T : F →L[ℂ] E => T y) hZQ
    simpa [hQ] using this
  -- assemble
  have heq' : (ofLp b (generator (sylvesterGroup U V b) z)) x
      = A ⟨Z x, hZxdom⟩ - Z (Bop ⟨x, hx'⟩) := by
    rw [← heq, hUval, hVval]
  have hcut : TauCeti.LinearPMap.specCutOp hB SB hSB hrB hcrB x
      = Bop ⟨Q x, hQx⟩ - (alp : ℂ) • Q x := hright.symm
  have hBQ : Z (Bop ⟨Q x, hQx⟩) = Z (Bop ⟨x, hx'⟩) := by
    rw [show (⟨Q x, hQx⟩ : Bop.domain)
        = ⟨Q x, TauCeti.LinearPMap.specProjection_mem_domain hB SB hSB ⟨x, hx'⟩⟩ from rfl,
      hQint, hZQx]
  simp only [sub_apply, ContinuousLinearMap.comp_apply, smul_apply, hleft, heq', hcut,
    map_sub, map_smul, hBQ, hZQx]
  module

end HilbertSchmidt
end TauCeti
