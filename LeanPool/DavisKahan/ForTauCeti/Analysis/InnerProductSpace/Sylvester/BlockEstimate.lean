/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.BlockIdentity
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Block

/-!
# The per-block Sylvester estimate

On a spectral block, `𝒮` is within `rA + rB` of the scalar `λ - α`:

`‖𝒮 W - (λ - α) W‖ ≤ (rA + rB) ‖W‖`.

This is `sylvester_block_identity` measured.  The identity writes the difference
as `(A - λ)|block ∘ Z - Z ∘ (B - α)|block` with both factors bounded; the two
Hilbert–Schmidt ideal properties then bound each term by the corresponding block
radius times `‖W‖`.

The one thing worth noticing is that the bound is relative to the **block's own**
norm, not to the norm of the vector it was cut from.  That is what makes the
blocks reassemble: `enorm_ge_of_blocks` needs a bound of exactly this shape, and
a bound in terms of `‖z‖` would be useless.

## Sources

The per-block estimate is the Bhatia--Davis--McIntosh bound applied blockwise; see
`prose/distilled_literature/BhatiaDavisMcIntosh1983_spectral_subspaces_sylvester.tex`.
The reassembly is
`ForTauCeti/Analysis/InnerProductSpace/BlockLowerBound.lean`, which follows nothing
in particular.

## Provenance

*New.*

Moved from
`ForTauCeti/Analysis/InnerProductSpace/SylvesterBlockEstimate.lean` to
`ForTauCeti/Analysis/InnerProductSpace/Sylvester/BlockEstimate.lean`.  The `Sylvester/`
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

/-- Composing a block on one side only, as an instance of `blockCLM`. -/
theorem norm_blockFun_one_right (b : HilbertBasis ι ℂ F) (P : E →L[ℂ] E)
    (f : lp (fun _ : ι => E) 2) :
    ‖blockFun b P (1 : F →L[ℂ] F) f‖ ≤ ‖P‖ * ‖f‖ := by
  calc ‖blockFun b P (1 : F →L[ℂ] F) f‖ ≤ ‖P‖ * ‖(1 : F →L[ℂ] F)‖ * ‖f‖ :=
        norm_blockFun_le b P (1 : F →L[ℂ] F) f
    _ ≤ ‖P‖ * 1 * ‖f‖ := by gcongr; exact ContinuousLinearMap.norm_id_le
    _ = ‖P‖ * ‖f‖ := by ring

/-- One-sided bound with the identity on the left: `‖1 · Z · Q‖ ≤ ‖Q‖ ‖Z‖`.  The mirror of
`norm_blockFun_one_right`; both exist because the Sylvester flow uses each side separately. -/
theorem norm_blockFun_one_left (b : HilbertBasis ι ℂ F) (Q : F →L[ℂ] F)
    (f : lp (fun _ : ι => E) 2) :
    ‖blockFun b (1 : E →L[ℂ] E) Q f‖ ≤ ‖Q‖ * ‖f‖ := by
  calc ‖blockFun b (1 : E →L[ℂ] E) Q f‖ ≤ ‖(1 : E →L[ℂ] E)‖ * ‖Q‖ * ‖f‖ :=
        norm_blockFun_le b (1 : E →L[ℂ] E) Q f
    _ ≤ 1 * ‖Q‖ * ‖f‖ := by gcongr; exact ContinuousLinearMap.norm_id_le
    _ = ‖Q‖ * ‖f‖ := by ring

/-- **The per-block Sylvester estimate.**  On a spectral block the Sylvester
operator is within `rA + rB` of the scalar `λ - α`, relative to the block's own
norm. -/
theorem norm_sylvester_block_sub_smul_le
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
    ‖generator (sylvesterGroup U V b) z
        - ((lam : ℂ) - (alp : ℂ)) • (z : lp (fun _ : ι => E) 2)‖
      ≤ (rA + rB) * ‖(z : lp (fun _ : ι => E) 2)‖ := by
  set Z := ofLp b (z : lp (fun _ : ι => E) 2) with hZdef
  set cutA := TauCeti.LinearPMap.specCutOp hA SA hSA hrA hcrA with hcutA
  set cutB := TauCeti.LinearPMap.specCutOp hB SB hSB hrB hcrB with hcutB
  -- the difference is the difference of two one-sided blocks
  have hsplit : generator (sylvesterGroup U V b) z
      - ((lam : ℂ) - (alp : ℂ)) • (z : lp (fun _ : ι => E) 2)
      = blockFun b cutA (1 : F →L[ℂ] F) (z : lp (fun _ : ι => E) 2)
        - blockFun b (1 : E →L[ℂ] E) cutB (z : lp (fun _ : ι => E) 2) := by
    refine ofLp_injective b ?_
    rw [ofLp_sub, ofLp_sub, ofLp_smul, ofLp_blockFun, ofLp_blockFun]
    have hid := sylvester_block_identity U V b hA hB hUA hVB hSA hSB hbndA hrA hcrA
      hbndB hrB hcrB z hZP hZQ
    rw [← hZdef, ← hcutA, ← hcutB] at hid
    rw [hid]
    ext x
    simp [hZdef]
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  have h1 := norm_blockFun_one_right b cutA (z : lp (fun _ : ι => E) 2)
  have h2 := norm_blockFun_one_left b cutB (z : lp (fun _ : ι => E) 2)
  have hA' : ‖cutA‖ ≤ rA := TauCeti.LinearPMap.norm_specCutOp_le hA SA hSA hrA hcrA
  have hB' : ‖cutB‖ ≤ rB := TauCeti.LinearPMap.norm_specCutOp_le hB SB hSB hrB hcrB
  nlinarith [norm_nonneg ((z : lp (fun _ : ι => E) 2)), norm_nonneg cutA, norm_nonneg cutB]

end HilbertSchmidt
end TauCeti
