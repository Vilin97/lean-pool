/-
Copyright (c) 2026 Jon Crall, Edward Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.Released under Apache 2.0 license as described in the file LICENSE.Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtTensor
import LeanPool.DavisKahan.DavisKahan.Sylvester.HomogeneousUniqueness
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Generator
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.StoneUniqueness
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralGapInverse

/-! # Hilbert Schmidt Defect First -/

open TauCeti.DavisKahan.Sylvester

/-!
# Defect-first reduction for the square-norm Sylvester theorem

This file contains the non-circular core of Davis--Kahan Theorem 6.2.
Starting from a Hilbert--Schmidt defect `C`, represent `C` by its column family.
If the Sylvester flow has vector spectral gap `delta` at that family, the
bounded reciprocal functional calculus produces a `z0` with

`generator z0 = c` and `‖z0‖ <= delta⁻¹ ‖c‖`.

The generator equation turns `z0` into a bounded operator `X0` satisfying the
original closed Sylvester equation.  Operator-norm homogeneous uniqueness then
identifies every supplied bounded solution `X` with `X0`.  In particular, no
Hilbert--Schmidt membership of `X` is assumed before it is proved.

## Provenance

The mathematics is unchanged; only the model is.  The Hilbert--Schmidt space
used to be `vendor/Spectra`'s Hilbert tensor product, and the four spectral
inputs came from Spectra's Born-rule stack.  Both are now native:

* the space is `lp` of columns (`ForTauCeti/…/HilbertSchmidtLp.lean`);
* the flow is `TauCeti.HilbertSchmidt.sylvesterGroup`, whose generator is
  self-adjoint by Stone's theorem (`…/OneParameterUnitaryGroup/Stone.lean`) and
  satisfies the Sylvester equation by `generator_sylvesterGroup_apply`;
* the gap inverse is `TauCeti.LinearPMap.gapInverse`, with the sharp `δ⁻¹`;
* `generator (genToGroup hA) = A` is Stone's uniqueness half
  (`…/LinearPMap/StoneUniqueness.lean`), which is what lets a statement about
  the *flow* be read as a statement about `A` and `B`.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace
open TauCeti.HilbertSchmidt
open TauCeti.OneParameterUnitaryGroup (generator)

noncomputable section

universe v

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

private theorem hasClosedSylvesterEquation_of_generator
    {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (z : (generator (sylvesterGroup (TauCeti.LinearPMap.genToGroup hA)
      (TauCeti.LinearPMap.genToGroup hB) (hSBasis F))).domain) :
    TauCeti.LinearPMap.SylvesterEquation A B
      (ofLp (hSBasis F) (z : lp (fun _ : HSIndex F => E) 2))
      (ofLp (hSBasis F) (generator (sylvesterGroup (TauCeti.LinearPMap.genToGroup hA)
        (TauCeti.LinearPMap.genToGroup hB) (hSBasis F)) z)) := by
  have hAU : generator (TauCeti.LinearPMap.genToGroup hA) = A :=
    TauCeti.LinearPMap.generator_genToGroup hA
  have hBV : generator (TauCeti.LinearPMap.genToGroup hB) = B :=
    TauCeti.LinearPMap.generator_genToGroup hB
  have hdomA : (generator (TauCeti.LinearPMap.genToGroup hA)).domain = A.domain :=
    congrArg LinearPMap.domain hAU
  have hdomB : (generator (TauCeti.LinearPMap.genToGroup hB)).domain = B.domain :=
    congrArg LinearPMap.domain hBV
  refine ⟨?_, ?_⟩
  · intro x
    obtain ⟨hmem, -⟩ :=
      generator_sylvesterGroup_apply (TauCeti.LinearPMap.genToGroup hA)
        (TauCeti.LinearPMap.genToGroup hB) (hSBasis F) z
        ⟨(x : F), (le_of_eq hdomB.symm) x.property⟩
    exact (le_of_eq hdomA) hmem
  · intro x
    obtain ⟨hmem, heq⟩ :=
      generator_sylvesterGroup_apply (TauCeti.LinearPMap.genToGroup hA)
        (TauCeti.LinearPMap.genToGroup hB) (hSBasis F) z
        ⟨(x : F), (le_of_eq hdomB.symm) x.property⟩
    have hAapply := (LinearPMap.ext_iff.mp hAU).2
      (x := ofLp (hSBasis F) (z : lp (fun _ : HSIndex F => E) 2) (x : F))
      (hf := hmem) (hg := (le_of_eq hdomA) hmem)
    have hBapply := (LinearPMap.ext_iff.mp hBV).2
      (x := (x : F))
      (hf := (le_of_eq hdomB.symm) x.property) (hg := x.property)
    rw [← hAapply, ← hBapply]
    exact heq

/-- Defect-first square-norm estimate, reduced to the vector spectral gap of
the Hilbert--Schmidt defect. -/
theorem hilbertSchmidt_sylvester_defectFirst
    {A : E →ₗ.[ℂ] E}
    {B : F →ₗ.[ℂ] F}
    {X C : F →L[ℂ] E}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {δ : ℝ} (hδ : 0 < δ)
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X C)
    (hunique : ∀ {Y : F →L[ℂ] E},
      TauCeti.LinearPMap.SylvesterEquation A B Y 0 → Y = 0)
    (hC : approximationNumberEnergy C ≠ ⊤)
    (hCgap : TauCeti.LinearPMap.HasVectorSpectralGap
      (isSelfAdjoint_generator_sylvesterGroup (TauCeti.LinearPMap.genToGroup hA)
        (TauCeti.LinearPMap.genToGroup hB) (hSBasis F))
      δ (hilbertSchmidtTensor C hC)) :
    approximationNumberEnergy X ≠ ⊤ ∧
      δ * ContinuousLinearMap.hilbertSchmidtNorm X ≤ ContinuousLinearMap.hilbertSchmidtNorm C := by
  set hS := isSelfAdjoint_generator_sylvesterGroup (TauCeti.LinearPMap.genToGroup hA)
    (TauCeti.LinearPMap.genToGroup hB) (hSBasis F) with hSdef
  set c := hilbertSchmidtTensor C hC with hc
  obtain ⟨hz0, hgen⟩ := TauCeti.LinearPMap.apply_gapInverse hS hδ hCgap
  set z0 := TauCeti.LinearPMap.gapInverse hS hδ c with hz0def
  set X0 := ofLp (hSBasis F) z0 with hX0
  have hEq0raw := hasClosedSylvesterEquation_of_generator hA hB ⟨z0, hz0⟩
  have hcOp : ofLp (hSBasis F) c = C := toOperator_hilbertSchmidtTensor C hC
  have hEq0 : TauCeti.LinearPMap.SylvesterEquation A B X0 C := by
    have h := hEq0raw
    rw [hgen, hcOp] at h
    exact h
  have hhom : TauCeti.LinearPMap.SylvesterEquation A B (X - X0) 0 := by
    simpa using hEq.sub hEq0
  have hXX0 : X = X0 := sub_eq_zero.mp (hunique hhom)
  have hX0mem : approximationNumberEnergy X0 ≠ ⊤ := approximationNumberEnergy_ne_top_toOperator z0
  refine ⟨hXX0 ▸ hX0mem, ?_⟩
  rw [hXX0, hX0, hilbertSchmidtNorm_toOperator]
  calc
    δ * ‖z0‖ ≤ δ * (δ⁻¹ * ‖c‖) :=
      mul_le_mul_of_nonneg_left
        (TauCeti.LinearPMap.norm_gapInverse_apply_le hS hδ c) hδ.le
    _ = ‖c‖ := by field_simp
    _ = ContinuousLinearMap.hilbertSchmidtNorm C := norm_hilbertSchmidtTensor C hC

end

end ExactSinTheta
end DavisKahan
end TauCeti
