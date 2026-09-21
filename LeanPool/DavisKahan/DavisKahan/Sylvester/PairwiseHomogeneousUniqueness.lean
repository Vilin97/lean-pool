/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Sylvester.PairwiseSpectrumGap
import LeanPool.DavisKahan.DavisKahan.Sylvester.ClosedSylvesterEquation
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Rosenblum

/-!
# Homogeneous Sylvester uniqueness at arbitrary spectral separation

A domain-aware closed Sylvester equation says exactly that its solution
intertwines the two operators, and Rosenblum's theorem then forces a bounded
intertwiner of disjoint spectra to vanish.  Unlike the older uniqueness lemma,
no interval/exterior or ordered half-line geometry is required.

Until 2026-07-29 this ran through Spectra: the Sylvester equation was converted
into `GeneratorIntertwines` between the two Yosida groups, and the donor's
`generatorIntertwiner_eq_zero_of_disjoint_spectrum` closed it.  The generator
layer was pure overhead — the intertwining relation *is* the Sylvester equation
— so the conversion is gone and the native
`TauCeti.LinearPMap.eq_zero_of_intertwines_of_disjoint_spectrum` is applied
directly.
-/

namespace TauCeti
namespace DavisKahan
namespace Sylvester

open scoped InnerProductSpace

noncomputable section

universe v

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A bounded homogeneous Sylvester solution for raw self-adjoint partial maps
vanishes whenever their spectra are disjoint. -/
theorem Sylvester_homogeneous_eq_zero_of_disjoint_spectrum
    {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X : F →L[ℂ] E}
    (hdisj : Disjoint
      (TauCeti.LinearPMap.spectrum A)
      (TauCeti.LinearPMap.spectrum B))
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X 0) :
    X = 0 := by
  refine TauCeti.LinearPMap.eq_zero_of_intertwines_of_disjoint_spectrum hA hB
    (fun y => hEq.mapsTo_domain y) (fun y => ?_) hdisj
  simpa using sub_eq_zero.mp (hEq.equation y)

/-- Positive pairwise spectral distance gives homogeneous uniqueness for raw
self-adjoint partial maps. -/
theorem Sylvester_homogeneous_eq_zero_of_pairwiseSpectrumGap
    {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X : F →L[ℂ] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : LinearPMap.PairwiseSpectrumGap A B δ)
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X 0) :
    X = 0 := by
  exact Sylvester_homogeneous_eq_zero_of_disjoint_spectrum
    hA hB (hgap.disjoint hδ) hEq

/-- **Sylvester--Rosenblum uniqueness for raw self-adjoint partial maps.**  Two bounded
solutions of the same Sylvester equation coincide as soon as the two spectra are
*disjoint*; no quantitative gap is needed.

The gap version below is this statement composed with
`PairwiseSpectrumGap.disjoint`, so a positive separation buys nothing here — it is
needed only where a *bound* on the solution is wanted. -/
theorem Sylvester_solution_unique_of_disjoint_spectrum
    {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X Y C : F →L[ℂ] E}
    (hdisj : Disjoint
      (TauCeti.LinearPMap.spectrum A)
      (TauCeti.LinearPMap.spectrum B))
    (hX : TauCeti.LinearPMap.SylvesterEquation A B X C)
    (hY : TauCeti.LinearPMap.SylvesterEquation A B Y C) :
    X = Y := by
  have hhom : TauCeti.LinearPMap.SylvesterEquation A B (X - Y) 0 := by
    simpa using hX.sub hY
  exact sub_eq_zero.mp
    (Sylvester_homogeneous_eq_zero_of_disjoint_spectrum hA hB hdisj hhom)

/-- Two bounded raw partial-map Sylvester solutions coincide under positive
pairwise spectral separation.  A corollary of
`Sylvester_solution_unique_of_disjoint_spectrum`, which is the sharp form. -/
theorem Sylvester_solution_unique_of_pairwiseSpectrumGap
    {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X Y C : F →L[ℂ] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : LinearPMap.PairwiseSpectrumGap A B δ)
    (hX : TauCeti.LinearPMap.SylvesterEquation A B X C)
    (hY : TauCeti.LinearPMap.SylvesterEquation A B Y C) :
    X = Y :=
  Sylvester_solution_unique_of_disjoint_spectrum hA hB (hgap.disjoint hδ) hX hY

/-- A bounded homogeneous closed Sylvester solution vanishes whenever the two
self-adjoint spectra are disjoint. -/
theorem closedSylvester_homogeneous_eq_zero_of_disjoint_spectrum
    {A : E →ₗ.[ℂ] E}
    {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X : F →L[ℂ] E}
    (hdisj : Disjoint
      (TauCeti.LinearPMap.spectrum A)
      (TauCeti.LinearPMap.spectrum B))
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X 0) :
    X = 0 := by
  exact Sylvester_homogeneous_eq_zero_of_disjoint_spectrum
    hA hB hdisj hEq

/-- Positive pairwise spectral distance implies homogeneous uniqueness. -/
theorem closedSylvester_homogeneous_eq_zero_of_pairwiseSpectrumGap
    {A : E →ₗ.[ℂ] E}
    {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X : F →L[ℂ] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : PairwiseSpectrumGap A B δ)
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X 0) :
    X = 0 := by
  exact Sylvester_homogeneous_eq_zero_of_pairwiseSpectrumGap
    hA hB hδ hgap hEq

/-- **Sylvester--Rosenblum uniqueness for closed operators.**  Two bounded solutions of the
same closed Sylvester equation coincide as soon as the two spectra are *disjoint*. -/
theorem closedSylvester_solution_unique_of_disjoint_spectrum
    {A : E →ₗ.[ℂ] E}
    {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X Y C : F →L[ℂ] E}
    (hdisj : Disjoint
      (TauCeti.LinearPMap.spectrum A)
      (TauCeti.LinearPMap.spectrum B))
    (hX : TauCeti.LinearPMap.SylvesterEquation A B X C)
    (hY : TauCeti.LinearPMap.SylvesterEquation A B Y C) :
    X = Y :=
  Sylvester_solution_unique_of_disjoint_spectrum hA hB hdisj hX hY

/-- Two bounded solutions of the same closed Sylvester equation coincide under
positive pairwise spectral separation.  A corollary of
`closedSylvester_solution_unique_of_disjoint_spectrum`, which is the sharp form. -/
theorem closedSylvester_solution_unique_of_pairwiseSpectrumGap
    {A : E →ₗ.[ℂ] E}
    {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X Y C : F →L[ℂ] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : PairwiseSpectrumGap A B δ)
    (hX : TauCeti.LinearPMap.SylvesterEquation A B X C)
    (hY : TauCeti.LinearPMap.SylvesterEquation A B Y C) :
    X = Y :=
  closedSylvester_solution_unique_of_disjoint_spectrum hA hB (hgap.disjoint hδ) hX hY

end

end Sylvester
end DavisKahan
end TauCeti
