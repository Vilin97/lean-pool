/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.BoundedSelfAdjointSpectralProjection
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.BoundedFromSpectrum
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.PartialMap.RealSpectrum
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-! # Self Adjoint Borel Calculus -/

open TauCeti.DavisKahan.Sylvester

/-!
# Bounded Borel calculus for bounded self-adjoint operators

`TauCeti.BorelCalculus` supplies the real-line bounded Borel functional
calculus of a normal operator, indexed along a measurable relabelling of its
spectrum; for a self-adjoint operator that relabelling is the real part.  This
module wraps it for a bounded self-adjoint `A : H →L[ℂ] H` with symbols defined
on all of `ℝ`, which is the form the Sylvester finite-step argument consumes.

The one extra layer is the fact that symbols need only be bounded on the actual
spectrum; we obtain it by zero-extending the symbol off the spectrum.  The
bounded-on-spectrum hypothesis is explicit: measurability alone does not imply
boundedness, even on a compact set.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open MeasureTheory Set Filter
open scoped InnerProductSpace BigOperators

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- The bounded symbol, pulled back to the spectrum, is admissible. -/
theorem isBddMeasurable_pullback (A : H →L[ℂ] H)
    (f : ℝ → ℂ) (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x : ℝ, ‖f x‖ ≤ C) :
    TauCeti.BorelCalculus.IsBddMeasurable
      (fun w : spectrum ℂ A => f (TauCeti.BorelCalculus.reCoord w)) := by
  obtain ⟨C, hC⟩ := hfb
  exact ⟨hf.comp TauCeti.BorelCalculus.measurable_reCoord, max 0 C, le_max_left 0 C,
    fun w => le_trans (hC _) (le_max_right 0 C)⟩

/-- Complex-valued globally bounded Borel calculus of a bounded self-adjoint
map: the native Borel calculus of the (normal) operator, with the symbol pulled
back along the real part of the spectrum. -/
noncomputable def boundedSelfAdjointBorelCalculusC
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (f : ℝ → ℂ) (hf : Measurable f)
    (hfb : ∃ C : ℝ, ∀ x : ℝ, ‖f x‖ ≤ C) : H →L[ℂ] H :=
  TauCeti.BorelCalculus.borelCalculus
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA).isStarNormal
    (isBddMeasurable_pullback A f hf hfb)

/-- Two symbols agreeing on the real spectrum give the same calculus. -/
theorem boundedSelfAdjointBorelCalculusC_congr_on_spectrum'
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    {f g : ℝ → ℂ}
    (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hg : Measurable g) (hgb : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C)
    (hfg : ∀ x ∈ realSpectrum A, f x = g x) :
    boundedSelfAdjointBorelCalculusC A hA f hf hfb =
      boundedSelfAdjointBorelCalculusC A hA g hg hgb := by
  refine TauCeti.BorelCalculus.borelCalculus_congr_ae _ _ _ fun η =>
    Filter.Eventually.of_forall fun w => ?_
  refine hfg _ ?_
  change ((TauCeti.BorelCalculus.reCoord w : ℝ) : ℂ) ∈ spectrum ℂ A
  rw [coe_reCoord A hA w]
  exact w.2

/-- The operator norm of the calculus is controlled by a global symbol bound. -/
theorem norm_boundedSelfAdjointBorelCalculusC_le'
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (f : ℝ → ℂ) (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x ∈ realSpectrum A, ‖f x‖ ≤ C) :
    ‖boundedSelfAdjointBorelCalculusC A hA f hf hfb‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun x => ?_
  refine TauCeti.BorelCalculus.norm_borelCalculus_apply_le _ _ hC0 (fun w => ?_) x
  refine hC _ ?_
  change ((TauCeti.BorelCalculus.reCoord w : ℝ) : ℂ) ∈ spectrum ℂ A
  rw [coe_reCoord A hA w]
  exact w.2

omit [CompleteSpace H] in
/-- Application of the full-domain realization is the original map. -/
theorem toPMap_top_apply
    (A : H →L[ℂ] H) (y : H)
    (hy : y ∈ ((A : H →ₗ[ℂ] H).toPMap ⊤).domain) :
    ((A : H →ₗ[ℂ] H).toPMap ⊤) ⟨y, hy⟩ = A y := rfl

omit [CompleteSpace H] in
/-- The resolvent set of the full-domain realization is exactly the
invertibility locus of `A - z` in the bounded operator algebra. -/
theorem mem_resolventSet_toPMap_top_iff
    (A : H →L[ℂ] H) (z : ℂ) :
    z ∈ TauCeti.LinearPMap.resolventSet ((A : H →ₗ[ℂ] H).toPMap ⊤) ↔
      IsUnit (A - z • (1 : H →L[ℂ] H)) := by
  -- The canonical resolvent core already provides the bounded bridge, to Mathlib's
  -- `resolventSet`, i.e. to `IsUnit (z • 1 - A)`.  This statement is the `A - z`
  -- orientation, which differs from it by a sign, and `IsUnit` is sign-blind.
  rw [TauCeti.LinearPMap.mem_resolventSet_toPMap_top_iff, spectrum.mem_resolventSet_iff,
    Algebra.algebraMap_eq_smul_one,
    show z • (1 : H →L[ℂ] H) - A = -(A - z • (1 : H →L[ℂ] H)) by abel,
    IsUnit.neg_iff]

omit [CompleteSpace H] in
/-- The real spectrum of the bounded map agrees with the `LinearPMap` spectrum
of its full-domain realization. -/
theorem realSpectrum_eq_toPMap_top_spectrum
    (A : H →L[ℂ] H) :
    realSpectrum A =
      Complex.ofReal ⁻¹'
        TauCeti.LinearPMap.spectrum ((A : H →ₗ[ℂ] H).toPMap ⊤) := by
  ext r
  change (r : ℂ) ∈ spectrum ℂ A ↔ (r : ℂ) ∉ TauCeti.LinearPMap.resolventSet _
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one,
    ← IsUnit.neg_iff, neg_sub, mem_resolventSet_toPMap_top_iff A (r : ℂ)]

/-- The real spectrum of a bounded self-adjoint operator is closed. -/
theorem isClosed_realSpectrum_boundedSelfAdjoint
    (A : H →L[ℂ] H) (_hA : A.IsSymmetric) :
    IsClosed (realSpectrum A) := by
  have hpre : realSpectrum A = (fun r : ℝ => (r : ℂ)) ⁻¹' spectrum ℂ A := rfl
  rw [hpre]
  exact (spectrum.isClosed A).preimage Complex.continuous_ofReal

/-- The real spectrum is measurable. -/
theorem measurableSet_realSpectrum_boundedSelfAdjoint
    (A : H →L[ℂ] H) (hA : A.IsSymmetric) :
    MeasurableSet (realSpectrum A) :=
  (isClosed_realSpectrum_boundedSelfAdjoint A hA).measurableSet

/-- Restrict a real symbol to the actual spectrum and coerce it to `ℂ`. -/
noncomputable def spectrumRestrictedSymbol
    (A : H →L[ℂ] H) (f : ℝ → ℝ) : ℝ → ℂ :=
  Set.indicator (realSpectrum A) fun x => (f x : ℂ)

/-- Measurability of the spectrum-restricted symbol. -/
theorem measurable_spectrumRestrictedSymbol
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (f : ℝ → ℝ) (hf : Measurable f) :
    Measurable (spectrumRestrictedSymbol A f) := by
  exact Complex.measurable_ofReal.comp hf |>.indicator
    (measurableSet_realSpectrum_boundedSelfAdjoint A hA)

omit [CompleteSpace H] in
/-- A spectral bound becomes a global bound after zero extension. -/
theorem bounded_spectrumRestrictedSymbol
    (A : H →L[ℂ] H) (f : ℝ → ℝ)
    (hf : BoundedOnSpectrum A f) :
    ∃ C : ℝ, ∀ x : ℝ, ‖spectrumRestrictedSymbol A f x‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := hf
  refine ⟨C, fun x => ?_⟩
  by_cases hx : x ∈ realSpectrum A
  · rw [spectrumRestrictedSymbol, Set.indicator_of_mem hx, Complex.norm_real,
      Real.norm_eq_abs]
    exact hC x hx
  · rw [spectrumRestrictedSymbol, Set.indicator_of_notMem hx, norm_zero]
    exact hC0

/-- Real-valued bounded-on-spectrum Borel calculus.  The explicit boundedness
hypothesis is mathematically necessary. -/
noncomputable def boundedSelfAdjointBorelCalculus
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (f : ℝ → ℝ) (hf : Measurable f) (hfb : BoundedOnSpectrum A f) :
    H →L[ℂ] H :=
  boundedSelfAdjointBorelCalculusC A hA
    (spectrumRestrictedSymbol A f)
    (measurable_spectrumRestrictedSymbol A hA f hf)
    (bounded_spectrumRestrictedSymbol A f hfb)

/-- The scalar indicator symbol is uniformly bounded by one. -/
theorem indicator_one_bdd (s : Set ℝ) :
    ∃ C : ℝ, ∀ x : ℝ, ‖Set.indicator s (fun _ => (1 : ℂ)) x‖ ≤ C := by
  classical
  refine ⟨1, fun x => ?_⟩
  by_cases hx : x ∈ s <;> simp [hx]

/-- The complex calculus of an indicator is the canonical spectral projection. -/
theorem boundedSelfAdjointBorelCalculusC_indicator
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (s : Set ℝ) (hs : MeasurableSet s) :
    boundedSelfAdjointBorelCalculusC A hA
      (Set.indicator s fun _ => (1 : ℂ))
      (measurable_const.indicator hs)
      (indicator_one_bdd s) =
      boundedSelfAdjointSpectralProjection A hA s hs := by
  rfl

/-- Symbols agreeing on the real spectrum have the same bounded calculus. -/
theorem boundedSelfAdjointBorelCalculusC_congr_on_spectrum
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    {f g : ℝ → ℂ}
    (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hg : Measurable g) (hgb : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C)
    (hfg : ∀ x ∈ realSpectrum A, f x = g x) :
    boundedSelfAdjointBorelCalculusC A hA f hf hfb =
      boundedSelfAdjointBorelCalculusC A hA g hg hgb :=
  boundedSelfAdjointBorelCalculusC_congr_on_spectrum' A hA hf hfb hg hgb hfg

/-- The calculus depends only on the symbol. -/
theorem boundedSelfAdjointBorelCalculusC_congr
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    {f g : ℝ → ℂ} (hfg : f = g)
    (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hg : Measurable g) (hgb : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C) :
    boundedSelfAdjointBorelCalculusC A hA f hf hfb =
      boundedSelfAdjointBorelCalculusC A hA g hg hgb :=
  boundedSelfAdjointBorelCalculusC_congr_on_spectrum' A hA hf hfb hg hgb
    (fun x _ => by rw [hfg])

/-- The calculus is additive in the symbol. -/
theorem boundedSelfAdjointBorelCalculusC_add
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    {f g : ℝ → ℂ}
    (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hg : Measurable g) (hgb : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C)
    (hs : Measurable (fun x => f x + g x))
    (hsb : ∃ C : ℝ, ∀ x, ‖f x + g x‖ ≤ C) :
    boundedSelfAdjointBorelCalculusC A hA (fun x => f x + g x) hs hsb =
      boundedSelfAdjointBorelCalculusC A hA f hf hfb +
        boundedSelfAdjointBorelCalculusC A hA g hg hgb := by
  rw [boundedSelfAdjointBorelCalculusC, boundedSelfAdjointBorelCalculusC,
    boundedSelfAdjointBorelCalculusC, ← TauCeti.BorelCalculus.borelCalculus_add]

/-- The calculus is homogeneous in the symbol. -/
theorem boundedSelfAdjointBorelCalculusC_smul
    (A : H →L[ℂ] H) (hA : A.IsSymmetric) (c : ℂ)
    {f : ℝ → ℂ} (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hs : Measurable (fun x => c * f x))
    (hsb : ∃ C : ℝ, ∀ x, ‖c * f x‖ ≤ C) :
    boundedSelfAdjointBorelCalculusC A hA (fun x => c * f x) hs hsb =
      c • boundedSelfAdjointBorelCalculusC A hA f hf hfb := by
  rw [boundedSelfAdjointBorelCalculusC, boundedSelfAdjointBorelCalculusC,
    ← TauCeti.BorelCalculus.borelCalculus_const_smul]

/-- The calculus of the zero symbol vanishes. -/
theorem boundedSelfAdjointBorelCalculusC_zero
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (hm : Measurable (fun _ : ℝ => (0 : ℂ)))
    (hb : ∃ C : ℝ, ∀ x, ‖(fun _ : ℝ => (0 : ℂ)) x‖ ≤ C) :
    boundedSelfAdjointBorelCalculusC A hA (fun _ => (0 : ℂ)) hm hb = 0 := by
  rw [← norm_le_zero_iff]
  exact norm_boundedSelfAdjointBorelCalculusC_le' A hA _ hm hb le_rfl (fun _ _ => by simp)

/-- Operator norm is bounded by a global pointwise symbol bound. -/
theorem norm_boundedSelfAdjointBorelCalculusC_le
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (f : ℝ → ℂ) (hf : Measurable f)
    (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    ‖boundedSelfAdjointBorelCalculusC A hA f hf hfb‖ ≤ C :=
  norm_boundedSelfAdjointBorelCalculusC_le' A hA f hf hfb
    (le_trans (norm_nonneg (f 0)) (hC 0)) (fun x _ => hC x)

/-- A spectrum-only pointwise bound controls a calculus difference. -/
theorem boundedSelfAdjointBorelCalculusC_norm_sub_le
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    {f g : ℝ → ℂ}
    (hf : Measurable f) (hfb : ∃ Cf : ℝ, ∀ x, ‖f x‖ ≤ Cf)
    (hg : Measurable g) (hgb : ∃ Cg : ℝ, ∀ x, ‖g x‖ ≤ Cg)
    {C : ℝ} (hC0 : 0 ≤ C)
    (h : ∀ x ∈ realSpectrum A, ‖f x - g x‖ ≤ C) :
    ‖boundedSelfAdjointBorelCalculusC A hA f hf hfb -
      boundedSelfAdjointBorelCalculusC A hA g hg hgb‖ ≤ C := by
  have hd : Measurable (fun x => f x - g x) := hf.sub hg
  have hdb : ∃ D : ℝ, ∀ x, ‖f x - g x‖ ≤ D := by
    obtain ⟨Cf, hCf⟩ := hfb
    obtain ⟨Cg, hCg⟩ := hgb
    exact ⟨Cf + Cg, fun x => (norm_sub_le _ _).trans (add_le_add (hCf x) (hCg x))⟩
  have hsub : boundedSelfAdjointBorelCalculusC A hA f hf hfb -
      boundedSelfAdjointBorelCalculusC A hA g hg hgb =
      boundedSelfAdjointBorelCalculusC A hA (fun x => f x - g x) hd hdb := by
    rw [boundedSelfAdjointBorelCalculusC, boundedSelfAdjointBorelCalculusC,
      boundedSelfAdjointBorelCalculusC]
    have hgneg : TauCeti.BorelCalculus.borelCalculus
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA).isStarNormal
        ((isBddMeasurable_pullback A g hg hgb).const_smul (-1 : ℂ))
        = -TauCeti.BorelCalculus.borelCalculus
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA).isStarNormal
            (isBddMeasurable_pullback A g hg hgb) := by
      rw [TauCeti.BorelCalculus.borelCalculus_const_smul
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA).isStarNormal (-1 : ℂ)
        (isBddMeasurable_pullback A g hg hgb)]
      module
    rw [sub_eq_add_neg, ← hgneg, ← TauCeti.BorelCalculus.borelCalculus_add]
    refine TauCeti.BorelCalculus.borelCalculus_congr_ae _ _ _ fun η =>
      Filter.Eventually.of_forall fun w => ?_
    change f _ + -1 * g _ = f _ - g _
    ring
  rw [hsub]
  refine norm_boundedSelfAdjointBorelCalculusC_le' A hA _ hd hdb hC0 h

/-- A globally bounded cut-off of the identity symbol. -/
noncomputable def boundedIdentitySymbol (A : H →L[ℂ] H) : ℝ → ℂ :=
  Set.indicator (Set.Icc (-‖A‖) ‖A‖) fun x => (x : ℂ)

omit [CompleteSpace H] in
/-- The cut-off identity symbol is measurable. -/
theorem measurable_boundedIdentitySymbol (A : H →L[ℂ] H) :
    Measurable (boundedIdentitySymbol A) := by
  exact Complex.measurable_ofReal.indicator measurableSet_Icc

omit [CompleteSpace H] in
/-- The cut-off identity symbol is globally bounded by `‖A‖`. -/
theorem bounded_boundedIdentitySymbol (A : H →L[ℂ] H) :
    ∃ C : ℝ, ∀ x, ‖boundedIdentitySymbol A x‖ ≤ C := by
  refine ⟨‖A‖, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (-‖A‖) ‖A‖
  · rw [boundedIdentitySymbol, Set.indicator_of_mem hx, Complex.norm_real,
      Real.norm_eq_abs]
    exact abs_le.mpr hx
  · rw [boundedIdentitySymbol, Set.indicator_of_notMem hx, norm_zero]
    exact norm_nonneg A

/-- Every real spectral value of a bounded operator lies in the norm interval. -/
theorem realSpectrum_subset_norm_Icc [Nontrivial H]
    (A : H →L[ℂ] H) : realSpectrum A ⊆ Set.Icc (-‖A‖) ‖A‖ := by
  intro x hx
  change (x : ℂ) ∈ spectrum ℂ A at hx
  have hnorm : ‖(x : ℂ)‖ ≤ ‖A‖ := spectrum.norm_le_norm_of_mem hx
  have habs : |x| ≤ ‖A‖ := by simpa using hnorm
  exact abs_le.mp habs

/-- The cut-off identity agrees with the identity on the real spectrum. -/
theorem boundedIdentitySymbol_eq [Nontrivial H]
    (A : H →L[ℂ] H) {x : ℝ} (hx : x ∈ realSpectrum A) :
    boundedIdentitySymbol A x = (x : ℂ) := by
  rw [boundedIdentitySymbol, Set.indicator_of_mem (realSpectrum_subset_norm_Icc A hx)]

/-- The bounded calculus of the cut-off identity is the original operator. -/
theorem boundedSelfAdjointBorelCalculusC_id [Nontrivial H]
    (A : H →L[ℂ] H) (hA : A.IsSymmetric) :
    boundedSelfAdjointBorelCalculusC A hA (boundedIdentitySymbol A)
      (measurable_boundedIdentitySymbol A)
      (bounded_boundedIdentitySymbol A) = A := by
  set X : C(spectrum ℂ A, ℂ) := (ContinuousMap.id ℂ).restrict (spectrum ℂ A) with hX
  have hXb : TauCeti.BorelCalculus.IsBddMeasurable (fun w => X w) :=
    TauCeti.BorelCalculus.IsBddMeasurable.of_continuous X
  have hstep : boundedSelfAdjointBorelCalculusC A hA (boundedIdentitySymbol A)
      (measurable_boundedIdentitySymbol A) (bounded_boundedIdentitySymbol A)
      = TauCeti.BorelCalculus.borelCalculus
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA).isStarNormal hXb := by
    refine TauCeti.BorelCalculus.borelCalculus_congr_ae _ _ _ fun η =>
      Filter.Eventually.of_forall fun w => ?_
    have hmem : TauCeti.BorelCalculus.reCoord w ∈ realSpectrum A := by
      change ((TauCeti.BorelCalculus.reCoord w : ℝ) : ℂ) ∈ spectrum ℂ A
      rw [coe_reCoord A hA w]
      exact w.2
    change boundedIdentitySymbol A (TauCeti.BorelCalculus.reCoord w) = X w
    rw [boundedIdentitySymbol_eq A hmem]
    exact coe_reCoord A hA w
  rw [hstep, TauCeti.BorelCalculus.borelCalculus_of_continuous, hX, cfcHom_id]

/-- The real identity symbol is bounded on the real spectrum by the operator
norm. -/
theorem identity_boundedOnSpectrum [Nontrivial H]
    (A : H →L[ℂ] H) : BoundedOnSpectrum A (fun x => x) := by
  refine ⟨‖A‖, norm_nonneg A, fun x hx => ?_⟩
  exact abs_le.mpr (realSpectrum_subset_norm_Icc A hx)

/-- Spectrum-only sup control for the real-valued calculus. -/
theorem boundedSelfAdjointBorelCalculus_norm_sub_le
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfb : BoundedOnSpectrum A f) (hgb : BoundedOnSpectrum A g)
    {C : ℝ} (hC0 : 0 ≤ C)
    (h : ∀ x ∈ realSpectrum A, |f x - g x| ≤ C) :
    ‖boundedSelfAdjointBorelCalculus A hA f hf hfb -
      boundedSelfAdjointBorelCalculus A hA g hg hgb‖ ≤ C := by
  apply boundedSelfAdjointBorelCalculusC_norm_sub_le A hA
  · exact hC0
  · intro x hx
    simp only [spectrumRestrictedSymbol, Set.indicator_of_mem hx]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact h x hx

/-- The real Borel calculus of the identity is the original operator. -/
theorem boundedSelfAdjointBorelCalculus_id [Nontrivial H]
    (A : H →L[ℂ] H) (hA : A.IsSymmetric) :
    boundedSelfAdjointBorelCalculus A hA (fun x => x) measurable_id
      (identity_boundedOnSpectrum A) = A := by
  have hcongr : boundedSelfAdjointBorelCalculusC A hA
      (spectrumRestrictedSymbol A fun x => x)
      (measurable_spectrumRestrictedSymbol A hA _ measurable_id)
      (bounded_spectrumRestrictedSymbol A _ (identity_boundedOnSpectrum A)) =
      boundedSelfAdjointBorelCalculusC A hA (boundedIdentitySymbol A)
        (measurable_boundedIdentitySymbol A)
        (bounded_boundedIdentitySymbol A) := by
    apply boundedSelfAdjointBorelCalculusC_congr_on_spectrum A hA
    intro x hx
    rw [spectrumRestrictedSymbol, Set.indicator_of_mem hx,
      boundedIdentitySymbol_eq A hx]
  exact hcongr.trans (boundedSelfAdjointBorelCalculusC_id A hA)

end
end DavisKahanExt
end TauCeti
