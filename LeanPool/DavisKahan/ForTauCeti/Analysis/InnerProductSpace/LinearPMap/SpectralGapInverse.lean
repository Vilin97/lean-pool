/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralSupport

/-!
# Inverting a self-adjoint operator across a vector spectral gap

If the diagonal measure of `ξ` gives no mass to `(-δ, δ)` — a *vector* spectral
gap — then `ξ` is in the range of `A`, and the preimage has norm at most
`δ⁻¹ ‖ξ‖`.

The construction is the Borel calculus of the **cut-off reciprocal**

```
gapSymbol δ s = if δ ≤ |s| then s⁻¹ else 0
```

which is bounded by `δ⁻¹` everywhere, so the norm bound is immediate from
`norm_borelCalculus_apply_le` and needs no spectral theory at all.  The
substance is the other half: `s · gapSymbol δ s = 1` wherever `δ ≤ |s|`, and the
vector gap says the diagonal measure lives exactly there — so multiplying by the
coordinate recovers `ξ`.

## Why this is not stated for Hilbert–Schmidt operators

It is the engine of the Davis–Kahan square-norm Sylvester estimate, where `A` is
the Sylvester operator `Z ↦ A Z - Z B` on the Hilbert–Schmidt class and the gap
is the pairwise spectral separation.  But nothing in it is about
Hilbert–Schmidt: it is a statement about *any* self-adjoint operator and *any*
vector whose diagonal measure avoids a neighbourhood of zero.  Stating it
generically is what makes the sharp constant `δ⁻¹` reusable — and the sharp
constant is the whole point, since the Fourier/semigroup route to the same
estimate yields `π/(2δ)`.

## Provenance

The donor is `Spectra.QuantumMechanics.SpectralTheory.spectralGapSolution`
(`SpectralTheory/Calculus/SpectralGapInverse.lean`), and the *symbol* is its
idea: Spectra also inverts by cutting off the reciprocal.  What differs is the
setting — Spectra runs it through the group calculus of a one-parameter unitary
group, this runs it through the native Cayley-transform Borel calculus, so no
Stone theorem is involved.
-/

public section

open scoped InnerProductSpace
open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti
namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section GapSymbol

/-- The cut-off reciprocal: `s⁻¹` where `|s| ≥ δ`, and `0` elsewhere. -/
noncomputable def gapSymbol (δ : ℝ) (s : ℝ) : ℂ :=
  if δ ≤ |s| then ((s : ℂ))⁻¹ else 0

/-- The cut-off reciprocal symbol is measurable. -/
theorem measurable_gapSymbol (δ : ℝ) : Measurable (gapSymbol δ) := by
  unfold gapSymbol
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_le measurable_const measurable_norm
  · exact (Complex.measurable_ofReal).inv

/-- The cut-off reciprocal is bounded by `δ⁻¹`. -/
theorem norm_gapSymbol_le {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    ‖gapSymbol δ s‖ ≤ δ⁻¹ := by
  unfold gapSymbol
  split_ifs with hs
  · have hs0 : (0 : ℝ) < |s| := lt_of_lt_of_le hδ hs
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs]
    exact inv_anti₀ hδ hs
  · simpa using inv_nonneg.mpr hδ.le

/-- **The defining identity of the cut-off reciprocal**: it inverts the
coordinate exactly where the cut-off is inactive. -/
theorem coord_mul_gapSymbol {δ : ℝ} {s : ℝ} (hs : δ ≤ |s|) (hδ : 0 < δ) :
    (s : ℂ) * gapSymbol δ s = 1 := by
  have hs0 : (s : ℂ) ≠ 0 := by
    have : (0 : ℝ) < |s| := lt_of_lt_of_le hδ hs
    exact_mod_cast abs_pos.mp this
  rw [gapSymbol, ite_eq_left hs, mul_inv_cancel₀ hs0]

end GapSymbol

section GapInverse

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-- The cut-off reciprocal pulled back to the spectrum of the Cayley transform,
which is where the Borel calculus of an unbounded self-adjoint operator lives. -/
noncomputable def gapSymbolCayley (δ : ℝ) :
    _root_.spectrum ℂ (cayley hA) → ℂ :=
  fun w => gapSymbol δ (cayleyInv hA w)

/-- The gap symbol, pulled back along the Cayley relabelling, is admissible for the bounded Borel
calculus.  Boundedness is where the gap is used: off `(-δ, δ)` the reciprocal is bounded by
`δ⁻¹`. -/
theorem isBddMeasurable_gapSymbolCayley {δ : ℝ} (hδ : 0 < δ) :
    BorelCalculus.IsBddMeasurable (gapSymbolCayley hA δ) :=
  ⟨(measurable_gapSymbol δ).comp (measurable_cayleyInv hA), δ⁻¹,
    by positivity, fun w => norm_gapSymbol_le hδ _⟩

/-- **The bounded inverse across a spectral gap.**  On the part of the spectrum
at distance `δ` from the origin this is `A⁻¹`; elsewhere it is zero. -/
noncomputable def gapInverse {δ : ℝ} (hδ : 0 < δ) : H →L[ℂ] H :=
  BorelCalculus.borelCalculus (isStarNormal_cayley hA)
    (isBddMeasurable_gapSymbolCayley hA hδ)

/-- **The sharp constant.**  It is `δ⁻¹` and it is immediate: the symbol is
bounded by `δ⁻¹` pointwise, so no spectral theory enters the estimate at all.

This is the constant the Fourier/semigroup route cannot reach — that one yields
`π/(2δ)`, the exact `L¹` mass of the Haagerup--Zsidó kernel. -/
theorem norm_gapInverse_apply_le {δ : ℝ} (hδ : 0 < δ) (ξ : H) :
    ‖gapInverse hA hδ ξ‖ ≤ δ⁻¹ * ‖ξ‖ :=
  BorelCalculus.norm_borelCalculus_apply_le _ _ (by positivity)
    (fun w => norm_gapSymbol_le hδ _) ξ

/-- **The sharp bound `‖𝒮⁻¹‖ ≤ δ⁻¹`.**  It is immediate rather than deep: the symbol is bounded by
`δ⁻¹` pointwise, so no spectral theory enters the estimate itself. -/
theorem norm_gapInverse_le {δ : ℝ} (hδ : 0 < δ) :
    ‖gapInverse hA hδ‖ ≤ δ⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (norm_gapInverse_apply_le hA hδ)

/-- **The domain lemma, in general symbol form.**  If multiplying the symbol by
`κ + i` leaves it bounded, then the Borel calculus of `h` lands in `dom A`, and
`A + i` acts there by multiplying the symbol.

`SpectralMeasure.specProjection_apply_sub_smul` is the indicator instance of
this; a later cleanup can collapse the two. -/
theorem borelCalculus_mem_domain_of_coord_mul
    {h : _root_.spectrum ℂ (cayley hA) → ℂ}
    (hh : BorelCalculus.IsBddMeasurable h)
    (hq : BorelCalculus.IsBddMeasurable
      (fun w => ((cayleyInv hA w : ℂ) + Complex.I) * h w)) (ξ : H) :
    ∃ hmem : BorelCalculus.borelCalculus (isStarNormal_cayley hA) hh ξ ∈ A.domain,
      A ⟨BorelCalculus.borelCalculus (isStarNormal_cayley hA) hh ξ, hmem⟩
          + Complex.I • BorelCalculus.borelCalculus (isStarNormal_cayley hA) hh ξ
        = BorelCalculus.borelCalculus (isStarNormal_cayley hA) hq ξ := by
  set hU := isStarNormal_cayley hA with hhU
  set hni := negI_mem_resolventSet hA with hhni
  set κ := cayleyInv hA with hκ
  -- The canonical resolvent's symbol is `(w - 1)/(2i)`; the symbol that inverts `κ + i`
  -- pointwise is its negative, so the calculus below is `-R(-i)`.
  set gcan : C(_root_.spectrum ℂ (cayley hA), ℂ) :=
    (2 * Complex.I)⁻¹ • (cayleyCoord hA - 1) with hgcan
  have hgcb : BorelCalculus.IsBddMeasurable (fun w => gcan w) :=
    BorelCalculus.IsBddMeasurable.of_continuous gcan
  have hRcan : resolvent A (-Complex.I) = BorelCalculus.borelCalculus hU hgcb :=
    resolvent_negI_eq_borelCalculus hA hgcb
  set gsym : C(_root_.spectrum ℂ (cayley hA), ℂ) :=
    (2 * Complex.I)⁻¹ • (1 - cayleyCoord hA) with hgsym
  have hgb : BorelCalculus.IsBddMeasurable (fun w => gsym w) :=
    BorelCalculus.IsBddMeasurable.of_continuous gsym
  have hgbEq : BorelCalculus.borelCalculus hU hgb
      = BorelCalculus.borelCalculus hU (hgcb.const_smul (-1)) :=
    BorelCalculus.borelCalculus_congr_ae hU _ _ fun η =>
      Filter.Eventually.of_forall fun w => by simp [hgsym, hgcan]; ring
  have hRg : BorelCalculus.borelCalculus hU hgb = -(resolvent A (-Complex.I)) := by
    rw [hgbEq, BorelCalculus.borelCalculus_const_smul hU (-1) hgcb, ← hRcan]
    module
  -- `gsym · ((κ + i) h) = h` off the Cayley singularity, which is null
  have hprod : BorelCalculus.borelCalculus hU (hgb.mul hq)
      = BorelCalculus.borelCalculus hU hh := by
    refine borelCalculus_congr_of_ne_one hA _ _ fun w hw1 => ?_
    have hgval : gsym w = (2 * Complex.I)⁻¹ * (1 - (w : ℂ)) := by simp [hgsym]
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change gsym w * (((κ w : ℂ) + Complex.I) * h w) = h w
    rw [hgval, ← mul_assoc,
      inv_two_I_mul_one_sub_mul_cayleyInv_add_I hA hw1, one_mul]
  set T := BorelCalculus.borelCalculus hU hq with hT
  have hPy : resolvent A (-Complex.I) (T ξ)
      = -(BorelCalculus.borelCalculus hU hh ξ) := by
    have hmul := congrArg (fun L : H →L[ℂ] H => L ξ)
      ((BorelCalculus.borelCalculus_mul hU hgb hq).symm.trans hprod)
    simp only [_root_.mul_apply_eq_comp] at hmul
    rw [← hmul, hRg]
    simp only [_root_.neg_apply, neg_neg]
    rw [hT]
  have hmemneg : -(BorelCalculus.borelCalculus hU hh ξ) ∈ A.domain := by
    rw [← hPy]; exact resolvent_mem_domain hni (T ξ)
  have hmem : BorelCalculus.borelCalculus hU hh ξ ∈ A.domain := by
    simpa using neg_mem hmemneg
  refine ⟨hmem, ?_⟩
  have hsolve := smul_sub_apply_resolvent hni (T ξ)
  have hcongr : (⟨resolvent A (-Complex.I) (T ξ), resolvent_mem_domain hni (T ξ)⟩ : A.domain)
      = -(⟨BorelCalculus.borelCalculus hU hh ξ, hmem⟩ : A.domain) := Subtype.ext hPy
  rw [hcongr, _root_.LinearPMap.map_neg, hPy] at hsolve
  linear_combination (norm := module) hsolve

/-! ## The vector spectral gap -/

/-- The set of spectral points at distance at least `δ` from the origin. -/
def gapSet (δ : ℝ) : Set ℝ := {s : ℝ | δ ≤ |s|}

/-- The gap set is measurable, so it admits a spectral projection. -/
theorem measurableSet_gapSet (δ : ℝ) : MeasurableSet (gapSet δ) :=
  (isClosed_le continuous_const continuous_abs).measurableSet

/-- The complement of the gap set is the open interval `(-δ, δ)`. -/
theorem compl_gapSet (δ : ℝ) : (gapSet δ)ᶜ = Set.Ioo (-δ) δ := by
  ext s
  simp only [gapSet, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, Set.mem_Ioo,
    abs_lt]

/-- **A vector spectral gap**: the diagonal measure of `ξ` gives no mass to
`(-δ, δ)`.  This is the hypothesis under which `ξ` is in the range of `A` with
the sharp bound. -/
@[expose]
def HasVectorSpectralGap (δ : ℝ) (ξ : H) : Prop :=
  (spectralPVM hA).diag ξ (Set.Ioo (-δ) δ) = 0

/-- Under a vector gap the spectral projection of the gap set fixes `ξ`. -/
@[simp]
theorem specProjection_gapSet_apply {δ : ℝ} {ξ : H}
    (hgap : HasVectorSpectralGap hA δ ξ) :
    specProjection hA (gapSet δ) (measurableSet_gapSet δ) ξ = ξ := by
  have hcompl : (spectralPVM hA).diag ξ (gapSet δ)ᶜ = 0 := by
    rw [compl_gapSet]; exact hgap
  have hzero : specProjection hA (gapSet δ)ᶜ (measurableSet_gapSet δ).compl ξ = 0 := by
    have hq := (spectralPVM hA).norm_sq_proj_apply (gapSet δ)ᶜ
      (measurableSet_gapSet δ).compl ξ
    rw [hcompl] at hq
    simp only [ENNReal.toReal_zero] at hq
    rw [← specProjection_def] at hq
    have hz : ‖specProjection hA (gapSet δ)ᶜ (measurableSet_gapSet δ).compl ξ‖ = 0 :=
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hq
    exact norm_eq_zero.mp hz
  have hc := (spectralPVM hA).proj_compl (gapSet δ) (measurableSet_gapSet δ)
  have happ := congrArg (fun T : H →L[ℂ] H => T ξ) hc
  simp only [sub_apply, ContinuousLinearMap.id_apply] at happ
  rw [show (spectralPVM hA).proj (gapSet δ)ᶜ (measurableSet_gapSet δ).compl
      = specProjection hA (gapSet δ)ᶜ (measurableSet_gapSet δ).compl from by
        rw [specProjection_def], hzero] at happ
  rw [show specProjection hA (gapSet δ) (measurableSet_gapSet δ)
      = (spectralPVM hA).proj (gapSet δ) (measurableSet_gapSet δ) from by rw [specProjection_def]]
  linear_combination (norm := module) happ

/-! ## The endpoint -/

/-- Multiplying the cut-off reciprocal by `κ` gives the indicator of the gap
set: that is the whole content of "cut-off reciprocal". -/
theorem coord_mul_gapSymbolCayley {δ : ℝ} (hδ : 0 < δ) (w : _root_.spectrum ℂ (cayley hA)) :
    ((cayleyInv hA w : ℂ)) * gapSymbolCayley hA δ w
      = (cayleyInv hA ⁻¹' gapSet δ).indicator (fun _ => (1 : ℂ)) w := by
  classical
  by_cases hw : w ∈ cayleyInv hA ⁻¹' gapSet δ
  · have hmem : δ ≤ |cayleyInv hA w| := hw
    rw [Set.indicator_of_mem hw, gapSymbolCayley, coord_mul_gapSymbol hmem hδ]
  · have hnot : ¬ δ ≤ |cayleyInv hA w| := hw
    rw [Set.indicator_of_notMem hw, gapSymbolCayley, gapSymbol, ite_eq_right hnot, mul_zero]

/-- **Inversion across a vector spectral gap.**  If the diagonal measure of `ξ`
avoids `(-δ, δ)` then `ξ` is in the range of `A`, and the preimage
`gapInverse hA hδ ξ` has norm at most `δ⁻¹ ‖ξ‖`.

This is the engine of the Davis--Kahan square-norm Sylvester estimate, and the
constant is the sharp one. -/
theorem apply_gapInverse {δ : ℝ} (hδ : 0 < δ) {ξ : H}
    (hgap : HasVectorSpectralGap hA δ ξ) :
    ∃ hmem : gapInverse hA hδ ξ ∈ A.domain,
      A ⟨gapInverse hA hδ ξ, hmem⟩ = ξ := by
  classical
  set hU := isStarNormal_cayley hA with hhU
  set κ := cayleyInv hA with hκ
  set g := gapSymbolCayley hA δ with hg
  have hgb : BorelCalculus.IsBddMeasurable g := isBddMeasurable_gapSymbolCayley hA hδ
  set S : Set (_root_.spectrum ℂ (cayley hA)) := κ ⁻¹' gapSet δ with hS
  have hSm : MeasurableSet S := measurable_cayleyInv hA (measurableSet_gapSet δ)
  have hindb : BorelCalculus.IsBddMeasurable (S.indicator (fun _ => (1 : ℂ))) :=
    BorelCalculus.isBddMeasurable_indicator (a := cayley hA) hSm
  -- `(κ + i) g = 1_S + i g`
  have hsplit : (fun w => ((κ w : ℂ) + Complex.I) * g w)
      = fun w => S.indicator (fun _ => (1 : ℂ)) w + Complex.I * g w := by
    funext w
    rw [add_mul, coord_mul_gapSymbolCayley hA hδ w]
  have hq : BorelCalculus.IsBddMeasurable
      (fun w => ((κ w : ℂ) + Complex.I) * g w) := by
    rw [hsplit]
    exact hindb.add (hgb.const_smul Complex.I)
  obtain ⟨hmem, hval⟩ := borelCalculus_mem_domain_of_coord_mul hA hgb hq ξ
  refine ⟨hmem, ?_⟩
  -- the right-hand side splits into the projection plus `i` times the inverse
  have hrhs : BorelCalculus.borelCalculus hU hq ξ
      = specProjection hA (gapSet δ) (measurableSet_gapSet δ) ξ
        + Complex.I • BorelCalculus.borelCalculus hU hgb ξ := by
    have hcongr : BorelCalculus.borelCalculus hU hq
        = BorelCalculus.borelCalculus hU (hindb.add (hgb.const_smul Complex.I)) := by
      refine BorelCalculus.borelCalculus_congr_ae hU _ _ fun η =>
        Filter.Eventually.of_forall fun w => ?_
      exact congrFun hsplit w
    rw [hcongr, BorelCalculus.borelCalculus_add hU hindb (hgb.const_smul Complex.I),
      BorelCalculus.borelCalculus_const_smul hU Complex.I hgb,
      specProjection_eq_borelCalculus]
    rfl
  rw [hrhs, specProjection_gapSet_apply hA hgap] at hval
  -- `gapInverse` and its unfolding are the same term but different atoms to
  -- `module`, so the identity is proved in the unfolded form and transported by
  -- definitional equality.
  have hfinal : A ⟨BorelCalculus.borelCalculus hU hgb ξ, hmem⟩ = ξ := by
    linear_combination (norm := module) hval
  exact hfinal

end GapInverse

end LinearPMap
end TauCeti
