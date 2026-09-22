/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.MultiplicityModel
public import LeanPool.DavisKahan.ForTauCeti.MeasureTheory.LpRealPart
public import LeanPool.DavisKahan.ForTauCeti.MeasureTheory.LpStar

/-!
# When the real part of a multiplicity model is invariant

A `TauCeti.MultiplicityDatum ℂ` presents multiplication by the (truncated) spectral coordinate
on `L²` of a measure living on `ℂ × ℕ`.  The `star`-fixed part of that `L²` space is the real
`L²` space (`TauCeti.starFixedLpEquivRealLp`), so a real model can only be read off the complex
one if the model operator maps the `star`-fixed part into itself.

**It does not, in general.**  Multiplication by a symbol `w` satisfies `star (w * F) = conj w * F`
on a `star`-fixed `F`, so `w * F` is `star`-fixed exactly where `conj w = w` or `F = 0`.  The main
theorem below is the resulting **biconditional**:

`TauCeti.MultiplicityDatum.StarFixedInvariant D ↔ D.base {z | z.im ≠ 0} = 0`.

Both directions are genuine.  The forward direction is *not* vacuous: it is proved by feeding the
operator the indicator of the non-real part of the zeroth slice, which is an honest element of
`L²` because `MultiplicityDatum.base_finite` makes that set have finite measure, and which is
`star`-fixed because it is real valued.

## Why this is a hypothesis and not a field

`base_supported_real` is deliberately **not** added to `TauCeti.MultiplicityDatum`.  The datum's
one existing support field, `base_supported_level_zero`, is there because without it a datum is
not determined even in principle -- mass outside `level 0` contributes to no summand of
`measure`, so two data differing only there present the *same* operator.  Reality of the base
measure has no such character: a datum whose base charges the non-real points is perfectly well
determined and presents a perfectly good operator.  It is a property of the *operator being
self-adjoint*, not a well-formedness condition on the presentation.

Making it a field would also be an outright regression.  The datum's *general* construction site
is `TauCeti.BorelCalculus.exists_hasMultiplicityModel`, complex Hahn--Hellinger for an arbitrary
bounded **normal** operator.  A normal operator has complex spectrum, so that construction could
not discharge such a field at all, and adding it would make the theorem unprovable.  The
`star`-equivariant refinement below, `TauCeti.BorelCalculus.exists_hasMultiplicityModel_star`,
*does* deliver reality of the base -- but only because it additionally assumes the operator
self-adjoint, and it delivers it as a **conclusion**, which is exactly the point: it is a property
of the operator, not a well-formedness condition on presentations in general.

## Main results

* `TauCeti.MultiplicityDatum.base_eq_zero_iff_measure_fst_preimage_eq_zero`: the base measure and
  the model measure have the same null sets of spectral values.  This is where
  `base_supported_level_zero` is consumed.
* `TauCeti.star_eq_self_iff_of_coeFn_mul`: a class presented as a bounded symbol times a
  `star`-fixed class is `star`-fixed exactly where the symbol is real or the class vanishes.
* `TauCeti.MultiplicityDatum.StarFixedInvariant`: the property that the model operator preserves
  the `star`-fixed part.
* `TauCeti.MultiplicityDatum.starFixedInvariant_iff_base_im_eq_zero`: **the D1 verdict.**
* `TauCeti.MultiplicityDatum.mapsTo_starFixedSubmodule`: the submodule phrasing of the useful
  direction.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib and `ForTauCeti`.
-/

public section

open MeasureTheory

open scoped ENNReal ComplexConjugate

namespace TauCeti

section BaseNull

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The model measure of a set of spectral values is the sum, over the levels, of the base
measure of that set inside each level. -/
theorem MultiplicityDatum.measure_fst_preimage (D : MultiplicityDatum 𝕜) {S : Set ℂ}
    (hS : MeasurableSet S) :
    D.measure (Prod.fst ⁻¹' S) = ∑' k, D.base (S ∩ D.level k) := by
  rw [MultiplicityDatum.measure_def, sliceSum_apply _ (hS.preimage measurable_fst)]
  refine tsum_congr fun k => ?_
  have hfib : {z : ℂ | (z, k) ∈ Prod.fst ⁻¹' S} = S := rfl
  rw [hfib, Measure.restrict_apply hS]

/-- The model measure of the zeroth slice over a set of spectral values is the base measure of
that set inside `level 0` -- and so is finite, because the base measure is. -/
theorem MultiplicityDatum.measure_fst_preimage_inter_slice_zero (D : MultiplicityDatum 𝕜)
    {S : Set ℂ} (hS : MeasurableSet S) :
    D.measure (Prod.fst ⁻¹' S ∩ slice 0) = D.base (S ∩ D.level 0) := by
  rw [MultiplicityDatum.measure_def,
    sliceSum_apply _ ((hS.preimage measurable_fst).inter (measurableSet_slice 0)),
    tsum_eq_single 0 ?_]
  · have hfib : {z : ℂ | (z, (0 : ℕ)) ∈ Prod.fst ⁻¹' S ∩ slice 0} = S := by
      ext z
      simp [mem_slice]
    rw [hfib, Measure.restrict_apply hS]
  · intro m hm
    have hfib : {z : ℂ | (z, m) ∈ Prod.fst ⁻¹' S ∩ slice 0} = (∅ : Set ℂ) := by
      ext z
      simp [mem_slice, hm]
    rw [hfib, measure_empty]

/-- **The base measure and the model measure have the same null sets of spectral values.**

The `←` direction is the one with content, and it is exactly where
`MultiplicityDatum.base_supported_level_zero` is consumed: without that field the base measure
could charge `S` entirely outside `level 0`, where the model measure never looks. -/
theorem MultiplicityDatum.base_eq_zero_iff_measure_fst_preimage_eq_zero (D : MultiplicityDatum 𝕜)
    {S : Set ℂ} (hS : MeasurableSet S) :
    D.base S = 0 ↔ D.measure (Prod.fst ⁻¹' S) = 0 := by
  rw [D.measure_fst_preimage hS, ENNReal.tsum_eq_zero]
  constructor
  · exact fun h k => measure_mono_null Set.inter_subset_left h
  · intro h
    have hsub : S ⊆ (S ∩ D.level 0) ∪ (D.level 0)ᶜ := by
      intro z hz
      by_cases hz0 : z ∈ D.level 0
      · exact Or.inl ⟨hz, hz0⟩
      · exact Or.inr hz0
    exact measure_mono_null hsub (measure_union_null (h 0) D.base_supported_level_zero)

/-- A base-null set of spectral values is avoided by almost every point of the model. -/
theorem MultiplicityDatum.ae_fst_notMem (D : MultiplicityDatum 𝕜) {S : Set ℂ}
    (hS : MeasurableSet S) (h : D.base S = 0) : ∀ᵐ q ∂D.measure, q.1 ∉ S := by
  rw [ae_iff]
  have hset : {q : ℂ × ℕ | ¬ q.1 ∉ S} = Prod.fst ⁻¹' S := by
    ext q
    simp
  rw [hset]
  exact (D.base_eq_zero_iff_measure_fst_preimage_eq_zero hS).mp h

end BaseNull

section StarMultiplication

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}

/-- A `star`-fixed `Lᵖ` class is almost everywhere fixed by pointwise conjugation.  This is
`ae_ofReal_re_eq_of_star_eq_self` in the phrasing multiplication arguments want. -/
theorem ae_conj_eq_self_of_star_eq_self {F : Lp ℂ p μ} (hF : star F = F) :
    ∀ᵐ x ∂μ, conj ((F : α → ℂ) x) = (F : α → ℂ) x := by
  filter_upwards [ae_ofReal_re_eq_of_star_eq_self hF] with x hx
  exact RCLike.conj_eq_iff_re.mpr hx

/-- **A class presented as a bounded symbol times a `star`-fixed class is `star`-fixed exactly
where the symbol is real or the class vanishes.**

This is the pointwise heart of the D1 verdict: `star` conjugates the symbol and leaves the
`star`-fixed factor alone, so the two products agree iff the conjugated symbol does.  It is
stated for an arbitrary `G` presented by a pointwise product so that it serves both
`mulLpField` and `MultiplicityDatum.operator`, whose bodies the module system does not
expose. -/
theorem star_eq_self_iff_of_coeFn_mul {g : α → ℂ} {F G : Lp ℂ 2 μ}
    (hG : (G : α → ℂ) =ᵐ[μ] fun x => g x * (F : α → ℂ) x) (hF : star F = F) :
    star G = G ↔ ∀ᵐ x ∂μ, conj (g x) * (F : α → ℂ) x = g x * (F : α → ℂ) x := by
  have hkey : ∀ᵐ x ∂μ, ((star G : Lp ℂ 2 μ) : α → ℂ) x = conj (g x) * (F : α → ℂ) x := by
    filter_upwards [Lp.coeFn_star G, hG, ae_conj_eq_self_of_star_eq_self hF] with x h1 h2 h3
    rw [h1, Pi.star_apply, h2, RCLike.star_def, map_mul, h3]
  constructor
  · intro h
    have hcoe : ((star G : Lp ℂ 2 μ) : α → ℂ) = (G : α → ℂ) :=
      congrArg (fun H : Lp ℂ 2 μ => (H : α → ℂ)) h
    filter_upwards [hkey, hG] with x h1 h2
    calc conj (g x) * (F : α → ℂ) x = ((star G : Lp ℂ 2 μ) : α → ℂ) x := h1.symm
      _ = (G : α → ℂ) x := congrFun hcoe x
      _ = g x * (F : α → ℂ) x := h2
  · intro h
    refine Lp.ext ?_
    filter_upwards [hkey, hG, h] with x h1 h2 h3
    calc ((star G : Lp ℂ 2 μ) : α → ℂ) x = conj (g x) * (F : α → ℂ) x := h1
      _ = g x * (F : α → ℂ) x := h3
      _ = (G : α → ℂ) x := h2.symm

/-- The `mulLpField` specialization of `star_eq_self_iff_of_coeFn_mul`. -/
theorem star_mulLpField_eq_self_iff (ρ : Measure α) {g : α → ℂ} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) {F : Lp ℂ 2 ρ} (hF : star F = F) :
    star (mulLpField ρ hg hgC F) = mulLpField ρ hg hgC F ↔
      ∀ᵐ x ∂ρ, conj (g x) * (F : α → ℂ) x = g x * (F : α → ℂ) x :=
  star_eq_self_iff_of_coeFn_mul (coeFn_mulLpField ρ hg hgC F) hF

end StarMultiplication

section Coord

/-- Inside the ball, reality of the point makes the truncated coordinate real. -/
theorem conj_coordTrunc_of_im_eq_zero {R : ℝ} {z : ℂ} (hzR : ‖z‖ ≤ R) (hz : z.im = 0) :
    conj (coordTrunc R z) = coordTrunc R z := by
  rw [coordTrunc_eq_self hzR]
  exact Complex.conj_eq_iff_im.mpr hz

/-- Inside the ball, where the truncation is inert, reality of the truncated coordinate is
reality of the point. -/
theorem im_eq_zero_of_conj_coordTrunc {R : ℝ} {z : ℂ} (hzR : ‖z‖ ≤ R)
    (h : conj (coordTrunc R z) = coordTrunc R z) : z.im = 0 := by
  rw [coordTrunc_eq_self hzR] at h
  exact Complex.conj_eq_iff_im.mp h

end Coord

section StarFixedInvariance

/-- The set of non-real spectral values is measurable. -/
theorem measurableSet_im_ne_zero : MeasurableSet {z : ℂ | z.im ≠ 0} :=
  (Complex.measurable_im (measurableSet_singleton (0 : ℝ))).compl

/-- **The model operator preserves the `star`-fixed part of its `L²` space.**

Named rather than left inline because both directions of the D1 verdict quantify over it, and
because it is the hypothesis every real-model construction downstream will carry. -/
def MultiplicityDatum.StarFixedInvariant (D : MultiplicityDatum ℂ) : Prop :=
  ∀ F : Lp ℂ 2 D.measure, star F = F → star (D.operator F) = D.operator F

/-- The model operator is pointwise multiplication by the *complex* truncated coordinate; this is
`MultiplicityDatum.coeFn_operator` with the field-valued symbol specialized. -/
theorem MultiplicityDatum.coeFn_operator_complex (D : MultiplicityDatum ℂ)
    (F : Lp ℂ 2 D.measure) :
    (D.operator F : ℂ × ℕ → ℂ) =ᵐ[D.measure]
      fun q => coordTrunc D.bound q.1 * (F : ℂ × ℕ → ℂ) q := by
  simpa only [coordTruncField_complex] using D.coeFn_operator F

/-- The model operator's action on a `star`-fixed class, tested pointwise. -/
theorem MultiplicityDatum.star_operator_eq_self_iff (D : MultiplicityDatum ℂ)
    {F : Lp ℂ 2 D.measure} (hF : star F = F) :
    star (D.operator F) = D.operator F ↔
      ∀ᵐ q ∂D.measure, conj (coordTrunc D.bound q.1) * (F : ℂ × ℕ → ℂ) q
        = coordTrunc D.bound q.1 * (F : ℂ × ℕ → ℂ) q :=
  star_eq_self_iff_of_coeFn_mul (D.coeFn_operator_complex F) hF

/-- A datum carried by the real axis has `star`-invariant real part.  This is the direction the
real Hahn--Hellinger route consumes. -/
theorem MultiplicityDatum.starFixedInvariant_of_base_im_eq_zero {D : MultiplicityDatum ℂ}
    (h : D.base {z : ℂ | z.im ≠ 0} = 0) : D.StarFixedInvariant := by
  intro F hF
  rw [D.star_operator_eq_self_iff hF]
  filter_upwards [D.ae_fst_notMem measurableSet_im_ne_zero h, D.ae_norm_le_bound] with q hq hqb
  have him : (q.1 : ℂ).im = 0 := by simpa using hq
  rw [conj_coordTrunc_of_im_eq_zero hqb him]

/-- **The converse.**  If the model operator preserves the `star`-fixed part then the base measure
is carried by the real axis.

The witness is the indicator of the non-real part of the zeroth slice.  It lies in `L²` because
`MultiplicityDatum.base_finite` makes that set have finite model measure, and it is `star`-fixed
because it is real valued; feeding it to the hypothesis forces the set to be null, and
`base_eq_zero_iff_measure_fst_preimage_eq_zero` converts that back to the base measure. -/
theorem MultiplicityDatum.base_im_eq_zero_of_starFixedInvariant {D : MultiplicityDatum ℂ}
    (h : D.StarFixedInvariant) : D.base {z : ℂ | z.im ≠ 0} = 0 := by
  classical
  set S : Set ℂ := {z : ℂ | z.im ≠ 0} with hSdef
  set T : Set (ℂ × ℕ) := Prod.fst ⁻¹' S ∩ slice 0 with hTdef
  have hSm : MeasurableSet S := measurableSet_im_ne_zero
  have hTm : MeasurableSet T := (hSm.preimage measurable_fst).inter (measurableSet_slice 0)
  have hTval : D.measure T = D.base (S ∩ D.level 0) :=
    D.measure_fst_preimage_inter_slice_zero hSm
  have hTfin : D.measure T ≠ ⊤ := by
    rw [hTval]
    exact (measure_lt_top D.base _).ne
  set F : Lp ℂ 2 D.measure := indicatorConstLp 2 hTm hTfin (1 : ℂ) with hFdef
  have hFcoe : (F : ℂ × ℕ → ℂ) =ᵐ[D.measure] T.indicator fun _ => (1 : ℂ) :=
    indicatorConstLp_coeFn
  have hFstar : star F = F := by
    rw [star_eq_self_iff_ae_im_eq_zero]
    filter_upwards [hFcoe] with q hq
    rw [hq, Set.indicator_apply]
    split_ifs <;> simp
  have hmain := (D.star_operator_eq_self_iff hFstar).mp (h F hFstar)
  have hnull : ∀ᵐ q ∂D.measure, q ∉ T := by
    filter_upwards [hmain, hFcoe, D.ae_norm_le_bound] with q h1 h2 h3
    intro hqT
    have hone : (F : ℂ × ℕ → ℂ) q = 1 := by
      rw [h2, Set.indicator_of_mem hqT]
    rw [hone, mul_one, mul_one] at h1
    exact hqT.1 (im_eq_zero_of_conj_coordTrunc h3 h1)
  have hT0 : D.measure T = 0 := by
    have h' := (ae_iff (μ := D.measure) (p := fun q => q ∉ T)).mp hnull
    have hset : {q : ℂ × ℕ | ¬ q ∉ T} = T := by
      ext q
      simp
    rwa [hset] at h'
  have hbase0 : D.base (S ∩ D.level 0) = 0 := by rw [← hTval, hT0]
  have hsub : S ⊆ (S ∩ D.level 0) ∪ (D.level 0)ᶜ := by
    intro z hz
    by_cases hz0 : z ∈ D.level 0
    · exact Or.inl ⟨hz, hz0⟩
    · exact Or.inr hz0
  exact measure_mono_null hsub (measure_union_null hbase0 D.base_supported_level_zero)

/-- **D1, the verdict.**  The `star`-fixed part of the model `L²` space is invariant under the
model operator **if and only if** the base measure is carried by the real axis.

Neither direction is formal.  The `←` direction is what a real Hahn--Hellinger model needs; the
`→` direction is what says the hypothesis cannot be dropped, since a datum charging any non-real
set of positive base measure already breaks invariance. -/
theorem MultiplicityDatum.starFixedInvariant_iff_base_im_eq_zero (D : MultiplicityDatum ℂ) :
    D.StarFixedInvariant ↔ D.base {z : ℂ | z.im ≠ 0} = 0 :=
  ⟨MultiplicityDatum.base_im_eq_zero_of_starFixedInvariant,
    MultiplicityDatum.starFixedInvariant_of_base_im_eq_zero⟩

/-- The submodule phrasing: for a real-carried datum the model operator maps
`TauCeti.starFixedSubmodule` into itself, which is the form `TauCeti.starFixedLpEquivRealLp`
consumes. -/
theorem MultiplicityDatum.mapsTo_starFixedSubmodule {D : MultiplicityDatum ℂ}
    (h : D.base {z : ℂ | z.im ≠ 0} = 0) :
    ∀ F ∈ starFixedSubmodule ℂ 2 D.measure,
      D.operator F ∈ starFixedSubmodule ℂ 2 D.measure := by
  intro F hF
  rw [mem_starFixedSubmodule] at hF ⊢
  exact MultiplicityDatum.starFixedInvariant_of_base_im_eq_zero h F hF

end StarFixedInvariance

section Compression

variable {α : Type*} [MeasurableSpace α]

/-- **The real-valued multiplication operator is the compression of the complex one to the real
classes -- unconditionally.**

`RCLike.map ℂ ℝ` is `RCLike.reCLM` (`RCLike.map_to_real`), so `coordTruncField ℝ` is the real
part of `coordTrunc`; this lemma is the corresponding statement one level down, for an arbitrary
bounded symbol.  It holds with no reality hypothesis because the real part of `w * r` is
`(re w) * r` whenever `r` is real.

What it does **not** say is that the complex operator *restricts*: the compression is a
restriction exactly when `MultiplicityDatum.StarFixedInvariant` holds, which by
`MultiplicityDatum.starFixedInvariant_iff_base_im_eq_zero` is exactly reality of the base
measure. -/
theorem reLp_mulLpField_ofRealLp (ρ : Measure α) {g : α → ℂ} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) (f : Lp ℝ 2 ρ) :
    reLp (mulLpField ρ hg hgC (ofRealLp f)) =
      mulLpField ρ (𝕜 := ℝ) (Complex.measurable_re.comp hg)
        (fun x => (RCLike.norm_re_le_norm (K := ℂ) (g x)).trans (hgC x)) f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_reLp (mulLpField ρ hg hgC (ofRealLp f)),
    coeFn_mulLpField ρ hg hgC (ofRealLp (K := ℂ) f),
    coeFn_ofRealLp (K := ℂ) f,
    coeFn_mulLpField ρ (𝕜 := ℝ) (Complex.measurable_re.comp hg)
      (fun x => (RCLike.norm_re_le_norm (K := ℂ) (g x)).trans (hgC x)) f] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  simp

end Compression

section RealModel

/-- At a real point inside the ball, the complex symbol times a real value is the coercion of the
real symbol times that value.  This is the pointwise identity behind the compression, isolated so
that the `Lᵖ` argument never has to reason about coercions. -/
theorem coordTruncField_complex_mul_ofReal {R : ℝ} {z : ℂ} (hzR : ‖z‖ ≤ R) (hz : z.im = 0)
    (r : ℝ) : coordTruncField ℂ R z * (r : ℂ) = ((coordTruncField ℝ R z * r : ℝ) : ℂ) := by
  have hre : ((coordTrunc R z).re : ℂ) = coordTrunc R z :=
    Complex.conj_eq_iff_re.mp (conj_coordTrunc_of_im_eq_zero hzR hz)
  simp only [coordTruncField_complex, coordTruncField_real]
  rw [Complex.ofReal_mul, hre]

/-- **On a real-carried datum the model operator restricts to the real classes, and acts there by
the real truncated coordinate.**

This is the equational form of `MultiplicityDatum.mapsTo_starFixedSubmodule`: not merely that the
`star`-fixed part is preserved, but *what the restriction is*.  The reality hypothesis is used
pointwise, through `conj_coordTrunc_of_im_eq_zero`, at almost every point of the model measure --
which is where `MultiplicityDatum.ae_fst_notMem` and `MultiplicityDatum.ae_norm_le_bound` enter. -/
theorem MultiplicityDatum.operator_ofRealLp {D : MultiplicityDatum ℂ}
    (hbase : D.base {z : ℂ | z.im ≠ 0} = 0) (f : Lp ℝ 2 D.measure) :
    D.operator (ofRealLp f) = ofRealLp (mulLpField D.measure
      ((measurable_coordTruncField ℝ D.bound).comp measurable_fst)
      (fun p => norm_coordTruncField_le ℝ D.bound_nonneg p.1) f) := by
  refine Lp.ext ?_
  filter_upwards [D.coeFn_operator (ofRealLp f), coeFn_ofRealLp (K := ℂ) f,
    coeFn_ofRealLp (K := ℂ) (mulLpField D.measure
      ((measurable_coordTruncField ℝ D.bound).comp measurable_fst)
      (fun p => norm_coordTruncField_le ℝ D.bound_nonneg p.1) f),
    coeFn_mulLpField D.measure ((measurable_coordTruncField ℝ D.bound).comp measurable_fst)
      (fun p => norm_coordTruncField_le ℝ D.bound_nonneg p.1) f,
    D.ae_fst_notMem measurableSet_im_ne_zero hbase, D.ae_norm_le_bound] with q h1 h2 h3 h4 h5 h6
  rw [h1, h2, h3, h4]
  simp only [Function.comp_apply]
  exact coordTruncField_complex_mul_ofReal h6 (not_not.mp h5) _

/-- **A real model, read off a `star`-equivariant complex model.**

`E` is presented as a real form of `H`: an `ℝ`-linear isometry `jE` into the fixed set of `cH`,
with a retraction `rE` inverting it there, carrying `T` to `A`.  The model side needs no such
hypothesis-shaped input, because `TauCeti.ofRealLpₗᵢ` and `TauCeti.reLp` *are* the corresponding
data for `star`, by `TauCeti.star_ofRealLp` and `TauCeti.ofRealLp_reLp_of_star_eq_self`.

The retyped datum carries the same base measure and the same level sets
(`MultiplicityDatum.retype_base`, `MultiplicityDatum.retype_level`), so no multiplicity content
is lost or invented in the descent: only the scalar field of the `L²` fibres changes. -/
theorem operatorUnitaryEquiv_retype_real_of_starOperatorUnitaryEquiv {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {cH : H → H} {A : H →L[ℂ] H} {T : E →L[ℝ] E}
    {D : MultiplicityDatum ℂ} (hbase : D.base {z : ℂ | z.im ≠ 0} = 0) (jE : E → H) (rE : H → E)
    (hjEadd : ∀ x y, jE (x + y) = jE x + jE y)
    (hjEsmul : ∀ (c : ℝ) x, jE (c • x) = (c : ℂ) • jE x)
    (hjEnorm : ∀ x, ‖jE x‖ = ‖x‖) (hfixE : ∀ x, cH (jE x) = jE x)
    (hrjE : ∀ y, cH y = y → jE (rE y) = y) (hT : ∀ x, A (jE x) = jE (T x))
    (h : StarOperatorUnitaryEquiv cH star A D.operator) :
    OperatorUnitaryEquiv T (D.retype ℝ).operator := by
  refine operatorUnitaryEquiv_retype_real_operator_of_mulLpField D ?_
  exact operatorUnitaryEquiv_of_starOperatorUnitaryEquiv jE rE hjEadd hjEsmul hjEnorm hfixE
    hrjE hT (fun f => (ofRealLp f : Lp ℂ 2 D.measure)) reLp (fun f g => ofRealLp_add f g)
    (fun c f => ofRealLp_coe_smul c f) (fun f => norm_ofRealLp f) (fun f => star_ofRealLp f)
    (fun _ hG => ofRealLp_reLp_of_star_eq_self hG)
    (fun f => MultiplicityDatum.operator_ofRealLp hbase f) h

/-- **Multiplication by a real-valued symbol restricts to the real classes**, with no reality
hypothesis on the measure at all.

A real symbol commutes with pointwise conjugation outright, which is what lets the *second* half
of the real classification run entirely inside the complex Radon--Nikodym theory and then descend.
Compare `MultiplicityDatum.operator_ofRealLp`, where the symbol is the complex coordinate and the
statement is therefore conditional on the base measure being carried by the real axis. -/
theorem mulLp_ofReal_ofRealLp {α : Type*} [MeasurableSpace α] (ρ : Measure α) {g : α → ℝ}
    (hg : Measurable g) {C : ℝ} (hgC : ∀ x, ‖g x‖ ≤ C)
    (hgC' : ∀ x, ‖((g x : ℝ) : ℂ)‖ ≤ C) (f : Lp ℝ 2 ρ) :
    mulLp ρ (Complex.measurable_ofReal.comp hg) hgC' (ofRealLp f)
      = ofRealLp (mulLpField ρ (𝕜 := ℝ) hg hgC f) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_mulLp ρ (Complex.measurable_ofReal.comp hg) hgC' (ofRealLp f),
    coeFn_ofRealLp (K := ℂ) f, coeFn_ofRealLp (K := ℂ) (mulLpField ρ (𝕜 := ℝ) hg hgC f),
    coeFn_mulLpField ρ (𝕜 := ℝ) hg hgC f] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  simp

/-- **The real converse: real data agreeing up to measure class and null sets present unitarily
equivalent real operators.**

This is `operatorUnitaryEquiv_of_measureEquiv_complex` at real scalars, and it is proved *without*
a real
Radon--Nikodym theory.  The trick is that the real model operator is multiplication by a symbol
that happens to be real valued, so it is the restriction to the real classes of multiplication by
the **same** symbol read in `ℂ` -- and that complex operator is intertwined by the ordinary
complex Radon--Nikodym unitary, which is `star`-equivariant because the Radon--Nikodym density is
a nonnegative real function.  Descending the resulting `TauCeti.StarOperatorUnitaryEquiv` gives
the real statement.

Note what is *not* assumed: the base measures need not be carried by the real axis.  Reality of
the base is what the *forward* direction needs, because there the symbol is the complex
coordinate. -/
theorem operatorUnitaryEquiv_of_measureEquiv_real {D E : MultiplicityDatum ℝ}
    (hbase : MeasureEquiv D.base E.base)
    (hlevel : ∀ k, D.base (symmDiff (D.level k) (E.level k)) = 0) :
    OperatorUnitaryEquiv D.operator E.operator := by
  have hmeas : MeasureEquiv D.measure E.measure :=
    measureEquiv_measure_of_measureEquiv_base hbase hlevel
  set R : ℝ := max D.bound E.bound with hRdef
  have hR0 : (0 : ℝ) ≤ R := le_trans D.bound_nonneg (le_max_left _ _)
  have hgmeas : Measurable (coordTruncField ℝ R ∘ (Prod.fst : ℂ × ℕ → ℂ)) :=
    (measurable_coordTruncField ℝ R).comp measurable_fst
  have hgC : ∀ p : ℂ × ℕ, ‖(coordTruncField ℝ R ∘ (Prod.fst : ℂ × ℕ → ℂ)) p‖
      ≤ ‖RCLike.map ℂ ℝ‖ * R := fun p => norm_coordTruncField_le ℝ hR0 p.1
  have hgC' : ∀ p : ℂ × ℕ,
      ‖(((coordTruncField ℝ R ∘ (Prod.fst : ℂ × ℕ → ℂ)) p : ℝ) : ℂ)‖ ≤ ‖RCLike.map ℂ ℝ‖ * R := by
    intro p
    rw [Complex.norm_real]
    exact hgC p
  rw [MultiplicityDatum.operator_eq_mulLpField_of_le (D := D) hR0 (le_max_left _ _),
    MultiplicityDatum.operator_eq_mulLpField_of_le (D := E) hR0 (le_max_right _ _)]
  have hstar : StarOperatorUnitaryEquiv star star
      (mulLp D.measure (Complex.measurable_ofReal.comp hgmeas) hgC')
      (mulLp E.measure (Complex.measurable_ofReal.comp hgmeas) hgC') :=
    starOperatorUnitaryEquiv_of_intertwines (rnDerivL2Equiv hmeas.1 hmeas.2)
      (fun F => rnDerivL2Equiv_mulLp hmeas.1 hmeas.2
        (Complex.measurable_ofReal.comp hgmeas) hgC' F)
      (fun F => (star_rnDerivL2Equiv hmeas.1 hmeas.2 F).symm)
  exact operatorUnitaryEquiv_of_starOperatorUnitaryEquiv
    (fun f => (ofRealLp f : Lp ℂ 2 D.measure)) reLp ofRealLp_add ofRealLp_coe_smul norm_ofRealLp
    star_ofRealLp (fun _ hG => ofRealLp_reLp_of_star_eq_self hG)
    (fun f => mulLp_ofReal_ofRealLp D.measure hgmeas hgC hgC' f)
    (fun f => (ofRealLp f : Lp ℂ 2 E.measure)) reLp ofRealLp_add ofRealLp_coe_smul norm_ofRealLp
    star_ofRealLp (fun _ hG => ofRealLp_reLp_of_star_eq_self hG)
    (fun f => mulLp_ofReal_ofRealLp E.measure hgmeas hgC hgC' f) hstar

end RealModel

namespace BorelCalculus

section StarModel

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {a : H →L[ℂ] H}

/-- **The `star`-equivariant multiplicity model.**

`TauCeti.BorelCalculus.exists_hasMultiplicityModel` produces a model for an arbitrary bounded
normal operator, but it produces it as a bare `TauCeti.OperatorUnitaryEquiv`, which forgets its
unitary.  A conjugation cannot be pushed through a forgotten unitary, and -- this is the
mathematical point, not a Lean difficulty -- an *arbitrary* intertwiner need not commute with the
conjugations, since the intertwiner is unique only up to the commutant.  So the equivariance has
to be carried along the chain, not recovered at the end.

The cyclic decomposition is taken as a **hypothesis** rather than constructed here.  The complex
construction chooses its cyclic vectors by an arbitrary maximality argument and has no reason to
choose conjugation-fixed ones; the real analogue
`exists_countable_isHilbertSum_lp_diagMeasure_real`, in
`TauCeti.DavisKahan.Experimental.RealSpectralRestriction`,
does, and it lives downstream of this module.  Taking the decomposition as input keeps this
module free of the complexification API and makes the *only* input the equivariance `hstar` of
each cyclic isometry.

Self-adjointness is used for exactly one thing: the spectrum is real, so the base measure of the
resulting datum vanishes off the real axis, which by
`TauCeti.MultiplicityDatum.starFixedInvariant_iff_base_im_eq_zero` is precisely what makes the
`star`-fixed part of the model invariant.  It is delivered as a conclusion rather than assumed. -/
theorem exists_hasMultiplicityModel_star 
    (ha : IsStarNormal a) (hsa : IsSelfAdjoint a) {cH : H → H} (hcH : Continuous cH)
    (hcHadd : ∀ x y, cH (x + y) = cH x + cH y) {ξ : ℕ → H}
    (hsum : IsHilbertSum ℂ (fun n => Lp ℂ 2 (diagMeasure ha (ξ n)))
      (fun n => cyclicIsometry ha (ξ n)))
    (hstar : ∀ (n : ℕ) (F : Lp ℂ 2 (diagMeasure ha (ξ n))),
      cyclicIsometry ha (ξ n) (star F) = cH (cyclicIsometry ha (ξ n) F)) :
    ∃ D : MultiplicityDatum ℂ, D.base {z : ℂ | z.im ≠ 0} = 0 ∧
      StarOperatorUnitaryEquiv cH star a D.operator := by
  classical
  have hR0 : (0 : ℝ) ≤ ‖a‖ * ‖(1 : H →L[ℂ] H)‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hspec : ∀ w : spectrum ℂ a, ‖(w : ℂ)‖ ≤ ‖a‖ * ‖(1 : H →L[ℂ] H)‖ := by
    intro w
    have hw := spectrum.subset_closedBall_norm_mul a w.2
    simpa [Metric.mem_closedBall, dist_zero_right] using hw
  have hmeasSpec : MeasurableSet (spectrum ℂ a) := (spectrum.isCompact a).isClosed.measurableSet
  have hemb : MeasurableEmbedding ((↑) : spectrum ℂ a → ℂ) :=
    MeasurableEmbedding.subtype_coe hmeasSpec
  have hfin : ∀ n, IsFiniteMeasure (Measure.map ((↑) : spectrum ℂ a → ℂ)
      (diagMeasure ha (ξ n))) := fun n => Measure.isFiniteMeasure_map _ _
  have hsum' : IsHilbertSum ℂ
      (fun n => Lp ℂ 2 (Measure.map ((↑) : spectrum ℂ a → ℂ) (diagMeasure ha (ξ n))))
      (fun n => (cyclicIsometry ha (ξ n)).comp
        (embLpEquiv hemb (diagMeasure ha (ξ n))).toLinearIsometry) :=
    isHilbertSum_comp_linearIsometryEquiv hsum fun n => embLpEquiv hemb (diagMeasure ha (ξ n))
  have hsum2 := isHilbertSum_sliceLp
    (fun n => Measure.map ((↑) : spectrum ℂ a → ℂ) (diagMeasure ha (ξ n)))
  have hA : ∀ (n : ℕ)
      (F : Lp ℂ 2 (Measure.map ((↑) : spectrum ℂ a → ℂ) (diagMeasure ha (ξ n)))),
      a (((cyclicIsometry ha (ξ n)).comp
          (embLpEquiv hemb (diagMeasure ha (ξ n))).toLinearIsometry) F)
        = ((cyclicIsometry ha (ξ n)).comp
          (embLpEquiv hemb (diagMeasure ha (ξ n))).toLinearIsometry)
          (mulLp _ (measurable_coordTrunc (‖a‖ * ‖(1 : H →L[ℂ] H)‖))
            (norm_coordTrunc_le hR0) F) := by
    intro n F
    have h1 : embLpEquiv hemb (diagMeasure ha (ξ n))
        (mulLp _ (measurable_coordTrunc (‖a‖ * ‖(1 : H →L[ℂ] H)‖)) (norm_coordTrunc_le hR0) F)
        = coordMulLp ha (ξ n) (embLpEquiv hemb (diagMeasure ha (ξ n)) F) :=
      (embLpEquiv_mulLp hemb (diagMeasure ha (ξ n))
        (measurable_coordTrunc (‖a‖ * ‖(1 : H →L[ℂ] H)‖)) (norm_coordTrunc_le hR0) F).trans
        (mulLp_eq_coordMulLp ha (ξ n) _ _ (fun w => coordTrunc_eq_self (hspec w)) _)
    change a (cyclicIsometry ha (ξ n) (embLpEquiv hemb (diagMeasure ha (ξ n)) F))
      = cyclicIsometry ha (ξ n) (embLpEquiv hemb (diagMeasure ha (ξ n)) _)
    rw [h1, cyclicIsometry_coordMulLp ha (ξ n)]
  have hB : ∀ (n : ℕ)
      (F : Lp ℂ 2 (Measure.map ((↑) : spectrum ℂ a → ℂ) (diagMeasure ha (ξ n)))),
      (mulLp _ ((measurable_coordTrunc (‖a‖ * ‖(1 : H →L[ℂ] H)‖)).comp measurable_fst)
          (fun p => norm_coordTrunc_le hR0 p.1))
        (sliceLp (fun n => Measure.map ((↑) : spectrum ℂ a → ℂ)
          (diagMeasure ha (ξ n))) n F)
        = sliceLp (fun n => Measure.map ((↑) : spectrum ℂ a → ℂ) (diagMeasure ha (ξ n))) n
          (mulLp _ (measurable_coordTrunc (‖a‖ * ‖(1 : H →L[ℂ] H)‖))
            (norm_coordTrunc_le hR0) F) :=
    fun n F => (sliceLp_mulLp (fun m => Measure.map ((↑) : spectrum ℂ a → ℂ)
      (diagMeasure ha (ξ m))) n (measurable_coordTrunc (‖a‖ * ‖(1 : H →L[ℂ] H)‖))
      (norm_coordTrunc_le hR0) F).symm
  have hVc : ∀ (n : ℕ)
      (F : Lp ℂ 2 (Measure.map ((↑) : spectrum ℂ a → ℂ) (diagMeasure ha (ξ n)))),
      ((cyclicIsometry ha (ξ n)).comp
          (embLpEquiv hemb (diagMeasure ha (ξ n))).toLinearIsometry) (star F)
        = cH (((cyclicIsometry ha (ξ n)).comp
          (embLpEquiv hemb (diagMeasure ha (ξ n))).toLinearIsometry) F) := by
    intro n F
    change cyclicIsometry ha (ξ n) (embLpEquiv hemb (diagMeasure ha (ξ n)) (star F))
      = cH (cyclicIsometry ha (ξ n) (embLpEquiv hemb (diagMeasure ha (ξ n)) F))
    rw [← star_embLpEquiv hemb (diagMeasure ha (ξ n)) F, hstar]
  have hWc : ∀ (n : ℕ)
      (F : Lp ℂ 2 (Measure.map ((↑) : spectrum ℂ a → ℂ) (diagMeasure ha (ξ n)))),
      sliceLp (fun m => Measure.map ((↑) : spectrum ℂ a → ℂ) (diagMeasure ha (ξ m))) n (star F)
        = star (sliceLp (fun m => Measure.map ((↑) : spectrum ℂ a → ℂ)
          (diagMeasure ha (ξ m))) n F) :=
    fun n F => (star_sliceLp (fun m => Measure.map ((↑) : spectrum ℂ a → ℂ)
      (diagMeasure ha (ξ m))) n F).symm
  have hstep1 := starOperatorUnitaryEquiv_of_isHilbertSum hsum' hsum2 hA hB hcH hcHadd
    continuous_star_lp star_add_lp hVc hWc
  obtain ⟨ρ, D, hρfin, hDmeas, hDanti, hρsupp, hρzero, hstep2⟩ :=
    exists_multiplicityLevels (fun n => Measure.map ((↑) : spectrum ℂ a → ℂ)
      (diagMeasure ha (ξ n))) (measurable_coordTrunc (‖a‖ * ‖(1 : H →L[ℂ] H)‖))
      (norm_coordTrunc_le hR0)
  have hbase : ρ {z : ℂ | z.im ≠ 0} = 0 := by
    refine hρsupp _ measurableSet_im_ne_zero fun n => ?_
    rw [Measure.map_apply hemb.measurable measurableSet_im_ne_zero]
    convert measure_empty (μ := diagMeasure ha (ξ n))
    refine Set.eq_empty_iff_forall_notMem.mpr fun w hw => ?_
    exact hw (hsa.im_eq_zero_of_mem_spectrum w.2)
  refine ⟨⟨ρ, ‖a‖ * ‖(1 : H →L[ℂ] H)‖, D, hρfin, hR0, ?_, hρzero, hDmeas, hDanti⟩, hbase, ?_⟩
  · refine hρsupp _ (measurableSet_lt measurable_const measurable_norm) fun n => ?_
    rw [Measure.map_apply hemb.measurable (measurableSet_lt measurable_const measurable_norm)]
    convert measure_empty (μ := diagMeasure ha (ξ n))
    refine Set.eq_empty_iff_forall_notMem.mpr fun w hw => ?_
    exact absurd (hspec w) (not_le.mpr hw)
  · exact starOperatorUnitaryEquiv_operator_of_mulLp_sliceSum _ (hstep1.trans hstep2)

end StarModel

end BorelCalculus

end TauCeti
