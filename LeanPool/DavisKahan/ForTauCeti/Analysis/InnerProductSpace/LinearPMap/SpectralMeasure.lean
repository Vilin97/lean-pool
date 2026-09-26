/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralMeasure.Construction

/-!
# The spectral measure of an unbounded self-adjoint operator: bounded sets

Given the spectral measure built in
`…LinearPMap.SpectralMeasure.Construction`, this module is what a bounded Borel
set `B` buys: on `specRange hA B hB` the operator `A` is *bounded*, and away from
`B` its restriction has a resolvent gap.

* `truncSymbol` and `truncation`, the bounded operator agreeing with `A` on the
  spectral range of a bounded set, with its self-adjointness and its commutation
  with `specProjection`;
* `tendsto_specProjection_Icc`, the exhaustion of `H` by bounded spectral sets;
* `re_inner_apply_bounds_of_subset_Icc`, the numerical range bound on a spectral
  subspace of an interval;
* `mem_resolventSet_specRestrict_of_gap`, the resolvent gap: a real point at
  distance `ε` from `B` lies in the resolvent set of `specRestrict`.

Importing this module gives the whole spectral-measure development, as it did
before the split.

## Sources

See `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean`
for the sources of the construction (the classical Cayley-transform route, and
the Spectra-removal plan for the comparison against the donor's).  The
bounded-set truncation and the resolvent-gap estimate in this file are shaped by
what the Davis--Kahan block argument consumes and follow no source's presentation.

## Provenance

*Split, not restated.*  Until 2026-07-29 this file held the construction and this
bounded-set theory together in 1243 lines, over Tau Ceti's stated 1000-line limit
for a new file (`ForTauCeti/README.md` §4).  It was divided at its
`end Reduce` / `section BoundedSet` seam; the construction moved to
`…SpectralMeasure.Construction` and this root kept the `BoundedSet` and
`ResolventGap` sections.  **No statement, signature, proof, attribute or
declaration name changed**, and every consumer's `import
ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralMeasure` still resolves
to the whole development.

The material itself is *new*; see
`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean` for the
provenance of the route, and the Spectra-removal plan for the
comparison against Spectra's Herglotz/Poisson route that chose it.
-/

@[expose] public section

open scoped InnerProductSpace
open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti
namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section BoundedSet

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-- Off the Cayley singularity, `κ(w) + i = 2i/(1 - w)`. -/
theorem cayleyInv_add_I {w : _root_.spectrum ℂ (cayley hA)} (hw1 : (w : ℂ) ≠ 1) :
    ((cayleyInv hA w : ℝ) : ℂ) + Complex.I = (2 * Complex.I) / (1 - (w : ℂ)) := by
  have hnorm : ‖(w : ℂ)‖ = 1 :=
    spectrum.norm_eq_one_of_unitary (cayley_mem_unitary hA) w.2
  have hd : (1 : ℂ) - (w : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have hcast : ((cayleyInv hA w : ℝ) : ℂ) = Complex.I * (1 + (w : ℂ)) / (1 - (w : ℂ)) :=
    Complex.ext (by simp [cayleyInv_def])
      (by simpa using (inverseCayley_im_eq_zero hnorm hw1).symm)
  rw [hcast]
  field_simp
  ring

/-- **The Cayley symbol and `κ + i` are reciprocal off the singularity.**

`(2i)⁻¹(1 - w)` is the value of the symbol every construction here calls `gsym`, and this
says it inverts `κ(w) + i`.  Three proofs -- two `hprod`s and one `hgae`, in this file and
in `SpectralGapInverse.lean` -- each derived it inline from `cayleyInv_add_I` and
`field_simp`; it is one line of algebra and belongs beside the identity it uses. -/
theorem inv_two_I_mul_one_sub_mul_cayleyInv_add_I
    {w : _root_.spectrum ℂ (cayley hA)} (hw1 : (w : ℂ) ≠ 1) :
    (2 * Complex.I)⁻¹ * (1 - (w : ℂ)) * (((cayleyInv hA w : ℝ) : ℂ) + Complex.I) = 1 := by
  have hd : (1 : ℂ) - (w : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  rw [cayleyInv_add_I hA hw1]
  field_simp

variable (B : Set ℝ) (hB : MeasurableSet B)

/-- The symbol `(κ - c) · 1_B` of the shifted bounded truncation. -/
noncomputable def truncSymbol (c : ℝ) : _root_.spectrum ℂ (cayley hA) → ℂ :=
  fun w => ((cayleyInv hA w : ℂ) - (c : ℂ)) *
    (cayleyInv hA ⁻¹' B).indicator (fun _ => (1 : ℂ)) w

/-- The truncation symbol is bounded by `r` whenever `B` sits within `r` of `c`.  Both branches
matter: off `B` the indicator kills the symbol, so the bound needs only `0 ≤ r`. -/
theorem norm_truncSymbol_le {c r : ℝ} (hr : 0 ≤ r) (hcr : ∀ s ∈ B, |s - c| ≤ r)
    (w : _root_.spectrum ℂ (cayley hA)) : ‖truncSymbol hA B c w‖ ≤ r := by
  by_cases hw : w ∈ cayleyInv hA ⁻¹' B
  · have hκB : cayleyInv hA w ∈ B := hw
    have h2 : (cayleyInv hA ⁻¹' B).indicator (fun _ => (1 : ℂ)) w = 1 := by simp [hw]
    rw [truncSymbol]
    simp only [h2, mul_one]
    rw [show ((cayleyInv hA w : ℂ) - (c : ℂ)) = ((cayleyInv hA w - c : ℝ) : ℂ) by
        push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
    exact hcr _ hκB
  · have h2 : (cayleyInv hA ⁻¹' B).indicator (fun _ => (1 : ℂ)) w = 0 := by simp [hw]
    rw [truncSymbol]
    simp only [h2, mul_zero, norm_zero]
    exact hr

include hB in
/-- The truncation symbol is admissible for the bounded Borel calculus -- measurable, from
measurability of the relabelling and of `B`, and bounded by the previous lemma. -/
theorem isBddMeasurable_truncSymbol {c r : ℝ} (hr : 0 ≤ r)
    (hcr : ∀ s ∈ B, |s - c| ≤ r) :
    BorelCalculus.IsBddMeasurable (truncSymbol hA B c) := by
  have hmeasκ : Measurable fun w => ((cayleyInv hA w : ℝ) : ℂ) :=
    Complex.continuous_ofReal.measurable.comp (measurable_cayleyInv hA)
  have hSm : MeasurableSet (cayleyInv hA ⁻¹' B) := measurable_cayleyInv hA hB
  exact ⟨(hmeasκ.sub measurable_const).mul (measurable_const.indicator hSm), r, hr,
    norm_truncSymbol_le hA B hr hcr⟩

/-- The indicator of the Cayley preimage of `B`: the symbol whose Borel calculus
is the spectral projection `E_A(B)`.

Named because it was being rebuilt inline in every proof that needed it,
together with its two pointwise values — `specProjection_apply_sub_smul` and
`mem_resolventSet_specRestrict_of_gap` between them proved those four times. -/
private noncomputable def cayleyIndicator : _root_.spectrum ℂ (cayley hA) → ℂ :=
  (cayleyInv hA ⁻¹' B).indicator (fun _ => (1 : ℂ))

private theorem cayleyIndicator_of_mem {w : _root_.spectrum ℂ (cayley hA)}
    (hw : w ∈ cayleyInv hA ⁻¹' B) : cayleyIndicator hA B w = 1 := by
  simp [cayleyIndicator, hw]

private theorem cayleyIndicator_of_notMem {w : _root_.spectrum ℂ (cayley hA)}
    (hw : w ∉ cayleyInv hA ⁻¹' B) : cayleyIndicator hA B w = 0 := by
  simp [cayleyIndicator, hw]

include hB in
private theorem isBddMeasurable_cayleyIndicator :
    BorelCalculus.IsBddMeasurable (cayleyIndicator hA B) :=
  BorelCalculus.isBddMeasurable_indicator (a := cayley hA) (measurable_cayleyInv hA hB)


/-- The inverting symbol `(κ - lam)⁻¹ · 1_B` of the resolvent-gap argument.

`lam` is an explicit argument rather than a section variable, which is all it
needed: nothing about the surrounding section has to change to give this
function a name. -/
private noncomputable def gapSymbol (lam : ℝ) : _root_.spectrum ℂ (cayley hA) → ℂ :=
  fun w => ((cayleyInv hA w : ℂ) - (lam : ℂ))⁻¹ * cayleyIndicator hA B w

/-- On the support the inverting symbol is the plain reciprocal. -/
private theorem gapSymbol_of_mem {lam : ℝ} {w : _root_.spectrum ℂ (cayley hA)}
    (hw : w ∈ cayleyInv hA ⁻¹' B) :
    gapSymbol hA B lam w = ((cayleyInv hA w : ℂ) - (lam : ℂ))⁻¹ := by
  rw [gapSymbol, cayleyIndicator_of_mem hA B hw, mul_one]

/-- Off the support the indicator kills the inverting symbol. -/
private theorem gapSymbol_of_notMem {lam : ℝ} {w : _root_.spectrum ℂ (cayley hA)}
    (hw : w ∉ cayleyInv hA ⁻¹' B) : gapSymbol hA B lam w = 0 := by
  rw [gapSymbol, cayleyIndicator_of_notMem hA B hw, mul_zero]

include hB in
/-- The inverting symbol is admissible for the bounded Borel calculus.  The
bound is `ε⁻¹`, from the gap alone: on the support the factor is at least `ε` in
modulus, and off it the indicator kills the symbol. -/
private theorem isBddMeasurable_gapSymbol {lam ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ s ∈ B, ε ≤ |s - lam|) :
    BorelCalculus.IsBddMeasurable (gapSymbol hA B lam) := by
  classical
  have hmeasκ : Measurable fun w => ((cayleyInv hA w : ℝ) : ℂ) :=
    Complex.continuous_ofReal.measurable.comp (measurable_cayleyInv hA)
  have hgapS : ∀ w ∈ cayleyInv hA ⁻¹' B,
      ε ≤ ‖((cayleyInv hA w : ℂ) - (lam : ℂ))‖ := by
    intro w hw
    rw [show ((cayleyInv hA w : ℂ) - (lam : ℂ)) = ((cayleyInv hA w - lam : ℝ) : ℂ) by
        push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
    exact hgap _ hw
  refine ⟨((hmeasκ.sub measurable_const).inv).mul
      (isBddMeasurable_cayleyIndicator hA B hB).measurable, ε⁻¹, by positivity, fun w => ?_⟩
  by_cases hw : w ∈ cayleyInv hA ⁻¹' B
  · rw [gapSymbol_of_mem hA B hw, norm_inv]
    simpa only [one_div] using one_div_le_one_div_of_le hε (hgapS w hw)
  · rw [gapSymbol_of_notMem hA B hw, norm_zero]
    positivity


/-- **Bounded spectral sets.**  If the spectral parameter stays within `r` of `c`
on `B`, then the spectral projection lands in `dom A` and `A - c` is bounded by
`r` there.  Both facts come from one identity: `(A + i) E_A(B)` is the Borel
calculus of `(κ + i) 1_B`, because the resolvent's symbol `(1-w)/(2i)` is the
pointwise inverse of `κ + i` away from the Cayley singularity. -/
theorem specProjection_apply_sub_smul {M c r : ℝ}
    (hbnd : ∀ s ∈ B, |s| ≤ M) (hr : 0 ≤ r) (hcr : ∀ s ∈ B, |s - c| ≤ r) (y : H) :
    ∃ hy : specProjection hA B hB y ∈ A.domain,
      A ⟨specProjection hA B hB y, hy⟩ - (c : ℂ) • specProjection hA B hB y
        = BorelCalculus.borelCalculus (isStarNormal_cayley hA)
            (isBddMeasurable_truncSymbol hA B hB hr hcr) y := by
  classical
  set hU := isStarNormal_cayley hA with hhU
  set hni := negI_mem_resolventSet hA with hhni
  set κ := cayleyInv hA with hκ
  set S : Set (_root_.spectrum ℂ (cayley hA)) := κ ⁻¹' B with hS
  have hSm : MeasurableSet S := measurable_cayleyInv hA hB
  set ind : _root_.spectrum ℂ (cayley hA) → ℂ := cayleyIndicator hA B with hind
  have hmeasκ : Measurable fun w => ((κ w : ℝ) : ℂ) :=
    Complex.continuous_ofReal.measurable.comp (measurable_cayleyInv hA)
  have hindb : BorelCalculus.IsBddMeasurable ind :=
    BorelCalculus.isBddMeasurable_indicator (a := cayley hA) hSm
  -- the spectral projection *is* this calculus; `specProjection_eq_borelCalculus` is what
  -- replaces unfolding its body, and `IsBddMeasurable` is a `Prop`, so the two admissibility
  -- proofs are interchangeable
  have hP : specProjection hA B hB = BorelCalculus.borelCalculus hU hindb :=
    specProjection_eq_borelCalculus hA B hB
  set q : _root_.spectrum ℂ (cayley hA) → ℂ :=
    fun w => ((κ w : ℂ) + Complex.I) * ind w with hq
  set pf : _root_.spectrum ℂ (cayley hA) → ℂ :=
    fun w => ((κ w : ℂ) - (c : ℂ)) * ind w with hpf
  have hqb : BorelCalculus.IsBddMeasurable q := by
    refine ⟨(hmeasκ.add measurable_const).mul hindb.measurable, max 0 M + 1,
      by positivity, fun w => ?_⟩
    by_cases hw : w ∈ S
    · have hκB : κ w ∈ B := hw
      have h1 : ‖((κ w : ℂ) + Complex.I)‖ ≤ max 0 M + 1 := by
        refine le_trans (norm_add_le _ _) ?_
        rw [Complex.norm_real, Real.norm_eq_abs, Complex.norm_I]
        have := hbnd _ hκB
        have := le_max_right 0 M
        linarith
      have h2 : ind w = 1 := by rw [hind]; exact cayleyIndicator_of_mem hA B hw
      rw [hq]; simp only [h2, mul_one]; exact h1
    · have h2 : ind w = 0 := by rw [hind]; exact cayleyIndicator_of_notMem hA B hw
      rw [hq]; simp only [h2, mul_zero, norm_zero]; positivity
  -- `pf` is `truncSymbol hA B c`, so its admissibility is the lemma above, not a new argument
  have hpb : BorelCalculus.IsBddMeasurable pf := isBddMeasurable_truncSymbol hA B hB hr hcr
  -- the resolvent as a Borel-calculus image
  set gsym : C(_root_.spectrum ℂ (cayley hA), ℂ) :=
    (2 * Complex.I)⁻¹ • (cayleyCoord hA - 1) with hgsym
  have hgb : BorelCalculus.IsBddMeasurable (fun w => gsym w) :=
    BorelCalculus.IsBddMeasurable.of_continuous gsym
  have hRg : resolvent A (-Complex.I) = BorelCalculus.borelCalculus hU hgb :=
    resolvent_negI_eq_borelCalculus hA hgb
  -- The canonical resolvent's symbol is `(w - 1)/(2i)`, the negative of the `A - z`
  -- convention's, so the product symbol is *minus* the indicator off the singularity.
  have hnind : BorelCalculus.IsBddMeasurable (fun w => (-1 : ℂ) * ind w) :=
    hindb.const_smul (-1)
  -- `IsBddMeasurable` is a `Prop`, so this is the `const_smul` lemma restated with `hnind`
  have hsmul : BorelCalculus.borelCalculus hU hnind
      = (-1 : ℂ) • BorelCalculus.borelCalculus hU hindb :=
    BorelCalculus.borelCalculus_const_smul hU (-1) hindb
  have hprod : BorelCalculus.borelCalculus hU (hgb.mul hqb)
      = BorelCalculus.borelCalculus hU hnind := by
    refine borelCalculus_congr_of_ne_one hA _ _ fun w hw1 => ?_
    have hgval : gsym w = (2 * Complex.I)⁻¹ * ((w : ℂ) - 1) := by simp [hgsym]
    -- states the goal with the definition unfolded, in the shape the next step needs.
    change gsym w * q w = (-1 : ℂ) * ind w
    have hqw : q w = ((κ w : ℂ) + Complex.I) * ind w := rfl
    have hneg : (2 * Complex.I)⁻¹ * ((w : ℂ) - 1)
        = -((2 * Complex.I)⁻¹ * (1 - (w : ℂ))) := by ring
    rw [hgval, hqw, hneg, neg_mul, ← mul_assoc,
      inv_two_I_mul_one_sub_mul_cayleyInv_add_I hA hw1, one_mul, neg_one_mul]
  -- the shifted symbol is the difference of the two Borel-calculus images
  set hsm := hindb.const_smul (-(Complex.I + (c : ℂ))) with hhsm
  have heq : BorelCalculus.borelCalculus hU hpb
      = BorelCalculus.borelCalculus hU (hqb.add hsm) := by
    refine BorelCalculus.borelCalculus_congr_ae hU _ _ fun η =>
      Filter.Eventually.of_forall fun w => ?_
    -- states the goal with the definition unfolded, in the shape the next step needs.
    change pf w = q w + -(Complex.I + (c : ℂ)) * ind w
    rw [hpf, hq]; ring
  -- hence `(A + i) E(B)` is the Borel calculus of `(κ + i) 1_B`
  set T := BorelCalculus.borelCalculus hU hqb with hT
  have hPy : resolvent A (-Complex.I) (T y) = -(specProjection hA B hB y) := by
    have h := congrArg (fun L : H →L[ℂ] H => L y)
      ((BorelCalculus.borelCalculus_mul hU hgb hqb).symm.trans hprod)
    simp only [_root_.mul_apply_eq_comp] at h
    rw [hRg, h, hsmul, hP]
    simp only [neg_one_smul, _root_.neg_apply]
  have hyneg : -(specProjection hA B hB y) ∈ A.domain := by
    rw [← hPy]; exact resolvent_mem_domain hni (T y)
  have hy : specProjection hA B hB y ∈ A.domain := by
    simpa using neg_mem hyneg
  refine ⟨hy, ?_⟩
  -- solve for `A` on the range
  have hsolve := smul_sub_apply_resolvent hni (T y)
  have hcongr : (⟨resolvent A (-Complex.I) (T y), resolvent_mem_domain hni (T y)⟩ : A.domain)
      = -(⟨specProjection hA B hB y, hy⟩ : A.domain) := Subtype.ext hPy
  rw [hcongr, hPy, _root_.LinearPMap.map_neg] at hsolve
  have hval : BorelCalculus.borelCalculus hU hpb y
      = T y - (Complex.I + (c : ℂ)) • specProjection hA B hB y := by
    rw [heq, BorelCalculus.borelCalculus_add hU hqb hsm,
      BorelCalculus.borelCalculus_const_smul hU (-(Complex.I + (c : ℂ))) hindb]
    simp only [_root_.add_apply, _root_.smul_apply, hT]
    rw [neg_smul, ← sub_eq_add_neg, hP]
  have hgoal : A ⟨specProjection hA B hB y, hy⟩ - (c : ℂ) • specProjection hA B hB y
      = BorelCalculus.borelCalculus hU hpb y := by
    rw [hval]
    linear_combination (norm := module) hsolve
  exact hgoal

/-- A bounded spectral range lies inside the operator domain. -/
theorem mem_domain_of_mem_specRange_of_bounded {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M)
    {x : H} (hx : x ∈ specRange hA B hB) : x ∈ A.domain := by
  have hfix : specProjection hA B hB x = x := (mem_specRange_iff hA B hB x).mp hx
  obtain ⟨hy, -⟩ := specProjection_apply_sub_smul hA B hB hbnd
    (c := 0) (r := max 0 M) (le_max_left 0 M)
    (fun s hs => by simpa using le_trans (hbnd s hs) (le_max_right 0 M)) x
  rwa [hfix] at hy

/-- On a spectral range over a set within `r` of `c`, the operator differs from
`c` by at most `r` in norm. -/
theorem norm_sub_smul_le_of_mem_specRange {M c r : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M)
    (hr : 0 ≤ r) (hcr : ∀ s ∈ B, |s - c| ≤ r) {x : H} (hx : x ∈ specRange hA B hB)
    (hmem : x ∈ A.domain) :
    ‖A ⟨x, hmem⟩ - (c : ℂ) • x‖ ≤ r * ‖x‖ := by
  have hfix : specProjection hA B hB x = x := (mem_specRange_iff hA B hB x).mp hx
  obtain ⟨hy, hb⟩ := specProjection_apply_sub_smul hA B hB hbnd hr hcr x
  have hsub : (⟨specProjection hA B hB x, hy⟩ : A.domain) = ⟨x, hmem⟩ := Subtype.ext hfix
  rw [hsub, hfix] at hb
  rw [hb]
  exact BorelCalculus.norm_borelCalculus_apply_le _ _ hr
    (norm_truncSymbol_le hA B hr hcr) x

/-- **The interval cutoffs converge strongly to the identity.** -/
theorem tendsto_specProjection_Icc (x : H) :
    Filter.Tendsto
      (fun τ : ℝ => specProjection hA (Set.Icc (-τ) τ) measurableSet_Icc x)
      Filter.atTop (nhds x) := by
  classical
  set hU := isStarNormal_cayley hA with hhU
  set μ := BorelCalculus.diagMeasure hU x with hμ
  set κ := cayleyInv hA with hκ
  set F : ℝ → _root_.spectrum ℂ (cayley hA) → ℝ :=
    fun τ => (κ ⁻¹' Set.Icc (-τ) τ).indicator (fun _ => (1 : ℝ)) with hF
  -- the diagonal masses are the indicator integrals
  have hd : ∀ τ : ℝ, (((spectralPVM hA).diag x) (Set.Icc (-τ) τ)).toReal
      = ∫ w, F τ w ∂μ := by
    intro τ
    have hSm : MeasurableSet (κ ⁻¹' Set.Icc (-τ) τ) :=
      measurable_cayleyInv hA measurableSet_Icc
    have hdiag : ((spectralPVM hA).diag x) = Measure.map κ μ := by
      rw [spectralPVM_def, BorelCalculus.toProjValMeasure_diag,
        BorelCalculus.specDiag_def, hμ, hκ]
    -- Left as a `rw` chain on purpose: `simp only` with this same list leaves the
    -- goal unsolved.  `integral_indicator_const` only applies once `Measure.map_apply`
    -- has put the measure in the right form, and `simp only` normalises past that shape
    -- before the integral lemma can see it.
    rw [hdiag,
      Measure.map_apply (measurable_cayleyInv hA) measurableSet_Icc, hF,
      integral_indicator_const _ hSm, smul_eq_mul, mul_one,
      MeasureTheory.measureReal_def]
  -- dominated convergence
  have hlim : Filter.Tendsto (fun τ : ℝ => ∫ w, F τ w ∂μ) Filter.atTop
      (nhds (∫ _w, (1 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
      (Filter.Eventually.of_forall fun τ =>
        (measurable_const.indicator
          (measurable_cayleyInv hA measurableSet_Icc)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun τ => Filter.Eventually.of_forall fun w => ?_)
      (integrable_const _)
      (Filter.Eventually.of_forall fun w => ?_)
    · by_cases hw : w ∈ κ ⁻¹' Set.Icc (-τ) τ <;> simp [hF, hw]
    · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Filter.eventually_ge_atTop |κ w|] with τ hτ
      have hmem : w ∈ κ ⁻¹' Set.Icc (-τ) τ :=
        ⟨by linarith [neg_abs_le (κ w)], by linarith [le_abs_self (κ w)]⟩
      simp [hF, hmem]
  have htot : ∫ _w, (1 : ℝ) ∂μ = ‖x‖ ^ 2 := by
    rw [integral_const, smul_eq_mul, mul_one, MeasureTheory.measureReal_def, hμ,
      BorelCalculus.diagMeasure_univ_toReal]
  -- the squared distance is the missing mass
  have hsq : ∀ τ : ℝ,
      ‖specProjection hA (Set.Icc (-τ) τ) measurableSet_Icc x - x‖ ^ 2
        = ‖x‖ ^ 2 - (((spectralPVM hA).diag x) (Set.Icc (-τ) τ)).toReal := by
    intro τ
    have hnormP : ‖specProjection hA (Set.Icc (-τ) τ) measurableSet_Icc x‖ ^ 2
        = (((spectralPVM hA).diag x) (Set.Icc (-τ) τ)).toReal := by
      rw [specProjection_def]; exact (spectralPVM hA).norm_sq_proj_apply _ _ x
    have hinner : ⟪x, specProjection hA (Set.Icc (-τ) τ) measurableSet_Icc x⟫_ℂ
        = ((((spectralPVM hA).diag x) (Set.Icc (-τ) τ)).toReal : ℂ) := by
      rw [specProjection_def]; exact (spectralPVM hA).inner_proj _ _ x
    have hre : RCLike.re (⟪specProjection hA (Set.Icc (-τ) τ) measurableSet_Icc x, x⟫_ℂ)
        = (((spectralPVM hA).diag x) (Set.Icc (-τ) τ)).toReal := by
      rw [← inner_conj_symm, hinner]
      simp
    rw [norm_sub_sq (𝕜 := ℂ), hnormP, hre]
    ring
  -- conclude
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  have hsq' : Filter.Tendsto
      (fun τ : ℝ => ‖specProjection hA (Set.Icc (-τ) τ) measurableSet_Icc x - x‖ ^ 2)
      Filter.atTop (nhds 0) := by
    have hconv : Filter.Tendsto
        (fun τ : ℝ => ‖x‖ ^ 2 - (((spectralPVM hA).diag x) (Set.Icc (-τ) τ)).toReal)
        Filter.atTop (nhds (‖x‖ ^ 2 - ‖x‖ ^ 2)) := by
      refine Filter.Tendsto.sub tendsto_const_nhds ?_
      simpa only [hd, htot] using hlim
    simpa only [hsq, sub_self] using hconv
  have hfin := (Real.continuous_sqrt.tendsto 0).comp hsq'
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hfin

/-- **Form bounds on a spectral range.**  If `B ⊆ [β, α]` then the quadratic
form of `A` on the spectral range of `B` is confined to `[β, α]`. -/
theorem re_inner_apply_bounds_of_subset_Icc {β α : ℝ} (hBsub : B ⊆ Set.Icc β α)
    {y : H} (hyK : y ∈ specRange hA B hB) (hy : y ∈ A.domain) :
    β * ‖y‖ ^ 2 ≤ (⟪A ⟨y, hy⟩, y⟫_ℂ).re ∧ (⟪A ⟨y, hy⟩, y⟫_ℂ).re ≤ α * ‖y‖ ^ 2 := by
  rcases le_or_gt β α with hβα | hβα
  · have hM : ∀ s ∈ B, |s| ≤ max |β| |α| := fun s hs => by
      obtain ⟨h1, h2⟩ := hBsub hs
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · have h3 := neg_abs_le β
        have h4 := le_max_left |β| |α|
        linarith
      · have h3 := le_abs_self α
        have h4 := le_max_right |β| |α|
        linarith
    have hr : (0 : ℝ) ≤ (α - β) / 2 := by linarith
    have hcr : ∀ s ∈ B, |s - (β + α) / 2| ≤ (α - β) / 2 := fun s hs => by
      obtain ⟨h1, h2⟩ := hBsub hs
      rw [abs_le]
      constructor <;> linarith
    have hbound := norm_sub_smul_le_of_mem_specRange hA B hB hM hr hcr hyK hy
    have hyy : (⟪y, y⟫_ℂ).re = ‖y‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    have hexp : (⟪A ⟨y, hy⟩ - (((β + α) / 2 : ℝ) : ℂ) • y, y⟫_ℂ).re
        = (⟪A ⟨y, hy⟩, y⟫_ℂ).re - (β + α) / 2 * ‖y‖ ^ 2 := by
      rw [inner_sub_left, inner_smul_left, Complex.sub_re, Complex.conj_ofReal,
        Complex.re_ofReal_mul, hyy]
    have hcs : |(⟪A ⟨y, hy⟩ - (((β + α) / 2 : ℝ) : ℂ) • y, y⟫_ℂ).re|
        ≤ (α - β) / 2 * ‖y‖ ^ 2 := by
      calc |(⟪A ⟨y, hy⟩ - (((β + α) / 2 : ℝ) : ℂ) • y, y⟫_ℂ).re|
          ≤ ‖⟪A ⟨y, hy⟩ - (((β + α) / 2 : ℝ) : ℂ) • y, y⟫_ℂ‖ := Complex.abs_re_le_norm _
        _ ≤ ‖A ⟨y, hy⟩ - (((β + α) / 2 : ℝ) : ℂ) • y‖ * ‖y‖ := norm_inner_le_norm _ _
        _ ≤ ((α - β) / 2 * ‖y‖) * ‖y‖ := by gcongr
        _ = (α - β) / 2 * ‖y‖ ^ 2 := by ring
    rw [hexp, abs_le] at hcs
    constructor <;> nlinarith [hcs.1, hcs.2]
  · -- `Set.Icc β α` is empty, hence so is `B`, hence the spectral range is trivial
    have hIcc : Set.Icc β α = (∅ : Set ℝ) := Set.Icc_eq_empty (not_le.mpr hβα)
    have hBempty : B = (∅ : Set ℝ) := Set.eq_empty_of_subset_empty (hIcc ▸ hBsub)
    have hfix : specProjection hA B hB y = y := (mem_specRange_iff hA B hB y).mp hyK
    have hzero : ‖y‖ ^ 2 = 0 := by
      conv_lhs => rw [← hfix]
      rw [show specProjection hA B hB y = (spectralPVM hA).proj B hB y from
          congrFun (congrArg _ (specProjection_def hA B hB)) y,
        (spectralPVM hA).norm_sq_proj_apply, hBempty, measure_empty, ENNReal.toReal_zero]
    have hy0 : y = 0 := norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero)
    subst hy0
    have h0 : (⟨(0 : H), hy⟩ : A.domain) = 0 := Subtype.ext rfl
    rw [h0, _root_.LinearPMap.map_zero]
    simp

/-- **The bounded truncation of `A` to a bounded spectral set** — the Borel
calculus of `κ · 1_B`.  It agrees with `A` on the spectral range. -/
noncomputable def truncation {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M) : H →L[ℂ] H :=
  BorelCalculus.borelCalculus (isStarNormal_cayley hA)
    (isBddMeasurable_truncSymbol hA B hB (c := 0) (r := max 0 M) (le_max_left 0 M)
      (fun s hs => by simpa using le_trans (hbnd s hs) (le_max_right 0 M)))

/-- **The truncation agrees with `A` on the spectral range.**  This is the point of the
construction: `A` is unbounded, but on a bounded spectral set it is implemented by a bounded
operator, and the existential carries the domain membership that lets `A` be applied at all. -/
theorem truncation_eq_on_specProjection {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M) (y : H) :
    ∃ hy : specProjection hA B hB y ∈ A.domain,
      A ⟨specProjection hA B hB y, hy⟩ = truncation hA B hB hbnd y := by
  obtain ⟨hy, hb⟩ := specProjection_apply_sub_smul hA B hB hbnd (c := 0)
    (r := max 0 M) (le_max_left 0 M)
    (fun s hs => by simpa using le_trans (hbnd s hs) (le_max_right 0 M)) y
  exact ⟨hy, by simpa [truncation] using hb⟩

/-- The truncation is bounded by the spectral bound of `B`. -/
theorem norm_truncation_apply_le {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M) (y : H) :
    ‖truncation hA B hB hbnd y‖ ≤ max 0 M * ‖y‖ :=
  BorelCalculus.norm_borelCalculus_apply_le _ _ (le_max_left 0 M)
    (norm_truncSymbol_le hA B (c := 0) (r := max 0 M) (le_max_left 0 M)
      (fun s hs => by simpa using le_trans (hbnd s hs) (le_max_right 0 M))) y

/-- The truncation is self-adjoint: its symbol is real. -/
theorem isSelfAdjoint_truncation {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M) :
    IsSelfAdjoint (truncation hA B hB hbnd) := by
  have hs := isBddMeasurable_truncSymbol hA B hB (c := 0) (r := max 0 M) (le_max_left 0 M)
    (fun s hs => by simpa using le_trans (hbnd s hs) (le_max_right 0 M))
  have hconj : BorelCalculus.borelCalculus (isStarNormal_cayley hA) hs.conj
      = BorelCalculus.borelCalculus (isStarNormal_cayley hA) hs := by
    refine BorelCalculus.borelCalculus_congr_ae _ _ _ fun η =>
      Filter.Eventually.of_forall fun w => ?_
    -- states the goal with the definition unfolded, in the shape the next step needs.
    change (starRingEnd ℂ) (truncSymbol hA B 0 w) = truncSymbol hA B 0 w
    rw [truncSymbol]
    by_cases hw : w ∈ cayleyInv hA ⁻¹' B <;> simp [hw, Complex.conj_ofReal]
  have hkey : ContinuousLinearMap.adjoint
      (BorelCalculus.borelCalculus (isStarNormal_cayley hA) hs)
      = BorelCalculus.borelCalculus (isStarNormal_cayley hA) hs := by
    rw [← BorelCalculus.borelCalculus_conj (isStarNormal_cayley hA) hs, hconj]
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint]
  exact hkey

/-- The truncation commutes with every spectral projection. -/
theorem truncation_comm_specProjection {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M)
    (C : Set ℝ) (hC : MeasurableSet C) :
    truncation hA B hB hbnd * specProjection hA C hC
      = specProjection hA C hC * truncation hA B hB hbnd := by
  rw [truncation, specProjection_eq_borelCalculus]
  exact BorelCalculus.borelCalculus_comm _ _ _

/-- The truncation absorbs its own spectral projection. -/
theorem truncation_mul_specProjection {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M) :
    truncation hA B hB hbnd * specProjection hA B hB = truncation hA B hB hbnd := by
  rw [truncation, specProjection_eq_borelCalculus, ← BorelCalculus.borelCalculus_mul]
  refine BorelCalculus.borelCalculus_congr_ae _ _ _ fun η =>
    Filter.Eventually.of_forall fun w => ?_
  -- states the goal with the definition unfolded, in the shape the next step needs.
  change truncSymbol hA B 0 w
      * (cayleyInv hA ⁻¹' B).indicator (fun _ => (1 : ℂ)) w = truncSymbol hA B 0 w
  rw [truncSymbol]
  by_cases hw : w ∈ cayleyInv hA ⁻¹' B <;> simp [hw]

/-- The spectral projection is a left identity for the truncation: the truncation already lands in
the spectral range, so projecting again changes nothing. -/
theorem specProjection_mul_truncation {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M) :
    specProjection hA B hB * truncation hA B hB hbnd = truncation hA B hB hbnd := by
  rw [← truncation_comm_specProjection hA B hB hbnd B hB]
  exact truncation_mul_specProjection hA B hB hbnd

end BoundedSet

section ResolventGap

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (B : Set ℝ) (hB : MeasurableSet B)

/-- The scalar estimate behind the boundedness of the companion symbol
`(κ + i) · (κ - lam)⁻¹ 1_B`: a point kept at distance `ε` from `lam` admits a
bound on `‖z + i‖ / ‖z - lam‖` depending only on `lam` and `ε`.

Stated for an arbitrary `z : ℂ` because the argument is the triangle inequality
applied to `z + i = (z - lam) + (lam + i)`; the use site instantiates it at the
real points of the Cayley spectrum. -/
private lemma norm_add_I_mul_inv_norm_sub_le {lam ε : ℝ} (hε : 0 < ε) (z : ℂ)
    (hgap : ε ≤ ‖z - (lam : ℂ)‖) :
    ‖z + Complex.I‖ * ‖z - (lam : ℂ)‖⁻¹ ≤ 1 + (|lam| + 1) / ε := by
  have hpos : 0 < ‖z - (lam : ℂ)‖ := lt_of_lt_of_le hε hgap
  have hb1 : ‖z + Complex.I‖ ≤ ‖z - (lam : ℂ)‖ + (|lam| + 1) := by
    have hsplit : z + Complex.I = (z - (lam : ℂ)) + ((lam : ℂ) + Complex.I) := by ring
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    gcongr
    refine le_trans (norm_add_le _ _) ?_
    rw [Complex.norm_real, Real.norm_eq_abs, Complex.norm_I]
  have hinv : ‖z - (lam : ℂ)‖⁻¹ ≤ ε⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hε hgap
  have hstep : ‖z + Complex.I‖ * ‖z - (lam : ℂ)‖⁻¹
      ≤ (‖z - (lam : ℂ)‖ + (|lam| + 1)) * ‖z - (lam : ℂ)‖⁻¹ := by
    gcongr
  have hexp : (‖z - (lam : ℂ)‖ + (|lam| + 1)) * ‖z - (lam : ℂ)‖⁻¹
      = 1 + (|lam| + 1) * ‖z - (lam : ℂ)‖⁻¹ := by
    rw [add_mul, mul_inv_cancel₀ (ne_of_gt hpos)]
  have hlast : (|lam| + 1) * ‖z - (lam : ℂ)‖⁻¹ ≤ (|lam| + 1) / ε := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv (by positivity)
  linarith

/-- A real point of the Cayley spectrum never cancels `i`; the imaginary parts
cannot agree. -/
private lemma real_add_I_ne_zero (t : ℝ) : ((t : ℂ) + Complex.I) ≠ 0 := by
  intro h0
  have him := congrArg Complex.im h0
  simp at him

/-- The pointwise identity behind the **right** inverse law
`(A - lam) T_f = E(B)`: on the support of the indicator, the symbol
`f = (κ - lam)⁻¹` inverts `κ - lam` after the `(κ + i)` companion is split off. -/
private lemma symbol_right_inverse_pointwise {z lam : ℂ} (hz : z - lam ≠ 0) :
    (z + Complex.I) * (z - lam)⁻¹ + -(Complex.I + lam) * (z - lam)⁻¹ = 1 := by
  field_simp
  ring

/-- The pointwise identity behind the **left** inverse law: the same symbol,
composed with `g = (κ + i)⁻¹`, recovers `g` on the support of the indicator. -/
private lemma symbol_left_inverse_pointwise {z lam : ℂ} (hz : z - lam ≠ 0)
    (hi : z + Complex.I ≠ 0) :
    (z - lam)⁻¹ + -(Complex.I + lam) * ((z - lam)⁻¹ * (z + Complex.I)⁻¹)
      = (z + Complex.I)⁻¹ := by
  field_simp
  ring

omit hB in
/-- **The gap hypothesis, transported to the Cayley spectrum.**

`hgap` bounds `|s - lam|` for the real points `s ∈ B`; the symbols are indexed
instead by the spectrum of the Cayley transform, where the corresponding point
is `cayleyInv hA w`.  This is the bridge between the two, and it is what makes
the denominator `κ - lam` bounded away from zero on the support of the
indicator. -/
private lemma le_norm_cayleyInv_sub_of_gap {lam ε : ℝ}
    (hgap : ∀ s ∈ B, ε ≤ |s - lam|)
    {w : _root_.spectrum ℂ (cayley hA)} (hw : w ∈ cayleyInv hA ⁻¹' B) :
    ε ≤ ‖((cayleyInv hA w : ℂ) - (lam : ℂ))‖ := by
  rw [show ((cayleyInv hA w : ℂ) - (lam : ℂ)) = ((cayleyInv hA w - lam : ℝ) : ℂ) by
      push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs]
  exact hgap _ hw

omit hB in
/-- The immediate consequence of the transported gap: the denominator never
vanishes on the support of the indicator, so the inverting symbol is defined
there. -/
private lemma cayleyInv_sub_ne_zero_of_gap {lam ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ s ∈ B, ε ≤ |s - lam|)
    {w : _root_.spectrum ℂ (cayley hA)} (hw : w ∈ cayleyInv hA ⁻¹' B) :
    ((cayleyInv hA w : ℂ) - (lam : ℂ)) ≠ 0 := by
  intro hzero
  have h := le_norm_cayleyInv_sub_of_gap hA B hgap hw
  rw [hzero, norm_zero] at h
  linarith

/-- **The `(κ + i)`-companion of the gap symbol is boundedly measurable.**  On the
gap set the symbol is `(κ - lam)⁻¹`, so the product has modulus at most
`1 + (|lam| + 1) / ε` by `norm_add_I_mul_inv_norm_sub_le`; off the set the symbol
vanishes and so does the product.

This is the multiplier that turns the Borel calculus of `gapSymbol` into a right
inverse for `A - lam`, and it was built inline in
`mem_resolventSet_specRestrict_of_gap`.

`hBm` is taken explicitly rather than through the section variable because it is
used only in the proof, where section binders are not auto-included. -/
private theorem isBddMeasurable_cayleyCoord_add_I_mul_gapSymbol
    (hBm : MeasurableSet B) {lam ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ s ∈ B, ε ≤ |s - lam|) :
    BorelCalculus.IsBddMeasurable
      (fun w => ((cayleyInv hA w : ℂ) + Complex.I) * gapSymbol hA B lam w) := by
  classical
  have hmeasκ : Measurable fun w => ((cayleyInv hA w : ℝ) : ℂ) :=
    Complex.continuous_ofReal.measurable.comp (measurable_cayleyInv hA)
  have hfb : BorelCalculus.IsBddMeasurable (gapSymbol hA B lam) :=
    isBddMeasurable_gapSymbol hA B hBm hε hgap
  refine ⟨(hmeasκ.add measurable_const).mul hfb.measurable,
    1 + (|lam| + 1) / ε, by positivity, fun w => ?_⟩
  by_cases hw : w ∈ cayleyInv hA ⁻¹' B
  · have hfw : ‖gapSymbol hA B lam w‖ =
        (‖((cayleyInv hA w : ℂ) - (lam : ℂ))‖)⁻¹ := by
      rw [gapSymbol_of_mem hA B hw, norm_inv]
    rw [norm_mul, hfw]
    exact norm_add_I_mul_inv_norm_sub_le hε _
      (le_norm_cayleyInv_sub_of_gap hA B hgap hw)
  · rw [gapSymbol_of_notMem hA B hw, mul_zero, norm_zero]
    positivity

/-- **The indicator splits as the companion symbol plus a multiple of the gap
symbol**, pointwise: `1_B = (κ + i)·f + (-(i + lam))·f`, because on the gap set
`f = (κ - lam)⁻¹` and `(κ + i) - (i + lam) = κ - lam`, while off it `f = 0` and
both sides vanish.

This is the pointwise identity behind the right-inverse law in
`mem_resolventSet_specRestrict_of_gap`; stating it separately keeps the
`borelCalculus_congr_ae` step to three lines. -/
private theorem cayleyIndicator_eq_add_smul_gapSymbol
    {lam ε : ℝ} (hε : 0 < ε) (hgap : ∀ s ∈ B, ε ≤ |s - lam|)
    (w : _root_.spectrum ℂ (cayley hA)) :
    cayleyIndicator hA B w
      = ((cayleyInv hA w : ℂ) + Complex.I) * gapSymbol hA B lam w
        + -(Complex.I + (lam : ℂ)) * gapSymbol hA B lam w := by
  classical
  by_cases hw : w ∈ cayleyInv hA ⁻¹' B
  · have hfw : gapSymbol hA B lam w = ((cayleyInv hA w : ℂ) - (lam : ℂ))⁻¹ :=
      gapSymbol_of_mem hA B hw
    rw [cayleyIndicator_of_mem hA B hw, hfw]
    exact (symbol_right_inverse_pointwise
      (cayleyInv_sub_ne_zero_of_gap hA B hε hgap hw)).symm
  · rw [cayleyIndicator_of_notMem hA B hw, gapSymbol_of_notMem hA B hw]
    ring

/-- **The indicator absorbs into the gap symbol.**  `1_B · f = f`, since `f` is
supported on the gap set: on it the indicator is `1`, off it `f` is `0`. -/
private theorem cayleyIndicator_mul_gapSymbol {lam : ℝ}
    (w : _root_.spectrum ℂ (cayley hA)) :
    cayleyIndicator hA B w * gapSymbol hA B lam w = gapSymbol hA B lam w := by
  classical
  by_cases hw : w ∈ cayleyInv hA ⁻¹' B
  · rw [cayleyIndicator_of_mem hA B hw, one_mul]
  · rw [gapSymbol_of_notMem hA B hw, mul_zero]

/-- **The gap symbol is a left inverse pointwise, after multiplying by
`(κ + i)⁻¹`.**  The companion of `cayleyIndicator_eq_add_smul_gapSymbol` for the
other inverse law: on the gap set `f = (κ - lam)⁻¹` and the product telescopes;
off it `f = 0` and both sides vanish. -/
private theorem gapSymbol_left_inverse_pointwise
    {lam ε : ℝ} (hε : 0 < ε) (hgap : ∀ s ∈ B, ε ≤ |s - lam|)
    {w : _root_.spectrum ℂ (cayley hA)}
    (hkne : ((cayleyInv hA w : ℂ) + Complex.I) ≠ 0) :
    gapSymbol hA B lam w +
        -(Complex.I + (lam : ℂ)) *
          (gapSymbol hA B lam w * ((cayleyInv hA w : ℂ) + Complex.I)⁻¹) =
      cayleyIndicator hA B w * ((cayleyInv hA w : ℂ) + Complex.I)⁻¹ := by
  classical
  by_cases hwS : w ∈ cayleyInv hA ⁻¹' B
  · rw [cayleyIndicator_of_mem hA B hwS, gapSymbol_of_mem hA B hwS, one_mul]
    exact symbol_left_inverse_pointwise
      (cayleyInv_sub_ne_zero_of_gap hA B hε hgap hwS) hkne
  · rw [cayleyIndicator_of_notMem hA B hwS, gapSymbol_of_notMem hA B hwS]
    ring

/-- A bounded inverse with both ambient algebraic identities restricts to the
spectral range. Keeping the bounded maps as parameters isolates the domain
and range transports from the concrete Borel-calculus construction. -/
private theorem mem_resolventSet_specRestrict_of_bounded_inverse
    (lam : ℝ) (Rop G P0 : H →L[ℂ] H)
    (hni : -Complex.I ∈ resolventSet A)
    (hP : specProjection hA B hB = P0)
    (hRg : G = -(resolvent A (-Complex.I)))
    (hmemdom : ∀ φ : H, Rop φ ∈ A.domain)
    (hKmap : ∀ φ : H, Rop φ ∈ specRange hA B hB)
    (hright : ∀ φ : H, A ⟨Rop φ, hmemdom φ⟩ - (lam : ℂ) • Rop φ = P0 φ)
    (hlefts' : Rop + (-(Complex.I + (lam : ℂ))) • (Rop * G) = P0 * G) :
    (lam : ℂ) ∈ resolventSet (specRestrict hA B hB) := by
  classical
  -- The canonical resolvent inverts `lam • I - A`; `Rop` inverts `A - lam`, so the
  -- witness is `-Rop`.
  refine mem_resolventSet_iff.mpr
    ⟨-(Rop.restrict (fun x _ => hKmap x)),
      fun φ => neg_mem (hmemdom ((φ : specRange hA B hB) : H)), fun φ => ?_, fun ψ => ?_⟩
  · -- right inverse: `(lam • I - A) (-Rop φ) = φ`
    apply Subtype.ext
    set y : H := ((φ : specRange hA B hB) : H) with hy
    have hmy : -(Rop y) ∈ A.domain := neg_mem (hmemdom y)
    -- states the goal with the definition unfolded, in the shape the next step needs.
    change (lam : ℂ) • (-(Rop y)) - A ⟨-(Rop y), hmy⟩ = y
    have hstep : A (⟨-(Rop y), hmy⟩ : A.domain) = -(A ⟨Rop y, hmemdom y⟩) :=
      _root_.LinearPMap.map_neg A ⟨Rop y, hmemdom y⟩
    have hr := hright y
    have hPy : P0 y = y := by
      rw [← hP]; exact (mem_specRange_iff hA B hB y).mp (φ : specRange hA B hB).2
    rw [hPy] at hr
    rw [hstep]
    linear_combination (norm := module) hr
  · -- left inverse on the domain: `-Rop ((lam • I - A) ψ) = ψ`
    apply Subtype.ext
    have hydom : ((ψ : specRange hA B hB) : H) ∈ A.domain := ψ.2
    have hyK : ((ψ : specRange hA B hB) : H) ∈ specRange hA B hB :=
      (ψ : specRange hA B hB).2
    -- states the goal with the definition unfolded, in the shape the next step needs.
    change -(Rop ((lam : ℂ) • ((ψ : specRange hA B hB) : H)
        - A ⟨((ψ : specRange hA B hB) : H), hydom⟩)) = ((ψ : specRange hA B hB) : H)
    set y : H := ((ψ : specRange hA B hB) : H) with hy
    set φ₀ : H := (-Complex.I) • y - A ⟨y, hydom⟩ with hφ₀
    have hy0 : resolvent A (-Complex.I) φ₀ = y := resolvent_smul_sub_apply hni ⟨y, hydom⟩
    have hsplit : (lam : ℂ) • y - A ⟨y, hydom⟩ = φ₀ + (Complex.I + (lam : ℂ)) • y := by
      rw [hφ₀]; module
    have hPy : P0 y = y := by
      rw [← hP]; exact (mem_specRange_iff hA B hB y).mp hyK
    have hfin := congrArg (fun L : H →L[ℂ] H => L φ₀) hlefts'
    simp only [_root_.add_apply, _root_.smul_apply, _root_.mul_apply_eq_comp] at hfin
    -- `borelCalculus hU hgb = -resolvent A (-i)`, and `R(-i) φ₀ = y`
    rw [hRg] at hfin
    simp only [_root_.neg_apply, hy0, map_neg] at hfin
    rw [hPy] at hfin
    rw [hsplit, map_add, map_smul]
    linear_combination (norm := module) -hfin

/-- **A spectral gap gives a resolvent point of the restriction.**  If `B` keeps
its distance `ε` from `lam`, then `lam` is in the resolvent set of the
restriction of `A` to the spectral range of `B`; the inverse is the Borel
calculus of `(κ - lam)⁻¹ 1_B`. -/
theorem mem_resolventSet_specRestrict_of_gap {lam ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ s ∈ B, ε ≤ |s - lam|) :
    (lam : ℂ) ∈ resolventSet (specRestrict hA B hB) := by
  classical
  set hU := isStarNormal_cayley hA with hhU
  set hni := negI_mem_resolventSet hA with hhni
  set κ := cayleyInv hA with hκ
  set S : Set (_root_.spectrum ℂ (cayley hA)) := κ ⁻¹' B with hS
  have hSm : MeasurableSet S := measurable_cayleyInv hA hB
  set ind : _root_.spectrum ℂ (cayley hA) → ℂ := cayleyIndicator hA B with hind
  have hindb : BorelCalculus.IsBddMeasurable ind :=
    BorelCalculus.isBddMeasurable_indicator (a := cayley hA) hSm
  -- the spectral projection *is* this calculus; `specProjection_eq_borelCalculus` is what
  -- replaces unfolding its body, and `IsBddMeasurable` is a `Prop`, so the two admissibility
  -- proofs are interchangeable
  have hP : specProjection hA B hB = BorelCalculus.borelCalculus hU hindb :=
    specProjection_eq_borelCalculus hA B hB
  -- the inverting symbol and its `(κ + i)`-companion
  set f : _root_.spectrum ℂ (cayley hA) → ℂ := gapSymbol hA B lam with hf
  set hsym : _root_.spectrum ℂ (cayley hA) → ℂ :=
    fun w => ((κ w : ℂ) + Complex.I) * f w with hhsym
  have hfb : BorelCalculus.IsBddMeasurable f := by
    rw [hf]
    exact isBddMeasurable_gapSymbol hA B hB hε hgap
  have hhb : BorelCalculus.IsBddMeasurable hsym :=
    isBddMeasurable_cayleyCoord_add_I_mul_gapSymbol hA B hB hε hgap
  -- the resolvent as a Borel-calculus image, and `g = (κ + i)⁻¹` almost everywhere
  -- The canonical resolvent's symbol is `(w - 1)/(2i)`.  The symbol that inverts `κ + i`
  -- pointwise is its negative, `(1 - w)/(2i)`; keep that as the working symbol and record
  -- the sign once, here.
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
  have hgae : ∀ η : H, ∀ᵐ w ∂(BorelCalculus.diagMeasure hU η),
      gsym w * ((κ w : ℂ) + Complex.I) = 1 := by
    intro η
    have hae := MeasureTheory.compl_mem_ae_iff.mpr (diagMeasure_cayley_preimage_one hA η)
    filter_upwards [hae] with w hw
    have hw1 : (w : ℂ) ≠ 1 := hw
    have hgval : gsym w = (2 * Complex.I)⁻¹ * (1 - (w : ℂ)) := by simp [hgsym]
    rw [hgval]
    exact inv_two_I_mul_one_sub_mul_cayleyInv_add_I hA hw1
  -- `R(-i) ∘ T_hsym = T_f`
  have hcomp : BorelCalculus.borelCalculus hU (hgb.mul hhb)
      = BorelCalculus.borelCalculus hU hfb := by
    refine BorelCalculus.borelCalculus_congr_ae hU _ _ fun η => ?_
    filter_upwards [hgae η] with w hw
    -- states the goal with the definition unfolded, in the shape the next step needs.
    change gsym w * (((κ w : ℂ) + Complex.I) * f w) = f w
    rw [← mul_assoc, hw, one_mul]
  set Rop := BorelCalculus.borelCalculus hU hfb with hRop
  have hRopdom : ∀ φ : H,
      Rop φ = -(resolvent A (-Complex.I) (BorelCalculus.borelCalculus hU hhb φ)) := by
    intro φ
    have hx := congrArg (fun L : H →L[ℂ] H => L φ)
      ((BorelCalculus.borelCalculus_mul hU hgb hhb).symm.trans hcomp)
    simp only [_root_.mul_apply_eq_comp] at hx
    rw [← hx, hRg]
    simp only [_root_.neg_apply]
  have hmemdom : ∀ φ : H, Rop φ ∈ A.domain := by
    intro φ
    rw [hRopdom φ]
    exact neg_mem (resolvent_mem_domain hni _)
  have hAeq : ∀ φ : H, A ⟨Rop φ, hmemdom φ⟩
      = BorelCalculus.borelCalculus hU hhb φ - Complex.I • Rop φ := by
    intro φ
    have hsolve := smul_sub_apply_resolvent hni (BorelCalculus.borelCalculus hU hhb φ)
    have hRS : resolvent A (-Complex.I) (BorelCalculus.borelCalculus hU hhb φ) = -(Rop φ) := by
      rw [hRopdom φ]; module
    have hcongr : (⟨resolvent A (-Complex.I) (BorelCalculus.borelCalculus hU hhb φ),
        resolvent_mem_domain hni _⟩ : A.domain) = -(⟨Rop φ, hmemdom φ⟩ : A.domain) :=
      Subtype.ext hRS
    rw [hcongr, _root_.LinearPMap.map_neg, hRS] at hsolve
    linear_combination (norm := module) hsolve
  -- `(A - lam) T_f = E(B)`
  set hsm2 := hfb.const_smul (-(Complex.I + (lam : ℂ))) with hhsm2
  have hidsym : BorelCalculus.borelCalculus hU hindb
      = BorelCalculus.borelCalculus hU (hhb.add hsm2) := by
    refine BorelCalculus.borelCalculus_congr_ae hU _ _ fun η =>
      Filter.Eventually.of_forall fun w =>
        cayleyIndicator_eq_add_smul_gapSymbol hA B hε hgap w
  have hright : ∀ φ : H, A ⟨Rop φ, hmemdom φ⟩ - (lam : ℂ) • Rop φ
      = BorelCalculus.borelCalculus hU hindb φ := by
    intro φ
    rw [hAeq φ, hidsym, BorelCalculus.borelCalculus_add hU hhb hsm2,
      BorelCalculus.borelCalculus_const_smul hU (-(Complex.I + (lam : ℂ))) hfb]
    simp only [_root_.add_apply, _root_.smul_apply, ← hRop]
    module
  -- `T_f` lands in the spectral range: `1_B · f = f`, so `E(B) T_f = T_f`.
  have hKmap : ∀ φ : H, Rop φ ∈ specRange hA B hB := fun φ => by
    have hindf : BorelCalculus.borelCalculus hU (hindb.mul hfb)
        = BorelCalculus.borelCalculus hU hfb :=
      BorelCalculus.borelCalculus_congr_ae hU _ _ fun η =>
        Filter.Eventually.of_forall fun w => cayleyIndicator_mul_gapSymbol hA B w
    have hx := congrArg (fun L : H →L[ℂ] H => L φ)
      ((BorelCalculus.borelCalculus_mul hU hindb hfb).symm.trans hindf)
    simp only [_root_.mul_apply_eq_comp] at hx
    -- through the API lemma, not through the range body: `⟨Rop φ, hx⟩` would need
    -- `specRange` to reduce to a `LinearMap.range`, which is the only thing that kept
    -- that definition exposed.
    exact (mem_specRange_iff hA B hB _).mpr (by rw [hP]; exact hx)
  -- the left inverse
  have hkne : ∀ w : _root_.spectrum ℂ (cayley hA), ((κ w : ℂ) + Complex.I) ≠ 0 :=
    fun w => real_add_I_ne_zero (κ w)
  have hlefts : BorelCalculus.borelCalculus hU
        (hfb.add ((hfb.mul hgb).const_smul (-(Complex.I + (lam : ℂ)))))
      = BorelCalculus.borelCalculus hU (hindb.mul hgb) := by
    refine BorelCalculus.borelCalculus_congr_ae hU _ _ fun η => ?_
    filter_upwards [hgae η] with w hw
    have hgval : gsym w = ((κ w : ℂ) + Complex.I)⁻¹ := by
      field_simp [hkne w]
      linear_combination hw
    rw [hgval]
    exact gapSymbol_left_inverse_pointwise hA B hε hgap (hkne w)
  have hlefts' : Rop + (-(Complex.I + (lam : ℂ)))
        • (Rop * BorelCalculus.borelCalculus hU hgb)
      = BorelCalculus.borelCalculus hU hindb * BorelCalculus.borelCalculus hU hgb := by
    rw [← BorelCalculus.borelCalculus_mul hU hfb hgb,
      ← BorelCalculus.borelCalculus_const_smul hU (-(Complex.I + (lam : ℂ))) (hfb.mul hgb),
      hRop, ← BorelCalculus.borelCalculus_add hU hfb ((hfb.mul hgb).const_smul _),
      ← BorelCalculus.borelCalculus_mul hU hindb hgb]
    exact hlefts
  exact mem_resolventSet_specRestrict_of_bounded_inverse hA B hB lam Rop
    (BorelCalculus.borelCalculus hU hgb) (BorelCalculus.borelCalculus hU hindb)
    hni hP hRg hmemdom hKmap hright hlefts'

end ResolventGap

end LinearPMap
end TauCeti
