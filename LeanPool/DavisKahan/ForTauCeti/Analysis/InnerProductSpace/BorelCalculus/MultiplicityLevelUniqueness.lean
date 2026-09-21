/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.MulLpBorel
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.MultiplicityUniqueness
public import LeanPool.DavisKahan.ForTauCeti.MeasureTheory.MatrixKernelSelection

/-!
# The level sets of a multiplicity datum are determined by the operator

**The level-set half of Hahn--Hellinger uniqueness.**  Together with the measure-class half
(`measureEquiv_base_of_operatorUnitaryEquiv`) this closes the uniqueness of the multiplicity
normal form:

```text
OperatorUnitaryEquiv D.operator E.operator
  →  MeasureEquiv D.base E.base  ∧  ∀ k, D.base (D.level k ∆ E.level k) = 0,
```

the exact converse of `operatorUnitaryEquiv_of_measureEquiv_complex`.

## The invariant, and how the model computes it

The pivot is `SpectralGeneratedLE ha hS m`: the range of the spectral projection of `S` lies in
the closed calculus-span of `m` vectors.  It transfers along unitaries
(`spectralGeneratedLE_of_intertwines`), and on the multiplication model of a datum it counts
slices:

* **Upper bound** (`spectralGeneratedLE_mulLp_datumSymbol`): if `base (S ∩ level k) = 0` then
  `k` generators suffice -- the indicators of the slices `(S ∩ level j) × {j}`, `j < k`.  A
  vector orthogonal to their calculus orbits has, by a duality argument on each slice, sections
  vanishing on `S`, so it is orthogonal to the whole range of the projection.
* **Lower bound** (`not_spectralGeneratedLE_mulLp_datumSymbol`): if `base (S ∩ level k) > 0`
  then `k` generators do *not* suffice.  Given claimed generators `v₁, …, v_k`, the measurable
  kernel selection (`exists_measurable_unit_nullVector`) produces a unit vector field over
  `S ∩ level k` pointwise orthogonal to the `k` sections `(v_i(·, 0), …, v_i(·, k))` in
  `ℂ^{k+1}`; assembled over the `k + 1` slices that all contain `S ∩ level k`, it is a nonzero
  vector fixed by the projection and orthogonal to every orbit.  That contradiction is the
  dimension count `k < k + 1`, done measurably.

Both bounds go through the identification of the model's Borel calculus
(`borelCalculus_comp_val_mulLp`): symbols act as multiplication by `h ∘ symbol`, which is
constant in the slice index -- the reason a slice contributes exactly one generator.

## Main results

* `TauCeti.BorelCalculus.spectralGeneratedLE_mulLp_datumSymbol`: **the upper bound.**
* `TauCeti.BorelCalculus.not_spectralGeneratedLE_mulLp_datumSymbol`: **the lower bound.**
* `TauCeti.BorelCalculus.base_level_symmDiff_eq_zero_of_operatorUnitaryEquiv`: **the level
  sets are unitary invariants.**
* `TauCeti.BorelCalculus.operatorUnitaryEquiv_iff_measureEquiv_and_level`: **Hahn--Hellinger
  uniqueness**, as a biconditional against `operatorUnitaryEquiv_of_measureEquiv_complex`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib and `ForTauCeti`.
-/

public section

open scoped InnerProductSpace ENNReal

open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti
namespace BorelCalculus

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {a : H →L[ℂ] H}

/-- **Membership in the closed calculus-span, by duality.**  A vector lies in the closed
calculus-span of the `v i` as soon as every vector orthogonal to all their calculus orbits is
orthogonal to it. -/
theorem mem_closure_iSup_cyclicSubspace_of_forall_inner (ha : IsStarNormal a) {ι : Type*}
    (v : ι → H) {y : H}
    (h : ∀ w : H,
      (∀ (i : ι) (f : spectrum ℂ a → ℂ) (hf : IsBddMeasurable f),
        ⟪borelCalculus ha hf (v i), w⟫_ℂ = 0) → ⟪w, y⟫_ℂ = 0) :
    y ∈ (⨆ i, cyclicSubspace ha (v i)).topologicalClosure := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
  intro w hw
  refine h w fun i f hf => ?_
  exact (Submodule.mem_orthogonal _ w).mp hw _
    (le_iSup (fun i => cyclicSubspace ha (v i)) i
      (borelCalculus_apply_mem_cyclicSubspace ha hf (v i)))

/-- A vector orthogonal to every calculus orbit of the `v i` is orthogonal to their closed
calculus-span.  Converse companion to `mem_closure_iSup_cyclicSubspace_of_forall_inner`. -/
theorem inner_eq_zero_of_mem_closure_iSup_cyclicSubspace (ha : IsStarNormal a) {ι : Type*}
    (v : ι → H) {w : H}
    (hw : ∀ (i : ι) (f : spectrum ℂ a → ℂ) (hf : IsBddMeasurable f),
      ⟪w, borelCalculus ha hf (v i)⟫_ℂ = 0)
    {x : H} (hx : x ∈ (⨆ i, cyclicSubspace ha (v i)).topologicalClosure) :
    ⟪w, x⟫_ℂ = 0 := by
  have hker : (⨆ i, cyclicSubspace ha (v i)).topologicalClosure
      ≤ LinearMap.ker ((innerSL ℂ w : H →L[ℂ] ℂ) : H →ₗ[ℂ] ℂ) := by
    refine Submodule.topologicalClosure_minimal _ (iSup_le fun i => ?_)
      (ContinuousLinearMap.isClosed_ker _)
    refine cyclicSubspace_le ha (ContinuousLinearMap.isClosed_ker _) fun f hf => ?_
    rw [LinearMap.mem_ker]
    simpa using hw i f hf
  have hmem := hker hx
  rw [LinearMap.mem_ker] at hmem
  simpa using hmem

end Hilbert

section Duality

variable {X : Type*} [MeasurableSpace X]

/-- **The duality detector for vanishing.**  An integrable function whose pairings against
every bounded measurable test function vanish is almost everywhere zero.  The test functions
used are the truncations of the function itself. -/
theorem ae_eq_zero_of_forall_integral_conj_mul (ν : Measure X) {φ : X → ℂ}
    (hφm : Measurable φ) (hφi : Integrable φ ν)
    (h0 : ∀ h : X → ℂ, Measurable h → (∃ C, ∀ z, ‖h z‖ ≤ C) →
      ∫ z, (starRingEnd ℂ) (h z) * φ z ∂ν = 0) :
    ∀ᵐ z ∂ν, φ z = 0 := by
  have hA : ∀ n : ℕ, ∀ᵐ z ∂ν, ‖φ z‖ ≤ (n : ℝ) → φ z = 0 := by
    intro n
    have hAm : MeasurableSet {z | ‖φ z‖ ≤ (n : ℝ)} :=
      measurableSet_le hφm.norm measurable_const
    have hbound : ∀ z, ‖{z | ‖φ z‖ ≤ (n : ℝ)}.indicator φ z‖ ≤ (n : ℝ) := by
      intro z
      by_cases hz : z ∈ {z | ‖φ z‖ ≤ (n : ℝ)}
      · rw [Set.indicator_of_mem hz]
        exact hz
      · rw [Set.indicator_of_notMem hz, norm_zero]
        positivity
    have htest := h0 _ (hφm.indicator hAm) ⟨(n : ℝ), hbound⟩
    have hint : ∀ z, (starRingEnd ℂ) ({z | ‖φ z‖ ≤ (n : ℝ)}.indicator φ z) * φ z
        = (({z | ‖φ z‖ ≤ (n : ℝ)}.indicator (fun z => ‖φ z‖ ^ 2) z : ℝ) : ℂ) := by
      intro z
      by_cases hz : z ∈ {z | ‖φ z‖ ≤ (n : ℝ)}
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, RCLike.conj_mul]
        push_cast
        exact rfl
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, map_zero, zero_mul,
          Complex.ofReal_zero]
    rw [integral_congr_ae (Filter.Eventually.of_forall hint), integral_complex_ofReal] at htest
    have hr0 : ∫ z, {z | ‖φ z‖ ≤ (n : ℝ)}.indicator (fun z => ‖φ z‖ ^ 2) z ∂ν = 0 := by
      exact_mod_cast htest
    have hrint : Integrable ({z | ‖φ z‖ ≤ (n : ℝ)}.indicator fun z => ‖φ z‖ ^ 2) ν := by
      refine Integrable.mono' (hφi.norm.const_mul (n : ℝ))
        ((hφm.norm.pow_const 2).indicator hAm).aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs]
      by_cases hz : z ∈ {z | ‖φ z‖ ≤ (n : ℝ)}
      · rw [Set.indicator_of_mem hz, abs_of_nonneg (by positivity), pow_two]
        exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
      · rw [Set.indicator_of_notMem hz, abs_zero]
        positivity
    have hae := (integral_eq_zero_iff_of_nonneg
      (Set.indicator_nonneg fun z _ => by positivity) hrint).mp hr0
    filter_upwards [hae] with z hz hzn
    have hzmem : z ∈ {z | ‖φ z‖ ≤ (n : ℝ)} := hzn
    rw [Pi.zero_apply, Set.indicator_of_mem hzmem] at hz
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hz)
  have hall := ae_all_iff.mpr hA
  filter_upwards [hall] with z hz
  obtain ⟨n, hn⟩ := exists_nat_ge ‖φ z‖
  exact hz n hn

end Duality

section Slice

variable {X : Type*} [MeasurableSpace X]

/-- Finiteness of the `L²` seminorm, phrased through the quadratic Lebesgue integral. -/
theorem eLpNorm_two_lt_top_iff_lintegral (ν : Measure X) (f : X → ℂ)
    (hf : AEStronglyMeasurable f ν) :
    eLpNorm f 2 ν < ∞ ↔ ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν < ∞ := by
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num) hf]
  have h2 : ((2 : ℝ≥0∞)).toReal = ((2 : ℕ) : ℝ) := by norm_num
  rw [h2]
  refine Iff.of_eq (congrArg (· < ∞) (lintegral_congr fun x => ?_))
  rw [ENNReal.rpow_natCast]

/-- A square-integrable function on a slice sum has square-integrable sections. -/
theorem memLp_two_section {ν : ℕ → Measure X} {f : X × ℕ → ℂ} (hm : Measurable f)
    (hf : ∫⁻ p, ‖f p‖ₑ ^ 2 ∂(sliceSum ν) < ∞) (n : ℕ) :
    MemLp (fun z => f (z, n)) 2 (ν n) := by
  rw [MemLp, eLpNorm_two_lt_top_iff_lintegral (ν n) (fun z => f (z, n))
    (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable]
  rw [lintegral_sliceSum ν (hm.enorm.pow_const 2)] at hf
  exact (ENNReal.le_tsum n).trans_lt hf

/-- Every `L²` element admits a genuinely measurable representative with finite quadratic
Lebesgue integral.  The almost-everywhere representative of the class is only almost
everywhere strongly measurable; the slice arguments below need honest measurability. -/
theorem exists_measurable_rep_lp_two (ν : Measure X) (F : Lp ℂ 2 ν) :
    ∃ f : X → ℂ, Measurable f ∧ (F : X → ℂ) =ᵐ[ν] f ∧ ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν < ∞ := by
  refine ⟨(Lp.aestronglyMeasurable F).mk (F : X → ℂ),
    (Lp.aestronglyMeasurable F).stronglyMeasurable_mk.measurable,
    (Lp.aestronglyMeasurable F).ae_eq_mk, ?_⟩
  have hcongr : ∫⁻ x, ‖(Lp.aestronglyMeasurable F).mk (F : X → ℂ) x‖ₑ ^ 2 ∂ν
      = ∫⁻ x, ‖(F : X → ℂ) x‖ₑ ^ 2 ∂ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [(Lp.aestronglyMeasurable F).ae_eq_mk] with x hx
    rw [hx]
  rw [hcongr]
  exact lintegral_enorm_sq_lt_top ν F

end Slice

section Model

/-- **The matrix element of a symbol acting on the model, decomposed into slices.**  The symbol
acts through the first coordinate only, so each slice contributes a separate integral against
the corresponding restriction of the base measure. -/
theorem inner_mulLp_comp_eq_tsum (D : MultiplicityDatum ℂ) {h : ℂ → ℂ} (hm : Measurable h)
    {C : ℝ} (hC : ∀ z, ‖h z‖ ≤ C) (V W : Lp ℂ 2 D.measure) {vb wb : ℂ × ℕ → ℂ}
    (hvb : (V : ℂ × ℕ → ℂ) =ᵐ[D.measure] vb) (hwb : (W : ℂ × ℕ → ℂ) =ᵐ[D.measure] wb) :
    ⟪mulLp D.measure (hm.comp (measurable_datumSymbol D))
        (fun p => hC (datumSymbol D p)) V, W⟫_ℂ
      = ∑' n, ∫ z, (starRingEnd ℂ) (h z * vb (z, n)) * wb (z, n)
          ∂(D.base.restrict (D.level n)) := by
  have hae : ∀ᵐ p ∂D.measure,
      (starRingEnd ℂ) (h (datumSymbol D p) * (V : ℂ × ℕ → ℂ) p) * (W : ℂ × ℕ → ℂ) p
        = (starRingEnd ℂ) (h p.1 * vb p) * wb p := by
    filter_upwards [ae_datumSymbol_eq_fst D, hvb, hwb] with p h1 h2 h3
    rw [h1, h2, h3]
  have hJint : Integrable (fun p => (starRingEnd ℂ) (h p.1 * vb p) * wb p) D.measure := by
    have hI := MeasureTheory.L2.integrable_inner (𝕜 := ℂ)
      (mulLp D.measure (hm.comp (measurable_datumSymbol D))
        (fun p => hC (datumSymbol D p)) V) W
    refine hI.congr ?_
    filter_upwards [coeFn_mulLp D.measure (hm.comp (measurable_datumSymbol D))
      (fun p => hC (datumSymbol D p)) V, hae] with p h1 h2
    rw [RCLike.inner_apply, h1, ← h2]
    simp only [Function.comp_apply]
    ring
  calc ⟪mulLp D.measure (hm.comp (measurable_datumSymbol D))
        (fun p => hC (datumSymbol D p)) V, W⟫_ℂ
      = ∫ p, (starRingEnd ℂ) (h (datumSymbol D p) * (V : ℂ × ℕ → ℂ) p)
          * (W : ℂ × ℕ → ℂ) p ∂D.measure :=
        inner_mulLp_left D.measure (hm.comp (measurable_datumSymbol D))
          (fun p => hC (datumSymbol D p)) V W
    _ = ∫ p, (starRingEnd ℂ) (h p.1 * vb p) * wb p ∂D.measure := integral_congr_ae hae
    _ = ∑' n, ∫ z, (starRingEnd ℂ) (h z * vb (z, n)) * wb (z, n)
          ∂(D.base.restrict (D.level n)) := by
        rw [MultiplicityDatum.measure_def] at hJint ⊢
        exact integral_sliceSum _ hJint

/-- Beyond the critical index, the slice restrictions give the spectral subset no mass. -/
theorem restrict_level_inter_eq_zero (E : MultiplicityDatum ℂ) {S : Set ℂ}
    (hS : MeasurableSet S) {k n : ℕ} (hkn : k ≤ n)
    (hnull : E.base (S ∩ E.level k) = 0) :
    (E.base.restrict (E.level n)) (S ∩ E.level n) = 0 := by
  rw [Measure.restrict_apply (hS.inter (E.measurableSet_level n))]
  refine measure_mono_null (fun z hz => ?_) hnull
  exact ⟨hz.1.1, E.antitone_level hkn hz.1.2⟩

/-- **The upper bound: off the `k`-th level set, the model is generated by `k` vectors.**

If `S` meets `level k` in a null set, the indicators of the slices `(S ∩ level j) × {j}` for
`j < k` generate the range of the spectral projection of `S`: a vector orthogonal to their
calculus orbits has, slice by slice, sections vanishing on `S` -- by duality against every
bounded Borel symbol on the low slices, and because `S` itself is negligible on the high
ones. -/
theorem spectralGeneratedLE_mulLp_datumSymbol (E : MultiplicityDatum ℂ) {S : Set ℂ}
    (hS : MeasurableSet S) {k : ℕ} (hnull : E.base (S ∩ E.level k) = 0) :
    SpectralGeneratedLE
      (isStarNormal_mulLp E.measure (measurable_datumSymbol E) (norm_datumSymbol_le E))
      hS k := by
  classical
  have hAm : ∀ j : Fin k, MeasurableSet ((S ∩ E.level j) ×ˢ ({(j : ℕ)} : Set ℕ)) := fun j =>
    (hS.inter (E.measurableSet_level j)).prod (measurableSet_singleton _)
  have hAfin : ∀ j : Fin k, E.measure ((S ∩ E.level j) ×ˢ ({(j : ℕ)} : Set ℕ)) ≠ ∞ := by
    intro j
    rw [MultiplicityDatum.measure_def, sliceSum_apply _ (hAm j)]
    rw [tsum_eq_single (j : ℕ) ?_]
    · exact ne_of_lt (lt_of_le_of_lt (measure_mono (Set.subset_univ _)) (measure_lt_top _ _))
    · intro n hn
      convert measure_empty (μ := E.base.restrict (E.level n))
      refine Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
      simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_singleton_iff] at hz
      exact hn hz.2
  refine spectralGeneratedLE_of_generators
    (fun j => indicatorConstLp 2 (hAm j) (hAfin j) (1 : ℂ)) fun x => ?_
  refine mem_closure_iSup_cyclicSubspace_of_forall_inner _ _ fun w hw => ?_
  obtain ⟨wb, hwbm, hwb, hwbint⟩ := exists_measurable_rep_lp_two E.measure w
  -- Slice sections of `w` vanish on `S`: duality on the low slices.
  have hker : ∀ j : Fin k, ∀ᵐ z ∂(E.base.restrict (E.level j)),
      (S ∩ E.level j).indicator (fun _ => (1 : ℂ)) z * wb (z, (j : ℕ)) = 0 := by
    intro j
    have hwsec : MemLp (fun z => wb (z, (j : ℕ))) 2 (E.base.restrict (E.level j)) := by
      refine memLp_two_section (ν := fun n => E.base.restrict (E.level n)) hwbm ?_ (j : ℕ)
      rwa [← MultiplicityDatum.measure_def]
    refine ae_eq_zero_of_forall_integral_conj_mul _
      ((measurable_const.indicator (hS.inter (E.measurableSet_level j))).mul
        (hwbm.comp (measurable_id.prodMk measurable_const))) ?_ ?_
    · refine Integrable.mono' (hwsec.integrable one_le_two).norm
        ((measurable_const.indicator (hS.inter (E.measurableSet_level j))).mul
          (hwbm.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => ?_)
      rw [norm_mul]
      by_cases hz : z ∈ S ∩ E.level j
      · rw [Set.indicator_of_mem hz, norm_one, one_mul]
      · rw [Set.indicator_of_notMem hz, norm_zero, zero_mul]
        exact norm_nonneg _
    · rintro h hm ⟨C, hC⟩
      have horbit : ⟪mulLp E.measure (hm.comp (measurable_datumSymbol E))
          (fun p => hC (datumSymbol E p))
          (indicatorConstLp 2 (hAm j) (hAfin j) (1 : ℂ)), w⟫_ℂ = 0 := by
        rw [← borelCalculus_comp_val_mulLp E.measure (measurable_datumSymbol E)
          (norm_datumSymbol_le E) hm hC (hm.comp (measurable_datumSymbol E))
          (fun p => hC (datumSymbol E p)) (Filter.Eventually.of_forall fun p => rfl)]
        exact hw j _ (isBddMeasurable_comp_val hm hC)
      rw [inner_mulLp_comp_eq_tsum E hm hC _ w indicatorConstLp_coeFn hwb] at horbit
      rw [tsum_eq_single (j : ℕ) ?_] at horbit
      · rw [← horbit]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        by_cases hz : z ∈ S ∩ E.level j
        · have hmem : ((z, (j : ℕ)) : ℂ × ℕ) ∈ (S ∩ E.level j) ×ˢ ({(j : ℕ)} : Set ℕ) :=
            ⟨hz, rfl⟩
          simp only [Set.indicator_of_mem hz, Set.indicator_of_mem hmem, one_mul, mul_one]
        · have hnot : ((z, (j : ℕ)) : ℂ × ℕ) ∉ (S ∩ E.level j) ×ˢ ({(j : ℕ)} : Set ℕ) :=
            fun hmem => hz hmem.1
          simp only [Set.indicator_of_notMem hz, Set.indicator_of_notMem hnot, zero_mul,
            mul_zero, map_zero]
      · intro n hn
        refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun z => ?_)
        have hnot : ((z, n) : ℂ × ℕ) ∉ (S ∩ E.level j) ×ˢ ({(j : ℕ)} : Set ℕ) := by
          rintro ⟨-, hmem2⟩
          exact hn hmem2
        simp only [Pi.zero_apply, Set.indicator_of_notMem hnot, mul_zero, map_zero, zero_mul]
  -- Assemble the sections into one statement over the model measure.
  have hsecall : ∀ᵐ p ∂E.measure, p.1 ∈ S → wb p = 0 := by
    rw [MultiplicityDatum.measure_def]
    refine ae_sliceSum_of_forall fun n => ?_
    by_cases hnk : n < k
    · filter_upwards [hker ⟨n, hnk⟩, ae_restrict_mem (E.measurableSet_level n)]
        with z hz hzlvl hzS
      have hzmem : z ∈ S ∩ E.level n := ⟨hzS, hzlvl⟩
      rwa [Set.indicator_of_mem hzmem, one_mul] at hz
    · rw [not_lt] at hnk
      have h0 := restrict_level_inter_eq_zero E hS hnk hnull
      have hnotS : ∀ᵐ z ∂(E.base.restrict (E.level n)), z ∉ S ∩ E.level n := by
        rw [ae_iff]
        simp only [not_not, Set.ofPred_mem_eq]
        exact h0
      filter_upwards [hnotS, ae_restrict_mem (E.measurableSet_level n)] with z hz hzlvl hzS
      exact absurd ⟨hzS, hzlvl⟩ hz
  -- Hence `w` is orthogonal to the range of the projection.
  rw [← inner_conj_symm]
  suffices hPx : ⟪specProjC (isStarNormal_mulLp E.measure (measurable_datumSymbol E)
      (norm_datumSymbol_le E)) hS x, w⟫_ℂ = 0 by
    rw [hPx, map_zero]
  rw [specProjC_mulLp E.measure (measurable_datumSymbol E) (norm_datumSymbol_le E) hS,
    inner_mulLp_left]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ae_datumSymbol_eq_fst E, hwb, hsecall] with p h1 h2 h3
  rw [Pi.zero_apply, Function.comp_apply, h1, h2]
  by_cases hp : p.1 ∈ S
  · rw [h3 hp, mul_zero]
  · rw [Set.indicator_of_notMem hp, zero_mul, map_zero, zero_mul]

/-- The measurable unit defect direction has exactly the mass of its supporting level. -/
private theorem defect_vector_mass (D : MultiplicityDatum ℂ) {S : Set ℂ} {k : ℕ}
    (hS'm : MeasurableSet (S ∩ D.level k)) (w₀ : ℂ → Fin (k + 1) → ℂ)
    (hw₀m : ∀ j, Measurable fun z => w₀ z j)
    (hw₀unit : ∀ z, ∑ j, ‖w₀ z j‖ ^ 2 = 1)
    (W : ℂ × ℕ → ℂ) (hWm : Measurable W)
    (hWval : ∀ (z : ℂ) (n : ℕ) (hn : n < k + 1),
      W (z, n) = (S ∩ D.level k).indicator (fun z => w₀ z ⟨n, hn⟩) z)
    (hWval' : ∀ (z : ℂ) (n : ℕ), k < n → W (z, n) = 0) :
    ∫⁻ p, ‖W p‖ₑ ^ 2 ∂D.measure = D.base (S ∩ D.level k) := by
  classical
  have hrestr : ∀ j : Fin (k + 1),
      (D.base.restrict (D.level (j : ℕ))).restrict (S ∩ D.level k)
        = D.base.restrict (S ∩ D.level k) := by
    intro j
    rw [Measure.restrict_restrict hS'm]
    congr 1
    refine Set.inter_eq_self_of_subset_left fun z hz => ?_
    have hjk : (j : ℕ) ≤ k := by
      have := j.isLt
      omega
    exact D.antitone_level hjk hz.2
  rw [MultiplicityDatum.measure_def, lintegral_sliceSum _ (hWm.enorm.pow_const 2)]
  have hterm : ∀ j : Fin (k + 1),
      ∫⁻ z, ‖W (z, (j : ℕ))‖ₑ ^ 2 ∂(D.base.restrict (D.level (j : ℕ)))
        = ∫⁻ z, ‖w₀ z j‖ₑ ^ 2 ∂(D.base.restrict (S ∩ D.level k)) := by
    intro j
    have hpt : ∀ z, ‖W (z, (j : ℕ))‖ₑ ^ 2
        = (S ∩ D.level k).indicator (fun z => ‖w₀ z j‖ₑ ^ 2) z := by
      intro z
      rw [hWval z (j : ℕ) j.isLt, Fin.eta]
      by_cases hz : z ∈ S ∩ D.level k
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, enorm_zero]
        simp
    rw [lintegral_congr hpt, lintegral_indicator hS'm, ← hrestr j]
  rw [tsum_eq_sum (s := Finset.range (k + 1)) ?_, ← Fin.sum_univ_eq_sum_range]
  · have hstep : ∀ j : Fin (k + 1),
        ∫⁻ z, ‖W (z, (j : ℕ))‖ₑ ^ 2 ∂(D.base.restrict (D.level (j : ℕ)))
          = ∫⁻ z, ‖w₀ z j‖ₑ ^ 2 ∂(D.base.restrict (S ∩ D.level k)) := hterm
    rw [Finset.sum_congr rfl fun j _ => hstep j, ← lintegral_finsetSum _
      (fun j _ => (hw₀m j).enorm.pow_const 2)]
    have hone : ∀ z, (∑ j : Fin (k + 1), ‖w₀ z j‖ₑ ^ 2) = 1 := by
      intro z
      have h2 : ∀ j : Fin (k + 1), ‖w₀ z j‖ₑ ^ 2 = ENNReal.ofReal (‖w₀ z j‖ ^ 2) := by
        intro j
        rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      rw [Finset.sum_congr rfl fun j _ => h2 j,
        ← ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity, hw₀unit z,
        ENNReal.ofReal_one]
    rw [lintegral_congr hone, setLIntegral_one]
  · intro n hn
    have hkn : k < n := by
      simp only [Finset.mem_range, not_lt] at hn
      omega
    have hzero : ∀ z : ℂ, ‖W (z, n)‖ₑ ^ 2 = 0 := by
      intro z
      rw [hWval' z n hkn]
      simp
    rw [lintegral_congr hzero, lintegral_zero]

/-- **The lower bound: on the `k`-th level set, `k` generators never suffice.**

If `S` meets `level k` in a set of positive measure, no `k` vectors generate the range of the
spectral projection of `S`.  The witness against any claimed generators is assembled by the
measurable kernel selection: over `S ∩ level k`, a pointwise unit vector in `ℂ^{k+1}`
orthogonal to the `k` generator sections, spread over the `k + 1` lowest slices -- all of which
carry `S ∩ level k` with full base measure.  The result is a nonzero vector fixed by the
projection and orthogonal to every calculus orbit of the generators, which is absurd. -/
theorem not_spectralGeneratedLE_mulLp_datumSymbol (D : MultiplicityDatum ℂ) {S : Set ℂ}
    (hS : MeasurableSet S) {k : ℕ} (hpos : D.base (S ∩ D.level k) ≠ 0) :
    ¬ SpectralGeneratedLE
      (isStarNormal_mulLp D.measure (measurable_datumSymbol D) (norm_datumSymbol_le D))
      hS k := by
  classical
  intro hgen
  obtain ⟨v, hv⟩ := hgen.exists_generators
  have hS'm : MeasurableSet (S ∩ D.level k) := hS.inter (D.measurableSet_level k)
  choose vb hvbm hvb hvbint using fun i : Fin k =>
    exists_measurable_rep_lp_two D.measure (v i)
  -- The pointwise defect direction, chosen measurably.
  obtain ⟨w₀, hw₀m, hw₀unit, hw₀ker⟩ := exists_measurable_unit_nullVector
    (Nat.lt_succ_self k)
    (A := fun z => Matrix.of fun (i : Fin k) (j : Fin (k + 1)) =>
      (starRingEnd ℂ) (vb i (z, (j : ℕ))))
    (fun i j => Complex.continuous_conj.measurable.comp
      ((hvbm i).comp (measurable_id.prodMk measurable_const)))
  -- The defect vector on the model: the selection over `S ∩ level k`, one copy per low slice.
  set W : ℂ × ℕ → ℂ := fun p => ∑ j : Fin (k + 1),
    (slice (j : ℕ)).indicator (fun q => (S ∩ D.level k).indicator (fun z => w₀ z j) q.1) p
    with hWdef
  have hWm : Measurable W := by
    refine Finset.measurable_sum _ fun j _ => ?_
    exact (((hw₀m j).indicator hS'm).comp measurable_fst).indicator
      (measurableSet_slice (j : ℕ))
  have hWval : ∀ (z : ℂ) (n : ℕ) (hn : n < k + 1),
      W (z, n) = (S ∩ D.level k).indicator (fun z => w₀ z ⟨n, hn⟩) z := by
    intro z n hn
    have hterm : ∀ j : Fin (k + 1),
        (slice (j : ℕ)).indicator
          (fun q => (S ∩ D.level k).indicator (fun z => w₀ z j) q.1) (z, n)
        = if j = ⟨n, hn⟩ then (S ∩ D.level k).indicator (fun z => w₀ z j) z else 0 := by
      intro j
      by_cases hj : j = ⟨n, hn⟩
      · subst hj
        rw [ite_eq_left rfl]
        exact Set.indicator_of_mem
          (show ((z, n) : ℂ × ℕ) ∈ slice ((⟨n, hn⟩ : Fin (k + 1)) : ℕ) from
            mem_slice.mpr rfl) _
      · rw [ite_eq_right hj]
        refine Set.indicator_of_notMem (fun hmem => hj ?_) _
        rw [mem_slice] at hmem
        exact Fin.ext hmem.symm
    simp only [hWdef]
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_ite_eq' Finset.univ,
      ite_eq_left (Finset.mem_univ _)]
  have hWval' : ∀ (z : ℂ) (n : ℕ), k < n → W (z, n) = 0 := by
    intro z n hn
    simp only [hWdef]
    refine Finset.sum_eq_zero fun j _ => ?_
    refine Set.indicator_of_notMem (fun hmem => ?_) _
    rw [mem_slice] at hmem
    have := j.isLt
    omega
  have hWsupp : ∀ p : ℂ × ℕ, W p ≠ 0 → p.1 ∈ S ∩ D.level k := by
    intro p hp
    simp only [hWdef] at hp
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
    by_contra hp1
    refine hj ?_
    by_cases hmem : p ∈ slice (j : ℕ)
    · rw [Set.indicator_of_mem hmem]
      exact Set.indicator_of_notMem hp1 _
    · exact Set.indicator_of_notMem hmem _
  -- The squared mass of the defect vector is exactly the mass of `S ∩ level k`.
  have hrestr : ∀ j : Fin (k + 1),
      (D.base.restrict (D.level (j : ℕ))).restrict (S ∩ D.level k)
        = D.base.restrict (S ∩ D.level k) := by
    intro j
    rw [Measure.restrict_restrict hS'm]
    congr 1
    refine Set.inter_eq_self_of_subset_left fun z hz => ?_
    have hjk : (j : ℕ) ≤ k := by
      have := j.isLt
      omega
    exact D.antitone_level hjk hz.2
  have hlint : ∫⁻ p, ‖W p‖ₑ ^ 2 ∂D.measure = D.base (S ∩ D.level k) :=
    defect_vector_mass D hS'm w₀ hw₀m hw₀unit W hWm hWval hWval'
  have hW2 : MemLp W 2 D.measure := by
    rw [MemLp, eLpNorm_two_lt_top_iff_lintegral _ _ hWm.aestronglyMeasurable, hlint]
    exact measure_lt_top _ _
  set w : Lp ℂ 2 D.measure := hW2.toLp W with hwdef
  have hwcoe : (w : ℂ × ℕ → ℂ) =ᵐ[D.measure] W := hW2.coeFn_toLp
  -- The defect vector is fixed by the spectral projection of `S`.
  have hPw : specProjC (isStarNormal_mulLp D.measure (measurable_datumSymbol D)
      (norm_datumSymbol_le D)) hS w = w := by
    rw [specProjC_mulLp D.measure (measurable_datumSymbol D) (norm_datumSymbol_le D) hS]
    refine Lp.ext ?_
    filter_upwards [coeFn_mulLp D.measure ((measurable_indicator_one hS).comp
      (measurable_datumSymbol D)) (fun p => norm_indicator_one_le (datumSymbol D p)) w,
      hwcoe, ae_datumSymbol_eq_fst D] with p h1 h2 h3
    rw [h1, Function.comp_apply, h3, h2]
    by_cases hW0 : W p = 0
    · rw [hW0, mul_zero]
    · rw [Set.indicator_of_mem (hWsupp p hW0).1, one_mul]
  -- The defect vector is nonzero.
  have hne : w ≠ 0 := by
    intro h0
    have hW0 : W =ᵐ[D.measure] 0 := by
      refine hwcoe.symm.trans ?_
      rw [h0]
      exact Lp.coeFn_zero ℂ 2 D.measure
    have h1 : ∫⁻ p, ‖W p‖ₑ ^ 2 ∂D.measure = ∫⁻ _, 0 ∂D.measure := by
      refine lintegral_congr_ae ?_
      filter_upwards [hW0] with p hp
      rw [hp]
      simp
    rw [lintegral_zero, hlint] at h1
    exact hpos h1
  -- The defect vector is orthogonal to every calculus orbit of the generators.
  have horth : ∀ (i : Fin k)
      (f : spectrum ℂ (mulLp D.measure (measurable_datumSymbol D)
        (norm_datumSymbol_le D)) → ℂ) (hf : IsBddMeasurable f),
      ⟪w, borelCalculus (isStarNormal_mulLp D.measure (measurable_datumSymbol D)
        (norm_datumSymbol_le D)) hf (v i)⟫_ℂ = 0 := by
    intro i f hf
    obtain ⟨h, hm, hC, hgeq⟩ := exists_comp_val_eq hf
    have hfeq : f = fun ww : spectrum ℂ (mulLp D.measure (measurable_datumSymbol D)
        (norm_datumSymbol_le D)) => h (ww : ℂ) := funext hgeq
    subst hfeq
    have hbc : borelCalculus (isStarNormal_mulLp D.measure (measurable_datumSymbol D)
        (norm_datumSymbol_le D)) hf (v i)
        = mulLp D.measure (hm.comp (measurable_datumSymbol D))
            (fun p => hC (datumSymbol D p)) (v i) := by
      have hlem := borelCalculus_comp_val_mulLp D.measure (measurable_datumSymbol D)
        (norm_datumSymbol_le D) hm hC (hm.comp (measurable_datumSymbol D))
        (fun p => hC (datumSymbol D p)) (Filter.Eventually.of_forall fun p => rfl)
      exact congrArg (fun T : Lp ℂ 2 D.measure →L[ℂ] Lp ℂ 2 D.measure => T (v i)) hlem
    -- integrability of each slice term
    have hsecint : ∀ j : Fin (k + 1), Integrable
        (fun z => (starRingEnd ℂ) (h z * vb i (z, (j : ℕ))) * w₀ z j)
        (D.base.restrict (S ∩ D.level k)) := by
      intro j
      have hsec : MemLp (fun z => vb i (z, (j : ℕ))) 2
          (D.base.restrict (D.level (j : ℕ))) := by
        refine memLp_two_section (ν := fun n => D.base.restrict (D.level n)) (hvbm i) ?_
          (j : ℕ)
        rw [← MultiplicityDatum.measure_def]
        exact hvbint i
      have hsec' : MemLp (fun z => vb i (z, (j : ℕ))) 2
          (D.base.restrict (S ∩ D.level k)) := by
        have := hsec.restrict (S ∩ D.level k)
        rwa [hrestr j] at this
      refine Integrable.mono' ((hsec'.integrable one_le_two).norm.const_mul
        hf.chooseBound) ?_ (Filter.Eventually.of_forall fun z => ?_)
      · refine Measurable.aestronglyMeasurable ?_
        refine Measurable.mul ?_ ((hw₀m j).comp measurable_id)
        exact Complex.continuous_conj.measurable.comp
          ((hm.mul ((hvbm i).comp (measurable_id.prodMk measurable_const))))
      · rw [norm_mul, RCLike.norm_conj, norm_mul]
        have hw₀le : ‖w₀ z j‖ ≤ 1 := by
          have h1 := hw₀unit z
          have h2 : ‖w₀ z j‖ ^ 2 ≤ 1 := by
            rw [← h1]
            exact Finset.single_le_sum (f := fun j => ‖w₀ z j‖ ^ 2)
              (fun i _ => by positivity) (Finset.mem_univ j)
          nlinarith [norm_nonneg (w₀ z j)]
        calc ‖h z‖ * ‖vb i (z, (j : ℕ))‖ * ‖w₀ z j‖
            ≤ hf.chooseBound * ‖vb i (z, (j : ℕ))‖ * 1 := by
              refine mul_le_mul (mul_le_mul_of_nonneg_right (hC z) (norm_nonneg _))
                hw₀le (norm_nonneg _) ?_
              exact mul_nonneg hf.chooseBound_nonneg (norm_nonneg _)
          _ = hf.chooseBound * ‖vb i (z, (j : ℕ))‖ := by ring
    -- the slice sum vanishes by the pointwise kernel property
    have htsum : (∑' n, ∫ z, (starRingEnd ℂ) (h z * vb i (z, n)) * W (z, n)
        ∂(D.base.restrict (D.level n))) = 0 := by
      rw [tsum_eq_sum (s := Finset.range (k + 1)) ?_, ← Fin.sum_univ_eq_sum_range]
      · have hterm : ∀ j : Fin (k + 1),
            ∫ z, (starRingEnd ℂ) (h z * vb i (z, (j : ℕ))) * W (z, (j : ℕ))
              ∂(D.base.restrict (D.level (j : ℕ)))
            = ∫ z, (starRingEnd ℂ) (h z * vb i (z, (j : ℕ))) * w₀ z j
              ∂(D.base.restrict (S ∩ D.level k)) := by
          intro j
          have hpt : ∀ z, (starRingEnd ℂ) (h z * vb i (z, (j : ℕ))) * W (z, (j : ℕ))
              = (S ∩ D.level k).indicator
                  (fun z => (starRingEnd ℂ) (h z * vb i (z, (j : ℕ))) * w₀ z j) z := by
            intro z
            rw [hWval z (j : ℕ) j.isLt, Fin.eta]
            by_cases hz : z ∈ S ∩ D.level k
            · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
            · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero]
          rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
            integral_indicator hS'm, ← hrestr j]
        rw [Finset.sum_congr rfl fun j _ => hterm j,
          ← integral_finsetSum _ fun j _ => hsecint j]
        refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun z => ?_)
        change (∑ j : Fin (k + 1), (starRingEnd ℂ) (h z * vb i (z, (j : ℕ))) * w₀ z j) = 0
        have hker := hw₀ker z i
        simp only [Matrix.of_apply] at hker
        have hfactor : ∀ j : Fin (k + 1),
            (starRingEnd ℂ) (h z * vb i (z, (j : ℕ))) * w₀ z j
              = (starRingEnd ℂ) (h z) * ((starRingEnd ℂ) (vb i (z, (j : ℕ))) * w₀ z j) := by
          intro j
          rw [map_mul]
          ring
        rw [Finset.sum_congr rfl fun j _ => hfactor j, ← Finset.mul_sum, hker, mul_zero]
      · intro n hn
        have hkn : k < n := by
          simp only [Finset.mem_range, not_lt] at hn
          omega
        refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun z => ?_)
        change (starRingEnd ℂ) (h z * vb i (z, n)) * W (z, n) = 0
        rw [hWval' z n hkn, mul_zero]
    rw [← inner_conj_symm, hbc,
      inner_mulLp_comp_eq_tsum D hm hC (v i) w (hvb i) hwcoe, htsum, map_zero]
  -- Contradiction: the defect vector is orthogonal to a closed span containing itself.
  have hin := hv w
  rw [hPw] at hin
  have hzero := inner_eq_zero_of_mem_closure_iSup_cyclicSubspace _ v horth hin
  rw [inner_self_eq_zero] at hzero
  exact hne hzero

/-- One half of the level-set comparison: what `D` claims above level `k`, `E` must claim
too, up to a null set. -/
theorem base_level_diff_eq_zero_of_operatorUnitaryEquiv {D E : MultiplicityDatum ℂ}
    (h : OperatorUnitaryEquiv D.operator E.operator) (k : ℕ) :
    D.base (D.level k \ E.level k) = 0 := by
  by_contra hpos
  have hSm : MeasurableSet (D.level k \ E.level k) :=
    (D.measurableSet_level k).diff (E.measurableSet_level k)
  -- The set avoids `E.level k`, so on the `E` side `k` generators suffice.
  have hnullE : E.base ((D.level k \ E.level k) ∩ E.level k) = 0 := by
    convert measure_empty (μ := E.base)
    refine Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
    exact hz.1.2 hz.2
  have hupper := spectralGeneratedLE_mulLp_datumSymbol E hSm hnullE
  rw [operator_eq_mulLp_datumSymbol D, operator_eq_mulLp_datumSymbol E] at h
  obtain ⟨e, he⟩ := h.symm.exists_intertwiner
  have htrans := spectralGeneratedLE_of_intertwines _ e he hupper
  -- But the set fills `D.level k` with positive measure, so on the `D` side they cannot.
  refine not_spectralGeneratedLE_mulLp_datumSymbol D hSm ?_ htrans
  rw [Set.inter_eq_self_of_subset_left fun z hz => hz.1]
  exact hpos

/-- **The level sets of a multiplicity datum are unitary invariants.**  This is the level-set
half of Hahn--Hellinger uniqueness; the measure-class half is
`measureEquiv_base_of_operatorUnitaryEquiv`. -/
theorem base_level_symmDiff_eq_zero_of_operatorUnitaryEquiv {D E : MultiplicityDatum ℂ}
    (h : OperatorUnitaryEquiv D.operator E.operator) (k : ℕ) :
    D.base (symmDiff (D.level k) (E.level k)) = 0 := by
  have h1 := base_level_diff_eq_zero_of_operatorUnitaryEquiv h k
  have h2 := base_level_diff_eq_zero_of_operatorUnitaryEquiv h.symm k
  have hbase := measureEquiv_base_of_operatorUnitaryEquiv h
  have h2' : D.base (E.level k \ D.level k) = 0 := hbase.1 h2
  rw [Set.symmDiff_def]
  exact measure_union_null h1 h2'

/-- **Hahn--Hellinger uniqueness, both halves.**  Unitarily equivalent multiplicity models
agree in measure class and, up to null sets, in every level set. -/
theorem measureEquiv_and_level_of_operatorUnitaryEquiv {D E : MultiplicityDatum ℂ}
    (h : OperatorUnitaryEquiv D.operator E.operator) :
    MeasureEquiv D.base E.base ∧
      ∀ k, D.base (symmDiff (D.level k) (E.level k)) = 0 :=
  ⟨measureEquiv_base_of_operatorUnitaryEquiv h,
    fun k => base_level_symmDiff_eq_zero_of_operatorUnitaryEquiv h k⟩

/-- **The multiplicity datum is a complete invariant, canonically.**  Two data present
unitarily equivalent operators exactly when they agree in measure class and, up to null sets,
in every level set.  The forward direction is the uniqueness proved in this module; the
converse is the existence-side transport `operatorUnitaryEquiv_of_measureEquiv_complex`. -/
theorem operatorUnitaryEquiv_iff_measureEquiv_and_level {D E : MultiplicityDatum ℂ} :
    OperatorUnitaryEquiv D.operator E.operator ↔
      MeasureEquiv D.base E.base ∧
        ∀ k, D.base (symmDiff (D.level k) (E.level k)) = 0 :=
  ⟨fun h => measureEquiv_and_level_of_operatorUnitaryEquiv h,
    fun h => operatorUnitaryEquiv_of_measureEquiv_complex h.1 h.2⟩

end Model

end BorelCalculus
end TauCeti
