/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothFourierData
public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothLoop
public import LeanPool.NavierStokesAndEuler.NavierStokes.PulseCovariance
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Actual torus and native-coordinate averages

The integer covering is treated as an actual surjective additive homomorphism
of the compact torus. Haar invariance is a conclusion, not an assumption.
-/

@[expose] public section


noncomputable section

open Set Function MeasureTheory
open scoped BigOperators Topology ContDiff Interval

namespace NavierStokes.TorusAverages

open TorusInverse SmoothFourierData

local instance instTorusAverages1 : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩

local instance instTorusAverages2 : Measure.IsAddHaarMeasure torusMeasure := by
  unfold torusMeasure
  infer_instance

local instance planeVolumeHaar : Measure.IsAddHaarMeasure (volume : Measure Plane) := by
  change Measure.IsAddHaarMeasure ((volume : Measure ℝ).prod (volume : Measure ℝ))
  infer_instance

/-- Quotient point, given by `((z.1 : UnitAddCircle), (z.2 : UnitAddCircle))`. -/
noncomputable def quotientPoint (z : Plane) : Torus := ((z.1 : UnitAddCircle), (z.2 :
    UnitAddCircle))

/-- The manuscript's real covering matrix `[[3,1],[1,5]]`. -/
noncomputable def covering (z : Plane) : Plane := (3 * z.1 + z.2, z.1 + 5 * z.2)

/-- Torus covering, bundling `toFun`, `map_zero`, `map_add`. -/
noncomputable def torusCovering : Torus →+ Torus where
  toFun z := ((3 : ℕ) • z.1 + z.2, z.1 + (5 : ℕ) • z.2)
  map_zero' := by simp
  map_add' := by
    intro z w
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, nsmul_add] <;> abel

theorem torusCovering_continuous : Continuous torusCovering :=
  ((continuous_fst.nsmul 3).add continuous_snd).prodMk
    (continuous_fst.add (continuous_snd.nsmul 5))

theorem quotient_covering (z : Plane) :
    quotientPoint (covering z) = torusCovering (quotientPoint z) := by
  apply Prod.ext
  · change (((3 * z.1 + z.2 : ℝ) : UnitAddCircle)) =
      (3 : ℕ) • (z.1 : UnitAddCircle) + (z.2 : UnitAddCircle)
    rw [AddCircle.coe_add, ← AddCircle.coe_nsmul]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
  · change (((z.1 + 5 * z.2 : ℝ) : UnitAddCircle)) =
      (z.1 : UnitAddCircle) + (5 : ℕ) • (z.2 : UnitAddCircle)
    rw [AddCircle.coe_add, ← AddCircle.coe_nsmul]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]

/-- Surjectivity is explicit: choose real lifts and apply the inverse matrix
`(1/14)[[5,-1],[-1,3]]` before projecting to the torus. -/
theorem torusCovering_surjective : Surjective torusCovering := by
  rintro ⟨x, y⟩
  refine Quotient.inductionOn' x (fun a => ?_)
  refine Quotient.inductionOn' y (fun b => ?_)
  refine ⟨quotientPoint ((5 * a - b) / 14, (-a + 3 * b) / 14), ?_⟩
  rw [← quotient_covering]
  have heq : covering ((5 * a - b) / 14, (-a + 3 * b) / 14) = (a, b) := by
    apply Prod.ext <;> dsimp [covering] <;> ring
  rw [heq]
  rfl

theorem torusCovering_measurePreserving :
    MeasurePreserving torusCovering torusMeasure torusMeasure :=
  torusCovering.measurePreserving torusCovering_continuous torusCovering_surjective rfl

theorem quotient_covering_iterate (n : ℕ) (z : Plane) :
    quotientPoint (covering^[n] z) = torusCovering^[n] (quotientPoint z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Function.iterate_succ_apply', quotient_covering, ih]

theorem covering_continuous : Continuous covering :=
  ((continuous_const.mul continuous_fst).add continuous_snd).prodMk
    (continuous_fst.add (continuous_const.mul continuous_snd))

/-- Every covering power preserves the actual Haar integral. Continuity is
already sufficient; no Fourier-decay premise or assumed average identity occurs. -/
theorem integral_torusCovering_iterate {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (f : Torus → V) (hf : Continuous f) (n : ℕ) :
    (∫ z, f (torusCovering^[n] z) ∂torusMeasure) = ∫ z, f z ∂torusMeasure := by
  have hp := torusCovering_measurePreserving.iterate n
  rw [← integral_map hp.measurable.aemeasurable hf.aestronglyMeasurable, hp.map_eq]

/-- Square average, given by `∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f (x, y)`. -/
noncomputable def squareAverage {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Plane → V) : V := ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f (x, y)

theorem squareAverage_torusLift (f : C(Torus, ℂ)) :
    squareAverage (torusLift f) = ∫ z, f z ∂torusMeasure := by
  rw [squareAverage, ← coefficient_zero_eq_integral, coefficient_zero_eq_mean]

/-- Unit-square version for a genuine continuous unit-periodic complex field. -/
theorem squareAverage_covering_iterate {f : Plane → ℂ}
    (hf : Continuous f) (hp : UnitPeriodic f) (n : ℕ) :
    squareAverage (fun z => f (covering^[n] z)) = squareAverage f := by
  let g : C(Torus, ℂ) := descendContinuous f hf hp
  let h : C(Torus, ℂ) :=
    ⟨fun z => g (torusCovering^[n] z), g.continuous.comp (torusCovering_continuous.iterate n)⟩
  have heq : torusLift h = (fun z => f (covering^[n] z)) := by
    funext z
    change g (torusCovering^[n] (quotientPoint z)) = f (covering^[n] z)
    rw [← quotient_covering_iterate]
    rfl
  have hg : squareAverage f = ∫ z, g z ∂torusMeasure := squareAverage_torusLift g
  rw [← heq, squareAverage_torusLift]
  exact (integral_torusCovering_iterate g g.continuous n).trans hg.symm

theorem squareAverage_covering_iterate_smooth {f : Plane → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : UnitPeriodic f) (n : ℕ) :
    squareAverage (fun z => f (covering^[n] z)) = squareAverage f :=
  squareAverage_covering_iterate hf.continuous hp n

/-- Real-valued form, with the same actual unit-square integral. -/
theorem squareAverage_covering_iterate_real {f : Plane → ℝ}
    (hf : Continuous f)
    (hp : ∀ z : Plane, ∀ k : Frequency, f (z + ((k.1 : ℝ), (k.2 : ℝ))) = f z)
    (n : ℕ) : squareAverage (fun z => f (covering^[n] z)) = squareAverage f := by
  have hp' : UnitPeriodic (fun z => (f z : ℂ)) := fun z k => congrArg Complex.ofReal (hp z k)
  have h := squareAverage_covering_iterate (Complex.continuous_ofReal.comp hf) hp' n
  apply Complex.ofReal_injective
  simpa only [squareAverage, Function.comp_def, ← intervalIntegral.integral_ofReal] using h

/-! ## Lattice periodization and its actual integral -/

/-- Lattice point, given by `((k.1 : ℝ), (k.2 : ℝ))`. -/
noncomputable def latticePoint (k : Frequency) : Plane := ((k.1 : ℝ), (k.2 : ℝ))

theorem latticePoint_add (k l : Frequency) :
    latticePoint (k + l) = latticePoint k + latticePoint l := by
  ext <;> simp [latticePoint]

theorem latticePoint_injective : Injective latticePoint := by
  intro k l h
  apply Prod.ext
  · have h1 := congrArg Prod.fst h
    change (k.1 : ℝ) = (l.1 : ℝ) at h1
    exact_mod_cast h1
  · have h2 := congrArg Prod.snd h
    change (k.2 : ℝ) = (l.2 : ℝ) at h2
    exact_mod_cast h2

theorem quotientPoint_lattice_add (k : Frequency) (z : Plane) :
    quotientPoint (latticePoint k + z) = quotientPoint z := by
  simp [quotientPoint, latticePoint, circle_int_eq_zero]

/-- Each translated half-open unit square is an injective coordinate chart
for the quotient to the torus. -/
theorem quotientPoint_injOn_square (a : Plane) :
    InjOn quotientPoint (Ico a.1 (a.1 + 1) ×ˢ Ico a.2 (a.2 + 1)) := by
  intro x hx y hy hxy
  apply Prod.ext
  · exact (AddCircle.coe_eq_coe_iff_of_mem_Ico hx.1 hy.1).mp (congrArg Prod.fst hxy)
  · exact (AddCircle.coe_eq_coe_iff_of_mem_Ico hx.2 hy.2).mp (congrArg Prod.snd hxy)

/-- A concrete smallness criterion for the native parallelogram. The product
norm on `Plane` is the maximum norm, so `ball 0 r` is the open native square. -/
theorem quotientPoint_injOn_small_chart (L : Plane ≃L[ℝ] Plane) (center : Plane)
    (r : ℝ) (hr : ‖(L : Plane →L[ℝ] Plane)‖ * r < 1 / 2) :
    InjOn quotientPoint ((fun z => center + L z) '' Metric.ball (0 : Plane) r) := by
  apply (quotientPoint_injOn_square (center - (1 / 2, 1 / 2))).mono
  rintro _ ⟨z, hz, rfl⟩
  have hz' : ‖z‖ < r := by simpa using hz
  have hnorm : ‖L z‖ < 1 / 2 :=
    ((L : Plane →L[ℝ] Plane).le_opNorm z).trans_lt
      ((mul_le_mul_of_nonneg_left hz'.le (norm_nonneg _)).trans_lt hr)
  have h1 : |(L z).1| < 1 / 2 := (norm_fst_le (L z)).trans_lt hnorm
  have h2 : |(L z).2| < 1 / 2 := (norm_snd_le (L z)).trans_lt hnorm
  change (center.1 + (L z).1 ∈ Ico (center.1 - 1 / 2) (center.1 - 1 / 2 + 1)) ∧
    (center.2 + (L z).2 ∈ Ico (center.2 - 1 / 2) (center.2 - 1 / 2 + 1))
  constructor <;> constructor
  · linarith [(abs_lt.mp h1).1]
  · linarith [(abs_lt.mp h1).2]
  · linarith [(abs_lt.mp h2).1]
  · linarith [(abs_lt.mp h2).2]

/-- A positive injective native radius always exists; this proof supplies the
explicit radius `1 / (4 * (‖L‖ + 1))`. -/
theorem exists_injective_native_radius (L : Plane ≃L[ℝ] Plane) (center : Plane) :
    ∃ r : ℝ, 0 < r ∧
      InjOn quotientPoint ((fun z => center + L z) '' Metric.ball (0 : Plane) r) := by
  let N : ℝ := ‖(L : Plane →L[ℝ] Plane)‖
  have hN : 0 ≤ N := norm_nonneg _
  have hpos : 0 < 4 * (N + 1) := by positivity
  refine ⟨1 / (4 * (N + 1)), by positivity,
    quotientPoint_injOn_small_chart L center _ ?_⟩
  change N * (1 / (4 * (N + 1))) < 1 / 2
  rw [mul_one_div, div_lt_iff₀ hpos]
  nlinarith

theorem latticeTranslate_unique {s : Set Plane} (hs : InjOn quotientPoint s)
    {z : Plane} {k l : Frequency} (hk : latticePoint k + z ∈ s)
    (hl : latticePoint l + z ∈ s) : k = l := by
  apply latticePoint_injective
  apply add_right_cancel (b := z)
  exact hs hk hl (by rw [quotientPoint_lattice_add, quotientPoint_lattice_add])

/-- The `AddAction Frequency Plane` structure used in torus averages. -/
local instance latticeAddAction : AddAction Frequency Plane where
  vadd k z := latticePoint k + z
  zero_vadd z := by
    change latticePoint 0 + z = z
    simp [latticePoint]
  add_vadd k l z := by
    change latticePoint (k + l) + z = latticePoint k + (latticePoint l + z)
    simp [latticePoint, Prod.add_def, add_assoc]

local instance instTorusAverages3 : MeasurableVAdd Frequency Plane where
  measurable_const_vadd _ := measurable_const.add measurable_id
  measurable_vadd_const _ := measurable_of_countable _

local instance instTorusAverages4 : VAddInvariantMeasure Frequency Plane (volume : Measure Plane)
    where
  measure_preimage_vadd k s _ :=
    measure_preimage_add (volume : Measure Plane) (latticePoint k) s

/-- Fundamental square, given by `Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1`. -/
noncomputable def fundamentalSquare : Set Plane := Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1

/-- The half-open unit square is proved to tile the plane, using integer floors. -/
theorem fundamentalSquare_isAddFundamentalDomain :
    IsAddFundamentalDomain Frequency fundamentalSquare (volume : Measure Plane) := by
  apply IsAddFundamentalDomain.mk'
    ((measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet)
  intro z
  refine ⟨(-⌊z.1⌋, -⌊z.2⌋), ?_, ?_⟩
  · change ((-⌊z.1⌋ : ℤ) : ℝ) + z.1 ∈ Ico (0 : ℝ) 1 ∧
      ((-⌊z.2⌋ : ℤ) : ℝ) + z.2 ∈ Ico (0 : ℝ) 1
    simpa only [Int.cast_neg, Int.fract, sub_eq_add_neg, add_comm]
      using And.intro ⟨Int.fract_nonneg z.1, Int.fract_lt_one z.1⟩
        ⟨Int.fract_nonneg z.2, Int.fract_lt_one z.2⟩
  · intro k hk
    have h1 : ⌊(k.1 : ℝ) + z.1⌋ = 0 := Int.floor_eq_zero_iff.mpr hk.1
    have h2 : ⌊(k.2 : ℝ) + z.2⌋ = 0 := Int.floor_eq_zero_iff.mpr hk.2
    rw [Int.floor_intCast_add] at h1 h2
    apply Prod.ext <;> dsimp
    · omega
    · omega

/-- The periodization is the actual sum over integer translates. -/
noncomputable def periodize {V : Type*} [NormedAddCommGroup V] (f : Plane → V)
    (z : Plane) : V := ∑' k : Frequency, f (latticePoint k + z)

/-- A compactly supported field has only finitely many active translates on
every bounded set. This supplies an actual local finite-sum formula. -/
theorem finite_translates_on_ball {V : Type*} [Zero V] {f : Plane → V}
    (hf : HasCompactSupport f) (R : ℝ) :
    ∃ s : Finset Frequency, ∀ z : Plane, ‖z‖ ≤ R →
      ∀ k : Frequency, k ∉ s → f (latticePoint k + z) = 0 := by
  classical
  obtain ⟨C, hC⟩ := hf.isCompact.isBounded.exists_norm_le
  let N : ℤ := ⌈C + R⌉
  refine ⟨(Finset.Icc (-N) N).product (Finset.Icc (-N) N), ?_⟩
  intro z hz k hk
  by_contra hne
  have hnorm : ‖latticePoint k‖ ≤ C + R := by
    calc
      ‖latticePoint k‖ = ‖(latticePoint k + z) - z‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖latticePoint k + z‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ C + R := add_le_add (hC _ (subset_tsupport f hne)) hz
  have hn : C + R ≤ (N : ℝ) := Int.le_ceil _
  have hk1 : |(k.1 : ℝ)| ≤ (N : ℝ) := (norm_fst_le (latticePoint k)).trans (hnorm.trans hn)
  have hk2 : |(k.2 : ℝ)| ≤ (N : ℝ) := (norm_snd_le (latticePoint k)).trans (hnorm.trans hn)
  have hm : k ∈ (Finset.Icc (-N) N).product (Finset.Icc (-N) N) := by
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      constructor
      · exact_mod_cast (abs_le.mp hk1).1
      · exact_mod_cast (abs_le.mp hk1).2
    · apply Finset.mem_Icc.mpr
      constructor
      · exact_mod_cast (abs_le.mp hk2).1
      · exact_mod_cast (abs_le.mp hk2).2
  exact hk hm

theorem periodize_eventually_eq_sum {V : Type*} [NormedAddCommGroup V] {f : Plane → V}
    (hf : HasCompactSupport f) (z : Plane) :
    ∃ s : Finset Frequency,
      periodize f =ᶠ[𝓝 z] fun w => ∑ k ∈ s, f (latticePoint k + w) := by
  obtain ⟨s, hs⟩ := finite_translates_on_ball hf (‖z‖ + 1)
  refine ⟨s, ?_⟩
  have hnear : {w : Plane | ‖w‖ < ‖z‖ + 1} ∈ 𝓝 z :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (by simp)
  filter_upwards [hnear] with w hw
  exact tsum_eq_sum (hs w hw.le)

theorem periodize_continuous {V : Type*} [NormedAddCommGroup V] {f : Plane → V}
    (hf : Continuous f) (hcf : HasCompactSupport f) : Continuous (periodize f) := by
  rw [continuous_iff_continuousAt]
  intro z
  obtain ⟨s, hs⟩ := periodize_eventually_eq_sum hcf z
  have hsum : Continuous (fun w => ∑ k ∈ s, f (latticePoint k + w)) :=
    continuous_finsetSum _ (fun k _ => hf.comp (continuous_const.add continuous_id))
  exact hsum.continuousAt.congr_of_eventuallyEq hs

theorem periodize_contDiff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Plane → V} (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) :
    ContDiff ℝ ∞ (periodize f) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  obtain ⟨s, hs⟩ := periodize_eventually_eq_sum hcf z
  have hsum : ContDiff ℝ ∞ (fun w => ∑ k ∈ s, f (latticePoint k + w)) :=
    ContDiff.sum (fun k _ => hf.comp (contDiff_const.add contDiff_id))
  exact hsum.contDiffAt.congr_of_eventuallyEq hs

theorem periodize_periodic {V : Type*} [NormedAddCommGroup V]
    (f : Plane → V) (z : Plane) (k : Frequency) :
    periodize f (z + latticePoint k) = periodize f z := by
  unfold periodize
  calc
    (∑' l : Frequency, f (latticePoint l + (z + latticePoint k))) =
        ∑' l : Frequency, f (latticePoint (l + k) + z) := by
      apply tsum_congr
      intro l
      rw [latticePoint_add]
      congr 1
      abel
    _ = ∑' l : Frequency, f (latticePoint l + z) :=
      (Equiv.addRight k).tsum_eq (fun l : Frequency => f (latticePoint l + z))

/-- On an injective slot, a periodization equals the one native copy present
there. The result includes the case that the native value itself is zero. -/
theorem periodize_eq_native_copy {V : Type*} [NormedAddCommGroup V]
    {s : Set Plane} (hs : InjOn quotientPoint s) {f : Plane → V}
    (hf : Function.support f ⊆ s) {z : Plane} {k : Frequency}
    (hk : latticePoint k + z ∈ s) : periodize f z = f (latticePoint k + z) := by
  apply tsum_eq_single k
  intro l hl
  by_contra hne
  exact hl (latticeTranslate_unique hs (hf hne) hk)

/-- Products of actual periodized fields have no cross-copy terms when both
native fields are supported in the same injective slot. -/
theorem periodize_mul_of_injective_support {s : Set Plane} (hs : InjOn quotientPoint s)
    {f g : Plane → ℝ} (hf : Function.support f ⊆ s) (hg : Function.support g ⊆ s)
    (z : Plane) : periodize f z * periodize g z = periodize (fun w => f w * g w) z := by
  have hfg : Function.support (fun w => f w * g w) ⊆ s := by
    intro w hw
    exact hf (mul_ne_zero_iff.mp hw).1
  by_cases h : ∃ k : Frequency, f (latticePoint k + z) ≠ 0
  · obtain ⟨k, hk⟩ := h
    rw [periodize_eq_native_copy hs hf (hf hk),
      periodize_eq_native_copy hs hg (hf hk),
      periodize_eq_native_copy hs hfg (hf hk)]
  · have hzero : ∀ k : Frequency, f (latticePoint k + z) = 0 := by
      simpa only [not_exists, not_not] using h
    simp [periodize, hzero]

/-- The set-integral and iterated-integral descriptions of the unit-square
average agree. Endpoint choices have zero Lebesgue measure. -/
theorem squareAverage_eq_setIntegral {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Plane → V} (hf : Continuous f) :
    squareAverage f = ∫ z in fundamentalSquare, f z := by
  have hi : Integrable f ((volume.restrict (Ico (0 : ℝ) 1)).prod
      (volume.restrict (Ico (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact (hf.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ico_subset_Icc_self Ico_subset_Icc_self)
  have h := integral_prod_symm f hi
  rw [Measure.prod_restrict] at h
  change (∫ z in fundamentalSquare, f z) =
    ∫ y in Ico (0 : ℝ) 1, ∫ x in Ico (0 : ℝ) 1, f (x, y) at h
  simp only [restrict_Ico_eq_restrict_Ioc] at h
  simp only [squareAverage, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact h.symm

/-- Every integrable field, in particular a smooth compactly supported slot,
has exactly its plane integral as the integral of its lattice periodization. -/
theorem integral_periodize {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Plane → V} (hf : Integrable f) :
    (∫ z in fundamentalSquare, periodize f z) = ∫ z, f z := by
  have hm (k : Frequency) :
      AEStronglyMeasurable (fun z => f (latticePoint k + z))
        (volume.restrict fundamentalSquare) :=
    (hf.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_add_left (volume : Measure Plane) (latticePoint k))).restrict
  have hn : (∑' k : Frequency,
      ∫⁻ z in fundamentalSquare, ‖f (latticePoint k + z)‖ₑ) ≠ ⊤ := by
    change (∑' k : Frequency, ∫⁻ z in fundamentalSquare, ‖f (k +ᵥ z)‖ₑ) ≠ ⊤
    rw [← fundamentalSquare_isAddFundamentalDomain.lintegral_eq_tsum''
      (fun z => ‖f z‖ₑ)]
    exact hf.hasFiniteIntegral.ne
  change (∫ z in fundamentalSquare, ∑' k : Frequency, f (latticePoint k + z)) = _
  rw [integral_tsum hm hn]
  exact (fundamentalSquare_isAddFundamentalDomain.integral_eq_tsum'' f hf).symm

theorem squareAverage_periodize {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Plane → V} (hf : Continuous f) (hcf : HasCompactSupport f) :
    squareAverage (periodize f) = ∫ z, f z := by
  rw [squareAverage_eq_setIntegral (periodize_continuous hf hcf),
    integral_periodize (hf.integrable_of_hasCompactSupport hcf)]

theorem squareAverage_periodize_covering {f : Plane → ℂ}
    (hf : Continuous f) (hcf : HasCompactSupport f) (n : ℕ) :
    squareAverage (fun z => periodize f (covering^[n] z)) = ∫ z, f z := by
  rw [squareAverage_covering_iterate (periodize_continuous hf hcf)
    (periodize_periodic f) n, squareAverage_periodize hf hcf]

theorem squareAverage_periodize_covering_real {f : Plane → ℝ}
    (hf : Continuous f) (hcf : HasCompactSupport f) (n : ℕ) :
    squareAverage (fun z => periodize f (covering^[n] z)) = ∫ z, f z := by
  rw [squareAverage_covering_iterate_real (periodize_continuous hf hcf)
    (periodize_periodic f) n, squareAverage_periodize hf hcf]

/-! ## Native coordinates and the determinant prefactor -/

/-- A native field placed at `center` in the linear coordinate chart `L`. -/
noncomputable def nativeField {V : Type*} (L : Plane ≃L[ℝ] Plane) (center : Plane)
    (f : Plane → V) (z : Plane) : V := f (L.symm (z - center))

theorem nativeField_continuous {V : Type*} [TopologicalSpace V]
    (L : Plane ≃L[ℝ] Plane) (center : Plane) {f : Plane → V} (hf : Continuous f) :
    Continuous (nativeField L center f) :=
  hf.comp (L.symm.continuous.comp (continuous_id.sub continuous_const))

theorem nativeField_contDiff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : Plane ≃L[ℝ] Plane) (center : Plane) {f : Plane → V} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (nativeField L center f) :=
  hf.comp (L.symm.contDiff.comp (contDiff_id.sub contDiff_const))

theorem nativeField_hasCompactSupport {V : Type*} [Zero V]
    (L : Plane ≃L[ℝ] Plane) (center : Plane) {f : Plane → V} (hf : HasCompactSupport f) :
    HasCompactSupport (nativeField L center f) := by
  exact (hf.comp_homeomorph L.symm.toHomeomorph).comp_homeomorph
    (Homeomorph.subRight center)

/-- Actual linear change of variables, including the absolute determinant. -/
theorem integral_nativeField {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : Plane ≃L[ℝ] Plane) (center : Plane) (f : Plane → V) :
    (∫ z, nativeField L center f z) =
      |LinearMap.det (L : Plane →ₗ[ℝ] Plane)| • ∫ z, f z := by
  unfold nativeField
  rw [integral_sub_right_eq_self (fun z => f (L.symm z)) center]
  change (∫ x, f (L.symm.toHomeomorph.toMeasurableEquiv x)) = _
  rw [← integral_map_equiv (μ := (volume : Measure Plane)) L.symm.toHomeomorph.toMeasurableEquiv f]
  have hmap : Measure.map L.symm (volume : Measure Plane) =
      ENNReal.ofReal |(LinearMap.det (L.symm : Plane →ₗ[ℝ] Plane))⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure Plane)
      (LinearEquiv.isUnit_det' L.symm.toLinearEquiv).ne_zero
  change (∫ y, f y ∂Measure.map L.symm volume) = _
  rw [hmap, integral_smul_measure]
  have hd : LinearMap.det (L.symm : Plane →ₗ[ℝ] Plane) =
      (LinearMap.det (L : Plane →ₗ[ℝ] Plane))⁻¹ :=
    LinearEquiv.det_coe_symm L.toLinearEquiv
  rw [hd, inv_inv, ENNReal.toReal_ofReal (abs_nonneg _)]

/-- The native compact-slot average is obtained from periodization and a
Jacobian theorem, with no assumed averaging identity. -/
theorem integral_periodize_nativeField {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : Plane ≃L[ℝ] Plane) (center : Plane) {f : Plane → V}
    (hf : Continuous f) (hcf : HasCompactSupport f) :
    (∫ z in fundamentalSquare, periodize (nativeField L center f) z) =
      |LinearMap.det (L : Plane →ₗ[ℝ] Plane)| • ∫ z, f z := by
  rw [integral_periodize ((nativeField_continuous L center hf).integrable_of_hasCompactSupport
    (nativeField_hasCompactSupport L center hcf)), integral_nativeField]

/-- The linear map with the radial and longitudinal vectors as its columns. -/
noncomputable def slotLinearMap (vr vt : Plane) : Plane →ₗ[ℝ] Plane :=
  Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
    !![vr.1, vt.1; vr.2, vt.2]

theorem slotLinearMap_apply (vr vt z : Plane) :
    slotLinearMap vr vt z = z.1 • vr + z.2 • vt := by
  rw [slotLinearMap, Matrix.toLin_finTwoProd_apply]
  ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

theorem det_slotLinearMap (vr vt : Plane) :
    LinearMap.det (slotLinearMap vr vt) = vr.1 * vt.2 - vr.2 * vt.1 := by
  simp [slotLinearMap, LinearMap.det_toLin, Matrix.det_fin_two, mul_comm]

/-- The genuine nondegenerate native chart. -/
noncomputable def slotChart (vr vt : Plane) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) :
    Plane ≃L[ℝ] Plane :=
  ((slotLinearMap vr vt).equivOfDetNeZero ((det_slotLinearMap vr vt).trans_ne
      hdet)).toContinuousLinearEquiv

theorem slotChart_apply (vr vt : Plane) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (z : Plane) :
    slotChart vr vt hdet z = z.1 • vr + z.2 • vt := slotLinearMap_apply vr vt z

theorem det_slotChart (vr vt : Plane) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) :
    LinearMap.det (slotChart vr vt hdet : Plane →ₗ[ℝ] Plane) =
      vr.1 * vt.2 - vr.2 * vt.1 := det_slotLinearMap vr vt

theorem integral_periodize_slot {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (vr vt center : Plane) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) {f : Plane → V}
    (hf : Continuous f) (hcf : HasCompactSupport f) :
    (∫ z in fundamentalSquare, periodize (nativeField (slotChart vr vt hdet) center f) z) =
      |vr.1 * vt.2 - vr.2 * vt.1| • ∫ z, f z := by
  rw [integral_periodize_nativeField _ center hf hcf, det_slotChart]

/-- Rescaling the transverse coordinate by `ci`. -/
noncomputable def transverseChart (ci : ℝ) (hci : ci ≠ 0) : Plane ≃L[ℝ] Plane :=
  slotChart (1, 0) (0, ci) (by simpa using hci)

theorem transverseChart_apply (ci : ℝ) (hci : ci ≠ 0) (z : Plane) :
    transverseChart ci hci z = (z.1, ci * z.2) := by
  rw [transverseChart, slotChart_apply]
  ext <;> simp [mul_comm]

theorem transverseChart_symm_apply (ci : ℝ) (hci : ci ≠ 0) (z : Plane) :
    (transverseChart ci hci).symm z = (z.1, z.2 / ci) := by
  apply (transverseChart ci hci).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, transverseChart_apply]
  ext <;> simp [hci, mul_div_cancel₀]

theorem det_transverseChart (ci : ℝ) (hci : ci ≠ 0) :
    LinearMap.det (transverseChart ci hci : Plane →ₗ[ℝ] Plane) = ci := by
  rw [transverseChart, det_slotChart]
  simp

/-- `η = ci * v - r0`, written as the field in the native `(ξ,η)` coordinates. -/
noncomputable def transverseStretch {V : Type*} (ci r0 : ℝ) (f : Plane → V) (z : Plane) : V :=
  f (z.1, (z.2 + r0) / ci)

theorem transverseStretch_eq_nativeField {V : Type*} (ci r0 : ℝ) (hci : ci ≠ 0)
    (f : Plane → V) :
    transverseStretch ci r0 f = nativeField (transverseChart ci hci) (0, -r0) f := by
  funext z
  simp [transverseStretch, nativeField, transverseChart_symm_apply]

theorem transverseStretch_continuous {V : Type*} [TopologicalSpace V] (ci r0 : ℝ)
    (hci : ci ≠ 0) {f : Plane → V} (hf : Continuous f) :
    Continuous (transverseStretch ci r0 f) := by
  rw [transverseStretch_eq_nativeField ci r0 hci]
  exact nativeField_continuous _ _ hf

theorem transverseStretch_contDiff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ci r0 : ℝ) (hci : ci ≠ 0) {f : Plane → V} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (transverseStretch ci r0 f) := by
  rw [transverseStretch_eq_nativeField ci r0 hci]
  exact nativeField_contDiff _ _ hf

theorem transverseStretch_hasCompactSupport {V : Type*} [Zero V] (ci r0 : ℝ)
    (hci : ci ≠ 0) {f : Plane → V} (hf : HasCompactSupport f) :
    HasCompactSupport (transverseStretch ci r0 f) := by
  rw [transverseStretch_eq_nativeField ci r0 hci]
  exact nativeField_hasCompactSupport _ _ hf

theorem integral_transverseStretch {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ci r0 : ℝ) (hci : ci ≠ 0) (f : Plane → V) :
    (∫ z, transverseStretch ci r0 f z) = |ci| • ∫ z, f z := by
  rw [transverseStretch_eq_nativeField ci r0 hci, integral_nativeField, det_transverseChart]

/-- The actual native-slot average after every integer covering power. The
transverse-coordinate Jacobian is positive `ci`, not an assumed model scale. -/
theorem squareAverage_covered_nativeSlot (vr vt center : Plane)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (ci r0 : ℝ) (hci : 0 < ci)
    {f : Plane → ℝ} (hf : Continuous f) (hcf : HasCompactSupport f) (n : ℕ) :
    squareAverage (fun z => periodize
      (nativeField (slotChart vr vt hdet) center (transverseStretch ci r0 f))
      (covering^[n] z)) =
      |vr.1 * vt.2 - vr.2 * vt.1| * ci * ∫ z, f z := by
  rw [squareAverage_periodize_covering_real
    (nativeField_continuous _ _ (transverseStretch_continuous ci r0 hci.ne' hf))
    (nativeField_hasCompactSupport _ _ (transverseStretch_hasCompactSupport ci r0 hci.ne' hcf)) n,
    integral_nativeField, det_slotChart, integral_transverseStretch ci r0 hci.ne',
    abs_of_pos hci, smul_eq_mul, smul_eq_mul, mul_assoc]

theorem productProfile_hasCompactSupport {a b : ℝ → ℝ}
    (ha : HasCompactSupport a) (hb : HasCompactSupport b) :
    HasCompactSupport (fun z : Plane => a z.1 * b z.2) := by
  apply HasCompactSupport.of_support_subset_isCompact (ha.isCompact.prod hb.isCompact)
  intro z hz
  exact ⟨subset_tsupport a (mul_ne_zero_iff.mp hz).1,
    subset_tsupport b (mul_ne_zero_iff.mp hz).2⟩

/-- Separation of the actual longitudinal and transverse integrals. -/
theorem squareAverage_covered_product (vr vt center : Plane)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (ci r0 : ℝ) (hci : 0 < ci)
    {a b : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b) (n : ℕ) :
    squareAverage (fun z => periodize
      (nativeField (slotChart vr vt hdet) center
        (transverseStretch ci r0 (fun w : Plane => a w.1 * b w.2)))
      (covering^[n] z)) =
      |vr.1 * vt.2 - vr.2 * vt.1| * (∫ ξ : ℝ, a ξ) * (ci * ∫ v : ℝ, b v) := by
  rw [squareAverage_covered_nativeSlot vr vt center hdet ci r0 hci
    (f := fun w : Plane => a w.1 * b w.2)
    ((ha.comp continuous_fst).mul (hb.comp continuous_snd))
    (productProfile_hasCompactSupport hca hcb) n]
  change |vr.1 * vt.2 - vr.2 * vt.1| * ci *
    (∫ z, a z.1 * b z.2 ∂(volume : Measure ℝ).prod (volume : Measure ℝ)) = _
  rw [integral_prod_mul]
  ring

/-- The native covariance coefficient before angular averaging. -/
noncomputable def pulseProfile (χ ψ x : ℝ → ℝ) (t : ℝ → PulseCovariance.Vec2)
    (i : Fin 2) (z : Plane) : ℝ := χ z.1 ^ 2 * (ψ z.2 ^ 2 * x z.2 * t z.2 i)

theorem squareAverage_covered_pulseColumn (vr vt center : Plane)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (ci r0 : ℝ) (hci : 0 < ci)
    {χ ψ x : ℝ → ℝ} {t : ℝ → PulseCovariance.Vec2}
    (hχ : Continuous χ) (hψ : Continuous ψ) (hx : Continuous x) (ht : Continuous t)
    (hcχ : HasCompactSupport χ) (hcψ : HasCompactSupport ψ) (i : Fin 2) (n : ℕ) :
    squareAverage (fun z => periodize
      (nativeField (slotChart vr vt hdet) center
        (transverseStretch ci r0 (pulseProfile χ ψ x t i)))
      (covering^[n] z)) =
      |vr.1 * vt.2 - vr.2 * vt.1| * (∫ ξ : ℝ, χ ξ ^ 2) *
        PulseCovariance.actualColumn ci ψ x t i := by
  have hca : HasCompactSupport (fun ξ => χ ξ ^ 2) := by
    apply hcχ.mono
    intro ξ hξ heq
    exact hξ (by simp [heq])
  have hcb : HasCompactSupport (fun v => ψ v ^ 2 * x v * t v i) := by
    apply hcψ.mono
    intro v hv heq
    exact hv (by simp [heq])
  exact squareAverage_covered_product vr vt center hdet ci r0 hci
    (hχ.pow 2) (((hψ.pow 2).mul hx).mul ((continuous_apply i).comp ht)) hca hcb n

/-! ## The real-cosine factor in Lemma 8.7 -/

/-- An arbitrary phase shift does not change the average of a nonzero integer
angular harmonic squared. -/
theorem angularMean_cos_sq_harmonic (j : ℤ) (hj : j ≠ 0) (phase : ℝ) :
    SmoothLoop.angularMean (fun θ => Real.cos ((j : ℝ) * θ + phase) ^ 2) = 1 / 2 := by
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast hj
  have hs : Real.sin ((j : ℝ) * (2 * Real.pi) + phase) = Real.sin phase := by
    rw [add_comm]
    exact Real.sin_add_int_mul_two_pi phase j
  have hc : Real.cos ((j : ℝ) * (2 * Real.pi) + phase) = Real.cos phase := by
    rw [add_comm]
    exact Real.cos_add_int_mul_two_pi phase j
  unfold SmoothLoop.angularMean
  rw [intervalIntegral.integral_comp_mul_add (fun θ => Real.cos θ ^ 2) hjR phase,
    integral_cos_sq]
  simp only [mul_zero, zero_add, hs, hc, smul_eq_mul]
  field_simp [hjR, Real.pi_ne_zero]; ring

theorem squareAverage_const_mul (c : ℝ) (f : Plane → ℝ) :
    squareAverage (fun z => c * f z) = c * squareAverage f := by
  simp only [squareAverage, intervalIntegral.integral_const_mul]

theorem angular_cosine_covariance (a phase : Plane → ℝ) (j : ℤ) (hj : j ≠ 0) :
    squareAverage (fun z => SmoothLoop.angularMean
      (fun θ => a z * Real.cos ((j : ℝ) * θ + phase z) ^ 2)) =
      (1 / 2) * squareAverage a := by
  simp only [SmoothLoop.angularMean_const_mul, angularMean_cos_sq_harmonic j hj]
  simpa only [mul_comm] using squareAverage_const_mul (1 / 2) a

/-- The displayed native prefactor in Lemma 8.7, for actual periodized slot
coefficients and actual angular averages. The harmonic is the rounded integer
`k*p`, so its only required property here is nonzero integrality. -/
theorem primary_covariance_average (vr vt center : Plane)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (ci r0 : ℝ) (hci : 0 < ci)
    {χ ψ x : ℝ → ℝ} {t : ℝ → PulseCovariance.Vec2}
    (hχ : Continuous χ) (hψ : Continuous ψ) (hx : Continuous x) (ht : Continuous t)
    (hcχ : HasCompactSupport χ) (hcψ : HasCompactSupport ψ) (i : Fin 2) (n : ℕ)
    (phase : Plane → ℝ) (j : ℤ) (hj : j ≠ 0) :
    let a := fun z => periodize
      (nativeField (slotChart vr vt hdet) center
        (transverseStretch ci r0 (pulseProfile χ ψ x t i)))
      (covering^[n] z)
    squareAverage (fun z => SmoothLoop.angularMean
      (fun θ => a z * Real.cos ((j : ℝ) * θ + phase z) ^ 2)) =
      (|vr.1 * vt.2 - vr.2 * vt.1| / 2) * (∫ ξ : ℝ, χ ξ ^ 2) *
        PulseCovariance.actualColumn ci ψ x t i := by
  dsimp only
  rw [angular_cosine_covariance _ phase j hj,
    squareAverage_covered_pulseColumn vr vt center hdet ci r0 hci
      hχ hψ hx ht hcχ hcψ i n]
  ring

/-- The same exact prefactor with the transverse integral restricted to the
actual pulse interval, using the already verified compact pulse support. -/
theorem primary_covariance_average_interval (vr vt center : Plane)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (ci r0 : ℝ) (hci : 0 < ci)
    {r a A b B : ℝ} {χ ψ x : ℝ → ℝ} {t : ℝ → PulseCovariance.Vec2}
    (hp : PulseCovariance.PulseBounds r a A b B ψ x)
    (hχ : Continuous χ) (ht : Continuous t) (hcχ : HasCompactSupport χ)
    (i : Fin 2) (n : ℕ) (phase : Plane → ℝ) (j : ℤ) (hj : j ≠ 0) :
    let amp := fun z => periodize
      (nativeField (slotChart vr vt hdet) center
        (transverseStretch ci r0 (pulseProfile χ ψ x t i)))
      (covering^[n] z)
    squareAverage (fun z => SmoothLoop.angularMean
      (fun θ => amp z * Real.cos ((j : ℝ) * θ + phase z) ^ 2)) =
      (|vr.1 * vt.2 - vr.2 * vt.1| / 2) * (∫ ξ : ℝ, χ ξ ^ 2) *
        (ci * ∫ v in (0 : ℝ)..r ^ 2, ψ v ^ 2 * x v * t v i) := by
  rw [← hp.actualColumn_eq_intervalIntegral ci t i]
  exact primary_covariance_average vr vt center hdet ci r0 hci
    hχ hp.cutoff_continuous hp.component_continuous ht hcχ hp.cutoff_compact i n phase j hj

end NavierStokes.TorusAverages
