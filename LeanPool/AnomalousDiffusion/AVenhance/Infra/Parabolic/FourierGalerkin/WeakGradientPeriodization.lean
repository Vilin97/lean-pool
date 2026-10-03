/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.TestDensityBridge
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Heat.PeriodicCutoff
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain

/-!
# Periodizing compact Euclidean tests against the periodic weak gradient

The lattice of integer translations has a compact fundamental cell. Compact support makes the
periodization locally a finite sum, so it retains the smoothness of the original test.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped Pointwise Topology

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Integer span of the coordinate basis, defining the period lattice. -/
abbrev WeakGradientPeriodization.PeriodLattice :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2)))

/-- Additive group of translations by vectors in the period lattice. -/
abbrev WeakGradientPeriodization.PeriodTranslations :=
    WeakGradientPeriodization.PeriodLattice.toAddSubgroup

/-- Fundamental cell for translations by the coordinate period lattice. -/
def WeakGradientPeriodization.PeriodCell : Set (Vec 2) :=
  ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 2))

theorem WeakGradientPeriodization.periodTranslations_fundamentalDomain :
    IsAddFundamentalDomain WeakGradientPeriodization.PeriodTranslations
        WeakGradientPeriodization.PeriodCell (volume : Measure (Vec 2)) := by
  exact ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin 2)) volume

theorem WeakGradientPeriodization.periodCell_ae_unitCube :
    WeakGradientPeriodization.PeriodCell =ᵐ[volume] AVenhance.unitCube := by
  have hIcoIcc :
      (Set.pi Set.univ fun _ : Fin 2 => Set.Ico (0 : ℝ) 1) =ᵐ[volume]
        Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1 := by
    simpa [volume_pi] using
      (Measure.univ_pi_Ico_ae_eq_Icc (f := fun _ : Fin 2 => (0 : ℝ))
        (g := fun _ : Fin 2 => (1 : ℝ)))
  have hIooIcc :
      AVenhance.unitCube =ᵐ[volume]
        Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1 := by
    simpa [AVenhance.unitCube, volume_pi] using
      (Measure.univ_pi_Ioo_ae_eq_Icc (f := fun _ : Fin 2 => (0 : ℝ))
        (g := fun _ : Fin 2 => (1 : ℝ)))
  rw [WeakGradientPeriodization.PeriodCell, ZSpan.fundamentalDomain_pi_basisFun]
  exact hIcoIcc.trans hIooIcc.symm

theorem WeakGradientPeriodization.periodTranslation_integerVector (z :
    WeakGradientPeriodization.PeriodTranslations) :
    ∃ k : Fin 2 → ℤ, (z : Vec 2) = AVenhance.latticeShift k := by
  have hrepr :=
    ((Pi.basisFun ℝ (Fin 2)).mem_span_iff_repr_mem ℤ (z : Vec 2)).mp z.property
  have hcoord : ∀ i : Fin 2, ∃ n : ℤ,
      (n : ℝ) = (Pi.basisFun ℝ (Fin 2)).repr (z : Vec 2) i := by
    intro i
    exact Set.mem_range.mp (hrepr i)
  let k : Fin 2 → ℤ := fun i => Classical.choose (hcoord i)
  refine ⟨k, ?_⟩
  funext i
  change (z : Vec 2) i = (k i : ℝ)
  simpa only [k, Pi.basisFun_repr] using (Classical.choose_spec (hcoord i)).symm

/-- Integer coordinate vector representing a period translation. -/
noncomputable def WeakGradientPeriodization.periodTranslationIndex (z :
    WeakGradientPeriodization.PeriodTranslations) : Fin 2 → ℤ :=
  Classical.choose (WeakGradientPeriodization.periodTranslation_integerVector z)

theorem WeakGradientPeriodization.periodTranslationIndex_spec (z :
    WeakGradientPeriodization.PeriodTranslations) :
    (z : Vec 2) = AVenhance.latticeShift (WeakGradientPeriodization.periodTranslationIndex z) :=
  Classical.choose_spec (WeakGradientPeriodization.periodTranslation_integerVector z)

theorem WeakGradientPeriodization.periodLattice_countable :
    (WeakGradientPeriodization.PeriodLattice : Set (Vec 2)).Countable := by
  have hrange : (WeakGradientPeriodization.PeriodLattice : Set (Vec 2)) = Set.range
      AVenhance.latticeShift := by
    ext x
    constructor
    · intro hx
      let z : WeakGradientPeriodization.PeriodTranslations := ⟨x, hx⟩
      exact ⟨WeakGradientPeriodization.periodTranslationIndex z,
          (WeakGradientPeriodization.periodTranslationIndex_spec z).symm⟩
    · rintro ⟨k, rfl⟩
      change AVenhance.latticeShift k ∈
        Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2)))
      rw [(Pi.basisFun ℝ (Fin 2)).mem_span_iff_repr_mem ℤ]
      intro i
      exact ⟨k i, by simp [AVenhance.latticeShift, Pi.basisFun_repr]⟩
  rw [hrange]
  exact Set.countable_range _

instance WeakGradientPeriodization.periodTranslations_countable : Countable
    WeakGradientPeriodization.PeriodTranslations :=
  WeakGradientPeriodization.periodLattice_countable.to_subtype

theorem WeakGradientPeriodization.periodCell_measurable : MeasurableSet
    WeakGradientPeriodization.PeriodCell := by
  rw [WeakGradientPeriodization.PeriodCell, ZSpan.fundamentalDomain_pi_basisFun]
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ico)

instance WeakGradientPeriodization.periodCell_finiteMeasure :
    IsFiniteMeasure (volume.restrict WeakGradientPeriodization.PeriodCell) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ, WeakGradientPeriodization.PeriodCell,
    ZSpan.fundamentalDomain_pi_basisFun, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ico]

theorem WeakGradientPeriodization.periodCell_memLp {g : Vec 2 → ℝ}
    (hg : MemLp g 2 (volume.restrict AVenhance.unitCube)) :
    MemLp g 2 (volume.restrict WeakGradientPeriodization.PeriodCell) := by
  rw [Measure.restrict_congr_set WeakGradientPeriodization.periodCell_ae_unitCube]
  exact hg

theorem WeakGradientPeriodization.periodCell_translate_memLp {g : Vec 2 → ℝ}
    (hg : MemLp g 2 (volume.restrict WeakGradientPeriodization.PeriodCell))
    (hperiodic : AVenhance.IsZ2Periodic g) (z : WeakGradientPeriodization.PeriodTranslations) :
    MemLp g 2 (volume.restrict ((z : Vec 2) +ᵥ WeakGradientPeriodization.PeriodCell)) := by
  let shift : Vec 2 := -(z : Vec 2)
  have hpre : (fun x : Vec 2 => x + shift) ⁻¹' WeakGradientPeriodization.PeriodCell =
      (z : Vec 2) +ᵥ WeakGradientPeriodization.PeriodCell := by
    ext x
    change (x + shift ∈ WeakGradientPeriodization.PeriodCell) ↔ _
    simp only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    rw [show x + shift = -(z : Vec 2) + x by dsimp [shift]; abel]
  have hmp : MeasurePreserving (fun x : Vec 2 => x + shift)
      (volume.restrict ((z : Vec 2) +ᵥ WeakGradientPeriodization.PeriodCell))
      (volume.restrict WeakGradientPeriodization.PeriodCell) := by
    simpa [hpre] using
      (measurePreserving_add_right (volume : Measure (Vec 2)) shift).restrict_preimage
        WeakGradientPeriodization.periodCell_measurable
  have hcomp := hg.comp_measurePreserving hmp
  apply MemLp.ae_eq (μ := volume.restrict ((z : Vec 2) +ᵥ WeakGradientPeriodization.PeriodCell))
    (Filter.Eventually.of_forall fun x => ?_) hcomp
  obtain ⟨k, hk⟩ := WeakGradientPeriodization.periodTranslation_integerVector z
  have hper := hperiodic (-k) x
  have hshift : shift = AVenhance.latticeShift (-k) := by
    funext i
    simp [shift, hk, AVenhance.latticeShift]
  simpa [hshift, AVenhance.latticeShift, Pi.add_apply] using hper

theorem WeakGradientPeriodization.periodCell_translate_preimage (z :
    WeakGradientPeriodization.PeriodTranslations) :
    (fun x : Vec 2 => x - (z : Vec 2)) ⁻¹' WeakGradientPeriodization.PeriodCell =
      (z : Vec 2) +ᵥ WeakGradientPeriodization.PeriodCell := by
  ext x
  change (x - (z : Vec 2) ∈ WeakGradientPeriodization.PeriodCell) ↔ _
  simp only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
  rw [show x - (z : Vec 2) = -(z : Vec 2) + x by abel]

theorem WeakGradientPeriodization.periodCell_translate_measurable (z :
    WeakGradientPeriodization.PeriodTranslations) :
    MeasurableSet ((z : Vec 2) +ᵥ WeakGradientPeriodization.PeriodCell) := by
  rw [← WeakGradientPeriodization.periodCell_translate_preimage z]
  exact WeakGradientPeriodization.periodCell_measurable.preimage (measurable_id.sub
      measurable_const)

theorem WeakGradientPeriodization.periodCell_translate_finiteMeasure (z :
    WeakGradientPeriodization.PeriodTranslations) :
    IsFiniteMeasure (volume.restrict ((z : Vec 2) +ᵥ WeakGradientPeriodization.PeriodCell)) := by
  let shift : Vec 2 := -(z : Vec 2)
  have hpre := WeakGradientPeriodization.periodCell_translate_preimage z
  have hpre' : (fun x : Vec 2 => x + shift) ⁻¹' WeakGradientPeriodization.PeriodCell =
      (z : Vec 2) +ᵥ WeakGradientPeriodization.PeriodCell := by
    simpa [shift, sub_eq_add_neg] using hpre
  have hmp : MeasurePreserving (fun x : Vec 2 => x + shift)
      (volume.restrict ((z : Vec 2) +ᵥ WeakGradientPeriodization.PeriodCell))
      (volume.restrict WeakGradientPeriodization.PeriodCell) := by
    simpa only [hpre'] using
      (measurePreserving_add_right (volume : Measure (Vec 2)) shift).restrict_preimage
        WeakGradientPeriodization.periodCell_measurable
  have hmass : volume ((z : Vec 2) +ᵥ WeakGradientPeriodization.PeriodCell) = volume
      WeakGradientPeriodization.PeriodCell := by
    have h := congrArg (fun μ : Measure (Vec 2) => μ Set.univ) hmp.map_eq
    rw [Measure.map_apply hmp.measurable MeasurableSet.univ] at h
    simpa only [Measure.restrict_apply_univ, preimage_univ] using h
  have hcell : volume WeakGradientPeriodization.PeriodCell ≠ ⊤ := by
    rw [WeakGradientPeriodization.PeriodCell, ZSpan.fundamentalDomain_pi_basisFun, volume_pi,
        Measure.pi_pi]
    simp [Real.volume_Ico]
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ, hmass]
  exact lt_top_iff_ne_top.mpr hcell

theorem WeakGradientPeriodization.periodCell_translate_integrable {g : Vec 2 → ℝ}
    (hg : MemLp g 2 (volume.restrict AVenhance.unitCube))
    (hperiodic : AVenhance.IsZ2Periodic g) (z : WeakGradientPeriodization.PeriodTranslations) :
    IntegrableOn g ((z : Vec 2) +ᵥ WeakGradientPeriodization.PeriodCell) := by
  have hmem := WeakGradientPeriodization.periodCell_translate_memLp
      (WeakGradientPeriodization.periodCell_memLp hg) hperiodic z
  have hfinite := WeakGradientPeriodization.periodCell_translate_finiteMeasure z
  exact @MemLp.integrable (Vec 2) ℝ _ (volume.restrict ((z : Vec 2) +ᵥ
      WeakGradientPeriodization.PeriodCell))
    inferInstance inferInstance (2 : ENNReal)
    (by norm_num : (1 : ENNReal) ≤ 2) g hfinite hmem

theorem WeakGradientPeriodization.continuous_compact_support_norm_bound {w : Vec 2 → ℝ}
    (hw : Continuous w) (hws : HasCompactSupport w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖w x‖ ≤ C := by
  have hbounded : Bornology.IsBounded (w '' tsupport w) :=
    hws.isCompact.image hw |>.isBounded
  obtain ⟨C, hCpos, hC⟩ := hbounded.subset_ball_lt 0 0
  refine ⟨C, hCpos.le, ?_⟩
  intro x
  by_cases hx : x ∈ tsupport w
  · have hball := hC ⟨x, hx, rfl⟩
    have hnorm : ‖w x‖ < C := by
      simpa [Metric.mem_ball, dist_eq_norm] using hball
    exact hnorm.le
  · have hzero : w x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [hzero, hCpos.le]

theorem WeakGradientPeriodization.integrableOn_periodic_mul_continuous_compact
    {g w : Vec 2 → ℝ} (hg : MemLp g 2 (volume.restrict AVenhance.unitCube))
    (hperiodic : AVenhance.IsZ2Periodic g) (hw : Continuous w)
    (hws : HasCompactSupport w) (z : WeakGradientPeriodization.PeriodTranslations) :
    IntegrableOn (fun x => g x * w x) ((z : Vec 2) +ᵥ WeakGradientPeriodization.PeriodCell) := by
  obtain ⟨C, hC, hbound⟩ := WeakGradientPeriodization.continuous_compact_support_norm_bound hw hws
  have hbase := WeakGradientPeriodization.periodCell_translate_integrable hg hperiodic z
  change Integrable (fun x => g x * w x)
    (volume.restrict ((z : Vec 2) +ᵥ WeakGradientPeriodization.PeriodCell))
  have hmeas : AEStronglyMeasurable (fun x => g x * w x)
      (volume.restrict ((z : Vec 2) +ᵥ WeakGradientPeriodization.PeriodCell)) :=
    hbase.aestronglyMeasurable.mul hw.measurable.aestronglyMeasurable
  have hmajor : Integrable (fun x => C * ‖g x‖)
      (volume.restrict ((z : Vec 2) +ᵥ WeakGradientPeriodization.PeriodCell)) :=
          hbase.norm.const_mul C
  apply hmajor.mono hmeas
  filter_upwards with x
  rw [norm_mul]
  calc
    ‖g x‖ * ‖w x‖ ≤ ‖g x‖ * C :=
      mul_le_mul_of_nonneg_left (hbound x) (norm_nonneg _)
    _ = ‖C * ‖g x‖‖ := by
      simp [Real.norm_eq_abs, abs_of_nonneg hC]
      ring

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def WeakGradientPeriodization.periodCellClosure : Set (Vec 2) :=
  Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1

theorem WeakGradientPeriodization.periodCellClosure_compact : IsCompact
    WeakGradientPeriodization.periodCellClosure := by
  simpa [WeakGradientPeriodization.periodCellClosure] using
    (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)

theorem WeakGradientPeriodization.periodCell_subset_closure : WeakGradientPeriodization.PeriodCell
    ⊆ WeakGradientPeriodization.periodCellClosure := by
  rw [WeakGradientPeriodization.PeriodCell, ZSpan.fundamentalDomain_pi_basisFun]
  intro x hx
  simp only [WeakGradientPeriodization.periodCellClosure, Set.mem_pi, Set.mem_univ,
      forall_true_left]
  intro i
  have hi := hx i (Set.mem_univ _)
  exact ⟨hi.1, hi.2.le⟩

/-- Periodize a compactly supported test function by summing its lattice translates. -/
def compactTestPeriodization (φ : Vec 2 → ℝ) : Vec 2 → ℝ := fun x =>
  ∑ᶠ z : WeakGradientPeriodization.PeriodTranslations, φ (x + (z : Vec 2))

theorem WeakGradientPeriodization.periodized_family_locallyFinite {φ : Vec 2 → ℝ}
    (hφ : HasCompactSupport φ) :
    LocallyFinite (fun z : WeakGradientPeriodization.PeriodTranslations =>
      {x : Vec 2 | φ (x + (z : Vec 2)) ≠ 0}) := by
  intro x
  let U : Set (Vec 2) := Metric.ball x 1
  have hU : U ∈ 𝓝 x := Metric.ball_mem_nhds x zero_lt_one
  let K : Set (Vec 2) :=
    (fun p : Vec 2 × Vec 2 => p.1 - p.2) ''
      (tsupport φ ×ˢ Metric.closedBall x 1)
  have hK : IsCompact K :=
    (hφ.isCompact.prod (isCompact_closedBall x 1)).image
      (continuous_fst.sub continuous_snd)
  have hLatticeFinite :
      (K ∩ (WeakGradientPeriodization.PeriodLattice : Set (Vec 2))).Finite := by
    exact ZSpan.setFinite_inter (Pi.basisFun ℝ (Fin 2)) hK.isBounded
  let S : Set WeakGradientPeriodization.PeriodTranslations :=
    (fun z : WeakGradientPeriodization.PeriodTranslations => (z : Vec 2)) ⁻¹'
      (K ∩ (WeakGradientPeriodization.PeriodLattice : Set (Vec 2)))
  have hS : S.Finite := hLatticeFinite.preimage Subtype.val_injective.injOn
  refine ⟨U, hU, ?_⟩
  apply hS.subset
  intro z hz
  change (({y : Vec 2 | φ (y + (z : Vec 2)) ≠ 0} ∩ U).Nonempty) at hz
  rcases hz with ⟨y, ⟨hyφ, hyU⟩⟩
  have hyφ' : y + (z : Vec 2) ∈ tsupport φ := subset_closure hyφ
  have hzBound : (z : Vec 2) ∈ K := by
    refine ⟨(y + (z : Vec 2), y), ⟨hyφ', ?_⟩, ?_⟩
    · exact Metric.mem_closedBall.mpr
        (le_of_lt (by simpa [U] using hyU))
    · change y + (z : Vec 2) - y = (z : Vec 2)
      abel
  exact ⟨hzBound, z.property⟩

theorem WeakGradientPeriodization.integral_periodic_mul_compact_eq_cell_periodization
    {g w : Vec 2 → ℝ} (hg : MemLp g 2 (volume.restrict AVenhance.unitCube))
    (hperiodic : AVenhance.IsZ2Periodic g) (hw : Continuous w)
    (hws : HasCompactSupport w) :
    Integrable (fun x => g x * w x) volume ∧
      ∫ x, g x * w x =
        ∫ x in WeakGradientPeriodization.PeriodCell, g x * compactTestPeriodization w x := by
  classical
  let F : Vec 2 → ℝ := fun x => g x * w x
  let Q (z : WeakGradientPeriodization.PeriodTranslations) : Set (Vec 2) :=
    {x | w (x + (z : Vec 2)) ≠ 0}
  let S : Set WeakGradientPeriodization.PeriodTranslations :=
    {z | (Q z ∩ WeakGradientPeriodization.periodCellClosure).Nonempty}
  have hlocal := WeakGradientPeriodization.periodized_family_locallyFinite hws
  have hSfinite : S.Finite := by
    exact hlocal.finite_nonempty_inter_compact WeakGradientPeriodization.periodCellClosure_compact
  let shifts := hSfinite.toFinset
  let tiles : Set (Vec 2) :=
    ⋃ z ∈ shifts, (z : Vec 2) +ᵥ WeakGradientPeriodization.PeriodCell
  have htilesMeas : MeasurableSet tiles := by
    dsimp [tiles]
    exact shifts.finite_toSet.measurableSet_biUnion
      (fun z hz => WeakGradientPeriodization.periodCell_translate_measurable z)
  have htileInt : ∀ z ∈ shifts,
      IntegrableOn F ((z : Vec 2) +ᵥ WeakGradientPeriodization.PeriodCell) := by
    intro z hz
    exact WeakGradientPeriodization.integrableOn_periodic_mul_continuous_compact hg hperiodic hw
        hws z
  have hFtiles : IntegrableOn F tiles := by
    dsimp [tiles]
    exact integrableOn_finset_iUnion.mpr htileInt
  have hcover : ∀ᵐ x ∂(volume : Measure (Vec 2)),
      ∃ z : WeakGradientPeriodization.PeriodTranslations, x ∈ (z : Vec 2) +ᵥ
          WeakGradientPeriodization.PeriodCell := by
    filter_upwards [WeakGradientPeriodization.periodTranslations_fundamentalDomain.ae_covers] with
        x hx
    rcases hx with ⟨z, hz⟩
    refine ⟨-z, ?_⟩
    rw [mem_vadd_set_iff_neg_vadd_mem]
    change (z : Vec 2) + x ∈ WeakGradientPeriodization.PeriodCell at hz
    simpa using hz
  have hFzero : F =ᵐ[volume] tiles.indicator F := by
    filter_upwards [hcover] with x hx
    by_cases hxt : x ∈ tiles
    · simp [hxt]
    · have hwzero : w x = 0 := by
        by_contra hwne
        rcases hx with ⟨z, hxz⟩
        have hy : -(z : Vec 2) + x ∈ WeakGradientPeriodization.PeriodCell := by
          exact (mem_vadd_set_iff_neg_vadd_mem.mp hxz)
        have hzS : z ∈ S := by
          refine ⟨-(z : Vec 2) + x, ⟨?_, WeakGradientPeriodization.periodCell_subset_closure hy⟩⟩
          change w ((-(z : Vec 2) + x) + (z : Vec 2)) ≠ 0
          rw [show (-(z : Vec 2) + x) + (z : Vec 2) = x by abel]
          exact hwne
        have hzFin : z ∈ shifts := hSfinite.mem_toFinset.mpr hzS
        exact hxt (Set.mem_iUnion.2 ⟨z, Set.mem_iUnion.2 ⟨hzFin, hxz⟩⟩)
      simp [hxt, F, hwzero]
  have hFint : Integrable F volume :=
    (hFtiles.integrable_indicator htilesMeas).congr hFzero.symm
  have hzeroTerm (z : WeakGradientPeriodization.PeriodTranslations) (hz : z ∉ shifts) :
      ∫ x in WeakGradientPeriodization.PeriodCell, F (x + (z : Vec 2)) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    by_contra hne
    have hwne : w (x + (z : Vec 2)) ≠ 0 := by
      dsimp [F] at hne
      exact right_ne_zero_of_mul hne
    have hzS : z ∈ S := by
      exact ⟨x, ⟨hwne, WeakGradientPeriodization.periodCell_subset_closure hx⟩⟩
    exact hz (hSfinite.mem_toFinset.mpr hzS)
  have htermInt (z : WeakGradientPeriodization.PeriodTranslations) :
      Integrable (fun x => F (x + (z : Vec 2)))
        (volume.restrict WeakGradientPeriodization.PeriodCell) := by
    by_cases hz : z ∈ shifts
    · have htranslated := htileInt z hz
      change Integrable F (volume.restrict ((z : Vec 2) +ᵥ WeakGradientPeriodization.PeriodCell))
          at htranslated
      have hmp : MeasurePreserving (fun x : Vec 2 => x + (z : Vec 2))
          (volume.restrict WeakGradientPeriodization.PeriodCell)
          (volume.restrict ((z : Vec 2) +ᵥ WeakGradientPeriodization.PeriodCell)) := by
        have hpre : (fun x : Vec 2 => x + (z : Vec 2)) ⁻¹'
            ((z : Vec 2) +ᵥ WeakGradientPeriodization.PeriodCell) =
                WeakGradientPeriodization.PeriodCell := by
          ext x
          change (x + (z : Vec 2) ∈ (z : Vec 2) +ᵥ WeakGradientPeriodization.PeriodCell) ↔ x ∈
              WeakGradientPeriodization.PeriodCell
          simp only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
          rw [show -(z : Vec 2) + (x + (z : Vec 2)) = x by abel]
        simpa [hpre] using
          (measurePreserving_add_right (volume : Measure (Vec 2)) (z : Vec 2)).restrict_preimage
            (WeakGradientPeriodization.periodCell_translate_measurable z)
      exact hmp.integrable_comp_of_integrable htranslated
    · have hzero : ∀ x ∈ WeakGradientPeriodization.PeriodCell, F (x + (z : Vec 2)) = 0 := by
        intro x hx
        by_contra hne
        have hwne : w (x + (z : Vec 2)) ≠ 0 := by
          dsimp [F] at hne
          exact right_ne_zero_of_mul hne
        have hzS : z ∈ S :=
          ⟨x, ⟨hwne, WeakGradientPeriodization.periodCell_subset_closure hx⟩⟩
        exact hz (hSfinite.mem_toFinset.mpr hzS)
      have hconst : Integrable (fun _ : Vec 2 => (0 : ℝ))
          (volume.restrict WeakGradientPeriodization.PeriodCell) := integrable_const 0
      have hAE : (fun x => F (x + (z : Vec 2))) =ᵐ[
          volume.restrict WeakGradientPeriodization.PeriodCell] (fun _ => 0) := by
        filter_upwards [ae_restrict_mem WeakGradientPeriodization.periodCell_measurable] with x hx
        exact hzero x hx
      exact hconst.congr hAE.symm
  have hunfold :=
    WeakGradientPeriodization.periodTranslations_fundamentalDomain.integral_eq_tsum'' F hFint
  have hunfold' : ∫ x, F x =
      ∑' z : WeakGradientPeriodization.PeriodTranslations, ∫ x in
          WeakGradientPeriodization.PeriodCell, F (x + (z : Vec 2)) := by
    convert hunfold using 1
    apply tsum_congr
    intro z
    apply setIntegral_congr_fun WeakGradientPeriodization.periodCell_measurable
    intro x hx
    simp only [AddSubgroup.vadd_def, vadd_eq_add]
    change F (x + (z : Vec 2)) = F ((z : Vec 2) + x)
    congr 1
    abel
  rw [hunfold', tsum_eq_sum (s := shifts) (fun z hz => hzeroTerm z hz)]
  constructor
  · exact hFint
  · calc
      (∑ z ∈ shifts, ∫ x in WeakGradientPeriodization.PeriodCell, F (x + (z : Vec 2))) =
          ∫ x in WeakGradientPeriodization.PeriodCell, ∑ z ∈ shifts, F (x + (z : Vec 2)) :=
            (integral_finsetSum (s := shifts) (μ := volume.restrict
                WeakGradientPeriodization.PeriodCell)
              (f := fun z x => F (x + (z : Vec 2))) (fun z hz => htermInt z)).symm
      _ = ∫ x in WeakGradientPeriodization.PeriodCell, g x * compactTestPeriodization w x := by
        apply setIntegral_congr_fun WeakGradientPeriodization.periodCell_measurable
        intro x hx
        have hsupport : Function.support (fun z : WeakGradientPeriodization.PeriodTranslations =>
            w (x + (z : Vec 2))) ⊆ shifts := by
          intro z hz
          have hwne : w (x + (z : Vec 2)) ≠ 0 := by
            simpa [Function.mem_support] using hz
          have hzS : z ∈ S := by
            exact ⟨x, ⟨hwne, WeakGradientPeriodization.periodCell_subset_closure hx⟩⟩
          exact hSfinite.mem_toFinset.mpr hzS
        have hperiodized : compactTestPeriodization w x =
            ∑ z ∈ shifts, w (x + (z : Vec 2)) := by
          dsimp [compactTestPeriodization]
          rw [finsum_eq_sum_of_support_subset _ hsupport]
        calc
          (∑ z ∈ shifts, F (x + (z : Vec 2))) =
              ∑ z ∈ shifts, g x * w (x + (z : Vec 2)) := by
                apply Finset.sum_congr rfl
                intro z hz
                dsimp [F]
                rw [show g (x + (z : Vec 2)) = g x by
                  rw [WeakGradientPeriodization.periodTranslationIndex_spec z]
                  exact hperiodic (WeakGradientPeriodization.periodTranslationIndex z) x]
          _ = g x * ∑ z ∈ shifts, w (x + (z : Vec 2)) := by
                rw [← Finset.mul_sum]
          _ = g x * compactTestPeriodization w x := by rw [← hperiodized]

theorem compactTestPeriodization_contDiff {φ : Vec 2 → ℝ}
    (hφ : HasCompactSupport φ) (hφsmooth : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (compactTestPeriodization φ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hloc := WeakGradientPeriodization.periodized_family_locallyFinite hφ x
  obtain ⟨U, hU, hfinite⟩ := hloc
  let S : Set WeakGradientPeriodization.PeriodTranslations := {z | (({y | φ (y + (z : Vec 2)) ≠ 0}
      ∩ U).Nonempty)}
  have hS : S.Finite := hfinite
  let s : Finset WeakGradientPeriodization.PeriodTranslations := hS.toFinset
  have hsumSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Vec 2 => ∑ z ∈ s, φ (y + (z : Vec 2))) := by
    apply ContDiff.sum
    intro z hz
    exact hφsmooth.comp (contDiff_id.add contDiff_const)
  have heq : (fun y : Vec 2 => compactTestPeriodization φ y) =ᶠ[𝓝 x]
      fun y => ∑ z ∈ s, φ (y + (z : Vec 2)) := by
    filter_upwards [hU] with y hy
    dsimp [compactTestPeriodization]
    have hsupport : Function.support (fun z : WeakGradientPeriodization.PeriodTranslations =>
        φ (y + (z : Vec 2))) ⊆ s := by
      intro z hz
      apply Finset.mem_coe.mp
      have hzS : z ∈ S := by
        change (({w : Vec 2 | φ (w + (z : Vec 2)) ≠ 0} ∩ U).Nonempty)
        exact ⟨y, ⟨by simpa using hz, hy⟩⟩
      exact hS.mem_toFinset.mpr hzS
    rw [finsum_eq_sum_of_support_subset _ hsupport]
  exact hsumSmooth.contDiffAt.congr_of_eventuallyEq heq

theorem WeakGradientPeriodization.compactTestPeriodization_periodic_translation (φ : Vec 2 → ℝ)
    (z : WeakGradientPeriodization.PeriodTranslations) (x : Vec 2) :
    compactTestPeriodization φ (x + (z : Vec 2)) = compactTestPeriodization φ x := by
  dsimp [compactTestPeriodization]
  have harg : ∀ w : WeakGradientPeriodization.PeriodTranslations,
      (x + (z : Vec 2)) + (w : Vec 2) = x + ((z + w :
          WeakGradientPeriodization.PeriodTranslations) : Vec 2) := by
    intro w
    simp only [AddSubgroup.coe_add]
    abel
  simp_rw [harg]
  exact finsum_comp (Equiv.addLeft z) (Equiv.addLeft z).bijective
    (g := fun w : WeakGradientPeriodization.PeriodTranslations => φ (x + (w : Vec 2)))

theorem compactTestPeriodization_periodic {φ : Vec 2 → ℝ} :
    AVenhance.IsZ2Periodic (compactTestPeriodization φ) := by
  intro k x
  let z : Vec 2 := AVenhance.latticeShift k
  have hz : z ∈ WeakGradientPeriodization.PeriodLattice := by
    change z ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2)))
    rw [(Pi.basisFun ℝ (Fin 2)).mem_span_iff_repr_mem ℤ]
    intro i
    simp [z, AVenhance.latticeShift, Pi.basisFun_repr]
  let zL : WeakGradientPeriodization.PeriodTranslations := ⟨z, hz⟩
  have h := WeakGradientPeriodization.compactTestPeriodization_periodic_translation φ zL x
  simpa [zL, z] using h

theorem compactTestPeriodization_spaceGrad_eq {φ : Vec 2 → ℝ}
    (hφ : HasCompactSupport φ) (hφsmooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (compactTestPeriodization φ) x i =
      ∑ᶠ z : WeakGradientPeriodization.PeriodTranslations,
        AVenhance.spaceGrad φ (x + (z : Vec 2)) i := by
  classical
  have hloc := WeakGradientPeriodization.periodized_family_locallyFinite hφ x
  obtain ⟨U, hU, hfinite⟩ := hloc
  let S : Set WeakGradientPeriodization.PeriodTranslations := {z | (({y | φ (y + (z : Vec 2)) ≠ 0}
      ∩ U).Nonempty)}
  have hS : S.Finite := hfinite
  let s : Finset WeakGradientPeriodization.PeriodTranslations := hS.toFinset
  have heq : (fun y : Vec 2 => compactTestPeriodization φ y) =ᶠ[𝓝 x]
      fun y => ∑ z ∈ s, φ (y + (z : Vec 2)) := by
    filter_upwards [hU] with y hy
    dsimp [compactTestPeriodization]
    have hsupport : Function.support (fun z : WeakGradientPeriodization.PeriodTranslations =>
        φ (y + (z : Vec 2))) ⊆ s := by
      intro z hz
      apply Finset.mem_coe.mp
      have hzS : z ∈ S := by
        change (({w : Vec 2 | φ (w + (z : Vec 2)) ≠ 0} ∩ U).Nonempty)
        exact ⟨y, ⟨by simpa using hz, hy⟩⟩
      exact hS.mem_toFinset.mpr hzS
    rw [finsum_eq_sum_of_support_subset _ hsupport]
  have hderiv : fderiv ℝ (compactTestPeriodization φ) x =
      fderiv ℝ (fun y : Vec 2 => ∑ z ∈ s, φ (y + (z : Vec 2))) x := heq.fderiv_eq
  have hfiniteDeriv :
      fderiv ℝ (fun y : Vec 2 => ∑ z ∈ s, φ (y + (z : Vec 2))) x =
        ∑ z ∈ s, fderiv ℝ (fun y : Vec 2 => φ (y + (z : Vec 2))) x := by
    rw [fderiv_fun_sum (u := s)
      (A := fun (z : WeakGradientPeriodization.PeriodTranslations) (y : Vec 2) => φ (y + (z : Vec
          2)))
      (fun z hz => ((hφsmooth.comp (contDiff_id.add contDiff_const)).differentiable
        (by norm_num)).differentiableAt)]
  have hterms (z : WeakGradientPeriodization.PeriodTranslations) :
      fderiv ℝ (fun y : Vec 2 => φ (y + (z : Vec 2))) x =
        fderiv ℝ φ (x + (z : Vec 2)) := by
    exact fderiv_comp_add_right (z : Vec 2)
  have hderivSupport : Function.support (fun z : WeakGradientPeriodization.PeriodTranslations =>
      AVenhance.spaceGrad φ (x + (z : Vec 2)) i) ⊆ s := by
    intro z hz
    by_contra hzNotMem
    have hzNotS : z ∉ S := by
      intro hzS
      exact hzNotMem (hS.mem_toFinset.mpr hzS)
    have hzero : (fun y : Vec 2 => φ (y + (z : Vec 2))) =ᶠ[𝓝 x]
        fun _ => 0 := by
      filter_upwards [hU] with y hy
      by_contra hne
      exact hzNotS ⟨y, ⟨by simpa using hne, hy⟩⟩
    have hzeroDeriv :
        fderiv ℝ (fun y : Vec 2 => φ (y + (z : Vec 2))) x =
          fderiv ℝ (fun _ : Vec 2 => (0 : ℝ)) x := hzero.fderiv_eq
    have hcoord := congrArg (fun L : Vec 2 →L[ℝ] ℝ => L (Homogenization.basisVec i)) hzeroDeriv
    have hgrad : AVenhance.spaceGrad φ (x + (z : Vec 2)) i = 0 := by
      change fderiv ℝ φ (x + (z : Vec 2)) (Homogenization.basisVec i) = 0
      rw [← hterms z]
      simpa using hcoord
    exact hz (by simpa [Function.mem_support] using hgrad)
  have hsumDeriv :
      (∑ z ∈ s, AVenhance.spaceGrad φ (x + (z : Vec 2)) i) =
        ∑ᶠ z : WeakGradientPeriodization.PeriodTranslations, AVenhance.spaceGrad φ (x + (z : Vec
            2)) i := by
    symm
    exact finsum_eq_sum_of_support_subset _ hderivSupport
  change fderiv ℝ (compactTestPeriodization φ) x (Homogenization.basisVec i) = _
  rw [hderiv, hfiniteDeriv]
  simp_rw [hterms]
  simpa [AVenhance.spaceGrad, ContinuousLinearMap.toLinearMap_sum,
    LinearMap.sum_apply] using hsumDeriv

/-- Fourier weak-derivative identities imply the global weak-gradient clause. A compact
Euclidean test is periodized, the cell identity is applied to that smooth periodic test, and the
two resulting cell pairings are unfolded back to `ℝ²`. -/
theorem hasWeakGradientOn_of_realFourierModes
    {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (hu : MemLp u 2 (volume.restrict AVenhance.unitCube))
    (hDu : ∀ i : Fin 2,
      MemLp (fun x => Du x i) 2 (volume.restrict AVenhance.unitCube))
    (hperiodicU : AVenhance.IsZ2Periodic u)
    (hperiodicDu : AVenhance.IsZ2Periodic Du)
    (hmode : ∀ i : Fin 2, ∀ N : ℕ, ∀ j : Fin (RealFourierDimension N),
      ∫ x in AVenhance.unitCube,
        u x * AVenhance.spaceGrad
          (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j)) x i =
      -∫ x in AVenhance.unitCube,
        Du x i * realFourierModeAmbient N
          ((realFourierIndexEquivFin N).symm j) x) :
    HasWeakGradientOn Set.univ u Du := by
  intro i φ hφsmooth hφcompact hφsupport
  let w : Vec 2 → ℝ := fun x => AVenhance.spaceGrad φ x i
  have hwcont : Continuous w := by
    dsimp [w, AVenhance.spaceGrad]
    exact (hφsmooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hwcompact : HasCompactSupport w := by
    dsimp [w, AVenhance.spaceGrad]
    exact hφcompact.fderiv_apply (𝕜 := ℝ) (Homogenization.basisVec i)
  have hduperiodic : AVenhance.IsZ2Periodic (fun x => Du x i) := by
    intro k x
    exact congrFun (hperiodicDu k x) i
  have hperiodSmooth := compactTestPeriodization_contDiff hφcompact hφsmooth
  have hperiodPeriodic := compactTestPeriodization_periodic (φ := φ)
  have hcell := cellWeakDerivative_of_realFourierModes
    hu (hDu i) i (fun N j => hmode i N j) hperiodSmooth hperiodPeriodic
  have hleft := WeakGradientPeriodization.integral_periodic_mul_compact_eq_cell_periodization
    hu hperiodicU hwcont hwcompact
  have hright := WeakGradientPeriodization.integral_periodic_mul_compact_eq_cell_periodization
    (hDu i) hduperiodic hφsmooth.continuous hφcompact
  have hperiodDerivative (x : Vec 2) :
      compactTestPeriodization w x =
        AVenhance.spaceGrad (compactTestPeriodization φ) x i := by
    dsimp [w]
    rw [compactTestPeriodization_spaceGrad_eq hφcompact hφsmooth i x]
    rfl
  have hcell' :
      ∫ x in WeakGradientPeriodization.PeriodCell, u x * compactTestPeriodization w x =
      -∫ x in WeakGradientPeriodization.PeriodCell,
        Du x i * compactTestPeriodization φ x := by
    calc
      ∫ x in WeakGradientPeriodization.PeriodCell, u x * compactTestPeriodization w x =
              ∫ x in AVenhance.unitCube,
            u x * AVenhance.spaceGrad (compactTestPeriodization φ) x i := by
              rw [MeasureTheory.setIntegral_congr_set
                  WeakGradientPeriodization.periodCell_ae_unitCube]
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun x =>
                congrArg (fun a => u x * a) (hperiodDerivative x)
      _ = -∫ x in AVenhance.unitCube,
            Du x i * compactTestPeriodization φ x := hcell
      _ = -∫ x in WeakGradientPeriodization.PeriodCell,
            Du x i * compactTestPeriodization φ x := by
              rw [MeasureTheory.setIntegral_congr_set
                  WeakGradientPeriodization.periodCell_ae_unitCube]
  have hglobalLeft : Integrable (fun x => u x * w x) volume ∧
      ∫ x, u x * w x =
        ∫ x in WeakGradientPeriodization.PeriodCell, u x * compactTestPeriodization w x := hleft
  have hglobalRight : Integrable (fun x => Du x i * φ x) volume ∧
      ∫ x, Du x i * φ x =
        ∫ x in WeakGradientPeriodization.PeriodCell, Du x i * compactTestPeriodization φ x := hright
  simpa only [MeasureTheory.setIntegral_univ, AVenhance.spaceGrad, w] using
    hglobalLeft.2.trans (hcell'.trans (congrArg Neg.neg hglobalRight.2.symm))

/-- A periodic cell-`L²` function paired with a continuous compactly supported test is globally
integrable. This is the integrability bridge needed to take linear combinations of global weak
derivative identities. -/
theorem periodic_compact_pairing_integrable
    {u w : Vec 2 → ℝ} (hu : MemL2On AVenhance.unitCube u)
    (hperiodic : AVenhance.IsZ2Periodic u) (hw : Continuous w)
    (hws : HasCompactSupport w) :
    Integrable (fun x => u x * w x) volume :=
  (WeakGradientPeriodization.integral_periodic_mul_compact_eq_cell_periodization hu hperiodic hw
      hws).1

end AVenhance.Infra.Parabolic.FourierGalerkin

end
