/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Measure.GiryMonad


/-!
# Measurability of finite Radon measure families

On a second-countable locally compact Hausdorff space, a family of finite
regular measures is measurable when integration against every compactly
supported real continuous function is measurable.  The proof uses compact
exhaustions and Urysohn cutoffs to make every open-set evaluation a countable
supremum of measurable test integrals, then applies Mathlib's Giry
π-system criterion.

The compact exhaustion and cutoff choices are private implementation details.
-/

@[expose] public section

open scoped CompactlySupported ENNReal NNReal Topology
open Set MeasureTheory TopologicalSpace

namespace MeasureTheory

namespace MeasurableRadonFamily

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

private noncomputable def compactSet (U : Set X) (hU : IsOpen U) (n : ℕ) : Set X := by
  letI := hU.locallyCompactSpace
  exact Subtype.val '' CompactExhaustion.choice U n

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
private lemma compactSet_isCompact (U : Set X) (hU : IsOpen U) (n : ℕ) :
    IsCompact (compactSet U hU n) := by
  let := hU.locallyCompactSpace
  exact (CompactExhaustion.choice U).isCompact n |>.image continuous_subtype_val

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
private lemma compactSet_subset (U : Set X) (hU : IsOpen U) (n : ℕ) :
    compactSet U hU n ⊆ U :=
  image_subset_iff.mpr fun x _ ↦ x.property

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
private lemma iUnion_compactSet (U : Set X) (hU : IsOpen U) :
    ⋃ n, compactSet U hU n = U := by
  let := hU.locallyCompactSpace
  ext x
  simp only [compactSet, mem_iUnion, mem_image]
  constructor
  · rintro ⟨n, y, -, rfl⟩
    exact y.property
  · intro hx
    let y : U := ⟨x, hx⟩
    obtain ⟨n, hn⟩ := (CompactExhaustion.choice U).exists_mem y
    exact ⟨n, y, hn, rfl⟩

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
private lemma compactSet_mono (U : Set X) (hU : IsOpen U) :
    Monotone (compactSet U hU) := by
  let := hU.locallyCompactSpace
  intro m n hmn
  exact image_mono ((CompactExhaustion.choice U).subset hmn)

private noncomputable def openCutoff (U : Set X) (hU : IsOpen U) (n : ℕ) : C_c(X, ℝ) := by
  choose f hf using exists_continuousMap_one_of_isCompact_subset_isOpen
    (compactSet_isCompact U hU n) hU (compactSet_subset U hU n)
  exact ⟨f, hasCompactSupport_def.mpr hf.2.1⟩

omit [MeasurableSpace X] [BorelSpace X] in
private lemma cutoff_eq_one (U : Set X) (hU : IsOpen U) (n : ℕ) :
    Set.EqOn (openCutoff U hU n) 1 (compactSet U hU n) := by
  unfold openCutoff
  exact Classical.choose_spec
    (exists_continuousMap_one_of_isCompact_subset_isOpen
      (compactSet_isCompact U hU n) hU (compactSet_subset U hU n)) |>.1

omit [MeasurableSpace X] [BorelSpace X] in
private lemma cutoff_tsupport_subset (U : Set X) (hU : IsOpen U) (n : ℕ) :
    tsupport (openCutoff U hU n) ⊆ U := by
  unfold openCutoff
  exact Classical.choose_spec
    (exists_continuousMap_one_of_isCompact_subset_isOpen
      (compactSet_isCompact U hU n) hU (compactSet_subset U hU n)) |>.2.2.1

omit [MeasurableSpace X] [BorelSpace X] in
private lemma cutoff_mem_Icc (U : Set X) (hU : IsOpen U) (n : ℕ) (x : X) :
    openCutoff U hU n x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold openCutoff
  exact Classical.choose_spec
    (exists_continuousMap_one_of_isCompact_subset_isOpen
      (compactSet_isCompact U hU n) hU (compactSet_subset U hU n)) |>.2.2.2 x

private lemma measure_open_eq_iSup_integral_cutoff (U : Set X) (hU : IsOpen U)
    (ν : Measure X) [IsFiniteMeasure ν] :
    ν U = ⨆ n, ENNReal.ofReal (∫ x, openCutoff U hU n x ∂ν) := by
  apply le_antisymm
  · have hmeasure : ν U = ⨆ n, ν (compactSet U hU n) := by
      calc
        ν U = ν (⋃ n, compactSet U hU n) := congrArg ν (iUnion_compactSet U hU).symm
        _ = ⨆ n, ν (compactSet U hU n) := (compactSet_mono U hU).measure_iUnion
    rw [hmeasure]
    refine iSup_le fun n ↦ ?_
    refine le_trans ?_ (le_iSup (fun n ↦ ENNReal.ofReal (∫ x, openCutoff U hU n x ∂ν)) n)
    rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (integral_nonneg
      fun x ↦ (cutoff_mem_Icc U hU n x).1)]
    rw [← measureReal_def, ← integral_indicator_one (compactSet_isCompact U hU n).measurableSet]
    refine integral_mono ?_ (openCutoff U hU n).integrable fun x ↦ ?_
    · exact
        (continuousOn_const.integrableOn_compact
          (compactSet_isCompact U hU n)).integrable_indicator
            (compactSet_isCompact U hU n).measurableSet
    · by_cases hx : x ∈ compactSet U hU n
      · rw [indicator_of_mem hx, Pi.one_apply, cutoff_eq_one U hU n hx, Pi.one_apply]
      · exact (indicator_of_notMem hx _).trans_le (cutoff_mem_Icc U hU n x).1
  · refine iSup_le fun n ↦ ?_
    rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
    rw [← measureReal_def, ← integral_indicator_one hU.measurableSet]
    refine integral_mono (openCutoff U hU n).integrable ?_ fun x ↦ ?_
    · exact IntegrableOn.integrable_indicator integrableOn_const hU.measurableSet
    · by_cases hx : x ∈ tsupport (openCutoff U hU n)
      · simp only [indicator_of_mem (cutoff_tsupport_subset U hU n hx), Pi.one_apply]
        exact (cutoff_mem_Icc U hU n x).2
      · rw [image_eq_zero_of_notMem_tsupport hx]
        exact (indicator_nonneg fun _ _ ↦ zero_le_one) x

end MeasurableRadonFamily

/-- A finite regular measure family is Giry-measurable when all of its
compactly supported continuous test integrals are measurable. -/
theorem measurable_measure_of_measurable_integral_compactlySupported
    {Q X : Type*} [MeasurableSpace Q]
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μ : Q → Measure X) [∀ q, IsFiniteMeasure (μ q)]
    (hμ : ∀ f : C_c(X, ℝ), Measurable fun q ↦ ∫ x, f x ∂μ q) :
    Measurable μ := by
  refine Measurable.measure_of_isPiSystem (S := generatePiSystem (countableBasis X))
    (by rw [BorelSpace.measurable_eq (α := X), (isBasis_countableBasis X).borel_eq_generateFrom,
      generateFrom_generatePiSystem_eq])
    (isPiSystem_generatePiSystem _) ?_ ?_
  · intro U hU
    have hU_open : IsOpen U := by
      induction hU using generatePiSystem_induction with
      | base _ h => exact isOpen_of_mem_countableBasis h
      | inter _ _ _ _ _ hs ht => exact hs.inter ht
    have heval : (fun q ↦ μ q U) = fun q ↦
        ⨆ n, ENNReal.ofReal (∫ x, MeasurableRadonFamily.openCutoff U hU_open n x ∂μ q) := by
      funext q
      exact MeasurableRadonFamily.measure_open_eq_iSup_integral_cutoff U hU_open (μ q)
    rw [heval]
    exact Measurable.iSup fun n ↦ (hμ (MeasurableRadonFamily.openCutoff U hU_open n)).ennreal_ofReal
  · have heval : (fun q ↦ μ q Set.univ) = fun q ↦
        ⨆ n, ENNReal.ofReal
          (∫ x, MeasurableRadonFamily.openCutoff Set.univ isOpen_univ n x ∂μ q) := by
      funext q
      exact MeasurableRadonFamily.measure_open_eq_iSup_integral_cutoff Set.univ isOpen_univ (μ q)
    rw [heval]
    exact Measurable.iSup fun n ↦
      (hμ (MeasurableRadonFamily.openCutoff Set.univ isOpen_univ n)).ennreal_ofReal

end MeasureTheory
