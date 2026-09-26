/-
Copyright (c) 2026 Petr Girg, Petr Nečesal, Martin Dvořák, Jakub Psutka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Petr Girg, Petr Nečesal, Martin Dvořák, Jakub Psutka
-/

module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import LeanPool.NemytskiiLebesgue.Basic

/-!
# Nemytskii operators: Caratheodory

Adapted from `madvorak/nemytskii-lebesgue` (Apache-2.0).
-/

public section

namespace NemytskiiLebesgue

open scoped NemytskiiLebesgue

open MeasureTheory TopologicalSpace Filter
open scoped Topology

/--
A function `f : Ω → D → F` is **Carathéodory** with respect to a measure `μ` if:
(1) For every `x ∈ D`, the mapping `(f · x)` is strongly measurable.
(2) For almost every `ω ∈ Ω` with respect to `μ`, the mapping `(f ω ·)` is continuous.
-/
structure IsCaratheodory {Ω D F : Type*}
    [MeasurableSpace Ω] [TopologicalSpace D] [TopologicalSpace F]
    (f : Ω → D → F) (μ : Measure Ω) :
    Prop where
  isStronglyMeasurable : ∀ x : D, StronglyMeasurable (f · x)
  ae_continuous : ∀ᵐ ω : Ω ∂μ, Continuous (f ω)

theorem normSMulSelf_isCaratheodory
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ} :
    IsCaratheodory (@normSMulSelf Ω n) μ :=
  ⟨↓stronglyMeasurable_const, ae_of_all _ ↓(continuous_norm.smul continuous_id)⟩

lemma aestronglyMeasurable_composition_of_stronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F] [PseudoMetrizableSpace F]
    {f : Ω → D → F} (hf : ∀ x : D, AEStronglyMeasurable (f · x) μ) (hf' : ∀ᵐ ω : Ω ∂μ, Continuous
      (f ω))
    {g : Ω → D} (hg : StronglyMeasurable g) :
    AEStronglyMeasurable (fun ω : Ω => f ω (g ω)) μ := by
  have converg : ∀ᵐ ω : Ω ∂μ, Tendsto (fun n : ℕ => f ω (hg.approx n ω)) atTop (𝓝 (f ω (g ω))) := by
    filter_upwards [hf'] with ω hω using hω.continuousAt.tendsto.comp (hg.tendsto_approx ω)
  have measurabl : ∀ n : ℕ, AEStronglyMeasurable (fun ω : Ω => f ω (hg.approx n ω)) μ := by
    intro n
    have measurab : ∀ s : Set Ω, MeasurableSet s → AEStronglyMeasurable (fun ω : Ω => f ω
      (hg.approx n ω)) (μ.restrict s) := by
      intro s hs
      have measura : ∀ d : D, AEStronglyMeasurable (f · d) (μ.restrict (s ∩ { ω : Ω | hg.approx n ω
        = d })) :=
        (hf · |>.mono_measure Measure.restrict_le_self)
      have measura' :
        ∀ d ∈ Set.range (hg.approx n),
          AEStronglyMeasurable (fun ω : Ω => f ω (hg.approx n ω)) (μ.restrict (s ∩ { ω : Ω |
            hg.approx n ω = d })) := by
        intro d hd
        exact
          (measura d).congr
            (eventuallyEq_of_mem
              (ae_restrict_mem (hs.inter ((hg.approx n).measurableSet_fiber d)))
              ↓↓(by simp_all))
      have measur :
        ∀ S : Finset D,
          (∀ d ∈ S, AEStronglyMeasurable (fun ω : Ω => f ω (hg.approx n ω)) (μ.restrict (         s
            ∩ { ω : Ω | hg.approx n ω = d }))) →
                    AEStronglyMeasurable (fun ω : Ω => f ω (hg.approx n ω)) (μ.restrict (⋃ d ∈ S, s
                      ∩ { ω : Ω | hg.approx n ω = d })) := by
        intro S hS
        classical
        induction S using Finset.induction <;> simp_all
      convert measur (hg.approx n).finite_range.toFinset _ <;> aesop
    simpa using measurab ⊤ MeasurableSet.univ
  exact aestronglyMeasurable_of_tendsto_ae _ measurabl converg

theorem aestronglyMeasurable_composition
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F] [PseudoMetrizableSpace F]
    {f : Ω → D → F} (hf : ∀ x : D, AEStronglyMeasurable (f · x) μ) (hf' : ∀ᵐ ω : Ω ∂μ, Continuous
      (f ω))
    {g : Ω → D} (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun ω : Ω => f ω (g ω)) μ := by
  have ae_eq_mk : ∀ᵐ ω : Ω ∂μ, f ω (g ω) = f ω (hg.mk g ω) := by
    filter_upwards [hf', hg.ae_eq_mk] with ω hfω huω
    congr
  apply (aestronglyMeasurable_composition_of_stronglyMeasurable hf hf'
    hg.stronglyMeasurable_mk).congr
  filter_upwards [ae_eq_mk] with ω hω
  simp [hω]

theorem IsCaratheodory.aestronglyMeas_nemytskii_of_aestronglyMeas
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F] [PseudoMetrizableSpace F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {g : Ω → D} (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun ω : Ω => f ω (g ω)) μ :=
  aestronglyMeasurable_composition
    (hf.isStronglyMeasurable ·|>.aestronglyMeasurable)
    hf.ae_continuous
    hg

theorem IsCaratheodory.aestronglyMeas_nemytskii_of_aeMeas_real
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ} {D : Set ℝ^m}
    {f : Ω → D → ℝ^k} (hf : IsCaratheodory f μ)
    {g : Ω → D} (hg : AEMeasurable g μ) :
    AEStronglyMeasurable (fun ω : Ω => f ω (g ω)) μ :=
  hf.aestronglyMeas_nemytskii_of_aestronglyMeas hg.aestronglyMeasurable

theorem IsCaratheodory.aeMeas_nemytskii_of_aeMeas_real
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ} {D : Set ℝ^m}
    {f : Ω → D → ℝ^k} (hf : IsCaratheodory f μ)
    {g : Ω → D} (hg : AEMeasurable g μ) :
    AEMeasurable (fun ω : Ω => f ω (g ω)) μ :=
  (hf.aestronglyMeas_nemytskii_of_aeMeas_real hg).aemeasurable

end NemytskiiLebesgue
