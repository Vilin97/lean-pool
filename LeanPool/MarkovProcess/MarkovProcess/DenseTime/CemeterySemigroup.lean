/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.DenseTime.CemeteryExtension
public import LeanPool.MarkovProcess.MarkovProcess.Kernel.KernelSemigroup


/-!
# Cemetery extensions of sub-Markov kernel semigroups

This file shows that conservative cemetery extension preserves the identity
kernel and composition of sub-Markov kernels.  Consequently, applying the
extension at every time turns any sub-Markov kernel semigroup into a
conservative semigroup on the cemetery state space.
-/

@[expose] public section

noncomputable section PortComputability

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

section

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]

namespace Kernel

/-- Conservative cemetery extension preserves the identity kernel. -/
theorem cemeteryExtension_id :
    cemeteryExtension (Kernel.id : Kernel α α) = Kernel.id := by
  ext z s hs
  cases z with
  | inl x =>
      rw [cemeteryExtension_alive_apply' _ x hs, Kernel.id_apply,
        Measure.dirac_apply' _ (measurable_inl hs)]
      simp only [Measure.dirac_apply' _ MeasurableSet.univ, Set.mem_univ,
        Set.indicator_of_mem, Pi.one_apply, tsub_self, zero_mul, add_zero,
        ]
      rw [Kernel.id_apply, Measure.dirac_apply' _ hs]
      rfl
  | inr u =>
      cases u
      rw [cemeteryExtension_delta_apply' _ hs, Kernel.id_apply,
        Measure.dirac_apply' _ hs]

/-- On live measurable sets, cemetery extension preserves kernel composition. -/
theorem cemeteryExtension_comp_alive_image (η κ : Kernel α α)
    (x : α) {s : Set α} (hs : MeasurableSet s) :
    cemeteryExtension (η.comp κ) (Cemetery.alive x) (Cemetery.alive '' s) =
      ((cemeteryExtension η).comp (cemeteryExtension κ))
        (Cemetery.alive x) (Cemetery.alive '' s) := by
  rw [cemeteryExtension_alive_image _ x hs, Kernel.comp_apply' _ _ _ hs.inl_image,
    cemeteryExtension_alive_apply, lintegral_add_measure,
    lintegral_map ((cemeteryExtension η).measurable_coe hs.inl_image) measurable_inl]
  have hnot : Cemetery.delta ∉ Cemetery.alive '' s := by
    rintro ⟨a, -, h⟩
    exact Sum.inl_ne_inr h
  simp only [cemeteryExtension_alive_image _ _ hs, lintegral_smul_measure]
  rw [MeasureTheory.lintegral_dirac' Cemetery.delta
    ((cemeteryExtension η).measurable_coe hs.inl_image)]
  rw [cemeteryExtension_delta_apply' _ hs.inl_image, Set.indicator_of_notMem hnot,
    smul_zero, add_zero]
  rw [Kernel.comp_apply' _ _ _ hs]

/-- Conservative cemetery extension preserves composition of sub-Markov kernels. -/
theorem cemeteryExtension_comp (η κ : Kernel α α)
    (hη : IsSubMarkovKernel η) (hκ : IsSubMarkovKernel κ) :
    cemeteryExtension (η.comp κ) =
      (cemeteryExtension η).comp (cemeteryExtension κ) := by
  have hηκ : IsSubMarkovKernel (η.comp κ) := hη.comp hκ
  have hleft : IsMarkovKernel (cemeteryExtension (η.comp κ)) :=
    isMarkovKernel_cemeteryExtension _ hηκ
  have hright : IsMarkovKernel ((cemeteryExtension η).comp (cemeteryExtension κ)) := by
    let : IsMarkovKernel (cemeteryExtension η) := isMarkovKernel_cemeteryExtension _ hη
    let : IsMarkovKernel (cemeteryExtension κ) := isMarkovKernel_cemeteryExtension _ hκ
    infer_instance
  ext z u hu
  cases z with
  | inr v =>
      cases v
      rw [cemeteryExtension_delta_apply' _ hu, Kernel.comp_apply' _ _ _ hu,
        cemeteryExtension_delta_apply, MeasureTheory.lintegral_dirac',
        cemeteryExtension_delta_apply' _ hu]
      exact (cemeteryExtension η).measurable_coe hu
  | inl x =>
      let live : Set (Cemetery α) := Cemetery.alive '' (Cemetery.alive ⁻¹' u)
      have hlive : MeasurableSet live := (measurable_inl hu).inl_image
      have hlive_eq : live = u \ {Cemetery.delta} := by
        ext y
        cases y with
        | inl a =>
            constructor
            · rintro ⟨b, hb, hba⟩
              injection hba with hba
              subst b
              exact ⟨hb, Sum.inl_ne_inr⟩
            · rintro ⟨ha, -⟩
              exact ⟨a, ha, rfl⟩
        | inr v =>
            cases v
            simp only [live, Cemetery.alive, Cemetery.delta, Set.mem_image,
              Set.mem_preimage, Set.mem_sdiff, Set.mem_singleton_iff,
              not_true_eq_false, and_false, Sum.inl_ne_inr, exists_false]
      have hlive_agree :
          cemeteryExtension (η.comp κ) (Cemetery.alive x) live =
            ((cemeteryExtension η).comp (cemeteryExtension κ))
              (Cemetery.alive x) live := by
        exact cemeteryExtension_comp_alive_image η κ x (measurable_inl hu)
      by_cases hδ : Cemetery.delta ∈ u
      · have hu_union : u = live ∪ {Cemetery.delta} := by
          rw [hlive_eq]
          exact (Set.sdiff_union_of_subset (Set.singleton_subset_iff.mpr hδ)).symm
        have hdisj : Disjoint live ({Cemetery.delta} : Set (Cemetery α)) := by
          rw [hlive_eq]
          exact Set.disjoint_sdiff_left
        have hdelta : MeasurableSet ({Cemetery.delta} : Set (Cemetery α)) := by
          simpa only [Set.range_unique] using
            (measurableSet_range_inr : MeasurableSet (Set.range (Sum.inr : Unit → α ⊕ Unit)))
        rw [hu_union, measure_union hdisj hdelta,
          measure_union hdisj hdelta, hlive_agree]
        congr 1
        let allLive : Set (Cemetery α) := Cemetery.alive '' (Set.univ : Set α)
        have hall :
            cemeteryExtension (η.comp κ) (Cemetery.alive x) allLive =
              ((cemeteryExtension η).comp (cemeteryExtension κ))
                (Cemetery.alive x) allLive :=
          cemeteryExtension_comp_alive_image η κ x MeasurableSet.univ
        have hcomp : allLiveᶜ = ({Cemetery.delta} : Set (Cemetery α)) := by
          ext y
          cases y with
          | inl a =>
              simp only [allLive, Cemetery.alive, Cemetery.delta, Set.mem_compl_iff,
                Set.mem_image, Set.mem_univ, true_and, Sum.inl.injEq,
                Set.mem_singleton_iff, Sum.inl_ne_inr, iff_false]
              exact fun h ↦ h ⟨a, rfl⟩
          | inr v =>
              cases v
              simp only [allLive, Cemetery.alive, Cemetery.delta, Set.mem_compl_iff,
                Set.mem_image, Set.mem_univ, true_and, Sum.inl_ne_inr,
                Set.mem_singleton_iff, not_exists]
              exact iff_true_intro fun _ ↦ id
        have hall_meas : MeasurableSet allLive := MeasurableSet.univ.inl_image
        rw [← hcomp, measure_compl hall_meas (measure_ne_top _ _),
          measure_compl hall_meas (measure_ne_top _ _),
          hleft.isProbabilityMeasure (Cemetery.alive x) |>.measure_univ,
          hright.isProbabilityMeasure (Cemetery.alive x) |>.measure_univ, hall]
      · have hu_eq : u = live := by
          rw [hlive_eq]
          ext y
          constructor
          · intro hy
            exact ⟨hy, fun hyδ ↦ hδ (hyδ ▸ hy)⟩
          · exact fun hy ↦ hy.1
        rw [hu_eq, hlive_agree]

end Kernel

namespace SubMarkovKernelSemigroup

/-- The conservative cemetery extension of a sub-Markov kernel semigroup. -/
noncomputable def cemeterySemigroup (P : SubMarkovKernelSemigroup α) :
    SubMarkovKernelSemigroup (Cemetery α) where
  kernel t := Kernel.cemeteryExtension (P t)
  measurable_kernel := by
    let e : NNReal × Cemetery α ≃ᵐ (NNReal × α) ⊕ (NNReal × Unit) :=
      MeasurableEquiv.prodSumDistrib _ _ _
    apply e.symm.measurable_comp_iff.1
    apply measurable_fun_sum
    · exact
        (((Measure.measurable_map Cemetery.alive measurable_inl).comp P.measurable_toMeasure).add
          ((measurable_const.sub (P.measurable_measure MeasurableSet.univ)).smul_measure
            (Measure.dirac Cemetery.delta)))
    · exact measurable_const
  kernel_zero := by rw [P.zero, Kernel.cemeteryExtension_id]
  kernel_add s t := by
    rw [P.add]
    exact Kernel.cemeteryExtension_comp (P t) (P s) (P.isSubMarkovKernel t)
      (P.isSubMarkovKernel s)
  isSubMarkovKernel t := by
    let : IsMarkovKernel (Kernel.cemeteryExtension (P t)) :=
      Kernel.isMarkovKernel_cemeteryExtension (P t) (P.isSubMarkovKernel t)
    exact IsSubMarkovKernel.of_isMarkovKernel _

variable (P : SubMarkovKernelSemigroup α)

@[simp]
theorem cemeterySemigroup_apply (t : NNReal) :
    cemeterySemigroup P t = Kernel.cemeteryExtension (P t) :=
  by rw [cemeterySemigroup]

/-- The cemetery extension semigroup is conservative. -/
theorem isConservative_cemeterySemigroup : (cemeterySemigroup P).IsConservative := by
  intro t z
  rw [cemeterySemigroup_apply]
  exact (Kernel.isMarkovKernel_cemeteryExtension (P t) (P.isSubMarkovKernel
      t)).isProbabilityMeasure z |>.measure_univ

/-- The cemetery state is absorbing at every time in the extension semigroup. -/
theorem cemeterySemigroup_absorbing (t : NNReal) :
    cemeterySemigroup P t Cemetery.delta = Measure.dirac Cemetery.delta :=
  by rw [cemeterySemigroup_apply]; exact Kernel.cemeteryExtension_absorbing (P t)

end SubMarkovKernelSemigroup

end MarkovProcess

end

end PortComputability
