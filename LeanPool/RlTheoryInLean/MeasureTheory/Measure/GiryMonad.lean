/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.Bornology.Basic

/-!
# LeanPool.RlTheoryInLean.MeasureTheory.Measure.GiryMonad
-/

open MeasureTheory MeasureTheory.Measure  ProbabilityTheory Finset NNReal ENNReal Preorder Filter

namespace MeasureTheory.Measure

variable {α β γ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

lemma ae_join_of_ae_ae
  {m : Measure (Measure α)}
  {p : α → Prop} (hp : MeasurableSet {a | p a})
  (h : ∀ᵐ μ ∂m, ∀ᵐ a ∂μ, p a) :
  ∀ᵐ a ∂m.join, p a := by
  apply ae_iff.mpr
  rw [show {a | ¬p a} = {a | p a}ᶜ from rfl, join_apply hp.compl,
      ← lintegral_zero (μ := m)]
  exact lintegral_congr_ae (h.mono fun μ hμ => ae_iff.mp hμ)

lemma ae_bind_of_ae_ae
  {m : Measure α}
  {p : β → Prop} {hp : MeasurableSet {a | p a}}
  {f : α → Measure β}
  (hf : AEMeasurable f m)
  (h : ∀ᵐ a ∂m, ∀ᵐ b ∂f a, p b) :
  ∀ᵐ b ∂m.bind f, p b := by
  unfold Measure.bind
  apply ae_join_of_ae_ae hp
  have hmeas : MeasurableSet {ν : Measure β | ∀ᵐ b ∂ν, p b} := by
    rw [show {ν : Measure β | ∀ᵐ b ∂ν, p b} =
          (fun ν : Measure β => ν {a | ¬ p a}) ⁻¹' {0} from by
      ext ν; simp [ae_iff]]
    exact (Measure.measurable_measure.mp measurable_id _ hp.compl) (measurableSet_singleton 0)
  exact (ae_map_iff hf hmeas).mpr h


end MeasureTheory.Measure
