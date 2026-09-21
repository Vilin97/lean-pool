/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Lifetime.Law

/-!
# Detecting nonexplosion from countably many coordinates

For a lifetime path, infinite lifetime is equivalent to being alive at every natural-number
time. Consequently, nonexplosion of a lifetime-path kernel can be proved from countably many
almost-sure coordinate statements. This is the measure-theoretic reduction later used to turn
conservativity of transition laws into nonexplosion.
-/

noncomputable section PortComputability

open MeasureTheory
open scoped ENNReal NNReal

namespace MarkovProcess

section

namespace LifetimePath

variable {alpha : Type*} [TopologicalSpace alpha]

/-- A lifetime path has infinite lifetime exactly when it is alive at every natural-number
time. -/
theorem lifetime_eq_top_iff_coordinate_nat_ne_delta (omega : LifetimePath alpha) :
    omega.lifetime = ∞ ↔
      ∀ n : ℕ, coordinate (n : NNReal) omega ≠ Cemetery.delta := by
  constructor
  · intro hlifetime n
    rw [coordinate_ne_delta_iff, hlifetime]
    exact ENNReal.coe_lt_top
  · intro hcoordinate
    by_contra hlifetime
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hlifetime
    exact hcoordinate n (coordinate_of_le omega (n : NNReal) hn.le)

end LifetimePath

namespace Kernel

variable {beta alpha : Type*} [MeasurableSpace beta] [TopologicalSpace alpha]
  [MeasurableSpace alpha]

/-- Nonexplosion is equivalent to almost-sure liveness at every natural-number time, separately
for every starting point. -/
theorem isNonexplosive_iff_coordinate_nat_ne_delta
    (kappa : ProbabilityTheory.Kernel beta (LifetimePath alpha)) :
    IsNonexplosive kappa ↔
      ∀ n : ℕ, ∀ x, ∀ᵐ omega ∂kappa x,
        LifetimePath.coordinate (n : NNReal) omega ≠ Cemetery.delta := by
  constructor
  · intro hnonexplosive n x
    exact (hnonexplosive x).mono fun omega hlifetime ↦
      (LifetimePath.lifetime_eq_top_iff_coordinate_nat_ne_delta omega).mp hlifetime n
  · intro hcoordinate x
    filter_upwards [ae_all_iff.2 fun n ↦ hcoordinate n x] with omega homega
    exact (LifetimePath.lifetime_eq_top_iff_coordinate_nat_ne_delta omega).mpr homega

/-- Equivalently, nonexplosion is the vanishing of the cemetery mass in every
natural-number-time coordinate marginal. -/
theorem isNonexplosive_iff_map_coordinate_nat_delta
    (kappa : ProbabilityTheory.Kernel beta (LifetimePath alpha)) :
    IsNonexplosive kappa ↔
      ∀ n : ℕ, ∀ x,
        kappa.map (LifetimePath.coordinate (n : NNReal)) x {Cemetery.delta} = 0 := by
  have hdelta : MeasurableSet ({Cemetery.delta} : Set (Cemetery alpha)) := by
    simpa only [Set.range_unique] using
      (measurableSet_range_inr :
        MeasurableSet (Set.range (Sum.inr : Unit → alpha ⊕ Unit)))
  constructor
  · intro hnonexplosive n x
    rw [ProbabilityTheory.Kernel.map_apply' _
      (LifetimePath.measurable_coordinate (n : NNReal)) x hdelta]
    apply measure_eq_zero_iff_ae_notMem.mpr
    exact (hnonexplosive x).mono fun omega hlifetime homega ↦
      ((LifetimePath.lifetime_eq_top_iff_coordinate_nat_ne_delta omega).mp hlifetime n)
        (by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using homega)
  · rw [isNonexplosive_iff_coordinate_nat_ne_delta]
    intro hdeltaMass n x
    apply measure_eq_zero_iff_ae_notMem.mp
    change kappa x
      (LifetimePath.coordinate (n : NNReal) ⁻¹' {Cemetery.delta}) = 0
    rw [← ProbabilityTheory.Kernel.map_apply' _
      (LifetimePath.measurable_coordinate (n : NNReal)) x hdelta]
    exact hdeltaMass n x

end Kernel
end
end MarkovProcess

end PortComputability
