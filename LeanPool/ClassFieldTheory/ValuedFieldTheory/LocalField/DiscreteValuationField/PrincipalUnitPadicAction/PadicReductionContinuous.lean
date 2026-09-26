/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
/-!
# Continuity of reduction of p-adic integers

Reduction modulo `p^n` has open kernel and is continuous for the discrete
topology on the quotient. This source has no local-field dependencies.
-/

@[expose] public section

namespace LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

/-- The kernel of reduction `Z_p -> ZMod (p^n)` is open. -/
theorem isOpen_ker_padicIntToZModPow
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsOpen
      ((RingHom.ker (PadicInt.toZModPow n : ℤ_[p] →+* ZMod (p ^ n)) :
        Ideal ℤ_[p]) : Set ℤ_[p]) := by
  rw [PadicInt.ker_toZModPow]
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hr : (p : ℝ) ^ (-n : ℤ) ≠ 0 := zpow_ne_zero (-n : ℤ) hp0
  have hball :
      IsOpen (Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-n : ℤ))) :=
    IsUltrametricDist.isOpen_closedBall (0 : ℤ_[p]) hr
  have heq :
      ((Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]) : Set ℤ_[p]) =
        Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-n : ℤ)) := by
    ext x
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (PadicInt.norm_le_pow_iff_mem_span_pow x n).symm
  rw [heq]
  exact hball

/-- Reduction of p-adic integers modulo `p^n` is continuous for the
discrete topology on the target. -/
theorem Internal.continuous_padicIntToZModPow
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    @Continuous ℤ_[p] (ZMod (p ^ n))
      (inferInstance : TopologicalSpace ℤ_[p]) ⊥
      (PadicInt.toZModPow n : ℤ_[p] → ZMod (p ^ n)) := by
  let : TopologicalSpace (ZMod (p ^ n)) := ⊥
  let : DiscreteTopology (ZMod (p ^ n)) := ⟨rfl⟩
  apply continuous_of_continuousAt_zero
    (PadicInt.toZModPow n : ℤ_[p] →+* ZMod (p ^ n))
  rw [ContinuousAt, nhds_discrete (ZMod (p ^ n)), map_zero, Filter.tendsto_pure]
  exact (isOpen_ker_padicIntToZModPow p n).mem_nhds
    (RingHom.ker (PadicInt.toZModPow n)).zero_mem

end LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
