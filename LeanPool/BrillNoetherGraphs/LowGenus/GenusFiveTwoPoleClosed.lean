/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveTwoPole
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveConfigurations
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DiscreteSpecialization

/-!
# Six closed genus-five constructions from the common positive proof

The same canonical core weights are used on every face. Finite discrete
specialization transports their rank from positive subdivisions to the
contracted graph. No row-specific boundary construction is imported here.
-/

namespace AtanasovRanganathan.GenusFiveTwoPoleClosed

open Utilities Utilities.Certificate
open ExplicitPotential SubdivisionGraph DegenerateSpec
open ContractionForestCensusGeneral
open Utilities.Subdivision.SubdivisionCoreSupport
open Configurations GenusFiveCoreAtlas GenusFiveTwoPoleData GenusFiveTwoPole

/-- A fixed nonnegative degree-four weight with positive-subdivision rank
one gives a closed-orthant construction by discrete specialization. -/
theorem closedConstruction_of_fixed_positive_rank
    {n p : ℕ} (core : ExplicitPotential.Core n p)
    (hNonempty : 0 < n) (hConnected : core.Connected)
    (hLoopless : ∀ e, core.tail e ≠ core.head e)
    (weight : Fin n → ℤ) (hWeight : ∀ v, 0 ≤ weight v)
    (hDegree : ∑ v : Fin n, weight v = 4)
    (hPositive : ∀ s : Spec n p, s.core = core →
      rank s.graph (coreDivisor s weight) ≥ 1) :
    ClosedSubdivisionDharConstruction core hNonempty := by
  intro length forest not_loopy
  let d := faceSpec core hNonempty length forest not_loopy
  refine ⟨DegreeFourDharPencil.ofEffectiveRankOne (d.coreClassDivisor weight)
    (d.coreClassDivisor_effective weight hWeight) ?_ ?_⟩
  · simpa only [d.deg_coreClassDivisor] using hDegree
  · apply DiscreteSpecialization.rank_ge_one_coreClassDivisor_of_positive d
      hConnected hLoopless _ weight hWeight hPositive
    intro u v huv
    exact (compFold_iff core (zeroSlots length) u v).mp huv

/-- Row 01 on its entire genus-preserving closed length orthant. -/
theorem row01_closedConstruction :
    ClosedSubdivisionDharConstruction row01Core (by norm_num) :=
  closedConstruction_of_fixed_positive_rank row01Core (by norm_num)
    row01_connected row01_loopless row01Weight row01_weight_nonneg
    row01_weight_sum row01_rank_positive

/-- Row 02 on its entire genus-preserving closed length orthant. -/
theorem row02_closedConstruction :
    ClosedSubdivisionDharConstruction row02Core (by norm_num) :=
  closedConstruction_of_fixed_positive_rank row02Core (by norm_num)
    row02_connected row02_loopless row02Weight row02_weight_nonneg
    row02_weight_sum row02_rank_positive

/-- Row 03 on its entire genus-preserving closed length orthant. -/
theorem row03_closedConstruction :
    ClosedSubdivisionDharConstruction row03Core (by norm_num) :=
  closedConstruction_of_fixed_positive_rank row03Core (by norm_num)
    row03_connected row03_loopless row03Weight row03_weight_nonneg
    row03_weight_sum row03_rank_positive

/-- Row 04 on its entire genus-preserving closed length orthant. -/
theorem row04_closedConstruction :
    ClosedSubdivisionDharConstruction row04Core (by norm_num) :=
  closedConstruction_of_fixed_positive_rank row04Core (by norm_num)
    row04_connected row04_loopless row04Weight row04_weight_nonneg
    row04_weight_sum row04_rank_positive

/-- Row 07 on its entire genus-preserving closed length orthant. -/
theorem row07_closedConstruction :
    ClosedSubdivisionDharConstruction row07Core (by norm_num) :=
  closedConstruction_of_fixed_positive_rank row07Core (by norm_num)
    row07_connected row07_loopless row07Weight row07_weight_nonneg
    row07_weight_sum row07_rank_positive

/-- Row 13 on its entire genus-preserving closed length orthant. -/
theorem row13_closedConstruction :
    ClosedSubdivisionDharConstruction row13Core (by norm_num) :=
  closedConstruction_of_fixed_positive_rank row13Core (by norm_num)
    row13_connected row13_loopless row13Weight row13_weight_nonneg
    row13_weight_sum row13_rank_positive

end AtanasovRanganathan.GenusFiveTwoPoleClosed
