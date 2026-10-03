/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.RestrictionObservable
public import LeanPool.CoarseGraining.Homogenization.Probability.RegCoeffField.RestrictionBridge

/-! # Mu Locality Gate -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch04

open MeasureTheory

/-!
# The `LocalSigmaR` → `IsRestrictionLocalRandomVariable` gate (Packet P4b, P5 input)

This file exposes the σ-algebra bridge `localSigmaR_le_restrictionSigmaR` at the
Chapter 4 observable interface: a carrier observable that is measurable for the
local entry-test σ-algebra `LocalSigmaR U` is a genuine restriction-local random
variable `IsRestrictionLocalRandomVariable U hU`.

This is the P5 gate for carrier `Mu` locality.  The plan's route for the coarse
observable `Mu` is:

1. re-aim the raw `Mu`/`toHilbertMatrixL2` measurability machinery
   (`measurable_toHilbertMatrixL2_of_dense_inner` and the dense-probe inner
   products, which are set integrals `∫_U w · a(·)_{ij}` — the entry-test
   generators, via `entryTestR_eq_setIntegral_of_support`) so that
   `a ↦ Mu (cubeSet Q) P0 a.toFun` is `LocalSigmaR (cubeSet Q)`-measurable;
2. apply `IsRestrictionLocalRandomVariable.of_measurable_localSigmaR` (below) to conclude
   `IsRestrictionLocalRandomVariable (cubeSet Q) hQ (fun a => Mu (cubeSet Q) P0 a.toFun)`.

Step 2 is provided here, law-independently.  Step 1 (the carrier re-aim of the raw
subtype/slice `L²` machinery) is the remaining P5 work; the honest, genuinely
measurable slice sets it needs are now available
(`Homogenization.measurableSet_localSigmaR_aeeSlice`).

Reference: the paper (Armstrong–Kuusi–Loher, to appear).
-/

namespace IsRestrictionLocalRandomVariable

/-- **The `LocalSigmaR` → restriction-local gate.**  A carrier observable
measurable for the local entry-test σ-algebra `LocalSigmaR U` is a restriction-local
random variable on the measurable observation set `U`. -/
theorem of_measurable_localSigmaR {β : Type*} [MeasurableSpace β] {d : ℕ}
    {U : Set (Vec d)} (hU : MeasurableSet U) {X : RegCoeffField d → β}
    (hX : @Measurable (RegCoeffField d) β (LocalSigmaR U) _ X) :
    IsRestrictionLocalRandomVariable U hU X :=
  Homogenization.measurable_restrictionSigmaR_of_measurable_localSigmaR hU hX

end IsRestrictionLocalRandomVariable

end Ch04
end Book
end Homogenization
