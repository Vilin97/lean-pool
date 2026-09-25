/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Measure.RestrictedVolume
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Topology.Algebra.Support

/-!
# Compact Multiplier

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set


namespace CKN

/-- If `f` is locally integrable on an open set `U` and `q` is continuous with compact support
whose topological support is contained in `U`, then the product `f * q` is integrable on `U`. -/
theorem integrableOn_mul_continuous_of_tsupport_subset
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {f q : Vec d → ℝ} (hf : LocallyIntegrableOn f U volume)
    (hq : Continuous q) (hqCompact : HasCompactSupport q)
    (hqU : tsupport q ⊆ U) : IntegrableOn (fun x => f x * q x) U volume := by
  have hfK : IntegrableOn f (tsupport q) volume :=
    hf.integrableOn_compact_subset hqU hqCompact.isCompact
  have hprodK : IntegrableOn (fun x => f x * q x) (tsupport q) volume :=
    hfK.mul_continuousOn hq.continuousOn hqCompact.isCompact
  have hzero : ∀ x ∈ U \ tsupport q, f x * q x = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx.2, mul_zero]
  simpa only [IntegrableOn, volumeOn] using
    hprodK.of_forall_sdiff_eq_zero hU.measurableSet hzero

end CKN
