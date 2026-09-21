/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceObservable
import LeanPool.CoarseGraining.Homogenization.Probability.RandomField

/-!
# Source-local coefficient observables

This module provides the exact coarse-source local version of the smooth
coefficient-field test, independently of the regular-carrier observable lane.
-/

namespace Homogenization.Book.Ch04

open MeasureTheory

noncomputable section

/-- The smooth coefficient-field test is directly measurable for the exact
coarse-source local integral sigma algebra. -/
theorem source_isLocalObservable_localTestObservable {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) (e e' : Vec d) {φ : Vec d → ℝ}
    (hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_support : tsupport φ ⊆ U) :
    Source.Coarse.IsLocalObservable U hU
      (fun a : Source.Coarse.Carrier d => localTestObservable e e' φ a.1) := by
  change @Measurable (Source.Coarse.Carrier d) ℝ (Source.Coarse.localSigma U hU) _
    (fun a : Source.Coarse.Carrier d => localTestObservable e e' φ a.1)
  have htest :
      (fun a : Source.Coarse.Carrier d => localTestObservable e e' φ a.1) =
        Source.Coarse.bilinearTest e e' φ := by
    rfl
  rw [htest]
  intro t ht
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨e, e', φ, ⟨hφ_cont, hφ_compact⟩, hφ_support, t, ht, rfl⟩

namespace SourceObservable

/-- The smooth coefficient-field test observable, bundled for the exact coarse
source carrier.  Its locality is the direct source-local test generator theorem. -/
noncomputable def localTest {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U)
    (e e' : Vec d) {φ : Vec d → ℝ}
    (hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_support : tsupport φ ⊆ U) :
    SourceObservable d U ℝ where
  measurableSet := hU
  toFun := fun a => localTestObservable e e' φ a.1
  isLocal :=
    source_isLocalObservable_localTestObservable hU e e' hφ_cont hφ_compact hφ_support

@[simp]
theorem localTest_apply {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U)
    (e e' : Vec d) {φ : Vec d → ℝ}
    (hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_support : tsupport φ ⊆ U) (a : Source.Coarse.Carrier d) :
    localTest hU e e' hφ_cont hφ_compact hφ_support a =
      localTestObservable e e' φ a.1 :=
  rfl

end SourceObservable

end

end Homogenization.Book.Ch04
