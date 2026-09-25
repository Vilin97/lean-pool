/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.Algebra.Membership

/-! # Localized Zero Trace -/

@[expose] public section

namespace Homogenization

noncomputable section

/-- Localized scalar zero-trace condition.

This is the Sobolev/a.e. replacement for saying that a scalar function vanishes
on the part of `∂Ω` seen through the localization window `V`: every smooth
compactly supported cutoff localized in `V` turns the function into an
admissible `H¹₀(Ω)` test function. -/
def LocalizedZeroTraceFunctionOn {d : ℕ} (Ω V : Set (Vec d))
    (u : Vec d → ℝ) : Prop :=
  ∀ η : Vec d → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) η →
    HasCompactSupport η →
    tsupport η ⊆ V →
      MemH10 Ω (fun y => η y * u y)

/-- The localized scalar zero-trace condition gives exactly the admissible
cutoff product encoded in its definition. -/
theorem localizedZeroTraceFunctionOn_memH10_mul {d : ℕ}
    {Ω V : Set (Vec d)} {u η : Vec d → ℝ}
    (hu : LocalizedZeroTraceFunctionOn Ω V u)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η)
    (hη_sub : tsupport η ⊆ V) :
    MemH10 Ω (fun y => η y * u y) :=
  hu η hη hη_compact hη_sub

/-- A genuine `H¹₀(Ω)` function has localized zero trace in every window
contained in `Ω`. -/
theorem localizedZeroTraceFunctionOn_of_h10 {d : ℕ} {Ω V : Set (Vec d)}
    (hΩ : IsOpen Ω) (hV : V ⊆ Ω) (u : H10Function Ω) :
    LocalizedZeroTraceFunctionOn Ω V u.toH1Function.toFun := by
  intro η hη hη_compact hη_sub
  exact
    (u.mulSmoothCutoff hΩ hη hη_compact (hη_sub.trans hV)).memH10

/-- A genuine `H¹₀(Ω)` function has localized zero trace in any localization
window.  The cutoff need not be supported in `Ω`: the compactly supported
approximants of the `H¹₀` function are already supported in `Ω`. -/
theorem localizedZeroTraceFunctionOn_of_h10_any {d : ℕ} {Ω V : Set (Vec d)}
    (u : H10Function Ω) :
    LocalizedZeroTraceFunctionOn Ω V u.toH1Function.toFun := by
  intro η hη hη_compact _hη_sub
  exact (u.mulContDiffHasCompactSupport hη hη_compact).memH10

/-- Localized zero trace is closed under addition. -/
theorem localizedZeroTraceFunctionOn_add {d : ℕ}
    {Ω V : Set (Vec d)} {u v : Vec d → ℝ}
    (hu : LocalizedZeroTraceFunctionOn Ω V u)
    (hv : LocalizedZeroTraceFunctionOn Ω V v) :
    LocalizedZeroTraceFunctionOn Ω V (fun y => u y + v y) := by
  intro η hη hη_compact hη_sub
  have huη : MemH10 Ω (fun y => η y * u y) :=
    hu η hη hη_compact hη_sub
  have hvη : MemH10 Ω (fun y => η y * v y) :=
    hv η hη hη_compact hη_sub
  simpa [mul_add] using memH10_add huη hvη

/-- Localized zero trace is closed under negation. -/
theorem localizedZeroTraceFunctionOn_neg {d : ℕ}
    {Ω V : Set (Vec d)} {u : Vec d → ℝ}
    (hu : LocalizedZeroTraceFunctionOn Ω V u) :
    LocalizedZeroTraceFunctionOn Ω V (fun y => -u y) := by
  intro η hη hη_compact hη_sub
  have huη : MemH10 Ω (fun y => η y * u y) :=
    hu η hη hη_compact hη_sub
  simpa [mul_neg] using memH10_neg huη

/-- Localized zero trace is closed under subtraction. -/
theorem localizedZeroTraceFunctionOn_sub {d : ℕ}
    {Ω V : Set (Vec d)} {u v : Vec d → ℝ}
    (hu : LocalizedZeroTraceFunctionOn Ω V u)
    (hv : LocalizedZeroTraceFunctionOn Ω V v) :
    LocalizedZeroTraceFunctionOn Ω V (fun y => u y - v y) := by
  intro η hη hη_compact hη_sub
  have huη : MemH10 Ω (fun y => η y * u y) :=
    hu η hη hη_compact hη_sub
  have hvη : MemH10 Ω (fun y => η y * v y) :=
    hv η hη hη_compact hη_sub
  simpa [mul_sub] using memH10_sub huη hvη

end

end Homogenization
