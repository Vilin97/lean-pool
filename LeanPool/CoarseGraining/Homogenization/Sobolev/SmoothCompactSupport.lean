/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.BasicLemmas
public import Mathlib.Analysis.Distribution.TestFunction

/-!
# Smooth compactly supported test functions

This is a thin adapter over Mathlib's genuine test-function carrier
`𝓓^{⊤}(Ω, ℝ)`.  It records the concrete Euclidean-coordinate gradient used by
the project's weak Sobolev witnesses, without introducing a second test-space
structure or any regularity hypothesis on `Ω`.
-/

@[expose] public section

namespace Homogenization

open TopologicalSpace
open scoped Distributions

/-- Mathlib's smooth compactly supported real-valued test functions on `Ω`. -/
abbrev SmoothCompactSupportFunction {d : ℕ} (Ω : Opens (Vec d)) : Type _ :=
  𝓓^{⊤}(Ω, ℝ)

namespace SmoothCompactSupportFunction

/-- The explicit Euclidean-coordinate gradient of a smooth test function. -/
noncomputable def gradient {d : ℕ} {Ω : Opens (Vec d)}
    (φ : SmoothCompactSupportFunction Ω) : Vec d → Vec d :=
  fun x i => (fderiv ℝ φ x) (basisVec i)

/-- The literal global smoothness fact carried by Mathlib's test-function type. -/
theorem contDiff {d : ℕ} {Ω : Opens (Vec d)} (φ : SmoothCompactSupportFunction Ω) :
    ContDiff ℝ (⊤ : ℕ∞) (φ : Vec d → ℝ) :=
  TestFunction.contDiff φ

/-- The literal compact-support fact carried by Mathlib's test-function type. -/
theorem hasCompactSupport {d : ℕ} {Ω : Opens (Vec d)}
    (φ : SmoothCompactSupportFunction Ω) :
    HasCompactSupport (φ : Vec d → ℝ) :=
  TestFunction.hasCompactSupport φ

/-- The literal support-in-domain fact carried by Mathlib's test-function type. -/
theorem tsupport_subset {d : ℕ} {Ω : Opens (Vec d)}
    (φ : SmoothCompactSupportFunction Ω) :
    tsupport (φ : Vec d → ℝ) ⊆ (Ω : Set (Vec d)) :=
  TestFunction.tsupport_subset φ

/-- Regard a smooth compactly supported test function as a `W^{1,p}` function
on its open support domain. -/
noncomputable def toW1pFunction {d : ℕ} (Ω : Opens (Vec d)) (p : ENNReal)
    (φ : SmoothCompactSupportFunction Ω) : W1pFunction (Ω : Set (Vec d)) p :=
  W1pFunction.ofContDiff Ω.isOpen ((contDiff φ).of_le (by simp)) (hasCompactSupport φ) p

@[simp] theorem toW1pFunction_toFun {d : ℕ} (Ω : Opens (Vec d)) (p : ENNReal)
    (φ : SmoothCompactSupportFunction Ω) :
    (φ.toW1pFunction Ω p).toFun = (φ : Vec d → ℝ) :=
  rfl

@[simp] theorem toW1pFunction_grad {d : ℕ} (Ω : Opens (Vec d)) (p : ENNReal)
    (φ : SmoothCompactSupportFunction Ω) :
    (φ.toW1pFunction Ω p).grad = φ.gradient :=
  rfl

/-- Negating a test function negates its explicit gradient.  This is the sign
compatibility needed when symmetric test classes are used in dual suprema. -/
@[simp] theorem gradient_neg {d : ℕ} {Ω : Opens (Vec d)}
    (φ : SmoothCompactSupportFunction Ω) :
    (-φ).gradient = -φ.gradient := by
  ext x i
  change (fderiv ℝ (fun y => -φ y) x) (basisVec i) =
    -(fderiv ℝ (φ : Vec d → ℝ) x) (basisVec i)
  rw [fderiv_fun_neg, neg_apply]

end SmoothCompactSupportFunction

end Homogenization
