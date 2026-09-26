/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basis
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# Coord Deriv

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

noncomputable section

namespace CKN

/-- The `i`th coordinate component of the Fréchet derivative of `f` at `x` equals the
ordinary derivative, at `x i`, of the one-variable function obtained from `f` by varying
the `i`th coordinate alone: `s ↦ f (Function.update x i s)`. -/
theorem coordFDeriv_eq_deriv_update {d : ℕ} {f : Vec d → ℝ} {x : Vec d}
    (hf : DifferentiableAt ℝ f x) (i : Fin d) :
    (fderiv ℝ f x) (basisVec i) =
      deriv (fun s : ℝ => f (Function.update x i s)) (x i) := by
  have hcomp := HasFDerivAt.comp (x i)
    (by simpa only [Function.update_eq_self] using hf.hasFDerivAt)
    (hasFDerivAt_update (𝕜 := ℝ) (i := i) x (x i))
  have hderiv : HasDerivAt (fun s : ℝ => f (Function.update x i s))
      ((fderiv ℝ f x ∘SL ContinuousLinearMap.pi
        (Pi.single i (ContinuousLinearMap.id ℝ ℝ))) 1) (x i) := by
    have := (hasFDerivAt_iff_hasDerivAt (f' := fderiv ℝ f x ∘SL
      ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ)))).mp hcomp
    simpa [Function.comp_def] using this
  rw [hderiv.deriv]
  have hb : ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ)) 1 =
      basisVec i := by
    ext j
    by_cases hji : j = i <;> simp [basisVec, hji]
  rw [show (fderiv ℝ f x ∘SL
      ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ))) 1 =
      (fderiv ℝ f x) (ContinuousLinearMap.pi
        (Pi.single i (ContinuousLinearMap.id ℝ ℝ)) 1) by rfl, hb]

end CKN
