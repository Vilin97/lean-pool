/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.HighContrast.Coupled.LocalEnergy.Cutoff
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.MeanZero

/-!
# Local block energy: the centered potentials and the test pair

The centered potentials `u = v − ½p·x − c`, `u* = v* − ½p·x + c` as
`H¹` functions (with constant gradients `V = ∇v − ½p`, `V* = ∇v* − ½p`), and
the smooth test pair `(η²u, η²u*)` built from the library's smooth×`H¹` product
`H1Function.mulContDiffMemLpTop`.  The admissibility
`MemH10 (η²u + η²u*)` is obtained from `η²·(v+v*−p·x) ∈ H¹₀` via
`H10Function.mulContDiffMemLpTop`.
-/

namespace Homogenization

open Homogenization
open MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d] {m : ℤ}

/-- Abbreviation for the centered open cube. -/
local notation "U" => openCubeSet (originCube d m)

/-! ## The centered potentials -/

/-- `u = v − ½ p·x − c` as an `H¹` function. -/
def centeredPotential (m : ℤ) (v : H1Function (openCubeSet (originCube d m)))
    (p : Vec d) (c : ℝ) : H1Function (openCubeSet (originCube d m)) :=
  letI := isFiniteMeasure_openCubeSet_originCube (d := d) m
  v + (-(1 / 2 : ℝ)) • affineH1 m p + H1Function.const (-c)

omit [NeZero d] in
/-- Evaluation formula for the centered potential. -/
@[simp] theorem centeredPotential_toFun (v : H1Function (openCubeSet (originCube d m)))
    (p : Vec d) (c : ℝ) (x : Vec d) :
    (centeredPotential m v p c).toFun x = v.toFun x - (1 / 2 : ℝ) * vecDot p x - c := by
  let := isFiniteMeasure_openCubeSet_originCube (d := d) m
  show (v + (-(1 / 2 : ℝ)) • affineH1 m p + H1Function.const (-c)).toFun x = _
  simp only [Homogenization.H1Function.add_toFun, Homogenization.H1Function.smul_toFun,
    affineH1_toFun, H1Function.const_apply]
  ring

omit [NeZero d] in
/-- Gradient formula for the centered potential. -/
@[simp] theorem centeredPotential_grad (v : H1Function (openCubeSet (originCube d m)))
    (p : Vec d) (c : ℝ) (x : Vec d) :
    (centeredPotential m v p c).grad x = v.grad x - (1 / 2 : ℝ) • p := by
  let := isFiniteMeasure_openCubeSet_originCube (d := d) m
  show (v + (-(1 / 2 : ℝ)) • affineH1 m p + H1Function.const (-c)).grad x = _
  simp only [Homogenization.H1Function.add_grad, Homogenization.H1Function.smul_grad,
    affineH1_grad, H1Function.grad_const, add_zero]
  module

omit [NeZero d] in
/-- The sum of the two centered potentials is `v + v* − p·x`. -/
theorem centeredPotential_add_toFun (v vstar : H1Function (openCubeSet (originCube d m)))
    (p : Vec d) (c : ℝ) (x : Vec d) :
    (centeredPotential m v p c).toFun x + (centeredPotential m vstar p (-c)).toFun x =
      v.toFun x + vstar.toFun x - vecDot p x := by
  rw [centeredPotential_toFun, centeredPotential_toFun]
  ring

/-! ## `L^∞` data for `η²` -/

variable {η : Vec d → ℝ}

omit [NeZero d] in
/-- Packaged `L^∞` data for `η²` on the finite-measure cube. -/
theorem sqCutoff_memLpTop (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hIcc : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1) :
    MemLp (sqCutoff η) (⊤ : ENNReal) (volume.restrict (openCubeSet (originCube d m))) :=
  memLpTop_sqCutoff hη hIcc

omit [NeZero d] in
/-- Packaged `L∞` data for a partial derivative of `η²`. -/
theorem sqCutoff_fderiv_memLpTop (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hIcc : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1) {Gη : ℝ}
    (hGη : ∀ x i, |fderiv ℝ η x (basisVec i)| ≤ Gη) (i : Fin d) :
    MemLp (fun x => (fderiv ℝ (sqCutoff η) x) (basisVec i)) (⊤ : ENNReal)
      (volume.restrict (openCubeSet (originCube d m))) :=
  memLpTop_fderiv_sqCutoff hη hIcc hGη i

/-! ## The test function `η²·u` -/

/-- `η² · u` as an `H¹` function via the library's smooth×`H¹` product. -/
def testFun (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hIcc : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    {Gη : ℝ} (hGη : ∀ x i, |fderiv ℝ η x (basisVec i)| ≤ Gη)
    (u : H1Function (openCubeSet (originCube d m))) :
    H1Function (openCubeSet (originCube d m)) :=
  u.mulContDiffMemLpTop (sqCutoff_contDiff hη) (sqCutoff_memLpTop (m := m) hη hIcc)
    (fun i => sqCutoff_fderiv_memLpTop (m := m) hη hIcc hGη i)

omit [NeZero d] in
/-- Evaluation formula for the cutoff test function. -/
@[simp] theorem testFun_toFun (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hIcc : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1) {Gη : ℝ}
    (hGη : ∀ x i, |fderiv ℝ η x (basisVec i)| ≤ Gη)
    (u : H1Function (openCubeSet (originCube d m))) (x : Vec d) :
    (testFun hη hIcc hGη u).toFun x = sqCutoff η x * u.toFun x := by
  rw [testFun, Homogenization.H1Function.mulContDiffMemLpTop_toFun]

omit [NeZero d] in
/-- Gradient formula for the cutoff test function. -/
@[simp] theorem testFun_grad (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hIcc : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1) {Gη : ℝ}
    (hGη : ∀ x i, |fderiv ℝ η x (basisVec i)| ≤ Gη)
    (u : H1Function (openCubeSet (originCube d m))) (x : Vec d) (i : Fin d) :
    (testFun hη hIcc hGη u).grad x i =
      sqCutoff η x * u.grad x i + u.toFun x * (fderiv ℝ (sqCutoff η) x) (basisVec i) := by
  rw [testFun, Homogenization.H1Function.mulContDiffMemLpTop_grad]

/-! ## Admissibility of the test pair -/

omit [NeZero d] in
/-- `MemH10 (η² u + η² u*)`, from `η² · (u + u*) ∈ H¹₀` and the library's
`H10Function` smooth product.  The input `hTrace` is the trace fact
`v + v* − p·x ∈ H¹₀(U)`. -/
theorem memH10_testPair_sum (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hIcc : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1) {Gη : ℝ}
    (hGη : ∀ x i, |fderiv ℝ η x (basisVec i)| ≤ Gη)
    {v vstar : H1Function (openCubeSet (originCube d m))} {p : Vec d} {c : ℝ}
    (hTrace : MemH10 (openCubeSet (originCube d m))
      (fun x => v.toFun x + vstar.toFun x - vecDot p x)) :
    MemH10 (openCubeSet (originCube d m))
      (fun x => (testFun hη hIcc hGη (centeredPotential m v p c)).toFun x
        + (testFun hη hIcc hGη (centeredPotential m vstar p (-c))).toFun x) := by
  obtain ⟨w0, hw0⟩ := hTrace
  refine ⟨w0.mulContDiffMemLpTop (sqCutoff_contDiff hη) (sqCutoff_memLpTop (m := m) hη hIcc)
    (fun i => sqCutoff_fderiv_memLpTop (m := m) hη hIcc hGη i), ?_⟩
  funext x
  rw [Homogenization.H10Function.mulContDiffMemLpTop_toFun]
  show sqCutoff η x * w0.toH1Function.toFun x = _
  rw [hw0]
  simp only [testFun_toFun, centeredPotential_toFun]
  ring

end

end Homogenization
