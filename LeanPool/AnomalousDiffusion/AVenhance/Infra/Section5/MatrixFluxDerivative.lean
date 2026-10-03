/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MatrixFluxProduct

/-! A local Fréchet derivative rule for a matrix-vector flux. -/

@[expose] public section

namespace AVenhance.Infra.Section5

open AVenhance Homogenization

/-- Entrywise matrix derivatives and a vector derivative give the Fréchet
derivative of their pointwise matrix-vector product. -/
theorem hasFDerivAt_matrix_mulVec
    {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {V : Vec 2 → Vec 2}
    {x : Vec 2} {LA : Fin 2 → Fin 2 → Vec 2 →L[ℝ] ℝ}
    {LV : Vec 2 →L[ℝ] Vec 2}
    (hA : ∀ i j, HasFDerivAt (fun y => A y i j) (LA i j) x)
    (hV : HasFDerivAt V LV x) :
    HasFDerivAt (fun y => (A y).mulVec (V y))
      (ContinuousLinearMap.pi fun i : Fin 2 =>
        ∑ j : Fin 2,
          ((V x j) • LA i j +
            (A x i j) • ((ContinuousLinearMap.proj j).comp LV))) x := by
  let D : Fin 2 → Vec 2 →L[ℝ] ℝ := fun i =>
    ∑ j : Fin 2,
      ((V x j) • LA i j +
        (A x i j) • ((ContinuousLinearMap.proj j).comp LV))
  have hrow (i : Fin 2) : HasFDerivAt
      (fun y => (A y).mulVec (V y) i) (D i) x := by
    have hfun : (fun y => (A y).mulVec (V y) i) =
        ∑ j : Fin 2, (fun y => A y i j * V y j) := by
      funext y
      simp [Matrix.mulVec, dotProduct]
    rw [hfun]
    apply HasFDerivAt.sum
    intro j hj
    have hVj : HasFDerivAt (fun y => V y j)
        ((ContinuousLinearMap.proj j).comp LV) x := by
      exact (ContinuousLinearMap.proj j).hasFDerivAt.comp x hV
    convert (hA i j).mul hVj using 1
    exact add_comm _ _
  apply hasFDerivAt_pi.2
  intro i
  simpa [D] using hrow i

end AVenhance.Infra.Section5
