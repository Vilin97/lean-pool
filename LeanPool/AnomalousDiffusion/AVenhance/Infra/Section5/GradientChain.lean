/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms

/-! Coordinate chain rule for the flow-pulled gradient used in Section 5.1. -/

@[expose] public section

open Homogenization

namespace AVenhance.Infra.Section5

/-- The gradient of a scalar composition is the flow Jacobian times the
gradient of the outer function, in the row-Jacobian convention of `gradMatrix`.
-/
theorem spaceGrad_comp_eq_gradMatrix_mul
    {f : Vec 2 → ℝ} {X : Vec 2 → Vec 2} {x : Vec 2}
    {Lf : Vec 2 →L[ℝ] ℝ} {LX : Vec 2 →L[ℝ] Vec 2}
    (hf : HasFDerivAt f Lf (X x)) (hX : HasFDerivAt X LX x) (i : Fin 2) :
    spaceGrad (fun y => f (X y)) x i =
      ∑ j : Fin 2, gradMatrix X x i j * spaceGrad f (X x) j := by
  have hcomp : HasFDerivAt (fun y => f (X y)) (Lf.comp LX) x := by
    simpa [Function.comp_def] using hf.comp x hX
  have hcoord (j : Fin 2) :
      gradMatrix X x i j = (LX (basisVec i)) j := by
    rw [gradMatrix, Matrix.of_apply]
    change fderiv ℝ (fun y => X y j) x (basisVec i) = _
    rw [fderiv_apply hX.differentiableAt j, hX.fderiv]
    rfl
  have hdecomp :
      LX (basisVec i) =
        ∑ j : Fin 2, (LX (basisVec i) j) • basisVec j := by
    funext j
    fin_cases j <;> simp [Homogenization.basisVec, Fin.sum_univ_two]
  calc
    spaceGrad (fun y => f (X y)) x i = (Lf.comp LX) (basisVec i) := by
      change fderiv ℝ (fun y => f (X y)) x (basisVec i) = _
      rw [hcomp.fderiv]
    _ = Lf (LX (basisVec i)) := rfl
    _ = ∑ j : Fin 2, (LX (basisVec i) j) * Lf (basisVec j) := by
      rw [hdecomp]
      simp [map_smul, smul_eq_mul]
    _ = ∑ j : Fin 2, gradMatrix X x i j * spaceGrad f (X x) j := by
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [hcoord j]
      simp [spaceGrad, hf.fderiv]

/-- Product rule for the gradient of the corrector pairing `χ · G`. -/
theorem spaceGrad_vecDot
    {χ G : Vec 2 → Vec 2} {x : Vec 2}
    {Lχ LG : Vec 2 →L[ℝ] Vec 2}
    (hχ : HasFDerivAt χ Lχ x) (hG : HasFDerivAt G LG x)
    (i : Fin 2) :
    spaceGrad (fun y => vecDot (χ y) (G y)) x i =
      (gradMatrix χ x).mulVec (G x) i +
        ∑ j : Fin 2, χ x j * spaceGrad (fun y => G y j) x i := by
  have hχj (j : Fin 2) : HasFDerivAt (fun y => χ y j)
      ((ContinuousLinearMap.proj j).comp Lχ) x := by
    exact (ContinuousLinearMap.proj j).hasFDerivAt.comp x hχ
  have hGj (j : Fin 2) : HasFDerivAt (fun y => G y j)
      ((ContinuousLinearMap.proj j).comp LG) x := by
    exact (ContinuousLinearMap.proj j).hasFDerivAt.comp x hG
  let D : Fin 2 → Vec 2 →L[ℝ] ℝ := fun j =>
    χ x j • ((ContinuousLinearMap.proj j).comp LG) +
      G x j • ((ContinuousLinearMap.proj j).comp Lχ)
  have hsum : HasFDerivAt (fun y => vecDot (χ y) (G y))
      (D 0 + D 1) x := by
    have h := ((hχj 0).mul (hGj 0)).add ((hχj 1).mul (hGj 1))
    convert h using 1
    · funext y
      simp [vecDot, Fin.sum_univ_two]
  rw [spaceGrad, hsum.fderiv]
  simp [D, gradMatrix, Matrix.mulVec, Fin.sum_univ_two, spaceGrad,
    (hχj 0).fderiv, (hχj 1).fderiv, (hGj 0).fderiv, (hGj 1).fderiv,
    mul_comm]
  ring_nf

/-- The Fréchet derivative of the scalar pairing `χ · G`, expressed using
the component projections of the two vector derivatives. -/
def vecDotDerivativeAt
    {χ G : Vec 2 → Vec 2} (x : Vec 2)
    (Lχ LG : Vec 2 →L[ℝ] Vec 2) : Vec 2 →L[ℝ] ℝ :=
  (χ x 0) • ((ContinuousLinearMap.proj 0).comp LG) +
    (G x 0) • ((ContinuousLinearMap.proj 0).comp Lχ) +
  (χ x 1) • ((ContinuousLinearMap.proj 1).comp LG) +
    (G x 1) • ((ContinuousLinearMap.proj 1).comp Lχ)

/-- Product rule for the finite-dimensional vector pairing. -/
theorem hasFDerivAt_vecDot
    {χ G : Vec 2 → Vec 2} {x : Vec 2}
    {Lχ LG : Vec 2 →L[ℝ] Vec 2}
    (hχ : HasFDerivAt χ Lχ x) (hG : HasFDerivAt G LG x) :
    HasFDerivAt (fun y => vecDot (χ y) (G y))
      (vecDotDerivativeAt (χ := χ) (G := G) x Lχ LG) x := by
  have hχj (j : Fin 2) : HasFDerivAt (fun y => χ y j)
      ((ContinuousLinearMap.proj j).comp Lχ) x := by
    exact (ContinuousLinearMap.proj j).hasFDerivAt.comp x hχ
  have hGj (j : Fin 2) : HasFDerivAt (fun y => G y j)
      ((ContinuousLinearMap.proj j).comp LG) x := by
    exact (ContinuousLinearMap.proj j).hasFDerivAt.comp x hG
  let D : Fin 2 → Vec 2 →L[ℝ] ℝ := fun j =>
    χ x j • ((ContinuousLinearMap.proj j).comp LG) +
      G x j • ((ContinuousLinearMap.proj j).comp Lχ)
  have hsum : HasFDerivAt (fun y => vecDot (χ y) (G y)) (D 0 + D 1) x := by
    have h := ((hχj 0).mul (hGj 0)).add ((hχj 1).mul (hGj 1))
    convert h using 1
    funext y
    simp [vecDot, Fin.sum_univ_two]
  convert hsum using 1
  simp [vecDotDerivativeAt, D]
  abel

/-- The defining flow-pulled gradient obeys the source chain rule
`G_l = (∇X_l ∘ X_l⁻¹) ∇T`. -/
theorem G_eq_flowGrad_mulVec
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (T : ℝ → Vec 2 → ℝ)
    (l : ℤ) (t : ℝ) (x : Vec 2)
    {LT : Vec 2 →L[ℝ] ℝ} {LX : Vec 2 →L[ℝ] Vec 2}
    (hT : HasFDerivAt (T t) LT x)
    (hX : HasFDerivAt (I.xFlow hΦ m l t) LX
      (I.xFlowInv hΦ m l t x))
    (hinv : I.xFlow hΦ m l t (I.xFlowInv hΦ m l t x) = x) :
    G I hΦ m T l t x =
      (I.flowGrad hΦ m l t x).mulVec (spaceGrad (T t) x) := by
  have hT' : HasFDerivAt (T t) LT
      (I.xFlow hΦ m l t (I.xFlowInv hΦ m l t x)) := by
    simpa [hinv] using hT
  have h := spaceGrad_comp_eq_gradMatrix_mul hT' hX
  funext i
  simpa [G, Ingredients.flowGrad, Matrix.mulVec, hinv] using h i

end AVenhance.Infra.Section5
