/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.DoubledResponse.ScalarMaximizers

/-! # Maximizer Algebra -/

namespace Homogenization
namespace Internal
namespace Ch02

noncomputable section

namespace BookCh02

open Book.Ch02

/-!
# Doubled Maximizer Algebra

This file is split mechanically out of `Internal.Ch02.DoubledResponse`.
-/

theorem doubledFieldOfScalarMaximizers_sameAE_of_sameGradient {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    {v w : Solution U a} {vStar wStar : Solution U a.transpose}
    (hvw : Solution.SameGradientAE v w)
    (hvStarwStar : Solution.SameGradientAE vStar wStar) :
    DoubledField.SameAE (U := U)
      (doubledFieldOfScalarMaximizers a v vStar)
      (doubledFieldOfScalarMaximizers a w wStar) := by
  constructor
  · filter_upwards [hvw, hvStarwStar] with x hx hxStar
    change
      ((1 / 2 : ℝ) • (fun x => v.toH1.grad x + vStar.toH1.grad x)) x =
        ((1 / 2 : ℝ) • (fun x => w.toH1.grad x + wStar.toH1.grad x)) x
    simp [hx, hxStar]
  · filter_upwards [hvw, hvStarwStar] with x hx hxStar
    change
      ((1 / 2 : ℝ) •
          (fun x =>
            matVecMul (a.toCoeffField x) (v.toH1.grad x) -
              matVecMul (a.transpose.toCoeffField x) (vStar.toH1.grad x))) x =
        ((1 / 2 : ℝ) •
          (fun x =>
            matVecMul (a.toCoeffField x) (w.toH1.grad x) -
              matVecMul (a.transpose.toCoeffField x) (wStar.toH1.grad x))) x
    simp [CoeffOn.transpose_apply, hx, hxStar]

theorem doubledFieldOfScalarMaximizers_sameAE_add_of_grad_add {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    {v12 v1 v2 : Solution U a} {vStar12 vStar1 vStar2 : Solution U a.transpose}
    (hv :
      v12.toH1.grad =ᵐ[volumeMeasureOn (U : Set (Vec d))]
        fun x => v1.toH1.grad x + v2.toH1.grad x)
    (hvStar :
      vStar12.toH1.grad =ᵐ[volumeMeasureOn (U : Set (Vec d))]
        fun x => vStar1.toH1.grad x + vStar2.toH1.grad x) :
    DoubledField.SameAE (U := U)
      (doubledFieldOfScalarMaximizers a v12 vStar12)
      (doubledFieldOfScalarMaximizers a v1 vStar1 +
        doubledFieldOfScalarMaximizers a v2 vStar2) := by
  constructor
  · filter_upwards [hv, hvStar] with x hx hxStar
    ext i
    change
      (((1 / 2 : ℝ) • (fun x => v12.toH1.grad x + vStar12.toH1.grad x)) x) i =
        ((((1 / 2 : ℝ) • (fun x => v1.toH1.grad x + vStar1.toH1.grad x)) +
          ((1 / 2 : ℝ) • (fun x => v2.toH1.grad x + vStar2.toH1.grad x))) x) i
    simp [hx, hxStar]
    ring
  · filter_upwards [hv, hvStar] with x hx hxStar
    ext i
    change
      (((1 / 2 : ℝ) •
          (fun x =>
            matVecMul (a.toCoeffField x) (v12.toH1.grad x) -
              matVecMul (a.transpose.toCoeffField x) (vStar12.toH1.grad x))) x) i =
        ((((1 / 2 : ℝ) •
            (fun x =>
              matVecMul (a.toCoeffField x) (v1.toH1.grad x) -
                matVecMul (a.transpose.toCoeffField x) (vStar1.toH1.grad x))) +
          ((1 / 2 : ℝ) •
            (fun x =>
              matVecMul (a.toCoeffField x) (v2.toH1.grad x) -
                matVecMul (a.transpose.toCoeffField x) (vStar2.toH1.grad x)))) x) i
    simp [CoeffOn.transpose_apply, hx, hxStar, matVecMul_add, sub_eq_add_neg]
    ring

theorem doubledFieldOfScalarMaximizers_sameAE_smul_of_grad_smul {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (c : ℝ)
    {vc v : Solution U a} {vStarc vStar : Solution U a.transpose}
    (hv :
      vc.toH1.grad =ᵐ[volumeMeasureOn (U : Set (Vec d))]
        fun x => c • v.toH1.grad x)
    (hvStar :
      vStarc.toH1.grad =ᵐ[volumeMeasureOn (U : Set (Vec d))]
        fun x => c • vStar.toH1.grad x) :
    DoubledField.SameAE (U := U)
      (doubledFieldOfScalarMaximizers a vc vStarc)
      (c • doubledFieldOfScalarMaximizers a v vStar) := by
  constructor
  · filter_upwards [hv, hvStar] with x hx hxStar
    ext i
    change
      (((1 / 2 : ℝ) • (fun x => vc.toH1.grad x + vStarc.toH1.grad x)) x) i =
        ((c • ((1 / 2 : ℝ) • (fun x => v.toH1.grad x + vStar.toH1.grad x))) x) i
    simp [hx, hxStar]
    ring
  · filter_upwards [hv, hvStar] with x hx hxStar
    ext i
    change
      (((1 / 2 : ℝ) •
          (fun x =>
            matVecMul (a.toCoeffField x) (vc.toH1.grad x) -
              matVecMul (a.transpose.toCoeffField x) (vStarc.toH1.grad x))) x) i =
        ((c • ((1 / 2 : ℝ) •
          (fun x =>
            matVecMul (a.toCoeffField x) (v.toH1.grad x) -
              matVecMul (a.transpose.toCoeffField x) (vStar.toH1.grad x)))) x) i
    simp [CoeffOn.transpose_apply, hx, hxStar, matVecMul_smul, sub_eq_add_neg]
    ring

theorem maximizer_unique_ae_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    ∀ P Q : BlockVec d, ∀ X Y : DoubledField d,
      IsDoubledResponseMaximizer U a P Q X →
        IsDoubledResponseMaximizer U a P Q Y →
          DoubledField.SameAE (U := U) X Y := by
  intro P Q X Y hX hY
  rcases P with ⟨p, q⟩
  rcases Q with ⟨qStar, pStar⟩
  rcases doubled_maximizer_sameAE_scalar_maximizers_of_isEllipticFieldOn
      U a hEll p pStar q qStar X hX with
    ⟨vX, vStarX, hvX, hvStarX, hXsame⟩
  rcases doubled_maximizer_sameAE_scalar_maximizers_of_isEllipticFieldOn
      U a hEll p pStar q qStar Y hY with
    ⟨vY, vStarY, hvY, hvStarY, hYsame⟩
  have hUnique := responseGradientUniquenessTheory_of_isEllipticFieldOn U a hEll
  have hEllAdj :
      IsEllipticFieldOn a.transpose.lam a.transpose.Lam (U : Set (Vec d))
        a.transpose.toCoeffField := by
    simpa [Homogenization.adjointCoeffField] using!
      isEllipticFieldOn_adjointCoeffField hEll
  have hUniqueAdj := responseGradientUniquenessTheory_of_isEllipticFieldOn U a.transpose hEllAdj
  have hvSame :=
    hUnique.unique_gradient (p - pStar) (qStar - q) vX vY hvX hvY
  have hvStarSame :=
    hUniqueAdj.unique_gradient (pStar + p) (qStar + q) vStarX vStarY hvStarX hvStarY
  have hCandSame :=
    doubledFieldOfScalarMaximizers_sameAE_of_sameGradient U a hvSame hvStarSame
  exact doubledSameAE_trans hXsame
    (doubledSameAE_trans hCandSame (doubledSameAE_symm hYsame))

theorem maximizer_add_sameAE_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    ∀ P1 Q1 P2 Q2 : BlockVec d, ∀ X12 X1 X2 : DoubledField d,
      IsDoubledResponseMaximizer U a (P1 + P2) (Q1 + Q2) X12 →
        IsDoubledResponseMaximizer U a P1 Q1 X1 →
          IsDoubledResponseMaximizer U a P2 Q2 X2 →
            DoubledField.SameAE (U := U) X12 (X1 + X2) := by
  intro P1 Q1 P2 Q2 X12 X1 X2 h12 h1 h2
  rcases P1 with ⟨p1, q1⟩
  rcases Q1 with ⟨qStar1, pStar1⟩
  rcases P2 with ⟨p2, q2⟩
  rcases Q2 with ⟨qStar2, pStar2⟩
  rcases doubled_maximizer_sameAE_scalar_maximizers_of_isEllipticFieldOn
      U a hEll (p1 + p2) (pStar1 + pStar2) (q1 + q2) (qStar1 + qStar2)
      X12 (by simpa using h12) with
    ⟨v12, vStar12, hv12, hvStar12, h12same⟩
  rcases doubled_maximizer_sameAE_scalar_maximizers_of_isEllipticFieldOn
      U a hEll p1 pStar1 q1 qStar1 X1 h1 with
    ⟨v1, vStar1, hv1, hvStar1, h1same⟩
  rcases doubled_maximizer_sameAE_scalar_maximizers_of_isEllipticFieldOn
      U a hEll p2 pStar2 q2 qStar2 X2 h2 with
    ⟨v2, vStar2, hv2, hvStar2, h2same⟩
  have hLinear := responseGradientLinearityTheory_of_isEllipticFieldOn U a hEll
  have hEllAdj :
      IsEllipticFieldOn a.transpose.lam a.transpose.Lam (U : Set (Vec d))
        a.transpose.toCoeffField := by
    simpa [Homogenization.adjointCoeffField] using!
      isEllipticFieldOn_adjointCoeffField hEll
  have hLinearAdj := responseGradientLinearityTheory_of_isEllipticFieldOn U a.transpose hEllAdj
  have hv12' :
      Book.Ch02.IsResponseMaximizer U a
        ((p1 - pStar1) + (p2 - pStar2))
        ((qStar1 - q1) + (qStar2 - q2)) v12 := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hv12
  have hvStar12' :
      Book.Ch02.IsResponseMaximizer U a.transpose
        ((pStar1 + p1) + (pStar2 + p2))
        ((qStar1 + q1) + (qStar2 + q2)) vStar12 := by
    simpa [add_comm, add_left_comm, add_assoc] using hvStar12
  have hvAdd :=
    hLinear.add_gradient (p1 - pStar1) (qStar1 - q1)
      (p2 - pStar2) (qStar2 - q2) v12 v1 v2 hv12' hv1 hv2
  have hvStarAdd :=
    hLinearAdj.add_gradient (pStar1 + p1) (qStar1 + q1)
      (pStar2 + p2) (qStar2 + q2) vStar12 vStar1 vStar2
      hvStar12' hvStar1 hvStar2
  have hCandAdd :=
    doubledFieldOfScalarMaximizers_sameAE_add_of_grad_add U a hvAdd hvStarAdd
  have hSum :=
    doubledSameAE_add (doubledSameAE_symm h1same) (doubledSameAE_symm h2same)
  exact doubledSameAE_trans h12same (doubledSameAE_trans hCandAdd hSum)

theorem maximizer_smul_sameAE_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    ∀ c : ℝ, ∀ P Q : BlockVec d, ∀ Xc X : DoubledField d,
      IsDoubledResponseMaximizer U a (c • P) (c • Q) Xc →
        IsDoubledResponseMaximizer U a P Q X →
          DoubledField.SameAE (U := U) Xc (c • X) := by
  intro c P Q Xc X hc hX
  rcases P with ⟨p, q⟩
  rcases Q with ⟨qStar, pStar⟩
  rcases doubled_maximizer_sameAE_scalar_maximizers_of_isEllipticFieldOn
      U a hEll (c • p) (c • pStar) (c • q) (c • qStar)
      Xc (by simpa using hc) with
    ⟨vc, vStarc, hvc, hvStarc, hcsame⟩
  rcases doubled_maximizer_sameAE_scalar_maximizers_of_isEllipticFieldOn
      U a hEll p pStar q qStar X hX with
    ⟨v, vStar, hv, hvStar, hsame⟩
  have hLinear := responseGradientLinearityTheory_of_isEllipticFieldOn U a hEll
  have hEllAdj :
      IsEllipticFieldOn a.transpose.lam a.transpose.Lam (U : Set (Vec d))
        a.transpose.toCoeffField := by
    simpa [Homogenization.adjointCoeffField] using!
      isEllipticFieldOn_adjointCoeffField hEll
  have hLinearAdj := responseGradientLinearityTheory_of_isEllipticFieldOn U a.transpose hEllAdj
  have hvc' :
      Book.Ch02.IsResponseMaximizer U a (c • (p - pStar)) (c • (qStar - q)) vc := by
    simpa [sub_eq_add_neg, smul_add, smul_neg] using hvc
  have hvStarc' :
      Book.Ch02.IsResponseMaximizer U a.transpose
        (c • (pStar + p)) (c • (qStar + q)) vStarc := by
    simpa [smul_add] using hvStarc
  have hvSmul :=
    hLinear.smul_gradient c (p - pStar) (qStar - q) vc v hvc' hv
  have hvStarSmul :=
    hLinearAdj.smul_gradient c (pStar + p) (qStar + q) vStarc vStar
      hvStarc' hvStar
  have hCandSmul :=
    doubledFieldOfScalarMaximizers_sameAE_smul_of_grad_smul U a c hvSmul hvStarSmul
  have hScaled := doubledSameAE_smul c (doubledSameAE_symm hsame)
  exact doubledSameAE_trans hcsame (doubledSameAE_trans hCandSmul hScaled)

end BookCh02

end

end Ch02
end Internal
end Homogenization
