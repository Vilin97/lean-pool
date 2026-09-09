/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CoefficientCostMonotone
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedCanonicalRadius
public import LeanPool.NavierStokesAndEuler.Euler.PacketParentTransverseCosts

@[expose] public section

/-! Polynomial formulas for the fixed-order inverse and for a common
source-radius envelope. No target radius, forcing amplitude or grade
occurs in the primitive envelope. -/

noncomputable section

namespace EulerParameterWordGevrey


def inversePolynomial (I B : Polynomial ℝ) : ℕ → Polynomial ℝ
  | 0 => I
  | n+1 => I+inversePolynomial I B n+2^n*B*(inversePolynomial I B n)^2

theorem inversePolynomial_eval (I B : Polynomial ℝ) (n : ℕ) (x : ℝ) :
    (inversePolynomial I B n).eval x=sobolevInverseCost (I.eval x) (B.eval x) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [inversePolynomial,sobolevInverseCost,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,ih]

def inverseBlockPolynomial (q : ℕ) (I R C D : Polynomial ℝ) : Polynomial ℝ :=
  1+inversePolynomial I (coefficientPolynomial q R C) q*(coefficientPolynomial q R C+D)

theorem inverseBlockPolynomial_eval (q : ℕ) (I R C D : Polynomial ℝ) (x : ℝ) :
    (inverseBlockPolynomial q I R C D).eval x=
      inverseBlockCost (Fin 4) q (I.eval x) (R.eval x) (C.eval x) (D.eval x) := by
  simp only [inverseBlockPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_one,
    inversePolynomial_eval,coefficientPolynomial_eval,inverseBlockCost]

theorem inverseBlockCost_mono_all {ι : Type*} [Fintype ι] (q : ℕ)
    {I R C D I' R' C' D' : ℝ} (hI : 0 ≤ I) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hi : I ≤ I') (hr : R ≤ R') (hc : C ≤ C') (hd : D ≤ D') :
    inverseBlockCost ι q I R C D ≤ inverseBlockCost ι q I' R' C' D' := by
  have hB := sobolevCoefficientAmplitude_nonneg (ι := ι) q R C hR hC
  have hb := sobolevCoefficientAmplitude_mono_all (ι := ι) q hR hC hr hc
  have hS := sobolevInverseCost_mono hI hB hi hb q
  have hS' := sobolevInverseCost_nonneg I' (sobolevCoefficientAmplitude ι q R' C')
    (hI.trans hi) (hB.trans hb) q
  unfold inverseBlockCost
  exact add_le_add le_rfl (mul_le_mul hS (add_le_add hb hd) (add_nonneg hB hD) hS')

theorem inverseBlockCost_one_le {ι : Type*} [Fintype ι] (q : ℕ)
    {I R C D : ℝ} (hI : 0 ≤ I) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    1 ≤ inverseBlockCost ι q I R C D := by
  have hb := sobolevCoefficientAmplitude_nonneg (ι := ι) q R C hR hC
  have hs := sobolevInverseCost_nonneg I (sobolevCoefficientAmplitude ι q R C) hI hb q
  unfold inverseBlockCost
  exact le_add_of_nonneg_right (mul_nonneg hs (add_nonneg hb hD))

end EulerParameterWordGevrey

namespace EulerPacketRadiusPolynomial

open EulerParameterWordGevrey EulerPacketTerminalDatum EulerGevreyCutoff EulerPolynomialCost

abbrev coeff (R C : ℝ) : ℝ := sobolevCoefficientAmplitude (Fin 4) 6 R C
abbrev coeffPoly (R C : Polynomial ℝ) : Polynomial ℝ := coefficientPolynomial 6 R C

def inverseEnvelope (W : ℝ) : ℝ := 2*(1+2*W^5+2*W^2)^2
def formEnvelope (W : ℝ) : ℝ := 36*W^2*(1+W)
def endpointEnvelope (W : ℝ) : ℝ := 6*coeff W W*W

def weakEnvelope (W : ℝ) : ℝ :=
  inverseBlockCost (Fin 4) 6 (inverseEnvelope W) W (formEnvelope W)
    (3*coeff W (2*W)*endpointEnvelope W)

def strongEnvelope (W : ℝ) : ℝ :=
  inverseBlockCost (Fin 4) 6 W W (3*W^2)
    (3*coeff W W*(endpointEnvelope W+6*coeff W W*(2*W+2)))

def forwardEnvelope (W : ℝ) : ℝ :=
  let b := coeff (4*W) (1+36*W^4)
  1+sobolevInverseCost 1 b 6*(b+W*(2*W+2))

def jetEnvelope (W : ℝ) : ℝ := 64+40*W^2

def requiredEnvelope (W : ℝ) : ℝ :=
  W+16*jetEnvelope W+2*(weakEnvelope W+strongEnvelope W)*(16*W+1)+
    2*forwardEnvelope W*(64*W+1)

def physicalEnvelope (W : ℝ) : ℝ :=
  let a := coeff (4*W) W
  3*a+3*a*(3*coeff (4*W) (18*W^3)+3*coeff (4*W) (3*W^2))

def commonEnvelope (W : ℝ) : ℝ :=
  6*coeff W W*(2*W+2)+6*coeff W W+physicalEnvelope W

def normalEnvelope (W : ℝ) : ℝ := coeff (5*W+1) (1+W+6*W^2+729*W^6)

def pressureEnvelope (W : ℝ) : ℝ :=
  3*coeff (4*W) (3*W^2)*(1+6*coeff (4*W) W*commonEnvelope W)

def gradeEnvelope (W : ℝ) : ℝ :=
  commonEnvelope W+135*(normalEnvelope W)^2*(period*commonEnvelope W)+
    3*period*pressureEnvelope W

def meanEnvelope (W : ℝ) : ℝ :=
  let a := coeff W W
  3*a*(W+2)+3*(a*(W+2)+a)+3*a*(W+3*a+6*a*(W+2))

def terminalEnvelope (W : ℝ) : ℝ :=
  coeff (jetEnvelope W) (300*(9/rawBump 0)^3*W^2*terminalMass)*W

def radiusEnvelope (W : ℝ) : ℝ :=
  18*W+2*requiredEnvelope W+meanEnvelope W+gradeEnvelope W*(1+terminalEnvelope W)

def radiusPolynomial : Polynomial ℝ :=
  let X : Polynomial ℝ := Polynomial.X
  let a := coeffPoly X X
  let endpoint := 6*a*X
  let weak := inverseBlockPolynomial 6 (2*(1+2*X^5+2*X^2)^2) X (36*X^2*(1+X))
    (3*coeffPoly X (2*X)*endpoint)
  let strong := inverseBlockPolynomial 6 X X (3*X^2) (3*a*(endpoint+6*a*(2*X+2)))
  let b := coeffPoly (4*X) (1+36*X^4)
  let forward := 1+inversePolynomial 1 b 6*(b+X*(2*X+2))
  let jet := 64+40*X^2
  let required := X+16*jet+2*(weak+strong)*(16*X+1)+2*forward*(64*X+1)
  let a4 := coeffPoly (4*X) X
  let physical := 3*a4+3*a4*(3*coeffPoly (4*X) (18*X^3)+3*coeffPoly (4*X) (3*X^2))
  let common := 6*a*(2*X+2)+6*a+physical
  let normal := coeffPoly (5*X+1) (1+X+6*X^2+729*X^6)
  let pressure := 3*coeffPoly (4*X) (3*X^2)*(1+6*a4*common)
  let grade := common+135*normal^2*(Polynomial.C period*common)+3*Polynomial.C period*pressure
  let mean := 3*a*(X+2)+3*(a*(X+2)+a)+3*a*(X+3*a+6*a*(X+2))
  let terminal := coeffPoly jet (Polynomial.C (300*(9/rawBump 0)^3*terminalMass)*X^2)*X
  18*X+2*required+mean+grade*(1+terminal)

theorem radiusPolynomial_eval (W : ℝ) : radiusPolynomial.eval W=radiusEnvelope W := by
  simp only [radiusPolynomial,radiusEnvelope,requiredEnvelope,weakEnvelope,strongEnvelope,
    inverseEnvelope,formEnvelope,endpointEnvelope,forwardEnvelope,jetEnvelope,meanEnvelope,
    gradeEnvelope,commonEnvelope,physicalEnvelope,normalEnvelope,pressureEnvelope,terminalEnvelope,
    coeffPoly,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,
    Polynomial.eval_one,Polynomial.eval_X,Polynomial.eval_C,inversePolynomial_eval,
    inverseBlockPolynomial_eval,coefficientPolynomial_eval,coeff]
  congr 3
  ring_nf

def radiusConstant : ℝ := coefficientCost radiusPolynomial
def radiusPower : ℕ := radiusPolynomial.natDegree

theorem radiusConstant_pos : 0 < radiusConstant := coefficientCost_pos _

theorem radiusEnvelope_power (W : ℝ) (hW : 1 ≤ W) :
    radiusEnvelope W ≤ radiusConstant*W^radiusPower := by
  rw [← radiusPolynomial_eval]
  exact (le_abs_self _).trans (eval_bound radiusPolynomial W hW)

end EulerPacketRadiusPolynomial
