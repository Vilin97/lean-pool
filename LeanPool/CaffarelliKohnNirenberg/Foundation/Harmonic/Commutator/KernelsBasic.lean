/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Kernels Basic

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators Topology
open Filter MeasureTheory

namespace CKN.Foundation.Harmonic.Commutator

noncomputable section

def q (x : CKN.Vec 3) : ℝ := CKN.vecNormSq x

private theorem hasFDerivAt_q (x : CKN.Vec 3) :
    HasFDerivAt q
      (∑ i : Fin 3, (2 * x i) •
        (ContinuousLinearMap.proj i : CKN.Vec 3 →L[ℝ] ℝ)) x := by
  have hfun : q = ∑ i : Fin 3, (fun y : CKN.Vec 3 => y i * y i) := by
    funext y
    simp [q, CKN.vecNormSq, CKN.vecDot]
  have hsum : HasFDerivAt
      (∑ i : Fin 3, (fun y : CKN.Vec 3 => y i * y i))
      (∑ i : Fin 3, (2 * x i) •
        (ContinuousLinearMap.proj i : CKN.Vec 3 →L[ℝ] ℝ)) x := by
    apply HasFDerivAt.sum
    intro i _hi
    have hprod := (hasFDerivAt_apply (𝕜 := ℝ) i x).mul
      (hasFDerivAt_apply (𝕜 := ℝ) i x)
    convert hprod using 1
    ext z
    simp only [add_apply, smul_apply, ContinuousLinearMap.proj_apply]
    ring
  rw [hfun]
  exact hsum

private theorem hasFDerivAt_q_rpow {x : CKN.Vec 3} (p : ℝ) (hx : q x ≠ 0) :
    HasFDerivAt (fun y : CKN.Vec 3 => q y ^ p)
      ((p * q x ^ (p - 1)) •
        ∑ i : Fin 3, (2 * x i) •
          (ContinuousLinearMap.proj i : CKN.Vec 3 →L[ℝ] ℝ)) x :=
  (hasFDerivAt_q x).rpow_const (p := p) (Or.inl (by simpa [q] using hx))

/-- The inverse Euclidean radius, extended by zero at the origin. -/
def radialInverse (x : CKN.Vec 3) : ℝ :=
  if x = 0 then 0 else q x ^ (-(1 : ℝ) / 2)

private theorem q_pos_of_ne_zero {x : CKN.Vec 3} (hx : x ≠ 0) : 0 < q x := by
  rw [q, ← CKN.vecEuclideanNorm_sq]
  exact sq_pos_of_ne_zero (by
    intro h
    apply hx
    exact CKN.vecEuclideanNorm_eq_zero_iff.mp h)


theorem hasFDerivAt_radialInverse {x : CKN.Vec 3} (hx : x ≠ 0) :
    HasFDerivAt radialInverse
      ((-(1 : ℝ) / 2 * q x ^ (-(1 : ℝ) / 2 - 1)) •
        ∑ i : Fin 3, (2 * x i) •
          (ContinuousLinearMap.proj i : CKN.Vec 3 →L[ℝ] ℝ)) x := by
  have hq0 : q x ≠ 0 := (q_pos_of_ne_zero hx).ne'
  have hpow := hasFDerivAt_q_rpow (-(1 : ℝ) / 2) hq0
  apply hpow.congr_of_eventuallyEq
  filter_upwards [isOpen_ne.mem_nhds hx] with y hy
  simp [radialInverse, hy]

theorem spatialDeriv_radialInverse {x : CKN.Vec 3} (hx : x ≠ 0)
    (i : Fin 3) :
    CKN.spatialDeriv radialInverse i x =
      -x i * q x ^ (-(3 : ℝ) / 2) := by
  have h := hasFDerivAt_radialInverse hx
  have hi := congrArg (fun L : CKN.Vec 3 →L[ℝ] ℝ => L (CKN.basisVec i)) h.fderiv
  rw [CKN.spatialDeriv, hi]
  simp only [smul_apply, smul_eq_mul]
  rw [sum_apply]
  simp only [smul_apply, ContinuousLinearMap.proj_apply, CKN.basisVec_apply]
  simp
  ring_nf

def firstFormula (i : Fin 3) (x : CKN.Vec 3) : ℝ :=
  -x i * q x ^ (-(3 : ℝ) / 2)

theorem hasFDerivAt_firstFormula {x : CKN.Vec 3} (hx : x ≠ 0)
    (i : Fin 3) :
    HasFDerivAt (firstFormula i)
      ((-(q x ^ (-(3 : ℝ) / 2))) •
          (ContinuousLinearMap.proj i : CKN.Vec 3 →L[ℝ] ℝ) +
        (-(x i) •
          ((-(3 : ℝ) / 2 * q x ^ (-(3 : ℝ) / 2 - 1)) •
            ∑ k : Fin 3, (2 * x k) •
              (ContinuousLinearMap.proj k : CKN.Vec 3 →L[ℝ] ℝ)))) x := by
  have hq0 : q x ≠ 0 := (q_pos_of_ne_zero hx).ne'
  have hcoord : HasFDerivAt (fun y : CKN.Vec 3 => y i)
      (ContinuousLinearMap.proj i) x := hasFDerivAt_apply (𝕜 := ℝ) i x
  have hpow := hasFDerivAt_q_rpow (-(3 : ℝ) / 2) hq0
  have hneg := (hcoord.mul hpow).neg
  have hfun : firstFormula i = -((fun y : CKN.Vec 3 => y i) *
      (fun y : CKN.Vec 3 => q y ^ (-(3 : ℝ) / 2))) := by
    funext y
    simp [firstFormula]
  rw [hfun]
  apply hneg.congr_fderiv
  ext z
  simp [sum_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]

theorem spatialDeriv_firstFormula {x : CKN.Vec 3} (hx : x ≠ 0)
    (i j : Fin 3) :
    CKN.spatialDeriv (firstFormula i) j x =
      3 * x i * x j * q x ^ (-(5 : ℝ) / 2) -
        (if i = j then 1 else 0) * q x ^ (-(3 : ℝ) / 2) := by
  have h := hasFDerivAt_firstFormula hx i
  have hj := congrArg (fun L : CKN.Vec 3 →L[ℝ] ℝ => L (CKN.basisVec j)) h.fderiv
  rw [CKN.spatialDeriv, hj]
  simp only [smul_apply, add_apply, smul_eq_mul]
  rw [sum_apply]
  simp only [smul_apply, ContinuousLinearMap.proj_apply, CKN.basisVec_apply]
  simp
  ring_nf
  by_cases h : i = j
  · subst j
    simp
    ring
  · simp [h]

private theorem spatialDeriv_firstFormula_ne {x : CKN.Vec 3} (hx : x ≠ 0)
    (i : Fin 3) :
    (fun y => CKN.spatialDeriv radialInverse i y) =ᶠ[𝓝 x] firstFormula i := by
  filter_upwards [isOpen_ne.mem_nhds hx] with y hy
  rw [spatialDeriv_radialInverse hy]
  rfl

private theorem spatialDeriv_second_radialInverse {x : CKN.Vec 3} (hx : x ≠ 0)
    (i j : Fin 3) :
    CKN.spatialDeriv (CKN.spatialDeriv radialInverse i) j x =
      3 * x i * x j * q x ^ (-(5 : ℝ) / 2) -
        (if i = j then 1 else 0) * q x ^ (-(3 : ℝ) / 2) := by
  have h := (hasFDerivAt_firstFormula hx i).congr_of_eventuallyEq
    (spatialDeriv_firstFormula_ne hx i)
  have hj := congrArg (fun L : CKN.Vec 3 →L[ℝ] ℝ => L (CKN.basisVec j)) h.fderiv
  rw [CKN.spatialDeriv, hj]
  simp only [smul_apply, add_apply, smul_eq_mul]
  rw [sum_apply]
  simp only [smul_apply, ContinuousLinearMap.proj_apply, CKN.basisVec_apply]
  simp
  ring_nf
  by_cases h' : i = j
  · subst j
    simp
    ring
  · simp [h']

def secondFormula (i j : Fin 3) (x : CKN.Vec 3) : ℝ :=
  3 * x i * x j * q x ^ (-(5 : ℝ) / 2) -
    (if i = j then 1 else 0) * q x ^ (-(3 : ℝ) / 2)

def qDerivative (p : ℝ) (x : CKN.Vec 3) : CKN.Vec 3 →L[ℝ] ℝ :=
  (p * q x ^ (p - 1)) •
    ∑ k : Fin 3, (2 * x k) •
      (ContinuousLinearMap.proj k : CKN.Vec 3 →L[ℝ] ℝ)

def secondDerivative (i j : Fin 3) (x : CKN.Vec 3) : CKN.Vec 3 →L[ℝ] ℝ :=
  3 • ((x i * x j) • qDerivative (-(5 : ℝ) / 2) x +
    (q x ^ (-(5 : ℝ) / 2)) •
      (x i • (ContinuousLinearMap.proj j : CKN.Vec 3 →L[ℝ] ℝ) +
        x j • (ContinuousLinearMap.proj i : CKN.Vec 3 →L[ℝ] ℝ))) -
    (if i = j then 1 else 0) • qDerivative (-(3 : ℝ) / 2) x

theorem hasFDerivAt_secondFormula {x : CKN.Vec 3} (hx : x ≠ 0)
    (i j : Fin 3) :
    HasFDerivAt (secondFormula i j) (secondDerivative i j x) x := by
  by_cases hij : i = j
  · subst j
    have hq0 : q x ≠ 0 := (q_pos_of_ne_zero hx).ne'
    have hcoordi : HasFDerivAt (fun y : CKN.Vec 3 => y i)
        (ContinuousLinearMap.proj i) x := hasFDerivAt_apply (𝕜 := ℝ) i x
    have hprod := hcoordi.mul hcoordi
    have hterm := (hprod.mul (hasFDerivAt_q_rpow (-(5 : ℝ) / 2) hq0)).const_mul (3 : ℝ)
    have htotal := hterm.sub (hasFDerivAt_q_rpow (-(3 : ℝ) / 2) hq0)
    convert htotal using 1
    · funext y
      simp [secondFormula]
      ring
    · ext z
      simp [secondDerivative, qDerivative, sum_apply, smul_eq_mul]
  · have hq0 : q x ≠ 0 := (q_pos_of_ne_zero hx).ne'
    have hcoordi : HasFDerivAt (fun y : CKN.Vec 3 => y i)
        (ContinuousLinearMap.proj i) x := hasFDerivAt_apply (𝕜 := ℝ) i x
    have hcoordj : HasFDerivAt (fun y : CKN.Vec 3 => y j)
        (ContinuousLinearMap.proj j) x := hasFDerivAt_apply (𝕜 := ℝ) j x
    have hprod := hcoordi.mul hcoordj
    have hterm := (hprod.mul (hasFDerivAt_q_rpow (-(5 : ℝ) / 2) hq0)).const_mul (3 : ℝ)
    have hzero : HasFDerivAt (fun _y : CKN.Vec 3 => (0 : ℝ)) 0 x :=
      hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) x
    have htotal := hterm.sub hzero
    convert htotal using 1
    · funext y
      simp [secondFormula, hij]
      ring
    · ext z
      simp [secondDerivative, qDerivative, sum_apply, smul_eq_mul, hij]

theorem spatialDeriv_secondFormula {x : CKN.Vec 3} (hx : x ≠ 0)
    (i j m : Fin 3) :
    CKN.spatialDeriv (secondFormula i j) m x =
      3 * (if m = i then 1 else 0) * x j * q x ^ (-(5 : ℝ) / 2) +
      3 * x i * (if m = j then 1 else 0) * q x ^ (-(5 : ℝ) / 2) -
      15 * x i * x j * x m * q x ^ (-(7 : ℝ) / 2) +
      3 * (if i = j then 1 else 0) * x m * q x ^ (-(5 : ℝ) / 2) := by
  have h := hasFDerivAt_secondFormula hx i j
  have hm := congrArg (fun L : CKN.Vec 3 →L[ℝ] ℝ => L (CKN.basisVec m)) h.fderiv
  rw [CKN.spatialDeriv, hm]
  by_cases hmi : m = i
  · subst i
    by_cases hmj : m = j
    · subst j
      simp [secondDerivative, qDerivative, sum_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul]
      all_goals ring_nf
    · have hjm : ¬j = m := by
        intro h
        exact hmj h.symm
      simp [secondDerivative, qDerivative, sum_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul, hmj, hjm]
      all_goals ring_nf
  · by_cases hmj : m = j
    · subst j
      have him : ¬i = m := by
        intro h
        exact hmi h.symm
      simp [secondDerivative, qDerivative, sum_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul, hmi, him]
      all_goals simp only [show -(5 : ℝ) / 2 - 1 = -(7 : ℝ) / 2 by norm_num]
      all_goals ring_nf
    · by_cases hij : i = j
      · subst j
        have him : ¬i = m := by
          intro h
          exact hmi h.symm
        simp [secondDerivative, qDerivative, sum_apply,
          ContinuousLinearMap.proj_apply, smul_eq_mul, hmi, him]
        simp only [show -(5 : ℝ) / 2 - 1 = -(7 : ℝ) / 2 by norm_num]
        ring_nf
      · have him : ¬i = m := by
          intro h
          exact hmi h.symm
        have hjm : ¬j = m := by
          intro h
          exact hmj h.symm
        simp [secondDerivative, qDerivative, sum_apply,
          ContinuousLinearMap.proj_apply, smul_eq_mul, hmi, hmj, hij, him, hjm]
        all_goals ring_nf

theorem spatialDeriv_third_radialInverse {x : CKN.Vec 3} (hx : x ≠ 0)
    (i j m : Fin 3) :
    CKN.spatialDeriv (CKN.spatialDeriv (CKN.spatialDeriv radialInverse i) j) m x =
      3 * (if m = i then 1 else 0) * x j * q x ^ (-(5 : ℝ) / 2) +
      3 * x i * (if m = j then 1 else 0) * q x ^ (-(5 : ℝ) / 2) -
      15 * x i * x j * x m * q x ^ (-(7 : ℝ) / 2) +
      3 * (if i = j then 1 else 0) * x m * q x ^ (-(5 : ℝ) / 2) := by
  have hEq : (fun y =>
      CKN.spatialDeriv (CKN.spatialDeriv radialInverse i) j y) =ᶠ[𝓝 x]
      secondFormula i j := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    simpa [secondFormula] using spatialDeriv_second_radialInverse hy i j
  have h := (hasFDerivAt_secondFormula hx i j).congr_of_eventuallyEq hEq
  have hm := congrArg (fun L : CKN.Vec 3 →L[ℝ] ℝ => L (CKN.basisVec m)) h.fderiv
  rw [CKN.spatialDeriv, hm]
  have hcalc := spatialDeriv_secondFormula hx i j m
  rw [CKN.spatialDeriv] at hcalc
  have h2 := hasFDerivAt_secondFormula hx i j
  have hm2 := congrArg (fun L : CKN.Vec 3 →L[ℝ] ℝ => L (CKN.basisVec m)) h2.fderiv
  rw [hm2] at hcalc
  exact hcalc

private theorem q_rpow_eq_norm_rpow {x : CKN.Vec 3} (_ : x ≠ 0)
    (p : ℝ) : q x ^ p = (CKN.vecEuclideanNorm x) ^ (2 * p) := by
  rw [q, ← CKN.vecEuclideanNorm_sq]
  rw [← Real.rpow_natCast]
  rw [Real.rpow_mul (CKN.vecEuclideanNorm_nonneg x)]
  norm_num

private theorem q_rpow_neg_five {x : CKN.Vec 3} (hx : x ≠ 0) :
    q x ^ (-(5 : ℝ) / 2) = (CKN.vecEuclideanNorm x ^ 5)⁻¹ := by
  rw [q_rpow_eq_norm_rpow hx (-(5 : ℝ) / 2)]
  rw [show 2 * (-(5 : ℝ) / 2) = -(5 : ℝ) by ring]
  rw [Real.rpow_neg (CKN.vecEuclideanNorm_nonneg x)]
  norm_num

private theorem q_rpow_neg_seven {x : CKN.Vec 3} (hx : x ≠ 0) :
    q x ^ (-(7 : ℝ) / 2) = (CKN.vecEuclideanNorm x ^ 7)⁻¹ := by
  rw [q_rpow_eq_norm_rpow hx (-(7 : ℝ) / 2)]
  rw [show 2 * (-(7 : ℝ) / 2) = -(7 : ℝ) by ring]
  rw [Real.rpow_neg (CKN.vecEuclideanNorm_nonneg x)]
  norm_num

private theorem q_rpow_neg_nine {x : CKN.Vec 3} (hx : x ≠ 0) :
    q x ^ (-(9 : ℝ) / 2) = (CKN.vecEuclideanNorm x ^ 9)⁻¹ := by
  rw [q_rpow_eq_norm_rpow hx (-(9 : ℝ) / 2)]
  rw [show 2 * (-(9 : ℝ) / 2) = -(9 : ℝ) by ring]
  rw [Real.rpow_neg (CKN.vecEuclideanNorm_nonneg x)]
  norm_num

/-- The third derivative of the inverse Euclidean radius, in the convention
used by the Newtonian kernel. -/
def inverseThirdFormula (m j l : Fin 3) (x : CKN.Vec 3) : ℝ :=
  -15 * x m * x j * x l * (CKN.vecEuclideanNorm x ^ 7)⁻¹ +
    3 * ((if m = l then 1 else 0) * x j +
      (if m = j then 1 else 0) * x l +
      (if l = j then 1 else 0) * x m) *
      (CKN.vecEuclideanNorm x ^ 5)⁻¹

theorem third_derivative_inverse_norm {x : CKN.Vec 3} (hx : x ≠ 0)
    (m j l : Fin 3) :
    CKN.spatialDeriv (CKN.spatialDeriv (CKN.spatialDeriv radialInverse l) j) m x =
      inverseThirdFormula m j l x := by
  rw [spatialDeriv_third_radialInverse hx l j m]
  rw [q_rpow_neg_five hx, q_rpow_neg_seven hx]
  unfold inverseThirdFormula
  ring


def inverseThirdFormulaQ (m j l : Fin 3) (x : CKN.Vec 3) : ℝ :=
  -15 * x m * x j * x l * q x ^ (-(7 : ℝ) / 2) +
    3 * ((if m = l then 1 else 0) * x j +
      (if m = j then 1 else 0) * x l +
      (if l = j then 1 else 0) * x m) * q x ^ (-(5 : ℝ) / 2)

def inverseThirdFormulaQDerivative (m j l : Fin 3) (x : CKN.Vec 3) :
    CKN.Vec 3 →L[ℝ] ℝ :=
  (-15 : ℝ) • (
      q x ^ (-(7 : ℝ) / 2) •
          ((x j * x l) • (ContinuousLinearMap.proj m : CKN.Vec 3 →L[ℝ] ℝ) +
            (x m * x l) • (ContinuousLinearMap.proj j : CKN.Vec 3 →L[ℝ] ℝ) +
            (x m * x j) • (ContinuousLinearMap.proj l : CKN.Vec 3 →L[ℝ] ℝ)) +
        (x m * x j * x l) • qDerivative (-(7 : ℝ) / 2) x) +
    (3 : ℝ) • (
      q x ^ (-(5 : ℝ) / 2) •
          ((if m = l then 1 else 0) •
              (ContinuousLinearMap.proj j : CKN.Vec 3 →L[ℝ] ℝ) +
            (if m = j then 1 else 0) •
              (ContinuousLinearMap.proj l : CKN.Vec 3 →L[ℝ] ℝ) +
            (if l = j then 1 else 0) •
              (ContinuousLinearMap.proj m : CKN.Vec 3 →L[ℝ] ℝ)) +
        ((if m = l then 1 else 0) * x j +
          (if m = j then 1 else 0) * x l +
          (if l = j then 1 else 0) * x m) •
          qDerivative (-(5 : ℝ) / 2) x)

private theorem hasFDerivAt_inverseThirdFormulaQ {x : CKN.Vec 3} (hx : x ≠ 0)
    (m j l : Fin 3) :
    HasFDerivAt (inverseThirdFormulaQ m j l)
      (inverseThirdFormulaQDerivative m j l x) x := by
  have hq0 : q x ≠ 0 := (q_pos_of_ne_zero hx).ne'
  have hm : HasFDerivAt (fun y : CKN.Vec 3 => y m)
      (ContinuousLinearMap.proj m) x := hasFDerivAt_apply (𝕜 := ℝ) m x
  have hj : HasFDerivAt (fun y : CKN.Vec 3 => y j)
      (ContinuousLinearMap.proj j) x := hasFDerivAt_apply (𝕜 := ℝ) j x
  have hl : HasFDerivAt (fun y : CKN.Vec 3 => y l)
      (ContinuousLinearMap.proj l) x := hasFDerivAt_apply (𝕜 := ℝ) l x
  have hfirst := hm.mul (hj.mul hl)
  have hfirst' := hfirst.mul (hasFDerivAt_q_rpow (-(7 : ℝ) / 2) hq0)
  have hA := hfirst'.const_mul (-15 : ℝ)
  have hml := hj.const_mul (if m = l then (1 : ℝ) else 0)
  have hmj := hl.const_mul (if m = j then (1 : ℝ) else 0)
  have hlj := hm.const_mul (if l = j then (1 : ℝ) else 0)
  have hsum := (hml.add hmj).add hlj
  have hsecond := hsum.mul (hasFDerivAt_q_rpow (-(5 : ℝ) / 2) hq0)
  have hB := hsecond.const_mul (3 : ℝ)
  have htotal := hA.add hB
  convert htotal using 1
  · funext y
    simp [inverseThirdFormulaQ]
    ring
  · ext z
    simp only [inverseThirdFormulaQDerivative, qDerivative, add_apply,
      smul_apply, sum_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
      Pi.mul_apply, Pi.add_apply, ite_smul, one_smul, zero_smul,
      ite_mul, one_mul, zero_mul]
    ring

/-- The Newtonian potential and its third-derivative kernel. -/
def newtonianPotential (x : CKN.Vec 3) : ℝ :=
  -(4 * Real.pi)⁻¹ * radialInverse x

def newtonianKernel (m j l : Fin 3) (x : CKN.Vec 3) : ℝ :=
  -(4 * Real.pi)⁻¹ * inverseThirdFormula m j l x

theorem newtonianKernel_spatialDeriv_size_bound {x : CKN.Vec 3} (hx : x ≠ 0)
    (m j l n : Fin 3) :
    |CKN.spatialDeriv (newtonianKernel m j l) n x| ≤
      (204 / (4 * Real.pi)) * CKN.vecEuclideanNorm x ^ (-5 : ℝ) := by
  have hEq : (fun y => inverseThirdFormula m j l y) =ᶠ[𝓝 x]
      (fun y => inverseThirdFormulaQ m j l y) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    simp only [inverseThirdFormula, inverseThirdFormulaQ]
    rw [← q_rpow_neg_five hy, ← q_rpow_neg_seven hy]
  have hbase := (hasFDerivAt_inverseThirdFormulaQ hx m j l).congr_of_eventuallyEq hEq
  have hscaled := hbase.const_mul (-(4 * Real.pi)⁻¹)
  have hkernelEq : (fun y => newtonianKernel m j l y) =ᶠ[𝓝 x]
      (fun y => -(4 * Real.pi)⁻¹ * inverseThirdFormula m j l y) := by
    filter_upwards [] with y
    rfl
  have hkernel := hscaled.congr_of_eventuallyEq hkernelEq
  have hn := congrArg (fun L : CKN.Vec 3 →L[ℝ] ℝ => L (CKN.basisVec n)) hkernel.fderiv
  rw [CKN.spatialDeriv, hn]
  have hite (p : Prop) [Decidable p] (L : CKN.Vec 3 →L[ℝ] ℝ) :
      (if p then L else 0) (CKN.basisVec n) =
        if p then L (CKN.basisVec n) else 0 := by
    by_cases hp : p <;> simp [hp]
  have hinner :
      |inverseThirdFormulaQDerivative m j l x (CKN.basisVec n)| ≤
        204 * CKN.vecEuclideanNorm x ^ (-5 : ℝ) := by
    let r := CKN.vecEuclideanNorm x
    have hr : 0 < r := by
      dsimp [r]
      apply lt_of_le_of_ne (CKN.vecEuclideanNorm_nonneg x)
      intro h
      apply hx
      exact CKN.vecEuclideanNorm_eq_zero_iff.mp h.symm
    have hcoord (i : Fin 3) : |x i| ≤ r := by
      exact abs_apply_le_vecEuclideanNorm x i
    have hq5 : q x ^ (-(5 : ℝ) / 2) = (r ^ 5)⁻¹ := by
      simpa [r] using q_rpow_neg_five hx
    have hq7 : q x ^ (-(7 : ℝ) / 2) = (r ^ 7)⁻¹ := by
      simpa [r] using q_rpow_neg_seven hx
    have hq9 : q x ^ (-(9 : ℝ) / 2) = (r ^ 9)⁻¹ := by
      simpa [r] using q_rpow_neg_nine hx
    have hq7' : q x ^ (-(7 : ℝ) / 2 - 1) = (r ^ 9)⁻¹ := by
      rw [show -(7 : ℝ) / 2 - 1 = -(9 : ℝ) / 2 by norm_num, hq9]
    have hq5' : q x ^ (-(5 : ℝ) / 2 - 1) = (r ^ 7)⁻¹ := by
      rw [show -(5 : ℝ) / 2 - 1 = -(7 : ℝ) / 2 by norm_num, hq7]
    simp [inverseThirdFormulaQDerivative, qDerivative, sum_apply,
      ContinuousLinearMap.proj_apply, CKN.basisVec_apply, smul_eq_mul, hite]
    rw [hq5, hq7, hq7', hq5']
    rw [show CKN.vecEuclideanNorm x = r by rfl]
    have hdelta (p : Prop) [Decidable p] (a : ℝ) :
        |if p then a else 0| ≤ |a| := by
      by_cases hp : p <;> simp [hp]
    have hA (a b : Fin 3) :
        |15 * ((r ^ 7)⁻¹ * (x a * x b))| ≤ 15 * (r ^ 5)⁻¹ := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 15),
        abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr.le _))]
      calc
        15 * ((r ^ 7)⁻¹ * (|x a| * |x b|)) ≤
            15 * ((r ^ 7)⁻¹ * (r * r)) := by
          gcongr
          · exact hcoord a
          · exact hcoord b
        _ = 15 * (r ^ 5)⁻¹ := by
          field_simp [hr.ne']
    have hB (p q' : Prop) [Decidable p] [Decidable q'] :
        |if p then if q' then 3 * (r ^ 5)⁻¹ else 0 else 0| ≤
          3 * (r ^ 5)⁻¹ := by
      by_cases hp : p
      · by_cases hq' : q'
        · simp [hp, hq', abs_of_pos hr]
        · simp [hp, hq']
          positivity
      · by_cases hq' : q'
        · simp [hp]
          positivity
        · simp [hp]
          positivity
    have habs8 (a b c d e f g h : ℝ) :
        |a + b + c + d + e + f + g + h| ≤
          |a| + |b| + |c| + |d| + |e| + |f| + |g| + |h| := by
      calc
        |a + b + c + d + e + f + g + h| ≤
            |a| + |b + c + d + e + f + g + h| := by
          simpa [add_assoc] using (abs_add_le a (b + c + d + e + f + g + h))
        _ ≤ |a| + (|b| + |c + d + e + f + g + h|) := by
          gcongr
          simpa [add_assoc] using (abs_add_le b (c + d + e + f + g + h))
        _ ≤ |a| + (|b| + (|c| + |d + e + f + g + h|)) := by
          gcongr
          simpa [add_assoc] using (abs_add_le c (d + e + f + g + h))
        _ ≤ |a| + (|b| + (|c| + (|d| + |e + f + g + h|))) := by
          gcongr
          simpa [add_assoc] using (abs_add_le d (e + f + g + h))
        _ ≤ |a| + (|b| + (|c| + (|d| + (|e| + |f + g + h|)))) := by
          gcongr
          simpa [add_assoc] using (abs_add_le e (f + g + h))
        _ ≤ |a| + (|b| + (|c| + (|d| + (|e| + (|f| + |g + h|))))) := by
          gcongr
          simpa [add_assoc] using (abs_add_le f (g + h))
        _ ≤ |a| + |b| + |c| + |d| + |e| + |f| + |g| + |h| := by
          calc
            _ ≤ |a| + (|b| + (|c| + (|d| + (|e| + (|f| + (|g| + |h|)))))) := by
              gcongr
              exact abs_add_le g h
            _ = _ := by ring
    have hsum := habs8
      (-if m = n then 15 * ((r ^ 7)⁻¹ * (x j * x l)) else 0)
      (-if j = n then 15 * ((r ^ 7)⁻¹ * (x m * x l)) else 0)
      (-if l = n then 15 * ((r ^ 7)⁻¹ * (x m * x j)) else 0)
      (-(15 * (x m * x j * x l * (-7 / 2 * (r ^ 9)⁻¹ * (2 * x n)))))
      (if m = l then if j = n then 3 * (r ^ 5)⁻¹ else 0 else 0)
      (if m = j then if l = n then 3 * (r ^ 5)⁻¹ else 0 else 0)
      (if l = j then if m = n then 3 * (r ^ 5)⁻¹ else 0 else 0)
      (3 * (((if m = l then x j else 0) + if m = j then x l else 0) +
        if l = j then x m else 0) * (-5 / 2 * (r ^ 7)⁻¹ * (2 * x n)))
    have hA1 :
        |-if m = n then 15 * ((r ^ 7)⁻¹ * (x j * x l)) else 0| ≤
          15 * (r ^ 5)⁻¹ := by
      calc
        _ = |if m = n then 15 * ((r ^ 7)⁻¹ * (x j * x l)) else 0| := abs_neg _
        _ ≤ |15 * ((r ^ 7)⁻¹ * (x j * x l))| := hdelta _ _
        _ ≤ _ := hA j l
    have hA2 :
        |-if j = n then 15 * ((r ^ 7)⁻¹ * (x m * x l)) else 0| ≤
          15 * (r ^ 5)⁻¹ := by
      calc
        _ = |if j = n then 15 * ((r ^ 7)⁻¹ * (x m * x l)) else 0| := abs_neg _
        _ ≤ |15 * ((r ^ 7)⁻¹ * (x m * x l))| := hdelta _ _
        _ ≤ _ := hA m l
    have hA3 :
        |-if l = n then 15 * ((r ^ 7)⁻¹ * (x m * x j)) else 0| ≤
          15 * (r ^ 5)⁻¹ := by
      calc
        _ = |if l = n then 15 * ((r ^ 7)⁻¹ * (x m * x j)) else 0| := abs_neg _
        _ ≤ |15 * ((r ^ 7)⁻¹ * (x m * x j))| := hdelta _ _
        _ ≤ _ := hA m j
    have hA4 :
        |-(15 * (x m * x j * x l * (-7 / 2 * (r ^ 9)⁻¹ * (2 * x n))))| ≤
          105 * (r ^ 5)⁻¹ := by
      rw [abs_neg, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul]
      norm_num [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr.le _))]
      calc
        15 * (|x m| * |x j| * |x l| *
              ((7 / 2 : ℝ) * (r ^ 9)⁻¹ * (2 * |x n|))) ≤
            15 * (r * r * r * ((7 / 2 : ℝ) * (r ^ 9)⁻¹ * (2 * r))) := by
          gcongr
          · exact hcoord m
          · exact hcoord j
          · exact hcoord l
          · exact hcoord n
        _ = 105 * (r ^ 5)⁻¹ := by
          field_simp [hr.ne']
          ring
    have habs3 (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
      calc
        |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
        _ ≤ (|a| + |b|) + |c| := by
          gcongr
          exact abs_add_le _ _
        _ = |a| + |b| + |c| := by ring
    have hS :
        |((if m = l then x j else 0) + if m = j then x l else 0) +
            if l = j then x m else 0| ≤ 3 * r := by
      have hml : |if m = l then x j else 0| ≤ |x j| := hdelta _ _
      have hmj : |if m = j then x l else 0| ≤ |x l| := hdelta _ _
      have hlj : |if l = j then x m else 0| ≤ |x m| := hdelta _ _
      calc
        _ ≤ |if m = l then x j else 0| +
            |if m = j then x l else 0| +
            |if l = j then x m else 0| := habs3 _ _ _
        _ ≤ |x j| + |x l| + |x m| := by
          exact add_le_add (add_le_add hml hmj) hlj
        _ ≤ r + r + r := by gcongr <;> exact hcoord _
        _ = 3 * r := by ring
    have hB4 :
        |3 * (((if m = l then x j else 0) + if m = j then x l else 0) +
            if l = j then x m else 0) *
            (-5 / 2 * (r ^ 7)⁻¹ * (2 * x n))| ≤
          45 * (r ^ 5)⁻¹ := by
      rw [abs_mul, abs_mul]
      norm_num [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr.le _))]
      have hfactor : 0 ≤ (5 / 2 : ℝ) * (r ^ 7)⁻¹ * (2 * |x n|) := by
        positivity
      calc
        3 * |((if m = l then x j else 0) + if m = j then x l else 0) +
              if l = j then x m else 0| *
              ((5 / 2 : ℝ) * (r ^ 7)⁻¹ * (2 * |x n|)) ≤
            3 * (3 * r * ((5 / 2 : ℝ) * (r ^ 7)⁻¹ * (2 * r))) := by
          calc
            _ ≤ 3 * (3 * r) *
                ((5 / 2 : ℝ) * (r ^ 7)⁻¹ * (2 * |x n|)) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hS (by norm_num)) hfactor
            _ ≤ _ := by
              have hc : 0 ≤ (5 / 2 : ℝ) * (r ^ 7)⁻¹ := by positivity
              have hfactor_le :
                  (5 / 2 : ℝ) * (r ^ 7)⁻¹ * (2 * |x n|) ≤
                    (5 / 2 : ℝ) * (r ^ 7)⁻¹ * (2 * r) := by
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left (hcoord n) (by norm_num)) hc
              have houter : 0 ≤ 3 * (3 * r) := by positivity
              simpa [mul_assoc] using mul_le_mul_of_nonneg_left hfactor_le houter
        _ = 45 * (r ^ 5)⁻¹ := by
          field_simp [hr.ne']
          ring
    have hB1 := hB (m = l) (j = n)
    have hB2 := hB (m = j) (l = n)
    have hB3 := hB (l = j) (m = n)
    calc
      _ ≤
          |(-if m = n then 15 * ((r ^ 7)⁻¹ * (x j * x l)) else 0)| +
            |(-if j = n then 15 * ((r ^ 7)⁻¹ * (x m * x l)) else 0)| +
            |(-if l = n then 15 * ((r ^ 7)⁻¹ * (x m * x j)) else 0)| +
            |-(15 * (x m * x j * x l * (-7 / 2 * (r ^ 9)⁻¹ * (2 * x n))))| +
            |if m = l then if j = n then 3 * (r ^ 5)⁻¹ else 0 else 0| +
            |if m = j then if l = n then 3 * (r ^ 5)⁻¹ else 0 else 0| +
            |if l = j then if m = n then 3 * (r ^ 5)⁻¹ else 0 else 0| +
            |3 * (((if m = l then x j else 0) + if m = j then x l else 0) +
              if l = j then x m else 0) *
              (-5 / 2 * (r ^ 7)⁻¹ * (2 * x n))| := by
        convert hsum using 1
        all_goals congr 1
        all_goals ring
      _ ≤ 204 * (r ^ 5)⁻¹ := by
        calc
          _ ≤
              15 * (r ^ 5)⁻¹ + 15 * (r ^ 5)⁻¹ + 15 * (r ^ 5)⁻¹ +
                105 * (r ^ 5)⁻¹ + 3 * (r ^ 5)⁻¹ + 3 * (r ^ 5)⁻¹ +
                3 * (r ^ 5)⁻¹ + 45 * (r ^ 5)⁻¹ := by
            linarith only [hA1, hA2, hA3, hA4, hB1, hB2, hB3, hB4]
          _ = 204 * (r ^ 5)⁻¹ := by ring
  change |-(4 * Real.pi)⁻¹ * inverseThirdFormulaQDerivative m j l x
      (CKN.basisVec n)| ≤ _
  rw [abs_mul]
  have hscale : |-(4 * Real.pi)⁻¹| = (4 * Real.pi)⁻¹ := by
    rw [abs_neg, abs_of_nonneg]
    positivity
  rw [hscale]
  calc
    (4 * Real.pi)⁻¹ *
          |inverseThirdFormulaQDerivative m j l x (CKN.basisVec n)| ≤
        (4 * Real.pi)⁻¹ *
          (204 * CKN.vecEuclideanNorm x ^ (-5 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = (204 / (4 * Real.pi)) * CKN.vecEuclideanNorm x ^ (-5 : ℝ) := by
      ring

end
end CKN.Foundation.Harmonic.Commutator
