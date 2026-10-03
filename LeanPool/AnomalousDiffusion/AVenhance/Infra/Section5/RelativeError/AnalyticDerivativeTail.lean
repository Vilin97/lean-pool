/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsThetaAnalytic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.AnalyticTail
public import Mathlib.Data.Nat.Choose.Bounds

/-! # analytic tails after arbitrary ordered derivatives

The analyticity bounds control every ordered coordinate derivative.
This module keeps the order explicit and applies the existing Fourier tail
estimate to the derivative before taking its spectral complement. -/

@[expose] public section

noncomputable section

open MeasureTheory
open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance.Infra.Torus
open AVenhance.Infra.Ergodic

/-- Iterate real spatial directional derivatives in the order prescribed by a word. -/
def orderedRealDerivative : List (Fin 2) → (Vec 2 → ℝ) → Vec 2 → ℝ
  | [], f => f
  | i :: is, f => fun x => fderiv ℝ (orderedRealDerivative is f) x (basisVec i)

/-- Iterate complex coordinate derivatives in the order prescribed by a word. -/
def AnalyticDerivativeTail.complexDirectionIter : List (Fin 2) → (Vec 2 → ℂ) → Vec 2 → ℂ
  | [], f => f
  | i :: is, f => coordDeriv i (AnalyticDerivativeTail.complexDirectionIter is f)

theorem AnalyticDerivativeTail.orderedRealDerivative_contDiff_top (is : List (Fin 2))
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (orderedRealDerivative is f) := by
  induction is with
  | nil => simpa [orderedRealDerivative] using hf
  | cons i is ih =>
      have h := ih.contDiff_fderiv_apply (m := ∞) (by simp)
      have hc : ContDiff ℝ ∞ (fun x : Vec 2 => (x, basisVec i)) :=
        contDiff_id.prodMk contDiff_const
      convert h.comp hc using 1
      ext x
      rfl

theorem AnalyticDerivativeTail.complexDirectionIter_contDiff_top (is : List (Fin 2))
    {f : Vec 2 → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (AnalyticDerivativeTail.complexDirectionIter is f) := by
  induction is with
  | nil => simpa [AnalyticDerivativeTail.complexDirectionIter] using hf
  | cons i is ih =>
      have h := ih.contDiff_fderiv_apply (m := ∞) (by simp)
      have hc : ContDiff ℝ ∞ (fun x : Vec 2 => (x, basisVec i)) :=
        contDiff_id.prodMk contDiff_const
      convert h.comp hc using 1
      ext x
      rfl

theorem AnalyticDerivativeTail.orderedRealDerivative_periodic (is : List (Fin 2))
    {f : Vec 2 → ℝ} (hf : IsZ2Periodic f) :
    IsZ2Periodic (orderedRealDerivative is f) := by
  induction is with
  | nil => simpa [orderedRealDerivative] using hf
  | cons i is ih =>
      intro k x
      have hfun : (fun y : Vec 2 => orderedRealDerivative is f
          (y + latticeShift k)) = orderedRealDerivative is f := by
        funext y
        exact ih k y
      have hder : fderiv ℝ (orderedRealDerivative is f)
          (x + latticeShift k) = fderiv ℝ (orderedRealDerivative is f) x := by
        calc
          fderiv ℝ (orderedRealDerivative is f) (x + latticeShift k) =
              fderiv ℝ (fun y => orderedRealDerivative is f
                (y + latticeShift k)) x := by rw [fderiv_comp_add_right]
          _ = fderiv ℝ (orderedRealDerivative is f) x := by rw [hfun]
      exact congrArg (fun L : Vec 2 →L[ℝ] ℝ => L (basisVec i)) hder

theorem AnalyticDerivativeTail.complexDirectionIter_periodic (is : List (Fin 2))
    {f : Vec 2 → ℂ} (hf : IsZdPeriodic f) :
    IsZdPeriodic (AnalyticDerivativeTail.complexDirectionIter is f) := by
  induction is with
  | nil => simpa [AnalyticDerivativeTail.complexDirectionIter] using hf
  | cons i is ih =>
      intro k x
      have hfun : (fun y : Vec 2 => AnalyticDerivativeTail.complexDirectionIter is f
          (y + intVector k)) = AnalyticDerivativeTail.complexDirectionIter is f := by
        funext y
        exact ih k y
      have hder : fderiv ℝ (AnalyticDerivativeTail.complexDirectionIter is f)
          (x + intVector k) = fderiv ℝ (AnalyticDerivativeTail.complexDirectionIter is f) x := by
        calc
          fderiv ℝ (AnalyticDerivativeTail.complexDirectionIter is f) (x + intVector k) =
              fderiv ℝ (fun y => AnalyticDerivativeTail.complexDirectionIter is f
                (y + intVector k)) x := by rw [fderiv_comp_add_right]
          _ = fderiv ℝ (AnalyticDerivativeTail.complexDirectionIter is f) x := by rw [hfun]
      change coordDeriv i (AnalyticDerivativeTail.complexDirectionIter is f) (x + intVector k) = _
      exact congrArg (fun L : Vec 2 →L[ℝ] ℂ => L (basisVec i)) hder

theorem AnalyticDerivativeTail.coordDeriv_realCast {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin 2) (x : Vec 2) :
    coordDeriv i (fun y => (f y : ℂ)) x =
      (fderiv ℝ f x (basisVec i) : ℂ) := by
  have hreal := (hf.contDiffAt (x := x)).differentiableAt (by norm_num)
  change fderiv ℝ (Complex.ofRealCLM ∘ f) x (basisVec i) = _
  rw [fderiv_comp x Complex.ofRealCLM.differentiableAt hreal]
  simp [basisVec]

theorem AnalyticDerivativeTail.complexDirectionIter_realCast (is : List (Fin 2))
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ ∞ f) :
    AnalyticDerivativeTail.complexDirectionIter is (fun x => (f x : ℂ)) =
      fun x => (orderedRealDerivative is f x : ℂ) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      have htail : AnalyticDerivativeTail.complexDirectionIter is (fun x => (f x : ℂ)) =
          fun x => (orderedRealDerivative is f x : ℂ) := ih
      rw [AnalyticDerivativeTail.complexDirectionIter, htail]
      funext x
      exact AnalyticDerivativeTail.coordDeriv_realCast
        ((AnalyticDerivativeTail.orderedRealDerivative_contDiff_top is hf).of_le (by simp)) i x

theorem AnalyticDerivativeTail.orderedRealDerivative_eq_iteratedFDeriv
    (is : List (Fin 2)) {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ ∞ f) (x : Vec 2) :
    orderedRealDerivative is f x =
      iteratedFDeriv ℝ is.length f x (fun j => basisVec (is.get j)) := by
  induction is generalizing x with
  | nil => rfl
  | cons i is ih =>
      change fderiv ℝ (orderedRealDerivative is f) x (basisVec i) = _
      change fderiv ℝ (orderedRealDerivative is f) x (basisVec i) =
        iteratedFDeriv ℝ (is.length + 1) f x
          (fun j => basisVec ((i :: is).get j))
      rw [iteratedFDeriv_succ_apply_left]
      have htail : Fin.tail
          (fun j : Fin (is.length + 1) => basisVec ((i :: is).get j)) =
          fun j => basisVec (is.get j) := by
        funext j
        change basisVec ((i :: is).get j.succ) = basisVec (is.get j)
        simp
      rw [htail]
      have hiter : ContDiff ℝ 1 (iteratedFDeriv ℝ is.length f) :=
        hf.iteratedFDeriv_right (i := is.length) (m := 1)
          (n := (⊤ : ℕ∞)) (by simp)
      have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ is.length f) x :=
        (hiter.differentiable (by norm_num)) x
      have hcontract :
          (fun y : Vec 2 => iteratedFDeriv ℝ is.length f y
            (fun j => basisVec (is.get j))) = orderedRealDerivative is f := by
        funext y
        exact (ih y).symm
      have hderiv := congrArg
        (fun q : Vec 2 → ℝ => fderiv ℝ q x (basisVec i)) hcontract
      change fderiv ℝ (orderedRealDerivative is f) x (basisVec i) = _
      have happly := fderiv_continuousMultilinear_apply_const_apply hdiff
        (fun j : Fin is.length => basisVec (is.get j)) (basisVec i)
      exact hderiv.symm.trans happly

theorem AnalyticDerivativeTail.coordDerivIter_append (is : List (Fin 2)) (i : Fin 2)
    (m : ℕ) {f : Vec 2 → ℂ} :
    coordDerivIter i m (AnalyticDerivativeTail.complexDirectionIter is f) =
      AnalyticDerivativeTail.complexDirectionIter (List.replicate m i ++ is) f := by
  induction m with
  | zero => simp [coordDerivIter]
  | succ m ih =>
      rw [coordDerivIter, ih]
      simp [AnalyticDerivativeTail.complexDirectionIter, List.replicate_succ]

theorem AnalyticDerivativeTail.factorial_add_le_pow_mul (m n : ℕ) :
    (m + n).factorial ≤ 2 ^ (m + n) * n.factorial * m.factorial := by
  have hchoose := Nat.choose_mul_factorial_mul_factorial
    (n := m + n) (k := n) (by omega)
  have hsub : m + n - n = m := by omega
  rw [hsub] at hchoose
  calc
    (m + n).factorial = (m + n).choose n * n.factorial * m.factorial :=
      hchoose.symm
    _ ≤ 2 ^ (m + n) * n.factorial * m.factorial := by
      gcongr
      exact Nat.choose_le_two_pow (m + n) n

theorem AnalyticDerivativeTail.analytic_factorial_shift
    {m n : ℕ} {R N : ℝ} (hR : 0 < R) (hN : 0 ≤ N) :
    N * ((m + n).factorial : ℝ) / R ^ (m + n) ≤
      (2 ^ n * (n.factorial : ℝ) * N / R ^ n) *
        ((m.factorial : ℝ) / (R / 2) ^ m) := by
  have hfactNat := AnalyticDerivativeTail.factorial_add_le_pow_mul m n
  have hfact : ((m + n).factorial : ℝ) ≤
      (2 : ℝ) ^ (m + n) * (n.factorial : ℝ) * (m.factorial : ℝ) := by
    exact_mod_cast hfactNat
  have hpow : (0 : ℝ) < R ^ (m + n) := pow_pos hR _
  have hscaled := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hfact hN) hpow.le
  have halg :
      N * ((2 : ℝ) ^ (m + n) * (n.factorial : ℝ) * (m.factorial : ℝ)) /
          R ^ (m + n) =
        (2 ^ n * (n.factorial : ℝ) * N / R ^ n) *
          ((m.factorial : ℝ) / (R / 2) ^ m) := by
    rw [div_pow]
    field_simp [ne_of_gt hR]
    have hpowR : R ^ n * R ^ m = R ^ (m + n) := by
      rw [← pow_add]
      congr 1
      omega
    have hpowTwo : (2 : ℝ) ^ (m + n) = 2 ^ n * 2 ^ m := by
      rw [show m + n = n + m by omega, pow_add]
    calc
      N * 2 ^ (m + n) * R ^ n * R ^ m =
          N * (2 : ℝ) ^ (m + n) * (R ^ n * R ^ m) := by ring
      _ = N * (2 ^ n * 2 ^ m) * R ^ (m + n) := by
        rw [hpowTwo, hpowR]
      _ = N * R ^ (m + n) * 2 ^ n * 2 ^ m := by ring
  calc
    N * ((m + n).factorial : ℝ) / R ^ (m + n) =
        (N * ((m + n).factorial : ℝ)) / R ^ (m + n) := by ring
    _ ≤ _ := hscaled
    _ = _ := halg

theorem AnalyticDerivativeTail.torusCharacter_line_eq_local {n : ℕ} (i : Fin (n + 1))
    (k : Fin (n + 1) → ℤ) (z : Vec n) (t : ℝ) :
    Torus.torusCharacter k (i.insertNth t z) =
      fourier (-(k i)) (t : UnitAddCircle) *
        ∏ j : Fin n, fourier (-(k (i.succAbove j)))
          (z j : UnitAddCircle) := by
  simp [Torus.torusCharacter, UnitAddTorus.mFourier,
    ContinuousMap.coe_mk, Torus.toUnitTorus, i.prod_univ_succAbove]

theorem AnalyticDerivativeTail.torusCharacter_line_hasDerivAt_local {n : ℕ}
    (i : Fin (n + 1)) (k : (Fin (n + 1) → ℤ)) (z : Vec n) (t : ℝ) :
    HasDerivAt (fun s => Torus.torusCharacter k (i.insertNth s z))
      ((-2 * Real.pi * Complex.I * (k i : ℂ)) *
        Torus.torusCharacter k (i.insertNth t z)) t := by
  let c : ℂ := ∏ j : Fin n,
    fourier (-(k (i.succAbove j))) (z j : UnitAddCircle)
  have hline : ∀ s, Torus.torusCharacter k (i.insertNth s z) =
      fourier (-(k i)) (s : UnitAddCircle) * c := by
    intro s
    simpa [c] using AnalyticDerivativeTail.torusCharacter_line_eq_local i k z s
  have h := (hasDerivAt_fourier_neg (T := 1) (k i) t).mul_const c
  convert h using 1
  · exact funext hline
  · rw [hline t]
    simp
    ring

theorem AnalyticDerivativeTail.coordDeriv_torusCharacter_local (i : Fin 2)
    (k : Fin 2 → ℤ) (x : Vec 2) :
    coordDeriv i (Torus.torusCharacter k) x =
      (-2 * Real.pi * Complex.I * (k i : ℂ)) *
        Torus.torusCharacter k x := by
  let z := i.removeNth x
  have hx : i.insertNth (x i) z = x := Fin.insertNth_self_removeNth i x
  have h₁ := ((Torus.torusCharacter_contDiff k).differentiable (by simp)
      (i.insertNth (x i) z)).hasFDerivAt.comp_hasDerivAt (x i)
      (Homogenization.hasDerivAt_insertNth i z (x i))
  have h₂ := AnalyticDerivativeTail.torusCharacter_line_hasDerivAt_local i k z (x i)
  calc
    coordDeriv i (Torus.torusCharacter k) x =
        deriv (fun t => Torus.torusCharacter k (i.insertNth t z)) (x i) := by
      rw [← hx]
      simpa [coordDeriv, Function.comp_def] using h₁.deriv.symm
    _ = (-2 * Real.pi * Complex.I * (k i : ℂ)) *
        Torus.torusCharacter k (i.insertNth (x i) z) := h₂.deriv
    _ = _ := by rw [hx]

theorem AnalyticDerivativeTail.lowProjection_coordinateDerivative
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ ∞ f)
    (hper : AVenhance.IsZ2Periodic f) (M : ℕ) (i : Fin 2) :
    (fun x => fderiv ℝ (Ergodic.lowProjection f M) x (basisVec i)) =
      Ergodic.lowProjection
        (fun x => fderiv ℝ f x (basisVec i)) M := by
  funext x
  let fC : Vec 2 → ℂ := fun y => (f y : ℂ)
  let a : (Fin 2 → ℤ) → ℂ := fun k => Torus.smoothFourierCoeff fC k
  let F : Vec 2 → ℂ := Ergodic.complexEuclideanCutoff M a
  let L : Vec 2 →L[ℝ] ℂ :=
    ∑ k ∈ Ergodic.frequencyBall M,
      a k • fderiv ℝ (Torus.torusCharacter (-k)) x
  have hfC : ContDiff ℝ ∞ fC := Complex.ofRealCLM.contDiff.comp hf
  have hfperC : IsZdPeriodic fC := by
    intro k y
    exact congrArg Complex.ofReal ((isZdPeriodic_iff_frozen f).2 hper k y)
  have hsum : HasFDerivAt F L x := by
    change HasFDerivAt
      (fun y => ∑ k ∈ Ergodic.frequencyBall M,
        a k * Torus.torusCharacter (-k) y) L x
    have hterms : ∀ k ∈ Ergodic.frequencyBall M,
        HasFDerivAt (fun y => a k * Torus.torusCharacter (-k) y)
          (a k • fderiv ℝ (Torus.torusCharacter (-k)) x) x := by
      intro k hk
      have hchar :=
        ((Torus.torusCharacter_contDiff (-k)).differentiable (by simp) x).hasFDerivAt
      simpa [smul_eq_mul] using hchar.const_mul (a k)
    have hs := HasFDerivAt.sum hterms
    have hfun : (fun y => ∑ k ∈ Ergodic.frequencyBall M,
        a k * Torus.torusCharacter (-k) y) =
      ∑ k ∈ Ergodic.frequencyBall M,
        (fun y => a k * Torus.torusCharacter (-k) y) := by
      funext y
      simp
    rw [hfun]
    simpa [L, smul_eq_mul] using hs
  have hsumCoord : fderiv ℝ F x (basisVec i) =
      ∑ k ∈ Ergodic.frequencyBall M,
        a k * coordDeriv i (Torus.torusCharacter (-k)) x := by
    rw [hsum.fderiv]
    simp [L, coordDeriv, smul_eq_mul]
  have hchar (k : Fin 2 → ℤ) :
      coordDeriv i (Torus.torusCharacter (-k)) x =
        (2 * Real.pi * Complex.I * (k i : ℂ)) *
          Torus.torusCharacter (-k) x := by
    rw [AnalyticDerivativeTail.coordDeriv_torusCharacter_local]
    simp only [Pi.neg_apply, Int.cast_neg]
    ring
  have hcoeff (k : Fin 2 → ℤ) :
      Torus.smoothFourierCoeff (coordDeriv i fC) k =
        (2 * Real.pi * Complex.I * (k i : ℂ)) * a k := by
    exact Torus.smoothFourierCoeff_coordDeriv i
      (hfC.of_le (by simp)) hfperC k
  have hcast :
      (fun y => (fderiv ℝ f y (basisVec i) : ℂ)) = coordDeriv i fC := by
    funext y
    exact (AnalyticDerivativeTail.coordDeriv_realCast (hf.of_le (by simp)) i y).symm
  have hrealDerivative :
      fderiv ℝ (Ergodic.lowProjection f M) x (basisVec i) =
        (∑ k ∈ Ergodic.frequencyBall M,
          a k * coordDeriv i (Torus.torusCharacter (-k)) x).re := by
    change fderiv ℝ (fun y => (F y).re) x (basisVec i) = _
    have heval :
        (fderiv ℝ (fun y => (F y).re) x) (basisVec i) =
          (fderiv ℝ F x (basisVec i)).re := by
      change fderiv ℝ (Complex.reCLM ∘ F) x (basisVec i) = _
      rw [fderiv_comp x Complex.reCLM.differentiableAt hsum.differentiableAt]
      simp [Complex.reCLM_apply]
    rw [heval, hsumCoord]
  calc
    fderiv ℝ (Ergodic.lowProjection f M) x (basisVec i) =
        (∑ k ∈ Ergodic.frequencyBall M,
          a k * coordDeriv i (Torus.torusCharacter (-k)) x).re := hrealDerivative
    _ = (∑ k ∈ Ergodic.frequencyBall M,
          Torus.smoothFourierCoeff (coordDeriv i fC) k *
            Torus.torusCharacter (-k) x).re := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [hchar k, hcoeff k]
      ring
    _ = Ergodic.lowProjection (fun y => fderiv ℝ f y (basisVec i)) M x := by
      rw [← hcast]
      rfl

theorem AnalyticDerivativeTail.orderedRealDerivative_lowProjection
    (is : List (Fin 2)) {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ ∞ f) (hper : AVenhance.IsZ2Periodic f) (M : ℕ) :
    orderedRealDerivative is (Ergodic.lowProjection f M) =
      Ergodic.lowProjection (orderedRealDerivative is f) M := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      have htailDiff := AnalyticDerivativeTail.orderedRealDerivative_contDiff_top is hf
      have htailPer := AnalyticDerivativeTail.orderedRealDerivative_periodic is hper
      have htail : orderedRealDerivative is (Ergodic.lowProjection f M) =
          Ergodic.lowProjection (orderedRealDerivative is f) M := ih
      funext x
      change fderiv ℝ (orderedRealDerivative is
        (Ergodic.lowProjection f M)) x (basisVec i) = _
      rw [htail]
      exact congrFun
        (AnalyticDerivativeTail.lowProjection_coordinateDerivative htailDiff htailPer M i) x

theorem AnalyticDerivativeTail.orderedRealDerivative_sub
    (is : List (Fin 2)) {f g : Vec 2 → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    orderedRealDerivative is (fun x => f x - g x) =
      fun x => orderedRealDerivative is f x - orderedRealDerivative is g x := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      have htailF := AnalyticDerivativeTail.orderedRealDerivative_contDiff_top is hf
      have htailG := AnalyticDerivativeTail.orderedRealDerivative_contDiff_top is hg
      have htail : orderedRealDerivative is (fun x => f x - g x) =
          fun x => orderedRealDerivative is f x - orderedRealDerivative is g x := ih
      funext x
      change fderiv ℝ (orderedRealDerivative is (fun x => f x - g x))
        x (basisVec i) = _
      rw [htail]
      change fderiv ℝ
          (orderedRealDerivative is f - orderedRealDerivative is g)
          x (basisVec i) = _
      rw [fderiv_sub (htailF.differentiable (by simp) x)
        (htailG.differentiable (by simp) x)]
      rfl

theorem AnalyticDerivativeTail.orderedRealDerivative_highRemainder_eq
    (is : List (Fin 2)) {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ ∞ f) (hper : AVenhance.IsZ2Periodic f) (M : ℕ) :
    orderedRealDerivative is (Ergodic.highRemainder f M) =
      Ergodic.highRemainder (orderedRealDerivative is f) M := by
  have hlow := AnalyticDerivativeTail.orderedRealDerivative_lowProjection is hf hper M
  have hsub := AnalyticDerivativeTail.orderedRealDerivative_sub is (f := f)
    (g := Ergodic.lowProjection f M) hf
    ((Ergodic.lowProjection_contDiff (f := f) M).of_le (by simp))
  funext x
  change orderedRealDerivative is
    (fun y => f y - Ergodic.lowProjection f M y) x = _
  rw [hsub, hlow]
  rfl

/-- The ordered derivative bounds imply the coordinate analytic
Fourier bounds for every fixed ordered derivative, with half the analytic
radius. The loss is explicit: order `n` costs `2^n n! R^{-n}`. -/
theorem thetaAnalytic_orderedDerivative_hasCoordinateAnalyticL2Bounds
    {g : Vec 2 → ℝ} {R : ℝ}
    (hg : ContDiff ℝ ∞ g) (hper : AVenhance.IsZ2Periodic g)
    (hθ : AVenhance.IsThetaAnalytic R g) (hR : 0 < R)
    (is : List (Fin 2)) (his : 0 < is.length) :
    HasCoordinateAnalyticL2Bounds
      (fun x => (orderedRealDerivative is g x : ℂ))
      (2 ^ is.length * (is.length.factorial : ℝ) *
        Real.sqrt (AVenhance.l2NormSq g) / R ^ is.length)
      (R / 2) := by
  let v : Vec 2 → ℂ := fun x => (orderedRealDerivative is g x : ℂ)
  let N : ℝ := Real.sqrt (AVenhance.l2NormSq g)
  have hv : ContDiff ℝ ∞ v := by
    exact Complex.ofRealCLM.contDiff.comp
        (AnalyticDerivativeTail.orderedRealDerivative_contDiff_top is hg)
  have hvper : IsZdPeriodic v := by
    intro k x
    exact congrArg Complex.ofReal (AnalyticDerivativeTail.orderedRealDerivative_periodic is hper k
        x)
  intro i m
  let js : List (Fin 2) := List.replicate m i ++ is
  have hjslen : js.length = m + is.length := by simp [js]
  have hjsPos : 1 ≤ js.length := by
    rw [hjslen]
    omega
  have hanalytic := hθ js.length hjsPos (fun j => js.get j)
  have hcomplex : coordDerivIter i m v =
      fun x => (orderedRealDerivative js g x : ℂ) := by
    have hvEq : v = AnalyticDerivativeTail.complexDirectionIter is (fun x => (g x : ℂ)) := by
      funext x
      exact congrFun (AnalyticDerivativeTail.complexDirectionIter_realCast is hg).symm x
    rw [hvEq, AnalyticDerivativeTail.coordDerivIter_append]
    exact AnalyticDerivativeTail.complexDirectionIter_realCast js hg
  have hreal : ∀ x : Vec 2,
      orderedRealDerivative js g x =
        iteratedFDeriv ℝ js.length g x (fun j => basisVec (js.get j)) := by
    intro x
    exact AnalyticDerivativeTail.orderedRealDerivative_eq_iteratedFDeriv js hg x
  have hnorm :
      (∫ x in Torus.unitCell 2, ‖coordDerivIter i m v x‖ ^ 2) =
        ∫ x in AVenhance.unitCube,
          (iteratedFDeriv ℝ js.length g x
            (fun j => basisVec (js.get j))) ^ 2 := by
    calc
      _ = ∫ x in Torus.unitCell 2,
          (iteratedFDeriv ℝ js.length g x
            (fun j => basisVec (js.get j))) ^ 2 := by
              apply setIntegral_congr_fun (Torus.measurableSet_unitCell 2)
              intro x hx
              change ‖coordDerivIter i m v x‖ ^ 2 =
                (iteratedFDeriv ℝ js.length g x
                  (fun j => basisVec (js.get j))) ^ 2
              rw [congrFun hcomplex x, hreal x]
              simp
      _ = _ := Torus.integral_unitCell_eq_unitCube _
  have hanalytic' :
      Real.sqrt (∫ x in Torus.unitCell 2,
        ‖coordDerivIter i m v x‖ ^ 2) ≤
        N * ((js.length.factorial : ℝ) / R ^ js.length) := by
    rw [hnorm]
    simpa [N, Real.sqrt_eq_rpow] using hanalytic
  have hshift := AnalyticDerivativeTail.analytic_factorial_shift (m := m) (n := is.length)
    (N := Real.sqrt (AVenhance.l2NormSq g)) hR
    (Real.sqrt_nonneg _)
  have hfinal :
      N * ((js.length.factorial : ℝ) / R ^ js.length) ≤
      (2 ^ is.length * (is.length.factorial : ℝ) * N / R ^ is.length) *
          ((m.factorial : ℝ) / (R / 2) ^ m) := by
    rw [hjslen]
    convert hshift using 1
    ring
  have hbound := hanalytic'.trans hfinal
  simpa [N, v, mul_div_assoc, Real.sqrt_eq_rpow] using hbound

/-- analyticity gives an exponential high-frequency tail after any
ordered derivative of positive order. The Euclidean cube cutoff is the same
cutoff used by `Ergodic.highRemainder`. -/
theorem thetaAnalytic_orderedDerivative_highRemainderL2_le
    {g : Vec 2 → ℝ} {R : ℝ}
    (hg : ContDiff ℝ ∞ g) (hper : AVenhance.IsZ2Periodic g)
    (hθ : AVenhance.IsThetaAnalytic R g) (hR : 0 < R)
    (is : List (Fin 2)) (his : 0 < is.length)
    (M : ℕ) (hscale : 1 ≤ (R / 2) * (M + 1 : ℝ)) :
    (∫ x in Torus.unitCell 2,
      (Ergodic.highRemainder (orderedRealDerivative is g) M x) ^ 2) ^
        (1 / 2 : ℝ) ≤
      3072 * (2 ^ is.length * (is.length.factorial : ℝ) *
        Real.sqrt (AVenhance.l2NormSq g) / R ^ is.length) *
        Real.exp (-(R / 2) * (M + 1 : ℝ) / 512) := by
  let gα : Vec 2 → ℝ := orderedRealDerivative is g
  let v : Vec 2 → ℂ := fun x => (gα x : ℂ)
  let q : Vec 2 → ℂ := fun x => (Ergodic.highRemainder gα M x : ℂ)
  have hgα : ContDiff ℝ ∞ gα := AnalyticDerivativeTail.orderedRealDerivative_contDiff_top is hg
  have hgαper : IsZ2Periodic gα := AnalyticDerivativeTail.orderedRealDerivative_periodic is hper
  have hv : ContDiff ℝ ∞ v := Complex.ofRealCLM.contDiff.comp hgα
  have hvper : IsZdPeriodic v := by
    intro k x
    exact congrArg Complex.ofReal (hgαper k x)
  have hq : ContDiff ℝ ∞ q := by
    exact Complex.ofRealCLM.contDiff.comp
      (Ergodic.highRemainder_contDiff hgα M)
  let a : (Fin 2 → ℤ) → ℂ := fun k => Torus.smoothFourierCoeff v k
  have ha : ∀ k, a (-k) = star (a k) := by
    intro k
    exact smoothFourierCoeff_real_neg k
  have hlowCoeff (k : Fin 2 → ℤ) :
      Torus.smoothFourierCoeff
        (fun x => (Ergodic.lowProjection gα M x : ℂ)) k =
        if k ∈ frequencyBall M then a k else 0 := by
    exact smoothFourierCoeff_euclideanCutoff M a ha k
  have hqcoeff (k : Fin 2 → ℤ) :
      Torus.smoothFourierCoeff q k =
        if ‖k‖ ≤ (M : ℝ) then 0 else Torus.smoothFourierCoeff v k := by
    have hcast : q = fun x => v x - (Ergodic.lowProjection gα M x : ℂ) := by
      funext x
      simp [q, v, gα, Ergodic.highRemainder]
    rw [hcast]
    have hsub := smoothFourierCoeff_sub
      (f := v)
      (g := fun x => (Ergodic.lowProjection gα M x : ℂ))
      hv.continuous
      ((Complex.ofRealCLM.contDiff.comp
        (Ergodic.lowProjection_contDiff M)).continuous) k
    rw [hsub, hlowCoeff]
    by_cases hk : ‖k‖ ≤ (M : ℝ)
    · have hball : k ∈ frequencyBall M := mem_frequencyBall.mpr hk
      simp [a, hk, hball]
    · have hball : k ∉ frequencyBall M := by
        simpa [mem_frequencyBall] using hk
      simp [a, hk, hball]
  have hderiv := thetaAnalytic_orderedDerivative_hasCoordinateAnalyticL2Bounds
    hg hper hθ hR is his
  let Cf : ℝ :=
    2 ^ is.length * (is.length.factorial : ℝ) *
      Real.sqrt (AVenhance.l2NormSq g) / R ^ is.length
  have htail := fourierTailL2_le_of_coordinateAnalyticL2Bounds
    (d := 2) (hd := by norm_num) hv hvper Cf (R / 2)
    (by dsimp [Cf]; positivity) (by positivity) hderiv M hscale hq hqcoeff
  have hnorm :
      (∫ x in Torus.unitCell 2, ‖q x‖ ^ 2) =
        ∫ x in Torus.unitCell 2,
          (Ergodic.highRemainder gα M x) ^ 2 := by
    apply setIntegral_congr_fun (Torus.measurableSet_unitCell 2)
    intro x hx
    simp [q]
  rw [hnorm] at htail
  have htail' :
      (∫ x in Torus.unitCell 2, (Ergodic.highRemainder gα M x) ^ 2) ^
          (1 / 2 : ℝ) ≤
        3 * 1024 * Cf *
          Real.exp (-(R / 2) * (M + 1 : ℝ) / 512) := by
    calc
      _ ≤ 3 * Cf * (1024 *
          Real.exp (-(R / 2) * (M + 1 : ℝ) / 512)) := by
            simpa [show (2 : ℝ) + 1 = 3 by norm_num,
              mul_assoc, mul_left_comm, mul_comm] using htail
      _ = _ := by ring
  calc
    _ ≤ 3 * 1024 * Cf *
        Real.exp (-(R / 2) * (M + 1 : ℝ) / 512) := by
          simpa [gα] using htail'
    _ = _ := by
      dsimp [Cf]
      ring

/-- The ordered derivative commutes with the finite Fourier cutoff, so the
previous estimate is the tail of the derivative of `(1 - P_M) g` itself. -/
theorem thetaAnalytic_derivative_highFrequencyRemainderL2_le
    {g : Vec 2 → ℝ} {R : ℝ}
    (hg : ContDiff ℝ ∞ g) (hper : AVenhance.IsZ2Periodic g)
    (hθ : AVenhance.IsThetaAnalytic R g) (hR : 0 < R)
    (is : List (Fin 2)) (his : 0 < is.length)
    (M : ℕ) (hscale : 1 ≤ (R / 2) * (M + 1 : ℝ)) :
    (∫ x in Torus.unitCell 2,
      (orderedRealDerivative is (Ergodic.highRemainder g M) x) ^ 2) ^
        (1 / 2 : ℝ) ≤
      3072 * (2 ^ is.length * (is.length.factorial : ℝ) *
        Real.sqrt (AVenhance.l2NormSq g) / R ^ is.length) *
        Real.exp (-(R / 2) * (M + 1 : ℝ) / 512) := by
  have hcommute := AnalyticDerivativeTail.orderedRealDerivative_highRemainder_eq is hg hper M
  have hnorm :
      (∫ x in Torus.unitCell 2,
        (orderedRealDerivative is (Ergodic.highRemainder g M) x) ^ 2) =
      ∫ x in Torus.unitCell 2,
        (Ergodic.highRemainder (orderedRealDerivative is g) M x) ^ 2 := by
    apply setIntegral_congr_fun (Torus.measurableSet_unitCell 2)
    intro x hx
    change orderedRealDerivative is (Ergodic.highRemainder g M) x ^ 2 =
      (Ergodic.highRemainder (orderedRealDerivative is g) M x) ^ 2
    rw [congrFun hcommute x]
  rw [hnorm]
  exact thetaAnalytic_orderedDerivative_highRemainderL2_le
    hg hper hθ hR is his M hscale

end AVenhance.Infra.Section5.RelativeError

end
