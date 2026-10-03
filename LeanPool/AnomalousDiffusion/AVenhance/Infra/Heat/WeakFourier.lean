/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Heat.WeakBridge
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Heat.PeriodicCutoff

/-! Fourier coefficients of periodic weak gradients. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open AVenhance.Infra.Torus

namespace AVenhance.Infra.Heat

/-- Real part of a periodic character used in the weak heat equation. -/
def WeakFourier.heatWeakRealCharacter (k : Frequency) (x : Vec 2) : ℝ :=
  Complex.reCLM (torusCharacter k x)

/-- Imaginary part of a periodic character used in the weak heat equation. -/
def WeakFourier.heatWeakImagCharacter (k : Frequency) (x : Vec 2) : ℝ :=
  Complex.imCLM (torusCharacter k x)

theorem WeakFourier.heatWeak_torusCharacter_line_eq {n : ℕ} (i : Fin (n + 1))
    (k : Fin (n + 1) → ℤ) (z : Vec n) (t : ℝ) :
    torusCharacter k (i.insertNth t z) =
      fourier (-(k i)) (t : UnitAddCircle) *
        ∏ j : Fin n, fourier (-(k (i.succAbove j))) (z j : UnitAddCircle) := by
  simp [torusCharacter, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    toUnitTorus, i.prod_univ_succAbove]

theorem WeakFourier.heatWeak_torusCharacter_line_hasDerivAt {n : ℕ}
    (i : Fin (n + 1)) (k : Fin (n + 1) → ℤ) (z : Vec n) (t : ℝ) :
    HasDerivAt (fun s => torusCharacter k (i.insertNth s z))
      ((-2 * Real.pi * Complex.I * (k i : ℂ)) *
        torusCharacter k (i.insertNth t z)) t := by
  let c : ℂ := ∏ j : Fin n,
    fourier (-(k (i.succAbove j))) (z j : UnitAddCircle)
  have hline : ∀ s, torusCharacter k (i.insertNth s z) =
      fourier (-(k i)) (s : UnitAddCircle) * c := by
    intro s
    simpa [c] using WeakFourier.heatWeak_torusCharacter_line_eq i k z s
  have h := (hasDerivAt_fourier_neg (T := 1) (k i) t).mul_const c
  convert h using 1
  · exact funext hline
  · rw [hline t]
    simp
    ring

theorem WeakFourier.heatWeak_coordDeriv_torusCharacter (i : Fin 2)
    (k : Frequency) (x : Vec 2) :
    coordDeriv i (torusCharacter k) x =
      (-2 * Real.pi * Complex.I * (k i : ℂ)) * torusCharacter k x := by
  let z := i.removeNth x
  have hx : i.insertNth (x i) z = x := Fin.insertNth_self_removeNth i x
  have h₁ :=
    ((torusCharacter_contDiff k).differentiable (by simp)
      (i.insertNth (x i) z)).hasFDerivAt.comp_hasDerivAt (x i)
      (Homogenization.hasDerivAt_insertNth i z (x i))
  have h₂ := WeakFourier.heatWeak_torusCharacter_line_hasDerivAt i k z (x i)
  calc
    coordDeriv i (torusCharacter k) x =
        deriv (fun t => torusCharacter k (i.insertNth t z)) (x i) := by
      rw [← hx]
      simpa [coordDeriv, Function.comp_def] using h₁.deriv.symm
    _ = (-2 * Real.pi * Complex.I * (k i : ℂ)) *
        torusCharacter k (i.insertNth (x i) z) := h₂.deriv
    _ = (-2 * Real.pi * Complex.I * (k i : ℂ)) * torusCharacter k x := by rw [hx]

theorem WeakFourier.heatWeak_coordDeriv_realCharacter (i : Fin 2)
    (k : Frequency) (x : Vec 2) :
    fderiv ℝ (WeakFourier.heatWeakRealCharacter k) x (basisVec i) =
      ((-2 * Real.pi * Complex.I * (k i : ℂ)) * torusCharacter k x).re := by
  have hchar : DifferentiableAt ℝ (torusCharacter k) x :=
    (ContDiff.contDiffAt (x := x) (torusCharacter_contDiff k)).differentiableAt
      (by simp)
  have hre : DifferentiableAt ℝ Complex.reCLM (torusCharacter k x) :=
    Complex.reCLM.differentiableAt
  have hlinear : fderiv ℝ Complex.reCLM (torusCharacter k x) = Complex.reCLM :=
    Complex.reCLM.hasFDerivAt.fderiv
  calc
    fderiv ℝ (WeakFourier.heatWeakRealCharacter k) x (basisVec i) =
        (fderiv ℝ Complex.reCLM (torusCharacter k x) ∘SL
          fderiv ℝ (torusCharacter k) x) (basisVec i) := by
      change fderiv ℝ (Complex.reCLM ∘ torusCharacter k) x (basisVec i) = _
      rw [fderiv_comp x hre hchar]
    _ = ((-2 * Real.pi * Complex.I * (k i : ℂ)) * torusCharacter k x).re := by
      rw [hlinear]
      change (coordDeriv i (torusCharacter k) x).re = _
      rw [WeakFourier.heatWeak_coordDeriv_torusCharacter]

theorem WeakFourier.heatWeak_coordDeriv_imagCharacter (i : Fin 2)
    (k : Frequency) (x : Vec 2) :
    fderiv ℝ (WeakFourier.heatWeakImagCharacter k) x (basisVec i) =
      ((-2 * Real.pi * Complex.I * (k i : ℂ)) * torusCharacter k x).im := by
  have hchar : DifferentiableAt ℝ (torusCharacter k) x :=
    (ContDiff.contDiffAt (x := x) (torusCharacter_contDiff k)).differentiableAt
      (by simp)
  have him : DifferentiableAt ℝ Complex.imCLM (torusCharacter k x) :=
    Complex.imCLM.differentiableAt
  have hlinear : fderiv ℝ Complex.imCLM (torusCharacter k x) = Complex.imCLM :=
    Complex.imCLM.hasFDerivAt.fderiv
  calc
    fderiv ℝ (WeakFourier.heatWeakImagCharacter k) x (basisVec i) =
        (fderiv ℝ Complex.imCLM (torusCharacter k x) ∘SL
          fderiv ℝ (torusCharacter k) x) (basisVec i) := by
      change fderiv ℝ (Complex.imCLM ∘ torusCharacter k) x (basisVec i) = _
      rw [fderiv_comp x him hchar]
    _ = ((-2 * Real.pi * Complex.I * (k i : ℂ)) * torusCharacter k x).im := by
      rw [hlinear]
      change (coordDeriv i (torusCharacter k) x).im = _
      rw [WeakFourier.heatWeak_coordDeriv_torusCharacter]

theorem WeakFourier.heatWeak_realCharacter_contDiff (k : Frequency) :
    ContDiff ℝ (⊤ : ℕ∞) (WeakFourier.heatWeakRealCharacter k) := by
  change ContDiff ℝ (⊤ : ℕ∞) (Complex.reCLM ∘ torusCharacter k)
  have hRe : ContDiff ℝ (⊤ : ℕ∞) Complex.reCLM :=
    Complex.reCLM.contDiff.of_le le_top
  have hChar : ContDiff ℝ (⊤ : ℕ∞) (torusCharacter k) :=
    (torusCharacter_contDiff k).of_le le_top
  exact hRe.comp hChar

theorem WeakFourier.heatWeak_imagCharacter_contDiff (k : Frequency) :
    ContDiff ℝ (⊤ : ℕ∞) (WeakFourier.heatWeakImagCharacter k) := by
  change ContDiff ℝ (⊤ : ℕ∞) (Complex.imCLM ∘ torusCharacter k)
  have hIm : ContDiff ℝ (⊤ : ℕ∞) Complex.imCLM :=
    Complex.imCLM.contDiff.of_le le_top
  have hChar : ContDiff ℝ (⊤ : ℕ∞) (torusCharacter k) :=
    (torusCharacter_contDiff k).of_le le_top
  exact hIm.comp hChar

theorem WeakFourier.heatWeak_realCharacter_periodic (k : Frequency) :
    IsZdPeriodic (WeakFourier.heatWeakRealCharacter k) := by
  intro n x
  exact congrArg Complex.reCLM (torusCharacter_periodic k n x)

theorem WeakFourier.heatWeak_imagCharacter_periodic (k : Frequency) :
    IsZdPeriodic (WeakFourier.heatWeakImagCharacter k) := by
  intro n x
  exact congrArg Complex.imCLM (torusCharacter_periodic k n x)

theorem WeakFourier.heatWeak_realCharacterDeriv_periodic (i : Fin 2)
    (k : Frequency) :
    IsZdPeriodic (fun x : Vec 2 =>
      fderiv ℝ (WeakFourier.heatWeakRealCharacter k) x (basisVec i)) := by
  intro n x
  calc
    fderiv ℝ (WeakFourier.heatWeakRealCharacter k) (x + intVector n) (basisVec i) =
        ((-2 * Real.pi * Complex.I * (k i : ℂ)) *
          torusCharacter k (x + intVector n)).re :=
      WeakFourier.heatWeak_coordDeriv_realCharacter i k (x + intVector n)
    _ = ((-2 * Real.pi * Complex.I * (k i : ℂ)) * torusCharacter k x).re := by
      rw [torusCharacter_periodic k n x]
    _ = fderiv ℝ (WeakFourier.heatWeakRealCharacter k) x (basisVec i) :=
      (WeakFourier.heatWeak_coordDeriv_realCharacter i k x).symm

theorem WeakFourier.heatWeak_imagCharacterDeriv_periodic (i : Fin 2)
    (k : Frequency) :
    IsZdPeriodic (fun x : Vec 2 =>
      fderiv ℝ (WeakFourier.heatWeakImagCharacter k) x (basisVec i)) := by
  intro n x
  calc
    fderiv ℝ (WeakFourier.heatWeakImagCharacter k) (x + intVector n) (basisVec i) =
        ((-2 * Real.pi * Complex.I * (k i : ℂ)) *
          torusCharacter k (x + intVector n)).im :=
      WeakFourier.heatWeak_coordDeriv_imagCharacter i k (x + intVector n)
    _ = ((-2 * Real.pi * Complex.I * (k i : ℂ)) * torusCharacter k x).im := by
      rw [torusCharacter_periodic k n x]
    _ = fderiv ℝ (WeakFourier.heatWeakImagCharacter k) x (basisVec i) :=
      (WeakFourier.heatWeak_coordDeriv_imagCharacter i k x).symm

/-- Real periodic character localized by the compactly supported heat cutoff. -/
def WeakFourier.heatWeakRealTest (k : Frequency) : Vec 2 → ℝ :=
  fun x => heatPeriodicCutoff2 x * WeakFourier.heatWeakRealCharacter k x

/-- Imaginary periodic character localized by the compactly supported heat cutoff. -/
def WeakFourier.heatWeakImagTest (k : Frequency) : Vec 2 → ℝ :=
  fun x => heatPeriodicCutoff2 x * WeakFourier.heatWeakImagCharacter k x

theorem WeakFourier.heatWeak_realTest_contDiff (k : Frequency) :
    ContDiff ℝ (⊤ : ℕ∞) (WeakFourier.heatWeakRealTest k) := by
  change ContDiff ℝ (⊤ : ℕ∞)
    (heatPeriodicCutoff2 * WeakFourier.heatWeakRealCharacter k)
  exact heatPeriodicCutoff2_contDiff.mul (WeakFourier.heatWeak_realCharacter_contDiff k)

theorem WeakFourier.heatWeak_imagTest_contDiff (k : Frequency) :
    ContDiff ℝ (⊤ : ℕ∞) (WeakFourier.heatWeakImagTest k) := by
  change ContDiff ℝ (⊤ : ℕ∞)
    (heatPeriodicCutoff2 * WeakFourier.heatWeakImagCharacter k)
  exact heatPeriodicCutoff2_contDiff.mul (WeakFourier.heatWeak_imagCharacter_contDiff k)

theorem WeakFourier.heatWeak_realTest_hasCompactSupport (k : Frequency) :
    HasCompactSupport (WeakFourier.heatWeakRealTest k) := by
  change HasCompactSupport (heatPeriodicCutoff2 * WeakFourier.heatWeakRealCharacter k)
  exact heatPeriodicCutoff2_hasCompactSupport.mul_right

theorem WeakFourier.heatWeak_imagTest_hasCompactSupport (k : Frequency) :
    HasCompactSupport (WeakFourier.heatWeakImagTest k) := by
  change HasCompactSupport (heatPeriodicCutoff2 * WeakFourier.heatWeakImagCharacter k)
  exact heatPeriodicCutoff2_hasCompactSupport.mul_right

theorem WeakFourier.fderiv_heatWeakRealTest (i : Fin 2) (k : Frequency)
    (x : Vec 2) :
    fderiv ℝ (WeakFourier.heatWeakRealTest k) x (basisVec i) =
      heatPeriodicCutoff2 x *
          fderiv ℝ (WeakFourier.heatWeakRealCharacter k) x (basisVec i) +
        WeakFourier.heatWeakRealCharacter k x *
          fderiv ℝ heatPeriodicCutoff2 x (basisVec i) := by
  have hchi : DifferentiableAt ℝ heatPeriodicCutoff2 x :=
    (ContDiff.contDiffAt (x := x) heatPeriodicCutoff2_contDiff).differentiableAt
      (by simp)
  have hchar : DifferentiableAt ℝ (WeakFourier.heatWeakRealCharacter k) x :=
    (ContDiff.contDiffAt (x := x) (WeakFourier.heatWeak_realCharacter_contDiff k)).differentiableAt
      (by simp)
  change fderiv ℝ (heatPeriodicCutoff2 * WeakFourier.heatWeakRealCharacter k) x
    (basisVec i) = _
  rw [fderiv_mul hchi hchar]
  simp [smul_eq_mul]

theorem WeakFourier.fderiv_heatWeakImagTest (i : Fin 2) (k : Frequency)
    (x : Vec 2) :
    fderiv ℝ (WeakFourier.heatWeakImagTest k) x (basisVec i) =
      heatPeriodicCutoff2 x *
          fderiv ℝ (WeakFourier.heatWeakImagCharacter k) x (basisVec i) +
        WeakFourier.heatWeakImagCharacter k x *
          fderiv ℝ heatPeriodicCutoff2 x (basisVec i) := by
  have hchi : DifferentiableAt ℝ heatPeriodicCutoff2 x :=
    (ContDiff.contDiffAt (x := x) heatPeriodicCutoff2_contDiff).differentiableAt
      (by simp)
  have hchar : DifferentiableAt ℝ (WeakFourier.heatWeakImagCharacter k) x :=
    (ContDiff.contDiffAt (x := x) (WeakFourier.heatWeak_imagCharacter_contDiff k)).differentiableAt
      (by simp)
  change fderiv ℝ (heatPeriodicCutoff2 * WeakFourier.heatWeakImagCharacter k) x
    (basisVec i) = _
  rw [fderiv_mul hchi hchar]
  simp [smul_eq_mul]

theorem WeakFourier.heatWeak_realTestDeriv_support_subset_tiles (i : Fin 2)
    (k : Frequency) :
    Function.support (fun x : Vec 2 => fderiv ℝ (WeakFourier.heatWeakRealTest k) x
      (basisVec i)) ⊆ ⋃ b : Bool × Bool, heatPeriodicTile b := by
  intro x hx
  simp only [Function.mem_support] at hx
  by_contra hnot
  have hχ : heatPeriodicCutoff2 x = 0 := by
    by_contra hχ
    have hs : x ∈ Function.support heatPeriodicCutoff2 :=
      Function.mem_support.mpr hχ
    exact hnot (heatPeriodicCutoff2_support_subset_tiles hs)
  have hDχ : fderiv ℝ heatPeriodicCutoff2 x (basisVec i) = 0 := by
    by_contra hDχ
    have hs : x ∈ Function.support (fun y : Vec 2 =>
        fderiv ℝ heatPeriodicCutoff2 y (basisVec i)) :=
      Function.mem_support.mpr hDχ
    exact hnot (heatPeriodicCutoff2_coordDeriv_support_subset_tiles i hs)
  exact hx (by rw [WeakFourier.fderiv_heatWeakRealTest, hχ, hDχ]; simp)

theorem WeakFourier.heatWeak_imagTestDeriv_support_subset_tiles (i : Fin 2)
    (k : Frequency) :
    Function.support (fun x : Vec 2 => fderiv ℝ (WeakFourier.heatWeakImagTest k) x
      (basisVec i)) ⊆ ⋃ b : Bool × Bool, heatPeriodicTile b := by
  intro x hx
  simp only [Function.mem_support] at hx
  by_contra hnot
  have hχ : heatPeriodicCutoff2 x = 0 := by
    by_contra hχ
    have hs : x ∈ Function.support heatPeriodicCutoff2 :=
      Function.mem_support.mpr hχ
    exact hnot (heatPeriodicCutoff2_support_subset_tiles hs)
  have hDχ : fderiv ℝ heatPeriodicCutoff2 x (basisVec i) = 0 := by
    by_contra hDχ
    have hs : x ∈ Function.support (fun y : Vec 2 =>
        fderiv ℝ heatPeriodicCutoff2 y (basisVec i)) :=
      Function.mem_support.mpr hDχ
    exact hnot (heatPeriodicCutoff2_coordDeriv_support_subset_tiles i hs)
  exact hx (by rw [WeakFourier.fderiv_heatWeakImagTest, hχ, hDχ]; simp)

theorem WeakFourier.heatWeak_realTest_periodization (k : Frequency)
    {x : Vec 2} (hx : x ∈ unitCell 2) :
    ∑ b : Bool × Bool,
      WeakFourier.heatWeakRealTest k (x + heatPeriodicTileStart b) =
        WeakFourier.heatWeakRealCharacter k x := by
  have hχ := sum_heatPeriodicCutoff2_translates hx
  have hper : ∀ b : Bool × Bool,
      WeakFourier.heatWeakRealCharacter k (x + heatPeriodicTileStart b) =
        WeakFourier.heatWeakRealCharacter k x := by
    intro b
    simpa [heatPeriodicTileStart] using
      WeakFourier.heatWeak_realCharacter_periodic k (heatPeriodicTileShift b) x
  simp only [WeakFourier.heatWeakRealTest]
  calc
    ∑ b : Bool × Bool,
        heatPeriodicCutoff2 (x + heatPeriodicTileStart b) *
          WeakFourier.heatWeakRealCharacter k (x + heatPeriodicTileStart b) =
      ∑ b : Bool × Bool,
        heatPeriodicCutoff2 (x + heatPeriodicTileStart b) *
          WeakFourier.heatWeakRealCharacter k x := by
            apply Finset.sum_congr rfl
            intro b hb
            rw [hper b]
    _ = (∑ b : Bool × Bool,
        heatPeriodicCutoff2 (x + heatPeriodicTileStart b)) *
          WeakFourier.heatWeakRealCharacter k x := by rw [← Finset.sum_mul]
    _ = WeakFourier.heatWeakRealCharacter k x := by
      have hχ' :
          ∑ b : Bool × Bool,
            heatPeriodicCutoff2 (x + heatPeriodicTileStart b) = 1 := by
        simpa [heatPeriodicTileStart] using hχ
      rw [hχ', one_mul]

theorem WeakFourier.heatWeak_imagTest_periodization (k : Frequency)
    {x : Vec 2} (hx : x ∈ unitCell 2) :
    ∑ b : Bool × Bool,
      WeakFourier.heatWeakImagTest k (x + heatPeriodicTileStart b) =
        WeakFourier.heatWeakImagCharacter k x := by
  have hχ := sum_heatPeriodicCutoff2_translates hx
  have hper : ∀ b : Bool × Bool,
      WeakFourier.heatWeakImagCharacter k (x + heatPeriodicTileStart b) =
        WeakFourier.heatWeakImagCharacter k x := by
    intro b
    simpa [heatPeriodicTileStart] using
      WeakFourier.heatWeak_imagCharacter_periodic k (heatPeriodicTileShift b) x
  simp only [WeakFourier.heatWeakImagTest]
  calc
    ∑ b : Bool × Bool,
        heatPeriodicCutoff2 (x + heatPeriodicTileStart b) *
          WeakFourier.heatWeakImagCharacter k (x + heatPeriodicTileStart b) =
      ∑ b : Bool × Bool,
        heatPeriodicCutoff2 (x + heatPeriodicTileStart b) *
          WeakFourier.heatWeakImagCharacter k x := by
            apply Finset.sum_congr rfl
            intro b hb
            rw [hper b]
    _ = (∑ b : Bool × Bool,
        heatPeriodicCutoff2 (x + heatPeriodicTileStart b)) *
          WeakFourier.heatWeakImagCharacter k x := by rw [← Finset.sum_mul]
    _ = WeakFourier.heatWeakImagCharacter k x := by
      have hχ' :
          ∑ b : Bool × Bool,
            heatPeriodicCutoff2 (x + heatPeriodicTileStart b) = 1 := by
        simpa [heatPeriodicTileStart] using hχ
      rw [hχ', one_mul]

theorem WeakFourier.heatWeak_realTestDeriv_periodization (i : Fin 2)
    (k : Frequency) {x : Vec 2} (hx : x ∈ unitCell 2) :
    ∑ b : Bool × Bool,
      fderiv ℝ (WeakFourier.heatWeakRealTest k) (x + heatPeriodicTileStart b)
        (basisVec i) =
      fderiv ℝ (WeakFourier.heatWeakRealCharacter k) x (basisVec i) := by
  have hχ0 := sum_heatPeriodicCutoff2_translates hx
  have hDχ0 := sum_heatPeriodicCutoff2_coordDeriv_translates i hx
  have hχ : ∑ b : Bool × Bool,
      heatPeriodicCutoff2 (x + heatPeriodicTileStart b) = 1 := by
    simpa [heatPeriodicTileStart] using hχ0
  have hDχ : ∑ b : Bool × Bool,
      fderiv ℝ heatPeriodicCutoff2 (x + heatPeriodicTileStart b)
        (basisVec i) = 0 := by
    simpa [heatPeriodicTileStart] using hDχ0
  have hchar : ∀ b : Bool × Bool,
      WeakFourier.heatWeakRealCharacter k (x + heatPeriodicTileStart b) =
        WeakFourier.heatWeakRealCharacter k x := by
    intro b
    simpa [heatPeriodicTileStart] using
      WeakFourier.heatWeak_realCharacter_periodic k (heatPeriodicTileShift b) x
  have hderiv : ∀ b : Bool × Bool,
      fderiv ℝ (WeakFourier.heatWeakRealCharacter k) (x + heatPeriodicTileStart b)
        (basisVec i) = fderiv ℝ (WeakFourier.heatWeakRealCharacter k) x (basisVec i) := by
    intro b
    simpa [heatPeriodicTileStart] using
      WeakFourier.heatWeak_realCharacterDeriv_periodic i k (heatPeriodicTileShift b) x
  have hterms : ∀ b : Bool × Bool,
      heatPeriodicCutoff2 (x + heatPeriodicTileStart b) *
          fderiv ℝ (WeakFourier.heatWeakRealCharacter k)
            (x + heatPeriodicTileStart b) (basisVec i) +
        WeakFourier.heatWeakRealCharacter k (x + heatPeriodicTileStart b) *
          fderiv ℝ heatPeriodicCutoff2 (x + heatPeriodicTileStart b)
            (basisVec i) =
        heatPeriodicCutoff2 (x + heatPeriodicTileStart b) *
            fderiv ℝ (WeakFourier.heatWeakRealCharacter k) x (basisVec i) +
          WeakFourier.heatWeakRealCharacter k x *
            fderiv ℝ heatPeriodicCutoff2 (x + heatPeriodicTileStart b)
              (basisVec i) := by
    intro b
    rw [hderiv b, hchar b]
  calc
    (∑ b : Bool × Bool,
        fderiv ℝ (WeakFourier.heatWeakRealTest k) (x + heatPeriodicTileStart b)
          (basisVec i)) =
      ∑ b : Bool × Bool,
        (heatPeriodicCutoff2 (x + heatPeriodicTileStart b) *
            fderiv ℝ (WeakFourier.heatWeakRealCharacter k)
              (x + heatPeriodicTileStart b) (basisVec i) +
          WeakFourier.heatWeakRealCharacter k (x + heatPeriodicTileStart b) *
            fderiv ℝ heatPeriodicCutoff2 (x + heatPeriodicTileStart b)
              (basisVec i)) := by
      apply Finset.sum_congr rfl
      intro b hb
      exact WeakFourier.fderiv_heatWeakRealTest i k (x + heatPeriodicTileStart b)
    _ = ∑ b : Bool × Bool,
        (heatPeriodicCutoff2 (x + heatPeriodicTileStart b) *
            fderiv ℝ (WeakFourier.heatWeakRealCharacter k) x (basisVec i) +
          WeakFourier.heatWeakRealCharacter k x *
            fderiv ℝ heatPeriodicCutoff2 (x + heatPeriodicTileStart b)
              (basisVec i)) := by
      apply Finset.sum_congr rfl
      intro b hb
      exact hterms b
    _ = (∑ b : Bool × Bool,
          heatPeriodicCutoff2 (x + heatPeriodicTileStart b)) *
          fderiv ℝ (WeakFourier.heatWeakRealCharacter k) x (basisVec i) +
        WeakFourier.heatWeakRealCharacter k x *
          (∑ b : Bool × Bool,
            fderiv ℝ heatPeriodicCutoff2
              (x + heatPeriodicTileStart b) (basisVec i)) := by
      rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    _ = fderiv ℝ (WeakFourier.heatWeakRealCharacter k) x (basisVec i) := by
      rw [hχ, hDχ]
      ring

theorem WeakFourier.heatWeak_imagTestDeriv_periodization (i : Fin 2)
    (k : Frequency) {x : Vec 2} (hx : x ∈ unitCell 2) :
    ∑ b : Bool × Bool,
      fderiv ℝ (WeakFourier.heatWeakImagTest k) (x + heatPeriodicTileStart b)
        (basisVec i) =
      fderiv ℝ (WeakFourier.heatWeakImagCharacter k) x (basisVec i) := by
  have hχ0 := sum_heatPeriodicCutoff2_translates hx
  have hDχ0 := sum_heatPeriodicCutoff2_coordDeriv_translates i hx
  have hχ : ∑ b : Bool × Bool,
      heatPeriodicCutoff2 (x + heatPeriodicTileStart b) = 1 := by
    simpa [heatPeriodicTileStart] using hχ0
  have hDχ : ∑ b : Bool × Bool,
      fderiv ℝ heatPeriodicCutoff2 (x + heatPeriodicTileStart b)
        (basisVec i) = 0 := by
    simpa [heatPeriodicTileStart] using hDχ0
  have hchar : ∀ b : Bool × Bool,
      WeakFourier.heatWeakImagCharacter k (x + heatPeriodicTileStart b) =
        WeakFourier.heatWeakImagCharacter k x := by
    intro b
    simpa [heatPeriodicTileStart] using
      WeakFourier.heatWeak_imagCharacter_periodic k (heatPeriodicTileShift b) x
  have hderiv : ∀ b : Bool × Bool,
      fderiv ℝ (WeakFourier.heatWeakImagCharacter k) (x + heatPeriodicTileStart b)
        (basisVec i) = fderiv ℝ (WeakFourier.heatWeakImagCharacter k) x (basisVec i) := by
    intro b
    simpa [heatPeriodicTileStart] using
      WeakFourier.heatWeak_imagCharacterDeriv_periodic i k (heatPeriodicTileShift b) x
  have hterms : ∀ b : Bool × Bool,
      heatPeriodicCutoff2 (x + heatPeriodicTileStart b) *
          fderiv ℝ (WeakFourier.heatWeakImagCharacter k)
            (x + heatPeriodicTileStart b) (basisVec i) +
        WeakFourier.heatWeakImagCharacter k (x + heatPeriodicTileStart b) *
          fderiv ℝ heatPeriodicCutoff2 (x + heatPeriodicTileStart b)
            (basisVec i) =
        heatPeriodicCutoff2 (x + heatPeriodicTileStart b) *
            fderiv ℝ (WeakFourier.heatWeakImagCharacter k) x (basisVec i) +
          WeakFourier.heatWeakImagCharacter k x *
            fderiv ℝ heatPeriodicCutoff2 (x + heatPeriodicTileStart b)
              (basisVec i) := by
    intro b
    rw [hderiv b, hchar b]
  calc
    (∑ b : Bool × Bool,
        fderiv ℝ (WeakFourier.heatWeakImagTest k) (x + heatPeriodicTileStart b)
          (basisVec i)) =
      ∑ b : Bool × Bool,
        (heatPeriodicCutoff2 (x + heatPeriodicTileStart b) *
            fderiv ℝ (WeakFourier.heatWeakImagCharacter k)
              (x + heatPeriodicTileStart b) (basisVec i) +
          WeakFourier.heatWeakImagCharacter k (x + heatPeriodicTileStart b) *
            fderiv ℝ heatPeriodicCutoff2 (x + heatPeriodicTileStart b)
              (basisVec i)) := by
      apply Finset.sum_congr rfl
      intro b hb
      exact WeakFourier.fderiv_heatWeakImagTest i k (x + heatPeriodicTileStart b)
    _ = ∑ b : Bool × Bool,
        (heatPeriodicCutoff2 (x + heatPeriodicTileStart b) *
            fderiv ℝ (WeakFourier.heatWeakImagCharacter k) x (basisVec i) +
          WeakFourier.heatWeakImagCharacter k x *
            fderiv ℝ heatPeriodicCutoff2 (x + heatPeriodicTileStart b)
              (basisVec i)) := by
      apply Finset.sum_congr rfl
      intro b hb
      exact hterms b
    _ = (∑ b : Bool × Bool,
          heatPeriodicCutoff2 (x + heatPeriodicTileStart b)) *
          fderiv ℝ (WeakFourier.heatWeakImagCharacter k) x (basisVec i) +
        WeakFourier.heatWeakImagCharacter k x *
          (∑ b : Bool × Bool,
            fderiv ℝ heatPeriodicCutoff2
              (x + heatPeriodicTileStart b) (basisVec i)) := by
      rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    _ = fderiv ℝ (WeakFourier.heatWeakImagCharacter k) x (basisVec i) := by
      rw [hχ, hDχ]
      ring

theorem WeakFourier.heatWeak_realTest_support_subset_tiles (k : Frequency) :
    Function.support (WeakFourier.heatWeakRealTest k) ⊆
      ⋃ b : Bool × Bool, heatPeriodicTile b := by
  intro x hx
  simp only [Function.mem_support] at hx
  have hχ : heatPeriodicCutoff2 x ≠ 0 := by
    intro hχ
    apply hx
    simp [WeakFourier.heatWeakRealTest, hχ]
  exact heatPeriodicCutoff2_support_subset_tiles
    (Function.mem_support.mpr hχ)

theorem WeakFourier.heatWeak_imagTest_support_subset_tiles (k : Frequency) :
    Function.support (WeakFourier.heatWeakImagTest k) ⊆
      ⋃ b : Bool × Bool, heatPeriodicTile b := by
  intro x hx
  simp only [Function.mem_support] at hx
  have hχ : heatPeriodicCutoff2 x ≠ 0 := by
    intro hχ
    apply hx
    simp [WeakFourier.heatWeakImagTest, hχ]
  exact heatPeriodicCutoff2_support_subset_tiles
    (Function.mem_support.mpr hχ)

theorem WeakFourier.heatWeak_continuous_fderiv_apply {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) :
    Continuous (fun x => fderiv ℝ f x (basisVec i)) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  exact (hf1.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem WeakFourier.heatWeak_realTestDeriv_continuous (i : Fin 2)
    (k : Frequency) :
    Continuous (fun x => fderiv ℝ (WeakFourier.heatWeakRealTest k) x (basisVec i)) :=
  WeakFourier.heatWeak_continuous_fderiv_apply (WeakFourier.heatWeak_realTest_contDiff k) i

theorem WeakFourier.heatWeak_imagTestDeriv_continuous (i : Fin 2)
    (k : Frequency) :
    Continuous (fun x => fderiv ℝ (WeakFourier.heatWeakImagTest k) x (basisVec i)) :=
  WeakFourier.heatWeak_continuous_fderiv_apply (WeakFourier.heatWeak_imagTest_contDiff k) i

theorem WeakFourier.heatWeak_realTestDeriv_hasCompactSupport (i : Fin 2)
    (k : Frequency) :
    HasCompactSupport (fun x => fderiv ℝ (WeakFourier.heatWeakRealTest k) x (basisVec i)) :=
  HasCompactSupport.fderiv_apply ℝ (WeakFourier.heatWeak_realTest_hasCompactSupport k)
    (basisVec i)

theorem WeakFourier.heatWeak_imagTestDeriv_hasCompactSupport (i : Fin 2)
    (k : Frequency) :
    HasCompactSupport (fun x => fderiv ℝ (WeakFourier.heatWeakImagTest k) x (basisVec i)) :=
  HasCompactSupport.fderiv_apply ℝ (WeakFourier.heatWeak_imagTest_hasCompactSupport k)
    (basisVec i)

theorem WeakFourier.volume_unitCellAt_ne_top (a : Fin 2 → ℝ) :
    volume (unitCellAt 2 a) ≠ ⊤ := by
  unfold unitCellAt
  have hset : {x : Vec 2 | ∀ i, x i ∈ Ioc (a i) (a i + 1)} =
      Set.univ.pi (fun i => Ioc (a i) (a i + 1)) := by
    ext x
    simp
  rw [hset, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioc]

theorem WeakFourier.memLp_heatWeak_unitCell {f : Vec 2 → ℝ}
    (hf : MemL2On AVenhance.unitCube f) :
    MemLp f 2 (volume.restrict (unitCell 2)) := by
  have hμ : (volume : Measure (Vec 2)).restrict (unitCell 2) =
      volume.restrict AVenhance.unitCube :=
    Measure.restrict_congr_set unitCell_ae_eq_unitCube
  rw [hμ]
  exact hf

theorem WeakFourier.integrableOn_periodic_heatWeak_tile {f : Vec 2 → ℝ}
    (hf : MemL2On AVenhance.unitCube f) (hper : IsZdPeriodic f)
    (b : Bool × Bool) : IntegrableOn f (heatPeriodicTile b) := by
  let a := heatPeriodicTileStart b
  have hmem := memLp_periodic_unitCellAt (WeakFourier.memLp_heatWeak_unitCell hf) hper
    (heatPeriodicTileShift b)
  have hmem' : MemLp f 2 (volume.restrict (unitCellAt 2 a)) := by
    simpa [a, heatPeriodicTileStart] using hmem
  have hfinite : IsFiniteMeasure (volume.restrict (unitCellAt 2 a)) :=
    isFiniteMeasure_restrict.mpr (WeakFourier.volume_unitCellAt_ne_top a)
  have hL1 : Integrable f (volume.restrict (unitCellAt 2 a)) :=
    @MemLp.integrable (Vec 2) ℝ _ (volume.restrict (unitCellAt 2 a))
      inferInstance inferInstance (2 : ENNReal)
      (by norm_num : (1 : ENNReal) ≤ 2) f hfinite hmem'
  change Integrable f (volume.restrict (heatPeriodicTile b))
  simpa [heatPeriodicTile, a] using hL1

theorem WeakFourier.heatWeak_norm_bound_of_continuous_compact_support
    {w : Vec 2 → ℝ} (hwc : Continuous w) (hws : HasCompactSupport w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖w x‖ ≤ C := by
  have hbounded : Bornology.IsBounded (w '' tsupport w) :=
    hws.isCompact.image hwc |>.isBounded
  obtain ⟨C, hCpos, hC⟩ := hbounded.subset_ball_lt 0 0
  refine ⟨C, hCpos.le, ?_⟩
  intro x
  by_cases hx : x ∈ tsupport w
  · have hball := hC ⟨x, hx, rfl⟩
    have hnorm : ‖w x‖ < C := by
      simpa [Metric.mem_ball, dist_eq_norm] using hball
    exact hnorm.le
  · have hzero : w x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [hzero, hCpos.le]

theorem WeakFourier.integrableOn_mul_of_norm_bound {f w : Vec 2 → ℝ}
    {S : Set (Vec 2)} (hf : IntegrableOn f S) (hw : Continuous w)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, ‖w x‖ ≤ C) :
    IntegrableOn (fun x => f x * w x) S := by
  change Integrable (fun x => f x * w x) (volume.restrict S)
  change Integrable f (volume.restrict S) at hf
  have hmeas : AEStronglyMeasurable (fun x => f x * w x)
      (volume.restrict S) :=
    hf.aestronglyMeasurable.mul hw.measurable.aestronglyMeasurable
  have hmajor : Integrable (fun x => C * ‖f x‖) (volume.restrict S) :=
    hf.norm.const_mul C
  apply hmajor.mono hmeas
  filter_upwards with x
  rw [norm_mul]
  calc
    ‖f x‖ * ‖w x‖ ≤ ‖f x‖ * C :=
      mul_le_mul_of_nonneg_left (hbound x) (norm_nonneg _)
    _ = ‖C * ‖f x‖‖ := by
      simp [Real.norm_eq_abs, abs_of_nonneg hC]
      ring

theorem WeakFourier.heatWeak_tile_weight_integrable {f : Vec 2 → ℝ}
    (hf : MemL2On AVenhance.unitCube f) (hper : IsZdPeriodic f)
    {w : Vec 2 → ℝ} (hwc : Continuous w) (hws : HasCompactSupport w) :
    ∀ b : Bool × Bool,
      IntegrableOn (fun x => f x * w x) (heatPeriodicTile b) := by
  obtain ⟨C, hC, hbound⟩ := WeakFourier.heatWeak_norm_bound_of_continuous_compact_support hwc hws
  intro b
  exact WeakFourier.integrableOn_mul_of_norm_bound
    (WeakFourier.integrableOn_periodic_heatWeak_tile hf hper b) hwc hC hbound

theorem WeakFourier.heatWeak_torusCharacter_norm (k : Frequency) (x : Vec 2) :
    ‖torusCharacter k x‖ = 1 := by
  simp [torusCharacter, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    toUnitTorus, Complex.norm_exp, Complex.mul_re]

theorem WeakFourier.integrableOn_heatWeak_character_mul_real {f : Vec 2 → ℝ}
    (hf : MemL2On AVenhance.unitCube f) (hper : IsZdPeriodic f)
    (k : Frequency) :
    IntegrableOn (fun x => torusCharacter k x * (f x : ℂ)) (unitCell 2) := by
  have hbase := WeakFourier.integrableOn_periodic_heatWeak_tile hf hper (true, true)
  have hstart : heatPeriodicTileStart (true, true) = 0 := by
    ext j
    fin_cases j <;>
      simp [heatPeriodicTileStart, heatPeriodicTileShift, intVector]
  have hbase' : IntegrableOn f (unitCell 2) := by
    rw [show heatPeriodicTile (true, true) = unitCell 2 by
      change unitCellAt 2 (heatPeriodicTileStart (true, true)) =
        unitCellAt 2 (fun _ : Fin 2 => 0)
      exact congrArg (unitCellAt 2) hstart] at hbase
    exact hbase
  change Integrable (fun x => torusCharacter k x * (f x : ℂ))
    (volume.restrict (unitCell 2))
  have hcomplex : Integrable (fun x => (f x : ℂ))
      (volume.restrict (unitCell 2)) := by
    exact hbase'.ofReal
  have hchar : Continuous (torusCharacter k) :=
    (torusCharacter_contDiff k).continuous
  have hmeas : AEStronglyMeasurable
      (fun x => torusCharacter k x * (f x : ℂ))
      (volume.restrict (unitCell 2)) :=
    hchar.measurable.aestronglyMeasurable.mul hcomplex.aestronglyMeasurable
  apply hcomplex.mono hmeas
  filter_upwards with x
  rw [Complex.norm_mul, WeakFourier.heatWeak_torusCharacter_norm]
  simp [Complex.norm_real, Real.norm_eq_abs]

theorem WeakFourier.heatWeak_gradientCoord_periodic {Du : Vec 2 → Vec 2}
    (hDu : IsZdPeriodic Du) (i : Fin 2) :
    IsZdPeriodic (fun x => Du x i) := by
  intro n x
  exact congrArg (fun v : Vec 2 => v i) (hDu n x)

theorem WeakFourier.heatWeak_realCellIBP {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (h : AVenhance.IsPeriodicH1With u Du) (i : Fin 2) (k : Frequency) :
    ∫ x in unitCell 2,
        u x * fderiv ℝ (WeakFourier.heatWeakRealCharacter k) x (basisVec i) =
      -∫ x in unitCell 2, Du x i * WeakFourier.heatWeakRealCharacter k x := by
  have hweak := h.2.2.2.2 i (WeakFourier.heatWeakRealTest k)
    (WeakFourier.heatWeak_realTest_contDiff k) (WeakFourier.heatWeak_realTest_hasCompactSupport k)
    (by simp)
  have hweak' :
      ∫ x, u x * fderiv ℝ (WeakFourier.heatWeakRealTest k) x (basisVec i) =
        -∫ x, Du x i * WeakFourier.heatWeakRealTest k x := by
    simpa using hweak
  have hleft := integral_periodic_weight2 (g := u)
    (w := fun x => fderiv ℝ (WeakFourier.heatWeakRealTest k) x (basisVec i))
    (q := fun x => fderiv ℝ (WeakFourier.heatWeakRealCharacter k) x (basisVec i)) h.1
    (WeakFourier.heatWeak_realTestDeriv_support_subset_tiles i k)
      (WeakFourier.heatWeak_tile_weight_integrable h.2.2.1 h.1
      (WeakFourier.heatWeak_realTestDeriv_continuous i k)
      (WeakFourier.heatWeak_realTestDeriv_hasCompactSupport i k))
    (fun x hx => WeakFourier.heatWeak_realTestDeriv_periodization i k hx)
  have hDuPer := WeakFourier.heatWeak_gradientCoord_periodic h.2.1 i
  have hright := integral_periodic_weight2 (g := fun x => Du x i)
    (w := WeakFourier.heatWeakRealTest k) (q := WeakFourier.heatWeakRealCharacter k) hDuPer
    (WeakFourier.heatWeak_realTest_support_subset_tiles k)
    (WeakFourier.heatWeak_tile_weight_integrable (h.2.2.2.1 i) hDuPer
      ((WeakFourier.heatWeak_realTest_contDiff k).continuous)
      (WeakFourier.heatWeak_realTest_hasCompactSupport k))
    (fun x hx => WeakFourier.heatWeak_realTest_periodization k hx)
  calc
    ∫ x in unitCell 2, u x * fderiv ℝ (WeakFourier.heatWeakRealCharacter k) x
        (basisVec i) =
      ∫ x, u x * fderiv ℝ (WeakFourier.heatWeakRealTest k) x (basisVec i) := hleft.2.symm
    _ = -∫ x, Du x i * WeakFourier.heatWeakRealTest k x := hweak'
    _ = -∫ x in unitCell 2, Du x i * WeakFourier.heatWeakRealCharacter k x := by
      rw [hright.2]

theorem WeakFourier.heatWeak_imagCellIBP {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (h : AVenhance.IsPeriodicH1With u Du) (i : Fin 2) (k : Frequency) :
    ∫ x in unitCell 2,
        u x * fderiv ℝ (WeakFourier.heatWeakImagCharacter k) x (basisVec i) =
      -∫ x in unitCell 2, Du x i * WeakFourier.heatWeakImagCharacter k x := by
  have hweak := h.2.2.2.2 i (WeakFourier.heatWeakImagTest k)
    (WeakFourier.heatWeak_imagTest_contDiff k) (WeakFourier.heatWeak_imagTest_hasCompactSupport k)
    (by simp)
  have hweak' :
      ∫ x, u x * fderiv ℝ (WeakFourier.heatWeakImagTest k) x (basisVec i) =
        -∫ x, Du x i * WeakFourier.heatWeakImagTest k x := by
    simpa using hweak
  have hleft := integral_periodic_weight2 (g := u)
    (w := fun x => fderiv ℝ (WeakFourier.heatWeakImagTest k) x (basisVec i))
    (q := fun x => fderiv ℝ (WeakFourier.heatWeakImagCharacter k) x (basisVec i)) h.1
    (WeakFourier.heatWeak_imagTestDeriv_support_subset_tiles i k)
      (WeakFourier.heatWeak_tile_weight_integrable h.2.2.1 h.1
      (WeakFourier.heatWeak_imagTestDeriv_continuous i k)
      (WeakFourier.heatWeak_imagTestDeriv_hasCompactSupport i k))
    (fun x hx => WeakFourier.heatWeak_imagTestDeriv_periodization i k hx)
  have hDuPer := WeakFourier.heatWeak_gradientCoord_periodic h.2.1 i
  have hright := integral_periodic_weight2 (g := fun x => Du x i)
    (w := WeakFourier.heatWeakImagTest k) (q := WeakFourier.heatWeakImagCharacter k) hDuPer
    (WeakFourier.heatWeak_imagTest_support_subset_tiles k)
    (WeakFourier.heatWeak_tile_weight_integrable (h.2.2.2.1 i) hDuPer
      ((WeakFourier.heatWeak_imagTest_contDiff k).continuous)
      (WeakFourier.heatWeak_imagTest_hasCompactSupport k))
    (fun x hx => WeakFourier.heatWeak_imagTest_periodization k hx)
  calc
    ∫ x in unitCell 2, u x * fderiv ℝ (WeakFourier.heatWeakImagCharacter k) x
        (basisVec i) =
      ∫ x, u x * fderiv ℝ (WeakFourier.heatWeakImagTest k) x (basisVec i) := hleft.2.symm
    _ = -∫ x, Du x i * WeakFourier.heatWeakImagTest k x := hweak'
    _ = -∫ x in unitCell 2, Du x i * WeakFourier.heatWeakImagCharacter k x := by
      rw [hright.2]

/-- Fourier multiplier for differentiation in a spatial coordinate. -/
def WeakFourier.heatWeakGradientMultiplier (i : Fin 2) (k : Frequency) : ℂ :=
  2 * Real.pi * Complex.I * (k i : ℂ)

theorem WeakFourier.heatWeak_realMultiplier_cell {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (h : AVenhance.IsPeriodicH1With u Du) (i : Fin 2) (k : Frequency) :
    ∫ x in unitCell 2,
        u x * (WeakFourier.heatWeakGradientMultiplier i k * torusCharacter k x).re =
      ∫ x in unitCell 2, Du x i * WeakFourier.heatWeakRealCharacter k x := by
  have hderiv (x : Vec 2) :
      fderiv ℝ (WeakFourier.heatWeakRealCharacter k) x (basisVec i) =
        -((WeakFourier.heatWeakGradientMultiplier i k * torusCharacter k x).re) := by
    rw [WeakFourier.heatWeak_coordDeriv_realCharacter]
    have hmul :
        (-2 * Real.pi * Complex.I * (k i : ℂ)) * torusCharacter k x =
          -(WeakFourier.heatWeakGradientMultiplier i k * torusCharacter k x) := by
      dsimp [WeakFourier.heatWeakGradientMultiplier]
      ring
    rw [hmul]
    simp
  have hcell := WeakFourier.heatWeak_realCellIBP h i k
  calc
    ∫ x in unitCell 2,
        u x * (WeakFourier.heatWeakGradientMultiplier i k * torusCharacter k x).re =
      -∫ x in unitCell 2,
        u x * fderiv ℝ (WeakFourier.heatWeakRealCharacter k) x (basisVec i) := by
      calc
        ∫ x in unitCell 2,
            u x * (WeakFourier.heatWeakGradientMultiplier i k * torusCharacter k x).re =
          ∫ x in unitCell 2,
            -(u x * fderiv ℝ (WeakFourier.heatWeakRealCharacter k) x (basisVec i)) := by
              apply setIntegral_congr_fun (measurableSet_unitCell 2)
              intro x hx
              change u x * (WeakFourier.heatWeakGradientMultiplier i k *
                torusCharacter k x).re =
                -(u x * fderiv ℝ (WeakFourier.heatWeakRealCharacter k) x (basisVec i))
              rw [hderiv x]
              ring
        _ = -∫ x in unitCell 2,
            u x * fderiv ℝ (WeakFourier.heatWeakRealCharacter k) x (basisVec i) := by
              rw [integral_neg]
    _ = ∫ x in unitCell 2, Du x i * WeakFourier.heatWeakRealCharacter k x := by
      rw [hcell]
      ring

theorem WeakFourier.heatWeak_imagMultiplier_cell {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (h : AVenhance.IsPeriodicH1With u Du) (i : Fin 2) (k : Frequency) :
    ∫ x in unitCell 2,
        u x * (WeakFourier.heatWeakGradientMultiplier i k * torusCharacter k x).im =
      ∫ x in unitCell 2, Du x i * WeakFourier.heatWeakImagCharacter k x := by
  have hderiv (x : Vec 2) :
      fderiv ℝ (WeakFourier.heatWeakImagCharacter k) x (basisVec i) =
        -((WeakFourier.heatWeakGradientMultiplier i k * torusCharacter k x).im) := by
    rw [WeakFourier.heatWeak_coordDeriv_imagCharacter]
    have hmul :
        (-2 * Real.pi * Complex.I * (k i : ℂ)) * torusCharacter k x =
          -(WeakFourier.heatWeakGradientMultiplier i k * torusCharacter k x) := by
      dsimp [WeakFourier.heatWeakGradientMultiplier]
      ring
    rw [hmul]
    simp
  have hcell := WeakFourier.heatWeak_imagCellIBP h i k
  calc
    ∫ x in unitCell 2,
        u x * (WeakFourier.heatWeakGradientMultiplier i k * torusCharacter k x).im =
      -∫ x in unitCell 2,
        u x * fderiv ℝ (WeakFourier.heatWeakImagCharacter k) x (basisVec i) := by
      calc
        ∫ x in unitCell 2,
            u x * (WeakFourier.heatWeakGradientMultiplier i k * torusCharacter k x).im =
          ∫ x in unitCell 2,
            -(u x * fderiv ℝ (WeakFourier.heatWeakImagCharacter k) x (basisVec i)) := by
              apply setIntegral_congr_fun (measurableSet_unitCell 2)
              intro x hx
              change u x * (WeakFourier.heatWeakGradientMultiplier i k *
                torusCharacter k x).im =
                -(u x * fderiv ℝ (WeakFourier.heatWeakImagCharacter k) x (basisVec i))
              rw [hderiv x]
              ring
        _ = -∫ x in unitCell 2,
            u x * fderiv ℝ (WeakFourier.heatWeakImagCharacter k) x (basisVec i) := by
              rw [integral_neg]
    _ = ∫ x in unitCell 2, Du x i * WeakFourier.heatWeakImagCharacter k x := by
      rw [hcell]
      ring

theorem WeakFourier.heatWeak_gradientFourierCoeff_eq {u : Vec 2 → ℝ}
    {Du : Vec 2 → Vec 2} (h : AVenhance.IsPeriodicH1With u Du)
    (i : Fin 2) (k : Frequency) :
    (WeakFourier.heatWeakGradientMultiplier i k *
        ∫ x in unitCell 2, torusCharacter k x * (u x : ℂ)).re =
      (∫ x in unitCell 2, torusCharacter k x * (Du x i : ℂ)).re ∧
    (WeakFourier.heatWeakGradientMultiplier i k *
        ∫ x in unitCell 2, torusCharacter k x * (u x : ℂ)).im =
      (∫ x in unitCell 2, torusCharacter k x * (Du x i : ℂ)).im := by
  have hu := WeakFourier.integrableOn_heatWeak_character_mul_real h.2.2.1 h.1 k
  have hDuPer := WeakFourier.heatWeak_gradientCoord_periodic h.2.1 i
  have hDu := WeakFourier.integrableOn_heatWeak_character_mul_real (h.2.2.2.1 i) hDuPer k
  change Integrable (fun x => torusCharacter k x * (u x : ℂ))
    (volume.restrict (unitCell 2)) at hu
  change Integrable (fun x => torusCharacter k x * (Du x i : ℂ))
    (volume.restrict (unitCell 2)) at hDu
  have hmulU : Integrable (fun x => WeakFourier.heatWeakGradientMultiplier i k *
      (torusCharacter k x * (u x : ℂ))) (volume.restrict (unitCell 2)) :=
    hu.const_mul (WeakFourier.heatWeakGradientMultiplier i k)
  have hrealInt := integral_re hmulU
  have himagInt := integral_im hmulU
  have hrealCoeff := integral_re hDu
  have himagCoeff := integral_im hDu
  have hrealPoint (x : Vec 2) :
      u x * (WeakFourier.heatWeakGradientMultiplier i k * torusCharacter k x).re =
        (WeakFourier.heatWeakGradientMultiplier i k *
          (torusCharacter k x * (u x : ℂ))).re := by
    rw [show WeakFourier.heatWeakGradientMultiplier i k *
        (torusCharacter k x * (u x : ℂ)) =
          (WeakFourier.heatWeakGradientMultiplier i k * torusCharacter k x) *
            (u x : ℂ) by ring]
    simp [Complex.mul_re]
    ring
  have himagPoint (x : Vec 2) :
      u x * (WeakFourier.heatWeakGradientMultiplier i k * torusCharacter k x).im =
        (WeakFourier.heatWeakGradientMultiplier i k *
          (torusCharacter k x * (u x : ℂ))).im := by
    rw [show WeakFourier.heatWeakGradientMultiplier i k *
        (torusCharacter k x * (u x : ℂ)) =
          (WeakFourier.heatWeakGradientMultiplier i k * torusCharacter k x) *
            (u x : ℂ) by ring]
    simp [Complex.mul_im]
    ring
  have hrightRealPoint (x : Vec 2) :
      Du x i * WeakFourier.heatWeakRealCharacter k x =
        (torusCharacter k x * (Du x i : ℂ)).re := by
    simp [WeakFourier.heatWeakRealCharacter, Complex.mul_re]
    ring
  have hrightImagPoint (x : Vec 2) :
      Du x i * WeakFourier.heatWeakImagCharacter k x =
        (torusCharacter k x * (Du x i : ℂ)).im := by
    simp [WeakFourier.heatWeakImagCharacter, Complex.mul_im]
    ring
  constructor
  · calc
      (WeakFourier.heatWeakGradientMultiplier i k *
          ∫ x in unitCell 2, torusCharacter k x * (u x : ℂ)).re =
        Complex.re (WeakFourier.heatWeakGradientMultiplier i k *
          ∫ x in unitCell 2, torusCharacter k x * (u x : ℂ)) := rfl
      _ = Complex.re (∫ x in unitCell 2,
          WeakFourier.heatWeakGradientMultiplier i k *
            (torusCharacter k x * (u x : ℂ))) := by
              rw [integral_const_mul]
      _ = ∫ x in unitCell 2,
          (WeakFourier.heatWeakGradientMultiplier i k *
            (torusCharacter k x * (u x : ℂ))).re := hrealInt.symm
      _ = ∫ x in unitCell 2,
          u x * (WeakFourier.heatWeakGradientMultiplier i k * torusCharacter k x).re := by
              apply setIntegral_congr_fun (measurableSet_unitCell 2)
              intro x hx
              exact hrealPoint x |>.symm
      _ = ∫ x in unitCell 2, Du x i * WeakFourier.heatWeakRealCharacter k x :=
        WeakFourier.heatWeak_realMultiplier_cell h i k
      _ = ∫ x in unitCell 2,
          (torusCharacter k x * (Du x i : ℂ)).re := by
            apply setIntegral_congr_fun (measurableSet_unitCell 2)
            intro x hx
            exact hrightRealPoint x
      _ = (∫ x in unitCell 2,
          torusCharacter k x * (Du x i : ℂ)).re := hrealCoeff
  · calc
      (WeakFourier.heatWeakGradientMultiplier i k *
          ∫ x in unitCell 2, torusCharacter k x * (u x : ℂ)).im =
        Complex.im (WeakFourier.heatWeakGradientMultiplier i k *
          ∫ x in unitCell 2, torusCharacter k x * (u x : ℂ)) := rfl
      _ = Complex.im (∫ x in unitCell 2,
          WeakFourier.heatWeakGradientMultiplier i k *
            (torusCharacter k x * (u x : ℂ))) := by
              rw [integral_const_mul]
      _ = ∫ x in unitCell 2,
          (WeakFourier.heatWeakGradientMultiplier i k *
            (torusCharacter k x * (u x : ℂ))).im := himagInt.symm
      _ = ∫ x in unitCell 2,
          u x * (WeakFourier.heatWeakGradientMultiplier i k * torusCharacter k x).im := by
              apply setIntegral_congr_fun (measurableSet_unitCell 2)
              intro x hx
              exact himagPoint x |>.symm
      _ = ∫ x in unitCell 2, Du x i * WeakFourier.heatWeakImagCharacter k x :=
        WeakFourier.heatWeak_imagMultiplier_cell h i k
      _ = ∫ x in unitCell 2,
          (torusCharacter k x * (Du x i : ℂ)).im := by
            apply setIntegral_congr_fun (measurableSet_unitCell 2)
            intro x hx
            exact hrightImagPoint x
      _ = (∫ x in unitCell 2,
          torusCharacter k x * (Du x i : ℂ)).im := himagCoeff

theorem mFourierCoeff_frozenPeriodicH1GradientL2
    {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (h : AVenhance.IsPeriodicH1With u Du) (i : Fin 2) (k : Frequency) :
    UnitAddTorus.mFourierCoeff (frozenPeriodicH1GradientL2 h i) k =
      (2 * Real.pi * Complex.I * (k i : ℂ)) *
        UnitAddTorus.mFourierCoeff (frozenPeriodicH1ValueL2 h) k := by
  change UnitAddTorus.mFourierCoeff
      (frozenCellToTorusL2 (h.2.2.2.1 i)) k =
    WeakFourier.heatWeakGradientMultiplier i k *
      UnitAddTorus.mFourierCoeff (frozenCellToTorusL2 h.2.2.1) k
  rw [mFourierCoeff_frozenCellToTorusL2 (h.2.2.2.1 i),
    mFourierCoeff_frozenCellToTorusL2 h.2.2.1]
  obtain ⟨hre, him⟩ := WeakFourier.heatWeak_gradientFourierCoeff_eq h i k
  apply Complex.ext <;> simp [hre, him]

end AVenhance.Infra.Heat
