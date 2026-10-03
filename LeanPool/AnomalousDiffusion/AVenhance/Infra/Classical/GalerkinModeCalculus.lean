/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.Commutator
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.Drift
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.RealModes.Frequency
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.RealModes.Modes
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.RealModes.Projection
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FourierCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FrozenBridge
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.ODE.Linear.Basic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.PeriodicCalculus
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Coordinate derivatives of the real Fourier modes used by the Galerkin system. -/

@[expose] public section

noncomputable section

open Homogenization MeasureTheory
open AVenhance.Infra.Torus
open AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance classicalGalerkinMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

namespace AVenhance.Infra.Classical

open Set

namespace LinearIntegralSolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Applying a fixed continuous linear map to a finite-dimensional linear ODE solution adds the
commutator of that map with the ODE operator to the transformed forcing. -/
theorem continuousLinearMap_transform
    {A : ℝ → E →L[ℝ] E} {f y : ℝ → E} {y₀ : E} {a b : ℝ}
    (hab : a ≤ b)
    (hy : AVenhance.Infra.ODE.IsLinearIntegralSolution A f y₀ a b y)
    (hRhs : IntervalIntegrable (AVenhance.Infra.ODE.linearRhs A f y) volume a b)
    (L : E →L[ℝ] E) :
    AVenhance.Infra.ODE.IsLinearIntegralSolution A
      (fun t => L (f t) + L (A t (y t)) - A t (L (y t)))
      (L y₀) a b (fun t => L (y t)) := by
  intro t ht
  have hsubset : uIcc a t ⊆ uIcc a b := by
    rw [uIcc_of_le ht.1, uIcc_of_le hab]
    intro s hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  have hRhsT : IntervalIntegrable
      (AVenhance.Infra.ODE.linearRhs A f y) volume a t := hRhs.mono_set hsubset
  have hsource (s : ℝ) :
      L (AVenhance.Infra.ODE.linearRhs A f y s) =
        AVenhance.Infra.ODE.linearRhs A
          (fun t => L (f t) + L (A t (y t)) - A t (L (y t)))
          (fun t => L (y t)) s := by
    simp only [AVenhance.Infra.ODE.linearRhs, map_add]
    abel
  calc
    L (y t) = L (y₀ +
        ∫ s in a..t, AVenhance.Infra.ODE.linearRhs A f y s) :=
      congrArg L (hy t ht)
    _ = L y₀ + ∫ s in a..t,
        L (AVenhance.Infra.ODE.linearRhs A f y s) := by
      rw [map_add]
      apply congrArg (fun z : E => L y₀ + z)
      exact (L.intervalIntegral_comp_comm hRhsT).symm
    _ = L y₀ + ∫ s in a..t,
        AVenhance.Infra.ODE.linearRhs A
          (fun t => L (f t) + L (A t (y t)) - A t (L (y t)))
          (fun t => L (y t)) s := by
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      exact hsource s

end LinearIntegralSolution

theorem GalerkinModeCalculus.torusCharacter_line_eq {n : ℕ} (i : Fin (n + 1))
    (k : Fin (n + 1) → ℤ) (z : Vec n) (t : ℝ) :
    torusCharacter k (i.insertNth t z) =
      fourier (-(k i)) (t : UnitAddCircle) *
        ∏ j : Fin n, fourier (-(k (i.succAbove j))) (z j : UnitAddCircle) := by
  simp [torusCharacter, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    toUnitTorus, i.prod_univ_succAbove]

theorem GalerkinModeCalculus.torusCharacter_line_hasDerivAt {n : ℕ} (i : Fin (n + 1))
    (k : Fin (n + 1) → ℤ) (z : Vec n) (t : ℝ) :
    HasDerivAt (fun s => torusCharacter k (i.insertNth s z))
      ((-2 * Real.pi * Complex.I * (k i : ℂ)) *
        torusCharacter k (i.insertNth t z)) t := by
  let c : ℂ := ∏ j : Fin n,
    fourier (-(k (i.succAbove j))) (z j : UnitAddCircle)
  have hline : ∀ s, torusCharacter k (i.insertNth s z) =
      fourier (-(k i)) (s : UnitAddCircle) * c := by
    intro s
    simpa [c] using GalerkinModeCalculus.torusCharacter_line_eq i k z s
  have h := (hasDerivAt_fourier_neg (T := 1) (k i) t).mul_const c
  convert h using 1
  · exact funext hline
  · rw [hline t]
    simp
    ring

theorem GalerkinModeCalculus.coordDeriv_torusCharacter {n : ℕ} (i : Fin (n + 1))
    (k : Fin (n + 1) → ℤ) (x : Vec (n + 1)) :
    coordDeriv i (torusCharacter k) x =
      (-2 * Real.pi * Complex.I * (k i : ℂ)) * torusCharacter k x := by
  let z := i.removeNth x
  have hx : i.insertNth (x i) z = x := Fin.insertNth_self_removeNth i x
  have hline :=
    ((torusCharacter_contDiff k).differentiable (by simp)
      (i.insertNth (x i) z)).hasFDerivAt.comp_hasDerivAt (x i)
      (Homogenization.hasDerivAt_insertNth i z (x i))
  have hchar := GalerkinModeCalculus.torusCharacter_line_hasDerivAt i k z (x i)
  calc
    coordDeriv i (torusCharacter k) x =
        deriv (fun t => torusCharacter k (i.insertNth t z)) (x i) := by
      rw [← hx]
      simpa [coordDeriv, Function.comp_def] using hline.deriv.symm
    _ = (-2 * Real.pi * Complex.I * (k i : ℂ)) *
        torusCharacter k (i.insertNth (x i) z) := hchar.deriv
    _ = (-2 * Real.pi * Complex.I * (k i : ℂ)) * torusCharacter k x := by rw [hx]

theorem coordDeriv_re {f : Vec 2 → ℂ} (hf : ContDiff ℝ 1 f) (i : Fin 2) (x : Vec 2) :
    coordDeriv i (fun y => (f y).re) x = (coordDeriv i f x).re := by
  let ρ : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM
  have hcomp := (hasFDerivAt_const ρ x).clm_apply
    ((hf.differentiable (by norm_num) x).hasFDerivAt)
  have hderiv : fderiv ℝ (fun y => ρ (f y)) x = ρ.comp (fderiv ℝ f x) := by
    simpa [ρ] using hcomp.fderiv
  have hfun : (fun y => ((f y).re : ℂ)) = fun y => ρ (f y) := by
    funext y
    simp [ρ]
  simp only [coordDeriv]
  rw [hfun, hderiv]
  simp [ρ, ContinuousLinearMap.comp_apply]

theorem coordDeriv_im {f : Vec 2 → ℂ} (hf : ContDiff ℝ 1 f) (i : Fin 2) (x : Vec 2) :
    coordDeriv i (fun y => (f y).im) x = (coordDeriv i f x).im := by
  let ρ : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.imCLM
  have hcomp := (hasFDerivAt_const ρ x).clm_apply
    ((hf.differentiable (by norm_num) x).hasFDerivAt)
  have hderiv : fderiv ℝ (fun y => ρ (f y)) x = ρ.comp (fderiv ℝ f x) := by
    simpa [ρ] using hcomp.fderiv
  have hfun : (fun y => ((f y).im : ℂ)) = fun y => ρ (f y) := by
    funext y
    simp [ρ]
  simp only [coordDeriv]
  rw [hfun, hderiv]
  simp [ρ, ContinuousLinearMap.comp_apply]

theorem GalerkinModeCalculus.spaceGrad_re_eq_coordDeriv {f : Vec 2 → ℂ}
    (hf : ContDiff ℝ 1 f) (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (fun y => (f y).re) x i = (coordDeriv i f x).re := by
  have hreal : ContDiff ℝ 1 (fun y : Vec 2 => (f y).re) := by
    exact Complex.reCLM.contDiff.comp hf
  have hcast := coordDeriv_realToComplex hreal i x
  have hcast' : coordDeriv i (fun y : Vec 2 => (f y).re) x =
      (AVenhance.spaceGrad (fun y : Vec 2 => (f y).re) x i : ℂ) := by
    have hfun : (fun y : Vec 2 => ((f y).re : ℂ)) =
        realToComplex (fun y : Vec 2 => (f y).re) := by
      funext y
      rfl
    rw [hfun]
    exact hcast
  have hRe := coordDeriv_re hf i x
  rw [hcast'] at hRe
  exact Complex.ofReal_injective hRe

theorem GalerkinModeCalculus.spaceGrad_im_eq_coordDeriv {f : Vec 2 → ℂ}
    (hf : ContDiff ℝ 1 f) (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (fun y => (f y).im) x i = (coordDeriv i f x).im := by
  have himag : ContDiff ℝ 1 (fun y : Vec 2 => (f y).im) := by
    exact Complex.imCLM.contDiff.comp hf
  have hcast := coordDeriv_realToComplex himag i x
  have hcast' : coordDeriv i (fun y : Vec 2 => (f y).im) x =
      (AVenhance.spaceGrad (fun y : Vec 2 => (f y).im) x i : ℂ) := by
    have hfun : (fun y : Vec 2 => ((f y).im : ℂ)) =
        realToComplex (fun y : Vec 2 => (f y).im) := by
      funext y
      rfl
    rw [hfun]
    exact hcast
  have hIm := coordDeriv_im hf i x
  rw [hcast'] at hIm
  exact Complex.ofReal_injective hIm

theorem GalerkinModeCalculus.spaceGrad_const_smul {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f)
    (c : ℝ) (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (fun y => c * f y) x i = c * AVenhance.spaceGrad f x i := by
  change fderiv ℝ (c • f) x (basisVec i) = _
  have hderiv : fderiv ℝ (c • f) x = c • fderiv ℝ f x := by
    exact fderiv_const_smul (hf.differentiable (by norm_num) x) c
  rw [hderiv]
  rfl

/-- Exchange the sine and cosine modes at each frequency, fixing the constant mode. -/
def realFourierModeIndexSwap {N : ℕ} : RealFourierIndex N → RealFourierIndex N
  | none => none
  | some (p, false) => some (p, true)
  | some (p, true) => some (p, false)

theorem realFourierModeIndexSwap_involutive {N : ℕ} (a : RealFourierIndex N) :
    realFourierModeIndexSwap (realFourierModeIndexSwap a) = a := by
  cases a with
  | none => rfl
  | some q =>
      rcases q with ⟨p, h⟩
      cases h <;> rfl

/-- The signed frequency multiplier in the coordinate derivative of a real mode. -/
def realFourierModeDerivativeScale {N : ℕ} (a : RealFourierIndex N) (i : Fin 2) : ℝ :=
  match a with
  | none => 0
  | some (p, false) => -(2 * Real.pi * (representativeFrequency p i : ℝ))
  | some (p, true) => 2 * Real.pi * (representativeFrequency p i : ℝ)

theorem representativeFrequency_coordinate_abs_le (N : ℕ)
    (p : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N}) (i : Fin 2) :
    |representativeFrequency p i| ≤ N := by
  have hbox := (mem_positiveFrequencyRepresentatives p.2).1
  simp only [symmetricFrequencyBox, Finset.mem_product, Finset.mem_Icc] at hbox
  rcases hbox with ⟨⟨h₀, h₁⟩, ⟨h₂, h₃⟩⟩
  fin_cases i
  · simpa [representativeFrequency, pairFrequency] using
      (abs_le.mpr ⟨h₀, h₁⟩ : |p.1.1| ≤ (N : ℤ))
  · simpa [representativeFrequency, pairFrequency] using
      (abs_le.mpr ⟨h₂, h₃⟩ : |p.1.2| ≤ (N : ℤ))

theorem realFourierModeDerivativeScale_abs_le (N : ℕ) (a : RealFourierIndex N)
    (i : Fin 2) : |realFourierModeDerivativeScale a i| ≤ 2 * Real.pi * N := by
  cases a with
  | none => simp only [realFourierModeDerivativeScale, abs_zero]; positivity
  | some q =>
      rcases q with ⟨p, sine⟩
      have hkZ := representativeFrequency_coordinate_abs_le N p i
      have hk : |(representativeFrequency p i : ℝ)| ≤ (N : ℝ) := by
        exact_mod_cast hkZ
      cases sine <;>
        simp only [realFourierModeDerivativeScale, abs_neg]
      all_goals
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
        exact mul_le_mul_of_nonneg_left hk (by positivity)

theorem realFourierModeDerivativeScale_swap (N : ℕ) (a : RealFourierIndex N)
    (i : Fin 2) :
    realFourierModeDerivativeScale (realFourierModeIndexSwap a) i =
      -realFourierModeDerivativeScale a i := by
  cases a with
  | none => simp [realFourierModeIndexSwap, realFourierModeDerivativeScale]
  | some q =>
      rcases q with ⟨p, sine⟩
      cases sine <;> simp [realFourierModeIndexSwap, realFourierModeDerivativeScale]

/-- A coordinate derivative of a real Fourier mode is the frequency factor times its paired
sine or cosine mode. -/
theorem spaceGrad_realFourierModeAmbient (N : ℕ) (a : RealFourierIndex N)
    (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (realFourierModeAmbient N a) x i =
      match a with
      | none => 0
      | some (p, false) =>
          -(2 * Real.pi * (representativeFrequency p i : ℝ)) *
            realFourierModeAmbient N (realFourierModeIndexSwap a) x
      | some (p, true) =>
          (2 * Real.pi * (representativeFrequency p i : ℝ)) *
            realFourierModeAmbient N (realFourierModeIndexSwap a) x := by
  cases a with
  | none =>
      change fderiv ℝ (fun _ : Vec 2 => (1 : ℝ)) x (basisVec i) = 0
      simp
  | some q =>
      rcases q with ⟨p, sine⟩
      let k := representativeFrequency p
      let χ : Vec 2 → ℂ := fun y => torusCharacter (-k) y
      have hχ : ContDiff ℝ 1 χ := (torusCharacter_contDiff (-k)).of_le (by simp)
      have hcoeff :
          (-2 * Real.pi * Complex.I * ((-k i : ℤ) : ℂ)) =
            (2 * Real.pi * (k i : ℝ)) * Complex.I := by
        push_cast
        ring
      have hchar (y : Vec 2) : coordDeriv i χ y =
          ((2 * Real.pi * (k i : ℝ)) * Complex.I) * χ y := by
        rw [GalerkinModeCalculus.coordDeriv_torusCharacter]
        simpa [χ, k] using congrArg (fun c : ℂ => c * torusCharacter (-k) y) hcoeff
      cases sine with
      | false =>
          have hgrad := GalerkinModeCalculus.spaceGrad_const_smul
            (Complex.reCLM.contDiff.comp hχ) (Real.sqrt 2) i x
          have hgrad' : AVenhance.spaceGrad
              (fun y => Real.sqrt 2 * (χ y).re) x i =
              Real.sqrt 2 * AVenhance.spaceGrad (fun y => (χ y).re) x i := by
            simpa [Complex.reCLM, Function.comp_def] using hgrad
          rw [show realFourierModeAmbient N (some (p, false)) =
              fun y => Real.sqrt 2 * (χ y).re by rfl]
          rw [hgrad', GalerkinModeCalculus.spaceGrad_re_eq_coordDeriv hχ i x, hchar]
          simp [realFourierModeAmbient, realFourierModeIndexSwap, χ, k,
            Complex.mul_re, Complex.I_re, Complex.I_im]
          ring
      | true =>
          have hgrad := GalerkinModeCalculus.spaceGrad_const_smul
            (Complex.imCLM.contDiff.comp hχ) (Real.sqrt 2) i x
          have hgrad' : AVenhance.spaceGrad
              (fun y => Real.sqrt 2 * (χ y).im) x i =
              Real.sqrt 2 * AVenhance.spaceGrad (fun y => (χ y).im) x i := by
            simpa [Complex.imCLM, Function.comp_def] using hgrad
          rw [show realFourierModeAmbient N (some (p, true)) =
              fun y => Real.sqrt 2 * (χ y).im by rfl]
          rw [hgrad', GalerkinModeCalculus.spaceGrad_im_eq_coordDeriv hχ i x, hchar]
          simp [realFourierModeAmbient, realFourierModeIndexSwap, χ, k,
            Complex.mul_im, Complex.I_re, Complex.I_im]
          ring

/-- A finite real Fourier expansion written on Euclidean representatives. -/
def realFourierModeAmbientExpansion (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) : Vec 2 → ℝ :=
  fun x => ∑ j : Fin (RealFourierDimension N),
    c j * realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) x

theorem GalerkinModeCalculus.contDiff_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → Vec 2 → ℝ)
    (hf : ∀ i ∈ s, ContDiff ℝ ⊤ (f i)) :
    ContDiff ℝ ⊤ (fun x => ∑ i ∈ s, f i x) := by
  exact ContDiff.sum (s := s) (fun i hi => hf i hi)

theorem GalerkinModeCalculus.spaceGrad_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → Vec 2 → ℝ)
    (hf : ∀ i ∈ s, ContDiff ℝ ⊤ (f i))
    (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (fun y => s.sum (fun j => f j y)) x i =
      s.sum (fun j => AVenhance.spaceGrad (f j) x i) := by
  classical
  change (fderiv ℝ (fun y => ∑ j ∈ s, f j y) x) (basisVec i) = _
  rw [fderiv_fun_sum (fun j hj => (hf j hj).differentiable (by simp) x)]
  simp [AVenhance.spaceGrad]

theorem GalerkinModeCalculus.spaceGrad_realConstant_mul {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) (c : ℝ) (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (fun y => c * f y) x i =
      c * AVenhance.spaceGrad f x i := by
  change fderiv ℝ (c • f) x (basisVec i) = _
  rw [fderiv_const_smul (hf.differentiable (by norm_num) x) c]
  rfl

theorem realFourierModeAmbientExpansion_contDiff (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) :
    ContDiff ℝ ⊤ (realFourierModeAmbientExpansion N c) := by
  classical
  unfold realFourierModeAmbientExpansion
  apply GalerkinModeCalculus.contDiff_finset_sum Finset.univ
  intro j hj
  exact (contDiff_const : ContDiff ℝ ⊤ (fun _ : Vec 2 => (c j : ℝ))).mul
    (realFourierModeAmbient_contDiff N ((realFourierIndexEquivFin N).symm j))

/-- Differentiating a finite Fourier expansion multiplies each coefficient by its frequency and
replaces its cosine or sine mode with the paired mode. The result therefore stays in the same
cutoff space. -/
theorem spaceGrad_realFourierModeAmbientExpansion (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (realFourierModeAmbientExpansion N c) x i =
      ∑ j : Fin (RealFourierDimension N),
        c j * realFourierModeDerivativeScale ((realFourierIndexEquivFin N).symm j) i *
          realFourierModeAmbient N
            (realFourierModeIndexSwap ((realFourierIndexEquivFin N).symm j)) x := by
  classical
  unfold realFourierModeAmbientExpansion
  change AVenhance.spaceGrad
    (fun y => Finset.univ.sum (fun j : Fin (RealFourierDimension N) =>
      c j * realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) y)) x i = _
  rw [GalerkinModeCalculus.spaceGrad_finset_sum Finset.univ]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [GalerkinModeCalculus.spaceGrad_realConstant_mul
      ((realFourierModeAmbient_contDiff N ((realFourierIndexEquivFin N).symm j)).of_le
        (by exact le_top))]
    rw [spaceGrad_realFourierModeAmbient]
    simp only [realFourierModeDerivativeScale]
    split <;> simp_all <;> ring
  · intro j hj
    exact (contDiff_const : ContDiff ℝ ⊤ (fun _ : Vec 2 => (c j : ℝ))).mul
      (realFourierModeAmbient_contDiff N ((realFourierIndexEquivFin N).symm j))

/-- Sine-cosine exchange transported to the finite Galerkin index set. -/
def GalerkinModeCalculus.realFourierModeIndexSwapFinEquiv (N : ℕ) :
    Fin (RealFourierDimension N) ≃ Fin (RealFourierDimension N) where
  toFun j := realFourierIndexEquivFin N
    (realFourierModeIndexSwap ((realFourierIndexEquivFin N).symm j))
  invFun j := realFourierIndexEquivFin N
    (realFourierModeIndexSwap ((realFourierIndexEquivFin N).symm j))
  left_inv j := by
    change (realFourierIndexEquivFin N)
        (realFourierModeIndexSwap
          ((realFourierIndexEquivFin N).symm
            ((realFourierIndexEquivFin N)
              (realFourierModeIndexSwap ((realFourierIndexEquivFin N).symm j))))) = j
    rw [Equiv.symm_apply_apply, realFourierModeIndexSwap_involutive,
      Equiv.apply_symm_apply]
  right_inv j := by
    change (realFourierIndexEquivFin N)
        (realFourierModeIndexSwap
          ((realFourierIndexEquivFin N).symm
            ((realFourierIndexEquivFin N)
              (realFourierModeIndexSwap ((realFourierIndexEquivFin N).symm j))))) = j
    rw [Equiv.symm_apply_apply, realFourierModeIndexSwap_involutive,
      Equiv.apply_symm_apply]

/-- Coefficients of the coordinate derivative of a finite Fourier expansion. -/
def realFourierModeDerivativeCoefficients (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) (i : Fin 2) :
    Coefficients (RealFourierDimension N) :=
  WithLp.toLp 2 (fun j =>
    c (realFourierIndexEquivFin N
      (realFourierModeIndexSwap ((realFourierIndexEquivFin N).symm j))) *
      realFourierModeDerivativeScale
        (realFourierModeIndexSwap ((realFourierIndexEquivFin N).symm j)) i)

/-- Coordinate derivatives of a finite real Fourier expansion are represented by the explicit
coefficient derivative map, without leaving the cutoff space. -/
theorem spaceGrad_realFourierModeAmbientExpansion_eq_derivativeExpansion (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) (i : Fin 2) :
    (fun x => AVenhance.spaceGrad (realFourierModeAmbientExpansion N c) x i) =
      realFourierModeAmbientExpansion N (realFourierModeDerivativeCoefficients N c i) := by
  funext x
  rw [spaceGrad_realFourierModeAmbientExpansion]
  unfold realFourierModeAmbientExpansion realFourierModeDerivativeCoefficients
  have hsum := Fintype.sum_equiv (GalerkinModeCalculus.realFourierModeIndexSwapFinEquiv N)
    (fun j =>
      (c (GalerkinModeCalculus.realFourierModeIndexSwapFinEquiv N j) *
        realFourierModeDerivativeScale
          ((realFourierIndexEquivFin N).symm
              (GalerkinModeCalculus.realFourierModeIndexSwapFinEquiv N j)) i) *
        realFourierModeAmbient N
          ((realFourierIndexEquivFin N).symm j) x)
    (fun j =>
      c j * realFourierModeDerivativeScale
        ((realFourierIndexEquivFin N).symm j) i *
        realFourierModeAmbient N
          (realFourierModeIndexSwap ((realFourierIndexEquivFin N).symm j)) x)
    (by
      intro j
      simp [GalerkinModeCalculus.realFourierModeIndexSwapFinEquiv,
          realFourierModeIndexSwap_involutive])
  simpa [GalerkinModeCalculus.realFourierModeIndexSwapFinEquiv,
      realFourierModeIndexSwap_involutive] using hsum.symm

theorem GalerkinModeCalculus.coefficient_norm_sq_eq_sum_sq {n : ℕ} (c : Coefficients n) :
    ‖c‖ ^ 2 = ∑ j : Fin n, (c j) ^ 2 := by
  calc
    ‖c‖ ^ 2 = inner ℝ c c := (real_inner_self_eq_norm_sq c).symm
    _ = ∑ j : Fin n, (c j) ^ 2 := by
      rw [PiLp.inner_apply]
      simp [pow_two]

/-- The coordinate derivative map has the expected cutoff-dependent Fourier multiplier bound.
The differentiated-energy estimates below will remove this frequency factor by measuring one more
spatial derivative. -/
theorem realFourierModeDerivativeCoefficients_norm_le (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) (i : Fin 2) :
    ‖realFourierModeDerivativeCoefficients N c i‖ ≤
      (2 * Real.pi * N) * ‖c‖ := by
  let L : ℝ := 2 * Real.pi * N
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hpoint (j : Fin (RealFourierDimension N)) :
      |realFourierModeDerivativeCoefficients N c i j| ≤
        L * |c (GalerkinModeCalculus.realFourierModeIndexSwapFinEquiv N j)| := by
    rw [realFourierModeDerivativeCoefficients, PiLp.toLp_apply]
    calc
      |c (realFourierIndexEquivFin N
          (realFourierModeIndexSwap ((realFourierIndexEquivFin N).symm j))) *
          realFourierModeDerivativeScale
            (realFourierModeIndexSwap ((realFourierIndexEquivFin N).symm j)) i| =
          |c (GalerkinModeCalculus.realFourierModeIndexSwapFinEquiv N j)| *
            |realFourierModeDerivativeScale
              (realFourierModeIndexSwap ((realFourierIndexEquivFin N).symm j)) i| := by
            simp [GalerkinModeCalculus.realFourierModeIndexSwapFinEquiv, abs_mul]
      _ ≤ |c (GalerkinModeCalculus.realFourierModeIndexSwapFinEquiv N j)| * L :=
        mul_le_mul_of_nonneg_left
          (realFourierModeDerivativeScale_abs_le N _ i) (abs_nonneg _)
      _ = L * |c (GalerkinModeCalculus.realFourierModeIndexSwapFinEquiv N j)| := by ring
  have hpointSq (j : Fin (RealFourierDimension N)) :
      (realFourierModeDerivativeCoefficients N c i j) ^ 2 ≤
        (L * |c (GalerkinModeCalculus.realFourierModeIndexSwapFinEquiv N j)|) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hL (abs_nonneg _))).2 (hpoint j)
    simpa [sq_abs] using h
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hpointSq j
  have hperm := Fintype.sum_equiv (GalerkinModeCalculus.realFourierModeIndexSwapFinEquiv N)
    (fun j : Fin (RealFourierDimension N) =>
      (c (GalerkinModeCalculus.realFourierModeIndexSwapFinEquiv N j)) ^ 2)
    (fun j => (c j) ^ 2) (by intro j; rfl)
  have hsq :
      ‖realFourierModeDerivativeCoefficients N c i‖ ^ 2 ≤ (L * ‖c‖) ^ 2 := by
    rw [GalerkinModeCalculus.coefficient_norm_sq_eq_sum_sq]
    calc
      ∑ j : Fin (RealFourierDimension N),
          (realFourierModeDerivativeCoefficients N c i j) ^ 2 ≤
        ∑ j : Fin (RealFourierDimension N),
          (L * |c (GalerkinModeCalculus.realFourierModeIndexSwapFinEquiv N j)|) ^ 2 := hsum
      _ = L ^ 2 * ∑ j : Fin (RealFourierDimension N),
          (c (GalerkinModeCalculus.realFourierModeIndexSwapFinEquiv N j)) ^ 2 := by
        simp_rw [mul_pow, sq_abs]
        rw [← Finset.mul_sum]
      _ = L ^ 2 * ∑ j : Fin (RealFourierDimension N), (c j) ^ 2 := by
        rw [hperm]
      _ = (L * ‖c‖) ^ 2 := by
        rw [← GalerkinModeCalculus.coefficient_norm_sq_eq_sum_sq c]
        ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).1 hsq

/-- Coordinate differentiation of Fourier coefficients as a linear map. -/
def GalerkinModeCalculus.realFourierModeDerivativeLinearMap (N : ℕ) (i : Fin 2) :
    Coefficients (RealFourierDimension N) →ₗ[ℝ]
      Coefficients (RealFourierDimension N) where
  toFun := fun c => realFourierModeDerivativeCoefficients N c i
  map_add' := by
    intro c d
    ext j
    simp [realFourierModeDerivativeCoefficients, add_mul]
  map_smul' := by
    intro r c
    ext j
    simp [realFourierModeDerivativeCoefficients, mul_assoc]

/-- The coordinate derivative on the finite Fourier coefficient space as a continuous linear map.
Its operator norm is bounded by the largest retained frequency. -/
def realFourierModeDerivativeMap (N : ℕ) (i : Fin 2) :
    Coefficients (RealFourierDimension N) →L[ℝ]
      Coefficients (RealFourierDimension N) :=
  LinearMap.mkContinuous (GalerkinModeCalculus.realFourierModeDerivativeLinearMap N i) (2 *
      Real.pi * N)
    (realFourierModeDerivativeCoefficients_norm_le N · i)

@[simp]
theorem realFourierModeDerivativeMap_apply (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) (i : Fin 2) :
    realFourierModeDerivativeMap N i c = realFourierModeDerivativeCoefficients N c i := rfl

/-- The coefficient transform for an ordered word of coordinate derivatives. -/
def realFourierWordDerivativeCoefficients (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) : List (Fin 2) →
      Coefficients (RealFourierDimension N)
  | [] => c
  | i :: w => realFourierModeDerivativeCoefficients N
      (realFourierWordDerivativeCoefficients N c w) i

/-- The bounded linear map on Fourier coefficients associated with a derivative word. -/
def realFourierWordDerivativeMap (N : ℕ) : List (Fin 2) →
    Coefficients (RealFourierDimension N) →L[ℝ]
      Coefficients (RealFourierDimension N)
  | [] => ContinuousLinearMap.id ℝ _
  | i :: w => (realFourierModeDerivativeMap N i).comp
      (realFourierWordDerivativeMap N w)

@[simp]
theorem realFourierWordDerivativeMap_apply (N : ℕ)
    (w : List (Fin 2)) (c : Coefficients (RealFourierDimension N)) :
    realFourierWordDerivativeMap N w c = realFourierWordDerivativeCoefficients N c w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      simp [realFourierWordDerivativeMap, realFourierWordDerivativeCoefficients, ih]

/-- Every ordered spatial derivative of a finite Fourier expansion remains in its original
cutoff, with coefficients given by the corresponding word derivative map. -/
theorem classicalWordDerivative_realFourierModeAmbientExpansion (N : ℕ)
    (w : List (Fin 2)) (c : Coefficients (RealFourierDimension N)) :
    classicalWordDerivative w (realFourierModeAmbientExpansion N c) =
      realFourierModeAmbientExpansion N (realFourierWordDerivativeCoefficients N c w) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      funext x
      change AVenhance.spaceGrad
        (classicalWordDerivative w (realFourierModeAmbientExpansion N c)) x i = _
      rw [ih]
      simpa [realFourierWordDerivativeCoefficients] using
        congrFun (spaceGrad_realFourierModeAmbientExpansion_eq_derivativeExpansion N
          (realFourierWordDerivativeCoefficients N c w) i) x

/-- Product of the normalized Haar measures on the two circle factors. -/
noncomputable def GalerkinModeCalculus.standardUnitTorusVolume : Measure Torus :=
  Measure.pi (fun _ : Fin 2 => AddCircle.haarAddCircle)

theorem GalerkinModeCalculus.galerkinTorusVolume_eq_standard :
    (volume : Measure Torus) = GalerkinModeCalculus.standardUnitTorusVolume := by
  rfl

theorem GalerkinModeCalculus.integral_periodicToTorus_mul_eq_unitCell {f g : Vec 2 → ℝ} :
    (∫ x : Torus, AVenhance.Infra.Torus.periodicToTorus f x *
        AVenhance.Infra.Torus.periodicToTorus g x) =
      ∫ x in AVenhance.Infra.Torus.unitCell 2, f x * g x := by
  have hfun : (fun x : Torus =>
      AVenhance.Infra.Torus.periodicToTorus f x *
        AVenhance.Infra.Torus.periodicToTorus g x) =
      AVenhance.Infra.Torus.periodicToTorus (fun x => f x * g x) := by
    funext x
    rfl
  rw [hfun]
  calc
    (∫ x : Torus,
        AVenhance.Infra.Torus.periodicToTorus (fun x : Vec 2 => f x * g x) x) =
        ∫ x : Torus,
          AVenhance.Infra.Torus.periodicToTorus (fun x : Vec 2 => f x * g x) x
            ∂GalerkinModeCalculus.standardUnitTorusVolume := by rw
                [GalerkinModeCalculus.galerkinTorusVolume_eq_standard]
    _ = ∫ x in AVenhance.Infra.Torus.unitCell 2, f x * g x := by
      exact AVenhance.Infra.Torus.integral_periodicToTorus_eq_unitCell
        (fun x : Vec 2 => f x * g x)

/-- Fourier projection commutes with a coordinate derivative. The weak gradient identity follows
from periodic integration by parts and the fact that differentiating a retained mode stays in the
same cutoff. -/
theorem realFourierModeDerivativeCoefficients_projection (N : ℕ)
    (f : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hper : AVenhance.IsZ2Periodic f)
    (i : Fin 2) :
    realFourierModeDerivativeCoefficients N
        (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus f)) i =
      modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus (fun x => AVenhance.spaceGrad f x i)) := by
  classical
  ext j
  let a := (realFourierIndexEquivFin N).symm j
  have hIBP := integral_unitCell_coord_ibp_real i
    ((realFourierModeAmbient_contDiff N a).of_le (by simp)) (hf.of_le (by simp))
    (realFourierModeAmbient_periodic N a) hper
  have hscale := realFourierModeDerivativeScale_swap N a i
  have hderiv (x : Vec 2) := spaceGrad_realFourierModeAmbient N a i x
  simp only [realFourierModeDerivativeCoefficients, PiLp.toLp_apply,
    modeProjectionCoefficients, PiLp.toLp_apply]
  change (∫ x : Torus, AVenhance.Infra.Torus.periodicToTorus f x *
      realFourierModeFin N (GalerkinModeCalculus.realFourierModeIndexSwapFinEquiv N j) x) *
        realFourierModeDerivativeScale (realFourierModeIndexSwap a) i =
    ∫ x : Torus,
      AVenhance.Infra.Torus.periodicToTorus (fun y => AVenhance.spaceGrad f y i) x *
        realFourierModeFin N j x
  have hleft : (∫ x : Torus,
        AVenhance.Infra.Torus.periodicToTorus (fun y => AVenhance.spaceGrad f y i) x *
          realFourierModeFin N j x) =
        ∫ x in AVenhance.Infra.Torus.unitCell 2,
          AVenhance.spaceGrad f x i * realFourierModeAmbient N a x := by
      simpa [realFourierModeFin_eq_periodicToTorus, a] using
        (GalerkinModeCalculus.integral_periodicToTorus_mul_eq_unitCell
          (f := fun x => AVenhance.spaceGrad f x i)
          (g := realFourierModeAmbient N a))
  have hright : (∫ x : Torus, AVenhance.Infra.Torus.periodicToTorus f x *
        realFourierModeFin N (GalerkinModeCalculus.realFourierModeIndexSwapFinEquiv N j) x) =
        ∫ x in AVenhance.Infra.Torus.unitCell 2,
          f x * realFourierModeAmbient N (realFourierModeIndexSwap a) x := by
      simpa [realFourierModeFin_eq_periodicToTorus,
        GalerkinModeCalculus.realFourierModeIndexSwapFinEquiv, a] using
        (GalerkinModeCalculus.integral_periodicToTorus_mul_eq_unitCell
          (f := f)
          (g := realFourierModeAmbient N (realFourierModeIndexSwap a)))
  have hcomm :
        (fun x => AVenhance.spaceGrad f x i * realFourierModeAmbient N a x) =
          fun x => realFourierModeAmbient N a x * AVenhance.spaceGrad f x i := by
      funext x
      ring
  have hscaled :
        (∫ x in AVenhance.Infra.Torus.unitCell 2,
            AVenhance.spaceGrad (realFourierModeAmbient N a) x i * f x) =
          realFourierModeDerivativeScale a i *
            ∫ x in AVenhance.Infra.Torus.unitCell 2,
              f x * realFourierModeAmbient N (realFourierModeIndexSwap a) x := by
      have hfun : (fun x =>
          AVenhance.spaceGrad (realFourierModeAmbient N a) x i * f x) =
          fun x => realFourierModeDerivativeScale a i *
            (f x * realFourierModeAmbient N (realFourierModeIndexSwap a) x) := by
        funext x
        rw [hderiv x]
        cases a with
        | none => simp [realFourierModeDerivativeScale]
        | some q =>
            rcases q with ⟨p, sine⟩
            cases sine <;> simp [realFourierModeDerivativeScale] <;> ring
      calc
        (∫ x in AVenhance.Infra.Torus.unitCell 2,
            AVenhance.spaceGrad (realFourierModeAmbient N a) x i * f x) =
            ∫ x in AVenhance.Infra.Torus.unitCell 2,
              realFourierModeDerivativeScale a i *
                (f x * realFourierModeAmbient N (realFourierModeIndexSwap a) x) := by
                  rw [hfun]
        _ = realFourierModeDerivativeScale a i *
            ∫ x in AVenhance.Infra.Torus.unitCell 2,
              f x * realFourierModeAmbient N (realFourierModeIndexSwap a) x := by
                simp only [MeasureTheory.integral_const_mul]
  have hcell :
        (∫ x in AVenhance.Infra.Torus.unitCell 2,
            AVenhance.spaceGrad f x i * realFourierModeAmbient N a x) =
          realFourierModeDerivativeScale (realFourierModeIndexSwap a) i *
            ∫ x in AVenhance.Infra.Torus.unitCell 2,
              f x * realFourierModeAmbient N (realFourierModeIndexSwap a) x := by
      calc
        _ = ∫ x in AVenhance.Infra.Torus.unitCell 2,
            realFourierModeAmbient N a x * AVenhance.spaceGrad f x i := by
              rw [hcomm]
        _ = -(∫ x in AVenhance.Infra.Torus.unitCell 2,
            AVenhance.spaceGrad (realFourierModeAmbient N a) x i * f x) := hIBP
        _ = realFourierModeDerivativeScale (realFourierModeIndexSwap a) i *
            ∫ x in AVenhance.Infra.Torus.unitCell 2,
              f x * realFourierModeAmbient N (realFourierModeIndexSwap a) x := by
              rw [hscaled, hscale]
              ring
  calc
    _ = realFourierModeDerivativeScale (realFourierModeIndexSwap a) i *
        ∫ x in AVenhance.Infra.Torus.unitCell 2,
          f x * realFourierModeAmbient N (realFourierModeIndexSwap a) x := by
          rw [hright]
          ring
    _ = ∫ x in AVenhance.Infra.Torus.unitCell 2,
        AVenhance.spaceGrad f x i * realFourierModeAmbient N a x := hcell.symm
    _ = ∫ x : Torus,
        AVenhance.Infra.Torus.periodicToTorus (fun y => AVenhance.spaceGrad f y i) x *
          realFourierModeFin N j x := hleft.symm

end AVenhance.Infra.Classical

end
