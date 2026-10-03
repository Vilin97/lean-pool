/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.FluxStructure
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Explicit spatial derivatives of the single-mode correctors. -/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Section3

theorem CorrectorGradient.spaceGrad_cosCoordinate (A ω : ℝ) (i j : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (fun y => A * Real.cos (ω * y i)) x j =
      if j = i then -A * ω * Real.sin (ω * x i) else 0 := by
  unfold AVenhance.spaceGrad
  have hproj : HasFDerivAt (fun y : Vec 2 => y i)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i) x :=
    hasFDerivAt_apply (𝕜 := ℝ) i x
  have hlin : HasFDerivAt (fun y : Vec 2 => ω * y i)
      (ω • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i) x := by
    exact hproj.const_mul ω
  have hcos := (Real.hasDerivAt_cos (ω * x i)).comp_hasFDerivAt x hlin
  have hfun := hcos.const_mul A
  have hderiv : fderiv ℝ (fun y : Vec 2 => A * Real.cos (ω * y i)) x =
      A • (-Real.sin (ω * x i)) • ω •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i := by
    simpa only [Function.comp_apply] using hfun.fderiv
  rw [hderiv]
  by_cases hji : j = i
  · subst j
    simp only [smul_apply, ContinuousLinearMap.proj_apply, basisVec_apply,
      ite_true]
    ring
  · have hij : i ≠ j := Ne.symm hji
    simp only [smul_apply, ContinuousLinearMap.proj_apply, basisVec_apply,
      hji, hij, ite_false, smul_zero]

theorem CorrectorGradient.freq_eq (ε x : ℝ) (hε : ε ≠ 0) :
    (2 * Real.pi / ε) * x = 2 * Real.pi * x / ε := by
  field_simp [hε]

/-- The nonzero corrector derivative for a horizontal odd shear. -/
theorem chiMK_spaceGrad_one {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (κ : ℝ) (k : ℤ) (t : ℝ) (x : Vec 2)
    (hk : k % 4 = 1) (hε : AVenhance.epsilon β I.Λ m ≠ 0) :
    AVenhance.spaceGrad (fun y => I.chiMK κ m k t y 1) x 0 =
      4 * Real.pi ^ 2 * AVenhance.a β I.Λ m * I.corrTime κ m k t *
        Real.sin (2 * Real.pi * x 0 / AVenhance.epsilon β I.Λ m) := by
  let ε := AVenhance.epsilon β I.Λ m
  let ω := 2 * Real.pi / ε
  let A := -(I.corrTime κ m k t * (2 * Real.pi * AVenhance.a β I.Λ m * ε))
  have hfun : (fun y : Vec 2 => I.chiMK κ m k t y 1) =
      fun y => A * Real.cos (ω * y 0) := by
    funext y
    simp [A, ω, ε, AVenhance.Ingredients.chiMK, AVenhance.uShear, hk,
      CorrectorGradient.freq_eq ε (y 0) hε]
    ring
  rw [hfun, CorrectorGradient.spaceGrad_cosCoordinate]
  have hfreq := CorrectorGradient.freq_eq ε (x 0) hε
  simp only [↓reduceIte]
  rw [hfreq]
  dsimp [A, ω, ε]
  field_simp [hε]
  ring

/-- The full coordinate derivative formula for the horizontal component of an
active horizontal shear. -/
theorem chiMK_spaceGrad_one_all {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (κ : ℝ) (k : ℤ) (t : ℝ) (x : Vec 2) (j : Fin 2)
    (hk : k % 4 = 1) (hε : AVenhance.epsilon β I.Λ m ≠ 0) :
    AVenhance.spaceGrad (fun y => I.chiMK κ m k t y 1) x j =
      if j = 0 then
        4 * Real.pi ^ 2 * AVenhance.a β I.Λ m * I.corrTime κ m k t *
          Real.sin (2 * Real.pi * x 0 / AVenhance.epsilon β I.Λ m)
      else 0 := by
  let ε := AVenhance.epsilon β I.Λ m
  let ω := 2 * Real.pi / ε
  let A := -(I.corrTime κ m k t * (2 * Real.pi * AVenhance.a β I.Λ m * ε))
  have hfun : (fun y : Vec 2 => I.chiMK κ m k t y 1) =
      fun y => A * Real.cos (ω * y 0) := by
    funext y
    simp [A, ω, ε, AVenhance.Ingredients.chiMK, AVenhance.uShear, hk,
      CorrectorGradient.freq_eq ε (y 0) hε]
    ring
  rw [hfun, CorrectorGradient.spaceGrad_cosCoordinate]
  by_cases hj : j = 0
  · subst j
    rw [CorrectorGradient.freq_eq ε (x 0) hε]
    dsimp [A, ω, ε]
    field_simp [hε]
    ring
  · simp [hj]

/-- The nonzero corrector derivative for a vertical odd shear. -/
theorem chiMK_spaceGrad_three {β : ℝ}
    (I : AVenhance.Ingredients β) {m : ℕ} (κ : ℝ) (k : ℤ) (t : ℝ)
    (x : Vec 2) (hk : k % 4 = 3)
    (hε : AVenhance.epsilon β I.Λ m ≠ 0) :
    AVenhance.spaceGrad (fun y => I.chiMK κ m k t y 0) x 1 =
      -(4 * Real.pi ^ 2 * AVenhance.a β I.Λ m * I.corrTime κ m k t) *
        Real.sin (2 * Real.pi * x 1 / AVenhance.epsilon β I.Λ m) := by
  let ε := AVenhance.epsilon β I.Λ m
  let ω := 2 * Real.pi / ε
  let A := I.corrTime κ m k t * (2 * Real.pi * AVenhance.a β I.Λ m * ε)
  have hfun : (fun y : Vec 2 => I.chiMK κ m k t y 0) =
      fun y => A * Real.cos (ω * y 1) := by
    funext y
    simp [A, ω, ε, AVenhance.Ingredients.chiMK, AVenhance.uShear, hk,
      CorrectorGradient.freq_eq ε (y 1) hε]
    ring
  rw [hfun, CorrectorGradient.spaceGrad_cosCoordinate]
  have hfreq := CorrectorGradient.freq_eq ε (x 1) hε
  simp only [↓reduceIte]
  rw [hfreq]
  dsimp [A, ω, ε]
  field_simp [hε]
  ring

/-- The full coordinate derivative formula for the vertical component of an
active vertical shear. -/
theorem chiMK_spaceGrad_three_all {β : ℝ}
    (I : AVenhance.Ingredients β) {m : ℕ} (κ : ℝ) (k : ℤ) (t : ℝ)
    (x : Vec 2) (j : Fin 2) (hk : k % 4 = 3)
    (hε : AVenhance.epsilon β I.Λ m ≠ 0) :
    AVenhance.spaceGrad (fun y => I.chiMK κ m k t y 0) x j =
      if j = 1 then
        -(4 * Real.pi ^ 2 * AVenhance.a β I.Λ m * I.corrTime κ m k t) *
          Real.sin (2 * Real.pi * x 1 / AVenhance.epsilon β I.Λ m)
      else 0 := by
  let ε := AVenhance.epsilon β I.Λ m
  let ω := 2 * Real.pi / ε
  let A := I.corrTime κ m k t * (2 * Real.pi * AVenhance.a β I.Λ m * ε)
  have hfun : (fun y : Vec 2 => I.chiMK κ m k t y 0) =
      fun y => A * Real.cos (ω * y 1) := by
    funext y
    simp [A, ω, ε, AVenhance.Ingredients.chiMK, AVenhance.uShear, hk,
      CorrectorGradient.freq_eq ε (y 1) hε]
    ring
  rw [hfun, CorrectorGradient.spaceGrad_cosCoordinate]
  by_cases hj : j = 1
  · subst j
    rw [CorrectorGradient.freq_eq ε (x 1) hε]
    dsimp [A, ω, ε]
    field_simp [hε]
    ring
  · simp [hj]

end AVenhance.Infra.Section3
