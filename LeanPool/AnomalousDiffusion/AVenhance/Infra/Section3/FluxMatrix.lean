/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ChiMRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ActiveModeFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.CutoffSymmetry
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.CorrectorBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.Flux

/-! Matrix entry calculations for the explicit active-mode flux. -/

@[expose] public section

noncomputable section

open MeasureTheory
open Homogenization

namespace AVenhance.Infra.Section3

open AVenhance

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def FluxMatrix.closedUnitSquare : Set (Vec 2) :=
  Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

theorem FluxMatrix.continuous_integrableOn_unitCell {f : Vec 2 → ℝ}
    (hf : Continuous f) : IntegrableOn f (AVenhance.Infra.Torus.unitCell 2) := by
  have hcompact : IsCompact FluxMatrix.closedUnitSquare := by
    simpa [FluxMatrix.closedUnitSquare] using
      (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)
  have hsubset : AVenhance.Infra.Torus.unitCell 2 ⊆ FluxMatrix.closedUnitSquare := by
    intro x hx
    simp only [AVenhance.Infra.Torus.unitCell,
      AVenhance.Infra.Torus.unitCellAt, Set.mem_ofPred_eq] at hx
    simp only [FluxMatrix.closedUnitSquare, Set.mem_pi]
    intro i _hi
    exact ⟨le_of_lt (hx i).1, by simpa only [zero_add] using (hx i).2⟩
  exact (hf.continuousOn.integrableOn_compact hcompact).mono_set hsubset

theorem FluxMatrix.spaceAvg_add_of_continuous {f g : Vec 2 → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    spaceAvg (fun x => f x + g x) = spaceAvg f + spaceAvg g := by
  unfold spaceAvg
  rw [← AVenhance.Infra.Torus.integral_unitCell_eq_unitCube (fun x => f x + g x),
    ← AVenhance.Infra.Torus.integral_unitCell_eq_unitCube f,
    ← AVenhance.Infra.Torus.integral_unitCell_eq_unitCube g]
  rw [integral_add (FluxMatrix.continuous_integrableOn_unitCell hf)
    (FluxMatrix.continuous_integrableOn_unitCell hg)]

theorem FluxMatrix.spaceAvg_sub_of_continuous {f g : Vec 2 → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    spaceAvg (fun x => f x - g x) = spaceAvg f - spaceAvg g := by
  unfold spaceAvg
  rw [← AVenhance.Infra.Torus.integral_unitCell_eq_unitCube (fun x => f x - g x),
    ← AVenhance.Infra.Torus.integral_unitCell_eq_unitCube f,
    ← AVenhance.Infra.Torus.integral_unitCell_eq_unitCube g]
  rw [integral_sub (FluxMatrix.continuous_integrableOn_unitCell hf)
    (FluxMatrix.continuous_integrableOn_unitCell hg)]

theorem FluxMatrix.spaceAvg_const_eq (c : ℝ) :
    spaceAvg (fun _ : Vec 2 => c) = c := by
  unfold spaceAvg
  rw [← AVenhance.Infra.Torus.integral_unitCell_eq_unitCube]
  rw [setIntegral_const]
  have hcell : AVenhance.Infra.Torus.unitCell 2 =
      Set.pi Set.univ (fun _ : Fin 2 => Set.Ioc (0 : ℝ) 1) := by
    ext x
    simp [AVenhance.Infra.Torus.unitCell,
      AVenhance.Infra.Torus.unitCellAt, Set.pi]
  have hmeasure : (volume : Measure (Vec 2))
      (AVenhance.Infra.Torus.unitCell 2) = 1 := by
    rw [hcell, volume_pi_pi]
    simp
  change (((volume : Measure (Vec 2))
    (AVenhance.Infra.Torus.unitCell 2)).toReal) • c = c
  rw [hmeasure]
  norm_num

theorem FluxMatrix.spaceAvg_const_mul (c : ℝ) (f : Vec 2 → ℝ) :
    spaceAvg (fun x => c * f x) = c * spaceAvg f := by
  unfold spaceAvg
  rw [integral_const_mul]

theorem FluxMatrix.chiMK_horizontal_zero_component {β : ℝ}
    (I : Ingredients β) {m : ℕ} (κ : ℝ) (k : ℤ) (t : ℝ)
    (hk : k % 4 = 1) :
    (fun x : Vec 2 => I.chiMK κ m k t x 0) = fun _ => 0 := by
  funext x
  simp [Ingredients.chiMK, uShear, hk]

theorem FluxMatrix.chiMK_vertical_zero_component {β : ℝ}
    (I : Ingredients β) {m : ℕ} (κ : ℝ) (k : ℤ) (t : ℝ)
    (hk : k % 4 = 3) :
    (fun x : Vec 2 => I.chiMK κ m k t x 1) = fun _ => 0 := by
  funext x
  simp [Ingredients.chiMK, uShear, hk]

/-- Entries of the gradient matrix for a horizontal active corrector mode. -/
theorem chiMK_gradMatrix_one_entries {β : ℝ} (I : Ingredients β)
    {m : ℕ} (κ : ℝ) (k : ℤ) (t : ℝ) (x : Vec 2)
    (hk : k % 4 = 1) (hε : epsilon β I.Λ m ≠ 0) :
    gradMatrix (fun y => I.chiMK κ m k t y) x 0 0 = 0 ∧
    gradMatrix (fun y => I.chiMK κ m k t y) x 0 1 =
      4 * Real.pi ^ 2 * a β I.Λ m * I.corrTime κ m k t *
        Real.sin (2 * Real.pi * x 0 / epsilon β I.Λ m) ∧
    gradMatrix (fun y => I.chiMK κ m k t y) x 1 0 = 0 ∧
    gradMatrix (fun y => I.chiMK κ m k t y) x 1 1 = 0 := by
  have hz := FluxMatrix.chiMK_horizontal_zero_component (m := m) I κ k t hk
  have hactive := chiMK_spaceGrad_one_all I κ k t x 0 hk hε
  have hother := chiMK_spaceGrad_one_all I κ k t x 1 hk hε
  refine ⟨?_, ?_, ?_, ?_⟩
  · change spaceGrad (fun y => I.chiMK κ m k t y 0) x 0 = 0
    rw [hz]
    simp [spaceGrad]
  · change spaceGrad (fun y => I.chiMK κ m k t y 1) x 0 = _
    simpa using hactive
  · change spaceGrad (fun y => I.chiMK κ m k t y 0) x 1 = 0
    rw [hz]
    simp [spaceGrad]
  · change spaceGrad (fun y => I.chiMK κ m k t y 1) x 1 = 0
    simpa using hother

/-- Entries of the gradient matrix for a vertical active corrector mode. -/
theorem chiMK_gradMatrix_three_entries {β : ℝ} (I : Ingredients β)
    {m : ℕ} (κ : ℝ) (k : ℤ) (t : ℝ) (x : Vec 2)
    (hk : k % 4 = 3) (hε : epsilon β I.Λ m ≠ 0) :
    gradMatrix (fun y => I.chiMK κ m k t y) x 0 0 = 0 ∧
    gradMatrix (fun y => I.chiMK κ m k t y) x 0 1 = 0 ∧
    gradMatrix (fun y => I.chiMK κ m k t y) x 1 0 =
      -(4 * Real.pi ^ 2 * a β I.Λ m * I.corrTime κ m k t) *
        Real.sin (2 * Real.pi * x 1 / epsilon β I.Λ m) ∧
    gradMatrix (fun y => I.chiMK κ m k t y) x 1 1 = 0 := by
  have hz := FluxMatrix.chiMK_vertical_zero_component (m := m) I κ k t hk
  have hother := chiMK_spaceGrad_three_all I κ k t x 0 hk hε
  have hactive := chiMK_spaceGrad_three_all I κ k t x 1 hk hε
  refine ⟨?_, ?_, ?_, ?_⟩
  · change spaceGrad (fun y => I.chiMK κ m k t y 0) x 0 = 0
    simpa using hother
  · change spaceGrad (fun y => I.chiMK κ m k t y 1) x 0 = 0
    rw [hz]
    simp [spaceGrad]
  · change spaceGrad (fun y => I.chiMK κ m k t y 0) x 1 = _
    simpa using hactive
  · change spaceGrad (fun y => I.chiMK κ m k t y 1) x 1 = 0
    rw [hz]
    simp [spaceGrad]

/-- A single shear mode has zero spatial mean. -/
theorem spaceAvg_psi_eq_zero {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (k : ℤ) (hk : k % 4 = 1 ∨ k % 4 = 3) :
    spaceAvg (psi β I.Λ m k) = 0 := by
  have hfreq (z : ℝ) :
      (2 * Real.pi / epsilon β I.Λ m) * z =
        2 * Real.pi * (epsilon β I.Λ m)⁻¹ * z := by
    ring
  have hfun : (psi β I.Λ m k) = fun x =>
      a β I.Λ m * epsilon β I.Λ m ^ 2 *
        Real.sin (2 * Real.pi * (epsilon β I.Λ m)⁻¹ *
          x (if k % 4 = 1 then 0 else 1)) := by
    funext x
    rw [psi_sineCoordinate]
    rcases hk with h1 | h3
    · simp only [ite_eq_left h1]
      rw [hfreq]
    · have hnot1 : k % 4 ≠ 1 := by omega
      simp only [ite_eq_right hnot1, ite_eq_left h3]
      rw [hfreq]
  rw [hfun]
  unfold spaceAvg
  rw [integral_const_mul]
  rcases hk with h1 | h3
  · have hcoord : (if k % 4 = 1 then (0 : Fin 2) else 1) = 0 := by simp [h1]
    rw [hcoord]
    have havg := spaceAvg_sin_epsilon I hm 0
    unfold spaceAvg at havg
    rw [havg]
    ring
  · have hnot1 : k % 4 ≠ 1 := by omega
    have hcoord : (if k % 4 = 1 then (0 : Fin 2) else 1) = 1 := by simp [hnot1]
    rw [hcoord]
    have havg := spaceAvg_sin_epsilon I hm 1
    unfold spaceAvg at havg
    rw [havg]
    ring

theorem FluxMatrix.psiM_eq_active_mode {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (k : ℤ) (t : ℝ) (hk : Odd k)
    (hzk : I.zetaMK m k t ≠ 0) :
    (fun x : Vec 2 => I.psiM m t x) =
      fun x => I.zetaProd m k t * psi β I.Λ m k x := by
  funext x
  exact psiM_eq_single_of_zetaMK_ne_zero I hm (k := k) hk t x hzk

theorem FluxMatrix.chiM_eq_active_mode {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (κ : ℝ) (k : ℤ) (t : ℝ) (hk : Odd k)
    (hzk : I.zetaMK m k t ≠ 0) :
    I.chiM κ m t = fun x => I.chiMK κ m k t x := by
  funext x
  exact chiM_eq_chiMK_of_zetaMK_ne_zero I hm κ (k := k) hk t x hzk

/-- The full flux integrand on an active horizontal mode, entry by entry. -/
theorem FluxMatrix.fluxIntegrand_active_one_matrix {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (k : ℤ) (t : ℝ)
    (hk : k % 4 = 1) (hzk : I.zetaMK m k t ≠ 0) (x : Vec 2) :
    I.fluxIntegrand κ m t x = Matrix.of (fun i j =>
      if i = 0 then
        if j = 0 then κ else
          κ * spaceGrad (fun y => I.chiMK κ m k t y 1) x 0 -
            I.zetaProd m k t * psi β I.Λ m k x
      else if j = 0 then I.zetaProd m k t * psi β I.Λ m k x else
        κ + I.zetaProd m k t * psi β I.Λ m k x *
          spaceGrad (fun y => I.chiMK κ m k t y 1) x 0) := by
  have hodd : Odd k := by
    rcases Int.even_or_odd k with heven | hodd
    · rcases heven with ⟨z, hz⟩
      omega
    · exact hodd
  have hpsi := FluxMatrix.psiM_eq_active_mode I hm k t hodd hzk
  have hchi := FluxMatrix.chiM_eq_active_mode I hm κ k t hodd hzk
  have hε : epsilon β I.Λ m ≠ 0 :=
    ne_of_gt (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le)
  have hg := chiMK_gradMatrix_one_entries I κ k t x hk hε
  rcases hg with ⟨h00, h01, h10, h11⟩
  rw [Ingredients.fluxIntegrand, congrFun hpsi x, hchi]
  rw [chiMK_spaceGrad_one I κ k t x hk hε]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.mul_apply, Fin.sum_univ_two, sigmaMat, h00, h01, h10, h11]
    all_goals ring

theorem FluxMatrix.fluxIntegrand_active_three_matrix {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (k : ℤ) (t : ℝ)
    (hk : k % 4 = 3) (hzk : I.zetaMK m k t ≠ 0) (x : Vec 2) :
    I.fluxIntegrand κ m t x = Matrix.of (fun i j =>
      if i = 0 then
        if j = 0 then κ + I.zetaProd m k t * psi β I.Λ m k x *
          (-spaceGrad (fun y => I.chiMK κ m k t y 0) x 1)
        else -(I.zetaProd m k t * psi β I.Λ m k x)
      else if j = 0 then I.zetaProd m k t * psi β I.Λ m k x +
        -κ * (-spaceGrad (fun y => I.chiMK κ m k t y 0) x 1)
      else κ) := by
  have hodd : Odd k := by
    rcases Int.even_or_odd k with heven | hodd
    · rcases heven with ⟨z, hz⟩
      omega
    · exact hodd
  have hpsi := FluxMatrix.psiM_eq_active_mode I hm k t hodd hzk
  have hchi := FluxMatrix.chiM_eq_active_mode I hm κ k t hodd hzk
  have hε : epsilon β I.Λ m ≠ 0 :=
    ne_of_gt (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le)
  have hg := chiMK_gradMatrix_three_entries I κ k t x hk hε
  rcases hg with ⟨h00, h01, h10, h11⟩
  rw [Ingredients.fluxIntegrand, congrFun hpsi x, hchi]
  rw [chiMK_spaceGrad_three I κ k t x hk hε]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.mul_apply, Fin.sum_univ_two, sigmaMat, h00, h01, h10, h11]

/-- The full spatially averaged flux matrix on an active horizontal mode. -/
theorem flux_active_one {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (κ : ℝ) (k : ℤ) (t : ℝ)
    (hk : k % 4 = 1) (hzk : I.zetaMK m k t ≠ 0) :
    I.flux κ m t = κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 *
        I.zetaProd m k t * I.corrTime κ m k t) • Matrix.single 1 1 1 := by
  let P : Vec 2 → ℝ := fun x => I.zetaProd m k t * psi β I.Λ m k x
  let D : Vec 2 → ℝ := fun x =>
    spaceGrad (fun y => I.chiMK κ m k t y 1) x 0
  have hodd : Odd k := by
    rcases Int.even_or_odd k with heven | hodd
    · rcases heven with ⟨z, hz⟩
      omega
    · exact hodd
  have hpsi := FluxMatrix.psiM_eq_active_mode I hm k t hodd hzk
  have hchi := FluxMatrix.chiM_eq_active_mode I hm κ k t hodd hzk
  have hε : epsilon β I.Λ m ≠ 0 :=
    ne_of_gt (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le)
  have hfluxfun : (fun x => I.fluxIntegrand κ m t x) =
      fun x => Matrix.of (fun i j =>
        if i = 0 then
          if j = 0 then κ else κ * D x - P x
        else if j = 0 then P x else κ + P x * D x) := by
    funext x
    simpa [P, D] using FluxMatrix.fluxIntegrand_active_one_matrix I hm κ k t hk hzk x
  have hPcont : Continuous P := by
    have hformula : psi β I.Λ m k = fun x =>
        a β I.Λ m * epsilon β I.Λ m ^ 2 *
          Real.sin ((2 * Real.pi / epsilon β I.Λ m) * x 0) := by
      funext x
      rw [psi_sineCoordinate]
      simp [hk]
    change Continuous (fun x => I.zetaProd m k t * psi β I.Λ m k x)
    rw [hformula]
    fun_prop
  have hDcont : Continuous D := by
    change Continuous (fun x => spaceGrad (fun y => I.chiMK κ m k t y 1) x 0)
    simp_rw [chiMK_spaceGrad_one I κ k t _ hk hε]
    fun_prop
  have hPavg : spaceAvg P = 0 := by
    calc
      spaceAvg P = I.zetaProd m k t * spaceAvg (psi β I.Λ m k) := by
        dsimp [P]
        exact FluxMatrix.spaceAvg_const_mul _ _
      _ = 0 := by
        rw [spaceAvg_psi_eq_zero I hm k (Or.inl hk)]
        ring
  have hcomp : (fun y : Vec 2 => I.chiMK κ m k t y 1) =
      fun y => I.chiM κ m t y 1 := by
    funext y
    exact congrArg (fun v : Vec 2 => v 1) ((congrFun hchi y).symm)
  have hDfun : D = fun x =>
      spaceGrad (fun y => I.chiM κ m t y 1) x 0 := by
    funext x
    change spaceGrad (fun y => I.chiMK κ m k t y 1) x 0 = _
    rw [hcomp]
  have hDavg : spaceAvg D = 0 := by
    rw [hDfun]
    exact spaceAvg_chiM_component_deriv_eq_zero I hm κ t 1 0
  have hPDavg : spaceAvg (fun x => P x * D x) =
      2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 *
        I.zetaProd m k t * I.corrTime κ m k t := by
    simpa [P, D] using spaceAvg_cross_one I hm κ k t hk hε
  have h01avg : spaceAvg (fun x => κ * D x - P x) = 0 := by
    rw [FluxMatrix.spaceAvg_sub_of_continuous (f := fun x => κ * D x) (g := P)
      (continuous_const.mul hDcont) hPcont,
      FluxMatrix.spaceAvg_const_mul, hDavg, hPavg]
    ring
  have h11avg : spaceAvg (fun x => κ + P x * D x) =
      κ + 2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 *
        I.zetaProd m k t * I.corrTime κ m k t := by
    rw [FluxMatrix.spaceAvg_add_of_continuous (f := fun _ => κ) (g := fun x => P x * D x)
      continuous_const (hPcont.mul hDcont),
      FluxMatrix.spaceAvg_const_eq, hPDavg]
  unfold Ingredients.flux
  change spaceAvgMat (fun x => I.fluxIntegrand κ m t x) = _
  rw [hfluxfun]
  unfold AVenhance.spaceAvgMat
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [Matrix.one_apply, Matrix.single_apply] using FluxMatrix.spaceAvg_const_eq κ
  · simpa [P, D, Matrix.one_apply, Matrix.single_apply] using h01avg
  · simpa [P, D, Matrix.one_apply, Matrix.single_apply] using hPavg
  · simpa [P, D, Matrix.one_apply, Matrix.single_apply] using h11avg

/-- The full spatially averaged flux matrix on an active vertical mode. -/
theorem flux_active_three {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (κ : ℝ) (k : ℤ) (t : ℝ)
    (hk : k % 4 = 3) (hzk : I.zetaMK m k t ≠ 0) :
    I.flux κ m t = κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 *
        I.zetaProd m k t * I.corrTime κ m k t) • Matrix.single 0 0 1 := by
  let P : Vec 2 → ℝ := fun x => I.zetaProd m k t * psi β I.Λ m k x
  let D : Vec 2 → ℝ := fun x =>
    -spaceGrad (fun y => I.chiMK κ m k t y 0) x 1
  have hodd : Odd k := by
    rcases Int.even_or_odd k with heven | hodd
    · rcases heven with ⟨z, hz⟩
      omega
    · exact hodd
  have hpsi := FluxMatrix.psiM_eq_active_mode I hm k t hodd hzk
  have hchi := FluxMatrix.chiM_eq_active_mode I hm κ k t hodd hzk
  have hε : epsilon β I.Λ m ≠ 0 :=
    ne_of_gt (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le)
  have hfluxfun : (fun x => I.fluxIntegrand κ m t x) =
      fun x => Matrix.of (fun i j =>
        if i = 0 then
          if j = 0 then κ + P x * D x else -P x
        else if j = 0 then P x - κ * D x else κ) := by
    funext x
    simpa [P, D] using FluxMatrix.fluxIntegrand_active_three_matrix I hm κ k t hk hzk x
  have hPcont : Continuous P := by
    have hformula : psi β I.Λ m k = fun x =>
        a β I.Λ m * epsilon β I.Λ m ^ 2 *
          Real.sin ((2 * Real.pi / epsilon β I.Λ m) * x 1) := by
      funext x
      rw [psi_sineCoordinate]
      simp [hk]
    change Continuous (fun x => I.zetaProd m k t * psi β I.Λ m k x)
    rw [hformula]
    fun_prop
  have hDcont : Continuous D := by
    change Continuous (fun x => -spaceGrad (fun y => I.chiMK κ m k t y 0) x 1)
    simp_rw [chiMK_spaceGrad_three I κ k t _ hk hε]
    fun_prop
  have hPavg : spaceAvg P = 0 := by
    calc
      spaceAvg P = I.zetaProd m k t * spaceAvg (psi β I.Λ m k) := by
        dsimp [P]
        exact FluxMatrix.spaceAvg_const_mul _ _
      _ = 0 := by
        rw [spaceAvg_psi_eq_zero I hm k (Or.inr hk)]
        ring
  have hcomp : (fun y : Vec 2 => I.chiMK κ m k t y 0) =
      fun y => I.chiM κ m t y 0 := by
    funext y
    exact congrArg (fun v : Vec 2 => v 0) ((congrFun hchi y).symm)
  have hDfun : D = fun x =>
      -spaceGrad (fun y => I.chiM κ m t y 0) x 1 := by
    funext x
    change -spaceGrad (fun y => I.chiMK κ m k t y 0) x 1 = _
    rw [hcomp]
  have hDavg : spaceAvg D = 0 := by
    calc
      spaceAvg D = -spaceAvg (fun x =>
          spaceGrad (fun y => I.chiM κ m t y 0) x 1) := by
        rw [hDfun]
        unfold spaceAvg
        rw [integral_neg]
      _ = 0 := by
        rw [spaceAvg_chiM_component_deriv_eq_zero I hm κ t 0 1]
        ring
  have hPDavg : spaceAvg (fun x => P x * D x) =
      2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 *
        I.zetaProd m k t * I.corrTime κ m k t := by
    simpa [P, D] using spaceAvg_cross_three I hm κ k t hk hε
  have h01avg : spaceAvg (fun x => -P x) = 0 := by
    calc
      spaceAvg (fun x => -P x) = -spaceAvg P := by
        unfold spaceAvg
        rw [integral_neg]
      _ = 0 := by rw [hPavg]; ring
  have h10avg : spaceAvg (fun x => P x - κ * D x) = 0 := by
    rw [FluxMatrix.spaceAvg_sub_of_continuous (f := P) (g := fun x => κ * D x)
      hPcont (continuous_const.mul hDcont), hPavg,
      FluxMatrix.spaceAvg_const_mul, hDavg]
    ring
  have h00avg : spaceAvg (fun x => κ + P x * D x) =
      κ + 2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 *
        I.zetaProd m k t * I.corrTime κ m k t := by
    rw [FluxMatrix.spaceAvg_add_of_continuous (f := fun _ => κ) (g := fun x => P x * D x)
      continuous_const (hPcont.mul hDcont),
      FluxMatrix.spaceAvg_const_eq, hPDavg]
  unfold Ingredients.flux
  change spaceAvgMat (fun x => I.fluxIntegrand κ m t x) = _
  rw [hfluxfun]
  unfold AVenhance.spaceAvgMat
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [Matrix.one_apply, Matrix.single_apply] using h00avg
  · simpa [P, D, Matrix.one_apply, Matrix.single_apply] using h01avg
  · simpa [P, D, Matrix.one_apply, Matrix.single_apply] using h10avg
  · simpa [Matrix.one_apply, Matrix.single_apply] using FluxMatrix.spaceAvg_const_eq κ

theorem FluxMatrix.gradMatrix_entry_continuous {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ t : ℝ) (i j : Fin 2) :
    Continuous (fun x => gradMatrix (I.chiM κ m t) x i j) := by
  change Continuous (fun x => spaceGrad (fun y => I.chiM κ m t y j) x i)
  have hreg := chiM_component_contDiff I hm κ t j
  have hreg1 : ContDiff ℝ 1 (fun y => I.chiM κ m t y j) := hreg.of_le (by simp)
  unfold AVenhance.spaceGrad
  exact (hreg1.continuous_fderiv (by simp)).clm_apply continuous_const

/-- If every odd stream mode is inactive, its spatially averaged flux is just
`κ I`; the remaining corrector-gradient term has zero mean by periodicity. -/
theorem flux_eq_kappa_of_no_odd_active {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (t : ℝ)
    (hzero : ∀ k : ℤ, Odd k → I.zetaMK m k t = 0) :
    I.flux κ m t = κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hpsi : I.psiM m t = fun _ => 0 := by
    funext x
    unfold Ingredients.psiM
    have hterms : (fun k : {k : ℤ // Odd k} =>
        I.zetaProd m k.1 t * psi β I.Λ m k.1 x) = fun _ => 0 := by
      funext k
      simp [Ingredients.zetaProd, hzero k.1 k.2]
    rw [hterms]
    simp
  have hfluxfun : (fun x => I.fluxIntegrand κ m t x) =
      fun x => Matrix.of (fun i j =>
        if i = j then κ + κ * gradMatrix (I.chiM κ m t) x i j
        else κ * gradMatrix (I.chiM κ m t) x i j) := by
    funext x
    rw [Ingredients.fluxIntegrand, congrFun hpsi x]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals
      simp [Matrix.mul_apply, Matrix.one_apply, sigmaMat, gradMatrix]
      all_goals ring
  unfold Ingredients.flux
  change spaceAvgMat (fun x => I.fluxIntegrand κ m t x) = _
  rw [hfluxfun]
  unfold AVenhance.spaceAvgMat
  ext i j
  by_cases hij : i = j
  · subst j
    have hgrad := spaceAvg_chiM_component_deriv_eq_zero I hm κ t i i
    have hgrad' : spaceAvg (fun x => gradMatrix (I.chiM κ m t) x i i) = 0 := by
      simpa [gradMatrix] using hgrad
    have hcont := FluxMatrix.gradMatrix_entry_continuous I hm κ t i i
    simp only [Matrix.of_apply, ↓reduceIte, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
        mul_one]
    rw [FluxMatrix.spaceAvg_add_of_continuous (f := fun _ => κ)
      (g := fun x => κ * gradMatrix (I.chiM κ m t) x i i)
      continuous_const (continuous_const.mul hcont),
      FluxMatrix.spaceAvg_const_eq, FluxMatrix.spaceAvg_const_mul, hgrad']
    ring
  · have hgrad := spaceAvg_chiM_component_deriv_eq_zero I hm κ t j i
    have hgrad' : spaceAvg (fun x => gradMatrix (I.chiM κ m t) x i j) = 0 := by
      simpa [gradMatrix] using hgrad
    simp only [Matrix.of_apply, hij, ↓reduceIte, Matrix.smul_apply, ne_eq, not_false_eq_true,
        Matrix.one_apply_ne,
      smul_eq_mul, mul_zero]
    rw [FluxMatrix.spaceAvg_const_mul, hgrad']
    ring

/-- The complete fixed-time flux has no off-diagonal entries. -/
theorem flux_offdiag_eq_zero {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (κ t : ℝ) {i j : Fin 2} (hij : i ≠ j) :
    I.flux κ m t i j = 0 := by
  classical
  by_cases hex : ∃ k : {k : ℤ // Odd k}, I.zetaMK m k.1 t ≠ 0
  · rcases hex with ⟨⟨k, hodd⟩, hzk⟩
    have hmod : k % 4 = 1 ∨ k % 4 = 3 := by
      rcases hodd with ⟨n, hn⟩
      omega
    rcases hmod with hk | hk
    · rw [flux_active_one I hm κ k t hk hzk]
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · simp
      · simp
      · exact (hij rfl).elim
    · rw [flux_active_three I hm κ k t hk hzk]
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · simp
      · simp
      · exact (hij rfl).elim
  · have hzero : ∀ k : ℤ, Odd k → I.zetaMK m k t = 0 := by
      intro k hk
      by_contra hne
      exact hex ⟨⟨k, hk⟩, hne⟩
    rw [flux_eq_kappa_of_no_odd_active I hm κ t hzero]
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simp
    · simp
    · exact (hij rfl).elim

/-- Every diagonal flux entry is at least the molecular diffusivity `κ`. -/
theorem flux_diag_ge_kappa {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (κ t : ℝ) (i : Fin 2) :
    κ ≤ I.flux κ m t i i := by
  classical
  by_cases hex : ∃ k : {k : ℤ // Odd k}, I.zetaMK m k.1 t ≠ 0
  · rcases hex with ⟨⟨k, hodd⟩, hzk⟩
    have hmod : k % 4 = 1 ∨ k % 4 = 3 := by
      rcases hodd with ⟨n, hn⟩
      omega
    have hz := zetaProd_nonneg I hm k t
    have hc := corrTime_nonneg I hm κ k t
    have hcoeff : 0 ≤ 2 * Real.pi ^ 2 * a β I.Λ m ^ 2 *
        epsilon β I.Λ m ^ 2 * I.zetaProd m k t * I.corrTime κ m k t := by
      positivity
    rcases hmod with hk | hk
    · rw [flux_active_one I hm κ k t hk hzk]
      fin_cases i
      · simp
      · simp only [Fin.isValue, Matrix.smul_single, smul_eq_mul, mul_one, Fin.mk_one,
          Matrix.add_apply,
          Matrix.smul_apply, Matrix.one_apply_eq, Matrix.single_apply_same,
              le_add_iff_nonneg_right, ge_iff_le]
        exact hcoeff
    · rw [flux_active_three I hm κ k t hk hzk]
      fin_cases i
      · simp only [Fin.isValue, Matrix.smul_single, smul_eq_mul, mul_one, Fin.zero_eta,
          Matrix.add_apply,
          Matrix.smul_apply, Matrix.one_apply_eq, Matrix.single_apply_same,
              le_add_iff_nonneg_right, ge_iff_le]
        exact hcoeff
      · simp
  · have hzero : ∀ k : ℤ, Odd k → I.zetaMK m k t = 0 := by
      intro k hk
      by_contra hne
      exact hex ⟨⟨k, hk⟩, hne⟩
    rw [flux_eq_kappa_of_no_odd_active I hm κ t hzero]
    simp

theorem FluxMatrix.activeFluxCoeff_le_amplitude {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (hκ : 0 < κ) (k : ℤ) (t : ℝ) :
    2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 *
        I.zetaProd m k t * I.corrTime κ m k t ≤
      a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / (2 * κ) := by
  have hε : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hρ : 0 < 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 := by positivity
  have hz := zetaProd_mem_Icc I hm k t
  have hc := corrTime_nonneg_le_inv I hm κ hκ k t
  have hzc : I.zetaProd m k t * I.corrTime κ m k t ≤
      (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2)⁻¹ := by
    calc
      I.zetaProd m k t * I.corrTime κ m k t ≤
          1 * I.corrTime κ m k t :=
        mul_le_mul_of_nonneg_right hz.2 hc.1
      _ = I.corrTime κ m k t := one_mul _
      _ ≤ (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2)⁻¹ := hc.2
  calc
    2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 *
        I.zetaProd m k t * I.corrTime κ m k t ≤
      (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2) *
        (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2)⁻¹ := by
      calc
        _ = (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2) *
            (I.zetaProd m k t * I.corrTime κ m k t) := by ring
        _ ≤ (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2) *
            (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left hzc (by positivity)
    _ = a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / (2 * κ) := by
      field_simp [ne_of_gt hε, ne_of_gt hκ, ne_of_gt Real.pi_pos]
      ring

/-- The fixed-time diagonal flux has a uniform upper bound from the memory
relaxation estimate. -/
theorem flux_diag_le_kappa_add_amplitude {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (hκ : 0 < κ) (t : ℝ) (i : Fin 2) :
    I.flux κ m t i i ≤
      κ + a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / (2 * κ) := by
  classical
  by_cases hex : ∃ k : {k : ℤ // Odd k}, I.zetaMK m k.1 t ≠ 0
  · rcases hex with ⟨⟨k, hkodd⟩, hzk⟩
    have hmod : k % 4 = 1 ∨ k % 4 = 3 := by
      rcases hkodd with ⟨n, hn⟩
      omega
    rcases hmod with hk | hk
    · rw [flux_active_one I hm κ k t hk hzk]
      fin_cases i
      · simp only [Fin.isValue, Matrix.smul_single, smul_eq_mul, mul_one, Fin.zero_eta,
          Matrix.add_apply,
          Matrix.smul_apply, Matrix.one_apply_eq, one_ne_zero, and_self, not_false_eq_true,
              Matrix.single_apply_of_ne,
          add_zero, le_add_iff_nonneg_right, ge_iff_le]
        positivity
      · simpa [Matrix.smul_apply, Matrix.one_apply, Matrix.single_apply,
          smul_eq_mul] using
          add_le_add_left (FluxMatrix.activeFluxCoeff_le_amplitude I hm κ hκ k t) κ
    · rw [flux_active_three I hm κ k t hk hzk]
      fin_cases i
      · simpa [Matrix.smul_apply, Matrix.one_apply, Matrix.single_apply,
          smul_eq_mul] using
          add_le_add_left (FluxMatrix.activeFluxCoeff_le_amplitude I hm κ hκ k t) κ
      · simp only [Fin.isValue, Matrix.smul_single, smul_eq_mul, mul_one, Fin.mk_one,
          Matrix.add_apply,
          Matrix.smul_apply, Matrix.one_apply_eq, zero_ne_one, and_self, not_false_eq_true,
              Matrix.single_apply_of_ne,
          add_zero, le_add_iff_nonneg_right, ge_iff_le]
        positivity
  · have hzero : ∀ k : ℤ, Odd k → I.zetaMK m k t = 0 := by
      intro k hk
      by_contra hne
      exact hex ⟨⟨k, hk⟩, hne⟩
    rw [flux_eq_kappa_of_no_odd_active I hm κ t hzero]
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
        le_add_iff_nonneg_right, ge_iff_le]
    positivity

end AVenhance.Infra.Section3
