/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.MovingFluxEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.MovingEnergyReduction

/-! Matrix-valued flux comparison with the mode-reduced moving energy. -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace AVenhance.Infra.Section3

open AVenhance
open Homogenization

/-- The spatially averaged gradient energy of one shear mode. -/
def movingEnergyModeCoefficient {β : ℝ} (I : Ingredients β)
    (κ : ℝ) (m : ℕ) (k : ℤ) (t : ℝ) : ℝ :=
  8 * Real.pi ^ 4 * a β I.Λ m ^ 2 * κ * I.corrTime κ m k t ^ 2

/-- Spatial coordinate selected by the moving-energy shear index. -/
def MovingFluxEnergyComplete.movingEnergyCoordinate (k : ℤ) : Fin 2 :=
  if k % 4 = 1 then 1 else 0

/-- Decide whether a coordinate is the active coordinate of a moving-energy shear mode. -/
def MovingFluxEnergyComplete.movingEnergyCoordinateActive (i : Fin 2) (k : ℤ) : Bool :=
  decide (i = MovingFluxEnergyComplete.movingEnergyCoordinate k)

/-- Cutoff-weighted contribution of an odd shear mode to the moving energy. -/
def MovingFluxEnergyComplete.movingEnergyModeTerm {β : ℝ} (I : Ingredients β)
    (κ : ℝ) (m : ℕ) (t : ℝ) (k : {k : ℤ // Odd k}) : ℝ :=
  I.xiMK m k.1 t ^ 2 * movingEnergyModeCoefficient I κ m k.1 t

/-- Entrywise spatial average of one mode's gradient Gram matrix. -/
def movingEnergyGramMean {β : ℝ} (I : Ingredients β)
    (κ : ℝ) (m : ℕ) (k : ℤ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => spaceAvg (fun x : Vec 2 =>
    (Matrix.transpose (gradMatrix (I.chiMK κ m k t) x) *
      gradMatrix (I.chiMK κ m k t) x) i j)

theorem MovingFluxEnergyComplete.movingEnergyGram_horizontal {β : ℝ} (I : Ingredients β)
    {m : ℕ} (κ : ℝ) (k : ℤ) (t : ℝ) (hk : k % 4 = 1)
    (x : Vec 2) :
    Matrix.transpose (gradMatrix (I.chiMK κ m k t) x) *
      gradMatrix (I.chiMK κ m k t) x =
        (spaceGrad (fun y => I.chiMK κ m k t y 1) x 0 ^ 2) •
          Matrix.single 1 1 1 := by
  have hε := ne_of_gt (Infra.Cutoff.epsilon_pos
    (m := m) I.one_lt_beta I.beta_lt I.two_pow_seven_le)
  obtain ⟨h00, h01, h10, h11⟩ :=
    chiMK_gradMatrix_one_entries (m := m) I κ k t x hk hε
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.single,
      h00, h10]
  · simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.single,
      h00, h01, h10, h11]
  · simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.single,
      h00, h01, h10, h11]
  · simp only [Fin.mk_one, Fin.isValue, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_two, h01, h11,
      mul_zero, add_zero, Matrix.single, Matrix.smul_apply, Matrix.of_apply, and_self, ↓reduceIte,
          smul_eq_mul, mul_one]
    have hgrad : spaceGrad (fun y => I.chiMK κ m k t y 1) x 0 =
        4 * Real.pi ^ 2 * a β I.Λ m * I.corrTime κ m k t *
          Real.sin (2 * Real.pi * x 0 / epsilon β I.Λ m) := by
      simpa [gradMatrix] using h01
    rw [hgrad]
    ring

theorem MovingFluxEnergyComplete.movingEnergyGram_vertical {β : ℝ} (I : Ingredients β)
    {m : ℕ} (κ : ℝ) (k : ℤ) (t : ℝ) (hk : k % 4 = 3)
    (x : Vec 2) :
    Matrix.transpose (gradMatrix (I.chiMK κ m k t) x) *
      gradMatrix (I.chiMK κ m k t) x =
        (spaceGrad (fun y => I.chiMK κ m k t y 0) x 1 ^ 2) •
          Matrix.single 0 0 1 := by
  have hε := ne_of_gt (Infra.Cutoff.epsilon_pos
    (m := m) I.one_lt_beta I.beta_lt I.two_pow_seven_le)
  obtain ⟨h00, h01, h10, h11⟩ :=
    chiMK_gradMatrix_three_entries (m := m) I κ k t x hk hε
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_two, h00,
      mul_zero, h10, neg_mul, mul_neg, neg_neg, zero_add, Matrix.single, Matrix.smul_apply,
          Matrix.of_apply, and_self,
      ↓reduceIte, smul_eq_mul, mul_one]
    have hgrad : spaceGrad (fun y => I.chiMK κ m k t y 0) x 1 =
        -(4 * Real.pi ^ 2 * a β I.Λ m * I.corrTime κ m k t) *
          Real.sin (2 * Real.pi * x 1 / epsilon β I.Λ m) := by
      simpa [gradMatrix] using h10
    rw [hgrad]
    ring
  · simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.single,
      h01, h11]
  · simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.single,
      h01, h11]
  · simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.single,
      h01, h11]

/-- The horizontal shear contributes only its active diagonal energy entry. -/
theorem movingEnergyGramMean_horizontal {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (k : ℤ) (t : ℝ)
    (hk : k % 4 = 1) :
    movingEnergyGramMean I κ m k t =
      (8 * Real.pi ^ 4 * a β I.Λ m ^ 2 * I.corrTime κ m k t ^ 2) •
        Matrix.single 1 1 1 := by
  ext i j
  have hfun : (fun x : Vec 2 =>
      (Matrix.transpose (gradMatrix (I.chiMK κ m k t) x) *
        gradMatrix (I.chiMK κ m k t) x) i j) =
      fun x => (spaceGrad (fun y => I.chiMK κ m k t y 1) x 0 ^ 2) *
        Matrix.single 1 1 1 i j := by
    funext x
    rw [MovingFluxEnergyComplete.movingEnergyGram_horizontal I κ k t hk x]
    simp
  rw [show (movingEnergyGramMean I κ m k t) i j =
      spaceAvg (fun x =>
        (Matrix.transpose (gradMatrix (I.chiMK κ m k t) x) *
          gradMatrix (I.chiMK κ m k t) x) i j) by rfl]
  rw [hfun]
  fin_cases i <;> fin_cases j
  · simp [Matrix.single, spaceAvg]
  · simp [Matrix.single, spaceAvg]
  · simp [Matrix.single, spaceAvg]
  · simpa [Matrix.single] using spaceAvg_chiMK_gradient_sq_one I hm κ k t hk

/-- The vertical shear contributes only its active diagonal energy entry. -/
theorem movingEnergyGramMean_vertical {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (k : ℤ) (t : ℝ)
    (hk : k % 4 = 3) :
    movingEnergyGramMean I κ m k t =
      (8 * Real.pi ^ 4 * a β I.Λ m ^ 2 * I.corrTime κ m k t ^ 2) •
        Matrix.single 0 0 1 := by
  ext i j
  have hfun : (fun x : Vec 2 =>
      (Matrix.transpose (gradMatrix (I.chiMK κ m k t) x) *
        gradMatrix (I.chiMK κ m k t) x) i j) =
      fun x => (spaceGrad (fun y => I.chiMK κ m k t y 0) x 1 ^ 2) *
        Matrix.single 0 0 1 i j := by
    funext x
    rw [MovingFluxEnergyComplete.movingEnergyGram_vertical I κ k t hk x]
    simp
  rw [show (movingEnergyGramMean I κ m k t) i j =
      spaceAvg (fun x =>
        (Matrix.transpose (gradMatrix (I.chiMK κ m k t) x) *
          gradMatrix (I.chiMK κ m k t) x) i j) by rfl]
  rw [hfun]
  fin_cases i <;> fin_cases j
  · simpa [Matrix.single] using spaceAvg_chiMK_gradient_sq_three I hm κ k t hk
  · simp [Matrix.single, spaceAvg]
  · simp [Matrix.single, spaceAvg]
  · simp [Matrix.single, spaceAvg]

/-- The mode-reduced spatial energy correction in coordinate `i`. -/
def movingCutoffEnergyCorrectionEntry {β : ℝ} (I : Ingredients β)
    (κ : ℝ) (m : ℕ) (t : ℝ) (i : Fin 2) : ℝ :=
  ∑' k : {k : ℤ // Odd k},
    if MovingFluxEnergyComplete.movingEnergyCoordinateActive i k.1 then
      MovingFluxEnergyComplete.movingEnergyModeTerm I κ m t k else 0

/-- The diagonal energy correction is exactly the sum of the spatially
averaged single-mode gradient Gram entries. This identifies the diagonal
energy matrix used in the flux estimate with the source's `E_m` formula after
the finite-support double-sum reduction. -/
theorem movingCutoffEnergyCorrectionEntry_eq_spatial_mode_sum {β : ℝ}
    (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (t : ℝ)
    (i : Fin 2) :
    movingCutoffEnergyCorrectionEntry I κ m t i =
      ∑' k : {k : ℤ // Odd k},
        (I.xiMK m k.1 t ^ 2 * κ) *
          movingEnergyGramMean I κ m k.1 t i i := by
  unfold movingCutoffEnergyCorrectionEntry
  apply tsum_congr
  intro k
  have hmod : k.1 % 4 = 1 ∨ k.1 % 4 = 3 := by
    rcases k.2 with ⟨z, hz⟩
    omega
  rcases hmod with h1 | h3
  · rw [movingEnergyGramMean_horizontal I hm κ k.1 t h1]
    fin_cases i <;>
      simp [MovingFluxEnergyComplete.movingEnergyCoordinateActive,
          MovingFluxEnergyComplete.movingEnergyCoordinate,
        MovingFluxEnergyComplete.movingEnergyModeTerm, movingEnergyModeCoefficient, Matrix.single,
        Matrix.smul_apply, h1]
    all_goals ring
  · rw [movingEnergyGramMean_vertical I hm κ k.1 t h3]
    fin_cases i <;>
      simp [MovingFluxEnergyComplete.movingEnergyCoordinateActive,
          MovingFluxEnergyComplete.movingEnergyCoordinate,
        MovingFluxEnergyComplete.movingEnergyModeTerm, movingEnergyModeCoefficient, Matrix.single,
        Matrix.smul_apply, h3]
    all_goals ring

/-- The moving energy after the double-sum orthogonality reduction. Its
molecular part is `κ I`; its modewise correction is diagonal. -/
def movingCutoffEnergyMatrix {β : ℝ} (I : Ingredients β)
    (κ : ℝ) (m : ℕ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
    Matrix.diagonal (movingCutoffEnergyCorrectionEntry I κ m t)

/-- Matrix form of the diagonal source energy after the double-sum reduction:
each diagonal correction is the sum of the spatial averages of the mode Gram
entries, and the molecular baseline is `κ I`. -/
theorem movingCutoffEnergyMatrix_eq_spatial_mode_sum {β : ℝ}
    (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (t : ℝ) :
    movingCutoffEnergyMatrix I κ m t =
      κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        Matrix.diagonal (fun i =>
          ∑' k : {k : ℤ // Odd k},
            (I.xiMK m k.1 t ^ 2 * κ) *
              movingEnergyGramMean I κ m k.1 t i i) := by
  rw [movingCutoffEnergyMatrix]
  congr 1
  ext i j
  simp only [Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j
    simpa using movingCutoffEnergyCorrectionEntry_eq_spatial_mode_sum I hm κ t i
  · simp [hij]

/-- Finite-support version of the source energy after the overlap reduction.
The diagonal terms are the spatial means of the single-mode Gram matrices. -/
def movingEnergyReducedSourceMatrix {β : ℝ} (I : Ingredients β)
    (κ : ℝ) (m : ℕ) (t : ℝ) (S : Finset {k : ℤ // Odd k}) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
    Matrix.diagonal (fun i =>
      ∑ k ∈ S, (I.xiMK m k.1 t ^ 2 * κ) *
        movingEnergyGramMean I κ m k.1 t i i)

/-- For the actual finite cutoff support, the source's spatially averaged
diagonal energy formula agrees with the mode-trace matrix used in the flux
estimate. Together with `movingEnergy_double_sum_reduces`, this closes the
finite `E_m` double-sum reduction. -/
theorem movingCutoffEnergyMatrix_eq_source_reduced {β : ℝ}
    (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (t : ℝ) :
    let S := (xiMK_odd_support_finite I hm t).toFinset
    movingCutoffEnergyMatrix I κ m t =
      movingEnergyReducedSourceMatrix I κ m t S := by
  let S := (xiMK_odd_support_finite I hm t).toFinset
  have hzero (k : {k : ℤ // Odd k}) (hk : k ∉ S) :
      I.xiMK m k.1 t = 0 := by
    by_contra hne
    apply hk
    simpa [S] using hne
  have hsum (i : Fin 2) :
      (∑' k : {k : ℤ // Odd k},
        (I.xiMK m k.1 t ^ 2 * κ) *
          movingEnergyGramMean I κ m k.1 t i i) =
        ∑ k ∈ S, (I.xiMK m k.1 t ^ 2 * κ) *
          movingEnergyGramMean I κ m k.1 t i i := by
    apply tsum_eq_sum (L := SummationFilter.unconditional
      {k : ℤ // Odd k}) (s := S)
    intro k hk
    simp [hzero k hk]
  rw [movingCutoffEnergyMatrix_eq_spatial_mode_sum I hm κ t]
  change κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      Matrix.diagonal (fun i =>
        ∑' k : {k : ℤ // Odd k},
          (I.xiMK m k.1 t ^ 2 * κ) *
            movingEnergyGramMean I κ m k.1 t i i) =
    κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      Matrix.diagonal (fun i =>
        ∑ k ∈ S, (I.xiMK m k.1 t ^ 2 * κ) *
          movingEnergyGramMean I κ m k.1 t i i)
  congr 1
  ext i j
  simp only [Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j
    simpa using hsum i
  · simp [hij]

theorem MovingFluxEnergyComplete.movingEnergyModeTerm_summable {β : ℝ}
    (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m)
    (κ : ℝ) (t : ℝ) :
    Summable (MovingFluxEnergyComplete.movingEnergyModeTerm I κ m t) := by
  apply summable_of_hasFiniteSupport
  apply (xiMK_odd_support_finite I hm t).subset
  intro k hk
  by_contra hξ
  have hξ0 : I.xiMK m k.1 t = 0 := not_ne_iff.mp hξ
  simp [MovingFluxEnergyComplete.movingEnergyModeTerm, hξ0] at hk

theorem MovingFluxEnergyComplete.movingEnergyCorrectionEntry_summable {β : ℝ}
    (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m)
    (κ : ℝ) (t : ℝ) (i : Fin 2) :
    Summable (fun k : {k : ℤ // Odd k} =>
      if MovingFluxEnergyComplete.movingEnergyCoordinateActive i k.1 then
        MovingFluxEnergyComplete.movingEnergyModeTerm I κ m t k else 0) := by
  apply summable_of_hasFiniteSupport
  apply (xiMK_odd_support_finite I hm t).subset
  intro k hk
  by_contra hξ
  have hξ0 : I.xiMK m k.1 t = 0 := not_ne_iff.mp hξ
  simp [MovingFluxEnergyComplete.movingEnergyModeTerm, hξ0] at hk

theorem MovingFluxEnergyComplete.movingCutoffEnergyTrace_eq_tsum_modeTerm {β : ℝ}
    (I : Ingredients β) {m : ℕ} (_hm : 1 ≤ m)
    (κ : ℝ) (t : ℝ) :
    movingCutoffEnergyTrace I κ m t =
      ∑' k : {k : ℤ // Odd k}, MovingFluxEnergyComplete.movingEnergyModeTerm I κ m t k := by
  unfold movingCutoffEnergyTrace movingCutoffMemoryEnergy
    MovingFluxEnergyComplete.movingEnergyModeTerm movingEnergyModeCoefficient
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  ring

theorem MovingFluxEnergyComplete.movingEnergyModeTerm_nonneg {β : ℝ}
    (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m)
    (κ : ℝ) (hκ : 0 < κ) (t : ℝ)
    (k : {k : ℤ // Odd k}) :
    0 ≤ MovingFluxEnergyComplete.movingEnergyModeTerm I κ m t k := by
  have hξ := xiMK_mem_Icc I hm k.1 t
  have hξsq : 0 ≤ I.xiMK m k.1 t ^ 2 := sq_nonneg _
  unfold MovingFluxEnergyComplete.movingEnergyModeTerm movingEnergyModeCoefficient
  positivity

/-- Each coordinate correction is nonnegative and bounded by the full trace. -/
theorem movingCutoffEnergyCorrectionEntry_bounds {β : ℝ}
    (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m)
    (κ : ℝ) (hκ : 0 < κ) (t : ℝ) (i : Fin 2) :
    0 ≤ movingCutoffEnergyCorrectionEntry I κ m t i ∧
      movingCutoffEnergyCorrectionEntry I κ m t i ≤
        movingCutoffEnergyTrace I κ m t := by
  have hmode := MovingFluxEnergyComplete.movingEnergyModeTerm_summable I hm κ t
  have hentry := MovingFluxEnergyComplete.movingEnergyCorrectionEntry_summable I hm κ t i
  have hpoint (k : {k : ℤ // Odd k}) :
      0 ≤ (if MovingFluxEnergyComplete.movingEnergyCoordinateActive i k.1 then
          MovingFluxEnergyComplete.movingEnergyModeTerm I κ m t k else 0) ∧
        (if MovingFluxEnergyComplete.movingEnergyCoordinateActive i k.1 then
          MovingFluxEnergyComplete.movingEnergyModeTerm I κ m t k else 0) ≤
            MovingFluxEnergyComplete.movingEnergyModeTerm I κ m t k := by
    cases MovingFluxEnergyComplete.movingEnergyCoordinateActive i k.1 <;>
      simp [MovingFluxEnergyComplete.movingEnergyModeTerm_nonneg I hm κ hκ t k]
  have hzeroSummable : Summable
      (fun _ : {k : ℤ // Odd k} => (0 : ℝ)) := by
    exact summable_zero
  have hnonneg := Summable.tsum_le_tsum (fun k => (hpoint k).1)
    hzeroSummable hentry
  have hsum := Summable.tsum_le_tsum (fun k => (hpoint k).2)
    hentry hmode
  constructor
  · simpa [movingCutoffEnergyCorrectionEntry] using hnonneg
  · calc
      movingCutoffEnergyCorrectionEntry I κ m t i ≤
          ∑' k : {k : ℤ // Odd k}, MovingFluxEnergyComplete.movingEnergyModeTerm I κ m t k := by
        simpa [movingCutoffEnergyCorrectionEntry] using hsum
      _ = movingCutoffEnergyTrace I κ m t :=
        (MovingFluxEnergyComplete.movingCutoffEnergyTrace_eq_tsum_modeTerm I hm κ t).symm

theorem MovingFluxEnergyComplete.movingCutoffEnergyCorrectionEntry_active {β : ℝ}
    (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m) (κ : ℝ)
    (k : ℤ) (hk : k % 4 = 1 ∨ k % 4 = 3) (t : ℝ)
    (hzk : I.zetaMK m k t ≠ 0) :
    ∀ i : Fin 2,
      movingCutoffEnergyCorrectionEntry I κ m t i =
        if MovingFluxEnergyComplete.movingEnergyCoordinateActive i k then
          movingCutoffEnergyTrace I κ m t else 0 := by
  have hodd : Odd k := by
    rcases hk with h1 | h3
    · rcases Int.even_or_odd k with he | ho
      · rcases he with ⟨z, hz⟩
        omega
      · exact ho
    · rcases Int.even_or_odd k with he | ho
      · rcases he with ⟨z, hz⟩
        omega
      · exact ho
  have hxi := xiMK_eq_one_of_zetaMK_ne_zero I hm k t hzk
  have htrace := movingCutoffEnergyTrace_eq_active_mode I hm κ k hodd t hzk
  intro i
  unfold movingCutoffEnergyCorrectionEntry
  let ksub : {k : ℤ // Odd k} := ⟨k, hodd⟩
  have htail (l : {l : ℤ // Odd l}) (hne : l ≠ ksub) :
      (if MovingFluxEnergyComplete.movingEnergyCoordinateActive i l.1 then
        MovingFluxEnergyComplete.movingEnergyModeTerm I κ m t l else 0) = 0 := by
    have hkl : l.1 ≠ k := by
      intro heq
      apply hne
      exact Subtype.ext heq
    have hzero := xiMK_eq_zero_of_zetaMK_ne_zero_of_odd_ne
      I hm hodd l.2 hkl t hzk
    simp [MovingFluxEnergyComplete.movingEnergyCoordinateActive,
        MovingFluxEnergyComplete.movingEnergyCoordinate,
      MovingFluxEnergyComplete.movingEnergyModeTerm, hzero]
  rw [tsum_eq_single ksub htail]
  rcases hk with h1 | h3
  · fin_cases i <;>
      simp [ksub, MovingFluxEnergyComplete.movingEnergyCoordinateActive,
          MovingFluxEnergyComplete.movingEnergyCoordinate, h1, hxi,
        MovingFluxEnergyComplete.movingEnergyModeTerm, movingEnergyModeCoefficient, htrace]
  · fin_cases i <;>
      simp [ksub, MovingFluxEnergyComplete.movingEnergyCoordinateActive,
          MovingFluxEnergyComplete.movingEnergyCoordinate, h3, hxi,
        MovingFluxEnergyComplete.movingEnergyModeTerm, movingEnergyModeCoefficient, htrace]

theorem MovingFluxEnergyComplete.movingCutoffEnergyMatrix_active {β : ℝ}
    (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m) (κ : ℝ)
    (k : ℤ) (hk : k % 4 = 1 ∨ k % 4 = 3) (t : ℝ)
    (hzk : I.zetaMK m k t ≠ 0) :
    movingCutoffEnergyMatrix I κ m t =
      κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        movingCutoffEnergyTrace I κ m t •
          (if k % 4 = 1 then Matrix.single 1 1 1
            else Matrix.single 0 0 1) := by
  have hentry := MovingFluxEnergyComplete.movingCutoffEnergyCorrectionEntry_active I hm κ k hk t hzk
  rcases hk with h1 | h3
  · have hzero := hentry 0
    have hone := hentry 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [movingCutoffEnergyMatrix, Matrix.single, Matrix.smul_apply,
        MovingFluxEnergyComplete.movingEnergyCoordinateActive,
            MovingFluxEnergyComplete.movingEnergyCoordinate, h1, hzero, hone]
  · have hzero := hentry 0
    have hone := hentry 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [movingCutoffEnergyMatrix, Matrix.single, Matrix.smul_apply,
        MovingFluxEnergyComplete.movingEnergyCoordinateActive,
            MovingFluxEnergyComplete.movingEnergyCoordinate, h3, hzero, hone]

theorem MovingFluxEnergyComplete.movingFluxEnergy_active_matrix_error {β C₀ : ℝ}
    (I : Ingredients β) (hCz : I.Czeta ≤ C₀) (hCh : I.Chat ≤ C₀)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (hκ : 0 < κ) (k : ℤ) (t : ℝ)
    (hk : k % 4 = 1 ∨ k % 4 = 3) (hzk : I.zetaMK m k t ≠ 0) :
    ∀ i j, |(I.flux κ m t - movingCutoffEnergyMatrix I κ m t) i j| ≤
      (((C₀ + C₀) / (4 * Real.pi ^ 2)) * (1 / 2) +
        C₀ ^ 2 / (16 * Real.pi ^ 4)) *
        (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
          (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) := by
  let S := a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ
  let qv := epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)
  let cActive := (C₀ + C₀) / (4 * Real.pi ^ 2) * (1 / 2)
  let cTail := C₀ ^ 2 / (16 * Real.pi ^ 4)
  have hC₀ : 0 ≤ C₀ := by linarith [I.one_le_Czeta, hCz]
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hτ : 0 < tau β I.Λ m := I.tau_pos' m
  have hqv : 0 ≤ qv := by
    dsimp [qv]
    exact div_nonneg (sq_nonneg _) (mul_nonneg hκ.le hτ.le)
  have hca : 0 ≤ cActive := by
    dsimp [cActive]
    exact mul_nonneg (div_nonneg (add_nonneg hC₀ hC₀) (by positivity))
      (by norm_num)
  have hct : 0 ≤ cTail := by
    dsimp [cTail]
    exact div_nonneg (sq_nonneg C₀) (by positivity)
  have htailTerm : 0 ≤ cTail * S * qv := by positivity
  have hD : 0 ≤ (cActive + cTail) * S * qv := by positivity
  have hcombine : cActive * S * qv ≤ (cActive + cTail) * S * qv := by
    calc
      cActive * S * qv ≤ cActive * S * qv + cTail * S * qv :=
        le_add_of_nonneg_right htailTerm
      _ = (cActive + cTail) * S * qv := by ring
  rcases hk with h1 | h3
  · have hflux := flux_active_one I hm κ k t h1 hzk
    have henergy := MovingFluxEnergyComplete.movingCutoffEnergyMatrix_active I hm κ k (Or.inl h1)
        t hzk
    have herr := movingFluxEnergy_active_entry_error I hCz hCh hm κ hκ k t
      (Or.inl h1) hzk
    have hactive : |I.flux κ m t 1 1 - κ - movingCutoffEnergyTrace I κ m t| ≤
        cActive * S * qv := by
      have hcalc :
          ((C₀ + C₀) / (4 * Real.pi ^ 2)) *
            (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / (2 * κ)) * qv =
          cActive * S * qv := by dsimp [cActive, S]; ring
      rw [hcalc] at herr
      simpa [h1, qv] using herr
    have hmain : |(2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 *
        I.zetaProd m k t * I.corrTime κ m k t) - movingCutoffEnergyTrace I κ m t| ≤
        cActive * S * qv := by
      simpa [hflux, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
        Matrix.single, h1] using hactive
    intro i j
    rw [hflux, henergy]
    fin_cases i <;> fin_cases j
    · simp [Matrix.single, Matrix.smul_apply, Matrix.sub_apply, h1]
      simpa [cActive, cTail, S, qv, mul_assoc] using hD
    · simp [Matrix.single, Matrix.smul_apply, Matrix.sub_apply, h1]
      simpa [cActive, cTail, S, qv, mul_assoc] using hD
    · simp [Matrix.single, Matrix.smul_apply, Matrix.sub_apply, h1]
      simpa [cActive, cTail, S, qv, mul_assoc] using hD
    · simpa [cActive, cTail, S, qv, mul_assoc, h1, Matrix.single,
        Matrix.smul_apply, Matrix.sub_apply] using hmain.trans hcombine
  · have hflux := flux_active_three I hm κ k t h3 hzk
    have henergy := MovingFluxEnergyComplete.movingCutoffEnergyMatrix_active I hm κ k (Or.inr h3)
        t hzk
    have herr := movingFluxEnergy_active_entry_error I hCz hCh hm κ hκ k t
      (Or.inr h3) hzk
    have hactive : |I.flux κ m t 0 0 - κ - movingCutoffEnergyTrace I κ m t| ≤
        cActive * S * qv := by
      have hcalc :
          ((C₀ + C₀) / (4 * Real.pi ^ 2)) *
            (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / (2 * κ)) * qv =
          cActive * S * qv := by dsimp [cActive, S]; ring
      rw [hcalc] at herr
      simpa [h3, qv] using herr
    have hmain : |(2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 *
        I.zetaProd m k t * I.corrTime κ m k t) - movingCutoffEnergyTrace I κ m t| ≤
        cActive * S * qv := by
      simpa [hflux, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
        Matrix.single, h3] using hactive
    intro i j
    rw [hflux, henergy]
    fin_cases i <;> fin_cases j
    · simpa [cActive, cTail, S, qv, mul_assoc, h3, Matrix.single,
        Matrix.smul_apply, Matrix.sub_apply] using hmain.trans hcombine
    · simp [Matrix.single, Matrix.smul_apply, Matrix.sub_apply, h3]
      simpa [cActive, cTail, S, qv, mul_assoc] using hD
    · simp [Matrix.single, Matrix.smul_apply, Matrix.sub_apply, h3]
      simpa [cActive, cTail, S, qv, mul_assoc] using hD
    · simp [Matrix.single, Matrix.smul_apply, Matrix.sub_apply, h3]
      simpa [cActive, cTail, S, qv, mul_assoc] using hD

/-- The full matrix flux-energy estimate, with the cutoff dependence reduced
to `C₀` and under the source's small-ratio condition. -/
theorem movingFluxEnergy_matrix_error {β C₀ : ℝ}
    (I : Ingredients β) (hCz : I.Czeta ≤ C₀) (hCh : I.Chat ≤ C₀)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (hκ : 0 < κ) (t : ℝ)
    (hcondition : epsilon β I.Λ m ^ 2 ≤ κ * tau β I.Λ m / 2) :
    ∀ i j, |(I.flux κ m t - movingCutoffEnergyMatrix I κ m t) i j| ≤
      (((C₀ + C₀) / (4 * Real.pi ^ 2)) * (1 / 2) +
        C₀ ^ 2 / (16 * Real.pi ^ 4)) *
        (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
          (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) := by
  classical
  by_cases hex : ∃ k : {k : ℤ // Odd k}, I.zetaMK m k.1 t ≠ 0
  · rcases hex with ⟨⟨k, hkodd⟩, hzk⟩
    have hmod : k % 4 = 1 ∨ k % 4 = 3 := by
      rcases hkodd with ⟨z, hz⟩
      omega
    exact MovingFluxEnergyComplete.movingFluxEnergy_active_matrix_error I hCz hCh hm κ hκ k t hmod
        hzk
  · have hzero : ∀ k : ℤ, Odd k → I.zetaMK m k t = 0 := by
      intro k hk
      by_contra hne
      exact hex ⟨⟨k, hk⟩, hne⟩
    have hforce : ∀ k : {k : ℤ // Odd k}, I.zetaProd m k.1 t = 0 := by
      intro k
      simp [Ingredients.zetaProd, hzero k.1 k.2]
    have htail := movingCutoffEnergyTrace_tail_bound_uniform I hCz hCh
      hm κ hκ t hforce hcondition
    have hflux := flux_eq_kappa_of_no_odd_active I hm κ t hzero
    have hCz0 : 0 ≤ C₀ := by linarith [I.one_le_Czeta, hCz]
    let S := a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ
    let qv := epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)
    let cActive := (C₀ + C₀) / (4 * Real.pi ^ 2) * (1 / 2)
    let cTail := C₀ ^ 2 / (16 * Real.pi ^ 4)
    have hτ : 0 < tau β I.Λ m := I.tau_pos' m
    have hscale : 0 ≤ S * qv := by
      apply mul_nonneg
      · dsimp [S]
        positivity
      · dsimp [qv]
        exact div_nonneg (sq_nonneg _) (mul_nonneg hκ.le hτ.le)
    have hca : 0 ≤ cActive := by
      dsimp [cActive]
      exact mul_nonneg (div_nonneg (add_nonneg hCz0 hCz0) (by positivity))
        (by norm_num)
    have hct : 0 ≤ cTail := by
      dsimp [cTail]
      exact div_nonneg (sq_nonneg C₀) (by positivity)
    have hD : 0 ≤ (cActive + cTail) * S * qv := by
      calc
        0 ≤ (cActive + cTail) * (S * qv) :=
          mul_nonneg (add_nonneg hca hct) hscale
        _ = (cActive + cTail) * S * qv := by ring
    have htracebound : movingCutoffEnergyTrace I κ m t ≤
        (cActive + cTail) * S * qv := by
      calc
        _ ≤ cTail * S * qv := by simpa [cTail, S, qv, mul_assoc] using htail
        _ ≤ (cActive + cTail) * S * qv := by
          calc
            cTail * S * qv = cTail * (S * qv) := by ring
            _ ≤ (cActive + cTail) * (S * qv) :=
              mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hca) hscale
            _ = (cActive + cTail) * S * qv := by ring
    have hfluxEq : I.flux κ m t = κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) := hflux
    rw [hfluxEq]
    intro i j
    rw [movingCutoffEnergyMatrix]
    have hentry := movingCutoffEnergyCorrectionEntry_bounds I hm κ hκ t i
    by_cases hij : i = j
    · subst j
      simp [Matrix.sub_apply, Matrix.smul_apply]
      have hentryLe := hentry.2.trans htracebound
      simpa [abs_of_nonneg hentry.1, cActive, cTail, S, qv, mul_assoc] using hentryLe
    · simp [Matrix.sub_apply, Matrix.smul_apply, hij]
      simpa [cActive, cTail, S, qv, mul_assoc] using hD

end AVenhance.Infra.Section3

end
