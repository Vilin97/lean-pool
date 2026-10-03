/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.BreakUp
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.FlowDiffeo
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.LFluxToEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.FluxTimeRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.SpaceAverages
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.CorrectorGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.HMinusOneErgodicCore

/-! # `e.bracket.FF` and `e.ergodic.break.up.second`

Source: `enhance.tex` 8396–8510.  The space average of `FᵗF` equals the reduced energy
`E_m(t)`: the linear terms `⟨∇Χ_{m,k} ∘ X⁻¹⟩` vanish (mean-zero sines), the quadratic terms are
`⟨(∇Χ)ᵗ∇Χ ∘ X⁻¹⟩ = ⟨(∇Χ)ᵗ∇Χ⟩` by measure preservation of the inverse flow, and this is the
diagonal matrix `movingEnergyGramMean`.  Then `l.flux.to.energy` bounds `κ_m⟨FᵗF⟩ - J_m`. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization

namespace AVenhance.Infra.Section5.LeftToShow

open AVenhance AVenhance.Infra.Section3

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-! ## The explicit corrector gradient entries -/

/-- Every entry of `∇Χ_{m,k}` is a constant multiple of a single-coordinate sine (the constant
is `0` for even `k`, where `Χ_{m,k} = 0`). -/
theorem gradMatrix_chiMK_entry_form (m : ℕ) (κ : ℝ) (k : ℤ) (t : ℝ) (i j : Fin 2) :
    ∃ (c : ℝ) (r : Fin 2), ∀ y : Vec 2, gradMatrix (I.chiMK κ m k t) y i j =
      c * Real.sin (2 * Real.pi * y r / epsilon β I.Λ m) := by
  have hε := epsilon_ne_zero I m
  have hk4 : k % 4 = 1 ∨ k % 4 = 3 ∨ (k % 4 ≠ 1 ∧ k % 4 ≠ 3) := by omega
  have hentry : ∀ y : Vec 2, gradMatrix (I.chiMK κ m k t) y i j =
      spaceGrad (fun z => I.chiMK κ m k t z j) y i := fun y => by simp [gradMatrix]
  have hzero : ∀ c : Fin 2, (∀ z : Vec 2, I.chiMK κ m k t z c = 0) → ∀ y : Vec 2,
      spaceGrad (fun z => I.chiMK κ m k t z c) y i = 0 := by
    intro c h y
    have : (fun z : Vec 2 => I.chiMK κ m k t z c) = fun _ => 0 := funext h
    rw [this]
    simp [spaceGrad]
  obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  · rcases hk4 with h1 | h3 | ⟨h1, h3⟩
    · refine ⟨0, 0, fun y => ?_⟩
      rw [hentry, hzero 0 (fun z => by simp [Ingredients.chiMK, uShear, h1])]
      simp
    · by_cases hi : i = 1
      · refine ⟨-(4 * Real.pi ^ 2 * a β I.Λ m * I.corrTime κ m k t), 1, fun y => ?_⟩
        rw [hentry, chiMK_spaceGrad_three_all I κ k t y i h3 hε]
        simp [hi]
      · refine ⟨0, 0, fun y => ?_⟩
        rw [hentry, chiMK_spaceGrad_three_all I κ k t y i h3 hε]
        simp [hi]
    · refine ⟨0, 0, fun y => ?_⟩
      rw [hentry, hzero 0 (fun z => by simp [Ingredients.chiMK, uShear, h1, h3])]
      simp
  · rcases hk4 with h1 | h3 | ⟨h1, h3⟩
    · by_cases hi : i = 0
      · refine ⟨4 * Real.pi ^ 2 * a β I.Λ m * I.corrTime κ m k t, 0, fun y => ?_⟩
        rw [hentry, chiMK_spaceGrad_one_all I κ k t y i h1 hε]
        simp [hi]
      · refine ⟨0, 0, fun y => ?_⟩
        rw [hentry, chiMK_spaceGrad_one_all I κ k t y i h1 hε]
        simp [hi]
    · refine ⟨0, 0, fun y => ?_⟩
      rw [hentry, hzero 1 (fun z => by simp [Ingredients.chiMK, uShear, h3])]
      simp
    · refine ⟨0, 0, fun y => ?_⟩
      rw [hentry, hzero 1 (fun z => by simp [Ingredients.chiMK, uShear, h1, h3])]
      simp

/-- `∇Χ_{m,k}` is `ℤ²`-periodic. -/
theorem gradMatrix_chiMK_periodic {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (k : ℤ) (t : ℝ) :
    Infra.Ergodic.IsZPeriodic (fun y : Vec 2 => gradMatrix (I.chiMK κ m k t) y) := by
  intro y n
  funext i j
  obtain ⟨c, r, h⟩ := gradMatrix_chiMK_entry_form I m κ k t i j
  change gradMatrix (I.chiMK κ m k t) (y + fun i => (n i : ℝ)) i j =
    gradMatrix (I.chiMK κ m k t) y i j
  rw [h, h]
  congr 1
  have hinv : (epsilon β I.Λ m)⁻¹ = ((⌈(I.Λ : ℝ) ^ (q β ^ m / (q β - 1))⌉₊ : ℕ) : ℝ) :=
    epsilon_inv_eq_ceil I hm
  have hdiv : ∀ z : ℝ, 2 * Real.pi * z / epsilon β I.Λ m =
      2 * Real.pi * (epsilon β I.Λ m)⁻¹ * z := fun z => by ring
  rw [hdiv, hdiv, hinv]
  have : 2 * Real.pi * (((⌈(I.Λ : ℝ) ^ (q β ^ m / (q β - 1))⌉₊ : ℕ) : ℝ)) *
      (y + fun i => (n i : ℝ)) r =
      2 * Real.pi * (((⌈(I.Λ : ℝ) ^ (q β ^ m / (q β - 1))⌉₊ : ℕ) : ℝ)) * y r +
        ((⌈(I.Λ : ℝ) ^ (q β ^ m / (q β - 1))⌉₊ : ℤ) * n r : ℤ) * (2 * Real.pi) := by
    simp only [Pi.add_apply]
    push_cast
    ring
  rw [this, Real.sin_add_int_mul_two_pi]

/-- The mean of each entry of `∇Χ_{m,k}` vanishes. -/
theorem spaceAvg_gradMatrix_chiMK {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (k : ℤ) (t : ℝ)
    (i j : Fin 2) : spaceAvg (fun y => gradMatrix (I.chiMK κ m k t) y i j) = 0 := by
  obtain ⟨c, r, h⟩ := gradMatrix_chiMK_entry_form I m κ k t i j
  have hfun : (fun y => gradMatrix (I.chiMK κ m k t) y i j) =
      fun y => c * Real.sin (2 * Real.pi * (epsilon β I.Λ m)⁻¹ * y r) := by
    funext y
    rw [h]
    congr 2
    ring
  rw [hfun]
  unfold spaceAvg
  rw [integral_const_mul]
  have h0 := spaceAvg_sin_epsilon I hm r
  unfold spaceAvg at h0
  rw [h0, mul_zero]

/-! ## Averages composed with the inverse flow -/

theorem spaceAvg_eq_cellAverage (f : Vec 2 → ℝ) : spaceAvg f = Infra.Ergodic.cellAverage f := by
  rw [Infra.Ergodic.cellAverage_eq_unitCellIntegral, Infra.Ergodic.unitCellSet_eq_torusUnitCell]
  exact (Infra.Torus.integral_unitCell_eq_unitCube f).symm

/-- A `ℤ²`-periodic function has the same space average after composing with `X⁻¹_{m-1,l}(t,·)`. -/
theorem spaceAvg_comp_xFlowInv (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) {g : Vec 2 → ℝ}
    (hg : Infra.Ergodic.IsZPeriodic g) :
    spaceAvg (fun x => g (I.xFlowInv hΦ m l t x)) = spaceAvg g := by
  have h := Infra.Ergodic.cellAverage_mul_comp_inv_eq (f := fun _ : Vec 2 => (1 : ℝ)) (g := g)
    (fun _ _ => rfl) hg (xFlowDiffeo I hΦ m l t)
  simp only [one_mul] at h
  rw [spaceAvg_eq_cellAverage, spaceAvg_eq_cellAverage]
  exact h

/-- `⟨∇Χ_{m,k}(t,·)⟩ = 0` and the inverse-flow average. -/
theorem spaceAvg_gradMatrix_chiMK_comp_xFlowInv (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m)
    (κm : ℝ) (k : ℤ) (l : ℤ) (t : ℝ) (i j : Fin 2) :
    spaceAvg (fun x => gradMatrix (I.chiMK κm m k t) (I.xFlowInv hΦ m l t x) i j) = 0 := by
  have hper : Infra.Ergodic.IsZPeriodic (fun y => gradMatrix (I.chiMK κm m k t) y i j) :=
    fun y n => congrFun (congrFun (gradMatrix_chiMK_periodic I hm κm k t y n) i) j
  rw [spaceAvg_comp_xFlowInv I hΦ m l t (g := fun y => gradMatrix (I.chiMK κm m k t) y i j) hper]
  exact spaceAvg_gradMatrix_chiMK I hm κm k t i j

theorem spaceAvg_gram_chiMK_comp_xFlowInv (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m)
    (κm : ℝ) (k l : ℤ) (t : ℝ) (i j : Fin 2) :
    spaceAvg (fun x => ((gradMatrix (I.chiMK κm m k t) (I.xFlowInv hΦ m l t x)).transpose *
        gradMatrix (I.chiMK κm m k t) (I.xFlowInv hΦ m l t x)) i j) =
      movingEnergyGramMean I κm m k t i j := by
  have hper : Infra.Ergodic.IsZPeriodic (fun y => ((gradMatrix (I.chiMK κm m k t) y).transpose *
      gradMatrix (I.chiMK κm m k t) y) i j) := fun y n => by
    have h : gradMatrix (I.chiMK κm m k t) (y + fun i => (n i : ℝ)) =
        gradMatrix (I.chiMK κm m k t) y := gradMatrix_chiMK_periodic I hm κm k t y n
    change ((gradMatrix (I.chiMK κm m k t) (y + fun i => (n i : ℝ))).transpose *
      gradMatrix (I.chiMK κm m k t) (y + fun i => (n i : ℝ))) i j =
        ((gradMatrix (I.chiMK κm m k t) y).transpose * gradMatrix (I.chiMK κm m k t) y) i j
    rw [h]
  rw [spaceAvg_comp_xFlowInv I hΦ m l t
    (g := fun y => ((gradMatrix (I.chiMK κm m k t) y).transpose *
      gradMatrix (I.chiMK κm m k t) y) i j) hper]
  rfl

/-! ## Linearity of the space average on continuous functions -/

theorem BracketFF.spaceAvg_const' (c : ℝ) : spaceAvg (fun _ : Vec 2 => c) = c := by
  unfold spaceAvg
  rw [setIntegral_const]
  have hvol : volume unitCube = 1 := by
    unfold unitCube
    rw [volume_pi, Measure.pi_pi]
    simp [Real.volume_Ioo]
  simp [Measure.real, hvol]

theorem BracketFF.spaceAvg_add' {f g : Vec 2 → ℝ} (hf : Continuous f) (hg : Continuous g) :
    spaceAvg (fun x => f x + g x) = spaceAvg f + spaceAvg g :=
  integral_add (integrableOn_unitCube_of_continuous hf) (integrableOn_unitCube_of_continuous hg)

theorem BracketFF.spaceAvg_const_mul' (c : ℝ) (f : Vec 2 → ℝ) :
    spaceAvg (fun x => c * f x) = c * spaceAvg f :=
  integral_const_mul c f

theorem BracketFF.spaceAvg_sum' {ι : Type*} (S : Finset ι) {f : ι → Vec 2 → ℝ}
    (hf : ∀ k ∈ S, Continuous (f k)) :
    spaceAvg (fun x => ∑ k ∈ S, f k x) = ∑ k ∈ S, spaceAvg (f k) :=
  integral_finsetSum S fun k hk => integrableOn_unitCube_of_continuous (hf k hk)

/-! ## The space average of `FᵗF` -/

/-- Continuity in `x` of the composed corrector gradient. -/
theorem BracketFF.continuous_gradMatrix_comp (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) {k : ℤ}
    (hk : Odd k) (l : ℤ) (t : ℝ) :
    Continuous (fun x : Vec 2 => gradMatrix (I.chiMK κm m k t) (I.xFlowInv hΦ m l t x)) :=
  (continuous_gradMatrix_chiMK I κm m hk).comp
    (continuous_const.prodMk (xFlowDiffeo I hΦ m l t).contDiff_invFun.continuous)

/-- One summand of `⟨FᵗF⟩`: the linear terms vanish and the quadratic term is the Gram mean. -/
theorem BracketFF.spaceAvg_summand (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) (κm t : ℝ)
    {k : ℤ} (hk : Odd k) (i j : Fin 2) :
    spaceAvg (fun x => ((I.xiMK m k t *
        ((gradMatrix (I.chiMK κm m k t) (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)).transpose i j +
          gradMatrix (I.chiMK κm m k t) (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) i j)) +
        I.xiMK m k t ^ 2 *
          ((gradMatrix (I.chiMK κm m k t) (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)).transpose *
            gradMatrix (I.chiMK κm m k t) (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)) i j)) =
      I.xiMK m k t ^ 2 * movingEnergyGramMean I κm m k t i j := by
  set l := lIdx β I.Λ m k
  have hA := BracketFF.continuous_gradMatrix_comp I hΦ m κm hk l t
  have h1 : Continuous fun x : Vec 2 =>
      (gradMatrix (I.chiMK κm m k t) (I.xFlowInv hΦ m l t x)).transpose i j :=
    (hA.matrix_transpose).matrix_elem i j
  have h2 : Continuous fun x : Vec 2 =>
      gradMatrix (I.chiMK κm m k t) (I.xFlowInv hΦ m l t x) i j := hA.matrix_elem i j
  have h3 : Continuous fun x : Vec 2 =>
      ((gradMatrix (I.chiMK κm m k t) (I.xFlowInv hΦ m l t x)).transpose *
        gradMatrix (I.chiMK κm m k t) (I.xFlowInv hΦ m l t x)) i j :=
    (hA.matrix_transpose.matrix_mul hA).matrix_elem i j
  have h12 : Continuous fun x : Vec 2 => I.xiMK m k t *
      ((gradMatrix (I.chiMK κm m k t) (I.xFlowInv hΦ m l t x)).transpose i j +
        gradMatrix (I.chiMK κm m k t) (I.xFlowInv hΦ m l t x) i j) := by fun_prop
  have h3' : Continuous fun x : Vec 2 => I.xiMK m k t ^ 2 *
      ((gradMatrix (I.chiMK κm m k t) (I.xFlowInv hΦ m l t x)).transpose *
        gradMatrix (I.chiMK κm m k t) (I.xFlowInv hΦ m l t x)) i j := by fun_prop
  rw [BracketFF.spaceAvg_add' h12 h3', BracketFF.spaceAvg_const_mul',
      BracketFF.spaceAvg_const_mul', BracketFF.spaceAvg_add' h1 h2]
  have e1 : spaceAvg (fun x : Vec 2 =>
      (gradMatrix (I.chiMK κm m k t) (I.xFlowInv hΦ m l t x)).transpose i j) = 0 := by
    simpa [Matrix.transpose_apply] using
      spaceAvg_gradMatrix_chiMK_comp_xFlowInv I hΦ hm κm k l t j i
  rw [e1, spaceAvg_gradMatrix_chiMK_comp_xFlowInv I hΦ hm κm k l t i j,
    spaceAvg_gram_chiMK_comp_xFlowInv I hΦ hm κm k l t i j]
  ring

/-- Entry `(i,j)` of `⟨FᵗF⟩`: `δ_{ij} + ∑_k ξ_{m,k}² ⟨(∇Χ_{m,k})ᵗ∇Χ_{m,k}⟩_{ij}`. -/
theorem spaceAvg_leadingGram_entry (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) (κm t : ℝ)
    (i j : Fin 2) :
    spaceAvg (fun x => ((leadingMatrix I hΦ m κm t x).transpose *
        leadingMatrix I hΦ m κm t x) i j) =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) i j +
        ∑ k ∈ (xiMK_odd_support_finite I hm t).toFinset,
          I.xiMK m k.1 t ^ 2 * movingEnergyGramMean I κm m k.1 t i j := by
  classical
  set S := (xiMK_odd_support_finite I hm t).toFinset
  have hpt : ∀ x : Vec 2, ((leadingMatrix I hΦ m κm t x).transpose *
        leadingMatrix I hΦ m κm t x) i j =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) i j + ∑ k ∈ S,
        ((I.xiMK m k.1 t *
          ((gradMatrix (I.chiMK κm m k.1 t)
              (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t x)).transpose i j +
            gradMatrix (I.chiMK κm m k.1 t) (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t x) i j)) +
          I.xiMK m k.1 t ^ 2 *
            ((gradMatrix (I.chiMK κm m k.1 t)
                (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t x)).transpose *
              gradMatrix (I.chiMK κm m k.1 t) (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t x)) i j) := by
    intro x
    rw [leadingMatrix_transpose_mul I hΦ hm κm t x]
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    congr 1
  simp_rw [hpt]
  have hcont : ∀ k ∈ S, Continuous fun x : Vec 2 =>
      ((I.xiMK m k.1 t *
          ((gradMatrix (I.chiMK κm m k.1 t)
              (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t x)).transpose i j +
            gradMatrix (I.chiMK κm m k.1 t) (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t x) i j)) +
          I.xiMK m k.1 t ^ 2 *
            ((gradMatrix (I.chiMK κm m k.1 t)
                (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t x)).transpose *
              gradMatrix (I.chiMK κm m k.1 t) (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t x)) i j) := by
    intro k _
    have hA := BracketFF.continuous_gradMatrix_comp I hΦ m κm k.2 (lIdx β I.Λ m k.1) t
    have h1 := (hA.matrix_transpose).matrix_elem i j
    have h2 := hA.matrix_elem i j
    have h3 := (hA.matrix_transpose.matrix_mul hA).matrix_elem i j
    fun_prop
  rw [BracketFF.spaceAvg_add' continuous_const (continuous_finsetSum S hcont),
      BracketFF.spaceAvg_const',
    BracketFF.spaceAvg_sum' S hcont]
  congr 1
  exact Finset.sum_congr rfl fun k _ => BracketFF.spaceAvg_summand I hΦ hm κm t k.2 i j

/-- The Gram means of the odd shear correctors are diagonal. -/
theorem movingEnergyGramMean_offDiag {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) {k : ℤ} (hk : Odd k) (t : ℝ)
    {i j : Fin 2} (hij : i ≠ j) : movingEnergyGramMean I κ m k t i j = 0 := by
  have hk4 : k % 4 = 1 ∨ k % 4 = 3 := by
    rcases hk with ⟨n, hn⟩
    omega
  rcases hk4 with h1 | h3
  · rw [movingEnergyGramMean_horizontal I hm κ k t h1]
    fin_cases i <;> fin_cases j <;> simp_all
  · rw [movingEnergyGramMean_vertical I hm κ k t h3]
    fin_cases i <;> fin_cases j <;> simp_all

/-- e.bracket.FF (8436–8465): `κ_m ⟨FᵗF⟩(t) = E_m(t)`. -/
theorem bracket_FF (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κm : ℝ} (_hκm : 0 < κm)
    (t : ℝ) :
    κm • leadingGramAvg I hΦ m κm t =
      movingEnergyReducedSourceMatrix I κm m t (xiMK_odd_support_finite I hm t).toFinset := by
  classical
  ext i j
  have hL : (κm • leadingGramAvg I hΦ m κm t) i j = κm *
      spaceAvg (fun x => ((leadingMatrix I hΦ m κm t x).transpose *
        leadingMatrix I hΦ m κm t x) i j) := by
    simp [leadingGramAvg, spaceAvgMat]
  rw [hL, spaceAvg_leadingGram_entry I hΦ hm κm t i j]
  unfold movingEnergyReducedSourceMatrix
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte, Matrix.one_apply_eq]
    rw [mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  · have hsum : ∑ k ∈ (xiMK_odd_support_finite I hm t).toFinset,
        I.xiMK m k.1 t ^ 2 * movingEnergyGramMean I κm m k.1 t i j = 0 :=
      Finset.sum_eq_zero fun k _ => by
        rw [movingEnergyGramMean_offDiag I hm κm k.2 t hij, mul_zero]
    simp [hij, hsum, Matrix.one_apply_ne hij]

/-! ## The second term of the break-up -/

/-- e.ergodic.break.up.second, pointwise in `t`, entrywise (via `l.flux.to.energy`). -/
theorem second_term_entry_abs_le {C₀ : ℝ} (hΦ : IsStreamSeq I Φ) (hCz : I.Czeta ≤ C₀)
    (hCh : I.Chat ≤ C₀) {m : ℕ} (hm : 1 ≤ m) {κm : ℝ} (hκm : 0 < κm) (t : ℝ)
    (hcondition : epsilon β I.Λ m ^ 2 ≤ κm * tau β I.Λ m / 2) (i j : Fin 2) :
    |(κm • leadingGramAvg I hΦ m κm t - I.flux κm m t) i j| ≤
      lFluxToEnergyConstant C₀ * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κm) *
        (epsilon β I.Λ m ^ 2 / (κm * tau β I.Λ m)) := by
  have h := (l_flux_to_energy I hCz hCh hm κm hκm t hcondition).2 i j
  rw [bracket_FF I hΦ hm hκm t, Matrix.sub_apply, abs_sub_comm, ← Matrix.sub_apply]
  exact h

/-- e.ergodic.break.up.second integrated in time. -/
theorem ergodic_break_up_second {C₀ : ℝ} (hΦ : IsStreamSeq I Φ) (hCz : I.Czeta ≤ C₀)
    (hCh : I.Chat ≤ C₀) {m : ℕ} (hm : 1 ≤ m) {κm : ℝ} (hκm : 0 < κm)
    (hcondition : epsilon β I.Λ m ^ 2 ≤ κm * tau β I.Λ m / 2) {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    |∫ t in (0 : ℝ)..1, gradQuad T (κm • leadingGramAvg I hΦ m κm t - I.flux κm m t) t| ≤
      2 * (lFluxToEnergyConstant C₀ * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κm) *
        (epsilon β I.Λ m ^ 2 / (κm * tau β I.Λ m))) *
        spaceTimeGradNormSq (fun t x => spaceGrad (T t) x) := by
  set B := lFluxToEnergyConstant C₀ * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κm) *
        (epsilon β I.Λ m ^ 2 / (κm * tau β I.Λ m)) with hB
  have hg : ContinuousOn (fun p : ℝ × Vec 2 => spaceGrad (T p.1) p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) :=
    (spaceGrad_continuousOn hT).mono (Set.prod_mono Set.Icc_subset_Ici_self subset_rfl)
  have hslice : ∀ t ∈ Set.Icc (0 : ℝ) 1, Continuous (spaceGrad (T t)) := fun t ht =>
    hg.comp_continuous (continuous_const.prodMk continuous_id) fun x => ⟨ht, Set.mem_univ _⟩
  have hQ : ContinuousOn (fun t => ∫ x in unitCube, vecNormSq (spaceGrad (T t) x))
      (Set.Icc (0 : ℝ) 1) :=
    continuousOn_integral_unitCube
      (h := fun t x => vecNormSq (spaceGrad (T t) x))
      (continuous_vecNormSq_two.comp_continuousOn hg)
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖gradQuad T (κm • leadingGramAvg I hΦ m κm t - I.flux κm m t) t‖ ≤
        2 * B * ∫ x in unitCube, vecNormSq (spaceGrad (T t) x) := fun t ht => by
    rw [Real.norm_eq_abs]
    exact abs_gradQuad_le (hslice t ht)
      (second_term_entry_abs_le I hΦ hCz hCh hm hκm t hcondition)
  have hint : IntervalIntegrable
      (fun t => 2 * B * ∫ x in unitCube, vecNormSq (spaceGrad (T t) x)) volume 0 1 :=
    intervalIntegrable_of_continuousOn_Icc (continuousOn_const.mul hQ)
  have h := intervalIntegral.norm_integral_le_of_norm_le (a := (0 : ℝ)) (b := 1)
    (f := fun t => gradQuad T (κm • leadingGramAvg I hΦ m κm t - I.flux κm m t) t)
    zero_le_one
    (Filter.Eventually.of_forall fun t ht => hbound t ⟨ht.1.le, ht.2⟩) hint
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
    ← spaceTimeGradNormSq_eq_intervalIntegral hg] at h
  exact h

end AVenhance.Infra.Section5.LeftToShow

end
