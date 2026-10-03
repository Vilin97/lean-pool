/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.CorrTimeRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.CorrectorBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.CorrectorGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ShearFormula
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.IsCorrectorSol
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! The explicit one-mode corrector solves its parabolic equation. -/

@[expose] public section

noncomputable section

open MeasureTheory
open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section3

open AVenhance

/-- The small cutoff of a mode vanishes before its translated support starts. -/
theorem zetaMK_eq_zero_before_support {β : ℝ} (I : Ingredients β)
    {m : ℕ} (k : ℤ) (t : ℝ)
    (ht : t < ((k : ℝ) - 2 / 3) * tau β I.Λ m) :
    I.zetaMK m k t = 0 := by
  have hτ : 0 < tau β I.Λ m :=
    Infra.Ingredients.tau_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  let u := (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m
  have hu : u < -(2 / 3 : ℝ) := by
    apply (div_lt_iff₀ hτ).2
    nlinarith
  have hnot : u ∉ Set.Icc (-(2 / 3 : ℝ)) (2 / 3) := by
    intro hu'
    linarith [hu'.1]
  have hind : indIcc (-(2 / 3 : ℝ)) (2 / 3) u = 0 := by
    simp [indIcc, hnot]
  have hle := I.zeta_le_ind u
  have hzle : I.zeta u ≤ 0 := by simpa [hind] using hle
  have hnonneg := I.zeta_nonneg u
  change I.zeta u = 0
  exact le_antisymm hzle hnonneg

/-- The memory coefficient is zero before the support of its forcing begins. -/
theorem corrTime_eq_zero_before_support {β : ℝ} (I : Ingredients β)
    {m : ℕ} (κ : ℝ) (k : ℤ) (t : ℝ)
    (ht : t < ((k : ℝ) - 2 / 3) * tau β I.Λ m) :
    I.corrTime κ m k t = 0 := by
  unfold Ingredients.corrTime
  calc
    (∫ s in Set.Iic t, I.zetaProd m k s *
        Real.exp (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * (s - t))) =
      ∫ s in Set.Iic t, (0 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro s hs
        have hzs := zetaMK_eq_zero_before_support I k s (lt_of_le_of_lt hs ht)
        simp [Ingredients.zetaProd, hzs]
    _ = 0 := by simp

/-- Each scalar component of `chiMK` is jointly C² in time and space. -/
theorem chiMK_component_contDiff_two {β : ℝ} (I : Ingredients β)
    {m : ℕ} (κ : ℝ) (k : ℤ) (j : Fin 2) :
    ContDiff ℝ 2 (fun p : ℝ × Vec 2 => I.chiMK κ m k p.1 p.2 j) := by
  have ht : ContDiff ℝ 2
      (fun p : ℝ × Vec 2 => I.corrTime κ m k p.1) := by
    exact (corrTime_contDiff_two I κ k).comp contDiff_fst
  have hu0 : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec 2 => uShear β I.Λ m k x j) := by
    unfold uShear
    split_ifs <;> fin_cases j <;> simp_all only [Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero,
        Fin.isValue, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.isValue,
        Fin.zero_eta, Matrix.cons_val_zero, Fin.isValue, Fin.mk_one, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Pi.zero_apply, Pi.zero_apply] <;> fun_prop
  have hu : ContDiff ℝ 2
      (fun p : ℝ × Vec 2 => uShear β I.Λ m k p.2 j) := by
    exact hu0.of_le (by simp) |>.comp contDiff_snd
  have hshape : (fun p : ℝ × Vec 2 => I.chiMK κ m k p.1 p.2 j) =
      fun p => -(I.corrTime κ m k p.1) * uShear β I.Λ m k p.2 j := by
    funext p
    simp [Ingredients.chiMK, Pi.smul_apply, smul_eq_mul]
  rw [hshape]
  exact ht.neg.mul hu

theorem ChiMKCorrector.spaceLap_zero_function (x : Vec 2) :
    spaceLap (fun _ : Vec 2 => (0 : ℝ)) x = 0 := by
  simp [spaceLap, AVenhance.spaceGrad]

theorem ChiMKCorrector.chiMK_spaceLap_of_zero_component {β : ℝ} (I : Ingredients β)
    {m : ℕ} (κ : ℝ) (k : ℤ) (t : ℝ) (x : Vec 2) (j : Fin 2)
    (hzero : (fun y => I.chiMK κ m k t y j) = fun _ => 0) :
    spaceLap (fun y => I.chiMK κ m k t y j) x =
      -(4 * Real.pi ^ 2 / epsilon β I.Λ m ^ 2) * I.chiMK κ m k t x j := by
  calc
    spaceLap (fun y => I.chiMK κ m k t y j) x =
        spaceLap (fun _ : Vec 2 => (0 : ℝ)) x := by rw [hzero]
    _ = 0 := ChiMKCorrector.spaceLap_zero_function x
    _ = -(4 * Real.pi ^ 2 / epsilon β I.Λ m ^ 2) *
        I.chiMK κ m k t x j := by rw [congrFun hzero x]; simp

theorem ChiMKCorrector.chiMK_spaceLap_one_active {β : ℝ} (I : Ingredients β)
    {m : ℕ} (κ : ℝ) (k : ℤ) (t : ℝ) (x : Vec 2)
    (hk : k % 4 = 1) :
    spaceLap (fun y => I.chiMK κ m k t y 1) x =
      -(4 * Real.pi ^ 2 / epsilon β I.Λ m ^ 2) *
        I.chiMK κ m k t x 1 := by
  let ε := epsilon β I.Λ m
  let freq := 2 * Real.pi / ε
  let A := 4 * Real.pi ^ 2 * a β I.Λ m * I.corrTime κ m k t
  have hε : ε ≠ 0 := ne_of_gt
    (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le)
  have hfreq (y : ℝ) : 2 * Real.pi * y / ε = freq * y := by
    dsimp [freq]
    field_simp [hε]
  have hgrad0 : (fun y => spaceGrad (fun z => I.chiMK κ m k t z 1) y 0) =
      fun y => A * Real.sin (freq * y 0) := by
    funext y
    rw [chiMK_spaceGrad_one I κ k t y hk hε]
    rw [hfreq]
  have hgrad1 : (fun y => spaceGrad (fun z => I.chiMK κ m k t z 1) y 1) =
      fun _ => 0 := by
    funext y
    have h := chiMK_spaceGrad_one_all I κ k t y 1 hk hε
    simpa using h
  have hchi : I.chiMK κ m k t x 1 =
      -(I.corrTime κ m k t) *
        (2 * Real.pi * a β I.Λ m * ε * Real.cos (freq * x 0)) := by
    calc
      I.chiMK κ m k t x 1 =
          -(I.corrTime κ m k t * uShear β I.Λ m k x 1) := by
        simp [Ingredients.chiMK, Pi.smul_apply, smul_eq_mul]
      _ = -(I.corrTime κ m k t) *
          (2 * Real.pi * a β I.Λ m * ε * Real.cos (freq * x 0)) := by
        have hu : uShear β I.Λ m k x 1 =
            2 * Real.pi * a β I.Λ m * ε *
              Real.cos (2 * Real.pi * x 0 / ε) := by
          simp [uShear, hk, ε]
        rw [hu, hfreq]
        ring
  unfold spaceLap
  simp only [Fin.sum_univ_two]
  rw [hgrad0, hgrad1]
  rw [spaceGrad_sineCoordinate A freq 0 0 x]
  have hzeroGrad : spaceGrad (fun _ : Vec 2 => (0 : ℝ)) x 1 = 0 := by
    simp [AVenhance.spaceGrad]
  rw [hzeroGrad]
  simp only [ite_true]
  rw [hchi]
  dsimp [A, freq, ε]
  field_simp [hε]
  ring

theorem ChiMKCorrector.chiMK_spaceLap_three_active {β : ℝ} (I : Ingredients β)
    {m : ℕ} (κ : ℝ) (k : ℤ) (t : ℝ) (x : Vec 2)
    (hk : k % 4 = 3) :
    spaceLap (fun y => I.chiMK κ m k t y 0) x =
      -(4 * Real.pi ^ 2 / epsilon β I.Λ m ^ 2) *
        I.chiMK κ m k t x 0 := by
  let ε := epsilon β I.Λ m
  let freq := 2 * Real.pi / ε
  let A := -(4 * Real.pi ^ 2 * a β I.Λ m * I.corrTime κ m k t)
  have hε : ε ≠ 0 := ne_of_gt
    (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le)
  have hfreq (y : ℝ) : 2 * Real.pi * y / ε = freq * y := by
    dsimp [freq]
    field_simp [hε]
  have hgrad0 : (fun y => spaceGrad (fun z => I.chiMK κ m k t z 0) y 0) =
      fun _ => 0 := by
    funext y
    have h := chiMK_spaceGrad_three_all I κ k t y 0 hk hε
    simpa using h
  have hgrad1 : (fun y => spaceGrad (fun z => I.chiMK κ m k t z 0) y 1) =
      fun y => A * Real.sin (freq * y 1) := by
    funext y
    rw [chiMK_spaceGrad_three I κ k t y hk hε]
    rw [hfreq]
  have hchi : I.chiMK κ m k t x 0 =
      I.corrTime κ m k t *
        (2 * Real.pi * a β I.Λ m * ε * Real.cos (freq * x 1)) := by
    calc
      I.chiMK κ m k t x 0 =
          -(I.corrTime κ m k t * uShear β I.Λ m k x 0) := by
        simp [Ingredients.chiMK, Pi.smul_apply, smul_eq_mul]
      _ = I.corrTime κ m k t *
          (2 * Real.pi * a β I.Λ m * ε * Real.cos (freq * x 1)) := by
        have hu : uShear β I.Λ m k x 0 =
            -(2 * Real.pi * a β I.Λ m * ε *
              Real.cos (2 * Real.pi * x 1 / ε)) := by
          simp [uShear, hk, ε]
        rw [hu, hfreq]
        ring
  unfold spaceLap
  simp only [Fin.sum_univ_two]
  rw [hgrad0, hgrad1]
  rw [spaceGrad_sineCoordinate A freq 1 1 x]
  have hzeroGrad : spaceGrad (fun _ : Vec 2 => (0 : ℝ)) x 0 = 0 := by
    simp [AVenhance.spaceGrad]
  rw [hzeroGrad]
  simp only [ite_true]
  rw [hchi]
  dsimp [A, freq, ε]
  field_simp [hε]
  ring

/-- Every single-mode corrector component is a spatial Laplacian eigenfunction
with its shear frequency. -/
theorem chiMK_component_spaceLap_eigen {β : ℝ} (I : Ingredients β)
    {m : ℕ} (κ : ℝ) (k : ℤ) (t : ℝ) (x : Vec 2) (j : Fin 2) :
    spaceLap (fun y => I.chiMK κ m k t y j) x =
      -(4 * Real.pi ^ 2 / epsilon β I.Λ m ^ 2) *
        I.chiMK κ m k t x j := by
  by_cases hk1 : k % 4 = 1
  · fin_cases j
    · have hzero : (fun y => I.chiMK κ m k t y 0) = fun _ => 0 := by
        funext y
        simp [Ingredients.chiMK, uShear, hk1]
      simpa using ChiMKCorrector.chiMK_spaceLap_of_zero_component I κ k t x 0 hzero
    · exact ChiMKCorrector.chiMK_spaceLap_one_active I κ k t x hk1
  · by_cases hk3 : k % 4 = 3
    · fin_cases j
      · exact ChiMKCorrector.chiMK_spaceLap_three_active I κ k t x hk3
      · have hzero : (fun y => I.chiMK κ m k t y 1) = fun _ => 0 := by
          funext y
          simp [Ingredients.chiMK, uShear, hk3]
        simpa using ChiMKCorrector.chiMK_spaceLap_of_zero_component I κ k t x 1 hzero
    · have hzero (j : Fin 2) : (fun y => I.chiMK κ m k t y j) = fun _ => 0 := by
        funext y
        simp [Ingredients.chiMK, uShear, hk1, hk3]
      exact ChiMKCorrector.chiMK_spaceLap_of_zero_component I κ k t x j (hzero j)

/-- The time derivative of one explicit corrector component. -/
theorem chiMK_component_hasDerivAt {β : ℝ} (I : Ingredients β)
    {m : ℕ} (κ : ℝ) (k : ℤ) (t : ℝ) (x : Vec 2) (j : Fin 2) :
    HasDerivAt (fun s => I.chiMK κ m k s x j)
      (-(I.zetaProd m k t -
          (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) *
            I.corrTime κ m k t) * uShear β I.Λ m k x j) t := by
  have h := (corrTime_hasDerivAt I (m := m) κ k t).neg.mul_const
    (uShear β I.Λ m k x j)
  simpa [Ingredients.chiMK, Pi.smul_apply, smul_eq_mul] using h

theorem ChiMKCorrector.spaceGrad_zero_of_fun_eq_zero {f : Vec 2 → ℝ}
    (hf : f = fun _ => (0 : ℝ)) (x : Vec 2) (i : Fin 2) :
    spaceGrad f x i = 0 := by
  rw [hf]
  simp [AVenhance.spaceGrad]

/-- The active shear is orthogonal to the corrector gradient, so its transport
of `e_j + ∇χ_j` is exactly its `j`th component. -/
theorem chiMK_transport_identity {β : ℝ} (I : Ingredients β)
    {m : ℕ} (κ : ℝ) (k : ℤ) (t : ℝ) (x : Vec 2) (j : Fin 2) :
    ∑ i : Fin 2, uShear β I.Λ m k x i *
      (basisVec j i + spaceGrad (fun y => I.chiMK κ m k t y j) x i) =
        uShear β I.Λ m k x j := by
  have hε : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hεne : epsilon β I.Λ m ≠ 0 := ne_of_gt hε
  by_cases h1 : k % 4 = 1
  · fin_cases j
    · have hzero : (fun y => I.chiMK κ m k t y 0) = fun _ => 0 := by
        funext y
        simp [Ingredients.chiMK, uShear, h1]
      have hg0 := ChiMKCorrector.spaceGrad_zero_of_fun_eq_zero hzero x 0
      have hg1 := ChiMKCorrector.spaceGrad_zero_of_fun_eq_zero hzero x 1
      simp [Fin.sum_univ_two, uShear, h1, basisVec_apply, hg0, hg1]
    · have hg1 : spaceGrad (fun y => I.chiMK κ m k t y 1) x 1 = 0 := by
        have h := chiMK_spaceGrad_one_all I κ k t x 1 h1 hεne
        simpa using h
      simp [Fin.sum_univ_two, uShear, h1, basisVec_apply, hg1]
  · by_cases h3 : k % 4 = 3
    · fin_cases j
      · have hg0 : spaceGrad (fun y => I.chiMK κ m k t y 0) x 0 = 0 := by
          have h := chiMK_spaceGrad_three_all I κ k t x 0 h3 hεne
          simpa using h
        simp [Fin.sum_univ_two, uShear, h3, basisVec_apply, hg0]
      · have hzero : (fun y => I.chiMK κ m k t y 1) = fun _ => 0 := by
          funext y
          simp [Ingredients.chiMK, uShear, h3]
        have hg0 := ChiMKCorrector.spaceGrad_zero_of_fun_eq_zero hzero x 0
        have hg1 := ChiMKCorrector.spaceGrad_zero_of_fun_eq_zero hzero x 1
        simp [Fin.sum_univ_two, uShear, h3, basisVec_apply, hg0, hg1]
    · simp [uShear, h1, h3]

/-- The explicit component solves the parabolic equation in direction
`e_j`. -/
theorem chiMK_component_hasCorrectorPDE {β : ℝ} (I : Ingredients β)
    {m : ℕ} (κ : ℝ) (k : ℤ) (j : Fin 2) :
    ∀ t x, HasDerivAt (fun s => I.chiMK κ m k s x j)
      (κ * spaceLap (fun y => I.chiMK κ m k t y j) x -
        I.zetaProd m k t *
          ∑ i : Fin 2, uShear β I.Λ m k x i *
            (basisVec j i +
              spaceGrad (fun y => I.chiMK κ m k t y j) x i)) t := by
  intro t x
  have hderiv := chiMK_component_hasDerivAt I (m := m) κ k t x j
  have hlap := chiMK_component_spaceLap_eigen I (m := m) κ k t x j
  have htransport := chiMK_transport_identity I (m := m) κ k t x j
  have hε : epsilon β I.Λ m ≠ 0 := ne_of_gt
    (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le)
  have hvalue :
      -(I.zetaProd m k t -
          (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) *
            I.corrTime κ m k t) * uShear β I.Λ m k x j =
        κ * spaceLap (fun y => I.chiMK κ m k t y j) x -
          I.zetaProd m k t *
            ∑ i : Fin 2, uShear β I.Λ m k x i *
              (basisVec j i +
                spaceGrad (fun y => I.chiMK κ m k t y j) x i) := by
    rw [hlap, htransport]
    simp only [Ingredients.chiMK, Pi.smul_apply, smul_eq_mul]
    field_simp [hε]
    ring
  exact hderiv.congr_deriv hvalue

/-- The explicit corrector vanishes before its support interval begins. -/
theorem chiMK_component_zero_before_support {β : ℝ} (I : Ingredients β)
    {m : ℕ} (κ : ℝ) (k : ℤ) (j : Fin 2) (t : ℝ) (x : Vec 2)
    (ht : t < (-(2 / 3) + (k : ℝ)) * tau β I.Λ m) :
    I.chiMK κ m k t x j = 0 := by
  have ht' : t < ((k : ℝ) - 2 / 3) * tau β I.Λ m := by
    convert ht using 1
    ring
  simp [Ingredients.chiMK, Pi.smul_apply, smul_eq_mul,
    corrTime_eq_zero_before_support I κ k t ht']

/-- The explicit single-mode corrector satisfies the equation and
initial cutoff condition. -/
theorem chiMK_isCorrectorSol {β : ℝ} (I : Ingredients β)
    (κ : ℝ) (m : ℕ) (k : ℤ) (j : Fin 2) :
    I.IsCorrectorSol κ m k (basisVec j)
      (fun t x => I.chiMK κ m k t x j) := by
  constructor
  · exact chiMK_component_hasCorrectorPDE I κ k j
  · intro t x ht
    exact chiMK_component_zero_before_support I κ k j t x ht

/-- The explicit `chiMK` component has all of the existence-side properties
in the statement of the diffusivity-recursion estimate: joint `C²` regularity, a global bound, and
    the
corrector equation with its prescribed past support. -/
theorem chiMK_component_isBoundedCorrectorSol {β : ℝ}
    (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (hκ : 0 < κ)
    (k : ℤ) (j : Fin 2) :
    ContDiff ℝ 2 (fun p : ℝ × Vec 2 => I.chiMK κ m k p.1 p.2 j) ∧
      (∃ B : ℝ, ∀ t x, |I.chiMK κ m k t x j| ≤ B) ∧
      I.IsCorrectorSol κ m k (basisVec j)
        (fun t x => I.chiMK κ m k t x j) := by
  refine ⟨chiMK_component_contDiff_two I κ k j, ?_,
    chiMK_isCorrectorSol I κ m k j⟩
  refine ⟨(4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2)⁻¹ *
      |2 * Real.pi * a β I.Λ m * epsilon β I.Λ m|, ?_⟩
  intro t x
  exact chiMK_component_abs_le I hm κ hκ k t x j

end AVenhance.Infra.Section3
