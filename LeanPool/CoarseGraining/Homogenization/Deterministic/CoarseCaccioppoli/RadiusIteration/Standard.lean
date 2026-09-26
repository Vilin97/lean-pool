/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.Height
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # Standard -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped BigOperators

/-- Geometric ratio used in the standard beta-dependent radius iteration.
It is close enough to `1` that the geometric loss has ratio bounded away from
`1`, but `1 - theta` is still explicitly comparable to `(max 1 beta)⁻¹`. -/
private noncomputable def coarseCaccioppoliStandardRadiusTheta (β : ℝ) : ℝ :=
  1 - (4 * max 1 β)⁻¹

private theorem coarseCaccioppoliStandardRadiusTheta_pos {β : ℝ} (_hβ : 0 ≤ β) :
    0 < coarseCaccioppoliStandardRadiusTheta β := by
  let M : ℝ := max 1 β
  have hM_ge_one : 1 ≤ M := by
    dsimp [M]
    exact le_max_left _ _
  have hM_pos : 0 < M := zero_lt_one.trans_le hM_ge_one
  have hinv_le_quarter : (4 * M)⁻¹ ≤ (1 / 4 : ℝ) := by
    have hfourM_pos : 0 < 4 * M := by positivity
    have hfour_pos : 0 < (4 : ℝ) := by norm_num
    have hfour_le : (4 : ℝ) ≤ 4 * M := by nlinarith
    have hraw : (4 * M)⁻¹ ≤ (4 : ℝ)⁻¹ :=
      (inv_le_inv₀ hfourM_pos hfour_pos).2 hfour_le
    simpa using hraw
  unfold coarseCaccioppoliStandardRadiusTheta
  dsimp [M] at *
  linarith

private theorem coarseCaccioppoliStandardRadiusTheta_lt_one {β : ℝ} (_hβ : 0 ≤ β) :
    coarseCaccioppoliStandardRadiusTheta β < 1 := by
  let M : ℝ := max 1 β
  have hM_ge_one : 1 ≤ M := by
    dsimp [M]
    exact le_max_left _ _
  have hM_pos : 0 < M := zero_lt_one.trans_le hM_ge_one
  have hinv_pos : 0 < (4 * M)⁻¹ := by positivity
  unfold coarseCaccioppoliStandardRadiusTheta
  dsimp [M] at *
  linarith

private theorem coarseCaccioppoliStandardRadiusTheta_le_one {β : ℝ} (hβ : 0 ≤ β) :
    coarseCaccioppoliStandardRadiusTheta β ≤ 1 :=
  (coarseCaccioppoliStandardRadiusTheta_lt_one hβ).le

private theorem coarseCaccioppoliStandardRadiusTheta_rpow_neg_le_four_thirds
    {β : ℝ} (hβ : 0 ≤ β) :
    Real.rpow (coarseCaccioppoliStandardRadiusTheta β) (-β) ≤
      (4 / 3 : ℝ) := by
  let M : ℝ := max 1 β
  let θ : ℝ := coarseCaccioppoliStandardRadiusTheta β
  have hM_ge_one : 1 ≤ M := by
    dsimp [M]
    exact le_max_left _ _
  have hM_pos : 0 < M := zero_lt_one.trans_le hM_ge_one
  have hβ_le_M : β ≤ M := by
    dsimp [M]
    exact le_max_right _ _
  have hθ_pos : 0 < θ := by
    dsimp [θ]
    exact coarseCaccioppoliStandardRadiusTheta_pos hβ
  have hθ_le_one : θ ≤ 1 := by
    dsimp [θ]
    exact coarseCaccioppoliStandardRadiusTheta_le_one hβ
  have hθM_ge :
      (3 / 4 : ℝ) ≤ Real.rpow θ M := by
    let u : ℝ := -((4 * M)⁻¹)
    have hu_lower : (-1 : ℝ) ≤ u := by
      dsimp [u]
      have hfourM_pos : 0 < 4 * M := by positivity
      have hinv_le_one : (4 * M)⁻¹ ≤ (1 : ℝ) := by
        have hone_pos : 0 < (1 : ℝ) := by norm_num
        have hone_le : (1 : ℝ) ≤ 4 * M := by nlinarith
        have hraw : (4 * M)⁻¹ ≤ (1 : ℝ)⁻¹ :=
          (inv_le_inv₀ hfourM_pos hone_pos).2 hone_le
        simpa using hraw
      linarith
    have hbern :=
      one_add_mul_self_le_rpow_one_add (s := u) hu_lower
        (p := M) hM_ge_one
    have hleft : 1 + M * u = (3 / 4 : ℝ) := by
      dsimp [u]
      field_simp [hM_pos.ne']
      ring
    have hone_add : 1 + u = θ := by
      dsimp [u, θ, coarseCaccioppoliStandardRadiusTheta, M]
      ring
    simpa [hleft, hone_add] using hbern
  have hnegM_le : Real.rpow θ (-M) ≤ (4 / 3 : ℝ) := by
    have hθM_pos : 0 < Real.rpow θ M := Real.rpow_pos_of_pos hθ_pos M
    have hthree_pos : 0 < (3 / 4 : ℝ) := by norm_num
    have hinv :
        (Real.rpow θ M)⁻¹ ≤ ((3 / 4 : ℝ)⁻¹) :=
      (inv_le_inv₀ hθM_pos hthree_pos).2 hθM_ge
    have hinv' : (Real.rpow θ M)⁻¹ ≤ (4 / 3 : ℝ) := by
      norm_num at hinv ⊢
      exact hinv
    have hneg_eq : Real.rpow θ (-M) = (Real.rpow θ M)⁻¹ := by
      simpa using Real.rpow_neg hθ_pos.le M
    exact hneg_eq.trans_le hinv'
  have hmono :
      Real.rpow θ (-β) ≤ Real.rpow θ (-M) :=
    Real.rpow_le_rpow_of_exponent_ge hθ_pos hθ_le_one (by linarith)
  exact hmono.trans hnegM_le

/-- The beta-dependent radius-iteration constant from the standard
hole-filling proof.  The factor `3` comes from summing a geometric series with
ratio at most `2 / 3`. -/
noncomputable def coarseCaccioppoliStandardRadiusIterationConst (β : ℝ) : ℝ :=
  let θ : ℝ := coarseCaccioppoliStandardRadiusTheta β
  3 * Real.rpow (1 - θ) (-β) * Real.rpow (2 / 3 : ℝ) (-β)

theorem coarseCaccioppoliStandardRadiusIterationConst_nonneg {β : ℝ} (hβ : 0 ≤ β) :
    0 ≤ coarseCaccioppoliStandardRadiusIterationConst β := by
  let θ : ℝ := coarseCaccioppoliStandardRadiusTheta β
  have hbase : 0 ≤ 1 - θ := by
    dsimp [θ]
    linarith [coarseCaccioppoliStandardRadiusTheta_le_one (β := β) hβ]
  unfold coarseCaccioppoliStandardRadiusIterationConst
  dsimp [θ]
  exact mul_nonneg
    (mul_nonneg (by norm_num) (Real.rpow_nonneg hbase _))
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3) _)

/-- Closed scalar form of the standard radius-iteration constant.  This is the
piece needed by the final Caccioppoli scalar envelope: the beta-dependent
iteration costs exactly a `(6 * max 1 beta)^beta` factor up to the harmless
front constant `3`. -/
theorem coarseCaccioppoliStandardRadiusIterationConst_eq_growth (β : ℝ) :
    coarseCaccioppoliStandardRadiusIterationConst β =
      3 * Real.rpow (6 * max 1 β) β := by
  let M : ℝ := max 1 β
  let θ : ℝ := coarseCaccioppoliStandardRadiusTheta β
  have hM_ge_one : 1 ≤ M := by
    dsimp [M]
    exact le_max_left _ _
  have hM_pos : 0 < M := zero_lt_one.trans_le hM_ge_one
  have hfourM_pos : 0 < 4 * M := by positivity
  have hthree_halves_pos : 0 < (3 / 2 : ℝ) := by norm_num
  have hbase : 1 - θ = (4 * M)⁻¹ := by
    dsimp [θ, coarseCaccioppoliStandardRadiusTheta, M]
    ring
  have hfirst :
      Real.rpow (1 - θ) (-β) = Real.rpow (4 * M) β := by
    rw [hbase]
    calc
      Real.rpow ((4 * M)⁻¹) (-β)
          = (Real.rpow ((4 * M)⁻¹) β)⁻¹ := by
            exact Real.rpow_neg (inv_nonneg.mpr hfourM_pos.le) β
      _ = ((Real.rpow (4 * M) β)⁻¹)⁻¹ := by
            exact congrArg Inv.inv (Real.inv_rpow hfourM_pos.le β)
      _ = Real.rpow (4 * M) β := by simp
  have hsecond :
      Real.rpow (2 / 3 : ℝ) (-β) = Real.rpow (3 / 2 : ℝ) β := by
    have hbase_nonneg : 0 ≤ (2 / 3 : ℝ) := by norm_num
    have hbase_eq : (2 / 3 : ℝ) = ((3 / 2 : ℝ))⁻¹ := by norm_num
    rw [hbase_eq]
    calc
      Real.rpow ((3 / 2 : ℝ)⁻¹) (-β)
          = (Real.rpow ((3 / 2 : ℝ)⁻¹) β)⁻¹ := by
            exact Real.rpow_neg (inv_nonneg.mpr hthree_halves_pos.le) β
      _ = ((Real.rpow (3 / 2 : ℝ) β)⁻¹)⁻¹ := by
            exact congrArg Inv.inv (Real.inv_rpow hthree_halves_pos.le β)
      _ = Real.rpow (3 / 2 : ℝ) β := by simp
  unfold coarseCaccioppoliStandardRadiusIterationConst
  dsimp [θ]
  change
    3 * Real.rpow (1 - coarseCaccioppoliStandardRadiusTheta β) (-β) *
        Real.rpow (2 / 3 : ℝ) (-β) =
      3 * Real.rpow (6 * max 1 β) β
  rw [show Real.rpow (1 - coarseCaccioppoliStandardRadiusTheta β) (-β) =
      Real.rpow (4 * M) β by simpa [θ] using hfirst, hsecond]
  calc
    3 * Real.rpow (4 * M) β * Real.rpow (3 / 2 : ℝ) β =
        3 * (Real.rpow (4 * M) β * Real.rpow (3 / 2 : ℝ) β) := by ring
    _ = 3 * Real.rpow ((4 * M) * (3 / 2 : ℝ)) β := by
          congr 1
          exact (Real.mul_rpow hfourM_pos.le hthree_halves_pos.le).symm
    _ = 3 * Real.rpow (6 * max 1 β) β := by
          congr 1
          congr 1
          dsimp [M]
          ring

/-- After taking the note-exponent root, the beta-dependent radius-iteration
constant has a dimensionless scalar bound.  This is the scalar cancellation
used by the note-facing Caccioppoli constant: the apparent beta growth is
absorbed by `sigma * beta <= 2`. -/
theorem coarseCaccioppoli_sigma_mul_standardRadiusIterationConst_root_le
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    let σ : ℝ := coarseCaccioppoliSigma s t
    let p : ℝ := 2 + 4 * s / σ
    σ * Real.rpow
        (coarseCaccioppoliStandardRadiusIterationConst
          (coarseCaccioppoliBeta s t)) p⁻¹ ≤ 36 := by
  let σ : ℝ := coarseCaccioppoliSigma s t
  let β : ℝ := coarseCaccioppoliBeta s t
  let p : ℝ := 2 + 4 * s / σ
  let base : ℝ := 6 * β
  have hσ_pos : 0 < σ := by
    dsimp [σ]
    exact coarseCaccioppoli_sigma_pos hst
  have hβ_ge_two : 2 ≤ β := by
    dsimp [β]
    exact coarseCaccioppoli_beta_ge_two hs hst
  have hβ_nonneg : 0 ≤ β := by linarith
  have hp_pos : 0 < p := by
    dsimp [p, σ]
    exact coarseCaccioppoli_noteExponent_pos hs hst
  have hp_ge_one : 1 ≤ p := by
    dsimp [p, σ]
    exact coarseCaccioppoli_noteExponent_ge_one hs hst
  have hβ_le_p : β ≤ p := by
    dsimp [β, p, σ]
    exact coarseCaccioppoli_beta_le_noteExponent hs hst
  have hp_inv_nonneg : 0 ≤ p⁻¹ := inv_nonneg.mpr hp_pos.le
  have hp_inv_le_one : p⁻¹ ≤ 1 := by
    exact inv_le_one_of_one_le₀ hp_ge_one
  have hβ_mul_inv_le_one : β * p⁻¹ ≤ 1 := by
    have hdiv : β / p ≤ 1 := by
      rw [div_le_iff₀ hp_pos]
      simpa using hβ_le_p
    simpa [div_eq_mul_inv] using hdiv
  have hbase_pos : 0 < base := by
    dsimp [base]
    positivity
  have hbase_nonneg : 0 ≤ base := hbase_pos.le
  have hbase_ge_one : 1 ≤ base := by
    dsimp [base]
    nlinarith
  have hthree_root_le :
      Real.rpow (3 : ℝ) p⁻¹ ≤ 3 := by
    calc
      Real.rpow (3 : ℝ) p⁻¹ ≤ Real.rpow (3 : ℝ) (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 3) hp_inv_le_one
      _ = 3 := by simp
  have hbase_root_le :
      Real.rpow base (β * p⁻¹) ≤ base := by
    calc
      Real.rpow base (β * p⁻¹) ≤ Real.rpow base (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hbase_ge_one hβ_mul_inv_le_one
      _ = base := by simp
  have hR_root_le :
      Real.rpow
          (coarseCaccioppoliStandardRadiusIterationConst β) p⁻¹ ≤
        3 * base := by
    rw [coarseCaccioppoliStandardRadiusIterationConst_eq_growth]
    have hmax : max 1 β = β := max_eq_right (by linarith)
    rw [hmax]
    have hsplit :
        Real.rpow (3 * Real.rpow base β) p⁻¹ =
          Real.rpow (3 : ℝ) p⁻¹ *
            Real.rpow (Real.rpow base β) p⁻¹ := by
      exact Real.mul_rpow
        (by norm_num : (0 : ℝ) ≤ 3)
        (Real.rpow_nonneg hbase_nonneg β)
    rw [show 6 * β = base by rfl, hsplit]
    have hbase_mul :
        Real.rpow (Real.rpow base β) p⁻¹ =
          Real.rpow base (β * p⁻¹) := by
      exact (Real.rpow_mul hbase_nonneg β p⁻¹).symm
    rw [hbase_mul]
    exact mul_le_mul hthree_root_le hbase_root_le
      (Real.rpow_nonneg hbase_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
  calc
    σ * Real.rpow
        (coarseCaccioppoliStandardRadiusIterationConst β) p⁻¹
        ≤ σ * (3 * base) := by
          exact mul_le_mul_of_nonneg_left hR_root_le hσ_pos.le
    _ = 18 * (σ * β) := by
          dsimp [base]
          ring
    _ ≤ 36 := by
          nlinarith [coarseCaccioppoli_sigma_mul_beta_le_two ht hst]

private theorem coarseCaccioppoli_radius_iteration_raw_of_sequence
    {F : ℝ → ℝ} {A β : ℝ} {ρ : ℕ → ℝ}
    (hstep : ∀ n : ℕ,
      F (ρ n) ≤ (1 / 2 : ℝ) * F (ρ (n + 1)) +
        A * Real.rpow (ρ (n + 1) - ρ n) (-β)) :
    ∀ N : ℕ,
      F (ρ 0) ≤
        (1 / 2 : ℝ) ^ N * F (ρ N) +
          A * Finset.sum (Finset.range N)
            (fun n : ℕ =>
              (1 / 2 : ℝ) ^ n *
                Real.rpow (ρ (n + 1) - ρ n) (-β)) := by
  intro N
  induction N with
  | zero =>
      simp
  | succ N hN =>
      have hstepN := hstep N
      calc
        F (ρ 0)
            ≤ (1 / 2 : ℝ) ^ N * F (ρ N) +
                A * Finset.sum (Finset.range N)
                  (fun n : ℕ =>
                    (1 / 2 : ℝ) ^ n *
                      Real.rpow (ρ (n + 1) - ρ n) (-β)) := hN
        _ ≤ (1 / 2 : ℝ) ^ N *
              ((1 / 2 : ℝ) * F (ρ (N + 1)) +
                A * Real.rpow (ρ (N + 1) - ρ N) (-β)) +
              A * Finset.sum (Finset.range N)
                (fun n : ℕ =>
                  (1 / 2 : ℝ) ^ n *
                    Real.rpow (ρ (n + 1) - ρ n) (-β)) := by
              gcongr
        _ = (1 / 2 : ℝ) ^ (N + 1) * F (ρ (N + 1)) +
              A * Finset.sum (Finset.range (N + 1))
                (fun n : ℕ =>
                  (1 / 2 : ℝ) ^ n *
                    Real.rpow (ρ (n + 1) - ρ n) (-β)) := by
              rw [Finset.sum_range_succ, pow_succ]
              ring

/-- Standard beta-dependent radius iteration on `[1/3,1]`.  Unlike the fixed
deterministic radius sequence, this is the note-facing hole-filling estimate:
the iteration constant grows like `(C * max 1 beta)^beta`. -/
theorem coarseCaccioppoli_standard_radius_iteration
    {F : ℝ → ℝ} {A β : ℝ}
    (hβ : 0 ≤ β) (hA : 0 ≤ A)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hrec : CoarseCaccioppoliRadiusRecurrence F A β) :
    F (1 / 3 : ℝ) ≤ A * coarseCaccioppoliStandardRadiusIterationConst β := by
  rcases hbounded with ⟨B, hB⟩
  let θ : ℝ := coarseCaccioppoliStandardRadiusTheta β
  let D : ℝ := (2 / 3 : ℝ)
  let pref : ℝ := Real.rpow (1 - θ) (-β) * Real.rpow D (-β)
  let ratio : ℝ := (1 / 2 : ℝ) * Real.rpow θ (-β)
  let ρ : ℕ → ℝ := fun n => 1 - θ ^ n * D
  have hθ_pos : 0 < θ := by
    dsimp [θ]
    exact coarseCaccioppoliStandardRadiusTheta_pos hβ
  have hθ_nonneg : 0 ≤ θ := hθ_pos.le
  have hθ_lt_one : θ < 1 := by
    dsimp [θ]
    exact coarseCaccioppoliStandardRadiusTheta_lt_one hβ
  have hθ_le_one : θ ≤ 1 := hθ_lt_one.le
  have hD_pos : 0 < D := by
    dsimp [D]
    norm_num
  have hD_nonneg : 0 ≤ D := hD_pos.le
  have hone_sub_θ_pos : 0 < 1 - θ := by linarith
  have hpref_nonneg : 0 ≤ pref := by
    dsimp [pref]
    exact mul_nonneg (Real.rpow_nonneg hone_sub_θ_pos.le _)
      (Real.rpow_nonneg hD_nonneg _)
  have hρ_zero : ρ 0 = (1 / 3 : ℝ) := by
    dsimp [ρ, D]
    norm_num
  have hpow_le_one : ∀ n : ℕ, θ ^ n ≤ 1 := by
    intro n
    exact pow_le_one₀ hθ_nonneg hθ_le_one
  have hρ_mem : ∀ n : ℕ, (1 / 3 : ℝ) ≤ ρ n ∧ ρ n ≤ 1 := by
    intro n
    have hpow_nonneg : 0 ≤ θ ^ n := pow_nonneg hθ_nonneg n
    have hpow_le : θ ^ n ≤ 1 := hpow_le_one n
    constructor
    · dsimp [ρ, D]
      nlinarith
    · dsimp [ρ, D]
      nlinarith
  have hgap_eq : ∀ n : ℕ,
      ρ (n + 1) - ρ n = (1 - θ) * θ ^ n * D := by
    intro n
    dsimp [ρ]
    rw [pow_succ]
    ring
  have hρ_lt : ∀ n : ℕ, ρ n < ρ (n + 1) := by
    intro n
    have hgap_pos : 0 < ρ (n + 1) - ρ n := by
      rw [hgap_eq n]
      positivity
    linarith
  have hstep : ∀ n : ℕ,
      F (ρ n) ≤ (1 / 2 : ℝ) * F (ρ (n + 1)) +
        A * Real.rpow (ρ (n + 1) - ρ n) (-β) := by
    intro n
    exact hrec (hρ_mem n).1 (hρ_lt n) (hρ_mem (n + 1)).2
  have hraw :=
    coarseCaccioppoli_radius_iteration_raw_of_sequence
      (F := F) (A := A) (β := β) (ρ := ρ) hstep
  have hratio_nonneg : 0 ≤ ratio := by
    dsimp [ratio]
    positivity
  have hratio_le_two_thirds : ratio ≤ (2 / 3 : ℝ) := by
    have hθpow : Real.rpow θ (-β) ≤ (4 / 3 : ℝ) := by
      simpa [θ] using
      coarseCaccioppoliStandardRadiusTheta_rpow_neg_le_four_thirds
        (β := β) hβ
    calc
      ratio = (1 / 2 : ℝ) * Real.rpow θ (-β) := by rfl
      _ ≤ (1 / 2 : ℝ) * (4 / 3 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hθpow (by norm_num)
      _ = (2 / 3 : ℝ) := by norm_num
  have hterm_le : ∀ n : ℕ,
      (1 / 2 : ℝ) ^ n * Real.rpow (ρ (n + 1) - ρ n) (-β) ≤
        pref * ratio ^ n := by
    intro n
    have hgap_nonneg : 0 ≤ ρ (n + 1) - ρ n := (sub_pos.mpr (hρ_lt n)).le
    have hθpow_nonneg : 0 ≤ θ ^ n := pow_nonneg hθ_nonneg n
    have hθrpow_nonneg : 0 ≤ Real.rpow θ (-β) :=
      Real.rpow_nonneg hθ_nonneg _
    have hθpow_rpow :
        Real.rpow (θ ^ n) (-β) = (Real.rpow θ (-β)) ^ n := by
      calc
        Real.rpow (θ ^ n) (-β)
            = Real.rpow (Real.rpow θ (n : ℝ)) (-β) := by
                simp [Real.rpow_natCast]
        _ = Real.rpow θ ((n : ℝ) * (-β)) := by
                exact (Real.rpow_mul hθ_nonneg (n : ℝ) (-β)).symm
        _ = Real.rpow θ ((-β) * (n : ℝ)) := by ring_nf
        _ = Real.rpow (Real.rpow θ (-β)) (n : ℝ) := by
                exact Real.rpow_mul hθ_nonneg (-β) (n : ℝ)
        _ = (Real.rpow θ (-β)) ^ n := by
                simp [Real.rpow_natCast]
    have hgap_rpow :
        Real.rpow ((1 - θ) * θ ^ n * D) (-β) =
          (Real.rpow (1 - θ) (-β) *
              Real.rpow (θ ^ n) (-β)) *
            Real.rpow D (-β) := by
      have hleft :
          Real.rpow ((1 - θ) * θ ^ n * D) (-β) =
            Real.rpow ((1 - θ) * θ ^ n) (-β) *
              Real.rpow D (-β) := by
        exact Real.mul_rpow
          (mul_nonneg hone_sub_θ_pos.le hθpow_nonneg) hD_nonneg
      have hsplit :
          Real.rpow ((1 - θ) * θ ^ n) (-β) =
            Real.rpow (1 - θ) (-β) *
              Real.rpow (θ ^ n) (-β) := by
        exact Real.mul_rpow hone_sub_θ_pos.le hθpow_nonneg
      rw [hleft, hsplit]
    calc
      (1 / 2 : ℝ) ^ n * Real.rpow (ρ (n + 1) - ρ n) (-β)
          = (1 / 2 : ℝ) ^ n *
              Real.rpow ((1 - θ) * θ ^ n * D) (-β) := by
                rw [hgap_eq n]
      _ =
          (1 / 2 : ℝ) ^ n *
            ((Real.rpow (1 - θ) (-β) *
                Real.rpow (θ ^ n) (-β)) *
              Real.rpow D (-β)) := by
                rw [hgap_rpow]
      _ =
          pref * ratio ^ n := by
                dsimp [pref, ratio]
                change
                  (1 / 2 : ℝ) ^ n *
                    ((Real.rpow (1 - θ) (-β) *
                        Real.rpow (θ ^ n) (-β)) *
                      Real.rpow D (-β)) =
                    (Real.rpow (1 - θ) (-β) * Real.rpow D (-β)) *
                      ((1 / 2 : ℝ) * Real.rpow θ (-β)) ^ n
                rw [hθpow_rpow, mul_pow]
                ring
      _ ≤ pref * ratio ^ n := le_rfl
  have hsum_le : ∀ N : ℕ,
      Finset.sum (Finset.range N)
          (fun n : ℕ =>
            (1 / 2 : ℝ) ^ n *
              Real.rpow (ρ (n + 1) - ρ n) (-β)) ≤
        3 * pref := by
    intro N
    have hgeom_summable :
        Summable (fun n : ℕ => ((2 / 3 : ℝ) ^ n)) :=
      summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2 / 3)
        (by norm_num : (2 / 3 : ℝ) < 1)
    calc
      Finset.sum (Finset.range N)
          (fun n : ℕ =>
            (1 / 2 : ℝ) ^ n *
              Real.rpow (ρ (n + 1) - ρ n) (-β))
          ≤ Finset.sum (Finset.range N)
              (fun n : ℕ => pref * ((2 / 3 : ℝ) ^ n)) := by
            refine Finset.sum_le_sum ?_
            intro n hn
            exact (hterm_le n).trans
              (mul_le_mul_of_nonneg_left
                (pow_le_pow_left₀ hratio_nonneg hratio_le_two_thirds n)
                hpref_nonneg)
      _ = pref * Finset.sum (Finset.range N)
              (fun n : ℕ => ((2 / 3 : ℝ) ^ n)) := by
            rw [Finset.mul_sum]
      _ ≤ pref * (∑' n : ℕ, ((2 / 3 : ℝ) ^ n)) := by
            exact mul_le_mul_of_nonneg_left
              (hgeom_summable.sum_le_tsum (Finset.range N)
                (fun n _ => pow_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3) n))
              hpref_nonneg
      _ = pref * 3 := by
            rw [tsum_geometric_of_lt_one
              (by norm_num : (0 : ℝ) ≤ 2 / 3)
              (by norm_num : (2 / 3 : ℝ) < 1)]
            norm_num
      _ = 3 * pref := by ring
  apply le_of_forall_pos_le_add
  intro ε hε
  have hpow :=
    (tendsto_pow_atTop_nhds_zero_of_abs_lt_one
      (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_const B
  rcases Metric.tendsto_atTop.1 hpow ε hε with ⟨N, hN⟩
  have hsmall_abs : |(1 / 2 : ℝ) ^ N * B| < ε := by
    simpa [dist_eq_norm, Real.norm_eq_abs] using hN N le_rfl
  have hsmall : (1 / 2 : ℝ) ^ N * B ≤ ε :=
    le_trans (le_abs_self _) hsmall_abs.le
  have hrawN := hraw N
  have hNmem := hρ_mem N
  calc
    F (1 / 3 : ℝ) = F (ρ 0) := by rw [hρ_zero]
    _ ≤ (1 / 2 : ℝ) ^ N * F (ρ N) +
          A * Finset.sum (Finset.range N)
            (fun n : ℕ =>
              (1 / 2 : ℝ) ^ n *
                Real.rpow (ρ (n + 1) - ρ n) (-β)) := hrawN
    _ ≤ (1 / 2 : ℝ) ^ N * B +
          A * Finset.sum (Finset.range N)
            (fun n : ℕ =>
              (1 / 2 : ℝ) ^ n *
                Real.rpow (ρ (n + 1) - ρ n) (-β)) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left (hB hNmem.1 hNmem.2)
                (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) N))
              le_rfl
    _ ≤ ε + A * (3 * pref) := by
            exact add_le_add hsmall
              (mul_le_mul_of_nonneg_left (hsum_le N) hA)
    _ = A * coarseCaccioppoliStandardRadiusIterationConst β + ε := by
            unfold coarseCaccioppoliStandardRadiusIterationConst
            dsimp [θ, pref]
            ring

end

end Homogenization
