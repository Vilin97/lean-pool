/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Iteration.Arithmetic
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.StartSmallness
public import LeanPool.CaffarelliKohnNirenberg.Pressure.OscillationLin34
public import LeanPool.CaffarelliKohnNirenberg.Setting.ExcessComparisonCore
public import LeanPool.CaffarelliKohnNirenberg.Setting.ExcessComparisonPressure
public import LeanPool.CaffarelliKohnNirenberg.Setting.Finiteness
public import LeanPool.CaffarelliKohnNirenberg.Setting.SliceNormBounds
public import LeanPool.CaffarelliKohnNirenberg.Statements.Theta

/-!
# Start

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-!
Route.lean integration contract.  The exact local statements exported by this
file and consumed by the final route are:

```
hstart : ∀ z ∈ vec3Ball 0 (3 / 4) ×ˢ Ioc (-(9 / 16 : ℝ)) 0,
  theta κ u Du p z (κ / 4) ≤ η ∧ lambda q f z (κ / 4) ≤ Λ₀

hiteration : ∀ z ∈ vec3Ball 0 (3 / 4) ×ˢ Ioc (-(9 / 16 : ℝ)) 0,
  ∀ r : ℝ, 0 < r → r ≤ κ / 4 →
    max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ (2 : ℕ)) ≤
      M * r ^ (2 / 5 : ℝ)

thmA_scaling_step :
  theta κ (rescaleVelocity μ z₀ u) (rescaleGradient μ z₀ Du)
      (rescalePressure μ z₀ p) ((0 : Vec3), (0 : ℝ)) (1 / 4) ≤ η ∧
    lambda q (rescaleForce μ z₀ f) ((0 : Vec3), (0 : ℝ)) (1 / 4) ≤ Λ₀ →
    theta κ u Du p z₀ (μ / 4) ≤ η ∧ lambda q f z₀ (μ / 4) ≤ Λ₀
```

The public `thmA_start_of_inputs` first returns a positive `ε₀` chosen from
`iterationKappa`, `iterationEta`, and `iterationLambda₀`; after the solution,
domain, and initial-data hypotheses are supplied, its only named analytic
inputs are `hCaccGamma` and `hLin34`, and it returns the displayed `hstart`.

The endgame input must consume the neighbourhood decay display produced from
these two statements: for a centre `z₀`, a positive `r₂`, and `M ≥ 1`, it
must use the containment and decay hypotheses at `r₂` and return, for every
`0 < r₃ < r₂ / 4`, an a.e. representative on the parabolic ball of radius
`r₃` with exponent `stepGamma₀ q`.  It must not bind the closed half-cylinder
representative, its uniform `C₄` bound, or the full regular-point conclusion
as an input.  The quantitative gluing and closure extension belong to
Route.lean.

The public start theorem chooses `ε₀` by `exists_theoremA_start_smallness` from
the numerical conventions.  Its named analytic estimates are therefore only
`hCaccGamma` and `hLin34`; the force and scalar start inequalities are local
consequences of that convention choice.
-/

private theorem pressureD_eq_delta_cube
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z : ParabolicPoint) {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I) :
    pressureD p z r = delta p z r ^ (3 : ℕ) := by
  unfold pressureD
  rw [sws_integral_abs_pow_eq_delta_cube hsol z hr hsub]
  field_simp [hr.ne']

private theorem quarter_subset_unit
    {z : ParabolicPoint}
    (hz : z ∈ vec3Ball 0 (3 / 4) ×ˢ Ioc (-(9 / 16 : ℝ)) 0) :
    parabolicCylinder z.1 z.2 (1 / 4) ⊆ parabolicCylinder 0 0 1 := by
  intro w hw
  rw [parabolicCylinder] at hw ⊢
  rcases hz with ⟨hzx, hzt⟩
  rcases hw with ⟨hwx, hwt⟩
  refine ⟨?_, ?_⟩
  · change vec3EuclideanNorm (w.1 - 0) < 1
    rw [sub_zero]
    have htriangle : vec3EuclideanNorm w.1 ≤
        vec3EuclideanNorm (w.1 - z.1) + vec3EuclideanNorm z.1 := by
      simpa [vec3EuclideanNorm_eq_l2, sub_eq_add_neg, add_assoc] using
        (norm_add_le (WithLp.toLp 2 (w.1 - z.1)) (WithLp.toLp 2 z.1))
    have hwx' : vec3EuclideanNorm (w.1 - z.1) < 1 / 4 := by simpa using hwx
    have hzx' : vec3EuclideanNorm z.1 < 3 / 4 := by
      simpa [mem_vec3Ball] using hzx
    nlinarith only [htriangle, hwx', hzx']
  · have hlow : -(1 : ℝ) < w.2 := by
      have hztlow : -(9 / 16 : ℝ) < z.2 := hzt.1
      have hwtlow := hwt.1
      nlinarith only [hztlow, hwtlow]
    have hlow' : 0 - (1 : ℝ) ^ 2 < w.2 := by simpa using hlow
    exact ⟨hlow', hwt.2.trans hzt.2⟩

/-- The quarter-cylinder data read directly from `eq:thmA-hyp`. -/
theorem thmA_quarter_data_of_hyp
    (q ε₀ : ℝ) (hq : 5 / 2 < q) (hε₀ : 0 ≤ ε₀)
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hQ₁ : closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I)
    (hthmA : (∫⁻ z in parabolicCylinder 0 0 1,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀) :
    ∀ z ∈ vec3Ball 0 (3 / 4) ×ˢ Ioc (-(9 / 16 : ℝ)) 0,
      gamma u z (1 / 4) ^ (3 : ℕ) ≤ 16 * ε₀ ∧
      delta p z (1 / 4) ^ (3 : ℕ) ≤ 16 * ε₀ ∧
      lambda q f z (1 / 4) ≤ ε₀ ^ (1 / q : ℝ) := by
  have _hsol := hsol
  intro z hz
  have hρ : 0 < (1 / 4 : ℝ) := by norm_num
  have hsubset := quarter_subset_unit hz
  have hclosure : closure (parabolicCylinder z.1 z.2 (1 / 4)) ⊆
      spaceTimeSet Ω I := (closure_mono hsubset).trans hQ₁
  have hsum : ∫⁻ w in parabolicCylinder z.1 z.2 (1 / 4),
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
          ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q ≤ ENNReal.ofReal ε₀ := by
    calc
      _ ≤ ∫⁻ w in parabolicCylinder z.1 z.2 (1 / 4),
          ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
            ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q := le_rfl
      _ ≤ ∫⁻ w in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
            ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q :=
        lintegral_mono_set hsubset
      _ ≤ ENNReal.ofReal ε₀ := hthmA
  have hvel : ∫⁻ w in parabolicCylinder z.1 z.2 (1 / 4),
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) ≤ ENNReal.ofReal ε₀ := by
    calc
      _ ≤ ∫⁻ w in parabolicCylinder z.1 z.2 (1 / 4),
          ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
            ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q := by
        refine lintegral_mono ?_
        intro w
        have hp : 0 ≤ ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) := by positivity
        have hf : 0 ≤ ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q := by positivity
        exact (le_add_of_nonneg_right hp).trans (le_add_of_nonneg_right hf)
      _ ≤ _ := hsum
  have hpress : ∫⁻ w in parabolicCylinder z.1 z.2 (1 / 4),
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) ≤ ENNReal.ofReal ε₀ := by
    calc
      _ ≤ ∫⁻ w in parabolicCylinder z.1 z.2 (1 / 4),
          ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
            ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q := by
        refine lintegral_mono ?_
        intro w
        have hu : 0 ≤ ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) := by positivity
        have hf : 0 ≤ ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q := by positivity
        exact (le_add_of_nonneg_left hu).trans (le_add_of_nonneg_right hf)
      _ ≤ _ := hsum
  have hforce : ∫⁻ w in parabolicCylinder z.1 z.2 (1 / 4),
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q ≤ ENNReal.ofReal ε₀ := by
    calc
      _ ≤ ∫⁻ w in parabolicCylinder z.1 z.2 (1 / 4),
          ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
            ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q := by
        refine lintegral_mono ?_
        intro w
        have hu : 0 ≤ ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) := by positivity
        have hp : 0 ≤ ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) := by positivity
        exact le_add_of_nonneg_left (add_nonneg hu hp)
      _ ≤ _ := hsum
  have hreal_vel : (∫⁻ w in parabolicCylinder z.1 z.2 (1 / 4),
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal ≤ ε₀ := by
    have htop := ne_of_lt (lt_of_le_of_lt hvel ENNReal.ofReal_lt_top)
    rw [← ENNReal.toReal_ofReal hε₀]
    exact (ENNReal.toReal_le_toReal htop ENNReal.ofReal_ne_top).2 hvel
  have hreal_press : (∫⁻ w in parabolicCylinder z.1 z.2 (1 / 4),
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal ≤ ε₀ := by
    have htop := ne_of_lt (lt_of_le_of_lt hpress ENNReal.ofReal_lt_top)
    rw [← ENNReal.toReal_ofReal hε₀]
    exact (ENNReal.toReal_le_toReal htop ENNReal.ofReal_ne_top).2 hpress
  have hreal_force : (∫⁻ w in parabolicCylinder z.1 z.2 (1 / 4),
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q).toReal ≤ ε₀ := by
    have htop := ne_of_lt (lt_of_le_of_lt hforce ENNReal.ofReal_lt_top)
    rw [← ENNReal.toReal_ofReal hε₀]
    exact (ENNReal.toReal_le_toReal htop ENNReal.ofReal_ne_top).2 hforce
  have hgamma : gamma u z (1 / 4) ^ (3 : ℕ) ≤ 16 * ε₀ := by
    rw [gamma_cube_eq u z (1 / 4) hρ]
    norm_num [Real.rpow_neg hρ.le]
    simpa [Real.rpow_natCast] using hreal_vel
  have hdelta : delta p z (1 / 4) ^ (3 : ℕ) ≤ 16 * ε₀ := by
    rw [delta_cube_eq p z (1 / 4) hρ]
    norm_num [Real.rpow_neg hρ.le]
    exact hreal_press
  have hqpos : 0 < q := lt_trans (by norm_num : (0 : ℝ) < 5 / 2) hq
  have hforcepow : lambda q f z (1 / 4) ^ q ≤ ε₀ := by
    have hLamPow := lambda_pow_eq q f z (1 / 4) hρ hqpos
    rw [hLamPow]
    have hfactor : ((1 / 4 : ℝ) ^ (3 - 5 / q)) ^ q ≤ 1 := by
      have hs : 3 - 5 / q > 0 := by
        have : 5 / q < (3 : ℝ) := (div_lt_iff₀ hqpos).2 (by nlinarith only [hq])
        linarith only [this]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (1 / 4 : ℝ))]
      exact Real.rpow_le_one (by norm_num) (by norm_num)
        (by positivity)
    have hpow : (∫⁻ w in parabolicCylinder z.1 z.2 (1 / 4),
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q).toReal ≤ ε₀ := hreal_force
    calc
      ((1 / 4 : ℝ) ^ (3 - 5 / q)) ^ q *
          (∫⁻ w in parabolicCylinder z.1 z.2 (1 / 4),
            ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q).toReal ≤
          1 * (∫⁻ w in parabolicCylinder z.1 z.2 (1 / 4),
            ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q).toReal :=
        mul_le_mul_of_nonneg_right hfactor ENNReal.toReal_nonneg
      _ ≤ ε₀ := by simpa using hpow
  have hLam : lambda q f z (1 / 4) ≤ ε₀ ^ (1 / q : ℝ) := by
    have hLamNonneg : 0 ≤ lambda q f z (1 / 4) := by
      unfold lambda
      positivity
    simpa [one_div] using
      (Real.le_rpow_inv_iff_of_pos hLamNonneg hε₀ hqpos).2 hforcepow
  exact ⟨hgamma, hdelta, hLam⟩

/-! The start lemma keeps the two remaining analytic displays visible at its
interface.  The excess comparison is discharged by the established
`pressureChat_le_eight_gamma_cube` theorem. -/

private lemma thmA_start_of_smallness_hDsq_1 :
    ∀ (q κ C₃₂ : ℝ) {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
      (z : Vec3 × ℝ),
      delta p z (κ / (4 : ℝ)) ^ (3 : ℕ) ≤
          C₃₂ *
            (κ⁻¹ ^ (2 : ℕ) * ((8 : ℝ) * gamma u z (1 / 4 : ℝ) ^ (3 : ℕ)) +
                κ * delta p z (1 / 4 : ℝ) ^ (3 : ℕ) +
              κ ^ (3 / 2 : ℝ) * lambda q f z (1 / 4 : ℝ) ^ (3 / 2 : ℝ)) →
        (0 : ℝ) ≤ delta p z (κ / (4 : ℝ)) →
          (0 : ℝ) ≤ delta p z (κ / (4 : ℝ)) ^ (3 : ℕ) →
            delta p z (κ / (4 : ℝ)) ^ (2 : ℕ) ≤
              (C₃₂ *
                  (κ⁻¹ ^ (2 : ℕ) * ((8 : ℝ) * gamma u z (1 / 4 : ℝ) ^ (3 : ℕ)) +
                      κ * delta p z (1 / 4 : ℝ) ^ (3 : ℕ) +
                    κ ^ (3 / 2 : ℝ) * lambda q f z (1 / 4 : ℝ) ^ (3 / 2 : ℝ))) ^
                (2 / 3 : ℝ)
    := by
  intro q κ C₃₂ u p f z hD hdelta_nonneg hDnonneg
  have hpow : delta p z (κ / 4) ^ (2 : ℕ) =
      (delta p z (κ / 4) ^ (3 : ℕ)) ^ (2 / 3 : ℝ) := by
    calc
      delta p z (κ / 4) ^ (2 : ℕ) =
          delta p z (κ / 4) ^ (2 : ℝ) :=
        (Real.rpow_natCast (delta p z (κ / 4)) 2).symm
      _ = (delta p z (κ / 4) ^ (3 : ℝ)) ^ (2 / 3 : ℝ) := by
        rw [← Real.rpow_mul hdelta_nonneg]
        norm_num
      _ = (delta p z (κ / 4) ^ (3 : ℕ)) ^ (2 / 3 : ℝ) := by
        exact congrArg (fun x : ℝ => x ^ (2 / 3 : ℝ))
          (Real.rpow_natCast (delta p z (κ / 4)) 3)
  rw [hpow]
  exact Real.rpow_le_rpow hDnonneg hD (by norm_num)

private lemma thmA_start_of_smallness_heps16_nonneg_2 :
    ∀ (q ε₀ : ℝ) {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      (∀ z ∈ vec3Ball (0 : Vec3) (3 / 4 : ℝ) ×ˢ Ioc (-(9 / 16 : ℝ)) (0 : ℝ),
          gamma u z (1 / 4 : ℝ) ^ (3 : ℕ) ≤ (16 : ℝ) * ε₀ ∧
            delta p z (1 / 4 : ℝ) ^ (3 : ℕ) ≤ (16 : ℝ) * ε₀ ∧
              lambda q f z (1 / 4 : ℝ) ≤ ε₀ ^ ((1 : ℝ) / q)) →
        ∀ z ∈ vec3Ball (0 : Vec3) (3 / 4 : ℝ) ×ˢ Ioc (-(9 / 16 : ℝ)) (0 : ℝ),
          (0 : ℝ) ≤ gamma u z (1 / 4 : ℝ) → gamma u z (1 / 4 : ℝ) ≤ ((16 : ℝ) * ε₀) ^ (1 / 3 : ℝ)
    := by
  intro q ε₀ u p f hquarter z hz hgamma_nonneg
  have hpow : gamma u z (1 / 4) =
      (gamma u z (1 / 4) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) := by
    calc
      gamma u z (1 / 4) = gamma u z (1 / 4) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (gamma u z (1 / 4) ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := by
        rw [← Real.rpow_mul hgamma_nonneg]
        norm_num
      _ = (gamma u z (1 / 4) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) := by
        exact congrArg (fun x : ℝ => x ^ (1 / 3 : ℝ))
          (Real.rpow_natCast (gamma u z (1 / 4)) 3)
  rw [hpow]
  exact Real.rpow_le_rpow (by positivity) (hquarter z hz).1 (by norm_num)

private lemma thmA_start_of_smallness_hdelta_3 :
    ∀ (q κ ε₀ : ℝ) {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      (∀ z ∈ vec3Ball (0 : Vec3) (3 / 4 : ℝ) ×ˢ Ioc (-(9 / 16 : ℝ)) (0 : ℝ),
          gamma u z (1 / 4 : ℝ) ^ (3 : ℕ) ≤ (16 : ℝ) * ε₀ ∧
            delta p z (1 / 4 : ℝ) ^ (3 : ℕ) ≤ (16 : ℝ) * ε₀ ∧
              lambda q f z (1 / 4 : ℝ) ≤ ε₀ ^ ((1 : ℝ) / q)) →
        ∀ z ∈ vec3Ball (0 : Vec3) (3 / 4 : ℝ) ×ˢ Ioc (-(9 / 16 : ℝ)) (0 : ℝ),
          (0 : ℝ) ≤ delta p z (κ / (4 : ℝ)) →
            (0 : ℝ) ≤ delta p z (1 / 4 : ℝ) → delta p z (1 / 4 : ℝ) ≤ ((16 : ℝ) * ε₀) ^ (1 / 3 : ℝ)
    := by
  intro q κ ε₀ u p f hquarter z hz hdelta_nonneg hdelta_nonneg
  have hpow : delta p z (1 / 4) =
      (delta p z (1 / 4) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) := by
    calc
      delta p z (1 / 4) = delta p z (1 / 4) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (delta p z (1 / 4) ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := by
        rw [← Real.rpow_mul hdelta_nonneg]
        norm_num
      _ = (delta p z (1 / 4) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) := by
        exact congrArg (fun x : ℝ => x ^ (1 / 3 : ℝ))
          (Real.rpow_natCast (delta p z (1 / 4)) 3)
  rw [hpow]
  exact Real.rpow_le_rpow (by positivity) (hquarter z hz).2.1 (by norm_num)

private lemma thmA_start_of_smallness_hD_numeric_4 :
    ∀ (q κ ε₀ C₃₂ : ℝ),
      (0 : ℝ) < κ →
        (0 : ℝ) ≤ C₃₂ →
          ∀ {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
            (∀ z ∈ vec3Ball (0 : Vec3) (3 / 4 : ℝ) ×ˢ Ioc (-(9 / 16 : ℝ)) (0 : ℝ),
                gamma u z (1 / 4 : ℝ) ^ (3 : ℕ) ≤ (16 : ℝ) * ε₀ ∧
                  delta p z (1 / 4 : ℝ) ^ (3 : ℕ) ≤ (16 : ℝ) * ε₀ ∧
                    lambda q f z (1 / 4 : ℝ) ≤ ε₀ ^ ((1 : ℝ) / q)) →
              ∀ z ∈ vec3Ball (0 : Vec3) (3 / 4 : ℝ) ×ˢ Ioc (-(9 / 16 : ℝ)) (0 : ℝ),
                (0 : ℝ) ≤ gamma u z (1 / 4 : ℝ) →
                  (0 : ℝ) ≤ delta p z (1 / 4 : ℝ) →
                    (0 : ℝ) ≤ lambda q f z (1 / 4 : ℝ) →
                      lambda q f z (1 / 4 : ℝ) ^ (3 / 2 : ℝ) ≤ (ε₀ ^ ((1 : ℝ) / q)) ^ (3 / 2 : ℝ) →
                        (C₃₂ *
                              (κ⁻¹ ^ (2 : ℕ) * ((8 : ℝ) * gamma u z (1 / 4 : ℝ) ^ (3 : ℕ)) +
                                  κ * delta p z (1 / 4 : ℝ) ^ (3 : ℕ) +
                                κ ^ (3 / 2 : ℝ) * lambda q f z (1 / 4 : ℝ) ^ (3 / 2 : ℝ))) ^
                            (2 / 3 : ℝ) ≤
                          (C₃₂ *
                              (κ⁻¹ ^ (2 : ℕ) * ((8 : ℝ) * ((16 : ℝ) * ε₀)) + κ * ((16 : ℝ) * ε₀) +
                                κ ^ (3 / 2 : ℝ) * (ε₀ ^ ((1 : ℝ) / q)) ^ (3 / 2 : ℝ))) ^
                            (2 / 3 : ℝ)
    := by
  intro q κ ε₀ C₃₂ hκ hC₃₂ u p f hquarter z hz hgamma_nonneg hdelta_nonneg hlambda_nonneg
    hlambda_three_halves
  apply Real.rpow_le_rpow
  · positivity
  · have hbase :
        κ⁻¹ ^ (2 : ℕ) * (8 * gamma u z (1 / 4) ^ (3 : ℕ)) +
            κ * delta p z (1 / 4) ^ (3 : ℕ) +
            κ ^ (3 / 2 : ℝ) * lambda q f z (1 / 4) ^ (3 / 2 : ℝ) ≤
          κ⁻¹ ^ (2 : ℕ) * (8 * (16 * ε₀)) +
            κ * (16 * ε₀) +
            κ ^ (3 / 2 : ℝ) * (ε₀ ^ (1 / q : ℝ)) ^ (3 / 2 : ℝ) := by
      gcongr
      · exact (hquarter z hz).1
      · exact (hquarter z hz).2.1
    exact mul_le_mul_of_nonneg_left hbase hC₃₂
  · norm_num

/-- Conditional form of `lem:thmA-start`, with the paper displays
`eq:caccioppoli-gamma` and `eq:lin35-force` named at the
interface. -/
private theorem thmA_start_of_smallness
    (q κ η Λ₀ ε₀ C₂₅ C₂₆ C₃₂ : ℝ)
    (hq : 5 / 2 < q) (hκ : 0 < κ) (hκle : κ ≤ 1 / 2)
    (hC₂₅ : 0 ≤ C₂₅) (hC₂₆ : 0 ≤ C₂₆) (hC₃₂ : 0 ≤ C₃₂)
    (hε₀ : 0 ≤ ε₀)
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hQ₁ : closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I)
    (hthmA : (∫⁻ z in parabolicCylinder 0 0 1,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀)
    (hCaccGamma : ∀ {z : ParabolicPoint} {r ρ : ℝ}, 0 < ρ → 0 < r →
      r ≤ ρ / 2 →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
      alpha u z r + beta u Du z r ≤
        C₂₅ * ((r / ρ) * gamma u z ρ +
          (r / ρ) ^ (-1 : ℝ) * gamma u z ρ ^ (3 / 2 : ℝ) +
          (r / ρ) ^ (-1 : ℝ) * delta p z ρ * gamma u z ρ ^ (1 / 2 : ℝ)) +
        C₂₆ * (r / ρ) ^ (-1 / 2 : ℝ) * gamma u z ρ ^ (1 / 2 : ℝ) *
          lambda q f z ρ ^ (1 / 2 : ℝ))
    (hLin34 : ∀ {z : ParabolicPoint} {r ρ : ℝ}, 0 < ρ → 0 < r →
      r ≤ ρ / 2 →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
      pressureD p z r ≤ C₃₂ *
        ((ρ / r) ^ (2 : ℕ) * pressureChat u z ρ +
          (r / ρ) * pressureD p z ρ +
          (r / ρ) ^ (3 / 2 : ℝ) * lambda q f z ρ ^ (3 / 2 : ℝ)))
    (hε : ε₀ ^ (1 / q : ℝ) ≤ Λ₀)
    (hsmall :
      C₂₅ * (κ * (16 * ε₀) ^ (1 / 3 : ℝ) +
          κ ^ (-1 : ℝ) * (16 * ε₀) ^ (1 / 2 : ℝ) +
          κ ^ (-1 : ℝ) * (16 * ε₀) ^ (1 / 3 : ℝ) *
            (16 * ε₀) ^ (1 / 6 : ℝ)) +
        C₂₆ * κ ^ (-1 / 2 : ℝ) * (16 * ε₀) ^ (1 / 6 : ℝ) *
          (ε₀ ^ (1 / q : ℝ)) ^ (1 / 2 : ℝ) +
        κ ^ (-4 : ℝ) *
          (C₃₂ * (κ⁻¹ ^ (2 : ℕ) * (8 * (16 * ε₀)) +
            κ * (16 * ε₀) +
            κ ^ (3 / 2 : ℝ) * (ε₀ ^ (1 / q : ℝ)) ^ (3 / 2 : ℝ))) ^
              (2 / 3 : ℝ) ≤ η) :
    ∀ z ∈ vec3Ball 0 (3 / 4) ×ˢ Ioc (-(9 / 16 : ℝ)) 0,
      theta κ u Du p z (κ / 4) ≤ η ∧ lambda q f z (κ / 4) ≤ Λ₀ := by
  have hquarter := thmA_quarter_data_of_hyp q ε₀ hq hε₀ hsol hQ₁ hthmA
  intro z hz
  have hρ : 0 < (1 / 4 : ℝ) := by norm_num
  have hr : 0 < κ / 4 := by positivity
  have hhalf : κ / 4 ≤ (1 / 4 : ℝ) / 2 := by
    have h := div_le_div_of_nonneg_right hκle (by norm_num : (0 : ℝ) ≤ 4)
    norm_num at h ⊢
    exact h
  have hclosure : closure (parabolicCylinder z.1 z.2 (1 / 4)) ⊆
      spaceTimeSet Ω I := (closure_mono (quarter_subset_unit hz)).trans hQ₁
  have hCacc := hCaccGamma (z := z) (r := κ / 4) (ρ := 1 / 4)
    hρ hr hhalf hclosure
  have hratio : (κ / 4 : ℝ) / (1 / 4 : ℝ) = κ := by field_simp
  have hCacc' : alpha u z (κ / 4) + beta u Du z (κ / 4) ≤
      C₂₅ * (κ * gamma u z (1 / 4) +
          κ ^ (-1 : ℝ) * gamma u z (1 / 4) ^ (3 / 2 : ℝ) +
          κ ^ (-1 : ℝ) * delta p z (1 / 4) *
            gamma u z (1 / 4) ^ (1 / 2 : ℝ)) +
        C₂₆ * κ ^ (-1 / 2 : ℝ) * gamma u z (1 / 4) ^ (1 / 2 : ℝ) *
          lambda q f z (1 / 4) ^ (1 / 2 : ℝ) := by
    simpa [hratio] using hCacc
  have hLin := hLin34 (z := z) (r := κ / 4) (ρ := 1 / 4) hρ hr hhalf hclosure
  have hDρ := pressureD_eq_delta_cube hsol z hρ hclosure
  have hDr := pressureD_eq_delta_cube hsol z hr
    ((closure_parabolicCylinder_mono hr.le (by nlinarith only [hκle])).trans hclosure)
  have hEx := pressureChat_le_eight_gamma_cube hsol hρ hclosure
  rw [hDr, hDρ] at hLin
  have hinvratio : (1 / 4 : ℝ) / (κ / 4) = κ⁻¹ := by field_simp
  rw [hinvratio, hratio] at hLin
  have hLin' : delta p z (κ / 4) ^ (3 : ℕ) ≤
      C₃₂ * (κ⁻¹ ^ (2 : ℕ) * pressureChat u z (1 / 4) +
        κ * delta p z (1 / 4) ^ (3 : ℕ) +
        κ ^ (3 / 2 : ℝ) * lambda q f z (1 / 4) ^ (3 / 2 : ℝ)) := by
    exact hLin
  have hD : delta p z (κ / 4) ^ (3 : ℕ) ≤
      C₃₂ * (κ⁻¹ ^ (2 : ℕ) * (8 * gamma u z (1 / 4) ^ (3 : ℕ)) +
        κ * delta p z (1 / 4) ^ (3 : ℕ) +
        κ ^ (3 / 2 : ℝ) * lambda q f z (1 / 4) ^ (3 / 2 : ℝ)) := by
    calc
      _ ≤ C₃₂ * (κ⁻¹ ^ (2 : ℕ) * pressureChat u z (1 / 4) +
          κ * delta p z (1 / 4) ^ (3 : ℕ) +
          κ ^ (3 / 2 : ℝ) * lambda q f z (1 / 4) ^ (3 / 2 : ℝ)) := hLin'
      _ ≤ _ := by
        gcongr
  have hdelta_nonneg : 0 ≤ delta p z (κ / 4) := by
    unfold delta
    positivity
  have hDnonneg : 0 ≤ delta p z (κ / 4) ^ (3 : ℕ) := by positivity
  have hDsq := @thmA_start_of_smallness_hDsq_1 q κ C₃₂ u p f z hD hdelta_nonneg hDnonneg
  have hgamma_nonneg : 0 ≤ gamma u z (1 / 4) := by
    unfold gamma
    positivity
  have hdelta_nonneg : 0 ≤ delta p z (1 / 4) := by
    unfold delta
    positivity
  have hlambda_nonneg : 0 ≤ lambda q f z (1 / 4) := by
    unfold lambda
    positivity
  have heps16_nonneg : 0 ≤ 16 * ε₀ := by positivity
  have hgamma := @thmA_start_of_smallness_heps16_nonneg_2 q ε₀ u p f hquarter z hz hgamma_nonneg
  have hdelta := @thmA_start_of_smallness_hdelta_3 q κ ε₀ u p f hquarter z hz (by assumption)
    hdelta_nonneg
  have hgamma_half : gamma u z (1 / 4) ^ (1 / 2 : ℝ) ≤
      (16 * ε₀) ^ (1 / 6 : ℝ) := by
    calc
      gamma u z (1 / 4) ^ (1 / 2 : ℝ) ≤
          ((16 * ε₀) ^ (1 / 3 : ℝ)) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow hgamma_nonneg hgamma (by norm_num)
      _ = (16 * ε₀) ^ (1 / 6 : ℝ) := by
        rw [← Real.rpow_mul heps16_nonneg]
        norm_num
  have hgamma_three_halves : gamma u z (1 / 4) ^ (3 / 2 : ℝ) ≤
      (16 * ε₀) ^ (1 / 2 : ℝ) := by
    calc
      gamma u z (1 / 4) ^ (3 / 2 : ℝ) ≤
          ((16 * ε₀) ^ (1 / 3 : ℝ)) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow hgamma_nonneg hgamma (by norm_num)
      _ = (16 * ε₀) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_mul heps16_nonneg]
        norm_num
  have hlambda_half : lambda q f z (1 / 4) ^ (1 / 2 : ℝ) ≤
      (ε₀ ^ (1 / q : ℝ)) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hlambda_nonneg (hquarter z hz).2.2 (by norm_num)
  have hlambda_three_halves : lambda q f z (1 / 4) ^ (3 / 2 : ℝ) ≤
      (ε₀ ^ (1 / q : ℝ)) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hlambda_nonneg (hquarter z hz).2.2 (by norm_num)
  have hCacc_numeric :
      C₂₅ * (κ * gamma u z (1 / 4) +
          κ ^ (-1 : ℝ) * gamma u z (1 / 4) ^ (3 / 2 : ℝ) +
          κ ^ (-1 : ℝ) * delta p z (1 / 4) *
            gamma u z (1 / 4) ^ (1 / 2 : ℝ)) +
        C₂₆ * κ ^ (-1 / 2 : ℝ) * gamma u z (1 / 4) ^ (1 / 2 : ℝ) *
          lambda q f z (1 / 4) ^ (1 / 2 : ℝ) ≤
      C₂₅ * (κ * (16 * ε₀) ^ (1 / 3 : ℝ) +
          κ ^ (-1 : ℝ) * (16 * ε₀) ^ (1 / 2 : ℝ) +
          κ ^ (-1 : ℝ) * (16 * ε₀) ^ (1 / 3 : ℝ) *
            (16 * ε₀) ^ (1 / 6 : ℝ)) +
        C₂₆ * κ ^ (-1 / 2 : ℝ) * (16 * ε₀) ^ (1 / 6 : ℝ) *
          (ε₀ ^ (1 / q : ℝ)) ^ (1 / 2 : ℝ) := by
    gcongr
  have hD_numeric := @thmA_start_of_smallness_hD_numeric_4 q κ ε₀ C₃₂ hκ hC₃₂ u p f hquarter z hz
    hgamma_nonneg hdelta_nonneg hlambda_nonneg hlambda_three_halves
  have hnumeric :
      C₂₅ * (κ * gamma u z (1 / 4) +
          κ ^ (-1 : ℝ) * gamma u z (1 / 4) ^ (3 / 2 : ℝ) +
          κ ^ (-1 : ℝ) * delta p z (1 / 4) *
            gamma u z (1 / 4) ^ (1 / 2 : ℝ)) +
        C₂₆ * κ ^ (-1 / 2 : ℝ) * gamma u z (1 / 4) ^ (1 / 2 : ℝ) *
          lambda q f z (1 / 4) ^ (1 / 2 : ℝ) +
        κ ^ (-4 : ℝ) *
          (C₃₂ * (κ⁻¹ ^ (2 : ℕ) * (8 * gamma u z (1 / 4) ^ (3 : ℕ)) +
            κ * delta p z (1 / 4) ^ (3 : ℕ) +
            κ ^ (3 / 2 : ℝ) * lambda q f z (1 / 4) ^ (3 / 2 : ℝ))) ^
              (2 / 3 : ℝ) ≤
      C₂₅ * (κ * (16 * ε₀) ^ (1 / 3 : ℝ) +
          κ ^ (-1 : ℝ) * (16 * ε₀) ^ (1 / 2 : ℝ) +
          κ ^ (-1 : ℝ) * (16 * ε₀) ^ (1 / 3 : ℝ) *
            (16 * ε₀) ^ (1 / 6 : ℝ)) +
        C₂₆ * κ ^ (-1 / 2 : ℝ) * (16 * ε₀) ^ (1 / 6 : ℝ) *
          (ε₀ ^ (1 / q : ℝ)) ^ (1 / 2 : ℝ) +
        κ ^ (-4 : ℝ) *
          (C₃₂ * (κ⁻¹ ^ (2 : ℕ) * (8 * (16 * ε₀)) +
            κ * (16 * ε₀) +
            κ ^ (3 / 2 : ℝ) * (ε₀ ^ (1 / q : ℝ)) ^ (3 / 2 : ℝ))) ^
              (2 / 3 : ℝ) := by
    exact add_le_add hCacc_numeric
      (mul_le_mul_of_nonneg_left hD_numeric (by positivity))
  have htheta : theta κ u Du p z (κ / 4) ≤ η := by
    unfold theta
    have hmult := mul_le_mul_of_nonneg_left hDsq
      (Real.rpow_nonneg hκ.le (-4 : ℝ))
    have hsum := add_le_add hCacc' hmult
    exact hsum.trans (hnumeric.trans hsmall)
  have hqpos : 0 < q := lt_trans (by norm_num : (0 : ℝ) < 5 / 2) hq
  have hsigma : 0 ≤ 3 - 5 / q := by
    have hfive : (5 : ℝ) < 3 * q := by nlinarith only [hq]
    have hdiv : 5 / q < (3 : ℝ) := (div_lt_iff₀ hqpos).2 hfive
    linarith only [hdiv]
  have hκone : κ ≤ 1 := by linarith only [hκle]
  have hLamMono := lambda_mono_radius_of_sws hsol z hr
    (by nlinarith only [hκle]) hclosure
  rw [hratio] at hLamMono
  have hκpow : κ ^ (3 - 5 / q) ≤ 1 :=
    Real.rpow_le_one hκ.le hκone hsigma
  have hLamQuarter : 0 ≤ lambda q f z (1 / 4) := hlambda_nonneg
  have hLamScale : lambda q f z (κ / 4) ≤ lambda q f z (1 / 4) := by
    calc
      lambda q f z (κ / 4) ≤ κ ^ (3 - 5 / q) * lambda q f z (1 / 4) := hLamMono
      _ ≤ lambda q f z (1 / 4) :=
        by simpa [mul_comm] using mul_le_of_le_one_right hLamQuarter hκpow
  exact ⟨htheta, hLamScale.trans ((hquarter z hz).2.2.trans hε)⟩

/-- The convention-driven form of `lem:thmA-start`.

The small-data threshold is chosen before the domain and the solution.  After
that choice, the only named analytic estimates needed by the start step are
the gamma-form Caccioppoli estimate and the pressure oscillation estimate.
-/
theorem thmA_start_of_inputs
    (q C₂₅ C₂₆ C₂₇ C₂₈ C₃₂ : ℝ)
    (hq : 5 / 2 < q) (hC₂₇ : 0 < C₂₇) (hC₂₈ : 0 < C₂₈)
    (hC₂₅ : 0 ≤ C₂₅) (hC₂₆ : 0 ≤ C₂₆) (hC₃₂ : 0 ≤ C₃₂) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) →
      (hQ₁ : closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I) →
      (hthmA : (∫⁻ z in parabolicCylinder 0 0 1,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
          ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀) →
      (hCaccGamma : ∀ {z : ParabolicPoint} {r ρ : ℝ}, 0 < ρ → 0 < r →
        r ≤ ρ / 2 →
        closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
        alpha u z r + beta u Du z r ≤
          C₂₅ * ((r / ρ) * gamma u z ρ +
            (r / ρ) ^ (-1 : ℝ) * gamma u z ρ ^ (3 / 2 : ℝ) +
            (r / ρ) ^ (-1 : ℝ) * delta p z ρ * gamma u z ρ ^ (1 / 2 : ℝ)) +
          C₂₆ * (r / ρ) ^ (-1 / 2 : ℝ) * gamma u z ρ ^ (1 / 2 : ℝ) *
            lambda q f z ρ ^ (1 / 2 : ℝ)) →
      (hLin34 : ∀ {z : ParabolicPoint} {r ρ : ℝ}, 0 < ρ → 0 < r →
        r ≤ ρ / 2 →
        closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
        pressureD p z r ≤ C₃₂ *
          ((ρ / r) ^ (2 : ℕ) * pressureChat u z ρ +
            (r / ρ) * pressureD p z ρ +
            (r / ρ) ^ (3 / 2 : ℝ) * lambda q f z ρ ^ (3 / 2 : ℝ))) →
      ∀ z ∈ vec3Ball 0 (3 / 4) ×ˢ Ioc (-(9 / 16 : ℝ)) 0,
        theta (iterationKappa C₂₇) u Du p z (iterationKappa C₂₇ / 4) ≤
            iterationEta C₂₇ ∧
          lambda q f z (iterationKappa C₂₇ / 4) ≤
            iterationLambda₀ C₂₇ C₂₈ := by
  obtain ⟨ε₀, hε₀, hε, hsmall⟩ := exists_theoremA_start_smallness
    q C₂₅ C₂₆ C₂₇ C₂₈ C₃₂ (by linarith only [hq]) hC₂₇ hC₂₈
  refine ⟨ε₀, hε₀, ?_⟩
  intro Ω I u Du p f hsol hQ₁ hthmA hCaccGamma hLin34
  have hκ : 0 < iterationKappa C₂₇ := iterationKappa_pos hC₂₇
  have hκle : iterationKappa C₂₇ ≤ 1 / 2 := iterationKappa_le_half C₂₇
  have hsmall' :
      C₂₅ * (iterationKappa C₂₇ * (16 * ε₀) ^ (1 / 3 : ℝ) +
          iterationKappa C₂₇ ^ (-1 : ℝ) * (16 * ε₀) ^ (1 / 2 : ℝ) +
          iterationKappa C₂₇ ^ (-1 : ℝ) * (16 * ε₀) ^ (1 / 3 : ℝ) *
            (16 * ε₀) ^ (1 / 6 : ℝ)) +
        C₂₆ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) * (16 * ε₀) ^ (1 / 6 : ℝ) *
          (ε₀ ^ (1 / q : ℝ)) ^ (1 / 2 : ℝ) +
        iterationKappa C₂₇ ^ (-4 : ℝ) *
          (C₃₂ * ((iterationKappa C₂₇)⁻¹ ^ (2 : ℕ) * (8 * (16 * ε₀)) +
            iterationKappa C₂₇ * (16 * ε₀) +
            iterationKappa C₂₇ ^ (3 / 2 : ℝ) *
              (ε₀ ^ (1 / q : ℝ)) ^ (3 / 2 : ℝ))) ^ (2 / 3 : ℝ) ≤
        iterationEta C₂₇ := by
    simpa [theoremAStartBound] using hsmall
  exact thmA_start_of_smallness q (iterationKappa C₂₇) (iterationEta C₂₇)
    (iterationLambda₀ C₂₇ C₂₈) ε₀ C₂₅ C₂₆ C₃₂ hq hκ hκle hC₂₅ hC₂₆ hC₃₂
    hε₀.le hsol hQ₁ hthmA hCaccGamma hLin34 hε hsmall'

end CKN
