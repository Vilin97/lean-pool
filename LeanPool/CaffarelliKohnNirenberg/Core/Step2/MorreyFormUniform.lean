/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step2.MorreyForm
public import LeanPool.CaffarelliKohnNirenberg.Core.Step2.MorreyFormFixedScale

/-!
# Morrey Form Uniform

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

noncomputable section

namespace CKN

/-- Uniform small-scale velocity coefficient derived from the Gagliardo interpolation bound. -/
noncomputable def uniformVelocitySmallConstant (M : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((8 : ℝ) ^ (2 : ℝ) *
    (2 * gagliardoConstant * (M * (8 : ℝ) ^ (2 / 5 : ℝ))) ^ 3)

/-- Uniform small-scale gradient coefficient derived from the energy decay bound. -/
noncomputable def uniformGradientSmallConstant (M : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (M ^ 2 * (8 : ℝ) ^ (9 / 5 : ℝ))

/-- Uniform small-scale pressure coefficient derived from pressure decay. -/
noncomputable def uniformPressureSmallConstant (M : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (M ^ (3 / 2 : ℝ) * (8 : ℝ) ^ (13 / 5 : ℝ))

/-- Velocity integral bound on the reference cylinder of radius `r₂ / 2`. -/
noncomputable def uniformVelocityReferenceIntegral (M r₂ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((r₂ / 2) ^ (2 : ℝ) *
    (2 * gagliardoConstant * (M * (r₂ / 2) ^ (2 / 5 : ℝ))) ^ 3)

/-- Gradient integral bound on the reference cylinder of radius `r₂ / 2`. -/
noncomputable def uniformGradientReferenceIntegral (M r₂ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (M ^ 2 * (r₂ / 2) ^ (9 / 5 : ℝ))

/-- Pressure integral bound on the reference cylinder of radius `r₂ / 2`. -/
noncomputable def uniformPressureReferenceIntegral (M r₂ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (M ^ (3 / 2 : ℝ) * (r₂ / 2) ^ (13 / 5 : ℝ))

/-- Velocity Morrey coefficient combining the small-scale estimate and reference-cylinder bound.
-/
noncomputable def uniformVelocityLargeConstant (M r₂ : ℝ) : ℝ≥0∞ :=
  max ((uniformVelocitySmallConstant M) ^ (1 / 3 : ℝ))
    ((ENNReal.ofReal (r₂ / 128)) ^ (-(5 * (1 / 3 - 1 / (25 / 3 : ℝ)))) *
      (uniformVelocityReferenceIntegral M r₂) ^ (1 / 3 : ℝ))

/-- Gradient Morrey coefficient combining the small-scale estimate and reference-cylinder bound.
-/
noncomputable def uniformGradientLargeConstant (M r₂ : ℝ) : ℝ≥0∞ :=
  max ((uniformGradientSmallConstant M) ^ (1 / 2 : ℝ))
    ((ENNReal.ofReal (r₂ / 128)) ^ (-(5 * (1 / 2 - 1 / (25 / 8 : ℝ)))) *
      (uniformGradientReferenceIntegral M r₂) ^ (1 / 2 : ℝ))

/-- Pressure Morrey coefficient combining the small-scale estimate and reference-cylinder bound.
-/
noncomputable def uniformPressureLargeConstant (M r₂ : ℝ) : ℝ≥0∞ :=
  max ((uniformPressureSmallConstant M) ^ (2 / 3 : ℝ))
    ((ENNReal.ofReal (r₂ / 128)) ^ (-(5 * (1 / (3 / 2) - 1 / (25 / 8 : ℝ)))) *
      (uniformPressureReferenceIntegral M r₂) ^ (2 / 3 : ℝ))

private theorem uniform_cell_bound_ennreal {p q a : ℝ} {K : ℝ≥0∞}
    {g : ParabolicPoint → ℝ} {z : ParabolicPoint} {r : ℝ}
    (hp : 0 < p) (hr : 0 < r) (ha0 : 0 ≤ a)
    (ha : a = 5 * (1 - p / q))
    (hI : ballPowerIntegral p g z r ≤ K * ENNReal.ofReal (r ^ a)) :
    morreyBallCell p q g z r ≤ K ^ (1 / p : ℝ) := by
  unfold morreyBallCell
  have hroot := ENNReal.rpow_le_rpow hI (by positivity : 0 ≤ (1 / p : ℝ))
  have hpdiv : 0 ≤ (1 / p : ℝ) := one_div_nonneg.mpr hp.le
  have hroot' : (ballPowerIntegral p g z r) ^ (1 / p : ℝ) ≤
      K ^ (1 / p : ℝ) * (ENNReal.ofReal r) ^ (a / p : ℝ) := by
    calc
      _ ≤ (K * ENNReal.ofReal (r ^ a)) ^ (1 / p : ℝ) := hroot
      _ = K ^ (1 / p : ℝ) * (ENNReal.ofReal r) ^ (a / p : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hpdiv,
          ← ENNReal.ofReal_rpow_of_nonneg hr.le ha0, ← ENNReal.rpow_mul]
        congr 1
        ring_nf
  have hrpow : ENNReal.ofReal r ≠ 0 := ENNReal.ofReal_pos.mpr hr |>.ne'
  have hrpowtop : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcancel : (ENNReal.ofReal r) ^ (-(5 * (1 - p / q) / p)) *
      (ENNReal.ofReal r) ^ (a / p : ℝ) = 1 := by
    rw [← ENNReal.rpow_add _ _ hrpow hrpowtop, ha]
    norm_num
  calc
    _ ≤ (ENNReal.ofReal r) ^ (-(5 * (1 - p / q) / p)) *
        (K ^ (1 / p : ℝ) * (ENNReal.ofReal r) ^ (a / p : ℝ)) :=
      mul_le_mul_of_nonneg_left hroot' (by positivity)
    _ = K ^ (1 / p : ℝ) := by
      calc
        _ = K ^ (1 / p : ℝ) * ((ENNReal.ofReal r) ^
            (-(5 * (1 - p / q) / p)) * (ENNReal.ofReal r) ^ (a / p : ℝ)) := by
              ac_rfl
        _ = _ := by rw [hcancel, mul_one]

private theorem uniform_negative_scale {r₀ r d : ℝ} (hr₀ : 0 < r₀)
    (hrr : r₀ ≤ r) (hd : 0 ≤ d) :
    (ENNReal.ofReal r) ^ (-d) ≤ (ENNReal.ofReal r₀) ^ (-d) := by
  have hr : 0 < r := lt_of_lt_of_le hr₀ hrr
  have hnn : Real.toNNReal r₀ ≤ Real.toNNReal r := Real.toNNReal_monotone hrr
  have hpos : 0 < Real.toNNReal r₀ := Real.toNNReal_pos.mpr hr₀
  have hposr : 0 < Real.toNNReal r := Real.toNNReal_pos.mpr hr
  have hnnr := NNReal.rpow_le_rpow_of_nonpos hpos hnn (neg_nonpos.mpr hd)
  change ((Real.toNNReal r : ℝ≥0∞) ^ (-d) ≤
    (Real.toNNReal r₀ : ℝ≥0∞) ^ (-d))
  rw [← ENNReal.coe_rpow_of_ne_zero (x := Real.toNNReal r)
      (y := -d) hposr.ne',
    ← ENNReal.coe_rpow_of_ne_zero (x := Real.toNNReal r₀)
      (y := -d) hpos.ne']
  exact ENNReal.coe_le_coe.mpr hnnr

private theorem uniform_cell_bound_global {p q : ℝ} {r₀ r : ℝ} {I : ℝ≥0∞}
    {g : ParabolicPoint → ℝ} {z : ParabolicPoint} (hp : 0 < p) (hpq : p ≤ q)
    (hr₀ : 0 < r₀) (hrr : r₀ ≤ r)
    (hI : ballPowerIntegral p g z r ≤ I) :
    morreyBallCell p q g z r ≤
      (ENNReal.ofReal r₀) ^ (-(5 * (1 / p - 1 / q))) * I ^ (1 / p : ℝ) := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hd : 0 ≤ 5 * (1 / p - 1 / q) := by
    exact mul_nonneg (by norm_num)
      (sub_nonneg.mpr (one_div_le_one_div_of_le hp hpq))
  have hscale := uniform_negative_scale hr₀ hrr hd
  have hroot := ENNReal.rpow_le_rpow hI (one_div_nonneg.mpr hp.le)
  have hexp : -(5 * (1 - p / q) / p) = -(5 * (1 / p - 1 / q)) := by
    field_simp [hp.ne', hq.ne']
  unfold morreyBallCell
  rw [hexp]
  calc
    _ ≤ (ENNReal.ofReal r) ^ (-(5 * (1 / p - 1 / q))) *
        I ^ (1 / p : ℝ) :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hscale (by positivity)

private theorem uniform_morreyBallNorm_le_of_cell_bound
    {P τ : ℝ} {g : ParabolicPoint → ℝ} {K : ℝ≥0∞}
    (hcell : ∀ z : ParabolicPoint, ∀ r : ℝ, 0 < r →
      morreyBallCell P τ g z r ≤ K) :
    morreyBallNorm P τ g ≤ K := by
  unfold morreyBallNorm
  refine iSup_le fun z => iSup_le fun r => hcell z r.1 r.2

private theorem uniform_ballPowerIntegral_zero {p : ℝ} {Q : Set ParabolicPoint}
    {g : ParabolicPoint → ℝ} {z : ParabolicPoint} {r : ℝ} (hp : 0 < p)
    (hdis : Metric.ball z r ∩ Q = ∅) : ballPowerIntegral p (Q.indicator g) z r = 0 := by
  unfold ballPowerIntegral
  apply le_antisymm
  · have heq : (∫⁻ y in Metric.ball z r,
        ENNReal.ofReal |Q.indicator g y| ^ p) = ∫⁻ y in Metric.ball z r, (0 : ℝ≥0∞) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_ball)] with y hy
      have hyQ : y ∉ Q := by
        intro hyQ
        have hmem : y ∈ Metric.ball z r ∩ Q := ⟨hy, hyQ⟩
        rw [hdis] at hmem
        exact hmem
      simp [Set.indicator_of_notMem hyQ, ENNReal.zero_rpow_of_pos hp]
    exact heq.le.trans_eq (by simp)
  · exact bot_le

private theorem uniform_ballPowerIntegral_le_of_subset {p : ℝ} {Q C : Set ParabolicPoint}
    {g : ParabolicPoint → ℝ} {F : ParabolicPoint → ℝ≥0∞} {z : ParabolicPoint} {r : ℝ}
    (hp : 0 < p) (hQ : MeasurableSet Q) (hQC : Q ⊆ C)
    (hpoint : ∀ y, ENNReal.ofReal |g y| ^ p ≤ F y) :
    ballPowerIntegral p (Q.indicator g) z r ≤ ∫⁻ y in C, F y := by
  unfold ballPowerIntegral
  have hind : (fun y => ENNReal.ofReal |Q.indicator g y| ^ p) =
      Q.indicator (fun y => ENNReal.ofReal |g y| ^ p) := by
    funext y
    by_cases hy : y ∈ Q <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem,
      hy, ENNReal.zero_rpow_of_pos hp]
  rw [hind, setLIntegral_indicator hQ]
  calc
    _ ≤ ∫⁻ y in Q ∩ Metric.ball z r, F y := lintegral_mono (fun y => hpoint y)
    _ ≤ _ := lintegral_mono_set (inter_subset_left.trans hQC)

private theorem uniform_component_abs_le_vec3norm (v : Vec3) (i : Fin 3) :
    |v i| ≤ vec3EuclideanNorm v := by
  unfold vec3EuclideanNorm
  exact Real.abs_le_sqrt (Finset.single_le_sum
    (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i))

private theorem uniform_local_setup {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    {z₀ : ParabolicPoint} {r₂ M ρ : ℝ} (_ : 0 < r₂) (hρ : 0 < ρ)
    (hρsmall : 128 * ρ ≤ r₂)
    (hcarrier : Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I)
    (hdecay : ∀ z : ParabolicPoint, z ∈ Metric.ball z₀ r₂ → ∀ r, 0 < r → r < r₂ →
      max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤ M * r ^ (2 / 5 : ℝ))
    {Q₂ : Set ParabolicPoint} (hQ₂ : Q₂ = Metric.ball z₀ (r₂ / 4))
    {z : ParabolicPoint} (hz : Metric.ball z ρ ∩ Q₂ ≠ ∅) :
    ∃ z' : ParabolicPoint, z' ∈ Metric.ball z₀ r₂ ∧
      Metric.ball z ρ ⊆ parabolicCylinder z'.1 z'.2 (4 * ρ) ∧
      closure (parabolicCylinder z'.1 z'.2 (16 * ρ)) ⊆ spaceTimeSet Ω I ∧
      max (max (alpha u z' (8 * ρ)) (beta u Du z' (8 * ρ)))
        (delta p z' (8 * ρ) ^ 2) ≤ M * (8 * ρ) ^ (2 / 5 : ℝ) := by
  subst Q₂
  obtain ⟨w, hwz, hw0⟩ := Set.nonempty_iff_ne_empty.mpr hz
  have hw0' : dist w z₀ < r₂ / 4 := hw0
  let z' : ParabolicPoint := (w.1, w.2 + (2 * ρ) ^ 2)
  have hshift : dist z' w ≤ 2 * ρ := by
    dsimp [z']
    rw [show @dist ParabolicPoint
      (@PseudoMetricSpace.toDist ParabolicPoint parabolicMetricSpace.toPseudoMetricSpace)
      ((w.1, w.2 + (2 * ρ) ^ 2) : ParabolicPoint) w = 2 * ρ from
        step2_shifted_center_dist (w := w) (r := 2 * ρ) (by positivity)]
  have hz'0 : dist z' z₀ < r₂ := by
    have htri := dist_triangle z' w z₀
    nlinarith only [htri, hshift, hw0', hρ, hρsmall]
  have hclosure : closure (parabolicCylinder z'.1 z'.2 (128 * ρ)) ⊆
      Metric.ball z₀ (2 * r₂) := by
    intro y hy
    have hyc := step2_closure_cylinder_subset_closedBall (x := z'.1) (t := z'.2)
      (r := 128 * ρ) (by positivity) hy
    have htri := dist_triangle y z' z₀
    rw [Metric.mem_ball]
    nlinarith only [htri, Metric.mem_closedBall.mp hyc, hz'0, hρsmall]
  have hsub16 : closure (parabolicCylinder z'.1 z'.2 (16 * ρ)) ⊆
      spaceTimeSet Ω I :=
    (closure_mono (parabolicCylinder_mono (by positivity) (by nlinarith only [hρ]))).trans
      (hclosure.trans hcarrier)
  have hdec := hdecay z' hz'0 (8 * ρ) (by positivity)
    (by nlinarith only [hρ, hρsmall])
  refine ⟨z', hz'0, ?_, hsub16, hdec⟩
  dsimp [z']
  exact step2_shifted_ball_cylinder hρ hwz

private theorem uniform_velocity_small_cell {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3} {i : Fin 3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z₀ : ParabolicPoint} {r₂ M ρ : ℝ} (hr₂ : 0 < r₂) (hM : 1 ≤ M)
    (hρ : 0 < ρ) (hρsmall : 128 * ρ ≤ r₂)
    (hcarrier : Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I)
    (hdecay : ∀ z : ParabolicPoint, z ∈ Metric.ball z₀ r₂ → ∀ r, 0 < r → r < r₂ →
      max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤ M * r ^ (2 / 5 : ℝ))
    {Q₂ : Set ParabolicPoint} (hQ₂ : Q₂ = Metric.ball z₀ (r₂ / 4))
    {z : ParabolicPoint} (hz : Metric.ball z ρ ∩ Q₂ ≠ ∅) :
    ballPowerIntegral 3 (Q₂.indicator (fun w => u w i)) z ρ ≤
      uniformVelocitySmallConstant M * ENNReal.ofReal (ρ ^ (16 / 5 : ℝ)) := by
  obtain ⟨z', -, hball, hsub16, hdec⟩ :=
    uniform_local_setup hr₂ hρ hρsmall hcarrier hdecay hQ₂ hz
  have hfixed := step2_fixed_scale_integrals hsol (R := 8 * ρ) (by positivity)
    hM (by convert hsub16 using 1; ring_nf) hdec
  have hballint : ballPowerIntegral 3 (Q₂.indicator (fun w => u w i)) z ρ ≤
      ∫⁻ y in parabolicCylinder z'.1 z'.2 (8 * ρ),
        ENNReal.ofReal (vec3EuclideanNorm (u y)) ^ (3 : ℝ) := by
    unfold ballPowerIntegral
    calc
      _ ≤ ∫⁻ y in Metric.ball z ρ,
          ENNReal.ofReal (vec3EuclideanNorm (u y)) ^ (3 : ℝ) := by
        apply lintegral_mono
        intro y
        by_cases hy : y ∈ Q₂
        · simp only [Set.indicator_of_mem hy]
          exact ENNReal.rpow_le_rpow
            (ENNReal.ofReal_le_ofReal (uniform_component_abs_le_vec3norm (u y) i))
            (by norm_num)
        · simp [Set.indicator_of_notMem hy]
      _ ≤ _ := lintegral_mono_set (hball.trans
        (parabolicCylinder_mono (by positivity) (by nlinarith only [hρ])))
  calc
    _ ≤ ∫⁻ y in parabolicCylinder z'.1 z'.2 (8 * ρ),
        ENNReal.ofReal (vec3EuclideanNorm (u y)) ^ (3 : ℝ) := hballint
    _ ≤ ENNReal.ofReal ((8 * ρ) ^ (2 : ℝ) *
        (2 * gagliardoConstant * (M * (8 * ρ) ^ (2 / 5 : ℝ))) ^ 3) := hfixed.1
    _ = uniformVelocitySmallConstant M * ENNReal.ofReal (ρ ^ (16 / 5 : ℝ)) := by
      have hscale : (8 * ρ) ^ (2 : ℝ) *
          (2 * gagliardoConstant * (M * (8 * ρ) ^ (2 / 5 : ℝ))) ^ 3 =
          ((8 : ℝ) ^ (2 : ℝ) *
            (2 * gagliardoConstant * (M * (8 : ℝ) ^ (2 / 5 : ℝ))) ^ 3) *
            ρ ^ (16 / 5 : ℝ) := by
        have hpow : (8 * ρ) ^ (2 / 5 : ℝ) =
            (8 : ℝ) ^ (2 / 5 : ℝ) * ρ ^ (2 / 5 : ℝ) :=
          Real.mul_rpow (by norm_num) hρ.le
        rw [show (8 * ρ) ^ (2 : ℝ) = (8 : ℝ) ^ (2 : ℝ) * ρ ^ (2 : ℝ) by
          rw [Real.mul_rpow (by norm_num) hρ.le], hpow]
        have hinner : 2 * gagliardoConstant *
            (M * (8 ^ (2 / 5 : ℝ) * ρ ^ (2 / 5 : ℝ))) =
            (2 * gagliardoConstant * (M * 8 ^ (2 / 5 : ℝ))) *
              ρ ^ (2 / 5 : ℝ) := by ring
        rw [hinner, mul_pow]
        have hρpow : (ρ ^ (2 / 5 : ℝ)) ^ (3 : ℕ) =
            ρ ^ (6 / 5 : ℝ) := by
          rw [show (ρ ^ (2 / 5 : ℝ)) ^ (3 : ℕ) =
              (ρ ^ (2 / 5 : ℝ)) ^ (3 : ℝ) by norm_num,
            ← Real.rpow_mul hρ.le]
          norm_num
        rw [hρpow]
        calc
          _ = ((8 : ℝ) ^ (2 : ℝ) *
              (2 * gagliardoConstant * (M * 8 ^ (2 / 5 : ℝ))) ^ 3) *
              (ρ ^ (2 : ℝ) * ρ ^ (6 / 5 : ℝ)) := by ring
          _ = _ := by
            rw [← Real.rpow_add hρ]
            norm_num
      have hG : 0 ≤ gagliardoConstant := by
        unfold gagliardoConstant
        positivity
      have hM0 : 0 ≤ M := by linarith only [hM]
      have hnonneg : 0 ≤ (8 : ℝ) ^ (2 : ℝ) *
          (2 * gagliardoConstant * (M * 8 ^ (2 / 5 : ℝ))) ^ 3 := by positivity
      rw [hscale, uniformVelocitySmallConstant, ENNReal.ofReal_mul hnonneg]

private theorem uniform_gradient_small_cell {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3} {i j : Fin 3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z₀ : ParabolicPoint} {r₂ M ρ : ℝ} (hr₂ : 0 < r₂) (hM : 1 ≤ M)
    (hρ : 0 < ρ) (hρsmall : 128 * ρ ≤ r₂)
    (hcarrier : Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I)
    (hdecay : ∀ z : ParabolicPoint, z ∈ Metric.ball z₀ r₂ → ∀ r, 0 < r → r < r₂ →
      max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤ M * r ^ (2 / 5 : ℝ))
    {Q₂ : Set ParabolicPoint} (hQ₂ : Q₂ = Metric.ball z₀ (r₂ / 4))
    {z : ParabolicPoint} (hz : Metric.ball z ρ ∩ Q₂ ≠ ∅) :
    ballPowerIntegral 2 (Q₂.indicator (fun w => Du w i j)) z ρ ≤
      uniformGradientSmallConstant M * ENNReal.ofReal (ρ ^ (9 / 5 : ℝ)) := by
  obtain ⟨z', -, hball, hsub16, hdec⟩ :=
    uniform_local_setup hr₂ hρ hρsmall hcarrier hdecay hQ₂ hz
  have hfixed := step2_fixed_scale_integrals hsol (R := 8 * ρ) (by positivity)
    hM (by convert hsub16 using 1; ring_nf) hdec
  have hballint : ballPowerIntegral 2 (Q₂.indicator (fun w => Du w i j)) z ρ ≤
      ∫⁻ y in parabolicCylinder z'.1 z'.2 (8 * ρ),
        ENNReal.ofReal (spatialGradientSq u Du y) := by
    unfold ballPowerIntegral
    calc
      _ ≤ ∫⁻ y in Metric.ball z ρ,
          ENNReal.ofReal (spatialGradientSq u Du y) := by
        apply lintegral_mono
        intro y
        by_cases hy : y ∈ Q₂
        · simp only [Set.indicator_of_mem hy]
          rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
          apply ENNReal.ofReal_le_ofReal
          unfold spatialGradientSq
          have hterm : (Du y i j) ^ 2 ≤ ∑ k : Fin 3, ∑ l : Fin 3, (Du y k l) ^ 2 := by
            exact (Finset.single_le_sum (fun l _ => sq_nonneg (Du y i l))
              (Finset.mem_univ j)).trans
              (Finset.single_le_sum (fun k _ => Finset.sum_nonneg
                (fun l _ => sq_nonneg (Du y k l))) (Finset.mem_univ i))
          simpa [sq_abs] using hterm
        · simp [Set.indicator_of_notMem hy]
      _ ≤ _ := lintegral_mono_set (hball.trans
        (parabolicCylinder_mono (by positivity) (by nlinarith only [hρ])))
  calc
    _ ≤ ∫⁻ y in parabolicCylinder z'.1 z'.2 (8 * ρ),
        ENNReal.ofReal (spatialGradientSq u Du y) := hballint
    _ ≤ ENNReal.ofReal (M ^ 2 * (8 * ρ) ^ (9 / 5 : ℝ)) := hfixed.2.1
    _ = uniformGradientSmallConstant M * ENNReal.ofReal (ρ ^ (9 / 5 : ℝ)) := by
      have hscale : M ^ 2 * (8 * ρ) ^ (9 / 5 : ℝ) =
          (M ^ 2 * (8 : ℝ) ^ (9 / 5 : ℝ)) * ρ ^ (9 / 5 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) hρ.le]
        ring
      have hnonneg : 0 ≤ M ^ 2 * (8 : ℝ) ^ (9 / 5 : ℝ) := by positivity
      rw [hscale, uniformGradientSmallConstant, ENNReal.ofReal_mul hnonneg]

private theorem uniform_pressure_small_cell {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z₀ : ParabolicPoint} {r₂ M ρ : ℝ} (hr₂ : 0 < r₂) (hM : 1 ≤ M)
    (hρ : 0 < ρ) (hρsmall : 128 * ρ ≤ r₂)
    (hcarrier : Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I)
    (hdecay : ∀ z : ParabolicPoint, z ∈ Metric.ball z₀ r₂ → ∀ r, 0 < r → r < r₂ →
      max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤ M * r ^ (2 / 5 : ℝ))
    {Q₂ : Set ParabolicPoint} (hQ₂ : Q₂ = Metric.ball z₀ (r₂ / 4))
    {z : ParabolicPoint} (hz : Metric.ball z ρ ∩ Q₂ ≠ ∅) :
    ballPowerIntegral (3 / 2 : ℝ) (Q₂.indicator p) z ρ ≤
      uniformPressureSmallConstant M * ENNReal.ofReal (ρ ^ (13 / 5 : ℝ)) := by
  obtain ⟨z', -, hball, hsub16, hdec⟩ :=
    uniform_local_setup hr₂ hρ hρsmall hcarrier hdecay hQ₂ hz
  have hfixed := step2_fixed_scale_integrals hsol (R := 8 * ρ) (by positivity)
    hM (by convert hsub16 using 1; ring_nf) hdec
  have hballint : ballPowerIntegral (3 / 2 : ℝ) (Q₂.indicator p) z ρ ≤
      ∫⁻ y in parabolicCylinder z'.1 z'.2 (8 * ρ),
        ENNReal.ofReal |p y| ^ (3 / 2 : ℝ) := by
    unfold ballPowerIntegral
    calc
      _ ≤ ∫⁻ y in Metric.ball z ρ,
          ENNReal.ofReal |p y| ^ (3 / 2 : ℝ) := by
        apply lintegral_mono
        intro y
        by_cases hy : y ∈ Q₂ <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]
      _ ≤ _ := lintegral_mono_set (hball.trans
        (parabolicCylinder_mono (by positivity) (by nlinarith only [hρ])))
  calc
    _ ≤ ∫⁻ y in parabolicCylinder z'.1 z'.2 (8 * ρ),
        ENNReal.ofReal |p y| ^ (3 / 2 : ℝ) := hballint
    _ ≤ ENNReal.ofReal (M ^ (3 / 2 : ℝ) * (8 * ρ) ^ (13 / 5 : ℝ)) := hfixed.2.2
    _ = uniformPressureSmallConstant M * ENNReal.ofReal (ρ ^ (13 / 5 : ℝ)) := by
      have hscale : M ^ (3 / 2 : ℝ) * (8 * ρ) ^ (13 / 5 : ℝ) =
          (M ^ (3 / 2 : ℝ) * (8 : ℝ) ^ (13 / 5 : ℝ)) *
            ρ ^ (13 / 5 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) hρ.le]
        ring
      have hnonneg : 0 ≤ M ^ (3 / 2 : ℝ) * (8 : ℝ) ^ (13 / 5 : ℝ) := by positivity
      rw [hscale, uniformPressureSmallConstant, ENNReal.ofReal_mul hnonneg]

private lemma step2_morrey_form_uniform_hcellU_1 :
    ∀ (M r₂ : ℝ),
      (1 : ℝ) ≤ M →
        (0 : ℝ) < r₂ →
          ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
            {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
            {f : ParabolicPoint → Vec3},
            IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
              ∀ (z₀ : ParabolicPoint),
                Metric.ball z₀ ((2 : ℝ) * r₂) ⊆ spaceTimeSet Ω I →
                  (∀ z ∈ Metric.ball z₀ r₂,
                      ∀ (r : ℝ),
                        (0 : ℝ) < r →
                          r < r₂ →
                            max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ (2 : ℕ)) ≤
                              M * r ^ (2 / 5 : ℝ)) →
                    let Q₂ : Set ParabolicPoint := Metric.ball z₀ (r₂ / (4 : ℝ));
                    let zG : ParabolicPoint := (z₀.1, z₀.2 + (r₂ / (4 : ℝ)) ^ (2 : ℕ));
                    ∫⁻ (w : ParabolicPoint) in parabolicCylinder zG.1 zG.2 (r₂ / (2 : ℝ)),
                          ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) ≤
                        uniformVelocityReferenceIntegral M r₂ →
                      ∀ (i : Fin (3 : ℕ)) (z : ParabolicPoint) (r : ℝ),
                        (0 : ℝ) < r →
                          morreyBallCell (3 : ℝ) (25 / 3 : ℝ)
                              (Q₂.indicator fun (w : ParabolicPoint) => u w i) z r ≤
                            uniformVelocityLargeConstant M r₂
    := by
  intro M r₂ hM hr₂ Ω I q u Du p f hsol z₀ hcarrier hdecay Q₂ zG hIU i z r hr
  by_cases hdis : Metric.ball z r ∩ Q₂ = ∅
  · unfold morreyBallCell
    rw [uniform_ballPowerIntegral_zero (by norm_num) hdis]
    simp
  by_cases hs : 128 * r ≤ r₂
  · exact (uniform_cell_bound_ennreal (p := 3) (q := 25 / 3) (a := 16 / 5)
      (K := uniformVelocitySmallConstant M) (g := Q₂.indicator (fun w => u w i))
      (z := z) (r := r) (by norm_num) hr (by norm_num) (by norm_num)
      (uniform_velocity_small_cell hsol hr₂ hM hr hs hcarrier hdecay rfl hdis)).trans
      (by dsimp [uniformVelocityLargeConstant]; exact le_max_left _ _)
  · have hrr : r₂ / 128 ≤ r := by nlinarith only [hr₂, hr, hs]
    have hballU : ballPowerIntegral 3 (Q₂.indicator (fun w => u w i)) z r ≤
        ∫⁻ y in parabolicCylinder zG.1 zG.2 (r₂ / 2),
          ENNReal.ofReal (vec3EuclideanNorm (u y)) ^ (3 : ℝ) := by
      apply uniform_ballPowerIntegral_le_of_subset (p := 3) (Q := Q₂)
        (C := parabolicCylinder zG.1 zG.2 (r₂ / 2))
        (g := fun w => u w i)
        (F := fun w => ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ))
        (z := z) (r := r) (by norm_num) measurableSet_ball
      · intro y hy
        change y ∈ Metric.ball z₀ (r₂ / 4) at hy
        have h := metricBall_subset_parabolicCylinder_doubled z₀
          (r := r₂ / 4) (by positivity) hy
        dsimp [zG]
        convert h using 1
        ring_nf
      · intro y
        exact ENNReal.rpow_le_rpow
          (ENNReal.ofReal_le_ofReal (uniform_component_abs_le_vec3norm (u y) i))
          (by norm_num)
    have hIu : ballPowerIntegral 3 (Q₂.indicator (fun w => u w i)) z r ≤
        uniformVelocityReferenceIntegral M r₂ := hballU.trans hIU
    exact (uniform_cell_bound_global (p := 3) (q := 25 / 3) (r₀ := r₂ / 128)
      (I := uniformVelocityReferenceIntegral M r₂)
      (g := Q₂.indicator (fun w => u w i)) (z := z) (r := r)
      (by norm_num) (by norm_num) (by positivity) hrr hIu).trans (by
        dsimp [uniformVelocityLargeConstant]; exact le_max_right _ _)

private lemma step2_morrey_form_uniform_hcellDu_2 :
    ∀ (M r₂ : ℝ),
      (1 : ℝ) ≤ M →
        (0 : ℝ) < r₂ →
          ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
            {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
            {f : ParabolicPoint → Vec3},
            IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
              ∀ (z₀ : ParabolicPoint),
                Metric.ball z₀ ((2 : ℝ) * r₂) ⊆ spaceTimeSet Ω I →
                  (∀ z ∈ Metric.ball z₀ r₂,
                      ∀ (r : ℝ),
                        (0 : ℝ) < r →
                          r < r₂ →
                            max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ (2 : ℕ)) ≤
                              M * r ^ (2 / 5 : ℝ)) →
                    let Q₂ : Set ParabolicPoint := Metric.ball z₀ (r₂ / (4 : ℝ));
                    let zG : ParabolicPoint := (z₀.1, z₀.2 + (r₂ / (4 : ℝ)) ^ (2 : ℕ));
                    ∫⁻ (w : ParabolicPoint) in parabolicCylinder zG.1 zG.2 (r₂ / (2 : ℝ)),
                          ENNReal.ofReal (spatialGradientSq u Du w) ≤
                        uniformGradientReferenceIntegral M r₂ →
                      ∀ (i j : Fin (3 : ℕ)) (z : ParabolicPoint) (r : ℝ),
                        (0 : ℝ) < r →
                          morreyBallCell (2 : ℝ) (25 / 8 : ℝ)
                              (Q₂.indicator fun (w : ParabolicPoint) => Du w i j) z r ≤
                            uniformGradientLargeConstant M r₂
    := by
  intro M r₂ hM hr₂ Ω I q u Du p f hsol z₀ hcarrier hdecay Q₂ zG hID i j z r hr
  by_cases hdis : Metric.ball z r ∩ Q₂ = ∅
  · unfold morreyBallCell
    rw [uniform_ballPowerIntegral_zero (by norm_num) hdis]
    simp
  by_cases hs : 128 * r ≤ r₂
  · exact (uniform_cell_bound_ennreal (p := 2) (q := 25 / 8) (a := 9 / 5)
      (K := uniformGradientSmallConstant M)
      (g := Q₂.indicator (fun w => Du w i j)) (z := z) (r := r)
      (by norm_num) hr (by norm_num) (by norm_num)
      (uniform_gradient_small_cell hsol hr₂ hM hr hs hcarrier hdecay rfl hdis)).trans
      (by dsimp [uniformGradientLargeConstant]; exact le_max_left _ _)
  · have hrr : r₂ / 128 ≤ r := by nlinarith only [hr₂, hr, hs]
    have hballDu : ballPowerIntegral 2 (Q₂.indicator (fun w => Du w i j)) z r ≤
        ∫⁻ y in parabolicCylinder zG.1 zG.2 (r₂ / 2),
          ENNReal.ofReal (spatialGradientSq u Du y) := by
      apply uniform_ballPowerIntegral_le_of_subset (p := 2) (Q := Q₂)
        (C := parabolicCylinder zG.1 zG.2 (r₂ / 2))
        (g := fun w => Du w i j)
        (F := fun w => ENNReal.ofReal (spatialGradientSq u Du w))
        (z := z) (r := r) (by norm_num) measurableSet_ball
      · intro y hy
        change y ∈ Metric.ball z₀ (r₂ / 4) at hy
        have h := metricBall_subset_parabolicCylinder_doubled z₀
          (r := r₂ / 4) (by positivity) hy
        dsimp [zG]
        convert h using 1
        ring_nf
      · intro y
        rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
        apply ENNReal.ofReal_le_ofReal
        unfold spatialGradientSq
        have hterm : (Du y i j) ^ 2 ≤
            ∑ k : Fin 3, ∑ l : Fin 3, (Du y k l) ^ 2 := by
          exact (Finset.single_le_sum (fun l _ => sq_nonneg (Du y i l))
            (Finset.mem_univ j)).trans
            (Finset.single_le_sum (fun k _ => Finset.sum_nonneg
              (fun l _ => sq_nonneg (Du y k l))) (Finset.mem_univ i))
        simpa [sq_abs] using hterm
    have hIDu : ballPowerIntegral 2 (Q₂.indicator (fun w => Du w i j)) z r ≤
        uniformGradientReferenceIntegral M r₂ := hballDu.trans hID
    exact (uniform_cell_bound_global (p := 2) (q := 25 / 8) (r₀ := r₂ / 128)
      (I := uniformGradientReferenceIntegral M r₂)
      (g := Q₂.indicator (fun w => Du w i j)) (z := z) (r := r)
      (by norm_num) (by norm_num) (by positivity) hrr hIDu).trans (by
        dsimp [uniformGradientLargeConstant]; exact le_max_right _ _)

/-- Step 2 with constants chosen before the solution data.  The constants are
functions only of the decay constant and the reference radius. -/
theorem step2_morrey_form_uniform
    (M r₂ : ℝ) (hM : 1 ≤ M) (hr₂ : 0 < r₂) :
    ∃ Kᵤ K_Du Kₚ : ℝ≥0∞, Kᵤ < ⊤ ∧ K_Du < ⊤ ∧ Kₚ < ⊤ ∧
      ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
        {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ z₀ : ParabolicPoint,
        Metric.ball z₀ (2 * r₂) ⊆ spaceTimeSet Ω I →
        (∀ z ∈ Metric.ball z₀ r₂, ∀ r : ℝ, 0 < r → r < r₂ →
          max (max (alpha u z r) (beta u Du z r)) (delta p z r ^ 2) ≤
            M * r ^ (2 / 5 : ℝ)) →
        (∀ i : Fin 3, morreyBallNorm 3 (25 / 3 : ℝ)
          ((Metric.ball z₀ (r₂ / 4)).indicator (fun z => u z i)) ≤ Kᵤ) ∧
        (∀ i j : Fin 3, morreyBallNorm 2 (25 / 8 : ℝ)
          ((Metric.ball z₀ (r₂ / 4)).indicator (fun z => Du z i j)) ≤ K_Du) ∧
        morreyBallNorm (3 / 2 : ℝ) (25 / 8 : ℝ)
          ((Metric.ball z₀ (r₂ / 4)).indicator p) ≤ Kₚ := by
  have hsmallV : uniformVelocitySmallConstant M < ⊤ := by
    unfold uniformVelocitySmallConstant
    exact ENNReal.ofReal_lt_top
  have hsmallD : uniformGradientSmallConstant M < ⊤ := by
    unfold uniformGradientSmallConstant
    exact ENNReal.ofReal_lt_top
  have hsmallP : uniformPressureSmallConstant M < ⊤ := by
    unfold uniformPressureSmallConstant
    exact ENNReal.ofReal_lt_top
  have hr₀ : 0 < r₂ / 128 := by positivity
  have hbase : 0 < ENNReal.ofReal (r₂ / 128) := ENNReal.ofReal_pos.mpr hr₀
  have hbasepowV : (ENNReal.ofReal (r₂ / 128)) ^
      (-(5 * (1 / 3 - 1 / (25 / 3 : ℝ)))) < ⊤ := by
    exact lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero
      hbase.ne' ENNReal.ofReal_ne_top)
  have hbasepowD : (ENNReal.ofReal (r₂ / 128)) ^
      (-(5 * (1 / 2 - 1 / (25 / 8 : ℝ)))) < ⊤ := by
    exact lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero
      hbase.ne' ENNReal.ofReal_ne_top)
  have hbasepowP : (ENNReal.ofReal (r₂ / 128)) ^
      (-(5 * (1 / (3 / 2) - 1 / (25 / 8 : ℝ)))) < ⊤ := by
    exact lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero
      hbase.ne' ENNReal.ofReal_ne_top)
  have hrefV : uniformVelocityReferenceIntegral M r₂ < ⊤ := by
    unfold uniformVelocityReferenceIntegral
    exact ENNReal.ofReal_lt_top
  have hrefD : uniformGradientReferenceIntegral M r₂ < ⊤ := by
    unfold uniformGradientReferenceIntegral
    exact ENNReal.ofReal_lt_top
  have hrefP : uniformPressureReferenceIntegral M r₂ < ⊤ := by
    unfold uniformPressureReferenceIntegral
    exact ENNReal.ofReal_lt_top
  have hlargeV : uniformVelocityLargeConstant M r₂ < ⊤ := by
    unfold uniformVelocityLargeConstant
    exact max_lt
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) hsmallV.ne)
      (ENNReal.mul_lt_top hbasepowV
        (ENNReal.rpow_lt_top_of_nonneg (by positivity) hrefV.ne))
  have hlargeD : uniformGradientLargeConstant M r₂ < ⊤ := by
    unfold uniformGradientLargeConstant
    exact max_lt
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) hsmallD.ne)
      (ENNReal.mul_lt_top hbasepowD
        (ENNReal.rpow_lt_top_of_nonneg (by positivity) hrefD.ne))
  have hlargeP : uniformPressureLargeConstant M r₂ < ⊤ := by
    unfold uniformPressureLargeConstant
    exact max_lt
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) hsmallP.ne)
      (ENNReal.mul_lt_top hbasepowP
        (ENNReal.rpow_lt_top_of_nonneg (by positivity) hrefP.ne))
  refine ⟨uniformVelocityLargeConstant M r₂, uniformGradientLargeConstant M r₂,
    uniformPressureLargeConstant M r₂, hlargeV, hlargeD, hlargeP, ?_⟩
  intro Ω I q u Du p f hsol z₀ hcarrier hdecay
  let Q₂ : Set ParabolicPoint := Metric.ball z₀ (r₂ / 4)
  let zG : ParabolicPoint := (z₀.1, z₀.2 + (r₂ / 4) ^ 2)
  have hzG : dist zG z₀ = r₂ / 4 := by
    dsimp [zG]
    exact step2_shifted_center_dist (w := z₀) (r := r₂ / 4) (by positivity)
  have hzGmem : zG ∈ Metric.ball z₀ r₂ := by
    rw [Metric.mem_ball]
    nlinarith only [hzG, hr₂]
  have hclose : closure (parabolicCylinder zG.1 zG.2 r₂) ⊆
      Metric.ball z₀ (2 * r₂) := by
    intro y hy
    have hyc := step2_closure_cylinder_subset_closedBall (x := zG.1) (t := zG.2)
      (r := r₂) (by positivity) hy
    have htri := dist_triangle y zG z₀
    rw [Metric.mem_ball]
    nlinarith only [htri, Metric.mem_closedBall.mp hyc, hzG, hr₂]
  have hsubhelper : closure (parabolicCylinder zG.1 zG.2 (2 * (r₂ / 2))) ⊆
      spaceTimeSet Ω I := by
    apply (closure_mono (parabolicCylinder_mono (x := zG.1) (t := zG.2)
      (r₁ := 2 * (r₂ / 2)) (r₂ := r₂) (by positivity) (by nlinarith only))).trans
    exact hclose.trans hcarrier
  have hdecR := hdecay zG hzGmem (r₂ / 2) (by positivity) (by nlinarith only [hr₂])
  have hfixed := step2_fixed_scale_integrals hsol (R := r₂ / 2) (by positivity)
    hM hsubhelper hdecR
  have hIU : (∫⁻ w in parabolicCylinder zG.1 zG.2 (r₂ / 2),
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≤
      uniformVelocityReferenceIntegral M r₂ := by
    simpa [uniformVelocityReferenceIntegral] using hfixed.1
  have hID : (∫⁻ w in parabolicCylinder zG.1 zG.2 (r₂ / 2),
      ENNReal.ofReal (spatialGradientSq u Du w)) ≤
      uniformGradientReferenceIntegral M r₂ := by
    simpa [uniformGradientReferenceIntegral] using hfixed.2.1
  have hIP : (∫⁻ w in parabolicCylinder zG.1 zG.2 (r₂ / 2),
      ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) ≤
      uniformPressureReferenceIntegral M r₂ := by
    simpa [uniformPressureReferenceIntegral] using hfixed.2.2
  have hcellU := @step2_morrey_form_uniform_hcellU_1 M r₂ hM hr₂ Ω I q u Du p f hsol z₀ hcarrier
    hdecay hIU
  have hcellDu := @step2_morrey_form_uniform_hcellDu_2 M r₂ hM hr₂ Ω I q u Du p f hsol z₀ hcarrier
    hdecay hID
  have hcellP : ∀ z : ParabolicPoint, ∀ r : ℝ, 0 < r →
      morreyBallCell (3 / 2 : ℝ) (25 / 8 : ℝ) (Q₂.indicator p) z r ≤
        uniformPressureLargeConstant M r₂ := by
    intro z r hr
    by_cases hdis : Metric.ball z r ∩ Q₂ = ∅
    · unfold morreyBallCell
      rw [uniform_ballPowerIntegral_zero (by norm_num) hdis]
      simp
    by_cases hs : 128 * r ≤ r₂
    · exact (uniform_cell_bound_ennreal (p := 3 / 2) (q := 25 / 8) (a := 13 / 5)
        (K := uniformPressureSmallConstant M) (g := Q₂.indicator p) (z := z) (r := r)
        (by norm_num) hr (by norm_num) (by norm_num)
        (uniform_pressure_small_cell hsol hr₂ hM hr hs hcarrier hdecay rfl hdis)).trans
        (by dsimp [uniformPressureLargeConstant]; norm_num)
    · have hrr : r₂ / 128 ≤ r := by nlinarith only [hr₂, hr, hs]
      have hballP : ballPowerIntegral (3 / 2 : ℝ) (Q₂.indicator p) z r ≤
          ∫⁻ y in parabolicCylinder zG.1 zG.2 (r₂ / 2),
            ENNReal.ofReal |p y| ^ (3 / 2 : ℝ) := by
        apply uniform_ballPowerIntegral_le_of_subset (p := 3 / 2) (Q := Q₂)
          (C := parabolicCylinder zG.1 zG.2 (r₂ / 2)) (g := p)
          (F := fun w => ENNReal.ofReal |p w| ^ (3 / 2 : ℝ))
          (z := z) (r := r) (by norm_num) measurableSet_ball
        · intro y hy
          change y ∈ Metric.ball z₀ (r₂ / 4) at hy
          have h := metricBall_subset_parabolicCylinder_doubled z₀
            (r := r₂ / 4) (by positivity) hy
          dsimp [zG]
          convert h using 1
          ring_nf
        · intro y
          rfl
      have hIPp : ballPowerIntegral (3 / 2 : ℝ) (Q₂.indicator p) z r ≤
          uniformPressureReferenceIntegral M r₂ := hballP.trans hIP
      exact (uniform_cell_bound_global (p := 3 / 2) (q := 25 / 8) (r₀ := r₂ / 128)
        (I := uniformPressureReferenceIntegral M r₂) (g := Q₂.indicator p)
        (z := z) (r := r) (by norm_num) (by norm_num) (by positivity) hrr hIPp).trans (by
          dsimp [uniformPressureLargeConstant]; norm_num)
  have hnormU : ∀ i : Fin 3, morreyBallNorm 3 (25 / 3 : ℝ)
      (Q₂.indicator (fun z => u z i)) ≤ uniformVelocityLargeConstant M r₂ := by
    intro i
    exact uniform_morreyBallNorm_le_of_cell_bound (hcellU i)
  have hnormDu : ∀ i j : Fin 3, morreyBallNorm 2 (25 / 8 : ℝ)
      (Q₂.indicator (fun z => Du z i j)) ≤ uniformGradientLargeConstant M r₂ := by
    intro i j
    exact uniform_morreyBallNorm_le_of_cell_bound (hcellDu i j)
  have hnormP : morreyBallNorm (3 / 2 : ℝ) (25 / 8 : ℝ)
      (Q₂.indicator p) ≤ uniformPressureLargeConstant M r₂ :=
    uniform_morreyBallNorm_le_of_cell_bound hcellP
  simpa [Q₂] using And.intro hnormU (And.intro hnormDu hnormP)

/-- Membership is the finite-constant corollary of the uniform norm export. -/
theorem step2_morrey_form_uniform_membership
    {Q₂ : Set ParabolicPoint} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {Kᵤ K_Du Kₚ : ℝ≥0∞}
    (hKᵤ : Kᵤ < ⊤) (hK_Du : K_Du < ⊤) (hKₚ : Kₚ < ⊤)
    (hᵤ : ∀ i : Fin 3, morreyBallNorm 3 (25 / 3 : ℝ)
      (Q₂.indicator (fun z => u z i)) ≤ Kᵤ)
    (hDu : ∀ i : Fin 3, ∀ j : Fin 3, morreyBallNorm 2 (25 / 8 : ℝ)
      (Q₂.indicator (fun z => Du z i j)) ≤ K_Du)
    (hp : morreyBallNorm (3 / 2 : ℝ) (25 / 8 : ℝ)
      (Q₂.indicator p) ≤ Kₚ) :
    morreyVecMem 3 (25 / 3 : ℝ) Q₂ u ∧
      (∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ) Q₂ (fun z => Du z i)) ∧
      morreyBallNorm (3 / 2 : ℝ) (25 / 8 : ℝ) (Q₂.indicator p) < ⊤ := by
  refine ⟨?_, ?_, lt_of_le_of_lt hp hKₚ⟩
  · intro i
    exact lt_of_le_of_lt (hᵤ i) hKᵤ
  · intro i j
    exact lt_of_le_of_lt (hDu i j) hK_Du

/-- Fixed-scale Step 2 bounds with the scale and constants before the
solution data.  These are the localized estimates used to make the large
Morrey scales depend only on the decay constant and the reference radius. -/
theorem step2_morrey_form_uniform_fixed_scale
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    {z : ParabolicPoint} {r₂ M : ℝ}
    (hr₂ : 0 < r₂) (hM : 1 ≤ M)
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hsub : closure (parabolicCylinder z.1 z.2 (2 * r₂)) ⊆ spaceTimeSet Ω I)
    (hdec : max (max (alpha u z r₂) (beta u Du z r₂))
      (delta p z r₂ ^ 2) ≤ M * r₂ ^ (2 / 5 : ℝ)) :
    (∫⁻ w in parabolicCylinder z.1 z.2 r₂,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≤
        ENNReal.ofReal (r₂ ^ (2 : ℝ) *
          (2 * gagliardoConstant * (M * r₂ ^ (2 / 5 : ℝ))) ^ 3) ∧
      (∫⁻ w in parabolicCylinder z.1 z.2 r₂,
        ENNReal.ofReal (spatialGradientSq u Du w)) ≤
        ENNReal.ofReal (M ^ 2 * r₂ ^ (9 / 5 : ℝ)) ∧
      (∫⁻ w in parabolicCylinder z.1 z.2 r₂,
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) ≤
        ENNReal.ofReal (M ^ (3 / 2 : ℝ) * r₂ ^ (13 / 5 : ℝ)) := by
  exact step2_fixed_scale_integrals hsol hr₂ hM hsub hdec

end CKN
