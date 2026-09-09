/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.LoopVariance
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import LeanPool.NavierStokesAndEuler.NavierStokes.ConeAlgebra
import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricRephase
import LeanPool.NavierStokesAndEuler.NavierStokes.UniformCone
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Construction of the true-cone loop

This file assembles the actual exponential moment inverse, a smooth speed
correction, compact uniform cone margins, and the smooth phase change.
-/

@[expose] public section


namespace NavierStokes.TrueConeLoop

noncomputable section

open Set Filter MeasureTheory
open SmoothLoop LoopMoments LoopVariance ConeAlgebra
open scoped ContDiff Topology Interval

/-- Low speed, given by `2 + δ / 8`. -/
def lowSpeed (δ : ℝ) : ℝ := 2 + δ / 8
/-- High speed, given by `2 + δ / 4`. -/
def highSpeed (δ : ℝ) : ℝ := 2 + δ / 4
/-- Target speed, given by `2 + δ / 2`. -/
def targetSpeed (δ : ℝ) : ℝ := 2 + δ / 2

/-- Speed cutoff, given by `1 - Real.smoothTransition ((v - lowSpeed δ) / (δ / 8))`. -/
def speedCutoff (δ v : ℝ) : ℝ :=
  1 - Real.smoothTransition ((v - lowSpeed δ) / (δ / 8))

theorem speedCutoff_contDiff (δ : ℝ) : ContDiff ℝ ∞ (speedCutoff δ) := by
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const (δ / 8)))

theorem speedCutoff_mem_Icc (δ v : ℝ) : speedCutoff δ v ∈ Icc (0 : ℝ) 1 := by
  have hlo := Real.smoothTransition.nonneg ((v - lowSpeed δ) / (δ / 8))
  have hhi := Real.smoothTransition.le_one ((v - lowSpeed δ) / (δ / 8))
  unfold speedCutoff
  constructor <;> linarith

theorem speedCutoff_one (δ v : ℝ) (hδ : 0 < δ) (hv : v ≤ lowSpeed δ) : speedCutoff δ v = 1 := by
  have harg : (v - lowSpeed δ) / (δ / 8) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hv) (by positivity)
  simp only [speedCutoff, Real.smoothTransition.zero_of_nonpos harg, sub_zero]

theorem speedCutoff_zero (δ v : ℝ) (hδ : 0 < δ) (hv : highSpeed δ ≤ v) : speedCutoff δ v = 0 := by
  have harg : 1 ≤ (v - lowSpeed δ) / (δ / 8) := by
    apply (le_div_iff₀ (by positivity : 0 < δ / 8)).mpr
    dsimp [lowSpeed, highSpeed] at *
    linarith
  simp only [speedCutoff, Real.smoothTransition.one_of_one_le harg, sub_self]

/-- Correction root, given by `speedCutoff δ v * Real.sqrt (targetSpeed δ - v)`. -/
def correctionRoot (δ v : ℝ) : ℝ := speedCutoff δ v * Real.sqrt (targetSpeed δ - v)
/-- Correction, given by `correctionRoot δ v ^ 2`. -/
def correction (δ v : ℝ) : ℝ := correctionRoot δ v ^ 2
/-- Corrected speed, given by `v + correction δ v`. -/
def correctedSpeed (δ v : ℝ) : ℝ := v + correction δ v

theorem correctionRoot_zero (δ v : ℝ) (hδ : 0 < δ) (hv : highSpeed δ ≤ v) :
    correctionRoot δ v = 0 := by
  simp only [correctionRoot, speedCutoff_zero δ v hδ hv, zero_mul]

theorem correctionRoot_contDiff (δ : ℝ) (hδ : 0 < δ) : ContDiff ℝ ∞ (correctionRoot δ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro v
  by_cases hv : v < targetSpeed δ
  · exact (speedCutoff_contDiff δ).contDiffAt.mul
      ((contDiffAt_const.sub contDiffAt_id).sqrt (ne_of_gt (sub_pos.mpr hv)))
  · have hhigh : highSpeed δ < v := by
      dsimp [highSpeed, targetSpeed] at *
      linarith
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) v).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hhigh] with w hw
    exact correctionRoot_zero δ w hδ hw.le

theorem correctionRoot_nonneg (δ v : ℝ) : 0 ≤ correctionRoot δ v :=
  mul_nonneg (speedCutoff_mem_Icc δ v).1 (Real.sqrt_nonneg _)

theorem correction_nonneg (δ v : ℝ) : 0 ≤ correction δ v := sq_nonneg _

theorem correction_formula (δ v : ℝ) (hδ : 0 < δ) :
    correction δ v = speedCutoff δ v ^ 2 * (targetSpeed δ - v) := by
  by_cases hv : highSpeed δ ≤ v
  · simp only [correction, correctionRoot_zero δ v hδ hv, speedCutoff_zero δ v hδ hv,
      zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul]
  · have hgap : 0 ≤ targetSpeed δ - v := by
      dsimp [targetSpeed, highSpeed] at *
      linarith
    simp only [correction, correctionRoot, mul_pow, Real.sq_sqrt hgap]

theorem correction_zero (δ v : ℝ) (hδ : 0 < δ) (hv : highSpeed δ ≤ v) : correction δ v = 0 := by
  simp only [correction, correctionRoot_zero δ v hδ hv, zero_pow (by decide : (2 : ℕ) ≠ 0)]

theorem correction_le_gap (δ v : ℝ) (hδ : 0 < δ) (hv : v ≤ highSpeed δ) :
    correction δ v ≤ targetSpeed δ - v := by
  have hz := speedCutoff_mem_Icc δ v
  have hzs : speedCutoff δ v ^ 2 ≤ 1 := by nlinarith [hz.1, hz.2]
  have hgap : 0 ≤ targetSpeed δ - v := by
    dsimp [highSpeed, targetSpeed] at *
    linarith
  rw [correction_formula δ v hδ]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hzs hgap

theorem correction_lt_three (δ v : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hv : 0 < v) :
    correction δ v < 3 := by
  by_cases hh : highSpeed δ ≤ v
  · rw [correction_zero δ v hδ hh]
    norm_num
  · have h := correction_le_gap δ v hδ (le_of_not_ge hh)
    dsimp [targetSpeed] at h
    linarith

theorem correctedSpeed_gt_two (δ v : ℝ) (hδ : 0 < δ) : 2 < correctedSpeed δ v := by
  by_cases hv : v ≤ lowSpeed δ
  · rw [correctedSpeed, correction_formula δ v hδ, speedCutoff_one δ v hδ hv]
    dsimp [targetSpeed]
    linarith
  · have hn := correction_nonneg δ v
    dsimp [correctedSpeed, lowSpeed] at *
    linarith

theorem correctedSpeed_le_target_of_active (δ v : ℝ) (hδ : 0 < δ)
    (hactive : speedCutoff δ v ≠ 0) : correctedSpeed δ v ≤ targetSpeed δ := by
  have hv : v ≤ highSpeed δ := by
    by_contra h
    exact hactive (speedCutoff_zero δ v hδ (le_of_lt (lt_of_not_ge h)))
  have h := correction_le_gap δ v hδ hv
  dsimp [correctedSpeed]
  linarith

/-- Variance root, given by `correctionRoot δ v / Real.sqrt a`. -/
def varianceRoot (a δ v : ℝ) : ℝ := correctionRoot δ v / Real.sqrt a

theorem varianceRoot_nonneg (a δ v : ℝ) : 0 ≤ varianceRoot a δ v :=
  div_nonneg (correctionRoot_nonneg δ v) (Real.sqrt_nonneg a)

theorem varianceRoot_sq (a δ v : ℝ) (ha : 0 < a) :
    varianceRoot a δ v ^ 2 = correction δ v / a := by
  simp only [varianceRoot, div_pow, Real.sq_sqrt ha.le, correction]

theorem varianceRoot_zero (a δ v : ℝ) (hδ : 0 < δ) (hv : highSpeed δ ≤ v) :
    varianceRoot a δ v = 0 := by
  simp only [varianceRoot, correctionRoot_zero δ v hδ hv, zero_div]

theorem varianceRoot_bound (amin a δ v : ℝ) (hmin : 0 < amin) (ha : amin ≤ a)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hv : 0 < v) :
    varianceRoot a δ v ≤ Real.sqrt (3 / amin) := by
  have hap : 0 < a := lt_of_lt_of_le hmin ha
  have hρ := (correction_lt_three δ v hδ hδ₁ hv).le
  have hsq : varianceRoot a δ v ^ 2 ≤ 3 / amin := by
    rw [varianceRoot_sq a δ v hap]
    exact (div_le_div_of_nonneg_right hρ hap.le).trans
      (div_le_div_of_nonneg_left (by norm_num) hmin ha)
  have hR := Real.sq_sqrt (show 0 ≤ 3 / amin by positivity)
  have hp := Real.sqrt_nonneg (3 / amin)
  nlinarith [varianceRoot_nonneg a δ v]

theorem solvedTilt_fixed_joint_contDiff (d : ℝ) (hd : d ≠ 0) :
    ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × (ℝ × ℝ) => solvedTilt z.1.1 d z.1.2 z.2.1 z.2.2) := by
  exact solvedTilt_smooth_family _ _ _ _ _ contDiff_fst.fst contDiff_const
    contDiff_fst.snd contDiff_snd.fst contDiff_snd.snd (fun _ => hd)

theorem solvedTilt_continuous_family {X : Type*} [TopologicalSpace X]
    (m p r θ : X → ℝ) (d : ℝ) (hd : d ≠ 0)
    (hm : Continuous m) (hp : Continuous p) (hr : Continuous r) (hθ : Continuous θ) :
    Continuous (fun x => solvedTilt (m x) d (p x) (r x) (θ x)) :=
  (solvedTilt_fixed_joint_contDiff d hd).continuous.comp ((hm.prodMk hp).prodMk (hr.prodMk hθ))

theorem uniform_tilt_cone_margin {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (m p₁ p₂ : X → ℝ)
    (hm : Continuous m) (hp₁ : Continuous p₁) (hp₂ : Continuous p₂)
    (d R : ℝ) (hd : 0 < d)
    (hmargin : ∀ x ∈ K, 2 ≤ p₁ x + p₂ x * m x - d) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ∀ r ∈ Icc (0 : ℝ) R, ∀ θ : ℝ,
      2 + ε ≤ coneBound (p₁ x + p₂ x * solvedTilt (m x) d (p₂ x) r θ)
        (p₂ x - p₁ x * solvedTilt (m x) d (p₂ x) r θ) := by
  let Q : Set (X × (ℝ × ℝ)) := K ×ˢ (Icc 0 R ×ˢ Icc 0 (2 * Real.pi))
  have hQ : IsCompact Q := hK.prod (isCompact_Icc.prod isCompact_Icc)
  let t : X × (ℝ × ℝ) → ℝ := fun z => solvedTilt (m z.1) d (p₂ z.1) z.2.1 z.2.2
  have ht : Continuous t := solvedTilt_continuous_family _ _ _ _ d (ne_of_gt hd)
    (hm.comp continuous_fst) (hp₂.comp continuous_fst) continuous_snd.fst continuous_snd.snd
  let P : X × (ℝ × ℝ) → ℝ := fun z => p₁ z.1 + p₂ z.1 * t z
  let J : X × (ℝ × ℝ) → ℝ := fun z => p₂ z.1 - p₁ z.1 * t z
  have hP : Continuous P := (hp₁.comp continuous_fst).add ((hp₂.comp continuous_fst).mul ht)
  have hJ : Continuous J := (hp₂.comp continuous_fst).sub ((hp₁.comp continuous_fst).mul ht)
  have hU : Continuous (fun z => coneBound (P z) (J z)) :=
    UniformCone.continuous_coneBound.comp (hP.prodMk
      (hJ.prodMk (continuous_const : Continuous (fun _ : X × (ℝ × ℝ) => (0 : ℝ)))))
  obtain ⟨ε, hε, hb⟩ := UniformCone.positive_uniform_margin hQ
    (hU.sub continuous_const).continuousOn (fun z hz => by
      apply sub_pos.mpr
      apply coneBound_gt_two
      exact solvedTilt_projection (p₁ z.1) (m z.1) d (p₂ z.1) z.2.1 hd (hmargin z.1 hz.1) z.2.2)
  refine ⟨ε, hε, fun x hx r hr θ => ?_⟩
  obtain ⟨θ₀, hθ₀, heq⟩ := (solvedTilt_periodic (m x) d (p₂ x) r).exists_mem_Ico₀ period_pos θ
  have hbound := hb (x, r, θ₀) ⟨hx, hr, ⟨hθ₀.1, hθ₀.2.le⟩⟩
  dsimp [P, J, t] at hbound
  rw [heq]
  linarith

/-- Nominal speed, given by `a * (1 + m ^ 2)`. -/
def nominalSpeed (a m : ℝ) : ℝ := a * (1 + m ^ 2)
/-- Seed rho, given by `correction δ (nominalSpeed a m)`. -/
def seedRho (a m δ : ℝ) : ℝ := correction δ (nominalSpeed a m)
/-- Seed speed, given by `correctedSpeed δ (nominalSpeed a m)`. -/
def seedSpeed (a m δ : ℝ) : ℝ := correctedSpeed δ (nominalSpeed a m)
/-- Seed tilt, given by `solvedTilt m d p (varianceRoot a δ (nominalSpeed a m)) θ`. -/
def seedTilt (a m d p δ θ : ℝ) : ℝ :=
  solvedTilt m d p (varianceRoot a δ (nominalSpeed a m)) θ

theorem seedSpeed_gt_two (a m δ : ℝ) (hδ : 0 < δ) : 2 < seedSpeed a m δ :=
  correctedSpeed_gt_two δ (nominalSpeed a m) hδ

theorem seedTilt_contDiff (a m d p δ : ℝ) : ContDiff ℝ ∞ (seedTilt a m d p δ) :=
  solvedTilt_contDiff _ _ _ _

theorem seedTilt_periodic (a m d p δ : ℝ) : Function.Periodic (seedTilt a m d p δ) (2 * Real.pi) :=
  solvedTilt_periodic _ _ _ _

theorem seedTilt_mean (a m d p δ : ℝ) : angularMean (seedTilt a m d p δ) = m :=
  solvedTilt_mean _ _ _ _

theorem seedTilt_variance (a m d p δ : ℝ) (ha : 0 < a) (hd : d ≠ 0) :
    angularMean (fun θ => (seedTilt a m d p δ θ - m) ^ 2) = seedRho a m δ / a := by
  unfold seedTilt
  rw [solvedTilt_variance _ _ _ _ hd, varianceRoot_sq a δ _ ha]
  rfl

theorem seedTilt_nominal_of_inactive (a m d p δ : ℝ)
    (hzero : speedCutoff δ (nominalSpeed a m) = 0) : seedTilt a m d p δ = (fun _ => m) := by
  funext θ
  unfold seedTilt varianceRoot correctionRoot
  rw [hzero, zero_mul, zero_div]
  exact solvedTilt_zero_target m d p θ

theorem seedSpeed_nominal_of_inactive (a m δ : ℝ)
    (hzero : speedCutoff δ (nominalSpeed a m) = 0) : seedSpeed a m δ = nominalSpeed a m := by
  simp only [seedSpeed, correctedSpeed, correction, correctionRoot, hzero,
    zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero]

theorem seedTilt_nominal (a m d p δ : ℝ) (hδ : 0 < δ)
    (hh : highSpeed δ ≤ nominalSpeed a m) : seedTilt a m d p δ = (fun _ => m) :=
  seedTilt_nominal_of_inactive a m d p δ (speedCutoff_zero δ _ hδ hh)

theorem seed_cone (a m p₁ p₂ d δ R : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hR : Real.sqrt (3 / a) ≤ R)
    (hmargin : 2 ≤ p₁ + p₂ * m - d)
    (hrelaxed : nominalSpeed a m < coneBound (p₁ + p₂ * m) (p₂ - p₁ * m))
    (hU : ∀ r ∈ Icc (0 : ℝ) R, ∀ θ,
      2 + δ ≤ coneBound (p₁ + p₂ * solvedTilt m d p₂ r θ)
        (p₂ - p₁ * solvedTilt m d p₂ r θ)) :
    ∀ θ, 2 < p₁ + p₂ * seedTilt a m d p₂ δ θ ∧
      seedSpeed a m δ < coneBound (p₁ + p₂ * seedTilt a m d p₂ δ θ)
        (p₂ - p₁ * seedTilt a m d p₂ δ θ) := by
  intro θ
  constructor
  · exact solvedTilt_projection p₁ m d p₂ _ hd hmargin θ
  · by_cases hzero : speedCutoff δ (nominalSpeed a m) = 0
    · rw [seedTilt_nominal_of_inactive a m d p₂ δ hzero,
        seedSpeed_nominal_of_inactive a m δ hzero]
      exact hrelaxed
    · have hv0 : 0 < nominalSpeed a m := mul_pos ha (one_add_sq_pos m)
      have hr : varianceRoot a δ (nominalSpeed a m) ∈ Icc (0 : ℝ) R :=
        ⟨varianceRoot_nonneg _ _ _,
          (varianceRoot_bound a a δ _ ha le_rfl hδ hδ₁ hv0).trans hR⟩
      have hu := hU _ hr θ
      have hv := correctedSpeed_le_target_of_active δ (nominalSpeed a m) hδ hzero
      dsimp [targetSpeed] at hv
      change seedSpeed a m δ ≤ 2 + δ / 2 at hv
      change 2 + δ ≤ coneBound (p₁ + p₂ * seedTilt a m d p₂ δ θ)
        (p₂ - p₁ * seedTilt a m d p₂ δ θ) at hu
      linarith

/-- Seed density, constructed using `densityOfTilt`. -/
def seedDensity (a m d p δ : ℝ) (ha : 0 < a) (hd : d ≠ 0) (hδ : 0 < δ) : CircleDensity :=
  densityOfTilt (seedTilt a m d p δ) a m (seedRho a m δ) (seedSpeed a m δ) ha
    (lt_trans (by norm_num) (seedSpeed_gt_two a m δ hδ))
    (seedTilt_contDiff a m d p δ) (seedTilt_periodic a m d p δ)
    (seedTilt_mean a m d p δ) (seedTilt_variance a m d p δ ha hd) rfl

/-- Constructed A, given by `rephase (seedDensity a m d p δ ha hd hδ) (fun θ => loopA (seedSpeed
a m δ) (seedTilt a m d p δ θ))`. -/
def constructedA (a m d p δ : ℝ) (ha : 0 < a) (hd : d ≠ 0) (hδ : 0 < δ) : ℝ → ℝ :=
  rephase (seedDensity a m d p δ ha hd hδ) (fun θ => loopA (seedSpeed a m δ) (seedTilt a m d p δ θ))

/-- Constructed C, given by `rephase (seedDensity a m d p δ ha hd hδ) (fun θ => loopC (seedSpeed
a m δ) (seedTilt a m d p δ θ))`. -/
def constructedC (a m d p δ : ℝ) (ha : 0 < a) (hd : d ≠ 0) (hδ : 0 < δ) : ℝ → ℝ :=
  rephase (seedDensity a m d p δ ha hd hδ) (fun θ => loopC (seedSpeed a m δ) (seedTilt a m d p δ θ))

/-- In true cone, constructed using `0`. -/
def InTrueCone (p₁ p₂ A C : ℝ) : Prop :=
  0 < A ∧ 2 < A * (1 + (C / A) ^ 2) ∧ 2 < p₁ + p₂ * (C / A) ∧
    A * (1 + (C / A) ^ 2) < coneBound (p₁ + p₂ * (C / A)) (p₂ - p₁ * (C / A))

/-- Positive additive margins for all four scalar inequalities, including
the positive first shear component. -/
def HasConeMargin (ε p₁ p₂ A C : ℝ) : Prop :=
  ε ≤ A ∧ ε ≤ A * (1 + (C / A) ^ 2) - 2 ∧ ε ≤ p₁ + p₂ * (C / A) - 2 ∧
    ε ≤ coneBound (p₁ + p₂ * (C / A)) (p₂ - p₁ * (C / A)) - A * (1 + (C / A) ^ 2)

/-- Compact slow parameters and a periodic fast parameter turn strict
pointwise cone inequalities into one positive margin at every fast angle. -/
theorem compact_periodic_trueCone_margins {X : Type*} [TopologicalSpace X]
    (p₁ p₂ : X → ℝ) (A C : X × ℝ → ℝ) {K : Set X} (hK : IsCompact K)
    (hp₁ : ContinuousOn p₁ K) (hp₂ : ContinuousOn p₂ K)
    (hA : ContinuousOn A (K ×ˢ (univ : Set ℝ)))
    (hC : ContinuousOn C (K ×ˢ (univ : Set ℝ)))
    (hAp : ∀ x ∈ K, Function.Periodic (fun φ => A (x, φ)) 1)
    (hCp : ∀ x ∈ K, Function.Periodic (fun φ => C (x, φ)) 1)
    (hcone : ∀ x ∈ K, ∀ φ, InTrueCone (p₁ x) (p₂ x) (A (x, φ)) (C (x, φ))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ∀ φ,
      HasConeMargin ε (p₁ x) (p₂ x) (A (x, φ)) (C (x, φ)) := by
  let Q : Set (X × ℝ) := K ×ˢ Icc 0 1
  have hQ : IsCompact Q := hK.prod isCompact_Icc
  have hAQ : ContinuousOn A Q := hA.mono (fun z hz => ⟨hz.1, mem_univ _⟩)
  have hCQ : ContinuousOn C Q := hC.mono (fun z hz => ⟨hz.1, mem_univ _⟩)
  have hp₁Q : ContinuousOn (fun z : X × ℝ => p₁ z.1) Q :=
    hp₁.comp continuousOn_fst (fun _ hz => hz.1)
  have hp₂Q : ContinuousOn (fun z : X × ℝ => p₂ z.1) Q :=
    hp₂.comp continuousOn_fst (fun _ hz => hz.1)
  let t : X × ℝ → ℝ := fun z => C z / A z
  let P : X × ℝ → ℝ := fun z => p₁ z.1 + p₂ z.1 * t z
  let J : X × ℝ → ℝ := fun z => p₂ z.1 - p₁ z.1 * t z
  let v : X × ℝ → ℝ := fun z => A z * (1 + t z ^ 2)
  have ht : ContinuousOn t Q := hCQ.div hAQ
    (fun z hz => ne_of_gt (hcone z.1 hz.1 z.2).1)
  have hP : ContinuousOn P Q := hp₁Q.add (hp₂Q.mul ht)
  have hJ : ContinuousOn J Q := hp₂Q.sub (hp₁Q.mul ht)
  have hv : ContinuousOn v Q := hAQ.mul (continuousOn_const.add (ht.pow 2))
  obtain ⟨εa, hεa, hma⟩ := UniformCone.positive_uniform_margin hQ hAQ
    (fun z hz => (hcone z.1 hz.1 z.2).1)
  obtain ⟨εc, hεc, hmc⟩ := UniformCone.compact_trueCone_margins hQ hP hJ hv
    (fun z hz => (hcone z.1 hz.1 z.2).2)
  refine ⟨min εa εc, lt_min hεa hεc, fun x hx φ => ?_⟩
  have hpair : Function.Periodic (fun θ => (A (x, θ), C (x, θ))) 1 := by
    intro θ
    exact Prod.ext (hAp x hx θ) (hCp x hx θ)
  obtain ⟨θ, hθ, heq⟩ := hpair.exists_mem_Ico₀ (by norm_num) φ
  have hAE : A (x, φ) = A (x, θ) := congrArg Prod.fst heq
  have hCE : C (x, φ) = C (x, θ) := congrArg Prod.snd heq
  rw [hAE, hCE]
  have hmem : (x, θ) ∈ Q := ⟨hx, hθ.1, hθ.2.le⟩
  exact ⟨(min_le_left _ _).trans (hma (x, θ) hmem),
    (min_le_right _ _).trans (hmc (x, θ) hmem).1,
    (min_le_right _ _).trans (hmc (x, θ) hmem).2.1,
    (min_le_right _ _).trans (hmc (x, θ) hmem).2.2⟩

theorem constructed_smooth (a m d p δ : ℝ) (ha : 0 < a) (hd : d ≠ 0) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (constructedA a m d p δ ha hd hδ) ∧
      ContDiff ℝ ∞ (constructedC a m d p δ ha hd hδ) := by
  have h := smooth_loop_shears (seedTilt a m d p δ) (seedSpeed a m δ) (seedTilt_contDiff a m d p δ)
  exact ⟨rephase_contDiff _ _ h.1, rephase_contDiff _ _ h.2⟩

theorem constructed_periodic (a m d p δ : ℝ) (ha : 0 < a) (hd : d ≠ 0) (hδ : 0 < δ) :
    Function.Periodic (constructedA a m d p δ ha hd hδ) 1 ∧
      Function.Periodic (constructedC a m d p δ ha hd hδ) 1 := by
  have h := periodic_loop_shears (seedTilt a m d p δ) (seedSpeed a m δ) (seedTilt_periodic a m d p
      δ)
  exact ⟨rephase_periodic _ _ h.1, rephase_periodic _ _ h.2⟩

theorem constructed_means (a m d p δ : ℝ) (ha : 0 < a) (hd : d ≠ 0) (hδ : 0 < δ) :
    (∫ φ in (0 : ℝ)..1, constructedA a m d p δ ha hd hδ φ) = a ∧
      (∫ φ in (0 : ℝ)..1, constructedC a m d p δ ha hd hδ φ) = a * m := by
  have hs := smooth_loop_shears (seedTilt a m d p δ) (seedSpeed a m δ) (seedTilt_contDiff a m d p δ)
  have hv : seedSpeed a m δ ≠ 0 := ne_of_gt (lt_trans (by norm_num) (seedSpeed_gt_two a m δ hδ))
  have hmom := angular_rephasing_moments (seedTilt a m d p δ) a m (seedRho a m δ)
    (seedSpeed a m δ) (ne_of_gt ha) hv (seedTilt_contDiff a m d p δ).continuous
    (seedTilt_mean a m d p δ) (seedTilt_variance a m d p δ ha hd) rfl
  constructor
  · unfold constructedA
    rw [integral_rephase _ _ hs.1.continuous]
    change (∫ θ in (0 : ℝ)..(2 * Real.pi),
      loopA (seedSpeed a m δ) (seedTilt a m d p δ θ) *
      (phaseDensity a (seedSpeed a m δ) (seedTilt a m d p δ θ) / (2 * Real.pi))) = a
    simp_rw [← mul_div_assoc, mul_comm (loopA _ _) (phaseDensity _ _ _)]
    rw [intervalIntegral.integral_div]
    exact hmom.2.1
  · unfold constructedC
    rw [integral_rephase _ _ hs.2.continuous]
    change (∫ θ in (0 : ℝ)..(2 * Real.pi),
      loopC (seedSpeed a m δ) (seedTilt a m d p δ θ) *
      (phaseDensity a (seedSpeed a m δ) (seedTilt a m d p δ θ) / (2 * Real.pi))) = a * m
    simp_rw [← mul_div_assoc, mul_comm (loopC _ _) (phaseDensity _ _ _)]
    rw [intervalIntegral.integral_div]
    exact hmom.2.2

theorem constructed_trueCone (a m p₁ p₂ d δ R : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hR : Real.sqrt (3 / a) ≤ R)
    (hmargin : 2 ≤ p₁ + p₂ * m - d)
    (hrelaxed : nominalSpeed a m < coneBound (p₁ + p₂ * m) (p₂ - p₁ * m))
    (hU : ∀ r ∈ Icc (0 : ℝ) R, ∀ θ,
      2 + δ ≤ coneBound (p₁ + p₂ * solvedTilt m d p₂ r θ)
        (p₂ - p₁ * solvedTilt m d p₂ r θ)) :
    ∀ φ, InTrueCone p₁ p₂ (constructedA a m d p₂ δ ha (ne_of_gt hd) hδ φ)
      (constructedC a m d p₂ δ ha (ne_of_gt hd) hδ φ) := by
  intro φ
  have hv := seedSpeed_gt_two a m δ hδ
  have hvpos : 0 < seedSpeed a m δ := lt_trans (by norm_num) hv
  let θ := (phaseHomeomorph (seedDensity a m d p₂ δ ha (ne_of_gt hd) hδ)).symm φ
  have hc := seed_cone a m p₁ p₂ d δ R ha hd hδ hδ₁ hR hmargin hrelaxed hU θ
  change InTrueCone p₁ p₂ (loopA (seedSpeed a m δ) (seedTilt a m d p₂ δ θ))
    (loopC (seedSpeed a m δ) (seedTilt a m d p₂ δ θ))
  unfold InTrueCone
  rw [loop_slope _ _ (ne_of_gt hvpos), loop_speed]
  exact ⟨loopA_pos _ _ hvpos, hv, hc⟩

theorem constructed_nominal (a m d p δ : ℝ) (ha : 0 < a) (hd : d ≠ 0) (hδ : 0 < δ)
    (hh : highSpeed δ ≤ nominalSpeed a m) :
    constructedA a m d p δ ha hd hδ = (fun _ => a) ∧
      constructedC a m d p δ ha hd hδ = (fun _ => a * m) := by
  have hz := speedCutoff_zero δ (nominalSpeed a m) hδ hh
  have ht := seedTilt_nominal_of_inactive a m d p δ hz
  have hv := seedSpeed_nominal_of_inactive a m δ hz
  constructor <;> funext φ <;> dsimp [constructedA, constructedC, rephase]
  · rw [ht, hv]
    unfold loopA nominalSpeed
    exact mul_div_cancel_right₀ a (ne_of_gt (one_add_sq_pos m))
  · rw [ht, hv]
    unfold loopC nominalSpeed
    have hnz := ne_of_gt (one_add_sq_pos m)
    field_simp

/-- Fixed-parameter true-cone realization, with no assumed loop or margin.
The nominal data need only satisfy the relaxed cone. -/
theorem exists_trueCone_loop (a m p₁ p₂ : ℝ) (ha : 0 < a)
    (hP : 2 < p₁ + p₂ * m)
    (hrelaxed : nominalSpeed a m < coneBound (p₁ + p₂ * m) (p₂ - p₁ * m)) :
    ∃ A C : ℝ → ℝ, ContDiff ℝ ∞ A ∧ ContDiff ℝ ∞ C ∧
      Function.Periodic A 1 ∧ Function.Periodic C 1 ∧
      (∫ φ in (0 : ℝ)..1, A φ) = a ∧ (∫ φ in (0 : ℝ)..1, C φ) = a * m ∧
      ∀ φ, InTrueCone p₁ p₂ (A φ) (C φ) := by
  let d := (p₁ + p₂ * m - 2) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hmargin : 2 ≤ p₁ + p₂ * m - d := by dsimp [d]; linarith
  let R := Real.sqrt (3 / a)
  obtain ⟨ε, hε, hU⟩ := uniform_tilt_cone_margin (X := ℝ) (K := {0}) isCompact_singleton
    (fun _ => m) (fun _ => p₁) (fun _ => p₂) continuous_const continuous_const continuous_const
    d R hd (fun _ _ => hmargin)
  let δ := min ε 1
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδ₁ : δ ≤ 1 := min_le_right _ _
  have hUδ : ∀ r ∈ Icc (0 : ℝ) R, ∀ θ,
      2 + δ ≤ coneBound (p₁ + p₂ * solvedTilt m d p₂ r θ) (p₂ - p₁ * solvedTilt m d p₂ r θ) := by
    intro r hr θ
    exact (add_le_add_right (min_le_left ε 1) 2).trans (hU 0 (by simp) r hr θ)
  let A := constructedA a m d p₂ δ ha (ne_of_gt hd) hδ
  let C := constructedC a m d p₂ δ ha (ne_of_gt hd) hδ
  have hs := constructed_smooth a m d p₂ δ ha (ne_of_gt hd) hδ
  have hp := constructed_periodic a m d p₂ δ ha (ne_of_gt hd) hδ
  have hm := constructed_means a m d p₂ δ ha (ne_of_gt hd) hδ
  exact ⟨A, C, hs.1, hs.2, hp.1, hp.2, hm.1, hm.2,
    constructed_trueCone a m p₁ p₂ d δ R ha hd hδ hδ₁ le_rfl hmargin hrelaxed hUδ⟩

/-- Family choices data, collecting `aMin`, `d`, `radius`, `maxAmplitude`, `delta`, `aMin_pos`
and their compatibility conditions. -/
structure FamilyChoices {X : Type*} (a m p₁ p₂ : X → ℝ) (K B : Set X) where
  /-- A min of `FamilyChoices`, of type `ℝ`. -/
  aMin : ℝ
  /-- D of `FamilyChoices`, of type `ℝ`. -/
  d : ℝ
  /-- Radius of `FamilyChoices`, of type `ℝ`. -/
  radius : ℝ
  /-- Max amplitude of `FamilyChoices`, of type `ℝ`. -/
  maxAmplitude : ℝ
  /-- Delta of `FamilyChoices`, of type `ℝ`. -/
  delta : ℝ
  aMin_pos : 0 < aMin
  d_pos : 0 < d
  radius_eq : radius = Real.sqrt (3 / aMin)
  maxAmplitude_pos : 0 < maxAmplitude
  delta_pos : 0 < delta
  delta_le_one : delta ≤ 1
  aMin_le : ∀ x ∈ K, aMin ≤ a x
  projection_margin : ∀ x ∈ K, 2 ≤ p₁ x + p₂ x * m x - d
  amplitude_large : ∀ x ∈ K, 3 / aMin < tiltVariance d (p₂ x) maxAmplitude
  cone_margin : ∀ x ∈ K, ∀ r ∈ Icc (0 : ℝ) radius, ∀ θ,
    2 + delta ≤ coneBound (p₁ x + p₂ x * solvedTilt (m x) d (p₂ x) r θ)
      (p₂ x - p₁ x * solvedTilt (m x) d (p₂ x) r θ)
  boundary_inactive : ∀ x ∈ B, highSpeed delta < nominalSpeed (a x) (m x)

theorem exists_family_choices {X : Type*} [TopologicalSpace X]
    (a m p₁ p₂ : X → ℝ) {K B : Set X} (hK : IsCompact K) (hB : IsCompact B)
    (ha : Continuous a) (hm : Continuous m) (hp₁ : Continuous p₁) (hp₂ : Continuous p₂)
    (haK : ∀ x ∈ K, 0 < a x) (hPK : ∀ x ∈ K, 2 < p₁ x + p₂ x * m x)
    (htrueB : ∀ x ∈ B, 2 < nominalSpeed (a x) (m x)) :
    Nonempty (FamilyChoices a m p₁ p₂ K B) := by
  obtain ⟨amin, hamin, haminle⟩ := UniformCone.positive_uniform_margin hK ha.continuousOn haK
  obtain ⟨ep, hep, heple⟩ := UniformCone.positive_uniform_margin hK
    ((hp₁.fun_add (hp₂.fun_mul hm)).fun_sub continuous_const).continuousOn
    (fun x hx => sub_pos.mpr (hPK x hx))
  let d := ep / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hproj : ∀ x ∈ K, 2 ≤ p₁ x + p₂ x * m x - d := by
    intro x hx
    have h := heple x hx
    dsimp [d]
    linarith
  let R := Real.sqrt (3 / amin)
  obtain ⟨M, hM, hML⟩ := uniform_variance_amplitude (hK.image hp₂) d (3 / amin) hd (by positivity)
  obtain ⟨eu, heu, hmargin⟩ := uniform_tilt_cone_margin hK m p₁ p₂ hm hp₁ hp₂ d R hd hproj
  have hnom : Continuous (fun x => nominalSpeed (a x) (m x)) :=
    ha.mul (continuous_const.add (hm.pow 2))
  obtain ⟨eb, heb, heble⟩ := UniformCone.positive_uniform_margin hB
    (hnom.fun_sub continuous_const).continuousOn (fun x hx => sub_pos.mpr (htrueB x hx))
  let δ := min 1 (min eu eb)
  have hδ : 0 < δ := lt_min (by norm_num) (lt_min heu heb)
  have hδu : δ ≤ eu := (min_le_right _ _).trans (min_le_left _ _)
  have hδb : δ ≤ eb := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨⟨amin, d, R, M, δ, hamin, hd, rfl, hM, hδ, min_le_left _ _, haminle,
    hproj, ?_, ?_, ?_⟩⟩
  · intro x hx
    exact hML (p₂ x) (mem_image_of_mem p₂ hx)
  · intro x hx r hr θ
    exact (add_le_add_right hδu 2).trans (hmargin x hx r hr θ)
  · intro x hx
    have h := heble x hx
    dsimp [highSpeed]
    linarith

theorem FamilyChoices.root_bound {X : Type*} {a m p₁ p₂ : X → ℝ} {K B : Set X}
    (c : FamilyChoices a m p₁ p₂ K B) {x : X} (hx : x ∈ K) :
    varianceRoot (a x) c.delta (nominalSpeed (a x) (m x)) ∈ Icc (0 : ℝ) c.radius := by
  have ha : 0 < a x := lt_of_lt_of_le c.aMin_pos (c.aMin_le x hx)
  rw [c.radius_eq]
  exact ⟨varianceRoot_nonneg _ _ _, varianceRoot_bound c.aMin (a x) c.delta _
    c.aMin_pos (c.aMin_le x hx) c.delta_pos c.delta_le_one (mul_pos ha (one_add_sq_pos _))⟩

theorem FamilyChoices.amplitude_bound {X : Type*} {a m p₁ p₂ : X → ℝ} {K B : Set X}
    (c : FamilyChoices a m p₁ p₂ K B) {x : X} (hx : x ∈ K) :
    0 ≤ solveScale c.d (p₂ x) (varianceRoot (a x) c.delta (nominalSpeed (a x) (m x))) ∧
      solveScale c.d (p₂ x) (varianceRoot (a x) c.delta (nominalSpeed (a x) (m x))) <
          c.maxAmplitude := by
  let r := varianceRoot (a x) c.delta (nominalSpeed (a x) (m x))
  have hr := c.root_bound hx
  have hμ := solveScale_nonneg c.d (p₂ x) r c.d_pos hr.1
  refine ⟨hμ, ?_⟩
  have htarget : tiltVariance c.d (p₂ x) (solveScale c.d (p₂ x) r) ≤ 3 / c.aMin := by
    rw [solveScale_variance _ _ _ (ne_of_gt c.d_pos)]
    have hR := Real.sq_sqrt (div_nonneg (by norm_num : (0 : ℝ) ≤ 3) c.aMin_pos.le)
    have hrle : r ≤ Real.sqrt (3 / c.aMin) := by simpa only [c.radius_eq] using hr.2
    have hsqnonneg := Real.sqrt_nonneg (3 / c.aMin)
    nlinarith [hr.1]
  by_contra hn
  have hμM : c.maxAmplitude ≤ solveScale c.d (p₂ x) r := le_of_not_gt hn
  have hmono := (tiltVariance_strictMonoOn c.d (p₂ x) c.d_pos).monotoneOn
    c.maxAmplitude_pos.le hμ hμM
  have hlarge := c.amplitude_large x hx
  linarith

section SmoothFamily

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem nominalSpeed_family_contDiff (a m : E → ℝ)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) :
    ContDiff ℝ ∞ (fun x => nominalSpeed (a x) (m x)) :=
  ha.mul (contDiff_const.add (hm.pow 2))

theorem seedSpeed_family_contDiff (a m : E → ℝ) (δ : ℝ)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (fun x => seedSpeed (a x) (m x) δ) := by
  have hn := nominalSpeed_family_contDiff a m ha hm
  exact hn.add (((correctionRoot_contDiff δ hδ).comp hn).pow 2)

theorem seedTilt_family_contDiffOn (a m p : E → ℝ) (d δ : ℝ)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp : ContDiff ℝ ∞ p)
    (hd : d ≠ 0) (hδ : 0 < δ) :
    ContDiffOn ℝ ∞ (fun z : E × ℝ => seedTilt (a z.1) (m z.1) d (p z.1) δ z.2)
      ({x | 0 < a x} ×ˢ (univ : Set ℝ)) := by
  let S : Set (E × ℝ) := {x | 0 < a x} ×ˢ (univ : Set ℝ)
  have haf : ContDiffOn ℝ ∞ (fun z : E × ℝ => a z.1) S := (ha.comp contDiff_fst).contDiffOn
  have hmf : ContDiffOn ℝ ∞ (fun z : E × ℝ => m z.1) S := (hm.comp contDiff_fst).contDiffOn
  have hpf : ContDiffOn ℝ ∞ (fun z : E × ℝ => p z.1) S := (hp.comp contDiff_fst).contDiffOn
  have hnom : ContDiffOn ℝ ∞ (fun z : E × ℝ => nominalSpeed (a z.1) (m z.1)) S :=
    haf.mul (contDiffOn_const.add (hmf.pow 2))
  have hsqrt : ContDiffOn ℝ ∞ (fun z : E × ℝ => Real.sqrt (a z.1)) S :=
    haf.sqrt (fun z hz => ne_of_gt hz.1)
  have hroot : ContDiffOn ℝ ∞
      (fun z : E × ℝ => varianceRoot (a z.1) δ (nominalSpeed (a z.1) (m z.1))) S :=
    ((correctionRoot_contDiff δ hδ).comp_contDiffOn hnom).div hsqrt
      (fun z hz => ne_of_gt (Real.sqrt_pos.mpr hz.1))
  exact (solvedTilt_fixed_joint_contDiff d hd).comp_contDiffOn
    ((hmf.prodMk hpf).prodMk (hroot.prodMk contDiff_snd.contDiffOn))

/-- Constant density, bundling `rate`, `smooth`, `positive`, `periodic` and the required
compatibility proofs. -/
def constantDensity : CircleDensity where
  rate _ := 1 / (2 * Real.pi)
  smooth := contDiff_const
  positive _ := one_div_pos.mpr period_pos
  periodic := fun _ => rfl
  integral_one := by
    rw [intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    field_simp [Real.pi_ne_zero]

/-- Family density, defined pointwise by `if hx : 0 < a x then seedDensity (a x) (m x) d (p x) δ
hx hd hδ else constantDensity`. -/
def familyDensity (a m p : E → ℝ) (d δ : ℝ) (hd : d ≠ 0) (hδ : 0 < δ) : E → CircleDensity :=
  fun x => if hx : 0 < a x then seedDensity (a x) (m x) d (p x) δ hx hd hδ else constantDensity

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem familyDensity_eq (a m p : E → ℝ) (d δ : ℝ) (hd : d ≠ 0) (hδ : 0 < δ)
    (x : E) (hx : 0 < a x) :
    familyDensity a m p d δ hd hδ x = seedDensity (a x) (m x) d (p x) δ hx hd hδ := by
  simp only [familyDensity, dite_eq_left hx]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem familyDensity_rate_eq (a m p : E → ℝ) (d δ : ℝ) (hd : d ≠ 0) (hδ : 0 < δ)
    (x : E) (hx : 0 < a x) (θ : ℝ) :
    (familyDensity a m p d δ hd hδ x).rate θ =
      phaseDensity (a x) (seedSpeed (a x) (m x) δ) (seedTilt (a x) (m x) d (p x) δ θ) /
        (2 * Real.pi) := by
  rw [familyDensity_eq a m p d δ hd hδ x hx]
  rfl

theorem familyDensity_rate_contDiffOn (a m p : E → ℝ) (d δ : ℝ)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp : ContDiff ℝ ∞ p)
    (hd : d ≠ 0) (hδ : 0 < δ) :
    ContDiffOn ℝ ∞ (fun z : E × ℝ => (familyDensity a m p d δ hd hδ z.1).rate z.2)
      ({x | 0 < a x} ×ˢ (univ : Set ℝ)) := by
  have ht := seedTilt_family_contDiffOn a m p d δ ha hm hp hd hδ
  have hv : ContDiff ℝ ∞ (fun z : E × ℝ => seedSpeed (a z.1) (m z.1) δ) :=
    (seedSpeed_family_contDiff a m δ ha hm hδ).comp contDiff_fst
  have hrat : ContDiffOn ℝ ∞ (fun z : E × ℝ =>
      phaseDensity (a z.1) (seedSpeed (a z.1) (m z.1) δ) (seedTilt (a z.1) (m z.1) d (p z.1) δ z.2)
          /
        (2 * Real.pi)) ({x | 0 < a x} ×ˢ (univ : Set ℝ)) := by
    exact (((ha.comp contDiff_fst).contDiffOn.mul (contDiffOn_const.add (ht.pow 2))).div
      hv.contDiffOn (fun z _ => ne_of_gt (lt_trans (by norm_num)
        (seedSpeed_gt_two (a z.1) (m z.1) δ hδ)))).div_const _
  apply hrat.congr
  intro z hz
  exact familyDensity_rate_eq a m p d δ hd hδ z.1 hz.1 z.2

/-- Unphased A, given by `loopA (seedSpeed (a z.1) (m z.1) δ) (seedTilt (a z.1) (m z.1) d (p
z.1) δ z.2)`. -/
def unphasedA (a m p : E → ℝ) (d δ : ℝ) (z : E × ℝ) : ℝ :=
  loopA (seedSpeed (a z.1) (m z.1) δ) (seedTilt (a z.1) (m z.1) d (p z.1) δ z.2)

/-- Unphased C, given by `loopC (seedSpeed (a z.1) (m z.1) δ) (seedTilt (a z.1) (m z.1) d (p
z.1) δ z.2)`. -/
def unphasedC (a m p : E → ℝ) (d δ : ℝ) (z : E × ℝ) : ℝ :=
  loopC (seedSpeed (a z.1) (m z.1) δ) (seedTilt (a z.1) (m z.1) d (p z.1) δ z.2)

theorem unphased_contDiffOn (a m p : E → ℝ) (d δ : ℝ)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp : ContDiff ℝ ∞ p)
    (hd : d ≠ 0) (hδ : 0 < δ) :
    ContDiffOn ℝ ∞ (unphasedA a m p d δ) ({x | 0 < a x} ×ˢ (univ : Set ℝ)) ∧
      ContDiffOn ℝ ∞ (unphasedC a m p d δ) ({x | 0 < a x} ×ˢ (univ : Set ℝ)) := by
  have ht := seedTilt_family_contDiffOn a m p d δ ha hm hp hd hδ
  have hv : ContDiffOn ℝ ∞ (fun z : E × ℝ => seedSpeed (a z.1) (m z.1) δ)
      ({x | 0 < a x} ×ˢ (univ : Set ℝ)) :=
    ((seedSpeed_family_contDiff a m δ ha hm hδ).comp contDiff_fst).contDiffOn
  have hden : ContDiffOn ℝ ∞
      (fun z : E × ℝ => 1 + seedTilt (a z.1) (m z.1) d (p z.1) δ z.2 ^ 2)
      ({x | 0 < a x} ×ˢ (univ : Set ℝ)) := contDiffOn_const.add (ht.pow 2)
  have hnz : ∀ z ∈ ({x | 0 < a x} ×ˢ (univ : Set ℝ)),
      1 + seedTilt (a z.1) (m z.1) d (p z.1) δ z.2 ^ 2 ≠ 0 :=
    fun z _ => ne_of_gt (one_add_sq_pos _)
  exact ⟨hv.div hden hnz, (hv.mul ht).div hden hnz⟩

/-- Family A, given by `rephase (familyDensity a m p d δ hd hδ z.1) (fun θ => unphasedA a m p d
δ (z.1, θ)) z.2`. -/
def familyA (a m p : E → ℝ) (d δ : ℝ) (hd : d ≠ 0) (hδ : 0 < δ) (z : E × ℝ) : ℝ :=
  rephase (familyDensity a m p d δ hd hδ z.1)
    (fun θ => unphasedA a m p d δ (z.1, θ)) z.2

/-- Family C, given by `rephase (familyDensity a m p d δ hd hδ z.1) (fun θ => unphasedC a m p d
δ (z.1, θ)) z.2`. -/
def familyC (a m p : E → ℝ) (d δ : ℝ) (hd : d ≠ 0) (hδ : 0 < δ) (z : E × ℝ) : ℝ :=
  rephase (familyDensity a m p d δ hd hδ z.1)
    (fun θ => unphasedC a m p d δ (z.1, θ)) z.2

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem familyA_eq_constructed (a m p : E → ℝ) (d δ : ℝ) (hd : d ≠ 0) (hδ : 0 < δ)
    (x : E) (hx : 0 < a x) :
    (fun φ => familyA a m p d δ hd hδ (x, φ)) = constructedA (a x) (m x) d (p x) δ hx hd hδ := by
  funext φ
  unfold familyA
  rw [familyDensity_eq a m p d δ hd hδ x hx]
  rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem familyC_eq_constructed (a m p : E → ℝ) (d δ : ℝ) (hd : d ≠ 0) (hδ : 0 < δ)
    (x : E) (hx : 0 < a x) :
    (fun φ => familyC a m p d δ hd hδ (x, φ)) = constructedC (a x) (m x) d (p x) δ hx hd hδ := by
  funext φ
  unfold familyC
  rw [familyDensity_eq a m p d δ hd hδ x hx]
  rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem family_pointwise_properties (a m p₁ p₂ : E → ℝ) {K B : Set E}
    (c : FamilyChoices a m p₁ p₂ K B)
    (hrelaxed : ∀ x ∈ K, nominalSpeed (a x) (m x) <
      coneBound (p₁ x + p₂ x * m x) (p₂ x - p₁ x * m x)) :
    ∀ x ∈ K,
      Function.Periodic (fun φ => familyA a m p₂ c.d c.delta (ne_of_gt c.d_pos) c.delta_pos (x, φ))
          1 ∧
      Function.Periodic (fun φ => familyC a m p₂ c.d c.delta (ne_of_gt c.d_pos) c.delta_pos (x, φ))
          1 ∧
      (∫ φ in (0 : ℝ)..1, familyA a m p₂ c.d c.delta (ne_of_gt c.d_pos) c.delta_pos (x, φ)) = a x ∧
      (∫ φ in (0 : ℝ)..1, familyC a m p₂ c.d c.delta (ne_of_gt c.d_pos) c.delta_pos (x, φ)) = a x *
          m x ∧
      ∀ φ, InTrueCone (p₁ x) (p₂ x)
        (familyA a m p₂ c.d c.delta (ne_of_gt c.d_pos) c.delta_pos (x, φ))
        (familyC a m p₂ c.d c.delta (ne_of_gt c.d_pos) c.delta_pos (x, φ)) := by
  intro x hx
  have hax : 0 < a x := lt_of_lt_of_le c.aMin_pos (c.aMin_le x hx)
  have hAe := familyA_eq_constructed a m p₂ c.d c.delta (ne_of_gt c.d_pos) c.delta_pos x hax
  have hCe := familyC_eq_constructed a m p₂ c.d c.delta (ne_of_gt c.d_pos) c.delta_pos x hax
  have hp := constructed_periodic (a x) (m x) c.d (p₂ x) c.delta hax (ne_of_gt c.d_pos) c.delta_pos
  have hm := constructed_means (a x) (m x) c.d (p₂ x) c.delta hax (ne_of_gt c.d_pos) c.delta_pos
  have hR : Real.sqrt (3 / a x) ≤ c.radius := by
    rw [c.radius_eq]
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (by norm_num) c.aMin_pos (c.aMin_le x hx))
  have hc := constructed_trueCone (a x) (m x) (p₁ x) (p₂ x) c.d c.delta c.radius hax c.d_pos
    c.delta_pos c.delta_le_one hR (c.projection_margin x hx) (hrelaxed x hx) (c.cone_margin x hx)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hAe]
    exact hp.1
  · rw [hCe]
    exact hp.2
  · simpa only [hAe] using hm.1
  · simpa only [hCe] using hm.2
  · intro φ
    rw [congrFun hAe φ, congrFun hCe φ]
    exact hc φ

omit [NormedSpace ℝ E] in
theorem family_nominal_neighborhood (a m p₁ p₂ : E → ℝ) {K B : Set E}
    (c : FamilyChoices a m p₁ p₂ K B) (ha : Continuous a) (hm : Continuous m) (hBK : B ⊆ K) :
    ∃ N : Set E, IsOpen N ∧ B ⊆ N ∧ N ⊆ {x | 0 < a x} ∧
      ∀ x ∈ N, ∀ φ,
        familyA a m p₂ c.d c.delta (ne_of_gt c.d_pos) c.delta_pos (x, φ) = a x ∧
        familyC a m p₂ c.d c.delta (ne_of_gt c.d_pos) c.delta_pos (x, φ) = a x * m x := by
  let N : Set E := {x | 0 < a x} ∩ {x | highSpeed c.delta < nominalSpeed (a x) (m x)}
  have hnom : Continuous (fun x => nominalSpeed (a x) (m x)) := ha.mul (continuous_const.add
      (hm.pow 2))
  have hN : IsOpen N := (isOpen_lt continuous_const ha).inter (isOpen_lt continuous_const hnom)
  have hBN : B ⊆ N := by
    intro x hx
    exact ⟨lt_of_lt_of_le c.aMin_pos (c.aMin_le x (hBK hx)), c.boundary_inactive x hx⟩
  refine ⟨N, hN, hBN, inter_subset_left, ?_⟩
  intro x hx φ
  have hAe := familyA_eq_constructed a m p₂ c.d c.delta (ne_of_gt c.d_pos) c.delta_pos x hx.1
  have hCe := familyC_eq_constructed a m p₂ c.d c.delta (ne_of_gt c.d_pos) c.delta_pos x hx.1
  have hn := constructed_nominal (a x) (m x) c.d (p₂ x) c.delta hx.1
    (ne_of_gt c.d_pos) c.delta_pos hx.2.le
  rw [congrFun hAe φ, congrFun hCe φ, hn.1, hn.2]
  exact ⟨rfl, rfl⟩

theorem family_joint_contDiffOn [FiniteDimensional ℝ E]
    (a m p : E → ℝ) (d δ : ℝ)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp : ContDiff ℝ ∞ p)
    (hd : d ≠ 0) (hδ : 0 < δ) :
    ContDiffOn ℝ ∞ (familyA a m p d δ hd hδ) ({x | 0 < a x} ×ˢ (univ : Set ℝ)) ∧
      ContDiffOn ℝ ∞ (familyC a m p d δ hd hδ) ({x | 0 < a x} ×ˢ (univ : Set ℝ)) := by
  have hU : IsOpen {x | 0 < a x} := isOpen_lt continuous_const ha.continuous
  have hrate := familyDensity_rate_contDiffOn a m p d δ ha hm hp hd hδ
  have hf := unphased_contDiffOn a m p d δ ha hm hp hd hδ
  exact ⟨ParametricRephase.rephaseFamily_contDiffOn (familyDensity a m p d δ hd hδ)
      (unphasedA a m p d δ) _ hU hrate hf.1,
    ParametricRephase.rephaseFamily_contDiffOn (familyDensity a m p d δ hd hδ)
      (unphasedC a m p d δ) _ hU hrate hf.2⟩

/-- Full compact-family true-cone realization. The set `B` can be the two
interval boundary faces (including any compact auxiliary parameter set).
The output agrees exactly with the nominal shear on an open neighborhood
of `B`, and is jointly C∞ in slow parameters and periodic angle. -/
theorem exists_compact_trueCone_family [FiniteDimensional ℝ E]
    (a m p₁ p₂ : E → ℝ) {K B : Set E}
    (hK : IsCompact K) (hB : IsCompact B) (hBK : B ⊆ K)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m)
    (hp₁ : ContDiff ℝ ∞ p₁) (hp₂ : ContDiff ℝ ∞ p₂)
    (haK : ∀ x ∈ K, 0 < a x)
    (hPK : ∀ x ∈ K, 2 < p₁ x + p₂ x * m x)
    (hrelaxed : ∀ x ∈ K, nominalSpeed (a x) (m x) <
      coneBound (p₁ x + p₂ x * m x) (p₂ x - p₁ x * m x))
    (htrueB : ∀ x ∈ B, 2 < nominalSpeed (a x) (m x)) :
    ∃ U N : Set E, ∃ A C : E × ℝ → ℝ,
      IsOpen U ∧ K ⊆ U ∧ IsOpen N ∧ B ⊆ N ∧ N ⊆ U ∧
      ContDiffOn ℝ ∞ A (U ×ˢ (univ : Set ℝ)) ∧
      ContDiffOn ℝ ∞ C (U ×ˢ (univ : Set ℝ)) ∧
      (∀ x ∈ K, Function.Periodic (fun φ => A (x, φ)) 1 ∧
        Function.Periodic (fun φ => C (x, φ)) 1 ∧
        (∫ φ in (0 : ℝ)..1, A (x, φ)) = a x ∧
        (∫ φ in (0 : ℝ)..1, C (x, φ)) = a x * m x ∧
        ∀ φ, InTrueCone (p₁ x) (p₂ x) (A (x, φ)) (C (x, φ))) ∧
      (∀ x ∈ N, ∀ φ, A (x, φ) = a x ∧ C (x, φ) = a x * m x) := by
  obtain ⟨c⟩ := exists_family_choices a m p₁ p₂ hK hB ha.continuous hm.continuous
    hp₁.continuous hp₂.continuous haK hPK htrueB
  let U : Set E := {x | 0 < a x}
  let A := familyA a m p₂ c.d c.delta (ne_of_gt c.d_pos) c.delta_pos
  let C := familyC a m p₂ c.d c.delta (ne_of_gt c.d_pos) c.delta_pos
  obtain ⟨N, hN, hBN, hNU, hmatch⟩ :=
    family_nominal_neighborhood a m p₁ p₂ c ha.continuous hm.continuous hBK
  have hs := family_joint_contDiffOn a m p₂ c.d c.delta ha hm hp₂ (ne_of_gt c.d_pos) c.delta_pos
  exact ⟨U, N, A, C, isOpen_lt continuous_const ha.continuous, haK,
    hN, hBN, hNU, hs.1, hs.2, family_pointwise_properties a m p₁ p₂ c hrelaxed, hmatch⟩

/-- The complete family theorem with one strictly positive margin valid
for every slow parameter in `K` and every fast angle. -/
theorem exists_compact_trueCone_family_with_margin [FiniteDimensional ℝ E]
    (a m p₁ p₂ : E → ℝ) {K B : Set E}
    (hK : IsCompact K) (hB : IsCompact B) (hBK : B ⊆ K)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m)
    (hp₁ : ContDiff ℝ ∞ p₁) (hp₂ : ContDiff ℝ ∞ p₂)
    (haK : ∀ x ∈ K, 0 < a x)
    (hPK : ∀ x ∈ K, 2 < p₁ x + p₂ x * m x)
    (hrelaxed : ∀ x ∈ K, nominalSpeed (a x) (m x) <
      coneBound (p₁ x + p₂ x * m x) (p₂ x - p₁ x * m x))
    (htrueB : ∀ x ∈ B, 2 < nominalSpeed (a x) (m x)) :
    ∃ ε : ℝ, ∃ U N : Set E, ∃ A C : E × ℝ → ℝ,
      0 < ε ∧ IsOpen U ∧ K ⊆ U ∧ IsOpen N ∧ B ⊆ N ∧ N ⊆ U ∧
      ContDiffOn ℝ ∞ A (U ×ˢ (univ : Set ℝ)) ∧
      ContDiffOn ℝ ∞ C (U ×ˢ (univ : Set ℝ)) ∧
      (∀ x ∈ K, Function.Periodic (fun φ => A (x, φ)) 1 ∧
        Function.Periodic (fun φ => C (x, φ)) 1 ∧
        (∫ φ in (0 : ℝ)..1, A (x, φ)) = a x ∧
        (∫ φ in (0 : ℝ)..1, C (x, φ)) = a x * m x ∧
        ∀ φ, InTrueCone (p₁ x) (p₂ x) (A (x, φ)) (C (x, φ)) ∧
          HasConeMargin ε (p₁ x) (p₂ x) (A (x, φ)) (C (x, φ))) ∧
      (∀ x ∈ N, ∀ φ, A (x, φ) = a x ∧ C (x, φ) = a x * m x) := by
  obtain ⟨U, N, A, C, hU, hKU, hN, hBN, hNU, hA, hC, hloops, hmatch⟩ :=
    exists_compact_trueCone_family a m p₁ p₂ hK hB hBK ha hm hp₁ hp₂ haK hPK hrelaxed htrueB
  have hsub : K ×ˢ (univ : Set ℝ) ⊆ U ×ˢ (univ : Set ℝ) :=
    fun _ hz => ⟨hKU hz.1, hz.2⟩
  obtain ⟨ε, hε, hmargin⟩ := compact_periodic_trueCone_margins p₁ p₂ A C hK
    hp₁.continuous.continuousOn hp₂.continuous.continuousOn
    (hA.continuousOn.mono hsub) (hC.continuousOn.mono hsub)
    (fun x hx => (hloops x hx).1) (fun x hx => (hloops x hx).2.1)
    (fun x hx => (hloops x hx).2.2.2.2)
  refine ⟨ε, U, N, A, C, hε, hU, hKU, hN, hBN, hNU, hA, hC, ?_, hmatch⟩
  intro x hx
  obtain ⟨hpA, hpC, hmA, hmC, hc⟩ := hloops x hx
  exact ⟨hpA, hpC, hmA, hmC, fun φ => ⟨hc φ, hmargin x hx φ⟩⟩

end SmoothFamily

end

end NavierStokes.TrueConeLoop
