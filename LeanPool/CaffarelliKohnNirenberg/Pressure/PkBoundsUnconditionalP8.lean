/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsUnconditionalConstants

/-!
# Pk Bounds Unconditional P8

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration

noncomputable section

namespace CKN

private theorem force_time_norm_bound
    {H : ℝ → ℝ≥0∞} {T : Set ℝ} {q A : ℝ}
    (hq : 0 < q) (hA : 0 ≤ A)
    (hHae : ∀ᵐ s ∂volume.restrict T, H s < ⊤)
    (hglobal : (∫⁻ s in T, H s) ≤ ENNReal.ofReal (A ^ q)) :
    eLpNorm' (fun s => (H s).toReal ^ (1 / q)) q
        (volume.restrict T) ≤ ENNReal.ofReal A := by
  let g : ℝ → ℝ := fun s => (H s).toReal ^ (1 / q)
  have hpow : ∀ᵐ s ∂volume.restrict T,
      ‖g s‖ₑ ^ q = H s := by
    filter_upwards [hHae] with s hs
    have hmul : (1 / q) * q = (1 : ℝ) := by field_simp
    rw [Real.enorm_eq_ofReal (Real.rpow_nonneg ENNReal.toReal_nonneg _)]
    rw [ENNReal.ofReal_rpow_of_nonneg
      (Real.rpow_nonneg ENNReal.toReal_nonneg _) hq.le]
    rw [← Real.rpow_mul ENNReal.toReal_nonneg, hmul, Real.rpow_one,
      ENNReal.ofReal_toReal hs.ne]
  have hlin : (∫⁻ s in T, ‖g s‖ₑ ^ q) = ∫⁻ s in T, H s := by
    apply lintegral_congr_ae
    exact hpow
  have hnorm : eLpNorm' g q (volume.restrict T) ≤ ENNReal.ofReal A := by
    rw [eLpNorm'_eq_lintegral_enorm, hlin]
    calc
      (∫⁻ s in T, H s) ^ (1 / q) ≤
          (ENNReal.ofReal (A ^ q)) ^ (1 / q) :=
        ENNReal.rpow_le_rpow hglobal (by positivity)
      _ = ENNReal.ofReal A := by
        rw [← ENNReal.ofReal_rpow_of_nonneg hA hq.le,
          ← ENNReal.rpow_mul]
        rw [show q * (1 / q) = (1 : ℝ) by field_simp]
        simp
  simpa [g] using hnorm

private lemma pressureP8_bound_hX_1 :
    ∀ {q : ℝ} {f : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ r : ℝ},
      (0 : ℝ) < r →
        let Tρ : Set ℝ := Ioc (z.2 - ρ ^ (2 : ℕ)) z.2;
        let Tr : Set ℝ := Ioc (z.2 - r ^ (2 : ℕ)) z.2;
        ∀ (H : ℝ → ℝ≥0∞),
          let G : ℝ → ℝ := fun (s : ℝ) => (H s).toReal ^ ((1 : ℝ) / q);
          eLpNorm' G q (volume.restrict Tρ) ≤
              ENNReal.ofReal (ρ ^ ((5 : ℝ) / q - (3 : ℝ)) * lambda q f z ρ) →
            (∫⁻ (s : ℝ) in Ioc (z.2 - r ^ (2 : ℕ)) z.2, ENNReal.ofReal (G s) ^ (3 / 2 : ℝ)) ^
                  (2 / 3 : ℝ) ≤
                ENNReal.ofReal r ^ ((2 : ℝ) * ((2 / 3 : ℝ) - (1 : ℝ) / q)) *
                  eLpNorm' G q (volume.restrict (Ioc (z.2 - ρ ^ (2 : ℕ)) z.2)) →
              (∫⁻ (s : ℝ) in Tr, ‖G s‖ₑ ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
                ENNReal.ofReal (r ^ ((2 : ℝ) * ((2 / 3 : ℝ) - (1 : ℝ) / q))) *
                  ENNReal.ofReal (ρ ^ ((5 : ℝ) / q - (3 : ℝ)) * lambda q f z ρ)
    := by
  intro q f z ρ r hr Tρ Tr H G hGbound htime_holder
  calc
    _ = (∫⁻ s in Tr, ENNReal.ofReal (G s) ^
        (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
      congr 1
      apply lintegral_congr
      intro s
      rw [Real.enorm_eq_ofReal (by dsimp [G]; positivity)]
    _ ≤ (ENNReal.ofReal r) ^ (2 * (2 / 3 - 1 / q : ℝ)) *
        eLpNorm' G q (volume.restrict Tρ) := by
      simpa [Tr, Tρ] using htime_holder
    _ = ENNReal.ofReal (r ^ (2 * (2 / 3 - 1 / q : ℝ))) *
        eLpNorm' G q (volume.restrict Tρ) := by
      rw [ENNReal.ofReal_rpow_of_pos hr]
    _ ≤ _ := by
      gcongr

private lemma pressureP8_bound_hpoint_2 :
    ∀ {q : ℝ} {_ : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ r : ℝ}
      (hρ : (0 : ℝ) < ρ),
      (0 : ℝ) < r →
        r ≤ ρ / (2 : ℝ) →
          let Bρ : Set Vec3 := vec3Ball z.1 ρ;
          let Br : Set Vec3 := vec3Ball z.1 r;
          let Tρ : Set ℝ := Ioc (z.2 - ρ ^ (2 : ℕ)) z.2;
          let F : Vec3 × ℝ → ℝ := fun (w : Vec3 × ℝ) => vec3EuclideanNorm (f w);
          let H : ℝ → ℝ≥0∞ := fun (s : ℝ) => ∫⁻ (x : Vec3) in Bρ, ENNReal.ofReal (F (x, s) ^ q);
          let G : ℝ → ℝ := fun (s : ℝ) => (H s).toReal ^ ((1 : ℝ) / q);
          let A : ℝ :=
            (6 : ℝ) * cutoffGradientConstant *
              (Real.pi * (4 : ℝ) / (3 : ℝ)) ^ ((1 : ℝ) - (1 : ℝ) / q);
          let K : ℝ := A * ρ ^ ((1 : ℝ) - (3 : ℝ) / q);
          (5 / 2 : ℝ) < q →
            (0 : ℝ) < q →
              AEStronglyMeasurable f ((volume.restrict Bρ).prod (volume.restrict Tρ)) →
                (∀ᵐ (s : ℝ) ∂volume.restrict Tρ, H s < ∞) →
                  (0 : ℝ) ≤ cutoffGradientConstant →
                    ∀ᵐ (s : ℝ) ∂volume.restrict Tρ,
                      ∀ x ∈ Br, |pressureP8 (mollifiedBallCutoff z.1 hρ) f s x| ≤ K * G s
    := by
  intro q p f z ρ r hρ hr hhalf Bρ Br Tρ F H G A K hq hqpos hfBT hHs hC
  have hfm := hfBT.prodMk_right
  filter_upwards [hfm, hHs] with s hms hHs'
  let _ : IsFiniteMeasure (volume.restrict Bρ) := by
    refine ⟨?_⟩
    simpa only [Measure.restrict_apply_univ] using
      (volume_vec3Ball_lt_top (x := z.1) (r := ρ))
  have hFmeas : AEStronglyMeasurable (fun y : Vec3 => F (y, s))
      (volume.restrict Bρ) := by
    have hc : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
      unfold vec3EuclideanNorm
      fun_prop
    exact hc.comp_aestronglyMeasurable hms
  have hFnonneg : ∀ y : Vec3, 0 ≤ F (y, s) := by
    intro y
    dsimp [F]
    exact vec3EuclideanNorm_nonneg _
  have hFqmeas : AEStronglyMeasurable
      (fun y : Vec3 => F (y, s) ^ q) (volume.restrict Bρ) :=
    (Real.continuous_rpow_const hqpos.le).comp_aestronglyMeasurable hFmeas
  have hFq : Integrable (fun y : Vec3 => F (y, s) ^ q)
      (volume.restrict Bρ) := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      hFqmeas (Eventually.of_forall fun y => Real.rpow_nonneg
        (hFnonneg y) _)).mp
    simpa [H] using (ne_of_lt hHs')
  have hFmem : MemLp (fun y : Vec3 => F (y, s))
      (ENNReal.ofReal q) (volume.restrict Bρ) := by
    apply (integrable_norm_rpow_iff hFmeas (by positivity) (by simp)).mp
    simpa only [ENNReal.toReal_ofReal hqpos.le, Real.norm_eq_abs,
      abs_of_nonneg (hFnonneg _)] using hFq
  have hOne : MemLp (fun _ : Vec3 => (1 : ℝ))
      (ENNReal.ofReal (q / (q - 1))) (volume.restrict Bρ) := by
    exact memLp_const 1
  have hqone : 1 < q := by linarith only [hq]
  have hconj : q.HolderConjugate (q / (q - 1)) := by
    rw [Real.holderConjugate_iff]
    constructor
    · exact hqone
    · field_simp [hqpos.ne', (sub_pos.mpr hqone).ne']
      ring_nf
  have hsp := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict Bρ) hconj
    (Eventually.of_forall fun y => hFnonneg y)
    (Eventually.of_forall fun _ => by norm_num) hFmem hOne
  have hconv : ENNReal.ofReal (∫ y in Bρ, F (y, s) ^ q) = H s := by
    have hconv := ofReal_integral_eq_lintegral_ofReal hFq
      (Eventually.of_forall fun y => Real.rpow_nonneg (hFnonneg y) _)
    simpa [H] using hconv
  have hqint : (∫ y in Bρ, F (y, s) ^ q) = (H s).toReal := by
    have hnonnegint : 0 ≤ ∫ y in Bρ, F (y, s) ^ q :=
      integral_nonneg_of_ae (Eventually.of_forall fun y =>
        Real.rpow_nonneg (hFnonneg y) _)
    rw [← hconv, ENNReal.toReal_ofReal hnonnegint]
  have hvol : (volume Bρ).toReal =
      (Real.pi * 4 / 3) * ρ ^ (3 : ℕ) := by
    rw [pressure_volume_ball (x₀ := z.1) hρ,
      ENNReal.toReal_ofReal (by positivity)]
    congr 1
    ring_nf
  have hsp' : ∫ y in Bρ, F (y, s) ≤
      ((Real.pi * 4 / 3) ^ (1 - 1 / q : ℝ) *
        ρ ^ (3 - 3 / q : ℝ)) * G s := by
    calc
      _ = ∫ y in Bρ, F (y, s) * 1 := by simp
      _ ≤ (∫ y in Bρ, F (y, s) ^ q) ^ (1 / q) *
          (∫ y in Bρ, (1 : ℝ) ^ (q / (q - 1))) ^
            (1 / (q / (q - 1))) := hsp
      _ = ((Real.pi * 4 / 3) ^ (1 - 1 / q : ℝ) *
          ρ ^ (3 - 3 / q : ℝ)) * G s := by
        rw [hqint]
        rw [show (∫ y in Bρ, (1 : ℝ) ^ (q / (q - 1))) =
          (volume Bρ).toReal by
            simp [Measure.real]]
        rw [hvol]
        dsimp [G]
        rw [show 1 / (q / (q - 1)) = 1 - 1 / q by
          field_simp [hqpos.ne']]
        rw [Real.mul_rpow (by positivity) (by positivity)]
        rw [show (ρ ^ (3 : ℕ) : ℝ) = ρ ^ (3 : ℝ) by norm_num]
        rw [← Real.rpow_mul hρ.le]
        norm_num
        ring_nf
  have hfB : Integrable (fun y : Vec3 => F (y, s))
      (volume.restrict Bρ) := by
    have h := integrable_norm_rpow_of_le hFmeas (p := (1 : ℝ))
      (q := q) (by norm_num) hqpos.le (by linarith only [hq])
      (by simpa only [Real.norm_eq_abs, abs_of_nonneg (hFnonneg _),
        Real.rpow_one] using hFq)
    convert h using 1
    funext y
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnonneg y), Real.rpow_one]
  have hfixed := pressureP8_fixed_bound hρ hr hhalf hfB hms
    (hηeq := rfl) (mollifiedBallCutoff_smooth z.1 hρ)
    (mollifiedBallCutoff_hasCompactSupport z.1 hρ)
    (pressure_cutoff_support_subset_ball z.1 hρ)
  intro x hx
  calc
    _ ≤ (6 * cutoffGradientConstant) / ρ ^ 2 *
        (∫ y in Bρ, F (y, s)) := hfixed x hx
    _ ≤ K * G s := by
      rw [show K * G s =
        (6 * cutoffGradientConstant) / ρ ^ 2 *
          ((Real.pi * 4 / 3) ^ (1 - 1 / q : ℝ) *
            ρ ^ (3 - 3 / q : ℝ) * G s) by
        dsimp [K, A]
        field_simp [ne_of_gt hρ]
        calc
          _ = cutoffGradientConstant * G s *
              (ρ ^ ((q - 3) / q) * ρ ^ (2 : ℕ)) := by ring
          _ = cutoffGradientConstant * G s *
              ρ ^ (3 * (q - 1) / q) := by
            rw [← Real.rpow_two, ← Real.rpow_add hρ]
            congr 2
            field_simp [hqpos.ne']
            ring_nf]
      exact mul_le_mul_of_nonneg_left hsp'
        (by positivity)

private lemma pressureP8_bound_hP8_3 :
    ∀ {q : ℝ} {f : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ r : ℝ} (hρ : (0 : ℝ) < ρ),
      let Br : Set Vec3 := vec3Ball z.1 r;
      let Tr : Set ℝ := Ioc (z.2 - r ^ (2 : ℕ)) z.2;
      ∀ (H : ℝ → ℝ≥0∞),
        let G : ℝ → ℝ := fun (s : ℝ) => (H s).toReal ^ ((1 : ℝ) / q);
        ∀ (K : ℝ) (J : Set ℝ),
          Ioc (z.2 - ρ ^ (2 : ℕ)) z.2 ⊆ J →
            (0 : ℝ) ≤ K →
              (∀ᵐ (x : ℝ) ∂volume.restrict Tr,
                  ∀ x_1 ∈ Br, |pressureP8 (mollifiedBallCutoff z.1 hρ) f x x_1| ≤ K * G x) →
                ∀ᵐ (w : ParabolicPoint) ∂volume.restrict (parabolicCylinder z.1 z.2 r),
                  ‖pressureP8 (mollifiedBallCutoff z.1 hρ) f w.2 w.1‖ₑ ≤ ENNReal.ofReal K * ‖G w.2‖ₑ
    := by
  intro q f z ρ r hρ Br Tr H G K J htime hK hpointTr
  have htime : ∀ᵐ s ∂volume.restrict Tr, ∀ x ∈ Br,
      |pressureP8 (mollifiedBallCutoff z.1 hρ) f s x| ≤ K * G s := by
    filter_upwards [hpointTr] with s hs x hx
    exact hs x hx
  have hlift := pressure_lift_time_ae (B := Br) (T := Tr) htime
  have hsubc : parabolicCylinder z.1 z.2 r ⊆ Br ×ˢ Tr := by
    intro w hw
    rw [parabolicCylinder] at hw
    exact hw
  have hc := ae_restrict_of_ae_restrict_of_subset hsubc hlift
  have hmem := ae_restrict_mem (μ := volume) (show MeasurableSet
      (parabolicCylinder z.1 z.2 r) from by
    change MeasurableSet (vec3Ball z.1 r ×ˢ Ioc (z.2 - r ^ 2) z.2)
    exact (vec3Ball_measurable z.1 r).prod measurableSet_Ioc)
  filter_upwards [hc, hmem] with w hw hwm
  change w ∈ vec3Ball z.1 r ×ˢ Ioc (z.2 - r ^ 2) z.2 at hwm
  have habs := hw w.1 hwm.1
  have hGpos : 0 ≤ G w.2 := by dsimp [G]; positivity
  simpa only [Real.enorm_eq_ofReal_abs, abs_of_nonneg hGpos,
    ENNReal.ofReal_mul hK] using ENNReal.ofReal_le_ofReal habs

private lemma pressureP8_bound_hscale_4 :
    ∀ {q : ℝ} {f : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ r : ℝ},
      (0 : ℝ) < ρ →
        (0 : ℝ) < r →
          let Br : Set Vec3 := vec3Ball z.1 r;
          let Tr : Set ℝ := Ioc (z.2 - r ^ (2 : ℕ)) z.2;
          ∀ (G : ℝ → ℝ),
            let A : ℝ :=
              (6 : ℝ) * cutoffGradientConstant *
                (Real.pi * (4 : ℝ) / (3 : ℝ)) ^ ((1 : ℝ) - (1 : ℝ) / q);
            ∀ (K : ℝ),
              (0 : ℝ) ≤ A →
                ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
                      (ENNReal.ofReal K ^ (3 / 2 : ℝ) * (volume : Set Vec3 → ℝ≥0∞) Br *
                          ∫⁻ (s : ℝ) in Tr, ‖G s‖ₑ ^ (3 / 2 : ℝ)) ^
                        (2 / 3 : ℝ) ≤
                    ENNReal.ofReal
                      (A * ((4 : ℝ) * Real.pi / (3 : ℝ)) ^ (2 / 3 : ℝ) *
                            r ^ ((2 : ℝ) - (2 : ℝ) / q) *
                          ρ ^ ((-2 : ℝ) + (2 : ℝ) / q) *
                        lambda q f z ρ) →
                  (0 : ℝ) ≤ r / ρ →
                    (r / ρ) ^ ((2 : ℝ) - (2 : ℝ) / q) ≤ r / ρ →
                      ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
                          (ENNReal.ofReal K ^ (3 / 2 : ℝ) * (volume : Set Vec3 → ℝ≥0∞) Br *
                              ∫⁻ (s : ℝ) in Tr, ‖G s‖ₑ ^ (3 / 2 : ℝ)) ^
                            (2 / 3 : ℝ) ≤
                        ENNReal.ofReal (pressureP13Constant q * (r / ρ) * lambda q f z ρ)
    := by
  intro q f z ρ r hρ hr Br Tr G A K hA hscale0 hκ hpowκ
  have hconst : A * (4 * Real.pi / 3) ^ (2 / 3 : ℝ) =
      pressureP13Constant q := by
    dsimp [A, pressureP13Constant]
    congr 2
    ring_nf
  have htarget : 0 ≤ pressureP13Constant q * (r / ρ) *
      lambda q f z ρ := by
    rw [← hconst]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hA (by positivity)) hκ)
      (by unfold lambda; positivity)
  have hle : A * (4 * Real.pi / 3) ^ (2 / 3 : ℝ) *
      (r / ρ) ^ (2 - 2 / q : ℝ) * lambda q f z ρ ≤
      pressureP13Constant q * (r / ρ) * lambda q f z ρ := by
    have hAnonneg : 0 ≤ 6 * cutoffGradientConstant *
        (4 * Real.pi / 3) ^ (1 - 1 / q : ℝ) := by
      have hpi : Real.pi * 4 / 3 = 4 * Real.pi / 3 := by ring_nf
      simpa [A, hpi] using hA
    rw [hconst]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpowκ
        (mul_nonneg hAnonneg (by positivity)))
      (by unfold lambda; positivity)
  have hpowscale : r ^ (2 - 2 / q : ℝ) * ρ ^ (-2 + 2 / q : ℝ) =
      (r / ρ) ^ (2 - 2 / q : ℝ) := by
    calc
      r ^ (2 - 2 / q : ℝ) * ρ ^ (-2 + 2 / q : ℝ) =
          r ^ (2 - 2 / q : ℝ) * ρ ^ (-(2 - 2 / q : ℝ)) := by
            congr 2
            ring_nf
      _ = r ^ (2 - 2 / q : ℝ) *
          (ρ ^ (2 - 2 / q : ℝ))⁻¹ := by
            rw [Real.rpow_neg hρ.le]
      _ = r ^ (2 - 2 / q : ℝ) / ρ ^ (2 - 2 / q : ℝ) := by
            simp only [div_eq_mul_inv]
      _ = (r / ρ) ^ (2 - 2 / q : ℝ) := by
            rw [Real.div_rpow hr.le hρ.le]
  have hle' : A * (4 * Real.pi / 3) ^ (2 / 3 : ℝ) *
      r ^ (2 - 2 / q : ℝ) * ρ ^ (-2 + 2 / q : ℝ) *
        lambda q f z ρ ≤
      pressureP13Constant q * (r / ρ) * lambda q f z ρ := by
    calc
      _ = A * (4 * Real.pi / 3) ^ (2 / 3 : ℝ) *
          (r / ρ) ^ (2 - 2 / q : ℝ) * lambda q f z ρ := by
        rw [← hpowscale]
        ring_nf
      _ ≤ _ := hle
  exact hscale0.trans (ENNReal.ofReal_le_ofReal hle')

theorem pressureP8_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hhalf : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        eLpNorm' (fun w : ParabolicPoint =>
          pressureP8 (mollifiedBallCutoff z.1 hρ) f w.2 w.1) (3 / 2 : ℝ)
          (volume.restrict (parabolicCylinder z.1 z.2 r)) ≤
      ENNReal.ofReal (pressureP13Constant q * (r / ρ) *
        (lambda q f z ρ)) := by
  let Bρ : Set Vec3 := vec3Ball z.1 ρ
  let Br : Set Vec3 := vec3Ball z.1 r
  let Tρ : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2
  let Tr : Set ℝ := Ioc (z.2 - r ^ 2) z.2
  let F : Vec3 × ℝ → ℝ := fun w => vec3EuclideanNorm (f w)
  let H : ℝ → ℝ≥0∞ := fun s =>
    ∫⁻ x in Bρ, ENNReal.ofReal ((F (x, s)) ^ q)
  let G : ℝ → ℝ := fun s => (H s).toReal ^ (1 / q : ℝ)
  let A : ℝ := 6 * cutoffGradientConstant *
    (Real.pi * 4 / 3) ^ (1 - 1 / q : ℝ)
  let K : ℝ := A * ρ ^ (1 - 3 / q : ℝ)
  obtain ⟨Ω', J, hbox, hball, htime⟩ :=
    pressure_box_geometry hsol hρ hsub
  have hdata := hsol.2.2.2.2.2.1 Ω' J hbox
  have hq : 5 / 2 < q := hsol.2.2.2.1
  have hqpos : 0 < q := lt_trans (by norm_num) hq
  have hfglobal : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet Ω' J)) := hdata.2.2.2.1
  have hfprod : AEStronglyMeasurable f
      ((volume.restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    exact hfglobal
  have hfBT : AEStronglyMeasurable f
      ((volume.restrict Bρ).prod (volume.restrict Tρ)) :=
    hfprod.mono_measure (Measure.prod_mono
      (Measure.restrict_mono_set volume hball)
      (Measure.restrict_mono_set volume htime))
  have hFglobal : AEStronglyMeasurable
      (fun w : ParabolicPoint => vec3EuclideanNorm (f w))
      (volume.restrict (spaceTimeSet Ω' J)) := by
    have hc : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
      unfold vec3EuclideanNorm
      fun_prop
    exact hc.comp_aestronglyMeasurable hfglobal
  have hFpowglobal : AEStronglyMeasurable
      (fun w : ParabolicPoint => (vec3EuclideanNorm (f w)) ^ q)
      (volume.restrict (spaceTimeSet Ω' J)) := by
    exact (Real.continuous_rpow_const hqpos.le).comp_aestronglyMeasurable
      hFglobal
  have hFpowprod : AEStronglyMeasurable
      (fun w : Vec3 × ℝ => (vec3EuclideanNorm (f w)) ^ q)
      ((volume.restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    exact hFpowglobal
  have hFpowBT' := hFpowprod.mono_measure (Measure.prod_mono
      (Measure.restrict_mono_set volume hball)
      (Measure.restrict_mono_set volume htime))
  have hFpowBT : AEMeasurable
      (fun w : Vec3 × ℝ => (F w) ^ q)
      ((volume.restrict Bρ).prod (volume.restrict Tρ)) := by
    simpa [F] using hFpowBT'.aemeasurable
  have hHae : AEMeasurable H (volume.restrict Tρ) := by
    have h := hFpowBT.ennreal_ofReal.lintegral_prod_left'
      (μ := volume.restrict Bρ) (ν := volume.restrict Tρ)
    simpa [H, F] using h
  have hswap := pressure_prod_lintegral_swap (B := Bρ) (T := Tρ)
    (F := fun w => (F w) ^ q) hFpowBT
  have htotal : (∫⁻ s in Tρ, H s) =
      ∫⁻ w in parabolicCylinder z.1 z.2 ρ,
        ENNReal.ofReal ((vec3EuclideanNorm (f w)) ^ q) := by
    change (∫⁻ s in Tρ, ∫⁻ x in Bρ,
      ENNReal.ofReal ((F (x, s)) ^ q)) = _
    calc
      _ = ∫⁻ w in Bρ ×ˢ Tρ, ENNReal.ofReal ((F w) ^ q) := hswap.symm
      _ = ∫⁻ w in parabolicCylinder z.1 z.2 ρ,
          ENNReal.ofReal ((vec3EuclideanNorm (f w)) ^ q) := by
        rw [parabolicCylinder, MeasureTheory.Measure.volume_eq_prod Vec3 ℝ,
          volume_parabolicPoint_eq_prod]
        rfl
  have hforce := sws_lintegral_vec3EuclideanNorm_pow_eq_ofReal_lambda_pow
    hsol z hρ hsub
  have htotal' : (∫⁻ s in Tρ, H s) =
      ∫⁻ w in parabolicCylinder z.1 z.2 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q := by
    rw [htotal]
    apply lintegral_congr
    intro w
    rw [ENNReal.ofReal_rpow_of_nonneg
      (vec3EuclideanNorm_nonneg (f w)) hqpos.le]
  have hHglobal : (∫⁻ s in Tρ, H s) ≤
      ENNReal.ofReal ((ρ ^ (5 / q - 3) * lambda q f z ρ) ^ q) := by
    rw [htotal', hforce]
  have hHtop : (∫⁻ s in Tρ, H s) < ⊤ :=
    lt_of_le_of_lt hHglobal (ENNReal.ofReal_lt_top)
  have hHs : ∀ᵐ s ∂volume.restrict Tρ, H s < ⊤ :=
    ae_lt_top' hHae (ne_of_lt hHtop)
  have hGmeas : AEStronglyMeasurable G (volume.restrict Tρ) := by
    have hreal : AEMeasurable (fun s => (H s).toReal)
        (volume.restrict Tρ) := hHae.ennreal_toReal
    have hc : Continuous (fun x : ℝ => x ^ (1 / q : ℝ)) :=
      Real.continuous_rpow_const (by positivity)
    simpa [Function.comp_def, G] using
      (hc.measurable.comp_aemeasurable hreal).aestronglyMeasurable
  have hGnonneg : 0 ≤ᵐ[volume.restrict Tρ] G :=
    Eventually.of_forall (fun s => Real.rpow_nonneg ENNReal.toReal_nonneg _)
  have hAforce : 0 ≤ ρ ^ (5 / q - 3) * lambda q f z ρ := by
    exact mul_nonneg (Real.rpow_nonneg hρ.le _) (by unfold lambda; positivity)
  have hGbound : eLpNorm' G q (volume.restrict Tρ) ≤
      ENNReal.ofReal (ρ ^ (5 / q - 3) * lambda q f z ρ) := by
    exact force_time_norm_bound hqpos hAforce hHs hHglobal
  have htime_holder := time_holder_q (t₀ := z.2) (r := r) (ρ := ρ) (q := q)
    hr hhalf (by linarith only [hq]) (g := G) hGmeas hGnonneg
  have hX := @pressureP8_bound_hX_1 q f z ρ r hr H hGbound htime_holder
  have hC : 0 ≤ cutoffGradientConstant :=
    (pressure_cutoff_constants_nonneg (x₀ := z.1) hρ).1
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hpoint := @pressureP8_bound_hpoint_2 q p f z ρ r hρ hr hhalf hq hqpos hfBT hHs hC
  have hTr : Tr ⊆ Tρ := by
    intro s hs
    have hρ0 : 0 ≤ ρ := by
      have : 0 ≤ ρ / 2 := le_of_lt (lt_of_lt_of_le hr hhalf)
      linarith only [this]
    have hsq : r ^ 2 ≤ ρ ^ 2 := by
      apply (sq_le_sq₀ hr.le hρ0).2
      linarith only [hhalf, hρ0]
    exact ⟨by linarith only [hs.1, hsq], hs.2⟩
  have hpointTr := ae_restrict_of_ae_restrict_of_subset hTr hpoint
  have hP8 := @pressureP8_bound_hP8_3 q f z ρ r hρ H K J htime hK hpointTr
  have hGr : AEStronglyMeasurable G (volume.restrict Tr) :=
    hGmeas.mono_measure (Measure.restrict_mono_set volume hTr)
  have hscale0 := pressureP8_scale (q := q) (A := A) (K := K) (V := Br)
    (X := ∫⁻ s in Tr, ‖G s‖ₑ ^ (3 / 2 : ℝ)) hr hρ hA
    (by rfl) hX (pressure_volume_ball hr)
  have hqone : 1 ≤ q := by linarith only [hq]
  have hκ : 0 ≤ r / ρ := by positivity
  have hκle : r / ρ ≤ 1 := by
    exact (div_le_iff₀ hρ).2 (by linarith only [hhalf, hρ])
  have hpowκ : (r / ρ) ^ (2 - 2 / q : ℝ) ≤ r / ρ := by
    have hqexp : 1 ≤ 2 - 2 / q := by
      have hq2 : 2 ≤ q := by linarith only [hq]
      have hquot : 0 ≤ (q - 2) / q :=
        div_nonneg (sub_nonneg.mpr hq2) hqpos.le
      have heq : (2 - 2 / q : ℝ) - 1 = (q - 2) / q := by
        field_simp [hqpos.ne']
        ring_nf
      apply sub_nonneg.mp
      rw [heq]
      exact hquot
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge (x := r / ρ)
        (y := 2 - 2 / q) (z := 1) (div_pos hr hρ) hκle hqexp)
  have hscale := @pressureP8_bound_hscale_4 q f z ρ r hρ hr G K hA hscale0 hκ hpowκ
  exact pressureP8_cylinder_bound (η := mollifiedBallCutoff z.1 hρ)
    (f := f) (x₀ := z.1) (t₀ := z.2) (r := r) (ρ := ρ) (K := K)
    (C₁₃ := pressureP13Constant q) (lam := lambda q f z ρ)
    hρ hr hhalf hK hGr hP8 (by simpa [Bρ, Br, Tr] using hscale)

end CKN
