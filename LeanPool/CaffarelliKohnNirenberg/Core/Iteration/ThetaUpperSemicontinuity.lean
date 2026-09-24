/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Iteration.UpperSemicontinuity
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SliceIntegrability
public import LeanPool.CaffarelliKohnNirenberg.Setting.SliceNormBounds
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Cylinders
public import Mathlib.MeasureTheory.Measure.ContinuousPreimage
public import Mathlib.MeasureTheory.Group.Prod
public import LeanPool.CaffarelliKohnNirenberg.Core.Iteration.ThetaUpperSemicontinuityBasic
public import LeanPool.CaffarelliKohnNirenberg.Core.Iteration.ThetaUpperSemicontinuityAlpha

/-!
# Theta Upper Semicontinuity

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration


noncomputable section

namespace CKN


private lemma theta_usc_hsubAt_1 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z₀ : ParabolicPoint} {R : ℝ},
          euclideanClosedBall z₀.1 R ×ˢ Icc (z₀.2 - R ^ (2 : ℕ)) z₀.2 ⊆ spaceTimeSet Ω I →
            z₀.2 ∈ I →
              (0 : ℝ) < R →
                ∀ (h₁ : ℝ),
                  z₀.2 + h₁ ∈ I →
                    ∀ {h : ℝ},
                      (0 : ℝ) ≤ h →
                        h ≤ h₁ → closure (parabolicCylinder z₀.1 (z₀.2 + h) R) ⊆ spaceTimeSet Ω I
    := by
  intro Ω I q u Du p f hsol z₀ R hrect ht₀ hR h₁ ht₁I h hh hhh
  rw [closure_parabolicCylinder hR]
  intro z hz
  have hlow : z₀.2 - R ^ 2 ≤ z₀.2 + h - R ^ 2 := by linarith only [hh]
  have hupperI : z₀.2 + h ∈ I := by
    apply hsol.2.2.1.out ht₀ ht₁I
    exact ⟨le_add_of_nonneg_right hh, add_le_add_right hhh _⟩
  have htime : z.2 ∈ I := by
    rcases le_total z.2 z₀.2 with hleft | hright
    · exact (hrect ⟨mem_euclideanClosedBall_of_vec3Norm_le hR.le
        hz.1, ⟨by linarith only [hz.2.1, hh], hleft⟩⟩).2
    · exact hsol.2.2.1.out ht₀ hupperI ⟨hright, hz.2.2⟩
  have hspace : z.1 ∈ Ω := by
    have hz0 : (z.1, z₀.2) ∈
      euclideanClosedBall z₀.1 R ×ˢ Icc (z₀.2 - R ^ 2) z₀.2 := by
      exact ⟨mem_euclideanClosedBall_of_vec3Norm_le hR.le hz.1,
        ⟨sub_le_self _ (sq_nonneg R), le_rfl⟩⟩
    exact (hrect hz0).1
  exact ⟨hspace, htime⟩

private lemma theta_usc_hpIntO_2 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z₀ : ParabolicPoint} {R : ℝ},
          (0 : ℝ) < R →
            ∀ (h₁ : ℝ),
              (0 : ℝ) < h₁ →
                (∀ {h : ℝ},
                    (0 : ℝ) ≤ h →
                      h ≤ h₁ → closure (parabolicCylinder z₀.1 (z₀.2 + h) R) ⊆ spaceTimeSet Ω I) →
                  ∀ (Ωo : Set Vec3) (Jo : Set ℝ),
                    let Wold : Set ParabolicPoint :=
                      vec3Ball z₀.1 R ×ˢ Ioo (z₀.2 - R ^ (2 : ℕ)) z₀.2;
                    Wold ⊆ parabolicCylinder z₀.1 z₀.2 R →
                      Wold ⊆ spaceTimeSet Ωo Jo →
                        AEStronglyMeasurable (fun (w : ParabolicPoint) => |p w| ^ (3 / 2 : ℝ))
                            (volume.restrict (spaceTimeSet Ωo Jo)) →
                          IntegrableOn (fun (w : ParabolicPoint) => |p w| ^ (3 / 2 : ℝ)) Wold volume
    := by
  intro Ω I q u Du p f hsol z₀ R hR h₁ hh₁ hsubAt Ωo Jo Wold hWoldcyl hWoldbox hpmeasO
  apply pressure_integrable_of_meas hpmeasO hWoldbox
  have htop := sws_pressure_integral_lt_top hsol hR (by
    simpa only [add_zero] using
      (hsubAt (h := 0) (by norm_num) hh₁.le))
  have hcongr : (∫⁻ w in parabolicCylinder z₀.1 z₀.2 R,
      ENNReal.ofReal (|p w| ^ (3 / 2 : ℝ))) =
      ∫⁻ w in parabolicCylinder z₀.1 z₀.2 R,
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) :=
    lintegral_congr (fun w =>
      (ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (p w))
        (by norm_num : (0 : ℝ) ≤ 3 / 2)).symm)
  rw [← hcongr] at htop
  exact (ne_of_lt (lt_of_le_of_lt (lintegral_mono_set hWoldcyl)
    htop))

private lemma theta_usc_hpIntF_3 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z₀ : ParabolicPoint} {R : ℝ},
          (0 : ℝ) < R →
            ∀ (h₁ : ℝ),
              (0 : ℝ) < h₁ →
                (∀ {h : ℝ},
                    (0 : ℝ) ≤ h →
                      h ≤ h₁ → closure (parabolicCylinder z₀.1 (z₀.2 + h) R) ⊆ spaceTimeSet Ω I) →
                  ∀ (Ωf : Set Vec3) (Jf : Set ℝ),
                    let Wfuture : Set ParabolicPoint :=
                      vec3Ball z₀.1 R ×ˢ Ioo (z₀.2 + h₁ - R ^ (2 : ℕ)) (z₀.2 + h₁);
                    Wfuture ⊆ parabolicCylinder z₀.1 (z₀.2 + h₁) R →
                      Wfuture ⊆ spaceTimeSet Ωf Jf →
                        AEStronglyMeasurable (fun (w : ParabolicPoint) => |p w| ^ (3 / 2 : ℝ))
                            (volume.restrict (spaceTimeSet Ωf Jf)) →
                          IntegrableOn (fun (w : ParabolicPoint) => |p w| ^ (3 / 2 : ℝ)) Wfuture
                            volume
    := by
  intro Ω I q u Du p f hsol z₀ R hR h₁ hh₁ hsubAt Ωf Jf Wfuture hWfuturecyl hWfuturebox hpmeasF
  apply pressure_integrable_of_meas hpmeasF hWfuturebox
  have hsubf : closure (parabolicCylinder z₀.1 (z₀.2 + h₁) R) ⊆
      spaceTimeSet Ω I := hsubAt (h := h₁) hh₁.le le_rfl
  have htop := sws_pressure_integral_lt_top hsol
    (z := (z₀.1, z₀.2 + h₁)) hR hsubf
  have hcongr : (∫⁻ w in parabolicCylinder z₀.1 (z₀.2 + h₁) R,
      ENNReal.ofReal (|p w| ^ (3 / 2 : ℝ))) =
      ∫⁻ w in parabolicCylinder z₀.1 (z₀.2 + h₁) R,
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) :=
    lintegral_congr (fun w =>
      (ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (p w))
        (by norm_num : (0 : ℝ) ≤ 3 / 2)).symm)
  rw [← hcongr] at htop
  have htop' : (∫⁻ w in parabolicCylinder z₀.1 (z₀.2 + h₁) R,
      ENNReal.ofReal (|p w| ^ (3 / 2 : ℝ))) < ⊤ := by
    simpa only [Prod.fst, Prod.snd] using htop
  exact (ne_of_lt (lt_of_le_of_lt (lintegral_mono_set hWfuturecyl)
    htop'))

private lemma theta_usc_hβrepr_4 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {z₀ : ParabolicPoint} {rho R : ℝ},
      (0 : ℝ) < rho →
        ∀ (h₁ : ℝ),
          let Wold : Set ParabolicPoint := vec3Ball z₀.1 R ×ˢ Ioo (z₀.2 - R ^ (2 : ℕ)) z₀.2;
          let Wfuture : Set ParabolicPoint :=
            vec3Ball z₀.1 R ×ˢ Ioo (z₀.2 + h₁ - R ^ (2 : ℕ)) (z₀.2 + h₁);
          let G : Set ParabolicPoint := Wold ∪ Wfuture;
          IntegrableOn (fun (w : ParabolicPoint) => spatialGradientSq u Du w) G volume →
            ∀ (z : ParabolicPoint),
              closure (parabolicCylinder z.1 z.2 rho) ⊆ spaceTimeSet Ω I →
                parabolicCylinder z.1 z.2 rho ⊆ G →
                  beta u Du z rho =
                    (rho⁻¹ *
                        ∫ (w : ParabolicPoint) in parabolicCylinder z.1 z.2 rho,
                          spatialGradientSq u Du w) ^
                      (1 / 2 : ℝ)
    := by
  intro Ω I u Du z₀ rho R hrho h₁ Wold Wfuture G hgradInt z hz hzg
  have hiG : Integrable (fun w => spatialGradientSq u Du w)
      (volume.restrict G) := hgradInt
  have hi := hiG.mono_measure (Measure.restrict_mono hzg le_rfl)
  have hreal := integral_spatialGradientSq_eq_beta_sq u Du z hrho hi
  have hscale : rho⁻¹ * ∫ w in parabolicCylinder z.1 z.2 rho,
      spatialGradientSq u Du w = beta u Du z rho ^ 2 := by
    rw [hreal]
    field_simp
  have hb : 0 ≤ beta u Du z rho := by unfold beta; positivity
  calc
    beta u Du z rho = (beta u Du z rho ^ 2) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_nonneg hb]
    _ = (rho⁻¹ * ∫ w in parabolicCylinder z.1 z.2 rho,
        spatialGradientSq u Du w) ^ (1 / 2 : ℝ) := by rw [hscale]

private lemma theta_usc_hδrepr_5 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {p : ParabolicPoint → ℝ} {z₀ : ParabolicPoint} {rho R : ℝ},
      (0 : ℝ) < rho →
        ∀ (h₁ : ℝ),
          let Wold : Set ParabolicPoint := vec3Ball z₀.1 R ×ˢ Ioo (z₀.2 - R ^ (2 : ℕ)) z₀.2;
          let Wfuture : Set ParabolicPoint :=
            vec3Ball z₀.1 R ×ˢ Ioo (z₀.2 + h₁ - R ^ (2 : ℕ)) (z₀.2 + h₁);
          let G : Set ParabolicPoint := Wold ∪ Wfuture;
          IntegrableOn (fun (w : ParabolicPoint) => |p w| ^ (3 / 2 : ℝ)) G volume →
            ∀ (z : ParabolicPoint),
              closure (parabolicCylinder z.1 z.2 rho) ⊆ spaceTimeSet Ω I →
                parabolicCylinder z.1 z.2 rho ⊆ G →
                  delta p z rho =
                    (rho ^ (-2 : ℝ) *
                        ∫ (w : ParabolicPoint) in parabolicCylinder z.1 z.2 rho,
                          |p w| ^ (3 / 2 : ℝ)) ^
                      (1 / 3 : ℝ)
    := by
  intro Ω I p z₀ rho R hrho h₁ Wold Wfuture G hpInt z hz hzg
  have hiG : Integrable (fun w => |p w| ^ (3 / 2 : ℝ))
      (volume.restrict G) := hpInt
  have hi := hiG.mono_measure (Measure.restrict_mono hzg le_rfl)
  have hreal := integral_abs_pow_eq_delta_cube p z hrho hi
  have hscale : rho ^ (-2 : ℝ) * ∫ w in parabolicCylinder z.1 z.2 rho,
      |p w| ^ (3 / 2 : ℝ) = delta p z rho ^ 3 := by
    rw [hreal]
    have hρ2 : rho ^ (2 : ℕ) = rho ^ (2 : ℝ) := by
      exact (Real.rpow_natCast rho 2).symm
    rw [hρ2]
    calc
      rho ^ (-2 : ℝ) * (rho ^ (2 : ℝ) * delta p z rho ^ 3) =
          (rho ^ (-2 : ℝ) * rho ^ (2 : ℝ)) * delta p z rho ^ 3 := by ring
      _ = delta p z rho ^ 3 := by
        rw [← Real.rpow_add hrho]
        norm_num
  have hd : 0 ≤ delta p z rho := by unfold delta; positivity
  calc
    delta p z rho = (delta p z rho ^ 3) ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hd]
      norm_num
    _ = (rho ^ (-2 : ℝ) * ∫ w in parabolicCylinder z.1 z.2 rho,
        |p w| ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ) := by rw [hscale]

private lemma theta_usc_hIntAt_6 :
    ∀ {u : ParabolicPoint → Vec3} {z₀ : ParabolicPoint} {R : ℝ},
      (0 : ℝ) < R →
        ∀ (r h₁ : ℝ),
          h₁ < R ^ (2 : ℕ) →
            ∀ (Ωo : Set Vec3) (Jo : Set ℝ) (Ωf : Set Vec3) (Jf : Set ℝ),
              parabolicCylinder z₀.1 (z₀.2 + h₁) R ⊆ spaceTimeSet Ωf Jf →
                parabolicCylinder z₀.1 z₀.2 R ⊆ spaceTimeSet Ωo Jo →
                  (∀ᵐ (s : ℝ) ∂volume.restrict Jo,
                      IntegrableOn (fun (y : Vec3) => vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ))
                        (vec3Ball z₀.1 r) volume) →
                    (∀ᵐ (s : ℝ) ∂volume.restrict Jf,
                        IntegrableOn (fun (y : Vec3) => vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ))
                          (vec3Ball z₀.1 r) volume) →
                      (∀ᵐ (s : ℝ) ∂volume.restrict Jo,
                          IntegrableOn (fun (y : Vec3) => vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ))
                            (vec3Ball z₀.1 R) volume) →
                        (∀ᵐ (s : ℝ) ∂volume.restrict Jf,
                            IntegrableOn (fun (y : Vec3) => vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ))
                              (vec3Ball z₀.1 R) volume) →
                          ∀ {h : ℝ},
                            (0 : ℝ) < h →
                              h ≤ h₁ →
                                ∀ᵐ (s : ℝ) ∂volume.restrict (Ioc (z₀.2 - R ^ (2 : ℕ)) (z₀.2 + h)),
                                  IntegrableOn
                                      (fun (y : Vec3) => vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ))
                                      (vec3Ball z₀.1 r) volume ∧
                                    IntegrableOn
                                      (fun (y : Vec3) => vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ))
                                      (vec3Ball z₀.1 R) volume
    := by
  intro u z₀ R hR r h₁ hh₁R Ωo Jo Ωf Jf hcf hco0 hvelrO hvelrF hvelRO hvelRF h hh hhh
  have hold : Ioc (z₀.2 - R ^ 2) z₀.2 ⊆ Jo := by
    intro s hs
    have hm : ((z₀.1, s) : ParabolicPoint) ∈
        parabolicCylinder z₀.1 z₀.2 R := by
      rw [parabolicCylinder]
      exact ⟨by rw [mem_vec3Ball]; simp [vec3EuclideanNorm_zero, hR], hs⟩
    exact (hco0 hm).2
  have hfuture : Ioc z₀.2 (z₀.2 + h) ⊆ Jf := by
    intro s hs
    have hm : ((z₀.1, s) : ParabolicPoint) ∈
        parabolicCylinder z₀.1 (z₀.2 + h₁) R := by
      rw [parabolicCylinder]
      exact ⟨by rw [mem_vec3Ball]; simp [vec3EuclideanNorm_zero, hR],
        ⟨by linarith only [hs.1, hh₁R], by linarith only [hs.2, hhh]⟩⟩
    exact (hcf hm).2
  have hu : Ioc (z₀.2 - R ^ 2) (z₀.2 + h) =
      Ioc (z₀.2 - R ^ 2) z₀.2 ∪ Ioc z₀.2 (z₀.2 + h) := by
    ext s
    constructor
    · intro hs
      by_cases hleft : s ≤ z₀.2
      · exact Or.inl ⟨hs.1, hleft⟩
      · exact Or.inr ⟨lt_of_not_ge hleft, hs.2⟩
    · rintro (hs | hs)
      · exact ⟨hs.1, le_trans hs.2 (by linarith only [hh.le])⟩
      · exact ⟨by nlinarith only [hs.1, hR], hs.2⟩
  rw [hu, ae_restrict_union_iff]
  exact ⟨ae_restrict_of_ae_restrict_of_subset hold hvelrO |>.and
      (ae_restrict_of_ae_restrict_of_subset hold hvelRO),
    ae_restrict_of_ae_restrict_of_subset hfuture hvelrF |>.and
      (ae_restrict_of_ae_restrict_of_subset hfuture hvelRF)⟩

private lemma theta_usc_hfiniteRAt_7 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z₀ : ParabolicPoint} {R : ℝ},
          euclideanClosedBall z₀.1 R ×ˢ Icc (z₀.2 - R ^ (2 : ℕ)) z₀.2 ⊆ spaceTimeSet Ω I →
            (0 : ℝ) < R →
              ∀ (r h₁ : ℝ),
                h₁ < R ^ (2 : ℕ) →
                  (∀ {h : ℝ},
                      (0 : ℝ) ≤ h →
                        h ≤ h₁ → closure (parabolicCylinder z₀.1 (z₀.2 + h) R) ⊆ spaceTimeSet Ω I) →
                    (∀ {h : ℝ},
                        (0 : ℝ) < h →
                          h ≤ h₁ →
                            ∀ᵐ (s : ℝ) ∂volume.restrict (Ioc (z₀.2 - R ^ (2 : ℕ)) (z₀.2 + h)),
                              IntegrableOn
                                  (fun (y : Vec3) => vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ))
                                  (vec3Ball z₀.1 r) volume ∧
                                IntegrableOn
                                  (fun (y : Vec3) => vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ))
                                  (vec3Ball z₀.1 R) volume) →
                      ∀ {h : ℝ},
                        (0 : ℝ) < h →
                          h ≤ h₁ →
                            essSup
                                (fun (s : ℝ) =>
                                  ENNReal.ofReal
                                    (∫ (y : Vec3) in vec3Ball z₀.1 R,
                                      vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ)))
                                (volume.restrict (Ioc (z₀.2 - R ^ (2 : ℕ)) (z₀.2 + h))) ≠
                              ∞
    := by
  intro Ω I q u Du p f hsol z₀ R hrect hR r h₁ hh₁R hsubAt hIntAt h hh hhh
  have hrectFull : euclideanClosedBall z₀.1 R ×ˢ
      Icc (z₀.2 - R ^ 2) (z₀.2 + h) ⊆ spaceTimeSet Ω I := by
    intro w hw
    by_cases hpast : w.2 ≤ z₀.2
    · apply hrect
      exact ⟨hw.1, ⟨hw.2.1, hpast⟩⟩
    · have hhl : h < R ^ 2 := lt_of_le_of_lt hhh hh₁R
      have hsub := hsubAt (h := h) (le_of_lt hh) hhh
      apply hsub
      rw [closure_parabolicCylinder hR]
      have heq :=
        (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR.le).1 hw.1
      have heq' : vec3EuclideanNorm (w.1 - z₀.1) ≤ R := by
        have hnorm : vecEuclideanNorm (w.1 - z₀.1) =
            vec3EuclideanNorm (w.1 - z₀.1) := by
          simp only [vecEuclideanNorm, vecNormSq, vecDot, Pi.sub_apply, vec3EuclideanNorm]
          apply congrArg Real.sqrt
          apply Finset.sum_congr rfl
          intro i hi
          ring
        rw [← hnorm]
        exact heq
      exact ⟨heq', ⟨by linarith only [lt_of_not_ge hpast, hhl], hw.2.2⟩⟩
  have hT := sws_timeSliceBallEnergy_essSup_lt_top hsol hR
    (by nlinarith only [hR, hh]) hrectFull
  have hEq : ∀ᵐ s ∂volume.restrict
        (Ioc (z₀.2 - R ^ 2) (z₀.2 + h)),
        timeSliceBallEnergy z₀.1 R s
            (fun w => vec3EuclideanNorm (u w)) =
          ENNReal.ofReal (∫ y in vec3Ball z₀.1 R,
            (vec3EuclideanNorm (u (y, s))) ^ 2) := by
    filter_upwards [hIntAt hh hhh] with s hs
    have hsR := hs.2
    exact (time_slice_energy_eq_ofReal hsR).symm
  rw [← essSup_congr_ae hEq]
  exact ne_of_lt hT

private lemma theta_usc_hfiniteSmallAt_8 :
    ∀ {u : ParabolicPoint → Vec3} {z₀ : ParabolicPoint} {R : ℝ},
      ∀ r < R,
        ∀ (h₁ : ℝ),
          (∀ {h : ℝ},
              (0 : ℝ) < h →
                h ≤ h₁ →
                  ∀ᵐ (s : ℝ) ∂volume.restrict (Ioc (z₀.2 - R ^ (2 : ℕ)) (z₀.2 + h)),
                    IntegrableOn (fun (y : Vec3) => vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ))
                        (vec3Ball z₀.1 r) volume ∧
                      IntegrableOn (fun (y : Vec3) => vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ))
                        (vec3Ball z₀.1 R) volume) →
            (∀ {h : ℝ},
                (0 : ℝ) < h →
                  h ≤ h₁ →
                    essSup
                        (fun (s : ℝ) =>
                          ENNReal.ofReal
                            (∫ (y : Vec3) in vec3Ball z₀.1 R,
                              vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ)))
                        (volume.restrict (Ioc (z₀.2 - R ^ (2 : ℕ)) (z₀.2 + h))) ≠
                      ∞) →
              ∀ {h : ℝ},
                (0 : ℝ) < h →
                  h ≤ h₁ →
                    essSup
                        (fun (x : ℝ) =>
                          timeSliceBallEnergy z₀.1 r x fun (w : ParabolicPoint) =>
                            vec3EuclideanNorm (u w))
                        (volume.restrict (Ioc (z₀.2 - R ^ (2 : ℕ)) (z₀.2 + h))) ≠
                      ∞
    := by
  intro u z₀ R r hrrR h₁ hIntAt hfiniteRAt h hh hhh
  have hIntAt' := hIntAt (h := h) hh hhh
  have hmono := essSup_mono_measure_and_ae
    (μ := volume.restrict (Ioc (z₀.2 - R ^ 2) (z₀.2 + h)))
    (ν := volume.restrict (Ioc (z₀.2 - R ^ 2) (z₀.2 + h))) le_rfl (by
      filter_upwards [hIntAt'] with s hs
      have hsub : vec3Ball z₀.1 r ⊆ vec3Ball z₀.1 R := by
        intro x hx
        rw [mem_vec3Ball] at hx ⊢
        exact lt_trans hx hrrR
      exact ENNReal.ofReal_le_ofReal (setIntegral_mono_set hs.2
        (Filter.Eventually.of_forall (fun x => sq_nonneg _))
        (Filter.Eventually.of_forall (fun x hx => hsub hx))))
  have hfiniteRealr := ne_of_lt (hmono.trans_lt
    (lt_top_iff_ne_top.mpr (hfiniteRAt hh hhh)))
  have hEqFixedr : ∀ᵐ s ∂volume.restrict
        (Ioc (z₀.2 - R ^ 2) (z₀.2 + h)),
        timeSliceBallEnergy z₀.1 r s
            (fun w => vec3EuclideanNorm (u w)) =
          ENNReal.ofReal (∫ x in vec3Ball z₀.1 r,
            (vec3EuclideanNorm (u (x, s))) ^ 2) := by
    filter_upwards [hIntAt'] with s hs
    exact (time_slice_energy_eq_ofReal hs.1).symm
  rw [essSup_congr_ae hEqFixedr]
  exact hfiniteRealr

private lemma theta_usc_htimeMap_9 :
    ∀ {z₀ : ParabolicPoint},
      Tendsto (fun (z : ParabolicPoint) => z.2 - z₀.2) (𝓝 z₀ ⊓ 𝓟 {z : ParabolicPoint | z.2 > z₀.2})
        (𝓝[>] (0 : ℝ))
    := by
  intro z₀
  apply tendsto_nhdsWithin_iff.2
  constructor
  · have ht0 : Tendsto (fun z : ParabolicPoint => z.2 - z₀.2)
        (𝓝 z₀) (𝓝 (0 : ℝ)) := by
      simpa only [sub_self] using
        ((continuous_snd_parabolicPoint.tendsto z₀).sub_const z₀.2)
    exact ht0.mono_left (show
      (𝓝 z₀ ⊓ 𝓟 {z : ParabolicPoint | z.2 > z₀.2}) ≤ 𝓝 z₀ from inf_le_left)
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact sub_pos.mpr hz

private lemma theta_uschAlphaEventually_10_hFyCond_1 :
    ∀ {z₀ : ParabolicPoint} {rho : ℝ} (F : ℝ → ℝ),
      Tendsto (fun (z : ParabolicPoint) => z.2 - z₀.2) (𝓝 z₀ ⊓ 𝓟 {z : ParabolicPoint | z.2 > z₀.2})
          (𝓝[>] (0 : ℝ)) →
        ∀ {y : ℝ},
          (∀ᶠ (h : ℝ) in 𝓝[>] (0 : ℝ), F h < rho * y) →
            ∀ᶠ (z : ParabolicPoint) in 𝓝 z₀, z.2 ≤ z₀.2 ∨ F (z.2 - z₀.2) < rho * y
    := by
  intro z₀ rho F htimeMap y hFy
  have he : ∀ᶠ z : ParabolicPoint in
      (𝓝 z₀ ⊓ 𝓟 {z : ParabolicPoint | z.2 > z₀.2}),
      F (z.2 - z₀.2) < rho * y := htimeMap.eventually hFy
  have he' : {z : ParabolicPoint | F (z.2 - z₀.2) < rho * y} ∈
      (𝓝 z₀ ⊓ 𝓟 {z : ParabolicPoint | z.2 > z₀.2}) := he
  have he'' : {z : ParabolicPoint |
      z.2 > z₀.2 → F (z.2 - z₀.2) < rho * y} ∈ 𝓝 z₀ :=
    (mem_inf_principal).mp he'
  filter_upwards [he''] with z hz
  by_cases hpast : z.2 ≤ z₀.2
  · exact Or.inl hpast
  · exact Or.inr (hz (lt_of_not_ge hpast))

private lemma theta_uschAlphaEventually_10_hballr_2 :
    ∀ {z₀ : ParabolicPoint} {rho : ℝ} (r : ℝ) (z : ParabolicPoint),
      z.1 ∈ vec3Ball z₀.1 (r - rho) → vec3Ball z.1 rho ⊆ vec3Ball z₀.1 r
    := by
  intro z₀ rho r z hzspace x hx
  rw [mem_vec3Ball] at hx ⊢
  calc
    vec3EuclideanNorm (x - z₀.1) =
        vec3EuclideanNorm ((x - z.1) + (z.1 - z₀.1)) := by
          congr 1
          ring
    _ ≤ vec3EuclideanNorm (x - z.1) +
          vec3EuclideanNorm (z.1 - z₀.1) := euclidean_triangle _ _
    _ < rho + (r - rho) := add_lt_add hx hzspace
    _ = r := by ring

private lemma theta_usc_hAlphaEventually_10 :
    ∀ {u : ParabolicPoint → Vec3} {z₀ : ParabolicPoint} {rho R : ℝ},
      (0 : ℝ) < rho →
        (0 : ℝ) < R →
          (0 : ℝ) < R ^ (2 : ℕ) - rho ^ (2 : ℕ) →
            ∀ r < R,
              essSup
                    (fun (x : ℝ) =>
                      timeSliceBallEnergy z₀.1 R x fun (w : ParabolicPoint) =>
                        vec3EuclideanNorm (u w))
                    (volume.restrict (Ioc (z₀.2 - R ^ (2 : ℕ)) z₀.2)) ≠
                  ∞ →
                ∀ (h₁ : ℝ) (Ωo : Set Vec3) (Jo : Set ℝ),
                  parabolicCylinder z₀.1 z₀.2 R ⊆ spaceTimeSet Ωo Jo →
                    let F : ℝ → ℝ := fun (h : ℝ) =>
                      (essSup
                          (fun (s : ℝ) =>
                            ENNReal.ofReal
                              (∫ (y : Vec3) in vec3Ball z₀.1 r,
                                vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ)))
                          (volume.restrict (Ioc (z₀.2 - R ^ (2 : ℕ)) (z₀.2 + h)))).toReal;
                    limsup F (𝓝[>] (0 : ℝ)) ≤
                        (essSup
                            (fun (x : ℝ) =>
                              timeSliceBallEnergy z₀.1 R x fun (w : ParabolicPoint) =>
                                vec3EuclideanNorm (u w))
                            (volume.restrict (Ioc (z₀.2 - R ^ (2 : ℕ)) z₀.2))).toReal →
                      IsCoboundedUnder (fun (x1 x2 : ℝ) => x1 ≤ x2) (𝓝[>] (0 : ℝ)) F →
                        (∀ᵐ (s : ℝ) ∂volume.restrict Jo,
                            IntegrableOn (fun (y : Vec3) => vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ))
                              (vec3Ball z₀.1 R) volume) →
                          (∀ {h : ℝ},
                              (0 : ℝ) < h →
                                h ≤ h₁ →
                                  ∀ᵐ (s : ℝ) ∂volume.restrict (Ioc (z₀.2 - R ^ (2 : ℕ)) (z₀.2 + h)),
                                    IntegrableOn
                                        (fun (y : Vec3) => vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ))
                                        (vec3Ball z₀.1 r) volume ∧
                                      IntegrableOn
                                        (fun (y : Vec3) => vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ))
                                        (vec3Ball z₀.1 R) volume) →
                            (∀ {h : ℝ},
                                (0 : ℝ) < h →
                                  h ≤ h₁ →
                                    essSup
                                        (fun (x : ℝ) =>
                                          timeSliceBallEnergy z₀.1 r x fun (w : ParabolicPoint) =>
                                            vec3EuclideanNorm (u w))
                                        (volume.restrict (Ioc (z₀.2 - R ^ (2 : ℕ)) (z₀.2 + h))) ≠
                                      ∞) →
                              IsBoundedUnder (fun (x1 x2 : ℝ) => x1 ≤ x2) (𝓝[>] (0 : ℝ)) F →
                                (∀ᵐ (s : ℝ) ∂volume.restrict (Ioc (z₀.2 - R ^ (2 : ℕ)) z₀.2),
                                    (timeSliceBallEnergy z₀.1 R s fun (w : ParabolicPoint) =>
                                        vec3EuclideanNorm (u w)) =
                                      ENNReal.ofReal
                                        (∫ (y : Vec3) in vec3Ball z₀.1 R,
                                          vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ))) →
                                  R / rho * alpha u z₀ R ^ (2 : ℕ) =
                                      rho⁻¹ *
                                        (essSup
                                            (fun (x : ℝ) =>
                                              timeSliceBallEnergy z₀.1 R x
                                                fun (w : ParabolicPoint) => vec3EuclideanNorm (u w))
                                            (volume.restrict
                                              (Ioc (z₀.2 - R ^ (2 : ℕ)) z₀.2))).toReal →
                                    (∀ᶠ (z : ParabolicPoint) in 𝓝 z₀,
                                        z.1 ∈ vec3Ball z₀.1 (r - rho)) →
                                      ∀ (τ : ℝ),
                                        (0 : ℝ) < τ →
                                          τ ≤ h₁ / (2 : ℝ) →
                                            τ ≤ (R ^ (2 : ℕ) - rho ^ (2 : ℕ)) / (2 : ℝ) →
                                              (∀ᶠ (z : ParabolicPoint) in 𝓝 z₀,
                                                  z.2 ∈ Ioo (z₀.2 - τ) (z₀.2 + τ)) →
                                                Tendsto (fun (z : ParabolicPoint) => z.2 - z₀.2)
                                                    (𝓝 z₀ ⊓ 𝓟 {z : ParabolicPoint | z.2 > z₀.2})
                                                    (𝓝[>] (0 : ℝ)) →
                                                  ∀ {y : ℝ},
                                                    R / rho * alpha u z₀ R ^ (2 : ℕ) < y →
                                                      ∀ᶠ (z : ParabolicPoint) in 𝓝 z₀,
                                                        alpha u z rho ^ (2 : ℕ) < y
    := by
  intro u z₀ rho R hrho hR hgap r hrrR hS0 h₁ Ωo Jo hco0 F hFusc hFco hvelRO hIntAt hfiniteSmallAt
    hFbound
    hEqOld htarget hspace τ hτ hτh₁ hτgap htime htimeMap y hy
  have hSlt :
      (essSup (timeSliceBallEnergy z₀.1 R ·
        (fun w => vec3EuclideanNorm (u w)))
        (volume.restrict (Ioc (z₀.2 - R ^ 2) z₀.2))).toReal < rho * y := by
    calc
      _ = rho * (rho⁻¹ *
          (essSup (timeSliceBallEnergy z₀.1 R ·
            (fun w => vec3EuclideanNorm (u w)))
            (volume.restrict (Ioc (z₀.2 - R ^ 2) z₀.2))).toReal) := by
              field_simp [ne_of_gt hrho]
      _ = rho * ((R / rho) * alpha u z₀ R ^ 2) := by rw [htarget]
      _ < rho * y := mul_lt_mul_of_pos_left hy hrho
  have hFy : ∀ᶠ h in (𝓝[>] (0 : ℝ)), F h < rho * y := by
    have hFy' := (Filter.limsup_le_iff' hFco hFbound).1 hFusc
      (((essSup (timeSliceBallEnergy z₀.1 R ·
        (fun w => vec3EuclideanNorm (u w)))
        (volume.restrict (Ioc (z₀.2 - R ^ 2) z₀.2))).toReal + rho * y) / 2)
      (by linarith only [hSlt])
    filter_upwards [hFy'] with h hh
    linarith only [hh, hSlt]
  have hFyCond := @theta_uschAlphaEventually_10_hFyCond_1 z₀ rho F htimeMap y hFy
  filter_upwards [hspace, htime, hFyCond] with z hzspace hztime hzFy
  have hballr := @theta_uschAlphaEventually_10_hballr_2 z₀ rho r z hzspace
  by_cases hpast : z.2 ≤ z₀.2
  · have hballR : vec3Ball z.1 rho ⊆ vec3Ball z₀.1 R := by
      intro x hx
      rw [mem_vec3Ball] at hx ⊢
      calc
        vec3EuclideanNorm (x - z₀.1) =
            vec3EuclideanNorm ((x - z.1) + (z.1 - z₀.1)) := by
              congr 1
              ring
        _ ≤ vec3EuclideanNorm (x - z.1) +
              vec3EuclideanNorm (z.1 - z₀.1) := euclidean_triangle _ _
        _ < rho + (r - rho) := add_lt_add hx hzspace
        _ = r := by ring
        _ < R := hrrR
    have hinterval : Ioc (z.2 - rho ^ 2) z.2 ⊆
        Ioc (z₀.2 - R ^ 2) z₀.2 := by
      intro s hs
      have hlower : z₀.2 - R ^ 2 < z.2 - rho ^ 2 := by
        nlinarith only [hztime.1, hτgap, hgap]
      exact ⟨lt_trans hlower hs.1, le_trans hs.2 hpast⟩
    have hold : Ioc (z₀.2 - R ^ 2) z₀.2 ⊆ Jo := by
      intro s hs
      have hm : ((z₀.1, s) : ParabolicPoint) ∈
          parabolicCylinder z₀.1 z₀.2 R := by
        rw [parabolicCylinder]
        exact ⟨by rw [mem_vec3Ball]; simp [vec3EuclideanNorm_zero, hR], hs⟩
      exact (hco0 hm).2
    have hIntOld : ∀ᵐ s ∂volume.restrict
        (Ioc (z₀.2 - R ^ 2) z₀.2),
        IntegrableOn (fun y : Vec3 =>
          (vec3EuclideanNorm (u (y, s))) ^ 2)
          (vec3Ball z₀.1 R) volume :=
      ae_restrict_of_ae_restrict_of_subset hold hvelRO
    have hbound := alpha_sq_le_of_essSup hrho hballR hinterval hIntOld hS0
    have hSreal : essSup (fun s => ENNReal.ofReal
        (∫ y in vec3Ball z₀.1 R,
          (vec3EuclideanNorm (u (y, s))) ^ 2))
        (volume.restrict (Ioc (z₀.2 - R ^ 2) z₀.2)) =
        essSup (timeSliceBallEnergy z₀.1 R ·
          (fun w => vec3EuclideanNorm (u w)))
          (volume.restrict (Ioc (z₀.2 - R ^ 2) z₀.2)) :=
      (essSup_congr_ae hEqOld).symm
    rw [hSreal] at hbound
    exact hbound.trans_lt (by rw [← htarget]; exact hy)
  · have hzfuture : z₀.2 < z.2 := lt_of_not_ge hpast
    let h : ℝ := z.2 - z₀.2
    have hh : 0 < h := by dsimp [h]; exact sub_pos.mpr hzfuture
    have hhh : h ≤ h₁ := by
      dsimp [h]
      linarith only [hztime.2, hτh₁, hτ]
    have hinterval : Ioc (z.2 - rho ^ 2) z.2 ⊆
        Ioc (z₀.2 - R ^ 2) z.2 := by
      intro s hs
      have hlower : z₀.2 - R ^ 2 < z.2 - rho ^ 2 := by
        nlinarith only [hzfuture, hgap]
      exact ⟨lt_trans hlower hs.1, hs.2⟩
    have hIntFuture : ∀ᵐ s ∂volume.restrict
        (Ioc (z₀.2 - R ^ 2) z.2),
        IntegrableOn (fun y : Vec3 =>
          (vec3EuclideanNorm (u (y, s))) ^ 2)
          (vec3Ball z₀.1 r) volume := by
      have hEqtime : z₀.2 + h = z.2 := by
        dsimp [h]
        ring
      have hIntAt' := hIntAt (h := h) hh hhh
      rw [hEqtime] at hIntAt'
      filter_upwards [hIntAt'] with s hs
      exact hs.1
    have hEqtime : z₀.2 + h = z.2 := by
      dsimp [h]
      ring
    have hfiniteSmallAt' := hfiniteSmallAt (h := h) hh hhh
    rw [hEqtime] at hfiniteSmallAt'
    have hbound := alpha_sq_le_of_essSup hrho hballr hinterval hIntFuture
      hfiniteSmallAt'
    have hFy' : F h < rho * y := by
      exact hzFy.resolve_left hpast
    have hF_eq : F h =
        (essSup (fun s => ENNReal.ofReal
          (∫ y in vec3Ball z₀.1 r,
            (vec3EuclideanNorm (u (y, s))) ^ 2))
          (volume.restrict (Ioc (z₀.2 - R ^ 2) z.2))).toReal := by
      dsimp [F]
      rw [hEqtime]
    calc
      alpha u z rho ^ 2 ≤ rho⁻¹ * F h := by
        rw [hF_eq]
        exact hbound
      _ < rho⁻¹ * (rho * y) :=
        mul_lt_mul_of_pos_left hFy' (inv_pos.mpr hrho)
      _ = y := by field_simp [ne_of_gt hrho]

private lemma theta_usc_ht₁I_1 :
    ∀ {I : Set ℝ} {z₀ : ParabolicPoint} {R : ℝ},
      ∀ ε > (0 : ℝ),
        ball z₀.2 ε ⊆ I →
          let h₁ : ℝ := min (ε / (2 : ℝ)) (R ^ (2 : ℕ) / (2 : ℝ));
          (0 : ℝ) < h₁ → z₀.2 + h₁ ∈ I
    := by
  intro I z₀ R ε hε hεI h₁ hh₁
  apply hεI
  apply Metric.mem_ball'.2
  rw [Real.dist_eq, show z₀.2 - (z₀.2 + h₁) = -h₁ by ring,
    abs_neg, abs_of_nonneg hh₁.le]
  dsimp [h₁]
  exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)

private lemma theta_usc_hWoldopen_2 :
    ∀ {z₀ : ParabolicPoint} {R : ℝ},
      let Wold : Set ParabolicPoint := vec3Ball z₀.1 R ×ˢ Ioo (z₀.2 - R ^ (2 : ℕ)) z₀.2;
      IsOpen Wold
    := by
  intro z₀ R Wold
  dsimp [Wold]
  change IsOpen (parabolicHomeomorph ⁻¹'
    (vec3Ball z₀.1 R ×ˢ Ioo (z₀.2 - R ^ 2) z₀.2))
  exact (isOpen_vec3Ball _ _).prod isOpen_Ioo |>.preimage
    parabolicHomeomorph.continuous

private lemma theta_usc_hWfutureopen_3 :
    ∀ {z₀ : ParabolicPoint} {R : ℝ} (ε : ℝ),
      let h₁ : ℝ := min (ε / (2 : ℝ)) (R ^ (2 : ℕ) / (2 : ℝ));
      let Wfuture : Set ParabolicPoint :=
        vec3Ball z₀.1 R ×ˢ Ioo (z₀.2 + h₁ - R ^ (2 : ℕ)) (z₀.2 + h₁);
      IsOpen Wfuture
    := by
  intro z₀ R ε h₁ Wfuture
  dsimp [Wfuture]
  change IsOpen (parabolicHomeomorph ⁻¹'
    (vec3Ball z₀.1 R ×ˢ Ioo (z₀.2 + h₁ - R ^ 2) (z₀.2 + h₁)))
  exact (isOpen_vec3Ball _ _).prod isOpen_Ioo |>.preimage
    parabolicHomeomorph.continuous

private lemma theta_usc_hballo_4 :
    ∀ {z₀ : ParabolicPoint} {R : ℝ} (ε : ℝ),
      let h₁ : ℝ := min (ε / (2 : ℝ)) (R ^ (2 : ℕ) / (2 : ℝ));
      (0 : ℝ) < h₁ →
        h₁ < R ^ (2 : ℕ) →
          ∀ (Ωo : Set Vec3) (Jo : Set ℝ),
            parabolicCylinder z₀.1 z₀.2 R ⊆ spaceTimeSet Ωo Jo → vec3Ball z₀.1 R ⊆ Ωo
    := by
  intro z₀ R ε h₁ hh₁ hh₁R Ωo Jo hco0 x hx
  have hx' : ((x, z₀.2) : ParabolicPoint) ∈
      parabolicCylinder z₀.1 z₀.2 R := by
    rw [parabolicCylinder]
    exact ⟨hx, ⟨by linarith only [hh₁, hh₁R], le_rfl⟩⟩
  exact (hco0 hx').1

private lemma theta_usc_hballf_5 :
    ∀ {z₀ : ParabolicPoint} {R : ℝ} (ε : ℝ),
      let h₁ : ℝ := min (ε / (2 : ℝ)) (R ^ (2 : ℕ) / (2 : ℝ));
      (0 : ℝ) < h₁ →
        h₁ < R ^ (2 : ℕ) →
          ∀ (Ωf : Set Vec3) (Jf : Set ℝ),
            parabolicCylinder z₀.1 (z₀.2 + h₁) R ⊆ spaceTimeSet Ωf Jf → vec3Ball z₀.1 R ⊆ Ωf
    := by
  intro z₀ R ε h₁ hh₁ hh₁R Ωf Jf hcf x hx
  have hx' : ((x, z₀.2 + h₁) : ParabolicPoint) ∈
      parabolicCylinder z₀.1 (z₀.2 + h₁) R := by
    rw [parabolicCylinder]
    exact ⟨hx, ⟨by linarith only [hh₁, hh₁R], le_rfl⟩⟩
  exact (hcf hx').1

private lemma theta_usc_hK_6 :
    ∀ {z₀ : ParabolicPoint} {rho R : ℝ},
      (0 : ℝ) < rho →
        rho < R →
          (0 : ℝ) < R ^ (2 : ℕ) - rho ^ (2 : ℕ) →
            ∀ (ε : ℝ),
              let h₁ : ℝ := min (ε / (2 : ℝ)) (R ^ (2 : ℕ) / (2 : ℝ));
              (0 : ℝ) < h₁ →
                h₁ < R ^ (2 : ℕ) →
                  let Wold : Set ParabolicPoint := vec3Ball z₀.1 R ×ˢ Ioo (z₀.2 - R ^ (2 : ℕ)) z₀.2;
                  let Wfuture : Set ParabolicPoint :=
                    vec3Ball z₀.1 R ×ˢ Ioo (z₀.2 + h₁ - R ^ (2 : ℕ)) (z₀.2 + h₁);
                  closure (parabolicCylinder z₀.1 z₀.2 rho) ⊆ Wold ∪ Wfuture
    := by
  intro z₀ rho R hrho hrhoR hgap ε h₁ hh₁ hh₁R Wold Wfuture
  rw [closure_parabolicCylinder hrho]
  intro z hz
  have hsp : z.1 ∈ vec3Ball z₀.1 R := by
    rw [mem_vec3Ball]
    exact lt_of_le_of_lt hz.1 hrhoR
  rcases lt_or_eq_of_le hz.2.2 with hlt | heq
  · exact Or.inl ⟨hsp, ⟨by linarith only [hz.2.1, hgap], hlt⟩⟩
  · exact Or.inr ⟨hsp, ⟨by linarith only [hh₁R, heq], by linarith only [hh₁, heq]⟩⟩

private lemma theta_usc_hgradmeasO_7 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ (Ωo : Set Vec3) (Jo : Set ℝ),
          localBox Ω I Ωo Jo →
            AEStronglyMeasurable (β := ℝ) (m₀ := MeasureSpace.toMeasurableSpace)
              (fun (w : ParabolicPoint) => spatialGradientSq u Du w)
              (Measure.restrict volume (spaceTimeSet Ωo Jo))
    := by
  intro Ω I q u Du p f hsol Ωo Jo hboxo
  have hDu := (hsol.2.2.2.2.2.1 Ωo Jo hboxo).2.1
  have hc : Continuous (fun v : Fin 3 → Vec3 =>
      ∑ i, ∑ j, (v i j) ^ (2 : ℕ)) := by fun_prop
  have hm := hc.comp_aestronglyMeasurable hDu
  simpa [spatialGradientSq, Function.comp_def] using hm

private lemma theta_usc_hgradmeasF_8 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ (Ωf : Set Vec3) (Jf : Set ℝ),
          localBox Ω I Ωf Jf →
            AEStronglyMeasurable (β := ℝ) (m₀ := MeasureSpace.toMeasurableSpace)
              (fun (w : ParabolicPoint) => spatialGradientSq u Du w)
              (Measure.restrict volume (spaceTimeSet Ωf Jf))
    := by
  intro Ω I q u Du p f hsol Ωf Jf hboxf
  have hDu := (hsol.2.2.2.2.2.1 Ωf Jf hboxf).2.1
  have hc : Continuous (fun v : Fin 3 → Vec3 =>
      ∑ i, ∑ j, (v i j) ^ (2 : ℕ)) := by fun_prop
  have hm := hc.comp_aestronglyMeasurable hDu
  simpa [spatialGradientSq, Function.comp_def] using hm

private lemma theta_usc_hgradIntO_9 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z₀ : ParabolicPoint} {R : ℝ},
          (0 : ℝ) < R →
            ∀ (ε : ℝ),
              let h₁ : ℝ := min (ε / (2 : ℝ)) (R ^ (2 : ℕ) / (2 : ℝ));
              (0 : ℝ) < h₁ →
                (∀ {h : ℝ},
                    (0 : ℝ) ≤ h →
                      h ≤ h₁ → closure (parabolicCylinder z₀.1 (z₀.2 + h) R) ⊆ spaceTimeSet Ω I) →
                  ∀ (Ωo : Set Vec3) (Jo : Set ℝ),
                    let Wold : Set ParabolicPoint :=
                      vec3Ball z₀.1 R ×ˢ Ioo (z₀.2 - R ^ (2 : ℕ)) z₀.2;
                    Wold ⊆ parabolicCylinder z₀.1 z₀.2 R →
                      Wold ⊆ spaceTimeSet Ωo Jo →
                        AEStronglyMeasurable (β := ℝ) (m₀ := MeasureSpace.toMeasurableSpace)
                            (fun (w : ParabolicPoint) => spatialGradientSq u Du w)
                            (Measure.restrict volume (spaceTimeSet Ωo Jo)) →
                          IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                            (fun (w : ParabolicPoint) => spatialGradientSq u Du w) Wold volume
    := by
  intro Ω I q u Du p f hsol z₀ R hR ε h₁ hh₁ hsubAt Ωo Jo Wold hWoldcyl hWoldbox hgradmeasO
  apply gradient_integrable_of_meas hgradmeasO hWoldbox
  have hsubo : closure (parabolicCylinder z₀.1 z₀.2 R) ⊆
      spaceTimeSet Ω I := by
    simpa only [add_zero] using
      (hsubAt (h := 0) (by norm_num) hh₁.le)
  exact (ne_of_lt (lt_of_le_of_lt (lintegral_mono_set hWoldcyl)
    (sws_gradient_integral_lt_top hsol hR hsubo)))

private lemma theta_usc_hgradIntF_10 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z₀ : ParabolicPoint} {R : ℝ},
          (0 : ℝ) < R →
            ∀ (ε : ℝ),
              let h₁ : ℝ := min (ε / (2 : ℝ)) (R ^ (2 : ℕ) / (2 : ℝ));
              (0 : ℝ) < h₁ →
                (∀ {h : ℝ},
                    (0 : ℝ) ≤ h →
                      h ≤ h₁ → closure (parabolicCylinder z₀.1 (z₀.2 + h) R) ⊆ spaceTimeSet Ω I) →
                  ∀ (Ωf : Set Vec3) (Jf : Set ℝ),
                    let Wfuture : Set ParabolicPoint :=
                      vec3Ball z₀.1 R ×ˢ Ioo (z₀.2 + h₁ - R ^ (2 : ℕ)) (z₀.2 + h₁);
                    Wfuture ⊆ parabolicCylinder z₀.1 (z₀.2 + h₁) R →
                      Wfuture ⊆ spaceTimeSet Ωf Jf →
                        AEStronglyMeasurable (β := ℝ) (m₀ := MeasureSpace.toMeasurableSpace)
                            (fun (w : ParabolicPoint) => spatialGradientSq u Du w)
                            (Measure.restrict volume (spaceTimeSet Ωf Jf)) →
                          IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                            (fun (w : ParabolicPoint) => spatialGradientSq u Du w) Wfuture volume
    := by
  intro Ω I q u Du p f hsol z₀ R hR ε h₁ hh₁ hsubAt Ωf Jf Wfuture hWfuturecyl hWfuturebox hgradmeasF
  apply gradient_integrable_of_meas hgradmeasF hWfuturebox
  have hsubf : closure (parabolicCylinder z₀.1 (z₀.2 + h₁) R) ⊆
      spaceTimeSet Ω I := hsubAt (h := h₁) hh₁.le le_rfl
  exact (ne_of_lt (lt_of_le_of_lt (lintegral_mono_set hWfuturecyl)
    (sws_gradient_integral_lt_top hsol (z := (z₀.1, z₀.2 + h₁)) hR hsubf)))

private lemma theta_usc_hKbar_11 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {z₀ : ParabolicPoint} {rho R : ℝ},
      euclideanClosedBall z₀.1 R ×ˢ Icc (z₀.2 - R ^ (2 : ℕ)) z₀.2 ⊆ spaceTimeSet Ω I →
        (0 : ℝ) < R →
          let r : ℝ := (rho + R) / (2 : ℝ);
          r < R → (0 : ℝ) < r → closure (parabolicCylinder z₀.1 z₀.2 r) ⊆ spaceTimeSet Ω I
    := by
  intro Ω I z₀ rho R hrect hR r hrrR hrpos
  rw [closure_parabolicCylinder hrpos]
  intro w hw
  have hrsq : r ^ 2 < R ^ 2 := by nlinarith only [hrpos, hR, hrrR]
  have hw0 : (w.1, w.2) ∈
      euclideanClosedBall z₀.1 R ×ˢ Icc (z₀.2 - R ^ 2) z₀.2 := by
    exact ⟨mem_euclideanClosedBall_of_vec3Norm_le hR.le
        (le_trans hw.1 hrrR.le), ⟨by linarith only [hw.2.1, hrsq], hw.2.2⟩⟩
  exact hrect hw0

private lemma theta_usc_hcarevent_12 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {z₀ : ParabolicPoint} {rho R : ℝ},
      (0 : ℝ) < rho →
        let r : ℝ := (rho + R) / (2 : ℝ);
        rho < r →
          (0 : ℝ) < r →
            IsOpen (spaceTimeSet Ω I) →
              closure (parabolicCylinder z₀.1 z₀.2 r) ⊆ spaceTimeSet Ω I →
                ∀ᶠ (z : ParabolicPoint) in 𝓝 z₀,
                  closure (parabolicCylinder z.1 z.2 rho) ⊆ spaceTimeSet Ω I
    := by
  intro Ω I z₀ rho R hrho r hrr hrpos hopen hKbar
  have hev := eventually_cylinder_subset_of_open hrpos hopen hKbar
  filter_upwards [hev] with z hz
  intro w hw
  apply hz
  rw [closure_parabolicCylinder hrho] at hw
  rw [parabolicCylinder]
  have hρrsq : rho ^ 2 < r ^ 2 := by nlinarith only [hrho, hrpos, hrr]
  exact ⟨lt_of_le_of_lt hw.1 hrr,
    ⟨by linarith only [hw.2.1, hρrsq], hw.2.2⟩⟩

private lemma theta_usc_hEqOld_13 :
    ∀ {u : ParabolicPoint → Vec3} {z₀ : ParabolicPoint} {R : ℝ},
      (0 : ℝ) < R →
        ∀ (Ωo : Set Vec3) (Jo : Set ℝ),
          parabolicCylinder z₀.1 z₀.2 R ⊆ spaceTimeSet Ωo Jo →
            (∀ᵐ (s : ℝ) ∂Measure.restrict volume Jo,
                IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                  (fun (y : Vec3) => vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ)) (vec3Ball z₀.1 R)
                  volume) →
              ∀ᵐ (s : ℝ) ∂Measure.restrict volume (Ioc (z₀.2 - R ^ (2 : ℕ)) z₀.2),
                (timeSliceBallEnergy z₀.1 R s fun (w : ParabolicPoint) => vec3EuclideanNorm (u w)) =
                  ENNReal.ofReal
                    (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                      (Measure.restrict volume (vec3Ball z₀.1 R)) fun (y : Vec3) =>
                      vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ))
    := by
  intro u z₀ R hR Ωo Jo hco0 hvelRO
  have hold : Ioc (z₀.2 - R ^ 2) z₀.2 ⊆ Jo := by
    intro s hs
    have hm : ((z₀.1, s) : ParabolicPoint) ∈
        parabolicCylinder z₀.1 z₀.2 R := by
      rw [parabolicCylinder]
      exact ⟨by rw [mem_vec3Ball]; simp [vec3EuclideanNorm_zero, hR], hs⟩
    exact (hco0 hm).2
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hold hvelRO] with s hs
  exact (time_slice_energy_eq_ofReal hs).symm

private lemma theta_usc_hspace_14 :
    ∀ {z₀ : ParabolicPoint} {rho R : ℝ},
      let r : ℝ := (rho + R) / (2 : ℝ);
      rho < r → ∀ᶠ (z : ParabolicPoint) in 𝓝 z₀, z.1 ∈ vec3Ball z₀.1 (r - rho)
    := by
  intro z₀ rho R r hrr
  have hz : z₀.1 ∈ vec3Ball z₀.1 (r - rho) := by
    rw [mem_vec3Ball]
    simp only [sub_self, vec3EuclideanNorm_zero, sub_pos]
    exact hrr
  exact ((isOpen_vec3Ball z₀.1 (r - rho)).preimage
    continuous_fst_parabolicPoint).mem_nhds hz

private lemma theta_usc_hAbound_15 :
    ∀ {u : ParabolicPoint → Vec3} {z₀ : ParabolicPoint} {rho R : ℝ},
      (∀ {y : ℝ},
          R / rho * alpha u z₀ R ^ (2 : ℕ) < y →
            ∀ᶠ (z : ParabolicPoint) in 𝓝 z₀, alpha u z rho ^ (2 : ℕ) < y) →
        IsBoundedUnder (fun (x1 x2 : ℝ) => x1 ≤ x2) (𝓝 z₀) fun (z : ParabolicPoint) =>
          alpha u z rho ^ (2 : ℕ)
    := by
  intro u z₀ rho R hAlphaEventually
  apply isBoundedUnder_of_eventually_le
  on_goal 1 =>
    filter_upwards [hAlphaEventually
      (y := (R / rho) * alpha u z₀ R ^ 2 + 1)
      (lt_add_of_pos_right _ (by norm_num))] with z hz
  exact hz.le

private lemma theta_usc_hsub0_1 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {z₀ : ParabolicPoint} {R : ℝ},
      euclideanClosedBall z₀.1 R ×ˢ Icc (z₀.2 - R ^ (2 : ℕ)) z₀.2 ⊆ spaceTimeSet Ω I →
        (0 : ℝ) < R → closure (parabolicCylinder z₀.1 z₀.2 R) ⊆ spaceTimeSet Ω I
    := by
  intro Ω I z₀ R hrect hR
  rw [closure_parabolicCylinder hR]
  intro z hz
  apply hrect
  exact ⟨mem_euclideanClosedBall_of_vec3Norm_le hR.le hz.1, hz.2⟩

private lemma theta_usc_hWoldcyl_2 :
    ∀ {z₀ : ParabolicPoint} {R : ℝ},
      let Wold : Set ParabolicPoint := vec3Ball z₀.1 R ×ˢ Ioo (z₀.2 - R ^ (2 : ℕ)) z₀.2;
      Wold ⊆ parabolicCylinder z₀.1 z₀.2 R
    := by
  intro z₀ R Wold z hz
  dsimp [Wold] at hz ⊢
  exact ⟨hz.1, hz.2.1, hz.2.2.le⟩

private lemma theta_usc_hWfuturecyl_3 :
    ∀ {z₀ : ParabolicPoint} {R : ℝ} (ε : ℝ),
      let h₁ : ℝ := min (ε / (2 : ℝ)) (R ^ (2 : ℕ) / (2 : ℝ));
      let Wfuture : Set ParabolicPoint :=
        vec3Ball z₀.1 R ×ˢ Ioo (z₀.2 + h₁ - R ^ (2 : ℕ)) (z₀.2 + h₁);
      Wfuture ⊆ parabolicCylinder z₀.1 (z₀.2 + h₁) R
    := by
  intro z₀ R ε h₁ Wfuture z hz
  dsimp [Wfuture] at hz ⊢
  exact ⟨hz.1, hz.2.1, hz.2.2.le⟩

private lemma theta_usc_hpmeasO_4 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ (Ωo : Set Vec3) (Jo : Set ℝ),
          localBox Ω I Ωo Jo →
            AEStronglyMeasurable (β := ℝ) (m₀ := MeasureSpace.toMeasurableSpace)
              (fun (w : ParabolicPoint) => |p w| ^ (3 / 2 : ℝ))
              (Measure.restrict volume (spaceTimeSet Ωo Jo))
    := by
  intro Ω I q u Du p f hsol Ωo Jo hboxo
  have hp := (hsol.2.2.2.2.2.1 Ωo Jo hboxo).2.2.1
  have hc := (Real.continuous_rpow_const
    (by norm_num : (0 : ℝ) ≤ 3 / 2)).comp continuous_abs
  exact hc.comp_aestronglyMeasurable hp

private lemma theta_usc_hpmeasF_5 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ (Ωf : Set Vec3) (Jf : Set ℝ),
          localBox Ω I Ωf Jf →
            AEStronglyMeasurable (β := ℝ) (m₀ := MeasureSpace.toMeasurableSpace)
              (fun (w : ParabolicPoint) => |p w| ^ (3 / 2 : ℝ))
              (Measure.restrict volume (spaceTimeSet Ωf Jf))
    := by
  intro Ω I q u Du p f hsol Ωf Jf hboxf
  have hp := (hsol.2.2.2.2.2.1 Ωf Jf hboxf).2.2.1
  have hc := (Real.continuous_rpow_const
    (by norm_num : (0 : ℝ) ≤ 3 / 2)).comp continuous_abs
  exact hc.comp_aestronglyMeasurable hp

private lemma theta_usc_hz₀carrier_6 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {z₀ : ParabolicPoint} {rho R : ℝ},
      (0 : ℝ) < rho →
        let r : ℝ := (rho + R) / (2 : ℝ);
        rho < r →
          closure (parabolicCylinder z₀.1 z₀.2 ((rho + R) / (2 : ℝ))) ⊆ spaceTimeSet Ω I →
            closure (parabolicCylinder z₀.1 z₀.2 rho) ⊆ spaceTimeSet Ω I
    := by
  intro Ω I z₀ rho R hrho r hrr hKbar
  have hmono : parabolicCylinder z₀.1 z₀.2 rho ⊆
      parabolicCylinder z₀.1 z₀.2 r :=
    parabolicCylinder_mono hrho.le hrr.le
  exact (closure_mono hmono).trans hKbar

private lemma theta_usc_hβcont_7 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {z₀ : ParabolicPoint}
      {rho : ℝ},
      Tendsto
          ((fun (x : ℝ) => x ^ (1 / 2 : ℝ)) ∘ fun (z : ParabolicPoint) =>
            rho⁻¹ *
              @integral _ _ _ _ MeasureSpace.toMeasurableSpace
                (Measure.restrict volume (parabolicCylinder z.1 z.2 rho))
                fun (w : ParabolicPoint) => spatialGradientSq u Du w)
          (𝓝 z₀)
          (𝓝
            ((rho⁻¹ *
                @integral _ _ _ _ MeasureSpace.toMeasurableSpace
                  (Measure.restrict volume (parabolicCylinder z₀.1 z₀.2 rho))
                  fun (w : ParabolicPoint) => spatialGradientSq u Du w) ^
              (1 / 2 : ℝ))) →
        (∀ᶠ (z : ParabolicPoint) in 𝓝 z₀,
            beta u Du z rho =
              (rho⁻¹ *
                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace
                    (Measure.restrict volume (parabolicCylinder z.1 z.2 rho))
                    fun (w : ParabolicPoint) => spatialGradientSq u Du w) ^
                (1 / 2 : ℝ)) →
          beta u Du z₀ rho =
              (rho⁻¹ *
                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace
                    (Measure.restrict volume (parabolicCylinder z₀.1 z₀.2 rho))
                    fun (w : ParabolicPoint) => spatialGradientSq u Du w) ^
                (1 / 2 : ℝ) →
            Tendsto (fun (z : ParabolicPoint) => beta u Du z rho) (𝓝 z₀) (𝓝 (beta u Du z₀ rho))
    := by
  intro u Du z₀ rho hβpow hβevent hβ₀
  have hβevent' := hβevent.mono (fun z hz => hz.symm)
  have ht := hβpow.congr' hβevent'
  simpa only [hβ₀] using ht

private lemma theta_usc_hδcont_8 :
    ∀ {p : ParabolicPoint → ℝ} {z₀ : ParabolicPoint} {rho : ℝ},
      Tendsto
          ((fun (x : ℝ) => x ^ (1 / 3 : ℝ)) ∘ fun (z : ParabolicPoint) =>
            rho ^ (-2 : ℝ) *
              @integral _ _ _ _ MeasureSpace.toMeasurableSpace
                (Measure.restrict volume (parabolicCylinder z.1 z.2 rho))
                fun (w : ParabolicPoint) => |p w| ^ (3 / 2 : ℝ))
          (𝓝 z₀)
          (𝓝
            ((rho ^ (-2 : ℝ) *
                @integral _ _ _ _ MeasureSpace.toMeasurableSpace
                  (Measure.restrict volume (parabolicCylinder z₀.1 z₀.2 rho))
                  fun (w : ParabolicPoint) => |p w| ^ (3 / 2 : ℝ)) ^
              (1 / 3 : ℝ))) →
        (∀ᶠ (z : ParabolicPoint) in 𝓝 z₀,
            delta p z rho =
              (rho ^ (-2 : ℝ) *
                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace
                    (Measure.restrict volume (parabolicCylinder z.1 z.2 rho))
                    fun (w : ParabolicPoint) => |p w| ^ (3 / 2 : ℝ)) ^
                (1 / 3 : ℝ)) →
          delta p z₀ rho =
              (rho ^ (-2 : ℝ) *
                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace
                    (Measure.restrict volume (parabolicCylinder z₀.1 z₀.2 rho))
                    fun (w : ParabolicPoint) => |p w| ^ (3 / 2 : ℝ)) ^
                (1 / 3 : ℝ) →
            Tendsto (fun (z : ParabolicPoint) => delta p z rho) (𝓝 z₀) (𝓝 (delta p z₀ rho))
    := by
  intro p z₀ rho hδpow hδevent hδ₀
  have hδevent' := hδevent.mono (fun z hz => hz.symm)
  have ht := hδpow.congr' hδevent'
  simpa only [hδ₀] using ht

private lemma theta_usc_hballrO_9 :
    ∀ {z₀ : ParabolicPoint} {rho R : ℝ},
      let r : ℝ := (rho + R) / (2 : ℝ);
      r < R → ∀ (Ωo : Set Vec3), vec3Ball z₀.1 R ⊆ Ωo → vec3Ball z₀.1 r ⊆ Ωo
    := by
  intro z₀ rho R r hrrR Ωo hballo x hx
  apply hballo
  rw [mem_vec3Ball] at hx ⊢
  exact lt_trans hx hrrR

private lemma theta_usc_hballrF_10 :
    ∀ {z₀ : ParabolicPoint} {rho R : ℝ},
      let r : ℝ := (rho + R) / (2 : ℝ);
      r < R → ∀ (Ωf : Set Vec3), vec3Ball z₀.1 R ⊆ Ωf → vec3Ball z₀.1 r ⊆ Ωf
    := by
  intro z₀ rho R r hrrR Ωf hballf x hx
  apply hballf
  rw [mem_vec3Ball] at hx ⊢
  exact lt_trans hx hrrR

private lemma theta_usc_htarget_11 :
    ∀ {u : ParabolicPoint → Vec3} {z₀ : ParabolicPoint} {rho R : ℝ},
      (0 : ℝ) < rho →
        (0 : ℝ) < R →
          R / rho * alpha u z₀ R ^ (2 : ℕ) =
            rho⁻¹ *
              ENNReal.toReal
                (@essSup _ _ _ MeasureSpace.toMeasurableSpace
                  (fun (x : ℝ) =>
                    timeSliceBallEnergy z₀.1 R x fun (w : ParabolicPoint) =>
                      vec3EuclideanNorm (u w))
                  (Measure.restrict volume (Ioc (z₀.2 - R ^ (2 : ℕ)) z₀.2)))
    := by
  intro u z₀ rho R hrho hR
  rw [alpha_sq_eq u z₀ R hR]
  simp only [timeSliceEnergyEssSup]
  field_simp [ne_of_gt hrho, ne_of_gt hR]

private lemma theta_usc_htime_12 :
    ∀ {z₀ : ParabolicPoint} {rho R : ℝ} (ε : ℝ),
      let h₁ : ℝ := min (ε / (2 : ℝ)) (R ^ (2 : ℕ) / (2 : ℝ));
      let τ : ℝ := min (h₁ / (2 : ℝ)) ((R ^ (2 : ℕ) - rho ^ (2 : ℕ)) / (2 : ℝ));
      (0 : ℝ) < τ → ∀ᶠ (z : ParabolicPoint) in 𝓝 z₀, z.2 ∈ Ioo (z₀.2 - τ) (z₀.2 + τ)
    := by
  intro z₀ rho R ε h₁ τ hτ
  have hz : z₀.2 ∈ Ioo (z₀.2 - τ) (z₀.2 + τ) := by
    exact ⟨sub_lt_self _ hτ, lt_add_of_pos_right _ hτ⟩
  exact ((isOpen_Ioo.preimage continuous_snd_parabolicPoint).mem_nhds hz)

private lemma theta_usc_hAlimsup_13 :
    ∀ {u : ParabolicPoint → Vec3} {z₀ : ParabolicPoint} {rho R : ℝ},
      (∀ {y : ℝ},
          R / rho * alpha u z₀ R ^ (2 : ℕ) < y →
            ∀ᶠ (z : ParabolicPoint) in 𝓝 z₀, alpha u z rho ^ (2 : ℕ) < y) →
        (IsCoboundedUnder (fun (x1 x2 : ℝ) => x1 ≤ x2) (𝓝 z₀) fun (z : ParabolicPoint) =>
            alpha u z rho ^ (2 : ℕ)) →
          (IsBoundedUnder (fun (x1 x2 : ℝ) => x1 ≤ x2) (𝓝 z₀) fun (z : ParabolicPoint) =>
              alpha u z rho ^ (2 : ℕ)) →
            limsup (fun (z : ParabolicPoint) => alpha u z rho ^ (2 : ℕ)) (𝓝 z₀) ≤
              R / rho * alpha u z₀ R ^ (2 : ℕ)
    := by
  intro u z₀ rho R hAlphaEventually hAco hAbound
  rw [Filter.limsup_le_iff' hAco hAbound]
  intro y hy
  filter_upwards [hAlphaEventually hy] with z hz
  exact hz.le

/-- The scale quantities have the base-point semicontinuity and continuity used
in the Step 2 transfer argument. -/
theorem theta_usc_of_sws_with_alpha_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z₀ : ParabolicPoint} {rho R : ℝ} (hrho : 0 < rho) (hrhoR : rho < R)
    (hrect : euclideanClosedBall z₀.1 R ×ˢ Icc (z₀.2 - R ^ 2) z₀.2 ⊆
      spaceTimeSet Ω I) (ht₀ : z₀.2 ∈ I) :
    Filter.limsup (fun z : ParabolicPoint => alpha u z rho ^ 2) (𝓝 z₀) ≤
        (R / rho) * alpha u z₀ R ^ 2 ∧
      Tendsto (fun z => beta u Du z rho) (𝓝 z₀)
        (𝓝 (beta u Du z₀ rho)) ∧
      Tendsto (fun z => delta p z rho) (𝓝 z₀)
        (𝓝 (delta p z₀ rho)) ∧
      IsBoundedUnder (· ≤ ·) (𝓝 z₀)
        (fun z : ParabolicPoint => alpha u z rho ^ 2) := by
  have hR : 0 < R := lt_trans hrho hrhoR
  have hgap : 0 < R ^ 2 - rho ^ 2 := by nlinarith only [hR, hrho, hrhoR]
  let r : ℝ := (rho + R) / 2
  have hrr : rho < r := by dsimp [r]; linarith only [hrhoR]
  have hrrR : r < R := by dsimp [r]; linarith only [hrhoR]
  have hsub0 := @theta_usc_hsub0_1 Ω I z₀ R hrect hR
  have hrpos : 0 < r := lt_trans hrho hrr
  have hαusc := alpha_usc_of_sws hsol hrpos hrrR
    (by nlinarith only [hR]) hrect
  have hS0 : essSup (timeSliceBallEnergy z₀.1 R ·
      (fun w => vec3EuclideanNorm (u w)))
      (volume.restrict (Ioc (z₀.2 - R ^ 2) z₀.2)) ≠ ⊤ :=
    ne_of_lt (sws_timeSliceBallEnergy_essSup_lt_top hsol hR
      (by nlinarith only [hR]) hrect)
  obtain ⟨ε, hε, hεI⟩ := Metric.mem_nhds_iff.mp
    (hsol.2.1.mem_nhds ht₀)
  let h₁ : ℝ := min (ε / 2) (R ^ 2 / 2)
  have hh₁ : 0 < h₁ := by
    dsimp [h₁]
    exact lt_min (by positivity) (by positivity)
  have hh₁R : h₁ < R ^ 2 := by
    dsimp [h₁]
    exact lt_of_le_of_lt (min_le_right _ _) (by nlinarith only [hR])
  have ht₁I := @theta_usc_ht₁I_1 I z₀ R ε hε hεI hh₁
  have hsubAt := @theta_usc_hsubAt_1 Ω I q u Du p f hsol z₀ R hrect ht₀ hR h₁ ht₁I
  obtain ⟨Ωo, Jo, hboxo, hco⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 hR (by
      simpa only [add_zero] using (hsubAt (h := 0) (by norm_num) hh₁.le))
  obtain ⟨Ωf, Jf, hboxf, hcf⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 hR (hsubAt (h := h₁) hh₁.le le_rfl)
  let Wold : Set ParabolicPoint :=
    vec3Ball z₀.1 R ×ˢ Ioo (z₀.2 - R ^ 2) z₀.2
  let Wfuture : Set ParabolicPoint :=
    vec3Ball z₀.1 R ×ˢ Ioo (z₀.2 + h₁ - R ^ 2) (z₀.2 + h₁)
  have hWoldopen := @theta_usc_hWoldopen_2 z₀ R
  have hWfutureopen := @theta_usc_hWfutureopen_3 z₀ R ε
  have hWoldcyl := @theta_usc_hWoldcyl_2 z₀ R
  have hWfuturecyl := @theta_usc_hWfuturecyl_3 z₀ R ε
  have hco0 : parabolicCylinder z₀.1 z₀.2 R ⊆ spaceTimeSet Ωo Jo := by
    simpa only [add_zero] using hco
  have hWoldbox : Wold ⊆ spaceTimeSet Ωo Jo := hWoldcyl.trans hco0
  have hWfuturebox : Wfuture ⊆ spaceTimeSet Ωf Jf := hWfuturecyl.trans hcf
  have hballo := @theta_usc_hballo_4 z₀ R ε hh₁ hh₁R Ωo Jo hco0
  have hballf := @theta_usc_hballf_5 z₀ R ε hh₁ hh₁R Ωf Jf hcf
  have hK : closure (parabolicCylinder z₀.1 z₀.2 rho) ⊆ Wold ∪ Wfuture := by
    exact @theta_usc_hK_6 z₀ rho R hrho hrhoR hgap ε hh₁ hh₁R
  let G : Set ParabolicPoint := Wold ∪ Wfuture
  have hGopen : IsOpen G := hWoldopen.union hWfutureopen
  have hgradmeasO := @theta_usc_hgradmeasO_7 Ω I q u Du p f hsol Ωo Jo hboxo
  have hgradmeasF := @theta_usc_hgradmeasF_8 Ω I q u Du p f hsol Ωf Jf hboxf
  have hgradIntO := @theta_usc_hgradIntO_9 Ω I q u Du p f hsol z₀ R hR ε hh₁ hsubAt Ωo Jo hWoldcyl
    hWoldbox hgradmeasO
  have hgradIntF := @theta_usc_hgradIntF_10 Ω I q u Du p f hsol z₀ R hR ε hh₁ hsubAt Ωf Jf
    hWfuturecyl hWfuturebox hgradmeasF
  have hgradInt : IntegrableOn (fun w => spatialGradientSq u Du w) G volume := by
    exact hgradIntO.union hgradIntF
  have hpmeasO := @theta_usc_hpmeasO_4 Ω I q u Du p f hsol Ωo Jo hboxo
  have hpmeasF := @theta_usc_hpmeasF_5 Ω I q u Du p f hsol Ωf Jf hboxf
  have hpIntO := @theta_usc_hpIntO_2 Ω I q u Du p f hsol z₀ R hR h₁ hh₁ hsubAt Ωo Jo hWoldcyl
    hWoldbox hpmeasO
  have hpIntF := @theta_usc_hpIntF_3 Ω I q u Du p f hsol z₀ R hR h₁ hh₁ hsubAt Ωf Jf hWfuturecyl
    hWfuturebox hpmeasF
  have hpInt : IntegrableOn (fun w => |p w| ^ (3 / 2 : ℝ)) G volume := by
    exact hpIntO.union hpIntF
  have hgradT := cylinder_integral_tendsto_of_open hGopen hrho hK hgradInt
  have hpT := cylinder_integral_tendsto_of_open hGopen hrho hK hpInt
  have hβrepr := @theta_usc_hβrepr_4 Ω I u Du z₀ rho R hrho h₁ hgradInt
  have hδrepr := @theta_usc_hδrepr_5 Ω I p z₀ rho R hrho h₁ hpInt
  have hopen : IsOpen (spaceTimeSet Ω I) :=
    isOpen_spaceTimeSet Ω I hsol.1 hsol.2.1
  have hKbar := @theta_usc_hKbar_11 Ω I z₀ rho R hrect hR hrrR hrpos
  have hGevent : ∀ᶠ z in 𝓝 z₀,
      parabolicCylinder z.1 z.2 rho ⊆ G :=
    eventually_cylinder_subset_of_open hrho hGopen hK
  have hcarevent := @theta_usc_hcarevent_12 Ω I z₀ rho R hrho hrr hrpos hopen hKbar
  have hβbase : Tendsto
      (fun z => rho⁻¹ * ∫ w in parabolicCylinder z.1 z.2 rho,
        spatialGradientSq u Du w) (𝓝 z₀)
      (𝓝 (rho⁻¹ * ∫ w in parabolicCylinder z₀.1 z₀.2 rho,
        spatialGradientSq u Du w)) :=
    tendsto_const_nhds.mul hgradT
  have hδbase : Tendsto
      (fun z => rho ^ (-2 : ℝ) * ∫ w in parabolicCylinder z.1 z.2 rho,
        |p w| ^ (3 / 2 : ℝ)) (𝓝 z₀)
      (𝓝 (rho ^ (-2 : ℝ) * ∫ w in parabolicCylinder z₀.1 z₀.2 rho,
        |p w| ^ (3 / 2 : ℝ))) :=
    tendsto_const_nhds.mul hpT
  have hβpow := (Real.continuous_rpow_const
    (q := (1 / 2 : ℝ)) (by norm_num)).continuousAt.tendsto.comp hβbase
  have hδpow := (Real.continuous_rpow_const
    (q := (1 / 3 : ℝ)) (by norm_num)).continuousAt.tendsto.comp hδbase
  have hβevent : ∀ᶠ z in 𝓝 z₀,
      beta u Du z rho =
        (rho⁻¹ * ∫ w in parabolicCylinder z.1 z.2 rho,
          spatialGradientSq u Du w) ^ (1 / 2 : ℝ) := by
    filter_upwards [hcarevent, hGevent] with z hz hzG
    exact hβrepr z hz hzG
  have hδevent : ∀ᶠ z in 𝓝 z₀,
      delta p z rho =
        (rho ^ (-2 : ℝ) * ∫ w in parabolicCylinder z.1 z.2 rho,
          |p w| ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ) := by
    filter_upwards [hcarevent, hGevent] with z hz hzG
    exact hδrepr z hz hzG
  have hz₀carrier := @theta_usc_hz₀carrier_6 Ω I z₀ rho R hrho hrr hKbar
  have hz₀G : parabolicCylinder z₀.1 z₀.2 rho ⊆ G := by
    intro w hw
    simpa [G] using hK (subset_closure hw)
  have hβ₀ := hβrepr z₀ hz₀carrier hz₀G
  have hδ₀ := hδrepr z₀ hz₀carrier hz₀G
  have hβcont := @theta_usc_hβcont_7 u Du z₀ rho hβpow hβevent hβ₀
  have hδcont := @theta_usc_hδcont_8 p z₀ rho hδpow hδevent hδ₀
  let F : ℝ → ℝ := fun h =>
    (essSup (fun s => ENNReal.ofReal
      (∫ y in vec3Ball z₀.1 r,
        (vec3EuclideanNorm (u (y, s))) ^ 2))
      (volume.restrict (Ioc (z₀.2 - R ^ 2) (z₀.2 + h)))).toReal
  have hFusc : Filter.limsup F (𝓝[>] (0 : ℝ)) ≤
      (essSup (timeSliceBallEnergy z₀.1 R ·
        (fun w => vec3EuclideanNorm (u w)))
        (volume.restrict (Ioc (z₀.2 - R ^ 2) z₀.2))).toReal := by
    simpa only [F] using hαusc
  have hFnonneg : ∀ᶠ h in (𝓝[>] (0 : ℝ)), 0 ≤ F h := by
    filter_upwards [] with h
    exact ENNReal.toReal_nonneg
  have hFco : IsCoboundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ)) F :=
    isCoboundedUnder_le_of_eventually_le _ hFnonneg
  have hballrO := @theta_usc_hballrO_9 z₀ rho R hrrR Ωo hballo
  have hballrF := @theta_usc_hballrF_10 z₀ rho R hrrR Ωf hballf
  have hvelrO := velocity_slice_integrable hsol hboxo hballrO
  have hvelrF := velocity_slice_integrable hsol hboxf hballrF
  have hvelRO := velocity_slice_integrable hsol hboxo hballo
  have hvelRF := velocity_slice_integrable hsol hboxf hballf
  have hIntAt := @theta_usc_hIntAt_6 u z₀ R hR r h₁ hh₁R Ωo Jo Ωf Jf hcf hco0 hvelrO hvelrF hvelRO
    hvelRF
  have hfiniteRAt := @theta_usc_hfiniteRAt_7 Ω I q u Du p f hsol z₀ R hrect hR r h₁ hh₁R hsubAt
    hIntAt
  have hfiniteSmallAt := @theta_usc_hfiniteSmallAt_8 u z₀ R r hrrR h₁ hIntAt hfiniteRAt
  have hFbound : IsBoundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ)) F := by
    simpa only [F] using
      theta_usc_timeSliceEnergy_bounded hsol hR hrrR hh₁ hh₁R hsubAt hIntAt hS0
  have hEqOld := @theta_usc_hEqOld_13 u z₀ R hR Ωo Jo hco0 hvelRO
  have hfiniteROld : essSup (fun s => ENNReal.ofReal
        (∫ y in vec3Ball z₀.1 R,
          (vec3EuclideanNorm (u (y, s))) ^ 2))
        (volume.restrict (Ioc (z₀.2 - R ^ 2) z₀.2)) ≠ ⊤ := by
    rw [← essSup_congr_ae hEqOld]
    exact hS0
  have htarget := @theta_usc_htarget_11 u z₀ rho R hrho hR
  have hspace := @theta_usc_hspace_14 z₀ rho R hrr
  let τ : ℝ := min (h₁ / 2) ((R ^ 2 - rho ^ 2) / 2)
  have hτ : 0 < τ := by
    dsimp [τ]
    positivity
  have hτh₁ : τ ≤ h₁ / 2 := min_le_left _ _
  have hτgap : τ ≤ (R ^ 2 - rho ^ 2) / 2 := min_le_right _ _
  have htime := @theta_usc_htime_12 z₀ rho R ε hτ
  have htimeMap := @theta_usc_htimeMap_9 z₀
  have hAlphaEventually := @theta_usc_hAlphaEventually_10 u z₀ rho R hrho hR hgap r hrrR hS0 h₁ Ωo
    Jo hco0 hFusc hFco hvelRO hIntAt hfiniteSmallAt hFbound hEqOld htarget hspace τ hτ hτh₁ hτgap
    htime htimeMap
  have hAco : IsCoboundedUnder (· ≤ ·) (𝓝 z₀)
      (fun z : ParabolicPoint => alpha u z rho ^ 2) :=
    isCoboundedUnder_le_of_eventually_le _
      (Filter.Eventually.of_forall (fun z => sq_nonneg _))
  have hAbound := @theta_usc_hAbound_15 u z₀ rho R hAlphaEventually
  have hAlimsup := @theta_usc_hAlimsup_13 u z₀ rho R hAlphaEventually hAco hAbound
  exact ⟨hAlimsup, hβcont, hδcont, hAbound⟩

/-- The paper-shaped semicontinuity and continuity statement for the scale
quantities. -/
theorem theta_usc_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z₀ : ParabolicPoint} {rho R : ℝ} (hrho : 0 < rho) (hrhoR : rho < R)
    (hrect : euclideanClosedBall z₀.1 R ×ˢ Icc (z₀.2 - R ^ 2) z₀.2 ⊆
      spaceTimeSet Ω I) (ht₀ : z₀.2 ∈ I) :
    Filter.limsup (fun z : ParabolicPoint => alpha u z rho ^ 2) (𝓝 z₀) ≤
        (R / rho) * alpha u z₀ R ^ 2 ∧
      Tendsto (fun z => beta u Du z rho) (𝓝 z₀)
        (𝓝 (beta u Du z₀ rho)) ∧
      Tendsto (fun z => delta p z rho) (𝓝 z₀)
        (𝓝 (delta p z₀ rho)) := by
  have h := theta_usc_of_sws_with_alpha_bound hsol hrho hrhoR hrect ht₀
  exact ⟨h.1, h.2.1, h.2.2.1⟩

end CKN
