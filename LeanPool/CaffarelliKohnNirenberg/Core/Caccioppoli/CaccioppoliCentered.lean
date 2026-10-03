/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.CaccioppoliAssembly
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.CaccioppoliCenteredRhs

/-!
# Caccioppoli Centered

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration


noncomputable section

namespace CKN

private lemma caccioppoli_centered_hcenter_hc_1 :
    ∀ {u : ParabolicPoint → Vec3} {x₀ : Vec3} {ρ : ℝ} (J : Set ℝ),
      let B : Set Vec3 := vec3Ball x₀ ρ;
      AEStronglyMeasurable (fun (z : Vec3 × ℝ) => vec3EuclideanNorm (u z) ^ (2 : ℕ))
          ((volume.restrict B).prod (volume.restrict J)) →
        let c : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
          ⨍ (x : Vec3) in B, vec3EuclideanNorm (u (x, z.2)) ^ (2 : ℕ);
        AEMeasurable (fun (s : ℝ) => c (x₀, s)) (volume.restrict J)
    := by
  intro u x₀ ρ J B hsqProd c
  have hsm := MeasureTheory.AEStronglyMeasurable.integral_prod_right'
    hsqProd.prod_swap
  have hsm' : AEMeasurable (fun s =>
      ∫ x in B, (vec3EuclideanNorm (u (x, s))) ^ (2 : ℕ))
      (volume.restrict J) := by
    simpa only [Prod.swap_prod_mk] using hsm.aemeasurable
  let k : ℝ := ((volume.restrict B).real Set.univ)⁻¹
  convert hsm'.const_mul k using 1
  · funext s
    rw [show c (x₀, s) = k *
        ∫ x in B, (vec3EuclideanNorm (u (x, s))) ^ (2 : ℕ) by
      simp [k, c, MeasureTheory.average_eq, smul_eq_mul]]

private lemma caccioppoli_centered_hcenter_habsProd_2 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ : ℝ},
      closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I →
        ∀ (J : Set ℝ),
          let B : Set Vec3 := vec3Ball x₀ ρ;
          AEStronglyMeasurable (fun (z : Vec3 × ℝ) => vec3EuclideanNorm (u z) ^ (2 : ℕ))
              ((volume.restrict B).prod (volume.restrict J)) →
            let c : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
              ⨍ (x : Vec3) in B, vec3EuclideanNorm (u (x, z.2)) ^ (2 : ℕ);
            AEMeasurable (fun (z : Vec3 × ℝ) => c (z.1, z.2))
                ((volume.restrict B).prod (volume.restrict J)) →
              AEMeasurable
                (fun (z : Vec3 × ℝ) =>
                  ENNReal.ofReal |vec3EuclideanNorm (u z) ^ (2 : ℕ) - c (z.1, z.2)|)
                ((volume.restrict B).prod (volume.restrict J))
    := by
  intro Ω I u x₀ t₀ ρ hsub J B hsqProd c hcProd
  have hreal : AEMeasurable (fun z : Vec3 × ℝ =>
      |(vec3EuclideanNorm (u z)) ^ 2 - c (z.1, z.2)|)
      ((volume.restrict B).prod (volume.restrict J)) := by
    have hreal' := hsqProd.sub hcProd.aestronglyMeasurable
    have hsub : AEMeasurable (fun z : Vec3 × ℝ =>
        (vec3EuclideanNorm (u z)) ^ 2 - c (z.1, z.2))
        ((volume.restrict B).prod (volume.restrict J)) := by
      have heq : (fun z : Vec3 × ℝ =>
          (vec3EuclideanNorm (u z)) ^ 2 - c (z.1, z.2)) =
          (fun z : Vec3 × ℝ => (vec3EuclideanNorm (u z)) ^ 2) -
            (fun z : Vec3 × ℝ => c (z.1, z.2)) := by
        rfl
      rw [heq]
      exact hreal'.aemeasurable
    exact continuous_abs.measurable.comp_aemeasurable hsub
  exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable hreal

private lemma caccioppoli_centered_hcenter_hD_cyl_3 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {x₀ : Vec3} {t₀ ρ : ℝ}
      (J : Set ℝ),
      let B : Set Vec3 := vec3Ball x₀ ρ;
      let T : Set ℝ := Ioc (t₀ - ρ ^ (2 : ℕ)) t₀;
      T ⊆ J →
        AEStronglyMeasurable Du ((volume.restrict B).prod (volume.restrict J)) →
          AEMeasurable (fun (z : ParabolicPoint) => ENNReal.ofReal (spatialGradientSq u Du z))
            (volume.restrict (parabolicCylinder x₀ t₀ ρ))
    := by
  intro u Du x₀ t₀ ρ J B T hT' hDuProd
  have hsum : Continuous (fun v : Fin 3 → Vec3 =>
      ENNReal.ofReal (∑ i : Fin 3, ∑ j : Fin 3, (v i j) ^ (2 : ℕ))) := by
    exact ENNReal.continuous_ofReal.comp (by fun_prop)
  have hDprod : AEMeasurable (fun z : Vec3 × ℝ =>
      ENNReal.ofReal (spatialGradientSq u Du z))
      ((volume.restrict B).prod (volume.restrict J)) := by
    exact (hsum.comp_aestronglyMeasurable hDuProd).aemeasurable
  have hDprod' := hDprod
  rw [Measure.prod_restrict] at hDprod'
  rw [volume_parabolicPoint_eq_prod]
  exact hDprod'.mono_measure
    (Measure.restrict_mono (μ := volume.prod volume) (ν := volume.prod volume)
      (by
        intro z hz
        exact ⟨hz.1, hT' hz.2⟩) le_rfl)

private lemma caccioppoli_centered_hcenter_hEbound_4 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {x₀ : Vec3} {t₀ ρ : ℝ},
          (0 : ℝ) < ρ →
            closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I →
              let B : Set Vec3 := vec3Ball x₀ ρ;
              let T : Set ℝ := Ioc (t₀ - ρ ^ (2 : ℕ)) t₀;
              ∀ᵐ (s : ℝ) ∂volume.restrict T,
                ∫⁻ (x : Vec3) in B, ENNReal.ofReal (vec3EuclideanNorm (u (x, s)) ^ (2 : ℕ)) ≤
                  ENNReal.ofReal (ρ * alpha u (x₀, t₀) ρ ^ (2 : ℕ))
    := by
  intro Ω I q u Du p f hsol x₀ t₀ ρ hρ hsub B T
  have heq := sws_timeSliceEnergyEssSup_eq_ofReal_alpha_sq hsol
    (x₀, t₀) hρ hsub
  rw [timeSliceEnergyEssSup] at heq
  have hae := ENNReal.ae_le_essSup (μ := volume.restrict T)
    (fun s => timeSliceBallEnergy x₀ ρ s (fun w => vec3EuclideanNorm (u w)))
  have htime : ∀ᵐ s ∂volume.restrict T,
      (∫⁻ x in B, ENNReal.ofReal ((vec3EuclideanNorm (u (x, s))) ^ (2 : ℕ))) ≤
        essSup (fun s => timeSliceBallEnergy x₀ ρ s
          (fun w => vec3EuclideanNorm (u w))) (volume.restrict T) := by
    filter_upwards [hae] with s hs
    calc
      (∫⁻ x in B, ENNReal.ofReal ((vec3EuclideanNorm (u (x, s))) ^ (2 : ℕ))) =
          ∫⁻ x in B, ‖vec3EuclideanNorm (u (x, s))‖ₑ ^ (2 : ℝ) := by
        apply lintegral_congr
        intro x
        rw [Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _),
          ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg _)
            (by norm_num)]
        norm_num [Real.rpow_natCast]
      _ ≤ essSup (fun s => timeSliceBallEnergy x₀ ρ s
          (fun w => vec3EuclideanNorm (u w))) (volume.restrict T) := by
        simpa [B, timeSliceBallEnergy] using hs
  rw [heq] at htime
  exact htime

private lemma caccioppoli_centered_hcenter_hgood_5 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {t₀ ρ : ℝ} (Ω' : Set Vec3) (J : Set ℝ),
          localBox Ω I Ω' J →
            (∀ s ∈ Ioc (t₀ - ρ ^ (2 : ℕ)) t₀, s ∈ J) →
              let T : Set ℝ := Ioc (t₀ - ρ ^ (2 : ℕ)) t₀;
              ∀ᵐ (s : ℝ) ∂volume.restrict T,
                (MemLp (fun (x : Vec3) => u (x, s)) (2 : ℝ≥0∞) (volume.restrict Ω') ∧
                    MemLp (fun (x : Vec3) => Du (x, s)) (2 : ℝ≥0∞) (volume.restrict Ω')) ∧
                  ∀ (i : Fin (3 : ℕ)),
                    HasWeakGradientOn Ω' (fun (x : Vec (3 : ℕ)) => u (x, s) i)
                      fun (x : Vec (3 : ℕ)) => Du (x, s) i
    := by
  intro Ω I q u Du p f hsol t₀ ρ Ω' J hbox hT T
  have hslice := slice_memLp_ae_of_sws hsol hbox
  have hgrad : ∀ i : Fin 3, ∀ᵐ s ∂volume.restrict J,
      HasWeakGradientOn Ω' (fun x => u (x, s) i)
        (fun x => Du (x, s) i) :=
    (hsol.2.2.2.2.2.1 Ω' J hbox).2.2.2.2.2.2.2.2
  have hgradAll : ∀ᵐ s ∂volume.restrict J, ∀ i : Fin 3,
      HasWeakGradientOn Ω' (fun x => u (x, s) i)
        (fun x => Du (x, s) i) := by
    rw [ae_all_iff]
    intro i
    exact hgrad i
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hT hslice,
    ae_restrict_of_ae_restrict_of_subset hT hgradAll] with s hs hg
  exact ⟨hs, hg⟩

private lemma caccioppoli_centered_hcenter_heInt_6 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {x₀ : Vec3} {t₀ ρ : ℝ}
      (Ω' : Set Vec3),
      let B : Set Vec3 := vec3Ball x₀ ρ;
      let T : Set ℝ := Ioc (t₀ - ρ ^ (2 : ℕ)) t₀;
      B ⊆ Ω' →
        (∀ᵐ (s : ℝ) ∂volume.restrict T,
            (MemLp (fun (x : Vec3) => u (x, s)) (2 : ℝ≥0∞) (volume.restrict Ω') ∧
                MemLp (fun (x : Vec3) => Du (x, s)) (2 : ℝ≥0∞) (volume.restrict Ω')) ∧
              ∀ (i : Fin (3 : ℕ)),
                HasWeakGradientOn Ω' (fun (x : Vec (3 : ℕ)) => u (x, s) i) fun (x : Vec (3 : ℕ)) =>
                  Du (x, s) i) →
          ∀ᵐ (s : ℝ) ∂volume.restrict T,
            IntegrableOn (fun (x : Vec3) => vec3EuclideanNorm (u (x, s)) ^ (2 : ℕ)) B volume
    := by
  intro u Du x₀ t₀ ρ Ω' B T hB hgood
  filter_upwards [hgood] with s hs
  let μ : Measure Vec3 := volume.restrict B
  have huB : MemLp (fun x : Vec3 => u (x, s)) 2 μ :=
    hs.1.1.mono_measure (Measure.restrict_mono_set volume hB)
  have hnorm : AEStronglyMeasurable
      (fun x : Vec3 => vec3EuclideanNorm (u (x, s))) μ := by
    exact continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      huB.aestronglyMeasurable
  have hsq : AEStronglyMeasurable
      (fun x : Vec3 => (vec3EuclideanNorm (u (x, s))) ^ (2 : ℕ)) μ :=
    hnorm.pow 2
  have hbound : ∀ᵐ x ∂μ,
      ‖(vec3EuclideanNorm (u (x, s))) ^ (2 : ℕ)‖ ≤
        3 * ‖u (x, s)‖ ^ (2 : ℕ) := by
    filter_upwards [] with x
    have hx := native_euclidean_norm_le_sqrt_three_norm (u (x, s))
    have hsqx := (sq_le_sq₀ (vec3EuclideanNorm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).2 hx
    calc
      ‖(vec3EuclideanNorm (u (x, s))) ^ (2 : ℕ)‖ =
          (vec3EuclideanNorm (u (x, s))) ^ (2 : ℕ) := by
            rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ ≤ (Real.sqrt 3 * ‖u (x, s)‖) ^ (2 : ℕ) := hsqx
      _ = 3 * ‖u (x, s)‖ ^ (2 : ℕ) := by
        rw [mul_pow, Real.sq_sqrt (by norm_num)]
  exact Integrable.mono' ((huB.integrable_norm_pow (by norm_num)).const_mul (3 : ℝ))
    hsq hbound

private lemma caccioppoli_centered_hcenter_hdInt_7 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {x₀ : Vec3} {t₀ ρ : ℝ}
      (Ω' : Set Vec3),
      let B : Set Vec3 := vec3Ball x₀ ρ;
      let T : Set ℝ := Ioc (t₀ - ρ ^ (2 : ℕ)) t₀;
      B ⊆ Ω' →
        AEMeasurable
            (fun (s : ℝ) => ∫⁻ (x : Vec3) in B, ENNReal.ofReal (spatialGradientSq u Du (x, s)))
            (volume.restrict T) →
          (∀ᵐ (s : ℝ) ∂volume.restrict T,
              (MemLp (fun (x : Vec3) => u (x, s)) (2 : ℝ≥0∞) (volume.restrict Ω') ∧
                  MemLp (fun (x : Vec3) => Du (x, s)) (2 : ℝ≥0∞) (volume.restrict Ω')) ∧
                ∀ (i : Fin (3 : ℕ)),
                  HasWeakGradientOn Ω' (fun (x : Vec (3 : ℕ)) => u (x, s) i)
                    fun (x : Vec (3 : ℕ)) => Du (x, s) i) →
            ∀ᵐ (s : ℝ) ∂volume.restrict T,
              IntegrableOn (fun (x : Vec3) => spatialGradientSq u Du (x, s)) B volume
    := by
  intro u Du x₀ t₀ ρ Ω' B T hB hDmeas hgood
  filter_upwards [hgood] with s hs
  let μ : Measure Vec3 := volume.restrict B
  have hDuB : MemLp (fun x : Vec3 => Du (x, s)) 2 μ :=
    hs.1.2.mono_measure (Measure.restrict_mono_set volume hB)
  have hDu : AEStronglyMeasurable (fun x : Vec3 => Du (x, s)) μ :=
    hDuB.aestronglyMeasurable
  have hDmeas : AEStronglyMeasurable
      (fun x : Vec3 => spatialGradientSq u Du (x, s)) μ := by
    have hcont : Continuous (fun v : Fin 3 → Vec3 =>
        ∑ i : Fin 3, ∑ j : Fin 3, (v i j) ^ (2 : ℕ)) := by fun_prop
    simpa only [spatialGradientSq] using hcont.comp_aestronglyMeasurable hDu
  have hbound : ∀ᵐ x ∂μ,
      ‖spatialGradientSq u Du (x, s)‖ ≤ 9 * ‖Du (x, s)‖ ^ (2 : ℕ) := by
    filter_upwards [] with x
    have hterm : ∀ i : Fin 3, ∀ j : Fin 3,
        (Du (x, s) i j) ^ (2 : ℕ) ≤ ‖Du (x, s)‖ ^ (2 : ℕ) := by
      intro i j
      rw [← sq_abs]
      apply pow_le_pow_left₀ (abs_nonneg _)
      exact le_trans (norm_le_pi_norm (Du (x, s) i) j)
        (norm_le_pi_norm (Du (x, s)) i)
    have hsum : spatialGradientSq u Du (x, s) ≤
        ∑ i : Fin 3, ∑ j : Fin 3, ‖Du (x, s)‖ ^ (2 : ℕ) := by
      unfold spatialGradientSq
      exact Finset.sum_le_sum (fun i _ =>
        Finset.sum_le_sum (fun j _ => hterm i j))
    calc
      ‖spatialGradientSq u Du (x, s)‖ = spatialGradientSq u Du (x, s) := by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        unfold spatialGradientSq
        positivity
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖Du (x, s)‖ ^ (2 : ℕ) := hsum
      _ = 9 * ‖Du (x, s)‖ ^ (2 : ℕ) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
  exact Integrable.mono' ((hDuB.integrable_norm_pow (by norm_num)).const_mul (9 : ℝ))
    hDmeas hbound

private lemma caccioppoli_centered_hcenter_hFiter_8 :
    ∀ {u : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ : ℝ} (J : Set ℝ),
      let B : Set Vec3 := vec3Ball x₀ ρ;
      let T : Set ℝ := Ioc (t₀ - ρ ^ (2 : ℕ)) t₀;
      T ⊆ J →
        AEMeasurable (fun (z : Vec3 × ℝ) => ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ))
            ((volume.restrict B).prod (volume.restrict J)) →
          ∫⁻ (s : ℝ) in T,
              ∫⁻ (x : Vec3) in B, ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ) =
            ∫⁻ (z : ParabolicPoint) in parabolicCylinder x₀ t₀ ρ,
              ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ)
    := by
  intro u x₀ t₀ ρ J B T hT' hFprod
  symm
  apply lintegral_parabolicCylinder
  have hFprod' := hFprod
  rw [Measure.prod_restrict] at hFprod'
  rw [volume_parabolicPoint_eq_prod]
  exact hFprod'.mono_measure
    (Measure.restrict_mono (μ := volume.prod volume) (ν := volume.prod volume)
      (by
        intro z hz
        exact ⟨hz.1, hT' hz.2⟩) le_rfl)

private lemma caccioppoli_centered_hcenter_h3Int_9 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {x₀ : Vec3} {t₀ ρ : ℝ}
      (Ω' : Set Vec3),
      let B : Set Vec3 := vec3Ball x₀ ρ;
      let T : Set ℝ := Ioc (t₀ - ρ ^ (2 : ℕ)) t₀;
      B ⊆ Ω' →
        (∀ᵐ (s : ℝ) ∂volume.restrict T,
            (MemLp (fun (x : Vec3) => u (x, s)) (2 : ℝ≥0∞) (volume.restrict Ω') ∧
                MemLp (fun (x : Vec3) => Du (x, s)) (2 : ℝ≥0∞) (volume.restrict Ω')) ∧
              ∀ (i : Fin (3 : ℕ)),
                HasWeakGradientOn Ω' (fun (x : Vec (3 : ℕ)) => u (x, s) i) fun (x : Vec (3 : ℕ)) =>
                  Du (x, s) i) →
          (∀ᵐ (s : ℝ) ∂volume.restrict T,
              ∫⁻ (x : Vec3) in B, ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ) ≠ ∞) →
            ∀ᵐ (s : ℝ) ∂volume.restrict T,
              IntegrableOn (fun (x : Vec3) => vec3EuclideanNorm (u (x, s)) ^ (3 : ℝ)) B volume
    := by
  intro u Du x₀ t₀ ρ Ω' B T hB hgood hFsliceTop
  filter_upwards [hFsliceTop, hgood] with s htop hs
  let μ : Measure Vec3 := volume.restrict B
  have huB : MemLp (fun x : Vec3 => u (x, s)) 2 μ :=
    hs.1.1.mono_measure (Measure.restrict_mono_set volume hB)
  have hnorm : AEStronglyMeasurable
      (fun x : Vec3 => vec3EuclideanNorm (u (x, s))) μ :=
    continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      huB.aestronglyMeasurable
  have hmeas : AEMeasurable
      (fun x : Vec3 => (vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ)) μ :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3)).comp_aestronglyMeasurable
      hnorm |>.aemeasurable
  have heq : (∫⁻ x in B,
      ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ)) =
      ∫⁻ x in B, ENNReal.ofReal
        ((vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ)) := by
    apply lintegral_congr
    intro x
    rw [ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg _)
      (by norm_num)]
  have hfin : (∫⁻ x in B, ENNReal.ofReal
      ((vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ))) ≠ ∞ := by
    rw [← heq]
    exact htop
  have hi := (lintegral_ofReal_ne_top_iff_integrable hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x =>
      Real.rpow_nonneg (vec3EuclideanNorm_nonneg _) _))).mp hfin
  change Integrable (fun x : Vec3 =>
    (vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ)) (volume.restrict B)
  simpa [μ] using hi

private lemma caccioppoli_centered_hcenter_hgInt_10 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {x₀ : Vec3} {t₀ ρ : ℝ}
      (Ω' : Set Vec3),
      let B : Set Vec3 := vec3Ball x₀ ρ;
      let T : Set ℝ := Ioc (t₀ - ρ ^ (2 : ℕ)) t₀;
      B ⊆ Ω' →
        let c : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
          ⨍ (x : Vec3) in B, vec3EuclideanNorm (u (x, z.2)) ^ (2 : ℕ);
        (∀ᵐ (s : ℝ) ∂volume.restrict T,
            (MemLp (fun (x : Vec3) => u (x, s)) (2 : ℝ≥0∞) (volume.restrict Ω') ∧
                MemLp (fun (x : Vec3) => Du (x, s)) (2 : ℝ≥0∞) (volume.restrict Ω')) ∧
              ∀ (i : Fin (3 : ℕ)),
                HasWeakGradientOn Ω' (fun (x : Vec (3 : ℕ)) => u (x, s) i) fun (x : Vec (3 : ℕ)) =>
                  Du (x, s) i) →
          (∀ᵐ (s : ℝ) ∂volume.restrict T,
              IntegrableOn (fun (x : Vec3) => vec3EuclideanNorm (u (x, s)) ^ (3 : ℝ)) B volume) →
            ∀ᵐ (s : ℝ) ∂volume.restrict T,
              IntegrableOn
                (fun (x : Vec3) =>
                  |vec3EuclideanNorm (u (x, s)) ^ (2 : ℕ) - c (x, s)| ^ (3 / 2 : ℝ))
                B volume
    := by
  intro u Du x₀ t₀ ρ Ω' B T hB c hgood h3Int
  filter_upwards [h3Int, hgood] with s h3 hs
  let μ : Measure Vec3 := volume.restrict B
  have huB : MemLp (fun x : Vec3 => u (x, s)) 2 μ :=
    hs.1.1.mono_measure (Measure.restrict_mono_set volume hB)
  have hnorm : AEStronglyMeasurable
      (fun x : Vec3 => vec3EuclideanNorm (u (x, s))) μ := by
    exact continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      huB.aestronglyMeasurable
  have ha32 : Integrable (fun x : Vec3 =>
      ((vec3EuclideanNorm (u (x, s))) ^ 2) ^ (3 / 2 : ℝ)) μ := by
    have heq : (fun x : Vec3 =>
        ((vec3EuclideanNorm (u (x, s))) ^ 2) ^ (3 / 2 : ℝ)) =
        (fun x : Vec3 => (vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ)) := by
      funext x
      rw [← Real.rpow_natCast, ← Real.rpow_mul
        (vec3EuclideanNorm_nonneg _)]
      norm_num
    rw [heq]
    change Integrable (fun x : Vec3 =>
      (vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ)) (volume.restrict B) at h3
    exact h3
  have hcint : Integrable (fun _ : Vec3 =>
      |c (x₀, s)| ^ (3 / 2 : ℝ)) μ := by
    dsimp [μ]
    exact integrableOn_const (volume_vec3Ball_lt_top (x := x₀) (r := ρ)).ne
  have hmajor : Integrable (fun x : Vec3 =>
      (2 : ℝ) ^ (1 / 2 : ℝ) *
        (((vec3EuclideanNorm (u (x, s))) ^ 2) ^ (3 / 2 : ℝ) +
          |c (x₀, s)| ^ (3 / 2 : ℝ))) μ :=
    (ha32.add hcint).const_mul ((2 : ℝ) ^ (1 / 2 : ℝ))
  have hmeas : AEMeasurable (fun x : Vec3 =>
      |(vec3EuclideanNorm (u (x, s))) ^ 2 - c (x, s)| ^ (3 / 2 : ℝ)) μ := by
    have hsq : AEMeasurable (fun x : Vec3 =>
        (vec3EuclideanNorm (u (x, s))) ^ 2) μ :=
      hnorm.pow 2 |>.aemeasurable
    have habs : AEMeasurable (fun x : Vec3 =>
        |(vec3EuclideanNorm (u (x, s))) ^ 2 - c (x, s)|) μ :=
      continuous_abs.measurable.comp_aemeasurable
        (hsq.sub
          (measurable_const : Measurable (fun _ : Vec3 => c (x₀, s))).aemeasurable)
    have hpow := (Real.continuous_rpow_const
      (by norm_num : (0 : ℝ) ≤ 3 / 2)).comp_aestronglyMeasurable
      habs.aestronglyMeasurable
    exact hpow.aemeasurable
  apply Integrable.mono' hmajor hmeas.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    |(vec3EuclideanNorm (u (x, s))) ^ 2 - c (x, s)| ^ (3 / 2 : ℝ) ≤
        ((vec3EuclideanNorm (u (x, s))) ^ 2 + |c (x₀, s)|) ^
          (3 / 2 : ℝ) := by
      have hcxs : c (x, s) = c (x₀, s) := by rfl
      have hnon : 0 ≤ (vec3EuclideanNorm (u (x, s))) ^ (2 : ℕ) :=
        sq_nonneg _
      rw [hcxs]
      have hdiff : |(vec3EuclideanNorm (u (x, s))) ^ 2 - c (x₀, s)| ≤
          (vec3EuclideanNorm (u (x, s))) ^ 2 + |c (x₀, s)| := by
        calc
          |(vec3EuclideanNorm (u (x, s))) ^ 2 - c (x₀, s)| ≤
              |(vec3EuclideanNorm (u (x, s))) ^ 2 - 0| +
                |0 - c (x₀, s)| :=
            abs_sub_le ((vec3EuclideanNorm (u (x, s))) ^ 2) 0 (c (x₀, s))
          _ = (vec3EuclideanNorm (u (x, s))) ^ 2 + |c (x₀, s)| := by
            rw [sub_zero, abs_of_nonneg hnon, zero_sub, abs_neg]
      exact Real.rpow_le_rpow (abs_nonneg _) hdiff (by norm_num)
    _ ≤ (2 : ℝ) ^ (1 / 2 : ℝ) *
        (((vec3EuclideanNorm (u (x, s))) ^ 2) ^ (3 / 2 : ℝ) +
          |c (x₀, s)| ^ (3 / 2 : ℝ)) :=
      caccioppoli_real_rpow_add_bound _ _ (by positivity) (abs_nonneg _)

private lemma caccioppoli_centered_hcenter_hc_cyl_11 :
    ∀ {u : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ : ℝ} (J : Set ℝ),
      let B : Set Vec3 := vec3Ball x₀ ρ;
      let T : Set ℝ := Ioc (t₀ - ρ ^ (2 : ℕ)) t₀;
      T ⊆ J →
        let c : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
          ⨍ (x : Vec3) in B, vec3EuclideanNorm (u (x, z.2)) ^ (2 : ℕ);
        AEMeasurable (fun (s : ℝ) => c (x₀, s)) (volume.restrict J) →
          AEMeasurable (fun (w : ParabolicPoint) => c w)
            (volume.restrict (parabolicCylinder x₀ t₀ ρ))
    := by
  intro u x₀ t₀ ρ J B T hT' c hc
  have hcProd' : AEMeasurable (fun z : Vec3 × ℝ => c z)
      ((volume.restrict B).prod (volume.restrict J)) := by
    have hcc : AEMeasurable (fun z : Vec3 × ℝ => c (x₀, z.2))
        ((volume.restrict B).prod (volume.restrict J)) := hc.comp_snd
    simpa only [c] using hcc
  rw [Measure.prod_restrict] at hcProd'
  rw [volume_parabolicPoint_eq_prod]
  exact hcProd'.mono_measure
    (Measure.restrict_mono (μ := volume.prod volume) (ν := volume.prod volume)
      (by
        intro z hz
        exact ⟨hz.1, hT' hz.2⟩) le_rfl)

private lemma caccioppoli_centered_hcenter_hcenterFinal_12 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {x₀ : Vec3} {t₀ ρ : ℝ},
      (0 : ℝ) < ρ →
        let B : Set Vec3 := vec3Ball x₀ ρ;
        let T : Set ℝ := Ioc (t₀ - ρ ^ (2 : ℕ)) t₀;
        let c : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
          ⨍ (x : Vec3) in B, vec3EuclideanNorm (u (x, z.2)) ^ (2 : ℕ);
        (∫⁻ (s : ℝ) in T,
                ∫⁻ (x : Vec3) in B,
                  ENNReal.ofReal
                    (|vec3EuclideanNorm (u (x, s)) ^ (2 : ℕ) - c (x, s)| ^ (3 / 2 : ℝ))) ^
              (2 / 3 : ℝ) ≤
            ENNReal.ofReal poincareSobolevL1VectorConstant *
                  ENNReal.ofReal (ρ * alpha u (x₀, t₀) ρ ^ (2 : ℕ)) ^ (1 / 2 : ℝ) *
                ENNReal.ofReal (ρ * beta u Du (x₀, t₀) ρ ^ (2 : ℕ)) ^ (1 / 2 : ℝ) *
              ENNReal.ofReal (ρ ^ (2 : ℕ)) ^ (1 / 6 : ℝ) →
          ∫⁻ (s : ℝ) in T,
                ∫⁻ (x : Vec3) in B,
                  ENNReal.ofReal |vec3EuclideanNorm (u (x, s)) ^ (2 : ℕ) - c (x, s)| ^ (3 / 2 : ℝ) =
              ∫⁻ (w : ParabolicPoint) in parabolicCylinder x₀ t₀ ρ,
                ENNReal.ofReal |vec3EuclideanNorm (u w) ^ (2 : ℕ) - c w| ^ (3 / 2 : ℝ) →
            (∫⁻ (w : ParabolicPoint) in parabolicCylinder x₀ t₀ ρ,
                  ENNReal.ofReal |vec3EuclideanNorm (u w) ^ (2 : ℕ) - c w| ^ (3 / 2 : ℝ)) ^
                (2 / 3 : ℝ) ≤
              ENNReal.ofReal
                (poincareSobolevL1VectorConstant * ρ ^ (4 / 3 : ℝ) * alpha u (x₀, t₀) ρ *
                  beta u Du (x₀, t₀) ρ)
    := by
  intro u Du x₀ t₀ ρ hρ B T c hcenter hcenter_iter
  rw [← hcenter_iter]
  have hcenter_integrand :
      (∫⁻ s in T, ∫⁻ x in B, ENNReal.ofReal
        |(vec3EuclideanNorm (u (x, s))) ^ 2 - c (x, s)| ^ (3 / 2 : ℝ)) =
      (∫⁻ s in T, ∫⁻ x in B, ENNReal.ofReal
        (|(vec3EuclideanNorm (u (x, s))) ^ 2 - c (x, s)| ^ (3 / 2 : ℝ))) := by
    apply lintegral_congr_ae
    filter_upwards [] with s
    apply lintegral_congr_ae
    filter_upwards [] with x
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
  have hcenter' :
      (∫⁻ s in T, ∫⁻ x in B, ENNReal.ofReal
        |(vec3EuclideanNorm (u (x, s))) ^ 2 - c (x, s)| ^ (3 / 2 : ℝ)) ^
          (2 / 3 : ℝ) ≤
        ENNReal.ofReal poincareSobolevL1VectorConstant *
            ENNReal.ofReal (ρ * alpha u (x₀, t₀) ρ ^ 2) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (ρ * beta u Du (x₀, t₀) ρ ^ 2) ^ (1 / 2 : ℝ) *
            ENNReal.ofReal (ρ ^ 2) ^ (1 / 6 : ℝ) := by
    rw [hcenter_integrand]
    exact hcenter
  calc
    (∫⁻ s in T, ∫⁻ x in B, ENNReal.ofReal
        |(vec3EuclideanNorm (u (x, s))) ^ 2 - c (x, s)| ^ (3 / 2 : ℝ)) ^
        (2 / 3 : ℝ) ≤
      ENNReal.ofReal poincareSobolevL1VectorConstant *
          ENNReal.ofReal (ρ * alpha u (x₀, t₀) ρ ^ 2) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal (ρ * beta u Du (x₀, t₀) ρ ^ 2) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal (ρ ^ 2) ^ (1 / 6 : ℝ) := hcenter'
    _ = ENNReal.ofReal (poincareSobolevL1VectorConstant *
        ρ ^ (4 / 3 : ℝ) * alpha u (x₀, t₀) ρ * beta u Du (x₀, t₀) ρ) := by
      apply caccioppoli_centered_rhs_eq
      · exact (by
          rw [poincareSobolevL1VectorConstant]
          exact mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
            ENNReal.toReal_nonneg)
      · exact hρ
      · unfold alpha
        positivity
      · unfold beta
        positivity

private lemma caccioppoli_centered_hcenter_hmean_slice_13 :
    ∀ {u : ParabolicPoint → Vec3} {_ : ParabolicPoint → ℝ} {x₀ : Vec3} {t₀ ρ : ℝ},
      let B : Set Vec3 := vec3Ball x₀ ρ;
      let T : Set ℝ := Ioc (t₀ - ρ ^ (2 : ℕ)) t₀;
      let c : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        ⨍ (x : Vec3) in B, vec3EuclideanNorm (u (x, z.2)) ^ (2 : ℕ);
      (∀ᵐ (s : ℝ) ∂volume.restrict T,
          IntegrableOn (fun (x : Vec3) => vec3EuclideanNorm (u (x, s)) ^ (2 : ℕ)) B volume) →
        (∀ᵐ (s : ℝ) ∂volume.restrict T,
            IntegrableOn (fun (x : Vec3) => vec3EuclideanNorm (u (x, s)) ^ (3 : ℝ)) B volume) →
          (volume : Set Vec3 → ℝ≥0∞) B ≠ (0 : ℝ≥0∞) →
            (volume : Set Vec3 → ℝ≥0∞) B ≠ ∞ →
              (∀ (w : ParabolicPoint), (0 : ℝ) ≤ c w) →
                ∀ᵐ (s : ℝ) ∂volume.restrict T,
                  ENNReal.ofReal (c (x₀, s)) ^ (3 / 2 : ℝ) * (volume : Set Vec3 → ℝ≥0∞) B ≤
                    ∫⁻ (x : Vec3) in B, ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ)
    := by
  intro u p x₀ t₀ ρ B T c heInt h3Int hB0 hBtop hc_nonneg
  filter_upwards [h3Int, heInt] with s hs3 hs2
  have hJ := (convexOn_rpow (p := (3 / 2 : ℝ)) (by norm_num)).map_set_average_le
    (Real.continuous_rpow_const (by norm_num)).continuousOn isClosed_Ici hB0 hBtop
    (by
      filter_upwards [] with x
      exact sq_nonneg (vec3EuclideanNorm (u (x, s))))
    hs2 (by
      have heq : (fun x : Vec3 =>
          ((vec3EuclideanNorm (u ((x, s) : ParabolicPoint))) ^ (2 : ℕ)) ^
            (3 / 2 : ℝ)) =
          (fun x : Vec3 => (vec3EuclideanNorm (u ((x, s) : ParabolicPoint))) ^
            (3 : ℝ)) := by
        funext x
        rw [← Real.rpow_natCast, ← Real.rpow_mul
          (vec3EuclideanNorm_nonneg _)]
        norm_num
      change IntegrableOn (fun x : Vec3 =>
        ((vec3EuclideanNorm (u ((x, s) : ParabolicPoint))) ^ (2 : ℕ)) ^
          (3 / 2 : ℝ)) B volume
      rw [heq]
      exact hs3)
  have hJ2 : (⨍ x in B,
      (vec3EuclideanNorm (u ((x, s) : ParabolicPoint))) ^ (2 : ℕ)) ^
        (3 / 2 : ℝ) ≤
      ⨍ x in B, (vec3EuclideanNorm (u ((x, s) : ParabolicPoint))) ^
        (3 : ℝ) := by
    calc
      _ ≤ ⨍ x in B, (vec3EuclideanNorm
          (u ((x, s) : ParabolicPoint)) ^ (2 : ℕ)) ^ (3 / 2 : ℝ) := hJ
      _ = _ := by
        apply average_congr
        filter_upwards [] with x
        rw [← Real.rpow_natCast, ← Real.rpow_mul
          (vec3EuclideanNorm_nonneg _)]
        norm_num
  have hJ' : (c ((x₀, s) : ParabolicPoint)) ^ (3 / 2 : ℝ) ≤
      ⨍ x in B, (vec3EuclideanNorm (u ((x, s) : ParabolicPoint))) ^
        (3 : ℝ) := by
    simpa only [c, Function.comp_apply] using hJ2
  have hJ'' : ENNReal.ofReal (c ((x₀, s) : ParabolicPoint) ^ (3 / 2 : ℝ)) ≤
      ENNReal.ofReal (⨍ x in B,
        (vec3EuclideanNorm (u ((x, s) : ParabolicPoint))) ^ (3 : ℝ)) :=
    ENNReal.ofReal_le_ofReal hJ'
  have hAvg := MeasureTheory.ofReal_setAverage hs3
    (by
      filter_upwards [] with x
      exact Real.rpow_nonneg (vec3EuclideanNorm_nonneg _) _)
  calc
    ENNReal.ofReal (c ((x₀, s) : ParabolicPoint)) ^ (3 / 2 : ℝ) * volume B =
        ENNReal.ofReal (c ((x₀, s) : ParabolicPoint) ^ (3 / 2 : ℝ)) * volume B := by
          exact congrArg (fun y : ℝ≥0∞ => y * volume B)
            (ENNReal.ofReal_rpow_of_nonneg
              (hc_nonneg ((x₀, s) : ParabolicPoint)) (by norm_num))
    _ ≤ ENNReal.ofReal (⨍ x in B,
        (vec3EuclideanNorm (u ((x, s) : ParabolicPoint))) ^ (3 : ℝ)) * volume B :=
      mul_le_mul_left hJ'' _
    _ = (∫⁻ x in B, ENNReal.ofReal
        ((vec3EuclideanNorm (u ((x, s) : ParabolicPoint))) ^ (3 : ℝ))) /
          volume B * volume B := by
      rw [hAvg]
    _ = ∫⁻ x in B, ENNReal.ofReal (vec3EuclideanNorm (u ((x, s) : ParabolicPoint))) ^
        (3 : ℝ) := by
      rw [ENNReal.div_mul_cancel hB0 hBtop]
      apply lintegral_congr_ae
      filter_upwards [] with x
      rw [ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg _)
        (by norm_num)]

private lemma caccioppoli_centered_hcenter_hmeanFinal_14 :
    ∀ {u : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ : ℝ},
      (0 : ℝ) < ρ →
        let B : Set Vec3 := vec3Ball x₀ ρ;
        let T : Set ℝ := Ioc (t₀ - ρ ^ (2 : ℕ)) t₀;
        let c : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
          ⨍ (x : Vec3) in B, vec3EuclideanNorm (u (x, z.2)) ^ (2 : ℕ);
        ∫⁻ (s : ℝ) in T,
              ∫⁻ (x : Vec3) in B, ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ) =
            ∫⁻ (z : ParabolicPoint) in parabolicCylinder x₀ t₀ ρ,
              ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) →
          ∫⁻ (s : ℝ) in T,
                ∫⁻ (x : Vec3) in B, ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ) ≠
              ∞ →
            AEMeasurable (fun (w : ParabolicPoint) => c w)
                (volume.restrict (parabolicCylinder x₀ t₀ ρ)) →
              ∫⁻ (s : ℝ) in T,
                    ENNReal.ofReal (c (x₀, s)) ^ (3 / 2 : ℝ) * (volume : Set Vec3 → ℝ≥0∞) B ≤
                  ∫⁻ (s : ℝ) in T,
                    ∫⁻ (x : Vec3) in B, ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ) →
                ∫⁻ (w : ParabolicPoint) in parabolicCylinder x₀ t₀ ρ,
                    ENNReal.ofReal (c w) ^ (3 / 2 : ℝ) ≤
                  ENNReal.ofReal (ρ ^ (2 : ℕ) * gamma u (x₀, t₀) ρ ^ (3 : ℕ))
    := by
  intro u x₀ t₀ ρ hρ B T c hFiter hFtop hc_cyl hmean_prod
  have hcc' : ∀ w : ParabolicPoint, c w = c (x₀, w.2) := by
    intro w
    rfl
  have hconst : ∀ s : ℝ, (∫⁻ x in B,
      ENNReal.ofReal (c ((x, s) : ParabolicPoint)) ^ (3 / 2 : ℝ)) =
      ENNReal.ofReal (c ((x₀, s) : ParabolicPoint)) ^ (3 / 2 : ℝ) * volume B := by
    intro s
    have heq : (fun x : Vec3 => ENNReal.ofReal (c ((x, s) : ParabolicPoint)) ^
        (3 / 2 : ℝ)) = (fun _ : Vec3 =>
        ENNReal.ofReal (c ((x₀, s) : ParabolicPoint)) ^ (3 / 2 : ℝ)) := by
      funext x
      rw [show c ((x, s) : ParabolicPoint) =
        c ((x₀, s) : ParabolicPoint) by rfl]
    rw [heq, setLIntegral_const]
  calc
    (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal (c w) ^ (3 / 2 : ℝ)) =
        ∫⁻ s in T, ∫⁻ x in B,
          ENNReal.ofReal (c ((x, s) : ParabolicPoint)) ^ (3 / 2 : ℝ) := by
      apply lintegral_parabolicCylinder
      exact ((ENNReal.continuous_ofReal.measurable.comp_aemeasurable hc_cyl).pow_const
        (3 / 2 : ℝ))
    _ = ∫⁻ s in T, ENNReal.ofReal (c ((x₀, s) : ParabolicPoint)) ^
        (3 / 2 : ℝ) * volume B := by
      apply lintegral_congr_ae
      filter_upwards [] with s
      exact hconst s
    _ ≤ ∫⁻ s in T, ∫⁻ x in B,
        ENNReal.ofReal (vec3EuclideanNorm (u ((x, s) : ParabolicPoint))) ^
          (3 : ℝ) :=
      hmean_prod
    _ = ∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) := hFiter
    _ = ENNReal.ofReal (ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3) := by
      have hvtop : (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
          ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ∞ := by
        rw [← hFiter]
        exact hFtop
      exact caccioppoli_I2_velocity_integral_identity
        (u := u) (z := (x₀, t₀)) (ρ := ρ) hρ hvtop

private lemma caccioppoli_centered_hcenter_huProd_1 :
    ∀ {u : ParabolicPoint → Vec3} {x₀ : Vec3} {ρ : ℝ} (Ω' : Set Vec3) (J : Set ℝ),
      let B : Set Vec3 := vec3Ball x₀ ρ;
      B ⊆ Ω' →
        AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) u
            (Measure.restrict volume (spaceTimeSet Ω' J)) →
          AEStronglyMeasurable (m₀ := Prod.instMeasurableSpace) u
            (Measure.prod (Measure.restrict volume B) (Measure.restrict volume J))
    := by
  intro u x₀ ρ Ω' J B hB hu0
  have huWide : AEStronglyMeasurable u
      ((volume.restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    exact hu0
  exact huWide.mono_measure
    (Measure.prod_mono (Measure.restrict_mono_set volume hB) le_rfl)

private lemma caccioppoli_centered_hcenter_hsqProd_2 :
    ∀ {u : ParabolicPoint → Vec3} {x₀ : Vec3} {ρ : ℝ} (J : Set ℝ),
      let B : Set Vec3 := vec3Ball x₀ ρ;
      AEStronglyMeasurable (β := ℝ) (m₀ := Prod.instMeasurableSpace)
          (fun (z : Vec3 × ℝ) => vec3EuclideanNorm (u z))
          (Measure.prod (Measure.restrict volume B) (Measure.restrict volume J)) →
        AEStronglyMeasurable (β := ℝ) (m₀ := Prod.instMeasurableSpace)
          (fun (z : Vec3 × ℝ) => vec3EuclideanNorm (u z) ^ (2 : ℕ))
          (Measure.prod (Measure.restrict volume B) (Measure.restrict volume J))
    := by
  intro u x₀ ρ J B hnormProd
  have h := hnormProd.pow 2
  have heq : (fun z : Vec3 × ℝ => (vec3EuclideanNorm (u z)) ^ (2 : ℕ)) =
      (fun z : Vec3 × ℝ => vec3EuclideanNorm (u z)) ^ (2 : ℕ) := by
    funext z
    simp only [Pi.pow_apply]
  rw [heq]
  exact h

private lemma caccioppoli_centered_hcenter_hA_3 :
    ∀ {u : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ : ℝ} (J : Set ℝ),
      let B : Set Vec3 := vec3Ball x₀ ρ;
      let T : Set ℝ := Ioc (t₀ - ρ ^ (2 : ℕ)) t₀;
      T ⊆ J →
        let c : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
          ⨍ (x : Vec3) in B, vec3EuclideanNorm (u (x, z.2)) ^ (2 : ℕ);
        AEMeasurable (β := ℝ≥0∞) (_m := Prod.instMeasurableSpace)
            (fun (z : Vec3 × ℝ) =>
              ENNReal.ofReal
                |vec3EuclideanNorm (u z) ^ (2 : ℕ) -
                    (fun (z : ParabolicPoint) =>
                        (⨍ (x : Vec3) in vec3Ball x₀ ρ, vec3EuclideanNorm (u (x, z.2)) ^ (2 : ℕ) :
                          ℝ))
                      (z.1, z.2)|)
            (Measure.prod (Measure.restrict volume (vec3Ball x₀ ρ)) (Measure.restrict volume J)) →
          AEMeasurable (β := ℝ≥0∞) (_m := MeasureSpace.toMeasurableSpace)
            (fun (w : ParabolicPoint) => ENNReal.ofReal |vec3EuclideanNorm (u w) ^ (2 : ℕ) - c w|)
            (Measure.restrict volume (parabolicCylinder x₀ t₀ ρ))
    := by
  intro u x₀ t₀ ρ J B T hT' c habsProd
  have habsProd' := habsProd
  rw [Measure.prod_restrict] at habsProd'
  rw [volume_parabolicPoint_eq_prod]
  exact habsProd'.mono_measure
    (Measure.restrict_mono (μ := volume.prod volume) (ν := volume.prod volume)
      (by
        intro z hz
        exact ⟨hz.1, hT' hz.2⟩) le_rfl)

private lemma caccioppoli_centered_hcenter_hDmeas_4 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {x₀ : Vec3} {t₀ ρ : ℝ}
      (J : Set ℝ),
      let B : Set Vec3 := vec3Ball x₀ ρ;
      let T : Set ℝ := Ioc (t₀ - ρ ^ (2 : ℕ)) t₀;
      T ⊆ J →
        AEStronglyMeasurable (m₀ := Prod.instMeasurableSpace) Du
            (Measure.prod (Measure.restrict volume B) (Measure.restrict volume J)) →
          AEMeasurable (β := ℝ≥0∞) (_m := MeasureSpace.toMeasurableSpace)
            (fun (s : ℝ) => ∫⁻ (x : Vec3) in B, ENNReal.ofReal (spatialGradientSq u Du (x, s)))
            (Measure.restrict volume T)
    := by
  intro u Du x₀ t₀ ρ J B T hT' hDuProd
  have hsum : Continuous (fun v : Fin 3 → Vec3 =>
      ENNReal.ofReal (∑ i : Fin 3, ∑ j : Fin 3, (v i j) ^ (2 : ℕ))) := by
    exact ENNReal.continuous_ofReal.comp (by fun_prop)
  have hDprod : AEMeasurable (fun z : Vec3 × ℝ =>
      ENNReal.ofReal (spatialGradientSq u Du z))
      ((volume.restrict B).prod (volume.restrict J)) := by
    exact (hsum.comp_aestronglyMeasurable hDuProd).aemeasurable
  exact hDprod.lintegral_prod_left'.mono_measure
    (Measure.restrict_mono_set volume hT')

private lemma caccioppoli_centered_hcenter_hDint_5 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {x₀ : Vec3} {t₀ ρ : ℝ},
          (0 : ℝ) < ρ →
            closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I →
              let B : Set Vec3 := vec3Ball x₀ ρ;
              let T : Set ℝ := Ioc (t₀ - ρ ^ (2 : ℕ)) t₀;
              AEMeasurable (β := ℝ≥0∞) (_m := MeasureSpace.toMeasurableSpace)
                  (fun (z : ParabolicPoint) => ENNReal.ofReal (spatialGradientSq u Du z))
                  (Measure.restrict volume (parabolicCylinder x₀ t₀ ρ)) →
                ∫⁻ (s : ℝ) in T,
                    ∫⁻ (x : Vec3) in B, ENNReal.ofReal (spatialGradientSq u Du (x, s)) ≤
                  ENNReal.ofReal (ρ * beta u Du (x₀, t₀) ρ ^ (2 : ℕ))
    := by
  intro Ω I q u Du p f hsol x₀ t₀ ρ hρ hsub B T hD_cyl
  rw [show (∫⁻ s in T, ∫⁻ x in B,
      ENNReal.ofReal (spatialGradientSq u Du (x, s))) =
      ∫⁻ z in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal (spatialGradientSq u Du z) by
    symm
    apply lintegral_parabolicCylinder
    exact hD_cyl]
  exact le_rfl.trans_eq (sws_lintegral_spatialGradientSq_eq_ofReal_beta_sq
    hsol (x₀, t₀) hρ hsub)

theorem caccioppoli_centered_hcenter
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I) :
    ∃ c : ParabolicPoint → ℝ,
      AEMeasurable (fun w => ENNReal.ofReal
        |(vec3EuclideanNorm (u w)) ^ 2 - c w|)
        (volume.restrict (parabolicCylinder x₀ t₀ ρ)) ∧
      AEMeasurable (fun w => c w)
        (volume.restrict (parabolicCylinder x₀ t₀ ρ)) ∧
      (∀ w : ParabolicPoint, c w = c (x₀, w.2)) ∧
      (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal |(vec3EuclideanNorm (u w)) ^ 2 - c w| ^
          (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
        ENNReal.ofReal (poincareSobolevL1VectorConstant * ρ ^ (4 / 3 : ℝ) *
          alpha u (x₀, t₀) ρ * beta u Du (x₀, t₀) ρ) ∧
      (∀ w, 0 ≤ c w) ∧
      (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal (c w) ^ (3 / 2 : ℝ)) ≤
        ENNReal.ofReal (ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3) := by
  obtain ⟨R, Ω', J, hρR, hbox, hball, hT, hpoint⟩ :=
    caccioppoli_slice_poincare_ae hsol hρ hsub
  let B : Set Vec3 := vec3Ball x₀ ρ
  let T : Set ℝ := Ioc (t₀ - ρ ^ 2) t₀
  have hB : B ⊆ Ω' := by
    intro x hx
    exact hball x (vec3Ball_mono hρR.le hx)
  have hT' : T ⊆ J := by
    intro s hs
    exact hT s hs
  have hcyl : parabolicCylinder x₀ t₀ ρ ⊆ spaceTimeSet Ω' J := by
    intro z hz
    exact ⟨hB hz.1, hT' hz.2⟩
  have hu0 : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet Ω' J)) :=
    (hsol.2.2.2.2.2.1 Ω' J hbox).1
  have hDu0 : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet Ω' J)) :=
    (hsol.2.2.2.2.2.1 Ω' J hbox).2.1
  have huProd := @caccioppoli_centered_hcenter_huProd_1 u x₀ ρ Ω' J hB hu0
  have hDuProd : AEStronglyMeasurable Du
      ((volume.restrict B).prod (volume.restrict J)) := by
    have hDuWide : AEStronglyMeasurable Du
        ((volume.restrict Ω').prod (volume.restrict J)) := by
      rw [Measure.prod_restrict Ω' J]
      exact hDu0
    exact hDuWide.mono_measure
      (Measure.prod_mono (Measure.restrict_mono_set volume hB) le_rfl)
  have hnormProd : AEStronglyMeasurable
      (fun z : Vec3 × ℝ => vec3EuclideanNorm (u z))
      ((volume.restrict B).prod (volume.restrict J)) := by
    exact (continuous_vec3EuclideanNorm.comp_aestronglyMeasurable huProd)
  have hsqProd := @caccioppoli_centered_hcenter_hsqProd_2 u x₀ ρ J hnormProd
  have hsqMeas : AEMeasurable
      (fun z : Vec3 × ℝ => ENNReal.ofReal
        ((vec3EuclideanNorm (u z)) ^ (2 : ℕ)))
      ((volume.restrict B).prod (volume.restrict J)) := by
    exact (ENNReal.continuous_ofReal.comp continuous_id).comp_aestronglyMeasurable
      hsqProd |>.aemeasurable
  let c : ParabolicPoint → ℝ := fun z =>
    ⨍ x in B, (vec3EuclideanNorm (u (x, z.2))) ^ (2 : ℕ)
  have hc := @caccioppoli_centered_hcenter_hc_1 u x₀ ρ J hsqProd
  have hcProd : AEMeasurable (fun z : Vec3 × ℝ => c (z.1, z.2))
      ((volume.restrict B).prod (volume.restrict J)) :=
    hc.comp_snd
  have habsProd := @caccioppoli_centered_hcenter_habsProd_2 Ω I u x₀ t₀ ρ hsub J hsqProd hcProd
  have hA := @caccioppoli_centered_hcenter_hA_3 u x₀ t₀ ρ J hT' habsProd
  have hDmeas := @caccioppoli_centered_hcenter_hDmeas_4 u Du x₀ t₀ ρ J hT' hDuProd
  have hD_cyl := @caccioppoli_centered_hcenter_hD_cyl_3 u Du x₀ t₀ ρ J hT' hDuProd
  have hEbound := @caccioppoli_centered_hcenter_hEbound_4 Ω I q u Du p f hsol x₀ t₀ ρ hρ hsub
  have hDint := @caccioppoli_centered_hcenter_hDint_5 Ω I q u Du p f hsol x₀ t₀ ρ hρ hsub hD_cyl
  have hTvol : volume T ≤ ENNReal.ofReal (ρ ^ 2) := by
    rw [Real.volume_Ioc]
    rw [sub_sub_cancel]
  have hgood := @caccioppoli_centered_hcenter_hgood_5 Ω I q u Du p f hsol t₀ ρ Ω' J hbox hT
  have heInt := @caccioppoli_centered_hcenter_heInt_6 u Du x₀ t₀ ρ Ω' hB hgood
  have hdInt := @caccioppoli_centered_hcenter_hdInt_7 u Du x₀ t₀ ρ Ω' hB hDmeas hgood
  have hFprod : AEMeasurable
      (fun z : Vec3 × ℝ => ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ))
      ((volume.restrict B).prod (volume.restrict J)) := by
    have hbase : AEMeasurable
        (fun z : Vec3 × ℝ => ENNReal.ofReal (vec3EuclideanNorm (u z)))
        ((volume.restrict B).prod (volume.restrict J)) :=
      (ENNReal.continuous_ofReal.comp continuous_id).comp_aestronglyMeasurable
        hnormProd |>.aemeasurable
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hbase
  have hFtime : AEMeasurable
      (fun s : ℝ => ∫⁻ x in B,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ))
      (volume.restrict T) :=
    hFprod.lintegral_prod_left'.mono_measure
      (Measure.restrict_mono_set volume hT')
  have hFiter := @caccioppoli_centered_hcenter_hFiter_8 u x₀ t₀ ρ J hT' hFprod
  have hFtop : (∫⁻ s in T, ∫⁻ x in B,
      ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ)) ≠ ∞ := by
    rw [hFiter]
    exact caccioppoli_velocity_integral_ne_top hsol hρ hsub
  have hFsliceTop : ∀ᵐ s ∂volume.restrict T,
      (∫⁻ x in B, ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ)) ≠ ∞ :=
    (ae_lt_top' hFtime hFtop).mono fun _ h => h.ne
  have h3Int := @caccioppoli_centered_hcenter_h3Int_9 u Du x₀ t₀ ρ Ω' hB hgood hFsliceTop
  have hgInt := @caccioppoli_centered_hcenter_hgInt_10 u Du x₀ t₀ ρ Ω' hB hgood h3Int
  have hpoint' : ∀ᵐ s ∂volume.restrict T,
      (∫ x in B, |(vec3EuclideanNorm (u (x, s))) ^ 2 - c (x, s)| ^
        (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
      poincareSobolevL1VectorConstant *
        (∫ x in B, (vec3EuclideanNorm (u (x, s))) ^ 2) ^
          (1 / 2 : ℝ) *
        (∫ x in B, spatialGradientSq u Du (x, s)) ^
          (1 / 2 : ℝ) := by
    exact hpoint
  have hcenter := caccioppoli_centered_bound_of_slice_data
    (B := B) (T := T)
    (g := fun z => |(vec3EuclideanNorm (u z)) ^ 2 - c z| ^ (3 / 2 : ℝ))
    (e := fun z => (vec3EuclideanNorm (u z)) ^ 2)
    (d := fun z => spatialGradientSq u Du z)
    (F := fun s => ∫⁻ x in B, ENNReal.ofReal
      (|(vec3EuclideanNorm (u (x, s))) ^ 2 - c (x, s)| ^ (3 / 2 : ℝ)))
    (E := fun s => ∫⁻ x in B, ENNReal.ofReal
      ((vec3EuclideanNorm (u (x, s))) ^ 2))
    (D := fun s => ∫⁻ x in B, ENNReal.ofReal
      (spatialGradientSq u Du (x, s)))
    (E₀ := ENNReal.ofReal (ρ * alpha u (x₀, t₀) ρ ^ 2))
    (D₀ := ENNReal.ofReal (ρ * beta u Du (x₀, t₀) ρ ^ 2))
    (V := ENNReal.ofReal (ρ ^ 2))
    (cC := poincareSobolevL1VectorConstant)
    (by intro s; rfl) (by intro s; rfl) (by intro s; rfl)
    hDmeas
    hgInt heInt hdInt
    (by
      filter_upwards [] with s
      filter_upwards [] with x
      positivity)
    (by
      filter_upwards [] with s
      filter_upwards [] with x
      positivity)
    (by
      filter_upwards [] with s
      filter_upwards [] with x
      unfold spatialGradientSq
      positivity)
    hpoint' (by unfold poincareSobolevL1VectorConstant; positivity)
    ENNReal.ofReal_ne_top hEbound hDint hTvol (by simp)
  have hcenter_meas : AEMeasurable
      (fun w : ParabolicPoint => ENNReal.ofReal
        |(vec3EuclideanNorm (u w)) ^ 2 - c w| ^ (3 / 2 : ℝ))
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)) := by
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hA
  have hcenter_iter : (∫⁻ s in T, ∫⁻ x in B, ENNReal.ofReal
      |(vec3EuclideanNorm (u (x, s))) ^ 2 - c (x, s)| ^ (3 / 2 : ℝ)) =
      ∫⁻ w in parabolicCylinder x₀ t₀ ρ, ENNReal.ofReal
        |(vec3EuclideanNorm (u w)) ^ 2 - c w| ^ (3 / 2 : ℝ) := by
    symm
    simpa [B, T] using
      (lintegral_parabolicCylinder (x := x₀) (t := t₀) (r := ρ)
        hcenter_meas)
  have hc_cyl := @caccioppoli_centered_hcenter_hc_cyl_11 u x₀ t₀ ρ J hT' hc
  have hcenterFinal := @caccioppoli_centered_hcenter_hcenterFinal_12 u Du x₀ t₀ ρ hρ hcenter
    hcenter_iter
  have hB0 : volume B ≠ 0 := (volume_vec3Ball_pos hρ).ne'
  have hBtop : volume B ≠ ∞ := volume_vec3Ball_lt_top.ne
  have hc_nonneg : ∀ w : ParabolicPoint, 0 ≤ c w := by
    intro w
    dsimp [c]
    exact average_nonneg (fun x => sq_nonneg (vec3EuclideanNorm (u (x, w.2))))
  have hmean_slice := @caccioppoli_centered_hcenter_hmean_slice_13 u p x₀ t₀ ρ heInt h3Int hB0
    hBtop hc_nonneg
  have hmean_prod : (∫⁻ s in T,
      ENNReal.ofReal (c (x₀, s)) ^ (3 / 2 : ℝ) * volume B) ≤
      ∫⁻ s in T, ∫⁻ x in B,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ) :=
    lintegral_mono_ae hmean_slice
  have hmeanFinal := @caccioppoli_centered_hcenter_hmeanFinal_14 u x₀ t₀ ρ hρ hFiter hFtop hc_cyl
    hmean_prod
  refine ⟨c, hA, hc_cyl, ?_, hcenterFinal, hc_nonneg, hmeanFinal⟩
  intro w
  rfl


end CKN
