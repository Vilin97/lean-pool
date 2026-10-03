/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.CaccioppoliEnergyTools
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Caccioppoli Energy Terms

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open CKN.Foundation.Heat


noncomputable section

namespace CKN

private lemma caccioppoli_rhs_terms_bound_hD_1 :
    ∀ {u : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ r ε : ℝ} (hρ : (0 : ℝ) < ρ) (hε : (0 : ℝ) < ε),
      let _ : MeasurableSpace ParabolicPoint := MeasureSpace.toMeasurableSpace;
      let Q : Set ParabolicPoint := parabolicCylinder x₀ t₀ ρ;
      let F : Vec3 × ℝ → ℝ := fun (z : Vec3 × ℝ) =>
        backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z;
      AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) u (Measure.restrict volume Q) →
        (∀ (i : Fin (3 : ℕ)),
            ContDiff ℝ (F := ℝ) (⊤ : ℕ∞) fun (z : Vec3 × ℝ) => spatialPartial F i z) →
          AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
            (fun (z : ParabolicPoint) => ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z)
            (Measure.restrict volume Q)
    := by
  intro u x₀ t₀ ρ r ε hρ hε localHypothesis8 Q F huStrong hspC
  have hvec : AEStronglyMeasurable
      (fun z : ParabolicPoint => fun i => spatialPartial F i z)
      (volume.restrict Q) := by
    exact (continuous_pi (fun i => (hspC i).continuous)).aestronglyMeasurable
  have hpair : AEStronglyMeasurable
      (fun z : ParabolicPoint => (u z, fun i => spatialPartial F i z))
      (volume.restrict Q) := huStrong.prodMk hvec
  have hc : Continuous (fun z : Vec3 × (Fin 3 → ℝ) =>
      ∑ i, z.1 i * z.2 i) := by fun_prop
  exact hc.comp_aestronglyMeasurable hpair |>.aemeasurable

private lemma caccioppoli_rhs_terms_bound_hg4_2 :
    ∀ {u f : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ r ε : ℝ} (hρ : (0 : ℝ) < ρ)
      (hε : (0 : ℝ) < ε),
      let _ : MeasurableSpace ParabolicPoint := MeasureSpace.toMeasurableSpace;
      let _ : MeasurableSpace (Vec3 × ℝ) := MeasureSpace.toMeasurableSpace;
      let Q : Set ParabolicPoint := parabolicCylinder x₀ t₀ ρ;
      let F : Vec3 × ℝ → ℝ := fun (z : Vec3 × ℝ) =>
        backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z;
      ContDiff ℝ (⊤ : ℕ∞) F →
        AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) u (Measure.restrict volume Q) →
          AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) f
              (Measure.restrict volume Q) →
            AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
              (fun (z : ParabolicPoint) => ((2 : ℝ) * ∑ i : Fin (3 : ℕ), f z i * u z i) * F z)
              (Measure.restrict volume Q)
    := by
  intro u f x₀ t₀ ρ r ε hρ hε localHypothesis9 localHypothesis10 Q F hFcont huStrong hfStrong
  have hfu : AEMeasurable (fun z : ParabolicPoint =>
      ∑ i, f z i * u z i) (volume.restrict Q) := by
    have hpair : AEStronglyMeasurable
        (fun z : ParabolicPoint => (f z, u z)) (volume.restrict Q) :=
      hfStrong.prodMk huStrong
    have hc : Continuous (fun z : Vec3 × Vec3 =>
        ∑ i, z.1 i * z.2 i) := by fun_prop
    exact hc.comp_aestronglyMeasurable hpair |>.aemeasurable
  have hFmeas : AEMeasurable F (volume.restrict Q) := hFcont.continuous.aemeasurable
  exact (hfu.const_mul 2).mul hFmeas

private lemma caccioppoli_rhs_terms_bound_hraw1_3 :
    ∀ {u : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ r ε : ℝ} (hρ : (0 : ℝ) < ρ) (hε : (0 : ℝ) < ε),
      let Q : Set ParabolicPoint := parabolicCylinder x₀ t₀ ρ;
      let F : Vec3 × ℝ → ℝ := fun (z : Vec3 × ℝ) =>
        backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z;
      let g1 : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        vec3EuclideanNorm (u z) ^ (2 : ℕ) *
          (timePartial F z + ∑ i : Fin (3 : ℕ), spatialSecondPartial F i i z);
      ∫⁻ (z : ParabolicPoint) in parabolicCylinder x₀ t₀ ρ,
            ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (2 : ℝ) *
              ENNReal.ofReal
                |timePartial
                      (fun (w : ParabolicPoint) =>
                        backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w)
                      z +
                    ∑ i : Fin (3 : ℕ),
                      spatialSecondPartial
                        (fun (w : ParabolicPoint) =>
                          backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w)
                        i i z| ≠
          ∞ →
        ∫⁻ (z : ParabolicPoint) in Q, ENNReal.ofReal |g1 z| ≠ ∞
    := by
  intro u x₀ t₀ ρ r ε hρ hε Q F g1 hne1
  have hle : (∫⁻ z in Q, ENNReal.ofReal |g1 z|) ≤
      ∫⁻ z in Q, ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (2 : ℝ) *
        ENNReal.ofReal |timePartial F z + ∑ i,
          spatialSecondPartial F i i z| := by
    apply lintegral_mono
    intro z
    dsimp [g1]
    rw [abs_mul, abs_of_nonneg (sq_nonneg _),
      ENNReal.ofReal_mul (sq_nonneg _),
      ← Real.rpow_natCast (vec3EuclideanNorm (u z)) 2,
      ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg _)
        (by norm_num)]
    norm_num [Real.rpow_natCast]
  have htop : (∫⁻ z in Q, ENNReal.ofReal (vec3EuclideanNorm (u z)) ^
      (2 : ℝ) * ENNReal.ofReal |timePartial F z + ∑ i,
        spatialSecondPartial F i i z|) < ∞ := by
    have hne : (∫⁻ z in Q, ENNReal.ofReal (vec3EuclideanNorm (u z)) ^
        (2 : ℝ) * ENNReal.ofReal |timePartial F z + ∑ i,
          spatialSecondPartial F i i z|) ≠ ∞ := by
      dsimp [Q, F]
      exact hne1
    exact lt_top_iff_ne_top.mpr hne
  exact ne_of_lt (hle.trans_lt htop)

private lemma caccioppoli_rhs_terms_bound_hraw2_4 :
    ∀ {u : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ r ε : ℝ} (hρ : (0 : ℝ) < ρ) (hε : (0 : ℝ) < ε)
      {c : ParabolicPoint → ℝ},
      let Q : Set ParabolicPoint := parabolicCylinder x₀ t₀ ρ;
      let F : Vec3 × ℝ → ℝ := fun (z : Vec3 × ℝ) =>
        backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z;
      let g2 : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        (vec3EuclideanNorm (u z) ^ (2 : ℕ) - c z) * ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z;
      ∫⁻ (w : ParabolicPoint) in parabolicCylinder x₀ t₀ ρ,
            ENNReal.ofReal |vec3EuclideanNorm (u w) ^ (2 : ℕ) - c w| *
                ENNReal.ofReal (vec3EuclideanNorm (u w)) *
              ENNReal.ofReal
                (∑ i : Fin (3 : ℕ),
                  |spatialPartial
                      (fun (y : ParabolicPoint) =>
                        backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y)
                      i w|) ≠
          ∞ →
        ∫⁻ (z : ParabolicPoint) in Q, ENNReal.ofReal |g2 z| ≠ ∞
    := by
  intro u x₀ t₀ ρ r ε hρ hε c Q F g2 hne2
  have hpoint : ∀ z, ENNReal.ofReal |g2 z| ≤
      ENNReal.ofReal |(vec3EuclideanNorm (u z)) ^ 2 - c z| *
        ENNReal.ofReal (vec3EuclideanNorm (u z)) *
        ENNReal.ofReal (∑ i, |spatialPartial F i z|) := by
    intro z
    have hd := caccioppoli_partial_sum_abs (u := u) (F := F) (z := z)
    have hreal : |g2 z| ≤
        |(vec3EuclideanNorm (u z)) ^ 2 - c z| *
          (vec3EuclideanNorm (u z) * ∑ i, |spatialPartial F i z|) := by
      dsimp [g2]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hd (abs_nonneg _)
    calc
      _ ≤ ENNReal.ofReal (|(vec3EuclideanNorm (u z)) ^ 2 - c z| *
          (vec3EuclideanNorm (u z) * ∑ i, |spatialPartial F i z|)) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = _ := by
        rw [ENNReal.ofReal_mul (abs_nonneg _),
          ENNReal.ofReal_mul (vec3EuclideanNorm_nonneg _)]
        ring
  have hle := lintegral_mono (μ := volume.restrict Q) hpoint
  have htop : (∫⁻ z in Q, ENNReal.ofReal |(vec3EuclideanNorm (u z)) ^ 2 - c z| *
        ENNReal.ofReal (vec3EuclideanNorm (u z)) *
        ENNReal.ofReal (∑ i, |spatialPartial F i z|)) < ∞ := by
    have hne : (∫⁻ z in Q, ENNReal.ofReal |(vec3EuclideanNorm (u z)) ^ 2 - c z| *
        ENNReal.ofReal (vec3EuclideanNorm (u z)) *
        ENNReal.ofReal (∑ i, |spatialPartial F i z|)) ≠ ∞ := by
      dsimp [Q, F]
      exact hne2
    exact lt_top_iff_ne_top.mpr hne
  exact ne_of_lt (hle.trans_lt htop)

private lemma caccioppoli_rhs_terms_bound_hraw3_5 :
    ∀ {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {x₀ : Vec3} {t₀ ρ r ε : ℝ}
      (hρ : (0 : ℝ) < ρ) (hε : (0 : ℝ) < ε),
      let Q : Set ParabolicPoint := parabolicCylinder x₀ t₀ ρ;
      let F : Vec3 × ℝ → ℝ := fun (z : Vec3 × ℝ) =>
        backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z;
      let g3 : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        (2 : ℝ) * (p z - (0 : ℝ)) * ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z;
      ∫⁻ (w : ParabolicPoint) in parabolicCylinder x₀ t₀ ρ,
            (2 : ℝ≥0∞) * ENNReal.ofReal |p w| * ENNReal.ofReal (vec3EuclideanNorm (u w)) *
              ENNReal.ofReal
                (∑ i : Fin (3 : ℕ),
                  |spatialPartial
                      (fun (y : ParabolicPoint) =>
                        backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y)
                      i w|) ≠
          ∞ →
        ∫⁻ (z : ParabolicPoint) in Q, ENNReal.ofReal |g3 z| ≠ ∞
    := by
  intro u p x₀ t₀ ρ r ε hρ hε Q F g3 hne3
  have hpoint : ∀ z, ENNReal.ofReal |g3 z| ≤
      (2 : ℝ≥0∞) * ENNReal.ofReal |p z| *
        ENNReal.ofReal (vec3EuclideanNorm (u z)) *
        ENNReal.ofReal (∑ i, |spatialPartial F i z|) := by
    intro z
    have hd := caccioppoli_partial_sum_abs (u := u)
      (F := show ParabolicPoint → ℝ from F) (z := z)
    have hd' : |∑ i, u z i * spatialPartial F i z| ≤
        vec3EuclideanNorm (u z) * ∑ i, |spatialPartial F i z| := by
      simpa only using hd
    have hreal : |g3 z| ≤
        2 * |p z| * (vec3EuclideanNorm (u z) *
          ∑ i, |spatialPartial F i z|) := by
      calc
        |g3 z| = 2 * |p z| * |∑ i, u z i * spatialPartial F i z| := by
          simp [g3, abs_mul]
        _ ≤ 2 * |p z| *
              (vec3EuclideanNorm (u z) * ∑ i, |spatialPartial F i z|) :=
          mul_le_mul_of_nonneg_left hd' (by positivity)
    calc
      _ ≤ ENNReal.ofReal (2 * |p z| * (vec3EuclideanNorm (u z) *
          ∑ i, |spatialPartial F i z|)) := ENNReal.ofReal_le_ofReal hreal
      _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * |p z|),
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_mul (vec3EuclideanNorm_nonneg _)]
        norm_num
        ring
  have hle := lintegral_mono (μ := volume.restrict Q) hpoint
  have htop : (∫⁻ z in Q, (2 : ℝ≥0∞) * ENNReal.ofReal |p z| *
        ENNReal.ofReal (vec3EuclideanNorm (u z)) *
        ENNReal.ofReal (∑ i, |spatialPartial F i z|)) < ∞ := by
    have hne : (∫⁻ z in Q, (2 : ℝ≥0∞) * ENNReal.ofReal |p z| *
        ENNReal.ofReal (vec3EuclideanNorm (u z)) *
        ENNReal.ofReal (∑ i, |spatialPartial F i z|)) ≠ ∞ := by
      dsimp [Q, F]
      exact hne3
    exact lt_top_iff_ne_top.mpr hne
  exact ne_of_lt (hle.trans_lt htop)

private lemma caccioppoli_rhs_terms_bound_hraw4_6 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {u f : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ r ε : ℝ}
      (hρ : (0 : ℝ) < ρ) (hε : (0 : ℝ) < ε),
      let Q : Set ParabolicPoint := parabolicCylinder x₀ t₀ ρ;
      let F : Vec3 × ℝ → ℝ := fun (z : Vec3 × ℝ) =>
        backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z;
      let g4 : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        ((2 : ℝ) * ∑ i : Fin (3 : ℕ), f z i * u z i) * F z;
      (Membership.mem (γ := Set (Vec3 × ℝ → ℝ)) (spaceTimeTestFunction Ω I)
            (backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r) ∧
          ∀ (z : Vec3 × ℝ),
            (0 : ℝ) ≤ backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z) →
        ∫⁻ (w : ParabolicPoint) in parabolicCylinder x₀ t₀ ρ,
              (2 : ℝ≥0∞) * ENNReal.ofReal (vec3EuclideanNorm (f w)) *
                  ENNReal.ofReal (vec3EuclideanNorm (u w)) *
                ENNReal.ofReal
                  (backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) ≠
            ∞ →
          ∫⁻ (z : ParabolicPoint) in Q, ENNReal.ofReal |g4 z| ≠ ∞
    := by
  intro Ω I u f x₀ t₀ ρ r ε hρ hε Q F g4 htest hne4
  have hpoint : ∀ z, ENNReal.ofReal |g4 z| ≤
      (2 : ℝ≥0∞) * ENNReal.ofReal (vec3EuclideanNorm (f z)) *
      ENNReal.ofReal (vec3EuclideanNorm (u z)) *
        ENNReal.ofReal (F (show Vec3 × ℝ from z)) := by
    intro z
    have hF0 : 0 ≤ F (show Vec3 × ℝ from z) := by
      simpa only [F] using htest.2 z
    have hreal := caccioppoli_force_abs_le (u := u) (f := f)
      (F := show ParabolicPoint → ℝ from F)
      hF0 (z := z)
    calc
      _ = ENNReal.ofReal |(2 * (∑ i, f z i * u z i) *
          F (show Vec3 × ℝ from z))| := by rfl
      _ ≤ ENNReal.ofReal (2 * vec3EuclideanNorm (f z) *
          vec3EuclideanNorm (u z) * F (show Vec3 × ℝ from z)) := by
        apply ENNReal.ofReal_le_ofReal
        simpa [g4, abs_of_nonneg hF0] using hreal
      _ = _ := by
        have hfn : 0 ≤ vec3EuclideanNorm (f z) := vec3EuclideanNorm_nonneg _
        have hun : 0 ≤ vec3EuclideanNorm (u z) := vec3EuclideanNorm_nonneg _
        rw [ENNReal.ofReal_mul (mul_nonneg
            (mul_nonneg (by norm_num) hfn) hun),
          ENNReal.ofReal_mul (mul_nonneg (by norm_num) hfn),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
  have hle := lintegral_mono (μ := volume.restrict Q) hpoint
  have htop : (∫⁻ z in Q, (2 : ℝ≥0∞) *
        ENNReal.ofReal (vec3EuclideanNorm (f z)) *
        ENNReal.ofReal (vec3EuclideanNorm (u z)) *
          ENNReal.ofReal (F (show Vec3 × ℝ from z))) < ∞ := by
    have hne : (∫⁻ z in Q, (2 : ℝ≥0∞) *
        ENNReal.ofReal (vec3EuclideanNorm (f z)) *
        ENNReal.ofReal (vec3EuclideanNorm (u z)) *
          ENNReal.ofReal (F (show Vec3 × ℝ from z))) ≠ ∞ := by
      dsimp [Q, F]
      exact hne4
    exact lt_top_iff_ne_top.mpr hne
  exact ne_of_lt (hle.trans_lt htop)

private lemma caccioppoli_rhs_terms_bound_hRS_7 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ r ε : ℝ} (hρ : (0 : ℝ) < ρ) (hε : (0 : ℝ) < ε)
      (t : ℝ),
      let S : Set ParabolicPoint := Ω ×ˢ Iio t;
      @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
          (fun (z : Vec3 × ℝ) =>
            localEnergyRhs u p f
              (backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r) z)
          volume →
        IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
          (fun (z : ParabolicPoint) =>
            localEnergyRhs u p f
              (backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r) z)
          S volume
    := by
  intro Ω u p f x₀ t₀ ρ r ε hρ hε t S hRint
  change Integrable (fun z : ParabolicPoint => localEnergyRhs u p f
      (backwardHeatCutoff
        (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r) z)
    (volume.restrict S)
  rw [volume_parabolicPoint_eq_prod]
  rw [← MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
  change Integrable (μ := (volume : Measure (Vec3 × ℝ)).restrict S)
    (fun z : Vec3 × ℝ => localEnergyRhs u p f
      (backwardHeatCutoff
        (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r) z)
  have hRrestrict := hRint.mono_measure (Measure.restrict_le_self :
    volume.restrict S ≤ volume)
  exact hRrestrict

private lemma caccioppoli_rhs_terms_bound_hgc_8 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ r ε : ℝ} (hρ : (0 : ℝ) < ρ) (hε : (0 : ℝ) < ε),
      closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I →
        ∀ {c : ParabolicPoint → ℝ},
          let F : Vec3 × ℝ → ℝ := fun (z : Vec3 × ℝ) =>
            backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z;
          let g1 : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
            vec3EuclideanNorm (u z) ^ (2 : ℕ) *
              (timePartial F z + ∑ i : Fin (3 : ℕ), spatialSecondPartial F i i z);
          let g2 : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
            (vec3EuclideanNorm (u z) ^ (2 : ℕ) - c z) *
              ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z;
          let g3 : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
            (2 : ℝ) * (p z - (0 : ℝ)) * ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z;
          let g4 : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
            ((2 : ℝ) * ∑ i : Fin (3 : ℕ), f z i * u z i) * F z;
          ∀ (t : ℝ),
            let S : Set ParabolicPoint := Ω ×ˢ Iio t;
            let gC : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
              c z * ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z;
            IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                (fun (z : ParabolicPoint) =>
                  localEnergyRhs u p f
                    (backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r) z)
                S volume →
              IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                  (fun (z : ParabolicPoint) => g1 z + g2 z + g3 z + g4 z) S volume →
                IntegrableOn (mα := MeasureSpace.toMeasurableSpace) gC S volume
    := by
  intro Ω I u p f x₀ t₀ ρ r ε hρ hε hsub c F g1 g2 g3 g4 t S gC hRS hsumS
  have hsub := hRS.sub hsumS
  apply hsub.congr_fun_ae
  filter_upwards [] with z
  change localEnergyRhs u p f F z -
    (g1 z + g2 z + g3 z + g4 z) = gC z
  have hdec := caccioppoli_localEnergyRhs_decompose
    (u := u) (p := p) (f := f)
    (ψ := show Vec3 × ℝ → ℝ from F) z
  rw [hdec]
  dsimp [gC, g1, g2, g3, g4]
  ring

private lemma caccioppoli_rhs_terms_bound_hKΩ_9 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {x₀ : Vec3} {t₀ ρ : ℝ},
      (0 : ℝ) < ρ →
        closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I →
          let K : Set Vec3 := euclideanClosedBall x₀ ((3 : ℝ) * ρ / (4 : ℝ));
          K ⊆ Ω
    := by
  intro Ω I x₀ t₀ ρ hρ hsub K x hx
  have hmem : (x, t₀ - ρ ^ 2) ∈ closure (parabolicCylinder x₀ t₀ ρ) := by
    rw [closure_parabolicCylinder hρ]
    have hx' := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
      (by positivity)).1 hx
    have hxr' : vec3EuclideanNorm (x - x₀) ≤ ρ := by
      have hρ34 : 3 * ρ / 4 ≤ ρ := by linarith only [hρ]
      simpa [vec3EuclideanNorm, CKN.vecEuclideanNorm, vecNormSq, vecDot,
        pow_two] using hx'.trans hρ34
    exact ⟨hxr', ⟨le_rfl, sub_le_self _ (sq_nonneg ρ)⟩⟩
  exact (hsub hmem).1

private lemma caccioppoli_rhs_terms_bound_hCslice_10 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ r ε : ℝ} (hρ : (0 : ℝ) < ρ) (hε : (0 : ℝ) < ε)
      {c : ParabolicPoint → ℝ},
      (∀ (w : ParabolicPoint), c w = c (x₀, w.2)) →
        let F : Vec3 × ℝ → ℝ := fun (z : Vec3 × ℝ) =>
          backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z;
        ContDiff ℝ (⊤ : ℕ∞) F →
          tsupport F ⊆
              euclideanClosedBall x₀ ((3 : ℝ) * ρ / (4 : ℝ)) ×ˢ Icc (t₀ - ρ ^ (2 : ℕ)) (t₀ + ε) →
            ∀ t ≤ t₀,
              (∀ᵐ (z : ParabolicPoint) ∂Measure.restrict volume (Ω ×ˢ Iio t),
                  z ∈ parabolicCylinder x₀ t₀ ρ ∨
                    vec3EuclideanNorm (u z) ^ (2 : ℕ) *
                          (timePartial F z + ∑ i : Fin (3 : ℕ), spatialSecondPartial F i i z) =
                        (0 : ℝ) ∧
                      vec3EuclideanNorm (u z) ^ (2 : ℕ) *
                            ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z =
                          (0 : ℝ) ∧
                        (2 : ℝ) * (p z - (0 : ℝ)) *
                              ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z =
                            (0 : ℝ) ∧
                          ((2 : ℝ) * ∑ i : Fin (3 : ℕ), f z i * u z i) * F z = (0 : ℝ) ∧
                            ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z = (0 : ℝ)) →
                let gC : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
                  c z * ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z;
                (∀ᵐ (s : ℝ),
                    s ∈ Iio t ∩ Ioc (t₀ - ρ ^ (2 : ℕ)) t₀ →
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                          fun (x : Vec3) =>
                          ∑ i : Fin (3 : ℕ), u (x, s) i * spatialPartial F i (x, s)) =
                        (0 : ℝ)) →
                  (∀ᵐ (s : ℝ), s ≠ t₀ - ρ ^ (2 : ℕ)) →
                    ∀ᵐ (s : ℝ) ∂Measure.restrict volume (Iio t),
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                          fun (x : Vec3) => gC (x, s)) =
                        (0 : ℝ)
    := by
  intro Ω u p f x₀ t₀ ρ r ε hρ hε c hcc F hFcont hFsupp t ht hzero gC hDsliceInter' hneq
  apply (ae_restrict_iff' measurableSet_Iio).2
  filter_upwards [hDsliceInter', hneq] with s hs hne
  intro hsIio
  by_cases hsJ : s ∈ Ioc (t₀ - ρ ^ 2) t₀
  · have hd := hs ⟨hsIio, hsJ⟩
    calc
      ∫ x in Ω, gC (x, s) =
          ∫ x in Ω, c (x₀, s) *
            (∑ i, u (x, s) i * spatialPartial F i (x, s)) := by
        apply integral_congr_ae
        filter_upwards [] with x
        dsimp [gC]
        rw [hcc (x, s)]
      _ = c (x₀, s) *
          (∫ x in Ω, ∑ i, u (x, s) i * spatialPartial F i (x, s)) := by
        rw [integral_const_mul]
      _ = 0 := by rw [hd, mul_zero]
  · have hst : s < t₀ := lt_of_lt_of_le hsIio ht
    have hle : s ≤ t₀ - ρ ^ 2 := by
      by_contra hnot
      exact hsJ ⟨lt_of_not_ge hnot, hst.le⟩
    have hslt : s < t₀ - ρ ^ 2 := lt_of_le_of_ne hle hne
    have hD0 : ∀ x : Vec3,
        ∑ i, u (x, s) i * spatialPartial F i (x, s) = 0 := by
      intro x
      apply Finset.sum_eq_zero
      intro i hi
      apply mul_eq_zero.mpr
      right
      apply caccioppoli_spatialPartial_zero_of_not_mem_tsupport hFcont
      intro hz
      exact not_le_of_gt hslt ((hFsupp hz).2.1)
    have hzero : (fun x : Vec3 => gC (x, s)) =ᵐ[volume.restrict Ω]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [] with x
      dsimp [gC]
      rw [hD0 x, mul_zero]
    simpa using (integral_congr_ae hzero)

private lemma caccioppoli_rhs_terms_bound_hpoint2_11 :
    ∀ {u : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ r ε : ℝ} (hρ : (0 : ℝ) < ρ) (hε : (0 : ℝ) < ε)
      {c : ParabolicPoint → ℝ},
      let F : Vec3 × ℝ → ℝ := fun (z : Vec3 × ℝ) =>
        backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z;
      let g2 : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        (vec3EuclideanNorm (u z) ^ (2 : ℕ) - c z) * ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z;
      ∀ (z : ParabolicPoint),
        ENNReal.ofReal |g2 z| ≤
          ENNReal.ofReal |vec3EuclideanNorm (u z) ^ (2 : ℕ) - c z| *
              ENNReal.ofReal (vec3EuclideanNorm (u z)) *
            ENNReal.ofReal (∑ i : Fin (3 : ℕ), |spatialPartial F i z|)
    := by
  intro u x₀ t₀ ρ r ε hρ hε c F g2 z
  have hd := caccioppoli_partial_sum_abs (u := u) (F := F) (z := z)
  have hreal : |g2 z| ≤
      |(vec3EuclideanNorm (u z)) ^ 2 - c z| *
        (vec3EuclideanNorm (u z) * ∑ i, |spatialPartial F i z|) := by
    dsimp [g2]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hd (abs_nonneg _)
  calc
    _ ≤ ENNReal.ofReal (|(vec3EuclideanNorm (u z)) ^ 2 - c z| *
        (vec3EuclideanNorm (u z) * ∑ i, |spatialPartial F i z|)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = _ := by
      rw [ENNReal.ofReal_mul (abs_nonneg _),
        ENNReal.ofReal_mul (vec3EuclideanNorm_nonneg _)]
      ring

private lemma caccioppoli_rhs_terms_bound_hpoint3_12 :
    ∀ {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {x₀ : Vec3} {t₀ ρ r ε : ℝ}
      (hρ : (0 : ℝ) < ρ) (hε : (0 : ℝ) < ε),
      let F : Vec3 × ℝ → ℝ := fun (z : Vec3 × ℝ) =>
        backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z;
      let g3 : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        (2 : ℝ) * (p z - (0 : ℝ)) * ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z;
      ∀ (z : ParabolicPoint),
        ENNReal.ofReal |g3 z| ≤
          (2 : ℝ≥0∞) * ENNReal.ofReal |p z| * ENNReal.ofReal (vec3EuclideanNorm (u z)) *
            ENNReal.ofReal (∑ i : Fin (3 : ℕ), |spatialPartial F i z|)
    := by
  intro u p x₀ t₀ ρ r ε hρ hε F g3 z
  have hd := caccioppoli_partial_sum_abs (u := u)
    (F := show ParabolicPoint → ℝ from F) (z := z)
  have hd' : |∑ i, u z i * spatialPartial F i z| ≤
      vec3EuclideanNorm (u z) * ∑ i, |spatialPartial F i z| := by
    simpa only using hd
  have hreal : |g3 z| ≤
      2 * |p z| * (vec3EuclideanNorm (u z) *
        ∑ i, |spatialPartial F i z|) := by
    calc
      |g3 z| = 2 * |p z| * |∑ i, u z i * spatialPartial F i z| := by
        simp [g3, abs_mul]
      _ ≤ 2 * |p z| *
            (vec3EuclideanNorm (u z) * ∑ i, |spatialPartial F i z|) :=
        mul_le_mul_of_nonneg_left hd' (by positivity)
  calc
    _ ≤ ENNReal.ofReal (2 * |p z| * (vec3EuclideanNorm (u z) *
        ∑ i, |spatialPartial F i z|)) := ENNReal.ofReal_le_ofReal hreal
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * |p z|),
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_mul (vec3EuclideanNorm_nonneg _)]
      norm_num
      ring

private lemma caccioppoli_rhs_terms_bound_hpoint4_13 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {u f : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ r ε : ℝ}
      (hρ : (0 : ℝ) < ρ) (hε : (0 : ℝ) < ε),
      let F : Vec3 × ℝ → ℝ := fun (z : Vec3 × ℝ) =>
        backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z;
      let g4 : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        ((2 : ℝ) * ∑ i : Fin (3 : ℕ), f z i * u z i) * F z;
      (Membership.mem (γ := Set (Vec3 × ℝ → ℝ)) (spaceTimeTestFunction Ω I)
            (backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r) ∧
          ∀ (z : Vec3 × ℝ),
            (0 : ℝ) ≤ backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z) →
        ∀ (z : ParabolicPoint),
          ENNReal.ofReal |g4 z| ≤
            (2 : ℝ≥0∞) * ENNReal.ofReal (vec3EuclideanNorm (f z)) *
                ENNReal.ofReal (vec3EuclideanNorm (u z)) *
              ENNReal.ofReal
                (F
                  (have this : Vec3 × ℝ := z;
                  this))
    := by
  intro Ω I u f x₀ t₀ ρ r ε hρ hε F g4 htest z
  have hF0 : 0 ≤ F (show Vec3 × ℝ from z) := by
    simpa only [F] using htest.2 z
  have hreal := caccioppoli_force_abs_le (u := u) (f := f)
    (F := show ParabolicPoint → ℝ from F) hF0 (z := z)
  calc
    _ = ENNReal.ofReal |(2 * (∑ i, f z i * u z i) *
        F (show Vec3 × ℝ from z))| := by rfl
    _ ≤ ENNReal.ofReal (2 * vec3EuclideanNorm (f z) *
        vec3EuclideanNorm (u z) * F (show Vec3 × ℝ from z)) := by
      apply ENNReal.ofReal_le_ofReal
      simpa [g4, abs_of_nonneg hF0] using hreal
    _ = _ := by
      have hfn : 0 ≤ vec3EuclideanNorm (f z) := vec3EuclideanNorm_nonneg _
      have hun : 0 ≤ vec3EuclideanNorm (u z) := vec3EuclideanNorm_nonneg _
      rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) hfn) hun),
        ENNReal.ofReal_mul (mul_nonneg (by norm_num) hfn),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num

private lemma caccioppoli_rhs_terms_bound_hR_eq_14 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ r ε : ℝ} (hρ : (0 : ℝ) < ρ) (hε : (0 : ℝ) < ε)
      {c : ParabolicPoint → ℝ},
      let F : Vec3 × ℝ → ℝ := fun (z : Vec3 × ℝ) =>
        backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z;
      let g1 : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        vec3EuclideanNorm (u z) ^ (2 : ℕ) *
          (timePartial F z + ∑ i : Fin (3 : ℕ), spatialSecondPartial F i i z);
      let g2 : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        (vec3EuclideanNorm (u z) ^ (2 : ℕ) - c z) * ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z;
      let g3 : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        (2 : ℝ) * (p z - (0 : ℝ)) * ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z;
      let g4 : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        ((2 : ℝ) * ∑ i : Fin (3 : ℕ), f z i * u z i) * F z;
      ∀ (t : ℝ),
        let S : Set ParabolicPoint := Ω ×ˢ Iio t;
        let gC : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
          c z * ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z;
        IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
            (fun (z : ParabolicPoint) => g1 z + g2 z + g3 z + g4 z) S volume →
          IntegrableOn (mα := MeasureSpace.toMeasurableSpace) gC S volume →
            (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume S)
                  fun (z : ParabolicPoint) => gC z) =
                (0 : ℝ) →
              Eq (α := ℝ)
                (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume S)
                  fun (z : ParabolicPoint) =>
                  localEnergyRhs u p f
                    (backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r) z)
                (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume S)
                  fun (z : ParabolicPoint) => g1 z + g2 z + g3 z + g4 z)
    := by
  intro Ω u p f x₀ t₀ ρ r ε hρ hε c F g1 g2 g3 g4 t S gC hsumS hgc hcancelC
  calc
    _ = ∫ z in S, (g1 z + g2 z + g3 z + g4 z) + gC z := by
      apply integral_congr_ae
      filter_upwards [] with z
      change localEnergyRhs u p f F z =
        (g1 z + g2 z + g3 z + g4 z) + gC z
      have hdec := caccioppoli_localEnergyRhs_decompose
        (u := u) (p := p) (f := f)
        (ψ := show Vec3 × ℝ → ℝ from F) z
      rw [hdec]
      dsimp [gC, g1, g2, g3, g4]
      ring
    _ = (∫ z in S, g1 z + g2 z + g3 z + g4 z) +
        (∫ z in S, gC z) := by
      exact integral_add hsumS.integrable hgc.integrable
    _ = ∫ z in S, (g1 z + g2 z + g3 z + g4 z) := by
      rw [hcancelC, add_zero]

private lemma caccioppoli_rhs_terms_bound_hg2_1 :
    ∀ {u : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ r ε : ℝ} (hρ : (0 : ℝ) < ρ) (hε : (0 : ℝ) < ε)
      {c : ParabolicPoint → ℝ},
      AEMeasurable (_m := MeasureSpace.toMeasurableSpace) c
          (Measure.restrict volume (parabolicCylinder x₀ t₀ ρ)) →
        let _ : MeasurableSpace ParabolicPoint := MeasureSpace.toMeasurableSpace;
        let Q : Set ParabolicPoint := parabolicCylinder x₀ t₀ ρ;
        let F : Vec3 × ℝ → ℝ := fun (z : Vec3 × ℝ) =>
          backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z;
        AEStronglyMeasurable (β := ℝ) (m₀ := MeasureSpace.toMeasurableSpace)
            (fun (z : ParabolicPoint) => vec3EuclideanNorm (u z)) (Measure.restrict volume Q) →
          AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
              (fun (z : ParabolicPoint) =>
                ∑ i : Fin (3 : ℕ),
                  u z i *
                    spatialPartial
                      (fun (z : Vec3 × ℝ) =>
                        backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z)
                      i z)
              (Measure.restrict volume (parabolicCylinder x₀ t₀ ρ)) →
            AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
              (fun (z : ParabolicPoint) =>
                (vec3EuclideanNorm (u z) ^ (2 : ℕ) - c z) *
                  ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z)
              (Measure.restrict volume Q)
    := by
  intro u x₀ t₀ ρ r ε hρ hε c hcm localHypothesis10 Q F huNormStrong hD
  have hsq : AEMeasurable (fun z : ParabolicPoint =>
      (vec3EuclideanNorm (u z)) ^ 2) (volume.restrict Q) :=
    (huNormStrong.pow 2).aemeasurable
  exact ((hsq.aestronglyMeasurable.sub hcm.aestronglyMeasurable).mul
    hD.aestronglyMeasurable).aemeasurable

private lemma caccioppoli_rhs_terms_bound_hz2_2 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ r ε : ℝ} (hρ : (0 : ℝ) < ρ) (hε : (0 : ℝ) < ε)
      {c : ParabolicPoint → ℝ},
      let Q : Set ParabolicPoint := parabolicCylinder x₀ t₀ ρ;
      let F : Vec3 × ℝ → ℝ := fun (z : Vec3 × ℝ) =>
        backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z;
      let g2 : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        (vec3EuclideanNorm (u z) ^ (2 : ℕ) - c z) * ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z;
      ∀ (t : ℝ),
        let S : Set ParabolicPoint := Ω ×ˢ Iio t;
        (∀ᵐ (z : ParabolicPoint) ∂Measure.restrict volume (Ω ×ˢ Iio t),
            z ∈ parabolicCylinder x₀ t₀ ρ ∨
              vec3EuclideanNorm (u z) ^ (2 : ℕ) *
                    (timePartial F z + ∑ i : Fin (3 : ℕ), spatialSecondPartial F i i z) =
                  (0 : ℝ) ∧
                vec3EuclideanNorm (u z) ^ (2 : ℕ) *
                      ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z =
                    (0 : ℝ) ∧
                  (2 : ℝ) * (p z - (0 : ℝ)) * ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z =
                      (0 : ℝ) ∧
                    ((2 : ℝ) * ∑ i : Fin (3 : ℕ), f z i * u z i) * F z = (0 : ℝ) ∧
                      ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z = (0 : ℝ)) →
          ∀ᵐ (z : ParabolicPoint) ∂Measure.restrict volume S, z ∈ Q ∨ g2 z = (0 : ℝ)
    := by
  intro Ω u p f x₀ t₀ ρ r ε hρ hε c Q F g2 t S hzero
  filter_upwards [hzero] with z hz
  rcases hz with hz | hz
  · exact Or.inl hz
  · exact Or.inr (by
      dsimp only [g2]
      apply mul_eq_zero.mpr
      right
      exact hz.2.2.2.2)

private lemma caccioppoli_rhs_terms_bound_hKR_3 :
    ∀ {x₀ : Vec3} {ρ : ℝ},
      (0 : ℝ) < ρ →
        let K : Set Vec3 := euclideanClosedBall x₀ ((3 : ℝ) * ρ / (4 : ℝ));
        ∀ (R : ℝ), ρ < R → K ⊆ vec3Ball x₀ R
    := by
  intro x₀ ρ hρ K R hρR x hx
  rw [mem_vec3Ball]
  have hx' := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
    (by positivity)).1 hx
  have hlt : 3 * ρ / 4 < R := by linarith only [hρR, hρ]
  simpa [vec3EuclideanNorm, CKN.vecEuclideanNorm, vecNormSq, vecDot,
    pow_two] using hx'.trans_lt hlt

private lemma caccioppoli_rhs_terms_bound_hUs_4 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {x₀ : Vec3} {t₀ ρ : ℝ},
      let K : Set Vec3 := euclideanClosedBall x₀ ((3 : ℝ) * ρ / (4 : ℝ));
      IsCompact K →
        ∀ (Ω₁ : Set Vec3),
          K ⊆ Ω₁ →
            (∀ᵐ (x : ℝ) ∂Measure.restrict volume (Ioc (t₀ - ρ ^ (2 : ℕ)) t₀),
                MemLp (ε := Vec3) (m0 := MeasureSpace.toMeasurableSpace)
                    (fun (x_1 : Vec3) => u (x_1, x)) (2 : ℝ≥0∞) (Measure.restrict volume Ω₁) ∧
                  MemLp (ε := Fin (3 : ℕ) → Vec3) (m0 := MeasureSpace.toMeasurableSpace)
                    (fun (x_1 : Vec3) => Du (x_1, x)) (2 : ℝ≥0∞) (Measure.restrict volume Ω₁)) →
              ∀ᵐ (s : ℝ) ∂Measure.restrict volume (Ioc (t₀ - ρ ^ (2 : ℕ)) t₀),
                IntegrableOn (ε := Vec3) (mα := MeasureSpace.toMeasurableSpace)
                  (fun (x : Vec3) => u (x, s)) K volume
    := by
  intro u Du x₀ t₀ ρ K hKcompact Ω₁ hKΩ₁ hmem
  filter_upwards [hmem] with s hs
  let _ : IsFiniteMeasure (volume.restrict K) := by
    exact isFiniteMeasure_restrict.mpr hKcompact.measure_lt_top.ne
  have hKmem : MemLp (fun x : Vec3 => u (x, s)) 2
      (volume.restrict K) :=
    hs.1.mono_measure (Measure.restrict_mono_set volume hKΩ₁)
  change Integrable (fun x : Vec3 => u (x, s)) (volume.restrict K)
  exact hKmem.integrable (by norm_num)

private lemma caccioppoli_rhs_terms_bound_houterC_5 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ r ε : ℝ} (hρ : (0 : ℝ) < ρ) (hε : (0 : ℝ) < ε)
      {c : ParabolicPoint → ℝ},
      let F : Vec3 × ℝ → ℝ := fun (z : Vec3 × ℝ) =>
        backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z;
      ∀ (t : ℝ),
        (∀ᵐ (z : ParabolicPoint) ∂Measure.restrict volume (Ω ×ˢ Iio t),
            z ∈ parabolicCylinder x₀ t₀ ρ ∨
              vec3EuclideanNorm (u z) ^ (2 : ℕ) *
                    (timePartial F z + ∑ i : Fin (3 : ℕ), spatialSecondPartial F i i z) =
                  (0 : ℝ) ∧
                vec3EuclideanNorm (u z) ^ (2 : ℕ) *
                      ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z =
                    (0 : ℝ) ∧
                  (2 : ℝ) * (p z - (0 : ℝ)) * ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z =
                      (0 : ℝ) ∧
                    ((2 : ℝ) * ∑ i : Fin (3 : ℕ), f z i * u z i) * F z = (0 : ℝ) ∧
                      ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z = (0 : ℝ)) →
          let gC : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
            c z * ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z;
          (∀ᵐ (s : ℝ) ∂Measure.restrict volume (Iio t),
              (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                  fun (x : Vec3) =>
                  (fun (z : ParabolicPoint) =>
                      c z *
                        ∑ i : Fin (3 : ℕ),
                          u z i *
                            spatialPartial
                              (fun (z : Vec3 × ℝ) =>
                                backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀
                                  r z)
                              i z)
                    (x, s)) =
                (0 : ℝ)) →
            (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume (Iio t))
                fun (s : ℝ) =>
                @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                  fun (x : Vec3) => gC (x, s)) =
              (0 : ℝ)
    := by
  intro Ω u p f x₀ t₀ ρ r ε hρ hε c F t hzero gC hCslice
  have hzero : (fun s : ℝ => ∫ x in Ω, gC (x, s)) =ᵐ[volume.restrict (Iio t)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hCslice] with s hs
    exact hs
  simpa using (integral_congr_ae hzero)

private lemma caccioppoli_rhs_terms_bound_hcancelC_6 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ r ε : ℝ} (hρ : (0 : ℝ) < ρ)
      (hε : (0 : ℝ) < ε) {c : ParabolicPoint → ℝ},
      let F : Vec3 × ℝ → ℝ := fun (z : Vec3 × ℝ) =>
        backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z;
      ∀ (t : ℝ),
        let S : Set ParabolicPoint := Ω ×ˢ Iio t;
        let gC : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
          c z * ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z;
        (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume (Iio t))
              fun (s : ℝ) =>
              @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                fun (x : Vec3) => gC (x, s)) =
            (0 : ℝ) →
          Eq (α := ℝ)
              (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume (Iio t))
                fun (s : ℝ) =>
                @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                  fun (x : Vec3) => gC (x, s))
              (@integral _ _ _ _ Prod.instMeasurableSpace
                (Measure.restrict (Measure.prod volume volume) (Ω ×ˢ Iio t)) fun (z : Vec3 × ℝ) =>
                gC z) →
            (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume S)
                fun (z : ParabolicPoint) => gC z) =
              (0 : ℝ)
    := by
  intro Ω u x₀ t₀ ρ r ε hρ hε c F t S gC houterC hnestC
  have hprodzero : ∫ z in Ω ×ˢ Iio t, gC z
      ∂((volume : Measure Vec3).prod volume) = 0 := by
    rw [← hnestC]
    exact houterC
  change ∫ z : Vec3 × ℝ in Ω ×ˢ Iio t, gC z
      ∂((volume : Measure Vec3).prod volume) = 0
  exact hprodzero

private lemma caccioppoli_rhs_terms_bound_hpoint1_7 :
    ∀ {u : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ r ε : ℝ} (hρ : (0 : ℝ) < ρ) (hε : (0 : ℝ) < ε),
      let F : Vec3 × ℝ → ℝ := fun (z : Vec3 × ℝ) =>
        backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z;
      let g1 : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        vec3EuclideanNorm (u z) ^ (2 : ℕ) *
          (timePartial F z + ∑ i : Fin (3 : ℕ), spatialSecondPartial F i i z);
      ∀ (z : ParabolicPoint),
        ENNReal.ofReal |g1 z| ≤
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (2 : ℝ) *
            ENNReal.ofReal |timePartial F z + ∑ i : Fin (3 : ℕ), spatialSecondPartial F i i z|
    := by
  intro u x₀ t₀ ρ r ε hρ hε F g1 z
  dsimp [g1]
  rw [abs_mul, abs_of_nonneg (sq_nonneg _),
    ENNReal.ofReal_mul (sq_nonneg _),
    ← Real.rpow_natCast (vec3EuclideanNorm (u z)) 2,
    ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg _)
      (by norm_num)]
  norm_num [Real.rpow_natCast]

private lemma caccioppoli_rhs_terms_bound_hRprod_8 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ r ε : ℝ} (hρ : (0 : ℝ) < ρ) (hε : (0 : ℝ) < ε)
      (t : ℝ),
      let S : Set ParabolicPoint := Ω ×ˢ Iio t;
      @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
          (fun (z : Vec3 × ℝ) =>
            localEnergyRhs u p f
              (backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r) z)
          volume →
        IntegrableOn (ε := ℝ) (mα := Prod.instMeasurableSpace)
          (fun (z : ParabolicPoint) =>
            localEnergyRhs u p f
              (backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r) z)
          S (Measure.prod volume volume)
    := by
  intro Ω u p f x₀ t₀ ρ r ε hρ hε t S hRint
  rw [← MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
  change Integrable (μ := (volume : Measure (Vec3 × ℝ)).restrict S)
    (fun z : Vec3 × ℝ => localEnergyRhs u p f
      (backwardHeatCutoff
        (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r) z)
  exact hRint.mono_measure (Measure.restrict_le_self : volume.restrict S ≤ volume)

private lemma caccioppoli_rhs_terms_bound_hsum_1 :
    ∀ {x₀ : Vec3} {t₀ ρ r ε : ℝ} (hρ : (0 : ℝ) < ρ) (hε : (0 : ℝ) < ε),
      let F : Vec3 × ℝ → ℝ := fun (z : Vec3 × ℝ) =>
        backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z;
      (∀ (i j : Fin (3 : ℕ)),
          ContDiff ℝ (F := ℝ) (⊤ : ℕ∞) fun (z : Vec3 × ℝ) =>
            spatialSecondPartial F i j z) →
        ContDiff ℝ (F := ℝ) (⊤ : ℕ∞) fun (z : Vec3 × ℝ) =>
          ∑ i : Fin (3 : ℕ), spatialSecondPartial F i i z
    := by
  intro x₀ t₀ ρ r ε hρ hε F hssC
  apply ContDiff.sum
  intro i hi
  exact hssC i i

private lemma caccioppoli_rhs_terms_bound_hg3_2 :
    ∀ {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {x₀ : Vec3} {t₀ ρ r ε : ℝ}
      (hρ : (0 : ℝ) < ρ) (hε : (0 : ℝ) < ε),
      let Q : Set ParabolicPoint := parabolicCylinder x₀ t₀ ρ;
      let F : Vec3 × ℝ → ℝ := fun (z : Vec3 × ℝ) =>
        backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z;
      AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace) (fun (z : ParabolicPoint) => p z)
          (Measure.restrict volume Q) →
        AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
            (fun (z : ParabolicPoint) =>
              ∑ i : Fin (3 : ℕ),
                u z i *
                  spatialPartial
                    (fun (z : Vec3 × ℝ) =>
                      backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z)
                    i z)
            (Measure.restrict volume (parabolicCylinder x₀ t₀ ρ)) →
          AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
            (fun (z : ParabolicPoint) =>
              (2 : ℝ) * (p z - (0 : ℝ)) * ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z)
            (Measure.restrict volume Q)
    := by
  intro u p x₀ t₀ ρ r ε hρ hε Q F hp hD
  exact (((hp.aestronglyMeasurable.sub
    measurable_const.aestronglyMeasurable).const_mul (2 : ℝ)).mul
      hD.aestronglyMeasurable).aemeasurable

private lemma caccioppoli_rhs_terms_bound_hz1_3 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ r ε : ℝ} (hρ : (0 : ℝ) < ρ) (hε : (0 : ℝ) < ε),
      let Q : Set ParabolicPoint := parabolicCylinder x₀ t₀ ρ;
      let F : Vec3 × ℝ → ℝ := fun (z : Vec3 × ℝ) =>
        backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z;
      let g1 : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        vec3EuclideanNorm (u z) ^ (2 : ℕ) *
          (timePartial F z + ∑ i : Fin (3 : ℕ), spatialSecondPartial F i i z);
      ∀ (t : ℝ),
        let S : Set ParabolicPoint := Ω ×ˢ Iio t;
        (∀ᵐ (z : ParabolicPoint) ∂Measure.restrict volume (Ω ×ˢ Iio t),
            z ∈ parabolicCylinder x₀ t₀ ρ ∨
              vec3EuclideanNorm (u z) ^ (2 : ℕ) *
                    (timePartial F z + ∑ i : Fin (3 : ℕ), spatialSecondPartial F i i z) =
                  (0 : ℝ) ∧
                vec3EuclideanNorm (u z) ^ (2 : ℕ) *
                      ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z =
                    (0 : ℝ) ∧
                  (2 : ℝ) * (p z - (0 : ℝ)) * ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z =
                      (0 : ℝ) ∧
                    ((2 : ℝ) * ∑ i : Fin (3 : ℕ), f z i * u z i) * F z = (0 : ℝ) ∧
                      ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z = (0 : ℝ)) →
          ∀ᵐ (z : ParabolicPoint) ∂Measure.restrict volume S, z ∈ Q ∨ g1 z = (0 : ℝ)
    := by
  intro Ω u p f x₀ t₀ ρ r ε hρ hε Q F g1 t S hzero
  filter_upwards [hzero] with z hz
  rcases hz with hz | hz
  · exact Or.inl hz
  · exact Or.inr (by simpa only [g1] using hz.1)

private lemma caccioppoli_rhs_terms_bound_hz3_4 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ r ε : ℝ} (hρ : (0 : ℝ) < ρ) (hε : (0 : ℝ) < ε),
      let Q : Set ParabolicPoint := parabolicCylinder x₀ t₀ ρ;
      let F : Vec3 × ℝ → ℝ := fun (z : Vec3 × ℝ) =>
        backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z;
      let g3 : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        (2 : ℝ) * (p z - (0 : ℝ)) * ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z;
      ∀ (t : ℝ),
        let S : Set ParabolicPoint := Ω ×ˢ Iio t;
        (∀ᵐ (z : ParabolicPoint) ∂Measure.restrict volume (Ω ×ˢ Iio t),
            z ∈ parabolicCylinder x₀ t₀ ρ ∨
              vec3EuclideanNorm (u z) ^ (2 : ℕ) *
                    (timePartial F z + ∑ i : Fin (3 : ℕ), spatialSecondPartial F i i z) =
                  (0 : ℝ) ∧
                vec3EuclideanNorm (u z) ^ (2 : ℕ) *
                      ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z =
                    (0 : ℝ) ∧
                  (2 : ℝ) * (p z - (0 : ℝ)) * ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z =
                      (0 : ℝ) ∧
                    ((2 : ℝ) * ∑ i : Fin (3 : ℕ), f z i * u z i) * F z = (0 : ℝ) ∧
                      ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z = (0 : ℝ)) →
          ∀ᵐ (z : ParabolicPoint) ∂Measure.restrict volume S, z ∈ Q ∨ g3 z = (0 : ℝ)
    := by
  intro Ω u p f x₀ t₀ ρ r ε hρ hε Q F g3 t S hzero
  filter_upwards [hzero] with z hz
  rcases hz with hz | hz
  · exact Or.inl hz
  · exact Or.inr (by simpa only [g3] using hz.2.2.1)

private lemma caccioppoli_rhs_terms_bound_hz4_5 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ r ε : ℝ} (hρ : (0 : ℝ) < ρ) (hε : (0 : ℝ) < ε),
      let Q : Set ParabolicPoint := parabolicCylinder x₀ t₀ ρ;
      let F : Vec3 × ℝ → ℝ := fun (z : Vec3 × ℝ) =>
        backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z;
      let g4 : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        ((2 : ℝ) * ∑ i : Fin (3 : ℕ), f z i * u z i) * F z;
      ∀ (t : ℝ),
        let S : Set ParabolicPoint := Ω ×ˢ Iio t;
        (∀ᵐ (z : ParabolicPoint) ∂Measure.restrict volume (Ω ×ˢ Iio t),
            z ∈ parabolicCylinder x₀ t₀ ρ ∨
              vec3EuclideanNorm (u z) ^ (2 : ℕ) *
                    (timePartial F z + ∑ i : Fin (3 : ℕ), spatialSecondPartial F i i z) =
                  (0 : ℝ) ∧
                vec3EuclideanNorm (u z) ^ (2 : ℕ) *
                      ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z =
                    (0 : ℝ) ∧
                  (2 : ℝ) * (p z - (0 : ℝ)) * ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z =
                      (0 : ℝ) ∧
                    ((2 : ℝ) * ∑ i : Fin (3 : ℕ), f z i * u z i) * F z = (0 : ℝ) ∧
                      ∑ i : Fin (3 : ℕ), u z i * spatialPartial F i z = (0 : ℝ)) →
          ∀ᵐ (z : ParabolicPoint) ∂Measure.restrict volume S, z ∈ Q ∨ g4 z = (0 : ℝ)
    := by
  intro Ω u p f x₀ t₀ ρ r ε hρ hε Q F g4 t S hzero
  filter_upwards [hzero] with z hz
  rcases hz with hz | hz
  · exact Or.inl hz
  · exact Or.inr (by simpa only [g4] using hz.2.2.2.1)

private lemma caccioppoli_rhs_terms_bound_hDslice_6 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ r ε : ℝ} (hρ : (0 : ℝ) < ρ)
      (hε : (0 : ℝ) < ε),
      let F : Vec3 × ℝ → ℝ := fun (z : Vec3 × ℝ) =>
        backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z;
      ContDiff ℝ (⊤ : ℕ∞) F →
        let K : Set Vec3 := euclideanClosedBall x₀ ((3 : ℝ) * ρ / (4 : ℝ));
        IsCompact K →
          (have K : Set Vec3 := euclideanClosedBall x₀ ((3 : ℝ) * ρ / (4 : ℝ));
            K ⊆ Ω) →
            (∀ᵐ (s : ℝ) ∂Measure.restrict volume (Ioc (t₀ - ρ ^ (2 : ℕ)) t₀),
                IntegrableOn (ε := Vec3) (mα := MeasureSpace.toMeasurableSpace)
                  (fun (x : Vec3) => u (x, s)) (euclideanClosedBall x₀ ((3 : ℝ) * ρ / (4 : ℝ)))
                  volume) →
              (∀ᵐ (s : ℝ) ∂Measure.restrict volume (Ioc (t₀ - ρ ^ (2 : ℕ)) t₀),
                  ∀ (x : ℝ),
                    parametricPairing
                        (fun (s : ℝ) (y : Vec3) =>
                          backwardHeatCutoff (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r
                            (y, s))
                        (fun (_ : Vec3) => (0 : ℝ)) (fun (y : Vec3) => u (y, s))
                        (fun (_ : Vec3) => (0 : Fin (3 : ℕ) → Fin (3 : ℕ) → ℝ)) x =
                      (0 : ℝ)) →
                tsupport F ⊆ SProd.sprod (β := Set ℝ) K univ →
                  ∀ᵐ (s : ℝ) ∂Measure.restrict volume (Ioc (t₀ - ρ ^ (2 : ℕ)) t₀),
                    (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω)
                        fun (x : Vec3) =>
                        ∑ i : Fin (3 : ℕ), u (x, s) i * spatialPartial F i (x, s)) =
                      (0 : ℝ)
    := by
  intro Ω u x₀ t₀ ρ r ε hρ hε F hFcont K hKcompact hKΩ hUs hpair hFsuppK
  filter_upwards [hpair, hUs] with s hs hUs'
  exact (caccioppoli_pairing_zero_to_slice_integral hKcompact hKΩ hFcont
    hFsuppK hUs' (hs s)).2

theorem caccioppoli_rhs_terms_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ r ε : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hr : 0 < r)
    (hscale : r ≤ ρ / 2) (hεr : ε < r ^ 2)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I)
    (hfuture : Icc t₀ (t₀ + ε) ⊆ I)
    {c : ParabolicPoint → ℝ}
    (hA : AEMeasurable (fun w => ENNReal.ofReal
      |(vec3EuclideanNorm (u w)) ^ 2 - c w|)
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)))
    (hcm : AEMeasurable c
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)))
    (hcenter :
      (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal |(vec3EuclideanNorm (u w)) ^ 2 - c w| ^
          (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
        ENNReal.ofReal (poincareSobolevL1VectorConstant * ρ ^ (4 / 3 : ℝ) *
          alpha u (x₀, t₀) ρ * beta u Du (x₀, t₀) ρ))
    (hcc : ∀ w, c w = c (x₀, w.2))
    (hvelocity : (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ∞) :
    ∀ t ≤ t₀, ∫ s in Iio t, ∫ x in Ω,
      localEnergyRhs u p f
        (backwardHeatCutoff
          (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r) (x, s) ≤
      caccioppoliI1HeatCutoffRaw (u := u) (x₀ := x₀) (t₀ := t₀)
          (ρ := ρ) (ε := ε) (r := r) hρ hε +
      caccioppoliI2HeatCutoffRaw (u := u) (c := c) (x₀ := x₀)
          (t₀ := t₀) (ρ := ρ) (ε := ε) (r := r) hρ hε +
      caccioppoliI3HeatCutoffRaw (p := p) (v := u) (x₀ := x₀)
          (t₀ := t₀) (ρ := ρ) (ε := ε) (r := r) hρ hε +
      caccioppoliI4HeatCutoffRaw (u := u) (f := f) (x₀ := x₀)
          (t₀ := t₀) (ρ := ρ) (ε := ε) (r := r) hρ hε := by
  let _ : MeasurableSpace ParabolicPoint :=
    Measure.prod.measureSpace.toMeasurableSpace
  let _ : MeasurableSpace (Vec3 × ℝ) :=
    Measure.prod.measureSpace.toMeasurableSpace
  let Q : Set ParabolicPoint := parabolicCylinder x₀ t₀ ρ
  let F : Vec3 × ℝ → ℝ := fun z => backwardHeatCutoff
    (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z
  let g1 : ParabolicPoint → ℝ := fun z =>
    (vec3EuclideanNorm (u z)) ^ 2 *
      (timePartial F z + ∑ i, spatialSecondPartial F i i z)
  let g2 : ParabolicPoint → ℝ := fun z =>
    ((vec3EuclideanNorm (u z)) ^ 2 - c z) *
      (∑ i, u z i * spatialPartial F i z)
  let g3 : ParabolicPoint → ℝ := fun z =>
    2 * (p z - 0) * (∑ i, u z i * spatialPartial F i z)
  let g4 : ParabolicPoint → ℝ := fun z =>
    2 * (∑ i, f z i * u z i) * F z
  have htest := caccioppoli_heat_cutoff_testFunction hsol hρ hε hr hεr
    hsub hfuture
  have hFcont : ContDiff ℝ (⊤ : ℕ∞) F := by
    simpa only [F] using htest.1.1
  have hFsupp : tsupport F ⊆ euclideanClosedBall x₀ (3 * ρ / 4) ×ˢ
      Icc (t₀ - ρ ^ 2) (t₀ + ε) := by
    simpa only [F] using caccioppoli_heat_cutoff_tsupport_subset hρ hε hFcont
  have hΩ : MeasurableSet Ω := hsol.1.measurableSet
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 hρ hsub
  have hdata := hsol.2.2.2.2.2.1 Ω' J hbox
  have huStrong : AEStronglyMeasurable u (volume.restrict Q) := by
    exact AEStronglyMeasurable.mono_measure hdata.1
      (Measure.restrict_mono hcyl le_rfl)
  have hfStrong : AEStronglyMeasurable f (volume.restrict Q) := by
    exact AEStronglyMeasurable.mono_measure hdata.2.2.2.1
      (Measure.restrict_mono hcyl le_rfl)
  have huNormStrong : AEStronglyMeasurable
      (fun z : ParabolicPoint => vec3EuclideanNorm (u z))
      (volume.restrict Q) := by
    exact continuous_vec3EuclideanNorm.comp_aestronglyMeasurable huStrong
  have hp : AEMeasurable (fun z : ParabolicPoint => p z)
      (volume.restrict Q) := hdata.2.2.1.aemeasurable.mono_measure
        (Measure.restrict_mono hcyl le_rfl)
  have htimeC : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => timePartial F z) :=
    caccioppoli_timePartial_contDiff hFcont
  have hspC : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialPartial F i z) := fun i =>
    spatialPartial_contDiff hFcont i
  have hssC : ∀ i j : Fin 3, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialSecondPartial F i j z) := by
    intro i j
    exact spatialPartial_contDiff (spatialPartial_contDiff hFcont i) j
  have hsum := @caccioppoli_rhs_terms_bound_hsum_1 x₀ t₀ ρ r ε hρ hε hssC
  have hLstrong : AEStronglyMeasurable (fun z : ParabolicPoint =>
      timePartial F z + ∑ i, spatialSecondPartial F i i z)
      (volume.restrict Q) := by
    exact (htimeC.add hsum).continuous.aestronglyMeasurable
  have hD := @caccioppoli_rhs_terms_bound_hD_1 u x₀ t₀ ρ r ε hρ hε huStrong hspC
  have hg1 : AEMeasurable (fun z : ParabolicPoint =>
      (vec3EuclideanNorm (u z)) ^ 2 *
        (timePartial F z + ∑ i, spatialSecondPartial F i i z))
      (volume.restrict Q) := by
    exact ((huNormStrong.pow 2).mul hLstrong).aemeasurable
  have hg2 := @caccioppoli_rhs_terms_bound_hg2_1 u x₀ t₀ ρ r ε hρ hε c hcm huNormStrong hD
  have hg3 := @caccioppoli_rhs_terms_bound_hg3_2 u p x₀ t₀ ρ r ε hρ hε hp hD
  have hg4 := @caccioppoli_rhs_terms_bound_hg4_2 u f x₀ t₀ ρ r ε hρ hε hFcont huStrong hfStrong
  have hg1' : AEMeasurable g1 (volume.restrict Q) := by
    simpa only [g1] using hg1
  have hg2' : AEMeasurable g2 (volume.restrict Q) := by
    simpa only [g2] using hg2
  have hg3' : AEMeasurable g3 (volume.restrict Q) := by
    simpa only [g3] using hg3
  have hg4' : AEMeasurable g4 (volume.restrict Q) := by
    simpa only [g4] using hg4
  have hne1 := caccioppoli_I1_heat_cutoff_raw_ne_top hsol hρ hε hr hscale
    hεr hsub hfuture
  have hne2 := caccioppoli_I2_heat_cutoff_raw_ne_top hsol hρ hε hr hscale
    hsub hA hcenter hvelocity
  have hne3 := caccioppoli_I3_heat_cutoff_raw_ne_top hsol hρ hε hr hscale
    hsub hvelocity
  have hne4 := caccioppoli_I4_heat_cutoff_raw_ne_top hsol hρ hε hr hsub
    hvelocity
  have hraw1 := @caccioppoli_rhs_terms_bound_hraw1_3 u x₀ t₀ ρ r ε hρ hε hne1
  have hraw2 := @caccioppoli_rhs_terms_bound_hraw2_4 u x₀ t₀ ρ r ε hρ hε c hne2
  have hraw3 := @caccioppoli_rhs_terms_bound_hraw3_5 u p x₀ t₀ ρ r ε hρ hε hne3
  have hraw4 := @caccioppoli_rhs_terms_bound_hraw4_6 Ω I u f x₀ t₀ ρ r ε hρ hε htest hne4
  have hi1 : IntegrableOn g1 Q volume :=
    caccioppoli_integrable_of_lintegral_abs_ne_top hg1' hraw1
  have hi2 : IntegrableOn g2 Q volume :=
    caccioppoli_integrable_of_lintegral_abs_ne_top hg2' hraw2
  have hi3 : IntegrableOn g3 Q volume :=
    caccioppoli_integrable_of_lintegral_abs_ne_top hg3' hraw3
  have hi4 : IntegrableOn g4 Q volume :=
    caccioppoli_integrable_of_lintegral_abs_ne_top hg4' hraw4
  intro t ht
  let S : Set ParabolicPoint := Ω ×ˢ Iio t
  have hS : MeasurableSet S := hΩ.prod measurableSet_Iio
  have hzero := caccioppoli_terms_zero_ae_outside_cylinder
    (Ω := Ω) (x₀ := x₀) (t₀ := t₀) (ρ := ρ) (ε := ε) hρ hΩ hFcont hFsupp
    (u := u) (p := p) (f := f) (t := t) ht
  have hz1 := @caccioppoli_rhs_terms_bound_hz1_3 Ω u p f x₀ t₀ ρ r ε hρ hε t hzero
  have hz2 := @caccioppoli_rhs_terms_bound_hz2_2 Ω u p f x₀ t₀ ρ r ε hρ hε c t hzero
  have hz3 := @caccioppoli_rhs_terms_bound_hz3_4 Ω u p f x₀ t₀ ρ r ε hρ hε t hzero
  have hz4 := @caccioppoli_rhs_terms_bound_hz4_5 Ω u p f x₀ t₀ ρ r ε hρ hε t hzero
  have hi1S : IntegrableOn g1 S volume :=
    caccioppoli_integrable_term_on hS hi1 hz1
  have hi2S : IntegrableOn g2 S volume :=
    caccioppoli_integrable_term_on hS hi2 hz2
  have hi3S : IntegrableOn g3 S volume :=
    caccioppoli_integrable_term_on hS hi3 hz3
  have hi4S : IntegrableOn g4 S volume :=
    caccioppoli_integrable_term_on hS hi4 hz4
  have hterm1 := caccioppoli_integral_term_le_raw hS
    (measurableSet_parabolicCylinder x₀ t₀ ρ) hi1 hz1
  have hterm2 := caccioppoli_integral_term_le_raw hS
    (measurableSet_parabolicCylinder x₀ t₀ ρ) hi2 hz2
  have hterm3 := caccioppoli_integral_term_le_raw hS
    (measurableSet_parabolicCylinder x₀ t₀ ρ) hi3 hz3
  have hterm4 := caccioppoli_integral_term_le_raw hS
    (measurableSet_parabolicCylinder x₀ t₀ ρ) hi4 hz4
  let gC : ParabolicPoint → ℝ := fun z =>
    c z * (∑ i, u z i * spatialPartial F i z)
  have hRint := (suitableWeakSolution_energy_integrable hsol htest.1 htest.2).2.1
  have hRS := @caccioppoli_rhs_terms_bound_hRS_7 Ω u p f x₀ t₀ ρ r ε hρ hε t hRint
  have hsumS : IntegrableOn (fun z : ParabolicPoint =>
      g1 z + g2 z + g3 z + g4 z) S volume := by
    exact ((hi1S.add hi2S).add hi3S).add hi4S
  have hgc := @caccioppoli_rhs_terms_bound_hgc_8 Ω I u p f x₀ t₀ ρ r ε hρ hε hsub c t hRS hsumS
  let K : Set Vec3 := euclideanClosedBall x₀ (3 * ρ / 4)
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact isCompact_euclideanClosedBall x₀ (by positivity)
  have hKΩ := @caccioppoli_rhs_terms_bound_hKΩ_9 Ω I x₀ t₀ ρ hρ hsub
  obtain ⟨R, Ω₁, J, hρR, hbox, hball, hT, _⟩ :=
    caccioppoli_slice_poincare_ae hsol hρ hsub
  have hKR := @caccioppoli_rhs_terms_bound_hKR_3 x₀ ρ hρ R hρR
  have hKΩ₁ : K ⊆ Ω₁ := fun x hx => hball x (hKR hx)
  have hmem := ae_restrict_of_ae_restrict_of_subset hT
    (slice_memLp_ae_of_sws hsol hbox)
  have hUs := @caccioppoli_rhs_terms_bound_hUs_4 u Du x₀ t₀ ρ hKcompact Ω₁ hKΩ₁ hmem
  have hpair := caccioppoli_heat_cutoff_cancel hsol hρ hε hr hεr hsub hfuture
  have hFsuppK : tsupport F ⊆ K ×ˢ (Set.univ : Set ℝ) := by
    intro z hz
    exact ⟨(hFsupp hz).1, mem_univ _⟩
  have hDslice := @caccioppoli_rhs_terms_bound_hDslice_6 Ω u x₀ t₀ ρ r ε hρ hε hFcont hKcompact
    hKΩ hUs hpair hFsuppK
  have hDsliceInter : ∀ᵐ s ∂volume.restrict
      (Iio t ∩ Ioc (t₀ - ρ ^ 2) t₀),
      ∫ x in Ω, ∑ i, u (x, s) i * spatialPartial F i (x, s) = 0 :=
    ae_restrict_of_ae_restrict_of_subset (fun s hs => hs.2) hDslice
  have hDsliceInter' : ∀ᵐ s ∂volume,
      s ∈ Iio t ∩ Ioc (t₀ - ρ ^ 2) t₀ →
        ∫ x in Ω, ∑ i, u (x, s) i * spatialPartial F i (x, s) = 0 :=
    (ae_restrict_iff' (measurableSet_Iio.inter measurableSet_Ioc)).mp hDsliceInter
  have hneq : ∀ᵐ s ∂volume, s ≠ t₀ - ρ ^ 2 :=
    Measure.ae_ne (volume : Measure ℝ) (t₀ - ρ ^ 2)
  have hCslice := @caccioppoli_rhs_terms_bound_hCslice_10 Ω u p f x₀ t₀ ρ r ε hρ hε c hcc hFcont
    hFsupp t ht hzero hDsliceInter' hneq
  have hgcProd : IntegrableOn gC S
      ((volume : Measure Vec3).prod volume) := by
    rw [← volume_parabolicPoint_eq_prod]
    exact hgc
  have houterC := @caccioppoli_rhs_terms_bound_houterC_5 Ω u p f x₀ t₀ ρ r ε hρ hε c t hzero hCslice
  have hnestC := caccioppoli_energy_nested_integral_eq (Ω := Ω) (T := Iio t)
    (g := gC) hgcProd
  have hcancelC := @caccioppoli_rhs_terms_bound_hcancelC_6 Ω u x₀ t₀ ρ r ε hρ hε c t houterC hnestC
  have hpoint1 := @caccioppoli_rhs_terms_bound_hpoint1_7 u x₀ t₀ ρ r ε hρ hε
  have hpoint2 := @caccioppoli_rhs_terms_bound_hpoint2_11 u x₀ t₀ ρ r ε hρ hε c
  have hpoint3 := @caccioppoli_rhs_terms_bound_hpoint3_12 u p x₀ t₀ ρ r ε hρ hε
  have hpoint4 := @caccioppoli_rhs_terms_bound_hpoint4_13 Ω I u f x₀ t₀ ρ r ε hρ hε htest
  have hterm1' := hterm1.trans (ENNReal.toReal_mono hne1
    (lintegral_mono (μ := volume.restrict Q) hpoint1))
  have hterm2' := hterm2.trans (ENNReal.toReal_mono hne2
    (lintegral_mono (μ := volume.restrict Q) hpoint2))
  have hterm3' := hterm3.trans (ENNReal.toReal_mono hne3
    (lintegral_mono (μ := volume.restrict Q) hpoint3))
  have hterm4' := hterm4.trans (ENNReal.toReal_mono hne4
    (lintegral_mono (μ := volume.restrict Q) hpoint4))
  have hRprod := @caccioppoli_rhs_terms_bound_hRprod_8 Ω u p f x₀ t₀ ρ r ε hρ hε t hRint
  have hnestR := caccioppoli_energy_nested_integral_eq (Ω := Ω) (T := Iio t)
    (g := fun z : ParabolicPoint => localEnergyRhs u p f
      (backwardHeatCutoff
        (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r) z) hRprod
  have hR_eq := @caccioppoli_rhs_terms_bound_hR_eq_14 Ω u p f x₀ t₀ ρ r ε hρ hε c t hsumS hgc
    hcancelC
  exact caccioppoli_rhs_integral_sum_bound hR_eq hnestR
    hi1S hi2S hi3S hi4S hterm1' hterm2' hterm3' hterm4'
end CKN
