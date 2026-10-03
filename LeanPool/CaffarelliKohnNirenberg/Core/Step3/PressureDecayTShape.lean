/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.PressureDecayMeasurability
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.PressureDecay
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsUnconditionalP234
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsUnconditionalP56
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsUnconditionalP8
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsP7SolutionBound

/-!
# Pressure Decay TShape

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Core.Step3

open CKN

private lemma pressure_delta_sq_eq_scale_toReal_T
    {p : ParabolicPoint → ℝ} {z : ParabolicPoint} {r : ℝ}
    (hr : 0 < r) :
    delta p z r ^ 2 = r ^ (-4 / 3 : ℝ) *
      (eLpNorm' p (3 / 2 : ℝ)
        (volume.restrict (parabolicCylinder z.1 z.2 r))).toReal := by
  unfold delta
  have hnonneg : 0 ≤ (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal := ENNReal.toReal_nonneg
  have hbase : 0 ≤ r ^ (-2 : ℝ) *
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hbase]
  norm_num only [Nat.cast_ofNat]
  have hpow : (r ^ (-2 : ℝ) *
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal) ^ (2 / 3 : ℝ) =
      r ^ (-4 / 3 : ℝ) *
        (∫⁻ w in parabolicCylinder z.1 z.2 r,
          ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal ^ (2 / 3 : ℝ) := by
    rw [Real.mul_rpow (Real.rpow_nonneg (le_of_lt hr) _) hnonneg]
    rw [← Real.rpow_mul hr.le]
    norm_num
  rw [hpow]
  have heq : eLpNorm' p (3 / 2 : ℝ)
      (volume.restrict (parabolicCylinder z.1 z.2 r)) =
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
    rw [eLpNorm'_eq_lintegral_enorm]
    norm_num only [Nat.cast_ofNat]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [] with w
    rw [← ofReal_norm, Real.norm_eq_abs]
  rw [heq, ← ENNReal.toReal_rpow]
  ring_nf

private lemma pressure_eLpNorm_le_sum_T
    {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    {x₀ : Vec3} {t₀ r : ℝ}
    (hη : ∀ x, x ∈ vec3Ball x₀ r → η x = 1)
    (hmeas1 : AEStronglyMeasurable
      (fun z : ParabolicPoint => pressureP1 η u c p f z.2 z.1)
      (volume.restrict (parabolicCylinder x₀ t₀ r)))
    (hmeas2 : AEStronglyMeasurable
      (fun z : ParabolicPoint => pressureP2 η u c z.2 z.1)
      (volume.restrict (parabolicCylinder x₀ t₀ r)))
    (hmeas3 : AEStronglyMeasurable
      (fun z : ParabolicPoint => pressureP3 η u c z.2 z.1)
      (volume.restrict (parabolicCylinder x₀ t₀ r)))
    (hmeas4 : AEStronglyMeasurable
      (fun z : ParabolicPoint => pressureP4 η u c z.2 z.1)
      (volume.restrict (parabolicCylinder x₀ t₀ r)))
    (hmeas5 : AEStronglyMeasurable
      (fun z : ParabolicPoint => pressureP5 η p z.2 z.1)
      (volume.restrict (parabolicCylinder x₀ t₀ r)))
    (hmeas6 : AEStronglyMeasurable
      (fun z : ParabolicPoint => pressureP6 η p z.2 z.1)
      (volume.restrict (parabolicCylinder x₀ t₀ r)))
    (hmeas7 : AEStronglyMeasurable
      (fun z : ParabolicPoint => pressureP7 η f z.2 z.1)
      (volume.restrict (parabolicCylinder x₀ t₀ r)))
    (hmeas8 : AEStronglyMeasurable
      (fun z : ParabolicPoint => pressureP8 η f z.2 z.1)
      (volume.restrict (parabolicCylinder x₀ t₀ r))) :
    eLpNorm' p (3 / 2 : ℝ)
        (volume.restrict (parabolicCylinder x₀ t₀ r)) ≤
      ∑ k : Fin 8, eLpNorm'
        (fun z : ParabolicPoint => match k with
          | 0 => pressureP1 η u c p f z.2 z.1
          | 1 => pressureP2 η u c z.2 z.1
          | 2 => pressureP3 η u c z.2 z.1
          | 3 => pressureP4 η u c z.2 z.1
          | 4 => pressureP5 η p z.2 z.1
          | 5 => pressureP6 η p z.2 z.1
          | 6 => pressureP7 η f z.2 z.1
          | 7 => pressureP8 η f z.2 z.1)
        (3 / 2 : ℝ) (volume.restrict (parabolicCylinder x₀ t₀ r)) := by
  let μ : Measure ParabolicPoint := volume.restrict (parabolicCylinder x₀ t₀ r)
  have hrep : ∀ᵐ z ∂μ,
      p z = pressureP1 η u c p f z.2 z.1 + pressureP2 η u c z.2 z.1 +
        pressureP3 η u c z.2 z.1 + pressureP4 η u c z.2 z.1 +
        pressureP5 η p z.2 z.1 + pressureP6 η p z.2 z.1 +
        pressureP7 η f z.2 z.1 + pressureP8 η f z.2 z.1 := by
    filter_upwards [ae_restrict_mem (measurableSet_parabolicCylinder x₀ t₀ r)]
      with z hz
    rcases z with ⟨x, s⟩
    have hx := (mem_parabolicCylinder.mp hz).1
    have hpoint := pressure_decomposition_pointwise η u c p f s x
    simpa [hη x hx] using hpoint
  have hmono : eLpNorm' p (3 / 2 : ℝ) μ ≤
      eLpNorm' (fun z : ParabolicPoint => pressureP1 η u c p f z.2 z.1 +
        pressureP2 η u c z.2 z.1 + pressureP3 η u c z.2 z.1 +
        pressureP4 η u c z.2 z.1 + pressureP5 η p z.2 z.1 +
        pressureP6 η p z.2 z.1 + pressureP7 η f z.2 z.1 +
        pressureP8 η f z.2 z.1) (3 / 2 : ℝ) μ := by
    apply eLpNorm'_mono_ae (by norm_num)
    filter_upwards [hrep] with z hz
    rw [hz]
  have hsum := eLpNorm'_sum_le
    (s := (Finset.univ : Finset (Fin 8)))
    (f := fun k : Fin 8 => fun z : ParabolicPoint => match k with
      | 0 => pressureP1 η u c p f z.2 z.1
      | 1 => pressureP2 η u c z.2 z.1
      | 2 => pressureP3 η u c z.2 z.1
      | 3 => pressureP4 η u c z.2 z.1
      | 4 => pressureP5 η p z.2 z.1
      | 5 => pressureP6 η p z.2 z.1
      | 6 => pressureP7 η f z.2 z.1
      | 7 => pressureP8 η f z.2 z.1)
    (by intro k hk; fin_cases k <;> assumption)
    (by norm_num : (1 : ℝ) ≤ 3 / 2)
  have hfun : (∑ i : Fin 8, fun z : ParabolicPoint => match i with
      | 0 => pressureP1 η u c p f z.2 z.1
      | 1 => pressureP2 η u c z.2 z.1
      | 2 => pressureP3 η u c z.2 z.1
      | 3 => pressureP4 η u c z.2 z.1
      | 4 => pressureP5 η p z.2 z.1
      | 5 => pressureP6 η p z.2 z.1
      | 6 => pressureP7 η f z.2 z.1
      | 7 => pressureP8 η f z.2 z.1) =
      (fun z : ParabolicPoint => pressureP1 η u c p f z.2 z.1 +
        pressureP2 η u c z.2 z.1 + pressureP3 η u c z.2 z.1 +
        pressureP4 η u c z.2 z.1 + pressureP5 η p z.2 z.1 +
        pressureP6 η p z.2 z.1 + pressureP7 η f z.2 z.1 +
        pressureP8 η f z.2 z.1) := by
    funext z
    simp [Fin.sum_univ_succ]
    ring
  rw [hfun] at hsum
  exact hmono.trans hsum

private lemma pressure_five_group_bound_T
    {N a b c d e B₁ B₂ B₃ B₄ B₅ : ℝ≥0∞}
    (h₁ : N * a ≤ B₁) (h₂ : N * b ≤ B₂) (h₃ : N * c ≤ B₃)
    (h₄ : N * d ≤ B₄) (h₅ : N * e ≤ B₅) :
    N * (a + b + c + d + e) ≤ B₁ + B₂ + B₃ + B₄ + B₅ := by
  calc
    N * (a + b + c + d + e) = N * a + N * b + N * c + N * d + N * e := by ring
    _ ≤ B₁ + B₂ + B₃ + B₄ + B₅ := by
      exact add_le_add (add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄) h₅

private lemma pressureDecay_one_scale_Thterms_1_htri'_1 :
    ∀ {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
      {z : ParabolicPoint} {ρ r : ℝ} (hρ : (0 : ℝ) < ρ),
      let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ;
      let c : ℝ → Vec3 := fun (t : ℝ) (j : Fin (3 : ℕ)) =>
        ⨍ (y : Vec3) in vec3Ball z.1 ρ, u (y, t) j;
      @eLpNorm' _ _ _ MeasureSpace.toMeasurableSpace p (3 / 2 : ℝ)
            (Measure.restrict volume (parabolicCylinder z.1 z.2 r)) ≤
          ∑ k : Fin (8 : ℕ),
            @eLpNorm' _ ℝ _ MeasureSpace.toMeasurableSpace
              (fun (z : ParabolicPoint) =>
                match k with
                | (0 : Fin (8 : ℕ)) => pressureP1 η u c p f z.2 z.1
                | (1 : Fin (8 : ℕ)) => pressureP2 η u c z.2 z.1
                | (2 : Fin (8 : ℕ)) => pressureP3 η u c z.2 z.1
                | (3 : Fin (8 : ℕ)) => pressureP4 η u c z.2 z.1
                | (4 : Fin (8 : ℕ)) => pressureP5 η p z.2 z.1
                | (5 : Fin (8 : ℕ)) => pressureP6 η p z.2 z.1
                | (6 : Fin (8 : ℕ)) => pressureP7 η f z.2 z.1
                | (7 : Fin (8 : ℕ)) => pressureP8 η f z.2 z.1)
              (3 / 2 : ℝ) (Measure.restrict volume (parabolicCylinder z.1 z.2 r)) →
        let μ : Measure ParabolicPoint := Measure.restrict volume (parabolicCylinder z.1 z.2 r);
        eLpNorm' p (3 / 2 : ℝ) μ ≤
          eLpNorm' (ε := ℝ) (fun (w : ParabolicPoint) => pressureP1 η u c p f w.2 w.1) (3 / 2 : ℝ)
                    μ +
                  (eLpNorm' (ε := ℝ) (fun (w : ParabolicPoint) => pressureP2 η u c w.2 w.1)
                        (3 / 2 : ℝ) μ +
                      eLpNorm' (ε := ℝ) (fun (w : ParabolicPoint) => pressureP3 η u c w.2 w.1)
                        (3 / 2 : ℝ) μ +
                    eLpNorm' (ε := ℝ) (fun (w : ParabolicPoint) => pressureP4 η u c w.2 w.1)
                      (3 / 2 : ℝ) μ) +
                (eLpNorm' (ε := ℝ) (fun (w : ParabolicPoint) => pressureP5 η p w.2 w.1) (3 / 2 : ℝ)
                    μ +
                  eLpNorm' (ε := ℝ) (fun (w : ParabolicPoint) => pressureP6 η p w.2 w.1) (3 / 2 : ℝ)
                    μ) +
              eLpNorm' (ε := ℝ) (fun (w : ParabolicPoint) => pressureP7 η f w.2 w.1) (3 / 2 : ℝ) μ +
            eLpNorm' (ε := ℝ) (fun (w : ParabolicPoint) => pressureP8 η f w.2 w.1) (3 / 2 : ℝ) μ
    := by
  intro u p f z ρ r hρ η c htri μ
  calc
    _ ≤ ∑ k : Fin 8, eLpNorm'
        (fun w : ParabolicPoint => match k with
          | 0 => pressureP1 η u c p f w.2 w.1
          | 1 => pressureP2 η u c w.2 w.1
          | 2 => pressureP3 η u c w.2 w.1
          | 3 => pressureP4 η u c w.2 w.1
          | 4 => pressureP5 η p w.2 w.1
          | 5 => pressureP6 η p w.2 w.1
          | 6 => pressureP7 η f w.2 w.1
          | 7 => pressureP8 η f w.2 w.1)
        (3 / 2 : ℝ) μ := by exact htri
    _ = _ := by simp [Fin.sum_univ_succ]; ring

private lemma pressureDecay_one_scale_Thterms_1_hP234'_2 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} (C₁₂_p1 : ℝ)
      {z : ParabolicPoint} {ρ r : ℝ} (hρ : (0 : ℝ) < ρ),
      let pressureP12Constant : ℝ := max CKN.pressureP12Constant C₁₂_p1;
      let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ;
      let c : ℝ → Vec3 := fun (t : ℝ) (j : Fin (3 : ℕ)) =>
        ⨍ (y : Vec3) in vec3Ball z.1 ρ, u (y, t) j;
      let N : ℝ≥0∞ := ENNReal.ofReal (r ^ (-4 / 3 : ℝ));
      let μ : Measure ParabolicPoint := Measure.restrict volume (parabolicCylinder z.1 z.2 r);
      ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
            (@eLpNorm' _ ℝ _ MeasureSpace.toMeasurableSpace
                  (fun (w : ParabolicPoint) =>
                    pressureP2 (mollifiedBallCutoff z.1 hρ) u
                      (fun (t : ℝ) (j : Fin (3 : ℕ)) => ⨍ (y : Vec3) in vec3Ball z.1 ρ, u (y, t) j)
                      w.2 w.1)
                  (3 / 2 : ℝ) (Measure.restrict volume (parabolicCylinder z.1 z.2 r)) +
                @eLpNorm' _ ℝ _ MeasureSpace.toMeasurableSpace
                  (fun (w : ParabolicPoint) =>
                    pressureP3 (mollifiedBallCutoff z.1 hρ) u
                      (fun (t : ℝ) (j : Fin (3 : ℕ)) => ⨍ (y : Vec3) in vec3Ball z.1 ρ, u (y, t) j)
                      w.2 w.1)
                  (3 / 2 : ℝ) (Measure.restrict volume (parabolicCylinder z.1 z.2 r)) +
              @eLpNorm' _ ℝ _ MeasureSpace.toMeasurableSpace
                (fun (w : ParabolicPoint) =>
                  pressureP4 (mollifiedBallCutoff z.1 hρ) u
                    (fun (t : ℝ) (j : Fin (3 : ℕ)) => ⨍ (y : Vec3) in vec3Ball z.1 ρ, u (y, t) j)
                    w.2 w.1)
                (3 / 2 : ℝ) (Measure.restrict volume (parabolicCylinder z.1 z.2 r))) ≤
          ENNReal.ofReal (CKN.pressureP12Constant * (r / ρ) * alpha u z ρ * beta u Du z ρ) →
        (∀ {a b x y z : ℝ},
            a ≤ b → (0 : ℝ) ≤ x → (0 : ℝ) ≤ y → (0 : ℝ) ≤ z → a * x * y * z ≤ b * x * y * z) →
          (0 : ℝ) < r / ρ →
            (0 : ℝ) ≤ alpha u z ρ →
              (0 : ℝ) ≤ beta u Du z ρ →
                N *
                    (eLpNorm' (ε := ℝ) (fun (w : ParabolicPoint) => pressureP2 η u c w.2 w.1)
                          (3 / 2 : ℝ) μ +
                        eLpNorm' (ε := ℝ) (fun (w : ParabolicPoint) => pressureP3 η u c w.2 w.1)
                          (3 / 2 : ℝ) μ +
                      eLpNorm' (ε := ℝ) (fun (w : ParabolicPoint) => pressureP4 η u c w.2 w.1)
                        (3 / 2 : ℝ) μ) ≤
                  ENNReal.ofReal (pressureP12Constant * (r / ρ) * alpha u z ρ * beta u Du z ρ)
    := by
  intro u Du C₁₂_p1 z ρ r hρ pressureP12Constant η c N μ hP234 hmul4 hratio_pos halpha hbeta
  have hP234old : N * (eLpNorm' (fun w : ParabolicPoint => pressureP2 η u c w.2 w.1)
      (3 / 2 : ℝ) μ + eLpNorm' (fun w : ParabolicPoint => pressureP3 η u c w.2 w.1)
      (3 / 2 : ℝ) μ + eLpNorm' (fun w : ParabolicPoint => pressureP4 η u c w.2 w.1)
      (3 / 2 : ℝ) μ) ≤ ENNReal.ofReal (CKN.pressureP12Constant * (r / ρ) *
        alpha u z ρ * beta u Du z ρ) := by exact hP234
  calc
    _ ≤ ENNReal.ofReal (CKN.pressureP12Constant * (r / ρ) *
        alpha u z ρ * beta u Du z ρ) := hP234old
    _ ≤ _ := by
      apply ENNReal.ofReal_mono
      exact hmul4 (le_max_left CKN.pressureP12Constant C₁₂_p1)
        hratio_pos.le halpha hbeta

private lemma pressureDecay_one_scale_Thterms_1_hP56'_3 :
    ∀ {p : ParabolicPoint → ℝ} (C₁₂_p1 : ℝ) {z : ParabolicPoint} {ρ r : ℝ} (hρ : (0 : ℝ) < ρ),
      let pressureP12Constant : ℝ := max CKN.pressureP12Constant C₁₂_p1;
      let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ;
      let N : ℝ≥0∞ := ENNReal.ofReal (r ^ (-4 / 3 : ℝ));
      let μ : Measure ParabolicPoint := Measure.restrict volume (parabolicCylinder z.1 z.2 r);
      ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
            (@eLpNorm' _ ℝ _ MeasureSpace.toMeasurableSpace
                (fun (w : ParabolicPoint) => pressureP5 (mollifiedBallCutoff z.1 hρ) p w.2 w.1)
                (3 / 2 : ℝ) (Measure.restrict volume (parabolicCylinder z.1 z.2 r)) +
              @eLpNorm' _ ℝ _ MeasureSpace.toMeasurableSpace
                (fun (w : ParabolicPoint) => pressureP6 (mollifiedBallCutoff z.1 hρ) p w.2 w.1)
                (3 / 2 : ℝ) (Measure.restrict volume (parabolicCylinder z.1 z.2 r))) ≤
          ENNReal.ofReal (CKN.pressureP12Constant * (r / ρ) ^ (2 / 3 : ℝ) * delta p z ρ ^ (2 : ℕ)) →
        (∀ {a b x y : ℝ}, a ≤ b → (0 : ℝ) ≤ x → (0 : ℝ) ≤ y → a * x * y ≤ b * x * y) →
          (0 : ℝ) ≤ (r / ρ) ^ (2 / 3 : ℝ) →
            (0 : ℝ) ≤ delta p z ρ ^ (2 : ℕ) →
              N *
                  (eLpNorm' (ε := ℝ) (fun (w : ParabolicPoint) => pressureP5 η p w.2 w.1)
                      (3 / 2 : ℝ) μ +
                    eLpNorm' (ε := ℝ) (fun (w : ParabolicPoint) => pressureP6 η p w.2 w.1)
                      (3 / 2 : ℝ) μ) ≤
                ENNReal.ofReal (pressureP12Constant * (r / ρ) ^ (2 / 3 : ℝ) * delta p z ρ ^ (2 : ℕ))
    := by
  intro p C₁₂_p1 z ρ r hρ pressureP12Constant η N μ hP56 hmul3 hpow hdelta_sq
  have hP56old : N * (eLpNorm' (fun w : ParabolicPoint => pressureP5 η p w.2 w.1)
      (3 / 2 : ℝ) μ + eLpNorm' (fun w : ParabolicPoint => pressureP6 η p w.2 w.1)
      (3 / 2 : ℝ) μ) ≤ ENNReal.ofReal (CKN.pressureP12Constant * (r / ρ) ^ (2 / 3 : ℝ) *
        (delta p z ρ) ^ 2) := by exact hP56
  calc
    _ ≤ ENNReal.ofReal (CKN.pressureP12Constant * (r / ρ) ^ (2 / 3 : ℝ) *
        (delta p z ρ) ^ 2) := hP56old
    _ ≤ _ := by
      apply ENNReal.ofReal_mono
      exact hmul3 (le_max_left CKN.pressureP12Constant C₁₂_p1)
        hpow hdelta_sq

private lemma pressureDecay_one_scale_T_hterms_1 :
    ∀ {q : ℝ} {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3} (C₁₂_p1 : ℝ) {z : ParabolicPoint}
      {ρ r : ℝ} (hρ : (0 : ℝ) < ρ),
      (0 : ℝ) < r →
        ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
              @eLpNorm' _ ℝ _ MeasureSpace.toMeasurableSpace
                (fun (w : ParabolicPoint) =>
                  pressureP1 (mollifiedBallCutoff z.1 hρ) u
                    (fun (t : ℝ) (j : Fin (3 : ℕ)) => ⨍ (y : Vec3) in vec3Ball z.1 ρ, u (y, t) j) p
                    f w.2 w.1)
                (3 / 2 : ℝ) (Measure.restrict volume (parabolicCylinder z.1 z.2 r)) ≤
            ENNReal.ofReal (C₁₂_p1 * (r / ρ)⁻¹ * alpha u z ρ * beta u Du z ρ) →
          let pressureP12Constant : ℝ := max CKN.pressureP12Constant C₁₂_p1;
          let pressureP13Constant : ℝ → ℝ := fun (_ : ℝ) =>
            max (CKN.pressureP13Constant q) (pressureP7SolutionConstant q).toReal;
          ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
                @eLpNorm' _ ℝ _ MeasureSpace.toMeasurableSpace
                  (fun (w : ParabolicPoint) => pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1)
                  (3 / 2 : ℝ) (Measure.restrict volume (parabolicCylinder z.1 z.2 r)) ≤
              ENNReal.ofReal (pressureP13Constant q * (r / ρ) * lambda q f z ρ) →
            let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ;
            let c : ℝ → Vec3 := fun (t : ℝ) (j : Fin (3 : ℕ)) =>
              ⨍ (y : Vec3) in vec3Ball z.1 ρ, u (y, t) j;
            AEStronglyMeasurable (β := ℝ) (m₀ := MeasureSpace.toMeasurableSpace)
                (fun (w : ParabolicPoint) => pressureP8 (mollifiedBallCutoff z.1 hρ) f w.2 w.1)
                (Measure.restrict volume (parabolicCylinder z.1 z.2 ρ)) →
              @eLpNorm' _ _ _ MeasureSpace.toMeasurableSpace p (3 / 2 : ℝ)
                    (Measure.restrict volume (parabolicCylinder z.1 z.2 r)) ≤
                  ∑ k : Fin (8 : ℕ),
                    @eLpNorm' _ ℝ _ MeasureSpace.toMeasurableSpace
                      (fun (z : ParabolicPoint) =>
                        match k with
                        | (0 : Fin (8 : ℕ)) => pressureP1 η u c p f z.2 z.1
                        | (1 : Fin (8 : ℕ)) => pressureP2 η u c z.2 z.1
                        | (2 : Fin (8 : ℕ)) => pressureP3 η u c z.2 z.1
                        | (3 : Fin (8 : ℕ)) => pressureP4 η u c z.2 z.1
                        | (4 : Fin (8 : ℕ)) => pressureP5 η p z.2 z.1
                        | (5 : Fin (8 : ℕ)) => pressureP6 η p z.2 z.1
                        | (6 : Fin (8 : ℕ)) => pressureP7 η f z.2 z.1
                        | (7 : Fin (8 : ℕ)) => pressureP8 η f z.2 z.1)
                      (3 / 2 : ℝ) (Measure.restrict volume (parabolicCylinder z.1 z.2 r)) →
                let N : ℝ≥0∞ := ENNReal.ofReal (r ^ (-4 / 3 : ℝ));
                let μ : Measure ParabolicPoint :=
                  Measure.restrict volume (parabolicCylinder z.1 z.2 r);
                ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
                      (@eLpNorm' _ ℝ _ MeasureSpace.toMeasurableSpace
                            (fun (w : ParabolicPoint) =>
                              pressureP2 (mollifiedBallCutoff z.1 hρ) u
                                (fun (t : ℝ) (j : Fin (3 : ℕ)) =>
                                  ⨍ (y : Vec3) in vec3Ball z.1 ρ, u (y, t) j)
                                w.2 w.1)
                            (3 / 2 : ℝ) (Measure.restrict volume (parabolicCylinder z.1 z.2 r)) +
                          @eLpNorm' _ ℝ _ MeasureSpace.toMeasurableSpace
                            (fun (w : ParabolicPoint) =>
                              pressureP3 (mollifiedBallCutoff z.1 hρ) u
                                (fun (t : ℝ) (j : Fin (3 : ℕ)) =>
                                  ⨍ (y : Vec3) in vec3Ball z.1 ρ, u (y, t) j)
                                w.2 w.1)
                            (3 / 2 : ℝ) (Measure.restrict volume (parabolicCylinder z.1 z.2 r)) +
                        @eLpNorm' _ ℝ _ MeasureSpace.toMeasurableSpace
                          (fun (w : ParabolicPoint) =>
                            pressureP4 (mollifiedBallCutoff z.1 hρ) u
                              (fun (t : ℝ) (j : Fin (3 : ℕ)) =>
                                ⨍ (y : Vec3) in vec3Ball z.1 ρ, u (y, t) j)
                              w.2 w.1)
                          (3 / 2 : ℝ) (Measure.restrict volume (parabolicCylinder z.1 z.2 r))) ≤
                    ENNReal.ofReal
                      (CKN.pressureP12Constant * (r / ρ) * alpha u z ρ * beta u Du z ρ) →
                  ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
                        (@eLpNorm' _ ℝ _ MeasureSpace.toMeasurableSpace
                            (fun (w : ParabolicPoint) =>
                              pressureP5 (mollifiedBallCutoff z.1 hρ) p w.2 w.1)
                            (3 / 2 : ℝ) (Measure.restrict volume (parabolicCylinder z.1 z.2 r)) +
                          @eLpNorm' _ ℝ _ MeasureSpace.toMeasurableSpace
                            (fun (w : ParabolicPoint) =>
                              pressureP6 (mollifiedBallCutoff z.1 hρ) p w.2 w.1)
                            (3 / 2 : ℝ) (Measure.restrict volume (parabolicCylinder z.1 z.2 r))) ≤
                      ENNReal.ofReal
                        (CKN.pressureP12Constant * (r / ρ) ^ (2 / 3 : ℝ) * delta p z ρ ^ (2 : ℕ)) →
                    ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
                          @eLpNorm' _ ℝ _ MeasureSpace.toMeasurableSpace
                            (fun (w : ParabolicPoint) =>
                              pressureP8 (mollifiedBallCutoff z.1 hρ) f w.2 w.1)
                            (3 / 2 : ℝ) (Measure.restrict volume (parabolicCylinder z.1 z.2 r)) ≤
                        ENNReal.ofReal (CKN.pressureP13Constant q * (r / ρ) * lambda q f z ρ) →
                      N * eLpNorm' p (3 / 2 : ℝ) μ ≤
                        ENNReal.ofReal
                                  (pressureP12Constant * (r / ρ)⁻¹ * alpha u z ρ * beta u Du z ρ) +
                                ENNReal.ofReal
                                  (pressureP12Constant * (r / ρ) * alpha u z ρ * beta u Du z ρ) +
                              ENNReal.ofReal
                                (pressureP12Constant * (r / ρ) ^ (2 / 3 : ℝ) *
                                  delta p z ρ ^ (2 : ℕ)) +
                            ENNReal.ofReal (pressureP13Constant q * (r / ρ) * lambda q f z ρ) +
                          ENNReal.ofReal (pressureP13Constant q * (r / ρ) * lambda q f z ρ)
    := by
  intro q u Du p f C₁₂_p1 z ρ r hρ hr hCZ_p1 pressureP12Constant pressureP13Constant hP7common η c
    hP8' htri N μ hP234 hP56 hP8
  have htri' := @pressureDecay_one_scale_Thterms_1_htri'_1 u p f z ρ r hρ htri
  have hmul := mul_le_mul_of_nonneg_left htri' (by positivity : 0 ≤ N)
  have hCZbase : N * eLpNorm' (fun w : ParabolicPoint => pressureP1 η u c p f w.2 w.1)
      (3 / 2 : ℝ) μ ≤ ENNReal.ofReal (C₁₂_p1 * (r / ρ)⁻¹ *
        alpha u z ρ * beta u Du z ρ) := by exact hCZ_p1
  have hmul3 {a b x y : ℝ} (hab : a ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y) :
      a * x * y ≤ b * x * y := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hab hx) hy
  have hmul4 {a b x y z : ℝ} (hab : a ≤ b) (hx : 0 ≤ x)
      (hy : 0 ≤ y) (hz : 0 ≤ z) :
      a * x * y * z ≤ b * x * y * z := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hab hx) hy) hz
  have hratio_pos : 0 < r / ρ := div_pos hr hρ
  have hratio_inv_nonneg : 0 ≤ (r / ρ)⁻¹ := (inv_pos.mpr hratio_pos).le
  have halpha : 0 ≤ alpha u z ρ := by
    unfold alpha
    positivity
  have hbeta : 0 ≤ beta u Du z ρ := by
    unfold beta
    positivity
  have hpow : 0 ≤ (r / ρ) ^ (2 / 3 : ℝ) := by
    exact Real.rpow_nonneg hratio_pos.le _
  have hdelta_sq : 0 ≤ (delta p z ρ) ^ 2 := sq_nonneg _
  have hlam : 0 ≤ lambda q f z ρ := by
    unfold lambda
    positivity
  have hCZ' : N * eLpNorm' (fun w : ParabolicPoint => pressureP1 η u c p f w.2 w.1)
      (3 / 2 : ℝ) μ ≤ ENNReal.ofReal (pressureP12Constant * (r / ρ)⁻¹ *
        alpha u z ρ * beta u Du z ρ) := by
    calc
      _ ≤ ENNReal.ofReal (C₁₂_p1 * (r / ρ)⁻¹ *
          alpha u z ρ * beta u Du z ρ) := hCZbase
      _ ≤ _ := by
        apply ENNReal.ofReal_mono
        exact hmul4 (le_max_right CKN.pressureP12Constant C₁₂_p1)
          hratio_inv_nonneg halpha hbeta
  have hP234' := @pressureDecay_one_scale_Thterms_1_hP234'_2 u Du C₁₂_p1 z ρ r hρ hP234 hmul4
    hratio_pos halpha hbeta
  have hP56' := @pressureDecay_one_scale_Thterms_1_hP56'_3 p C₁₂_p1 z ρ r hρ hP56 hmul3 hpow
    hdelta_sq
  have hP7'' : N * eLpNorm' (fun w : ParabolicPoint => pressureP7 η f w.2 w.1)
      (3 / 2 : ℝ) μ ≤ ENNReal.ofReal (pressureP13Constant q * (r / ρ) *
        lambda q f z ρ) := by exact hP7common
  have hP8' : N * eLpNorm' (fun w : ParabolicPoint => pressureP8 η f w.2 w.1)
      (3 / 2 : ℝ) μ ≤ ENNReal.ofReal (pressureP13Constant q * (r / ρ) *
        lambda q f z ρ) := by
    have hP8old := hP8
    calc
      _ ≤ ENNReal.ofReal (CKN.pressureP13Constant q * (r / ρ) *
          lambda q f z ρ) := by exact hP8old
      _ ≤ _ := by
        apply ENNReal.ofReal_mono
        exact hmul3 (le_max_left (CKN.pressureP13Constant q)
          (pressureP7SolutionConstant q).toReal) hratio_pos.le hlam
  let A : ℝ≥0∞ := eLpNorm' (fun w : ParabolicPoint =>
    pressureP1 η u c p f w.2 w.1) (3 / 2 : ℝ) μ
  let B : ℝ≥0∞ := eLpNorm' (fun w : ParabolicPoint =>
    pressureP2 η u c w.2 w.1) (3 / 2 : ℝ) μ +
    eLpNorm' (fun w : ParabolicPoint => pressureP3 η u c w.2 w.1)
      (3 / 2 : ℝ) μ + eLpNorm' (fun w : ParabolicPoint =>
    pressureP4 η u c w.2 w.1) (3 / 2 : ℝ) μ
  let C : ℝ≥0∞ := eLpNorm' (fun w : ParabolicPoint =>
    pressureP5 η p w.2 w.1) (3 / 2 : ℝ) μ +
    eLpNorm' (fun w : ParabolicPoint => pressureP6 η p w.2 w.1)
      (3 / 2 : ℝ) μ
  let D : ℝ≥0∞ := eLpNorm' (fun w : ParabolicPoint =>
    pressureP7 η f w.2 w.1) (3 / 2 : ℝ) μ
  let E : ℝ≥0∞ := eLpNorm' (fun w : ParabolicPoint =>
    pressureP8 η f w.2 w.1) (3 / 2 : ℝ) μ
  have hmul' : N * eLpNorm' p (3 / 2 : ℝ) μ ≤ N * (A + B + C + D + E) := by
    exact hmul
  have hgroup := pressure_five_group_bound_T hCZ' hP234' hP56' hP7'' hP8'
  have hgroup' : N * (A + B + C + D + E) ≤
      ENNReal.ofReal (pressureP12Constant * (r / ρ)⁻¹ *
          alpha u z ρ * beta u Du z ρ) +
        ENNReal.ofReal (pressureP12Constant * (r / ρ) *
          alpha u z ρ * beta u Du z ρ) +
        ENNReal.ofReal (pressureP12Constant * (r / ρ) ^ (2 / 3 : ℝ) *
          (delta p z ρ) ^ 2) +
        ENNReal.ofReal (pressureP13Constant q * (r / ρ) *
          lambda q f z ρ) +
        ENNReal.ofReal (pressureP13Constant q * (r / ρ) *
          lambda q f z ρ) := by
    exact hgroup
  exact hmul'.trans hgroup'

private lemma pressureDecay_one_scale_T_hrightfin_2 :
    ∀ {q : ℝ} {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3} (C₁₂_p1 : ℝ) {z : ParabolicPoint}
      {ρ r : ℝ},
      let pressureP12Constant : ℝ := max CKN.pressureP12Constant C₁₂_p1;
      let pressureP13Constant : ℝ → ℝ := fun (_ : ℝ) =>
        max (CKN.pressureP13Constant q) (pressureP7SolutionConstant q).toReal;
      ENNReal.ofReal (pressureP12Constant * (r / ρ)⁻¹ * alpha u z ρ * beta u Du z ρ) +
                ENNReal.ofReal (pressureP12Constant * (r / ρ) * alpha u z ρ * beta u Du z ρ) +
              ENNReal.ofReal (pressureP12Constant * (r / ρ) ^ (2 / 3 : ℝ) * delta p z ρ ^ (2 : ℕ)) +
            ENNReal.ofReal (pressureP13Constant q * (r / ρ) * lambda q f z ρ) +
          ENNReal.ofReal (pressureP13Constant q * (r / ρ) * lambda q f z ρ) ≠
        ∞
    := by
  intro q u Du p f C₁₂_p1 z ρ r pressureP12Constant pressureP13Constant
  apply ENNReal.add_ne_top.mpr
  constructor
  · apply ENNReal.add_ne_top.mpr
    constructor
    · apply ENNReal.add_ne_top.mpr
      constructor
      · apply ENNReal.add_ne_top.mpr
        exact ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
      · exact ENNReal.ofReal_ne_top
    · exact ENNReal.ofReal_ne_top
  · exact ENNReal.ofReal_ne_top

private lemma pressureDecay_one_scale_T_hrhs_toReal_3 :
    ∀ {q : ℝ} {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3} (C₁₂_p1 : ℝ) {z : ParabolicPoint}
      {ρ r : ℝ},
      (0 : ℝ) < ρ →
        (0 : ℝ) < r →
          let pressureP12Constant : ℝ := max CKN.pressureP12Constant C₁₂_p1;
          let pressureP13Constant : ℝ → ℝ := fun (_ : ℝ) =>
            max (CKN.pressureP13Constant q) (pressureP7SolutionConstant q).toReal;
          (0 : ℝ) ≤ CKN.pressureP12Constant →
            (0 : ℝ) ≤ CKN.pressureP13Constant q →
              (ENNReal.ofReal (pressureP12Constant * (r / ρ)⁻¹ * alpha u z ρ * beta u Du z ρ) +
                          ENNReal.ofReal
                            (pressureP12Constant * (r / ρ) * alpha u z ρ * beta u Du z ρ) +
                        ENNReal.ofReal
                          (pressureP12Constant * (r / ρ) ^ (2 / 3 : ℝ) * delta p z ρ ^ (2 : ℕ)) +
                      ENNReal.ofReal (pressureP13Constant q * (r / ρ) * lambda q f z ρ) +
                    ENNReal.ofReal (pressureP13Constant q * (r / ρ) * lambda q f z ρ)).toReal =
                pressureP12Constant * (r / ρ)⁻¹ * alpha u z ρ * beta u Du z ρ +
                        pressureP12Constant * (r / ρ) * alpha u z ρ * beta u Du z ρ +
                      pressureP12Constant * (r / ρ) ^ (2 / 3 : ℝ) * delta p z ρ ^ (2 : ℕ) +
                    pressureP13Constant q * (r / ρ) * lambda q f z ρ +
                  pressureP13Constant q * (r / ρ) * lambda q f z ρ
    := by
  intro q u Du p f C₁₂_p1 z ρ r hρ hr pressureP12Constant pressureP13Constant hP12base hP13base
  have hA : ENNReal.ofReal (pressureP12Constant * (r / ρ)⁻¹ *
      alpha u z ρ * beta u Du z ρ) ≠ ∞ := ENNReal.ofReal_ne_top
  have hB : ENNReal.ofReal (pressureP12Constant * (r / ρ) *
      alpha u z ρ * beta u Du z ρ) ≠ ∞ := ENNReal.ofReal_ne_top
  have hC : ENNReal.ofReal (pressureP12Constant * (r / ρ) ^ (2 / 3 : ℝ) *
      (delta p z ρ) ^ 2) ≠ ∞ := ENNReal.ofReal_ne_top
  have hD : ENNReal.ofReal (pressureP13Constant q * (r / ρ) *
      lambda q f z ρ) ≠ ∞ := ENNReal.ofReal_ne_top
  have hα : 0 ≤ alpha u z ρ := by
    unfold alpha
    positivity
  have hβ : 0 ≤ beta u Du z ρ := by
    unfold beta
    positivity
  have hlam : 0 ≤ lambda q f z ρ := by
    unfold lambda
    positivity
  have hAn : 0 ≤ pressureP12Constant * (r / ρ)⁻¹ *
      alpha u z ρ * beta u Du z ρ := by positivity
  have hBn : 0 ≤ pressureP12Constant * (r / ρ) *
      alpha u z ρ * beta u Du z ρ := by positivity
  have hCn : 0 ≤ pressureP12Constant * (r / ρ) ^ (2 / 3 : ℝ) *
      (delta p z ρ) ^ 2 := by positivity
  have hDn : 0 ≤ pressureP13Constant q * (r / ρ) *
      lambda q f z ρ := by positivity
  have hAB :
      (ENNReal.ofReal (pressureP12Constant * (r / ρ)⁻¹ *
        alpha u z ρ * beta u Du z ρ) +
        ENNReal.ofReal (pressureP12Constant * (r / ρ) *
          alpha u z ρ * beta u Du z ρ)) ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hA, hB⟩
  have hABC :
      (ENNReal.ofReal (pressureP12Constant * (r / ρ)⁻¹ *
        alpha u z ρ * beta u Du z ρ) +
        ENNReal.ofReal (pressureP12Constant * (r / ρ) *
          alpha u z ρ * beta u Du z ρ) +
        ENNReal.ofReal (pressureP12Constant * (r / ρ) ^ (2 / 3 : ℝ) *
          (delta p z ρ) ^ 2)) ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hAB, hC⟩
  have hABCD :
      (ENNReal.ofReal (pressureP12Constant * (r / ρ)⁻¹ *
        alpha u z ρ * beta u Du z ρ) +
        ENNReal.ofReal (pressureP12Constant * (r / ρ) *
          alpha u z ρ * beta u Du z ρ) +
        ENNReal.ofReal (pressureP12Constant * (r / ρ) ^ (2 / 3 : ℝ) *
          (delta p z ρ) ^ 2) +
        ENNReal.ofReal (pressureP13Constant q * (r / ρ) *
          lambda q f z ρ)) ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hABC, hD⟩
  rw [ENNReal.toReal_add hABCD hD, ENNReal.toReal_add hABC hD,
    ENNReal.toReal_add hAB hC, ENNReal.toReal_add hA hB]
  rw [ENNReal.toReal_ofReal hAn, ENNReal.toReal_ofReal hBn,
    ENNReal.toReal_ofReal hCn, ENNReal.toReal_ofReal hDn]

theorem pressureDecay_one_scale_T
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (C₁₂_p1 : ℝ)
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hhalf : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hCZ_p1 : ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
      eLpNorm' (fun w : ParabolicPoint => pressureP1
        (mollifiedBallCutoff z.1 hρ) u
        (fun t j => MeasureTheory.average
          (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
        p f w.2 w.1) (3 / 2 : ℝ)
        (volume.restrict (parabolicCylinder z.1 z.2 r)) ≤
      ENNReal.ofReal (C₁₂_p1 * (r / ρ)⁻¹ *
        alpha u z ρ * beta u Du z ρ))
    :
    delta p z r ≤
      Real.sqrt (2 * max pressureP12Constant C₁₂_p1) *
          (r / ρ) ^ (-1 / 2 : ℝ) *
          Real.sqrt (alpha u z ρ) * Real.sqrt (beta u Du z ρ) +
        Real.sqrt (2 * max pressureP12Constant C₁₂_p1) *
            (r / ρ) ^ (1 / 3 : ℝ) *
          delta p z ρ +
        Real.sqrt (2 * max (pressureP13Constant q)
          (pressureP7SolutionConstant q).toReal) *
            (r / ρ) ^ (1 / 2 : ℝ) *
          Real.sqrt (lambda q f z ρ) := by
  let pressureP12Constant : ℝ := max CKN.pressureP12Constant C₁₂_p1
  let pressureP13Constant : ℝ → ℝ := fun _ =>
    max (CKN.pressureP13Constant q) (pressureP7SolutionConstant q).toReal
  have hP12base : 0 ≤ CKN.pressureP12Constant := by
    rw [CKN.pressureP12Constant]
    rcases le_total CKN.pressureP234Constant CKN.pressureP56Constant with h | h
    · rw [max_eq_right h]
      exact CKN.pressureP56Constant_nonneg (x₀ := (0 : Vec3)) (ρ := 1) (by norm_num)
    · rw [max_eq_left h]
      exact CKN.pressureP234Constant_nonneg (x₀ := (0 : Vec3)) (ρ := 1) (by norm_num)
  have hP13base : 0 ≤ CKN.pressureP13Constant q :=
    CKN.pressureP13Constant_nonneg (x₀ := (0 : Vec3)) (ρ := 1) (by norm_num)
  have hC12 : 0 ≤ pressureP12Constant := by
    dsimp [pressureP12Constant]
    exact le_trans hP12base (le_max_left _ _)
  have hC13 : 0 ≤ pressureP13Constant q := by
    dsimp [pressureP13Constant]
    exact le_trans hP13base (le_max_left _ _)
  have hq : 5 / 2 < q := hsol.2.2.2.1
  have hP7top : pressureP7SolutionConstant q ≠ ∞ :=
    pressureP7SolutionConstant_ne_top hq
  have hP7le : pressureP7SolutionConstant q ≤ ENNReal.ofReal (pressureP13Constant q) := by
    have hto : (pressureP7SolutionConstant q).toReal ≤ pressureP13Constant q := by
      dsimp [pressureP13Constant]
      exact le_max_right _ _
    calc
      pressureP7SolutionConstant q =
          ENNReal.ofReal (pressureP7SolutionConstant q).toReal :=
        (ENNReal.ofReal_toReal hP7top).symm
      _ ≤ ENNReal.ofReal (pressureP13Constant q) := ENNReal.ofReal_mono hto
  have hP7raw := pressureP7_bound hsol hρ hr hhalf hsub
  have hP7common :
      ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
          eLpNorm' (fun w : ParabolicPoint => pressureP7
            (mollifiedBallCutoff z.1 hρ) f w.2 w.1) (3 / 2 : ℝ)
            (volume.restrict (parabolicCylinder z.1 z.2 r)) ≤
        ENNReal.ofReal (pressureP13Constant q * (r / ρ) *
          lambda q f z ρ) := by
    calc
      _ ≤ pressureP7SolutionConstant q *
          ENNReal.ofReal ((r / ρ) * lambda q f z ρ) := hP7raw
      _ ≤ ENNReal.ofReal (pressureP13Constant q) *
          ENNReal.ofReal ((r / ρ) * lambda q f z ρ) :=
        mul_le_mul_of_nonneg_right hP7le (by positivity)
      _ = _ := by
        rw [show pressureP13Constant q * (r / ρ) * lambda q f z ρ =
          pressureP13Constant q * ((r / ρ) * lambda q f z ρ) by ring]
        rw [ENNReal.ofReal_mul (hC13)]
  let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ
  let c : ℝ → Vec3 := fun t j => MeasureTheory.average
    (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j)
  obtain ⟨B, T, η', c', hB, hT, hη', hc', hP1, hP2, hP3, hP4, hP5, hP6,
    hP7', hP8'⟩ := pressure_source_measurable_on_cylinder hsol hρ hsub
  subst B
  subst T
  subst η'
  have hc_eq : c' = c := by
    funext t
    simpa [c] using hc' t
  subst c'
  have hQr : parabolicCylinder z.1 z.2 r ⊆
      parabolicCylinder z.1 z.2 ρ :=
    parabolicCylinder_mono (by positivity)
      (by nlinarith only [hhalf, hρ])
  have hP1r := hP1.mono_measure (Measure.restrict_mono_set volume hQr)
  have hP2r := hP2.mono_measure (Measure.restrict_mono_set volume hQr)
  have hP3r := hP3.mono_measure (Measure.restrict_mono_set volume hQr)
  have hP4r := hP4.mono_measure (Measure.restrict_mono_set volume hQr)
  have hP5r := hP5.mono_measure (Measure.restrict_mono_set volume hQr)
  have hP6r := hP6.mono_measure (Measure.restrict_mono_set volume hQr)
  have hP7r := hP7'.mono_measure (Measure.restrict_mono_set volume hQr)
  have hP8r := hP8'.mono_measure (Measure.restrict_mono_set volume hQr)
  have htri := pressure_eLpNorm_le_sum_T (η := η) (u := u) (c := c)
    (p := p) (f := f) (x₀ := z.1) (t₀ := z.2) (r := r)
    (by
      intro x hx
      apply mollifiedBallCutoff_eq_one_on_inner z.1 hρ
      rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)]
      have hx' := mem_vec3Ball.mp hx
      have hrinner : r < 13 * ρ / 20 := by
        nlinarith only [hhalf, hρ]
      have hx'' : vecEuclideanNorm (x - z.1) < r := by
        simpa [vecEuclideanNorm, vec3EuclideanNorm, vecNormSq, vecDot, pow_two]
          using hx'
      exact lt_of_lt_of_le hx'' hrinner.le)
    hP1r hP2r
    hP3r hP4r
    hP5r hP6r
    hP7r hP8r
  let N : ℝ≥0∞ := ENNReal.ofReal (r ^ (-4 / 3 : ℝ))
  let μ : Measure ParabolicPoint := volume.restrict
    (parabolicCylinder z.1 z.2 r)
  have hP234 := pressureP234_bound hsol hρ hr hhalf hsub
  have hP56 := pressureP56_bound hsol hρ hr hhalf hsub
  have hP8 := pressureP8_bound hsol hρ hr hhalf hsub
  have hterms := @pressureDecay_one_scale_T_hterms_1 q u Du p f C₁₂_p1 z ρ r hρ hr hCZ_p1
    hP7common hP8' htri hP234 hP56 hP8
  have hrightfin := @pressureDecay_one_scale_T_hrightfin_2 q u Du p f C₁₂_p1 z ρ r
  have hleft : N * eLpNorm' p (3 / 2 : ℝ) μ ≠ ∞ := by
    exact ne_of_lt (lt_of_le_of_lt hterms (lt_top_iff_ne_top.mpr hrightfin))
  have hnormR := (ENNReal.toReal_le_toReal hleft hrightfin).2 hterms
  have hscale : 0 ≤ r ^ (-4 / 3 : ℝ) := by positivity
  simp only [N, ENNReal.toReal_mul, ENNReal.toReal_ofReal hscale] at hnormR
  have hP12nonneg : 0 ≤ pressureP12Constant := by
    exact hC12
  have hP13nonneg : 0 ≤ pressureP13Constant q := hC13
  have hrhs_toReal := @pressureDecay_one_scale_T_hrhs_toReal_3 q u Du p f C₁₂_p1 z ρ r hρ hr
    hP12base hP13base
  have hsq : (delta p z r) ^ 2 ≤
      pressureP12Constant * (r / ρ)⁻¹ * alpha u z ρ * beta u Du z ρ +
      pressureP12Constant * (r / ρ) * alpha u z ρ * beta u Du z ρ +
      pressureP12Constant * (r / ρ) ^ (2 / 3 : ℝ) * (delta p z ρ) ^ 2 +
      (2 * pressureP13Constant q) * (r / ρ) * lambda q f z ρ := by
    rw [pressure_delta_sq_eq_scale_toReal_T hr]
    calc
      _ ≤ pressureP12Constant * (r / ρ)⁻¹ * alpha u z ρ * beta u Du z ρ +
          pressureP12Constant * (r / ρ) * alpha u z ρ * beta u Du z ρ +
          pressureP12Constant * (r / ρ) ^ (2 / 3 : ℝ) * (delta p z ρ) ^ 2 +
          pressureP13Constant q * (r / ρ) * lambda q f z ρ +
          pressureP13Constant q * (r / ρ) * lambda q f z ρ := by
            rw [hrhs_toReal] at hnormR
            exact hnormR
      _ = _ := by
        ring
  apply pressureDecay_algebra
  · exact div_pos hr hρ
  · exact (div_le_iff₀ hρ).2 (by nlinarith only [hhalf])
  · exact hC12
  · exact mul_nonneg (by norm_num) hC13
  · unfold alpha; positivity
  · unfold beta; positivity
  · unfold delta; positivity
  · unfold lambda; positivity
  · unfold delta; positivity
  · exact hsq

end CKN.Core.Step3
