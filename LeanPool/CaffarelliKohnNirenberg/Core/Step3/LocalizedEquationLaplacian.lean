/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationBasics

/-!
# Localized Equation Laplacian

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
noncomputable section
namespace CKN.Core.Step3
open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Core.HeatPotential
private lemma laplacian_transfer_hBint_1 :
    ∀ {u : ParabolicPoint → Vec3} {_ : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {Ω' : Set Vec3}
      {J : Set ℝ},
      tsupport φ ⊆ Ω' ×ˢ J →
        ∀ {ψ : Vec3 × ℝ → Vec3},
          ContDiff ℝ (⊤ : ℕ∞) φ →
            HasCompactSupport φ →
              let μ : Measure ParabolicPoint := Measure.restrict volume (spaceTimeSet Ω' J);
              IsFiniteMeasure μ →
                (∀ (i : Fin (3 : ℕ)),
                    MemLp (ε := ℝ) (fun (z : ParabolicPoint) => u z i) (2 : ℝ≥0∞) μ) →
                  (∀ (i j : Fin (3 : ℕ)),
                      ContDiff ℝ (F := ℝ) (⊤ : ℕ∞) fun (z : Vec3 × ℝ) =>
                        spatialSecondPartial (fun (w : ParabolicPoint) => ψ w i) j j z) →
                    ∀ (i j : Fin (3 : ℕ)),
                      @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                        (fun (z : ParabolicPoint) =>
                          u z i *
                            (φ z * spatialSecondPartial (fun (w : ParabolicPoint) => ψ w i) j j z))
                        volume
    := by
  intro u f φ Ω' J hφbox ψ hφd hφc μ this huComp hφsecond i j
  have hbcont : Continuous (fun z : Vec3 × ℝ => φ z *
      spatialSecondPartial (fun w => ψ w i) j j z) :=
    (hφd.mul (hφsecond i j)).continuous
  have hbc := hφc.mul_right (f' := fun z : Vec3 × ℝ =>
    spatialSecondPartial (fun w => ψ w i) j j z)
  have hbs : tsupport (fun z : Vec3 × ℝ => φ z *
      spatialSecondPartial (fun w => ψ w i) j j z) ⊆
      (spaceTimeSet Ω' J : Set (Vec3 × ℝ)) := by
    exact (tsupport_mul_subset_left (f := φ) (g := fun z : Vec3 × ℝ =>
      spatialSecondPartial (fun w => ψ w i) j j z)).trans hφbox
  have hui : Integrable (fun z => u z i) μ := (huComp i).integrable (by norm_num)
  exact compact_factor_integrable (a := fun z => u z i)
    (b := fun z : Vec3 × ℝ => φ z * spatialSecondPartial
      (fun w => ψ w i) j j z) (by simpa [μ] using hui) hbcont hbc
    (by simpa [μ] using hbs)

private lemma laplacian_transfer_hAint_2 :
    ∀ {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {_ : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ}
      {Ω' : Set Vec3} {J : Set ℝ},
      tsupport φ ⊆ Ω' ×ˢ J →
        ∀ {ψ : Vec3 × ℝ → Vec3},
          ContDiff ℝ (⊤ : ℕ∞) φ →
            HasCompactSupport φ →
              let μ : Measure ParabolicPoint := Measure.restrict volume (spaceTimeSet Ω' J);
              IsFiniteMeasure μ →
                (∀ (i j : Fin (3 : ℕ)),
                    MemLp (ε := ℝ) (fun (z : ParabolicPoint) => Du z i j) (2 : ℝ≥0∞) μ) →
                  (∀ (i : Fin (3 : ℕ)),
                      ContDiff ℝ (F := ℝ) (⊤ : ℕ∞) fun (z : Vec3 × ℝ) => ψ z i) →
                    ∀ (i j : Fin (3 : ℕ)),
                      @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                        (fun (z : ParabolicPoint) =>
                          Du z i j * (φ z * spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z))
                        volume
    := by
  intro Du f φ Ω' J hφbox ψ hφd hφc μ this hDuComp hψi i j
  have hbcont : Continuous (fun z : Vec3 × ℝ => φ z *
      spatialPartial (fun w => ψ w i) j z) :=
    (hφd.mul (spatialPartial_contDiff (hψi i) j)).continuous
  have hbc := hφc.mul_right (f' := fun z : Vec3 × ℝ =>
    spatialPartial (fun w => ψ w i) j z)
  have hbs : tsupport (fun z : Vec3 × ℝ => φ z *
      spatialPartial (fun w => ψ w i) j z) ⊆
      (spaceTimeSet Ω' J : Set (Vec3 × ℝ)) := by
    exact (tsupport_mul_subset_left (f := φ) (g := fun z : Vec3 × ℝ =>
      spatialPartial (fun w => ψ w i) j z)).trans hφbox
  have hDui : Integrable (fun z => Du z i j) μ :=
    (hDuComp i j).integrable (by norm_num)
  exact compact_factor_integrable (a := fun z => Du z i j)
    (b := fun z : Vec3 × ℝ => φ z * spatialPartial
      (fun w => ψ w i) j z) (by simpa [μ] using hDui) hbcont hbc
    (by simpa [μ] using hbs)

private lemma laplacian_transfer_hCint_3 :
    ∀ {u : ParabolicPoint → Vec3} {_ : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {Ω' : Set Vec3}
      {J : Set ℝ},
      tsupport φ ⊆ Ω' ×ˢ J →
        ∀ {ψ : Vec3 × ℝ → Vec3},
          let μ : Measure ParabolicPoint := Measure.restrict volume (spaceTimeSet Ω' J);
          IsFiniteMeasure μ →
            (∀ (i : Fin (3 : ℕ)), MemLp (ε := ℝ) (fun (z : ParabolicPoint) => u z i) (2 : ℝ≥0∞) μ) →
              (∀ (j : Fin (3 : ℕ)),
                  ContDiff ℝ (F := ℝ) (⊤ : ℕ∞) fun (z : Vec3 × ℝ) =>
                    spatialPartial φ j z) →
                (∀ (i : Fin (3 : ℕ)),
                    ContDiff ℝ (F := ℝ) (⊤ : ℕ∞) fun (z : Vec3 × ℝ) => ψ z i) →
                  (∀ (j : Fin (3 : ℕ)),
                      HasCompactSupport (β := ℝ) fun (z : Vec3 × ℝ) => spatialPartial φ j z) →
                    (∀ (j : Fin (3 : ℕ)),
                        (tsupport (α := ℝ) fun (z : Vec3 × ℝ) => spatialPartial φ j z) ⊆
                          tsupport φ) →
                      ∀ (i j : Fin (3 : ℕ)),
                        @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                          (fun (z : ParabolicPoint) =>
                            u z i *
                              (spatialPartial φ j z *
                                spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z))
                          volume
    := by
  intro u f φ Ω' J hφbox ψ μ this huComp hφsp hψi hφsp_c hφsp_ts i j
  have hbcont : Continuous (fun z : Vec3 × ℝ => spatialPartial φ j z *
      spatialPartial (fun w => ψ w i) j z) :=
    (hφsp j |>.mul (spatialPartial_contDiff (hψi i) j)).continuous
  have hbc := (hφsp_c j).mul_right (f' := fun z : Vec3 × ℝ =>
    spatialPartial (fun w => ψ w i) j z)
  have hbs : tsupport (fun z : Vec3 × ℝ => spatialPartial φ j z *
      spatialPartial (fun w => ψ w i) j z) ⊆
      (spaceTimeSet Ω' J : Set (Vec3 × ℝ)) := by
    exact (tsupport_mul_subset_left (f := fun z : Vec3 × ℝ =>
      spatialPartial φ j z) (g := fun z : Vec3 × ℝ =>
        spatialPartial (fun w => ψ w i) j z)).trans (hφsp_ts j) |>.trans hφbox
  have hui : Integrable (fun z => u z i) (volume.restrict (spaceTimeSet Ω' J)) := by
    simpa [μ] using (huComp i).integrable (by norm_num)
  exact compact_factor_integrable (a := fun z => u z i)
    (b := fun z : Vec3 × ℝ => spatialPartial φ j z *
      spatialPartial (fun w => ψ w i) j z) hui hbcont hbc (by simpa [μ] using hbs)

private lemma laplacian_transfer_hslice_4 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {_ : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ}
      {Ω' : Set Vec3} {J : Set ℝ},
      localBox Ω I Ω' J →
        tsupport φ ⊆ Ω' ×ˢ J →
          ∀ {ψ : Vec3 × ℝ → Vec3},
            ContDiff ℝ (⊤ : ℕ∞) φ →
              (∀ (i : Fin (3 : ℕ)),
                  ContDiff ℝ (F := ℝ) (⊤ : ℕ∞) fun (z : Vec3 × ℝ) => ψ z i) →
                (∀ (i j : Fin (3 : ℕ)),
                    ∀ᵐ (t : ℝ) ∂Measure.restrict volume J,
                      @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                        (fun (x : Vec3) =>
                          u (x, t) i *
                            (φ (x, t) *
                              spatialSecondPartial (fun (w : ParabolicPoint) => ψ w i) j j (x, t)))
                        (Measure.restrict volume Ω')) →
                  (∀ (i j : Fin (3 : ℕ)),
                      ∀ᵐ (t : ℝ) ∂Measure.restrict volume J,
                        @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                          (fun (x : Vec3) =>
                            Du (x, t) i j *
                              (φ (x, t) *
                                spatialPartial (fun (w : ParabolicPoint) => ψ w i) j (x, t)))
                          (Measure.restrict volume Ω')) →
                    (∀ (i j : Fin (3 : ℕ)),
                        ∀ᵐ (t : ℝ) ∂Measure.restrict volume J,
                          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                            (fun (x : Vec3) =>
                              u (x, t) i *
                                (spatialPartial φ j (x, t) *
                                  spatialPartial (fun (w : ParabolicPoint) => ψ w i) j (x, t)))
                            (Measure.restrict volume Ω')) →
                      (∀ᵐ (t : ℝ) ∂Measure.restrict volume J,
                          ∀ (i j : Fin (3 : ℕ)),
                            HasWeakPartialDerivOn Ω' j (fun (x : Vec (3 : ℕ)) => u (x, t) i)
                              fun (x : Vec (3 : ℕ)) => Du (x, t) i j) →
                        ∀ (i j : Fin (3 : ℕ)),
                          ∀ᵐ (t : ℝ) ∂Measure.restrict volume J,
                            (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                                (Measure.restrict volume Ω') fun (x : Vec3) =>
                                u (x, t) i * φ (x, t) *
                                  spatialSecondPartial (fun (w : ParabolicPoint) => ψ w i) j j
                                    (x, t)) =
                              HSub.hSub (α := ℝ)
                                (-@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                                    (Measure.restrict volume Ω') fun (x : Vec3) =>
                                    Du (x, t) i j * φ (x, t) *
                                      spatialPartial (fun (w : ParabolicPoint) => ψ w i) j (x, t))
                                (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                                  (Measure.restrict volume Ω') fun (x : Vec3) =>
                                  u (x, t) i * spatialPartial φ j (x, t) *
                                    spatialPartial (fun (w : ParabolicPoint) => ψ w i) j (x, t))
    := by
  intro Ω I u Du f φ Ω' J hbox hφbox ψ hφd hψi hBslice hAslice hCslice hgrad_all i j
  filter_upwards [hgrad_all, hBslice i j, hAslice i j, hCslice i j]
    with t hgt hB hA hC
  let a : Vec3 → ℝ := fun x => φ (x, t) *
    spatialPartial (fun w => ψ w i) j (x, t)
  have hac : ContDiff ℝ (⊤ : ℕ∞) a := by
    exact (hφd.mul (spatialPartial_contDiff (hψi i) j)).comp
      (contDiff_prodMk_left (𝕜 := ℝ) (n := (⊤ : ℕ∞)) t)
  have has : HasCompactSupport a := by
    apply HasCompactSupport.of_support_subset_isCompact hbox.2.1
    intro x hx
    have hφx : φ (x, t) ≠ 0 := by
      intro hzero
      apply hx
      simp [a, hzero]
    have hpair : (x, t) ∈ tsupport φ :=
      subset_tsupport (f := φ) (Function.mem_support.mpr hφx)
    exact subset_closure (hφbox hpair).1
  have hat : tsupport a ⊆ Ω' := by
    have hclosed : IsClosed {x : Vec3 | (x, t) ∈ tsupport φ} :=
      (isClosed_tsupport φ).preimage
        (continuous_id.prodMk continuous_const)
    refine (closure_minimal ?_ hclosed).trans ?_
    · intro x hx
      have hφx : φ (x, t) ≠ 0 := by
        intro hzero
        apply hx
        simp [a, hzero]
      exact subset_tsupport (f := φ) (Function.mem_support.mpr hφx)
    · intro x hx
      exact (hφbox hx).1
  have hw := (hgt i j) a hac has hat
  have hderiv : ∀ x : Vec3,
      (fderiv ℝ a x) (basisVec j) =
        spatialPartial φ j (x, t) * spatialPartial
            (fun w => ψ w i) j (x, t) +
          φ (x, t) * spatialSecondPartial
            (fun w => ψ w i) j j (x, t) := by
    intro x
    simpa [a, spatialSecondPartial, spatialPartial] using
      (spatialPartial_mul_full hφd (spatialPartial_contDiff (hψi i) j)
        j (x, t))
  have hw' :
      (∫ x in Ω', u (x, t) i *
        (spatialPartial φ j (x, t) * spatialPartial
          (fun w => ψ w i) j (x, t) + φ (x, t) *
            spatialSecondPartial (fun w => ψ w i) j j (x, t))) =
        -∫ x in Ω', Du (x, t) i j * φ (x, t) *
          spatialPartial (fun w => ψ w i) j (x, t) := by
    calc
      (∫ x in Ω', u (x, t) i *
          (spatialPartial φ j (x, t) * spatialPartial
            (fun w => ψ w i) j (x, t) + φ (x, t) *
              spatialSecondPartial (fun w => ψ w i) j j (x, t))) =
          ∫ x in Ω', u (x, t) i * (fderiv ℝ a x) (basisVec j) := by
        apply setIntegral_congr_fun hbox.1.measurableSet
        intro x hx
        change u ((x, t) : ParabolicPoint) i *
            (spatialPartial φ j (x, t) * spatialPartial
              (fun w => ψ w i) j (x, t) + φ (x, t) *
                spatialSecondPartial (fun w => ψ w i) j j (x, t)) =
          u ((x, t) : ParabolicPoint) i *
            (fderiv ℝ a x) (basisVec j)
        rw [hderiv]
      _ = -∫ x in Ω', Du (x, t) i j * a x := hw
      _ = -∫ x in Ω', Du (x, t) i j * φ (x, t) *
          spatialPartial (fun w => ψ w i) j (x, t) := by
        congr 1
        apply setIntegral_congr_fun hbox.1.measurableSet
        intro x hx
        change Du ((x, t) : ParabolicPoint) i j *
          (φ (x, t) * spatialPartial (fun w => ψ w i) j (x, t)) =
          Du ((x, t) : ParabolicPoint) i j * φ (x, t) *
            spatialPartial (fun w => ψ w i) j (x, t)
        ring
  have hsplit :
      (∫ x in Ω', u (x, t) i *
        (spatialPartial φ j (x, t) * spatialPartial
          (fun w => ψ w i) j (x, t) + φ (x, t) *
            spatialSecondPartial (fun w => ψ w i) j j (x, t))) =
        (∫ x in Ω', u (x, t) i * spatialPartial φ j (x, t) *
          spatialPartial (fun w => ψ w i) j (x, t)) +
          ∫ x in Ω', u (x, t) i * φ (x, t) *
            spatialSecondPartial (fun w => ψ w i) j j (x, t) := by
    have hC' : Integrable (fun x : Vec3 => u (x, t) i *
        spatialPartial φ j (x, t) * spatialPartial
          (fun w => ψ w i) j (x, t)) (volume.restrict Ω') := by
      apply hC.congr
      filter_upwards [] with x
      ring
    have hB' : Integrable (fun x : Vec3 => u (x, t) i * φ (x, t) *
        spatialSecondPartial (fun w => ψ w i) j j (x, t))
        (volume.restrict Ω') := by
      apply hB.congr
      filter_upwards [] with x
      ring
    calc
      _ = ∫ x in Ω', (u (x, t) i * spatialPartial φ j (x, t) *
          spatialPartial (fun w => ψ w i) j (x, t)) +
          (u (x, t) i * φ (x, t) *
            spatialSecondPartial (fun w => ψ w i) j j (x, t)) := by
        apply setIntegral_congr_fun hbox.1.measurableSet
        intro x hx
        ring
      _ = _ := integral_add hC' hB'
  calc
    (∫ x in Ω', u (x, t) i * φ (x, t) *
        spatialSecondPartial (fun w => ψ w i) j j (x, t)) =
      ((∫ x in Ω', u (x, t) i * spatialPartial φ j (x, t) *
        spatialPartial (fun w => ψ w i) j (x, t)) +
        ∫ x in Ω', u (x, t) i * φ (x, t) *
          spatialSecondPartial (fun w => ψ w i) j j (x, t)) -
        ∫ x in Ω', u (x, t) i * spatialPartial φ j (x, t) *
          spatialPartial (fun w => ψ w i) j (x, t) := by ring
    _ = (-∫ x in Ω', Du (x, t) i j * φ (x, t) *
        spatialPartial (fun w => ψ w i) j (x, t)) -
        ∫ x in Ω', u (x, t) i * spatialPartial φ j (x, t) *
        spatialPartial (fun w => ψ w i) j (x, t) := by
          rw [← hsplit, hw']

private lemma laplacian_transfer_hBzero_5 :
    ∀ {u : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {Ω' : Set Vec3} {J : Set ℝ}
      {ψ : Vec3 × ℝ → Vec3},
      let B : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        ∑ i : Fin (3 : ℕ),
          ∑ j : Fin (3 : ℕ),
            u z i * (φ z * spatialSecondPartial (fun (w : ParabolicPoint) => ψ w i) j j z);
      (∀ z ∉ spaceTimeSet Ω' J, φ (z.1, z.2) = (0 : ℝ)) → ∀ z ∉ spaceTimeSet Ω' J, B z = (0 : ℝ)
    := by
  intro u φ Ω' J ψ B hφout z hz
  dsimp [B]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  have hφz : φ z = 0 := by
    change φ (z.1, z.2) = 0
    exact hφout z hz
  simp only [hφz, zero_mul, mul_zero]

private lemma laplacian_transfer_hAzero_6 :
    ∀ {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {φ : Vec3 × ℝ → ℝ} {Ω' : Set Vec3} {J : Set ℝ}
      {ψ : Vec3 × ℝ → Vec3},
      let A : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        ∑ i : Fin (3 : ℕ),
          ∑ j : Fin (3 : ℕ),
            Du z i j * (φ z * spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z);
      (∀ z ∉ spaceTimeSet Ω' J, φ (z.1, z.2) = (0 : ℝ)) → ∀ z ∉ spaceTimeSet Ω' J, A z = (0 : ℝ)
    := by
  intro Du φ Ω' J ψ A hφout z hz
  dsimp [A]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  have hφz : φ z = 0 := by
    change φ (z.1, z.2) = 0
    exact hφout z hz
  simp only [hφz, zero_mul, mul_zero]

private lemma laplacian_transfer_hCzero_7 :
    ∀ {u : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {Ω' : Set Vec3} {J : Set ℝ}
      {ψ : Vec3 × ℝ → Vec3},
      let C : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        ∑ i : Fin (3 : ℕ),
          ∑ j : Fin (3 : ℕ),
            u z i * (spatialPartial φ j z * spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z);
      (∀ (j : Fin (3 : ℕ)), ∀ z ∉ spaceTimeSet Ω' J, spatialPartial φ j (z.1, z.2) = (0 : ℝ)) →
        ∀ z ∉ spaceTimeSet Ω' J, C z = (0 : ℝ)
    := by
  intro u φ Ω' J ψ C hφspout z hz
  dsimp [C]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  have hφspz : spatialPartial φ j z = 0 := by
    change spatialPartial φ j (z.1, z.2) = 0
    exact hφspout j z hz
  simp only [hφspz, zero_mul, mul_zero]

private lemma laplacian_transfer_hsliceSum_8 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {φ : Vec3 × ℝ → ℝ}
      {Ω' : Set Vec3} {J : Set ℝ} {ψ : Vec3 × ℝ → Vec3},
      let B : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        ∑ i : Fin (3 : ℕ),
          ∑ j : Fin (3 : ℕ),
            u z i * (φ z * spatialSecondPartial (fun (w : ParabolicPoint) => ψ w i) j j z);
      let A : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        ∑ i : Fin (3 : ℕ),
          ∑ j : Fin (3 : ℕ),
            Du z i j * (φ z * spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z);
      let C : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        ∑ i : Fin (3 : ℕ),
          ∑ j : Fin (3 : ℕ),
            u z i * (spatialPartial φ j z * spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z);
      (∀ᵐ (t : ℝ) ∂Measure.restrict volume J,
          ∀ (i j : Fin (3 : ℕ)),
            @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
              (fun (x : Vec3) =>
                u (x, t) i *
                  (φ (x, t) * spatialSecondPartial (fun (w : ParabolicPoint) => ψ w i) j j (x, t)))
              (Measure.restrict volume Ω')) →
        (∀ᵐ (t : ℝ) ∂Measure.restrict volume J,
            ∀ (i j : Fin (3 : ℕ)),
              @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                (fun (x : Vec3) =>
                  Du (x, t) i j *
                    (φ (x, t) * spatialPartial (fun (w : ParabolicPoint) => ψ w i) j (x, t)))
                (Measure.restrict volume Ω')) →
          (∀ᵐ (t : ℝ) ∂Measure.restrict volume J,
              ∀ (i j : Fin (3 : ℕ)),
                @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                  (fun (x : Vec3) =>
                    u (x, t) i *
                      (spatialPartial φ j (x, t) *
                        spatialPartial (fun (w : ParabolicPoint) => ψ w i) j (x, t)))
                  (Measure.restrict volume Ω')) →
            (∀ᵐ (t : ℝ) ∂Measure.restrict volume J,
                ∀ (i j : Fin (3 : ℕ)),
                  (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω')
                      fun (x : Vec3) =>
                      u (x, t) i * φ (x, t) *
                        spatialSecondPartial (fun (w : ParabolicPoint) => ψ w i) j j (x, t)) =
                    HSub.hSub (α := ℝ)
                      (-@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                          (Measure.restrict volume Ω') fun (x : Vec3) =>
                          Du (x, t) i j * φ (x, t) *
                            spatialPartial (fun (w : ParabolicPoint) => ψ w i) j (x, t))
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω')
                        fun (x : Vec3) =>
                        u (x, t) i * spatialPartial φ j (x, t) *
                          spatialPartial (fun (w : ParabolicPoint) => ψ w i) j (x, t))) →
              ∀ᵐ (t : ℝ) ∂Measure.restrict volume J,
                (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω')
                    fun (x : Vec3) => B (x, t)) =
                  HSub.hSub (α := ℝ)
                    (-@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω')
                        fun (x : Vec3) => A (x, t))
                    (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume Ω')
                      fun (x : Vec3) => C (x, t))
    := by
  intro u Du φ Ω' J ψ B A C hBsliceAll hAsliceAll hCsliceAll hsliceAll
  filter_upwards [hsliceAll, hBsliceAll, hAsliceAll, hCsliceAll]
    with t hst hBst hAst hCst
  have hBs : Integrable (fun x : Vec3 => B (x, t))
      (volume.restrict Ω') := by
    dsimp [B]
    exact integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ =>
      integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ =>
        hBst i j))
  have hAs : Integrable (fun x : Vec3 => A (x, t))
      (volume.restrict Ω') := by
    dsimp [A]
    exact integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ =>
      integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ =>
        hAst i j))
  have hCs : Integrable (fun x : Vec3 => C (x, t))
      (volume.restrict Ω') := by
    dsimp [C]
    exact integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ =>
      integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ =>
        hCst i j))
  have hsumB :
      (∫ x in Ω', B (x, t)) =
        ∑ i, ∑ j, ∫ x in Ω',
          u (x, t) i * (φ (x, t) * spatialSecondPartial
            (fun w => ψ w i) j j (x, t)) := by
    dsimp [B]
    rw [integral_finsetSum (s := Finset.univ)]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum (s := Finset.univ)]
      intro j hj
      exact hBst i j
    · intro i hi
      exact integrable_finsetSum (Finset.univ : Finset (Fin 3))
        (fun j hj => hBst i j)
  have hsumA :
      (∫ x in Ω', A (x, t)) =
        ∑ i, ∑ j, ∫ x in Ω',
          Du (x, t) i j * (φ (x, t) * spatialPartial
            (fun w => ψ w i) j (x, t)) := by
    dsimp [A]
    rw [integral_finsetSum (s := Finset.univ)]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum (s := Finset.univ)]
      intro j hj
      exact hAst i j
    · intro i hi
      exact integrable_finsetSum (Finset.univ : Finset (Fin 3))
        (fun j hj => hAst i j)
  have hsumC :
      (∫ x in Ω', C (x, t)) =
        ∑ i, ∑ j, ∫ x in Ω',
          u (x, t) i * (spatialPartial φ j (x, t) * spatialPartial
            (fun w => ψ w i) j (x, t)) := by
    dsimp [C]
    rw [integral_finsetSum (s := Finset.univ)]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum (s := Finset.univ)]
      intro j hj
      exact hCst i j
    · intro i hi
      exact integrable_finsetSum (Finset.univ : Finset (Fin 3))
        (fun j hj => hCst i j)
  have hAassoc :
      (∑ i, ∑ j, ∫ x in Ω', Du (x, t) i j * φ (x, t) *
        spatialPartial (fun w => ψ w i) j (x, t)) =
        ∑ i, ∑ j, ∫ x in Ω', Du (x, t) i j *
          (φ (x, t) * spatialPartial (fun w => ψ w i) j (x, t)) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  have hCassoc :
      (∑ i, ∑ j, ∫ x in Ω', u (x, t) i * spatialPartial φ j (x, t) *
        spatialPartial (fun w => ψ w i) j (x, t)) =
        ∑ i, ∑ j, ∫ x in Ω', u (x, t) i *
          (spatialPartial φ j (x, t) *
            spatialPartial (fun w => ψ w i) j (x, t)) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [hsumB, hsumA, hsumC]
  calc
    (∑ i, ∑ j, ∫ x in Ω', u (x, t) i *
        (φ (x, t) * spatialSecondPartial (fun w => ψ w i) j j (x, t))) =
        ∑ i, ∑ j, ((-(∫ x in Ω', Du (x, t) i j * φ (x, t) *
          spatialPartial (fun w => ψ w i) j (x, t))) -
            (∫ x in Ω', u (x, t) i * spatialPartial φ j (x, t) *
              spatialPartial (fun w => ψ w i) j (x, t))) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simpa only [mul_assoc] using hst i j
    _ = (-(∑ i, ∑ j, ∫ x in Ω', Du (x, t) i j *
          (φ (x, t) * spatialPartial (fun w => ψ w i) j (x, t)))) -
        (∑ i, ∑ j, ∫ x in Ω', u (x, t) i *
          (spatialPartial φ j (x, t) *
            spatialPartial (fun w => ψ w i) j (x, t))) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
      rw [hAassoc, hCassoc]

private lemma laplacian_transfer_hAC_9 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {φ : Vec3 × ℝ → ℝ}
      {ψ : Vec3 × ℝ → Vec3},
      let A : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        ∑ i : Fin (3 : ℕ),
          ∑ j : Fin (3 : ℕ),
            Du z i j * (φ z * spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z);
      let C : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        ∑ i : Fin (3 : ℕ),
          ∑ j : Fin (3 : ℕ),
            u z i * (spatialPartial φ j z * spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z);
      @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace A volume →
        @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace C volume →
          (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (z : ParabolicPoint) =>
              ∑ i : Fin (3 : ℕ),
                ∑ j : Fin (3 : ℕ),
                  (Du z i j * (φ z * spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z) +
                    u z i *
                      (spatialPartial φ j z *
                        spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z))) =
            HAdd.hAdd (α := ℝ)
              (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (z : ParabolicPoint) =>
                A z)
              (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (z : ParabolicPoint) =>
                C z)
    := by
  intro u Du φ ψ A C hA hC
  have hsumA : Integrable (fun z => ∑ i, ∑ j,
      Du z i j * (φ z * spatialPartial (fun w => ψ w i) j z)) volume := hA
  have hsumC : Integrable (fun z => ∑ i, ∑ j,
      u z i * (spatialPartial φ j z * spatialPartial
        (fun w => ψ w i) j z)) volume := hC
  calc
    _ = ∫ z, (A z + C z) := by
      apply integral_congr_ae
      filter_upwards [] with z
      dsimp [A, C]
      simp only [Finset.sum_add_distrib]
    _ = _ := integral_add hsumA hsumC

private lemma laplacian_transfer_hφtime_c_1 :
    ∀ {φ : Vec3 × ℝ → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → HasCompactSupport (β := ℝ) fun (z : Vec3 × ℝ) => timePartial φ z
    := by
  intro φ hφd hφc
  apply HasCompactSupport.of_support_subset_isCompact hφc.isCompact
  intro z hz
  by_contra hnot
  apply hz
  exact timePartial_zero_of_not_mem_tsupport_public hφd hnot

private lemma laplacian_transfer_hφsp_c_2 :
    ∀ {φ : Vec3 × ℝ → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ →
          ∀ (j : Fin (3 : ℕ)), HasCompactSupport (β := ℝ) fun (z : Vec3 × ℝ) => spatialPartial φ j z
    := by
  intro φ hφd hφc j
  apply HasCompactSupport.of_support_subset_isCompact hφc.isCompact
  intro z hz
  by_contra hnot
  apply hz
  exact spatialPartial_zero_of_not_mem_tsupport_public hφd hnot j

private lemma laplacian_transfer_hφsp_ts_3 :
    ∀ {φ : Vec3 × ℝ → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) φ →
        ∀ (j : Fin (3 : ℕ)),
          (tsupport (α := ℝ) fun (z : Vec3 × ℝ) => spatialPartial φ j z) ⊆ tsupport φ
    := by
  intro φ hφd j
  apply closure_minimal
  · intro z hz
    by_contra hnot
    apply hz
    exact spatialPartial_zero_of_not_mem_tsupport_public hφd hnot j
  · exact isClosed_tsupport φ

private lemma laplacian_transfer_hBslice_4 :
    ∀ {_ : ℝ} {u : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {Ω' : Set Vec3} {J : Set ℝ}
      {ψ : Vec3 × ℝ → Vec3},
      (∀ (i j : Fin (3 : ℕ)),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
            (fun (z : ParabolicPoint) =>
              u z i * (φ z * spatialSecondPartial (fun (w : ParabolicPoint) => ψ w i) j j z))
            volume) →
        ∀ (i j : Fin (3 : ℕ)),
          ∀ᵐ (t : ℝ) ∂Measure.restrict volume J,
            @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
              (fun (x : Vec3) =>
                u (x, t) i *
                  (φ (x, t) * spatialSecondPartial (fun (w : ParabolicPoint) => ψ w i) j j (x, t)))
              (Measure.restrict volume Ω')
    := by
  intro q u φ Ω' J ψ hBint i j
  have h := (hBint i j).mono_measure
    (Measure.restrict_le_self : volume.restrict (spaceTimeSet Ω' J) ≤ volume)
  change Integrable (fun q : Vec3 × ℝ =>
    u ((q.1, q.2) : ParabolicPoint) i *
      (φ q * spatialSecondPartial (fun w => ψ w i) j j q))
    (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict (Ω' ×ˢ J)) at h
  rw [← Measure.prod_restrict Ω' J] at h
  exact h.prod_left_ae

private lemma laplacian_transfer_hAslice_5 :
    ∀ {_ : ℝ} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {φ : Vec3 × ℝ → ℝ} {Ω' : Set Vec3}
      {J : Set ℝ} {ψ : Vec3 × ℝ → Vec3},
      (∀ (i j : Fin (3 : ℕ)),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
            (fun (z : ParabolicPoint) =>
              Du z i j * (φ z * spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z))
            volume) →
        ∀ (i j : Fin (3 : ℕ)),
          ∀ᵐ (t : ℝ) ∂Measure.restrict volume J,
            @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
              (fun (x : Vec3) =>
                Du (x, t) i j *
                  (φ (x, t) * spatialPartial (fun (w : ParabolicPoint) => ψ w i) j (x, t)))
              (Measure.restrict volume Ω')
    := by
  intro q Du φ Ω' J ψ hAint i j
  have h := (hAint i j).mono_measure
    (Measure.restrict_le_self : volume.restrict (spaceTimeSet Ω' J) ≤ volume)
  change Integrable (fun q : Vec3 × ℝ =>
    Du ((q.1, q.2) : ParabolicPoint) i j *
      (φ q * spatialPartial (fun w => ψ w i) j q))
    (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict (Ω' ×ˢ J)) at h
  rw [← Measure.prod_restrict Ω' J] at h
  exact h.prod_left_ae

private lemma laplacian_transfer_hCslice_6 :
    ∀ {_ : ℝ} {u : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {Ω' : Set Vec3} {J : Set ℝ}
      {ψ : Vec3 × ℝ → Vec3},
      (∀ (i j : Fin (3 : ℕ)),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
            (fun (z : ParabolicPoint) =>
              u z i *
                (spatialPartial φ j z * spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z))
            volume) →
        ∀ (i j : Fin (3 : ℕ)),
          ∀ᵐ (t : ℝ) ∂Measure.restrict volume J,
            @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
              (fun (x : Vec3) =>
                u (x, t) i *
                  (spatialPartial φ j (x, t) *
                    spatialPartial (fun (w : ParabolicPoint) => ψ w i) j (x, t)))
              (Measure.restrict volume Ω')
    := by
  intro q u φ Ω' J ψ hCint i j
  have h := (hCint i j).mono_measure
    (Measure.restrict_le_self : volume.restrict (spaceTimeSet Ω' J) ≤ volume)
  change Integrable (fun q : Vec3 × ℝ =>
    u ((q.1, q.2) : ParabolicPoint) i *
      (spatialPartial φ j q * spatialPartial
      (fun w => ψ w i) j q))
    (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict (Ω' ×ˢ J)) at h
  rw [← Measure.prod_restrict Ω' J] at h
  exact h.prod_left_ae

private lemma laplacian_transfer_hgrad_all_7 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {Ω' : Set Vec3}
      {J : Set ℝ},
      (∀ (i : Fin (3 : ℕ)),
          ∀ᵐ (s : ℝ) ∂Measure.restrict volume J,
            HasWeakGradientOn Ω' (fun (x : Vec (3 : ℕ)) => u (x, s) i) fun (x : Vec (3 : ℕ)) =>
              Du (x, s) i) →
        ∀ᵐ (t : ℝ) ∂Measure.restrict volume J,
          ∀ (i j : Fin (3 : ℕ)),
            HasWeakPartialDerivOn Ω' j (fun (x : Vec (3 : ℕ)) => u (x, t) i)
              fun (x : Vec (3 : ℕ)) => Du (x, t) i j
    := by
  intro u Du Ω' J hgrad
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  filter_upwards [hgrad i] with t ht
  exact ht j

private lemma laplacian_transfer_hφspout_8 :
    ∀ {φ : Vec3 × ℝ → ℝ} {Ω' : Set Vec3} {J : Set ℝ},
      tsupport φ ⊆ Ω' ×ˢ J →
        ContDiff ℝ (⊤ : ℕ∞) φ →
          ∀ (j : Fin (3 : ℕ)), ∀ z ∉ spaceTimeSet Ω' J, spatialPartial φ j (z.1, z.2) = (0 : ℝ)
    := by
  intro φ Ω' J hφbox hφd j z hz
  apply spatialPartial_zero_of_not_mem_tsupport_public hφd
  intro hmem
  apply hz
  exact hφbox hmem

private lemma laplacian_transfer_hBsliceAll_9 :
    ∀ {u : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {Ω' : Set Vec3} {J : Set ℝ}
      {ψ : Vec3 × ℝ → Vec3},
      (∀ (i j : Fin (3 : ℕ)),
          ∀ᵐ (t : ℝ) ∂Measure.restrict volume J,
            @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
              (fun (x : Vec3) =>
                u (x, t) i *
                  (φ (x, t) * spatialSecondPartial (fun (w : ParabolicPoint) => ψ w i) j j (x, t)))
              (Measure.restrict volume Ω')) →
        ∀ᵐ (t : ℝ) ∂Measure.restrict volume J,
          ∀ (i j : Fin (3 : ℕ)),
            @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
              (fun (x : Vec3) =>
                u (x, t) i *
                  (φ (x, t) * spatialSecondPartial (fun (w : ParabolicPoint) => ψ w i) j j (x, t)))
              (Measure.restrict volume Ω')
    := by
  intro u φ Ω' J ψ hBslice
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  exact hBslice i j

private lemma laplacian_transfer_hAsliceAll_10 :
    ∀ {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {φ : Vec3 × ℝ → ℝ} {Ω' : Set Vec3} {J : Set ℝ}
      {ψ : Vec3 × ℝ → Vec3},
      (∀ (i j : Fin (3 : ℕ)),
          ∀ᵐ (t : ℝ) ∂Measure.restrict volume J,
            @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
              (fun (x : Vec3) =>
                Du (x, t) i j *
                  (φ (x, t) * spatialPartial (fun (w : ParabolicPoint) => ψ w i) j (x, t)))
              (Measure.restrict volume Ω')) →
        ∀ᵐ (t : ℝ) ∂Measure.restrict volume J,
          ∀ (i j : Fin (3 : ℕ)),
            @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
              (fun (x : Vec3) =>
                Du (x, t) i j *
                  (φ (x, t) * spatialPartial (fun (w : ParabolicPoint) => ψ w i) j (x, t)))
              (Measure.restrict volume Ω')
    := by
  intro Du φ Ω' J ψ hAslice
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  exact hAslice i j

theorem laplacian_transfer_of_sws {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ} {f :
      ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I) {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I
      Ω' J)
    (hφbox : tsupport φ ⊆ Ω' ×ˢ J) {ψ : Vec3 × ℝ → Vec3}
    (hψ : ψ ∈ spaceTimeTestFunction (V := Vec3) Set.univ Set.univ) :
    (∫ z, ∑ i, φ z * u z i * ∑ j, spatialSecondPartial (fun w => ψ w i) j j z) =
      -∫ z, ∑ i, ∑ j,
        (φ z * Du z i j + u z i * spatialPartial φ j z) *
          spatialPartial (fun w => ψ w i) j z := by
  rcases hsol with ⟨hΩ, hI, hIord, hq, hf, hdata, hS2, hS3, hS4⟩
  rcases hφ with ⟨hφd, hφc, hφΩ⟩
  rcases hψ with ⟨hψd, hψc, hψΩ⟩
  let μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet Ω' J)
  have : IsFiniteMeasure μ := local_box_isFiniteMeasure hbox.2.1 hbox.2.2.2.2.1
  obtain ⟨hu, hDu, hpmeas, hfmeas, hEssSup, henergy, hp, hf, hgrad⟩ :=
    hdata Ω' J hbox
  have hLp := local_memLp_two_of_energy (hu := hu) (hDu := hDu) henergy
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [ENNReal.one_le_ofReal]
    linarith only [hq]
  have huComp (i : Fin 3) : MemLp (fun z => u z i) 2 μ :=
    hLp.1.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
  have hDuComp (i j : Fin 3) : MemLp (fun z => Du z i j) 2 μ :=
    (hLp.2.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : (Fin 3 → Vec3) →L[ℝ] Vec3)).continuousLinearMap_comp
      (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ)
  have hpInt : Integrable p μ := hp.integrable (by norm_num)
  have hfInt : Integrable f μ := hf.integrable hq1
  have hφtime : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => timePartial φ z) := timePartial_contDiff_full hφd
  have hφsp (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialPartial φ j z) :=
    spatialPartial_contDiff hφd j
  have hφsecond (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialSecondPartial (fun w => ψ w i) j j z) :=
    spatialSecondPartial_contDiff_full
      ((contDiff_apply ℝ ℝ i).comp hψd) j j
  have hψi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun z => ψ z i) :=
    (contDiff_apply ℝ ℝ i).comp hψd
  have hφtime_c := @laplacian_transfer_hφtime_c_1 φ hφd hφc
  have hφsp_c (j : Fin 3) := @laplacian_transfer_hφsp_c_2 φ hφd hφc j
  have hφsp_ts (j : Fin 3) := @laplacian_transfer_hφsp_ts_3 φ hφd j
  have hboxset : (spaceTimeSet Ω' J : Set (Vec3 × ℝ)) = Ω' ×ˢ J := rfl
  have hBint (i j : Fin 3) := @laplacian_transfer_hBint_1 u f φ Ω' J hφbox ψ hφd hφc (by
    infer_instance) huComp hφsecond i j
  have hAint (i j : Fin 3) := @laplacian_transfer_hAint_2 Du f φ Ω' J hφbox ψ hφd hφc (by
    infer_instance) hDuComp hψi i j
  have hCint (i j : Fin 3) := @laplacian_transfer_hCint_3 u f φ Ω' J hφbox ψ (by infer_instance)
    huComp hφsp hψi hφsp_c hφsp_ts i j
  have hBslice (i j : Fin 3) := @laplacian_transfer_hBslice_4 q u φ Ω' J ψ hBint i j
  have hAslice (i j : Fin 3) := @laplacian_transfer_hAslice_5 q Du φ Ω' J ψ hAint i j
  have hCslice (i j : Fin 3) := @laplacian_transfer_hCslice_6 q u φ Ω' J ψ hCint i j
  have hgrad_all := @laplacian_transfer_hgrad_all_7 u Du Ω' J hgrad
  have hslice (i j : Fin 3) := @laplacian_transfer_hslice_4 Ω I u Du f φ Ω' J hbox hφbox ψ hφd hψi
    hBslice hAslice hCslice hgrad_all i j
  let B : ParabolicPoint → ℝ := fun z =>
    ∑ i, ∑ j, u z i * (φ z * spatialSecondPartial
      (fun w => ψ w i) j j z)
  let A : ParabolicPoint → ℝ := fun z =>
    ∑ i, ∑ j, Du z i j * (φ z * spatialPartial
      (fun w => ψ w i) j z)
  let C : ParabolicPoint → ℝ := fun z =>
    ∑ i, ∑ j, u z i * (spatialPartial φ j z * spatialPartial
      (fun w => ψ w i) j z)
  have hB : Integrable B volume := by
    dsimp [B]
    exact integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ =>
      integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ =>
        hBint i j))
  have hA : Integrable A volume := by
    dsimp [A]
    exact integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ =>
      integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ =>
        hAint i j))
  have hC : Integrable C volume := by
    dsimp [C]
    exact integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ =>
      integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ =>
        hCint i j))
  have hφout : ∀ z ∉ spaceTimeSet Ω' J, φ (z.1, z.2) = 0 :=
    zero_outside_box_of_tsupport_subset hφbox
  have hφspout (j : Fin 3) := @laplacian_transfer_hφspout_8 φ Ω' J hφbox hφd j
  have hBzero := @laplacian_transfer_hBzero_5 u φ Ω' J ψ hφout
  have hAzero := @laplacian_transfer_hAzero_6 Du φ Ω' J ψ hφout
  have hCzero := @laplacian_transfer_hCzero_7 u φ Ω' J ψ hφspout
  have hBsliceAll := @laplacian_transfer_hBsliceAll_9 u φ Ω' J ψ hBslice
  have hAsliceAll := @laplacian_transfer_hAsliceAll_10 Du φ Ω' J ψ hAslice
  have hCsliceAll : ∀ᵐ t ∂volume.restrict J,
      ∀ i j : Fin 3,
        Integrable (fun x : Vec3 => u (x, t) i *
          (spatialPartial φ j (x, t) * spatialPartial
            (fun w => ψ w i) j (x, t))) (volume.restrict Ω') := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    exact hCslice i j
  have hsliceAll : ∀ᵐ t ∂volume.restrict J,
      ∀ i j : Fin 3,
        (∫ x in Ω', u (x, t) i * φ (x, t) *
          spatialSecondPartial (fun w => ψ w i) j j (x, t)) =
          (-(∫ x in Ω', Du (x, t) i j * φ (x, t) *
            spatialPartial (fun w => ψ w i) j (x, t))) -
            (∫ x in Ω', u (x, t) i * spatialPartial φ j (x, t) *
              spatialPartial (fun w => ψ w i) j (x, t)) := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    exact hslice i j
  have hsliceSum := @laplacian_transfer_hsliceSum_8 u Du φ Ω' J ψ hBsliceAll hAsliceAll hCsliceAll
    hsliceAll
  have htransfer := global_integral_transfer (Ω' := Ω') (J := J)
    (B := B) (A := A) (C := C) hB hA hC hBzero hAzero hCzero hsliceSum
  have hAC := @laplacian_transfer_hAC_9 u Du φ ψ hA hC
  calc
    (∫ z, ∑ i, φ z * u z i *
      ∑ j, spatialSecondPartial (fun w => ψ w i) j j z) = ∫ z, B z := by
        apply integral_congr_ae
        filter_upwards [] with z
        dsimp [B]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = (-(∫ z, A z)) - (∫ z, C z) := htransfer
    _ = -(∫ z, ∑ i, ∑ j, (Du z i j * (φ z * spatialPartial
        (fun w => ψ w i) j z) + u z i * (spatialPartial φ j z *
          spatialPartial (fun w => ψ w i) j z))) := by
      rw [hAC]
      ring
    _ = -∫ z, ∑ i, ∑ j,
        (φ z * Du z i j + u z i * spatialPartial φ j z) *
          spatialPartial (fun w => ψ w i) j z := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with z
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
end CKN.Core.Step3
