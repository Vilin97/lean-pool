/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsP7SolutionMeas
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsUnconditionalCore

/-!
# Pressure Decay Measurability

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN.Core.Step3

open CKN

/-! The pressure decomposition is evaluated on a bounded product cylinder.
The solution fields have measurable representatives there; the representatives
are used only to discharge the certificates needed by the `eLpNorm'` triangle
inequality. -/

private lemma pressure_tensor_measurable {u : ParabolicPoint → Vec3} {c : ℝ → Vec3}
    (hu : Measurable u) (hc : Measurable c) (i j : Fin 3) :
    Measurable (fun z => pressureUTensor u c z i j) := by
  exact ((measurable_pi_apply i).comp hu).neg.mul
    (((measurable_pi_apply j).comp hu).sub
      (((measurable_pi_apply j).comp hc).comp measurable_snd))

private lemma pressure_kernel_measurable :
    Measurable (newtonianKernel : Vec3 → ℝ) := by
  have hnorm : Measurable (fun z : Vec3 => vec3EuclideanNorm z) := by
    unfold vec3EuclideanNorm
    fun_prop
  unfold newtonianKernel
  exact measurable_const.div (measurable_const.mul hnorm)

private lemma pressure_kernel_derivative_measurable (j : Fin 3) :
    Measurable (fun z : Vec3 => spatialDeriv newtonianKernel j z) := by
  unfold spatialDeriv
  exact measurable_fderiv_apply_const ℝ newtonianKernel (basisVec j)

private lemma pressure_source_measurable_on_cylinder_hcmeas_1 :
    ∀ {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ},
      let B : Set Vec3 := vec3Ball z.1 ρ;
      let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2;
      let c : ℝ → Vec3 := fun s j => ⨍ (y : Vec3) in B, u (y, s) j;
      ∀ (Ω' : Set Vec3) (J : Set ℝ),
        vec3Ball z.1 ρ ⊆ Ω' →
          Ioc (z.2 - ρ ^ 2) z.2 ⊆ J →
            AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) u
                (Measure.restrict volume (spaceTimeSet Ω' J)) →
              ∀ (j : Fin 3),
                AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace) (fun s => c s j)
                  (Measure.restrict volume T)
    := by
  intro u z ρ B T c Ω' J hball htime hu j
  dsimp [c, B, T]
  have hI : AEMeasurable (fun s : ℝ =>
      ∫ y in vec3Ball z.1 ρ, u (y, s) j)
      (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) := by
    apply pressure_slice_integral_aemeasurable (g := fun w => u w j)
      (vec3Ball_measurable z.1 ρ) measurableSet_Ioc hball
    have hST' : spaceTimeSet Ω' (Ioc (z.2 - ρ ^ 2) z.2) ⊆
        spaceTimeSet Ω' J := by
      intro w hw
      exact ⟨hw.1, htime hw.2⟩
    exact (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).continuous
      |>.comp_aestronglyMeasurable hu
      |>.mono_measure (Measure.restrict_mono_set volume hST')
  simpa only [MeasureTheory.average_eq, smul_eq_mul] using
    hI.const_mul ((volume.restrict (vec3Ball z.1 ρ)).real Set.univ)⁻¹

private lemma pressure_source_measurable_on_cylinder_hsrc2_2 :
    ∀ {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ},
      let B : Set Vec3 := vec3Ball z.1 ρ;
      let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2;
      ∀ (η : Vec3 → ℝ) (c cm : ℝ → Vec3),
        c =ᵐ[Measure.restrict volume T] cm →
          ∀ (um : ParabolicPoint → Vec3),
            (∀ᵐ (s : ℝ) ∂Measure.restrict volume T,
                ∀ᵐ (y : Vec3) ∂Measure.restrict volume B, u (y, s) = um (y, s)) →
              (∀ (i j : Fin 3), tsupport (mixedSecond η i j) ⊆ B) →
                ∀ (i j : Fin 3),
                  ∀ᵐ (s : ℝ) ∂Measure.restrict volume T,
                    (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) =ᵐ[volume]
                      fun y => mixedSecond η i j y * pressureUTensor um cm (y, s) i j
    := by
  intro u z ρ B T η c cm hcmEq um huSlices hηddsupp i j
  filter_upwards [huSlices, hcmEq] with s hus hcs
  apply ae_of_ae_restrict_of_ae_restrict_compl B
  · filter_upwards [hus] with y hy
    have hy' : u (⟨y, s⟩ : ParabolicPoint) = um (⟨y, s⟩ : ParabolicPoint) := by
      simpa using hy
    have hcs' : c s = cm s := hcs
    change mixedSecond η i j y * pressureUTensor u c
        (⟨y, s⟩ : ParabolicPoint) i j =
      mixedSecond η i j y * pressureUTensor um cm
        (⟨y, s⟩ : ParabolicPoint) i j
    simp only [pressureUTensor, hy', hcs']
  · filter_upwards [ae_restrict_mem
      (show MeasurableSet Bᶜ from (vec3Ball_measurable z.1 ρ).compl)] with y hy
    have hy' : y ∉ tsupport (mixedSecond η i j) := by
      intro hyt
      exact hy (hηddsupp i j hyt)
    rw [image_eq_zero_of_notMem_tsupport hy']
    simp

private lemma pressure_source_measurable_on_cylinder_hsrc3_3 :
    ∀ {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ},
      let B : Set Vec3 := vec3Ball z.1 ρ;
      let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2;
      ∀ (η : Vec3 → ℝ) (c cm : ℝ → Vec3),
        c =ᵐ[Measure.restrict volume T] cm →
          ∀ (um : ParabolicPoint → Vec3),
            (∀ᵐ (s : ℝ) ∂Measure.restrict volume T,
                ∀ᵐ (y : Vec3) ∂Measure.restrict volume B, u (y, s) = um (y, s)) →
              (∀ (j : Fin 3), tsupport (spatialDeriv η j) ⊆ B) →
                ∀ (i j : Fin 3),
                  ∀ᵐ (s : ℝ) ∂Measure.restrict volume T,
                    (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) =ᵐ[volume]
                      fun y => pressureUTensor um cm (y, s) i j * spatialDeriv η i y
    := by
  intro u z ρ B T η c cm hcmEq um huSlices hηdsupp i j
  filter_upwards [huSlices, hcmEq] with s hus hcs
  apply ae_of_ae_restrict_of_ae_restrict_compl B
  · filter_upwards [hus] with y hy
    have hy' : u (⟨y, s⟩ : ParabolicPoint) = um (⟨y, s⟩ : ParabolicPoint) := by
      simpa using hy
    have hcs' : c s = cm s := hcs
    change pressureUTensor u c (⟨y, s⟩ : ParabolicPoint) i j * spatialDeriv η i y =
      pressureUTensor um cm (⟨y, s⟩ : ParabolicPoint) i j * spatialDeriv η i y
    simp only [pressureUTensor, hy', hcs']
  · filter_upwards [ae_restrict_mem
      (show MeasurableSet Bᶜ from (vec3Ball_measurable z.1 ρ).compl)] with y hy
    have hy' : y ∉ tsupport (spatialDeriv η i) := by
      intro hyt
      exact hy (hηdsupp i hyt)
    rw [image_eq_zero_of_notMem_tsupport hy']
    simp

private lemma pressure_source_measurable_on_cylinder_hsrc4_4 :
    ∀ {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ},
      let B : Set Vec3 := vec3Ball z.1 ρ;
      let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2;
      ∀ (η : Vec3 → ℝ) (c cm : ℝ → Vec3),
        c =ᵐ[Measure.restrict volume T] cm →
          ∀ (um : ParabolicPoint → Vec3),
            (∀ᵐ (s : ℝ) ∂Measure.restrict volume T,
                ∀ᵐ (y : Vec3) ∂Measure.restrict volume B, u (y, s) = um (y, s)) →
              (∀ (j : Fin 3), tsupport (spatialDeriv η j) ⊆ B) →
                ∀ (i j : Fin 3),
                  ∀ᵐ (s : ℝ) ∂Measure.restrict volume T,
                    (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) =ᵐ[volume]
                      fun y => pressureUTensor um cm (y, s) i j * spatialDeriv η j y
    := by
  intro u z ρ B T η c cm hcmEq um huSlices hηdsupp i j
  filter_upwards [huSlices, hcmEq] with s hus hcs
  apply ae_of_ae_restrict_of_ae_restrict_compl B
  · filter_upwards [hus] with y hy
    have hy' : u (⟨y, s⟩ : ParabolicPoint) = um (⟨y, s⟩ : ParabolicPoint) := by
      simpa using hy
    have hcs' : c s = cm s := hcs
    change pressureUTensor u c (⟨y, s⟩ : ParabolicPoint) i j * spatialDeriv η j y =
      pressureUTensor um cm (⟨y, s⟩ : ParabolicPoint) i j * spatialDeriv η j y
    simp only [pressureUTensor, hy', hcs']
  · filter_upwards [ae_restrict_mem
      (show MeasurableSet Bᶜ from (vec3Ball_measurable z.1 ρ).compl)] with y hy
    have hy' : y ∉ tsupport (spatialDeriv η j) := by
      intro hyt
      exact hy (hηdsupp j hyt)
    rw [image_eq_zero_of_notMem_tsupport hy']
    simp

private lemma pressure_source_measurable_on_cylinder_hsrc5_5 :
    ∀ {p : ParabolicPoint → ℝ} {z : ParabolicPoint} {ρ : ℝ},
      let B : Set Vec3 := vec3Ball z.1 ρ;
      let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2;
      ∀ (η : Vec3 → ℝ) (pm : ParabolicPoint → ℝ),
        (∀ᵐ (s : ℝ) ∂Measure.restrict volume T,
            ∀ᵐ (y : Vec3) ∂Measure.restrict volume B, p (y, s) = pm (y, s)) →
          tsupport (spatialLaplacian η) ⊆ B →
            ∀ᵐ (s : ℝ) ∂Measure.restrict volume T,
              (fun y => p (y, s) * spatialLaplacian η y) =ᵐ[volume] fun y =>
                pm (y, s) * spatialLaplacian η y
    := by
  intro p z ρ B T η pm hpSlices hηlapsupp
  filter_upwards [hpSlices] with s hps
  apply ae_of_ae_restrict_of_ae_restrict_compl B
  · filter_upwards [hps] with y hy
    rw [hy]
  · filter_upwards [ae_restrict_mem
      (show MeasurableSet Bᶜ from (vec3Ball_measurable z.1 ρ).compl)] with y hy
    have hy' : y ∉ tsupport (spatialLaplacian η) := by
      intro hyt
      exact hy (hηlapsupp hyt)
    rw [image_eq_zero_of_notMem_tsupport hy']
    simp

private lemma pressure_source_measurable_on_cylinder_hsrc6_6 :
    ∀ {p : ParabolicPoint → ℝ} {z : ParabolicPoint} {ρ : ℝ},
      let B : Set Vec3 := vec3Ball z.1 ρ;
      let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2;
      ∀ (η : Vec3 → ℝ) (pm : ParabolicPoint → ℝ),
        (∀ᵐ (s : ℝ) ∂Measure.restrict volume T,
            ∀ᵐ (y : Vec3) ∂Measure.restrict volume B, p (y, s) = pm (y, s)) →
          (∀ (j : Fin 3), tsupport (spatialDeriv η j) ⊆ B) →
            ∀ (j : Fin 3),
              ∀ᵐ (s : ℝ) ∂Measure.restrict volume T,
                (fun y => spatialDeriv η j y * p (y, s)) =ᵐ[volume] fun y =>
                  spatialDeriv η j y * pm (y, s)
    := by
  intro p z ρ B T η pm hpSlices hηdsupp j
  filter_upwards [hpSlices] with s hps
  apply ae_of_ae_restrict_of_ae_restrict_compl B
  · filter_upwards [hps] with y hy
    rw [hy]
  · filter_upwards [ae_restrict_mem
      (show MeasurableSet Bᶜ from (vec3Ball_measurable z.1 ρ).compl)] with y hy
    have hy' : y ∉ tsupport (spatialDeriv η j) := by
      intro hyt
      exact hy (hηdsupp j hyt)
    rw [image_eq_zero_of_notMem_tsupport hy']
    simp

private lemma pressure_source_measurable_on_cylinder_hsrc7_7 :
    ∀ {f : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ},
      let B : Set Vec3 := vec3Ball z.1 ρ;
      let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2;
      ∀ (η : Vec3 → ℝ) (fm : ParabolicPoint → Vec3),
        (∀ᵐ (s : ℝ) ∂Measure.restrict volume T,
            ∀ᵐ (y : Vec3) ∂Measure.restrict volume B, f (y, s) = fm (y, s)) →
          tsupport η ⊆ B →
            ∀ (j : Fin 3),
              ∀ᵐ (s : ℝ) ∂Measure.restrict volume T,
                (fun y => η y * f (y, s) j) =ᵐ[volume] fun y => η y * fm (y, s) j
    := by
  intro f z ρ B T η fm hfSlices hηsupp j
  filter_upwards [hfSlices] with s hfs
  apply ae_of_ae_restrict_of_ae_restrict_compl B
  · filter_upwards [hfs] with y hy
    rw [hy]
  · filter_upwards [ae_restrict_mem
      (show MeasurableSet Bᶜ from (vec3Ball_measurable z.1 ρ).compl)] with y hy
    have hy' : y ∉ tsupport η := by
      intro hyt
      exact hy (hηsupp hyt)
    rw [image_eq_zero_of_notMem_tsupport hy']
    simp

private lemma pressure_source_measurable_on_cylinder_hsrc8_8 :
    ∀ {f : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ},
      let B : Set Vec3 := vec3Ball z.1 ρ;
      let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2;
      ∀ (η : Vec3 → ℝ) (fm : ParabolicPoint → Vec3),
        (∀ᵐ (s : ℝ) ∂Measure.restrict volume T,
            ∀ᵐ (y : Vec3) ∂Measure.restrict volume B, f (y, s) = fm (y, s)) →
          (∀ (j : Fin 3), tsupport (spatialDeriv η j) ⊆ B) →
            ∀ (j : Fin 3),
              ∀ᵐ (s : ℝ) ∂Measure.restrict volume T,
                (fun y => spatialDeriv η j y * f (y, s) j) =ᵐ[volume] fun y =>
                  spatialDeriv η j y * fm (y, s) j
    := by
  intro f z ρ B T η fm hfSlices hηdsupp j
  filter_upwards [hfSlices] with s hfs
  apply ae_of_ae_restrict_of_ae_restrict_compl B
  · filter_upwards [hfs] with y hy
    rw [hy]
  · filter_upwards [ae_restrict_mem
      (show MeasurableSet Bᶜ from (vec3Ball_measurable z.1 ρ).compl)] with y hy
    have hy' : y ∉ tsupport (spatialDeriv η j) := by
      intro hyt
      exact hy (hηdsupp j hyt)
    rw [image_eq_zero_of_notMem_tsupport hy']
    simp

private lemma pressure_source_measurable_on_cylinder_hpot2_9 :
    ∀ {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ},
      let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2;
      ∀ (η : Vec3 → ℝ) (c cm : ℝ → Vec3) (um : ParabolicPoint → Vec3),
        (∀ (i j : Fin 3),
            ∀ᵐ (s : ℝ) ∂Measure.restrict volume T,
              (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) =ᵐ[volume] fun y =>
                mixedSecond η i j y * pressureUTensor um cm (y, s) i j) →
          let R2 : ParabolicPoint → ℝ := fun w =>
            ∑ i : Fin 3,
              ∑ j : Fin 3,
                @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                  -newtonianKernel (w.1 - y) *
                    (mixedSecond η i j y * pressureUTensor um cm (y, w.2) i j);
          ∀ᵐ (s : ℝ) ∂Measure.restrict volume T, ∀ (x : Vec3), pressureP2 η u c s x = R2 (x, s)
    := by
  intro u z ρ T η c cm um hsrc2 R2
  have hall : ∀ᵐ s ∂volume.restrict T, ∀ i j : Fin 3, ∀ᵐ y ∂volume,
      mixedSecond η i j y * pressureUTensor u c (y, s) i j =
        mixedSecond η i j y * pressureUTensor um cm (y, s) i j := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    exact hsrc2 i j
  filter_upwards [hall] with s hs x
  unfold pressureP2 R2
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply integral_congr_ae
  filter_upwards [hs i j] with y hy
  rw [hy]

private lemma pressure_source_measurable_on_cylinder_hpot3_10 :
    ∀ {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ},
      let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2;
      ∀ (η : Vec3 → ℝ) (c cm : ℝ → Vec3) (um : ParabolicPoint → Vec3),
        (∀ (i j : Fin 3),
            ∀ᵐ (s : ℝ) ∂Measure.restrict volume T,
              (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) =ᵐ[volume] fun y =>
                pressureUTensor um cm (y, s) i j * spatialDeriv η i y) →
          let R3 : ParabolicPoint → ℝ := fun w =>
            ∑ i : Fin 3,
              ∑ j : Fin 3,
                @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                  spatialDeriv newtonianKernel j (w.1 - y) *
                    (pressureUTensor um cm (y, w.2) i j * spatialDeriv η i y);
          ∀ᵐ (s : ℝ) ∂Measure.restrict volume T, ∀ (x : Vec3), pressureP3 η u c s x = R3 (x, s)
    := by
  intro u z ρ T η c cm um hsrc3 R3
  have hall : ∀ᵐ s ∂volume.restrict T, ∀ i j : Fin 3, ∀ᵐ y ∂volume,
      pressureUTensor u c (y, s) i j * spatialDeriv η i y =
        pressureUTensor um cm (y, s) i j * spatialDeriv η i y := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    exact hsrc3 i j
  filter_upwards [hall] with s hs x
  unfold pressureP3 R3
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply integral_congr_ae
  filter_upwards [hs i j] with y hy
  rw [hy]

private lemma pressure_source_measurable_on_cylinder_hpot4_11 :
    ∀ {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ},
      let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2;
      ∀ (η : Vec3 → ℝ) (c cm : ℝ → Vec3) (um : ParabolicPoint → Vec3),
        (∀ (i j : Fin 3),
            ∀ᵐ (s : ℝ) ∂Measure.restrict volume T,
              (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) =ᵐ[volume] fun y =>
                pressureUTensor um cm (y, s) i j * spatialDeriv η j y) →
          let R4 : ParabolicPoint → ℝ := fun w =>
            ∑ i : Fin 3,
              ∑ j : Fin 3,
                @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                  spatialDeriv newtonianKernel i (w.1 - y) *
                    (pressureUTensor um cm (y, w.2) i j * spatialDeriv η j y);
          ∀ᵐ (s : ℝ) ∂Measure.restrict volume T, ∀ (x : Vec3), pressureP4 η u c s x = R4 (x, s)
    := by
  intro u z ρ T η c cm um hsrc4 R4
  have hall : ∀ᵐ s ∂volume.restrict T, ∀ i j : Fin 3, ∀ᵐ y ∂volume,
      pressureUTensor u c (y, s) i j * spatialDeriv η j y =
        pressureUTensor um cm (y, s) i j * spatialDeriv η j y := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    exact hsrc4 i j
  filter_upwards [hall] with s hs x
  unfold pressureP4 R4
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply integral_congr_ae
  filter_upwards [hs i j] with y hy
  rw [hy]

private lemma pressure_source_measurable_on_cylinder_hpot6_12 :
    ∀ {p : ParabolicPoint → ℝ} {z : ParabolicPoint} {ρ : ℝ},
      let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2;
      ∀ (η : Vec3 → ℝ) (pm : ParabolicPoint → ℝ),
        (∀ (j : Fin 3),
            ∀ᵐ (s : ℝ) ∂Measure.restrict volume T,
              (fun y => spatialDeriv η j y * p (y, s)) =ᵐ[volume] fun y =>
                spatialDeriv η j y * pm (y, s)) →
          let R6 : ParabolicPoint → ℝ := fun w =>
            -2 *
              ∑ j : Fin 3,
                @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                  spatialDeriv newtonianKernel j (w.1 - y) * (spatialDeriv η j y * pm (y, w.2));
          ∀ᵐ (s : ℝ) ∂Measure.restrict volume T, ∀ (x : Vec3), pressureP6 η p s x = R6 (x, s)
    := by
  intro p z ρ T η pm hsrc6 R6
  have hall : ∀ᵐ s ∂volume.restrict T, ∀ j : Fin 3, ∀ᵐ y ∂volume,
      spatialDeriv η j y * p (y, s) =
        spatialDeriv η j y * pm (y, s) := by
    rw [ae_all_iff]
    intro j
    exact hsrc6 j
  filter_upwards [hall] with s hs x
  unfold pressureP6 R6
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  apply integral_congr_ae
  filter_upwards [hs j] with y hy
  rw [hy]

private lemma pressure_source_measurable_on_cylinder_hpot7_13 :
    ∀ {f : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ},
      let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2;
      ∀ (η : Vec3 → ℝ) (fm : ParabolicPoint → Vec3),
        (∀ (j : Fin 3),
            ∀ᵐ (s : ℝ) ∂Measure.restrict volume T,
              (fun y => η y * f (y, s) j) =ᵐ[volume] fun y => η y * fm (y, s) j) →
          let R7 : ParabolicPoint → ℝ := fun w =>
            -∑ j : Fin 3,
                @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                  spatialDeriv newtonianKernel j (w.1 - y) * (η y * fm (y, w.2) j);
          ∀ᵐ (s : ℝ) ∂Measure.restrict volume T, ∀ (x : Vec3), pressureP7 η f s x = R7 (x, s)
    := by
  intro f z ρ T η fm hsrc7 R7
  have hall : ∀ᵐ s ∂volume.restrict T, ∀ j : Fin 3, ∀ᵐ y ∂volume,
      η y * f (y, s) j = η y * fm (y, s) j := by
    rw [ae_all_iff]
    intro j
    exact hsrc7 j
  filter_upwards [hall] with s hs x
  unfold pressureP7 R7
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  apply integral_congr_ae
  filter_upwards [hs j] with y hy
  rw [hy]

private lemma pressure_source_measurable_on_cylinder_hpot8_14 :
    ∀ {f : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ},
      let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2;
      ∀ (η : Vec3 → ℝ) (fm : ParabolicPoint → Vec3),
        (∀ (j : Fin 3),
            ∀ᵐ (s : ℝ) ∂Measure.restrict volume T,
              (fun y => spatialDeriv η j y * f (y, s) j) =ᵐ[volume] fun y =>
                spatialDeriv η j y * fm (y, s) j) →
          let R8 : ParabolicPoint → ℝ := fun w =>
            -∑ j : Fin 3,
                @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                  -newtonianKernel (w.1 - y) * (spatialDeriv η j y * fm (y, w.2) j);
          ∀ᵐ (s : ℝ) ∂Measure.restrict volume T, ∀ (x : Vec3), pressureP8 η f s x = R8 (x, s)
    := by
  intro f z ρ T η fm hsrc8 R8
  have hall : ∀ᵐ s ∂volume.restrict T, ∀ j : Fin 3, ∀ᵐ y ∂volume,
      spatialDeriv η j y * f (y, s) j =
        spatialDeriv η j y * fm (y, s) j := by
    rw [ae_all_iff]
    intro j
    exact hsrc8 j
  filter_upwards [hall] with s hs x
  unfold pressureP8 R8
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  apply integral_congr_ae
  filter_upwards [hs j] with y hy
  rw [hy]

private lemma pressure_source_measurable_on_cylinder_hQ2_15 :
    ∀ {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ},
      let _ : Set Vec3 := vec3Ball z.1 ρ;
      let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2;
      ∀ (η : Vec3 → ℝ) (c : ℝ → Vec3) (R2 : ParabolicPoint → ℝ),
        (∀ᵐ (s : ℝ) ∂Measure.restrict volume T, ∀ (x : Vec3), pressureP2 η u c s x = R2 (x, s)) →
          (fun w =>
              pressureP2 η u c w.2 w.1) =ᵐ[Measure.restrict volume (parabolicCylinder z.1 z.2 ρ)]
            R2
    := by
  intro u z ρ B T η c R2 hpot2
  change (fun w : ParabolicPoint => pressureP2 η u c w.2 w.1) =ᵐ[
    volume.restrict (B ×ˢ T)] R2
  have hmeasureBT : volume.restrict (B ×ˢ T) =
      (volume.restrict B).prod (volume.restrict T) := by
    rw [Measure.prod_restrict B T,
      MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
  rw [hmeasureBT]
  have hprod := (Measure.quasiMeasurePreserving_snd
    (μ := volume.restrict B) (ν := volume.restrict T)).ae hpot2
  filter_upwards [hprod] with w hw
  exact hw w.1

private lemma pressure_source_measurable_on_cylinder_hQ3_16 :
    ∀ {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ},
      let _ : Set Vec3 := vec3Ball z.1 ρ;
      let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2;
      ∀ (η : Vec3 → ℝ) (c : ℝ → Vec3) (R3 : ParabolicPoint → ℝ),
        (∀ᵐ (s : ℝ) ∂Measure.restrict volume T, ∀ (x : Vec3), pressureP3 η u c s x = R3 (x, s)) →
          (fun w =>
              pressureP3 η u c w.2 w.1) =ᵐ[Measure.restrict volume (parabolicCylinder z.1 z.2 ρ)]
            R3
    := by
  intro u z ρ B T η c R3 hpot3
  change (fun w : ParabolicPoint => pressureP3 η u c w.2 w.1) =ᵐ[
    volume.restrict (B ×ˢ T)] R3
  have hmeasureBT : volume.restrict (B ×ˢ T) =
      (volume.restrict B).prod (volume.restrict T) := by
    rw [Measure.prod_restrict B T,
      MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
  rw [hmeasureBT]
  have hprod := (Measure.quasiMeasurePreserving_snd
    (μ := volume.restrict B) (ν := volume.restrict T)).ae hpot3
  filter_upwards [hprod] with w hw
  exact hw w.1

private lemma pressure_source_measurable_on_cylinder_hQ4_17 :
    ∀ {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ},
      let _ : Set Vec3 := vec3Ball z.1 ρ;
      let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2;
      ∀ (η : Vec3 → ℝ) (c : ℝ → Vec3) (R4 : ParabolicPoint → ℝ),
        (∀ᵐ (s : ℝ) ∂Measure.restrict volume T, ∀ (x : Vec3), pressureP4 η u c s x = R4 (x, s)) →
          (fun w =>
              pressureP4 η u c w.2 w.1) =ᵐ[Measure.restrict volume (parabolicCylinder z.1 z.2 ρ)]
            R4
    := by
  intro u z ρ B T η c R4 hpot4
  change (fun w : ParabolicPoint => pressureP4 η u c w.2 w.1) =ᵐ[
    volume.restrict (B ×ˢ T)] R4
  have hmeasureBT : volume.restrict (B ×ˢ T) =
      (volume.restrict B).prod (volume.restrict T) := by
    rw [Measure.prod_restrict B T,
      MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
  rw [hmeasureBT]
  have hprod := (Measure.quasiMeasurePreserving_snd
    (μ := volume.restrict B) (ν := volume.restrict T)).ae hpot4
  filter_upwards [hprod] with w hw
  exact hw w.1

private lemma pressure_source_measurable_on_cylinder_hQ5_18 :
    ∀ {p : ParabolicPoint → ℝ} {z : ParabolicPoint} {ρ : ℝ},
      let _ : Set Vec3 := vec3Ball z.1 ρ;
      let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2;
      ∀ (η : Vec3 → ℝ) (R5 : ParabolicPoint → ℝ),
        (∀ᵐ (s : ℝ) ∂Measure.restrict volume T, ∀ (x : Vec3), pressureP5 η p s x = R5 (x, s)) →
          (fun w =>
              pressureP5 η p w.2 w.1) =ᵐ[Measure.restrict volume (parabolicCylinder z.1 z.2 ρ)]
            R5
    := by
  intro p z ρ B T η R5 hpot5
  change (fun w : ParabolicPoint => pressureP5 η p w.2 w.1) =ᵐ[
    volume.restrict (B ×ˢ T)] R5
  have hmeasureBT : volume.restrict (B ×ˢ T) =
      (volume.restrict B).prod (volume.restrict T) := by
    rw [Measure.prod_restrict B T,
      MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
  rw [hmeasureBT]
  have hprod := (Measure.quasiMeasurePreserving_snd
    (μ := volume.restrict B) (ν := volume.restrict T)).ae hpot5
  filter_upwards [hprod] with w hw
  exact hw w.1

private lemma pressure_source_measurable_on_cylinder_hQ6_19 :
    ∀ {p : ParabolicPoint → ℝ} {z : ParabolicPoint} {ρ : ℝ},
      let _ : Set Vec3 := vec3Ball z.1 ρ;
      let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2;
      ∀ (η : Vec3 → ℝ) (R6 : ParabolicPoint → ℝ),
        (∀ᵐ (s : ℝ) ∂Measure.restrict volume T, ∀ (x : Vec3), pressureP6 η p s x = R6 (x, s)) →
          (fun w =>
              pressureP6 η p w.2 w.1) =ᵐ[Measure.restrict volume (parabolicCylinder z.1 z.2 ρ)]
            R6
    := by
  intro p z ρ B T η R6 hpot6
  change (fun w : ParabolicPoint => pressureP6 η p w.2 w.1) =ᵐ[
    volume.restrict (B ×ˢ T)] R6
  have hmeasureBT : volume.restrict (B ×ˢ T) =
      (volume.restrict B).prod (volume.restrict T) := by
    rw [Measure.prod_restrict B T,
      MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
  rw [hmeasureBT]
  have hprod := (Measure.quasiMeasurePreserving_snd
    (μ := volume.restrict B) (ν := volume.restrict T)).ae hpot6
  filter_upwards [hprod] with w hw
  exact hw w.1

private lemma pressure_source_measurable_on_cylinder_hQ7_20 :
    ∀ {f : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ},
      let _ : Set Vec3 := vec3Ball z.1 ρ;
      let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2;
      ∀ (η : Vec3 → ℝ) (R7 : ParabolicPoint → ℝ),
        (∀ᵐ (s : ℝ) ∂Measure.restrict volume T, ∀ (x : Vec3), pressureP7 η f s x = R7 (x, s)) →
          (fun w =>
              pressureP7 η f w.2 w.1) =ᵐ[Measure.restrict volume (parabolicCylinder z.1 z.2 ρ)]
            R7
    := by
  intro f z ρ B T η R7 hpot7
  change (fun w : ParabolicPoint => pressureP7 η f w.2 w.1) =ᵐ[
    volume.restrict (B ×ˢ T)] R7
  have hmeasureBT : volume.restrict (B ×ˢ T) =
      (volume.restrict B).prod (volume.restrict T) := by
    rw [Measure.prod_restrict B T,
      MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
  rw [hmeasureBT]
  have hprod := (Measure.quasiMeasurePreserving_snd
    (μ := volume.restrict B) (ν := volume.restrict T)).ae hpot7
  filter_upwards [hprod] with w hw
  exact hw w.1

private lemma pressure_source_measurable_on_cylinder_hQ8_21 :
    ∀ {f : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ},
      let _ : Set Vec3 := vec3Ball z.1 ρ;
      let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2;
      ∀ (η : Vec3 → ℝ) (R8 : ParabolicPoint → ℝ),
        (∀ᵐ (s : ℝ) ∂Measure.restrict volume T, ∀ (x : Vec3), pressureP8 η f s x = R8 (x, s)) →
          (fun w =>
              pressureP8 η f w.2 w.1) =ᵐ[Measure.restrict volume (parabolicCylinder z.1 z.2 ρ)]
            R8
    := by
  intro f z ρ B T η R8 hpot8
  change (fun w : ParabolicPoint => pressureP8 η f w.2 w.1) =ᵐ[
    volume.restrict (B ×ˢ T)] R8
  have hmeasureBT : volume.restrict (B ×ˢ T) =
      (volume.restrict B).prod (volume.restrict T) := by
    rw [Measure.prod_restrict B T,
      MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
  rw [hmeasureBT]
  have hprod := (Measure.quasiMeasurePreserving_snd
    (μ := volume.restrict B) (ν := volume.restrict T)).ae hpot8
  filter_upwards [hprod] with w hw
  exact hw w.1

private lemma pressure_source_measurable_on_cylinder_huBT_1 :
    ∀ {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ},
      let B : Set Vec3 := vec3Ball z.1 ρ;
      let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2;
      ∀ (Ω' : Set Vec3) (J : Set ℝ)
        (hu :
          AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) u
            (Measure.restrict volume (spaceTimeSet Ω' J))),
        let um : ParabolicPoint → Vec3 := AEStronglyMeasurable.mk u hu;
        B ×ˢ T ⊆ spaceTimeSet Ω' J →
          u =ᵐ[Measure.prod (Measure.restrict volume B) (Measure.restrict volume T)] fun w =>
            um (w.1, w.2)
    := by
  intro u z ρ B T Ω' J hu um hBT
  have h := ae_restrict_of_ae_restrict_of_subset hBT
    (hu.ae_eq_mk : u =ᵐ[volume.restrict (spaceTimeSet Ω' J)] um)
  have hmeasure : volume.restrict (B ×ˢ T) =
      (volume.restrict B).prod (volume.restrict T) := by
    rw [Measure.prod_restrict B T,
      MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
  change u =ᵐ[volume.restrict (B ×ˢ T)] um at h
  exact hmeasure ▸ h

private lemma pressure_source_measurable_on_cylinder_hpBT_2 :
    ∀ {p : ParabolicPoint → ℝ} {z : ParabolicPoint} {ρ : ℝ},
      let B : Set Vec3 := vec3Ball z.1 ρ;
      let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2;
      ∀ (Ω' : Set Vec3) (J : Set ℝ)
        (hp :
          AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) p
            (Measure.restrict volume (spaceTimeSet Ω' J))),
        let pm : ParabolicPoint → ℝ := AEStronglyMeasurable.mk p hp;
        B ×ˢ T ⊆ spaceTimeSet Ω' J →
          p =ᵐ[Measure.prod (Measure.restrict volume B) (Measure.restrict volume T)] fun w =>
            pm (w.1, w.2)
    := by
  intro p z ρ B T Ω' J hp pm hBT
  have h := ae_restrict_of_ae_restrict_of_subset hBT
    (hp.ae_eq_mk : p =ᵐ[volume.restrict (spaceTimeSet Ω' J)] pm)
  have hmeasure : volume.restrict (B ×ˢ T) =
      (volume.restrict B).prod (volume.restrict T) := by
    rw [Measure.prod_restrict B T,
      MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
  change p =ᵐ[volume.restrict (B ×ˢ T)] pm at h
  exact hmeasure ▸ h

private lemma pressure_source_measurable_on_cylinder_hfBT_3 :
    ∀ {f : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ},
      let B : Set Vec3 := vec3Ball z.1 ρ;
      let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2;
      ∀ (Ω' : Set Vec3) (J : Set ℝ)
        (hf :
          AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) f
            (Measure.restrict volume (spaceTimeSet Ω' J))),
        let fm : ParabolicPoint → Vec3 := AEStronglyMeasurable.mk f hf;
        B ×ˢ T ⊆ spaceTimeSet Ω' J →
          f =ᵐ[Measure.prod (Measure.restrict volume B) (Measure.restrict volume T)] fun w =>
            fm (w.1, w.2)
    := by
  intro f z ρ B T Ω' J hf fm hBT
  have h := ae_restrict_of_ae_restrict_of_subset hBT
    (hf.ae_eq_mk : f =ᵐ[volume.restrict (spaceTimeSet Ω' J)] fm)
  have hmeasure : volume.restrict (B ×ˢ T) =
      (volume.restrict B).prod (volume.restrict T) := by
    rw [Measure.prod_restrict B T,
      MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
  change f =ᵐ[volume.restrict (B ×ˢ T)] fm at h
  exact hmeasure ▸ h

private lemma pressure_source_measurable_on_cylinder_hηlapsupp_4 :
    ∀ {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ),
      let B : Set Vec3 := vec3Ball z.1 ρ;
      let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ;
      (∀ (j : Fin 3), tsupport (spatialDeriv η j) ⊆ B) → tsupport (spatialLaplacian η) ⊆ B
    := by
  intro z ρ hρ B η hηdsupp
  change tsupport (fun x => ∑ j : Fin 3,
    spatialDeriv (spatialDeriv η j) j x) ⊆ B
  apply decomposition_ts_support_sum₃_sws
  intro j
  exact (tsupport_fderiv_apply_subset ℝ (basisVec j)).trans (hηdsupp j)

private lemma pressure_source_measurable_on_cylinder_hR2ij_5 :
    ∀ {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ),
      let B : Set Vec3 := vec3Ball z.1 ρ;
      let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ;
      let c : ℝ → Vec3 := fun s j => ⨍ (y : Vec3) in B, u (y, s) j;
      ∀ (Ω' : Set Vec3) (J : Set ℝ)
        (hu :
          AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) u
            (Measure.restrict volume (spaceTimeSet Ω' J)))
        (hcmeas :
          ∀ (j : Fin 3),
            AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
              (fun s =>
                (fun (s : ℝ) (j : Fin 3) => (⨍ (y : Vec3) in vec3Ball z.1 ρ, u (y, s) j : ℝ)) s j)
              (Measure.restrict volume (Ioc (z.2 - ρ ^ 2) z.2))),
        let cm : ℝ → Vec3 := fun s j => AEMeasurable.mk (fun t => c t j) (hcmeas j) s;
        Measurable cm →
          let um : ParabolicPoint → Vec3 := AEStronglyMeasurable.mk u hu;
          Measurable um →
            (∀ (i j : Fin 3), Measurable (mixedSecond η i j)) →
              (Measurable (β := ℝ) fun (w : ParabolicPoint × Vec3) =>
                  -newtonianKernel (w.1.1 - w.2)) →
                (∀ {g : ParabolicPoint × Vec3 → ℝ},
                    Measurable g →
                      AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
                        (fun (w : ParabolicPoint) =>
                          @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume
                            fun (y : Vec3) => g (w, y))
                        volume) →
                  ∀ (i j : Fin 3),
                    AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
                      (fun (w : ParabolicPoint) =>
                        @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                          -newtonianKernel (w.1 - y) *
                            (mixedSecond η i j y * pressureUTensor um cm (y, w.2) i j))
                      volume
    := by
  intro u z ρ hρ B η c Ω' J hu hcmeas cm hcm um hum hηdd hkernel0 hIntegral i j
  exact hIntegral (g := fun w : ParabolicPoint × Vec3 =>
    -newtonianKernel (w.1.1 - w.2) *
      (mixedSecond η i j w.2 *
        pressureUTensor um cm (w.2, w.1.2) i j)) (by
    exact hkernel0.mul (((hηdd i j).comp measurable_snd).mul
      ((pressure_tensor_measurable hum hcm i j).comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))))

private lemma pressure_source_measurable_on_cylinder_hR2_6 :
    ∀ {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ),
      let B : Set Vec3 := vec3Ball z.1 ρ;
      let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ;
      let c : ℝ → Vec3 := fun s j => ⨍ (y : Vec3) in B, u (y, s) j;
      ∀ (Ω' : Set Vec3) (J : Set ℝ)
        (hu :
          AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) u
            (Measure.restrict volume (spaceTimeSet Ω' J)))
        (hcmeas :
          ∀ (j : Fin 3),
            AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
              (fun s =>
                (fun (s : ℝ) (j : Fin 3) => (⨍ (y : Vec3) in vec3Ball z.1 ρ, u (y, s) j : ℝ)) s j)
              (Measure.restrict volume (Ioc (z.2 - ρ ^ 2) z.2))),
        let cm : ℝ → Vec3 := fun s j => AEMeasurable.mk (fun t => c t j) (hcmeas j) s;
        let um : ParabolicPoint → Vec3 := AEStronglyMeasurable.mk u hu;
        let R2 : ParabolicPoint → ℝ := fun w =>
          ∑ i : Fin 3,
            ∑ j : Fin 3,
              @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                -newtonianKernel (w.1 - y) *
                  (mixedSecond η i j y * pressureUTensor um cm (y, w.2) i j);
        (∀ (i j : Fin 3),
            AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
              (fun (w : ParabolicPoint) =>
                @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                  -newtonianKernel (w.1 - y) *
                    (mixedSecond η i j y * pressureUTensor um cm (y, w.2) i j))
              volume) →
          AEMeasurable (_m := MeasureSpace.toMeasurableSpace) R2 volume
    := by
  intro u z ρ hρ B η c Ω' J hu hcmeas cm um R2 hR2ij
  dsimp [R2]
  change AEMeasurable (∑ i : Fin 3, ∑ j : Fin 3, fun w : ParabolicPoint =>
    ∫ y : Vec3, (-newtonianKernel (w.1 - y)) *
      (mixedSecond η i j y * pressureUTensor um cm (y, w.2) i j)) volume
  exact Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3)) (fun i _ =>
    Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3)) (fun j _ => hR2ij i j))

private lemma pressure_source_measurable_on_cylinder_hR3ij_7 :
    ∀ {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ),
      let B : Set Vec3 := vec3Ball z.1 ρ;
      let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ;
      let c : ℝ → Vec3 := fun s j => ⨍ (y : Vec3) in B, u (y, s) j;
      ∀ (Ω' : Set Vec3) (J : Set ℝ)
        (hu :
          AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) u
            (Measure.restrict volume (spaceTimeSet Ω' J)))
        (hcmeas :
          ∀ (j : Fin 3),
            AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
              (fun s =>
                (fun (s : ℝ) (j : Fin 3) => (⨍ (y : Vec3) in vec3Ball z.1 ρ, u (y, s) j : ℝ)) s j)
              (Measure.restrict volume (Ioc (z.2 - ρ ^ 2) z.2))),
        let cm : ℝ → Vec3 := fun s j => AEMeasurable.mk (fun t => c t j) (hcmeas j) s;
        Measurable cm →
          let um : ParabolicPoint → Vec3 := AEStronglyMeasurable.mk u hu;
          Measurable um →
            (∀ (j : Fin 3), Measurable (spatialDeriv η j)) →
              (∀ (j : Fin 3),
                  Measurable (β := ℝ) fun (w : ParabolicPoint × Vec3) =>
                    spatialDeriv newtonianKernel j (w.1.1 - w.2)) →
                (∀ {g : ParabolicPoint × Vec3 → ℝ},
                    Measurable g →
                      AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
                        (fun (w : ParabolicPoint) =>
                          @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume
                            fun (y : Vec3) => g (w, y))
                        volume) →
                  ∀ (i j : Fin 3),
                    AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
                      (fun (w : ParabolicPoint) =>
                        @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                          spatialDeriv newtonianKernel j (w.1 - y) *
                            (pressureUTensor um cm (y, w.2) i j * spatialDeriv η i y))
                      volume
    := by
  intro u z ρ hρ B η c Ω' J hu hcmeas cm hcm um hum hηd hkernel1 hIntegral i j
  exact hIntegral (g := fun w : ParabolicPoint × Vec3 =>
    spatialDeriv newtonianKernel j (w.1.1 - w.2) *
      (pressureUTensor um cm (w.2, w.1.2) i j * spatialDeriv η i w.2)) (by
    exact (hkernel1 j).mul (((pressure_tensor_measurable hum hcm i j).comp
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).mul
        ((hηd i).comp measurable_snd)))

private lemma pressure_source_measurable_on_cylinder_hR3_8 :
    ∀ {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ),
      let B : Set Vec3 := vec3Ball z.1 ρ;
      let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ;
      let c : ℝ → Vec3 := fun s j => ⨍ (y : Vec3) in B, u (y, s) j;
      ∀ (Ω' : Set Vec3) (J : Set ℝ)
        (hu :
          AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) u
            (Measure.restrict volume (spaceTimeSet Ω' J)))
        (hcmeas :
          ∀ (j : Fin 3),
            AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
              (fun s =>
                (fun (s : ℝ) (j : Fin 3) => (⨍ (y : Vec3) in vec3Ball z.1 ρ, u (y, s) j : ℝ)) s j)
              (Measure.restrict volume (Ioc (z.2 - ρ ^ 2) z.2))),
        let cm : ℝ → Vec3 := fun s j => AEMeasurable.mk (fun t => c t j) (hcmeas j) s;
        let um : ParabolicPoint → Vec3 := AEStronglyMeasurable.mk u hu;
        let R3 : ParabolicPoint → ℝ := fun w =>
          ∑ i : Fin 3,
            ∑ j : Fin 3,
              @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                spatialDeriv newtonianKernel j (w.1 - y) *
                  (pressureUTensor um cm (y, w.2) i j * spatialDeriv η i y);
        (∀ (i j : Fin 3),
            AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
              (fun (w : ParabolicPoint) =>
                @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                  spatialDeriv newtonianKernel j (w.1 - y) *
                    (pressureUTensor um cm (y, w.2) i j * spatialDeriv η i y))
              volume) →
          AEMeasurable (_m := MeasureSpace.toMeasurableSpace) R3 volume
    := by
  intro u z ρ hρ B η c Ω' J hu hcmeas cm um R3 hR3ij
  dsimp [R3]
  change AEMeasurable (∑ i : Fin 3, ∑ j : Fin 3, fun w : ParabolicPoint =>
    ∫ y : Vec3, spatialDeriv newtonianKernel j (w.1 - y) *
      (pressureUTensor um cm (y, w.2) i j * spatialDeriv η i y)) volume
  exact Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3)) (fun i _ =>
    Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3)) (fun j _ => hR3ij i j))

private lemma pressure_source_measurable_on_cylinder_hR4ij_9 :
    ∀ {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ),
      let B : Set Vec3 := vec3Ball z.1 ρ;
      let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ;
      let c : ℝ → Vec3 := fun s j => ⨍ (y : Vec3) in B, u (y, s) j;
      ∀ (Ω' : Set Vec3) (J : Set ℝ)
        (hu :
          AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) u
            (Measure.restrict volume (spaceTimeSet Ω' J)))
        (hcmeas :
          ∀ (j : Fin 3),
            AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
              (fun s =>
                (fun (s : ℝ) (j : Fin 3) => (⨍ (y : Vec3) in vec3Ball z.1 ρ, u (y, s) j : ℝ)) s j)
              (Measure.restrict volume (Ioc (z.2 - ρ ^ 2) z.2))),
        let cm : ℝ → Vec3 := fun s j => AEMeasurable.mk (fun t => c t j) (hcmeas j) s;
        Measurable cm →
          let um : ParabolicPoint → Vec3 := AEStronglyMeasurable.mk u hu;
          Measurable um →
            (∀ (j : Fin 3), Measurable (spatialDeriv η j)) →
              (∀ (j : Fin 3),
                  Measurable (β := ℝ) fun (w : ParabolicPoint × Vec3) =>
                    spatialDeriv newtonianKernel j (w.1.1 - w.2)) →
                (∀ {g : ParabolicPoint × Vec3 → ℝ},
                    Measurable g →
                      AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
                        (fun (w : ParabolicPoint) =>
                          @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume
                            fun (y : Vec3) => g (w, y))
                        volume) →
                  ∀ (i j : Fin 3),
                    AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
                      (fun (w : ParabolicPoint) =>
                        @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                          spatialDeriv newtonianKernel i (w.1 - y) *
                            (pressureUTensor um cm (y, w.2) i j * spatialDeriv η j y))
                      volume
    := by
  intro u z ρ hρ B η c Ω' J hu hcmeas cm hcm um hum hηd hkernel1 hIntegral i j
  exact hIntegral (g := fun w : ParabolicPoint × Vec3 =>
    spatialDeriv newtonianKernel i (w.1.1 - w.2) *
      (pressureUTensor um cm (w.2, w.1.2) i j * spatialDeriv η j w.2)) (by
    exact (hkernel1 i).mul (((pressure_tensor_measurable hum hcm i j).comp
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).mul
        ((hηd j).comp measurable_snd)))

private lemma pressure_source_measurable_on_cylinder_hR4_10 :
    ∀ {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ),
      let B : Set Vec3 := vec3Ball z.1 ρ;
      let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ;
      let c : ℝ → Vec3 := fun s j => ⨍ (y : Vec3) in B, u (y, s) j;
      ∀ (Ω' : Set Vec3) (J : Set ℝ)
        (hu :
          AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) u
            (Measure.restrict volume (spaceTimeSet Ω' J)))
        (hcmeas :
          ∀ (j : Fin 3),
            AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
              (fun s =>
                (fun (s : ℝ) (j : Fin 3) => (⨍ (y : Vec3) in vec3Ball z.1 ρ, u (y, s) j : ℝ)) s j)
              (Measure.restrict volume (Ioc (z.2 - ρ ^ 2) z.2))),
        let cm : ℝ → Vec3 := fun s j => AEMeasurable.mk (fun t => c t j) (hcmeas j) s;
        let um : ParabolicPoint → Vec3 := AEStronglyMeasurable.mk u hu;
        let R4 : ParabolicPoint → ℝ := fun w =>
          ∑ i : Fin 3,
            ∑ j : Fin 3,
              @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                spatialDeriv newtonianKernel i (w.1 - y) *
                  (pressureUTensor um cm (y, w.2) i j * spatialDeriv η j y);
        (∀ (i j : Fin 3),
            AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
              (fun (w : ParabolicPoint) =>
                @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                  spatialDeriv newtonianKernel i (w.1 - y) *
                    (pressureUTensor um cm (y, w.2) i j * spatialDeriv η j y))
              volume) →
          AEMeasurable (_m := MeasureSpace.toMeasurableSpace) R4 volume
    := by
  intro u z ρ hρ B η c Ω' J hu hcmeas cm um R4 hR4ij
  dsimp [R4]
  change AEMeasurable (∑ i : Fin 3, ∑ j : Fin 3, fun w : ParabolicPoint =>
    ∫ y : Vec3, spatialDeriv newtonianKernel i (w.1 - y) *
      (pressureUTensor um cm (y, w.2) i j * spatialDeriv η j y)) volume
  exact Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3)) (fun i _ =>
    Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3)) (fun j _ => hR4ij i j))

private lemma pressure_source_measurable_on_cylinder_hR5_11 :
    ∀ {p : ParabolicPoint → ℝ} {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ),
      let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ;
      ∀ (Ω' : Set Vec3) (J : Set ℝ)
        (hp :
          AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) p
            (Measure.restrict volume (spaceTimeSet Ω' J))),
        let pm : ParabolicPoint → ℝ := AEStronglyMeasurable.mk p hp;
        Measurable pm →
          Measurable (spatialLaplacian η) →
            (Measurable (β := ℝ) fun (w : ParabolicPoint × Vec3) =>
                -newtonianKernel (w.1.1 - w.2)) →
              (∀ {g : ParabolicPoint × Vec3 → ℝ},
                  Measurable g →
                    AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
                      (fun (w : ParabolicPoint) =>
                        @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                          g (w, y))
                      volume) →
                let R5 : ParabolicPoint → ℝ := fun w =>
                  -@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                      -newtonianKernel (w.1 - y) * (pm (y, w.2) * spatialLaplacian η y);
                AEMeasurable (_m := MeasureSpace.toMeasurableSpace) R5 volume
    := by
  intro p z ρ hρ η Ω' J hp pm hpm hηlap hkernel0 hIntegral R5
  dsimp [R5]
  convert (hIntegral (g := fun w : ParabolicPoint × Vec3 =>
    -newtonianKernel (w.1.1 - w.2) *
      (pm (w.2, w.1.2) * spatialLaplacian η w.2)) (by
    apply hkernel0.mul
    exact (hpm.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).mul
      (hηlap.comp measurable_snd))).neg using 1

private lemma pressure_source_measurable_on_cylinder_hR6j_12 :
    ∀ {p : ParabolicPoint → ℝ} {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ),
      let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ;
      ∀ (Ω' : Set Vec3) (J : Set ℝ)
        (hp :
          AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) p
            (Measure.restrict volume (spaceTimeSet Ω' J))),
        let pm : ParabolicPoint → ℝ := AEStronglyMeasurable.mk p hp;
        Measurable pm →
          (∀ (j : Fin 3), Measurable (spatialDeriv η j)) →
            (∀ (j : Fin 3),
                Measurable (β := ℝ) fun (w : ParabolicPoint × Vec3) =>
                  spatialDeriv newtonianKernel j (w.1.1 - w.2)) →
              (∀ {g : ParabolicPoint × Vec3 → ℝ},
                  Measurable g →
                    AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
                      (fun (w : ParabolicPoint) =>
                        @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                          g (w, y))
                      volume) →
                ∀ (j : Fin 3),
                  AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
                    (fun (w : ParabolicPoint) =>
                      @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                        spatialDeriv newtonianKernel j (w.1 - y) *
                          (spatialDeriv η j y * pm (y, w.2)))
                    volume
    := by
  intro p z ρ hρ η Ω' J hp pm hpm hηd hkernel1 hIntegral j
  exact hIntegral (g := fun w : ParabolicPoint × Vec3 =>
    spatialDeriv newtonianKernel j (w.1.1 - w.2) *
      (spatialDeriv η j w.2 * pm (w.2, w.1.2))) (by
    apply hkernel1 j |>.mul
    exact (hηd j).comp measurable_snd |>.mul
      (hpm.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))

private lemma pressure_source_measurable_on_cylinder_hR6_13 :
    ∀ {p : ParabolicPoint → ℝ} {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ),
      let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ;
      ∀ (Ω' : Set Vec3) (J : Set ℝ)
        (hp :
          AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) p
            (Measure.restrict volume (spaceTimeSet Ω' J))),
        let pm : ParabolicPoint → ℝ := AEStronglyMeasurable.mk p hp;
        let R6 : ParabolicPoint → ℝ := fun w =>
          -2 *
            ∑ j : Fin 3,
              @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                spatialDeriv newtonianKernel j (w.1 - y) * (spatialDeriv η j y * pm (y, w.2));
        (∀ (j : Fin 3),
            AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
              (fun (w : ParabolicPoint) =>
                @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                  spatialDeriv newtonianKernel j (w.1 - y) * (spatialDeriv η j y * pm (y, w.2)))
              volume) →
          AEMeasurable (_m := MeasureSpace.toMeasurableSpace) R6 volume
    := by
  intro p z ρ hρ η Ω' J hp pm R6 hR6j
  dsimp [R6]
  change AEMeasurable ((-2 : ℝ) •
    (∑ j : Fin 3, fun w : ParabolicPoint => ∫ y : Vec3,
      spatialDeriv newtonianKernel j (w.1 - y) *
        (spatialDeriv η j y * pm (y, w.2)))) volume
  exact (Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3))
    (fun j _ => hR6j j)).const_mul (-2)

private lemma pressure_source_measurable_on_cylinder_hR7j_14 :
    ∀ {f : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ),
      let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ;
      ∀ (Ω' : Set Vec3) (J : Set ℝ)
        (hf :
          AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) f
            (Measure.restrict volume (spaceTimeSet Ω' J))),
        let fm : ParabolicPoint → Vec3 := AEStronglyMeasurable.mk f hf;
        Measurable fm →
          Measurable η →
            (∀ (j : Fin 3),
                Measurable (β := ℝ) fun (w : ParabolicPoint × Vec3) =>
                  spatialDeriv newtonianKernel j (w.1.1 - w.2)) →
              (∀ {g : ParabolicPoint × Vec3 → ℝ},
                  Measurable g →
                    AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
                      (fun (w : ParabolicPoint) =>
                        @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                          g (w, y))
                      volume) →
                ∀ (j : Fin 3),
                  AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
                    (fun (w : ParabolicPoint) =>
                      @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                        spatialDeriv newtonianKernel j (w.1 - y) * (η y * fm (y, w.2) j))
                    volume
    := by
  intro f z ρ hρ η Ω' J hf fm hfm hηm hkernel1 hIntegral j
  exact hIntegral (g := fun w : ParabolicPoint × Vec3 =>
    spatialDeriv newtonianKernel j (w.1.1 - w.2) *
      (η w.2 * fm (w.2, w.1.2) j)) (by
    apply hkernel1 j |>.mul
    exact (hηm.comp measurable_snd).mul
      ((ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).measurable.comp
        (hfm.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  )

private lemma pressure_source_measurable_on_cylinder_hR7_15 :
    ∀ {f : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ),
      let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ;
      ∀ (Ω' : Set Vec3) (J : Set ℝ)
        (hf :
          AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) f
            (Measure.restrict volume (spaceTimeSet Ω' J))),
        let fm : ParabolicPoint → Vec3 := AEStronglyMeasurable.mk f hf;
        let R7 : ParabolicPoint → ℝ := fun w =>
          -∑ j : Fin 3,
              @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                spatialDeriv newtonianKernel j (w.1 - y) * (η y * fm (y, w.2) j);
        (∀ (j : Fin 3),
            AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
              (fun (w : ParabolicPoint) =>
                @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                  spatialDeriv newtonianKernel j (w.1 - y) * (η y * fm (y, w.2) j))
              volume) →
          AEMeasurable (_m := MeasureSpace.toMeasurableSpace) R7 volume
    := by
  intro f z ρ hρ η Ω' J hf fm R7 hR7j
  dsimp [R7]
  change AEMeasurable (-∑ j : Fin 3, fun w : ParabolicPoint =>
    ∫ y : Vec3, spatialDeriv newtonianKernel j (w.1 - y) *
      (η y * fm (y, w.2) j)) volume
  exact (Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3))
    (fun j _ => hR7j j)).neg

private lemma pressure_source_measurable_on_cylinder_hR8j_16 :
    ∀ {f : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ),
      let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ;
      ∀ (Ω' : Set Vec3) (J : Set ℝ)
        (hf :
          AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) f
            (Measure.restrict volume (spaceTimeSet Ω' J))),
        let fm : ParabolicPoint → Vec3 := AEStronglyMeasurable.mk f hf;
        Measurable fm →
          (∀ (j : Fin 3), Measurable (spatialDeriv η j)) →
            (Measurable (β := ℝ) fun (w : ParabolicPoint × Vec3) =>
                -newtonianKernel (w.1.1 - w.2)) →
              (∀ {g : ParabolicPoint × Vec3 → ℝ},
                  Measurable g →
                    AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
                      (fun (w : ParabolicPoint) =>
                        @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                          g (w, y))
                      volume) →
                ∀ (j : Fin 3),
                  AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
                    (fun (w : ParabolicPoint) =>
                      @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                        -newtonianKernel (w.1 - y) * (spatialDeriv η j y * fm (y, w.2) j))
                    volume
    := by
  intro f z ρ hρ η Ω' J hf fm hfm hηd hkernel0 hIntegral j
  exact hIntegral (g := fun w : ParabolicPoint × Vec3 =>
    -newtonianKernel (w.1.1 - w.2) *
      (spatialDeriv η j w.2 * fm (w.2, w.1.2) j)) (by
    apply hkernel0.mul
    exact (hηd j).comp measurable_snd |>.mul
      ((ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).measurable.comp
        (hfm.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  )

private lemma pressure_source_measurable_on_cylinder_hR8_17 :
    ∀ {f : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ),
      let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ;
      ∀ (Ω' : Set Vec3) (J : Set ℝ)
        (hf :
          AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) f
            (Measure.restrict volume (spaceTimeSet Ω' J))),
        let fm : ParabolicPoint → Vec3 := AEStronglyMeasurable.mk f hf;
        let R8 : ParabolicPoint → ℝ := fun w =>
          -∑ j : Fin 3,
              @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                -newtonianKernel (w.1 - y) * (spatialDeriv η j y * fm (y, w.2) j);
        (∀ (j : Fin 3),
            AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
              (fun (w : ParabolicPoint) =>
                @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                  -newtonianKernel (w.1 - y) * (spatialDeriv η j y * fm (y, w.2) j))
              volume) →
          AEMeasurable (_m := MeasureSpace.toMeasurableSpace) R8 volume
    := by
  intro f z ρ hρ η Ω' J hf fm R8 hR8j
  dsimp [R8]
  change AEMeasurable (-∑ j : Fin 3, fun w : ParabolicPoint =>
    ∫ y : Vec3, (-newtonianKernel (w.1 - y)) *
      (spatialDeriv η j y * fm (y, w.2) j)) volume
  exact (Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3))
    (fun j _ => hR8j j)).neg

private lemma pressure_source_measurable_on_cylinder_hpot5_18 :
    ∀ {p : ParabolicPoint → ℝ} {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ),
      let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2;
      let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ;
      ∀ (Ω' : Set Vec3) (J : Set ℝ)
        (hp :
          AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) p
            (Measure.restrict volume (spaceTimeSet Ω' J))),
        let pm : ParabolicPoint → ℝ := AEStronglyMeasurable.mk p hp;
        (∀ᵐ (s : ℝ) ∂Measure.restrict volume (Ioc (z.2 - ρ ^ 2) z.2),
            (fun y => p (y, s) * spatialLaplacian η y) =ᵐ[volume] fun y =>
              pm (y, s) * spatialLaplacian η y) →
          let R5 : ParabolicPoint → ℝ := fun w =>
            -@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                -newtonianKernel (w.1 - y) * (pm (y, w.2) * spatialLaplacian η y);
          ∀ᵐ (s : ℝ) ∂Measure.restrict volume T, ∀ (x : Vec3), pressureP5 η p s x = R5 (x, s)
    := by
  intro p z ρ hρ T η Ω' J hp pm hsrc5 R5
  filter_upwards [hsrc5] with s hs x
  unfold pressureP5 R5
  congr 1
  apply integral_congr_ae
  filter_upwards [hs] with y hy
  rw [hy]

private lemma pressure_source_measurable_on_cylinder_hpQ_19 :
    ∀ {p : ParabolicPoint → ℝ} {z : ParabolicPoint} {ρ : ℝ},
      let B : Set Vec3 := vec3Ball z.1 ρ;
      let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2;
      ∀ (Ω' : Set Vec3) (J : Set ℝ)
        (hp :
          AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) p
            (Measure.restrict volume (spaceTimeSet Ω' J))),
        let pm : ParabolicPoint → ℝ := AEStronglyMeasurable.mk p hp;
        (p =ᵐ[Measure.prod (Measure.restrict volume B) (Measure.restrict volume T)] fun w =>
            pm (w.1, w.2)) →
          (fun w => p w) =ᵐ[Measure.restrict volume (parabolicCylinder z.1 z.2 ρ)] fun w => pm w
    := by
  intro p z ρ B T Ω' J hp pm hpBT
  change p =ᵐ[volume.restrict (B ×ˢ T)] pm
  have hmeasureBT : volume.restrict (B ×ˢ T) =
      (volume.restrict B).prod (volume.restrict T) := by
    rw [Measure.prod_restrict B T,
      MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
  rw [hmeasureBT]
  exact hpBT

private lemma pressure_source_measurable_on_cylinder_hP1ae_20 :
    ∀ {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
      {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ),
      let B : Set Vec3 := vec3Ball z.1 ρ;
      let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2;
      let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ;
      let c : ℝ → Vec3 := fun s j => ⨍ (y : Vec3) in B, u (y, s) j;
      ∀ (Ω' : Set Vec3) (J : Set ℝ)
        (hu :
          AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) u
            (Measure.restrict volume (spaceTimeSet Ω' J)))
        (hp :
          AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) p
            (Measure.restrict volume (spaceTimeSet Ω' J)))
        (hf :
          AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) f
            (Measure.restrict volume (spaceTimeSet Ω' J))),
        AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) p
            (Measure.restrict volume (spaceTimeSet Ω' T)) →
          ∀
            (hcmeas :
              ∀ (j : Fin 3),
                AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
                  (fun s =>
                    (fun (s : ℝ) (j : Fin 3) => (⨍ (y : Vec3) in vec3Ball z.1 ρ, u (y, s) j : ℝ))
                      s j)
                  (Measure.restrict volume (Ioc (z.2 - ρ ^ 2) z.2))),
            let cm : ℝ → Vec3 := fun s j => AEMeasurable.mk (fun t => c t j) (hcmeas j) s;
            let um : ParabolicPoint → Vec3 := AEStronglyMeasurable.mk u hu;
            let pm : ParabolicPoint → ℝ := AEStronglyMeasurable.mk p hp;
            let fm : ParabolicPoint → Vec3 := AEStronglyMeasurable.mk f hf;
            let R2 : ParabolicPoint → ℝ := fun w =>
              ∑ i : Fin 3,
                ∑ j : Fin 3,
                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                    -newtonianKernel (w.1 - y) *
                      (mixedSecond η i j y * pressureUTensor um cm (y, w.2) i j);
            let R3 : ParabolicPoint → ℝ := fun w =>
              ∑ i : Fin 3,
                ∑ j : Fin 3,
                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                    spatialDeriv newtonianKernel j (w.1 - y) *
                      (pressureUTensor um cm (y, w.2) i j * spatialDeriv η i y);
            let R4 : ParabolicPoint → ℝ := fun w =>
              ∑ i : Fin 3,
                ∑ j : Fin 3,
                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                    spatialDeriv newtonianKernel i (w.1 - y) *
                      (pressureUTensor um cm (y, w.2) i j * spatialDeriv η j y);
            let R5 : ParabolicPoint → ℝ := fun w =>
              -@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                  -newtonianKernel (w.1 - y) * (pm (y, w.2) * spatialLaplacian η y);
            let R6 : ParabolicPoint → ℝ := fun w =>
              -2 *
                ∑ j : Fin 3,
                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                    spatialDeriv newtonianKernel j (w.1 - y) * (spatialDeriv η j y * pm (y, w.2));
            let R7 : ParabolicPoint → ℝ := fun w =>
              -∑ j : Fin 3,
                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                    spatialDeriv newtonianKernel j (w.1 - y) * (η y * fm (y, w.2) j);
            let R8 : ParabolicPoint → ℝ := fun w =>
              -∑ j : Fin 3,
                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                    -newtonianKernel (w.1 - y) * (spatialDeriv η j y * fm (y, w.2) j);
            (fun w =>
                  pressureP2 η u c w.2
                    w.1) =ᵐ[Measure.restrict volume (parabolicCylinder z.1 z.2 ρ)]
                R2 →
              (fun w =>
                    pressureP3 η u c w.2
                      w.1) =ᵐ[Measure.restrict volume (parabolicCylinder z.1 z.2 ρ)]
                  R3 →
                (fun w =>
                      pressureP4 η u c w.2
                        w.1) =ᵐ[Measure.restrict volume (parabolicCylinder z.1 z.2 ρ)]
                    R4 →
                  (fun w =>
                        pressureP5 η p w.2
                          w.1) =ᵐ[Measure.restrict volume (parabolicCylinder z.1 z.2 ρ)]
                      R5 →
                    (fun w =>
                          pressureP6 η p w.2
                            w.1) =ᵐ[Measure.restrict volume (parabolicCylinder z.1 z.2 ρ)]
                        R6 →
                      (fun w =>
                            pressureP7 η f w.2
                              w.1) =ᵐ[Measure.restrict volume (parabolicCylinder z.1 z.2 ρ)]
                          R7 →
                        (fun w =>
                              pressureP8 η f w.2
                                w.1) =ᵐ[Measure.restrict volume (parabolicCylinder z.1 z.2 ρ)]
                            R8 →
                          let R1 : ParabolicPoint → ℝ := fun w =>
                            η w.1 * pm (w.1, w.2) -
                              (R2 w + R3 w + R4 w + R5 w + R6 w + R7 w + R8 w);
                          ((fun w =>
                                p w) =ᵐ[Measure.restrict volume (parabolicCylinder z.1 z.2 ρ)]
                              fun w => pm w) →
                            (fun w =>
                                pressureP1 η u c p f w.2
                                  w.1) =ᵐ[Measure.restrict volume (parabolicCylinder z.1 z.2 ρ)]
                              R1
    := by
  intro u p f z ρ hρ B T η c Ω' J hu hp hf hp' hcmeas cm um pm fm R2 R3 R4 R5 R6 R7 R8 hQ2 hQ3 hQ4
    hQ5 hQ6 hQ7 hQ8 R1 hpQ
  filter_upwards [hpQ, hQ2, hQ3, hQ4, hQ5, hQ6, hQ7, hQ8]
    with w hp h2 h3 h4 h5 h6 h7 h8
  have hp' : p (w.1, w.2) = pm (w.1, w.2) := by
    change p w = pm w
    exact hp
  unfold pressureP1 R1
  rw [hp', h2, h3, h4, h5, h6, h7, h8]

private lemma pressure_source_measurable_on_cylinder_hcm_1 :
    ∀ {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ},
      let B : Set Vec3 := vec3Ball z.1 ρ;
      let c : ℝ → Vec3 := fun (s : ℝ) (j : Fin (3 : ℕ)) => ⨍ (y : Vec3) in B, u (y, s) j;
      ∀
        (hcmeas :
          ∀ (j : Fin (3 : ℕ)),
            AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
              (fun (s : ℝ) =>
                (fun (s : ℝ) (j : Fin (3 : ℕ)) => (⨍ (y : Vec3) in vec3Ball z.1 ρ, u (y, s) j : ℝ))
                  s j)
              (Measure.restrict volume (Ioc (z.2 - ρ ^ (2 : ℕ)) z.2))),
        let cm : ℝ → Vec3 := fun (s : ℝ) (j : Fin (3 : ℕ)) =>
          AEMeasurable.mk (fun (t : ℝ) => c t j) (hcmeas j) s;
        Measurable cm
    := by
  intro u z ρ B c hcmeas cm
  apply Measurable.of_eval
  intro j
  exact (hcmeas j).measurable_mk

private lemma pressure_source_measurable_on_cylinder_hcmEq_2 :
    ∀ {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ},
      let B : Set Vec3 := vec3Ball z.1 ρ;
      let T : Set ℝ := Ioc (z.2 - ρ ^ (2 : ℕ)) z.2;
      let c : ℝ → Vec3 := fun (s : ℝ) (j : Fin (3 : ℕ)) => ⨍ (y : Vec3) in B, u (y, s) j;
      ∀
        (hcmeas :
          ∀ (j : Fin (3 : ℕ)),
            AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
              (fun (s : ℝ) =>
                (fun (s : ℝ) (j : Fin (3 : ℕ)) => (⨍ (y : Vec3) in vec3Ball z.1 ρ, u (y, s) j : ℝ))
                  s j)
              (Measure.restrict volume (Ioc (z.2 - ρ ^ (2 : ℕ)) z.2))),
        let cm : ℝ → Vec3 := fun (s : ℝ) (j : Fin (3 : ℕ)) =>
          AEMeasurable.mk (fun (t : ℝ) => c t j) (hcmeas j) s;
        c =ᵐ[Measure.restrict volume T] cm
    := by
  intro u z ρ B T c hcmeas cm
  filter_upwards [(hcmeas 0).ae_eq_mk, (hcmeas 1).ae_eq_mk,
    (hcmeas 2).ae_eq_mk] with s h0 h1 h2
  funext j
  fin_cases j <;> assumption

private lemma pressure_source_measurable_on_cylinder_huSlices_3 :
    ∀ {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ},
      let B : Set Vec3 := vec3Ball z.1 ρ;
      let T : Set ℝ := Ioc (z.2 - ρ ^ (2 : ℕ)) z.2;
      ∀ (Ω' : Set Vec3) (J : Set ℝ)
        (hu :
          AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) u
            (Measure.restrict volume (spaceTimeSet Ω' J))),
        let um : ParabolicPoint → Vec3 := AEStronglyMeasurable.mk u hu;
        (u =ᵐ[Measure.prod (Measure.restrict volume (vec3Ball z.1 ρ))
              (Measure.restrict volume (Ioc (z.2 - ρ ^ (2 : ℕ)) z.2))]
            fun (w : Vec3 × ℝ) => AEStronglyMeasurable.mk u hu (w.1, w.2)) →
          ∀ᵐ (s : ℝ) ∂Measure.restrict volume T,
            ∀ᵐ (y : Vec3) ∂Measure.restrict volume B, u (y, s) = um (y, s)
    := by
  intro u z ρ B T Ω' J hu um huBT
  have hswap := MeasureTheory.Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp
    huBT
  exact MeasureTheory.Measure.ae_ae_of_ae_prod hswap

private lemma pressure_source_measurable_on_cylinder_hpSlices_4 :
    ∀ {p : ParabolicPoint → ℝ} {z : ParabolicPoint} {ρ : ℝ},
      let B : Set Vec3 := vec3Ball z.1 ρ;
      let T : Set ℝ := Ioc (z.2 - ρ ^ (2 : ℕ)) z.2;
      ∀ (Ω' : Set Vec3) (J : Set ℝ)
        (hp :
          AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) p
            (Measure.restrict volume (spaceTimeSet Ω' J))),
        let pm : ParabolicPoint → ℝ := AEStronglyMeasurable.mk p hp;
        (p =ᵐ[Measure.prod (Measure.restrict volume (vec3Ball z.1 ρ))
              (Measure.restrict volume (Ioc (z.2 - ρ ^ (2 : ℕ)) z.2))]
            fun (w : Vec3 × ℝ) => AEStronglyMeasurable.mk p hp (w.1, w.2)) →
          ∀ᵐ (s : ℝ) ∂Measure.restrict volume T,
            ∀ᵐ (y : Vec3) ∂Measure.restrict volume B, p (y, s) = pm (y, s)
    := by
  intro p z ρ B T Ω' J hp pm hpBT
  have hswap := MeasureTheory.Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp
    hpBT
  exact MeasureTheory.Measure.ae_ae_of_ae_prod hswap

private lemma pressure_source_measurable_on_cylinder_hfSlices_5 :
    ∀ {f : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ},
      let B : Set Vec3 := vec3Ball z.1 ρ;
      let T : Set ℝ := Ioc (z.2 - ρ ^ (2 : ℕ)) z.2;
      ∀ (Ω' : Set Vec3) (J : Set ℝ)
        (hf :
          AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) f
            (Measure.restrict volume (spaceTimeSet Ω' J))),
        let fm : ParabolicPoint → Vec3 := AEStronglyMeasurable.mk f hf;
        (f =ᵐ[Measure.prod (Measure.restrict volume (vec3Ball z.1 ρ))
              (Measure.restrict volume (Ioc (z.2 - ρ ^ (2 : ℕ)) z.2))]
            fun (w : Vec3 × ℝ) => AEStronglyMeasurable.mk f hf (w.1, w.2)) →
          ∀ᵐ (s : ℝ) ∂Measure.restrict volume T,
            ∀ᵐ (y : Vec3) ∂Measure.restrict volume B, f (y, s) = fm (y, s)
    := by
  intro f z ρ B T Ω' J hf fm hfBT
  have hswap := MeasureTheory.Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp
    hfBT
  exact MeasureTheory.Measure.ae_ae_of_ae_prod hswap

private lemma pressure_source_measurable_on_cylinder_hIntegral_6 :
    ∀ {g : ParabolicPoint × Vec3 → ℝ},
      Measurable g →
        AEMeasurable (β := ℝ) (_m := MeasureSpace.toMeasurableSpace)
          (fun (w : ParabolicPoint) =>
            @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) => g (w, y))
          volume
    := by
  intro g hg
  have h := hg.aestronglyMeasurable.integral_prod_right'
    (μ := (volume : Measure ParabolicPoint))
    (ν := (volume : Measure Vec3))
  simpa only [Function.comp_apply] using h.aemeasurable

theorem pressure_source_measurable_on_cylinder
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∃ (B : Set Vec3) (T : Set ℝ) (η : Vec3 → ℝ)
      (c : ℝ → Vec3),
      B = vec3Ball z.1 ρ ∧ T = Ioc (z.2 - ρ ^ 2) z.2 ∧
      η = mollifiedBallCutoff z.1 hρ ∧
      (∀ s, c s = fun j =>
        MeasureTheory.average (volume.restrict B) (fun y => u (y, s) j)) ∧
      AEStronglyMeasurable
        (fun w : ParabolicPoint => pressureP1 η u c p f w.2 w.1)
        (volume.restrict (parabolicCylinder z.1 z.2 ρ)) ∧
      AEStronglyMeasurable
        (fun w : ParabolicPoint => pressureP2 η u c w.2 w.1)
        (volume.restrict (parabolicCylinder z.1 z.2 ρ)) ∧
      AEStronglyMeasurable
        (fun w : ParabolicPoint => pressureP3 η u c w.2 w.1)
        (volume.restrict (parabolicCylinder z.1 z.2 ρ)) ∧
      AEStronglyMeasurable
        (fun w : ParabolicPoint => pressureP4 η u c w.2 w.1)
        (volume.restrict (parabolicCylinder z.1 z.2 ρ)) ∧
      AEStronglyMeasurable
        (fun w : ParabolicPoint => pressureP5 η p w.2 w.1)
        (volume.restrict (parabolicCylinder z.1 z.2 ρ)) ∧
      AEStronglyMeasurable
        (fun w : ParabolicPoint => pressureP6 η p w.2 w.1)
        (volume.restrict (parabolicCylinder z.1 z.2 ρ)) ∧
      AEStronglyMeasurable
        (fun w : ParabolicPoint => pressureP7 η f w.2 w.1)
        (volume.restrict (parabolicCylinder z.1 z.2 ρ)) ∧
      AEStronglyMeasurable
        (fun w : ParabolicPoint => pressureP8 η f w.2 w.1)
        (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
  let B : Set Vec3 := vec3Ball z.1 ρ
  let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2
  let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ
  let c : ℝ → Vec3 := fun s => fun j =>
    MeasureTheory.average (volume.restrict B) (fun y => u (y, s) j)
  obtain ⟨Ω', J, hbox, hball, htime⟩ :=
    pressure_box_geometry hsol hρ hsub
  have hdata := hsol.2.2.2.2.2.1 Ω' J hbox
  have hu :=
    hdata.1
  have hp :=
    hdata.2.2.1
  have hf :=
    hdata.2.2.2.1
  have hST : spaceTimeSet Ω' T ⊆ spaceTimeSet Ω' J := by
    intro w hw
    exact ⟨hw.1, htime hw.2⟩
  have hp' :=
    hp.mono_measure (Measure.restrict_mono_set volume hST)
  have hcmeas (j : Fin 3) := @pressure_source_measurable_on_cylinder_hcmeas_1 u z ρ Ω' J hball
    htime hu j
  let cm : ℝ → Vec3 := fun s => fun j =>
    AEMeasurable.mk (fun t : ℝ => c t j) (hcmeas j) s
  have hcm := @pressure_source_measurable_on_cylinder_hcm_1 u z ρ hcmeas
  have hcmEq := @pressure_source_measurable_on_cylinder_hcmEq_2 u z ρ hcmeas
  let um : ParabolicPoint → Vec3 := hu.mk u
  let pm : ParabolicPoint → ℝ := hp.mk p
  let fm : ParabolicPoint → Vec3 := hf.mk f
  have hum : Measurable um := hu.measurable_mk
  have hpm : Measurable pm := hp.measurable_mk
  have hfm : Measurable fm := hf.measurable_mk
  have hBT : B ×ˢ T ⊆ spaceTimeSet Ω' J := by
    intro w hw
    exact ⟨hball hw.1, htime hw.2⟩
  have huBT := @pressure_source_measurable_on_cylinder_huBT_1 u z ρ Ω' J hu hBT
  have hpBT := @pressure_source_measurable_on_cylinder_hpBT_2 p z ρ Ω' J hp hBT
  have hfBT := @pressure_source_measurable_on_cylinder_hfBT_3 f z ρ Ω' J hf hBT
  have huSlices := @pressure_source_measurable_on_cylinder_huSlices_3 u z ρ Ω' J hu huBT
  have hpSlices := @pressure_source_measurable_on_cylinder_hpSlices_4 p z ρ Ω' J hp hpBT
  have hfSlices := @pressure_source_measurable_on_cylinder_hfSlices_5 f z ρ Ω' J hf hfBT
  have hηsupp : tsupport η ⊆ B := by
    dsimp [η, B]
    exact pressure_cutoff_support_subset_ball z.1 hρ
  have hηm : Measurable η := by
    dsimp [η]
    exact (mollifiedBallCutoff_smooth z.1 hρ).continuous.measurable
  have hηd (j : Fin 3) : Measurable (spatialDeriv η j) := by
    exact (contDiff_spatialDeriv_smooth
      (mollifiedBallCutoff_smooth z.1 hρ) j).continuous.measurable
  have hηdd (i j : Fin 3) : Measurable (mixedSecond η i j) := by
    exact (contDiff_mixedSecond_smooth
      (mollifiedBallCutoff_smooth z.1 hρ) i j).continuous.measurable
  have hηlap : Measurable (spatialLaplacian η) := by
    exact (contDiff_spatialLaplacian_smooth
      (mollifiedBallCutoff_smooth z.1 hρ)).continuous.measurable
  have hηddsupp (i j : Fin 3) : tsupport (mixedSecond η i j) ⊆ B := by
    exact (tsupport_fderiv_apply_subset ℝ (basisVec i)).trans
      ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηsupp)
  have hηdsupp (j : Fin 3) : tsupport (spatialDeriv η j) ⊆ B := by
    exact (tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηsupp
  have hηlapsupp := @pressure_source_measurable_on_cylinder_hηlapsupp_4 z ρ hρ hηdsupp
  have hsrc2 (i j : Fin 3) := @pressure_source_measurable_on_cylinder_hsrc2_2 u z ρ η c cm hcmEq
    um huSlices hηddsupp i j
  have hsrc3 (i j : Fin 3) := @pressure_source_measurable_on_cylinder_hsrc3_3 u z ρ η c cm hcmEq
    um huSlices hηdsupp i j
  have hsrc4 (i j : Fin 3) := @pressure_source_measurable_on_cylinder_hsrc4_4 u z ρ η c cm hcmEq
    um huSlices hηdsupp i j
  have hsrc5 := @pressure_source_measurable_on_cylinder_hsrc5_5 p z ρ η pm hpSlices hηlapsupp
  have hsrc6 (j : Fin 3) := @pressure_source_measurable_on_cylinder_hsrc6_6 p z ρ η pm hpSlices
    hηdsupp j
  have hsrc7 (j : Fin 3) := @pressure_source_measurable_on_cylinder_hsrc7_7 f z ρ η fm hfSlices
    hηsupp j
  have hsrc8 (j : Fin 3) := @pressure_source_measurable_on_cylinder_hsrc8_8 f z ρ η fm hfSlices
    hηdsupp j
  have hkernel0 : Measurable (fun w : ParabolicPoint × Vec3 =>
      -newtonianKernel (w.1.1 - w.2)) := by
    exact pressure_kernel_measurable.neg.comp
      ((measurable_fst.comp measurable_fst).sub measurable_snd)
  have hkernel1 (j : Fin 3) : Measurable (fun w : ParabolicPoint × Vec3 =>
      spatialDeriv newtonianKernel j (w.1.1 - w.2)) := by
    exact (pressure_kernel_derivative_measurable j).comp
      ((measurable_fst.comp measurable_fst).sub measurable_snd)
  have hIntegral {g : ParabolicPoint × Vec3 → ℝ} (hg : Measurable g) :=
    @pressure_source_measurable_on_cylinder_hIntegral_6 g hg
  let R2 : ParabolicPoint → ℝ := fun w =>
    ∑ i, ∑ j, ∫ y : Vec3,
      (-newtonianKernel (w.1 - y)) *
        (mixedSecond η i j y * pressureUTensor um cm (y, w.2) i j)
  let R3 : ParabolicPoint → ℝ := fun w =>
    ∑ i, ∑ j, ∫ y : Vec3,
      spatialDeriv newtonianKernel j (w.1 - y) *
        (pressureUTensor um cm (y, w.2) i j * spatialDeriv η i y)
  let R4 : ParabolicPoint → ℝ := fun w =>
    ∑ i, ∑ j, ∫ y : Vec3,
      spatialDeriv newtonianKernel i (w.1 - y) *
        (pressureUTensor um cm (y, w.2) i j * spatialDeriv η j y)
  let R5 : ParabolicPoint → ℝ := fun w =>
    -∫ y : Vec3, (-newtonianKernel (w.1 - y)) *
      (pm (y, w.2) * spatialLaplacian η y)
  let R6 : ParabolicPoint → ℝ := fun w =>
    -2 * ∑ j, ∫ y : Vec3,
      spatialDeriv newtonianKernel j (w.1 - y) *
        (spatialDeriv η j y * pm (y, w.2))
  let R7 : ParabolicPoint → ℝ := fun w =>
    -∑ j, ∫ y : Vec3, spatialDeriv newtonianKernel j (w.1 - y) *
      (η y * fm (y, w.2) j)
  let R8 : ParabolicPoint → ℝ := fun w =>
    -∑ j, ∫ y : Vec3, (-newtonianKernel (w.1 - y)) *
      (spatialDeriv η j y * fm (y, w.2) j)
  have hR2ij (i j : Fin 3) := @pressure_source_measurable_on_cylinder_hR2ij_5 u z ρ hρ Ω' J hu
    hcmeas hcm hum hηdd hkernel0 hIntegral i j
  have hR2 := @pressure_source_measurable_on_cylinder_hR2_6 u z ρ hρ Ω' J hu hcmeas hR2ij
  have hR3ij (i j : Fin 3) := @pressure_source_measurable_on_cylinder_hR3ij_7 u z ρ hρ Ω' J hu
    hcmeas hcm hum hηd hkernel1 hIntegral i j
  have hR3 := @pressure_source_measurable_on_cylinder_hR3_8 u z ρ hρ Ω' J hu hcmeas hR3ij
  have hR4ij (i j : Fin 3) := @pressure_source_measurable_on_cylinder_hR4ij_9 u z ρ hρ Ω' J hu
    hcmeas hcm hum hηd hkernel1 hIntegral i j
  have hR4 := @pressure_source_measurable_on_cylinder_hR4_10 u z ρ hρ Ω' J hu hcmeas hR4ij
  have hR5 := @pressure_source_measurable_on_cylinder_hR5_11 p z ρ hρ Ω' J hp hpm hηlap hkernel0
    hIntegral
  have hR6j (j : Fin 3) := @pressure_source_measurable_on_cylinder_hR6j_12 p z ρ hρ Ω' J hp hpm
    hηd hkernel1 hIntegral j
  have hR6 := @pressure_source_measurable_on_cylinder_hR6_13 p z ρ hρ Ω' J hp hR6j
  have hR7j (j : Fin 3) := @pressure_source_measurable_on_cylinder_hR7j_14 f z ρ hρ Ω' J hf hfm
    hηm hkernel1 hIntegral j
  have hR7 := @pressure_source_measurable_on_cylinder_hR7_15 f z ρ hρ Ω' J hf hR7j
  have hR8j (j : Fin 3) := @pressure_source_measurable_on_cylinder_hR8j_16 f z ρ hρ Ω' J hf hfm
    hηd hkernel0 hIntegral j
  have hR8 := @pressure_source_measurable_on_cylinder_hR8_17 f z ρ hρ Ω' J hf hR8j
  have hpot2 := @pressure_source_measurable_on_cylinder_hpot2_9 u z ρ η c cm um hsrc2
  have hpot3 := @pressure_source_measurable_on_cylinder_hpot3_10 u z ρ η c cm um hsrc3
  have hpot4 := @pressure_source_measurable_on_cylinder_hpot4_11 u z ρ η c cm um hsrc4
  have hpot5 := @pressure_source_measurable_on_cylinder_hpot5_18 p z ρ hρ Ω' J hp hsrc5
  have hpot6 := @pressure_source_measurable_on_cylinder_hpot6_12 p z ρ η pm hsrc6
  have hpot7 := @pressure_source_measurable_on_cylinder_hpot7_13 f z ρ η fm hsrc7
  have hpot8 := @pressure_source_measurable_on_cylinder_hpot8_14 f z ρ η fm hsrc8
  have hQ2 := @pressure_source_measurable_on_cylinder_hQ2_15 u z ρ η c R2 hpot2
  have hQ3 := @pressure_source_measurable_on_cylinder_hQ3_16 u z ρ η c R3 hpot3
  have hQ4 := @pressure_source_measurable_on_cylinder_hQ4_17 u z ρ η c R4 hpot4
  have hQ5 := @pressure_source_measurable_on_cylinder_hQ5_18 p z ρ η R5 hpot5
  have hQ6 := @pressure_source_measurable_on_cylinder_hQ6_19 p z ρ η R6 hpot6
  have hQ7 := @pressure_source_measurable_on_cylinder_hQ7_20 f z ρ η R7 hpot7
  have hQ8 := @pressure_source_measurable_on_cylinder_hQ8_21 f z ρ η R8 hpot8
  have hR8c : AEStronglyMeasurable R8
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) :=
    hR8.aestronglyMeasurable.restrict
  have hP7 := pressureP7_aestronglyMeasurable_on_cylinder hsol hρ hsub
  have hP8 : AEStronglyMeasurable
      (fun w : ParabolicPoint => pressureP8 η f w.2 w.1)
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
    exact hR8c.congr hQ8.symm
  have hP2 : AEStronglyMeasurable
      (fun w : ParabolicPoint => pressureP2 η u c w.2 w.1)
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
    exact hR2.aestronglyMeasurable.restrict.congr hQ2.symm
  have hP3 : AEStronglyMeasurable
      (fun w : ParabolicPoint => pressureP3 η u c w.2 w.1)
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
    exact hR3.aestronglyMeasurable.restrict.congr hQ3.symm
  have hP4 : AEStronglyMeasurable
      (fun w : ParabolicPoint => pressureP4 η u c w.2 w.1)
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
    exact hR4.aestronglyMeasurable.restrict.congr hQ4.symm
  have hP5 : AEStronglyMeasurable
      (fun w : ParabolicPoint => pressureP5 η p w.2 w.1)
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
    exact hR5.aestronglyMeasurable.restrict.congr hQ5.symm
  have hP6 : AEStronglyMeasurable
      (fun w : ParabolicPoint => pressureP6 η p w.2 w.1)
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
    exact hR6.aestronglyMeasurable.restrict.congr hQ6.symm
  let R1 : ParabolicPoint → ℝ := fun w =>
    η w.1 * pm (w.1, w.2) -
      (R2 w + R3 w + R4 w + R5 w + R6 w + R7 w + R8 w)
  have hR1 : AEMeasurable R1 volume := by
    exact ((hηm.comp measurable_fst).mul hpm).aemeasurable.sub
      ((((((hR2.add hR3).add hR4).add hR5).add hR6).add hR7).add hR8)
  have hpQ := @pressure_source_measurable_on_cylinder_hpQ_19 p z ρ Ω' J hp hpBT
  have hP1ae := @pressure_source_measurable_on_cylinder_hP1ae_20 u p f z ρ hρ Ω' J hu hp hf hp'
    hcmeas hQ2 hQ3 hQ4 hQ5 hQ6 hQ7 hQ8 hpQ
  have hP1 : AEStronglyMeasurable
      (fun w : ParabolicPoint => pressureP1 η u c p f w.2 w.1)
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
    exact hR1.aestronglyMeasurable.restrict.congr hP1ae.symm
  refine ⟨B, T, η, c, rfl, rfl, rfl, ?_, hP1, hP2, hP3, hP4, hP5, hP6,
    hP7, hP8⟩
  intro s
  rfl

end CKN.Core.Step3
