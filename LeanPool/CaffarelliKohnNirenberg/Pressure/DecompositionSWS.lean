/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SupportRestrict
public import LeanPool.CaffarelliKohnNirenberg.Pressure.DecompositionIdentity
public import LeanPool.CaffarelliKohnNirenberg.Pressure.DecompositionSWSBasic

/-!
# Decomposition SWS

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN

private lemma pressureP1_distributional_identity_hfInt_1 :
    ∀ {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
      (Ω' : Set Vec3) (s : ℝ),
      MemLp (ε := Vec3) (m0 := MeasureSpace.toMeasurableSpace) (fun (x : Vec3) => u (x, s))
            (2 : ℝ≥0∞) (Measure.restrict volume Ω') ∧
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace (fun (x : Vec3) => p (x, s))
              (Measure.restrict volume Ω') ∧
            @Integrable Vec3 _ _ _ MeasureSpace.toMeasurableSpace (fun (x : Vec3) => f (x, s))
              (Measure.restrict volume Ω') →
        ∀ (i : Fin (3 : ℕ)),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace (fun (x : Vec3) => f (x, s) i)
            (Measure.restrict volume Ω')
    := by
  intro u p f Ω' s hLp_s i
  apply hLp_s.2.2.mono
    ((ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable
      hLp_s.2.2.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖f (x, s) i‖ ≤ ‖f (x, s)‖
  rw [Pi.norm_def]
  simpa only [coe_nnnorm] using
    (NNReal.coe_le_coe.mpr
      (Finset.le_sup (s := (Finset.univ : Finset (Fin 3)))
        (f := fun b => ‖f (x, s) b‖₊) (Finset.mem_univ i)))

private lemma pressureP1_distributional_identity_huuScalar_2 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {_ : ParabolicPoint → Vec3} (Ω' : Set Vec3)
      (s : ℝ),
      (∀ (i : Fin (3 : ℕ)),
          MemLp (ε := ℝ) (m0 := MeasureSpace.toMeasurableSpace) (fun (x : Vec3) => u (x, s) i)
            (2 : ℝ≥0∞) (Measure.restrict volume Ω')) →
        ∀ {i j : Fin (3 : ℕ)} {g : Vec3 → ℝ},
          Continuous g →
            HasCompactSupport g →
              tsupport g ⊆ Ω' →
                IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                  (fun (x : Vec3) => u (x, s) i * u (x, s) j * g x) Ω volume
    := by
  intro Ω u f Ω' s huComp i j g hg hgc hgΩ
  exact (CKN.Foundation.Measure.integrable_mul_of_tsupport_subset
    ((huComp i).integrable_mul (huComp j)) hg hgc hgΩ).integrableOn

private lemma pressureP1_distributional_identity_hB_3 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {_ : ParabolicPoint → Vec3} {η : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) η →
        HasCompactSupport η →
          ∀ {c : ℝ → Vec3} {ψ : Vec3 → ℝ} (Ω' : Set Vec3),
            tsupport η ⊆ Ω' →
              ∀ (s : ℝ),
                Ω' ⊆ Ω →
                  (∀ {i j : Fin (3 : ℕ)} {g : Vec3 → ℝ},
                      Continuous g →
                        HasCompactSupport g →
                          tsupport g ⊆ Ω' →
                            IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                              (fun (x : Vec3) => pressureUTensor u c (x, s) i j * g x) Ω volume) →
                    (∀ {g : Fin (3 : ℕ) → Vec3 → ℝ},
                        (∀ (i : Fin (3 : ℕ)),
                            IntegrableOn (mα := MeasureSpace.toMeasurableSpace) (g i) Ω volume) →
                          IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                            (fun (x : Vec3) => ∑ i : Fin (3 : ℕ), g i x) Ω volume) →
                      (∀ (i j : Fin (3 : ℕ)), ContDiff ℝ (⊤ : ℕ∞) (mixedSecond ψ i j)) →
                        @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                          (fun (x : Vec3) =>
                            ∑ i : Fin (3 : ℕ),
                              ∑ j : Fin (3 : ℕ),
                                η x * pressureUTensor u c (x, s) i j * mixedSecond ψ i j x)
                          volume
    := by
  intro Ω u f η hη hηc c ψ Ω' hηΩ' s hΩ'sub hUScalar hfinite hψm
  have hBij (i j : Fin 3) : IntegrableOn
      (fun x => η x * pressureUTensor u c (x, s) i j * mixedSecond ψ i j x) Ω volume := by
    convert hUScalar (i := i) (j := j) (hη.mul (hψm i j)).continuous
      (hηc.mul_right (f' := mixedSecond ψ i j))
      ((tsupport_mul_subset_left (f := η) (g := mixedSecond ψ i j)).trans hηΩ') using 1
    funext x
    ring
  have hBΩ : tsupport (fun x => ∑ i, ∑ j,
      η x * pressureUTensor u c (x, s) i j * mixedSecond ψ i j x) ⊆ Ω := by
    apply decomposition_ts_support_sum₂_sws
    intro i j
    rw [show (fun x => η x * pressureUTensor u c (x, s) i j * mixedSecond ψ i j x) =
      (fun x => η x * (pressureUTensor u c (x, s) i j * mixedSecond ψ i j x)) by
        funext x; ring]
    exact ((tsupport_mul_subset_left (f := η) (g :=
      fun x => pressureUTensor u c (x, s) i j * mixedSecond ψ i j x)).trans hηΩ').trans hΩ'sub
  exact decomposition_full_of_on_sws (hfinite fun i => hfinite fun j => hBij i j) hBΩ

private lemma pressureP1_distributional_identity_hC6_4 :
    ∀ {Ω : Set Vec3} {p : ParabolicPoint → ℝ} {_ : ParabolicPoint → Vec3} {η : Vec3 → ℝ},
      tsupport η ⊆ Ω →
        ∀ {ψ : Vec3 → ℝ} (Ω' : Set Vec3),
          tsupport η ⊆ Ω' →
            ∀ (s : ℝ),
              (∀ {g : Vec3 → ℝ},
                  Continuous g →
                    HasCompactSupport g →
                      tsupport g ⊆ Ω' →
                        IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                          (fun (x : Vec3) => p (x, s) * g x) Ω volume) →
                (∀ {g : Fin (3 : ℕ) → Vec3 → ℝ},
                    (∀ (i : Fin (3 : ℕ)),
                        IntegrableOn (mα := MeasureSpace.toMeasurableSpace) (g i) Ω volume) →
                      IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                        (fun (x : Vec3) => ∑ i : Fin (3 : ℕ), g i x) Ω volume) →
                  (∀ (i : Fin (3 : ℕ)), ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv η i)) →
                    (∀ (i : Fin (3 : ℕ)), ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv ψ i)) →
                      (∀ (i : Fin (3 : ℕ)), HasCompactSupport (spatialDeriv η i)) →
                        @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                          (fun (x : Vec3) => spatialGradDot η ψ x * p (x, s)) volume
    := by
  intro Ω p f η hηΩ ψ Ω' hηΩ' s hpScalar hfinite hηd hψd hηdc
  have hsum : Integrable (fun x => ∑ j, p (x, s) *
      (spatialDeriv η j x * spatialDeriv ψ j x)) volume := by
    exact decomposition_full_of_on_sws (hfinite fun j =>
      hpScalar ((hηd j).mul (hψd j)).continuous
        ((hηdc j).mul_right (f' := spatialDeriv ψ j))
        ((tsupport_mul_subset_left (f := spatialDeriv η j) (g := spatialDeriv ψ j)).trans
          ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ')))
      (by
        apply decomposition_ts_support_sum₃_sws
        intro j
        exact (tsupport_mul_subset_right (f := fun x => p (x, s))
          (g := fun x => spatialDeriv η j x * spatialDeriv ψ j x)).trans
          ((tsupport_mul_subset_left (f := spatialDeriv η j)
            (g := spatialDeriv ψ j)).trans
            ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ)))
  exact hsum.congr (Filter.Eventually.of_forall fun x => by
    simp only [spatialGradDot]
    calc
      _ = p (x, s) * ∑ j, spatialDeriv η j x * spatialDeriv ψ j x := by
        rw [Finset.mul_sum]
      _ = _ := by ring)

private lemma pressureP1_distributional_identity_hF7_5 :
    ∀ {Ω : Set Vec3} {f : ParabolicPoint → Vec3} {η : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) η →
        HasCompactSupport η →
          tsupport η ⊆ Ω →
            ∀ {ψ : Vec3 → ℝ} (Ω' : Set Vec3),
              tsupport η ⊆ Ω' →
                ∀ (s : ℝ),
                  (∀ {i : Fin (3 : ℕ)} {g : Vec3 → ℝ},
                      Continuous g →
                        HasCompactSupport g →
                          tsupport g ⊆ Ω' →
                            IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                              (fun (x : Vec3) => f (x, s) i * g x) Ω volume) →
                    (∀ {g : Fin (3 : ℕ) → Vec3 → ℝ},
                        (∀ (i : Fin (3 : ℕ)),
                            IntegrableOn (mα := MeasureSpace.toMeasurableSpace) (g i) Ω volume) →
                          IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                            (fun (x : Vec3) => ∑ i : Fin (3 : ℕ), g i x) Ω volume) →
                      (∀ (i : Fin (3 : ℕ)), ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv ψ i)) →
                        @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                          (fun (x : Vec3) =>
                            ∑ i : Fin (3 : ℕ), f (x, s) i * (η x * spatialDeriv ψ i x))
                          volume
    := by
  intro Ω f η hη hηc hηΩ ψ Ω' hηΩ' s hfScalar hfinite hψd
  exact decomposition_full_of_on_sws (hfinite fun i =>
    hfScalar ((hη.mul (hψd i)).continuous)
      (hηc.mul_right (f' := spatialDeriv ψ i))
      ((tsupport_mul_subset_left (f := η) (g := spatialDeriv ψ i)).trans hηΩ'))
    (by
      apply decomposition_ts_support_sum₃_sws
      intro i
      exact (tsupport_mul_subset_right (f := fun x => f (x, s) i)
        (g := fun x => η x * spatialDeriv ψ i x)).trans
        ((tsupport_mul_subset_left (f := η) (g := spatialDeriv ψ i)).trans hηΩ))

private lemma pressureP1_distributional_identity_hF8_6 :
    ∀ {Ω : Set Vec3} {f : ParabolicPoint → Vec3} {η ψ : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ →
          tsupport ψ ⊆ Ω →
            ∀ (Ω' : Set Vec3),
              tsupport ψ ⊆ Ω' →
                ∀ (s : ℝ),
                  (∀ {i : Fin (3 : ℕ)} {g : Vec3 → ℝ},
                      Continuous g →
                        HasCompactSupport g →
                          tsupport g ⊆ Ω' →
                            IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                              (fun (x : Vec3) => f (x, s) i * g x) Ω volume) →
                    (∀ {g : Fin (3 : ℕ) → Vec3 → ℝ},
                        (∀ (i : Fin (3 : ℕ)),
                            IntegrableOn (mα := MeasureSpace.toMeasurableSpace) (g i) Ω volume) →
                          IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                            (fun (x : Vec3) => ∑ i : Fin (3 : ℕ), g i x) Ω volume) →
                      (∀ (i : Fin (3 : ℕ)), ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv η i)) →
                        @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                          (fun (x : Vec3) =>
                            ∑ i : Fin (3 : ℕ), f (x, s) i * (ψ x * spatialDeriv η i x))
                          volume
    := by
  intro Ω f η ψ hψ hψc hψΩ Ω' hψΩ' s hfScalar hfinite hηd
  exact decomposition_full_of_on_sws (hfinite fun i =>
    hfScalar ((hψ.mul (hηd i)).continuous)
      (hψc.mul_right (f' := spatialDeriv η i))
      ((tsupport_mul_subset_left (f := ψ) (g := spatialDeriv η i)).trans hψΩ'))
    (by
      apply decomposition_ts_support_sum₃_sws
      intro i
      exact (tsupport_mul_subset_right (f := fun x => f (x, s) i)
        (g := fun x => ψ x * spatialDeriv η i x)).trans
        ((tsupport_mul_subset_left (f := ψ) (g := spatialDeriv η i)).trans hψΩ))

private lemma pressureP1_distributional_identity_hP2term_7 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {_ : ParabolicPoint → Vec3} {η : Vec3 → ℝ}
      {c : ℝ → Vec3} {ψ : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) ψ →
        ∀ (Ω' : Set Vec3) (s : ℝ),
          Ω' ⊆ Ω →
            (∀ {i j : Fin (3 : ℕ)} {g : Vec3 → ℝ},
                Continuous g →
                  HasCompactSupport g →
                    tsupport g ⊆ Ω' →
                      IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                        (fun (x : Vec3) => pressureUTensor u c (x, s) i j * g x) Ω volume) →
              (∀ (i j : Fin (3 : ℕ)), ContDiff ℝ (⊤ : ℕ∞) (mixedSecond η i j)) →
                (∀ (i j : Fin (3 : ℕ)), HasCompactSupport (mixedSecond η i j)) →
                  (∀ (i j : Fin (3 : ℕ)), tsupport (mixedSecond η i j) ⊆ Ω') →
                    HasCompactSupport (spatialLaplacian ψ) →
                      (∀ (g : Vec3 → ℝ),
                          IntegrableOn (mα := MeasureSpace.toMeasurableSpace) g Ω volume →
                            tsupport g ⊆ Ω →
                              @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume) →
                        ∀ (i j : Fin (3 : ℕ)),
                          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                            (fun (x : Vec3) =>
                              pressureNewtonianPotential
                                  (fun (y : Vec3) =>
                                    mixedSecond η i j y * pressureUTensor u c (y, s) i j)
                                  x *
                                spatialLaplacian ψ x)
                            volume
    := by
  intro Ω u f η c ψ hψ Ω' s hΩ'sub hUScalar hηm hηmc hηmΩ hψLapc hSource i j
  have hon := hUScalar (i := i) (j := j) (hηm i j).continuous
    (hηmc i j) (hηmΩ i j)
  have hon' : IntegrableOn
      (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) Ω volume :=
    hon.congr (Filter.Eventually.of_forall fun y => by ring)
  have hs := hSource _ hon'
    ((tsupport_mul_subset_left (f := mixedSecond η i j)
      (g := fun y => pressureUTensor u c (y, s) i j)).trans
      ((hηmΩ i j).trans hΩ'sub))
  exact pressureNewtonianPotential_mul_smooth_integrable hs
    ((hηmc i j).mul_right (f' := fun y => pressureUTensor u c (y, s) i j))
    (contDiff_spatialLaplacian_smooth hψ) hψLapc

private lemma pressureP1_distributional_identity_hP5_8 :
    ∀ {Ω : Set Vec3} {p : ParabolicPoint → ℝ} {_ : ParabolicPoint → Vec3} {η : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) η →
        ∀ {ψ : Vec3 → ℝ},
          ContDiff ℝ (⊤ : ℕ∞) ψ →
            ∀ (Ω' : Set Vec3) (s : ℝ),
              Ω' ⊆ Ω →
                (∀ {g : Vec3 → ℝ},
                    Continuous g →
                      HasCompactSupport g →
                        tsupport g ⊆ Ω' →
                          IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                            (fun (x : Vec3) => p (x, s) * g x) Ω volume) →
                  tsupport (spatialLaplacian η) ⊆ Ω' →
                    HasCompactSupport (spatialLaplacian ψ) →
                      HasCompactSupport (spatialLaplacian η) →
                        (∀ (g : Vec3 → ℝ),
                            IntegrableOn (mα := MeasureSpace.toMeasurableSpace) g Ω volume →
                              tsupport g ⊆ Ω →
                                @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume) →
                          tsupport (spatialLaplacian η) ⊆ Ω' →
                            @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                              (fun (x : Vec3) => pressureP5 η p s x * spatialLaplacian ψ x) volume
    := by
  intro Ω p f η hη ψ hψ Ω' s hΩ'sub hpScalar hηLapΩ hψLapc hηLapc hSource hηLapΩ
  change Integrable (fun x => -pressureNewtonianPotential
    (fun y => p (y, s) * spatialLaplacian η y) x * spatialLaplacian ψ x) volume
  have hon := hpScalar (contDiff_spatialLaplacian_smooth hη).continuous
    hηLapc hηLapΩ
  convert (pressureNewtonianPotential_mul_smooth_integrable
    (hSource _ hon (((tsupport_mul_subset_right (f := fun y => p (y, s))
      (g := spatialLaplacian η)).trans hηLapΩ).trans hΩ'sub))
    ((hηLapc).mul_left (f := fun y => p (y, s)))
    (contDiff_spatialLaplacian_smooth hψ) hψLapc).neg using 1
  funext x
  simp only [Pi.neg_apply]
  ring

private lemma pressureP1_distributional_identity_hP6term_9 :
    ∀ {Ω : Set Vec3} {p : ParabolicPoint → ℝ} {_ : ParabolicPoint → Vec3} {η ψ : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) ψ →
        ∀ (Ω' : Set Vec3),
          tsupport η ⊆ Ω' →
            ∀ (s : ℝ),
              Ω' ⊆ Ω →
                (∀ {g : Vec3 → ℝ},
                    Continuous g →
                      HasCompactSupport g →
                        tsupport g ⊆ Ω' →
                          IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                            (fun (x : Vec3) => p (x, s) * g x) Ω volume) →
                  (∀ (i : Fin (3 : ℕ)), ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv η i)) →
                    (∀ (i : Fin (3 : ℕ)), HasCompactSupport (spatialDeriv η i)) →
                      HasCompactSupport (spatialLaplacian ψ) →
                        (∀ (g : Vec3 → ℝ),
                            IntegrableOn (mα := MeasureSpace.toMeasurableSpace) g Ω volume →
                              tsupport g ⊆ Ω →
                                @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume) →
                          ∀ (j : Fin (3 : ℕ)),
                            @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                              (fun (x : Vec3) =>
                                pressureNewtonianDerivativePotential j
                                    (fun (y : Vec3) => spatialDeriv η j y * p (y, s)) x *
                                  spatialLaplacian ψ x)
                              volume
    := by
  intro Ω p f η ψ hψ Ω' hηΩ' s hΩ'sub hpScalar hηd hηdc hψLapc hSource j
  have hon := hpScalar (hηd j).continuous (hηdc j)
    ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ')
  have hon' : IntegrableOn (fun y => spatialDeriv η j y * p (y, s)) Ω volume :=
    hon.congr (Filter.Eventually.of_forall fun y => by ring)
  exact pressureNewtonianDerivativePotential_mul_smooth_integrable
    (hSource _ hon' (((tsupport_mul_subset_left (f := spatialDeriv η j)
      (g := fun y => p (y, s))).trans
      ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ')).trans hΩ'sub))
    ((hηdc j).mul_right (f' := fun y => p (y, s)))
    (contDiff_spatialLaplacian_smooth hψ) hψLapc

private lemma pressureP1_distributional_identity_hP6_10 :
    ∀ {p : ParabolicPoint → ℝ} {η ψ : Vec3 → ℝ} (s : ℝ),
      (∀ (j : Fin (3 : ℕ)),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
            (fun (x : Vec3) =>
              pressureNewtonianDerivativePotential j
                  (fun (y : Vec3) => spatialDeriv η j y * p (y, s)) x *
                spatialLaplacian ψ x)
            volume) →
        @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
          (fun (x : Vec3) => pressureP6 η p s x * spatialLaplacian ψ x) volume
    := by
  intro p η ψ s hP6term
  change Integrable (fun x => (-2 : ℝ) *
    (∑ j, pressureNewtonianDerivativePotential j
      (fun y => spatialDeriv η j y * p (y, s)) x) * spatialLaplacian ψ x) volume
  have hs :=
    integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => hP6term j)
  convert hs.const_mul (-2) using 1
  funext x
  calc
    (-2 * ∑ j, pressureNewtonianDerivativePotential j
        (fun y => spatialDeriv η j y * p (y, s)) x) * spatialLaplacian ψ x =
        -2 * ((∑ j, pressureNewtonianDerivativePotential j
          (fun y => spatialDeriv η j y * p (y, s)) x) * spatialLaplacian ψ x) := by ring
    _ = -2 * ∑ j, pressureNewtonianDerivativePotential j
        (fun y => spatialDeriv η j y * p (y, s)) x * spatialLaplacian ψ x := by
          rw [Finset.sum_mul]

private lemma pressureP1_distributional_identity_hP7_11 :
    ∀ {f : ParabolicPoint → Vec3} {η ψ : Vec3 → ℝ} (s : ℝ),
      (∀ (j : Fin (3 : ℕ)),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
            (fun (x : Vec3) =>
              pressureNewtonianDerivativePotential j (fun (y : Vec3) => η y * f (y, s) j) x *
                spatialLaplacian ψ x)
            volume) →
        @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
          (fun (x : Vec3) => pressureP7 η f s x * spatialLaplacian ψ x) volume
    := by
  intro f η ψ s hP7term
  change Integrable (fun x => -(∑ j, pressureNewtonianDerivativePotential j
    (fun y => η y * f (y, s) j) x) * spatialLaplacian ψ x) volume
  have hs :=
    integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => hP7term j)
  convert hs.neg using 1
  funext x
  calc
    (-∑ j, pressureNewtonianDerivativePotential j
        (fun y => η y * f (y, s) j) x) * spatialLaplacian ψ x =
        -((∑ j, pressureNewtonianDerivativePotential j
          (fun y => η y * f (y, s) j) x) * spatialLaplacian ψ x) := by ring
    _ = -∑ j, pressureNewtonianDerivativePotential j
        (fun y => η y * f (y, s) j) x * spatialLaplacian ψ x := by
          rw [Finset.sum_mul]

private lemma pressureP1_distributional_identity_hP8term_12 :
    ∀ {Ω : Set Vec3} {f : ParabolicPoint → Vec3} {η ψ : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) ψ →
        ∀ (Ω' : Set Vec3),
          tsupport η ⊆ Ω' →
            ∀ (s : ℝ),
              Ω' ⊆ Ω →
                (∀ {i : Fin (3 : ℕ)} {g : Vec3 → ℝ},
                    Continuous g →
                      HasCompactSupport g →
                        tsupport g ⊆ Ω' →
                          IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                            (fun (x : Vec3) => f (x, s) i * g x) Ω volume) →
                  (∀ (i : Fin (3 : ℕ)), ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv η i)) →
                    (∀ (i : Fin (3 : ℕ)), HasCompactSupport (spatialDeriv η i)) →
                      HasCompactSupport (spatialLaplacian ψ) →
                        (∀ (g : Vec3 → ℝ),
                            IntegrableOn (mα := MeasureSpace.toMeasurableSpace) g Ω volume →
                              tsupport g ⊆ Ω →
                                @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume) →
                          ∀ (j : Fin (3 : ℕ)),
                            @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                              (fun (x : Vec3) =>
                                pressureNewtonianPotential
                                    (fun (y : Vec3) => spatialDeriv η j y * f (y, s) j) x *
                                  spatialLaplacian ψ x)
                              volume
    := by
  intro Ω f η ψ hψ Ω' hηΩ' s hΩ'sub hfScalar hηd hηdc hψLapc hSource j
  have hon := hfScalar (i := j) (hηd j).continuous (hηdc j)
    ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ')
  have hon' : IntegrableOn (fun y => spatialDeriv η j y * f (y, s) j) Ω volume :=
    hon.congr (Filter.Eventually.of_forall fun y => by ring)
  exact pressureNewtonianPotential_mul_smooth_integrable
    (hSource _ hon' (((tsupport_mul_subset_left (f := spatialDeriv η j)
      (g := fun y => f (y, s) j)).trans
      ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ')).trans hΩ'sub))
    ((hηdc j).mul_right (f' := fun y => f (y, s) j))
    (contDiff_spatialLaplacian_smooth hψ) hψLapc

private lemma pressureP1_distributional_identity_hP8_13 :
    ∀ {f : ParabolicPoint → Vec3} {η ψ : Vec3 → ℝ} (s : ℝ),
      (∀ (j : Fin (3 : ℕ)),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
            (fun (x : Vec3) =>
              pressureNewtonianPotential (fun (y : Vec3) => spatialDeriv η j y * f (y, s) j) x *
                spatialLaplacian ψ x)
            volume) →
        @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
          (fun (x : Vec3) => pressureP8 η f s x * spatialLaplacian ψ x) volume
    := by
  intro f η ψ s hP8term
  change Integrable (fun x => -(∑ j, pressureNewtonianPotential
    (fun y => spatialDeriv η j y * f (y, s) j) x) * spatialLaplacian ψ x) volume
  have hs :=
    integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => hP8term j)
  convert hs.neg using 1
  funext x
  calc
    (-∑ j, pressureNewtonianPotential
        (fun y => spatialDeriv η j y * f (y, s) j) x) * spatialLaplacian ψ x =
        -((∑ j, pressureNewtonianPotential
          (fun y => spatialDeriv η j y * f (y, s) j) x) * spatialLaplacian ψ x) := by ring
    _ = -∑ j, pressureNewtonianPotential
        (fun y => spatialDeriv η j y * f (y, s) j) x * spatialLaplacian ψ x := by
          rw [Finset.sum_mul]

private lemma pressureP1_distributional_identity_hC6Ω_14 :
    ∀ {Ω : Set Vec3} {p : ParabolicPoint → ℝ} {_ : ParabolicPoint → Vec3} {η ψ : Vec3 → ℝ}
      (Ω' : Set Vec3),
      tsupport η ⊆ Ω' →
        ∀ (s : ℝ),
          Ω' ⊆ Ω → (tsupport (α := ℝ) fun (x : Vec3) => spatialGradDot η ψ x * p (x, s)) ⊆ Ω
    := by
  intro Ω p f η ψ Ω' hηΩ' s hΩ'sub
  rw [show (fun x => spatialGradDot η ψ x * p (x, s)) =
    (fun x => ∑ j, p (x, s) * (spatialDeriv η j x * spatialDeriv ψ j x)) by
      funext x
      simp only [spatialGradDot]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring]
  apply decomposition_ts_support_sum₃_sws
  intro j
  exact (((tsupport_mul_subset_right
    (f := fun x => p (x, s))
    (g := fun x => spatialDeriv η j x * spatialDeriv ψ j x)).trans
    ((tsupport_mul_subset_left (f := spatialDeriv η j)
      (g := spatialDeriv ψ j)).trans
      ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ'))).trans hΩ'sub)

private lemma pressureP1_distributional_identity_hC6Int_15 :
    ∀ {Ω : Set Vec3} {p : ParabolicPoint → ℝ} {_ : ParabolicPoint → Vec3} {η ψ : Vec3 → ℝ}
      (Ω' : Set Vec3),
      tsupport η ⊆ Ω' →
        ∀ (s : ℝ),
          Ω' ⊆ Ω →
            (∀ {g : Vec3 → ℝ},
                Continuous g →
                  HasCompactSupport g →
                    tsupport g ⊆ Ω' →
                      IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                        (fun (x : Vec3) => p (x, s) * g x) Ω volume) →
              (∀ (i : Fin (3 : ℕ)), ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv η i)) →
                (∀ (i : Fin (3 : ℕ)), ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv ψ i)) →
                  (∀ (i : Fin (3 : ℕ)), HasCompactSupport (spatialDeriv η i)) →
                    (∀ (g : Vec3 → ℝ),
                        IntegrableOn (mα := MeasureSpace.toMeasurableSpace) g Ω volume →
                          tsupport g ⊆ Ω →
                            @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume) →
                      ∀ (j : Fin (3 : ℕ)),
                        @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                          (fun (y : Vec3) => p (y, s) * (spatialDeriv η j y * spatialDeriv ψ j y))
                          volume
    := by
  intro Ω p f η ψ Ω' hηΩ' s hΩ'sub hpScalar hηd hψd hηdc hSource j
  have hon := hpScalar ((hηd j).mul (hψd j)).continuous
    ((hηdc j).mul_right (f' := spatialDeriv ψ j))
    ((tsupport_mul_subset_left (f := spatialDeriv η j)
      (g := spatialDeriv ψ j)).trans
      ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ'))
  exact hSource _ hon
    ((((tsupport_mul_subset_right (f := fun y => p (y, s))
      (g := fun y => spatialDeriv η j y * spatialDeriv ψ j y)).trans
      ((tsupport_mul_subset_left (f := spatialDeriv η j)
        (g := spatialDeriv ψ j)).trans
        ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ'))).trans hΩ'sub))

private lemma pressureP1_distributional_identity_hPair2_16 :
    ∀ {u : ParabolicPoint → Vec3} {η : Vec3 → ℝ} {c : ℝ → Vec3} {ψ : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ →
          ∀ (s : ℝ),
            (∀ (i j : Fin (3 : ℕ)),
                @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                  (fun (x : Vec3) => pressureUTensor u c (x, s) i j * (mixedSecond η i j x * ψ x))
                  volume) →
              (∀ {G : Fin (3 : ℕ) → Fin (3 : ℕ) → Vec3 → ℝ},
                  (∀ (i j : Fin (3 : ℕ)),
                      @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace (G i j) volume) →
                    Eq (α := ℝ)
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                        ∑ i : Fin (3 : ℕ), ∑ j : Fin (3 : ℕ), G i j x)
                      (∑ i : Fin (3 : ℕ),
                        ∑ j : Fin (3 : ℕ),
                          @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                            G i j x)) →
                (∀ (i j : Fin (3 : ℕ)),
                    @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                      (fun (y : Vec3) => mixedSecond η i j y * pressureUTensor u c (y, s) i j)
                      volume) →
                  (∀ (i j : Fin (3 : ℕ)),
                      HasCompactSupport (β := ℝ) fun (y : Vec3) =>
                        mixedSecond η i j y * pressureUTensor u c (y, s) i j) →
                    Eq (α := ℝ)
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                        pressureP2 η u c s x * spatialLaplacian ψ x)
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                        ∑ i : Fin (3 : ℕ),
                          ∑ j : Fin (3 : ℕ),
                            pressureUTensor u c (x, s) i j * (mixedSecond η i j x * ψ x))
    := by
  intro u η c ψ hψ hψc s hU1 integral_sum₂ hP2Int hP2Supp
  calc
    _ = ∑ i, ∑ j, ∫ y, mixedSecond η i j y *
        pressureUTensor u c (y, s) i j * ψ y :=
      pressureP2_distributional_pairing hP2Int hP2Supp hψ hψc
    _ = ∑ i, ∑ j, ∫ y, pressureUTensor u c (y, s) i j *
        (mixedSecond η i j y * ψ y) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    _ = _ := (integral_sum₂ (fun i j => hU1 i j)).symm

private lemma pressureP1_distributional_identity_hPair3_17 :
    ∀ {u : ParabolicPoint → Vec3} {η : Vec3 → ℝ} {c : ℝ → Vec3} {ψ : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ →
          ∀ (s : ℝ),
            (∀ (i j : Fin (3 : ℕ)),
                @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                  (fun (x : Vec3) =>
                    pressureUTensor u c (x, s) i j * (spatialDeriv η i x * spatialDeriv ψ j x))
                  volume) →
              (∀ {G : Fin (3 : ℕ) → Fin (3 : ℕ) → Vec3 → ℝ},
                  (∀ (i j : Fin (3 : ℕ)),
                      @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace (G i j) volume) →
                    Eq (α := ℝ)
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                        ∑ i : Fin (3 : ℕ), ∑ j : Fin (3 : ℕ), G i j x)
                      (∑ i : Fin (3 : ℕ),
                        ∑ j : Fin (3 : ℕ),
                          @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                            G i j x)) →
                (∀ (i j : Fin (3 : ℕ)),
                    @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                      (fun (y : Vec3) => pressureUTensor u c (y, s) i j * spatialDeriv η i y)
                      volume) →
                  (∀ (i j : Fin (3 : ℕ)),
                      HasCompactSupport (β := ℝ) fun (y : Vec3) =>
                        pressureUTensor u c (y, s) i j * spatialDeriv η i y) →
                    Eq (α := ℝ)
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                        pressureP3 η u c s x * spatialLaplacian ψ x)
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                        ∑ i : Fin (3 : ℕ),
                          ∑ j : Fin (3 : ℕ),
                            pressureUTensor u c (x, s) i j *
                              (spatialDeriv η i x * spatialDeriv ψ j x))
    := by
  intro u η c ψ hψ hψc s hU2 integral_sum₂ hP3Int hP3Supp
  calc
    _ = ∑ i, ∑ j, ∫ y, pressureUTensor u c (y, s) i j *
        spatialDeriv η i y * CKN.spatialDeriv ψ j y :=
      pressureP3_distributional_pairing hP3Int hP3Supp hψ hψc
    _ = ∑ i, ∑ j, ∫ y, pressureUTensor u c (y, s) i j *
        (spatialDeriv η i y * spatialDeriv ψ j y) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    _ = _ := (integral_sum₂ (fun i j => hU2 i j)).symm

private lemma pressureP1_distributional_identity_hPair4_18 :
    ∀ {u : ParabolicPoint → Vec3} {η : Vec3 → ℝ} {c : ℝ → Vec3} {ψ : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ →
          ∀ (s : ℝ),
            (∀ (i j : Fin (3 : ℕ)),
                @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                  (fun (x : Vec3) =>
                    pressureUTensor u c (x, s) i j * (spatialDeriv η j x * spatialDeriv ψ i x))
                  volume) →
              (∀ {G : Fin (3 : ℕ) → Fin (3 : ℕ) → Vec3 → ℝ},
                  (∀ (i j : Fin (3 : ℕ)),
                      @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace (G i j) volume) →
                    Eq (α := ℝ)
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                        ∑ i : Fin (3 : ℕ), ∑ j : Fin (3 : ℕ), G i j x)
                      (∑ i : Fin (3 : ℕ),
                        ∑ j : Fin (3 : ℕ),
                          @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                            G i j x)) →
                (∀ (i j : Fin (3 : ℕ)),
                    @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                      (fun (y : Vec3) => pressureUTensor u c (y, s) i j * spatialDeriv η j y)
                      volume) →
                  (∀ (i j : Fin (3 : ℕ)),
                      HasCompactSupport (β := ℝ) fun (y : Vec3) =>
                        pressureUTensor u c (y, s) i j * spatialDeriv η j y) →
                    Eq (α := ℝ)
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                        pressureP4 η u c s x * spatialLaplacian ψ x)
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                        ∑ i : Fin (3 : ℕ),
                          ∑ j : Fin (3 : ℕ),
                            pressureUTensor u c (x, s) i j *
                              (spatialDeriv η j x * spatialDeriv ψ i x))
    := by
  intro u η c ψ hψ hψc s hU3 integral_sum₂ hP4Int hP4Supp
  calc
    _ = ∑ i, ∑ j, ∫ y, pressureUTensor u c (y, s) i j *
        spatialDeriv η j y * CKN.spatialDeriv ψ i y :=
      pressureP4_distributional_pairing hP4Int hP4Supp hψ hψc
    _ = ∑ i, ∑ j, ∫ y, pressureUTensor u c (y, s) i j *
        (spatialDeriv η j y * spatialDeriv ψ i y) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    _ = _ := (integral_sum₂ (fun i j => hU3 i j)).symm

private lemma pressureP1_distributional_identity_hPair6_19 :
    ∀ {p : ParabolicPoint → ℝ} {η ψ : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ →
          ∀ (s : ℝ),
            (∀ {G : Fin (3 : ℕ) → Vec3 → ℝ},
                (∀ (j : Fin (3 : ℕ)),
                    @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace (G j) volume) →
                  Eq (α := ℝ)
                    (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                      ∑ j : Fin (3 : ℕ), G j x)
                    (∑ j : Fin (3 : ℕ),
                      @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                        G j x)) →
              (∀ (j : Fin (3 : ℕ)),
                  @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                    (fun (y : Vec3) => spatialDeriv η j y * p (y, s)) volume) →
                (∀ (j : Fin (3 : ℕ)),
                    HasCompactSupport (β := ℝ) fun (y : Vec3) => spatialDeriv η j y * p (y, s)) →
                  (∀ (j : Fin (3 : ℕ)),
                      @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                        (fun (y : Vec3) => p (y, s) * (spatialDeriv η j y * spatialDeriv ψ j y))
                        volume) →
                    (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                        pressureP6 η p s x * spatialLaplacian ψ x) =
                      (-2 : ℝ) *
                        @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                          spatialGradDot η ψ x * p (x, s)
    := by
  intro p η ψ hψ hψc s integral_sum₁ hP6Int hP6Supp hC6Int
  calc
    _ = -2 * ∑ j, ∫ y, spatialDeriv η j y * p (y, s) *
        CKN.spatialDeriv ψ j y :=
      pressureP6_distributional_pairing hP6Int hP6Supp hψ hψc
    _ = -2 * ∫ y, ∑ j, p (y, s) *
        (spatialDeriv η j y * spatialDeriv ψ j y) := by
      congr 1
      rw [integral_sum₁ (G := fun j y =>
        p (y, s) * (spatialDeriv η j y * spatialDeriv ψ j y))
        (fun j => hC6Int j)]
      apply Finset.sum_congr rfl
      intro j hj
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [spatialGradDot]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring

private lemma pressureP1_distributional_identity_hPair7_20 :
    ∀ {f : ParabolicPoint → Vec3} {η ψ : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ →
          ∀ (s : ℝ),
            (∀ {G : Fin (3 : ℕ) → Vec3 → ℝ},
                (∀ (j : Fin (3 : ℕ)),
                    @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace (G j) volume) →
                  Eq (α := ℝ)
                    (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                      ∑ j : Fin (3 : ℕ), G j x)
                    (∑ j : Fin (3 : ℕ),
                      @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                        G j x)) →
              (∀ (j : Fin (3 : ℕ)),
                  @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                    (fun (y : Vec3) => η y * f (y, s) j) volume) →
                (∀ (j : Fin (3 : ℕ)),
                    HasCompactSupport (β := ℝ) fun (y : Vec3) => η y * f (y, s) j) →
                  (∀ (j : Fin (3 : ℕ)),
                      @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                        (fun (y : Vec3) => f (y, s) j * (η y * spatialDeriv ψ j y)) volume) →
                    Eq (α := ℝ)
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                        pressureP7 η f s x * spatialLaplacian ψ x)
                      (-@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                          ∑ i : Fin (3 : ℕ), f (x, s) i * (η x * spatialDeriv ψ i x))
    := by
  intro f η ψ hψ hψc s integral_sum₁ hP7Int hP7Supp hF7PairInt
  calc
    _ = -∑ j, ∫ y, η y * f (y, s) j * CKN.spatialDeriv ψ j y :=
      pressureP7_distributional_pairing hP7Int hP7Supp hψ hψc
    _ = -∫ y, ∑ j, f (y, s) j * (η y * spatialDeriv ψ j y) := by
      rw [integral_sum₁ (G := fun j y =>
        f (y, s) j * (η y * spatialDeriv ψ j y))
        (fun j => hF7PairInt j)]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      apply integral_congr_ae
      filter_upwards [] with y
      ring

private lemma pressureP1_distributional_identity_hPair8_21 :
    ∀ {f : ParabolicPoint → Vec3} {η ψ : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ →
          ∀ (s : ℝ),
            (∀ {G : Fin (3 : ℕ) → Vec3 → ℝ},
                (∀ (j : Fin (3 : ℕ)),
                    @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace (G j) volume) →
                  Eq (α := ℝ)
                    (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                      ∑ j : Fin (3 : ℕ), G j x)
                    (∑ j : Fin (3 : ℕ),
                      @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                        G j x)) →
              (∀ (j : Fin (3 : ℕ)),
                  @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                    (fun (y : Vec3) => spatialDeriv η j y * f (y, s) j) volume) →
                (∀ (j : Fin (3 : ℕ)),
                    HasCompactSupport (β := ℝ) fun (y : Vec3) => spatialDeriv η j y * f (y, s) j) →
                  (∀ (j : Fin (3 : ℕ)),
                      @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                        (fun (y : Vec3) => f (y, s) j * (ψ y * spatialDeriv η j y)) volume) →
                    Eq (α := ℝ)
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                        pressureP8 η f s x * spatialLaplacian ψ x)
                      (-@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                          ∑ i : Fin (3 : ℕ), f (x, s) i * (ψ x * spatialDeriv η i x))
    := by
  intro f η ψ hψ hψc s integral_sum₁ hP8Int hP8Supp hF8PairInt
  calc
    _ = -∑ j, ∫ y, spatialDeriv η j y * f (y, s) j * ψ y :=
      pressureP8_distributional_pairing hP8Int hP8Supp hψ hψc
    _ = -∫ y, ∑ j, f (y, s) j * (ψ y * spatialDeriv η j y) := by
      rw [integral_sum₁ (G := fun j y =>
        f (y, s) j * (ψ y * spatialDeriv η j y))
        (fun j => hF8PairInt j)]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      apply integral_congr_ae
      filter_upwards [] with y
      ring

private lemma pressureP1_distributional_identity_hpScalar_1 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3} (Ω' : Set Vec3) (s : ℝ),
      MemLp (ε := Vec3) (m0 := MeasureSpace.toMeasurableSpace) (fun (x : Vec3) => u (x, s))
            (2 : ℝ≥0∞) (Measure.restrict volume Ω') ∧
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace (fun (x : Vec3) => p (x, s))
              (Measure.restrict volume Ω') ∧
            @Integrable Vec3 _ _ _ MeasureSpace.toMeasurableSpace (fun (x : Vec3) => f (x, s))
              (Measure.restrict volume Ω') →
        ∀ {g : Vec3 → ℝ},
          Continuous g →
            HasCompactSupport g →
              tsupport g ⊆ Ω' →
                IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                  (fun (x : Vec3) => p (x, s) * g x) Ω volume
    := by
  intro Ω u p f Ω' s hLp_s g hg hgc hgΩ
  exact (CKN.Foundation.Measure.integrable_mul_of_tsupport_subset
    hLp_s.2.1 hg hgc hgΩ).integrableOn

private lemma pressureP1_distributional_identity_huScalar_2 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {_ : ParabolicPoint → Vec3} (Ω' : Set Vec3)
      (s : ℝ),
      (∀ (i : Fin (3 : ℕ)),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace (fun (x : Vec3) => u (x, s) i)
            (Measure.restrict volume Ω')) →
        ∀ {i : Fin (3 : ℕ)} {g : Vec3 → ℝ},
          Continuous g →
            HasCompactSupport g →
              tsupport g ⊆ Ω' →
                IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                  (fun (x : Vec3) => u (x, s) i * g x) Ω volume
    := by
  intro Ω u f Ω' s huInt i g hg hgc hgΩ
  exact (CKN.Foundation.Measure.integrable_mul_of_tsupport_subset
    (huInt i) hg hgc hgΩ).integrableOn

private lemma pressureP1_distributional_identity_hfScalar_3 :
    ∀ {Ω : Set Vec3} {f : ParabolicPoint → Vec3} (Ω' : Set Vec3) (s : ℝ),
      (∀ (i : Fin (3 : ℕ)),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace (fun (x : Vec3) => f (x, s) i)
            (Measure.restrict volume Ω')) →
        ∀ {i : Fin (3 : ℕ)} {g : Vec3 → ℝ},
          Continuous g →
            HasCompactSupport g →
              tsupport g ⊆ Ω' →
                IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                  (fun (x : Vec3) => f (x, s) i * g x) Ω volume
    := by
  intro Ω f Ω' s hfInt i g hg hgc hgΩ
  exact (CKN.Foundation.Measure.integrable_mul_of_tsupport_subset
    (hfInt i) hg hgc hgΩ).integrableOn

private lemma pressureP1_distributional_identity_hUScalar_4 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} (Ω' : Set Vec3) (s : ℝ),
      (∀ {i : Fin (3 : ℕ)} {g : Vec3 → ℝ},
          Continuous g →
            HasCompactSupport g →
              tsupport g ⊆ Ω' →
                IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                  (fun (x : Vec3) => u (x, s) i * g x) Ω volume) →
        (∀ {i j : Fin (3 : ℕ)} {g : Vec3 → ℝ},
            Continuous g →
              HasCompactSupport g →
                tsupport g ⊆ Ω' →
                  IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                    (fun (x : Vec3) => u (x, s) i * u (x, s) j * g x) Ω volume) →
          ∀ {i j : Fin (3 : ℕ)} {g : Vec3 → ℝ},
            Continuous g →
              HasCompactSupport g →
                tsupport g ⊆ Ω' →
                  IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                    (fun (x : Vec3) => pressureUTensor u c (x, s) i j * g x) Ω volume
    := by
  intro Ω u c Ω' s huScalar huuScalar i j g hg hgc hgΩ
  have hu := huuScalar (i := i) (j := j) hg hgc hgΩ
  have huc := huScalar (i := i) hg hgc hgΩ
  have hs : IntegrableOn (fun x => -(u (x, s) i * u (x, s) j * g x) +
      c s j * (u (x, s) i * g x)) Ω volume := hu.neg.add (huc.const_mul (c s j))
  exact hs.congr (Filter.Eventually.of_forall fun x => by
    simp only [pressureUTensor]
    ring)

private lemma pressureP1_distributional_identity_hηLapΩ_5 :
    ∀ {η : Vec3 → ℝ} (Ω' : Set Vec3), tsupport η ⊆ Ω' → tsupport (spatialLaplacian η) ⊆ Ω'
    := by
  intro η Ω' hηΩ'
  change tsupport (fun x => ∑ i : Fin 3,
    spatialDeriv (spatialDeriv η i) i x) ⊆ Ω'
  apply decomposition_ts_support_sum₃_sws
  intro i
  exact (tsupport_fderiv_apply_subset ℝ (basisVec i)).trans
    ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hηΩ')

private lemma pressureP1_distributional_identity_hAon_6 :
    ∀ {Ω : Set Vec3} {p : ParabolicPoint → ℝ} {_ : ParabolicPoint → Vec3} {η : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) η →
        HasCompactSupport η →
          ∀ {ψ : Vec3 → ℝ},
            ContDiff ℝ (⊤ : ℕ∞) ψ →
              ∀ (Ω' : Set Vec3),
                tsupport η ⊆ Ω' →
                  ∀ (s : ℝ),
                    (∀ {g : Vec3 → ℝ},
                        Continuous g →
                          HasCompactSupport g →
                            tsupport g ⊆ Ω' →
                              IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                                (fun (x : Vec3) => p (x, s) * g x) Ω volume) →
                      IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                        (fun (x : Vec3) => η x * p (x, s) * spatialLaplacian ψ x) Ω volume
    := by
  intro Ω p f η hη hηc ψ hψ Ω' hηΩ' s hpScalar
  convert hpScalar (hη.mul (contDiff_spatialLaplacian_smooth hψ)).continuous
    (hηc.mul_right (f' := spatialLaplacian ψ))
    ((tsupport_mul_subset_left (f := η) (g := spatialLaplacian ψ)).trans hηΩ') using 1
  funext x
  ring

private lemma pressureP1_distributional_identity_hU0_7 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {_ : ParabolicPoint → Vec3} {η : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) η →
        HasCompactSupport η →
          ∀ {c : ℝ → Vec3} {ψ : Vec3 → ℝ} (Ω' : Set Vec3),
            tsupport η ⊆ Ω' →
              ∀ (s : ℝ),
                Ω' ⊆ Ω →
                  (∀ {i j : Fin (3 : ℕ)} {g : Vec3 → ℝ},
                      Continuous g →
                        HasCompactSupport g →
                          tsupport g ⊆ Ω' →
                            IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                              (fun (x : Vec3) => pressureUTensor u c (x, s) i j * g x) Ω volume) →
                    (∀ (i j : Fin (3 : ℕ)), ContDiff ℝ (⊤ : ℕ∞) (mixedSecond ψ i j)) →
                      (∀ (g : Vec3 → ℝ),
                          IntegrableOn (mα := MeasureSpace.toMeasurableSpace) g Ω volume →
                            tsupport g ⊆ Ω →
                              @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume) →
                        ∀ (i j : Fin (3 : ℕ)),
                          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                            (fun (x : Vec3) =>
                              pressureUTensor u c (x, s) i j * (η x * mixedSecond ψ i j x))
                            volume
    := by
  intro Ω u f η hη hηc c ψ Ω' hηΩ' s hΩ'sub hUScalar hψm hSource i j
  have hU0Ω : tsupport (fun x => pressureUTensor u c (x, s) i j *
    (η x * mixedSecond ψ i j x)) ⊆ Ω := by
    exact ((tsupport_mul_subset_right (f := fun x => pressureUTensor u c (x, s) i j)
      (g := fun x => η x * mixedSecond ψ i j x)).trans
      ((tsupport_mul_subset_left (f := η) (g := mixedSecond ψ i j)).trans hηΩ')).trans hΩ'sub
  exact hSource _ (hUScalar (i := i) (j := j) (hη.mul (hψm i j)).continuous
    (hηc.mul_right (f' := mixedSecond ψ i j))
    ((tsupport_mul_subset_left (f := η) (g := mixedSecond ψ i j)).trans hηΩ')) hU0Ω

private lemma pressureP1_distributional_identity_hU1_8 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {_ : ParabolicPoint → Vec3} {η : Vec3 → ℝ}
      {c : ℝ → Vec3} {ψ : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ →
          ∀ (Ω' : Set Vec3),
            tsupport ψ ⊆ Ω' →
              ∀ (s : ℝ),
                Ω' ⊆ Ω →
                  (∀ {i j : Fin (3 : ℕ)} {g : Vec3 → ℝ},
                      Continuous g →
                        HasCompactSupport g →
                          tsupport g ⊆ Ω' →
                            IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                              (fun (x : Vec3) => pressureUTensor u c (x, s) i j * g x) Ω volume) →
                    (∀ (i j : Fin (3 : ℕ)), ContDiff ℝ (⊤ : ℕ∞) (mixedSecond η i j)) →
                      (∀ (g : Vec3 → ℝ),
                          IntegrableOn (mα := MeasureSpace.toMeasurableSpace) g Ω volume →
                            tsupport g ⊆ Ω →
                              @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume) →
                        ∀ (i j : Fin (3 : ℕ)),
                          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                            (fun (x : Vec3) =>
                              pressureUTensor u c (x, s) i j * (mixedSecond η i j x * ψ x))
                            volume
    := by
  intro Ω u f η c ψ hψ hψc Ω' hψΩ' s hΩ'sub hUScalar hηm hSource i j
  have hU1Ω : tsupport (fun x => pressureUTensor u c (x, s) i j *
      (mixedSecond η i j x * ψ x)) ⊆ Ω := by
    exact ((tsupport_mul_subset_right (f := fun x => pressureUTensor u c (x, s) i j)
      (g := fun x => mixedSecond η i j x * ψ x)).trans
      ((tsupport_mul_subset_right (f := mixedSecond η i j) (g := ψ)).trans hψΩ')).trans hΩ'sub
  exact hSource _ (hUScalar (i := i) (j := j) ((hηm i j).mul hψ).continuous
    (hψc.mul_left (f := mixedSecond η i j))
    ((tsupport_mul_subset_right (f := mixedSecond η i j) (g := ψ)).trans hψΩ')) hU1Ω

private lemma pressureP1_distributional_identity_hU3_9 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {_ : ParabolicPoint → Vec3} {η : Vec3 → ℝ},
      tsupport η ⊆ Ω →
        ∀ {c : ℝ → Vec3} {ψ : Vec3 → ℝ} (Ω' : Set Vec3),
          tsupport η ⊆ Ω' →
            ∀ (s : ℝ),
              (∀ {i j : Fin (3 : ℕ)} {g : Vec3 → ℝ},
                  Continuous g →
                    HasCompactSupport g →
                      tsupport g ⊆ Ω' →
                        IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                          (fun (x : Vec3) => pressureUTensor u c (x, s) i j * g x) Ω volume) →
                (∀ (i : Fin (3 : ℕ)), ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv η i)) →
                  (∀ (i : Fin (3 : ℕ)), ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv ψ i)) →
                    (∀ (i : Fin (3 : ℕ)), HasCompactSupport (spatialDeriv η i)) →
                      (∀ (g : Vec3 → ℝ),
                          IntegrableOn (mα := MeasureSpace.toMeasurableSpace) g Ω volume →
                            tsupport g ⊆ Ω →
                              @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume) →
                        ∀ (i j : Fin (3 : ℕ)),
                          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                            (fun (x : Vec3) =>
                              pressureUTensor u c (x, s) i j *
                                (spatialDeriv η j x * spatialDeriv ψ i x))
                            volume
    := by
  intro Ω u f η hηΩ c ψ Ω' hηΩ' s hUScalar hηd hψd hηdc hSource i j
  exact hSource _ (hUScalar (i := i) (j := j) ((hηd j).mul (hψd i)).continuous
    ((hηdc j).mul_right (f' := spatialDeriv ψ i))
    ((tsupport_mul_subset_left (f := spatialDeriv η j) (g := spatialDeriv ψ i)).trans
      ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ')))
    ((tsupport_mul_subset_right (f := fun x => pressureUTensor u c (x, s) i j)
      (g := fun x => spatialDeriv η j x * spatialDeriv ψ i x)).trans
      ((tsupport_mul_subset_left (f := spatialDeriv η j) (g := spatialDeriv ψ i)).trans
        ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ)))

private lemma pressureP1_distributional_identity_hC5_10 :
    ∀ {Ω : Set Vec3} {p : ParabolicPoint → ℝ} {_ : ParabolicPoint → Vec3} {η : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) η →
        HasCompactSupport η →
          ∀ {ψ : Vec3 → ℝ},
            ContDiff ℝ (⊤ : ℕ∞) ψ →
              HasCompactSupport ψ →
                tsupport ψ ⊆ Ω →
                  ∀ (Ω' : Set Vec3),
                    tsupport ψ ⊆ Ω' →
                      ∀ (s : ℝ),
                        (∀ {g : Vec3 → ℝ},
                            Continuous g →
                              HasCompactSupport g →
                                tsupport g ⊆ Ω' →
                                  IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                                    (fun (x : Vec3) => p (x, s) * g x) Ω volume) →
                          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                            (fun (x : Vec3) => p (x, s) * (ψ x * spatialLaplacian η x)) volume
    := by
  intro Ω p f η hη hηc ψ hψ hψc hψΩ Ω' hψΩ' s hpScalar
  exact decomposition_full_of_on_sws
    (hpScalar (hψ.mul (contDiff_spatialLaplacian_smooth hη)).continuous
      (hψc.mul_right (f' := spatialLaplacian η))
      ((tsupport_mul_subset_left (f := ψ) (g := spatialLaplacian η)).trans hψΩ'))
    ((tsupport_mul_subset_right (f := fun x => p (x, s))
      (g := fun x => ψ x * spatialLaplacian η x)).trans
      ((tsupport_mul_subset_left (f := ψ) (g := spatialLaplacian η)).trans hψΩ))

private lemma pressureP1_distributional_identity_hηLapΩ_11 :
    ∀ {η : Vec3 → ℝ} (Ω' : Set Vec3), tsupport η ⊆ Ω' → tsupport (spatialLaplacian η) ⊆ Ω'
    := by
  intro η Ω' hηΩ'
  change tsupport (fun x => ∑ i : Fin 3,
    spatialDeriv (spatialDeriv η i) i x) ⊆ Ω'
  apply decomposition_ts_support_sum₃_sws
  intro i
  exact (tsupport_fderiv_apply_subset ℝ (basisVec i)).trans
    ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hηΩ')

private lemma pressureP1_distributional_identity_hP7term_12 :
    ∀ {Ω : Set Vec3} {f : ParabolicPoint → Vec3} {η : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) η →
        HasCompactSupport η →
          ∀ {ψ : Vec3 → ℝ},
            ContDiff ℝ (⊤ : ℕ∞) ψ →
              ∀ (Ω' : Set Vec3),
                tsupport η ⊆ Ω' →
                  ∀ (s : ℝ),
                    Ω' ⊆ Ω →
                      (∀ {i : Fin (3 : ℕ)} {g : Vec3 → ℝ},
                          Continuous g →
                            HasCompactSupport g →
                              tsupport g ⊆ Ω' →
                                IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                                  (fun (x : Vec3) => f (x, s) i * g x) Ω volume) →
                        HasCompactSupport (spatialLaplacian ψ) →
                          (∀ (g : Vec3 → ℝ),
                              IntegrableOn (mα := MeasureSpace.toMeasurableSpace) g Ω volume →
                                tsupport g ⊆ Ω →
                                  @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume) →
                            ∀ (j : Fin (3 : ℕ)),
                              @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                                (fun (x : Vec3) =>
                                  pressureNewtonianDerivativePotential j
                                      (fun (y : Vec3) => η y * f (y, s) j) x *
                                    spatialLaplacian ψ x)
                                volume
    := by
  intro Ω f η hη hηc ψ hψ Ω' hηΩ' s hΩ'sub hfScalar hψLapc hSource j
  have hon := hfScalar (i := j) hη.continuous hηc hηΩ'
  have hon' : IntegrableOn (fun y => η y * f (y, s) j) Ω volume :=
    hon.congr (Filter.Eventually.of_forall fun y => by ring)
  exact pressureNewtonianDerivativePotential_mul_smooth_integrable
    (hSource _ hon' (((tsupport_mul_subset_left (f := η)
      (g := fun y => f (y, s) j)).trans hηΩ').trans hΩ'sub))
    (hηc.mul_right (f' := fun y => f (y, s) j))
    (contDiff_spatialLaplacian_smooth hψ) hψLapc

private lemma pressureP1_distributional_identity_hB0Ω_13 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {_ : ParabolicPoint → Vec3} {η : Vec3 → ℝ}
      {c : ℝ → Vec3} {ψ : Vec3 → ℝ} (Ω' : Set Vec3),
      tsupport η ⊆ Ω' →
        ∀ (s : ℝ),
          Ω' ⊆ Ω →
            (tsupport (α := ℝ) fun (x : Vec3) =>
                ∑ i : Fin (3 : ℕ),
                  ∑ j : Fin (3 : ℕ), pressureUTensor u c (x, s) i j * (η x * mixedSecond ψ i j x)) ⊆
              Ω
    := by
  intro Ω u f η c ψ Ω' hηΩ' s hΩ'sub
  apply decomposition_ts_support_sum₂_sws
  intro i j
  exact ((tsupport_mul_subset_right (f := fun x => pressureUTensor u c (x, s) i j)
    (g := fun x => η x * mixedSecond ψ i j x)).trans
    ((tsupport_mul_subset_left (f := η) (g := mixedSecond ψ i j)).trans hηΩ')).trans hΩ'sub

private lemma pressureP1_distributional_identity_hB1Ω_14 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {_ : ParabolicPoint → Vec3} {η : Vec3 → ℝ}
      {c : ℝ → Vec3} {ψ : Vec3 → ℝ} (Ω' : Set Vec3),
      tsupport ψ ⊆ Ω' →
        ∀ (s : ℝ),
          Ω' ⊆ Ω →
            (tsupport (α := ℝ) fun (x : Vec3) =>
                ∑ i : Fin (3 : ℕ),
                  ∑ j : Fin (3 : ℕ), pressureUTensor u c (x, s) i j * (mixedSecond η i j x * ψ x)) ⊆
              Ω
    := by
  intro Ω u f η c ψ Ω' hψΩ' s hΩ'sub
  apply decomposition_ts_support_sum₂_sws
  intro i j
  exact ((tsupport_mul_subset_right (f := fun x => pressureUTensor u c (x, s) i j)
    (g := fun x => mixedSecond η i j x * ψ x)).trans
    ((tsupport_mul_subset_right (f := mixedSecond η i j) (g := ψ)).trans hψΩ')).trans hΩ'sub

private lemma pressureP1_distributional_identity_hB2Ω_15 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {_ : ParabolicPoint → Vec3} {η : Vec3 → ℝ}
      {c : ℝ → Vec3} {ψ : Vec3 → ℝ} (Ω' : Set Vec3),
      tsupport η ⊆ Ω' →
        ∀ (s : ℝ),
          Ω' ⊆ Ω →
            (tsupport (α := ℝ) fun (x : Vec3) =>
                ∑ i : Fin (3 : ℕ),
                  ∑ j : Fin (3 : ℕ),
                    pressureUTensor u c (x, s) i j * (spatialDeriv η i x * spatialDeriv ψ j x)) ⊆
              Ω
    := by
  intro Ω u f η c ψ Ω' hηΩ' s hΩ'sub
  apply decomposition_ts_support_sum₂_sws
  intro i j
  exact ((tsupport_mul_subset_right (f := fun x => pressureUTensor u c (x, s) i j)
    (g := fun x => spatialDeriv η i x * spatialDeriv ψ j x)).trans
    ((tsupport_mul_subset_left (f := spatialDeriv η i)
      (g := spatialDeriv ψ j)).trans
      ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hηΩ'))).trans hΩ'sub

private lemma pressureP1_distributional_identity_hB3Ω_16 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {_ : ParabolicPoint → Vec3} {η : Vec3 → ℝ}
      {c : ℝ → Vec3} {ψ : Vec3 → ℝ} (Ω' : Set Vec3),
      tsupport η ⊆ Ω' →
        ∀ (s : ℝ),
          Ω' ⊆ Ω →
            (tsupport (α := ℝ) fun (x : Vec3) =>
                ∑ i : Fin (3 : ℕ),
                  ∑ j : Fin (3 : ℕ),
                    pressureUTensor u c (x, s) i j * (spatialDeriv η j x * spatialDeriv ψ i x)) ⊆
              Ω
    := by
  intro Ω u f η c ψ Ω' hηΩ' s hΩ'sub
  apply decomposition_ts_support_sum₂_sws
  intro i j
  exact ((tsupport_mul_subset_right (f := fun x => pressureUTensor u c (x, s) i j)
    (g := fun x => spatialDeriv η j x * spatialDeriv ψ i x)).trans
    ((tsupport_mul_subset_left (f := spatialDeriv η j)
      (g := spatialDeriv ψ i)).trans
      ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ'))).trans hΩ'sub

private lemma pressureP1_distributional_identity_hF7Ω_17 :
    ∀ {Ω : Set Vec3} {f : ParabolicPoint → Vec3} {η : Vec3 → ℝ},
      tsupport η ⊆ Ω →
        ∀ {ψ : Vec3 → ℝ} (s : ℝ),
          (tsupport (α := ℝ) fun (x : Vec3) =>
              ∑ i : Fin (3 : ℕ), f (x, s) i * (η x * spatialDeriv ψ i x)) ⊆
            Ω
    := by
  intro Ω f η hηΩ ψ s
  apply decomposition_ts_support_sum₃_sws
  intro i
  exact (tsupport_mul_subset_right (f := fun x => f (x, s) i)
    (g := fun x => η x * spatialDeriv ψ i x)).trans
    ((tsupport_mul_subset_left (f := η) (g := spatialDeriv ψ i)).trans hηΩ)

private lemma pressureP1_distributional_identity_hF8Ω_18 :
    ∀ {Ω : Set Vec3} {f : ParabolicPoint → Vec3} {η ψ : Vec3 → ℝ},
      tsupport ψ ⊆ Ω →
        ∀ (s : ℝ),
          (tsupport (α := ℝ) fun (x : Vec3) =>
              ∑ i : Fin (3 : ℕ), f (x, s) i * (ψ x * spatialDeriv η i x)) ⊆
            Ω
    := by
  intro Ω f η ψ hψΩ s
  apply decomposition_ts_support_sum₃_sws
  intro i
  exact (tsupport_mul_subset_right (f := fun x => f (x, s) i)
    (g := fun x => ψ x * spatialDeriv η i x)).trans
    ((tsupport_mul_subset_left (f := ψ) (g := spatialDeriv η i)).trans hψΩ)

private lemma pressureP1_distributional_identity_hQ_19 :
    ∀ {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
      {η : Vec3 → ℝ} {c : ℝ → Vec3} {ψ : Vec3 → ℝ} (s : ℝ),
      @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
          (fun (x : Vec3) => pressureP2 η u c s x * spatialLaplacian ψ x) volume →
        @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
            (fun (x : Vec3) => pressureP3 η u c s x * spatialLaplacian ψ x) volume →
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
              (fun (x : Vec3) => pressureP4 η u c s x * spatialLaplacian ψ x) volume →
            @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                (fun (x : Vec3) => pressureP5 η p s x * spatialLaplacian ψ x) volume →
              @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                  (fun (x : Vec3) => pressureP6 η p s x * spatialLaplacian ψ x) volume →
                @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                    (fun (x : Vec3) => pressureP7 η f s x * spatialLaplacian ψ x) volume →
                  @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                      (fun (x : Vec3) => pressureP8 η f s x * spatialLaplacian ψ x) volume →
                    @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                      (fun (x : Vec3) =>
                        (pressureP2 η u c s x + pressureP3 η u c s x + pressureP4 η u c s x +
                                  pressureP5 η p s x +
                                pressureP6 η p s x +
                              pressureP7 η f s x +
                            pressureP8 η f s x) *
                          spatialLaplacian ψ x)
                      volume
    := by
  intro u p f η c ψ s hP2 hP3 hP4 hP5 hP6 hP7 hP8
  have hs := hP2.add (hP3.add (hP4.add (hP5.add (hP6.add (hP7.add hP8)))))
  convert hs using 1
  funext x
  simp only [Pi.add_apply]
  ring

private lemma pressureP1_distributional_identity_integral_sum₂_20 :
    ∀ (_ : ℝ) {G : Fin (3 : ℕ) → Fin (3 : ℕ) → Vec3 → ℝ},
      (∀ (i j : Fin (3 : ℕ)), @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace (G i j) volume) →
        Eq (α := ℝ)
          (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
            ∑ i : Fin (3 : ℕ), ∑ j : Fin (3 : ℕ), G i j x)
          (∑ i : Fin (3 : ℕ),
            ∑ j : Fin (3 : ℕ),
              @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) => G i j x)
    := by
  intro s G hG
  rw [integral_finsetSum (s := Finset.univ)]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum (s := Finset.univ)]
    intro j hj
    exact hG i j
  · intro i hi
    exact integrable_finsetSum (Finset.univ : Finset (Fin 3))
      (fun j hj => hG i j)

private lemma pressureP1_distributional_identity_hP2Int_21 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {_ : ParabolicPoint → Vec3} {η : Vec3 → ℝ}
      {c : ℝ → Vec3} (Ω' : Set Vec3) (s : ℝ),
      Ω' ⊆ Ω →
        (∀ {i j : Fin (3 : ℕ)} {g : Vec3 → ℝ},
            Continuous g →
              HasCompactSupport g →
                tsupport g ⊆ Ω' →
                  IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                    (fun (x : Vec3) => pressureUTensor u c (x, s) i j * g x) Ω volume) →
          (∀ (i j : Fin (3 : ℕ)), ContDiff ℝ (⊤ : ℕ∞) (mixedSecond η i j)) →
            (∀ (i j : Fin (3 : ℕ)), HasCompactSupport (mixedSecond η i j)) →
              (∀ (i j : Fin (3 : ℕ)), tsupport (mixedSecond η i j) ⊆ Ω') →
                (∀ (g : Vec3 → ℝ),
                    IntegrableOn (mα := MeasureSpace.toMeasurableSpace) g Ω volume →
                      tsupport g ⊆ Ω →
                        @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume) →
                  ∀ (i j : Fin (3 : ℕ)),
                    @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                      (fun (y : Vec3) => mixedSecond η i j y * pressureUTensor u c (y, s) i j)
                      volume
    := by
  intro Ω u f η c Ω' s hΩ'sub hUScalar hηm hηmc hηmΩ hSource i j
  have hon := hUScalar (i := i) (j := j) (hηm i j).continuous
    (hηmc i j) (hηmΩ i j)
  exact hSource _ (hon.congr (Filter.Eventually.of_forall fun y => by ring))
    (((tsupport_mul_subset_left (f := mixedSecond η i j)
      (g := fun y => pressureUTensor u c (y, s) i j)).trans (hηmΩ i j)).trans hΩ'sub)

private lemma pressureP1_distributional_identity_hP3Int_22 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {_ : ParabolicPoint → Vec3} {η : Vec3 → ℝ}
      {c : ℝ → Vec3} (Ω' : Set Vec3),
      tsupport η ⊆ Ω' →
        ∀ (s : ℝ),
          Ω' ⊆ Ω →
            (∀ {i j : Fin (3 : ℕ)} {g : Vec3 → ℝ},
                Continuous g →
                  HasCompactSupport g →
                    tsupport g ⊆ Ω' →
                      IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                        (fun (x : Vec3) => pressureUTensor u c (x, s) i j * g x) Ω volume) →
              (∀ (i : Fin (3 : ℕ)), ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv η i)) →
                (∀ (i : Fin (3 : ℕ)), HasCompactSupport (spatialDeriv η i)) →
                  (∀ (g : Vec3 → ℝ),
                      IntegrableOn (mα := MeasureSpace.toMeasurableSpace) g Ω volume →
                        tsupport g ⊆ Ω →
                          @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume) →
                    ∀ (i j : Fin (3 : ℕ)),
                      @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                        (fun (y : Vec3) => pressureUTensor u c (y, s) i j * spatialDeriv η i y)
                        volume
    := by
  intro Ω u f η c Ω' hηΩ' s hΩ'sub hUScalar hηd hηdc hSource i j
  exact hSource _ (hUScalar (i := i) (j := j) (hηd i).continuous (hηdc i)
    ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hηΩ'))
    (((tsupport_mul_subset_right (f := fun y => pressureUTensor u c (y, s) i j)
      (g := spatialDeriv η i)).trans
      ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hηΩ')).trans hΩ'sub)

private lemma pressureP1_distributional_identity_hP4Int_23 :
    ∀ {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {_ : ParabolicPoint → Vec3} {η : Vec3 → ℝ}
      {c : ℝ → Vec3} (Ω' : Set Vec3),
      tsupport η ⊆ Ω' →
        ∀ (s : ℝ),
          Ω' ⊆ Ω →
            (∀ {i j : Fin (3 : ℕ)} {g : Vec3 → ℝ},
                Continuous g →
                  HasCompactSupport g →
                    tsupport g ⊆ Ω' →
                      IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                        (fun (x : Vec3) => pressureUTensor u c (x, s) i j * g x) Ω volume) →
              (∀ (i : Fin (3 : ℕ)), ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv η i)) →
                (∀ (i : Fin (3 : ℕ)), HasCompactSupport (spatialDeriv η i)) →
                  (∀ (g : Vec3 → ℝ),
                      IntegrableOn (mα := MeasureSpace.toMeasurableSpace) g Ω volume →
                        tsupport g ⊆ Ω →
                          @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume) →
                    ∀ (i j : Fin (3 : ℕ)),
                      @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                        (fun (y : Vec3) => pressureUTensor u c (y, s) i j * spatialDeriv η j y)
                        volume
    := by
  intro Ω u f η c Ω' hηΩ' s hΩ'sub hUScalar hηd hηdc hSource i j
  exact hSource _ (hUScalar (i := i) (j := j) (hηd j).continuous (hηdc j)
    ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ'))
    (((tsupport_mul_subset_right (f := fun y => pressureUTensor u c (y, s) i j)
      (g := spatialDeriv η j)).trans
      ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ')).trans hΩ'sub)

private lemma pressureP1_distributional_identity_hP6Int_24 :
    ∀ {Ω : Set Vec3} {p : ParabolicPoint → ℝ} {_ : ParabolicPoint → Vec3} {η : Vec3 → ℝ}
      (Ω' : Set Vec3),
      tsupport η ⊆ Ω' →
        ∀ (s : ℝ),
          Ω' ⊆ Ω →
            (∀ {g : Vec3 → ℝ},
                Continuous g →
                  HasCompactSupport g →
                    tsupport g ⊆ Ω' →
                      IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                        (fun (x : Vec3) => p (x, s) * g x) Ω volume) →
              (∀ (i : Fin (3 : ℕ)), ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv η i)) →
                (∀ (i : Fin (3 : ℕ)), HasCompactSupport (spatialDeriv η i)) →
                  (∀ (g : Vec3 → ℝ),
                      IntegrableOn (mα := MeasureSpace.toMeasurableSpace) g Ω volume →
                        tsupport g ⊆ Ω →
                          @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume) →
                    ∀ (j : Fin (3 : ℕ)),
                      @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                        (fun (y : Vec3) => spatialDeriv η j y * p (y, s)) volume
    := by
  intro Ω p f η Ω' hηΩ' s hΩ'sub hpScalar hηd hηdc hSource j
  have hon := hpScalar (hηd j).continuous (hηdc j)
    ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ')
  exact hSource _ (hon.congr (Filter.Eventually.of_forall fun y => by ring))
    (((tsupport_mul_subset_left (f := spatialDeriv η j)
      (g := fun y => p (y, s))).trans
      ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ')).trans hΩ'sub)

private lemma pressureP1_distributional_identity_hP8Int_25 :
    ∀ {Ω : Set Vec3} {f : ParabolicPoint → Vec3} {η : Vec3 → ℝ} (Ω' : Set Vec3),
      tsupport η ⊆ Ω' →
        ∀ (s : ℝ),
          Ω' ⊆ Ω →
            (∀ {i : Fin (3 : ℕ)} {g : Vec3 → ℝ},
                Continuous g →
                  HasCompactSupport g →
                    tsupport g ⊆ Ω' →
                      IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                        (fun (x : Vec3) => f (x, s) i * g x) Ω volume) →
              (∀ (i : Fin (3 : ℕ)), ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv η i)) →
                (∀ (i : Fin (3 : ℕ)), HasCompactSupport (spatialDeriv η i)) →
                  (∀ (g : Vec3 → ℝ),
                      IntegrableOn (mα := MeasureSpace.toMeasurableSpace) g Ω volume →
                        tsupport g ⊆ Ω →
                          @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume) →
                    ∀ (j : Fin (3 : ℕ)),
                      @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                        (fun (y : Vec3) => spatialDeriv η j y * f (y, s) j) volume
    := by
  intro Ω f η Ω' hηΩ' s hΩ'sub hfScalar hηd hηdc hSource j
  have hon := hfScalar (i := j) (hηd j).continuous (hηdc j)
    ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ')
  exact hSource _ (hon.congr (Filter.Eventually.of_forall fun y => by ring))
    (((tsupport_mul_subset_left (f := spatialDeriv η j)
      (g := fun y => f (y, s) j)).trans
      ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ')).trans hΩ'sub)

private lemma pressureP1_distributional_identity_hF7PairInt_26 :
    ∀ {Ω : Set Vec3} {f : ParabolicPoint → Vec3} {η : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) η →
        HasCompactSupport η →
          ∀ {ψ : Vec3 → ℝ} (Ω' : Set Vec3),
            tsupport η ⊆ Ω' →
              ∀ (s : ℝ),
                Ω' ⊆ Ω →
                  (∀ {i : Fin (3 : ℕ)} {g : Vec3 → ℝ},
                      Continuous g →
                        HasCompactSupport g →
                          tsupport g ⊆ Ω' →
                            IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                              (fun (x : Vec3) => f (x, s) i * g x) Ω volume) →
                    (∀ (i : Fin (3 : ℕ)), ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv ψ i)) →
                      (∀ (g : Vec3 → ℝ),
                          IntegrableOn (mα := MeasureSpace.toMeasurableSpace) g Ω volume →
                            tsupport g ⊆ Ω →
                              @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume) →
                        ∀ (j : Fin (3 : ℕ)),
                          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                            (fun (y : Vec3) => f (y, s) j * (η y * spatialDeriv ψ j y)) volume
    := by
  intro Ω f η hη hηc ψ Ω' hηΩ' s hΩ'sub hfScalar hψd hSource j
  exact hSource _ (hfScalar (i := j) (hη.mul (hψd j)).continuous
    (hηc.mul_right (f' := spatialDeriv ψ j))
    ((tsupport_mul_subset_left (f := η) (g := spatialDeriv ψ j)).trans hηΩ'))
    ((((tsupport_mul_subset_right (f := fun y => f (y, s) j)
      (g := fun y => η y * spatialDeriv ψ j y)).trans
      ((tsupport_mul_subset_left (f := η) (g := spatialDeriv ψ j)).trans hηΩ')).trans
      hΩ'sub))

private lemma pressureP1_distributional_identity_hF8PairInt_27 :
    ∀ {Ω : Set Vec3} {f : ParabolicPoint → Vec3} {η ψ : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ →
          ∀ (Ω' : Set Vec3),
            tsupport ψ ⊆ Ω' →
              ∀ (s : ℝ),
                Ω' ⊆ Ω →
                  (∀ {i : Fin (3 : ℕ)} {g : Vec3 → ℝ},
                      Continuous g →
                        HasCompactSupport g →
                          tsupport g ⊆ Ω' →
                            IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                              (fun (x : Vec3) => f (x, s) i * g x) Ω volume) →
                    (∀ (i : Fin (3 : ℕ)), ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv η i)) →
                      (∀ (g : Vec3 → ℝ),
                          IntegrableOn (mα := MeasureSpace.toMeasurableSpace) g Ω volume →
                            tsupport g ⊆ Ω →
                              @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume) →
                        ∀ (j : Fin (3 : ℕ)),
                          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                            (fun (y : Vec3) => f (y, s) j * (ψ y * spatialDeriv η j y)) volume
    := by
  intro Ω f η ψ hψ hψc Ω' hψΩ' s hΩ'sub hfScalar hηd hSource j
  exact hSource _ (hfScalar (i := j) (hψ.mul (hηd j)).continuous
    (hψc.mul_right (f' := spatialDeriv η j))
    ((tsupport_mul_subset_left (f := ψ) (g := spatialDeriv η j)).trans hψΩ'))
    ((((tsupport_mul_subset_right (f := fun y => f (y, s) j)
      (g := fun y => ψ y * spatialDeriv η j y)).trans
      ((tsupport_mul_subset_left (f := ψ) (g := spatialDeriv η j)).trans hψΩ')).trans
      hΩ'sub))

private lemma pressureP1_distributional_identity_hPair5_28 :
    ∀ {p : ParabolicPoint → ℝ} {η ψ : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ →
          ∀ (s : ℝ),
            @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                (fun (y : Vec3) => p (y, s) * spatialLaplacian η y) volume →
              (HasCompactSupport (β := ℝ) fun (y : Vec3) => p (y, s) * spatialLaplacian η y) →
                Eq (α := ℝ)
                  (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                    pressureP5 η p s x * spatialLaplacian ψ x)
                  (-@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
                      p (x, s) * (ψ x * spatialLaplacian η x))
    := by
  intro p η ψ hψ hψc s hP5Int hP5Supp
  calc
    _ = -∫ y, p (y, s) * spatialLaplacian η y * ψ y :=
      pressureP5_distributional_pairing hP5Int hP5Supp hψ hψc
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with y
      ring

private lemma pressureP1_distributional_identity_hAΩ_1 :
    ∀ {Ω : Set Vec3} {p : ParabolicPoint → ℝ} {_ : ParabolicPoint → Vec3} {η : Vec3 → ℝ},
      tsupport η ⊆ Ω →
        ∀ {ψ : Vec3 → ℝ} (s : ℝ),
          (tsupport (α := ℝ) fun (x : Vec3) => η x * p (x, s) * spatialLaplacian ψ x) ⊆ Ω
    := by
  intro Ω p f η hηΩ ψ s
  rw [show (fun x => η x * p (x, s) * spatialLaplacian ψ x) =
    (fun x => η x * (p (x, s) * spatialLaplacian ψ x)) by funext x; ring]
  exact (tsupport_mul_subset_left (f := η) (g := fun x =>
    p (x, s) * spatialLaplacian ψ x)).trans hηΩ

private lemma pressureP1_distributional_identity_hP2_2 :
    ∀ {u : ParabolicPoint → Vec3} {η : Vec3 → ℝ} {c : ℝ → Vec3} {ψ : Vec3 → ℝ} (s : ℝ),
      (∀ (i j : Fin (3 : ℕ)),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
            (fun (x : Vec3) =>
              pressureNewtonianPotential
                  (fun (y : Vec3) => mixedSecond η i j y * pressureUTensor u c (y, s) i j) x *
                spatialLaplacian ψ x)
            volume) →
        @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
          (fun (x : Vec3) => pressureP2 η u c s x * spatialLaplacian ψ x) volume
    := by
  intro u η c ψ s hP2term
  have hs := integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ =>
    integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => hP2term i j))
  simpa only [pressureP2, Finset.sum_mul] using hs

private lemma pressureP1_distributional_identity_hP3_3 :
    ∀ {u : ParabolicPoint → Vec3} {η : Vec3 → ℝ} {c : ℝ → Vec3} {ψ : Vec3 → ℝ} (s : ℝ),
      (∀ (i j : Fin (3 : ℕ)),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
            (fun (x : Vec3) =>
              pressureNewtonianDerivativePotential j
                  (fun (y : Vec3) => pressureUTensor u c (y, s) i j * spatialDeriv η i y) x *
                spatialLaplacian ψ x)
            volume) →
        @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
          (fun (x : Vec3) => pressureP3 η u c s x * spatialLaplacian ψ x) volume
    := by
  intro u η c ψ s hP3term
  have hs := integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ =>
    integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => hP3term i j))
  simpa only [pressureP3, Finset.sum_mul] using hs

private lemma pressureP1_distributional_identity_hP4_4 :
    ∀ {u : ParabolicPoint → Vec3} {η : Vec3 → ℝ} {c : ℝ → Vec3} {ψ : Vec3 → ℝ} (s : ℝ),
      (∀ (i j : Fin (3 : ℕ)),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
            (fun (x : Vec3) =>
              pressureNewtonianDerivativePotential i
                  (fun (y : Vec3) => pressureUTensor u c (y, s) i j * spatialDeriv η j y) x *
                spatialLaplacian ψ x)
            volume) →
        @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
          (fun (x : Vec3) => pressureP4 η u c s x * spatialLaplacian ψ x) volume
    := by
  intro u η c ψ s hP4term
  have hs := integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ =>
    integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => hP4term i j))
  simpa only [pressureP4, Finset.sum_mul] using hs

private lemma pressureP1_distributional_identity_hC5Ω_5 :
    ∀ {Ω : Set Vec3} {p : ParabolicPoint → ℝ} {_ : ParabolicPoint → Vec3} {η ψ : Vec3 → ℝ},
      tsupport ψ ⊆ Ω →
        ∀ (s : ℝ), (tsupport (α := ℝ) fun (x : Vec3) => p (x, s) * (ψ x * spatialLaplacian η x)) ⊆ Ω
    := by
  intro Ω p f η ψ hψΩ s
  exact (tsupport_mul_subset_right (f := fun x => p (x, s))
    (g := fun x => ψ x * spatialLaplacian η x)).trans
    ((tsupport_mul_subset_left (f := ψ) (g := spatialLaplacian η)).trans hψΩ)

private lemma pressureP1_distributional_identity_integral_sum₁_6 :
    ∀ (_ : ℝ) {G : Fin (3 : ℕ) → Vec3 → ℝ},
      (∀ (j : Fin (3 : ℕ)), @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace (G j) volume) →
        Eq (α := ℝ)
          (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) =>
            ∑ j : Fin (3 : ℕ), G j x)
          (∑ j : Fin (3 : ℕ),
            @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (x : Vec3) => G j x)
    := by
  intro s G hG
  rw [integral_finsetSum (s := Finset.univ)]
  intro j hj
  exact hG j

private lemma pressureP1_distributional_identity_hP5Int_7 :
    ∀ {Ω : Set Vec3} {p : ParabolicPoint → ℝ} {_ : ParabolicPoint → Vec3} {η : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) η →
        ∀ (Ω' : Set Vec3) (s : ℝ),
          Ω' ⊆ Ω →
            (∀ {g : Vec3 → ℝ},
                Continuous g →
                  HasCompactSupport g →
                    tsupport g ⊆ Ω' →
                      IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                        (fun (x : Vec3) => p (x, s) * g x) Ω volume) →
              tsupport (spatialLaplacian η) ⊆ Ω' →
                HasCompactSupport (spatialLaplacian η) →
                  (∀ (g : Vec3 → ℝ),
                      IntegrableOn (mα := MeasureSpace.toMeasurableSpace) g Ω volume →
                        tsupport g ⊆ Ω →
                          @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume) →
                    tsupport (spatialLaplacian η) ⊆ Ω' →
                      @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                        (fun (y : Vec3) => p (y, s) * spatialLaplacian η y) volume
    := by
  intro Ω p f η hη Ω' s hΩ'sub hpScalar hηLapΩ hηLapc hSource hηLapΩ
  exact hSource _ (hpScalar (contDiff_spatialLaplacian_smooth hη).continuous
    hηLapc hηLapΩ)
    (((tsupport_mul_subset_right (f := fun y => p (y, s))
      (g := spatialLaplacian η)).trans hηLapΩ).trans hΩ'sub)

private lemma pressureP1_distributional_identity_hP7Int_8 :
    ∀ {Ω : Set Vec3} {f : ParabolicPoint → Vec3} {η : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) η →
        HasCompactSupport η →
          ∀ (Ω' : Set Vec3),
            tsupport η ⊆ Ω' →
              ∀ (s : ℝ),
                Ω' ⊆ Ω →
                  (∀ {i : Fin (3 : ℕ)} {g : Vec3 → ℝ},
                      Continuous g →
                        HasCompactSupport g →
                          tsupport g ⊆ Ω' →
                            IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                              (fun (x : Vec3) => f (x, s) i * g x) Ω volume) →
                    (∀ (g : Vec3 → ℝ),
                        IntegrableOn (mα := MeasureSpace.toMeasurableSpace) g Ω volume →
                          tsupport g ⊆ Ω →
                            @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace g volume) →
                      ∀ (j : Fin (3 : ℕ)),
                        @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                          (fun (y : Vec3) => η y * f (y, s) j) volume
    := by
  intro Ω f η hη hηc Ω' hηΩ' s hΩ'sub hfScalar hSource j
  have hon := hfScalar (i := j) hη.continuous hηc hηΩ'
  exact hSource _ (hon.congr (Filter.Eventually.of_forall fun y => by ring))
    (((tsupport_mul_subset_left (f := η) (g := fun y => f (y, s) j)).trans
      hηΩ').trans hΩ'sub)

private lemma integrable_double_sum {G : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hG : ∀ i j, Integrable (G i j) volume) :
    Integrable (fun x => ∑ i, ∑ j, G i j x) volume :=
  integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hG i j))

theorem pressureP1_distributional_identity_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω)
    {c : ℝ → Vec3} {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψΩ : tsupport ψ ⊆ Ω) :
    ∀ᵐ s ∂volume.restrict I,
      ∫ x, pressureP1 η u c p f s x * spatialLaplacian ψ x =
        ∫ x, ∑ i, ∑ j, η x * pressureUTensor u c (x, s) i j *
          mixedSecond ψ i j x := by
  obtain ⟨Ω', hΩ'open, hηΩ', hψΩ', hΩ'compact, hΩ'Ω, hLp⟩ :=
    decomposition_slice_integrability hsol hηc hηΩ hψc hψΩ
  have : IsFiniteMeasure (volume.restrict Ω') := by
    apply isFiniteMeasure_restrict.mpr
    exact (lt_of_le_of_lt (measure_mono (μ := volume) subset_closure)
      hΩ'compact.measure_lt_top).ne
  have hcut := pressure_laplace_cutoff_identity_ae hsol hη hηc hηΩ (c := c) hψ hψc hψΩ
  filter_upwards [hcut, hLp] with s hcut_s hLp_s
  have hΩ'sub : Ω' ⊆ Ω := subset_closure.trans hΩ'Ω
  have huComp (i : Fin 3) :=
    hLp_s.1.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
  have huInt (i : Fin 3) :=
    huComp i |>.integrable (by norm_num)
  have hfInt (i : Fin 3) := pressureP1_distributional_identity_hfInt_1 Ω' s hLp_s i
  have hpScalar {g : Vec3 → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
      (hgΩ : tsupport g ⊆ Ω') := @pressureP1_distributional_identity_hpScalar_1 Ω u p f Ω' s hLp_s
        g hg hgc hgΩ
  have huScalar {i : Fin 3} {g : Vec3 → ℝ} (hg : Continuous g)
      (hgc : HasCompactSupport g) (hgΩ : tsupport g ⊆ Ω') :=
        @pressureP1_distributional_identity_huScalar_2 Ω u f Ω' s huInt i g hg hgc hgΩ
  have huuScalar {i j : Fin 3} {g : Vec3 → ℝ} (hg : Continuous g)
      (hgc : HasCompactSupport g) (hgΩ : tsupport g ⊆ Ω') :=
        @pressureP1_distributional_identity_huuScalar_2 Ω u f Ω' s huComp i j g hg hgc hgΩ
  have hfScalar {i : Fin 3} {g : Vec3 → ℝ} (hg : Continuous g)
      (hgc : HasCompactSupport g) (hgΩ : tsupport g ⊆ Ω') :=
        @pressureP1_distributional_identity_hfScalar_3 Ω f Ω' s hfInt i g hg hgc hgΩ
  have hUScalar {i j : Fin 3} {g : Vec3 → ℝ} (hg : Continuous g)
      (hgc : HasCompactSupport g) (hgΩ : tsupport g ⊆ Ω') :=
        @pressureP1_distributional_identity_hUScalar_4 Ω u c Ω' s huScalar huuScalar i j g hg hgc
        hgΩ
  have hfinite {g : Fin 3 → Vec3 → ℝ} (hg : ∀ i, IntegrableOn (g i) Ω volume) :
      IntegrableOn (fun x => ∑ i, g i x) Ω volume := by
    change Integrable (∑ i, (fun x => g i x)) (volume.restrict Ω)
    exact integrable_finsetSum' (Finset.univ : Finset (Fin 3)) (fun i _ => hg i)
  have hηd (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv η i) :=
    contDiff_spatialDeriv_smooth hη i
  have hψd (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv ψ i) :=
    contDiff_spatialDeriv_smooth hψ i
  have hηm (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (mixedSecond η i j) :=
    contDiff_mixedSecond_smooth hη i j
  have hψm (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (mixedSecond ψ i j) :=
    contDiff_mixedSecond_smooth hψ i j
  have hηdc (i : Fin 3) : HasCompactSupport (spatialDeriv η i) :=
    (hηc.fderiv_apply (𝕜 := ℝ) (basisVec i))
  have hηmc (i j : Fin 3) : HasCompactSupport (mixedSecond η i j) := by
    exact (hηdc j).fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hηmΩ (i j : Fin 3) : tsupport (mixedSecond η i j) ⊆ Ω' := by
    exact (tsupport_fderiv_apply_subset ℝ (basisVec i)).trans
      ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ')
  have hηLapΩ := pressureP1_distributional_identity_hηLapΩ_5 Ω' hηΩ'
  have hψLapc : HasCompactSupport (spatialLaplacian ψ) :=
    decomposition_laplacian_hasCompactSupport_sws hψc
  have hηLapc : HasCompactSupport (spatialLaplacian η) :=
    decomposition_laplacian_hasCompactSupport_sws hηc
  have hAon := @pressureP1_distributional_identity_hAon_6 Ω p f η hη hηc ψ hψ Ω' hηΩ' s hpScalar
  have hAΩ := @pressureP1_distributional_identity_hAΩ_1 Ω p f η hηΩ ψ s
  have hA : Integrable (fun x => η x * p (x, s) * spatialLaplacian ψ x) volume :=
    decomposition_full_of_on_sws hAon hAΩ
  have hSource (g : Vec3 → ℝ) (hg : IntegrableOn g Ω volume)
      (hgΩ : tsupport g ⊆ Ω) :=
    decomposition_full_of_on_sws hg
        hgΩ
  have hU0 (i j : Fin 3) : Integrable
      (fun x => pressureUTensor u c (x, s) i j * (η x * mixedSecond ψ i j x)) volume :=
    by
      exact @pressureP1_distributional_identity_hU0_7 Ω u f η hη hηc c ψ Ω' hηΩ' s hΩ'sub hUScalar
        hψm hSource i j
  have hU1 (i j : Fin 3) : Integrable
      (fun x => pressureUTensor u c (x, s) i j * (mixedSecond η i j x * ψ x)) volume :=
    by
      exact @pressureP1_distributional_identity_hU1_8 Ω u f η c ψ hψ hψc Ω' hψΩ' s hΩ'sub hUScalar
        hηm hSource i j
  have hU2 (i j : Fin 3) :=
    hSource _ (hUScalar (i := i) (j := j) ((hηd i).mul (hψd j)).continuous
      ((hηdc i).mul_right (f' := spatialDeriv ψ j))
      ((tsupport_mul_subset_left (f := spatialDeriv η i) (g := spatialDeriv ψ j)).trans
        ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hηΩ')))
      ((tsupport_mul_subset_right (f := fun x => pressureUTensor u c (x, s) i j)
        (g := fun x => spatialDeriv η i x * spatialDeriv ψ j x)).trans
        ((tsupport_mul_subset_left (f := spatialDeriv η i) (g := spatialDeriv ψ j)).trans
          ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hηΩ)))
  have hU3 (i j : Fin 3) := @pressureP1_distributional_identity_hU3_9 Ω u f η hηΩ c ψ Ω' hηΩ' s
    hUScalar hηd hψd hηdc hSource i j
  have hC5 := @pressureP1_distributional_identity_hC5_10 Ω p f η hη hηc ψ hψ hψc hψΩ Ω' hψΩ' s
    hpScalar
  have hC6 := @pressureP1_distributional_identity_hC6_4 Ω p f η hηΩ ψ Ω' hηΩ' s hpScalar hfinite
    hηd hψd hηdc
  have hF7 := pressureP1_distributional_identity_hF7_5 hη hηc hηΩ Ω' hηΩ' s hfScalar hfinite hψd
  have hF8 := pressureP1_distributional_identity_hF8_6 hψ hψc hψΩ Ω' hψΩ' s hfScalar hfinite hηd
  have hηLapΩ := pressureP1_distributional_identity_hηLapΩ_11 Ω' hηΩ'
  have hP2term (i j : Fin 3) := @pressureP1_distributional_identity_hP2term_7 Ω u f η c ψ hψ Ω' s
    hΩ'sub hUScalar hηm hηmc hηmΩ hψLapc hSource i j
  have hP2 := pressureP1_distributional_identity_hP2_2 s hP2term
  have hP3term (i j : Fin 3) : Integrable
      (fun x => pressureNewtonianDerivativePotential j
        (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) x *
          spatialLaplacian ψ x) volume :=
    pressureNewtonianDerivativePotential_mul_smooth_integrable
      (hSource _ (hUScalar (i := i) (j := j) (hηd i).continuous (hηdc i)
        ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hηΩ'))
        (((tsupport_mul_subset_right (f := fun y => pressureUTensor u c (y, s) i j)
          (g := spatialDeriv η i)).trans
          ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hηΩ')).trans hΩ'sub))
      ((hηdc i).mul_left (f := fun y => pressureUTensor u c (y, s) i j))
        (contDiff_spatialLaplacian_smooth hψ) hψLapc
  have hP3 := pressureP1_distributional_identity_hP3_3 s hP3term
  have hP4term (i j : Fin 3) : Integrable
      (fun x => pressureNewtonianDerivativePotential i
        (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) x *
          spatialLaplacian ψ x) volume :=
    pressureNewtonianDerivativePotential_mul_smooth_integrable
      (hSource _ (hUScalar (i := i) (j := j) (hηd j).continuous (hηdc j)
        ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ'))
        (((tsupport_mul_subset_right (f := fun y => pressureUTensor u c (y, s) i j)
          (g := spatialDeriv η j)).trans
          ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ')).trans hΩ'sub))
      ((hηdc j).mul_left (f := fun y => pressureUTensor u c (y, s) i j))
        (contDiff_spatialLaplacian_smooth hψ) hψLapc
  have hP4 := pressureP1_distributional_identity_hP4_4 s hP4term
  have hP5 := @pressureP1_distributional_identity_hP5_8 Ω p f η hη ψ hψ Ω' s hΩ'sub hpScalar (by
    assumption) hψLapc hηLapc hSource hηLapΩ
  have hP6term (j : Fin 3) := @pressureP1_distributional_identity_hP6term_9 Ω p f η ψ hψ Ω' hηΩ' s
    hΩ'sub hpScalar hηd hηdc hψLapc hSource j
  have hP6 := pressureP1_distributional_identity_hP6_10 s hP6term
  have hP7term (j : Fin 3) := pressureP1_distributional_identity_hP7term_12 hη hηc hψ Ω'
    hηΩ' s hΩ'sub hfScalar hψLapc hSource j
  have hP7 := pressureP1_distributional_identity_hP7_11 s hP7term
  have hP8term (j : Fin 3) := pressureP1_distributional_identity_hP8term_12 hψ Ω' hηΩ' s
    hΩ'sub hfScalar hηd hηdc hψLapc hSource j
  have hP8 := pressureP1_distributional_identity_hP8_13 s hP8term
  have hB0 := integrable_double_sum hU0
  have hB1 := integrable_double_sum hU1
  have hB2 := integrable_double_sum hU2
  have hB3 := integrable_double_sum hU3
  have hB0Ω := @pressureP1_distributional_identity_hB0Ω_13 Ω u f η c ψ Ω' hηΩ' s hΩ'sub
  have hB1Ω := @pressureP1_distributional_identity_hB1Ω_14 Ω u f η c ψ Ω' hψΩ' s hΩ'sub
  have hB2Ω := @pressureP1_distributional_identity_hB2Ω_15 Ω u f η c ψ Ω' hηΩ' s hΩ'sub
  have hB3Ω := @pressureP1_distributional_identity_hB3Ω_16 Ω u f η c ψ Ω' hηΩ' s hΩ'sub
  have hC5Ω := @pressureP1_distributional_identity_hC5Ω_5 Ω p f η ψ hψΩ s
  have hC6Ω := @pressureP1_distributional_identity_hC6Ω_14 Ω p f η ψ Ω' hηΩ' s hΩ'sub
  have hF7Ω := @pressureP1_distributional_identity_hF7Ω_17 Ω f η hηΩ ψ s
  have hF8Ω := @pressureP1_distributional_identity_hF8Ω_18 Ω f η ψ hψΩ s
  have hQ := pressureP1_distributional_identity_hQ_19 s hP2 hP3 hP4 hP5 hP6 hP7 hP8
  have integral_sum₁ {G : Fin 3 → Vec3 → ℝ}
      (hG : ∀ j, Integrable (G j) volume) := pressureP1_distributional_identity_integral_sum₁_6 s hG
  have integral_sum₂ {G : Fin 3 → Fin 3 → Vec3 → ℝ}
      (hG : ∀ i j, Integrable (G i j) volume) :=
        pressureP1_distributional_identity_integral_sum₂_20 s hG
  have hP2Int (i j : Fin 3) := @pressureP1_distributional_identity_hP2Int_21 Ω u f η c Ω' s hΩ'sub
    hUScalar hηm hηmc hηmΩ hSource i j
  have hP2Supp (i j : Fin 3) :=
    (hηmc i j).mul_right (f' := fun y => pressureUTensor u c (y, s) i j)
  have hP3Int (i j : Fin 3) := @pressureP1_distributional_identity_hP3Int_22 Ω u f η c Ω' hηΩ' s
    hΩ'sub hUScalar hηd hηdc hSource i j
  have hP3Supp (i j : Fin 3) :=
    (hηdc i).mul_left (f := fun y => pressureUTensor u c (y, s) i j)
  have hP4Int (i j : Fin 3) := @pressureP1_distributional_identity_hP4Int_23 Ω u f η c Ω' hηΩ' s
    hΩ'sub hUScalar hηd hηdc hSource i j
  have hP4Supp (i j : Fin 3) :=
    (hηdc j).mul_left (f := fun y => pressureUTensor u c (y, s) i j)
  have hP5Int := @pressureP1_distributional_identity_hP5Int_7 Ω p f η hη Ω' s hΩ'sub hpScalar (by
    assumption) hηLapc hSource hηLapΩ
  have hP5Supp := hηLapc.mul_left (f := fun y => p (y, s))
  have hP6Int (j : Fin 3) := @pressureP1_distributional_identity_hP6Int_24 Ω p f η Ω' hηΩ' s
    hΩ'sub hpScalar hηd hηdc hSource j
  have hP6Supp (j : Fin 3) := (hηdc j).mul_right (f' := fun y => p (y, s))
  have hP7Int (j : Fin 3) := pressureP1_distributional_identity_hP7Int_8 hη hηc Ω' hηΩ' s
    hΩ'sub hfScalar hSource j
  have hP7Supp (j : Fin 3) := hηc.mul_right (f' := fun y => f (y, s) j)
  have hP8Int (j : Fin 3) := pressureP1_distributional_identity_hP8Int_25 Ω' hηΩ' s hΩ'sub
    hfScalar hηd hηdc hSource j
  have hP8Supp (j : Fin 3) := (hηdc j).mul_right (f' := fun y => f (y, s) j)
  have hC6Int (j : Fin 3) := @pressureP1_distributional_identity_hC6Int_15 Ω p f η ψ Ω' hηΩ' s
    hΩ'sub hpScalar hηd hψd hηdc hSource j
  have hF7PairInt (j : Fin 3) := pressureP1_distributional_identity_hF7PairInt_26 hη hηc
    Ω' hηΩ' s hΩ'sub hfScalar hψd hSource j
  have hF8PairInt (j : Fin 3) := pressureP1_distributional_identity_hF8PairInt_27 hψ hψc
    Ω' hψΩ' s hΩ'sub hfScalar hηd hSource j
  have hPair2 := pressureP1_distributional_identity_hPair2_16 hψ hψc s hU1 integral_sum₂
    hP2Int hP2Supp
  have hPair3 := pressureP1_distributional_identity_hPair3_17 hψ hψc s hU2 integral_sum₂
    hP3Int hP3Supp
  have hPair4 := pressureP1_distributional_identity_hPair4_18 hψ hψc s hU3 integral_sum₂
    hP4Int hP4Supp
  have hPair5 := pressureP1_distributional_identity_hPair5_28 hψ hψc s hP5Int hP5Supp
  have hPair6 := pressureP1_distributional_identity_hPair6_19 hψ hψc s integral_sum₁ hP6Int
    hP6Supp hC6Int
  have hPair7 := pressureP1_distributional_identity_hPair7_20 hψ hψc s integral_sum₁ hP7Int
    hP7Supp hF7PairInt
  have hPair8 := pressureP1_distributional_identity_hPair8_21 hψ hψc s integral_sum₁ hP8Int
    hP8Supp hF8PairInt
  exact pressureP1_distributional_identity_of_cutoff
    hcut_s hA hAΩ hB0 hB0Ω hB1 hB1Ω hB2 hB2Ω
    hB3 hB3Ω hC5 hC5Ω hC6 hC6Ω hF7 hF7Ω hF8 hF8Ω
    hQ hP2 hP3 hP4 hP5 hP6 hP7 hP8 hPair2 hPair3
    hPair4 hPair5 hPair6 hPair7 hPair8

end CKN
