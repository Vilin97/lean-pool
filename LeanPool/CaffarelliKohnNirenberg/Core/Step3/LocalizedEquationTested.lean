/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationLaplacian

/-!
# Localized Equation Tested

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
noncomputable section
namespace CKN.Core.Step3
open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Core.HeatPotential
private lemma localized_divergence_tested_hG_1 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {ψ : Vec3 × ℝ → Vec3},
      (∀ (i : Fin (3 : ℕ)),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
            (fun (z : ParabolicPoint) => u z i * (timePartial φ z * ψ z i)) volume) →
        (∀ (i j : Fin (3 : ℕ)),
            @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
              (fun (z : ParabolicPoint) => u z i * u z j * (spatialPartial φ j z * ψ z i)) volume) →
          (∀ (i j : Fin (3 : ℕ)),
              @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                (fun (z : ParabolicPoint) => Du z i j * (spatialPartial φ j z * ψ z i)) volume) →
            (∀ (i : Fin (3 : ℕ)),
                @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                  (fun (z : ParabolicPoint) => p z * (spatialPartial φ i z * ψ z i)) volume) →
              (∀ (i : Fin (3 : ℕ)),
                  @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                    (fun (z : ParabolicPoint) => f z i * (φ z * ψ z i)) volume) →
                @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                  (fun (z : ParabolicPoint) =>
                    ∑ i : Fin (3 : ℕ), localizedDivergenceG φ u Du p f z i * ψ z i)
                  volume
    := by
  intro u Du p f φ ψ hGtime hGconv hGgrad hGpress hGforce
  have hGi (i : Fin 3) : Integrable
      (fun z : ParabolicPoint =>
        localizedDivergenceG φ u Du p f z i * ψ z i) volume := by
    have h2 : Integrable (fun z : ParabolicPoint => ∑ j,
        u z i * u z j * (spatialPartial φ j z * ψ z i)) volume :=
      integrable_finsetSum (Finset.univ : Finset (Fin 3))
        (fun j _ => hGconv i j)
    have h3 : Integrable (fun z : ParabolicPoint => ∑ j,
        Du z i j * (spatialPartial φ j z * ψ z i)) volume :=
      integrable_finsetSum (Finset.univ : Finset (Fin 3))
        (fun j _ => hGgrad i j)
    have h4 := hGpress i
    have h5 := hGforce i
    have hsum := (hGtime i).add (h2.sub (h3.sub (h4.add h5)))
    refine hsum.congr (Filter.Eventually.of_forall (fun z => ?_))
    simp only [localizedDivergenceG, Pi.add_apply, Pi.sub_apply, add_mul,
      sub_mul, Finset.sum_mul]
    simp_rw [mul_assoc, mul_left_comm, mul_comm]
    ring
  exact integrable_finsetSum (Finset.univ : Finset (Fin 3))
    (fun i _ => hGi i)

private lemma localized_divergence_tested_hH_2 :
    ∀ {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {φ : Vec3 × ℝ → ℝ} {ψ : Vec3 × ℝ → Vec3},
      (∀ (i j : Fin (3 : ℕ)),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
            (fun (z : ParabolicPoint) =>
              φ z * u z i * u z j * spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z)
            volume) →
        (∀ (i j : Fin (3 : ℕ)),
            @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
              (fun (z : ParabolicPoint) =>
                u z i * spatialPartial φ j z *
                  spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z)
              volume) →
          (∀ (i : Fin (3 : ℕ)),
              @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                (fun (z : ParabolicPoint) =>
                  p z * φ z * spatialPartial (fun (w : ParabolicPoint) => ψ w i) i z)
                volume) →
            @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
              (fun (z : ParabolicPoint) =>
                ∑ i : Fin (3 : ℕ),
                  ∑ j : Fin (3 : ℕ),
                    localizedDivergenceH φ u p j z i *
                      spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z)
              volume
    := by
  intro u p φ ψ hHconv hHgrad hHpress
  have hHij (i j : Fin 3) : Integrable
      (fun z : ParabolicPoint => localizedDivergenceH φ u p j z i *
        spatialPartial (fun w => ψ w i) j z) volume := by
    by_cases hij : i = j
    · subst j
      have hsum := (hHconv i i).add (hHgrad i i)
      have hsum' := hsum.add (hHpress i)
      refine hsum'.congr (Filter.Eventually.of_forall (fun z => ?_))
      simp only [Pi.add_apply, localizedDivergenceH, ↓reduceIte]
      ring
    · have hsum := (hHconv i j).add (hHgrad i j)
      refine hsum.congr (Filter.Eventually.of_forall (fun z => ?_))
      simp only [Pi.add_apply, localizedDivergenceH, hij, ↓reduceIte, add_zero]
      ring
  exact integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ =>
    integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => hHij i j))

private lemma localized_divergence_tested_hRF_3 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {Ω' : Set Vec3}
      {J : Set ℝ} {ψ : Vec3 × ℝ → Vec3},
      (∀ (i : Fin (3 : ℕ)),
          ∀ᵐ (s : ℝ) ∂Measure.restrict volume J,
            HasWeakGradientOn Ω' (fun (x : Vec (3 : ℕ)) => u (x, s) i) fun (x : Vec (3 : ℕ)) =>
              Du (x, s) i) →
        let φp : ParabolicPoint → ℝ := fun (z : ParabolicPoint) => φ (z.1, z.2);
        (φp =
            have this : ParabolicPoint → ℝ := φ;
            this) →
          let ψp : ParabolicPoint → Vec3 := fun (z : ParabolicPoint) => ψ (z.1, z.2);
          (ψp =
              have this : ParabolicPoint → Vec3 := ψ;
              this) →
            (∀ (i : Fin (3 : ℕ)) (z : ParabolicPoint),
                timePartial (fun (w : ParabolicPoint) => (φ • ψ) w i) z =
                  timePartial φp z * ψp z i +
                    φp z * timePartial (fun (w : ParabolicPoint) => ψ w i) z) →
              (∀ (i j : Fin (3 : ℕ)) (z : ParabolicPoint),
                  spatialPartial (fun (w : ParabolicPoint) => (φ • ψ) w i) j z =
                    spatialPartial φp j z * ψp z i +
                      φp z * spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z) →
                let R : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
                  HSub.hSub (α := ℝ)
                          (-∑ i : Fin (3 : ℕ),
                              u z i * timePartial (fun (w : ParabolicPoint) => (φ • ψ) w i) z)
                          (∑ i : Fin (3 : ℕ),
                            ∑ j : Fin (3 : ℕ),
                              u z i * u z j *
                                spatialPartial (fun (w : ParabolicPoint) => (φ • ψ) w i) j z) +
                        ∑ i : Fin (3 : ℕ),
                          ∑ j : Fin (3 : ℕ),
                            Du z i j *
                              spatialPartial (fun (w : ParabolicPoint) => (φ • ψ) w i) j z -
                      p z *
                        ∑ i : Fin (3 : ℕ),
                          spatialPartial (fun (w : ParabolicPoint) => (φ • ψ) w i) i z -
                    ∑ i : Fin (3 : ℕ), f z i * (φ • ψ) z i;
                let F : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
                  HSub.hSub (α := ℝ)
                          (-∑ i : Fin (3 : ℕ),
                              u z i * (φp z * timePartial (fun (w : ParabolicPoint) => ψp w i) z))
                          (∑ i : Fin (3 : ℕ),
                            ∑ j : Fin (3 : ℕ),
                              u z i * u z j *
                                (φp z * spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z)) +
                        ∑ i : Fin (3 : ℕ),
                          ∑ j : Fin (3 : ℕ),
                            Du z i j *
                              (φp z * spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z) -
                      p z *
                        ∑ i : Fin (3 : ℕ),
                          φp z * spatialPartial (fun (w : ParabolicPoint) => ψp w i) i z -
                    ∑ i : Fin (3 : ℕ), localizedDivergenceG φ u Du p f z i * ψp z i;
                R = F
    := by
  intro u Du p f φ Ω' J ψ hgrad φp hφp_eq ψp hψp_eq htimeProd hspaceProd R F
  funext z
  dsimp [R, F]
  simp_rw [htimeProd, hspaceProd]
  have hforce (i : Fin 3) : (φ • ψ) z i = φp z * ψp z i := by
    rfl
  simp_rw [hforce]
  have hGpoint (i : Fin 3) :
      localizedDivergenceG φ u Du p f z i * ψp z i =
        (timePartial (show ParabolicPoint → ℝ from φ) z * u z i +
          ∑ j, u z i * u z j * spatialPartial φp j z -
          ∑ j, Du z i j *
            spatialPartial φp j z +
          p z * spatialPartial φp i z +
          f z i * φp z) * ψp z i := by
    rfl
  simp_rw [hGpoint]
  simp only [Finset.sum_add_distrib, add_mul, sub_mul, Finset.sum_mul]
  simp only [mul_add]
  have hconv (i : Fin 3) :
      (∑ j, u z i * u z j *
          (spatialPartial φp j z * ψp z i)) =
        ∑ j, u z i * u z j * spatialPartial φp j z * ψp z i := by
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hgrad (i : Fin 3) :
      (∑ j, Du z i j *
          (spatialPartial φp j z * ψp z i)) =
        ∑ j, Du z i j * spatialPartial φp j z * ψp z i := by
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hconvAll :
      (∑ i, ∑ j, u z i * u z j *
        (spatialPartial φp j z * ψp z i)) =
        ∑ i, ∑ j, u z i * u z j * spatialPartial φp j z * ψp z i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hconv i
  have hgradAll :
      (∑ i, ∑ j, Du z i j *
        (spatialPartial φp j z * ψp z i)) =
        ∑ i, ∑ j, Du z i j * spatialPartial φp j z * ψp z i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hgrad i
  rw [hconvAll, hgradAll, hφp_eq, hψp_eq]
  simp only [Finset.mul_sum]
  simp_rw [mul_assoc, mul_left_comm, mul_comm]
  abel

private lemma localized_divergence_tested_hFzero_4 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {ψ : Vec3 × ℝ → Vec3},
      ContDiff ℝ (⊤ : ℕ∞) φ →
        tsupport φ ⊆ spaceTimeSet Ω I →
          let φp : ParabolicPoint → ℝ := fun (z : ParabolicPoint) => φ (z.1, z.2);
          (φp =
              have this : ParabolicPoint → ℝ := φ;
              this) →
            let ψp : ParabolicPoint → Vec3 := fun (z : ParabolicPoint) => ψ (z.1, z.2);
            let F : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
              HSub.hSub (α := ℝ)
                      (-∑ i : Fin (3 : ℕ),
                          u z i * (φp z * timePartial (fun (w : ParabolicPoint) => ψp w i) z))
                      (∑ i : Fin (3 : ℕ),
                        ∑ j : Fin (3 : ℕ),
                          u z i * u z j *
                            (φp z * spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z)) +
                    ∑ i : Fin (3 : ℕ),
                      ∑ j : Fin (3 : ℕ),
                        Du z i j *
                          (φp z * spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z) -
                  p z *
                    ∑ i : Fin (3 : ℕ),
                      φp z * spatialPartial (fun (w : ParabolicPoint) => ψp w i) i z -
                ∑ i : Fin (3 : ℕ), localizedDivergenceG φ u Du p f z i * ψp z i;
            ∀ z ∉ spaceTimeSet Ω I, F z = (0 : ℝ)
    := by
  intro Ω I u Du p f φ ψ hφd hφΩ φp hφp_eq ψp F z hz
  have hnot : parabolicHomeomorph z ∉ tsupport φ := by
    intro hzφ
    apply hz
    rw [show spaceTimeSet Ω I = parabolicHomeomorph ⁻¹' (Ω ×ˢ I) by
      rw [spaceTimeSet, parabolicHomeomorph_preimage]]
    exact hφΩ hzφ
  have hφzero : φ (z.1, z.2) = 0 :=
    image_eq_zero_of_notMem_tsupport hnot
  have hφzero' : φ z = 0 := by
    change φ (z.1, z.2) = 0
    exact hφzero
  have htzero : timePartial φ (z.1, z.2) = 0 :=
    timePartial_zero_of_not_mem_tsupport_public hφd hnot
  have htzero' : timePartial φ z = 0 := by
    change timePartial φ (z.1, z.2) = 0
    exact htzero
  have hszero (j : Fin 3) : spatialPartial φ j (z.1, z.2) = 0 :=
    spatialPartial_zero_of_not_mem_tsupport_public hφd hnot j
  have hszero' (j : Fin 3) : spatialPartial φ j z = 0 := by
    change spatialPartial φ j (z.1, z.2) = 0
    exact hszero j
  have hφpzero : φp z = 0 := by
    rw [hφp_eq]
    exact hφzero'
  simp only [localizedDivergenceG, hφpzero, zero_mul, mul_zero, Finset.sum_const_zero,
    neg_zero, sub_self, add_zero, htzero', hszero', hφzero', F]

private lemma localized_divergence_tested_hK_5 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {φ : Vec3 × ℝ → ℝ}
      {ψ : Vec3 × ℝ → Vec3},
      @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
          (fun (z : ParabolicPoint) =>
            ∑ i : Fin (3 : ℕ),
              ∑ j : Fin (3 : ℕ),
                Du z i j * (φ z * spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z))
          volume →
        let φp : ParabolicPoint → ℝ := fun (z : ParabolicPoint) => φ (z.1, z.2);
        (φp =
            have this : ParabolicPoint → ℝ := φ;
            this) →
          let ψp : ParabolicPoint → Vec3 := fun (z : ParabolicPoint) => ψ (z.1, z.2);
          (ψp =
              have this : ParabolicPoint → Vec3 := ψ;
              this) →
            let U : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
              ∑ i : Fin (3 : ℕ),
                ∑ j : Fin (3 : ℕ),
                  u z i * spatialPartial φp j z *
                    spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z;
            let K : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
              ∑ i : Fin (3 : ℕ),
                ∑ j : Fin (3 : ℕ),
                  (φp z * Du z i j + u z i * spatialPartial φp j z) *
                    spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z;
            @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace U volume →
              @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace K volume
    := by
  intro u Du φ ψ hLgrad φp hφp_eq ψp hψp_eq U K hU
  have hC : Integrable (fun z => ∑ i, ∑ j,
      Du z i j * (φp z * spatialPartial (fun w => ψp w i) j z)) volume := by
    rw [hφp_eq, hψp_eq]
    exact hLgrad
  have hCU := hC.add hU
  refine hCU.congr (Filter.Eventually.of_forall (fun z => ?_))
  dsimp [K, U]
  simp only [Finset.sum_add_distrib, add_mul]
  have hfirst :
      (∑ i, ∑ j, Du z i j * (φp z * spatialPartial
          (fun w => ψp w i) j z)) =
        ∑ i, ∑ j, φp z * Du z i j * spatialPartial
          (fun w => ψp w i) j z := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hfirst]

private lemma localized_divergence_tested_hLap'_6 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {φ : Vec3 × ℝ → ℝ}
      {ψ : Vec3 × ℝ → Vec3},
      let φp : ParabolicPoint → ℝ := fun (z : ParabolicPoint) => φ (z.1, z.2);
      let ψp : ParabolicPoint → Vec3 := fun (z : ParabolicPoint) => ψ (z.1, z.2);
      Eq (α := ℝ)
          (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (z : Vec3 × ℝ) =>
            ∑ i : Fin (3 : ℕ),
              φ z * u z i *
                ∑ j : Fin (3 : ℕ), spatialSecondPartial (fun (w : ParabolicPoint) => ψ w i) j j z)
          (-@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (z : Vec3 × ℝ) =>
              ∑ i : Fin (3 : ℕ),
                ∑ j : Fin (3 : ℕ),
                  (φ z * Du z i j + u z i * spatialPartial φ j z) *
                    spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z) →
        let B : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
          ∑ i : Fin (3 : ℕ),
            ∑ j : Fin (3 : ℕ),
              u z i * (φp z * spatialSecondPartial (fun (w : ParabolicPoint) => ψp w i) j j z);
        let K : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
          ∑ i : Fin (3 : ℕ),
            ∑ j : Fin (3 : ℕ),
              (φp z * Du z i j + u z i * spatialPartial φp j z) *
                spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z;
        Eq (α := ℝ)
          (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (z : ParabolicPoint) => B z)
          (-@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (z : ParabolicPoint) => K z)
    := by
  intro u Du φ ψ φp ψp hLap B K
  have hLap₀ :
      (∫ z : ParabolicPoint, ∑ i, φp z * u z i * ∑ j,
        spatialSecondPartial (fun w => ψp w i) j j z) =
        -∫ z : ParabolicPoint, ∑ i, ∑ j,
          (φp z * Du z i j + u z i * spatialPartial φp j z) *
            spatialPartial (fun w => ψp w i) j z := by
    rw [Integration.volume_parabolicPoint_eq_prod]
    change (∫ z : Vec3 × ℝ, ∑ i, φ z * u z i * ∑ j,
        spatialSecondPartial (fun w : Vec3 × ℝ => ψ w i) j j z) =
      -∫ z : Vec3 × ℝ, ∑ i, ∑ j,
        (φ z * Du z i j + u z i * spatialPartial φ j z) *
          spatialPartial (fun w : Vec3 × ℝ => ψ w i) j z
    exact hLap
  calc
    (∫ z, B z) = ∫ z, ∑ i, φp z * u z i * ∑ j,
        spatialSecondPartial (fun w => ψp w i) j j z := by
      apply integral_congr_ae
      filter_upwards [] with z
      dsimp [B]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = -∫ z, K z := by simpa only [K] using hLap₀

private lemma localized_divergence_tested_hpointInt_7 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {ψ : Vec3 × ℝ → Vec3},
      let φp : ParabolicPoint → ℝ := fun (z : ParabolicPoint) => φ (z.1, z.2);
      let ψp : ParabolicPoint → Vec3 := fun (z : ParabolicPoint) => ψ (z.1, z.2);
      let F : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        HSub.hSub (α := ℝ)
                (-∑ i : Fin (3 : ℕ),
                    u z i * (φp z * timePartial (fun (w : ParabolicPoint) => ψp w i) z))
                (∑ i : Fin (3 : ℕ),
                  ∑ j : Fin (3 : ℕ),
                    u z i * u z j *
                      (φp z * spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z)) +
              ∑ i : Fin (3 : ℕ),
                ∑ j : Fin (3 : ℕ),
                  Du z i j * (φp z * spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z) -
            p z *
              ∑ i : Fin (3 : ℕ), φp z * spatialPartial (fun (w : ParabolicPoint) => ψp w i) i z -
          ∑ i : Fin (3 : ℕ), localizedDivergenceG φ u Du p f z i * ψp z i;
      @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace F volume →
        let A : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
          ∑ i : Fin (3 : ℕ), u z i * (φp z * timePartial (fun (w : ParabolicPoint) => ψp w i) z);
        let G₀ : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
          ∑ i : Fin (3 : ℕ), localizedDivergenceG φ u Du p f z i * ψp z i;
        let H₀ : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
          ∑ i : Fin (3 : ℕ),
            ∑ j : Fin (3 : ℕ),
              localizedDivergenceH φ u p j z i *
                spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z;
        let K : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
          ∑ i : Fin (3 : ℕ),
            ∑ j : Fin (3 : ℕ),
              (φp z * Du z i j + u z i * spatialPartial φp j z) *
                spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z;
        @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace A volume →
          @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace G₀ volume →
            @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace H₀ volume →
              @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace K volume →
                (∀ (z : ParabolicPoint), F z + G₀ z + H₀ z = -A z + K z) →
                  (HAdd.hAdd (α := ℝ)
                        (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume
                          fun (z : ParabolicPoint) => F z)
                        (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume
                          fun (z : ParabolicPoint) => G₀ z) +
                      @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume
                        fun (z : ParabolicPoint) => H₀ z) =
                    HAdd.hAdd (α := ℝ)
                      (-@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume
                          fun (z : ParabolicPoint) => A z)
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume
                        fun (z : ParabolicPoint) => K z)
    := by
  intro u Du p f φ ψ φp ψp F hF A G₀ H₀ K hA hG₀ hH₀ hK hpoint
  calc
    _ = (∫ z, F z + G₀ z) + (∫ z, H₀ z) := by
      rw [integral_add hF hG₀]
    _ = ∫ z, (F z + G₀ z) + H₀ z := by
      symm
      exact integral_add (hF.add hG₀) hH₀
    _ = ∫ z, -A z + K z := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = _ := by
      calc
        (∫ z, -A z + K z) = (∫ z, -A z) + (∫ z, K z) :=
          integral_add hA.neg hK
        _ = _ := by rw [integral_neg]

private lemma localized_divergence_tested_hHij_8 :
    ∀ {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {φ : Vec3 × ℝ → ℝ} {ψ : Vec3 × ℝ → Vec3},
      (∀ (i j : Fin (3 : ℕ)),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
            (fun (z : ParabolicPoint) =>
              φ z * u z i * u z j * spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z)
            volume) →
        (∀ (i j : Fin (3 : ℕ)),
            @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
              (fun (z : ParabolicPoint) =>
                u z i * spatialPartial φ j z *
                  spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z)
              volume) →
          (∀ (i : Fin (3 : ℕ)),
              @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                (fun (z : ParabolicPoint) =>
                  p z * φ z * spatialPartial (fun (w : ParabolicPoint) => ψ w i) i z)
                volume) →
            ∀ (i j : Fin (3 : ℕ)),
              @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                (fun (z : ParabolicPoint) =>
                  localizedDivergenceH φ u p j z i *
                    spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z)
                volume
    := by
  intro u p φ ψ hHconv hHgrad hHpress i j
  by_cases hij : i = j
  · subst j
    have hs := (hHconv i i).add (hHgrad i i)
    refine (hs.add (hHpress i)).congr
      (Filter.Eventually.of_forall (fun z => ?_))
    simp only [Pi.add_apply, localizedDivergenceH, ↓reduceIte]
    ring
  · have hs := (hHconv i j).add (hHgrad i j)
    refine hs.congr (Filter.Eventually.of_forall (fun z => ?_))
    simp only [Pi.add_apply, localizedDivergenceH, hij, ↓reduceIte, add_zero]
    ring

private lemma localized_divergence_tested_hHsum_9 :
    ∀ {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {φ : Vec3 × ℝ → ℝ} {ψ : Vec3 × ℝ → Vec3},
      let ψp : ParabolicPoint → Vec3 := fun (z : ParabolicPoint) => ψ (z.1, z.2);
      (ψp =
          have this : ParabolicPoint → Vec3 := ψ;
          this) →
        let H₀ : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
          ∑ i : Fin (3 : ℕ),
            ∑ j : Fin (3 : ℕ),
              localizedDivergenceH φ u p j z i *
                spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z;
        (∀ (i j : Fin (3 : ℕ)),
            @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
              (fun (z : ParabolicPoint) =>
                localizedDivergenceH φ u p j z i *
                  spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z)
              volume) →
          Eq (α := ℝ)
            (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (z : ParabolicPoint) =>
              H₀ z)
            (∑ i : Fin (3 : ℕ),
              ∑ j : Fin (3 : ℕ),
                @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (z : ParabolicPoint) =>
                  localizedDivergenceH φ u p j z i *
                    spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z)
    := by
  intro u p φ ψ ψp hψp_eq H₀ hHij
  rw [show H₀ = fun z => ∑ i, ∑ j,
    localizedDivergenceH φ u p j z i * spatialPartial
      (fun w => ψ w i) j z by
    funext z
    dsimp [H₀]
    rw [hψp_eq]]
  change (∫ z, ∑ i, ∑ j,
    localizedDivergenceH φ u p j z i * spatialPartial
      (fun w => ψ w i) j z) = _
  rw [integral_finsetSum (s := (Finset.univ : Finset (Fin 3)))]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum (s := (Finset.univ : Finset (Fin 3)))]
    intro j hj
    exact hHij i j
  · intro i hi
    exact integrable_finsetSum (Finset.univ : Finset (Fin 3))
      (fun j _ => hHij i j)

private lemma localized_divergence_tested_hφtime_c_1 :
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

private lemma localized_divergence_tested_hφtime_ts_2 :
    ∀ {φ : Vec3 × ℝ → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) φ →
        (tsupport (α := ℝ) fun (z : Vec3 × ℝ) => timePartial φ z) ⊆ tsupport φ
    := by
  intro φ hφd
  apply closure_minimal
  · intro z hz
    by_contra hnot
    apply hz
    exact timePartial_zero_of_not_mem_tsupport_public hφd hnot
  · exact isClosed_tsupport φ

private lemma localized_divergence_tested_hφsp_c_3 :
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

private lemma localized_divergence_tested_hφsp_ts_4 :
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

private lemma localized_divergence_tested_hbox_factor_5 :
    ∀ {_ : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {Ω' : Set Vec3} {J : Set ℝ},
      tsupport φ ⊆ Ω' ×ˢ J →
        let μ : Measure ParabolicPoint := Measure.restrict volume (spaceTimeSet Ω' J);
        ∀ {a : ParabolicPoint → ℝ},
          Integrable a μ →
            ∀ {α : Vec3 × ℝ → ℝ},
              HasCompactSupport α →
                tsupport α ⊆ tsupport φ →
                  Continuous α →
                    ∀ {b : Vec3 × ℝ → ℝ},
                      Continuous b →
                        @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                          (fun (z : ParabolicPoint) => a z * (α z * b z)) volume
    := by
  intro f φ Ω' J hφbox μ a ha α hαc hαts hα b hb
  have hbc : HasCompactSupport (fun z : Vec3 × ℝ => α z * b z) :=
    hαc.mul_right (f' := b)
  have hbs : tsupport (fun z : Vec3 × ℝ => α z * b z) ⊆
      (spaceTimeSet Ω' J : Set (Vec3 × ℝ)) := by
    exact (tsupport_mul_subset_left (f := α) (g := b)).trans
      (hαts.trans hφbox)
  exact compact_factor_integrable (a := a)
    (b := fun z : Vec3 × ℝ => α z * b z)
    (by simpa only [μ] using ha) (hα.mul hb) hbc hbs

private lemma localized_divergence_tested_hLpress_6 :
    ∀ {p : ParabolicPoint → ℝ} {φ : Vec3 × ℝ → ℝ} {ψ : Vec3 × ℝ → Vec3},
      (∀ (i : Fin (3 : ℕ)),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
            (fun (z : ParabolicPoint) =>
              p z * (φ z * spatialPartial (fun (w : ParabolicPoint) => ψ w i) i z))
            volume) →
        @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
          (fun (z : ParabolicPoint) =>
            p z * ∑ i : Fin (3 : ℕ), φ z * spatialPartial (fun (w : ParabolicPoint) => ψ w i) i z)
          volume
    := by
  intro p φ ψ hPressPsi
  have hi : Integrable (fun z => ∑ i,
      p z * (φ z * spatialPartial (fun w => ψ w i) i z)) volume :=
    integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ => hPressPsi i)
  convert hi using 1
  funext z
  rw [Finset.mul_sum]

private lemma localized_divergence_tested_hFglobal_7 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {ψ : Vec3 × ℝ → Vec3},
      let φp : ParabolicPoint → ℝ := fun (z : ParabolicPoint) => φ (z.1, z.2);
      let ψp : ParabolicPoint → Vec3 := fun (z : ParabolicPoint) => ψ (z.1, z.2);
      let R : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        HSub.hSub (α := ℝ)
                (-∑ i : Fin (3 : ℕ),
                    u z i * timePartial (fun (w : ParabolicPoint) => (φ • ψ) w i) z)
                (∑ i : Fin (3 : ℕ),
                  ∑ j : Fin (3 : ℕ),
                    u z i * u z j * spatialPartial (fun (w : ParabolicPoint) => (φ • ψ) w i) j z) +
              ∑ i : Fin (3 : ℕ),
                ∑ j : Fin (3 : ℕ),
                  Du z i j * spatialPartial (fun (w : ParabolicPoint) => (φ • ψ) w i) j z -
            p z * ∑ i : Fin (3 : ℕ), spatialPartial (fun (w : ParabolicPoint) => (φ • ψ) w i) i z -
          ∑ i : Fin (3 : ℕ), f z i * (φ • ψ) z i;
      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume (spaceTimeSet Ω I))
            fun (z : ParabolicPoint) => R z) =
          (0 : ℝ) →
        let F : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
          HSub.hSub (α := ℝ)
                  (-∑ i : Fin (3 : ℕ),
                      u z i * (φp z * timePartial (fun (w : ParabolicPoint) => ψp w i) z))
                  (∑ i : Fin (3 : ℕ),
                    ∑ j : Fin (3 : ℕ),
                      u z i * u z j *
                        (φp z * spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z)) +
                ∑ i : Fin (3 : ℕ),
                  ∑ j : Fin (3 : ℕ),
                    Du z i j * (φp z * spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z) -
              p z *
                ∑ i : Fin (3 : ℕ), φp z * spatialPartial (fun (w : ParabolicPoint) => ψp w i) i z -
            ∑ i : Fin (3 : ℕ), localizedDivergenceG φ u Du p f z i * ψp z i;
        R = F →
          (have ψp : ParabolicPoint → Vec3 := fun (z : ParabolicPoint) => ψ (z.1, z.2);
            have F : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
              HSub.hSub (α := ℝ)
                      (-∑ i : Fin (3 : ℕ),
                          u z i *
                            ((fun (z : ParabolicPoint) => φ (z.1, z.2)) z *
                              timePartial (fun (w : ParabolicPoint) => ψp w i) z))
                      (∑ i : Fin (3 : ℕ),
                        ∑ j : Fin (3 : ℕ),
                          u z i * u z j *
                            ((fun (z : ParabolicPoint) => φ (z.1, z.2)) z *
                              spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z)) +
                    ∑ i : Fin (3 : ℕ),
                      ∑ j : Fin (3 : ℕ),
                        Du z i j *
                          ((fun (z : ParabolicPoint) => φ (z.1, z.2)) z *
                            spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z) -
                  p z *
                    ∑ i : Fin (3 : ℕ),
                      (fun (z : ParabolicPoint) => φ (z.1, z.2)) z *
                        spatialPartial (fun (w : ParabolicPoint) => ψp w i) i z -
                ∑ i : Fin (3 : ℕ), localizedDivergenceG φ u Du p f z i * ψp z i;
            ∀ z ∉ spaceTimeSet Ω I, F z = (0 : ℝ)) →
            (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (z : ParabolicPoint) =>
                F z) =
              (0 : ℝ)
    := by
  intro Ω I u Du p f φ ψ φp ψp R hS3zero F hRF hFzero
  calc
    (∫ z, F z) = ∫ z in spaceTimeSet Ω I, F z := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hFzero]
    _ = ∫ z in spaceTimeSet Ω I, R z := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => hRF.symm ▸ rfl)
    _ = 0 := hS3zero

private lemma localized_divergence_tested_hU_8 :
    ∀ {u : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {ψ : Vec3 × ℝ → Vec3},
      (∀ (i j : Fin (3 : ℕ)),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
            (fun (z : ParabolicPoint) =>
              u z i * spatialPartial φ j z * spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z)
            volume) →
        let φp : ParabolicPoint → ℝ := fun (z : ParabolicPoint) => φ (z.1, z.2);
        (φp =
            have this : ParabolicPoint → ℝ := φ;
            this) →
          let ψp : ParabolicPoint → Vec3 := fun (z : ParabolicPoint) => ψ (z.1, z.2);
          (ψp =
              have this : ParabolicPoint → Vec3 := ψ;
              this) →
            let U : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
              ∑ i : Fin (3 : ℕ),
                ∑ j : Fin (3 : ℕ),
                  u z i * spatialPartial φp j z *
                    spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z;
            @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace U volume
    := by
  intro u φ ψ hHgrad φp hφp_eq ψp hψp_eq U
  have hU' : Integrable (fun z => ∑ i, ∑ j,
      u z i * spatialPartial φ j z * spatialPartial
        (fun w => ψ w i) j z) volume :=
    integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ =>
      integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ =>
        hHgrad i j))
  dsimp [U]
  rw [hφp_eq, hψp_eq]
  exact hU'

open scoped Classical in
private lemma localized_divergence_tested_hpoint_9 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {ψ : Vec3 × ℝ → Vec3},
      let φp : ParabolicPoint → ℝ := fun (z : ParabolicPoint) => φ (z.1, z.2);
      let ψp : ParabolicPoint → Vec3 := fun (z : ParabolicPoint) => ψ (z.1, z.2);
      let F : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        HSub.hSub (α := ℝ)
                (-∑ i : Fin (3 : ℕ),
                    u z i * (φp z * timePartial (fun (w : ParabolicPoint) => ψp w i) z))
                (∑ i : Fin (3 : ℕ),
                  ∑ j : Fin (3 : ℕ),
                    u z i * u z j *
                      (φp z * spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z)) +
              ∑ i : Fin (3 : ℕ),
                ∑ j : Fin (3 : ℕ),
                  Du z i j * (φp z * spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z) -
            p z *
              ∑ i : Fin (3 : ℕ), φp z * spatialPartial (fun (w : ParabolicPoint) => ψp w i) i z -
          ∑ i : Fin (3 : ℕ), localizedDivergenceG φ u Du p f z i * ψp z i;
      let A : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        ∑ i : Fin (3 : ℕ), u z i * (φp z * timePartial (fun (w : ParabolicPoint) => ψp w i) z);
      let G₀ : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        ∑ i : Fin (3 : ℕ), localizedDivergenceG φ u Du p f z i * ψp z i;
      let H₀ : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        ∑ i : Fin (3 : ℕ),
          ∑ j : Fin (3 : ℕ),
            localizedDivergenceH φ u p j z i *
              spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z;
      let K : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        ∑ i : Fin (3 : ℕ),
          ∑ j : Fin (3 : ℕ),
            (φp z * Du z i j + u z i * spatialPartial φp j z) *
              spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z;
      (∀ (z : ParabolicPoint),
          Eq (α := ℝ)
            (∑ i : Fin (3 : ℕ),
              ∑ j : Fin (3 : ℕ),
                (if i = j then p z * φp z else (0 : ℝ)) *
                  spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z)
            (∑ i : Fin (3 : ℕ),
              p z * φp z * spatialPartial (fun (w : ParabolicPoint) => ψp w i) i z)) →
        (∀ (z : ParabolicPoint) (i : Fin (3 : ℕ)),
            localizedDivergenceG φ u Du p f z i * ψp z i =
              (timePartial φp z * u z i + ∑ j : Fin (3 : ℕ), u z i * u z j * spatialPartial φp j z -
                      ∑ j : Fin (3 : ℕ), Du z i j * spatialPartial φp j z +
                    p z * spatialPartial φp i z +
                  f z i * φp z) *
                ψp z i) →
          (∀ (z : ParabolicPoint) (i j : Fin (3 : ℕ)),
              localizedDivergenceH φ u p j z i *
                  spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z =
                (φp z * u z i * u z j + u z i * spatialPartial φp j z +
                    if i = j then p z * φp z else (0 : ℝ)) *
                  spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z) →
            ∀ (z : ParabolicPoint), F z + G₀ z + H₀ z = -A z + K z
    := by
  intro u Du p f φ ψ φp ψp F A G₀ H₀ K hdiag hGpoint₀ hHpoint₀ z
  dsimp [F, A, G₀, H₀, K]
  simp_rw [hGpoint₀, hHpoint₀]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, add_mul,
    sub_mul, Finset.sum_mul, Finset.mul_sum]
  rw [hdiag]
  simp_rw [mul_assoc, mul_left_comm, mul_comm]
  abel

private lemma localized_divergence_tested_hConvPsi_1 :
    ∀ {u : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {Ω' : Set Vec3} {J : Set ℝ}
      {ψ : Vec3 × ℝ → Vec3},
      ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ →
          let μ : Measure ParabolicPoint := Measure.restrict volume (spaceTimeSet Ω' J);
          (∀ (i j : Fin (3 : ℕ)),
              ContDiff ℝ (F := ℝ) (⊤ : ℕ∞) fun (z : Vec3 × ℝ) =>
                spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z) →
            (∀ {a : ParabolicPoint → ℝ},
                Integrable a μ →
                  ∀ {α : Vec3 × ℝ → ℝ},
                    HasCompactSupport α →
                      tsupport α ⊆ tsupport φ →
                        Continuous α →
                          ∀ {b : Vec3 × ℝ → ℝ},
                            Continuous b →
                              @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                                (fun (z : ParabolicPoint) => a z * (α z * b z)) volume) →
              (∀ (i j : Fin (3 : ℕ)),
                  Integrable (ε := ℝ) (fun (z : ParabolicPoint) => u z i * u z j) μ) →
                ∀ (i j : Fin (3 : ℕ)),
                  @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                    (fun (z : ParabolicPoint) =>
                      u z i * u z j *
                        (φ z * spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z))
                    volume
    := by
  intro u φ Ω' J ψ hφd hφc μ hψsp hbox_factor hUU i j
  have h := hbox_factor (hUU i j) hφc (by exact subset_rfl) hφd.continuous
    (hψsp i j).continuous
  convert h using 1

private lemma localized_divergence_tested_hForce_2 :
    ∀ {q : ℝ} {f : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {Ω' : Set Vec3} {J : Set ℝ}
      {ψ : Vec3 × ℝ → Vec3},
      ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ →
          let μ : Measure ParabolicPoint := Measure.restrict volume (spaceTimeSet Ω' J);
          IsFiniteMeasure μ →
            (1 : ℝ≥0∞) ≤ ENNReal.ofReal q →
              (∀ (i : Fin (3 : ℕ)),
                  ContDiff ℝ (F := ℝ) (⊤ : ℕ∞) fun (z : Vec3 × ℝ) => ψ z i) →
                (∀ {a : ParabolicPoint → ℝ},
                    Integrable a μ →
                      ∀ {α : Vec3 × ℝ → ℝ},
                        HasCompactSupport α →
                          tsupport α ⊆ tsupport φ →
                            Continuous α →
                              ∀ {b : Vec3 × ℝ → ℝ},
                                Continuous b →
                                  @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                                    (fun (z : ParabolicPoint) => a z * (α z * b z)) volume) →
                  (∀ (i : Fin (3 : ℕ)),
                      MemLp (ε := ℝ) (fun (z : ParabolicPoint) => f z i) (ENNReal.ofReal q) μ) →
                    ∀ (i : Fin (3 : ℕ)),
                      @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                        (fun (z : ParabolicPoint) => f z i * (φ z * ψ z i)) volume
    := by
  intro q f φ Ω' J ψ hφd hφc μ this hq1 hψi hbox_factor hfComp i
  exact hbox_factor ((hfComp i).integrable hq1) hφc (by exact subset_rfl)
    hφd.continuous
    (hψi i).continuous

private lemma localized_divergence_tested_hGconv_3 :
    ∀ {u : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {Ω' : Set Vec3} {J : Set ℝ}
      {ψ : Vec3 × ℝ → Vec3},
      let μ : Measure ParabolicPoint := Measure.restrict volume (spaceTimeSet Ω' J);
      (∀ (j : Fin (3 : ℕ)),
          ContDiff ℝ (F := ℝ) (⊤ : ℕ∞) fun (z : Vec3 × ℝ) => spatialPartial φ j z) →
        (∀ (j : Fin (3 : ℕ)),
            HasCompactSupport (β := ℝ) fun (z : Vec3 × ℝ) => spatialPartial φ j z) →
          (∀ (j : Fin (3 : ℕ)),
              (tsupport (α := ℝ) fun (z : Vec3 × ℝ) => spatialPartial φ j z) ⊆ tsupport φ) →
            (∀ (i : Fin (3 : ℕ)),
                ContDiff ℝ (F := ℝ) (⊤ : ℕ∞) fun (z : Vec3 × ℝ) => ψ z i) →
              (∀ {a : ParabolicPoint → ℝ},
                  Integrable a μ →
                    ∀ {α : Vec3 × ℝ → ℝ},
                      HasCompactSupport α →
                        tsupport α ⊆ tsupport φ →
                          Continuous α →
                            ∀ {b : Vec3 × ℝ → ℝ},
                              Continuous b →
                                @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                                  (fun (z : ParabolicPoint) => a z * (α z * b z)) volume) →
                (∀ (i j : Fin (3 : ℕ)),
                    Integrable (ε := ℝ) (fun (z : ParabolicPoint) => u z i * u z j) μ) →
                  ∀ (i j : Fin (3 : ℕ)),
                    @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                      (fun (z : ParabolicPoint) => u z i * u z j * (spatialPartial φ j z * ψ z i))
                      volume
    := by
  intro u φ Ω' J ψ μ hφsp hφsp_c hφsp_ts hψi hbox_factor hUU i j
  have h := hbox_factor (hUU i j) (hφsp_c j) (hφsp_ts j)
    (hφsp j).continuous
    (hψi i).continuous
  convert h using 1

private lemma localized_divergence_tested_hGgrad_4 :
    ∀ {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {φ : Vec3 × ℝ → ℝ} {Ω' : Set Vec3} {J : Set ℝ}
      {ψ : Vec3 × ℝ → Vec3},
      let μ : Measure ParabolicPoint := Measure.restrict volume (spaceTimeSet Ω' J);
      (∀ (j : Fin (3 : ℕ)),
          ContDiff ℝ (F := ℝ) (⊤ : ℕ∞) fun (z : Vec3 × ℝ) => spatialPartial φ j z) →
        (∀ (j : Fin (3 : ℕ)),
            HasCompactSupport (β := ℝ) fun (z : Vec3 × ℝ) => spatialPartial φ j z) →
          (∀ (j : Fin (3 : ℕ)),
              (tsupport (α := ℝ) fun (z : Vec3 × ℝ) => spatialPartial φ j z) ⊆ tsupport φ) →
            (∀ (i : Fin (3 : ℕ)),
                ContDiff ℝ (F := ℝ) (⊤ : ℕ∞) fun (z : Vec3 × ℝ) => ψ z i) →
              (∀ {a : ParabolicPoint → ℝ},
                  Integrable a μ →
                    ∀ {α : Vec3 × ℝ → ℝ},
                      HasCompactSupport α →
                        tsupport α ⊆ tsupport φ →
                          Continuous α →
                            ∀ {b : Vec3 × ℝ → ℝ},
                              Continuous b →
                                @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                                  (fun (z : ParabolicPoint) => a z * (α z * b z)) volume) →
                (∀ (i j : Fin (3 : ℕ)),
                    Integrable (ε := ℝ) (fun (z : ParabolicPoint) => Du z i j) μ) →
                  ∀ (i j : Fin (3 : ℕ)),
                    @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                      (fun (z : ParabolicPoint) => Du z i j * (spatialPartial φ j z * ψ z i)) volume
    := by
  intro Du φ Ω' J ψ μ hφsp hφsp_c hφsp_ts hψi hbox_factor hDij i j
  exact hbox_factor (hDij i j) (hφsp_c j) (hφsp_ts j)
    (hφsp j).continuous
    (hψi i).continuous

private lemma localized_divergence_tested_hHgrad_5 :
    ∀ {u : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {Ω' : Set Vec3} {J : Set ℝ}
      {ψ : Vec3 × ℝ → Vec3},
      let μ : Measure ParabolicPoint := Measure.restrict volume (spaceTimeSet Ω' J);
      (∀ (j : Fin (3 : ℕ)),
          ContDiff ℝ (F := ℝ) (⊤ : ℕ∞) fun (z : Vec3 × ℝ) => spatialPartial φ j z) →
        (∀ (j : Fin (3 : ℕ)),
            HasCompactSupport (β := ℝ) fun (z : Vec3 × ℝ) => spatialPartial φ j z) →
          (∀ (j : Fin (3 : ℕ)),
              (tsupport (α := ℝ) fun (z : Vec3 × ℝ) => spatialPartial φ j z) ⊆ tsupport φ) →
            (∀ (i j : Fin (3 : ℕ)),
                ContDiff ℝ (F := ℝ) (⊤ : ℕ∞) fun (z : Vec3 × ℝ) =>
                  spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z) →
              (∀ {a : ParabolicPoint → ℝ},
                  Integrable a μ →
                    ∀ {α : Vec3 × ℝ → ℝ},
                      HasCompactSupport α →
                        tsupport α ⊆ tsupport φ →
                          Continuous α →
                            ∀ {b : Vec3 × ℝ → ℝ},
                              Continuous b →
                                @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                                  (fun (z : ParabolicPoint) => a z * (α z * b z)) volume) →
                (∀ (i : Fin (3 : ℕ)), Integrable (ε := ℝ) (fun (z : ParabolicPoint) => u z i) μ) →
                  ∀ (i j : Fin (3 : ℕ)),
                    @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                      (fun (z : ParabolicPoint) =>
                        u z i * spatialPartial φ j z *
                          spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z)
                      volume
    := by
  intro u φ Ω' J ψ μ hφsp hφsp_c hφsp_ts hψsp hbox_factor hUi i j
  have h := hbox_factor (hUi i) (hφsp_c j) (hφsp_ts j)
    (hφsp j).continuous
    (hψsp i j).continuous
  simpa only [mul_assoc] using h

private lemma localized_divergence_tested_hHpress_6 :
    ∀ {p : ParabolicPoint → ℝ} {φ : Vec3 × ℝ → ℝ} {Ω' : Set Vec3} {J : Set ℝ} {ψ : Vec3 × ℝ → Vec3},
      ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ →
          let μ : Measure ParabolicPoint := Measure.restrict volume (spaceTimeSet Ω' J);
          Integrable p μ →
            (∀ (i j : Fin (3 : ℕ)),
                ContDiff ℝ (F := ℝ) (⊤ : ℕ∞) fun (z : Vec3 × ℝ) =>
                  spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z) →
              (∀ {a : ParabolicPoint → ℝ},
                  Integrable a μ →
                    ∀ {α : Vec3 × ℝ → ℝ},
                      HasCompactSupport α →
                        tsupport α ⊆ tsupport φ →
                          Continuous α →
                            ∀ {b : Vec3 × ℝ → ℝ},
                              Continuous b →
                                @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                                  (fun (z : ParabolicPoint) => a z * (α z * b z)) volume) →
                ∀ (i : Fin (3 : ℕ)),
                  @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                    (fun (z : ParabolicPoint) =>
                      p z * φ z * spatialPartial (fun (w : ParabolicPoint) => ψ w i) i z)
                    volume
    := by
  intro p φ Ω' J ψ hφd hφc μ hpInt hψsp hbox_factor i
  have h := hbox_factor hpInt hφc (by exact subset_rfl) hφd.continuous
    (hψsp i i).continuous
  simpa only [mul_assoc] using h

private lemma localized_divergence_tested_hLsecond_7 :
    ∀ {u : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {ψ : Vec3 × ℝ → Vec3},
      (∀ (i j : Fin (3 : ℕ)),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
            (fun (z : ParabolicPoint) =>
              u z i * (φ z * spatialSecondPartial (fun (w : ParabolicPoint) => ψ w i) j j z))
            volume) →
        @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
          (fun (z : ParabolicPoint) =>
            ∑ i : Fin (3 : ℕ),
              ∑ j : Fin (3 : ℕ),
                u z i * (φ z * spatialSecondPartial (fun (w : ParabolicPoint) => ψ w i) j j z))
          volume
    := by
  intro u φ ψ hVsecond
  exact integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ =>
    integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ =>
      hVsecond i j))

private lemma localized_divergence_tested_hLconv_8 :
    ∀ {u : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {ψ : Vec3 × ℝ → Vec3},
      (∀ (i j : Fin (3 : ℕ)),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
            (fun (z : ParabolicPoint) =>
              u z i * u z j * (φ z * spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z))
            volume) →
        @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
          (fun (z : ParabolicPoint) =>
            ∑ i : Fin (3 : ℕ),
              ∑ j : Fin (3 : ℕ),
                u z i * u z j * (φ z * spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z))
          volume
    := by
  intro u φ ψ hConvPsi
  exact integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ =>
    integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ =>
      hConvPsi i j))

private lemma localized_divergence_tested_hLgrad_9 :
    ∀ {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {φ : Vec3 × ℝ → ℝ} {ψ : Vec3 × ℝ → Vec3},
      (∀ (i j : Fin (3 : ℕ)),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
            (fun (z : ParabolicPoint) =>
              Du z i j * (φ z * spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z))
            volume) →
        @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
          (fun (z : ParabolicPoint) =>
            ∑ i : Fin (3 : ℕ),
              ∑ j : Fin (3 : ℕ),
                Du z i j * (φ z * spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z))
          volume
    := by
  intro Du φ ψ hGradPsi
  exact integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ =>
    integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ =>
      hGradPsi i j))

private lemma localized_divergence_tested_htimeProd_10 :
    ∀ {φ : Vec3 × ℝ → ℝ} {ψ : Vec3 × ℝ → Vec3},
      ContDiff ℝ (⊤ : ℕ∞) φ →
        (∀ (i : Fin (3 : ℕ)), ContDiff ℝ (F := ℝ) (⊤ : ℕ∞) fun (z : Vec3 × ℝ) => ψ z i) →
          let φp : ParabolicPoint → ℝ := fun (z : ParabolicPoint) => φ (z.1, z.2);
          let ψp : ParabolicPoint → Vec3 := fun (z : ParabolicPoint) => ψ (z.1, z.2);
          ∀ (i : Fin (3 : ℕ)) (z : ParabolicPoint),
            timePartial (fun (w : ParabolicPoint) => (φ • ψ) w i) z =
              timePartial φp z * ψp z i + φp z * timePartial (fun (w : ParabolicPoint) => ψ w i) z
    := by
  intro φ ψ hφd hψi φp ψp i z
  have h := timePartial_mul_full hφd (hψi i) z
  convert h using 1
  all_goals rfl

private lemma localized_divergence_tested_hspaceProd_11 :
    ∀ {φ : Vec3 × ℝ → ℝ} {ψ : Vec3 × ℝ → Vec3},
      ContDiff ℝ (⊤ : ℕ∞) φ →
        (∀ (i : Fin (3 : ℕ)), ContDiff ℝ (F := ℝ) (⊤ : ℕ∞) fun (z : Vec3 × ℝ) => ψ z i) →
          let φp : ParabolicPoint → ℝ := fun (z : ParabolicPoint) => φ (z.1, z.2);
          let ψp : ParabolicPoint → Vec3 := fun (z : ParabolicPoint) => ψ (z.1, z.2);
          ∀ (i j : Fin (3 : ℕ)) (z : ParabolicPoint),
            spatialPartial (fun (w : ParabolicPoint) => (φ • ψ) w i) j z =
              spatialPartial φp j z * ψp z i +
                φp z * spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z
    := by
  intro φ ψ hφd hψi φp ψp i j z
  have h := spatialPartial_mul_full hφd (hψi i) j z
  convert h using 1
  all_goals rfl

private lemma localized_divergence_tested_hF_12 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {ψ : Vec3 × ℝ → Vec3},
      @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
          (fun (z : ParabolicPoint) =>
            ∑ i : Fin (3 : ℕ), u z i * (φ z * timePartial (fun (w : ParabolicPoint) => ψ w i) z))
          volume →
        @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
            (fun (z : ParabolicPoint) =>
              ∑ i : Fin (3 : ℕ),
                ∑ j : Fin (3 : ℕ),
                  u z i * u z j * (φ z * spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z))
            volume →
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
              (fun (z : ParabolicPoint) =>
                ∑ i : Fin (3 : ℕ),
                  ∑ j : Fin (3 : ℕ),
                    Du z i j * (φ z * spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z))
              volume →
            @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                (fun (z : ParabolicPoint) =>
                  p z *
                    ∑ i : Fin (3 : ℕ), φ z * spatialPartial (fun (w : ParabolicPoint) => ψ w i) i z)
                volume →
              @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                  (fun (z : ParabolicPoint) =>
                    ∑ i : Fin (3 : ℕ), localizedDivergenceG φ u Du p f z i * ψ z i)
                  volume →
                let φp : ParabolicPoint → ℝ := fun (z : ParabolicPoint) => φ (z.1, z.2);
                (φp =
                    have this : ParabolicPoint → ℝ := φ;
                    this) →
                  let ψp : ParabolicPoint → Vec3 := fun (z : ParabolicPoint) => ψ (z.1, z.2);
                  (ψp =
                      have this : ParabolicPoint → Vec3 := ψ;
                      this) →
                    let F : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
                      HSub.hSub (α := ℝ)
                              (-∑ i : Fin (3 : ℕ),
                                  u z i *
                                    (φp z * timePartial (fun (w : ParabolicPoint) => ψp w i) z))
                              (∑ i : Fin (3 : ℕ),
                                ∑ j : Fin (3 : ℕ),
                                  u z i * u z j *
                                    (φp z *
                                      spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z)) +
                            ∑ i : Fin (3 : ℕ),
                              ∑ j : Fin (3 : ℕ),
                                Du z i j *
                                  (φp z * spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z) -
                          p z *
                            ∑ i : Fin (3 : ℕ),
                              φp z * spatialPartial (fun (w : ParabolicPoint) => ψp w i) i z -
                        ∑ i : Fin (3 : ℕ), localizedDivergenceG φ u Du p f z i * ψp z i;
                    @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace F volume
    := by
  intro u Du p f φ ψ hLtime hLconv hLgrad hLpress hG φp hφp_eq ψp hψp_eq F
  dsimp [F]
  rw [hφp_eq, hψp_eq]
  exact (((hLtime.neg.sub hLconv).add hLgrad).sub hLpress).sub hG

private lemma localized_divergence_tested_hA_13 :
    ∀ {u : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {ψ : Vec3 × ℝ → Vec3},
      @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
          (fun (z : ParabolicPoint) =>
            ∑ i : Fin (3 : ℕ), u z i * (φ z * timePartial (fun (w : ParabolicPoint) => ψ w i) z))
          volume →
        let φp : ParabolicPoint → ℝ := fun (z : ParabolicPoint) => φ (z.1, z.2);
        (φp =
            have this : ParabolicPoint → ℝ := φ;
            this) →
          let ψp : ParabolicPoint → Vec3 := fun (z : ParabolicPoint) => ψ (z.1, z.2);
          (ψp =
              have this : ParabolicPoint → Vec3 := ψ;
              this) →
            let A : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
              ∑ i : Fin (3 : ℕ),
                u z i * (φp z * timePartial (fun (w : ParabolicPoint) => ψp w i) z);
            @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace A volume
    := by
  intro u φ ψ hLtime φp hφp_eq ψp hψp_eq A
  dsimp [A]
  rw [hφp_eq, hψp_eq]
  exact hLtime

private lemma localized_divergence_tested_hB_14 :
    ∀ {u : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {ψ : Vec3 × ℝ → Vec3},
      @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
          (fun (z : ParabolicPoint) =>
            ∑ i : Fin (3 : ℕ),
              ∑ j : Fin (3 : ℕ),
                u z i * (φ z * spatialSecondPartial (fun (w : ParabolicPoint) => ψ w i) j j z))
          volume →
        let φp : ParabolicPoint → ℝ := fun (z : ParabolicPoint) => φ (z.1, z.2);
        (φp =
            have this : ParabolicPoint → ℝ := φ;
            this) →
          let ψp : ParabolicPoint → Vec3 := fun (z : ParabolicPoint) => ψ (z.1, z.2);
          (ψp =
              have this : ParabolicPoint → Vec3 := ψ;
              this) →
            let B : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
              ∑ i : Fin (3 : ℕ),
                ∑ j : Fin (3 : ℕ),
                  u z i * (φp z * spatialSecondPartial (fun (w : ParabolicPoint) => ψp w i) j j z);
            @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace B volume
    := by
  intro u φ ψ hLsecond φp hφp_eq ψp hψp_eq B
  dsimp [B]
  rw [hφp_eq, hψp_eq]
  exact hLsecond

private lemma localized_divergence_tested_hG₀_15 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {ψ : Vec3 × ℝ → Vec3},
      @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
          (fun (z : ParabolicPoint) =>
            ∑ i : Fin (3 : ℕ), localizedDivergenceG φ u Du p f z i * ψ z i)
          volume →
        let ψp : ParabolicPoint → Vec3 := fun (z : ParabolicPoint) => ψ (z.1, z.2);
        (ψp =
            have this : ParabolicPoint → Vec3 := ψ;
            this) →
          let G₀ : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
            ∑ i : Fin (3 : ℕ), localizedDivergenceG φ u Du p f z i * ψp z i;
          @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace G₀ volume
    := by
  intro u Du p f φ ψ hG ψp hψp_eq G₀
  dsimp [G₀]
  rw [hψp_eq]
  exact hG

private lemma localized_divergence_tested_hH₀_16 :
    ∀ {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {φ : Vec3 × ℝ → ℝ} {ψ : Vec3 × ℝ → Vec3},
      @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
          (fun (z : ParabolicPoint) =>
            ∑ i : Fin (3 : ℕ),
              ∑ j : Fin (3 : ℕ),
                localizedDivergenceH φ u p j z i *
                  spatialPartial (fun (w : ParabolicPoint) => ψ w i) j z)
          volume →
        let ψp : ParabolicPoint → Vec3 := fun (z : ParabolicPoint) => ψ (z.1, z.2);
        (ψp =
            have this : ParabolicPoint → Vec3 := ψ;
            this) →
          let H₀ : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
            ∑ i : Fin (3 : ℕ),
              ∑ j : Fin (3 : ℕ),
                localizedDivergenceH φ u p j z i *
                  spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z;
          @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace H₀ volume
    := by
  intro u p φ ψ hH ψp hψp_eq H₀
  dsimp [H₀]
  rw [hψp_eq]
  exact hH

private lemma localized_divergence_tested_hrel_17 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {ψ : Vec3 × ℝ → Vec3},
      let φp : ParabolicPoint → ℝ := fun (z : ParabolicPoint) => φ (z.1, z.2);
      let ψp : ParabolicPoint → Vec3 := fun (z : ParabolicPoint) => ψ (z.1, z.2);
      let _ : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
        HSub.hSub (α := ℝ)
                (-∑ i : Fin (3 : ℕ),
                    u z i * (φp z * timePartial (fun (w : ParabolicPoint) => ψp w i) z))
                (∑ i : Fin (3 : ℕ),
                  ∑ j : Fin (3 : ℕ),
                    u z i * u z j *
                      (φp z * spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z)) +
              ∑ i : Fin (3 : ℕ),
                ∑ j : Fin (3 : ℕ),
                  Du z i j * (φp z * spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z) -
            p z *
              ∑ i : Fin (3 : ℕ), φp z * spatialPartial (fun (w : ParabolicPoint) => ψp w i) i z -
          ∑ i : Fin (3 : ℕ), localizedDivergenceG φ u Du p f z i * ψp z i;
      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (z : ParabolicPoint) =>
            (fun (z : ParabolicPoint) =>
                HSub.hSub (α := ℝ)
                        (-∑ i : Fin (3 : ℕ),
                            u z i *
                              ((fun (z : ParabolicPoint) => φ (z.1, z.2)) z *
                                timePartial
                                  (fun (w : ParabolicPoint) =>
                                    (fun (z : ParabolicPoint) => ψ (z.1, z.2)) w i)
                                  z))
                        (∑ i : Fin (3 : ℕ),
                          ∑ j : Fin (3 : ℕ),
                            u z i * u z j *
                              ((fun (z : ParabolicPoint) => φ (z.1, z.2)) z *
                                spatialPartial
                                  (fun (w : ParabolicPoint) =>
                                    (fun (z : ParabolicPoint) => ψ (z.1, z.2)) w i)
                                  j z)) +
                      ∑ i : Fin (3 : ℕ),
                        ∑ j : Fin (3 : ℕ),
                          Du z i j *
                            ((fun (z : ParabolicPoint) => φ (z.1, z.2)) z *
                              spatialPartial
                                (fun (w : ParabolicPoint) =>
                                  (fun (z : ParabolicPoint) => ψ (z.1, z.2)) w i)
                                j z) -
                    p z *
                      ∑ i : Fin (3 : ℕ),
                        (fun (z : ParabolicPoint) => φ (z.1, z.2)) z *
                          spatialPartial
                            (fun (w : ParabolicPoint) =>
                              (fun (z : ParabolicPoint) => ψ (z.1, z.2)) w i)
                            i z -
                  ∑ i : Fin (3 : ℕ),
                    localizedDivergenceG φ u Du p f z i *
                      (fun (z : ParabolicPoint) => ψ (z.1, z.2)) z i)
              z) =
          (0 : ℝ) →
        let A : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
          ∑ i : Fin (3 : ℕ), u z i * (φp z * timePartial (fun (w : ParabolicPoint) => ψp w i) z);
        let G₀ : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
          ∑ i : Fin (3 : ℕ), localizedDivergenceG φ u Du p f z i * ψp z i;
        let H₀ : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
          ∑ i : Fin (3 : ℕ),
            ∑ j : Fin (3 : ℕ),
              localizedDivergenceH φ u p j z i *
                spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z;
        let K : ParabolicPoint → ℝ := fun (z : ParabolicPoint) =>
          ∑ i : Fin (3 : ℕ),
            ∑ j : Fin (3 : ℕ),
              (φp z * Du z i j + u z i * spatialPartial φp j z) *
                spatialPartial (fun (w : ParabolicPoint) => ψp w i) j z;
        (HAdd.hAdd (α := ℝ)
                (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (z : ParabolicPoint) =>
                  (fun (z : ParabolicPoint) =>
                      HSub.hSub (α := ℝ)
                              (-∑ i : Fin (3 : ℕ),
                                  u z i *
                                    ((fun (z : ParabolicPoint) => φ (z.1, z.2)) z *
                                      timePartial
                                        (fun (w : ParabolicPoint) =>
                                          (fun (z : ParabolicPoint) => ψ (z.1, z.2)) w i)
                                        z))
                              (∑ i : Fin (3 : ℕ),
                                ∑ j : Fin (3 : ℕ),
                                  u z i * u z j *
                                    ((fun (z : ParabolicPoint) => φ (z.1, z.2)) z *
                                      spatialPartial
                                        (fun (w : ParabolicPoint) =>
                                          (fun (z : ParabolicPoint) => ψ (z.1, z.2)) w i)
                                        j z)) +
                            ∑ i : Fin (3 : ℕ),
                              ∑ j : Fin (3 : ℕ),
                                Du z i j *
                                  ((fun (z : ParabolicPoint) => φ (z.1, z.2)) z *
                                    spatialPartial
                                      (fun (w : ParabolicPoint) =>
                                        (fun (z : ParabolicPoint) => ψ (z.1, z.2)) w i)
                                      j z) -
                          p z *
                            ∑ i : Fin (3 : ℕ),
                              (fun (z : ParabolicPoint) => φ (z.1, z.2)) z *
                                spatialPartial
                                  (fun (w : ParabolicPoint) =>
                                    (fun (z : ParabolicPoint) => ψ (z.1, z.2)) w i)
                                  i z -
                        ∑ i : Fin (3 : ℕ),
                          localizedDivergenceG φ u Du p f z i *
                            (fun (z : ParabolicPoint) => ψ (z.1, z.2)) z i)
                    z)
                (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (z : ParabolicPoint) =>
                  (fun (z : ParabolicPoint) =>
                      (∑ i : Fin (3 : ℕ),
                          localizedDivergenceG φ u Du p f z i *
                            (fun (z : ParabolicPoint) => ψ (z.1, z.2)) z i :
                        ℝ))
                    z) +
              @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (z : ParabolicPoint) =>
                (fun (z : ParabolicPoint) =>
                    (∑ i : Fin (3 : ℕ),
                        ∑ j : Fin (3 : ℕ),
                          localizedDivergenceH φ u p j z i *
                            spatialPartial
                              (fun (w : ParabolicPoint) =>
                                (fun (z : ParabolicPoint) => ψ (z.1, z.2)) w i)
                              j z :
                      ℝ))
                  z) =
            HAdd.hAdd (α := ℝ)
              (-@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (z : ParabolicPoint) =>
                  (fun (z : ParabolicPoint) =>
                      (∑ i : Fin (3 : ℕ),
                          u z i *
                            ((fun (z : ParabolicPoint) => φ (z.1, z.2)) z *
                              timePartial
                                (fun (w : ParabolicPoint) =>
                                  (fun (z : ParabolicPoint) => ψ (z.1, z.2)) w i)
                                z) :
                        ℝ))
                    z)
              (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (z : ParabolicPoint) =>
                (fun (z : ParabolicPoint) =>
                    (∑ i : Fin (3 : ℕ),
                        ∑ j : Fin (3 : ℕ),
                          ((fun (z : ParabolicPoint) => φ (z.1, z.2)) z * Du z i j +
                              u z i *
                                spatialPartial (fun (z : ParabolicPoint) => φ (z.1, z.2)) j z) *
                            spatialPartial
                              (fun (w : ParabolicPoint) =>
                                (fun (z : ParabolicPoint) => ψ (z.1, z.2)) w i)
                              j z :
                      ℝ))
                  z) →
          HAdd.hAdd (α := ℝ)
              (-@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (z : ParabolicPoint) =>
                  A z)
              (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (z : ParabolicPoint) =>
                K z) =
            HAdd.hAdd (α := ℝ)
              (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (z : ParabolicPoint) =>
                G₀ z)
              (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (z : ParabolicPoint) =>
                H₀ z)
    := by
  intro u Du p f φ ψ φp ψp F hFglobal A G₀ H₀ K hpointInt
  calc
    _ = (∫ z, F z) + (∫ z, G₀ z) + (∫ z, H₀ z) := hpointInt.symm
    _ = _ := by rw [hFglobal]; simp only [zero_add]

private theorem localized_velocity_test_integral
    (u : ParabolicPoint → Vec3) (φ : ParabolicPoint → ℝ)
    (ψ : ParabolicPoint → Vec3)
    (hA : Integrable (fun z => ∑ i, u z i *
      (φ z * timePartial (fun w => ψ w i) z)) volume)
    (hB : Integrable (fun z => ∑ i, ∑ j, u z i *
      (φ z * spatialSecondPartial (fun w => ψ w i) j j z)) volume) :
    (∫ z, ∑ i, localizedVelocity φ u z i *
      (-(timePartial (fun w => ψ w i) z) -
        ∑ j, spatialSecondPartial (fun w => ψ w i) j j z)) =
      -(∫ z, ∑ i, u z i * (φ z * timePartial (fun w => ψ w i) z)) -
        ∫ z, ∑ i, ∑ j, u z i *
          (φ z * spatialSecondPartial (fun w => ψ w i) j j z) := by
  have hpoint (z : ParabolicPoint) :
      (∑ i, localizedVelocity φ u z i *
        (-(timePartial (fun w => ψ w i) z) -
          ∑ j, spatialSecondPartial (fun w => ψ w i) j j z)) =
        -(∑ i, u z i * (φ z * timePartial (fun w => ψ w i) z)) -
          ∑ i, ∑ j, u z i *
            (φ z * spatialSecondPartial (fun w => ψ w i) j j z) := by
    simp only [localizedVelocity, Pi.smul_apply, smul_eq_mul, mul_sub, mul_neg,
      Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    congr 1
    · congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    · apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
  simp_rw [hpoint]
  calc
    _ = (∫ z, -(∑ i, u z i * (φ z * timePartial (fun w => ψ w i) z))) -
        ∫ z, ∑ i, ∑ j, u z i *
          (φ z * spatialSecondPartial (fun w => ψ w i) j j z) := integral_sub hA.neg hB
    _ = _ := by rw [integral_neg]

theorem localized_divergence_tested_of_sws {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ} {f :
      ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I) {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I
      Ω' J)
    (hφbox : tsupport φ ⊆ Ω' ×ˢ J) {ψ : Vec3 × ℝ → Vec3}
    (hψ : ψ ∈ spaceTimeTestFunction (V := Vec3) Set.univ Set.univ) :
    (∫ z, ∑ i, localizedVelocity (show ParabolicPoint → ℝ from φ) u z i *
      (-(timePartial (fun w => ψ w i) z) - ∑ j, spatialSecondPartial (fun w => ψ w i) j j z)) =
      (∫ z, ∑ i, localizedDivergenceG φ u Du p f z i * ψ z i) +
        ∑ i, ∑ j, ∫ z,
          localizedDivergenceH φ u p j z i *
            spatialPartial (fun w => ψ w i) j z := by
  have hsol' : IsSuitableWeakSolutionIntegrable Ω I q u Du p f := hsol
  have hφ' : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I := hφ
  have hψ' : ψ ∈ spaceTimeTestFunction (V := Vec3) Set.univ Set.univ := hψ
  rcases hsol with ⟨hΩ, hI, hIord, hq, hfSol, hdata, hS2, hS3, hS4⟩
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
  have hφtime : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => timePartial φ z) := timePartial_contDiff_full hφd
  have hφtime_c := @localized_divergence_tested_hφtime_c_1 φ hφd hφc
  have hφtime_ts := @localized_divergence_tested_hφtime_ts_2 φ hφd
  have hφsp (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialPartial φ j z) :=
    spatialPartial_contDiff hφd j
  have hφsp_c (j : Fin 3) := @localized_divergence_tested_hφsp_c_3 φ hφd hφc j
  have hφsp_ts (j : Fin 3) := @localized_divergence_tested_hφsp_ts_4 φ hφd j
  have hψi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => ψ z i) :=
    (contDiff_apply ℝ ℝ i).comp hψd
  have hψtime (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => timePartial (fun w => ψ w i) z) :=
    timePartial_contDiff_full (hψi i)
  have hψsp (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialPartial (fun w => ψ w i) j z) :=
    spatialPartial_contDiff (hψi i) j
  have hψsecond (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialSecondPartial
        (fun w => ψ w i) j j z) :=
    spatialSecondPartial_contDiff_full (hψi i) j j
  have hbox_factor {a : ParabolicPoint → ℝ}
      (ha : Integrable a μ) {α : Vec3 × ℝ → ℝ}
      (hαc : HasCompactSupport α)
      (hαts : tsupport α ⊆ tsupport φ)
      (hα : Continuous α) {b : Vec3 × ℝ → ℝ} (hb : Continuous b) :=
        @localized_divergence_tested_hbox_factor_5 f φ Ω' J hφbox a ha α hαc hαts hα b hb
  have hUi (i : Fin 3) : Integrable (fun z => u z i) μ :=
    (huComp i).integrable (by norm_num)
  have hDij (i j : Fin 3) : Integrable (fun z => Du z i j) μ :=
    (hDuComp i j).integrable (by norm_num)
  have hUU (i j : Fin 3) : Integrable (fun z => u z i * u z j) μ :=
    (huComp i).integrable_mul (huComp j)
  have hfComp (i : Fin 3) : MemLp (fun z => f z i) (ENNReal.ofReal q) μ :=
    hf.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
  have hVt (i : Fin 3) :=
    hbox_factor (hUi i) hφc subset_rfl hφd.continuous
      (hψtime i).continuous
  have hVsecond (i j : Fin 3) :=
    hbox_factor (hUi i) hφc subset_rfl hφd.continuous
      (hψsecond i j).continuous
  have hConvPsi (i j : Fin 3) := @localized_divergence_tested_hConvPsi_1 u φ Ω' J ψ hφd hφc hψsp
    hbox_factor hUU i j
  have hGradPsi (i j : Fin 3) :=
    hbox_factor (hDij i j) hφc subset_rfl hφd.continuous
      (hψsp i j).continuous
  have hPressPsi (i : Fin 3) :=
    hbox_factor hpInt hφc subset_rfl hφd.continuous
      (hψsp i i).continuous
  have hForce (i : Fin 3) := @localized_divergence_tested_hForce_2 q f φ Ω' J ψ hφd hφc (by
    infer_instance) hq1 hψi hbox_factor hfComp i
  have hGtime (i : Fin 3) :=
    hbox_factor (hUi i) hφtime_c hφtime_ts hφtime.continuous
      (hψi i).continuous
  have hGconv (i j : Fin 3) := @localized_divergence_tested_hGconv_3 u φ Ω' J ψ hφsp hφsp_c
    hφsp_ts hψi hbox_factor hUU i j
  have hGgrad (i j : Fin 3) := @localized_divergence_tested_hGgrad_4 Du φ Ω' J ψ hφsp hφsp_c
    hφsp_ts hψi hbox_factor hDij i j
  have hGpress (i : Fin 3) :=
    hbox_factor hpInt (hφsp_c i) (hφsp_ts i) (hφsp i).continuous
      (hψi i).continuous
  have hGforce (i : Fin 3) : Integrable
      (fun z => f z i * (φ z * ψ z i)) volume := hForce i
  have hHconv (i j : Fin 3) : Integrable
      (fun z : ParabolicPoint => (φ z * u z i * u z j) *
        spatialPartial (fun w => ψ w i) j z) volume := by
    have h := hConvPsi i j
    simpa only [mul_comm, mul_left_comm, mul_assoc] using h
  have hHgrad (i j : Fin 3) := @localized_divergence_tested_hHgrad_5 u φ Ω' J ψ hφsp hφsp_c
    hφsp_ts hψsp hbox_factor hUi i j
  have hHpress (i : Fin 3) := @localized_divergence_tested_hHpress_6 p φ Ω' J ψ hφd hφc hpInt hψsp
    hbox_factor i
  have hLtime : Integrable (fun z => ∑ i,
      u z i * (φ z * timePartial (fun w => ψ w i) z)) volume :=
    integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ => hVt i)
  have hLsecond := @localized_divergence_tested_hLsecond_7 u φ ψ hVsecond
  have hLconv := @localized_divergence_tested_hLconv_8 u φ ψ hConvPsi
  have hLgrad := @localized_divergence_tested_hLgrad_9 Du φ ψ hGradPsi
  have hLpress := @localized_divergence_tested_hLpress_6 p φ ψ hPressPsi
  have hG := @localized_divergence_tested_hG_1 u Du p f φ ψ hGtime hGconv hGgrad hGpress hGforce
  have hH := @localized_divergence_tested_hH_2 u p φ ψ hHconv hHgrad hHpress
  let φp : ParabolicPoint → ℝ := fun z => φ (z.1, z.2)
  have hφp_eq : φp = (show ParabolicPoint → ℝ from φ) := by
    funext z
    rfl
  let ψp : ParabolicPoint → Vec3 := fun z => ψ (z.1, z.2)
  have hψp_eq : ψp = (show ParabolicPoint → Vec3 from ψ) := by
    funext z
    rfl
  have htimeProd (i : Fin 3) (z : ParabolicPoint) := @localized_divergence_tested_htimeProd_10 φ ψ
    hφd hψi i z
  have hspaceProd (i j : Fin 3) (z : ParabolicPoint) := @localized_divergence_tested_hspaceProd_11
    φ ψ hφd hψi i j z
  have hηtest : (φ • ψ) ∈
      spaceTimeTestFunction (V := Vec3) Ω I := by
    refine ⟨hφd.smul hψd, hψc.smul_left, ?_⟩
    exact (tsupport_smul_subset_left φ ψ).trans hφΩ
  have hS3test := hS3 (φ • ψ) hηtest
  let R : ParabolicPoint → ℝ := fun z =>
    (-(∑ i, u z i * timePartial (fun w => (φ • ψ) w i) z))
      - ∑ i, ∑ j, u z i * u z j *
          spatialPartial (fun w => (φ • ψ) w i) j z
      + ∑ i, ∑ j, Du z i j *
          spatialPartial (fun w => (φ • ψ) w i) j z
      - p z * ∑ i, spatialPartial (fun w => (φ • ψ) w i) i z
      - ∑ i, f z i * (φ • ψ) z i
  have hS3zero : (∫ z in spaceTimeSet Ω I, R z) = 0 := by
    simpa only using hS3test.2
  have hF := @localized_divergence_tested_hF_12 u Du p f φ ψ hLtime hLconv hLgrad hLpress hG
    hφp_eq hψp_eq
  have hRF := @localized_divergence_tested_hRF_3 u Du p f φ Ω' J ψ hgrad hφp_eq hψp_eq htimeProd
    hspaceProd
  have hFzero := @localized_divergence_tested_hFzero_4 Ω I u Du p f φ ψ hφd hφΩ hφp_eq
  have hFglobal := @localized_divergence_tested_hFglobal_7 Ω I u Du p f φ ψ hS3zero hRF hFzero
  have hLap := laplacian_transfer_of_sws hsol' hφ' hbox hφbox hψ'
  let A : ParabolicPoint → ℝ := fun z =>
    ∑ i, u z i * (φp z * timePartial (fun w => ψp w i) z)
  let B : ParabolicPoint → ℝ := fun z =>
    ∑ i, ∑ j, u z i * (φp z * spatialSecondPartial
      (fun w => ψp w i) j j z)
  let G₀ : ParabolicPoint → ℝ := fun z =>
    ∑ i, localizedDivergenceG φ u Du p f z i * ψp z i
  let H₀ : ParabolicPoint → ℝ := fun z =>
    ∑ i, ∑ j, localizedDivergenceH φ u p j z i * spatialPartial
      (fun w => ψp w i) j z
  let K : ParabolicPoint → ℝ := fun z =>
    ∑ i, ∑ j, (φp z * Du z i j + u z i * spatialPartial φp j z) *
      spatialPartial (fun w => ψp w i) j z
  have hA := @localized_divergence_tested_hA_13 u φ ψ hLtime hφp_eq hψp_eq
  have hB := @localized_divergence_tested_hB_14 u φ ψ hLsecond hφp_eq hψp_eq
  have hG₀ := @localized_divergence_tested_hG₀_15 u Du p f φ ψ hG hψp_eq
  have hH₀ := @localized_divergence_tested_hH₀_16 u p φ ψ hH hψp_eq
  have hU := @localized_divergence_tested_hU_8 u φ ψ hHgrad hφp_eq hψp_eq
  have hK := @localized_divergence_tested_hK_5 u Du φ ψ hLgrad hφp_eq hψp_eq hU
  have hLap' : (∫ z, B z) = -∫ z, K z := by
    exact @localized_divergence_tested_hLap'_6 u Du φ ψ hLap
  have hdiag (z : ParabolicPoint) :
      (∑ i, ∑ j, (if i = j then p z * φp z else 0) *
        spatialPartial (fun w => ψp w i) j z) =
        ∑ i, p z * φp z * spatialPartial (fun w => ψp w i) i z := by
    classical
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hpoint (z : ParabolicPoint) := @localized_divergence_tested_hpoint_9 u Du p f φ ψ hdiag (by
    intros; rfl) (by intros; rfl) z
  have hpointInt := @localized_divergence_tested_hpointInt_7 u Du p f φ ψ hF hA hG₀ hH₀ hK hpoint
  have hrel := @localized_divergence_tested_hrel_17 u Du p f φ ψ hFglobal hpointInt
  have hHij (i j : Fin 3) := @localized_divergence_tested_hHij_8 u p φ ψ hHconv hHgrad hHpress i j
  have hHsum := @localized_divergence_tested_hHsum_9 u p φ ψ hψp_eq hHij
  calc
    (∫ z, ∑ i, localizedVelocity (show ParabolicPoint → ℝ from φ) u z i *
        (-(timePartial (fun w => ψ w i) z) -
          ∑ j, spatialSecondPartial (fun w => ψ w i) j j z)) =
        (-(∫ z, A z)) - (∫ z, B z) :=
      localized_velocity_test_integral u φp ψp hA hB
    _ = (-(∫ z, A z)) + (∫ z, K z) := by rw [hLap']; ring_nf
    _ = (∫ z, G₀ z) + (∫ z, H₀ z) := hrel
    _ = (∫ z, ∑ i, localizedDivergenceG φ u Du p f z i * ψ z i) +
        ∑ i, ∑ j, ∫ z, localizedDivergenceH φ u p j z i *
          spatialPartial (fun w => ψ w i) j z := by
      rw [hHsum]
      congr 1
end CKN.Core.Step3
