/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.Admissibility
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.Conversions
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.Cutoff
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.Terms
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.I4
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.RawI1
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.RawI2Bound
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.RawI3Bound
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.RawI4
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.Finiteness
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.FinitenessComponentBounds
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.LocalBox
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.Integrability
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.AELocalEnergy
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.PointwiseEnergy
public import LeanPool.CaffarelliKohnNirenberg.Setting.PoincareSobolevL1Slice
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SliceIntegrability
public import LeanPool.CaffarelliKohnNirenberg.Setting.VectorInequalities

/-!
# Caccioppoli Mean Subtraction

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration


noncomputable section

namespace CKN

private theorem caccioppoli_native_euclidean_eq (v : Vec3) :
    vec3EuclideanNorm v = vecEuclideanNorm v := by
  simp [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]

private theorem caccioppoli_exists_euclidean_radius
    {Ω : Set Vec3} (hΩ : IsOpen Ω) {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : euclideanClosedBall x₀ ρ ⊆ Ω) :
    ∃ R : ℝ, ρ < R ∧ vec3Ball x₀ R ⊆ Ω := by
  have hK : IsCompact (euclideanClosedBall x₀ ρ) :=
    isCompact_euclideanClosedBall x₀ hρ.le
  obtain ⟨δ, hδ, hδsub⟩ := hK.exists_thickening_subset_open hΩ hball
  refine ⟨ρ + δ / 2, by linarith only [hδ], ?_⟩
  intro y hy
  change vec3EuclideanNorm (y - x₀) < ρ + δ / 2 at hy
  by_cases hinside : vec3EuclideanNorm (y - x₀) ≤ ρ
  · apply hball
    apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hρ.le).2
    simpa only [caccioppoli_native_euclidean_eq] using hinside
  have hρy : ρ < vec3EuclideanNorm (y - x₀) := lt_of_not_ge hinside
  have hnormpos : 0 < vec3EuclideanNorm (y - x₀) := lt_trans hρ hρy
  let a : ℝ := ρ / vec3EuclideanNorm (y - x₀)
  let x : Vec3 := x₀ + a • (y - x₀)
  have ha : 0 < a := div_pos hρ hnormpos
  have hxa : vec3EuclideanNorm (x - x₀) = ρ := by
    dsimp [x]
    rw [show x₀ + a • (y - x₀) - x₀ = a • (y - x₀) by abel,
      vec3EuclideanNorm_smul, abs_of_pos ha]
    dsimp [a]
    field_simp [ne_of_gt hnormpos]
  have hx : x ∈ euclideanClosedBall x₀ ρ :=
    (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hρ.le).2
      (by simpa only [caccioppoli_native_euclidean_eq] using hxa.le)
  apply hδsub
  rw [Metric.mem_thickening_iff]
  refine ⟨x, hx, ?_⟩
  have hdiff : y - x = (1 - a) • (y - x₀) := by
    calc
      y - x = (y - x₀) - a • (y - x₀) := by dsimp [x]; abel
      _ = (1 - a) • (y - x₀) := by rw [sub_smul]; simp
  have ha_le : a ≤ 1 := by
    dsimp [a]
    exact (div_le_iff₀ hnormpos).2 (by simpa using hρy.le)
  have hdiffnorm : (1 - a) * vec3EuclideanNorm (y - x₀) =
      vec3EuclideanNorm (y - x₀) - ρ := by
    dsimp [a]
    field_simp [ne_of_gt hnormpos]
  have hdist : dist y x ≤ vec3EuclideanNorm (y - x₀) - ρ := by
    rw [dist_eq_norm]
    calc
      ‖y - x‖ ≤ vec3EuclideanNorm (y - x) :=
        CKN.caccioppoli_native_norm_le_euclidean (y - x)
      _ = (1 - a) * vec3EuclideanNorm (y - x₀) := by
        rw [hdiff, vec3EuclideanNorm_smul, abs_of_nonneg (sub_nonneg.mpr ha_le)]
      _ = vec3EuclideanNorm (y - x₀) - ρ := hdiffnorm
  exact hdist.trans_lt (by nlinarith only [hy, hδ])

theorem caccioppoli_poincare_radius
    {Ω : Set Vec3} {I : Set ℝ} {z₀ : ParabolicPoint} {ρ : ℝ}
    (hΩ : IsOpen Ω) (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z₀.1 z₀.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∃ R : ℝ, ρ < R ∧ vec3Ball z₀.1 R ⊆ Ω := by
  have hball : euclideanClosedBall z₀.1 ρ ⊆ Ω := by
    intro x hx
    have hmem : (x, z₀.2 - ρ ^ 2) ∈
        closure (parabolicCylinder z₀.1 z₀.2 ρ) := by
      rw [closure_parabolicCylinder hρ]
      refine ⟨?_, ?_⟩
      · change vec3EuclideanNorm (x - z₀.1) ≤ ρ
        simpa only [caccioppoli_native_euclidean_eq] using
          (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hρ.le).1 hx
      · exact ⟨le_rfl, sub_le_self _ (sq_nonneg ρ)⟩
    exact (hsub hmem).1
  exact caccioppoli_exists_euclidean_radius hΩ hρ hball

theorem caccioppoli_local_energy_ae
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hψ_nonneg : ∀ z, 0 ≤ ψ z) :
    ∀ᵐ t ∂(volume.restrict I),
      (∫ x in Ω, (vec3EuclideanNorm (u (x, t))) ^ 2 * ψ (x, t))
        + 2 * ∫ s in Iio t, ∫ x in Ω,
            spatialGradientSq u Du (x, s) * ψ (x, s) ≤
        ∫ s in Iio t, ∫ x in Ω, localEnergyRhs u p f ψ (x, s) :=
  suitableWeakSolution_localEnergyInequality_ae hsol hψ hψ_nonneg

theorem caccioppoli_localEnergyRhs_decompose
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} {ψ : Vec3 × ℝ → ℝ}
    (z : ParabolicPoint) :
    localEnergyRhs u p f ψ z =
      (vec3EuclideanNorm (u z)) ^ 2 *
          (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z) +
        (vec3EuclideanNorm (u z)) ^ 2 *
          (∑ i, u z i * spatialPartial ψ i z) +
        2 * p z * (∑ i, u z i * spatialPartial ψ i z) +
        2 * (∑ i, f z i * u z i) * ψ z := by
  unfold localEnergyRhs timePartialProd spatialSecondPartialProd spatialPartialProd
  ring

theorem caccioppoli_local_energy_ae_decomposed
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hψ_nonneg : ∀ z, 0 ≤ ψ z) :
    ∀ᵐ t ∂(volume.restrict I),
      (∫ x in Ω, (vec3EuclideanNorm (u (x, t))) ^ 2 * ψ (x, t))
        + 2 * ∫ s in Iio t, ∫ x in Ω,
            spatialGradientSq u Du (x, s) * ψ (x, s) ≤
        ∫ s in Iio t, ∫ x in Ω,
          ((vec3EuclideanNorm (u (x, s))) ^ 2 *
              (timePartial ψ (x, s) + ∑ i, spatialSecondPartial ψ i i (x, s)) +
            (vec3EuclideanNorm (u (x, s))) ^ 2 *
              (∑ i, u (x, s) i * spatialPartial ψ i (x, s)) +
            2 * p (x, s) *
              (∑ i, u (x, s) i * spatialPartial ψ i (x, s)) +
            2 * (∑ i, f (x, s) i * u (x, s) i) * ψ (x, s)) := by
  have h := caccioppoli_local_energy_ae hsol hψ hψ_nonneg
  filter_upwards [h] with t ht
  refine ht.trans_eq ?_
  apply integral_congr_ae
  filter_upwards [] with s
  apply integral_congr_ae
  filter_upwards [] with x
  exact caccioppoli_localEnergyRhs_decompose (x, s)

private theorem caccioppoli_countable_slice_cancel
    {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3}
    {K : Set Vec3} (hK : IsCompact K) (Ψ : ℝ → Vec3 → ℝ)
    (hC : Set.Countable (Set.range (fun q : ℚ => (q : ℝ))))
    (hD : Dense (Set.range (fun q : ℚ => (q : ℝ))))
    (hΨ₀ : Continuous (fun z : ℝ × Vec3 => Ψ z.1 z.2))
    (hΨ₁ : ∀ i : Fin 3,
      Continuous (fun z : ℝ × Vec3 => spatialDeriv (Ψ z.1) i z.2))
    (hΨ₂ : ∀ i j : Fin 3,
      Continuous (fun z : ℝ × Vec3 => mixedSecond (Ψ z.1) i j z.2))
    (hK₀ : ∀ x y, y ∉ K → Ψ x y = 0)
    (hK₁ : ∀ x y i, y ∉ K → spatialDeriv (Ψ x) i y = 0)
    (hK₂ : ∀ x y i j, y ∉ K → mixedSecond (Ψ x) i j y = 0)
    (hCtest : ∀ ψ ∈ Set.range (fun q : ℚ => fun y => Ψ (q : ℝ) y),
      ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Ω)
    (hslice : ∀ᵐ s ∂volume.restrict I, ∀ ψ ∈ Set.range
      (fun q : ℚ => fun y => Ψ (q : ℝ) y),
      ∫ x in Ω, ∑ i, u (x, s) i * (fderiv ℝ ψ x) (basisVec i) = 0)
    (hu : ∀ᵐ s ∂volume.restrict I,
      IntegrableOn (fun x => u (x, s)) K volume) :
    ∀ᵐ s ∂volume.restrict I, ∀ x : ℝ,
      parametricPairing Ψ (fun _ : Vec3 => 0) (fun y => u (y, s))
        (fun _ => 0) x = 0 := by
  filter_upwards [hslice, hu] with s hs hUs
  have hp := caccioppoli_I2_mean_subtraction hK Ψ
    (fun _ : Vec3 => 0) (fun y => u (y, s)) (fun _ => 0)
    hC hD hΨ₀ hΨ₁ hΨ₂ hK₀ hK₁ hK₂
    (integrableOn_zero) hUs (integrableOn_zero)
    (fun q hq => by
      obtain ⟨q', rfl⟩ := hq
      rcases hCtest _ ⟨q', rfl⟩ with ⟨hψ, hψc, hψΩ⟩
      have hderivcont : ∀ i : Fin 3,
          Continuous (fun y : Vec3 => spatialDeriv (Ψ (q' : ℝ)) i y) := by
        intro i
        have hmap : Continuous (fun y : Vec3 => ((q' : ℝ), y)) :=
          (continuous_const : Continuous (fun _ : Vec3 => (q' : ℝ))).prodMk
            continuous_id
        have hcomp := (hΨ₁ i).comp hmap
        change Continuous (fun y : Vec3 =>
          spatialDeriv (Ψ (((q' : ℝ), y).1)) i (((q' : ℝ), y).2)) at hcomp
        exact hcomp
      have hprod : ∀ i : Fin 3,
          Integrable (fun y : Vec3 => u (y, s) i *
            spatialDeriv (Ψ (q' : ℝ)) i y) volume := by
        intro i
        have hui : Integrable (fun y : Vec3 => u (y, s) i)
            (volume.restrict K) := by
          exact (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).integrableOn_comp hUs
        have hcontK : ContinuousOn
            (fun y : Vec3 => ‖spatialDeriv (Ψ (q' : ℝ)) i y‖) K :=
          (hderivcont i).norm.continuousOn
        obtain ⟨C, hCbound⟩ := bddAbove_def.mp (hK.bddAbove_image hcontK)
        have hbound : ∀ᵐ y ∂volume.restrict K,
            ‖spatialDeriv (Ψ (q' : ℝ)) i y‖ ≤ max C 0 := by
          filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
          exact le_max_of_le_left (hCbound _ ⟨y, hy, rfl⟩)
        have hprodK : Integrable (fun y : Vec3 => u (y, s) i *
            spatialDeriv (Ψ (q' : ℝ)) i y) (volume.restrict K) :=
          hui.mul_bdd (hderivcont i).aestronglyMeasurable hbound
        apply (integrableOn_iff_integrable_of_support_subset (μ := volume)
          (s := K) (by
            intro y hy
            by_contra hnot
            apply hy
            rw [mul_eq_zero]
            right
            have hz := hK₁ (q' : ℝ) y i hnot
            simpa [spatialDeriv] using hz)).mp
        exact hprodK
      have hsumInt : ∫ y, ∑ i, u (y, s) i *
          spatialDeriv (Ψ (q' : ℝ)) i y =
          ∑ i, ∫ y, u (y, s) i * spatialDeriv (Ψ (q' : ℝ)) i y := by
        simpa only [Finset.sum_apply] using
          (integral_finsetSum (s := (Finset.univ : Finset (Fin 3)))
            (fun i _ => hprod i))
      have hzeroOutside : ∀ y ∉ Ω, ∑ i, u (y, s) i *
          spatialDeriv (Ψ (q' : ℝ)) i y = 0 := by
        intro y hy
        apply Finset.sum_eq_zero
        intro i hi
        have hψzero : Ψ (q' : ℝ) =ᶠ[𝓝 y] (fun _ : Vec3 => (0 : ℝ)) := by
          filter_upwards [((isClosed_tsupport (Ψ (q' : ℝ))).isOpen_compl.mem_nhds
            (fun hmem => hy (hψΩ hmem)))] with w hw
          exact image_eq_zero_of_notMem_tsupport hw
        have hfd : fderiv ℝ (Ψ (q' : ℝ)) y = 0 := by
          rw [Filter.EventuallyEq.fderiv_eq hψzero, fderiv_const_apply]
        simp [spatialDeriv, hfd]
      have hset := setIntegral_eq_integral_of_forall_compl_eq_zero
        (μ := (volume : Measure Vec3)) hzeroOutside
      have hzero := hs ((fun q : ℚ => fun y : Vec3 => Ψ (q : ℝ) y) q')
        ⟨q', rfl⟩
      have hzero' : (∫ y, ∑ i, u (y, s) i *
          spatialDeriv (Ψ (q' : ℝ)) i y) = 0 := by
        rw [← hset]
        exact hzero
      have hzero'' : (∑ i, ∫ y, u (y, s) i *
          spatialDeriv (Ψ (q' : ℝ)) i y) = 0 := by
        rw [← hsumInt]
        exact hzero'
      simpa [parametricPairing] using hzero''
    )
  exact hp

theorem caccioppoli_square_sum_le_square_sum
    {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : ℝ}
    (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) (hy₃ : 0 ≤ y₃) (hy₄ : 0 ≤ y₄)
    (h₁ : x₁ ≤ y₁ ^ 2) (h₂ : x₂ ≤ y₂ ^ 2)
    (h₃ : x₃ ≤ y₃ ^ 2) (h₄ : x₄ ≤ y₄ ^ 2) :
    x₁ + x₂ + x₃ + x₄ ≤ (y₁ + y₂ + y₃ + y₄) ^ 2 := by
  have hsum : x₁ + x₂ + x₃ + x₄ ≤ y₁ ^ 2 + y₂ ^ 2 + y₃ ^ 2 + y₄ ^ 2 := by
    linarith only [h₁, h₂, h₃, h₄]
  have hcross₁₂ : 0 ≤ 2 * y₁ * y₂ := by positivity
  have hcross₁₃ : 0 ≤ 2 * y₁ * y₃ := by positivity
  have hcross₁₄ : 0 ≤ 2 * y₁ * y₄ := by positivity
  have hcross₂₃ : 0 ≤ 2 * y₂ * y₃ := by positivity
  have hcross₂₄ : 0 ≤ 2 * y₂ * y₄ := by positivity
  have hcross₃₄ : 0 ≤ 2 * y₃ * y₄ := by positivity
  nlinarith only [hsum, hcross₁₂, hcross₁₃, hcross₁₄, hcross₂₃, hcross₂₄,
    hcross₃₄]

theorem caccioppoli_slice_poincare_ae
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I) :
    ∃ R Ω' J, ρ < R ∧ localBox Ω I Ω' J ∧
      (∀ x ∈ vec3Ball x₀ R, x ∈ Ω') ∧
      (∀ s ∈ Ioc (t₀ - ρ ^ 2) t₀, s ∈ J) ∧
      (∀ᵐ s ∂volume.restrict (Ioc (t₀ - ρ ^ 2) t₀),
        (∫ x in vec3Ball x₀ ρ,
            |(vec3EuclideanNorm (u (x, s))) ^ 2 -
              ⨍ y in vec3Ball x₀ ρ, (vec3EuclideanNorm (u (y, s))) ^ 2| ^
                (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
          poincareSobolevL1VectorConstant *
            (∫ x in vec3Ball x₀ ρ,
              (vec3EuclideanNorm (u (x, s))) ^ 2) ^ (1 / 2 : ℝ) *
            (∫ x in vec3Ball x₀ ρ,
              spatialGradientSq u Du (x, s)) ^ (1 / 2 : ℝ)) := by
  have hradius := caccioppoli_poincare_radius
    (Ω := Ω) (I := I) (z₀ := (x₀, t₀)) (ρ := ρ) hsol.1 hρ hsub
  obtain ⟨R, hρR, hRΩ⟩ := hradius
  let R' : ℝ := (ρ + R) / 2
  have hρR' : ρ < R' := by
    dsimp [R']
    linarith only [hρR]
  have hR'R : R' < R := by
    dsimp [R']
    linarith only [hρR]
  have hR'pos : 0 < R' := by
    linarith only [hρ, hρR']
  have hclosed : euclideanClosedBall x₀ R' ⊆ Ω := by
    intro x hx
    apply hRΩ
    rw [mem_vec3Ball]
    have hx' := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR'pos.le).1 hx
    simpa only [caccioppoli_native_euclidean_eq] using hx'.trans_lt hR'R
  let K : Set ParabolicPoint := parabolicHomeomorph ⁻¹'
    (euclideanClosedBall x₀ R' ×ˢ Icc (t₀ - ρ ^ 2) t₀)
  have hKcompact : IsCompact K := by
    exact (parabolicHomeomorph.isCompact_preimage).2
      ((isCompact_euclideanClosedBall x₀ hR'pos.le).prod isCompact_Icc)
  have hKsub : K ⊆ spaceTimeSet Ω I := by
    rintro ⟨x, s⟩ hxs
    have hxs' : x ∈ euclideanClosedBall x₀ R' ∧
        s ∈ Icc (t₀ - ρ ^ 2) t₀ := by
      change (x, s) ∈ euclideanClosedBall x₀ R' ×ˢ Icc (t₀ - ρ ^ 2) t₀ at hxs
      exact hxs
    rcases hxs' with ⟨hx, hs⟩
    refine ⟨hclosed hx, ?_⟩
    have hz : (x₀, s) ∈ closure (parabolicCylinder x₀ t₀ ρ) := by
      rw [closure_parabolicCylinder hρ]
      exact ⟨by simp [vec3EuclideanNorm_zero, hρ.le], hs⟩
    exact (hsub hz).2
  obtain ⟨Ω', J, hbox, hKbox⟩ := caccioppoli_localBox_of_compact_subset
    hsol.1 hsol.2.1 hsol.2.2.1 hKcompact hKsub
  have hball : ∀ x ∈ vec3Ball x₀ R', x ∈ Ω' := by
    intro x hx
    have hx' : x ∈ euclideanClosedBall x₀ R' := by
      apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR'pos.le).2
      have hxe := mem_vec3Ball.mp hx
      simpa only [caccioppoli_native_euclidean_eq] using hxe.le
    have hm : (x, t₀) ∈ K := by
      change parabolicHomeomorph (x, t₀) ∈
        euclideanClosedBall x₀ R' ×ˢ Icc (t₀ - ρ ^ 2) t₀
      change x ∈ euclideanClosedBall x₀ R' ∧ t₀ ∈ Icc (t₀ - ρ ^ 2) t₀
      exact ⟨hx', ⟨sub_le_self _ (sq_nonneg ρ), le_rfl⟩⟩
    exact (hKbox hm).1
  have hT : Ioc (t₀ - ρ ^ 2) t₀ ⊆ J := by
    intro s hs
    have hx : x₀ ∈ euclideanClosedBall x₀ R' := by
      exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR'pos.le).2
        (by simpa [vecEuclideanNorm, vecNormSq, vecDot] using hR'pos.le)
    have hm : (x₀, s) ∈ K := by
      change parabolicHomeomorph (x₀, s) ∈
        euclideanClosedBall x₀ R' ×ˢ Icc (t₀ - ρ ^ 2) t₀
      change x₀ ∈ euclideanClosedBall x₀ R' ∧ s ∈ Icc (t₀ - ρ ^ 2) t₀
      exact ⟨hx, ⟨le_of_lt hs.1, hs.2⟩⟩
    exact (hKbox hm).2
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
  have hgood : ∀ᵐ s ∂volume.restrict (Ioc (t₀ - ρ ^ 2) t₀),
      ((MemLp (fun x : Vec3 => u (x, s)) 2 (volume.restrict Ω') ∧
        MemLp (fun x : Vec3 => Du (x, s)) 2 (volume.restrict Ω')) ∧
        ∀ i : Fin 3, HasWeakGradientOn Ω'
          (fun x => u (x, s) i) (fun x => Du (x, s) i)) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hT hslice,
      ae_restrict_of_ae_restrict_of_subset hT hgradAll] with s hs hg
    exact ⟨hs, hg⟩
  refine ⟨R', Ω', J, hρR', hbox, hball, hT, ?_⟩
  filter_upwards [hgood] with s hs
  exact poincareSobolevL1_vec3_slice_euclidean (U := Ω') hbox.1 hρ hρR'
    (fun x hx => hball x hx) (fun x => u (x, s)) (fun x => Du (x, s))
    (fun i => hs.1.1.eval i) (fun i => hs.1.2.eval i) hs.2

theorem caccioppoli_heat_cutoff_cancel
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ ε r : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hr : 0 < r) (hεr : ε < r ^ 2)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I)
    (hfuture : Icc t₀ (t₀ + ε) ⊆ I) :
    ∀ᵐ s ∂volume.restrict (Ioc (t₀ - ρ ^ 2) t₀),
      ∀ x : ℝ, parametricPairing
        (fun s y => backwardHeatCutoff
          (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r (y, s))
        (fun _ : Vec3 => 0) (fun y => u (y, s)) (fun _ => 0) x = 0 := by
  obtain ⟨R, Ω', J, hρR, hbox, hball, hT, _⟩ :=
    caccioppoli_slice_poincare_ae hsol hρ hsub
  let K : Set Vec3 := euclideanClosedBall x₀ (3 * ρ / 4)
  let F : Vec3 × ℝ → ℝ :=
    fun z => backwardHeatCutoff
      (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z
  let Ψ : ℝ → Vec3 → ℝ := fun s y => F (y, s)
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact isCompact_euclideanClosedBall x₀ (by positivity)
  have hKR : K ⊆ vec3Ball x₀ R := by
    intro x hx
    rw [mem_vec3Ball]
    have hx' := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).1 hx
    have hlt : 3 * ρ / 4 < R := by linarith only [hρR, hρ]
    simpa only [caccioppoli_native_euclidean_eq] using hx'.trans_lt hlt
  have hKΩ : K ⊆ Ω := by
    intro x hx
    have hmem : (x, t₀ - ρ ^ 2) ∈ closure (parabolicCylinder x₀ t₀ ρ) := by
      rw [closure_parabolicCylinder hρ]
      have hx' := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).1 hx
      have hxr' : vecEuclideanNorm (x - x₀) ≤ ρ := by
        have hρ34 : 3 * ρ / 4 ≤ ρ := by linarith only [hρ]
        exact hx'.trans hρ34
      have hxr : vec3EuclideanNorm (x - x₀) ≤ ρ := by
        simpa only [caccioppoli_native_euclidean_eq] using hxr'
      exact ⟨hxr, ⟨le_rfl, sub_le_self _ (sq_nonneg ρ)⟩⟩
    exact (hsub hmem).1
  have hKΩ' : K ⊆ Ω' := by
    intro x hx
    exact hball x (hKR hx)
  have hFsupport : Function.support F ⊆
      euclideanBall x₀ (3 * ρ / 4) ×ˢ (Set.univ : Set ℝ) := by
    intro z hz
    have hη : caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε z ≠ 0 := by
      intro hzero
      apply hz
      simp [F, backwardHeatCutoff, hzero]
    have hm := caccioppoli_heat_cutoff_support_subset x₀ t₀ ρ ε hρ hε
      (Function.mem_support.mpr hη)
    exact ⟨hm.1, mem_univ _⟩
  have hKclosed : IsClosed K := by
    dsimp [K]
    exact isClosed_euclideanClosedBall x₀ (3 * ρ / 4)
  have hK₀ : ∀ s y, y ∉ K → Ψ s y = 0 := by
    intro s y hy
    by_contra hne
    have hmem := hFsupport (Function.mem_support.mpr hne)
    have hle : y ∈ K := by
      apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
      exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hmem.1).le
    exact hy hle
  have hK₁ : ∀ s y i, y ∉ K → spatialDeriv (Ψ s) i y = 0 := by
    intro s y i hy
    have hnear : ∀ᶠ w in 𝓝 y, w ∉ K := hKclosed.isOpen_compl.mem_nhds hy
    have hzero : (fun w : Vec3 => Ψ s w) =ᶠ[𝓝 y]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [hnear] with w hw
      exact hK₀ s w hw
    rw [spatialDeriv, hzero.fderiv_eq, fderiv_const_apply]
    simp
  have hK₂ : ∀ s y i j, y ∉ K → mixedSecond (Ψ s) i j y = 0 := by
    intro s y i j hy
    have hnear : ∀ᶠ w in 𝓝 y, w ∉ K := hKclosed.isOpen_compl.mem_nhds hy
    have hzero : (fun w : Vec3 => spatialDeriv (Ψ s) j w) =ᶠ[𝓝 y]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [hnear] with w hw
      exact hK₁ s w j hw
    change (fderiv ℝ (fun w : Vec3 => spatialDeriv (Ψ s) j w) y)
        (basisVec i) = 0
    rw [hzero.fderiv_eq, fderiv_const_apply]
    simp
  have htest := caccioppoli_heat_cutoff_testFunction hsol hρ hε hr hεr hsub hfuture
  have hFcont : ContDiff ℝ (⊤ : ℕ∞) F := by
    simpa only [F] using htest.1.1
  have hΨ₀ : Continuous (fun z : ℝ × Vec3 => Ψ z.1 z.2) := by
    have hcomp := hFcont.continuous.comp (continuous_snd.prodMk continuous_fst)
    change Continuous (fun z : ℝ × Vec3 => F (z.2, z.1)) at hcomp
    simpa only [Ψ] using hcomp
  have hΨ₁ : ∀ i : Fin 3,
      Continuous (fun z : ℝ × Vec3 => spatialDeriv (Ψ z.1) i z.2) := by
    intro i
    have hsp := spatialPartial_contDiff hFcont i
    have hcomp := hsp.continuous.comp (continuous_snd.prodMk continuous_fst)
    change Continuous (fun z : ℝ × Vec3 => spatialPartial F i (z.2, z.1)) at hcomp
    simpa only [Ψ, spatialPartial, spatialDeriv] using hcomp
  have hΨ₂ : ∀ i j : Fin 3,
      Continuous (fun z : ℝ × Vec3 => mixedSecond (Ψ z.1) i j z.2) := by
    intro i j
    have hsp := spatialPartial_contDiff (spatialPartial_contDiff hFcont j) i
    have hcomp := hsp.continuous.comp (continuous_snd.prodMk continuous_fst)
    change Continuous (fun z : ℝ × Vec3 =>
      (fderiv ℝ (fun x =>
        (fderiv ℝ (fun y => F (y, z.1)) x) (basisVec j)) z.2)
          (basisVec i))
    exact hcomp
  have hCtest : ∀ ψ ∈ Set.range (fun s : ℚ => fun y : Vec3 => Ψ s y),
      ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Ω := by
    intro ψ hψ
    obtain ⟨s, rfl⟩ := hψ
    have hψmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Vec3 => (y, (s : ℝ))) :=
      contDiff_id.prodMk (contDiff_const :
        ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec3 => (s : ℝ)))
    have hψcont := hFcont.comp hψmap
    have hψsupport : Function.support (fun y : Vec3 => Ψ (s : ℝ) y) ⊆ K := by
      intro y hy
      have hmem := hFsupport (Function.mem_support.mpr hy)
      apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
      exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hmem.1).le
    have hψts : tsupport (fun y : Vec3 => Ψ (s : ℝ) y) ⊆ K := by
      apply closure_minimal hψsupport hKclosed
    refine ⟨?_, ?_, ?_⟩
    · change ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => F (y, (s : ℝ))) at hψcont
      simpa only [Ψ] using hψcont
    · exact HasCompactSupport.intro hKcompact (fun y hy =>
        not_not.mp (fun hne => hy (hψsupport (Function.mem_support.mpr hne))))
    · exact hψts.trans hKΩ
  have hCcount : (Set.range (fun s : ℚ => fun y : Vec3 => Ψ (s : ℝ) y)).Countable :=
    Set.countable_range _
  have hsliceI := caccioppoli_I2_slice_divfree_countable hsol hCcount hCtest
  have hsliceT : ∀ᵐ s ∂volume.restrict (Ioc (t₀ - ρ ^ 2) t₀), ∀ ψ ∈
      Set.range (fun s : ℚ => fun y : Vec3 => Ψ s y),
      ∫ x in Ω, ∑ i, u (x, s) i * (fderiv ℝ ψ x) (basisVec i) = 0 := by
    exact ae_restrict_of_ae_restrict_of_subset
      (fun s hs => hbox.2.2.2.2.2 (subset_closure (hT s hs))) hsliceI
  have hmem := ae_restrict_of_ae_restrict_of_subset hT
    (slice_memLp_ae_of_sws hsol hbox)
  have hu : ∀ᵐ s ∂volume.restrict (Ioc (t₀ - ρ ^ 2) t₀),
      IntegrableOn (fun x => u (x, s)) K volume := by
    filter_upwards [hmem] with s hs
    let _ : IsFiniteMeasure (volume.restrict K) := by
      exact isFiniteMeasure_restrict.mpr hKcompact.measure_lt_top.ne
    have hKmem : MemLp (fun x : Vec3 => u (x, s))
        2 (volume.restrict K) :=
      hs.1.mono_measure (Measure.restrict_mono_set volume hKΩ')
    change Integrable (fun x : Vec3 => u (x, s)) (volume.restrict K)
    exact hKmem.integrable (by norm_num)
  have hCscalar : (Set.range (fun s : ℚ => (s : ℝ))).Countable :=
    Set.countable_range _
  exact caccioppoli_countable_slice_cancel hKcompact Ψ
    hCscalar Rat.denseRange_cast
    hΨ₀ hΨ₁ hΨ₂ hK₀ hK₁ hK₂ hCtest hsliceT hu


end CKN
