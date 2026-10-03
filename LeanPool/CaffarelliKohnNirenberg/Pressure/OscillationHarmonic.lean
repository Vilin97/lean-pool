/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SupportRestrict
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorSmooth
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorEstimates
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.LpConvergence
public import LeanPool.CaffarelliKohnNirenberg.Pressure.DecompositionPotentials
public import LeanPool.CaffarelliKohnNirenberg.Pressure.DecompositionSWSBasic

/-!
# Oscillation Harmonic

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open CKN.Foundation.Heat

noncomputable section

namespace CKN

private lemma euclideanBall_eq_vec3Ball_oscillation {x₀ : Vec3} {r : ℝ}
    (hr : 0 < r) : euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  change x ∈ euclideanBall x₀ r ↔ vec3EuclideanNorm (x - x₀) < r
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
    (mem_euclideanBall_iff_vecEuclideanNorm_lt hr)

private lemma euclideanBall_measurable_oscillation (x₀ : Vec3) (r : ℝ) :
    MeasurableSet (euclideanBall x₀ r) := by
  have hopen : IsOpen (euclideanBall x₀ r) := by
    change IsOpen {y : Vec3 | euclideanSqDist y x₀ < r ^ 2}
    exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
  exact hopen.measurableSet

private lemma euclideanBall_finite_oscillation {x₀ : Vec3} {r : ℝ} (hr : 0 < r) :
    IsFiniteMeasure (volume.restrict (euclideanBall x₀ r)) := by
  rw [isFiniteMeasure_restrict, euclideanBall_eq_vec3Ball_oscillation hr]
  exact (volume_vec3Ball_lt_top (x := x₀) (r := r)).ne

/-! The weak-to-smooth pressure component used by the oscillation estimate. -/

theorem pressure_harmonic_part_on_inner
    {h : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hmem : MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ)))
    (hweak : WeaklyHarmonicOn (euclideanBall x₀ ρ) h) :
    ∃ H : Vec3 → ℝ,
      ContDiffOn ℝ (1 : ℕ∞) H (euclideanBall x₀ (ρ / 2)) ∧
      h =ᵐ[volume.restrict (euclideanBall x₀ (ρ / 2))] H ∧
      (∀ x ∈ euclideanBall x₀ (ρ / 2),
        |H x| ≤ weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ ρ))) ∧
      (∀ x ∈ euclideanBall x₀ (ρ / 2),
        vec3EuclideanNorm (classicalGradient H x) ≤
          1728 * harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹ *
            lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall x₀ ρ))) := by
  exact weakly_harmonic_interior_smooth hρ hmem hweak

theorem pressure_harmonic_inner_integral_bound
    {H : Vec3 → ℝ} {x₀ : Vec3} {ρ r A : ℝ} (hρ : 0 < ρ)
    (hr : 0 < r) (hhalf : r ≤ ρ / 2) (_ : 0 ≤ A)
    (hHmem : MemLp H (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ r)))
    (hHbound : ∀ x ∈ euclideanBall x₀ (ρ / 2), |H x| ≤ A) :
    ∫ x in euclideanBall x₀ r, |H x| ^ (3 / 2 : ℝ) ≤
      (volume (euclideanBall x₀ r)).toReal * A ^ (3 / 2 : ℝ) := by
  let Br : Set Vec3 := euclideanBall x₀ r
  have hHint : Integrable (fun x => |H x| ^ (3 / 2 : ℝ))
      (volume.restrict Br) := by
    have h := hHmem.integrable_norm_rpow (by norm_num) (by norm_num)
    convert h using 1
    norm_num
  let _ : IsFiniteMeasure (volume.restrict Br) :=
    euclideanBall_finite_oscillation hr
  have hconst : Integrable (fun _ : Vec3 => A ^ (3 / 2 : ℝ))
      (volume.restrict Br) := integrable_const _
  change (∫ x, |H x| ^ (3 / 2 : ℝ) ∂(volume.restrict Br)) ≤ _
  calc
    (∫ x, |H x| ^ (3 / 2 : ℝ) ∂(volume.restrict Br)) ≤
        ∫ x, A ^ (3 / 2 : ℝ) ∂(volume.restrict Br) := by
      apply integral_mono_ae hHint hconst
      filter_upwards [ae_restrict_mem
          (euclideanBall_measurable_oscillation x₀ r)] with x hx
      exact Real.rpow_le_rpow (abs_nonneg _) (hHbound x (by
        apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
        exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hx).trans_le hhalf))
        (by norm_num)
    _ = (volume (euclideanBall x₀ r)).toReal * A ^ (3 / 2 : ℝ) := by
      simp [Br, Measure.real]

private lemma spatialLaplacian_zero_of_notMem_tsupport
    {ψ : Vec3 → ℝ} {x : Vec3} (hx : x ∉ tsupport ψ) :
    spatialLaplacian ψ x = 0 := by
  simp only [spatialLaplacian]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hxi : x ∉ tsupport (spatialDeriv ψ i) := by
    intro hi
    apply hx
    exact closure_minimal (by
      intro y hy
      by_contra hyt
      exact hy (by simp [spatialDeriv, fderiv_of_notMem_tsupport (𝕜 := ℝ) hyt]))
      (isClosed_tsupport ψ) hi
  simp [spatialDeriv, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxi]

theorem pressureNewtonianPotential_weaklyHarmonicOn
    {U : Set Vec3} {g : Vec3 → ℝ}
    (hg : Integrable g volume)
    (hgc : HasCompactSupport g)
    (hzero : ∀ y ∈ U, g y = 0) :
    WeaklyHarmonicOn U (pressureNewtonianPotential g) := by
  intro ψ hψ hψc hψU
  have hprod : Integrable
      (fun x : Vec3 => pressureNewtonianPotential g x * spatialLaplacian ψ x)
      volume := by
    exact pressureNewtonianPotential_mul_smooth_integrable hg hgc
      (contDiff_spatialLaplacian_smooth hψ)
      (laplacian_compact_support_global hψc)
  have hzeroOut : ∀ x, x ∉ U →
      pressureNewtonianPotential g x * spatialLaplacian ψ x = 0 := by
    intro x hx
    have hxt : x ∉ tsupport ψ := fun hxt => hx (hψU hxt)
    rw [spatialLaplacian_zero_of_notMem_tsupport hxt, mul_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzeroOut]
  rw [pressureNewtonianPotential_distributional_pairing hg hgc hψ hψc]
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  by_cases hy : y ∈ U
  · simp [hzero y hy]
  · have hyt : y ∉ tsupport ψ := fun hyt => hy (hψU hyt)
    simp [image_eq_zero_of_notMem_tsupport hyt]

theorem pressureNewtonianDerivativePotential_weaklyHarmonicOn
    {U : Set Vec3} {g : Vec3 → ℝ} (i : Fin 3)
    (hg : Integrable g volume) (hgc : HasCompactSupport g)
    (hzero : ∀ y ∈ U, g y = 0) :
    WeaklyHarmonicOn U (pressureNewtonianDerivativePotential i g) := by
  intro ψ hψ hψc hψU
  have hprod : Integrable
      (fun x : Vec3 => pressureNewtonianDerivativePotential i g x *
        spatialLaplacian ψ x) volume := by
    exact pressureNewtonianDerivativePotential_mul_smooth_integrable (i := i) hg hgc
      (contDiff_spatialLaplacian_smooth hψ)
      (laplacian_compact_support_global hψc)
  have hzeroOut : ∀ x, x ∉ U →
      pressureNewtonianDerivativePotential i g x * spatialLaplacian ψ x = 0 := by
    intro x hx
    have hxt : x ∉ tsupport ψ := fun hxt => hx (hψU hxt)
    rw [spatialLaplacian_zero_of_notMem_tsupport hxt, mul_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzeroOut]
  rw [pressureNewtonianDerivativePotential_distributional_pairing_smooth hg hgc hψ hψc]
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  by_cases hy : y ∈ U
  · simp [hzero y hy]
  · have hyt : y ∉ tsupport ψ := fun hyt => hy (hψU hyt)
    have hderivzero : spatialDeriv ψ i y = 0 := by
      simp [spatialDeriv, fderiv_of_notMem_tsupport (𝕜 := ℝ) hyt]
    simp [hderivzero]

/-- Integrability, support, and inner-ball vanishing data for the annular pressure terms. -/
structure PressureHarmonicPotentialData
    (U : Set Vec3) (η : Vec3 → ℝ) (u : ParabolicPoint → Vec3)
    (c : ℝ → Vec3) (p : ParabolicPoint → ℝ) (s : ℝ) : Prop where
  p2_integrable : ∀ i j, Integrable
    (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) volume
  p2_compactSupport : ∀ i j, HasCompactSupport
    (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j)
  p2_vanishes : ∀ i j y, y ∈ U →
    mixedSecond η i j y * pressureUTensor u c (y, s) i j = 0
  p3_integrable : ∀ i j, Integrable
    (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) volume
  p3_compactSupport : ∀ i j, HasCompactSupport
    (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y)
  p3_vanishes : ∀ i j y, y ∈ U →
    pressureUTensor u c (y, s) i j * spatialDeriv η i y = 0
  p4_integrable : ∀ i j, Integrable
    (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) volume
  p4_compactSupport : ∀ i j, HasCompactSupport
    (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y)
  p4_vanishes : ∀ i j y, y ∈ U →
    pressureUTensor u c (y, s) i j * spatialDeriv η j y = 0
  p5_integrable : Integrable
    (fun y => p (y, s) * spatialLaplacian η y) volume
  p5_compactSupport : HasCompactSupport
    (fun y => p (y, s) * spatialLaplacian η y)
  p5_vanishes : ∀ y ∈ U, p (y, s) * spatialLaplacian η y = 0
  p6_integrable : ∀ j, Integrable
    (fun y => spatialDeriv η j y * p (y, s)) volume
  p6_compactSupport : ∀ j, HasCompactSupport
    (fun y => spatialDeriv η j y * p (y, s))
  p6_vanishes : ∀ j y, y ∈ U → spatialDeriv η j y * p (y, s) = 0

private lemma pressure_harmonic_potentials_weaklyHarmonicOn_hsum₂_1 :
    ∀ {U : Set Vec3} {_ : ℝ} (ψ : Vec3 → ℝ) {A : Fin 3 → Fin 3 → Vec3 → ℝ},
      (∀ (i j : Fin 3),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
            (fun (x : Vec3) => A i j x * spatialLaplacian ψ x) volume) →
        (∀ (i j : Fin 3),
            (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume U) fun x =>
                A i j x * spatialLaplacian ψ x) =
              0) →
          (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume U) fun x =>
              (∑ i : Fin 3, ∑ j : Fin 3, A i j x) * spatialLaplacian ψ x) =
            0
    := by
  intro U s ψ A hA hAzero
  rw [show (fun x => (∑ i, ∑ j, A i j x) * spatialLaplacian ψ x) =
    fun x => ∑ i, ∑ j, A i j x * spatialLaplacian ψ x by
      funext x
      simp_rw [Finset.sum_mul]]
  calc
    _ = ∑ i, ∫ x in U, ∑ j, A i j x * spatialLaplacian ψ x := by
      exact integral_finsetSum (s := (Finset.univ : Finset (Fin 3)))
        (fun i _ => integrable_finsetSum' (Finset.univ : Finset (Fin 3))
          (fun j _ => (hA i j).integrableOn))
    _ = ∑ i, ∑ j, ∫ x in U, A i j x * spatialLaplacian ψ x := by
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_finsetSum (s := (Finset.univ : Finset (Fin 3)))
        (fun j _ => (hA i j).integrableOn)
    _ = 0 := by simp only [hAzero, Finset.sum_const_zero]

private lemma pressure_harmonic_potentials_weaklyHarmonicOn_h6sum_2 :
    ∀ {U : Set Vec3} {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {s : ℝ}
      (ψ : Vec3 → ℝ),
      (∀ (i j : Fin 3),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
            (fun (x : Vec3) =>
              pressureNewtonianPotential
                  (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) x *
                spatialLaplacian ψ x)
            volume) →
        let F₂ : Vec3 → ℝ := fun x =>
          (∑ i : Fin 3,
              ∑ j : Fin 3,
                pressureNewtonianPotential
                  (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) x) *
            spatialLaplacian ψ x;
        @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace F₂ (Measure.restrict volume U)
    := by
  intro U η u c s ψ h2int F₂
  change Integrable (fun x => (∑ i, ∑ j, pressureNewtonianPotential
    (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) x) *
    spatialLaplacian ψ x) (volume.restrict U)
  rw [show (fun x => (∑ i, ∑ j, pressureNewtonianPotential
    (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) x) *
    spatialLaplacian ψ x) = fun x => ∑ i, ∑ j,
    pressureNewtonianPotential
      (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) x *
      spatialLaplacian ψ x by
    funext x
    simp_rw [Finset.sum_mul]]
  exact integrable_finsetSum' (Finset.univ : Finset (Fin 3))
    (fun i _ => integrable_finsetSum' (Finset.univ : Finset (Fin 3))
      (fun j _ => (h2int i j).integrableOn))

private lemma pressure_harmonic_potentials_weaklyHarmonicOn_hF3_3 :
    ∀ {U : Set Vec3} {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {s : ℝ}
      (ψ : Vec3 → ℝ),
      (∀ (i j : Fin 3),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
            (fun (x : Vec3) =>
              pressureNewtonianDerivativePotential j
                  (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) x *
                spatialLaplacian ψ x)
            volume) →
        let F₃ : Vec3 → ℝ := fun x =>
          (∑ i : Fin 3,
              ∑ j : Fin 3,
                pressureNewtonianDerivativePotential j
                  (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) x) *
            spatialLaplacian ψ x;
        @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace F₃ (Measure.restrict volume U)
    := by
  intro U η u c s ψ h3int F₃
  change Integrable (fun x => (∑ i, ∑ j, pressureNewtonianDerivativePotential j
    (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) x) *
    spatialLaplacian ψ x) (volume.restrict U)
  rw [show (fun x => (∑ i, ∑ j, pressureNewtonianDerivativePotential j
    (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) x) *
    spatialLaplacian ψ x) = fun x => ∑ i, ∑ j,
    pressureNewtonianDerivativePotential j
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) x *
      spatialLaplacian ψ x by
    funext x
    simp_rw [Finset.sum_mul]]
  exact integrable_finsetSum' (Finset.univ : Finset (Fin 3))
    (fun i _ => integrable_finsetSum' (Finset.univ : Finset (Fin 3))
      (fun j _ => (h3int i j).integrableOn))

private lemma pressure_harmonic_potentials_weaklyHarmonicOn_hF4_4 :
    ∀ {U : Set Vec3} {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {s : ℝ}
      (ψ : Vec3 → ℝ),
      (∀ (i j : Fin 3),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
            (fun (x : Vec3) =>
              pressureNewtonianDerivativePotential i
                  (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) x *
                spatialLaplacian ψ x)
            volume) →
        let F₄ : Vec3 → ℝ := fun x =>
          (∑ i : Fin 3,
              ∑ j : Fin 3,
                pressureNewtonianDerivativePotential i
                  (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) x) *
            spatialLaplacian ψ x;
        @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace F₄ (Measure.restrict volume U)
    := by
  intro U η u c s ψ h4int F₄
  change Integrable (fun x => (∑ i, ∑ j, pressureNewtonianDerivativePotential i
    (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) x) *
    spatialLaplacian ψ x) (volume.restrict U)
  rw [show (fun x => (∑ i, ∑ j, pressureNewtonianDerivativePotential i
    (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) x) *
    spatialLaplacian ψ x) = fun x => ∑ i, ∑ j,
    pressureNewtonianDerivativePotential i
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) x *
      spatialLaplacian ψ x by
    funext x
    simp_rw [Finset.sum_mul]]
  exact integrable_finsetSum' (Finset.univ : Finset (Fin 3))
    (fun i _ => integrable_finsetSum' (Finset.univ : Finset (Fin 3))
      (fun j _ => (h4int i j).integrableOn))

private lemma pressure_harmonic_potentials_weaklyHarmonicOn_hF5_5 :
    ∀ {U : Set Vec3} {η : Vec3 → ℝ} {p : ParabolicPoint → ℝ} {s : ℝ} (ψ : Vec3 → ℝ),
      (∀ (j : Fin 3),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
            (fun (x : Vec3) =>
              pressureNewtonianDerivativePotential j (fun y => spatialDeriv η j y * p (y, s)) x *
                spatialLaplacian ψ x)
            volume) →
        let F₆ : Vec3 → ℝ := fun x =>
          (∑ j : Fin 3,
              pressureNewtonianDerivativePotential j (fun y => spatialDeriv η j y * p (y, s)) x) *
            spatialLaplacian ψ x;
        @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace F₆ (Measure.restrict volume U)
    := by
  intro U η p s ψ h6int F₆
  change Integrable (fun x => (∑ j, pressureNewtonianDerivativePotential j
    (fun y => spatialDeriv η j y * p (y, s)) x) * spatialLaplacian ψ x)
    (volume.restrict U)
  rw [show (fun x => (∑ j, pressureNewtonianDerivativePotential j
    (fun y => spatialDeriv η j y * p (y, s)) x) * spatialLaplacian ψ x) =
    fun x => ∑ j, pressureNewtonianDerivativePotential j
      (fun y => spatialDeriv η j y * p (y, s)) x * spatialLaplacian ψ x by
    funext x
    simp_rw [Finset.sum_mul]]
  exact integrable_finsetSum' (Finset.univ : Finset (Fin 3))
    (fun j _ => (h6int j).integrableOn)

theorem pressure_harmonic_potentials_weaklyHarmonicOn
    {U : Set Vec3} {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3}
    {c : ℝ → Vec3} {p : ParabolicPoint → ℝ} {s : ℝ}
    (hP2Int : ∀ i j, Integrable
      (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) volume)
    (hP2Supp : ∀ i j, HasCompactSupport
      (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j))
    (hP2zero : ∀ i j y, y ∈ U →
      mixedSecond η i j y * pressureUTensor u c (y, s) i j = 0)
    (hP3Int : ∀ i j, Integrable
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) volume)
    (hP3Supp : ∀ i j, HasCompactSupport
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y))
    (hP3zero : ∀ i j y, y ∈ U →
      pressureUTensor u c (y, s) i j * spatialDeriv η i y = 0)
    (hP4Int : ∀ i j, Integrable
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) volume)
    (hP4Supp : ∀ i j, HasCompactSupport
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y))
    (hP4zero : ∀ i j y, y ∈ U →
      pressureUTensor u c (y, s) i j * spatialDeriv η j y = 0)
    (hP5Int : Integrable
      (fun y => p (y, s) * spatialLaplacian η y) volume)
    (hP5Supp : HasCompactSupport
      (fun y => p (y, s) * spatialLaplacian η y))
    (hP5zero : ∀ y ∈ U, p (y, s) * spatialLaplacian η y = 0)
    (hP6Int : ∀ j, Integrable
      (fun y => spatialDeriv η j y * p (y, s)) volume)
    (hP6Supp : ∀ j, HasCompactSupport
      (fun y => spatialDeriv η j y * p (y, s)))
    (hP6zero : ∀ j y, y ∈ U → spatialDeriv η j y * p (y, s) = 0) :
    WeaklyHarmonicOn U
      (pressureP2 η u c s + pressureP3 η u c s + pressureP4 η u c s +
        pressureP5 η p s + pressureP6 η p s) := by
  have h2 (i j : Fin 3) : WeaklyHarmonicOn U
      (pressureNewtonianPotential
        (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j)) :=
    pressureNewtonianPotential_weaklyHarmonicOn
      (hP2Int i j) (hP2Supp i j) (hP2zero i j)
  have h3 (i j : Fin 3) : WeaklyHarmonicOn U
      (pressureNewtonianDerivativePotential j
        (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y)) :=
    pressureNewtonianDerivativePotential_weaklyHarmonicOn j
      (hP3Int i j) (hP3Supp i j) (hP3zero i j)
  have h4 (i j : Fin 3) : WeaklyHarmonicOn U
      (pressureNewtonianDerivativePotential i
        (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y)) :=
    pressureNewtonianDerivativePotential_weaklyHarmonicOn i
      (hP4Int i j) (hP4Supp i j) (hP4zero i j)
  have h5 : WeaklyHarmonicOn U
      (pressureNewtonianPotential
        (fun y => p (y, s) * spatialLaplacian η y)) :=
    pressureNewtonianPotential_weaklyHarmonicOn hP5Int hP5Supp hP5zero
  have h6 (j : Fin 3) : WeaklyHarmonicOn U
      (pressureNewtonianDerivativePotential j
        (fun y => spatialDeriv η j y * p (y, s))) :=
    pressureNewtonianDerivativePotential_weaklyHarmonicOn j
      (hP6Int j) (hP6Supp j) (hP6zero j)
  intro ψ hψ hψc hψU
  have h2zero (i j : Fin 3) := h2 i j ψ hψ hψc hψU
  have h3zero (i j : Fin 3) := h3 i j ψ hψ hψc hψU
  have h4zero (i j : Fin 3) := h4 i j ψ hψ hψc hψU
  have h5zero := h5 ψ hψ hψc hψU
  have h6zero (j : Fin 3) := h6 j ψ hψ hψc hψU
  have h2int (i j : Fin 3) : Integrable
      (fun x => pressureNewtonianPotential
        (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) x *
          spatialLaplacian ψ x) volume := by
    exact pressureNewtonianPotential_mul_smooth_integrable
      (hP2Int i j) (hP2Supp i j)
      (contDiff_spatialLaplacian_smooth hψ)
      (laplacian_compact_support_global hψc)
  have h3int (i j : Fin 3) : Integrable
      (fun x => pressureNewtonianDerivativePotential j
        (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) x *
          spatialLaplacian ψ x) volume := by
    exact pressureNewtonianDerivativePotential_mul_smooth_integrable
      (i := j) (hP3Int i j) (hP3Supp i j)
      (contDiff_spatialLaplacian_smooth hψ)
      (laplacian_compact_support_global hψc)
  have h4int (i j : Fin 3) : Integrable
      (fun x => pressureNewtonianDerivativePotential i
        (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) x *
          spatialLaplacian ψ x) volume := by
    exact pressureNewtonianDerivativePotential_mul_smooth_integrable
      (i := i) (hP4Int i j) (hP4Supp i j)
      (contDiff_spatialLaplacian_smooth hψ)
      (laplacian_compact_support_global hψc)
  have h5int : Integrable
      (fun x => pressureNewtonianPotential
        (fun y => p (y, s) * spatialLaplacian η y) x *
          spatialLaplacian ψ x) volume := by
    exact pressureNewtonianPotential_mul_smooth_integrable hP5Int hP5Supp
      (contDiff_spatialLaplacian_smooth hψ)
      (laplacian_compact_support_global hψc)
  have h6int (j : Fin 3) : Integrable
      (fun x => pressureNewtonianDerivativePotential j
        (fun y => spatialDeriv η j y * p (y, s)) x *
          spatialLaplacian ψ x) volume := by
    exact pressureNewtonianDerivativePotential_mul_smooth_integrable
      (i := j) (hP6Int j) (hP6Supp j)
      (contDiff_spatialLaplacian_smooth hψ)
      (laplacian_compact_support_global hψc)
  let F₂ : Vec3 → ℝ := fun x =>
    (∑ i, ∑ j, pressureNewtonianPotential
      (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) x) *
      spatialLaplacian ψ x
  let F₃ : Vec3 → ℝ := fun x =>
    (∑ i, ∑ j, pressureNewtonianDerivativePotential j
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) x) *
      spatialLaplacian ψ x
  let F₄ : Vec3 → ℝ := fun x =>
    (∑ i, ∑ j, pressureNewtonianDerivativePotential i
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) x) *
      spatialLaplacian ψ x
  let F₅ : Vec3 → ℝ := fun x =>
    pressureNewtonianPotential
      (fun y => p (y, s) * spatialLaplacian η y) x * spatialLaplacian ψ x
  let F₆ : Vec3 → ℝ := fun x =>
    (∑ j, pressureNewtonianDerivativePotential j
      (fun y => spatialDeriv η j y * p (y, s)) x) * spatialLaplacian ψ x
  have hsum₂ {A : Fin 3 → Fin 3 → Vec3 → ℝ}
      (hA : ∀ i j, Integrable (fun x => A i j x * spatialLaplacian ψ x) volume)
      (hAzero : ∀ i j, ∫ x in U, A i j x * spatialLaplacian ψ x = 0) :=
        @pressure_harmonic_potentials_weaklyHarmonicOn_hsum₂_1 U s ψ A hA hAzero
  have hsum₁ {A : Fin 3 → Vec3 → ℝ}
      (hA : ∀ j, Integrable (fun x => A j x * spatialLaplacian ψ x) volume)
      (hAzero : ∀ j, ∫ x in U, A j x * spatialLaplacian ψ x = 0) :
      ∫ x in U, (∑ j, A j x) * spatialLaplacian ψ x = 0 := by
    rw [show (fun x => (∑ j, A j x) * spatialLaplacian ψ x) =
      fun x => ∑ j, A j x * spatialLaplacian ψ x by
        funext x
        simp_rw [Finset.sum_mul]]
    rw [integral_finsetSum (s := (Finset.univ : Finset (Fin 3)))
      (fun j _ => (hA j).integrableOn)]
    simp only [hAzero, Finset.sum_const_zero]
  have h2sum : ∫ x in U, F₂ x = 0 := hsum₂ h2int h2zero
  have h3sum : ∫ x in U, F₃ x = 0 := hsum₂ h3int h3zero
  have h4sum : ∫ x in U, F₄ x = 0 := hsum₂ h4int h4zero
  have h6sum : ∫ x in U, F₆ x = 0 := hsum₁ h6int h6zero
  have hF2 := @pressure_harmonic_potentials_weaklyHarmonicOn_h6sum_2 U η u c s ψ h2int
  have hF3 := @pressure_harmonic_potentials_weaklyHarmonicOn_hF3_3 U η u c s ψ h3int
  have hF4 := @pressure_harmonic_potentials_weaklyHarmonicOn_hF4_4 U η u c s ψ h4int
  have hF5 : Integrable F₅ (volume.restrict U) := h5int.integrableOn
  have hF6 := @pressure_harmonic_potentials_weaklyHarmonicOn_hF5_5 U η p s ψ h6int
  have hrewrite :
      (fun x => (pressureP2 η u c s + pressureP3 η u c s + pressureP4 η u c s +
        pressureP5 η p s + pressureP6 η p s) x * spatialLaplacian ψ x) =
      (fun x => F₂ x + F₃ x + F₄ x - F₅ x - 2 * F₆ x) := by
    funext x
    simp only [pressureP2, pressureP3, pressureP4, pressureP5, pressureP6,
      Pi.add_apply]
    dsimp [F₂, F₃, F₄, F₅, F₆]
    ring
  rw [hrewrite]
  calc
    (∫ x in U, F₂ x + F₃ x + F₄ x - F₅ x - 2 * F₆ x) =
        ∫ x in U, ((F₂ + F₃ + F₄ - F₅) x - (fun y => 2 * F₆ y) x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp
    _ = ((∫ x in U, (F₂ + F₃ + F₄ - F₅) x) -
        (∫ x in U, (fun y => 2 * F₆ y) x)) :=
      integral_sub (((hF2.add hF3).add hF4).sub hF5) (hF6.const_mul 2)
    _ = ((((∫ x in U, F₂ x) + (∫ x in U, F₃ x)) +
        (∫ x in U, F₄ x)) - (∫ x in U, F₅ x)) -
        (∫ x in U, (fun y => 2 * F₆ y) x) := by
      calc
        ((∫ x in U, (F₂ + F₃ + F₄ - F₅) x) -
            (∫ x in U, (fun y => 2 * F₆ y) x)) =
            ((∫ x in U, (F₂ + F₃ + F₄) x) - (∫ x in U, F₅ x)) -
              (∫ x in U, (fun y => 2 * F₆ y) x) := by
          change ((∫ x in U, (F₂ + F₃ + F₄) x - F₅ x) -
            (∫ x in U, (fun y => 2 * F₆ y) x)) = _
          rw [integral_sub ((hF2.add hF3).add hF4) hF5]
        _ = ((((∫ x in U, (F₂ + F₃) x) + (∫ x in U, F₄ x)) -
              (∫ x in U, F₅ x)) -
              (∫ x in U, (fun y => 2 * F₆ y) x)) := by
          change ((∫ x in U, (F₂ + F₃) x + F₄ x) -
            (∫ x in U, F₅ x) -
            (∫ x in U, (fun y => 2 * F₆ y) x)) = _
          rw [integral_add (hF2.add hF3) hF4]
        _ = ((((∫ x in U, F₂ x) + (∫ x in U, F₃ x)) +
              (∫ x in U, F₄ x)) - (∫ x in U, F₅ x)) -
              (∫ x in U, (fun y => 2 * F₆ y) x) := by
          change (((∫ x in U, F₂ x + F₃ x) + (∫ x in U, F₄ x)) -
            (∫ x in U, F₅ x) -
            (∫ x in U, (fun y => 2 * F₆ y) x)) = _
          rw [integral_add hF2 hF3]
    _ = 0 := by
      have h6const : (∫ x in U, (fun y => 2 * F₆ y) x) =
          2 * (∫ x in U, F₆ x) := by
        rw [integral_const_mul]
      have h5sum : (∫ x in U, F₅ x) = 0 := by
        simpa only [F₅] using h5zero
      simp only [h6const, h2sum, h3sum, h4sum, h5sum, h6sum,
        add_zero, sub_zero, mul_zero]

theorem pressure_harmonic_potentials_weaklyHarmonicOn_of_data
    {U : Set Vec3} {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3}
    {c : ℝ → Vec3} {p : ParabolicPoint → ℝ} {s : ℝ}
    (hdata : PressureHarmonicPotentialData U η u c p s) :
    WeaklyHarmonicOn U
      (pressureP2 η u c s + pressureP3 η u c s + pressureP4 η u c s +
        pressureP5 η p s + pressureP6 η p s) := by
  exact pressure_harmonic_potentials_weaklyHarmonicOn
    hdata.p2_integrable hdata.p2_compactSupport hdata.p2_vanishes
    hdata.p3_integrable hdata.p3_compactSupport hdata.p3_vanishes
    hdata.p4_integrable hdata.p4_compactSupport hdata.p4_vanishes
    hdata.p5_integrable hdata.p5_compactSupport hdata.p5_vanishes
    hdata.p6_integrable hdata.p6_compactSupport hdata.p6_vanishes

theorem pressure_harmonic_potential_data_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {η : Vec3 → ℝ} {c : ℝ → Vec3} {U : Set Vec3}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ Ω)
    (hηd0 : ∀ i y, y ∈ U → spatialDeriv η i y = 0)
    (hηm0 : ∀ i j y, y ∈ U → mixedSecond η i j y = 0)
    (hηLap0 : ∀ y, y ∈ U → spatialLaplacian η y = 0) :
    ∀ᵐ s ∂volume.restrict I,
      PressureHarmonicPotentialData U η u c p s := by
  obtain ⟨Omega, hrest⟩ :=
    decomposition_slice_integrability hsol hηc hηΩ hηc hηΩ
  rcases hrest with ⟨hOmegaOpen, hrest⟩
  rcases hrest with ⟨hEtaSup, hrest⟩
  rcases hrest with ⟨hEtaSup2, hrest⟩
  rcases hrest with ⟨hOmegaCompact, hrest⟩
  rcases hrest with ⟨hOmegaSub, hslice⟩
  have : IsFiniteMeasure (volume.restrict Omega) := by
    apply isFiniteMeasure_restrict.mpr
    exact (lt_of_le_of_lt (measure_mono (μ := volume) subset_closure)
      hOmegaCompact.measure_lt_top).ne
  filter_upwards [hslice] with s hs
  rcases hs with ⟨hu, hp, hf⟩
  have huComp (i : Fin 3) : MemLp (fun x : Vec3 => u (x, s) i) 2
      (volume.restrict Omega) :=
    hu.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
  have huInt (i : Fin 3) : Integrable (fun x : Vec3 => u (x, s) i)
      (volume.restrict Omega) := huComp i |>.integrable (by norm_num)
  have hUScalar {i j : Fin 3} {g : Vec3 → ℝ} (hg : Continuous g)
      (hgc : HasCompactSupport g) (hgΩ : tsupport g ⊆ Omega) : IntegrableOn
      (fun x => pressureUTensor u c (x, s) i j * g x) Omega volume := by
    have h'int := (CKN.Foundation.Measure.integrable_mul_of_tsupport_subset
      ((huComp i).integrable_mul (huComp j)) hg hgc hgΩ).integrableOn (s := Omega)
    have hi' := (CKN.Foundation.Measure.integrable_mul_of_tsupport_subset
      (huInt i) hg hgc hgΩ).integrableOn (s := Omega)
    exact (h'int.neg.add (hi'.const_mul (c s j))).congr
      (Filter.Eventually.of_forall fun x => by
        simp only [pressureUTensor, Pi.neg_apply, Pi.add_apply, Pi.mul_apply]
        ring)
  have hpScalar {g : Vec3 → ℝ} (hg : Continuous g)
      (hgc : HasCompactSupport g) (hgΩ : tsupport g ⊆ Omega) : IntegrableOn
      (fun x => p (x, s) * g x) Omega volume := by
    exact (CKN.Foundation.Measure.integrable_mul_of_tsupport_subset hp hg hgc hgΩ).integrableOn
  have hsource {g : Vec3 → ℝ} (hg : IntegrableOn g Omega volume)
      (hgs : tsupport g ⊆ Omega) : Integrable g volume :=
    decomposition_full_of_on_sws hg hgs
  have hηd (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv η i) :=
    contDiff_spatialDeriv_smooth hη i
  have hηd' (i : Fin 3) : HasCompactSupport (spatialDeriv η i) :=
    hηc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hηm (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (mixedSecond η i j) := by
    exact contDiff_mixedSecond_smooth hη i j
  have hηm' (i j : Fin 3) : HasCompactSupport (mixedSecond η i j) := by
    exact (hηd' j).fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hηdΩ (i : Fin 3) : tsupport (spatialDeriv η i) ⊆ Omega :=
    (tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hEtaSup
  have hηmΩ (i j : Fin 3) : tsupport (mixedSecond η i j) ⊆ Omega :=
    (tsupport_fderiv_apply_subset ℝ (basisVec i)).trans
      ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hEtaSup)
  have hηLapc : HasCompactSupport (spatialLaplacian η) :=
    decomposition_laplacian_hasCompactSupport_sws hηc
  have hηLapΩ : tsupport (spatialLaplacian η) ⊆ Omega := by
    change tsupport (fun x => ∑ i : Fin 3,
      spatialDeriv (spatialDeriv η i) i x) ⊆ Omega
    apply decomposition_ts_support_sum₃_sws
    intro i
    exact (tsupport_fderiv_apply_subset ℝ (basisVec i)).trans
      ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hEtaSup)
  have hP2Int (i j : Fin 3) : Integrable
      (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) volume := by
    exact hsource
      ((hUScalar (i := i) (j := j) (hηm i j).continuous (hηm' i j) (hηmΩ i j)).congr
        (Filter.Eventually.of_forall fun y => by ring))
      ((tsupport_mul_subset_left (f := mixedSecond η i j)
        (g := fun y => pressureUTensor u c (y, s) i j)).trans (hηmΩ i j))
  have hP3Int (i j : Fin 3) : Integrable
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) volume := by
    apply hsource
    · exact hUScalar (i := i) (j := j) (hηd i).continuous (hηd' i) (hηdΩ i)
    · exact (tsupport_mul_subset_right
        (f := fun y => pressureUTensor u c (y, s) i j)
        (g := spatialDeriv η i)).trans (hηdΩ i)
  have hP4Int (i j : Fin 3) : Integrable
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) volume := by
    apply hsource
    · exact hUScalar (i := i) (j := j) (hηd j).continuous (hηd' j) (hηdΩ j)
    · exact (tsupport_mul_subset_right
        (f := fun y => pressureUTensor u c (y, s) i j)
        (g := spatialDeriv η j)).trans (hηdΩ j)
  have hP5Int : Integrable
      (fun y => p (y, s) * spatialLaplacian η y) volume := by
    apply hsource
    · exact hpScalar (contDiff_spatialLaplacian_smooth hη).continuous
        hηLapc hηLapΩ
    · exact (tsupport_mul_subset_right (f := fun y => p (y, s))
        (g := spatialLaplacian η)).trans hηLapΩ
  have hP6Int (j : Fin 3) : Integrable
      (fun y => spatialDeriv η j y * p (y, s)) volume := by
    apply hsource
    · exact (hpScalar (hηd j).continuous (hηd' j) (hηdΩ j)).congr
        (Filter.Eventually.of_forall fun y => by ring)
    · exact (tsupport_mul_subset_left (f := spatialDeriv η j)
        (g := fun y => p (y, s))).trans (hηdΩ j)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hP2Int
  · exact fun i j => (hηm' i j).mul_right
      (f' := fun y => pressureUTensor u c (y, s) i j)
  · intro i j y hy
    rw [hηm0 i j y hy, zero_mul]
  · exact hP3Int
  · exact fun i j => (hηd' i).mul_left
      (f := fun y => pressureUTensor u c (y, s) i j)
  · intro i j y hy
    rw [hηd0 i y hy, mul_zero]
  · exact hP4Int
  · exact fun i j => (hηd' j).mul_left
      (f := fun y => pressureUTensor u c (y, s) i j)
  · intro i j y hy
    rw [hηd0 j y hy, mul_zero]
  · exact hP5Int
  · exact hηLapc.mul_left (f := fun y => p (y, s))
  · intro y hy
    rw [hηLap0 y hy, mul_zero]
  · exact hP6Int
  · exact fun j => (hηd' j).mul_right (f' := fun y => p (y, s))
  · intro j y hy
    rw [hηd0 j y hy, zero_mul]

end CKN
