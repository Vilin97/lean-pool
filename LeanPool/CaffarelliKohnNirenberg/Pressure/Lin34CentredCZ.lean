/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionUnconditional
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34CentredSource
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34SliceIntegrated

/-!
# Lin34 Centred CZ

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

open CKN.Foundation.Euclidean

/-!
# The Calderón--Zygmund bound for the centred first pressure potential

The oscillation estimate `prop:lin34` of `paper/ckn.tex` consumes the external
input `ext:CZ` in the shape

`‖p₁(·, s)‖_{L^{3/2}(ℝ³)} ≤ C₁₁ · (∫_{B_ρ} |u - ⨍u|³)^{2/3}`,

where `p₁` is the leading potential of `prop:pressure-decomposition` run with
the doubly centred nonlinearity `eq:Uhat`.  This file derives that display from
the unconditional singular-integral estimate for the indexed second-order Riesz
extension, the source estimate for the cut-off centred tensor, and the
distributional identification data for the centred potential.
-/

/-- The Calderón--Zygmund constant `C₁₁` of `ext:CZ` produced here: nine times
the component constant of the indexed second-order extension, the factor nine
coming from summing the nine entries of the tensor source. -/
def lin34CZConstant : ℝ := 9 * czP1OperatorConstant

theorem lin34CZConstant_nonneg : 0 ≤ lin34CZConstant := by
  have h : 0 ≤ czP1OperatorConstant := by
    unfold czP1OperatorConstant czP1Constant
    exact ENNReal.toReal_nonneg
  unfold lin34CZConstant
  linarith only [h]

private lemma lin34Centred_rpow_twenty_seven {V : ℝ} (hV : 0 ≤ V) :
    (27 * V) ^ (2 / 3 : ℝ) = 9 * V ^ (2 / 3 : ℝ) := by
  have h27 : ((27 : ℝ)) ^ (2 / 3 : ℝ) = 9 := by
    have hbase : (27 : ℝ) = (3 : ℝ) ^ (3 : ℕ) := by norm_num
    rw [hbase, ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rw [Real.mul_rpow (by norm_num) hV, h27]

private lemma lin34Centred_euclideanBall_eq_ball {x₀ : Vec3} {r : ℝ}
    (hr : 0 < r) : euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  change x ∈ euclideanBall x₀ r ↔ vec3EuclideanNorm (x - x₀) < r
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
    (mem_euclideanBall_iff_vecEuclideanNorm_lt hr)

/-- **`ext:CZ` for the centred potential on one time slice.**  Given the
distributional identification data for the centred first potential and the
linear-growth control of its residual against the indexed extension, the
`L^{3/2}` norm of `p₁` is controlled by the `L³` oscillation of the velocity on
`B_ρ`, with the explicit constant `lin34CZConstant`. -/
theorem lin34_hCZ_p1_slice_of_identification
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) {s : ℝ}
    (hu : AEStronglyMeasurable (fun y : Vec3 => u (y, s))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hv : IntegrableOn
      (fun y => vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (3 : ℕ))
      (euclideanBall x₀ ρ) volume)
    (hP1 : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      Integrable (fun x => lin34CentredP1 u p f x₀ ρ hρ s x *
        spatialLaplacian ψ x) volume →
      ∫ x, lin34CentredP1 u p f x₀ ρ hρ s x * spatialLaplacian ψ x =
        pressureSecondPairing (lin34CentredSource u x₀ hρ s) ψ)
    (hP1Int : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      Integrable (fun x => lin34CentredP1 u p f x₀ ρ hρ s x *
        spatialLaplacian ψ x) volume)
    (hresidual : ∃ C : ℝ, 0 ≤ C ∧
      (∀ R : ℝ, 0 < R →
        MemLp (fun x => lin34CentredP1 u p f x₀ ρ hρ s x -
          pressureSecondExtensionOperator rieszSecondL2Input
            rieszSecondL2_weak_type (lin34CentredSource u x₀ hρ s) x)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) R))) ∧
      (∀ R : ℝ, 0 < R →
        lpNorm (fun x => lin34CentredP1 u p f x₀ ρ hρ s x -
          pressureSecondExtensionOperator rieszSecondL2Input
            rieszSecondL2_weak_type (lin34CentredSource u x₀ hρ s) x)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) R)) ≤ C * (1 + R))) :
    MemLp (lin34CentredP1 u p f x₀ ρ hρ s)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
      lpNorm (lin34CentredP1 u p f x₀ ρ hρ s)
          (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
        lin34CZConstant *
          (∫ y in vec3Ball x₀ ρ,
            vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (3 : ℕ)) ^
              (2 / 3 : ℝ) := by
  obtain ⟨C, hC, hmem, hgrowth⟩ := hresidual
  set V : ℝ := ∫ y in euclideanBall x₀ ρ,
    vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (3 : ℕ) with hVdef
  have hV0 : 0 ≤ V := by
    rw [hVdef]
    exact integral_nonneg (fun y => pow_nonneg (vec3EuclideanNorm_nonneg _) 3)
  have hG : ∀ i j, MemLp (lin34CentredSource u x₀ hρ s i j)
      (ENNReal.ofReal ((3 : ℝ) / 2)) volume :=
    fun i j => (lin34CentredSource_memLp_and_lpNorm_le hρ hu hv i j).1
  have hGc : ∀ i j, HasCompactSupport (lin34CentredSource u x₀ hρ s i j) :=
    fun i j => lin34CentredSource_hasCompactSupport u x₀ hρ s i j
  have hsum := lin34CentredSource_sum_lpNorm_le hρ hu hv
  have hsource : (∑ i, ∑ j, lpNorm (lin34CentredSource u x₀ hρ s i j)
      (ENNReal.ofReal ((3 : ℝ) / 2)) volume) ≤ (27 * V) ^ (2 / 3 : ℝ) := by
    rw [lin34Centred_rpow_twenty_seven hV0]
    exact hsum
  have hE : (0 : ℝ) ≤ 27 * V := by linarith only [hV0]
  have hcz : 0 ≤ czP1OperatorConstant := by
    unfold czP1OperatorConstant czP1Constant
    exact ENNReal.toReal_nonneg
  have hbound := hCZ_p1_unconditional czP1OperatorConstant czP1OperatorConstant
    (27 * V) C hcz le_rfl le_rfl hE hC
    (p₁ := lin34CentredP1 u p f x₀ ρ hρ s)
    (G := lin34CentredSource u x₀ hρ s) hG hGc hsource hP1 hP1Int hmem hgrowth
  have hident := pressureP1_hident_of_pressureSecondExtension_unconditional
    hC hG hP1 hP1Int hmem hgrowth
  have hTmem := pressureSecondExtension_memLp rieszSecondL2Input
    rieszSecondL2_weak_type hG
  refine ⟨hTmem.ae_eq hident.symm, ?_⟩
  have hball : (∫ y in vec3Ball x₀ ρ,
      vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (3 : ℕ)) = V := by
    rw [hVdef, lin34Centred_euclideanBall_eq_ball hρ]
  rw [hball]
  calc
    lpNorm (lin34CentredP1 u p f x₀ ρ hρ s)
        (ENNReal.ofReal ((3 : ℝ) / 2)) volume ≤
        czP1OperatorConstant * (27 * V) ^ (2 / 3 : ℝ) := hbound
    _ = lin34CZConstant * V ^ (2 / 3 : ℝ) := by
      rw [lin34Centred_rpow_twenty_seven hV0]
      unfold lin34CZConstant
      ring

/-- **`ext:CZ` at solution level.**  For a suitable weak solution and almost
every time of the cylinder `Q_ρ(z₀)`, the centred first potential of
`prop:pressure-decomposition` is globally `L^{3/2}` with norm controlled by the
velocity oscillation `eq:Chat`.  This is exactly the hypothesis `hCZ_p1` that
`pressure_lin34_force_lambda_of_sws` consumes, with `C₁₁ = lin34CZConstant`.
The named inputs are the distributional identification data for the centred
potential and the linear growth of its residual. -/
theorem lin34_hCZ_p1_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hP1 : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        Integrable (fun x => lin34CentredP1 u p f z.1 ρ hρ s x *
          spatialLaplacian ψ x) volume →
        ∫ x, lin34CentredP1 u p f z.1 ρ hρ s x * spatialLaplacian ψ x =
          pressureSecondPairing (lin34CentredSource u z.1 hρ s) ψ)
    (hP1Int : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        Integrable (fun x => lin34CentredP1 u p f z.1 ρ hρ s x *
          spatialLaplacian ψ x) volume)
    (hresidual : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2), ∃ C : ℝ, 0 ≤ C ∧
      (∀ R : ℝ, 0 < R →
        MemLp (fun x => lin34CentredP1 u p f z.1 ρ hρ s x -
          pressureSecondExtensionOperator rieszSecondL2Input
            rieszSecondL2_weak_type (lin34CentredSource u z.1 hρ s) x)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) R))) ∧
      (∀ R : ℝ, 0 < R →
        lpNorm (fun x => lin34CentredP1 u p f z.1 ρ hρ s x -
          pressureSecondExtensionOperator rieszSecondL2Input
            rieszSecondL2_weak_type (lin34CentredSource u z.1 hρ s) x)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) R)) ≤ C * (1 + R))) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (lin34CentredP1 u p f z.1 ρ hρ s)
          (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
        lpNorm (lin34CentredP1 u p f z.1 ρ hρ s)
            (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
          lin34CZConstant * lin34VelocitySlice u z ρ s ^ (2 / 3 : ℝ) := by
  obtain ⟨Ω', J, hbox, hball, htime⟩ := pressure_box_geometry hsol hρ hsub
  have hslices := ae_restrict_of_ae_restrict_of_subset htime
    (slice_memLp_ae_of_sws hsol hbox)
  have hVae := lin34_slice_integrableOn_ball_ae
    (lin34_integrableOn_meanFree_cube (u := u) (x := z.1) (t := z.2) (r := ρ)
      hρ (tsai_integrable_velocity_on_cylinder hsol hρ hsub)
      (tsai_integrable_velocity_cube_on_cylinder hsol hρ hsub))
  filter_upwards [hslices, hVae, hP1, hP1Int, hresidual] with s hus hVs hsP1
    hsP1Int hsRes
  have hu : MemLp (fun y : Vec3 => u (y, s)) 2
      (volume.restrict (vec3Ball z.1 ρ)) :=
    hus.1.mono_measure (Measure.restrict_mono_set volume hball)
  have hv : IntegrableOn
      (fun y => vec3EuclideanNorm (meanFreeVec u z.1 ρ s y) ^ (3 : ℕ))
      (euclideanBall z.1 ρ) volume := by
    rw [lin34Centred_euclideanBall_eq_ball hρ]
    exact hVs
  exact lin34_hCZ_p1_slice_of_identification hρ hu.aestronglyMeasurable hv
    hsP1 hsP1Int hsRes

end CKN
