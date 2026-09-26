/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionPairingCylinder
public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationWholeSpace
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PotentialDecayPotentials
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PotentialDecayGrowthSum
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.PotentialLocalLp
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.PotentialLocalLpMeasure
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.PotentialLocalLpExponents
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientPotential

/-! # The first-order identification of the slice first pressure potential

The local decomposition `eq:pk` writes the first pressure term as the double
Riesz transform `p₁ = -R_iR_j(η U_{ij})`, a second-order object.  Display (3.5)
of the pressure-gradient section instead needs the first-order form.  In the
Lean convention
`pressureNewtonianDerivativePotential i g = −(∂ᵢN * g)`, the divergence-form
source is
`Vᵢ = −∂ⱼ(η Uᵢⱼ) = +∂ⱼ(η uᵢ(uⱼ − ⟨uⱼ⟩))`.

Both sides pair with `Δψ` against the same second-order source `η U_{ij}`: the
left by the distributional identity of the pressure decomposition, the right by
the adjoint of the first-order Newtonian derivative potential using the
displayed divergence-form source.  Their difference is therefore weakly
harmonic on `ℝ³`, and the whole-space Liouville theorem with local `L^{3/2}`
linear growth identifies them almost everywhere.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat
open CKN.Foundation.Euclidean

noncomputable section

namespace CKN.Core.Step4

private theorem hasCompactSupport_spatialLaplacian_ident {ψ : Vec3 → ℝ}
    (hψc : HasCompactSupport ψ) : HasCompactSupport (spatialLaplacian ψ) := by
  have hdiag (i : Fin 3) :
      HasCompactSupport (spatialDeriv (spatialDeriv ψ i) i) :=
    (hψc.fderiv_apply (𝕜 := ℝ) (basisVec i)).fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hsum : HasCompactSupport (fun y : Vec3 =>
      spatialDeriv (spatialDeriv ψ (0 : Fin 3)) 0 y +
        spatialDeriv (spatialDeriv ψ (1 : Fin 3)) 1 y +
        spatialDeriv (spatialDeriv ψ (2 : Fin 3)) 2 y) := by
    have h01 : HasCompactSupport (fun y : Vec3 =>
        spatialDeriv (spatialDeriv ψ (0 : Fin 3)) 0 y +
          spatialDeriv (spatialDeriv ψ (1 : Fin 3)) 1 y) := by
      convert (hdiag (0 : Fin 3)).add (hdiag (1 : Fin 3)) using 1
    convert h01.add (hdiag (2 : Fin 3)) using 1
  have heq : spatialLaplacian ψ = fun y : Vec3 =>
      spatialDeriv (spatialDeriv ψ (0 : Fin 3)) 0 y +
        spatialDeriv (spatialDeriv ψ (1 : Fin 3)) 1 y +
        spatialDeriv (spatialDeriv ψ (2 : Fin 3)) 2 y := by
    funext y
    simp only [spatialLaplacian, Fin.sum_univ_three]
  rw [heq]
  exact hsum

/-- The coordinate sum of first-order Newtonian derivative potentials of an
integrable compactly supported source is integrable against the Laplacian of a
test function. -/
theorem newtonianDerivativeSum_laplacian_integrable
    {V : Vec3 → Vec3}
    (hVint : ∀ i : Fin 3, Integrable (fun x => V x i) volume)
    (hVc : ∀ i : Fin 3, HasCompactSupport (fun x => V x i))
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun x =>
      (∑ i, pressureNewtonianDerivativePotential i (fun y => V y i) x) *
        spatialLaplacian ψ x) volume := by
  classical
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (spatialLaplacian ψ) :=
    contDiff_spatialLaplacian_smooth hψ
  have hφc : HasCompactSupport (spatialLaplacian ψ) :=
    hasCompactSupport_spatialLaplacian_ident hψc
  have hterm : ∀ i : Fin 3, Integrable (fun x =>
      pressureNewtonianDerivativePotential i (fun y => V y i) x *
        spatialLaplacian ψ x) volume := fun i =>
    pressureNewtonianDerivativePotential_mul_smooth_integrable
      (hVint i) (hVc i) hφ hφc
  have hsum := integrable_finsetSum (Finset.univ : Finset (Fin 3))
    (μ := volume)
    (f := fun i x => pressureNewtonianDerivativePotential i
      (fun y => V y i) x * spatialLaplacian ψ x)
    (fun i _ => hterm i)
  refine hsum.congr (Eventually.of_forall fun x => ?_)
  simp only [Finset.sum_mul]

/-- The Laplacian pairing of the coordinate sum of first-order Newtonian
derivative potentials is the divergence pairing of its source. -/
theorem newtonianDerivativeSum_laplacian_pairing
    {V : Vec3 → Vec3}
    (hVint : ∀ i : Fin 3, Integrable (fun x => V x i) volume)
    (hVc : ∀ i : Fin 3, HasCompactSupport (fun x => V x i))
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    (∫ x, (∑ i, pressureNewtonianDerivativePotential i (fun y => V y i) x) *
        spatialLaplacian ψ x) =
      ∑ i : Fin 3, ∫ x, V x i * spatialDeriv ψ i x := by
  classical
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (spatialLaplacian ψ) :=
    contDiff_spatialLaplacian_smooth hψ
  have hφc : HasCompactSupport (spatialLaplacian ψ) :=
    hasCompactSupport_spatialLaplacian_ident hψc
  have hterm : ∀ i : Fin 3, Integrable (fun x =>
      pressureNewtonianDerivativePotential i (fun y => V y i) x *
        spatialLaplacian ψ x) volume := fun i =>
    pressureNewtonianDerivativePotential_mul_smooth_integrable
      (hVint i) (hVc i) hφ hφc
  have hsplit : (∫ x, (∑ i, pressureNewtonianDerivativePotential i
      (fun y => V y i) x) * spatialLaplacian ψ x) =
      ∫ x, ∑ i : Fin 3, pressureNewtonianDerivativePotential i
        (fun y => V y i) x * spatialLaplacian ψ x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Finset.sum_mul]
  rw [hsplit, integral_finsetSum (Finset.univ : Finset (Fin 3))
    (fun i _ => hterm i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact pressureNewtonianDerivativePotential_distributional_pairing_smooth
    (hVint i) (hVc i) hψ hψc

/-- The first-order identification of `p₁`.  Both `p₁` and the coordinate sum
of the first-order Newtonian derivative potentials of `V` pair with `Δψ`
against the same second-order source `G`, and their difference has local
`L^{3/2}` linear growth; the whole-space Liouville theorem identifies them. -/
theorem pressureP1_eq_newtonianDerivativeSum_of_pairings
    {p₁ : Vec3 → ℝ} {V : Vec3 → Vec3} {G : Fin 3 → Fin 3 → Vec3 → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hVint : ∀ i : Fin 3, Integrable (fun x => V x i) volume)
    (hVc : ∀ i : Fin 3, HasCompactSupport (fun x => V x i))
    (hVpair : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∑ i : Fin 3, ∫ x, V x i * spatialDeriv ψ i x) =
        pressureSecondPairing G ψ)
    (hP1 : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      Integrable (fun x => p₁ x * spatialLaplacian ψ x) volume →
      ∫ x, p₁ x * spatialLaplacian ψ x = pressureSecondPairing G ψ)
    (hP1Int : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      Integrable (fun x => p₁ x * spatialLaplacian ψ x) volume)
    (hmem : ∀ r : ℝ, 0 < r →
      MemLp (fun x => p₁ x -
          ∑ i, pressureNewtonianDerivativePotential i (fun y => V y i) x)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) r)))
    (hgrowth : ∀ r : ℝ, 0 < r →
      lpNorm (fun x => p₁ x -
          ∑ i, pressureNewtonianDerivativePotential i (fun y => V y i) x)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) r)) ≤ C * (1 + r)) :
    p₁ =ᵐ[volume]
      fun x => ∑ i, pressureNewtonianDerivativePotential i (fun y => V y i) x :=
  pressureP1_eq_of_wholeSpace_identity_and_linear_growth hC hP1
    (fun ψ hψ hψc _ => by
      rw [newtonianDerivativeSum_laplacian_pairing hVint hVc hψ hψc]
      exact hVpair ψ hψ hψc)
    hP1Int
    (fun ψ hψ hψc =>
      newtonianDerivativeSum_laplacian_integrable hVint hVc hψ hψc)
    hmem hgrowth

/-- Display (3.5) needs the identification on almost every slice of a suitable
weak solution.  The pressure side of the pairing is unconditional; the two
named inputs are the divergence-form characterization of the slice source `V`
and the local `L^{3/2}` linear growth of the residual. -/
theorem slice_selected_gradient_hident_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    {V : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hVdata : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      (∀ i : Fin 3, Integrable (fun x => V (x, s) i) volume) ∧
      (∀ i : Fin 3, HasCompactSupport (fun x => V (x, s) i)))
    (hVpair : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        (∑ i : Fin 3, ∫ x, V (x, s) i * spatialDeriv ψ i x) =
          pressureSecondPairing
            (fun i j x => mollifiedBallCutoff z.1 hρ x *
              pressureUTensor u (fun t j => average
                (volume.restrict (vec3Ball z.1 ρ))
                (fun y : Vec3 => u (y, t) j)) (x, s) i j) ψ)
    (hgrow : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2), ∃ C : ℝ, 0 ≤ C ∧
      (∀ r : ℝ, 0 < r →
        MemLp (fun x => pressureP1 (mollifiedBallCutoff z.1 hρ) u
            (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
              (fun y : Vec3 => u (y, t) j)) p f s x -
            ∑ i, pressureNewtonianDerivativePotential i
              (fun y => V (y, s) i) x)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) r))) ∧
      (∀ r : ℝ, 0 < r →
        lpNorm (fun x => pressureP1 (mollifiedBallCutoff z.1 hρ) u
            (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
              (fun y : Vec3 => u (y, t) j)) p f s x -
            ∑ i, pressureNewtonianDerivativePotential i
              (fun y => V (y, s) i) x)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) r)) ≤ C * (1 + r))) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      pressureP1 (mollifiedBallCutoff z.1 hρ) u
          (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
            (fun y : Vec3 => u (y, t) j)) p f s =ᵐ[
        volume.restrict (euclideanBall z.1 (ρ / 2))]
        fun x => ∑ i, pressureNewtonianDerivativePotential i
          (fun y => V (y, s) i) x := by
  have hdata := pressureP1_cz_identification_data_ae_of_sws_cylinder hsol hρ hsub
  filter_upwards [hdata, hVdata, hVpair, hgrow] with s hs hVs hVp hgs
  obtain ⟨C, hC, hmem, hgrowth⟩ := hgs
  exact ae_restrict_of_ae
    (pressureP1_eq_newtonianDerivativeSum_of_pairings (V := fun x => V (x, s))
      hC hVs.1 hVs.2 hVp hs.1 hs.2 hmem hgrowth)

/-! ### The local growth of the first-order potential

The whole-space Liouville step needs the residual `p₁ - ∑ᵢ ∂ᵢN * Vᵢ` to have
local `L^{3/2}` norms growing at most linearly in the radius.  The pressure
side of that residual is the global `L^{3/2}` bound of `p₁` supplied by the
Calderón–Zygmund selection; the potential side is the inverse-square far-field
decay of the first-order Newtonian derivative potential. -/

/-- The first-derivative Newtonian potential of a compactly supported `L^{6/5}`
datum is `L^{3/2}` on every ball about the origin, with local norms growing at
most linearly in the radius. -/
theorem pressureNewtonianDerivativePotential_local_growth_of_memLp_sixFifths
    (i : Fin 3) {G : Vec3 → ℝ}
    (hG : MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hGc : HasCompactSupport G) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ r : ℝ, 0 < r → MemLp (pressureNewtonianDerivativePotential i G)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) r))) ∧
      (∀ r : ℝ, 0 < r → lpNorm (pressureNewtonianDerivativePotential i G)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) r)) ≤ C * (1 + r)) := by
  obtain ⟨r, hr⟩ := hGc.isCompact.isBounded.subset_closedBall (0 : Vec3)
  obtain ⟨R, hR, hsub⟩ : ∃ R : ℝ, 0 < R ∧ tsupport G ⊆ closedBall (0 : Vec3) R :=
    ⟨max r 1, lt_of_lt_of_le zero_lt_one (le_max_right r 1),
      hr.trans (closedBall_subset_closedBall (le_max_left r 1))⟩
  have hGzero : ∀ y, y ∉ closedBall (0 : Vec3) R → G y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun hy' => hy (hsub hy')
  obtain ⟨G', hG'meas, hGG', hG'zero⟩ :=
    exists_measurable_representative_of_support_closedBall
      hG.aestronglyMeasurable hGzero
  have hpot : pressureNewtonianDerivativePotential i G =
      pressureNewtonianDerivativePotential i G' :=
    pressureNewtonianDerivativePotential_congr_of_ae_eq i hGG'
  have hG' : MemLp G' (ENNReal.ofReal (6 / 5 : ℝ)) volume := hG.ae_eq hGG'
  have hint : Integrable G' volume :=
    integrable_of_memLp_ofReal_of_support (by norm_num) hG' hG'zero
  have hsupp' : tsupport G' ⊆ closedBall (0 : Vec3) R := by
    have hsup : Function.support G' ⊆ closedBall (0 : Vec3) R := by
      intro y hy
      by_contra hy'
      exact hy (hG'zero y hy')
    exact closure_minimal hsup isClosed_closedBall
  have hmeas : AEStronglyMeasurable
      (pressureNewtonianDerivativePotential i G') volume :=
    aestronglyMeasurable_pressureNewtonianDerivativePotential i hG'meas
  have hrpos : 0 < 2 * (2 * R + 2 * ‖(0 : Vec3)‖) := by
    rw [norm_zero]
    linarith only [hR]
  have hnear : MemLp (pressureNewtonianDerivativePotential i G')
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (ball (0 : Vec3) (2 * (2 * R + 2 * ‖(0 : Vec3)‖)))) :=
    pressureNewtonianDerivativePotential_memLp_ball i hR hrpos hG'meas hG' hG'zero
  have hmain := memLp_and_lpNorm_linear_growth_pressureNewtonianDerivativePotential
    hint hR hsupp' i hmeas hnear
  refine ⟨invNormGrowthConstant (pressureNewtonianDerivativePotential i G')
      (2 * (4 * (4 * Real.pi)⁻¹ * (∫ y, |G' y|) / (2 * R)))
      (2 * R + 2 * ‖(0 : Vec3)‖), ?_, ?_, ?_⟩
  · refine invNormGrowthConstant_nonneg ?_
    have hmass : (0 : ℝ) ≤ ∫ y, |G' y| := integral_nonneg fun y => abs_nonneg (G' y)
    have h2R : (0 : ℝ) < 2 * R := by linarith only [hR]
    have hA : (0 : ℝ) ≤ 4 * (4 * Real.pi)⁻¹ * ∫ y, |G' y| :=
      mul_nonneg (by positivity) hmass
    have hdiv : (0 : ℝ) ≤ 4 * (4 * Real.pi)⁻¹ * (∫ y, |G' y|) / (2 * R) :=
      div_nonneg hA h2R.le
    linarith only [hdiv]
  · rw [hpot]
    exact hmain.1
  · rw [hpot]
    exact hmain.2

/-- The coordinate sum of first-order Newtonian derivative potentials of a
compactly supported `L^{6/5}` source has local `L^{3/2}` linear growth. -/
theorem newtonianDerivativeSum_local_growth_of_memLp_sixFifths
    {V : Vec3 → Vec3}
    (hV : ∀ i : Fin 3, MemLp (fun x => V x i)
      (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hVc : ∀ i : Fin 3, HasCompactSupport (fun x => V x i)) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ r : ℝ, 0 < r → MemLp
        (fun x => ∑ i, pressureNewtonianDerivativePotential i
          (fun y => V y i) x)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) r))) ∧
      (∀ r : ℝ, 0 < r → lpNorm
        (fun x => ∑ i, pressureNewtonianDerivativePotential i
          (fun y => V y i) x)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) r)) ≤ C * (1 + r)) := by
  classical
  choose C hC hmem hgrow using fun i : Fin 3 =>
    pressureNewtonianDerivativePotential_local_growth_of_memLp_sixFifths i
      (hV i) (hVc i)
  set F : Fin 3 → Vec3 → ℝ := fun i =>
    pressureNewtonianDerivativePotential i (fun y => V y i) with hF
  have heq : (∑ i ∈ (Finset.univ : Finset (Fin 3)), F i) =
      fun x => ∑ i, pressureNewtonianDerivativePotential i
        (fun y => V y i) x := by
    funext x
    simp only [Finset.sum_apply, hF]
  refine ⟨∑ i : Fin 3, C i, Finset.sum_nonneg fun i _ => hC i, ?_, ?_⟩
  · intro r hr
    have := memLp_euclideanBall_family_sum (s := (Finset.univ : Finset (Fin 3)))
      (f := F) (fun i _ => hmem i) r hr
    rwa [heq] at this
  · intro r hr
    have := lpNorm_euclideanBall_growth_sum (s := (Finset.univ : Finset (Fin 3)))
      (f := F) (C := C) (fun i _ => hmem i) (fun i _ => hgrow i) hr
    rwa [heq] at this

/-- The identification residual has local `L^{3/2}` linear growth once the
first pressure potential is globally `L^{3/2}` and the source is a compactly
supported `L^{6/5}` field. -/
theorem pressureP1_residual_local_growth_of_source
    {p₁ : Vec3 → ℝ} {V : Vec3 → Vec3}
    (hp₁ : MemLp p₁ (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hV : ∀ i : Fin 3, MemLp (fun x => V x i)
      (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hVc : ∀ i : Fin 3, HasCompactSupport (fun x => V x i)) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ r : ℝ, 0 < r →
        MemLp (fun x => p₁ x -
            ∑ i, pressureNewtonianDerivativePotential i (fun y => V y i) x)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) r))) ∧
      (∀ r : ℝ, 0 < r →
        lpNorm (fun x => p₁ x -
            ∑ i, pressureNewtonianDerivativePotential i (fun y => V y i) x)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) r)) ≤ C * (1 + r)) := by
  obtain ⟨Cs, hCs, hmemS, hgrowS⟩ :=
    newtonianDerivativeSum_local_growth_of_memLp_sixFifths hV hVc
  have hmemP : ∀ r : ℝ, 0 < r → MemLp p₁ (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) r)) :=
    fun r _ => memLp_euclideanBall_of_memLp_volume hp₁ r
  have hgrowP : ∀ r : ℝ, 0 < r → lpNorm p₁ (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) r)) ≤
      lpNorm p₁ (ENNReal.ofReal (3 / 2 : ℝ)) volume * (1 + r) :=
    fun r hr => lpNorm_euclideanBall_le_of_memLp_volume hp₁ hr
  refine ⟨lpNorm p₁ (ENNReal.ofReal (3 / 2 : ℝ)) volume + Cs,
    add_nonneg lpNorm_nonneg hCs, ?_, ?_⟩
  · intro r hr
    exact memLp_euclideanBall_family_sub hmemP hmemS r hr
  · intro r hr
    exact lpNorm_euclideanBall_growth_sub hmemP hgrowP hgrowS hr

/-- Display (3.5) needs the identification on almost every slice of a suitable
weak solution.  The pressure side of the pairing and the growth of the residual
are unconditional given the Calderón–Zygmund slice bound; the single named
input is the divergence-form characterization of the slice source `V`. -/
theorem slice_selected_gradient_hident_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    {V : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hp₁ : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (pressureP1 (mollifiedBallCutoff z.1 hρ) u
        (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
          (fun y : Vec3 => u (y, t) j)) p f s)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hV : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      (∀ i : Fin 3, MemLp (fun x => V (x, s) i)
        (ENNReal.ofReal (6 / 5 : ℝ)) volume) ∧
      (∀ i : Fin 3, HasCompactSupport (fun x => V (x, s) i)))
    (hVpair : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        (∑ i : Fin 3, ∫ x, V (x, s) i * spatialDeriv ψ i x) =
          pressureSecondPairing
            (fun i j x => mollifiedBallCutoff z.1 hρ x *
              pressureUTensor u (fun t j => average
                (volume.restrict (vec3Ball z.1 ρ))
                (fun y : Vec3 => u (y, t) j)) (x, s) i j) ψ) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      pressureP1 (mollifiedBallCutoff z.1 hρ) u
          (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
            (fun y : Vec3 => u (y, t) j)) p f s =ᵐ[
        volume.restrict (euclideanBall z.1 (ρ / 2))]
        fun x => ∑ i, pressureNewtonianDerivativePotential i
          (fun y => V (y, s) i) x := by
  have hVdata : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      (∀ i : Fin 3, Integrable (fun x => V (x, s) i) volume) ∧
      (∀ i : Fin 3, HasCompactSupport (fun x => V (x, s) i)) := by
    filter_upwards [hV] with s hs
    exact ⟨fun i => memLp_six_fifths_integrable_of_hasCompactSupport
      (hs.1 i) (hs.2 i), hs.2⟩
  have hgrow : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2), ∃ C : ℝ, 0 ≤ C ∧
      (∀ r : ℝ, 0 < r →
        MemLp (fun x => pressureP1 (mollifiedBallCutoff z.1 hρ) u
            (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
              (fun y : Vec3 => u (y, t) j)) p f s x -
            ∑ i, pressureNewtonianDerivativePotential i
              (fun y => V (y, s) i) x)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) r))) ∧
      (∀ r : ℝ, 0 < r →
        lpNorm (fun x => pressureP1 (mollifiedBallCutoff z.1 hρ) u
            (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
              (fun y : Vec3 => u (y, t) j)) p f s x -
            ∑ i, pressureNewtonianDerivativePotential i
              (fun y => V (y, s) i) x)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) r)) ≤ C * (1 + r)) := by
    filter_upwards [hp₁, hV] with s hps hVs
    exact pressureP1_residual_local_growth_of_source (V := fun x => V (x, s))
      hps hVs.1 hVs.2
  exact slice_selected_gradient_hident_of_sws hsol hρ hsub hVdata hVpair hgrow

end CKN.Core.Step4
