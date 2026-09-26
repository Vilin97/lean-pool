/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientAssembly
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientScaling
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientForceP8
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientForceSlices
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsUnconditionalConstants

/-! # The force potentials of a slice carry a weak gradient, with no condition on `div f`

The last two summands `p₇ + p₈` of the local pressure decomposition `eq:pk`
are the force potentials.  The class `def:sws` imposes no condition on the
spatial divergence of the force, so display (3.5) of the pressure-gradient
section must carry them: they do not cancel in general.

The first, `p₇ = -∑ⱼ ∂ⱼN * (η fⱼ)`, is a coordinate sum of Newtonian
derivative potentials of the cut-off force, which is exactly the shape the
Calderón–Zygmund selection differentiates, with the `L^{6/5}` bound of that
selection.  The second, `p₈ = -∑ⱼ N * (∂ⱼη fⱼ)`, has its density carried by
the cutoff annulus, hence is `C¹` on the inner ball `B_{ρ/2}(x₀)` with the
far-field gradient bound of `eq:har-Ck` at order one; its classical gradient
there is its weak gradient.  Adding the two produces one slice field, in
`L^{6/5}` of the inner ball with the `ρ^{-1/2}` weight of display (3.5).
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN.Core.Step4

private lemma isOpen_euclideanBall_force (x₀ : Vec3) (r : ℝ) :
    IsOpen (euclideanBall x₀ r) := by
  change IsOpen {x : Vec3 | euclideanSqDist x x₀ < r ^ 2}
  exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const

private lemma euclideanBall_eq_vec3Ball_force {x₀ : Vec3} {r : ℝ} (hr : 0 < r) :
    euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hr, mem_vec3Ball]
  simp only [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]

/-- A weak partial derivative changes sign with its function. -/
theorem hasWeakPartialDerivOn_neg {B : Set Vec3} {k : Fin 3} {w g : Vec3 → ℝ}
    (h : HasWeakPartialDerivOn B k w g) :
    HasWeakPartialDerivOn B k (fun x => -w x) (fun x => -g x) := by
  intro φ hφ hφc hφB
  have hb := h φ hφ hφc hφB
  simp only [neg_mul]
  rw [integral_neg, integral_neg, hb, neg_neg]

/-- The force slot of display (3.5) on one slice, from the data of the two
force densities.  The Calderón–Zygmund selection `hP1` differentiates the first
force potential; the second is differentiated classically on the inner ball,
where it is `C¹` with the gradient bound `M ρ^{-3}`.  The resulting field is the
coordinate weak gradient of `p₇ + p₈` there, and its `L^{6/5}` norm carries the
`ρ^{-1/2}` weight of the display. -/
theorem slice_force_weak_gradient_of_slice_data
    (C_CZ M : ℝ) (hC_CZ : 0 ≤ C_CZ) (hM : 0 ≤ M)
    {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    {f : ParabolicPoint → Vec3} {s : ℝ}
    (hP1 : ∀ (i : Fin 3) (G : Vec3 → ℝ),
      MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume → HasCompactSupport G →
      ∃ D : Vec3 → Vec3,
        MemLp D (ENNReal.ofReal (6 / 5 : ℝ)) volume ∧
        (∀ (j : Fin 3) (ψ : Vec3 → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          (∫ x, pressureNewtonianDerivativePotential i G x * spatialDeriv ψ j x) =
            -(∫ x, D x j * ψ x)) ∧
        eLpNorm D (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
          ENNReal.ofReal C_CZ * eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hmem : ∀ j : Fin 3, MemLp (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * f (y, s) j)
      (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hcs : ∀ j : Fin 3, HasCompactSupport
      (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * f (y, s) j))
    (hp8 : ContDiffOn ℝ (1 : ℕ∞) (pressureP8 (mollifiedBallCutoff x₀ hρ) f s)
      (euclideanBall x₀ (ρ / 2)))
    (hsup : ∀ x ∈ euclideanBall x₀ (ρ / 2),
      vec3EuclideanNorm
        (classicalGradient (pressureP8 (mollifiedBallCutoff x₀ hρ) f s) x) ≤
        M * (ρ ^ 3)⁻¹) :
    ∃ g : Fin 3 → Vec3 → ℝ, ∀ k : Fin 3,
      HasWeakPartialDerivOn (euclideanBall x₀ (ρ / 2)) k
          (pressureP7 (mollifiedBallCutoff x₀ hρ) f s +
            pressureP8 (mollifiedBallCutoff x₀ hρ) f s) (g k) ∧
        LocallyIntegrableOn (g k) (euclideanBall x₀ (ρ / 2)) volume ∧
        eLpNorm (g k) (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict (euclideanBall x₀ (ρ / 2))) ≤
          ENNReal.ofReal (C_CZ * (∑ j : Fin 3,
              lpNorm (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * f (y, s) j)
                (ENNReal.ofReal (6 / 5 : ℝ)) volume) + M * ρ ^ (-1 / 2 : ℝ)) := by
  classical
  set B : Set Vec3 := euclideanBall x₀ (ρ / 2) with hBdef
  have hB : IsOpen B := isOpen_euclideanBall_force x₀ (ρ / 2)
  set V : Vec3 → Vec3 := fun y i => mollifiedBallCutoff x₀ hρ y * f (y, s) i with hVdef
  have hV : ∀ i : Fin 3, MemLp (fun x => V x i) (ENNReal.ofReal (6 / 5 : ℝ)) volume := hmem
  have hVc : ∀ i : Fin 3, HasCompactSupport (fun x => V x i) := hcs
  obtain ⟨Dpot, hDmem, hDpair, hDbound⟩ :=
    newtonian_derivative_sum_weak_gradient_of_extension C_CZ hP1 hV hVc
  have hP7eq : pressureP7 (mollifiedBallCutoff x₀ hρ) f s =
      fun x => -(∑ i, pressureNewtonianDerivativePotential i (fun y => V y i) x) := rfl
  have hweak7 : ∀ k : Fin 3, HasWeakPartialDerivOn B k
      (pressureP7 (mollifiedBallCutoff x₀ hρ) f s) (fun x => -(Dpot x k)) := by
    intro k
    rw [hP7eq]
    exact hasWeakPartialDerivOn_neg
      (CKN.Core.Endgame.weak_partial_deriv_on_of_global_pairing hB
        (fun ψ hψ hψc => hDpair k ψ hψ hψc))
  have hloc7 : LocallyIntegrableOn
      (pressureP7 (mollifiedBallCutoff x₀ hρ) f s) B volume := by
    rw [hP7eq]
    have hsum := newtonianDerivativeSum_locallyIntegrable hV hVc
    exact hsum.neg.locallyIntegrableOn B
  have hloc8 : LocallyIntegrableOn
      (pressureP8 (mollifiedBallCutoff x₀ hρ) f s) B volume :=
    hp8.continuousOn.locallyIntegrableOn hB.measurableSet
  have hlocg7 : ∀ k : Fin 3, LocallyIntegrableOn (fun x => -(Dpot x k)) B volume := by
    intro k
    exact (potentialComponent_locallyIntegrableOn hDmem k B).neg
  have hlocg8 : ∀ k : Fin 3, LocallyIntegrableOn
      (fun x => classicalGradient (pressureP8 (mollifiedBallCutoff x₀ hρ) f s) x k)
      B volume := fun k => locallyIntegrableOn_classicalGradient hB k hp8
  refine ⟨fun k x => -(Dpot x k) +
    classicalGradient (pressureP8 (mollifiedBallCutoff x₀ hρ) f s) x k,
    fun k => ⟨?_, (hlocg7 k).add (hlocg8 k), ?_⟩⟩
  · exact hasWeakPartialDerivOn_add hB (hweak7 k)
      (hasWeakPartialDerivOn_classicalGradient hB k hp8) hloc7 hloc8
      (hlocg7 k) (hlocg8 k)
  · have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (6 / 5 : ℝ) :=
      ENNReal.one_le_ofReal.2 (by norm_num)
    have hsplit := eLpNorm_add_le (f := fun x => -(Dpot x k))
      (g := fun x => classicalGradient
        (pressureP8 (mollifiedBallCutoff x₀ hρ) f s) x k)
      (μ := volume.restrict B) (p := ENNReal.ofReal (6 / 5 : ℝ)) hp
    have hneg : eLpNorm (fun x => -(Dpot x k)) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict B) =
        eLpNorm (fun x => Dpot x k) (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict B) :=
      eLpNorm_neg (fun x => Dpot x k) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict B)
    have hpot : eLpNorm (fun x => Dpot x k) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict B) ≤
        ENNReal.ofReal C_CZ * ∑ i : Fin 3,
          eLpNorm (fun x => V x i) (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
      have hmeas : AEStronglyMeasurable (fun x => Dpot x k) volume :=
        (ContinuousLinearMap.proj (R := ℝ) k).continuous.comp_aestronglyMeasurable
          hDmem.aestronglyMeasurable
      have hcomp : eLpNorm (fun x => Dpot x k) (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
          eLpNorm Dpot (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
        eLpNorm_mono_ae hmeas
          (Eventually.of_forall fun x => norm_le_pi_norm (Dpot x) k)
      exact ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans hcomp).trans hDbound
    have hsum_eq : ENNReal.ofReal C_CZ * ∑ i : Fin 3,
          eLpNorm (fun x => V x i) (ENNReal.ofReal (6 / 5 : ℝ)) volume =
        ENNReal.ofReal (C_CZ * ∑ j : Fin 3,
          lpNorm (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * f (y, s) j)
            (ENNReal.ofReal (6 / 5 : ℝ)) volume) := by
      rw [ENNReal.ofReal_mul hC_CZ,
        ENNReal.ofReal_sum_of_nonneg (fun i _ => lpNorm_nonneg)]
      refine congrArg (fun t => ENNReal.ofReal C_CZ * t) ?_
      exact Finset.sum_congr rfl fun i _ => (ofReal_lpNorm (hmem i)).symm
    have hgrad : eLpNorm (fun x => classicalGradient
          (pressureP8 (mollifiedBallCutoff x₀ hρ) f s) x k)
          (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) ≤
        ENNReal.ofReal (M * ρ ^ (-1 / 2 : ℝ)) := by
      have hmeas : AEStronglyMeasurable (fun x => classicalGradient
          (pressureP8 (mollifiedBallCutoff x₀ hρ) f s) x k)
          (volume.restrict (euclideanBall x₀ (ρ / 2))) :=
        (locallyIntegrableOn_classicalGradient hB k hp8).aestronglyMeasurable
      have h1 := eLpNorm_classicalGradient_component_le_of_sup (x₀ := x₀) (ρ := ρ)
        (M := M * (ρ ^ 3)⁻¹) hρ (mul_nonneg hM (by positivity)) k hmeas hsup
      exact h1.trans (halfBall_volume_rpow_five_sixths_mul_inv_cube_le x₀ hρ hM)
    have hnn1 : 0 ≤ C_CZ * ∑ j : Fin 3,
        lpNorm (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * f (y, s) j)
          (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
      mul_nonneg hC_CZ (Finset.sum_nonneg fun i _ => lpNorm_nonneg)
    have hnn2 : 0 ≤ M * ρ ^ (-1 / 2 : ℝ) := mul_nonneg hM (by positivity)
    calc eLpNorm (fun x => -(Dpot x k) + classicalGradient
            (pressureP8 (mollifiedBallCutoff x₀ hρ) f s) x k)
          (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B)
        ≤ eLpNorm (fun x => -(Dpot x k)) (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict B) +
          eLpNorm (fun x => classicalGradient
            (pressureP8 (mollifiedBallCutoff x₀ hρ) f s) x k)
            (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) := hsplit
      _ ≤ ENNReal.ofReal (C_CZ * ∑ j : Fin 3,
            lpNorm (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * f (y, s) j)
              (ENNReal.ofReal (6 / 5 : ℝ)) volume) +
            ENNReal.ofReal (M * ρ ^ (-1 / 2 : ℝ)) :=
          add_le_add (by rw [hneg]; exact hpot.trans_eq hsum_eq) hgrad
      _ = ENNReal.ofReal (C_CZ * (∑ j : Fin 3,
            lpNorm (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * f (y, s) j)
              (ENNReal.ofReal (6 / 5 : ℝ)) volume) + M * ρ ^ (-1 / 2 : ℝ)) :=
          (ENNReal.ofReal_add hnn1 hnn2).symm

/-- The constant of the force slot of display (3.5): the order-one far-field
constant of `eq:har-Ck` for the annular Newtonian potential, against the
gradient size of the ball cutoff of `lem:cutoff`. -/
noncomputable def sliceForceGradientConstant : ℝ :=
  400 * sliceForcePotentialConstant * cutoffGradientConstant

/-- The constant of the force slot of display (3.5) is nonnegative. -/
theorem sliceForceGradientConstant_nonneg : 0 ≤ sliceForceGradientConstant :=
  mul_nonneg (mul_nonneg (by norm_num) sliceForcePotentialConstant_nonneg)
    (pressure_cutoff_constants_nonneg (x₀ := (0 : Vec3)) (ρ := (1 : ℝ)) one_pos).1

/-- The `L^{6/5}` size of the force slot of display (3.5) on one time slice: the
Calderón–Zygmund norm of the cut-off force together with the `ρ^{-1/2}`-weighted
`L¹` norm of the force on the ball. -/
noncomputable def sliceForceGradientBound (C_CZ C₈ : ℝ) (x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (f : ParabolicPoint → Vec3) (s : ℝ) : ℝ :=
  C_CZ * (∑ j : Fin 3,
      lpNorm (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * f (y, s) j)
        (ENNReal.ofReal (6 / 5 : ℝ)) volume) +
    C₈ * (∫ y in vec3Ball x₀ ρ, vec3EuclideanNorm (f (y, s))) * ρ ^ (-1 / 2 : ℝ)

/-- The force slot of display (3.5) on one slice, from the `L^{6/5}` membership
of the first force density and the `L¹` data of the second.  The two force
potentials of `eq:pk` have a common coordinate weak gradient on the inner ball
`B_{ρ/2}(x₀)`, with the `L^{6/5}` bound of the display. -/
theorem slice_force_weak_gradient_of_slice_sources
    (C_CZ C₈ : ℝ) (hC_CZ : 0 ≤ C_CZ) (hC₈ : sliceForceGradientConstant ≤ C₈)
    {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    {f : ParabolicPoint → Vec3} {s : ℝ}
    (hP1 : ∀ (i : Fin 3) (G : Vec3 → ℝ),
      MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume → HasCompactSupport G →
      ∃ D : Vec3 → Vec3,
        MemLp D (ENNReal.ofReal (6 / 5 : ℝ)) volume ∧
        (∀ (j : Fin 3) (ψ : Vec3 → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          (∫ x, pressureNewtonianDerivativePotential i G x * spatialDeriv ψ j x) =
            -(∫ x, D x j * ψ x)) ∧
        eLpNorm D (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
          ENNReal.ofReal C_CZ * eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hmem : ∀ j : Fin 3, MemLp (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * f (y, s) j)
      (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hint : ∀ j : Fin 3, Integrable
      (fun y : Vec3 => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j)
      volume)
    (hbnd : ∀ j : Fin 3, (∫ y : Vec3,
        ‖spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j‖) ≤
      (cutoffGradientConstant / ρ) *
        ∫ y in vec3Ball x₀ ρ, vec3EuclideanNorm (f (y, s))) :
    ∃ g : Fin 3 → Vec3 → ℝ, ∀ k : Fin 3,
      HasWeakPartialDerivOn (euclideanBall x₀ (ρ / 2)) k
          (pressureP7 (mollifiedBallCutoff x₀ hρ) f s +
            pressureP8 (mollifiedBallCutoff x₀ hρ) f s) (g k) ∧
        LocallyIntegrableOn (g k) (euclideanBall x₀ (ρ / 2)) volume ∧
        eLpNorm (g k) (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict (euclideanBall x₀ (ρ / 2))) ≤
          ENNReal.ofReal (sliceForceGradientBound C_CZ C₈ x₀ hρ f s) := by
  have hρ0 : ρ ≠ 0 := ne_of_gt hρ
  have hIfs : 0 ≤ ∫ y in vec3Ball x₀ ρ, vec3EuclideanNorm (f (y, s)) :=
    setIntegral_nonneg (vec3Ball_measurable x₀ ρ)
      fun y _ => vec3EuclideanNorm_nonneg _
  have hK : 0 ≤ cutoffGradientConstant :=
    (pressure_cutoff_constants_nonneg (x₀ := x₀) hρ).1
  have hA0 : 0 ≤ (cutoffGradientConstant / ρ) *
      ∫ y in vec3Ball x₀ ρ, vec3EuclideanNorm (f (y, s)) :=
    mul_nonneg (div_nonneg hK hρ.le) hIfs
  have hC₈0 : 0 ≤ C₈ := sliceForceGradientConstant_nonneg.trans hC₈
  have hM : 0 ≤ C₈ * ∫ y in vec3Ball x₀ ρ, vec3EuclideanNorm (f (y, s)) :=
    mul_nonneg hC₈0 hIfs
  have hball : euclideanBall x₀ (ρ / 2) = vec3Ball x₀ (ρ / 2) :=
    euclideanBall_eq_vec3Ball_force (by positivity)
  have hp8 : ContDiffOn ℝ (1 : ℕ∞) (pressureP8 (mollifiedBallCutoff x₀ hρ) f s)
      (euclideanBall x₀ (ρ / 2)) := by
    rw [hball]
    exact contDiffOn_pressureP8_halfBall hρ hint
  have hsup : ∀ x ∈ euclideanBall x₀ (ρ / 2),
      vec3EuclideanNorm
        (classicalGradient (pressureP8 (mollifiedBallCutoff x₀ hρ) f s) x) ≤
        (C₈ * ∫ y in vec3Ball x₀ ρ, vec3EuclideanNorm (f (y, s))) * (ρ ^ 3)⁻¹ := by
    intro x hx
    rw [hball] at hx
    refine (vec3EuclideanNorm_classicalGradient_pressureP8_le hρ hA0 hint hbnd hx).trans ?_
    have harith : 400 * sliceForcePotentialConstant *
        ((cutoffGradientConstant / ρ) *
          ∫ y in vec3Ball x₀ ρ, vec3EuclideanNorm (f (y, s))) * (ρ ^ 2)⁻¹ =
        sliceForceGradientConstant *
          (∫ y in vec3Ball x₀ ρ, vec3EuclideanNorm (f (y, s))) * (ρ ^ 3)⁻¹ := by
      simp only [sliceForceGradientConstant]
      field_simp
    rw [harith]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₈ hIfs)
      (by positivity)
  have hcs : ∀ j : Fin 3, HasCompactSupport
      (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * f (y, s) j) :=
    fun j => hasCompactSupport_cutoff_mul_force x₀ hρ f s j
  have hmain := slice_force_weak_gradient_of_slice_data C_CZ
    (C₈ * ∫ y in vec3Ball x₀ ρ, vec3EuclideanNorm (f (y, s))) hC_CZ hM hρ hP1
    hmem hcs hp8 hsup
  simpa only [sliceForceGradientBound] using hmain

/-- A slice field selected for almost every time becomes a single function of
time.  This is the measurable-free Skolemization that display (3.5) needs
before the space-time selection of the pressure gradient is applied. -/
theorem exists_slice_field_of_ae
    {B : Set Vec3} {J : Set ℝ} {w : ℝ → Vec3 → ℝ} {Sw : ℝ → ℝ}
    (h : ∀ᵐ s ∂volume.restrict J, ∃ g : Fin 3 → Vec3 → ℝ, ∀ k : Fin 3,
      HasWeakPartialDerivOn B k (w s) (g k) ∧
        LocallyIntegrableOn (g k) B volume ∧
        eLpNorm (g k) (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) ≤
          ENNReal.ofReal (Sw s)) :
    ∃ gw : ℝ → Fin 3 → Vec3 → ℝ,
      ∀ᵐ s ∂volume.restrict J, ∀ k : Fin 3,
        HasWeakPartialDerivOn B k (w s) (gw s k) ∧
          LocallyIntegrableOn (gw s k) B volume ∧
          eLpNorm (gw s k) (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) ≤
            ENNReal.ofReal (Sw s) := by
  classical
  have htotal : ∀ s : ℝ, ∃ g : Fin 3 → Vec3 → ℝ,
      (∃ g' : Fin 3 → Vec3 → ℝ, ∀ k : Fin 3,
        HasWeakPartialDerivOn B k (w s) (g' k) ∧
          LocallyIntegrableOn (g' k) B volume ∧
          eLpNorm (g' k) (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) ≤
            ENNReal.ofReal (Sw s)) →
      ∀ k : Fin 3,
        HasWeakPartialDerivOn B k (w s) (g k) ∧
          LocallyIntegrableOn (g k) B volume ∧
          eLpNorm (g k) (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) ≤
            ENNReal.ofReal (Sw s) := by
    intro s
    by_cases hs : ∃ g' : Fin 3 → Vec3 → ℝ, ∀ k : Fin 3,
        HasWeakPartialDerivOn B k (w s) (g' k) ∧
          LocallyIntegrableOn (g' k) B volume ∧
          eLpNorm (g' k) (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) ≤
            ENNReal.ofReal (Sw s)
    · exact ⟨hs.choose, fun _ => hs.choose_spec⟩
    · exact ⟨fun _ _ => 0, fun hcon => absurd hcon hs⟩
  choose gw hgw using htotal
  refine ⟨gw, ?_⟩
  filter_upwards [h] with s hs
  exact hgw s hs

/-- The force slot of display (3.5) for a suitable weak solution, with no
condition on the divergence of the force.  For almost every time of the
one-sided interval `J_ρ` the two force potentials of `eq:pk` have a common
coordinate weak gradient on the inner ball `B_{ρ/2}(x₀)`, locally integrable
there and bounded in `L^{6/5}` by the Calderón–Zygmund norm of the cut-off
force together with the `ρ^{-1/2}`-weighted `L¹` norm of the force on
`B_ρ(x₀)`. -/
theorem exists_slice_force_weak_gradient_ae_of_sws
    (C_CZ C₈ : ℝ) (hC_CZ : 0 ≤ C_CZ) (hC₈ : sliceForceGradientConstant ≤ C₈)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hP1 : ∀ (i : Fin 3) (G : Vec3 → ℝ),
      MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume → HasCompactSupport G →
      ∃ D : Vec3 → Vec3,
        MemLp D (ENNReal.ofReal (6 / 5 : ℝ)) volume ∧
        (∀ (j : Fin 3) (ψ : Vec3 → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          (∫ x, pressureNewtonianDerivativePotential i G x * spatialDeriv ψ j x) =
            -(∫ x, D x j * ψ x)) ∧
        eLpNorm D (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
          ENNReal.ofReal C_CZ * eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume) :
    ∃ gw : ℝ → Fin 3 → Vec3 → ℝ,
      ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2), ∀ k : Fin 3,
        HasWeakPartialDerivOn (euclideanBall z.1 (ρ / 2)) k
            (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
              pressureP8 (mollifiedBallCutoff z.1 hρ) f s) (gw s k) ∧
          LocallyIntegrableOn (gw s k) (euclideanBall z.1 (ρ / 2)) volume ∧
          eLpNorm (gw s k) (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict (euclideanBall z.1 (ρ / 2))) ≤
            ENNReal.ofReal (sliceForceGradientBound C_CZ C₈ z.1 hρ f s) := by
  refine exists_slice_field_of_ae (B := euclideanBall z.1 (ρ / 2))
    (J := Ioc (z.2 - ρ ^ 2) z.2)
    (w := fun s => pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
      pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
    (Sw := fun s => sliceForceGradientBound C_CZ C₈ z.1 hρ f s) ?_
  filter_upwards [slice_force_source_data_ae_of_sws hsol hρ hsub] with s hs
  exact slice_force_weak_gradient_of_slice_sources C_CZ C₈ hC_CZ hC₈ hρ hP1
    hs.2.1 hs.2.2.1 hs.2.2.2

end CKN.Core.Step4
