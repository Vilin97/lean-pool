/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientAssembly
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientScaling
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientSWS
public import LeanPool.CaffarelliKohnNirenberg.Pressure.HarmonicRemainderSlice

/-! # The selected weak pressure gradient of a suitable weak solution slice

For a suitable weak solution and almost every time `s` of the one-sided
interval `J_ρ = (t₀ - ρ², t₀]`, the local pressure decomposition of the
pressure-gradient section writes the slice as `p₁ + p_har + (p₇ + p₈)` on the
inner ball `B_{13ρ/20}(x₀)`.  Differentiating the three summands separately —
the first by the Calderón–Zygmund selection applied to the divergence-form
source, the second classically on `B_{ρ/2}(x₀)`, the third by its own
potential identities — produces the slice field of display (3.5).

The harmonic term is taken from the interior gradient display, whose
`ρ^{-3}` weight becomes the `ρ^{-1/2}` weight of display (3.5) once it is
integrated over the half ball.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN.Core.Step4

private lemma isOpen_euclideanBall_slice (x₀ : Vec3) (r : ℝ) :
    IsOpen (euclideanBall x₀ r) := by
  change IsOpen {x : Vec3 | euclideanSqDist x x₀ < r ^ 2}
  exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const

private lemma euclideanBall_half_subset_inner {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) :
    euclideanBall x₀ (ρ / 2) ⊆ euclideanBall x₀ (13 * ρ / 20) := by
  intro x hx
  have hx' : vecEuclideanNorm (x - x₀) < ρ / 2 :=
    (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hx
  exact (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
    (hx'.trans (by linarith only [hρ]))

private lemma volume_euclideanBall_ne_top (x₀ : Vec3) {r : ℝ} (hr : 0 < r) :
    volume (euclideanBall x₀ r) ≠ ∞ := by
  have heq : euclideanBall x₀ r = vec3Ball x₀ r := by
    ext x
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hr, mem_vec3Ball]
    simp only [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
  rw [heq]
  exact (CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top (x := x₀) (r := r)).ne

/-- A slice which lies in `L^{3/2}` of a ball of finite measure is locally
integrable there.  This is the regularity of the force potentials which
display (3.5) uses before their weak derivatives are taken. -/
theorem locallyIntegrableOn_of_memLp_three_halves {g : Vec3 → ℝ}
    {x₀ : Vec3} {r : ℝ} (hr : 0 < r)
    (hg : MemLp g (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ r))) :
    LocallyIntegrableOn g (euclideanBall x₀ r) volume := by
  have hfin : IsFiniteMeasure (volume.restrict (euclideanBall x₀ r)) :=
    isFiniteMeasure_restrict.mpr (volume_euclideanBall_ne_top x₀ hr)
  have hint : IntegrableOn g (euclideanBall x₀ r) volume :=
    hg.integrable (ENNReal.one_le_ofReal.2 (by norm_num))
  exact hint.locallyIntegrableOn

/-- The coordinate `L^{6/5}` bound of the harmonic part of the pressure slice
on the half ball, in the `ρ^{-1/2}` normalization of display (3.5).  The input
is the interior gradient display of the harmonic remainder. -/
theorem slice_harmonic_gradient_component_ae_of_sws
    (C₁₇ C₁₁ : ℝ)
    (hC₁₇ : 1000 * harmonicInteriorDisplayConstant ≤ C₁₇)
    {E F : ℝ → ℝ}
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hC₁₁ : 0 ≤ C₁₁) (hE : ∀ s, 0 ≤ E s) (hF : ∀ s, 0 ≤ F s)
    (hCZ_p1 : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (pressureP1 (mollifiedBallCutoff z.1 hρ) u
        (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
          (fun y : Vec3 => u (y, t) j)) p f s)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
      lpNorm (pressureP1 (mollifiedBallCutoff z.1 hρ) u
        (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
          (fun y : Vec3 => u (y, t) j)) p f s)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤ C₁₁ * (E s) ^ (2 / 3 : ℝ))
    (hP78 : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall z.1 (13 * ρ / 20))) ∧
      lpNorm (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall z.1 (13 * ρ / 20))) ≤ F s)
    (hregular : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ContDiffOn ℝ (1 : ℕ∞)
        (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
          (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
            (fun y : Vec3 => u (y, t) j)) p s)
        (euclideanBall z.1 (ρ / 2))) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2), ∀ k : Fin 3,
      eLpNorm (fun x => classicalGradient
          (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
            (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
              (fun y : Vec3 => u (y, t) j)) p s) x k)
        (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (euclideanBall z.1 (ρ / 2))) ≤
      ENNReal.ofReal (C₁₇ *
        (lpNorm (fun x : Vec3 => p (x, s)) (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall z.1 ρ)) +
          C₁₁ * (E s) ^ (2 / 3 : ℝ) + F s) * ρ ^ (-1 / 2 : ℝ)) := by
  have hC₁₇nonneg : 0 ≤ C₁₇ :=
    (mul_nonneg (by norm_num) harmonicInteriorDisplayConstant_nonneg).trans hC₁₇
  have hharm := harmonic_remainder_gradient_eLpNorm_ae_of_sws C₁₇ C₁₁ hC₁₇
    hsol hρ hsub hC₁₁ hE hF hCZ_p1 hP78 hregular
  filter_upwards [hharm, hregular] with s hs hsreg
  intro k
  have hL : 0 ≤ lpNorm (fun x : Vec3 => p (x, s)) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall z.1 ρ)) +
      C₁₁ * (E s) ^ (2 / 3 : ℝ) + F s :=
    add_nonneg (add_nonneg lpNorm_nonneg
      (mul_nonneg hC₁₁ (Real.rpow_nonneg (hE s) _))) (hF s)
  have hmeas : AEStronglyMeasurable
      (fun x => classicalGradient
        (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
          (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
            (fun y : Vec3 => u (y, t) j)) p s) x k)
      (volume.restrict (euclideanBall z.1 (ρ / 2))) :=
    (locallyIntegrableOn_classicalGradient
      (isOpen_euclideanBall_slice z.1 (ρ / 2)) k hsreg).aestronglyMeasurable
  have hcomp := eLpNorm_mono_ae (p := ENNReal.ofReal (6 / 5 : ℝ))
    (μ := volume.restrict (euclideanBall z.1 (ρ / 2))) hmeas
    (Eventually.of_forall fun x => norm_le_pi_norm
      (classicalGradient (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
        (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
          (fun y : Vec3 => u (y, t) j)) p s) x) k)
  refine hcomp.trans (hs.2.trans ?_)
  have hscale := halfBall_volume_rpow_five_sixths_mul_inv_cube_le z.1 (C := C₁₇ *
      (lpNorm (fun x : Vec3 => p (x, s)) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall z.1 ρ)) +
        C₁₁ * (E s) ^ (2 / 3 : ℝ) + F s)) hρ (mul_nonneg hC₁₇nonneg hL)
  have hcongr : (C₁₇ * (ρ ^ 3)⁻¹) *
      (lpNorm (fun x : Vec3 => p (x, s)) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall z.1 ρ)) +
        C₁₁ * (E s) ^ (2 / 3 : ℝ) + F s) =
      (C₁₇ * (lpNorm (fun x : Vec3 => p (x, s)) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall z.1 ρ)) +
        C₁₁ * (E s) ^ (2 / 3 : ℝ) + F s)) * (ρ ^ 3)⁻¹ := by ring
  rw [hcongr]
  exact hscale

/-- Display (3.5) of the pressure-gradient section, on one time slice of a
suitable weak solution.

For almost every time of the one-sided interval `J_ρ` the pressure slice has a
`Vec3`-valued weak spatial gradient on the half ball `B_{ρ/2}(x₀)`: its
coordinates are locally integrable there, it lies in `L^{6/5}` there, it is the
coordinate weak gradient of the slice, and its coordinate norms are bounded by
the Calderón–Zygmund norm of the divergence-form source together with the
`ρ^{-1/2}`-weighted `L^{3/2}` norm of the pressure and the force-potential
term. -/
theorem slice_selected_gradient_ae_of_sws
    (C_CZ C₁₇ C₁₁ : ℝ)
    (hC₁₇ : 1000 * harmonicInteriorDisplayConstant ≤ C₁₇)
    {E F Sw : ℝ → ℝ}
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    {V : ParabolicPoint → Vec3} {gw : ℝ → Fin 3 → Vec3 → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hC₁₁ : 0 ≤ C₁₁) (hE : ∀ s, 0 ≤ E s) (hF : ∀ s, 0 ≤ F s)
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
    (hCZ_p1 : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (pressureP1 (mollifiedBallCutoff z.1 hρ) u
        (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
          (fun y : Vec3 => u (y, t) j)) p f s)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
      lpNorm (pressureP1 (mollifiedBallCutoff z.1 hρ) u
        (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
          (fun y : Vec3 => u (y, t) j)) p f s)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤ C₁₁ * (E s) ^ (2 / 3 : ℝ))
    (hP78 : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall z.1 (13 * ρ / 20))) ∧
      lpNorm (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall z.1 (13 * ρ / 20))) ≤ F s)
    (hregular : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ContDiffOn ℝ (1 : ℕ∞)
        (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
          (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
            (fun y : Vec3 => u (y, t) j)) p s)
        (euclideanBall z.1 (ρ / 2)))
    (hV : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      (∀ i : Fin 3, MemLp (fun x => V (x, s) i)
        (ENNReal.ofReal (6 / 5 : ℝ)) volume) ∧
      (∀ i : Fin 3, HasCompactSupport (fun x => V (x, s) i)))
    (hident : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      pressureP1 (mollifiedBallCutoff z.1 hρ) u
          (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
            (fun y : Vec3 => u (y, t) j)) p f s =ᵐ[
        volume.restrict (euclideanBall z.1 (ρ / 2))]
        fun x => ∑ i, pressureNewtonianDerivativePotential i
          (fun y => V (y, s) i) x)
    (hforce : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2), ∀ k : Fin 3,
      HasWeakPartialDerivOn (euclideanBall z.1 (ρ / 2)) k
          (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
            pressureP8 (mollifiedBallCutoff z.1 hρ) f s) (gw s k) ∧
        LocallyIntegrableOn (gw s k) (euclideanBall z.1 (ρ / 2)) volume ∧
        eLpNorm (gw s k) (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall z.1 (ρ / 2))) ≤
          ENNReal.ofReal (Sw s)) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∃ D : Vec3 → Vec3,
        (∀ k : Fin 3, LocallyIntegrableOn (fun x => D x k)
          (euclideanBall z.1 (ρ / 2)) volume) ∧
        MemLp D (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall z.1 (ρ / 2))) ∧
        (∀ k : Fin 3, HasWeakPartialDerivOn (euclideanBall z.1 (ρ / 2)) k
          (fun x => p (x, s)) (fun x => D x k)) ∧
        (∀ k : Fin 3, eLpNorm (fun x => D x k) (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict (euclideanBall z.1 (ρ / 2))) ≤
          ENNReal.ofReal C_CZ *
              (∑ i : Fin 3, eLpNorm (fun x => V (x, s) i)
                (ENNReal.ofReal (6 / 5 : ℝ)) volume) +
            ENNReal.ofReal (C₁₇ *
              (lpNorm (fun x : Vec3 => p (x, s)) (ENNReal.ofReal (3 / 2 : ℝ))
                  (volume.restrict (euclideanBall z.1 ρ)) +
                C₁₁ * (E s) ^ (2 / 3 : ℝ) + F s) * ρ ^ (-1 / 2 : ℝ)) +
            ENNReal.ofReal (Sw s)) := by
  have hharmbd := slice_harmonic_gradient_component_ae_of_sws C₁₇ C₁₁ hC₁₇
    hsol hρ hsub hC₁₁ hE hF hCZ_p1 hP78 hregular
  have hslice := pressure_slice_representation_of_sws hsol hρ hsub
  filter_upwards [hslice, hharmbd, hregular, hP78, hV, hident, hforce] with
    s hs hbd hreg h78 hVs hid hfs
  have hwloc : LocallyIntegrableOn
      (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
      (euclideanBall z.1 (ρ / 2)) volume :=
    locallyIntegrableOn_of_memLp_three_halves (by positivity)
      (h78.1.mono_measure
        (Measure.restrict_mono_set volume (euclideanBall_half_subset_inner hρ)))
  have hrep : (fun x : Vec3 => p (x, s)) =ᵐ[
      volume.restrict (euclideanBall z.1 (ρ / 2))]
      fun x => (∑ i, pressureNewtonianDerivativePotential i
          (fun y => V (y, s) i) x) +
        (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
            (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
              (fun y : Vec3 => u (y, t) j)) p s x +
          (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
            pressureP8 (mollifiedBallCutoff z.1 hρ) f s) x) := by
    have hrep0 := ae_restrict_of_ae_restrict_of_subset
      (euclideanBall_half_subset_inner hρ) hs.1
    filter_upwards [hrep0, hid] with x hx hxid
    simp only [Pi.add_apply] at hx ⊢
    rw [hx, hxid]
    ring
  exact slice_selected_gradient_of_potential_representation C_CZ
    (Sh := ENNReal.ofReal (C₁₇ *
      (lpNorm (fun x : Vec3 => p (x, s)) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall z.1 ρ)) +
        C₁₁ * (E s) ^ (2 / 3 : ℝ) + F s) * ρ ^ (-1 / 2 : ℝ)))
    (Sw := ENNReal.ofReal (Sw s))
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    (isOpen_euclideanBall_slice z.1 (ρ / 2)) hP1 hVs.1 hVs.2 hrep hreg hbd
    hwloc (fun k => (hfs k).1) (fun k => (hfs k).2.1) (fun k => (hfs k).2.2)

/-- The vector-valued slice field of display (3.5) supplies the scalar
per-coordinate interface consumed by the space-time measurable selection of the
pressure gradient. -/
theorem exists_scalar_slice_gradient_of_vector_slice
    {B : Set Vec3} {J : Set ℝ} {p : ParabolicPoint → ℝ} {K : ℝ → ℝ≥0∞}
    (k : Fin 3)
    (hD : ∀ᵐ s ∂(volume.restrict J), ∃ D : Vec3 → Vec3,
      (∀ j : Fin 3, LocallyIntegrableOn (fun x => D x j) B volume) ∧
      MemLp D (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) ∧
      (∀ j : Fin 3, HasWeakPartialDerivOn B j (fun x => p (x, s))
        (fun x => D x j)) ∧
      (∀ j : Fin 3, eLpNorm (fun x => D x j) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict B) ≤ K s)) :
    ∀ᵐ s ∂(volume.restrict J), ∃ g : Vec3 → ℝ,
      LocallyIntegrableOn g B volume ∧
      HasWeakPartialDerivOn B k (fun x => p (x, s)) g ∧
      eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) ≤ K s := by
  filter_upwards [hD] with s hs
  obtain ⟨D, hloc, _hmem, hweak, hbound⟩ := hs
  exact ⟨fun x => D x k, hloc k, hweak k, hbound k⟩

end CKN.Core.Step4
