/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34CentredPotentialGrowth
public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionGrowth
public import LeanPool.CaffarelliKohnNirenberg.Pressure.HarmonicRemainderForceTerms
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34Slices
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34SliceIntegrated

/-!
# Lin34 Centred Residual

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

open CKN.Foundation.Euclidean

/-!
# Local growth of the centred first potential against its indexed extension

This file supplies the decay hypothesis of the Liouville step of `ext:newtonian`
in `paper/ckn.tex` for the centred first potential of
`prop:pressure-decomposition`: for a suitable weak solution and almost every time
of the cylinder `Q_ρ(z₀)`, the difference between the centred potential `p₁` and
the indexed second-order Riesz extension of its source lies in `L^{3/2}` on every
round ball about the origin, with norm growing at most linearly in the radius.

The residual bookkeeping is the established comparison
`pressureSecondExtension_residual_growth_of_decomposition`, fed with the
`p₂`--`p₆` group of `prop:pressure-decomposition`, the force group `p₇ + p₈`, the
cut-off pressure, and the indexed extension of the cut-off centred tensor.
-/

private lemma lin34Residual_euclideanBall_eq_vec3Ball {x₀ : Vec3} {r : ℝ}
    (hr : 0 < r) : euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  change x ∈ euclideanBall x₀ r ↔ vec3EuclideanNorm (x - x₀) < r
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
    (mem_euclideanBall_iff_vecEuclideanNorm_lt hr)

/-- The cut-off pressure `x ↦ η(x)·p(x,s)` of `prop:pressure-decomposition`,
formed with the mollified cut-off of `B_ρ(x₀)`, is `L^{3/2}` with respect to
Lebesgue measure on all of `ℝ³` as soon as the pressure slice is `L^{3/2}` on
`B_ρ(x₀)`: the cut-off is bounded by one and supported there. -/
private lemma lin34Residual_cutoffPressure_memLp_volume
    {p : ParabolicPoint → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) {s : ℝ}
    (hp : MemLp (fun y : Vec3 => p (y, s)) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (vec3Ball x₀ ρ))) :
    MemLp (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * p (y, s))
      (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
  have hηsupp : tsupport (mollifiedBallCutoff x₀ hρ) ⊆ vec3Ball x₀ ρ :=
    pressure_cutoff_support_subset_ball x₀ hρ
  have hzero : ∀ y, y ∉ vec3Ball x₀ ρ →
      mollifiedBallCutoff x₀ hρ y * p (y, s) = 0 := by
    intro y hy
    have hout : y ∉ tsupport (mollifiedBallCutoff x₀ hρ) :=
      fun hmem => hy (hηsupp hmem)
    rw [image_eq_zero_of_notMem_tsupport hout, zero_mul]
  have hsupp : Function.support
      (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * p (y, s)) ⊆ vec3Ball x₀ ρ :=
    Function.support_subset_iff'.2 hzero
  have hmeasBall : AEStronglyMeasurable
      (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * p (y, s))
      (volume.restrict (vec3Ball x₀ ρ)) :=
    ((mollifiedBallCutoff_smooth x₀ hρ).continuous.aestronglyMeasurable).mul
      hp.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable
      (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * p (y, s)) volume := by
    have hind : (vec3Ball x₀ ρ).indicator
        (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * p (y, s)) =
        (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * p (y, s)) :=
      Set.indicator_eq_self.2 hsupp
    have h := (aestronglyMeasurable_indicator_iff
      (isOpen_vec3Ball x₀ ρ).measurableSet).2 hmeasBall
    rwa [hind] at h
  have hball : MemLp (fun y : Vec3 => mollifiedBallCutoff x₀ hρ y * p (y, s))
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball x₀ ρ)) :=
    pressure_cutoff_pressure_memLp_slice hp
      ((mollifiedBallCutoff_smooth x₀ hρ).continuous.aestronglyMeasurable)
      (Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr
          ⟨by linarith only [mollifiedBallCutoff_nonneg x₀ hρ x],
            mollifiedBallCutoff_le_one x₀ hρ x⟩))
  exact memLp_volume_of_memLp_restrict_of_support hmeas hsupp hball

/-- **Decay of the centred potential residual.**  For a suitable weak solution
and almost every time `s` of the cylinder `Q_ρ(z₀)`, the difference between the
centred first potential `p₁` of `prop:pressure-decomposition` and the indexed
second-order Riesz extension of its source `η·Û` lies in `L^{3/2}` on every round
ball about the origin, with local norm bounded by a constant times `1 + R`.

The constant accumulates the four pieces of the decomposition: the cut-off
pressure, the `p₂`--`p₆` group, the force group `p₇ + p₈`, and the indexed
extension itself.  This is the Liouville decay input of `ext:newtonian` in
`paper/ckn.tex`. -/
theorem lin34_centred_residual_local_growth_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2), ∃ C : ℝ, 0 ≤ C ∧
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
          (volume.restrict (euclideanBall (0 : Vec3) R)) ≤ C * (1 + R)) := by
  let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ
  let R₀ : ℝ := vec3EuclideanNorm z.1 + ρ
  have hR₀ : 0 < R₀ := by
    dsimp [R₀]
    linarith only [vec3EuclideanNorm_nonneg z.1, hρ]
  obtain ⟨Ω', J, hbox, hball, htime⟩ := pressure_box_geometry hsol hρ hsub
  have hslices := ae_restrict_of_ae_restrict_of_subset htime
    (slice_memLp_ae_of_sws hsol hbox)
  have hVae := lin34_slice_integrableOn_ball_ae
    (lin34_integrableOn_meanFree_cube (u := u) (x := z.1) (t := z.2) (r := ρ)
      hρ (tsai_integrable_velocity_on_cylinder hsol hρ hsub)
      (tsai_integrable_velocity_cube_on_cylinder hsol hρ hsub))
  have hpslices := sws_pressure_memLp_slice_ae hsol hρ hsub
  have hforce := pressure_force_memLp_and_lpNorm_growth_ae_of_sws hsol hρ hsub
  filter_upwards [hslices, hVae, hpslices, hforce] with s hus hVs hpSlice hJ
  have hu : AEStronglyMeasurable (fun y : Vec3 => u (y, s))
      (volume.restrict (vec3Ball z.1 ρ)) :=
    (hus.1.mono_measure (Measure.restrict_mono_set volume hball)).aestronglyMeasurable
  have hv : IntegrableOn
      (fun y => vec3EuclideanNorm (meanFreeVec u z.1 ρ s y) ^ (3 : ℕ))
      (euclideanBall z.1 ρ) volume := by
    rw [lin34Residual_euclideanBall_eq_vec3Ball hρ]
    exact hVs
  have hHdata := lin34_centred_potentials_memLp_and_growth (u := u) (p := p)
    (x₀ := z.1) hρ hu hv hpSlice
  obtain ⟨C_H, hC_H, hHmemRaw, hHboundRaw⟩ := hHdata
  have hG : ∀ i j, MemLp (lin34CentredSource u z.1 hρ s i j)
      (ENNReal.ofReal ((3 : ℝ) / 2)) volume :=
    fun i j => (lin34CentredSource_memLp_and_lpNorm_le hρ hu hv i j).1
  have hT := pressureSecondExtension_memLp rieszSecondL2Input
    rieszSecondL2_weak_type (G := lin34CentredSource u z.1 hρ s) hG
  have hPglobal : MemLp (fun y : Vec3 => η y * p (y, s))
      (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
    simpa only [η] using lin34Residual_cutoffPressure_memLp_volume hρ hpSlice
  obtain ⟨hJmemRaw, hJnonnegRaw, hJboundRaw⟩ := hJ
  let H : Vec3 → ℝ := fun x =>
    pressureP2 η (lin34CentredVelocity u z.1 ρ) 0 s x +
      pressureP3 η (lin34CentredVelocity u z.1 ρ) 0 s x +
      pressureP4 η (lin34CentredVelocity u z.1 ρ) 0 s x +
      pressureP5 η p s x + pressureP6 η p s x
  let Jf : Vec3 → ℝ := pressureP7 η f s + pressureP8 η f s
  have hHmem : ∀ R : ℝ, 0 < R →
      MemLp H (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) R)) :=
    fun R hR => by simpa only [H, η] using hHmemRaw R hR
  have hHbound : ∀ R : ℝ, 0 < R →
      lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) R)) ≤ C_H * (1 + R) :=
    fun R hR => by simpa only [H, η] using hHboundRaw R hR
  have hJmem : ∀ R : ℝ, 0 < R →
      MemLp Jf (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) R)) :=
    fun R hR => by simpa only [Jf, η] using hJmemRaw R hR
  have hJbound : ∀ R : ℝ, 0 < R →
      lpNorm Jf (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) R)) ≤
        (pressureP7GrowthConstant η f s R₀ + pressureP8GrowthConstant η f s R₀) *
          (1 + R) :=
    fun R hR => by simpa only [Jf, η, R₀] using hJboundRaw R hR
  have hJnonneg : 0 ≤ pressureP7GrowthConstant η f s R₀ +
      pressureP8GrowthConstant η f s R₀ := by
    simpa only [η, R₀] using hJnonnegRaw
  have hdecomp : lin34CentredP1 u p f z.1 ρ hρ s =
      (fun x => η x * p (x, s)) - (H + Jf) := by
    funext x
    simp only [lin34CentredP1, pressureP1, H, Jf, η, Pi.sub_apply, Pi.add_apply]
    ring
  have hres := pressureSecondExtension_residual_growth_of_decomposition
    (p₁ := lin34CentredP1 u p f z.1 ρ hρ s)
    (T := pressureSecondExtensionOperator rieszSecondL2Input rieszSecondL2_weak_type
      (lin34CentredSource u z.1 hρ s))
    (P := fun x => η x * p (x, s)) (H := H) (J := Jf)
    (C₀ := lpNorm (fun x => η x * p (x, s)) (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (C_H := C_H)
    (C_J := pressureP7GrowthConstant η f s R₀ + pressureP8GrowthConstant η f s R₀)
    (C_T := lpNorm (pressureSecondExtensionOperator rieszSecondL2Input
      rieszSecondL2_weak_type (lin34CentredSource u z.1 hρ s))
      (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    hdecomp
    (fun R _hR => memLp_euclideanBall_of_memLp_volume hPglobal R)
    (fun R hR => lpNorm_euclideanBall_le_of_memLp_volume hPglobal hR)
    hHmem hHbound hJmem hJbound
    (fun R _hR => memLp_euclideanBall_of_memLp_volume hT R)
    (fun R hR => lpNorm_euclideanBall_le_of_memLp_volume hT hR)
  refine ⟨lpNorm (fun x => η x * p (x, s)) (ENNReal.ofReal (3 / 2 : ℝ)) volume +
      C_H +
      (pressureP7GrowthConstant η f s R₀ + pressureP8GrowthConstant η f s R₀) +
      lpNorm (pressureSecondExtensionOperator rieszSecondL2Input
        rieszSecondL2_weak_type (lin34CentredSource u z.1 hρ s))
        (ENNReal.ofReal (3 / 2 : ℝ)) volume, ?_, ?_, ?_⟩
  · linarith only [lpNorm_nonneg (μ := volume)
      (f := fun x => η x * p (x, s)) (p := ENNReal.ofReal (3 / 2 : ℝ)),
      hC_H, hJnonneg,
      lpNorm_nonneg (μ := volume)
        (f := pressureSecondExtensionOperator rieszSecondL2Input
          rieszSecondL2_weak_type (lin34CentredSource u z.1 hρ s))
        (p := ENNReal.ofReal (3 / 2 : ℝ))]
  · intro R hR
    simpa only [η, R₀] using (hres R hR).1
  · intro R hR
    simpa only [η, R₀] using (hres R hR).2

end CKN
