/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.Localization
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientMorrey
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.WeakPressureSlice
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SourceMorreyData
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorDisplays
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolutionIntegrable
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Minkowski
public import LeanPool.CaffarelliKohnNirenberg.Pressure.DecompositionSWSBasic
public import LeanPool.CaffarelliKohnNirenberg.Pressure.DerivativeAdjoint
public import LeanPool.CaffarelliKohnNirenberg.Pressure.HarmonicPartDerivatives
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34Slices
public import LeanPool.CaffarelliKohnNirenberg.Pressure.HarmonicRemainderSlice
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientScaling

/-!
# Pressure Gradient SWS

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Heat

noncomputable section

namespace CKN.Core.Step4

/-! The p₁ slot is supplied by the completed weak-gradient extension.  This
adapter deliberately consumes the D15 existential and never differentiates
the literal first-potential representative. -/

theorem pressure_slice_bound_of_riesz_weak_extension
    {B B' : Set Vec3} (hB : IsOpen B)
    {p H gh G : Vec3 → ℝ} {i : Fin 3} {ρ C : ℝ}
    (hP1 : ∀ (i : Fin 3) (G : Vec3 → ℝ),
      MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume → HasCompactSupport G →
      ∃ D : Vec3 → Vec3,
        MemLp D (ENNReal.ofReal (6 / 5 : ℝ)) volume ∧
        (∀ (j : Fin 3) (ψ : Vec3 → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          (∫ x, pressureNewtonianDerivativePotential i G x * spatialDeriv ψ j x) =
            -(∫ x, D x j * ψ x)) ∧
        eLpNorm D (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
          ENNReal.ofReal C * eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    {k : Fin 3}
    (hG : MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hGc : HasCompactSupport G)
    (hrep : p =ᵐ[volume.restrict B]
      pressureNewtonianDerivativePotential i G + H)
    (hH : HasWeakPartialDerivOn B k H gh)
    (hPloc : LocallyIntegrableOn
      (pressureNewtonianDerivativePotential i G) B volume)
    (hHloc : LocallyIntegrableOn H B volume)
    (hghloc : LocallyIntegrableOn gh B volume)
    (hgh : eLpNorm gh (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B') ≤
      ENNReal.ofReal C * ENNReal.ofReal (ρ ^ (-1 / 2 : ℝ)) *
        eLpNorm p (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict B)) :
    ∃ g : Vec3 → ℝ,
      LocallyIntegrableOn g B volume ∧
      HasWeakPartialDerivOn B k p g ∧
      eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B') ≤
        ENNReal.ofReal C * (eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume +
          ENNReal.ofReal (ρ ^ (-1 / 2 : ℝ)) *
            eLpNorm p (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict B)) := by
  obtain ⟨D, hDmem, hDpair, hDbound⟩ := hP1 i G hG hGc
  refine ⟨fun x => D x k + gh x, ?_⟩
  exact CKN.Core.Endgame.pressure_slice_bound_of_vector_weak_extension
    hB hrep (hDpair k) hH hPloc hHloc hDmem hghloc hDbound hgh

/-! The solution-level local decomposition used by the slice gradient route.
The harmonic-gradient estimate is deliberately not folded into this bridge:
the harmonic slice producer supplies that estimate separately. -/

theorem pressure_slice_representation_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂(volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)),
      (fun x : Vec3 => p (x, s)) =ᵐ[
        volume.restrict (euclideanBall z.1 (13 * ρ / 20))]
        (pressureP1 (mollifiedBallCutoff z.1 hρ) u
          (fun t j => MeasureTheory.average
            (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j)) p f s +
          harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
            (fun t j => MeasureTheory.average
              (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j)) p s +
          (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
            pressureP8 (mollifiedBallCutoff z.1 hρ) f s)) ∧
      WeaklyHarmonicOn (euclideanBall z.1 (13 * ρ / 20))
        (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
          (fun t j => MeasureTheory.average
            (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j)) p s) := by
  have hdata := pressure_harmonic_potential_data_ae_of_sws_annulus
    hsol hρ hsub (fun y hy => pressure_cutoff_derivatives_vanish z.1 hρ hy)
  have hinner : euclideanBall z.1 (13 * ρ / 20) ⊆
      (euclideanBall z.1 (3 * ρ / 4) \ euclideanClosedBall z.1
        (13 * ρ / 20))ᶜ := by
    intro y hy hyann
    apply hyann.2
    apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
    exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hy).le
  filter_upwards [hdata] with s hs
  have hweakU := harmonicPressurePart_weaklyHarmonicOn_of_data hs
  have hweak := local_weak_harmonic hinner hweakU
  have hrep := pressure_remainder_eq_on_inner
    (u := u) (c := fun t j => MeasureTheory.average
      (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
    (p := p) (f := f) (x₀ := z.1) (ρ := ρ) (s := s) hρ
  refine ⟨?_, hweak⟩
  filter_upwards [hrep] with x hx
  change p (x, s) =
    pressureP1 (mollifiedBallCutoff z.1 hρ) u
        (fun t j => MeasureTheory.average
          (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j)) p f s x +
      harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
        (fun t j => MeasureTheory.average
          (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j)) p s x +
      (pressureP7 (mollifiedBallCutoff z.1 hρ) f s x +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s x)
  change harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
      (fun t j => MeasureTheory.average
        (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j)) p s x =
    p (x, s) - pressureP1 (mollifiedBallCutoff z.1 hρ) u
        (fun t j => MeasureTheory.average
          (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j)) p f s x -
      (pressureP7 (mollifiedBallCutoff z.1 hρ) f s x +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s x) at hx
  linarith only [hx]

end CKN.Core.Step4
