/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.Liouville

/-!
# Potential Decay Growth Sum

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
noncomputable section
namespace CKN

/-!
# Growth bookkeeping for local `L^{3/2}` norms of pressure potentials

This file collects the elementary measure-theoretic bookkeeping used to
compare the local `L^{3/2}` norms of the pressure potentials on the round
balls `euclideanBall 0 ρ`: a global `MemLp` bound restricts to any ball, the
local norm is controlled by the global norm times the linear growth factor
`1 + ρ`, and the operation of adding, subtracting, or summing finitely many
potentials preserves an affine growth bound of the shape `C * (1 + ρ)`.
The statements are purely about `MeasureTheory.lpNorm`; no analysis enters.
-/

/-- A function that is `L^{3/2}` with respect to Lebesgue measure remains
    `L^{3/2}` after restricting Lebesgue measure to any round ball about the
    origin. -/
theorem memLp_euclideanBall_of_memLp_volume {h : Vec3 → ℝ}
    (hh : MemLp h (ENNReal.ofReal (3 / 2 : ℝ)) volume) (ρ : ℝ) :
    MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) :=
  hh.restrict _

/-- The local `L^{3/2}` norm of a global `L^{3/2}` function over the ball of
    radius `ρ > 0` is at most the global norm multiplied by `1 + ρ`. -/
theorem lpNorm_euclideanBall_le_of_memLp_volume {h : Vec3 → ℝ}
    (hh : MemLp h (ENNReal.ofReal (3 / 2 : ℝ)) volume) {ρ : ℝ} (hρ : 0 < ρ) :
    lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
      lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) volume * (1 + ρ) := by
  have hmono : eLpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
      eLpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
    eLpNorm_mono_measure h Measure.restrict_le_self
  have hnorm : lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
      lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
    rw [← toReal_eLpNorm, ← toReal_eLpNorm]
    exact ENNReal.toReal_mono hh.eLpNorm_ne_top hmono
  calc lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ))
      ≤ lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) volume := hnorm
    _ ≤ lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) volume * (1 + ρ) :=
        le_mul_of_one_le_right lpNorm_nonneg (by linarith only [hρ])

/-- A function whose support is contained in `s` and which is `L^{3/2}` on
    `s` is `L^{3/2}` with respect to the ambient Lebesgue measure, provided it
    is almost everywhere strongly measurable there. -/
theorem memLp_volume_of_memLp_restrict_of_support {h : Vec3 → ℝ} {s : Set Vec3}
    (hmeas : AEStronglyMeasurable h volume) (hsupp : Function.support h ⊆ s)
    (hh : MemLp h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict s)) :
    MemLp h (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
  rw [memLp_iff] at hh ⊢
  rwa [eLpNorm_restrict_eq_of_support_subset hmeas hsupp] at hh

/-- If `f` and `g` obey local `L^{3/2}` growth bounds with constants `C` and
    `D`, then `f + g` obeys the local growth bound with constant `C + D`. -/
theorem lpNorm_euclideanBall_growth_add {f g : Vec3 → ℝ} {C D : ℝ}
    (hfmem : ∀ ρ : ℝ, 0 < ρ → MemLp f (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)))
    (hf : ∀ ρ : ℝ, 0 < ρ → lpNorm f (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ C * (1 + ρ))
    (hg : ∀ ρ : ℝ, 0 < ρ → lpNorm g (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ D * (1 + ρ))
    {ρ : ℝ} (hρ : 0 < ρ) :
    lpNorm (f + g) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ (C + D) * (1 + ρ) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (3 / 2 : ℝ) :=
    ENNReal.one_le_ofReal.2 (by norm_num)
  calc lpNorm (f + g) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ))
      ≤ lpNorm f (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) ρ)) +
        lpNorm g (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) ρ)) :=
        lpNorm_add_le (hfmem ρ hρ) hp1
    _ ≤ C * (1 + ρ) + D * (1 + ρ) := add_le_add (hf ρ hρ) (hg ρ hρ)
    _ = (C + D) * (1 + ρ) := by ring

/-- If `f` and `g` obey local `L^{3/2}` growth bounds with constants `C` and
    `D`, then `f - g` obeys the local growth bound with constant `C + D`. -/
theorem lpNorm_euclideanBall_growth_sub {f g : Vec3 → ℝ} {C D : ℝ}
    (hfmem : ∀ ρ : ℝ, 0 < ρ → MemLp f (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)))
    (hf : ∀ ρ : ℝ, 0 < ρ → lpNorm f (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ C * (1 + ρ))
    (hg : ∀ ρ : ℝ, 0 < ρ → lpNorm g (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ D * (1 + ρ))
    {ρ : ℝ} (hρ : 0 < ρ) :
    lpNorm (f - g) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ (C + D) * (1 + ρ) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (3 / 2 : ℝ) :=
    ENNReal.one_le_ofReal.2 (by norm_num)
  calc lpNorm (f - g) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ))
      ≤ lpNorm f (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) ρ)) +
        lpNorm g (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) ρ)) :=
        lpNorm_sub_le (hfmem ρ hρ) hp1
    _ ≤ C * (1 + ρ) + D * (1 + ρ) := add_le_add (hf ρ hρ) (hg ρ hρ)
    _ = (C + D) * (1 + ρ) := by ring

/-- A finite sum of `L^{3/2}` potentials obeying local growth bounds with
    constants `C i` obeys the local growth bound with constant `∑ i ∈ s, C i`. -/
theorem lpNorm_euclideanBall_growth_sum {ι : Type*} {s : Finset ι}
    {f : ι → Vec3 → ℝ} {C : ι → ℝ}
    (hmem : ∀ i ∈ s, ∀ ρ : ℝ, 0 < ρ → MemLp (f i) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)))
    (hb : ∀ i ∈ s, ∀ ρ : ℝ, 0 < ρ → lpNorm (f i) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ C i * (1 + ρ))
    {ρ : ℝ} (hρ : 0 < ρ) :
    lpNorm (∑ i ∈ s, f i) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ (∑ i ∈ s, C i) * (1 + ρ) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (3 / 2 : ℝ) :=
    ENNReal.one_le_ofReal.2 (by norm_num)
  calc lpNorm (∑ i ∈ s, f i) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ))
      ≤ ∑ i ∈ s, lpNorm (f i) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) ρ)) :=
        lpNorm_sum_le (fun i hi => hmem i hi ρ hρ) hp1
    _ ≤ ∑ i ∈ s, C i * (1 + ρ) := Finset.sum_le_sum (fun i hi => hb i hi ρ hρ)
    _ = (∑ i ∈ s, C i) * (1 + ρ) := by rw [Finset.sum_mul]

end CKN
