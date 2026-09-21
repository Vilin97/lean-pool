/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.NormalizedLp
import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.Definitions
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Generic normalized `W^{1,p}` implementation kernel

This module implements normalized `W^{1,p}` quantities on an arbitrary
positive-finite-volume `BoundedMeasurableDomain`.  It is a reusable analytic
kernel, not the Chapter 1 source-facing carrier: Chapter 1 exposes these
operations only after restricting to its nonempty bounded open convex-domain
facade.
-/

namespace Homogenization

open scoped ENNReal

namespace W1pFunction

/-- Componentwise `L^p` control of a weak gradient gives `L^p` control of its
explicit Euclidean magnitude, after volume normalization. -/
theorem gradEuclideanMemLp {d : ℕ} (U : BoundedMeasurableDomain d) (p : ℝ≥0∞)
    (u : W1pFunction (U : Set (Vec d)) p) :
    MeasureTheory.MemLp (fun x => euclideanNorm (u.grad x)) p U.normalizedVolume := by
  have hgrad_restricted :
      MeasureTheory.MemLp (fun x => HilbertVec.ofVec (u.grad x)) p U.restrictedVolume := by
    rw [MeasureTheory.memLp_piLp_iff]
    intro i
    simpa only [Function.comp_apply, PiLp.toLp_apply,
      BoundedMeasurableDomain.restrictedVolume] using u.gradMemLp i
  have hnorm_restricted :
      MeasureTheory.MemLp (fun x => euclideanNorm (u.grad x)) p U.restrictedVolume := by
    simpa only [euclideanNorm_eq_norm_ofVec] using hgrad_restricted.norm
  exact (U.memLp_normalizedVolume_iff p _).mpr hnorm_restricted

end W1pFunction

namespace BoundedMeasurableDomain

/-- The real Lebesgue volume of a bounded measurable domain.  Its conversion
from `ℝ≥0∞` is certified by `volume_ne_top`. -/
noncomputable def volumeReal {d : ℕ} (U : BoundedMeasurableDomain d) : ℝ :=
  (MeasureTheory.volume (U : Set (Vec d))).toReal

/-- A bounded measurable domain has strictly positive real Lebesgue volume. -/
theorem volumeReal_pos {d : ℕ} (U : BoundedMeasurableDomain d) : 0 < U.volumeReal :=
  ENNReal.toReal_pos U.volume_ne_zero U.volume_ne_top

theorem volumeReal_ne_zero {d : ℕ} (U : BoundedMeasurableDomain d) : U.volumeReal ≠ 0 :=
  ne_of_gt U.volumeReal_pos

/-! ## Generic kernel

The declarations below are deliberately nested under
`BoundedMeasurableDomain.NormalizedW1pKernel`. They require only the broad
bounded-measurable positive-volume carrier and must not be presented as the
Chapter 1 source-facing domain API. -/

namespace NormalizedW1pKernel

/-- The finite-exponent normalized `W^{1,p}` seminorm in the generic kernel. -/
noncomputable def seminorm {d : ℕ} [NeZero d]
    (U : BoundedMeasurableDomain d) (p : ℝ≥0∞) (_hp_one : 1 ≤ p) (_hp_top : p ≠ ∞)
    (u : W1pFunction (U : Set (Vec d)) p) : ℝ :=
  U.normalizedEuclideanLpNorm p u.grad (u.gradEuclideanMemLp U p)

/-- Characterization of the generic finite-exponent normalized seminorm. -/
theorem seminorm_eq {d : ℕ} [NeZero d]
    (U : BoundedMeasurableDomain d) (p : ℝ≥0∞) (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : W1pFunction (U : Set (Vec d)) p) :
    seminorm U p hp_one hp_top u =
      U.normalizedEuclideanLpNorm p u.grad (u.gradEuclideanMemLp U p) :=
  rfl

/-- The generic finite-exponent seminorm is invariant under an a.e. equality
of the explicitly stored weak gradients. -/
theorem seminorm_congr_ae {d : ℕ} [NeZero d]
    (U : BoundedMeasurableDomain d) (p : ℝ≥0∞) (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    (u v : W1pFunction (U : Set (Vec d)) p)
    (hgrad : u.grad =ᵐ[U.normalizedVolume] v.grad) :
    seminorm U p hp_one hp_top u = seminorm U p hp_one hp_top v := by
  unfold seminorm
  exact U.normalizedEuclideanLpNorm_congr_ae p (u.gradEuclideanMemLp U p)
    (v.gradEuclideanMemLp U p) hgrad

/-- The generic finite-exponent normalized `W^{1,p}` norm:
`(‖∇u‖^p + |U|^(-p/d) ‖u‖^p)^(1/p)`. -/
noncomputable def norm {d : ℕ} [NeZero d]
    (U : BoundedMeasurableDomain d) (p : ℝ≥0∞) (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : W1pFunction (U : Set (Vec d)) p) : ℝ :=
  (seminorm U p hp_one hp_top u ^ p.toReal +
    U.volumeReal ^ (-(p.toReal / (d : ℝ))) *
      U.normalizedLpNorm p u.toFun
        ((U.memLp_normalizedVolume_iff p _).mpr u.memLp) ^ p.toReal) ^
    p.toReal⁻¹

/-- Characterization of the generic finite-exponent normalized norm. -/
theorem norm_eq {d : ℕ} [NeZero d]
    (U : BoundedMeasurableDomain d) (p : ℝ≥0∞) (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : W1pFunction (U : Set (Vec d)) p) :
    norm U p hp_one hp_top u =
      (seminorm U p hp_one hp_top u ^ p.toReal +
        U.volumeReal ^ (-(p.toReal / (d : ℝ))) *
          U.normalizedLpNorm p u.toFun
            ((U.memLp_normalizedVolume_iff p _).mpr u.memLp) ^ p.toReal) ^ p.toReal⁻¹ :=
  rfl

/-- The generic finite-exponent normalized norm is invariant under separate
a.e. equalities of the function and its explicitly stored weak gradient. -/
theorem norm_congr_ae {d : ℕ} [NeZero d]
    (U : BoundedMeasurableDomain d) (p : ℝ≥0∞) (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    (u v : W1pFunction (U : Set (Vec d)) p)
    (hfun : u.toFun =ᵐ[U.normalizedVolume] v.toFun)
    (hgrad : u.grad =ᵐ[U.normalizedVolume] v.grad) :
    norm U p hp_one hp_top u = norm U p hp_one hp_top v := by
  unfold norm
  rw [seminorm_congr_ae U p hp_one hp_top u v hgrad,
    U.normalizedLpNorm_congr_ae p
      ((U.memLp_normalizedVolume_iff p _).mpr u.memLp)
      ((U.memLp_normalizedVolume_iff p _).mpr v.memLp) hfun]

/-- The generic normalized `W^{1,∞}` seminorm of a weak Sobolev witness. -/
noncomputable def seminormTop {d : ℕ} [NeZero d]
    (U : BoundedMeasurableDomain d) (u : W1pFunction (U : Set (Vec d)) ∞) : ℝ :=
  U.normalizedEuclideanLpNorm ∞ u.grad (u.gradEuclideanMemLp U ∞)

/-- Characterization of the generic normalized `W^{1,∞}` seminorm. -/
theorem seminormTop_eq {d : ℕ} [NeZero d]
    (U : BoundedMeasurableDomain d) (u : W1pFunction (U : Set (Vec d)) ∞) :
    seminormTop U u =
      U.normalizedEuclideanLpNorm ∞ u.grad (u.gradEuclideanMemLp U ∞) :=
  rfl

/-- The generic endpoint seminorm is invariant under an a.e. equality of the
explicitly stored weak gradients. -/
theorem seminormTop_congr_ae {d : ℕ} [NeZero d]
    (U : BoundedMeasurableDomain d) (u v : W1pFunction (U : Set (Vec d)) ∞)
    (hgrad : u.grad =ᵐ[U.normalizedVolume] v.grad) :
    seminormTop U u = seminormTop U v := by
  unfold seminormTop
  exact U.normalizedEuclideanLpNorm_congr_ae ∞ (u.gradEuclideanMemLp U ∞)
    (v.gradEuclideanMemLp U ∞) hgrad

/-- The generic endpoint normalized `W^{1,∞}` norm.  The two terms are added,
rather than combined using a maximum. -/
noncomputable def normTop {d : ℕ} [NeZero d]
    (U : BoundedMeasurableDomain d) (u : W1pFunction (U : Set (Vec d)) ∞) : ℝ :=
  seminormTop U u + U.volumeReal ^ (-(1 / (d : ℝ))) *
    U.normalizedLpNorm ∞ u.toFun ((U.memLp_normalizedVolume_iff ∞ _).mpr u.memLp)

/-- Characterization of the generic endpoint normalized norm. -/
theorem normTop_eq {d : ℕ} [NeZero d]
    (U : BoundedMeasurableDomain d) (u : W1pFunction (U : Set (Vec d)) ∞) :
    normTop U u =
      seminormTop U u + U.volumeReal ^ (-(1 / (d : ℝ))) *
        U.normalizedLpNorm ∞ u.toFun
          ((U.memLp_normalizedVolume_iff ∞ _).mpr u.memLp) :=
  rfl

/-- The generic endpoint normalized norm is invariant under separate a.e.
equalities of the function and its explicitly stored weak gradient. -/
theorem normTop_congr_ae {d : ℕ} [NeZero d]
    (U : BoundedMeasurableDomain d) (u v : W1pFunction (U : Set (Vec d)) ∞)
    (hfun : u.toFun =ᵐ[U.normalizedVolume] v.toFun)
    (hgrad : u.grad =ᵐ[U.normalizedVolume] v.grad) :
    normTop U u = normTop U v := by
  unfold normTop
  rw [seminormTop_congr_ae U u v hgrad,
    U.normalizedLpNorm_congr_ae ∞
      ((U.memLp_normalizedVolume_iff ∞ _).mpr u.memLp)
      ((U.memLp_normalizedVolume_iff ∞ _).mpr v.memLp) hfun]

end NormalizedW1pKernel

end BoundedMeasurableDomain

end Homogenization
