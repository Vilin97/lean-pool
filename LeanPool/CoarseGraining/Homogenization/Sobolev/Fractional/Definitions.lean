/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import LeanPool.CoarseGraining.Homogenization.Multiscale.NormalizedNorms

/-!
# Fractional Sobolev (Gagliardo) seminorms on triadic cubes

This file defines the volume-normalized fractional Sobolev seminorm
`[u]_{W̲^{s,p}(□)}` of the manuscript (CG Chapter 1, "Fractional Sobolev
seminorms") as an `eLpNorm` of a difference-quotient kernel over a product
measure, together with the membership predicate `MemWsp` playing the role of
`u ∈ W^{s,p}(□)`.

Design notes:

* The kernel uses the ambient `Vec d` sup-norm distance, which differs from
  the manuscript's Euclidean distance by a factor absorbed into dimensional
  constants (uniformly in `s, p`, since the kernel exponent `s + d/p` is at
  most `d + 1` on the manuscript range `s < 1 ≤ p`).
* The manuscript's `⨍∫` normalization is carried by the product measure
  `gagliardoCubeMeasure` (normalized in the first slot, plain in the second),
  not by an ad-hoc volume prefactor.
* At `p = ∞` the kernel exponent `s + d / p.toReal` collapses to `s`
  (junk-value `d / 0 = 0`), so the seminorm degenerates to the essential
  Hölder `C^{0,s}` seminorm, matching the manuscript's
  `[·]_{C^{0,s}} ≈ [·]_{W̲^{s,∞}}` convention.
* Consumers must not unfold the definitions: the lemmas in the `Internal`
  namespace are reserved for the comparison proof files.  Everything else
  goes through the exported API.
-/

namespace Homogenization
namespace Gagliardo

noncomputable section

open MeasureTheory
open scoped ENNReal

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The kernel exponent `s + d/p`.  At `p = ∞` it collapses to `s`. -/
def kernelExponent (d : ℕ) (s : ℝ) (p : ℝ≥0∞) : ℝ :=
  s + (d : ℝ) / p.toReal

theorem kernelExponent_top (d : ℕ) (s : ℝ) :
    kernelExponent d s ∞ = s := by
  simp [kernelExponent]

/-- Difference-quotient kernel of the fractional Sobolev seminorm. -/
noncomputable def gagliardoKernel (s : ℝ) (p : ℝ≥0∞) (u : Vec d → E) :
    Vec d × Vec d → E :=
  fun z => (dist z.1 z.2 ^ (-kernelExponent d s p)) • (u z.1 - u z.2)

theorem gagliardoKernel_apply (s : ℝ) (p : ℝ≥0∞) (u : Vec d → E)
    (z : Vec d × Vec d) :
    gagliardoKernel s p u z =
      (dist z.1 z.2 ^ (-kernelExponent d s p)) • (u z.1 - u z.2) := rfl

theorem gagliardoKernel_zero (s : ℝ) (p : ℝ≥0∞) :
    gagliardoKernel s p (0 : Vec d → E) = 0 := by
  funext z
  simp [gagliardoKernel]

theorem gagliardoKernel_add (s : ℝ) (p : ℝ≥0∞) (u v : Vec d → E) :
    gagliardoKernel s p (u + v) =
      gagliardoKernel s p u + gagliardoKernel s p v := by
  funext z
  simp only [gagliardoKernel, Pi.add_apply]
  rw [show u z.1 + v z.1 - (u z.2 + v z.2)
      = (u z.1 - u z.2) + (v z.1 - v z.2) by abel, smul_add]

theorem gagliardoKernel_neg (s : ℝ) (p : ℝ≥0∞) (u : Vec d → E) :
    gagliardoKernel s p (-u) = -gagliardoKernel s p u := by
  funext z
  simp only [gagliardoKernel, Pi.neg_apply]
  rw [show -u z.1 - -u z.2 = -(u z.1 - u z.2) by abel, smul_neg]

theorem gagliardoKernel_smul (s : ℝ) (p : ℝ≥0∞) (c : ℝ) (u : Vec d → E) :
    gagliardoKernel s p (c • u) = c • gagliardoKernel s p u := by
  funext z
  simp only [gagliardoKernel, Pi.smul_apply]
  rw [← smul_sub, smul_smul, smul_smul, mul_comm]

/-- The manuscript's `⨍_□ ∫_□` normalization as a product measure:
normalized in the first variable, plain restricted volume in the second. -/
noncomputable def gagliardoCubeMeasure (Q : TriadicCube d) :
    Measure (Vec d × Vec d) :=
  (normalizedCubeMeasure Q).prod (cubeMeasure Q)

instance instIsFiniteMeasureGagliardoCubeMeasure (Q : TriadicCube d) :
    IsFiniteMeasure (gagliardoCubeMeasure Q) := by
  have : IsFiniteMeasure (cubeMeasure Q) :=
    ⟨lt_top_iff_ne_top.2 (cubeMeasure_apply_univ_ne_top Q)⟩
  have : SFinite (cubeMeasure Q) := by
    unfold cubeMeasure
    infer_instance
  unfold gagliardoCubeMeasure
  infer_instance

instance instSFiniteGagliardoCubeMeasure (Q : TriadicCube d) :
    SFinite (gagliardoCubeMeasure Q) := by
  have : SFinite (cubeMeasure Q) := by
    unfold cubeMeasure
    infer_instance
  unfold gagliardoCubeMeasure
  infer_instance

/-- The integral seminorm, including nonmeasurable functions, with the essential
supremum at infinity. This keeps the manuscript's integral definition independent
of the measurability convention in Mathlib's `eLpNorm`. -/
def integralLpSeminorm {α : Type*} [MeasurableSpace α]
    (f : α → E) (p : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  if p = 0 then 0 else if p = ∞ then eLpNormEssSup f μ else eLpNorm' f p.toReal μ

/-- For measurable functions the integral seminorm agrees with Mathlib's norm. -/
theorem integralLpSeminorm_eq_eLpNorm {α : Type*} [MeasurableSpace α]
    (f : α → E) (p : ℝ≥0∞) (μ : Measure α) (hf : AEStronglyMeasurable f μ) :
    integralLpSeminorm f p μ = eLpNorm f p μ := by
  simp only [integralLpSeminorm, eLpNorm, if_pos hf]

/-- `[u]_{W̲^{s,p}(Q)}`, ℝ≥0∞-valued, defined for all `p ∈ [1,∞]`
(`p = ∞` gives the essential Hölder seminorm). -/
noncomputable def cubeGagliardoESeminorm (Q : TriadicCube d) (s : ℝ)
    (p : ℝ≥0∞) (u : Vec d → E) : ℝ≥0∞ :=
  integralLpSeminorm (gagliardoKernel s p u) p (gagliardoCubeMeasure Q)

/-- Real-valued fractional Sobolev seminorm (junk value `0` when infinite). -/
noncomputable def cubeGagliardoSeminorm (Q : TriadicCube d) (s : ℝ)
    (p : ℝ≥0∞) (u : Vec d → E) : ℝ :=
  (cubeGagliardoESeminorm Q s p u).toReal

/-- Unnormalized fractional Sobolev seminorm over an arbitrary set. -/
noncomputable def gagliardoESeminormOn (A : Set (Vec d)) (s : ℝ)
    (p : ℝ≥0∞) (u : Vec d → E) : ℝ≥0∞ :=
  integralLpSeminorm (gagliardoKernel s p u) p
    ((MeasureTheory.volume.restrict A).prod (MeasureTheory.volume.restrict A))

/-- `u ∈ W^{s,p}(Q)`: the membership predicate, mirroring `MemLp`. -/
def MemWsp (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → E) : Prop :=
  MemLp (gagliardoKernel s p u) p (gagliardoCubeMeasure Q)

namespace Internal

/-- Unfolding lemma, reserved for the comparison proof files. -/
theorem cubeGagliardoESeminorm_def (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞)
    (u : Vec d → E)
    (hu : AEStronglyMeasurable (gagliardoKernel s p u) (gagliardoCubeMeasure Q)) :
    cubeGagliardoESeminorm Q s p u =
      eLpNorm (gagliardoKernel s p u) p (gagliardoCubeMeasure Q) :=
  integralLpSeminorm_eq_eLpNorm _ _ _ hu

/-- Finite-`p` lintegral form, reserved for the comparison proof files. -/
theorem cubeGagliardoESeminorm_eq_lintegral {Q : TriadicCube d} {s : ℝ}
    {p : ℝ≥0∞} {u : Vec d → E} (hp0 : p ≠ 0) (hpt : p ≠ ∞) :
    cubeGagliardoESeminorm Q s p u =
      (∫⁻ z, ‖gagliardoKernel s p u z‖ₑ ^ p.toReal
        ∂gagliardoCubeMeasure Q) ^ (1 / p.toReal) := by
  simp only [cubeGagliardoESeminorm, integralLpSeminorm, if_neg hp0, if_neg hpt]
  exact eLpNorm'_eq_lintegral_enorm (gagliardoKernel s p u) _ _

end Internal

theorem MemWsp.aestronglyMeasurable {Q : TriadicCube d} {s : ℝ} {p : ℝ≥0∞}
    {u : Vec d → E} (h : MemWsp Q s p u) :
    AEStronglyMeasurable (gagliardoKernel s p u) (gagliardoCubeMeasure Q) :=
  MemLp.aestronglyMeasurable h

theorem MemWsp.eSeminorm_lt_top {Q : TriadicCube d} {s : ℝ} {p : ℝ≥0∞}
    {u : Vec d → E} (h : MemWsp Q s p u) :
    cubeGagliardoESeminorm Q s p u < ∞ := by
  rw [Internal.cubeGagliardoESeminorm_def _ _ _ _ h.aestronglyMeasurable]
  exact MemLp.eLpNorm_lt_top h

theorem memWsp_iff {Q : TriadicCube d} {s : ℝ} {p : ℝ≥0∞} {u : Vec d → E} :
    MemWsp Q s p u ↔
      AEStronglyMeasurable (gagliardoKernel s p u) (gagliardoCubeMeasure Q) ∧
        cubeGagliardoESeminorm Q s p u < ∞ := by
  constructor
  · intro h
    exact ⟨h.aestronglyMeasurable, h.eSeminorm_lt_top⟩
  · rintro ⟨hmeas, hfinite⟩
    rw [Internal.cubeGagliardoESeminorm_def _ _ _ _ hmeas] at hfinite
    exact hfinite

theorem MemWsp.add {Q : TriadicCube d} {s : ℝ} {p : ℝ≥0∞} {u v : Vec d → E}
    (hu : MemWsp Q s p u) (hv : MemWsp Q s p v) :
    MemWsp Q s p (u + v) := by
  show MemLp (gagliardoKernel s p (u + v)) p (gagliardoCubeMeasure Q)
  rw [gagliardoKernel_add]
  exact MemLp.add hu hv

theorem MemWsp.neg {Q : TriadicCube d} {s : ℝ} {p : ℝ≥0∞} {u : Vec d → E}
    (hu : MemWsp Q s p u) :
    MemWsp Q s p (-u) := by
  show MemLp (gagliardoKernel s p (-u)) p (gagliardoCubeMeasure Q)
  rw [gagliardoKernel_neg]
  exact MemLp.neg hu

theorem MemWsp.smul {Q : TriadicCube d} {s : ℝ} {p : ℝ≥0∞} {u : Vec d → E}
    (c : ℝ) (hu : MemWsp Q s p u) :
    MemWsp Q s p (c • u) := by
  show MemLp (gagliardoKernel s p (c • u)) p (gagliardoCubeMeasure Q)
  rw [gagliardoKernel_smul]
  exact MemLp.const_smul hu c

theorem cubeGagliardoESeminorm_zero (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) :
    cubeGagliardoESeminorm Q s p (0 : Vec d → E) = 0 := by
  simp only [cubeGagliardoESeminorm, gagliardoKernel_zero]
  rw [integralLpSeminorm_eq_eLpNorm _ _ _ aestronglyMeasurable_zero]
  exact eLpNorm_zero

theorem cubeGagliardoESeminorm_neg (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞)
    (u : Vec d → E) :
    cubeGagliardoESeminorm Q s p (-u) = cubeGagliardoESeminorm Q s p u := by
  simp only [cubeGagliardoESeminorm, gagliardoKernel_neg, integralLpSeminorm,
    eLpNormEssSup_eq_essSup_enorm, Pi.neg_apply, enorm_neg, eLpNorm'_neg]

theorem cubeGagliardoESeminorm_const_smul (Q : TriadicCube d) (s : ℝ)
    (p : ℝ≥0∞) (c : ℝ) (u : Vec d → E) :
    cubeGagliardoESeminorm Q s p (c • u) =
      ‖c‖ₑ * cubeGagliardoESeminorm Q s p u := by
  by_cases hp0 : p = 0
  · simp [cubeGagliardoESeminorm, integralLpSeminorm, hp0]
  by_cases hpt : p = ∞
  · simp only [cubeGagliardoESeminorm, gagliardoKernel_smul, integralLpSeminorm,
      if_neg hp0, if_pos hpt]
    exact eLpNormEssSup_const_smul _ _
  · simp only [cubeGagliardoESeminorm, gagliardoKernel_smul, integralLpSeminorm,
      if_neg hp0, if_neg hpt]
    exact eLpNorm'_const_smul c (ENNReal.toReal_pos hp0 hpt)

/-- Triangle inequality for the fractional Sobolev seminorm. -/
theorem cubeGagliardoESeminorm_add_le {Q : TriadicCube d} {s : ℝ} {p : ℝ≥0∞}
    {u v : Vec d → E} (hp : 1 ≤ p) (hu : MemWsp Q s p u) (hv : MemWsp Q s p v) :
    cubeGagliardoESeminorm Q s p (u + v) ≤
      cubeGagliardoESeminorm Q s p u + cubeGagliardoESeminorm Q s p v := by
  rw [Internal.cubeGagliardoESeminorm_def _ _ _ _ (hu.add hv).aestronglyMeasurable,
    Internal.cubeGagliardoESeminorm_def _ _ _ _ hu.aestronglyMeasurable,
    Internal.cubeGagliardoESeminorm_def _ _ _ _ hv.aestronglyMeasurable,
    gagliardoKernel_add]
  exact eLpNorm_add_le hp

theorem cubeGagliardoSeminorm_nonneg (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞)
    (u : Vec d → E) :
    0 ≤ cubeGagliardoSeminorm Q s p u :=
  ENNReal.toReal_nonneg

end

end Gagliardo
end Homogenization
