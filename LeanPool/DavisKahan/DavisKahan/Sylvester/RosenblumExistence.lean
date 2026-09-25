/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.CircleRieszEndpoints
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Operator

/-!
# Rosenblum's theorem: solving the Sylvester equation

Sylvester--Rosenblum has two halves.  The uniqueness half — a bounded
intertwiner between operators with disjoint spectra vanishes — is proved
elsewhere in this development
(`DavisKahan.Sylvester.PairwiseHomogeneousUniqueness`).  This file supplies the
existence half, which was missing: if a circle separates the spectrum of `A`
from the spectrum of `B`, then

`S := (2 π i)⁻¹ ∮ (z - A)⁻¹ C (z - B)⁻¹ dz`

solves `A S - S B = C`.

## The one identity everything runs on

Off both spectra, write `R := (z - A)⁻¹` and `T := (z - B)⁻¹`.  From
`(z - A) R = 1` and `T (z - B) = 1` we get `A R = z R - 1` and `T B = z T - 1`,
and the `z`-terms cancel in

`A (R C T) - (R C T) B = (z R - 1) C T - R C (z T - 1) = R C - C T`.

Integrating over the circle turns the right-hand side into
`P_A C - C P_B`, where `P_A` and `P_B` are the Riesz projections of the two
operators for that circle.  With the circle chosen around `spectrum A` and away
from `spectrum B` these are `1` and `0`, and the result is `C`.

The same identity, read with the roles of the data and the unknown exchanged,
gives uniqueness: `R (A X - X B) T = R X - X T` integrates to `P_A X - X P_B`,
so `rosenblumSolution` recovers any `X` from `A X - X B`.  Existence and
uniqueness are therefore the *same* computation, and the Sylvester operator is
a bijection (`existsUnique_comp_sub_comp_eq`).

Both endpoints come from `DavisKahan.SpectralTheory.CircleRieszEndpoints` and
need no self-adjointness, so the results here hold for arbitrary bounded
operators.
-/

@[expose] public section

open Metric Set Filter Complex ContinuousLinearMap
open scoped Topology

namespace TauCeti
namespace DavisKahan

universe u

variable {E F : Type u}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

section Definitions

/-- The Rosenblum integrand `(z - A)⁻¹ C (z - B)⁻¹`. -/
noncomputable def rosenblumIntegrand (A : E →L[ℂ] E) (B : F →L[ℂ] F)
    (C : F →L[ℂ] E) (z : ℂ) : F →L[ℂ] E :=
  Ring.inverse (z • (1 : E →L[ℂ] E) - A) ∘L C ∘L
    Ring.inverse (z • (1 : F →L[ℂ] F) - B)

/-- Rosenblum's contour solution of the Sylvester equation `A S - S B = C`. -/
noncomputable def rosenblumSolution (A : E →L[ℂ] E) (B : F →L[ℂ] F)
    (C : F →L[ℂ] E) (center radius : ℝ) : F →L[ℂ] E :=
  (2 * Real.pi * Complex.I)⁻¹ •
    ∮ z in C((center : ℂ), radius), rosenblumIntegrand A B C z

end Definitions

section PencilAlgebra

variable {A : E →L[ℂ] E} {B : F →L[ℂ] F} {z : ℂ}

omit [CompleteSpace E] in
/-- `A (z - A)⁻¹ = z (z - A)⁻¹ - 1`. -/
theorem comp_ringInverse_eq (hA : z ∉ spectrum ℂ A) :
    A ∘L Ring.inverse (z • (1 : E →L[ℂ] E) - A) =
      z • Ring.inverse (z • (1 : E →L[ℂ] E) - A) - 1 := by
  have h : (z • (1 : E →L[ℂ] E) - A) * Ring.inverse (z • (1 : E →L[ℂ] E) - A) = 1 :=
    Ring.mul_inverse_cancel _ (isUnit_smul_one_sub_of_notMem_spectrum hA)
  rw [sub_mul, smul_mul_assoc, one_mul] at h
  rw [← ContinuousLinearMap.mul_def, eq_sub_iff_add_eq, sub_eq_iff_eq_add.mp h]
  exact add_comm _ _

omit [CompleteSpace E] in
/-- `(z - A)⁻¹ A = z (z - A)⁻¹ - 1`. -/
theorem ringInverse_comp_eq (hA : z ∉ spectrum ℂ A) :
    Ring.inverse (z • (1 : E →L[ℂ] E) - A) ∘L A =
      z • Ring.inverse (z • (1 : E →L[ℂ] E) - A) - 1 := by
  have h : Ring.inverse (z • (1 : E →L[ℂ] E) - A) * (z • (1 : E →L[ℂ] E) - A) = 1 :=
    Ring.inverse_mul_cancel _ (isUnit_smul_one_sub_of_notMem_spectrum hA)
  rw [mul_sub, mul_smul_comm, mul_one] at h
  rw [← ContinuousLinearMap.mul_def, eq_sub_iff_add_eq, sub_eq_iff_eq_add.mp h]
  exact add_comm _ _

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The Rosenblum identity, existence form.**  Applying the Sylvester
operator to the integrand collapses it to a difference of one-sided resolvent
terms; the `z`-dependent parts cancel. -/
theorem comp_rosenblumIntegrand_sub_comp (C : F →L[ℂ] E)
    (hA : z ∉ spectrum ℂ A) (hB : z ∉ spectrum ℂ B) :
    A ∘L rosenblumIntegrand A B C z - rosenblumIntegrand A B C z ∘L B =
      Ring.inverse (z • (1 : E →L[ℂ] E) - A) ∘L C -
        C ∘L Ring.inverse (z • (1 : F →L[ℂ] F) - B) := by
  have hSB : Ring.inverse (z • (1 : F →L[ℂ] F) - B) ∘L B =
      z • Ring.inverse (z • (1 : F →L[ℂ] F) - B) - 1 := ringInverse_comp_eq hB
  rw [rosenblumIntegrand]
  calc A ∘L (Ring.inverse (z • (1 : E →L[ℂ] E) - A) ∘L
          (C ∘L Ring.inverse (z • (1 : F →L[ℂ] F) - B))) -
        (Ring.inverse (z • (1 : E →L[ℂ] E) - A) ∘L
          (C ∘L Ring.inverse (z • (1 : F →L[ℂ] F) - B))) ∘L B
      = (A ∘L Ring.inverse (z • (1 : E →L[ℂ] E) - A)) ∘L
            (C ∘L Ring.inverse (z • (1 : F →L[ℂ] F) - B)) -
          Ring.inverse (z • (1 : E →L[ℂ] E) - A) ∘L
            (C ∘L (Ring.inverse (z • (1 : F →L[ℂ] F) - B) ∘L B)) := by
        simp only [ContinuousLinearMap.comp_assoc]
    _ = (z • Ring.inverse (z • (1 : E →L[ℂ] E) - A) - 1) ∘L
            (C ∘L Ring.inverse (z • (1 : F →L[ℂ] F) - B)) -
          Ring.inverse (z • (1 : E →L[ℂ] E) - A) ∘L
            (C ∘L (z • Ring.inverse (z • (1 : F →L[ℂ] F) - B) - 1)) := by
        rw [comp_ringInverse_eq hA, hSB]
    _ = Ring.inverse (z • (1 : E →L[ℂ] E) - A) ∘L C -
          C ∘L Ring.inverse (z • (1 : F →L[ℂ] F) - B) := by
        simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
          ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
          ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
          ContinuousLinearMap.comp_id]
        abel

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The Rosenblum identity, uniqueness form.**  Feeding `A X - X B` to the
integrand recovers the same one-sided difference, now in `X`. -/
theorem rosenblumIntegrand_comp_sub (X : F →L[ℂ] E)
    (hA : z ∉ spectrum ℂ A) (hB : z ∉ spectrum ℂ B) :
    rosenblumIntegrand A B (A ∘L X - X ∘L B) z =
      Ring.inverse (z • (1 : E →L[ℂ] E) - A) ∘L X -
        X ∘L Ring.inverse (z • (1 : F →L[ℂ] F) - B) := by
  have hBS : B ∘L Ring.inverse (z • (1 : F →L[ℂ] F) - B) =
      z • Ring.inverse (z • (1 : F →L[ℂ] F) - B) - 1 := comp_ringInverse_eq hB
  rw [rosenblumIntegrand]
  calc Ring.inverse (z • (1 : E →L[ℂ] E) - A) ∘L
        ((A ∘L X - X ∘L B) ∘L Ring.inverse (z • (1 : F →L[ℂ] F) - B))
      = (Ring.inverse (z • (1 : E →L[ℂ] E) - A) ∘L A) ∘L
            (X ∘L Ring.inverse (z • (1 : F →L[ℂ] F) - B)) -
          Ring.inverse (z • (1 : E →L[ℂ] E) - A) ∘L
            (X ∘L (B ∘L Ring.inverse (z • (1 : F →L[ℂ] F) - B))) := by
        simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
          ContinuousLinearMap.comp_assoc]
    _ = (z • Ring.inverse (z • (1 : E →L[ℂ] E) - A) - 1) ∘L
            (X ∘L Ring.inverse (z • (1 : F →L[ℂ] F) - B)) -
          Ring.inverse (z • (1 : E →L[ℂ] E) - A) ∘L
            (X ∘L (z • Ring.inverse (z • (1 : F →L[ℂ] F) - B) - 1)) := by
        rw [ringInverse_comp_eq hA, hBS]
    _ = Ring.inverse (z • (1 : E →L[ℂ] E) - A) ∘L X -
          X ∘L Ring.inverse (z • (1 : F →L[ℂ] F) - B) := by
        simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
          ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
          ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
          ContinuousLinearMap.comp_id]
        abel

end PencilAlgebra

section Integration

/-- A continuous linear map passes through a circle integral. -/
private theorem circleIntegral_map {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [CompleteSpace Y] (L : X →L[ℂ] Y) (f : ℂ → X) (c : ℂ) (R : ℝ)
    (hf : CircleIntegrable f c R) :
    (∮ z in C(c, R), L (f z)) = L (∮ z in C(c, R), f z) := by
  simp only [circleIntegral]
  rw [show (fun θ : ℝ => deriv (circleMap c R) θ • L (f (circleMap c R θ))) =
      fun θ : ℝ => L (deriv (circleMap c R) θ • f (circleMap c R θ)) from
    funext fun θ => (L.map_smul _ _).symm]
  exact L.intervalIntegral_comp_comm ((circleIntegrable_iff R).mp hf)

/-- A continuous linear map preserves circle integrability. -/
private theorem circleIntegrable_map {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y] (L : X →L[ℂ] Y)
    {f : ℂ → X} {c : ℂ} {R : ℝ} (hf : CircleIntegrable f c R) :
    CircleIntegrable (fun z => L (f z)) c R :=
  ⟨L.integrable_comp hf.1, L.integrable_comp hf.2⟩

variable (A : E →L[ℂ] E) (B : F →L[ℂ] F) {center radius : ℝ}

omit [CompleteSpace F] in
/-- Post-composition passes through a circle integral. -/
private theorem comp_circleIntegral (L : E →L[ℂ] E) (f : ℂ → F →L[ℂ] E) (c : ℂ)
    (R : ℝ) (hf : CircleIntegrable f c R) :
    L ∘L (∮ z in C(c, R), f z) = ∮ z in C(c, R), L ∘L f z := by
  simpa using (circleIntegral_map (ContinuousLinearMap.compL ℂ F E E L) f c R hf).symm

omit [CompleteSpace F] in
/-- Pre-composition passes through a circle integral. -/
private theorem circleIntegral_comp (M : F →L[ℂ] F) (f : ℂ → F →L[ℂ] E) (c : ℂ)
    (R : ℝ) (hf : CircleIntegrable f c R) :
    (∮ z in C(c, R), f z) ∘L M = ∮ z in C(c, R), f z ∘L M := by
  simpa using
    (circleIntegral_map ((ContinuousLinearMap.compL ℂ F F E).flip M) f c R hf).symm

/-- The resolvent of a bounded operator is circle integrable around a circle
avoiding its spectrum. -/
theorem circleIntegrable_ringInverse (hr : 0 ≤ radius)
    (hA : ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius → z ∉ spectrum ℂ A) :
    CircleIntegrable
      (fun z : ℂ => Ring.inverse (z • (1 : E →L[ℂ] E) - A)) (center : ℂ) radius := by
  refine ContinuousOn.circleIntegrable hr fun z hz => ?_
  rw [mem_sphere, dist_eq_norm] at hz
  exact (differentiableAt_ringInverse_smul_one_sub A
    (hA z hz)).continuousAt.continuousWithinAt

/-- The Rosenblum integrand is circle-integrable, which is what makes the contour integral defining
the solution well-posed. -/
theorem circleIntegrable_rosenblumIntegrand (C : F →L[ℂ] E) (hr : 0 ≤ radius)
    (hA : ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius → z ∉ spectrum ℂ A)
    (hB : ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius → z ∉ spectrum ℂ B) :
    CircleIntegrable (rosenblumIntegrand A B C) (center : ℂ) radius := by
  refine ContinuousOn.circleIntegrable hr fun z hz => ?_
  rw [mem_sphere, dist_eq_norm] at hz
  have h1 := (differentiableAt_ringInverse_smul_one_sub A (hA z hz)).continuousAt
  have h2 := (differentiableAt_ringInverse_smul_one_sub B (hB z hz)).continuousAt
  exact (h1.clm_comp (continuousAt_const.clm_comp h2)).continuousWithinAt

/-- **The integrated identity.**  The one-sided resolvent difference integrates
to the difference of the two Riesz projections.  This is the single step shared
by existence and uniqueness. -/
theorem circleIntegral_resolvent_sub (C : F →L[ℂ] E) (hr : 0 ≤ radius)
    (hA : ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius → z ∉ spectrum ℂ A)
    (hB : ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius → z ∉ spectrum ℂ B) :
    (2 * Real.pi * Complex.I)⁻¹ •
        ∮ z in C((center : ℂ), radius),
          (Ring.inverse (z • (1 : E →L[ℂ] E) - A) ∘L C -
            C ∘L Ring.inverse (z • (1 : F →L[ℂ] F) - B)) =
      circleRieszProjection A center radius ∘L C -
        C ∘L circleRieszProjection B center radius := by
  have hLA : CircleIntegrable
      (fun z : ℂ => Ring.inverse (z • (1 : E →L[ℂ] E) - A) ∘L C)
      (center : ℂ) radius := by
    refine ContinuousOn.circleIntegrable hr fun z hz => ?_
    rw [mem_sphere, dist_eq_norm] at hz
    exact ((differentiableAt_ringInverse_smul_one_sub A
      (hA z hz)).continuousAt.clm_comp continuousAt_const).continuousWithinAt
  have hLB : CircleIntegrable
      (fun z : ℂ => C ∘L Ring.inverse (z • (1 : F →L[ℂ] F) - B))
      (center : ℂ) radius := by
    refine ContinuousOn.circleIntegrable hr fun z hz => ?_
    rw [mem_sphere, dist_eq_norm] at hz
    exact (continuousAt_const.clm_comp (differentiableAt_ringInverse_smul_one_sub B
      (hB z hz)).continuousAt).continuousWithinAt
  have hmapA : (∮ z in C((center : ℂ), radius),
      Ring.inverse (z • (1 : E →L[ℂ] E) - A) ∘L C) =
      (∮ z in C((center : ℂ), radius),
        Ring.inverse (z • (1 : E →L[ℂ] E) - A)) ∘L C :=
    circleIntegral_map ((ContinuousLinearMap.compL ℂ F E E).flip C) _ _ _
      (circleIntegrable_ringInverse A hr hA)
  have hmapB : (∮ z in C((center : ℂ), radius),
      C ∘L Ring.inverse (z • (1 : F →L[ℂ] F) - B)) =
      C ∘L ∮ z in C((center : ℂ), radius),
        Ring.inverse (z • (1 : F →L[ℂ] F) - B) :=
    circleIntegral_map (ContinuousLinearMap.compL ℂ F F E C) _ _ _
      (circleIntegrable_ringInverse B hr hB)
  simp only [circleIntegral.integral_sub hLA hLB, hmapA, hmapB, smul_sub,
    circleRieszProjection, circleRieszProjection,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

end Integration

section Main

omit [CompleteSpace E] in
/-- **A spectrum inside the open ball misses the circle.**

Derived identically in both Rosenblum identities below. -/
private theorem notMem_spectrum_of_norm_eq_radius {S : E →L[ℂ] E} {center radius : ℝ}
    (hS : spectrum ℂ S ⊆ ball ((center : ℂ)) radius) :
    ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius → z ∉ spectrum ℂ S := by
  intro z hz hmem
  have hb := hS hmem
  rw [mem_ball, dist_eq_norm, hz] at hb
  exact absurd hb (lt_irrefl _)

variable (A : E →L[ℂ] E) (B : F →L[ℂ] F) (C : F →L[ℂ] E) {center radius : ℝ}

/-- The Sylvester operator applied to the Rosenblum solution, before the two
Riesz projections are evaluated. -/
theorem comp_rosenblumSolution_sub_comp (hr : 0 ≤ radius)
    (hA : ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius → z ∉ spectrum ℂ A)
    (hB : ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius → z ∉ spectrum ℂ B) :
    A ∘L rosenblumSolution A B C center radius -
        rosenblumSolution A B C center radius ∘L B =
      circleRieszProjection A center radius ∘L C -
        C ∘L circleRieszProjection B center radius := by
  have hint := circleIntegrable_rosenblumIntegrand A B C hr hA hB
  have hAint : CircleIntegrable (fun z => A ∘L rosenblumIntegrand A B C z)
      (center : ℂ) radius := by
    simpa using circleIntegrable_map (ContinuousLinearMap.compL ℂ F E E A) hint
  have hBint : CircleIntegrable (fun z => rosenblumIntegrand A B C z ∘L B)
      (center : ℂ) radius := by
    simpa using
      circleIntegrable_map ((ContinuousLinearMap.compL ℂ F F E).flip B) hint
  simp only [rosenblumSolution, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.smul_comp, ← smul_sub,
    comp_circleIntegral A _ _ _ hint, circleIntegral_comp B _ _ _ hint,
    ← circleIntegral.integral_sub hAint hBint,
    ← circleIntegral_resolvent_sub A B C hr hA hB]
  exact congrArg _ (circleIntegral.integral_congr hr fun z hz => by
    rw [mem_sphere, dist_eq_norm] at hz
    exact comp_rosenblumIntegrand_sub_comp C (hA z hz) (hB z hz))

/-- **Rosenblum's theorem.**  If a circle encloses the whole spectrum of `A` and
its closed disc misses the spectrum of `B`, the contour integral solves the
Sylvester equation. -/
theorem comp_rosenblumSolution_sub_comp_eq (hr : 0 < radius)
    (hA : spectrum ℂ A ⊆ ball ((center : ℂ)) radius)
    (hB : ∀ z : ℂ, z ∈ closedBall ((center : ℂ)) radius → z ∉ spectrum ℂ B) :
    A ∘L rosenblumSolution A B C center radius -
      rosenblumSolution A B C center radius ∘L B = C := by
  have hAs : ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius → z ∉ spectrum ℂ A :=
    notMem_spectrum_of_norm_eq_radius hA
  have hBs : ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius → z ∉ spectrum ℂ B := fun z hz =>
    hB z (by rw [mem_closedBall, dist_eq_norm, hz])
  simp only [comp_rosenblumSolution_sub_comp A B C hr.le hAs hBs,
    circleRieszProjection_eq_one A hr hA,
    circleRieszProjection_eq_zero B hr hB,
    ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_zero, sub_zero]

/-- **Existence for the Sylvester equation.**  This is the half of
Sylvester--Rosenblum that the uniqueness results in
`DavisKahan.Sylvester.PairwiseHomogeneousUniqueness` were missing. -/
theorem exists_comp_sub_comp_eq (hr : 0 < radius)
    (hA : spectrum ℂ A ⊆ ball ((center : ℂ)) radius)
    (hB : ∀ z : ℂ, z ∈ closedBall ((center : ℂ)) radius → z ∉ spectrum ℂ B) :
    ∃ S : F →L[ℂ] E, A ∘L S - S ∘L B = C :=
  ⟨rosenblumSolution A B C center radius,
    comp_rosenblumSolution_sub_comp_eq A B C hr hA hB⟩

/-- **Uniqueness, from the same identity.**  The Rosenblum integral recovers any
`X` from `A X - X B`, so the Sylvester operator is injective. -/
theorem rosenblumSolution_comp_sub_comp (X : F →L[ℂ] E) (hr : 0 < radius)
    (hA : spectrum ℂ A ⊆ ball ((center : ℂ)) radius)
    (hB : ∀ z : ℂ, z ∈ closedBall ((center : ℂ)) radius → z ∉ spectrum ℂ B) :
    rosenblumSolution A B (A ∘L X - X ∘L B) center radius = X := by
  have hAs : ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius → z ∉ spectrum ℂ A :=
    notMem_spectrum_of_norm_eq_radius hA
  have hBs : ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius → z ∉ spectrum ℂ B := fun z hz =>
    hB z (by rw [mem_closedBall, dist_eq_norm, hz])
  have hcongr : (∮ z in C((center : ℂ), radius),
      rosenblumIntegrand A B (A ∘L X - X ∘L B) z) =
      ∮ z in C((center : ℂ), radius),
        (Ring.inverse (z • (1 : E →L[ℂ] E) - A) ∘L X -
          X ∘L Ring.inverse (z • (1 : F →L[ℂ] F) - B)) :=
    circleIntegral.integral_congr hr.le fun z hz => by
      rw [mem_sphere, dist_eq_norm] at hz
      exact rosenblumIntegrand_comp_sub X (hAs z hz) (hBs z hz)
  -- Left as a `rw` chain on purpose: `simp only` with this same list leaves the goal unsolved: at
  -- least one lemma here has to fire at one occurrence, in order, and simp's normal form loses the
  -- intermediate shape.
  rw [rosenblumSolution, hcongr, circleIntegral_resolvent_sub A B X hr.le hAs hBs,
    circleRieszProjection_eq_one A hr hA, circleRieszProjection_eq_zero B hr hB,
    ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_zero, sub_zero]

/-- **Sylvester--Rosenblum, both halves.**  Under circle separation the Sylvester
equation has exactly one solution. -/
theorem existsUnique_comp_sub_comp_eq (hr : 0 < radius)
    (hA : spectrum ℂ A ⊆ ball ((center : ℂ)) radius)
    (hB : ∀ z : ℂ, z ∈ closedBall ((center : ℂ)) radius → z ∉ spectrum ℂ B) :
    ∃! S : F →L[ℂ] E, A ∘L S - S ∘L B = C := by
  refine ⟨rosenblumSolution A B C center radius,
    comp_rosenblumSolution_sub_comp_eq A B C hr hA hB, fun Y hY => ?_⟩
  rw [← hY, rosenblumSolution_comp_sub_comp A B Y hr hA hB]

end Main

section BoundedInverse

variable (A : E →L[ℂ] E) (B : F →L[ℂ] F) {center radius : ℝ}

omit [CompleteSpace E] [CompleteSpace F] in
/-- The Rosenblum solution of the homogeneous equation is zero. -/
@[simp]
theorem rosenblumSolution_zero (center radius : ℝ) :
    rosenblumSolution A B 0 center radius = 0 := by
  simp [rosenblumSolution, rosenblumIntegrand, circleIntegral]

/-- **The Sylvester operator is a linear homeomorphism under circle separation.**

Bijectivity is exactly the pair of Rosenblum identities: `rosenblumSolution` is a
right inverse by `comp_rosenblumSolution_sub_comp_eq` and a left inverse by
`rosenblumSolution_comp_sub_comp`.  Boundedness of the inverse is then the open
mapping theorem.

This is the reason to bundle the Sylvester operator at all: injectivity, closed
range and a bounded inverse are statements about an *operator*, and the
consequence downstream users want — the reverse estimate
`‖X‖ ≤ K * ‖A X - X B‖` of `norm_le_mul_norm_sylvesterOperator` — is not
available from the pointwise `∃!` alone. -/
noncomputable def sylvesterEquiv (hr : 0 < radius)
    (hA : spectrum ℂ A ⊆ ball ((center : ℂ)) radius)
    (hB : ∀ z : ℂ, z ∈ closedBall ((center : ℂ)) radius → z ∉ spectrum ℂ B) :
    (F →L[ℂ] E) ≃L[ℂ] (F →L[ℂ] E) :=
  ContinuousLinearEquiv.ofBijective (ContinuousLinearMap.sylvesterOperatorL A B)
    (LinearMap.ker_eq_bot'.mpr fun X hX => by
      have hX' : A ∘L X - X ∘L B = 0 := hX
      have h := rosenblumSolution_comp_sub_comp A B X hr hA hB
      rw [hX', rosenblumSolution_zero] at h
      exact h.symm)
    (LinearMap.range_eq_top.mpr fun C =>
      ⟨rosenblumSolution A B C center radius,
        comp_rosenblumSolution_sub_comp_eq A B C hr hA hB⟩)

/-- The Sylvester equivalence, unfolded to its underlying map. -/
@[simp]
theorem sylvesterEquiv_apply (hr : 0 < radius)
    (hA : spectrum ℂ A ⊆ ball ((center : ℂ)) radius)
    (hB : ∀ z : ℂ, z ∈ closedBall ((center : ℂ)) radius → z ∉ spectrum ℂ B)
    (X : F →L[ℂ] E) :
    sylvesterEquiv A B hr hA hB X = A ∘L X - X ∘L B :=
  rfl

/-- The inverse of the Sylvester operator *is* the Rosenblum contour integral. -/
theorem sylvesterEquiv_symm_apply (hr : 0 < radius)
    (hA : spectrum ℂ A ⊆ ball ((center : ℂ)) radius)
    (hB : ∀ z : ℂ, z ∈ closedBall ((center : ℂ)) radius → z ∉ spectrum ℂ B)
    (C : F →L[ℂ] E) :
    (sylvesterEquiv A B hr hA hB).symm C = rosenblumSolution A B C center radius := by
  refine (ContinuousLinearEquiv.symm_apply_eq _).mpr ?_
  rw [sylvesterEquiv_apply]
  exact (comp_rosenblumSolution_sub_comp_eq A B C hr hA hB).symm

/-- **The Sylvester operator is bounded below.**  This is the estimate the
Davis--Kahan gap bounds consume, and it is what the bundled form buys: the
constant is uniform in `X`, which an `∃!` statement cannot express. -/
theorem norm_le_mul_norm_sylvesterOperator (hr : 0 < radius)
    (hA : spectrum ℂ A ⊆ ball ((center : ℂ)) radius)
    (hB : ∀ z : ℂ, z ∈ closedBall ((center : ℂ)) radius → z ∉ spectrum ℂ B)
    (X : F →L[ℂ] E) :
    ‖X‖ ≤ ‖((sylvesterEquiv A B hr hA hB).symm : (F →L[ℂ] E) →L[ℂ] (F →L[ℂ] E))‖ *
      ‖A ∘L X - X ∘L B‖ := by
  have h := ((sylvesterEquiv A B hr hA hB).symm :
    (F →L[ℂ] E) →L[ℂ] (F →L[ℂ] E)).le_opNorm (A ∘L X - X ∘L B)
  rwa [ContinuousLinearEquiv.coe_coe, ← sylvesterEquiv_apply A B hr hA hB X,
    ContinuousLinearEquiv.symm_apply_apply] at h

/-- The uniform lower bound, packaged without naming the equivalence. -/
theorem exists_norm_le_mul_norm_sylvesterOperator (hr : 0 < radius)
    (hA : spectrum ℂ A ⊆ ball ((center : ℂ)) radius)
    (hB : ∀ z : ℂ, z ∈ closedBall ((center : ℂ)) radius → z ∉ spectrum ℂ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : F →L[ℂ] E, ‖X‖ ≤ K * ‖A ∘L X - X ∘L B‖ :=
  ⟨‖((sylvesterEquiv A B hr hA hB).symm : (F →L[ℂ] E) →L[ℂ] (F →L[ℂ] E))‖,
    ContinuousLinearMap.opNorm_nonneg _,
    norm_le_mul_norm_sylvesterOperator A B hr hA hB⟩

end BoundedInverse

end DavisKahan
end TauCeti
