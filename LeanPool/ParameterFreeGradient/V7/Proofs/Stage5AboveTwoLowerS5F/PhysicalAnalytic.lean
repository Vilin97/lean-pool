/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5F.PhysicalScaling
import Mathlib.Basic.Real.Pointwise

/-!
Physical rescaling preserves convexity, gradients, smoothness, and the prescribed minimizer
distance.
-/

namespace V7.Stage5AboveTwoLowerS5F

open scoped Pointwise

lemma physicalOracle_coordinateGradient {d : ℕ} (x0 : Point d)
    {L R rT : ℝ} (hL : 0 < L) (hR : 0 < R) (hrT : 0 < rT)
    (bar : PairOracle d) (hgrad : O3.IsCoordinateGradient bar.value bar.gradient) :
    O3.IsCoordinateGradient (physicalOracle x0 L R rT bar).value
      (physicalOracle x0 L R rT bar).gradient := by
  intro x
  let a := rT / R
  let A := L * R ^ (2 : ℕ) / rT ^ (2 : ℕ)
  let B := L * R / rT
  let z := physicalBackward x0 R rT x
  have hinner : HasFDerivAt (physicalBackward x0 R rT)
      (a • ContinuousLinearMap.id ℝ (Point d)) x := by
    change HasFDerivAt (fun y : Point d => a • (y - x0))
      (a • ContinuousLinearMap.id ℝ (Point d)) x
    fun_prop
  have hbase := (hgrad z).1.hasFDerivAt
  have hcomp := hbase.comp x hinner
  have hscaled := hcomp.const_mul A
  have hAB : A * a = B := by
    dsimp [A, a, B]
    field_simp [hR.ne', hrT.ne']
  constructor
  · simpa [physicalOracle, A, z] using hscaled.differentiableAt
  · intro h
    have heq := congrArg (fun F : Point d →L[ℝ] ℝ => F h) hscaled.fderiv
    change fderiv ℝ (physicalOracle x0 L R rT bar).value x h =
      pairing ((physicalOracle x0 L R rT bar).gradient x) h
    rw [show fderiv ℝ (physicalOracle x0 L R rT bar).value x h =
        (A • fderiv ℝ bar.value z ∘L
          (a • ContinuousLinearMap.id ℝ (Point d))) h by
      simpa [physicalOracle, A, z, Function.comp_apply] using heq]
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
    rw [(hgrad z).2]
    rw [O3.Stage2RouteD.pairing_smul_right]
    change A * (a * pairing (bar.gradient z) h) =
      pairing (B • bar.gradient z) h
    calc
      _ = B * pairing (bar.gradient z) h := by rw [← mul_assoc, hAB]
      _ = pairing (B • bar.gradient z) h :=
        (O3.Stage2RouteD.pairing_smul_left B (bar.gradient z) h).symm

lemma physicalOracle_convex {d : ℕ} (x0 : Point d) {L R rT : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hrT : 0 < rT)
    (bar : PairOracle d) (hconv : O3.IsConvexObjective bar.value) :
    O3.IsConvexObjective (physicalOracle x0 L R rT bar).value := by
  unfold O3.IsConvexObjective at hconv ⊢
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let A := L * R ^ (2 : ℕ) / rT ^ (2 : ℕ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have harg : physicalBackward x0 R rT (a • x + b • y) =
      a • physicalBackward x0 R rT x + b • physicalBackward x0 R rT y := by
    unfold physicalBackward
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    have hx0 := congrArg (fun c : ℝ => c * x0 i) hab
    linear_combination (rT / R) * hx0
  have hc := hconv.2 (Set.mem_univ (physicalBackward x0 R rT x))
    (Set.mem_univ (physicalBackward x0 R rT y)) ha hb hab
  change A * bar.value (physicalBackward x0 R rT (a • x + b • y)) ≤
    a * (A * bar.value (physicalBackward x0 R rT x)) +
      b * (A * bar.value (physicalBackward x0 R rT y))
  rw [harg]
  have hmul := mul_le_mul_of_nonneg_left hc hA
  calc
    _ ≤ A * (a * bar.value (physicalBackward x0 R rT x) +
      b * bar.value (physicalBackward x0 R rT y)) := by
        simpa [smul_eq_mul] using hmul
    _ = _ := by ring

lemma physicalBackward_sub (x0 : Point d) (R rT : ℝ) (x y : Point d) :
    physicalBackward x0 R rT x - physicalBackward x0 R rT y =
      (rT / R) • (x - y) := by
  unfold physicalBackward
  module

lemma physicalOracle_smooth {p : ℝ} {d : ℕ} (hp : 2 < p) (x0 : Point d)
    {L R rT : ℝ} (hL : 0 < L) (hR : 0 < R) (hrT : 0 < rT)
    (bar : PairOracle d) (hsmooth : IsLpSmooth p 1 bar) :
    IsLpSmooth p L (physicalOracle x0 L R rT bar) := by
  intro x y
  let B := L * R / rT
  have hB : 0 < B := by dsimp [B]; positivity
  have hq := O3.one_lt_conjugateExponent (by linarith : 1 < p)
  change lpNorm (conjugateExponent p)
      (B • bar.gradient (physicalBackward x0 R rT x) -
        B • bar.gradient (physicalBackward x0 R rT y)) ≤ L * lpNorm p (x - y)
  rw [← smul_sub]
  change O3.lpNorm (conjugateExponent p)
      (B • (bar.gradient (physicalBackward x0 R rT x) -
        bar.gradient (physicalBackward x0 R rT y))) ≤ _
  rw [O3.Stage2RouteC.lpNorm_smul hq.le,
    abs_of_pos hB]
  have hb := hsmooth (physicalBackward x0 R rT x)
    (physicalBackward x0 R rT y)
  rw [one_mul, physicalBackward_sub,
    O3.Stage2RouteC.lpNorm_smul (by linarith : 1 ≤ p),
    abs_of_pos (div_pos hrT hR)] at hb
  calc
    B * lpNorm (conjugateExponent p)
        (bar.gradient (physicalBackward x0 R rT x) -
          bar.gradient (physicalBackward x0 R rT y)) ≤
      B * ((rT / R) * lpNorm p (x - y)) :=
        mul_le_mul_of_nonneg_left hb hB.le
    _ = L * lpNorm p (x - y) := by
      dsimp [B]
      field_simp [hR.ne', hrT.ne']


lemma physical_minimizer_iff (x0 : Point d) {L R rT : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hrT : 0 < rT)
    (bar : PairOracle d) (x : Point d) :
    x ∈ O3.MinimizerSet (physicalOracle x0 L R rT bar).value ↔
      physicalBackward x0 R rT x ∈ O3.MinimizerSet bar.value := by
  let A := L * R ^ (2 : ℕ) / rT ^ (2 : ℕ)
  have hA : 0 < A := by dsimp [A]; positivity
  constructor
  · intro hx z
    have h := hx (physicalForward x0 R rT z)
    change A * bar.value (physicalBackward x0 R rT x) ≤
      A * bar.value (physicalBackward x0 R rT
        (physicalForward x0 R rT z)) at h
    rw [physicalBackward_forward x0 hR hrT] at h
    nlinarith
  · intro hx y
    change A * bar.value (physicalBackward x0 R rT x) ≤
      A * bar.value (physicalBackward x0 R rT y)
    have h := hx (physicalBackward x0 R rT y)
    nlinarith

lemma physical_minimizerNonempty (x0 : Point d) {L R rT : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hrT : 0 < rT)
    (bar : PairOracle d) (hne : (O3.MinimizerSet bar.value).Nonempty) :
    (O3.MinimizerSet (physicalOracle x0 L R rT bar).value).Nonempty := by
  rcases hne with ⟨z, hz⟩
  refine ⟨physicalForward x0 R rT z, ?_⟩
  rw [physical_minimizer_iff x0 hL hR hrT]
  simpa [physicalBackward_forward x0 hR hrT] using hz

lemma physical_minimizerDistance {p : ℝ} (hp : 2 < p) (x0 : Point d)
    {L R rT : ℝ} (hL : 0 < L) (hR : 0 < R) (hrT : 0 < rT)
    (bar : PairOracle d) (hradius : minimizerDistance p bar 0 = rT) :
    minimizerDistance p (physicalOracle x0 L R rT bar) x0 = R := by
  let barDistances : Set ℝ :=
    (fun z : Point d => lpNorm p (z - 0)) '' O3.MinimizerSet bar.value
  let physicalDistances : Set ℝ :=
    (fun x : Point d => lpNorm p (x - x0)) ''
      O3.MinimizerSet (physicalOracle x0 L R rT bar).value
  have hset : physicalDistances = (R / rT) • barDistances := by
    ext s
    constructor
    · rintro ⟨x, hx, rfl⟩
      let z := physicalBackward x0 R rT x
      have hz := (physical_minimizer_iff x0 hL hR hrT bar x).mp hx
      refine ⟨lpNorm p (z - 0), ⟨z, hz, rfl⟩, ?_⟩
      change (R / rT) * lpNorm p (z - 0) = lpNorm p (x - x0)
      rw [show x - x0 = (R / rT) • z by
        dsimp [z, physicalBackward]
        have hscale : (R / rT) * (rT / R) = 1 := by field_simp
        rw [smul_smul, hscale, one_smul]]
      have hn := O3.Stage2RouteC.lpNorm_smul (d := d)
        (by linarith : 1 ≤ p) (R / rT) z
      change (R / rT) * O3.lpNorm p (z - 0) =
        O3.lpNorm p ((R / rT) • z)
      rw [hn, abs_of_pos (div_pos hR hrT)]
      simp
    · rintro ⟨s, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨physicalForward x0 R rT z, ?_, ?_⟩
      · rw [physical_minimizer_iff x0 hL hR hrT]
        simpa [physicalBackward_forward x0 hR hrT] using hz
      · change lpNorm p (physicalForward x0 R rT z - x0) =
          (R / rT) * lpNorm p (z - 0)
        rw [show physicalForward x0 R rT z - x0 = (R / rT) • z by
          unfold physicalForward; module]
        have hn := O3.Stage2RouteC.lpNorm_smul (d := d)
          (by linarith : 1 ≤ p) (R / rT) z
        change O3.lpNorm p ((R / rT) • z) =
          (R / rT) * O3.lpNorm p (z - 0)
        rw [hn, abs_of_pos (div_pos hR hrT)]
        simp
  unfold minimizerDistance O3.minimizerDistance
  change sInf physicalDistances = R
  rw [hset, Real.sInf_smul_of_nonneg (div_pos hR hrT).le]
  change (R / rT) * minimizerDistance p bar 0 = R
  rw [hradius]
  field_simp [hrT.ne']

end V7.Stage5AboveTwoLowerS5F
