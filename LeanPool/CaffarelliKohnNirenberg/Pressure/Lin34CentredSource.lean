/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34SliceCore
public import LeanPool.CaffarelliKohnNirenberg.Pressure.CZStartBridgeSource

/-!
# Lin34 Centred Source

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- The cut-off, doubly centred velocity tensor that enters the
Calderón--Zygmund estimate of `prop:lin34` as its source: with `η` the
mollified cut-off of `B_ρ` and `Û` the centred tensor `eq:Uhat`, at the time
`s` and in the entries `i, j` it is the function

`x ↦ η(x) · Û_{ij}(x, s)`. -/
def lin34CentredSource (u : ParabolicPoint → Vec3) (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ)
    (s : ℝ) (i j : Fin 3) : Vec3 → ℝ :=
  fun x => mollifiedBallCutoff x₀ hρ x *
    pressureUTensor (lin34CentredVelocity u x₀ ρ) 0 ((x, s) : ParabolicPoint) i j

/-- The cut-off is supported well inside `B_ρ`, so the centred source tensor
vanishes off the ball carrying the velocity oscillation of `eq:Chat`. -/
theorem lin34CentredSource_eq_zero_of_notMem
    (u : ParabolicPoint → Vec3) (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ) (s : ℝ)
    (i j : Fin 3) {y : Vec3} (hy : y ∉ euclideanBall x₀ ρ) :
    lin34CentredSource u x₀ hρ s i j y = 0 := by
  have hsub : euclideanBall x₀ (3 * ρ / 4) ⊆ euclideanBall x₀ ρ := by
    intro w hw
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).2
    exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt
      (by positivity : (0 : ℝ) < 3 * ρ / 4)).1 hw).trans_le (by linarith only [hρ])
  have hout : y ∉ tsupport (mollifiedBallCutoff x₀ hρ) := fun hmem =>
    hy (hsub (mollifiedBallCutoff_tsupport_subset_outer x₀ hρ hmem))
  have hzero : mollifiedBallCutoff x₀ hρ y = 0 :=
    image_eq_zero_of_notMem_tsupport hout
  show mollifiedBallCutoff x₀ hρ y *
    pressureUTensor (lin34CentredVelocity u x₀ ρ) 0 ((y, s) : ParabolicPoint) i j = 0
  rw [hzero, zero_mul]

/-- The centred source tensor is compactly supported: it vanishes outside the
closed ball of radius `3ρ/4`, which carries the support of the mollified
cut-off. -/
theorem lin34CentredSource_hasCompactSupport
    (u : ParabolicPoint → Vec3) (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ) (s : ℝ)
    (i j : Fin 3) :
    HasCompactSupport (lin34CentredSource u x₀ hρ s i j) := by
  refine HasCompactSupport.intro
    (isCompact_euclideanClosedBall x₀ (R := 3 * ρ / 4) (by positivity)) ?_
  intro y hy
  have hball : y ∉ euclideanBall x₀ (3 * ρ / 4) := by
    intro hmem
    apply hy
    show euclideanSqDist y x₀ ≤ (3 * ρ / 4) ^ 2
    exact (hmem : euclideanSqDist y x₀ < (3 * ρ / 4) ^ 2).le
  have hout : y ∉ tsupport (mollifiedBallCutoff x₀ hρ) := fun hmem =>
    hball (mollifiedBallCutoff_tsupport_subset_outer x₀ hρ hmem)
  have hzero : mollifiedBallCutoff x₀ hρ y = 0 :=
    image_eq_zero_of_notMem_tsupport hout
  show mollifiedBallCutoff x₀ hρ y *
    pressureUTensor (lin34CentredVelocity u x₀ ρ) 0 ((y, s) : ParabolicPoint) i j = 0
  rw [hzero, zero_mul]

private lemma lin34Centred_euclideanBall_eq_vec3Ball {x₀ : Vec3} {r : ℝ}
    (hr : 0 < r) : euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  change x ∈ euclideanBall x₀ r ↔ vec3EuclideanNorm (x - x₀) < r
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
    (mem_euclideanBall_iff_vecEuclideanNorm_lt hr)

private lemma lin34CentredSource_aestronglyMeasurable
    {u : ParabolicPoint → Vec3} {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) {s : ℝ}
    (hu : AEStronglyMeasurable (fun y : Vec3 => u (y, s))
      (volume.restrict (vec3Ball x₀ ρ)))
    (i j : Fin 3) :
    AEStronglyMeasurable (lin34CentredSource u x₀ hρ s i j) volume := by
  have hzero : ∀ y, y ∉ euclideanBall x₀ ρ →
      lin34CentredSource u x₀ hρ s i j y = 0 := fun y hy =>
    lin34CentredSource_eq_zero_of_notMem u x₀ hρ s i j hy
  have hzero' : ∀ y, y ∉ vec3Ball x₀ ρ →
      lin34CentredSource u x₀ hρ s i j y = 0 := fun y hy =>
    hzero y (by rw [lin34Centred_euclideanBall_eq_vec3Ball hρ]; exact hy)
  have hind : (vec3Ball x₀ ρ).indicator (lin34CentredSource u x₀ hρ s i j) =
      lin34CentredSource u x₀ hρ s i j := by
    apply Set.indicator_eq_self.2
    exact Function.support_subset_iff'.2 hzero'
  have hcv : AEStronglyMeasurable
      (fun y : Vec3 => lin34CentredVelocity u x₀ ρ (y, s))
      (volume.restrict (vec3Ball x₀ ρ)) := by
    rw [lin34_centredVelocity_slice_eq]
    exact hu.sub aestronglyMeasurable_const
  have hcomp : ∀ k : Fin 3, AEStronglyMeasurable
      (fun y : Vec3 => lin34CentredVelocity u x₀ ρ (y, s) k)
      (volume.restrict (vec3Ball x₀ ρ)) := fun k =>
    (continuous_apply k).comp_aestronglyMeasurable hcv
  have hpoly : AEStronglyMeasurable
      (fun y : Vec3 => pressureUTensor (lin34CentredVelocity u x₀ ρ) 0
        ((y, s) : ParabolicPoint) i j)
      (volume.restrict (vec3Ball x₀ ρ)) := by
    simp only [pressureUTensor, Pi.zero_apply, sub_zero]
    exact (hcomp i).neg.mul (hcomp j)
  have hη : AEStronglyMeasurable (mollifiedBallCutoff x₀ hρ)
      (volume.restrict (vec3Ball x₀ ρ)) :=
    (mollifiedBallCutoff_smooth x₀ hρ).continuous.aestronglyMeasurable
  have hrestrict : AEStronglyMeasurable (lin34CentredSource u x₀ hρ s i j)
      (volume.restrict (vec3Ball x₀ ρ)) := hη.mul hpoly
  have h := (aestronglyMeasurable_indicator_iff
    (isOpen_vec3Ball x₀ ρ).measurableSet).2 hrestrict
  rwa [hind] at h

/-- The pointwise Hölder input of `prop:lin34`: the cut-off centred tensor is
bounded by the square of the Euclidean norm of the mean-free velocity, because
the cut-off takes values in `[0,1]` and the centred tensor `eq:Uhat` has norm
`|Û| = |v|²`. -/
private lemma lin34CentredSource_abs_le
    {u : ParabolicPoint → Vec3} {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) {s : ℝ}
    (i j : Fin 3) (y : Vec3) :
    |lin34CentredSource u x₀ hρ s i j y| ≤
      vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (2 : ℕ) := by
  have hη0 : 0 ≤ mollifiedBallCutoff x₀ hρ y :=
    mollifiedBallCutoff_nonneg x₀ hρ y
  have hη1 : mollifiedBallCutoff x₀ hρ y ≤ 1 :=
    mollifiedBallCutoff_le_one x₀ hρ y
  have hcomp := pressure_component_abs_le_utensorNorm
    (lin34CentredVelocity u x₀ ρ) 0 s y i j
  show |mollifiedBallCutoff x₀ hρ y *
    pressureUTensor (lin34CentredVelocity u x₀ ρ) 0 ((y, s) : ParabolicPoint) i j| ≤ _
  rw [abs_mul, abs_of_nonneg hη0]
  calc
    mollifiedBallCutoff x₀ hρ y *
        |pressureUTensor (lin34CentredVelocity u x₀ ρ) 0
          ((y, s) : ParabolicPoint) i j| ≤
        1 * pressureUTensorNorm (lin34CentredVelocity u x₀ ρ) 0 s y := by
      gcongr
    _ = vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (2 : ℕ) := by
      rw [one_mul, lin34_pressureUTensorNorm_centred]

/-- The `L^{3/2}` source estimate of `prop:lin34`: each entry of the cut-off
centred velocity tensor lies in `L^{3/2}(ℝ³)`, with norm at most
`(∫_{B_ρ} |v(·,s)|³)^{2/3}`, the square of the `L³(B_ρ)` norm of the mean-free
velocity.  These are the source facts the Calderón--Zygmund input `ext:CZ`
consumes. -/
theorem lin34CentredSource_memLp_and_lpNorm_le
    {u : ParabolicPoint → Vec3} {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) {s : ℝ}
    (hu : AEStronglyMeasurable (fun y : Vec3 => u (y, s))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hv : IntegrableOn
      (fun y => vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (3 : ℕ))
      (euclideanBall x₀ ρ) volume)
    (i j : Fin 3) :
    MemLp (lin34CentredSource u x₀ hρ s i j) (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
      lpNorm (lin34CentredSource u x₀ hρ s i j)
          (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
        (∫ y in euclideanBall x₀ ρ,
          vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (3 : ℕ)) ^ (2 / 3 : ℝ) := by
  have hmeas : AEStronglyMeasurable (lin34CentredSource u x₀ hρ s i j) volume :=
    lin34CentredSource_aestronglyMeasurable hρ hu i j
  have hzero : ∀ y, y ∉ euclideanBall x₀ ρ →
      lin34CentredSource u x₀ hρ s i j y = 0 := fun y hy =>
    lin34CentredSource_eq_zero_of_notMem u x₀ hρ s i j hy
  have hbound : ∀ y, |lin34CentredSource u x₀ hρ s i j y| ≤
      vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (2 : ℕ) :=
    lin34CentredSource_abs_le hρ i j
  exact ⟨memLp_three_halves_of_velocity_square_bound
      (v := meanFreeVec u x₀ ρ s) hmeas hv hzero hbound,
    lpNorm_three_halves_le_of_velocity_square_bound
      (v := meanFreeVec u x₀ ρ s) hmeas hv hzero hbound⟩

/-- The nine-entry form of the source estimate, as the tensor pressure operator
of `prop:pressure-decomposition` consumes it: the sum of the `L^{3/2}` norms of
the entries of the cut-off centred velocity tensor is at most nine times the
square of the `L³(B_ρ)` norm of the mean-free velocity. -/
theorem lin34CentredSource_sum_lpNorm_le
    {u : ParabolicPoint → Vec3} {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) {s : ℝ}
    (hu : AEStronglyMeasurable (fun y : Vec3 => u (y, s))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hv : IntegrableOn
      (fun y => vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (3 : ℕ))
      (euclideanBall x₀ ρ) volume) :
    (∑ i, ∑ j, lpNorm (lin34CentredSource u x₀ hρ s i j)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume) ≤
      9 * (∫ y in euclideanBall x₀ ρ,
        vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (3 : ℕ)) ^ (2 / 3 : ℝ) := by
  classical
  have hentry : ∀ i j : Fin 3,
      lpNorm (lin34CentredSource u x₀ hρ s i j)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
      (∫ y in euclideanBall x₀ ρ,
        vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (3 : ℕ)) ^ (2 / 3 : ℝ) :=
    fun i j => (lin34CentredSource_memLp_and_lpNorm_le hρ hu hv i j).2
  calc
    (∑ i, ∑ j, lpNorm (lin34CentredSource u x₀ hρ s i j)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume) ≤
        ∑ _i : Fin 3, ∑ _j : Fin 3,
          (∫ y in euclideanBall x₀ ρ,
            vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (3 : ℕ)) ^
              (2 / 3 : ℝ) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
    _ = 9 * (∫ y in euclideanBall x₀ ρ,
        vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (3 : ℕ)) ^ (2 / 3 : ℝ) := by
      simp [Finset.sum_const, Finset.card_univ]
      ring

end CKN
