/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34CentredPotentialSource
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.PotentialLocalLpGrowth
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PotentialDecayGrowthSum
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PotentialDecay
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsCylinder

/-!
# Lin34 Centred Potential Growth

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
# Summation of the centred potentials `p₂`--`p₆`

The five sources of `prop:pressure-decomposition` produced in
`Lin34CentredPotentialSource.lean` are fed to the single-potential growth engines and
the resulting nine-entry groups are summed.
-/

/-! ### Step D: summation of the nine-entry groups -/

/-- A double sum of `L^{3/2}` functions, each obeying a local linear growth bound,
obeys the local membership and the linear growth bound with the sum of the
constants.  This packages the `Fin 3 × Fin 3` index range over which the potentials
`p₂`, `p₃`, `p₄` of `prop:pressure-decomposition` are summed. -/
theorem lin34_double_sum_memLp_and_lpNorm_growth {G : Fin 3 → Fin 3 → Vec3 → ℝ}
    {C : Fin 3 → Fin 3 → ℝ}
    (hmem : ∀ i j : Fin 3, ∀ ρ : ℝ, 0 < ρ →
      MemLp (G i j) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)))
    (hb : ∀ i j : Fin 3, ∀ ρ : ℝ, 0 < ρ →
      lpNorm (G i j) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ C i j * (1 + ρ)) :
    (∀ ρ : ℝ, 0 < ρ →
      MemLp (fun x => ∑ i : Fin 3, ∑ j : Fin 3, G i j x) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ))) ∧
    (∀ ρ : ℝ, 0 < ρ →
      lpNorm (fun x => ∑ i : Fin 3, ∑ j : Fin 3, G i j x) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
        (∑ i : Fin 3, ∑ j : Fin 3, C i j) * (1 + ρ)) := by
  have hsum_eq : (∑ i : Fin 3, ∑ j : Fin 3, G i j) =
      fun x => ∑ i : Fin 3, ∑ j : Fin 3, G i j x := by
    funext x
    simp only [Finset.sum_apply]
  constructor
  · intro ρ hρ
    have hinner : ∀ i : Fin 3, ∀ ρ : ℝ, 0 < ρ →
        MemLp (∑ j : Fin 3, G i j) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) ρ)) :=
      fun i ρ hρ => memLp_euclideanBall_family_sum (s := Finset.univ) (f := G i)
        (fun j _ ρ hρ => hmem i j ρ hρ) ρ hρ
    have houter := memLp_euclideanBall_family_sum (s := Finset.univ)
      (f := fun i : Fin 3 => ∑ j : Fin 3, G i j)
      (fun i _ ρ hρ => hinner i ρ hρ) ρ hρ
    rwa [hsum_eq] at houter
  · intro ρ hρ
    have hinner : ∀ i : Fin 3, ∀ ρ : ℝ, 0 < ρ →
        lpNorm (∑ j : Fin 3, G i j) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤
          (∑ j : Fin 3, C i j) * (1 + ρ) :=
      fun i ρ hρ => lpNorm_euclideanBall_growth_sum (s := Finset.univ) (f := G i)
        (C := C i) (fun j _ ρ hρ => hmem i j ρ hρ) (fun j _ ρ hρ => hb i j ρ hρ) hρ
    have hmemouter : ∀ i ∈ (Finset.univ : Finset (Fin 3)), ∀ ρ : ℝ, 0 < ρ →
        MemLp (∑ j : Fin 3, G i j) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) ρ)) :=
      fun i _ ρ hρ => memLp_euclideanBall_family_sum (s := Finset.univ) (f := G i)
        (fun j _ ρ hρ => hmem i j ρ hρ) ρ hρ
    have houter := lpNorm_euclideanBall_growth_sum (s := Finset.univ)
      (f := fun i : Fin 3 => ∑ j : Fin 3, G i j)
      (C := fun i : Fin 3 => ∑ j : Fin 3, C i j)
      hmemouter (fun i _ ρ hρ => hinner i ρ hρ) hρ
    rwa [hsum_eq] at houter

/-! ### Steps C and D: the group `p₂ + p₃ + p₄ + p₅ + p₆` -/

/-- Local `L^{3/2}` membership on every round ball about the origin, with linear
growth of the norm, for the five Newtonian-potential parts `p₂, p₃, p₄, p₅, p₆` of
the pressure decomposition `prop:pressure-decomposition`, run with the mollified
cut-off of `B_ρ(x₀)` and the doubly centred velocity `eq:Uhat`.  This is the decay
input of the Liouville identification step of `prop:lin34`. -/
theorem lin34_centred_potentials_memLp_and_growth
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) {s : ℝ}
    (hu : AEStronglyMeasurable (fun y : Vec3 => u (y, s))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hv : IntegrableOn
      (fun y => vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (3 : ℕ))
      (euclideanBall x₀ ρ) volume)
    (hp : MemLp (fun y : Vec3 => p (y, s)) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (vec3Ball x₀ ρ))) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ R : ℝ, 0 < R →
        MemLp (fun x =>
            pressureP2 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s x +
              pressureP3 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s x +
              pressureP4 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s x +
              pressureP5 (mollifiedBallCutoff x₀ hρ) p s x +
              pressureP6 (mollifiedBallCutoff x₀ hρ) p s x)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) R))) ∧
      (∀ R : ℝ, 0 < R →
        lpNorm (fun x =>
            pressureP2 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s x +
              pressureP3 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s x +
              pressureP4 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s x +
              pressureP5 (mollifiedBallCutoff x₀ hρ) p s x +
              pressureP6 (mollifiedBallCutoff x₀ hρ) p s x)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) R)) ≤ C * (1 + R)) := by
  classical
  have hR₀ : 0 < vec3EuclideanNorm x₀ + ρ := by
    linarith only [vec3EuclideanNorm_nonneg x₀, hρ]
  have hg2 (i j : Fin 3) := lin34CentredTensorHessian_memLp_and_zero hρ hu hv i j
  have hg3 (i j : Fin 3) := lin34CentredTensorGradientI_memLp_and_zero hρ hu hv i j
  have hg4 (i j : Fin 3) := lin34CentredTensorGradientJ_memLp_and_zero hρ hu hv i j
  have hg5 := lin34CentredPressureLaplacian_memLp_and_zero hρ hp
  have hg6 (j : Fin 3) := lin34CentredPressureGradient_memLp_and_zero hρ hp j
  have hp2ij (i j : Fin 3) :=
    pressureNewtonianPotential_memLp_and_lpNorm_growth_three_halves
      (R := vec3EuclideanNorm x₀ + ρ) hR₀ (hg2 i j).1 (hg2 i j).2
  have hp3ij (i j : Fin 3) :=
    pressureNewtonianDerivativePotential_memLp_and_lpNorm_growth_three_halves j
      (R := vec3EuclideanNorm x₀ + ρ) hR₀ (hg3 i j).1 (hg3 i j).2
  have hp4ij (i j : Fin 3) :=
    pressureNewtonianDerivativePotential_memLp_and_lpNorm_growth_three_halves i
      (R := vec3EuclideanNorm x₀ + ρ) hR₀ (hg4 i j).1 (hg4 i j).2
  have hp5 :=
    pressureNewtonianPotential_memLp_and_lpNorm_growth_three_halves
      (R := vec3EuclideanNorm x₀ + ρ) hR₀ hg5.1 hg5.2
  have hp6 (j : Fin 3) :=
    pressureNewtonianDerivativePotential_memLp_and_lpNorm_growth_three_halves j
      (R := vec3EuclideanNorm x₀ + ρ) hR₀ (hg6 j).1 (hg6 j).2
  let C2 : Fin 3 → Fin 3 → ℝ := fun i j =>
    newtonianPotentialGrowthConstant (lin34CentredTensorHessian u x₀ hρ s i j)
      (vec3EuclideanNorm x₀ + ρ)
  let C3 : Fin 3 → Fin 3 → ℝ := fun i j =>
    newtonianDerivativePotentialGrowthConstant j (lin34CentredTensorGradientI u x₀ hρ s i j)
      (vec3EuclideanNorm x₀ + ρ)
  let C4 : Fin 3 → Fin 3 → ℝ := fun i j =>
    newtonianDerivativePotentialGrowthConstant i (lin34CentredTensorGradientJ u x₀ hρ s i j)
      (vec3EuclideanNorm x₀ + ρ)
  let C6 : Fin 3 → ℝ := fun j =>
    newtonianDerivativePotentialGrowthConstant j (lin34CentredPressureGradient p x₀ hρ s j)
      (vec3EuclideanNorm x₀ + ρ)
  have hP2eq : pressureP2 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s =
      fun x => ∑ i : Fin 3, ∑ j : Fin 3,
        pressureNewtonianPotential (lin34CentredTensorHessian u x₀ hρ s i j) x := rfl
  have hP3eq : pressureP3 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s =
      fun x => ∑ i : Fin 3, ∑ j : Fin 3,
        pressureNewtonianDerivativePotential j (lin34CentredTensorGradientI u x₀ hρ s i j) x := rfl
  have hP4eq : pressureP4 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s =
      fun x => ∑ i : Fin 3, ∑ j : Fin 3,
        pressureNewtonianDerivativePotential i (lin34CentredTensorGradientJ u x₀ hρ s i j) x := rfl
  have hP5eq : pressureP5 (mollifiedBallCutoff x₀ hρ) p s =
      -(pressureNewtonianPotential (lin34CentredPressureLaplacian p x₀ hρ s)) := rfl
  have hP6eq : pressureP6 (mollifiedBallCutoff x₀ hρ) p s =
      (-2 : ℝ) • (fun x => ∑ j : Fin 3,
        pressureNewtonianDerivativePotential j (lin34CentredPressureGradient p x₀ hρ s j) x) := rfl
  have h2 := lin34_double_sum_memLp_and_lpNorm_growth
    (G := fun i j => pressureNewtonianPotential (lin34CentredTensorHessian u x₀ hρ s i j))
    (C := C2)
    (fun i j ρ hρ => (hp2ij i j).1 ρ hρ) (fun i j ρ hρ => (hp2ij i j).2 ρ hρ)
  have h3 := lin34_double_sum_memLp_and_lpNorm_growth
    (G := fun i j =>
      pressureNewtonianDerivativePotential j (lin34CentredTensorGradientI u x₀ hρ s i j))
    (C := C3)
    (fun i j ρ hρ => (hp3ij i j).1 ρ hρ) (fun i j ρ hρ => (hp3ij i j).2 ρ hρ)
  have h4 := lin34_double_sum_memLp_and_lpNorm_growth
    (G := fun i j =>
      pressureNewtonianDerivativePotential i (lin34CentredTensorGradientJ u x₀ hρ s i j))
    (C := C4)
    (fun i j ρ hρ => (hp4ij i j).1 ρ hρ) (fun i j ρ hρ => (hp4ij i j).2 ρ hρ)
  have h2mem : ∀ r : ℝ, 0 < r →
      MemLp (pressureP2 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s)
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r)) := by
    intro r hr
    rw [hP2eq]
    exact h2.1 r hr
  have h2bound : ∀ r : ℝ, 0 < r →
      lpNorm (pressureP2 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s)
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r)) ≤
        (∑ i : Fin 3, ∑ j : Fin 3, C2 i j) * (1 + r) := by
    intro r hr
    rw [hP2eq]
    exact h2.2 r hr
  have h3mem : ∀ r : ℝ, 0 < r →
      MemLp (pressureP3 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s)
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r)) := by
    intro r hr
    rw [hP3eq]
    exact h3.1 r hr
  have h3bound : ∀ r : ℝ, 0 < r →
      lpNorm (pressureP3 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s)
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r)) ≤
        (∑ i : Fin 3, ∑ j : Fin 3, C3 i j) * (1 + r) := by
    intro r hr
    rw [hP3eq]
    exact h3.2 r hr
  have h4mem : ∀ r : ℝ, 0 < r →
      MemLp (pressureP4 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s)
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r)) := by
    intro r hr
    rw [hP4eq]
    exact h4.1 r hr
  have h4bound : ∀ r : ℝ, 0 < r →
      lpNorm (pressureP4 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s)
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r)) ≤
        (∑ i : Fin 3, ∑ j : Fin 3, C4 i j) * (1 + r) := by
    intro r hr
    rw [hP4eq]
    exact h4.2 r hr
  have h5mem : ∀ r : ℝ, 0 < r →
      MemLp (pressureP5 (mollifiedBallCutoff x₀ hρ) p s) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) r)) := by
    intro r hr
    rw [hP5eq]
    exact (hp5.1 r hr).neg
  have h5bound : ∀ r : ℝ, 0 < r →
      lpNorm (pressureP5 (mollifiedBallCutoff x₀ hρ) p s) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) r)) ≤
        newtonianPotentialGrowthConstant (lin34CentredPressureLaplacian p x₀ hρ s)
          (vec3EuclideanNorm x₀ + ρ) * (1 + r) := by
    intro r hr
    rw [hP5eq, lpNorm_neg]
    exact hp5.2 r hr
  have h6mem : ∀ r : ℝ, 0 < r →
      MemLp (pressureP6 (mollifiedBallCutoff x₀ hρ) p s) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) r)) := by
    intro r hr
    have hsum := memLp_euclideanBall_family_sum (s := Finset.univ)
      (f := fun j : Fin 3 =>
        pressureNewtonianDerivativePotential j (lin34CentredPressureGradient p x₀ hρ s j))
      (fun j _ r hr => (hp6 j).1 r hr) r hr
    have hsumeq : (∑ j : Fin 3,
        pressureNewtonianDerivativePotential j (lin34CentredPressureGradient p x₀ hρ s j)) =
        fun x => ∑ j : Fin 3,
          pressureNewtonianDerivativePotential j (lin34CentredPressureGradient p x₀ hρ s j) x := by
      funext x
      simp only [Finset.sum_apply]
    rw [hsumeq] at hsum
    rw [hP6eq]
    exact hsum.const_smul (-2 : ℝ)
  have h6bound : ∀ r : ℝ, 0 < r →
      lpNorm (pressureP6 (mollifiedBallCutoff x₀ hρ) p s) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall (0 : Vec3) r)) ≤
        (∑ j : Fin 3, 2 * C6 j) * (1 + r) := by
    intro r hr
    rw [hP6eq, lpNorm_const_smul]
    have hsum := lpNorm_euclideanBall_growth_sum (s := Finset.univ)
      (f := fun j : Fin 3 =>
        pressureNewtonianDerivativePotential j (lin34CentredPressureGradient p x₀ hρ s j))
      (C := C6)
      (fun j _ r hr => (hp6 j).1 r hr) (fun j _ r hr => (hp6 j).2 r hr) hr
    have hsumeq : (∑ j : Fin 3,
        pressureNewtonianDerivativePotential j (lin34CentredPressureGradient p x₀ hρ s j)) =
        fun x => ∑ j : Fin 3,
          pressureNewtonianDerivativePotential j (lin34CentredPressureGradient p x₀ hρ s j) x := by
      funext x
      simp only [Finset.sum_apply]
    rw [hsumeq] at hsum
    calc
      ‖(-2 : ℝ)‖₊ * lpNorm (fun x => ∑ j : Fin 3,
          pressureNewtonianDerivativePotential j
            (lin34CentredPressureGradient p x₀ hρ s j) x)
          (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r))
          ≤ 2 * ((∑ j : Fin 3, C6 j) * (1 + r)) := by
        have hle := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 2 by norm_num)
        simpa using hle
      _ = (∑ j : Fin 3, 2 * C6 j) * (1 + r) := by
        rw [← Finset.mul_sum]
        ring
  have h23mem := memLp_euclideanBall_family_add h2mem h3mem
  have h23bound : ∀ r : ℝ, 0 < r →
      lpNorm (pressureP2 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s +
          pressureP3 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s)
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r)) ≤
        ((∑ i : Fin 3, ∑ j : Fin 3, C2 i j) + (∑ i : Fin 3, ∑ j : Fin 3, C3 i j)) *
          (1 + r) :=
    fun r hr => lpNorm_euclideanBall_growth_add h2mem h2bound h3bound hr
  have h234mem := memLp_euclideanBall_family_add h23mem h4mem
  have h234bound : ∀ r : ℝ, 0 < r →
      lpNorm (pressureP2 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s +
          pressureP3 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s +
          pressureP4 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s)
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r)) ≤
        (((∑ i : Fin 3, ∑ j : Fin 3, C2 i j) + (∑ i : Fin 3, ∑ j : Fin 3, C3 i j)) +
          (∑ i : Fin 3, ∑ j : Fin 3, C4 i j)) * (1 + r) :=
    fun r hr => lpNorm_euclideanBall_growth_add h23mem h23bound h4bound hr
  have h2345mem := memLp_euclideanBall_family_add h234mem h5mem
  have h2345bound : ∀ r : ℝ, 0 < r →
      lpNorm (pressureP2 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s +
          pressureP3 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s +
          pressureP4 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s +
          pressureP5 (mollifiedBallCutoff x₀ hρ) p s)
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r)) ≤
        ((((∑ i : Fin 3, ∑ j : Fin 3, C2 i j) + (∑ i : Fin 3, ∑ j : Fin 3, C3 i j)) +
          (∑ i : Fin 3, ∑ j : Fin 3, C4 i j)) +
          newtonianPotentialGrowthConstant (lin34CentredPressureLaplacian p x₀ hρ s)
            (vec3EuclideanNorm x₀ + ρ)) * (1 + r) :=
    fun r hr => lpNorm_euclideanBall_growth_add h234mem h234bound h5bound hr
  have h23456mem := memLp_euclideanBall_family_add h2345mem h6mem
  have h23456bound : ∀ r : ℝ, 0 < r →
      lpNorm (pressureP2 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s +
          pressureP3 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s +
          pressureP4 (mollifiedBallCutoff x₀ hρ) (lin34CentredVelocity u x₀ ρ) 0 s +
          pressureP5 (mollifiedBallCutoff x₀ hρ) p s +
          pressureP6 (mollifiedBallCutoff x₀ hρ) p s)
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall (0 : Vec3) r)) ≤
        (((((∑ i : Fin 3, ∑ j : Fin 3, C2 i j) + (∑ i : Fin 3, ∑ j : Fin 3, C3 i j)) +
          (∑ i : Fin 3, ∑ j : Fin 3, C4 i j)) +
          newtonianPotentialGrowthConstant (lin34CentredPressureLaplacian p x₀ hρ s)
            (vec3EuclideanNorm x₀ + ρ)) + (∑ j : Fin 3, 2 * C6 j)) * (1 + r) :=
    fun r hr => lpNorm_euclideanBall_growth_add h2345mem h2345bound h6bound hr
  have hC2 : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, C2 i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      newtonianPotentialGrowthConstant_nonneg (lin34CentredTensorHessian u x₀ hρ s i j)
        (vec3EuclideanNorm x₀ + ρ)
  have hC3 : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, C3 i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      newtonianDerivativePotentialGrowthConstant_nonneg j hR₀
        (lin34CentredTensorGradientI u x₀ hρ s i j)
  have hC4 : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, C4 i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      newtonianDerivativePotentialGrowthConstant_nonneg i hR₀
        (lin34CentredTensorGradientJ u x₀ hρ s i j)
  have hC5 : 0 ≤ newtonianPotentialGrowthConstant (lin34CentredPressureLaplacian p x₀ hρ s)
      (vec3EuclideanNorm x₀ + ρ) :=
    newtonianPotentialGrowthConstant_nonneg (lin34CentredPressureLaplacian p x₀ hρ s)
      (vec3EuclideanNorm x₀ + ρ)
  have hC6 : 0 ≤ ∑ j : Fin 3, 2 * C6 j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (by norm_num)
      (newtonianDerivativePotentialGrowthConstant_nonneg j hR₀
        (lin34CentredPressureGradient p x₀ hρ s j))
  have hCnonneg : 0 ≤ (((((∑ i : Fin 3, ∑ j : Fin 3, C2 i j) +
      (∑ i : Fin 3, ∑ j : Fin 3, C3 i j)) +
      (∑ i : Fin 3, ∑ j : Fin 3, C4 i j)) +
      newtonianPotentialGrowthConstant (lin34CentredPressureLaplacian p x₀ hρ s)
        (vec3EuclideanNorm x₀ + ρ)) + (∑ j : Fin 3, 2 * C6 j)) := by
    linarith only [hC2, hC3, hC4, hC5, hC6]
  refine ⟨_, hCnonneg, ?_, ?_⟩
  · intro R hR
    exact h23456mem R hR
  · intro R hR
    exact h23456bound R hR

end CKN
