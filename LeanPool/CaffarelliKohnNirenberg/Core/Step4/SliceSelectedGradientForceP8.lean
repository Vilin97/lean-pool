/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.KernelAllOrders
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsCylinder
public import LeanPool.CaffarelliKohnNirenberg.Pressure.DecompositionPotentials

/-! # The inner-ball gradient of the second force potential `p₈`

The local pressure decomposition `eq:pk` writes the pressure on a ball as
`p₁ + (p₂ + … + p₆) + (p₇ + p₈)`.  The last summand

  `pressureP8 η f s = fun x => -∑ j, pressureNewtonianPotential
      (fun y => spatialDeriv η j y * f (y, s) j) x`

is the second force potential.  With `η = mollifiedBallCutoff x₀ hρ` its density
`spatialDeriv η j · * f (·, s) j` is carried by the cutoff annulus
`pressureAnnulus x₀ ρ = B(x₀, 3ρ/4) \ B(x₀, 13ρ/20)`, so on the inner ball
`B(x₀, ρ/2)` the Newtonian kernel is smooth in the evaluation point and the
potential is `C¹`, with the far-field gradient bound of `eq:har-Ck` and the
separation `3ρ/20` of `lem:cutoff`.  Display (3.5) of the pressure-gradient
section consumes exactly that: the classical gradient of `p₈` on the inner ball,
measured in the Euclidean norm, is controlled by the `L¹` size of the annular
density with a constant that is uniform in the ball and its centre.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN.Core.Step4

/-- The explicit round Euclidean ball of positive radius agrees with the native
vector ball. -/
private lemma euclideanBall_eq_vec3Ball_of_pos {x₀ : Vec3} {r : ℝ} (hr : 0 < r) :
    euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  change (x ∈ euclideanBall x₀ r) ↔ vec3EuclideanNorm (x - x₀) < r
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
    (mem_euclideanBall_iff_vecEuclideanNorm_lt hr)

/-- A point outside the cutoff annulus `pressureAnnulus x₀ ρ` lies outside the
slightly smaller annulus on which the cutoff derivatives can fail to vanish, so
every spatial derivative of the cutoff is zero there (`lem:cutoff`). -/
private lemma spatialDeriv_mollifiedBallCutoff_eq_zero_of_notMem_pressureAnnulus
    {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) {y : Vec3}
    (hy : y ∉ CKN.pressureAnnulus x₀ ρ) (i : Fin 3) :
    spatialDeriv (mollifiedBallCutoff x₀ hρ) i y = 0 := by
  have houter : euclideanBall x₀ (3 * ρ / 4) = vec3Ball x₀ (3 * ρ / 4) :=
    euclideanBall_eq_vec3Ball_of_pos (by positivity)
  have hin : euclideanBall x₀ (13 * ρ / 20) = vec3Ball x₀ (13 * ρ / 20) :=
    euclideanBall_eq_vec3Ball_of_pos (by positivity)
  have hyann : y ∉ euclideanBall x₀ (3 * ρ / 4) \
      euclideanClosedBall x₀ (13 * ρ / 20) := by
    intro hyann
    refine hy ⟨by rw [← houter]; exact hyann.1, fun hyinner => hyann.2 ?_⟩
    refine (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2 ?_
    have hyinner' : y ∈ euclideanBall x₀ (13 * ρ / 20) := by
      rw [hin]; exact hyinner
    exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hyinner').le
  exact (pressure_cutoff_derivatives_vanish x₀ hρ hyann).1 i

/-- The uniform constant of the inner-ball gradient bound for the annular
Newtonian potential, read off from the all-order kernel estimate of `eq:har-Ck`
at order one.  It depends on no parameter of the ball geometry. -/
noncomputable def sliceForcePotentialConstant : ℝ :=
  (CKN.Foundation.Heat.exists_norm_iteratedFDeriv_pressureNewtonianPotential_annulus_le
    1).choose

/-- The constant of the inner-ball gradient bound is nonnegative. -/
theorem sliceForcePotentialConstant_nonneg : 0 ≤ sliceForcePotentialConstant :=
  (CKN.Foundation.Heat.exists_norm_iteratedFDeriv_pressureNewtonianPotential_annulus_le
    1).choose_spec.1

/-- The first derivative of the annular Newtonian potential on the inner ball is
controlled by the `L¹` size of the density times the inverse square of the
separation `3ρ/20` of `lem:cutoff`: this is `eq:har-Ck` at order one, in the
shape display (3.5) of the pressure-gradient section consumes. -/
theorem norm_fderiv_pressureNewtonianPotential_annulus_le
    {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) {g : Vec3 → ℝ} (hg : Integrable g volume)
    (hg0 : ∀ y : Vec3, y ∉ CKN.pressureAnnulus x₀ ρ → g y = 0)
    {x : Vec3} (hx : x ∈ vec3Ball x₀ (ρ / 2)) :
    ‖fderiv ℝ (CKN.pressureNewtonianPotential g) x‖ ≤
      sliceForcePotentialConstant * ((3 * ρ / 20) ^ 2)⁻¹ * ∫ y : Vec3, ‖g y‖ := by
  have h : ‖iteratedFDeriv ℝ 1 (CKN.pressureNewtonianPotential g) x‖ ≤
      sliceForcePotentialConstant * ((3 * ρ / 20) ^ (1 + 1))⁻¹ *
        ∫ y : Vec3, ‖g y‖ :=
    (CKN.Foundation.Heat.exists_norm_iteratedFDeriv_pressureNewtonianPotential_annulus_le
      1).choose_spec.2 x₀ ρ hρ g hg hg0 x hx
  have hpow : ((3 * ρ / 20) ^ (1 + 1))⁻¹ = ((3 * ρ / 20) ^ 2)⁻¹ := by norm_num
  rw [hpow] at h
  rwa [norm_iteratedFDeriv_one] at h

/-- The second force potential `p₈` of the local pressure decomposition `eq:pk`
is `C¹` on the inner ball `B(x₀, ρ/2)` whenever its density is integrable: the
density of the cutoff is carried by the annulus `pressureAnnulus x₀ ρ`, on which
the potential is smooth (`eq:har-Ck`). -/
theorem contDiffOn_pressureP8_halfBall
    {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) {f : ParabolicPoint → Vec3} {s : ℝ}
    (hint : ∀ j : Fin 3, Integrable
      (fun y : Vec3 => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j)
      volume) :
    ContDiffOn ℝ (1 : ℕ∞) (CKN.pressureP8 (mollifiedBallCutoff x₀ hρ) f s)
      (vec3Ball x₀ (ρ / 2)) := by
  have hone : ((1 : ℕ) : WithTop ℕ∞) = ((1 : ℕ∞) : WithTop ℕ∞) := by norm_cast
  change ContDiffOn ℝ (1 : ℕ∞)
    (fun x => -∑ j, CKN.pressureNewtonianPotential
      (fun y : Vec3 => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j) x)
    (vec3Ball x₀ (ρ / 2))
  refine (ContDiffOn.sum (s := Finset.univ) ?_).neg
  intro j _
  exact hone ▸ CKN.Foundation.Heat.contDiffOn_pressureNewtonianPotential_annulus
    (x₀ := x₀) (ρ := ρ) hρ (hint j)
    (fun y hy => by
      rw [spatialDeriv_mollifiedBallCutoff_eq_zero_of_notMem_pressureAnnulus hρ hy j,
        zero_mul])
    1

/-- Display (3.5) of the pressure-gradient section for the second force
potential: on the inner ball `B(x₀, ρ/2)` the Euclidean norm of the classical
gradient of `p₈` is bounded by `400 · c · A · ρ⁻²`, where `A` bounds the `L¹`
sizes of the annular components of the density and `c` is the uniform constant
of `eq:har-Ck` at order one. -/
theorem vec3EuclideanNorm_classicalGradient_pressureP8_le
    {x₀ : Vec3} {ρ A : ℝ} (hρ : 0 < ρ) (hA0 : 0 ≤ A)
    {f : ParabolicPoint → Vec3} {s : ℝ}
    (hint : ∀ j : Fin 3, Integrable
      (fun y : Vec3 => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j)
      volume)
    (hA : ∀ j : Fin 3, (∫ y : Vec3,
      ‖spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j‖) ≤ A)
    {x : Vec3} (hx : x ∈ vec3Ball x₀ (ρ / 2)) :
    vec3EuclideanNorm
        (classicalGradient (CKN.pressureP8 (mollifiedBallCutoff x₀ hρ) f s) x) ≤
      400 * sliceForcePotentialConstant * A * (ρ ^ 2)⁻¹ := by
  classical
  set G : Fin 3 → Vec3 → ℝ :=
    fun j y => spatialDeriv (mollifiedBallCutoff x₀ hρ) j y * f (y, s) j with hG
  have hg : ∀ j : Fin 3, Integrable (G j) volume := by
    intro j
    rw [hG]
    exact hint j
  have hA' : ∀ j : Fin 3, (∫ y : Vec3, ‖G j y‖) ≤ A := by
    intro j
    rw [hG]
    exact hA j
  have hg0 : ∀ j : Fin 3, ∀ y : Vec3, y ∉ CKN.pressureAnnulus x₀ ρ → G j y = 0 := by
    intro j y hy
    simp only [hG]
    rw [spatialDeriv_mollifiedBallCutoff_eq_zero_of_notMem_pressureAnnulus hρ hy j,
      zero_mul]
  have hone : ((1 : ℕ) : WithTop ℕ∞) = ((1 : ℕ∞) : WithTop ℕ∞) := by norm_cast
  have hcont : ∀ j : Fin 3, ContDiffOn ℝ (1 : ℕ∞)
      (CKN.pressureNewtonianPotential (G j)) (vec3Ball x₀ (ρ / 2)) := by
    intro j
    exact hone ▸ CKN.Foundation.Heat.contDiffOn_pressureNewtonianPotential_annulus
      (x₀ := x₀) (ρ := ρ) hρ (hg j) (hg0 j) 1
  have hdiff : ∀ j : Fin 3,
      DifferentiableAt ℝ (CKN.pressureNewtonianPotential (G j)) x := by
    intro j
    exact ((hcont j).differentiableOn_one).differentiableAt
      ((isOpen_vec3Ball x₀ (ρ / 2)).mem_nhds hx)
  have hP8 : CKN.pressureP8 (mollifiedBallCutoff x₀ hρ) f s =
      fun y => -∑ j, CKN.pressureNewtonianPotential (G j) y := by
    unfold CKN.pressureP8
    rw [hG]
  have hfderiv : fderiv ℝ (CKN.pressureP8 (mollifiedBallCutoff x₀ hρ) f s) x =
      -(∑ j, fderiv ℝ (CKN.pressureNewtonianPotential (G j)) x) := by
    have hsum : HasFDerivAt (fun y => ∑ j, CKN.pressureNewtonianPotential (G j) y)
        (∑ j, fderiv ℝ (CKN.pressureNewtonianPotential (G j)) x) x := by
      simpa using HasFDerivAt.fun_sum (u := Finset.univ)
        (fun j _ => (hdiff j).hasFDerivAt)
    rw [hP8]
    exact hsum.neg.fderiv
  have hcinv : 0 ≤ sliceForcePotentialConstant * ((3 * ρ / 20) ^ 2)⁻¹ :=
    mul_nonneg sliceForcePotentialConstant_nonneg (inv_nonneg.2 (sq_nonneg _))
  have hterm : ∀ j : Fin 3,
      ‖fderiv ℝ (CKN.pressureNewtonianPotential (G j)) x‖ ≤
        sliceForcePotentialConstant * ((3 * ρ / 20) ^ 2)⁻¹ * A := by
    intro j
    exact (norm_fderiv_pressureNewtonianPotential_annulus_le (x₀ := x₀) (ρ := ρ) hρ
      (hg := hg j) (hg0 := hg0 j) (hx := hx)).trans
      (mul_le_mul_of_nonneg_left (hA' j) hcinv)
  have hfd_le : ‖fderiv ℝ (CKN.pressureP8 (mollifiedBallCutoff x₀ hρ) f s) x‖ ≤
      3 * (sliceForcePotentialConstant * ((3 * ρ / 20) ^ 2)⁻¹ * A) := by
    rw [hfderiv, norm_neg]
    refine (norm_sum_le Finset.univ _).trans ?_
    have hconst : (∑ _j : Fin 3,
        sliceForcePotentialConstant * ((3 * ρ / 20) ^ 2)⁻¹ * A) =
        3 * (sliceForcePotentialConstant * ((3 * ρ / 20) ^ 2)⁻¹ * A) := by
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← hconst]
    exact Finset.sum_le_sum (fun j _ => hterm j)
  have hbnd_nonneg : 0 ≤ 400 / 3 * sliceForcePotentialConstant * A * (ρ ^ 2)⁻¹ :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) sliceForcePotentialConstant_nonneg) hA0)
      (inv_nonneg.2 (sq_nonneg ρ))
  have hkey : 3 * (sliceForcePotentialConstant * ((3 * ρ / 20) ^ 2)⁻¹ * A) =
      400 / 3 * sliceForcePotentialConstant * A * (ρ ^ 2)⁻¹ := by
    have hρne : ρ ≠ 0 := ne_of_gt hρ
    field_simp
    ring
  have hcoord : ∀ i : Fin 3,
      ‖classicalGradient (CKN.pressureP8 (mollifiedBallCutoff x₀ hρ) f s) x i‖ ≤
        400 / 3 * sliceForcePotentialConstant * A * (ρ ^ 2)⁻¹ := by
    intro i
    rw [classicalGradient_apply]
    calc
      ‖(fderiv ℝ (CKN.pressureP8 (mollifiedBallCutoff x₀ hρ) f s) x) (basisVec i)‖
          ≤ ‖fderiv ℝ (CKN.pressureP8 (mollifiedBallCutoff x₀ hρ) f s) x‖ *
              ‖basisVec i‖ :=
            ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ (CKN.pressureP8 (mollifiedBallCutoff x₀ hρ) f s) x‖ * 1 :=
            mul_le_mul_of_nonneg_left (CKN.Foundation.Heat.norm_basisVec_le_one i)
              (norm_nonneg _)
      _ = ‖fderiv ℝ (CKN.pressureP8 (mollifiedBallCutoff x₀ hρ) f s) x‖ := mul_one _
      _ ≤ 3 * (sliceForcePotentialConstant * ((3 * ρ / 20) ^ 2)⁻¹ * A) := hfd_le
      _ = 400 / 3 * sliceForcePotentialConstant * A * (ρ ^ 2)⁻¹ := hkey
  have hgrad_norm : ‖classicalGradient (CKN.pressureP8 (mollifiedBallCutoff x₀ hρ) f s) x‖ ≤
      400 / 3 * sliceForcePotentialConstant * A * (ρ ^ 2)⁻¹ :=
    (pi_norm_le_iff_of_nonneg hbnd_nonneg).2 hcoord
  have heuc : spaceEuclideanNorm
      (classicalGradient (CKN.pressureP8 (mollifiedBallCutoff x₀ hρ) f s) x) =
      vec3EuclideanNorm
        (classicalGradient (CKN.pressureP8 (mollifiedBallCutoff x₀ hρ) f s) x) := rfl
  have hnorm_le := euclideanNorm_le_three_mul_space_norm
    (classicalGradient (CKN.pressureP8 (mollifiedBallCutoff x₀ hρ) f s) x)
  rw [heuc] at hnorm_le
  calc
    vec3EuclideanNorm (classicalGradient (CKN.pressureP8 (mollifiedBallCutoff x₀ hρ) f s) x)
        ≤ 3 * ‖classicalGradient (CKN.pressureP8 (mollifiedBallCutoff x₀ hρ) f s) x‖ :=
          hnorm_le
    _ ≤ 3 * (400 / 3 * sliceForcePotentialConstant * A * (ρ ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left hgrad_norm (by norm_num)
    _ = 400 * sliceForcePotentialConstant * A * (ρ ^ 2)⁻¹ := by ring

end CKN.Core.Step4
