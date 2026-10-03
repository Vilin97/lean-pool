/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelOperator
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeWeight

/-!
# Duhamel operators in the source's time profile

The bounded Green operator in the normalized continuous-path space inherits
its constant directly from the relative homogeneous propagator bound. The
frozen-coefficient identity is exact and will be differentiated for quantitative
parameter estimates; no norm of the weighted primitive is used.
-/

@[expose] public section


noncomputable section


namespace EulerLinearDuhamel

open Set ContinuousLinearMap EulerVolterraConvolution EulerContinuousTimeIntegral
  EulerContinuousTimeWeight

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {T : ℝ} {hT : 0 ≤ T} {B : C(Icc (0 : ℝ) T, E →L[ℝ] E)}

namespace Evolution

variable (U : Evolution T hT B) (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)

/-- The actual homogeneous data map, normalized by the profile. -/
def weightedInitial : E →L[ℝ] C(Icc (0 : ℝ) T,E) :=
  (EulerContinuousTimeWeight.normalize g hg).comp U.initialOperator

/-- The actual Green map for forcing measured in the source profile. -/
def weightedForcing : C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 : ℝ) T,E) :=
  (EulerContinuousTimeWeight.normalize g hg).comp (U.forcingOperator.comp (weight g))

omit [CompleteSpace E] in
/-- The initial-data norm uses just the relative propagator constant. -/
theorem weightedInitial_norm (hg₀ : g ⟨0, le_rfl, hT⟩ = 1) (C : ℝ) (hC : 0 ≤ C)
    (hU : ∀ t s : Icc (0 : ℝ) T, s ≤ t → ‖U.propagator t s‖ ≤ C*g t/g s) :
    ‖U.weightedInitial g hg‖ ≤ C := by
  apply opNorm_le_bound _ hC
  intro a₀
  apply normalize_norm_le g hg (U.initialOperator a₀) (C*‖a₀‖) (mul_nonneg hC (norm_nonneg a₀))
  intro t
  exact (U.initialOperator_profile_bound a₀ g hg₀ C hU t).trans_eq (by ring)

/-- The Green-operator norm is interval length times the relative propagator
constant. Neither the maximum nor minimum of the profile appears. -/
theorem weightedForcing_norm (hg₀ : g ⟨0, le_rfl, hT⟩ = 1) (C : ℝ) (hC : 0 ≤ C)
    (hU : ∀ t s : Icc (0 : ℝ) T, s ≤ t → ‖U.propagator t s‖ ≤ C*g t/g s) :
    ‖U.weightedForcing g hg‖ ≤ C*T := by
  apply opNorm_le_bound _ (mul_nonneg hC hT)
  intro f
  apply normalize_norm_le g hg (U.forcingOperator (weight (E := E) g f)) (C*T*‖f‖)
    (mul_nonneg (mul_nonneg hC hT) (norm_nonneg f))
  intro t
  have hp := U.forcingOperator_profile_bound (weight (E := E) g f) g hg hg₀ C ‖f‖ hC hU
    (fun s => (weight_pointwise_bound g (fun s => (hg s).le) f s).trans_eq (mul_comm _ _)) t
  have ht := mul_le_mul_of_nonneg_right t.property.2
    (mul_nonneg (mul_nonneg hC (hg t).le) (norm_nonneg f))
  nlinarith only [hT, hp, ht]

/-- The normalized constructed path, with normalized forcing as input. -/
def weightedSolution (f : C(Icc (0 : ℝ) T, E)) (a₀ : E) : C(Icc (0 : ℝ) T,E) :=
  EulerContinuousTimeWeight.normalize (E := E) g hg (U.solution (weight (E := E) g f) a₀)

/-- The normalized solution is still exactly the two actual data maps. -/
theorem weightedSolution_eq (f : C(Icc (0 : ℝ) T, E)) (a₀ : E) :
    U.weightedSolution g hg f a₀ = U.weightedInitial g hg a₀ + U.weightedForcing g hg f := by
  unfold weightedSolution
  rw [U.solution_eq_operators, map_add]
  rfl

variable {D : C(Icc (0 : ℝ) T, E →L[ℝ] E)} (V : Evolution T hT D)

/-- Freezing the coefficient is an actual identity of constructed solutions. -/
theorem frozen_solution (f : C(Icc (0 : ℝ) T, E)) (a₀ : E) :
    V.solution f a₀ = U.initialOperator a₀ +
      U.forcingOperator (f + multiplier (D-B) (V.solution f a₀)) := by
  rw [← U.solution_eq_operators]
  ext t
  apply U.solution_unique _ a₀ (V.solutionReal f a₀) _ (V.solution_initial f a₀) t
  intro s
  have hd := V.solution_derivative f a₀ s
  convert hd using 1
  change B s (V.solution f a₀ s) +
    (f s + (D s-B s) (V.solution f a₀ s)) = D s (V.solution f a₀ s) + f s
  rw [sub_apply]
  abel

/-- The exact frozen identity in the fixed profile-normalized path space. -/
theorem weighted_frozen_solution (f : C(Icc (0 : ℝ) T, E)) (a₀ : E) :
    V.weightedSolution g hg f a₀ = U.weightedInitial g hg a₀ +
      U.weightedForcing g hg (f + multiplier (D-B) (V.weightedSolution g hg f a₀)) := by
  have he := U.frozen_solution V (weight (E := E) g f) a₀
  rw [weightedForcing, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    (weight (E := E) g).map_add, weight_multiplier, weightedSolution, weight_normalize]
  exact (congrArg (EulerContinuousTimeWeight.normalize (E := E) g hg) he).trans
    ((EulerContinuousTimeWeight.normalize (E := E) g hg).map_add _ _)

end Evolution

end EulerLinearDuhamel
