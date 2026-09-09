/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelGevrey

@[expose] public section

/-!
# A frozen bounded-operator equation for the actual forward solve

At a chosen parameter x, Duhamel gives an exact equation with coefficient
Id minus the fixed Green operator applied to the coefficient difference.
Its coefficient at x is exactly Id. Thus the fixed-Sobolev inverse estimate
can use the identity inverse; it never requires a norm for a profile-weighted
raw time primitive.
-/

noncomputable section

namespace EulerLinearDuhamel

open Set ContinuousLinearMap EulerContinuousTimeIntegral EulerContinuousTimeWeight
  EulerContinuousPathCalculus
open scoped ContDiff

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (T : ℝ) (hT : 0 ≤ T) (B : P → C(Icc (0 : ℝ) T,E →L[ℝ] E))
  (U : ∀ x, Evolution T hT (B x))
  (g : C(Icc (0 : ℝ) T,ℝ)) (hg : ∀ t, 0 < g t)

private local instance : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
private local instance : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) T,E) := inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) T,E) := inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) T,E →L[ℝ] E) := inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) T,E →L[ℝ] E) := inferInstance
private local instance : NormedAddCommGroup (C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 : ℝ) T,E)) :=
  inferInstance
private local instance : NormedSpace ℝ (C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 : ℝ) T,E)) :=
  inferInstance

/-- The exact frozen coefficient, using the actual weighted Green operator. -/
def frozenOperator (x y : P) : C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 : ℝ) T,E) :=
  ContinuousLinearMap.id ℝ _ - ((U x).weightedForcing g hg).comp (multiplier (B y)-multiplier (B x))

/-- The exact transformed data under the fixed homogeneous and Green operators. -/
def frozenForcing (f : P → C(Icc (0 : ℝ) T,E)) (a₀ : P → E) (x y : P) : C(Icc (0 : ℝ) T,E) :=
  (U x).weightedInitial g hg (a₀ y)+(U x).weightedForcing g hg (f y)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- The frozen coefficient at its base parameter is the identity. -/
theorem frozenOperator_self (x : P) :
    frozenOperator T hT B U g hg x x = ContinuousLinearMap.id ℝ _ := by
  simp only [frozenOperator, sub_self, comp_zero, sub_zero]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- The actual normalized Duhamel solution satisfies this bounded-operator equation. -/
theorem frozenOperator_equation (f : P → C(Icc (0 : ℝ) T,E)) (a₀ : P → E) (x y : P) :
    frozenOperator T hT B U g hg x y ((U y).weightedSolution g hg (f y) (a₀ y)) =
      frozenForcing T hT B U g hg f a₀ x y := by
  have hd : multiplier (B y-B x) = multiplier (B y)-multiplier (B x) := by
    ext p t
    rfl
  have h := (U x).weighted_frozen_solution g hg (U y) (f y) (a₀ y)
  rw [hd, map_add] at h
  change (U y).weightedSolution g hg (f y) (a₀ y)-
      (U x).weightedForcing g hg ((multiplier (B y)-multiplier (B x))
        ((U y).weightedSolution g hg (f y) (a₀ y))) = _
  exact sub_eq_iff_eq_add.mpr (by simpa only [frozenForcing, add_assoc] using h)

/-- The frozen coefficient is genuinely smooth in the translated coefficients. -/
theorem frozenOperator_contDiff (hB : ContDiff ℝ ∞ B) (x : P) :
    ContDiff ℝ ∞ (frozenOperator T hT B U g hg x) :=
  contDiff_const.sub (contDiff_const.clm_comp ((contDiff_multiplier B hB).sub contDiff_const))

/-- The transformed data retain the actual parameter smoothness of the original data. -/
theorem frozenForcing_contDiff (f : P → C(Icc (0 : ℝ) T,E)) (a₀ : P → E)
    (hf : ContDiff ℝ ∞ f) (ha₀ : ContDiff ℝ ∞ a₀) (x : P) :
    ContDiff ℝ ∞ (frozenForcing T hT B U g hg f a₀ x) :=
  (((U x).weightedInitial g hg).contDiff.comp ha₀).add
    (((U x).weightedForcing g hg).contDiff.comp hf)

end EulerLinearDuhamel
