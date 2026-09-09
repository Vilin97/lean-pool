/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevDerivatives

/-! Operator-norm continuity into a finite Sobolev space is equivalent
to continuity of all its actual derivative-coordinate operators. -/

@[expose] public section


noncomputable section

namespace EulerCylinderSobolevSpace

open EulerLiftedGradientSpace

variable (P : ℝ) [Fact (0 < P)] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Word composition, defined pointwise by `(wordOperator P w).comp A`. -/
def wordComposition (q : ℕ) (A : E →L[ℝ] SobolevSpace P q) :
    SobolevWord q → E →L[ℝ] LiftL2 P := fun w => (wordOperator P w).comp A

theorem norm_wordComposition (q : ℕ) (A : E →L[ℝ] SobolevSpace P q) :
    ‖wordComposition P q A‖ = ‖A‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg A)).mpr
    intro w
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
    intro u
    exact (word_norm_le P (A u) w).trans (A.le_opNorm u)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro u
    change ‖(A u).val‖ ≤ ‖wordComposition P q A‖*‖u‖
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg u))).mpr
    intro w
    exact ((wordComposition P q A w).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right (norm_le_pi_norm (wordComposition P q A) w) (norm_nonneg u))

theorem wordComposition_isometry (q : ℕ) :
    Isometry (wordComposition (E := E) P q) := by
  apply Isometry.of_dist_eq
  intro A B
  rw [dist_eq_norm,dist_eq_norm]
  have he : wordComposition P q A-wordComposition P q B = wordComposition P q (A-B) := by
    funext w
    apply ContinuousLinearMap.ext
    intro u
    rfl
  rw [he,norm_wordComposition]

theorem continuous_of_wordCompositions {K : Type*} [TopologicalSpace K]
    (q : ℕ) (A : K → E →L[ℝ] SobolevSpace P q)
    (hA : ∀ w : SobolevWord q, Continuous (fun t => (wordOperator P w).comp (A t))) :
    Continuous A :=
  (wordComposition_isometry (E := E) P q).comp_continuous_iff.mp (continuous_pi hA)

theorem continuous_of_valueComposition {K : Type*} [TopologicalSpace K]
    (A : K → E →L[ℝ] SobolevSpace P 0)
    (hA : Continuous (fun t => (valueOperator P 0).comp (A t))) : Continuous A := by
  apply continuous_of_wordCompositions P 0 A
  rintro ⟨⟨n,hn⟩,w⟩
  have hn0 : n=0 := by omega
  subst n
  have hw : w=Fin.elim0 := Subsingleton.elim _ _
  subst w
  exact hA

theorem continuous_of_value_and_derivatives {K : Type*} [TopologicalSpace K]
    (q : ℕ) (A : K → E →L[ℝ] SobolevSpace P (q + 1))
    (hA : Continuous (fun t => (valueOperator P (q + 1)).comp (A t)))
    (hD : ∀ i : Fin 4, Continuous (fun t => (derivativeOperator P q i).comp (A t))) :
    Continuous A := by
  apply continuous_of_wordCompositions P (q+1) A
  rintro ⟨⟨n,hn⟩,w⟩
  cases n with
  | zero =>
    have hw : w=Fin.elim0 := Subsingleton.elim _ _
    subst w
    exact hA
  | succ n =>
    let w₀ : SobolevWord q := ⟨⟨n,by omega⟩,Fin.init w⟩
    let i : Fin 4 := w (Fin.last n)
    have he : wordOperator P ⟨⟨n+1,hn⟩,w⟩ =
        (wordOperator P w₀).comp (derivativeOperator P q i) := by
      apply ContinuousLinearMap.ext
      intro u
      change u.val ⟨⟨n+1,hn⟩,w⟩ = u.val (derivativeIndex i w₀)
      simp only [derivativeIndex,w₀,i,Fin.snoc_init_self]
    rw [he]
    simpa only [ContinuousLinearMap.comp_assoc] using
      (hD i).const_clm_comp (wordOperator P w₀)

end EulerCylinderSobolevSpace
