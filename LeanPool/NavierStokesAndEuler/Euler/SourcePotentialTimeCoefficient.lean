/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SourcePotentialCoefficient
public import LeanPool.NavierStokesAndEuler.Euler.PacketNormalTimeMap

@[expose] public section

/-! The actual time coefficient of the vector potential, with uniform factorial bounds. -/

noncomputable section

namespace EulerSourcePotentialCoefficient

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerMeanCoefficients
  EulerPacketCrossProduct EulerSourceNormalCoefficient EulerBoundedFieldCalculus
  EulerOperatorGevreyCalculus EulerGevrey EulerTimeLpGramGevrey EulerVolterraConvolution
open scoped BoundedContinuousFunction ContDiff

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

private local instance : NormedAddCommGroup (Space →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] ℝ) := inferInstance
private local instance : NormedAddCommGroup (ℝ →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (ℝ →L[ℝ] Space) := inferInstance
private local instance : NormedAddCommGroup NormalField := inferInstance
private local instance : NormedSpace ℝ NormalField := inferInstance
private local instance : NormedAddCommGroup (Space →ᵇ ℝ →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ ℝ →L[ℝ] Space) := inferInstance
private local instance : NormedAddCommGroup (ℝ →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ (ℝ →L[ℝ] ℝ) := inferInstance
private local instance : NormedAddCommGroup (Space →ᵇ ℝ →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ ℝ →L[ℝ] ℝ) := inferInstance
private local instance : NormedAddCommGroup C(K,NormalField) := inferInstance
private local instance : NormedSpace ℝ C(K,NormalField) := inferInstance
private local instance : NormedAddCommGroup C(K,Space →ᵇ ℝ →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ C(K,Space →ᵇ ℝ →L[ℝ] Space) := inferInstance
private local instance : NormedAddCommGroup C(K,Space →ᵇ ℝ →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ C(K,Space →ᵇ ℝ →L[ℝ] ℝ) := inferInstance
private local instance : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
private local instance : NormedAddCommGroup PotentialField := inferInstance
private local instance : NormedSpace ℝ PotentialField := inferInstance
private local instance : NormedAddCommGroup C(K,PotentialField) := inferInstance
private local instance : NormedSpace ℝ C(K,PotentialField) := inferInstance

def timeNormalPath (N : C(K,NormalField)) (Q₁ : C(K,Space →ᵇ ℝ →L[ℝ] Space)) : C(K,NormalField) :=
  pathCompositionMap (pathCompositionMap N (pathAdjointMap N)) (pathAdjointMap Q₁) -
    (2 : ℝ) • pathCompositionMap (pathCompositionMap N Q₁) N

theorem timeNormalPath_apply (N : C(K,NormalField)) (Q₁ : C(K,Space →ᵇ ℝ →L[ℝ] Space))
    (t : K) (y : Space) : timeNormalPath N Q₁ t y = normalTimeMap (N t y) (Q₁ t y) := rfl

theorem timeNormalPath_translation (N : C(K,NormalField)) (Q₁ : C(K,Space →ᵇ ℝ →L[ℝ] Space))
    (a : Space) : translateCoefficientPath (timeNormalPath N Q₁) a =
      timeNormalPath (translateCoefficientPath N a) (translateCoefficientPath Q₁ a) := by
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro y
  rfl

section Families

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (N : X → C(K,NormalField)) (Q₁ : X → C(K,Space →ᵇ ℝ →L[ℝ] Space))
  (hN : ContDiff ℝ ∞ N) (hQ₁ : ContDiff ℝ ∞ Q₁)

include hN hQ₁ in
theorem timeNormalPath_contDiff : ContDiff ℝ ∞ (fun a => timeNormalPath (N a) (Q₁ a)) := by
  have hNa := (pathAdjointMap (α := Space) (K := K) (U := Space) (E := ℝ)).contDiff.comp hN
  have hQa := (pathAdjointMap (α := Space) (K := K) (U := ℝ) (E := Space)).contDiff.comp hQ₁
  have hNN := pathComposition_contDiff N (fun x => pathAdjointMap (N x)) hN hNa
  have hNQ := pathComposition_contDiff N Q₁ hN hQ₁
  have hA := pathComposition_contDiff
    (fun x => pathCompositionMap (N x) (pathAdjointMap (N x)))
    (fun x => pathAdjointMap (Q₁ x)) hNN hQa
  have hB := pathComposition_contDiff (fun x => pathCompositionMap (N x) (Q₁ x)) N hNQ hN
  exact hA.sub (hB.const_smul 2)

include hN hQ₁ in
theorem timeNormalPath_bound (R C D : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbN : ∀ n a, ‖iteratedFDeriv ℝ n N a‖ ≤ C*majorant R 0 n)
    (hbQ₁ : ∀ n a, ‖iteratedFDeriv ℝ n Q₁ a‖ ≤ D*majorant R 0 n)
    (n : ℕ) (a : X) :
    ‖iteratedFDeriv ℝ n (fun x => timeNormalPath (N x) (Q₁ x)) a‖ ≤
      (27*C^2*D)*majorant R 0 n := by
  let A := fun x => pathCompositionMap (pathCompositionMap (N x) (pathAdjointMap (N x)))
    (pathAdjointMap (Q₁ x))
  let B := fun x => pathCompositionMap (pathCompositionMap (N x) (Q₁ x)) (N x)
  have hNa := (pathAdjointMap (α := Space) (K := K) (U := Space) (E := ℝ)).contDiff.comp hN
  have hQa := (pathAdjointMap (α := Space) (K := K) (U := ℝ) (E := Space)).contDiff.comp hQ₁
  have hNN := pathComposition_contDiff N (fun x => pathAdjointMap (N x)) hN hNa
  have hNQ := pathComposition_contDiff N Q₁ hN hQ₁
  have hA : ContDiff ℝ ∞ A := pathComposition_contDiff _ _ hNN hQa
  have hB : ContDiff ℝ ∞ B := pathComposition_contDiff _ _ hNQ hN
  have hbNa := contraction_bound (pathAdjointMap (α := Space) (K := K) (U := Space) (E := ℝ))
    pathAdjointMap_norm N hN R C hR hC 0 hbN
  have hbQa := contraction_bound (pathAdjointMap (α := Space) (K := K) (U := ℝ) (E := Space))
    pathAdjointMap_norm Q₁ hQ₁ R D hR hD 0 hbQ₁
  have hbNN := pathComposition_bound N (fun x => pathAdjointMap (N x)) hN hNa
    R C C hR hC hC 0 0 hbN hbNa
  have hbNQ := pathComposition_bound N Q₁ hN hQ₁ R C D hR hC hD 0 0 hbN hbQ₁
  have hbA : ∀ j x, ‖iteratedFDeriv ℝ j A x‖ ≤ (3*(3*C*C)*D)*majorant R 0 j :=
    pathComposition_bound _ _ hNN hQa R (3*C*C) D hR (by positivity) hD 0 0 hbNN hbQa
  have hbB : ∀ j x, ‖iteratedFDeriv ℝ j B x‖ ≤ (3*(3*C*D)*C)*majorant R 0 j :=
    pathComposition_bound _ _ hNQ hN R (3*C*D) C hR (by positivity) hC 0 0 hbNQ hbN
  have hb₂B (j : ℕ) (x : X) :
      ‖iteratedFDeriv ℝ j (fun y => (2 : ℝ) • B y) x‖ ≤
        (2*(3*(3*C*D)*C))*majorant R 0 j := by
    rw [iteratedFDeriv_const_smul_apply' (hB.contDiffAt.of_le (by simp)), norm_smul]
    norm_num only [Real.norm_ofNat]
    exact (mul_le_mul_of_nonneg_left (hbB j x) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
  have h := sub_bound A (fun y => (2 : ℝ) • B y) hA (hB.const_smul 2)
    R (3*(3*C*C)*D) (2*(3*(3*C*D)*C)) 0 hbA hb₂B n a
  exact h.trans_eq (by ring)

end Families

variable (m m₁ : SmoothCoefficientPath K Space) (c : ℝ) (hc : 0 < c)
  (hm : ∀ t y, c ≤ ‖m.field t y‖^2)

def potentialTimeCoefficient : C(K,PotentialField) :=
  potentialPathMap (timeNormalPath (normalFunctional m c hc hm) (normalColumn m₁).field)

theorem potentialTimeCoefficient_apply (t : K) (y : Space) :
    potentialTimeCoefficient m m₁ c hc hm t y =
      potentialMultiplierDerivative (m.field t y) (m₁.field t y) := by
  have hn : m.field t y ≠ 0 := by
    intro hz
    have h := hm t y
    rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
    linarith
  exact normalTimeMap_potential (m.field t y) (m₁.field t y)
    (normalFunctional m c hc hm t y) hn (normalFunctional_apply m c hc hm t y)

theorem potentialTimeCoefficient_translation :
    translateCoefficientPath (potentialTimeCoefficient m m₁ c hc hm) =
      fun a => potentialPathMap (timeNormalPath
        (translateCoefficientPath (normalFunctional m c hc hm) a)
        (translateCoefficientPath (normalColumn m₁).field a)) := by
  funext a
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro y
  rfl

theorem potentialTimeCoefficient_translation_contDiff :
    ContDiff ℝ ∞ (translateCoefficientPath (potentialTimeCoefficient m m₁ c hc hm)) := by
  rw [potentialTimeCoefficient_translation]
  have h := timeNormalPath_contDiff _ _
    (normalFunctional_translation_contDiff m c hc hm) (normalColumn m₁).translation_contDiff
  exact (potentialPathMap (K := K)).contDiff.comp h

/-- The derivative coefficient is polynomial in the already constructed normal functional. -/
theorem potentialTimeCoefficient_translation_bound (R C D : ℝ)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbN : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath (normalFunctional m c hc hm)) a‖ ≤
      C*majorant R 0 n)
    (hbm₁ : ∀ n t y, ‖iteratedFDeriv ℝ n (m₁.field t : Space → Space) y‖ ≤ D*majorant R 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (potentialTimeCoefficient m m₁ c hc hm)) a‖ ≤
      (27*C^2*D)*majorant R 0 n := by
  have hQ (j : ℕ) (x : Space) :
      ‖iteratedFDeriv ℝ j (translateCoefficientPath (normalColumn m₁).field) x‖ ≤ D*majorant R 0 j
        := by
    apply (normalColumn m₁).norm_iteratedFDeriv_translation_le j (D*majorant R 0 j)
      (mul_nonneg hD (majorant_nonneg R hR 0 j))
    intro t y
    exact SmoothCoefficientPath.map_derivative_bound
      (ContinuousLinearMap.toSpanSingletonLIE ℝ Space).toLinearIsometry.toContinuousLinearMap
      (ContinuousLinearMap.toSpanSingletonLIE ℝ
        Space).toLinearIsometry.norm_toContinuousLinearMap_le
      m₁ j (D*majorant R 0 j) (hbm₁ j) t y
  rw [potentialTimeCoefficient_translation]
  exact contraction_bound (potentialPathMap (K := K)) potentialPathMap_norm _
    (timeNormalPath_contDiff _ _ (normalFunctional_translation_contDiff m c hc hm)
      (normalColumn m₁).translation_contDiff) R (27*C^2*D) hR (by positivity) 0
    (timeNormalPath_bound _ _ (normalFunctional_translation_contDiff m c hc hm)
      (normalColumn m₁).translation_contDiff R C D hR hC hD hbN hQ) n a

end EulerSourcePotentialCoefficient
