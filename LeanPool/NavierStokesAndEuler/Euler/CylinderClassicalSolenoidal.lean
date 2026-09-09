/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ClassicalDivergence

@[expose] public section

/-! Classical lifted divergence zero implies membership in the actual closed L² constraint space. -/

noncomputable section

namespace EulerCylinderClassicalSolenoidal

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerLiftedGradientSpace
  EulerMetricTransport EulerTransportDerivatives EulerLiftedWeakDerivative
  EulerClassicalPressureCurl EulerLiftedCurl
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]

theorem mem_of_test_integral (κ : ℝ) (m : Vector3) (u : LiftL2 P)
    (h : ∀ φ : LiftDomain P → ℝ,
      (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (localLift P φ x)) →
      (∫ x, inner ℝ (liftedGradient P κ m φ x) (u x) ∂liftMeasure P) = 0) :
    u ∈ divergenceFreeSpace P κ m := by
  let K := (innerSL ℝ u).ker
  have hg : Submodule.span ℝ {g : LiftL2 P | ∃ φ : LiftDomain P → ℝ,
      (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (localLift P φ x)) ∧
      g =ᵐ[liftMeasure P] liftedGradient P κ m φ} ≤ K := by
    apply Submodule.span_le.mpr
    rintro g ⟨φ,hφ,hgφ⟩
    change inner ℝ u g = 0
    rw [real_inner_comm,MeasureTheory.L2.inner_def]
    calc
      _ = ∫ x, inner ℝ (liftedGradient P κ m φ x) (u x) ∂liftMeasure P := by
        apply integral_congr_ae
        filter_upwards [hgφ] with x hx
        rw [hx]
      _ = 0 := h φ hφ
  have hc : gradientSpace P κ m ≤ K :=
    (Submodule.topologicalClosure_minimal _ hg (innerSL ℝ u).isClosed_ker)
  intro g hg'
  rw [real_inner_comm]
  exact hc hg'

theorem mem_of_classical (κ : ℝ) (m : Vector3) (u : LiftL2 P)
    (f : LiftDomain P → Vector3)
    (hrep : (u : LiftDomain P → Vector3) =ᵐ[liftMeasure P] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift P f x))
    (hdiv : ∀ x, (∑ i : Fin 3, (fieldDerivative P (coordinateDirection κ m i) f x) i) = 0) :
    u ∈ divergenceFreeSpace P κ m := by
  apply mem_of_test_integral P κ m u
  intro ψ hψ
  let fi := fun (i : Fin 3) (x : LiftDomain P) => f x i
  let di := fun (i : Fin 3) => fieldDerivative P (coordinateDirection κ m i) (fi i)
  have hfi (i : Fin 3) : ∀ x, ContDiff ℝ ∞ (localFieldLift P (fi i) x) :=
    fun x => (EuclideanSpace.proj i : Vector3 →L[ℝ] ℝ).contDiff.comp (hf x)
  have hdi (i : Fin 3) : ∀ x, ContDiff ℝ ∞ (localFieldLift P (di i) x) :=
    fieldDerivative_smooth P (coordinateDirection κ m i) (fi i) (hfi i)
  have hs (x : LiftDomain P) : (∑ i : Fin 3, di i x) = 0 := by
    calc
      _ = ∑ i : Fin 3, (fieldDerivative P (coordinateDirection κ m i) f x) i := by
        apply Finset.sum_congr rfl
        intro i _
        exact fieldDerivative_linear P (EuclideanSpace.proj i) f hf (coordinateDirection κ m i) x
      _ = 0 := hdiv x
  have hI (i : Fin 3) := scalar_product_integrable P (di i) ψ (hdi i) hψ.2 hψ.1
  have hJ (i : Fin 3) := scalar_product_integrable P (fi i)
    (fieldDerivative P (coordinateDirection κ m i) ψ) (hfi i)
    (fieldDerivative_smooth P (coordinateDirection κ m i) ψ hψ.2)
    (fieldDerivative_compact P (coordinateDirection κ m i) ψ hψ.1)
  calc
    _ = ∫ x, ∑ i : Fin 3, fi i x * fieldDerivative P (coordinateDirection κ m i) ψ x
        ∂liftMeasure P := by
      apply integral_congr_ae
      filter_upwards [hrep] with x hx
      rw [hx,EuclideanSpace.inner_eq_star_dotProduct]
      change (∑ i : Fin 3, f x i * liftedGradient P κ m ψ x i) = _
      simp_rw [liftedGradient_component]
      rfl
    _ = ∑ i : Fin 3, ∫ x, fi i x * fieldDerivative P (coordinateDirection κ m i) ψ x
        ∂liftMeasure P := integral_finsetSum _ (fun i _ => hJ i)
    _ = -(∑ i : Fin 3, ∫ x, di i x * ψ x ∂liftMeasure P) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      have hi := scalar_integration_by_parts_test P (coordinateDirection κ m i) (fi i) ψ
        (hfi i) hψ.2 hψ.1
      change (∫ x, fi i x * fieldDerivative P (coordinateDirection κ m i) ψ x ∂liftMeasure P) =
        -(∫ x, fieldDerivative P (coordinateDirection κ m i) (fi i) x * ψ x ∂liftMeasure P)
      linarith
    _ = -(∫ x, ∑ i : Fin 3, di i x * ψ x ∂liftMeasure P) := by
      rw [integral_finsetSum _ (fun i _ => hI i)]
    _ = 0 := by
      have he : (fun x : LiftDomain P => ∑ i : Fin 3, di i x * ψ x) = 0 := by
        funext x
        rw [← Finset.sum_mul,hs x,zero_mul]
        rfl
      rw [he]
      change -(∫ _ : LiftDomain P, (0 : ℝ) ∂liftMeasure P) = 0
      rw [integral_zero,neg_zero]

end EulerCylinderClassicalSolenoidal
