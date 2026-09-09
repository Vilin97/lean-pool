/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ClassicalPressureCurl

@[expose] public section

/-! Actual smooth representatives of the closed divergence-free space have pointwise lifted
  divergence zero. -/

noncomputable section

namespace EulerClassicalDivergence

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives EulerLiftedWeakDerivative EulerLiftedCurl EulerClassicalPressureCurl
open scoped ContDiff Topology

variable (period : ℝ) [Fact (0 < period)]

/-- A genuine smooth representative of a weakly lifted-divergence-free L² field has zero pointwise lifted divergence. -/
theorem divergenceFree_classical_divergence_zero (κ : ℝ) (m : Vector3)
    (u : LiftL2 period) (hu : u ∈ divergenceFreeSpace period κ m)
    (g : LiftDomain period → Vector3)
    (hrep : (u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    ∀ x, (∑ i : Fin 3, (fieldDerivative period (coordinateDirection κ m i) g x) i) = 0 := by
  let φ := fun (i : Fin 3) (y : LiftDomain period) => g y i
  let a := coordinateDirection κ m
  let d := fun (i : Fin 3) => fieldDerivative period (a i) (φ i)
  let q := fun y => ∑ i : Fin 3, d i y
  have hφ (i : Fin 3) : ∀ y, ContDiff ℝ ∞ (localFieldLift period (φ i) y) :=
    fun y => (EuclideanSpace.proj i : Vector3 →L[ℝ] ℝ).contDiff.comp (hg y)
  have hd (i : Fin 3) : ∀ y, ContDiff ℝ ∞ (localFieldLift period (d i) y) :=
    fieldDerivative_smooth period (a i) (φ i) (hφ i)
  have hq : ∀ y, ContDiff ℝ ∞ (localFieldLift period q y) := by
    intro y
    change ContDiff ℝ ∞ (fun z => ∑ i : Fin 3, localFieldLift period (d i) y z)
    exact ContDiff.sum (fun i _ => hd i y)
  have hzero := smooth_eq_zero_of_compact_test_integrals period q hq (fun ψ hψc hψ => by
    have hw := weak_divergence_test_integral period κ m hu ψ ⟨hψc,hψ⟩
    have hw' : (∫ y, ∑ i : Fin 3, φ i y * fieldDerivative period (a i) ψ y ∂liftMeasure period) = 0
      := by
      rw [← hw]
      apply integral_congr_ae
      filter_upwards [hrep] with y hy
      rw [hy,EuclideanSpace.inner_eq_star_dotProduct]
      change (∑ i : Fin 3, g y i * fieldDerivative period (coordinateDirection κ m i) ψ y) =
        ∑ i : Fin 3, g y i * liftedGradient period κ m ψ y i
      simp_rw [liftedGradient_component]
    have hI (i : Fin 3) := scalar_product_integrable period (d i) ψ (hd i) hψ hψc
    have hJ (i : Fin 3) := scalar_product_integrable period (φ i) (fieldDerivative period (a i) ψ)
      (hφ i) (fieldDerivative_smooth period (a i) ψ hψ) (fieldDerivative_compact period (a i) ψ hψc)
    change (∫ y, (∑ i : Fin 3, d i y) * ψ y ∂liftMeasure period) = 0
    simp_rw [Finset.sum_mul]
    rw [integral_finsetSum _ (fun i _ => hI i)]
    calc
      _ = ∑ i : Fin 3, -(∫ y, φ i y * fieldDerivative period (a i) ψ y ∂liftMeasure period) := by
        apply Finset.sum_congr rfl
        intro i _
        exact scalar_integration_by_parts_test period (a i) (φ i) ψ (hφ i) hψ hψc
      _ = -(∫ y, ∑ i : Fin 3, φ i y * fieldDerivative period (a i) ψ y ∂liftMeasure period) := by
        rw [integral_finsetSum _ (fun i _ => hJ i),Finset.sum_neg_distrib]
      _ = 0 := by rw [hw',neg_zero])
  intro x
  calc
    _ = q x := by
      apply Finset.sum_congr rfl
      intro i _
      exact (fieldDerivative_linear period (EuclideanSpace.proj i) g hg (a i) x).symm
    _ = 0 := hzero x

end EulerClassicalDivergence
