/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevMetricTransport
public import LeanPool.NavierStokesAndEuler.Euler.SobolevHeatGenerator
public import LeanPool.NavierStokesAndEuler.Euler.SobolevRestriction

@[expose] public section

/-! The genuine commuting coordinate derivatives and bounded Laplacian on the complete Sobolev
  scale. -/

noncomputable section

namespace EulerSobolevLaplacian

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerMetricTransport
  EulerCylinderSobolev EulerCylinderSobolevSpace EulerSobolevHeat EulerSobolevHeatGenerator
  EulerMollifierRepresentative EulerPressureSpatialRegularity EulerSpatialSobolevInverse
    EulerTransportDerivatives
open scoped Topology ContDiff ENNReal NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- A genuine Sobolev coordinate derivative agrees with every smooth representative's classical derivative. -/
theorem derivative_value_ae {q : ℕ} (i : Fin 4) (u : SobolevSpace period (q+1))
    (g : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    (value period (derivativeOperator period q i u) : LiftDomain period → Vector3) =ᵐ[liftMeasure
      period]
      fieldDerivative period (standardDirection i) g :=
  EulerStrongSmoothJet.translation_derivative_ae period (standardDirection i)
    (value period u) (value period (derivativeOperator period q i u)) g hu hg
    (derivativeOperator_hasDerivAt period i u)

/-- Coordinate derivatives commute on every genuinely smooth represented Sobolev field. -/
theorem derivative_commute_smooth {q : ℕ} (i j : Fin 4) (u : SobolevSpace period (q+2))
    (g : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    derivativeOperator period q i (derivativeOperator period (q+1) j u) =
      derivativeOperator period q j (derivativeOperator period (q+1) i u) := by
  apply value_injective period
  apply Lp.ext
  have hi := derivative_value_ae period i (derivativeOperator period (q+1) j u)
    (fieldDerivative period (standardDirection j) g) (derivative_value_ae period j u g hu hg)
    (fieldDerivative_smooth period (standardDirection j) g hg)
  have hj := derivative_value_ae period j (derivativeOperator period (q+1) i u)
    (fieldDerivative period (standardDirection i) g) (derivative_value_ae period i u g hu hg)
    (fieldDerivative_smooth period (standardDirection i) g hg)
  filter_upwards [hi, hj] with x hix hjx
  rw [hix, hjx]
  exact EulerLiftedCurl.fieldDerivatives_commute period (standardDirection i) (standardDirection j)
    g hg x

/-- Strong coordinate derivatives commute for every actual finite Sobolev field, by genuine smooth density. -/
theorem derivative_commute {q : ℕ} (i j : Fin 4) (u : SobolevSpace period (q+2)) :
    derivativeOperator period q i (derivativeOperator period (q+1) j u) =
      derivativeOperator period q j (derivativeOperator period (q+1) i u) := by
  let A := (derivativeOperator period q i).comp (derivativeOperator period (q+1) j)
  let B := (derivativeOperator period q j).comp (derivativeOperator period (q+1) i)
  have hA := A.continuous.continuousAt.tendsto.comp (sobolevMollifier_tendsto period u)
  have hB := B.continuous.continuousAt.tendsto.comp (sobolevMollifier_tendsto period u)
  have he : (fun n => A (sobolevMollifier period (q+2) n u)) =
      fun n => B (sobolevMollifier period (q+2) n u) := by
    funext n
    exact derivative_commute_smooth period i j (sobolevMollifier period (q+2) n u)
      (smoothMollifier period n (value period u)) (sobolevMollifier_representative period n u)
      (smoothMollifier_smooth period n (value period u))
  change Filter.Tendsto (fun n => A (sobolevMollifier period (q+2) n u)) Filter.atTop (𝓝 (A u)) at
    hA
  rw [he] at hA
  exact tendsto_nhds_unique hA hB

/-- The actual Laplacian as a bounded map H^(q+2)→Hq. -/
def laplacianOperator (q : ℕ) : SobolevSpace period (q+2) →L[ℝ] SobolevSpace period q :=
  ∑ i : Fin 4, (derivativeOperator period q i).comp (derivativeOperator period (q+1) i)

/-- The bounded Laplacian is the sum of the genuine pure second derivatives. -/
theorem laplacianOperator_apply {q : ℕ} (u : SobolevSpace period (q+2)) :
    laplacianOperator period q u = ∑ i : Fin 4,
      derivativeOperator period q i (derivativeOperator period (q+1) i u) := by
  simp only [laplacianOperator, sum_apply, ContinuousLinearMap.comp_apply]

/-- Its L² field is exactly the previously proved actual Laplacian evaluation. -/
theorem laplacianOperator_value {q : ℕ} (u : SobolevSpace period (q+2)) :
    value period (laplacianOperator period q u) = laplacianEvaluation period (q+2) (by omega) u :=
      by
  rw [laplacianOperator_apply, laplacianEvaluation_apply]
  change (valueOperator period q) (∑ i : Fin 4, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change u.val ⟨⟨2, _⟩, Fin.snoc (Fin.snoc Fin.elim0 i) i⟩ = u.val ⟨⟨2, _⟩, fun _ => i⟩
  have hw : Fin.snoc (Fin.snoc (Fin.elim0 : Fin 0 → Fin 4) i) i = (fun _ : Fin 2 => i) := by
    funext j
    fin_cases j <;> rfl
  rw [hw]

/-- The actual complete-Sobolev Laplacian has norm at most four. -/
theorem laplacianOperator_bound {q : ℕ} (u : SobolevSpace period (q+2)) :
    ‖laplacianOperator period q u‖ ≤ 4 * ‖u‖ := by
  rw [laplacianOperator_apply]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin 4, ‖u‖ := Finset.sum_le_sum fun i _ =>
      (derivativeOperator_bound period i _).trans (derivativeOperator_bound period i u)
    _ = _ := by simp

/-- The actual Laplacian commutes with every coordinate derivative. -/
theorem laplacian_derivative {q : ℕ} (i : Fin 4) (u : SobolevSpace period (q+3)) :
    laplacianOperator period q (derivativeOperator period (q+2) i u) =
      derivativeOperator period q i (laplacianOperator period (q+1) u) := by
  rw [laplacianOperator_apply, laplacianOperator_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [derivative_commute period j i u,
    derivative_commute period j i (derivativeOperator period (q+2) j u)]

end EulerSobolevLaplacian
