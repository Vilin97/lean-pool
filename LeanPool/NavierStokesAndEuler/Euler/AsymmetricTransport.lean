/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevTransport
public import LeanPool.NavierStokesAndEuler.Euler.GevreyOrderZero

/-! The actual asymmetric Sobolev transport map needed for the parabolic source upgrade. -/

@[expose] public section


noncomputable section

namespace EulerAsymmetricTransport

open EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevL2Product EulerSobolevTransport
  EulerGevreyOrderZero
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Cache the standard `NormedAddCommGroup (SobolevSpace period q)` instance to shorten
typeclass synthesis. -/
local instance asymmetricGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance
/-- Cache the standard `NormedSpace ℝ (SobolevSpace period q)` instance to shorten typeclass
synthesis. -/
local instance asymmetricSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- Actual transport Hs×H^(s+1)→Hs; the coefficient velocity needs no extra derivative. -/
def asymmetricTransport {s : ℕ} (hs : 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1) :
    SobolevSpace period s →L[ℝ] SobolevSpace period (s+1) →L[ℝ] SobolevSpace period s :=
  ∑ i : Fin 4, (productHqBilinear period hs (L i) (hL i)).bilinearComp
    (ContinuousLinearMap.id ℝ (SobolevSpace period s)) (derivativeOperator period s i)

/-- The literal scalar-times-derivative formula of asymmetric transport. -/
theorem asymmetricTransport_apply {s : ℕ} (hs : 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u : SobolevSpace period s) (v : SobolevSpace period (s + 1)) :
    asymmetricTransport period hs L hL u v = ∑ i : Fin 4,
      productHq period hs (L i) (hL i) u (derivativeOperator period s i v) := by
  simp only [asymmetricTransport, sum_apply, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.id_apply, productHqBilinear_apply]

/-- The asymmetric map agrees with the already constructed genuine transport on common inputs. -/
theorem asymmetricTransport_eq {s : ℕ} (hs : 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s + 1)) :
    asymmetricTransport period hs L hL (truncateOperator period s u) v = transportBilinear period
        hs L hL u v := by
  rw [asymmetricTransport_apply, transportBilinear_apply]

/-- The background-drift expression is the same actual asymmetric transport operator. -/
theorem asymmetricTransport_eq_background {s : ℕ} (hs : 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u : SobolevSpace period s) (v : SobolevSpace period (s + 1)) :
    asymmetricTransport period hs L hL u v = backgroundDrift period hs L hL v u := by
  rw [asymmetricTransport_apply]
  rfl

/-- The genuine asymmetric transport bound needed to multiply a bounded Hs path with an L²-time
H^(s+1) path. -/
theorem asymmetricTransport_bound {s : ℕ} (hs : 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u : SobolevSpace period s) (v : SobolevSpace period (s + 1)) :
    ‖asymmetricTransport period hs L hL u v‖ ≤ 4*sobolevProductConstant period s*‖u‖*‖v‖ := by
  rw [asymmetricTransport_apply]
  have h := (norm_sum_le _ _).trans (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun i
      _ =>
    (productHq_norm period hs (L i) (hL i) u (derivativeOperator period s i v)).trans
      (mul_le_mul_of_nonneg_left (derivativeOperator_bound period i v)
        (mul_nonneg (sobolevProductConstant_nonneg period s) (norm_nonneg u)))))
  exact h.trans_eq (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring)

/-- Operator-norm control of the actual asymmetric transport bilinear map. -/
theorem asymmetricTransport_norm {s : ℕ} (hs : 6 ≤ s)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1) :
    ‖asymmetricTransport period hs L hL‖ ≤ 4*sobolevProductConstant period s := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by
      norm_num) (sobolevProductConstant_nonneg period s))
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg (by norm_num)
    (sobolevProductConstant_nonneg period s)) (norm_nonneg u))
  intro v
  exact asymmetricTransport_bound period hs L hL u v

end EulerAsymmetricTransport
