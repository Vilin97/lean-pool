/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderJetLp
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldAdvection
import LeanPool.NavierStokesAndEuler.Euler.CylinderCoveringDerivative
import LeanPool.NavierStokesAndEuler.Euler.CylinderJetLpMap
import LeanPool.NavierStokesAndEuler.Euler.PacketNormalDriftBounds
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder

/-! Addition and transport of the actual cylinder derivative tensors.
All norm statements concern genuine L² functions on the cylinder. -/

@[expose] public section


noncomputable section


namespace EulerCylinderJetLp

open Set MeasureTheory EulerLiftedGradientSpace EulerMetricTransport
  EulerCylinderSobolev EulerCylinderSmoothOrbit EulerCylinderCoverDescent
  EulerLiftedTransportTrace EulerPacketCylinderField
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Cache the standard `NormedAddCommGroup (LiftTangent [×n]→L[ℝ] V)` instance to shorten
typeclass synthesis. -/
local instance instCylinderJetLpAlgebra1 (n : ℕ) : NormedAddCommGroup (LiftTangent [×n]→L[ℝ] V) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftTangent [×n]→L[ℝ] V)` instance to shorten typeclass
synthesis. -/
local instance instCylinderJetLpAlgebra2 (n : ℕ) : NormedSpace ℝ (LiftTangent [×n]→L[ℝ] V) :=
    inferInstance

theorem tensor_add (f g : LiftDomain P → V)
    (hf : ∀ q, ContDiff ℝ ∞ (localFieldLift P f q))
    (hg : ∀ q, ContDiff ℝ ∞ (localFieldLift P g q)) (n : ℕ) (q : LiftDomain P) :
    tensor P (fun x => f x + g x) n q = tensor P f n q + tensor P g n q := by
  exact iteratedFDeriv_add_apply ((coverField_contDiff P f hf).of_le (by simp)).contDiffAt
    ((coverField_contDiff P g hg).of_le (by simp)).contDiffAt

theorem tensor_add_memLp (f g : LiftDomain P → V)
    (hf : ∀ q, ContDiff ℝ ∞ (localFieldLift P f q))
    (hg : ∀ q, ContDiff ℝ ∞ (localFieldLift P g q)) (n : ℕ)
    (hF : MemLp (tensor P f n) 2 (liftMeasure P))
    (hG : MemLp (tensor P g n) 2 (liftMeasure P)) :
    MemLp (tensor P (fun x => f x + g x) n) 2 (liftMeasure P) := by
  have he : tensor P (fun x => f x + g x) n = tensor P f n + tensor P g n :=
    funext (tensor_add P f g hf hg n)
  rw [he]
  exact MemLp.add (f := tensor P f n) (g := tensor P g n) (p := 2) (μ := liftMeasure P) hF hG

theorem tensor_add_norm_le (f g : LiftDomain P → V)
    (hf : ∀ q, ContDiff ℝ ∞ (localFieldLift P f q))
    (hg : ∀ q, ContDiff ℝ ∞ (localFieldLift P g q)) (n : ℕ)
    (hF : MemLp (tensor P f n) 2 (liftMeasure P))
    (hG : MemLp (tensor P g n) 2 (liftMeasure P)) :
    (eLpNorm (tensor P (fun x => f x + g x) n) 2 (liftMeasure P)).toReal ≤
      (eLpNorm (tensor P f n) 2 (liftMeasure P)).toReal +
      (eLpNorm (tensor P g n) 2 (liftMeasure P)).toReal := by
  have hS := tensor_add_memLp P f g hf hg n hF hG
  have he : hS.toLp _ = hF.toLp _ + hG.toLp _ := by
    apply Lp.ext
    filter_upwards [hS.coeFn_toLp, hF.coeFn_toLp, hG.coeFn_toLp,
      Lp.coeFn_add (hF.toLp _) (hG.toLp _)] with q hs hf' hg' ha
    simp only [Pi.add_apply] at ha
    rw [ha, hs, hf', hg']
    exact tensor_add P f g hf hg n q
  have h := norm_add_le (hF.toLp _) (hG.toLp _)
  rw [← he] at h
  simpa only [Lp.norm_toLp] using h

theorem tensor_transport_norm_le_full (κ : ℝ) (m : Vector3) (f : LiftDomain P → Vector3)
    (hf : ∀ q, ContDiff ℝ ∞ (localFieldLift P f q)) (n : ℕ)
    (hF : MemLp (tensor P f n) 2 (liftMeasure P)) :
    (eLpNorm (tensor P (fun x => transportDirection κ m (f x)) n) 2 (liftMeasure P)).toReal ≤
      (|κ| + ‖m‖) * (eLpNorm (tensor P f n) 2 (liftMeasure P)).toReal := by
  apply (tensor_transport_norm_le P κ m f hf n hF).trans
  have hN := (tensor_map_norm_le P (normalComponentMap m) f hf n hF).trans
    (mul_le_mul_of_nonneg_right (normalComponentMap_norm_le m) ENNReal.toReal_nonneg)
  simpa only [add_mul] using add_le_add (le_refl _) hN

theorem tensor_transport_add_norm_le (κ : ℝ) (m : Vector3) (f g : LiftDomain P → Vector3)
    (hf : ∀ q, ContDiff ℝ ∞ (localFieldLift P f q))
    (hg : ∀ q, ContDiff ℝ ∞ (localFieldLift P g q)) (n : ℕ)
    (hF : MemLp (tensor P f n) 2 (liftMeasure P))
    (hG : MemLp (tensor P g n) 2 (liftMeasure P)) :
    (eLpNorm (tensor P (fun x => transportDirection κ m (f x + g x)) n)
      2 (liftMeasure P)).toReal ≤
      |κ| * (eLpNorm (tensor P f n) 2 (liftMeasure P)).toReal +
        (eLpNorm (tensor P (fun x => normalComponentMap m (f x)) n) 2 (liftMeasure P)).toReal +
          (|κ| + ‖m‖) * (eLpNorm (tensor P g n) 2 (liftMeasure P)).toReal := by
  have he : (fun x => transportDirection κ m (f x + g x)) =
      (fun x => transportLinear κ m (f x) + transportLinear κ m (g x)) := by
    funext x
    exact (transportLinear κ m).map_add (f x) (g x)
  rw [he]
  have hf' : ∀ q, ContDiff ℝ ∞ (localFieldLift P (fun x => transportLinear κ m (f x)) q) :=
    fun q => (transportLinear κ m).contDiff.comp (hf q)
  have hg' : ∀ q, ContDiff ℝ ∞ (localFieldLift P (fun x => transportLinear κ m (g x)) q) :=
    fun q => (transportLinear κ m).contDiff.comp (hg q)
  exact (tensor_add_norm_le P _ _ hf' hg' n
    (tensor_map_memLp P (transportLinear κ m) f hf n hF)
    (tensor_map_memLp P (transportLinear κ m) g hg n hG)).trans
      (add_le_add (tensor_transport_norm_le P κ m f hf n hF)
        (tensor_transport_norm_le_full P κ m g hg n hG))

end EulerCylinderJetLp
