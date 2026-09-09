/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderJetLp
public import LeanPool.NavierStokesAndEuler.Euler.LiftedSmoothTimeField

@[expose] public section

/-! Bounded linear maps act on the actual descended tensors and their
L² classes. In particular the small normal component is retained in the
four-dimensional transport estimate. -/

noncomputable section


namespace EulerCylinderJetLp

open Set MeasureTheory ContinuousLinearMap EulerLiftedGradientSpace EulerMetricTransport
  EulerCylinderSobolev EulerCylinderSmoothOrbit EulerCylinderCoverDescent
  EulerLiftedTransportTrace EulerLiftedSmoothTimeField EulerPacketCylinderField
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem tensor_map (L : V →L[ℝ] W) (f : LiftDomain P → V)
    (hf : ∀ q, ContDiff ℝ ∞ (localFieldLift P f q)) (n : ℕ) (q : LiftDomain P) :
    tensor P (fun x => L (f x)) n q = L.compContinuousMultilinearMap (tensor P f n q) := by
  change iteratedFDeriv ℝ n (L ∘ fun z => f (coveringMap P z)) (sectionPoint P q) = _
  exact L.iteratedFDeriv_comp_left ((coverField_contDiff P f hf).contDiffAt) (by simp)

theorem tensor_map_memLp (L : V →L[ℝ] W) (f : LiftDomain P → V)
    (hf : ∀ q, ContDiff ℝ ∞ (localFieldLift P f q)) (n : ℕ)
    (hLp : MemLp (tensor P f n) 2 (liftMeasure P)) :
    MemLp (tensor P (fun x => L (f x)) n) 2 (liftMeasure P) := by
  have h := hLp.continuousLinearMap_comp
    (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin n => LiftTangent) V W L)
  change MemLp (fun q => L.compContinuousMultilinearMap (tensor P f n q)) 2 (liftMeasure P) at h
  simp_rw [← tensor_map P L f hf n] at h
  exact h

theorem tensor_map_norm_le (L : V →L[ℝ] W) (f : LiftDomain P → V)
    (hf : ∀ q, ContDiff ℝ ∞ (localFieldLift P f q)) (n : ℕ)
    (hLp : MemLp (tensor P f n) 2 (liftMeasure P)) :
    (eLpNorm (tensor P (fun x => L (f x)) n) 2 (liftMeasure P)).toReal ≤
      ‖L‖ * (eLpNorm (tensor P f n) 2 (liftMeasure P)).toReal := by
  have hM := tensor_map_memLp P L f hf n hLp
  have h : ‖hM.toLp (tensor P (fun x => L (f x)) n)‖ ≤ ‖L‖ * ‖hLp.toLp (tensor P f n)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hM.coeFn_toLp, hLp.coeFn_toLp] with q hq hq'
    rw [hq, hq', tensor_map P L f hf n]
    exact L.norm_compContinuousMultilinearMap_le _
  simpa only [Lp.norm_toLp] using h

section Transport

variable (κ : ℝ) (m : Vector3) (f : LiftDomain P → Vector3)
  (hf : ∀ q, ContDiff ℝ ∞ (localFieldLift P f q)) (n : ℕ)
  (hLp : MemLp (tensor P f n) 2 (liftMeasure P))

include hf in
omit [Fact (0 < P)] in
private theorem normal_smooth (q : LiftDomain P) :
    ContDiff ℝ ∞ (localFieldLift P (fun x => normalComponentMap m (f x)) q) :=
  (normalComponentMap m).contDiff.comp (hf q)

include hf in
theorem tensor_transport_split (q : LiftDomain P) :
    tensor P (fun x => transportDirection κ m (f x)) n q =
      κ • tensor P (fun x => ContinuousLinearMap.inl ℝ Vector3 ℝ (f x)) n q +
        tensor P (fun x => angularInjection (normalComponentMap m (f x))) n q := by
  rw [show (fun x => transportDirection κ m (f x)) =
    (fun x => transportLinear κ m (f x)) from rfl]
  rw [tensor_map P (transportLinear κ m) f hf n,
    tensor_map P (ContinuousLinearMap.inl ℝ Vector3 ℝ) f hf n,
    tensor_map P angularInjection _ (normal_smooth P m f hf) n,
    tensor_map P (normalComponentMap m) f hf n]
  apply ContinuousMultilinearMap.ext
  intro v
  exact congrArg (fun L : Vector3 →L[ℝ] LiftTangent => L (tensor P f n q v))
    (transportLinear_split κ m)

include hf hLp in
theorem tensor_transport_norm_le :
    (eLpNorm (tensor P (fun x => transportDirection κ m (f x)) n) 2 (liftMeasure P)).toReal ≤
      |κ| * (eLpNorm (tensor P f n) 2 (liftMeasure P)).toReal +
        (eLpNorm (tensor P (fun x => normalComponentMap m (f x)) n) 2 (liftMeasure P)).toReal := by
  let F := tensor P (fun x => transportDirection κ m (f x)) n
  let G := tensor P (fun x => ContinuousLinearMap.inl ℝ Vector3 ℝ (f x)) n
  let H := tensor P (fun x => angularInjection (normalComponentMap m (f x))) n
  have hF : MemLp F 2 (liftMeasure P) := tensor_map_memLp P (transportLinear κ m) f hf n hLp
  have hG : MemLp G 2 (liftMeasure P) := tensor_map_memLp P (ContinuousLinearMap.inl ℝ Vector3 ℝ) f
    hf n hLp
  have hN := tensor_map_memLp P (normalComponentMap m) f hf n hLp
  have hH : MemLp H 2 (liftMeasure P) :=
    tensor_map_memLp P angularInjection _ (normal_smooth P m f hf) n hN
  have he : hF.toLp F = κ • hG.toLp G + hH.toLp H := by
    apply Lp.ext
    filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp, hH.coeFn_toLp,
      Lp.coeFn_smul κ (hG.toLp G), Lp.coeFn_add (κ • hG.toLp G) (hH.toLp H)]
      with q hq hg hh hs ha
    simp only [Pi.add_apply] at ha
    simp only [Pi.smul_apply] at hs
    rw [ha, hs, hq, hg, hh]
    exact tensor_transport_split P κ m f hf n q
  have hi := (tensor_map_norm_le P (ContinuousLinearMap.inl ℝ Vector3 ℝ) f hf n hLp).trans
    (mul_le_mul_of_nonneg_right spatialInjection_norm ENNReal.toReal_nonneg)
  have hj := (tensor_map_norm_le P angularInjection _ (normal_smooth P m f hf) n hN).trans
    (mul_le_mul_of_nonneg_right angularInjection_norm ENNReal.toReal_nonneg)
  have h := (norm_add_le (κ • hG.toLp G) (hH.toLp H))
  rw [← he, norm_smul, Real.norm_eq_abs] at h
  simp only [Lp.norm_toLp] at h
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_left (by simpa only [one_mul] using hi)
    (abs_nonneg κ)) (by simpa only [one_mul] using hj))

end Transport
end EulerCylinderJetLp
