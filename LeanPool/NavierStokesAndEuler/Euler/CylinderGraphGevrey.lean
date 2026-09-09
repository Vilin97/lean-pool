/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderJetGraphTrace
public import LeanPool.NavierStokesAndEuler.Euler.CylinderPhysicalTensor
public import LeanPool.NavierStokesAndEuler.Euler.GevreyFixedShift

@[expose] public section

/-! Periodic cover Gevrey bounds give actual physical graph bounds.
The L² trace uses one extra angular derivative but no extra factor of
the graph frequency. Only the n physical derivatives cost its n-th power. -/

noncomputable section

namespace EulerCylinderGraphGevrey

open Set MeasureTheory Filter InnerProductSpace EulerLiftedGradientSpace EulerCylinderCoverDescent
  EulerCylinderJetGraphTrace EulerGraphPullback EulerGevrey EulerOperatorGevreyCalculus
open scoped ContDiff

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

def graphFactor (k : ℝ) (m : Vector3) : ℝ := 1+|k| * ‖m‖

theorem graphFactor_nonneg (k : ℝ) (m : Vector3) : 0 ≤ graphFactor k m := by
  unfold graphFactor
  positivity

omit [CompleteSpace W] in
theorem norm_graph_derivative_le (f : LiftTangent → W) (hf : ContDiff ℝ ∞ f)
    (k : ℝ) (m : Vector3) (n : ℕ) (x : Vector3) :
    ‖iteratedFDeriv ℝ n (f ∘ graphMap k m) x‖ ≤
      (graphFactor k m)^n*‖iteratedFDeriv ℝ n f (graphMap k m x)‖ := by
  rw [(graphMap k m).iteratedFDeriv_comp_right hf x (by simp)]
  have h := (iteratedFDeriv ℝ n f (graphMap k m x)).norm_compContinuousLinearMap_le
    (fun _ : Fin n => graphMap k m)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at h
  apply h.trans
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (EulerCylinderPhysicalTensor.graphMap_norm_le k m) n)
    (norm_nonneg _)

omit [CompleteSpace W] in
theorem graph_sup_bound (f : LiftTangent → W) (hf : ContDiff ℝ ∞ f)
    (k : ℝ) (m : Vector3) (B R : ℝ)
    (hb : ∀ n z, ‖iteratedFDeriv ℝ n f z‖ ≤ B*R^n*(n.factorial : ℝ)^2)
    (n : ℕ) (x : Vector3) :
    ‖iteratedFDeriv ℝ n (f ∘ graphMap k m) x‖ ≤
      B*(R*graphFactor k m)^n*(n.factorial : ℝ)^2 := by
  apply (norm_graph_derivative_le f hf k m n x).trans
  exact (mul_le_mul_of_nonneg_left (hb n _) (pow_nonneg (graphFactor_nonneg k m) n)).trans_eq
    (by rw [mul_pow]; ring)

variable (P : ℝ) [Fact (0 < P)] (f : LiftTangent → W)
  (hperiod : ∀ (c : AddSubgroup.zmultiples P) z, f (z.1,(c : ℝ)+z.2)=f z)
  (hf : ContDiff ℝ ∞ f)

include hperiod hf in
theorem graph_evaluated_tensor_bound (k : ℝ) (m : Vector3) (C R : ℝ)
    (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hLp : ∀ n, MemLp (fun q => jetSeries P f q n) 2 (liftMeasure P))
    (hn : ∀ n, (eLpNorm (fun q => jetSeries P f q n) 2 (liftMeasure P)).toReal ≤
      C*R^n*(n.factorial : ℝ)^2) (n : ℕ) :
    MemLp (fun x => iteratedFDeriv ℝ n f (graphMap k m x)) 2 volume ∧
      (eLpNorm (fun x => iteratedFDeriv ℝ n f (graphMap k m x)) 2 volume).toReal ≤
        (Real.sqrt (2/P+2*P)*C*(1+R))*(4*R)^n*(n.factorial : ℝ)^2 := by
  let θ : Vector3 → AddCircle P := fun x => (k*inner ℝ m x : ℝ)
  have hθ : Continuous θ := (AddCircle.continuous_mk' P).comp
    (continuous_const.mul (continuous_const.inner continuous_id))
  obtain ⟨hg,hgNorm⟩ := jet_graph_memLp_and_bound P f hperiod hf n (hLp n) (hLp (n+1))
    θ hθ (C*R^n*(n.factorial : ℝ)^2) (C*R^(n+1)*((n+1).factorial : ℝ)^2)
    (by positivity) (by positivity) (hn n) (hn (n+1))
  have he : (fun x => jetSeries P f (x,θ x) n) =
      fun x => iteratedFDeriv ℝ n f (graphMap k m x) :=
    funext (fun x => jetSeries_cover P f hperiod n (graphMap k m x))
  rw [he] at hg hgNorm
  refine ⟨hg,hgNorm.trans ?_⟩
  have hfirst : C*R^n*(n.factorial : ℝ)^2 ≤ C*majorant (4*R) 0 n := by
    simpa only [majorant,Nat.add_zero,mul_assoc] using mul_le_mul_of_nonneg_left
      (majorant_radius_mono R (4*R) hR (by linarith) 0 n) hC
  have hsecond : C*R^(n+1)*((n+1).factorial : ℝ)^2 ≤ C*R*majorant (4*R) 0 n := by
    simpa only [majorant,mul_assoc] using mul_le_mul_of_nonneg_left
      (majorant_one_le_radius_four R hR n) hC
  exact (mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (Real.sqrt_nonneg _)).trans_eq
    (by simp only [majorant,Nat.add_zero]; ring)

include hperiod hf in
theorem graph_Lp_bound (k : ℝ) (m : Vector3) (C R : ℝ)
    (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hLp : ∀ n, MemLp (fun q => jetSeries P f q n) 2 (liftMeasure P))
    (hn : ∀ n, (eLpNorm (fun q => jetSeries P f q n) 2 (liftMeasure P)).toReal ≤
      C*R^n*(n.factorial : ℝ)^2) (n : ℕ) :
    MemLp (iteratedFDeriv ℝ n (f ∘ graphMap k m)) 2 volume ∧
      (eLpNorm (iteratedFDeriv ℝ n (f ∘ graphMap k m)) 2 volume).toReal ≤
        (Real.sqrt (2/P+2*P)*C*(1+R))*(4*R*graphFactor k m)^n*(n.factorial : ℝ)^2 := by
  obtain ⟨hg,hgNorm⟩ := graph_evaluated_tensor_bound P f hperiod hf k m C R hC hR hLp hn n
  have hm : AEStronglyMeasurable (iteratedFDeriv ℝ n (f ∘ graphMap k m)) volume :=
    ((hf.comp (graphMap k m).contDiff).continuous_iteratedFDeriv (m := n) (by
      simp)).aestronglyMeasurable
  have hbound := norm_graph_derivative_le f hf k m n
  have hcomp : MemLp (iteratedFDeriv ℝ n (f ∘ graphMap k m)) 2 volume :=
    hg.of_le_mul hm (Eventually.of_forall hbound)
  have hnorm : (eLpNorm (iteratedFDeriv ℝ n (f ∘ graphMap k m)) 2 volume).toReal ≤
      (graphFactor k m)^n*(eLpNorm (fun x => iteratedFDeriv ℝ n f (graphMap k m x)) 2
        volume).toReal := by
    have h : ‖hcomp.toLp _‖ ≤ (graphFactor k m)^n*‖hg.toLp _‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [hcomp.coeFn_toLp,hg.coeFn_toLp] with x hx hy
      rw [hx,hy]
      exact hbound x
    simpa only [Lp.norm_toLp] using h
  refine ⟨hcomp,hnorm.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left hgNorm (pow_nonneg (graphFactor_nonneg k m) n)).trans_eq
    (by rw [mul_pow]; ring)

end EulerCylinderGraphGevrey
