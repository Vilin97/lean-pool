/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamel

@[expose] public section

/-!
# Construction of a homogeneous fundamental solution

Continuous bounded coefficients in a real Banach algebra have actual forward
and inverse fundamental paths. Existence is the previously proved global
Lipschitz Picard theorem; both inverse identities follow by differentiation
and ODE uniqueness. This result is qualitative. No exponential estimate from
this construction is used in the later profile estimates.
-/

noncomputable section

namespace EulerLinearFundamentalExistence

open Set ContinuousLinearMap EulerVolterraConvolution EulerPacketExistence

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  (T : ℝ) (hT : 0 ≤ T) (B : C(Icc (0 : ℝ) T,A))

/-- A continuous coefficient field has two-sided inverse fundamental paths. -/
theorem exists_fundamental : ∃ Φ Ψ : ℝ → A,
    Φ 0 = 1 ∧ Ψ 0 = 1 ∧
    (∀ t ∈ Icc (0 : ℝ) T, HasDerivAt Φ (extendPath T hT B t * Φ t) t) ∧
    (∀ t ∈ Icc (0 : ℝ) T, HasDerivAt Ψ (-(Ψ t * extendPath T hT B t)) t) ∧
    (∀ t ∈ Icc (0 : ℝ) T, Φ t * Ψ t = 1 ∧ Ψ t * Φ t = 1) := by
  let b := extendPath T hT B
  have hb : Continuous b := extendPath_continuous T hT B
  have hnorm (t : ℝ) : ‖b t‖ ≤ ‖B‖ := B.norm_coe_le_norm _
  have hcL : Continuous (Function.uncurry (fun (t : ℝ) (x : A) => b t*x)) :=
    (hb.comp continuous_fst).mul continuous_snd
  have hcR : Continuous (Function.uncurry (fun (t : ℝ) (x : A) => -(x*b t))) :=
    (continuous_snd.mul (hb.comp continuous_fst)).neg
  have hLipL (t : ℝ) : LipschitzWith ‖B‖₊ (fun x : A => b t*x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm, ← mul_sub]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hnorm t) (norm_nonneg _))
  have hLipR (t : ℝ) : LipschitzWith ‖B‖₊ (fun x : A => -(x*b t)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_neg_neg, dist_eq_norm, dist_eq_norm, ← sub_mul]
    exact (norm_mul_le _ _).trans
      ((mul_le_mul_of_nonneg_left (hnorm t) (norm_nonneg (x-y))).trans_eq (mul_comm _ _))
  obtain ⟨Φ,hΦ0,hΦ⟩ := exists_solution_on_compact_interval
    (⟨0,le_rfl,hT⟩ : Icc (0 : ℝ) T) hcL hLipL (1 : A)
  obtain ⟨Ψ,hΨ0,hΨ⟩ := exists_solution_on_compact_interval
    (⟨0,le_rfl,hT⟩ : Icc (0 : ℝ) T) hcR hLipR (1 : A)
  change Φ 0 = 1 at hΦ0
  change Ψ 0 = 1 at hΨ0
  have hcΦ : ContinuousOn Φ (Icc (0 : ℝ) T) := fun t ht => (hΦ t ht).continuousAt.continuousWithinAt
  have hcΨ : ContinuousOn Ψ (Icc (0 : ℝ) T) := fun t ht => (hΨ t ht).continuousAt.continuousWithinAt
  have hback (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : Ψ t*Φ t = 1 := by
    have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
        HasDerivWithinAt (fun r => Ψ r*Φ r) 0 (Icc (0 : ℝ) T) s := by
      have hh := ((hΨ s hs).mul (hΦ s hs)).hasDerivWithinAt (s := Icc (0 : ℝ) T)
      convert hh using 1
      all_goals first | rfl | simp only [neg_mul, mul_assoc, neg_add_cancel]
    have hbound := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hd
      (fun s hs => by simp) (convex_Icc (0 : ℝ) T)
      (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩) ht
    simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero, hΦ0, hΨ0, one_mul] using hbound
  have hLipC (t : ℝ) : LipschitzWith (2*‖B‖₊) (fun x : A => b t*x-x*b t) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    have he : (b t*x-x*b t)-(b t*y-y*b t) = b t*(x-y)-(x-y)*b t := by noncomm_ring
    rw [he]
    calc
      _ ≤ ‖b t*(x-y)‖ + ‖(x-y)*b t‖ := norm_sub_le _ _
      _ ≤ ‖b t‖*‖x-y‖ + ‖x-y‖*‖b t‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ ‖B‖*‖x-y‖ + ‖x-y‖*‖B‖ := add_le_add
        (mul_le_mul_of_nonneg_right (hnorm t) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (hnorm t) (norm_nonneg _))
      _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_ofNat, coe_nnnorm]; ring
  have hfront : EqOn (fun t => Φ t*Ψ t) (fun _ => (1 : A)) (Icc (0 : ℝ) T) := by
    apply ODE_solution_unique_of_mem_Icc_right
      (v := fun t x => b t*x-x*b t) (s := fun _ => Set.univ)
      (fun t _ => (hLipC t).lipschitzOnWith)
      (hcΦ.mul hcΨ) ?_ (fun _ _ => mem_univ _) continuousOn_const ?_
      (fun _ _ => mem_univ _) (by change Φ 0*Ψ 0 = 1; rw [hΦ0,hΨ0,one_mul])
    · intro t ht
      have hh := ((hΦ t ⟨ht.1,ht.2.le⟩).mul (hΨ t ⟨ht.1,ht.2.le⟩)).hasDerivWithinAt (s := Ici t)
      convert hh using 1
      all_goals first | rfl | simp only [Pi.mul_apply, mul_neg, mul_assoc, sub_eq_add_neg]
    · intro t _
      simpa only [mul_one, one_mul, sub_self] using
        (hasDerivAt_const t (1 : A)).hasDerivWithinAt (s := Ici t)
  exact ⟨Φ,Ψ,hΦ0,hΨ0,hΦ,hΨ,fun t ht => ⟨hfront ht,hback t ht⟩⟩

end EulerLinearFundamentalExistence
