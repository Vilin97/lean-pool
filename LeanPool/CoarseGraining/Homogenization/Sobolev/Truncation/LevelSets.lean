/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Truncation.Basic

/-! # Level Sets -/

@[expose] public section

namespace Homogenization

open Homogenization MeasureTheory Filter Topology

/-!
# Vanishing of the gradient on level sets

`grad_ae_zero_on_level_set`, derived from the positive-part truncation applied
to `u` at `c` and to `−u` at `−c`.  Stated on `IsOpenBoundedConvexDomain U`.
-/

/-- **Vanishing of the gradient on level sets.**  For `u ∈ H¹(U)` the weak gradient vanishes almost
everywhere on the level set `{u = c}`.

Proof: `(u−c)₊ − (c−u)₊ = u − c`, so the difference `v₁ − v₂` of the two D1
truncations has the same weak gradient as `u` (constant shift is `H¹`-trivial),
while pointwise on `{u = c}` both truncation gradients vanish. -/
theorem grad_ae_zero_on_level_set {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U) (c : ℝ) :
    ∀ᵐ x ∂(volumeMeasureOn U), u.toFun x = c → u.grad x = 0 := by
  have : IsFiniteMeasure (volumeMeasureOn U) :=
    hU.isBoundedDomain.isFiniteMeasure_restrict_volume
  obtain ⟨v₁, hv₁f, hv₁g⟩ := exists_h1_max_sub_const hU u c
  obtain ⟨v₂, hv₂f, hv₂g⟩ := exists_h1_max_sub_const hU (-u) (-c)
  -- Constant `c` as an `H¹` function (weak gradient zero).
  have hcweak : HasWeakGradientOn U (fun _ : Vec d => c) (fun _ _ => 0) := by
    have h := HasWeakGradientOn.of_contDiff (U := U)
      (contDiff_const : ContDiff ℝ 1 (fun _ : Vec d => c))
    have heq : (fun (x : Vec d) (i : Fin d) => (fderiv ℝ (fun _ : Vec d => c) x) (basisVec i))
        = (fun _ _ => (0 : ℝ)) := by funext x i; simp
    rwa [heq] at h
  let cH : H1Function U :=
    { toFun := fun _ => c, grad := fun _ _ => 0
      memL2 := memLp_const c
      gradMemL2 := fun _ => by exact memLp_const (0 : ℝ)
      hasWeakGradient := hcweak }
  set v : H1Function U := v₁ - v₂ with hv_def
  set w : H1Function U := u - cH with hw_def
  -- `v` and `w` have the same value function `u − c`.
  have htoFun_eq : v.toFun = w.toFun := by
    funext x
    have hA : max ((-u).toFun x - -c) 0 = max (c - u.toFun x) 0 := by
      have hAeq : (-u).toFun x - -c = c - u.toFun x := by
        simp only [H1Function.neg_toFun]; ring
      rw [hAeq]
    have h1 : v.toFun x = max (u.toFun x - c) 0 - max (c - u.toFun x) 0 := by
      simp only [hv_def, H1Function.sub_toFun, hv₁f, hv₂f]
      rw [hA]
    have h2 : w.toFun x = u.toFun x - c := by
      simp only [hw_def, H1Function.sub_toFun, cH]
    rw [h1, h2]
    rcases le_total (u.toFun x - c) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  -- Same value ⟹ same weak gradient a.e.
  have hgrad_ae : ∀ᵐ x ∂(volumeMeasureOn U), v.grad x = w.grad x := by
    have hloc : ∀ (z : H1Function U) (i : Fin d),
        LocallyIntegrableOn (fun x => z.grad x i) U volume := fun z i =>
      locallyIntegrableOn_of_locallyIntegrable_restrict
        ((z.gradMemL2 i).locallyIntegrable (by norm_num))
    have hcoord : ∀ i : Fin d,
        (fun x => v.grad x i) =ᵐ[volumeMeasureOn U] (fun x => w.grad x i) := by
      intro i
      refine HasWeakPartialDerivOn.ae_eq hU.isOpen (hloc v i) (hloc w i)
        (v.hasWeakGradient i) ?_
      have := w.hasWeakGradient i
      rwa [← htoFun_eq] at this
    have hall : ∀ᵐ x ∂(volumeMeasureOn U), ∀ i, v.grad x i = w.grad x i :=
      ae_all_iff.mpr hcoord
    filter_upwards [hall] with x hx
    funext i; exact hx i
  -- `w.grad = u.grad`.
  have hw_grad : ∀ x, w.grad x = u.grad x := by
    intro x; funext i
    simp only [hw_def, H1Function.sub_grad, cH, Pi.sub_apply, sub_zero]
  -- Assemble.
  filter_upwards [hgrad_ae, hv₁g, hv₂g] with x hgx h1x h2x hc
  have hvgrad : v.grad x = v₁.grad x - v₂.grad x := by
    funext i; simp only [hv_def, H1Function.sub_grad]
  have hv1 : v₁.grad x = 0 := by
    rw [h1x]; simp [hc]
  have hv2 : v₂.grad x = 0 := by
    rw [h2x]
    refine Set.indicator_of_notMem ?_ _
    simp only [Set.mem_ofPred_eq, H1Function.neg_toFun, not_lt, hc, le_refl]
  have : u.grad x = 0 := by
    rw [← hw_grad x, ← hgx, hvgrad, hv1, hv2, sub_zero]
  exact this

end Homogenization
