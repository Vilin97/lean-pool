/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowMaterialJets
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.FlowInvLeftInverse

/-! The actual coarse material cancellation in the stream recursion. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance.Infra.Flow

/-- A scalar composed with the actual inverse flow is transported exactly.
Both differentiability and the cancellation follow from the characterized flow. -/
theorem amnr_inverse_flow_material_zero {φ : ℝ → Vec 2 → ℝ}
    (hφ : AVenhance.IsAdmissibleStream φ) {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) (s : ℝ) (z : AmnrSpace) :
    amnrOp (fun y => AVenhance.streamVel φ y.1 y.2) none
      (fun y => f (AVenhance.flowInv (AVenhance.streamVel φ)
        hφ.vel_continuous hφ.vel_lipschitz y.1 y.2 s)) z = 0 := by
  let b := AVenhance.streamVel φ
  let X := AVenhance.flow b hφ.vel_continuous hφ.vel_lipschitz
  let Z := fun y : AmnrSpace => AVenhance.flowInv b hφ.vel_continuous
    hφ.vel_lipschitz y.1 y.2 s
  have hb := AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ
  have hX : AVenhance.IsFlow b X := AVenhance.flow_isFlow b _ _
  have hZ : ContDiff ℝ 1 Z := by
    exact (flow_inverse_joint_contDiff_one hb hX).comp
      (show ContDiff ℝ 1 (fun y : AmnrSpace => (y.1, y.2, s)) by fun_prop)
  let x := Z z
  have hright : X z.1 x s = z.2 :=
    AVenhance.flowInv_rightInverse b _ _ z.1 s z.2
  have hc : HasDerivAt (fun r => X r x s) (b z.1 z.2) z.1 := by
    simpa only [hright] using hX.2 x s z.1
  have hpair := (hasDerivAt_id z.1).prodMk hc
  have hF := (hf.comp hZ).differentiable (by norm_num) z
  have heval : z = (z.1, X z.1 x s) := by rw [hright]
  have hd := hF.hasFDerivAt.comp_hasDerivAt_of_eq z.1 hpair heval
  have heq : (fun r => f (Z (r, X r x s))) = fun _ : ℝ => f x := by
    funext r
    rw [show Z (r, X r x s) = x from AVenhance.flowInv_leftInverse b _ _ r s x]
  have hh := hd.deriv
  change deriv (fun r => f (Z (r, X r x s))) z.1 = _ at hh
  rw [heq, deriv_const] at hh
  exact hh.symm

/-- Smooth time amplitudes times transported profiles have precisely the
ordinary amplitude derivative as their coarse material derivative. -/
theorem amnr_inverse_flow_material_product {φ : ℝ → Vec 2 → ℝ}
    (hφ : AVenhance.IsAdmissibleStream φ) {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) {c : ℝ → ℝ} (hc : ContDiff ℝ 1 c)
    (s : ℝ) (z : AmnrSpace) :
    amnrOp (fun y => AVenhance.streamVel φ y.1 y.2) none
      (fun y => c y.1 * f (AVenhance.flowInv (AVenhance.streamVel φ)
        hφ.vel_continuous hφ.vel_lipschitz y.1 y.2 s)) z =
      deriv c z.1 * f (AVenhance.flowInv (AVenhance.streamVel φ)
        hφ.vel_continuous hφ.vel_lipschitz z.1 z.2 s) := by
  have hb := AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ
  have hX := AVenhance.flow_isFlow (AVenhance.streamVel φ)
    hφ.vel_continuous hφ.vel_lipschitz
  have hZ : ContDiff ℝ 1 (fun y : AmnrSpace => AVenhance.flowInv
      (AVenhance.streamVel φ) hφ.vel_continuous hφ.vel_lipschitz y.1 y.2 s) := by
    exact (flow_inverse_joint_contDiff_one hb hX).comp
      (show ContDiff ℝ 1 (fun y : AmnrSpace => (y.1, y.2, s)) by fun_prop)
  change amnrOp _ none ((fun y : AmnrSpace => c y.1) *
    (fun y => f (AVenhance.flowInv (AVenhance.streamVel φ)
      hφ.vel_continuous hφ.vel_lipschitz y.1 y.2 s))) z = _
  have hdc : DifferentiableAt ℝ (fun y : AmnrSpace => c y.1) z :=
    (hc.comp contDiff_fst).differentiable (by norm_num) z
  have hdf : DifferentiableAt ℝ (fun y : AmnrSpace => f (AVenhance.flowInv
      (AVenhance.streamVel φ) hφ.vel_continuous hφ.vel_lipschitz y.1 y.2 s)) z :=
    (hf.comp hZ).differentiable (by norm_num) z
  rw [amnrOp_mul none hdc hdf,
    amnrOp_timeOnly (hc.differentiable (by norm_num) z.1),
    amnr_inverse_flow_material_zero hφ hf s z, mul_zero, add_zero]

/-- Every pure material jet of a transported profile differentiates only
its time amplitude. The inverse map is required only to be jointly C¹. -/
theorem amnr_inverse_flow_material_word {φ : ℝ → Vec 2 → ℝ}
    (hφ : AVenhance.IsAdmissibleStream φ) {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) {c : ℝ → ℝ} {N : ℕ} (hc : ContDiff ℝ N c)
    (s : ℝ) (ℓ : ℕ) (hℓ : ℓ ≤ N) :
    amnrWord (fun y => AVenhance.streamVel φ y.1 y.2) (List.replicate ℓ none)
      (fun y => c y.1 * f (AVenhance.flowInv (AVenhance.streamVel φ)
        hφ.vel_continuous hφ.vel_lipschitz y.1 y.2 s)) =
      fun y => iteratedDeriv ℓ c y.1 * f (AVenhance.flowInv (AVenhance.streamVel φ)
        hφ.vel_continuous hφ.vel_lipschitz y.1 y.2 s) := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    rw [List.replicate_succ]
    change amnrOp _ none (amnrWord _ (List.replicate ℓ none) _) = _
    rw [ih (by omega)]
    have hci : ContDiff ℝ 1 (iteratedDeriv ℓ c) :=
      (contDiff_nat_succ_iff_contDiff_one_iteratedDeriv.mp
        (hc.of_le (by exact_mod_cast (show ℓ + 1 ≤ N by omega)))).2
    funext y
    rw [amnr_inverse_flow_material_product hφ hf hci, iteratedDeriv_succ]

/-- The prescribed shear profile is smooth at every finite order. -/
theorem amnr_psi_contDiff {β : ℝ} (I : AVenhance.Ingredients β) (m : ℕ) (k : ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (AVenhance.psi β I.Λ m k) := by
  unfold AVenhance.psi AVenhance.psi0
  split_ifs <;> fun_prop

/-- Exact material jets of the actual stream-recursion summand. Coarse
advection cancels the inverse-flow profile at every material order. -/
theorem amnr_nextStreamTerm_material_word {β : ℝ} (I : AVenhance.Ingredients β)
    {φ : ℝ → Vec 2 → ℝ} (hφ : AVenhance.IsAdmissibleStream φ)
    (m : ℕ) (k : ℤ) (ℓ : ℕ) :
    amnrWord (fun y => AVenhance.streamVel φ y.1 y.2) (List.replicate ℓ none)
      (fun y => I.nextStreamTerm m φ hφ y.1 y.2 k) =
      fun y => iteratedDeriv ℓ (I.hatZetaML m (AVenhance.lIdx β I.Λ m k) * I.zetaMK m k) y.1 *
        AVenhance.psi β I.Λ m k (AVenhance.flowInv (AVenhance.streamVel φ)
          hφ.vel_continuous hφ.vel_lipschitz y.1 y.2
            ((AVenhance.lIdx β I.Λ m k : ℝ) * AVenhance.tauPP β I.Λ m)) := by
  have hh : ContDiff ℝ (⊤ : ℕ∞) (I.hatZetaML m (AVenhance.lIdx β I.Λ m k)) := by
    unfold AVenhance.Ingredients.hatZetaML AVenhance.shiftCutoff
    exact (I.hatZeta_smooth m).comp (by fun_prop)
  have hz : ContDiff ℝ (⊤ : ℕ∞) (I.zetaMK m k) := by
    unfold AVenhance.Ingredients.zetaMK AVenhance.scaledCutoff
    exact I.zeta_smooth.comp (by fun_prop)
  exact amnr_inverse_flow_material_word (N := ℓ) hφ ((amnr_psi_contDiff I m k).of_le (by simp))
    ((hh.mul hz).of_le (by simp)) _ ℓ le_rfl

end AVenhance.Infra.Section4
