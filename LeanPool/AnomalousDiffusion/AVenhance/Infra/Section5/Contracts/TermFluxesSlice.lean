/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermFluxesJoint
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TIterateSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesDiffusion
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowGlobalJointSmoothness
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowSpatialPeriodicity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.MovingFluxEnergy

/-! # Fixed-time smoothness and periodicity of the flux ingredients

At a fixed time the `ξ`-sums are finite, `ψTilde_m` and the diffusion matrix are smooth and
`ℤ²`-periodic (actual flow and inverse flow are lattice equivariant), and `G_l`, `∇G_l`,
`uShear ∘ X⁻¹` are smooth and periodic when the temperature slice is. -/

@[expose] public section

open Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-! ### The generic flux form at a fixed time -/

theorem tfFlux_slice_contDiff (c : {k : ℤ // Odd k} → ℝ → ℝ)
    (D : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (W : {k : ℤ // Odd k} → ℝ → Vec 2 → Vec 2)
    (t : ℝ) (hfin : {k : {k : ℤ // Odd k} | c k t ≠ 0}.Finite)
    (hD : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => D t x i j))
    (hW : ∀ k j, ContDiff ℝ (⊤ : ℕ∞) (fun x => W k t x j)) :
    ContDiff ℝ (⊤ : ℕ∞) (tfFlux c D W t) := by
  classical
  have hfun : tfFlux c D W t = fun x =>
      ∑ k ∈ hfin.toFinset, c k t • (D t x).mulVec (W k t x) := by
    funext x
    refine tsum_eq_sum fun k hk => ?_
    have : c k t = 0 := by
      by_contra hne
      exact hk ((Set.Finite.mem_toFinset hfin).2 hne)
    simp [this]
  rw [hfun]
  refine ContDiff.sum fun k _ => ContDiff.const_smul _ ?_
  rw [← contDiffOn_univ]
  exact contDiffOn_pi.2 fun i => tf_mulVec_contDiffOn (s := Set.univ)
    (fun i j => (hD i j).contDiffOn) (fun j => (hW k j).contDiffOn) i

theorem tfFlux_periodic (c : {k : ℤ // Odd k} → ℝ → ℝ)
    (D : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (W : {k : ℤ // Odd k} → ℝ → Vec 2 → Vec 2)
    (t : ℝ) (hD : IsZ2Periodic (D t)) (hW : ∀ k, IsZ2Periodic (W k t)) :
    IsZ2Periodic (tfFlux c D W t) := by
  intro n x
  unfold tfFlux
  refine tsum_congr fun k => ?_
  rw [hD n x, hW k n x]

/-! ### The diffusion matrix at a fixed time -/

theorem tf_sin_shift (a : ℝ) (z : ℤ) :
    Real.sin (2 * Real.pi * (a + z)) = Real.sin (2 * Real.pi * a) := by
  rw [show 2 * Real.pi * (a + z) = 2 * Real.pi * a + z * (2 * Real.pi) by ring]
  exact Real.sin_add_int_mul_two_pi _ _

theorem tf_psi_periodic (m : ℕ) (k : ℤ) : IsZ2Periodic (psi β I.Λ m k) := by
  intro n x
  obtain ⟨N, hN⟩ := epsilon_inv_exists_nat β I.Λ m
  have key : ∀ c : Fin 2, (epsilon β I.Λ m)⁻¹ * (x c + (n c : ℝ)) =
      (epsilon β I.Λ m)⁻¹ * x c + ((n c * (N : ℤ) : ℤ) : ℝ) := by
    intro c
    rw [mul_add, hN]
    push_cast
    ring
  simp only [psi, psi0, Pi.smul_apply, Pi.add_apply, smul_eq_mul, latticeShift]
  rw [key 0, key 1, tf_sin_shift, tf_sin_shift]

theorem tf_psiTilde_periodic (hΦ : IsStreamSeq I Φ) (m : ℕ) (t : ℝ) :
    IsZ2Periodic (psiTilde I hΦ m t) := by
  intro n x
  unfold psiTilde
  refine tsum_congr fun k => ?_
  rw [Infra.Section4.amnr_xFlowInv_lattice_equivariant I hΦ m _ t n x, tf_psi_periodic I m k.1 n]

theorem tf_diffusion_periodic (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm t : ℝ) :
    IsZ2Periodic (diffusionMatrix I hΦ m κm t) := by
  intro n x
  unfold diffusionMatrix
  rw [tf_psiTilde_periodic I hΦ m t n x]

theorem tf_diffusion_slice_contDiff (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm t : ℝ) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => diffusionMatrix I hΦ m κm t x i j) :=
  (tf_diffusion_contDiff I hΦ m κm i j).comp (contDiff_prodMk_right t)

/-! ### `G_l`, `∇G_l`, the pulled-back shear -/

theorem tf_G_slice_contDiff (hΦ : IsStreamSeq I Φ) (m : ℕ) (T : ℝ → Vec 2 → ℝ) (t : ℝ) (l : ℤ)
    (hT : ContDiff ℝ (⊤ : ℕ∞) (T t)) :
    ContDiff ℝ (⊤ : ℕ∞) (G I hΦ m T l t) := by
  let f : Vec 2 → ℝ := fun y => T t (I.xFlow hΦ m l t y)
  have hflow : ContDiff ℝ (⊤ : ℕ∞) (I.xFlow hΦ m l t) :=
    (Infra.Section4.amnr_xFlow_joint_contDiff_infty I hΦ m l).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)))
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := hT.comp hflow
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (spaceGrad f) := Infra.Section4.iterate_gradient_smooth hf
  have hinv : ContDiff ℝ (⊤ : ℕ∞) (I.xFlowInv hΦ m l t) :=
    (Infra.Section4.amnr_xFlowInv_joint_contDiff_infty I hΦ m l).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
  change ContDiff ℝ (⊤ : ℕ∞) (spaceGrad f ∘ I.xFlowInv hΦ m l t)
  exact hgrad.comp hinv

theorem tf_G_slice_periodic (hΦ : IsStreamSeq I Φ) (m : ℕ) (T : ℝ → Vec 2 → ℝ) (t : ℝ) (l : ℤ)
    (hT : IsZ2Periodic (T t)) :
    IsZ2Periodic (G I hΦ m T l t) := by
  let f : Vec 2 → ℝ := fun y => T t (I.xFlow hΦ m l t y)
  have hflowper := Infra.Section4.amnr_xFlow_lattice_equivariant I hΦ m l t
  have hinvper := Infra.Section4.amnr_xFlowInv_lattice_equivariant I hΦ m l t
  have hfper : IsZ2Periodic f := by
    intro k x
    dsimp [f]
    rw [hflowper k x]
    exact hT k (I.xFlow hΦ m l t x)
  intro k x
  change spaceGrad f (I.xFlowInv hΦ m l t (x + latticeShift k)) =
    spaceGrad f (I.xFlowInv hΦ m l t x)
  rw [hinvper k x]
  exact spaceGrad_isZ2Periodic hfper k _

theorem tf_gradG_slice_contDiff (hΦ : IsStreamSeq I Φ) (m : ℕ) (T : ℝ → Vec 2 → ℝ) (t : ℝ)
    (l : ℤ) (hT : ContDiff ℝ (⊤ : ℕ∞) (T t)) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => gradG I hΦ m T l t x i j) :=
  contDiff_spaceGrad_component (f := fun y => G I hΦ m T l t y j)
    (contDiff_pi.1 (tf_G_slice_contDiff I hΦ m T t l hT) j) i

theorem tf_gradG_slice_periodic (hΦ : IsStreamSeq I Φ) (m : ℕ) (T : ℝ → Vec 2 → ℝ) (t : ℝ)
    (l : ℤ) (hT : IsZ2Periodic (T t)) (i j : Fin 2) :
    IsZ2Periodic (fun x => gradG I hΦ m T l t x i j) := by
  intro n x
  have hG := tf_G_slice_periodic I hΦ m T t l hT
  have hGj : IsZ2Periodic (fun y => G I hΦ m T l t y j) := fun n y => congrFun (hG n y) j
  exact congrFun (spaceGrad_isZ2Periodic hGj n x) i

theorem tf_chiW_slice_contDiff (hΦ : IsStreamSeq I Φ) (m : ℕ) (T : ℝ → Vec 2 → ℝ) (t : ℝ)
    (k : ℤ) (hT : ContDiff ℝ (⊤ : ℕ∞) (T t)) (i : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => tfChiW I hΦ m T k t x i) := by
  unfold tfChiW
  refine ContDiff.sum fun j _ => ContDiff.mul ?_ (tf_gradG_slice_contDiff I hΦ m T t _ hT i j)
  have hXI : ContDiff ℝ (⊤ : ℕ∞) (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) :=
    (xFlowInv_joint_contDiff_infty I hΦ m (lIdx β I.Λ m k)).comp (contDiff_prodMk_right t)
  exact ((contDiff_apply ℝ ℝ j).comp ((contDiff_uShear' β I.Λ m k).comp hXI)).neg

theorem tf_chiW_slice_periodic (hΦ : IsStreamSeq I Φ) (m : ℕ) (T : ℝ → Vec 2 → ℝ) (t : ℝ)
    (k : ℤ) (hT : IsZ2Periodic (T t)) : IsZ2Periodic (tfChiW I hΦ m T k t) := by
  intro n x
  funext i
  unfold tfChiW
  refine Finset.sum_congr rfl fun j _ => ?_
  have hg : gradG I hΦ m T (lIdx β I.Λ m k) t (x + latticeShift n) i j =
      gradG I hΦ m T (lIdx β I.Λ m k) t x i j :=
    tf_gradG_slice_periodic I hΦ m T t _ hT i j n x
  rw [Infra.Section4.amnr_xFlowInv_lattice_equivariant I hΦ m _ t n x,
    uShear_isZ2Periodic β I.Λ m k n, hg]

/-! ### The three fluxes at a fixed time -/

theorem tf_twistie3Flux_slice (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (hs : ContDiff ℝ (⊤ : ℕ∞) (T t)) (hp : IsZ2Periodic (T t)) :
    ContDiff ℝ (⊤ : ℕ∞) (twistie3Flux I hΦ m κm T t) ∧
      IsZ2Periodic (twistie3Flux I hΦ m κm T t) := by
  refine ⟨tfFlux_slice_contDiff (fun k t => I.xiMK m k.1 t)
    (fun t x => diffusionMatrix I hΦ m κm t x)
    (fun k t x => spaceGrad (T t) x - G I hΦ m T (lIdx β I.Λ m k.1) t x) t
    (Infra.Section3.xiMK_odd_support_finite I hm t) (tf_diffusion_slice_contDiff I hΦ m κm t)
    (fun k j => ?_), tfFlux_periodic (fun k t => I.xiMK m k.1 t)
    (fun t x => diffusionMatrix I hΦ m κm t x)
    (fun k t x => spaceGrad (T t) x - G I hΦ m T (lIdx β I.Λ m k.1) t x) t
    (tf_diffusion_periodic I hΦ m κm t) (fun k => ?_)⟩
  · exact (contDiff_pi.1 ((Infra.Section4.iterate_gradient_smooth hs).sub
      (tf_G_slice_contDiff I hΦ m T t _ hs)) j)
  · intro n x
    change spaceGrad (T t) (x + latticeShift n) - G I hΦ m T (lIdx β I.Λ m k.1) t (x + latticeShift
        n) =
      spaceGrad (T t) x - G I hΦ m T (lIdx β I.Λ m k.1) t x
    rw [spaceGrad_isZ2Periodic hp n x, tf_G_slice_periodic I hΦ m T t _ hp n x]

theorem tf_normie1Flux_slice (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (hs : ContDiff ℝ (⊤ : ℕ∞) (T t)) (hp : IsZ2Periodic (T t)) :
    ContDiff ℝ (⊤ : ℕ∞) (normie1Flux I hΦ m κm T t) ∧
      IsZ2Periodic (normie1Flux I hΦ m κm T t) := by
  have heq : normie1Flux I hΦ m κm T t = tfFlux (fun k t => I.xiMK m k.1 t * I.corrTime κm m k.1 t)
      (fun t x => diffusionMatrix I hΦ m κm t x) (fun k t x => tfChiW I hΦ m T k.1 t x) t :=
    funext fun x => tf_normie1Flux_eq I hΦ m κm T t x
  rw [heq]
  refine ⟨tfFlux_slice_contDiff _ _ _ t ?_ (tf_diffusion_slice_contDiff I hΦ m κm t)
    (fun k j => tf_chiW_slice_contDiff I hΦ m T t k.1 hs j),
    tfFlux_periodic _ _ _ t (tf_diffusion_periodic I hΦ m κm t)
    (fun k => tf_chiW_slice_periodic I hΦ m T t k.1 hp)⟩
  refine (Infra.Section3.xiMK_odd_support_finite I hm t).subset fun k hk => ?_
  intro h
  exact hk (by simp [h])

theorem tf_normie2Flux_slice (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (hs : ContDiff ℝ (⊤ : ℕ∞) (I.Hm hΦ m κm T t))
    (hp : IsZ2Periodic (I.Hm hΦ m κm T t)) :
    ContDiff ℝ (⊤ : ℕ∞) (normie2Flux I hΦ m κm T t) ∧
      IsZ2Periodic (normie2Flux I hΦ m κm T t) := by
  refine ⟨?_, fun n x => ?_⟩
  · rw [← contDiffOn_univ]
    exact contDiffOn_pi.2 fun i => tf_mulVec_contDiffOn (s := Set.univ)
      (A := fun x => diffusionMatrix I hΦ m κm t x)
      (v := fun x => spaceGrad (fun z => I.Hm hΦ m κm T t z) x)
      (fun i j => (tf_diffusion_slice_contDiff I hΦ m κm t i j).contDiffOn)
      (fun j => (contDiff_pi.1 (Infra.Section4.iterate_gradient_smooth hs) j).contDiffOn) i
  · change (diffusionMatrix I hΦ m κm t (x + latticeShift n)).mulVec
        (spaceGrad (fun z => I.Hm hΦ m κm T t z) (x + latticeShift n)) =
      (diffusionMatrix I hΦ m κm t x).mulVec (spaceGrad (fun z => I.Hm hΦ m κm T t z) x)
    rw [tf_diffusion_periodic I hΦ m κm t n x, spaceGrad_isZ2Periodic hp n x]

end AVenhance.Infra.Section5.Contracts
end
