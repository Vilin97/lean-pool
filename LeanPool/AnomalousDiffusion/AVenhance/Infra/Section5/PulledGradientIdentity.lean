/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.ClassicalRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FlowGradientRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.GradientChain
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MaterialGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MatrixTransport
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.PulledGradientTransport
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.TEquationRegularity

/-! Material transport of the flow-pulled iterate gradient. -/

@[expose] public section

open Homogenization Filter Topology
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5

open AVenhance Infra.Flow

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The pulled gradient of the last T-iterate satisfies the source
transport identity `e.tbm1.two`. The forcing from the finite iteration tail
is retained in the divergence, exactly as in the source's `e_{m-1}`. -/
theorem final_iterate_pulled_gradient_transport
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κm κprev : ℝ)
    (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ)
    (hT : Ingredients.IsTIterates I hΦ m κm κprev θ₀ θprev T)
    (l : ℤ) {t : ℝ} (ht : 0 < t) (y : Vec 2) (i : Fin 2) :
    deriv (fun r => G I hΦ m (T (Nstar β)) l r
      (I.xFlow hΦ m l r y) i) t =
      (I.flowGrad hΦ m l t (I.xFlow hΦ m l t y)).mulVec
        (gradDiv (fun r z =>
          (I.Kmat κm m r + I.sMat hΦ m κm r z).mulVec
            (spaceGrad (T (Nstar β) r) z) +
          iterateError I hΦ m κm κprev T r z)
          t (I.xFlow hΦ m l t y)) i := by
  rcases hT with ⟨hzero, hstep⟩
  have hN : 1 ≤ Nstar β := by
    have h := AVenhance.Infra.Ingredients.Nstar_ge_256 I.one_lt_beta I.beta_lt
    omega
  let Tm : ℝ → Vec 2 → ℝ := T (Nstar β)
  let b : ℝ → Vec 2 → Vec 2 := streamVel (Φ (m - 1))
  let X : ℝ → Vec 2 → ℝ → Vec 2 := flow b
    (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz
  let s : ℝ := (l : ℝ) * tauPP β I.Λ m
  let z : Vec 2 := I.xFlow hΦ m l t y
  let V : ℝ → Vec 2 → Vec 2 := fun r q =>
    (I.Kmat κm m r + I.sMat hΦ m κm r q).mulVec (spaceGrad (Tm r) q) +
      iterateError I hΦ m κm κprev T r q
  have hsol : IsClassicalSol b κprev
      (I.TForcing hΦ m κm κprev (T (Nstar β - 1))) θ₀ Tm := by
    exact hstep (Nstar β) hN le_rfl
  have hX : IsFlow b X :=
    flow_isFlow b (hΦ.adm_pred m).vel_continuous
      (hΦ.adm_pred m).vel_lipschitz
  have hb : SmoothPeriodicField b :=
    Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m)
  have hinv (r : ℝ) :
      I.xFlowInv hΦ m l r (I.xFlow hΦ m l r y) = y := by
    change X s (X r y s) r = y
    calc
      X s (X r y s) r = X s y s :=
        Infra.Flow.flow_group_law b (hΦ.adm_pred m).vel_lipschitz hX y s r s
      _ = y := hX.1 y s
  have hpde (q : Vec 2) :
      deriv (fun r => Tm r q) t + vecDot (b t q) (spaceGrad (Tm t) q) =
        vecDiv (V t) q := by
    exact final_iterate_transport_eq_of_classical I hΦ m hm κm κprev θ₀
      θprev T ⟨hzero, hstep⟩ (t := t) (x := q) ht
  have hmaterial (q : Vec 2) :
      materialDerivative Tm b t q = vecDiv (V t) q := by
    rw [materialDerivative_eq_advective_of_hasFDerivAt
      (classicalSol_hasFDerivAt_of_pos hsol ht q)]
    exact hpde q
  let A : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun r =>
    I.flowGrad hΦ m l r (I.xFlow hΦ m l r y)
  let g : ℝ → Vec 2 := fun r =>
    spaceGrad (Tm r) (I.xFlow hΦ m l r y)
  let C : Matrix (Fin 2) (Fin 2) ℝ := gradMatrix (b t) z
  let h : Vec 2 := spaceGrad (fun q => vecDiv (V t) q) z
  have hTjoint : ContDiffAt ℝ 2 (Function.uncurry Tm) (t, z) :=
    (classicalSol_contDiffAt_of_pos hsol ht z).of_le (by norm_num)
  have hbjoint : ContDiffAt ℝ 1 (Function.uncurry b) (t, z) :=
    hb.smooth.contDiffAt.of_le (by norm_num)
  have hgradEventually (j : Fin 2) :
      (fun r => spaceGrad (Tm r) (I.xFlow hΦ m l r y) j) =ᶠ[𝓝 t]
        fun r => fderiv ℝ (Function.uncurry Tm)
          (r, I.xFlow hΦ m l r y) (0, basisVec j) := by
    exact classicalSol_spaceGrad_eq_jointFDeriv_eventually hsol ht
      (fun r => I.xFlow hΦ m l r y) j
  have hgradMaterial (j : Fin 2) :
      spaceGrad (materialDerivative Tm b t) z j = h j := by
    have heq : materialDerivative Tm b t = fun q => vecDiv (V t) q := by
      funext q
      exact hmaterial q
    exact congrArg (fun f : Vec 2 → ℝ => spaceGrad f z j) heq
  have hbdiff : DifferentiableAt ℝ (b t) z :=
    by
      have hjoint : DifferentiableAt ℝ (Function.uncurry b) (t, z) :=
        hb.smooth.differentiable (by norm_num) (t, z)
      have hspace := hjoint.hasFDerivAt.comp z (hasFDerivAt_prodMk_right t z)
      simpa [Function.uncurry, Function.comp_def] using hspace.differentiableAt
  have hcorrection (j : Fin 2) :
      fderiv ℝ (Function.uncurry Tm) (t, z)
          (0, fderiv ℝ (Function.uncurry b) (t, z) (0, basisVec j)) =
        ∑ p : Fin 2, C j p * g t p := by
    rw [fderiv_uncurry_scalar_spatial
      (hTjoint.differentiableAt (by norm_num))]
    rw [fderiv_uncurry_vector_spatial
      (hbjoint.differentiableAt (by norm_num))]
    rw [fderiv_scalar_eq_sum_spaceGrad]
    apply Finset.sum_congr rfl
    intro p hp
    have hentry : C j p = fderiv ℝ (b t) z (basisVec j) p := by
      exact (gradMatrix_entry_eq_fderiv hbdiff j p)
    rw [← hentry]
  have hg (j : Fin 2) : HasDerivAt (fun r => g r j)
      (h j - ∑ p : Fin 2, C j p * g t p) t := by
    have hderiv := gradient_material_deriv_along_flow hX (t := t) (s := s)
      (y := y) j hTjoint hbjoint (hgradEventually j)
    have hrate :
        spaceGrad (materialDerivative Tm b t) (X t y s) j -
          fderiv ℝ (Function.uncurry Tm) (t, X t y s)
            (0, fderiv ℝ (Function.uncurry b) (t, X t y s) (0, basisVec j)) =
        h j - ∑ p : Fin 2, C j p * g t p := by
      rw [show X t y s = z by simp [z, b, X, s, Ingredients.xFlow],
        hgradMaterial j, hcorrection j]
    simpa [g, b, X, s, Ingredients.xFlow] using hderiv.congr_deriv hrate
  have hXdiff : DifferentiableAt ℝ (I.xFlow hΦ m l t) y :=
    xFlow_spatial_contDiff_two I hΦ m l t |>.differentiable
      (by norm_num) y
  have hAentry (p : Fin 2) :
      A t i p = fderiv ℝ (I.xFlow hΦ m l t) y (basisVec i) p := by
    change gradMatrix (I.xFlow hΦ m l t)
      (I.xFlowInv hΦ m l t (I.xFlow hΦ m l t y)) i p = _
    rw [hinv t]
    exact gradMatrix_entry_eq_fderiv hXdiff i p
  have hbrate : ∀ j : Fin 2,
      jointSpatialFDeriv b t z
          (fderiv ℝ (I.xFlow hΦ m l t) y (basisVec i)) j =
        ∑ p : Fin 2, A t i p * C p j := by
    intro j
    rw [jointSpatialFDeriv_eq_slice hb]
    rw [fderiv_vector_component_eq_sum_gradMatrix hbdiff j]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hAentry p]
  have hA (j : Fin 2) : HasDerivAt (fun r => A r i j)
      (∑ p : Fin 2, A t i p * C p j) t := by
    have hderiv := flowGrad_material_deriv_component I hΦ m l t y i j
    simpa [A, b, X, s, C, Ingredients.xFlow] using hderiv.congr_deriv (hbrate j)
  have hproduct : HasDerivAt (fun r => (A r).mulVec (g r) i)
      ((A t).mulVec h i) t :=
    hasDerivAt_matrixVec_mul_transport i hA hg
  have hrepresentation :
      (fun r => G I hΦ m Tm l r (I.xFlow hΦ m l r y) i) =ᶠ[𝓝 t]
        fun r => (A r).mulVec (g r) i := by
    filter_upwards [Ioi_mem_nhds ht] with r hr
    have hTslice : HasFDerivAt (Tm r)
        (fderiv ℝ (Tm r) (I.xFlow hΦ m l r y)) (I.xFlow hΦ m l r y) := by
      exact ((classicalSol_space_contDiff_of_nonneg hsol (le_of_lt hr)).differentiable
        (by norm_num) (I.xFlow hΦ m l r y)).hasFDerivAt
    have hXsliceY : HasFDerivAt (I.xFlow hΦ m l r)
        (fderiv ℝ (I.xFlow hΦ m l r) y) y := by
      exact ((xFlow_spatial_contDiff_two I hΦ m l r).differentiable
        (by norm_num) y).hasFDerivAt
    have hXslice : HasFDerivAt (I.xFlow hΦ m l r)
        (fderiv ℝ (I.xFlow hΦ m l r) y)
        (I.xFlowInv hΦ m l r (I.xFlow hΦ m l r y)) := by
      simpa [hinv r] using hXsliceY
    have hinvRight : I.xFlow hΦ m l r
        (I.xFlowInv hΦ m l r (I.xFlow hΦ m l r y)) =
          I.xFlow hΦ m l r y := by
      change X r (X s (X r y s) r) s = X r y s
      calc
        X r (X s (X r y s) r) s = X r (X r y s) r :=
          Infra.Flow.flow_group_law b (hΦ.adm_pred m).vel_lipschitz hX
            (X r y s) r s r
        _ = X r y s := hX.1 (X r y s) r
    have hrep := G_eq_flowGrad_mulVec I hΦ m Tm l r
      (I.xFlow hΦ m l r y) hTslice hXslice hinvRight
    simpa [A, g] using congrArg (fun v : Vec 2 => v i) hrep
  have hproduct' := hproduct.congr_of_eventuallyEq hrepresentation
  simpa [A, g, h, V, Tm, b, X, s, z, Ingredients.xFlow, gradDiv] using
    hproduct'.deriv

end AVenhance.Infra.Section5

end
