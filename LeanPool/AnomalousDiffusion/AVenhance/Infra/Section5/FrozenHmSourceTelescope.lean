/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FrozenHmSourceIdentity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FrozenHmTelescope

/-! Source-specific finite telescope for the `H_m` potential. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5

open AVenhance
open Homogenization

variable {β : ℝ} (I : Ingredients β)
variable {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)

/-- The `H_m` material equation follows by telescoping the proved
per-index `A/q` steps. `hDt` and `hDx` state the time and spatial
differentiability used for the finite sum; all transport increments are
derived from and the primitive recursion for `q`. -/
theorem frozen_Hm_material_equation
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2)
    (ht : 0 < t)
    (Dt : ℕ → ℝ) (LH : ℕ → Vec 2 →L[ℝ] ℝ)
    (hDt : ∀ r ∈ Finset.range (Jcut β),
      HasDerivAt (fun s => I.Hmr hΦ m κ T r s x) (Dt r) t)
    (hDx : ∀ r ∈ Finset.range (Jcut β),
      HasFDerivAt (I.Hmr hΦ m κ T r t) (LH r) x)
    (hb : ContDiff ℝ 2
      (fun z : ST => streamVel (Φ (m - 1)) z.1 z.2))
    (hdiv : ∀ z : ST,
      stDiv (fun w => streamVel (Φ (m - 1)) w.1 w.2) z = 0)
    (hA : ∀ r ∈ Finset.range (Jcut β),
      ∀ (n : ℕ) (i j k : Fin 2) (z : ST), 0 < z.1 →
        DifferentiableAt ℝ
          (fun w : ST => I.Amnr hΦ m κ n T r w.1 w.2 i j k) z)
    (hPair : ∀ r ∈ Finset.range (Jcut β),
      ∀ (a : AmnrPairIndex) (z : ST), 0 < z.1 →
        DifferentiableAt ℝ (amnrPairFlux I hΦ m κ T r a) z)
    (hFlux : ∀ r ∈ Finset.range (Jcut β),
      ContDiffAt ℝ 2 (amnrPairFluxSum I hΦ m (Nstar β) κ T r) (t, x))
    (hEndNext : ∀ r ∈ Finset.range (Jcut β),
      DifferentiableAt ℝ
        (amnrPairEndpointFluxSum I hΦ m (Nstar β) κ T (r + 1)) (t, x))
    (hEnd : ∀ r ∈ Finset.range (Jcut β),
      DifferentiableAt ℝ
        (amnrPairEndpointFluxSum I hΦ m (Nstar β) κ T r) (t, x)) :
    deriv (fun s => I.Hm hΦ m κ T s x) t +
        fderiv ℝ (I.Hm hΦ m κ T t) x
          (streamVel (Φ (m - 1)) t x) =
      hmEndpoint I hΦ m κ T (Jcut β) t x - hmEndpoint I hΦ m κ T 0 t x := by
  let b : ℝ → Vec 2 → Vec 2 := fun s y => streamVel (Φ (m - 1)) s y
  have hstep : ∀ r ∈ Finset.range (Jcut β),
      Dt r + LH r (b t x) =
        hmEndpoint I hΦ m κ T (r + 1) t x - hmEndpoint I hΦ m κ T r t x := by
    intro r hr
    have hmaterial := frozen_Hmr_material_step I hΦ m κ T r t x ht hb hdiv
      (hA r hr) (hPair r hr) (hFlux r hr) (hEndNext r hr) (hEnd r hr)
    rw [(hDt r hr).deriv, (hDx r hr).fderiv] at hmaterial
    exact hmaterial
  exact frozen_hm_material_telescope I hΦ m κ T b t x Dt LH
    hDt hDx hstep

end AVenhance.Infra.Section5

end
