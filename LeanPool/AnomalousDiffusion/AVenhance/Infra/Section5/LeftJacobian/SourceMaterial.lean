/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.Transport
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.SourceHelpers
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.StreamFlowPiola

/-!: the source material equation for the names.

This is `frozen_source_material_equation` with the two corrected-form inputs switched in:
the coarse coefficient (`I.sMat = sMatPlus`) and the base tensor
(`I.Amnr · 0 = amnrBasePlus`); both are `rfl` (`sMat_eq_sMatPlus`,
`Amnr_zero_eq_amnrBasePlus`). The conclusion is the transport equation with the Piola flux `V_tr`
(`transportFluxPlus`) and the corrected-form forcing error `d⁺` (`sourceErrorDPlus`). -/

@[expose] public section

noncomputable section

open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.LeftJacobian

open AVenhance AVenhance.Infra.Section5

/-- Pure regrouping of the four vector fields of the split. -/
theorem add_four_regroup {a B tr fs iter tail : Vec 2} (h : a + B = tr + fs) :
    a + iter + tail + B = tr + (fs + tail) + iter := by
  calc a + iter + tail + B = (a + B) + iter + tail := by abel
    _ = _ := by rw [h]; abel

/-- corrected-form source material equation for the `T`, `H_m`.

Regularity hypotheses (the analogues of `hAvg`, `hTail`, `hGap` of
`frozen_source_material_equation`; each is the differentiability at `x` of one of the three
vector fields whose divergence is split):
* `hAvg`: `y ↦ (K + s⁺(y)) ∇T(y) + iterateError(y)` (the transported-iterate flux);
* `hTail`: the terminal tensor flux `Σ_n A_{n,Jcut} q_{n,Jcut}`;
* `hBase`: the base-flux field `y ↦ Σ_l ξ̂_l F_lᵀ(JHat - K)F_l ∇T`. -/
theorem variantA_source_material_equation
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m)
    (κm κprev : ℝ) (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ) (hT : Ingredients.IsTIterates I hΦ m κm κprev θ₀ θprev T)
    (t : ℝ) (ht : 0 < t) (x : Vec 2)
    (Dt : ℕ → ℝ) (LH : ℕ → Vec 2 →L[ℝ] ℝ)
    (hDt : ∀ r ∈ Finset.range (Jcut β),
      HasDerivAt (fun s => I.Hmr hΦ m κm (T (Nstar β)) r s x) (Dt r) t)
    (hDx : ∀ r ∈ Finset.range (Jcut β),
      HasFDerivAt (I.Hmr hΦ m κm (T (Nstar β)) r t) (LH r) x)
    (hA : ∀ r ∈ Finset.range (Jcut β),
      ∀ (n : ℕ) (i j k : Fin 2) (z : ST), 0 < z.1 →
        DifferentiableAt ℝ
          (fun w : ST => I.Amnr hΦ m κm n (T (Nstar β)) r w.1 w.2 i j k) z)
    (hPair : ∀ r ∈ Finset.range (Jcut β),
      ∀ (a : AmnrPairIndex) (z : ST), 0 < z.1 →
        DifferentiableAt ℝ (amnrPairFlux I hΦ m κm (T (Nstar β)) r a) z)
    (hFlux : ∀ r ∈ Finset.range (Jcut β),
      ContDiffAt ℝ 2
        (amnrPairFluxSum I hΦ m (Nstar β) κm (T (Nstar β)) r) (t, x))
    (hEndNext : ∀ r ∈ Finset.range (Jcut β),
      DifferentiableAt ℝ
        (amnrPairEndpointFluxSum I hΦ m (Nstar β) κm (T (Nstar β)) (r + 1)) (t, x))
    (hEnd : ∀ r ∈ Finset.range (Jcut β),
      DifferentiableAt ℝ
        (amnrPairEndpointFluxSum I hΦ m (Nstar β) κm (T (Nstar β)) r) (t, x))
    (hAvg : DifferentiableAt ℝ
      (fun y => (I.Kmat κm m t + sMatPlus I hΦ m κm t y).mulVec
          (spaceGrad (T (Nstar β) t) y) +
        iterateError I hΦ m κm κprev T t y) x)
    (hTail : DifferentiableAt ℝ
      (terminalTail I hΦ m κm (T (Nstar β)) t) x)
    (hBase : DifferentiableAt ℝ
      (fun y => ∑' l : ℤ, I.hatXiML m l t •
        ((I.flowGrad hΦ m l t y).transpose.mulVec
          ((I.Jhat κm m t - I.Kmat κm m t).mulVec
            ((I.flowGrad hΦ m l t y).mulVec (spaceGrad (T (Nstar β) t) y))))) x) :
    deriv (fun s => T (Nstar β) s x) t +
        vecDot (streamVel (Φ (m - 1)) t x)
          (spaceGrad (T (Nstar β) t) x) +
        deriv (fun s => I.Hm hΦ m κm (T (Nstar β)) s x) t +
        fderiv ℝ (I.Hm hΦ m κm (T (Nstar β)) t) x
          (streamVel (Φ (m - 1)) t x) =
      vecDiv (fun y => transportFluxPlus I hΦ m κm (T (Nstar β)) t y +
        sourceErrorDPlus I hΦ m κm (T (Nstar β)) t y +
        iterateError I hΦ m κm κprev T t y) x := by
  rcases hT with ⟨hzero, hstep⟩
  have hTm := final_iterate_transport_eq_of_classical I hΦ m hm κm κprev
    θ₀ θprev T ⟨hzero, hstep⟩ (t := t) (x := x) ht
  simp only [sMat_eq_sMatPlus] at hTm
  have hHm := frozen_Hm_material_equation I hΦ m κm
    (T (Nstar β)) t x ht Dt LH hDt hDx
    (by
      change ContDiff ℝ 2 (Function.uncurry (streamVel (Φ (m - 1))))
      exact (Infra.Construction.smoothPeriodic_streamVel
        (hΦ.adm_pred m)).smooth.of_le (by norm_num))
    (by
      let φ := Φ (m - 1)
      have hφ : IsAdmissibleStream φ := hΦ.adm_pred m
      intro z
      rw [stDiv_eq_vecDiv (F := fun w : ST => streamVel φ w.1 w.2)
        (t := z.1) (x := z.2)
        (by
          have hb := Infra.Classical.streamVel_smoothPeriodic φ hφ
          have h := hb.smooth.differentiable (by norm_num) (z.1, z.2)
          simpa [Function.uncurry] using h)]
      exact Infra.Classical.streamVel_vecDiv_eq_zero φ hφ z.1 z.2)
    hA hPair hFlux hEndNext hEnd
  have hterm : hmEndpoint I hΦ m κm (T (Nstar β)) (Jcut β) t x =
      vecDiv (terminalTail I hΦ m κm (T (Nstar β)) t) x := rfl
  have hbase := variantA_hmEndpoint_zero I hΦ m hm κm (T (Nstar β)) t x
  rw [hterm, hbase] at hHm
  have hfields : (fun y =>
      ((I.Kmat κm m t + sMatPlus I hΦ m κm t y).mulVec
          (spaceGrad (T (Nstar β) t) y) +
        iterateError I hΦ m κm κprev T t y) +
        terminalTail I hΦ m κm (T (Nstar β)) t y +
        ∑' l : ℤ, I.hatXiML m l t •
          ((I.flowGrad hΦ m l t y).transpose.mulVec
            ((I.Jhat κm m t - I.Kmat κm m t).mulVec
              ((I.flowGrad hΦ m l t y).mulVec (spaceGrad (T (Nstar β) t) y))))) =
      fun y => transportFluxPlus I hΦ m κm (T (Nstar β)) t y +
        sourceErrorDPlus I hΦ m κm (T (Nstar β)) t y +
        iterateError I hΦ m κm κprev T t y := by
    funext y
    have hdec := transport_decomposition I hΦ m hm κm (T (Nstar β)) t y
    rw [sourceErrorDPlus_eq]
    exact add_four_regroup hdec
  have hsum := vecDiv_add3_of_differentiableAt hAvg hTail hBase
  rw [hfields] at hsum
  rw [hsum]
  linarith [hTm, hHm]

end AVenhance.Infra.Section5.LeftJacobian

end
