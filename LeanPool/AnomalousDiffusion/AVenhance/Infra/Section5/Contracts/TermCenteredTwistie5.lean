/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredTwistie
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredTime
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesFlux

/-! # `Twistie5CenteredSourceContract`

In the corrected form, `twistie5 = -div(flux)` (`twistie5_eq_neg_div_flux`) is a pure divergence
    of a smooth
periodic flux, so the proof is flux-only: the centered `HDot⁻¹` norm of a slice is at most the `L²`
norm of the flux (`sd_tw5_time_bound`), which is pointwise `≲ ε_{m-1}^{2δ} ψ_m |∇T|`
(`sd_flux_bound`); integrating in time (`sd_time_transfer`) and using `ψ_m² ≤ K κ_m κ_{m-1}`
together with `TGradientContract` gives the source right side `C ε_{m-1}^δ √κ_m B`.  The jet
hypotheses `TPositiveJetsContract`, `FirstOrderGradJetContract` of the earlier (ergodic) proof are
no longer needed. -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff ENNReal

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration
  AVenhance.Infra.Section5.RelativeError AVenhance.Infra.Ergodic

theorem twistie5CenteredSource_contract (β C₀ A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ C₁ : ℝ, OnA7Instances β C₀ C₁ (fun I _Φ hΦ κ M _R _θ₀ m _θprev T =>
      ∀ B : ℝ, 0 ≤ B → TPositiveJetsContract I m T A B →
        TGradientContract β (I.kappaSeq κ M (m - 1)) T A B →
        FirstOrderGradJetContract I m (I.kappaSeq κ M (m - 1)) T A B →
        Twistie5CenteredSourceContract I hΦ m (I.kappaSeq κ M m) T C B) := by
  by_cases hb : 1 < β ∧ β < 4 / 3
  swap
  · exact ⟨0, le_rfl, 0, fun I => absurd ⟨I.one_lt_beta, I.beta_lt⟩ hb⟩
  obtain ⟨hβ, hβ'⟩ := hb
  obtain ⟨K, hK1, hK⟩ := LeftToShow.left_to_show_scales β C₀
  obtain ⟨cfl, hcfl0, hfl⟩ := sd_flux_bound (β := β)
  refine ⟨2 * cfl * Real.sqrt K * A, by positivity, 0, ?_⟩
  intro I hz hx hh _hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ _ _ _ _ m hm hmM θprev T hθprev hT B hB
    _hJets hTG _hHess
  obtain ⟨hm2, hκm⟩ := onA7_basic I hperm hR hm
  obtain ⟨-, hmono, -, h4, -, -, -⟩ := hK I hz hx hh κ hκ M hM hperm m hm2 hmM
  have hκp : 0 < I.kappaSeq κ M (m - 1) := hκm.trans_le hmono
  have hψ0 : 0 ≤ a β I.Λ m * epsilon β I.Λ m ^ 2 :=
    mul_nonneg (a_nonneg' I m) (sq_nonneg _)
  have hψκ : (a β I.Λ m * epsilon β I.Λ m ^ 2) ^ 2 ≤
      K * I.kappaSeq κ M m * I.kappaSeq κ M (m - 1) := by
    have h4' := (div_le_iff₀ hκm).1 h4
    calc (a β I.Λ m * epsilon β I.Λ m ^ 2) ^ 2
        = a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 := by ring
      _ ≤ K * I.kappaSeq κ M (m - 1) * I.kappaSeq κ M m := h4'
      _ = _ := by ring
  have hx0 : 0 < epsilon β I.Λ (m - 1) := epsilon_pos' I (m - 1)
  have hx1 : epsilon β I.Λ (m - 1) ≤ 1 := epsilon_le_one' I (m - 1)
  have hδ := Infra.Ingredients.delta_pos hβ hβ'
  have hed : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ epsilon β I.Λ (m - 1) ^ delta β :=
    Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)
  have he0 : 0 ≤ epsilon β I.Λ (m - 1) ^ (2 * delta β) := (Real.rpow_pos_of_pos hx0 _).le
  have hTs : ∀ t : ℝ, 0 ≤ t → ContDiff ℝ (⊤ : ℕ∞) (T (Nstar β) t) := fun t ht =>
    Infra.Section4.tIterate_space_contDiff I hΦ hT hθprev le_rfl ht
  have hTp : ∀ t : ℝ, 0 ≤ t → IsZ2Periodic (T (Nstar β) t) := fun t ht =>
    Infra.Section4.tIterate_periodic I hΦ hT hθprev le_rfl ht
  have hTjoint := Infra.Section4.tIterate_contDiffOn_nonneg I hΦ hT hθprev (i := Nstar β) le_rfl
  set cf : ℝ := cfl * (epsilon β I.Λ (m - 1) ^ (2 * delta β) *
    (a β I.Λ m * epsilon β I.Λ m ^ 2)) with hcf
  have hcf0 : 0 ≤ cf := by positivity
  let V : Fin 3 → ℝ → Vec 2 → Vec 2 := fun _ t x => spaceGrad (T (Nstar β) t) x
  have hVj : ∀ (j : Fin 3) (i : Fin 2), ContinuousOn (fun p : ℝ × Vec 2 => V j p.1 p.2 i)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := fun _ i => sa_gradT_cont hTjoint i
  have hVc : ∀ (j : Fin 3) (t : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 → Continuous (V j t) := by
    intro j t ht
    refine continuous_pi fun i => ?_
    exact (hVj j i).comp_continuous (Continuous.prodMk continuous_const continuous_id)
      (fun x => ⟨⟨ht.1.le, ht.2.le⟩, Set.mem_univ x⟩)
  have htime := sd_time_transfer (f := fun t x => Integration.centerCell
    (twistie5 I hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t) x) (V := V)
    (P := ![cf, 0, 0]) (P₂ := 0)
    (by intro j; fin_cases j <;> simp [hcf0]) le_rfl hVj (by
      intro t ht
      have hTt := hTs t ht.1.le
      have key := sd_tw5_time_bound I hΦ (by omega : 1 ≤ m) (I.kappaSeq κ M m)
        (T (Nstar β)) hTt (hTp t ht.1.le) (cf := cf) (V₀ := V 0 t) (hVc 0 t ht)
        (fun x => (hfl I hΦ hm2 hκm (T (Nstar β)) hTt x).2)
      simpa [Fin.sum_univ_three, abs_of_nonneg hcf0] using key)
  refine htime.trans (ENNReal.ofReal_le_ofReal ?_)
  have hD0 : 0 ≤ Real.sqrt (spaceTimeGradNormSq (V 0)) := Real.sqrt_nonneg _
  have hψle : a β I.Λ m * epsilon β I.Λ m ^ 2 ≤
      Real.sqrt K * Real.sqrt (I.kappaSeq κ M m) * Real.sqrt (I.kappaSeq κ M (m - 1)) := by
    rw [← Real.sqrt_mul (by linarith), ← Real.sqrt_mul (by positivity)]
    exact (le_abs_self _).trans (Real.abs_le_sqrt hψκ)
  have hTG' : Real.sqrt (I.kappaSeq κ M (m - 1)) * Real.sqrt (spaceTimeGradNormSq (V 0)) ≤
      A * B := hTG
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, zero_mul, add_zero]
  calc 2 * (cf * Real.sqrt (spaceTimeGradNormSq (V 0)))
      ≤ 2 * (cfl * (epsilon β I.Λ (m - 1) ^ (2 * delta β) *
          (Real.sqrt K * Real.sqrt (I.kappaSeq κ M m) *
            Real.sqrt (I.kappaSeq κ M (m - 1))))) * Real.sqrt (spaceTimeGradNormSq (V 0)) := by
        rw [hcf, ← mul_assoc]
        gcongr
    _ = 2 * cfl * epsilon β I.Λ (m - 1) ^ (2 * delta β) * Real.sqrt K *
          Real.sqrt (I.kappaSeq κ M m) *
          (Real.sqrt (I.kappaSeq κ M (m - 1)) * Real.sqrt (spaceTimeGradNormSq (V 0))) := by
        ring
    _ ≤ 2 * cfl * epsilon β I.Λ (m - 1) ^ (2 * delta β) * Real.sqrt K *
          Real.sqrt (I.kappaSeq κ M m) * (A * B) := by gcongr
    _ ≤ 2 * cfl * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt K *
          Real.sqrt (I.kappaSeq κ M m) * (A * B) := by gcongr
    _ = _ := by ring

end AVenhance.Infra.Section5.Contracts
end
