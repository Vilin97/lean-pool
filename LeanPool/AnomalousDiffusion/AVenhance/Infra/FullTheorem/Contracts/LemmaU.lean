/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.LemmaUContract
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.LemmaU.Assembly

/-!
# Lemma U (uniform time-Hölder bound in `L²`), proved

`lemmaU_contract` discharges `LemmaUContract`: for a bounded, measurable, periodic,
divergence-free drift and `0 < κ ≤ 1`, every weak solution with `H¹` datum satisfies
`‖θ(t) − θ(s)‖ ≤ 40 (1 + B) κ^{-1/2} |t − s|^{1/4} ‖θ₀‖_{H¹}`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization

namespace AVenhance.Infra.FullTheorem.Contracts

open AVenhance AVenhance.Infra.FullTheorem AVenhance.Infra.FullTheorem.LemmaU

theorem lemmaU_contract : AVenhance.Infra.FullTheorem.LemmaUContract := by
  refine ⟨40, by norm_num, ?_⟩
  intro b hb_meas hb_per hdiv B hB0 hB κ hκ hκ1 θ₀ Dθ₀ hθ₀ θ D hu s hs t ht
  have hsqrt : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hmono : ∀ h : ℝ, 0 ≤ h → ∀ S : ℝ, 0 ≤ S →
      20 * (1 + 2 * B) / Real.sqrt κ * h ^ ((1 : ℝ) / 4) * S ≤
        40 * (1 + B) / Real.sqrt κ * h ^ ((1 : ℝ) / 4) * S := by
    intro h hh S hS
    have : 20 * (1 + 2 * B) ≤ 40 * (1 + B) := by linarith
    gcongr
  rcases le_total s t with hst | hts
  · have hcore := lemmaU_core hκ hκ1 hB0 hb_meas hb_per hdiv hB hθ₀ hu hs ht hst
    rw [abs_of_nonneg (sub_nonneg.mpr hst)]
    exact hcore.trans (hmono _ (sub_nonneg.mpr hst) _ (Real.sqrt_nonneg _))
  · have hcore := lemmaU_core hκ hκ1 hB0 hb_meas hb_per hdiv hB hθ₀ hu ht hs hts
    have hsymm : l2NormSq (fun x => θ t x - θ s x) = l2NormSq (fun x => θ s x - θ t x) := by
      unfold l2NormSq
      congr 1
      funext x
      ring
    rw [hsymm, abs_of_nonpos (sub_nonpos.mpr hts), neg_sub]
    exact hcore.trans (hmono _ (sub_nonneg.mpr hts) _ (Real.sqrt_nonneg _))

end AVenhance.Infra.FullTheorem.Contracts

end
