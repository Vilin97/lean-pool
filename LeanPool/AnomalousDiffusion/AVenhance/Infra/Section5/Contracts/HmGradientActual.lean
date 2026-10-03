/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ATensorHm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectGradientUniform

/-! # `κ_{m-1}`-normalised `HTilde_m` gradient from the AMNR tensor bound (actual iterates)

`hm_gradient_sharp_actual` is the `relative_initial_Hm_gradient_sharp` (`κ_{m-1}`
normalisation, `e.Hm.gradient.L2`) for the actual last iterate `T N*`, with the differentiability
and measurability premises discharged on the open half space exactly as in
`relative_Hm_gradient_actual` (which gives the weaker `κ_m` normalisation).  The only analytic
input is the AMNR tensor bound. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization
open scoped Matrix.Norms.Elementwise ContDiff

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section4 AVenhance.Infra.Section5.LeftToShow
  AVenhance.Infra.Section5.RelativeError

/-- The sharp (`κ_{m-1}`-normalised) open-time `HTilde_m` gradient bound for the actual iterates. -/
theorem hm_gradient_sharp_actual (β C₀ CA : ℝ) (hCA : 0 ≤ CA) :
    ∃ CH : ℝ, 0 ≤ CH ∧ ∃ Λ₀ : ℝ, ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ →
      Λ₀ ≤ (I.Λ : ℝ) →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, ∀ hΦ : IsStreamSeq I Φ,
      ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ → ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
      ∀ m : ℕ, 2 ≤ m → m ≤ M →
      ∀ (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ) (T : ℕ → ℝ → Vec 2 → ℝ),
        IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaSeq κ M (m - 1)) (fun _ _ => 0) θ₀ θprev →
        I.IsTIterates hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) θ₀ θprev T →
      ∀ S : ℝ, 0 ≤ S →
        (∀ r₀ ∈ Finset.range (Jcut β), ∀ n ∈ Finset.range (Nstar β),
          eLpNorm (amnrSpatialDivergenceGradientTensor I hΦ m (I.kappaSeq κ M m)
              (T (Nstar β)) n r₀) 2 (volume.restrict timeCube) ≤
            ENNReal.ofReal (CA * S * (epsilon β I.Λ m ^ 2 / I.kappaSeq κ M m) /
              Real.sqrt (I.kappaSeq κ M (m - 1)) *
              (epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2))) ^ 2 *
                ((tauP β I.Λ m)⁻¹) ^ r₀)) →
        Real.sqrt (I.kappaSeq κ M (m - 1)) * Real.sqrt (spaceTimeGradNormSq (fun s x =>
            spaceGrad (I.Hm hΦ m (I.kappaSeq κ M m) (T (Nstar β)) s) x)) ≤
          CH * epsilon β I.Λ (m - 1) ^ (4 * delta β) * S := by
  obtain ⟨CH, hCH, Λ₀, h⟩ := relative_initial_Hm_gradient_sharp β C₀ CA hCA
  obtain ⟨K, -, hK⟩ := left_to_show_scales β C₀
  refine ⟨CH, hCH, Λ₀, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκp M hM hperm m hm hmM θ₀ θprev T hθprev hT S hS hAmnr
  obtain ⟨hκm, -⟩ := hK I hz hx hh κ hκp M hM hperm m hm hmM
  have hm1 : 1 ≤ m := by omega
  have hAJ := fun n r i j k =>
    Integration.amnr_contDiffOn_Ioi_top I hΦ hm1 hκm hθprev hT n r i j k
  have hHJ := fun r => Integration.Hmr_contDiffOn_Ioi_top I hΦ hm1 hκm hθprev hT r
  refine h I hz hx hh hΛ Φ hΦ κ hκp M hM hperm m hm hmM (T (Nstar β)) S hS ?_ ?_ ?_ ?_ ?_ hAmnr
  · intro r _ n _
    exact amnr_hm_hessian_entry_measurable_of_contDiff I hΦ m (I.kappaSeq κ M m)
      (T (Nstar β)) n r (fun i j k => (hAJ n r i j k).of_le (by simp))
  · intro r _
    refine aestronglyMeasurable_timeCube_of_contDiffOn_Ioi (continuousOn_pi.mpr fun j => ?_)
    exact (Integration.contDiffOn_spaceGrad_slice_Ioi (hHJ r) j).continuousOn
  · intro r _ n _ i j k t ht x
    exact differentiableAt_slice_of_contDiffOn_Ioi
      (F := fun t y => I.Amnr hΦ m (I.kappaSeq κ M m) n (T (Nstar β)) r t y i j k)
      (hAJ n r i j k) ht x
  · intro r _ n _ i j k t ht x
    exact differentiableAt_slice_of_contDiffOn_Ioi
      (F := fun t y => spaceGrad
        (fun x => I.Amnr hΦ m (I.kappaSeq κ M m) n (T (Nstar β)) r t x i j k) y i)
      (Integration.contDiffOn_spaceGrad_slice_Ioi
        (F := fun t y => I.Amnr hΦ m (I.kappaSeq κ M m) n (T (Nstar β)) r t y i j k)
        (hAJ n r i j k) i) ht x
  · intro r _ t ht x
    exact differentiableAt_slice_of_contDiffOn_Ioi
      (F := fun t y => I.Hmr hΦ m (I.kappaSeq κ M m) (T (Nstar β)) r t y) (hHJ r) ht x

end AVenhance.Infra.Section5.Contracts
