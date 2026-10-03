/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ATensorHmEngine
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIHmRegularityHm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.HmAdapter

/-! # the open-time `HTilde_m` gradient from the AMNR tensor bound (actual iterates)

`relative_Hm_gradient_actual` is `relative_Hm_gradient` for the actual last iterate `T N*` of an
`IsTIterates` family.  The only analytic input is the AMNR tensor bound; all differentiability
and measurability facts are proved from the joint `C^∞` regularity of `Amnr` and `HTilde_{m,r}` on
the open half space `(0,∞) × ℝ²`, so nothing is assumed at `t ≤ 0`. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization
open scoped Matrix.Norms.Elementwise ContDiff

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance AVenhance.Infra.Section4 AVenhance.Infra.Section5.LeftToShow

/-- A function jointly `C^∞` on the open half space is differentiable in space at each
positive time. -/
theorem differentiableAt_slice_of_contDiffOn_Ioi {F : ℝ → Vec 2 → ℝ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => F p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ))
    {t : ℝ} (ht : 0 < t) (x : Vec 2) : DifferentiableAt ℝ (F t) x := by
  have hU : IsOpen (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) :=
    isOpen_Ioi.prod isOpen_univ
  have hJ : DifferentiableAt ℝ (fun p : ℝ × Vec 2 => F p.1 p.2) (t, x) :=
    (hF.contDiffAt (hU.mem_nhds (show (t, x) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)) from
      ⟨ht, trivial⟩))).differentiableAt (by simp)
  exact hJ.comp x ((differentiableAt_const t).prodMk differentiableAt_id)

/-- A function jointly `C^∞` on the open half space is a.e.-strongly measurable on the time
cube. -/
theorem aestronglyMeasurable_timeCube_of_contDiffOn_Ioi {G : ℝ × Vec 2 → Vec 2}
    (hG : ContinuousOn G (Set.Ioi (0 : ℝ) ×ˢ Set.univ)) :
    AEStronglyMeasurable G (volume.restrict timeCube) :=
  (hG.mono (fun _ hz => ⟨hz.1.1, Set.mem_univ _⟩)).aestronglyMeasurable
    (μ := volume) amnr_timeCube_isOpen.measurableSet

/-- **Open-time `HTilde_m` gradient bound for the actual iterates** (16)-(18).  The AMNR
tensor bound is the only analytic input; all regularity and measurability premises of
`relative_Hm_gradient` are discharged on the open half space. -/
theorem relative_Hm_gradient_actual (β C₀ CA : ℝ) (hCA : 0 ≤ CA) :
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
        Real.sqrt (I.kappaSeq κ M m) * Real.sqrt (spaceTimeGradNormSq (fun s x =>
            spaceGrad (I.Hm hΦ m (I.kappaSeq κ M m) (T (Nstar β)) s) x)) ≤
          CH * epsilon β I.Λ (m - 1) ^ (4 * delta β) * S := by
  obtain ⟨CH, hCH, Λ₀, h⟩ := relative_Hm_gradient_Ioi β C₀ CA hCA
  obtain ⟨K, -, hK⟩ := left_to_show_scales β C₀
  refine ⟨CH, hCH, Λ₀, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκp M hM hperm m hm hmM θ₀ θprev T hθprev hT S hS hAmnr
  obtain ⟨hκm, -⟩ := hK I hz hx hh κ hκp M hM hperm m hm hmM
  have hm1 : 1 ≤ m := by omega
  -- joint `C^∞` regularity on the open half space
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

end AVenhance.Infra.Section5.RelativeError
