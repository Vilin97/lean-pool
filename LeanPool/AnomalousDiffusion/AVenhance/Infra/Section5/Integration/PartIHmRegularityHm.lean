/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIHmRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.Hm

/-! # Part I: `HTilde_m` is jointly `C^∞` on the open half space

`HTilde_{m,r} = ∇ · ∑ 𝐀_{m,n,r} 𝐪_{m,n,r+1}` and `HTilde_m = ∑_{r < Jcut} HTilde_{m,r}`.  On the
    open set
`(0,∞) × ℝ²` the spatial gradient of a jointly `C^∞` function is jointly `C^∞`, so `HTilde_m` is
jointly `C^∞` there and every positive-time slice is `C^∞`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.Integration

open AVenhance AVenhance.Infra.Section4

/-- On the open half space the spatial gradient components of a jointly `C^∞` function are
jointly `C^∞`. -/
theorem contDiffOn_spaceGrad_slice_Ioi {F : ℝ → Vec 2 → ℝ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => F p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ)) (j : Fin 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => spaceGrad (F p.1) p.2 j)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  set s : Set (ℝ × Vec 2) := Set.Ioi (0 : ℝ) ×ˢ Set.univ with hs
  have hso : IsOpen s := isOpen_Ioi.prod isOpen_univ
  have hsu : UniqueDiffOn ℝ s := hso.uniqueDiffOn
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 =>
        fderivWithin ℝ (fun q : ℝ × Vec 2 => F q.1 q.2) s p (0, basisVec j)) s :=
    (hF.fderivWithin hsu (by simp)).clm_apply contDiffOn_const
  refine h1.congr ?_
  rintro ⟨t, x⟩ ⟨ht, -⟩
  exact Section5.RelativeError.spaceGrad_slice_eq_fderivWithin
    (F := fun q : ℝ × Vec 2 => F q.1 q.2) (s := s) t x
    (fun y => ⟨ht, trivial⟩) (hF.differentiableOn (by simp) (t, x) ⟨ht, trivial⟩) j

/-- Each `HTilde_{m,r}` is jointly `C^∞` on the open half space. -/
theorem Hmr_contDiffOn_Ioi_top {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) (r : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × Vec 2 => I.Hmr hΦ m κm (T (Nstar β)) r z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  have hG : ∀ i : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ℝ × Vec 2 => ∑ n ∈ Finset.range (Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
        I.Amnr hΦ m κm n (T (Nstar β)) r z.1 z.2 i j k * I.qMNR κm m n (r + 1) z.1 j k)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
    intro i
    refine ContDiffOn.sum fun n _ => ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ => ?_
    have hq : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => I.qMNR κm m n (r + 1) t j k) :=
      contDiff_pi.mp (contDiff_pi.mp (residual_qMNR_contDiff I κm m n (r + 1)) j) k
    exact (amnr_contDiffOn_Ioi_top I hΦ hm hκm hθprev hT n r i j k).mul
      (hq.comp contDiff_fst).contDiffOn
  unfold Ingredients.Hmr vecDiv
  exact ContDiffOn.sum fun i _ =>
    contDiffOn_spaceGrad_slice_Ioi
      (F := fun t y => ∑ n ∈ Finset.range (Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
        I.Amnr hΦ m κm n (T (Nstar β)) r t y i j k * I.qMNR κm m n (r + 1) t j k) (hG i) i

/-- **`HTilde_m` is jointly `C^∞` on the open half space `(0,∞) × ℝ²`.** -/
theorem Hm_contDiffOn_Ioi_top {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × Vec 2 => I.Hm hΦ m κm (T (Nstar β)) z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  unfold Ingredients.Hm
  exact ContDiffOn.sum fun r _ => Hmr_contDiffOn_Ioi_top I hΦ hm hκm hθprev hT r

/-- Every positive-time slice of `HTilde_m` is `C^∞` in space. -/
theorem Hm_slice_contDiff_pos {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ (⊤ : ℕ∞) (I.Hm hΦ m κm (T (Nstar β)) t) := by
  have h : ContDiffOn ℝ (⊤ : ℕ∞)
      ((fun z : ℝ × Vec 2 => I.Hm hΦ m κm (T (Nstar β)) z.1 z.2) ∘
        (fun y : Vec 2 => (t, y))) Set.univ :=
    (Hm_contDiffOn_Ioi_top I hΦ hm hκm hθprev hT).comp
      (contDiff_prodMk_right t).contDiffOn (fun y _ => ⟨ht, trivial⟩)
  exact contDiffOn_univ.mp h

end AVenhance.Infra.Section5.Integration
