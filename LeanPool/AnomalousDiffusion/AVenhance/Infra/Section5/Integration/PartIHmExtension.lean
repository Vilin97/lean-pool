/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIHmExtensionAmnr
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Energy.AnsatzRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Energy.Regularity

/-! # Part I: continuous extension of the actual `HTilde_m` and of `∇(ansatz)` to `t ≥ 0`

The actual `HTilde_m` (built from the two-sided `Amnr` recursion) is jointly `C^∞` on the open half
space.  Its one-sided version `Hhat`, built from `amnrWithin`, is jointly `C^∞` on the closed half
space and equals `HTilde_m` at every positive time.  Consequently `∇ θTilde_m` has a continuous
    extension
to `[0,∞) × ℝ²`.  Nothing is assumed about `Amnr`, `Hm` or the ansatz at `t ≤ 0`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.Integration

open AVenhance AVenhance.Infra.Section4

/-- **`HTilde_m` extends to a jointly `C^∞` function on `[0,∞) × ℝ²`.** -/
theorem Hm_extends_Ici {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) :
    ∃ Hhat : ℝ × Vec 2 → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) Hhat (Set.Ici (0 : ℝ) ×ˢ Set.univ) ∧
      ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)),
        I.Hm hΦ m κm (T (Nstar β)) p.1 p.2 = Hhat p := by
  have hbInf : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => streamVel (Φ (m - 1)) z.1 z.2) :=
    contDiff_infty.mpr (fun N => amnr_previous_velocity_contDiff I hΦ hm N)
  have hTg : ∀ p : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞) (amnrTGradient (T (Nstar β)) p)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := fun p =>
    Section5.RelativeError.contDiffOn_spaceGrad_slice
      (F := T (Nstar β)) (tIterate_contDiffOn_nonneg I hΦ hT hθprev le_rfl) p
  let V : ℕ → Fin 2 → ℝ → Vec 2 → ℝ := fun r i t y =>
    ∑ n ∈ Finset.range (Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
      amnrWithin I hΦ m κm n (T (Nstar β)) r t y i j k * I.qMNR κm m n (r + 1) t j k
  have hV : ∀ r i, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × Vec 2 => V r i z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    intro r i
    refine ContDiffOn.sum fun n _ => ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ => ?_
    have hq : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => I.qMNR κm m n (r + 1) t j k) :=
      contDiff_pi.mp (contDiff_pi.mp (residual_qMNR_contDiff I κm m n (r + 1)) j) k
    exact (amnrWithin_contDiffOn I hΦ hm κm n (T (Nstar β)) j k hbInf
      (fun i p => amnrSeedMultiplier_contDiff_top I hΦ hm hκm n j k i p) hTg r i).mul
      (hq.comp contDiff_fst).contDiffOn
  refine ⟨fun z => ∑ r ∈ Finset.range (Jcut β), ∑ i : Fin 2, spaceGrad (V r i z.1) z.2 i,
    ContDiffOn.sum fun r _ => ContDiffOn.sum fun i _ =>
      Section5.RelativeError.contDiffOn_spaceGrad_slice (F := V r i) (hV r i) i, ?_⟩
  rintro ⟨t, x⟩ ⟨ht, -⟩
  change ∑ r ∈ Finset.range (Jcut β), I.Hmr hΦ m κm (T (Nstar β)) r t x = _
  refine Finset.sum_congr rfl fun r _ => ?_
  unfold Ingredients.Hmr vecDiv
  refine Finset.sum_congr rfl fun i _ => ?_
  have hfun : (fun y => ∑ n ∈ Finset.range (Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
        I.Amnr hΦ m κm n (T (Nstar β)) r t y i j k * I.qMNR κm m n (r + 1) t j k) =
      V r i t := by
    funext y
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    rw [amnrWithin_eq_Amnr I hΦ m κm n (T (Nstar β)) r t ht y i j k]
  rw [hfun]

/-- **`∇(θTilde_m)` extends continuously to `[0,∞) × ℝ²`.** -/
theorem ansatz_spaceGrad_extends_Ici {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} (hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) :
    ∃ G : ℝ × Vec 2 → Vec 2, ContinuousOn G (Set.Ici (0 : ℝ) ×ˢ Set.univ) ∧
      ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)),
        spaceGrad (I.ansatz hΦ m κm (T (Nstar β)) p.1) p.2 = G p := by
  obtain ⟨Hhat, hHhat, hHeq⟩ := Hm_extends_Ici I hΦ hm hκm hθprev hT
  have hT0 := tIterate_contDiffOn_nonneg I hΦ hT hθprev (i := Nstar β) le_rfl
  let A : ℝ → Vec 2 → ℝ := fun t y =>
    T (Nstar β) t y + (∑' k : ℤ, ansatzSummand I hΦ m κm (T (Nstar β)) k t y) + Hhat (t, y)
  have hA : ContDiffOn ℝ 2 (Function.uncurry A) (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    (hT0.of_le (by simp)).add (ansatz_series_contDiffOn_two I hΦ m κm hT0) |>.add
      (hHhat.of_le (by simp))
  refine ⟨fun p => spaceGrad (A p.1) p.2,
    Energy.spaceGrad_continuousOn_one (hA.of_le (by norm_num)), ?_⟩
  rintro ⟨t, x⟩ ⟨ht, -⟩
  have hfun : I.ansatz hΦ m κm (T (Nstar β)) t = A t := by
    funext y
    rw [ansatz_eq_summand, hHeq (t, y) ⟨ht, trivial⟩]
  change spaceGrad (I.ansatz hΦ m κm (T (Nstar β)) t) x = spaceGrad (A t) x
  rw [hfun]

end AVenhance.Infra.Section5.Integration
