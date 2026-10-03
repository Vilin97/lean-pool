/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIHmRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.Hm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowSpatialPeriodicity

/-! # Part I: spatial periodicity of `Amnr` and `HTilde_m` for positive times

`Amnr` is built from `ℤ²`-periodic pieces (`∇T`, the pulled-back flow gradient, the previous
velocity and its gradient).  Time derivatives only see a neighbourhood of `t`, so periodicity at
`t > 0` follows from periodicity at all nearby (positive) times.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Homogenization

namespace AVenhance.Infra.Section5.Integration

open AVenhance AVenhance.Infra.Section4

/-- The previous velocity is `ℤ²`-periodic in space at every time. -/
theorem streamVel_prev_isZ2Periodic {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (t : ℝ) :
    IsZ2Periodic (streamVel (Φ (m - 1)) t) := by
  intro n x
  have hb := AVenhance.Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m)
  simpa using hb.periodic 0 n t x

/-- `Amnr` is `ℤ²`-periodic in space at positive times, given a spatially periodic `T`
at nonnegative times. -/
theorem Amnr_isZ2Periodic_pos {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (n : ℕ) {Tm1 : ℝ → Vec 2 → ℝ}
    (hTper : ∀ t : ℝ, 0 ≤ t → IsZ2Periodic (Tm1 t)) (r : ℕ) :
    ∀ t : ℝ, 0 < t → ∀ i j k : Fin 2,
      IsZ2Periodic (fun x => I.Amnr hΦ m κm n Tm1 r t x i j k) := by
  induction r with
  | zero =>
    intro t ht i j k s x
    have hp : ∀ l a b, I.flowGrad hΦ m l t (x + latticeShift s) a b =
        I.flowGrad hΦ m l t x a b := fun l a b =>
      amnr_flowGrad_spatial_periodic I hΦ m l t a b s x
    have hg : ∀ p, spaceGrad (Tm1 t) (x + latticeShift s) p = spaceGrad (Tm1 t) x p :=
      fun p => congrFun (Section5.RelativeError.spaceGrad_isZ2Periodic (hTper t ht.le) s x) p
    simp only [Ingredients.Amnr, hp, hg]
  | succ r ih =>
    intro t ht i j k s x
    have hderiv : deriv (fun s' => I.Amnr hΦ m κm n Tm1 r s' (x + latticeShift s) i j k) t =
        deriv (fun s' => I.Amnr hΦ m κm n Tm1 r s' x i j k) t := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [Ioi_mem_nhds ht] with s' hs'
      exact ih s' hs' i j k s x
    have hv : streamVel (Φ (m - 1)) t (x + latticeShift s) = streamVel (Φ (m - 1)) t x :=
      streamVel_prev_isZ2Periodic hΦ m t s x
    have hsg : spaceGrad (fun y => I.Amnr hΦ m κm n Tm1 r t y i j k) (x + latticeShift s) =
        spaceGrad (fun y => I.Amnr hΦ m κm n Tm1 r t y i j k) x :=
      Section5.RelativeError.spaceGrad_isZ2Periodic (ih t ht i j k) s x
    have hgv : ∀ ℓ, spaceGrad (fun y => streamVel (Φ (m - 1)) t y i) (x + latticeShift s) ℓ =
        spaceGrad (fun y => streamVel (Φ (m - 1)) t y i) x ℓ := fun ℓ =>
      congrFun (Section5.RelativeError.spaceGrad_isZ2Periodic
        (fun s' y => congrFun (streamVel_prev_isZ2Periodic hΦ m t s' y) i) s x) ℓ
    have hA : ∀ ℓ, I.Amnr hΦ m κm n Tm1 r t (x + latticeShift s) ℓ j k =
        I.Amnr hΦ m κm n Tm1 r t x ℓ j k := fun ℓ => ih t ht ℓ j k s x
    simp only [Ingredients.Amnr, hderiv, hv, hsg, hgv, hA]

/-- Each `HTilde_{m,r}` is `ℤ²`-periodic at positive times. -/
theorem Hmr_isZ2Periodic_pos {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) {Tm1 : ℝ → Vec 2 → ℝ}
    (hTper : ∀ t : ℝ, 0 ≤ t → IsZ2Periodic (Tm1 t)) (r : ℕ) {t : ℝ} (ht : 0 < t) :
    IsZ2Periodic (I.Hmr hΦ m κm Tm1 r t) := by
  intro s x
  unfold Ingredients.Hmr vecDiv
  refine Finset.sum_congr rfl fun i _ => ?_
  have hV : IsZ2Periodic (fun y => ∑ n ∈ Finset.range (Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
      I.Amnr hΦ m κm n Tm1 r t y i j k * I.qMNR κm m n (r + 1) t j k) := by
    intro s' y
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    exact congrArg (· * I.qMNR κm m n (r + 1) t j k)
      (Amnr_isZ2Periodic_pos I hΦ m κm n hTper r t ht i j k s' y)
  exact congrFun (Section5.RelativeError.spaceGrad_isZ2Periodic hV s x) i

/-- **`HTilde_m` is `ℤ²`-periodic in space at every positive time.** -/
theorem Hm_periodic_pos {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (_hm : 1 ≤ m) {κm κprev : ℝ} (_hκm : 0 < κm)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) {t : ℝ} (ht : 0 < t) :
    IsZ2Periodic (I.Hm hΦ m κm (T (Nstar β)) t) := by
  have hTper := (terminalT_contDiffOn_nonneg_and_periodic I hΦ hT hθprev).2
  intro s x
  unfold Ingredients.Hm
  exact Finset.sum_congr rfl fun r _ => Hmr_isZ2Periodic_pos I hΦ m κm hTper r ht s x

end AVenhance.Infra.Section5.Integration
