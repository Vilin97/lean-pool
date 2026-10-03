/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIHmRegularityHm

/-! # Part I: the one-sided recursion `amnrWithin` and its `C^∞` extension to `t ≥ 0`

The `Amnr` recursion differentiates in time with the two-sided `deriv`, so at `t = 0` it
depends on the arbitrary negative-time values of `T`.  `amnrWithin` is the same recursion with
`derivWithin (·) (Set.Ici 0)`.  It agrees with `Amnr` at every positive time and is jointly
`C^∞` on the closed half space `[0,∞) × ℝ²`.  Nothing is assumed about `Amnr` at `t ≤ 0`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.Integration

open AVenhance AVenhance.Infra.Section4

/-- The recursion of the `Amnr`, with the time derivative taken within `[0,∞)`. -/
def amnrWithin {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κm : ℝ) (n : ℕ) (Tm1 : ℝ → Vec 2 → ℝ) :
    ℕ → ℝ → Vec 2 → Fin 2 → Fin 2 → Fin 2 → ℝ
  | 0 => I.Amnr hΦ m κm n Tm1 0
  | r + 1 => fun t x i j k =>
      (derivWithin (fun s => amnrWithin I hΦ m κm n Tm1 r s x i j k) (Set.Ici 0) t +
        vecDot (streamVel (Φ (m - 1)) t x)
          (spaceGrad (fun y => amnrWithin I hΦ m κm n Tm1 r t y i j k) x)) -
      ∑ ℓ : Fin 2, spaceGrad (fun y => streamVel (Φ (m - 1)) t y i) x ℓ *
        amnrWithin I hΦ m κm n Tm1 r t x ℓ j k

/-- At positive times the one-sided recursion is the `Amnr`. -/
theorem amnrWithin_eq_Amnr {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (n : ℕ) (Tm1 : ℝ → Vec 2 → ℝ) (r : ℕ) :
    ∀ t : ℝ, 0 < t → ∀ (x : Vec 2) (i j k : Fin 2),
      amnrWithin I hΦ m κm n Tm1 r t x i j k = I.Amnr hΦ m κm n Tm1 r t x i j k := by
  induction r with
  | zero => intro t _ x i j k; rfl
  | succ r ih =>
    intro t ht x i j k
    have hd : derivWithin (fun s => amnrWithin I hΦ m κm n Tm1 r s x i j k) (Set.Ici 0) t =
        deriv (fun s => I.Amnr hΦ m κm n Tm1 r s x i j k) t := by
      rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht)]
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [Ioi_mem_nhds ht] with s hs using ih s hs x i j k
    have hg : (fun y => amnrWithin I hΦ m κm n Tm1 r t y i j k) =
        fun y => I.Amnr hΦ m κm n Tm1 r t y i j k :=
      funext fun y => ih t ht y i j k
    have hl : ∀ ℓ : Fin 2, amnrWithin I hΦ m κm n Tm1 r t x ℓ j k =
        I.Amnr hΦ m κm n Tm1 r t x ℓ j k := fun ℓ => ih t ht x ℓ j k
    change (derivWithin (fun s => amnrWithin I hΦ m κm n Tm1 r s x i j k) (Set.Ici 0) t +
        vecDot (streamVel (Φ (m - 1)) t x)
          (spaceGrad (fun y => amnrWithin I hΦ m κm n Tm1 r t y i j k) x)) -
      ∑ ℓ : Fin 2, spaceGrad (fun y => streamVel (Φ (m - 1)) t y i) x ℓ *
        amnrWithin I hΦ m κm n Tm1 r t x ℓ j k =
      (deriv (fun s => I.Amnr hΦ m κm n Tm1 r s x i j k) t +
        vecDot (streamVel (Φ (m - 1)) t x)
          (spaceGrad (fun y => I.Amnr hΦ m κm n Tm1 r t y i j k) x)) -
      ∑ ℓ : Fin 2, spaceGrad (fun y => streamVel (Φ (m - 1)) t y i) x ℓ *
        I.Amnr hΦ m κm n Tm1 r t x ℓ j k
    rw [hd, hg]
    simp only [hl]

/-- The time slice derivative within `[0,∞)` of a function differentiable within the closed half
space is the corresponding directional `fderivWithin`. -/
theorem derivWithin_slice_eq_fderivWithin {F : ℝ × Vec 2 → ℝ} (t : ℝ) (x : Vec 2) (ht : 0 ≤ t)
    (hF : DifferentiableWithinAt ℝ F (Set.Ici (0 : ℝ) ×ˢ Set.univ) (t, x)) :
    derivWithin (fun s => F (s, x)) (Set.Ici 0) t =
      fderivWithin ℝ F (Set.Ici (0 : ℝ) ×ˢ Set.univ) (t, x) (1, 0) := by
  have hs : HasDerivWithinAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : Vec 2)) (Set.Ici 0) t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x)).hasDerivWithinAt
  have hmaps : Set.MapsTo (fun s : ℝ => (s, x)) (Set.Ici 0)
      (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) := fun s hs => ⟨hs, trivial⟩
  have hc := hF.hasFDerivWithinAt.comp_hasDerivWithinAt t hs hmaps
  exact hc.derivWithin (uniqueDiffOn_Ici 0 t ht)

/-- **`amnrWithin` is jointly `C^∞` on `[0,∞) × ℝ²`**, given `C^∞` coefficient factors. -/
theorem amnrWithin_contDiffOn {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) (κm : ℝ) (n : ℕ) (Tm1 : ℝ → Vec 2 → ℝ)
    (j k : Fin 2)
    (hb : ContDiff ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => streamVel (Φ (m - 1)) z.1 z.2))
    (hf : ∀ i p, ContDiff ℝ (⊤ : ℕ∞) (amnrSeedMultiplier I hΦ m κm n j k i p))
    (hg : ∀ p, ContDiffOn ℝ (⊤ : ℕ∞) (amnrTGradient Tm1 p)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (r : ℕ) :
    ∀ i : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ℝ × Vec 2 => amnrWithin I hΦ m κm n Tm1 r z.1 z.2 i j k)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  have hsu : UniqueDiffOn ℝ (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) :=
    UniqueDiffOn.prod (uniqueDiffOn_Ici 0) uniqueDiffOn_univ
  induction r with
  | zero =>
    intro i
    refine (ContDiffOn.sum (s := Finset.univ) fun p _ => (hf i p).contDiffOn.mul (hg p)).congr ?_
    intro z _
    exact Amnr_zero_factors I hΦ hm κm n Tm1 z.1 z.2 i j k
  | succ r ih =>
    intro i
    have htime : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : ℝ × Vec 2 =>
          derivWithin (fun s => amnrWithin I hΦ m κm n Tm1 r s z.2 i j k) (Set.Ici 0) z.1)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
      have h1 : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun z : ℝ × Vec 2 =>
            fderivWithin ℝ (fun q : ℝ × Vec 2 => amnrWithin I hΦ m κm n Tm1 r q.1 q.2 i j k)
              (Set.Ici (0 : ℝ) ×ˢ Set.univ) z (1, 0)) (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
        ((ih i).fderivWithin hsu (by simp)).clm_apply contDiffOn_const
      refine h1.congr ?_
      rintro ⟨t, x⟩ ⟨ht, -⟩
      exact derivWithin_slice_eq_fderivWithin
        (F := fun q : ℝ × Vec 2 => amnrWithin I hΦ m κm n Tm1 r q.1 q.2 i j k) t x ht
        ((ih i).differentiableOn (by simp) (t, x) ⟨ht, trivial⟩)
    have hvel : ∀ p : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : ℝ × Vec 2 => streamVel (Φ (m - 1)) z.1 z.2 p) (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
      fun p => ((contDiff_pi.mp hb) p).contDiffOn
    have hvg : ∀ ℓ : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : ℝ × Vec 2 => spaceGrad (fun y => streamVel (Φ (m - 1)) z.1 y i) z.2 ℓ)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ) := fun ℓ =>
      (amnrVelocityGradient_contDiffOn_infty isOpen_univ hb.contDiffOn i ℓ).mono
        (Set.subset_univ _)
    exact (htime.add (ContDiffOn.sum fun p _ =>
        (hvel p).mul (Section5.RelativeError.contDiffOn_spaceGrad_slice
          (F := fun t y => amnrWithin I hΦ m κm n Tm1 r t y i j k) (ih i) p))).sub
      (ContDiffOn.sum fun ℓ _ => (hvg ℓ).mul (ih ℓ))

end AVenhance.Infra.Section5.Integration
