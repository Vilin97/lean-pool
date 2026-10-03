/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.AnsatzProduct
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.LocalFinite

/-! Local-finiteness and time differentiation for the ansatz cutoff sum. -/

@[expose] public section

noncomputable section

open Homogenization Filter
open scoped Topology

namespace AVenhance.Infra.Section5

open AVenhance

variable {β : ℝ} (I : Ingredients β)
variable {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The indices whose cutoff may be nonzero in a fixed time neighborhood. -/
def xiMKNearSupport (m : ℕ) (t ρ : ℝ) : Set ℤ :=
  {k | ∃ s ∈ Set.Ioo (t - ρ) (t + ρ), I.xiMK m k s ≠ 0}

theorem FrozenAnsatzTime.xiMK_nonzero_time_bound (m : ℕ) (k : ℤ) {s : ℝ}
    (hne : I.xiMK m k s ≠ 0) :
    |s - (k : ℝ) * tau β I.Λ m| ≤ 5 / 4 * tau β I.Λ m := by
  have hτ := I.tau_pos' m
  let u := (s - k * tau β I.Λ m) / tau β I.Λ m
  have hu : u ∈ Set.Icc (-(5 / 4 : ℝ)) (5 / 4) := by
    by_contra hnot
    apply hne
    have h1 := I.xi_le_ind u
    have h2 := I.ind_le_xi u
    rw [indIcc_eq_zero_of_not_mem hnot] at h1
    have h3 := indIcc_nonneg' (-(3 / 4)) (3 / 4) u
    exact le_antisymm h1 (h3.trans h2)
  have hratio : |u| ≤ 5 / 4 := abs_le.mpr ⟨hu.1, hu.2⟩
  have hscaled : |s - (k : ℝ) * tau β I.Λ m| / tau β I.Λ m ≤
      5 / 4 := by
    simpa [u, abs_div, abs_of_pos hτ] using hratio
  rw [div_le_iff₀ hτ] at hscaled
  exact hscaled

/-- The cutoff family is uniformly finite on each bounded time neighborhood. -/
theorem xiMKNearSupport_finite (m : ℕ) (t ρ : ℝ) :
    (xiMKNearSupport I m t ρ).Finite := by
  have hτ := Ingredients.tau_pos' I m
  refine finite_lattice_near hτ t (ρ + 5 / 4 * tau β I.Λ m) |>.subset ?_
  intro k hk
  rcases hk with ⟨s, hs, hne⟩
  have hsBound := FrozenAnsatzTime.xiMK_nonzero_time_bound I m k hne
  have htBound : |t - s| ≤ ρ := by
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2]
  calc
    |t - (k : ℝ) * tau β I.Λ m| = |(t - s) + (s - (k : ℝ) * tau β I.Λ m)| := by
      congr 1; ring
    _ ≤ |t - s| + |s - (k : ℝ) * tau β I.Λ m| := abs_add_le _ _
    _ ≤ ρ + 5 / 4 * tau β I.Λ m := add_le_add htBound hsBound

/-- Finite index set controlling the cutoff series near `t`. -/
noncomputable def xiMKNearSupportFinset (m : ℕ) (t ρ : ℝ) : Finset ℤ :=
  (xiMKNearSupport_finite I m t ρ).toFinset

theorem FrozenAnsatzTime.xiMK_eq_zero_outside_nearSupport (m : ℕ) (t ρ s : ℝ)
    (hs : s ∈ Set.Ioo (t - ρ) (t + ρ)) {k : ℤ}
    (hk : k ∉ xiMKNearSupportFinset I m t ρ) : I.xiMK m k s = 0 := by
  by_contra hne
  have hmem : k ∈ xiMKNearSupport I m t ρ := ⟨s, hs, hne⟩
  exact hk ((xiMKNearSupport_finite I m t ρ).mem_toFinset.mpr hmem)

/-- The ansatz time derivative is an ordinary finite product-rule
calculation once the individual pulled fields are differentiable. The support
finset is uniform on a neighborhood of `t`, so differentiating the original
`ℤ`-indexed tsum is justified. -/
theorem ansatz_hasDerivAt
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm ρ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (t : ℝ) (x : Vec 2) (T' H' : ℝ → ℝ)
    (ξ' : ℤ → ℝ) (χ' G' : ℤ → Vec 2)
    (hρ : 0 < ρ)
    (hT : HasDerivAt (fun s => T s x) (T' t) t)
    (hH : HasDerivAt (fun s => I.Hm hΦ m κm T s x) (H' t) t)
    (hξ : ∀ k ∈ xiMKNearSupportFinset I m t ρ,
      HasDerivAt (I.xiMK m k) (ξ' k) t)
    (hχ : ∀ k ∈ xiMKNearSupportFinset I m t ρ,
      HasDerivAt (fun s => I.chiTilde hΦ m κm k s x) (χ' k) t)
    (hG : ∀ k ∈ xiMKNearSupportFinset I m t ρ,
      HasDerivAt (fun s => G I hΦ m T (lIdx β I.Λ m k) s x) (G' k) t) :
    HasDerivAt (fun s => I.ansatz hΦ m κm T s x)
      (T' t + (∑ k ∈ xiMKNearSupportFinset I m t ρ,
        (ξ' k * vecDot (I.chiTilde hΦ m κm k t x)
            (G I hΦ m T (lIdx β I.Λ m k) t x) +
          I.xiMK m k t * (vecDot (χ' k)
              (G I hΦ m T (lIdx β I.Λ m k) t x) +
            vecDot (I.chiTilde hΦ m κm k t x) (G' k)))) + H' t) t := by
  let S := xiMKNearSupportFinset I m t ρ
  let ξ : ℤ → ℝ → ℝ := fun k s => I.xiMK m k s
  let χ : ℤ → ℝ → Vec 2 := fun k s => I.chiTilde hΦ m κm k s x
  let Gc : ℤ → ℝ → Vec 2 := fun k s =>
    G I hΦ m T (lIdx β I.Λ m k) s x
  let P : ℝ → ℝ := fun s =>
    ∑ k ∈ S, ξ k s * vecDot (χ k s) (Gc k s)
  have hseries (s : ℝ) (hs : s ∈ Set.Ioo (t - ρ) (t + ρ)) :
      (∑' k : ℤ, I.xiMK m k s *
        vecDot (I.chiTilde hΦ m κm k s x)
          (G I hΦ m T (lIdx β I.Λ m k) s x)) = P s := by
    dsimp [P, ξ, χ, Gc, S]
    apply tsum_eq_sum
    intro k hk
    simp [FrozenAnsatzTime.xiMK_eq_zero_outside_nearSupport I m t ρ s hs hk]
  have hseriesAnsatz (s : ℝ) (hs : s ∈ Set.Ioo (t - ρ) (t + ρ)) :
      (∑' k : ℤ, I.xiMK m k s *
        vecDot (I.chiTilde hΦ m κm k s x)
          (spaceGrad (fun y => T s (I.xFlow hΦ m (lIdx β I.Λ m k) s y))
            (I.xFlowInv hΦ m (lIdx β I.Λ m k) s x))) = P s := by
    simpa [P, ξ, χ, Gc, G] using hseries s hs
  have hlocal :
      (fun s => I.ansatz hΦ m κm T s x) =ᶠ[𝓝 t]
        (fun s => T s x + P s + I.Hm hΦ m κm T s x) := by
    filter_upwards [isOpen_Ioo.mem_nhds
      ⟨sub_lt_self t hρ, lt_add_of_pos_right t hρ⟩] with s hs
    simp only [Ingredients.ansatz]
    rw [hseriesAnsatz s hs]
  have hfinite : HasDerivAt
      (fun s => T s x + P s + I.Hm hΦ m κm T s x)
      (T' t + (∑ k ∈ S,
        (ξ' k * vecDot (χ k t) (Gc k t) +
          I.xiMK m k t * (vecDot (χ' k) (Gc k t) +
            vecDot (χ k t) (G' k)))) + H' t) t := by
    simpa [P, ξ, χ, Gc, S] using
      hasDerivAt_finiteAnsatz S (fun s => T s x)
        (fun s => I.Hm hΦ m κm T s x) T' H'
        (fun k s => I.xiMK m k s) (fun k _ => ξ' k)
        (fun k s => I.chiTilde hΦ m κm k s x) Gc
        (fun k _ => χ' k) (fun k _ => G' k)
        hT hH (by simpa using hξ) (by simpa using hχ) (by simpa using hG)
  exact hfinite.congr_of_eventuallyEq hlocal

end AVenhance.Infra.Section5

end
