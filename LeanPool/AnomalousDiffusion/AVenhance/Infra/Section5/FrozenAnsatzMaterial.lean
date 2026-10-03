/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FiniteAnsatzMaterial
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FrozenAnsatzTime

/-! The finite material-derivative expansion instantiated on the
locally finite cutoff ansatz. -/

@[expose] public section

noncomputable section

open Homogenization
open Filter
open scoped Topology

namespace AVenhance.Infra.Section5

open AVenhance

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

theorem FrozenAnsatzMaterial.xiMK_eq_zero_off_nearSupport
    (m : ℕ) (t ρ s : ℝ) (hs : s ∈ Set.Ioo (t - ρ) (t + ρ))
    {k : ℤ} (hk : k ∉ xiMKNearSupportFinset I m t ρ) :
    I.xiMK m k s = 0 := by
  by_contra hne
  have hmem : k ∈ xiMKNearSupport I m t ρ := ⟨s, hs, hne⟩
  exact hk ((xiMKNearSupport_finite I m t ρ).mem_toFinset.mpr hmem)

/-- Source-level material differentiation of the line-2 ansatz. The
finite cutoff support is chosen uniformly near `t`; the hypotheses are the
pointwise time and space derivatives needed by the product rule. The source
identity `e.timecomp.0` follows by substituting its transport identities and
the separate equation for `Hm`. -/
theorem frozen_ansatz_material_expansion
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κ : ℝ)
    (T : ℝ → Vec 2 → ℝ) (ρ t : ℝ) (x b : Vec 2)
    (Tt Ht : ℝ) (ξt : ℤ → ℝ) (χt Gt : ℤ → Vec 2)
    (LT LH : Vec 2 →L[ℝ] ℝ)
    (Lχ LG : ℤ → Vec 2 →L[ℝ] Vec 2)
    (hρ : 0 < ρ)
    (hTt : HasDerivAt (fun s => T s x) Tt t)
    (hHt : HasDerivAt (fun s => I.Hm hΦ m κ T s x) Ht t)
    (hξt : ∀ k ∈ xiMKNearSupportFinset I m t ρ,
      HasDerivAt (I.xiMK m k) (ξt k) t)
    (hχt : ∀ k ∈ xiMKNearSupportFinset I m t ρ,
      HasDerivAt (fun s => I.chiTilde hΦ m κ k s x) (χt k) t)
    (hGt : ∀ k ∈ xiMKNearSupportFinset I m t ρ,
      HasDerivAt (fun s => G I hΦ m T (lIdx β I.Λ m k) s x) (Gt k) t)
    (hTx : HasFDerivAt (T t) LT x)
    (hHx : HasFDerivAt (I.Hm hΦ m κ T t) LH x)
    (hχx : ∀ k ∈ xiMKNearSupportFinset I m t ρ,
      HasFDerivAt (I.chiTilde hΦ m κ k t) (Lχ k) x)
    (hGx : ∀ k ∈ xiMKNearSupportFinset I m t ρ,
      HasFDerivAt (fun y => G I hΦ m T (lIdx β I.Λ m k) t y)
        (LG k) x) :
    deriv (fun s => I.ansatz hΦ m κ T s x) t +
        fderiv ℝ (I.ansatz hΦ m κ T t) x b =
      Tt + Ht +
        (∑ k ∈ xiMKNearSupportFinset I m t ρ,
          (ξt k * vecDot (I.chiTilde hΦ m κ k t x)
              (G I hΦ m T (lIdx β I.Λ m k) t x) +
            I.xiMK m k t *
              (vecDot (χt k) (G I hΦ m T (lIdx β I.Λ m k) t x) +
                vecDot (I.chiTilde hΦ m κ k t x) (Gt k)))) +
        (LT b +
          (∑ k ∈ xiMKNearSupportFinset I m t ρ,
            I.xiMK m k t *
              (vecDot (Lχ k b) (G I hΦ m T (lIdx β I.Λ m k) t x) +
                vecDot (I.chiTilde hΦ m κ k t x) (LG k b))) + LH b) := by
  let S := xiMKNearSupportFinset I m t ρ
  let ξ : ℤ → ℝ → ℝ := fun k s => I.xiMK m k s
  let χ : ℤ → ℝ → Vec 2 → Vec 2 := fun k s y => I.chiTilde hΦ m κ k s y
  let Gc : ℤ → ℝ → Vec 2 → Vec 2 := fun k s y =>
    G I hΦ m T (lIdx β I.Λ m k) s y
  let H : ℝ → Vec 2 → ℝ := fun s y => I.Hm hΦ m κ T s y
  have hlocal (s : ℝ) (y : Vec 2)
      (hs : s ∈ Set.Ioo (t - ρ) (t + ρ)) :
      (∑' k : ℤ, I.xiMK m k s *
        vecDot (I.chiTilde hΦ m κ k s y)
          (G I hΦ m T (lIdx β I.Λ m k) s y)) =
        ∑ k ∈ S, I.xiMK m k s *
          vecDot (I.chiTilde hΦ m κ k s y)
            (G I hΦ m T (lIdx β I.Λ m k) s y) := by
    apply tsum_eq_sum
    intro k hk
    simp [FrozenAnsatzMaterial.xiMK_eq_zero_off_nearSupport I m t ρ s hs hk]
  have hpoint : I.ansatz hΦ m κ T t =
      finiteAnsatzField S T H ξ χ Gc t := by
    funext y
    have htmem : t ∈ Set.Ioo (t - ρ) (t + ρ) := by
      constructor <;> linarith
    have hlocal' :
        (∑' k : ℤ, I.xiMK m k t *
          vecDot (I.chiTilde hΦ m κ k t y)
            (spaceGrad (fun z => T t (I.xFlow hΦ m
              (lIdx β I.Λ m k) t z))
              (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y))) =
          ∑ k ∈ S, I.xiMK m k t *
            vecDot (I.chiTilde hΦ m κ k t y)
              (spaceGrad (fun z => T t (I.xFlow hΦ m
                (lIdx β I.Λ m k) t z))
                (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y)) := by
      simpa only [G] using hlocal t y htmem
    simp only [finiteAnsatzField, H, ξ, χ, Gc, Ingredients.ansatz, G]
    rw [hlocal']
  have htimeFrozen := ansatz_hasDerivAt I hΦ m κ ρ T t x
    (fun _ => Tt) (fun _ => Ht) ξt χt Gt
    hρ hTt hHt hξt hχt hGt
  have htimeFinite := hasDerivAt_finiteAnsatz S
    (fun s => T s x) (fun s => H s x) (fun _ => Tt) (fun _ => Ht)
    ξ (fun k _ => ξt k) (fun k s => χ k s x) (fun k s => Gc k s x)
    (fun k _ => χt k) (fun k _ => Gt k) hTt hHt
    (by simpa [S, ξ] using hξt)
    (by simpa [S, χ] using hχt)
    (by simpa [S, Gc] using hGt)
  have hderiv : deriv (fun s => I.ansatz hΦ m κ T s x) t =
      deriv (fun s => finiteAnsatzField S T H ξ χ Gc s x) t := by
    rw [htimeFrozen.deriv]
    simpa [finiteAnsatzField, H, ξ, χ, Gc] using htimeFinite.deriv.symm
  have hgradEq : fderiv ℝ (I.ansatz hΦ m κ T t) x b =
      fderiv ℝ (finiteAnsatzField S T H ξ χ Gc t) x b := by
    exact congrArg (fun f : Vec 2 → ℝ => fderiv ℝ f x b) hpoint
  have hfiniteExpansion := finiteAnsatz_material_expansion S T H ξ χ Gc
    t x b Tt Ht ξt χt Gt LT LH Lχ LG hTt hHt
    (by simpa [S] using hξt)
    (by simpa [S, χ] using hχt)
    (by simpa [S, Gc] using hGt)
    hTx (by simpa [H] using hHx)
    (by simpa [S, χ] using hχx)
    (by simpa [S, Gc] using hGx)
  calc
    deriv (fun s => I.ansatz hΦ m κ T s x) t +
        fderiv ℝ (I.ansatz hΦ m κ T t) x b =
      deriv (fun s => finiteAnsatzField S T H ξ χ Gc s x) t +
        fderiv ℝ (finiteAnsatzField S T H ξ χ Gc t) x b := by
          rw [hderiv, hgradEq]
    _ = Tt + Ht +
        (∑ k ∈ S,
          (ξt k * vecDot (χ k t x) (Gc k t x) +
            ξ k t * (vecDot (χt k) (Gc k t x) +
              vecDot (χ k t x) (Gt k)))) +
        (LT b +
          (∑ k ∈ S, ξ k t *
            (vecDot (Lχ k b) (Gc k t x) +
              vecDot (χ k t x) (LG k b))) + LH b) := hfiniteExpansion
    _ = _ := by simp [S, ξ, χ, Gc]

end AVenhance.Infra.Section5

end
