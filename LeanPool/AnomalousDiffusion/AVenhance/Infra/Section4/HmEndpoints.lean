/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.Hm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.CorrectorBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureCoefficientBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureEnergyIntegrability
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureFluxBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.DriftCommutatorExpansion
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureMaterialInduction
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TensorNorm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SeedMultiplierSourceBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureIterateClassicalFamily
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.DissipationCoordinateL2
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsThetaAnalytic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureCoefficientTopSourceBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SourceSmallnessThreshold
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.LRecurse
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FrozenHmTelescope

/-! The Hm expansion vanishes in the gaps between the large-scale
cutoff supports.  This is the endpoint input in the source's transported
energy argument. -/

@[expose] public section

noncomputable section

open Homogenization Filter Topology

namespace AVenhance.Infra.Section4

open AVenhance

/-- Every translated large-scale `zeta` cutoff vanishes in a gap of radius
`tauP` around a half-cell boundary. -/
theorem hatZetaML_eq_zero_of_cellGap {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (l k : ℤ) {t : ℝ}
    (ht : t ∈ Set.Ioo
      ((l + 1 / 2) * tauPP β I.Λ m - tauP β I.Λ m)
      ((l + 1 / 2) * tauPP β I.Λ m + tauP β I.Λ m)) :
    I.hatZetaML m k t = 0 := by
  have hP : 0 < tauPP β I.Λ m :=
    Infra.Cutoff.tauPP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hp : 0 < tauP β I.Λ m :=
    Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hnot : t ∉ Set.Icc
      ((k - 1 / 2) * tauPP β I.Λ m + tauP β I.Λ m)
      ((k + 1 / 2) * tauPP β I.Λ m - tauP β I.Λ m) := by
    by_cases hkl : k ≤ l
    · intro hmem
      have htlo := ht.1
      have hklcast : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hkl
      have hend : (k : ℝ) + 1 / 2 ≤ (l : ℝ) + 1 / 2 := by linarith
      have hupper :
          (k + 1 / 2) * tauPP β I.Λ m - tauP β I.Λ m ≤
            (l + 1 / 2) * tauPP β I.Λ m - tauP β I.Λ m := by
        exact sub_le_sub_right (mul_le_mul_of_nonneg_right hend hP.le) _
      have htmem := hmem.2
      linarith
    · have hlk' : l + 1 ≤ k := by omega
      intro hmem
      have htup := ht.2
      have hlkcast : (l : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hlk'
      have hend : (l : ℝ) + 1 / 2 ≤ (k : ℝ) - 1 / 2 := by linarith
      have hlower :
          (l + 1 / 2) * tauPP β I.Λ m + tauP β I.Λ m ≤
            (k - 1 / 2) * tauPP β I.Λ m + tauP β I.Λ m := by
        exact add_le_add_left (mul_le_mul_of_nonneg_right hend hP.le) _
      have htmem := hmem.1
      linarith
  have hupper := I.hatZeta_le m hm k t
  rw [indIcc_eq_zero_of_not_mem hnot] at hupper
  have hnonneg := Infra.Ingredients.hatZetaML_nonneg I hm k t
  exact le_antisymm hupper hnonneg

/-- The actual memory coefficient `L_{m,n}` is identically zero on every
large-scale cutoff gap. -/
theorem LMN_eq_zero_of_cellGap {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (l : ℤ) {t κ : ℝ} (n : ℕ)
    (ht : t ∈ Set.Ioo
      ((l + 1 / 2) * tauPP β I.Λ m - tauP β I.Λ m)
      ((l + 1 / 2) * tauPP β I.Λ m + tauP β I.Λ m)) :
    I.LMN κ m n t = 0 := by
  have hzero (k : ℤ) : I.hatZetaML m k t = 0 :=
    hatZetaML_eq_zero_of_cellGap I hm l k ht
  simp [Ingredients.LMN, hzero]

/-- Every recursively defined `A_{m,n,r}` tensor vanishes throughout a
large-scale cutoff gap.  The induction uses the literal corrected
recursion, and only differentiates a function that is locally identically
zero there. -/
theorem Amnr_eq_zero_of_cellGap {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (n : ℕ)
    (l : ℤ) : ∀ r : ℕ, ∀ t ∈ Set.Ioo
      ((l + 1 / 2) * tauPP β I.Λ m - tauP β I.Λ m)
      ((l + 1 / 2) * tauPP β I.Λ m + tauP β I.Λ m),
      ∀ x i j k, I.Amnr hΦ m κ n T r t x i j k = 0 := by
  intro r
  induction r with
  | zero =>
      intro t ht x i j k
      rw [Ingredients.Amnr]
      simp [LMN_eq_zero_of_cellGap I hm l n ht]
  | succ r ih =>
      intro t ht x i j k
      have hlocal : (fun s => I.Amnr hΦ m κ n T r s x i j k) =ᶠ[𝓝 t]
          fun _ => 0 := by
        have hnhds : Set.Ioo
            ((l + 1 / 2) * tauPP β I.Λ m - tauP β I.Λ m)
            ((l + 1 / 2) * tauPP β I.Λ m + tauP β I.Λ m) ∈ 𝓝 t :=
          isOpen_Ioo.mem_nhds ht
        filter_upwards [hnhds] with s hs
        exact ih s hs x i j k
      have hderiv : deriv (fun s => I.Amnr hΦ m κ n T r s x i j k) t = 0 := by
        have hconst : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t := hasDerivAt_const t 0
        exact (hconst.congr_of_eventuallyEq hlocal).deriv
      have hspace : (fun y => I.Amnr hΦ m κ n T r t y i j k) = fun _ => 0 := by
        funext y
        exact ih t ht y i j k
      have hgrad : AVenhance.spaceGrad
          (fun y => I.Amnr hΦ m κ n T r t y i j k) x = 0 := by
        rw [hspace]
        change (fun p : Fin 2 => fderiv ℝ (fun _ : Vec 2 => (0 : ℝ)) x
          (Homogenization.basisVec p)) = 0
        ext p
        simp
      rw [Amnr_succ]
      unfold amnrMaterial
      rw [hderiv, hgrad]
      have hA0 := ih t ht x 0 j k
      have hA1 := ih t ht x 1 j k
      unfold vecDot
      simp [hA0, hA1]

/-- Each `H_{m,r}` vanishes in the same cutoff gap, since its entire
divergence field is spatially zero there. -/
theorem Hmr_eq_zero_of_cellGap {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (r : ℕ) (l : ℤ) {t : ℝ}
    (ht : t ∈ Set.Ioo
      ((l + 1 / 2) * tauPP β I.Λ m - tauP β I.Λ m)
      ((l + 1 / 2) * tauPP β I.Λ m + tauP β I.Λ m)) (x : Vec 2) :
    I.Hmr hΦ m κ T r t x = 0 := by
  have hA (n : ℕ) (y : Vec 2) (i j k : Fin 2) :
      I.Amnr hΦ m κ n T r t y i j k = 0 := by
    exact Amnr_eq_zero_of_cellGap I hΦ hm κ T n l r t ht y i j k
  have hfield : (fun y i => ∑ n ∈ Finset.range (Nstar β),
      ∑ j : Fin 2, ∑ k : Fin 2,
        I.Amnr hΦ m κ n T r t y i j k * I.qMNR κ m n (r + 1) t j k) =
      fun _ _ => 0 := by
    funext y i
    simp [hA]
  unfold Ingredients.Hmr
  rw [hfield]
  change ∑ i : Fin 2, AVenhance.spaceGrad (fun _ : Vec 2 => (0 : ℝ)) x i = 0
  simp [AVenhance.spaceGrad]

/-- The `H_m` expansion vanishes at every half-cell boundary. -/
theorem Hm_eq_zero_at_halfCell {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (l : ℤ) :
    I.Hm hΦ m κ T ((l + 1 / 2) * tauPP β I.Λ m) = fun _ => 0 := by
  funext x
  unfold Ingredients.Hm
  apply Finset.sum_eq_zero
  intro r hr
  have ht : ((l + 1 / 2) * tauPP β I.Λ m) ∈ Set.Ioo
      ((l + 1 / 2) * tauPP β I.Λ m - tauP β I.Λ m)
      ((l + 1 / 2) * tauPP β I.Λ m + tauP β I.Λ m) := by
    have hp := Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
    constructor <;> linarith
  exact Hmr_eq_zero_of_cellGap I hΦ hm κ T r l ht x

/-- Each endpoint potential in the telescope vanishes at every
half-cell boundary.  This is the companion endpoint to `Hm_eq_zero_at_halfCell`. -/
theorem hmEndpoint_eq_zero_at_halfCell {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (r : ℕ) (l : ℤ) :
    AVenhance.Infra.Section5.hmEndpoint I hΦ m κ T r
      ((l + 1 / 2) * tauPP β I.Λ m) = fun _ => 0 := by
  funext x
  unfold AVenhance.Infra.Section5.hmEndpoint vecDiv
  apply Finset.sum_eq_zero
  intro i hi
  have hzero (n : ℕ) (j k : Fin 2) :
      ∀ y, I.Amnr hΦ m κ n T r ((l + 1 / 2) * tauPP β I.Λ m) y i j k = 0 := by
    intro y
    have hp : 0 < tauP β I.Λ m := Infra.Cutoff.tauP_pos
      I.one_lt_beta I.beta_lt I.two_pow_seven_le
    have ht : ((l + 1 / 2) * tauPP β I.Λ m) ∈ Set.Ioo
        ((l + 1 / 2) * tauPP β I.Λ m - tauP β I.Λ m)
        ((l + 1 / 2) * tauPP β I.Λ m + tauP β I.Λ m) := by
      constructor <;> linarith
    exact Amnr_eq_zero_of_cellGap I hΦ hm κ T n l r
      ((l + 1 / 2) * tauPP β I.Λ m) ht y i j k
  have hfield : (fun y => ∑ n ∈ Finset.range (Nstar β),
      ∑ j : Fin 2, ∑ k : Fin 2,
        I.Amnr hΦ m κ n T r ((l + 1 / 2) * tauPP β I.Λ m) y i j k *
          I.qMNR κ m n r ((l + 1 / 2) * tauPP β I.Λ m) j k) =
      fun _ => (0 : ℝ) := by
    funext y
    apply Finset.sum_eq_zero
    intro n hn
    apply Finset.sum_eq_zero
    intro j hj
    apply Finset.sum_eq_zero
    intro k hk
    rw [hzero n j k y]
    simp
  rw [hfield]
  simp [AVenhance.spaceGrad]

end AVenhance.Infra.Section4

end
