/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.R46
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.Overlap
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.FluxMatrix
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.Approx

/-! Support and fixed-time algebra for the transition-window flux.

The cutoff inequalities in the ingredient package imply genuine
support statements because their lower bounds are nonnegative indicators.
-/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization
namespace AVenhance.Infra.Section5

open AVenhance

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

theorem R46FluxSupport.indIcc_nonneg_r46 (a b t : ℝ) : 0 ≤ indIcc a b t := by
  by_cases ht : t ∈ Set.Icc a b <;> simp [indIcc, ht]

theorem R46FluxSupport.hatZetaML_mem_refresh_window (m : ℕ) (hm : 1 ≤ m)
    (l : ℤ) (t : ℝ) (hne : I.hatZetaML m l t ≠ 0) :
    t ∈ Set.Icc ((l - 1 / 2) * tauPP β I.Λ m + tauP β I.Λ m)
      ((l + 1 / 2) * tauPP β I.Λ m - tauP β I.Λ m) := by
  have hnonneg := Infra.Ingredients.hatZetaML_nonneg I hm l t
  have hpos : 0 < I.hatZetaML m l t := lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hle := I.hatZeta_le m hm l t
  by_contra hnot
  have hz : indIcc ((l - 1 / 2) * tauPP β I.Λ m + tauP β I.Λ m)
      ((l + 1 / 2) * tauPP β I.Λ m - tauP β I.Λ m) t = 0 := by
    unfold indIcc
    rw [Set.indicator_of_notMem hnot]
  rw [hz] at hle
  change I.hatZetaML m l t ≤ 0 at hle
  linarith

theorem R46FluxSupport.xiMK_ne_zero_near_center (m : ℕ) {k : ℤ} {t : ℝ}
    (hne : I.xiMK m k t ≠ 0) :
    |t - (k : ℝ) * tau β I.Λ m| ≤ 5 / 4 * tau β I.Λ m := by
  simp only [Ingredients.xiMK, scaledCutoff] at hne
  have hτ := I.tau_pos' m
  let u := (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m
  have hmem : u ∈ Set.Icc (-(5 / 4) : ℝ) (5 / 4) := by
    by_contra hnot
    have hz : indIcc (-(5 / 4)) (5 / 4) u = 0 := by
      unfold indIcc
      rw [Set.indicator_of_notMem hnot]
    have hle := I.xi_le_ind u
    rw [hz] at hle
    have hnonneg : 0 ≤ I.xi u :=
      (R46FluxSupport.indIcc_nonneg_r46 (-(3 / 4)) (3 / 4) u).trans (I.ind_le_xi u)
    have hzero : I.xi u = 0 := le_antisymm hle hnonneg
    exact hne (by simpa [u, Ingredients.xiMK, scaledCutoff] using hzero)
  have hu := abs_le.mpr ⟨hmem.1, hmem.2⟩
  rw [show u = (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m by rfl,
    abs_div, abs_of_pos hτ, div_le_iff₀ hτ] at hu
  nlinarith

theorem R46FluxSupport.tauP_ge_five_tau (m : ℕ) (hm : 1 ≤ m) :
    5 * tau β I.Λ m ≤ tauP β I.Λ m := by
  rw [Infra.Ingredients.tauP_eq_cellFactor_mul_tau hm]
  have hceil : 1 ≤
      (⌈epsilon β I.Λ (m - 1) ^ (-delta β)⌉₊ : ℝ) := by
    have hp : 0 < epsilon β I.Λ (m - 1) ^ (-delta β) :=
      Real.rpow_pos_of_pos (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
        (by exact_mod_cast I.two_pow_seven_le)) _
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.ceil_pos.mpr hp))
  have hfactor : 5 ≤ Infra.Ingredients.tauCellFactor β I.Λ m := by
    unfold Infra.Ingredients.tauCellFactor
    linarith
  exact mul_le_mul_of_nonneg_right hfactor (I.tau_pos' m).le

/-- If a large refresh cutoff and a small `xi` cutoff are both active, the
small cutoff's refresh index is the large cutoff's index. -/
theorem lIdx_eq_of_hatZeta_xiMK_ne_zero (m : ℕ) (hm : 1 ≤ m)
    (l k : ℤ) (t : ℝ) (hz : I.hatZetaML m l t ≠ 0)
    (hξ : I.xiMK m k t ≠ 0) :
    lIdx β I.Λ m k = l := by
  have hwindow := R46FluxSupport.hatZetaML_mem_refresh_window I m hm l t hz
  have hnear := R46FluxSupport.xiMK_ne_zero_near_center I m hξ
  have hτ := I.tau_pos' m
  have hτP := R46FluxSupport.tauP_ge_five_tau I m hm
  have hcenterLow : (l : ℝ) * tauPP β I.Λ m - tauPP β I.Λ m / 2 <
      (k : ℝ) * tau β I.Λ m := by
    have hh := abs_le.mp hnear
    nlinarith [hwindow.1, hτP]
  have hcenterHigh : (k : ℝ) * tau β I.Λ m <
      (l : ℝ) * tauPP β I.Λ m + tauPP β I.Λ m / 2 := by
    have hh := abs_le.mp hnear
    nlinarith [hwindow.2, hτP]
  have hcell := Infra.Ingredients.taum_prime_supp k I.one_lt_beta I.beta_lt
    (by exact_mod_cast I.two_pow_seven_le) hm
  have hmem : (k : ℝ) * tau β I.Λ m ∈
      Set.Icc ((k : ℝ) * tau β I.Λ m - tau β I.Λ m / 2)
        ((k : ℝ) * tau β I.Λ m + tau β I.Λ m / 2) := by
    constructor <;> linarith [hτ]
  have hassigned := hcell hmem
  have hassignedLow :
      (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m - tauPP β I.Λ m / 2 ≤
        (k : ℝ) * tau β I.Λ m := hassigned.1
  have hassignedHigh :
      (k : ℝ) * tau β I.Λ m ≤
        (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m + tauPP β I.Λ m / 2 :=
    hassigned.2
  by_contra hne
  have hlt : lIdx β I.Λ m k < l ∨ l < lIdx β I.Λ m k := by omega
  rcases hlt with hlt | hlt
  · have hlt' : (lIdx β I.Λ m k : ℝ) + 1 ≤ l := by exact_mod_cast (Int.add_one_le_iff.mpr hlt)
    have hlarge : (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m +
        tauPP β I.Λ m / 2 ≤ (l : ℝ) * tauPP β I.Λ m -
          tauPP β I.Λ m / 2 := by
      nlinarith [I.tauPP_pos' m]
    linarith [hassignedHigh, hcenterLow]
  · have hlt' : (l : ℝ) + 1 ≤ (lIdx β I.Λ m k : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr hlt)
    have hlarge : (l : ℝ) * tauPP β I.Λ m +
        tauPP β I.Λ m / 2 ≤ (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m -
          tauPP β I.Λ m / 2 := by
      nlinarith [I.tauPP_pos' m]
    linarith [hassignedLow, hcenterHigh]

theorem R46FluxSupport.hatXiML_eq_one_of_hatZeta_ne_zero (m : ℕ) (hm : 1 ≤ m)
    (l : ℤ) (t : ℝ) (hz : I.hatZetaML m l t ≠ 0) :
    I.hatXiML m l t = 1 := by
  have hwindow := R46FluxSupport.hatZetaML_mem_refresh_window I m hm l t hz
  have hcore : indIcc ((l - 1 / 2) * tauPP β I.Λ m + tauP β I.Λ m)
      ((l + 1 / 2) * tauPP β I.Λ m - tauP β I.Λ m) t = 1 := by
    change Set.indicator (Set.Icc _ _) (fun _ => (1 : ℝ)) t = 1
    rw [Set.indicator_of_mem hwindow]
  have hge := I.hatXi_ge m hm l t
  change indIcc ((l - 1 / 2) * tauPP β I.Λ m + tauP β I.Λ m)
      ((l + 1 / 2) * tauPP β I.Λ m - tauP β I.Λ m) t ≤ I.hatXiML m l t at hge
  have hle := (Infra.Ingredients.hatXiML_mem_Icc I hm l t).2
  rw [hcore] at hge
  exact le_antisymm hle hge

theorem R46FluxSupport.hatXiML_eq_zero_of_ne_refresh (m : ℕ) (hm : 1 ≤ m)
    (l j : ℤ) (t : ℝ) (hz : I.hatZetaML m l t ≠ 0) (hjl : j ≠ l) :
    I.hatXiML m j t = 0 := by
  classical
  have hone := R46FluxSupport.hatXiML_eq_one_of_hatZeta_ne_zero I m hm l t hz
  let S : Finset ℤ := {l, j}
  have hfinite := I.hatXiML_support_finite hm t
  have hsumle : (∑ q ∈ S, I.hatXiML m q t) ≤
      ∑' q : ℤ, I.hatXiML m q t :=
    (summable_of_hasFiniteSupport hfinite).sum_le_tsum S
      (fun q _ => (Infra.Ingredients.hatXiML_mem_Icc I hm q t).1)
  have hsumid : (∑ q ∈ S, I.hatXiML m q t) =
      I.hatXiML m l t + I.hatXiML m j t := by
    change Finset.sum {l, j} (fun q => I.hatXiML m q t) = _
    rw [Finset.sum_insert (by simpa using Ne.symm hjl)]
    simp
  rw [hsumid, Infra.Ingredients.hatXiML_partition I hm t, hone] at hsumle
  have hjnonneg := (Infra.Ingredients.hatXiML_mem_Icc I hm j t).1
  linarith

/-- On any active refresh window, the large-scale average of the pulled-back
gradients is exactly the gradient with that window's index. -/
theorem Gbar_eq_G_of_hatZeta_ne_zero (hΦ : IsStreamSeq I Φ) (m : ℕ)
    (hm : 1 ≤ m) (T : ℝ → Vec 2 → ℝ) (l : ℤ) (t : ℝ) (x : Vec 2)
    (hz : I.hatZetaML m l t ≠ 0) :
    Gbar I hΦ m T t x = G I hΦ m T l t x := by
  classical
  have hone := R46FluxSupport.hatXiML_eq_one_of_hatZeta_ne_zero I m hm l t hz
  have hzero : ∀ j : ℤ, j ≠ l → I.hatXiML m j t = 0 := by
    intro j hj
    exact R46FluxSupport.hatXiML_eq_zero_of_ne_refresh I m hm l j t hz hj
  unfold Gbar
  rw [tsum_eq_single l (fun j hj => by rw [hzero j hj]; simp)]
  simp [hone]

/-- If all refresh coefficients vanish, the exact Section 3 flux formula
reduces to the molecular matrix. This uses the `zetaProd` coefficient
and does not require the unmasked small cutoff `zetaMK` itself to vanish. -/
theorem flux_eq_kappa_of_hatZeta_zero (m : ℕ) (hm : 1 ≤ m) (κ t : ℝ)
    (hzero : ∀ l : ℤ, I.hatZetaML m l t = 0) :
    I.flux κ m t = κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hterms : (fun k : {k : ℤ // Odd k} =>
      (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 *
        I.zetaProd m k.1 t * I.corrTime κ m k.1 t) •
        ((if (k : ℤ) % 4 = 1 then
            (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) else 0) +
          (if (k : ℤ) % 4 = 3 then
            (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) else 0))) = fun _ => 0 := by
    funext k
    simp [Ingredients.zetaProd, hzero (lIdx β I.Λ m k.1)]
  rw [Infra.Section3.flux_eq_odd_mode_sum I hm κ t, hterms]
  simp

/-- The flux vanishes wherever one of the refresh cutoffs is active. -/
theorem r46Flux_eq_zero_of_hatZeta_ne_zero (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (hm : 1 ≤ m) (κm : ℝ) (T : ℝ → Vec 2 → ℝ)
    (l : ℤ) (t : ℝ) (hz : I.hatZetaML m l t ≠ 0) :
    r46Flux I hΦ m κm T t = 0 := by
  classical
  funext x
  have hGbar := Gbar_eq_G_of_hatZeta_ne_zero I hΦ m hm T l t x hz
  have hdefect : (∑' k : {k : ℤ // Odd k}, I.xiMK m k t •
      (Gbar I hΦ m T t x - G I hΦ m T (lIdx β I.Λ m k) t x)) = 0 := by
    have hterms : (fun k : {k : ℤ // Odd k} => I.xiMK m k t •
        (Gbar I hΦ m T t x - G I hΦ m T (lIdx β I.Λ m k) t x)) = fun _ => 0 := by
      funext k
      by_cases hξ : I.xiMK m k t = 0
      · simp [hξ]
      · have hk := lIdx_eq_of_hatZeta_xiMK_ne_zero I m hm l k t hz hξ
        rw [hGbar, hk]
        simp
    rw [hterms]
    simp
  unfold r46Flux
  rw [hdefect]
  simp

/-- On the complement of the refresh windows the actual flux factor of the transition-window term
is exactly `κm I`. -/
theorem r46Flux_eq_kappa_smul_defect_of_hatZeta_zero
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ)
    (hzero : ∀ l : ℤ, I.hatZetaML m l t = 0) :
    r46Flux I hΦ m κm T t = κm •
      (∑' k : {k : ℤ // Odd k}, I.xiMK m k t •
        (Gbar I hΦ m T t - G I hΦ m T (lIdx β I.Λ m k) t)) := by
  unfold r46Flux
  rw [flux_eq_kappa_of_hatZeta_zero I m hm κm t hzero]
  funext x
  have hmul (v : Vec 2) :
      (κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)).mulVec v = κm • v := by
    change (κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) • v = κm • v
    rw [smul_assoc, one_smul]
  rw [hmul]
  have hsupp : {k : {k : ℤ // Odd k} | I.xiMK m k t •
      (Gbar I hΦ m T t - G I hΦ m T (lIdx β I.Λ m k) t) ≠ (0 : Vec 2 → Vec 2)}.Finite :=
    (Set.Finite.preimage (f := Subtype.val) Subtype.val_injective.injOn
      (I.xiMK_support_finite m t)).subset (by
      intro k hk
      by_contra hξ
      have hξ0 : I.xiMK m k t = 0 := by
        by_contra hne
        exact hξ (by simpa using hne)
      apply hk
      simp [hξ0])
  have hsum : Summable (fun k : {k : ℤ // Odd k} => I.xiMK m k t •
      (Gbar I hΦ m T t - G I hΦ m T (lIdx β I.Λ m k) t)) :=
    summable_of_hasFiniteSupport hsupp
  have hsum_apply : (∑' k : {k : ℤ // Odd k}, I.xiMK m k t •
      (Gbar I hΦ m T t x - G I hΦ m T (lIdx β I.Λ m k) t x)) =
      (∑' k : {k : ℤ // Odd k}, I.xiMK m k t •
        (Gbar I hΦ m T t - G I hΦ m T (lIdx β I.Λ m k) t)) x := by
    simpa only [Pi.smul_apply, Pi.sub_apply] using
      (Pi.tsum_apply hsum (x := x)).symm
  exact congrArg (fun v : Vec 2 => κm • v) hsum_apply

end AVenhance.Infra.Section5
end
