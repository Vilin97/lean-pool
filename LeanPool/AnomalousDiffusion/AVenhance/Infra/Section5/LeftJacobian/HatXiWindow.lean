/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.R46FluxSupport

/-! LeftJacobian the left-Jacobian form: on an active refresh window the large-scale cutoff `ξ̂_l`
    is the
indicator of that window (local re-proof of the private lemmas of
`Terms/R46FluxSupport`, which are not exported). -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5.LeftJacobian

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β)

theorem HatXiWindow.indIcc_nonneg_e53 (a b t : ℝ) : 0 ≤ indIcc a b t := by
  by_cases ht : t ∈ Set.Icc a b <;> simp [indIcc, ht]

theorem hatZetaML_mem_window (m : ℕ) (hm : 1 ≤ m)
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

/-- On an active refresh window the large cutoff equals one. -/
theorem hatXiML_eq_one_of_hatZeta_ne_zero (m : ℕ) (hm : 1 ≤ m)
    (l : ℤ) (t : ℝ) (hz : I.hatZetaML m l t ≠ 0) :
    I.hatXiML m l t = 1 := by
  have hwindow := hatZetaML_mem_window I m hm l t hz
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

/-- On an active refresh window all other large cutoffs vanish. -/
theorem hatXiML_eq_zero_of_ne_refresh (m : ℕ) (hm : 1 ≤ m)
    (l j : ℤ) (t : ℝ) (hz : I.hatZetaML m l t ≠ 0) (hjl : j ≠ l) :
    I.hatXiML m j t = 0 := by
  classical
  have hone := hatXiML_eq_one_of_hatZeta_ne_zero I m hm l t hz
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

end AVenhance.Infra.Section5.LeftJacobian

end
