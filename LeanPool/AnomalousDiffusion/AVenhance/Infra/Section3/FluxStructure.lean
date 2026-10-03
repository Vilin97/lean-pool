/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.SpaceAverages
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.ChiM
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.PsiM
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.Flux

/-! The cutoff separation that reduces the spatial flux to one active shear. -/

@[expose] public section

noncomputable section

open MeasureTheory
open Homogenization

namespace AVenhance.Infra.Section3

open AVenhance

theorem FluxStructure.zetaMK_coord_bound {β : ℝ} (I : Ingredients β) {m : ℕ}
    (k : ℤ) (t : ℝ) (hzk : I.zetaMK m k t ≠ 0) :
    (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m ∈
      Set.Icc (-(2 / 3 : ℝ)) (2 / 3) := by
  have hτ := Infra.Ingredients.tau_pos I.one_lt_beta I.beta_lt
    I.two_pow_seven_le (m := m)
  let u := (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m
  have hpos : 0 < I.zeta u := by
    have hn := I.zeta_nonneg u
    change I.zeta u ≠ 0 at hzk
    exact lt_of_le_of_ne hn (Ne.symm hzk)
  by_contra hnot
  have hind : indIcc (-(2 / 3 : ℝ)) (2 / 3) u = 0 := by
    unfold indIcc
    rw [Set.indicator_of_notMem hnot]
  have hle := I.zeta_le_ind u
  rw [hind] at hle
  change I.zeta u ≤ 0 at hle
  linarith

theorem FluxStructure.xi_eq_one_of_zetaMK_ne_zero {β : ℝ}
    (I : Ingredients β) {m : ℕ} (_hm : 1 ≤ m) (k : ℤ) (t : ℝ)
    (hzk : I.zetaMK m k t ≠ 0) : I.xiMK m k t = 1 := by
  have hτ := Infra.Ingredients.tau_pos I.one_lt_beta I.beta_lt
    I.two_pow_seven_le (m := m)
  let u := (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m
  have hu := FluxStructure.zetaMK_coord_bound I k t hzk
  have hinner : u ∈ Set.Icc (-(3 / 4 : ℝ)) (3 / 4) := by
    constructor <;> have := hu.1 <;> have := hu.2 <;> norm_num at * <;> linarith
  have houter : u ∈ Set.Icc (-(5 / 4 : ℝ)) (5 / 4) := by
    constructor <;> have := hu.1 <;> have := hu.2 <;> norm_num at * <;> linarith
  have hlow := I.ind_le_xi u
  have hhigh := I.xi_le_ind u
  have hinner' : indIcc (-(3 / 4 : ℝ)) (3 / 4) u = 1 := by
    simp [indIcc, hinner]
  have houter' : indIcc (-(5 / 4 : ℝ)) (5 / 4) u = 1 := by
    simp [indIcc, houter]
  rw [hinner'] at hlow
  rw [houter'] at hhigh
  change I.xi u = 1
  linarith

theorem FluxStructure.xi_eq_zero_outside {β : ℝ} (I : Ingredients β) {u : ℝ}
    (hu : u ∉ Set.Icc (-(5 / 4 : ℝ)) (5 / 4)) : I.xi u = 0 := by
  have hind_nonneg : 0 ≤ indIcc (-(3 / 4 : ℝ)) (3 / 4) u := by
    by_cases hmem : u ∈ Set.Icc (-(3 / 4 : ℝ)) (3 / 4)
    · simp [indIcc, hmem]
    · simp [indIcc, hmem]
  have hlow := I.ind_le_xi u
  have hhigh := I.xi_le_ind u
  have houter : indIcc (-(5 / 4 : ℝ)) (5 / 4) u = 0 := by
    unfold indIcc
    rw [Set.indicator_of_notMem hu]
  rw [houter] at hhigh
  change I.xi u ≤ 0 at hhigh
  have hnonneg : 0 ≤ I.xi u := le_trans hind_nonneg hlow
  linarith

/-- The scaled corrector cutoff vanishes outside its support interval. -/
theorem xiMK_eq_zero_outside {β : ℝ} (I : Ingredients β) {m : ℕ}
    (k : ℤ) (t : ℝ)
    (hu : (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m ∉
      Set.Icc (-(5 / 4 : ℝ)) (5 / 4)) : I.xiMK m k t = 0 := by
  change I.xi ((t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m) = 0
  exact FluxStructure.xi_eq_zero_outside I hu

theorem FluxStructure.odd_indices_separated {k l : ℤ} (hk : Odd k) (hl : Odd l)
    (hne : k ≠ l) : l ≤ k - 2 ∨ k + 2 ≤ l := by
  rcases hk with ⟨a, rfl⟩
  rcases hl with ⟨b, rfl⟩
  omega

/-- On the support of an odd small cutoff, its own transition cutoff is one. -/
theorem xiMK_eq_one_of_zetaMK_ne_zero {β : ℝ} (I : Ingredients β)
    {m : ℕ} (_hm : 1 ≤ m) (k : ℤ) (t : ℝ)
    (hzk : I.zetaMK m k t ≠ 0) : I.xiMK m k t = 1 := by
  exact FluxStructure.xi_eq_one_of_zetaMK_ne_zero I _hm k t hzk

/-- At a time in one odd shear's active cutoff, all other odd transition
cutoffs vanish. -/
theorem xiMK_eq_zero_of_zetaMK_ne_zero_of_odd_ne {β : ℝ}
    (I : Ingredients β) {m : ℕ} (_hm : 1 ≤ m) {k l : ℤ}
    (hk : Odd k) (hl : Odd l) (hne : l ≠ k) (t : ℝ)
    (hzk : I.zetaMK m k t ≠ 0) : I.xiMK m l t = 0 := by
  have hτ := Infra.Ingredients.tau_pos I.one_lt_beta I.beta_lt
    I.two_pow_seven_le (m := m)
  have hu := FluxStructure.zetaMK_coord_bound I k t hzk
  have hsep := FluxStructure.odd_indices_separated hk hl (Ne.symm hne)
  have hcoord :
      (t - (l : ℝ) * tau β I.Λ m) / tau β I.Λ m =
        (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m -
          ((l : ℝ) - (k : ℝ)) := by
    field_simp [ne_of_gt hτ]
    ring
  have hout :
      (t - (l : ℝ) * tau β I.Λ m) / tau β I.Λ m < -(5 / 4 : ℝ) ∨
      5 / 4 < (t - (l : ℝ) * tau β I.Λ m) / tau β I.Λ m := by
    rw [hcoord]
    rcases hsep with hleft | hright
    · have hidx : (l : ℝ) ≤ (k : ℝ) - 2 := by exact_mod_cast hleft
      right
      have h := hu.1
      nlinarith
    · have hidx : (k : ℝ) + 2 ≤ (l : ℝ) := by exact_mod_cast hright
      left
      have h := hu.2
      nlinarith
  change I.xi ((t - (l : ℝ) * tau β I.Λ m) / tau β I.Λ m) = 0
  apply FluxStructure.xi_eq_zero_outside I
  intro hmem
  rcases hout with hlt | hgt
  · exact (not_le_of_gt hlt) hmem.1
  · exact (not_le_of_gt hgt) hmem.2

/-- On the support of one odd stream cutoff, the summed corrector is exactly
the matching single-mode corrector. -/
theorem chiM_eq_chiMK_of_zetaMK_ne_zero {β : ℝ}
    (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) {k : ℤ}
    (hk : Odd k) (t : ℝ) (x : Vec 2)
    (hzk : I.zetaMK m k t ≠ 0) :
    I.chiM κ m t x = I.chiMK κ m k t x := by
  have htail (l : ℤ) (hl : l ≠ k) :
      I.xiMK m l t • I.chiMK κ m l t x = 0 := by
    by_cases hodd : Odd l
    · have hxi := xiMK_eq_zero_of_zetaMK_ne_zero_of_odd_ne
        I hm hk hodd hl t hzk
      simp [hxi]
    · have hnot1 : l % 4 ≠ 1 := by
        intro hmod
        have hodd' : Odd l := by
          rcases Int.even_or_odd l with heven | hodd'
          · rcases heven with ⟨a, ha⟩
            omega
          · exact hodd'
        exact hodd hodd'
      have hnot3 : l % 4 ≠ 3 := by
        intro hmod
        have hodd' : Odd l := by
          rcases Int.even_or_odd l with heven | hodd'
          · rcases heven with ⟨a, ha⟩
            omega
          · exact hodd'
        exact hodd hodd'
      have hu : uShear β I.Λ m l x = 0 := by
        simp [uShear, hnot1, hnot3]
      simp [Ingredients.chiMK, hu]
  unfold Ingredients.chiM
  rw [tsum_eq_single k htail]
  simp [xiMK_eq_one_of_zetaMK_ne_zero I hm k t hzk]

/-- When an odd mode is active, the stream field sum has only that mode. -/
theorem psiM_eq_single_of_zetaMK_ne_zero {β : ℝ}
    (I : Ingredients β) {m : ℕ} (_hm : 1 ≤ m) {k : ℤ}
    (hk : Odd k) (t : ℝ) (x : Vec 2)
    (hzk : I.zetaMK m k t ≠ 0) :
    I.psiM m t x = I.zetaProd m k t * psi β I.Λ m k x := by
  have htail (l : {l : ℤ // Odd l}) (hl : l ≠ ⟨k, hk⟩) :
      I.zetaProd m l.1 t * psi β I.Λ m l.1 x = 0 := by
    have hne : l.1 ≠ k := by
      intro heq
      apply hl
      exact Subtype.ext heq
    have hz : I.zetaMK m l.1 t = 0 := by
      by_contra hz
      have hτ := Infra.Ingredients.tau_pos I.one_lt_beta I.beta_lt
        I.two_pow_seven_le (m := m)
      have huK := FluxStructure.zetaMK_coord_bound I k t hzk
      have huL := FluxStructure.zetaMK_coord_bound I l.1 t hz
      have hsep := FluxStructure.odd_indices_separated hk l.2 (Ne.symm hne)
      have hshift :
          (t - (l.1 : ℝ) * tau β I.Λ m) / tau β I.Λ m =
            (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m -
              ((l.1 : ℝ) - (k : ℝ)) := by
        field_simp [ne_of_gt hτ]
        ring
      rw [hshift] at huL
      rcases hsep with hleft | hright
      · have hidx : (l.1 : ℝ) ≤ (k : ℝ) - 2 := by exact_mod_cast hleft
        have := huK.1
        have := huL.2
        nlinarith
      · have hidx : (k : ℝ) + 2 ≤ (l.1 : ℝ) := by exact_mod_cast hright
        have := huK.2
        have := huL.1
        nlinarith
    simp [Ingredients.zetaProd, hz]
  unfold Ingredients.psiM
  rw [tsum_eq_single ⟨k, hk⟩ htail]

end AVenhance.Infra.Section3
