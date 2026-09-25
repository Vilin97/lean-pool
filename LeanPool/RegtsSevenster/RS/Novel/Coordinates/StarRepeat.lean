/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.StarPerm

/-!
# Fermionic vanishing of star coordinates

Repeated odd colours kill the star coordinate: the adjacent-swap
inversion count is the both-odd indicator, so a colouring fixed
by an adjacent swap of equal odd colours equals its own negation.
-/

namespace RS

open CategoryTheory Finset

variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))
variable {k ℓ : ℕ}
variable (e : stdSuperPair k ℓ ⟶ P.ω.obj (SkeinObj.mk 1))
variable (e' : P.ω.obj (SkeinObj.mk 1) ⟶ stdSuperPair k ℓ)

/-- The adjacent swap has exactly the both-odd inversion. -/
theorem oddInversions_adjacent {n : ℕ} (i : ℕ)
    (h2 : i + 1 < n) (c : MixedColouring k ℓ n) :
    oddInversions (_root_.Equiv.swap
        (⟨i, by omega⟩ : Fin n) ⟨i + 1, h2⟩) c =
      (if (c ⟨i, by omega⟩).isRight ∧
          (c ⟨i + 1, h2⟩).isRight then 1 else 0) := by
  unfold oddInversions
  -- ═══════ BOTH SWAPPED POSITIONS CARRY ODD COLOURS ═══════
  -- Then the swap is an inversion and the count moves by one;
  -- otherwise the pair contributes nothing and the count is fixed.
  by_cases hodd : (c ⟨i, by omega⟩).isRight ∧
      (c ⟨i + 1, h2⟩).isRight
  · rw [ite_eq_left hodd]
    rw [show (univ.filter (fun p : Fin n × Fin n =>
        p.1 < p.2 ∧ _root_.Equiv.swap
          (⟨i, by omega⟩ : Fin n) ⟨i + 1, h2⟩ p.1 >
          _root_.Equiv.swap
            (⟨i, by omega⟩ : Fin n) ⟨i + 1, h2⟩ p.2 ∧
        (c (_root_.Equiv.swap
          (⟨i, by omega⟩ : Fin n) ⟨i + 1, h2⟩ p.1)).isRight ∧
        (c (_root_.Equiv.swap
          (⟨i, by omega⟩ : Fin n) ⟨i + 1, h2⟩
          p.2)).isRight)) =
      {((⟨i, by omega⟩ : Fin n), (⟨i + 1, h2⟩ : Fin n))}
      from ?_]
    · exact card_singleton _
    ext p
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨hlt, hgt, _, _⟩
      by_cases h1 : p.1 = (⟨i, by omega⟩ : Fin n)
      · by_cases h2' : p.2 = (⟨i + 1, h2⟩ : Fin n)
        · exact Prod.ext_iff.mpr ⟨h1, h2'⟩
        · exfalso
          rw [h1, _root_.Equiv.swap_apply_left] at hgt
          rw [_root_.Equiv.swap_apply_of_ne_of_ne
            (fun hx => by
              rw [h1] at hlt
              exact absurd (hx ▸ hlt) (lt_irrefl _)) h2']
            at hgt
          have hv1 := (Fin.lt_def.mp hgt)
          have hv2 := (Fin.lt_def.mp hlt)
          rw [h1] at hv2
          simp only [] at hv1 hv2
          omega
      · by_cases h2' : p.2 = (⟨i, by omega⟩ : Fin n)
        · exfalso
          rw [h2', _root_.Equiv.swap_apply_left] at hgt
          by_cases h1' : p.1 = (⟨i + 1, h2⟩ : Fin n)
          · rw [h1', _root_.Equiv.swap_apply_right] at hgt
            have hv1 := Fin.lt_def.mp hgt
            have hv2 := Fin.lt_def.mp hlt
            rw [h1', h2'] at hv2
            simp only [] at hv1 hv2
            omega
          · rw [_root_.Equiv.swap_apply_of_ne_of_ne h1 h1']
              at hgt
            have hv1 := Fin.lt_def.mp hgt
            have hv2 := Fin.lt_def.mp hlt
            rw [h2'] at hv2
            simp only [] at hv1 hv2
            omega
        · by_cases h1' : p.1 = (⟨i + 1, h2⟩ : Fin n)
          · exfalso
            rw [h1', _root_.Equiv.swap_apply_right] at hgt
            by_cases h2'' : p.2 = (⟨i + 1, h2⟩ : Fin n)
            · rw [h1', h2''] at hlt
              exact absurd hlt (lt_irrefl _)
            · rw [_root_.Equiv.swap_apply_of_ne_of_ne h2'
                h2''] at hgt
              have hv1 := Fin.lt_def.mp hgt
              have hv2 := Fin.lt_def.mp hlt
              rw [h1'] at hv2
              simp only [] at hv1 hv2
              omega
          · exfalso
            by_cases h2'' : p.2 = (⟨i + 1, h2⟩ : Fin n)
            · rw [h2'', _root_.Equiv.swap_apply_right] at hgt
              rw [_root_.Equiv.swap_apply_of_ne_of_ne h1 h1']
                at hgt
              have hv1 := Fin.lt_def.mp hgt
              have hv2 := Fin.lt_def.mp hlt
              rw [h2''] at hv2
              simp only [] at hv1 hv2
              omega
            · rw [_root_.Equiv.swap_apply_of_ne_of_ne h1 h1',
                _root_.Equiv.swap_apply_of_ne_of_ne h2'
                  h2''] at hgt
              exact absurd hlt (not_lt.mpr (le_of_lt hgt))
    · intro hp
      rw [hp]
      refine ⟨Fin.lt_def.mpr (by
        change i < i + 1; omega), ?_, ?_, ?_⟩
      · rw [_root_.Equiv.swap_apply_left,
          _root_.Equiv.swap_apply_right]
        exact Fin.lt_def.mpr (by
          change i < i + 1; omega)
      · rw [_root_.Equiv.swap_apply_left]
        exact hodd.2
      · rw [_root_.Equiv.swap_apply_right]
        exact hodd.1
  · rw [ite_eq_right hodd]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro p _ ⟨hlt, hgt, ho1, ho2⟩
    refine hodd ?_
    by_cases h1 : p.1 = (⟨i, by omega⟩ : Fin n)
    · by_cases h2' : p.2 = (⟨i + 1, h2⟩ : Fin n)
      · rw [h1, _root_.Equiv.swap_apply_left] at ho1
        rw [h2', _root_.Equiv.swap_apply_right] at ho2
        exact ⟨ho2, ho1⟩
      · exfalso
        rw [h1, _root_.Equiv.swap_apply_left] at hgt
        rw [_root_.Equiv.swap_apply_of_ne_of_ne
          (fun hx => by
            rw [h1] at hlt
            exact absurd (hx ▸ hlt) (lt_irrefl _)) h2']
          at hgt
        have hv1 := Fin.lt_def.mp hgt
        have hv2 := Fin.lt_def.mp hlt
        rw [h1] at hv2
        simp only [] at hv1 hv2
        omega
    · exfalso
      by_cases h2' : p.2 = (⟨i, by omega⟩ : Fin n)
      · rw [h2', _root_.Equiv.swap_apply_left] at hgt
        by_cases h1' : p.1 = (⟨i + 1, h2⟩ : Fin n)
        · rw [h1', _root_.Equiv.swap_apply_right] at hgt
          have hv1 := Fin.lt_def.mp hgt
          have hv2 := Fin.lt_def.mp hlt
          rw [h1', h2'] at hv2
          simp only [] at hv1 hv2
          omega
        · rw [_root_.Equiv.swap_apply_of_ne_of_ne h1 h1']
            at hgt
          have hv1 := Fin.lt_def.mp hgt
          have hv2 := Fin.lt_def.mp hlt
          rw [h2'] at hv2
          simp only [] at hv1 hv2
          omega
      · by_cases h1' : p.1 = (⟨i + 1, h2⟩ : Fin n)
        · rw [h1', _root_.Equiv.swap_apply_right] at hgt
          by_cases h2'' : p.2 = (⟨i + 1, h2⟩ : Fin n)
          · rw [h1', h2''] at hlt
            exact absurd hlt (lt_irrefl _)
          · rw [_root_.Equiv.swap_apply_of_ne_of_ne h2'
              h2''] at hgt
            have hv1 := Fin.lt_def.mp hgt
            have hv2 := Fin.lt_def.mp hlt
            rw [h1'] at hv2
            simp only [] at hv1 hv2
            omega
        · by_cases h2'' : p.2 = (⟨i + 1, h2⟩ : Fin n)
          · rw [h2'', _root_.Equiv.swap_apply_right] at hgt
            rw [_root_.Equiv.swap_apply_of_ne_of_ne h1 h1']
              at hgt
            have hv1 := Fin.lt_def.mp hgt
            have hv2 := Fin.lt_def.mp hlt
            rw [h2''] at hv2
            simp only [] at hv1 hv2
            omega
          · rw [_root_.Equiv.swap_apply_of_ne_of_ne h1 h1',
              _root_.Equiv.swap_apply_of_ne_of_ne h2' h2'']
              at hgt
            exact absurd hlt (not_lt.mpr (le_of_lt hgt))

/-- **Adjacent equal odd colours kill the star coordinate.** -/
theorem starCoord_adjacent_repeat
    (hee' : (e' ≫ e : P.ω.obj (SkeinObj.mk 1) ⟶
      P.ω.obj (SkeinObj.mk 1)) = 𝟙 _)
    (he'e : (e ≫ e' : stdSuperPair k ℓ ⟶ stdSuperPair k ℓ) = 𝟙 _)
    {d : ℕ} (i : ℕ) (h2 : i + 1 < d)
    (c : MixedColouring k ℓ d)
    (hodd : (c ⟨i, by omega⟩).isRight)
    (heq : c ⟨i, by omega⟩ = c ⟨i + 1, h2⟩) :
    starCoord f P e' d c = 0 := by
  have hfix : c ∘ _root_.Equiv.swap
      (⟨i, by omega⟩ : Fin d) ⟨i + 1, h2⟩ = c := by
    funext x
    change c (_root_.Equiv.swap _ _ x) = c x
    by_cases hx1 : x = (⟨i, by omega⟩ : Fin d)
    · rw [hx1, _root_.Equiv.swap_apply_left]
      exact heq.symm
    · by_cases hx2 : x = (⟨i + 1, h2⟩ : Fin d)
      · rw [hx2, _root_.Equiv.swap_apply_right]
        exact heq
      · rw [_root_.Equiv.swap_apply_of_ne_of_ne hx1 hx2]
  have hperm := starCoord_perm f P e e' hee' he'e d
    (_root_.Equiv.swap (⟨i, by omega⟩ : Fin d)
      ⟨i + 1, h2⟩) c
  rw [hfix] at hperm
  rw [oddInversions_adjacent i h2 c] at hperm
  rw [ite_eq_left ⟨hodd, heq ▸ hodd⟩] at hperm
  rw [pow_one] at hperm
  have h2x : starCoord f P e' d c =
      -(starCoord f P e' d c) := by
    rw [neg_one_mul] at hperm
    exact hperm
  exact CharZero.eq_neg_self_iff.mp h2x

/-- **Repeated odd colours kill the star coordinate.** -/
theorem starCoord_repeat_zero
    (hee' : (e' ≫ e : P.ω.obj (SkeinObj.mk 1) ⟶
      P.ω.obj (SkeinObj.mk 1)) = 𝟙 _)
    (he'e : (e ≫ e' : stdSuperPair k ℓ ⟶ stdSuperPair k ℓ) = 𝟙 _)
    {d : ℕ} (c : MixedColouring k ℓ d) (i j : Fin d)
    (hij : i.val < j.val)
    (hodd : (c i).isRight) (heq : c i = c j) :
    starCoord f P e' d c = 0 := by
  obtain ⟨gap, hgap⟩ : ∃ gap, j.val = i.val + 1 + gap :=
    ⟨j.val - i.val - 1, by omega⟩
  revert hgap
  induction gap generalizing c i j with
  | zero =>
    intro hgap
    have hb : i.val + 1 < d := by have := j.isLt; omega
    have hbj : (⟨i.val + 1, hb⟩ : Fin d) = j :=
      Fin.ext (by change i.val + 1 = j.val; omega)
    refine starCoord_adjacent_repeat f P e e' hee' he'e
      i.val hb c
      (show (c ⟨i.val, by omega⟩).isRight from by
        rw [show (⟨i.val, by omega⟩ : Fin d) = i from
          Fin.ext rfl]
        exact hodd) ?_
    rw [show (⟨i.val, by omega⟩ : Fin d) = i from
      Fin.ext rfl]
    rw [hbj]
    exact heq
  | succ gap ih =>
    intro hgap
    -- Swap positions j-1 and j to shorten the gap.
    have hj1 : j.val - 1 + 1 < d := by
      have := j.isLt; omega
    set σ := _root_.Equiv.swap
      (⟨j.val - 1, by omega⟩ : Fin d) ⟨j.val - 1 + 1, hj1⟩
      with hσ
    have hperm := starCoord_perm f P e e' hee' he'e d σ c
    have hc' : starCoord f P e' d (c ∘ σ) = 0 := by
      have hb1 : i.val < j.val - 1 := by omega
      have hb2 : j.val - 1 = i.val + 1 + gap := by omega
      have hb3 : j.val - 1 < d := by
        have := j.isLt; omega
      have hbj : (⟨j.val - 1 + 1, hj1⟩ : Fin d) = j :=
        Fin.ext (by change j.val - 1 + 1 = j.val; omega)
      refine ih (c ∘ σ) i ⟨j.val - 1, hb3⟩ hb1 ?_ ?_ hb2
      · change (c (σ i)).isRight
        rw [show σ i = i from
          _root_.Equiv.swap_apply_of_ne_of_ne
            (Fin.ne_of_val_ne (by
              change i.val ≠ j.val - 1; omega))
            (Fin.ne_of_val_ne (by
              change i.val ≠ j.val - 1 + 1; omega))]
        exact hodd
      · change c (σ i) = c (σ ⟨j.val - 1, by omega⟩)
        rw [show σ i = i from
          _root_.Equiv.swap_apply_of_ne_of_ne
            (Fin.ne_of_val_ne (by
              change i.val ≠ j.val - 1; omega))
            (Fin.ne_of_val_ne (by
              change i.val ≠ j.val - 1 + 1; omega))]
        rw [show σ ⟨j.val - 1, by
            have := j.isLt; omega⟩ =
          ⟨j.val - 1 + 1, hj1⟩ from
          _root_.Equiv.swap_apply_left _ _]
        rw [hbj]
        exact heq
    rw [hc'] at hperm
    exact (mul_eq_zero.mp hperm.symm).resolve_left
      (pow_ne_zero _ (by norm_num))

end RS
