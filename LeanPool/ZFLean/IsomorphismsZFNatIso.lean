/-
Copyright (c) 2026 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/

import LeanPool.ZFLean.Isomorphisms

/-!
# LeanPool.ZFLean.IsomorphismsZFNatIso

Imported Lean Pool material for `LeanPool.ZFLean.IsomorphismsZFNatIso`.
-/

namespace ZFSet

namespace ZFNat

open Classical in
/-- The map identifying `k` with `(k + 1) \ {ℓ}` for `ℓ ∈ k + 1`. -/
noncomputable abbrev deletePointIsoMap (k : ZFNat) (ℓ : ZFSet) : ZFSet :=
  ZFSet.prod ↑k (↑(k+1) \ {ℓ}) |>.sep fun xy ↦
    let x := xy.π₁
    let y := xy.π₂
    if x ∈ ℓ then x = y else y = insert x x

@[zfun]
theorem deletePointIsoMap_isFunc {k : ZFNat} {ℓ : ZFSet} :
    IsFunc ↑k (↑(k+1) \ {ℓ}) (deletePointIsoMap k ℓ) := by
  classical
  dsimp [deletePointIsoMap]
  and_intros
  · exact sep_subset_self
  · intro x x_mem_k
    simp only [mem_sep, mem_prod, mem_sdiff, mem_singleton, pair_inj,
      exists_eq_right_right', π₁_pair, π₂_pair]
    split_ifs with x_mem_ℓ
    · use x
      and_intros <;> beta_reduce
      · exact x_mem_k
      · rw [add_one_eq_succ, succ, mem_insert_iff]
        right
        exact x_mem_k
      · rintro rfl
        nomatch mem_irrefl _ x_mem_ℓ
      · rfl
      · rintro _ ⟨_, rfl⟩
        rfl
    · use (insert x x)
      and_intros <;> beta_reduce
      · exact x_mem_k
      · rw [add_one_eq_succ, succ, mem_insert_iff]
        have hx : x ∈ Nat := mem_Nat_of_mem_mem_Nat k.prop x_mem_k
        suffices (⟨x, hx⟩ + 1 : ZFNat) = k ∨ (⟨x, hx⟩ + 1 : ZFNat) < k by
          rcases this with rfl | h
          · left
            rw [add_one_eq_succ, succ]
          · right
            rw [add_one_eq_succ, succ] at h
            exact h
        symm
        change (⟨x, hx⟩ + 1 : ZFNat) ≤ k
        change ⟨x, hx⟩ < k at x_mem_k
        rw [lt_le_iff, ←add_one_eq_succ, add_comm, add_comm k, add_lt_add_iff_left]
        exact x_mem_k
      · rintro rfl
        rw [mem_insert_iff, not_or] at x_mem_ℓ
        nomatch x_mem_ℓ.1 rfl
      · rfl
      · rintro _ ⟨_, rfl⟩
        rfl

theorem deletePointIsoMap_bijective {k : ZFNat} {ℓ : ZFSet}
    (ℓ_mem_m : ℓ ∈ (↑(k + 1) : ZFSet)) :
    (deletePointIsoMap k ℓ).IsBijective deletePointIsoMap_isFunc := by
  classical
  dsimp [deletePointIsoMap]
  and_intros
  · intro x y z hz hy hz g_xz g_yz
    simp only [mem_sep, mem_prod, mem_sdiff, mem_singleton, pair_inj,
      exists_eq_right_right', π₁_pair, π₂_pair] at g_xz g_yz
    obtain ⟨⟨mem_x_k, mem_z_succ_k, z_ne_ℓ⟩, z_eq⟩ := g_xz
    obtain ⟨⟨mem_y_k, -, -⟩, z_eq'⟩ := g_yz
    have z_Nat : z ∈ Nat := mem_Nat_of_mem_mem_Nat (k.succ.prop) (by
      rwa [add_one_eq_succ] at mem_z_succ_k)
    have x_Nat : x ∈ Nat := mem_Nat_of_mem_mem_Nat (k.prop) mem_x_k
    have y_Nat : y ∈ Nat := mem_Nat_of_mem_mem_Nat (k.prop) hy
    have ℓ_Nat : ℓ ∈ Nat := mem_Nat_of_mem_mem_Nat (k.succ.prop) (by
      rwa [add_one_eq_succ] at ℓ_mem_m)
    let Z : ZFNat := ⟨z, z_Nat⟩
    let X : ZFNat := ⟨x, x_Nat⟩
    let Y : ZFNat := ⟨y, y_Nat⟩
    let L : ZFNat := ⟨ℓ, ℓ_Nat⟩
    split_ifs at z_eq z_eq' with x_mem_ℓ y_mem_ℓ y_lt_ℓ
    · subst x y
      rfl
    · subst x
      have Z_eq_succ_Y : Z = Y + 1 := by
        rw [add_one_eq_succ, succ, Subtype.ext_iff]
        exact z_eq'
      change Z < L at x_mem_ℓ
      change ¬ Y < L at y_mem_ℓ
      rw [not_lt] at y_mem_ℓ
      obtain L_lt_Y | L_eq_Y := y_mem_ℓ
      · have := lt_trans x_mem_ℓ L_lt_Y
        rw [Z_eq_succ_Y] at this
        absurd this
        rw [not_lt, add_one_eq_succ]
        exact le_succ
      · rw [L_eq_Y, Z_eq_succ_Y] at x_mem_ℓ
        absurd x_mem_ℓ
        rw [not_lt, add_one_eq_succ]
        exact le_succ
    · subst y
      have Z_eq_succ_X : Z = X + 1 := by
        rw [add_one_eq_succ, succ, Subtype.ext_iff]
        exact z_eq
      change ¬ X < L at x_mem_ℓ
      change Z < L at y_lt_ℓ
      rw [not_lt] at x_mem_ℓ
      obtain L_lt_X | L_eq_X := x_mem_ℓ
      · have := lt_trans y_lt_ℓ L_lt_X
        rw [Z_eq_succ_X] at this
        absurd this
        rw [not_lt, add_one_eq_succ]
        exact le_succ
      · rw [L_eq_X, Z_eq_succ_X] at y_lt_ℓ
        absurd y_lt_ℓ
        rw [not_lt, add_one_eq_succ]
        exact le_succ
    · apply succ_inj_aux'
      rw [←z_eq, ←z_eq']
  · intro y hy
    have y_Nat : y ∈ Nat := by
      apply mem_Nat_of_mem_mem_Nat (k.succ.prop)
      rw [add_one_eq_succ, mem_sdiff] at hy
      exact hy.1
    have ℓ_Nat : ℓ ∈ Nat := mem_Nat_of_mem_mem_Nat (k.succ.prop) (by
      rwa [add_one_eq_succ] at ℓ_mem_m)
    let Y : ZFNat := ⟨y, y_Nat⟩
    let L : ZFNat := ⟨ℓ, ℓ_Nat⟩
    simp only [add_one_eq_succ, succ, mem_insert_iff, mem_sdiff, mem_singleton] at hy
    obtain ⟨rfl | y_mem_k, y_ne_ℓ⟩ := hy
    · have ℓ_Nat : ℓ ∈ Nat := mem_Nat_of_mem_mem_Nat (k.succ.prop) (by
        rwa [add_one_eq_succ] at ℓ_mem_m)
      let L : ZFNat := ⟨ℓ, ℓ_Nat⟩
      change L < k + 1 at ℓ_mem_m
      rw [add_one_eq_succ, ←lt_le_iff] at ℓ_mem_m
      rcases ℓ_mem_m with L_lt_k | L_eq_k
      · have := ZFNat.not_zero_imp_succ (n := k) ?_
        · obtain ⟨s, rfl⟩ := this
          use s, lt_succ
          simp only [mem_sep, pair_mem_prod, mem_sdiff, mem_singleton, π₁_pair, π₂_pair]
          and_intros
          · exact lt_succ
          · rw [add_one_eq_succ]
            exact lt_succ
          · rintro rfl
            contradiction
          · rw [←lt_le_iff] at L_lt_k
            conv =>
                enter [1]
                change s < L
            rcases L_lt_k with L_lt_s | rfl
            · rw [ite_cond_eq_false (h := eq_false (nomatch lt_irrefl <| lt_trans · L_lt_s))]
              rfl
            · rw [ite_cond_eq_false (h := eq_false lt_irrefl)]
              rfl
        · rintro rfl
          nomatch not_lt_zero L_lt_k
      · nomatch (Subtype.coe_ne_coe.mp y_ne_ℓ) L_eq_k.symm
    · by_cases y_lt_ℓ : y ∈ ℓ
      · change Y < L at y_lt_ℓ
        use y, y_mem_k
        simp only [mem_sep, mem_prod, mem_sdiff, mem_singleton, pair_inj,
          exists_eq_right_right', π₁_pair, π₂_pair]
        split_ifs
        · and_intros
          · exact y_mem_k
          · change Y < k + 1
            trans L
            · exact y_lt_ℓ
            · exact ℓ_mem_m
          · exact y_ne_ℓ
          · trivial
        · contradiction
      · change ¬ Y < L at y_lt_ℓ
        change Y < k at y_mem_k
        rw [not_lt] at y_lt_ℓ
        rw [←ne_eq, ne_comm, ne_eq] at y_ne_ℓ
        have := ZFNat.not_zero_imp_succ (n := Y) ?_
        · obtain ⟨s, Y_eq⟩ := this
          use s
          and_intros
          · change s < k
            rw [Y_eq] at y_mem_k
            trans s.succ
            · exact lt_succ
            · exact y_mem_k
          · rw [Y_eq] at y_mem_k y_lt_ℓ
            unfold Y at Y_eq
            rw [succ, Subtype.ext_iff] at Y_eq
            dsimp at Y_eq
            subst y
            replace y_ne_ℓ : ¬ L = s.succ := by
              intro eq
              unfold L at eq
              rw [succ, Subtype.ext_iff] at eq
              dsimp at eq
              subst ℓ
              nomatch y_ne_ℓ
            rcases y_lt_ℓ with L_lt_s | L_eq_s
            · rw [← lt_le_iff] at L_lt_s
              rcases L_lt_s with L_lt_s | L_eq_s
              · rw [mem_sep, pair_mem_prod, π₁_pair, π₂_pair]
                and_intros
                · change s < k
                  exact lt_of_succ_lt y_mem_k
                · rw [mem_sdiff, mem_singleton]
                  and_intros
                  · change s.succ < k + 1
                    rw [add_one_eq_succ, ←succ_mono]
                    exact lt_of_succ_lt y_mem_k
                  · intro contr
                    replace contr : L = s.succ := by
                      rw [succ, Subtype.ext_iff]
                      exact contr.symm
                    contradiction
                · conv =>
                    enter [1]
                    change s < L
                  rw [ite_cond_eq_false
                    (h := eq_false (nomatch lt_irrefl <| lt_trans · L_lt_s))]
              · subst s
                rw [mem_sep, pair_mem_prod, π₁_pair, π₂_pair]
                and_intros
                · change L < k
                  exact lt_of_succ_lt y_mem_k
                · rw [mem_sdiff, mem_singleton]
                  and_intros
                  · change L.succ < k + 1
                    rw [add_one_eq_succ, ←succ_mono]
                    exact lt_of_succ_lt y_mem_k
                  · intro contr
                    replace contr : L = L.succ := by
                      rw [succ, Subtype.ext_iff]
                      exact contr.symm
                    contradiction
                · conv =>
                    enter [1]
                    change L < L
                  rw [ite_cond_eq_false (h := eq_false lt_irrefl)]
            · contradiction
        · intro eq_zero
          have := Or.resolve_right y_lt_ℓ (Subtype.coe_ne_coe.mp y_ne_ℓ)
          rw [eq_zero] at this
          nomatch ZFNat.not_lt_zero this

theorem isIso_delete_singleton {k : ZFNat} {ℓ : ZFSet} (ℓ_mem_m : ℓ ∈ (↑(k + 1) : ZFSet)) :
    ↑k ≅ᶻ (↑(k + 1) \ {ℓ}) := by
  use deletePointIsoMap k ℓ, deletePointIsoMap_isFunc
  exact deletePointIsoMap_bijective ℓ_mem_m

/-- Imported ZFLean declaration. -/
theorem iso_eq_iff_proof {n m : ZFNat} : ↑n ≅ᶻ ↑m ↔ n = m where
  mp := by classical
    intro iso
    induction n generalizing m with
    | zero =>
      obtain ⟨bij, isfunc, isbij⟩ := iso
      ext z
      simp_rw [ZFNat.natZero_eq, notMem_empty, false_iff]
      intro contr
      obtain ⟨x, contr, _⟩ := isbij.2 z contr
      nomatch notMem_empty x contr
    | succ n ih =>
      obtain ⟨f, isfunc, bij⟩ := iso
      obtain ⟨ℓ, hℓ, ℓ_unq⟩ := isfunc.2 ↑n <| add_one_eq_succ ▸ lt_succ
      have ℓ_mem_m := isfunc.1 hℓ |> pair_mem_prod.mp |>.2
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := by
        simp_rw [ZFNat.add_one_eq_succ]
        apply ZFNat.not_zero_imp_succ
        rintro rfl
        nomatch notMem_empty _ ℓ_mem_m
      rw [add_right_cancel]
      apply ih
      let f' := ZFSet.prod ↑n (↑(k+1) \ {ℓ}) |>.sep (· ∈ f)
      have : IsFunc ↑n (↑(k+1) \ {ℓ}) f' := by
        and_intros
        · exact sep_subset_self
        · intro z zn
          have : z ∈ (↑(n+1) : ZFSet) := by
            rw [add_one_eq_succ, ZFNat.succ, mem_insert_iff]
            right
            exact zn
          obtain ⟨y, hy, y_unq⟩ := isfunc.2 z this
          use y
          and_intros <;> beta_reduce
          · rw [mem_sep, pair_mem_prod]
            and_intros
            · exact zn
            · rw [mem_sdiff, mem_singleton]
              and_intros
              · exact isfunc.1 hy |> pair_mem_prod.mp |>.2
              · rintro ⟨⟩
                rw [bij.1 ↑n z ℓ _ this ℓ_mem_m hℓ hy] at zn
                · nomatch mem_irrefl _ zn
                · rw [add_one_eq_succ]
                  exact lt_succ
            · exact hy
          · intro w hzw
            rw [mem_sep, pair_mem_prod, mem_sdiff, mem_singleton] at hzw
            exact y_unq w hzw.2
      have bij' : IsBijective f' this := by
        rw [bijective_exists1_iff]
        intro y hy
        rw [mem_sdiff, add_one_eq_succ, mem_singleton, succ, mem_insert_iff] at hy
        obtain ⟨rfl | y_mem_k, y_ne_ℓ⟩ := hy
        · rw [bijective_exists1_iff] at bij
          have := bij k ?_
          · obtain ⟨x, ⟨x_mem_succ_n, x_k_f⟩, x_unq⟩ := this
            use x
            rw [add_one_eq_succ, succ, mem_insert_iff] at x_mem_succ_n
            rcases x_mem_succ_n with rfl | x_mem_n
            · nomatch y_ne_ℓ <| isfunc.2 _ (by
                rw [add_one_eq_succ]; exact lt_succ) |>.unique x_k_f hℓ
            · and_intros <;> beta_reduce
              · exact x_mem_n
              · rw [mem_sep, pair_mem_prod, mem_sdiff, mem_singleton]
                and_intros
                · exact x_mem_n
                · rw [add_one_eq_succ]
                  exact lt_succ
                · exact y_ne_ℓ
                · exact x_k_f
              · rintro y ⟨yn, y_k_f⟩
                rw [mem_sep, pair_mem_prod, mem_sdiff, mem_singleton] at y_k_f
                apply bij k (by rw [add_one_eq_succ]; exact lt_succ) |>.unique
                · and_intros
                  · rw [add_one_eq_succ, succ, mem_insert_iff]
                    right
                    exact y_k_f.1.1
                  · exact y_k_f.2
                · and_intros
                  · rw [add_one_eq_succ, succ, mem_insert_iff]
                    right
                    exact x_mem_n
                  · exact x_k_f
          · rw [add_one_eq_succ]
            exact lt_succ
        · rw [bijective_exists1_iff] at bij
          have := bij y ?_
          · obtain ⟨x, ⟨x_mem_succ_n, x_k_f⟩, x_unq⟩ := this
            use x
            rw [add_one_eq_succ, succ, mem_insert_iff] at x_mem_succ_n
            rcases x_mem_succ_n with rfl | x_mem_n
            · nomatch y_ne_ℓ <| isfunc.2 _ (by
                rw [add_one_eq_succ]; exact lt_succ) |>.unique x_k_f hℓ
            · and_intros <;> beta_reduce
              · exact x_mem_n
              · rw [mem_sep, pair_mem_prod, mem_sdiff, mem_singleton]
                and_intros
                · exact x_mem_n
                · rw [add_one_eq_succ, succ, mem_insert_iff]
                  right
                  exact y_mem_k
                · exact y_ne_ℓ
                · exact x_k_f
              · rintro z ⟨zn, z_k_f⟩
                rw [mem_sep, pair_mem_prod, mem_sdiff, mem_singleton] at z_k_f
                apply bij y ?_ |>.unique
                · and_intros
                  · rw [add_one_eq_succ, succ, mem_insert_iff]
                    right
                    exact z_k_f.1.1
                  · exact z_k_f.2
                · and_intros
                  · rw [add_one_eq_succ, succ, mem_insert_iff]
                    right
                    exact x_mem_n
                  · exact x_k_f
                · rw [add_one_eq_succ, succ, mem_insert_iff]
                  right
                  exact y_mem_k
          · rw [add_one_eq_succ, succ, mem_insert_iff]
            right
            exact y_mem_k
      have k_iso : ↑k ≅ᶻ (↑(k+1) \ {ℓ}) := isIso_delete_singleton ℓ_mem_m
      trans ↑(k+1) \ {ℓ}
      · use f', this
      · apply ZFSet.isIso_symm
        exact k_iso
  mpr := by
    rintro rfl
    apply isIso_refl

theorem _root_.ZFSet.ZFNat.iso_eq_iff {n m : ZFNat} : ↑n ≅ᶻ ↑m ↔ n = m :=
  iso_eq_iff_proof

end ZFNat

end ZFSet
