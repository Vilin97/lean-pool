/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import LeanPool.ACMax.Counting.HeavyClass
public import LeanPool.ACMax.Counting.V9Discharge

/-!
# Region inequalities for the exact Moore range

The parameter inequalities consumed by the exact non-backtracking argument on
a degree-`3`-separated obstruction at `n ≥ 48`. Notation:
`X = excessX n G`, `h = |V₉ᶜ|` (the heavies `deg ≥ 5`), `v = |V₉|`, `n_g` the giant count.

* `giant_le_two` — the giant census `n_g ≤ 2`, from `hoarding_law` and `giant_excess_bound`.
* `master_dprime` — **MASTER''**: `10·X + 7·h ≤ 4·n − 186`, assembled by `omega` from
  `slots_p_row`, `p_choke_row_unconditional`, `heavy_class_ledger`, `heavy_class_disjoint` and
  `giant_le_two`.  Sharper reach than `master_prime_57` (`n ≥ 48` vs `n ≥ 57`) at the slightly
  weaker constant `−186`, avoiding the credit-4 heavy budget.
* the V₉ 2-core parameter rows the assembly feeds to the girth kill: `v9_card_add_compl`
  (`v = n − h`) and `t9_window` (`X + 3h + 4 ≤ n`, the kill-template positivity).

Everything is `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

@[expose] public section

namespace ACMax

open SimpleGraph Finset

open Classical in
/-- The complement of the tier-9 population `V₉ = {deg ≤ 4}` is exactly the heavies
`{deg ≥ 5}`. -/
theorem v9_compl_eq {n : ℕ} (G : SimpleGraph (Fin n)) :
    (v9Set G)ᶜ = Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v) := by
  ext v
  simp only [Finset.mem_compl, mem_v9Set, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

open Classical in
/-- The number of heavies `h = |V₉ᶜ|` is bounded by the total degree excess `X`. -/
theorem heavy_card_le_excess {n : ℕ} (G : SimpleGraph (Fin n)) :
    (v9Set G)ᶜ.card ≤ excessX n G := by
  rw [v9_compl_eq]; exact heavy_le_excess G

open Classical in
/-- **The giant census `n_g ≤ 2`.**  On a never-firing starved census at `n ≥ 48`, hoarding
(`3X + 32 ≤ n + 3·n_g`) and the giant bound (`n_g·(n − 20) ≤ 9X`) are jointly infeasible for
`n_g ≥ 3`: substituting `n = d + 20`, the two rows force `(n_g − 3)·(d − 28) < 9(n_g − 4)`, which
`nlinarith` refutes.  So at most two giants survive. -/
theorem giant_le_two {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n)) (hn : 48 ≤ n)
    (hm : G.edgeFinset.card = 2 * (n - 2)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hnf : ¬ algConn G ≤ 2)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w) :
    ((hubSet G).filter (fun h => n + 15 < 9 * G.degree h)).card ≤ 2 := by
  have hho := hoarding_law G (by omega) hm h3 hnf hs0
  have hgi := giant_excess_bound G (by omega)
  set ng := ((hubSet G).filter (fun h => n + 15 < 9 * G.degree h)).card with hngdef
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 20 := ⟨n - 20, by omega⟩
  rw [Nat.add_sub_cancel] at hgi
  nlinarith [hgi, hho, hcon, hn]

open Classical in
/-- **Master finite-band inequality.** A degree-`3`-separated obstruction
(`m = 2(n−2)`, `δ ≥ 3`, `hs0`, `¬ algConn ≤ 2`) satisfies `10·X + 7·h ≤ 4·n − 186`
(`X = excessX n G`, `h = |V₉ᶜ|`).  Assembled by `omega`: the slots row forces
`t₄ ≥ 24 + 2X − p − h₆₊ − 4·n_g`; the choke row then gives `17X + p + 200 ≤ 4n + 7·h₆₊ + 28·n_g`;
the ledger (`h + h₆₊ + 3·n_g ≤ X`) and `n_g ≤ 2` collapse this to `10X + 7h + 186 ≤ 4n`.  Reaches
`n ≥ 48` (vs `master_prime_57`'s `n ≥ 57`) without the credit-4 heavy budget. -/
theorem master_dprime {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n)) (hn : 48 ≤ n)
    (hm : G.edgeFinset.card = 2 * (n - 2)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hnf : ¬ algConn G ≤ 2)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w) :
    10 * excessX n G + 7 * (v9Set G)ᶜ.card ≤ 4 * n - 186 := by
  have hsl := slots_p_row G (by omega) hm h3 hnf hs0
  have hpc := p_choke_row_unconditional (by omega) G hm h3 hs0 hnf
  have hled := heavy_class_ledger G (by omega)
  have hdis := heavy_class_disjoint G (by omega)
  have hng := giant_le_two G hn hm h3 hnf hs0
  have hcompl : (v9Set G)ᶜ.card
      = (Finset.univ.filter (fun v : Fin n => 5 ≤ G.degree v)).card := by
    rw [v9_compl_eq]
  omega

open Classical in
/-- **The V₉ size bridge** (`v = n − h`).  `Fin n` partitions as `V₉ ⊔ V₉ᶜ`, so the tier-9
population size and the heavy count sum to `n`. -/
theorem v9_card_add_compl {n : ℕ} (G : SimpleGraph (Fin n)) :
    (v9Set G).card + (v9Set G)ᶜ.card = n := by
  rw [Finset.card_add_card_compl, Fintype.card_fin]

open Classical in
/-- **The kill-template positivity window** (`X + 3h + 4 ≤ n`).  From MASTER'' and `h ≤ X`; its
role is to keep the honest excess `t₉ = n − 4 − X − 3h` non-negative for the girth kill. -/
theorem t9_window {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n)) (hn : 48 ≤ n)
    (hm : G.edgeFinset.card = 2 * (n - 2)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hnf : ¬ algConn G ≤ 2)
    (hs0 : ∀ v w : Fin n, G.degree v = 3 → G.degree w = 3 → ¬G.Adj v w) :
    excessX n G + 3 * (v9Set G)ᶜ.card + 4 ≤ n := by
  have hmaster := master_dprime G hn hm h3 hnf hs0
  have hh := heavy_card_le_excess G
  omega

end ACMax
