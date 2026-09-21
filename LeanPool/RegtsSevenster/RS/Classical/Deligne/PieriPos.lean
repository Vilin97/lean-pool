/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.HookZero
import LeanPool.RegtsSevenster.RS.Classical.Deligne.NewtonConv
import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperValues

/-!
# Pieri rules and hook positivity for Schur specialisations

Three layers on top of the additive splitting of Schur
specialisations.

1. **Linear independence**: the Schur specialisations of the shapes
   of one size, as functions of the scalar sequence, are linearly
   independent; a graded refinement separates sizes through the
   homogeneity of the specialisation under `t c ↦ z^c · t c`.
2. **Pieri rules**: the Schur specialisation of a diagram at
   `t + superPS 1 0` (one extra even variable) is the sum of the
   Schur specialisations of its horizontal-strip sub-diagrams, by a
   unipotent row operation on the Jacobi–Trudi matrix followed by a
   multilinear expansion of the rows; at `t + superPS 0 1` (one
   extra odd variable) the analogous identity over vertical-strip
   sub-diagrams follows from a direct two-term expansion of the
   rows.  Extracting coefficients through the graded linear
   independence yields the induction-multiplicity Pieri rules
   `indMult lam μ (rowShape m)` and `indMult lam μ (colShape m)`.
3. **Hook positivity**: building a diagram avoiding the cell
   `(p, q)` by horizontal strips in the first `p` rows and vertical
   strips in the first `q` columns shows that its Schur
   specialisation at `superPS p q` is a positive natural number —
   the nonvanishing direction of Deligne 1.9 on the character side.
-/

namespace RS

open Finset Matrix

/-! ### Linear independence of Schur specialisations at a fixed size

The hypothesis pairs the class function
`π ↦ ∑ μ, c μ · jtChar μ (recast π)` to zero against every completed
cycle product; the Frobenius determination of class functions forces
the character combination to vanish, and orthonormality of the
recast characters extracts each coefficient. -/

/-- **Linear independence of Schur specialisations at a fixed
size**: a coefficient family on the shapes of size `n` whose
weighted sum of Schur specialisations vanishes at every scalar
sequence is identically zero. -/
theorem diagramSchur_lin_indep {n : ℕ} (c : Shape n → ℂ)
    (h : ∀ t : ℕ → ℂ, ∑ μ : Shape n, c μ * diagramSchur μ.val t = 0) :
    ∀ μ, c μ = 0 := by
  have hfac : ((n.factorial : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  -- the character combination attached to the coefficients
  set δ : Equiv.Perm (Fin n) → ℂ := fun π =>
    ∑ μ : Shape n, c μ * jtChar μ.val (permCast μ.prop.symm π) with hδ
  have hconj : ∀ g k : Equiv.Perm (Fin n), δ (k * g * k⁻¹) = δ g := by
    intro g k
    rw [hδ]
    refine Finset.sum_congr rfl fun μ _ => ?_
    congr 1
    rw [permCast_mul, permCast_mul, permCast_inv]
    exact jtChar_conj μ.val (permCast μ.prop.symm k)
      (permCast μ.prop.symm g)
  have hvan : ∀ t : ℕ → ℂ,
      ∑ π : Equiv.Perm (Fin n), δ π * cycleProd t π = 0 := by
    intro t
    rw [Finset.sum_congr rfl fun π _ => by rw [hδ, Finset.sum_mul]]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun μ _ => show
        (∑ π : Equiv.Perm (Fin n),
          c μ * jtChar μ.val (permCast μ.prop.symm π) * cycleProd t π) =
        c μ * ((n.factorial : ℂ) * diagramSchur μ.val t) from by
      rw [show ((n.factorial : ℂ)) * diagramSchur μ.val t =
          ∑ π : Equiv.Perm (Fin n),
            jtChar μ.val (permCast μ.prop.symm π) * cycleFun t π from by
        rw [← jtChar_shape_frobenius μ t, ← mul_assoc,
          mul_inv_cancel₀ hfac, one_mul]]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun π _ => ?_
      rw [cycleFun_eq_cycleProd]
      ring]
    rw [Finset.sum_congr rfl fun μ _ =>
      mul_left_comm (c μ) ((n.factorial : ℂ)) (diagramSchur μ.val t)]
    rw [← Finset.mul_sum, h t, mul_zero]
  have hδ0 : ∀ π, δ π = 0 :=
    classFun_eq_zero_of_cycleProd δ hconj hvan
  intro ν
  have hnorm : ((n.factorial : ℂ))⁻¹ * ∑ π : Equiv.Perm (Fin n),
      δ π * jtChar ν.val (permCast ν.prop.symm π) = c ν := by
    rw [Finset.sum_congr rfl fun π _ => by rw [hδ, Finset.sum_mul]]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun μ _ => show
        (∑ π : Equiv.Perm (Fin n),
          c μ * jtChar μ.val (permCast μ.prop.symm π) *
            jtChar ν.val (permCast ν.prop.symm π)) =
        c μ * ∑ π : Equiv.Perm (Fin n),
          jtChar μ.val (permCast μ.prop.symm π) *
            jtChar ν.val (permCast ν.prop.symm π) from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun π _ => by ring]
    rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun μ _ =>
      mul_left_comm ((n.factorial : ℂ))⁻¹ (c μ) _]
    rw [Finset.sum_eq_single ν
      (fun μ _ hμν => by rw [jtChar_orthogonal μ ν hμν, mul_zero])
      (fun hν => absurd (Finset.mem_univ ν) hν)]
    rw [jtChar_shape_orthonormal ν, mul_one]
  rw [← hnorm]
  rw [Finset.sum_congr rfl fun π _ => by rw [hδ0 π, zero_mul]]
  rw [Finset.sum_const_zero, mul_zero]

/-! ### Homogeneity and the graded refinement -/

private theorem multiset_prod_map_pow (z : ℂ) (m : Multiset ℕ) :
    (m.map fun c => z ^ c).prod = z ^ m.sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, ih,
        Multiset.sum_cons, pow_add]

/-- The completed cycle product scales by `z^n` under the
substitution `t c ↦ z^c · t c`. -/
theorem cycleFun_smul_pow {n : ℕ} (z : ℂ) (t : ℕ → ℂ)
    (π : Equiv.Perm (Fin n)) :
    cycleFun (fun c => z ^ c * t c) π = z ^ n * cycleFun t π := by
  have hle : π.cycleType.sum ≤ n := by
    have h := Equiv.Perm.sum_cycleType_le π
    rwa [Fintype.card_fin] at h
  have hpow : z ^ π.cycleType.sum * z ^ (n - π.cycleType.sum) =
      z ^ n := by
    rw [← pow_add]
    congr 1
    omega
  simp only [cycleFun]
  rw [Multiset.prod_map_mul, multiset_prod_map_pow, pow_one, mul_pow]
  linear_combination ((π.cycleType.map t).prod *
    (t 1) ^ (n - π.cycleType.sum)) * hpow

/-- **Homogeneity of the Schur specialisation**: substituting
`t c ↦ z^c · t c` scales the value of a diagram by `z` to its
number of cells. -/
theorem diagramSchur_smul_pow (mu : YoungDiagram) (t : ℕ → ℂ)
    (z : ℂ) :
    diagramSchur mu (fun c => z ^ c * t c) =
      z ^ mu.card * diagramSchur mu t := by
  show diagramSchur (⟨mu, rfl⟩ : Shape mu.card).val
      (fun c => z ^ c * t c) =
    z ^ mu.card * diagramSchur (⟨mu, rfl⟩ : Shape mu.card).val t
  rw [← jtChar_shape_frobenius (⟨mu, rfl⟩ : Shape mu.card)
    (fun c => z ^ c * t c),
    ← jtChar_shape_frobenius (⟨mu, rfl⟩ : Shape mu.card) t]
  rw [Finset.sum_congr rfl fun π _ => by
    rw [cycleFun_smul_pow z t π,
      mul_left_comm _ (z ^ mu.card) (cycleFun t π)]]
  rw [← Finset.mul_sum, mul_left_comm]

/-- **Graded linear independence**: a size-indexed coefficient
family on the shapes of sizes `≤ n` whose combined Schur pairing
vanishes at every scalar sequence vanishes in every graded piece —
homogeneity separates the sizes, and the fixed-size independence
finishes. -/
theorem diagramSchur_graded_lin_indep {n : ℕ}
    (c : (k : ℕ) → Shape k → ℂ)
    (h : ∀ t : ℕ → ℂ, ∑ k ∈ Finset.range (n + 1), ∑ κ : Shape k,
      c k κ * diagramSchur κ.val t = 0) :
    ∀ k, k ≤ n → ∀ κ : Shape k, c k κ = 0 := by
  have hgrade : ∀ (t : ℕ → ℂ) (k), k ≤ n →
      ∑ κ : Shape k, c k κ * diagramSchur κ.val t = 0 := by
    intro t k hk
    set p : Polynomial ℂ := ∑ j ∈ Finset.range (n + 1),
      Polynomial.C (∑ κ : Shape j, c j κ * diagramSchur κ.val t) *
        Polynomial.X ^ j with hp
    have heval : ∀ z : ℂ, p.eval z = 0 := by
      intro z
      rw [hp, Polynomial.eval_finsetSum]
      rw [Finset.sum_congr rfl fun j _ => by
        rw [Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_X]]
      have hz := h (fun c => z ^ c * t c)
      rw [Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl
        fun κ _ => by
          rw [diagramSchur_smul_pow κ.val t z, κ.prop])] at hz
      rw [← hz]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun κ _ => by ring
    have hp0 : p = 0 := Polynomial.zero_of_eval_zero p heval
    have hcoeff := congrArg (fun q : Polynomial ℂ => q.coeff k) hp0
    rw [hp, Polynomial.finsetSum_coeff, Polynomial.coeff_zero]
      at hcoeff
    rw [Finset.sum_congr rfl (fun j _ => by
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow])] at hcoeff
    rw [Finset.sum_congr rfl (fun j _ => show
        (∑ κ : Shape j, c j κ * diagramSchur κ.val t) *
          (if k = j then (1 : ℂ) else 0) =
        if j = k then (∑ κ : Shape j, c j κ * diagramSchur κ.val t)
          else 0 from by
      by_cases hjk : j = k
      · rw [if_pos hjk, if_pos hjk.symm, mul_one]
      · rw [if_neg hjk, if_neg (fun hkj => hjk hkj.symm), mul_zero])]
      at hcoeff
    rw [Finset.sum_ite_eq' (Finset.range (n + 1)) k
      (fun j => ∑ κ : Shape j, c j κ * diagramSchur κ.val t),
      if_pos (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))] at hcoeff
    exact hcoeff
  intro k hk
  exact diagramSchur_lin_indep (c k) (fun t => hgrade t k hk)

/-! ### Row-length utilities for Young diagrams -/

/-- Rows inside the row-length list are nonempty. -/
theorem rowLen_pos_of_lt_length (mu : YoungDiagram) {i : ℕ}
    (h : i < mu.rowLens.length) : 0 < mu.rowLen i := by
  rw [YoungDiagram.length_rowLens] at h
  exact YoungDiagram.mem_iff_lt_rowLen.mp
    (YoungDiagram.mem_iff_lt_colLen.mpr h)

/-- A membership description of every row pins the row length. -/
private theorem rowLen_eq_of_forall {mu : YoungDiagram} {i L : ℕ}
    (h : ∀ j, (i, j) ∈ mu ↔ j < L) : mu.rowLen i = L := by
  rcases Nat.eq_zero_or_pos L with h0 | hpos
  · subst h0
    by_contra hne
    have hmem := YoungDiagram.mem_iff_lt_rowLen.mpr
      (Nat.pos_of_ne_zero hne : 0 < mu.rowLen i)
    exact absurd ((h 0).mp hmem) (by omega)
  · have h1 : L - 1 < mu.rowLen i :=
      YoungDiagram.mem_iff_lt_rowLen.mp ((h (L - 1)).mpr (by omega))
    have h2 : ¬ L < mu.rowLen i := fun hlt =>
      absurd ((h L).mp (YoungDiagram.mem_iff_lt_rowLen.mpr hlt))
        (by omega)
    omega

/-- Diagrams with the same row lengths are equal. -/
theorem ext_of_rowLen_eq {mu nu : YoungDiagram}
    (h : ∀ i, mu.rowLen i = nu.rowLen i) : mu = nu := by
  refine YoungDiagram.ext ?_
  refine Finset.ext fun c => ?_
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells]
  obtain ⟨i, j⟩ := c
  rw [YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_rowLen,
    h i]

/-- Containment of diagrams is monotone on column lengths. -/
theorem colLen_le_of_le {mu lam : YoungDiagram} (h : mu ≤ lam)
    (j : ℕ) : mu.colLen j ≤ lam.colLen j := by
  rcases Nat.eq_zero_or_pos (mu.colLen j) with h0 | hpos
  · omega
  · have hmem : (mu.colLen j - 1, j) ∈ mu :=
      YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    have hmem' : (mu.colLen j - 1, j) ∈ lam :=
      (YoungDiagram.mem_cells _).mp
        (YoungDiagram.cells_subset_iff.mpr h
          ((YoungDiagram.mem_cells _).mpr hmem))
    have := YoungDiagram.mem_iff_lt_colLen.mp hmem'
    omega

/-- Rowwise domination of row lengths gives containment. -/
theorem le_of_rowLen_le {mu lam : YoungDiagram}
    (h : ∀ i, mu.rowLen i ≤ lam.rowLen i) : mu ≤ lam := by
  rw [← YoungDiagram.cells_subset_iff]
  intro c hc
  rw [YoungDiagram.mem_cells] at hc ⊢
  obtain ⟨i, j⟩ := c
  rw [YoungDiagram.mem_iff_lt_rowLen] at hc ⊢
  exact lt_of_lt_of_le hc (h i)

private theorem list_sum_map_range (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  rw [Finset.sum_eq_multiset_sum, Finset.range_val,
    ← Multiset.coe_range, Multiset.map_coe, Multiset.sum_coe]

/-- The cell count as a row-length sum over any range covering the
column length. -/
theorem card_eq_sum_range_rowLen (mu : YoungDiagram) (N : ℕ)
    (hN : mu.colLen 0 ≤ N) :
    mu.card = ∑ i ∈ Finset.range N, mu.rowLen i := by
  rw [card_eq_sum_rowLens,
    show mu.rowLens = (List.range (mu.colLen 0)).map mu.rowLen
      from rfl,
    list_sum_map_range]
  refine Finset.sum_subset (Finset.range_subset_range.mpr hN)
    fun i _ hi => ?_
  rw [Finset.mem_range, not_lt] at hi
  exact rowLen_eq_zero_of_ge mu
    (by rw [YoungDiagram.length_rowLens]; omega)

/-! ### Diagrams from finite antitone row-length vectors -/

/-- Adjacent decrease of a vector on `Fin ℓ` implies full
antitonicity. -/
private theorem fin_antitone_of_adjacent {ℓ : ℕ} {r : Fin ℓ → ℕ}
    (h : ∀ (i : ℕ) (hi : i + 1 < ℓ),
      r ⟨i + 1, hi⟩ ≤ r ⟨i, Nat.lt_of_succ_lt hi⟩) :
    ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i := by
  suffices hd : ∀ (d : ℕ) (i j : Fin ℓ), (j : ℕ) = (i : ℕ) + d →
      r j ≤ r i by
    intro i j hij
    exact hd ((j : ℕ) - (i : ℕ)) i j (by omega)
  intro d
  induction d with
  | zero =>
      intro i j hij
      rw [show j = i from Fin.ext (by omega)]
  | succ e ih =>
      intro i j hij
      have hlt : (i : ℕ) + e + 1 < ℓ := by
        have := j.isLt
        omega
      have h1 : r j ≤ r ⟨(i : ℕ) + e, Nat.lt_of_succ_lt hlt⟩ := by
        rw [show j = ⟨(i : ℕ) + e + 1, hlt⟩ from Fin.ext (by omega)]
        exact h ((i : ℕ) + e) hlt
      exact le_trans h1 (ih i ⟨(i : ℕ) + e, Nat.lt_of_succ_lt hlt⟩
        rfl)

open scoped Classical in
/-- **The diagram of an antitone row-length vector** on `Fin ℓ`:
the Young diagram whose row `i < ℓ` has length `r i` (and `⊥` on
non-antitone junk input). -/
noncomputable def stripDiagram {ℓ : ℕ} (r : Fin ℓ → ℕ) :
    YoungDiagram :=
  if h : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i then
    YoungDiagram.ofRowLens (List.ofFn r)
      (List.sortedGE_iff_pairwise.mpr (List.pairwise_ofFn.mpr
        fun i j hij => h i j (le_of_lt hij)))
  else ⊥

/-- Membership in the diagram of a row-length vector. -/
theorem stripDiagram_mem {ℓ : ℕ} {r : Fin ℓ → ℕ}
    (h : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i) (c : ℕ × ℕ) :
    c ∈ stripDiagram r ↔ ∃ hc : c.1 < ℓ, c.2 < r ⟨c.1, hc⟩ := by
  rw [stripDiagram, dif_pos h, YoungDiagram.mem_ofRowLens]
  constructor
  · rintro ⟨h1, h2⟩
    have hc : c.1 < ℓ := by simpa using h1
    refine ⟨hc, ?_⟩
    rwa [List.getElem_ofFn] at h2
  · rintro ⟨hc, h2⟩
    have h1 : c.1 < (List.ofFn r).length := by simpa using hc
    refine ⟨h1, ?_⟩
    rwa [List.getElem_ofFn]

/-- Row lengths of the diagram of a vector, inside the range. -/
theorem stripDiagram_rowLen_lt {ℓ : ℕ} {r : Fin ℓ → ℕ}
    (h : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i) (i : Fin ℓ) :
    (stripDiagram r).rowLen (i : ℕ) = r i := by
  refine rowLen_eq_of_forall fun j => ?_
  rw [stripDiagram_mem h]
  constructor
  · rintro ⟨hc, h2⟩
    rwa [show (⟨(i : ℕ), hc⟩ : Fin ℓ) = i from Fin.ext rfl] at h2
  · intro hj
    exact ⟨i.isLt, by
      rwa [show (⟨(i : ℕ), i.isLt⟩ : Fin ℓ) = i from Fin.ext rfl]⟩

/-- Row lengths of the diagram of a vector, beyond the range. -/
theorem stripDiagram_rowLen_le {ℓ : ℕ} {r : Fin ℓ → ℕ}
    (h : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i) {i : ℕ} (hi : ℓ ≤ i) :
    (stripDiagram r).rowLen i = 0 := by
  refine rowLen_eq_of_forall fun j => ?_
  rw [stripDiagram_mem h]
  constructor
  · rintro ⟨hc, -⟩
    omega
  · intro hj
    exact absurd hj (Nat.not_lt_zero j)

/-- The diagram of a vector on `Fin ℓ` has at most `ℓ` rows. -/
theorem stripDiagram_colLen {ℓ : ℕ} {r : Fin ℓ → ℕ}
    (h : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i) :
    (stripDiagram r).colLen 0 ≤ ℓ := by
  by_contra hlt
  have hmem : (ℓ, 0) ∈ stripDiagram r :=
    YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  obtain ⟨hc, -⟩ := (stripDiagram_mem h _).mp hmem
  omega

/-- A diagram with at most `ℓ` rows is the diagram of its own
row-length vector on `Fin ℓ`. -/
theorem stripDiagram_of_rowLen {ℓ : ℕ} {mu : YoungDiagram}
    (hc : mu.colLen 0 ≤ ℓ) :
    stripDiagram (fun i : Fin ℓ => mu.rowLen (i : ℕ)) = mu := by
  have h : ∀ i j : Fin ℓ, i ≤ j →
      mu.rowLen (j : ℕ) ≤ mu.rowLen (i : ℕ) :=
    fun i j hij => mu.rowLen_anti _ _ hij
  refine ext_of_rowLen_eq fun i => ?_
  rcases Nat.lt_or_ge i ℓ with hi | hi
  · exact stripDiagram_rowLen_lt h ⟨i, hi⟩
  · rw [stripDiagram_rowLen_le h hi]
    exact (rowLen_eq_zero_of_ge mu
      (by rw [YoungDiagram.length_rowLens]; omega)).symm

/-- The cell count of the diagram of a vector is the sum of the
vector. -/
theorem stripDiagram_card {ℓ : ℕ} {r : Fin ℓ → ℕ}
    (h : ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i) :
    (stripDiagram r).card = ∑ i, r i := by
  rw [card_eq_sum_range_rowLen (stripDiagram r) ℓ
    (stripDiagram_colLen h)]
  rw [← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => stripDiagram_rowLen_lt h i

/-! ### Horizontal and vertical strips -/

/-- **Horizontal strip**: `mu` is contained in `lam` and interlaces
it — each row of `lam` reaches at most the previous row of `mu`, so
the removed skew cells occupy distinct columns. -/
def IsHStrip (lam mu : YoungDiagram) : Prop :=
  mu ≤ lam ∧ ∀ i, lam.rowLen (i + 1) ≤ mu.rowLen i

/-- **Vertical strip**: `mu` is contained in `lam` and each row
shrinks by at most one cell, so the removed skew cells occupy
distinct rows. -/
def IsVStrip (lam mu : YoungDiagram) : Prop :=
  mu ≤ lam ∧ ∀ i, lam.rowLen i ≤ mu.rowLen i + 1

/-! ### The one-row and one-column shapes -/

/-- The single-row shape of size `m`. -/
noncomputable def rowShape (m : ℕ) : Shape m :=
  ⟨stripDiagram (fun _ : Fin 1 => m), by
    rw [stripDiagram_card (fun _ _ _ => le_refl m)]
    simp⟩

/-- The single-column shape of size `m`. -/
noncomputable def colShape (m : ℕ) : Shape m :=
  ⟨stripDiagram (fun _ : Fin m => 1), by
    rw [stripDiagram_card (fun _ _ _ => le_refl 1)]
    simp⟩

/-- The first row of the one-row shape. -/
theorem rowShape_rowLen_zero (m : ℕ) :
    (rowShape m).val.rowLen 0 = m :=
  stripDiagram_rowLen_lt (fun _ _ _ => le_refl m) ⟨0, Nat.one_pos⟩

/-- The later rows of the one-row shape. -/
theorem rowShape_rowLen_succ (m i : ℕ) :
    (rowShape m).val.rowLen (i + 1) = 0 :=
  stripDiagram_rowLen_le (fun _ _ _ => le_refl m) (by omega)

/-- The one-row shape has at most one row. -/
theorem rowShape_colLen (m : ℕ) : (rowShape m).val.colLen 0 ≤ 1 :=
  stripDiagram_colLen (fun _ _ _ => le_refl m)

/-- The rows of the one-column shape, inside the column. -/
theorem colShape_rowLen_lt (m : ℕ) {i : ℕ} (hi : i < m) :
    (colShape m).val.rowLen i = 1 :=
  stripDiagram_rowLen_lt (fun _ _ _ => le_refl 1) ⟨i, hi⟩

/-- The rows of the one-column shape, beyond the column. -/
theorem colShape_rowLen_le (m : ℕ) {i : ℕ} (hi : m ≤ i) :
    (colShape m).val.rowLen i = 0 :=
  stripDiagram_rowLen_le (fun _ _ _ => le_refl 1) hi

/-- The one-column shape has rows of length at most one. -/
theorem colShape_rowLen_zero_le (m : ℕ) :
    (colShape m).val.rowLen 0 ≤ 1 := by
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · rw [colShape_rowLen_le m (by omega)]
    omega
  · rw [colShape_rowLen_lt m hpos]

/-- **Uniqueness of the one-row shape**: a shape of size `b` with
at most one row is `rowShape b`. -/
theorem shape_eq_rowShape {b : ℕ} (ν : Shape b)
    (h : ν.val.colLen 0 ≤ 1) : ν = rowShape b := by
  have h0 : ν.val.rowLen 0 = b := by
    have hcard := card_eq_sum_range_rowLen ν.val 1 h
    rw [ν.prop, Finset.sum_range_one] at hcard
    omega
  refine Shape.ext (ext_of_rowLen_eq fun i => ?_)
  cases i with
  | zero => rw [h0, rowShape_rowLen_zero]
  | succ j =>
      rw [rowShape_rowLen_succ]
      exact rowLen_eq_zero_of_ge ν.val
        (by rw [YoungDiagram.length_rowLens]; omega)

/-- **Uniqueness of the one-column shape**: a shape of size `b`
with rows of length at most one is `colShape b`. -/
theorem shape_eq_colShape {b : ℕ} (ν : Shape b)
    (h : ν.val.rowLen 0 ≤ 1) : ν = colShape b := by
  have hrow1 : ∀ i, i < ν.val.colLen 0 → ν.val.rowLen i = 1 := by
    intro i hi
    have hpos : 0 < ν.val.rowLen i :=
      rowLen_pos_of_lt_length ν.val
        (by rw [YoungDiagram.length_rowLens]; omega)
    have hle : ν.val.rowLen i ≤ ν.val.rowLen 0 :=
      ν.val.rowLen_anti 0 i (Nat.zero_le i)
    omega
  have hcard : b = ν.val.colLen 0 := by
    have h1 := card_eq_sum_range_rowLen ν.val (ν.val.colLen 0)
      (le_refl _)
    rw [ν.prop] at h1
    rw [Finset.sum_congr rfl
      (fun i hi => hrow1 i (Finset.mem_range.mp hi))] at h1
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul,
      mul_one] at h1
    exact h1
  refine Shape.ext (ext_of_rowLen_eq fun i => ?_)
  rcases Nat.lt_or_ge i b with hi | hi
  · rw [colShape_rowLen_lt b hi]
    exact hrow1 i (by omega)
  · rw [colShape_rowLen_le b hi]
    exact rowLen_eq_zero_of_ge ν.val
      (by rw [YoungDiagram.length_rowLens]; omega)

/-! ### The graded reindexing of strip-vector sums

A sum over a set of antitone row-length vectors, of a function of
the associated diagrams, is a graded sum over the shapes of each
size satisfying the membership predicate of the vector set. -/

open scoped Classical in
private theorem sum_stripDiagram_graded {ℓ n : ℕ}
    (P : Finset (Fin ℓ → ℕ)) (p : YoungDiagram → Prop)
    (F : YoungDiagram → ℂ)
    (hanti : ∀ r ∈ P, ∀ i j : Fin ℓ, i ≤ j → r j ≤ r i)
    (hp : ∀ r ∈ P, p (stripDiagram r))
    (hmem : ∀ mu : YoungDiagram, p mu → mu.card ≤ n ∧
      mu.colLen 0 ≤ ℓ ∧ (fun i : Fin ℓ => mu.rowLen (i : ℕ)) ∈ P) :
    ∑ r ∈ P, F (stripDiagram r) =
      ∑ k ∈ Finset.range (n + 1), ∑ μ : Shape k,
        (if p μ.val then 1 else 0) * F μ.val := by
  -- the indicator becomes a filter
  rw [Finset.sum_congr rfl (fun k _ => show
      (∑ μ : Shape k, (if p μ.val then (1 : ℂ) else 0) * F μ.val) =
      ∑ μ ∈ Finset.univ.filter (fun μ : Shape k => p μ.val),
        F μ.val from by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun μ _ => ?_
    by_cases hμ : p μ.val
    · rw [if_pos hμ, if_pos hμ, one_mul]
    · rw [if_neg hμ, if_neg hμ, zero_mul])]
  -- fiber the vector sum by the cell count
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun r : Fin ℓ → ℕ => (stripDiagram r).card)
    (t := Finset.range (n + 1))
    (fun r hr => Finset.mem_range.mpr (Nat.lt_succ_of_le
      (hmem _ (hp r hr)).1))
    (fun r => F (stripDiagram r))]
  refine Finset.sum_congr rfl fun k _ => ?_
  -- at each size the vectors of that count are the shapes with `p`
  refine Finset.sum_bij'
    (i := fun r hr => (⟨stripDiagram r,
      (Finset.mem_filter.mp hr).2⟩ : Shape k))
    (j := fun μ _ => fun i : Fin ℓ => μ.val.rowLen (i : ℕ))
    ?_ ?_ ?_ ?_ ?_
  · intro r hr
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hp r (Finset.mem_filter.mp hr).1⟩
  · intro μ hμ
    have hpμ : p μ.val := (Finset.mem_filter.mp hμ).2
    rw [Finset.mem_filter]
    refine ⟨(hmem μ.val hpμ).2.2, ?_⟩
    rw [stripDiagram_of_rowLen (hmem μ.val hpμ).2.1]
    exact μ.prop
  · intro r hr
    funext i
    exact stripDiagram_rowLen_lt
      (hanti r (Finset.mem_filter.mp hr).1) i
  · intro μ hμ
    have hpμ : p μ.val := (Finset.mem_filter.mp hμ).2
    exact Shape.ext (stripDiagram_of_rowLen (hmem μ.val hpμ).2.1)
  · intro r _
    rfl

/-! ### The Jacobi–Trudi determinant in row-length form -/

/-- The Schur specialisation of a diagram is its Jacobi–Trudi
determinant over any square of rows covering the column length,
with the row lengths as exponents — zero rows pad invisibly. -/
theorem diagramSchur_eq_det_rowLen (mu : YoungDiagram) {k : ℕ}
    (hk : mu.colLen 0 ≤ k) (t : ℕ → ℂ) :
    diagramSchur mu t =
      (Matrix.of fun i j : Fin k =>
        newtonHZ t ((mu.rowLen (i : ℕ) : ℤ) +
          (j : ℤ) - (i : ℤ))).det := by
  have hzero : ∀ i, mu.rowLens.length ≤ i → mu.rowLen i = 0 :=
    fun i hi => rowLen_eq_zero_of_ge mu hi
  have hLk : mu.rowLens.length ≤ k := by
    rw [YoungDiagram.length_rowLens]
    exact hk
  refine Eq.trans ?_
    (det_newtonHZ_pad t (fun i => mu.rowLen i) k hLk hzero).symm
  rw [diagramSchur, schurDet]
  congr 1
  refine Matrix.ext fun i j => ?_
  rw [Matrix.of_apply, Matrix.of_apply]
  congr 2
  rw [List.get_eq_getElem, YoungDiagram.get_rowLens]

/-! ### One extra even variable: the partial-sum sequence

At `t + superPS 1 0` the complete homogeneous sequence is the
partial-sum sequence of that of `t`; its integer-indexed first
difference is `newtonHZ t`, and telescoping produces the
interval-sum identity feeding the row operation. -/

private theorem newtonH_add_superPS_row (t : ℕ → ℂ) (n : ℕ) :
    newtonH (fun c => t c + superPS 1 0 c) n =
      ∑ m ∈ Finset.range (n + 1), newtonH t m := by
  rw [newtonH_add]
  rw [Finset.sum_congr rfl fun ij _ => by
    rw [newtonH_superPS_zero_q 1 ij.2 Nat.one_pos,
      show (1 - 1 + ij.2).choose ij.2 = 1 from by
        rw [show 1 - 1 + ij.2 = ij.2 from by omega, Nat.choose_self],
      Nat.cast_one, mul_one]]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

private theorem newtonHZ_row_step (t : ℕ → ℂ) (w : ℤ) :
    newtonHZ (fun c => t c + superPS 1 0 c) w =
      newtonHZ (fun c => t c + superPS 1 0 c) (w - 1) +
        newtonHZ t w := by
  rcases lt_or_ge w 0 with hw | hw
  · rw [newtonHZ_neg _ _ hw, newtonHZ_neg _ _ (by omega),
      newtonHZ_neg _ _ hw]
    ring
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hw
    cases n with
    | zero =>
        rw [newtonHZ_natCast, newtonHZ_natCast, newtonH_zero,
          newtonH_zero, newtonHZ_neg _ _ (by norm_num)]
        ring
    | succ m =>
        rw [show ((m + 1 : ℕ) : ℤ) - 1 = ((m : ℕ) : ℤ) from by
          push_cast; ring]
        rw [newtonHZ_natCast, newtonHZ_natCast, newtonHZ_natCast,
          newtonH_add_superPS_row, newtonH_add_superPS_row,
          Finset.sum_range_succ]

private theorem newtonHZ_row_sum (t : ℕ → ℂ) (z : ℤ) {b a : ℕ}
    (hba : b ≤ a) :
    newtonHZ (fun c => t c + superPS 1 0 c) ((a : ℤ) + z) =
      newtonHZ (fun c => t c + superPS 1 0 c) ((b : ℤ) - 1 + z) +
        ∑ μ ∈ Finset.Icc b a, newtonHZ t ((μ : ℤ) + z) := by
  induction a, hba using Nat.le_induction with
  | base =>
      rw [Finset.Icc_self, Finset.sum_singleton]
      have hstep := newtonHZ_row_step t ((b : ℤ) + z)
      rw [show (b : ℤ) + z - 1 = (b : ℤ) - 1 + z from by ring]
        at hstep
      exact hstep
  | succ a hba ih =>
      have hins : Finset.Icc b (a + 1) =
          insert (a + 1) (Finset.Icc b a) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hins, Finset.sum_insert (by
        simp only [Finset.mem_Icc]
        omega)]
      have hstep := newtonHZ_row_step t (((a + 1 : ℕ) : ℤ) + z)
      rw [show ((a + 1 : ℕ) : ℤ) + z - 1 = ((a : ℕ) : ℤ) + z from by
        push_cast; ring] at hstep
      rw [hstep, ih]
      ring

/-! ### The unipotent row operation -/

/-- The unipotent row-operation matrix subtracting from each row
its successor. -/
noncomputable def rowOp (ℓ : ℕ) : Matrix (Fin ℓ) (Fin ℓ) ℂ :=
  Matrix.of fun i k =>
    if k = i then 1 else if (k : ℕ) = (i : ℕ) + 1 then -1 else 0

/-- The row operation is upper triangular. -/
theorem rowOp_blockTriangular (ℓ : ℕ) :
    (rowOp ℓ).BlockTriangular id := by
  intro i k hki
  have h : (k : ℕ) < (i : ℕ) := hki
  simp only [rowOp, Matrix.of_apply]
  split_ifs with h1 h2
  · exact absurd (congrArg Fin.val h1) (by omega)
  · omega
  · rfl

/-- The row operation has determinant one. -/
theorem det_rowOp (ℓ : ℕ) : (rowOp ℓ).det = 1 := by
  rw [Matrix.det_of_upperTriangular (rowOp_blockTriangular ℓ)]
  refine Finset.prod_eq_one fun i _ => ?_
  simp [rowOp]

/-- Entries of a matrix transformed by the row operation. -/
private theorem rowOp_mul_apply {ℓ : ℕ}
    (M : Matrix (Fin ℓ) (Fin ℓ) ℂ) (i j : Fin ℓ) :
    (rowOp ℓ * M) i j =
      M i j - (if h : (i : ℕ) + 1 < ℓ then M ⟨(i : ℕ) + 1, h⟩ j
        else 0) := by
  rw [Matrix.mul_apply]
  by_cases h : (i : ℕ) + 1 < ℓ
  · rw [dif_pos h]
    have hsplit : ∀ k : Fin ℓ, rowOp ℓ i k * M k j =
        (if k = i then M k j else 0) +
          (if k = (⟨(i : ℕ) + 1, h⟩ : Fin ℓ) then -M k j else 0) := by
      intro k
      simp only [rowOp, Matrix.of_apply]
      by_cases h1 : k = i
      · rw [if_pos h1, if_pos h1, one_mul,
          if_neg (fun he => by
            have hv : (i : ℕ) = (i : ℕ) + 1 :=
              congrArg Fin.val (h1.symm.trans he)
            omega),
          add_zero]
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : (k : ℕ) = (i : ℕ) + 1
        · rw [if_pos h2, if_pos (Fin.ext h2), neg_one_mul, zero_add]
        · rw [if_neg h2,
            if_neg (fun hk => h2 (congrArg Fin.val hk)),
            zero_mul, add_zero]
    rw [Finset.sum_congr rfl fun k _ => hsplit k,
      Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ i (fun k => M k j),
      if_pos (Finset.mem_univ i),
      Finset.sum_ite_eq' Finset.univ (⟨(i : ℕ) + 1, h⟩ : Fin ℓ)
        (fun k => -M k j),
      if_pos (Finset.mem_univ _)]
    ring
  · rw [dif_neg h]
    have hone : ∀ k : Fin ℓ, rowOp ℓ i k * M k j =
        if k = i then M k j else 0 := by
      intro k
      simp only [rowOp, Matrix.of_apply]
      by_cases h1 : k = i
      · rw [if_pos h1, if_pos h1, one_mul]
      · rw [if_neg h1, if_neg h1,
          if_neg (fun h2 : (k : ℕ) = (i : ℕ) + 1 =>
            h (h2 ▸ k.isLt)),
          zero_mul]
    rw [Finset.sum_congr rfl fun k _ => hone k,
      Finset.sum_ite_eq' Finset.univ i (fun k => M k j),
      if_pos (Finset.mem_univ i)]
    ring

/-! ### The horizontal Pieri determinant identity -/

/-- The interlacing row-length vectors of a diagram: the exponent
choices of the horizontal-strip sub-diagrams. -/
private def rowStripVecs (lam : YoungDiagram) :
    Finset (Fin lam.rowLens.length → ℕ) :=
  Fintype.piFinset fun i =>
    Finset.Icc (lam.rowLen ((i : ℕ) + 1)) (lam.rowLen (i : ℕ))

private theorem mem_rowStripVecs {lam : YoungDiagram}
    {r : Fin lam.rowLens.length → ℕ} (hr : r ∈ rowStripVecs lam)
    (i : Fin lam.rowLens.length) :
    lam.rowLen ((i : ℕ) + 1) ≤ r i ∧ r i ≤ lam.rowLen (i : ℕ) :=
  Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hr i)

private theorem rowStripVecs_anti {lam : YoungDiagram} :
    ∀ r ∈ rowStripVecs lam, ∀ i j : Fin lam.rowLens.length,
      i ≤ j → r j ≤ r i := by
  intro r hr
  refine fin_antitone_of_adjacent fun i hi => ?_
  exact le_trans (mem_rowStripVecs hr ⟨i + 1, hi⟩).2
    (mem_rowStripVecs hr ⟨i, Nat.lt_of_succ_lt hi⟩).1

open scoped Classical in
/-- **One extra even variable — the horizontal Pieri identity**:
the Schur specialisation of `lam` at `t + superPS 1 0` is the sum
of the Schur specialisations at `t` of the horizontal-strip
sub-diagrams of `lam`, presented as a graded sum over the shapes
of each size with the strip indicator. -/
theorem diagramSchur_add_one_row (lam : YoungDiagram) (t : ℕ → ℂ) :
    diagramSchur lam (fun c => t c + superPS 1 0 c) =
      ∑ k ∈ Finset.range (lam.card + 1), ∑ μ : Shape k,
        (if IsHStrip lam μ.val then 1 else 0) *
          diagramSchur μ.val t := by
  classical
  set M : Matrix (Fin lam.rowLens.length)
      (Fin lam.rowLens.length) ℂ := Matrix.of fun i j =>
    newtonHZ (fun c => t c + superPS 1 0 c)
      ((lam.rowLen (i : ℕ) : ℤ) + (j : ℤ) - (i : ℤ)) with hM
  -- the specialisation as the determinant of `M`
  have h1 : diagramSchur lam (fun c => t c + superPS 1 0 c) =
      M.det :=
    diagramSchur_eq_det_rowLen lam
      (le_of_eq YoungDiagram.length_rowLens.symm) _
  -- rows after the row operation are interval sums
  have h2 : ∀ i j : Fin lam.rowLens.length,
      (rowOp lam.rowLens.length * M) i j =
      ∑ μ ∈ Finset.Icc (lam.rowLen ((i : ℕ) + 1))
          (lam.rowLen (i : ℕ)),
        newtonHZ t ((μ : ℤ) + (j : ℤ) - (i : ℤ)) := by
    intro i j
    rw [rowOp_mul_apply]
    have hba : lam.rowLen ((i : ℕ) + 1) ≤ lam.rowLen (i : ℕ) :=
      lam.rowLen_anti _ _ (by omega)
    have hsum := newtonHZ_row_sum t ((j : ℤ) - (i : ℤ)) hba
    have harg : (lam.rowLen (i : ℕ) : ℤ) + (j : ℤ) - (i : ℤ) =
        (lam.rowLen (i : ℕ) : ℤ) + ((j : ℤ) - (i : ℤ)) := by ring
    have hfix : (∑ μ ∈ Finset.Icc (lam.rowLen ((i : ℕ) + 1))
          (lam.rowLen (i : ℕ)),
        newtonHZ t ((μ : ℤ) + ((j : ℤ) - (i : ℤ)))) =
        ∑ μ ∈ Finset.Icc (lam.rowLen ((i : ℕ) + 1))
            (lam.rowLen (i : ℕ)),
          newtonHZ t ((μ : ℤ) + (j : ℤ) - (i : ℤ)) := by
      refine Finset.sum_congr rfl fun μ _ => ?_
      congr 1
      ring
    by_cases h : (i : ℕ) + 1 < lam.rowLens.length
    · rw [dif_pos h]
      show newtonHZ (fun c => t c + superPS 1 0 c)
          ((lam.rowLen (i : ℕ) : ℤ) + (j : ℤ) - (i : ℤ)) -
          newtonHZ (fun c => t c + superPS 1 0 c)
            ((lam.rowLen ((i : ℕ) + 1) : ℤ) + (j : ℤ) -
              (((i : ℕ) + 1 : ℕ) : ℤ)) = _
      rw [show (lam.rowLen ((i : ℕ) + 1) : ℤ) + (j : ℤ) -
          (((i : ℕ) + 1 : ℕ) : ℤ) =
          (lam.rowLen ((i : ℕ) + 1) : ℤ) - 1 +
            ((j : ℤ) - (i : ℤ)) from by push_cast; ring]
      rw [harg, hsum, hfix]
      ring
    · rw [dif_neg h]
      have hneg : (lam.rowLen ((i : ℕ) + 1) : ℤ) - 1 +
          ((j : ℤ) - (i : ℤ)) < 0 := by
        rw [rowLen_eq_zero_of_ge lam (by omega)]
        have hj := j.isLt
        have hi := i.isLt
        push_cast
        omega
      show newtonHZ (fun c => t c + superPS 1 0 c)
          ((lam.rowLen (i : ℕ) : ℤ) + (j : ℤ) - (i : ℤ)) - 0 = _
      rw [harg, hsum, newtonHZ_neg _ _ hneg, hfix]
      ring
  -- multilinear expansion of the transformed determinant
  have h3 : M.det = ∑ r ∈ rowStripVecs lam,
      (Matrix.of fun i j : Fin lam.rowLens.length =>
        newtonHZ t ((r i : ℤ) + (j : ℤ) - (i : ℤ))).det := by
    have hdet : M.det = (rowOp lam.rowLens.length * M).det := by
      rw [Matrix.det_mul, det_rowOp, one_mul]
    rw [hdet]
    have hrows : (fun i : Fin lam.rowLens.length =>
        (rowOp lam.rowLens.length * M) i) =
        fun i : Fin lam.rowLens.length =>
          ∑ μ ∈ Finset.Icc (lam.rowLen ((i : ℕ) + 1))
            (lam.rowLen (i : ℕ)),
          (fun j : Fin lam.rowLens.length =>
            newtonHZ t ((μ : ℤ) + (j : ℤ) - (i : ℤ))) := by
      funext i
      funext j
      rw [Finset.sum_apply]
      exact h2 i j
    show Matrix.detRowAlternating
      (fun i : Fin lam.rowLens.length =>
        (rowOp lam.rowLens.length * M) i) = _
    rw [hrows]
    exact (Matrix.detRowAlternating (n := Fin lam.rowLens.length)
      (R := ℂ)).toMultilinearMap.map_sum_finset
      (fun (i : Fin lam.rowLens.length) (μ : ℕ) =>
        fun j : Fin lam.rowLens.length =>
          newtonHZ t ((μ : ℤ) + (j : ℤ) - (i : ℤ)))
      (fun i => Finset.Icc (lam.rowLen ((i : ℕ) + 1))
        (lam.rowLen (i : ℕ)))
  -- each expansion term is the Schur value of its strip diagram
  have h4 : ∀ r ∈ rowStripVecs lam,
      (Matrix.of fun i j : Fin lam.rowLens.length =>
        newtonHZ t ((r i : ℤ) + (j : ℤ) - (i : ℤ))).det =
      diagramSchur (stripDiagram r) t := by
    intro r hr
    rw [diagramSchur_eq_det_rowLen (stripDiagram r)
      (k := lam.rowLens.length)
      (stripDiagram_colLen (rowStripVecs_anti r hr)) t]
    congr 1
    refine Matrix.ext fun i j => ?_
    rw [Matrix.of_apply, Matrix.of_apply,
      stripDiagram_rowLen_lt (rowStripVecs_anti r hr) i]
  -- assemble and reindex over the shapes of each size
  rw [h1, h3, Finset.sum_congr rfl h4]
  refine sum_stripDiagram_graded (rowStripVecs lam)
    (IsHStrip lam) (fun mu => diagramSchur mu t)
    rowStripVecs_anti ?_ ?_
  · intro r hr
    constructor
    · refine le_of_rowLen_le fun i => ?_
      rcases Nat.lt_or_ge i lam.rowLens.length with hi | hi
      · rw [stripDiagram_rowLen_lt (rowStripVecs_anti r hr) ⟨i, hi⟩]
        exact (mem_rowStripVecs hr ⟨i, hi⟩).2
      · rw [stripDiagram_rowLen_le (rowStripVecs_anti r hr) hi]
        omega
    · intro i
      rcases Nat.lt_or_ge i lam.rowLens.length with hi | hi
      · rw [stripDiagram_rowLen_lt (rowStripVecs_anti r hr) ⟨i, hi⟩]
        exact (mem_rowStripVecs hr ⟨i, hi⟩).1
      · rw [rowLen_eq_zero_of_ge lam (by omega)]
        omega
  · intro mu hmu
    refine ⟨YoungDiagram.card_le_card hmu.1, ?_, ?_⟩
    · rw [YoungDiagram.length_rowLens]
      exact colLen_le_of_le hmu.1 0
    · rw [rowStripVecs, Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_Icc]
      exact ⟨hmu.2 (i : ℕ), rowLen_mono hmu.1 (i : ℕ)⟩

/-! ### One extra odd variable: the two-term sequence

At `t + superPS 0 1` the complete homogeneous sequence is the
two-term convolution `h_n + h_{n-1}`: the generating series picks
up one factor `1 + X`. -/

private theorem newtonHZ_col_step (t : ℕ → ℂ) (z : ℤ) :
    newtonHZ (fun c => t c + superPS 0 1 c) z =
      newtonHZ t z + newtonHZ t (z - 1) := by
  rcases lt_or_ge z 0 with hz | hz
  · rw [newtonHZ_neg _ _ hz, newtonHZ_neg _ _ hz,
      newtonHZ_neg _ _ (by omega)]
    ring
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
    have h := congrArg (PowerSeries.coeff n)
      (newtonHSeries_add t (superPS 0 1))
    rw [show newtonHSeries (superPS 0 1) = 1 + PowerSeries.X from by
      have h1 := newtonHSeries_superPS 0 1
      rwa [pow_zero, one_mul, pow_one] at h1] at h
    rw [mul_add, mul_one, map_add] at h
    simp only [newtonHSeries, PowerSeries.coeff_mk] at h
    cases n with
    | zero =>
        rw [PowerSeries.coeff_zero_mul_X] at h
        rw [newtonHZ_natCast, newtonHZ_natCast,
          newtonHZ_neg _ _ (by norm_num)]
        exact h
    | succ m =>
        rw [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mk] at h
        rw [show ((m + 1 : ℕ) : ℤ) - 1 = ((m : ℕ) : ℤ) from by
          push_cast; ring]
        rw [newtonHZ_natCast, newtonHZ_natCast, newtonHZ_natCast]
        exact h

/-! ### The vertical Pieri determinant identity -/

open scoped Classical in
/-- The near-constant row-length vectors of a diagram: the exponent
choices of the vertical-strip sub-diagrams, each row shrinking by
at most one, filtered by monotonicity. -/
private noncomputable def colStripVecs (lam : YoungDiagram) :
    Finset (Fin lam.rowLens.length → ℕ) :=
  (Fintype.piFinset fun i : Fin lam.rowLens.length =>
    Finset.Icc (lam.rowLen (i : ℕ) - 1) (lam.rowLen (i : ℕ))).filter
    fun r => ∀ (i : ℕ) (hi : i + 1 < lam.rowLens.length),
      r ⟨i + 1, hi⟩ ≤ r ⟨i, Nat.lt_of_succ_lt hi⟩

private theorem mem_colStripVecs {lam : YoungDiagram}
    {r : Fin lam.rowLens.length → ℕ} (hr : r ∈ colStripVecs lam)
    (i : Fin lam.rowLens.length) :
    lam.rowLen (i : ℕ) - 1 ≤ r i ∧ r i ≤ lam.rowLen (i : ℕ) := by
  classical
  rw [colStripVecs, Finset.mem_filter] at hr
  exact Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hr.1 i)

private theorem colStripVecs_good {lam : YoungDiagram}
    {r : Fin lam.rowLens.length → ℕ} (hr : r ∈ colStripVecs lam) :
    ∀ (i : ℕ) (hi : i + 1 < lam.rowLens.length),
      r ⟨i + 1, hi⟩ ≤ r ⟨i, Nat.lt_of_succ_lt hi⟩ := by
  classical
  rw [colStripVecs, Finset.mem_filter] at hr
  exact hr.2

private theorem colStripVecs_anti {lam : YoungDiagram} :
    ∀ r ∈ colStripVecs lam, ∀ i j : Fin lam.rowLens.length,
      i ≤ j → r j ≤ r i := by
  intro r hr
  exact fin_antitone_of_adjacent (colStripVecs_good hr)

open scoped Classical in
/-- **One extra odd variable — the vertical Pieri identity**: the
Schur specialisation of `lam` at `t + superPS 0 1` is the sum of
the Schur specialisations at `t` of the vertical-strip sub-diagrams
of `lam`, presented as a graded sum over the shapes of each size
with the strip indicator. -/
theorem diagramSchur_add_one_col (lam : YoungDiagram) (t : ℕ → ℂ) :
    diagramSchur lam (fun c => t c + superPS 0 1 c) =
      ∑ k ∈ Finset.range (lam.card + 1), ∑ μ : Shape k,
        (if IsVStrip lam μ.val then 1 else 0) *
          diagramSchur μ.val t := by
  classical
  set M : Matrix (Fin lam.rowLens.length)
      (Fin lam.rowLens.length) ℂ := Matrix.of fun i j =>
    newtonHZ (fun c => t c + superPS 0 1 c)
      ((lam.rowLen (i : ℕ) : ℤ) + (j : ℤ) - (i : ℤ)) with hM
  have h1 : diagramSchur lam (fun c => t c + superPS 0 1 c) =
      M.det :=
    diagramSchur_eq_det_rowLen lam
      (le_of_eq YoungDiagram.length_rowLens.symm) _
  -- two-term decomposition of each row
  have h2 : (fun i : Fin lam.rowLens.length => M i) =
      fun i : Fin lam.rowLens.length =>
        ∑ z ∈ ({(lam.rowLen (i : ℕ) : ℤ) - 1,
            (lam.rowLen (i : ℕ) : ℤ)} : Finset ℤ),
          (fun j : Fin lam.rowLens.length =>
            newtonHZ t (z + (j : ℤ) - (i : ℤ))) := by
    funext i
    funext j
    rw [Finset.sum_apply]
    show newtonHZ (fun c => t c + superPS 0 1 c)
      ((lam.rowLen (i : ℕ) : ℤ) + (j : ℤ) - (i : ℤ)) = _
    rw [newtonHZ_col_step,
      Finset.sum_pair (by omega : (lam.rowLen (i : ℕ) : ℤ) - 1 ≠
        (lam.rowLen (i : ℕ) : ℤ)),
      show (lam.rowLen (i : ℕ) : ℤ) + (j : ℤ) - (i : ℤ) - 1 =
        (lam.rowLen (i : ℕ) : ℤ) - 1 + (j : ℤ) - (i : ℤ) from by
          ring]
    ring
  -- multilinear expansion over the two-element choices
  have h3 : M.det = ∑ r ∈ Fintype.piFinset
      (fun i : Fin lam.rowLens.length =>
        ({(lam.rowLen (i : ℕ) : ℤ) - 1,
          (lam.rowLen (i : ℕ) : ℤ)} : Finset ℤ)),
      (Matrix.of fun i j : Fin lam.rowLens.length =>
        newtonHZ t (r i + (j : ℤ) - (i : ℤ))).det := by
    show Matrix.detRowAlternating
      (fun i : Fin lam.rowLens.length => M i) = _
    rw [h2]
    exact (Matrix.detRowAlternating (n := Fin lam.rowLens.length)
      (R := ℂ)).toMultilinearMap.map_sum_finset
      (fun (i : Fin lam.rowLens.length) (z : ℤ) =>
        fun j : Fin lam.rowLens.length =>
          newtonHZ t (z + (j : ℤ) - (i : ℤ)))
      (fun i => ({(lam.rowLen (i : ℕ) : ℤ) - 1,
        (lam.rowLen (i : ℕ) : ℤ)} : Finset ℤ))
  -- non-monotone choices produce equal adjacent rows
  have h4 : ∀ r ∈ Fintype.piFinset
      (fun i : Fin lam.rowLens.length =>
        ({(lam.rowLen (i : ℕ) : ℤ) - 1,
          (lam.rowLen (i : ℕ) : ℤ)} : Finset ℤ)),
      (Matrix.of fun i j : Fin lam.rowLens.length =>
        newtonHZ t (r i + (j : ℤ) - (i : ℤ))).det ≠ 0 →
      ∀ (i : ℕ) (hi : i + 1 < lam.rowLens.length),
        r ⟨i + 1, hi⟩ ≤ r ⟨i, Nat.lt_of_succ_lt hi⟩ := by
    intro r hr hne i hi
    by_contra hlt
    rw [not_le] at hlt
    have hm1 := Fintype.mem_piFinset.mp hr ⟨i, Nat.lt_of_succ_lt hi⟩
    have hm2 := Fintype.mem_piFinset.mp hr ⟨i + 1, hi⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at hm1 hm2
    have hm1' : r ⟨i, Nat.lt_of_succ_lt hi⟩ = (lam.rowLen i : ℤ) - 1 ∨
        r ⟨i, Nat.lt_of_succ_lt hi⟩ = (lam.rowLen i : ℤ) := hm1
    have hm2' : r ⟨i + 1, hi⟩ = (lam.rowLen (i + 1) : ℤ) - 1 ∨
        r ⟨i + 1, hi⟩ = (lam.rowLen (i + 1) : ℤ) := hm2
    have hba : lam.rowLen (i + 1) ≤ lam.rowLen i :=
      lam.rowLen_anti _ _ (by omega)
    have hkey : r ⟨i, Nat.lt_of_succ_lt hi⟩ =
        (lam.rowLen i : ℤ) - 1 ∧
        r ⟨i + 1, hi⟩ = (lam.rowLen i : ℤ) := by
      rcases hm1' with h1 | h1 <;> rcases hm2' with h2 | h2 <;>
        constructor <;> omega
    refine hne (Matrix.det_zero_of_row_eq
      (i := (⟨i, Nat.lt_of_succ_lt hi⟩ : Fin lam.rowLens.length))
      (j := (⟨i + 1, hi⟩ : Fin lam.rowLens.length))
      (fun he => by
        have hv : i = i + 1 := congrArg Fin.val he
        omega) ?_)
    funext j
    show newtonHZ t (r ⟨i, Nat.lt_of_succ_lt hi⟩ +
        (j : ℤ) - ((i : ℕ) : ℤ)) =
      newtonHZ t (r ⟨i + 1, hi⟩ + (j : ℤ) - ((i + 1 : ℕ) : ℤ))
    rw [hkey.1, hkey.2]
    congr 1
    push_cast
    ring
  -- reindex the surviving choices to natural strip vectors
  have h5 : ∑ r ∈ Fintype.piFinset
      (fun i : Fin lam.rowLens.length =>
        ({(lam.rowLen (i : ℕ) : ℤ) - 1,
          (lam.rowLen (i : ℕ) : ℤ)} : Finset ℤ)),
      (Matrix.of fun i j : Fin lam.rowLens.length =>
        newtonHZ t (r i + (j : ℤ) - (i : ℤ))).det =
      ∑ s ∈ colStripVecs lam, diagramSchur (stripDiagram s) t := by
    rw [← Finset.sum_filter_of_ne (p := fun r =>
      ∀ (i : ℕ) (hi : i + 1 < lam.rowLens.length),
        r ⟨i + 1, hi⟩ ≤ r ⟨i, Nat.lt_of_succ_lt hi⟩) h4]
    refine Finset.sum_bij'
      (i := fun r _ => fun i : Fin lam.rowLens.length =>
        (r i).toNat)
      (j := fun s _ => fun i : Fin lam.rowLens.length =>
        ((s i : ℕ) : ℤ))
      ?_ ?_ ?_ ?_ ?_
    · intro r hr
      have hrp := Finset.mem_filter.mp hr
      rw [colStripVecs, Finset.mem_filter]
      constructor
      · rw [Fintype.mem_piFinset]
        intro i
        have hm := Fintype.mem_piFinset.mp hrp.1 i
        rw [Finset.mem_insert, Finset.mem_singleton] at hm
        have hpos : 0 < lam.rowLen (i : ℕ) :=
          rowLen_pos_of_lt_length lam i.isLt
        rw [Finset.mem_Icc]
        show lam.rowLen (i : ℕ) - 1 ≤ (r i).toNat ∧
          (r i).toNat ≤ lam.rowLen (i : ℕ)
        rcases hm with h | h <;> omega
      · intro i hi
        have hle := hrp.2 i hi
        show (r ⟨i + 1, hi⟩).toNat ≤
          (r ⟨i, Nat.lt_of_succ_lt hi⟩).toNat
        omega
    · intro s hs
      have hgood := colStripVecs_good hs
      rw [Finset.mem_filter]
      constructor
      · rw [Fintype.mem_piFinset]
        intro i
        have hpos : 0 < lam.rowLen (i : ℕ) :=
          rowLen_pos_of_lt_length lam i.isLt
        have hb := mem_colStripVecs hs i
        rw [Finset.mem_insert, Finset.mem_singleton]
        show ((s i : ℕ) : ℤ) = (lam.rowLen (i : ℕ) : ℤ) - 1 ∨
          ((s i : ℕ) : ℤ) = (lam.rowLen (i : ℕ) : ℤ)
        omega
      · intro i hi
        have := hgood i hi
        show ((s ⟨i + 1, hi⟩ : ℕ) : ℤ) ≤
          ((s ⟨i, Nat.lt_of_succ_lt hi⟩ : ℕ) : ℤ)
        omega
    · intro r hr
      funext i
      have hm := Fintype.mem_piFinset.mp
        (Finset.mem_filter.mp hr).1 i
      rw [Finset.mem_insert, Finset.mem_singleton] at hm
      have hpos : 0 < lam.rowLen (i : ℕ) :=
        rowLen_pos_of_lt_length lam i.isLt
      show ((r i).toNat : ℤ) = r i
      omega
    · intro s _
      funext i
      show ((s i : ℕ) : ℤ).toNat = s i
      omega
    · intro r hr
      have hgood := (Finset.mem_filter.mp hr).2
      have hanti := fin_antitone_of_adjacent
        (r := fun i : Fin lam.rowLens.length => (r i).toNat)
        (fun i hi => by
          have := hgood i hi
          omega)
      rw [diagramSchur_eq_det_rowLen
        (stripDiagram (fun i : Fin lam.rowLens.length =>
          (r i).toNat))
        (k := lam.rowLens.length) (stripDiagram_colLen hanti) t]
      congr 1
      refine Matrix.ext fun i j => ?_
      rw [Matrix.of_apply, Matrix.of_apply,
        stripDiagram_rowLen_lt hanti i]
      congr 1
      have hm := Fintype.mem_piFinset.mp
        (Finset.mem_filter.mp hr).1 i
      rw [Finset.mem_insert, Finset.mem_singleton] at hm
      have hpos : 0 < lam.rowLen (i : ℕ) :=
        rowLen_pos_of_lt_length lam i.isLt
      have hval : ((r i).toNat : ℤ) = r i := by omega
      rw [hval]
  -- assemble and reindex over the shapes of each size
  rw [h1, h3, h5]
  refine sum_stripDiagram_graded (colStripVecs lam)
    (IsVStrip lam) (fun mu => diagramSchur mu t)
    colStripVecs_anti ?_ ?_
  · intro s hs
    constructor
    · refine le_of_rowLen_le fun i => ?_
      rcases Nat.lt_or_ge i lam.rowLens.length with hi | hi
      · rw [stripDiagram_rowLen_lt (colStripVecs_anti s hs) ⟨i, hi⟩]
        exact (mem_colStripVecs hs ⟨i, hi⟩).2
      · rw [stripDiagram_rowLen_le (colStripVecs_anti s hs) hi]
        omega
    · intro i
      rcases Nat.lt_or_ge i lam.rowLens.length with hi | hi
      · rw [stripDiagram_rowLen_lt (colStripVecs_anti s hs) ⟨i, hi⟩]
        have h1 : lam.rowLen i - 1 ≤ s ⟨i, hi⟩ :=
          (mem_colStripVecs hs ⟨i, hi⟩).1
        omega
      · rw [rowLen_eq_zero_of_ge lam (by omega)]
        omega
  · intro mu hmu
    refine ⟨YoungDiagram.card_le_card hmu.1, ?_, ?_⟩
    · rw [YoungDiagram.length_rowLens]
      exact colLen_le_of_le hmu.1 0
    · rw [colStripVecs, Finset.mem_filter]
      constructor
      · rw [Fintype.mem_piFinset]
        intro i
        rw [Finset.mem_Icc]
        have h1 := hmu.2 (i : ℕ)
        have h2 := rowLen_mono hmu.1 (i : ℕ)
        omega
      · intro i hi
        exact mu.rowLen_anti i (i + 1) (by omega)

/-! ### The multiplicity Pieri rules

Splitting `t + superPS 1 0` through `diagramSchur_add` collapses
the second tensor factor to the one-row shape; comparing with the
determinant identity through the graded linear independence reads
off the induction multiplicities. -/

/-- Pairing a coefficient family against the one-row indicator
collapses the shape sum to the one-row shape. -/
private theorem sum_shape_superPS_row {b : ℕ} (G : Shape b → ℂ) :
    ∑ ν : Shape b, G ν * diagramSchur ν.val (superPS 1 0) =
      G (rowShape b) := by
  rw [Finset.sum_congr rfl fun ν _ => by
    rw [diagramSchur_superPS_row ν.val]]
  rw [Finset.sum_eq_single (rowShape b)
    (fun ν _ hne => by
      rw [if_neg (fun hle => hne (shape_eq_rowShape ν hle)),
        mul_zero])
    (fun h => absurd (Finset.mem_univ _) h)]
  rw [if_pos (rowShape_colLen b), mul_one]

/-- Pairing a coefficient family against the one-column indicator
collapses the shape sum to the one-column shape. -/
private theorem sum_shape_superPS_col {b : ℕ} (G : Shape b → ℂ) :
    ∑ ν : Shape b, G ν * diagramSchur ν.val (superPS 0 1) =
      G (colShape b) := by
  rw [Finset.sum_congr rfl fun ν _ => by
    rw [diagramSchur_superPS_col ν.val]]
  rw [Finset.sum_eq_single (colShape b)
    (fun ν _ hne => by
      rw [if_neg (fun hle => hne (shape_eq_colShape ν hle)),
        mul_zero])
    (fun h => absurd (Finset.mem_univ _) h)]
  rw [if_pos (colShape_rowLen_zero_le b), mul_one]

/-- Transport of induction multiplicities along an equality of the
second size. -/
private theorem indMult_congr {a b b' : ℕ} (h : b = b')
    (lam : Shape (a + b)) (lam' : Shape (a + b'))
    (hl : lam.val = lam'.val) (μ : Shape a)
    (ν : Shape b) (ν' : Shape b') (hν : ν.val = ν'.val) :
    indMult lam μ ν = indMult lam' μ ν' := by
  subst h
  rw [Shape.ext hl, Shape.ext hν]

/-- The additive splitting at `t + superPS 1 0`, with the one-row
collapse and the antidiagonal reindexed over sizes. -/
private theorem diagramSchur_add_superPS_row_expand {n : ℕ}
    (lam : Shape n) (t : ℕ → ℂ) :
    diagramSchur lam.val (fun c => t c + superPS 1 0 c) =
      ∑ k ∈ Finset.range (n + 1), ∑ κ : Shape k,
        (if h : k ≤ n then
          indMult (⟨lam.val, by rw [lam.prop]; omega⟩ :
            Shape (k + (n - k))) κ (rowShape (n - k))
        else 0) * diagramSchur κ.val t := by
  rw [diagramSchur_add lam.val t (superPS 1 0)]
  rw [Finset.sum_congr rfl fun ab _ => Finset.sum_congr rfl
    fun κ _ => sum_shape_superPS_row (fun ν =>
      indMult ⟨lam.val, (Finset.mem_antidiagonal.mp ab.2).symm⟩
          κ ν * diagramSchur κ.val t)]
  refine Finset.sum_bij'
    (i := fun ab _ => ab.1.1)
    (j := fun k hk => (⟨(k, lam.val.card - k),
      Finset.mem_antidiagonal.mpr (by
        have h1 := lam.prop
        have h2 := Finset.mem_range.mp hk
        omega)⟩ :
      {x // x ∈ Finset.antidiagonal lam.val.card}))
    ?_ ?_ ?_ ?_ ?_
  · intro ab _
    have h1 := Finset.mem_antidiagonal.mp ab.2
    have h2 := lam.prop
    exact Finset.mem_range.mpr (by omega)
  · intro k _
    exact Finset.mem_attach _ _
  · intro ab _
    have h1 := Finset.mem_antidiagonal.mp ab.2
    have h2 : lam.val.card - ab.1.1 = ab.1.2 := by omega
    exact Subtype.ext (show (ab.1.1, lam.val.card - ab.1.1) = ab.1
      from by rw [h2])
  · intro k _
    rfl
  · intro ab _
    refine Finset.sum_congr rfl fun κ _ => ?_
    have h1 := Finset.mem_antidiagonal.mp ab.2
    have h2 := lam.prop
    rw [dif_pos (show ab.1.1 ≤ n by omega)]
    congr 1
    exact indMult_congr (show ab.1.2 = n - ab.1.1 by omega)
      _ _ rfl κ _ _
      (congrArg (fun x => (rowShape x).val)
        (show ab.1.2 = n - ab.1.1 by omega))

/-- The additive splitting at `t + superPS 0 1`, with the
one-column collapse and the antidiagonal reindexed over sizes. -/
private theorem diagramSchur_add_superPS_col_expand {n : ℕ}
    (lam : Shape n) (t : ℕ → ℂ) :
    diagramSchur lam.val (fun c => t c + superPS 0 1 c) =
      ∑ k ∈ Finset.range (n + 1), ∑ κ : Shape k,
        (if h : k ≤ n then
          indMult (⟨lam.val, by rw [lam.prop]; omega⟩ :
            Shape (k + (n - k))) κ (colShape (n - k))
        else 0) * diagramSchur κ.val t := by
  rw [diagramSchur_add lam.val t (superPS 0 1)]
  rw [Finset.sum_congr rfl fun ab _ => Finset.sum_congr rfl
    fun κ _ => sum_shape_superPS_col (fun ν =>
      indMult ⟨lam.val, (Finset.mem_antidiagonal.mp ab.2).symm⟩
          κ ν * diagramSchur κ.val t)]
  refine Finset.sum_bij'
    (i := fun ab _ => ab.1.1)
    (j := fun k hk => (⟨(k, lam.val.card - k),
      Finset.mem_antidiagonal.mpr (by
        have h1 := lam.prop
        have h2 := Finset.mem_range.mp hk
        omega)⟩ :
      {x // x ∈ Finset.antidiagonal lam.val.card}))
    ?_ ?_ ?_ ?_ ?_
  · intro ab _
    have h1 := Finset.mem_antidiagonal.mp ab.2
    have h2 := lam.prop
    exact Finset.mem_range.mpr (by omega)
  · intro k _
    exact Finset.mem_attach _ _
  · intro ab _
    have h1 := Finset.mem_antidiagonal.mp ab.2
    have h2 : lam.val.card - ab.1.1 = ab.1.2 := by omega
    exact Subtype.ext (show (ab.1.1, lam.val.card - ab.1.1) = ab.1
      from by rw [h2])
  · intro k _
    rfl
  · intro ab _
    refine Finset.sum_congr rfl fun κ _ => ?_
    have h1 := Finset.mem_antidiagonal.mp ab.2
    have h2 := lam.prop
    rw [dif_pos (show ab.1.1 ≤ n by omega)]
    congr 1
    exact indMult_congr (show ab.1.2 = n - ab.1.1 by omega)
      _ _ rfl κ _ _
      (congrArg (fun x => (colShape x).val)
        (show ab.1.2 = n - ab.1.1 by omega))

/-! ### Hook positivity

Building a diagram avoiding `(p, q)` by strips: the first `p` rows
are grown one horizontal strip per new even variable, the columns
of the remainder one vertical strip per new odd variable.  Every
term of the strip expansions is a natural number, and the specific
strip term is positive by induction, so the total is positive. -/

/-- A finite sum of natural values with one positive distinguished
term is a positive natural value. -/
private theorem exists_pos_nat_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℂ) (hnat : ∀ i ∈ s, ∃ m : ℕ, f i = m) (i₀ : ι)
    (hi₀ : i₀ ∈ s) (hpos : ∃ m : ℕ, 0 < m ∧ f i₀ = m) :
    ∃ M : ℕ, 0 < M ∧ ∑ i ∈ s, f i = M := by
  classical
  obtain ⟨m, hm, hfm⟩ := hpos
  obtain ⟨M', hM'⟩ := exists_nat_sum (s.erase i₀) f
    (fun i hi => hnat i (Finset.mem_of_mem_erase hi))
  refine ⟨m + M', by omega, ?_⟩
  rw [← Finset.add_sum_erase s f hi₀, hfm, hM']
  push_cast
  ring

/-- **The rows phase**: a diagram with at most `p` rows has a
positive natural Schur value at `superPS p 0`. -/
private theorem diagramSchur_superPS_pos_rows :
    ∀ (p : ℕ) (lam : YoungDiagram), lam.colLen 0 ≤ p →
      ∃ m : ℕ, 0 < m ∧ diagramSchur lam (superPS p 0) = m := by
  intro p
  induction p with
  | zero =>
      intro lam hlam
      refine ⟨1, Nat.one_pos, ?_⟩
      rw [diagramSchur_eq_det_rowLen lam (k := 0) (by omega) _]
      rw [Matrix.det_isEmpty, Nat.cast_one]
  | succ p ih =>
      intro lam hlam
      classical
      have hsplit : superPS (p + 1) 0 =
          fun c => superPS p 0 c + superPS 1 0 c :=
        (superPS_add p 0 1 0).symm
      rw [hsplit, diagramSchur_add_one_row lam (superPS p 0)]
      -- the beheaded diagram: delete the first row
      set r₀ : Fin lam.rowLens.length → ℕ :=
        fun i => lam.rowLen ((i : ℕ) + 1) with hr₀
      have hanti₀ : ∀ i j : Fin lam.rowLens.length, i ≤ j →
          r₀ j ≤ r₀ i :=
        fun i j hij => lam.rowLen_anti _ _ (Nat.succ_le_succ hij)
      have hstrip : IsHStrip lam (stripDiagram r₀) := by
        constructor
        · refine le_of_rowLen_le fun i => ?_
          rcases Nat.lt_or_ge i lam.rowLens.length with hi | hi
          · rw [stripDiagram_rowLen_lt hanti₀ ⟨i, hi⟩]
            exact lam.rowLen_anti i (i + 1) (by omega)
          · rw [stripDiagram_rowLen_le hanti₀ hi]
            omega
        · intro i
          rcases Nat.lt_or_ge i lam.rowLens.length with hi | hi
          · rw [stripDiagram_rowLen_lt hanti₀ ⟨i, hi⟩]
          · rw [stripDiagram_rowLen_le hanti₀ hi,
              rowLen_eq_zero_of_ge lam (by omega)]
      have hcol : (stripDiagram r₀).colLen 0 ≤ p := by
        have hrp : (stripDiagram r₀).rowLen p = 0 := by
          rcases Nat.lt_or_ge p lam.rowLens.length with hp | hp
          · rw [stripDiagram_rowLen_lt hanti₀ ⟨p, hp⟩]
            refine rowLen_eq_zero_of_ge lam ?_
            show lam.rowLens.length ≤ p + 1
            have hl := YoungDiagram.length_rowLens (μ := lam)
            omega
          · exact stripDiagram_rowLen_le hanti₀ hp
        by_contra hlt
        have hmem : (p, 0) ∈ stripDiagram r₀ :=
          YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
        rw [YoungDiagram.mem_iff_lt_rowLen] at hmem
        omega
      obtain ⟨m₀, hm₀, hval₀⟩ := ih (stripDiagram r₀) hcol
      -- positivity of the graded sum through the strip term
      refine exists_pos_nat_sum _ _ ?_ (stripDiagram r₀).card ?_ ?_
      · intro k _
        refine exists_nat_sum _ _ fun μ _ => ?_
        by_cases hμ : IsHStrip lam μ.val
        · rw [if_pos hμ, one_mul]
          exact diagramSchur_superPS_exists_nat p 0 μ.val
        · rw [if_neg hμ, zero_mul]
          exact ⟨0, by simp⟩
      · exact Finset.mem_range.mpr
          (Nat.lt_succ_of_le (YoungDiagram.card_le_card hstrip.1))
      · refine exists_pos_nat_sum _ _ ?_
          (⟨stripDiagram r₀, rfl⟩ : Shape (stripDiagram r₀).card)
          (Finset.mem_univ _) ?_
        · intro μ _
          by_cases hμ : IsHStrip lam μ.val
          · rw [if_pos hμ, one_mul]
            exact diagramSchur_superPS_exists_nat p 0 μ.val
          · rw [if_neg hμ, zero_mul]
            exact ⟨0, by simp⟩
        · refine ⟨m₀, hm₀, ?_⟩
          show (if IsHStrip lam (stripDiagram r₀) then (1 : ℂ)
            else 0) * diagramSchur (stripDiagram r₀)
              (superPS p 0) = (m₀ : ℂ)
          rw [if_pos hstrip, one_mul, hval₀]

/-- **Hook positivity** (Deligne 1.9, nonvanishing direction,
character side): the Schur specialisation at the super power sums
of dimension `(p, q)` of any diagram avoiding the cell `(p, q)` is
a positive natural number. -/
theorem diagramSchur_superPS_pos {p q : ℕ} (lam : YoungDiagram)
    (hcell : (p, q) ∉ lam) :
    ∃ m : ℕ, 0 < m ∧ diagramSchur lam (superPS p q) = m := by
  induction q generalizing lam with
  | zero =>
      have hcol : lam.colLen 0 ≤ p := by
        rw [YoungDiagram.mem_iff_lt_colLen] at hcell
        omega
      exact diagramSchur_superPS_pos_rows p lam hcol
  | succ q ih =>
      classical
      have hrow : lam.rowLen p ≤ q + 1 := by
        rw [YoungDiagram.mem_iff_lt_rowLen] at hcell
        omega
      have hsplit : superPS p (q + 1) =
          fun c => superPS p q c + superPS 0 1 c :=
        (superPS_add p q 0 1).symm
      rw [hsplit, diagramSchur_add_one_col lam (superPS p q)]
      -- the trimmed diagram: shave one cell off each long row
      set r₁ : Fin lam.rowLens.length → ℕ :=
        fun i => if q < lam.rowLen (i : ℕ) then
          lam.rowLen (i : ℕ) - 1 else lam.rowLen (i : ℕ) with hr₁
      have hanti₁ : ∀ i j : Fin lam.rowLens.length, i ≤ j →
          r₁ j ≤ r₁ i := by
        intro i j hij
        have h := lam.rowLen_anti (i : ℕ) (j : ℕ) hij
        show (if q < lam.rowLen (j : ℕ) then lam.rowLen (j : ℕ) - 1
            else lam.rowLen (j : ℕ)) ≤
          (if q < lam.rowLen (i : ℕ) then lam.rowLen (i : ℕ) - 1
            else lam.rowLen (i : ℕ))
        split_ifs <;> omega
      have hstrip : IsVStrip lam (stripDiagram r₁) := by
        constructor
        · refine le_of_rowLen_le fun i => ?_
          rcases Nat.lt_or_ge i lam.rowLens.length with hi | hi
          · rw [stripDiagram_rowLen_lt hanti₁ ⟨i, hi⟩]
            show (if q < lam.rowLen i then lam.rowLen i - 1
              else lam.rowLen i) ≤ lam.rowLen i
            split_ifs <;> omega
          · rw [stripDiagram_rowLen_le hanti₁ hi]
            omega
        · intro i
          rcases Nat.lt_or_ge i lam.rowLens.length with hi | hi
          · rw [stripDiagram_rowLen_lt hanti₁ ⟨i, hi⟩]
            show lam.rowLen i ≤ (if q < lam.rowLen i then
              lam.rowLen i - 1 else lam.rowLen i) + 1
            split_ifs <;> omega
          · rw [stripDiagram_rowLen_le hanti₁ hi,
              rowLen_eq_zero_of_ge lam (by omega)]
            omega
      have hnotmem : (p, q) ∉ stripDiagram r₁ := by
        have hval : (stripDiagram r₁).rowLen p ≤ q := by
          rcases Nat.lt_or_ge p lam.rowLens.length with hp | hp
          · rw [stripDiagram_rowLen_lt hanti₁ ⟨p, hp⟩]
            show (if q < lam.rowLen p then lam.rowLen p - 1
              else lam.rowLen p) ≤ q
            split_ifs <;> omega
          · rw [stripDiagram_rowLen_le hanti₁ hp]
            omega
        intro hmem
        rw [YoungDiagram.mem_iff_lt_rowLen] at hmem
        omega
      obtain ⟨m₀, hm₀, hval₀⟩ := ih (stripDiagram r₁) hnotmem
      refine exists_pos_nat_sum _ _ ?_ (stripDiagram r₁).card ?_ ?_
      · intro k _
        refine exists_nat_sum _ _ fun μ _ => ?_
        by_cases hμ : IsVStrip lam μ.val
        · rw [if_pos hμ, one_mul]
          exact diagramSchur_superPS_exists_nat p q μ.val
        · rw [if_neg hμ, zero_mul]
          exact ⟨0, by simp⟩
      · exact Finset.mem_range.mpr
          (Nat.lt_succ_of_le (YoungDiagram.card_le_card hstrip.1))
      · refine exists_pos_nat_sum _ _ ?_
          (⟨stripDiagram r₁, rfl⟩ : Shape (stripDiagram r₁).card)
          (Finset.mem_univ _) ?_
        · intro μ _
          by_cases hμ : IsVStrip lam μ.val
          · rw [if_pos hμ, one_mul]
            exact diagramSchur_superPS_exists_nat p q μ.val
          · rw [if_neg hμ, zero_mul]
            exact ⟨0, by simp⟩
        · refine ⟨m₀, hm₀, ?_⟩
          show (if IsVStrip lam (stripDiagram r₁) then (1 : ℂ)
            else 0) * diagramSchur (stripDiagram r₁)
              (superPS p q) = (m₀ : ℂ)
          rw [if_pos hstrip, one_mul, hval₀]

end RS
