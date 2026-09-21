/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.JTChar

/-!
# Zero-row padding for the Jacobi–Trudi character

When `k ≥ μ.rowLens.length`, the Jacobi–Trudi character `jtChar μ`
can equivalently be written as a sum over `Perm (Fin k)`: every
extra permutation index beyond the diagram's row count contributes
zero weight, because the guard forces it to be fixed.
-/

namespace RS

open Finset Equiv

/-! ### Row lengths vanish beyond the diagram -/

/-- `μ.rowLen i = 0` for `i ≥ μ.rowLens.length`. -/
theorem rowLen_eq_zero_of_ge (μ : YoungDiagram) {i : ℕ}
    (hi : μ.rowLens.length ≤ i) : μ.rowLen i = 0 := by
  by_contra h
  have h0 : 0 < μ.rowLen i := Nat.pos_of_ne_zero h
  have hmem : (i, 0) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr h0
  have hlt : i < μ.colLen 0 := YoungDiagram.mem_iff_lt_colLen.mp hmem
  rw [YoungDiagram.length_rowLens] at hi
  omega

/-- `μ.rowLens.get i = μ.rowLen i` (bridging `List.get` and `rowLen`). -/
theorem get_rowLens_eq_rowLen (μ : YoungDiagram)
    (i : Fin μ.rowLens.length) :
    μ.rowLens.get i = μ.rowLen (i : ℕ) := by
  rw [List.get_eq_getElem]
  exact YoungDiagram.get_rowLens

/-! ### Tail-fixing: permutations satisfying the guard fix indices
beyond the diagram -/

/-- If σ : Perm (Fin k) satisfies the nonnegativity guard and
`(i : ℕ) ≥ μ.rowLens.length`, then `σ i = i`. -/
private theorem tail_ge_of_guard (μ : YoungDiagram) {k : ℕ}
    (_hk : μ.rowLens.length ≤ k)
    (σ : Equiv.Perm (Fin k))
    (hguard : ∀ i : Fin k,
      0 ≤ (μ.rowLen (i : ℕ) : ℤ) + ((σ i : Fin k) : ℕ) - (i : ℕ))
    (j : Fin k) (hj : μ.rowLens.length ≤ (j : ℕ)) :
    (j : ℕ) ≤ (σ j : ℕ) := by
  have hr : μ.rowLen (j : ℕ) = 0 := rowLen_eq_zero_of_ge μ hj
  have := hguard j
  simp [hr] at this
  omega

/-- The guard forces a permutation to fix every index beyond the
diagram's rows: the row length there is zero, so the guard fails
unless the index is fixed. -/
theorem tail_fixed_of_guard (μ : YoungDiagram) {k : ℕ}
    (hk : μ.rowLens.length ≤ k)
    (σ : Equiv.Perm (Fin k))
    (hguard : ∀ i : Fin k,
      0 ≤ (μ.rowLen (i : ℕ) : ℤ) + ((σ i : Fin k) : ℕ) - (i : ℕ))
    (i : Fin k) (hi : μ.rowLens.length ≤ (i : ℕ)) :
    σ i = i := by
  -- Downward induction on d where (i : ℕ) + d + 1 ≥ k.
  suffices key : ∀ d : ℕ, ∀ j : Fin k,
      μ.rowLens.length ≤ (j : ℕ) → k ≤ (j : ℕ) + d + 1 → σ j = j by
    exact key (k - 1 - (i : ℕ)) i hi (by omega)
  intro d
  induction d with
  | zero =>
    intro j hj hd
    have hge := tail_ge_of_guard μ hk σ hguard j hj
    have hlt := (σ j).isLt
    have hjk : (j : ℕ) = k - 1 := by omega
    ext; omega
  | succ d ih =>
    intro j hj hd
    have hge := tail_ge_of_guard μ hk σ hguard j hj
    by_cases heq : (σ j : ℕ) = (j : ℕ)
    · exact Fin.ext heq
    · -- (σ j : ℕ) > (j : ℕ), so σ j is also a tail index
      have hgt : (j : ℕ) < (σ j : ℕ) := by omega
      have hσj_tail : μ.rowLens.length ≤ (σ j : ℕ) := by omega
      have hσj_bound : k ≤ (σ j : ℕ) + d + 1 := by omega
      -- By IH, σ (σ j) = σ j
      have hfix := ih (σ j) hσj_tail hσj_bound
      -- By injectivity, σ j = j
      exact absurd (σ.injective hfix) (by intro h; exact heq (by rw [h]))

/-! ### Restriction and extension of tail-fixing permutations -/

/-- A tail-fixing permutation maps head indices to head indices. -/
private theorem head_maps_head (μ : YoungDiagram) {k : ℕ}
    (hk : μ.rowLens.length ≤ k)
    (σ : Equiv.Perm (Fin k))
    (hfix : ∀ i : Fin k, μ.rowLens.length ≤ (i : ℕ) → σ i = i)
    (j : Fin μ.rowLens.length) :
    (σ (Fin.castLE hk j) : ℕ) < μ.rowLens.length := by
  by_contra h
  push Not at h
  have hm := hfix (σ (Fin.castLE hk j)) h
  -- hm : σ (σ (castLE j)) = σ (castLE j), i.e. σ A = σ B with A = σ(..), B =
  --   castLE j
  have hinj : σ (Fin.castLE hk j) = Fin.castLE hk j := σ.injective hm
  have hval : (Fin.castLE hk j : ℕ) = (j : ℕ) := Fin.val_castLE hk j
  rw [hinj, show (Fin.castLE hk j : Fin k).val = (j : ℕ) from hval] at h
  exact absurd j.isLt (by omega)

/-- Restrict a tail-fixing permutation to the head indices. -/
noncomputable def restrictHead (μ : YoungDiagram) {k : ℕ}
    (hk : μ.rowLens.length ≤ k)
    (σ : Equiv.Perm (Fin k))
    (hfix : ∀ i : Fin k, μ.rowLens.length ≤ (i : ℕ) → σ i = i) :
    Equiv.Perm (Fin μ.rowLens.length) where
  toFun j := ⟨(σ (Fin.castLE hk j) : ℕ), head_maps_head μ hk σ hfix j⟩
  invFun j := ⟨(σ⁻¹ (Fin.castLE hk j) : ℕ),
    head_maps_head μ hk σ⁻¹ (fun i hi => by
      have h1 := hfix i hi
      show σ.symm i = i
      rw [Equiv.symm_apply_eq]
      exact h1.symm) j⟩
  left_inv j := by
    ext; simp [Fin.val_castLE]
  right_inv j := by
    ext; simp [Fin.val_castLE]

/-- Extend a permutation of `Fin μ.rowLens.length` to `Fin k` by
fixing tail indices. -/
noncomputable def extendTail (μ : YoungDiagram) {k : ℕ}
    (hk : μ.rowLens.length ≤ k)
    (σ' : Equiv.Perm (Fin μ.rowLens.length)) :
    Equiv.Perm (Fin k) :=
  Equiv.Perm.viaEmbedding σ' (Fin.castLEEmb hk)

/-- The extension fixes the tail indices by construction. -/
theorem extendTail_fixes_tail (μ : YoungDiagram) {k : ℕ}
    (hk : μ.rowLens.length ≤ k)
    (σ' : Equiv.Perm (Fin μ.rowLens.length))
    (i : Fin k) (hi : μ.rowLens.length ≤ (i : ℕ)) :
    extendTail μ hk σ' i = i := by
  unfold extendTail
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  intro ⟨j, hj⟩
  have : (Fin.castLEEmb hk j : ℕ) = (j : ℕ) := rfl
  rw [show Fin.castLEEmb hk j = i from hj] at this
  omega

/-- On head indices it acts as the permutation extended. -/
theorem extendTail_apply (μ : YoungDiagram) {k : ℕ}
    (hk : μ.rowLens.length ≤ k)
    (σ' : Equiv.Perm (Fin μ.rowLens.length))
    (j : Fin μ.rowLens.length) :
    extendTail μ hk σ' (Fin.castLE hk j) = Fin.castLE hk (σ' j) := by
  unfold extendTail
  have : (Fin.castLEEmb hk) j = Fin.castLE hk j := rfl
  rw [← this]
  have : (Fin.castLEEmb hk) (σ' j) = Fin.castLE hk (σ' j) := rfl
  rw [← this]
  exact Equiv.Perm.viaEmbedding_apply σ' (Fin.castLEEmb hk) j

/-- Restricting an extension recovers the permutation. -/
theorem restrictHead_extendTail (μ : YoungDiagram) {k : ℕ}
    (hk : μ.rowLens.length ≤ k)
    (σ' : Equiv.Perm (Fin μ.rowLens.length)) :
    restrictHead μ hk (extendTail μ hk σ')
      (extendTail_fixes_tail μ hk σ') = σ' := by
  ext j
  simp [restrictHead, extendTail_apply μ hk σ' j, Fin.val_castLE]

/-- And extending a restriction recovers the tail-fixing
permutation: the two are inverse. -/
theorem extendTail_restrictHead (μ : YoungDiagram) {k : ℕ}
    (hk : μ.rowLens.length ≤ k)
    (σ : Equiv.Perm (Fin k))
    (hfix : ∀ i : Fin k, μ.rowLens.length ≤ (i : ℕ) → σ i = i) :
    extendTail μ hk (restrictHead μ hk σ hfix) = σ := by
  ext i
  by_cases hi : (i : ℕ) < μ.rowLens.length
  · -- Head index: use extendTail_apply + restrictHead def
    have heq : i = Fin.castLE hk ⟨(i : ℕ), hi⟩ := by ext; simp
    rw [heq, extendTail_apply]
    simp [restrictHead]
  · -- Tail index: both sides fix it
    push Not at hi
    rw [extendTail_fixes_tail μ hk _ i hi, hfix i hi]

/-! ### Sign preservation -/

/-- Extension preserves sign, fixing the added indices. -/
theorem sign_extendTail (μ : YoungDiagram) {k : ℕ}
    (hk : μ.rowLens.length ≤ k)
    (σ' : Equiv.Perm (Fin μ.rowLens.length)) :
    Equiv.Perm.sign (extendTail μ hk σ') = Equiv.Perm.sign σ' := by
  simp only [extendTail, Equiv.Perm.viaEmbedding]
  rw [Equiv.Perm.sign_extendDomain]

/-! ### colourChar extension by zeros -/

/-- If `fibreCard g j = 0` for all j beyond N, then g maps into Fin N. -/
private theorem range_lt_of_fibreCard_zero {n k : ℕ} {N : ℕ}
    (g : Fin n → Fin k)
    (hfib : ∀ j : Fin k, N ≤ (j : ℕ) → fibreCard g j = 0)
    (x : Fin n) : (g x : ℕ) < N := by
  by_contra h
  push Not at h
  have hcard := hfib (g x) h
  rw [fibreCard] at hcard
  have hmem : x ∈ (Finset.univ.filter fun y => g y = g x) := by
    simp [Finset.mem_filter]
  rw [Finset.card_eq_zero.mp hcard] at hmem
  simp at hmem

open scoped Classical in
/-- `colourChar` is invariant under extending the composition by
zeros. -/
theorem colourChar_extend_zero {n N k : ℕ} (hNk : N ≤ k)
    (α : Fin N → ℕ) (_hsum : ∑ j : Fin N, α j = n)
    (π : Equiv.Perm (Fin n)) :
    colourChar α π =
      colourChar
        (fun i : Fin k => if h : (i : ℕ) < N then α ⟨i, h⟩ else 0)
        π := by
  classical
  let β : Fin k → ℕ := fun i => if h : (i : ℕ) < N then α ⟨i, h⟩ else 0
  show colourChar α π = colourChar β π
  unfold colourChar
  -- Helper: extended fibre condition forces range into first N
  have range_bound : ∀ g : Fin n → Fin k,
      (∀ j, fibreCard g j = β j) → ∀ x, (g x : ℕ) < N := by
    intro g hfib x
    exact range_lt_of_fibreCard_zero g (fun j hj => by
      have := hfib j
      simp only [β, dif_neg (by omega : ¬ (j : ℕ) < N)] at this
      exact this) x
  -- Key lemma: fibreCard of castLE ∘ g at a head index
  have fwd_fib_head : ∀ (g : Fin n → Fin N) (j : Fin N),
      fibreCard (Fin.castLE hNk ∘ g) (Fin.castLE hNk j) = fibreCard g j := by
    intro g j
    simp only [fibreCard.eq_1]
    congr 1; ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp]
    rw [Fin.ext_iff, Fin.ext_iff]
    simp [Fin.val_castLE]
  -- Key lemma: fibreCard of castLE ∘ g at a tail index
  have fwd_fib_tail : ∀ (g : Fin n → Fin N) (j : Fin k),
      ¬ (j : ℕ) < N → fibreCard (Fin.castLE hNk ∘ g) j = 0 := by
    intro g j hj
    simp only [fibreCard.eq_1]
    apply Finset.card_eq_zero.mpr
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp]
    constructor
    · intro h
      have := congrArg Fin.val h
      simp [Fin.val_castLE] at this
      exact absurd (this ▸ (g x).isLt) (by omega)
    · intro h; exact absurd h (by simp)
  -- Key lemma: fibreCard of restriction
  have bwd_fib : ∀ (g : Fin n → Fin k) (hb : ∀ x, (g x : ℕ) < N) (j : Fin N),
      fibreCard (fun x => (⟨(g x : ℕ), hb x⟩ : Fin N)) j =
        fibreCard g (Fin.castLE hNk j) := by
    intro g hb j
    simp only [fibreCard.eq_1]
    congr 1; ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Fin.ext_iff, Fin.ext_iff]
    simp [Fin.val_castLE]
  -- Helper: extract backward map as a standalone function
  let bwd_map : ∀ (g : Fin n → Fin k),
      (∀ j, fibreCard g j = β j) →
      Fin n → Fin N :=
    fun g hfib x => ⟨(g x : ℕ), range_bound g hfib x⟩
  apply Finset.card_bij'
    (fun g _ => Fin.castLE hNk ∘ g)
    (fun g hg => bwd_map g (Finset.mem_filter.mp hg).2.1)
  · -- Goal 1: hj (backward preserves filter)
    -- g : Fin n → Fin k, need bwd_map g ... ∈ s
    intro g hg
    have hfilt := (Finset.mem_filter.mp hg).2
    have hb : ∀ x, (g x : ℕ) < N := range_bound g hfilt.1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro j
      show fibreCard (fun x => (⟨(g x : ℕ), hb x⟩ : Fin N)) j = α j
      rw [bwd_fib g hb j]
      have hβ : β (Fin.castLE hNk j) = α j := by
        show (if h : (Fin.castLE hNk j : ℕ) < N then α ⟨(Fin.castLE hNk j : ℕ),
          h⟩ else 0) = α j
        have hlt : (Fin.castLE hNk j : ℕ) < N := by
          rw [Fin.val_castLE hNk j]; exact j.isLt
        rw [dif_pos hlt, show (⟨(Fin.castLE hNk j : ℕ), hlt⟩ : Fin N) = j from
          Fin.ext (Fin.val_castLE hNk j)]
      rw [← hβ]
      exact hfilt.1 (Fin.castLE hNk j)
    · show (fun x => (⟨(g x : ℕ), hb x⟩ : Fin N)) ∘ ↑π = fun x => ⟨(g x : ℕ), hb
      x⟩
      ext x
      simp only [Function.comp]
      exact congrArg Fin.val (congr_fun hfilt.2 x)
  · -- Goal 2: left_inv (bwd_map (castLE ∘ g) ... = g)
    intro g hg
    ext x
    simp only [bwd_map, Function.comp, Fin.val_castLE]
  · -- Goal 3: right_inv (castLE ∘ bwd_map g ... = g)
    intro g hg
    have hfilt := (Finset.mem_filter.mp hg).2
    ext x
    simp only [bwd_map, Function.comp, Fin.val_castLE]
  · -- Goal 4: hi (forward preserves filter)
    -- g : Fin n → Fin N, need castLE ∘ g ∈ t
    intro g hg
    have hfilt := (Finset.mem_filter.mp hg).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro j
      show fibreCard (Fin.castLE hNk ∘ g) j =
        (if h : (j : ℕ) < N then α ⟨(j : ℕ), h⟩ else 0)
      by_cases hj : (j : ℕ) < N
      · rw [dif_pos hj]
        have heq : j = Fin.castLE hNk ⟨(j : ℕ), hj⟩ := by ext; simp
        calc fibreCard (Fin.castLE hNk ∘ g) j
            = fibreCard (Fin.castLE hNk ∘ g) (Fin.castLE hNk ⟨(j : ℕ), hj⟩)
              := by rw [← heq]
          _ = fibreCard g ⟨(j : ℕ), hj⟩ := fwd_fib_head g ⟨(j : ℕ), hj⟩
          _ = α ⟨(j : ℕ), hj⟩ := hfilt.1 ⟨(j : ℕ), hj⟩
      · rw [dif_neg hj]
        exact fwd_fib_tail g j hj
    · ext x
      simp only [Function.comp]
      exact congrArg Fin.val (congrArg (Fin.castLE hNk) (congr_fun hfilt.2 x))

/-! ### Main theorem -/

open scoped Classical in
/-- **The padded Jacobi–Trudi character**: summing over `Perm (Fin k)`
for any `k` at least the row count gives the same value, the extra
indices contributing only through the terms their guard admits. -/
theorem jtChar_pad (μ : YoungDiagram) {k : ℕ}
    (hk : μ.rowLens.length ≤ k) (π : Equiv.Perm (Fin μ.card)) :
    jtChar μ π =
      ∑ σ : Equiv.Perm (Fin k),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) *
          (if ∀ i : Fin k,
              0 ≤ (μ.rowLen (i : ℕ) : ℤ) + ((σ i : Fin k) : ℕ) - (i : ℕ)
            then (colourChar
              (fun i : Fin k =>
                ((μ.rowLen (i : ℕ) : ℤ) + ((σ i : Fin k) : ℕ) -
                  (i : ℕ)).toNat) π : ℂ)
            else 0)
    := by
  classical
  -- ═══════ SETUP: THE BIG TERM AND THE TAIL-FIXING PREDICATE ═══════
  set n := μ.rowLens.length with hn_def
  -- The "big term" for σ : Perm (Fin k)
  let bigTerm (σ : Equiv.Perm (Fin k)) : ℂ :=
    ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      (if ∀ i : Fin k,
          0 ≤ (μ.rowLen (i : ℕ) : ℤ) + ((σ i : Fin k) : ℕ) - (i : ℕ)
        then (colourChar
          (fun i : Fin k =>
            ((μ.rowLen (i : ℕ) : ℤ) + ((σ i : Fin k) : ℕ) -
              (i : ℕ)).toNat) π : ℂ)
        else 0)
  -- The tail-fixing predicate
  let tailFix (σ : Equiv.Perm (Fin k)) : Prop :=
    ∀ i : Fin k, n ≤ (i : ℕ) → σ i = i
  -- ═══════ STAGE 1: NON-TAIL-FIXING TERMS VANISH ═══════
  have vanish : ∀ σ : Equiv.Perm (Fin k), ¬ tailFix σ → bigTerm σ = 0 := by
    intro σ hσ
    show bigTerm σ = 0
    simp only [bigTerm]
    rw [show (if ∀ i : Fin k, 0 ≤ (μ.rowLen (i : ℕ) : ℤ) + ((σ i : Fin k) : ℕ) -
      (i : ℕ)
      then _ else (0 : ℂ)) = 0 from by
      rw [if_neg]
      intro hguard
      exact hσ (fun i hi => tail_fixed_of_guard μ hk σ hguard i (hn_def ▸ hi))]
    simp
  -- ═══════ STAGE 2: RESTRICT THE SUM TO THE TAIL-FIXING TERMS ═══════
  have filter_eq : ∑ σ : Equiv.Perm (Fin k), bigTerm σ =
      ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin k) => tailFix σ),
        bigTerm σ := by
    symm
    exact Finset.sum_filter_of_ne (fun σ _ hne =>
      by_contra fun h => hne (vanish σ h))
  -- ═══════ STAGE 3: THE SIGNED VALUE OF AN EXTENDED PERMUTATION ═══════
  have signed_eq : ∀ (σ' : Equiv.Perm (Fin n)) (i : Fin k),
      (μ.rowLen (i : ℕ) : ℤ) + ((extendTail μ hk σ' i : ℕ) : ℤ) - ((i : ℕ) : ℤ)
        =
      if h : (i : ℕ) < n then jtSigned μ σ' ⟨(i : ℕ), h⟩ else 0 := by
    intro σ' i
    by_cases hi : (i : ℕ) < n
    · rw [dif_pos hi]
      have heqi : i = Fin.castLE hk ⟨(i : ℕ), hi⟩ :=
        Fin.ext (Fin.val_castLE hk ⟨(i : ℕ), hi⟩).symm
      have hext : (extendTail μ hk σ' i : ℕ) = (σ' ⟨(i : ℕ), hi⟩ : ℕ) := by
        conv_lhs => rw [heqi, extendTail_apply]
        exact Fin.val_castLE hk _
      have hrow : μ.rowLen (i : ℕ) = μ.rowLens.get ⟨(i : ℕ), hi⟩ :=
        (get_rowLens_eq_rowLen μ ⟨(i : ℕ), hi⟩).symm
      simp only [jtSigned, hext, hrow]
    · rw [dif_neg hi]
      push Not at hi
      rw [extendTail_fixes_tail μ hk σ' i hi, rowLen_eq_zero_of_ge μ hi]
      simp
  -- Guard equivalence
  have guard_iff : ∀ σ' : Equiv.Perm (Fin n),
      (∀ i : Fin k,
        0 ≤ (μ.rowLen (i : ℕ) : ℤ) + ((extendTail μ hk σ' i : ℕ) : ℤ) - ((i : ℕ)
          : ℤ)) ↔
      (∀ j : Fin n, 0 ≤ jtSigned μ σ' j) := by
    intro σ'
    constructor
    · intro hbig j
      have h1 := hbig (Fin.castLE hk j)
      rw [signed_eq] at h1
      rwa [dif_pos (show (Fin.castLE hk j : ℕ) < n from by
              rw [Fin.val_castLE]; exact j.isLt),
           show (⟨(Fin.castLE hk j : ℕ), _⟩ : Fin n) = j from
              Fin.ext (Fin.val_castLE hk j)] at h1
    · intro hsmall i
      rw [signed_eq]
      split
      · next hi => exact hsmall ⟨(i : ℕ), hi⟩
      · exact le_refl 0
  -- Composition equality under guard
  have comp_eq : ∀ (σ' : Equiv.Perm (Fin n)),
      (∀ j : Fin n, 0 ≤ jtSigned μ σ' j) →
      colourChar
        (fun i : Fin k =>
          ((μ.rowLen (i : ℕ) : ℤ) + ((extendTail μ hk σ' i : ℕ) : ℤ) -
            ((i : ℕ) : ℤ)).toNat) π =
      colourChar (jtComp μ σ') π := by
    intro σ' hguard
    rw [colourChar_extend_zero hk (jtComp μ σ') (sum_jtComp μ σ' hguard) π]
    congr 1; ext i
    have hsig := signed_eq σ' i
    by_cases hi : (i : ℕ) < n
    · rw [dif_pos hi] at hsig; rw [dif_pos hi, hsig]; rfl
    · rw [dif_neg hi] at hsig; rw [dif_neg hi, hsig]; simp
  -- ═══════ ASSEMBLY ═══════
  calc jtChar μ π
      = ∑ σ' : Equiv.Perm (Fin n),
          ((Equiv.Perm.sign σ' : ℤ) : ℂ) *
            (if ∀ i, 0 ≤ jtSigned μ σ' i
              then (colourChar (jtComp μ σ') π : ℂ) else 0) := by
        rfl
    _ = ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin k) => tailFix σ),
          bigTerm σ := by
        apply Finset.sum_nbij'
          (fun σ' => extendTail μ hk σ')
          (fun σ => if h : tailFix σ then restrictHead μ hk σ h else 1)
        · -- hi: extendTail maps univ into filter
          intro σ' _
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact fun i hi => extendTail_fixes_tail μ hk σ' i hi
        · -- hj: j_map maps filter into univ
          intro _ _; exact Finset.mem_univ _
        · -- left_inv
          intro σ' _
          have hfix : tailFix (extendTail μ hk σ') :=
            fun i hi => extendTail_fixes_tail μ hk σ' i hi
          rw [dif_pos hfix]
          exact restrictHead_extendTail μ hk σ'
        · -- right_inv
          intro σ hσ
          rw [dif_pos (Finset.mem_filter.mp hσ).2]
          exact extendTail_restrictHead μ hk σ (Finset.mem_filter.mp hσ).2
        · -- term matching
          intro σ' _
          show ((Equiv.Perm.sign σ' : ℤ) : ℂ) *
              (if ∀ i, 0 ≤ jtSigned μ σ' i
                then (colourChar (jtComp μ σ') π : ℂ) else 0) =
            bigTerm (extendTail μ hk σ')
          simp only [bigTerm]
          rw [show Equiv.Perm.sign (extendTail μ hk σ') = Equiv.Perm.sign σ'
            from
            sign_extendTail μ hk σ']
          congr 1
          by_cases hguard : ∀ i, 0 ≤ jtSigned μ σ' i
          · rw [if_pos hguard, if_pos ((guard_iff σ').mpr hguard)]
            exact_mod_cast (comp_eq σ' hguard).symm
          · rw [if_neg hguard,
                 if_neg (fun h => hguard ((guard_iff σ').mp h))]
    _ = ∑ σ, bigTerm σ := filter_eq.symm

end RS
