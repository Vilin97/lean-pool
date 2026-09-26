/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BetaDiag
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ModelPermCoord

/-!
# The diagonal cap pairing equals the colour pairing

The diagonal cap pairing `betaDiag m c` on a colouring
`c : MixedColouring k ℓ (m + m)` equals the tensor-power
pairing `betaColour` applied to the two halves of `c`.
-/

@[expose] public section

namespace RS

open Finset

variable {k ℓ : ℕ}

/-! ### Helper lemmas: peelColour and halves -/

/-- The first half of the first half of the peeled colouring
agrees with the original colouring on low positions. -/
private theorem peelFirstHalf_firstHalf (m : ℕ)
    (c : MixedColouring k ℓ ((m + 1) + (m + 1))) :
    MixedColouring.firstHalf (a := m) (b := m)
      (MixedColouring.firstHalf (a := m + m) (b := 2)
        (peelColour m c)) =
    fun (i : Fin m) => c ⟨i.val, by omega⟩ := by
  funext i
  change peelColour m c ⟨i.val, by omega⟩ = c ⟨i.val, by omega⟩
  rw [peelColour_low m c ⟨i.val, by omega⟩ i.isLt]

/-- The second half of the first half of the peeled colouring
agrees with the shifted original colouring. -/
private theorem peelFirstHalf_secondHalf (m : ℕ)
    (c : MixedColouring k ℓ ((m + 1) + (m + 1))) :
    MixedColouring.secondHalf (a := m) (b := m)
      (MixedColouring.firstHalf (a := m + m) (b := 2)
        (peelColour m c)) =
    fun (j : Fin m) => c ⟨(m + 1) + j.val, by omega⟩ := by
  funext j
  change peelColour m c ⟨m + j.val, by omega⟩ =
    c ⟨(m + 1) + j.val, by omega⟩
  rw [peelColour_apply]
  refine congrArg c (Fin.ext ?_)
  change capPeelInv m (m + j.val) = (m + 1) + j.val
  unfold capPeelInv; split_ifs <;> omega

/-- The peeled pair's first entry is c at position m. -/
private theorem peelSecondHalf_zero (m : ℕ)
    (c : MixedColouring k ℓ ((m + 1) + (m + 1))) :
    MixedColouring.secondHalf (a := m + m) (b := 2)
      (peelColour m c) 0 = c ⟨m, by omega⟩ := by
  change peelColour m c ⟨(m + m) + 0, by omega⟩ = c ⟨m, by omega⟩
  rw [peelColour_apply]
  refine congrArg c (Fin.ext ?_)
  change capPeelInv m ((m + m) + 0) = m
  unfold capPeelInv; split_ifs <;> omega

/-- The peeled pair's second entry is c at position (m+1)+m. -/
private theorem peelSecondHalf_one (m : ℕ)
    (c : MixedColouring k ℓ ((m + 1) + (m + 1))) :
    MixedColouring.secondHalf (a := m + m) (b := 2)
      (peelColour m c) 1 = c ⟨(m + 1) + m, by omega⟩ :=
  peelColour_pairSnd m c

/-! ### Relating halves of c to halves of peeled firstHalf -/

/-- The first half of c at `Fin.castSucc i` agrees with the
peeled firstHalf's firstHalf at `i`. -/
private theorem firstHalf_castSucc_eq (m : ℕ)
    (c : MixedColouring k ℓ ((m + 1) + (m + 1)))
    (i : Fin m) :
    MixedColouring.firstHalf (a := m + 1) (b := m + 1) c
      (Fin.castSucc i) =
    MixedColouring.firstHalf (a := m) (b := m)
      (MixedColouring.firstHalf (a := m + m) (b := 2)
        (peelColour m c)) i := by
  change c ⟨(Fin.castSucc i).val, by omega⟩ = _
  rw [peelFirstHalf_firstHalf]
  exact congrArg c (Fin.ext rfl)

/-- The second half of c at `Fin.castSucc j` agrees with the
peeled firstHalf's secondHalf at `j`. -/
private theorem secondHalf_castSucc_eq (m : ℕ)
    (c : MixedColouring k ℓ ((m + 1) + (m + 1)))
    (j : Fin m) :
    MixedColouring.secondHalf (a := m + 1) (b := m + 1) c
      (Fin.castSucc j) =
    MixedColouring.secondHalf (a := m) (b := m)
      (MixedColouring.firstHalf (a := m + m) (b := 2)
        (peelColour m c)) j := by
  change c ⟨(m + 1) + (Fin.castSucc j).val, by omega⟩ = _
  rw [peelFirstHalf_secondHalf]
  exact congrArg c (Fin.ext rfl)

/-- The first half of c at the last position is c at m. -/
private theorem firstHalf_last (m : ℕ)
    (c : MixedColouring k ℓ ((m + 1) + (m + 1))) :
    MixedColouring.firstHalf (a := m + 1) (b := m + 1) c
      (Fin.last m) = c ⟨m, by omega⟩ :=
  congrArg c (Fin.ext rfl)

/-- The second half of c at the last position. -/
private theorem secondHalf_last' (m : ℕ)
    (c : MixedColouring k ℓ ((m + 1) + (m + 1))) :
    MixedColouring.secondHalf (a := m + 1) (b := m + 1) c
      (Fin.last m) = c ⟨(m + 1) + m, by omega⟩ :=
  congrArg c (Fin.ext rfl)

/-! ### Product splitting -/

/-- The entry product over Fin (m+1) splits as the m-product
times the last entry, with the m-product matching the peeled
induction hypothesis. -/
private theorem prod_entry_split (m : ℕ)
    (c : MixedColouring k ℓ ((m + 1) + (m + 1))) :
    ∏ i : Fin (m + 1),
      colourFormEntry k ℓ
        (MixedColouring.firstHalf (a := m + 1) (b := m + 1) c i)
        (MixedColouring.secondHalf (a := m + 1) (b := m + 1) c i) =
    (∏ i : Fin m,
      colourFormEntry k ℓ
        (MixedColouring.firstHalf (a := m) (b := m)
          (MixedColouring.firstHalf (a := m + m) (b := 2)
            (peelColour m c)) i)
        (MixedColouring.secondHalf (a := m) (b := m)
          (MixedColouring.firstHalf (a := m + m) (b := 2)
            (peelColour m c)) i)) *
    colourFormEntry k ℓ
      (MixedColouring.secondHalf (a := m + m) (b := 2)
        (peelColour m c) 0)
      (MixedColouring.secondHalf (a := m + m) (b := 2)
        (peelColour m c) 1) := by
  rw [Fin.prod_univ_castSucc]
  congr 1
  · exact Finset.prod_congr rfl (fun i _hi => by
      rw [firstHalf_castSucc_eq, secondHalf_castSucc_eq])
  · rw [firstHalf_last, secondHalf_last',
      peelSecondHalf_zero, peelSecondHalf_one]

/-! ### Mixed pair lemmas -/

/-- Mixed-type entry is zero. -/
private theorem colourFormEntry_zero_of_isRight_ne
    (a : Fin k ⊕ Fin (2 * ℓ)) (b : Fin k ⊕ Fin (2 * ℓ))
    (h : a.isRight ≠ b.isRight) :
    colourFormEntry k ℓ a b = 0 := by
  rcases a with _ | _ <;> rcases b with _ | _ <;>
    simp [colourFormEntry] <;> simp_all

/-! ### The dite-false branch: betaDiag vanishes -/

/-- If the peeled first half is not even and there exists a mixed
pair, then betaColour is zero. The contrapositive: if all pairs
match, the peeled first half is even. -/
private theorem peelFirstHalf_isEven_of_matching (m : ℕ)
    (c : MixedColouring k ℓ ((m + 1) + (m + 1)))
    (hmatch : ∀ i : Fin (m + 1),
      (MixedColouring.firstHalf (a := m + 1) (b := m + 1)
        c i).isRight =
      (MixedColouring.secondHalf (a := m + 1) (b := m + 1)
        c i).isRight) :
    MixedColouring.IsEven
      (MixedColouring.firstHalf (a := m + m) (b := 2)
        (peelColour m c)) := by
  unfold MixedColouring.IsEven
  rw [MixedColouring.oddSet_card_split (a := m) (b := m)]
  rw [peelFirstHalf_firstHalf, peelFirstHalf_secondHalf]
  apply Nat.even_add.mpr
  have hcard :
      (MixedColouring.oddSet
        (fun i : Fin m => c ⟨i.val, by omega⟩)).card =
      (MixedColouring.oddSet
        (fun j : Fin m => c ⟨(m + 1) + j.val, by omega⟩)).card := by
    have hmatch' : ∀ i : Fin m,
        (c ⟨i.val, by omega⟩).isRight =
        (c ⟨(m + 1) + i.val, by omega⟩).isRight := by
      intro i
      have := hmatch (Fin.castSucc i)
      -- this : (c.firstHalf (castSucc i)).isRight =
      --        (c.secondHalf (castSucc i)).isRight
      exact this
    refine Finset.card_bij (fun i _hi => i) ?_ ?_ ?_
    · intro i hi
      simp only [MixedColouring.oddSet, mem_filter, mem_univ,
        true_and] at hi ⊢
      rwa [← hmatch' i]
    · intro _ _ _ _ h; exact h
    · intro j hj
      refine ⟨j, ?_, rfl⟩
      simp only [MixedColouring.oddSet, mem_filter, mem_univ,
        true_and] at hj ⊢
      rwa [hmatch' j]
  constructor <;> intro h <;> [rwa [hcard] at h; rwa [← hcard] at h]

/-! ### Sign identity -/

/-- The peelColour composed with finCongr and capPeelPerm
recovers the original colouring. -/
private theorem peelColour_finCongr_capPeelPerm (m : ℕ)
    (c : MixedColouring k ℓ ((m + 1) + (m + 1)))
    (x : Fin ((m + 1) + (m + 1))) :
    (peelColour m c ∘ ⇑(finCongr (capPeelArity m)))
      (capPeelPerm m x) = c x :=
  congr_fun (peelColour_spec m c) x

/-- The word-sign factor composed with the koszul sign of the
peeled halves gives the koszul sign of the (m+1)-halves.

Proved via the identity:
  oddInversions + koszulCrossings(m) = koszulCrossings(m+1)
both sides counting pairs in Fin((m+1)+(m+1)) weighted by the
inversions of capPeelPerm and the position-parity conditions. -/
private theorem sign_eq (m : ℕ)
    (c : MixedColouring k ℓ ((m + 1) + (m + 1)))
    (_hmatch : ∀ i : Fin (m + 1),
      (MixedColouring.firstHalf (a := m + 1) (b := m + 1)
        c i).isRight =
      (MixedColouring.secondHalf (a := m + 1) (b := m + 1)
        c i).isRight) :
    (-1 : ℂ) ^ oddInversions (capPeelPerm m)
        (peelColour m c ∘ ⇑(finCongr (capPeelArity m))) *
      ((-1 : ℂ) ^ koszulCrossings
        (MixedColouring.firstHalf (a := m) (b := m)
          (MixedColouring.firstHalf (a := m + m) (b := 2)
            (peelColour m c)))
        (MixedColouring.secondHalf (a := m) (b := m)
          (MixedColouring.firstHalf (a := m + m) (b := 2)
            (peelColour m c)))) =
    (-1 : ℂ) ^ koszulCrossings
      (MixedColouring.firstHalf (a := m + 1) (b := m + 1) c)
      (MixedColouring.secondHalf (a := m + 1) (b := m + 1) c) := by
  rw [← pow_add]; congr 1
  -- ═══════ STAGE 1: THE INVERSIONS OF THE PEEL PERMUTATION ═══════
  -- Characterize inversions of capPeelPerm:
  -- the only pairs (a,b) with a<b, σ(a)>σ(b) have a.val=m, m+1≤b.val≤m+m.
  have hinv : ∀ (a b : Fin ((m + 1) + (m + 1))),
      a < b → capPeelPerm m a > capPeelPerm m b →
      a.val = m ∧ m + 1 ≤ b.val ∧ b.val ≤ m + m := by
    intro a b hab hgt
    have ha := a.isLt; have hb := b.isLt
    have hva : (capPeelPerm m a).val = capPeelFun m a.val := by
      unfold capPeelPerm capPeelRotation
      simp [Equiv.trans_apply, capPeelFun, finCongr_apply]
    have hvb : (capPeelPerm m b).val = capPeelFun m b.val := by
      unfold capPeelPerm capPeelRotation
      simp [Equiv.trans_apply, capPeelFun, finCongr_apply]
    have hab' : a.val < b.val := hab
    have hgt' : (capPeelPerm m b).val <
        (capPeelPerm m a).val := hgt
    rw [hva, hvb] at hgt'
    unfold capPeelFun at hgt'
    split_ifs at hgt' <;> refine ⟨?_, ?_, ?_⟩ <;> omega
  have hdc := peelColour_finCongr_capPeelPerm m c
  -- Precompute σ values at key positions
  have hσm : (capPeelPerm m (⟨m, by omega⟩ :
      Fin ((m + 1) + (m + 1)))).val = m + m := by
    unfold capPeelPerm capPeelRotation
    simp [Equiv.trans_apply, capPeelFun, finCongr_apply]
  have hσi : ∀ (i : Fin m),
      (capPeelPerm m (⟨(m + 1) + i.val, by omega⟩ :
        Fin ((m + 1) + (m + 1)))).val = m + i.val := by
    intro i
    unfold capPeelPerm capPeelRotation
    simp [Equiv.trans_apply, capPeelFun, finCongr_apply]
    split_ifs <;> omega
  -- Abbreviate KC_{m+1} arguments
  set fHc := MixedColouring.firstHalf (a := m + 1)
    (b := m + 1) c with hfHc_def
  set sHc := MixedColouring.secondHalf (a := m + 1)
    (b := m + 1) c with hsHc_def
  -- ═══════ STAGE 2: SPLIT THE CROSSING SET AT THE PEELED SLOT ═══════
  -- Partition the KC_{m+1} filter by p.2 = last m
  set Kbig : Finset (Fin (m + 1) × Fin (m + 1)) :=
    univ.filter fun p =>
      p.1 < p.2 ∧ (fHc p.2).isRight ∧ (sHc p.1).isRight
  have hKC_eq : koszulCrossings fHc sHc = Kbig.card := rfl
  set Kinner := Kbig.filter fun p => p.2 ≠ Fin.last m
  set Kbdry := Kbig.filter fun p => p.2 = Fin.last m
  have hsplit : Kbig.card = Kinner.card + Kbdry.card := by
    rw [← card_union_of_disjoint
      (disjoint_filter.mpr fun _ _ h1 h2 => h1 h2)]
    congr 1; ext x
    simp only [mem_union, mem_filter]
    exact ⟨fun hx => if h : x.2 = Fin.last m
        then Or.inr ⟨hx, h⟩ else Or.inl ⟨hx, h⟩,
      fun h => h.elim (·.1) (·.1)⟩
  -- ═══════ STAGE 3: THE INTERIOR IS THE SMALLER CROSSING SET ═══════
  -- Kinner.card = KC_m via castSucc bijection
  have hinner : koszulCrossings
      (MixedColouring.firstHalf (a := m) (b := m)
        (MixedColouring.firstHalf (a := m + m) (b := 2)
          (peelColour m c)))
      (MixedColouring.secondHalf (a := m) (b := m)
        (MixedColouring.firstHalf (a := m + m) (b := 2)
          (peelColour m c))) = Kinner.card := by
    unfold koszulCrossings
    refine card_bij
      (fun p _hp => ((Fin.castSucc p.1, Fin.castSucc p.2) :
        Fin (m + 1) × Fin (m + 1))) ?_ ?_ ?_
    · intro ⟨i, j⟩ hp
      simp only [mem_filter, mem_univ, true_and] at hp
      refine mem_filter.mpr ⟨mem_filter.mpr
        ⟨mem_univ _, hp.1, ?_, ?_⟩, ?_⟩
      · rw [hfHc_def, firstHalf_castSucc_eq]; exact hp.2.1
      · rw [hsHc_def, secondHalf_castSucc_eq]; exact hp.2.2
      · intro h; have : j.val = m := congrArg Fin.val h
        omega
    · intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h
      exact Prod.ext
        (Fin.castSucc_injective _ (congrArg Prod.fst h))
        (Fin.castSucc_injective _ (congrArg Prod.snd h))
    · intro ⟨i, j⟩ hp
      have hp' := mem_filter.mp hp
      have hp'' := (mem_filter.mp hp'.1).2
      have hj_lt : j.val < m := by
        rcases Nat.lt_or_eq_of_le
          (Nat.lt_succ_iff.mp j.isLt) with h | h
        · exact h
        · exact absurd (Fin.ext h) hp'.2
      have hi_lt : i.val < m := Nat.lt_trans hp''.1 hj_lt
      refine ⟨(⟨i.val, hi_lt⟩, ⟨j.val, hj_lt⟩), ?_, ?_⟩
      · simp only [mem_filter, mem_univ, true_and]
        exact ⟨hp''.1,
          by rw [← firstHalf_castSucc_eq m c
               ⟨j.val, hj_lt⟩, ← hfHc_def]; exact hp''.2.1,
          by rw [← secondHalf_castSucc_eq m c
               ⟨i.val, hi_lt⟩, ← hsHc_def]; exact hp''.2.2⟩
      · exact Prod.ext (Fin.ext rfl) (Fin.ext rfl)
  -- ═══════ STAGE 4: THE BOUNDARY IS THE INVERSION COUNT ═══════
  -- Kbdry.card = OI via inversion bijection
  have hbdry : oddInversions (capPeelPerm m)
      (peelColour m c ∘ ⇑(finCongr (capPeelArity m))) =
      Kbdry.card := by
    unfold oddInversions
    refine card_bij
      (fun p _hp =>
        ((⟨p.2.val - (m + 1), by have := p.2.isLt; omega⟩ :
            Fin (m + 1)),
         Fin.last m)) ?_ ?_ ?_
    · intro ⟨a, b⟩ hp
      simp only [mem_filter, mem_univ, true_and] at hp
      obtain ⟨hab, hgt, hr1, hr2⟩ := hp
      obtain ⟨ha_eq, hb_lo, hb_hi⟩ := hinv a b hab hgt
      refine mem_filter.mpr ⟨mem_filter.mpr
        ⟨mem_univ _, ?_, ?_, ?_⟩, rfl⟩
      · change b.val - (m + 1) < m; omega
      · have hca : (c a).isRight := by rw [← hdc]; exact hr1
        have ha_fin : (⟨m, by omega⟩ :
            Fin ((m + 1) + (m + 1))) = a :=
          (Fin.ext ha_eq).symm
        rw [hfHc_def, firstHalf_last, ha_fin]; exact hca
      · have hcb : (c b).isRight := by rw [← hdc]; exact hr2
        have hb_fin : Fin.natAdd (m + 1)
            (⟨b.val - (m + 1), by omega⟩ : Fin (m + 1)) =
            b :=
          Fin.ext (by simp; omega)
        rw [hsHc_def]; change (c (Fin.natAdd (m + 1)
          ⟨b.val - (m + 1), _⟩)).isRight
        rw [hb_fin]; exact hcb
    · intro ⟨a₁, b₁⟩ hp₁ ⟨a₂, b₂⟩ hp₂ h
      simp only [mem_filter, mem_univ, true_and] at hp₁ hp₂
      obtain ⟨ha₁, hb₁_lo, _⟩ :=
        hinv a₁ b₁ hp₁.1 hp₁.2.1
      obtain ⟨ha₂, hb₂_lo, _⟩ :=
        hinv a₂ b₂ hp₂.1 hp₂.2.1
      have h_fst : b₁.val - (m + 1) = b₂.val - (m + 1) :=
        congrArg Fin.val (congrArg Prod.fst h)
      have ha : a₁ = a₂ := Fin.ext (by omega)
      have hb : b₁ = b₂ := Fin.ext (by omega)
      exact Prod.ext ha hb
    · intro ⟨i, j⟩ hp
      have hp' := mem_filter.mp hp
      have hp'' := (mem_filter.mp hp'.1).2
      have hj_eq : j = Fin.last m := hp'.2
      have hij := hp''.1
      have hrj := hp''.2.1
      have hri := hp''.2.2
      have hi_lt : i.val < m := by
        rw [hj_eq] at hij; exact hij
      refine ⟨(⟨m, by omega⟩, ⟨(m + 1) + i.val, by omega⟩),
        ?_, ?_⟩
      · simp only [mem_filter, mem_univ, true_and]
        refine ⟨show m < (m + 1) + i.val by omega, ?_, ?_, ?_⟩
        · change (capPeelPerm m
              ⟨(m + 1) + i.val, _⟩).val <
            (capPeelPerm m ⟨m, _⟩).val
          rw [hσm, hσi ⟨i.val, hi_lt⟩]; omega
        · rw [hdc]
          rw [show (⟨m, by omega⟩ :
                Fin ((m + 1) + (m + 1))) =
              Fin.castAdd (m + 1) (Fin.last m) from
              Fin.ext rfl]
          rw [hj_eq] at hrj; exact hrj
        · rw [hdc]
          rw [show (⟨(m + 1) + i.val, by omega⟩ :
                Fin ((m + 1) + (m + 1))) =
              Fin.natAdd (m + 1) i from Fin.ext rfl]
          exact hri
      · have hv : (m + 1 + i.val) - (m + 1) = i.val := by
          omega
        exact Prod.ext (Fin.ext hv)
          (hj_eq.symm ▸ rfl)
  -- Conclude: OI + KC_m = KC_{m+1}
  rw [hKC_eq, hsplit, ← hinner, ← hbdry]; omega

/-! ### The main theorem -/

-- The induction on the arity carries the whole
-- Koszul crossing count through each step.
/-- **The diagonal cap pairing equals the colour pairing**:
`betaDiag m c = betaColour (firstHalf c) (secondHalf c)`. -/
theorem betaDiag_eq_betaColour {k ℓ : ℕ} :
    ∀ (m : ℕ) (c : MixedColouring k ℓ (m + m)),
      betaDiag m c =
        betaColour
          (MixedColouring.firstHalf (a := m) (b := m) c)
          (MixedColouring.secondHalf (a := m) (b := m) c) := by
  intro m
  induction m with
  | zero =>
    intro c
    rw [betaDiag_zero]
    unfold betaColour koszulCrossings
    simp
  | succ m ih =>
    intro c
    -- Case split: are all position pairs matching in parity type?
    by_cases hmatch : ∀ i : Fin (m + 1),
        (MixedColouring.firstHalf (a := m + 1) (b := m + 1)
          c i).isRight =
        (MixedColouring.secondHalf (a := m + 1) (b := m + 1)
          c i).isRight
    · -- All pairs match: the main computation
      have heven := peelFirstHalf_isEven_of_matching m c hmatch
      rw [betaDiag_succ]
      rw [dite_eq_left heven]
      -- Apply the inductive hypothesis
      rw [ih]
      -- Unfold betaColour on both sides
      unfold betaColour
      -- Use the product splitting
      rw [prod_entry_split]
      -- Use the sign identity
      rw [wordSign_eq_oddInversions, wordPerm_adjWord]
      -- Rearrange: a * (b * (P * E)) = a * b * (P * E)
      -- = (a * b) * (P * E) = K' * (P * E)
      -- where a * b = K' by sign_eq
      set I := oddInversions (capPeelPerm m)
        (peelColour m c ∘ ⇑(finCongr (capPeelArity m)))
      set K := koszulCrossings
        (MixedColouring.firstHalf (a := m) (b := m)
          (MixedColouring.firstHalf (a := m + m) (b := 2)
            (peelColour m c)))
        (MixedColouring.secondHalf (a := m) (b := m)
          (MixedColouring.firstHalf (a := m + m) (b := 2)
            (peelColour m c)))
      set K' := koszulCrossings
        (MixedColouring.firstHalf (a := m + 1) (b := m + 1) c)
        (MixedColouring.secondHalf (a := m + 1) (b := m + 1) c)
      set P := ∏ i : Fin m,
        colourFormEntry k ℓ
          (MixedColouring.firstHalf (a := m) (b := m)
            (MixedColouring.firstHalf (a := m + m) (b := 2)
              (peelColour m c)) i)
          (MixedColouring.secondHalf (a := m) (b := m)
            (MixedColouring.firstHalf (a := m + m) (b := 2)
              (peelColour m c)) i)
      set E := colourFormEntry k ℓ
        (MixedColouring.secondHalf (a := m + m) (b := 2)
          (peelColour m c) 0)
        (MixedColouring.secondHalf (a := m + m) (b := 2)
          (peelColour m c) 1)
      have hsign : (-1 : ℂ) ^ I * (-1 : ℂ) ^ K =
          (-1 : ℂ) ^ K' := sign_eq m c hmatch
      -- The goal is (-1)^I * ((-1)^K * P * E) = (-1)^K' * (P * E)
      calc (-1 : ℂ) ^ I * ((-1) ^ K * P * E)
          = ((-1) ^ I * (-1) ^ K) * (P * E) := by ring
        _ = (-1) ^ K' * (P * E) := by rw [hsign]
    · -- Mixed pair: both sides are zero
      push Not at hmatch
      obtain ⟨i, hi⟩ := hmatch
      rw [show betaColour
          (MixedColouring.firstHalf (a := m + 1) (b := m + 1) c)
          (MixedColouring.secondHalf (a := m + 1) (b := m + 1)
            c) = 0 from betaColour_eq_zero_of_mixed i hi]
      rw [betaDiag_succ]
      -- Determine if mixed pair is at the last position
      by_cases hi_last : i = Fin.last m
      · -- Mixed at last m: the colourFormEntry is zero
        subst hi_last
        split_ifs with hev
        · -- dite-true
          have hentry : colourFormEntry k ℓ
              (MixedColouring.secondHalf (a := m + m) (b := 2)
                (peelColour m c) 0)
              (MixedColouring.secondHalf (a := m + m) (b := 2)
                (peelColour m c) 1) = 0 := by
            rw [peelSecondHalf_zero, peelSecondHalf_one]
            exact colourFormEntry_zero_of_isRight_ne _ _
              (by rwa [firstHalf_last, secondHalf_last'] at hi)
          rw [hentry, mul_zero, mul_zero]
        · -- dite-false
          rw [mul_zero]
      · -- Mixed at castSucc i': get i' from i
        have ⟨i', hi'⟩ : ∃ i' : Fin m, i = Fin.castSucc i' := by
          refine ⟨⟨i.val, ?_⟩, Fin.ext rfl⟩
          have := i.isLt
          have : (Fin.last m).val = m := rfl
          by_contra h
          exact hi_last (Fin.ext (by omega))
        subst hi'
        split_ifs with hev
        · -- dite-true: IH betaColour is zero
          rw [ih]
          have hbc : betaColour
              (MixedColouring.firstHalf (a := m) (b := m)
                (MixedColouring.firstHalf (a := m + m) (b := 2)
                  (peelColour m c)))
              (MixedColouring.secondHalf (a := m) (b := m)
                (MixedColouring.firstHalf (a := m + m) (b := 2)
                  (peelColour m c))) = 0 := by
            apply betaColour_eq_zero_of_mixed (i := i')
            rw [← firstHalf_castSucc_eq,
              ← secondHalf_castSucc_eq]
            exact hi
          rw [hbc, zero_mul, mul_zero]
        · -- dite-false
          rw [mul_zero]

end RS
