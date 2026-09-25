/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.PairOrbit

/-!
# The pair-colouring count with margins

Summed over all permutations, the number of fixed pair colourings
with prescribed row and column margins is `n!` times the number of
pair contents with those margins: Fubini, the pair stabilizer
count, content grouping, and orbit–stabilizer.
-/

@[expose] public section

namespace RS

open Finset Equiv

variable {n k : ℕ}

/-- The pair content as a symmetric power. -/
def pairContentSym (p : Fin n → Fin k × Fin k) :
    Sym (Fin k × Fin k) n :=
  ⟨pairContent p, by
    rw [pairContent, Multiset.card_map]
    simp⟩

/-- Every pair content is realized. -/
theorem pair_exists_content (s : Sym (Fin k × Fin k) n) :
    ∃ p : Fin n → Fin k × Fin k, pairContentSym p = s := by
  classical
  have hlen : s.1.toList.length = n := by
    rw [Multiset.length_toList]
    exact s.2
  refine ⟨fun i => s.1.toList.get ⟨i.1, by omega⟩,
    Subtype.ext ?_⟩
  rw [show (pairContentSym (fun i : Fin n =>
      s.1.toList.get ⟨i.1, by omega⟩)).1 =
    Finset.univ.val.map (fun i : Fin n =>
      s.1.toList.get ⟨i.1, by omega⟩) from rfl]
  rw [Fin.univ_val_map]
  rw [show (List.ofFn fun i : Fin n =>
      s.1.toList.get ⟨↑i, by omega⟩) = s.1.toList from by
    apply List.ext_get
    · simp
    · intro i hi₁ hi₂
      simp]
  exact Multiset.coe_toList s.1

/-- Margins are determined by the content. -/
theorem margin_fst_of_content (p : Fin n → Fin k × Fin k)
    (a : Fin k) :
    fibreCard (fun i => (p i).1) a =
      ∑ b : Fin k, (pairContentSym p).1.count (a, b) := by
  classical
  rw [fibreCard_fst_eq_sum]
  exact Finset.sum_congr rfl fun b _ => pairFibre_eq_count p (a, b)

/-- The second-coordinate analogue. -/
theorem margin_snd_of_content (p : Fin n → Fin k × Fin k)
    (b : Fin k) :
    fibreCard (fun i => (p i).2) b =
      ∑ a : Fin k, (pairContentSym p).1.count (a, b) := by
  classical
  rw [fibreCard_snd_eq_sum]
  exact Finset.sum_congr rfl fun a _ => pairFibre_eq_count p (a, b)

open scoped Classical in
/-- **The pair-colouring count with margins.** -/
theorem pair_count_sum (α β : Fin k → ℕ) :
    (∑ π : Equiv.Perm (Fin n),
      (Finset.univ.filter (fun p : Fin n → Fin k × Fin k =>
        (∀ a, fibreCard (fun i => (p i).1) a = α a) ∧
        (∀ b, fibreCard (fun i => (p i).2) b = β b) ∧
        p ∘ π = p)).card) =
      n.factorial * Fintype.card {s : Sym (Fin k × Fin k) n //
        (∀ a, (∑ b : Fin k, s.1.count (a, b)) = α a) ∧
        (∀ b, (∑ a : Fin k, s.1.count (a, b)) = β b)} := by
  classical
  -- ═══════ STAGE 1: FUBINI ON THE TWO SUMS ═══════
  have h1 : (∑ π : Equiv.Perm (Fin n),
      (Finset.univ.filter (fun p : Fin n → Fin k × Fin k =>
        (∀ a, fibreCard (fun i => (p i).1) a = α a) ∧
        (∀ b, fibreCard (fun i => (p i).2) b = β b) ∧
        p ∘ π = p)).card) =
      ∑ p ∈ Finset.univ.filter (fun p : Fin n → Fin k × Fin k =>
        (∀ a, fibreCard (fun i => (p i).1) a = α a) ∧
        (∀ b, fibreCard (fun i => (p i).2) b = β b)),
        (Finset.univ.filter
          (fun π : Equiv.Perm (Fin n) => p ∘ π = p)).card := by
    calc (∑ π : Equiv.Perm (Fin n),
        (Finset.univ.filter (fun p : Fin n → Fin k × Fin k =>
          (∀ a, fibreCard (fun i => (p i).1) a = α a) ∧
          (∀ b, fibreCard (fun i => (p i).2) b = β b) ∧
          p ∘ π = p)).card)
        = ∑ π : Equiv.Perm (Fin n),
            ∑ p : Fin n → Fin k × Fin k,
              (if ((∀ a, fibreCard (fun i => (p i).1) a = α a) ∧
                  (∀ b, fibreCard (fun i => (p i).2) b = β b)) ∧
                  p ∘ π = p
                then 1 else 0) := by
          refine Finset.sum_congr rfl fun π _ => ?_
          rw [Finset.card_filter]
          refine Finset.sum_congr rfl fun p _ => ?_
          by_cases hm : (∀ a, fibreCard (fun i => (p i).1) a =
              α a) ∧ (∀ b, fibreCard (fun i => (p i).2) b = β b)
          · by_cases hf : p ∘ π = p
            · rw [ite_eq_left ⟨hm.1, hm.2, hf⟩, ite_eq_left ⟨hm, hf⟩]
            · rw [ite_eq_right (fun hc => hf hc.2.2),
                ite_eq_right (fun hc => hf hc.2)]
          · rw [ite_eq_right (fun hc => hm ⟨hc.1, hc.2.1⟩),
              ite_eq_right (fun hc => hm hc.1)]
      _ = ∑ p : Fin n → Fin k × Fin k,
            ∑ π : Equiv.Perm (Fin n),
              (if ((∀ a, fibreCard (fun i => (p i).1) a = α a) ∧
                  (∀ b, fibreCard (fun i => (p i).2) b = β b)) ∧
                  p ∘ π = p
                then 1 else 0) := Finset.sum_comm
      _ = ∑ p ∈ Finset.univ.filter
            (fun p : Fin n → Fin k × Fin k =>
              (∀ a, fibreCard (fun i => (p i).1) a = α a) ∧
              (∀ b, fibreCard (fun i => (p i).2) b = β b)),
            (Finset.univ.filter
              (fun π : Equiv.Perm (Fin n) => p ∘ π = p)).card := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun p _ => ?_
          by_cases hm : (∀ a, fibreCard (fun i => (p i).1) a =
              α a) ∧ (∀ b, fibreCard (fun i => (p i).2) b = β b)
          · rw [ite_eq_left hm, Finset.card_filter]
            refine Finset.sum_congr rfl fun π _ => ?_
            by_cases hf : p ∘ π = p
            · rw [ite_eq_left ⟨hm, hf⟩, ite_eq_left hf]
            · rw [ite_eq_right (fun hc => hf hc.2), ite_eq_right hf]
          · rw [ite_eq_right hm]
            rw [Finset.sum_eq_zero fun π _ =>
              ite_eq_right (fun hc => hm hc.1)]
  rw [h1]
  -- ═══════ STAGE 2: THE STABILIZER COUNT PER COLOURING ═══════
  rw [Finset.sum_congr rfl (fun p _ => card_fixing_pairs p)]
  -- ═══════ STAGE 3: GROUP THE COLOURINGS BY CONTENT ═══════
  rw [show (∑ p ∈ Finset.univ.filter
      (fun p : Fin n → Fin k × Fin k =>
        (∀ a, fibreCard (fun i => (p i).1) a = α a) ∧
        (∀ b, fibreCard (fun i => (p i).2) b = β b)),
      ∏ c : Fin k × Fin k, (pairFibre p c).factorial) =
    ∑ p : Fin n → Fin k × Fin k,
      (if (∀ a, (∑ b : Fin k,
            (pairContentSym p).1.count (a, b)) = α a) ∧
          (∀ b, (∑ a : Fin k,
            (pairContentSym p).1.count (a, b)) = β b)
        then ∏ c : Fin k × Fin k,
          ((pairContentSym p).1.count c).factorial
        else 0) from by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hiff : ((∀ a, fibreCard (fun i => (p i).1) a = α a) ∧
        (∀ b, fibreCard (fun i => (p i).2) b = β b)) ↔
        ((∀ a, (∑ b : Fin k,
            (pairContentSym p).1.count (a, b)) = α a) ∧
          (∀ b, (∑ a : Fin k,
            (pairContentSym p).1.count (a, b)) = β b)) := by
      constructor
      · intro hm
        exact ⟨fun a => by
            rw [← margin_fst_of_content]; exact hm.1 a,
          fun b => by
            rw [← margin_snd_of_content]; exact hm.2 b⟩
      · intro hm
        exact ⟨fun a => by
            rw [margin_fst_of_content]; exact hm.1 a,
          fun b => by
            rw [margin_snd_of_content]; exact hm.2 b⟩
    by_cases hm : (∀ a, fibreCard (fun i => (p i).1) a = α a) ∧
        (∀ b, fibreCard (fun i => (p i).2) b = β b)
    · rw [ite_eq_left hm, ite_eq_left (hiff.mp hm)]
      refine Finset.prod_congr rfl fun c _ => ?_
      rw [pairFibre_eq_count]
      rfl
    · rw [ite_eq_right hm, ite_eq_right (fun hc => hm (hiff.mpr hc))]]
  rw [← Fintype.sum_fiberwise pairContentSym
    (fun p => (if (∀ a, (∑ b : Fin k,
          (pairContentSym p).1.count (a, b)) = α a) ∧
        (∀ b, (∑ a : Fin k,
          (pairContentSym p).1.count (a, b)) = β b)
      then ∏ c : Fin k × Fin k,
        ((pairContentSym p).1.count c).factorial
      else 0))]
  -- ═══════ STAGE 4: EVALUATE ONE CONTENT CLASS ═══════
  have hclass : ∀ s : Sym (Fin k × Fin k) n,
      (∑ p : {p : Fin n → Fin k × Fin k // pairContentSym p = s},
        (if (∀ a, (∑ b : Fin k,
              (pairContentSym p.1).1.count (a, b)) = α a) ∧
            (∀ b, (∑ a : Fin k,
              (pairContentSym p.1).1.count (a, b)) = β b)
          then ∏ c : Fin k × Fin k,
            ((pairContentSym p.1).1.count c).factorial
          else 0)) =
      if (∀ a, (∑ b : Fin k, s.1.count (a, b)) = α a) ∧
          (∀ b, (∑ a : Fin k, s.1.count (a, b)) = β b)
        then n.factorial else 0 := by
    intro s
    obtain ⟨p₀, hp₀⟩ := pair_exists_content s
    rw [Finset.sum_congr rfl
      (fun (p : {p : Fin n → Fin k × Fin k //
          pairContentSym p = s}) (_ : p ∈ Finset.univ) => by
        rw [p.2])]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    by_cases hm : (∀ a, (∑ b : Fin k, s.1.count (a, b)) = α a) ∧
        (∀ b, (∑ a : Fin k, s.1.count (a, b)) = β b)
    · rw [ite_eq_left hm, ite_eq_left hm]
      have h := pair_orbit_stab p₀
      have hv : pairContent p₀ = s.1 := congrArg Subtype.val hp₀
      rw [hv] at h
      have hc : Fintype.card
          {p : Fin n → Fin k × Fin k // pairContentSym p = s} =
          Fintype.card
            {p : Fin n → Fin k × Fin k // pairContent p = s.1} :=
        Fintype.card_congr (Equiv.subtypeEquivRight fun p =>
          ⟨fun h' => congrArg Subtype.val h',
            fun h' => Subtype.ext h'⟩)
      rw [hc]
      exact h
    · rw [ite_eq_right hm, ite_eq_right hm, mul_zero]
  rw [Finset.sum_congr rfl
    (fun (s : Sym (Fin k × Fin k) n) (_ : s ∈ Finset.univ) =>
      hclass s)]
  -- ═══════ ASSEMBLY: TOTAL OVER THE MARGIN CLASSES ═══════
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, smul_eq_mul, mul_comm,
    Fintype.card_subtype]

end RS
