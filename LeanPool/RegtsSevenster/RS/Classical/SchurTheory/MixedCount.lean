/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.MixedFixed
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.ColourWeight

/-!
# Mixed fixed-point convolution

Expresses the colour character of a lifted permutation as a convolution
over tail-content vectors.
-/

namespace RS

open Finset Equiv.Perm Fin

open scoped Classical in
/-- The colour character of a lifted permutation is a convolution
over how the free tail is coloured. -/
theorem colourChar_viaEmbedding {m n N : ℕ} (h : m ≤ n)
    (σ : Equiv.Perm (Fin m)) (α : Fin N → ℕ) :
    colourChar α (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h) σ) =
      ∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (n + 1)),
        (if ∀ a, w a ≤ α a then
          colourChar (fun a => α a - w a) σ *
            (Finset.univ.filter
              (fun t : ({i : Fin n // m ≤ (i : ℕ)} → Fin N) =>
                ∀ a, (Finset.univ.filter (fun i => t i = a)).card
                  = w a)).card
          else 0) := by
  classical
  set ι := Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h) σ with ι_def
  -- fibreCard decomposes through mixedFixedEquiv
  have fib_decomp : ∀ (f : {f : Fin n → Fin N // f ∘ ⇑ι = f}) (a : Fin N),
      fibreCard f.1 a = fibreCard ((mixedFixedEquiv h σ f).1).1 a +
        (univ.filter (fun i : {i : Fin n // m ≤ (i : ℕ)} =>
          (mixedFixedEquiv h σ f).2 i = a)).card := by
    intro f a
    have := mixedFixedEquiv_symm_fibreCard h σ
      (mixedFixedEquiv h σ f).1 (mixedFixedEquiv h σ f).2 a
    rwa [Prod.mk.eta, Equiv.symm_apply_apply] at this
  -- Core equivalence: LHS subtype ≃ product subtype with combined margin
  have main_equiv :
      {f : Fin n → Fin N // (∀ j, fibreCard f j = α j) ∧ f ∘ ⇑ι = f} ≃
      {p : {g : Fin m → Fin N // g ∘ ⇑σ = g} × ({i : Fin n // m ≤ (i : ℕ)} → Fin
        N) //
        ∀ a, fibreCard p.1.1 a +
          (univ.filter (fun i : {i : Fin n // m ≤ (i : ℕ)} => p.2 i = a)).card =
            α a} :=
    (Equiv.subtypeEquivRight (fun _ => And.comm)).trans
      ((Equiv.subtypeSubtypeEquivSubtypeInter
          (fun f : Fin n → Fin N => f ∘ ⇑ι = f)
          (fun f => ∀ j, fibreCard f j = α j)).symm.trans
        (Equiv.subtypeEquiv (mixedFixedEquiv h σ) (fun f =>
          ⟨fun hm a => by rw [← fib_decomp f a]; exact hm a,
           fun hm a => by rw [fib_decomp f a]; exact hm a⟩)))
  -- Convert LHS to Fintype.card of product subtype, then to filter card
  have lhs_eq : colourChar α ι =
      Fintype.card {p : {g : Fin m → Fin N // g ∘ ⇑σ = g} ×
        ({i : Fin n // m ≤ (i : ℕ)} → Fin N) //
        ∀ a, fibreCard p.1.1 a +
          (univ.filter (fun i : {i : Fin n // m ≤ (i : ℕ)} => p.2 i = a)).card =
            α a} := by
    show (univ.filter _).card = _
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr main_equiv
  rw [lhs_eq, Fintype.card_subtype]
  -- Set up partition machinery
  set S := (univ :
      Finset ({g : Fin m → Fin N // g ∘ ⇑σ = g} × ({i : Fin n // m ≤ (i : ℕ)} →
        Fin N))).filter
    (fun p => ∀ a, fibreCard p.1.1 a +
      (univ.filter (fun i : {i : Fin n // m ≤ (i : ℕ)} => p.2 i = a)).card = α
        a) with S_def
  set cmap := fun (p : {g : Fin m → Fin N // g ∘ ⇑σ = g} ×
      ({i : Fin n // m ≤ (i : ℕ)} → Fin N)) (a : Fin N) =>
    (univ.filter (fun i : {i : Fin n // m ≤ (i : ℕ)} => p.2 i = a)).card
      with cmap_def
  set W := Fintype.piFinset (fun _ : Fin N => Finset.range (n + 1)) with W_def
  -- cmap maps S into W
  have hcmap_mem : ∀ p ∈ S, cmap p ∈ W := by
    intro p _
    simp only [W_def, Fintype.mem_piFinset, mem_range, cmap_def]
    intro a
    have h1 : (univ.filter (fun i : {i : Fin n // m ≤ (i : ℕ)} => p.2 i =
      a)).card ≤
        Fintype.card {i : Fin n // m ≤ (i : ℕ)} := by
      rw [← card_univ]; exact card_filter_le _ _
    rw [card_tail h] at h1; omega
  -- Partition by tail content
  conv_lhs =>
    rw [show S.card = ∑ w ∈ W, (S.filter (fun p => cmap p = w)).card from
      card_eq_sum_card_fiberwise hcmap_mem]
  -- Per-fibre analysis
  refine sum_congr rfl fun w _ => ?_
  by_cases hw : ∀ a, w a ≤ α a
  · -- Case w ≤ α: factor the fibre as product of independent filters
    rw [if_pos hw]
    -- Rewrite fibre as product
    have fibre_eq :
        S.filter (fun p => cmap p = w) =
        (univ.filter (fun g : {g : Fin m → Fin N // g ∘ ⇑σ = g} =>
          ∀ a, fibreCard g.1 a = α a - w a)) ×ˢ
        (univ.filter (fun t : {i : Fin n // m ≤ (i : ℕ)} → Fin N =>
          ∀ a, (univ.filter (fun i : {i : Fin n // m ≤ (i : ℕ)} => t i =
            a)).card = w a)) := by
      ext ⟨g, t⟩
      simp only [S_def, cmap_def, mem_filter, mem_univ, true_and, mem_product]
      constructor
      · rintro ⟨hm, hc⟩
        refine ⟨fun a => ?_, fun a => congr_fun hc a⟩
        have := hm a; rw [congr_fun hc a] at this; omega
      · rintro ⟨hg, ht⟩
        refine ⟨fun a => ?_, funext ht⟩
        have hwa := hw a; rw [ht a, hg a]; omega
    rw [fibre_eq, card_product]
    -- First factor: colourChar connection
    congr 1
    · rw [colourChar, ← Fintype.card_subtype, ← Fintype.card_subtype]
      exact Fintype.card_congr
        ((Equiv.subtypeSubtypeEquivSubtypeInter
            (fun g : Fin m → Fin N => g ∘ ⇑σ = g)
            (fun g => ∀ a, fibreCard g a = α a - w a)).trans
          (Equiv.subtypeEquivRight (fun _ => And.comm)))
  · -- Case w ≰ α: fibre is empty
    rw [if_neg hw, card_eq_zero, filter_eq_empty_iff]
    intro ⟨g, t⟩ hp hcmap_eq
    rw [S_def] at hp
    simp only [mem_filter, mem_univ, true_and] at hp
    rw [cmap_def] at hcmap_eq
    simp only [not_forall, not_le] at hw
    obtain ⟨a, ha⟩ := hw
    have h1 := hp a
    have h2 : (univ.filter (fun i : {i : Fin n // m ≤ (i : ℕ)} => t i = a)).card
      = w a :=
      congr_fun hcmap_eq a
    omega

end RS
