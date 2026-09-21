/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.CommutantBound

/-!
# Polynomial commutant bounds for monomial word actions

Matrix entries of an intertwiner are determined, up to nonzero
scalars, by the simultaneous permutation orbits of pairs of words.
Such an orbit is determined by its letter-pair counts. Each count
lies between zero and the word length, giving the polynomial bound
`(n + 1) ^ (Fintype.card α ^ 2)`.
-/

namespace RS

open Finset Representation
open scoped Classical

noncomputable section

variable {α : Type*} {n : ℕ}

/-- Coordinates of a symmetric-group representation acting on words
by permutation of positions and multiplication by nonzero scalars. -/
structure MonomialWordAction
    (ρ : Representation ℂ (Equiv.Perm (Fin n))
      ((Fin n → α) → ℂ)) where
  /-- The scalar attached to a permutation and an output word. -/
  weight : Equiv.Perm (Fin n) → (Fin n → α) → ℂ
  /-- Every coordinate scalar is nonzero. -/
  weight_ne_zero : ∀ σ c, weight σ c ≠ 0
  /-- The action reindexes coordinates by the permutation. -/
  apply_eq : ∀ σ v c, ρ σ v c = weight σ c * v (c ∘ σ)

private def wordPairCounts (p : (Fin n → α) × (Fin n → α)) :
    (α × α) → Fin (n + 1) := fun a =>
  ⟨(univ.filter fun i => (p.1 i, p.2 i) = a).card,
    Nat.lt_succ_of_le (by simpa using
      (Finset.card_le_univ
        (univ.filter fun i => (p.1 i, p.2 i) = a)))⟩

private theorem wordPairCounts_eq_imp_perm
    (p q : (Fin n → α) × (Fin n → α))
    (h : wordPairCounts p = wordPairCounts q) :
    ∃ σ : Equiv.Perm (Fin n),
      q.1 = p.1 ∘ σ ∧ q.2 = p.2 ∘ σ := by
  classical
  have hc (a : α × α) :
      Fintype.card {i : Fin n // (q.1 i, q.2 i) = a} =
        Fintype.card {i : Fin n // (p.1 i, p.2 i) = a} := by
    have ha := congrArg Fin.val (congrFun h a)
    simpa [wordPairCounts, Fintype.card_subtype] using ha.symm
  let e (a : α × α) := Fintype.equivOfCardEq (hc a)
  refine ⟨Equiv.ofFiberEquiv e, ?_, ?_⟩
  · funext i
    exact (congrArg Prod.fst (Equiv.ofFiberEquiv_map e i)).symm
  · funext i
    exact (congrArg Prod.snd (Equiv.ofFiberEquiv_map e i)).symm

private theorem monomial_intertwining_entry
    {ρ : Representation ℂ (Equiv.Perm (Fin n))
      ((Fin n → α) → ℂ)} (M : MonomialWordAction ρ)
    (T : IntertwiningMap ρ ρ) (σ : Equiv.Perm (Fin n))
    (a b : Fin n → α) :
    M.weight σ b * T (Pi.single b 1) a =
      M.weight σ a * T (Pi.single (b ∘ σ) 1) (a ∘ σ) := by
  classical
  have hdelta : ρ σ (Pi.single (b ∘ σ) 1) =
      M.weight σ b • Pi.single b 1 := by
    funext c
    rw [M.apply_eq]
    by_cases hbc : b = c
    · subst c
      simp
    · have hcomp : b ∘ σ ≠ c ∘ σ := by
        intro h
        apply hbc
        funext i
        have hi := congrFun h (σ.symm i)
        simpa using hi
      simp [hbc, hcomp]
  have h := LinearMap.congr_fun (T.isIntertwining' σ)
    (Pi.single (b ∘ σ) 1)
  have ha := congrFun h a
  simpa [LinearMap.comp_apply, hdelta, M.apply_eq, map_smul,
    smul_eq_mul] using ha

private def commutantEntries
    (ρ : Representation ℂ (Equiv.Perm (Fin n))
      ((Fin n → α) → ℂ)) :
    IntertwiningMap ρ ρ →ₗ[ℂ] (((α × α) → Fin (n + 1)) → ℂ) where
  toFun T c := if h : ∃ p, wordPairCounts p = c then
    T (Pi.single (Classical.choose h).2 1) (Classical.choose h).1
    else 0
  map_add' T U := by
    funext c
    by_cases h : ∃ p, wordPairCounts p = c
    · simp only [dif_pos h, Pi.add_apply]
      rfl
    · simp only [dif_neg h, Pi.add_apply, add_zero]
  map_smul' z T := by
    funext c
    by_cases h : ∃ p, wordPairCounts p = c
    · simp only [dif_pos h, Pi.smul_apply, RingHom.id_apply]
      rfl
    · simp only [dif_neg h, Pi.smul_apply, smul_zero]

private theorem commutantEntries_injective [Fintype α]
    {ρ : Representation ℂ (Equiv.Perm (Fin n))
      ((Fin n → α) → ℂ)} (M : MonomialWordAction ρ) :
    Function.Injective (commutantEntries ρ) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro T hT
  have hentry (a b : Fin n → α) : T (Pi.single b 1) a = 0 := by
    let c := wordPairCounts (a, b)
    have hc : ∃ p, wordPairCounts p = c := ⟨(a, b), rfl⟩
    let p := Classical.choose hc
    have hp : wordPairCounts p = wordPairCounts (a, b) :=
      Classical.choose_spec hc
    have hz := congrFun hT c
    simp only [commutantEntries, LinearMap.coe_mk, AddHom.coe_mk,
      dif_pos hc, Pi.zero_apply] at hz
    obtain ⟨σ, hrow, hcol⟩ :=
      wordPairCounts_eq_imp_perm (a, b) p hp.symm
    have h := monomial_intertwining_entry M T σ a b
    rw [← hrow, ← hcol, hz, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (M.weight_ne_zero σ b)
  apply IntertwiningMap.toLinearMap_injective
  apply (Pi.basisFun ℂ (Fin n → α)).ext
  intro b
  funext a
  simpa using hentry a b

/-- The commutant of a monomial word action has polynomial dimension,
with one possible coordinate for each table of letter-pair counts. -/
theorem finrank_commutant_le_word_counts [Fintype α]
    {ρ : Representation ℂ (Equiv.Perm (Fin n))
      ((Fin n → α) → ℂ)} (M : MonomialWordAction ρ) :
    Module.finrank ℂ (IntertwiningMap ρ ρ) ≤
      (n + 1) ^ (Fintype.card α ^ 2) := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (commutantEntries_injective M)
  simpa [Module.finrank_pi, Fintype.card_fun, sq] using h

end

end RS
