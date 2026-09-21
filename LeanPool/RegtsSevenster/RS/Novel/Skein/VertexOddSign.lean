/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Common.ListAttach
import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueSplit

/-!
# Vertex-local in-sets and the incoming-flag sign

The vocabulary the orientation-change analysis is written in: at a
vertex, the participating flags attached to it and marked incoming
form a finite set, of which `EdgeSubset.relInFlagsAt` is the sorted
enumeration; each such flag carries an odd-pairing sign, and the
odd-colour pair it contributes is read off by two maps.

Flipping the colours on a set `S` negates the sign at the flags of
`S` and leaves the others alone, which is what makes the flip
analysis a product of independent local factors.
-/

namespace RS

open scoped Classical

variable {α : Type} {W : Fragment α} {F : EdgeSubset W}
  {k ℓ : ℕ} {S : Finset W.Flag}

/-! ## The in-set at a vertex -/

/-- The in-set at a vertex over a relative orientation: the
participating flags attached to the vertex and marked incoming. -/
noncomputable def relInSetAt {κ₀ : F.RelTransitionSystem}
    (o₀ : κ₀.Orientation) (vv : W.Vertex) : Finset W.Flag :=
  F.flags.filter
    (fun f => W.attach f = Sum.inl vv ∧ o₀.isOut f = false)

/-- Membership in the in-set at a vertex, unfolded. -/
theorem mem_relInSetAt {κ₀ : F.RelTransitionSystem}
    {o₀ : κ₀.Orientation} {vv : W.Vertex} {g : W.Flag} :
    g ∈ relInSetAt o₀ vv ↔
      g ∈ F.flags ∧ W.attach g = Sum.inl vv ∧
        o₀.isOut g = false :=
  Finset.mem_filter

/-- An in-flag at a vertex is an internal flag. -/
theorem relInSetAt_subset_internal {κ₀ : F.RelTransitionSystem}
    {o₀ : κ₀.Orientation} {vv : W.Vertex} {g : W.Flag}
    (hg : g ∈ relInSetAt o₀ vv) : g ∈ F.internalFlags := by
  obtain ⟨h1, h2, _⟩ := mem_relInSetAt.mp hg
  exact EdgeSubset.mem_internalFlags_of h1 ⟨vv, h2⟩

/-- `EdgeSubset.relInFlagsAt` enumerates the in-set at a vertex. -/
theorem relInFlagsAt_coe {κ₀ : F.RelTransitionSystem}
    (o₀ : κ₀.Orientation) (vv : W.Vertex) :
    (F.relInFlagsAt o₀ vv : Multiset W.Flag) =
      (relInSetAt o₀ vv).val := by
  letI := W.flagOrder
  letI := Classical.dec
  unfold EdgeSubset.relInFlagsAt
  rw [Finset.sort_eq]
  exact congrArg Finset.val (Finset.ext (fun g => by
    rw [Finset.mem_filter, mem_relInSetAt]))

/-! ## The odd-colour pair at an internal flag -/

/-- The flag's own odd colour. -/
noncomputable def pairA (φ : F.CoreOddColouring ℓ)
    (f : {f : W.Flag // f ∈ F.internalFlags}) : Fin (2 * ℓ) :=
  φ.val ⟨f.val, F.internalFlags_subset_coreFlags f.prop⟩

/-- The odd colour opposite the flag's transition partner. -/
noncomputable def pairB {κ₀ : F.RelTransitionSystem}
    (φ : F.CoreOddColouring ℓ)
    (f : {f : W.Flag // f ∈ F.internalFlags}) : Fin (2 * ℓ) :=
  oddPartner ℓ (φ.val ⟨κ₀.match_ f.val,
    F.internalFlags_subset_coreFlags (κ₀.match_mem _ f.prop)⟩)

/-- Reversing every odd pair of a list multiplies the odd
evaluation by `(−1)` per pair. -/
theorem evalOdd_flatMap_rev (hM : MixedFunctional k ℓ)
    (μ : Multiset (Fin k)) {β : Type*}
    (pa pb : β → Fin (2 * ℓ)) :
    ∀ (l : List β) (pre : List (Fin (2 * ℓ))),
      hM.evalOdd μ (pre ++ l.flatMap (fun f => [pb f, pa f])) =
        (-1 : ℂ) ^ l.length *
          hM.evalOdd μ (pre ++ l.flatMap (fun f => [pa f, pb f]))
  | [], pre => by simp
  | f :: t, pre => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append,
      List.length_cons]
    by_cases hab : pa f = pb f
    · have hz1 : ¬ (pre ++ pb f :: pa f ::
          t.flatMap (fun f => [pb f, pa f])).Nodup := by
        intro hnd
        have hsub := hnd.sublist (List.sublist_append_right pre _)
        simp only [List.nodup_cons, List.mem_cons] at hsub
        exact hsub.1 (Or.inl hab.symm)
      have hz2 : ¬ (pre ++ pa f :: pb f ::
          t.flatMap (fun f => [pa f, pb f])).Nodup := by
        intro hnd
        have hsub := hnd.sublist (List.sublist_append_right pre _)
        simp only [List.nodup_cons, List.mem_cons] at hsub
        exact hsub.1 (Or.inl hab)
      rw [hM.evalOdd_of_not_nodup μ hz1,
        hM.evalOdd_of_not_nodup μ hz2]
      ring
    · rw [hM.evalOdd_swap_adjacent μ pre
        (t.flatMap (fun f => [pb f, pa f])) hab]
      have hstep := evalOdd_flatMap_rev hM μ pa pb t
        (pre ++ [pa f, pb f])
      simp only [List.append_assoc, List.cons_append,
        List.nil_append] at hstep
      rw [hstep, pow_succ]
      ring

/-! ## The incoming-flag sign -/

/-- The odd-pairing sign an incoming flag carries, extended by one
off the core. -/
noncomputable def inSign (φ : F.CoreOddColouring ℓ)
    (g : W.Flag) : ℤ :=
  if hg : g ∈ F.coreFlags then oddPartnerSign ℓ (φ.val ⟨g, hg⟩)
  else 1

/-- Flipping the colours on `S` negates the sign at a flag of `S`. -/
theorem inSign_flip_of_mem {φ φ' : F.CoreOddColouring ℓ}
    (hφ' : ∀ g, φ'.val g =
      if g.val ∈ S then oddPartner ℓ (φ.val g) else φ.val g)
    {g : W.Flag} (hg : g ∈ S) (hcore : g ∈ F.coreFlags) :
    inSign φ' g = -inSign φ g := by
  unfold inSign
  rw [dif_pos hcore, dif_pos hcore, hφ' ⟨g, hcore⟩, if_pos hg,
    oddPartnerSign_oddPartner]

/-- Flipping the colours on `S` leaves the sign off `S` alone. -/
theorem inSign_flip_of_notMem {φ φ' : F.CoreOddColouring ℓ}
    (hφ' : ∀ g, φ'.val g =
      if g.val ∈ S then oddPartner ℓ (φ.val g) else φ.val g)
    {g : W.Flag} (hg : g ∉ S) : inSign φ' g = inSign φ g := by
  unfold inSign
  by_cases hcore : g ∈ F.coreFlags
  · rw [dif_pos hcore, dif_pos hcore, hφ' ⟨g, hcore⟩, if_neg hg]
  · rw [dif_neg hcore, dif_neg hcore]

/-- The sign is a square root of one. -/
theorem inSign_mul_self (φ : F.CoreOddColouring ℓ)
    (g : W.Flag) : inSign φ g * inSign φ g = 1 := by
  unfold inSign
  by_cases hg : g ∈ F.coreFlags
  · rw [dif_pos hg]
    unfold oddPartnerSign
    by_cases h : (φ.val ⟨g, hg⟩).val < ℓ <;> simp [h]
  · rw [dif_neg hg]
    norm_num

/-- Paired flags carry the same sign. -/
theorem inSign_pairing (φ : F.CoreOddColouring ℓ)
    {g : W.Flag} (hg : g ∈ F.coreFlags) :
    inSign φ (W.pairing g) = inSign φ g := by
  unfold inSign
  rw [dif_pos (F.pairing_mem_coreFlags hg), dif_pos hg]
  exact congrArg (oddPartnerSign ℓ) (φ.prop ⟨g, hg⟩)

/-! ## The core odd data in this vocabulary -/

/-- The odd pair an internal flag contributes, in terms of the two
pair maps. -/
theorem coreOddPairFn_eq' {κ₀ : F.RelTransitionSystem}
    (φ : F.CoreOddColouring ℓ) :
    F.coreOddPairFn κ₀ φ =
      fun f => [pairA φ f, pairB (κ₀ := κ₀) φ f] := rfl

/-- The sign an internal flag contributes is the incoming sign at
its transition partner. -/
theorem signFn_eq {κ₀ : F.RelTransitionSystem}
    (φ : F.CoreOddColouring ℓ)
    (f : {f : W.Flag // f ∈ F.internalFlags}) :
    F.coreOddSignFn κ₀ φ f = inSign φ (κ₀.match_ f.val) := by
  unfold EdgeSubset.coreOddSignFn inSign
  rw [dif_pos
    (F.internalFlags_subset_coreFlags (κ₀.match_mem _ f.prop))]

/-- The odd-pairing sign at a vertex is the product of the incoming
signs over the in-set. -/
theorem signAt_eq_prod {κ₀ : F.RelTransitionSystem}
    (o₀ : κ₀.Orientation) (φ : F.CoreOddColouring ℓ)
    (vv : W.Vertex) :
    F.coreOddSignAt o₀ φ vv =
      ∏ g ∈ relInSetAt o₀ vv, inSign φ (κ₀.match_ g) := by
  unfold EdgeSubset.coreOddSignAt
  rw [attachWith_map_eq (F.coreOddSignFn κ₀ φ)
    (fun g => inSign φ (κ₀.match_ g))
    (fun g hg => signFn_eq φ ⟨g, hg⟩) (F.relInFlagsAt o₀ vv) _]
  exact list_map_prod_eq_finset_prod (relInSetAt o₀ vv) _
    (relInFlagsAt_coe o₀ vv) _

end RS
