/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.ColourEmbedding
import LeanPool.RegtsSevenster.RS.DimensionDefinitions

/-!
# Padding a mixed model with unused colours

Extension by zero preserves the colouring sum: embedded colourings
have the original vertex values, and every other colouring has a
zero vertex factor. Equality of superdimensions then preserves the
free-circle factor as well.
-/

namespace RS

open Classical

namespace MixedColourEmbedding

variable {k ℓ K L : ℕ}

/-- The induced embedding of even edge colourings. -/
def evenColouring (e : MixedColourEmbedding k ℓ K L)
    {α : Type} {W : Fragment α} (F : EdgeSubset W) :
    F.EvenColouring k ↪ F.EvenColouring K where
  toFun ψ := ⟨fun a => e.even (ψ.val a), fun a => congrArg e.even (ψ.prop a)⟩
  inj' := by
    intro ψ χ h
    apply Subtype.ext
    funext a
    exact e.even.injective (congrArg (fun ψ => ψ.val a) h)

/-- The induced embedding of odd edge colourings. -/
def oddColouring (e : MixedColourEmbedding k ℓ K L)
    {α : Type} {W : Fragment α} (F : EdgeSubset W) :
    F.OddColouring ℓ ↪ F.OddColouring L where
  toFun φ := ⟨fun a => e.odd (φ.val a), fun a => congrArg e.odd (φ.prop a)⟩
  inj' := by
    intro φ χ h
    apply Subtype.ext
    funext a
    exact e.odd.injective (congrArg (fun φ => φ.val a) h)

private theorem exists_evenColouring (e : MixedColourEmbedding k ℓ K L)
    {W : ClosedFragment} (F : EdgeSubset W) (ψ : F.EvenColouring K)
    (hsupport : ∀ a, ψ.val a ∈ Set.range e.even) :
    ∃ χ, e.evenColouring F χ = ψ := by
  let χ := fun a => Classical.choose (hsupport a)
  have hχ : ∀ a, e.even (χ a) = ψ.val a := fun a =>
    Classical.choose_spec (hsupport a)
  refine ⟨⟨χ, ?_⟩, ?_⟩
  · intro a
    apply e.even.injective
    rw [hχ, hχ, ψ.prop]
  · exact Subtype.ext (funext hχ)

-- The odd lifting is the even lifting with the participating
-- flags as its domain and the odd embedding as its colour map.
private theorem exists_oddColouring (e : MixedColourEmbedding k ℓ K L)
    {W : ClosedFragment} (F : EdgeSubset W) (φ : F.OddColouring L)
    (hsupport : ∀ a, φ.val a ∈ Set.range e.odd) :
    ∃ χ, e.oddColouring F χ = φ := by
  let χ := fun a => Classical.choose (hsupport a)
  have hχ : ∀ a, e.odd (χ a) = φ.val a := fun a =>
    Classical.choose_spec (hsupport a)
  refine ⟨⟨χ, ?_⟩, ?_⟩
  · intro a
    apply e.odd.injective
    rw [hχ, hχ, φ.prop]
  · exact Subtype.ext (funext hχ)

/-- Taking the even multiset commutes with embedding colours. -/
theorem evenColoursAt_map (e : MixedColourEmbedding k ℓ K L)
    {α : Type} {W : Fragment α} (F : EdgeSubset W)
    (ψ : F.EvenColouring k) (v : W.Vertex) :
    F.evenColoursAt (e.evenColouring F ψ) v =
      (F.evenColoursAt ψ v).map e.even := by
  simp only [EdgeSubset.evenColoursAt, evenColouring,
    Multiset.map_map, Function.comp_def]
  rfl

/-- Taking the odd list commutes with embedding colours because
the odd embedding preserves symplectic partners. -/
theorem oddListAt_map (e : MixedColourEmbedding k ℓ K L)
    {α : Type} {W : Fragment α} (F : EdgeSubset W)
    {κ : F.TransitionSystem} (o : κ.Orientation)
    (φ : F.OddColouring ℓ) (v : W.Vertex) :
    F.oddListAt o (e.oddColouring F φ) v =
      (F.oddListAt o φ v).map e.odd := by
  unfold EdgeSubset.oddListAt
  rw [List.map_flatMap]
  congr 1
  funext a
  simp [EdgeSubset.oddPairFn, oddColouring, e.partner_eq]

/-- The odd vertex sign is preserved by embedding colours. -/
theorem oddSignAt_map (e : MixedColourEmbedding k ℓ K L)
    {α : Type} {W : Fragment α} (F : EdgeSubset W)
    {κ : F.TransitionSystem} (o : κ.Orientation)
    (φ : F.OddColouring ℓ) (v : W.Vertex) :
    F.oddSignAt o (e.oddColouring F φ) v = F.oddSignAt o φ v := by
  unfold EdgeSubset.oddSignAt
  congr 2
  funext a
  exact e.sign_eq _

private theorem even_support (e : MixedColourEmbedding k ℓ K L)
    {W : ClosedFragment} (F : EdgeSubset W)
    {κ : F.TransitionSystem} (o : κ.Orientation)
    (h : MixedFunctional k ℓ)
    (ψ : F.EvenColouring K) (φ : F.OddColouring L)
    (hne : ∏ v : W.Vertex, (F.oddSignAt o φ v : ℂ) *
      (h.extendColours e).evalOdd (F.evenColoursAt ψ v)
        (F.oddListAt o φ v) ≠ 0) :
    ∀ a, ψ.val a ∈ Set.range e.even := by
  intro a
  by_contra hout
  obtain ⟨v, hv⟩ : ∃ v, W.attach a.val = Sum.inl v := by
    cases ha : W.attach a.val with
    | inl v => exact ⟨v, rfl⟩
    | inr b => exact isEmptyElim b
  have hmem : ψ.val a ∈ F.evenColoursAt ψ v := by
    unfold EdgeSubset.evenColoursAt
    apply Multiset.mem_map.mpr
    refine ⟨a, ?_, rfl⟩
    simpa only [Finset.mem_val, Finset.mem_filter, Finset.mem_univ,
      true_and] using hv
  apply hne
  apply Finset.prod_eq_zero (Finset.mem_univ v)
  rw [h.evalOdd_extendColours_eq_zero_of_even e _ _ _ hmem hout,
    mul_zero]

private theorem odd_support (e : MixedColourEmbedding k ℓ K L)
    {W : ClosedFragment} (F : EdgeSubset W)
    {κ : F.TransitionSystem} (o : κ.Orientation)
    (h : MixedFunctional k ℓ)
    (ψ : F.EvenColouring K) (φ : F.OddColouring L)
    (hne : ∏ v : W.Vertex, (F.oddSignAt o φ v : ℂ) *
      (h.extendColours e).evalOdd (F.evenColoursAt ψ v)
        (F.oddListAt o φ v) ≠ 0) :
    ∀ a, φ.val a ∈ Set.range e.odd := by
  intro a
  by_contra hout
  obtain ⟨v, hv⟩ := κ.attach_internal a.val a.prop
  have hzero (c : Fin (2 * L)) (hc : c ∈ F.oddListAt o φ v)
      (hcOut : c ∉ Set.range e.odd) : False := by
    apply hne
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    rw [h.evalOdd_extendColours_eq_zero_of_odd e _ _ c hc hcOut,
      mul_zero]
  by_cases hin : o.isOut a.val = false
  · apply hzero (φ.val a) _ hout
    apply List.mem_flatMap.mpr
    refine ⟨a, ?_, by simp [EdgeSubset.oddPairFn]⟩
    exact (List.mem_attachWith _ _).mpr (mem_inFlagsAt_of a.prop hv hin)
  · have houtFlag : o.isOut a.val = true := Bool.eq_true_of_not_eq_false hin
    let b : {f : W.Flag // f ∈ F.flags} :=
      ⟨κ.match_ a.val, κ.match_mem _ a.prop⟩
    have hbin : o.isOut b.val = false := by
      simpa [b, houtFlag] using o.match_flip a.val a.prop
    have hbv : W.attach b.val = Sum.inl v := κ.match_vertex _ a.prop v hv
    apply hzero (oddPartner L (φ.val a))
    · apply List.mem_flatMap.mpr
      refine ⟨b, ?_, ?_⟩
      · exact (List.mem_attachWith _ _).mpr
          (mem_inFlagsAt_of b.prop hbv hbin)
      · have hmatch : (⟨κ.match_ b.val, κ.match_mem _ b.prop⟩ :
            {f : W.Flag // f ∈ F.flags}) = a :=
          Subtype.ext (κ.match_invol _ a.prop)
        simp [EdgeSubset.oddPairFn, hmatch]
    · rintro ⟨c, hc⟩
      apply hout
      refine ⟨oddPartner ℓ c, ?_⟩
      rw [e.partner_eq, hc, oddPartner_invol]

/-- Extension by zero preserves each closed Eulerian colouring
sum. Colourings using any additional colour have a zero factor. -/
theorem mixedSummand_extendColours (e : MixedColourEmbedding k ℓ K L)
    {W : ClosedFragment} (F : EdgeSubset W)
    {κ : F.TransitionSystem} (o : κ.Orientation)
    (h : MixedFunctional k ℓ) :
    F.mixedSummand (h.extendColours e) o = F.mixedSummand h o := by
  let i := (e.evenColouring F).prodMap (e.oddColouring F)
  have hsum := Fintype.sum_of_injective i i.injective
    (fun p => ∏ v : W.Vertex, (F.oddSignAt o p.2 v : ℂ) *
      h.evalOdd (F.evenColoursAt p.1 v) (F.oddListAt o p.2 v))
    (fun p => ∏ v : W.Vertex, (F.oddSignAt o p.2 v : ℂ) *
      (h.extendColours e).evalOdd (F.evenColoursAt p.1 v)
        (F.oddListAt o p.2 v)) (fun p hout => ?_) (fun p => ?_)
  · simpa only [EdgeSubset.mixedSummand, Fintype.sum_prod_type] using
      congrArg (fun z => (-1 : ℂ) ^ κ.circuitCount * z) hsum.symm
  · by_contra hne
    obtain ⟨ψ, hψ⟩ := exists_evenColouring e F p.1
      (even_support e F o h p.1 p.2 hne)
    obtain ⟨φ, hφ⟩ := exists_oddColouring e F p.2
      (odd_support e F o h p.1 p.2 hne)
    exact hout ⟨(ψ, φ), Prod.ext hψ hφ⟩
  · apply Finset.prod_congr rfl
    intro v _
    change _ = (F.oddSignAt o (e.oddColouring F p.2) v : ℂ) *
      (h.extendColours e).evalOdd
        (F.evenColoursAt (e.evenColouring F p.1) v)
        (F.oddListAt o (e.oddColouring F p.2) v)
    rw [evenColoursAt_map, oddListAt_map, oddSignAt_map,
      h.evalOdd_extendColours_map]

/-- The chosen Eulerian value is preserved by extension by zero. -/
theorem mixedValue_extendColours (e : MixedColourEmbedding k ℓ K L)
    {W : ClosedFragment} (F : EdgeSubset W) (h : MixedFunctional k ℓ) :
    F.mixedValue (h.extendColours e) = F.mixedValue h := by
  unfold EdgeSubset.mixedValue
  split_ifs
  · exact mixedSummand_extendColours e F _ h
  · rfl

/-- Extension by zero preserves the full partition function when
the source and target have the same superdimension. -/
theorem mixedPartition_extendColours (e : MixedColourEmbedding k ℓ K L)
    (h : MixedFunctional k ℓ)
    (hbalance : (K : ℂ) - 2 * L = (k : ℂ) - 2 * ℓ)
    (W : ClosedFragment) :
    mixedPartition (h.extendColours e) W = mixedPartition h W := by
  unfold mixedPartition
  rw [hbalance]
  apply congrArg (fun z : ℂ => ((k : ℂ) - 2 * ℓ) ^ W.circles * z)
  apply Finset.sum_congr rfl
  intro s _
  split_ifs
  · exact mixedValue_extendColours e _ h
  · rfl
  · rfl

end MixedColourEmbedding

/-- Pad a functional with unused even colours and unused
symplectic pairs of odd colours. -/
noncomputable def MixedFunctional.padColours {k ℓ K L : ℕ}
    (h : MixedFunctional k ℓ) (hk : k ≤ K) (hℓ : ℓ ≤ L) :
    MixedFunctional K L :=
  h.extendColours (MixedColourEmbedding.ofLE hk hℓ)

/-- Padding with equal numbers of unused even and odd colours
preserves the represented parameter, including free circles. -/
theorem MixedFunctional.padColours_represents {k ℓ K L : ℕ}
    (h : MixedFunctional k ℓ) (hk : k ≤ K) (hℓ : ℓ ≤ L)
    (hbalance : (K : ℂ) - 2 * L = (k : ℂ) - 2 * ℓ)
    {f : ClosedFragment → ℂ} (hrep : h.Represents f) :
    (h.padColours hk hℓ).Represents f := by
  intro W
  rw [hrep W]
  exact (MixedColourEmbedding.mixedPartition_extendColours
    (MixedColourEmbedding.ofLE hk hℓ) h hbalance W).symm

end RS
