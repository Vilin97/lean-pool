/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CoreParity
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.NFDef

/-!
# The h-generic value identity and Definition 5 normal-form theorem

For a closed fragment, an arbitrary mixed functional's Definition 5
summand equals the (κ, o)-free normal form — the engine of Eulerian
independence.
-/

@[expose] public section

namespace RS

open Finset

variable {k ℓ : ℕ}

/-! ## The h-generic value identity -/

-- Raised budget: the master summand of the flipped data colouring
-- is expanded to the vertex product, so the sort, the flip and the
-- circuit count all unfold together.
/-- **The h-generic value identity**: the h-generic master summand of
the flipped data colouring equals the circuit sign times the
vertex product of oddSign times evalOdd. -/
theorem hMaster_colouringOfFlip (h : MixedFunctional k ℓ)
    (W : ClosedFragment) (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) (ψ : F.EvenColouring k) (φ : F.OddColouring ℓ) :
    hMaster h W (colouringOfFlip W F o ψ φ) =
      ((-1 : ℂ) ^ κ.circuitCount) *
        ∏ v : W.Vertex, ((F.oddSignAt o φ v : ℂ) *
          h.evalOdd (F.evenColoursAt ψ v) (F.oddListAt o φ v)) := by
  have hmaster : hMaster h W (colouringOfFlip W F o ψ φ) =
    ((-1 : ℂ) ^ oddInversions (sortSplitPerm W)
        ((colouringOfFlip W F o ψ φ) ∘
          finCongr (degList_sum (starAssignEnum W))) *
      ∏ v, (if (oddListOf (blockRestrict
            (degList (starAssignEnum W))
            (((colouringOfFlip W F o ψ φ) ∘ finCongr
              (degList_sum (starAssignEnum W))) ∘
              sortSplitPerm W) v)).Nodup then
          (sortSign (oddListOf (blockRestrict
            (degList (starAssignEnum W))
            (((colouringOfFlip W F o ψ φ) ∘ finCongr
              (degList_sum (starAssignEnum W))) ∘
              sortSplitPerm W) v)) : ℂ) *
            h (evenMultisetOf (blockRestrict
              (degList (starAssignEnum W))
              (((colouringOfFlip W F o ψ φ) ∘ finCongr
                (degList_sum (starAssignEnum W))) ∘
                sortSplitPerm W) v))
              (oddFinsetOf (blockRestrict
                (degList (starAssignEnum W))
                (((colouringOfFlip W F o ψ φ) ∘ finCongr
                  (degList_sum (starAssignEnum W))) ∘
                  sortSplitPerm W) v))
        else 0)) *
    betaDiag (edgeCount W) (colouringOfFlip W F o ψ φ) := rfl
  rw [hmaster]
  rw [show oddInversions (sortSplitPerm W)
      ((colouringOfFlip W F o ψ φ) ∘
        finCongr (degList_sum (starAssignEnum W))) =
    patternOddInv W F from oddInversions_colouringOf W F ψ _]
  rw [betaDiag_colouringOfFlip W F o ψ φ]
  rw [prod_blockVertex W (fun vtx =>
    (F.oddSignAt o φ vtx : ℂ) *
      h.evalOdd (F.evenColoursAt ψ vtx)
        (F.oddListAt o φ vtx))]
  rw [prod_blockVertex W (fun vtx =>
    ((F.oddSignAt o φ vtx : ℤ) : ℂ))]
  -- ═══════ EVERY BLOCK'S ODD LIST IS DUPLICATE-FREE ═══════
  -- Then each block factor is its sorting sign times the vertex
  -- factor, and the grand parity collects the four sign families.
  by_cases hnd : ∀ v : Fin (ds W).length,
      (F.oddListAt o φ (blockVertex W v)).Nodup
  · rw [Finset.prod_congr rfl (fun v _ =>
      hMaster_vertex_nodup h W F o ψ φ v (hnd v))]
    have hgp := grand_parity W F o ψ φ hnd
    have hsplitL : (∏ v : Fin (ds W).length,
        ((sortSign (oddListOf (blockRestrict (ds W)
            (cSorted W (colouringOfFlip W F o ψ φ)) v)) : ℂ) *
          ((sortSign (F.oddListAt o φ
              (blockVertex W v)) : ℂ) *
            h.evalOdd
              (F.evenColoursAt ψ (blockVertex W v))
              (F.oddListAt o φ (blockVertex W v))))) =
      (∏ v : Fin (ds W).length,
        ((sortSign (oddListOf (blockRestrict (ds W)
            (cSorted W (colouringOfFlip W F o ψ φ)) v)) : ℂ) *
          (sortSign (F.oddListAt o φ
            (blockVertex W v)) : ℂ))) *
      ∏ v : Fin (ds W).length,
        h.evalOdd
          (F.evenColoursAt ψ (blockVertex W v))
          (F.oddListAt o φ (blockVertex W v)) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun v _ => by ring)
    have hsplitR : (∏ v : Fin (ds W).length,
        ((F.oddSignAt o φ (blockVertex W v) : ℂ) *
          h.evalOdd
            (F.evenColoursAt ψ (blockVertex W v))
            (F.oddListAt o φ (blockVertex W v)))) =
      (∏ v : Fin (ds W).length,
        ((F.oddSignAt o φ (blockVertex W v) : ℤ) : ℂ)) *
      ∏ v : Fin (ds W).length,
        h.evalOdd
          (F.evenColoursAt ψ (blockVertex W v))
          (F.oddListAt o φ (blockVertex W v)) := by
      rw [← Finset.prod_mul_distrib]
    calc ((-1 : ℂ) ^ patternOddInv W F *
        (∏ v : Fin (ds W).length,
          ((sortSign (oddListOf (blockRestrict (ds W)
              (cSorted W (colouringOfFlip W F o ψ φ))
              v)) : ℂ) *
            ((sortSign (F.oddListAt o φ
                (blockVertex W v)) : ℂ) *
              h.evalOdd
                (F.evenColoursAt ψ (blockVertex W v))
                (F.oddListAt o φ (blockVertex W v)))))) *
        ((-1 : ℂ) ^ (Finset.univ.filter
            (fun p : Fin (edgeCount W) × Fin (edgeCount W) =>
              p.1 < p.2 ∧ p.1 ∈ edgeIndexSet W F ∧
              p.2 ∈ edgeIndexSet W F)).card *
          (-1 : ℂ) ^ inRepCount W F o *
          ∏ v : Fin (ds W).length,
            ((F.oddSignAt o φ (blockVertex W v) : ℤ) : ℂ))
        = (((-1 : ℂ) ^ patternOddInv W F) *
            ((-1 : ℂ) ^ (Finset.univ.filter
              (fun p : Fin (edgeCount W) ×
                  Fin (edgeCount W) =>
                p.1 < p.2 ∧ p.1 ∈ edgeIndexSet W F ∧
                p.2 ∈ edgeIndexSet W F)).card *
              (-1 : ℂ) ^ inRepCount W F o) *
            ∏ v : Fin (ds W).length,
              ((sortSign (oddListOf (blockRestrict (ds W)
                  (cSorted W (colouringOfFlip W F o ψ φ))
                  v)) : ℂ) *
                (sortSign (F.oddListAt o φ
                  (blockVertex W v)) : ℂ))) *
          ((∏ v : Fin (ds W).length,
            ((F.oddSignAt o φ (blockVertex W v) : ℤ) : ℂ)) *
          ∏ v : Fin (ds W).length,
            h.evalOdd
              (F.evenColoursAt ψ (blockVertex W v))
              (F.oddListAt o φ (blockVertex W v))) := by
          rw [hsplitL]
          ring
      _ = ((-1 : ℂ) ^ κ.circuitCount) *
          ((∏ v : Fin (ds W).length,
            ((F.oddSignAt o φ (blockVertex W v) : ℤ) : ℂ)) *
          ∏ v : Fin (ds W).length,
            h.evalOdd
              (F.evenColoursAt ψ (blockVertex W v))
              (F.oddListAt o φ (blockVertex W v))) := by
          rw [hgp]
      _ = ((-1 : ℂ) ^ κ.circuitCount) *
          ∏ v : Fin (ds W).length,
            ((F.oddSignAt o φ (blockVertex W v) : ℂ) *
              h.evalOdd
                (F.evenColoursAt ψ (blockVertex W v))
                (F.oddListAt o φ (blockVertex W v))) := by
          rw [← hsplitR]
  -- ═══════ SOME BLOCK REPEATS AN ODD VALUE ═══════
  -- That block's factor is zero, and so is the vertex product.
  · simp only [not_forall] at hnd
    obtain ⟨v₀, hv₀⟩ := hnd
    have hL0 : (∏ v, (if (oddListOf (blockRestrict
          (degList (starAssignEnum W))
          (((colouringOfFlip W F o ψ φ ∘ finCongr
            (degList_sum (starAssignEnum W))) ∘
            sortSplitPerm W)) v)).Nodup then
        (sortSign (oddListOf (blockRestrict
          (degList (starAssignEnum W))
          (((colouringOfFlip W F o ψ φ ∘ finCongr
            (degList_sum (starAssignEnum W))) ∘
            sortSplitPerm W)) v)) : ℂ) *
          h (evenMultisetOf (blockRestrict
            (degList (starAssignEnum W))
            (((colouringOfFlip W F o ψ φ ∘ finCongr
              (degList_sum (starAssignEnum W))) ∘
              sortSplitPerm W)) v))
            (oddFinsetOf (blockRestrict
              (degList (starAssignEnum W))
              (((colouringOfFlip W F o ψ φ ∘ finCongr
                (degList_sum (starAssignEnum W))) ∘
                sortSplitPerm W)) v))
      else 0)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ v₀)
        (hMaster_vertex_not_nodup h W F o ψ φ v₀ hv₀)
    have hR0 : (∏ v : Fin (ds W).length,
        ((F.oddSignAt o φ (blockVertex W v) : ℂ) *
          h.evalOdd
            (F.evenColoursAt ψ (blockVertex W v))
            (F.oddListAt o φ (blockVertex W v)))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ v₀)
        (by rw [MixedFunctional.evalOdd_of_not_nodup _ _
            hv₀, mul_zero])
    rw [hL0, hR0]
    ring

/-! ## The normal-form theorem -/

/-- **The normal-form theorem**: the mixed summand of any transition
data equals the (κ, o)-free normal form `defFiveNF`. -/
theorem mixedSummand_eq_nf (h : MixedFunctional k ℓ)
    (W : ClosedFragment) (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) :
    F.mixedSummand h o = defFiveNF h W F := by
  unfold EdgeSubset.mixedSummand
  rw [defFiveNF_eq_flip h W F o]
  rw [Finset.sum_congr rfl (fun ψ _ =>
    Finset.sum_congr rfl (fun φ _ =>
      hMaster_colouringOfFlip h W F o ψ φ))]
  rw [show (∑ ψ : F.EvenColouring k,
      ∑ φ : F.OddColouring ℓ,
      ((-1 : ℂ) ^ κ.circuitCount) *
        ∏ v : W.Vertex,
          ((F.oddSignAt o φ v : ℂ) *
            h.evalOdd (F.evenColoursAt ψ v)
              (F.oddListAt o φ v))) =
    ((-1 : ℂ) ^ κ.circuitCount) *
      ∑ ψ : F.EvenColouring k,
      ∑ φ : F.OddColouring ℓ,
        ∏ v : W.Vertex,
          ((F.oddSignAt o φ v : ℂ) *
            h.evalOdd (F.evenColoursAt ψ v)
              (F.oddListAt o φ v)) from by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun ψ _ =>
      (Finset.mul_sum _ _ _).symm)]

/-! ## Closed-fragment Eulerian independence -/

/-- **Closed-fragment Eulerian independence**: the Definition 5
summand of a closed fragment's edge subset does not depend on the
transition system and orientation. -/
theorem eulerian_independence_closed
    (W : ClosedFragment) (F : EdgeSubset W) (h : MixedFunctional k ℓ)
    {κ κ' : F.TransitionSystem} (o : κ.Orientation) (o' : κ'.Orientation) :
    F.mixedSummand h o = F.mixedSummand h o' :=
  (mixedSummand_eq_nf h W F o).trans (mixedSummand_eq_nf h W F o').symm

/-! ## The choice-free value lemma -/

/-- **The choice-free value lemma**: under any concrete transition
data, the choice-based `mixedValue` equals the `mixedSummand`. -/
theorem mixedValue_eq_summand_closed
    (W : ClosedFragment) (F : EdgeSubset W) (h : MixedFunctional k ℓ)
    {κ : F.TransitionSystem} (o : κ.Orientation) :
    F.mixedValue h = F.mixedSummand h o := by
  have hne : Nonempty ((κ' : F.TransitionSystem) × κ'.Orientation) := ⟨⟨κ, o⟩⟩
  rw [EdgeSubset.mixedValue, dite_eq_left hne]
  exact eulerian_independence_closed W F h _ o

end RS
