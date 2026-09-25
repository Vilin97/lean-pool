/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.NFValue
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CircleModel

/-!
# The reindexing at the heart of the extraction

The master summand under a colouring flip, the fibre sum it induces,
and the identification of the parameter with Definition 5's mixed
partition function.
-/

namespace RS

open CategoryTheory MonoidalCategory Finset
open Functor.LaxMonoidal Functor.OplaxMonoidal


variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))
variable {k ℓ : ℕ}
variable (e : stdSuperPair k ℓ ⟶ P.ω.obj (SkeinObj.mk 1))
variable (e' : P.ω.obj (SkeinObj.mk 1) ⟶ stdSuperPair k ℓ)

-- Raised budget: the termwise identity assembles the star
-- coordinates, the cap pairing and every sign family into one
-- equation.
/-- **The termwise value identity**: the master summand of the
flipped data colouring is the Definition 5 term. -/
theorem masterSummand_colouringOfFlip
    (hee' : (e' ≫ e : P.ω.obj (SkeinObj.mk 1) ⟶
      P.ω.obj (SkeinObj.mk 1)) = 𝟙 _)
    (he'e : (e ≫ e' : stdSuperPair k ℓ ⟶ stdSuperPair k ℓ) = 𝟙 _)
    (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) (ψ : F.EvenColouring k)
    (φ : F.OddColouring ℓ) :
    masterSummand f P e' W (colouringOfFlip W F o ψ φ) =
      ((-1 : ℂ) ^ κ.circuitCount) *
        ∏ v : W.Vertex,
          ((F.oddSignAt o φ v : ℂ) *
            (hRS f P e').evalOdd (F.evenColoursAt ψ v)
              (F.oddListAt o φ v)) := by
  have hmaster : masterSummand f P e' W
      (colouringOfFlip W F o ψ φ) =
    ((-1 : ℂ) ^ oddInversions (sortSplitPerm W)
        ((colouringOfFlip W F o ψ φ) ∘
          finCongr (degList_sum (starAssignEnum W))) *
      ∏ v, starCoord f P e'
        ((degList (starAssignEnum W)).get v)
        (blockRestrict (degList (starAssignEnum W))
          (((colouringOfFlip W F o ψ φ) ∘ finCongr
            (degList_sum (starAssignEnum W))) ∘
            sortSplitPerm W) v)) *
    betaDiag (edgeCount W) (colouringOfFlip W F o ψ φ) := rfl
  rw [hmaster]
  rw [show oddInversions (sortSplitPerm W)
      ((colouringOfFlip W F o ψ φ) ∘
        finCongr (degList_sum (starAssignEnum W))) =
    patternOddInv W F from oddInversions_colouringOf W F ψ _]
  rw [betaDiag_colouringOfFlip W F o ψ φ]
  rw [prod_blockVertex W (fun vtx =>
    (F.oddSignAt o φ vtx : ℂ) *
      (hRS f P e').evalOdd (F.evenColoursAt ψ vtx)
        (F.oddListAt o φ vtx))]
  rw [prod_blockVertex W (fun vtx =>
    ((F.oddSignAt o φ vtx : ℤ) : ℂ))]
  -- ═══════ EVERY BLOCK'S ODD LIST IS DUPLICATE-FREE ═══════
  -- Then each block factor is its sorting sign times the vertex
  -- factor, and the grand parity collects the sign families.
  by_cases hnd : ∀ v : Fin (ds W).length,
      (F.oddListAt o φ (blockVertex W v)).Nodup
  · rw [Finset.prod_congr rfl (fun v _ =>
      starCoord_block_flip_nodup f P e e' hee' he'e
        W F o ψ φ v (hnd v))]
    have hgp := grand_parity W F o ψ φ hnd
    have hsplitL : (∏ v : Fin (ds W).length,
        ((sortSign (oddListOf (blockRestrict (ds W)
            (cSorted W (colouringOfFlip W F o ψ φ)) v)) : ℂ) *
          ((sortSign (F.oddListAt o φ
              (blockVertex W v)) : ℂ) *
            (hRS f P e').evalOdd
              (F.evenColoursAt ψ (blockVertex W v))
              (F.oddListAt o φ (blockVertex W v))))) =
      (∏ v : Fin (ds W).length,
        ((sortSign (oddListOf (blockRestrict (ds W)
            (cSorted W (colouringOfFlip W F o ψ φ)) v)) : ℂ) *
          (sortSign (F.oddListAt o φ
            (blockVertex W v)) : ℂ))) *
      ∏ v : Fin (ds W).length,
        (hRS f P e').evalOdd
          (F.evenColoursAt ψ (blockVertex W v))
          (F.oddListAt o φ (blockVertex W v)) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun v _ => by ring)
    have hsplitR : (∏ v : Fin (ds W).length,
        ((F.oddSignAt o φ (blockVertex W v) : ℂ) *
          (hRS f P e').evalOdd
            (F.evenColoursAt ψ (blockVertex W v))
            (F.oddListAt o φ (blockVertex W v)))) =
      (∏ v : Fin (ds W).length,
        ((F.oddSignAt o φ (blockVertex W v) : ℤ) : ℂ)) *
      ∏ v : Fin (ds W).length,
        (hRS f P e').evalOdd
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
              (hRS f P e').evalOdd
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
            (hRS f P e').evalOdd
              (F.evenColoursAt ψ (blockVertex W v))
              (F.oddListAt o φ (blockVertex W v))) := by
          rw [hsplitL]
          ring
      _ = ((-1 : ℂ) ^ κ.circuitCount) *
          ((∏ v : Fin (ds W).length,
            ((F.oddSignAt o φ (blockVertex W v) : ℤ) : ℂ)) *
          ∏ v : Fin (ds W).length,
            (hRS f P e').evalOdd
              (F.evenColoursAt ψ (blockVertex W v))
              (F.oddListAt o φ (blockVertex W v))) := by
          rw [hgp]
      _ = ((-1 : ℂ) ^ κ.circuitCount) *
          ∏ v : Fin (ds W).length,
            ((F.oddSignAt o φ (blockVertex W v) : ℂ) *
              (hRS f P e').evalOdd
                (F.evenColoursAt ψ (blockVertex W v))
                (F.oddListAt o φ (blockVertex W v))) := by
          rw [← hsplitR]
  -- ═══════ SOME BLOCK REPEATS AN ODD VALUE ═══════
  -- That block's factor is zero, and so is the vertex product.
  · push Not at hnd
    obtain ⟨v₀, hv₀⟩ := hnd
    have hL0 : (∏ v, starCoord f P e'
        ((degList (starAssignEnum W)).get v)
        (blockRestrict (degList (starAssignEnum W))
          (((colouringOfFlip W F o ψ φ) ∘ finCongr
            (degList_sum (starAssignEnum W))) ∘
            sortSplitPerm W) v)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ v₀)
        (starCoord_block_flip_not_nodup f P e e' hee' he'e
          W F o ψ φ v₀ hv₀)
    have hR0 : (∏ v : Fin (ds W).length,
        ((F.oddSignAt o φ (blockVertex W v) : ℂ) *
          (hRS f P e').evalOdd
            (F.evenColoursAt ψ (blockVertex W v))
            (F.oddListAt o φ (blockVertex W v)))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ v₀)
        (by rw [MixedFunctional.evalOdd_of_not_nodup _ _
            hv₀, mul_zero])
    rw [hL0, hR0]
    ring

open scoped Classical in
/-- **The fibre identity**, assembled from the vanishing branches
and the termwise value identity. -/
theorem fibreSum_eq
    (hee' : (e' ≫ e : P.ω.obj (SkeinObj.mk 1) ⟶
      P.ω.obj (SkeinObj.mk 1)) = 𝟙 _)
    (he'e : (e ≫ e' : stdSuperPair k ℓ ⟶ stdSuperPair k ℓ) = 𝟙 _)
    (W : ClosedFragment)
    (s : Finset W.Flag) :
    (∑ c ∈ Finset.univ.filter
        (fun c : {c : MixedColouring k ℓ
            (edgeCount W + edgeCount W) // c.IsEven} =>
          colourFlags W c.val = s),
      masterSummand f P e' W c.val) =
    (if hc : ∀ g ∈ s, W.pairing g ∈ s then
      if (EdgeSubset.mk s hc).Eulerian then
        (EdgeSubset.mk s hc).mixedValue (hRS f P e')
      else 0
    else 0) := by
  by_cases hc : ∀ g ∈ s, W.pairing g ∈ s
  · rw [dite_eq_left hc]
    by_cases hE : (EdgeSubset.mk s hc).Eulerian
    · rw [ite_eq_left hE]
      set F := EdgeSubset.mk s hc with hF
      obtain ⟨⟨κ, o⟩⟩ :=
        ClosedFragment.eulerian_transition_nonempty W F hE
      have hdata := fibreSum_eq_dataSum f P e' W F
      rw [show (Finset.univ.filter
          (fun c : {c : MixedColouring k ℓ
              (edgeCount W + edgeCount W) // c.IsEven} =>
            colourFlags W c.val = s)) =
        (Finset.univ.filter
          (fun c : {c : MixedColouring k ℓ
              (edgeCount W + edgeCount W) // c.IsEven} =>
            colourFlags W c.val = F.flags)) from rfl]
      rw [hdata]
      have hflip : ∀ ψ : F.EvenColouring k,
          (∑ φ : F.OddColouring ℓ,
            masterSummand f P e' W (colouringOf W F ψ φ)) =
          ∑ φ : F.OddColouring ℓ,
            masterSummand f P e' W
              (colouringOfFlip W F o ψ φ) := by
        intro ψ
        exact (EdgeSubset.OddColouring.sum_flip F
          (outRepSet W F o) (outRepSet_pairing_mem W F o)
          (fun φ => masterSummand f P e' W
            (colouringOf W F ψ φ))).symm
      rw [Finset.sum_congr rfl (fun ψ _ => hflip ψ)]
      rw [Finset.sum_congr rfl (fun ψ _ =>
        Finset.sum_congr rfl (fun φ _ =>
          masterSummand_colouringOfFlip f P e e' hee' he'e
            W F o ψ φ))]
      rw [show (∑ ψ : F.EvenColouring k,
          ∑ φ : F.OddColouring ℓ,
          ((-1 : ℂ) ^ κ.circuitCount) *
            ∏ v : W.Vertex,
              ((F.oddSignAt o φ v : ℂ) *
                (hRS f P e').evalOdd (F.evenColoursAt ψ v)
                  (F.oddListAt o φ v))) =
        ((-1 : ℂ) ^ κ.circuitCount) *
          ∑ ψ : F.EvenColouring k,
          ∑ φ : F.OddColouring ℓ,
            ∏ v : W.Vertex,
              ((F.oddSignAt o φ v : ℂ) *
                (hRS f P e').evalOdd (F.evenColoursAt ψ v)
                  (F.oddListAt o φ v)) from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun ψ _ =>
          (Finset.mul_sum _ _ _).symm)]
      rw [show ((-1 : ℂ) ^ κ.circuitCount) *
          (∑ ψ : F.EvenColouring k,
          ∑ φ : F.OddColouring ℓ,
            ∏ v : W.Vertex,
              ((F.oddSignAt o φ v : ℂ) *
                (hRS f P e').evalOdd (F.evenColoursAt ψ v)
                  (F.oddListAt o φ v))) =
        F.mixedSummand (hRS f P e') o from rfl]
      exact (mixedValue_eq_summand_closed W F
        (hRS f P e') o).symm
    · rw [ite_eq_right hE]
      refine Finset.sum_eq_zero (fun c hcmem => ?_)
      rw [Finset.mem_filter] at hcmem
      exact masterSummand_vanish_of_not_eulerian f P e' W
        c.val s hc hcmem.2 hE
  · rw [dite_eq_right hc]
    refine Finset.sum_eq_zero (fun c hcmem => ?_)
    rw [Finset.mem_filter] at hcmem
    exact masterSummand_vanish_of_not_closed f P e' W
      c.val s hcmem.2 hc

/-- **The conditional master identity**. -/
theorem parameter_eq_mixedPartition (W : ClosedFragment)
    (hee' : (e' ≫ e : P.ω.obj (SkeinObj.mk 1) ⟶
      P.ω.obj (SkeinObj.mk 1)) = 𝟙 _)
    (he'e : (e ≫ e' : stdSuperPair k ℓ ⟶ stdSuperPair k ℓ) = 𝟙 _)
    (hform :
      letI := P.braided
      SuperVect.Hom.comp
        (μ P.ω (SkeinObj.mk 1) (SkeinObj.mk 1) ≫
          P.ω.map (ε_ (SkeinObj.mk 1) (SkeinObj.mk 1)) ≫
          η P.ω)
        (SuperVect.tensorHom e e) = stdForm k ℓ)
    (hcopair :
      letI := P.braided
      SuperVect.Hom.comp (SuperVect.tensorHom e' e')
        (ε P.ω ≫ P.ω.map (η_ (SkeinObj.mk 1)
            (SkeinObj.mk 1)) ≫
          δ P.ω (SkeinObj.mk 1) (SkeinObj.mk 1)) =
        stdCopair k ℓ) :
    f.val W = mixedPartition (hRS f P e') W := by
  classical
  rw [parameter_masterSummand f P e e' W hee' hform]
  rw [masterSum_partition]
  rw [show mixedPartition (hRS f P e') W =
    ((k : ℂ) - 2 * ℓ) ^ W.circles *
      ∑ s : Finset W.Flag,
        (if hc : ∀ g ∈ s, W.pairing g ∈ s then
          if (EdgeSubset.mk s hc).Eulerian then
            (EdgeSubset.mk s hc).mixedValue (hRS f P e')
          else 0
        else 0) from rfl]
  rw [circleVal_model f P e e' hee' hform hcopair]
  congr 1
  exact Finset.sum_congr rfl (fun s _ =>
    fibreSum_eq f P e e' hee' he'e W s)

end RS
