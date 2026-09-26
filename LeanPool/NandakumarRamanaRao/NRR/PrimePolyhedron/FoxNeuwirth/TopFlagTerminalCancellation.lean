/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.TopFlagSubdivision
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.FacetShuffleEquiv
/-!
# Terminal cancellation for the top-flag subdivision

This module proves the terminal half of Step S3.  A terminal boundary face is a strict flag whose
last vertex is a Fox--Neuwirth facet.  Appending a top cell to that flag is equivalent to choosing a
top-cell extension of the final facet.  The coefficient of the resulting maximal flag is
independent of the chosen extension, while the number of extensions is divisible by the prime by
the facet--shuffle equivalence.

The proof is deliberately separated from the internal rank-two cancellation.  No classification
of rank-two intervals is used here.
-/

@[expose] public section

namespace NRR

open scoped BigOperators

variable {p d : Nat}

namespace FoxNeuwirthOrderComplex

namespace Simplex

/-- The index of a vertex in a strict chain is bounded by its dual dimension. -/
theorem index_le_dualDimension (s : Simplex p d) (i : Fin (d + 1)) :
    i.1 ≤ (s i).dualDimension := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
      have hlt : (s i.castSucc).dualDimension < (s i.succ).dualDimension :=
        (s.properFace (Fin.castSucc_lt_succ (i := i))).2
      simp only [Fin.val_succ, Fin.val_castSucc] at ih ⊢
      omega

/-- Append one cell above every vertex of a strict flag. -/
def snoc (s : Simplex p d) (c : BarredPermutation p)
    (hc : ∀ i : Fin (d + 1), ProperFace (s i) c) : Simplex p (d + 1) :=
  ⟨Fin.lastCases c (fun i => s i), by
    intro i j hij
    induction j using Fin.lastCases with
    | last =>
      induction i using Fin.lastCases with
      | last => exact absurd hij (lt_irrefl _)
      | cast i' => simpa using hc i'
    | cast j' =>
      induction i using Fin.lastCases with
      | last =>
          exact absurd hij (by
            simp only [Fin.lt_def, Fin.val_last, Fin.val_castSucc]
            omega)
      | cast i' =>
          have hlt : i' < j' := by
            have hji := hij
            simp only [Fin.castSucc_lt_castSucc_iff] at hji
            exact hji
          simpa using s.properFace hlt⟩

@[simp] theorem snoc_last (s : Simplex p d) (c : BarredPermutation p)
    (hc : ∀ i : Fin (d + 1), ProperFace (s i) c) :
    snoc s c hc (Fin.last (d + 1)) = c := by
  simp [snoc]

@[simp] theorem snoc_castSucc (s : Simplex p d) (c : BarredPermutation p)
    (hc : ∀ i : Fin (d + 1), ProperFace (s i) c) (i : Fin (d + 1)) :
    snoc s c hc i.castSucc = s i := by
  simp [snoc]

/-- Deleting the appended final vertex recovers the original simplex. -/
theorem snoc_restrict_omit_last (s : Simplex p d) (c : BarredPermutation p)
    (hc : ∀ i : Fin (d + 1), ProperFace (s i) c) :
    (snoc s c hc).restrict (FaceMap.delete (Fin.last (d + 1))) = s := by
  apply Simplex.ext
  intro i
  rw [Simplex.restrict_apply, FaceMap.delete_apply, Fin.succAbove_last,
    snoc_castSucc]

end Simplex

namespace TopFlagSubdivision

/-- Every Fox--Neuwirth dual dimension is at most `p - 1` when `p` is positive. -/
theorem dualDimension_le_top
    (hp0 : 0 < p) (c : BarredPermutation p) :
    c.dualDimension ≤ p - 1 := by
  rw [BarredPermutation.dualDimension_eq c hp0]
  omega

/-- A cell of maximal dual dimension is a top cell. -/
theorem isTop_of_dualDimension_eq_top
    (hp0 : 0 < p) (c : BarredPermutation p)
    (hc : c.dualDimension = p - 1) :
    c.IsTop := by
  have hcard := c.bars_card_le
  rw [BarredPermutation.dualDimension_eq c hp0] at hc
  unfold BarredPermutation.IsTop
  apply Finset.card_eq_zero.mp
  omega

/-- The final vertex of a maximal strict flag has top dual dimension. -/
theorem maximal_last_dualDimension
    (hp : Nat.Prime p) (s : Simplex p (p - 1)) :
    (s (Fin.last (p - 1))).dualDimension = p - 1 := by
  apply Nat.le_antisymm
  · exact dualDimension_le_top hp.pos _
  · simpa using Simplex.index_le_dualDimension s (Fin.last (p - 1))

/-- The terminal deletion index in the arithmetic presentation used by `deletionCoefficient`. -/
def terminalIndex (hp : Nat.Prime p) : Fin ((p - 2) + 2) :=
  ⟨p - 1, by
    have := hp.two_le
    omega⟩

@[simp] theorem terminalIndex_val (hp : Nat.Prime p) :
    (terminalIndex hp).1 = p - 1 :=
  rfl

/-- The terminal index is the last index of the maximal flag. -/
theorem terminalIndex_eq_last (hp : Nat.Prime p) :
    terminalIndex hp = Fin.last ((p - 2) + 1) := by
  apply Fin.ext
  simp only [terminalIndex_val, Fin.val_last]
  have := hp.two_le
  omega

/-- Maximal flags whose terminal face is a fixed codimension-one flag. -/
def TerminalSource (hp : Nat.Prime p) (target : Simplex p (p - 2)) :=
  {source : Simplex p ((p - 2) + 1) //
    source.restrict (FaceMap.delete (terminalIndex hp)) = target}

noncomputable instance (hp : Nat.Prime p) (target : Simplex p (p - 2)) :
    Fintype (TerminalSource hp target) := by unfold TerminalSource; infer_instance

noncomputable instance (hp : Nat.Prime p) (target : Simplex p (p - 2)) :
    DecidableEq (TerminalSource hp target) := by unfold TerminalSource; infer_instance

/-- Initial vertices of a terminal source agree with the target flag. -/
theorem terminalSource_castSucc
    (hp : Nat.Prime p) (target : Simplex p (p - 2))
    (u : TerminalSource hp target) (i : Fin ((p - 2) + 1)) :
    u.1 i.castSucc = target i := by
  have h : u.1.restrict (FaceMap.delete (terminalIndex hp)) i = target i := by rw [u.2]
  rw [Simplex.restrict_apply] at h
  simpa [terminalIndex_eq_last hp, FaceMap.delete] using h

/-- The last vertex of a terminal source has maximal dimension. -/
theorem terminalSource_last_dualDimension
    (hp : Nat.Prime p) (target : Simplex p (p - 2))
    (u : TerminalSource hp target) :
    (u.1 (Fin.last ((p - 2) + 1))).dualDimension = p - 1 := by
  apply Nat.le_antisymm
  · exact dualDimension_le_top hp.pos _
  · have hlow := Simplex.index_le_dualDimension u.1 (Fin.last ((p - 2) + 1))
    simp only [Fin.val_last] at hlow
    have := hp.two_le
    omega

/-- If a terminal source exists, the last target vertex is a facet-dimensional cell. -/
theorem terminalSource_target_last_dualDimension
    (hp : Nat.Prime p) (target : Simplex p (p - 2))
    (u : TerminalSource hp target) :
    (target (Fin.last (p - 2))).dualDimension = p - 2 := by
  have hlow := Simplex.index_le_dualDimension target (Fin.last (p - 2))
  have hface := u.1.properFace
    (Fin.castSucc_lt_last (n := (p - 2) + 1) (Fin.last (p - 2)))
  have htop := terminalSource_last_dualDimension hp target u
  have hinit := terminalSource_castSucc hp target u (Fin.last (p - 2))
  have hlt := hface.2
  rw [hinit, htop] at hlt
  simp only [Fin.val_last] at hlow
  omega

/-- A terminal source determines a top-cell extension of the final target facet. -/
noncomputable def terminalSourceToTopExtension
    (hp : Nat.Prime p) (target : Simplex p (p - 2))
    (u : TerminalSource hp target) :
    FoxNeuwirth.TopExtension (target (Fin.last (p - 2))) := by
  let c : BarredPermutation p := u.1 (Fin.last ((p - 2) + 1))
  have hcdim : c.dualDimension = p - 1 :=
    terminalSource_last_dualDimension hp target u
  have hctop : c.IsTop := isTop_of_dualDimension_eq_top hp.pos c hcdim
  refine ⟨⟨c, hctop⟩, ?_⟩
  have hface := u.1.properFace
    (Fin.castSucc_lt_last (n := (p - 2) + 1) (Fin.last (p - 2)))
  have hinit := terminalSource_castSucc hp target u (Fin.last (p - 2))
  have hfdim := terminalSource_target_last_dualDimension hp target u
  refine ⟨?_, ?_⟩
  · simpa [c, hinit] using hface.1
  · have h2 := hp.two_le
    simp only [c, hfdim, hcdim]
    omega

/-- Every vertex of the target lies properly below any top extension of its final facet. -/
theorem properFace_topExtension
    (hp : Nat.Prime p) (target : Simplex p (p - 2))
    (ha : (target (Fin.last (p - 2))).dualDimension = p - 2)
    (c : FoxNeuwirth.TopExtension (target (Fin.last (p - 2))))
    (i : Fin ((p - 2) + 1)) :
    ProperFace (target i) (c.1 : BarredPermutation p) := by
  have hfacet : ProperFace (target (Fin.last (p - 2))) (c.1 : BarredPermutation p) := by
    refine ⟨c.2.1, ?_⟩
    have htop := BarredPermutation.TopCell.dimension hp c.1
    have := hp.two_le
    omega
  by_cases hi : i = Fin.last (p - 2)
  · simpa [hi] using hfacet
  · have hilt : i < Fin.last (p - 2) := by
      apply Fin.lt_def.mpr
      have hi' : i.1 ≠ p - 2 := by
        intro hval
        apply hi
        apply Fin.ext
        simpa using hval
      have hiBound := i.2
      simp only [Fin.val_last]
      omega
    exact properFace_trans (target.properFace hilt) hfacet

/-- Append a chosen top extension to the target flag. -/
noncomputable def topExtensionToTerminalSource
    (hp : Nat.Prime p) (target : Simplex p (p - 2))
    (ha : (target (Fin.last (p - 2))).dualDimension = p - 2)
    (c : FoxNeuwirth.TopExtension (target (Fin.last (p - 2)))) :
    TerminalSource hp target := by
  let source : Simplex p ((p - 2) + 1) :=
    Simplex.snoc target (c.1 : BarredPermutation p)
      (properFace_topExtension hp target ha c)
  refine ⟨source, ?_⟩
  rw [terminalIndex_eq_last hp]
  exact Simplex.snoc_restrict_omit_last target (c.1 : BarredPermutation p)
    (properFace_topExtension hp target ha c)

/-- Terminal source flags are exactly top-cell extensions of the final facet. -/
noncomputable def terminalSourceEquivTopExtension
    (hp : Nat.Prime p) (target : Simplex p (p - 2))
    (u0 : TerminalSource hp target) :
    TerminalSource hp target ≃
      FoxNeuwirth.TopExtension (target (Fin.last (p - 2))) where
  toFun := terminalSourceToTopExtension hp target
  invFun := topExtensionToTerminalSource hp target
    (terminalSource_target_last_dualDimension hp target u0)
  left_inv := by
    intro u
    apply Subtype.ext
    apply Simplex.ext
    intro i
    cases i using Fin.lastCases with
    | last =>
        simp only [topExtensionToTerminalSource, terminalSourceToTopExtension]
        simp [Simplex.snoc_last]
    | cast i =>
        simp only [topExtensionToTerminalSource]
        simp [Simplex.snoc_castSucc, terminalSource_castSucc hp target u]
  right_inv := by
    intro c
    simp only [terminalSourceToTopExtension, topExtensionToTerminalSource]
    apply Subtype.ext
    apply Subtype.ext
    simp [Simplex.snoc_last]

/-- Cast-free core: the subdivision chain value depends only on the head vertex and the
bar-difference matrix. -/
theorem chain_eq_of_head_matrix (w w' : Simplex p (p - 1))
    (h0 : w 0 = w' 0)
    (hm : barDifferenceMatrix w = barDifferenceMatrix w') :
    chain w = chain w' := by
  simp only [chain_apply, integralCoefficient, barRemovalDeterminant, h0, hm]

/-- Applying a dimension-transported simplicial chain equals the chain applied to the
transported simplex. -/
theorem simplicialChain_cast_apply {p d d' : Nat} (h : d = d')
    (f : SimplicialChain (ZMod p) p d) (w : Simplex p d') :
    (h ▸ f) w = f (h.symm ▸ w) := by
  subst h; rfl

/-- Evaluating a dimension-transported simplex is evaluation at the reindexed vertex. -/
theorem simplex_cast_apply {p d d' : Nat} (h : d = d') (s : Simplex p d) (j : Fin (d' + 1)) :
    (h ▸ s) j = s (Fin.cast (by rw [h]) j) := by
  subst h; rfl

/-- `chain` transported to the index `(p - 2) + 1` used by the terminal deletion. -/
noncomputable def liftedTerminalChain (hp : Nat.Prime p) :
    SimplicialChain (ZMod p) p ((p - 2) + 1) :=
  (show p - 1 = (p - 2) + 1 by have := hp.two_le; omega) ▸ chain

/-- Any two terminal sources of the same target flag carry the same transported chain value:
their initial faces agree (both restrict to `target`) and their final vertices are top cells, so
the subdivision coefficient is independent of the terminal source. -/
theorem liftedTerminalChain_eq_of_terminalSource
    (hp : Nat.Prime p) (target : Simplex p (p - 2))
    (u v : TerminalSource hp target) :
    liftedTerminalChain hp u.1 = liftedTerminalChain hp v.1 := by
  unfold liftedTerminalChain
  rw [simplicialChain_cast_apply]
  rw [simplicialChain_cast_apply]
  apply chain_eq_of_head_matrix
  · -- head vertex
    simp only [simplex_cast_apply, Fin.cast_zero]
    exact (terminalSource_castSucc hp target u 0).trans (terminalSource_castSucc hp target v 0).symm
  · -- barDifferenceMatrix
    ext k r
    simp only [barDifferenceMatrix, simplex_cast_apply]
    have hp2 : 2 ≤ p := hp.two_le
    have heq : p - 1 + 1 = (p - 2) + 1 + 1 := by omega
    have hpc : (p - 1) = (p - 2) + 1 := by omega
    have hnp1 : NeZero (p - 1) := ⟨by omega⟩
    -- Let r' = Fin.cast hpc r : Fin ((p - 2) + 1)
    -- Then Fin.cast heq (r.castSucc) = (r').castSucc (both have value r.val in Fin p)
    -- And Fin.cast heq (r.succ) = (r').succ (both have value r.val + 1 in Fin p)
    have hv_cast_r : (Fin.cast hpc r : ℕ) = (r : ℕ) := by rfl
    have hrcast_eq : Fin.cast heq (Fin.castSucc r) = Fin.castSucc (Fin.cast hpc r) := by
      apply Fin.ext
      simp [Fin.val_castSucc]
    have rsucc_cast_eq : Fin.cast heq (Fin.succ r) = Fin.succ (Fin.cast hpc r) := by
      apply Fin.ext
      simp [Fin.val_succ]
    rw [hrcast_eq, rsucc_cast_eq]
    -- Now both sides use the same indices, so they're equal
    let r' : Fin ((p - 2) + 1) := Fin.cast hpc r
    have hu_cast := terminalSource_castSucc hp target u r'
    have hv_cast := terminalSource_castSucc hp target v r'
    -- For r'.castSucc: u.1 r'.castSucc = target r' = v.1 r'.castSucc
    -- For r'.succ: either r'.succ = i.castSucc for some i (then same as above)
    -- or r'.succ = Fin.last ((p-2)+1) : Fin p (then both are top cells, barIndicator = 0)
    have h_u_castSucc : u.1 r'.castSucc = v.1 r'.castSucc := hu_cast.trans hv_cast.symm
    -- For r'.succ, we need to handle two cases
    -- First, check if r' = Fin.last (p-2) : Fin ((p-2)+1)
    by_cases hr' : r' = Fin.last (p - 2)
    · -- Case: r' = Fin.last, so r'.succ = Fin.last ((p-2)+1) : Fin p, which is a top cell
      have hr'_last : r'.succ = Fin.last ((p - 2) + 1) := by
        simp only [hr', Fin.succ_last]
      rw [hr'_last]
      have hcdim : (u.1 (Fin.last ((p - 2) + 1))).dualDimension = p - 1 :=
        terminalSource_last_dualDimension hp target u
      have hctop : (u.1 (Fin.last ((p - 2) + 1))).IsTop := isTop_of_dualDimension_eq_top hp.pos
        _ hcdim
      have hcdim' : (v.1 (Fin.last ((p - 2) + 1))).dualDimension = p - 1 :=
        terminalSource_last_dualDimension hp target v
      have hctop' : (v.1 (Fin.last ((p - 2) + 1))).IsTop := isTop_of_dualDimension_eq_top hp.pos
        _ hcdim'
      simp only [barIndicator_of_not_mem _ _ (by rw [hctop]; simp), sub_zero,
        barIndicator_of_not_mem _ _ (by rw [hctop']; simp)]
      -- Need to show barIndicators are equal for the castSucc case
      have h_castSucc_eq : (Fin.cast hpc r).castSucc = r'.castSucc := rfl
      rw [h_castSucc_eq, hu_cast, hv_cast]
    · -- Case: r' ≠ Fin.last, so r'.succ = i.castSucc for some i
      -- Since r' < Fin.last, we have r'.succ = i.castSucc for i = r' + 1 (in Fin ((p-2)+1))
      have hr'_lt : r' < Fin.last (p - 2) := lt_of_le_of_ne (Fin.le_last _) hr'
      have hr'_val : r'.val < p - 2 := by
        simp only [Fin.lt_def, Fin.val_last] at hr'_lt
        exact hr'_lt
      -- Use i = r' + 1
      let i : Fin ((p - 2) + 1) := ⟨r'.val + 1, by omega⟩
      have hi_castSucc_u := terminalSource_castSucc hp target u i
      have hi_castSucc_v := terminalSource_castSucc hp target v i
      have hi_eq : i.castSucc = Fin.cast heq r.succ := by
        rw [rsucc_cast_eq]
        ext
        simp only [i, Fin.castSucc_mk]
        rfl
      have hi_bar_eq : barIndicator (u.1 i.castSucc) k = barIndicator (v.1 i.castSucc) k := by
        rw [hi_castSucc_u, hi_castSucc_v]
      have h_castSucc_eq : (Fin.cast hpc r).castSucc = r'.castSucc := rfl
      have h_castSucc_bar : barIndicator (u.1 (Fin.cast hpc r).castSucc) k = barIndicator (v.1
        (Fin.cast hpc r).castSucc) k := by
        rw [h_castSucc_eq, hu_cast, hv_cast]
      rw [← rsucc_cast_eq, hi_eq.symm]
      simp [hi_bar_eq, h_castSucc_bar]

/-- Reindex the terminal deletion sum by the actual terminal source subtype. -/
theorem deletionCoefficient_terminal_eq_source_sum
    (hp : Nat.Prime p) (target : Simplex p (p - 2)) :
    deletionCoefficient hp target (terminalIndex hp) =
      ∑ u : TerminalSource hp target,
        SimplicialChain.faceSign (R := ZMod p) (terminalIndex hp) *
          ((liftedTerminalChain hp) u.1) := by
  classical
  simp only [deletionCoefficient, SimplicialChain.faceContribution]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype
    (p := fun x => x.restrict (FaceMap.delete (terminalIndex hp)) = target)
    (Finset.univ.filter fun x => x.restrict (FaceMap.delete (terminalIndex hp)) = target)
    (fun x => by simp)
    (fun x => SimplicialChain.faceSign (R := ZMod p) (terminalIndex hp) *
      liftedTerminalChain hp x)

/-- The cardinality of the top-extension type vanishes in `ZMod p`. -/
theorem topExtension_card_cast_eq_zero
    (hp : Nat.Prime p) (a : BarredPermutation p) :
    (Fintype.card (FoxNeuwirth.TopExtension a) : ZMod p) = 0 := by
  rw [FoxNeuwirth.card_topExtension]
  have hdivInt : (p : Int) ∣ (FoxNeuwirth.topExtensionMultiplicity a : Int) := by
    exact_mod_cast FoxNeuwirth.prime_dvd_topExtensionMultiplicity hp
      (FoxNeuwirth.facetShuffleCardinality hp) a
  have hcast : ((FoxNeuwirth.topExtensionMultiplicity a : Int) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (FoxNeuwirth.topExtensionMultiplicity a : Int) p).2
      hdivInt
  exact_mod_cast hcast

/-- Terminal deleted faces cancel modulo the prime. -/
theorem terminalCancellation (hp : Nat.Prime p) : TerminalCancellation hp := by
  intro target k hk
  have hk' : k = terminalIndex hp := by
    apply Fin.ext
    simpa [terminalIndex] using hk
  subst k
  rw [deletionCoefficient_terminal_eq_source_sum hp target]
  classical
  by_cases hsrc : Nonempty (TerminalSource hp target)
  · let u0 : TerminalSource hp target := Classical.choice hsrc
    let e := terminalSourceEquivTopExtension hp target u0
    let a : BarredPermutation p := target (Fin.last (p - 2))
    let base : FoxNeuwirth.TopExtension a := e u0
    have hsum :
        (∑ u : TerminalSource hp target,
          SimplicialChain.faceSign (R := ZMod p) (terminalIndex hp) *
            ((liftedTerminalChain hp) u.1)) =
        ∑ c : FoxNeuwirth.TopExtension a,
          SimplicialChain.faceSign (R := ZMod p) (terminalIndex hp) *
            ((liftedTerminalChain hp) (e.symm c).1) := by
      simpa [a, e] using
        (Equiv.sum_comp e.symm
          (fun u : TerminalSource hp target =>
            SimplicialChain.faceSign (R := ZMod p) (terminalIndex hp) *
              ((liftedTerminalChain hp) u.1))).symm
    rw [hsum]
    have hconst : ∀ c : FoxNeuwirth.TopExtension a,
        ((liftedTerminalChain hp) (e.symm c).1) =
        ((liftedTerminalChain hp) (e.symm base).1) := by
      intro c
      exact liftedTerminalChain_eq_of_terminalSource hp target (e.symm c) (e.symm base)
    simp_rw [hconst]
    rw [show (∑ _c : FoxNeuwirth.TopExtension a,
        SimplicialChain.faceSign (R := ZMod p) (terminalIndex hp) *
          ((liftedTerminalChain hp) (e.symm base).1)) =
        (Fintype.card (FoxNeuwirth.TopExtension a) : ZMod p) *
          (SimplicialChain.faceSign (R := ZMod p) (terminalIndex hp) *
            ((liftedTerminalChain hp) (e.symm base).1)) by simp]
    rw [topExtension_card_cast_eq_zero hp a]
    simp
  · apply Finset.sum_eq_zero
    intro u hu
    exact (hsrc ⟨u⟩).elim

/-- The terminal local theorem required by the top-flag subdivision is unconditional. -/
theorem terminalMultiplicityTheorem : TerminalMultiplicityTheorem := by
  intro p hp
  exact terminalCancellation hp

/-- After terminal reindexing, only the rank-two internal pairing remains for the simplicial cycle.
-/
theorem cycle_of_rankTwo
    (hrank : RankTwoCancellationTheorem) :
    ∀ {p : Nat} (hp : Nat.Prime p), boundary hp = 0 :=
  cycle_of_rankTwo_and_terminal hrank terminalMultiplicityTheorem

end TopFlagSubdivision
end FoxNeuwirthOrderComplex

namespace AAK

/-- Step S3 terminal reindexing is complete. -/
theorem simplestRoute_terminalCancellation_complete :
    FoxNeuwirthOrderComplex.TopFlagSubdivision.TerminalMultiplicityTheorem :=
  FoxNeuwirthOrderComplex.TopFlagSubdivision.terminalMultiplicityTheorem

end AAK

end NRR
