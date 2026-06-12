/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import Mathlib.Data.Fintype.CardEmbedding

import LeanPool.TwoColoringOneRound.LowerBound.N1000000OrbitalBasis
import LeanPool.TwoColoringOneRound.LowerBound.N1000000MaskAtFacts
import LeanPool.TwoColoringOneRound.LowerBound.N1000000OrbitCounting
import LeanPool.TwoColoringOneRound.LowerBound.N1000000PairTransitivity
import LeanPool.TwoColoringOneRound.LowerBound.N1000000StructureConstants

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000IntersectionCounting
-/

namespace Distributed2Coloring.LowerBound

namespace N1000000IntersectionCounting

open scoped BigOperators

open Distributed2Coloring.LowerBound.N1000000OrbitalBasis
open Distributed2Coloring.LowerBound.N1000000MaskAtFacts
open Distributed2Coloring.LowerBound.N1000000OrbitCounting
open Distributed2Coloring.LowerBound.N1000000PairTransitivity
open Distributed2Coloring.LowerBound.N1000000StructureConstants

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev n : Nat := N1000000Data.n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev SymN := Sym n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev V := Vertex n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev DirIdx := N1000000StructureConstants.DirIdx

/-- The actual intersection fiber: vertices `v` with base-type `a` and relative-type `d` to `u`. -/
def Inter {k : DirIdx} (u : BaseOrbit k) (a d : DirIdx) : Type :=
  { v : V // dirMask baseVertex v = maskAt a ∧ dirMask v u.1 = maskAt d }

noncomputable instance {k : DirIdx} (u : BaseOrbit k) (a d : DirIdx) : Fintype (Inter u a d) := by
  dsimp [Inter]
  infer_instance

/-- Free coordinates for the intersection number `N[k][a][d]`: positions `j` where `v_j` is neither
a base symbol (`a`) nor a reused symbol from `u` (`d`). -/
def FreeCoord (a d : DirIdx) : Type :=
  { j : Fin 3 // colMatch (maskAt a) j = none ∧ rowMatch (maskAt d) j = none }

noncomputable instance (a d : DirIdx) : Fintype (FreeCoord a d) := by
  dsimp [FreeCoord]
  infer_instance

theorem card_freeCoord (a d : DirIdx) :
    Fintype.card (FreeCoord a d) = freeCoords (maskAt a) (maskAt d) := by
  classical
  exact Fintype.card_subtype
    (fun j : Fin 3 => colMatch (maskAt a) j = none ∧ rowMatch (maskAt d) j = none)

private noncomputable def freeSyms {k : DirIdx} (u : BaseOrbit k) : Finset SymN :=
  (Finset.univ : Finset (FreeCol k)).image (fun j => u.1.1 j.1)

private lemma freeSyms_disjoint_baseSet {k : DirIdx} (u : BaseOrbit k) :
    Disjoint (freeSyms (k := k) u) baseSet := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro x hxFree hxBase
  -- If `x ∈ baseSet`, then `x.1 < 3`.
  have hxlt : x.1 < 3 := by
    have : x = s0 ∨ x = s1 ∨ x = s2 := by
      simpa [baseSet] using hxBase
    rcases this with rfl | rfl | rfl <;> decide
  -- But `x ∈ freeSyms` comes from some free column, hence `x.1 ≥ 3`.
  rcases Finset.mem_image.1 hxFree with ⟨j, _hjUniv, rfl⟩
  have hxge : 3 ≤ (u.1.1 j.1).1 := baseOrbit_freeCoord_outside (u := u) j
  exact (Nat.not_lt_of_ge hxge hxlt).elim

private lemma card_freeSyms {k : DirIdx} (u : BaseOrbit k) :
    (freeSyms (k := k) u).card = Fintype.card (FreeCol k) := by
  classical
  -- The map `j ↦ u_j` is injective on `FreeCol k` since `u` is an injective triple.
  have hinj : Function.Injective (fun j : FreeCol k => u.1.1 j.1) := by
    intro a b hab
    apply Subtype.ext
    exact u.1.2 hab
  have hcard :
      (freeSyms (k := k) u).card = (Finset.univ : Finset (FreeCol k)).card := by
    simpa [freeSyms] using (Finset.card_image_of_injective (s := (Finset.univ : Finset (FreeCol k)))
      (f := fun j : FreeCol k => u.1.1 j.1) hinj)
  simp [hcard]

private lemma card_usedSet {k : DirIdx} (u : BaseOrbit k) :
    (baseSet ∪ freeSyms (k := k) u).card = 3 + freeCols (maskAt k) := by
  classical
  have hbase : baseSet.card = 3 := by
    simp [baseSet]
  have hdisj : Disjoint baseSet (freeSyms (k := k) u) := by
    simpa [disjoint_comm] using (freeSyms_disjoint_baseSet (k := k) u)
  have hfreeCard : (freeSyms (k := k) u).card = freeCols (maskAt k) := by
    -- `freeSyms.card = card FreeCol = freeCols`.
    have hCardFreeCol : Fintype.card (FreeCol k) = freeCols (maskAt k) := by
      classical
      exact Fintype.card_subtype (fun j : Fin 3 => colMatch (maskAt k) j = none)
    simpa [card_freeSyms (k := k) u] using hCardFreeCol
  calc
    (baseSet ∪ freeSyms (k := k) u).card
        = baseSet.card + (freeSyms (k := k) u).card := by
            simp [Finset.card_union_of_disjoint hdisj]
    _ = 3 + freeCols (maskAt k) := by simp [hbase, hfreeCard]

/-- Available symbols for new coordinates: those not in `baseSet` and not used by `u` on
its free columns. -/
def AvailFor {k : DirIdx} (u : BaseOrbit k) : Type :=
  { x : SymN // x ∉ (baseSet ∪ freeSyms (k := k) u) }

noncomputable instance {k : DirIdx} (u : BaseOrbit k) : Fintype (AvailFor u) := by
  dsimp [AvailFor]
  infer_instance

theorem card_availFor {k : DirIdx} (u : BaseOrbit k) :
    Fintype.card (AvailFor u) = n - (3 + freeCols (maskAt k)) := by
  classical
  -- Use `card_subtype_compl` on membership in the used finset.
  let used : Finset SymN := baseSet ∪ freeSyms (k := k) u
  have husedCard : used.card = 3 + freeCols (maskAt k) := by
    simpa [used] using card_usedSet (k := k) u
  have hsubCard : Fintype.card (↑used) = used.card := by
    simp
  -- `AvailFor u` is the complement subtype.
  have hcompl :
      Fintype.card (AvailFor u)
        = Fintype.card SymN - Fintype.card (↑used) := by
    -- `p x := x ∈ used`
    simpa [AvailFor,
      used] using (Fintype.card_subtype_compl (α := SymN) (p := fun x : SymN => x ∈ used))
  -- `card SymN = n`.
  have hSym : Fintype.card SymN = n := by simp [SymN, Sym]
  -- Finish.
  calc
    Fintype.card (AvailFor u)
        = Fintype.card SymN - Fintype.card (↑used) := hcompl
    _ = n - used.card := by simp [hSym, hsubCard]
    _ = n - (3 + freeCols (maskAt k)) := by simp [husedCard]

theorem card_embedding_freeCoord_availFor {k a d : DirIdx} (u : BaseOrbit k) :
    Fintype.card (FreeCoord a d ↪ AvailFor u) =
      (n - (3 + freeCols (maskAt k))).descFactorial (freeCoords (maskAt a) (maskAt d)) := by
  classical
  -- `card (α ↪ β) = card β P (card α)` for finite types.
  have hEmb :
      Fintype.card (FreeCoord a d ↪ AvailFor u)
        = (Fintype.card (AvailFor u)).descFactorial (Fintype.card (FreeCoord a d)) := by
    exact (Fintype.card_embedding_eq (α := FreeCoord a d) (β := AvailFor u))
  -- Rewrite cardinalities.
  simp [hEmb, card_availFor (u := u), card_freeCoord (a := a) (d := d)]

/-!
Intersection numbers.

For `u : BaseOrbit k`, we show `card (Inter u a d) = N k a d`, where `N` is the closed-form
structure-constant formula from `N1000000StructureConstants`.
-/

private lemma not_mem_baseSet_of_ge_three {x : SymN} (hx : 3 ≤ x.1) : x ∉ baseSet := by
  intro hxmem
  have hxlt : x.1 < 3 := by
    -- `x ∈ {0,1,2}`
    have : x = s0 ∨ x = s1 ∨ x = s2 := by
      simpa [baseSet] using hxmem
    rcases this with rfl | rfl | rfl <;> decide
  exact (Nat.not_lt_of_ge hx hxlt).elim

private lemma sym_mem_baseSet_of_lt_three {x : SymN} (hx : x.1 < 3) : x ∈ baseSet := by
  have : x.1 = 0 ∨ x.1 = 1 ∨ x.1 = 2 := by
    omega
  rcases this with hx0 | hx1 | hx2
  · -- `x = s0`
    have : x = s0 := by
      apply Fin.ext
      simp [hx0]
    simp [this, baseSet]
  · -- `x = s1`
    have : x = s1 := by
      apply Fin.ext
      simp [hx1]
    simp [this, baseSet]
  · -- `x = s2`
    have : x = s2 := by
      apply Fin.ext
      simp [hx2]
    simp [this, baseSet]

private lemma ge_three_of_not_mem_baseSet {x : SymN} (hx : x ∉ baseSet) : 3 ≤ x.1 := by
  by_contra hge
  have hxlt : x.1 < 3 := Nat.lt_of_not_ge hge
  exact hx (sym_mem_baseSet_of_lt_three (x := x) hxlt)

private lemma eq_of_dirMask_rowMatch {u v : V} {d : DirIdx} (h : dirMask u v = maskAt d)
    {i j : Fin 3} (hrow : rowMatch (maskAt d) i = some j) : u.1 i = v.1 j := by
  -- Compare the `(i,j)` bit in `dirMask u v = maskAt d`.
  have hm :
      (maskAt d).testBit (i.1 * 3 + j.1) = decide (rowMatch (maskAt d) i = some j) := by
    exact (maskAt_testBit_eq_decide_rowMatch (d := d) (i := i) (j := j))
  have hmTrue : (maskAt d).testBit (i.1 * 3 + j.1) = true := by
    simp [hm, hrow]
  have hdTrue : (dirMask u v).testBit (i.1 * 3 + j.1) = true := by
    exact (congrArg (fun z => z.testBit (i.1 * 3 + j.1)) h).trans hmTrue
  have hd :
      (dirMask u v).testBit (i.1 * 3 + j.1) = decide (u.1 i = v.1 j) := by
    simp [dirMask_testBit]
  have hdec : decide (u.1 i = v.1 j) = true := hd.symm.trans hdTrue
  exact of_decide_eq_true hdec

private lemma ne_of_dirMask_rowMatch_none {u v : V} {d : DirIdx} (h : dirMask u v = maskAt d)
    {i : Fin 3} (hrow : rowMatch (maskAt d) i = none) : ∀ j : Fin 3, u.1 i ≠ v.1 j := by
  intro j
  have hm :
      (maskAt d).testBit (i.1 * 3 + j.1) = decide (rowMatch (maskAt d) i = some j) := by
    exact (maskAt_testBit_eq_decide_rowMatch (d := d) (i := i) (j := j))
  have hmFalse : (maskAt d).testBit (i.1 * 3 + j.1) = false := by
    have : decide (rowMatch (maskAt d) i = some j) = false := by simp [hrow]
    simp [hm, this]
  have hdFalse : (dirMask u v).testBit (i.1 * 3 + j.1) = false := by
    exact (congrArg (fun z => z.testBit (i.1 * 3 + j.1)) h).trans hmFalse
  have hd :
      (dirMask u v).testBit (i.1 * 3 + j.1) = decide (u.1 i = v.1 j) := by
    simp [dirMask_testBit]
  have hdec : decide (u.1 i = v.1 j) = false := hd.symm.trans hdFalse
  exact (decide_eq_false_iff_not).1 hdec

private lemma u_coord_mem_usedSet {k : DirIdx} (u : BaseOrbit k) (j : Fin 3) :
    u.1.1 j ∈ (baseSet ∪ freeSyms (k := k) u) := by
  classical
  by_cases hcol : colMatch (maskAt k) j = none
  · -- `j` is a free column, so `u_j ∈ freeSyms`.
    have : u.1.1 j ∈ freeSyms (k := k) u := by
      refine Finset.mem_image.2 ?_
      refine ⟨⟨j, hcol⟩, by simp, rfl⟩
    exact Finset.mem_union_right _ this
  · -- `j` is fixed, so `u_j` is one of the base symbols.
    rcases (Option.ne_none_iff_exists').1 hcol with ⟨i, hi⟩
    have hEq : u.1.1 j = baseVertex.1 i := by
      simpa using (base_eq_of_colMatch (k := k) (u := u) (j := j) (i := i) (h := hi))
    have hmem : baseVertex.1 i ∈ baseSet := by
      fin_cases i <;> simp [baseVertex, baseTuple, baseSet, s0, s1, s2]
    have : u.1.1 j ∈ baseSet := by simpa [hEq] using hmem
    exact Finset.mem_union_left _ this

private lemma availFor_ne_u_coord {k : DirIdx} (u : BaseOrbit k) (x : AvailFor u) (j : Fin 3) :
    x.1 ≠ u.1.1 j := by
  intro hEq
  have hxmem : x.1 ∈ (baseSet ∪ freeSyms (k := k) u) := by
    simpa [hEq] using u_coord_mem_usedSet (k := k) u j
  exact x.2 hxmem

private lemma consistentAt_of_consistent {k a d : DirIdx}
    (h : consistent (maskAt k) (maskAt a) (maskAt d) = true) (j : Fin 3) :
    consistentAt (maskAt k) (maskAt a) (maskAt d) j = true := by
  have h'' :
      (consistentAt (maskAt k) (maskAt a) (maskAt d) ⟨0, by decide⟩ = true ∧
          consistentAt (maskAt k) (maskAt a) (maskAt d) ⟨1, by decide⟩ = true) ∧
        consistentAt (maskAt k) (maskAt a) (maskAt d) ⟨2, by decide⟩ = true := by
    simpa [consistent] using h
  have h' :
      consistentAt (maskAt k) (maskAt a) (maskAt d) ⟨0, by decide⟩ = true ∧
        consistentAt (maskAt k) (maskAt a) (maskAt d) ⟨1, by decide⟩ = true ∧
          consistentAt (maskAt k) (maskAt a) (maskAt d) ⟨2, by decide⟩ = true :=
    (and_assoc).1 h''
  fin_cases j
  · simpa using h'.1
  · simpa using h'.2.1
  · simpa using h'.2.2

private lemma rowMatch_baseOrbit_of_eq {k : DirIdx} (u : BaseOrbit k) {i j : Fin 3}
    (hEq : baseVertex.1 i = u.1.1 j) : rowMatch (maskAt k) i = some j := by
  -- Compare the `(i,j)` bit in `dirMask baseVertex u = maskAt k`.
  have hbitDir :
      (dirMask baseVertex u.1).testBit (i.1 * 3 + j.1) = true := by
    have hbit :
        (dirMask baseVertex u.1).testBit (i.1 * 3 + j.1) = decide (baseVertex.1 i = u.1.1 j) := by
      exact dirMask_testBit (u := baseVertex) (v := u.1) (i := i) (j := j)
    simp [hbit, hEq]
  have hbitMask : (maskAt k).testBit (i.1 * 3 + j.1) = true := by
    simpa [u.2] using hbitDir
  have hm :
      (maskAt k).testBit (i.1 * 3 + j.1) = decide (rowMatch (maskAt k) i = some j) := by
    simpa using (maskAt_testBit_eq_decide_rowMatch (d := k) (i := i) (j := j))
  have : decide (rowMatch (maskAt k) i = some j) = true := by
    simpa [hm] using hbitMask
  exact of_decide_eq_true this

private lemma consistent_of_inter {k : DirIdx} (u : BaseOrbit k) (a d : DirIdx) (w : Inter u a d) :
    consistent (maskAt k) (maskAt a) (maskAt d) = true := by
  classical
  -- Show `consistentAt ... j = true` for each coordinate.
  have hAt : ∀ j : Fin 3, consistentAt (maskAt k) (maskAt a) (maskAt d) j = true := by
    intro j
    have hbase : dirMask baseVertex w.1 = maskAt a := w.2.1
    have hrel : dirMask w.1 u.1 = maskAt d := w.2.2
    cases hcol : colMatch (maskAt a) j with
    | some i =>
        cases hrow : rowMatch (maskAt d) j with
        | none =>
            -- Need `rowMatch k i = none`.
            have hvj : w.1.1 j = baseVertex.1 i := by
              simpa using
                (base_eq_of_colMatch (k := a) (u := ⟨w.1, hbase⟩) (j := j) (i := i) (h := hcol))
            by_cases hk : rowMatch (maskAt k) i = none
            · simp [consistentAt, hcol, hrow, hk]
            · exfalso
              rcases (Option.ne_none_iff_exists').1 hk with ⟨l, hl⟩
              have hubase : baseVertex.1 i = u.1.1 l := by
                have :=
                  eq_of_dirMask_rowMatch (u := baseVertex) (v := u.1) (d := k)
                    (h := u.2) (i := i) (j := l) hl
                simpa [eq_comm] using this
              have hwul : w.1.1 j = u.1.1 l := by simp [hvj, hubase]
              have hne :=
                ne_of_dirMask_rowMatch_none (u := w.1) (v := u.1) (d := d) (h := hrel) (i := j) hrow
              exact (hne l) hwul
        | some l =>
            -- Need `rowMatch k i = some l`.
            have hvj : w.1.1 j = baseVertex.1 i := by
              simpa using
                (base_eq_of_colMatch (k := a) (u := ⟨w.1, hbase⟩) (j := j) (i := i) (h := hcol))
            have hvu : w.1.1 j = u.1.1 l :=
              eq_of_dirMask_rowMatch (u := w.1) (v := u.1) (d := d) (h := hrel)
                (i := j) (j := l) hrow
            have hubase : baseVertex.1 i = u.1.1 l := by simpa [hvj] using hvu
            have hk : rowMatch (maskAt k) i = some l := rowMatch_baseOrbit_of_eq (u := u) hubase
            simp [consistentAt, hcol, hrow, hk]
    | none =>
        cases hrow : rowMatch (maskAt d) j with
        | none =>
            simp [consistentAt, hcol, hrow]
        | some l =>
            -- Need `colMatch k l = none`.
            by_cases hk : colMatch (maskAt k) l = none
            · simp [consistentAt, hcol, hrow, hk]
            · rcases (Option.ne_none_iff_exists').1 hk with ⟨i, hi⟩
              have hubase : u.1.1 l = baseVertex.1 i := by
                simpa using (base_eq_of_colMatch (k := k) (u := u) (j := l) (i := i) (h := hi))
              have hvu : w.1.1 j = u.1.1 l :=
                eq_of_dirMask_rowMatch (u := w.1) (v := u.1) (d := d)
                  (h := hrel) (i := j) (j := l) hrow
              have hvbase : w.1.1 j = baseVertex.1 i := by simp [hvu, hubase]
              have hwge : 3 ≤ (w.1.1 j).1 := by
                exact baseOrbit_freeCoord_outside (u := ⟨w.1, hbase⟩) ⟨j, hcol⟩
              have hlt : (baseVertex.1 i).1 < 3 := by
                fin_cases i <;> decide
              have : (w.1.1 j).1 < 3 := by simpa [hvbase] using hlt
              exact (Nat.not_lt_of_ge hwge this).elim
  -- Combine the three coordinate facts into `consistent = true`.
  have h0 := hAt ⟨0, by decide⟩
  have h1 := hAt ⟨1, by decide⟩
  have h2 := hAt ⟨2, by decide⟩
  have h' :
      (consistentAt (maskAt k) (maskAt a) (maskAt d) ⟨0, by decide⟩ = true ∧
          consistentAt (maskAt k) (maskAt a) (maskAt d) ⟨1, by decide⟩ = true) ∧
        consistentAt (maskAt k) (maskAt a) (maskAt d) ⟨2, by decide⟩ = true :=
    ⟨⟨h0, h1⟩, h2⟩
  simpa [consistent] using h'

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev AvailFrom3 := N1000000OrbitCounting.AvailFrom3

private lemma availFor_ge_three {k : DirIdx} (u : BaseOrbit k) (x : AvailFor u) : 3 ≤ x.1.1 := by
  have hx : x.1 ∉ baseSet := by
    intro hxMem
    exact x.2 (by simp [hxMem])
  exact ge_three_of_not_mem_baseSet (x := x.1) hx

private theorem rowMatch_maskAt_inj (d : DirIdx) {i₁ i₂ j : Fin 3} :
    rowMatch (maskAt d) i₁ = some j → rowMatch (maskAt d) i₂ = some j → i₁ = i₂ := by
  intro h1 h2
  fin_cases d <;> fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j <;> cases h1 <;> cases h2 <;> rfl

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def encodeInter {k : DirIdx} (u : BaseOrbit k) (a d : DirIdx) (w : Inter u a d) :
    FreeCoord a d ↪ AvailFor u := by
  classical
  refine ⟨fun j => ?_, ?_⟩
  · refine ⟨w.1.1 j.1, ?_⟩
    have hbase : dirMask baseVertex w.1 = maskAt a := w.2.1
    have hrel : dirMask w.1 u.1 = maskAt d := w.2.2
    have hwge : 3 ≤ (w.1.1 j.1).1 :=
      baseOrbit_freeCoord_outside (u := ⟨w.1, hbase⟩) ⟨j.1, j.2.1⟩
    have hnotBase : w.1.1 j.1 ∉ baseSet := not_mem_baseSet_of_ge_three (x := w.1.1 j.1) hwge
    have hneAll :
        ∀ t : Fin 3, w.1.1 j.1 ≠ u.1.1 t :=
      ne_of_dirMask_rowMatch_none (u := w.1) (v := u.1) (d := d) (h := hrel) (i := j.1) j.2.2
    have hnotFree : w.1.1 j.1 ∉ freeSyms (k := k) u := by
      intro hmem
      rcases Finset.mem_image.1 hmem with ⟨jf, _hjfUniv, hjf⟩
      exact (hneAll jf.1) (by simp [hjf])
    -- Combine both exclusions.
    simp [Finset.mem_union, hnotBase, hnotFree]
  · intro j₁ j₂ hEq
    apply Subtype.ext
    -- Equality in `AvailFor u` implies equality in `SymN`.
    have hVal : w.1.1 j₁.1 = w.1.1 j₂.1 := by
      simpa using congrArg Subtype.val hEq
    exact w.1.2 hVal

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def gOfEmbeddingVal {k : DirIdx} (u : BaseOrbit k) (a d : DirIdx)
    (hcons : consistent (maskAt k) (maskAt a) (maskAt d) = true)
    (e : FreeCoord a d ↪ AvailFor u) : FreeCol a → AvailFrom3 :=
  fun j => by
    classical
    refine dite (rowMatch (maskAt d) j.1 = none) (fun hnone => ?_) (fun hne => ?_)
    · let x : AvailFor u := e ⟨j.1, ⟨j.2, hnone⟩⟩
      exact ⟨x.1, availFor_ge_three (u := u) x⟩
    · let l : Fin 3 := Classical.choose ((Option.ne_none_iff_exists').1 hne)
      have hl : rowMatch (maskAt d) j.1 = some l :=
        Classical.choose_spec ((Option.ne_none_iff_exists').1 hne)
      have hAt : consistentAt (maskAt k) (maskAt a) (maskAt d) j.1 = true :=
        consistentAt_of_consistent (k := k) (a := a) (d := d) hcons j.1
      have hkFree : colMatch (maskAt k) l = none := by
        have : decide (colMatch (maskAt k) l = none) = true := by
          simpa [consistentAt, j.2, hl] using hAt
        exact of_decide_eq_true this
      exact ⟨u.1.1 l, baseOrbit_freeCoord_outside (u := u) ⟨l, hkFree⟩⟩

theorem gOfEmbeddingVal_val_of_rowMatch_some {k : DirIdx} (u : BaseOrbit k) (a d : DirIdx)
    (hcons : consistent (maskAt k) (maskAt a) (maskAt d) = true)
    (e : FreeCoord a d ↪ AvailFor u) (j : FreeCol a) (l : Fin 3)
    (hrow : rowMatch (maskAt d) j.1 = some l) :
    (gOfEmbeddingVal (u := u) (a := a) (d := d) hcons e j).1 = u.1.1 l := by
  classical
  have hne : rowMatch (maskAt d) j.1 ≠ none := by
    intro hEq
    have h0 := hrow
    simp [hEq] at h0
  have hspec : rowMatch (maskAt d) j.1 =
      some (Classical.choose ((Option.ne_none_iff_exists').1 hne)) :=
    Classical.choose_spec ((Option.ne_none_iff_exists').1 hne)
  have hchoose : Classical.choose ((Option.ne_none_iff_exists').1 hne) = l := by
    have : some (Classical.choose ((Option.ne_none_iff_exists').1 hne)) = some l :=
      hspec.symm.trans hrow
    cases this
    rfl
  dsimp [gOfEmbeddingVal]
  rw [dif_neg hne]
  -- Only the first component matters; avoid simplifying proof fields.
  simp [hchoose]

theorem gOfEmbeddingVal_val_of_rowMatch_none {k : DirIdx} (u : BaseOrbit k) (a d : DirIdx)
    (hcons : consistent (maskAt k) (maskAt a) (maskAt d) = true)
    (e : FreeCoord a d ↪ AvailFor u) (j : FreeCol a)
    (hrow : rowMatch (maskAt d) j.1 = none) :
    (gOfEmbeddingVal (u := u) (a := a) (d := d) hcons e j).1 =
      (e ⟨j.1, ⟨j.2, hrow⟩⟩).1 := by
  classical
  dsimp [gOfEmbeddingVal]
  rw [dif_pos hrow]

private theorem gOfEmbeddingVal_injective {k : DirIdx} (u : BaseOrbit k) (a d : DirIdx)
    (hcons : consistent (maskAt k) (maskAt a) (maskAt d) = true)
    (e : FreeCoord a d ↪ AvailFor u) :
    Function.Injective (gOfEmbeddingVal (u := u) (a := a) (d := d) hcons e) := by
  classical
  intro j₁ j₂ hj
  have hjVal :
      (gOfEmbeddingVal (u := u) (a := a) (d := d) hcons e j₁).1 =
        (gOfEmbeddingVal (u := u) (a := a) (d := d) hcons e j₂).1 :=
    congrArg Subtype.val hj
  cases hrow₁ : rowMatch (maskAt d) j₁.1 <;> cases hrow₂ : rowMatch (maskAt d) j₂.1
  · have h₁ :=
      gOfEmbeddingVal_val_of_rowMatch_none (u := u) (a := a) (d := d)
        (hcons := hcons) (e := e) (j := j₁) hrow₁
    have h₂ :=
      gOfEmbeddingVal_val_of_rowMatch_none (u := u) (a := a) (d := d)
        (hcons := hcons) (e := e) (j := j₂) hrow₂
    have he :
        e ⟨j₁.1, ⟨j₁.2, hrow₁⟩⟩ = e ⟨j₂.1, ⟨j₂.2, hrow₂⟩⟩ := by
      apply Subtype.ext
      simpa [h₁, h₂] using hjVal
    have harg :
        (⟨j₁.1, ⟨j₁.2, hrow₁⟩⟩ : FreeCoord a d) = ⟨j₂.1, ⟨j₂.2, hrow₂⟩⟩ :=
      e.injective he
    exact Subtype.ext (by simpa using congrArg (fun x : FreeCoord a d => x.1) harg)
  · rename_i l
    exfalso
    have h₁ :=
      gOfEmbeddingVal_val_of_rowMatch_none (u := u) (a := a) (d := d)
        (hcons := hcons) (e := e) (j := j₁) hrow₁
    have h₂ :=
      gOfEmbeddingVal_val_of_rowMatch_some (u := u) (a := a) (d := d)
        (hcons := hcons) (e := e) (j := j₂) (l := l) hrow₂
    have : (e ⟨j₁.1, ⟨j₁.2, hrow₁⟩⟩).1 = u.1.1 l := by
      simpa [h₁, h₂] using hjVal
    exact (availFor_ne_u_coord (k := k) u (e ⟨j₁.1, ⟨j₁.2, hrow₁⟩⟩) l) this
  · rename_i l
    exfalso
    have h₁ :=
      gOfEmbeddingVal_val_of_rowMatch_some (u := u) (a := a) (d := d)
        (hcons := hcons) (e := e) (j := j₁) (l := l) hrow₁
    have h₂ :=
      gOfEmbeddingVal_val_of_rowMatch_none (u := u) (a := a) (d := d)
        (hcons := hcons) (e := e) (j := j₂) hrow₂
    have : (e ⟨j₂.1, ⟨j₂.2, hrow₂⟩⟩).1 = u.1.1 l := by
      simpa [h₁, h₂, eq_comm] using hjVal
    exact (availFor_ne_u_coord (k := k) u (e ⟨j₂.1, ⟨j₂.2, hrow₂⟩⟩) l) this
  · rename_i l₁ l₂
    have h₁ :=
      gOfEmbeddingVal_val_of_rowMatch_some (u := u) (a := a) (d := d)
        (hcons := hcons) (e := e) (j := j₁) (l := l₁) hrow₁
    have h₂ :=
      gOfEmbeddingVal_val_of_rowMatch_some (u := u) (a := a) (d := d)
        (hcons := hcons) (e := e) (j := j₂) (l := l₂) hrow₂
    have hul : u.1.1 l₁ = u.1.1 l₂ := by simpa [h₁, h₂] using hjVal
    have hl : l₁ = l₂ := u.1.2 hul
    have hrow₂' : rowMatch (maskAt d) j₂.1 = some l₁ := by simpa [hl] using hrow₂
    exact
      Subtype.ext
        (rowMatch_maskAt_inj (d := d) (i₁ := j₁.1) (i₂ := j₂.1) (j := l₁) hrow₁ hrow₂')

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def gOfEmbedding {k : DirIdx} (u : BaseOrbit k) (a d : DirIdx)
    (hcons : consistent (maskAt k) (maskAt a) (maskAt d) = true)
    (e : FreeCoord a d ↪ AvailFor u) : FreeCol a ↪ AvailFrom3 :=
  ⟨gOfEmbeddingVal (u := u) (a := a) (d := d) hcons e,
    gOfEmbeddingVal_injective (u := u) (a := a) (d := d) hcons e⟩

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def decodeInter {k : DirIdx} (u : BaseOrbit k) (a d : DirIdx)
    (hcons : consistent (maskAt k) (maskAt a) (maskAt d) = true)
    (e : FreeCoord a d ↪ AvailFor u) : Inter u a d := by
  classical
  let g : FreeCol a ↪ AvailFrom3 := gOfEmbedding (u := u) (a := a) (d := d) hcons e
  let v : V := decodeVertex (k := a) g
  have hvBase : dirMask baseVertex v = maskAt a := decodeVertex_mask (k := a) g
  have hDecide :
      ∀ i j : Fin 3, decide (v.1 i = u.1.1 j) = decide (rowMatch (maskAt d) i = some j) := by
    intro i j
    classical
    cases hrow : rowMatch (maskAt d) i with
    | some l =>
        have hvEq : v.1 i = u.1.1 l := by
          cases hcol : colMatch (maskAt a) i with
          | none =>
              have hv0 : v.1 i = (g ⟨i, hcol⟩).1 := by
                simpa [v, decodeVertex] using
                  (decodeTuple_of_colMatch_none (k := a) (g := g) (j := i) hcol)
              have hg0 : (g ⟨i, hcol⟩).1 = u.1.1 l := by
                have :=
                  gOfEmbeddingVal_val_of_rowMatch_some (u := u) (a := a) (d := d)
                    (hcons := hcons) (e := e)
                    (j := (⟨i, hcol⟩ : FreeCol a)) (l := l) (by simpa using hrow)
                simpa [g, gOfEmbedding] using this
              simp [hv0, hg0]
          | some ib =>
              have hv0 : v.1 i = baseVertex.1 ib := by
                simpa [v, decodeVertex] using
                  (decodeTuple_of_colMatch_some (k := a) (g := g) (j := i) (i := ib) hcol)
              have hAti : consistentAt (maskAt k) (maskAt a) (maskAt d) i = true :=
                consistentAt_of_consistent (k := k) (a := a) (d := d) hcons i
              have hk : rowMatch (maskAt k) ib = some l := by
                have : decide (rowMatch (maskAt k) ib = some l) = true := by
                  simpa [consistentAt, hcol, hrow] using hAti
                exact of_decide_eq_true this
              have hubase : baseVertex.1 ib = u.1.1 l :=
                eq_of_dirMask_rowMatch (u := baseVertex) (v := u.1) (d := k)
                  (h := u.2) (i := ib) (j := l) hk
              simp [hv0, hubase]
        by_cases hj : j = l
        · subst hj
          simp [hvEq]
        · have hne : v.1 i ≠ u.1.1 j := by
            intro hEq
            have : u.1.1 l = u.1.1 j := by
              calc
                u.1.1 l = v.1 i := by simp [hvEq]
                _ = u.1.1 j := hEq
            have : l = j := u.1.2 this
            exact hj this.symm
          have hj' : l ≠ j := by simpa [eq_comm] using hj
          simp [hj', hne]
    | none =>
        have hneAll : ∀ j' : Fin 3, v.1 i ≠ u.1.1 j' := by
          intro j'
          cases hcol : colMatch (maskAt a) i with
          | none =>
              have hv0 : v.1 i = (g ⟨i, hcol⟩).1 := by
                simpa [v, decodeVertex] using
                  (decodeTuple_of_colMatch_none (k := a) (g := g) (j := i) hcol)
              have hg0 :
                  (g ⟨i, hcol⟩).1 = (e ⟨i, ⟨hcol, hrow⟩⟩).1 := by
                have :=
                  gOfEmbeddingVal_val_of_rowMatch_none (u := u) (a := a) (d := d)
                    (hcons := hcons) (e := e)
                    (j := (⟨i, hcol⟩ : FreeCol a)) (by simpa using hrow)
                simpa [g, gOfEmbedding] using this
              intro hEq
              have : (e ⟨i, ⟨hcol, hrow⟩⟩).1 = u.1.1 j' := by simpa [hv0, hg0] using hEq
              exact (availFor_ne_u_coord (k := k) u (e ⟨i, ⟨hcol, hrow⟩⟩) j') this
          | some ib =>
              have hv0 : v.1 i = baseVertex.1 ib := by
                simpa [v, decodeVertex] using
                  (decodeTuple_of_colMatch_some (k := a) (g := g) (j := i) (i := ib) hcol)
              have hAti : consistentAt (maskAt k) (maskAt a) (maskAt d) i = true :=
                consistentAt_of_consistent (k := k) (a := a) (d := d) hcons i
              have hkNone : rowMatch (maskAt k) ib = none := by
                have : decide (rowMatch (maskAt k) ib = none) = true := by
                  simpa [consistentAt, hcol, hrow] using hAti
                exact of_decide_eq_true this
              have hne :=
                ne_of_dirMask_rowMatch_none (u := baseVertex) (v := u.1) (d := k)
                  (h := u.2) (i := ib) hkNone j'
              simpa [hv0, eq_comm] using hne
        have : decide (v.1 i = u.1.1 j) = false := (decide_eq_false_iff_not).2 (hneAll j)
        simp [this]
  have hvRel : dirMask v u.1 = maskAt d := by
    classical
    apply Nat.eq_of_testBit_eq
    intro t
    by_cases ht : t < 9
    · let iNat : Nat := t / 3
      let jNat : Nat := t % 3
      have hi : iNat < 3 := by
        have : t < 3 * 3 := by simpa using ht
        simpa [iNat] using (Nat.div_lt_of_lt_mul this)
      have hj : jNat < 3 := by
        have : 0 < 3 := by decide
        simpa [jNat] using Nat.mod_lt t this
      let i : Fin 3 := ⟨iNat, hi⟩
      let j : Fin 3 := ⟨jNat, hj⟩
      have htDecomp : i.1 * 3 + j.1 = t := by
        simpa [iNat, jNat, Nat.mul_comm] using (Nat.div_add_mod t 3)
      have hL :
          (dirMask v u.1).testBit (i.1 * 3 + j.1) = decide (v.1 i = u.1.1 j) := by
        exact dirMask_testBit (u := v) (v := u.1) (i := i) (j := j)
      have hR :
          (maskAt d).testBit (i.1 * 3 + j.1) = decide (rowMatch (maskAt d) i = some j) := by
        simpa using (maskAt_testBit_eq_decide_rowMatch (d := d) (i := i) (j := j))
      -- Prove `decide (v_i = u_j)` matches `rowMatch`.
      have hDec :
          decide (v.1 i = u.1.1 j) = decide (rowMatch (maskAt d) i = some j) :=
        hDecide i j
      calc
        Nat.testBit (dirMask v u.1) t
            = Nat.testBit (dirMask v u.1) (i.1 * 3 + j.1) := by simp [htDecomp]
        _ = decide (v.1 i = u.1.1 j) := by simp [hL]
        _ = decide (rowMatch (maskAt d) i = some j) := hDec
        _ = Nat.testBit (maskAt d) (i.1 * 3 + j.1) := by simp [hR]
        _ = Nat.testBit (maskAt d) t := by simp [htDecomp]
    · -- `t ≥ 9`: both sides are `< 2^9`.
      have h9t : 9 ≤ t := Nat.le_of_not_gt ht
      have hPow : (2 : Nat) ^ 9 ≤ (2 : Nat) ^ t :=
        Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) h9t
      have hLtL : dirMask v u.1 < (2 : Nat) ^ 9 := by
        simpa [Nat.shiftLeft_eq] using (dirMask_lt (u := v) (v := u.1))
      have hLtR : maskAt d < (2 : Nat) ^ 9 := by
        simpa [Nat.shiftLeft_eq] using (maskAt_lt_512 (d := d))
      have hLtL' : dirMask v u.1 < (2 : Nat) ^ t := lt_of_lt_of_le hLtL hPow
      have hLtR' : maskAt d < (2 : Nat) ^ t := lt_of_lt_of_le hLtR hPow
      simp [Nat.testBit_eq_false_of_lt hLtL', Nat.testBit_eq_false_of_lt hLtR']
  exact ⟨v, ⟨hvBase, hvRel⟩⟩

theorem encode_decodeInter {k : DirIdx} (u : BaseOrbit k) (a d : DirIdx)
    (hcons : consistent (maskAt k) (maskAt a) (maskAt d) = true)
    (e : FreeCoord a d ↪ AvailFor u) :
    encodeInter (u := u) (a := a) (d := d)
      (decodeInter (u := u) (a := a) (d := d) hcons e) = e := by
  classical
  apply Function.Embedding.ext
  intro j
  apply Subtype.ext
  have hjcol : colMatch (maskAt a) j.1 = none := j.2.1
  have hjrow : rowMatch (maskAt d) j.1 = none := j.2.2
  -- Reduce to the decoded vertex coordinate, then use the explicit evaluation lemma for
  -- `gOfEmbeddingVal`.
  simp only [encodeInter]
  calc
    (decodeInter (u := u) (a := a) (d := d) hcons e).1.1 j.1
        = (N1000000OrbitCounting.decodeVertex (k := a)
              (gOfEmbedding (u := u) (a := a) (d := d) hcons e)).1 j.1 := by
            simp [decodeInter]
    _ = (gOfEmbedding (u := u) (a := a) (d := d) hcons e ⟨j.1, hjcol⟩).1 := by
          simpa [N1000000OrbitCounting.decodeVertex] using
            (decodeTuple_of_colMatch_none (k := a)
              (g := gOfEmbedding (u := u) (a := a) (d := d) hcons e) (j := j.1) hjcol)
    _ = (e j).1 := by
          have h0 :
              (gOfEmbeddingVal (u := u) (a := a) (d := d) hcons e ⟨j.1, hjcol⟩).1 =
                (e ⟨j.1, ⟨hjcol, hjrow⟩⟩).1 :=
            gOfEmbeddingVal_val_of_rowMatch_none (u := u) (a := a) (d := d) (hcons := hcons)
              (e := e) (j := (⟨j.1, hjcol⟩ : FreeCol a)) hjrow
          have h0' :
              (gOfEmbedding (u := u) (a := a) (d := d) hcons e ⟨j.1, hjcol⟩).1 =
                (e ⟨j.1, ⟨hjcol, hjrow⟩⟩).1 := by
            simpa [gOfEmbedding] using h0
          have hjEq : (⟨j.1, ⟨hjcol, hjrow⟩⟩ : FreeCoord a d) = j := by
            apply Subtype.ext
            rfl
          simpa [hjEq] using h0'

theorem decode_encodeInter {k : DirIdx} (u : BaseOrbit k) (a d : DirIdx)
    (hcons : consistent (maskAt k) (maskAt a) (maskAt d) = true)
    (w : Inter u a d) :
    decodeInter (u := u) (a := a) (d := d) hcons
      (encodeInter (u := u) (a := a) (d := d) w) = w := by
  classical
  -- Two elements of `Inter` are equal if their underlying vertices are equal.
  apply Subtype.ext
  apply Subtype.ext
  funext j
  -- Split on whether `j` is a free column of `a`.
  by_cases hcol : colMatch (maskAt a) j = none
  · -- free column: evaluate via `decodeTuple_of_colMatch_none` and expand `gOfEmbedding`
    have hv0 :
        (decodeInter (u := u) (a := a) (d := d) hcons
          (encodeInter (u := u) (a := a) (d := d) w)).1.1 j =
          (gOfEmbedding (u := u) (a := a) (d := d) hcons
            (encodeInter (u := u) (a := a) (d := d) w) ⟨j,
            hcol⟩).1 := by
      -- Unfold `decodeInter`/`decodeVertex` and evaluate the decoded tuple at a free column.
      simp [decodeInter, N1000000OrbitCounting.decodeVertex, decodeTuple_of_colMatch_none, hcol]
    -- Now split on `rowMatch d j`.
    cases hrow : rowMatch (maskAt d) j with
    | some l =>
        have hwul : w.1.1 j = u.1.1 l :=
          eq_of_dirMask_rowMatch (u := w.1) (v := u.1) (d := d) (h := w.2.2) (i := j) (j := l) hrow
        -- In this branch, `gOfEmbedding` is forced to `u_l`.
        have hg : (gOfEmbedding (u := u) (a := a) (d := d) hcons
          (encodeInter (u := u) (a := a) (d := d) w) ⟨j,
          hcol⟩).1 =
            u.1.1 l := by
          simpa [gOfEmbedding] using
            (gOfEmbeddingVal_val_of_rowMatch_some (u := u) (a := a) (d := d) (hcons := hcons)
              (e := encodeInter (u := u) (a := a) (d := d) w) (j := (⟨j, hcol⟩ : FreeCol a))
              (l := l) hrow)
        simp [hv0, hg, hwul]
    | none =>
        -- In this branch, `gOfEmbedding` uses the encoded value, which is `w_j`.
        have hg : (gOfEmbedding (u := u) (a := a) (d := d) hcons
          (encodeInter (u := u) (a := a) (d := d) w) ⟨j,
          hcol⟩).1 =
            (encodeInter (u := u) (a := a) (d := d) w ⟨j, ⟨hcol, hrow⟩⟩).1 := by
          simpa [gOfEmbedding] using
            (gOfEmbeddingVal_val_of_rowMatch_none (u := u) (a := a) (d := d) (hcons := hcons)
              (e := encodeInter (u := u) (a := a) (d := d) w) (j := (⟨j, hcol⟩ : FreeCol a)) hrow)
        calc
          (decodeInter (u := u) (a := a) (d := d) hcons
            (encodeInter (u := u) (a := a) (d := d) w)).1.1 j
              = (gOfEmbedding (u := u) (a := a) (d := d) hcons
                    (encodeInter (u := u) (a := a) (d := d) w) ⟨j, hcol⟩).1 := hv0
          _ = (encodeInter (u := u) (a := a) (d := d) w ⟨j, ⟨hcol, hrow⟩⟩).1 := by
                simpa using hg
          _ = w.1.1 j := by
                simp [encodeInter]
  · -- fixed column: evaluate via `decodeTuple_of_colMatch_some` and use
    -- `base_eq_of_colMatch` for `w`.
    rcases (Option.ne_none_iff_exists').1 hcol with ⟨i, hi⟩
    have hv0 :
        (decodeInter (u := u) (a := a) (d := d) hcons
          (encodeInter (u := u) (a := a) (d := d) w)).1.1 j =
          baseVertex.1 i := by
      -- Unfold `decodeInter`/`decodeVertex` and evaluate the decoded tuple at a fixed column.
      simp [decodeInter, N1000000OrbitCounting.decodeVertex, decodeTuple_of_colMatch_some, hi]
    have hw0 : w.1.1 j = baseVertex.1 i := by
      -- `w` lies in the base orbit `a`.
      exact base_eq_of_colMatch (k := a) (u := ⟨w.1, w.2.1⟩) (j := j) (i := i) (h := hi)
    simp [hv0, hw0]

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def interEquivEmbedding {k : DirIdx} (u : BaseOrbit k) (a d : DirIdx)
    (hcons : consistent (maskAt k) (maskAt a) (maskAt d) = true) :
    Inter u a d ≃ (FreeCoord a d ↪ AvailFor u) where
  toFun := encodeInter (u := u) (a := a) (d := d)
  invFun := decodeInter (u := u) (a := a) (d := d) hcons
  left_inv := decode_encodeInter (u := u) (a := a) (d := d) hcons
  right_inv := encode_decodeInter (u := u) (a := a) (d := d) hcons

theorem card_inter_eq_N {k : DirIdx} (u : BaseOrbit k) (a d : DirIdx) :
    Fintype.card (Inter u a d) = N k a d := by
  classical
  by_cases hcons : consistent (maskAt k) (maskAt a) (maskAt d) = true
  · have hcard : Fintype.card (Inter u a d) = Fintype.card (FreeCoord a d ↪ AvailFor u) :=
        Fintype.card_congr (interEquivEmbedding (u := u) (a := a) (d := d) hcons)
    simpa [N, hcons, card_embedding_freeCoord_availFor (u := u)] using hcard
  · -- In the inconsistent case, `Inter u a d` is empty.
    have hempty : IsEmpty (Inter u a d) := by
      classical
      refine ⟨?_⟩
      intro w
      have : consistent (maskAt k) (maskAt a) (maskAt d) = true :=
        consistent_of_inter (k := k) u a d w
      exact (hcons this).elim
    have hcard : Fintype.card (Inter u a d) = 0 := by
      classical
      haveI : IsEmpty (Inter u a d) := hempty
      exact (Fintype.card_eq_zero : Fintype.card (Inter u a d) = 0)
    simp [N, hcons]

end N1000000IntersectionCounting

end Distributed2Coloring.LowerBound
