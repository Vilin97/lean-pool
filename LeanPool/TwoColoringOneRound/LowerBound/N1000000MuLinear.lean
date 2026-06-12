/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Polyrith
import Mathlib.Data.List.GetD
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

import LeanPool.TwoColoringOneRound.LowerBound.Correlation
import LeanPool.TwoColoringOneRound.LowerBound.N1000000MuWitness
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Relaxation
import LeanPool.TwoColoringOneRound.LowerBound.N1000000WeakDuality

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000MuLinear
-/

namespace Distributed2Coloring.LowerBound

namespace N1000000MuLinear

open scoped BigOperators

open Distributed2Coloring.LowerBound.Correlation
open Distributed2Coloring.LowerBound.N1000000Data
open Distributed2Coloring.LowerBound.N1000000MuWitness
open Distributed2Coloring.LowerBound.N1000000Relaxation
open Distributed2Coloring.LowerBound.N1000000WeakDuality

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev n : Nat := N1000000Data.n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Q := ℚ
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev G := Correlation.G n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Var := N1000000WeakDuality.Var
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Mu := N1000000WeakDuality.Mu

noncomputable instance : Fintype G := by infer_instance

instance : NeZero numVars := ⟨by decide⟩

instance : Inhabited PairMapData :=
  ⟨{ swap := false
    , srcU := (0, 0, 0)
    , srcV := (0, 0, 0)
    , tgtU := (0, 0, 0)
    , tgtV := (0, 0, 0)
    , srcSyms := []
    , tgtSyms := []
    , idxV := (0, 0, 0) }⟩

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def vertexOfLabels (t : N1000000MuWitness.LabelTriple) : Vertex n :=
  if h : LabelsDistinct t ∧ LabelsInRange t then
    ⟨tupleOfLabels t, tupleOfLabels_injective_of_labelsDistinct t h.1 h.2⟩
  else
    -- Unused in this development: all label triples coming from the generated witnesses
    -- satisfy `LabelsDistinct ∧ LabelsInRange`.
    varRepVertexU ⟨0, by decide⟩

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def PairMapOk (i : Var) (pm : PairMapData) : Prop :=
  pm.srcU = varRepUAt i ∧
    pm.srcV = varRepVAt i ∧
      pm.srcSyms.length = pm.tgtSyms.length ∧
        pm.srcSyms.Nodup ∧
          pm.tgtSyms.Nodup ∧
            pm.srcSyms.Forall (fun x => x < n) ∧
              pm.tgtSyms.Forall (fun x => x < n) ∧
                LabelsDistinct pm.tgtU ∧ LabelsInRange pm.tgtU ∧
                  LabelsDistinct pm.tgtV ∧ LabelsInRange pm.tgtV ∧
            2 < pm.srcSyms.length ∧
              pm.idxV.1 < pm.srcSyms.length ∧
                pm.idxV.2.1 < pm.srcSyms.length ∧
                  pm.idxV.2.2 < pm.srcSyms.length ∧
                    pm.srcSyms.getD 0 0 = pm.srcU.1 ∧
                      pm.srcSyms.getD 1 0 = pm.srcU.2.1 ∧
                        pm.srcSyms.getD 2 0 = pm.srcU.2.2 ∧
                          pm.tgtSyms.getD 0 0 = pm.tgtU.1 ∧
                            pm.tgtSyms.getD 1 0 = pm.tgtU.2.1 ∧
                              pm.tgtSyms.getD 2 0 = pm.tgtU.2.2 ∧
                                pm.srcSyms.getD pm.idxV.1 0 = pm.srcV.1 ∧
                                  pm.srcSyms.getD pm.idxV.2.1 0 = pm.srcV.2.1 ∧
                                    pm.srcSyms.getD pm.idxV.2.2 0 = pm.srcV.2.2 ∧
                                      pm.tgtSyms.getD pm.idxV.1 0 = pm.tgtV.1 ∧
                                        pm.tgtSyms.getD pm.idxV.2.1 0 = pm.tgtV.2.1 ∧
                                        pm.tgtSyms.getD pm.idxV.2.2 0 = pm.tgtV.2.2

instance (i : Var) (pm : PairMapData) : Decidable (PairMapOk i pm) := by
  unfold PairMapOk
  infer_instance

private theorem corrAvg_tgt_eq_xFromColoring
    (f : Coloring n) (i : Var) (pm : PairMapData) (hok : PairMapOk i pm) :
    corrAvg f (vertexOfLabels pm.tgtU) (vertexOfLabels pm.tgtV) = xFromColoring f i := by
  classical
  rcases hok with
    ⟨hsrcU, hsrcV, hlen, hndSrc, hndTgt, hsrcLt, htgtLt, htgtUd, htgtUr, htgtVd, htgtVr,
      h2lt, hidx0, hidx1, hidx2,
      hsrcU0,
        hsrcU1,
        hsrcU2,
        htgtU0,
        htgtU1,
        htgtU2,
        hsrcV0,
        hsrcV1,
        hsrcV2,
        htgtV0,
        htgtV1,
        htgtV2⟩
  let t : Nat := pm.srcSyms.length
  have htgtLen : pm.tgtSyms.length = t := by simpa [t] using hlen.symm
  have hsrcLtMem : ∀ x ∈ pm.srcSyms, x < n := (List.forall_iff_forall_mem).1 hsrcLt
  have htgtLtMem : ∀ x ∈ pm.tgtSyms, x < n := (List.forall_iff_forall_mem).1 htgtLt
  have hsSrcU : LabelsDistinct pm.srcU ∧ LabelsInRange pm.srcU := by
    constructor
    · simpa [hsrcU] using (varRepUAt_labelsDistinct (i := i))
    · simpa [hsrcU] using (varRepUAt_labelsInRange (i := i))
  have hsSrcV : LabelsDistinct pm.srcV ∧ LabelsInRange pm.srcV := by
    constructor
    · simpa [hsrcV] using (varRepVAt_labelsDistinct (i := i))
    · simpa [hsrcV] using (varRepVAt_labelsInRange (i := i))
  have hsTgtU : LabelsDistinct pm.tgtU ∧ LabelsInRange pm.tgtU := ⟨htgtUd, htgtUr⟩
  have hsTgtV : LabelsDistinct pm.tgtV ∧ LabelsInRange pm.tgtV := ⟨htgtVd, htgtVr⟩
  -- Embeddings enumerating the distinct symbols used by the pair.
  have hinjSrc : Function.Injective pm.srcSyms.get := (List.nodup_iff_injective_get).1 hndSrc
  have hinjTgt : Function.Injective pm.tgtSyms.get := (List.nodup_iff_injective_get).1 hndTgt
  let srcEmb : Fin t ↪ Sym n :=
    ⟨fun j => symOfNat (pm.srcSyms.get ⟨j.1, by simp [t]⟩), by
      intro a b hab
      apply Fin.ext
      let aIdx : Fin pm.srcSyms.length := ⟨a.1, by simp [t]⟩
      let bIdx : Fin pm.srcSyms.length := ⟨b.1, by simp [t]⟩
      have haLt : pm.srcSyms.get aIdx < n := hsrcLtMem _ (List.get_mem _ _)
      have hbLt : pm.srcSyms.get bIdx < n := hsrcLtMem _ (List.get_mem _ _)
      have hGet : pm.srcSyms.get aIdx = pm.srcSyms.get bIdx :=
        symOfNat_injective_of_lt haLt hbLt (by simpa [aIdx, bIdx] using hab)
      have hIdx : aIdx = bIdx := hinjSrc hGet
      simpa [aIdx, bIdx] using congrArg Fin.val hIdx⟩
  let tgtEmb : Fin t ↪ Sym n :=
    ⟨fun j => symOfNat (pm.tgtSyms.get ⟨j.1, by
        have : j.1 < pm.srcSyms.length := by simp [t]
        exact lt_of_lt_of_eq this hlen⟩), by
      intro a b hab
      apply Fin.ext
      let aIdx : Fin pm.tgtSyms.length := ⟨a.1, by
        have : a.1 < pm.srcSyms.length := by simp [t]
        exact lt_of_lt_of_eq this hlen⟩
      let bIdx : Fin pm.tgtSyms.length := ⟨b.1, by
        have : b.1 < pm.srcSyms.length := by simp [t]
        exact lt_of_lt_of_eq this hlen⟩
      have haLt : pm.tgtSyms.get aIdx < n := htgtLtMem _ (List.get_mem _ _)
      have hbLt : pm.tgtSyms.get bIdx < n := htgtLtMem _ (List.get_mem _ _)
      have hGet : pm.tgtSyms.get aIdx = pm.tgtSyms.get bIdx :=
        symOfNat_injective_of_lt haLt hbLt (by simpa [aIdx, bIdx] using hab)
      have hIdx : aIdx = bIdx := hinjTgt hGet
      simpa [aIdx, bIdx] using congrArg Fin.val hIdx⟩
  -- A permutation sending `srcEmb` to `tgtEmb`.
  letI : MulAction.IsMultiplyPretransitive G (Sym n) t :=
    Equiv.Perm.isMultiplyPretransitive (α := Sym n) t
  letI : MulAction.IsPretransitive G (Fin t ↪ Sym n) := by infer_instance
  rcases
    (MulAction.IsPretransitive.exists_smul_eq (M := G) (α := Fin t ↪ Sym n)
      srcEmb tgtEmb)
    with ⟨σ, hσ⟩
  have hσ_apply : ∀ j : Fin t, σ (srcEmb j) = tgtEmb j := by
    intro j
    have := congrArg (fun e : Fin t ↪ Sym n => e j) hσ
    simpa [Function.Embedding.smul_apply, Equiv.Perm.smul_def, srcEmb, tgtEmb] using this
  -- Convenient indices.
  have ht2 : 2 < t := by simpa [t] using h2lt
  have h0 : (0 : Nat) < t := Nat.lt_trans (by decide : (0 : Nat) < 2) ht2
  have h1 : (1 : Nat) < t := Nat.lt_trans (by decide : (1 : Nat) < 2) ht2
  have h2 : (2 : Nat) < t := ht2
  -- A compact helper: turn `hσ_apply` into a statement about `getD`.
  have hσ_getD (k : Nat) (hk : k < t) :
      σ (symOfNat (pm.srcSyms.getD k 0)) = symOfNat (pm.tgtSyms.getD k 0) := by
    have hkSrc : k < pm.srcSyms.length := by simpa [t] using hk
    have hkTgt : k < pm.tgtSyms.length := by simpa [htgtLen] using hk
    have hj :
        σ (symOfNat (pm.srcSyms.get ⟨k, hkSrc⟩)) = symOfNat (pm.tgtSyms.get ⟨k, hkTgt⟩) := by
      simpa [srcEmb, tgtEmb] using hσ_apply ⟨k, hk⟩
    have hsrc : pm.srcSyms.getD k 0 = pm.srcSyms.get ⟨k, hkSrc⟩ := by
      simpa using (List.getD_eq_get pm.srcSyms 0 ⟨k, hkSrc⟩)
    have htgt : pm.tgtSyms.getD k 0 = pm.tgtSyms.get ⟨k, hkTgt⟩ := by
      simpa using (List.getD_eq_get pm.tgtSyms 0 ⟨k, hkTgt⟩)
    rw [hsrc, htgt]
    exact hj
  -- Rewrite the `getD` identities in the bracketed `get?` form used by the simplifications below.
  have hsrcU0' : pm.srcSyms[0]?.getD 0 = pm.srcU.1 := by simpa using hsrcU0
  have hsrcU1' : pm.srcSyms[1]?.getD 0 = pm.srcU.2.1 := by simpa using hsrcU1
  have hsrcU2' : pm.srcSyms[2]?.getD 0 = pm.srcU.2.2 := by simpa using hsrcU2
  have htgtU0' : pm.tgtSyms[0]?.getD 0 = pm.tgtU.1 := by simpa using htgtU0
  have htgtU1' : pm.tgtSyms[1]?.getD 0 = pm.tgtU.2.1 := by simpa using htgtU1
  have htgtU2' : pm.tgtSyms[2]?.getD 0 = pm.tgtU.2.2 := by simpa using htgtU2
  have hsrcV0' : pm.srcSyms[pm.idxV.1]?.getD 0 = pm.srcV.1 := by simpa using hsrcV0
  have hsrcV1' : pm.srcSyms[pm.idxV.2.1]?.getD 0 = pm.srcV.2.1 := by simpa using hsrcV1
  have hsrcV2' : pm.srcSyms[pm.idxV.2.2]?.getD 0 = pm.srcV.2.2 := by simpa using hsrcV2
  have htgtV0' : pm.tgtSyms[pm.idxV.1]?.getD 0 = pm.tgtV.1 := by simpa using htgtV0
  have htgtV1' : pm.tgtSyms[pm.idxV.2.1]?.getD 0 = pm.tgtV.2.1 := by simpa using htgtV1
  have htgtV2' : pm.tgtSyms[pm.idxV.2.2]?.getD 0 = pm.tgtV.2.2 := by simpa using htgtV2
  -- Show `σ` maps the representative pair to the target pair.
  have hU : σ • vertexOfLabels pm.srcU = vertexOfLabels pm.tgtU := by
    apply Subtype.ext
    funext j
    fin_cases j
    · have h := hσ_getD 0 h0
      simpa [vertexOfLabels, hsSrcU, hsTgtU, tupleOfLabels, labelGet, hsrcU0', htgtU0'] using h
    · have h := hσ_getD 1 h1
      simpa [vertexOfLabels, hsSrcU, hsTgtU, tupleOfLabels, labelGet, hsrcU1', htgtU1'] using h
    · have h := hσ_getD 2 h2
      simpa [vertexOfLabels, hsSrcU, hsTgtU, tupleOfLabels, labelGet, hsrcU2', htgtU2'] using h
  have hV : σ • vertexOfLabels pm.srcV = vertexOfLabels pm.tgtV := by
    apply Subtype.ext
    funext j
    fin_cases j
    · have hk : pm.idxV.1 < t := by simpa [t] using hidx0
      have h := hσ_getD pm.idxV.1 hk
      simpa [vertexOfLabels, hsSrcV, hsTgtV, tupleOfLabels, labelGet, hsrcV0', htgtV0'] using h
    · have hk : pm.idxV.2.1 < t := by simpa [t] using hidx1
      have h := hσ_getD pm.idxV.2.1 hk
      simpa [vertexOfLabels, hsSrcV, hsTgtV, tupleOfLabels, labelGet, hsrcV1', htgtV1'] using h
    · have hk : pm.idxV.2.2 < t := by simpa [t] using hidx2
      have h := hσ_getD pm.idxV.2.2 hk
      simpa [vertexOfLabels, hsSrcV, hsTgtV, tupleOfLabels, labelGet, hsrcV2', htgtV2'] using h
  -- Transport correlation averages.
  have hInv :=
    corrAvg_smul (n := n) (f := f) (τ := σ) (u := vertexOfLabels pm.srcU)
      (v := vertexOfLabels pm.srcV)
  -- rewrite the mapped vertices and relate the source pair to `xFromColoring`.
  have hSrcEq :
      corrAvg f (vertexOfLabels pm.srcU) (vertexOfLabels pm.srcV) = xFromColoring f i := by
    -- Replace `(pm.srcU,pm.srcV)` by the canonical representatives for variable `i`.
    have hUrep : vertexOfLabels pm.srcU = varRepVertexU i := by
      have hvL :
          vertexOfLabels pm.srcU =
            ⟨tupleOfLabels pm.srcU,
              tupleOfLabels_injective_of_labelsDistinct _ hsSrcU.1 hsSrcU.2⟩ := by
        simp [vertexOfLabels, hsSrcU]
      have hvR :
          varRepVertexU i =
            ⟨tupleOfLabels pm.srcU,
              tupleOfLabels_injective_of_labelsDistinct _ hsSrcU.1 hsSrcU.2⟩ := by
        apply Subtype.ext
        simp [varRepVertexU, hsrcU.symm]
      exact hvL.trans hvR.symm
    have hVrep : vertexOfLabels pm.srcV = varRepVertexV i := by
      have hvL :
          vertexOfLabels pm.srcV =
            ⟨tupleOfLabels pm.srcV,
              tupleOfLabels_injective_of_labelsDistinct _ hsSrcV.1 hsSrcV.2⟩ := by
        simp [vertexOfLabels, hsSrcV]
      have hvR :
          varRepVertexV i =
            ⟨tupleOfLabels pm.srcV,
              tupleOfLabels_injective_of_labelsDistinct _ hsSrcV.1 hsSrcV.2⟩ := by
        apply Subtype.ext
        simp [varRepVertexV, hsrcV.symm]
      exact hvL.trans hvR.symm
    simp [xFromColoring, hUrep, hVrep]
  -- Finish: `corrAvg` is invariant under simultaneous action.
  -- `hInv` has the form `corrAvg f (σ•u) (σ•v) = corrAvg f u v`.
  -- Rewrite `(σ•u,σ•v)` using `hU/hV`, then use `hSrcEq`.
  simpa [hU, hV] using hInv.trans hSrcEq

private lemma xFromColoring_le_one (f : Coloring n) (i : Var) :
    xFromColoring f i ≤ (1 : Q) := by
  simpa [xFromColoring] using
    (corrAvg_le_one (f := f) (u := varRepVertexU i) (v := varRepVertexV i))

private lemma neg_one_le_xFromColoring (f : Coloring n) (i : Var) :
    (-1 : Q) ≤ xFromColoring f i := by
  simpa [xFromColoring] using
    (neg_one_le_corrAvg (f := f) (u := varRepVertexU i) (v := varRepVertexV i))

private def boxVar (k : Mu) : Var :=
  Fin.ofNat numVars (muBoxVar[k.1]!)

private def boxCoeff (k : Mu) : Q :=
  (muBoxCoeff[k.1]! : Q)

private lemma aCoeff_eq_boxCoeff (k : Mu) (hk : muBoxCoeff[k.1]! ≠ 0) (i : Var) :
    aCoeff k i = if i = boxVar k then boxCoeff k else 0 := by
  classical
  fin_cases k <;> fin_cases i <;> (try cases hk rfl) <;>
    decide

private lemma aDot_eq_box (f : Coloring n) (k : Mu) (hk : muBoxCoeff[k.1]! ≠ 0) :
    aDot k (xFromColoring f) = boxCoeff k * xFromColoring f (boxVar k) := by
  classical
  unfold aDot
  have hCoeff : ∀ i : Var, aCoeff k i = if i = boxVar k then boxCoeff k else 0 := by
    intro i
    simpa using aCoeff_eq_boxCoeff (k := k) (hk := hk) (i := i)
  calc
    (∑ i : Var, aCoeff k i * xFromColoring f i) =
        ∑ i : Var, (if i = boxVar k then boxCoeff k else 0) * xFromColoring f i := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          simp [hCoeff i]
    _ = ∑ i : Var, if i = boxVar k then (boxCoeff k * xFromColoring f i) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          by_cases h : i = boxVar k <;> simp [h]
    _ = boxCoeff k * xFromColoring f (boxVar k) := by
          exact
            (Fintype.sum_ite_eq' (ι := Var) (M := Q) (i := boxVar k)
              (f := fun j => boxCoeff k * xFromColoring f j))

private lemma muBoxCoeff_eq_one_or_eq_neg_one (k : Mu) (hk : muBoxCoeff[k.1]! ≠ 0) :
    muBoxCoeff[k.1]! = 1 ∨ muBoxCoeff[k.1]! = -1 := by
  fin_cases k <;> (try cases hk rfl) <;> decide

private lemma box_case (f : Coloring n) (k : Mu) (hk : muBoxCoeff[k.1]! ≠ 0) :
    aDot k (xFromColoring f) ≤ (1 : Q) := by
  have haDot := aDot_eq_box (f := f) (k := k) hk
  have hx_le : xFromColoring f (boxVar k) ≤ (1 : Q) := xFromColoring_le_one (f := f) (i := boxVar k)
  have hx_ge : (-1 : Q) ≤ xFromColoring f (boxVar k) :=
    neg_one_le_xFromColoring (f := f) (i := boxVar k)
  have hsign := muBoxCoeff_eq_one_or_eq_neg_one (k := k) hk
  rcases hsign with hpos | hneg
  · -- coefficient `+1`
    have : boxCoeff k = (1 : Q) := by simpa [boxCoeff] using congrArg (fun z : Int => (z : Q)) hpos
    simpa [haDot, this, one_mul] using hx_le
  · -- coefficient `-1`
    have : boxCoeff k = (-1 : Q) := by simpa [boxCoeff] using congrArg (fun z : Int => (z : Q)) hneg
    have hx : (-xFromColoring f (boxVar k)) ≤ (1 : Q) := by linarith [hx_ge]
    simpa [haDot, this] using hx

private def cuv (k : Mu) : Q :=
  match muTriForm[k.1]! with
  | 0 => (-1 : Q)
  | 1 => (1 : Q)
  | 2 => (1 : Q)
  | 3 => (-1 : Q)
  | _ => 0

private def cuw (k : Mu) : Q :=
  match muTriForm[k.1]! with
  | 0 => (-1 : Q)
  | 1 => (1 : Q)
  | 2 => (-1 : Q)
  | 3 => (1 : Q)
  | _ => 0

private def cvw (k : Mu) : Q :=
  match muTriForm[k.1]! with
  | 0 => (-1 : Q)
  | 1 => (-1 : Q)
  | 2 => (1 : Q)
  | 3 => (1 : Q)
  | _ => 0

private def uvVar (k : Mu) : Var :=
  Fin.ofNat numVars (muTriVars[k.1]!).1

private def uwVar (k : Mu) : Var :=
  Fin.ofNat numVars (muTriVars[k.1]!).2.1

private def vwVar (k : Mu) : Var :=
  Fin.ofNat numVars (muTriVars[k.1]!).2.2

private def triCoeff (k : Mu) (i : Var) : Q :=
  (if i = uvVar k then cuv k else 0) +
    (if i = uwVar k then cuw k else 0) +
      (if i = vwVar k then cvw k else 0)

private lemma muBoxCoeff_eq_zero_iff (k : Mu) :
    muBoxCoeff[k.1]! = 0 ↔ k.1 = 23 ∨ k.1 = 24 ∨ k.1 = 25 ∨ k.1 = 26 := by
  fin_cases k <;> decide

private lemma aVec_23 :
    N1000000WeakDuality.aVec (⟨23, by decide⟩ : Mu) =
      #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 1] := by
  simp [N1000000WeakDuality.aVec, N1000000Data.muSupport]

private lemma aVec_24 :
    N1000000WeakDuality.aVec (⟨24, by decide⟩ : Mu) =
      #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by
  simp [N1000000WeakDuality.aVec, N1000000Data.muSupport]

private lemma aVec_25 :
    N1000000WeakDuality.aVec (⟨25, by decide⟩ : Mu) =
      #[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] := by
  simp [N1000000WeakDuality.aVec, N1000000Data.muSupport]

private lemma aVec_26 :
    N1000000WeakDuality.aVec (⟨26, by decide⟩ : Mu) =
      #[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0] := by
  simp [N1000000WeakDuality.aVec, N1000000Data.muSupport]

private lemma aCoeff_eq_triCoeff (k : Mu) (hk : muBoxCoeff[k.1]! = 0) (i : Var) :
    aCoeff k i = triCoeff k i := by
  classical
  -- Reduce to the four triangle indices and then verify each finite `Var` case by computation
  -- (after rewriting `k` to a canonical `Fin` term so that no proof fields remain as variables).
  have hkCases : k.1 = 23 ∨ k.1 = 24 ∨ k.1 = 25 ∨ k.1 = 26 := by
    exact (muBoxCoeff_eq_zero_iff (k := k)).1 hk
  rcases hkCases with hk23 | hkRest
  · have hkEq : k = (⟨23, by decide⟩ : Mu) := by
      ext
      exact hk23
    have : aCoeff (⟨23, by decide⟩ : Mu) i = triCoeff (⟨23, by decide⟩ : Mu) i := by
      fin_cases i <;>
        simp (config := { decide := true })
          [N1000000WeakDuality.aCoeff, N1000000WeakDuality.aCoeffInt,
            Distributed2Coloring.LowerBound.N1000000.coeffAt, triCoeff, aVec_23]
    simpa [hkEq] using this
  · rcases hkRest with hk24 | hkRest
    · have hkEq : k = (⟨24, by decide⟩ : Mu) := by
        ext
        exact hk24
      have : aCoeff (⟨24, by decide⟩ : Mu) i = triCoeff (⟨24, by decide⟩ : Mu) i := by
        fin_cases i <;>
          simp (config := { decide := true })
            [N1000000WeakDuality.aCoeff, N1000000WeakDuality.aCoeffInt,
              Distributed2Coloring.LowerBound.N1000000.coeffAt, triCoeff, aVec_24]
      simpa [hkEq] using this
    · rcases hkRest with hk25 | hk26
      · have hkEq : k = (⟨25, by decide⟩ : Mu) := by
          ext
          exact hk25
        have : aCoeff (⟨25, by decide⟩ : Mu) i = triCoeff (⟨25, by decide⟩ : Mu) i := by
          fin_cases i <;>
            simp (config := { decide := true })
              [N1000000WeakDuality.aCoeff, N1000000WeakDuality.aCoeffInt,
                Distributed2Coloring.LowerBound.N1000000.coeffAt, triCoeff, aVec_25]
        simpa [hkEq] using this
      · have hkEq : k = (⟨26, by decide⟩ : Mu) := by
          ext
          exact hk26
        have : aCoeff (⟨26, by decide⟩ : Mu) i = triCoeff (⟨26, by decide⟩ : Mu) i := by
          fin_cases i <;>
            simp (config := { decide := true })
              [N1000000WeakDuality.aCoeff, N1000000WeakDuality.aCoeffInt,
                Distributed2Coloring.LowerBound.N1000000.coeffAt, triCoeff, aVec_26]
        simpa [hkEq] using this

private lemma aDot_eq_triLinear (f : Coloring n) (k : Mu) (hk : muBoxCoeff[k.1]! = 0) :
    aDot k (xFromColoring f) =
      cuv k * xFromColoring f (uvVar k) +
        cuw k * xFromColoring f (uwVar k) +
          cvw k * xFromColoring f (vwVar k) := by
  classical
  unfold aDot
  have hCoeff : ∀ i : Var, aCoeff k i = triCoeff k i := by
    intro i
    simpa using aCoeff_eq_triCoeff (k := k) (hk := hk) (i := i)
  -- Expand the coefficient function and evaluate the three indicator sums.
  have hsumUV :
      (∑ i : Var, if i = uvVar k then cuv k * xFromColoring f i else 0) =
        cuv k * xFromColoring f (uvVar k) := by
    simp
  have hsumUW :
      (∑ i : Var, if i = uwVar k then cuw k * xFromColoring f i else 0) =
        cuw k * xFromColoring f (uwVar k) := by
    simp
  have hsumVW :
      (∑ i : Var, if i = vwVar k then cvw k * xFromColoring f i else 0) =
        cvw k * xFromColoring f (vwVar k) := by
    simp
  have hpoint :
      ∀ i : Var,
        triCoeff k i * xFromColoring f i =
          (if i = uvVar k then cuv k * xFromColoring f i else 0) +
            (if i = uwVar k then cuw k * xFromColoring f i else 0) +
              (if i = vwVar k then cvw k * xFromColoring f i else 0) := by
    intro i
    by_cases huv : i = uvVar k <;> by_cases huw : i = uwVar k <;> by_cases hvw : i = vwVar k <;>
      simp [triCoeff, huv, huw, hvw, add_mul, add_assoc, add_left_comm, add_comm]
  calc
    (∑ i : Var, aCoeff k i * xFromColoring f i) = ∑ i : Var, triCoeff k i * xFromColoring f i := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        simp [hCoeff i]
    _ = ∑ i : Var,
          ((if i = uvVar k then cuv k * xFromColoring f i else 0) +
            (if i = uwVar k then cuw k * xFromColoring f i else 0) +
              (if i = vwVar k then cvw k * xFromColoring f i else 0)) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        simp [hpoint i]
    _ =
        (∑ i : Var, if i = uvVar k then cuv k * xFromColoring f i else 0) +
            (∑ i : Var, if i = uwVar k then cuw k * xFromColoring f i else 0) +
              (∑ i : Var, if i = vwVar k then cvw k * xFromColoring f i else 0) := by
        simp [Finset.sum_add_distrib]
    _ = cuv k * xFromColoring f (uvVar k) +
          cuw k * xFromColoring f (uwVar k) +
            cvw k * xFromColoring f (vwVar k) := by
        simp [hsumUV, hsumUW, hsumVW]

private lemma hokUv_of_hk (k : Mu) (hk : muBoxCoeff[k.1]! = 0) :
    PairMapOk (uvVar k) (muMapUv[k.1]!) := by
  fin_cases k <;> cases hk <;> decide

private lemma hokUw_of_hk (k : Mu) (hk : muBoxCoeff[k.1]! = 0) :
    PairMapOk (uwVar k) (muMapUw[k.1]!) := by
  fin_cases k <;> cases hk <;> decide

private lemma hokVw_of_hk (k : Mu) (hk : muBoxCoeff[k.1]! = 0) :
    PairMapOk (vwVar k) (muMapVw[k.1]!) := by
  fin_cases k <;> cases hk <;> decide

private lemma pmUv_targets_true (k : Mu) (hk : muBoxCoeff[k.1]! = 0)
    (hs : (muMapUv[k.1]!).swap = true) :
    (muMapUv[k.1]!).tgtU = muWitV[k.1]! ∧ (muMapUv[k.1]!).tgtV = muWitU[k.1]! := by
  classical
  rcases (muBoxCoeff_eq_zero_iff (k := k)).1 hk with hk23 | hk24 | hk25 | hk26
  · have h :
        (muMapUv[23]!).swap = true →
          (muMapUv[23]!).tgtU = muWitV[23]! ∧ (muMapUv[23]!).tgtV = muWitU[23]! := by
      decide
    have hs' := hs
    rw [hk23] at hs'
    rw [hk23]
    exact h hs'
  · have h :
        (muMapUv[24]!).swap = true →
          (muMapUv[24]!).tgtU = muWitV[24]! ∧ (muMapUv[24]!).tgtV = muWitU[24]! := by
      decide
    have hs' := hs
    rw [hk24] at hs'
    rw [hk24]
    exact h hs'
  · have h :
        (muMapUv[25]!).swap = true →
          (muMapUv[25]!).tgtU = muWitV[25]! ∧ (muMapUv[25]!).tgtV = muWitU[25]! := by
      decide
    have hs' := hs
    rw [hk25] at hs'
    rw [hk25]
    exact h hs'
  · have h :
        (muMapUv[26]!).swap = true →
          (muMapUv[26]!).tgtU = muWitV[26]! ∧ (muMapUv[26]!).tgtV = muWitU[26]! := by
      decide
    have hs' := hs
    rw [hk26] at hs'
    rw [hk26]
    exact h hs'

private lemma pmUv_targets_false (k : Mu) (hk : muBoxCoeff[k.1]! = 0)
    (hs : (muMapUv[k.1]!).swap = false) :
    (muMapUv[k.1]!).tgtU = muWitU[k.1]! ∧ (muMapUv[k.1]!).tgtV = muWitV[k.1]! := by
  classical
  rcases (muBoxCoeff_eq_zero_iff (k := k)).1 hk with hk23 | hk24 | hk25 | hk26
  · have h :
        (muMapUv[23]!).swap = false →
          (muMapUv[23]!).tgtU = muWitU[23]! ∧ (muMapUv[23]!).tgtV = muWitV[23]! := by
      decide
    have hs' := hs
    rw [hk23] at hs'
    rw [hk23]
    exact h hs'
  · have h :
        (muMapUv[24]!).swap = false →
          (muMapUv[24]!).tgtU = muWitU[24]! ∧ (muMapUv[24]!).tgtV = muWitV[24]! := by
      decide
    have hs' := hs
    rw [hk24] at hs'
    rw [hk24]
    exact h hs'
  · have h :
        (muMapUv[25]!).swap = false →
          (muMapUv[25]!).tgtU = muWitU[25]! ∧ (muMapUv[25]!).tgtV = muWitV[25]! := by
      decide
    have hs' := hs
    rw [hk25] at hs'
    rw [hk25]
    exact h hs'
  · have h :
        (muMapUv[26]!).swap = false →
          (muMapUv[26]!).tgtU = muWitU[26]! ∧ (muMapUv[26]!).tgtV = muWitV[26]! := by
      decide
    have hs' := hs
    rw [hk26] at hs'
    rw [hk26]
    exact h hs'

private lemma pmUw_targets_true (k : Mu) (hk : muBoxCoeff[k.1]! = 0)
    (hs : (muMapUw[k.1]!).swap = true) :
    (muMapUw[k.1]!).tgtU = muWitW[k.1]! ∧ (muMapUw[k.1]!).tgtV = muWitU[k.1]! := by
  classical
  rcases (muBoxCoeff_eq_zero_iff (k := k)).1 hk with hk23 | hk24 | hk25 | hk26
  · have h :
        (muMapUw[23]!).swap = true →
          (muMapUw[23]!).tgtU = muWitW[23]! ∧ (muMapUw[23]!).tgtV = muWitU[23]! := by
      decide
    have hs' := hs
    rw [hk23] at hs'
    rw [hk23]
    exact h hs'
  · have h :
        (muMapUw[24]!).swap = true →
          (muMapUw[24]!).tgtU = muWitW[24]! ∧ (muMapUw[24]!).tgtV = muWitU[24]! := by
      decide
    have hs' := hs
    rw [hk24] at hs'
    rw [hk24]
    exact h hs'
  · have h :
        (muMapUw[25]!).swap = true →
          (muMapUw[25]!).tgtU = muWitW[25]! ∧ (muMapUw[25]!).tgtV = muWitU[25]! := by
      decide
    have hs' := hs
    rw [hk25] at hs'
    rw [hk25]
    exact h hs'
  · have h :
        (muMapUw[26]!).swap = true →
          (muMapUw[26]!).tgtU = muWitW[26]! ∧ (muMapUw[26]!).tgtV = muWitU[26]! := by
      decide
    have hs' := hs
    rw [hk26] at hs'
    rw [hk26]
    exact h hs'

private lemma pmUw_targets_false (k : Mu) (hk : muBoxCoeff[k.1]! = 0)
    (hs : (muMapUw[k.1]!).swap = false) :
    (muMapUw[k.1]!).tgtU = muWitU[k.1]! ∧ (muMapUw[k.1]!).tgtV = muWitW[k.1]! := by
  classical
  rcases (muBoxCoeff_eq_zero_iff (k := k)).1 hk with hk23 | hk24 | hk25 | hk26
  · have h :
        (muMapUw[23]!).swap = false →
          (muMapUw[23]!).tgtU = muWitU[23]! ∧ (muMapUw[23]!).tgtV = muWitW[23]! := by
      decide
    have hs' := hs
    rw [hk23] at hs'
    rw [hk23]
    exact h hs'
  · have h :
        (muMapUw[24]!).swap = false →
          (muMapUw[24]!).tgtU = muWitU[24]! ∧ (muMapUw[24]!).tgtV = muWitW[24]! := by
      decide
    have hs' := hs
    rw [hk24] at hs'
    rw [hk24]
    exact h hs'
  · have h :
        (muMapUw[25]!).swap = false →
          (muMapUw[25]!).tgtU = muWitU[25]! ∧ (muMapUw[25]!).tgtV = muWitW[25]! := by
      decide
    have hs' := hs
    rw [hk25] at hs'
    rw [hk25]
    exact h hs'
  · have h :
        (muMapUw[26]!).swap = false →
          (muMapUw[26]!).tgtU = muWitU[26]! ∧ (muMapUw[26]!).tgtV = muWitW[26]! := by
      decide
    have hs' := hs
    rw [hk26] at hs'
    rw [hk26]
    exact h hs'

private lemma pmVw_targets_true (k : Mu) (hk : muBoxCoeff[k.1]! = 0)
    (hs : (muMapVw[k.1]!).swap = true) :
    (muMapVw[k.1]!).tgtU = muWitW[k.1]! ∧ (muMapVw[k.1]!).tgtV = muWitV[k.1]! := by
  classical
  rcases (muBoxCoeff_eq_zero_iff (k := k)).1 hk with hk23 | hk24 | hk25 | hk26
  · have h :
        (muMapVw[23]!).swap = true →
          (muMapVw[23]!).tgtU = muWitW[23]! ∧ (muMapVw[23]!).tgtV = muWitV[23]! := by
      decide
    have hs' := hs
    rw [hk23] at hs'
    rw [hk23]
    exact h hs'
  · have h :
        (muMapVw[24]!).swap = true →
          (muMapVw[24]!).tgtU = muWitW[24]! ∧ (muMapVw[24]!).tgtV = muWitV[24]! := by
      decide
    have hs' := hs
    rw [hk24] at hs'
    rw [hk24]
    exact h hs'
  · have h :
        (muMapVw[25]!).swap = true →
          (muMapVw[25]!).tgtU = muWitW[25]! ∧ (muMapVw[25]!).tgtV = muWitV[25]! := by
      decide
    have hs' := hs
    rw [hk25] at hs'
    rw [hk25]
    exact h hs'
  · have h :
        (muMapVw[26]!).swap = true →
          (muMapVw[26]!).tgtU = muWitW[26]! ∧ (muMapVw[26]!).tgtV = muWitV[26]! := by
      decide
    have hs' := hs
    rw [hk26] at hs'
    rw [hk26]
    exact h hs'

private lemma pmVw_targets_false (k : Mu) (hk : muBoxCoeff[k.1]! = 0)
    (hs : (muMapVw[k.1]!).swap = false) :
    (muMapVw[k.1]!).tgtU = muWitV[k.1]! ∧ (muMapVw[k.1]!).tgtV = muWitW[k.1]! := by
  classical
  rcases (muBoxCoeff_eq_zero_iff (k := k)).1 hk with hk23 | hk24 | hk25 | hk26
  · have h :
        (muMapVw[23]!).swap = false →
          (muMapVw[23]!).tgtU = muWitV[23]! ∧ (muMapVw[23]!).tgtV = muWitW[23]! := by
      decide
    have hs' := hs
    rw [hk23] at hs'
    rw [hk23]
    exact h hs'
  · have h :
        (muMapVw[24]!).swap = false →
          (muMapVw[24]!).tgtU = muWitV[24]! ∧ (muMapVw[24]!).tgtV = muWitW[24]! := by
      decide
    have hs' := hs
    rw [hk24] at hs'
    rw [hk24]
    exact h hs'
  · have h :
        (muMapVw[25]!).swap = false →
          (muMapVw[25]!).tgtU = muWitV[25]! ∧ (muMapVw[25]!).tgtV = muWitW[25]! := by
      decide
    have hs' := hs
    rw [hk25] at hs'
    rw [hk25]
    exact h hs'
  · have h :
        (muMapVw[26]!).swap = false →
          (muMapVw[26]!).tgtU = muWitV[26]! ∧ (muMapVw[26]!).tgtV = muWitW[26]! := by
      decide
    have hs' := hs
    rw [hk26] at hs'
    rw [hk26]
    exact h hs'

private lemma tri_case (f : Coloring n) (k : Mu) (hk : muBoxCoeff[k.1]! = 0) :
    aDot k (xFromColoring f) ≤ (1 : Q) := by
  classical
  -- unpack witness vertices
  let u : Vertex n := vertexOfLabels (muWitU[k.1]!)
  let v : Vertex n := vertexOfLabels (muWitV[k.1]!)
  let w : Vertex n := vertexOfLabels (muWitW[k.1]!)
  -- pair maps for the three variable-correlations
  let pmUv : PairMapData := muMapUv[k.1]!
  let pmUw : PairMapData := muMapUw[k.1]!
  let pmVw : PairMapData := muMapVw[k.1]!
  have hokUv : PairMapOk (uvVar k) pmUv := by simpa [pmUv] using hokUv_of_hk (k := k) hk
  have hokUw : PairMapOk (uwVar k) pmUw := by simpa [pmUw] using hokUw_of_hk (k := k) hk
  have hokVw : PairMapOk (vwVar k) pmVw := by simpa [pmVw] using hokVw_of_hk (k := k) hk
  have htgtUv :
      corrAvg f (vertexOfLabels pmUv.tgtU) (vertexOfLabels pmUv.tgtV) = xFromColoring f (uvVar k) :=
    corrAvg_tgt_eq_xFromColoring (f := f) (i := uvVar k) (pm := pmUv) hokUv
  have htgtUw :
      corrAvg f (vertexOfLabels pmUw.tgtU) (vertexOfLabels pmUw.tgtV) = xFromColoring f (uwVar k) :=
    corrAvg_tgt_eq_xFromColoring (f := f) (i := uwVar k) (pm := pmUw) hokUw
  have htgtVw :
      corrAvg f (vertexOfLabels pmVw.tgtU) (vertexOfLabels pmVw.tgtV) = xFromColoring f (vwVar k) :=
    corrAvg_tgt_eq_xFromColoring (f := f) (i := vwVar k) (pm := pmVw) hokVw
  -- relate witness-pair correlations to the (possibly swapped) target pair
  have huv : corrAvg f u v = xFromColoring f (uvVar k) := by
    by_cases hs : pmUv.swap
    · have hUV := pmUv_targets_true (k := k) hk (by simpa [pmUv] using hs)
      have hU : pmUv.tgtU = (muWitV[k.1]!) := by simpa [pmUv] using hUV.1
      have hV : pmUv.tgtV = (muWitU[k.1]!) := by simpa [pmUv] using hUV.2
      have hc : corrAvg f u v = corrAvg f v u := by simpa [u, v] using (corrAvg_comm (f := f) u v)
      have htgtUv' : corrAvg f v u = xFromColoring f (uvVar k) := by
        simpa [hU, hV, u, v] using htgtUv
      simpa using hc.trans htgtUv'
    · have hUV := pmUv_targets_false (k := k) hk (by simpa [pmUv] using hs)
      have hU : pmUv.tgtU = (muWitU[k.1]!) := by simpa [pmUv] using hUV.1
      have hV : pmUv.tgtV = (muWitV[k.1]!) := by simpa [pmUv] using hUV.2
      simpa [hs, hU, hV, u, v] using htgtUv
  have huw : corrAvg f u w = xFromColoring f (uwVar k) := by
    by_cases hs : pmUw.swap
    · have hUW := pmUw_targets_true (k := k) hk (by simpa [pmUw] using hs)
      have hU : pmUw.tgtU = (muWitW[k.1]!) := by simpa [pmUw] using hUW.1
      have hV : pmUw.tgtV = (muWitU[k.1]!) := by simpa [pmUw] using hUW.2
      have hc : corrAvg f u w = corrAvg f w u := by simpa [u, w] using (corrAvg_comm (f := f) u w)
      have htgtUw' : corrAvg f w u = xFromColoring f (uwVar k) := by
        simpa [hU, hV, u, w] using htgtUw
      simpa using hc.trans htgtUw'
    · have hUW := pmUw_targets_false (k := k) hk (by simpa [pmUw] using hs)
      have hU : pmUw.tgtU = (muWitU[k.1]!) := by simpa [pmUw] using hUW.1
      have hV : pmUw.tgtV = (muWitW[k.1]!) := by simpa [pmUw] using hUW.2
      simpa [hs, hU, hV, u, w] using htgtUw
  have hvw : corrAvg f v w = xFromColoring f (vwVar k) := by
    by_cases hs : pmVw.swap
    · have hVW := pmVw_targets_true (k := k) hk (by simpa [pmVw] using hs)
      have hU : pmVw.tgtU = (muWitW[k.1]!) := by simpa [pmVw] using hVW.1
      have hV : pmVw.tgtV = (muWitV[k.1]!) := by simpa [pmVw] using hVW.2
      have hc : corrAvg f v w = corrAvg f w v := by simpa [v, w] using (corrAvg_comm (f := f) v w)
      have htgtVw' : corrAvg f w v = xFromColoring f (vwVar k) := by
        simpa [hU, hV, v, w] using htgtVw
      simpa using hc.trans htgtVw'
    · have hVW := pmVw_targets_false (k := k) hk (by simpa [pmVw] using hs)
      have hU : pmVw.tgtU = (muWitV[k.1]!) := by simpa [pmVw] using hVW.1
      have hV : pmVw.tgtV = (muWitW[k.1]!) := by simpa [pmVw] using hVW.2
      simpa [hs, hU, hV, v, w] using htgtVw
  have haDot := aDot_eq_triLinear (f := f) (k := k) hk
  have haDot' :
      aDot k (xFromColoring f) =
        cuv k * corrAvg f u v +
          cuw k * corrAvg f u w +
            cvw k * corrAvg f v w := by
    simp [haDot, huv.symm, huw.symm, hvw.symm]
  rcases corrAvg_triangle (f := f) u v w with ⟨h0, h1, h2, h3⟩
  have hforms :
      muTriForm[k.1]! = 0 ∨ muTriForm[k.1]! = 1 ∨ muTriForm[k.1]! = 2 ∨ muTriForm[k.1]! = 3 := by
    fin_cases k <;> decide
  rcases hforms with hform0 | hform1 | hform2 | hform3
  · have hEq :
        cuv k * corrAvg f u v + cuw k * corrAvg f u w + cvw k * corrAvg f v w =
          -(corrAvg f u v + corrAvg f u w + corrAvg f v w) := by
      (simp [cuv, cuw, cvw, hform0]; ring)
    simpa [haDot', hEq] using h0
  · have hEq :
        cuv k * corrAvg f u v + cuw k * corrAvg f u w + cvw k * corrAvg f v w =
          (corrAvg f u v + corrAvg f u w - corrAvg f v w) := by
      (simp [cuv, cuw, cvw, hform1]; ring)
    simpa [haDot', hEq] using h1
  · have hEq :
        cuv k * corrAvg f u v + cuw k * corrAvg f u w + cvw k * corrAvg f v w =
          (corrAvg f u v - corrAvg f u w + corrAvg f v w) := by
      (simp [cuv, cuw, cvw, hform2]; ring)
    simpa [haDot', hEq] using h2
  · have hEq :
        cuv k * corrAvg f u v + cuw k * corrAvg f u w + cvw k * corrAvg f v w =
          (-corrAvg f u v + corrAvg f u w + corrAvg f v w) := by
      simp [cuv, cuw, cvw, hform3]
    simpa [haDot', hEq] using h3

theorem xFromColoring_muLinear (f : Coloring n) :
    ∀ k : Mu, aDot k (xFromColoring f) ≤ (1 : Q) := by
  classical
  intro k
  by_cases hk : muBoxCoeff[k.1]! = 0
  · exact tri_case (f := f) (k := k) hk
  · exact box_case (f := f) (k := k) hk

end N1000000MuLinear

end Distributed2Coloring.LowerBound
