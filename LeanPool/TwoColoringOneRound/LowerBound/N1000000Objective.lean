/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.GroupTheory.GroupAction.Quotient

import LeanPool.TwoColoringOneRound.LowerBound.Correlation
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Relaxation
import LeanPool.TwoColoringOneRound.LowerBound.N1000000WeakDuality

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000Objective
-/

namespace Distributed2Coloring.LowerBound

namespace N1000000Objective

open scoped BigOperators

open Distributed2Coloring.LowerBound.Correlation
open Distributed2Coloring.LowerBound.N1000000Data
open Distributed2Coloring.LowerBound.N1000000Relaxation
open Distributed2Coloring.LowerBound.N1000000WeakDuality

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev n : Nat := N1000000Data.n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Q := ℚ
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev G := Correlation.G n

noncomputable instance : Fintype G := by infer_instance

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Emb4 := Fin 4 ↪ Sym n

noncomputable instance : Fintype Emb4 := by infer_instance

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def edgeOfEmb (x : Emb4) : Edge n :=
  ⟨x, x.injective⟩

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def embOfEdge (e : Edge n) : Emb4 :=
  ⟨e.1, e.2⟩

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def edgeEquivEmb : Edge n ≃ Emb4 where
  toFun := embOfEdge
  invFun := edgeOfEmb
  left_inv := by
    intro e
    exact Subtype.ext rfl
  right_inv := by
    intro x
    ext i
    rfl

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def corrEdge (f : Coloring n) (e : Edge n) : Q :=
  corr f (Edge.src e) (Edge.dst e)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def corrEmb (f : Coloring n) (x : Emb4) : Q :=
  corrEdge f (edgeOfEmb x)

private lemma sum_corrEdge_eq_sum_corrEmb (f : Coloring n) :
    (∑ e : Edge n, corrEdge f e) = ∑ x : Emb4, corrEmb f x := by
  classical
  -- `Fintype.sum_equiv` changes variables along `edgeEquivEmb`.
  simpa [corrEmb] using
    (Fintype.sum_equiv edgeEquivEmb (fun e : Edge n => corrEdge f e) (fun x : Emb4 => corrEmb f x)
      (by intro e; rfl))

private lemma edge_src_smul (σ : G) (e : Edge n) :
    Edge.src (σ • e) = σ • Edge.src e := Subtype.ext rfl

private lemma edge_dst_smul (σ : G) (e : Edge n) :
    Edge.dst (σ • e) = σ • Edge.dst e := Subtype.ext rfl

private lemma corrEdge_smul (f : Coloring n) (σ : G) (e : Edge n) :
    corrEdge f (σ • e) = corr f (σ • Edge.src e) (σ • Edge.dst e) := by
  simp [corrEdge, edge_src_smul, edge_dst_smul]

private lemma corr_eq_sign (f : Coloring n) (u v : Vertex n) :
    corr f u v = ((signOfColoring f u : Int) : Q) * ((signOfColoring f v : Int) : Q) := by
  cases hU : f u <;> cases hV : f v <;>
    simp [Correlation.corr, Correlation.spin, signOfColoring, hU, hV]

private lemma edgeCorrSum_cast_eq_sum_corrEdge (f : Coloring n) :
    (edgeCorrSum f : Q) = ∑ e : Edge n, corrEdge f e := by
  classical
  unfold edgeCorrSum
  -- Cast the integer sum into `ℚ` using the ring hom.
  have hcast :
      ((∑ e : Edge n,
            signOfColoring f (Edge.src e) * signOfColoring f (Edge.dst e) : Int) : Q)
        =
        ∑ e : Edge n,
          ((signOfColoring f (Edge.src e) : Int) : Q) *
            ((signOfColoring f (Edge.dst e) : Int) : Q) := by
    change
        (Int.castRingHom Q)
            (∑ e : Edge n,
              signOfColoring f (Edge.src e) * signOfColoring f (Edge.dst e) : Int)
          =
          ∑ e : Edge n,
            ((signOfColoring f (Edge.src e) : Int) : Q) *
              ((signOfColoring f (Edge.dst e) : Int) : Q)
    simp [map_sum]
  -- Rewrite the RHS summand as `corrEdge`.
  -- (The order `src/dst` matches; `corr` is commutative anyway.)
  simp [corrEdge, corr_eq_sign, hcast]

private lemma edgeCorrelation_eq_avg_corrEdge (f : Coloring n) :
    edgeCorrelation f = (∑ e : Edge n, corrEdge f e) / (edgeCount n : Q) := by
  classical
  have hnum : (edgeCorrSum f : Q) = ∑ e : Edge n, corrEdge f e :=
    edgeCorrSum_cast_eq_sum_corrEdge (f := f)
  unfold edgeCorrelation
  -- Rewrite the numerator using `hnum`.
  exact congrArg (fun z : Q => z / (edgeCount n : Q)) hnum

private lemma orbitProdStabilizerEquivGroup_smul_fst
    (b : Emb4) (x : ↑(MulAction.orbit G b)) (h : MulAction.stabilizer G b) :
    (MulAction.orbitProdStabilizerEquivGroup G b (x, h)) • b = x := by
  classical
  -- Expand the definition: `orbitProdStabilizerEquivGroup` is
  -- `groupEquivQuotientProdSubgroup.symm ((orbitEquivQuotientStabilizer x), h)`.
  change
      ((Subgroup.groupEquivQuotientProdSubgroup (s := MulAction.stabilizer G b)).symm
            ((MulAction.orbitEquivQuotientStabilizer G b) x, h)) • b =
        x
  set g :=
    (Subgroup.groupEquivQuotientProdSubgroup (s := MulAction.stabilizer G b)).symm
      ((MulAction.orbitEquivQuotientStabilizer G b) x, h) with hg
  -- Show `QuotientGroup.mk g = (orbitEquivQuotientStabilizer G b) x`.
  have hgpair :
      Subgroup.groupEquivQuotientProdSubgroup (s := MulAction.stabilizer G b) g
        = ((MulAction.orbitEquivQuotientStabilizer G b) x, h) := by
    simp [g]
  have hfst :
      (Subgroup.groupEquivQuotientProdSubgroup (s := MulAction.stabilizer G b) g).1
        = (MulAction.orbitEquivQuotientStabilizer G b) x := congrArg Prod.fst hgpair
  have hmk : QuotientGroup.mk g = (MulAction.orbitEquivQuotientStabilizer G b) x := by
    -- The first projection of `groupEquivQuotientProdSubgroup` is `QuotientGroup.mk`.
    simpa [Subgroup.groupEquivQuotientProdSubgroup] using hfst
  -- Convert to the orbit element via `orbitEquivQuotientStabilizer`.
  have hx_orbit : (MulAction.orbitEquivQuotientStabilizer G b).symm (QuotientGroup.mk g) = x := by
    have hx := (MulAction.orbitEquivQuotientStabilizer G b).left_inv x
    rwa [hmk]
  have hx_val :
      ((MulAction.orbitEquivQuotientStabilizer G b).symm (QuotientGroup.mk g) : Emb4) = x := by
    exact congrArg Subtype.val hx_orbit
  -- Evaluate the orbit element as `g • b`.
  have hx_smul :
      ((MulAction.orbitEquivQuotientStabilizer G b).symm g : Emb4) = g • b := by
    exact MulAction.orbitEquivQuotientStabilizer_symm_apply (α := G) (b := b) g
  -- Put everything together.
  simpa [hg, g] using (hx_smul.trans hx_val)

private lemma avg_corrEmb_eq_avg_over_all_embeddings (f : Coloring n) (b : Emb4) :
    (∑ σ : G, corrEmb f (σ • b)) / (Fintype.card G : Q)
      = (∑ x : Emb4, corrEmb f x) / (Fintype.card Emb4 : Q) := by
  classical
  haveI : Nonempty Emb4 := ⟨b⟩
  -- The action on `Emb4` is pretransitive, so the orbit of `b` is all of `Emb4`.
  letI : MulAction.IsMultiplyPretransitive G (Sym n) 4 :=
    Equiv.Perm.isMultiplyPretransitive (α := Sym n) 4
  have hpre : MulAction.orbit G b = (Set.univ : Set Emb4) := by
    simpa using (MulAction.orbit_eq_univ (M := G) (a := b))
  letI : Fintype (↑(MulAction.orbit G b)) := Fintype.ofFinite _
  have hbmem : ∀ x : Emb4, x ∈ MulAction.orbit G b := by
    intro x
    simp [hpre]
  let hOrbitEquiv : (↑(MulAction.orbit G b)) ≃ Emb4 :=
    Equiv.subtypeUnivEquiv hbmem
  have hsumOrbit :
      (∑ x : ↑(MulAction.orbit G b), corrEmb f x.1) = ∑ x : Emb4, corrEmb f x := by
    simpa using
      (Fintype.sum_equiv hOrbitEquiv (fun x : ↑(MulAction.orbit G b) => corrEmb f x.1)
        (fun x : Emb4 => corrEmb f x) (by intro x; rfl))
  have hcardOrbit : Fintype.card (↑(MulAction.orbit G b)) = Fintype.card Emb4 :=
    Fintype.card_congr hOrbitEquiv
  -- Sum over the group is `|stab|` times the sum over the orbit.
  let e := MulAction.orbitProdStabilizerEquivGroup G b
  have hsumG :
      (∑ σ : G, corrEmb f (σ • b))
        =
        (Fintype.card (MulAction.stabilizer G b) : Q) *
          (∑ x : ↑(MulAction.orbit G b), corrEmb f x.1) := by
    classical
    calc
      (∑ σ : G, corrEmb f (σ • b))
          =
          ∑ p : (↑(MulAction.orbit G b)) × MulAction.stabilizer G b, corrEmb f ((e p) • b) := by
            simpa using
              (Fintype.sum_equiv e
                    (fun p => corrEmb f ((e p) • b))
                    (fun σ => corrEmb f (σ • b))
                    (by intro p; rfl)).symm
      _ =
          ∑ p : (↑(MulAction.orbit G b)) × MulAction.stabilizer G b, corrEmb f p.1 := by
            refine Fintype.sum_congr _ _ ?_
            rintro ⟨x, h⟩
            simp [e, orbitProdStabilizerEquivGroup_smul_fst (b := b) (x := x) (h := h)]
      _ =
          ∑ x : ↑(MulAction.orbit G b), ∑ _h : MulAction.stabilizer G b, corrEmb f x.1 := by
            simp [Fintype.sum_prod_type]
      _ =
          ∑ x : ↑(MulAction.orbit G b),
            (Fintype.card (MulAction.stabilizer G b) : Q) * corrEmb f x.1 := by
            refine Fintype.sum_congr _ _ ?_
            intro x
            simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ =
          (Fintype.card (MulAction.stabilizer G b) : Q) *
            ∑ x : ↑(MulAction.orbit G b), corrEmb f x.1 := by
            -- Pull out the constant using `Finset.mul_sum`.
            simpa using
              (Finset.mul_sum
                    (s := (Finset.univ : Finset (↑(MulAction.orbit G b))))
                    (f := fun x : ↑(MulAction.orbit G b) => corrEmb f x.1)
                    (a := (Fintype.card (MulAction.stabilizer G b) : Q))).symm
  have hcardNat :
      Fintype.card (↑(MulAction.orbit G b)) * Fintype.card (MulAction.stabilizer G b) =
        Fintype.card G := by
    simpa using
      (MulAction.card_orbit_mul_card_stabilizer_eq_card_group (α := G) (β := Emb4) b)
  have hcardG :
      (Fintype.card G : Q) =
        (Fintype.card Emb4 : Q) * (Fintype.card (MulAction.stabilizer G b) : Q) := by
    have :
        Fintype.card Emb4 * Fintype.card (MulAction.stabilizer G b) = Fintype.card G := by
      simpa [hcardOrbit] using hcardNat
    exact_mod_cast this.symm
  have hcardEmb4_ne : (Fintype.card Emb4 : Q) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card Emb4))
  have hcardStab_ne : (Fintype.card (MulAction.stabilizer G b) : Q) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card (MulAction.stabilizer G b)))
  -- Finish by cancelling the stabilizer cardinality.
  calc
    (∑ σ : G, corrEmb f (σ • b)) / (Fintype.card G : Q)
        =
        ((Fintype.card (MulAction.stabilizer G b) : Q) * (∑ x : Emb4, corrEmb f x)) /
          ((Fintype.card Emb4 : Q) * (Fintype.card (MulAction.stabilizer G b) : Q)) := by
          rw [hsumG, hsumOrbit, hcardG]
    _ = (∑ x : Emb4, corrEmb f x) / (Fintype.card Emb4 : Q) := by
          field_simp [hcardEmb4_ne, hcardStab_ne, mul_assoc, mul_left_comm, mul_comm]

private lemma avg_corrEmb_eq_avg_corrEdge (f : Coloring n) :
    (∑ x : Emb4, corrEmb f x) / (Fintype.card Emb4 : Q)
      = (∑ e : Edge n, corrEdge f e) / (edgeCount n : Q) := by
  classical
  have hsum : (∑ x : Emb4, corrEmb f x) = ∑ e : Edge n, corrEdge f e := by
    simp [sum_corrEdge_eq_sum_corrEmb (f := f)]
  have hcard : (Fintype.card Emb4 : Q) = (edgeCount n : Q) := by
    have : Fintype.card Emb4 = edgeCount n := by
      simpa [edgeCount] using (Fintype.card_congr edgeEquivEmb.symm)
    exact_mod_cast this
  calc
    (∑ x : Emb4, corrEmb f x) / (Fintype.card Emb4 : Q)
        = (∑ e : Edge n, corrEdge f e) / (Fintype.card Emb4 : Q) := by rw [hsum]
    _ = (∑ e : Edge n, corrEdge f e) / (edgeCount n : Q) := by rw [hcard]

theorem xEdge_xFromColoring_eq_edgeCorrelation (f : Coloring n) :
    xEdge (xFromColoring f) = edgeCorrelation f := by
  classical
  -- Replace `xEdge` by the orbit variable at `edgeVar`.
  have hxEdge :
      xEdge (xFromColoring f) =
        corrAvg f (varRepVertexU edgeVarVar) (varRepVertexV edgeVarVar) := by
    rfl
  -- Replace the representative vertices by `edgeRep`.
  have hsrc : Edge.src edgeRep = varRepVertexV edgeVarVar := edgeRep_src
  have hdst : Edge.dst edgeRep = varRepVertexU edgeVarVar := edgeRep_dst
  have hxEdge' :
      xEdge (xFromColoring f) = corrAvg f (Edge.src edgeRep) (Edge.dst edgeRep) := by
    -- `xFromColoring` uses `(U,V)` but `edgeRep` stores `(src,dst)` in the other order.
    have h0 :
        corrAvg f (varRepVertexU edgeVarVar) (varRepVertexV edgeVarVar)
          = corrAvg f (Edge.dst edgeRep) (Edge.src edgeRep) := by
      simp [hsrc, hdst]
    have h1 :
        corrAvg f (Edge.dst edgeRep) (Edge.src edgeRep)
          = corrAvg f (Edge.src edgeRep) (Edge.dst edgeRep) := by
      simpa using (corrAvg_comm (f := f) (u := Edge.dst edgeRep) (v := Edge.src edgeRep))
    simpa [hxEdge] using h0.trans h1
  -- Express the `corrAvg` as a group average, then convert it to an edge average.
  let b : Emb4 := ⟨edgeRep.1, edgeRep.2⟩
  have hb : edgeOfEmb b = edgeRep := by exact Subtype.ext rfl
  have hAvgGroup :
      corrAvg f (Edge.src edgeRep) (Edge.dst edgeRep)
        = (∑ σ : G, corrEmb f (σ • b)) / (Fintype.card G : Q) := by
    classical
    unfold corrAvg
    have hnum :
        (∑ σ : G, corr f (σ • Edge.src edgeRep) (σ • Edge.dst edgeRep))
          = ∑ σ : G, corrEmb f (σ • b) := by
      classical
      refine Finset.sum_congr rfl ?_
      intro σ _hσ
      have h1 : edgeOfEmb (σ • b) = σ • edgeRep := by exact Subtype.ext rfl
      calc
        corr f (σ • Edge.src edgeRep) (σ • Edge.dst edgeRep)
            = corrEdge f (σ • edgeRep) := by
                simpa using (corrEdge_smul (f := f) (σ := σ) (e := edgeRep)).symm
        _ = corrEmb f (σ • b) := by simp [corrEmb, h1]
    -- Rewrite the numerator using `hnum`.
    simp [hnum]
  have hAvgAll :
      corrAvg f (Edge.src edgeRep) (Edge.dst edgeRep)
        = (∑ e : Edge n, corrEdge f e) / (edgeCount n : Q) := by
    -- First, average over the group becomes average over all embeddings (pretransitivity),
    -- then over all edges using `edgeEquivEmb`.
    calc
      corrAvg f (Edge.src edgeRep) (Edge.dst edgeRep)
          = (∑ σ : G, corrEmb f (σ • b)) / (Fintype.card G : Q) := hAvgGroup
      _ = (∑ x : Emb4, corrEmb f x) / (Fintype.card Emb4 : Q) :=
            avg_corrEmb_eq_avg_over_all_embeddings (f := f) (b := b)
      _ = (∑ e : Edge n, corrEdge f e) / (edgeCount n : Q) := avg_corrEmb_eq_avg_corrEdge (f := f)
  have hedgeCorr :
      edgeCorrelation f = (∑ e : Edge n, corrEdge f e) / (edgeCount n : Q) :=
    edgeCorrelation_eq_avg_corrEdge (f := f)
  -- Finish.
  calc
    xEdge (xFromColoring f)
        = corrAvg f (Edge.src edgeRep) (Edge.dst edgeRep) := hxEdge'
    _ = (∑ e : Edge n, corrEdge f e) / (edgeCount n : Q) := hAvgAll
    _ = edgeCorrelation f := hedgeCorr.symm
end N1000000Objective

end Distributed2Coloring.LowerBound
