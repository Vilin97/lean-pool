/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import Mathlib.Tactic

import LeanPool.TwoColoringOneRound.LowerBound.CorrAvgMatrix
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionCompute
import LeanPool.TwoColoringOneRound.LowerBound.N1000000CorrAvgMatrixSymmDecompose
import LeanPool.TwoColoringOneRound.LowerBound.N1000000IntersectionCounting
import LeanPool.TwoColoringOneRound.LowerBound.N1000000MaskComplete
import LeanPool.TwoColoringOneRound.LowerBound.N1000000PairTransitivity
import LeanPool.TwoColoringOneRound.LowerBound.N1000000RelaxationPsdSoundness
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Transitivity
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Witness
import LeanPool.TwoColoringOneRound.LowerBound.N1000000WedderburnData

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionForB

open scoped BigOperators
open scoped Matrix

open Distributed2Coloring.LowerBound.Correlation
open Distributed2Coloring.LowerBound.N1000000BCompressionCompute
open Distributed2Coloring.LowerBound.N1000000CorrAvgMatrixSymmDecompose
open Distributed2Coloring.LowerBound.N1000000IntersectionCounting
open Distributed2Coloring.LowerBound.N1000000MaskComplete
open Distributed2Coloring.LowerBound.N1000000OrbitalBasis
open Distributed2Coloring.LowerBound.N1000000OrbitCounting
open Distributed2Coloring.LowerBound.N1000000PairTransitivity
open Distributed2Coloring.LowerBound.N1000000Relaxation
open Distributed2Coloring.LowerBound.N1000000RelaxationPsdSoundness
open Distributed2Coloring.LowerBound.N1000000StructureConstants
open Distributed2Coloring.LowerBound.N1000000Transitivity
open Distributed2Coloring.LowerBound.N1000000Witness
open Distributed2Coloring.LowerBound.N1000000WedderburnData
open Distributed2Coloring.LowerBound.N1000000WeakDuality

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev n : Nat := N1000000Data.n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Q := ℚ
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev V := Vertex n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Block := N1000000WeakDuality.Block
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Var := N1000000WeakDuality.Var
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev DirIdx := N1000000StructureConstants.DirIdx

noncomputable instance : Fintype (Correlation.G n) := by infer_instance

-- Candidate congruence matrices `B_r`, constant on base orbits.
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def B (r : Block) : Matrix V (Fin 3) Q :=
  fun u j => bVal r j (dirIdxBase u)

private lemma dirIdxBase_eq_of_baseOrbit {k : DirIdx} (u : BaseOrbit k) : dirIdxBase u.1 = k := by
  classical
  have h1 : maskAt (dirIdxBase u.1) = dirMask baseVertex u.1 := maskAt_dirIdxBase (u := u.1)
  have h2 : maskAt (dirIdxBase u.1) = maskAt k := by simpa using h1.trans u.2
  exact maskAt_injective h2

private lemma B_eq_bVal_of_baseOrbit (r : Block) {k : DirIdx} (u : BaseOrbit k) (j : Fin 3) :
    B r u.1 j = bVal r j k := by
  simp [B, dirIdxBase_eq_of_baseOrbit (u := u)]

-- An equivalence `V ≃ Σ k, BaseOrbit k` for reindexing `Fintype` sums.
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def vertexSigmaEquiv : V ≃ Σ k : DirIdx, BaseOrbit k where
  toFun := fun u => ⟨dirIdxBase u, ⟨u, (maskAt_dirIdxBase (u := u)).symm⟩⟩
  invFun := fun s => s.2.1
  left_inv := by
    intro u
    rfl
  right_inv := by
    rintro ⟨k, u⟩
    -- First, identify the index by injectivity of `maskAt`.
    have hk : dirIdxBase u.1 = k := dirIdxBase_eq_of_baseOrbit (u := u)
    -- Reduce to equality in the fiber using proof irrelevance.
    refine Sigma.ext hk ?_
    -- The predicates defining the two subtypes are equivalent by rewriting with `hk`,
    -- so `HEq` reduces to equality of the underlying vertices.
    have hpred :
        ∀ x : V,
          (dirMask baseVertex x = maskAt (dirIdxBase u.1)) ↔ (dirMask baseVertex x = maskAt k) := by
      intro x
      simp [hk]
    -- Use `Subtype.heq_iff_coe_eq` to reduce the `HEq` goal.
    have : (u.1 : V) = u.1 := rfl
    exact (Subtype.heq_iff_coe_eq hpred).2 this

private lemma sum_over_vertices_eq_sum_over_orbits (f : V → Q) :
    (∑ u : V, f u) = ∑ s : Σ k : DirIdx, BaseOrbit k, f s.2.1 := by
  classical
  -- Reindex along `vertexSigmaEquiv`.
  have :=
    (Fintype.sum_equiv vertexSigmaEquiv (fun u => f u) (fun s => f s.2.1) (by
      intro u
      rfl))
  simpa using this

-- The intersection fiber `Inter u a d` is the same as the `a`-orbit with the additional
-- constraint `dirMask v u = maskAt d`.
private noncomputable def interEquivBaseOrbit {k : DirIdx} (u : BaseOrbit k) (a d : DirIdx) :
    Inter u a d ≃ { v : BaseOrbit a // dirMask v.1 u.1 = maskAt d } where
  toFun := fun w => ⟨⟨w.1, w.2.1⟩, w.2.2⟩
  invFun := fun w => ⟨w.1.1, ⟨w.1.2, w.2⟩⟩
  left_inv := by
    intro w
    rfl
  right_inv := by
    intro w
    rfl

private lemma sum_A_over_baseOrbit_eq_N {k : DirIdx} (u : BaseOrbit k) (a d : DirIdx) :
    (∑ v : BaseOrbit a, (A d) u.1 v.1) = (N k a d : Q) := by
  classical
  -- First, rewrite the sum as a sum of `0/1` indicators.
  let p : BaseOrbit a → Prop := fun v => dirMask v.1 u.1 = maskAt d
  have hA : (∑ v : BaseOrbit a,
    (A d) u.1 v.1) = ∑ v : BaseOrbit a,
    (if p v then (1 : Q) else 0) := by
    refine Fintype.sum_congr _ _ ?_
    intro v
    simp [N1000000OrbitalBasis.A, p]
  rw [hA]
  -- Sum of indicators equals the cardinality of the satisfying subtype.
  have hsum_filter :
      (∑ v : BaseOrbit a, (if p v then (1 : Q) else 0)) = ((Finset.univ.filter p).card : Q) := by
    -- Turn the `Fintype` sum into a `Finset` sum and rewrite by filtering.
    change (Finset.univ.sum (fun v : BaseOrbit a => if p v then (1 : Q) else 0)) =
        ((Finset.univ.filter p).card : Q)
    -- Rewrite the sum of indicators as a sum over the filtered set.
    have hFilter :
        (Finset.univ.sum (fun v : BaseOrbit a => if p v then (1 : Q) else 0)) =
          ∑ v ∈ (Finset.univ : Finset (BaseOrbit a)) with p v, (1 : Q) := by
      -- `Finset.sum_filter` gives `∑ v ∈ univ with p v, 1 = ∑ v ∈ univ, if p v then 1 else 0`.
      -- We use the symmetric orientation, and `change` to avoid `simp` recursion.
      change (∑ v ∈ (Finset.univ : Finset (BaseOrbit a)), if p v then (1 : Q) else 0) =
          ∑ v ∈ (Finset.univ : Finset (BaseOrbit a)) with p v, (1 : Q)
      exact
        (Finset.sum_filter (s := (Finset.univ : Finset (BaseOrbit a))) (p := p)
          (f := fun _v : BaseOrbit a => (1 : Q))).symm
    -- Sum of `1`s is the cardinality (as a cast to `ℚ`).
    have hOnes :
        (∑ v ∈ (Finset.univ : Finset (BaseOrbit a)) with p v, (1 : Q)) =
          ((Finset.univ.filter p).card : Q) := by
      -- The LHS is the constant sum over the filtered `Finset`.
      change (∑ _v ∈ (Finset.univ.filter p), (1 : Q)) = ((Finset.univ.filter p).card : Q)
      -- Evaluate the constant sum and simplify `card • 1`.
      have h := (Finset.sum_const (s := (Finset.univ.filter p)) (b := (1 : Q)))
      -- `Finset.sum_const` returns the sum as `card • 1`; for `ℚ` this is the same as the cast.
      calc
        (∑ _v ∈ (Finset.univ.filter p), (1 : Q)) = (Finset.univ.filter p).card • (1 : Q) := h
        _ = ((Finset.univ.filter p).card : Q) := by
              exact nsmul_one (Finset.univ.filter p).card
    exact hFilter.trans hOnes
  have hcardNat : Fintype.card { v : BaseOrbit a // p v } = (Finset.univ.filter p).card := by
    simpa using (Fintype.card_subtype (α := BaseOrbit a) (p := p))
  have hcard :
      (Fintype.card { v : BaseOrbit a // p v } : Q) =
        ((Finset.univ.filter p).card : Q) := by
    exact_mod_cast hcardNat
  have hsum_sub :
      (∑ v : BaseOrbit a,
        (if p v then (1 : Q) else 0)) = (Fintype.card { v : BaseOrbit a // p v } : Q) :=
    hsum_filter.trans hcard.symm
  -- Identify this subtype with `Inter u a d` and use the exact intersection count.
  have hcardInter :
      (Fintype.card { v : BaseOrbit a // p v } : Q) = (Fintype.card (Inter u a d) : Q) := by
    have hNat : Fintype.card { v : BaseOrbit a // p v } = Fintype.card (Inter u a d) := by
      simpa using (Fintype.card_congr (interEquivBaseOrbit (u := u) (a := a) (d := d))).symm
    exact_mod_cast hNat
  have hsumInter :
      (∑ v : BaseOrbit a, (if p v then (1 : Q) else 0)) = (Fintype.card (Inter u a d) : Q) :=
    hsum_sub.trans hcardInter
  -- Finally, replace the cardinality by the closed-form intersection number.
  have hcardN : (Fintype.card (Inter u a d) : Q) = (N k a d : Q) := by
    exact_mod_cast (card_inter_eq_N (u := u) (a := a) (d := d))
  exact hsumInter.trans hcardN

-- `A`-compression: `(B_r)ᴴ * A_d * (B_r)` computed via intersection numbers.
theorem congr_A_eq_compBasis (r : Block) (d : DirIdx) :
    (B r)ᴴ * (A d) * (B r) = compBasis r d := by
  classical
  ext p q
  -- Expand the `3×3` entry of the triple product as a double sum over vertices.
  have hExpand :
      ((B r)ᴴ * (A d) * (B r)) p q = ∑ u : V, ∑ v : V, (B r u p) * (A d u v) * (B r v q) := by
    classical
    -- Expand outer, then inner multiplication, distribute, swap sums, and remove `star`.
    have sum_swap (f : V → V → Q) :
        (∑ v : V, ∑ u : V, f u v) = ∑ u : V, ∑ v : V, f u v := by
      -- Convert both sides to a single sum over `V × V`, then use `prodComm`.
      have h1 :
          (∑ v : V, ∑ u : V, f u v) = ∑ x : V × V, f x.2 x.1 := by
        simpa using (Fintype.sum_prod_type (f := fun x : V × V => f x.2 x.1)).symm
      have h2 :
          (∑ u : V, ∑ v : V, f u v) = ∑ x : V × V, f x.1 x.2 := by
        simpa using (Fintype.sum_prod_type (f := fun x : V × V => f x.1 x.2)).symm
      have h3 :
          (∑ x : V × V, f x.2 x.1) = ∑ x : V × V, f x.1 x.2 := by
        refine
          Fintype.sum_equiv (Equiv.prodComm V V) (fun x : V × V => f x.2 x.1)
            (fun x : V × V => f x.1 x.2) ?_
        intro x
        rfl
      exact h1.trans (h3.trans h2.symm)
    calc
      ((B r)ᴴ * (A d) * (B r)) p q
          = ∑ v : V, ((B r)ᴴ * (A d)) p v * (B r) v q := by
              exact (Matrix.mul_apply (M := (B r)ᴴ * (A d)) (N := (B r)) (i := p) (k := q))
      _ = ∑ v : V, (∑ u : V, ((B r)ᴴ) p u * (A d) u v) * (B r) v q := by
            refine Fintype.sum_congr _ _ ?_
            intro v
            -- Expand `((B r)ᴴ * (A d)) p v` by `Matrix.mul_apply`.
            exact congrArg (fun t => t * (B r) v q)
              (Matrix.mul_apply (M := (B r)ᴴ) (N := (A d)) (i := p) (k := v))
      _ = ∑ v : V, ∑ u : V, ((B r)ᴴ) p u * (A d) u v * (B r) v q := by
            refine Fintype.sum_congr _ _ ?_
            intro v
            -- Distribute multiplication by the (constant-in-`u`) factor `(B r) v q`.
            -- We avoid `Finset.sum_mul`/`Finset.mul_sum` over the huge type `V` by using
            -- `Fintype.sum_mul_sum` with a dummy `Unit` index.
            have hDist :
                (∑ u : V, ((B r)ᴴ) p u * (A d) u v) * (B r) v q
                  = ∑ u : V, ((B r)ᴴ) p u * (A d) u v * (B r) v q := by
              calc
                (∑ u : V, ((B r)ᴴ) p u * (A d) u v) * (B r) v q
                    = (∑ u : V, ((B r)ᴴ) p u * (A d) u v) * (∑ _ : Unit, (B r) v q) := by
                        simp
                _ = ∑ u : V, ∑ _ : Unit, ((B r)ᴴ) p u * (A d) u v * (B r) v q := by
                      simpa [mul_assoc] using
                        (Fintype.sum_mul_sum (f := fun u : V => ((B r)ᴴ) p u * (A d) u v)
                          (g := fun _ : Unit => (B r) v q))
                _ = ∑ u : V, ((B r)ᴴ) p u * (A d) u v * (B r) v q := by
                      simp
            exact hDist
      _ = ∑ u : V, ∑ v : V, ((B r)ᴴ) p u * (A d) u v * (B r) v q := by
            simpa using (sum_swap (f := fun u v => ((B r)ᴴ) p u * (A d) u v * (B r) v q))
      _ = ∑ u : V, ∑ v : V, (B r u p) * (A d u v) * (B r v q) := by
            -- `((B r)ᴴ) p u = star (B r u p) = B r u p` over `ℚ`.
            refine Fintype.sum_congr _ _ ?_
            intro u
            refine Fintype.sum_congr _ _ ?_
            intro v
            simp [Matrix.conjTranspose_apply]
  rw [hExpand]
  -- Reindex `u` and `v` by base orbits.
  have hU :
      (∑ u : V, ∑ v : V, B r u p * A d u v * B r v q)
        =
      ∑ su : Σ k : DirIdx, BaseOrbit k,
        ∑ v : V, B r su.2.1 p * A d su.2.1 v * B r v q := by
    simpa using (sum_over_vertices_eq_sum_over_orbits (f := fun u => ∑ v : V,
      B r u p * A d u v * B r v q))
  rw [hU]
  have hV :
      (∑ su : Σ k : DirIdx, BaseOrbit k, ∑ v : V, B r su.2.1 p * A d su.2.1 v * B r v q)
        =
      ∑ su : Σ k : DirIdx, BaseOrbit k,
        ∑ sv : Σ a : DirIdx, BaseOrbit a,
          B r su.2.1 p * A d su.2.1 sv.2.1 * B r sv.2.1 q := by
    refine Fintype.sum_congr _ _ ?_
    intro su
    simpa using (sum_over_vertices_eq_sum_over_orbits
      (f := fun v => B r su.2.1 p * A d su.2.1 v * B r v q))
  rw [hV]
  -- Convert the sigma-type sums into iterated sums over `k,u,a,v`.
  simp only [Fintype.sum_sigma, B_eq_bVal_of_baseOrbit]
  -- Now compute the `v`-sum using the intersection numbers.
  -- First, factor the constants `bVal r p k` and `bVal r q a` out of the `v`-sum.
  have hvFactor :
      ∀ (k : DirIdx) (u : BaseOrbit k) (a : DirIdx),
        (∑ v : BaseOrbit a, bVal r p k * (A d) u.1 v.1 * bVal r q a)
          = bVal r p k * (∑ v : BaseOrbit a, (A d) u.1 v.1) * bVal r q a := by
    intro k u a
    classical
    -- Unfold the `Fintype` sum to a `Finset` sum and factor out the constants using
    -- `Finset.sum_mul` and `Finset.mul_sum`.
    change (Finset.univ.sum (fun v : BaseOrbit a => bVal r p k * (A d) u.1 v.1 * bVal r q a))
        = bVal r p k * (Finset.univ.sum (fun v : BaseOrbit a => (A d) u.1 v.1)) * bVal r q a
    have hRight :
        Finset.univ.sum (fun v : BaseOrbit a => bVal r p k * (A d) u.1 v.1 * bVal r q a)
          =
          (Finset.univ.sum (fun v : BaseOrbit a => bVal r p k * (A d) u.1 v.1)) * bVal r q a := by
      exact
        (Finset.sum_mul (s := (Finset.univ : Finset (BaseOrbit a)))
            (f := fun v : BaseOrbit a => bVal r p k * (A d) u.1 v.1) (a := bVal r q a)).symm
    have hLeft :
        Finset.univ.sum (fun v : BaseOrbit a => bVal r p k * (A d) u.1 v.1)
          =
          bVal r p k * (Finset.univ.sum (fun v : BaseOrbit a => (A d) u.1 v.1)) := by
      exact
        (Finset.mul_sum (a := bVal r p k) (s := (Finset.univ : Finset (BaseOrbit a)))
            (f := fun v : BaseOrbit a => (A d) u.1 v.1)).symm
    calc
      Finset.univ.sum (fun v : BaseOrbit a => bVal r p k * (A d) u.1 v.1 * bVal r q a)
          =
          (Finset.univ.sum (fun v : BaseOrbit a => bVal r p k * (A d) u.1 v.1)) * bVal r q a := by
            exact hRight
      _ =
          (bVal r p k * (Finset.univ.sum (fun v : BaseOrbit a => (A d) u.1 v.1))) * bVal r q a := by
            rw [hLeft]
      _ =
          bVal r p k * (Finset.univ.sum (fun v : BaseOrbit a => (A d) u.1 v.1)) * bVal r q a := by
            rfl
  -- Apply the factorization and evaluate the `v`-sum via `sum_A_over_baseOrbit_eq_N`.
  have hvEval :
      ∀ (k : DirIdx) (u : BaseOrbit k) (a : DirIdx),
        (∑ v : BaseOrbit a, bVal r p k * (A d) u.1 v.1 * bVal r q a)
          = bVal r p k * (N k a d : Q) * bVal r q a := by
    intro k u a
    calc
      (∑ v : BaseOrbit a, bVal r p k * (A d) u.1 v.1 * bVal r q a)
          = bVal r p k * (∑ v : BaseOrbit a, (A d) u.1 v.1) * bVal r q a := hvFactor k u a
      _ = bVal r p k * (N k a d : Q) * bVal r q a := by
            -- Rewrite the inner sum using the intersection-number formula.
            rw [sum_A_over_baseOrbit_eq_N (u := u) (a := a) (d := d)]
  -- Rewrite the inner `v`-sum using `hvEval`.
  have hVsum :
      (∑ k : DirIdx, ∑ u : BaseOrbit k, ∑ a : DirIdx,
          ∑ v : BaseOrbit a, bVal r p k * (A d) u.1 v.1 * bVal r q a)
        =
        ∑ k : DirIdx, ∑ u : BaseOrbit k, ∑ a : DirIdx,
          bVal r p k * (N k a d : Q) * bVal r q a := by
    -- Rewrite the innermost `v`-sum everywhere.
    simp_rw [hvEval]
  rw [hVsum]
  -- The remaining `u`-sum is constant; evaluate it as `baseTypeCount k`.
  have huConst :
      ∀ k : DirIdx,
        (∑ _u : BaseOrbit k, (∑ a : DirIdx, bVal r p k * (N k a d : Q) * bVal r q a))
          = (baseTypeCount k : Q) * (∑ a : DirIdx, bVal r p k * (N k a d : Q) * bVal r q a) := by
    intro k
    classical
    -- Turn the `u`-sum into a `Finset` sum and use `Finset.sum_const`.
    change (Finset.univ.sum (fun _u : BaseOrbit k => (∑ a : DirIdx,
      bVal r p k * (N k a d : Q) * bVal r q a)))
        = (baseTypeCount k : Q) * (∑ a : DirIdx, bVal r p k * (N k a d : Q) * bVal r q a)
    -- `univ.card = card (BaseOrbit k)`, and `card (BaseOrbit k) = baseTypeCount k`.
    have hcardNat : (Finset.univ : Finset (BaseOrbit k)).card = baseTypeCount k := by
      -- `Fintype.card` is definitionally `Finset.univ.card`.
      change Fintype.card (BaseOrbit k) = baseTypeCount k
      exact N1000000OrbitCounting.baseOrbit_card (k := k)
    have hcardQ : ((Finset.univ : Finset (BaseOrbit k)).card : Q) = (baseTypeCount k : Q) := by
      exact_mod_cast hcardNat
    -- Sum of a constant.
    have hsum :
        (Finset.univ.sum (fun _u : BaseOrbit k => (∑ a : DirIdx,
          bVal r p k * (N k a d : Q) * bVal r q a)))
          = ((Finset.univ : Finset (BaseOrbit k)).card : Q)
              * (∑ a : DirIdx, bVal r p k * (N k a d : Q) * bVal r q a) := by
      -- `∑ _u in univ, c = card • c`.
      -- Align with `Finset.sum_const` and rewrite `card • c` as multiplication.
      let C : Q := (∑ a : DirIdx, bVal r p k * (N k a d : Q) * bVal r q a)
      change (∑ _u ∈ (Finset.univ : Finset (BaseOrbit k)), C) =
          ((Finset.univ : Finset (BaseOrbit k)).card : Q) * C
      calc
        (∑ _u ∈ (Finset.univ : Finset (BaseOrbit k)), C)
            = ((Finset.univ : Finset (BaseOrbit k)).card) • C := by
                  exact (Finset.sum_const (s := (Finset.univ : Finset (BaseOrbit k))) (b := C))
        _ = ((Finset.univ : Finset (BaseOrbit k)).card : Q) * C := by
              exact (nsmul_eq_mul ((Finset.univ : Finset (BaseOrbit k)).card) C)
    -- Replace the cardinality by `baseTypeCount k`.
    -- Rewrite the scalar factor via `hcardQ`.
    calc
      (Finset.univ.sum fun _u : BaseOrbit k =>
            (∑ a : DirIdx, bVal r p k * (N k a d : Q) * bVal r q a))
          = ((Finset.univ : Finset (BaseOrbit k)).card : Q)
              * (∑ a : DirIdx, bVal r p k * (N k a d : Q) * bVal r q a) := hsum
      _ = (baseTypeCount k : Q) * (∑ a : DirIdx, bVal r p k * (N k a d : Q) * bVal r q a) := by
            exact congrArg (fun t : Q => t * (∑ a : DirIdx,
              bVal r p k * (N k a d : Q) * bVal r q a)) hcardQ
  -- Use `huConst` to remove the `u`-sum, then match `compBasis`.
  -- First collapse the `u`-sum.
  have hUsum :
      (∑ k : DirIdx, ∑ _u : BaseOrbit k, ∑ a : DirIdx, bVal r p k * (N k a d : Q) * bVal r q a)
        =
        ∑ k : DirIdx,
          (baseTypeCount k : Q) * (∑ a : DirIdx,
          bVal r p k * (N k a d : Q) * bVal r q a) := by
    refine Fintype.sum_congr _ _ ?_
    · intro k
      -- `∑ _u, ∑ a, ...` is definitionaly `∑ _u, (∑ a, ...)`.
      exact huConst (k := k)
  rw [hUsum]
  -- Expand the remaining product and reorder to match `compBasis`.
  classical
  -- Unfold `compBasis` entrywise.
  simp [compBasis,
    N1000000BCompressionCompute.qOfNat,
    mul_assoc,
    mul_left_comm,
    mul_comm,
    Finset.mul_sum]

-- Symmetric basis compression.
theorem congr_ASymm_eq_compBasisSymm (r : Block) (d : DirIdx) :
    (B r)ᴴ * (ASymm d) * (B r) = compBasisSymm r d := by
  classical
  by_cases hFix : tTr[d.1]! = d.1
  · -- Fixed point: both `ASymm` and `compBasisSymm` are just the directed object.
    have hAS : ASymm d = A d := by
      unfold N1000000OrbitalBasis.ASymm
      rw [dif_pos hFix]
    have hCB : compBasisSymm r d = compBasis r d := by
      unfold compBasisSymm
      -- Avoid unfolding `tTr` by using `if_pos` directly.
      simpa using (if_pos hFix :
        (if tTr[d.1]! = d.1 then
          compBasis r d
        else
          compBasis r d + compBasis r (invDir d)) = compBasis r d)
    rw [hAS, hCB]
    exact congr_A_eq_compBasis (r := r) (d := d)
  · -- Non-fixed: `ASymm d = A d + A dTr`,
    -- and `compBasisSymm r d = compBasis r d + compBasis r (invDir d)`.
    let dTr : DirIdx :=
      ⟨tTr[d.1]!, by
        -- `tTr` is a permutation of the 34 indices.
        fin_cases d <;> decide⟩
    have hAS : ASymm d = A d + A dTr := by
      unfold N1000000OrbitalBasis.ASymm
      rw [dif_neg hFix]
    have hCB : compBasisSymm r d = compBasis r d + compBasis r (invDir d) := by
      unfold compBasisSymm
      -- Avoid unfolding `tTr` by using `if_neg` directly.
      simpa using (if_neg hFix :
        (if tTr[d.1]! = d.1 then compBasis r d else compBasis r d + compBasis r (invDir d))
          = (compBasis r d + compBasis r (invDir d)))
    -- Rewrite both sides using these decompositions.
    rw [hAS, hCB]
    -- Expand the matrix product across the sum and apply the directed compression lemma twice.
    calc
        (B r)ᴴ * (A d + A dTr) * (B r)
            = (B r)ᴴ * A d * (B r) + (B r)ᴴ * A dTr * (B r) := by
                -- Bilinearity of matrix multiplication.
                simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = compBasis r d + compBasis r dTr := by
            rw [congr_A_eq_compBasis (r := r) (d := d), congr_A_eq_compBasis (r := r) (d := dTr)]
      _ = compBasis r d + compBasis r (invDir d) := by
            -- `dTr` and `invDir d` have the same `.1`, so `compBasis` agrees entrywise.
              have hEq : compBasis r dTr = compBasis r (invDir d) := by
                ext p q
                rfl
              simp [hEq]

-- The concrete scaled compression identity for our chosen `B`.
theorem compressionHypScaledForB :
    ∀ f : Coloring n, ∀ r : Block,
      (blockScales[r.1]! : Q) • S (xFromColoring f) r =
        (B r)ᴴ * (corrAvgMatrix (f := f)) * (B r) := by
  classical
  intro f r
  have hDecomp := corrAvgMatrix_eq_A_id_add_sum_var (f := f)
  -- A transpose-form of the symmetric compression lemma (since `ℚ` has trivial `star`).
  have congr_ASymm_eq_compBasisSymm_T (d : DirIdx) :
      (B r)ᵀ * (ASymm d) * (B r) = compBasisSymm r d := by
    simpa using (congr_ASymm_eq_compBasisSymm (r := r) (d := d))
  -- First, expand the compression of `corrAvgMatrix` using the symmetric orbital decomposition.
  have hCompressed :
      (B r)ᴴ * (corrAvgMatrix (f := f)) * (B r)
        =
        (blockScales[r.1]! : Q) • S0 r
          + ∑ i : Var, (xFromColoring f i) • ((blockScales[r.1]! : Q) • Si r i) := by
    calc
        (B r)ᴴ * (corrAvgMatrix (f := f)) * (B r)
            = (B r)ᴴ *
                (A idDirIdx + ∑ i : Var, (xFromColoring f i) • ASymm (varOrbit i)) *
                (B r) := by
                  simp [hDecomp]
      _ =
          (B r)ᴴ * (A idDirIdx) * (B r)
            + (B r)ᴴ * (∑ i : Var, (xFromColoring f i) • ASymm (varOrbit i)) * (B r) := by
              -- Normalize to the right-associated form, distribute on the right, then re-associate
              -- back.
              -- (This avoids depending on definitional parenthesization.)
              -- `simp only` keeps this purely about associativity.
              simp only [Matrix.mul_assoc]
              -- Distribute `(A id + sum) * B` and then `Bᴴ * (...)`.
              rw [Matrix.add_mul, Matrix.mul_add]
              -- The goal is already in the same (right-associated) form after rewriting by
              -- `mul_assoc`.
      _ =
          compBasis r idDirIdx
            + (B r)ᴴ * (∑ i : Var, (xFromColoring f i) • ASymm (varOrbit i)) * (B r) := by
              rw [congr_A_eq_compBasis (r := r) (d := idDirIdx)]
      _ =
          compBasis r idDirIdx
            + ∑ i : Var, (xFromColoring f i) • (compBasisSymm r (varOrbit i)) := by
              -- Push the compression through the sum, and then use the symmetric compression lemma
              -- termwise.
              have hSum :
                  (B r)ᴴ * (∑ i : Var, (xFromColoring f i) • ASymm (varOrbit i)) * (B r)
                    =
                    ∑ i : Var, (xFromColoring f i) • ((B r)ᴴ * (ASymm (varOrbit i)) * (B r)) := by
                -- `Matrix.mul_sum` / `Matrix.sum_mul` rewrite `M * (∑ i, Xi) * N` into a sum of `M
                -- * Xi * N`.
                -- `Matrix.mul_smul` / `Matrix.smul_mul` pull scalars out.
                simp [Matrix.mul_sum,
                  Matrix.sum_mul,
                  Matrix.mul_smul,
                  Matrix.smul_mul,
                  Matrix.mul_assoc]
              calc
                compBasis r idDirIdx
                    + (B r)ᴴ * (∑ i : Var, (xFromColoring f i) • ASymm (varOrbit i)) * (B r)
                    =
                    compBasis r idDirIdx
                      + ∑ i : Var,
                        (xFromColoring f i) • ((B r)ᴴ * (ASymm (varOrbit i)) * (B r)) := by
                        simpa [hSum]
                  _ =
                      compBasis r idDirIdx
                        + ∑ i : Var, (xFromColoring f i) • (compBasisSymm r (varOrbit i)) := by
                          -- `simp` may unfold `ᴴ` into `ᵀ`, so provide both forms.
                          simp [congr_ASymm_eq_compBasisSymm_T]
      _ =
          (blockScales[r.1]! : Q) • S0 r
            + ∑ i : Var, (xFromColoring f i) • ((blockScales[r.1]! : Q) • Si r i) := by
              -- The computed identities match the compressed basis with the certificate blocks.
              simp [compBasis_id_matches_S0 (r := r), compBasisSymm_var_matches_Si (r := r)]
  -- Now rewrite the left-hand side into the same shape and conclude.
  calc
    (blockScales[r.1]! : Q) • S (xFromColoring f) r
        =
        (blockScales[r.1]! : Q) • S0 r
          + ∑ i : Var, (xFromColoring f i) • ((blockScales[r.1]! : Q) • Si r i) := by
          -- Distribute the outer scale through `S = S0 + ∑ x • Si`, commuting scalars as needed.
          -- (We use `Finset.smul_sum` since the big sum is a `Finset.univ` sum.)
          have hComm :
              ∀ x : Q, ∀ M : Matrix (Fin 3) (Fin 3) Q,
                (blockScales[r.1]! : Q) • (x • M) = x • ((blockScales[r.1]! : Q) • M) := by
            intro x M
            -- Both sides are `(blockScales * x) • M` up to commutativity of `ℚ`.
            simp [smul_smul, mul_comm]
          -- Expand `S` and push scalars through the sum.
          simp [N1000000WeakDuality.S, smul_add, Finset.smul_sum, hComm]
    _ = (B r)ᴴ * (corrAvgMatrix (f := f)) * (B r) := by
          simpa using hCompressed.symm

theorem compressionHypScaled :
    N1000000RelaxationPsdSoundness.CompressionHypScaled :=
  ⟨B, compressionHypScaledForB⟩

end N1000000BCompressionForB

end Distributed2Coloring.LowerBound
