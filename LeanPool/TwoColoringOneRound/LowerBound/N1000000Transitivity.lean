/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

import LeanPool.TwoColoringOneRound.LowerBound.Correlation
import LeanPool.TwoColoringOneRound.LowerBound.N1000000AvailFrom
import LeanPool.TwoColoringOneRound.LowerBound.N1000000MaskComplete
import LeanPool.TwoColoringOneRound.LowerBound.N1000000OrbitalBasis
import LeanPool.TwoColoringOneRound.LowerBound.N1000000OrbitCounting
import LeanPool.TwoColoringOneRound.LowerBound.N1000000PairTransitivity
import LeanPool.TwoColoringOneRound.LowerBound.N1000000StructureConstants

namespace Distributed2Coloring.LowerBound

namespace N1000000Transitivity

open scoped BigOperators

open Distributed2Coloring.LowerBound.Correlation
open Distributed2Coloring.LowerBound.N1000000AvailFrom
open Distributed2Coloring.LowerBound.N1000000MaskComplete
open Distributed2Coloring.LowerBound.N1000000OrbitalBasis
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
abbrev G := Correlation.G n
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Mask := Distributed2Coloring.LowerBound.Mask
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev DirIdx := N1000000StructureConstants.DirIdx

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev AvailFrom3 := AvailFrom (s := 3)

noncomputable instance : Fintype G := by infer_instance

theorem dirMask_smul (σ : G) (u v : V) : dirMask (σ • u) (σ • v) = dirMask u v := by
  classical
  simp [N1000000PairTransitivity.dirMask, N1000000PairTransitivity.bit]

theorem dirMask_isPartialPermMask (u v : V) : IsPartialPermMask (dirMask u v) := by
  classical
  constructor
  · intro i
    -- At most one `j` satisfies `u_i = v_j`.
    refine (Finset.card_le_one.2 ?_)
    intro j₁ hj₁ j₂ hj₂
    have hbit₁ : (dirMask u v).testBit (i.1 * 3 + j₁.1) = true := by
      exact (Finset.mem_filter.1 hj₁).2
    have hbit₂ : (dirMask u v).testBit (i.1 * 3 + j₂.1) = true := by
      exact (Finset.mem_filter.1 hj₂).2
    have hdec₁ : decide (u.1 i = v.1 j₁) = true := by
      -- rewrite the bit using `dirMask_testBit`
      exact (dirMask_testBit (u := u) (v := v) (i := i) (j := j₁)).symm.trans hbit₁
    have hdec₂ : decide (u.1 i = v.1 j₂) = true := by
      exact (dirMask_testBit (u := u) (v := v) (i := i) (j := j₂)).symm.trans hbit₂
    have h₁ : u.1 i = v.1 j₁ := of_decide_eq_true hdec₁
    have h₂ : u.1 i = v.1 j₂ := of_decide_eq_true hdec₂
    -- Injectivity of `v` forces `j₁ = j₂`.
    have : v.1 j₁ = v.1 j₂ := by
      calc
        v.1 j₁ = u.1 i := by simpa using h₁.symm
        _ = v.1 j₂ := by simpa using h₂
    exact v.2 this
  · intro j
    -- At most one `i` satisfies `u_i = v_j`.
    refine (Finset.card_le_one.2 ?_)
    intro i₁ hi₁ i₂ hi₂
    have hbit₁ : (dirMask u v).testBit (i₁.1 * 3 + j.1) = true := by
      exact (Finset.mem_filter.1 hi₁).2
    have hbit₂ : (dirMask u v).testBit (i₂.1 * 3 + j.1) = true := by
      exact (Finset.mem_filter.1 hi₂).2
    have hdec₁ : decide (u.1 i₁ = v.1 j) = true := by
      exact (dirMask_testBit (u := u) (v := v) (i := i₁) (j := j)).symm.trans hbit₁
    have hdec₂ : decide (u.1 i₂ = v.1 j) = true := by
      exact (dirMask_testBit (u := u) (v := v) (i := i₂) (j := j)).symm.trans hbit₂
    have h₁ : u.1 i₁ = v.1 j := of_decide_eq_true hdec₁
    have h₂ : u.1 i₂ = v.1 j := of_decide_eq_true hdec₂
    have : u.1 i₁ = u.1 i₂ := by
      calc
        u.1 i₁ = v.1 j := h₁
        _ = u.1 i₂ := by simpa using h₂.symm
    exact u.2 this

theorem exists_dirIdx_of_dirMask (u v : V) : ∃ d : DirIdx, maskAt d = dirMask u v := by
  have hm : dirMask u v < (1 <<< 9) := by
    simpa [Nat.shiftLeft_eq] using (dirMask_lt (u := u) (v := v))
  exact exists_dirIdx_of_isPartialPermMask (m := dirMask u v) hm (dirMask_isPartialPermMask u v)

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def dirIdxOfDirMask (u v : V) : DirIdx :=
  Classical.choose (exists_dirIdx_of_dirMask (u := u) (v := v))

theorem maskAt_dirIdxOfDirMask (u v : V) : maskAt (dirIdxOfDirMask u v) = dirMask u v :=
  Classical.choose_spec (exists_dirIdx_of_dirMask (u := u) (v := v))

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
noncomputable def dirIdxBase (u : V) : DirIdx :=
  dirIdxOfDirMask baseVertex u

theorem maskAt_dirIdxBase (u : V) : maskAt (dirIdxBase u) = dirMask baseVertex u :=
  maskAt_dirIdxOfDirMask (u := baseVertex) (v := u)

theorem exists_perm_send_to_base (u : V) : ∃ σ : G, σ • u = baseVertex := by
  classical
  have hmtp : MulAction.IsMultiplyPretransitive G SymN 3 :=
    Equiv.Perm.isMultiplyPretransitive (α := SymN) 3
  have hEmb :
      ∀ x y : Fin 3 ↪ SymN, ∃ σ : G, σ • x = y :=
    (MulAction.isMultiplyPretransitive_iff (G := G) (α := SymN) (n := 3)).1 hmtp
  let x : Fin 3 ↪ SymN := ⟨u.1, u.2⟩
  let y : Fin 3 ↪ SymN := ⟨baseVertex.1, baseVertex.2⟩
  rcases hEmb x y with ⟨σ, hσ⟩
  refine ⟨σ, ?_⟩
  apply Subtype.ext
  funext i
  have := congrArg (fun (t : Fin 3 ↪ SymN) => t i) hσ
  simpa [x, y] using this

-- Stabilizer transitivity within a fixed base orbit.
theorem exists_perm_fixing_base_of_baseOrbit (k : DirIdx) (w w' : BaseOrbit k) :
    ∃ τ : G, τ • baseVertex = baseVertex ∧ τ • w.1 = w'.1 := by
  classical
  let keyEmb (z : BaseOrbit k) : FreeCol k ↪ AvailFrom3 :=
    ⟨fun j => ⟨z.1.1 j.1, baseOrbit_freeCoord_outside (u := z) j⟩, by
      intro a b hab
      apply Subtype.ext
      have : z.1.1 a.1 = z.1.1 b.1 := by
        simpa using congrArg Subtype.val hab
      exact z.1.2 this⟩
  let cutoff : SymN := ⟨3, by decide⟩
  let baseSet : Set SymN := Set.Iio cutoff
  let availEquiv : AvailFrom3 ≃ ↥(SubMulAction.ofFixingSubgroup G baseSet) := by
    refine
      { toFun := fun x => ⟨x.1, by
            change ¬ x.1 < cutoff
            exact not_lt.2 (by simpa [cutoff] using x.2)⟩
        invFun := fun x => ⟨x.1, by
            have hx : x.1 ∉ baseSet := x.2
            have hx' : ¬ x.1 < cutoff := by
              simpa [baseSet] using hx
            simpa [cutoff] using (not_lt.1 hx')⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
  let m : Nat := Fintype.card (FreeCol k)
  let e : FreeCol k ≃ Fin m := Fintype.equivFin (FreeCol k)
  let x : Fin m ↪ SubMulAction.ofFixingSubgroup G baseSet :=
    (e.symm.toEmbedding).trans ((keyEmb w).trans availEquiv.toEmbedding)
  let y : Fin m ↪ SubMulAction.ofFixingSubgroup G baseSet :=
    (e.symm.toEmbedding).trans ((keyEmb w').trans availEquiv.toEmbedding)
  letI : MulAction.IsMultiplyPretransitive G SymN (baseSet.ncard + m) :=
    Equiv.Perm.isMultiplyPretransitive (α := SymN) (baseSet.ncard + m)
  have hmtp :
      MulAction.IsMultiplyPretransitive (fixingSubgroup G baseSet)
        (SubMulAction.ofFixingSubgroup G baseSet) m :=
    SubMulAction.ofFixingSubgroup.isMultiplyPretransitive (G := G) (s := baseSet)
      (m := m) (n := baseSet.ncard + m) rfl
  have hEmb :
      ∀ x y : Fin m ↪ SubMulAction.ofFixingSubgroup G baseSet,
        ∃ τ : fixingSubgroup G baseSet, τ • x = y :=
    (MulAction.isMultiplyPretransitive_iff
      (G := fixingSubgroup G baseSet)
      (α := SubMulAction.ofFixingSubgroup G baseSet)
      (n := m)).1 hmtp
  rcases hEmb x y with ⟨τ, hτ⟩
  refine ⟨τ.1, ?_, ?_⟩
  · have hfix := (mem_fixingSubgroup_iff G).1 τ.2
    apply Subtype.ext
    funext i
    have hi : baseVertex.1 i ∈ baseSet := by
      change (baseVertex.1 i : SymN) < cutoff
      fin_cases i <;> decide
    simpa using hfix (baseVertex.1 i) hi
  · have hfix := (mem_fixingSubgroup_iff G).1 τ.2
    apply Subtype.ext
    funext j
    cases hcol : colMatch (maskAt k) j with
    | none =>
        have hj : colMatch (maskAt k) j = none := by simp [hcol]
        let jf : FreeCol k := ⟨j, hj⟩
        let i : Fin m := e jf
        have hτ_apply :
            τ • (((keyEmb w).trans availEquiv.toEmbedding) jf) =
              ((keyEmb w').trans availEquiv.toEmbedding) jf := by
          have := congrArg
            (fun t : Fin m ↪ SubMulAction.ofFixingSubgroup G baseSet => t i) hτ
          simpa [x, y, e, i, jf, Function.Embedding.trans_apply] using this
        have : τ.1 (w.1.1 j) = w'.1.1 j := by
          simpa [keyEmb, availEquiv, Function.Embedding.trans_apply] using
            congrArg Subtype.val hτ_apply
        simpa using this
    | some i =>
        have hi : colMatch (maskAt k) j = some i := by simp [hcol]
        have hw : w.1.1 j = baseVertex.1 i := base_eq_of_colMatch (u := w) (j := j) (i := i) hi
        have hw' : w'.1.1 j = baseVertex.1 i := base_eq_of_colMatch (u := w') (j := j) (i := i) hi
        have hbase : baseVertex.1 i ∈ baseSet := by
          change (baseVertex.1 i : SymN) < cutoff
          fin_cases i <;> decide
        have hτ_base : τ.1 (baseVertex.1 i) = baseVertex.1 i := hfix _ hbase
        calc
          (τ.1 • w.1).1 j = τ.1 (w.1.1 j) := rfl
          _ = τ.1 (baseVertex.1 i) := by simp [hw]
          _ = baseVertex.1 i := hτ_base
          _ = w'.1.1 j := by simp [hw']

-- Full pair transitivity: equality of directed masks implies existence of a symbol permutation
-- mapping the pair.
theorem exists_perm_of_dirMask_eq {u v u' v' : V} (h : dirMask u v = dirMask u' v') :
    ∃ σ : G, σ • u = u' ∧ σ • v = v' := by
  classical
  rcases exists_perm_send_to_base (u := u) with ⟨σ1, hσ1⟩
  rcases exists_perm_send_to_base (u := u') with ⟨σ2, hσ2⟩
  let w : V := σ1 • v
  let w' : V := σ2 • v'
  have hw : dirMask baseVertex w = dirMask u v := by
    have : dirMask (σ1 • u) (σ1 • v) = dirMask u v := dirMask_smul (σ := σ1) (u := u) (v := v)
    simpa [w, hσ1] using this
  have hw' : dirMask baseVertex w' = dirMask u' v' := by
    have : dirMask (σ2 • u') (σ2 • v') = dirMask u' v' := dirMask_smul (σ := σ2) (u := u') (v := v')
    simpa [w', hσ2] using this
  have hbase : dirMask baseVertex w = dirMask baseVertex w' := by
    calc
      dirMask baseVertex w = dirMask u v := hw
      _ = dirMask u' v' := by simp [h]
      _ = dirMask baseVertex w' := by simpa using hw'.symm
  -- Choose the orbit index `k` for the common mask.
  let k : DirIdx := dirIdxOfDirMask baseVertex w
  have hk : dirMask baseVertex w = maskAt k := by
    simp [k, maskAt_dirIdxOfDirMask]
  have hk' : dirMask baseVertex w' = maskAt k := by
    simpa [hbase] using hk
  let wOrb : BaseOrbit k := ⟨w, hk⟩
  let w'Orb : BaseOrbit k := ⟨w', hk'⟩
  rcases exists_perm_fixing_base_of_baseOrbit k wOrb w'Orb with ⟨τ, hτbase, hτw⟩
  let σ : G := σ2.symm * τ * σ1
  refine ⟨σ, ?_, ?_⟩
  · -- on `u`
    calc
      σ • u = (σ2.symm * τ * σ1) • u := rfl
      _ = σ2.symm • (τ • (σ1 • u)) := by simp [mul_smul]
      _ = σ2.symm • (τ • baseVertex) := by simp [hσ1]
      _ = σ2.symm • baseVertex := by simp [hτbase]
      _ = u' := by
        have : σ2 • u' = baseVertex := hσ2
        -- act by `σ2.symm` on both sides
        have : u' = σ2.symm • baseVertex := by
          simpa [smul_smul] using congrArg (fun t => σ2.symm • t) this
        simpa using this.symm
  · -- on `v`
    have hτw' : τ • w = w' := by
      simpa [wOrb, w'Orb, w, w'] using hτw
    calc
      σ • v = (σ2.symm * τ * σ1) • v := rfl
      _ = σ2.symm • (τ • (σ1 • v)) := by simp [mul_smul]
      _ = σ2.symm • (τ • w) := by rfl
      _ = σ2.symm • w' := by simp [hτw']
      _ = v' := by
        -- `w' = σ2 • v'`
        simp [w', smul_smul]

theorem corrAvg_eq_of_dirMask_eq (f : Coloring n) {u v u' v' : V}
    (h : dirMask u v = dirMask u' v') : corrAvg f u v = corrAvg f u' v' := by
  classical
  rcases exists_perm_of_dirMask_eq (u := u) (v := v) (u' := u') (v' := v') h with ⟨σ, hu, hv⟩
  have hInv := (corrAvg_smul (f := f) (τ := σ) (u := u) (v := v))
  simpa [hu, hv] using hInv.symm

end N1000000Transitivity

end Distributed2Coloring.LowerBound
