/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Combinatorics.SymmetricChainBasic
import LeanPool.MarkoffModP.BGS.Combinatorics.SymmetricChainRectangle

/-!
# Products of symmetric-chain decompositions

The product with one more finite chain is obtained by composing four standard
equivalences: the old chain code, sigma-product distribution, the explicit
rectangle decomposition on each old chain, and sigma associativity.
-/

namespace BGS.Combinatorics

namespace SymmetricChainDecomposition

variable {P : Type*} [PartialOrder P] {rank : P → ℕ} {total : ℕ}

abbrev productKey
    (decomposition : SymmetricChainDecomposition P rank total)
    (a : ℕ) : Type :=
  Σ key : decomposition.Key,
    gridChainKey (decomposition.length key) a

instance productKeyFintype
    (decomposition : SymmetricChainDecomposition P rank total)
    (a : ℕ) :
    Fintype (decomposition.productKey a) := by
  letI : Fintype decomposition.Key := decomposition.keyFintype
  unfold productKey
  infer_instance

abbrev productLength
    (decomposition : SymmetricChainDecomposition P rank total)
    (a : ℕ) (key : decomposition.productKey a) : ℕ :=
  gridChainLength (decomposition.length key.1) a key.2

def productStart
    (decomposition : SymmetricChainDecomposition P rank total)
    (key : decomposition.productKey a) : ℕ :=
  decomposition.start key.1 + key.2

private def productEquiv
    (decomposition : SymmetricChainDecomposition P rank total)
    (a : ℕ) :
    P × Fin (a + 1) ≃
      Σ key : decomposition.productKey a,
        Fin (decomposition.productLength a key + 1) :=
  (((Equiv.prodCongr decomposition.equiv (Equiv.refl (Fin (a + 1)))).trans
      (Equiv.sigmaProdDistrib
        (fun key : decomposition.Key ↦
          Fin (decomposition.length key + 1))
        (Fin (a + 1)))).trans
      (Equiv.sigmaCongrRight
        (fun key : decomposition.Key ↦
          gridChainEquiv (decomposition.length key) a))).trans
    (Equiv.sigmaAssoc
      (fun (key : decomposition.Key)
        (rectangleKey :
          gridChainKey (decomposition.length key) a) ↦
        Fin (gridChainLength
          (decomposition.length key) a rectangleKey + 1))).symm

def productWithChain
    (decomposition : SymmetricChainDecomposition P rank total)
    (a : ℕ) :
    SymmetricChainDecomposition
      (P × Fin (a + 1))
      (fun x ↦ rank x.1 + x.2)
      (total + a) where
  Key := decomposition.productKey a
  start := decomposition.productStart
  length := decomposition.productLength a
  equiv := decomposition.productEquiv a
  rank_decode := by
    rintro ⟨⟨key, rectangleKey⟩, rectanglePosition⟩
    have hkey :
        (rectangleKey : ℕ) ≤ min (decomposition.length key) a :=
      Nat.le_of_lt_succ rectangleKey.isLt
    have hposition :
        (rectanglePosition : ℕ) ≤
          decomposition.length key + a - 2 * rectangleKey :=
      Nat.le_of_lt_succ rectanglePosition.isLt
    let oldPosition : Fin (decomposition.length key + 1) :=
      ⟨gridDecodeX (decomposition.length key) a
          rectangleKey rectanglePosition,
        Nat.lt_succ_iff.mpr
          (gridDecodeX_le hkey hposition)⟩
    let newPosition : Fin (a + 1) :=
      ⟨gridDecodeY (decomposition.length key) a
          rectangleKey rectanglePosition,
        Nat.lt_succ_iff.mpr
          (gridDecodeY_le hkey hposition)⟩
    have holdRank :=
      decomposition.rank_decode ⟨key, oldPosition⟩
    have hgrid := gridDecode_rank hkey hposition
    change
      rank (decomposition.equiv.symm ⟨key, oldPosition⟩) +
          newPosition =
        decomposition.start key + rectangleKey + rectanglePosition
    rw [holdRank]
    dsimp [oldPosition, newPosition]
    omega
  decode_mono := by
    intro productKey i j hij
    rcases productKey with ⟨key, rectangleKey⟩
    have hkey :
        (rectangleKey : ℕ) ≤ min (decomposition.length key) a :=
      Nat.le_of_lt_succ rectangleKey.isLt
    have hi :
        (i : ℕ) ≤ decomposition.length key + a - 2 * rectangleKey :=
      Nat.le_of_lt_succ i.isLt
    have hj :
        (j : ℕ) ≤ decomposition.length key + a - 2 * rectangleKey :=
      Nat.le_of_lt_succ j.isLt
    have hgrid := gridDecode_mono hkey hi hj hij
    change
      (decomposition.equiv.symm
          ⟨key,
            ⟨gridDecodeX (decomposition.length key) a rectangleKey i,
              Nat.lt_succ_iff.mpr (gridDecodeX_le hkey hi)⟩⟩,
        (⟨gridDecodeY (decomposition.length key) a rectangleKey i,
          Nat.lt_succ_iff.mpr (gridDecodeY_le hkey hi)⟩ : Fin (a + 1))) ≤
      (decomposition.equiv.symm
          ⟨key,
            ⟨gridDecodeX (decomposition.length key) a rectangleKey j,
              Nat.lt_succ_iff.mpr (gridDecodeX_le hkey hj)⟩⟩,
        (⟨gridDecodeY (decomposition.length key) a rectangleKey j,
          Nat.lt_succ_iff.mpr (gridDecodeY_le hkey hj)⟩ : Fin (a + 1)))
    constructor
    · exact decomposition.decode_mono key
        ⟨gridDecodeX (decomposition.length key) a rectangleKey i,
          Nat.lt_succ_iff.mpr (gridDecodeX_le hkey hi)⟩
        ⟨gridDecodeX (decomposition.length key) a rectangleKey j,
          Nat.lt_succ_iff.mpr (gridDecodeX_le hkey hj)⟩
        hgrid.1
    · exact hgrid.2
  symmetric := by
    rintro ⟨key, rectangleKey⟩
    have hkey :
        (rectangleKey : ℕ) ≤ min (decomposition.length key) a :=
      Nat.le_of_lt_succ rectangleKey.isLt
    have hleft : (rectangleKey : ℕ) ≤ decomposition.length key :=
      hkey.trans (min_le_left _ _)
    have hright : (rectangleKey : ℕ) ≤ a :=
      hkey.trans (min_le_right _ _)
    have hold := decomposition.symmetric key
    dsimp [productStart, productLength, gridChainLength]
    omega

def punit :
    SymmetricChainDecomposition PUnit (fun _ ↦ 0) 0 where
  Key := PUnit
  start := fun _ ↦ 0
  length := fun _ ↦ 0
  equiv :=
    { toFun := fun _ ↦ ⟨PUnit.unit, ⟨0, by omega⟩⟩
      invFun := fun _ ↦ PUnit.unit
      left_inv := by intro x; cases x; rfl
      right_inv := by
        rintro ⟨key, position⟩
        cases key
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          apply Fin.ext
          omega }
  rank_decode := by
    rintro ⟨key, position⟩
    simp
  decode_mono := by
    intro key i j hij
    trivial
  symmetric := by
    intro key
    rfl

end SymmetricChainDecomposition

end BGS.Combinatorics
