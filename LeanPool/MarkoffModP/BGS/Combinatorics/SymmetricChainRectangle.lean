/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Combinatorics.ProductOfChainsGrid

/-!
# The rectangle symmetric-chain equivalence

This packages the explicit rectangle codec as an equivalence.  Keeping this
finite, self-contained transport boundary separate lets product decompositions
be assembled from standard equivalence combinators.
-/

namespace BGS.Combinatorics

abbrev gridChainKey (m n : ℕ) :=
  Fin (min m n + 1)

abbrev gridChainLength (m n : ℕ) (key : gridChainKey m n) :=
  m + n - 2 * key

private def gridChainEncode (m n : ℕ)
    (point : Fin (m + 1) × Fin (n + 1)) :
    Σ key : gridChainKey m n, Fin (gridChainLength m n key + 1) := by
  have hx : (point.1 : ℕ) ≤ m :=
    Nat.le_of_lt_succ point.1.isLt
  have hy : (point.2 : ℕ) ≤ n :=
    Nat.le_of_lt_succ point.2.isLt
  let key := gridKey m n point.1 point.2
  let position := gridPosition m n point.1 point.2
  exact
    ⟨⟨key, Nat.lt_succ_iff.mpr (gridKey_le_min hx hy)⟩,
      ⟨position, Nat.lt_succ_iff.mpr (gridPosition_le hx hy)⟩⟩

private def gridChainDecode (m n : ℕ)
    (point :
      Σ key : gridChainKey m n, Fin (gridChainLength m n key + 1)) :
    Fin (m + 1) × Fin (n + 1) := by
  have hkey : (point.1 : ℕ) ≤ min m n :=
    Nat.le_of_lt_succ point.1.isLt
  have hposition :
      (point.2 : ℕ) ≤ m + n - 2 * point.1 :=
    Nat.le_of_lt_succ point.2.isLt
  exact
    (⟨gridDecodeX m n point.1 point.2,
        Nat.lt_succ_iff.mpr (gridDecodeX_le hkey hposition)⟩,
      ⟨gridDecodeY m n point.1 point.2,
        Nat.lt_succ_iff.mpr (gridDecodeY_le hkey hposition)⟩)

private theorem gridChainDecode_encode (m n : ℕ)
    (point : Fin (m + 1) × Fin (n + 1)) :
    gridChainDecode m n (gridChainEncode m n point) = point := by
  have hx : (point.1 : ℕ) ≤ m :=
    Nat.le_of_lt_succ point.1.isLt
  have hy : (point.2 : ℕ) ≤ n :=
    Nat.le_of_lt_succ point.2.isLt
  apply Prod.ext
  · apply Fin.ext
    exact gridDecode_encode_x hx hy
  · apply Fin.ext
    exact gridDecode_encode_y hx hy

private theorem gridChainEncode_decode (m n : ℕ)
    (point :
      Σ key : gridChainKey m n, Fin (gridChainLength m n key + 1)) :
    gridChainEncode m n (gridChainDecode m n point) = point := by
  rcases point with ⟨key, position⟩
  have hkey : (key : ℕ) ≤ min m n :=
    Nat.le_of_lt_succ key.isLt
  have hposition : (position : ℕ) ≤ m + n - 2 * key :=
    Nat.le_of_lt_succ position.isLt
  have hencodedKey :
      (gridChainEncode m n (gridChainDecode m n ⟨key, position⟩)).1 = key := by
    apply Fin.ext
    exact gridKey_decode hkey hposition
  refine Sigma.ext hencodedKey ?_
  apply (Fin.heq_ext_iff
    (congrArg (fun k ↦ gridChainLength m n k + 1) hencodedKey)).2
  exact gridPosition_decode hkey hposition

/-- The explicit symmetric-chain decomposition of a rectangle. -/
def gridChainEquiv (m n : ℕ) :
    Fin (m + 1) × Fin (n + 1) ≃
      Σ key : gridChainKey m n, Fin (gridChainLength m n key + 1) where
  toFun := gridChainEncode m n
  invFun := gridChainDecode m n
  left_inv := gridChainDecode_encode m n
  right_inv := gridChainEncode_decode m n

end BGS.Combinatorics
