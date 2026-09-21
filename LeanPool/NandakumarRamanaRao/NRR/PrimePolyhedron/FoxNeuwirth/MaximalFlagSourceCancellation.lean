/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.MaximalFlagBridge
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.TopFlagTerminalCancellation
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricFiniteCancellation

/-!
# Source-sum cancellation for maximal Fox--Neuwirth flags

This module performs the finite source-sum reindexing left open after the explicit maximal-flag
bridge.  Rather than classifying a rank-two interval abstractly, it works with the concrete code

```
(bottom permutation, bar-removal permutation, top permutation).
```

For the bottom deleted face, the source sum is paired by `bottomPartner`.  For every positive
internal deleted face, it is paired by the corresponding `removalPartner`.  The bridge theorems
from `MaximalFlagBridge` show that paired codes produce the same deleted simplex, while the code
orientation changes sign.  Mathlib's finite fixed-point-free involution cancellation theorem then
makes each code-indexed internal source sum vanish.

The deleted-face index carried through this module is `k : Fin ((p - 2) + 2)`, matching the index
type of `TopFlagSubdivision.deletionCoefficient`.  Restriction of a `(p - 1)`-dimensional flag
`toSimplex hp z` along that index uses the built-in-cast coface map `deleteFace`, which absorbs the
`(p - 2) + 2` vs `p - 1 + 1` reindexing.
-/

namespace NRR

open scoped BigOperators
open SphereOddDegree.AffineBarycentricSubdivision

variable {p : Nat}

namespace FoxNeuwirthOrderComplex
namespace MaximalFlagCode

open TopFlagSubdivision

/-- The face-dimension reindexing used to view a deletion index `Fin ((p - 2) + 2)` as a coface
index `Fin (p - 1 + 1)`. -/
theorem faceDimEq (hp : Nat.Prime p) : (p - 2) + 2 = p - 1 + 1 := by
  have := hp.two_le; omega

/-- The bottom deletion index, in the deletion-index type `Fin ((p - 2) + 2)`. -/
def bottomDelIdx : Fin ((p - 2) + 2) := ⟨0, by omega⟩

/-- Contribution of one maximal-flag code to one fixed deleted face. -/
noncomputable def codedFaceTerm
    (hp : Nat.Prime p)
    (target : Simplex p (p - 2))
    (k : Fin ((p - 2) + 2))
    (z : Code p) : ZMod p :=
  if (toSimplex hp z).restrict (deleteFace hp (Fin.cast (faceDimEq hp) k)) = target then
    SimplicialChain.faceSign (R := ZMod p) k * (coefficient z : ZMod p)
  else 0

/-- Code-indexed source sum for one fixed deleted position. -/
noncomputable def codedDeletionCoefficient
    (hp : Nat.Prime p)
    (target : Simplex p (p - 2))
    (k : Fin ((p - 2) + 2)) : ZMod p :=
  ∑ z : Code p, codedFaceTerm hp target k z

/-- The bottom partner negates the complete bottom-face summand, including its support predicate. -/
theorem codedFaceTerm_bottomPartner
    (hp : Nat.Prime p)
    (target : Simplex p (p - 2))
    (z : Code p) :
    codedFaceTerm hp target bottomDelIdx (bottomPartner hp z) =
      - codedFaceTerm hp target bottomDelIdx z := by
  have hface :
      (toSimplex hp (bottomPartner hp z)).restrict
          (deleteFace hp (Fin.cast (faceDimEq hp) (bottomDelIdx (p := p)))) =
        (toSimplex hp z).restrict
          (deleteFace hp (Fin.cast (faceDimEq hp) (bottomDelIdx (p := p)))) :=
    bottomFaceCompatibility hp z
  unfold codedFaceTerm
  rw [hface]
  by_cases hf : (toSimplex hp z).restrict
      (deleteFace hp (Fin.cast (faceDimEq hp) (bottomDelIdx (p := p)))) = target
  · simp only [hf, if_true]
    rw [coefficient_bottomPartner hp z]
    push_cast
    ring
  · simp only [hf, if_false, neg_zero]

/-- The code-indexed bottom-face source sum vanishes. -/
theorem codedDeletionCoefficient_bottom_eq_zero
    (hp : Nat.Prime p)
    (target : Simplex p (p - 2)) :
    codedDeletionCoefficient hp target bottomDelIdx = 0 := by
  unfold codedDeletionCoefficient
  exact finite_sum_cancel_of_fixedPointFree_involution
    (bottomPartner hp)
    (bottomPartner_involutive hp)
    (bottomPartner_ne hp)
    (codedFaceTerm hp target bottomDelIdx)
    (codedFaceTerm_bottomPartner hp target)

/-- A removal partner negates the complete positive-internal-face summand. -/
theorem codedFaceTerm_removalPartner
    (hp : Nat.Prime p)
    (target : Simplex p (p - 2))
    (i : Fin (p - 2))
    (z : Code p) :
    codedFaceTerm hp target i.succ.castSucc (removalPartner hp i z) =
      - codedFaceTerm hp target i.succ.castSucc z := by
  have hface :
      (toSimplex hp (removalPartner hp i z)).restrict
          (deleteFace hp (Fin.cast (faceDimEq hp) i.succ.castSucc)) =
        (toSimplex hp z).restrict
          (deleteFace hp (Fin.cast (faceDimEq hp) i.succ.castSucc)) :=
    removalFaceCompatibility hp i z
  unfold codedFaceTerm
  rw [hface]
  by_cases hf : (toSimplex hp z).restrict
      (deleteFace hp (Fin.cast (faceDimEq hp) i.succ.castSucc)) = target
  · simp only [hf, if_true]
    rw [coefficient_removalPartner hp i z]
    push_cast
    ring
  · simp only [hf, if_false, neg_zero]

/-- Every code-indexed positive internal source sum vanishes. -/
theorem codedDeletionCoefficient_removal_eq_zero
    (hp : Nat.Prime p)
    (target : Simplex p (p - 2))
    (i : Fin (p - 2)) :
    codedDeletionCoefficient hp target i.succ.castSucc = 0 := by
  unfold codedDeletionCoefficient
  exact finite_sum_cancel_of_fixedPointFree_involution
    (removalPartner hp i)
    (removalPartner_involutive hp i)
    (removalPartner_ne hp i)
    (codedFaceTerm hp target i.succ.castSucc)
    (codedFaceTerm_removalPartner hp target i)

/-- Every nonterminal code-indexed deleted-position sum vanishes. -/
theorem codedDeletionCoefficient_internal_eq_zero
    (hp : Nat.Prime p)
    (target : Simplex p (p - 2))
    (k : Fin ((p - 2) + 2))
    (hk : k.1 < p - 1) :
    codedDeletionCoefficient hp target k = 0 := by
  by_cases hk0 : k.1 = 0
  · have hk' : k = bottomDelIdx := by
      apply Fin.ext
      simpa [bottomDelIdx] using hk0
    subst k
    exact codedDeletionCoefficient_bottom_eq_zero hp target
  · let i : Fin (p - 2) := ⟨k.1 - 1, by omega⟩
    have hk' : k = i.succ.castSucc := by
      apply Fin.ext
      simp [i]
      omega
    rw [hk']
    exact codedDeletionCoefficient_removal_eq_zero hp target i

/-- The two purely enumerative facts needed to identify code-indexed sums with the original
maximal-simplex sums.  This structure contains no cancellation or boundary assertion. -/
structure CompleteEncoding (hp : Nat.Prime p) : Prop where
  bijective_toSimplex : Function.Bijective (toSimplex hp : Code p → Simplex p (p - 1))
  coefficient_eq : ∀ z : Code p,
    TopFlagSubdivision.integralCoefficient (toSimplex hp z) = coefficient z

/-- The explicit code map as an equivalence, once completeness of the enumeration is known. -/
noncomputable def codeEquivSimplex
    (hp : Nat.Prime p) (henc : CompleteEncoding hp) :
    Code p ≃ Simplex p (p - 1) :=
  Equiv.ofBijective (toSimplex hp) henc.bijective_toSimplex

/-- Transporting a chain along a dimension equality and evaluating it on the correspondingly
transported simplex recovers the original evaluation. -/
theorem transport_chain_apply {a b : ℕ} (h : a = b) (f : Simplex p a → ZMod p)
    (s : Simplex p a) :
    (h ▸ f) (Equiv.cast (congrArg (Simplex p) h) s) = f s := by
  cases h; rfl

/-- Evaluation of a dimension-cast simplex at a vertex index. -/
theorem cast_simplex_apply {a b : ℕ} (h : a = b) (s : Simplex p a) (i : Fin (b + 1)) :
    (Equiv.cast (congrArg (Simplex p) h) s) i = s (Fin.cast (by rw [h]) i) := by
  cases h; rfl

/-- The value of `Fin.succAbove` as an explicit `if`. -/
theorem val_succAbove_eq {n : ℕ} (k : Fin (n + 1)) (j : Fin n) :
    (k.succAbove j).1 = if j.1 < k.1 then j.1 else j.1 + 1 := by
  rcases lt_or_ge j.castSucc k with hlt | hge
  · rw [Fin.succAbove_of_castSucc_lt _ _ hlt, if_pos]
    · simp
    · rw [Fin.lt_def] at hlt; simpa using hlt
  · rw [Fin.succAbove_of_le_castSucc _ _ hge, if_neg]
    · simp
    · rw [Fin.le_def] at hge; simp only [Fin.val_castSucc] at hge; omega
/-- Reindex an actual fixed-position simplicial source sum by maximal-flag codes. -/
theorem deletionCoefficient_eq_codedDeletionCoefficient
    (hp : Nat.Prime p)
    (henc : CompleteEncoding hp)
    (target : Simplex p (p - 2))
    (k : Fin ((p - 2) + 2)) :
    TopFlagSubdivision.deletionCoefficient hp target k =
      codedDeletionCoefficient hp target k := by
  classical
  have hdim : p - 1 = (p - 2) + 1 := by have := hp.two_le; omega
  unfold TopFlagSubdivision.deletionCoefficient codedDeletionCoefficient
  let e2 : Code p ≃ Simplex p ((p - 2) + 1) :=
    (codeEquivSimplex hp henc).trans (Equiv.cast (congrArg (Simplex p) hdim))
  have he2 : ∀ z : Code p,
      e2 z = Equiv.cast (congrArg (Simplex p) hdim) (toSimplex hp z) := fun _ => rfl
  rw [← Equiv.sum_comp e2]
  apply Finset.sum_congr rfl
  intro z _
  have hcond : (e2 z).restrict (FaceMap.delete k)
      = (toSimplex hp z).restrict (deleteFace hp (Fin.cast (faceDimEq hp) k)) := by
    apply Simplex.ext
    intro j
    simp only [Simplex.restrict_apply, FaceMap.delete_apply, he2]
    rw [cast_simplex_apply hdim (toSimplex hp z) (k.succAbove j)]
    have hindex : (Fin.cast (by rw [hdim]) (k.succAbove j) : Fin (p - 1 + 1))
        = (deleteFace hp (Fin.cast (faceDimEq hp) k)).toFun j := by
      apply Fin.ext
      simp only [Fin.val_cast, val_succAbove_eq, deleteFace]
    rw [hindex]
  have hval : (hdim ▸ chain) (e2 z) = ((coefficient z : Int) : ZMod p) := by
    rw [he2, transport_chain_apply hdim chain (toSimplex hp z), chain_apply,
      henc.coefficient_eq]
  unfold SimplicialChain.faceContribution codedFaceTerm
  rw [hcond, hval]

/-- The completed finite source-sum reindexing proves the original rank-two cancellation as soon
as the explicit maximal-flag enumeration is identified with all maximal simplices. -/
theorem rankTwoCancellation_of_completeEncoding
    (henc : ∀ {p : Nat} (hp : Nat.Prime p), CompleteEncoding hp) :
    TopFlagSubdivision.RankTwoCancellationTheorem := by
  intro p hp target k hk
  rw [deletionCoefficient_eq_codedDeletionCoefficient hp (henc hp) target k]
  exact codedDeletionCoefficient_internal_eq_zero hp target k hk

/-- With the terminal theorem already proved, complete encoding yields the full simplicial cycle. -/
theorem topFlagCycle_of_completeEncoding
    (henc : ∀ {p : Nat} (hp : Nat.Prime p), CompleteEncoding hp) :
    ∀ {p : Nat} (hp : Nat.Prime p), TopFlagSubdivision.boundary hp = 0 :=
  TopFlagSubdivision.cycle_of_rankTwo
    (rankTwoCancellation_of_completeEncoding henc)

end MaximalFlagCode
end FoxNeuwirthOrderComplex

namespace AAK

/-- The finite source-sum cancellation step is unconditional at the explicit code level. -/
theorem simplestRoute_codeIndexedInternalCancellation :
    ∀ {p : Nat} (hp : Nat.Prime p)
      (target : FoxNeuwirthOrderComplex.Simplex p (p - 2))
      (k : Fin ((p - 2) + 2)),
      k.1 < p - 1 →
      FoxNeuwirthOrderComplex.MaximalFlagCode.codedDeletionCoefficient hp target k = 0 :=
  fun hp target k hk =>
    FoxNeuwirthOrderComplex.MaximalFlagCode.codedDeletionCoefficient_internal_eq_zero
      hp target k hk

end AAK

end NRR
