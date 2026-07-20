/-
Copyright (c) 2026 André Hernandez-Espiet, Vladimir Sedlacek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: André Hernandez-Espiet, Vladimir Sedlacek
-/
import LeanPool.SyntheticEuclid4.Axioms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra

/-!
Symmetry lemmas for the permutation tactics. These rewrite the geometric
primitives (`area`, `colinear`, `triangle`, `length`, `angle`, `SameSide`,
`diffside`, `para`) under permutations of their point arguments, and serve as
the building blocks for the `perm`/`perma`/`linperm` tactics defined in
`PermTactics`.
-/

namespace SyntheticEuclid4

open IncidenceGeometry

variable [i : IncidenceGeometry] {a b c : Point}

lemma ar132 : area a b c = area a c b := (area_invariant a b c).2

lemma ar312 : area a b c = area c a b := (area_invariant a b c).1

lemma ar231 : area a b c = area b c a :=
  by rw [(area_invariant a b c).1, (area_invariant c a b).1]

lemma ar213 : area a b c = area b a c :=
  by rw [(area_invariant a b c).2, (area_invariant a c b).1]

lemma ar321 : area a b c = area c b a :=
  by rw [(area_invariant a b c).2, (area_invariant c b a).1]

lemma col213 : colinear a b c ↔ colinear b a c :=
  exists_congr fun _ => and_left_comm

lemma col231 : colinear a b c ↔ colinear b c a :=
  exists_congr fun _ => and_rotate

lemma col132 : colinear a b c ↔ colinear a c b := by conv => rhs; rw [col213]; rw [col231]

lemma col312 : colinear a b c ↔ colinear c a b := by conv => lhs; rw [← col231]

lemma col321 : colinear a b c ↔ colinear c b a := by conv => rhs; rw [col231]; rw [col213]

lemma tr132 : triangle a b c ↔ triangle a c b := by
  constructor; all_goals dsimp [triangle]; rw [col132]; tauto

lemma tr213 : triangle a b c ↔ triangle b a c := by
  constructor; all_goals dsimp [triangle]; rw [col213]; tauto

lemma tr231 : triangle a b c ↔ triangle b c a := by
  constructor
  · dsimp [triangle]; rw [col231]; tauto
  · dsimp [triangle]; rw [← col231]; tauto

lemma tr312 : triangle a b c ↔ triangle c a b := by
  constructor
  · dsimp [triangle]; rw [col312]; tauto
  · dsimp [triangle]; rw [← col312]; tauto

lemma tr321 : triangle a b c ↔ triangle c b a := by
  constructor; all_goals dsimp [triangle]; rw [col321]; tauto

lemma ss21 {a b : Point} {L : Line} : SameSide a b L ↔ SameSide b a L :=
  ⟨sameside_symm, sameside_symm⟩

lemma ds21 {a b : Point} {L : Line} : diffside a b L ↔ diffside b a L :=
  ⟨fun ⟨naL, nbL, nss⟩ => ⟨nbL, naL, fun h => nss (sameside_symm h)⟩,
   fun ⟨naL, nbL, nss⟩ => ⟨nbL, naL, fun h => nss (sameside_symm h)⟩⟩

lemma para21 {L M : Line} : para L M ↔ para M L :=
  ⟨fun p e => (p e).symm, fun p e => (p e).symm⟩

end SyntheticEuclid4
