/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.ScalarExtension
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CenteredLift

/-!
# Adding slab coordinates to a flag fibre

The completeness refinement augments a fibre by finitely many affine
functionals. These coordinate maps project to the old fibre, retain the
additional coordinates along lower transitions, and commute with scalar
extension and reduction modulo every modulus.
-/

namespace EGZ

namespace Coord

variable {R : Type*} [CommRing R]

/-- Linear projection onto the first block of coordinates. -/
def first (m k : ℕ) : (Fin (m + k) → R) →ₗ[R] (Fin m → R) :=
  LinearMap.pi fun i ↦ LinearMap.proj (Fin.castAdd k i)

/-- Linear projection onto the last block of coordinates. -/
def last (m k : ℕ) : (Fin (m + k) → R) →ₗ[R] (Fin k → R) :=
  LinearMap.pi fun i ↦ LinearMap.proj (Fin.natAdd m i)

@[simp]
theorem first_apply {m k : ℕ} (q : Fin (m + k) → R) (i : Fin m) :
    first m k q i = q (Fin.castAdd k i) := rfl

@[simp]
theorem last_apply {m k : ℕ} (q : Fin (m + k) → R) (i : Fin k) :
    last m k q i = q (Fin.natAdd m i) := rfl

section Append

variable {V : Type*} [AddCommGroup V] [Module R V]

/-- Append the outputs of two affine maps in the standard finite coordinates. -/
def append {m k : ℕ} (A : V →ᵃ[R] (Fin m → R)) (B : V →ᵃ[R] (Fin k → R)) :
    V →ᵃ[R] (Fin (m + k) → R) :=
  AffineMap.pi (Fin.addCases
    (fun i ↦ (AffineMap.proj i).comp A) (fun i ↦ (AffineMap.proj i).comp B))

@[simp]
theorem append_castAdd {m k : ℕ} (A : V →ᵃ[R] (Fin m → R))
    (B : V →ᵃ[R] (Fin k → R)) (v : V) (i : Fin m) :
    append A B v (Fin.castAdd k i) = A v i := by
  simp [append]

@[simp]
theorem append_natAdd {m k : ℕ} (A : V →ᵃ[R] (Fin m → R))
    (B : V →ᵃ[R] (Fin k → R)) (v : V) (i : Fin k) :
    append A B v (Fin.natAdd m i) = B v i := by
  simp [append]

@[simp]
theorem first_append {m k : ℕ} (A : V →ᵃ[R] (Fin m → R))
    (B : V →ᵃ[R] (Fin k → R)) (v : V) : first m k (append A B v) = A v := by
  ext i
  simp

@[simp]
theorem last_append {m k : ℕ} (A : V →ᵃ[R] (Fin m → R))
    (B : V →ᵃ[R] (Fin k → R)) (v : V) : last m k (append A B v) = B v := by
  ext i
  simp

end Append

/-- Extend an affine map while leaving additional coordinates fixed. -/
def extend {m n : ℕ} (A : (Fin m → R) →ᵃ[R] (Fin n → R)) (k : ℕ) :
    (Fin (m + k) → R) →ᵃ[R] (Fin (n + k) → R) :=
  append (A.comp (first m k).toAffineMap) (last m k).toAffineMap

@[simp]
theorem first_extend {m n k : ℕ} (A : (Fin m → R) →ᵃ[R] (Fin n → R))
    (q : Fin (m + k) → R) : first n k (extend A k q) = A (first m k q) := by
  simp [extend]

@[simp]
theorem last_extend {m n k : ℕ} (A : (Fin m → R) →ᵃ[R] (Fin n → R))
    (q : Fin (m + k) → R) : last n k (extend A k q) = last m k q := by
  simp [extend]

theorem ext_first_last {m k : ℕ} {q r : Fin (m + k) → R}
    (hfirst : first m k q = first m k r) (hlast : last m k q = last m k r) : q = r := by
  funext i
  refine Fin.addCases (fun i ↦ congrFun hfirst i) (fun i ↦ congrFun hlast i) i

theorem extend_id (m k : ℕ) :
    extend (AffineMap.id R (Fin m → R)) k = AffineMap.id R _ := by
  ext q i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp [extend]

theorem extend_comp {l m n : ℕ} (A : (Fin m → R) →ᵃ[R] (Fin n → R))
    (B : (Fin l → R) →ᵃ[R] (Fin m → R)) (k : ℕ) :
    extend (A.comp B) k = (extend A k).comp (extend B k) := by
  apply AffineMap.ext
  intro q
  apply ext_first_last <;> simp

end Coord

namespace IntegralAffineMap

/-- Forget the extra coordinates of an augmented lattice fibre. -/
def first (m k : ℕ) : IntegralAffineMap (m + k) m where
  real := (Coord.first m k).toAffineMap
  integer := Coord.first m k
  modp _ := (Coord.first m k).toAffineMap
  real_integer _ := rfl
  mod_integer _ _ := rfl

/-- Apply an old transition and keep the newly added slab coordinates. -/
noncomputable def extend {m n : ℕ} (A : IntegralAffineMap m n) (k : ℕ) :
    IntegralAffineMap (m + k) (n + k) where
  real := Coord.extend A.real k
  integer := Coord.extend A.toIntAffineMap k
  modp p := Coord.extend (A.modp p) k
  real_integer q := by
    apply Coord.ext_first_last
    · change Coord.first n k (Coord.extend A.real k q.real) =
        Coord.first n k (IntCoord.real (Coord.extend A.toIntAffineMap k q))
      rw [Coord.first_extend]
      change A.real (IntCoord.real (Coord.first m k q)) =
        IntCoord.real (Coord.first n k (Coord.extend A.toIntAffineMap k q))
      rw [Coord.first_extend]
      exact A.real_integer _
    · change Coord.last n k (Coord.extend A.real k q.real) =
        Coord.last n k (IntCoord.real (Coord.extend A.toIntAffineMap k q))
      rw [Coord.last_extend]
      change IntCoord.real (Coord.last m k q) =
        IntCoord.real (Coord.last n k (Coord.extend A.toIntAffineMap k q))
      rw [Coord.last_extend]
  mod_integer p q := by
    apply Coord.ext_first_last
    · change Coord.first n k (Coord.extend (A.modp p) k (q.mod p)) =
        Coord.first n k (IntCoord.mod p (Coord.extend A.toIntAffineMap k q))
      rw [Coord.first_extend]
      change A.modp p (IntCoord.mod p (Coord.first m k q)) =
        IntCoord.mod p (Coord.first n k (Coord.extend A.toIntAffineMap k q))
      rw [Coord.first_extend]
      exact A.mod_integer _ _
    · change Coord.last n k (Coord.extend (A.modp p) k (q.mod p)) =
        Coord.last n k (IntCoord.mod p (Coord.extend A.toIntAffineMap k q))
      rw [Coord.last_extend]
      change IntCoord.mod p (Coord.last m k q) =
        IntCoord.mod p (Coord.last n k (Coord.extend A.toIntAffineMap k q))
      rw [Coord.last_extend]

theorem first_comp_extend {m n : ℕ} (A : IntegralAffineMap m n) (k : ℕ) :
    (first n k).comp (A.extend k) = A.comp (first m k) := by
  apply ext_integer
  funext q
  exact Coord.first_extend A.toIntAffineMap q

theorem extend_id (m k : ℕ) : (id m).extend k = id (m + k) := by
  apply ext_integer
  funext q
  change Coord.extend (id m).toIntAffineMap k q = q
  rw [toIntAffineMap_id, Coord.extend_id]
  rfl

theorem extend_comp {l m n : ℕ} (A : IntegralAffineMap m n)
    (B : IntegralAffineMap l m) (k : ℕ) :
    (A.comp B).extend k = (A.extend k).comp (B.extend k) := by
  apply ext_integer
  funext q
  change Coord.extend (A.comp B).toIntAffineMap k q =
    Coord.extend A.toIntAffineMap k (Coord.extend B.toIntAffineMap k q)
  rw [toIntAffineMap_comp, Coord.extend_comp]
  rfl

end IntegralAffineMap

theorem latticeSupNorm_le_of_first_last {m k B : ℕ} (q : IntCoord (m + k))
    (hfirst : latticeSupNorm (Coord.first m k q) ≤ B)
    (hlast : latticeSupNorm (Coord.last m k q) ≤ B) : latticeSupNorm q ≤ B := by
  apply Finset.sup_le
  intro i _
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · exact (Finset.le_sup (f := fun i ↦ ((Coord.first m k q) i).natAbs)
      (Finset.mem_univ j)).trans hfirst
  · exact (Finset.le_sup (f := fun i ↦ ((Coord.last m k q) i).natAbs)
      (Finset.mem_univ j)).trans hlast

end EGZ

namespace EGZ.Coord

variable {R : Type*} [CommRing R]

/-- Keep the initial coordinates of a finite coordinate vector. -/
def prefixMap (es et : ℕ) (h : et ≤ es) : (Fin es → R) →ₗ[R] (Fin et → R) :=
  LinearMap.pi fun i ↦ LinearMap.proj (Fin.castLE h i)

@[simp]
theorem prefixMap_apply {es et : ℕ} (h : et ≤ es) (q : Fin es → R) (i : Fin et) :
    prefixMap es et h q i = q (Fin.castLE h i) := rfl

@[simp]
theorem prefixMap_refl (e : ℕ) (q : Fin e → R) : prefixMap e e le_rfl q = q := by
  ext i
  rfl

@[simp]
theorem prefixMap_comp {es em et : ℕ} (hm : em ≤ es) (ht : et ≤ em) (q : Fin es → R) :
    prefixMap em et ht (prefixMap es em hm q) = prefixMap es et (ht.trans hm) q := rfl

/-- Apply an affine map to the old coordinates and keep an initial segment
of the additional coordinates. -/
def extendPrefix {m n : ℕ} (A : (Fin m → R) →ᵃ[R] (Fin n → R))
    (es et : ℕ) (h : et ≤ es) : (Fin (m + es) → R) →ᵃ[R] (Fin (n + et) → R) :=
  append (A.comp (first m es).toAffineMap)
    ((prefixMap es et h).toAffineMap.comp (last m es).toAffineMap)

@[simp]
theorem first_extendPrefix {m n es et : ℕ} (A : (Fin m → R) →ᵃ[R] (Fin n → R))
    (h : et ≤ es) (q : Fin (m + es) → R) :
    first n et (extendPrefix A es et h q) = A (first m es q) := by simp [extendPrefix]

@[simp]
theorem last_extendPrefix {m n es et : ℕ} (A : (Fin m → R) →ᵃ[R] (Fin n → R))
    (h : et ≤ es) (q : Fin (m + es) → R) :
    last n et (extendPrefix A es et h q) = prefixMap es et h (last m es q) := by
  simp [extendPrefix]

theorem extendPrefix_id (m e : ℕ) :
    extendPrefix (AffineMap.id R (Fin m → R)) e e le_rfl = AffineMap.id R _ := by
  apply AffineMap.ext
  intro q
  apply ext_first_last <;> simp

theorem extendPrefix_comp {l m n es em et : ℕ}
    (A : (Fin m → R) →ᵃ[R] (Fin n → R)) (B : (Fin l → R) →ᵃ[R] (Fin m → R))
    (hm : em ≤ es) (ht : et ≤ em) :
    extendPrefix (A.comp B) es et (ht.trans hm) =
      (extendPrefix A em et ht).comp (extendPrefix B es em hm) := by
  apply AffineMap.ext
  intro q
  apply ext_first_last <;> simp

end EGZ.Coord

namespace EGZ.IntegralAffineMap

/-- Extend an integral-affine map while retaining an initial segment of its
additional coordinates. -/
noncomputable def extendPrefix {m n : ℕ} (A : IntegralAffineMap m n)
    (es et : ℕ) (h : et ≤ es) : IntegralAffineMap (m + es) (n + et) where
  real := Coord.extendPrefix A.real es et h
  integer := Coord.extendPrefix A.toIntAffineMap es et h
  modp p := Coord.extendPrefix (A.modp p) es et h
  real_integer q := by
    apply Coord.ext_first_last
    · change Coord.first n et (Coord.extendPrefix A.real es et h q.real) =
        Coord.first n et (IntCoord.real (Coord.extendPrefix A.toIntAffineMap es et h q))
      rw [Coord.first_extendPrefix]
      change A.real (IntCoord.real (Coord.first m es q)) =
        IntCoord.real (Coord.first n et (Coord.extendPrefix A.toIntAffineMap es et h q))
      rw [Coord.first_extendPrefix]
      exact A.real_integer _
    · change Coord.last n et (Coord.extendPrefix A.real es et h q.real) =
        Coord.last n et (IntCoord.real (Coord.extendPrefix A.toIntAffineMap es et h q))
      rw [Coord.last_extendPrefix]
      change IntCoord.real (Coord.prefixMap es et h (Coord.last m es q)) =
        IntCoord.real (Coord.last n et (Coord.extendPrefix A.toIntAffineMap es et h q))
      rw [Coord.last_extendPrefix]
  mod_integer p q := by
    apply Coord.ext_first_last
    · change Coord.first n et (Coord.extendPrefix (A.modp p) es et h (q.mod p)) =
        Coord.first n et (IntCoord.mod p (Coord.extendPrefix A.toIntAffineMap es et h q))
      rw [Coord.first_extendPrefix]
      change A.modp p (IntCoord.mod p (Coord.first m es q)) =
        IntCoord.mod p (Coord.first n et (Coord.extendPrefix A.toIntAffineMap es et h q))
      rw [Coord.first_extendPrefix]
      exact A.mod_integer _ _
    · change Coord.last n et (Coord.extendPrefix (A.modp p) es et h (q.mod p)) =
        Coord.last n et (IntCoord.mod p (Coord.extendPrefix A.toIntAffineMap es et h q))
      rw [Coord.last_extendPrefix]
      change IntCoord.mod p (Coord.prefixMap es et h (Coord.last m es q)) =
        IntCoord.mod p (Coord.last n et (Coord.extendPrefix A.toIntAffineMap es et h q))
      rw [Coord.last_extendPrefix]

theorem first_comp_extendPrefix {m n : ℕ} (A : IntegralAffineMap m n)
    (es et : ℕ) (h : et ≤ es) :
    (first n et).comp (A.extendPrefix es et h) = A.comp (first m es) := by
  apply ext_integer
  funext q
  exact Coord.first_extendPrefix A.toIntAffineMap h q

theorem extendPrefix_id (m e : ℕ) : (id m).extendPrefix e e le_rfl = id (m + e) := by
  apply ext_integer
  funext q
  change Coord.extendPrefix (id m).toIntAffineMap e e le_rfl q = q
  rw [toIntAffineMap_id, Coord.extendPrefix_id]
  rfl

theorem extendPrefix_comp {l m n es em et : ℕ} (A : IntegralAffineMap m n)
    (B : IntegralAffineMap l m) (hm : em ≤ es) (ht : et ≤ em) :
    (A.comp B).extendPrefix es et (ht.trans hm) =
      (A.extendPrefix em et ht).comp (B.extendPrefix es em hm) := by
  apply ext_integer
  funext q
  change Coord.extendPrefix (A.comp B).toIntAffineMap es et (ht.trans hm) q =
    Coord.extendPrefix A.toIntAffineMap em et ht (Coord.extendPrefix B.toIntAffineMap es em hm q)
  rw [toIntAffineMap_comp, Coord.extendPrefix_comp _ _ hm ht]
  rfl

end EGZ.IntegralAffineMap
