/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.Orientation

/-!
# Order complex of the Fox--Neuwirth face relation

This module defines the order complex of the finite barred-permutation face relation.  Instead of trying to glue a family of
closed top-cell simplices by a separate regular-CW construction, it passes to the order complex
of the finite barred-permutation face relation.

A `d`-simplex is a strict chain of `d + 1` barred permutations.  Strictness is measured by a
proper face relation that includes a strict increase of dual dimension.  Consequently the vertices
of a simplex are distinct, relabelling preserves simplices, and every strictly increasing map of
finite ordinals gives a face restriction.  These are the combinatorial data needed for a later
global barycentric realization, where shared subchains are literally shared faces.

The file also defines the global barycentric carrier as nonnegative weights of total mass one
with chain support.  Compactness, simplex charts, the prime action on that carrier, and its
collision-free map into configuration space are the associated geometric constructions.
-/

namespace NRR

variable {p d m l : Nat}

namespace FoxNeuwirthOrderComplex

noncomputable section

/-- Dimension-increasing proper face relation used by the order complex. -/
def ProperFace (a b : BarredPermutation p) : Prop :=
  a.IsFace b ∧ a.dualDimension < b.dualDimension

instance properFaceDecidable (a b : BarredPermutation p) :
    Decidable (ProperFace a b) := Classical.dec _

/-- A proper face is never equal to the cell containing it. -/
theorem ProperFace.ne {a b : BarredPermutation p} (h : ProperFace a b) :
    a ≠ b := by
  intro hab
  subst b
  exact (Nat.lt_irrefl _ h.2)

/-- Proper faces compose. -/
theorem properFace_trans
    {a b c : BarredPermutation p}
    (hab : ProperFace a b) (hbc : ProperFace b c) :
    ProperFace a c :=
  ⟨BarredPermutation.isFace_trans hab.1 hbc.1, lt_trans hab.2 hbc.2⟩

/-- Relabelling preserves and reflects proper faces. -/
theorem properFace_relabel_iff
    (sigma : Equiv.Perm (Fin p)) (a b : BarredPermutation p) :
    ProperFace (a.relabel sigma) (b.relabel sigma) ↔ ProperFace a b := by
  constructor
  · intro h
    exact ⟨
      (BarredPermutation.isFace_relabel_iff sigma a b).1 h.1,
      by simpa using h.2⟩
  · intro h
    exact ⟨
      (BarredPermutation.isFace_relabel_iff sigma a b).2 h.1,
      by simpa using h.2⟩

/-- A `d`-simplex in the order complex is a strict chain of `d + 1` cells. -/
def Simplex (p d : Nat) :=
  {vertex : Fin (d + 1) → BarredPermutation p //
    ∀ ⦃i j : Fin (d + 1)⦄, i < j → ProperFace (vertex i) (vertex j)}

namespace Simplex

noncomputable instance : Fintype (Simplex p d) := by
  classical
  unfold Simplex
  exact Fintype.ofFinite _
noncomputable instance : DecidableEq (Simplex p d) := Classical.decEq _

instance : CoeFun (Simplex p d)
    (fun _ => Fin (d + 1) → BarredPermutation p) :=
  ⟨Subtype.val⟩

@[ext] theorem ext {s t : Simplex p d}
    (h : ∀ i, s i = t i) : s = t := by
  apply Subtype.ext
  funext i
  exact h i

/-- The defining chain relation, exposed as a theorem. -/
theorem properFace (s : Simplex p d)
    {i j : Fin (d + 1)} (hij : i < j) :
    ProperFace (s i) (s j) :=
  s.2 hij

/-- Vertices in a strict chain are pairwise distinct. -/
theorem vertex_injective (s : Simplex p d) :
    Function.Injective s := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (s.properFace hlt).ne hij
  · exact (s.properFace hgt).ne hij.symm

/-- Every barred permutation gives a vertex of the order complex. -/
def ofCell (c : BarredPermutation p) : Simplex p 0 :=
  ⟨fun _ => c, by
    intro i j hij
    omega⟩

@[simp] theorem ofCell_apply (c : BarredPermutation p) (i : Fin 1) :
    ofCell c i = c :=
  rfl

/-- Relabel every vertex in a simplex. -/
def relabel (sigma : Equiv.Perm (Fin p))
    (s : Simplex p d) : Simplex p d :=
  ⟨fun i => (s i).relabel sigma, by
    intro i j hij
    exact (properFace_relabel_iff sigma (s i) (s j)).2 (s.properFace hij)⟩

@[simp] theorem relabel_apply
    (sigma : Equiv.Perm (Fin p)) (s : Simplex p d) (i : Fin (d + 1)) :
    relabel sigma s i = (s i).relabel sigma :=
  rfl

@[simp] theorem relabel_one (s : Simplex p d) :
    relabel 1 s = s := by
  apply Simplex.ext
  intro i
  exact BarredPermutation.relabel_one (s i)

/-- Relabelling is a left action with the convention already used on configurations. -/
theorem relabel_mul
    (sigma tau : Equiv.Perm (Fin p)) (s : Simplex p d) :
    relabel (sigma * tau) s = relabel sigma (relabel tau s) := by
  apply Simplex.ext
  intro i
  exact BarredPermutation.relabel_mul sigma tau (s i)

instance primeSymmetryAction (hp : Nat.Prime p) :
    MulAction (PrimeSymmetry hp) (Simplex p d) where
  smul g s := relabel (PrimeSymmetry.toPerm hp g) s
  one_smul s := by
    change relabel (PrimeSymmetry.toPerm hp 1) s = s
    rw [map_one, relabel_one]
  mul_smul g h s := by
    exact relabel_mul (PrimeSymmetry.toPerm hp g)
      (PrimeSymmetry.toPerm hp h) s

@[simp] theorem prime_smul_apply
    (hp : Nat.Prime p) (g : PrimeSymmetry hp)
    (s : Simplex p d) (i : Fin (d + 1)) :
    (g • s) i = g • (s i) :=
  rfl

/-- Finite vertex support of an order-complex simplex. -/
def support (s : Simplex p d) : Finset (BarredPermutation p) :=
  Finset.univ.image s

@[simp] theorem mem_support_iff
    (s : Simplex p d) (c : BarredPermutation p) :
    c ∈ s.support ↔ ∃ i, s i = c := by
  simp [support]

/-- Every order-complex simplex has nonempty support. -/
theorem support_nonempty (s : Simplex p d) :
    s.support.Nonempty := by
  refine ⟨s 0, ?_⟩
  simp [support]

end Simplex

/-- A barycentric weight has chain support when every two distinct nonzero coordinates are
comparable by the proper-face relation. -/
def ChainSupported (weight : BarredPermutation p → ℝ) : Prop :=
  ∀ ⦃a b : BarredPermutation p⦄,
    weight a ≠ 0 → weight b ≠ 0 → a ≠ b →
      ProperFace a b ∨ ProperFace b a

/-- Global barycentric carrier of the order complex.

Using coordinates indexed by all barred permutations identifies shared faces automatically: a
point belongs to a simplex precisely when its nonzero coordinate support is contained in the
corresponding strict chain. -/
def Realization (p : Nat) :=
  {weight : BarredPermutation p → ℝ //
    (∀ c, 0 ≤ weight c) ∧
    (∑ c, weight c = 1) ∧
    ChainSupported weight}

namespace Realization

instance : CoeFun (Realization p) (fun _ => BarredPermutation p → ℝ) :=
  ⟨Subtype.val⟩

@[ext] theorem ext {x y : Realization p}
    (h : ∀ c, x c = y c) : x = y := by
  apply Subtype.ext
  funext c
  exact h c

/-- Every barycentric coordinate is nonnegative. -/
theorem nonneg (x : Realization p) (c : BarredPermutation p) :
    0 ≤ x c :=
  x.2.1 c

/-- Barycentric coordinates sum to one. -/
theorem sum_eq_one (x : Realization p) :
    ∑ c, x c = 1 :=
  x.2.2.1

/-- The nonzero coordinates form a chain. -/
theorem chainSupported (x : Realization p) :
    ChainSupported x :=
  x.2.2.2

/-- Finite nonzero coordinate support of a realization point. -/
def support (x : Realization p) : Finset (BarredPermutation p) :=
  Finset.univ.filter fun c => x c ≠ 0

@[simp] theorem mem_support_iff
    (x : Realization p) (c : BarredPermutation p) :
    c ∈ x.support ↔ x c ≠ 0 := by
  simp [support]

/-- Coordinate vector of a vertex. -/
def vertexWeight (c : BarredPermutation p) :
    BarredPermutation p → ℝ :=
  fun d => if d = c then 1 else 0

/-- Every barred permutation is a vertex of the global realization. -/
def vertex (c : BarredPermutation p) : Realization p :=
  ⟨vertexWeight c, by
    refine ⟨?_, ?_, ?_⟩
    · intro d
      by_cases h : d = c
      · simp [vertexWeight, h]
      · simp [vertexWeight, h]
    · simp [vertexWeight]
    · intro a b ha hb hab
      have hac : a = c := by
        by_contra h
        simp [vertexWeight, h] at ha
      have hbc : b = c := by
        by_contra h
        simp [vertexWeight, h] at hb
      exact (hab (hac.trans hbc.symm)).elim⟩

@[simp] theorem vertex_apply
    (c d : BarredPermutation p) :
    vertex c d = if d = c then 1 else 0 :=
  rfl

@[simp] theorem vertex_self (c : BarredPermutation p) :
    vertex c c = 1 := by
  simp [vertex_apply]

@[simp] theorem vertex_apply_of_ne
    {c d : BarredPermutation p} (h : d ≠ c) :
    vertex c d = 0 := by
  simp [vertex_apply, h]

/-- The support of a vertex is the singleton containing that cell. -/
theorem support_vertex (c : BarredPermutation p) :
    (vertex c).support = {c} := by
  ext d
  by_cases h : d = c
  · subst d
    simp [support, vertex_apply]
  · simp [support, vertex_apply, h]

end Realization

/-- A strictly increasing finite-ordinal map selects a face of an order-complex simplex. -/
structure FaceMap (m d : Nat) where
  toFun : Fin (m + 1) → Fin (d + 1)
  strictMono : StrictMono toFun

namespace FaceMap

instance : CoeFun (FaceMap m d) (fun _ => Fin (m + 1) → Fin (d + 1)) :=
  ⟨FaceMap.toFun⟩

/-- Identity face map. -/
def id (d : Nat) : FaceMap d d where
  toFun := fun i => i
  strictMono := by
    intro i j hij
    exact hij

/-- Composition of face maps. -/
def comp (f : FaceMap m d) (g : FaceMap l m) : FaceMap l d where
  toFun := fun i => f (g i)
  strictMono := by
    intro i j hij
    exact f.strictMono (g.strictMono hij)

@[simp] theorem id_apply (i : Fin (d + 1)) :
    id d i = i :=
  rfl

@[simp] theorem comp_apply
    (f : FaceMap m d) (g : FaceMap l m) (i : Fin (l + 1)) :
    f.comp g i = f (g i) :=
  rfl

end FaceMap

namespace Simplex

/-- Restrict a simplex along an increasing vertex map.  This is the abstract face operation. -/
def restrict (s : Simplex p d) (f : FaceMap m d) : Simplex p m :=
  ⟨fun i => s (f i), by
    intro i j hij
    exact s.properFace (f.strictMono hij)⟩

@[simp] theorem restrict_apply
    (s : Simplex p d) (f : FaceMap m d) (i : Fin (m + 1)) :
    s.restrict f i = s (f i) :=
  rfl

@[simp] theorem restrict_id (s : Simplex p d) :
    s.restrict (FaceMap.id d) = s := by
  apply Simplex.ext
  intro i
  rfl

@[simp] theorem restrict_comp
    (s : Simplex p d) (f : FaceMap m d) (g : FaceMap l m) :
    (s.restrict f).restrict g = s.restrict (f.comp g) := by
  apply Simplex.ext
  intro i
  rfl

/-- Relabelling commutes with taking abstract faces. -/
theorem relabel_restrict
    (sigma : Equiv.Perm (Fin p))
    (s : Simplex p d) (f : FaceMap m d) :
    (s.restrict f).relabel sigma = (s.relabel sigma).restrict f := by
  apply Simplex.ext
  intro i
  rfl

/-- The support of an abstract face is contained in the support of the ambient simplex. -/
theorem support_restrict_subset
    (s : Simplex p d) (f : FaceMap m d) :
    (s.restrict f).support ⊆ s.support := by
  intro c hc
  rcases (mem_support_iff (s.restrict f) c).1 hc with ⟨i, hi⟩
  exact (mem_support_iff s c).2 ⟨f i, hi⟩

end Simplex

/-- The order complex has a finite simplex type in every
fixed dimension. -/
theorem simplex_finite (p d : Nat) :
    Finite (Simplex p d) :=
  inferInstance

/-- The order complex is nonempty in dimension zero: every cell supplies a zero-simplex. -/
theorem zeroSimplex_nonempty (p : Nat) :
    Nonempty (Simplex p 0) := by
  exact ⟨Simplex.ofCell ⟨1, ∅⟩⟩

end

end FoxNeuwirthOrderComplex

end NRR
