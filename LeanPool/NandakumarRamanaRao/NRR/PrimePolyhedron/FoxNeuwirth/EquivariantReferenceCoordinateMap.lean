/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ReferenceAffineOrbitCount
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.AffinePrismObstruction
/-!
# Equivariant full-coordinate lift of the S5 reference map

The fixed-last-coordinate lift is convenient for calculations but obscures equivariance.  Here the
reference map is lifted before choosing difference coordinates: non-top cells use all block
indices, while top cells use the full triangular rank vector.  Taking differences against the last
label recovers exactly the S5 map.  Relabelling acts by the same coordinate permutation, so this
lift is genuinely prime-equivariant.
-/

namespace NRR
namespace AAK

open scoped BigOperators
open FoxNeuwirthOrderComplex

variable {p : Nat}

/-- Equivariant full-coordinate lift of the S5 affine reference map. -/
noncomputable def equivariantReferenceCoordinateMap
    (hp : Nat.Prime p) : CoordinateAffineVertexMap p where
  vertexValue c i :=
    if c.IsTop then
      -ReferenceAffineOrbitCount.epsilon hp *
        (ReferenceAffineOrbitCount.triangular (c.rank i).1 : Real)
    else
      (c.blockIndex i : Real)

/-- Its fixed difference-coordinate map is the S5 reference map. -/
theorem equivariantReferenceCoordinateMap_deviation
    (hp : Nat.Prime p) :
    (equivariantReferenceCoordinateMap hp).deviation hp =
      ReferenceAffineOrbitCount.referenceMap hp := by
  apply congrArg (fun vertexValue : BarredPermutation p → Fin (p - 1) → ℝ =>
    ({ vertexValue := vertexValue } : AffineVertexMap p (p - 1)))
  funext c r
  by_cases htop : c.IsTop
  · simp [equivariantReferenceCoordinateMap,
      ReferenceAffineOrbitCount.topDirection, htop]
    ring
  · simp [equivariantReferenceCoordinateMap,
      ReferenceAffineOrbitCount.blockDifference, htop]

/-- Vertex data transform by coordinate relabelling. -/
theorem equivariantReferenceCoordinateMap_vertex_smul
    (hp : Nat.Prime p) (g : PrimeSymmetry p)
    (c : BarredPermutation p) (i : Fin p) :
    (equivariantReferenceCoordinateMap hp).vertexValue (g • c) i =
      (equivariantReferenceCoordinateMap hp).vertexValue c
        ((PrimeSymmetry.toPerm p g).symm i) := by
  simp [equivariantReferenceCoordinateMap, BarredPermutation.IsTop]

/-- The global full-coordinate reference map is prime-equivariant. -/
theorem equivariantReferenceCoordinateMap_global_smul
    (hp : Nat.Prime p) (g : PrimeSymmetry p) (x : Realization p) :
    (equivariantReferenceCoordinateMap hp).globalValue (g • x) =
      g • (equivariantReferenceCoordinateMap hp).globalValue x := by
  classical
  funext i
  change
    (equivariantReferenceCoordinateMap hp).globalValue (g • x) i =
      (equivariantReferenceCoordinateMap hp).globalValue x
        ((PrimeSymmetry.toPerm p g).symm i)
  unfold CoordinateAffineVertexMap.globalValue
  have hvertex : ∀ c : BarredPermutation p,
      (equivariantReferenceCoordinateMap hp).vertexValue
          (BarredPermutation.relabel (PrimeSymmetry.toPerm p g) c) i =
        (equivariantReferenceCoordinateMap hp).vertexValue c
          ((PrimeSymmetry.toPerm p g).symm i) := by
    intro c
    simpa [BarredPermutation.prime_smul_def] using
      equivariantReferenceCoordinateMap_vertex_smul hp g c i
  change (∑ c, x (BarredPermutation.relabel
      (PrimeSymmetry.toPerm p g).symm c) *
      (equivariantReferenceCoordinateMap hp).vertexValue c i) = _
  calc
    (∑ c, x (BarredPermutation.relabel
          (PrimeSymmetry.toPerm p g).symm c) *
        (equivariantReferenceCoordinateMap hp).vertexValue c i) =
        ∑ c, x c * (equivariantReferenceCoordinateMap hp).vertexValue
          (BarredPermutation.relabel (PrimeSymmetry.toPerm p g) c) i := by
      simpa using
        (relabelEquiv (PrimeSymmetry.toPerm p g).symm).sum_comp
          (fun c => x c *
            (equivariantReferenceCoordinateMap hp).vertexValue
              (BarredPermutation.relabel (PrimeSymmetry.toPerm p g) c) i)
    _ = ∑ c, x c * (equivariantReferenceCoordinateMap hp).vertexValue c
          ((PrimeSymmetry.toPerm p g).symm i) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [hvertex c]

/-- A finite uniform vertex bound for the equivariant lift. -/
noncomputable def equivariantReferenceAbsBound (hp : Nat.Prime p) : Real :=
  1 + ∑ c : BarredPermutation p,
    ∑ i : Fin p, |(equivariantReferenceCoordinateMap hp).vertexValue c i|

 theorem equivariantReferenceAbsBound_pos (hp : Nat.Prime p) :
    0 < equivariantReferenceAbsBound hp := by
  unfold equivariantReferenceAbsBound
  positivity

 theorem equivariantReference_vertex_lt_bound
    (hp : Nat.Prime p) (c : BarredPermutation p) (i : Fin p) :
    |(equivariantReferenceCoordinateMap hp).vertexValue c i| <
      equivariantReferenceAbsBound hp := by
  unfold equivariantReferenceAbsBound
  have hinner : |(equivariantReferenceCoordinateMap hp).vertexValue c i| ≤
      ∑ i' : Fin p, |(equivariantReferenceCoordinateMap hp).vertexValue c i'| := by
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun i' : Fin p =>
        |(equivariantReferenceCoordinateMap hp).vertexValue c i'|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have houter :
      (∑ i' : Fin p, |(equivariantReferenceCoordinateMap hp).vertexValue c i'|) ≤
        ∑ c' : BarredPermutation p,
          ∑ i' : Fin p,
            |(equivariantReferenceCoordinateMap hp).vertexValue c' i'| := by
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun c' : BarredPermutation p =>
        ∑ i' : Fin p,
          |(equivariantReferenceCoordinateMap hp).vertexValue c' i'|)
      (fun c' _ => Finset.sum_nonneg fun j _ => abs_nonneg _)
      (Finset.mem_univ c)
  have hle := hinner.trans houter
  linarith

/-- Globally positive equivariant reference lift. -/
noncomputable def positiveEquivariantReferenceCoordinateMap
    (hp : Nat.Prime p) : CoordinateAffineVertexMap p where
  vertexValue c i :=
    (equivariantReferenceCoordinateMap hp).vertexValue c i +
      equivariantReferenceAbsBound hp

/-- Globally negative equivariant reference lift. -/
noncomputable def negativeEquivariantReferenceCoordinateMap
    (hp : Nat.Prime p) : CoordinateAffineVertexMap p where
  vertexValue c i :=
    (equivariantReferenceCoordinateMap hp).vertexValue c i -
      equivariantReferenceAbsBound hp

 theorem positiveEquivariantReferenceCoordinateMap_vertex_pos
    (hp : Nat.Prime p) :
    ∀ c i, 0 < (positiveEquivariantReferenceCoordinateMap hp).vertexValue c i := by
  intro c i
  have h := equivariantReference_vertex_lt_bound hp c i
  unfold positiveEquivariantReferenceCoordinateMap
  linarith [(abs_lt.mp h).1]

 theorem negativeEquivariantReferenceCoordinateMap_vertex_neg
    (hp : Nat.Prime p) :
    ∀ c i, (negativeEquivariantReferenceCoordinateMap hp).vertexValue c i < 0 := by
  intro c i
  have h := equivariantReference_vertex_lt_bound hp c i
  exact sub_neg.mpr (lt_of_le_of_lt (le_abs_self _) h)

 theorem positiveEquivariantReferenceCoordinateMap_deviation
    (hp : Nat.Prime p) :
    (positiveEquivariantReferenceCoordinateMap hp).deviation hp =
      ReferenceAffineOrbitCount.referenceMap hp := by
  rw [← equivariantReferenceCoordinateMap_deviation hp]
  apply congrArg (fun vertexValue : BarredPermutation p → Fin (p - 1) → ℝ =>
    ({ vertexValue := vertexValue } : AffineVertexMap p (p - 1)))
  funext c r
  simp [positiveEquivariantReferenceCoordinateMap]

 theorem negativeEquivariantReferenceCoordinateMap_deviation
    (hp : Nat.Prime p) :
    (negativeEquivariantReferenceCoordinateMap hp).deviation hp =
      ReferenceAffineOrbitCount.referenceMap hp := by
  rw [← equivariantReferenceCoordinateMap_deviation hp]
  apply congrArg (fun vertexValue : BarredPermutation p → Fin (p - 1) → ℝ =>
    ({ vertexValue := vertexValue } : AffineVertexMap p (p - 1)))
  funext c r
  simp [negativeEquivariantReferenceCoordinateMap]

 theorem positiveEquivariantReferenceCoordinateMap_global_smul
    (hp : Nat.Prime p) (g : PrimeSymmetry p) (x : Realization p) :
    (positiveEquivariantReferenceCoordinateMap hp).globalValue (g • x) =
      g • (positiveEquivariantReferenceCoordinateMap hp).globalValue x := by
  funext i
  change
    (positiveEquivariantReferenceCoordinateMap hp).globalValue (g • x) i =
      (positiveEquivariantReferenceCoordinateMap hp).globalValue x
        ((PrimeSymmetry.toPerm p g).symm i)
  have hshift : ∀ (z : Realization p) (j : Fin p),
      (positiveEquivariantReferenceCoordinateMap hp).globalValue z j =
        (equivariantReferenceCoordinateMap hp).globalValue z j +
          equivariantReferenceAbsBound hp := by
    intro z j
    unfold CoordinateAffineVertexMap.globalValue
    simp only [positiveEquivariantReferenceCoordinateMap, mul_add,
      Finset.sum_add_distrib]
    rw [show (∑ c : BarredPermutation p, z c * equivariantReferenceAbsBound hp) =
        equivariantReferenceAbsBound hp by
      calc
        (∑ c : BarredPermutation p, z c * equivariantReferenceAbsBound hp) =
            (∑ c : BarredPermutation p, z c) * equivariantReferenceAbsBound hp := by
              rw [Finset.sum_mul]
        _ = equivariantReferenceAbsBound hp := by rw [z.sum_eq_one, one_mul]]
  rw [hshift, hshift]
  simpa [PrimeSymmetry.smul_coordinate_apply] using
    congrArg (fun a : Real => a + equivariantReferenceAbsBound hp)
      (congrFun (equivariantReferenceCoordinateMap_global_smul hp g x) i)

 theorem negativeEquivariantReferenceCoordinateMap_global_smul
    (hp : Nat.Prime p) (g : PrimeSymmetry p) (x : Realization p) :
    (negativeEquivariantReferenceCoordinateMap hp).globalValue (g • x) =
      g • (negativeEquivariantReferenceCoordinateMap hp).globalValue x := by
  funext i
  change
    (negativeEquivariantReferenceCoordinateMap hp).globalValue (g • x) i =
      (negativeEquivariantReferenceCoordinateMap hp).globalValue x
        ((PrimeSymmetry.toPerm p g).symm i)
  have hshift : ∀ (z : Realization p) (j : Fin p),
      (negativeEquivariantReferenceCoordinateMap hp).globalValue z j =
        (equivariantReferenceCoordinateMap hp).globalValue z j -
          equivariantReferenceAbsBound hp := by
    intro z j
    unfold CoordinateAffineVertexMap.globalValue
    simp only [negativeEquivariantReferenceCoordinateMap, mul_sub,
      Finset.sum_sub_distrib]
    rw [show (∑ c : BarredPermutation p, z c * equivariantReferenceAbsBound hp) =
        equivariantReferenceAbsBound hp by
      calc
        (∑ c : BarredPermutation p, z c * equivariantReferenceAbsBound hp) =
            (∑ c : BarredPermutation p, z c) * equivariantReferenceAbsBound hp := by
              rw [Finset.sum_mul]
        _ = equivariantReferenceAbsBound hp := by rw [z.sum_eq_one, one_mul]]
  rw [hshift, hshift]
  simpa [PrimeSymmetry.smul_coordinate_apply] using
    congrArg (fun a : Real => a - equivariantReferenceAbsBound hp)
      (congrFun (equivariantReferenceCoordinateMap_global_smul hp g x) i)

 theorem positiveEquivariantReferenceCoordinateMap_global_pos
    (hp : Nat.Prime p) :
    ∀ x : Realization p, ∀ i : Fin p,
      0 < (positiveEquivariantReferenceCoordinateMap hp).globalValue x i := by
  intro x i
  unfold CoordinateAffineVertexMap.globalValue
  have hnonneg : ∀ c : BarredPermutation p,
      0 ≤ x c * (positiveEquivariantReferenceCoordinateMap hp).vertexValue c i := by
    intro c
    exact mul_nonneg (x.nonneg c)
      (le_of_lt (positiveEquivariantReferenceCoordinateMap_vertex_pos hp c i))
  obtain ⟨c, hc⟩ : ∃ c, 0 < x c := by
    by_contra h
    push Not at h
    have hz : ∀ c, x c = 0 := fun c => le_antisymm (h c) (x.nonneg c)
    have hx := x.sum_eq_one
    simp [hz] at hx
  exact Finset.sum_pos' (fun c _ => hnonneg c)
    ⟨c, Finset.mem_univ c,
      mul_pos hc (positiveEquivariantReferenceCoordinateMap_vertex_pos hp c i)⟩

 theorem negativeEquivariantReferenceCoordinateMap_global_neg
    (hp : Nat.Prime p) :
    ∀ x : Realization p, ∀ i : Fin p,
      (negativeEquivariantReferenceCoordinateMap hp).globalValue x i < 0 := by
  intro x i
  unfold CoordinateAffineVertexMap.globalValue
  have hnonpos : ∀ c : BarredPermutation p,
      x c * (negativeEquivariantReferenceCoordinateMap hp).vertexValue c i ≤ 0 := by
    intro c
    exact mul_nonpos_of_nonneg_of_nonpos (x.nonneg c)
      (le_of_lt (negativeEquivariantReferenceCoordinateMap_vertex_neg hp c i))
  obtain ⟨c, hc⟩ : ∃ c, 0 < x c := by
    by_contra h
    push Not at h
    have hz : ∀ c, x c = 0 := fun c => le_antisymm (h c) (x.nonneg c)
    have hx := x.sum_eq_one
    simp [hz] at hx
  exact Finset.sum_neg' (fun c _ => hnonpos c)
    ⟨c, Finset.mem_univ c,
      mul_neg_of_pos_of_neg hc
        (negativeEquivariantReferenceCoordinateMap_vertex_neg hp c i)⟩

/-- Positive local indices agree with S5 because the deviation is unchanged. -/
theorem positiveEquivariantReferenceIndex_eq_referenceIndex
    (hp : Nat.Prime p) :
    AffinePrismObstruction.positiveIndex hp
      (positiveEquivariantReferenceCoordinateMap hp) =
      ReferenceAffineOrbitCount.referenceIndex hp := by
  funext q
  unfold AffinePrismObstruction.positiveIndex
  rw [CoordinateAffineVertexMap.positiveLocalZeroIndex_eq_localZeroIndex_of_vertex_pos
    hp _ (positiveEquivariantReferenceCoordinateMap_vertex_pos hp)]
  rw [positiveEquivariantReferenceCoordinateMap_deviation hp]
  rfl

end AAK
end NRR
