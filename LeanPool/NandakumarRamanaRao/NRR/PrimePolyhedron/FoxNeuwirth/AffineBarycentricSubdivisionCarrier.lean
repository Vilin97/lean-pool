/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.IteratedSubdivisionSmallSimplex
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.AffineSubdivisionDeterminant
/-!
# Carrier coordinates for affine barycentric subdivision

The coordinates of one barycentric-subdivision simplex are monotone in the ordering permutation.
More precisely, if `z = affineSubdivMap n pi x`, then

`z (pi r) = sum_{k >= r} x k / (k+1)`.

Consequently every source coefficient is recovered from a consecutive coordinate drop.  A positive
source coefficient gives a strict cut in the ordered coordinates, so the corresponding prefix face
is determined by the image point itself.  These are the algebraic carrier facts used to prove that
piecewise-affine interpolation agrees on overlapping barycentric-subdivision simplices.
-/

open scoped BigOperators
open Finset

namespace SphereOddDegree
namespace AffineBarycentricSubdivision

/-
Coordinate of a prefix barycenter in its defining permutation order.
-/
theorem prefixBarycenter_apply_perm
    (n : Nat) (pi : Equiv.Perm (Fin (n + 1)))
    (k r : Fin (n + 1)) :
    prefixBarycenter n pi k (pi r) =
      if r.1 <= k.1 then (k.1 + 1 : Real)⁻¹ else 0 := by
  have h := NRR.AffineSubdivisionDeterminant.stepVertexMatrix_eq n pi
  have h_app := congr_fun (congr_fun h (pi r)) k
  dsimp [NRR.AffineSubdivisionDeterminant.stepVertexMatrix] at h_app
  change (prefixBarycenter n pi k).val (pi r) = _
  rw [h_app]
  rw [Matrix.mul_apply]
  have h_perm : ∀ j, Equiv.Perm.permMatrix Real pi.symm (pi r) j = if r = j then 1 else 0 := by
    intro j; simp [Equiv.Perm.permMatrix]
  simp_rw [h_perm, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  dsimp [NRR.AffineSubdivisionDeterminant.prefixAverageMatrix]

/-- Ordered-coordinate formula for one affine barycentric-subdivision chart. -/
theorem affineSubdivMap_apply_perm
    (n : Nat) (pi : Equiv.Perm (Fin (n + 1)))
    (x : Delta n) (r : Fin (n + 1)) :
    affineSubdivMap n pi x (pi r) =
      ∑ k : Fin (n + 1),
        if r.1 <= k.1 then x k * (k.1 + 1 : Real)⁻¹ else 0 := by
  rw [affineSubdivMap_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [prefixBarycenter_apply_perm]
  split_ifs <;> ring

/-- Coordinates of a barycentric-subdivision image are nonincreasing in the permutation order. -/
theorem affineSubdivMap_perm_antitone
    (n : Nat) (pi : Equiv.Perm (Fin (n + 1)))
    (x : Delta n) {r s : Fin (n + 1)} (hrs : r <= s) :
    affineSubdivMap n pi x (pi s) <= affineSubdivMap n pi x (pi r) := by
  rw [affineSubdivMap_apply_perm, affineSubdivMap_apply_perm]
  apply Finset.sum_le_sum
  intro k hk
  have hnonneg : 0 <= x k * (k.1 + 1 : Real)⁻¹ :=
    mul_nonneg (stdSimplex.zero_le x k) (inv_nonneg.mpr (by positivity))
  by_cases hsk : s.1 <= k.1
  · have hrk : r.1 <= k.1 := le_trans hrs hsk
    simp [hsk, hrk]
  · by_cases hrk : r.1 <= k.1
    · simp [hsk, hrk, hnonneg]
    · simp [hsk, hrk]

/-- A consecutive ordered-coordinate drop recovers the corresponding source coefficient. -/
theorem affineSubdivMap_perm_drop
    (n : Nat) (pi : Equiv.Perm (Fin (n + 1)))
    (x : Delta n) (r : Fin n) :
    affineSubdivMap n pi x (pi r.castSucc) -
        affineSubdivMap n pi x (pi r.succ) =
      x r.castSucc * (r.1 + 1 : Real)⁻¹ := by
  classical
  rw [affineSubdivMap_apply_perm, affineSubdivMap_apply_perm,
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single r.castSucc]
  · simp
  · intro k hk hkr
    have hne : k.1 ≠ r.1 := by
      intro h
      apply hkr
      apply Fin.ext
      exact h
    by_cases hrklt : r.1 < k.1
    · have hrk : r.1 <= k.1 := Nat.le_of_lt hrklt
      have hsucc : r.succ.1 <= k.1 := by simpa using hrklt
      simp [hrk, hsucc, hrklt]
    · have hkrlt : k.1 < r.1 := by omega
      have hrk : ¬ r.1 <= k.1 := Nat.not_le.mpr hkrlt
      have hsucc : ¬ r.succ.1 <= k.1 :=
        fun h => hrk (le_trans (by simp) h)
      simp [hrk, hsucc, hrklt]
  · simp

/-- The final ordered coordinate recovers the final source coefficient. -/
theorem affineSubdivMap_perm_last
    (n : Nat) (pi : Equiv.Perm (Fin (n + 1)))
    (x : Delta n) :
    affineSubdivMap n pi x (pi (Fin.last n)) =
      x (Fin.last n) * (n + 1 : Real)⁻¹ := by
  classical
  rw [affineSubdivMap_apply_perm]
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp
  · intro k hk hklast
    have hkne : k.1 ≠ n := by
      intro h
      apply hklast
      apply Fin.ext
      simpa using h
    have hkle : k.1 <= n := Nat.le_of_lt_succ k.isLt
    have hlt : k.1 < n := by omega
    have hnle : ¬ n <= k.1 := Nat.not_le.mpr hlt
    simp [hnle]
  · simp

/-- A positive nonfinal source coefficient produces a strict coordinate cut. -/
theorem affineSubdivMap_perm_strict_drop
    (n : Nat) (pi : Equiv.Perm (Fin (n + 1)))
    (x : Delta n) (r : Fin n) (hr : 0 < x r.castSucc) :
    affineSubdivMap n pi x (pi r.succ) <
      affineSubdivMap n pi x (pi r.castSucc) := by
  have hdrop := affineSubdivMap_perm_drop n pi x r
  have hinv : 0 < (r.1 + 1 : Real)⁻¹ := by positivity
  nlinarith [mul_pos hr hinv]

/-- A positive final source coefficient makes the final ordered coordinate positive. -/
theorem affineSubdivMap_perm_last_pos
    (n : Nat) (pi : Equiv.Perm (Fin (n + 1)))
    (x : Delta n) (hr : 0 < x (Fin.last n)) :
    0 < affineSubdivMap n pi x (pi (Fin.last n)) := by
  rw [affineSubdivMap_perm_last]
  exact mul_pos hr (by positivity)

/-- Every coordinate strictly after a positive cut is below the coordinate at that cut. -/
theorem affineSubdivMap_perm_lt_of_cut
    (n : Nat) (pi : Equiv.Perm (Fin (n + 1)))
    (x : Delta n) (r : Fin n) (hr : 0 < x r.castSucc)
    (s : Fin (n + 1)) (hrs : r.castSucc < s) :
    affineSubdivMap n pi x (pi s) <
      affineSubdivMap n pi x (pi r.castSucc) := by
  have hrsucc : r.succ <= s := by
    exact Fin.castSucc_lt_iff_succ_le.mp hrs
  exact lt_of_le_of_lt
    (affineSubdivMap_perm_antitone n pi x hrsucc)
    (affineSubdivMap_perm_strict_drop n pi x r hr)

/-- Every coordinate weakly before a cut is at least the coordinate at that cut. -/
theorem affineSubdivMap_perm_ge_of_le
    (n : Nat) (pi : Equiv.Perm (Fin (n + 1)))
    (x : Delta n) (r s : Fin (n + 1)) (hsr : s <= r) :
    affineSubdivMap n pi x (pi r) <=
      affineSubdivMap n pi x (pi s) :=
  affineSubdivMap_perm_antitone n pi x hsr

end AffineBarycentricSubdivision
end SphereOddDegree

namespace SphereOddDegree
namespace AffineBarycentricSubdivision

/-- The underlying vertex set of the `r`-th prefix face. -/
def prefixSet
    (n : Nat) (pi : Equiv.Perm (Fin (n + 1)))
    (r : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  (Finset.Iic r).image pi

@[simp] theorem mem_prefixSet
    (n : Nat) (pi : Equiv.Perm (Fin (n + 1)))
    (r j : Fin (n + 1)) :
    j ∈ prefixSet n pi r ↔ pi.symm j <= r := by
  classical
  constructor
  · intro hj
    rcases Finset.mem_image.mp hj with ⟨a, ha, haj⟩
    have har : a <= r := Finset.mem_Iic.mp ha
    have hasymm : pi.symm j = a := by
      rw [← haj]
      exact pi.symm_apply_apply a
    simpa [hasymm] using har
  · intro hj
    apply Finset.mem_image.mpr
    refine ⟨pi.symm j, Finset.mem_Iic.mpr hj, ?_⟩
    exact pi.apply_symm_apply j

@[simp] theorem card_prefixSet
    (n : Nat) (pi : Equiv.Perm (Fin (n + 1)))
    (r : Fin (n + 1)) :
    (prefixSet n pi r).card = r.1 + 1 := by
  classical
  unfold prefixSet
  rw [Finset.card_image_of_injective]
  · simp
  · exact pi.injective

/-- Coordinate formula for a prefix barycenter at an arbitrary ambient vertex. -/
theorem prefixBarycenter_apply
    (n : Nat) (pi : Equiv.Perm (Fin (n + 1)))
    (r j : Fin (n + 1)) :
    prefixBarycenter n pi r j =
      if j ∈ prefixSet n pi r then (r.1 + 1 : Real)⁻¹ else 0 := by
  have h := prefixBarycenter_apply_perm n pi r (pi.symm j)
  have heq : pi (pi.symm j) = j := Equiv.apply_symm_apply pi j
  rw [heq] at h
  rw [h]
  by_cases hj : j ∈ prefixSet n pi r
  · have hle : (pi.symm j).1 ≤ r.1 := (mem_prefixSet n pi r j).mp hj
    simp only [hj, hle, ite_true]
  · have hgt : ¬ (pi.symm j).1 ≤ r.1 := fun hle => hj ((mem_prefixSet n pi r j).mpr hle)
    simp only [hj, hgt, ite_false]

/-- At a positive cut, every vertex in the prefix has coordinate at least the cut coordinate. -/
theorem affineSubdivMap_ge_cut_of_mem_prefix
    (n : Nat) (pi : Equiv.Perm (Fin (n + 1)))
    (x : Delta n) (r j : Fin (n + 1))
    (hj : j ∈ prefixSet n pi r) :
    affineSubdivMap n pi x (pi r) <= affineSubdivMap n pi x j := by
  have hle : pi.symm j <= r := (mem_prefixSet n pi r j).mp hj
  have hmono := affineSubdivMap_perm_antitone n pi x hle
  simpa using hmono

/-
At a positive source coefficient, every vertex outside the corresponding prefix has strictly
smaller image coordinate than the cut coordinate.
-/
theorem affineSubdivMap_lt_cut_of_not_mem_prefix
    (n : Nat) (pi : Equiv.Perm (Fin (n + 1)))
    (x : Delta n) (r j : Fin (n + 1))
    (hr : 0 < x r)
    (hj : j ∉ prefixSet n pi r) :
    affineSubdivMap n pi x j < affineSubdivMap n pi x (pi r) := by
  have h_pi_inv_j_gt_r : r < pi.symm j := by
    contrapose! hj
    rw [mem_prefixSet]
    exact hj
  have hr_lt_n : r.1 < n := lt_of_lt_of_le h_pi_inv_j_gt_r (Fin.le_last _)
  have hlt := affineSubdivMap_perm_lt_of_cut n pi x ⟨r.1, hr_lt_n⟩ hr (pi.symm j) h_pi_inv_j_gt_r
  have h_eq : pi (pi.symm j) = j := Equiv.apply_symm_apply pi j
  have h_cast : (⟨r.1, hr_lt_n⟩ : Fin n).castSucc = r := rfl
  rw [h_cast] at hlt
  rw [h_eq] at hlt
  exact hlt

/-- A positive coefficient determines its prefix face from the image point.  Hence two
barycentric-subdivision charts representing the same point have the same active prefix. -/
theorem prefixSet_eq_of_affineSubdivMap_eq_of_pos
    (n : Nat) (pi sigma : Equiv.Perm (Fin (n + 1)))
    (x y : Delta n)
    (hxy : affineSubdivMap n pi x = affineSubdivMap n sigma y)
    (r : Fin (n + 1)) (hr : 0 < x r) :
    prefixSet n pi r = prefixSet n sigma r := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro j hjPi
    by_contra hjSigma
    have hex : ∃ l, l ∈ prefixSet n sigma r ∧ l ∉ prefixSet n pi r := by
      by_contra hnone
      push Not at hnone
      have hsub : prefixSet n sigma r ⊆ prefixSet n pi r := by
        intro l hl
        exact hnone l hl
      have heq : prefixSet n sigma r = prefixSet n pi r :=
        Finset.eq_of_subset_of_card_le hsub (by simp)
      exact hjSigma (by rw [heq]; exact hjPi)
    rcases hex with ⟨l, hlSigma, hlPi⟩
    have horder :
        affineSubdivMap n sigma y j <= affineSubdivMap n sigma y l := by
      have hjpos : sigma.symm l <= r :=
        (mem_prefixSet n sigma r l).mp hlSigma
      have hlpos : r < sigma.symm j :=
        lt_of_not_ge ((mem_prefixSet n sigma r j).not.mp hjSigma)
      have hle : sigma.symm l <= sigma.symm j :=
        le_trans hjpos (le_of_lt hlpos)
      simpa using affineSubdivMap_perm_antitone n sigma y hle
    have hjge := affineSubdivMap_ge_cut_of_mem_prefix n pi x r j hjPi
    have hllt := affineSubdivMap_lt_cut_of_not_mem_prefix n pi x r l hr hlPi
    have hzj := congrFun (congrArg Subtype.val hxy) j
    have hzl := congrFun (congrArg Subtype.val hxy) l
    have : affineSubdivMap n pi x j <= affineSubdivMap n pi x l := by
      calc
        affineSubdivMap n pi x j = affineSubdivMap n sigma y j := hzj
        _ <= affineSubdivMap n sigma y l := horder
        _ = affineSubdivMap n pi x l := hzl.symm
    linarith
  · simp

/-- Equality of image points identifies every active barycentric-subdivision vertex. -/
theorem prefixBarycenter_eq_of_affineSubdivMap_eq_of_pos
    (n : Nat) (pi sigma : Equiv.Perm (Fin (n + 1)))
    (x y : Delta n)
    (hxy : affineSubdivMap n pi x = affineSubdivMap n sigma y)
    (r : Fin (n + 1)) (hr : 0 < x r) :
    prefixBarycenter n pi r = prefixBarycenter n sigma r := by
  have hset := prefixSet_eq_of_affineSubdivMap_eq_of_pos n pi sigma x y hxy r hr
  apply stdSimplex.ext
  funext j
  simp [prefixBarycenter_apply, hset]

/-- The ordered coordinate at an active cut is independent of the sorting permutation. -/
theorem affineSubdivMap_cut_coordinate_eq_of_pos
    (n : Nat) (pi sigma : Equiv.Perm (Fin (n + 1)))
    (x y : Delta n)
    (hxy : affineSubdivMap n pi x = affineSubdivMap n sigma y)
    (r : Fin (n + 1)) (hr : 0 < x r) :
    affineSubdivMap n pi x (pi r) =
      affineSubdivMap n sigma y (sigma r) := by
  have hset := prefixSet_eq_of_affineSubdivMap_eq_of_pos n pi sigma x y hxy r hr
  have hsigma : sigma r ∈ prefixSet n pi r := by
    rw [hset]
    simp [mem_prefixSet]
  have hpi : pi r ∈ prefixSet n sigma r := by
    rw [← hset]
    simp [mem_prefixSet]
  have hleft := affineSubdivMap_ge_cut_of_mem_prefix n pi x r (sigma r) hsigma
  have hright := affineSubdivMap_ge_cut_of_mem_prefix n sigma y r (pi r) hpi
  have hz (j : Fin (n + 1)) :
      affineSubdivMap n pi x j = affineSubdivMap n sigma y j :=
    congrFun (congrArg Subtype.val hxy) j
  apply le_antisymm
  · calc
      affineSubdivMap n pi x (pi r) <= affineSubdivMap n pi x (sigma r) := hleft
      _ = affineSubdivMap n sigma y (sigma r) := hz _
  · calc
      affineSubdivMap n sigma y (sigma r) <= affineSubdivMap n sigma y (pi r) := hright
      _ = affineSubdivMap n pi x (pi r) := (hz _).symm

/-- The first coordinate after an active nonfinal cut is also permutation-independent. -/
theorem affineSubdivMap_next_coordinate_eq_of_pos
    (n : Nat) (pi sigma : Equiv.Perm (Fin (n + 1)))
    (x y : Delta n)
    (hxy : affineSubdivMap n pi x = affineSubdivMap n sigma y)
    (r : Fin n) (hr : 0 < x r.castSucc) :
    affineSubdivMap n pi x (pi r.succ) =
      affineSubdivMap n sigma y (sigma r.succ) := by
  have hset := prefixSet_eq_of_affineSubdivMap_eq_of_pos
    n pi sigma x y hxy r.castSucc hr
  have hsigmaNot : sigma r.succ ∉ prefixSet n pi r.castSucc := by
    rw [hset]
    simp [mem_prefixSet]
  have hpiNot : pi r.succ ∉ prefixSet n sigma r.castSucc := by
    rw [← hset]
    simp [mem_prefixSet]
  have hsigmaPos : r.succ <= pi.symm (sigma r.succ) := by
    have hlt : r.castSucc < pi.symm (sigma r.succ) :=
      lt_of_not_ge ((mem_prefixSet n pi r.castSucc (sigma r.succ)).not.mp hsigmaNot)
    exact Fin.castSucc_lt_iff_succ_le.mp hlt
  have hpiPos : r.succ <= sigma.symm (pi r.succ) := by
    have hlt : r.castSucc < sigma.symm (pi r.succ) :=
      lt_of_not_ge ((mem_prefixSet n sigma r.castSucc (pi r.succ)).not.mp hpiNot)
    exact Fin.castSucc_lt_iff_succ_le.mp hlt
  have hlePi : affineSubdivMap n pi x (sigma r.succ) <=
      affineSubdivMap n pi x (pi r.succ) := by
    simpa using affineSubdivMap_perm_antitone n pi x hsigmaPos
  have hleSigma : affineSubdivMap n sigma y (pi r.succ) <=
      affineSubdivMap n sigma y (sigma r.succ) := by
    simpa using affineSubdivMap_perm_antitone n sigma y hpiPos
  have hz (j : Fin (n + 1)) :
      affineSubdivMap n pi x j = affineSubdivMap n sigma y j :=
    congrFun (congrArg Subtype.val hxy) j
  apply le_antisymm
  · calc
      affineSubdivMap n pi x (pi r.succ) =
          affineSubdivMap n sigma y (pi r.succ) := hz _
      _ <= affineSubdivMap n sigma y (sigma r.succ) := hleSigma
  · calc
      affineSubdivMap n sigma y (sigma r.succ) =
          affineSubdivMap n pi x (sigma r.succ) := (hz _).symm
      _ <= affineSubdivMap n pi x (pi r.succ) := hlePi

/-- Every active source coefficient is independent of the chart representing the image point. -/
theorem affineSubdivMap_active_coefficient_eq
    (n : Nat) (pi sigma : Equiv.Perm (Fin (n + 1)))
    (x y : Delta n)
    (hxy : affineSubdivMap n pi x = affineSubdivMap n sigma y)
    (r : Fin (n + 1)) (hr : 0 < x r) :
    y r = x r := by
  by_cases hlast : r = Fin.last n
  · subst r
    have hcut := affineSubdivMap_cut_coordinate_eq_of_pos
      n pi sigma x y hxy (Fin.last n) hr
    rw [affineSubdivMap_perm_last, affineSubdivMap_perm_last] at hcut
    have hinv : 0 < (n + 1 : Real)⁻¹ := by positivity
    nlinarith
  · let r0 : Fin n := ⟨r.1, by
      have hrle : r.1 <= n := by omega
      exact lt_of_le_of_ne hrle (by
        intro h
        apply hlast
        apply Fin.ext
        simpa using h)⟩
    have hr0 : r0.castSucc = r := by
      apply Fin.ext
      rfl
    have hcut := affineSubdivMap_cut_coordinate_eq_of_pos
      n pi sigma x y hxy r hr
    have hnext := affineSubdivMap_next_coordinate_eq_of_pos
      n pi sigma x y hxy r0 (by simpa [hr0] using hr)
    have hxdrop := affineSubdivMap_perm_drop n pi x r0
    have hydrop := affineSubdivMap_perm_drop n sigma y r0
    rw [hr0] at hxdrop hydrop
    have hinv : 0 < (r0.1 + 1 : Real)⁻¹ := by positivity
    nlinarith

/-- One-step affine interpolation of arbitrary globally assigned vertex values agrees on overlap. -/
theorem affineSubdiv_vertexInterpolation_eq_of_map_eq
    {E : Type*} [AddCommMonoid E] [Module Real E]
    (n : Nat) (pi sigma : Equiv.Perm (Fin (n + 1)))
    (x y : Delta n)
    (hxy : affineSubdivMap n pi x = affineSubdivMap n sigma y)
    (V : Delta n → E) :
    (∑ r : Fin (n + 1), x r • V (prefixBarycenter n pi r)) =
      ∑ r : Fin (n + 1), y r • V (prefixBarycenter n sigma r) := by
  classical
  apply Finset.sum_congr rfl
  intro r hrmem
  by_cases hx : x r = 0
  · have hy : y r = 0 := by
      by_contra hy0
      have hypos : 0 < y r := lt_of_le_of_ne (stdSimplex.zero_le y r) (Ne.symm hy0)
      have hrev := affineSubdivMap_active_coefficient_eq
        n sigma pi y x hxy.symm r hypos
      apply hy0
      rw [← hrev]
      exact hx
    simp [hx, hy]
  · have hxpos : 0 < x r := lt_of_le_of_ne (stdSimplex.zero_le x r) (Ne.symm hx)
    have hvertex := prefixBarycenter_eq_of_affineSubdivMap_eq_of_pos
      n pi sigma x y hxy r hxpos
    have hcoeff := affineSubdivMap_active_coefficient_eq
      n pi sigma x y hxy r hxpos
    rw [hvertex, hcoeff]

end AffineBarycentricSubdivision
end SphereOddDegree

namespace SphereOddDegree
namespace AffineBarycentricSubdivision

/-- A positive source coefficient makes the image coordinate at its cut positive. -/
theorem affineSubdivMap_cut_pos
    (n : Nat) (pi : Equiv.Perm (Fin (n + 1)))
    (x : Delta n) (r : Fin (n + 1)) (hr : 0 < x r) :
    0 < affineSubdivMap n pi x (pi r) := by
  rw [affineSubdivMap_apply_perm]
  let f : Fin (n + 1) → Real := fun k =>
    if r.1 <= k.1 then x k * (k.1 + 1 : Real)⁻¹ else 0
  change 0 < ∑ k, f k
  have hf_nonneg : ∀ k, 0 <= f k := by
    intro k
    dsimp [f]
    split_ifs
    · exact mul_nonneg (stdSimplex.zero_le x k) (inv_nonneg.mpr (by positivity))
    · exact le_rfl
  have hle : f r <= ∑ k, f k :=
    Finset.single_le_sum (fun k _ => hf_nonneg k) (Finset.mem_univ r)
  have hfr : 0 < f r := by
    dsimp [f]
    simp only [le_refl, ite_true]
    exact mul_pos hr (by positivity)
  exact lt_of_lt_of_le hfr hle

/-- Every vertex in the prefix of a positive cut has positive image coordinate. -/
theorem affineSubdivMap_pos_of_mem_prefix
    (n : Nat) (pi : Equiv.Perm (Fin (n + 1)))
    (x : Delta n) (r j : Fin (n + 1))
    (hr : 0 < x r) (hj : j ∈ prefixSet n pi r) :
    0 < affineSubdivMap n pi x j := by
  exact lt_of_lt_of_le
    (affineSubdivMap_cut_pos n pi x r hr)
    (affineSubdivMap_ge_cut_of_mem_prefix n pi x r j hj)

/-
Every point of the standard simplex is the barycentric sum of its standard vertices.
-/
theorem delta_val_eq_sum_smul_stdVerts
    (n : Nat) (z : Delta n) :
    z.1 = ∑ i : Fin (n + 1), z i • BarycentricSubdivisionDiameter.stdVerts n i := by
  ext j; simp [BarycentricSubdivisionDiameter.stdVerts];
  rw [ Finset.sum_eq_single j ] <;> aesop

/-- Two iterated affine charts agree at a point if they agree at every active standard vertex. -/
theorem affineCompMap_eq_of_vertex_eq_on_support
    (n N : Nat)
    (rho sigma : Fin N → Equiv.Perm (Fin (n + 1)))
    (z : Delta n)
    (hvertex : ∀ i : Fin (n + 1), z i ≠ 0 →
      affineCompMap n N rho (stdSimplex.vertex (S := Real) i) =
        affineCompMap n N sigma (stdSimplex.vertex (S := Real) i)) :
    affineCompMap n N rho z = affineCompMap n N sigma z := by
  apply Subtype.ext
  rw [affineCompMap_coe, affineCompMap_coe,
    delta_val_eq_sum_smul_stdVerts n z, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [LinearMap.map_smul, LinearMap.map_smul]
  by_cases hzi : z i = 0
  · simp [hzi]
  · have hv := congrArg Subtype.val (hvertex i hzi)
    rw [affineCompMap_coe, affineCompMap_coe] at hv
    have hstd : BarycentricSubdivisionDiameter.stdVerts n i =
        (stdSimplex.vertex (S := Real) i).1 := by
      ext j
      simp [BarycentricSubdivisionDiameter.stdVerts, stdSimplex.vertex, Pi.single_apply]
    rw [hstd]
    exact congrArg (fun q => z i • q) hv

/-- Carrier theorem for iterated barycentric subdivision of one standard simplex.

If two iterated top-simplex charts represent the same point, every active source coefficient is
identical and the corresponding represented subdivision vertex is the same geometric point. -/
theorem affineCompMap_active_vertex_and_coefficient_eq
    (n N : Nat)
    (rho sigma : Fin N → Equiv.Perm (Fin (n + 1)))
    (x y : Delta n)
    (hxy : affineCompMap n N rho x = affineCompMap n N sigma y)
    (r : Fin (n + 1)) (hr : 0 < x r) :
    affineCompMap n N rho (stdSimplex.vertex (S := Real) r) =
        affineCompMap n N sigma (stdSimplex.vertex (S := Real) r) ∧
      y r = x r := by
  induction N generalizing x y r with
  | zero =>
      have hbase : x = y := by simpa using hxy
      constructor
      · simp
      · simpa [hbase]
  | succ N ih =>
      let rho0 : Fin N → Equiv.Perm (Fin (n + 1)) := fun i => rho i.castSucc
      let sigma0 : Fin N → Equiv.Perm (Fin (n + 1)) := fun i => sigma i.castSucc
      let pi : Equiv.Perm (Fin (n + 1)) := rho (Fin.last N)
      let tau : Equiv.Perm (Fin (n + 1)) := sigma (Fin.last N)
      let u : Delta n := affineSubdivMap n pi x
      let v : Delta n := affineSubdivMap n tau y
      have houter : affineCompMap n N rho0 u = affineCompMap n N sigma0 v := by
        simpa [affineCompMap_succ, rho0, sigma0, pi, tau, u, v] using hxy
      have huv : u = v := by
        apply stdSimplex.ext
        funext i
        by_cases hui : u i = 0
        · have hvi : v i = 0 := by
            by_contra hvi
            have hvpos : 0 < v i :=
              lt_of_le_of_ne (stdSimplex.zero_le v i) (Ne.symm hvi)
            have hrec := ih (rho := sigma0) (sigma := rho0)
              (x := v) (y := u) (r := i) houter.symm hvpos
            apply hvi
            rw [← hrec.2]
            exact hui
          simp [hui, hvi]
        · have hupos : 0 < u i :=
            lt_of_le_of_ne (stdSimplex.zero_le u i) (Ne.symm hui)
          have hrec := ih (rho := rho0) (sigma := sigma0)
            (x := u) (y := v) (r := i) houter hupos
          exact hrec.2.symm
      have hprefix : prefixBarycenter n pi r = prefixBarycenter n tau r :=
        prefixBarycenter_eq_of_affineSubdivMap_eq_of_pos
          n pi tau x y huv r hr
      have hcoeff : y r = x r :=
        affineSubdivMap_active_coefficient_eq n pi tau x y huv r hr
      have hvertexSupport : ∀ i : Fin (n + 1),
          prefixBarycenter n pi r i ≠ 0 →
          affineCompMap n N rho0 (stdSimplex.vertex (S := Real) i) =
            affineCompMap n N sigma0 (stdSimplex.vertex (S := Real) i) := by
        intro i hi
        have himem : i ∈ prefixSet n pi r := by
          by_contra hnot
          have hz : prefixBarycenter n pi r i = 0 := by
            simp [prefixBarycenter_apply, hnot]
          exact hi hz
        have hui : 0 < u i := by
          exact affineSubdivMap_pos_of_mem_prefix n pi x r i hr himem
        exact (ih (rho := rho0) (sigma := sigma0)
          (x := u) (y := v) (r := i) houter hui).1
      have hsame :
          affineCompMap n N rho0 (prefixBarycenter n pi r) =
            affineCompMap n N sigma0 (prefixBarycenter n pi r) :=
        affineCompMap_eq_of_vertex_eq_on_support
          n N rho0 sigma0 (prefixBarycenter n pi r) hvertexSupport
      have hfinalVertex :
          affineCompMap n N rho0 (prefixBarycenter n pi r) =
            affineCompMap n N sigma0 (prefixBarycenter n tau r) := by
        simpa [hprefix] using hsame
      constructor
      · simpa [affineCompMap_succ, rho0, sigma0, pi, tau,
          affineSubdivContinuousMap_apply, affineSubdivMap_vertex] using hfinalVertex
      · exact hcoeff

/-- Iterated affine interpolation of arbitrary globally assigned subdivision-vertex values agrees
on every overlap of iterated barycentric-subdivision top simplices. -/
theorem affineComp_vertexInterpolation_eq_of_map_eq
    {E : Type*} [AddCommMonoid E] [Module Real E]
    (n N : Nat)
    (rho sigma : Fin N → Equiv.Perm (Fin (n + 1)))
    (x y : Delta n)
    (hxy : affineCompMap n N rho x = affineCompMap n N sigma y)
    (V : Delta n → E) :
    (∑ r : Fin (n + 1), x r •
        V (affineCompMap n N rho (stdSimplex.vertex (S := Real) r))) =
      ∑ r : Fin (n + 1), y r •
        V (affineCompMap n N sigma (stdSimplex.vertex (S := Real) r)) := by
  classical
  apply Finset.sum_congr rfl
  intro r hrmem
  by_cases hx : x r = 0
  · have hy : y r = 0 := by
      by_contra hy0
      have hypos : 0 < y r :=
        lt_of_le_of_ne (stdSimplex.zero_le y r) (Ne.symm hy0)
      have hrev := affineCompMap_active_vertex_and_coefficient_eq
        n N sigma rho y x hxy.symm r hypos
      apply hy0
      rw [← hrev.2]
      exact hx
    simp [hx, hy]
  · have hxpos : 0 < x r :=
      lt_of_le_of_ne (stdSimplex.zero_le x r) (Ne.symm hx)
    have hactive := affineCompMap_active_vertex_and_coefficient_eq
      n N rho sigma x y hxy r hxpos
    rw [hactive.1, hactive.2]

end AffineBarycentricSubdivision
end SphereOddDegree

namespace SphereOddDegree
namespace AffineBarycentricSubdivision

/-- Coordinatewise barycentric formula for an iterated affine chart. -/
theorem affineCompMap_coordinate_eq_sum_vertices
    (n N : Nat)
    (rho : Fin N → Equiv.Perm (Fin (n + 1)))
    (x : Delta n) (j : Fin (n + 1)) :
    affineCompMap n N rho x j =
      ∑ r : Fin (n + 1), x r *
        affineCompMap n N rho (stdSimplex.vertex (S := Real) r) j := by
  have hvec :
      (affineCompMap n N rho x).1 =
        ∑ r : Fin (n + 1), x r •
          (affineCompMap n N rho (stdSimplex.vertex (S := Real) r)).1 := by
    rw [affineCompMap_coe, delta_val_eq_sum_smul_stdVerts n x, map_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [LinearMap.map_smul]
    have hstd : BarycentricSubdivisionDiameter.stdVerts n r =
        (stdSimplex.vertex (S := Real) r).1 := by
      ext k
      simp [BarycentricSubdivisionDiameter.stdVerts, stdSimplex.vertex, Pi.single_apply]
    rw [hstd]
    have hv := affineCompMap_coe n N rho
      (stdSimplex.vertex (S := Real) r)
    exact congrArg (fun q => x r • q) hv.symm
  have hj := congrFun hvec j
  rw [Finset.sum_apply] at hj
  exact hj

/-- The support of an active represented subdivision vertex is contained in the support of the
represented point. -/
theorem affineCompMap_vertex_support_subset
    (n N : Nat)
    (rho : Fin N → Equiv.Perm (Fin (n + 1)))
    (x : Delta n) (r j : Fin (n + 1))
    (hr : 0 < x r)
    (hj : 0 < affineCompMap n N rho
      (stdSimplex.vertex (S := Real) r) j) :
    0 < affineCompMap n N rho x j := by
  rw [affineCompMap_coordinate_eq_sum_vertices]
  let f : Fin (n + 1) → Real := fun k =>
    x k * affineCompMap n N rho (stdSimplex.vertex (S := Real) k) j
  change 0 < ∑ k, f k
  have hf_nonneg : ∀ k, 0 <= f k := by
    intro k
    exact mul_nonneg (stdSimplex.zero_le x k)
      (stdSimplex.zero_le
        (affineCompMap n N rho (stdSimplex.vertex (S := Real) k)) j)
  have hle : f r <= ∑ k, f k :=
    Finset.single_le_sum (fun k _ => hf_nonneg k) (Finset.mem_univ r)
  have hfr : 0 < f r := mul_pos hr hj
  exact lt_of_lt_of_le hfr hle

end AffineBarycentricSubdivision
end SphereOddDegree
