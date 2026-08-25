/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos132ThreeChain.Plane
import LeanPool.Erdos132ThreeChain.PowerThree

/-!
# The four-point catalogue relative to a shortest edge

Fix four plane points `A`, `B`, `C`, `D` whose six squared distances are all of the form
`c * 3 ^ e` with `e : ℕ`, where `c = sqDist A B` is the smallest of the six.  This file
classifies every such configuration.

`classify_point` uses only the triangle inequality: relative to the shortest edge `A B`, a
further point `P` is either *isoceles*, with `sqDist A P = sqDist B P`, or *spanning*, with
`{sqDist A P, sqDist B P} = {c, 3 * c}`.

The `pair_*` lemmas then feed the anchored Gram determinant, which must vanish for coplanar
points, into the arithmetic of `PowerThree`.  The outcome is that the two further points are
never both spanning in opposite senses, that every isoceles point has squared radius exactly
`c`, and that their mutual squared distance is `c` or `3 * c`.  Consequently all six squared
distances lie in the single adjacent pair `{c, 3 * c}`: no planar chain quadruple spans two
steps of the chain.
-/

namespace Erdos132ThreeChain

/-- Relative to a shortest edge `A B`, every further point is isoceles or spanning. -/
theorem classify_point {A B P : Point} {c : ℝ} (hc : 0 < c) (hAB : sqDist A B = c)
    (hAP : IsChainValue c (sqDist A P)) (hBP : IsChainValue c (sqDist B P)) :
    (∃ x : ℕ, sqDist A P = c * 3 ^ x ∧ sqDist B P = c * 3 ^ x)
      ∨ (sqDist A P = c ∧ sqDist B P = 3 * c)
      ∨ (sqDist A P = 3 * c ∧ sqDist B P = c) := by
  obtain ⟨x, hx⟩ := hAP
  obtain ⟨y, hy⟩ := hBP
  rcases le_total x y with hxy | hxy
  · have htri := sq_le_four_mul A B P
    rw [hAB, hx, hy] at htri
    have h' : (c * 3 ^ y - c * 3 ^ (0 : ℕ) - c * 3 ^ x) ^ 2
        ≤ 4 * (c * 3 ^ (0 : ℕ)) * (c * 3 ^ x) := by simpa using htri
    rcases exp_tri hc (Nat.zero_le x) hxy h' with h | ⟨h1, h2⟩
    · exact Or.inl ⟨x, hx, by rw [hy, h]⟩
    · refine Or.inr (Or.inl ⟨by rw [hx, ← h1, pow_zero, mul_one], by rw [hy, h2]; ring⟩)
  · have htri := sq_le_four_mul B A P
    rw [sqDist_comm B A, hAB, hx, hy] at htri
    have h' : (c * 3 ^ x - c * 3 ^ (0 : ℕ) - c * 3 ^ y) ^ 2
        ≤ 4 * (c * 3 ^ (0 : ℕ)) * (c * 3 ^ y) := by simpa using htri
    rcases exp_tri hc (Nat.zero_le y) hxy h' with h | ⟨h1, h2⟩
    · exact Or.inl ⟨x, hx, by rw [hy, ← h]⟩
    · refine Or.inr (Or.inr ⟨by rw [hx, h2]; ring, by rw [hy, ← h1, pow_zero, mul_one]⟩)

theorem gramDet_isoceles (c r s t : ℝ) :
    gramDet c r s r s t
      = -2 * c * (r ^ 2 + s ^ 2 + t ^ 2 - 2 * r * s - 2 * r * t - 2 * s * t + c * t) := by
  simp only [gramDet]; ring

theorem gramDet_mixed (c r t : ℝ) :
    gramDet c r c r (3 * c) t = -2 * c * ((r - t) ^ 2 - 3 * c * t + 3 * c ^ 2) := by
  simp only [gramDet]; ring

theorem gramDet_mixed' (c r t : ℝ) :
    gramDet c r (3 * c) r c t = -2 * c * ((r - t) ^ 2 - 3 * c * t + 3 * c ^ 2) := by
  simp only [gramDet]; ring

theorem gramDet_spanning (c t : ℝ) :
    gramDet c c c (3 * c) (3 * c) t = 2 * t * c * (3 * c - t) := by
  simp only [gramDet]; ring

theorem gramDet_spanning' (c t : ℝ) :
    gramDet c (3 * c) (3 * c) c c t = 2 * t * c * (3 * c - t) := by
  simp only [gramDet]; ring

theorem gramDet_opposite (c t : ℝ) :
    gramDet c c (3 * c) (3 * c) c t = -2 * c * (4 * c - t) * (7 * c - t) := by
  simp only [gramDet]; ring


/-- Two isoceles points: the shortest edge and both isoceles radii are equal to `c`, and the
two points are `3 * c` apart.  Auxiliary form, with the radii ordered. -/
theorem pair_isoceles_aux {A B C D : Point} {c : ℝ} (hc : 0 < c) {x y l : ℕ} (hxy : x ≤ y)
    (hAB : sqDist A B = c)
    (hAC : sqDist A C = c * 3 ^ x) (hBC : sqDist B C = c * 3 ^ x)
    (hAD : sqDist A D = c * 3 ^ y) (hBD : sqDist B D = c * 3 ^ y)
    (hCD : sqDist C D = c * 3 ^ l) :
    x = 0 ∧ y = 0 ∧ l = 1 := by
  have hdet := gramDet_eq_zero A B C D
  rw [hAB, hAC, hAD, hBC, hBD, hCD, gramDet_isoceles] at hdet
  have hbr : (c * 3 ^ x) ^ 2 + (c * 3 ^ y) ^ 2 + (c * 3 ^ l) ^ 2 - 2 * (c * 3 ^ x) * (c * 3 ^ y)
      - 2 * (c * 3 ^ x) * (c * 3 ^ l) - 2 * (c * 3 ^ y) * (c * 3 ^ l) + c * (c * 3 ^ l) = 0 :=
    (mul_eq_zero.mp hdet).resolve_left (by intro h; nlinarith)
  have hkey : (c : ℝ) ^ 2 * ((3 : ℝ) ^ x * 3 ^ x + 3 ^ y * 3 ^ y + 3 ^ l * 3 ^ l
      - 2 * (3 ^ x * 3 ^ y) - 2 * (3 ^ x * 3 ^ l) - 2 * (3 ^ y * 3 ^ l) + 3 ^ l) = 0 := by
    linear_combination hbr
  have hR : (3 : ℝ) ^ x * 3 ^ x + 3 ^ y * 3 ^ y + 3 ^ l * 3 ^ l - 2 * (3 ^ x * 3 ^ y)
      - 2 * (3 ^ x * 3 ^ l) - 2 * (3 ^ y * 3 ^ l) + 3 ^ l = 0 :=
    (mul_eq_zero.mp hkey).resolve_left (by positivity)
  have hZ : (3 : ℤ) ^ x * 3 ^ x + 3 ^ y * 3 ^ y + 3 ^ l * 3 ^ l - 2 * (3 ^ x * 3 ^ y)
      - 2 * (3 ^ x * 3 ^ l) - 2 * (3 ^ y * 3 ^ l) + 3 ^ l = 0 := by
    have hcast : (((3 : ℤ) ^ x * 3 ^ x + 3 ^ y * 3 ^ y + 3 ^ l * 3 ^ l - 2 * (3 ^ x * 3 ^ y)
        - 2 * (3 ^ x * 3 ^ l) - 2 * (3 ^ y * 3 ^ l) + 3 ^ l : ℤ) : ℝ) = 0 := by
      push_cast; linarith [hR]
    exact_mod_cast hcast
  have htri1 : (c * 3 ^ y - c * 3 ^ x - c * 3 ^ l) ^ 2 ≤ 4 * (c * 3 ^ x) * (c * 3 ^ l) := by
    have h := sq_le_four_mul C A D
    rwa [sqDist_comm C A, hAC, hAD, hCD] at h
  have htri2 : (c * 3 ^ l - c * 3 ^ x - c * 3 ^ y) ^ 2 ≤ 4 * (c * 3 ^ x) * (c * 3 ^ y) := by
    have h := sq_le_four_mul A C D
    rwa [hAC, hAD, hCD] at h
  have hcase : x = y ∨ (l = x ∧ y = x + 1) ∨ l = y := by
    rcases le_total l x with hlx | hxl
    · have h : (c * 3 ^ y - c * 3 ^ l - c * 3 ^ x) ^ 2 ≤ 4 * (c * 3 ^ l) * (c * 3 ^ x) := by
        calc (c * 3 ^ y - c * 3 ^ l - c * 3 ^ x) ^ 2
            = (c * 3 ^ y - c * 3 ^ x - c * 3 ^ l) ^ 2 := by ring
          _ ≤ 4 * (c * 3 ^ x) * (c * 3 ^ l) := htri1
          _ = 4 * (c * 3 ^ l) * (c * 3 ^ x) := by ring
      rcases exp_tri hc hlx hxy h with h1 | ⟨h1, h2⟩
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · rcases le_total l y with hly | hyl
      · rcases exp_tri hc hxl hly htri1 with h1 | ⟨h1, h2⟩
        · exact Or.inr (Or.inr (by omega))
        · exact Or.inr (Or.inl ⟨by omega, h2⟩)
      · rcases exp_tri hc hxy hyl htri2 with h1 | ⟨h1, h2⟩
        · exact Or.inr (Or.inr h1)
        · exact Or.inl h1
  exact isoceles_pair_solution hxy hcase hZ

/-- Two isoceles points relative to the shortest edge `A B` force both radii to equal `c` and
their mutual squared distance to equal `3 * c`. -/
theorem pair_isoceles {A B C D : Point} {c : ℝ} (hc : 0 < c) {x y l : ℕ}
    (hAB : sqDist A B = c)
    (hAC : sqDist A C = c * 3 ^ x) (hBC : sqDist B C = c * 3 ^ x)
    (hAD : sqDist A D = c * 3 ^ y) (hBD : sqDist B D = c * 3 ^ y)
    (hCD : sqDist C D = c * 3 ^ l) :
    x = 0 ∧ y = 0 ∧ l = 1 := by
  rcases le_total x y with h | h
  · exact pair_isoceles_aux hc h hAB hAC hBC hAD hBD hCD
  · obtain ⟨hy0, hx0, hl1⟩ :=
      pair_isoceles_aux hc h hAB hAD hBD hAC hBC (by rw [sqDist_comm D C]; exact hCD)
    exact ⟨hx0, hy0, hl1⟩

/-- One isoceles point and one spanning point: the isoceles radius is `c` and the two points
are `c` apart. -/
theorem pair_mixed {A B C D : Point} {c : ℝ} (hc : 0 < c) {x l : ℕ}
    (hAB : sqDist A B = c)
    (hAC : sqDist A C = c * 3 ^ x) (hBC : sqDist B C = c * 3 ^ x)
    (hD : (sqDist A D = c ∧ sqDist B D = 3 * c) ∨ (sqDist A D = 3 * c ∧ sqDist B D = c))
    (hCD : sqDist C D = c * 3 ^ l) :
    x = 0 ∧ l = 0 := by
  have hdet := gramDet_eq_zero A B C D
  have hbr : (c * 3 ^ x - c * 3 ^ l) ^ 2 - 3 * c * (c * 3 ^ l) + 3 * c ^ 2 = 0 := by
    rcases hD with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hAB, hAC, h1, hBC, h2, hCD, gramDet_mixed] at hdet
      exact (mul_eq_zero.mp hdet).resolve_left (by intro hz; nlinarith)
    · rw [hAB, hAC, h1, hBC, h2, hCD, gramDet_mixed'] at hdet
      exact (mul_eq_zero.mp hdet).resolve_left (by intro hz; nlinarith)
  have hkey : (c : ℝ) ^ 2 * (((3 : ℝ) ^ x - 3 ^ l) ^ 2 - 3 * 3 ^ l + 3) = 0 := by
    linear_combination hbr
  have hR : ((3 : ℝ) ^ x - 3 ^ l) ^ 2 - 3 * 3 ^ l + 3 = 0 :=
    (mul_eq_zero.mp hkey).resolve_left (by positivity)
  have hZ : ((3 : ℤ) ^ x - 3 ^ l) ^ 2 - 3 * 3 ^ l + 3 = 0 := by
    have hcast : ((((3 : ℤ) ^ x - 3 ^ l) ^ 2 - 3 * 3 ^ l + 3 : ℤ) : ℝ) = 0 := by
      push_cast; linarith [hR]
    exact_mod_cast hcast
  exact mixed_pair_solution hZ

/-- Two spanning points of the same sense are `3 * c` apart. -/
theorem pair_spanning {A B C D : Point} {c : ℝ} (hc : 0 < c) {l : ℕ}
    (hAB : sqDist A B = c) (hCD : sqDist C D = c * 3 ^ l)
    (h : (sqDist A C = c ∧ sqDist B C = 3 * c ∧ sqDist A D = c ∧ sqDist B D = 3 * c)
      ∨ (sqDist A C = 3 * c ∧ sqDist B C = c ∧ sqDist A D = 3 * c ∧ sqDist B D = c)) :
    l = 1 := by
  have hcne : (c : ℝ) ≠ 0 := ne_of_gt hc
  have hdet := gramDet_eq_zero A B C D
  have hfac : 2 * (c * 3 ^ l) * c * (3 * c - c * 3 ^ l) = 0 := by
    rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · rwa [hAB, h1, h3, h2, h4, hCD, gramDet_spanning] at hdet
    · rwa [hAB, h1, h3, h2, h4, hCD, gramDet_spanning'] at hdet
  have hpos : (0 : ℝ) < 2 * (c * 3 ^ l) * c := by positivity
  have hlin := (mul_eq_zero.mp hfac).resolve_left (ne_of_gt hpos)
  have hT : (3 : ℝ) ^ l = 3 := by
    have hz : c * (3 ^ l - 3) = 0 := by linear_combination -hlin
    have := (mul_eq_zero.mp hz).resolve_left hcne
    linarith
  have hZ : (3 : ℤ) ^ l = 3 ^ 1 := by
    have hcast : (((3 : ℤ) ^ l : ℤ) : ℝ) = (((3 : ℤ) ^ 1 : ℤ) : ℝ) := by
      push_cast; linarith [hT]
    exact_mod_cast hcast
  exact pow3_inj hZ

/-- Two spanning points of opposite senses cannot both occur. -/
theorem pair_opposite {A B C D : Point} {c : ℝ} (hc : 0 < c) {l : ℕ}
    (hAB : sqDist A B = c) (hCD : sqDist C D = c * 3 ^ l)
    (hAC : sqDist A C = c) (hBC : sqDist B C = 3 * c)
    (hAD : sqDist A D = 3 * c) (hBD : sqDist B D = c) : False := by
  have hcne : (c : ℝ) ≠ 0 := ne_of_gt hc
  have hdet := gramDet_eq_zero A B C D
  rw [hAB, hAC, hAD, hBC, hBD, hCD, gramDet_opposite] at hdet
  have h2 : (-2 : ℝ) * c ≠ 0 := by intro hz; nlinarith
  have hfac : (4 * c - c * 3 ^ l) * (7 * c - c * 3 ^ l) = 0 := by
    rcases mul_eq_zero.mp hdet with hu | hu
    · rcases mul_eq_zero.mp hu with hv | hv
      · exact absurd hv h2
      · rw [hv]; ring
    · rw [hu]; ring
  rcases mul_eq_zero.mp hfac with hu | hu
  · have hR : (3 : ℝ) ^ l = 4 := by
      have hz : c * (3 ^ l - 4) = 0 := by linear_combination -hu
      have := (mul_eq_zero.mp hz).resolve_left hcne
      linarith
    have hZ : (3 : ℤ) ^ l = 4 := by
      have hcast : (((3 : ℤ) ^ l : ℤ) : ℝ) = ((4 : ℤ) : ℝ) := by push_cast; linarith [hR]
      exact_mod_cast hcast
    exact pow3_ne_four hZ
  · have hR : (3 : ℝ) ^ l = 7 := by
      have hz : c * (3 ^ l - 7) = 0 := by linear_combination -hu
      have := (mul_eq_zero.mp hz).resolve_left hcne
      linarith
    have hZ : (3 : ℤ) ^ l = 7 := by
      have hcast : (((3 : ℤ) ^ l : ℤ) : ℝ) = ((7 : ℤ) : ℝ) := by push_cast; linarith [hR]
      exact_mod_cast hcast
    exact pow3_ne_seven hZ


/-- The position of a further point `P` relative to a shortest edge `A B` of squared length
`c`: both squared distances lie in the adjacent pair `{c, 3 * c}`, and at least one of them is
`c`. -/
structure ChainPos (A B P : Point) (c : ℝ) : Prop where
  /-- `P` is at squared distance `c` or `3 * c` from `A`. -/
  fromLeft : sqDist A P = c ∨ sqDist A P = 3 * c
  /-- `P` is at squared distance `c` or `3 * c` from `B`. -/
  fromRight : sqDist B P = c ∨ sqDist B P = 3 * c
  /-- At least one endpoint of the shortest edge is at squared distance exactly `c` from `P`. -/
  nearEnd : sqDist A P = c ∨ sqDist B P = c

/-- The seven labelled patterns a chain quadruple can take, once `A B` is a shortest edge of
squared length `c`.  Five of them carry a single long edge — the rhombus of two glued
equilateral triangles, with the long edge in any position other than `A B` — and two carry a
triangle of three long edges, the equilateral triangle together with its centroid, whose
centroid must be `A` or `B` because `A B` is short.  Dropping the choice of shortest edge these
are the `6 + 4 = 10` labelled assignments per adjacent pair of the chain. -/
inductive ChainPattern (A B C D : Point) (c : ℝ) : Prop
  /-- Rhombus whose single long edge is `C D`. -/
  | longCD : sqDist A C = c → sqDist B C = c → sqDist A D = c → sqDist B D = c →
      sqDist C D = 3 * c → ChainPattern A B C D c
  /-- Rhombus whose single long edge is `B D`. -/
  | longBD : sqDist A C = c → sqDist B C = c → sqDist A D = c → sqDist B D = 3 * c →
      sqDist C D = c → ChainPattern A B C D c
  /-- Rhombus whose single long edge is `A D`. -/
  | longAD : sqDist A C = c → sqDist B C = c → sqDist A D = 3 * c → sqDist B D = c →
      sqDist C D = c → ChainPattern A B C D c
  /-- Rhombus whose single long edge is `B C`. -/
  | longBC : sqDist A C = c → sqDist B C = 3 * c → sqDist A D = c → sqDist B D = c →
      sqDist C D = c → ChainPattern A B C D c
  /-- Rhombus whose single long edge is `A C`. -/
  | longAC : sqDist A C = 3 * c → sqDist B C = c → sqDist A D = c → sqDist B D = c →
      sqDist C D = c → ChainPattern A B C D c
  /-- Equilateral triangle `B C D` of long edges with centroid `A`. -/
  | centreA : sqDist A C = c → sqDist B C = 3 * c → sqDist A D = c → sqDist B D = 3 * c →
      sqDist C D = 3 * c → ChainPattern A B C D c
  /-- Equilateral triangle `A C D` of long edges with centroid `B`. -/
  | centreB : sqDist A C = 3 * c → sqDist B C = c → sqDist A D = 3 * c → sqDist B D = c →
      sqDist C D = 3 * c → ChainPattern A B C D c

/-- The conclusion of the four-point catalogue: everything the shortest edge `A B` forces on a
chain quadruple `A`, `B`, `C`, `D`. -/
structure ChainQuadruple (A B C D : Point) (c : ℝ) : Prop where
  /-- `C` sits in the adjacent pair `{c, 3 * c}` relative to `A B`. -/
  posC : ChainPos A B C c
  /-- `D` sits in the adjacent pair `{c, 3 * c}` relative to `A B`. -/
  posD : ChainPos A B D c
  /-- `C` and `D` are `c` or `3 * c` apart. -/
  distCD : sqDist C D = c ∨ sqDist C D = 3 * c
  /-- `C` and `D` never span `A B` in opposite senses, first half. -/
  sharedLeft : sqDist A C = c ∨ sqDist B D = c
  /-- `C` and `D` never span `A B` in opposite senses, second half. -/
  sharedRight : sqDist B C = c ∨ sqDist A D = c
  /-- The labelling is one of the seven patterns of the catalogue. -/
  pattern : ChainPattern A B C D c

/-- **The chain-quadruple theorem relative to a shortest edge.**  If the six squared distances
of `A`, `B`, `C`, `D` are all `c` times a power of three, with `c = sqDist A B` the smallest,
then all six lie in the adjacent pair `{c, 3 * c}`, the points `C` and `D` never span the edge
`A B` in opposite senses, and the labelling is one of the seven patterns of `ChainPattern`. -/
theorem pair_classification {A B C D : Point} {c : ℝ} (hc : 0 < c)
    (hAB : sqDist A B = c)
    (hAC : IsChainValue c (sqDist A C)) (hBC : IsChainValue c (sqDist B C))
    (hAD : IsChainValue c (sqDist A D)) (hBD : IsChainValue c (sqDist B D))
    (hCD : IsChainValue c (sqDist C D)) :
    ChainQuadruple A B C D c := by
  obtain ⟨l, hl⟩ := hCD
  have hlDC : sqDist D C = c * 3 ^ l := by rw [sqDist_comm D C]; exact hl
  have h1 : (c : ℝ) * 3 ^ (0 : ℕ) = c := by norm_num
  have h3 : (c : ℝ) * 3 ^ (1 : ℕ) = 3 * c := by ring
  rcases classify_point hc hAB hAC hBC with ⟨x, hx1, hx2⟩ | ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩ <;>
    rcases classify_point hc hAB hAD hBD with ⟨y, hy1, hy2⟩ | ⟨hd1, hd2⟩ | ⟨hd1, hd2⟩
  · obtain ⟨hx0, hy0, hl1⟩ := pair_isoceles hc hAB hx1 hx2 hy1 hy2 hl
    subst hx0; subst hy0; subst hl1
    rw [h1] at hx1 hx2 hy1 hy2; rw [h3] at hl
    exact ⟨⟨Or.inl hx1, Or.inl hx2, Or.inl hx1⟩, ⟨Or.inl hy1, Or.inl hy2, Or.inl hy1⟩,
      Or.inr hl, Or.inl hx1, Or.inl hx2, .longCD hx1 hx2 hy1 hy2 hl⟩
  · obtain ⟨hx0, hl0⟩ := pair_mixed hc hAB hx1 hx2 (Or.inl ⟨hd1, hd2⟩) hl
    subst hx0; subst hl0
    rw [h1] at hx1 hx2 hl
    exact ⟨⟨Or.inl hx1, Or.inl hx2, Or.inl hx1⟩, ⟨Or.inl hd1, Or.inr hd2, Or.inl hd1⟩,
      Or.inl hl, Or.inl hx1, Or.inl hx2, .longBD hx1 hx2 hd1 hd2 hl⟩
  · obtain ⟨hx0, hl0⟩ := pair_mixed hc hAB hx1 hx2 (Or.inr ⟨hd1, hd2⟩) hl
    subst hx0; subst hl0
    rw [h1] at hx1 hx2 hl
    exact ⟨⟨Or.inl hx1, Or.inl hx2, Or.inl hx1⟩, ⟨Or.inr hd1, Or.inl hd2, Or.inr hd2⟩,
      Or.inl hl, Or.inl hx1, Or.inl hx2, .longAD hx1 hx2 hd1 hd2 hl⟩
  · obtain ⟨hy0, hl0⟩ := pair_mixed hc hAB hy1 hy2 (Or.inl ⟨hc1, hc2⟩) hlDC
    subst hy0; subst hl0
    rw [h1] at hy1 hy2 hl
    exact ⟨⟨Or.inl hc1, Or.inr hc2, Or.inl hc1⟩, ⟨Or.inl hy1, Or.inl hy2, Or.inl hy1⟩,
      Or.inl hl, Or.inl hc1, Or.inr hy1, .longBC hc1 hc2 hy1 hy2 hl⟩
  · have hl1 := pair_spanning hc hAB hl (Or.inl ⟨hc1, hc2, hd1, hd2⟩)
    subst hl1; rw [h3] at hl
    exact ⟨⟨Or.inl hc1, Or.inr hc2, Or.inl hc1⟩, ⟨Or.inl hd1, Or.inr hd2, Or.inl hd1⟩,
      Or.inr hl, Or.inl hc1, Or.inr hd1, .centreA hc1 hc2 hd1 hd2 hl⟩
  · exact absurd (pair_opposite hc hAB hl hc1 hc2 hd1 hd2) (by simp)
  · obtain ⟨hy0, hl0⟩ := pair_mixed hc hAB hy1 hy2 (Or.inr ⟨hc1, hc2⟩) hlDC
    subst hy0; subst hl0
    rw [h1] at hy1 hy2 hl
    exact ⟨⟨Or.inr hc1, Or.inl hc2, Or.inr hc2⟩, ⟨Or.inl hy1, Or.inl hy2, Or.inl hy1⟩,
      Or.inl hl, Or.inr hy2, Or.inl hc2, .longAC hc1 hc2 hy1 hy2 hl⟩
  · exact absurd (pair_opposite hc hAB hlDC hd1 hd2 hc1 hc2) (by simp)
  · have hl1 := pair_spanning hc hAB hl (Or.inr ⟨hc1, hc2, hd1, hd2⟩)
    subst hl1; rw [h3] at hl
    exact ⟨⟨Or.inr hc1, Or.inl hc2, Or.inr hc2⟩, ⟨Or.inr hd1, Or.inl hd2, Or.inr hd2⟩,
      Or.inr hl, Or.inr hd2, Or.inl hc2, .centreB hc1 hc2 hd1 hd2 hl⟩

end Erdos132ThreeChain
