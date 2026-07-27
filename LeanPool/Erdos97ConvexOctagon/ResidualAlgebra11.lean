/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.CayleyMenger
import LeanPool.Erdos97ConvexOctagon.ResidualRepresentatives
import Mathlib.Analysis.Convex.Combination

/-! # The final residual incidence class

The metric constraints of residual class 11 determine a normalized quadratic
parameter. Each of its two possible ranges puts a labelled vertex in the
convex hull of four other vertices.
-/

namespace Erdos97Octagon

open scoped InnerProductSpace

private structure Residual11Distances (p : Vertex → Plane) where
  base : ℝ
  s : ℝ
  w05 : ℝ
  w13 : ℝ
  w27 : ℝ
  w46 : ℝ
  hbase : base ≠ 0
  hbase_pos : 0 < base
  hs : 0 < s
  d01 : sqDist (p 0) (p 1) / base = 1
  d02 : sqDist (p 0) (p 2) / base = 1
  d03 : sqDist (p 0) (p 3) / base = 1
  d04 : sqDist (p 0) (p 4) / base = 1
  d05 : sqDist (p 0) (p 5) / base = w05
  d06 : sqDist (p 0) (p 6) / base = s
  d07 : sqDist (p 0) (p 7) / base = s
  d12 : sqDist (p 1) (p 2) / base = 1
  d13 : sqDist (p 1) (p 3) / base = w13
  d14 : sqDist (p 1) (p 4) / base = s
  d15 : sqDist (p 1) (p 5) / base = 1
  d16 : sqDist (p 1) (p 6) / base = 1
  d17 : sqDist (p 1) (p 7) / base = s
  d23 : sqDist (p 2) (p 3) / base = s
  d24 : sqDist (p 2) (p 4) / base = s
  d25 : sqDist (p 2) (p 5) / base = s
  d26 : sqDist (p 2) (p 6) / base = s
  d27 : sqDist (p 2) (p 7) / base = w27
  d34 : sqDist (p 3) (p 4) / base = 1
  d35 : sqDist (p 3) (p 5) / base = 1
  d36 : sqDist (p 3) (p 6) / base = s
  d37 : sqDist (p 3) (p 7) / base = 1
  d45 : sqDist (p 4) (p 5) / base = s
  d46 : sqDist (p 4) (p 6) / base = w46
  d47 : sqDist (p 4) (p 7) / base = s
  d56 : sqDist (p 5) (p 6) / base = 1
  d57 : sqDist (p 5) (p 7) / base = 1
  d67 : sqDist (p 6) (p 7) / base = s

private noncomputable def residual11_distances
    {p : Vertex → Plane} (hC : ConvexIndependent ℝ p)
    (hRealises : Realises p residualRepresentative11) :
    Residual11Distances p := by
  classical
  let radius := Classical.choose
    (exists_positive_radii hC.injective residualRepresentative11 hRealises)
  have hradius := Classical.choose_spec
    (exists_positive_radii hC.injective residualRepresentative11 hRealises)
  have hpos : ∀ v : Vertex, 0 < radius v := by
    simpa [radius] using hradius.1
  have hdist :
      ∀ v w : Vertex, w ∈ residualRepresentative11.targets v →
        dist (p v) (p w) = radius v := by
    simpa [radius] using hradius.2
  have r01 : radius 0 = radius 1 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative11])
  have r03 : radius 0 = radius 3 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative11])
  have r15 : radius 1 = radius 5 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative11])
  have r24 : radius 2 = radius 4 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative11])
  have r26 : radius 2 = radius 6 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative11])
  have r47 : radius 4 = radius 7 :=
    radius_eq_of_mutual hdist (by
      simp [OctagonIncidence.Mutual, residualRepresentative11])
  have radius0 : radius 0 = radius 0 := rfl
  have radius1 : radius 1 = radius 0 := r01.symm
  have radius2 : radius 2 = radius 2 := rfl
  have radius3 : radius 3 = radius 0 := r03.symm
  have radius4 : radius 4 = radius 2 := r24.symm
  have radius5 : radius 5 = radius 0 := (r01.trans r15).symm
  have radius6 : radius 6 = radius 2 := r26.symm
  have radius7 : radius 7 = radius 2 := (r24.trans r47).symm
  let base : ℝ := radius 0 ^ 2
  have hbase : base ≠ 0 := by
    dsimp [base]
    exact pow_ne_zero 2 (ne_of_gt (hpos 0))
  have hbase_pos : 0 < base := by
    dsimp [base]
    positivity
  let s : ℝ := radius 2 ^ 2 / base
  have hs : 0 < s := by
    dsimp [s]
    exact div_pos (pow_pos (hpos 2) 2) hbase_pos
  let w05 : ℝ := sqDist (p 0) (p 5) / base
  let w13 : ℝ := sqDist (p 1) (p 3) / base
  let w27 : ℝ := sqDist (p 2) (p 7) / base
  let w46 : ℝ := sqDist (p 4) (p 6) / base
  have d01 : sqDist (p 0) (p 1) / base = 1 := by
    rw [sqDist, hdist 0 1 (by decide), radius0]
    exact div_self hbase
  have d02 : sqDist (p 0) (p 2) / base = 1 := by
    rw [sqDist, hdist 0 2 (by decide), radius0]
    exact div_self hbase
  have d03 : sqDist (p 0) (p 3) / base = 1 := by
    rw [sqDist, hdist 0 3 (by decide), radius0]
    exact div_self hbase
  have d04 : sqDist (p 0) (p 4) / base = 1 := by
    rw [sqDist, hdist 0 4 (by decide), radius0]
    exact div_self hbase
  have d05 : sqDist (p 0) (p 5) / base = w05 := rfl
  have d06 : sqDist (p 0) (p 6) / base = s := by
    rw [sqDist, dist_comm, hdist 6 0 (by decide), radius6]
  have d07 : sqDist (p 0) (p 7) / base = s := by
    rw [sqDist, dist_comm, hdist 7 0 (by decide), radius7]
  have d12 : sqDist (p 1) (p 2) / base = 1 := by
    rw [sqDist, hdist 1 2 (by decide), radius1]
    exact div_self hbase
  have d13 : sqDist (p 1) (p 3) / base = w13 := rfl
  have d14 : sqDist (p 1) (p 4) / base = s := by
    rw [sqDist, dist_comm, hdist 4 1 (by decide), radius4]
  have d15 : sqDist (p 1) (p 5) / base = 1 := by
    rw [sqDist, hdist 1 5 (by decide), radius1]
    exact div_self hbase
  have d16 : sqDist (p 1) (p 6) / base = 1 := by
    rw [sqDist, hdist 1 6 (by decide), radius1]
    exact div_self hbase
  have d17 : sqDist (p 1) (p 7) / base = s := by
    rw [sqDist, dist_comm, hdist 7 1 (by decide), radius7]
  have d23 : sqDist (p 2) (p 3) / base = s := by
    rw [sqDist, hdist 2 3 (by decide), radius2]
  have d24 : sqDist (p 2) (p 4) / base = s := by
    rw [sqDist, hdist 2 4 (by decide), radius2]
  have d25 : sqDist (p 2) (p 5) / base = s := by
    rw [sqDist, hdist 2 5 (by decide), radius2]
  have d26 : sqDist (p 2) (p 6) / base = s := by
    rw [sqDist, hdist 2 6 (by decide), radius2]
  have d27 : sqDist (p 2) (p 7) / base = w27 := rfl
  have d34 : sqDist (p 3) (p 4) / base = 1 := by
    rw [sqDist, hdist 3 4 (by decide), radius3]
    exact div_self hbase
  have d35 : sqDist (p 3) (p 5) / base = 1 := by
    rw [sqDist, hdist 3 5 (by decide), radius3]
    exact div_self hbase
  have d36 : sqDist (p 3) (p 6) / base = s := by
    rw [sqDist, dist_comm, hdist 6 3 (by decide), radius6]
  have d37 : sqDist (p 3) (p 7) / base = 1 := by
    rw [sqDist, hdist 3 7 (by decide), radius3]
    exact div_self hbase
  have d45 : sqDist (p 4) (p 5) / base = s := by
    rw [sqDist, hdist 4 5 (by decide), radius4]
  have d46 : sqDist (p 4) (p 6) / base = w46 := rfl
  have d47 : sqDist (p 4) (p 7) / base = s := by
    rw [sqDist, hdist 4 7 (by decide), radius4]
  have d56 : sqDist (p 5) (p 6) / base = 1 := by
    rw [sqDist, hdist 5 6 (by decide), radius5]
    exact div_self hbase
  have d57 : sqDist (p 5) (p 7) / base = 1 := by
    rw [sqDist, hdist 5 7 (by decide), radius5]
    exact div_self hbase
  have d67 : sqDist (p 6) (p 7) / base = s := by
    rw [sqDist, hdist 6 7 (by decide), radius6]
  exact {
    base, s, w05, w13, w27, w46, hbase, hbase_pos, hs,
    d01, d02, d03, d04, d05, d06, d07, d12, d13, d14, d15,
    d16, d17, d23, d24, d25, d26, d27, d34, d35, d36, d37,
    d45, d46, d47, d56, d57, d67
  }

private structure Residual11Normalized (p : Vertex → Plane) where
  base : ℝ
  s : ℝ
  hbase : base ≠ 0
  hbase_pos : 0 < base
  hs : 0 < s
  hs_ne_two : s ≠ 2
  eS : s ^ 2 - 4 * s + 1 = 0
  d01 : sqDist (p 0) (p 1) / base = 1
  d02 : sqDist (p 0) (p 2) / base = 1
  d03 : sqDist (p 0) (p 3) / base = 1
  d04 : sqDist (p 0) (p 4) / base = 1
  d05 : sqDist (p 0) (p 5) / base = 2
  d06 : sqDist (p 0) (p 6) / base = s
  d07 : sqDist (p 0) (p 7) / base = s
  d12 : sqDist (p 1) (p 2) / base = 1
  d13 : sqDist (p 1) (p 3) / base = 2
  d15 : sqDist (p 1) (p 5) / base = 1
  d23 : sqDist (p 2) (p 3) / base = s
  d24 : sqDist (p 2) (p 4) / base = s
  d25 : sqDist (p 2) (p 5) / base = s
  d26 : sqDist (p 2) (p 6) / base = s
  d27 : sqDist (p 2) (p 7) / base = 2 * s
  d35 : sqDist (p 3) (p 5) / base = 1
  d46 : sqDist (p 4) (p 6) / base = 2 * s
  d47 : sqDist (p 4) (p 7) / base = s
  d67 : sqDist (p 6) (p 7) / base = s

private def Residual11Distances.normalize
    {p : Vertex → Plane} (D : Residual11Distances p) :
    Residual11Normalized p := by
  have hcmS := cm4_normalized_eq_zero (p 0) (p 1) (p 2) (p 4) D.hbase
  rw [D.d01, D.d02, D.d04, D.d12, D.d14, D.d24] at hcmS
  have eS : D.s ^ 2 - 4 * D.s + 1 = 0 := by
    dsimp [cm4] at hcmS
    nlinarith only [hcmS]
  have hcm05a := cm4_normalized_eq_zero (p 0) (p 1) (p 2) (p 5) D.hbase
  rw [D.d01, D.d02, D.d05, D.d12, D.d15, D.d25] at hcm05a
  have e05a :
      D.s ^ 2 - D.s * D.w05 - 2 * D.s + D.w05 ^ 2 - 2 * D.w05 + 1 = 0 := by
    dsimp [cm4] at hcm05a
    nlinarith only [hcm05a]
  have hcm05b := cm4_normalized_eq_zero (p 0) (p 1) (p 4) (p 5) D.hbase
  rw [D.d01, D.d04, D.d05, D.d14, D.d15, D.d45] at hcm05b
  have e05b : D.s ^ 2 + D.s * D.w05 ^ 2 - 3 * D.s * D.w05 - 2 * D.s + 1 = 0 := by
    dsimp [cm4] at hcm05b
    nlinarith only [hcm05b]
  have hcm13a := cm4_normalized_eq_zero (p 0) (p 1) (p 2) (p 3) D.hbase
  rw [D.d01, D.d02, D.d03, D.d12, D.d13, D.d23] at hcm13a
  have e13a :
      D.s ^ 2 - D.s * D.w13 - 2 * D.s + D.w13 ^ 2 - 2 * D.w13 + 1 = 0 := by
    dsimp [cm4] at hcm13a
    nlinarith only [hcm13a]
  have hcm13b := cm4_normalized_eq_zero (p 0) (p 1) (p 3) (p 6) D.hbase
  rw [D.d01, D.d03, D.d06, D.d13, D.d16, D.d36] at hcm13b
  have e13b : D.s ^ 2 + D.s * D.w13 ^ 2 - 3 * D.s * D.w13 - 2 * D.s + 1 = 0 := by
    dsimp [cm4] at hcm13b
    nlinarith only [hcm13b]
  have hcm27a := cm4_normalized_eq_zero (p 0) (p 1) (p 2) (p 7) D.hbase
  rw [D.d01, D.d02, D.d07, D.d12, D.d17, D.d27] at hcm27a
  have e27a :
      D.s ^ 2 - 2 * D.s * D.w27 - 2 * D.s + D.w27 ^ 2 - D.w27 + 1 = 0 := by
    dsimp [cm4] at hcm27a
    nlinarith only [hcm27a]
  have hcm27b := cm4_normalized_eq_zero (p 0) (p 2) (p 4) (p 7) D.hbase
  rw [D.d02, D.d04, D.d07, D.d24, D.d27, D.d47] at hcm27b
  have e27b : D.s ^ 3 - 2 * D.s ^ 2 - 3 * D.s * D.w27 + D.s + D.w27 ^ 2 = 0 := by
    dsimp [cm4] at hcm27b
    nlinarith only [hcm27b]
  have hcm46a := cm4_normalized_eq_zero (p 0) (p 3) (p 4) (p 6) D.hbase
  rw [D.d03, D.d04, D.d06, D.d34, D.d36, D.d46] at hcm46a
  have e46a :
      D.s ^ 2 - 2 * D.s * D.w46 - 2 * D.s + D.w46 ^ 2 - D.w46 + 1 = 0 := by
    dsimp [cm4] at hcm46a
    nlinarith only [hcm46a]
  have hcm46b := cm4_normalized_eq_zero (p 0) (p 2) (p 4) (p 6) D.hbase
  rw [D.d02, D.d04, D.d06, D.d24, D.d26, D.d46] at hcm46b
  have e46b : D.s ^ 3 - 2 * D.s ^ 2 - 3 * D.s * D.w46 + D.s + D.w46 ^ 2 = 0 := by
    dsimp [cm4] at hcm46b
    nlinarith only [hcm46b]
  have w05_eq : D.w05 = 2 := by
    have factor : (D.w05 - 1) * (D.w05 - 2) = 0 := by
      nlinarith only [eS, e05b]
    rcases mul_eq_zero.mp factor with h | h
    · have hw : D.w05 = 1 := by linarith only [h]
      rw [hw] at e05a
      nlinarith only [eS, e05a]
    · linarith only [h]
  have w13_eq : D.w13 = 2 := by
    have factor : (D.w13 - 1) * (D.w13 - 2) = 0 := by
      nlinarith only [eS, e13b]
    rcases mul_eq_zero.mp factor with h | h
    · have hw : D.w13 = 1 := by linarith only [h]
      rw [hw] at e13a
      nlinarith only [eS, e13a]
    · linarith only [h]
  have es3 : D.s ^ 3 = 15 * D.s - 4 := by
    nlinarith only [eS]
  have w27_eq : D.w27 = 2 * D.s := by
    have factor : (D.w27 - 1) * (D.w27 - 2 * D.s) = 0 := by
      nlinarith only [eS, e27a]
    rcases mul_eq_zero.mp factor with h | h
    · have hw : D.w27 = 1 := by linarith only [h]
      rw [hw] at e27b
      nlinarith only [eS, e27b, es3]
    · linarith only [h]
  have w46_eq : D.w46 = 2 * D.s := by
    have factor : (D.w46 - 1) * (D.w46 - 2 * D.s) = 0 := by
      nlinarith only [eS, e46a]
    rcases mul_eq_zero.mp factor with h | h
    · have hw : D.w46 = 1 := by linarith only [h]
      rw [hw] at e46b
      nlinarith only [eS, e46b, es3]
    · linarith only [h]
  have hs_ne_two : D.s ≠ 2 := by
    intro hs2
    rw [hs2] at eS
    norm_num at eS
  exact {
    base := D.base, s := D.s, hbase := D.hbase, hbase_pos := D.hbase_pos,
    hs := D.hs, hs_ne_two, eS, d01 := D.d01, d02 := D.d02, d03 := D.d03,
    d04 := D.d04, d05 := D.d05.trans w05_eq, d06 := D.d06, d07 := D.d07,
    d12 := D.d12, d13 := D.d13.trans w13_eq, d15 := D.d15, d23 := D.d23,
    d24 := D.d24, d25 := D.d25, d26 := D.d26, d27 := D.d27.trans w27_eq,
    d35 := D.d35, d46 := D.d46.trans w46_eq, d47 := D.d47, d67 := D.d67
  }

private lemma scaled_of_div_eq
    {p : Vertex → Plane} {base x : ℝ} {i j : Vertex}
    (hbase : base ≠ 0) (h : sqDist (p i) (p j) / base = x) :
    sqDist (p i) (p j) = x * base :=
  (div_eq_iff hbase).mp h

private lemma inner_scaled
    {p : Vertex → Plane} {base : ℝ} (o x y : Vertex) (A B C : ℝ)
    (hox : sqDist (p o) (p x) = A * base)
    (hoy : sqDist (p o) (p y) = B * base)
    (hxy : sqDist (p x) (p y) = C * base) :
    ⟪p x - p o, p y - p o⟫_ℝ = (A + B - C) * base / 2 := by
  rw [inner_sub_sub_eq, hox, hoy, hxy]
  ring

private lemma self_scaled
    {p : Vertex → Plane} {base : ℝ} (o x : Vertex) (A : ℝ)
    (hox : sqDist (p o) (p x) = A * base) :
    ⟪p x - p o, p x - p o⟫_ℝ = A * base := by
  have hxx : sqDist (p x) (p x) = 0 := by simp [sqDist]
  have hinner := inner_scaled o x x A A 0 hox hox (by simpa using hxx)
  nlinarith only [hinner]

private lemma residual11_lt_contradiction
    {p : Vertex → Plane} (hC : ConvexIndependent ℝ p)
    (D : Residual11Normalized p) (hslt : D.s < 2) : False := by
  let alpha : ℝ := (2 - D.s) / 4
  let beta : ℝ := D.s / 4
  have halpha : 0 ≤ alpha := by dsimp [alpha]; linarith
  have hbeta : 0 ≤ beta := by
    dsimp [beta]
    exact div_nonneg (le_of_lt D.hs) (by norm_num)
  have hab : 2 * alpha + 2 * beta = 1 := by
    dsimp [alpha, beta]
    ring
  have q01 := scaled_of_div_eq D.hbase D.d01
  have q02 := scaled_of_div_eq D.hbase D.d02
  have q03 := scaled_of_div_eq D.hbase D.d03
  have q05 := scaled_of_div_eq D.hbase D.d05
  have q12 := scaled_of_div_eq D.hbase D.d12
  have q13 := scaled_of_div_eq D.hbase D.d13
  have q15 := scaled_of_div_eq D.hbase D.d15
  have q23 := scaled_of_div_eq D.hbase D.d23
  have q25 := scaled_of_div_eq D.hbase D.d25
  have q35 := scaled_of_div_eq D.hbase D.d35
  let u1 := p 1 - p 0
  let u2 := p 2 - p 0
  let u3 := p 3 - p 0
  let u5 := p 5 - p 0
  have i11 : ⟪u1, u1⟫_ℝ = D.base := by
    simpa [u1] using self_scaled 0 1 1 q01
  have i22 : ⟪u2, u2⟫_ℝ = D.base := by
    simpa [u2] using self_scaled 0 2 1 q02
  have i33 : ⟪u3, u3⟫_ℝ = D.base := by
    simpa [u3] using self_scaled 0 3 1 q03
  have i55 : ⟪u5, u5⟫_ℝ = 2 * D.base := by
    simpa [u5] using self_scaled 0 5 2 q05
  have i12 : ⟪u1, u2⟫_ℝ = D.base / 2 := by
    simpa [u1, u2] using inner_scaled 0 1 2 1 1 1 q01 q02 q12
  have i13 : ⟪u1, u3⟫_ℝ = 0 := by
    have h := inner_scaled 0 1 3 1 1 2 q01 q03 q13
    dsimp [u1, u3] at h ⊢
    ring_nf at h ⊢
    exact h
  have i15 : ⟪u1, u5⟫_ℝ = D.base := by
    simpa [u1, u5] using inner_scaled 0 1 5 1 2 1 q01 q05 q15
  have i23 : ⟪u2, u3⟫_ℝ = (2 - D.s) * D.base / 2 := by
    have h := inner_scaled 0 2 3 1 1 D.s q02 q03 q23
    dsimp [u2, u3] at h ⊢
    ring_nf at h ⊢
    exact h
  have i25 : ⟪u2, u5⟫_ℝ = (3 - D.s) * D.base / 2 := by
    have h := inner_scaled 0 2 5 1 2 D.s q02 q05 q25
    dsimp [u2, u5] at h ⊢
    ring_nf at h ⊢
    exact h
  have i35 : ⟪u3, u5⟫_ℝ = D.base := by
    simpa [u3, u5] using inner_scaled 0 3 5 1 2 1 q03 q05 q35
  have i21 : ⟪u2, u1⟫_ℝ = D.base / 2 := by rw [real_inner_comm]; exact i12
  have i31 : ⟪u3, u1⟫_ℝ = 0 := by rw [real_inner_comm]; exact i13
  have i51 : ⟪u5, u1⟫_ℝ = D.base := by rw [real_inner_comm]; exact i15
  have i32 : ⟪u3, u2⟫_ℝ = (2 - D.s) * D.base / 2 := by
    rw [real_inner_comm]
    exact i23
  have i52 : ⟪u5, u2⟫_ℝ = (3 - D.s) * D.base / 2 := by
    rw [real_inner_comm]
    exact i25
  have i53 : ⟪u5, u3⟫_ℝ = D.base := by rw [real_inner_comm]; exact i35
  let z := u2 - (alpha • u5 + alpha • u3 + beta • u1)
  have hzinner : ⟪z, z⟫_ℝ = 0 := by
    dsimp [z]
    simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [i11, i22, i33, i55, i12, i13, i15, i23, i25, i35,
      i21, i31, i51, i32, i52, i53]
    dsimp [alpha, beta]
    linear_combination (norm := ring) (-D.base / 4) * D.eS
  have hz : z = 0 := inner_self_eq_zero.mp hzinner
  have hu : u2 = alpha • u5 + alpha • u3 + beta • u1 := sub_eq_zero.mp hz
  have affine : p 2 =
      alpha • p 5 + alpha • p 3 + beta • p 0 + beta • p 1 := by
    dsimp [u1, u2, u3, u5] at hu
    linear_combination (norm := module) hu - hab • p 0
  have hmem : p 2 ∈ convexHull ℝ (p '' ({0, 1, 3, 5} : Set Vertex)) := by
    refine mem_convexHull_of_exists_fintype
      ![alpha, alpha, beta, beta] ![p 5, p 3, p 0, p 1] ?_ ?_ ?_ ?_
    · intro i
      fin_cases i <;> assumption
    · simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
      nlinarith only [hab]
    · intro i
      fin_cases i <;> simp
    · simp [Fin.sum_univ_four, affine, add_assoc]
  have htwo := hC ({0, 1, 3, 5} : Set Vertex) 2 hmem
  simp at htwo

private lemma residual11_gt_contradiction
    {p : Vertex → Plane} (hC : ConvexIndependent ℝ p)
    (D : Residual11Normalized p) (hsgt : D.s > 2) : False := by
  have hproduct : D.s * (4 - D.s) = 1 := by nlinarith only [D.eS]
  have hproduct_pos : 0 < D.s * (4 - D.s) := by rw [hproduct]; norm_num
  have hslt4 : D.s < 4 := by
    rcases (mul_pos_iff.mp hproduct_pos) with h | h
    · linarith only [h.2]
    · linarith only [D.hs, h.1]
  let alpha : ℝ := (D.s - 2) / 4
  let beta : ℝ := (4 - D.s) / 4
  have halpha : 0 ≤ alpha := by dsimp [alpha]; linarith
  have hbeta : 0 ≤ beta := by dsimp [beta]; linarith
  have hab : 2 * alpha + 2 * beta = 1 := by
    dsimp [alpha, beta]
    ring
  have q20 : sqDist (p 2) (p 0) = D.base := by
    have h := scaled_of_div_eq D.hbase D.d02
    simpa [sqDist, dist_comm] using h
  have q24 := scaled_of_div_eq D.hbase D.d24
  have q26 := scaled_of_div_eq D.hbase D.d26
  have q27 := scaled_of_div_eq D.hbase D.d27
  have q04 := scaled_of_div_eq D.hbase D.d04
  have q06 := scaled_of_div_eq D.hbase D.d06
  have q07 := scaled_of_div_eq D.hbase D.d07
  have q46 := scaled_of_div_eq D.hbase D.d46
  have q47 := scaled_of_div_eq D.hbase D.d47
  have q67 := scaled_of_div_eq D.hbase D.d67
  let v0 := p 0 - p 2
  let v4 := p 4 - p 2
  let v6 := p 6 - p 2
  let v7 := p 7 - p 2
  have i00 : ⟪v0, v0⟫_ℝ = D.base := by
    simpa [v0] using self_scaled 2 0 1 (by simpa using q20)
  have i44 : ⟪v4, v4⟫_ℝ = D.s * D.base := by
    simpa [v4] using self_scaled 2 4 D.s q24
  have i66 : ⟪v6, v6⟫_ℝ = D.s * D.base := by
    simpa [v6] using self_scaled 2 6 D.s q26
  have i77 : ⟪v7, v7⟫_ℝ = 2 * D.s * D.base := by
    have h := self_scaled 2 7 (2 * D.s) q27
    dsimp [v7] at h ⊢
    ring_nf at h ⊢
    exact h
  have i04 : ⟪v0, v4⟫_ℝ = D.s * D.base / 2 := by
    have h := inner_scaled 2 0 4 1 D.s 1 (by simpa using q20) q24 (by
      simpa [sqDist, dist_comm] using q04)
    dsimp [v0, v4] at h ⊢
    ring_nf at h ⊢
    exact h
  have i06 : ⟪v0, v6⟫_ℝ = D.base / 2 := by
    have h := inner_scaled 2 0 6 1 D.s D.s (by simpa using q20) q26 (by
      simpa [sqDist, dist_comm] using q06)
    dsimp [v0, v6] at h ⊢
    ring_nf at h ⊢
    exact h
  have i07 : ⟪v0, v7⟫_ℝ = (1 + D.s) * D.base / 2 := by
    have h := inner_scaled 2 0 7 1 (2 * D.s) D.s (by simpa using q20) q27 (by
      simpa [sqDist, dist_comm] using q07)
    dsimp [v0, v7] at h ⊢
    ring_nf at h ⊢
    exact h
  have i46 : ⟪v4, v6⟫_ℝ = 0 := by
    have h := inner_scaled 2 4 6 D.s D.s (2 * D.s) q24 q26 q46
    dsimp [v4, v6] at h ⊢
    ring_nf at h ⊢
    exact h
  have i47 : ⟪v4, v7⟫_ℝ = D.s * D.base := by
    have h := inner_scaled 2 4 7 D.s (2 * D.s) D.s q24 q27 q47
    dsimp [v4, v7] at h ⊢
    ring_nf at h ⊢
    exact h
  have i67 : ⟪v6, v7⟫_ℝ = D.s * D.base := by
    have h := inner_scaled 2 6 7 D.s (2 * D.s) D.s q26 q27 q67
    dsimp [v6, v7] at h ⊢
    ring_nf at h ⊢
    exact h
  have i40 : ⟪v4, v0⟫_ℝ = D.s * D.base / 2 := by rw [real_inner_comm]; exact i04
  have i60 : ⟪v6, v0⟫_ℝ = D.base / 2 := by rw [real_inner_comm]; exact i06
  have i70 : ⟪v7, v0⟫_ℝ = (1 + D.s) * D.base / 2 := by
    rw [real_inner_comm]
    exact i07
  have i64 : ⟪v6, v4⟫_ℝ = 0 := by rw [real_inner_comm]; exact i46
  have i74 : ⟪v7, v4⟫_ℝ = D.s * D.base := by rw [real_inner_comm]; exact i47
  have i76 : ⟪v7, v6⟫_ℝ = D.s * D.base := by rw [real_inner_comm]; exact i67
  let z := v0 - (beta • v6 + beta • v7 + alpha • v4)
  have hzinner : ⟪z, z⟫_ℝ = 0 := by
    dsimp [z]
    simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [i00, i44, i66, i77, i04, i06, i07, i46, i47, i67,
      i40, i60, i70, i64, i74, i76]
    dsimp [alpha, beta]
    linear_combination (norm := ring) (D.base * (D.s - 4) / 4) * D.eS
  have hz : z = 0 := inner_self_eq_zero.mp hzinner
  have hu : v0 = beta • v6 + beta • v7 + alpha • v4 := sub_eq_zero.mp hz
  have affine : p 0 =
      alpha • p 2 + beta • p 6 + beta • p 7 + alpha • p 4 := by
    dsimp [v0, v4, v6, v7] at hu
    linear_combination (norm := module) hu - hab • p 2
  have hmem : p 0 ∈ convexHull ℝ (p '' ({2, 4, 6, 7} : Set Vertex)) := by
    refine mem_convexHull_of_exists_fintype
      ![alpha, beta, beta, alpha] ![p 2, p 6, p 7, p 4] ?_ ?_ ?_ ?_
    · intro i
      fin_cases i <;> assumption
    · simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
      nlinarith only [hab]
    · intro i
      fin_cases i <;> simp
    · simp [Fin.sum_univ_four, affine, add_assoc]
  have hzero := hC ({2, 4, 6, 7} : Set Vertex) 0 hmem
  simp at hzero

/-- The unique realizable residual class cannot occur in convex position. -/
theorem residualRepresentative11_not_convex_realises
    {p : Vertex → Plane} (hC : ConvexIndependent ℝ p) :
    ¬ Realises p residualRepresentative11 := by
  intro hRealises
  let D := (residual11_distances hC hRealises).normalize
  rcases lt_or_gt_of_ne D.hs_ne_two with hslt | hsgt
  · exact residual11_lt_contradiction hC D hslt
  · exact residual11_gt_contradiction hC D hsgt

end Erdos97Octagon
