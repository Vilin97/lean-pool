/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import LeanPool.BollobasNikiforov.M.Config
public import LeanPool.BollobasNikiforov.CP.Basic
import LeanPool.BollobasNikiforov.CP.Closed
import LeanPool.BollobasNikiforov.M.GammaZero
import Mathlib.Algebra.Order.Star.Real

/-!
# Completely positivity of `M` on a right-angle planar cone

If planar Gram vectors have pairwise nonnegative inner products, they can be
rotated into the closed first quadrant. Then `M X = X ⊙ X` expands as a sum
of three nonnegative rank-ones. Scaling `X` by a positive square does not
change whether `M X` is completely positive. Zero Gram vectors may be deleted:
`M` of the remaining principal submatrix is completely positive if and only if
the original `M` is (pad a CP factor by zero coordinates). An open half-plane
with a unique supporting vector reduces, after rotation and scaling, to the
MX06 configuration (`k ≥ 1`). Unique and tied open-half-plane configurations
are completely positive (HP04–HP05), as is the closed half-plane (HP06).
-/

@[expose] public section

open Matrix Filter
open scoped Matrix Topology

namespace BollobasNikiforov

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]


noncomputable section

/-- The Gram matrix of a family of planar vectors. -/
def gram (z : n → Fin 2 → ℝ) : Matrix n n ℝ :=
  of fun i j => z i ⬝ᵥ z j

omit [Fintype n] [DecidableEq n] [LinearOrder n] in
@[simp]
lemma gram_apply (z : n → Fin 2 → ℝ) (i j : n) : gram z i j = z i ⬝ᵥ z j :=
  rfl

/-- Euclidean length of a vector in `ℝ²`. -/
def euclid (w : Fin 2 → ℝ) : ℝ :=
  Real.sqrt (w ⬝ᵥ w)

lemma euclid_inner_nonneg (w : Fin 2 → ℝ) : 0 ≤ w ⬝ᵥ w :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (w i)

lemma euclid_nonneg (w : Fin 2 → ℝ) : 0 ≤ euclid w :=
  Real.sqrt_nonneg _

lemma euclid_sq (w : Fin 2 → ℝ) : euclid w ^ 2 = w ⬝ᵥ w :=
  Real.sq_sqrt (euclid_inner_nonneg w)

lemma euclid_eq_zero (w : Fin 2 → ℝ) : euclid w = 0 ↔ w = 0 := by
  rw [euclid, Real.sqrt_eq_zero (euclid_inner_nonneg _), dotProduct_self_eq_zero]

lemma euclid_pos {w : Fin 2 → ℝ} (hw : w ≠ 0) : 0 < euclid w :=
  lt_of_le_of_ne (euclid_nonneg w) (Ne.symm (mt (euclid_eq_zero w).1 hw))

/-- Unit vector in the direction of a nonzero planar vector. -/
def normalize (w : Fin 2 → ℝ) : Fin 2 → ℝ :=
  (euclid w)⁻¹ • w

lemma normalize_inner {w : Fin 2 → ℝ} (hw : w ≠ 0) :
    normalize w ⬝ᵥ normalize w = 1 := by
  have hpos : euclid w ≠ 0 := (euclid_pos hw).ne'
  have : (euclid w)⁻¹ * (euclid w)⁻¹ * (w ⬝ᵥ w) = 1 := by
    rw [← euclid_sq, ← pow_two, ← mul_pow, inv_mul_cancel₀ hpos, one_pow]
  simp only [normalize, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rwa [← mul_assoc]

lemma smul_normalize {w : Fin 2 → ℝ} (hw : w ≠ 0) :
    euclid w • normalize w = w := by
  have hpos : euclid w ≠ 0 := (euclid_pos hw).ne'
  simp only [normalize, smul_smul]
  rw [mul_inv_cancel₀ hpos, one_smul]

/-- The 2-dimensional determinant `u₀ v₁ - u₁ v₀`. -/
def det2 (u v : Fin 2 → ℝ) : ℝ :=
  u 0 * v 1 - u 1 * v 0

lemma det2_smul_left (c : ℝ) (u v : Fin 2 → ℝ) : det2 (c • u) v = c * det2 u v := by
  simp [det2, smul_eq_mul]
  ring

lemma det2_smul_right (c : ℝ) (u v : Fin 2 → ℝ) : det2 u (c • v) = c * det2 u v := by
  simp [det2, smul_eq_mul]
  ring

lemma det2_zero_right (u : Fin 2 → ℝ) : det2 u 0 = 0 := by
  simp [det2]

/-- Rotate so that the unit vector `u` becomes the positive `x`-axis. -/
def rotateTo (u x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then u ⬝ᵥ x else det2 u x

lemma rotateTo_zero (u x : Fin 2 → ℝ) : rotateTo u x 0 = u ⬝ᵥ x := by
  simp [rotateTo]

lemma rotateTo_one (u x : Fin 2 → ℝ) : rotateTo u x 1 = det2 u x := by
  simp [rotateTo]

lemma rotateTo_apply_zero_vec (u : Fin 2 → ℝ) : rotateTo u 0 = 0 := by
  ext i
  simp [rotateTo, det2]

lemma rotateTo_inner (u x y : Fin 2 → ℝ) (hu : u ⬝ᵥ u = 1) :
    rotateTo u x ⬝ᵥ rotateTo u y = x ⬝ᵥ y := by
  have hu2 : u 0 ^ 2 + u 1 ^ 2 = 1 := by
    simpa [dotProduct, Fin.sum_univ_two, pow_two] using hu
  have hrot : rotateTo u x ⬝ᵥ rotateTo u y =
      (u ⬝ᵥ x) * (u ⬝ᵥ y) + det2 u x * det2 u y := by
    simp [rotateTo, dotProduct, Fin.sum_univ_two]
  have hid : (u ⬝ᵥ x) * (u ⬝ᵥ y) + det2 u x * det2 u y = x ⬝ᵥ y := by
    simp only [det2, dotProduct, Fin.sum_univ_two]
    convert_to (u 0 ^ 2 + u 1 ^ 2) * (x 0 * y 0 + x 1 * y 1) = x 0 * y 0 + x 1 * y 1 using 1
    · ring
    · rw [hu2, one_mul]
  exact hrot.trans hid

lemma rotateTo_eq_zero_iff (u x : Fin 2 → ℝ) (hu : u ⬝ᵥ u = 1) :
    rotateTo u x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have : x ⬝ᵥ x = 0 := by
      rw [← rotateTo_inner u x x hu, h]
      simp
    exact (dotProduct_self_eq_zero.mp this)
  · intro h
    simp [h, rotateTo_apply_zero_vec]

/-- If `α` is a right-half-plane unit vector of minimal second coordinate, then
every other such unit vector `γ` is counterclockwise from `α`. -/
lemma det2_nonneg_of_min_snd {α γ : Fin 2 → ℝ}
    (hα : α ⬝ᵥ α = 1) (hγ : γ ⬝ᵥ γ = 1)
    (hα0 : 0 ≤ α 0) (hγ0 : 0 ≤ γ 0) (hmin : α 1 ≤ γ 1) :
    0 ≤ det2 α γ := by
  have hαn : α 0 ^ 2 + α 1 ^ 2 = 1 := by
    simpa [dotProduct, Fin.sum_univ_two, pow_two] using hα
  have hγn : γ 0 ^ 2 + γ 1 ^ 2 = 1 := by
    simpa [dotProduct, Fin.sum_univ_two, pow_two] using hγ
  simp only [det2]
  rcases le_or_gt 0 (α 1) with hα1 | hα1
  · have hγ1 : 0 ≤ γ 1 := le_trans hα1 hmin
    have hγ0le : γ 0 ≤ α 0 := by
      apply le_of_sq_le_sq
      · have h1 : α 1 ^ 2 ≤ γ 1 ^ 2 := pow_le_pow_left₀ hα1 hmin 2
        linarith
      · exact hα0
    have h1 : α 0 * α 1 ≤ α 0 * γ 1 := mul_le_mul_of_nonneg_left hmin hα0
    have h2 : γ 0 * α 1 ≤ α 0 * α 1 := mul_le_mul_of_nonneg_right hγ0le hα1
    linarith
  · rcases le_or_gt (γ 1) 0 with hγ1 | hγ1
    · have hα0le : α 0 ≤ γ 0 := by
        apply le_of_sq_le_sq
        · have h1 : (-γ 1) ^ 2 ≤ (-α 1) ^ 2 :=
            pow_le_pow_left₀ (neg_nonneg.mpr hγ1) (neg_le_neg hmin) 2
          simp only [neg_sq] at h1
          linarith
        · exact hγ0
      have h1 : γ 0 * γ 1 ≤ α 0 * γ 1 := mul_le_mul_of_nonpos_right hα0le hγ1
      have h2 : -γ 1 * γ 0 ≤ -α 1 * γ 0 := mul_le_mul_of_nonneg_right (neg_le_neg hmin) hγ0
      linarith
    · have h1 : 0 ≤ α 0 * γ 1 := mul_nonneg hα0 hγ1.le
      have h2 : 0 ≤ -α 1 * γ 0 := mul_nonneg (neg_nonneg.mpr hα1.le) hγ0
      linarith

omit [DecidableEq n] [LinearOrder n] [Fintype n] in
variable [Finite n] in
lemma exists_nonneg_gram_factor (z : n → Fin 2 → ℝ)
    (hnn : ∀ i j, 0 ≤ z i ⬝ᵥ z j) :
    ∃ p q : n → ℝ, 0 ≤ p ∧ 0 ≤ q ∧
      gram z = vecMulVec p p + vecMulVec q q := by
  cases nonempty_fintype n
  by_cases hz : ∀ i, z i = 0
  · refine ⟨0, 0, le_rfl, le_rfl, ?_⟩
    ext i j
    simp [gram, hz i, hz j]
  · push Not at hz
    obtain ⟨k, hk⟩ := hz
    set u := normalize (z k)
    have hu : u ⬝ᵥ u = 1 := normalize_inner hk
    set w : n → Fin 2 → ℝ := fun i => rotateTo u (z i)
    have hw_inner (i j : n) : w i ⬝ᵥ w j = z i ⬝ᵥ z j :=
      rotateTo_inner u (z i) (z j) hu
    have hw0 (i : n) : 0 ≤ w i 0 := by
      have : w i 0 = u ⬝ᵥ z i := rotateTo_zero u (z i)
      rw [this]
      change 0 ≤ u ⬝ᵥ z i
      simp only [u, normalize, smul_dotProduct, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.mpr (euclid_nonneg _)) (hnn k i)
    let s := Finset.univ.filter (fun i : n => z i ≠ 0)
    have hs : s.Nonempty := ⟨k, by simp [s, hk]⟩
    obtain ⟨imin, himem, hmin⟩ :=
      s.exists_min_image (fun i => normalize (w i) 1) hs
    have hzmin : z imin ≠ 0 := by
      simpa [s, Finset.mem_filter] using himem
    have hwmin : w imin ≠ 0 :=
      mt (rotateTo_eq_zero_iff u (z imin) hu).mp hzmin
    set α := normalize (w imin)
    have hα : α ⬝ᵥ α = 1 := normalize_inner hwmin
    have hα0 : 0 ≤ α 0 := by
      simp only [normalize, Fin.isValue, Pi.smul_apply, smul_eq_mul, α]
      exact mul_nonneg (inv_nonneg.mpr (euclid_nonneg _)) (hw0 imin)
    refine ⟨fun i => α ⬝ᵥ w i, fun i => det2 α (w i), ?_, ?_, ?_⟩
    · intro i
      change 0 ≤ α ⬝ᵥ w i
      simp only [α, normalize, smul_dotProduct, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.mpr (euclid_nonneg _)) (by
        rw [hw_inner]
        exact hnn imin i)
    · intro i
      change 0 ≤ det2 α (w i)
      by_cases hzi : z i = 0
      · simp [w, hzi, rotateTo_apply_zero_vec, det2_zero_right]
      · have hwi : w i ≠ 0 := mt (rotateTo_eq_zero_iff u (z i) hu).mp hzi
        have hγ : normalize (w i) ⬝ᵥ normalize (w i) = 1 := normalize_inner hwi
        have hγ0 : 0 ≤ normalize (w i) 0 := by
          simp only [normalize, Fin.isValue, Pi.smul_apply, smul_eq_mul]
          exact mul_nonneg (inv_nonneg.mpr (euclid_nonneg _)) (hw0 i)
        have hord : α 1 ≤ normalize (w i) 1 :=
          hmin i (by simp [s, hzi])
        have hdet : 0 ≤ det2 α (normalize (w i)) :=
          det2_nonneg_of_min_snd hα hγ hα0 hγ0 hord
        have : det2 α (w i) = euclid (w i) * det2 α (normalize (w i)) := by
          calc
            det2 α (w i) = det2 α (euclid (w i) • normalize (w i)) := by
              rw [smul_normalize hwi]
            _ = euclid (w i) * det2 α (normalize (w i)) := det2_smul_right _ _ _
        rw [this]
        exact mul_nonneg (euclid_nonneg _) hdet
    · ext i j
      calc
        gram z i j = z i ⬝ᵥ z j := rfl
        _ = w i ⬝ᵥ w j := (hw_inner i j).symm
        _ = rotateTo α (w i) ⬝ᵥ rotateTo α (w j) :=
          (rotateTo_inner α (w i) (w j) hα).symm
        _ = (α ⬝ᵥ w i) * (α ⬝ᵥ w j) + det2 α (w i) * det2 α (w j) := by
          simp [rotateTo, dotProduct, Fin.sum_univ_two]
        _ = (vecMulVec (fun i => α ⬝ᵥ w i) (fun i => α ⬝ᵥ w i) +
              vecMulVec (fun i => det2 α (w i)) (fun i => det2 α (w i))) i j := by
          simp [vecMulVec_apply]

omit [Fintype n] [DecidableEq n] in
lemma laplacianCoeff_eq_zero_of_nonneg {X : Matrix n n ℝ}
    (h : ∀ i j, 0 ≤ X i j) (i j : n) : laplacianCoeff X i j = 0 := by
  unfold laplacianCoeff
  split_ifs with hcond
  · exact (not_lt.mpr (h i j) hcond.2).elim
  · rfl

lemma M_eq_hadamard_of_nonneg {X : Matrix n n ℝ} (h : ∀ i j, 0 ≤ X i j) :
    M X = X ⊙ X := by
  simp [M, laplacianCoeff_eq_zero_of_nonneg h]

omit [Fintype n] [DecidableEq n] [LinearOrder n] in
lemma hadamard_vecMulVec (p q : n → ℝ) :
    vecMulVec p p ⊙ vecMulVec q q = vecMulVec (p * q) (p * q) := by
  ext i j
  simp [hadamard_apply, vecMulVec_apply, Pi.mul_apply]
  ring

omit [Fintype n] [DecidableEq n] [LinearOrder n] in
lemma hadamard_add_self (A B : Matrix n n ℝ) :
    (A + B) ⊙ (A + B) = A ⊙ A + B ⊙ B + (2 : ℝ) • (A ⊙ B) := by
  ext i j
  simp [hadamard_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- **HP01.** If all planar inner products are nonnegative, then `M` of the
Gram matrix is completely positive. -/
lemma isCompletelyPositive_M_of_nonneg_inners (z : n → Fin 2 → ℝ)
    (hnn : ∀ i j, 0 ≤ z i ⬝ᵥ z j) :
    IsCompletelyPositive (M (gram z)) := by
  obtain ⟨p, q, hp, hq, hX⟩ := exists_nonneg_gram_factor z hnn
  have hXnn : ∀ i j, 0 ≤ gram z i j := fun i j => hnn i j
  rw [M_eq_hadamard_of_nonneg hXnn, hX, hadamard_add_self, hadamard_vecMulVec,
    hadamard_vecMulVec, hadamard_vecMulVec]
  refine ((isCompletelyPositive_vecMulVec ?_).add
      (isCompletelyPositive_vecMulVec ?_)).add
    ((isCompletelyPositive_vecMulVec ?_).smul (by norm_num : (0 : ℝ) ≤ 2))
  · intro i
    simp only [Pi.zero_apply, Pi.mul_apply]
    exact mul_nonneg (hp i) (hp i)
  · intro i
    simp only [Pi.zero_apply, Pi.mul_apply]
    exact mul_nonneg (hq i) (hq i)
  · intro i
    simp only [Pi.zero_apply, Pi.mul_apply]
    exact mul_nonneg (hp i) (hq i)

/-- **HP03.** Completely positivity of `M X` is invariant under positive
square scalings of `X`. -/
lemma isCompletelyPositive_M_smul_sq_iff {c : ℝ} (hc : 0 < c) (X : Matrix n n ℝ) :
    IsCompletelyPositive (M X) ↔ IsCompletelyPositive (M ((c ^ 2) • X)) := by
  rw [M_smul_sq hc.le]
  constructor
  · exact fun h => h.smul (pow_nonneg hc.le 4)
  · intro h
    have hc4 : (c ^ 4) ≠ 0 := pow_ne_zero 4 hc.ne'
    have : M X = (c ^ 4)⁻¹ • ((c ^ 4) • M X) :=
      (inv_smul_smul₀ hc4 (M X)).symm
    rw [this]
    exact h.smul (inv_nonneg.mpr (pow_nonneg hc.le 4))

/-! ### HP07 — delete zero Gram vectors -/

omit [Fintype n] [DecidableEq n] [LinearOrder n] in
lemma gram_isSymm (z : n → Fin 2 → ℝ) : (gram z).IsSymm :=
  IsSymm.ext fun i j => dotProduct_comm (z j) (z i)

omit [Fintype n] [DecidableEq n] [LinearOrder n] in
lemma gram_eq_zero_of_left {z : n → Fin 2 → ℝ} {i : n} (hi : z i = 0) (j : n) :
    gram z i j = 0 := by
  simp [gram, hi]

omit [Fintype n] [DecidableEq n] [LinearOrder n] in
lemma gram_eq_zero_of_right {z : n → Fin 2 → ℝ} {j : n} (hj : z j = 0) (i : n) :
    gram z i j = 0 := by
  simp [gram, hj]

omit [Fintype n] [DecidableEq n] [LinearOrder n] in
lemma gram_submatrix {ι : Type*} (z : n → Fin 2 → ℝ) (e : ι → n) :
    (gram z).submatrix e e = gram (z ∘ e) := by
  ext i j
  simp [gram, submatrix_apply]

omit [Fintype n] in
lemma laplacianCoeff_add_of_isSymm (X : Matrix n n ℝ) (hX : X.IsSymm) (i j : n) :
    laplacianCoeff X i j + laplacianCoeff X j i =
      if i ≠ j ∧ X i j < 0 then (X i j) ^ 2 else 0 := by
  unfold laplacianCoeff
  rcases eq_or_ne i j with rfl | hij
  · simp
  · rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · have : ¬ j < i := not_lt.mpr hijlt.le
      simp [hij, hijlt, this]
    · have : ¬ i < j := not_lt.mpr hjilt.le
      simp [hij, this, hjilt, hX.apply i j]

omit [Fintype n] [LinearOrder n] in
lemma vecMulVec_edge_diag (p q i : n) :
    vecMulVec (e p - e q) (e p - e q) i i =
      if p ≠ q ∧ (p = i ∨ q = i) then (1 : ℝ) else 0 := by
  rcases eq_or_ne p q with hpq | hpq
  · subst hpq
    simp [vecMulVec_apply]
  · simp only [vecMulVec_apply, Pi.sub_apply, e, Pi.single_apply]
    rcases eq_or_ne i p with hip | hip
    · subst hip
      simp [hpq]
    · rcases eq_or_ne i q with hiq | hiq
      · subst hiq
        simp [hpq, hip]
      · simp [hip, hiq, Ne.symm hip, Ne.symm hiq]

lemma M_apply_diag_of_isSymm (X : Matrix n n ℝ) (hX : X.IsSymm) (i : n) :
    M X i i =
      X i i * X i i +
        ∑ j : n, if i ≠ j ∧ X i j < 0 then (X i j) ^ 2 else 0 := by
  rw [M_apply]
  congr 1
  have hterm (p q : n) :
      laplacianCoeff X p q * vecMulVec (e p - e q) (e p - e q) i i =
        if p ≠ q ∧ (p = i ∨ q = i) then laplacianCoeff X p q else 0 := by
    rw [vecMulVec_edge_diag]
    split_ifs <;> simp
  have hdecomp (p q : n) :
      (if p ≠ q ∧ (p = i ∨ q = i) then laplacianCoeff X p q else 0) =
        (if p = i ∧ q ≠ i then laplacianCoeff X i q else 0) +
          (if q = i ∧ p ≠ i then laplacianCoeff X p i else 0) := by
    by_cases hp : p = i
    · by_cases hq : q = i
      · simp [hp, hq]
      · simp only [hp, ne_eq, hq, or_false, and_true, ite_not, not_false_eq_true, and_self,
        ↓reduceIte, not_true_eq_false, add_zero, ite_eq_right_iff]
        exact fun h => (hq h.symm).elim
    · by_cases hq : q = i
      · have hne : p ≠ q := fun h => hp (h.trans hq)
        simp [hp, hq]
      · simp [hp, hq]
  simp_rw [hterm, hdecomp, Finset.sum_add_distrib]
  have hL : ∑ p : n, ∑ q : n,
        (if p = i ∧ q ≠ i then laplacianCoeff X i q else 0) =
      ∑ j : n, if i ≠ j then laplacianCoeff X i j else 0 := by
    rw [Fintype.sum_eq_single i]
    · simp [ne_comm]
    · intro p hp
      simp [hp]
  have hR : ∑ p : n, ∑ q : n,
        (if q = i ∧ p ≠ i then laplacianCoeff X p i else 0) =
      ∑ j : n, if i ≠ j then laplacianCoeff X j i else 0 := by
    have hswap :
        ∑ p : n, ∑ q : n, (if q = i ∧ p ≠ i then laplacianCoeff X p i else 0) =
          ∑ q : n, ∑ p : n, (if q = i ∧ p ≠ i then laplacianCoeff X p i else 0) :=
      Finset.sum_comm
    rw [hswap, Fintype.sum_eq_single i]
    · simp [ne_comm]
    · intro q hq
      simp [hq]
  rw [hL, hR, ← Finset.sum_add_distrib]
  refine Fintype.sum_congr _ _ fun j => ?_
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, laplacianCoeff_add_of_isSymm X hX]

/-- A zero row and column of `X` remain zero in `M X`. -/
lemma M_eq_zero_of_row_col_zero {X : Matrix n n ℝ} {i0 : n}
    (hrow : ∀ j, X i0 j = 0) (hcol : ∀ j, X j i0 = 0) (j : n) :
    M X i0 j = 0 := by
  rcases eq_or_ne i0 j with rfl | hij
  · rw [M_apply]
    simp only [hrow i0, mul_zero, add_eq_left]
    refine Fintype.sum_eq_zero _ fun p => Fintype.sum_eq_zero _ fun q => ?_
    have hlap_row : laplacianCoeff X i0 q = 0 := by
      unfold laplacianCoeff
      simp [hrow q]
    have hlap_col : laplacianCoeff X p i0 = 0 := by
      unfold laplacianCoeff
      simp [hcol p]
    rw [vecMulVec_edge_diag]
    split_ifs with hcond
    · rcases hcond.2 with hp | hq
      · simpa [hp] using hlap_row
      · simpa [hq] using hlap_col
    · simp
  · rw [M_apply, laplacianCoeff_correction_offDiag X hij]
    unfold laplacianCoeff
    simp [hrow j, hcol j]

lemma M_eq_zero_of_col_row_zero {X : Matrix n n ℝ} {i0 : n}
    (hrow : ∀ j, X i0 j = 0) (hcol : ∀ j, X j i0 = 0) (j : n) :
    M X j i0 = 0 := by
  rcases eq_or_ne j i0 with rfl | hij
  · exact M_eq_zero_of_row_col_zero hrow hcol _
  · rw [M_apply, laplacianCoeff_correction_offDiag X hij]
    unfold laplacianCoeff
    simp [hrow j, hcol j]

omit [LinearOrder n] [DecidableEq n] in
lemma sum_comp_injective {ι : Type*} [Fintype ι]
    (σ : ι → n) (hσ : Function.Injective σ) (f : n → ℝ)
    (hf : ∀ j, j ∉ Set.range σ → f j = 0) :
    ∑ j : n, f j = ∑ a : ι, f (σ a) := by
  classical
  have hd : Disjoint (Finset.univ.image σ)
      (Finset.univ.filter fun j : n => j ∉ Set.range σ) := by
    refine Finset.disjoint_left.2 ?_
    intro j hj1 hj2
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hj1
    exact (Finset.mem_filter.mp hj2).2 ⟨a, rfl⟩
  have hu : Finset.univ.image σ ∪ Finset.univ.filter (fun j : n => j ∉ Set.range σ) =
      Finset.univ := by
    ext j
    constructor
    · intro
      exact Finset.mem_univ j
    · intro
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and]
      by_cases hj : j ∈ Set.range σ
      · exact Or.inl (Set.mem_range.mp hj)
      · exact Or.inr hj
  calc
    ∑ j : n, f j =
        ∑ j ∈ Finset.univ.image σ, f j +
          ∑ j ∈ Finset.univ.filter (fun j : n => j ∉ Set.range σ), f j := by
      rw [← Finset.sum_union hd, hu]
    _ = ∑ a : ι, f (σ a) + 0 := by
      rw [Finset.sum_image (fun _ _ _ _ hxy => hσ hxy)]
      congr 1
      exact Finset.sum_eq_zero fun j hj => hf j (by simpa using hj)
    _ = ∑ a : ι, f (σ a) := add_zero _

lemma M_eq_zero_of_not_mem_range {ι : Type*}
    {X : Matrix n n ℝ} (hX : X.IsSymm) {e : ι → n}
    (hzero : ∀ i, i ∉ Set.range e → ∀ j, X i j = 0)
    {i : n} (hi : i ∉ Set.range e) (j : n) :
    M X i j = 0 := by
  have hrow : ∀ k, X i k = 0 := hzero i hi
  have hcol : ∀ k, X k i = 0 := fun k => (hX.apply i k).symm ▸ hzero i hi k
  exact M_eq_zero_of_row_col_zero hrow hcol j

lemma M_eq_zero_of_not_mem_range_right {ι : Type*}
    {X : Matrix n n ℝ} (hX : X.IsSymm) {e : ι → n}
    (hzero : ∀ i, i ∉ Set.range e → ∀ j, X i j = 0)
    {j : n} (hj : j ∉ Set.range e) (i : n) :
    M X i j = 0 := by
  have hrow : ∀ k, X j k = 0 := hzero j hj
  have hcol : ∀ k, X k j = 0 := fun k => (hX.apply j k).symm ▸ hzero j hj k
  exact M_eq_zero_of_col_row_zero hrow hcol i

/-- If `X` is symmetric and vanishes off the image of an injection `e`, then
`M` commutes with taking the principal submatrix along `e`. -/
lemma M_submatrix_eq_of_zero_outside {ι : Type*}
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {X : Matrix n n ℝ} (hX : X.IsSymm) {e : ι → n} (he : Function.Injective e)
    (hzero : ∀ i, i ∉ Set.range e → ∀ j, X i j = 0) :
    (M X).submatrix e e = M (X.submatrix e e) := by
  ext a b
  rcases eq_or_ne a b with rfl | hab
  · have hXee : (X.submatrix e e).IsSymm := hX.submatrix e
    rw [submatrix_apply, M_apply_diag_of_isSymm X hX, M_apply_diag_of_isSymm _ hXee]
    simp only [submatrix_apply]
    congr 1
    refine (sum_comp_injective e he
        (fun j => if e a ≠ j ∧ X (e a) j < 0 then (X (e a) j) ^ 2 else 0) ?_).trans ?_
    · intro j hj
      have hx : X (e a) j = 0 := (hX.apply (e a) j).symm ▸ hzero j hj (e a)
      simp [hx]
    · refine Fintype.sum_congr _ _ fun c => ?_
      simp [he.ne_iff]
      rfl
  · have hab' : e a ≠ e b := he.ne hab
    have hXee : (X.submatrix e e).IsSymm := hX.submatrix e
    rw [submatrix_apply, M_apply_of_ne X hX hab', M_apply_of_ne _ hXee hab]
    simp [posPart_apply, submatrix_apply]

/-- **HP07.** Completely positivity of `M X` is unchanged by deleting zero
rows/columns along an injection. -/
lemma isCompletelyPositive_M_iff_submatrix {ι : Type*}
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {X : Matrix n n ℝ} (hX : X.IsSymm) {e : ι → n} (he : Function.Injective e)
    (hzero : ∀ i, i ∉ Set.range e → ∀ j, X i j = 0) :
    IsCompletelyPositive (M X) ↔ IsCompletelyPositive (M (X.submatrix e e)) := by
  constructor
  · intro h
    simpa [M_submatrix_eq_of_zero_outside hX he hzero] using h.submatrix e
  · intro h
    refine isCompletelyPositive_of_submatrix_pad he ?hCD ?hzeroM ?hMsym h
    · intro a b
      rw [← submatrix_apply (M X) e e, M_submatrix_eq_of_zero_outside hX he hzero]
    · intro i hi j
      exact M_eq_zero_of_not_mem_range hX hzero hi j
    · refine IsSymm.ext fun i j => ?_
      rcases eq_or_ne i j with rfl | hij
      · rfl
      · rw [M_apply_of_ne X hX hij, M_apply_of_ne X hX hij.symm]
        simp [posPart_apply, hX.apply]

/-- **HP07** for planar Grams: drop the zero vectors. -/
lemma isCompletelyPositive_M_gram_iff_nonzero (z : n → Fin 2 → ℝ) :
    IsCompletelyPositive (M (gram z)) ↔
      IsCompletelyPositive (M (gram fun i : {i // z i ≠ 0} => z i)) := by
  have he : Function.Injective (fun i : {i // z i ≠ 0} => (i : n)) :=
    Subtype.val_injective
  have hzero : ∀ i, i ∉ Set.range (fun i : {i // z i ≠ 0} => (i : n)) →
      ∀ j, gram z i j = 0 := by
    intro i hi j
    have hz : z i = 0 := by
      contrapose! hi
      exact ⟨⟨i, hi⟩, rfl⟩
    exact gram_eq_zero_of_left hz j
  rw [isCompletelyPositive_M_iff_submatrix (gram_isSymm z) he hzero, gram_submatrix]
  rfl

/-! ### HP02 — unique supporting vector reduces to MX06 -/

lemma eq_of_fin2 {v w : Fin 2 → ℝ} (h0 : v 0 = w 0) (h1 : v 1 = w 1) : v = w :=
  funext (Fin.forall_fin_two.mpr ⟨h0, h1⟩)

lemma rotateTo_smul (u : Fin 2 → ℝ) (c : ℝ) (x : Fin 2 → ℝ) :
    rotateTo u (c • x) = c • rotateTo u x := by
  refine eq_of_fin2 ?_ ?_
  · simp [rotateTo, smul_eq_mul]
  · simp [rotateTo, det2_smul_right, smul_eq_mul]

lemma rotateTo_eq_z0 (u : Fin 2 → ℝ) (hu : u ⬝ᵥ u = 1) :
    rotateTo u u = z0 := by
  refine eq_of_fin2 ?_ ?_
  · simpa [rotateTo, z0] using hu
  · simp [rotateTo, z0, det2]
    ring

lemma rotateTo_normalize_self {v : Fin 2 → ℝ} (hv : v ≠ 0) :
    rotateTo (normalize v) v = euclid v • z0 := by
  calc
    rotateTo (normalize v) v
        = rotateTo (normalize v) (euclid v • normalize v) := by
          rw [smul_normalize hv]
    _ = euclid v • rotateTo (normalize v) (normalize v) :=
          rotateTo_smul _ _ _
    _ = euclid v • z0 := by
          rw [rotateTo_eq_z0 _ (normalize_inner hv)]

lemma smul_rotateTo_normalize_self {v : Fin 2 → ℝ} (hv : v ≠ 0) :
    (euclid v)⁻¹ • rotateTo (normalize v) v = z0 := by
  rw [rotateTo_normalize_self hv, smul_smul, inv_mul_cancel₀ (euclid_pos hv).ne',
    one_smul]

omit [Fintype n] [DecidableEq n] [LinearOrder n] in
lemma gram_rotateTo (u : Fin 2 → ℝ) (hu : u ⬝ᵥ u = 1) (z : n → Fin 2 → ℝ) :
    gram (fun i => rotateTo u (z i)) = gram z := by
  ext i j
  simp [gram, rotateTo_inner u _ _ hu]

omit [Fintype n] [DecidableEq n] [LinearOrder n] in
lemma gram_smul_vec (c : ℝ) (z : n → Fin 2 → ℝ) :
    gram (fun i => c • z i) = (c ^ 2) • gram z := by
  ext i j
  simp [gram, smul_dotProduct, dotProduct_smul, smul_eq_mul, pow_two, mul_assoc]

lemma eq_zVec_coords {k : ℕ} (s t : Fin k → ℝ) (i : Fin k) {v : Fin 2 → ℝ}
    (h0 : v 0 < 0) (hs : s i = v 0 ^ 2) (ht : t i = v 1 / -v 0) :
    v = zVec s t i := by
  have hsqrt : Real.sqrt (s i) = -v 0 := by
    rw [hs, Real.sqrt_sq_eq_abs, abs_of_neg h0]
  refine eq_of_fin2 ?_ ?_
  · simp [zVec, hsqrt]
  · simp [zVec, hsqrt, ht]
    field_simp [h0.ne]

lemma eq_yVec_coords {p : ℕ} (ρ x : Fin p → ℝ) (j : Fin p) {v : Fin 2 → ℝ}
    (h1 : 0 < v 1) (hρ : ρ j = v 1 ^ 2) (hx : x j = v 0 / v 1) :
    v = yVec ρ x j := by
  have hsqrt : Real.sqrt (ρ j) = v 1 := by
    rw [hρ, Real.sqrt_sq_eq_abs, abs_of_pos h1]
  refine eq_of_fin2 ?_ ?_
  · simp [yVec, hsqrt, hx]
    field_simp
  · simp [yVec, hsqrt]

/-- Left indices in the rotated frame: strictly negative first coordinate. -/
def configLeft (z : n → Fin 2 → ℝ) : Finset n :=
  Finset.univ.filter (fun i => z i 0 < 0)

/-- Right indices: nonnegative first coordinate, excluding the unique axis vector. -/
def configRight (z : n → Fin 2 → ℝ) (i0 : n) : Finset n :=
  Finset.univ.filter (fun i => i ≠ i0 ∧ 0 ≤ z i 0)

omit [DecidableEq n] [LinearOrder n] in
lemma not_mem_configLeft_of_z0 {z : n → Fin 2 → ℝ} {i0 : n}
    (hz0 : z i0 = z0) : i0 ∉ configLeft z := by
  simp [configLeft, hz0, z0]

omit [DecidableEq n] [LinearOrder n] in
lemma mem_configLeft_iff {z : n → Fin 2 → ℝ} {i : n} :
    i ∈ configLeft z ↔ z i 0 < 0 := by
  simp [configLeft]

omit [LinearOrder n] in
lemma mem_configRight_iff {z : n → Fin 2 → ℝ} {i0 i : n} :
    i ∈ configRight z i0 ↔ i ≠ i0 ∧ 0 ≤ z i 0 := by
  simp [configRight]

omit [LinearOrder n] in
lemma mem_configRight_of_not_left {z : n → Fin 2 → ℝ} {i0 i : n}
    (hi0 : i ≠ i0) (hl : i ∉ configLeft z) : i ∈ configRight z i0 := by
  rw [mem_configRight_iff]
  exact ⟨hi0, le_of_not_gt (mt mem_configLeft_iff.mpr hl)⟩

omit [DecidableEq n] [Fintype n] in
variable [Finite n] in
/-- **HP02**, rotated frame: unique contact `z i0 = (1,0)`, all other vectors
strictly above the axis, and at least one left vector. The data match MX06. -/
lemma exists_config_of_rotated_unique (z : n → Fin 2 → ℝ) (i0 : n)
    (hz0 : z i0 = z0) (hup : ∀ i, i ≠ i0 → 0 < z i 1)
    (hleft : ∃ i, z i 0 < 0) :
    ∃ (k p : ℕ) (_ : 0 < k) (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
      (e : n ≃ ConfigIdx k p),
      (∀ i, 0 < s i) ∧ (∀ i, 0 < t i) ∧ (∀ j, 0 < ρ j) ∧ (∀ j, 0 ≤ x j) ∧
        ∀ i, z i = configVec s t ρ x (e i) := by
  cases nonempty_fintype n
  let left := configLeft z
  let right := configRight z i0
  let k := left.card
  let p := right.card
  have hleftNE : left.Nonempty := by
    obtain ⟨i, hi⟩ := hleft
    exact ⟨i, mem_configLeft_iff.mpr hi⟩
  have hk : 0 < k := Finset.card_pos.mpr hleftNE
  have hi0L : i0 ∉ left := not_mem_configLeft_of_z0 hz0
  let eL : {i // i ∈ left} ≃ Fin k := (left.orderIsoOfFin rfl).toEquiv.symm
  let eR : {j // j ∈ right} ≃ Fin p := (right.orderIsoOfFin rfl).toEquiv.symm
  let s : Fin k → ℝ := fun i => z (eL.symm i) 0 ^ 2
  let t : Fin k → ℝ := fun i => z (eL.symm i) 1 / -z (eL.symm i) 0
  let ρ : Fin p → ℝ := fun j => z (eR.symm j) 1 ^ 2
  let x : Fin p → ℝ := fun j => z (eR.symm j) 0 / z (eR.symm j) 1
  have hs : ∀ i, 0 < s i := by
    intro i
    exact sq_pos_of_ne_zero (mem_configLeft_iff.mp (eL.symm i).property).ne
  have ht : ∀ i, 0 < t i := by
    intro i
    have hmem := (eL.symm i).property
    have hneg := mem_configLeft_iff.mp hmem
    have hne : (eL.symm i : n) ≠ i0 := fun h => hi0L (h ▸ hmem)
    exact div_pos (hup _ hne) (neg_pos.mpr hneg)
  have hρ : ∀ j, 0 < ρ j := by
    intro j
    exact sq_pos_of_pos (hup _ (mem_configRight_iff.mp (eR.symm j).property).1)
  have hx : ∀ j, 0 ≤ x j := by
    intro j
    have hr := mem_configRight_iff.mp (eR.symm j).property
    exact div_nonneg hr.2 (hup _ hr.1).le
  let fromIdx : ConfigIdx k p → n := fun α =>
    match configIdxEquiv k p α with
    | Sum.inl none => i0
    | Sum.inl (some i) => (eL.symm i : n)
    | Sum.inr j => (eR.symm j : n)
  let toIdx : n → ConfigIdx k p := fun i =>
    if hi0 : i = i0 then idxZ0
    else if hl : i ∈ left then idxZ (eL ⟨i, hl⟩)
    else idxY (eR ⟨i, mem_configRight_of_not_left hi0 hl⟩)
  have hleft_inv : ∀ i, fromIdx (toIdx i) = i := by
    intro i
    by_cases hi0 : i = i0
    · subst hi0
      simp [toIdx, fromIdx, idxZ0]
    · by_cases hl : i ∈ left
      · simp [toIdx, fromIdx, idxZ, hi0, hl]
      · simp [toIdx, fromIdx, idxY, hi0, hl]
  have hright_inv : ∀ α, toIdx (fromIdx α) = α := by
    intro α
    rw [← (configIdxEquiv k p).symm_apply_apply α]
    rcases hα : configIdxEquiv k p α with o | j
    · rcases o with _ | i
      · simp [fromIdx, toIdx, idxZ0]
      · have hl : (eL.symm i : n) ∈ left := (eL.symm i).property
        have hi0 : (eL.symm i : n) ≠ i0 := fun h => hi0L (h ▸ hl)
        simp [fromIdx, toIdx, idxZ, hi0, hl]
    · have hr : (eR.symm j : n) ∈ right := (eR.symm j).property
      have hi0 : (eR.symm j : n) ≠ i0 := (mem_configRight_iff.mp hr).1
      have hl : (eR.symm j : n) ∉ left := fun hL =>
        not_lt.mpr (mem_configRight_iff.mp hr).2 (mem_configLeft_iff.mp hL)
      simp [fromIdx, toIdx, idxY, hi0, hl]
  let e : n ≃ ConfigIdx k p := ⟨toIdx, fromIdx, hleft_inv, hright_inv⟩
  refine ⟨k, p, hk, s, t, ρ, x, e, hs, ht, hρ, hx, ?_⟩
  intro i
  by_cases hi0 : i = i0
  · rw [hi0]
    change z i0 = configVec s t ρ x (toIdx i0)
    simp only [↓reduceDIte, configVec_z0, toIdx]
    exact hz0
  · by_cases hl : i ∈ left
    · change z i = configVec s t ρ x (toIdx i)
      simp only [hi0, ↓reduceDIte, hl, configVec_z, toIdx]
      refine eq_zVec_coords s t (eL ⟨i, hl⟩) (mem_configLeft_iff.mp hl) ?_ ?_
      · simp [s]
      · simp [t]
    · have hr : i ∈ right := mem_configRight_of_not_left hi0 hl
      change z i = configVec s t ρ x (toIdx i)
      simp only [hi0, ↓reduceDIte, hl, configVec_y, toIdx]
      refine eq_yVec_coords ρ x (eR ⟨i, hr⟩) (hup i hi0) ?_ ?_
      · simp [ρ]
      · simp [x]

omit [Fintype n] [DecidableEq n] [LinearOrder n] in
lemma gram_eq_Xconfig_submatrix {k p : ℕ}
    {s t : Fin k → ℝ} {ρ x : Fin p → ℝ} {e : n ≃ ConfigIdx k p}
    {z : n → Fin 2 → ℝ} (hz : ∀ i, z i = configVec s t ρ x (e i)) :
    gram z = (Xconfig s t ρ x).submatrix e e := by
  ext i j
  simp [gram, submatrix_apply, Xconfig, hz]

omit [DecidableEq n] [Fintype n] in
variable [Finite n] in
/-- **HP02.** Open half-plane, a negative pair, and a unique supporting
direction: after rotation and positive scaling the vectors match MX06
with `k ≥ 1`. -/
lemma exists_config_of_unique_minimizer (z : n → Fin 2 → ℝ)
    (hnz : ∀ i, z i ≠ 0)
    (hopen : ∃ w : Fin 2 → ℝ, w ≠ 0 ∧ ∀ i, 0 < w ⬝ᵥ z i)
    (hneg : ∃ i j, z i ⬝ᵥ z j < 0) (i0 : n)
    (hside : ∀ i, 0 ≤ det2 (normalize (z i0)) (z i))
    (huniq : ∀ i, det2 (normalize (z i0)) (z i) = 0 → i = i0) :
    ∃ (k p : ℕ) (_ : 0 < k) (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
      (e : n ≃ ConfigIdx k p) (c : ℝ),
      0 < c ∧ (∀ i, 0 < s i) ∧ (∀ i, 0 < t i) ∧ (∀ j, 0 < ρ j) ∧ (∀ j, 0 ≤ x j) ∧
        ∀ i, c • rotateTo (normalize (z i0)) (z i) = configVec s t ρ x (e i) := by
  obtain ⟨w, hw0, hw⟩ := hopen
  have := hw i0
  set u := normalize (z i0)
  set c := (euclid (z i0))⁻¹
  have hc : 0 < c := inv_pos.mpr (euclid_pos (hnz i0))
  have hu : u ⬝ᵥ u = 1 := normalize_inner (hnz i0)
  let z' : n → Fin 2 → ℝ := fun i => c • rotateTo u (z i)
  have hz0' : z' i0 = z0 := smul_rotateTo_normalize_self (hnz i0)
  have hup' : ∀ i, i ≠ i0 → 0 < z' i 1 := by
    intro i hi
    have hdet : 0 < det2 u (z i) :=
      lt_of_le_of_ne (hside i) fun h => hi (huniq i h.symm)
    simpa [z', u, c, rotateTo, smul_eq_mul] using mul_pos hc hdet
  have h1 : ∀ i, 0 ≤ z' i 1 := by
    intro i
    rcases eq_or_ne i i0 with rfl | hi
    · simp [hz0']
    · exact (hup' i hi).le
  have hleft' : ∃ i, z' i 0 < 0 := by
    obtain ⟨a, b, hab⟩ := hneg
    have hgram : z' a ⬝ᵥ z' b = c ^ 2 * (z a ⬝ᵥ z b) := by
      simp only [z', smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [rotateTo_inner u (z a) (z b) hu]
      ring
    have hneg' : z' a ⬝ᵥ z' b < 0 := by
      rw [hgram]
      exact mul_neg_of_pos_of_neg (sq_pos_of_pos hc) hab
    by_contra hall
    push Not at hall
    have hnn : 0 ≤ z' a ⬝ᵥ z' b := by
      simp [dotProduct, Fin.sum_univ_two]
      nlinarith [hall a, hall b, h1 a, h1 b]
    exact not_le.mpr hneg' hnn
  obtain ⟨k, p, hk, s, t, ρ, x, e, hs, ht, hρ, hx, hz'⟩ :=
    exists_config_of_rotated_unique z' i0 hz0' hup' hleft'
  exact ⟨k, p, hk, s, t, ρ, x, e, c, hc, hs, ht, hρ, hx, hz'⟩

/-! ### HP04 — unique minimizer implies `M (gram z)` is CP -/

/-- Permute the left (`zᵢ`) indices of a configuration. -/
def permIdx {k p : ℕ} (σ : Equiv.Perm (Fin k)) : ConfigIdx k p ≃ ConfigIdx k p where
  toFun α :=
    match configIdxEquiv k p α with
    | Sum.inl none => idxZ0
    | Sum.inl (some i) => idxZ (σ i)
    | Sum.inr j => idxY j
  invFun α :=
    match configIdxEquiv k p α with
    | Sum.inl none => idxZ0
    | Sum.inl (some i) => idxZ (σ.symm i)
    | Sum.inr j => idxY j
  left_inv α := by
    rw [← (configIdxEquiv k p).symm_apply_apply α]
    rcases configIdxEquiv k p α with o | j
    · rcases o with _ | i
      · simp [idxZ0]
      · simp [idxZ]
    · simp [idxY]
  right_inv α := by
    rw [← (configIdxEquiv k p).symm_apply_apply α]
    rcases configIdxEquiv k p α with o | j
    · rcases o with _ | i
      · simp [idxZ0]
      · simp [idxZ]
    · simp [idxY]

lemma permIdx_z0 {k p : ℕ} (σ : Equiv.Perm (Fin k)) :
    permIdx (p := p) σ idxZ0 = idxZ0 := by
  simp [permIdx, idxZ0]

lemma permIdx_z {k p : ℕ} (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    permIdx (p := p) σ (idxZ i) = idxZ (σ i) := by
  simp [permIdx, idxZ]

lemma permIdx_y {k p : ℕ} (σ : Equiv.Perm (Fin k)) (j : Fin p) :
    permIdx (k := k) σ (idxY j) = idxY j := by
  simp [permIdx, idxY]

lemma configVec_permIdx {k p : ℕ} (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (σ : Equiv.Perm (Fin k)) (α : ConfigIdx k p) :
    configVec (s ∘ σ) (t ∘ σ) ρ x α = configVec s t ρ x (permIdx σ α) := by
  rw [← (configIdxEquiv k p).symm_apply_apply α]
  rcases configIdxEquiv k p α with o | j
  · rcases o with _ | i
    · simp [permIdx, configVec, idxZ0]
    · simp [permIdx, configVec, idxZ]
      rfl
  · simp [permIdx, configVec, idxY]

lemma Xconfig_permIdx {k p : ℕ} (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (σ : Equiv.Perm (Fin k)) :
    Xconfig (s ∘ σ) (t ∘ σ) ρ x =
      (Xconfig s t ρ x).submatrix (permIdx σ) (permIdx σ) := by
  ext α β
  simp [Xconfig, submatrix_apply, configVec_permIdx]

lemma Xconfig_unperm {k p : ℕ} (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
    (σ : Equiv.Perm (Fin k)) :
    Xconfig s t ρ x =
      (Xconfig (s ∘ σ) (t ∘ σ) ρ x).submatrix (permIdx σ).symm (permIdx σ).symm := by
  rw [Xconfig_permIdx]
  ext α β
  simp [submatrix_apply]

lemma isCompletelyPositive_M_Xconfig_sorted {k p : ℕ} [NeZero k]
    (s t : Fin k → ℝ) (ρ x : Fin p → ℝ) (hs : ∀ i, 0 < s i)
    (ht : ∀ i, 0 < t i) (hρ : ∀ j, 0 < ρ j) (hx : ∀ j, 0 ≤ x j) :
    IsCompletelyPositive (M (Xconfig s t ρ x)) := by
  let σ := Tuple.sort t
  let s' := s ∘ σ
  let t' := t ∘ σ
  have hs' : ∀ i, 0 < s' i := fun i => hs _
  have ht' : ∀ i, 0 < t' i := fun i => ht _
  have hmono : Monotone t' := Tuple.monotone_sort t
  have hCP : IsCompletelyPositive (M (Xconfig s' t' ρ x)) := by
    by_cases hp : p = 0
    · subst hp
      exact isCompletelyPositive_M_Xconfig_of_p_eq_zero s' t' ρ x hs' ht' hmono
    · have hγnn := configγ_nonneg s' t' hρ x hs'
      rcases hγnn.eq_or_lt with hγ0 | hγpos
      · exact isCompletelyPositive_M_Xconfig_of_configγ_eq_zero s' t' ρ x
          hs' ht' hmono hρ hx hγ0.symm
      · exact isCompletelyPositive_M_Xconfig s' t' ρ x hs' ht' hmono hρ hx hγpos
  have he : Function.Injective ((permIdx (p := p) σ).symm : ConfigIdx k p → ConfigIdx k p) :=
    Equiv.injective _
  have hzero : ∀ α, α ∉ Set.range ((permIdx (p := p) σ).symm : ConfigIdx k p → ConfigIdx k p) →
      ∀ β, Xconfig s' t' ρ x α β = 0 := by
    intro α hα
    exact (hα ⟨permIdx σ α, Equiv.symm_apply_apply _ _⟩).elim
  rw [Xconfig_unperm s t ρ x σ]
  exact (isCompletelyPositive_M_iff_submatrix (n := ConfigIdx k p)
      (Xconfig_isSymm s' t' ρ x) he hzero).mp hCP

/-- **HP04.** Open half-plane, a negative pair, and a unique supporting
direction: `M` of the Gram matrix is completely positive. -/
lemma isCompletelyPositive_M_of_unique_minimizer (z : n → Fin 2 → ℝ)
    (hnz : ∀ i, z i ≠ 0)
    (hopen : ∃ w : Fin 2 → ℝ, w ≠ 0 ∧ ∀ i, 0 < w ⬝ᵥ z i)
    (hneg : ∃ i j, z i ⬝ᵥ z j < 0) (i0 : n)
    (hside : ∀ i, 0 ≤ det2 (normalize (z i0)) (z i))
    (huniq : ∀ i, det2 (normalize (z i0)) (z i) = 0 → i = i0) :
    IsCompletelyPositive (M (gram z)) := by
  obtain ⟨k, p, hk, s, t, ρ, x, e, c, hc, hs, ht, hρ, hx, hz⟩ :=
    exists_config_of_unique_minimizer z hnz hopen hneg i0 hside huniq
  have : NeZero k := ⟨hk.ne'⟩
  set u := normalize (z i0)
  have hu : u ⬝ᵥ u = 1 := normalize_inner (hnz i0)
  let z' : n → Fin 2 → ℝ := fun i => c • rotateTo u (z i)
  have hgram : gram z' = (c ^ 2) • gram z := by
    change gram (fun i => c • rotateTo u (z i)) = _
    rw [gram_smul_vec, gram_rotateTo u hu]
  apply (isCompletelyPositive_M_smul_sq_iff hc (gram z)).mpr
  rw [← hgram]
  have hz' : ∀ i, z' i = configVec s t ρ x (e i) := hz
  have hsub : gram z' = (Xconfig s t ρ x).submatrix e e :=
    gram_eq_Xconfig_submatrix hz'
  have he : Function.Injective (e : n → ConfigIdx k p) := e.injective
  have hzero : ∀ α, α ∉ Set.range (e : n → ConfigIdx k p) →
      ∀ β, Xconfig s t ρ x α β = 0 := by
    intro α hα
    exact (hα ⟨e.symm α, Equiv.apply_symm_apply _ _⟩).elim
  rw [hsub]
  exact (isCompletelyPositive_M_iff_submatrix (n := ConfigIdx k p)
      (Xconfig_isSymm s t ρ x) he hzero).mp
    (isCompletelyPositive_M_Xconfig_sorted s t ρ x hs ht hρ hx)

/-! ### Supporting direction and HP05 — tied minimizers -/

lemma det2_rotateTo (u x y : Fin 2 → ℝ) (hu : u ⬝ᵥ u = 1) :
    det2 (rotateTo u x) (rotateTo u y) = det2 x y := by
  have hu2 : u 0 ^ 2 + u 1 ^ 2 = 1 := by
    simpa [dotProduct, Fin.sum_univ_two, pow_two] using hu
  simp only [det2, rotateTo_zero, rotateTo_one]
  simp only [dotProduct, Fin.sum_univ_two]
  convert_to (u 0 ^ 2 + u 1 ^ 2) * (x 0 * y 1 - x 1 * y 0) = x 0 * y 1 - x 1 * y 0 using 1
  · ring
  · rw [hu2, one_mul]

lemma normalize_rotateTo (u x : Fin 2 → ℝ) (hu : u ⬝ᵥ u = 1) (_hx : x ≠ 0) :
    normalize (rotateTo u x) = rotateTo u (normalize x) := by
  have hlen : euclid (rotateTo u x) = euclid x := by
    simp [euclid, rotateTo_inner u x x hu]
  simp only [normalize, rotateTo_smul]
  rw [hlen]

lemma det2_add_right (u x y : Fin 2 → ℝ) : det2 u (x + y) = det2 u x + det2 u y := by
  simp [det2, Pi.add_apply]
  ring

/-- Counterclockwise perpendicular: `u ↦ (-u₁, u₀)`. -/
def rotate90 (u : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then -u 1 else u 0

lemma rotate90_zero (u : Fin 2 → ℝ) : rotate90 u 0 = -u 1 := by simp [rotate90]
lemma rotate90_one (u : Fin 2 → ℝ) : rotate90 u 1 = u 0 := by simp [rotate90]

lemma det2_rotate90 (u : Fin 2 → ℝ) : det2 u (rotate90 u) = u ⬝ᵥ u := by
  simp [det2, rotate90, dotProduct, Fin.sum_univ_two]

lemma det2_rotate90_of_unit {u : Fin 2 → ℝ} (hu : u ⬝ᵥ u = 1) :
    det2 u (rotate90 u) = 1 := by
  rw [det2_rotate90, hu]

lemma rotate90_inner (u : Fin 2 → ℝ) : rotate90 u ⬝ᵥ rotate90 u = u ⬝ᵥ u := by
  simp [rotate90, dotProduct, Fin.sum_univ_two]
  ring_nf

lemma euclid_rotate90_of_unit {u : Fin 2 → ℝ} (hu : u ⬝ᵥ u = 1) :
    euclid (rotate90 u) = 1 := by
  rw [euclid, rotate90_inner, hu, Real.sqrt_one]

omit [DecidableEq n] [LinearOrder n] [Fintype n] in
variable [Finite n] in
/-- Some vector realises a supporting ray of the open cone. -/
lemma exists_supporting_minimizer [Nonempty n] (z : n → Fin 2 → ℝ)
    (hnz : ∀ i, z i ≠ 0) {w : Fin 2 → ℝ} (hw : w ≠ 0)
    (hwz : ∀ i, 0 < w ⬝ᵥ z i) :
    ∃ i0 : n, ∀ i, 0 ≤ det2 (normalize (z i0)) (z i) := by
  cases nonempty_fintype n
  set u := normalize w
  have hu : u ⬝ᵥ u = 1 := normalize_inner hw
  let wr : n → Fin 2 → ℝ := fun i => rotateTo u (z i)
  have hwr0 (i : n) : 0 < wr i 0 := by
    simp only [wr, rotateTo_zero, u, normalize, smul_dotProduct, smul_eq_mul]
    exact mul_pos (inv_pos.mpr (euclid_pos hw)) (hwz i)
  have hwrnz (i : n) : wr i ≠ 0 :=
    mt (rotateTo_eq_zero_iff u (z i) hu).mp (hnz i)
  obtain ⟨i0, _, hmin⟩ :=
    Finset.univ.exists_min_image (fun i : n => normalize (wr i) 1) Finset.univ_nonempty
  refine ⟨i0, fun i => ?_⟩
  have hα : normalize (wr i0) ⬝ᵥ normalize (wr i0) = 1 :=
    normalize_inner (hwrnz i0)
  have hγ : normalize (wr i) ⬝ᵥ normalize (wr i) = 1 :=
    normalize_inner (hwrnz i)
  have hα0 : 0 ≤ normalize (wr i0) 0 := by
    simp only [normalize, Fin.isValue, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr (euclid_nonneg _)) (hwr0 i0).le
  have hγ0 : 0 ≤ normalize (wr i) 0 := by
    simp only [normalize, Fin.isValue, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr (euclid_nonneg _)) (hwr0 i).le
  have hdet : 0 ≤ det2 (normalize (wr i0)) (normalize (wr i)) :=
    det2_nonneg_of_min_snd hα hγ hα0 hγ0 (hmin i (Finset.mem_univ i))
  have hswap : det2 (normalize (z i0)) (z i) =
      euclid (wr i) * det2 (normalize (wr i0)) (normalize (wr i)) := by
    calc
      det2 (normalize (z i0)) (z i)
          = det2 (rotateTo u (normalize (z i0))) (rotateTo u (z i)) :=
            (det2_rotateTo u _ _ hu).symm
      _ = det2 (normalize (rotateTo u (z i0))) (wr i) := by
            rw [← normalize_rotateTo u (z i0) hu (hnz i0)]
      _ = det2 (normalize (wr i0)) (euclid (wr i) • normalize (wr i)) := by
            rw [smul_normalize (hwrnz i)]
      _ = euclid (wr i) * det2 (normalize (wr i0)) (normalize (wr i)) :=
            det2_smul_right _ _ _
  rw [hswap]
  exact mul_nonneg (euclid_nonneg _) hdet

/-- Shift every vector except `i0` by `ε • v`. -/
def perturbTied (z : n → Fin 2 → ℝ) (i0 : n) (v : Fin 2 → ℝ) (ε : ℝ) :
    n → Fin 2 → ℝ :=
  fun i => if i = i0 then z i else z i + ε • v

omit [Fintype n] [LinearOrder n] in
lemma perturbTied_i0 (z : n → Fin 2 → ℝ) (i0 : n) (v : Fin 2 → ℝ) (ε : ℝ) :
    perturbTied z i0 v ε i0 = z i0 := by
  simp [perturbTied]

omit [Fintype n] [LinearOrder n] in
lemma perturbTied_of_ne (z : n → Fin 2 → ℝ) {i0 i : n} (hi : i ≠ i0)
    (v : Fin 2 → ℝ) (ε : ℝ) :
    perturbTied z i0 v ε i = z i + ε • v := by
  simp [perturbTied, hi]

omit [Fintype n] [LinearOrder n] in
lemma perturbTied_zero (z : n → Fin 2 → ℝ) (i0 : n) (v : Fin 2 → ℝ) :
    perturbTied z i0 v 0 = z := by
  ext i k
  simp [perturbTied]

omit [Fintype n] [LinearOrder n] in
lemma continuous_perturbTied_apply (z : n → Fin 2 → ℝ) (i0 : n) (v : Fin 2 → ℝ)
    (i : n) : Continuous fun ε : ℝ => perturbTied z i0 v ε i := by
  by_cases hi : i = i0
  · simpa [perturbTied, hi] using continuous_const (y := z i)
  · simp only [perturbTied, hi, ite_false]
    exact continuous_const.add (continuous_id.smul continuous_const)

omit [Fintype n] [LinearOrder n] in
lemma continuous_gram_perturbTied (z : n → Fin 2 → ℝ) (i0 : n) (v : Fin 2 → ℝ) :
    Continuous fun ε : ℝ => gram (perturbTied z i0 v ε) := by
  refine continuous_matrix fun i j => ?_
  have hi := continuous_perturbTied_apply z i0 v i
  have hj := continuous_perturbTied_apply z i0 v j
  simp only [gram_apply, dotProduct, Fin.sum_univ_two]
  exact (((continuous_apply 0).comp hi).mul ((continuous_apply 0).comp hj)).add
    (((continuous_apply 1).comp hi).mul ((continuous_apply 1).comp hj))

omit [LinearOrder n] in
lemma perturbTied_ne_zero [Nonempty n] {z : n → Fin 2 → ℝ} {i0 : n}
    {v : Fin 2 → ℝ} (hnz : ∀ i, z i ≠ 0) (hv : euclid v = 1)
    {ε : ℝ} (hε0 : 0 < ε)
    (hε : ε < Finset.univ.inf' Finset.univ_nonempty fun i => euclid (z i))
    (i : n) : perturbTied z i0 v ε i ≠ 0 := by
  by_cases hi : i = i0
  · simpa [perturbTied, hi] using hnz i
  · intro h
    have heq : z i = -ε • v := by
      simpa [perturbTied, hi, add_eq_zero_iff_eq_neg] using h
    have hv2 : v ⬝ᵥ v = 1 := by
      rw [← euclid_sq, hv, one_pow]
    have hlen : euclid (z i) = ε := by
      apply (sq_eq_sq₀ (euclid_nonneg _) hε0.le).mp
      rw [heq, euclid_sq, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, hv2]
      ring
    have hle : Finset.univ.inf' Finset.univ_nonempty (fun j => euclid (z j)) ≤ euclid (z i) :=
      Finset.inf'_le _ (Finset.mem_univ i)
    exact (not_le_of_gt hε) (hle.trans_eq hlen)

omit [Fintype n] [LinearOrder n] in
lemma det2_perturbTied {z : n → Fin 2 → ℝ} {i0 : n} {v : Fin 2 → ℝ}
    (hnz0 : z i0 ≠ 0) (hside : ∀ i, 0 ≤ det2 (normalize (z i0)) (z i))
    (hv : det2 (normalize (z i0)) v = 1) {ε : ℝ} (hε : 0 < ε) :
    (∀ i, 0 ≤ det2 (normalize (perturbTied z i0 v ε i0)) (perturbTied z i0 v ε i)) ∧
      (∀ i, det2 (normalize (perturbTied z i0 v ε i0)) (perturbTied z i0 v ε i) = 0 →
        i = i0) := by
  set u := normalize (z i0)
  have hzi0 : perturbTied z i0 v ε i0 = z i0 := perturbTied_i0 z i0 v ε
  refine ⟨fun i => ?_, fun i hi => ?_⟩
  · rw [hzi0]
    by_cases hi : i = i0
    · subst hi
      rw [perturbTied_i0]
      simp only [det2, normalize, Fin.isValue, Pi.smul_apply, smul_eq_mul, sub_nonneg]
      exact le_of_eq (by ring)
    · rw [perturbTied_of_ne z hi, det2_add_right, det2_smul_right]
      nlinarith [hside i, hv, hε]
  · rw [hzi0] at hi
    by_contra hne
    rw [perturbTied_of_ne z hne, det2_add_right, det2_smul_right] at hi
    nlinarith [hside i, hv, hε]


/-- **HP05.** Open half-plane with a tied supporting ray: perturb into the
open cone so the contact is unique, apply HP04, and pass to the limit. -/
lemma isCompletelyPositive_M_of_tied_minimizers (z : n → Fin 2 → ℝ)
    (hnz : ∀ i, z i ≠ 0)
    (hopen : ∃ w : Fin 2 → ℝ, w ≠ 0 ∧ ∀ i, 0 < w ⬝ᵥ z i)
    (hneg : ∃ i j, z i ⬝ᵥ z j < 0) (i0 : n)
    (hside : ∀ i, 0 ≤ det2 (normalize (z i0)) (z i))
    (_htied : ¬ ∀ i, det2 (normalize (z i0)) (z i) = 0 → i = i0) :
    IsCompletelyPositive (M (gram z)) := by
  obtain ⟨w, hw0, hw⟩ := hopen
  have : Nonempty n := ⟨i0⟩
  set u := normalize (z i0)
  have hu : u ⬝ᵥ u = 1 := normalize_inner (hnz i0)
  set v := rotate90 u
  have hv : euclid v = 1 := euclid_rotate90_of_unit hu
  have hvdet : det2 u v = 1 := det2_rotate90_of_unit hu
  let mlen := Finset.univ.inf' Finset.univ_nonempty fun i => euclid (z i)
  have hmlen : 0 < mlen := by
    obtain ⟨imin, _, himin⟩ :=
      Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => euclid (z i))
    dsimp [mlen]
    rw [himin]
    exact euclid_pos (hnz imin)
  obtain ⟨a, b, hab⟩ := hneg
  let zε := perturbTied z i0 v
  have hgram0 : gram (zε 0) = gram z := by
    simp [zε, perturbTied_zero]
  have hf : Continuous fun ε : ℝ => gram (zε ε) a b :=
    (continuous_apply_apply a b).comp (continuous_gram_perturbTied z i0 v)
  have hneg_ev : ∀ᶠ ε in 𝓝 (0 : ℝ), gram (zε ε) a b < 0 :=
    (isOpen_lt hf continuous_const).mem_nhds (by
      simpa [zε, perturbTied_zero, gram_apply] using hab)
  let δw : ℝ :=
    if 0 ≤ w ⬝ᵥ v then 1
    else Finset.univ.inf' Finset.univ_nonempty fun i => w ⬝ᵥ z i / -(w ⬝ᵥ v)
  have hδw : 0 < δw := by
    by_cases hc : 0 ≤ w ⬝ᵥ v
    · dsimp [δw]
      rw [ite_eq_left hc]
      norm_num
    · have hcneg : w ⬝ᵥ v < 0 := lt_of_not_ge hc
      dsimp [δw]
      rw [ite_eq_right hc]
      obtain ⟨imin, _, himin⟩ :=
        Finset.exists_mem_eq_inf' Finset.univ_nonempty
          (fun i => w ⬝ᵥ z i / -(w ⬝ᵥ v))
      rw [himin]
      exact div_pos (hw imin) (neg_pos.mpr hcneg)
  let δ := min mlen δw
  have hδ : 0 < δ := lt_min hmlen hδw
  have hmem : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IsCompletelyPositive (M (gram (zε ε))) := by
    filter_upwards [Ioo_mem_nhdsGT hδ,
      eventually_nhdsWithin_of_eventually_nhds hneg_ev] with ε hε habε
    have hε0 : 0 < ε := hε.1
    have hεδ : ε < δ := hε.2
    have hεlen : ε < mlen := hεδ.trans_le (min_le_left _ _)
    have hεδw : ε < δw := hεδ.trans_le (min_le_right _ _)
    have hnzε : ∀ i, zε ε i ≠ 0 :=
      perturbTied_ne_zero hnz hv hε0 hεlen
    have hopenε : ∃ w' : Fin 2 → ℝ, w' ≠ 0 ∧ ∀ i, 0 < w' ⬝ᵥ zε ε i := by
      refine ⟨w, hw0, fun i => ?_⟩
      by_cases hi : i = i0
      · simpa [zε, perturbTied, hi] using hw i
      · have hdot : w ⬝ᵥ zε ε i = w ⬝ᵥ z i + ε * (w ⬝ᵥ v) := by
          simp [zε, perturbTied, hi, smul_eq_mul]
        rw [hdot]
        by_cases hc : 0 ≤ w ⬝ᵥ v
        · nlinarith [hw i, hε0]
        · have hcneg : w ⬝ᵥ v < 0 := lt_of_not_ge hc
          have hle : δw ≤ w ⬝ᵥ z i / -(w ⬝ᵥ v) := by
            dsimp [δw]
            rw [ite_eq_right hc]
            exact Finset.inf'_le _ (Finset.mem_univ i)
          have hbound : ε < w ⬝ᵥ z i / -(w ⬝ᵥ v) := hεδw.trans_le hle
          have hden : 0 < -(w ⬝ᵥ v) := neg_pos.mpr hcneg
          rw [← sub_neg_eq_add, sub_pos]
          calc
            -(ε * (w ⬝ᵥ v)) = ε * -(w ⬝ᵥ v) := by ring
            _ < (w ⬝ᵥ z i / -(w ⬝ᵥ v)) * -(w ⬝ᵥ v) :=
                  mul_lt_mul_of_pos_right hbound hden
            _ = w ⬝ᵥ z i := div_mul_cancel₀ _ hden.ne'
    have hnegε : ∃ i j, zε ε i ⬝ᵥ zε ε j < 0 := ⟨a, b, habε⟩
    have hsu := det2_perturbTied (hnz i0) hside hvdet hε0
    exact isCompletelyPositive_M_of_unique_minimizer (zε ε) hnzε hopenε hnegε i0
      hsu.1 hsu.2
  have hlim : Tendsto (fun ε => M (gram (zε ε))) (𝓝[>] 0) (𝓝 (M (gram z))) := by
    have hgram : Tendsto (fun ε => gram (zε ε)) (𝓝[>] 0) (𝓝 (gram z)) := by
      simpa [zε, perturbTied_zero] using
        tendsto_nhdsWithin_of_tendsto_nhds
          ((continuous_gram_perturbTied z i0 v).tendsto 0)
    exact (continuous_M.tendsto (gram z)).comp hgram
  exact isClosed_isCompletelyPositive.mem_of_tendsto hlim hmem

/-- Open half-plane (unique or tied supporting ray). -/
lemma isCompletelyPositive_M_of_open_halfplane (z : n → Fin 2 → ℝ)
    (hnz : ∀ i, z i ≠ 0)
    (hopen : ∃ w : Fin 2 → ℝ, w ≠ 0 ∧ ∀ i, 0 < w ⬝ᵥ z i) :
    IsCompletelyPositive (M (gram z)) := by
  by_cases hnn : ∀ i j, 0 ≤ z i ⬝ᵥ z j
  · exact isCompletelyPositive_M_of_nonneg_inners z hnn
  · push Not at hnn
    have : Nonempty n := ⟨hnn.choose⟩
    obtain ⟨w, hw0, hw⟩ := hopen
    obtain ⟨i0, hside⟩ := exists_supporting_minimizer z hnz hw0 hw
    by_cases huniq : ∀ i, det2 (normalize (z i0)) (z i) = 0 → i = i0
    · exact isCompletelyPositive_M_of_unique_minimizer z hnz ⟨w, hw0, hw⟩ hnn i0 hside huniq
    · exact isCompletelyPositive_M_of_tied_minimizers z hnz ⟨w, hw0, hw⟩ hnn i0 hside huniq

omit [Fintype n] [DecidableEq n] [LinearOrder n] in
lemma continuous_gram_shiftBy (z : n → Fin 2 → ℝ) (w : Fin 2 → ℝ) :
    Continuous fun ε : ℝ => gram (fun i => z i + ε • w) := by
  refine continuous_matrix fun i j => ?_
  have hi : Continuous fun ε : ℝ => (z i + ε • w : Fin 2 → ℝ) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hj : Continuous fun ε : ℝ => (z j + ε • w : Fin 2 → ℝ) :=
    continuous_const.add (continuous_id.smul continuous_const)
  simp only [gram_apply, dotProduct, Fin.sum_univ_two]
  exact (((continuous_apply 0).comp hi).mul ((continuous_apply 0).comp hj)).add
    (((continuous_apply 1).comp hi).mul ((continuous_apply 1).comp hj))

omit [Fintype n] [DecidableEq n] [LinearOrder n] in
lemma shiftBy_ne_zero (z : n → Fin 2 → ℝ) {w : Fin 2 → ℝ} (hw : w ≠ 0)
    (hwz : ∀ i, 0 ≤ w ⬝ᵥ z i) {ε : ℝ} (hε : 0 < ε) (i : n) :
    z i + ε • w ≠ 0 := by
  intro h
  have hdot : w ⬝ᵥ z i + ε * (w ⬝ᵥ w) = 0 := by
    have := congrArg (fun x => w ⬝ᵥ x) h
    simpa [dotProduct_add, dotProduct_smul, smul_eq_mul] using this
  have hw2 : 0 < w ⬝ᵥ w :=
    lt_of_le_of_ne (euclid_inner_nonneg w) fun h0 =>
      hw (dotProduct_self_eq_zero.mp h0.symm)
  nlinarith [hwz i]

/-- **HP06.** Vectors in a closed half-plane: `M` of the Gram matrix is CP. -/
lemma isCompletelyPositive_M_of_closed_halfplane (z : n → Fin 2 → ℝ)
    {w : Fin 2 → ℝ} (hw : w ≠ 0) (hwz : ∀ i, 0 ≤ w ⬝ᵥ z i) :
    IsCompletelyPositive (M (gram z)) := by
  by_cases hnn : ∀ i j, 0 ≤ z i ⬝ᵥ z j
  · exact isCompletelyPositive_M_of_nonneg_inners z hnn
  · let zε : ℝ → n → Fin 2 → ℝ := fun ε i => z i + ε • w
    have hnzε : ∀ ε, 0 < ε → ∀ i, zε ε i ≠ 0 :=
      fun ε hε i => shiftBy_ne_zero z hw hwz hε i
    have hopenε : ∀ ε, 0 < ε →
        ∃ w' : Fin 2 → ℝ, w' ≠ 0 ∧ ∀ i, 0 < w' ⬝ᵥ zε ε i := by
      intro ε hε
      refine ⟨w, hw, fun i => ?_⟩
      have : w ⬝ᵥ zε ε i = w ⬝ᵥ z i + ε * (w ⬝ᵥ w) := by
        simp [zε, smul_eq_mul]
      rw [this]
      have hw2 : 0 < w ⬝ᵥ w :=
        lt_of_le_of_ne (euclid_inner_nonneg w) fun h0 =>
          hw (dotProduct_self_eq_zero.mp h0.symm)
      nlinarith [hwz i]
    have hmem : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        IsCompletelyPositive (M (gram (zε ε))) :=
      eventually_of_mem self_mem_nhdsWithin fun ε hε =>
        isCompletelyPositive_M_of_open_halfplane (zε ε) (hnzε ε hε) (hopenε ε hε)
    have hlim : Tendsto (fun ε => M (gram (zε ε))) (𝓝[>] 0) (𝓝 (M (gram z))) := by
      have hgram : Tendsto (fun ε => gram (zε ε)) (𝓝[>] 0) (𝓝 (gram z)) := by
        have hz0 : (fun i => z i + (0 : ℝ) • w) = z := by
          ext i; simp
        simpa [zε, hz0] using
          tendsto_nhdsWithin_of_tendsto_nhds
            ((continuous_gram_shiftBy z w).tendsto 0)
      exact (continuous_M.tendsto (gram z)).comp hgram
    exact isClosed_isCompletelyPositive.mem_of_tendsto hlim hmem

end

end BollobasNikiforov
