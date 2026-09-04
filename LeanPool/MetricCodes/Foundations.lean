/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.SpherePacking
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Nat.Dist

/-!
# Foundations for binary and spherical code bounds

Elementary coding-theory definitions, projection certificates, and the finite Johnson bound.
-/

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

section

open scoped BigOperators InnerProductSpace

instance numeralTwoAtLeast : Nat.AtLeastTwo 2 := ⟨by decide⟩

/-- The ambient used in the metric-code argument. -/
abbrev Ambient (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The binary word used in the metric-code argument. -/
abbrev BinaryWord (n : ℕ) := Fin n → Bool

/-- The hamming dist used in the metric-code argument. -/
def hammingDist {n : ℕ} (x y : BinaryWord n) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ y i).card

@[simp] theorem hammingDist_self {n : ℕ} (x : BinaryWord n) :
    hammingDist x x = 0 := by
  simp only [hammingDist, ne_eq, not_true_eq_false, Finset.filter_false, Finset.card_empty]

/-- The binary weight used in the metric-code argument. -/
def binaryWeight {n : ℕ} (x : BinaryWord n) : ℕ :=
  (Finset.univ.filter fun i => x i = true).card

/-- The predicate asserting binary code. -/
def IsBinaryCode {n : ℕ} (d : ℕ) (C : Finset (BinaryWord n)) : Prop :=
  ∀ ⦃x⦄, x ∈ C → ∀ ⦃y⦄, y ∈ C → x ≠ y → d ≤ hammingDist x y

/-- The johnson sphere used in the Johnson-code argument. -/
abbrev JohnsonSphere (n w : ℕ) :=
  {x : BinaryWord n // binaryWeight x = w}

/-- The hamming correlation used in the metric-code argument. -/
def hammingCorrelation {n : ℕ} (x y : BinaryWord n) : ℝ :=
  1 - 2 * (hammingDist x y : ℝ) / (n : ℝ)

@[simp] theorem hammingCorrelation_self {n : ℕ} (x : BinaryWord n) :
    hammingCorrelation x x = 1 := by
  simp only [hammingCorrelation, hammingDist_self, CharP.cast_eq_zero, mul_zero, zero_div, sub_zero]

theorem hammingCorrelation_le_of_dist_le
    {n d : ℕ} (hn : 0 < n) {x y : BinaryWord n}
    (hd : d ≤ hammingDist x y) :
    hammingCorrelation x y ≤ 1 - 2 * (d : ℝ) / (n : ℝ) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hd' : (d : ℝ) ≤ (hammingDist x y : ℝ) := by
    exact_mod_cast hd
  unfold hammingCorrelation
  have hdiv :
      2 * (d : ℝ) / (n : ℝ) ≤
        2 * (hammingDist x y : ℝ) / (n : ℝ) := by
    exact (div_le_div_iff_of_pos_right hn').2 (by linarith)
  linarith

/-- The spherical entropy used in the metric-code argument. -/
def sphericalEntropy (u : ℝ) : ℝ :=
  (1 + u) * Real.logb 2 (1 + u) - u * Real.logb 2 u

@[simp] theorem sphericalEntropy_zero : sphericalEntropy 0 = 0 := by
  simp only [sphericalEntropy, add_zero, Real.logb_one, mul_zero, Real.logb_zero, sub_self]

theorem sphericalEntropy_eq_log_add {u : ℝ} (hu : 0 < u) :
    sphericalEntropy u =
      Real.logb 2 (1 + u) +
        u * Real.logb 2 ((1 + u) / u) := by
  have hu' : u ≠ 0 := hu.ne'
  have hone : 1 + u ≠ 0 := by linarith
  rw [Real.logb_div hone hu']
  unfold sphericalEntropy
  ring

/-- The binary entropy used in the metric-code argument. -/
def binaryEntropy (u : ℝ) : ℝ :=
  -(u * Real.logb 2 u) -
    (1 - u) * Real.logb 2 (1 - u)

@[simp] theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by
  simp only [binaryEntropy, Real.logb_zero, mul_zero, neg_zero, sub_zero, Real.logb_one, sub_self]

theorem binaryEntropy_nonneg {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1) :
    0 ≤ binaryEntropy u := by
  have h₁ : Real.logb 2 u ≤ 0 :=
    Real.logb_nonpos (by norm_num : (1 : ℝ) < 2) hu hu'
  have h₂ : Real.logb 2 (1 - u) ≤ 0 :=
    Real.logb_nonpos (by norm_num : (1 : ℝ) < 2)
      (by linarith) (by linarith)
  unfold binaryEntropy
  have hleft : u * Real.logb 2 u ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hu h₁
  have hright : (1 - u) * Real.logb 2 (1 - u) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) h₂
  linarith

/-- The gamma used in the metric-code argument. -/
def Gamma (a b : ℝ) : ℝ :=
  ((a - b) * (1 + a + b)) /
    ((1 + 2 * a) * Real.sqrt (a * (1 + a)))

theorem Gamma_eq_sub (a b : ℝ) :
    Gamma a b =
      (a * (1 + a) - b * (1 + b)) /
        ((1 + 2 * a) * Real.sqrt (a * (1 + a))) := by
  unfold Gamma
  congr 1
  ring

/-- The classical threshold used in the metric-code argument. -/
def classicalThreshold (s : ℝ) : ℝ :=
  (1 / Real.sqrt (1 - s ^ 2) - 1) / 2

@[simp] theorem classicalThreshold_zero : classicalThreshold 0 = 0 := by
  simp only [classicalThreshold, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
    Real.sqrt_one, one_ne_zero, div_self, sub_self, zero_div]

theorem classicalThreshold_pos {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    0 < classicalThreshold s := by
  have hrad : 0 < 1 - s ^ 2 := by nlinarith
  have hsqrt : 0 < Real.sqrt (1 - s ^ 2) := Real.sqrt_pos.2 hrad
  have hsqrt' : Real.sqrt (1 - s ^ 2) < 1 := by
    apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).2
    nlinarith
  have hrecip : 1 < 1 / Real.sqrt (1 - s ^ 2) := by
    apply (lt_div_iff₀ hsqrt).2
    simpa only [one_mul] using hsqrt'
  unfold classicalThreshold
  linarith

/-- The boolean harmonic dimension used in the metric-code argument. -/
def booleanHarmonicDimension (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => n.choose (k + 1) - n.choose k

theorem booleanHarmonicDimension_succ (n k : ℕ) :
    booleanHarmonicDimension n (k + 1) =
      n.choose (k + 1) - n.choose k := rfl

theorem sum_booleanHarmonicDimension (n L : ℕ) (hL : 2 * L ≤ n) :
    (∑ k ∈ Finset.range (L + 1), booleanHarmonicDimension n k) =
      n.choose L := by
  induction L generalizing n with
  | zero =>
      simp only [zero_add, Finset.range_one, booleanHarmonicDimension, Finset.sum_singleton,
        Nat.choose_zero_right]
  | succ L ih =>
      have hprev : 2 * L ≤ n := by omega
      have hhalf : L < n / 2 := by omega
      have hmono : n.choose L ≤ n.choose (L + 1) :=
        Nat.choose_le_succ_of_lt_half_left hhalf
      rw [Finset.sum_range_succ, ih n hprev]
      change n.choose L + (n.choose (L + 1) - n.choose L) =
        n.choose (L + 1)
      omega

/-- The hamming fibre dimension used in the metric-code argument. -/
abbrev hammingFibreDimension (n k : ℕ) : ℕ :=
  booleanHarmonicDimension n k

/-- The johnson fibre dimension used in the metric-code argument. -/
def johnsonFibreDimension (n w p q : ℕ) : ℕ :=
  booleanHarmonicDimension w p *
    booleanHarmonicDimension (n - w) q

/-- The hamming jacobi entry used in the metric-code argument. -/
def hammingJacobiEntry (n k i : ℕ) : ℝ :=
  (((i : ℝ) - (k : ℝ) + 1) *
    ((n : ℝ) - (i : ℝ) - (k : ℝ))) /
    ((n : ℝ) * Real.sqrt (((i : ℝ) + 1) * ((n : ℝ) - (i : ℝ))))

theorem hammingJacobiEntry_pos {n k i : ℕ}
    (hn : 0 < n) (hki : k ≤ i) (hi : i + k < n) :
    0 < hammingJacobiEntry n k i := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hki' : (k : ℝ) ≤ i := by exact_mod_cast hki
  have hi' : (i : ℝ) + (k : ℝ) < n := by exact_mod_cast hi
  have hzero : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  unfold hammingJacobiEntry
  apply div_pos
  · apply mul_pos <;> linarith
  · apply mul_pos hn'
    apply Real.sqrt_pos.2
    apply mul_pos <;> linarith

/-- The hamming jacobi matrix used in the metric-code argument. -/
def hammingJacobiMatrix (n k L : ℕ) :
    Matrix (Fin (L - k + 1)) (Fin (L - k + 1)) ℝ :=
  fun p q =>
    if p.val + 1 = q.val then
      hammingJacobiEntry n k (k + p.val)
    else if q.val + 1 = p.val then
      hammingJacobiEntry n k (k + q.val)
    else
      0

theorem hammingJacobiMatrix_symmetric (n k L : ℕ) :
    (hammingJacobiMatrix n k L).transpose =
      hammingJacobiMatrix n k L := by
  ext p q
  simp only [Matrix.transpose_apply]
  by_cases hpq : p.val + 1 = q.val
  · have hqp : q.val + 1 ≠ p.val := by omega
    simp only [hammingJacobiMatrix, hqp, ↓reduceIte, hpq]
  · by_cases hqp : q.val + 1 = p.val
    · simp only [hammingJacobiMatrix, hqp, ↓reduceIte, hpq]
    · simp only [hammingJacobiMatrix, hqp, ↓reduceIte, hpq]

/-- The hamming gamma used in the metric-code argument. -/
def hammingGamma (a b : ℝ) : ℝ :=
  (2 * (a - b) * (1 - a - b)) /
    Real.sqrt (a * (1 - a))

/-- The johnson j1 used in the metric-code argument. -/
def johnsonJ1 (w p : ℕ) : ℝ :=
  (w : ℝ) / 2 - (p : ℝ)

/-- The johnson j2 used in the metric-code argument. -/
def johnsonJ2 (n w q : ℕ) : ℝ :=
  ((n - w : ℕ) : ℝ) / 2 - (q : ℝ)

/-- The johnson j used in the metric-code argument. -/
def johnsonJ (n j : ℕ) : ℝ :=
  (n : ℝ) / 2 - (j : ℝ)

/-- The johnson m used in the metric-code argument. -/
def johnsonM (n w : ℕ) : ℝ :=
  (n : ℝ) / 2 - (w : ℝ)

/-- The johnson sigma used in the metric-code argument. -/
def johnsonSigma (n w p q : ℕ) : ℝ :=
  johnsonJ1 w p + johnsonJ2 n w q

/-- The johnson delta used in the metric-code argument. -/
def johnsonDelta (n w p q : ℕ) : ℝ :=
  johnsonJ2 n w q - johnsonJ1 w p

/-- The johnson last degree used in the metric-code argument. -/
def johnsonLastDegree (n w p q : ℕ) : ℕ :=
  min w (min (w - p + q) (n - w + p - q))

/-- The johnson mu used in the metric-code argument. -/
def johnsonMu (n w p q j : ℕ) : ℝ :=
  (johnsonM n w / 2) *
    (johnsonJ2 n w q * (johnsonJ2 n w q + 1) -
      johnsonJ1 w p * (johnsonJ1 w p + 1)) /
    (johnsonJ n j * (johnsonJ n j + 1))

/-- The johnson nu used in the metric-code argument. -/
def johnsonNu (n w p q j : ℕ) : ℝ :=
  Real.sqrt
      ((johnsonJ n j ^ 2 - johnsonM n w ^ 2) *
        (johnsonJ n j ^ 2 - johnsonDelta n w p q ^ 2) *
        ((johnsonSigma n w p q + 1) ^ 2 - johnsonJ n j ^ 2)) /
    (2 * johnsonJ n j *
      Real.sqrt ((2 * johnsonJ n j - 1) *
        (2 * johnsonJ n j + 1)))

/-- The johnson diagonal used in the metric-code argument. -/
def johnsonDiagonal (n w p q j : ℕ) : ℝ :=
  ((n : ℝ) * johnsonMu n w p q j - johnsonM n w ^ 2) /
    ((w : ℝ) * ((n - w : ℕ) : ℝ))

/-- The johnson edge used in the metric-code argument. -/
def johnsonEdge (n w p q j : ℕ) : ℝ :=
  ((n : ℝ) * johnsonNu n w p q j) /
    ((w : ℝ) * ((n - w : ℕ) : ℝ))

/-- The johnson zonal diagonal used in the metric-code argument. -/
def johnsonZonalDiagonal (n w j : ℕ) : ℝ :=
  johnsonDiagonal n w 0 0 j

/-- The johnson zonal edge used in the metric-code argument. -/
def johnsonZonalEdge (n w j : ℕ) : ℝ :=
  johnsonEdge n w 0 0 j

/-- The johnson hatted diagonal used in the metric-code argument. -/
def johnsonHattedDiagonal (n w p q j : ℕ) : ℝ :=
  if j = 0 then 0
  else johnsonDiagonal n w p q j ^ 2 / johnsonZonalDiagonal n w j

/-- The johnson hatted edge used in the metric-code argument. -/
def johnsonHattedEdge (n w p q j : ℕ) : ℝ :=
  johnsonEdge n w p q j ^ 2 / johnsonZonalEdge n w j

theorem johnsonHattedDiagonal_nonneg {n w p q j : ℕ}
    (hzero : 0 < johnsonZonalDiagonal n w j) :
    0 ≤ johnsonHattedDiagonal n w p q j := by
  unfold johnsonHattedDiagonal
  split <;> positivity

/-- The johnson jacobi matrix used in the metric-code argument. -/
def johnsonJacobiMatrix (n w p q L : ℕ) :
    Matrix (Fin (L - (p + q) + 1))
      (Fin (L - (p + q) + 1)) ℝ :=
  fun i j =>
    if i = j then
      johnsonHattedDiagonal n w p q (p + q + i.val)
    else if i.val + 1 = j.val then
      johnsonHattedEdge n w p q (p + q + i.val)
    else if j.val + 1 = i.val then
      johnsonHattedEdge n w p q (p + q + j.val)
    else
      0

@[simp] theorem johnsonJacobiMatrix_diag (n w p q L : ℕ)
    (i : Fin (L - (p + q) + 1)) :
    johnsonJacobiMatrix n w p q L i i =
      johnsonHattedDiagonal n w p q (p + q + i.val) := by
  simp only [johnsonJacobiMatrix, ↓reduceIte]

theorem johnsonJacobiMatrix_symmetric (n w p q L : ℕ) :
    (johnsonJacobiMatrix n w p q L).transpose =
      johnsonJacobiMatrix n w p q L := by
  ext i j
  simp only [Matrix.transpose_apply]
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : j ≠ i := Ne.symm hij
    by_cases hup : i.val + 1 = j.val
    · have hdown : j.val + 1 ≠ i.val := by omega
      simp only [johnsonJacobiMatrix, hji, ↓reduceIte, hdown, hup, hij]
    · by_cases hdown : j.val + 1 = i.val
      · simp only [johnsonJacobiMatrix, hji, ↓reduceIte, hdown, hij, hup]
      · simp only [johnsonJacobiMatrix, hji, ↓reduceIte, hdown, hup, hij]

end

section

open scoped BigOperators

namespace Boolean

/-- The function used in the binary-code argument. -/
abbrev Function (n : ℕ) := Finset (Fin n) → ℝ

/-- The level used in the binary-code argument. -/
abbrev Level (n k : ℕ) := {S : Finset (Fin n) // S.card = k}

theorem card_level (n k : ℕ) :
    Fintype.card (Level n k) = n.choose k := by
  simp only [Level, Fintype.card_finset_len, Fintype.card_fin]

/-- The raise at used in the binary-code argument. -/
def raiseAt {n : ℕ} (a : Fin n) (f : Function n) (S : Finset (Fin n)) : ℝ :=
  if a ∈ S then f (S.erase a) else 0

/-- The lower at used in the binary-code argument. -/
def lowerAt {n : ℕ} (a : Fin n) (f : Function n) (S : Finset (Fin n)) : ℝ :=
  if a ∈ S then 0 else f (insert a S)

/-- The raise used in the binary-code argument. -/
def raise {n : ℕ} (f : Function n) (S : Finset (Fin n)) : ℝ :=
  ∑ a : Fin n, raiseAt a f S

/-- The lower used in the binary-code argument. -/
def lower {n : ℕ} (f : Function n) (S : Finset (Fin n)) : ℝ :=
  ∑ a : Fin n, lowerAt a f S

/-- The predicate asserting level. -/
def IsLevel {n : ℕ} (k : ℕ) (f : Function n) : Prop :=
  ∀ S : Finset (Fin n), S.card ≠ k → f S = 0

/-- The predicate asserting harmonic. -/
def IsHarmonic {n : ℕ} (k : ℕ) (f : Function n) : Prop :=
  IsLevel k f ∧ ∀ S : Finset (Fin n), lower f S = 0

variable {n : ℕ}

theorem lowerAt_raiseAt_of_ne (f : Function n) (a b : Fin n)
    (hab : a ≠ b) (S : Finset (Fin n)) :
    lowerAt a (raiseAt b f) S = raiseAt b (lowerAt a f) S := by
  classical
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
  · simp only [lowerAt, ha, ↓reduceIte, raiseAt, hb, Finset.mem_erase, ne_eq, hab,
      not_false_eq_true, and_self]
  · simp only [lowerAt, ha, ↓reduceIte, raiseAt, hb]
  · simp only [lowerAt, ha, ↓reduceIte, raiseAt, Finset.mem_insert, hb, or_true,
      Finset.erase_insert_of_ne hab, Finset.mem_erase, ne_eq, hab, not_false_eq_true, and_false]
  · simp only [lowerAt, ha, ↓reduceIte, raiseAt, Finset.mem_insert, hab.symm, hb, or_self]

theorem lowerAt_raiseAt_self (f : Function n) (a : Fin n)
    (S : Finset (Fin n)) :
    lowerAt a (raiseAt a f) S = if a ∈ S then 0 else f S := by
  classical
  by_cases ha : a ∈ S
  · simp only [lowerAt, ha, ↓reduceIte]
  · simp only [lowerAt, ha, ↓reduceIte, raiseAt, Finset.mem_insert, or_false,
      Finset.erase_insert ha]

theorem raiseAt_lowerAt_self (f : Function n) (a : Fin n)
    (S : Finset (Fin n)) :
    raiseAt a (lowerAt a f) S = if a ∈ S then f S else 0 := by
  classical
  by_cases ha : a ∈ S
  · simp only [raiseAt, ha, ↓reduceIte, lowerAt, Finset.mem_erase, ne_eq, not_true_eq_false,
      and_true, Finset.insert_erase ha]
  · simp only [raiseAt, ha, ↓reduceIte]

theorem lowerAt_raise (f : Function n) (a : Fin n)
    (S : Finset (Fin n)) :
    lowerAt a (raise f) S =
      ∑ b : Fin n, lowerAt a (raiseAt b f) S := by
  classical
  by_cases ha : a ∈ S <;> simp [lowerAt, raise, ha]

theorem raiseAt_lower (f : Function n) (a : Fin n)
    (S : Finset (Fin n)) :
    raiseAt a (lower f) S =
      ∑ b : Fin n, raiseAt a (lowerAt b f) S := by
  classical
  by_cases ha : a ∈ S <;> simp [raiseAt, lower, ha]

theorem sum_mem_indicator (S : Finset (Fin n)) (x : ℝ) :
    (∑ a : Fin n, if a ∈ S then x else 0) = (S.card : ℝ) * x := by
  classical
  calc
    (∑ a : Fin n, if a ∈ S then x else 0) = ∑ a ∈ S, x := by
      simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    _ = (S.card : ℝ) * x := by simp only [Finset.sum_const, nsmul_eq_mul]

theorem lower_raise_sub_raise_lower (f : Function n)
    (S : Finset (Fin n)) :
    lower (raise f) S - raise (lower f) S =
      ((n : ℝ) - 2 * (S.card : ℝ)) * f S := by
  classical
  change
    (∑ a : Fin n, lowerAt a (raise f) S) -
      (∑ a : Fin n, raiseAt a (lower f) S) = _
  simp_rw [lowerAt_raise, raiseAt_lower]
  have hswap :
      (∑ a : Fin n, ∑ b : Fin n, raiseAt a (lowerAt b f) S) =
        ∑ b : Fin n, ∑ a : Fin n, raiseAt a (lowerAt b f) S := by
    exact Finset.sum_comm
  rw [hswap, ← Finset.sum_sub_distrib]
  have hcross (a : Fin n) :
      (∑ b : Fin n, lowerAt a (raiseAt b f) S) -
        (∑ b : Fin n, raiseAt b (lowerAt a f) S) =
          lowerAt a (raiseAt a f) S - raiseAt a (lowerAt a f) S := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_eq_single a
    · intro b _ hba
      rw [lowerAt_raiseAt_of_ne f a b hba.symm S]
      exact sub_self _
    · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]
  simp_rw [hcross, lowerAt_raiseAt_self, raiseAt_lowerAt_self]
  have hterm (a : Fin n) :
      (if a ∈ S then (0 : ℝ) else f S) -
          (if a ∈ S then f S else 0) =
        f S - 2 * (if a ∈ S then f S else 0) := by
    by_cases ha : a ∈ S <;> simp [ha] ; ring
  simp_rw [hterm, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, sum_mem_indicator]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem lower_raise_sub_raise_lower_of_level {k : ℕ}
    (f : Function n) (hf : IsLevel k f) (S : Finset (Fin n)) :
    lower (raise f) S - raise (lower f) S =
      ((n : ℝ) - 2 * (k : ℝ)) * f S := by
  by_cases hS : S.card = k
  · simpa only [hS] using lower_raise_sub_raise_lower f S
  · rw [lower_raise_sub_raise_lower, hf S hS]
    simp only [mul_zero]

theorem lower_raise_of_harmonic {k : ℕ} (f : Function n)
    (hf : IsHarmonic k f) (S : Finset (Fin n)) :
    lower (raise f) S = ((n : ℝ) - 2 * (k : ℝ)) * f S := by
  have hcomm := lower_raise_sub_raise_lower_of_level f hf.1 S
  have hzero : raise (lower f) S = 0 := by
    simp only [raise, raiseAt, hf.2, ite_self, Finset.sum_const_zero]
  simpa only [hzero, sub_zero] using hcomm

theorem raise_add (f g : Function n) :
    raise (f + g) = raise f + raise g := by
  classical
  funext S
  change
    (∑ a : Fin n, if a ∈ S then f (S.erase a) + g (S.erase a) else 0) =
      (∑ a : Fin n, if a ∈ S then f (S.erase a) else 0) +
        (∑ a : Fin n, if a ∈ S then g (S.erase a) else 0)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ S <;> simp [ha]

theorem raise_smul (c : ℝ) (f : Function n) :
    raise (c • f) = c • raise f := by
  classical
  funext S
  simp only [raise, raiseAt, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ S <;> simp [ha]

theorem lower_add (f g : Function n) :
    lower (f + g) = lower f + lower g := by
  classical
  funext S
  change
    (∑ a : Fin n, if a ∈ S then 0 else f (insert a S) + g (insert a S)) =
      (∑ a : Fin n, if a ∈ S then 0 else f (insert a S)) +
        (∑ a : Fin n, if a ∈ S then 0 else g (insert a S))
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ S <;> simp [ha]

theorem lower_smul (c : ℝ) (f : Function n) :
    lower (c • f) = c • lower f := by
  classical
  funext S
  simp only [lower, lowerAt, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ S <;> simp [ha]

/-- The raise linear used in the binary-code argument. -/
def raiseLinear (n : ℕ) : Function n →ₗ[ℝ] Function n where
  toFun := raise
  map_add' := raise_add
  map_smul' := raise_smul

/-- The lower linear used in the binary-code argument. -/
def lowerLinear (n : ℕ) : Function n →ₗ[ℝ] Function n where
  toFun := lower
  map_add' := lower_add
  map_smul' := lower_smul

@[simp] theorem raiseLinear_apply (f : Function n) :
    raiseLinear n f = raise f := rfl

theorem IsLevel.raise {k : ℕ} {f : Function n} (hf : IsLevel k f) :
    IsLevel (k + 1) (raise f) := by
  classical
  intro S hS
  unfold MetricCodes.Boolean.raise
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : a ∈ S
  · have herase : (S.erase a).card ≠ k := by
      intro he
      apply hS
      calc
        S.card = (S.erase a).card + 1 :=
          (Finset.card_erase_add_one ha).symm
        _ = k + 1 := by rw [he]
    simp only [raiseAt, ha, ↓reduceIte, hf (S.erase a) herase]
  · simp only [raiseAt, ha, ↓reduceIte]

theorem IsLevel.lower {k : ℕ} {f : Function n}
    (hf : IsLevel (k + 1) f) :
    IsLevel k (lower f) := by
  classical
  intro S hS
  unfold MetricCodes.Boolean.lower
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : a ∈ S
  · simp only [lowerAt, ha, ↓reduceIte]
  · have hinsert : (insert a S).card ≠ k + 1 := by
      intro hi
      have hcard : S.card + 1 = k + 1 := by
        simpa only [Finset.card_insert_of_notMem ha] using hi
      exact hS (Nat.add_right_cancel hcard)
    simp only [lowerAt, ha, ↓reduceIte, hf (insert a S) hinsert]

/-- The raised used in the binary-code argument. -/
def raised {n : ℕ} (f : Function n) : ℕ → Function n
  | 0 => f
  | r + 1 => raise (raised f r)

@[simp] theorem raised_succ (f : Function n) (r : ℕ) :
    raised f (r + 1) = raise (raised f r) := rfl

theorem IsLevel.raised {k : ℕ} {f : Function n}
    (hf : IsLevel k f) (r : ℕ) :
    IsLevel (k + r) (raised f r) := by
  induction r with
  | zero =>
      change IsLevel k f
      exact hf
  | succ r ih =>
      simpa only [raised_succ, Nat.add_assoc] using ih.raise

/-- The harmonic coefficient used in the binary-code argument. -/
def harmonicCoefficient (n k r : ℕ) : ℝ :=
  (r : ℝ) * ((n : ℝ) - 2 * (k : ℝ) - (r : ℝ) + 1)

@[simp] theorem harmonicCoefficient_zero (n k : ℕ) :
    harmonicCoefficient n k 0 = 0 := by
  simp only [harmonicCoefficient, CharP.cast_eq_zero, sub_zero, zero_mul]

theorem harmonicCoefficient_succ (n k r : ℕ) :
    harmonicCoefficient n k (r + 1) =
      harmonicCoefficient n k r +
        ((n : ℝ) - 2 * ((k + r : ℕ) : ℝ)) := by
  simp only [harmonicCoefficient, Nat.cast_add, Nat.cast_one]
  ring

theorem lower_raised_succ_of_harmonic {k : ℕ}
    (f : Function n) (hf : IsHarmonic k f) (r : ℕ) :
    lower (raised f (r + 1)) =
      harmonicCoefficient n k (r + 1) • raised f r := by
  induction r with
  | zero =>
      funext S
      simpa only [raised, harmonicCoefficient, zero_add, Nat.cast_one, sub_add_cancel, one_mul,
        Pi.smul_apply, smul_eq_mul] using lower_raise_of_harmonic f hf S
  | succ r ih =>
      have hlevel : IsLevel (k + (r + 1)) (raised f (r + 1)) :=
        hf.1.raised (r + 1)
      funext S
      have hcomm :=
        lower_raise_sub_raise_lower_of_level
          (raised f (r + 1)) hlevel S
      rw [ih, raise_smul] at hcomm
      have hsum := sub_eq_iff_eq_add.mp hcomm
      calc
        lower (raised f ((r + 1) + 1)) S =
            ((n : ℝ) - 2 * ((k + (r + 1) : ℕ) : ℝ)) *
                raised f (r + 1) S +
              harmonicCoefficient n k (r + 1) * raised f (r + 1) S := by
          simpa only [raised_succ, Pi.smul_apply, smul_eq_mul] using hsum
        _ = harmonicCoefficient n k ((r + 1) + 1) *
              raised f (r + 1) S := by
          rw [harmonicCoefficient_succ n k (r + 1)]
          ring
        _ = (harmonicCoefficient n k ((r + 1) + 1) •
              raised f (r + 1)) S := by
          simp only [raised_succ, Pi.smul_apply, smul_eq_mul]

private def toggle (a : Fin n) (S : Finset (Fin n)) : Finset (Fin n) :=
  if a ∈ S then S.erase a else insert a S

@[simp] theorem toggle_toggle (a : Fin n) (S : Finset (Fin n)) :
    toggle a (toggle a S) = S := by
  classical
  by_cases ha : a ∈ S
  · simp only [toggle, ha, ↓reduceIte, Finset.mem_erase, ne_eq, not_true_eq_false, and_true,
      Finset.insert_erase ha]
  · simp only [toggle, ha, ↓reduceIte, Finset.mem_insert, or_false, Finset.erase_insert ha]

private def toggleEquiv (a : Fin n) : Finset (Fin n) ≃ Finset (Fin n) where
  toFun := toggle a
  invFun := toggle a
  left_inv := toggle_toggle a
  right_inv := toggle_toggle a

/-- The dot used in the binary-code argument. -/
def dot (f g : Function n) : ℝ :=
  ∑ S : Finset (Fin n), f S * g S

theorem dot_raiseAt_eq_lowerAt (a : Fin n) (f g : Function n) :
    dot (raiseAt a f) g = dot f (lowerAt a g) := by
  classical
  unfold dot
  calc
    (∑ S : Finset (Fin n), raiseAt a f S * g S) =
        ∑ S : Finset (Fin n),
          raiseAt a f (toggle a S) * g (toggle a S) := by
      symm
      exact (toggleEquiv a).sum_comp
        (fun S : Finset (Fin n) => raiseAt a f S * g S)
    _ = ∑ S : Finset (Fin n), f S * lowerAt a g S := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases ha : a ∈ S
      · simp only [raiseAt, toggle, ha, ↓reduceIte, Finset.mem_erase, ne_eq, not_true_eq_false,
          and_true, zero_mul, lowerAt, mul_zero]
      · simp only [raiseAt, toggle, ha, ↓reduceIte, Finset.mem_insert, or_false,
          Finset.erase_insert ha, lowerAt]

theorem dot_raise_eq_lower (f g : Function n) :
    dot (raise f) g = dot f (lower g) := by
  classical
  calc
    dot (raise f) g = ∑ a : Fin n, dot (raiseAt a f) g := by
      simp only [dot, raise, Finset.sum_mul]
      exact Finset.sum_comm
    _ = ∑ a : Fin n, dot f (lowerAt a g) := by
      apply Finset.sum_congr rfl
      intro a _
      exact dot_raiseAt_eq_lowerAt a f g
    _ = dot f (lower g) := by
      simp only [dot, lower, Finset.mul_sum]
      exact Finset.sum_comm

theorem dot_comm (f g : Function n) : dot f g = dot g f := by
  classical
  unfold dot
  apply Finset.sum_congr rfl
  intro S _
  exact mul_comm _ _

theorem dot_smul_right (f g : Function n) (c : ℝ) :
    dot f (c • g) = c * dot f g := by
  classical
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem normSq_nonneg (f : Function n) : 0 ≤ (dot f f) := by
  unfold dot
  apply Finset.sum_nonneg
  intro S _
  exact mul_self_nonneg (f S)

@[simp] theorem normSq_eq_zero_iff (f : Function n) :
    (dot f f) = 0 ↔ f = 0 := by
  classical
  change (∑ S : Finset (Fin n), f S * f S) = 0 ↔ f = 0
  constructor
  · intro h
    have hz :=
      (Finset.sum_mul_self_eq_zero_iff
        (Finset.univ : Finset (Finset (Fin n))) f).mp h
    funext S
    exact hz S (Finset.mem_univ S)
  · intro h
    subst f
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]

end Boolean

end

section

open scoped BigOperators Matrix InnerProductSpace

/-- Data encoding the projection family construction. -/
structure ProjectionFamily (X : Type*) (D d : ℕ) where
  /-- The projection component. -/
  projection : X → Matrix (Fin D) (Fin D) ℝ
  symmetric : ∀ x, (projection x)ᵀ = projection x
  idempotent : ∀ x, projection x * projection x = projection x
  trace_eq : ∀ x, Matrix.trace (projection x) = (d : ℝ)

namespace ProjectionFamily

variable {X : Type*} {D d : ℕ}

/-- The overlap used in the metric-code argument. -/
def overlap (P : ProjectionFamily X D d) (x y : X) : ℝ :=
  Matrix.trace (P.projection x * P.projection y)

@[simp] theorem overlap_self (P : ProjectionFamily X D d) (x : X) :
    P.overlap x x = (d : ℝ) := by
  unfold overlap
  rw [P.idempotent x, P.trace_eq x]

theorem overlap_eq_trace_sq (P : ProjectionFamily X D d) (x y : X) :
    P.overlap x y =
      Matrix.trace
        ((P.projection x * P.projection y)ᴴ *
          (P.projection x * P.projection y)) := by
  unfold overlap
  rw [Matrix.conjTranspose_mul,
    Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.conjTranspose_eq_transpose_of_trivial,
    P.symmetric x, P.symmetric y]
  symm
  calc
    Matrix.trace
        ((P.projection y * P.projection x) *
          (P.projection x * P.projection y)) =
        Matrix.trace
          ((P.projection y * (P.projection x * P.projection x)) *
            P.projection y) := by
          congr 1
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace
          ((P.projection y * P.projection x) * P.projection y) := by
          rw [P.idempotent x]
    _ = Matrix.trace
          (P.projection y * (P.projection x * P.projection y)) := by
          rw [Matrix.mul_assoc]
    _ = Matrix.trace
          ((P.projection x * P.projection y) * P.projection y) := by
          exact Matrix.trace_mul_comm _ _
    _ = Matrix.trace
          (P.projection x * (P.projection y * P.projection y)) := by
          rw [Matrix.mul_assoc]
    _ = Matrix.trace (P.projection x * P.projection y) := by
          rw [P.idempotent y]

theorem overlap_nonneg (P : ProjectionFamily X D d) (x y : X) :
    0 ≤ P.overlap x y := by
  rw [P.overlap_eq_trace_sq]
  exact
    (Matrix.posSemidef_conjTranspose_mul_self
      (P.projection x * P.projection y)).trace_nonneg

theorem sq_trace_le_dimension_mul_trace_sq
    (A : Matrix (Fin D) (Fin D) ℝ) :
    (Matrix.trace A) ^ 2 ≤
      (D : ℝ) * Matrix.trace (Aᵀ * A) := by
  classical
  have hdiag :
      (Matrix.trace A) ^ 2 ≤
        (D : ℝ) * ∑ i : Fin D, (A i i) ^ 2 := by
    simpa only [Matrix.trace, Matrix.diag_apply, Finset.card_univ, Fintype.card_fin] using
      (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin D))) (f := fun i : Fin D => A
        i i))
  have hterm (i : Fin D) :
      (A i i) ^ 2 ≤ ∑ j : Fin D, (A i j) ^ 2 :=
    Finset.single_le_sum
      (fun j _ => sq_nonneg (A i j)) (Finset.mem_univ i)
  have hsum :
      (∑ i : Fin D, (A i i) ^ 2) ≤
        ∑ i : Fin D, ∑ j : Fin D, (A i j) ^ 2 :=
    Finset.sum_le_sum (fun i _ => hterm i)
  have htrace :
      Matrix.trace (Aᵀ * A) =
        ∑ i : Fin D, ∑ j : Fin D, (A i j) ^ 2 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.transpose_apply, pow_two]
    rw [Finset.sum_comm]
  calc
    (Matrix.trace A) ^ 2 ≤
        (D : ℝ) * ∑ i : Fin D, (A i i) ^ 2 := hdiag
    _ ≤ (D : ℝ) *
        (∑ i : Fin D, ∑ j : Fin D, (A i j) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg D)
    _ = (D : ℝ) * Matrix.trace (Aᵀ * A) := by rw [htrace]

theorem sum_symmetric (P : ProjectionFamily X D d)
    (C : Finset X) :
    (∑ x ∈ C, P.projection x)ᵀ =
      ∑ x ∈ C, P.projection x := by
  classical
  ext i j
  simp only [Matrix.transpose_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro x _
  have h := congrFun (congrFun (P.symmetric x) i) j
  simpa only [Matrix.transpose_apply] using h

theorem sum_overlap_eq_trace_mul_sum (P : ProjectionFamily X D d)
    (C : Finset X) :
    (∑ x ∈ C, ∑ y ∈ C, P.overlap x y) =
      Matrix.trace
        ((∑ x ∈ C, P.projection x) *
          (∑ y ∈ C, P.projection y)) := by
  classical
  simp only [overlap, Matrix.trace_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem card_mul_rank_sq_le_dimension_mul_sum_overlap
    (P : ProjectionFamily X D d) (C : Finset X) :
    ((C.card : ℝ) * (d : ℝ)) ^ 2 ≤
      (D : ℝ) * (∑ x ∈ C, ∑ y ∈ C, P.overlap x y) := by
  classical
  let A : Matrix (Fin D) (Fin D) ℝ :=
    ∑ x ∈ C, P.projection x
  have htrace : Matrix.trace A = (C.card : ℝ) * (d : ℝ) := by
    dsimp [A]
    simp only [Matrix.trace_sum, P.trace_eq, Finset.sum_const, nsmul_eq_mul]
  have hsym : Aᵀ = A := P.sum_symmetric C
  have hcs := sq_trace_le_dimension_mul_trace_sq A
  rw [htrace, hsym, ← P.sum_overlap_eq_trace_mul_sum C] at hcs
  exact hcs

end ProjectionFamily

section Gram

variable {X E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem gram_double_sum_nonneg (C : Finset X) (q : X → E) :
    0 ≤ ∑ x ∈ C, ∑ y ∈ C, ⟪q x, q y⟫_ℝ := by
  classical
  calc
    0 ≤ ⟪∑ x ∈ C, q x, ∑ x ∈ C, q x⟫_ℝ :=
      real_inner_self_nonneg
    _ = ∑ x ∈ C, ∑ y ∈ C, ⟪q x, q y⟫_ℝ := by
      simp only [sum_inner, inner_sum]
      rw [Finset.sum_comm]

end Gram

section Certificate

variable {X E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {D d : ℕ}

theorem projection_certificate_mul
    (P : ProjectionFamily X D d)
    (C : Finset X)
    (t : X → X → ℝ)
    (q : X → E)
    {s lam : ℝ}
    (hd : 0 < d)
    (hs : s < 1)
    (hgap : s < lam)
    (hdiag : ∀ x ∈ C, t x x = 1)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → t x y ≤ s)
    (hgram : ∀ x ∈ C, ∀ y ∈ C,
      ⟪q x, q y⟫_ℝ = (t x y - lam) * P.overlap x y) :
    (C.card : ℝ) * (lam - s) * (d : ℝ) ≤
      (1 - s) * (D : ℝ) := by
  classical
  let f : X → X → ℝ :=
    fun x y => (t x y - s) * P.overlap x y
  have hfeature (x : X) (hx : x ∈ C)
      (y : X) (hy : y ∈ C) :
      f x y =
        (lam - s) * P.overlap x y + ⟪q x, q y⟫_ℝ := by
    dsimp [f]
    rw [hgram x hx y hy]
    ring
  have hgram_nonneg :
      0 ≤ ∑ x ∈ C, ∑ y ∈ C, ⟪q x, q y⟫_ℝ :=
    gram_double_sum_nonneg C q
  have hfeature_sum :
      (∑ x ∈ C, ∑ y ∈ C, f x y) =
        (lam - s) * (∑ x ∈ C, ∑ y ∈ C, P.overlap x y) +
          (∑ x ∈ C, ∑ y ∈ C, ⟪q x, q y⟫_ℝ) := by
    calc
      (∑ x ∈ C, ∑ y ∈ C, f x y) =
          ∑ x ∈ C, ∑ y ∈ C,
            ((lam - s) * P.overlap x y + ⟪q x, q y⟫_ℝ) := by
              apply Finset.sum_congr rfl
              intro x hx
              apply Finset.sum_congr rfl
              intro y hy
              exact hfeature x hx y hy
      _ = (lam - s) * (∑ x ∈ C, ∑ y ∈ C, P.overlap x y) +
          (∑ x ∈ C, ∑ y ∈ C, ⟪q x, q y⟫_ℝ) := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hlower :
      (lam - s) * (∑ x ∈ C, ∑ y ∈ C, P.overlap x y) ≤
        ∑ x ∈ C, ∑ y ∈ C, f x y := by
    rw [hfeature_sum]
    exact le_add_of_nonneg_right hgram_nonneg
  have hrow (x : X) (hx : x ∈ C) :
      (∑ y ∈ C, f x y) ≤ (1 - s) * (d : ℝ) := by
    calc
      (∑ y ∈ C, f x y) ≤
          ∑ y ∈ C, if y = x then f x x else 0 := by
            apply Finset.sum_le_sum
            intro y hy
            by_cases hyx : y = x
            · subst y
              simp only [↓reduceIte, Std.le_refl]
            · have hnonpos : f x y ≤ 0 := by
                exact mul_nonpos_of_nonpos_of_nonneg
                  (sub_nonpos.mpr
                    (hsep x hx y hy (Ne.symm hyx)))
                  (P.overlap_nonneg x y)
              simpa only [hyx, ↓reduceIte, ge_iff_le] using hnonpos
      _ = f x x := by simp only [Finset.sum_ite_eq', hx, ↓reduceIte]
      _ = (1 - s) * (d : ℝ) := by
        dsimp [f]
        rw [hdiag x hx, P.overlap_self x]
  have hupper :
      (∑ x ∈ C, ∑ y ∈ C, f x y) ≤
        (C.card : ℝ) * (1 - s) * (d : ℝ) := by
    calc
      (∑ x ∈ C, ∑ y ∈ C, f x y) ≤
          ∑ x ∈ C, (1 - s) * (d : ℝ) :=
            Finset.sum_le_sum (fun x hx => hrow x hx)
      _ = (C.card : ℝ) * (1 - s) * (d : ℝ) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  have hoverlap :
      ((C.card : ℝ) * (d : ℝ)) ^ 2 ≤
        (D : ℝ) * (∑ x ∈ C, ∑ y ∈ C, P.overlap x y) :=
    P.card_mul_rank_sq_le_dimension_mul_sum_overlap C
  have hD : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
  have hgap_pos : 0 < lam - s := sub_pos.mpr hgap
  have hmain :
      (lam - s) * ((C.card : ℝ) * (d : ℝ)) ^ 2 ≤
        (D : ℝ) * ((C.card : ℝ) * (1 - s) * (d : ℝ)) := by
    calc
      (lam - s) * ((C.card : ℝ) * (d : ℝ)) ^ 2 ≤
          (lam - s) *
            ((D : ℝ) * (∑ x ∈ C, ∑ y ∈ C, P.overlap x y)) :=
              mul_le_mul_of_nonneg_left hoverlap hgap_pos.le
      _ = (D : ℝ) *
          ((lam - s) *
            (∑ x ∈ C, ∑ y ∈ C, P.overlap x y)) := by ring
      _ ≤ (D : ℝ) * (∑ x ∈ C, ∑ y ∈ C, f x y) :=
        mul_le_mul_of_nonneg_left hlower hD
      _ ≤ (D : ℝ) *
          ((C.card : ℝ) * (1 - s) * (d : ℝ)) :=
        mul_le_mul_of_nonneg_left hupper hD
  by_cases hC : C.Nonempty
  · have hcard : 0 < (C.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hC
    have hrank : 0 < (d : ℝ) := by exact_mod_cast hd
    have hcancel :
        ((C.card : ℝ) * (d : ℝ)) *
            ((C.card : ℝ) * (lam - s) * (d : ℝ)) ≤
          ((C.card : ℝ) * (d : ℝ)) *
            ((1 - s) * (D : ℝ)) := by
      calc
        ((C.card : ℝ) * (d : ℝ)) *
            ((C.card : ℝ) * (lam - s) * (d : ℝ)) =
            (lam - s) * ((C.card : ℝ) * (d : ℝ)) ^ 2 := by ring
        _ ≤ (D : ℝ) *
            ((C.card : ℝ) * (1 - s) * (d : ℝ)) := hmain
        _ = ((C.card : ℝ) * (d : ℝ)) *
            ((1 - s) * (D : ℝ)) := by ring
    exact le_of_mul_le_mul_left hcancel (mul_pos hcard hrank)
  · have hempty : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    subst C
    simpa only [Finset.card_empty, CharP.cast_eq_zero, zero_mul, ge_iff_le] using
      (mul_nonneg (sub_nonneg.mpr hs.le) (Nat.cast_nonneg D))

theorem projection_certificate
    (P : ProjectionFamily X D d)
    (C : Finset X)
    (t : X → X → ℝ)
    (q : X → E)
    {s lam : ℝ}
    (hd : 0 < d)
    (hs : s < 1)
    (hgap : s < lam)
    (hdiag : ∀ x ∈ C, t x x = 1)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → t x y ≤ s)
    (hgram : ∀ x ∈ C, ∀ y ∈ C,
      ⟪q x, q y⟫_ℝ = (t x y - lam) * P.overlap x y) :
    (C.card : ℝ) ≤
      ((1 - s) / (lam - s)) * ((D : ℝ) / (d : ℝ)) := by
  have hrank : 0 < (d : ℝ) := by exact_mod_cast hd
  have hgap_pos : 0 < lam - s := sub_pos.mpr hgap
  have hmul :=
    projection_certificate_mul P C t q hd hs hgap hdiag hsep hgram
  have hdiv :
      (C.card : ℝ) * (d : ℝ) ≤
        ((1 - s) * (D : ℝ)) / (lam - s) := by
    apply (le_div_iff₀ hgap_pos).2
    calc
      ((C.card : ℝ) * (d : ℝ)) * (lam - s) =
          (C.card : ℝ) * (lam - s) * (d : ℝ) := by ring
      _ ≤ (1 - s) * (D : ℝ) := hmul
  calc
    (C.card : ℝ) ≤
        (((1 - s) / (lam - s)) * (D : ℝ)) / (d : ℝ) := by
          apply (le_div_iff₀ hrank).2
          calc
            (C.card : ℝ) * (d : ℝ) ≤
                ((1 - s) * (D : ℝ)) / (lam - s) := hdiv
            _ = ((1 - s) / (lam - s)) * (D : ℝ) := by ring
    _ = ((1 - s) / (lam - s)) * ((D : ℝ) / (d : ℝ)) := by ring

end Certificate

end

section

open scoped BigOperators Matrix

namespace Boolean

variable {n : ℕ}

/-- The sign used in the binary-code argument. -/
def sign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem sign_mul_self (b : Bool) : sign b * sign b = 1 := by
  cases b <;> simp [sign]

private def character (x : BinaryWord n) (S : Finset (Fin n)) : ℝ :=
  ∏ a ∈ S, sign (x a)

@[simp] theorem character_mul_self
    (x : BinaryWord n) (S : Finset (Fin n)) :
    character x S * character x S = 1 := by
  classical
  unfold character
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro a _
  exact sign_mul_self (x a)

private def twist (x : BinaryWord n) (f : Function n) (S : Finset (Fin n)) : ℝ :=
  character x S * f S

theorem twist_smul (x : BinaryWord n) (c : ℝ) (f : Function n) :
    twist x (c • f) = c • twist x f := by
  funext S
  simp only [twist, Pi.smul_apply, smul_eq_mul, mul_left_comm]

theorem dot_twist (x : BinaryWord n) (f g : Function n) :
    dot (twist x f) (twist x g) = dot f g := by
  classical
  unfold dot
  apply Finset.sum_congr rfl
  intro S _
  unfold twist
  calc
    (character x S * f S) * (character x S * g S) =
        (character x S * character x S) * (f S * g S) := by ring
    _ = f S * g S := by rw [character_mul_self, one_mul]

theorem IsLevel.twist {k : ℕ} {f : Function n}
    (hf : IsLevel k f) (x : BinaryWord n) :
    IsLevel k (twist x f) := by
  intro S hS
  change character x S * f S = 0
  rw [hf S hS, mul_zero]

/-- The coordinate function used in the binary-code argument. -/
abbrev CoordinateFunction (n : ℕ) := Fin n → Function n

/-- The coordinate dot used in the binary-code argument. -/
def coordinateDot (f g : CoordinateFunction n) : ℝ :=
  ∑ a : Fin n, dot (f a) (g a)

/-- The delete channel used in the binary-code argument. -/
def deleteChannel (i : ℕ) (f : Function n) : CoordinateFunction n :=
  fun a => (Real.sqrt (i : ℝ))⁻¹ • lowerAt a f

private def addChannel (i : ℕ) (f : Function n) : CoordinateFunction n :=
  fun a => (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ • raiseAt a f

theorem sum_not_mem_indicator (S : Finset (Fin n)) (z : ℝ) :
    (∑ a : Fin n, if a ∈ S then 0 else z) =
      ((n : ℝ) - (S.card : ℝ)) * z := by
  classical
  have hterm (a : Fin n) :
      (if a ∈ S then (0 : ℝ) else z) =
        z - (if a ∈ S then z else 0) := by
    by_cases ha : a ∈ S <;> simp [ha]
  simp_rw [hterm, Finset.sum_sub_distrib]
  rw [sum_mem_indicator]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem sum_dot_lowerAt (f g : Function n) :
    (∑ a : Fin n, dot (lowerAt a f) (lowerAt a g)) =
      ∑ S : Finset (Fin n), (S.card : ℝ) * f S * g S := by
  classical
  calc
    (∑ a : Fin n, dot (lowerAt a f) (lowerAt a g)) =
        ∑ a : Fin n, dot (raiseAt a (lowerAt a f)) g := by
      apply Finset.sum_congr rfl
      intro a _
      exact (dot_raiseAt_eq_lowerAt a (lowerAt a f) g).symm
    _ = ∑ a : Fin n, ∑ S : Finset (Fin n),
          (if a ∈ S then f S else 0) * g S := by
      apply Finset.sum_congr rfl
      intro a _
      unfold dot
      apply Finset.sum_congr rfl
      intro S _
      rw [raiseAt_lowerAt_self]
    _ = ∑ S : Finset (Fin n), ∑ a : Fin n,
          (if a ∈ S then f S else 0) * g S := by
      exact Finset.sum_comm
    _ = ∑ S : Finset (Fin n), (S.card : ℝ) * f S * g S := by
      apply Finset.sum_congr rfl
      intro S _
      rw [← Finset.sum_mul, sum_mem_indicator]

theorem sum_dot_raiseAt (f g : Function n) :
    (∑ a : Fin n, dot (raiseAt a f) (raiseAt a g)) =
      ∑ S : Finset (Fin n),
        ((n : ℝ) - (S.card : ℝ)) * f S * g S := by
  classical
  calc
    (∑ a : Fin n, dot (raiseAt a f) (raiseAt a g)) =
        ∑ a : Fin n, dot f (lowerAt a (raiseAt a g)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact dot_raiseAt_eq_lowerAt a f (raiseAt a g)
    _ = ∑ a : Fin n, ∑ S : Finset (Fin n),
          f S * (if a ∈ S then 0 else g S) := by
      apply Finset.sum_congr rfl
      intro a _
      unfold dot
      apply Finset.sum_congr rfl
      intro S _
      rw [lowerAt_raiseAt_self]
    _ = ∑ S : Finset (Fin n), ∑ a : Fin n,
          f S * (if a ∈ S then 0 else g S) := by
      exact Finset.sum_comm
    _ = ∑ S : Finset (Fin n),
          ((n : ℝ) - (S.card : ℝ)) * f S * g S := by
      apply Finset.sum_congr rfl
      intro S _
      rw [← Finset.mul_sum, sum_not_mem_indicator]
      ring

theorem sum_dot_lowerAt_of_level {i : ℕ} (f g : Function n)
    (hf : IsLevel i f) :
    (∑ a : Fin n, dot (lowerAt a f) (lowerAt a g)) =
      (i : ℝ) * dot f g := by
  classical
  rw [sum_dot_lowerAt]
  calc
    (∑ S : Finset (Fin n), (S.card : ℝ) * f S * g S) =
        ∑ S : Finset (Fin n), (i : ℝ) * f S * g S := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases hS : S.card = i
      · simp only [hS]
      · simp only [hf S hS, mul_zero, zero_mul]
    _ = (i : ℝ) * dot f g := by
      simp only [dot, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ring

theorem sum_dot_raiseAt_of_level {i : ℕ} (f g : Function n)
    (hf : IsLevel i f) :
    (∑ a : Fin n, dot (raiseAt a f) (raiseAt a g)) =
      ((n : ℝ) - (i : ℝ)) * dot f g := by
  classical
  rw [sum_dot_raiseAt]
  calc
    (∑ S : Finset (Fin n),
          ((n : ℝ) - (S.card : ℝ)) * f S * g S) =
        ∑ S : Finset (Fin n),
          ((n : ℝ) - (i : ℝ)) * f S * g S := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases hS : S.card = i
      · simp only [hS]
      · simp only [hf S hS, mul_zero, zero_mul]
    _ = ((n : ℝ) - (i : ℝ)) * dot f g := by
      simp only [dot, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ring

theorem dot_smul_left (f g : Function n) (c : ℝ) :
    dot (c • f) g = c * dot f g := by
  rw [dot_comm, dot_smul_right, dot_comm]

theorem dot_add_right (f g h : Function n) :
    dot f (g + h) = dot f g + dot f h := by
  classical
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem normSq_raise_of_level {i : ℕ}
    (f : Function n) (hf : IsLevel i f) :
    (dot (raise f) (raise f)) = (dot (lower f) (lower f)) +
      ((n : ℝ) - 2 * (i : ℝ)) * (dot f f) := by
  have hcomm :
      lower (raise f) =
        raise (lower f) + ((n : ℝ) - 2 * (i : ℝ)) • f := by
    funext S
    have h :=
      sub_eq_iff_eq_add.mp
        (lower_raise_sub_raise_lower_of_level f hf S)
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_comm] using h
  calc
    (dot (raise f) (raise f)) = dot (raise f) (raise f) := rfl
    _ = dot f (lower (raise f)) := dot_raise_eq_lower f (raise f)
    _ = dot f
          (raise (lower f) + ((n : ℝ) - 2 * (i : ℝ)) • f) := by
      rw [hcomm]
    _ = dot f (raise (lower f)) +
          dot f (((n : ℝ) - 2 * (i : ℝ)) • f) :=
      dot_add_right f (raise (lower f))
        (((n : ℝ) - 2 * (i : ℝ)) • f)
    _ = (dot (lower f) (lower f)) +
          ((n : ℝ) - 2 * (i : ℝ)) * (dot f f) := by
      rw [dot_smul_right, dot_comm f (raise (lower f)),
        dot_raise_eq_lower]

theorem raise_eq_zero_iff_of_level {i : ℕ}
    (hi : 2 * i < n) (f : Function n) (hf : IsLevel i f) :
    raise f = 0 ↔ f = 0 := by
  constructor
  · intro hraise
    have hzero : (dot (raise f) (raise f)) = 0 := by
      rw [hraise]
      simp only [dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    have hidentity := normSq_raise_of_level f hf
    rw [hzero] at hidentity
    have hi' : (2 : ℝ) * (i : ℝ) < (n : ℝ) := by
      exact_mod_cast hi
    have hpos : 0 < (n : ℝ) - 2 * (i : ℝ) := by linarith
    have hnonneg := normSq_nonneg (lower f)
    have hfn := normSq_nonneg f
    have hnorm : (dot f f) = 0 := by nlinarith
    exact (normSq_eq_zero_iff f).mp hnorm
  · intro hfzero
    subst f
    change raiseLinear n (0 : Function n) = 0
    exact map_zero (raiseLinear n)

/-- The layer function used in the binary-code argument. -/
abbrev LayerFunction (n k : ℕ) := Level n k → ℝ

/-- The layer extend used in the binary-code argument. -/
def layerExtend {n k : ℕ} (f : LayerFunction n k) : Function n :=
  fun S => if h : S.card = k then f ⟨S, h⟩ else 0

/-- The layer restrict used in the binary-code argument. -/
def layerRestrict (k : ℕ) (f : Function n) : LayerFunction n k :=
  fun S => f S.val

theorem isLevel_layerExtend {k : ℕ} (f : LayerFunction n k) :
    IsLevel k (layerExtend f) := by
  intro S hS
  simp only [layerExtend, hS, ↓reduceDIte]

@[simp] theorem layerRestrict_layerExtend {k : ℕ}
    (f : LayerFunction n k) :
    layerRestrict k (layerExtend f) = f := by
  funext S
  simp only [layerRestrict, layerExtend, S.property, ↓reduceDIte, Subtype.coe_eta]

theorem layerExtend_layerRestrict_of_level {k : ℕ}
    (f : Function n) (hf : IsLevel k f) :
    layerExtend (layerRestrict k f) = f := by
  funext S
  by_cases hS : S.card = k
  · simp only [layerExtend, hS, ↓reduceDIte, layerRestrict]
  · simp only [layerExtend, hS, ↓reduceDIte, hf S hS]

theorem layerExtend_injective {k : ℕ} :
    Function.Injective (layerExtend (n := n) (k := k)) := by
  intro f g h
  have := congrArg (layerRestrict k) h
  simpa only [layerRestrict_layerExtend] using this

private def layerExtendLinear (n k : ℕ) :
    LayerFunction n k →ₗ[ℝ] Function n where
  toFun := layerExtend
  map_add' := by
    intro f g
    funext S
    by_cases hS : S.card = k <;>
      simp [layerExtend, hS, Pi.add_apply]
  map_smul' := by
    intro c f
    funext S
    by_cases hS : S.card = k <;>
      simp [layerExtend, hS, Pi.smul_apply, smul_eq_mul]

private def layerRestrictLinear (n k : ℕ) :
    Function n →ₗ[ℝ] LayerFunction n k where
  toFun := layerRestrict k
  map_add' := by
    intro f g
    rfl
  map_smul' := by
    intro c f
    rfl

private def layerUp (n k : ℕ) :
    LayerFunction n k →ₗ[ℝ] LayerFunction n (k + 1) :=
  (layerRestrictLinear n (k + 1)).comp
    ((raiseLinear n).comp (layerExtendLinear n k))

private def layerDown (n k : ℕ) :
    LayerFunction n (k + 1) →ₗ[ℝ] LayerFunction n k :=
  (layerRestrictLinear n k).comp
    ((lowerLinear n).comp (layerExtendLinear n (k + 1)))

@[simp] theorem layerUp_apply {k : ℕ} (f : LayerFunction n k) :
    layerUp n k f = layerRestrict (k + 1) (raise (layerExtend f)) := rfl

@[simp] theorem layerDown_apply {k : ℕ}
    (f : LayerFunction n (k + 1)) :
    layerDown n k f = layerRestrict k (lower (layerExtend f)) := rfl

theorem layerUp_injective {k : ℕ} (hk : 2 * k < n) :
    Function.Injective (layerUp n k) := by
  intro f g hfg
  have hflevel : IsLevel (k + 1) (raise (layerExtend f)) :=
    (isLevel_layerExtend f).raise
  have hglevel : IsLevel (k + 1) (raise (layerExtend g)) :=
    (isLevel_layerExtend g).raise
  have hrestrict :
      layerRestrict (k + 1) (raise (layerExtend f)) =
        layerRestrict (k + 1) (raise (layerExtend g)) := by
    simpa only [layerUp_apply] using hfg
  have hfull : raise (layerExtend f) = raise (layerExtend g) := by
    calc
      raise (layerExtend f) =
          layerExtend (layerRestrict (k + 1) (raise (layerExtend f))) :=
        (layerExtend_layerRestrict_of_level _ hflevel).symm
      _ = layerExtend
          (layerRestrict (k + 1) (raise (layerExtend g))) := by
        rw [hrestrict]
      _ = raise (layerExtend g) :=
        layerExtend_layerRestrict_of_level _ hglevel
  have hdifflevel : IsLevel k (layerExtend f - layerExtend g) := by
    intro S hS
    simp only [Pi.sub_apply, layerExtend, hS, ↓reduceDIte, sub_self]
  have hraisezero : raise (layerExtend f - layerExtend g) = 0 := by
    change raiseLinear n (layerExtend f - layerExtend g) = 0
    rw [map_sub, raiseLinear_apply, raiseLinear_apply, hfull, sub_self]
  have hdiffzero : layerExtend f - layerExtend g = 0 :=
    (raise_eq_zero_iff_of_level hk _ hdifflevel).mp hraisezero
  apply layerExtend_injective
  exact sub_eq_zero.mp hdiffzero

/-- The layer dot used in the binary-code argument. -/
def layerDot {n k : ℕ} (f g : LayerFunction n k) : ℝ :=
  ∑ S : Level n k, f S * g S

theorem dot_layerExtend {k : ℕ} (f g : LayerFunction n k) :
    dot (layerExtend f) (layerExtend g) = layerDot f g := by
  classical
  unfold dot layerDot
  refine Finset.sum_congr_set
    {S : Finset (Fin n) | S.card = k}
    (fun S => layerExtend f S * layerExtend g S)
    (fun S : Level n k => f S * g S) ?_ ?_
  · intro S hS
    change S.card = k at hS
    simp only [layerExtend, hS, ↓reduceDIte]
  · intro S hS
    change S.card ≠ k at hS
    simp only [layerExtend, hS, ↓reduceDIte, mul_zero]

theorem layerUp_layerDown_adjoint {k : ℕ}
    (f : LayerFunction n k) (g : LayerFunction n (k + 1)) :
    layerDot (layerUp n k f) g = layerDot f (layerDown n k g) := by
  rw [← dot_layerExtend, ← dot_layerExtend]
  have hup :
      layerExtend (layerUp n k f) = raise (layerExtend f) := by
    rw [layerUp_apply]
    exact layerExtend_layerRestrict_of_level _
      (isLevel_layerExtend f).raise
  have hdown :
      layerExtend (layerDown n k g) = lower (layerExtend g) := by
    rw [layerDown_apply]
    exact layerExtend_layerRestrict_of_level _
      (isLevel_layerExtend g).lower
  rw [hup, hdown, dot_raise_eq_lower]

theorem layerUp_toMatrix_transpose (n k : ℕ) :
    LinearMap.toMatrix' (layerUp n k) =
      (LinearMap.toMatrix' (layerDown n k))ᵀ := by
  classical
  ext T S
  change
    layerUp n k (Pi.single S 1) T =
      layerDown n k (Pi.single T 1) S
  have hadjoint := layerUp_layerDown_adjoint
    (n := n) (k := k) (Pi.single S 1) (Pi.single T 1)
  simpa only [layerUp_apply, layerDown_apply, layerDot, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, ite_mul, one_mul, zero_mul] using hadjoint

theorem layerUp_matrix_rank {k : ℕ} (hk : 2 * k < n) :
    (LinearMap.toMatrix' (layerUp n k)).rank = n.choose k := by
  classical
  have hker : LinearMap.ker (layerUp n k) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (layerUp_injective hk)
  have hrange := (layerUp n k).finrank_range_add_finrank_ker
  rw [hker, finrank_bot, add_zero,
    Module.finrank_fintype_fun_eq_card, card_level] at hrange
  have hlin :
      (LinearMap.toMatrix' (layerUp n k)).mulVecLin =
        layerUp n k := by
    simpa only [Matrix.toLin'_apply'] using
      Matrix.toLin'_toMatrix' (layerUp n k)
  change
    Module.finrank ℝ
      (LinearMap.range
        (LinearMap.toMatrix' (layerUp n k)).mulVecLin) =
      n.choose k
  rw [hlin]
  exact hrange

theorem layerDown_matrix_rank {k : ℕ} (hk : 2 * k < n) :
    (LinearMap.toMatrix' (layerDown n k)).rank = n.choose k := by
  classical
  calc
    (LinearMap.toMatrix' (layerDown n k)).rank =
        ((LinearMap.toMatrix' (layerDown n k))ᵀ).rank :=
      (Matrix.rank_transpose _).symm
    _ = (LinearMap.toMatrix' (layerUp n k)).rank := by
      rw [← layerUp_toMatrix_transpose n k]
    _ = n.choose k := layerUp_matrix_rank hk

theorem layerDown_surjective {k : ℕ} (hk : 2 * k < n) :
    Function.Surjective (layerDown n k) := by
  classical
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, card_level]
  have hlin :
      (LinearMap.toMatrix' (layerDown n k)).mulVecLin =
        layerDown n k := by
    simpa only [Matrix.toLin'_apply'] using
      Matrix.toLin'_toMatrix' (layerDown n k)
  calc
    Module.finrank ℝ (LinearMap.range (layerDown n k)) =
        (LinearMap.toMatrix' (layerDown n k)).rank := by
      change
        Module.finrank ℝ (LinearMap.range (layerDown n k)) =
          Module.finrank ℝ
            (LinearMap.range
              (LinearMap.toMatrix' (layerDown n k)).mulVecLin)
      rw [hlin]
    _ = n.choose k := layerDown_matrix_rank hk

theorem finrank_ker_layerDown {k : ℕ} (hk : 2 * k < n) :
    Module.finrank ℝ (LinearMap.ker (layerDown n k)) =
      n.choose (k + 1) - n.choose k := by
  have hrange : LinearMap.range (layerDown n k) = ⊤ :=
    LinearMap.range_eq_top.mpr (layerDown_surjective hk)
  have hcod : Module.finrank ℝ (LayerFunction n k) = n.choose k := by
    change Module.finrank ℝ (Level n k → ℝ) = n.choose k
    rw [Module.finrank_fintype_fun_eq_card, card_level]
  have hdomain :
      Module.finrank ℝ (LayerFunction n (k + 1)) =
        n.choose (k + 1) := by
    change
      Module.finrank ℝ (Level n (k + 1) → ℝ) = n.choose (k + 1)
    rw [Module.finrank_fintype_fun_eq_card, card_level]
  have hrank := (layerDown n k).finrank_range_add_finrank_ker
  rw [hrange, finrank_top, hcod, hdomain] at hrank
  exact Nat.eq_sub_of_add_eq' hrank

/-- The harmonic layer used in the binary-code argument. -/
def harmonicLayer (n : ℕ) :
    (k : ℕ) → Submodule ℝ (LayerFunction n k)
  | 0 => ⊤
  | k + 1 => LinearMap.ker (layerDown n k)

theorem harmonicLayer_finrank (n k : ℕ) (hk : 2 * k ≤ n) :
    Module.finrank ℝ (harmonicLayer n k) =
      MetricCodes.hammingFibreDimension n k := by
  cases k with
  | zero =>
      change Module.finrank ℝ (⊤ : Submodule ℝ (LayerFunction n 0)) =
        MetricCodes.hammingFibreDimension n 0
      rw [finrank_top,
        Module.finrank_fintype_fun_eq_card, card_level]
      simp only [Nat.choose_zero_right, hammingFibreDimension, booleanHarmonicDimension]
  | succ k =>
      have hbelow : 2 * k < n := by omega
      change
        Module.finrank ℝ (LinearMap.ker (layerDown n k)) =
          n.choose (k + 1) - n.choose k
      exact finrank_ker_layerDown (n := n) (k := k) hbelow

theorem deleteChannel_isometry {i : ℕ} (hi : 0 < i)
    (f g : Function n) (hf : IsLevel i f) :
    coordinateDot (deleteChannel i f) (deleteChannel i g) = dot f g := by
  classical
  have hi' : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
  have hs : Real.sqrt (i : ℝ) ≠ 0 := (Real.sqrt_pos.2 hi').ne'
  have hsqr : Real.sqrt (i : ℝ) * Real.sqrt (i : ℝ) = (i : ℝ) :=
    Real.mul_self_sqrt hi'.le
  have hscalar :
      (Real.sqrt (i : ℝ))⁻¹ * (Real.sqrt (i : ℝ))⁻¹ * (i : ℝ) = 1 := by
    calc
      (Real.sqrt (i : ℝ))⁻¹ * (Real.sqrt (i : ℝ))⁻¹ * (i : ℝ) =
          (Real.sqrt (i : ℝ))⁻¹ * (Real.sqrt (i : ℝ))⁻¹ *
            (Real.sqrt (i : ℝ) * Real.sqrt (i : ℝ)) := by rw [hsqr]
      _ = 1 := by field_simp [hs]
  calc
    coordinateDot (deleteChannel i f) (deleteChannel i g) =
        ((Real.sqrt (i : ℝ))⁻¹ * (Real.sqrt (i : ℝ))⁻¹) *
          (∑ a : Fin n, dot (lowerAt a f) (lowerAt a g)) := by
      simp only [coordinateDot, deleteChannel, dot_smul_left,
        dot_smul_right, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ((Real.sqrt (i : ℝ))⁻¹ * (Real.sqrt (i : ℝ))⁻¹) *
          ((i : ℝ) * dot f g) := by rw [sum_dot_lowerAt_of_level f g hf]
    _ = ((Real.sqrt (i : ℝ))⁻¹ * (Real.sqrt (i : ℝ))⁻¹ *
          (i : ℝ)) * dot f g := by ring
    _ = dot f g := by rw [hscalar, one_mul]

theorem addChannel_isometry {i : ℕ} (hi : i < n)
    (f g : Function n) (hf : IsLevel i f) :
    coordinateDot (addChannel i f) (addChannel i g) = dot f g := by
  classical
  have hi' : (i : ℝ) < (n : ℝ) := by exact_mod_cast hi
  have hpos : 0 < (n : ℝ) - (i : ℝ) := sub_pos.mpr hi'
  have hs : Real.sqrt ((n : ℝ) - (i : ℝ)) ≠ 0 :=
    (Real.sqrt_pos.2 hpos).ne'
  have hsqr :
      Real.sqrt ((n : ℝ) - (i : ℝ)) *
          Real.sqrt ((n : ℝ) - (i : ℝ)) = (n : ℝ) - (i : ℝ) :=
    Real.mul_self_sqrt hpos.le
  have hscalar :
      (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
          (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
            ((n : ℝ) - (i : ℝ)) = 1 := by
    calc
      (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
          (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
            ((n : ℝ) - (i : ℝ)) =
        (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
          (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
            (Real.sqrt ((n : ℝ) - (i : ℝ)) *
              Real.sqrt ((n : ℝ) - (i : ℝ))) := by rw [hsqr]
      _ = 1 := by field_simp [hs]
  calc
    coordinateDot (addChannel i f) (addChannel i g) =
        ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
          (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹) *
            (∑ a : Fin n, dot (raiseAt a f) (raiseAt a g)) := by
      simp only [coordinateDot, addChannel, dot_smul_left,
        dot_smul_right, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
          (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹) *
            (((n : ℝ) - (i : ℝ)) * dot f g) := by
      rw [sum_dot_raiseAt_of_level f g hf]
    _ = ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
          (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
            ((n : ℝ) - (i : ℝ))) * dot f g := by ring
    _ = dot f g := by rw [hscalar, one_mul]

theorem dot_lowerAt_raiseAt (a : Fin n) (f g : Function n) :
    dot (lowerAt a f) (raiseAt a g) = 0 := by
  classical
  unfold dot
  apply Finset.sum_eq_zero
  intro S _
  by_cases ha : a ∈ S <;> simp [lowerAt, raiseAt, ha]

theorem deleteChannel_orthogonal_addChannel (i j : ℕ)
    (f g : Function n) :
    coordinateDot (deleteChannel i f) (addChannel j g) = 0 := by
  classical
  unfold coordinateDot deleteChannel addChannel
  apply Finset.sum_eq_zero
  intro a _
  rw [dot_smul_left, dot_smul_right, dot_lowerAt_raiseAt]
  simp only [mul_zero]

/-- The harmonic norm factor used in the binary-code argument. -/
def harmonicNormFactor (n k r : ℕ) : ℝ :=
  ∏ j ∈ Finset.range r, harmonicCoefficient n k (j + 1)

@[simp] theorem harmonicNormFactor_zero (n k : ℕ) :
    harmonicNormFactor n k 0 = 1 := by
  simp only [harmonicNormFactor, Finset.range_zero, Finset.prod_empty]

theorem harmonicCoefficient_pos {n k r : ℕ}
    (hr : 0 < r) (hbound : 2 * k + r ≤ n) :
    0 < harmonicCoefficient n k r := by
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hbound' :
      (2 : ℝ) * (k : ℝ) + (r : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hbound
  unfold harmonicCoefficient
  apply mul_pos hr'
  linarith

theorem harmonicNormFactor_pos {n k r : ℕ}
    (hbound : 2 * k + r ≤ n) :
    0 < harmonicNormFactor n k r := by
  unfold harmonicNormFactor
  apply Finset.prod_pos
  intro j hj
  have hj' : j < r := Finset.mem_range.mp hj
  apply harmonicCoefficient_pos (Nat.succ_pos j)
  exact (Nat.add_le_add_left (Nat.succ_le_of_lt hj') (2 * k)).trans hbound

theorem dot_raised_succ_of_harmonic {k : ℕ}
    (f g : Function n) (hg : IsHarmonic k g) (r : ℕ) :
    dot (raised f (r + 1)) (raised g (r + 1)) =
      harmonicCoefficient n k (r + 1) *
        dot (raised f r) (raised g r) := by
  calc
    dot (raised f (r + 1)) (raised g (r + 1)) =
        dot (raise (raised f r)) (raise (raised g r)) := rfl
    _ = dot (raised f r) (lower (raise (raised g r))) :=
      dot_raise_eq_lower (raised f r) (raise (raised g r))
    _ = dot (raised f r) (lower (raised g (r + 1))) := rfl
    _ = dot (raised f r)
          (harmonicCoefficient n k (r + 1) • raised g r) := by
      rw [lower_raised_succ_of_harmonic g hg r]
    _ = harmonicCoefficient n k (r + 1) *
          dot (raised f r) (raised g r) := by
      rw [dot_smul_right]

theorem dot_raised_of_harmonic {k : ℕ}
    (f g : Function n) (hg : IsHarmonic k g) (r : ℕ) :
    dot (raised f r) (raised g r) =
      harmonicNormFactor n k r * dot f g := by
  induction r with
  | zero => simp only [raised, harmonicNormFactor, Finset.range_zero, Finset.prod_empty, one_mul]
  | succ r ih =>
      rw [dot_raised_succ_of_harmonic f g hg r, ih]
      simp only [harmonicNormFactor, Finset.prod_range_succ]
      ring

/-- The harmonic embedding used in the binary-code argument. -/
def harmonicEmbedding (k r : ℕ) (f : Function n) : Function n :=
  (Real.sqrt (harmonicNormFactor n k r))⁻¹ • raised f r

private def wordHarmonicEmbedding (x : BinaryWord n) (k r : ℕ)
    (f : Function n) : Function n :=
  twist x (harmonicEmbedding k r f)

theorem harmonicEmbedding_isometry {k : ℕ}
    (f g : Function n) (hg : IsHarmonic k g) (r : ℕ)
    (hbound : 2 * k + r ≤ n) :
    dot (harmonicEmbedding k r f) (harmonicEmbedding k r g) =
      dot f g := by
  have hpos : 0 < harmonicNormFactor n k r :=
    harmonicNormFactor_pos hbound
  have hs : Real.sqrt (harmonicNormFactor n k r) ≠ 0 :=
    (Real.sqrt_pos.2 hpos).ne'
  have hsqr :
      Real.sqrt (harmonicNormFactor n k r) *
          Real.sqrt (harmonicNormFactor n k r) =
        harmonicNormFactor n k r :=
    Real.mul_self_sqrt hpos.le
  have hscalar :
      (Real.sqrt (harmonicNormFactor n k r))⁻¹ *
          (Real.sqrt (harmonicNormFactor n k r))⁻¹ *
            harmonicNormFactor n k r = 1 := by
    calc
      (Real.sqrt (harmonicNormFactor n k r))⁻¹ *
          (Real.sqrt (harmonicNormFactor n k r))⁻¹ *
            harmonicNormFactor n k r =
        (Real.sqrt (harmonicNormFactor n k r))⁻¹ *
          (Real.sqrt (harmonicNormFactor n k r))⁻¹ *
            (Real.sqrt (harmonicNormFactor n k r) *
              Real.sqrt (harmonicNormFactor n k r)) := by rw [hsqr]
      _ = 1 := by field_simp [hs]
  calc
    dot (harmonicEmbedding k r f) (harmonicEmbedding k r g) =
        ((Real.sqrt (harmonicNormFactor n k r))⁻¹ *
          (Real.sqrt (harmonicNormFactor n k r))⁻¹) *
            dot (raised f r) (raised g r) := by
      simp only [harmonicEmbedding, dot_smul_left, dot_smul_right]
      ring
    _ = ((Real.sqrt (harmonicNormFactor n k r))⁻¹ *
          (Real.sqrt (harmonicNormFactor n k r))⁻¹) *
            (harmonicNormFactor n k r * dot f g) := by
      rw [dot_raised_of_harmonic f g hg r]
    _ = ((Real.sqrt (harmonicNormFactor n k r))⁻¹ *
          (Real.sqrt (harmonicNormFactor n k r))⁻¹ *
            harmonicNormFactor n k r) * dot f g := by ring
    _ = dot f g := by rw [hscalar, one_mul]

theorem wordHarmonicEmbedding_isometry {k : ℕ}
    (x : BinaryWord n) (f g : Function n)
    (hg : IsHarmonic k g) (r : ℕ) (hbound : 2 * k + r ≤ n) :
    dot (wordHarmonicEmbedding x k r f)
        (wordHarmonicEmbedding x k r g) = dot f g := by
  unfold wordHarmonicEmbedding
  rw [dot_twist]
  exact harmonicEmbedding_isometry f g hg r hbound

theorem IsLevel.harmonicEmbedding {k : ℕ} {f : Function n}
    (hf : IsLevel k f) (r : ℕ) :
    IsLevel (k + r) (harmonicEmbedding k r f) := by
  intro S hS
  change
    (Real.sqrt (harmonicNormFactor n k r))⁻¹ *
      MetricCodes.Boolean.raised f r S = 0
  rw [(MetricCodes.Boolean.IsLevel.raised hf r) S hS, mul_zero]

theorem IsLevel.wordHarmonicEmbedding {k : ℕ} {f : Function n}
    (hf : IsLevel k f) (x : BinaryWord n) (r : ℕ) :
    IsLevel (k + r) (wordHarmonicEmbedding x k r f) := by
  exact (hf.harmonicEmbedding r).twist x

theorem mem_harmonicLayer_iff {k : ℕ} (f : LayerFunction n k) :
    f ∈ harmonicLayer n k ↔ IsHarmonic k (layerExtend f) := by
  classical
  cases k with
  | zero =>
      constructor
      · intro _
        refine ⟨isLevel_layerExtend f, ?_⟩
        intro S
        unfold lower
        apply Finset.sum_eq_zero
        intro a _
        by_cases ha : a ∈ S
        · simp only [lowerAt, ha, ↓reduceIte]
        · have hcard : (insert a S).card ≠ 0 :=
            Finset.card_ne_zero_of_mem (Finset.mem_insert_self a S)
          simp only [lowerAt, ha, ↓reduceIte, layerExtend, not_false_eq_true,
            Finset.card_insert_of_notMem, Nat.add_eq_zero_iff, Finset.card_eq_zero, one_ne_zero,
            and_false, ↓reduceDIte]
      · intro _
        exact Submodule.mem_top
  | succ k =>
      constructor
      · intro hf
        change f ∈ LinearMap.ker (layerDown n k) at hf
        have hdown : layerDown n k f = 0 := LinearMap.mem_ker.mp hf
        refine ⟨isLevel_layerExtend f, ?_⟩
        have hrestrict :
            layerRestrict k (lower (layerExtend f)) = 0 := by
          simpa only [layerDown_apply] using hdown
        have hlower : lower (layerExtend f) = 0 := by
          calc
            lower (layerExtend f) =
                layerExtend (layerRestrict k (lower (layerExtend f))) :=
              (layerExtend_layerRestrict_of_level _
                (isLevel_layerExtend f).lower).symm
            _ = layerExtend (0 : LayerFunction n k) := by rw [hrestrict]
            _ = 0 := by
              change layerExtendLinear n k (0 : LayerFunction n k) = 0
              exact map_zero (layerExtendLinear n k)
        exact fun S => congrFun hlower S
      · intro hf
        change f ∈ LinearMap.ker (layerDown n k)
        apply LinearMap.mem_ker.mpr
        rw [layerDown_apply]
        have hlower : lower (layerExtend f) = 0 := funext hf.2
        rw [hlower]
        change layerRestrictLinear n k (0 : Function n) = 0
        exact map_zero (layerRestrictLinear n k)

/-- The euclidean layer used in the binary-code argument. -/
abbrev EuclideanLayer (n k : ℕ) := EuclideanSpace ℝ (Level n k)

/-- The harmonic euclidean layer used in the binary-code argument. -/
def harmonicEuclideanLayer (n k : ℕ) :
    Submodule ℝ (EuclideanLayer n k) :=
  (harmonicLayer n k).map
    (WithLp.linearEquiv 2 ℝ (LayerFunction n k)).symm.toLinearMap

theorem harmonicEuclideanLayer_finrank
    (n k : ℕ) (hk : 2 * k ≤ n) :
    Module.finrank ℝ (harmonicEuclideanLayer n k) =
      MetricCodes.hammingFibreDimension n k := by
  calc
    Module.finrank ℝ (harmonicEuclideanLayer n k) =
        Module.finrank ℝ (harmonicLayer n k) := by
      change
        Module.finrank ℝ
            ((harmonicLayer n k).map
              (WithLp.linearEquiv 2 ℝ (LayerFunction n k)).symm.toLinearMap) =
          Module.finrank ℝ (harmonicLayer n k)
      exact
        (WithLp.linearEquiv 2 ℝ (LayerFunction n k)).symm.finrank_map_eq
          (harmonicLayer n k)
    _ = MetricCodes.hammingFibreDimension n k := harmonicLayer_finrank n k hk

/-- The harmonic orthonormal basis used in the binary-code argument. -/
def harmonicOrthonormalBasis
    (n k : ℕ) (hk : 2 * k ≤ n) :
    OrthonormalBasis (Fin (MetricCodes.hammingFibreDimension n k)) ℝ
      (harmonicEuclideanLayer n k) :=
  (stdOrthonormalBasis ℝ (harmonicEuclideanLayer n k)).reindex
    (finCongr (harmonicEuclideanLayer_finrank n k hk))

/-- The harmonic basis function used in the binary-code argument. -/
def harmonicBasisFunction
    (n k : ℕ) (hk : 2 * k ≤ n)
    (p : Fin (MetricCodes.hammingFibreDimension n k)) : Function n :=
  layerExtend
    (WithLp.ofLp ((harmonicOrthonormalBasis n k hk p).val))

theorem harmonicBasisFunction_isHarmonic
    (n k : ℕ) (hk : 2 * k ≤ n)
    (p : Fin (MetricCodes.hammingFibreDimension n k)) :
    IsHarmonic k (harmonicBasisFunction n k hk p) := by
  let b := harmonicOrthonormalBasis n k hk p
  have hmem : b.val ∈ harmonicEuclideanLayer n k := b.property
  change
    b.val ∈
      (harmonicLayer n k).map
        (WithLp.linearEquiv 2 ℝ (LayerFunction n k)).symm.toLinearMap
    at hmem
  obtain ⟨g, hg, heq⟩ := (Submodule.mem_map).mp hmem
  have hcoef : WithLp.ofLp b.val = g := by
    have h := congrArg
      (fun z : EuclideanLayer n k => WithLp.ofLp z) heq.symm
    simpa only [LinearEquiv.coe_coe, WithLp.linearEquiv_symm_apply, AddEquiv.toEquiv_eq_coe,
      Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm, WithLp.addEquiv_symm_apply] using h
  change IsHarmonic k (layerExtend (WithLp.ofLp b.val))
  apply (mem_harmonicLayer_iff (WithLp.ofLp b.val)).mp
  rw [hcoef]
  exact hg

private def hammingWindowDimension (n k L : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (L - k + 1), n.choose (k + j)

private abbrev HammingWindowIndex (n k L : ℕ) :=
  Σ j : Fin (L - k + 1), Level n (k + j.val)

theorem hammingWindowIndex_card (n k L : ℕ) :
    Fintype.card (HammingWindowIndex n k L) =
      hammingWindowDimension n k L := by
  classical
  rw [Fintype.card_sigma]
  simp only [card_level]
  unfold hammingWindowDimension
  refine Finset.sum_bij (fun j _ => j.val) ?_ ?_ ?_ ?_
  · intro j _
    exact Finset.mem_range.mpr j.isLt
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro j hj
    refine ⟨⟨j, Finset.mem_range.mp hj⟩, Finset.mem_univ _, rfl⟩
  · intro j _
    rfl

private def hammingWindowIndexEquiv (n k L : ℕ) :
    HammingWindowIndex n k L ≃ Fin (hammingWindowDimension n k L) :=
  Fintype.equivOfCardEq (by
    simpa only [Fintype.card_sigma, Fintype.card_finset_len,
      Fintype.card_fin] using hammingWindowIndex_card n k L)

private def hammingRecurrenceWeight
    (n k L : ℕ) (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (j : Fin (L - k + 1)) : ℝ :=
  Real.sqrt (n.choose (k + j.val) : ℝ) * v j

private def hammingRecurrenceNormalization
    (n k L : ℕ) (v : EuclideanSpace ℝ (Fin (L - k + 1))) : ℝ :=
  ∑ j : Fin (L - k + 1), hammingRecurrenceWeight n k L v j

private def hammingFibreAmplitude
    (n k L : ℕ) (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (j : Fin (L - k + 1)) : ℝ :=
  Real.sqrt
    (hammingRecurrenceWeight n k L v j /
      hammingRecurrenceNormalization n k L v)

theorem hammingRecurrenceWeight_nonneg
    (n k L : ℕ) (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hv : ∀ j : Fin (L - k + 1), 0 ≤ v j)
    (j : Fin (L - k + 1)) :
    0 ≤ hammingRecurrenceWeight n k L v j := by
  exact mul_nonneg (Real.sqrt_nonneg _) (hv j)

theorem hammingRecurrenceNormalization_pos
    {n k L : ℕ} (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ j : Fin (L - k + 1), 0 ≤ v j) :
    0 < hammingRecurrenceNormalization n k L v := by
  classical
  have hvzero : v ≠ 0 := by
    intro hzero
    simp only [hzero, norm_zero, zero_ne_one] at hunit
  obtain ⟨j, hj⟩ : ∃ j : Fin (L - k + 1), 0 < v j := by
    by_contra hnone
    simp only [not_exists, not_lt] at hnone
    apply hvzero
    apply PiLp.ext
    intro i
    change v i = 0
    exact le_antisymm (hnone i) (hv i)
  have hlevel : k + j.val ≤ n := by
    have hjbound := j.isLt
    omega
  have hdimension : 0 < (n.choose (k + j.val) : ℝ) := by
    exact_mod_cast Nat.choose_pos hlevel
  unfold hammingRecurrenceNormalization
  apply Finset.sum_pos'
  · intro i _
    exact hammingRecurrenceWeight_nonneg n k L v hv i
  · refine ⟨j, Finset.mem_univ j, ?_⟩
    exact mul_pos (Real.sqrt_pos.2 hdimension) hj

theorem hammingFibreAmplitude_sq
    {n k L : ℕ} (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ j : Fin (L - k + 1), 0 ≤ v j)
    (j : Fin (L - k + 1)) :
    hammingFibreAmplitude n k L v j ^ 2 =
      hammingRecurrenceWeight n k L v j /
        hammingRecurrenceNormalization n k L v := by
  unfold hammingFibreAmplitude
  apply Real.sq_sqrt
  exact div_nonneg
    (hammingRecurrenceWeight_nonneg n k L v hv j)
    (hammingRecurrenceNormalization_pos hkL hLn v hunit hv).le

theorem hammingFibreAmplitude_sq_sum
    {n k L : ℕ} (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ j : Fin (L - k + 1), 0 ≤ v j) :
    (∑ j : Fin (L - k + 1), hammingFibreAmplitude n k L v j ^ 2) =
      1 := by
  simp_rw [hammingFibreAmplitude_sq hkL hLn v hunit hv]
  rw [← Finset.sum_div]
  change
    hammingRecurrenceNormalization n k L v /
      hammingRecurrenceNormalization n k L v = 1
  exact div_self
    (hammingRecurrenceNormalization_pos hkL hLn v hunit hv).ne'

theorem harmonicBasisFunction_dot
    (n k : ℕ) (hk : 2 * k ≤ n)
    (p q : Fin (MetricCodes.hammingFibreDimension n k)) :
    dot (harmonicBasisFunction n k hk p)
        (harmonicBasisFunction n k hk q) =
      if p = q then 1 else 0 := by
  classical
  unfold harmonicBasisFunction
  rw [dot_layerExtend]
  have h := (harmonicOrthonormalBasis n k hk).inner_eq_ite p q
  simpa only [layerDot, Submodule.coe_inner, PiLp.inner_apply, RCLike.inner_apply,
    Real.ringHom_apply, mul_comm] using h

theorem dot_eq_layerDot_of_level {i : ℕ}
    (f g : Function n) (hf : IsLevel i f) (hg : IsLevel i g) :
    dot f g = layerDot (layerRestrict i f) (layerRestrict i g) := by
  rw [← dot_layerExtend,
    layerExtend_layerRestrict_of_level f hf,
    layerExtend_layerRestrict_of_level g hg]

private def hammingWindowFibreMatrix
    (n k L : ℕ) (hk : 2 * k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (x : BinaryWord n) :
    Matrix (HammingWindowIndex n k L)
      (Fin (MetricCodes.hammingFibreDimension n k)) ℝ :=
  fun T p =>
    hammingFibreAmplitude n k L v T.1 *
      wordHarmonicEmbedding x k T.1.val
        (harmonicBasisFunction n k hk p) T.2.val

theorem hammingWindowFibreMatrix_transpose_mul
    {n k L : ℕ} (hk : 2 * k ≤ n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ j : Fin (L - k + 1), 0 ≤ v j)
    (x : BinaryWord n) :
    (hammingWindowFibreMatrix n k L hk v x)ᵀ *
        hammingWindowFibreMatrix n k L hk v x = 1 := by
  classical
  ext p q
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
  change
    (∑ T : HammingWindowIndex n k L,
      hammingWindowFibreMatrix n k L hk v x T p *
        hammingWindowFibreMatrix n k L hk v x T q) =
      if p = q then 1 else 0
  calc
    (∑ T : HammingWindowIndex n k L,
      hammingWindowFibreMatrix n k L hk v x T p *
        hammingWindowFibreMatrix n k L hk v x T q) =
      ∑ j : Fin (L - k + 1),
        hammingFibreAmplitude n k L v j ^ 2 *
          dot
            (wordHarmonicEmbedding x k j.val
              (harmonicBasisFunction n k hk p))
            (wordHarmonicEmbedding x k j.val
              (harmonicBasisFunction n k hk q)) := by
        simp only [hammingWindowFibreMatrix]
        rw [Fintype.sum_sigma]
        apply Finset.sum_congr rfl
        intro j _
        change
          (∑ S : Level n (k + j.val),
            (hammingFibreAmplitude n k L v j *
              wordHarmonicEmbedding x k j.val
                (harmonicBasisFunction n k hk p) S.val) *
            (hammingFibreAmplitude n k L v j *
              wordHarmonicEmbedding x k j.val
                (harmonicBasisFunction n k hk q) S.val)) =
            hammingFibreAmplitude n k L v j ^ 2 *
              dot
                (wordHarmonicEmbedding x k j.val
                  (harmonicBasisFunction n k hk p))
                (wordHarmonicEmbedding x k j.val
                  (harmonicBasisFunction n k hk q))
        calc
          (∑ S : Level n (k + j.val),
            (hammingFibreAmplitude n k L v j *
              wordHarmonicEmbedding x k j.val
                (harmonicBasisFunction n k hk p) S.val) *
            (hammingFibreAmplitude n k L v j *
              wordHarmonicEmbedding x k j.val
                (harmonicBasisFunction n k hk q) S.val)) =
              hammingFibreAmplitude n k L v j ^ 2 *
                (∑ S : Level n (k + j.val),
                  wordHarmonicEmbedding x k j.val
                    (harmonicBasisFunction n k hk p) S.val *
                  wordHarmonicEmbedding x k j.val
                    (harmonicBasisFunction n k hk q) S.val) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro S _
                ring
          _ = hammingFibreAmplitude n k L v j ^ 2 *
              dot
                (wordHarmonicEmbedding x k j.val
                  (harmonicBasisFunction n k hk p))
                (wordHarmonicEmbedding x k j.val
                  (harmonicBasisFunction n k hk q)) := by
                congr 1
                exact
                  (dot_eq_layerDot_of_level
                    (wordHarmonicEmbedding x k j.val
                      (harmonicBasisFunction n k hk p))
                    (wordHarmonicEmbedding x k j.val
                      (harmonicBasisFunction n k hk q))
                    (MetricCodes.Boolean.IsLevel.wordHarmonicEmbedding
                      (harmonicBasisFunction_isHarmonic n k hk p).1
                      x j.val)
                    (MetricCodes.Boolean.IsLevel.wordHarmonicEmbedding
                      (harmonicBasisFunction_isHarmonic n k hk q).1
                      x j.val)).symm
    _ = ∑ j : Fin (L - k + 1),
          hammingFibreAmplitude n k L v j ^ 2 *
            (if p = q then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        have hjbound : 2 * k + j.val ≤ n := by
          have hj := j.isLt
          omega
        rw [wordHarmonicEmbedding_isometry x
          (harmonicBasisFunction n k hk p)
          (harmonicBasisFunction n k hk q)
          (harmonicBasisFunction_isHarmonic n k hk q)
          j.val hjbound, harmonicBasisFunction_dot]
    _ = (if p = q then 1 else 0) := by
        by_cases hpq : p = q
        · simp only [hpq, ↓reduceIte, mul_one, hammingFibreAmplitude_sq_sum hkL hLn v hunit hv]
        · simp only [hpq, ↓reduceIte, mul_zero, Finset.sum_const_zero]

private def hammingFibreMatrix
    (n k L : ℕ) (hk : 2 * k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (x : BinaryWord n) :
    Matrix (Fin (hammingWindowDimension n k L))
      (Fin (MetricCodes.hammingFibreDimension n k)) ℝ :=
  fun i p =>
    hammingWindowFibreMatrix n k L hk v x
      ((hammingWindowIndexEquiv n k L).symm i) p

theorem hammingFibreMatrix_transpose_mul
    {n k L : ℕ} (hk : 2 * k ≤ n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ j : Fin (L - k + 1), 0 ≤ v j)
    (x : BinaryWord n) :
    (hammingFibreMatrix n k L hk v x)ᵀ *
        hammingFibreMatrix n k L hk v x = 1 := by
  classical
  ext p q
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
  change
    (∑ i : Fin (hammingWindowDimension n k L),
      hammingWindowFibreMatrix n k L hk v x
        ((hammingWindowIndexEquiv n k L).symm i) p *
      hammingWindowFibreMatrix n k L hk v x
        ((hammingWindowIndexEquiv n k L).symm i) q) =
      if p = q then 1 else 0
  calc
    (∑ i : Fin (hammingWindowDimension n k L),
      hammingWindowFibreMatrix n k L hk v x
        ((hammingWindowIndexEquiv n k L).symm i) p *
      hammingWindowFibreMatrix n k L hk v x
        ((hammingWindowIndexEquiv n k L).symm i) q) =
      ∑ T : HammingWindowIndex n k L,
        hammingWindowFibreMatrix n k L hk v x T p *
          hammingWindowFibreMatrix n k L hk v x T q :=
        (hammingWindowIndexEquiv n k L).symm.sum_comp
          (fun T =>
            hammingWindowFibreMatrix n k L hk v x T p *
              hammingWindowFibreMatrix n k L hk v x T q)
    _ = (if p = q then 1 else 0) := by
        have h := congrArg
          (fun M : Matrix
              (Fin (MetricCodes.hammingFibreDimension n k))
              (Fin (MetricCodes.hammingFibreDimension n k)) ℝ => M p q)
          (hammingWindowFibreMatrix_transpose_mul
            hk hkL hLn v hunit hv x)
        simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h

/-- The hamming projection family used in the binary-code argument. -/
def hammingProjectionFamily
    {n k L : ℕ} (hk : 2 * k ≤ n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ j : Fin (L - k + 1), 0 ≤ v j) :
    MetricCodes.ProjectionFamily (BinaryWord n)
      (hammingWindowDimension n k L)
      (MetricCodes.hammingFibreDimension n k) where
  projection x :=
    hammingFibreMatrix n k L hk v x *
      (hammingFibreMatrix n k L hk v x)ᵀ
  symmetric x := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  idempotent x := by
    let A := hammingFibreMatrix n k L hk v x
    change (A * Aᵀ) * (A * Aᵀ) = A * Aᵀ
    calc
      (A * Aᵀ) * (A * Aᵀ) = A * ((Aᵀ * A) * Aᵀ) := by
        simp only [Matrix.mul_assoc]
      _ = A * Aᵀ := by
        rw [hammingFibreMatrix_transpose_mul hk hkL hLn
          v hunit hv x, Matrix.one_mul]
  trace_eq x := by
    rw [Matrix.trace_mul_comm,
      hammingFibreMatrix_transpose_mul hk hkL hLn v hunit hv x]
    simp only [Matrix.trace_one, Fintype.card_fin]

theorem sign_mul_eq_difference_indicator (b c : Bool) :
    sign b * sign c =
      1 - 2 * (if b ≠ c then (1 : ℝ) else 0) := by
  cases b <;> cases c <;> norm_num [sign]

theorem sum_sign_mul_eq_hammingDist
    (x y : BinaryWord n) :
    (∑ a : Fin n, sign (x a) * sign (y a)) =
      (n : ℝ) - 2 * (MetricCodes.hammingDist x y : ℝ) := by
  classical
  calc
    (∑ a : Fin n, sign (x a) * sign (y a)) =
        ∑ a : Fin n,
          (1 - 2 * (if x a ≠ y a then (1 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact sign_mul_eq_difference_indicator (x a) (y a)
    _ = (n : ℝ) - 2 * (MetricCodes.hammingDist x y : ℝ) := by
      have hcount :
          (∑ a : Fin n,
            if x a ≠ y a then (1 : ℝ) else 0) =
              (MetricCodes.hammingDist x y : ℝ) := by
        simpa only [MetricCodes.hammingDist] using
          (Finset.sum_boole (R := ℝ)
            (fun a : Fin n => x a ≠ y a)
            (Finset.univ : Finset (Fin n)))
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hcount]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

private def hammingAxis (x : BinaryWord n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2
    (fun a : Fin n => (Real.sqrt (n : ℝ))⁻¹ * sign (x a))

theorem hammingAxis_inner {n : ℕ} (hn : 0 < n)
    (x y : BinaryWord n) :
    @inner ℝ (EuclideanSpace ℝ (Fin n)) _
      (hammingAxis x) (hammingAxis y) =
        MetricCodes.hammingCorrelation x y := by
  classical
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hs :
      Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
    Real.mul_self_sqrt hn'.le
  have hsne : Real.sqrt (n : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr hn').ne'
  calc
    @inner ℝ (EuclideanSpace ℝ (Fin n)) _
        (hammingAxis x) (hammingAxis y) =
      ∑ a : Fin n,
        ((Real.sqrt (n : ℝ))⁻¹ * sign (x a)) *
          ((Real.sqrt (n : ℝ))⁻¹ * sign (y a)) := by
        rw [PiLp.inner_apply]
        apply Finset.sum_congr rfl
        intro a _
        simp only [hammingAxis, RCLike.inner_apply, Real.ringHom_apply, mul_comm]
    _ = ((Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt (n : ℝ))⁻¹) *
        (∑ a : Fin n, sign (x a) * sign (y a)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
    _ = ((Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt (n : ℝ))⁻¹) *
        ((n : ℝ) - 2 * (MetricCodes.hammingDist x y : ℝ)) := by
        rw [sum_sign_mul_eq_hammingDist]
    _ = MetricCodes.hammingCorrelation x y := by
        unfold MetricCodes.hammingCorrelation
        field_simp [hsne, hn'.ne'] ; nlinarith [hs]

theorem character_insert
    (x : BinaryWord n) (a : Fin n) (S : Finset (Fin n))
    (ha : a ∉ S) :
    character x (insert a S) = sign (x a) * character x S := by
  classical
  simp only [character, ha, not_false_eq_true, Finset.prod_insert]

theorem character_erase
    (x : BinaryWord n) (a : Fin n) (S : Finset (Fin n))
    (ha : a ∈ S) :
    character x S = sign (x a) * character x (S.erase a) := by
  have h := character_insert x a (S.erase a)
    (by simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true])
  simpa only [Finset.insert_erase ha] using h

theorem lowerAt_twist
    (x : BinaryWord n) (a : Fin n) (f : Function n) :
    lowerAt a (twist x f) =
      sign (x a) • twist x (lowerAt a f) := by
  classical
  funext S
  by_cases ha : a ∈ S
  · simp only [lowerAt, ha, ↓reduceIte, Pi.smul_apply, twist, mul_zero, smul_eq_mul]
  · simp only [lowerAt, ha, ↓reduceIte, twist, character_insert x a S ha, mul_assoc, Pi.smul_apply,
      smul_eq_mul]

theorem raiseAt_twist
    (x : BinaryWord n) (a : Fin n) (f : Function n) :
    raiseAt a (twist x f) =
      sign (x a) • twist x (raiseAt a f) := by
  classical
  funext S
  by_cases ha : a ∈ S
  · simp only [raiseAt, ha, ite_true, twist,
      Pi.smul_apply, smul_eq_mul]
    rw [character_erase x a S ha]
    calc
      character x (S.erase a) * f (S.erase a) =
          (sign (x a) * sign (x a)) *
            (character x (S.erase a) * f (S.erase a)) := by
        rw [sign_mul_self, one_mul]
      _ = sign (x a) *
          ((sign (x a) * character x (S.erase a)) *
            f (S.erase a)) := by
        ring
  · simp only [raiseAt, ha, ↓reduceIte, Pi.smul_apply, twist, mul_zero, smul_eq_mul]

private def matrixHilbertSchmidtFeature
    {ι ρ : Type*}
    (A : Matrix ι ρ ℝ) : EuclideanSpace ℝ (ι × ρ) :=
  WithLp.toLp 2 (fun p : ι × ρ => A p.1 p.2)

theorem matrixHilbertSchmidtFeature_inner
    {ι ρ : Type*} [Fintype ι] [Fintype ρ]
    (A B : Matrix ι ρ ℝ) :
    @inner ℝ (EuclideanSpace ℝ (ι × ρ)) _
      (matrixHilbertSchmidtFeature A)
      (matrixHilbertSchmidtFeature B) =
        Matrix.trace (Aᵀ * B) := by
  classical
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  simp only [matrixHilbertSchmidtFeature, Real.inner_apply,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]

@[simp] theorem matrixHilbertSchmidtFeature_sub
    {ι ρ : Type*}
    (A B : Matrix ι ρ ℝ) :
    matrixHilbertSchmidtFeature (A - B) =
      matrixHilbertSchmidtFeature A -
        matrixHilbertSchmidtFeature B := by
  apply PiLp.ext
  intro p
  rfl

@[simp] theorem matrixHilbertSchmidtFeature_smul
    {ι ρ : Type*}
    (c : ℝ) (A : Matrix ι ρ ℝ) :
    matrixHilbertSchmidtFeature (c • A) =
      c • matrixHilbertSchmidtFeature A := by
  apply PiLp.ext
  intro p
  rfl

/-- The matrix axis lift used in the binary-code argument. -/
def matrixAxisLift {κ ι ρ : Type*}
    (z : κ → ℝ) (A : Matrix ι ρ ℝ) :
    Matrix (κ × ι) ρ ℝ :=
  fun p j => z p.1 * A p.2 j

theorem matrixAxisLift_transpose_mul
    {κ ι ρ : Type*} [Fintype κ] [Fintype ι]
    (z w : κ → ℝ) (A B : Matrix ι ρ ℝ) :
    (matrixAxisLift z A)ᵀ * matrixAxisLift w B =
      (∑ a : κ, z a * w a) • (Aᵀ * B) := by
  classical
  ext i j
  change
    (∑ p : κ × ι,
      (z p.1 * A p.2 i) * (w p.1 * B p.2 j)) =
      (∑ a : κ, z a * w a) *
        (∑ r : ι, A r i * B r j)
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

private def matrixAxisResidual
    {X κ : Type*} {D d : ℕ}
    (P : MetricCodes.ProjectionFamily X D d)
    (axis : X → κ → ℝ)
    (B : Matrix (κ × Fin D) (Fin D) ℝ)
    (c : ℝ) (x : X) :
    Matrix (κ × Fin D) (Fin D) ℝ :=
  matrixAxisLift (axis x) (P.projection x) -
    c • (B * P.projection x)

/-- The matrix axis gram feature used in the binary-code argument. -/
def matrixAxisGramFeature
    {X κ : Type*} {D d : ℕ}
    (P : MetricCodes.ProjectionFamily X D d)
    (axis : X → κ → ℝ)
    (B : Matrix (κ × Fin D) (Fin D) ℝ)
    (c : ℝ) (x : X) :
    EuclideanSpace ℝ ((κ × Fin D) × Fin D) :=
  matrixHilbertSchmidtFeature (matrixAxisResidual P axis B c x)

theorem matrixAxisResidual_gram
    {X κ : Type*} [Fintype κ] {D d : ℕ}
    (P : MetricCodes.ProjectionFamily X D d)
    (axis : X → κ → ℝ)
    (B : Matrix (κ × Fin D) (Fin D) ℝ)
    (c lam : ℝ)
    (hB : Bᵀ * B = 1)
    (haxis : ∀ x : X,
      Bᵀ * matrixAxisLift (axis x) (P.projection x) =
        c • P.projection x)
    (hsq : c ^ 2 = lam)
    (x y : X) :
    @inner ℝ (EuclideanSpace ℝ ((κ × Fin D) × Fin D)) _
      (matrixAxisGramFeature P axis B c x)
      (matrixAxisGramFeature P axis B c y) =
        ((∑ a : κ, axis x a * axis y a) - lam) *
          P.overlap x y := by
  classical
  let Lx : Matrix (κ × Fin D) (Fin D) ℝ :=
    matrixAxisLift (axis x) (P.projection x)
  let Ly : Matrix (κ × Fin D) (Fin D) ℝ :=
    matrixAxisLift (axis y) (P.projection y)
  let Gx : Matrix (κ × Fin D) (Fin D) ℝ :=
    B * P.projection x
  let Gy : Matrix (κ × Fin D) (Fin D) ℝ :=
    B * P.projection y
  have haxisx : Bᵀ * Lx = c • P.projection x := by
    simpa only [Lx] using haxis x
  have haxisy : Bᵀ * Ly = c • P.projection y := by
    simpa only [Ly] using haxis y
  have hleft : Lxᵀ * B = c • P.projection x := by
    calc
      Lxᵀ * B = (Bᵀ * Lx)ᵀ := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
      _ = (c • P.projection x)ᵀ := by rw [haxisx]
      _ = c • P.projection x := by
        rw [Matrix.transpose_smul, P.symmetric x]
  have hLL :
      @inner ℝ (EuclideanSpace ℝ ((κ × Fin D) × Fin D)) _
        (matrixHilbertSchmidtFeature Lx)
        (matrixHilbertSchmidtFeature Ly) =
          (∑ a : κ, axis x a * axis y a) * P.overlap x y := by
    dsimp [Lx, Ly]
    rw [matrixHilbertSchmidtFeature_inner,
      matrixAxisLift_transpose_mul, P.symmetric x,
      Matrix.trace_smul]
    simp only [smul_eq_mul, ProjectionFamily.overlap]
  have hLG :
      @inner ℝ (EuclideanSpace ℝ ((κ × Fin D) × Fin D)) _
        (matrixHilbertSchmidtFeature Lx)
        (matrixHilbertSchmidtFeature Gy) =
          c * P.overlap x y := by
    rw [matrixHilbertSchmidtFeature_inner]
    dsimp [Gy]
    rw [← Matrix.mul_assoc, hleft]
    simp only [Algebra.smul_mul_assoc, Matrix.trace_smul, smul_eq_mul, ProjectionFamily.overlap]
  have hGL :
      @inner ℝ (EuclideanSpace ℝ ((κ × Fin D) × Fin D)) _
        (matrixHilbertSchmidtFeature Gx)
        (matrixHilbertSchmidtFeature Ly) =
          c * P.overlap x y := by
    rw [matrixHilbertSchmidtFeature_inner]
    dsimp [Gx]
    rw [Matrix.transpose_mul, P.symmetric x,
      Matrix.mul_assoc, haxisy]
    simp only [Algebra.mul_smul_comm, Matrix.trace_smul, smul_eq_mul, ProjectionFamily.overlap]
  have hGG :
      @inner ℝ (EuclideanSpace ℝ ((κ × Fin D) × Fin D)) _
        (matrixHilbertSchmidtFeature Gx)
        (matrixHilbertSchmidtFeature Gy) =
          P.overlap x y := by
    rw [matrixHilbertSchmidtFeature_inner]
    dsimp [Gx, Gy]
    rw [Matrix.transpose_mul, P.symmetric x]
    change
      Matrix.trace
        ((P.projection x * Bᵀ) * (B * P.projection y)) =
          P.overlap x y
    calc
      Matrix.trace
          ((P.projection x * Bᵀ) * (B * P.projection y)) =
        Matrix.trace
          (P.projection x * ((Bᵀ * B) * P.projection y)) := by
            congr 1
            simp only [Matrix.mul_assoc]
      _ = P.overlap x y := by
        rw [hB, Matrix.one_mul]
        rfl
  change
    @inner ℝ (EuclideanSpace ℝ ((κ × Fin D) × Fin D)) _
      (matrixHilbertSchmidtFeature (Lx - c • Gx))
      (matrixHilbertSchmidtFeature (Ly - c • Gy)) =
        ((∑ a : κ, axis x a * axis y a) - lam) *
          P.overlap x y
  simp only [matrixHilbertSchmidtFeature_sub,
    matrixHilbertSchmidtFeature_smul,
    inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right,
    hLL, hLG, hGL, hGG]
  rw [← hsq]
  ring

@[simp] theorem harmonicNormFactor_succ (n k r : ℕ) :
    harmonicNormFactor n k (r + 1) =
      harmonicNormFactor n k r * harmonicCoefficient n k (r + 1) := by
  simp only [harmonicNormFactor, Finset.prod_range_succ]

theorem raise_harmonicEmbedding {k : ℕ}
    (f : Function n) (r : ℕ)
    (hbound : 2 * k + (r + 1) ≤ n) :
    raise (harmonicEmbedding k r f) =
      Real.sqrt (harmonicCoefficient n k (r + 1)) •
        harmonicEmbedding k (r + 1) f := by
  have hfactor : 0 < harmonicNormFactor n k r :=
    harmonicNormFactor_pos (by omega)
  have hcoefficient : 0 < harmonicCoefficient n k (r + 1) :=
    harmonicCoefficient_pos (by omega) hbound
  have hfactorne : Real.sqrt (harmonicNormFactor n k r) ≠ 0 :=
    (Real.sqrt_pos.mpr hfactor).ne'
  have hcoefficientne :
      Real.sqrt (harmonicCoefficient n k (r + 1)) ≠ 0 :=
    (Real.sqrt_pos.mpr hcoefficient).ne'
  unfold harmonicEmbedding
  rw [raise_smul, ← raised_succ, smul_smul,
    harmonicNormFactor_succ, Real.sqrt_mul hfactor.le]
  congr 1
  field_simp [hfactorne, hcoefficientne]

theorem lower_harmonicEmbedding {k : ℕ}
    (f : Function n) (hf : IsHarmonic k f) (r : ℕ)
    (hbound : 2 * k + (r + 1) ≤ n) :
    lower (harmonicEmbedding k (r + 1) f) =
      Real.sqrt (harmonicCoefficient n k (r + 1)) •
        harmonicEmbedding k r f := by
  have hfactor : 0 < harmonicNormFactor n k r :=
    harmonicNormFactor_pos (by omega)
  have hcoefficient : 0 < harmonicCoefficient n k (r + 1) :=
    harmonicCoefficient_pos (by omega) hbound
  have hfactorne : Real.sqrt (harmonicNormFactor n k r) ≠ 0 :=
    (Real.sqrt_pos.mpr hfactor).ne'
  have hcoefficientne :
      Real.sqrt (harmonicCoefficient n k (r + 1)) ≠ 0 :=
    (Real.sqrt_pos.mpr hcoefficient).ne'
  unfold harmonicEmbedding
  rw [lower_smul, lower_raised_succ_of_harmonic f hf r,
    smul_smul, smul_smul, harmonicNormFactor_succ,
    Real.sqrt_mul hfactor.le]
  congr 1
  field_simp [hfactorne, hcoefficientne] ;
    nlinarith [Real.sq_sqrt hcoefficient.le]

private def hammingSourceChannelCoefficient
    (n k L : ℕ)
    (m i : Fin (L - k + 1)) : ℝ :=
  MetricCodes.hammingJacobiMatrix n k L m i *
    Real.sqrt (n.choose (k + m.val) : ℝ) /
      Real.sqrt (n.choose (k + i.val) : ℝ)

theorem hammingSourceChannelCoefficient_mul_sqrt_choose
    {n k L : ℕ} (hkL : k ≤ L) (hLn : L + k ≤ n)
    (m i : Fin (L - k + 1)) :
    hammingSourceChannelCoefficient n k L m i *
        Real.sqrt (n.choose (k + i.val) : ℝ) =
      MetricCodes.hammingJacobiMatrix n k L m i *
        Real.sqrt (n.choose (k + m.val) : ℝ) := by
  have hi := i.isLt
  have hlevel : k + i.val ≤ n := by omega
  have hchoose : 0 < (n.choose (k + i.val) : ℝ) := by
    exact_mod_cast Nat.choose_pos hlevel
  have hsqrt : Real.sqrt (n.choose (k + i.val) : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr hchoose).ne'
  unfold hammingSourceChannelCoefficient
  field_simp [hsqrt]

theorem hammingSourceChannelCoefficient_nonneg
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (m i : Fin (L - k + 1)) :
    0 ≤ hammingSourceChannelCoefficient n k L m i := by
  have hm := m.isLt
  have hi := i.isLt
  have hentry : 0 ≤ MetricCodes.hammingJacobiMatrix n k L m i := by
    unfold MetricCodes.hammingJacobiMatrix
    split_ifs with hforward hbackward
    · exact (MetricCodes.hammingJacobiEntry_pos hn
        (by omega) (by omega)).le
    · exact (MetricCodes.hammingJacobiEntry_pos hn
        (by omega) (by omega)).le
    · exact le_rfl
  unfold hammingSourceChannelCoefficient
  exact div_nonneg
    (mul_nonneg hentry (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

theorem hammingRecurrenceWeight_eigenrecurrence
    {n k L : ℕ} (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1))) (lam : ℝ)
    (heigen :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        lam • v)
    (m : Fin (L - k + 1)) :
    (∑ i : Fin (L - k + 1),
      hammingSourceChannelCoefficient n k L m i *
        hammingRecurrenceWeight n k L v i) =
      lam * hammingRecurrenceWeight n k L v m := by
  classical
  have hcoordinate := congrArg
    (fun z : EuclideanSpace ℝ (Fin (L - k + 1)) => z m)
      heigen
  change
    (∑ i : Fin (L - k + 1),
      MetricCodes.hammingJacobiMatrix n k L m i * v i) =
      lam * v m at hcoordinate
  calc
    (∑ i : Fin (L - k + 1),
      hammingSourceChannelCoefficient n k L m i *
        hammingRecurrenceWeight n k L v i) =
      ∑ i : Fin (L - k + 1),
        (MetricCodes.hammingJacobiMatrix n k L m i * v i) *
          Real.sqrt (n.choose (k + m.val) : ℝ) := by
            apply Finset.sum_congr rfl
            intro i _
            unfold hammingRecurrenceWeight
            have h := hammingSourceChannelCoefficient_mul_sqrt_choose
              hkL hLn m i
            calc
              hammingSourceChannelCoefficient n k L m i *
                  (Real.sqrt (n.choose (k + i.val) : ℝ) * v i) =
                (hammingSourceChannelCoefficient n k L m i *
                  Real.sqrt (n.choose (k + i.val) : ℝ)) * v i := by
                    ring
              _ = (MetricCodes.hammingJacobiMatrix n k L m i *
                    Real.sqrt (n.choose (k + m.val) : ℝ)) * v i := by
                      rw [h]
              _ = (MetricCodes.hammingJacobiMatrix n k L m i * v i) *
                    Real.sqrt (n.choose (k + m.val) : ℝ) := by
                      ring
    _ = (∑ i : Fin (L - k + 1),
          MetricCodes.hammingJacobiMatrix n k L m i * v i) *
        Real.sqrt (n.choose (k + m.val) : ℝ) := by
          rw [Finset.sum_mul]
    _ = lam * hammingRecurrenceWeight n k L v m := by
          rw [hcoordinate]
          unfold hammingRecurrenceWeight
          ring

theorem hammingRecurrenceWeight_pos_of_pos
    {n k L : ℕ} (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (i : Fin (L - k + 1)) :
    0 < hammingRecurrenceWeight n k L v i := by
  have hi := i.isLt
  unfold hammingRecurrenceWeight
  apply mul_pos
  · apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.choose_pos (show k + i.val ≤ n by omega)
  · exact hv i

theorem hammingFibreAmplitude_pos_of_pos
    {n k L : ℕ} (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (i : Fin (L - k + 1)) :
    0 < hammingFibreAmplitude n k L v i := by
  unfold hammingFibreAmplitude
  apply Real.sqrt_pos.mpr
  exact div_pos
    (hammingRecurrenceWeight_pos_of_pos hkL hLn v hv i)
    (hammingRecurrenceNormalization_pos hkL hLn v hunit
      (fun j => (hv j).le))

private def hammingAdjacentBlockCoefficient
    (n k L : ℕ)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (lam : ℝ)
    (target source : Fin (L - k + 1)) : ℝ :=
  Real.sqrt
    (hammingSourceChannelCoefficient n k L source target *
      hammingRecurrenceWeight n k L v target /
        (lam * hammingRecurrenceWeight n k L v source))

theorem hammingAdjacentBlockCoefficient_sq
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (target source : Fin (L - k + 1)) :
    hammingAdjacentBlockCoefficient n k L v lam target source ^ 2 =
      hammingSourceChannelCoefficient n k L source target *
        hammingRecurrenceWeight n k L v target /
          (lam * hammingRecurrenceWeight n k L v source) := by
  unfold hammingAdjacentBlockCoefficient
  apply Real.sq_sqrt
  exact div_nonneg
    (mul_nonneg
      (hammingSourceChannelCoefficient_nonneg hn hkL hLn
        source target)
      (hammingRecurrenceWeight_pos_of_pos hkL hLn v hv target).le)
    (mul_pos hlam
      (hammingRecurrenceWeight_pos_of_pos hkL hLn v hv source)).le

theorem hammingAdjacentBlockCoefficient_sq_sum
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        lam • v)
    (source : Fin (L - k + 1)) :
    (∑ target : Fin (L - k + 1),
      hammingAdjacentBlockCoefficient n k L v lam target source ^ 2) =
      1 := by
  classical
  simp_rw [hammingAdjacentBlockCoefficient_sq
    hn hkL hLn v hv lam hlam]
  rw [← Finset.sum_div,
    hammingRecurrenceWeight_eigenrecurrence
      hkL hLn v lam heigen source]
  exact div_self
    (mul_pos hlam
      (hammingRecurrenceWeight_pos_of_pos hkL hLn v hv source)).ne'

theorem hammingAdjacentBlockCoefficient_amplitude_identity
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (target source : Fin (L - k + 1)) :
    hammingAdjacentBlockCoefficient n k L v lam target source *
        hammingFibreAmplitude n k L v target *
        Real.sqrt
          (hammingSourceChannelCoefficient n k L source target) =
      hammingAdjacentBlockCoefficient n k L v lam target source ^ 2 *
        Real.sqrt lam * hammingFibreAmplitude n k L v source := by
  have hcoefficient :=
    hammingSourceChannelCoefficient_nonneg hn hkL hLn source target
  have hsource :=
    hammingRecurrenceWeight_pos_of_pos hkL hLn v hv source
  have hnormal := hammingRecurrenceNormalization_pos
    hkL hLn v hunit (fun i => (hv i).le)
  have hleft :
      0 ≤ hammingAdjacentBlockCoefficient n k L v lam target source *
        hammingFibreAmplitude n k L v target *
        Real.sqrt
          (hammingSourceChannelCoefficient n k L source target) := by
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _)
        (hammingFibreAmplitude_pos_of_pos
          hkL hLn v hunit hv target).le)
      (Real.sqrt_nonneg _)
  have hright :
      0 ≤ hammingAdjacentBlockCoefficient n k L v lam target source ^ 2 *
        Real.sqrt lam * hammingFibreAmplitude n k L v source := by
    exact mul_nonneg
      (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))
      (hammingFibreAmplitude_pos_of_pos
        hkL hLn v hunit hv source).le
  have hsquare :
      (hammingAdjacentBlockCoefficient n k L v lam target source *
        hammingFibreAmplitude n k L v target *
        Real.sqrt
          (hammingSourceChannelCoefficient n k L source target)) ^ 2 =
      (hammingAdjacentBlockCoefficient n k L v lam target source ^ 2 *
        Real.sqrt lam * hammingFibreAmplitude n k L v source) ^ 2 := by
    simp only [mul_pow]
    rw [hammingAdjacentBlockCoefficient_sq
      hn hkL hLn v hv lam hlam target source,
      hammingFibreAmplitude_sq
        hkL hLn v hunit (fun i => (hv i).le) target,
      Real.sq_sqrt hcoefficient,
      Real.sq_sqrt hlam.le,
      hammingFibreAmplitude_sq
        hkL hLn v hunit (fun i => (hv i).le) source]
    field_simp [hlam.ne', hsource.ne', hnormal.ne']
  nlinarith

theorem hammingAdjacentBlockCoefficient_amplitude_sum
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        lam • v)
    (source : Fin (L - k + 1)) :
    (∑ target : Fin (L - k + 1),
      hammingAdjacentBlockCoefficient n k L v lam target source *
        hammingFibreAmplitude n k L v target *
        Real.sqrt
          (hammingSourceChannelCoefficient n k L source target)) =
      Real.sqrt lam * hammingFibreAmplitude n k L v source := by
  simp_rw [hammingAdjacentBlockCoefficient_amplitude_identity
    hn hkL hLn v hunit hv lam hlam]
  rw [← Finset.sum_mul, ← Finset.sum_mul,
    hammingAdjacentBlockCoefficient_sq_sum
      hn hkL hLn v hv lam hlam heigen source]
  simp only [one_mul]

theorem IsLevel.smul {i : ℕ} {f : Function n}
    (hf : IsLevel i f) (c : ℝ) : IsLevel i (c • f) := by
  intro S hS
  change c * f S = 0
  rw [hf S hS, mul_zero]

theorem IsLevel.lowerAt {i : ℕ} {f : Function n}
    (hf : IsLevel (i + 1) f) (a : Fin n) :
    IsLevel i (MetricCodes.Boolean.lowerAt a f) := by
  classical
  intro S hS
  by_cases ha : a ∈ S
  · change (if a ∈ S then 0 else f (insert a S)) = 0
    rw [ite_eq_left ha]
  · have hinsert : (insert a S).card ≠ i + 1 := by
      intro hcard
      apply hS
      have hinsertcard := Finset.card_insert_of_notMem ha
      omega
    change (if a ∈ S then 0 else f (insert a S)) = 0
    rw [ite_eq_right ha, hf (insert a S) hinsert]

theorem IsLevel.raiseAt {i : ℕ} {f : Function n}
    (hf : IsLevel i f) (a : Fin n) :
    IsLevel (i + 1) (MetricCodes.Boolean.raiseAt a f) := by
  classical
  intro S hS
  by_cases ha : a ∈ S
  · have herase : (S.erase a).card ≠ i := by
      intro hcard
      apply hS
      have herasecard := Finset.card_erase_add_one ha
      omega
    change (if a ∈ S then f (S.erase a) else 0) = 0
    rw [ite_eq_left ha, hf (S.erase a) herase]
  · change (if a ∈ S then f (S.erase a) else 0) = 0
    rw [ite_eq_right ha]

private def hammingWindowBasis (n k L : ℕ)
    (T : HammingWindowIndex n k L) : Function n :=
  fun S => if S = T.2.val then 1 else 0

theorem isLevel_hammingWindowBasis (n k L : ℕ)
    (T : HammingWindowIndex n k L) :
    IsLevel (k + T.1.val) (hammingWindowBasis n k L T) := by
  classical
  intro S hS
  unfold hammingWindowBasis
  split_ifs with heq
  · subst S
    exact False.elim (hS T.2.property)
  · rfl

theorem dot_hammingWindowBasis (n k L : ℕ)
    (S T : HammingWindowIndex n k L) :
    dot (hammingWindowBasis n k L S)
        (hammingWindowBasis n k L T) =
      if S.2.val = T.2.val then 1 else 0 := by
  classical
  by_cases h : S.2.val = T.2.val
  · unfold dot hammingWindowBasis
    rw [ite_eq_left h, Finset.sum_eq_single S.2.val]
    · rw [ite_eq_left rfl, ite_eq_left h]
      norm_num
    · intro U _ hU
      rw [ite_eq_right hU, zero_mul]
    · simp only [Finset.mem_univ, not_true_eq_false, ↓reduceIte, mul_ite, mul_one, mul_zero,
        ite_eq_right_iff, one_ne_zero, imp_false, IsEmpty.forall_iff]
  · have h' : T.2.val ≠ S.2.val := Ne.symm h
    simp only [dot, hammingWindowBasis, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, h', h]

private def hammingAdjacentChannel (n k L : ℕ)
    (target source : Fin (L - k + 1))
    (f : Function n) : CoordinateFunction n :=
  if target.val + 1 = source.val then
    deleteChannel (k + source.val) f
  else if source.val + 1 = target.val then
    addChannel (k + source.val) f
  else
    0

theorem coordinateDot_comm (f g : CoordinateFunction n) :
    coordinateDot f g = coordinateDot g f := by
  classical
  unfold coordinateDot
  apply Finset.sum_congr rfl
  intro a _
  exact dot_comm (f a) (g a)

theorem hammingAdjacentChannel_isometry
    {n k L : ℕ} (hkL : k ≤ L) (hLn : L + k ≤ n)
    (target source : Fin (L - k + 1))
    (hadjacent : target.val + 1 = source.val ∨
      source.val + 1 = target.val)
    (f g : Function n) (hf : IsLevel (k + source.val) f) :
    coordinateDot
      (hammingAdjacentChannel n k L target source f)
      (hammingAdjacentChannel n k L target source g) =
      dot f g := by
  have hs := source.isLt
  have ht := target.isLt
  rcases hadjacent with hdelete | hadd
  · simp only [hammingAdjacentChannel, hdelete, ↓reduceIte]
    exact deleteChannel_isometry (by omega) f g hf
  · have hnot : target.val + 1 ≠ source.val := by omega
    simp only [hammingAdjacentChannel, hnot, hadd, ↓reduceIte]
    exact addChannel_isometry (by omega) f g hf

theorem hammingAdjacentChannel_orthogonal
    (n k L : ℕ)
    (target source other : Fin (L - k + 1))
    (hne : source ≠ other)
    (f g : Function n) :
    coordinateDot
      (hammingAdjacentChannel n k L target source f)
      (hammingAdjacentChannel n k L target other g) = 0 := by
  classical
  have hvalne : source.val ≠ other.val := by
    intro h
    exact hne (Fin.ext h)
  have hvalne' : other.val ≠ source.val := Ne.symm hvalne
  by_cases hsourceDelete : target.val + 1 = source.val
  · by_cases hotherDelete : target.val + 1 = other.val
    · exfalso
      apply hne
      apply Fin.ext
      omega
    · by_cases hotherAdd : other.val + 1 = target.val
      · simpa only [hammingAdjacentChannel, hsourceDelete, ↓reduceIte, hvalne, hotherAdd] using
          (deleteChannel_orthogonal_addChannel (k + source.val) (k + other.val) f g)
      · simp only [coordinateDot, dot, hammingAdjacentChannel, hsourceDelete, ↓reduceIte, hvalne,
          hotherAdd, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  · by_cases hsourceAdd : source.val + 1 = target.val
    · by_cases hotherDelete : target.val + 1 = other.val
      · calc
          coordinateDot
              (hammingAdjacentChannel n k L target source f)
              (hammingAdjacentChannel n k L target other g) =
            coordinateDot
              (hammingAdjacentChannel n k L target other g)
              (hammingAdjacentChannel n k L target source f) :=
                coordinateDot_comm _ _
          _ = 0 := by
            simpa only [hammingAdjacentChannel, hotherDelete, ↓reduceIte, hvalne', hsourceAdd] using
              (deleteChannel_orthogonal_addChannel (k + other.val) (k + source.val) g f)
      · by_cases hotherAdd : other.val + 1 = target.val
        · exfalso
          apply hne
          apply Fin.ext
          omega
        · simp only [coordinateDot, dot, hammingAdjacentChannel, hsourceDelete, ↓reduceIte,
            hsourceAdd, hotherDelete, hotherAdd, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    · simp only [coordinateDot, dot, hammingAdjacentChannel, hsourceDelete, ↓reduceIte, hsourceAdd,
        Pi.zero_apply, zero_mul, Finset.sum_const_zero]

theorem hammingAdjacentChannel_isLevel
    (n k L : ℕ)
    (target source : Fin (L - k + 1))
    (f : Function n)
    (hf : IsLevel (k + source.val) f)
    (a : Fin n) :
    IsLevel (k + target.val)
      (hammingAdjacentChannel n k L target source f a) := by
  classical
  by_cases hdelete : target.val + 1 = source.val
  · have hsource :
        IsLevel ((k + target.val) + 1) f := by
      convert hf using 1 ; omega
    simpa only [hammingAdjacentChannel, hdelete, ↓reduceIte, deleteChannel, Nat.cast_add] using
      (hsource.lowerAt a).smul (Real.sqrt (k + source.val : ℝ))⁻¹
  · by_cases hadd : source.val + 1 = target.val
    · have hsource := (hf.raiseAt a).smul
        (Real.sqrt ((n : ℝ) - (k + source.val : ℝ)))⁻¹
      have htarget : k + source.val + 1 = k + target.val := by
        omega
      simpa only [hammingAdjacentChannel, hdelete, ↓reduceIte, hadd, addChannel, Nat.cast_add,
        htarget] using
        hsource
    · intro S hS
      simp only [hammingAdjacentChannel, hdelete, ↓reduceIte, hadd, Pi.zero_apply]

theorem hammingAdjacentChannel_restricted_coordinateDot
    (n k L : ℕ)
    (target source other : Fin (L - k + 1))
    (f g : Function n)
    (hf : IsLevel (k + source.val) f)
    (hg : IsLevel (k + other.val) g) :
    (∑ a : Fin n,
      ∑ S : Level n (k + target.val),
        hammingAdjacentChannel n k L target source f a S.val *
          hammingAdjacentChannel n k L target other g a S.val) =
      coordinateDot
        (hammingAdjacentChannel n k L target source f)
        (hammingAdjacentChannel n k L target other g) := by
  classical
  unfold coordinateDot
  apply Finset.sum_congr rfl
  intro a _
  simpa only [layerDot, layerRestrict] using
    (dot_eq_layerDot_of_level (hammingAdjacentChannel n k L target source f a)
        (hammingAdjacentChannel n k L target other g a) (hammingAdjacentChannel_isLevel n k L
          target source f hf a)
        (hammingAdjacentChannel_isLevel n k L target other g hg a)).symm

theorem hammingSourceChannelCoefficient_eq_zero_of_not_adjacent
    (n k L : ℕ)
    (source target : Fin (L - k + 1))
    (hnot : ¬ (target.val + 1 = source.val ∨
      source.val + 1 = target.val)) :
    hammingSourceChannelCoefficient n k L source target = 0 := by
  have hforward : source.val + 1 ≠ target.val := by
    intro h
    exact hnot (Or.inr h)
  have hbackward : target.val + 1 ≠ source.val := by
    intro h
    exact hnot (Or.inl h)
  simp only [hammingSourceChannelCoefficient, hammingJacobiMatrix, hforward, ↓reduceIte, hbackward,
    zero_mul, zero_div]

private def hammingWindowChannelMatrix
    (n k L : ℕ)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (lam : ℝ) :
    Matrix (Fin n × HammingWindowIndex n k L)
      (HammingWindowIndex n k L) ℝ :=
  fun p Q =>
    hammingAdjacentBlockCoefficient n k L v lam p.2.1 Q.1 *
      hammingAdjacentChannel n k L p.2.1 Q.1
        (hammingWindowBasis n k L Q) p.1 p.2.2.val

theorem hammingWindowChannelMatrix_pairing
    (n k L : ℕ)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (lam : ℝ)
    (Q R : HammingWindowIndex n k L) :
    (∑ p : Fin n × HammingWindowIndex n k L,
      hammingWindowChannelMatrix n k L v lam p Q *
        hammingWindowChannelMatrix n k L v lam p R) =
      ∑ target : Fin (L - k + 1),
        (hammingAdjacentBlockCoefficient n k L v lam target Q.1 *
          hammingAdjacentBlockCoefficient n k L v lam target R.1) *
        coordinateDot
          (hammingAdjacentChannel n k L target Q.1
            (hammingWindowBasis n k L Q))
          (hammingAdjacentChannel n k L target R.1
            (hammingWindowBasis n k L R)) := by
  classical
  unfold hammingWindowChannelMatrix
  rw [Fintype.sum_prod_type, Finset.sum_comm, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro target _
  calc
    (∑ S : Level n (k + target.val),
      ∑ a : Fin n,
        (hammingAdjacentBlockCoefficient n k L v lam target Q.1 *
          hammingAdjacentChannel n k L target Q.1
            (hammingWindowBasis n k L Q) a S.val) *
        (hammingAdjacentBlockCoefficient n k L v lam target R.1 *
          hammingAdjacentChannel n k L target R.1
            (hammingWindowBasis n k L R) a S.val)) =
      (hammingAdjacentBlockCoefficient n k L v lam target Q.1 *
        hammingAdjacentBlockCoefficient n k L v lam target R.1) *
        (∑ a : Fin n,
          ∑ S : Level n (k + target.val),
            hammingAdjacentChannel n k L target Q.1
                (hammingWindowBasis n k L Q) a S.val *
              hammingAdjacentChannel n k L target R.1
                (hammingWindowBasis n k L R) a S.val) := by
          rw [Finset.sum_comm, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro S _
          ring
    _ = (hammingAdjacentBlockCoefficient n k L v lam target Q.1 *
        hammingAdjacentBlockCoefficient n k L v lam target R.1) *
        coordinateDot
          (hammingAdjacentChannel n k L target Q.1
            (hammingWindowBasis n k L Q))
          (hammingAdjacentChannel n k L target R.1
            (hammingWindowBasis n k L R)) := by
          rw [hammingAdjacentChannel_restricted_coordinateDot
            n k L target Q.1 R.1
            (hammingWindowBasis n k L Q)
            (hammingWindowBasis n k L R)
            (isLevel_hammingWindowBasis n k L Q)
            (isLevel_hammingWindowBasis n k L R)]

theorem hammingWindowChannelMatrix_transpose_mul
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        lam • v) :
    (hammingWindowChannelMatrix n k L v lam)ᵀ *
      hammingWindowChannelMatrix n k L v lam = 1 := by
  classical
  ext Q R
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
  rw [hammingWindowChannelMatrix_pairing]
  rcases Q with ⟨source, S⟩
  rcases R with ⟨other, T⟩
  by_cases heq : source = other
  · subst other
    calc
      (∑ target : Fin (L - k + 1),
        (hammingAdjacentBlockCoefficient n k L v lam target source *
          hammingAdjacentBlockCoefficient n k L v lam target source) *
        coordinateDot
          (hammingAdjacentChannel n k L target source
            (hammingWindowBasis n k L ⟨source, S⟩))
          (hammingAdjacentChannel n k L target source
            (hammingWindowBasis n k L ⟨source, T⟩))) =
        ∑ target : Fin (L - k + 1),
          hammingAdjacentBlockCoefficient n k L v lam target source ^ 2 *
            dot (hammingWindowBasis n k L ⟨source, S⟩)
              (hammingWindowBasis n k L ⟨source, T⟩) := by
          apply Finset.sum_congr rfl
          intro target _
          by_cases hadjacent : target.val + 1 = source.val ∨
              source.val + 1 = target.val
          · rw [hammingAdjacentChannel_isometry
              hkL hLn target source hadjacent
              (hammingWindowBasis n k L ⟨source, S⟩)
              (hammingWindowBasis n k L ⟨source, T⟩)
              (isLevel_hammingWindowBasis n k L ⟨source, S⟩)]
            ring
          · have hzero :=
              hammingSourceChannelCoefficient_eq_zero_of_not_adjacent
                n k L source target hadjacent
            have hblock :
                hammingAdjacentBlockCoefficient
                  n k L v lam target source = 0 := by
              simp only [hammingAdjacentBlockCoefficient, hzero, zero_mul, zero_div, Real.sqrt_zero]
            simp only [hblock, mul_zero, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
              zero_pow]
      _ = (∑ target : Fin (L - k + 1),
            hammingAdjacentBlockCoefficient n k L v lam target source ^ 2) *
          dot (hammingWindowBasis n k L ⟨source, S⟩)
            (hammingWindowBasis n k L ⟨source, T⟩) := by
          rw [Finset.sum_mul]
      _ = if (⟨source, S⟩ : HammingWindowIndex n k L) =
            (⟨source, T⟩ : HammingWindowIndex n k L)
          then 1 else 0 := by
          rw [hammingAdjacentBlockCoefficient_sq_sum
            hn hkL hLn v hv lam hlam heigen source, one_mul,
            dot_hammingWindowBasis]
          by_cases hST : S = T
          · subst T
            simp only [↓reduceIte]
          · have hval : S.val ≠ T.val := by
              intro h
              exact hST (Subtype.ext h)
            have hsigma :
                (⟨source, S⟩ : HammingWindowIndex n k L) ≠
                  (⟨source, T⟩ : HammingWindowIndex n k L) := by
              intro h
              have hsecond : S.val = T.val :=
                congrArg (fun Z : HammingWindowIndex n k L => Z.2.val) h
              exact hval hsecond
            simp only [hval, ↓reduceIte, hsigma]
  · have hsigma :
        (⟨source, S⟩ : HammingWindowIndex n k L) ≠
          (⟨other, T⟩ : HammingWindowIndex n k L) := by
      intro h
      exact heq
        (congrArg (fun Z : HammingWindowIndex n k L => Z.1) h)
    rw [ite_eq_right hsigma]
    apply Finset.sum_eq_zero
    intro target _
    rw [hammingAdjacentChannel_orthogonal
      n k L target source other heq
      (hammingWindowBasis n k L ⟨source, S⟩)
      (hammingWindowBasis n k L ⟨other, T⟩)]
    ring

private def hammingChannelMatrix
    (n k L : ℕ)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (lam : ℝ) :
    Matrix (Fin n × Fin (hammingWindowDimension n k L))
      (Fin (hammingWindowDimension n k L)) ℝ :=
  fun p q =>
    hammingWindowChannelMatrix n k L v lam
      (p.1, (hammingWindowIndexEquiv n k L).symm p.2)
      ((hammingWindowIndexEquiv n k L).symm q)

theorem hammingChannelMatrix_transpose_mul
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        lam • v) :
    (hammingChannelMatrix n k L v lam)ᵀ *
      hammingChannelMatrix n k L v lam = 1 := by
  classical
  let e := hammingWindowIndexEquiv n k L
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
  change
    (∑ p : Fin n × Fin (hammingWindowDimension n k L),
      hammingWindowChannelMatrix n k L v lam
          (p.1, e.symm p.2) (e.symm i) *
        hammingWindowChannelMatrix n k L v lam
          (p.1, e.symm p.2) (e.symm j)) =
      if i = j then 1 else 0
  have hwindow := congrArg
    (fun M : Matrix (HammingWindowIndex n k L)
        (HammingWindowIndex n k L) ℝ =>
      M (e.symm i) (e.symm j))
    (hammingWindowChannelMatrix_transpose_mul
      hn hkL hLn v hv lam hlam heigen)
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.one_apply] at hwindow
  rw [Fintype.sum_prod_type] at hwindow ⊢
  calc
    (∑ a : Fin n,
      ∑ t : Fin (hammingWindowDimension n k L),
        hammingWindowChannelMatrix n k L v lam
            (a, e.symm t) (e.symm i) *
          hammingWindowChannelMatrix n k L v lam
            (a, e.symm t) (e.symm j)) =
      ∑ a : Fin n,
        ∑ T : HammingWindowIndex n k L,
          hammingWindowChannelMatrix n k L v lam
              (a, T) (e.symm i) *
            hammingWindowChannelMatrix n k L v lam
              (a, T) (e.symm j) := by
          apply Finset.sum_congr rfl
          intro a _
          exact e.symm.sum_comp
            (fun T : HammingWindowIndex n k L =>
              hammingWindowChannelMatrix n k L v lam
                  (a, T) (e.symm i) *
                hammingWindowChannelMatrix n k L v lam
                  (a, T) (e.symm j))
    _ = (if e.symm i = e.symm j then 1 else 0) := hwindow
    _ = (if i = j then 1 else 0) := by
      simp only [EmbeddingLike.apply_eq_iff_eq]

theorem hammingPositiveRadicalSymmetrization
    {d e a b N r : ℝ}
    (hd : 0 < d) (he : 0 < e)
    (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hcross : d * b = e * a) :
    (r / (N * a)) * Real.sqrt d =
      (r / (N * Real.sqrt (a * b))) * Real.sqrt e := by
  have hradical :
      Real.sqrt d * Real.sqrt b =
        Real.sqrt e * Real.sqrt a := by
    calc
      Real.sqrt d * Real.sqrt b = Real.sqrt (d * b) :=
        (Real.sqrt_mul hd.le b).symm
      _ = Real.sqrt (e * a) := by rw [hcross]
      _ = Real.sqrt e * Real.sqrt a :=
        Real.sqrt_mul he.le a
  have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have hsb : Real.sqrt b ≠ 0 := (Real.sqrt_pos.mpr hb).ne'
  calc
    (r / (N * a)) * Real.sqrt d =
        (r * Real.sqrt d) / (N * a) := by ring
    _ = (r * Real.sqrt e) /
          (N * (Real.sqrt a * Real.sqrt b)) := by
      apply (div_eq_div_iff
        (mul_ne_zero hN.ne' ha.ne')
        (mul_ne_zero hN.ne' (mul_ne_zero hsa hsb))).mpr
      calc
        (r * Real.sqrt d) *
            (N * (Real.sqrt a * Real.sqrt b)) =
          r * N * Real.sqrt a *
            (Real.sqrt d * Real.sqrt b) := by ring
        _ = r * N * Real.sqrt a *
            (Real.sqrt e * Real.sqrt a) := by rw [hradical]
        _ = (r * Real.sqrt e) *
            (N * (Real.sqrt a * Real.sqrt a)) := by ring
        _ = (r * Real.sqrt e) * (N * a) := by
          rw [Real.mul_self_sqrt ha.le]
    _ = (r / (N * Real.sqrt (a * b))) * Real.sqrt e := by
      rw [Real.sqrt_mul ha.le]
      ring

private def hammingDeletionChannelSquare (n k i : ℕ) : ℝ :=
  (((i : ℝ) - (k : ℝ) + 1) *
    ((n : ℝ) - (i : ℝ) - (k : ℝ))) /
      ((n : ℝ) * ((i : ℝ) + 1))

private def hammingInsertionChannelSquare (n k i : ℕ) : ℝ :=
  (((i : ℝ) - (k : ℝ) + 1) *
    ((n : ℝ) - (i : ℝ) - (k : ℝ))) /
      ((n : ℝ) * ((n : ℝ) - (i : ℝ)))

theorem hammingDeletionChannelSquare_mul_sqrt_choose
    {n k i : ℕ} (hn : 0 < n)
    (_ : k ≤ i) (hboundary : i + k < n) :
    hammingDeletionChannelSquare n k i *
        Real.sqrt (n.choose i : ℝ) =
      MetricCodes.hammingJacobiEntry n k i *
        Real.sqrt (n.choose (i + 1) : ℝ) := by
  have hi : i < n := by omega
  have hd : 0 < (n.choose i : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_of_lt hi)
  have he : 0 < (n.choose (i + 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show i + 1 ≤ n by omega)
  have ha : 0 < (i : ℝ) + 1 := by positivity
  have hb : 0 < (n : ℝ) - (i : ℝ) := by
    exact sub_pos.mpr (by exact_mod_cast hi)
  have hN : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcross :
      (n.choose i : ℝ) * ((n : ℝ) - (i : ℝ)) =
        (n.choose (i + 1) : ℝ) * ((i : ℝ) + 1) := by
    have h := congrArg (fun z : ℕ => (z : ℝ))
      (Nat.choose_succ_right_eq n i)
    simpa only [Nat.cast_mul, Nat.cast_sub (Nat.le_of_lt hi), Nat.cast_add,
      Nat.cast_one] using h.symm
  unfold hammingDeletionChannelSquare MetricCodes.hammingJacobiEntry
  exact hammingPositiveRadicalSymmetrization
    (r := (((i : ℝ) - (k : ℝ) + 1) *
      ((n : ℝ) - (i : ℝ) - (k : ℝ))))
    hd he ha hb hN hcross

theorem hammingInsertionChannelSquare_mul_sqrt_choose
    {n k i : ℕ} (hn : 0 < n)
    (_ : k ≤ i) (hboundary : i + k < n) :
    hammingInsertionChannelSquare n k i *
        Real.sqrt (n.choose (i + 1) : ℝ) =
      MetricCodes.hammingJacobiEntry n k i *
        Real.sqrt (n.choose i : ℝ) := by
  have hi : i < n := by omega
  have hd : 0 < (n.choose i : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_of_lt hi)
  have he : 0 < (n.choose (i + 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show i + 1 ≤ n by omega)
  have ha : 0 < (i : ℝ) + 1 := by positivity
  have hb : 0 < (n : ℝ) - (i : ℝ) := by
    exact sub_pos.mpr (by exact_mod_cast hi)
  have hN : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcross :
      (n.choose i : ℝ) * ((n : ℝ) - (i : ℝ)) =
        (n.choose (i + 1) : ℝ) * ((i : ℝ) + 1) := by
    have h := congrArg (fun z : ℕ => (z : ℝ))
      (Nat.choose_succ_right_eq n i)
    simpa only [Nat.cast_mul, Nat.cast_sub (Nat.le_of_lt hi), Nat.cast_add,
      Nat.cast_one] using h.symm
  have hradical := hammingPositiveRadicalSymmetrization
    (r := (((i : ℝ) - (k : ℝ) + 1) *
      ((n : ℝ) - (i : ℝ) - (k : ℝ))))
    he hd hb ha hN hcross.symm
  unfold hammingInsertionChannelSquare MetricCodes.hammingJacobiEntry
  convert hradical using 1 ; ring_nf

theorem hammingSourceChannelCoefficient_eq_deletion
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (source target : Fin (L - k + 1))
    (hadjacent : target.val + 1 = source.val) :
    hammingSourceChannelCoefficient n k L source target =
      hammingDeletionChannelSquare n k (k + target.val) := by
  have hs := source.isLt
  have ht := target.isLt
  have hboundary : k + target.val + k < n := by omega
  have hdimension : 0 < (n.choose (k + target.val) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show k + target.val ≤ n by omega)
  have hroot : Real.sqrt (n.choose (k + target.val) : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr hdimension).ne'
  apply mul_right_cancel₀ hroot
  rw [hammingSourceChannelCoefficient_mul_sqrt_choose
    hkL hLn source target]
  have hnot : source.val + 1 ≠ target.val := by omega
  have hdegree : k + source.val = (k + target.val) + 1 := by omega
  simpa only [hammingJacobiMatrix, hnot, ↓reduceIte, hadjacent, hdegree] using
    (hammingDeletionChannelSquare_mul_sqrt_choose hn (show k ≤ k + target.val by omega)
      hboundary).symm

theorem hammingSourceChannelCoefficient_eq_insertion
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (source target : Fin (L - k + 1))
    (hadjacent : source.val + 1 = target.val) :
    hammingSourceChannelCoefficient n k L source target =
      hammingInsertionChannelSquare n k (k + source.val) := by
  have hs := source.isLt
  have ht := target.isLt
  have hboundary : k + source.val + k < n := by omega
  have hdimension : 0 < (n.choose (k + target.val) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show k + target.val ≤ n by omega)
  have hroot : Real.sqrt (n.choose (k + target.val) : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr hdimension).ne'
  apply mul_right_cancel₀ hroot
  rw [hammingSourceChannelCoefficient_mul_sqrt_choose
    hkL hLn source target]
  have hdegree : k + target.val = (k + source.val) + 1 := by omega
  simpa only [hammingJacobiMatrix, hadjacent, ↓reduceIte, hdegree] using
    (hammingInsertionChannelSquare_mul_sqrt_choose hn (show k ≤ k + source.val by omega)
      hboundary).symm

theorem dot_lowerAt_eq_raiseAt (a : Fin n) (f g : Function n) :
    dot (lowerAt a f) g = dot f (raiseAt a g) := by
  calc
    dot (lowerAt a f) g = dot g (lowerAt a f) :=
      dot_comm _ _
    _ = dot (raiseAt a g) f :=
      (dot_raiseAt_eq_lowerAt a g f).symm
    _ = dot f (raiseAt a g) := dot_comm _ _

theorem sum_dot_twist_raiseAt
    (x : BinaryWord n) (f g : Function n) :
    (∑ a : Fin n, dot f (twist x (raiseAt a g))) =
      dot f (twist x (raise g)) := by
  classical
  unfold dot twist raise
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

theorem sum_dot_twist_lowerAt
    (x : BinaryWord n) (f g : Function n) :
    (∑ a : Fin n, dot f (twist x (lowerAt a g))) =
      dot f (twist x (lower g)) := by
  classical
  unfold dot twist lower
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

private def hammingAxisTensor (x : BinaryWord n) (f : Function n) :
    CoordinateFunction n :=
  fun a => hammingAxis x a • f

theorem coordinateDot_deleteChannel_hammingAxisTensor
    (i : ℕ) (x : BinaryWord n) (f g : Function n) :
    coordinateDot (deleteChannel i f)
      (hammingAxisTensor x (twist x g)) =
      ((Real.sqrt (i : ℝ))⁻¹ *
        (Real.sqrt (n : ℝ))⁻¹) *
        dot f (twist x (raise g)) := by
  classical
  unfold coordinateDot deleteChannel hammingAxisTensor
  simp only [dot_smul_left, dot_smul_right,
    hammingAxis, PiLp.toLp_apply]
  simp_rw [dot_lowerAt_eq_raiseAt,
    raiseAt_twist, dot_smul_right]
  calc
    (∑ a : Fin n,
      ((Real.sqrt (n : ℝ))⁻¹ * sign (x a)) *
        ((Real.sqrt (i : ℝ))⁻¹ *
          (sign (x a) * dot f (twist x (raiseAt a g))))) =
      ((Real.sqrt (i : ℝ))⁻¹ *
        (Real.sqrt (n : ℝ))⁻¹) *
        (∑ a : Fin n, dot f (twist x (raiseAt a g))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          calc
            ((Real.sqrt (n : ℝ))⁻¹ * sign (x a)) *
                ((Real.sqrt (i : ℝ))⁻¹ *
                  (sign (x a) * dot f (twist x (raiseAt a g)))) =
              ((Real.sqrt (i : ℝ))⁻¹ *
                (Real.sqrt (n : ℝ))⁻¹) *
                  ((sign (x a) * sign (x a)) *
                    dot f (twist x (raiseAt a g))) := by
                      ring
            _ = ((Real.sqrt (i : ℝ))⁻¹ *
                (Real.sqrt (n : ℝ))⁻¹) *
                  dot f (twist x (raiseAt a g)) := by
                    rw [sign_mul_self, one_mul]
    _ = ((Real.sqrt (i : ℝ))⁻¹ *
        (Real.sqrt (n : ℝ))⁻¹) *
        dot f (twist x (raise g)) := by
          rw [sum_dot_twist_raiseAt]

theorem coordinateDot_addChannel_hammingAxisTensor
    (i : ℕ) (x : BinaryWord n) (f g : Function n) :
    coordinateDot (addChannel i f)
      (hammingAxisTensor x (twist x g)) =
      ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
        (Real.sqrt (n : ℝ))⁻¹) *
        dot f (twist x (lower g)) := by
  classical
  unfold coordinateDot addChannel hammingAxisTensor
  simp only [dot_smul_left, dot_smul_right,
    hammingAxis, PiLp.toLp_apply]
  simp_rw [dot_raiseAt_eq_lowerAt,
    lowerAt_twist, dot_smul_right]
  calc
    (∑ a : Fin n,
      ((Real.sqrt (n : ℝ))⁻¹ * sign (x a)) *
        ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
          (sign (x a) * dot f (twist x (lowerAt a g))))) =
      ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
        (Real.sqrt (n : ℝ))⁻¹) *
        (∑ a : Fin n, dot f (twist x (lowerAt a g))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          calc
            ((Real.sqrt (n : ℝ))⁻¹ * sign (x a)) *
                ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
                  (sign (x a) * dot f (twist x (lowerAt a g)))) =
              ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
                (Real.sqrt (n : ℝ))⁻¹) *
                  ((sign (x a) * sign (x a)) *
                    dot f (twist x (lowerAt a g))) := by
                      ring
            _ = ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
                (Real.sqrt (n : ℝ))⁻¹) *
                  dot f (twist x (lowerAt a g)) := by
                    rw [sign_mul_self, one_mul]
    _ = ((Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ *
        (Real.sqrt (n : ℝ))⁻¹) *
        dot f (twist x (lower g)) := by
          rw [sum_dot_twist_lowerAt]

theorem hammingSqrtDivProduct
    {r a b : ℝ} (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (r / (a * b)) =
      (Real.sqrt a)⁻¹ * (Real.sqrt b)⁻¹ * Real.sqrt r := by
  rw [Real.sqrt_div hr, Real.sqrt_mul ha.le]
  field_simp [(Real.sqrt_pos.mpr ha).ne',
    (Real.sqrt_pos.mpr hb).ne']

theorem hammingSourceChannelCoefficient_sqrt_deletion
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (source target : Fin (L - k + 1))
    (hadjacent : target.val + 1 = source.val) :
    Real.sqrt (hammingSourceChannelCoefficient n k L source target) =
      (Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt (k + source.val : ℝ))⁻¹ *
          Real.sqrt (harmonicCoefficient n k source.val) := by
  have hs := source.isLt
  have hcoefficient : 0 < harmonicCoefficient n k source.val :=
    harmonicCoefficient_pos (by omega) (by omega)
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsreal : 0 < (k + source.val : ℝ) := by
    exact_mod_cast (show 0 < k + source.val by omega)
  have hnum :
      (((k + target.val : ℕ) : ℝ) - (k : ℝ) + 1) *
          ((n : ℝ) - ((k + target.val : ℕ) : ℝ) - (k : ℝ)) =
        harmonicCoefficient n k source.val := by
    have hval : source.val = target.val + 1 := by omega
    rw [hval]
    simp only [harmonicCoefficient, Nat.cast_add, Nat.cast_one]
    ring
  have hden :
      ((k + target.val : ℕ) : ℝ) + 1 =
        ((k + source.val : ℕ) : ℝ) := by
    exact_mod_cast (show k + target.val + 1 = k + source.val by omega)
  rw [hammingSourceChannelCoefficient_eq_deletion
    hn hkL hLn source target hadjacent]
  unfold hammingDeletionChannelSquare
  rw [hnum, hden]
  simpa only [Nat.cast_add] using
    hammingSqrtDivProduct hcoefficient.le hnreal hsreal

theorem hammingSourceChannelCoefficient_sqrt_insertion
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (source target : Fin (L - k + 1))
    (hadjacent : source.val + 1 = target.val) :
    Real.sqrt (hammingSourceChannelCoefficient n k L source target) =
      (Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt ((n : ℝ) - (k + source.val : ℝ)))⁻¹ *
          Real.sqrt (harmonicCoefficient n k target.val) := by
  have hs := source.isLt
  have ht := target.isLt
  have hcoefficient : 0 < harmonicCoefficient n k target.val :=
    harmonicCoefficient_pos (by omega) (by omega)
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsreal : 0 < (n : ℝ) - (k + source.val : ℝ) := by
    have hdegree : k + source.val < n := by omega
    exact sub_pos.mpr (by exact_mod_cast hdegree)
  have hnum :
      (((k + source.val : ℕ) : ℝ) - (k : ℝ) + 1) *
          ((n : ℝ) - ((k + source.val : ℕ) : ℝ) - (k : ℝ)) =
        harmonicCoefficient n k target.val := by
    have hval : target.val = source.val + 1 := by omega
    rw [hval]
    simp only [harmonicCoefficient, Nat.cast_add, Nat.cast_one]
    ring
  rw [hammingSourceChannelCoefficient_eq_insertion
    hn hkL hLn source target hadjacent]
  unfold hammingInsertionChannelSquare
  rw [hnum]
  simpa only [Nat.cast_add] using
    hammingSqrtDivProduct hcoefficient.le hnreal hsreal

theorem hammingAdjacentChannel_axis_inner
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (x : BinaryWord n)
    (target source : Fin (L - k + 1))
    (f h : Function n) (hh : IsHarmonic k h) :
    coordinateDot
      (hammingAdjacentChannel n k L target source f)
      (hammingAxisTensor x (wordHarmonicEmbedding x k target.val h)) =
      Real.sqrt (hammingSourceChannelCoefficient n k L source target) *
        dot f (wordHarmonicEmbedding x k source.val h) := by
  classical
  have hs := source.isLt
  have ht := target.isLt
  by_cases hdelete : target.val + 1 = source.val
  · simp only [hammingAdjacentChannel, hdelete, ↓reduceIte]
    unfold wordHarmonicEmbedding
    rw [coordinateDot_deleteChannel_hammingAxisTensor]
    rw [raise_harmonicEmbedding h target.val (by omega),
      twist_smul, dot_smul_right,
      hammingSourceChannelCoefficient_sqrt_deletion
        hn hkL hLn source target hdelete]
    have hval : target.val + 1 = source.val := hdelete
    rw [hval]
    simp only [Nat.cast_add]
    ring
  · by_cases hadd : source.val + 1 = target.val
    · simp only [hammingAdjacentChannel, hdelete,
        hadd, ↓reduceIte]
      unfold wordHarmonicEmbedding
      rw [coordinateDot_addChannel_hammingAxisTensor]
      have hval : target.val = source.val + 1 := by omega
      rw [hval,
        lower_harmonicEmbedding h hh source.val (by omega),
        twist_smul, dot_smul_right,
        hammingSourceChannelCoefficient_sqrt_insertion
          hn hkL hLn source target hadd]
      rw [hval]
      simp only [Nat.cast_add]
      ring
    · have hzero :=
        hammingSourceChannelCoefficient_eq_zero_of_not_adjacent
          n k L source target (by tauto)
      simp only [coordinateDot, dot, hammingAdjacentChannel, hdelete, ↓reduceIte, hadd,
        Pi.zero_apply, hammingAxisTensor, Pi.smul_apply, smul_eq_mul, zero_mul,
        Finset.sum_const_zero, hzero, Real.sqrt_zero]

theorem dot_hammingWindowBasis_apply
    (n k L : ℕ) (Q : HammingWindowIndex n k L)
    (f : Function n) :
    dot (hammingWindowBasis n k L Q) f = f Q.2.val := by
  classical
  unfold dot hammingWindowBasis
  rw [Finset.sum_eq_single Q.2.val]
  · rw [ite_eq_left rfl, one_mul]
  · intro S _ hS
    rw [ite_eq_right hS, zero_mul]
  · simp only [Finset.mem_univ, not_true_eq_false, ↓reduceIte, one_mul, IsEmpty.forall_iff]

theorem hammingAdjacentChannel_restricted_axisDot
    (n k L : ℕ) (x : BinaryWord n)
    (target source : Fin (L - k + 1))
    (f g : Function n)
    (hf : IsLevel (k + source.val) f)
    (hg : IsLevel (k + target.val) g) :
    (∑ a : Fin n,
      ∑ S : Level n (k + target.val),
        hammingAdjacentChannel n k L target source f a S.val *
          (hammingAxis x a * g S.val)) =
      coordinateDot
        (hammingAdjacentChannel n k L target source f)
        (hammingAxisTensor x g) := by
  classical
  unfold coordinateDot
  apply Finset.sum_congr rfl
  intro a _
  simpa only [hammingAxisTensor, layerDot, layerRestrict, Pi.smul_apply, smul_eq_mul] using
    (dot_eq_layerDot_of_level (hammingAdjacentChannel n k L target source f a)
      (hammingAxisTensor x g a)
        (hammingAdjacentChannel_isLevel n k L target source f hf a) (hg.smul (hammingAxis x
          a))).symm

theorem hammingWindowChannelMatrix_transpose_axis_fibre
    {n k L : ℕ} (hn : 0 < n) (hk : 2 * k ≤ n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        lam • v)
    (x : BinaryWord n) :
    (hammingWindowChannelMatrix n k L v lam)ᵀ *
      matrixAxisLift (fun a : Fin n => hammingAxis x a)
        (hammingWindowFibreMatrix n k L hk v x) =
      Real.sqrt lam • hammingWindowFibreMatrix n k L hk v x := by
  classical
  ext Q p
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.smul_apply, smul_eq_mul]
  change
    (∑ z : Fin n × HammingWindowIndex n k L,
      (hammingAdjacentBlockCoefficient n k L v lam z.2.1 Q.1 *
        hammingAdjacentChannel n k L z.2.1 Q.1
          (hammingWindowBasis n k L Q) z.1 z.2.2.val) *
      (hammingAxis x z.1 *
        (hammingFibreAmplitude n k L v z.2.1 *
          wordHarmonicEmbedding x k z.2.1.val
            (harmonicBasisFunction n k hk p) z.2.2.val))) =
      Real.sqrt lam *
        (hammingFibreAmplitude n k L v Q.1 *
          wordHarmonicEmbedding x k Q.1.val
            (harmonicBasisFunction n k hk p) Q.2.val)
  rw [Fintype.sum_prod_type, Finset.sum_comm, Fintype.sum_sigma]
  let h : Function n := harmonicBasisFunction n k hk p
  have hh : IsHarmonic k h :=
    harmonicBasisFunction_isHarmonic n k hk p
  calc
    (∑ target : Fin (L - k + 1),
      ∑ S : Level n (k + target.val),
      ∑ a : Fin n,
        (hammingAdjacentBlockCoefficient n k L v lam target Q.1 *
          hammingAdjacentChannel n k L target Q.1
            (hammingWindowBasis n k L Q) a S.val) *
        (hammingAxis x a *
          (hammingFibreAmplitude n k L v target *
            wordHarmonicEmbedding x k target.val h S.val))) =
      ∑ target : Fin (L - k + 1),
        (hammingAdjacentBlockCoefficient n k L v lam target Q.1 *
          hammingFibreAmplitude n k L v target) *
        coordinateDot
          (hammingAdjacentChannel n k L target Q.1
            (hammingWindowBasis n k L Q))
          (hammingAxisTensor x
            (wordHarmonicEmbedding x k target.val h)) := by
          apply Finset.sum_congr rfl
          intro target _
          rw [Finset.sum_comm, ←
            hammingAdjacentChannel_restricted_axisDot
              n k L x target Q.1
              (hammingWindowBasis n k L Q)
              (wordHarmonicEmbedding x k target.val h)
              (isLevel_hammingWindowBasis n k L Q)
              (IsLevel.wordHarmonicEmbedding hh.1 x target.val),
            Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro S _
          ring
    _ = (∑ target : Fin (L - k + 1),
          hammingAdjacentBlockCoefficient n k L v lam target Q.1 *
            hammingFibreAmplitude n k L v target *
              Real.sqrt
                (hammingSourceChannelCoefficient n k L Q.1 target)) *
          dot (hammingWindowBasis n k L Q)
            (wordHarmonicEmbedding x k Q.1.val h) := by
          simp_rw [hammingAdjacentChannel_axis_inner
            hn hkL hLn x _ Q.1
            (hammingWindowBasis n k L Q) h hh]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro target _
          ring
    _ = Real.sqrt lam *
          (hammingFibreAmplitude n k L v Q.1 *
            wordHarmonicEmbedding x k Q.1.val h Q.2.val) := by
          rw [hammingAdjacentBlockCoefficient_amplitude_sum
            hn hkL hLn v hunit hv lam hlam heigen Q.1,
            dot_hammingWindowBasis_apply]
          ring

theorem hammingChannelMatrix_transpose_axis_fibre
    {n k L : ℕ} (hn : 0 < n) (hk : 2 * k ≤ n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        lam • v)
    (x : BinaryWord n) :
    (hammingChannelMatrix n k L v lam)ᵀ *
      matrixAxisLift (fun a : Fin n => hammingAxis x a)
        (hammingFibreMatrix n k L hk v x) =
      Real.sqrt lam • hammingFibreMatrix n k L hk v x := by
  classical
  let e := hammingWindowIndexEquiv n k L
  ext i p
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.smul_apply, smul_eq_mul]
  change
    (∑ z : Fin n × Fin (hammingWindowDimension n k L),
      hammingWindowChannelMatrix n k L v lam
          (z.1, e.symm z.2) (e.symm i) *
        (hammingAxis x z.1 *
          hammingWindowFibreMatrix n k L hk v x
            (e.symm z.2) p)) =
      Real.sqrt lam *
        hammingWindowFibreMatrix n k L hk v x (e.symm i) p
  have hwindow := congrArg
    (fun M : Matrix (HammingWindowIndex n k L)
        (Fin (MetricCodes.hammingFibreDimension n k)) ℝ =>
      M (e.symm i) p)
    (hammingWindowChannelMatrix_transpose_axis_fibre
      hn hk hkL hLn v hunit hv lam hlam heigen x)
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.smul_apply, smul_eq_mul] at hwindow
  rw [Fintype.sum_prod_type] at hwindow ⊢
  calc
    (∑ a : Fin n,
      ∑ t : Fin (hammingWindowDimension n k L),
        hammingWindowChannelMatrix n k L v lam
            (a, e.symm t) (e.symm i) *
          (hammingAxis x a *
            hammingWindowFibreMatrix n k L hk v x
              (e.symm t) p)) =
      ∑ a : Fin n,
        ∑ T : HammingWindowIndex n k L,
          hammingWindowChannelMatrix n k L v lam
              (a, T) (e.symm i) *
            (hammingAxis x a *
              hammingWindowFibreMatrix n k L hk v x T p) := by
          apply Finset.sum_congr rfl
          intro a _
          exact e.symm.sum_comp
            (fun T : HammingWindowIndex n k L =>
              hammingWindowChannelMatrix n k L v lam
                  (a, T) (e.symm i) *
                (hammingAxis x a *
                  hammingWindowFibreMatrix n k L hk v x T p))
    _ = Real.sqrt lam *
      hammingWindowFibreMatrix n k L hk v x (e.symm i) p :=
        hwindow

theorem matrixAxisLift_mul
    {κ ι ρ σ : Type*} [Fintype ρ]
    (z : κ → ℝ) (A : Matrix ι ρ ℝ) (C : Matrix ρ σ ℝ) :
    matrixAxisLift z (A * C) = matrixAxisLift z A * C := by
  classical
  ext p j
  simp only [matrixAxisLift, Matrix.mul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem hammingChannelMatrix_transpose_axis_projection
    {n k L : ℕ} (hn : 0 < n) (hk : 2 * k ≤ n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        lam • v)
    (x : BinaryWord n) :
    (hammingChannelMatrix n k L v lam)ᵀ *
      matrixAxisLift (fun a : Fin n => hammingAxis x a)
        ((hammingProjectionFamily hk hkL hLn
          v hunit (fun i => (hv i).le)).projection x) =
      Real.sqrt lam •
        ((hammingProjectionFamily hk hkL hLn
          v hunit (fun i => (hv i).le)).projection x) := by
  let A := hammingFibreMatrix n k L hk v x
  change
    (hammingChannelMatrix n k L v lam)ᵀ *
      matrixAxisLift (fun a : Fin n => hammingAxis x a)
        (A * Aᵀ) =
      Real.sqrt lam • (A * Aᵀ)
  rw [matrixAxisLift_mul, ← Matrix.mul_assoc,
    hammingChannelMatrix_transpose_axis_fibre
      hn hk hkL hLn v hunit hv lam hlam heigen x,
    Matrix.smul_mul]

/-- The hamming projection gram feature used in the binary-code argument. -/
def hammingProjectionGramFeature
    {n k L : ℕ} (hk : 2 * k ≤ n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (x : BinaryWord n) :
    EuclideanSpace ℝ
      ((Fin n × Fin (hammingWindowDimension n k L)) ×
        Fin (hammingWindowDimension n k L)) :=
  matrixAxisGramFeature
    (hammingProjectionFamily hk hkL hLn
      v hunit (fun i => (hv i).le))
    (fun (y : BinaryWord n) (a : Fin n) => hammingAxis y a)
    (hammingChannelMatrix n k L v lam)
    (Real.sqrt lam) x

theorem hammingProjectionGramFeature_inner
    {n k L : ℕ} (hn : 0 < n) (hk : 2 * k ≤ n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        lam • v)
    (x y : BinaryWord n) :
    @inner ℝ
      (EuclideanSpace ℝ
        ((Fin n × Fin (hammingWindowDimension n k L)) ×
          Fin (hammingWindowDimension n k L))) _
      (hammingProjectionGramFeature hk hkL hLn
        v hunit hv lam x)
      (hammingProjectionGramFeature hk hkL hLn
        v hunit hv lam y) =
      (MetricCodes.hammingCorrelation x y - lam) *
        (hammingProjectionFamily hk hkL hLn
          v hunit (fun i => (hv i).le)).overlap x y := by
  have hgram := matrixAxisResidual_gram
    (hammingProjectionFamily hk hkL hLn
      v hunit (fun i => (hv i).le))
    (fun (z : BinaryWord n) (a : Fin n) => hammingAxis z a)
    (hammingChannelMatrix n k L v lam)
    (Real.sqrt lam) lam
    (hammingChannelMatrix_transpose_mul
      hn hkL hLn v hv lam hlam heigen)
    (fun z => hammingChannelMatrix_transpose_axis_projection
      hn hk hkL hLn v hunit hv lam hlam heigen z)
    (Real.sq_sqrt hlam.le) x y
  change
    @inner ℝ
      (EuclideanSpace ℝ
        ((Fin n × Fin (hammingWindowDimension n k L)) ×
          Fin (hammingWindowDimension n k L))) _
      (hammingProjectionGramFeature hk hkL hLn
        v hunit hv lam x)
      (hammingProjectionGramFeature hk hkL hLn
        v hunit hv lam y) =
      (MetricCodes.hammingCorrelation x y - lam) *
        (hammingProjectionFamily hk hkL hLn
          v hunit (fun i => (hv i).le)).overlap x y
  have haxis' :
      (∑ a : Fin n, hammingAxis x a * hammingAxis y a) =
        MetricCodes.hammingCorrelation x y := by
    simpa only [PiLp.inner_apply, Real.inner_apply, mul_comm] using
      hammingAxis_inner hn x y
  change
    @inner ℝ
      (EuclideanSpace ℝ
        ((Fin n × Fin (hammingWindowDimension n k L)) ×
          Fin (hammingWindowDimension n k L))) _
      (matrixAxisGramFeature
        (hammingProjectionFamily hk hkL hLn
          v hunit (fun i => (hv i).le))
        (fun (z : BinaryWord n) (a : Fin n) => hammingAxis z a)
        (hammingChannelMatrix n k L v lam)
        (Real.sqrt lam) x)
      (matrixAxisGramFeature
        (hammingProjectionFamily hk hkL hLn
          v hunit (fun i => (hv i).le))
        (fun (z : BinaryWord n) (a : Fin n) => hammingAxis z a)
        (hammingChannelMatrix n k L v lam)
        (Real.sqrt lam) y) = _
  rw [← haxis']
  exact hgram

end Boolean

end

section

open scoped BigOperators
open Finset

/-- The word support used in the metric-code argument. -/
def wordSupport {n : ℕ} (x : BinaryWord n) : Finset (Fin n) :=
  Finset.univ.filter fun i => x i = true

@[simp] theorem mem_wordSupport {n : ℕ} (x : BinaryWord n) (i : Fin n) :
    i ∈ wordSupport x ↔ x i = true := by
  simp only [wordSupport, mem_filter, mem_univ, true_and]

private def wordOfSupport {n : ℕ} (s : Finset (Fin n)) : BinaryWord n :=
  fun i => decide (i ∈ s)

@[simp] theorem wordOfSupport_apply {n : ℕ} (s : Finset (Fin n)) (i : Fin n) :
    wordOfSupport s i = true ↔ i ∈ s := by
  simp only [wordOfSupport, decide_eq_true_eq]

@[simp] theorem wordSupport_wordOfSupport {n : ℕ} (s : Finset (Fin n)) :
    wordSupport (wordOfSupport s) = s := by
  ext i
  simp only [mem_wordSupport, wordOfSupport_apply]

@[simp] theorem wordOfSupport_wordSupport {n : ℕ} (x : BinaryWord n) :
    wordOfSupport (wordSupport x) = x := by
  funext i
  cases h : x i <;> simp [wordOfSupport, wordSupport, h]

private def binaryWordEquivFinset (n : ℕ) : BinaryWord n ≃ Finset (Fin n) where
  toFun := wordSupport
  invFun := wordOfSupport
  left_inv := wordOfSupport_wordSupport
  right_inv := wordSupport_wordOfSupport

theorem wordOfSupport_injective {n : ℕ} :
    Function.Injective (wordOfSupport (n := n)) :=
  (binaryWordEquivFinset n).symm.injective

theorem binaryWeight_eq_card_wordSupport {n : ℕ} (x : BinaryWord n) :
    binaryWeight x = (wordSupport x).card := by
  rfl

theorem hammingDist_comm {n : ℕ} (x y : BinaryWord n) :
    hammingDist x y = hammingDist y x := by
  unfold hammingDist
  congr 1
  ext i
  simp only [ne_eq, mem_filter, mem_univ, true_and, ne_comm]

theorem hammingDist_eq_card_support_sdiff {n : ℕ}
    (x y : BinaryWord n) :
    hammingDist x y =
      (wordSupport x \ wordSupport y).card +
      (wordSupport y \ wordSupport x).card := by
  have hsets :
      (Finset.univ.filter fun i => x i ≠ y i) =
        (wordSupport x \ wordSupport y) ∪
        (wordSupport y \ wordSupport x) := by
    ext i
    cases hx : x i <;> cases hy : y i <;>
      simp [wordSupport, hx, hy]
  have hdisj :
      Disjoint (wordSupport x \ wordSupport y)
        (wordSupport y \ wordSupport x) := by
    apply Finset.disjoint_left.mpr
    intro i hxy hyx
    exact (Finset.mem_sdiff.mp hxy).2 (Finset.mem_sdiff.mp hyx).1
  unfold hammingDist
  rw [hsets, Finset.card_union_of_disjoint hdisj]

theorem hammingDist_eq_two_mul_of_binaryWeight_eq {n : ℕ}
    (x y : BinaryWord n) (hweight : binaryWeight x = binaryWeight y) :
    hammingDist x y = 2 * (wordSupport x \ wordSupport y).card := by
  have hcard : (wordSupport x).card = (wordSupport y).card := by
    simpa only [binaryWeight_eq_card_wordSupport] using hweight
  have hdiff :
      (wordSupport x \ wordSupport y).card =
        (wordSupport y \ wordSupport x).card :=
    Finset.card_sdiff_comm hcard
  rw [hammingDist_eq_card_support_sdiff, ← hdiff, two_mul]

/-- The johnson dist used in the metric-code argument. -/
def johnsonDist {n w : ℕ} (x y : JohnsonSphere n w) : ℕ :=
  (wordSupport (x : BinaryWord n) \ wordSupport (y : BinaryWord n)).card

theorem hammingDist_eq_two_mul_johnsonDist {n w : ℕ}
    (x y : JohnsonSphere n w) :
    hammingDist (x : BinaryWord n) (y : BinaryWord n) =
      2 * johnsonDist x y := by
  apply hammingDist_eq_two_mul_of_binaryWeight_eq
  exact x.property.trans y.property.symm

theorem johnsonDist_eq_weight_sub_inter {n w : ℕ}
    (x y : JohnsonSphere n w) :
    johnsonDist x y =
      w - (wordSupport (x : BinaryWord n) ∩
        wordSupport (y : BinaryWord n)).card := by
  unfold johnsonDist
  rw [Finset.card_sdiff, Finset.inter_comm]
  rw [← binaryWeight_eq_card_wordSupport, x.property]

private def binaryTranslate {n : ℕ} (x y : BinaryWord n) : BinaryWord n :=
  fun i => Bool.xor (x i) (y i)

@[simp] theorem binaryTranslate_involutive {n : ℕ} (x y : BinaryWord n) :
    binaryTranslate x (binaryTranslate x y) = y := by
  funext i
  change Bool.xor (x i) (Bool.xor (x i) (y i)) = y i
  rw [← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]

theorem binaryTranslate_injective {n : ℕ} (x : BinaryWord n) :
    Function.Injective (binaryTranslate x) := by
  intro y z h
  have := congrArg (binaryTranslate x) h
  simpa only [binaryTranslate_involutive] using this

theorem hammingDist_binaryTranslate {n : ℕ} (z x y : BinaryWord n) :
    hammingDist (binaryTranslate z x) (binaryTranslate z y) =
      hammingDist x y := by
  unfold hammingDist
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i _
  exact not_congr (Bool.xor_right_inj (x := z i) (y := x i) (z := y i))

theorem binaryWeight_binaryTranslate {n : ℕ} (x y : BinaryWord n) :
    binaryWeight (binaryTranslate x y) = hammingDist x y := by
  unfold binaryWeight hammingDist
  congr 1
  ext i
  simp only [binaryTranslate, bne_iff_ne, ne_eq, mem_filter, mem_univ, true_and]

private def weightShell (n w : ℕ) : Finset (BinaryWord n) :=
  Finset.univ.filter fun x => binaryWeight x = w

@[simp] theorem mem_weightShell {n w : ℕ} (x : BinaryWord n) :
    x ∈ weightShell n w ↔ binaryWeight x = w := by
  simp only [weightShell, mem_filter, mem_univ, true_and]

theorem weightShell_eq_image (n w : ℕ) :
    weightShell n w =
      ((Finset.univ : Finset (Fin n)).powersetCard w).image wordOfSupport := by
  ext x
  constructor
  · intro hx
    have hw : binaryWeight x = w := (mem_weightShell x).mp hx
    refine Finset.mem_image.mpr
      ⟨wordSupport x, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩,
        wordOfSupport_wordSupport x⟩
    simpa only [binaryWeight_eq_card_wordSupport] using hw
  · intro hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    apply (mem_weightShell _).mpr
    rw [binaryWeight_eq_card_wordSupport, wordSupport_wordOfSupport]
    exact (Finset.mem_powersetCard.mp hs).2

theorem card_weightShell (n w : ℕ) :
    (weightShell n w).card = n.choose w := by
  rw [weightShell_eq_image, Finset.card_image_of_injective _ wordOfSupport_injective,
    Finset.card_powersetCard]
  simp only [card_univ, Fintype.card_fin]

private def hammingSphere {n : ℕ} (x : BinaryWord n) (r : ℕ) :
    Finset (BinaryWord n) :=
  Finset.univ.filter fun y => hammingDist x y = r

@[simp] theorem mem_hammingSphere {n r : ℕ} (x y : BinaryWord n) :
    y ∈ hammingSphere x r ↔ hammingDist x y = r := by
  simp only [hammingSphere, mem_filter, mem_univ, true_and]

theorem hammingSphere_eq_image {n : ℕ} (x : BinaryWord n) (r : ℕ) :
    hammingSphere x r = (weightShell n r).image (binaryTranslate x) := by
  ext y
  constructor
  · intro hy
    have hd : hammingDist x y = r := (mem_hammingSphere x y).mp hy
    refine Finset.mem_image.mpr
      ⟨binaryTranslate x y, (mem_weightShell _).mpr ?_,
        binaryTranslate_involutive x y⟩
    simpa only [binaryWeight_binaryTranslate] using hd
  · intro hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    apply (mem_hammingSphere _ _).mpr
    rw [← binaryWeight_binaryTranslate, binaryTranslate_involutive]
    exact (mem_weightShell _).mp hz

theorem card_hammingSphere {n : ℕ} (x : BinaryWord n) (r : ℕ) :
    (hammingSphere x r).card = n.choose r := by
  rw [hammingSphere_eq_image,
    Finset.card_image_of_injective _ (binaryTranslate_injective x),
    card_weightShell]

private def localizedCode {n : ℕ} (C : Finset (BinaryWord n))
    (z : BinaryWord n) (w : ℕ) : Finset (BinaryWord n) :=
  C.filter fun x => binaryWeight (binaryTranslate z x) = w

@[simp] theorem mem_localizedCode {n w : ℕ} (C : Finset (BinaryWord n))
    (z x : BinaryWord n) :
    x ∈ localizedCode C z w ↔
      x ∈ C ∧ binaryWeight (binaryTranslate z x) = w := by
  simp only [localizedCode, mem_filter]

private def translateLocalizedCode {n : ℕ} (C : Finset (BinaryWord n))
    (z : BinaryWord n) (w : ℕ) : Finset (BinaryWord n) :=
  (localizedCode C z w).image (binaryTranslate z)

theorem translateLocalizedCode_subset_weightShell {n w : ℕ}
    (C : Finset (BinaryWord n)) (z : BinaryWord n) :
    translateLocalizedCode C z w ⊆ weightShell n w := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact (mem_weightShell _).mpr ((mem_localizedCode C z x).mp hx).2

theorem card_translateLocalizedCode {n w : ℕ}
    (C : Finset (BinaryWord n)) (z : BinaryWord n) :
    (translateLocalizedCode C z w).card = (localizedCode C z w).card := by
  exact Finset.card_image_of_injective _ (binaryTranslate_injective z)

theorem translateLocalizedCode_isBinaryCode {n d w : ℕ}
    (C : Finset (BinaryWord n)) (z : BinaryWord n)
    (hC : IsBinaryCode d C) :
    IsBinaryCode d (translateLocalizedCode C z w) := by
  intro x hx y hy hxy
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
  rw [hammingDist_binaryTranslate]
  apply hC ((mem_localizedCode C z u).mp hu).1
    ((mem_localizedCode C z v).mp hv).1
  intro huv
  exact hxy (congrArg (binaryTranslate z) huv)

theorem localization_double_count {n : ℕ}
    (C : Finset (BinaryWord n)) (w : ℕ) :
    (∑ z : BinaryWord n, (localizedCode C z w).card) =
      C.card * n.choose w := by
  calc
    (∑ z : BinaryWord n, (localizedCode C z w).card) =
        ∑ z : BinaryWord n, ∑ x ∈ C,
          if binaryWeight (binaryTranslate z x) = w then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro z hz
      change
        (C.filter fun x => binaryWeight (binaryTranslate z x) = w).card =
          ∑ x ∈ C,
            if binaryWeight (binaryTranslate z x) = w then 1 else 0
      exact Finset.card_filter
        (fun x => binaryWeight (binaryTranslate z x) = w) C
    _ = ∑ x ∈ C, ∑ z : BinaryWord n,
          if binaryWeight (binaryTranslate z x) = w then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x ∈ C, (hammingSphere x w).card := by
      apply Finset.sum_congr rfl
      intro x hx
      calc
        (∑ z : BinaryWord n,
            if binaryWeight (binaryTranslate z x) = w then 1 else 0) =
            (Finset.univ.filter fun z : BinaryWord n =>
              binaryWeight (binaryTranslate z x) = w).card :=
          (Finset.card_filter
            (fun z : BinaryWord n =>
              binaryWeight (binaryTranslate z x) = w)
            Finset.univ).symm
        _ = (hammingSphere x w).card := by
          congr 1
          ext z
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            mem_hammingSphere, binaryWeight_binaryTranslate]
          rw [hammingDist_comm]
    _ = C.card * n.choose w := by
      simp only [card_hammingSphere, sum_const, smul_eq_mul]

theorem bassalygo_elias_bound {n d w B : ℕ}
    (C : Finset (BinaryWord n)) (hC : IsBinaryCode d C)
    (hB : ∀ D : Finset (BinaryWord n),
      D ⊆ weightShell n w → IsBinaryCode d D → D.card ≤ B) :
    C.card * n.choose w ≤ 2 ^ n * B := by
  calc
    C.card * n.choose w =
        ∑ z : BinaryWord n, (localizedCode C z w).card :=
      (localization_double_count C w).symm
    _ ≤ ∑ _z : BinaryWord n, B := by
      apply Finset.sum_le_sum
      intro z hz
      rw [← card_translateLocalizedCode C z]
      exact hB (translateLocalizedCode C z w)
        (translateLocalizedCode_subset_weightShell C z)
        (translateLocalizedCode_isBinaryCode C z hC)
    _ = 2 ^ n * B := by
      simp only [sum_const, card_univ, Fintype.card_pi, Fintype.card_bool, prod_const,
        Fintype.card_fin, smul_eq_mul]

/-- The preceding binomial used in the metric-code argument. -/
def precedingBinomial (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => n.choose k

theorem choose_monotone_to_half (n : ℕ) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ n / 2) :
    n.choose i ≤ n.choose j := by
  have hi : 2 * i ≤ n := by omega
  have hj' : 2 * j ≤ n := by omega
  rw [← sum_booleanHarmonicDimension n i hi,
    ← sum_booleanHarmonicDimension n j hj']
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))

/-- The johnson ambient dimension used in the metric-code argument. -/
def johnsonAmbientDimension (n a L : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc a L, booleanHarmonicDimension n j

theorem johnsonAmbientDimension_eq (n a L : ℕ)
    (haL : a ≤ L) (hL : L ≤ n / 2) :
    johnsonAmbientDimension n a L =
      n.choose L - precedingBinomial n a := by
  unfold johnsonAmbientDimension
  induction L generalizing a with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      simp only [Icc_self, booleanHarmonicDimension, sum_singleton, Nat.choose_zero_right,
        precedingBinomial, tsub_zero]
  | succ L ih =>
      by_cases htop : a = L + 1
      · subst a
        simp only [Icc_self, booleanHarmonicDimension, sum_singleton, precedingBinomial]
      · have ha' : a ≤ L := by omega
        have hhalf : L < n / 2 := by omega
        have hchoose : n.choose L ≤ n.choose (L + 1) :=
          Nat.choose_le_succ_of_lt_half_left hhalf
        have hbase : precedingBinomial n a ≤ n.choose L := by
          cases a with
          | zero => simp only [precedingBinomial, zero_le]
          | succ a =>
              apply choose_monotone_to_half n
              · omega
              · exact hhalf.le
        have hinter :
            Finset.Icc a (L + 1) =
              insert (L + 1) (Finset.Icc a L) := by
          ext j
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        rw [hinter, Finset.sum_insert (by simp only [mem_Icc, add_le_iff_nonpos_right,
                                            nonpos_iff_eq_zero, one_ne_zero, and_false,
                                            not_false_eq_true]),
          ih a ha' hhalf.le, booleanHarmonicDimension_succ]
        exact Nat.sub_add_sub_cancel hchoose hbase

theorem johnsonAmbientDimension_eq_of_fibre (n p q L : ℕ)
    (hpq : p + q ≤ L) (hL : L ≤ n / 2) :
    johnsonAmbientDimension n (p + q) L =
      n.choose L - precedingBinomial n (p + q) :=
  johnsonAmbientDimension_eq n (p + q) L hpq hL

end

end MetricCodes

namespace SpherePacking

section


open Filter MeasureTheory Metric
open scoped ENNReal InnerProductSpace Topology

attribute [-instance]
  CohnElkies.numeralTwoAtLeast
  CohnElkies.euclideanFiniteDimensional
  CohnElkies.euclideanBorelSpace

/-- The euclidean used in the spherical-code argument. -/
abbrev Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)



end

section


open Filter Real
open scoped Nat Topology

private def factorialLogError (n : ℕ) : ℝ :=
  Real.log (n.factorial : ℝ) / (n : ℝ) - Real.log (n : ℝ) + 1

theorem tendsto_log_natCast_div_natCast :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have h :=
    (Real.tendsto_pow_log_div_mul_add_atTop
      (1 : ℝ) 0 1 (by norm_num)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  refine h.congr ?_
  intro n
  simp only [pow_one, one_mul, add_zero, Function.comp_apply]

theorem tendsto_log_two_mul_natCast_div_natCast :
    Tendsto (fun n : ℕ =>
      Real.log (2 * (n : ℝ)) / (n : ℝ)) atTop (nhds 0) := by
  have hc := tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)
  have hs := hc.add tendsto_log_natCast_div_natCast
  have heq :
      (fun n : ℕ =>
        Real.log 2 / (n : ℝ) + Real.log (n : ℝ) / (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => Real.log (2 * (n : ℝ)) / (n : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    rw [Real.log_mul (by norm_num) hn', add_div]
  simpa only [add_zero] using hs.congr' heq

theorem tendsto_log_stirlingSeq_div_natCast :
    Tendsto
      (fun n : ℕ => Real.log (Stirling.stirlingSeq n) / (n : ℝ))
      atTop (nhds 0) := by
  have hlog :
      Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n))
        atTop (nhds (Real.log (Real.sqrt Real.pi))) :=
    (Real.continuousAt_log (by positivity)).tendsto.comp
      Stirling.tendsto_stirlingSeq_sqrt_pi
  have hinv := tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)
  simpa only [div_eq_mul_inv, mul_zero] using hlog.mul hinv

theorem factorialLogError_eq (n : ℕ) (hn : n ≠ 0) :
    factorialLogError n =
      Real.log (Stirling.stirlingSeq n) / (n : ℝ) +
        (1 / 2 : ℝ) * Real.log (2 * (n : ℝ)) / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have he : Real.exp (1 : ℝ) ≠ 0 := (Real.exp_pos 1).ne'
  have hst := Stirling.log_stirlingSeq_formula n
  rw [Real.log_div hn' he, Real.log_exp] at hst
  have hlog : Real.log ((n : ℝ) * 2) = Real.log (2 * (n : ℝ)) := by
    rw [mul_comm]
  unfold factorialLogError
  field_simp [hn']
  nlinarith [hst, hlog]

theorem tendsto_factorialLogError :
    Tendsto factorialLogError atTop (nhds 0) := by
  have hhalf :=
    tendsto_log_two_mul_natCast_div_natCast.const_mul (1 / 2 : ℝ)
  have hsum := tendsto_log_stirlingSeq_div_natCast.add hhalf
  have heq :
      (fun n : ℕ =>
        Real.log (Stirling.stirlingSeq n) / (n : ℝ) +
          (1 / 2 : ℝ) * (Real.log (2 * (n : ℝ)) / (n : ℝ))) =ᶠ[atTop]
        factorialLogError := by
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    rw [factorialLogError_eq n hn]
    ring
  simpa only [one_div, mul_zero, add_zero] using hsum.congr' heq

theorem scaled_log_factorial_identity (m n : ℕ)
    (hm : m ≠ 0) (hn : n ≠ 0) :
    Real.log (m.factorial : ℝ) / (n : ℝ) -
        ((m : ℝ) / (n : ℝ)) * Real.log (n : ℝ) =
      ((m : ℝ) / (n : ℝ)) *
        (factorialLogError m + Real.log ((m : ℝ) / (n : ℝ)) - 1) := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [Real.log_div hm' hn']
  unfold factorialLogError
  field_simp [hm', hn']
  ring_nf

theorem tendsto_scaled_log_factorial_sub
    (k : ℕ → ℕ) (u : ℝ)
    (hk : Tendsto k atTop atTop)
    (hratio : Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ))
      atTop (nhds u))
    (hu : u ≠ 0) :
    Tendsto
      (fun n : ℕ =>
        Real.log ((k n).factorial : ℝ) / (n : ℝ) -
          ((k n : ℝ) / (n : ℝ)) * Real.log (n : ℝ))
      atTop (nhds (u * Real.log u - u)) := by
  have herror :
      Tendsto (fun n : ℕ => factorialLogError (k n))
        atTop (nhds 0) :=
    tendsto_factorialLogError.comp hk
  have hlog :
      Tendsto (fun n : ℕ => Real.log ((k n : ℝ) / (n : ℝ)))
        atTop (nhds (Real.log u)) :=
    (Real.continuousAt_log hu).tendsto.comp hratio
  have hproduct :=
    hratio.mul ((herror.add hlog).sub (tendsto_const_nhds (x := (1 : ℝ))))
  have heq :
      (fun n : ℕ =>
        ((k n : ℝ) / (n : ℝ)) *
          (factorialLogError (k n) +
            Real.log ((k n : ℝ) / (n : ℝ)) - 1)) =ᶠ[atTop]
      (fun n : ℕ =>
        Real.log ((k n).factorial : ℝ) / (n : ℝ) -
          ((k n : ℝ) / (n : ℝ)) * Real.log (n : ℝ)) := by
    filter_upwards [hk.eventually (eventually_ne_atTop (0 : ℕ)),
      eventually_ne_atTop (0 : ℕ)] with n hkn hn
    exact (scaled_log_factorial_identity (k n) n hkn hn).symm
  simpa only [zero_add, mul_sub, mul_one] using hproduct.congr' heq

theorem log_add_choose_div_eq (a b n : ℕ) :
    Real.log (((a + b).choose a : ℝ)) / (n : ℝ) =
      Real.log ((a + b).factorial : ℝ) / (n : ℝ) -
        Real.log (a.factorial : ℝ) / (n : ℝ) -
        Real.log (b.factorial : ℝ) / (n : ℝ) := by
  rw [Nat.cast_add_choose ℝ]
  rw [Real.log_div (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) (by positivity)]
  ring

theorem tendsto_log_add_choose_div
    (k l : ℕ → ℕ) (u v : ℝ)
    (hk : Tendsto k atTop atTop)
    (hl : Tendsto l atTop atTop)
    (hku : Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ))
      atTop (nhds u))
    (hlv : Tendsto (fun n : ℕ => (l n : ℝ) / (n : ℝ))
      atTop (nhds v))
    (hu : 0 < u) (hv : 0 < v) :
    Tendsto
      (fun n : ℕ =>
        Real.log (((k n + l n).choose (k n) : ℝ)) / (n : ℝ))
      atTop
      (nhds ((u + v) * Real.log (u + v) -
        u * Real.log u - v * Real.log v)) := by
  have hsum : Tendsto (fun n : ℕ => k n + l n) atTop atTop := by
    apply tendsto_atTop_mono (f := k)
    · intro n
      omega
    · exact hk
  have hsumratio :
      Tendsto (fun n : ℕ => ((k n + l n : ℕ) : ℝ) / (n : ℝ))
        atTop (nhds (u + v)) := by
    simpa only [Nat.cast_add, add_div] using hku.add hlv
  have htotal :=
    tendsto_scaled_log_factorial_sub (fun n => k n + l n)
      (u + v) hsum hsumratio (ne_of_gt (add_pos hu hv))
  have hfirst := tendsto_scaled_log_factorial_sub k u hk hku hu.ne'
  have hsecond := tendsto_scaled_log_factorial_sub l v hl hlv hv.ne'
  have hcomb := (htotal.sub hfirst).sub hsecond
  have heq :
      (fun n : ℕ =>
        (Real.log ((k n + l n).factorial : ℝ) / (n : ℝ) -
          (((k n + l n : ℕ) : ℝ) / (n : ℝ)) * Real.log (n : ℝ)) -
          (Real.log ((k n).factorial : ℝ) / (n : ℝ) -
            ((k n : ℝ) / (n : ℝ)) * Real.log (n : ℝ)) -
          (Real.log ((l n).factorial : ℝ) / (n : ℝ) -
            ((l n : ℝ) / (n : ℝ)) * Real.log (n : ℝ))) =ᶠ[atTop]
  (fun n : ℕ =>
        Real.log (((k n + l n).choose (k n) : ℝ)) / (n : ℝ)) := by
    apply Eventually.of_forall
    intro n
    change _ = Real.log (((k n + l n).choose (k n) : ℝ)) / (n : ℝ)
    rw [log_add_choose_div_eq]
    push_cast
    ring
  have hlimit :
      ((u + v) * Real.log (u + v) - (u + v)) -
          (u * Real.log u - u) - (v * Real.log v - v) =
        (u + v) * Real.log (u + v) -
          u * Real.log u - v * Real.log v := by
    ring
  rw [← hlimit]
  exact hcomb.congr' heq

end

end SpherePacking

namespace MetricCodes

section


open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology

namespace Hamming

private noncomputable def validCodes (n d : ℕ) : Finset (Finset (BinaryWord n)) := by
  classical
  exact Finset.univ.filter (MetricCodes.IsBinaryCode d)

theorem mem_validCodes {n d : ℕ} (C : Finset (BinaryWord n)) :
    C ∈ validCodes n d ↔ MetricCodes.IsBinaryCode d C := by
  classical
  simp only [validCodes, Finset.mem_filter, Finset.mem_univ, true_and]

theorem validCodes_nonempty (n d : ℕ) : (validCodes n d).Nonempty := by
  refine ⟨∅, (mem_validCodes (n := n) (d := d) ∅).2 ?_⟩
  simp only [IsBinaryCode, Finset.notMem_empty, ne_eq, IsEmpty.forall_iff, implies_true]

/-- The code number used in the binary-code argument. -/
noncomputable def codeNumber (n d : ℕ) : ℕ :=
  (validCodes n d).sup fun C => C.card

theorem card_le_codeNumber {n d : ℕ} (C : Finset (BinaryWord n))
    (hC : MetricCodes.IsBinaryCode d C) :
    C.card ≤ codeNumber n d := by
  unfold codeNumber
  exact Finset.le_sup ((mem_validCodes C).2 hC)

theorem exists_codeNumber (n d : ℕ) :
    ∃ C : Finset (BinaryWord n),
      MetricCodes.IsBinaryCode d C ∧ C.card = codeNumber n d := by
  obtain ⟨C, hC, hmax⟩ :=
    Finset.exists_mem_eq_sup (validCodes n d)
      (validCodes_nonempty n d) (fun C => C.card)
  exact ⟨C, (mem_validCodes C).1 hC, hmax.symm⟩

theorem codeNumber_real_le_of_forall {n d : ℕ} {B : ℝ}
    (h : ∀ C : Finset (BinaryWord n),
      MetricCodes.IsBinaryCode d C → (C.card : ℝ) ≤ B) :
    (codeNumber n d : ℝ) ≤ B := by
  obtain ⟨C, hC, hmax⟩ := exists_codeNumber n d
  simpa only [hmax] using h C hC

theorem codeNumber_pos (n d : ℕ) : 0 < codeNumber n d := by
  classical
  let x : BinaryWord n := fun _ => false
  have hcode : MetricCodes.IsBinaryCode d ({x} : Finset (BinaryWord n)) := by
    intro u hu v hv huv
    have hu' : u = x := Finset.mem_singleton.mp hu
    have hv' : v = x := Finset.mem_singleton.mp hv
    exact False.elim (huv (hu'.trans hv'.symm))
  have hcard : 1 ≤ codeNumber n d := by
    simpa only [Finset.card_singleton] using card_le_codeNumber ({ x } : Finset (BinaryWord n))
      hcode
  omega

/-- The ambient dimension used in the binary-code argument. -/
def ambientDimension (n k L : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (L - k + 1), n.choose (k + j)

theorem hammingFibreDimension_pos {n k : ℕ} (hk : 2 * k ≤ n) :
    0 < MetricCodes.hammingFibreDimension n k := by
  cases k with
  | zero => simp only [hammingFibreDimension, booleanHarmonicDimension, Order.lt_one_iff]
  | succ j =>
      change 0 < n.choose (j + 1) - n.choose j
      apply Nat.sub_pos_of_lt
      have hchoose : 0 < n.choose j := Nat.choose_pos (by omega)
      have hfactor : j + 1 < n - j := by omega
      have hmul :
          n.choose j * (j + 1) < n.choose j * (n - j) :=
        Nat.mul_lt_mul_of_pos_left hfactor hchoose
      have hmul' :
          n.choose j * (j + 1) < n.choose (j + 1) * (j + 1) := by
        calc
          n.choose j * (j + 1) < n.choose j * (n - j) := hmul
          _ = n.choose (j + 1) * (j + 1) :=
            (Nat.choose_succ_right_eq n j).symm
      exact (Nat.mul_lt_mul_right (by omega : 0 < j + 1)).mp hmul'

/-- The threshold used in the binary-code argument. -/
def threshold (n d : ℕ) : ℝ :=
  1 - 2 * (d : ℝ) / (n : ℝ)

theorem threshold_lt_one {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    threshold n d < 1 := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  unfold threshold
  have hpos : 0 < 2 * (d : ℝ) / (n : ℝ) := by positivity
  linarith

/-- The index used in the binary-code argument. -/
abbrev Index (k L : ℕ) := Fin (L - k + 1)

/-- The space used in the binary-code argument. -/
abbrev Space (k L : ℕ) := EuclideanSpace ℝ (Index k L)

/-- The matrix used in the binary-code argument. -/
def matrix (n k L : ℕ) : Matrix (Index k L) (Index k L) ℝ :=
  MetricCodes.hammingJacobiMatrix n k L

theorem matrix_hermitian (n k L : ℕ) : (matrix n k L).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have h := congrArg
    (fun A : Matrix (Index k L) (Index k L) ℝ => A i j)
    (MetricCodes.hammingJacobiMatrix_symmetric n k L)
  simpa only [matrix, star_trivial, Matrix.transpose_apply] using h

/-- The operator used in the binary-code argument. -/
def operator (n k L : ℕ) : Space k L →ₗ[ℝ] Space k L :=
  Matrix.toEuclideanLin (matrix n k L)

theorem operator_isSymmetric (n k L : ℕ) :
    (operator n k L).IsSymmetric := by
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (matrix_hermitian n k L)

/-- The continuous operator used in the binary-code argument. -/
def continuousOperator (n k L : ℕ) : Space k L →L[ℝ] Space k L :=
  LinearMap.toContinuousLinearMap (operator n k L)

/-- The rayleigh used in the binary-code argument. -/
def rayleigh (n k L : ℕ) (x : Space k L) : ℝ :=
  (continuousOperator n k L).rayleighQuotient x

theorem rayleigh_bddAbove (n k L : ℕ) :
    BddAbove
      (Set.range
        (fun x : {x : Space k L // x ≠ 0} => rayleigh n k L x)) := by
  refine ⟨‖continuousOperator n k L‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (le_abs_self _).trans
    ((continuousOperator n k L).rayleighQuotient_le_norm x)

/-- The top eigenvalue used in the binary-code argument. -/
def topEigenvalue (n k L : ℕ) : ℝ :=
  ⨆ x : {x : Space k L // x ≠ 0}, rayleigh n k L x

theorem rayleigh_le_top (n k L : ℕ) (x : Space k L) (hx : x ≠ 0) :
    rayleigh n k L x ≤ topEigenvalue n k L := by
  exact le_ciSup (rayleigh_bddAbove n k L) ⟨x, hx⟩

theorem topEigenvalue_hasEigenvalue (n k L : ℕ) :
    Module.End.HasEigenvalue (operator n k L) (topEigenvalue n k L) := by
  have h := (operator_isSymmetric n k L).hasEigenvalue_iSup_of_finiteDimensional
  simpa only [topEigenvalue, ne_eq, rayleigh, ContinuousLinearMap.rayleighQuotient,
    continuousOperator, ContinuousLinearMap.reApplyInnerSelf_apply,
    LinearMap.coe_toContinuousLinearMap', RCLike.re_to_real, Order.lt_one_iff,
    Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one, Real.ringHom_apply] using h

theorem exists_topEigenvector (n k L : ℕ) :
    ∃ x : Space k L, x ≠ 0 ∧
      operator n k L x = topEigenvalue n k L • x := by
  obtain ⟨x, hx⟩ :=
    (topEigenvalue_hasEigenvalue n k L).exists_hasEigenvector
  exact ⟨x, hx.2, hx.apply_eq_smul⟩

theorem rayleigh_eq_inner (n k L : ℕ) (x : Space k L) :
    rayleigh n k L x =
      @inner ℝ (Space k L) _ (operator n k L x) x / ‖x‖ ^ 2 := by
  rfl

/-- The coordinate abs used in the binary-code argument. -/
def coordinateAbs (k L : ℕ) (x : Space k L) : Space k L :=
  WithLp.toLp 2 (fun p : Index k L => |x p|)

theorem coordinateAbs_nonneg (k L : ℕ)
    (x : Space k L) (p : Index k L) :
    0 ≤ coordinateAbs k L x p :=
  abs_nonneg _

theorem coordinateAbs_norm (k L : ℕ) (x : Space k L) :
    ‖coordinateAbs k L x‖ = ‖x‖ := by
  have hsquare : ‖coordinateAbs k L x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [coordinateAbs, sq_abs]
  nlinarith [norm_nonneg (coordinateAbs k L x), norm_nonneg x]

theorem coordinateAbs_ne_zero (k L : ℕ)
    {x : Space k L} (hx : x ≠ 0) :
    coordinateAbs k L x ≠ 0 := by
  intro habs
  have hnorm := coordinateAbs_norm k L x
  rw [habs, norm_zero] at hnorm
  exact hx (norm_eq_zero.mp hnorm.symm)

theorem matrix_entry_nonneg {n k L : ℕ}
    (hn : 0 < n) (hkL : k ≤ L) (hLn : L + k ≤ n)
    (p q : Index k L) :
    0 ≤ matrix n k L p q := by
  unfold matrix MetricCodes.hammingJacobiMatrix
  split_ifs with hpq hqp
  · apply (MetricCodes.hammingJacobiEntry_pos hn (by omega) ?_).le
    have hq := q.isLt
    omega
  · apply (MetricCodes.hammingJacobiEntry_pos hn (by omega) ?_).le
    have hp := p.isLt
    omega
  · exact le_rfl

theorem inner_le_inner_coordinateAbs {n k L : ℕ}
    (hn : 0 < n) (hkL : k ≤ L) (hLn : L + k ≤ n)
    (x : Space k L) :
    @inner ℝ (Space k L) _ (operator n k L x) x ≤
      @inner ℝ (Space k L) _
        (operator n k L (coordinateAbs k L x))
        (coordinateAbs k L x) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [Real.inner_apply]
  change
    (∑ p : Index k L,
      (∑ q : Index k L, matrix n k L p q * x q) * x p) ≤
    (∑ p : Index k L,
      (∑ q : Index k L, matrix n k L p q * |x q|) * |x p|)
  simp_rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro q hq
  have hentry := matrix_entry_nonneg hn hkL hLn p q
  have hproduct : x q * x p ≤ |x q| * |x p| := by
    calc
      x q * x p ≤ |x q * x p| := le_abs_self _
      _ = |x q| * |x p| := abs_mul _ _
  calc
    matrix n k L p q * x q * x p =
        matrix n k L p q * (x q * x p) := by ring
    _ ≤ matrix n k L p q * (|x q| * |x p|) :=
      mul_le_mul_of_nonneg_left hproduct hentry
    _ = matrix n k L p q * |x q| * |x p| := by ring

theorem rayleigh_le_coordinateAbs {n k L : ℕ}
    (hn : 0 < n) (hkL : k ≤ L) (hLn : L + k ≤ n)
    (x : Space k L) :
    rayleigh n k L x ≤ rayleigh n k L (coordinateAbs k L x) := by
  rw [rayleigh_eq_inner, rayleigh_eq_inner, coordinateAbs_norm]
  gcongr
  exact inner_le_inner_coordinateAbs hn hkL hLn x

theorem rayleigh_eq_of_eigenvector
    (n k L : ℕ) (x : Space k L) (hx : x ≠ 0)
    (eigenvalue : ℝ)
    (heig : operator n k L x = eigenvalue • x) :
    rayleigh n k L x = eigenvalue := by
  rw [rayleigh_eq_inner, heig,
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hnorm : ‖x‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  field_simp [hnorm]

theorem coordinateAbs_top_rayleigh {n k L : ℕ}
    (hn : 0 < n) (hkL : k ≤ L) (hLn : L + k ≤ n)
    (x : Space k L) (hx : x ≠ 0)
    (heig : operator n k L x = topEigenvalue n k L • x) :
    rayleigh n k L (coordinateAbs k L x) = topEigenvalue n k L := by
  have hbelow := rayleigh_le_coordinateAbs hn hkL hLn x
  have habove := rayleigh_le_top n k L
    (coordinateAbs k L x) (coordinateAbs_ne_zero k L hx)
  rw [rayleigh_eq_of_eigenvector n k L x hx
    (topEigenvalue n k L) heig] at hbelow
  exact le_antisymm habove hbelow

theorem exists_nonnegative_topEigenvector {n k L : ℕ}
    (hn : 0 < n) (hkL : k ≤ L) (hLn : L + k ≤ n) :
    ∃ x : Space k L,
      x ≠ 0 ∧ operator n k L x = topEigenvalue n k L • x ∧
      ∀ p : Index k L, 0 ≤ x p := by
  obtain ⟨x, hx, heig⟩ := exists_topEigenvector n k L
  let y : Space k L := coordinateAbs k L x
  have hy : y ≠ 0 := coordinateAbs_ne_zero k L hx
  have hyray : rayleigh n k L y = topEigenvalue n k L :=
    coordinateAbs_top_rayleigh hn hkL hLn x hx heig
  have hself : IsSelfAdjoint (continuousOperator n k L) :=
    (operator_isSymmetric n k L).isSelfAdjoint
  have hmax :
      IsMaxOn (continuousOperator n k L).reApplyInnerSelf
        (sphere (0 : Space k L) ‖y‖) y := by
    intro z hz
    have hnorm : ‖z‖ = ‖y‖ := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
    have hznonzero : z ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hnorm
      exact hy (norm_eq_zero.mp hnorm.symm)
    have hray := rayleigh_le_top n k L z hznonzero
    rw [← hyray] at hray
    change
      (continuousOperator n k L).reApplyInnerSelf z / ‖z‖ ^ 2 ≤
        (continuousOperator n k L).reApplyInnerSelf y / ‖y‖ ^ 2 at hray
    rw [hnorm] at hray
    have hnormpos : 0 < ‖y‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr hy)
    exact (div_le_div_iff_of_pos_right hnormpos).mp hray
  have heigy := hself.hasEigenvector_of_isMaxOn hy hmax
  refine ⟨y, hy, ?_, fun p => coordinateAbs_nonneg k L x p⟩
  have happly := heigy.apply_eq_smul
  simpa only [topEigenvalue, ne_eq, rayleigh, continuousOperator,
    LinearMap.coe_toContinuousLinearMap, Real.ringHom_apply] using happly

theorem exists_nonnegative_unit_topEigenvector {n k L : ℕ}
    (hn : 0 < n) (hkL : k ≤ L) (hLn : L + k ≤ n) :
    ∃ x : Space k L,
      ‖x‖ = 1 ∧ operator n k L x = topEigenvalue n k L • x ∧
      ∀ p : Index k L, 0 ≤ x p := by
  obtain ⟨x, hx, heig, hnonneg⟩ :=
    exists_nonnegative_topEigenvector hn hkL hLn
  have hnormpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  refine ⟨‖x‖⁻¹ • x, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hnormpos)]
    exact inv_mul_cancel₀ (ne_of_gt hnormpos)
  · rw [map_smul, heig]
    exact smul_comm _ _ _
  · intro p
    change 0 ≤ ‖x‖⁻¹ * x p
    exact mul_nonneg (inv_nonneg.mpr hnormpos.le) (hnonneg p)

theorem matrix_adjacent_pos {n k L : ℕ}
    (hn : 0 < n) (hkL : k ≤ L) (hLn : L + k ≤ n)
    (p q : Index k L)
    (hadjacent : p.val + 1 = q.val ∨ q.val + 1 = p.val) :
    0 < matrix n k L p q := by
  have hp := p.isLt
  have hq := q.isLt
  rcases hadjacent with hforward | hbackward
  · have hnot : q.val + 1 ≠ p.val := by omega
    simpa only [matrix, hammingJacobiMatrix, hforward, ↓reduceIte, gt_iff_lt] using
      MetricCodes.hammingJacobiEntry_pos hn (show k ≤ k + p.val by omega) (show k + p.val + k <
        n by omega)
  · have hnot : p.val + 1 ≠ q.val := by omega
    simpa only [matrix, hammingJacobiMatrix, hnot, ↓reduceIte, hbackward, gt_iff_lt] using
      MetricCodes.hammingJacobiEntry_pos hn (show k ≤ k + q.val by omega) (show k + q.val + k <
        n by omega)

theorem nonnegative_eigenvector_zero_propagates {n k L : ℕ}
    (hn : 0 < n) (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : Space k L) (eigenvalue : ℝ)
    (heigen : operator n k L v = eigenvalue • v)
    (hnonnegative : ∀ i : Index k L, 0 ≤ v i)
    (p q : Index k L)
    (hp : v p = 0)
    (hadjacent : p.val + 1 = q.val ∨ q.val + 1 = p.val) :
    v q = 0 := by
  classical
  have hcoordinate := congrArg (fun z : Space k L => z p) heigen
  change
    (∑ i : Index k L, matrix n k L p i * v i) =
      eigenvalue * v p at hcoordinate
  rw [hp, mul_zero] at hcoordinate
  have hterms :
      ∀ i ∈ (Finset.univ : Finset (Index k L)),
        0 ≤ matrix n k L p i * v i := by
    intro i _
    exact mul_nonneg
      (matrix_entry_nonneg hn hkL hLn p i)
      (hnonnegative i)
  have hterm : matrix n k L p q * v q = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hcoordinate
      q (Finset.mem_univ q)
  exact (mul_eq_zero.mp hterm).resolve_left
    (matrix_adjacent_pos hn hkL hLn p q hadjacent).ne'

theorem nonnegative_eigenvector_coordinate_pos {n k L : ℕ}
    (hn : 0 < n) (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : Space k L) (eigenvalue : ℝ)
    (heigen : operator n k L v = eigenvalue • v)
    (hnonnegative : ∀ i : Index k L, 0 ≤ v i)
    (hnonzero : v ≠ 0)
    (i : Index k L) :
    0 < v i := by
  rcases (hnonnegative i).eq_or_lt with hzero | hpositive
  · exfalso
    apply hnonzero
    apply PiLp.ext
    intro q
    change v q = 0
    have hchain :
        ∀ distance : ℕ,
          ∀ q : Index k L,
            Nat.dist i.val q.val = distance → v q = 0 := by
      intro distance
      induction distance using Nat.strong_induction_on with
      | h distance ih =>
          intro q hdistance
          by_cases hequal : i.val = q.val
          · have hiq : i = q := Fin.ext hequal
            simpa only [hiq] using hzero.symm
          · by_cases hforward : i.val < q.val
            · let previous : Index k L :=
                ⟨q.val - 1, by have hq := q.isLt; omega⟩
              have hprevious_distance :
                  Nat.dist i.val previous.val < distance := by
                rw [Nat.dist_eq_sub_of_le
                  (show i.val ≤ previous.val by
                    dsimp [previous]
                    omega)]
                rw [Nat.dist_eq_sub_of_le
                  (Nat.le_of_lt hforward)] at hdistance
                dsimp [previous]
                omega
              have hprevious_zero : v previous = 0 :=
                ih (Nat.dist i.val previous.val)
                  hprevious_distance previous rfl
              exact nonnegative_eigenvector_zero_propagates
                hn hkL hLn v eigenvalue heigen hnonnegative previous q
                hprevious_zero (Or.inl (by
                  dsimp [previous]
                  omega))
            · have hbackward : q.val < i.val := by omega
              let next : Index k L :=
                ⟨q.val + 1, by have hi := i.isLt; omega⟩
              have hnext_distance :
                  Nat.dist i.val next.val < distance := by
                rw [Nat.dist_eq_sub_of_le_right
                  (show next.val ≤ i.val by
                    dsimp [next]
                    omega)]
                rw [Nat.dist_eq_sub_of_le_right
                  (Nat.le_of_lt hbackward)] at hdistance
                dsimp [next]
                omega
              have hnext_zero : v next = 0 :=
                ih (Nat.dist i.val next.val)
                  hnext_distance next rfl
              exact nonnegative_eigenvector_zero_propagates
                hn hkL hLn v eigenvalue heigen hnonnegative next q
                hnext_zero (Or.inr (by
                  dsimp [next]))
    exact hchain (Nat.dist i.val q.val) q rfl
  · exact hpositive

theorem nonnegative_eigenvalue_pos_of_lt {n k L : ℕ}
    (hn : 0 < n) (hkL : k < L) (hLn : L + k ≤ n)
    (v : Space k L) (eigenvalue : ℝ)
    (heigen : operator n k L v = eigenvalue • v)
    (hnonnegative : ∀ i : Index k L, 0 ≤ v i)
    (hnonzero : v ≠ 0) :
    0 < eigenvalue := by
  classical
  let p : Index k L := ⟨0, by omega⟩
  let q : Index k L := ⟨1, by omega⟩
  have hp : 0 < v p :=
    nonnegative_eigenvector_coordinate_pos
      hn hkL.le hLn v eigenvalue heigen hnonnegative hnonzero p
  have hq : 0 < v q :=
    nonnegative_eigenvector_coordinate_pos
      hn hkL.le hLn v eigenvalue heigen hnonnegative hnonzero q
  have hentry : 0 < matrix n k L p q := by
    apply matrix_adjacent_pos hn hkL.le hLn p q
    exact Or.inl (by rfl)
  have hterms :
      ∀ i ∈ (Finset.univ : Finset (Index k L)),
        0 ≤ matrix n k L p i * v i := by
    intro i _
    exact mul_nonneg
      (matrix_entry_nonneg hn hkL.le hLn p i)
      (hnonnegative i)
  have hsum :
      0 < ∑ i : Index k L, matrix n k L p i * v i := by
    apply Finset.sum_pos' hterms
    exact ⟨q, Finset.mem_univ q, mul_pos hentry hq⟩
  have hcoordinate := congrArg (fun z : Space k L => z p) heigen
  change
    (∑ i : Index k L, matrix n k L p i * v i) =
      eigenvalue * v p at hcoordinate
  rw [hcoordinate] at hsum
  exact (mul_pos_iff_of_pos_right hp).mp hsum

theorem exists_positive_unit_topEigenvector {n k L : ℕ}
    (hn : 0 < n) (hkL : k ≤ L) (hLn : L + k ≤ n) :
    ∃ v : Space k L,
      ‖v‖ = 1 ∧
        operator n k L v = topEigenvalue n k L • v ∧
        ∀ i : Index k L, 0 < v i := by
  obtain ⟨v, hunit, heigen, hnonnegative⟩ :=
    exists_nonnegative_unit_topEigenvector hn hkL hLn
  have hnonzero : v ≠ 0 := by
    intro hzero
    simp only [hzero, norm_zero, zero_ne_one] at hunit
  refine ⟨v, hunit, heigen, ?_⟩
  exact fun i => nonnegative_eigenvector_coordinate_pos
    hn hkL hLn v (topEigenvalue n k L)
      heigen hnonnegative hnonzero i

theorem topEigenvalue_pos {n k L : ℕ}
    (hn : 0 < n) (hkL : k < L) (hLn : L + k ≤ n) :
    0 < topEigenvalue n k L := by
  obtain ⟨v, hunit, heigen, hnonnegative⟩ :=
    exists_nonnegative_unit_topEigenvector hn hkL.le hLn
  have hnonzero : v ≠ 0 := by
    intro hzero
    simp only [hzero, norm_zero, zero_ne_one] at hunit
  exact nonnegative_eigenvalue_pos_of_lt hn hkL hLn
    v (topEigenvalue n k L) heigen hnonnegative hnonzero

theorem finite_bound_of_projection_gram
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n k L d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (C : Finset (BinaryWord n)) (hC : MetricCodes.IsBinaryCode d C)
    (P : MetricCodes.ProjectionFamily (BinaryWord n)
      (ambientDimension n k L) (MetricCodes.hammingFibreDimension n k))
    (q : BinaryWord n → E)
    (hrank : 0 < MetricCodes.hammingFibreDimension n k)
    (hgap : threshold n d < topEigenvalue n k L)
    (hgram : ∀ x ∈ C, ∀ y ∈ C,
      ⟪q x, q y⟫_ℝ =
        (MetricCodes.hammingCorrelation x y - topEigenvalue n k L) *
          P.overlap x y) :
    (C.card : ℝ) ≤
      ((1 - threshold n d) /
        (topEigenvalue n k L - threshold n d)) *
        ((ambientDimension n k L : ℝ) /
          (MetricCodes.hammingFibreDimension n k : ℝ)) := by
  refine MetricCodes.projection_certificate P C MetricCodes.hammingCorrelation q
    hrank (threshold_lt_one hn hd) hgap
    (fun x _ => MetricCodes.hammingCorrelation_self x) ?_ hgram
  intro x hx y hy hxy
  exact MetricCodes.hammingCorrelation_le_of_dist_le hn (hC hx hy hxy)

theorem finite_codeNumber_bound_of_projection_gram
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n k L d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (P : MetricCodes.ProjectionFamily (BinaryWord n)
      (ambientDimension n k L) (MetricCodes.hammingFibreDimension n k))
    (q : BinaryWord n → E)
    (hrank : 0 < MetricCodes.hammingFibreDimension n k)
    (hgap : threshold n d < topEigenvalue n k L)
    (hgram : ∀ x y : BinaryWord n,
      ⟪q x, q y⟫_ℝ =
        (MetricCodes.hammingCorrelation x y - topEigenvalue n k L) *
          P.overlap x y) :
    (codeNumber n d : ℝ) ≤
      ((1 - threshold n d) /
        (topEigenvalue n k L - threshold n d)) *
        ((ambientDimension n k L : ℝ) /
          (MetricCodes.hammingFibreDimension n k : ℝ)) := by
  apply codeNumber_real_le_of_forall
  intro C hC
  apply finite_bound_of_projection_gram hn hd C hC P q hrank hgap
  intro x hx y hy
  exact hgram x y

theorem binaryEntropy_eq_binEntropy_div_log (u : ℝ) :
    MetricCodes.binaryEntropy u = Real.binEntropy u / Real.log 2 := by
  simp only [MetricCodes.binaryEntropy, Real.logb, Real.binEntropy, Real.log_inv]
  ring

theorem binaryEntropy_le_one (u : ℝ) :
    MetricCodes.binaryEntropy u ≤ 1 := by
  rw [binaryEntropy_eq_binEntropy_div_log]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (div_le_iff₀ hlog).2
  simpa only [one_mul] using (Real.binEntropy_le_log_two (p := u))

theorem binaryEntropy_continuous : Continuous MetricCodes.binaryEntropy := by
  have hfun : MetricCodes.binaryEntropy =
      (fun u : ℝ => Real.binEntropy u / Real.log 2) :=
    funext binaryEntropy_eq_binEntropy_div_log
  rw [hfun]
  exact Real.binEntropy_continuous.div_const (Real.log 2)

/-- The feasible used in the binary-code argument. -/
def Feasible (δ a b : ℝ) : Prop :=
  0 ≤ b ∧ b < a ∧ a ≤ (1 : ℝ) / 2 ∧
    1 - 2 * δ < MetricCodes.hammingGamma a b

/-- The rate set used in the binary-code argument. -/
def rateSet (δ : ℝ) : Set ℝ :=
  {r | ∃ a b : ℝ, Feasible δ a b ∧
    r = MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b}

/-- The variational rate used in the binary-code argument. -/
def variationalRate (δ : ℝ) : ℝ := sInf (rateSet δ)

theorem rateSet_bddBelow (δ : ℝ) : BddBelow (rateSet δ) := by
  refine ⟨-1, ?_⟩
  rintro r ⟨a, b, hfeasible, rfl⟩
  obtain ⟨hb, hba, ha, hgamma⟩ := hfeasible
  have ha0 : 0 ≤ a := (lt_of_le_of_lt hb hba).le
  have ha1 : a ≤ 1 := by linarith
  have hapos := MetricCodes.binaryEntropy_nonneg ha0 ha1
  have hble := binaryEntropy_le_one b
  linarith

theorem variationalRate_le_of_feasible {δ a b : ℝ}
    (h : Feasible δ a b) :
    variationalRate δ ≤ MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b := by
  exact csInf_le (rateSet_bddBelow δ) ⟨a, b, h, rfl⟩

/-- The classical parameter used in the binary-code argument. -/
def classicalParameter (δ : ℝ) : ℝ :=
  (1 : ℝ) / 2 - Real.sqrt (δ * (1 - δ))

/-- The classical rate used in the binary-code argument. -/
def classicalRate (δ : ℝ) : ℝ :=
  MetricCodes.binaryEntropy (classicalParameter δ)

theorem classicalParameter_lt_half {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2) :
    classicalParameter δ < (1 : ℝ) / 2 := by
  have hrad : 0 < δ * (1 - δ) := mul_pos hδ (by linarith)
  unfold classicalParameter
  have hsqrt := Real.sqrt_pos.2 hrad
  linarith

theorem classicalParameter_pos {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2) :
    0 < classicalParameter δ := by
  have hsquare : 0 < (δ - (1 : ℝ) / 2) ^ 2 :=
    sq_pos_of_ne_zero (by linarith)
  have hrad : 0 < δ * (1 - δ) := mul_pos hδ (by linarith)
  have hrad_lt : δ * (1 - δ) < ((1 : ℝ) / 2) ^ 2 := by
    nlinarith
  have hroot : Real.sqrt (δ * (1 - δ)) < (1 : ℝ) / 2 := by
    exact (Real.sqrt_lt' (by norm_num)).2 hrad_lt
  unfold classicalParameter
  linarith

theorem classicalParameter_mul_one_sub {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2) :
    classicalParameter δ * (1 - classicalParameter δ) =
      ((1 : ℝ) / 2 - δ) ^ 2 := by
  have hrad : 0 ≤ δ * (1 - δ) :=
    (mul_pos hδ (by linarith)).le
  have hsqrt := Real.sq_sqrt hrad
  unfold classicalParameter
  nlinarith

theorem hammingGamma_zero {a : ℝ} (ha : 0 < a) (ha' : a < 1) :
    MetricCodes.hammingGamma a 0 = 2 * Real.sqrt (a * (1 - a)) := by
  have hrad : 0 < a * (1 - a) := mul_pos ha (sub_pos.mpr ha')
  have hsqrt : Real.sqrt (a * (1 - a)) ≠ 0 :=
    (Real.sqrt_pos.2 hrad).ne'
  have hsquare := Real.sq_sqrt hrad.le
  unfold MetricCodes.hammingGamma
  simp only [sub_zero]
  field_simp [hsqrt]
  nlinarith

theorem hammingGamma_classicalParameter {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2) :
    MetricCodes.hammingGamma (classicalParameter δ) 0 = 1 - 2 * δ := by
  have ha := classicalParameter_pos hδ hδ'
  have ha' : classicalParameter δ < 1 :=
    (classicalParameter_lt_half hδ hδ').trans (by norm_num)
  rw [hammingGamma_zero ha ha',
    classicalParameter_mul_one_sub hδ hδ',
    Real.sqrt_sq (by linarith : 0 ≤ (1 : ℝ) / 2 - δ)]
  ring

private def improvementSlope (a : ℝ) : ℝ :=
  2 / (1 - 2 * a) + 1

private def improvementPath (a b : ℝ) : ℝ :=
  a + improvementSlope a * b

theorem improvementSlope_gt_one {a : ℝ} (ha : a < (1 : ℝ) / 2) :
    1 < improvementSlope a := by
  have hden : 0 < 1 - 2 * a := by linarith
  have hfrac : 0 < 2 / (1 - 2 * a) := by positivity
  unfold improvementSlope
  linarith

theorem tendsto_improvementPath_zero (a : ℝ) :
    Tendsto (improvementPath a) (𝓝[>] (0 : ℝ)) (nhds a) := by
  have hcontinuous : Continuous (improvementPath a) := by
    unfold improvementPath
    fun_prop
  simpa only [improvementPath, mul_zero, add_zero] using
    (hcontinuous.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds

private def spectralMarginPolynomial (a c b : ℝ) : ℝ :=
  let r := a * (1 - a)
  let p := c * (1 - 2 * a) - 1
  let q := c ^ 2 - 1
  r * (c * (1 - 2 * a) - 2) +
    b * (p ^ 2 + r * (2 - c ^ 2)) -
      2 * b ^ 2 * p * q + b ^ 3 * q ^ 2

theorem spectralMarginPolynomial_factor (a c b : ℝ) :
    ((a + c * b - b) * (1 - (a + c * b) - b)) ^ 2 -
      (a * (1 - a)) * ((a + c * b) * (1 - (a + c * b))) =
        b * spectralMarginPolynomial a c b := by
  unfold spectralMarginPolynomial
  ring

theorem spectralMarginPolynomial_continuous (a c : ℝ) :
    Continuous (spectralMarginPolynomial a c) := by
  unfold spectralMarginPolynomial
  fun_prop

theorem spectralMarginPolynomial_improvement_zero {a : ℝ}
    (ha : a < (1 : ℝ) / 2) :
    spectralMarginPolynomial a (improvementSlope a) 0 =
      a * (1 - a) * (1 - 2 * a) := by
  have hden : 1 - 2 * a ≠ 0 := by linarith
  have hden' : 1 - a * 2 ≠ 0 := by
    simpa only [ne_eq, mul_comm] using hden
  unfold spectralMarginPolynomial improvementSlope
  field_simp [hden, hden']
  ; ring

theorem eventually_hammingGamma_improvement {a : ℝ}
    (ha : 0 < a) (ha' : a < (1 : ℝ) / 2) :
    ∀ᶠ b : ℝ in 𝓝[>] 0,
      MetricCodes.hammingGamma a 0 <
        MetricCodes.hammingGamma (improvementPath a b) b := by
  have hzero : 0 < spectralMarginPolynomial a (improvementSlope a) 0 := by
    rw [spectralMarginPolynomial_improvement_zero ha']
    have ha1 : 0 < 1 - a := by linarith
    have hhalf : 0 < 1 - 2 * a := by linarith
    exact mul_pos (mul_pos ha ha1) hhalf
  have hpoly :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        0 < spectralMarginPolynomial a (improvementSlope a) b := by
    have hcontinuous :
        ContinuousAt
          (spectralMarginPolynomial a (improvementSlope a)) 0 :=
      (spectralMarginPolynomial_continuous a (improvementSlope a)).continuousAt
    have hlim := hcontinuous.tendsto
    exact nhdsWithin_le_nhds (hlim.eventually (lt_mem_nhds hzero))
  have hhalf :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        improvementPath a b < (1 : ℝ) / 2 :=
    (tendsto_improvementPath_zero a).eventually (gt_mem_nhds ha')
  have hc : 1 < improvementSlope a := improvementSlope_gt_one ha'
  filter_upwards [hpoly, hhalf, self_mem_nhdsWithin]
    with b hbpoly hbhalf (hb : 0 < b)
  have hbpath : b < improvementPath a b := by
    unfold improvementPath
    nlinarith [mul_pos (sub_pos.mpr hc) hb]
  have hpath : 0 < improvementPath a b := lt_trans hb hbpath
  have hpath1 : improvementPath a b < 1 :=
    hbhalf.trans (by norm_num)
  have htail : 0 < 1 - improvementPath a b - b := by
    linarith
  have hbase : 0 < a * (1 - a) := mul_pos ha (by linarith)
  have hrad : 0 < improvementPath a b * (1 - improvementPath a b) :=
    mul_pos hpath (sub_pos.mpr hpath1)
  have hfactor :
      ((improvementPath a b - b) *
        (1 - improvementPath a b - b)) ^ 2 -
        (a * (1 - a)) *
          (improvementPath a b * (1 - improvementPath a b)) =
        b * spectralMarginPolynomial a (improvementSlope a) b := by
    simpa only [improvementPath] using spectralMarginPolynomial_factor a (improvementSlope a) b
  have hmargin :
      0 < ((improvementPath a b - b) *
        (1 - improvementPath a b - b)) ^ 2 -
        (a * (1 - a)) *
          (improvementPath a b * (1 - improvementPath a b)) := by
    rw [hfactor]
    exact mul_pos hb hbpoly
  have htarget :
      0 < (improvementPath a b - b) *
        (1 - improvementPath a b - b) :=
    mul_pos (sub_pos.mpr hbpath) htail
  have hsquare :
      (Real.sqrt (a * (1 - a)) *
        Real.sqrt (improvementPath a b *
          (1 - improvementPath a b))) ^ 2 =
        (a * (1 - a)) *
          (improvementPath a b * (1 - improvementPath a b)) := by
    rw [mul_pow, Real.sq_sqrt hbase.le, Real.sq_sqrt hrad.le]
  have hroot :
      Real.sqrt (a * (1 - a)) *
          Real.sqrt (improvementPath a b *
            (1 - improvementPath a b)) <
        (improvementPath a b - b) *
          (1 - improvementPath a b - b) := by
    have hnonneg :
        0 ≤ Real.sqrt (a * (1 - a)) *
          Real.sqrt (improvementPath a b *
            (1 - improvementPath a b)) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith
  have hquot :
      Real.sqrt (a * (1 - a)) <
        ((improvementPath a b - b) *
          (1 - improvementPath a b - b)) /
            Real.sqrt
              (improvementPath a b * (1 - improvementPath a b)) :=
    (lt_div_iff₀ (Real.sqrt_pos.2 hrad)).2 hroot
  rw [hammingGamma_zero ha (by linarith)]
  unfold MetricCodes.hammingGamma
  calc
    2 * Real.sqrt (a * (1 - a)) <
        2 * (((improvementPath a b - b) *
          (1 - improvementPath a b - b)) /
            Real.sqrt
              (improvementPath a b * (1 - improvementPath a b))) :=
      mul_lt_mul_of_pos_left hquot (by norm_num)
    _ = 2 * (improvementPath a b - b) *
        (1 - improvementPath a b - b) /
          Real.sqrt
            (improvementPath a b * (1 - improvementPath a b)) := by ring

theorem differentiableAt_binaryEntropy {a : ℝ}
    (ha : 0 < a) (ha' : a < 1) :
    DifferentiableAt ℝ MetricCodes.binaryEntropy a := by
  have hfun : MetricCodes.binaryEntropy =
      (fun u : ℝ => Real.binEntropy u / Real.log 2) :=
    funext binaryEntropy_eq_binEntropy_div_log
  rw [hfun]
  exact
    (Real.differentiableAt_binEntropy ha.ne' (ne_of_lt ha')).div_const
      (Real.log 2)

theorem neg_mul_logb_le_binaryEntropy {b : ℝ}
    (hb : 0 ≤ b) (hb' : b ≤ 1) :
    b * (-Real.logb 2 b) ≤ MetricCodes.binaryEntropy b := by
  have hlog : Real.logb 2 (1 - b) ≤ 0 :=
    Real.logb_nonpos (by norm_num) (by linarith) (by linarith)
  have hterm : (1 - b) * Real.logb 2 (1 - b) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) hlog
  unfold MetricCodes.binaryEntropy
  nlinarith

theorem eventually_binaryEntropy_improvement {a : ℝ}
    (ha : 0 < a) (ha' : a < (1 : ℝ) / 2) :
    ∀ᶠ b : ℝ in 𝓝[>] 0,
      MetricCodes.binaryEntropy (improvementPath a b) -
        MetricCodes.binaryEntropy b < MetricCodes.binaryEntropy a := by
  let f : ℝ → ℝ := fun b =>
    MetricCodes.binaryEntropy (improvementPath a b)
  have hinner : DifferentiableAt ℝ (improvementPath a) 0 := by
    unfold improvementPath
    fun_prop
  have houter :
      DifferentiableAt ℝ MetricCodes.binaryEntropy (improvementPath a 0) := by
    simpa only [improvementPath, mul_zero, add_zero] using
      differentiableAt_binaryEntropy ha (ha'.trans (by norm_num))
  have hf : DifferentiableAt ℝ f 0 :=
    houter.comp 0 hinner
  let M : ℝ := deriv f 0 + 1
  have hM : deriv f 0 < M := by
    dsimp [M]
    linarith
  have hslope := hf.hasDerivAt.tendsto_slope_zero_right
  have hupper :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        b⁻¹ * (MetricCodes.binaryEntropy (improvementPath a b) -
          MetricCodes.binaryEntropy a) < M := by
    have h := hslope.eventually (gt_mem_nhds hM)
    filter_upwards [h] with b hb
    simpa [f, improvementPath, smul_eq_mul] using hb
  have hloglim :
      Tendsto (fun b : ℝ => -Real.logb 2 b) (𝓝[>] 0) atTop := by
    simpa only [tendsto_neg_atTop_iff, Function.comp_def] using
      tendsto_neg_atBot_atTop.comp (Real.tendsto_logb_nhdsGT_zero (by norm_num : (1 : ℝ) < 2))
  have hlog :
      ∀ᶠ b : ℝ in 𝓝[>] 0, M < -Real.logb 2 b :=
    hloglim.eventually (eventually_gt_atTop M)
  have hsmall : ∀ᶠ b : ℝ in 𝓝[>] 0, b < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hupper, hlog, hsmall, self_mem_nhdsWithin]
    with b hbound hlogb hb1 (hb : 0 < b)
  have houter_bound :
      MetricCodes.binaryEntropy (improvementPath a b) -
        MetricCodes.binaryEntropy a < b * M := by
    calc
      MetricCodes.binaryEntropy (improvementPath a b) -
          MetricCodes.binaryEntropy a =
        b * (b⁻¹ * (MetricCodes.binaryEntropy (improvementPath a b) -
          MetricCodes.binaryEntropy a)) := by
            field_simp [hb.ne']
      _ < b * M := mul_lt_mul_of_pos_left hbound hb
  have hsingular :
      b * M < b * (-Real.logb 2 b) :=
    mul_lt_mul_of_pos_left hlogb hb
  have hentropy := neg_mul_logb_le_binaryEntropy hb.le hb1.le
  linarith

theorem exists_strict_improving_feasible {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2) :
    ∃ a b : ℝ, Feasible δ a b ∧
      MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b < classicalRate δ := by
  let a₀ : ℝ := classicalParameter δ
  have ha₀ : 0 < a₀ := classicalParameter_pos hδ hδ'
  have ha₀half : a₀ < (1 : ℝ) / 2 :=
    classicalParameter_lt_half hδ hδ'
  have hgamma := eventually_hammingGamma_improvement ha₀ ha₀half
  have hentropy := eventually_binaryEntropy_improvement ha₀ ha₀half
  have hhalf :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        improvementPath a₀ b < (1 : ℝ) / 2 :=
    (tendsto_improvementPath_zero a₀).eventually
      (gt_mem_nhds ha₀half)
  have hc : 1 < improvementSlope a₀ :=
    improvementSlope_gt_one ha₀half
  have hall :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        Feasible δ (improvementPath a₀ b) b ∧
          MetricCodes.binaryEntropy (improvementPath a₀ b) -
            MetricCodes.binaryEntropy b < classicalRate δ := by
    filter_upwards [hgamma, hentropy, hhalf, self_mem_nhdsWithin]
      with b hgamma' hentropy' hhalf' (hb : 0 < b)
    have hbpath : b < improvementPath a₀ b := by
      unfold improvementPath
      nlinarith [mul_pos (sub_pos.mpr hc) hb]
    constructor
    · refine ⟨hb.le, hbpath, hhalf'.le, ?_⟩
      have hboundary : MetricCodes.hammingGamma a₀ 0 = 1 - 2 * δ := by
        dsimp [a₀]
        exact hammingGamma_classicalParameter hδ hδ'
      rwa [hboundary] at hgamma'
    · simpa only [classicalRate] using hentropy'
  obtain ⟨b, hb⟩ := hall.exists
  exact ⟨improvementPath a₀ b, b, hb⟩

theorem variationalRate_lt_classicalRate {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2) :
    variationalRate δ < classicalRate δ := by
  obtain ⟨a, b, hfeasible, himprove⟩ :=
    exists_strict_improving_feasible hδ hδ'
  exact (variationalRate_le_of_feasible hfeasible).trans_lt himprove

/-- The longitudinal degree used in the binary-code argument. -/
def longitudinalDegree (a : ℝ) (n : ℕ) : ℕ :=
  Nat.floor (a * (n : ℝ))

/-- The transverse degree used in the binary-code argument. -/
def transverseDegree (b : ℝ) (n : ℕ) : ℕ :=
  Nat.floor (b * (n : ℝ))

theorem tendsto_longitudinal_ratio {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (longitudinalDegree a n : ℝ) / (n : ℝ))
      atTop (nhds a) := by
  simpa only [longitudinalDegree, Function.comp_def] using
    (tendsto_nat_floor_mul_div_atTop ha).comp (tendsto_natCast_atTop_atTop (R := ℝ))

theorem tendsto_transverse_ratio {b : ℝ} (hb : 0 ≤ b) :
    Tendsto (fun n : ℕ => (transverseDegree b n : ℝ) / (n : ℝ))
      atTop (nhds b) := by
  simpa only [transverseDegree, Function.comp_def] using
    (tendsto_nat_floor_mul_div_atTop hb).comp (tendsto_natCast_atTop_atTop (R := ℝ))

theorem tendsto_terminal_degree_ratio {a : ℝ}
    (ha : 0 < a) (r : ℕ) :
    Tendsto
      (fun n : ℕ => ((longitudinalDegree a n - r : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds a) := by
  have hoffset := tendsto_const_div_atTop_nhds_zero_nat (r : ℝ)
  have hmain := (tendsto_longitudinal_ratio ha.le).sub hoffset
  rw [sub_zero] at hmain
  have hgrowth : Tendsto (longitudinalDegree a) atTop atTop := by
    change Tendsto (fun n : ℕ => Nat.floor (a * (n : ℝ))) atTop atTop
    exact tendsto_nat_floor_mul_atTop a ha
  refine hmain.congr' ?_
  filter_upwards [hgrowth.eventually (eventually_ge_atTop r)] with n hn
  rw [Nat.cast_sub hn]
  ring

/-- The normalized coefficient used in the binary-code argument. -/
def normalizedCoefficient (x y z : ℝ) : ℝ :=
  ((x - y + z) * (1 - x - y)) /
    Real.sqrt ((x + z) * (1 - x))

theorem hammingJacobiEntry_eq_normalized
    (n k i : ℕ) (hn : 0 < n) :
    MetricCodes.hammingJacobiEntry n k i =
      normalizedCoefficient
        ((i : ℝ) / (n : ℝ))
        ((k : ℝ) / (n : ℝ))
        ((1 : ℝ) / (n : ℝ)) := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := hnreal.ne'
  have hrad :
      (((i : ℝ) + 1) * ((n : ℝ) - (i : ℝ))) =
        (n : ℝ) ^ 2 *
          (((i : ℝ) / (n : ℝ) + (1 : ℝ) / (n : ℝ)) *
            (1 - (i : ℝ) / (n : ℝ))) := by
    field_simp [hnne]
  unfold MetricCodes.hammingJacobiEntry normalizedCoefficient
  rw [hrad, Real.sqrt_mul (sq_nonneg (n : ℝ)),
    Real.sqrt_sq hnreal.le]
  field_simp [hnne]

theorem normalizedCoefficient_zero (a b : ℝ) :
    normalizedCoefficient a b 0 = MetricCodes.hammingGamma a b / 2 := by
  unfold normalizedCoefficient MetricCodes.hammingGamma
  simp only [add_zero]
  ring

theorem tendsto_terminal_coefficient {a b : ℝ}
    (ha : 0 < a) (ha' : a < 1) (hb : 0 ≤ b) (r : ℕ) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.hammingJacobiEntry n (transverseDegree b n)
          (longitudinalDegree a n - r))
      atTop (nhds (MetricCodes.hammingGamma a b / 2)) := by
  have hx := tendsto_terminal_degree_ratio ha r
  have hy := tendsto_transverse_ratio hb
  have hz := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hnum := ((hx.sub hy).add hz).mul ((hone.sub hx).sub hy)
  have hrad := (hx.add hz).mul (hone.sub hx)
  have hroot := hrad.sqrt
  have hrootne : Real.sqrt (a * (1 - a)) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos ha (sub_pos.mpr ha'))).ne'
  have pointwise_div {f g : ℕ → ℝ} {l : ℝ}
      (h : Tendsto (f / g) atTop (nhds l)) :
      Tendsto (fun n => f n / g n) atTop (nhds l) :=
    h.congr' (Filter.Eventually.of_forall (fun _ => rfl))
  have hnorm :
      Tendsto
        (fun n : ℕ => normalizedCoefficient
          (((longitudinalDegree a n - r : ℕ) : ℝ) / (n : ℝ))
          ((transverseDegree b n : ℝ) / (n : ℝ))
          ((1 : ℝ) / (n : ℝ)))
        atTop (nhds (normalizedCoefficient a b 0)) := by
    simpa only [normalizedCoefficient, one_div, add_zero] using
      pointwise_div (hnum.div hroot (by simpa using hrootne))
  rw [normalizedCoefficient_zero] at hnorm
  refine hnorm.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (hammingJacobiEntry_eq_normalized n
    (transverseDegree b n) (longitudinalDegree a n - r) hn).symm

theorem tridiagonal_quadratic_sum
    (d : ℕ) (c v : ℕ → ℝ) :
    (∑ p ∈ Finset.range (d + 1),
      ∑ q ∈ Finset.range (d + 1),
        (if p + 1 = q then c p
          else if q + 1 = p then c q else 0) * v q * v p) =
      2 * ∑ p ∈ Finset.range d, c p * v p * v (p + 1) := by
  have hpoint (p q : ℕ) :
      (if p + 1 = q then c p
        else if q + 1 = p then c q else 0) * v q * v p =
        (if p + 1 = q then c p * v q * v p else 0) +
        (if q + 1 = p then c q * v q * v p else 0) := by
    by_cases h₁ : p + 1 = q
    · have h₂ : ¬ q + 1 = p := by omega
      simp only [h₁, ↓reduceIte, h₂, add_zero]
    · by_cases h₂ : q + 1 = p
      · simp only [h₁, ↓reduceIte, h₂, zero_add]
      · simp only [h₁, ↓reduceIte, h₂, zero_mul, add_zero]
  have hupper :
      (∑ p ∈ Finset.range (d + 1),
        ∑ q ∈ Finset.range (d + 1),
          if p + 1 = q then c p * v q * v p else 0) =
        ∑ p ∈ Finset.range d, c p * v p * v (p + 1) := by
    simp only [Finset.sum_ite_eq, Finset.mem_range]
    rw [Finset.sum_range_succ]
    simp only [lt_self_iff_false, ite_false, add_zero]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' : p < d := Finset.mem_range.mp hp
    simp only [Order.lt_add_one_iff, Order.add_one_le_iff, hp', ↓reduceIte, mul_comm, mul_left_comm,
      mul_assoc]
  have hlower :
      (∑ p ∈ Finset.range (d + 1),
        ∑ q ∈ Finset.range (d + 1),
          if q + 1 = p then c q * v q * v p else 0) =
        ∑ p ∈ Finset.range d, c p * v p * v (p + 1) := by
    rw [Finset.sum_comm]
    calc
      (∑ q ∈ Finset.range (d + 1),
        ∑ p ∈ Finset.range (d + 1),
          if q + 1 = p then c q * v q * v p else 0) =
        ∑ q ∈ Finset.range (d + 1),
          ∑ p ∈ Finset.range (d + 1),
            if q + 1 = p then c q * v p * v q else 0 := by
              apply Finset.sum_congr rfl
              intro q hq
              apply Finset.sum_congr rfl
              intro p hp
              split_ifs <;> ring
      _ = _ := hupper
  calc
    (∑ p ∈ Finset.range (d + 1),
      ∑ q ∈ Finset.range (d + 1),
        (if p + 1 = q then c p
          else if q + 1 = p then c q else 0) * v q * v p) =
        ∑ p ∈ Finset.range (d + 1),
          ∑ q ∈ Finset.range (d + 1),
            ((if p + 1 = q then c p * v q * v p else 0) +
             (if q + 1 = p then c q * v q * v p else 0)) := by
              apply Finset.sum_congr rfl
              intro p hp
              apply Finset.sum_congr rfl
              intro q hq
              exact hpoint p q
    _ =
        (∑ p ∈ Finset.range (d + 1),
          ∑ q ∈ Finset.range (d + 1),
            if p + 1 = q then c p * v q * v p else 0) +
        (∑ p ∈ Finset.range (d + 1),
          ∑ q ∈ Finset.range (d + 1),
            if q + 1 = p then c q * v q * v p else 0) := by
              simp_rw [Finset.sum_add_distrib]
    _ = 2 * ∑ p ∈ Finset.range d, c p * v p * v (p + 1) := by
      rw [hupper, hlower]
      ring

/-- The terminal indicator used in the binary-code argument. -/
def terminalIndicator (d m p : ℕ) : ℝ :=
  if d - m ≤ p then 1 else 0

theorem terminal_indicator_sum (d m : ℕ) (hm : m ≤ d) :
    (∑ p ∈ Finset.range (d + 1), terminalIndicator d m p) =
      (m : ℝ) + 1 := by
  have hsplit : d + 1 = (d - m) + (m + 1) := by omega
  rw [hsplit, Finset.sum_range_add]
  have hfirst :
      (∑ p ∈ Finset.range (d - m), terminalIndicator d m p) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hp' : p < d - m := Finset.mem_range.mp hp
    simp only [terminalIndicator, Nat.not_le.mpr hp', ↓reduceIte]
  rw [hfirst, zero_add]
  calc
    (∑ p ∈ Finset.range (m + 1),
      terminalIndicator d m (d - m + p)) =
        ∑ _p ∈ Finset.range (m + 1), (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro p hp
          simp only [terminalIndicator, le_add_iff_nonneg_right, zero_le, ↓reduceIte]
    _ = (m : ℝ) + 1 := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
                            Nat.cast_add, Nat.cast_one, mul_one]

theorem terminal_indicator_edge_sum
    (d m : ℕ) (hm : m ≤ d) (c : ℕ → ℝ) :
    (∑ p ∈ Finset.range d,
      c p * terminalIndicator d m p *
        terminalIndicator d m (p + 1)) =
      ∑ r ∈ Finset.range m, c (d - m + r) := by
  have hsplit : d = (d - m) + m := by omega
  rw [hsplit, Finset.sum_range_add]
  simp only [← hsplit]
  have hfirst :
      (∑ p ∈ Finset.range (d - m),
        c p * terminalIndicator d m p *
          terminalIndicator d m (p + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hp' : p < d - m := Finset.mem_range.mp hp
    simp only [terminalIndicator, Nat.not_le.mpr hp', ↓reduceIte, mul_zero, tsub_le_iff_right,
      mul_ite, mul_one, ite_self]
  rw [hfirst, zero_add]
  apply Finset.sum_congr rfl
  intro p hp
  have h₁ : d - m ≤ d - m + p := by omega
  have h₂ : d - m ≤ d - m + p + 1 := by omega
  simp only [terminalIndicator, ite_eq_left h₁, ite_eq_left h₂, mul_one]

/-- The terminal vector used in the binary-code argument. -/
def terminalVector (k L m : ℕ) : Space k L :=
  WithLp.toLp 2
    (fun p : Fin (L - k + 1) => terminalIndicator (L - k) m p.val)

theorem terminalVector_last (k L m : ℕ) :
    terminalVector k L m (Fin.last (L - k)) = 1 := by
  change (if L - k - m ≤ L - k then (1 : ℝ) else 0) = 1
  simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le, ↓reduceIte]

theorem terminalVector_ne_zero (k L m : ℕ) :
    terminalVector k L m ≠ 0 := by
  intro h
  have hx := congrArg
    (fun x : Space k L => x (Fin.last (L - k))) h
  simp only [terminalVector_last, PiLp.zero_apply, one_ne_zero] at hx

theorem terminalVector_norm_sq
    (k L m : ℕ) (hm : m ≤ L - k) :
    ‖terminalVector k L m‖ ^ 2 = (m : ℝ) + 1 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change
    (∑ p : Fin (L - k + 1),
      terminalIndicator (L - k) m p.val ^ 2) = (m : ℝ) + 1
  have hsq (p : ℕ) :
      terminalIndicator (L - k) m p ^ 2 =
        terminalIndicator (L - k) m p := by
    simp only [terminalIndicator, tsub_le_iff_right, ite_pow, one_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
  simp_rw [hsq]
  rw [Fin.sum_univ_eq_sum_range]
  exact terminal_indicator_sum (L - k) m hm

theorem terminalVector_inner
    (n k L m : ℕ) (hkl : k ≤ L) (hm : m ≤ L - k) :
    @inner ℝ (Space k L) _
        (operator n k L (terminalVector k L m))
        (terminalVector k L m) =
      2 * ∑ r ∈ Finset.range m,
        MetricCodes.hammingJacobiEntry n k (L - m + r) := by
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply]
  change
    (∑ p : Fin (L - k + 1),
      (∑ q : Fin (L - k + 1),
        (if p.val + 1 = q.val then
          MetricCodes.hammingJacobiEntry n k (k + p.val)
        else if q.val + 1 = p.val then
          MetricCodes.hammingJacobiEntry n k (k + q.val)
        else 0) * terminalIndicator (L - k) m q.val) *
        terminalIndicator (L - k) m p.val) =
      2 * ∑ r ∈ Finset.range m,
        MetricCodes.hammingJacobiEntry n k (L - m + r)
  simp_rw [Finset.sum_mul]
  let f : ℕ → ℝ := fun p =>
    ∑ q : Fin (L - k + 1),
      (if p + 1 = q.val then
        MetricCodes.hammingJacobiEntry n k (k + p)
      else if q.val + 1 = p then
        MetricCodes.hammingJacobiEntry n k (k + q.val)
      else 0) * terminalIndicator (L - k) m q.val *
        terminalIndicator (L - k) m p
  change
    (∑ p : Fin (L - k + 1), f p.val) =
      2 * ∑ r ∈ Finset.range m,
        MetricCodes.hammingJacobiEntry n k (L - m + r)
  rw [Fin.sum_univ_eq_sum_range f]
  dsimp only [f]
  have hfin (p : ℕ) :
      (∑ q : Fin (L - k + 1),
        (if p + 1 = q.val then
          MetricCodes.hammingJacobiEntry n k (k + p)
        else if q.val + 1 = p then
          MetricCodes.hammingJacobiEntry n k (k + q.val)
        else 0) * terminalIndicator (L - k) m q.val *
          terminalIndicator (L - k) m p) =
        ∑ q ∈ Finset.range (L - k + 1),
          (if p + 1 = q then
            MetricCodes.hammingJacobiEntry n k (k + p)
          else if q + 1 = p then
            MetricCodes.hammingJacobiEntry n k (k + q)
          else 0) * terminalIndicator (L - k) m q *
            terminalIndicator (L - k) m p := by
    let g : ℕ → ℝ := fun q =>
      (if p + 1 = q then
        MetricCodes.hammingJacobiEntry n k (k + p)
      else if q + 1 = p then
        MetricCodes.hammingJacobiEntry n k (k + q)
      else 0) * terminalIndicator (L - k) m q *
        terminalIndicator (L - k) m p
    change (∑ q : Fin (L - k + 1), g q.val) =
      ∑ q ∈ Finset.range (L - k + 1), g q
    exact Fin.sum_univ_eq_sum_range g (L - k + 1)
  simp_rw [hfin]
  rw [tridiagonal_quadratic_sum]
  rw [terminal_indicator_edge_sum (L - k) m hm]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  omega

theorem terminalVector_rayleigh
    (n k L m : ℕ) (hkl : k ≤ L) (hm : m ≤ L - k) :
    rayleigh n k L (terminalVector k L m) =
      (2 * ∑ r ∈ Finset.range m,
        MetricCodes.hammingJacobiEntry n k (L - m + r)) /
          ((m : ℝ) + 1) := by
  rw [rayleigh_eq_inner,
    terminalVector_inner n k L m hkl hm,
    terminalVector_norm_sq k L m hm]

theorem terminal_edge_sum_le_top
    (n k L m : ℕ) (hkl : k ≤ L) (hm : m ≤ L - k) :
    (2 * ∑ r ∈ Finset.range m,
      MetricCodes.hammingJacobiEntry n k (L - m + r)) /
        ((m : ℝ) + 1) ≤ topEigenvalue n k L := by
  rw [← terminalVector_rayleigh n k L m hkl hm]
  exact rayleigh_le_top n k L
    (terminalVector k L m) (terminalVector_ne_zero k L m)

theorem eventually_transverse_add_le_longitudinal
    {a b : ℝ} (hb : 0 ≤ b) (hba : b < a) (m : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      transverseDegree b n + m ≤ longitudinalDegree a n := by
  let ε : ℝ := (a - b) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hεlt : ε < a - b := by
    dsimp [ε]
    linarith
  have ha : 0 ≤ a := (lt_of_le_of_lt hb hba).le
  have hratio :=
    ((tendsto_longitudinal_ratio ha).sub
      (tendsto_transverse_ratio hb)).eventually
        (lt_mem_nhds hεlt)
  have hgrowth :
      Tendsto (fun n : ℕ => ε * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hε
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge := hgrowth.eventually (eventually_ge_atTop (m : ℝ))
  filter_upwards [hratio, hlarge, eventually_gt_atTop (0 : ℕ)]
    with n hnratio hnlarge hn
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmul := mul_lt_mul_of_pos_right hnratio hnreal
  have hidentity :
      (((longitudinalDegree a n : ℝ) / (n : ℝ) -
        (transverseDegree b n : ℝ) / (n : ℝ)) * (n : ℝ)) =
        (longitudinalDegree a n : ℝ) -
          (transverseDegree b n : ℝ) := by
    field_simp [hnreal.ne']
  rw [hidentity] at hmul
  have hreal :
      (transverseDegree b n : ℝ) + (m : ℝ) ≤
        (longitudinalDegree a n : ℝ) := by
    linarith
  exact_mod_cast hreal

/-- The terminal edge rayleigh used in the binary-code argument. -/
def terminalEdgeRayleigh (a b : ℝ) (m n : ℕ) : ℝ :=
  (2 * ∑ r ∈ Finset.range m,
    MetricCodes.hammingJacobiEntry n (transverseDegree b n)
      (longitudinalDegree a n - (m - r))) /
        ((m : ℝ) + 1)

theorem tendsto_terminalEdgeRayleigh {a b : ℝ}
    (ha : 0 < a) (ha' : a < 1) (hb : 0 ≤ b) (m : ℕ) :
    Tendsto (terminalEdgeRayleigh a b m) atTop
      (nhds
        (((m : ℝ) / ((m : ℝ) + 1)) * MetricCodes.hammingGamma a b)) := by
  have hsum :
      Tendsto
        (fun n : ℕ => ∑ r ∈ Finset.range m,
          MetricCodes.hammingJacobiEntry n (transverseDegree b n)
            (longitudinalDegree a n - (m - r)))
        atTop
        (nhds (∑ _r ∈ Finset.range m,
          MetricCodes.hammingGamma a b / 2)) := by
    apply tendsto_finsetSum
    intro r hr
    exact tendsto_terminal_coefficient ha ha' hb (m - r)
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hquot := (htwo.mul hsum).div_const ((m : ℝ) + 1)
  change Tendsto
    (fun n : ℕ => terminalEdgeRayleigh a b m n) atTop
      (nhds (((m : ℝ) / ((m : ℝ) + 1)) * MetricCodes.hammingGamma a b))
  simpa only [terminalEdgeRayleigh, div_eq_mul_inv, mul_comm, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_left_comm, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel₀,
    mul_one, mul_assoc] using hquot

theorem terminalEdgeRayleigh_le_top
    (a b : ℝ) (m n : ℕ)
    (hfit : transverseDegree b n + m ≤ longitudinalDegree a n) :
    terminalEdgeRayleigh a b m n ≤
      topEigenvalue n (transverseDegree b n) (longitudinalDegree a n) := by
  have hkl : transverseDegree b n ≤ longitudinalDegree a n := by omega
  have hm : m ≤ longitudinalDegree a n - transverseDegree b n := by omega
  have hsum :
      (∑ r ∈ Finset.range m,
        MetricCodes.hammingJacobiEntry n (transverseDegree b n)
          (longitudinalDegree a n - (m - r))) =
        ∑ r ∈ Finset.range m,
          MetricCodes.hammingJacobiEntry n (transverseDegree b n)
            (longitudinalDegree a n - m + r) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hr' : r < m := Finset.mem_range.mp hr
    congr 1
    omega
  unfold terminalEdgeRayleigh
  rw [hsum]
  exact terminal_edge_sum_le_top n
    (transverseDegree b n) (longitudinalDegree a n) m hkl hm

theorem eventually_topEigenvalue_gt {a b s : ℝ}
    (hb : 0 ≤ b) (hba : b < a) (ha : a ≤ (1 : ℝ) / 2)
    (hs : s < MetricCodes.hammingGamma a b) :
    ∀ᶠ n : ℕ in atTop,
      s < topEigenvalue n
        (transverseDegree b n) (longitudinalDegree a n) := by
  have ha0 : 0 < a := lt_of_le_of_lt hb hba
  have ha1 : a < 1 := lt_of_le_of_lt ha (by norm_num)
  have hsecond : 0 < 1 - a - b := by linarith
  have hgamma : 0 < MetricCodes.hammingGamma a b := by
    unfold MetricCodes.hammingGamma
    apply div_pos
    · exact mul_pos (mul_pos (by norm_num) (sub_pos.mpr hba)) hsecond
    · exact Real.sqrt_pos.2 (mul_pos ha0 (sub_pos.mpr ha1))
  let ε : ℝ := (MetricCodes.hammingGamma a b - s) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (MetricCodes.hammingGamma a b / ε)
  have hprod : MetricCodes.hammingGamma a b < (m : ℝ) * ε :=
    (div_lt_iff₀ hε).mp hm
  have hden : 0 < (m : ℝ) + 1 := by positivity
  have hrem : MetricCodes.hammingGamma a b / ((m : ℝ) + 1) < ε := by
    apply (div_lt_iff₀ hden).2
    nlinarith
  have hidentity :
      ((m : ℝ) / ((m : ℝ) + 1)) * MetricCodes.hammingGamma a b =
        MetricCodes.hammingGamma a b -
          MetricCodes.hammingGamma a b / ((m : ℝ) + 1) := by
    field_simp [hden.ne']
    ; ring
  have hbelow :
      s < ((m : ℝ) / ((m : ℝ) + 1)) * MetricCodes.hammingGamma a b := by
    rw [hidentity]
    dsimp [ε] at hrem
    linarith
  have hquot := (tendsto_terminalEdgeRayleigh ha0 ha1 hb m).eventually
    (lt_mem_nhds hbelow)
  filter_upwards [hquot,
    eventually_transverse_add_le_longitudinal hb hba m] with n hn hfit
  exact hn.trans_le (terminalEdgeRayleigh_le_top a b m n hfit)

theorem longitudinalDegree_le_dimension {a : ℝ}
    (ha : a ≤ 1) (n : ℕ) :
    longitudinalDegree a n ≤ n := by
  unfold longitudinalDegree
  apply Nat.floor_le_of_le
  simpa only [one_mul] using mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg n)

theorem complement_longitudinalDegree_floor_le {a : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1) (n : ℕ) :
    longitudinalDegree (1 - a) n ≤ n - longitudinalDegree a n := by
  have hk := longitudinalDegree_le_dimension ha' n
  have hfloor : (longitudinalDegree a n : ℝ) ≤ a * (n : ℝ) := by
    unfold longitudinalDegree
    exact Nat.floor_le (mul_nonneg ha (Nat.cast_nonneg n))
  change Nat.floor ((1 - a) * (n : ℝ)) ≤
    n - longitudinalDegree a n
  apply Nat.floor_le_of_le
  change (1 - a) * (n : ℝ) ≤
    ((n - longitudinalDegree a n : ℕ) : ℝ)
  rw [Nat.cast_sub hk]
  nlinarith

theorem tendsto_complement_longitudinalDegree {a : ℝ}
    (ha : 0 ≤ a) (ha' : a < 1) :
    Tendsto (fun n : ℕ => n - longitudinalDegree a n) atTop atTop := by
  have hcomp : Tendsto (longitudinalDegree (1 - a)) atTop atTop := by
    change Tendsto
      (fun n : ℕ => Nat.floor ((1 - a) * (n : ℝ))) atTop atTop
    exact tendsto_nat_floor_mul_atTop (1 - a) (sub_pos.mpr ha')
  exact tendsto_atTop_mono
    (fun n => complement_longitudinalDegree_floor_le ha ha'.le n)
    hcomp

theorem tendsto_complement_longitudinal_ratio {a : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1) :
    Tendsto
      (fun n : ℕ => ((n - longitudinalDegree a n : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds (1 - a)) := by
  have hone : Tendsto
      (fun n : ℕ => (n : ℝ) / (n : ℝ)) atTop (nhds 1) := by
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    refine hconst.congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    simp only [ne_eq, Nat.cast_eq_zero, hn, not_false_eq_true, div_self]
  have hmain := hone.sub (tendsto_longitudinal_ratio ha)
  refine hmain.congr' (Filter.Eventually.of_forall fun n => ?_)
  change
    (n : ℝ) / (n : ℝ) -
      (longitudinalDegree a n : ℝ) / (n : ℝ) =
        ((n - longitudinalDegree a n : ℕ) : ℝ) / (n : ℝ)
  rw [Nat.cast_sub (longitudinalDegree_le_dimension ha' n)]
  ring

theorem tendsto_log_choose_longitudinal {a : ℝ}
    (ha : 0 < a) (ha' : a < 1) :
    Tendsto
      (fun n : ℕ =>
        Real.log (n.choose (longitudinalDegree a n) : ℝ) / (n : ℝ))
      atTop (nhds (Real.binEntropy a)) := by
  have hgrowth : Tendsto (longitudinalDegree a) atTop atTop := by
    change Tendsto (fun n : ℕ => Nat.floor (a * (n : ℝ))) atTop atTop
    exact tendsto_nat_floor_mul_atTop a ha
  have hcomplement := tendsto_complement_longitudinalDegree ha.le ha'
  have hratio := tendsto_longitudinal_ratio ha.le
  have hcomplementratio :=
    tendsto_complement_longitudinal_ratio ha.le ha'.le
  have hchoose := SpherePacking.tendsto_log_add_choose_div
    (longitudinalDegree a)
    (fun n : ℕ => n - longitudinalDegree a n)
    a (1 - a)
    hgrowth hcomplement hratio hcomplementratio ha (sub_pos.mpr ha')
  have hlimit :
      (a + (1 - a)) * Real.log (a + (1 - a)) -
        a * Real.log a - (1 - a) * Real.log (1 - a) =
        Real.binEntropy a := by
    simp only [add_sub_cancel, Real.log_one, mul_zero, zero_sub, Real.binEntropy, Real.log_inv,
      mul_neg]
    ring
  rw [hlimit] at hchoose
  refine hchoose.congr' (Filter.Eventually.of_forall fun n => ?_)
  have hk := longitudinalDegree_le_dimension ha'.le n
  have hsum :
      longitudinalDegree a n + (n - longitudinalDegree a n) = n := by
    omega
  rw [hsum]

theorem tendsto_logb_choose_longitudinal {a : ℝ}
    (ha : 0 < a) (ha' : a < 1) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2 (n.choose (longitudinalDegree a n) : ℝ) /
          (n : ℝ))
      atTop (nhds (MetricCodes.binaryEntropy a)) := by
  have h := (tendsto_log_choose_longitudinal ha ha').div_const (Real.log 2)
  rw [← binaryEntropy_eq_binEntropy_div_log a] at h
  refine h.congr' (Filter.Eventually.of_forall fun n => ?_)
  unfold Real.logb
  ring

theorem longitudinalDegree_le_half {a : ℝ}
    (ha : a ≤ (1 : ℝ) / 2) (n : ℕ) :
    longitudinalDegree a n ≤ n / 2 := by
  unfold longitudinalDegree
  calc
    Nat.floor (a * (n : ℝ)) ≤ Nat.floor ((n : ℝ) / 2) := by
      apply Nat.floor_mono
      have h := mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg n)
      linarith
    _ = n / 2 := by
      simpa only [Nat.cast_ofNat] using (Nat.floor_div_eq_div (K := ℝ) n 2)

theorem choose_le_ambientDimension (n k L : ℕ) (hkL : k ≤ L) :
    n.choose L ≤ ambientDimension n k L := by
  unfold ambientDimension
  have hindex : L - k ∈ Finset.range (L - k + 1) := by
    simp only [Finset.mem_range, lt_add_iff_pos_right, Order.lt_one_iff]
  have hterm := Finset.single_le_sum
    (s := Finset.range (L - k + 1))
    (f := fun j => n.choose (k + j))
    (fun j _ => Nat.zero_le _) hindex
  have hdegree : k + (L - k) = L := by omega
  simpa only [ge_iff_le, hdegree] using hterm

theorem ambientDimension_le_mul_choose
    (n k L : ℕ) (hkL : k ≤ L) (hL : L ≤ n / 2) :
    ambientDimension n k L ≤ (n + 1) * n.choose L := by
  calc
    ambientDimension n k L =
        ∑ j ∈ Finset.range (L - k + 1), n.choose (k + j) := rfl
    _ ≤ ∑ _j ∈ Finset.range (L - k + 1), n.choose L := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j < L - k + 1 := Finset.mem_range.mp hj
      apply MetricCodes.choose_monotone_to_half n (by omega) hL
    _ = (L - k + 1) * n.choose L := by simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ ≤ (n + 1) * n.choose L := by
      apply Nat.mul_le_mul_right
      omega

theorem choose_le_mul_hammingFibreDimension
    {n k : ℕ} (hk : 2 * k ≤ n) :
    n.choose k ≤ (n + 1) * MetricCodes.hammingFibreDimension n k := by
  cases k with
  | zero => simp only [Nat.choose_zero_right, hammingFibreDimension, booleanHarmonicDimension,
              mul_one, le_add_iff_nonneg_left, zero_le]
  | succ j =>
      change n.choose (j + 1) ≤
        (n + 1) * (n.choose (j + 1) - n.choose j)
      have hpositive :=
        hammingFibreDimension_pos (n := n) (k := j + 1) hk
      change 0 < n.choose (j + 1) - n.choose j at hpositive
      have hmono : n.choose j ≤ n.choose (j + 1) :=
        (Nat.sub_pos_iff_lt.mp hpositive).le
      have hrec :
          (n.choose (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) =
            (n.choose j : ℝ) * ((n - j : ℕ) : ℝ) := by
        exact_mod_cast Nat.choose_succ_right_eq n j
      have hidentity :
          ((n.choose (j + 1) - n.choose j : ℕ) : ℝ) *
              ((n - j : ℕ) : ℝ) =
            (n.choose (j + 1) : ℝ) *
              (((n - j : ℕ) : ℝ) - ((j + 1 : ℕ) : ℝ)) := by
        rw [Nat.cast_sub hmono]
        calc
          ((n.choose (j + 1) : ℝ) - (n.choose j : ℝ)) *
              ((n - j : ℕ) : ℝ) =
            (n.choose (j + 1) : ℝ) * ((n - j : ℕ) : ℝ) -
              (n.choose j : ℝ) * ((n - j : ℕ) : ℝ) := by ring
          _ = (n.choose (j + 1) : ℝ) * ((n - j : ℕ) : ℝ) -
              (n.choose (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
                rw [← hrec]
          _ = (n.choose (j + 1) : ℝ) *
              (((n - j : ℕ) : ℝ) - ((j + 1 : ℕ) : ℝ)) := by ring
      have hfactorNat : j + 2 ≤ n - j := by omega
      have hfactorReal :
          (1 : ℝ) ≤
            ((n - j : ℕ) : ℝ) - ((j + 1 : ℕ) : ℝ) := by
        have hcast : ((j + 2 : ℕ) : ℝ) ≤ ((n - j : ℕ) : ℝ) := by
          exact_mod_cast hfactorNat
        have hcastj : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by
          norm_num
        rw [hcastj]
        push_cast at hcast
        linarith
      have hlower :
          (n.choose (j + 1) : ℝ) ≤
            ((n.choose (j + 1) - n.choose j : ℕ) : ℝ) *
              ((n - j : ℕ) : ℝ) := by
        rw [hidentity]
        nlinarith [Nat.cast_nonneg (α := ℝ) (n.choose (j + 1))]
      have hrange :
          ((n - j : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show n - j ≤ n + 1 by omega)
      have hupper :
          ((n.choose (j + 1) - n.choose j : ℕ) : ℝ) *
              ((n - j : ℕ) : ℝ) ≤
            ((n + 1 : ℕ) : ℝ) *
              ((n.choose (j + 1) - n.choose j : ℕ) : ℝ) := by
        calc
          ((n.choose (j + 1) - n.choose j : ℕ) : ℝ) *
              ((n - j : ℕ) : ℝ) ≤
            ((n.choose (j + 1) - n.choose j : ℕ) : ℝ) *
              ((n + 1 : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left hrange (Nat.cast_nonneg _)
          _ = ((n + 1 : ℕ) : ℝ) *
              ((n.choose (j + 1) - n.choose j : ℕ) : ℝ) := by ring
      exact_mod_cast hlower.trans hupper

theorem hammingFibreDimension_le_choose (n k : ℕ) :
    MetricCodes.hammingFibreDimension n k ≤ n.choose k := by
  cases k with
  | zero => simp only [hammingFibreDimension, booleanHarmonicDimension, Nat.choose_zero_right,
              Std.le_refl]
  | succ j =>
      change n.choose (j + 1) - n.choose j ≤ n.choose (j + 1)
      exact Nat.sub_le _ _

theorem tendsto_logb_succ_div :
    Tendsto
      (fun n : ℕ => Real.logb 2 ((n + 1 : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds
  have hupper := SpherePacking.tendsto_log_two_mul_natCast_div_natCast
  have hnonneg :
      ∀ᶠ n : ℕ in atTop,
        (0 : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    apply div_nonneg
    · apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ n + 1 by omega)
    · exact Nat.cast_nonneg n
  have hle :
      ∀ᶠ n : ℕ in atTop,
        Real.log ((n + 1 : ℕ) : ℝ) / (n : ℝ) ≤
          Real.log (2 * (n : ℝ)) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    apply (div_le_div_iff_of_pos_right hnreal).2
    apply Real.log_le_log
    · positivity
    · have hnat : n + 1 ≤ 2 * n := by omega
      exact_mod_cast hnat
  have hnatural :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hzero hupper hnonneg hle
  have hbase := hnatural.div_const (Real.log 2)
  have hbase' :
      Tendsto
        (fun n : ℕ =>
          (Real.log ((n + 1 : ℕ) : ℝ) / (n : ℝ)) / Real.log 2)
        atTop (nhds 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, zero_div] using hbase
  refine hbase'.congr' (Filter.Eventually.of_forall fun n => ?_)
  unfold Real.logb
  ring

theorem tendsto_logb_ambientDimension {a b : ℝ}
    (hb : 0 ≤ b) (hba : b < a) (ha : a ≤ (1 : ℝ) / 2) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2
          (ambientDimension n
            (transverseDegree b n) (longitudinalDegree a n) : ℝ) /
          (n : ℝ))
      atTop (nhds (MetricCodes.binaryEntropy a)) := by
  have ha0 : 0 < a := lt_of_le_of_lt hb hba
  have ha1 : a < 1 := lt_of_le_of_lt ha (by norm_num)
  have hchoose := tendsto_logb_choose_longitudinal ha0 ha1
  have hpoly := tendsto_logb_succ_div
  have hupperlim :
      Tendsto
        (fun n : ℕ =>
          Real.logb 2 ((n + 1 : ℕ) : ℝ) / (n : ℝ) +
            Real.logb 2
              (n.choose (longitudinalDegree a n) : ℝ) / (n : ℝ))
        atTop (nhds (MetricCodes.binaryEntropy a)) := by
    simpa only [Nat.cast_add, Nat.cast_one, zero_add] using hpoly.add hchoose
  have hfit := eventually_transverse_add_le_longitudinal hb hba 0
  have hlower :
      ∀ᶠ n : ℕ in atTop,
        Real.logb 2
            (n.choose (longitudinalDegree a n) : ℝ) / (n : ℝ) ≤
          Real.logb 2
            (ambientDimension n (transverseDegree b n)
              (longitudinalDegree a n) : ℝ) / (n : ℝ) := by
    filter_upwards [hfit, eventually_gt_atTop (0 : ℕ)] with n hkn hn
    have hkL : transverseDegree b n ≤ longitudinalDegree a n := by omega
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    apply (div_le_div_iff_of_pos_right hnreal).2
    apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    · exact_mod_cast Nat.choose_pos
        (longitudinalDegree_le_dimension ha1.le n)
    · exact_mod_cast choose_le_ambientDimension n
        (transverseDegree b n) (longitudinalDegree a n) hkL
  have hupper :
      ∀ᶠ n : ℕ in atTop,
        Real.logb 2
            (ambientDimension n (transverseDegree b n)
              (longitudinalDegree a n) : ℝ) / (n : ℝ) ≤
          Real.logb 2 ((n + 1 : ℕ) : ℝ) / (n : ℝ) +
            Real.logb 2
              (n.choose (longitudinalDegree a n) : ℝ) / (n : ℝ) := by
    filter_upwards [hfit, eventually_gt_atTop (0 : ℕ)] with n hkn hn
    have hkL : transverseDegree b n ≤ longitudinalDegree a n := by omega
    have hhalf := longitudinalDegree_le_half ha n
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hchoosepos :
        0 < (n.choose (longitudinalDegree a n) : ℝ) := by
      exact_mod_cast Nat.choose_pos
        (longitudinalDegree_le_dimension ha1.le n)
    have hambientpos :
        0 < (ambientDimension n (transverseDegree b n)
          (longitudinalDegree a n) : ℝ) := by
      have hle := choose_le_ambientDimension n
        (transverseDegree b n) (longitudinalDegree a n) hkL
      exact lt_of_lt_of_le hchoosepos (by exact_mod_cast hle)
    calc
      Real.logb 2
          (ambientDimension n (transverseDegree b n)
            (longitudinalDegree a n) : ℝ) / (n : ℝ) ≤
        Real.logb 2
          (((n + 1) * n.choose (longitudinalDegree a n) : ℕ) : ℝ) /
            (n : ℝ) := by
          apply (div_le_div_iff_of_pos_right hnreal).2
          apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
            hambientpos
          exact_mod_cast ambientDimension_le_mul_choose n
            (transverseDegree b n) (longitudinalDegree a n) hkL hhalf
      _ = Real.logb 2 ((n + 1 : ℕ) : ℝ) / (n : ℝ) +
            Real.logb 2
              (n.choose (longitudinalDegree a n) : ℝ) / (n : ℝ) := by
          push_cast
          rw [Real.logb_mul (by positivity) hchoosepos.ne']
          ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hchoose hupperlim hlower hupper

theorem tendsto_logb_hammingFibreDimension {b : ℝ}
    (hb : 0 < b) (hb' : b ≤ (1 : ℝ) / 2) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2
          (MetricCodes.hammingFibreDimension n (transverseDegree b n) : ℝ) /
          (n : ℝ))
      atTop (nhds (MetricCodes.binaryEntropy b)) := by
  have hb1 : b < 1 := lt_of_le_of_lt hb' (by norm_num)
  have hchoose :
      Tendsto
        (fun n : ℕ =>
          Real.logb 2
            (n.choose (transverseDegree b n) : ℝ) / (n : ℝ))
        atTop (nhds (MetricCodes.binaryEntropy b)) := by
    simpa only [transverseDegree, longitudinalDegree] using tendsto_logb_choose_longitudinal hb hb1
  have hpoly := tendsto_logb_succ_div
  have hlowerlim :
      Tendsto
        (fun n : ℕ =>
          Real.logb 2
              (n.choose (transverseDegree b n) : ℝ) / (n : ℝ) -
            Real.logb 2 ((n + 1 : ℕ) : ℝ) / (n : ℝ))
        atTop (nhds (MetricCodes.binaryEntropy b)) := by
    simpa only [Nat.cast_add, Nat.cast_one, sub_zero] using hchoose.sub hpoly
  have hlower :
      ∀ᶠ n : ℕ in atTop,
        Real.logb 2
              (n.choose (transverseDegree b n) : ℝ) / (n : ℝ) -
            Real.logb 2 ((n + 1 : ℕ) : ℝ) / (n : ℝ) ≤
          Real.logb 2
            (MetricCodes.hammingFibreDimension n
              (transverseDegree b n) : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hkhalf : 2 * transverseDegree b n ≤ n := by
      have h : transverseDegree b n ≤ n / 2 := by
        simpa only [transverseDegree, longitudinalDegree] using longitudinalDegree_le_half hb' n
      omega
    have hfibre :
        0 < (MetricCodes.hammingFibreDimension n
          (transverseDegree b n) : ℝ) := by
      exact_mod_cast hammingFibreDimension_pos hkhalf
    have hchoosepos : 0 < (n.choose (transverseDegree b n) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega : transverseDegree b n ≤ n)
    have hlog :
        Real.logb 2 (n.choose (transverseDegree b n) : ℝ) ≤
          Real.logb 2 ((n + 1 : ℕ) : ℝ) +
            Real.logb 2
              (MetricCodes.hammingFibreDimension n
                (transverseDegree b n) : ℝ) := by
      rw [← Real.logb_mul (by positivity) hfibre.ne']
      apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        hchoosepos
      exact_mod_cast choose_le_mul_hammingFibreDimension hkhalf
    calc
      Real.logb 2 (n.choose (transverseDegree b n) : ℝ) / (n : ℝ) -
          Real.logb 2 ((n + 1 : ℕ) : ℝ) / (n : ℝ) =
        (Real.logb 2 (n.choose (transverseDegree b n) : ℝ) -
          Real.logb 2 ((n + 1 : ℕ) : ℝ)) / (n : ℝ) := by ring
      _ ≤ Real.logb 2
          (MetricCodes.hammingFibreDimension n
            (transverseDegree b n) : ℝ) / (n : ℝ) := by
        apply (div_le_div_iff_of_pos_right hnreal).2
        linarith
  have hupper :
      ∀ᶠ n : ℕ in atTop,
        Real.logb 2
            (MetricCodes.hammingFibreDimension n
              (transverseDegree b n) : ℝ) / (n : ℝ) ≤
          Real.logb 2
            (n.choose (transverseDegree b n) : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hkhalf : 2 * transverseDegree b n ≤ n := by
      have h : transverseDegree b n ≤ n / 2 := by
        simpa only [transverseDegree, longitudinalDegree] using longitudinalDegree_le_half hb' n
      omega
    have hfibre :
        0 < (MetricCodes.hammingFibreDimension n
          (transverseDegree b n) : ℝ) := by
      exact_mod_cast hammingFibreDimension_pos hkhalf
    apply (div_le_div_iff_of_pos_right hnreal).2
    apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      hfibre
    exact_mod_cast hammingFibreDimension_le_choose n
      (transverseDegree b n)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlowerlim hchoose hlower hupper

/-- The binary rate used in the binary-code argument. -/
def binaryRate (δ : ℝ) : ℝ :=
  Filter.limsup
    (fun n : ℕ =>
      Real.logb 2
        (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) / (n : ℝ))
    Filter.atTop

theorem tendsto_ceil_distance_ratio {δ : ℝ} (hδ : 0 ≤ δ) :
    Tendsto
      (fun n : ℕ => (Nat.ceil (δ * (n : ℝ)) : ℝ) / (n : ℝ))
      atTop (nhds δ) := by
  simpa only [Function.comp_def] using
    (tendsto_nat_ceil_mul_div_atTop hδ).comp (tendsto_natCast_atTop_atTop (R := ℝ))

theorem tendsto_threshold_ceil {δ : ℝ} (hδ : 0 ≤ δ) :
    Tendsto
      (fun n : ℕ => threshold n (Nat.ceil (δ * (n : ℝ))))
      atTop (nhds (1 - 2 * δ)) := by
  have hratio := tendsto_ceil_distance_ratio hδ
  have hlimit :=
    (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := (2 : ℝ))).mul hratio)
  refine hlimit.congr' (Filter.Eventually.of_forall fun n => ?_)
  unfold threshold
  ring

theorem ceil_distance_pos {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (hn : 0 < n) :
    0 < Nat.ceil (δ * (n : ℝ)) := by
  apply Nat.ceil_pos.mpr
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact mul_pos hδ hnreal

/-- The window fibre quotient used in the binary-code argument. -/
def windowFibreQuotient (a b : ℝ) (n : ℕ) : ℝ :=
  (ambientDimension n (transverseDegree b n)
      (longitudinalDegree a n) : ℝ) /
    (MetricCodes.hammingFibreDimension n (transverseDegree b n) : ℝ)

theorem windowFibreQuotient_pos_of_fit {a b : ℝ} {n : ℕ}
    (ha : a ≤ (1 : ℝ) / 2)
    (hfit : transverseDegree b n ≤ longitudinalDegree a n) :
    0 < windowFibreQuotient a b n := by
  have hhalf := longitudinalDegree_le_half ha n
  have hkhalf : 2 * transverseDegree b n ≤ n := by omega
  have hfibre :
      0 < (MetricCodes.hammingFibreDimension n (transverseDegree b n) : ℝ) := by
    exact_mod_cast hammingFibreDimension_pos hkhalf
  have haone : a ≤ 1 := by linarith
  have hchoose : 0 < (n.choose (longitudinalDegree a n) : ℝ) := by
    exact_mod_cast
      Nat.choose_pos (longitudinalDegree_le_dimension haone n)
  have hambient :
      0 < (ambientDimension n (transverseDegree b n)
        (longitudinalDegree a n) : ℝ) := by
    have hle := choose_le_ambientDimension n
      (transverseDegree b n) (longitudinalDegree a n) hfit
    exact lt_of_lt_of_le hchoose (by exact_mod_cast hle)
  exact div_pos hambient hfibre

theorem eventually_windowFibreQuotient_pos {a b : ℝ}
    (hb : 0 ≤ b) (hba : b < a) (ha : a ≤ (1 : ℝ) / 2) :
    ∀ᶠ n : ℕ in atTop, 0 < windowFibreQuotient a b n := by
  filter_upwards [eventually_transverse_add_le_longitudinal hb hba 0]
    with n hfit
  apply windowFibreQuotient_pos_of_fit ha
  omega

theorem tendsto_logb_windowFibreQuotient {a b : ℝ}
    (hb : 0 < b) (hba : b < a) (ha : a ≤ (1 : ℝ) / 2) :
    Tendsto
      (fun n : ℕ => Real.logb 2 (windowFibreQuotient a b n) / (n : ℝ))
      atTop (nhds (MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b)) := by
  have hbhalf : b ≤ (1 : ℝ) / 2 := hba.le.trans ha
  have hnum := tendsto_logb_ambientDimension hb.le hba ha
  have hden := tendsto_logb_hammingFibreDimension hb hbhalf
  have hdiff := hnum.sub hden
  refine hdiff.congr' ?_
  filter_upwards [eventually_transverse_add_le_longitudinal hb.le hba 0]
    with n hfit
  have hkn : transverseDegree b n ≤ longitudinalDegree a n := by omega
  have hhalf := longitudinalDegree_le_half ha n
  have hkhalf : 2 * transverseDegree b n ≤ n := by omega
  have hfibre :
      0 < (MetricCodes.hammingFibreDimension n (transverseDegree b n) : ℝ) := by
    exact_mod_cast hammingFibreDimension_pos hkhalf
  have haone : a ≤ 1 := by linarith
  have hchoose : 0 < (n.choose (longitudinalDegree a n) : ℝ) := by
    exact_mod_cast
      Nat.choose_pos (longitudinalDegree_le_dimension haone n)
  have hambient :
      0 < (ambientDimension n (transverseDegree b n)
        (longitudinalDegree a n) : ℝ) := by
    have hle := choose_le_ambientDimension n
      (transverseDegree b n) (longitudinalDegree a n) hkn
    exact lt_of_lt_of_le hchoose (by exact_mod_cast hle)
  unfold windowFibreQuotient
  rw [Real.logb_div hambient.ne' hfibre.ne']
  ring

theorem tendsto_logb_const_mul_windowFibreQuotient
    {a b C : ℝ} (hb : 0 < b) (hba : b < a)
    (ha : a ≤ (1 : ℝ) / 2) (hC : 0 < C) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2 (C * windowFibreQuotient a b n) / (n : ℝ))
      atTop (nhds (MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b)) := by
  have hconst :=
    tendsto_const_div_atTop_nhds_zero_nat (Real.logb 2 C)
  have hquot := tendsto_logb_windowFibreQuotient hb hba ha
  have hsum :
      Tendsto
        (fun n : ℕ =>
          Real.logb 2 C / (n : ℝ) +
            Real.logb 2 (windowFibreQuotient a b n) / (n : ℝ))
        atTop (nhds (MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b)) := by
    simpa only [zero_add] using hconst.add hquot
  refine hsum.congr' ?_
  filter_upwards [eventually_windowFibreQuotient_pos hb.le hba ha]
    with n hpos
  rw [Real.logb_mul hC.ne' hpos.ne']
  ring

theorem codeLogRate_nonneg (δ : ℝ) (n : ℕ) :
    0 ≤ Real.logb 2
      (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) / (n : ℝ) := by
  apply div_nonneg
  · apply Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
    exact_mod_cast codeNumber_pos n (Nat.ceil (δ * (n : ℝ)))
  · exact Nat.cast_nonneg n

theorem binaryRate_le_of_eventually {δ r : ℝ} {u : ℕ → ℝ}
    (hu : Tendsto u atTop (nhds r))
    (hbound : ∀ᶠ n : ℕ in atTop,
      Real.logb 2
        (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) / (n : ℝ) ≤ u n) :
    binaryRate δ ≤ r := by
  let w : ℕ → ℝ := fun n =>
    Real.logb 2
      (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) / (n : ℝ)
  have hlower : atTop.IsBoundedUnder (· ≥ ·) w :=
    Filter.isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall (codeLogRate_nonneg δ))
  have hcob : atTop.IsCoboundedUnder (· ≤ ·) w :=
    hlower.isCoboundedUnder_le
  have hcomparison : Filter.limsup w atTop ≤ Filter.limsup u atTop :=
    Filter.limsup_le_limsup hbound hcob hu.isBoundedUnder_le
  change Filter.limsup w atTop ≤ r
  exact hcomparison.trans_eq hu.limsup_eq

theorem ceil_distance_le_dimension {δ : ℝ} (hδ : δ ≤ 1) (n : ℕ) :
    Nat.ceil (δ * (n : ℝ)) ≤ n := by
  apply Nat.ceil_le.mpr
  calc
    δ * (n : ℝ) ≤ 1 * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg n)
    _ = (n : ℝ) := one_mul _

theorem threshold_ceil_numerator_le_two {δ : ℝ}
    (hδ : δ ≤ 1) {n : ℕ} (hn : 0 < n) :
    1 - threshold n (Nat.ceil (δ * (n : ℝ))) ≤ 2 := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdreal : (Nat.ceil (δ * (n : ℝ)) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast ceil_distance_le_dimension hδ n
  have hquot :
      2 * (Nat.ceil (δ * (n : ℝ)) : ℝ) / (n : ℝ) ≤ 2 := by
    apply (div_le_iff₀ hnreal).2
    exact mul_le_mul_of_nonneg_left hdreal (by norm_num)
  unfold threshold
  linarith

/-- The spectral gap used in the binary-code argument. -/
def spectralGap (δ a b : ℝ) : ℝ :=
  (MetricCodes.hammingGamma a b - (1 - 2 * δ)) / 4

theorem spectralGap_pos {δ a b : ℝ} (h : Feasible δ a b) :
    0 < spectralGap δ a b := by
  unfold spectralGap
  linarith [h.2.2.2]

theorem eventually_topEigenvalue_uniform_gap_ceil {δ a b : ℝ}
    (hδ : 0 ≤ δ) (h : Feasible δ a b) :
    ∀ᶠ n : ℕ in atTop,
      spectralGap δ a b <
        topEigenvalue n (transverseDegree b n)
          (longitudinalDegree a n) -
            threshold n (Nat.ceil (δ * (n : ℝ))) := by
  obtain ⟨hb, hba, ha, hgamma⟩ := h
  have hgap : 0 < spectralGap δ a b :=
    spectralGap_pos ⟨hb, hba, ha, hgamma⟩
  have hstrict :
      1 - 2 * δ + 2 * spectralGap δ a b <
        MetricCodes.hammingGamma a b := by
    unfold spectralGap
    linarith
  have heigen :=
    eventually_topEigenvalue_gt hb hba ha hstrict
  have hthreshold :
      ∀ᶠ n : ℕ in atTop,
        threshold n (Nat.ceil (δ * (n : ℝ))) <
          1 - 2 * δ + spectralGap δ a b :=
    (tendsto_threshold_ceil hδ).eventually
      (gt_mem_nhds (by linarith))
  filter_upwards [heigen, hthreshold] with n he hn
  linarith

/-- The spectral prefactor used in the binary-code argument. -/
def spectralPrefactor (δ a b : ℝ) : ℝ :=
  2 / spectralGap δ a b

theorem spectralPrefactor_pos {δ a b : ℝ} (h : Feasible δ a b) :
    0 < spectralPrefactor δ a b := by
  unfold spectralPrefactor
  exact div_pos (by norm_num) (spectralGap_pos h)

theorem eventually_hamming_prefactor_le {δ a b : ℝ}
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) (h : Feasible δ a b) :
    ∀ᶠ n : ℕ in atTop,
      ((1 - threshold n (Nat.ceil (δ * (n : ℝ)))) /
        (topEigenvalue n (transverseDegree b n)
          (longitudinalDegree a n) -
            threshold n (Nat.ceil (δ * (n : ℝ))))) ≤
        spectralPrefactor δ a b := by
  have hgap : 0 < spectralGap δ a b := spectralGap_pos h
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_topEigenvalue_uniform_gap_ceil hδ h]
      with n hn heigen
  unfold spectralPrefactor
  apply div_le_div₀ (by norm_num : (0 : ℝ) ≤ 2)
  · exact threshold_ceil_numerator_le_two hδ' hn
  · exact hgap
  · exact heigen.le

theorem rateSet_nonempty_of_interior {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2) :
    (rateSet δ).Nonempty := by
  obtain ⟨a, b, hfeasible, _⟩ :=
    exists_strict_improving_feasible hδ hδ'
  exact ⟨MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b,
    a, b, hfeasible, rfl⟩

theorem exists_positive_feasible_of_zero {δ a : ℝ}
    (h : Feasible δ a 0) :
    ∃ b : ℝ, 0 < b ∧ Feasible δ a b := by
  obtain ⟨_, ha, hahalf, hgamma⟩ := h
  have hcontinuous :
      Continuous (fun b : ℝ => MetricCodes.hammingGamma a b) := by
    unfold MetricCodes.hammingGamma
    fun_prop
  have hnear :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        1 - 2 * δ < MetricCodes.hammingGamma a b := by
    exact nhdsWithin_le_nhds
      ((hcontinuous.continuousAt (x := (0 : ℝ))).tendsto.eventually
        (lt_mem_nhds hgamma))
  have hsmall : ∀ᶠ b : ℝ in 𝓝[>] 0, b < a :=
    nhdsWithin_le_nhds (gt_mem_nhds ha)
  have htotal :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        0 < b ∧ Feasible δ a b := by
    filter_upwards [hnear, hsmall, self_mem_nhdsWithin]
      with b hgamma' hba (hb : 0 < b)
    exact ⟨hb, hb.le, hba, hahalf, hgamma'⟩
  exact htotal.exists

theorem binaryRate_le_of_eventually_windowFibreQuotient
    {δ a b C : ℝ}
    (hb : 0 < b) (hba : b < a)
    (ha : a ≤ (1 : ℝ) / 2) (hC : 0 < C)
    (hbound : ∀ᶠ n : ℕ in atTop,
      (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) ≤
        C * windowFibreQuotient a b n) :
    binaryRate δ ≤ MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b := by
  refine binaryRate_le_of_eventually
    (tendsto_logb_const_mul_windowFibreQuotient hb hba ha hC) ?_
  filter_upwards [hbound, eventually_gt_atTop (0 : ℕ)]
    with n hncode hn
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcode :
      0 < (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) := by
    exact_mod_cast codeNumber_pos n (Nat.ceil (δ * (n : ℝ)))
  apply (div_le_div_iff_of_pos_right hnreal).2
  exact Real.logb_le_logb_of_le
    (by norm_num : (1 : ℝ) < 2) hcode hncode

theorem binaryRate_le_of_positive_feasible_bound {δ a b : ℝ}
    (h : Feasible δ a b) (hb : 0 < b)
    (hbound : ∀ᶠ n : ℕ in atTop,
      (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) ≤
        spectralPrefactor δ a b * windowFibreQuotient a b n) :
    binaryRate δ ≤ MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b := by
  exact binaryRate_le_of_eventually_windowFibreQuotient
    hb h.2.1 h.2.2.1 (spectralPrefactor_pos h) hbound

theorem binaryRate_le_variationalRate_of_positive_feasible_bounds
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2)
    (hbound : ∀ ⦃a b : ℝ⦄,
      Feasible δ a b → 0 < b →
        ∀ᶠ n : ℕ in atTop,
          (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) ≤
            spectralPrefactor δ a b * windowFibreQuotient a b n) :
    binaryRate δ ≤ variationalRate δ := by
  have hcandidate :
      ∀ ⦃a b : ℝ⦄, Feasible δ a b →
        binaryRate δ ≤ MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b := by
    intro a b hfeasible
    rcases hfeasible.1.eq_or_lt with hzero | hpositive
    · have hbzero : b = 0 := hzero.symm
      subst b
      obtain ⟨c, hc, hfeasible'⟩ :=
        exists_positive_feasible_of_zero hfeasible
      have hrate := binaryRate_le_of_positive_feasible_bound
        hfeasible' hc (hbound hfeasible' hc)
      have hcunit : c ≤ 1 := by
        have hca := hfeasible'.2.1
        have hahalf := hfeasible'.2.2.1
        linarith
      have hentropy : 0 ≤ MetricCodes.binaryEntropy c :=
        MetricCodes.binaryEntropy_nonneg hc.le hcunit
      calc
        binaryRate δ ≤
            MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy c := hrate
        _ ≤ MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy 0 := by
          simpa only [binaryEntropy_zero, sub_zero, tsub_le_iff_right, le_add_iff_nonneg_right]
            using
            sub_le_self (MetricCodes.binaryEntropy a) hentropy
    · exact binaryRate_le_of_positive_feasible_bound
        hfeasible hpositive (hbound hfeasible hpositive)
  unfold variationalRate
  apply le_csInf (rateSet_nonempty_of_interior hδ hδ')
  rintro _ ⟨a, b, hfeasible, rfl⟩
  exact hcandidate hfeasible

theorem finite_bound {n k L d : ℕ}
    (hn : 0 < n) (hd : 0 < d)
    (hkL : k < L) (hLn : L + k ≤ n)
    (hgap : threshold n d < topEigenvalue n k L) :
    (codeNumber n d : ℝ) ≤
      ((1 - threshold n d) /
        (topEigenvalue n k L - threshold n d)) *
        ((ambientDimension n k L : ℝ) /
          (MetricCodes.hammingFibreDimension n k : ℝ)) := by
  have hk : 2 * k ≤ n := by omega
  obtain ⟨v, hunit, heigen, hpositive⟩ :=
    exists_positive_unit_topEigenvector hn hkL.le hLn
  have heigenraw :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        topEigenvalue n k L • v := by
    simpa only [operator, matrix] using heigen
  have hlambda : 0 < topEigenvalue n k L :=
    topEigenvalue_pos hn hkL hLn
  let P : MetricCodes.ProjectionFamily (BinaryWord n)
      (ambientDimension n k L) (MetricCodes.hammingFibreDimension n k) :=
    MetricCodes.Boolean.hammingProjectionFamily hk hkL.le hLn
      v hunit (fun i => (hpositive i).le)
  let q := MetricCodes.Boolean.hammingProjectionGramFeature
    hk hkL.le hLn v hunit hpositive (topEigenvalue n k L)
  apply finite_codeNumber_bound_of_projection_gram
    hn hd P q (hammingFibreDimension_pos hk) hgap
  intro x y
  simpa only [Boolean.hammingWindowDimension, ambientDimension] using
    (MetricCodes.Boolean.hammingProjectionGramFeature_inner hn hk hkL.le hLn v hunit hpositive
      (topEigenvalue n k L)
      hlambda heigenraw x y)

theorem eventually_codeNumber_le_spectralPrefactor_mul_windowFibreQuotient
    {δ a b : ℝ} (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2)
    (h : Feasible δ a b) :
    ∀ᶠ n : ℕ in atTop,
      (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) ≤
        spectralPrefactor δ a b * windowFibreQuotient a b n := by
  have hδone : δ ≤ 1 := by linarith
  filter_upwards [
    eventually_gt_atTop (0 : ℕ),
    eventually_transverse_add_le_longitudinal h.1 h.2.1 1,
    eventually_topEigenvalue_uniform_gap_ceil hδ.le h,
    eventually_hamming_prefactor_le hδ.le hδone h]
    with n hn hfit hmargin hprefactor
  have hkL : transverseDegree b n < longitudinalDegree a n := by
    omega
  have hhalf := longitudinalDegree_le_half h.2.2.1 n
  have hLn :
      longitudinalDegree a n + transverseDegree b n ≤ n := by
    omega
  have hd : 0 < Nat.ceil (δ * (n : ℝ)) :=
    ceil_distance_pos hδ hn
  have hgap :
      threshold n (Nat.ceil (δ * (n : ℝ))) <
        topEigenvalue n (transverseDegree b n)
          (longitudinalDegree a n) := by
    have hpositive := spectralGap_pos h
    linarith
  have hfinite := finite_bound hn hd hkL hLn hgap
  have hquotient : 0 ≤ windowFibreQuotient a b n :=
    (windowFibreQuotient_pos_of_fit h.2.2.1 hkL.le).le
  calc
    (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) ≤
        ((1 - threshold n (Nat.ceil (δ * (n : ℝ)))) /
          (topEigenvalue n (transverseDegree b n)
            (longitudinalDegree a n) -
              threshold n (Nat.ceil (δ * (n : ℝ))))) *
            windowFibreQuotient a b n := by
      simpa only [windowFibreQuotient] using hfinite
    _ ≤ spectralPrefactor δ a b * windowFibreQuotient a b n :=
      mul_le_mul_of_nonneg_right hprefactor hquotient

theorem binaryRate_le_variationalRate {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2) :
    binaryRate δ ≤ variationalRate δ := by
  apply binaryRate_le_variationalRate_of_positive_feasible_bounds hδ hδ'
  intro a b hfeasible _
  exact eventually_codeNumber_le_spectralPrefactor_mul_windowFibreQuotient
    hδ hδ' hfeasible





end Hamming

end

namespace Johnson

section

open scoped BigOperators InnerProductSpace Matrix

private def binaryCodeFamily (n d : ℕ) : Finset (Finset (BinaryWord n)) := by
  classical
  exact (Finset.univ : Finset (BinaryWord n)).powerset.filter
    (fun C => IsBinaryCode d C)

@[simp] theorem mem_binaryCodeFamily {n d : ℕ}
    (C : Finset (BinaryWord n)) :
    C ∈ binaryCodeFamily n d ↔ IsBinaryCode d C := by
  classical
  simp only [binaryCodeFamily, Finset.powerset_univ, Finset.mem_filter, Finset.mem_univ, true_and]

theorem binaryCodeFamily_nonempty (n d : ℕ) :
    (binaryCodeFamily n d).Nonempty := by
  classical
  refine ⟨∅, ?_⟩
  simp only [binaryCodeFamily, IsBinaryCode, ne_eq, Finset.powerset_univ, Finset.mem_filter,
    Finset.mem_univ, Finset.notMem_empty, IsEmpty.forall_iff, implies_true, and_self]

/-- The binary code number used in the Johnson-code argument. -/
def binaryCodeNumber (n d : ℕ) : ℕ :=
  (binaryCodeFamily n d).sup (fun C => C.card)

theorem card_le_binaryCodeNumber {n d : ℕ}
    (C : Finset (BinaryWord n)) (hC : IsBinaryCode d C) :
    C.card ≤ binaryCodeNumber n d := by
  exact Finset.le_sup ((mem_binaryCodeFamily C).mpr hC)

theorem exists_binaryCodeNumber (n d : ℕ) :
    ∃ C : Finset (BinaryWord n),
      IsBinaryCode d C ∧ C.card = binaryCodeNumber n d := by
  obtain ⟨C, hC, hmax⟩ :=
    Finset.exists_mem_eq_sup (binaryCodeFamily n d)
      (binaryCodeFamily_nonempty n d) (fun C => C.card)
  exact ⟨C, (mem_binaryCodeFamily C).mp hC, hmax.symm⟩

private def shellCodeFamily (n w d : ℕ) : Finset (Finset (BinaryWord n)) := by
  classical
  exact (weightShell n w).powerset.filter (fun C => IsBinaryCode d C)

@[simp] theorem mem_shellCodeFamily {n w d : ℕ}
    (C : Finset (BinaryWord n)) :
    C ∈ shellCodeFamily n w d ↔
      C ⊆ weightShell n w ∧ IsBinaryCode d C := by
  classical
  simp only [shellCodeFamily, Finset.mem_filter, Finset.mem_powerset]

theorem shellCodeFamily_nonempty (n w d : ℕ) :
    (shellCodeFamily n w d).Nonempty := by
  classical
  refine ⟨∅, ?_⟩
  rw [mem_shellCodeFamily]
  exact ⟨Finset.empty_subset _, fun {_} hx => (Finset.notMem_empty _ hx).elim⟩

private def shellCodeNumber (n w d : ℕ) : ℕ :=
  (shellCodeFamily n w d).sup (fun C => C.card)

theorem card_le_shellCodeNumber {n w d : ℕ}
    (C : Finset (BinaryWord n))
    (hweight : C ⊆ weightShell n w) (hC : IsBinaryCode d C) :
    C.card ≤ shellCodeNumber n w d := by
  exact Finset.le_sup ((mem_shellCodeFamily C).mpr ⟨hweight, hC⟩)

theorem exists_shellCodeNumber (n w d : ℕ) :
    ∃ C : Finset (BinaryWord n),
      C ⊆ weightShell n w ∧ IsBinaryCode d C ∧
        C.card = shellCodeNumber n w d := by
  obtain ⟨C, hC, hmax⟩ :=
    Finset.exists_mem_eq_sup (shellCodeFamily n w d)
      (shellCodeFamily_nonempty n w d) (fun C => C.card)
  obtain ⟨hweight, hdistance⟩ := (mem_shellCodeFamily C).mp hC
  exact ⟨C, hweight, hdistance, hmax.symm⟩

theorem bassalygo_elias (n w d : ℕ) :
    binaryCodeNumber n d * n.choose w ≤
      2 ^ n * shellCodeNumber n w d := by
  obtain ⟨C, hC, hcard⟩ := exists_binaryCodeNumber n d
  rw [← hcard]
  exact MetricCodes.bassalygo_elias_bound C hC
    (fun D hweight hD => card_le_shellCodeNumber D hweight hD)

theorem bassalygo_elias_real {n w d : ℕ} (hw : w ≤ n) :
    (binaryCodeNumber n d : ℝ) ≤
      ((2 : ℝ) ^ n / (n.choose w : ℝ)) *
        (shellCodeNumber n w d : ℝ) := by
  have hc : 0 < (n.choose w : ℝ) := by
    exact_mod_cast Nat.choose_pos hw
  calc
    (binaryCodeNumber n d : ℝ) ≤
        ((2 : ℝ) ^ n * (shellCodeNumber n w d : ℝ)) /
          (n.choose w : ℝ) := by
      apply (le_div_iff₀ hc).mpr
      exact_mod_cast bassalygo_elias n w d
    _ = ((2 : ℝ) ^ n / (n.choose w : ℝ)) *
        (shellCodeNumber n w d : ℝ) := by
      ring

theorem binaryCodeNumber_eq_hamming (n d : ℕ) :
    binaryCodeNumber n d = MetricCodes.Hamming.codeNumber n d := by
  apply Nat.le_antisymm
  · obtain ⟨C, hC, hcard⟩ := exists_binaryCodeNumber n d
    rw [← hcard]
    exact MetricCodes.Hamming.card_le_codeNumber C hC
  · obtain ⟨C, hC, hcard⟩ := MetricCodes.Hamming.exists_codeNumber n d
    rw [← hcard]
    exact card_le_binaryCodeNumber C hC

private def words {n w : ℕ} (C : Finset (JohnsonSphere n w)) :
    Finset (BinaryWord n) :=
  C.image Subtype.val

private def IsCode {n w : ℕ} (d : ℕ)
    (C : Finset (JohnsonSphere n w)) : Prop :=
  IsBinaryCode d (words C)

private def asSubtype {n w : ℕ} (C : Finset (BinaryWord n))
    (hweight : C ⊆ weightShell n w) :
    Finset (JohnsonSphere n w) := by
  classical
  exact C.attach.image (fun x =>
    (⟨x.val, (MetricCodes.mem_weightShell x.val).mp
      (hweight x.property)⟩ : JohnsonSphere n w))

theorem card_asSubtype {n w : ℕ}
    (C : Finset (BinaryWord n))
    (hweight : C ⊆ weightShell n w) :
    (asSubtype C hweight).card = C.card := by
  classical
  unfold asSubtype
  rw [Finset.card_image_of_injective, Finset.card_attach]
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun q : JohnsonSphere n w => q.val) hxy

theorem words_asSubtype {n w : ℕ}
    (C : Finset (BinaryWord n))
    (hweight : C ⊆ weightShell n w) :
    words (asSubtype C hweight) = C := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨z, _hz, hz⟩ := Finset.mem_image.mp hy
    have hval := congrArg Subtype.val hz
    simpa only using hval ▸ z.property
  · intro hx
    let z : {z : BinaryWord n // z ∈ C} := ⟨x, hx⟩
    let y : JohnsonSphere n w :=
      ⟨x, (MetricCodes.mem_weightShell x).mp (hweight hx)⟩
    apply Finset.mem_image.mpr
    refine ⟨y, ?_, rfl⟩
    unfold asSubtype
    apply Finset.mem_image.mpr
    refine ⟨z, by simp only [Finset.mem_attach], ?_⟩
    exact Subtype.ext rfl

theorem isCode_asSubtype {n w d : ℕ}
    (C : Finset (BinaryWord n))
    (hweight : C ⊆ weightShell n w)
    (hC : IsBinaryCode d C) :
    IsCode d (asSubtype C hweight) := by
  unfold IsCode
  rw [words_asSubtype]
  exact hC

/-- The correlation used in the Johnson-code argument. -/
def correlation {n w : ℕ} (x y : JohnsonSphere n w) : ℝ :=
  1 - (n : ℝ) * (MetricCodes.johnsonDist x y : ℝ) /
    ((w : ℝ) * ((n - w : ℕ) : ℝ))

@[simp] theorem correlation_self {n w : ℕ}
    (x : JohnsonSphere n w) :
    correlation x x = 1 := by
  simp only [correlation, johnsonDist, sdiff_self, Finset.bot_eq_empty, Finset.card_empty,
    CharP.cast_eq_zero, mul_zero, zero_div, sub_zero]

/-- The threshold used in the Johnson-code argument. -/
def threshold (n w d : ℕ) : ℝ :=
  1 - (n : ℝ) * (d : ℝ) /
    (2 * (w : ℝ) * ((n - w : ℕ) : ℝ))

theorem correlation_eq_hamming {n w : ℕ}
    (hw : 0 < w) (hwn : w < n) (x y : JohnsonSphere n w) :
    correlation x y =
      1 - (n : ℝ) *
        (MetricCodes.hammingDist (x : BinaryWord n) (y : BinaryWord n) : ℝ) /
          (2 * (w : ℝ) * ((n - w : ℕ) : ℝ)) := by
  have hw' : (w : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hw
  have hcomp : 0 < n - w := Nat.sub_pos_of_lt hwn
  have hcomp' : ((n - w : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hcomp
  rw [MetricCodes.hammingDist_eq_two_mul_johnsonDist]
  push_cast
  unfold correlation
  field_simp [hw', hcomp']

theorem threshold_lt_one {n w d : ℕ}
    (hw : 0 < w) (hwn : w < n) (hd : 0 < d) :
    threshold n w d < 1 := by
  have hn : 0 < n := by omega
  have hcomp : 0 < n - w := Nat.sub_pos_of_lt hwn
  have hnum : 0 < (n : ℝ) * (d : ℝ) := by positivity
  have hden : 0 < 2 * (w : ℝ) * ((n - w : ℕ) : ℝ) := by
    positivity
  unfold threshold
  have hfrac := div_pos hnum hden
  linarith

theorem correlation_le_threshold {n w d : ℕ}
    (hw : 0 < w) (hwn : w < n)
    {x y : JohnsonSphere n w}
    (hd : d ≤ MetricCodes.hammingDist (x : BinaryWord n) (y : BinaryWord n)) :
    correlation x y ≤ threshold n w d := by
  rw [correlation_eq_hamming hw hwn x y]
  have hcomp : 0 < n - w := Nat.sub_pos_of_lt hwn
  have hden : 0 < 2 * (w : ℝ) * ((n - w : ℕ) : ℝ) := by
    positivity
  have hd' : (d : ℝ) ≤
      (MetricCodes.hammingDist (x : BinaryWord n) (y : BinaryWord n) : ℝ) := by
    exact_mod_cast hd
  have hnum :
      (n : ℝ) * (d : ℝ) ≤
        (n : ℝ) *
          (MetricCodes.hammingDist (x : BinaryWord n) (y : BinaryWord n) : ℝ) :=
    mul_le_mul_of_nonneg_left hd' (Nat.cast_nonneg n)
  have hfrac :=
    (div_le_div_iff_of_pos_right hden).mpr hnum
  unfold threshold
  linarith

theorem correlation_le_threshold_of_code {n w d : ℕ}
    (hw : 0 < w) (hwn : w < n)
    {C : Finset (JohnsonSphere n w)} (hC : IsCode d C)
    {x y : JohnsonSphere n w}
    (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y) :
    correlation x y ≤ threshold n w d := by
  apply correlation_le_threshold hw hwn
  apply hC (Finset.mem_image_of_mem Subtype.val hx)
    (Finset.mem_image_of_mem Subtype.val hy)
  intro hval
  exact hxy (Subtype.ext hval)

/-- The coordinate indicator used in the Johnson-code argument. -/
def coordinateIndicator {n : ℕ} (x : BinaryWord n)
    (i : Fin n) : ℝ :=
  if i ∈ MetricCodes.wordSupport x then 1 else 0

theorem sum_coordinateIndicator {n : ℕ} (x : BinaryWord n) :
    (∑ i : Fin n, coordinateIndicator x i) =
      (MetricCodes.binaryWeight x : ℝ) := by
  simpa only [coordinateIndicator, mem_wordSupport, Finset.sum_boole,
    binaryWeight_eq_card_wordSupport, Nat.cast_inj,
    mul_one] using (MetricCodes.Boolean.sum_mem_indicator (MetricCodes.wordSupport x) (1 : ℝ))

theorem sum_coordinateIndicator_mul {n : ℕ}
    (x y : BinaryWord n) :
    (∑ i : Fin n, coordinateIndicator x i * coordinateIndicator y i) =
      ((MetricCodes.wordSupport x ∩ MetricCodes.wordSupport y).card : ℝ) := by
  calc
    (∑ i : Fin n, coordinateIndicator x i * coordinateIndicator y i) =
        ∑ i : Fin n,
          if i ∈ MetricCodes.wordSupport x ∩ MetricCodes.wordSupport y
            then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hx : i ∈ MetricCodes.wordSupport x <;>
        by_cases hy : i ∈ MetricCodes.wordSupport y <;>
        simp [coordinateIndicator, hx, hy]
    _ = ((MetricCodes.wordSupport x ∩ MetricCodes.wordSupport y).card : ℝ) := by
      simpa only [Finset.mem_inter, mem_wordSupport, Finset.sum_boole, Nat.cast_inj, mul_one] using
        (MetricCodes.Boolean.sum_mem_indicator (MetricCodes.wordSupport x ∩
          MetricCodes.wordSupport y) (1 : ℝ))

theorem centered_coordinate_inner_sum {n w : ℕ}
    (hn : 0 < n) (x y : JohnsonSphere n w) :
    (∑ i : Fin n,
      (coordinateIndicator (x : BinaryWord n) i -
        (w : ℝ) / (n : ℝ)) *
      (coordinateIndicator (y : BinaryWord n) i -
        (w : ℝ) / (n : ℝ))) =
      ((MetricCodes.wordSupport (x : BinaryWord n) ∩
        MetricCodes.wordSupport (y : BinaryWord n)).card : ℝ) -
        (w : ℝ) ^ 2 / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  calc
    (∑ i : Fin n,
      (coordinateIndicator (x : BinaryWord n) i -
        (w : ℝ) / (n : ℝ)) *
      (coordinateIndicator (y : BinaryWord n) i -
        (w : ℝ) / (n : ℝ))) =
        ∑ i : Fin n,
          (coordinateIndicator (x : BinaryWord n) i *
            coordinateIndicator (y : BinaryWord n) i -
            ((w : ℝ) / (n : ℝ)) *
              coordinateIndicator (x : BinaryWord n) i -
            ((w : ℝ) / (n : ℝ)) *
              coordinateIndicator (y : BinaryWord n) i +
            ((w : ℝ) / (n : ℝ)) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ((MetricCodes.wordSupport (x : BinaryWord n) ∩
          MetricCodes.wordSupport (y : BinaryWord n)).card : ℝ) -
        ((w : ℝ) / (n : ℝ)) * (w : ℝ) -
        ((w : ℝ) / (n : ℝ)) * (w : ℝ) +
        (n : ℝ) * ((w : ℝ) / (n : ℝ)) ^ 2 := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rw [sum_coordinateIndicator_mul,
        sum_coordinateIndicator, sum_coordinateIndicator,
        x.property, y.property]
    _ = ((MetricCodes.wordSupport (x : BinaryWord n) ∩
          MetricCodes.wordSupport (y : BinaryWord n)).card : ℝ) -
        (w : ℝ) ^ 2 / (n : ℝ) := by
      field_simp [hn']
      ; ring

/-- The geometric axis used in the Johnson-code argument. -/
def geometricAxis {n w : ℕ} (x : JohnsonSphere n w) : MetricCodes.Ambient n :=
  WithLp.toLp 2 (fun i : Fin n =>
    Real.sqrt ((n : ℝ) /
      ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (coordinateIndicator (x : BinaryWord n) i -
          (w : ℝ) / (n : ℝ)))

theorem geometricAxis_inner {n w : ℕ}
    (hw : 0 < w) (hwn : w < n)
    (x y : JohnsonSphere n w) :
    ⟪geometricAxis x, geometricAxis y⟫_ℝ = correlation x y := by
  have hn : 0 < n := by omega
  have hcomp : 0 < n - w := Nat.sub_pos_of_lt hwn
  have hn' : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  have hw' : (w : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hw
  have hcomp' : ((n - w : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hcomp
  have hscale :
      0 ≤ (n : ℝ) / ((w : ℝ) * ((n - w : ℕ) : ℝ)) := by
    positivity
  have hxcard : (MetricCodes.wordSupport (x : BinaryWord n)).card = w := by
    simpa only [binaryWeight_eq_card_wordSupport] using x.property
  have hinter :
      (MetricCodes.wordSupport (x : BinaryWord n) ∩
        MetricCodes.wordSupport (y : BinaryWord n)).card ≤ w := by
    calc
      (MetricCodes.wordSupport (x : BinaryWord n) ∩
        MetricCodes.wordSupport (y : BinaryWord n)).card ≤
          (MetricCodes.wordSupport (x : BinaryWord n)).card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = w := hxcard
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply]
  change
    (∑ i : Fin n,
      (Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (coordinateIndicator (x : BinaryWord n) i -
          (w : ℝ) / (n : ℝ))) *
      (Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (coordinateIndicator (y : BinaryWord n) i -
          (w : ℝ) / (n : ℝ)))) = correlation x y
  calc
    (∑ i : Fin n,
      (Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (coordinateIndicator (x : BinaryWord n) i -
          (w : ℝ) / (n : ℝ))) *
      (Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (coordinateIndicator (y : BinaryWord n) i -
          (w : ℝ) / (n : ℝ)))) =
      Real.sqrt ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) ^ 2 *
        (∑ i : Fin n,
          (coordinateIndicator (x : BinaryWord n) i -
            (w : ℝ) / (n : ℝ)) *
          (coordinateIndicator (y : BinaryWord n) i -
            (w : ℝ) / (n : ℝ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ((n : ℝ) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (((MetricCodes.wordSupport (x : BinaryWord n) ∩
            MetricCodes.wordSupport (y : BinaryWord n)).card : ℝ) -
          (w : ℝ) ^ 2 / (n : ℝ)) := by
      rw [Real.sq_sqrt hscale, centered_coordinate_inner_sum hn x y]
    _ = correlation x y := by
      unfold correlation
      rw [MetricCodes.johnsonDist_eq_weight_sub_inter,
        Nat.cast_sub hinter]
      field_simp [hn', hw', hcomp']
      rw [Nat.cast_sub (Nat.le_of_lt hwn)]
      ring

/-- The support coordinates used in the Johnson-code argument. -/
abbrev SupportCoordinates {n w : ℕ} (x : JohnsonSphere n w) :=
  {i : Fin n // i ∈ MetricCodes.wordSupport (x : BinaryWord n)}

/-- The complement coordinates used in the Johnson-code argument. -/
abbrev ComplementCoordinates {n w : ℕ} (x : JohnsonSphere n w) :=
  {i : Fin n // i ∈
    (Finset.univ : Finset (Fin n)) \
      MetricCodes.wordSupport (x : BinaryWord n)}

/-- The support coordinate equiv used in the Johnson-code argument. -/
def supportCoordinateEquiv {n w : ℕ} (x : JohnsonSphere n w) :
    SupportCoordinates x ≃ Fin w :=
  Fintype.equivOfCardEq (by
    simp only [Fintype.card_coe, Fintype.card_fin]
    simpa only [MetricCodes.binaryWeight_eq_card_wordSupport] using x.property)

/-- The complement coordinate equiv used in the Johnson-code argument. -/
def complementCoordinateEquiv {n w : ℕ} (x : JohnsonSphere n w) :
    ComplementCoordinates x ≃ Fin (n - w) :=
  Fintype.equivOfCardEq (by
    have hx : (MetricCodes.wordSupport (x : BinaryWord n)).card = w := by
      simpa only [MetricCodes.binaryWeight_eq_card_wordSupport] using x.property
    rw [Fintype.card_coe, Fintype.card_fin,
      Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp only [Finset.card_univ, Fintype.card_fin, hx])

/-- The harmonic fibre index used in the Johnson-code argument. -/
abbrev HarmonicFibreIndex (n w p q : ℕ) :=
  Fin (MetricCodes.hammingFibreDimension w p) ×
    Fin (MetricCodes.hammingFibreDimension (n - w) q)

/-- The harmonic fibre index equiv used in the Johnson-code argument. -/
def harmonicFibreIndexEquiv (n w p q : ℕ) :
    HarmonicFibreIndex n w p q ≃
      Fin (MetricCodes.johnsonFibreDimension n w p q) :=
  Fintype.equivOfCardEq (by
    change
      Fintype.card
          (Fin (MetricCodes.booleanHarmonicDimension w p) ×
            Fin (MetricCodes.booleanHarmonicDimension (n - w) q)) =
        Fintype.card
          (Fin (MetricCodes.booleanHarmonicDimension w p *
            MetricCodes.booleanHarmonicDimension (n - w) q))
    rw [Fintype.card_prod]
    simp only [Fintype.card_fin])

/-- The shell window index used in the Johnson-code argument. -/
abbrev ShellWindowIndex (n p q L : ℕ) :=
  Σ i : Fin (L - (p + q) + 1),
    Fin (MetricCodes.booleanHarmonicDimension n (p + q + i.val))

theorem shellWindowIndex_card (n p q L : ℕ)
    (hfirst : p + q ≤ L) :
    Fintype.card (ShellWindowIndex n p q L) =
      MetricCodes.johnsonAmbientDimension n (p + q) L := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  unfold MetricCodes.johnsonAmbientDimension
  refine Finset.sum_bij (fun i _ => p + q + i.val) ?_ ?_ ?_ ?_
  · intro i _
    apply Finset.mem_Icc.mpr
    constructor
    · omega
    · have hi := i.isLt
      omega
  · intro i _ j _ heq
    apply Fin.ext
    omega
  · intro j hj
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hj
    refine ⟨⟨j - (p + q), by omega⟩,
      Finset.mem_univ _, ?_⟩
    change p + q + (j - (p + q)) = j
    exact Nat.add_sub_of_le hlo
  · intro i _
    rfl

/-- The shell window index equiv used in the Johnson-code argument. -/
def shellWindowIndexEquiv (n p q L : ℕ)
    (hfirst : p + q ≤ L) :
    ShellWindowIndex n p q L ≃
      Fin (MetricCodes.johnsonAmbientDimension n (p + q) L) :=
  Fintype.equivOfCardEq (by
    simpa only [Fintype.card_fin] using
      shellWindowIndex_card n p q L hfirst)

/-- The index used in the Johnson-code argument. -/
abbrev Index (p q L : ℕ) := Fin (L - (p + q) + 1)

/-- The space used in the Johnson-code argument. -/
abbrev Space (p q L : ℕ) := EuclideanSpace ℝ (Index p q L)

/-- The matrix used in the Johnson-code argument. -/
def matrix (n w p q L : ℕ) :
    Matrix (Index p q L) (Index p q L) ℝ :=
  MetricCodes.johnsonJacobiMatrix n w p q L

theorem matrix_hermitian (n w p q L : ℕ) :
    (matrix n w p q L).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have h := congrArg
    (fun A : Matrix (Index p q L) (Index p q L) ℝ => A i j)
    (MetricCodes.johnsonJacobiMatrix_symmetric n w p q L)
  simpa only [matrix, star_trivial, Matrix.transpose_apply] using h

/-- The operator used in the Johnson-code argument. -/
def operator (n w p q L : ℕ) : Space p q L →ₗ[ℝ] Space p q L :=
  Matrix.toEuclideanLin (matrix n w p q L)

theorem operator_isSymmetric (n w p q L : ℕ) :
    (operator n w p q L).IsSymmetric := by
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (matrix_hermitian n w p q L)

/-- The continuous operator used in the Johnson-code argument. -/
def continuousOperator (n w p q L : ℕ) :
    Space p q L →L[ℝ] Space p q L :=
  LinearMap.toContinuousLinearMap (operator n w p q L)

/-- The rayleigh used in the Johnson-code argument. -/
def rayleigh (n w p q L : ℕ) (x : Space p q L) : ℝ :=
  (continuousOperator n w p q L).rayleighQuotient x

theorem rayleigh_bddAbove (n w p q L : ℕ) :
    BddAbove (Set.range
      (fun x : {x : Space p q L // x ≠ 0} =>
        rayleigh n w p q L x)) := by
  refine ⟨‖continuousOperator n w p q L‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (le_abs_self _).trans
    ((continuousOperator n w p q L).rayleighQuotient_le_norm x)

/-- The top eigenvalue used in the Johnson-code argument. -/
def topEigenvalue (n w p q L : ℕ) : ℝ :=
  ⨆ x : {x : Space p q L // x ≠ 0}, rayleigh n w p q L x

theorem rayleigh_le_top (n w p q L : ℕ)
    (x : Space p q L) (hx : x ≠ 0) :
    rayleigh n w p q L x ≤ topEigenvalue n w p q L := by
  exact le_ciSup (rayleigh_bddAbove n w p q L) ⟨x, hx⟩

theorem topEigenvalue_hasEigenvalue (n w p q L : ℕ) :
    Module.End.HasEigenvalue (operator n w p q L)
      (topEigenvalue n w p q L) := by
  have h :=
    (operator_isSymmetric n w p q L).hasEigenvalue_iSup_of_finiteDimensional
  simpa only [topEigenvalue, ne_eq, rayleigh, ContinuousLinearMap.rayleighQuotient,
    continuousOperator, ContinuousLinearMap.reApplyInnerSelf_apply,
    LinearMap.coe_toContinuousLinearMap', RCLike.re_to_real, Order.lt_one_iff,
    Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one, Real.ringHom_apply] using h

theorem exists_topEigenvector (n w p q L : ℕ) :
    ∃ x : Space p q L, x ≠ 0 ∧
      operator n w p q L x = topEigenvalue n w p q L • x := by
  obtain ⟨x, hx⟩ :=
    (topEigenvalue_hasEigenvalue n w p q L).exists_hasEigenvector
  exact ⟨x, hx.2, hx.apply_eq_smul⟩

theorem rayleigh_eq_inner (n w p q L : ℕ) (x : Space p q L) :
    rayleigh n w p q L x =
      @inner ℝ (Space p q L) _ (operator n w p q L x) x / ‖x‖ ^ 2 := by
  rfl

/-- Data encoding the admissible degrees construction. -/
structure AdmissibleDegrees (n w p q L : ℕ) : Prop where
  weight_pos : 0 < w
  weight_lt : w < n
  weight_half : 2 * w ≤ n
  support_half : 2 * p ≤ w
  complement_half : 2 * q ≤ n - w
  first_le : p + q ≤ L
  last_le : L ≤ MetricCodes.johnsonLastDegree n w p q

theorem AdmissibleDegrees.terminal_le_weight
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L) :
    L ≤ w := by
  exact h.last_le.trans (by
    unfold MetricCodes.johnsonLastDegree
    exact min_le_left _ _)

theorem AdmissibleDegrees.terminal_le_half
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L) :
    L ≤ n / 2 := by
  have hL := h.terminal_le_weight
  have hw := h.weight_half
  omega

theorem booleanHarmonicDimension_pos {n k : ℕ}
    (hk : 2 * k ≤ n) :
    0 < MetricCodes.booleanHarmonicDimension n k := by
  cases k with
  | zero => simp only [booleanHarmonicDimension, Order.lt_one_iff]
  | succ j =>
      change 0 < n.choose (j + 1) - n.choose j
      apply Nat.sub_pos_of_lt
      have hchoose : 0 < n.choose j := Nat.choose_pos (by omega)
      have hfactor : j + 1 < n - j := by omega
      have hmul :
          n.choose j * (j + 1) < n.choose j * (n - j) :=
        Nat.mul_lt_mul_of_pos_left hfactor hchoose
      have hmul' :
          n.choose j * (j + 1) < n.choose (j + 1) * (j + 1) := by
        calc
          n.choose j * (j + 1) < n.choose j * (n - j) := hmul
          _ = n.choose (j + 1) * (j + 1) :=
            (Nat.choose_succ_right_eq n j).symm
      exact (Nat.mul_lt_mul_right (by omega : 0 < j + 1)).mp hmul'

theorem AdmissibleDegrees.fibreDimension_pos
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L) :
    0 < MetricCodes.johnsonFibreDimension n w p q := by
  unfold MetricCodes.johnsonFibreDimension
  exact Nat.mul_pos
    (booleanHarmonicDimension_pos h.support_half)
    (booleanHarmonicDimension_pos h.complement_half)

theorem ambientDimension_eq {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L) :
    MetricCodes.johnsonAmbientDimension n (p + q) L =
      n.choose L - MetricCodes.precedingBinomial n (p + q) := by
  exact MetricCodes.johnsonAmbientDimension_eq_of_fibre n p q L
    h.first_le h.terminal_le_half

theorem zonalDiagonal_eq {n w j : ℕ}
    (hw : 0 < w) (hhalf : 2 * w < n) (hj : j ≤ w) :
    MetricCodes.johnsonZonalDiagonal n w j =
      MetricCodes.johnsonM n w ^ 2 * (j : ℝ) *
        ((n : ℝ) - (j : ℝ) + 1) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ) *
          MetricCodes.johnsonJ n j * (MetricCodes.johnsonJ n j + 1)) := by
  have hwn : w < n := by omega
  have hhalf' : (2 : ℝ) * (w : ℝ) < (n : ℝ) := by
    exact_mod_cast hhalf
  have hj' : (j : ℝ) ≤ (w : ℝ) := by
    exact_mod_cast hj
  have hsmall : (2 : ℝ) * (j : ℝ) < (n : ℝ) := by
    nlinarith
  have hw' : (w : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hw
  have hN' : (n : ℝ) - (w : ℝ) ≠ 0 := by
    have hwn' : (w : ℝ) < (n : ℝ) := by exact_mod_cast hwn
    linarith
  have hJ : 0 < MetricCodes.johnsonJ n j := by
    unfold MetricCodes.johnsonJ
    nlinarith
  have hJone : MetricCodes.johnsonJ n j + 1 ≠ 0 := by
    linarith
  have hD :
      (n : ℝ) * 2 - (n : ℝ) * (j : ℝ) * 4 +
          (n : ℝ) ^ 2 - (j : ℝ) * 4 + (j : ℝ) ^ 2 * 4 ≠ 0 := by
    have hfactor :
        (n : ℝ) * 2 - (n : ℝ) * (j : ℝ) * 4 +
            (n : ℝ) ^ 2 - (j : ℝ) * 4 + (j : ℝ) ^ 2 * 4 =
          ((n : ℝ) - 2 * (j : ℝ)) *
            ((n : ℝ) - 2 * (j : ℝ) + 2) := by
      ring
    rw [hfactor]
    exact (mul_pos (by linarith) (by linarith)).ne'
  unfold MetricCodes.johnsonZonalDiagonal MetricCodes.johnsonDiagonal
    MetricCodes.johnsonMu MetricCodes.johnsonM
    MetricCodes.johnsonJ1 MetricCodes.johnsonJ2
  rw [Nat.cast_sub (Nat.le_of_lt hwn)]
  field_simp [hw', hN', hJ.ne', hJone]
  unfold MetricCodes.johnsonJ
  ring

theorem zonalDiagonal_pos {n w j : ℕ}
    (hw : 0 < w) (hhalf : 2 * w < n)
    (hj : 0 < j) (hjw : j ≤ w) :
    0 < MetricCodes.johnsonZonalDiagonal n w j := by
  rw [zonalDiagonal_eq hw hhalf hjw]
  have hwn : w < n := by omega
  have hhalf' : (2 : ℝ) * (w : ℝ) < (n : ℝ) := by
    exact_mod_cast hhalf
  have hjw' : (j : ℝ) ≤ (w : ℝ) := by
    exact_mod_cast hjw
  have hM : 0 < MetricCodes.johnsonM n w := by
    unfold MetricCodes.johnsonM
    nlinarith
  have hJ : 0 < MetricCodes.johnsonJ n j := by
    unfold MetricCodes.johnsonJ
    nlinarith
  have hN : 0 < n - w := Nat.sub_pos_of_lt hwn
  have hlast : 0 < (n : ℝ) - (j : ℝ) + 1 := by
    nlinarith
  positivity

theorem associatedEdge_pos {n w p q j : ℕ}
    (hw : 0 < w) (hhalf : 2 * w < n)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (hfirst : p + q ≤ j)
    (hlast : j < MetricCodes.johnsonLastDegree n w p q) :
    0 < MetricCodes.johnsonEdge n w p q j := by
  have hwn : w < n := by omega
  have hN : 0 < n - w := Nat.sub_pos_of_lt hwn
  have hjw : j < w := by
    exact lt_of_lt_of_le hlast (by
      unfold MetricCodes.johnsonLastDegree
      exact min_le_left _ _)
  have hjleft : j < w - p + q := by
    apply lt_of_lt_of_le hlast
    unfold MetricCodes.johnsonLastDegree
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hjright : j < n - w + p - q := by
    apply lt_of_lt_of_le hlast
    unfold MetricCodes.johnsonLastDegree
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hhalf' : (2 : ℝ) * (w : ℝ) < (n : ℝ) := by
    exact_mod_cast hhalf
  have hjw' : (j : ℝ) < (w : ℝ) := by
    exact_mod_cast hjw
  have hfirst' : (p : ℝ) + (q : ℝ) ≤ (j : ℝ) := by
    exact_mod_cast hfirst
  have hjleft' :
      (j : ℝ) < (w : ℝ) - (p : ℝ) + (q : ℝ) := by
    have hcast : (j : ℝ) < ((w - p + q : ℕ) : ℝ) := by
      exact_mod_cast hjleft
    simpa only [Nat.cast_add, Nat.cast_sub (by omega : p ≤ w)]
      using hcast
  have hjright' :
      (j : ℝ) < (n : ℝ) - (w : ℝ) + (p : ℝ) - (q : ℝ) := by
    have hcast : (j : ℝ) < ((n - w + p - q : ℕ) : ℝ) := by
      exact_mod_cast hjright
    simpa only [Nat.cast_sub (by omega : q ≤ n - w + p),
      Nat.cast_add, Nat.cast_sub (by omega : w ≤ n)] using hcast
  have hJ : 0 < MetricCodes.johnsonJ n j := by
    unfold MetricCodes.johnsonJ
    nlinarith
  have hM : 0 < MetricCodes.johnsonM n w := by
    unfold MetricCodes.johnsonM
    nlinarith
  have hJminusM : 0 < MetricCodes.johnsonJ n j - MetricCodes.johnsonM n w := by
    unfold MetricCodes.johnsonJ MetricCodes.johnsonM
    linarith
  have hJplusM : 0 < MetricCodes.johnsonJ n j + MetricCodes.johnsonM n w := by
    linarith
  have hJminusDelta :
      0 < MetricCodes.johnsonJ n j - MetricCodes.johnsonDelta n w p q := by
    unfold MetricCodes.johnsonJ MetricCodes.johnsonDelta
      MetricCodes.johnsonJ2 MetricCodes.johnsonJ1
    rw [Nat.cast_sub (by omega : w ≤ n)]
    linarith
  have hJplusDelta :
      0 < MetricCodes.johnsonJ n j + MetricCodes.johnsonDelta n w p q := by
    unfold MetricCodes.johnsonJ MetricCodes.johnsonDelta
      MetricCodes.johnsonJ2 MetricCodes.johnsonJ1
    rw [Nat.cast_sub (by omega : w ≤ n)]
    linarith
  have hSigmaMinus :
      0 < MetricCodes.johnsonSigma n w p q + 1 -
        MetricCodes.johnsonJ n j := by
    unfold MetricCodes.johnsonSigma MetricCodes.johnsonJ1 MetricCodes.johnsonJ2
      MetricCodes.johnsonJ
    rw [Nat.cast_sub (by omega : w ≤ n)]
    linarith
  have hSigmaPlus :
      0 < MetricCodes.johnsonSigma n w p q + 1 +
        MetricCodes.johnsonJ n j := by
    linarith
  have hJM :
      0 < MetricCodes.johnsonJ n j ^ 2 - MetricCodes.johnsonM n w ^ 2 := by
    nlinarith [mul_pos hJminusM hJplusM]
  have hJDelta :
      0 < MetricCodes.johnsonJ n j ^ 2 -
        MetricCodes.johnsonDelta n w p q ^ 2 := by
    nlinarith [mul_pos hJminusDelta hJplusDelta]
  have hSigma :
      0 < (MetricCodes.johnsonSigma n w p q + 1) ^ 2 -
        MetricCodes.johnsonJ n j ^ 2 := by
    nlinarith [mul_pos hSigmaMinus hSigmaPlus]
  have hjstep : (j : ℝ) + 1 ≤ (w : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hjw
  have hhalfstep :
      (2 : ℝ) * (w : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast (show 2 * w + 1 ≤ n by omega)
  have hdenleft : 0 < 2 * MetricCodes.johnsonJ n j - 1 := by
    unfold MetricCodes.johnsonJ
    nlinarith
  have hdenright : 0 < 2 * MetricCodes.johnsonJ n j + 1 := by
    linarith
  have hnu : 0 < MetricCodes.johnsonNu n w p q j := by
    unfold MetricCodes.johnsonNu
    apply div_pos
    · exact Real.sqrt_pos.mpr
        (mul_pos (mul_pos hJM hJDelta) hSigma)
    · exact mul_pos (mul_pos (by norm_num) hJ)
        (Real.sqrt_pos.mpr (mul_pos hdenleft hdenright))
  unfold MetricCodes.johnsonEdge
  exact div_pos
    (mul_pos (by exact_mod_cast (show 0 < n by omega)) hnu)
    (mul_pos (by exact_mod_cast hw)
      (by exact_mod_cast hN))

theorem zonalEdge_pos {n w j : ℕ}
    (hw : 0 < w) (hhalf : 2 * w < n) (hj : j < w) :
    0 < MetricCodes.johnsonZonalEdge n w j := by
  have hlast : MetricCodes.johnsonLastDegree n w 0 0 = w := by
    simp only [johnsonLastDegree, tsub_zero, add_zero, min_eq_left (by omega : w ≤ n - w), min_self]
  unfold MetricCodes.johnsonZonalEdge
  apply associatedEdge_pos hw hhalf (by omega) (by omega)
    (Nat.zero_le j)
  simpa only [hlast] using hj

theorem hattedDiagonal_nonneg {n w p q j : ℕ}
    (hw : 0 < w) (hhalf : 2 * w < n) (hj : j ≤ w) :
    0 ≤ MetricCodes.johnsonHattedDiagonal n w p q j := by
  by_cases hz : j = 0
  · subst j
    simp only [johnsonHattedDiagonal, ↓reduceIte, Std.le_refl]
  · exact MetricCodes.johnsonHattedDiagonal_nonneg
      (zonalDiagonal_pos hw hhalf (Nat.pos_of_ne_zero hz) hj)

theorem hattedEdge_pos {n w p q j : ℕ}
    (hw : 0 < w) (hhalf : 2 * w < n)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (hfirst : p + q ≤ j)
    (hlast : j < MetricCodes.johnsonLastDegree n w p q) :
    0 < MetricCodes.johnsonHattedEdge n w p q j := by
  have hedge := associatedEdge_pos hw hhalf hp hq hfirst hlast
  have hjw : j < w :=
    lt_of_lt_of_le hlast (by
      unfold MetricCodes.johnsonLastDegree
      exact min_le_left _ _)
  unfold MetricCodes.johnsonHattedEdge
  exact div_pos (sq_pos_of_pos hedge)
    (zonalEdge_pos hw hhalf hjw)

theorem matrix_entry_nonneg {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (i j : Index p q L) :
    0 ≤ matrix n w p q L i j := by
  have hfirst := h.first_le
  have hiL : p + q + i.val ≤ L := by
    have hi := i.isLt
    omega
  have hjL : p + q + j.val ≤ L := by
    have hj := j.isLt
    omega
  unfold matrix MetricCodes.johnsonJacobiMatrix
  split_ifs with hdiag hforward hbackward
  · exact hattedDiagonal_nonneg h.weight_pos hstrict
      (hiL.trans h.terminal_le_weight)
  · apply (hattedEdge_pos h.weight_pos hstrict
      h.support_half h.complement_half (by omega) ?_).le
    apply lt_of_lt_of_le (by omega : p + q + i.val < L)
    exact h.last_le
  · apply (hattedEdge_pos h.weight_pos hstrict
      h.support_half h.complement_half (by omega) ?_).le
    apply lt_of_lt_of_le (by omega : p + q + j.val < L)
    exact h.last_le
  · exact le_rfl

/-- The coordinate abs used in the Johnson-code argument. -/
def coordinateAbs (p q L : ℕ)
    (x : Space p q L) : Space p q L :=
  WithLp.toLp 2 (fun i : Index p q L => |x i|)

theorem coordinateAbs_norm (p q L : ℕ)
    (x : Space p q L) :
    ‖coordinateAbs p q L x‖ = ‖x‖ := by
  have hsquare : ‖coordinateAbs p q L x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq,
      EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    simp only [coordinateAbs, sq_abs]
  nlinarith [norm_nonneg (coordinateAbs p q L x), norm_nonneg x]

theorem coordinateAbs_ne_zero (p q L : ℕ)
    {x : Space p q L} (hx : x ≠ 0) :
    coordinateAbs p q L x ≠ 0 := by
  intro habs
  have hnorm := coordinateAbs_norm p q L x
  rw [habs, norm_zero] at hnorm
  exact hx (norm_eq_zero.mp hnorm.symm)

theorem inner_le_inner_coordinateAbs {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (x : Space p q L) :
    @inner ℝ (Space p q L) _ (operator n w p q L x) x ≤
      @inner ℝ (Space p q L) _
        (operator n w p q L (coordinateAbs p q L x))
        (coordinateAbs p q L x) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [Real.inner_apply]
  change
    (∑ i : Index p q L,
      (∑ j : Index p q L, matrix n w p q L i j * x j) * x i) ≤
    (∑ i : Index p q L,
      (∑ j : Index p q L,
        matrix n w p q L i j * |x j|) * |x i|)
  simp_rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have hentry := matrix_entry_nonneg h hstrict i j
  have hproduct : x j * x i ≤ |x j| * |x i| := by
    calc
      x j * x i ≤ |x j * x i| := le_abs_self _
      _ = |x j| * |x i| := abs_mul _ _
  calc
    matrix n w p q L i j * x j * x i =
        matrix n w p q L i j * (x j * x i) := by ring
    _ ≤ matrix n w p q L i j * (|x j| * |x i|) :=
      mul_le_mul_of_nonneg_left hproduct hentry
    _ = matrix n w p q L i j * |x j| * |x i| := by ring

theorem rayleigh_le_coordinateAbs {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (x : Space p q L) :
    rayleigh n w p q L x ≤
      rayleigh n w p q L (coordinateAbs p q L x) := by
  rw [rayleigh_eq_inner, rayleigh_eq_inner, coordinateAbs_norm]
  gcongr
  exact inner_le_inner_coordinateAbs h hstrict x

theorem rayleigh_eq_of_eigenvector
    (n w p q L : ℕ) (x : Space p q L) (hx : x ≠ 0)
    (eigenvalue : ℝ)
    (heigen : operator n w p q L x = eigenvalue • x) :
    rayleigh n w p q L x = eigenvalue := by
  rw [rayleigh_eq_inner, heigen,
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hnorm : ‖x‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  field_simp [hnorm]

theorem coordinateAbs_top_rayleigh {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (x : Space p q L) (hx : x ≠ 0)
    (heigen :
      operator n w p q L x = topEigenvalue n w p q L • x) :
    rayleigh n w p q L (coordinateAbs p q L x) =
      topEigenvalue n w p q L := by
  have hbelow := rayleigh_le_coordinateAbs h hstrict x
  have habove := rayleigh_le_top n w p q L
    (coordinateAbs p q L x) (coordinateAbs_ne_zero p q L hx)
  rw [rayleigh_eq_of_eigenvector n w p q L x hx
    (topEigenvalue n w p q L) heigen] at hbelow
  exact le_antisymm habove hbelow

theorem exists_nonnegative_topEigenvector {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n) :
    ∃ x : Space p q L,
      x ≠ 0 ∧
        operator n w p q L x = topEigenvalue n w p q L • x ∧
        ∀ i : Index p q L, 0 ≤ x i := by
  obtain ⟨x, hx, heigen⟩ := exists_topEigenvector n w p q L
  let y : Space p q L := coordinateAbs p q L x
  have hy : y ≠ 0 := coordinateAbs_ne_zero p q L hx
  have hyray : rayleigh n w p q L y = topEigenvalue n w p q L :=
    coordinateAbs_top_rayleigh h hstrict x hx heigen
  have hself : IsSelfAdjoint (continuousOperator n w p q L) :=
    (operator_isSymmetric n w p q L).isSelfAdjoint
  have hmax :
      IsMaxOn (continuousOperator n w p q L).reApplyInnerSelf
        (Metric.sphere (0 : Space p q L) ‖y‖) y := by
    intro z hz
    have hnorm : ‖z‖ = ‖y‖ := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
    have hznonzero : z ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hnorm
      exact hy (norm_eq_zero.mp hnorm.symm)
    have hray := rayleigh_le_top n w p q L z hznonzero
    rw [← hyray] at hray
    change
      (continuousOperator n w p q L).reApplyInnerSelf z / ‖z‖ ^ 2 ≤
        (continuousOperator n w p q L).reApplyInnerSelf y / ‖y‖ ^ 2
      at hray
    rw [hnorm] at hray
    have hnormpos : 0 < ‖y‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr hy)
    exact (div_le_div_iff_of_pos_right hnormpos).mp hray
  have heigeny := hself.hasEigenvector_of_isMaxOn hy hmax
  refine ⟨y, hy, ?_, fun i => abs_nonneg (x i)⟩
  have happly := heigeny.apply_eq_smul
  simpa only [topEigenvalue, ne_eq, rayleigh, continuousOperator,
    LinearMap.coe_toContinuousLinearMap, Real.ringHom_apply] using happly

theorem exists_nonnegative_unit_topEigenvector
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n) :
    ∃ x : Space p q L,
      ‖x‖ = 1 ∧
        operator n w p q L x = topEigenvalue n w p q L • x ∧
        ∀ i : Index p q L, 0 ≤ x i := by
  obtain ⟨x, hx, heigen, hnonneg⟩ :=
    exists_nonnegative_topEigenvector h hstrict
  have hnormpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  refine ⟨‖x‖⁻¹ • x, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hnormpos)]
    exact inv_mul_cancel₀ (ne_of_gt hnormpos)
  · rw [map_smul, heigen]
    exact smul_comm _ _ _
  · intro i
    change 0 ≤ ‖x‖⁻¹ * x i
    exact mul_nonneg (inv_nonneg.mpr hnormpos.le) (hnonneg i)

theorem matrix_adjacent_pos {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (i j : Index p q L)
    (hadjacent : i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    0 < matrix n w p q L i j := by
  have hi := i.isLt
  have hj := j.isLt
  rcases hadjacent with hforward | hbackward
  · have hnot : j.val + 1 ≠ i.val := by omega
    have hne : i ≠ j := by
      intro heq
      subst j
      omega
    have hlast : p + q + i.val <
        MetricCodes.johnsonLastDegree n w p q := by
      have hlt : p + q + i.val < L := by omega
      exact hlt.trans_le h.last_le
    simpa only [matrix, johnsonJacobiMatrix, hne, ↓reduceIte, hforward, gt_iff_lt] using
      hattedEdge_pos h.weight_pos hstrict h.support_half h.complement_half (show p + q ≤ p + q +
        i.val by omega) hlast
  · have hnot : i.val + 1 ≠ j.val := by omega
    have hne : i ≠ j := by
      intro heq
      subst j
      omega
    have hlast : p + q + j.val <
        MetricCodes.johnsonLastDegree n w p q := by
      have hlt : p + q + j.val < L := by omega
      exact hlt.trans_le h.last_le
    simpa only [matrix, johnsonJacobiMatrix, hne, ↓reduceIte, hnot, hbackward, gt_iff_lt] using
      hattedEdge_pos h.weight_pos hstrict h.support_half h.complement_half (show p + q ≤ p + q +
        j.val by omega) hlast

theorem nonnegative_eigenvector_zero_propagates
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L) (eigenvalue : ℝ)
    (heigen : operator n w p q L v = eigenvalue • v)
    (hnonnegative : ∀ i : Index p q L, 0 ≤ v i)
    (i j : Index p q L)
    (hzero : v i = 0)
    (hadjacent : i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    v j = 0 := by
  classical
  have hcoordinate :=
    congrArg (fun z : Space p q L => z i) heigen
  change
    (∑ r : Index p q L, matrix n w p q L i r * v r) =
      eigenvalue * v i at hcoordinate
  rw [hzero, mul_zero] at hcoordinate
  have hterms :
      ∀ r ∈ (Finset.univ : Finset (Index p q L)),
        0 ≤ matrix n w p q L i r * v r := by
    intro r _
    exact mul_nonneg
      (matrix_entry_nonneg h hstrict i r)
      (hnonnegative r)
  have hterm : matrix n w p q L i j * v j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hcoordinate
      j (Finset.mem_univ j)
  exact (mul_eq_zero.mp hterm).resolve_left
    (matrix_adjacent_pos h hstrict i j hadjacent).ne'

theorem nonnegative_eigenvector_coordinate_pos
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L) (eigenvalue : ℝ)
    (heigen : operator n w p q L v = eigenvalue • v)
    (hnonnegative : ∀ i : Index p q L, 0 ≤ v i)
    (hnonzero : v ≠ 0)
    (i : Index p q L) :
    0 < v i := by
  rcases (hnonnegative i).eq_or_lt with hzero | hpositive
  · exfalso
    apply hnonzero
    apply PiLp.ext
    intro j
    change v j = 0
    have hchain :
        ∀ distance : ℕ,
          ∀ j : Index p q L,
            Nat.dist i.val j.val = distance → v j = 0 := by
      intro distance
      induction distance using Nat.strong_induction_on with
      | h distance ih =>
          intro j hdistance
          by_cases hequal : i.val = j.val
          · have hij : i = j := Fin.ext hequal
            simpa only [hij] using hzero.symm
          · by_cases hforward : i.val < j.val
            · let previous : Index p q L :=
                ⟨j.val - 1, by have hj := j.isLt; omega⟩
              have hprevious_distance :
                  Nat.dist i.val previous.val < distance := by
                rw [Nat.dist_eq_sub_of_le
                  (show i.val ≤ previous.val by
                    dsimp [previous]
                    omega)]
                rw [Nat.dist_eq_sub_of_le
                  (Nat.le_of_lt hforward)] at hdistance
                dsimp [previous]
                omega
              have hprevious_zero : v previous = 0 :=
                ih (Nat.dist i.val previous.val)
                  hprevious_distance previous rfl
              exact nonnegative_eigenvector_zero_propagates
                h hstrict v eigenvalue heigen hnonnegative previous j
                hprevious_zero (Or.inl (by
                  dsimp [previous]
                  omega))
            · have hbackward : j.val < i.val := by omega
              let next : Index p q L :=
                ⟨j.val + 1, by have hi := i.isLt; omega⟩
              have hnext_distance :
                  Nat.dist i.val next.val < distance := by
                rw [Nat.dist_eq_sub_of_le_right
                  (show next.val ≤ i.val by
                    dsimp [next]
                    omega)]
                rw [Nat.dist_eq_sub_of_le_right
                  (Nat.le_of_lt hbackward)] at hdistance
                dsimp [next]
                omega
              have hnext_zero : v next = 0 :=
                ih (Nat.dist i.val next.val)
                  hnext_distance next rfl
              exact nonnegative_eigenvector_zero_propagates
                h hstrict v eigenvalue heigen hnonnegative next j
                hnext_zero (Or.inr (by
                  dsimp [next]))
    exact hchain (Nat.dist i.val j.val) j rfl
  · exact hpositive

theorem exists_positive_unit_topEigenvector
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n) :
    ∃ v : Space p q L,
      ‖v‖ = 1 ∧
        operator n w p q L v = topEigenvalue n w p q L • v ∧
        ∀ i : Index p q L, 0 < v i := by
  obtain ⟨v, hunit, heigen, hnonnegative⟩ :=
    exists_nonnegative_unit_topEigenvector h hstrict
  have hnonzero : v ≠ 0 := by
    intro hzero
    simp only [hzero, norm_zero, zero_ne_one] at hunit
  exact ⟨v, hunit, heigen, fun i =>
    nonnegative_eigenvector_coordinate_pos h hstrict
      v (topEigenvalue n w p q L)
      heigen hnonnegative hnonzero i⟩

theorem topEigenvalue_pos {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (hwindow : p + q < L) :
    0 < topEigenvalue n w p q L := by
  classical
  obtain ⟨v, hunit, heigen, hv⟩ :=
    exists_positive_unit_topEigenvector h hstrict
  let i : Index p q L := ⟨0, by omega⟩
  let j : Index p q L := ⟨1, by omega⟩
  have hentry : 0 < matrix n w p q L i j :=
    matrix_adjacent_pos h hstrict i j (Or.inl (by rfl))
  have hterms :
      ∀ r ∈ (Finset.univ : Finset (Index p q L)),
        0 ≤ matrix n w p q L i r * v r := by
    intro r _
    exact mul_nonneg
      (matrix_entry_nonneg h hstrict i r) (hv r).le
  have hsum :
      0 < ∑ r : Index p q L,
        matrix n w p q L i r * v r := by
    apply Finset.sum_pos' hterms
    exact ⟨j, Finset.mem_univ j, mul_pos hentry (hv j)⟩
  have hcoordinate :=
    congrArg (fun z : Space p q L => z i) heigen
  change
    (∑ r : Index p q L, matrix n w p q L i r * v r) =
      topEigenvalue n w p q L * v i at hcoordinate
  rw [hcoordinate] at hsum
  exact (mul_pos_iff_of_pos_right (hv i)).mp hsum

theorem johnsonWindowHarmonicDimension_pos
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L)
    (i : Index p q L) :
    0 < MetricCodes.booleanHarmonicDimension n (p + q + i.val) := by
  apply booleanHarmonicDimension_pos
  have hi := i.isLt
  have hfirst := h.first_le
  have hterminal := h.terminal_le_weight
  have hhalf := h.weight_half
  omega

/-- The johnson recurrence weight used in the Johnson-code argument. -/
def johnsonRecurrenceWeight
    (n _ p q L : ℕ) (v : Space p q L) (i : Index p q L) : ℝ :=
  Real.sqrt (MetricCodes.booleanHarmonicDimension n (p + q + i.val) : ℝ) *
    v i

/-- The johnson source channel coefficient used in the Johnson-code argument. -/
def johnsonSourceChannelCoefficient
    (n w p q L : ℕ) (m i : Index p q L) : ℝ :=
  matrix n w p q L m i *
    Real.sqrt (MetricCodes.booleanHarmonicDimension n (p + q + m.val) : ℝ) /
      Real.sqrt (MetricCodes.booleanHarmonicDimension n (p + q + i.val) : ℝ)

theorem johnsonSourceChannelCoefficient_mul_sqrt_dimension
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L)
    (m i : Index p q L) :
    johnsonSourceChannelCoefficient n w p q L m i *
        Real.sqrt
          (MetricCodes.booleanHarmonicDimension n (p + q + i.val) : ℝ) =
      matrix n w p q L m i *
        Real.sqrt
          (MetricCodes.booleanHarmonicDimension n (p + q + m.val) : ℝ) := by
  have hdimension :
      0 < (MetricCodes.booleanHarmonicDimension n (p + q + i.val) : ℝ) := by
    exact_mod_cast johnsonWindowHarmonicDimension_pos h i
  have hsqrt :
      Real.sqrt
        (MetricCodes.booleanHarmonicDimension n (p + q + i.val) : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr hdimension).ne'
  unfold johnsonSourceChannelCoefficient
  field_simp [hsqrt]

theorem johnsonSourceChannelCoefficient_nonneg
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n) (m i : Index p q L) :
    0 ≤ johnsonSourceChannelCoefficient n w p q L m i := by
  unfold johnsonSourceChannelCoefficient
  exact div_nonneg
    (mul_nonneg (matrix_entry_nonneg h hstrict m i)
      (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

theorem johnsonRecurrenceWeight_pos_of_pos
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L)
    (v : Space p q L) (hv : ∀ i : Index p q L, 0 < v i)
    (i : Index p q L) :
    0 < johnsonRecurrenceWeight n w p q L v i := by
  unfold johnsonRecurrenceWeight
  apply mul_pos
  · apply Real.sqrt_pos.mpr
    exact_mod_cast johnsonWindowHarmonicDimension_pos h i
  · exact hv i

theorem johnsonRecurrenceWeight_eigenrecurrence
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L)
    (v : Space p q L) (lam : ℝ)
    (heigen : operator n w p q L v = lam • v)
    (m : Index p q L) :
    (∑ i : Index p q L,
      johnsonSourceChannelCoefficient n w p q L m i *
        johnsonRecurrenceWeight n w p q L v i) =
      lam * johnsonRecurrenceWeight n w p q L v m := by
  classical
  have hcoordinate :=
    congrArg (fun z : Space p q L => z m) heigen
  change
    (∑ i : Index p q L, matrix n w p q L m i * v i) =
      lam * v m at hcoordinate
  calc
    (∑ i : Index p q L,
      johnsonSourceChannelCoefficient n w p q L m i *
        johnsonRecurrenceWeight n w p q L v i) =
      ∑ i : Index p q L,
        (matrix n w p q L m i * v i) *
          Real.sqrt
            (MetricCodes.booleanHarmonicDimension n (p + q + m.val) : ℝ) := by
            apply Finset.sum_congr rfl
            intro i _
            unfold johnsonRecurrenceWeight
            have hentry :=
              johnsonSourceChannelCoefficient_mul_sqrt_dimension h m i
            calc
              johnsonSourceChannelCoefficient n w p q L m i *
                  (Real.sqrt
                    (MetricCodes.booleanHarmonicDimension
                      n (p + q + i.val) : ℝ) * v i) =
                (johnsonSourceChannelCoefficient n w p q L m i *
                  Real.sqrt
                    (MetricCodes.booleanHarmonicDimension
                      n (p + q + i.val) : ℝ)) * v i := by
                    ring
              _ = (matrix n w p q L m i *
                    Real.sqrt
                      (MetricCodes.booleanHarmonicDimension
                        n (p + q + m.val) : ℝ)) * v i := by
                      rw [hentry]
              _ = (matrix n w p q L m i * v i) *
                    Real.sqrt
                      (MetricCodes.booleanHarmonicDimension
                        n (p + q + m.val) : ℝ) := by
                      ring
    _ = (∑ i : Index p q L,
          matrix n w p q L m i * v i) *
        Real.sqrt
          (MetricCodes.booleanHarmonicDimension n (p + q + m.val) : ℝ) := by
          rw [Finset.sum_mul]
    _ = lam * johnsonRecurrenceWeight n w p q L v m := by
          rw [hcoordinate]
          unfold johnsonRecurrenceWeight
          ring

/-- The johnson adjacent block coefficient used in the Johnson-code argument. -/
def johnsonAdjacentBlockCoefficient
    (n w p q L : ℕ) (v : Space p q L) (lam : ℝ)
    (target source : Index p q L) : ℝ :=
  Real.sqrt
    (johnsonSourceChannelCoefficient n w p q L source target *
      johnsonRecurrenceWeight n w p q L v target /
        (lam * johnsonRecurrenceWeight n w p q L v source))

theorem johnsonAdjacentBlockCoefficient_sq
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L) (hv : ∀ i : Index p q L, 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (target source : Index p q L) :
    johnsonAdjacentBlockCoefficient n w p q L v lam target source ^ 2 =
      johnsonSourceChannelCoefficient n w p q L source target *
        johnsonRecurrenceWeight n w p q L v target /
          (lam * johnsonRecurrenceWeight n w p q L v source) := by
  unfold johnsonAdjacentBlockCoefficient
  apply Real.sq_sqrt
  exact div_nonneg
    (mul_nonneg
      (johnsonSourceChannelCoefficient_nonneg h hstrict source target)
      (johnsonRecurrenceWeight_pos_of_pos h v hv target).le)
    (mul_pos hlam
      (johnsonRecurrenceWeight_pos_of_pos h v hv source)).le

theorem johnsonAdjacentBlockCoefficient_sq_sum
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L) (hv : ∀ i : Index p q L, 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen : operator n w p q L v = lam • v)
    (source : Index p q L) :
    (∑ target : Index p q L,
      johnsonAdjacentBlockCoefficient n w p q L v lam
        target source ^ 2) = 1 := by
  classical
  simp_rw [johnsonAdjacentBlockCoefficient_sq
    h hstrict v hv lam hlam]
  rw [← Finset.sum_div,
    johnsonRecurrenceWeight_eigenrecurrence
      h v lam heigen source]
  exact div_self
    (mul_pos hlam
      (johnsonRecurrenceWeight_pos_of_pos h v hv source)).ne'

private def johnsonRecurrenceNormalization
    (n w p q L : ℕ) (v : Space p q L) : ℝ :=
  ∑ i : Index p q L, johnsonRecurrenceWeight n w p q L v i

/-- The johnson fibre amplitude used in the Johnson-code argument. -/
def johnsonFibreAmplitude
    (n w p q L : ℕ) (v : Space p q L) (i : Index p q L) : ℝ :=
  Real.sqrt
    (johnsonRecurrenceWeight n w p q L v i /
      johnsonRecurrenceNormalization n w p q L v)

theorem johnsonRecurrenceNormalization_pos
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L)
    (v : Space p q L) (hv : ∀ i : Index p q L, 0 < v i) :
    0 < johnsonRecurrenceNormalization n w p q L v := by
  classical
  let i : Index p q L := ⟨0, by
    have hfirst := h.first_le
    omega⟩
  unfold johnsonRecurrenceNormalization
  apply Finset.sum_pos'
  · intro j _
    exact (johnsonRecurrenceWeight_pos_of_pos h v hv j).le
  · exact ⟨i, Finset.mem_univ i,
      johnsonRecurrenceWeight_pos_of_pos h v hv i⟩

theorem johnsonFibreAmplitude_sq
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L)
    (v : Space p q L) (hv : ∀ i : Index p q L, 0 < v i)
    (i : Index p q L) :
    johnsonFibreAmplitude n w p q L v i ^ 2 =
      johnsonRecurrenceWeight n w p q L v i /
        johnsonRecurrenceNormalization n w p q L v := by
  unfold johnsonFibreAmplitude
  apply Real.sq_sqrt
  exact div_nonneg
    (johnsonRecurrenceWeight_pos_of_pos h v hv i).le
    (johnsonRecurrenceNormalization_pos h v hv).le

theorem johnsonFibreAmplitude_sq_sum
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L)
    (v : Space p q L) (hv : ∀ i : Index p q L, 0 < v i) :
    (∑ i : Index p q L,
      johnsonFibreAmplitude n w p q L v i ^ 2) = 1 := by
  simp_rw [johnsonFibreAmplitude_sq h v hv]
  rw [← Finset.sum_div]
  change
    johnsonRecurrenceNormalization n w p q L v /
      johnsonRecurrenceNormalization n w p q L v = 1
  exact div_self (johnsonRecurrenceNormalization_pos h v hv).ne'

theorem johnsonFibreAmplitude_pos_of_pos
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L)
    (v : Space p q L) (hv : ∀ i : Index p q L, 0 < v i)
    (i : Index p q L) :
    0 < johnsonFibreAmplitude n w p q L v i := by
  unfold johnsonFibreAmplitude
  apply Real.sqrt_pos.mpr
  exact div_pos
    (johnsonRecurrenceWeight_pos_of_pos h v hv i)
    (johnsonRecurrenceNormalization_pos h v hv)

theorem johnsonAdjacentBlockCoefficient_amplitude_identity
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L) (hv : ∀ i : Index p q L, 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (target source : Index p q L) :
    johnsonAdjacentBlockCoefficient n w p q L v lam target source *
        johnsonFibreAmplitude n w p q L v target *
        Real.sqrt
          (johnsonSourceChannelCoefficient n w p q L source target) =
      johnsonAdjacentBlockCoefficient n w p q L v lam target source ^ 2 *
        Real.sqrt lam * johnsonFibreAmplitude n w p q L v source := by
  have hcoefficient :=
    johnsonSourceChannelCoefficient_nonneg h hstrict source target
  have hsource :=
    johnsonRecurrenceWeight_pos_of_pos h v hv source
  have hnormal := johnsonRecurrenceNormalization_pos h v hv
  have hleft :
      0 ≤ johnsonAdjacentBlockCoefficient n w p q L v lam target source *
        johnsonFibreAmplitude n w p q L v target *
        Real.sqrt
          (johnsonSourceChannelCoefficient n w p q L source target) := by
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _)
        (johnsonFibreAmplitude_pos_of_pos h v hv target).le)
      (Real.sqrt_nonneg _)
  have hright :
      0 ≤
        johnsonAdjacentBlockCoefficient n w p q L v lam target source ^ 2 *
          Real.sqrt lam * johnsonFibreAmplitude n w p q L v source := by
    exact mul_nonneg
      (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))
      (johnsonFibreAmplitude_pos_of_pos h v hv source).le
  have hsquare :
      (johnsonAdjacentBlockCoefficient n w p q L v lam target source *
        johnsonFibreAmplitude n w p q L v target *
        Real.sqrt
          (johnsonSourceChannelCoefficient
            n w p q L source target)) ^ 2 =
      (johnsonAdjacentBlockCoefficient n w p q L v lam target source ^ 2 *
        Real.sqrt lam * johnsonFibreAmplitude n w p q L v source) ^ 2 := by
    simp only [mul_pow]
    rw [johnsonAdjacentBlockCoefficient_sq
      h hstrict v hv lam hlam target source,
      johnsonFibreAmplitude_sq h v hv target,
      Real.sq_sqrt hcoefficient,
      Real.sq_sqrt hlam.le,
      johnsonFibreAmplitude_sq h v hv source]
    field_simp [hlam.ne', hsource.ne', hnormal.ne']
  nlinarith

theorem johnsonAdjacentBlockCoefficient_amplitude_sum
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L) (hv : ∀ i : Index p q L, 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen : operator n w p q L v = lam • v)
    (source : Index p q L) :
    (∑ target : Index p q L,
      johnsonAdjacentBlockCoefficient n w p q L v lam target source *
        johnsonFibreAmplitude n w p q L v target *
        Real.sqrt
          (johnsonSourceChannelCoefficient
            n w p q L source target)) =
      Real.sqrt lam * johnsonFibreAmplitude n w p q L v source := by
  simp_rw [johnsonAdjacentBlockCoefficient_amplitude_identity
    h hstrict v hv lam hlam]
  rw [← Finset.sum_mul, ← Finset.sum_mul,
    johnsonAdjacentBlockCoefficient_sq_sum
      h hstrict v hv lam hlam heigen source]
  simp only [one_mul]

/-- Data encoding the projection gram construction. -/
structure ProjectionGram (n w p q L : ℕ) where
  /-- The projections component. -/
  projections :
    MetricCodes.ProjectionFamily (JohnsonSphere n w)
      (MetricCodes.johnsonAmbientDimension n (p + q) L)
      (MetricCodes.johnsonFibreDimension n w p q)
  /-- The feature component. -/
  feature : JohnsonSphere n w →
    EuclideanSpace ℝ
      (Fin (n * MetricCodes.johnsonAmbientDimension n (p + q) L *
        MetricCodes.johnsonAmbientDimension n (p + q) L))
  gram : ∀ x y : JohnsonSphere n w,
    ⟪feature x, feature y⟫_ℝ =
      (correlation x y - topEigenvalue n w p q L) *
        projections.overlap x y

theorem finite_bound_of_projection_gram
    {n w p q L d : ℕ}
    (hdegree : AdmissibleDegrees n w p q L)
    (hd : 0 < d)
    (data : ProjectionGram n w p q L)
    (C : Finset (JohnsonSphere n w)) (hC : IsCode d C)
    (hgap : threshold n w d < topEigenvalue n w p q L) :
    (C.card : ℝ) ≤
      ((1 - threshold n w d) /
        (topEigenvalue n w p q L - threshold n w d)) *
          ((MetricCodes.johnsonAmbientDimension n (p + q) L : ℝ) /
            (MetricCodes.johnsonFibreDimension n w p q : ℝ)) := by
  apply MetricCodes.projection_certificate data.projections C
    correlation data.feature hdegree.fibreDimension_pos
    (threshold_lt_one hdegree.weight_pos hdegree.weight_lt hd) hgap
  · intro x _
    exact correlation_self x
  · intro x hx y hy hxy
    exact correlation_le_threshold_of_code hdegree.weight_pos
      hdegree.weight_lt hC hx hy hxy
  · intro x _ y _
    exact data.gram x y

theorem finite_shellCodeNumber_bound_of_projection_gram
    {n w p q L d : ℕ}
    (hdegree : AdmissibleDegrees n w p q L)
    (hd : 0 < d)
    (data : ProjectionGram n w p q L)
    (hgap : threshold n w d < topEigenvalue n w p q L) :
    (shellCodeNumber n w d : ℝ) ≤
      ((1 - threshold n w d) /
        (topEigenvalue n w p q L - threshold n w d)) *
          ((MetricCodes.johnsonAmbientDimension n (p + q) L : ℝ) /
            (MetricCodes.johnsonFibreDimension n w p q : ℝ)) := by
  obtain ⟨C, hweight, hC, hcard⟩ := exists_shellCodeNumber n w d
  have hbound := finite_bound_of_projection_gram hdegree hd data
    (asSubtype C hweight) (isCode_asSubtype C hweight hC) hgap
  rw [card_asSubtype, hcard] at hbound
  exact hbound

theorem finite_binaryCodeNumber_bound_of_projection_gram
    {n w p q L d : ℕ}
    (hdegree : AdmissibleDegrees n w p q L)
    (hd : 0 < d)
    (data : ProjectionGram n w p q L)
    (hgap : threshold n w d < topEigenvalue n w p q L) :
    (binaryCodeNumber n d : ℝ) ≤
      ((2 : ℝ) ^ n / (n.choose w : ℝ)) *
        (((1 - threshold n w d) /
          (topEigenvalue n w p q L - threshold n w d)) *
            ((MetricCodes.johnsonAmbientDimension n (p + q) L : ℝ) /
              (MetricCodes.johnsonFibreDimension n w p q : ℝ))) := by
  have hfactor : 0 ≤ (2 : ℝ) ^ n / (n.choose w : ℝ) := by
    exact div_nonneg (by positivity) (Nat.cast_nonneg _)
  calc
    (binaryCodeNumber n d : ℝ) ≤
        ((2 : ℝ) ^ n / (n.choose w : ℝ)) *
          (shellCodeNumber n w d : ℝ) :=
      bassalygo_elias_real hdegree.weight_lt.le
    _ ≤ ((2 : ℝ) ^ n / (n.choose w : ℝ)) *
        (((1 - threshold n w d) /
          (topEigenvalue n w p q L - threshold n w d)) *
            ((MetricCodes.johnsonAmbientDimension n (p + q) L : ℝ) /
              (MetricCodes.johnsonFibreDimension n w p q : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (finite_shellCodeNumber_bound_of_projection_gram
          hdegree hd data hgap)
        hfactor

/-- The centered eta used in the Johnson-code argument. -/
def centeredEta (α β γ : ℝ) : ℝ :=
  1 - 2 * α + 2 * β - 2 * γ

/-- The spectral limit used in the Johnson-code argument. -/
def spectralLimit (α β γ u : ℝ) : ℝ :=
  let z := (1 - 2 * u)
  let m := (1 - 2 * α)
  let σ := (1 - 2 * β - 2 * γ)
  let η := centeredEta α β γ
  (σ * η - m * z ^ 2) ^ 2 /
      (z ^ 2 * (1 - m ^ 2) * (1 - z ^ 2)) +
    ((z ^ 2 - η ^ 2) * (σ ^ 2 - z ^ 2)) /
      (z ^ 2 * (1 - m ^ 2) * Real.sqrt (1 - z ^ 2))

theorem sqrt_one_sub_centeredDegree_sq {u : ℝ}
    (hu : 0 < u) (hhalf : u < (1 : ℝ) / 2) :
    Real.sqrt (1 - (1 - 2 * u) ^ 2) =
      2 * Real.sqrt (u * (1 - u)) := by
  have hvariance : 0 < u * (1 - u) :=
    mul_pos hu (by linarith)
  have hrad : 0 ≤ 1 - (1 - 2 * u) ^ 2 := by
    nlinarith
  have hsquare := Real.sq_sqrt hvariance.le
  apply (Real.sqrt_eq_iff_eq_sq hrad (by positivity)).mpr
  nlinarith

theorem zero_fibre_spectral_algebra
    (z m s : ℝ)
    (hz : z ≠ 0) (hm : 1 - m ^ 2 ≠ 0)
    (hs : s ≠ 0) (hplus : 1 + 2 * s ≠ 0)
    (hsquare : 4 * s ^ 2 = 1 - z ^ 2) :
    1 -
        ((m - m * z ^ 2) ^ 2 /
          (z ^ 2 * (1 - m ^ 2) * (1 - z ^ 2)) +
          ((z ^ 2 - m ^ 2) * (1 - z ^ 2)) /
            (z ^ 2 * (1 - m ^ 2) * (2 * s))) =
      (z ^ 2 - m ^ 2) /
        ((1 - m ^ 2) * (1 + 2 * s)) := by
  have hzsq : z ^ 2 = 1 - 4 * s ^ 2 := by
    nlinarith [hsquare]
  have hzsqne : 1 - 4 * s ^ 2 ≠ 0 := by
    rw [← hzsq]
    exact pow_ne_zero 2 hz
  have hplus' : 2 * s + 1 ≠ 0 := by
    simpa only [add_comm, ne_eq] using hplus
  have hplus'' : 1 + s * 2 ≠ 0 := by
    simpa only [ne_eq, mul_comm] using hplus
  have hfour : 4 * s ^ 2 ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hs)
  rw [hzsq]
  field_simp [hm, hs, hplus, hplus', hplus'', hfour, hzsqne]
  ; ring

theorem spectralLimit_zero_fibre_boundary {α u : ℝ}
    (hu : 0 < u) (hua : u < α)
    (ha : α < (1 : ℝ) / 2) :
    1 - spectralLimit α 0 0 u =
      (α * (1 - α) - u * (1 - u)) /
        (α * (1 - α) *
          (1 + 2 * Real.sqrt (u * (1 - u)))) := by
  let z : ℝ := (1 - 2 * u)
  let m : ℝ := (1 - 2 * α)
  let s : ℝ := Real.sqrt (u * (1 - u))
  have ha0 : 0 < α := lt_trans hu hua
  have haone : 0 < 1 - α := by linarith
  have huone : 0 < 1 - u := by linarith
  have hvariance : 0 < u * (1 - u) := mul_pos hu huone
  have hz : z ≠ 0 := by
    dsimp [z]
    nlinarith
  have hm : 1 - m ^ 2 ≠ 0 := by
    have hprod : 0 < α * (1 - α) := mul_pos ha0 haone
    dsimp [m]
    nlinarith
  have hs : s ≠ 0 := by
    dsimp [s]
    exact (Real.sqrt_pos.mpr hvariance).ne'
  have hplus : 1 + 2 * s ≠ 0 := by
    have hsnonneg : 0 ≤ s := by
      dsimp [s]
      exact Real.sqrt_nonneg _
    nlinarith
  have hsquare : 4 * s ^ 2 = 1 - z ^ 2 := by
    have hsqrt := Real.sq_sqrt hvariance.le
    dsimp [s, z]
    nlinarith
  have hradical : Real.sqrt (1 - z ^ 2) = 2 * s := by
    simpa only using sqrt_one_sub_centeredDegree_sq hu (lt_trans hua ha)
  have hsig : (1 - 2 * 0 - 2 * 0 : ℝ) = 1 := by
    norm_num
  have heta : centeredEta α 0 0 = (1 - 2 * α) := by
    simp only [centeredEta, mul_zero, add_zero, sub_zero]
  have hlimit :
      spectralLimit α 0 0 u =
        (m - m * z ^ 2) ^ 2 /
            (z ^ 2 * (1 - m ^ 2) * (1 - z ^ 2)) +
          ((z ^ 2 - m ^ 2) * (1 - z ^ 2)) /
            (z ^ 2 * (1 - m ^ 2) * (2 * s)) := by
    change
      (((1 - 2 * 0 - 2 * 0) * centeredEta α 0 0 -
          (1 - 2 * α) * (1 - 2 * u) ^ 2) ^ 2 /
        ((1 - 2 * u) ^ 2 *
          (1 - (1 - 2 * α) ^ 2) *
          (1 - (1 - 2 * u) ^ 2)) +
        (((1 - 2 * u) ^ 2 - centeredEta α 0 0 ^ 2) *
          ((1 - 2 * 0 - 2 * 0) ^ 2 - (1 - 2 * u) ^ 2)) /
          ((1 - 2 * u) ^ 2 *
            (1 - (1 - 2 * α) ^ 2) *
            Real.sqrt (1 - (1 - 2 * u) ^ 2))) = _
    rw [hsig, heta]
    simp only [one_mul, one_pow]
    change
      (m - m * z ^ 2) ^ 2 /
          (z ^ 2 * (1 - m ^ 2) * (1 - z ^ 2)) +
        ((z ^ 2 - m ^ 2) * (1 - z ^ 2)) /
          (z ^ 2 * (1 - m ^ 2) * Real.sqrt (1 - z ^ 2)) = _
    rw [hradical]
  have hA : α * (1 - α) ≠ 0 :=
    (mul_pos ha0 haone).ne'
  have hfourA : α * 4 - α ^ 2 * 4 ≠ 0 := by
    have hp : 0 < α * (1 - α) := mul_pos ha0 haone
    nlinarith
  have hmraw : 1 - (1 - 2 * α) ^ 2 ≠ 0 := by
    simpa [m] using hm
  have hplusraw :
      1 + 2 * Real.sqrt (u * (1 - u)) ≠ 0 := by
    simpa only [ne_eq] using hplus
  calc
    1 - spectralLimit α 0 0 u =
        (z ^ 2 - m ^ 2) /
          ((1 - m ^ 2) * (1 + 2 * s)) := by
      rw [hlimit]
      exact zero_fibre_spectral_algebra z m s hz hm hs hplus hsquare
    _ = (α * (1 - α) - u * (1 - u)) /
        (α * (1 - α) *
          (1 + 2 * Real.sqrt (u * (1 - u)))) := by
      dsimp [z, m, s]
      field_simp [hmraw, hA, hfourA, hplusraw]
      ; ring

/-- The asymptotic threshold used in the Johnson-code argument. -/
def asymptoticThreshold (δ α : ℝ) : ℝ :=
  1 - δ / (2 * α * (1 - α))

/-- The rank penalty used in the Johnson-code argument. -/
def rankPenalty (α β γ : ℝ) : ℝ :=
  α * MetricCodes.binaryEntropy (β / α) +
    (1 - α) * MetricCodes.binaryEntropy (γ / (1 - α))

/-- The shell rate used in the Johnson-code argument. -/
def shellRate (α β γ u : ℝ) : ℝ :=
  1 - MetricCodes.binaryEntropy α + MetricCodes.binaryEntropy u -
    rankPenalty α β γ

theorem binaryEntropy_eq_binEntropy_div_log (u : ℝ) :
    MetricCodes.binaryEntropy u = Real.binEntropy u / Real.log 2 := by
  simp only [MetricCodes.binaryEntropy, Real.logb, Real.binEntropy,
    Real.log_inv]
  ring

theorem binaryEntropy_le_one (u : ℝ) :
    MetricCodes.binaryEntropy u ≤ 1 := by
  rw [binaryEntropy_eq_binEntropy_div_log]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (div_le_iff₀ hlog).mpr
  simpa only [one_mul] using (Real.binEntropy_le_log_two (p := u))

/-- Data encoding the asymptotic parameters construction. -/
structure AsymptoticParameters (δ α β γ u : ℝ) : Prop where
  distance_pos : 0 < δ
  distance_lt_half : δ < (1 : ℝ) / 2
  weight_gt_distance : δ / 2 < α
  weight_lt_half : α < (1 : ℝ) / 2
  support_nonneg : 0 ≤ β
  support_lt_half : β < α / 2
  complement_nonneg : 0 ≤ γ
  complement_lt_half : γ < (1 - α) / 2
  first_lt_degree : β + γ < u
  degree_lt_weight : u < α
  degree_lt_left : u < α - β + γ
  degree_lt_right : u < 1 - α + β - γ

namespace AsymptoticParameters

variable {δ α β γ u : ℝ}

theorem weight_pos (h : AsymptoticParameters δ α β γ u) :
    0 < α := by
  nlinarith [h.distance_pos, h.weight_gt_distance]

theorem weight_complement_pos
    (h : AsymptoticParameters δ α β γ u) :
    0 < 1 - α := by
  nlinarith [h.weight_lt_half]

theorem degree_pos (h : AsymptoticParameters δ α β γ u) :
    0 < u := by
  nlinarith [h.support_nonneg, h.complement_nonneg,
    h.first_lt_degree]

theorem centeredDegree_pos
    (h : AsymptoticParameters δ α β γ u) :
    0 < (1 - 2 * u) := by
  nlinarith [h.degree_lt_weight, h.weight_lt_half]

theorem centeredWeight_pos
    (h : AsymptoticParameters δ α β γ u) :
    0 < (1 - 2 * α) := by
  nlinarith [h.weight_lt_half]

theorem centeredSigma_gt_degree
    (h : AsymptoticParameters δ α β γ u) :
    (1 - 2 * u) < (1 - 2 * β - 2 * γ) := by
  nlinarith [h.first_lt_degree]

theorem centeredSigma_pos
    (h : AsymptoticParameters δ α β γ u) :
    0 < (1 - 2 * β - 2 * γ) := by
  exact lt_trans h.centeredDegree_pos h.centeredSigma_gt_degree

theorem centeredEta_lt_degree
    (h : AsymptoticParameters δ α β γ u) :
    centeredEta α β γ < (1 - 2 * u) := by
  unfold centeredEta
  nlinarith [h.degree_lt_left]

theorem neg_degree_lt_centeredEta
    (h : AsymptoticParameters δ α β γ u) :
    -(1 - 2 * u) < centeredEta α β γ := by
  unfold centeredEta
  nlinarith [h.degree_lt_right]

theorem one_sub_centeredWeight_sq_pos
    (h : AsymptoticParameters δ α β γ u) :
    0 < 1 - (1 - 2 * α) ^ 2 := by
  have hprod : 0 < α * (1 - α) :=
    mul_pos h.weight_pos h.weight_complement_pos
  nlinarith

theorem one_sub_centeredDegree_sq_pos
    (h : AsymptoticParameters δ α β γ u) :
    0 < 1 - (1 - 2 * u) ^ 2 := by
  have huone : 0 < 1 - u := by
    nlinarith [h.degree_lt_weight, h.weight_lt_half]
  have hprod : 0 < u * (1 - u) := mul_pos h.degree_pos huone
  nlinarith

theorem degree_sq_sub_eta_sq_pos
    (h : AsymptoticParameters δ α β γ u) :
    0 < (1 - 2 * u) ^ 2 - centeredEta α β γ ^ 2 := by
  have hleft : 0 < (1 - 2 * u) - centeredEta α β γ :=
    sub_pos.mpr h.centeredEta_lt_degree
  have hright : 0 < (1 - 2 * u) + centeredEta α β γ := by
    linarith [h.neg_degree_lt_centeredEta]
  nlinarith [mul_pos hleft hright]

theorem sigma_sq_sub_degree_sq_pos
    (h : AsymptoticParameters δ α β γ u) :
    0 < (1 - 2 * β - 2 * γ) ^ 2 - (1 - 2 * u) ^ 2 := by
  have hleft : 0 < (1 - 2 * β - 2 * γ) - (1 - 2 * u) :=
    sub_pos.mpr h.centeredSigma_gt_degree
  have hright : 0 < (1 - 2 * β - 2 * γ) + (1 - 2 * u) :=
    add_pos h.centeredSigma_pos h.centeredDegree_pos
  nlinarith [mul_pos hleft hright]

theorem rankPenalty_le_one
    (h : AsymptoticParameters δ α β γ u) :
    rankPenalty α β γ ≤ 1 := by
  have hsupport := mul_le_mul_of_nonneg_left
    (binaryEntropy_le_one (β / α)) h.weight_pos.le
  have hcomplement := mul_le_mul_of_nonneg_left
    (binaryEntropy_le_one (γ / (1 - α)))
    h.weight_complement_pos.le
  unfold rankPenalty
  nlinarith

theorem shellRate_lower
    (h : AsymptoticParameters δ α β γ u) :
    -1 ≤ shellRate α β γ u := by
  have hαentropy := binaryEntropy_le_one α
  have huone : u ≤ 1 := by
    nlinarith [h.degree_lt_weight, h.weight_lt_half]
  have huentropy := MetricCodes.binaryEntropy_nonneg h.degree_pos.le huone
  unfold shellRate
  nlinarith [h.rankPenalty_le_one]

end AsymptoticParameters

@[simp] theorem shellRate_zero_fibre (α u : ℝ) :
    shellRate α 0 0 u =
      1 - MetricCodes.binaryEntropy α + MetricCodes.binaryEntropy u := by
  simp only [shellRate, rankPenalty, zero_div, binaryEntropy_zero, mul_zero, add_zero, sub_zero]

/-- The predicate asserting spectrally feasible. -/
def IsSpectrallyFeasible (δ α β γ u : ℝ) : Prop :=
  asymptoticThreshold δ α < spectralLimit α β γ u

/-- The feasible used in the Johnson-code argument. -/
def Feasible (δ α β γ u : ℝ) : Prop :=
  AsymptoticParameters δ α β γ u ∧
    IsSpectrallyFeasible δ α β γ u

/-- The rate set used in the Johnson-code argument. -/
def rateSet (δ : ℝ) : Set ℝ :=
  {r | ∃ α β γ u : ℝ,
    Feasible δ α β γ u ∧ r = shellRate α β γ u}

theorem rateSet_bddBelow (δ : ℝ) :
    BddBelow (rateSet δ) := by
  refine ⟨-1, ?_⟩
  rintro r ⟨α, β, γ, u, ⟨hparameter, _hspectral⟩, rfl⟩
  exact hparameter.shellRate_lower

/-- The variational rate used in the Johnson-code argument. -/
def variationalRate (δ : ℝ) : ℝ :=
  sInf (rateSet δ)

theorem variationalRate_le_of_feasible {δ α β γ u : ℝ}
    (h : Feasible δ α β γ u) :
    variationalRate δ ≤ shellRate α β γ u := by
  exact csInf_le (rateSet_bddBelow δ) ⟨α, β, γ, u, h, rfl⟩

/-- The mrrw g used in the Johnson-code argument. -/
def mrrwG (v : ℝ) : ℝ :=
  MetricCodes.binaryEntropy ((1 - Real.sqrt (1 - v)) / 2)

@[simp] theorem mrrwG_one : mrrwG 1 = 1 := by
  have hlog : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num)).ne'
  simp only [mrrwG, sub_self, Real.sqrt_zero, sub_zero, one_div,
    binaryEntropy_eq_binEntropy_div_log, Real.binEntropy_two_inv, ne_eq, hlog, not_false_eq_true,
    div_self]

theorem mrrwG_continuous : Continuous mrrwG := by
  unfold mrrwG
  exact MetricCodes.Hamming.binaryEntropy_continuous.comp
    ((continuous_const.sub
      ((continuous_const.sub continuous_id).sqrt)).div_const 2)

theorem mrrwG_nonneg {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ mrrwG v := by
  have hroot : Real.sqrt (1 - v) ≤ 1 :=
    Real.sqrt_le_one.mpr (by linarith)
  have hroot' : 0 ≤ Real.sqrt (1 - v) :=
    Real.sqrt_nonneg _
  unfold mrrwG
  apply MetricCodes.binaryEntropy_nonneg
  · linarith
  · linarith

/-- The mrrw objective used in the Johnson-code argument. -/
def mrrwObjective (δ r : ℝ) : ℝ :=
  1 + mrrwG (r ^ 2) -
    mrrwG (r ^ 2 + 2 * δ * r + 2 * δ)

theorem mrrwObjective_continuous (δ : ℝ) :
    Continuous (mrrwObjective δ) := by
  have hsquare : Continuous (fun r : ℝ => r ^ 2) :=
    continuous_id.pow 2
  have hargument :
      Continuous (fun r : ℝ => r ^ 2 + 2 * δ * r + 2 * δ) :=
    (hsquare.add (continuous_const.mul continuous_id)).add
      continuous_const
  unfold mrrwObjective
  exact (continuous_const.add (mrrwG_continuous.comp hsquare)).sub
    (mrrwG_continuous.comp hargument)

theorem mrrwObjective_endpoint {δ : ℝ}
    (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    mrrwObjective δ (1 - 2 * δ) =
      MetricCodes.Hamming.classicalRate δ := by
  have hlast :
      (1 - 2 * δ) ^ 2 + 2 * δ * (1 - 2 * δ) + 2 * δ =
        (1 : ℝ) := by
    ring
  have hroot :
      Real.sqrt (1 - (1 - 2 * δ) ^ 2) =
        2 * Real.sqrt (δ * (1 - δ)) := by
    exact sqrt_one_sub_centeredDegree_sq hδ hhalf
  calc
    mrrwObjective δ (1 - 2 * δ) =
        mrrwG ((1 - 2 * δ) ^ 2) := by
      unfold mrrwObjective
      rw [hlast, mrrwG_one]
      ring
    _ = MetricCodes.Hamming.classicalRate δ := by
      unfold mrrwG MetricCodes.Hamming.classicalRate
        MetricCodes.Hamming.classicalParameter
      rw [hroot]
      congr 1 ; ring

theorem mrrwG_variance {u : ℝ}
    (hu : u ≤ (1 : ℝ) / 2) :
    mrrwG (4 * u * (1 - u)) = MetricCodes.binaryEntropy u := by
  have hrad :
      1 - 4 * u * (1 - u) = (1 - 2 * u) ^ 2 := by
    ring
  have hroot :
      Real.sqrt (1 - 4 * u * (1 - u)) = 1 - 2 * u := by
    rw [hrad, Real.sqrt_sq (by linarith)]
  unfold mrrwG
  rw [hroot]
  congr 1
  ring

theorem zero_fibre_boundary_variance {δ α u : ℝ}
    (hu : 0 < u) (hua : u < α)
    (ha : α < (1 : ℝ) / 2)
    (hboundary :
      spectralLimit α 0 0 u = asymptoticThreshold δ α) :
    4 * α * (1 - α) =
      (2 * Real.sqrt (u * (1 - u))) ^ 2 +
        2 * δ * (2 * Real.sqrt (u * (1 - u))) + 2 * δ := by
  have hα : 0 < α := lt_trans hu hua
  have hαone : 0 < 1 - α := by linarith
  have huone : 0 < 1 - u := by linarith
  have hA : α * (1 - α) ≠ 0 :=
    (mul_pos hα hαone).ne'
  have hs : 0 ≤ Real.sqrt (u * (1 - u)) :=
    Real.sqrt_nonneg _
  have hplus : 1 + 2 * Real.sqrt (u * (1 - u)) ≠ 0 := by
    nlinarith
  have hrel :
      δ / (2 * α * (1 - α)) =
        (α * (1 - α) - u * (1 - u)) /
          (α * (1 - α) *
            (1 + 2 * Real.sqrt (u * (1 - u)))) := by
    calc
      δ / (2 * α * (1 - α)) =
          1 - spectralLimit α 0 0 u := by
        rw [hboundary]
        unfold asymptoticThreshold
        ring
      _ = _ := spectralLimit_zero_fibre_boundary hu hua ha
  have hsquare := Real.sq_sqrt (mul_pos hu huone).le
  field_simp [hA, hα.ne', hαone.ne', hplus] at hrel
  nlinarith [hsquare]

theorem mrrwObjective_zero_fibre_boundary {δ α u : ℝ}
    (hu : 0 < u) (hua : u < α)
    (ha : α < (1 : ℝ) / 2)
    (hboundary :
      spectralLimit α 0 0 u = asymptoticThreshold δ α) :
    mrrwObjective δ (2 * Real.sqrt (u * (1 - u))) =
      shellRate α 0 0 u := by
  have huone : 0 < 1 - u := by linarith
  have hsquare := Real.sq_sqrt (mul_pos hu huone).le
  have hvariance :
      (2 * Real.sqrt (u * (1 - u))) ^ 2 =
        4 * u * (1 - u) := by
    nlinarith [hsquare]
  have hboundary' :=
    zero_fibre_boundary_variance hu hua ha hboundary
  have hargument :
      4 * u * (1 - u) +
        2 * δ * (2 * Real.sqrt (u * (1 - u))) + 2 * δ =
        4 * α * (1 - α) := by
    nlinarith [hboundary', hvariance]
  unfold mrrwObjective
  rw [hvariance, hargument,
    mrrwG_variance (by linarith : u ≤ (1 : ℝ) / 2),
    mrrwG_variance ha.le, shellRate_zero_fibre]
  ring

private def mrrwRateSet (δ : ℝ) : Set ℝ :=
  {t | ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 - 2 * δ ∧
    t = mrrwObjective δ r}

theorem mrrwRateSet_bddBelow (δ : ℝ) :
    BddBelow (mrrwRateSet δ) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨r, _hr, _hupper, rfl⟩
  have hfirst := mrrwG_nonneg (sq_nonneg r)
  have hsecond :
      mrrwG (r ^ 2 + 2 * δ * r + 2 * δ) ≤ 1 := by
    unfold mrrwG
    exact binaryEntropy_le_one _
  unfold mrrwObjective
  linarith

/-- The mrrw rate used in the Johnson-code argument. -/
def mrrwRate (δ : ℝ) : ℝ :=
  sInf (mrrwRateSet δ)

theorem mrrwRate_le_objective {δ r : ℝ}
    (hr : 0 ≤ r) (hupper : r ≤ 1 - 2 * δ) :
    mrrwRate δ ≤ mrrwObjective δ r := by
  exact csInf_le (mrrwRateSet_bddBelow δ)
    ⟨r, hr, hupper, rfl⟩

theorem exists_mrrw_minimizer {δ : ℝ}
    (hhalf : δ ≤ (1 : ℝ) / 2) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 - 2 * δ ∧
      ∀ s : ℝ, 0 ≤ s → s ≤ 1 - 2 * δ →
        mrrwObjective δ r ≤ mrrwObjective δ s := by
  have hnonempty : (Set.Icc 0 (1 - 2 * δ)).Nonempty := by
    refine ⟨0, ?_⟩
    constructor
    · exact le_rfl
    · linarith
  obtain ⟨r, hr, hmin⟩ :=
    isCompact_Icc.exists_isMinOn hnonempty
      (mrrwObjective_continuous δ).continuousOn
  refine ⟨r, hr.1, hr.2, ?_⟩
  intro s hs hupper
  exact hmin ⟨hs, hupper⟩

theorem mrrwRate_eq_objective_of_minimizer {δ r : ℝ}
    (hr : 0 ≤ r) (hupper : r ≤ 1 - 2 * δ)
    (hmin : ∀ s : ℝ, 0 ≤ s → s ≤ 1 - 2 * δ →
      mrrwObjective δ r ≤ mrrwObjective δ s) :
    mrrwRate δ = mrrwObjective δ r := by
  apply le_antisymm
  · exact mrrwRate_le_objective hr hupper
  · unfold mrrwRate
    apply le_csInf
    · exact ⟨mrrwObjective δ r, r, hr, hupper, rfl⟩
    · rintro _ ⟨s, hs, hsupper, rfl⟩
      exact hmin s hs hsupper

theorem mrrwRate_le_classicalRate {δ : ℝ}
    (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    mrrwRate δ ≤ MetricCodes.Hamming.classicalRate δ := by
  calc
    mrrwRate δ ≤ mrrwObjective δ (1 - 2 * δ) :=
      mrrwRate_le_objective (by linarith) (le_refl _)
    _ = MetricCodes.Hamming.classicalRate δ :=
      mrrwObjective_endpoint hδ hhalf

theorem mrrw_endpoint_dichotomy {δ : ℝ}
    (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    mrrwRate δ < MetricCodes.Hamming.classicalRate δ ∨
      mrrwRate δ = MetricCodes.Hamming.classicalRate δ := by
  exact lt_or_eq_of_le (mrrwRate_le_classicalRate hδ hhalf)

/-- The combined variational rate used in the Johnson-code argument. -/
def combinedVariationalRate (δ : ℝ) : ℝ :=
  min (MetricCodes.Hamming.variationalRate δ) (variationalRate δ)

theorem combinedVariationalRate_le_hamming (δ : ℝ) :
    combinedVariationalRate δ ≤ MetricCodes.Hamming.variationalRate δ := by
  exact min_le_left _ _

theorem combinedVariationalRate_le_shell (δ : ℝ) :
    combinedVariationalRate δ ≤ variationalRate δ := by
  exact min_le_right _ _

theorem combinedVariationalRate_lt_mrrw_of_endpoint
    {δ : ℝ} (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2)
    (hendpoint : mrrwRate δ = MetricCodes.Hamming.classicalRate δ) :
    combinedVariationalRate δ < mrrwRate δ := by
  calc
    combinedVariationalRate δ ≤
        MetricCodes.Hamming.variationalRate δ :=
      combinedVariationalRate_le_hamming δ
    _ < MetricCodes.Hamming.classicalRate δ :=
      MetricCodes.Hamming.variationalRate_lt_classicalRate hδ hhalf
    _ = mrrwRate δ := hendpoint.symm

end

end Johnson

end MetricCodes

end MetricCodesNoncomputable
