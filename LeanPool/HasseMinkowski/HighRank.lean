/-
Copyright (c) 2026 jayyswan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jayyswan
-/
module

public import LeanPool.HasseMinkowski.HilbertSymbol.Local
public import LeanPool.HasseMinkowski.Legendre
public import LeanPool.HasseMinkowski.Prod
public import LeanPool.HasseMinkowski.RankCriteria
public import LeanPool.HasseMinkowski.RatApproximation
public import LeanPool.HasseMinkowski.Padics.Squares
public import Mathlib.Analysis.Real.Sqrt

/-!
# WP5 toolkit: diagonal Hasse–Minkowski for rank ≥ 5

This file collects the two "one-step" tools of the rank-`n ≥ 5` induction of Serre IV.2
(see `Plan-v3.md` §WP5).  The final rank ≥ 5 theorem is proved elsewhere; here we supply

* **WP5.1** — over an odd prime, a ternary diagonal form whose three weights are `p`-adic
  units is isotropic, and hence so is any diagonal form with at least three unit weights;
* **WP5.2** — the openness of the nonzero square classes of `ℝ` and `ℚ_[p]` (a number close
  enough to a nonzero `a₀` has `a / a₀` a square), and the vector form of weak approximation
  for `ℚ` (a rational vector can be found close to prescribed local vectors).

The rank-three criterion of `RankCriteria.lean` together with `hilbertSym_padicInt_units`
turns the local isotropy into the vanishing of a Hilbert symbol of two `p`-adic units.
-/

public section

open Module QuadraticMap

namespace HasseMinkowski

/-! ### WP5.1 — three unit weights over an odd prime -/

-- Theorem: over an odd prime, a ternary diagonal form all of whose weights are `p`-adic units
-- is isotropic.
--
-- The rank-three criterion `weightedSumSquares_isotropic_iff_hilbertSym_eq_one` reduces this
-- to `(-u₂u₀, -u₂u₁) = 1`; both arguments are units of `ℤ_[p]`, so `hilbertSym_padicInt_units`
-- gives the result.
theorem isotropic_weightedSumSquares_three_units (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (u : Fin 3 → ℤ_[p]ˣ) :
    (weightedSumSquares ℚ_[p] (fun i => (u i : ℚ_[p]))).Isotropic := by
  have hfun : (fun i : Fin 3 => (u i : ℚ_[p])) =
      ![(u 0 : ℚ_[p]), (u 1 : ℚ_[p]), (u 2 : ℚ_[p])] := by
    funext i
    fin_cases i <;> rfl
  have hne : ∀ i : Fin 3, ((u i : ℤ_[p]) : ℚ_[p]) ≠ 0 := fun i => by
    rw [PadicInt.coe_ne_zero]
    exact (u i).ne_zero
  rw [hfun, weightedSumSquares_isotropic_iff_hilbertSym_eq_one _ _ _
    (hne 0) (hne 1) (hne 2)]
  have h0 : (-(u 2 : ℚ_[p])) * (u 0 : ℚ_[p]) = ((-(u 2 * u 0) : ℤ_[p]ˣ) : ℚ_[p]) := by
    rw [Units.val_neg, Units.val_mul]
    push_cast
    ring
  have h1 : (-(u 2 : ℚ_[p])) * (u 1 : ℚ_[p]) = ((-(u 2 * u 1) : ℤ_[p]ˣ) : ℚ_[p]) := by
    rw [Units.val_neg, Units.val_mul]
    push_cast
    ring
  rw [h0, h1]
  exact hilbertSym_padicInt_units hp (-(u 2 * u 0)) (-(u 2 * u 1))

-- Theorem: over an odd prime, a diagonal form with at least three `p`-adic unit weights is
-- isotropic.
--
-- The three unit coordinates span a ternary subform which is isotropic by
-- `isotropic_weightedSumSquares_three_units`; extending its isotropic vector by `0` to `ι`
-- preserves the value of the whole form, because the added coordinates have weight `0`.
theorem isotropic_of_three_units (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {ι : Type*}
    [Fintype ι] {w : ι → ℚ_[p]} (u : Fin 3 ↪ ι)
    (hu : ∀ j, ∃ v : ℤ_[p]ˣ, (v : ℚ_[p]) = w (u j)) :
    (weightedSumSquares ℚ_[p] w).Isotropic := by
  classical
  choose v hv using hu
  have hsub : (weightedSumSquares ℚ_[p] (fun j : Fin 3 => w (u j))).Isotropic := by
    have hw_eq : (fun j : Fin 3 => (v j : ℚ_[p])) = fun j : Fin 3 => w (u j) :=
      funext fun j => hv j
    rw [← hw_eq]
    exact isotropic_weightedSumSquares_three_units p hp v
  obtain ⟨y, hy_ne, hy0⟩ := hsub
  let V : ι → ℚ_[p] := fun i =>
    if hi : i ∈ Set.range (fun j : Fin 3 => u j) then y (Classical.choose hi) else 0
  have hVf : ∀ j, V (u j) = y j := by
    intro j
    have hi : u j ∈ Set.range (fun j : Fin 3 => u j) := ⟨j, rfl⟩
    have hc : Classical.choose hi = j := u.injective (Classical.choose_spec hi)
    dsimp only [V]
    rw [dite_eq_left hi, hc]
  have hV0 : ∀ i, i ∉ Set.range (fun j : Fin 3 => u j) → V i = 0 := by
    intro i hi
    dsimp only [V]
    rw [dite_eq_right hi]
  refine ⟨V, ?_, ?_⟩
  · intro hVz
    have hex : ∃ j, y j ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      exact hy_ne (funext hcon)
    obtain ⟨j, hj⟩ := hex
    exact hj (by rw [← hVf j, hVz]; rfl)
  · have hL : (weightedSumSquares ℚ_[p] w) V = ∑ i : ι, w i * (V i * V i) := by
      simp only [weightedSumSquares_apply, smul_eq_mul]
    have hR : (weightedSumSquares ℚ_[p] (fun j : Fin 3 => w (u j))) y =
        ∑ j : Fin 3, w (u j) * (y j * y j) := by
      simp only [weightedSumSquares_apply, smul_eq_mul]
    have hsum : (∑ i : ι, w i * (V i * V i)) = ∑ j : Fin 3, w (u j) * (y j * y j) := by
      have hzero : ∀ i ∈ (Finset.univ : Finset ι),
          i ∉ Finset.univ.image (fun j : Fin 3 => u j) → w i * (V i * V i) = 0 := by
        intro i _ hi
        have hir : i ∉ Set.range (fun j : Fin 3 => u j) := by
          intro hmem
          obtain ⟨a, ha⟩ := hmem
          exact hi (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ha⟩)
        rw [hV0 i hir]; ring
      rw [← Finset.sum_subset
        (Finset.subset_univ (Finset.univ.image (fun j : Fin 3 => u j))) hzero]
      rw [Finset.sum_image (fun a _ b _ hab => u.injective hab)]
      exact Finset.sum_congr rfl (fun j _ => by simp only [hVf j])
    rw [hL, hsum, ← hR]
    exact hy0

-- Theorem: the integral-weight form of `isotropic_of_three_units`, stated with the literal
-- hypothesis that the three chosen weights are units of `ℤ_[p]`.
theorem isotropic_of_three_units_int (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {ι : Type*}
    [Fintype ι] {w : ι → ℤ_[p]} (u : Fin 3 ↪ ι) (hu : ∀ j, IsUnit (w (u j))) :
    (weightedSumSquares ℚ_[p] (fun i => (w i : ℚ_[p]))).Isotropic := by
  refine isotropic_of_three_units p hp u (fun j => ?_)
  exact ⟨(hu j).unit, by rw [IsUnit.unit_spec]⟩

/-! ### WP5.2 — openness of square classes and vector approximation -/

-- Theorem (openness of the nonzero square class of `ℝ`): a real number within distance
-- `‖a₀‖` of a nonzero `a₀` has `a / a₀` positive, hence a square.
theorem isSquare_div_of_close_real {a₀ a : ℝ} (h₀ : a₀ ≠ 0) (h : ‖a - a₀‖ < ‖a₀‖) :
    IsSquare (a / a₀) := by
  have h' : |a - a₀| < |a₀| := by simpa only [Real.norm_eq_abs] using h
  rw [Real.isSquare_iff]
  by_cases hpos : 0 < a₀
  · rw [abs_of_pos hpos] at h'
    have ha : 0 < a := by linarith [(abs_lt.mp h').1]
    exact le_of_lt (div_pos ha hpos)
  · have hneg : a₀ < 0 := lt_of_le_of_ne (not_lt.mp hpos) h₀
    rw [abs_of_neg hneg] at h'
    have ha : a < 0 := by linarith [(abs_lt.mp h').2]
    exact le_of_lt (div_pos_of_neg_of_neg ha hneg)

-- Theorem (openness of the nonzero square class of `ℚ_[p]`, odd `p`): a `p`-adic number
-- within distance `‖a₀‖` of a nonzero `a₀` has `a / a₀` a square.
--
-- Writing `a / a₀ = 1 + (a - a₀) / a₀`, the closeness hypothesis gives
-- `dist (a / a₀) 1 ≤ ‖a - a₀‖ / ‖a₀‖ < 1`, and `Padic.isSquare_of_dist_one_lt_one` applies.
theorem isSquare_div_of_close_padic (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {a₀ a : ℚ_[p]}
    (h₀ : a₀ ≠ 0) (h : ‖a - a₀‖ < ‖a₀‖) : IsSquare (a / a₀) := by
  refine Padic.isSquare_of_dist_one_lt_one (p := p) hp ?_
  rw [dist_eq_norm, show a / a₀ - 1 = (a - a₀) / a₀ by field_simp, norm_div,
    div_lt_one (norm_pos_iff.mpr h₀)]
  exact h

-- Theorem (openness of the nonzero square class of `ℚ_[2]`): the same conclusion holds for
-- `p = 2`, but the closeness must be measured against the modulus-`8` threshold `2⁻²`.
--
-- Indeed `a / a₀` is a `2`-adic square as soon as `dist (a / a₀) 1 < 2⁻²`.
theorem isSquare_div_of_close_padic_two {a₀ a : ℚ_[2]} (h₀ : a₀ ≠ 0)
    (h : ‖a - a₀‖ < 2 ^ (-(2 : ℤ)) * ‖a₀‖) : IsSquare (a / a₀) := by
  refine Padic.isSquare_of_dist_one_lt_pow ?_
  rw [dist_eq_norm, show a / a₀ - 1 = (a - a₀) / a₀ by field_simp, norm_div,
    div_lt_iff₀ (norm_pos_iff.mpr h₀)]
  exact h

-- Theorem: a prime bundled as `Nat.Primes` is prime, as an instance (needed to form `ℚ_[p]`
-- for `p` ranging over a finite set of primes).
local instance factPrimeOfPrimesHighRank (p : Nat.Primes) : Fact (Nat.Prime (p : ℕ)) :=
  ⟨p.2⟩

-- Theorem (vector weak approximation for `ℚ`): given local vectors `x p ∈ ℚ_p²` at the
-- finitely many places `p ∈ S`, there is a rational vector `q ∈ ℚ²` whose coordinates are
-- within `1` of `x p` at every place `p ∈ S`.
--
-- The two coordinates are approximated independently by `Rat.approximation'`; the real
-- coordinate of the approximation theorem is irrelevant here and is taken to be `0`.
theorem exists_rat_close_vec {S : Finset Nat.Primes}
    (x : Π p : S, Fin 2 → ℚ_[p]) :
    ∃ q : Fin 2 → ℚ, ∀ p : S,
      ‖(x p) 0 - (q 0 : ℚ_[p])‖ < 1 ∧ ‖(x p) 1 - (q 1 : ℚ_[p])‖ < 1 := by
  classical
  obtain ⟨q₀, hq₀⟩ := Rat.approximation' (S := S) (ε := 1) (by norm_num)
    (0, fun p : S => (x p) 0)
  obtain ⟨q₁, hq₁⟩ := Rat.approximation' (S := S) (ε := 1) (by norm_num)
    (0, fun p : S => (x p) 1)
  refine ⟨![q₀, q₁], fun p => ⟨?_, ?_⟩⟩
  · simp only [Matrix.cons_val_zero]
    have hsingle : ‖(x p) 0 - (q₀ : ℚ_[p])‖ ≤
        Finset.sum (Finset.attach S) (fun n => ‖(x n) 0 - (q₀ : ℚ_[n])‖) :=
      Finset.single_le_sum (f := fun n : S => ‖(x n) 0 - (q₀ : ℚ_[n])‖)
        (fun i _ => norm_nonneg _) (Finset.mem_attach S p)
    have hle : Finset.sum (Finset.attach S) (fun n => ‖(x n) 0 - (q₀ : ℚ_[n])‖) ≤
        ‖(0 : ℝ) - q₀‖ +
          Finset.sum (Finset.attach S) (fun n => ‖(x n) 0 - (q₀ : ℚ_[n])‖) :=
      le_add_of_nonneg_left (norm_nonneg _)
    exact lt_of_le_of_lt hsingle (lt_of_le_of_lt hle hq₀)
  · simp only [Matrix.cons_val_one]
    have hsingle : ‖(x p) 1 - (q₁ : ℚ_[p])‖ ≤
        Finset.sum (Finset.attach S) (fun n => ‖(x n) 1 - (q₁ : ℚ_[n])‖) :=
      Finset.single_le_sum (f := fun n : S => ‖(x n) 1 - (q₁ : ℚ_[n])‖)
        (fun i _ => norm_nonneg _) (Finset.mem_attach S p)
    have hle : Finset.sum (Finset.attach S) (fun n => ‖(x n) 1 - (q₁ : ℚ_[n])‖) ≤
        ‖(0 : ℝ) - q₁‖ +
          Finset.sum (Finset.attach S) (fun n => ‖(x n) 1 - (q₁ : ℚ_[n])‖) :=
      le_add_of_nonneg_left (norm_nonneg _)
    exact lt_of_le_of_lt hsingle (lt_of_le_of_lt hle hq₁)

/-! ### The rank-four input of the high-rank induction

The rank-`n ≥ 5` induction of Serre IV.2 bottoms out at rank 4, so `HighRank.lean` is stated
relative to the following `Prop`, which is exactly the diagonal rank-four Hasse–Minkowski
theorem that `RankFour.lean` (WP4.2) proves.  Keeping it as an explicit hypothesis lets the
high-rank induction be developed and checked independently of the rank-four proof. -/

/-- Diagonal rank-four Hasse–Minkowski over `ℚ`: a diagonal rank-four form with nonzero
rational weights that is isotropic over every `p`-adic completion and over `ℝ` is isotropic
over `ℚ`.  This is the WP4.2 statement, recorded as a `Prop` so that the rank-`≥ 5`
induction can be stated against it. -/
@[expose] def RankFourDiagonalHM : Prop :=
  ∀ w : Fin 4 → ℚ, (∀ i, w i ≠ 0) →
    (∀ (p : ℕ) [Fact (Nat.Prime p)],
      (weightedSumSquares ℚ_[p] (fun i => (w i : ℚ_[p]))).Isotropic) →
    (weightedSumSquares ℝ (fun i => (w i : ℝ))).Isotropic →
    (weightedSumSquares ℚ w).Isotropic

/-! ### WP5.3 — algebraic splitting of a weighted sum of squares

The induction writes `⟨w₀, …, w_{n-1}⟩` as `⟨w₀, w₁⟩ ⊥ (w₂, …, w_{n-1})`.  These lemmas
realise that split on the level of vectors, so that local isotropy of the big form can be
read off by `prod_isotropic_iff`. -/

section SplitWSS

-- Theorem: the sum over `Fin (m+2)` splits off its first two terms.
theorem sum_fin_add_two {α : Type*} [AddCommMonoid α] (m : ℕ) (f : Fin (m + 2) → α) :
    (∑ i : Fin (m + 2), f i) = f 0 + f 1 + ∑ j : Fin m, f j.succ.succ := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.succ_zero_eq_one]
  ac_rfl

-- Theorem: the value of `weightedSumSquares K w` splits as the sum of the values of the
-- first two weights and of the remaining `m` weights.
theorem wss_add_two_val {K : Type*} [CommSemiring K] (m : ℕ) (w : Fin (m + 2) → K)
    (v : Fin (m + 2) → K) :
    (weightedSumSquares K w) v =
      (weightedSumSquares K ![w 0, w 1]) ![v 0, v 1] +
      (weightedSumSquares K (fun j : Fin m => w j.succ.succ)) (fun j => v j.succ.succ) := by
  simp only [weightedSumSquares_apply, smul_eq_mul]
  rw [sum_fin_add_two m, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

-- Theorem: isotropy of `⟨w₀, …, w_{m+1}⟩` gives isotropy of the orthogonal sum
-- `⟨w₀, w₁⟩ ⊥ ⟨w₂, …, w_{m+1}⟩`.
theorem prod_isotropic_of_wss {K : Type*} [CommSemiring K] (m : ℕ) (w : Fin (m + 2) → K)
    (hiso : (weightedSumSquares K w).Isotropic) :
    ((weightedSumSquares K ![w 0, w 1]).prod
      (weightedSumSquares K (fun j : Fin m => w j.succ.succ))).Isotropic := by
  obtain ⟨v, hv, hv0⟩ := hiso
  refine ⟨(![v 0, v 1], fun j => v j.succ.succ), ?_, ?_⟩
  · intro h
    apply hv
    funext i
    induction i using Fin.cases with
    | zero => simpa using congrArg (fun t : (Fin 2 → K) × (Fin m → K) => t.1 0) h
    | succ j =>
        induction j using Fin.cases with
        | zero => simpa using congrArg (fun t : (Fin 2 → K) × (Fin m → K) => t.1 1) h
        | succ k => simpa using congrArg (fun t : (Fin 2 → K) × (Fin m → K) => t.2 k) h
  · rw [QuadraticMap.prod_apply, ← wss_add_two_val m w v, hv0]

-- Theorem: isotropy of the tail `⟨w₂, …, w_{m+1}⟩` gives isotropy of `⟨w₀, …, w_{m+1}⟩`.
theorem wss_tail_isotropic {K : Type*} [CommSemiring K] (m : ℕ) (w : Fin (m + 2) → K)
    (hiso : (weightedSumSquares K (fun j : Fin m => w j.succ.succ)).Isotropic) :
    (weightedSumSquares K w).Isotropic := by
  obtain ⟨y, hy, hy0⟩ := hiso
  refine ⟨Fin.cons 0 (Fin.cons 0 y), ?_, ?_⟩
  · intro h
    apply hy
    funext j
    simpa using congrArg (fun t : Fin (m + 2) → K => t j.succ.succ) h
  · rw [wss_add_two_val m w (Fin.cons 0 (Fin.cons 0 y))]
    simp [hy0]

-- Theorem: a weighted sum of squares with nonzero weights is nondegenerate.
theorem nondegenerate_wss_of_ne {K : Type*} [Field K] [Invertible (2 : K)] {ι : Type*}
    [Fintype ι] {w : ι → K} (hw : ∀ i, w i ≠ 0) :
    (weightedSumSquares K w).Nondegenerate := by
  let u : ι → Kˣ := fun i => Units.mk0 (w i) (hw i)
  have hu : (fun i => (u i : K)) = w := by funext i; simp [u]
  rw [← hu]
  exact nondegenerate_weightedSumSquares u

-- Theorem: local isotropy of `⟨w₀, …, w_{m+1}⟩` yields a nonzero value `a` represented by
-- `⟨w₀, w₁⟩` and by `-⟨w₂, …, w_{m+1}⟩`.
--
-- This is the "common value" step of the rank-lowering induction: since
-- `⟨w₀, …, w_{m+1}⟩ ≅ ⟨w₀, w₁⟩ ⊥ ⟨w₂, …, w_{m+1}⟩`, `prod_isotropic_iff` exhibits such a
-- value unless one of the two summands is itself isotropic, in which case nondegeneracy
-- makes it represent every value.
theorem exists_local_common_value {K : Type*} [Field K] [Invertible (2 : K)] {m : ℕ}
    [NeZero m] {w : Fin (m + 2) → K} (hw : ∀ i, w i ≠ 0)
    (hiso : (weightedSumSquares K w).Isotropic) :
    ∃ a : K, a ≠ 0 ∧
      (weightedSumSquares K ![w 0, w 1]).represents a ∧
      (weightedSumSquares K (fun j : Fin m => w j.succ.succ)).represents (-a) := by
  have hsplit := prod_isotropic_of_wss m w hiso
  have hndh : (weightedSumSquares K ![w 0, w 1]).Nondegenerate := by
    refine nondegenerate_wss_of_ne ?_
    intro i
    fin_cases i
    · simpa using hw 0
    · simpa using hw 1
  have hndg : (weightedSumSquares K (fun j : Fin m => w j.succ.succ)).Nondegenerate :=
    nondegenerate_wss_of_ne (fun j => hw _)
  rcases (prod_isotropic_iff _ _).mp hsplit with hI | hI | ⟨a, ha, hha, hga⟩
  · obtain ⟨b, hb, hgb⟩ := exists_ne_zero_represents_of_nondegenerate hndg
    exact ⟨-b, neg_ne_zero.mpr hb,
      represents_of_isotropic_nondegenerate hndh hI (-b), by rwa [neg_neg]⟩
  · obtain ⟨b, hb, hhb⟩ := exists_ne_zero_represents_of_nondegenerate hndh
    exact ⟨b, hb, hhb, represents_of_isotropic_nondegenerate hndg hI (-b)⟩
  · exact ⟨a, ha, hha, hga⟩

-- Theorem (vector form of weak approximation, with the archimedean place): a rational
-- vector can be found `ε`-close to prescribed local vectors at the real place and at every
-- prime of a finite set.
theorem exists_rat_close_vec' {S : Finset Nat.Primes} {ε : ℝ} (hε : 0 < ε)
    (xr : Fin 2 → ℝ) (x : Π p : S, Fin 2 → ℚ_[p]) :
    ∃ q : Fin 2 → ℚ, (∀ i, ‖xr i - (q i : ℝ)‖ < ε) ∧
      ∀ p : S, ∀ i, ‖(x p) i - (q i : ℚ_[p])‖ < ε := by
  classical
  have h2 : ∀ i : Fin 2, ∃ q : ℚ,
      ‖xr i - (q : ℝ)‖ < ε ∧ ∀ p : S, ‖(x p) i - (q : ℚ_[p])‖ < ε := by
    intro i
    obtain ⟨q, hq⟩ := Rat.approximation' (S := S) (ε := ε) hε (xr i, fun p : S => (x p) i)
    refine ⟨q, ?_, ?_⟩
    · exact lt_of_le_of_lt (le_add_of_nonneg_right (Finset.sum_nonneg fun n _ => norm_nonneg _)) hq
    · intro p
      have hle : ‖(x p) i - (q : ℚ_[p])‖ ≤
          Finset.sum (Finset.attach S) (fun n => ‖(x n) i - (q : ℚ_[n])‖) :=
        Finset.single_le_sum (f := fun n : S => ‖(x n) i - (q : ℚ_[n])‖)
          (fun n _ => norm_nonneg _) (Finset.mem_attach S p)
      exact lt_of_le_of_lt hle (lt_of_le_of_lt (le_add_of_nonneg_left (norm_nonneg _)) hq)
  choose q hq using h2
  exact ⟨q, fun i => (hq i).1, fun p i => (hq i).2 p⟩

-- Theorem: a `p`-adic number of norm one is the underlying element of an integral unit.
theorem exists_padicUnit_of_norm_eq_one {p : ℕ} [Fact p.Prime] {x : ℚ_[p]}
    (h : ‖x‖ = 1) : ∃ u : ℤ_[p]ˣ, (u : ℚ_[p]) = x :=
  ⟨PadicInt.mkUnits h, PadicInt.mkUnits_eq h⟩

end SplitWSS

/-! ### WP5.3 — the quantitative closeness bound -/

section CloseBound

-- Theorem (per-place estimate): if `q` is `ε`-close to `x` and `x` is bounded by `B`, then
-- the values of `⟨w₀, w₁⟩` differ by at most `(‖w₀‖ + ‖w₁‖) · ε · (ε + 2B)`.
theorem wss_pair_close {K : Type*} [NormedField K] {w x q : Fin 2 → K} {ε B : ℝ}
    (h2 : ‖(2 : K)‖ ≤ 2) (hq : ∀ i, ‖q i - x i‖ ≤ ε) (hx : ∀ i, ‖x i‖ ≤ B) :
    ‖(weightedSumSquares K w) q - (weightedSumSquares K w) x‖ ≤
      (‖w 0‖ + ‖w 1‖) * (ε * (ε + 2 * B)) := by
  have hB : 0 ≤ B := le_trans (norm_nonneg _) (hx 0)
  have hε : 0 ≤ ε := le_trans (norm_nonneg _) (hq 0)
  have hval : ∀ z : Fin 2 → K, (weightedSumSquares K w) z = w 0 * z 0 ^ 2 + w 1 * z 1 ^ 2 := by
    intro z
    simp [weightedSumSquares_apply, Fin.sum_univ_two, smul_eq_mul, pow_two]
  have hplus : ∀ i : Fin 2, ‖q i + x i‖ ≤ ε + 2 * B := by
    intro i
    have hsplit : q i + x i = (q i - x i) + 2 * x i := by ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have hstep : ‖(2 : K)‖ * ‖x i‖ ≤ 2 * B :=
      mul_le_mul h2 (hx i) (norm_nonneg _) (by norm_num)
    linarith [hq i]
  rw [hval q, hval x]
  have hdiff : w 0 * q 0 ^ 2 + w 1 * q 1 ^ 2 - (w 0 * x 0 ^ 2 + w 1 * x 1 ^ 2) =
      w 0 * (q 0 - x 0) * (q 0 + x 0) + w 1 * (q 1 - x 1) * (q 1 + x 1) := by ring
  rw [hdiff]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  have h0 : ‖w 0‖ * ‖q 0 - x 0‖ * ‖q 0 + x 0‖ ≤ ‖w 0‖ * ε * (ε + 2 * B) :=
    mul_le_mul (mul_le_mul_of_nonneg_left (hq 0) (norm_nonneg _)) (hplus 0)
      (norm_nonneg _) (by positivity)
  have h1 : ‖w 1‖ * ‖q 1 - x 1‖ * ‖q 1 + x 1‖ ≤ ‖w 1‖ * ε * (ε + 2 * B) :=
    mul_le_mul (mul_le_mul_of_nonneg_left (hq 1) (norm_nonneg _)) (hplus 1)
      (norm_nonneg _) (by positivity)
  linarith [h0, h1]

end CloseBound

/-! ### WP5.3 — the finite set of bad primes -/

section PlaceSet

/-- The finite set of primes dividing the numerator or denominator of some weight, together
with `2`.  Off this set every weight is a `p`-adic unit. -/
noncomputable def smallPrimes {ι : Type*} [Fintype ι] (w : ι → ℚ) : Finset Nat.Primes :=
  let m : ℕ := ∏ i, (w i).num.natAbs * (w i).den
  insert ⟨2, Nat.prime_two⟩
    (((m.divisors.filter Nat.Prime).attach).image
      (fun x => (⟨x.1, (Finset.mem_filter.mp x.2).2⟩ : Nat.Primes)))

-- Theorem: a prime outside `smallPrimes w` divides no numerator and no denominator.
theorem notMem_smallPrimes {ι : Type*} [Fintype ι] {w : ι → ℚ} (hw : ∀ i, w i ≠ 0)
    {p : Nat.Primes} (hp : p ∉ smallPrimes w) (i : ι) :
    ¬ (p : ℕ) ∣ (w i).num.natAbs ∧ ¬ (p : ℕ) ∣ (w i).den := by
  have hm0 : (∏ j, (w j).num.natAbs * (w j).den) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
    exact mul_ne_zero (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr (hw j))) (Rat.den_ne_zero _)
  have hp2 : (p : ℕ) ≠ 2 := by
    intro h
    exact hp (by
      simp only [smallPrimes]
      exact Finset.mem_insert.mpr (Or.inl (Subtype.ext h)))
  have hpdvd : ¬ (p : ℕ) ∣ ∏ j, (w j).num.natAbs * (w j).den := by
    intro hd
    apply hp
    simp only [smallPrimes]
    refine Finset.mem_insert.mpr (Or.inr ?_)
    refine Finset.mem_image.mpr ⟨⟨(p : ℕ), ?_⟩, Finset.mem_attach _ _, rfl⟩
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd, hm0⟩, p.2⟩
  constructor
  · intro hnum
    exact hpdvd (dvd_trans (dvd_mul_of_dvd_left hnum _)
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))
  · intro hden
    exact hpdvd (dvd_trans (dvd_mul_of_dvd_right hden _)
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))

-- Theorem: off `smallPrimes w`, every rational weight has `p`-adic norm `1`.
theorem norm_eq_one_of_notMem_smallPrimes {ι : Type*} [Fintype ι] {w : ι → ℚ}
    (hw : ∀ i, w i ≠ 0) {p : Nat.Primes} (hp : p ∉ smallPrimes w) (i : ι) :
    ‖((w i : ℚ) : ℚ_[p])‖ = 1 := by
  obtain ⟨hnum, hden⟩ := notMem_smallPrimes hw hp i
  have hq : (((w i : ℚ)) : ℚ_[p]) ≠ 0 := by exact_mod_cast hw i
  have hv : Padic.valuation (((w i : ℚ)) : ℚ_[p]) = 0 := by
    rw [Padic.valuation_ratCast, padicValRat_def]
    rw [show padicValInt (p : ℕ) (w i).num = padicValNat (p : ℕ) (w i).num.natAbs from rfl,
      padicValNat.eq_zero_of_not_dvd hnum, padicValNat.eq_zero_of_not_dvd hden]
    norm_num
  rw [Padic.norm_eq_zpow_neg_valuation hq, hv, neg_zero, zpow_zero]

end PlaceSet

/-! ### WP5.3 — base change and the rank-lowering assembly -/

section Assembly

-- Theorem: base change of a binary rational weighted sum of squares.
theorem wss_cast_val {K : Type*} [CommSemiring K] [Algebra ℚ K] (v z : Fin 2 → ℚ) :
    (algebraMap ℚ K ((weightedSumSquares ℚ v) z)) =
      (weightedSumSquares K (fun i => algebraMap ℚ K (v i)))
        (fun i => algebraMap ℚ K (z i)) := by
  simp only [weightedSumSquares_apply, Fin.sum_univ_two, smul_eq_mul, map_add, map_mul]

-- Theorem: negating all weights preserves isotropy.
theorem isotropic_wss_neg {K : Type*} [Field K] {m : ℕ} {w : Fin m → K}
    (h : (weightedSumSquares K w).Isotropic) :
    (weightedSumSquares K (fun j => -(w j))).Isotropic := by
  obtain ⟨y, hy, hyv⟩ := h
  refine ⟨y, hy, ?_⟩
  simp only [weightedSumSquares_apply, smul_eq_mul] at hyv ⊢
  have hneg : (∑ j, (-(w j)) * (y j * y j)) = -(∑ j, w j * (y j * y j)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hneg, hyv, neg_zero]

-- Theorem: if `Q` represents `-av` and `A/av` is a square (with `A ≠ 0`), then `Q`
-- represents `-A`: scale a representing vector by a square root of `A/av`.
theorem represents_neg_of_represents_neg_of_square {K : Type*} [Field K] {V : Type*}
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {av A : K} (hA : A ≠ 0)
    (hav : av ≠ 0) (h : Q.represents (-av)) (hs : IsSquare (A / av)) :
    Q.represents (-A) := by
  obtain ⟨s, hs⟩ := hs
  obtain ⟨y, hy, hyv⟩ := h
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs
    exact (div_ne_zero hA hav) hs
  refine ⟨s • y, smul_ne_zero hs0 hy, ?_⟩
  have hval : Q (s • y) = s * (s * Q y) := by
    rw [QuadraticMap.map_smul]; ring
  rw [hval, hyv, show s * (s * -av) = -(s * s * av) by ring, hs.symm, div_mul_cancel₀ A hav]

-- Theorem: `⟨c⟩ ⊥ ⟨-w⟩` is isotropic when `⟨w⟩` represents `-c`.
theorem wss_cons_neg_isotropic_of_represents {K : Type*} [Field K] {m : ℕ} (c : K)
    {w : Fin m → K} (h : (weightedSumSquares K w).represents (-c)) :
    (weightedSumSquares K (Fin.cons (-c) (fun j => -(w j)))).Isotropic := by
  obtain ⟨y, hy, hyv⟩ := h
  refine ⟨Fin.cons 1 y, ?_, ?_⟩
  · intro h0
    have h1 : (1 : K) = 0 := by simpa using congr_fun h0 0
    exact one_ne_zero h1
  · have hval : (weightedSumSquares K (Fin.cons (-c) (fun j => -(w j)))) (Fin.cons 1 y) =
        (-c) * 1 ^ 2 + (weightedSumSquares K (fun j => -(w j))) y := by
      simp only [weightedSumSquares_apply, smul_eq_mul]
      rw [Fin.sum_univ_succ]
      simp
    have hneg : (weightedSumSquares K (fun j => -(w j))) y = -(weightedSumSquares K w) y := by
      simp only [weightedSumSquares_apply, smul_eq_mul]
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hval, hneg, hyv]
    ring

-- Theorem: `⟨c⟩ ⊥ ⟨-w⟩` is isotropic when `⟨-w⟩` is isotropic.
theorem wss_cons_neg_isotropic_of_tail {K : Type*} [Field K] {m : ℕ} (c : K)
    {w : Fin m → K} (h : (weightedSumSquares K (fun j => -(w j))).Isotropic) :
    (weightedSumSquares K (Fin.cons (-c) (fun j => -(w j)))).Isotropic := by
  obtain ⟨y, hy, hyv⟩ := h
  refine ⟨Fin.cons 0 y, ?_, ?_⟩
  · intro h0
    apply hy
    funext j
    simpa using congr_fun h0 j.succ
  · have hval : (weightedSumSquares K (Fin.cons (-c) (fun j => -(w j)))) (Fin.cons 0 y) =
        (-c) * 0 ^ 2 + (weightedSumSquares K (fun j => -(w j))) y := by
      simp only [weightedSumSquares_apply, smul_eq_mul]
      rw [Fin.sum_univ_succ]
      simp
    rw [hval, hyv]
    ring

-- Theorem: rational-weight version of `wss_cons_neg_isotropic_of_represents`.
theorem wss_cons_neg_isotropic_of_represents_rat {K : Type*} [Field K]
    {m : ℕ} (A : ℚ) {v : Fin m → ℚ}
    (h : (weightedSumSquares K (fun j => (v j : K))).represents (-(A : K))) :
    (weightedSumSquares K (fun i : Fin (m + 1) =>
      ((Fin.cons (-A) (fun j => -(v j)) : Fin (m + 1) → ℚ) i : K))).Isotropic := by
  have hw : (fun i : Fin (m + 1) =>
      ((Fin.cons (-A) (fun j => -(v j)) : Fin (m + 1) → ℚ) i : K)) =
      Fin.cons (-(A : K)) (fun j => -((v j : K))) := by
    funext i
    induction i using Fin.cases with
    | zero => simp only [Fin.cons_zero]; push_cast; ring
    | succ j => simp only [Fin.cons_succ]; push_cast; ring
  rw [hw]
  exact wss_cons_neg_isotropic_of_represents (A : K) h

-- Theorem: rational-weight version of `wss_cons_neg_isotropic_of_tail`.
theorem wss_cons_neg_isotropic_of_tail_rat {K : Type*} [Field K]
    {m : ℕ} (A : ℚ) {v : Fin m → ℚ}
    (h : (weightedSumSquares K (fun j => -((v j : K)))).Isotropic) :
    (weightedSumSquares K (fun i : Fin (m + 1) =>
      ((Fin.cons (-A) (fun j => -(v j)) : Fin (m + 1) → ℚ) i : K))).Isotropic := by
  have hw : (fun i : Fin (m + 1) =>
      ((Fin.cons (-A) (fun j => -(v j)) : Fin (m + 1) → ℚ) i : K)) =
      Fin.cons (-(A : K)) (fun j => -((v j : K))) := by
    funext i
    induction i using Fin.cases with
    | zero => simp only [Fin.cons_zero]; push_cast; ring
    | succ j => simp only [Fin.cons_succ]; push_cast; ring
  rw [hw]
  exact wss_cons_neg_isotropic_of_tail (A : K) h

-- Theorem: `p`-adic square-class openness with the modulus-8 threshold as explicit factor.
theorem isSquare_div_of_close_padic' (p : ℕ) [Fact p.Prime] {a₀ a : ℚ_[p]}
    (h₀ : a₀ ≠ 0)
    (h : ‖a - a₀‖ < (if p = 2 then 2 ^ (-(2 : ℤ)) else 1) * ‖a₀‖) :
    IsSquare (a / a₀) := by
  by_cases hp : p = 2
  · subst hp
    exact isSquare_div_of_close_padic_two h₀ (by simpa using h)
  · exact isSquare_div_of_close_padic p hp h₀ (by simpa only [ite_eq_right hp, one_mul] using h)

-- Theorem: if `h := ⟨w 0, w 1⟩` represents the nonzero value `av p` locally at every
-- `p ∈ S` and `ar` at the real place, then some rational vector `q` has `h(q) ≠ 0` with
-- `h(q)/av p` a square at every `p ∈ S` and `h(q)/ar` a square in `ℝ`.
theorem exists_rat_value_close {m : ℕ} (w : Fin (m + 2) → ℚ) {S : Finset Nat.Primes}
    (xp : Π p : S, Fin 2 → ℚ_[p]) (av : Π p : S, ℚ_[p]) (hav : ∀ p, av p ≠ 0)
    (hxpa : ∀ p, (weightedSumSquares ℚ_[p] ![w 0, w 1]) (xp p) = av p)
    (xr : Fin 2 → ℝ) (ar : ℝ) (har : ar ≠ 0)
    (hxra : (weightedSumSquares ℝ ![w 0, w 1]) xr = ar) :
    ∃ q : Fin 2 → ℚ, (weightedSumSquares ℚ ![w 0, w 1]) q ≠ 0 ∧
      IsSquare (((weightedSumSquares ℚ ![w 0, w 1]) q : ℝ) / ar) ∧
      ∀ p : S, IsSquare (((weightedSumSquares ℚ ![w 0, w 1]) q : ℚ_[p]) / av p) := by
  classical
  let Bp : S → ℝ := fun p => 1 + ‖xp p 0‖ + ‖xp p 1‖
  let Cp : S → ℝ := fun p => ‖(w 0 : ℚ_[p])‖ + ‖(w 1 : ℚ_[p])‖
  let thrP : S → ℝ := fun p => (if (p : ℕ) = 2 then 2 ^ (-(2 : ℤ)) else 1) * ‖av p‖
  let ηP : S → ℝ := fun p => thrP p / (Cp p * (1 + 2 * Bp p) + 1)
  let Br : ℝ := 1 + ‖xr 0‖ + ‖xr 1‖
  let Cr : ℝ := ‖(w 0 : ℝ)‖ + ‖(w 1 : ℝ)‖
  let ηR : ℝ := ‖ar‖ / (Cr * (1 + 2 * Br) + 1)
  let cand : Finset ℝ := insert 1 (insert (1 / ηR) (S.attach.image fun p => 1 / ηP p))
  let ε : ℝ := 1 / (1 + cand.sum fun c => c)
  have hBrnn : 0 ≤ Br := by simp only [Br]; positivity
  have hCrnn : 0 ≤ Cr := by simp only [Cr]; positivity
  have hBpnn : ∀ p : S, 0 ≤ Bp p := fun p => by simp only [Bp]; positivity
  have hCpnn : ∀ p : S, 0 ≤ Cp p := fun p => by simp only [Cp]; positivity
  have hBrle : ∀ i : Fin 2, ‖xr i‖ ≤ Br := by
    have h0 : ‖xr (0 : Fin 2)‖ ≤ Br := by
      simp only [Br]; linarith [norm_nonneg (xr 1)]
    have h1 : ‖xr (1 : Fin 2)‖ ≤ Br := by
      simp only [Br]; linarith [norm_nonneg (xr 0)]
    intro i; fin_cases i
    · exact h0
    · exact h1
  have hBple : ∀ p : S, ∀ i : Fin 2, ‖xp p i‖ ≤ Bp p := by
    intro p
    have h0 : ‖xp p (0 : Fin 2)‖ ≤ Bp p := by
      simp only [Bp]; linarith [norm_nonneg (xp p 1)]
    have h1 : ‖xp p (1 : Fin 2)‖ ≤ Bp p := by
      simp only [Bp]; linarith [norm_nonneg (xp p 0)]
    intro i; fin_cases i
    · exact h0
    · exact h1
  have hthrP : ∀ p : S, 0 < thrP p := by
    intro p
    simp only [thrP]
    split_ifs with h2
    · have := norm_pos_iff.mpr (hav p); positivity
    · have := norm_pos_iff.mpr (hav p); positivity
  have hηRpos : 0 < ηR := by
    simp only [ηR]
    exact div_pos (norm_pos_iff.mpr har) (by nlinarith)
  have hηPpos : ∀ p : S, 0 < ηP p := by
    intro p
    have hd : 0 < Cp p * (1 + 2 * Bp p) + 1 := by nlinarith [hCpnn p, hBpnn p]
    simpa only [ηP] using div_pos (hthrP p) hd
  have hnonneg : ∀ c ∈ cand, 0 ≤ c := by
    intro c hc
    simp only [cand, Finset.mem_insert] at hc
    rcases hc with rfl | rfl | hc
    · norm_num
    · exact div_nonneg zero_le_one hηRpos.le
    · obtain ⟨p, -, hpc⟩ := Finset.mem_image.mp hc
      rw [← hpc]
      exact div_nonneg zero_le_one (hηPpos p).le
  have hεpos : 0 < ε := by
    simp only [ε]
    exact one_div_pos.mpr (by linarith [Finset.sum_nonneg hnonneg])
  have hεR : ε ≤ ηR := by
    have hmem : (1 / ηR) ∈ cand := by simp [cand]
    have hle : (1 / ηR) ≤ cand.sum (fun c => c) := Finset.single_le_sum hnonneg hmem
    have hpos : 0 < 1 / ηR := one_div_pos.mpr hηRpos
    have hεc : ε ≤ 1 / (1 / ηR) := by
      simp only [ε]
      exact one_div_le_one_div_of_le hpos (by linarith)
    rwa [one_div_one_div] at hεc
  have hεP : ∀ p : S, ε ≤ ηP p := by
    intro p
    have hmem : (1 / ηP p) ∈ cand := by simp [cand]
    have hle : (1 / ηP p) ≤ cand.sum (fun c => c) := Finset.single_le_sum hnonneg hmem
    have hpos : 0 < 1 / ηP p := one_div_pos.mpr (hηPpos p)
    have hεc : ε ≤ 1 / (1 / ηP p) := by
      simp only [ε]
      exact one_div_le_one_div_of_le hpos (by linarith)
    rwa [one_div_one_div] at hεc
  have hε1 : ε ≤ 1 := by
    have hmem : (1 : ℝ) ∈ cand := by simp [cand]
    have hle : (1 : ℝ) ≤ cand.sum (fun c => c) := Finset.single_le_sum hnonneg hmem
    have h := one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num)
      (by linarith : (1 : ℝ) ≤ 1 + cand.sum (fun c => c))
    simpa only [ε, one_div_one] using h
  obtain ⟨q, hqr, hqp⟩ := exists_rat_close_vec' hεpos xr xp
  have hqR : ∀ i, ‖(q i : ℝ) - xr i‖ ≤ ε := fun i => by
    rw [norm_sub_rev]; exact le_of_lt (hqr i)
  have hqP : ∀ p : S, ∀ i, ‖(q i : ℚ_[p]) - xp p i‖ ≤ ε := fun p i => by
    rw [norm_sub_rev]; exact le_of_lt (hqp p i)
  let A : ℚ := (weightedSumSquares ℚ ![w 0, w 1]) q
  have hweqR : (fun i : Fin 2 => (((![w 0, w 1] : Fin 2 → ℚ) i) : ℝ)) =
      ![(w 0 : ℝ), (w 1 : ℝ)] := by funext i; fin_cases i <;> simp
  have hAb : ‖((A : ℚ) : ℝ) - ar‖ ≤ Cr * (ε * (ε + 2 * Br)) := by
    have hcastR : ((A : ℚ) : ℝ) = (weightedSumSquares ℝ
        (fun i : Fin 2 => (((![w 0, w 1] : Fin 2 → ℚ) i) : ℝ)))
        (fun i => (q i : ℝ)) := wss_cast_val _ _
    have hxr' : (weightedSumSquares ℝ
        (fun i : Fin 2 => (((![w 0, w 1] : Fin 2 → ℚ) i) : ℝ))) xr = ar := by
      rw [hweqR]; exact hxra
    have hclose := wss_pair_close (K := ℝ)
      (w := fun i : Fin 2 => (((![w 0, w 1] : Fin 2 → ℚ) i) : ℝ))
      (x := xr) (q := fun i => (q i : ℝ)) (ε := ε) (B := Br)
      (by norm_num) hqR hBrle
    rw [hcastR, ← hxr']
    simpa only [Cr, hweqR, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      using hclose
  have hAb' : ‖((A : ℚ) : ℝ) - ar‖ < ‖ar‖ := by
    refine lt_of_le_of_lt hAb ?_
    have hDnn : 0 ≤ Cr * (1 + 2 * Br) := by nlinarith [hCrnn, hBrnn]
    have hstep1 : ε * (ε + 2 * Br) ≤ ε * (1 + 2 * Br) :=
      mul_le_mul_of_nonneg_left (by linarith) hεpos.le
    have hstep2 : Cr * (ε * (ε + 2 * Br)) ≤ ε * (Cr * (1 + 2 * Br)) := by
      have := mul_le_mul_of_nonneg_left hstep1 hCrnn
      nlinarith
    calc Cr * (ε * (ε + 2 * Br)) ≤ ε * (Cr * (1 + 2 * Br)) := hstep2
      _ ≤ ηR * (Cr * (1 + 2 * Br)) := mul_le_mul_of_nonneg_right hεR hDnn
      _ = ‖ar‖ * (Cr * (1 + 2 * Br)) / (Cr * (1 + 2 * Br) + 1) := by
          simp only [ηR]; rw [div_mul_eq_mul_div]
      _ < ‖ar‖ := by
          rw [div_lt_iff₀ (by linarith)]
          nlinarith [norm_pos_iff.mpr har]
  have hAne : A ≠ 0 := by
    intro hA0
    have hz : ((0 : ℚ) : ℝ) = 0 := by norm_num
    rw [hA0, hz, zero_sub, norm_neg] at hAb'
    exact lt_irrefl _ hAb'
  refine ⟨q, hAne, isSquare_div_of_close_real har hAb', ?_⟩
  intro p
  have hcastP : ((A : ℚ) : ℚ_[p]) = (weightedSumSquares ℚ_[p]
      (fun i : Fin 2 => (((![w 0, w 1] : Fin 2 → ℚ) i) : ℚ_[p])))
      (fun i => (q i : ℚ_[p])) := wss_cast_val _ _
  have hweqP : (fun i : Fin 2 => (((![w 0, w 1] : Fin 2 → ℚ) i) : ℚ_[p])) =
      ![(w 0 : ℚ_[p]), (w 1 : ℚ_[p])] := by funext i; fin_cases i <;> simp
  have hxp' : (weightedSumSquares ℚ_[p]
      (fun i : Fin 2 => (((![w 0, w 1] : Fin 2 → ℚ) i) : ℚ_[p]))) (xp p) = av p := by
    rw [hweqP]; exact hxpa p
  have h2p : ‖(2 : ℚ_[p])‖ ≤ 2 := by
    have h1 : ‖(2 : ℚ_[p])‖ ≤ 1 := by
      rw [show (2 : ℚ_[p]) = ((2 : ℚ) : ℚ_[p]) by norm_cast, Padic.eq_padicNorm]
      exact_mod_cast (padicNorm.of_nat 2)
    linarith
  have hclose := wss_pair_close (K := ℚ_[p])
    (w := fun i : Fin 2 => (((![w 0, w 1] : Fin 2 → ℚ) i) : ℚ_[p]))
    (x := xp p) (q := fun i => (q i : ℚ_[p])) (ε := ε) (B := Bp p)
    h2p (hqP p) (hBple p)
  have hb : ‖((A : ℚ) : ℚ_[p]) - av p‖ ≤ Cp p * (ε * (ε + 2 * Bp p)) := by
    rw [hcastP, ← hxp']
    simpa only [Cp, hweqP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      using hclose
  have hDnn : 0 ≤ Cp p * (1 + 2 * Bp p) := by nlinarith [hCpnn p, hBpnn p]
  have hstep1 : ε * (ε + 2 * Bp p) ≤ ε * (1 + 2 * Bp p) :=
    mul_le_mul_of_nonneg_left (by linarith) hεpos.le
  have hstep2 : Cp p * (ε * (ε + 2 * Bp p)) ≤ ε * (Cp p * (1 + 2 * Bp p)) := by
    have := mul_le_mul_of_nonneg_left hstep1 (hCpnn p)
    nlinarith
  have hb' : ‖((A : ℚ) : ℚ_[p]) - av p‖ < thrP p := by
    refine lt_of_le_of_lt hb ?_
    calc Cp p * (ε * (ε + 2 * Bp p)) ≤ ε * (Cp p * (1 + 2 * Bp p)) := hstep2
      _ ≤ ηP p * (Cp p * (1 + 2 * Bp p)) := mul_le_mul_of_nonneg_right (hεP p) hDnn
      _ = thrP p * (Cp p * (1 + 2 * Bp p)) / (Cp p * (1 + 2 * Bp p) + 1) := by
          simp only [ηP]; rw [div_mul_eq_mul_div]
      _ < thrP p := by
          rw [div_lt_iff₀ (by linarith)]
          nlinarith [hthrP p]
  simp only [thrP] at hb'
  exact isSquare_div_of_close_padic' p (hav p) hb'

-- Theorem: `‖2‖ ≤ 2` in every `p`-adic completion.
theorem norm_two_padic_le_two (p : ℕ) [Fact p.Prime] : ‖(2 : ℚ_[p])‖ ≤ 2 := by
  have h : ‖(2 : ℚ_[p])‖ ≤ 1 := by
    rw [show (2 : ℚ_[p]) = ((2 : ℚ) : ℚ_[p]) by norm_cast, Padic.eq_padicNorm]
    exact_mod_cast (padicNorm.of_nat 2)
  linarith

end Assembly

/-! ### The high-rank diagonal input -/

/-- Diagonal Hasse–Minkowski over `ℚ` in rank `n ≥ 5`: a diagonal form with nonzero rational
weights that is isotropic over every `p`-adic completion and over `ℝ` is isotropic over `ℚ`.
This is the WP5.3 statement, recorded as a `Prop` so that the assembly of `hasseMinkowski`
(WP6.2) can be developed against it while the induction is proved. -/
@[expose] def RankFiveLeDiagonalHM : Prop :=
  ∀ {n : ℕ}, 5 ≤ n → ∀ w : Fin n → ℚ, (∀ i, w i ≠ 0) →
    (∀ (p : ℕ) [Fact (Nat.Prime p)],
      (weightedSumSquares ℚ_[p] (fun i => (w i : ℚ_[p]))).Isotropic) →
    (weightedSumSquares ℝ (fun i => (w i : ℝ))).Isotropic →
    (weightedSumSquares ℚ w).Isotropic

/-! ### WP5.3 — the rank-lowering induction -/

section RankLowering

-- Theorem: diagonal Hasse-Minkowski for rank >= 4, with rank 4 from `RankFourDiagonalHM`.
theorem diagonal_hm_ge_four (h4 : RankFourDiagonalHM) :
    ∀ k, 4 ≤ k → ∀ w : Fin k → ℚ, (∀ i, w i ≠ 0) →
      (∀ (p : ℕ) [Fact (Nat.Prime p)],
        (weightedSumSquares ℚ_[p] (fun i => (w i : ℚ_[p]))).Isotropic) →
      (weightedSumSquares ℝ (fun i => (w i : ℝ))).Isotropic →
      (weightedSumSquares ℚ w).Isotropic := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk w hw hfin hreal
    rcases eq_or_lt_of_le hk with hk4 | hk5
    · subst hk4
      exact h4 w hw hfin hreal
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
      have hm : 3 ≤ m := by omega
      have : NeZero m := ⟨by omega⟩
      set S : Finset Nat.Primes := smallPrimes w with hS
      have hloc : ∀ p : S, ∃ a : ℚ_[p], a ≠ 0 ∧
          (weightedSumSquares ℚ_[p] ![w 0, w 1]).represents a ∧
          (weightedSumSquares ℚ_[p] (fun j : Fin m => w j.succ.succ)).represents (-a) :=
        fun p => exists_local_common_value (m := m)
          (w := fun i : Fin (m + 2) => ((w i : ℚ) : ℚ_[p]))
          (fun i => by exact_mod_cast hw i) (hfin p)
      choose av hav using hloc
      have hav_ne : ∀ p : S, av p ≠ 0 := fun p => (hav p).1
      have hg_rep : ∀ p : S,
          (weightedSumSquares ℚ_[p] (fun j : Fin m => w j.succ.succ)).represents (-(av p)) :=
        fun p => (hav p).2.2
      have hav_rep : ∀ p : S,
          (weightedSumSquares ℚ_[p] ![w 0, w 1]).represents (av p) := fun p => (hav p).2.1
      choose xp hxp_ne hxp using hav_rep
      obtain ⟨ar, har_ne, har_rep, hg_repR⟩ := exists_local_common_value (m := m)
        (w := fun i : Fin (m + 2) => ((w i : ℚ) : ℝ))
        (fun i => by exact_mod_cast hw i) hreal
      choose xr hxr_ne hxr using har_rep
      obtain ⟨q, hqne, hAsqR, hAsqP⟩ :=
        exists_rat_value_close w xp av hav_ne hxp xr ar har_ne hxr
      let A : ℚ := (weightedSumSquares ℚ ![w 0, w 1]) q
      have hAne : A ≠ 0 := hqne
      have hAneP : ∀ p : S, ((A : ℚ) : ℚ_[p]) ≠ 0 := fun p => by exact_mod_cast hAne
      have hAneR : ((A : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hAne
      have hAsqR' : IsSquare (((A : ℚ) : ℝ) / ar) := by simpa only [A] using hAsqR
      have hAsqP' : ∀ p : S, IsSquare (((A : ℚ) : ℚ_[p]) / av p) :=
        fun p => by simpa only [A] using hAsqP p
      have hgA : ∀ p : S, (weightedSumSquares ℚ_[p]
          (fun j : Fin m => w j.succ.succ)).represents (-((A : ℚ) : ℚ_[p])) :=
        fun p => represents_neg_of_represents_neg_of_square (hAneP p) (hav_ne p) (hg_rep p)
          (hAsqP' p)
      have hgAR : (weightedSumSquares ℝ (fun j : Fin m => w j.succ.succ)).represents
          (-((A : ℚ) : ℝ)) :=
        represents_neg_of_represents_neg_of_square hAneR har_ne hg_repR hAsqR'
      let W : Fin (m + 1) → ℚ := Fin.cons (-A) (fun j : Fin m => -(w j.succ.succ))
      have hWne : ∀ i, W i ≠ 0 := by
        intro i
        induction i using Fin.cases with
        | zero => simp only [W, Fin.cons_zero]; exact neg_ne_zero.mpr hAne
        | succ j => simp only [W, Fin.cons_succ]; exact neg_ne_zero.mpr (hw _)
      have hWreal : (weightedSumSquares ℝ (fun i => (W i : ℝ))).Isotropic :=
        wss_cons_neg_isotropic_of_represents_rat A hgAR
      have hWfin : ∀ (p : ℕ) [Fact (Nat.Prime p)],
          (weightedSumSquares ℚ_[p] (fun i => (W i : ℚ_[p]))).Isotropic := by
        intro p hp
        have : Fact (Nat.Prime p) := hp
        by_cases hmem : (⟨p, hp.out⟩ : Nat.Primes) ∈ S
        · exact wss_cons_neg_isotropic_of_represents_rat A (hgA ⟨⟨p, hp.out⟩, hmem⟩)
        · have hmem' : (⟨p, hp.out⟩ : Nat.Primes) ∉ smallPrimes w := by rwa [hS] at hmem
          have hp2 : p ≠ 2 := by
            intro h
            apply hmem
            rw [show (⟨p, hp.out⟩ : Nat.Primes) = ⟨2, Nat.prime_two⟩ from Subtype.ext h]
            exact Finset.mem_insert_self _ _
          let e : Fin 3 ↪ Fin m :=
            ⟨Fin.castLE hm, fun a b hab => Fin.ext (by simpa using congrArg Fin.val hab)⟩
          have hunit : ∀ j : Fin 3, ∃ u : ℤ_[p]ˣ,
              (u : ℚ_[p]) = (fun j' : Fin m => (w j'.succ.succ : ℚ_[p])) (e j) := by
            intro j
            refine exists_padicUnit_of_norm_eq_one (p := p) ?_
            simpa using norm_eq_one_of_notMem_smallPrimes hw hmem' ((e j).succ.succ)
          have htail := isotropic_of_three_units (p := p) (hp := hp2)
            (w := fun j' : Fin m => (w j'.succ.succ : ℚ_[p])) e hunit
          have hneg : (weightedSumSquares ℚ_[p]
              (fun j' : Fin m => -((w j'.succ.succ : ℚ) : ℚ_[p]))).Isotropic := by
            simpa only using isotropic_wss_neg htail
          exact wss_cons_neg_isotropic_of_tail_rat A hneg
      have hWiso : (weightedSumSquares ℚ W).Isotropic :=
        ih (m + 1) (by omega) (by omega) W hWne hWfin hWreal
      obtain ⟨u, hu_ne, hu0⟩ := hWiso
      have hkey : (weightedSumSquares ℚ (fun j : Fin m => w j.succ.succ))
          (fun j => u j.succ) = -A * u 0 ^ 2 := by
        have hval : (weightedSumSquares ℚ W) u = (-A) * u 0 ^ 2 +
            (weightedSumSquares ℚ (fun j : Fin m => -(w j.succ.succ)))
              (fun j => u j.succ) := by
          simp only [W, weightedSumSquares_apply, smul_eq_mul]
          rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          ring
        have hneg : (weightedSumSquares ℚ (fun j : Fin m => -(w j.succ.succ)))
            (fun j => u j.succ) = -(weightedSumSquares ℚ (fun j : Fin m => w j.succ.succ))
            (fun j => u j.succ) := by
          simp only [weightedSumSquares_apply, smul_eq_mul]
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [hval, hneg] at hu0
        linarith
      by_cases hu0z : u 0 = 0
      · apply wss_tail_isotropic m w
        refine ⟨fun j => u j.succ, ?_, ?_⟩
        · intro hy
          apply hu_ne
          funext i
          induction i using Fin.cases with
          | zero => simpa using hu0z
          | succ j => simpa using congr_fun hy j
        · rw [hkey, hu0z]; ring
      · have hqne' : q ≠ 0 := by
          intro h0
          apply hAne
          change (weightedSumSquares ℚ ![w 0, w 1]) q = 0
          rw [h0, map_zero]
        have hyv : (weightedSumSquares ℚ (fun j : Fin m => w j.succ.succ))
            (fun j => u j.succ / u 0) = -A := by
          have hsc : (weightedSumSquares ℚ (fun j : Fin m => w j.succ.succ))
              (fun j => u j.succ / u 0) =
              (weightedSumSquares ℚ (fun j : Fin m => w j.succ.succ)) (fun j => u j.succ)
                / u 0 ^ 2 := by
            simp only [weightedSumSquares_apply, smul_eq_mul]
            rw [Finset.sum_div]
            exact Finset.sum_congr rfl fun j _ => by field_simp
          rw [hsc, hkey, mul_div_assoc, div_self (pow_ne_zero 2 hu0z), mul_one]
        let v : Fin (m + 2) → ℚ :=
          Fin.cons (q 0) (Fin.cons (q 1) (fun j => u j.succ / u 0))
        refine ⟨v, ?_, ?_⟩
        · intro hv
          apply hqne'
          funext i
          fin_cases i
          · simpa [v] using congr_fun hv 0
          · simpa [v] using congr_fun hv 1
        · rw [wss_add_two_val m w v]
          have hvq : (![v 0, v 1] : Fin 2 → ℚ) = q := by
            funext i; fin_cases i <;> simp [v]
          have hvy : (fun j : Fin m => v j.succ.succ) = fun j => u j.succ / u 0 := by
            funext j; simp [v]
          rw [hvq, hvy, hyv]
          ring

-- Theorem: diagonal Hasse-Minkowski for rank at least five (WP5.3).
theorem diagonal_hm_five_le (h4 : RankFourDiagonalHM) :
    ∀ {n : ℕ}, 5 ≤ n → ∀ w : Fin n → ℚ, (∀ i, w i ≠ 0) →
      (∀ (p : ℕ) [Fact (Nat.Prime p)],
        (weightedSumSquares ℚ_[p] (fun i => (w i : ℚ_[p]))).Isotropic) →
      (weightedSumSquares ℝ (fun i => (w i : ℝ))).Isotropic →
      (weightedSumSquares ℚ w).Isotropic :=
  fun {n} hn w hw hfin hreal => diagonal_hm_ge_four h4 n (by omega) w hw hfin hreal

-- Theorem: `RankFiveLeDiagonalHM` holds given the rank-four input.
theorem rankFiveLeDiagonalHM (h4 : RankFourDiagonalHM) : RankFiveLeDiagonalHM :=
  diagonal_hm_five_le h4

end RankLowering

end HasseMinkowski
