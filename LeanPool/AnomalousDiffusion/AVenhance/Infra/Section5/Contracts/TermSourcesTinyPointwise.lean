/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Algebra.Order.Chebyshev

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesBasic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWeightedFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordSplitPrincipal
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.Tiny
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SourceErrors
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorBoundsL2Ioi
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorBoundsPointwise

/-! # Pointwise bounds for the `tiny` source contract

Pure pointwise (in `(t, x)`) calculus for the last-iterate error `e_{m-1}`:

* `e = -B ∇V` where `V = T_{N*} - T_{N*-1}` is the last increment and
  `B = K_m - κ_{m-1} I + s_{m-1}`;
* the Leibniz expansion of `∇(∇ · (B ∇V))` into the words of length `≤ 2` applied to `V`, with
  the coefficient jets of `B` (`sc_gradDiv_abs_le`);
* the pointwise bound of the nondivergence part `∑_k ξ_{m,k} χTilde_{m,k} · (∇X ∘ X⁻¹) ∇(∇ · e)` by
  `|∇(∇ · e)|` (`sc_nd_sq_le`).

Only products of coordinate bounds are used; the constants are crude since the source (7900–7925)
leaves an enormous amount of room (`N_*` large). -/

@[expose] public section

open Homogenization
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section4

/-- The seven words of length at most two. -/
def scWords2 : Finset (List (Fin 2)) :=
  {[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1]}

theorem mem_scWords2 {w : List (Fin 2)} (hw : w.length ≤ 2) : w ∈ scWords2 := by
  match w, hw with
  | [], _ => decide
  | [a], _ => fin_cases a <;> decide
  | [a, b], _ => fin_cases a <;> fin_cases b <;> decide

/-- `|∇ ∇·(A ∇v)|` in terms of ordered Leibniz splits of the words `[k, i]`. -/
theorem sc_gradDiv_flux_eq {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : Vec 2 → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (x : Vec 2) (i : Fin 2) :
    spaceGrad (vecDiv (fun y => (A y).mulVec (spaceGrad v y))) x i =
      ∑ k : Fin 2, iterateWordFlux A v [k, i] x k := by
  have hH : ContDiff ℝ (⊤ : ℕ∞) (fun x => (A x).mulVec (spaceGrad v x)) := by
    apply contDiff_pi.mpr
    intro i
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ j : Fin 2, A x i j * spaceGrad v x j)
    apply ContDiff.sum
    intro j _
    exact (contDiff_pi.mp (contDiff_pi.mp hA i) j).mul
      (contDiff_pi.mp (iterate_gradient_smooth hv) j)
  have h1 := iterateSpatialWord_divergence hH [i]
  have h2 : spaceGrad (vecDiv (fun y => (A y).mulVec (spaceGrad v y))) x i =
      iterateSpatialWord [i] (vecDiv (fun y => (A y).mulVec (spaceGrad v y))) x := rfl
  rw [h2, h1]
  unfold vecDiv
  refine Finset.sum_congr rfl fun k _ => ?_
  exact congrFun (iterateSpatialWord_matrix_flux hA hv [k, i] k) x

theorem sc_list_abs_sum_le {α : Type*} (L : List α) (f : α → ℝ) (c : ℝ)
    (h : ∀ a ∈ L, |f a| ≤ c) : |(L.map f).sum| ≤ (L.length : ℝ) * c := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    calc _ ≤ |f a| + |(L.map f).sum| := abs_add_le _ _
      _ ≤ c + (L.length : ℝ) * c := add_le_add h1 h2
      _ = ((L.length : ℝ) + 1) * c := by ring

/-- Each term of the expanded flux of `∇ ∇·(A ∇v)` is bounded by the coefficient jets times
the gradient of a word of length `≤ 2` applied to `v`. -/
theorem sc_flux_term_abs_le {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : Vec 2 → ℝ} (x : Vec 2)
    {D r : ℝ} (hD : 0 ≤ D) (hr : 1 ≤ r)
    (hAj : ∀ p : List (Fin 2), p.length ≤ 2 → ∀ j k,
      |iterateMatrixWord A p x j k| ≤ D * (p.length.factorial : ℝ) * r ^ p.length)
    (w : List (Fin 2)) (hw : w.length = 2) {p : List (Fin 2) × List (Fin 2)}
    (hp : p ∈ iterateSpatialSplits w) (k j : Fin 2) :
    |iterateSpatialWord p.1 (fun y => A y k j) x * spaceGrad (iterateSpatialWord p.2 v) x j| ≤
      2 * D * r ^ 2 * ∑ w' ∈ scWords2,
        Real.sqrt (vecNormSq (spaceGrad (iterateSpatialWord w' v) x)) := by
  have hord := iterateSpatialSplits_orders w hp
  have h1 : p.1.length ≤ 2 := by omega
  have h2 : p.2.length ≤ 2 := by omega
  have hcoef := hAj p.1 h1 k j
  have hfac : (p.1.length.factorial : ℝ) ≤ 2 := by
    interval_cases hl : p.1.length <;> norm_num [Nat.factorial]
  have hrp : r ^ p.1.length ≤ r ^ 2 := pow_le_pow_right₀ hr h1
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hcoef' : |iterateSpatialWord p.1 (fun y => A y k j) x| ≤ 2 * D * r ^ 2 := by
    refine hcoef.trans ?_
    have hf0 : (0 : ℝ) ≤ (p.1.length.factorial : ℝ) := Nat.cast_nonneg _
    calc D * (p.1.length.factorial : ℝ) * r ^ p.1.length ≤ D * 2 * r ^ 2 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hfac hD) hrp (by positivity) (by positivity)
      _ = 2 * D * r ^ 2 := by ring
  have hgrad : |spaceGrad (iterateSpatialWord p.2 v) x j| ≤
      ∑ w' ∈ scWords2, Real.sqrt (vecNormSq (spaceGrad (iterateSpatialWord w' v) x)) := by
    refine (RelativeError.abs_apply_le_sqrt_vecNormSq _ j).trans ?_
    exact Finset.single_le_sum (f := fun w' =>
      Real.sqrt (vecNormSq (spaceGrad (iterateSpatialWord w' v) x)))
      (fun _ _ => Real.sqrt_nonneg _) (mem_scWords2 h2)
  rw [abs_mul]
  exact mul_le_mul hcoef' hgrad (abs_nonneg _) (by positivity)

/-- **Pointwise bound of `∇ ∇·(A ∇v)`** by the coefficient jets of `A` (orders `≤ 2`) and the
gradients of the words of length `≤ 2` applied to `v`. -/
theorem sc_gradDiv_abs_le {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : Vec 2 → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (x : Vec 2)
    {D r : ℝ} (hD : 0 ≤ D) (hr : 1 ≤ r)
    (hAj : ∀ p : List (Fin 2), p.length ≤ 2 → ∀ j k,
      |iterateMatrixWord A p x j k| ≤ D * (p.length.factorial : ℝ) * r ^ p.length)
    (i : Fin 2) :
    |spaceGrad (vecDiv (fun y => (A y).mulVec (spaceGrad v y))) x i| ≤
      32 * D * r ^ 2 * ∑ w ∈ scWords2,
        Real.sqrt (vecNormSq (spaceGrad (iterateSpatialWord w v) x)) := by
  set S : ℝ := ∑ w ∈ scWords2, Real.sqrt (vecNormSq (spaceGrad (iterateSpatialWord w v) x))
    with hS
  have hterm : ∀ k : Fin 2, |iterateWordFlux A v [k, i] x k| ≤ 16 * D * r ^ 2 * S := by
    intro k
    unfold iterateWordFlux
    have hj : ∀ j : Fin 2, |((iterateSpatialSplits [k, i]).map (fun p =>
        iterateSpatialWord p.1 (fun y => A y k j) x *
          spaceGrad (iterateSpatialWord p.2 v) x j)).sum| ≤ 8 * D * r ^ 2 * S := by
      intro j
      have hlen : (iterateSpatialSplits [k, i]).length = 4 := by
        simpa using iterateSpatialSplits_length [k, i]
      have h := sc_list_abs_sum_le (iterateSpatialSplits [k, i]) (fun p =>
        iterateSpatialWord p.1 (fun y => A y k j) x *
          spaceGrad (iterateSpatialWord p.2 v) x j) (2 * D * r ^ 2 * S)
        (fun p hp => sc_flux_term_abs_le x hD hr hAj [k, i] rfl hp k j)
      rw [hlen] at h
      calc _ ≤ ((4 : ℕ) : ℝ) * (2 * D * r ^ 2 * S) := h
        _ = 8 * D * r ^ 2 * S := by push_cast; ring
    calc _ ≤ |((iterateSpatialSplits [k, i]).map (fun p =>
          iterateSpatialWord p.1 (fun y => A y k 0) x *
            spaceGrad (iterateSpatialWord p.2 v) x 0)).sum| +
        |((iterateSpatialSplits [k, i]).map (fun p =>
          iterateSpatialWord p.1 (fun y => A y k 1) x *
            spaceGrad (iterateSpatialWord p.2 v) x 1)).sum| := by
          rw [Fin.sum_univ_two]; exact abs_add_le _ _
      _ ≤ 8 * D * r ^ 2 * S + 8 * D * r ^ 2 * S := add_le_add (hj 0) (hj 1)
      _ = 16 * D * r ^ 2 * S := by ring
  rw [sc_gradDiv_flux_eq hA hv x i]
  calc _ ≤ |iterateWordFlux A v [0, i] x 0| + |iterateWordFlux A v [1, i] x 1| := by
        rw [Fin.sum_univ_two]; exact abs_add_le _ _
    _ ≤ 16 * D * r ^ 2 * S + 16 * D * r ^ 2 * S := add_le_add (hterm 0) (hterm 1)
    _ = 32 * D * r ^ 2 * S := by ring

theorem sc_vecNormSq_eq (v : Vec 2) : vecNormSq v = v 0 * v 0 + v 1 * v 1 := by
  simp [vecNormSq, vecDot, Fin.sum_univ_two]

theorem sc_card_scWords2 : scWords2.card = 7 := by decide

/-- `|∇ ∇·(A ∇v)|²` is bounded by the sum of the squares of the word gradients. -/
theorem sc_gradDiv_vecNormSq_le {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : Vec 2 → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (x : Vec 2)
    {D r : ℝ} (hD : 0 ≤ D) (hr : 1 ≤ r)
    (hAj : ∀ p : List (Fin 2), p.length ≤ 2 → ∀ j k,
      |iterateMatrixWord A p x j k| ≤ D * (p.length.factorial : ℝ) * r ^ p.length) :
    vecNormSq (spaceGrad (vecDiv (fun y => (A y).mulVec (spaceGrad v y))) x) ≤
      14336 * D ^ 2 * r ^ 4 * ∑ w ∈ scWords2, vecNormSq (spaceGrad (iterateSpatialWord w v) x) := by
  set S : ℝ := ∑ w ∈ scWords2, Real.sqrt (vecNormSq (spaceGrad (iterateSpatialWord w v) x))
    with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have hcs : S ^ 2 ≤ 7 * ∑ w ∈ scWords2, vecNormSq (spaceGrad (iterateSpatialWord w v) x) := by
    have h := sq_sum_le_card_mul_sum_sq (s := scWords2)
      (f := fun w => Real.sqrt (vecNormSq (spaceGrad (iterateSpatialWord w v) x)))
    rw [sc_card_scWords2] at h
    have hsq : ∀ w ∈ scWords2, Real.sqrt (vecNormSq (spaceGrad (iterateSpatialWord w v) x)) ^ 2 =
        vecNormSq (spaceGrad (iterateSpatialWord w v) x) := fun w _ =>
      Real.sq_sqrt (vecNormSq_nonneg _)
    rw [Finset.sum_congr rfl hsq] at h
    exact_mod_cast h
  have hb := fun i => sc_gradDiv_abs_le hA hv x hD hr hAj i
  rw [sc_vecNormSq_eq]
  have h0 := hb 0
  have h1 := hb 1
  have hW : 0 ≤ 32 * D * r ^ 2 * S := by
    have : 0 ≤ r := by linarith
    positivity
  have e0 : spaceGrad (vecDiv (fun y => (A y).mulVec (spaceGrad v y))) x 0 *
      spaceGrad (vecDiv (fun y => (A y).mulVec (spaceGrad v y))) x 0 ≤
      (32 * D * r ^ 2 * S) ^ 2 := by
    rw [← sq]; exact sq_le_sq' (by linarith [abs_le.mp h0]) (abs_le.mp h0).2
  have e1 : spaceGrad (vecDiv (fun y => (A y).mulVec (spaceGrad v y))) x 1 *
      spaceGrad (vecDiv (fun y => (A y).mulVec (spaceGrad v y))) x 1 ≤
      (32 * D * r ^ 2 * S) ^ 2 := by
    rw [← sq]; exact sq_le_sq' (by linarith [abs_le.mp h1]) (abs_le.mp h1).2
  calc _ ≤ 2 * (32 * D * r ^ 2 * S) ^ 2 := by linarith
    _ = 2048 * D ^ 2 * r ^ 4 * S ^ 2 := by ring
    _ ≤ 2048 * D ^ 2 * r ^ 4 * (7 * ∑ w ∈ scWords2,
          vecNormSq (spaceGrad (iterateSpatialWord w v) x)) := by
        apply mul_le_mul_of_nonneg_left hcs
        have : 0 ≤ r := by linarith
        positivity
    _ = _ := by ring

/-- A matrix with entries of size `≤ b` maps `g` to a vector of squared norm `≤ 4 b² |g|²`. -/
theorem sc_mulVec_vecNormSq_le {M : Matrix (Fin 2) (Fin 2) ℝ} {b : ℝ} (g : Vec 2)
    (hM : ∀ i j, |M i j| ≤ b) : vecNormSq (M.mulVec g) ≤ 4 * b ^ 2 * vecNormSq g := by
  have hb : 0 ≤ b := (abs_nonneg _).trans (hM 0 0)
  have hk : ∀ k : Fin 2, (M.mulVec g k) ^ 2 ≤ 2 * b ^ 2 * (g 0 * g 0 + g 1 * g 1) := by
    intro k
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have h0 := hM k 0
    have h1 := hM k 1
    have m0 : M k 0 ^ 2 ≤ b ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) h0 2
      rwa [sq_abs] at this
    have m1 : M k 1 ^ 2 ≤ b ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) h1 2
      rwa [sq_abs] at this
    have e0 : (M k 0 * g 0) ^ 2 ≤ b ^ 2 * (g 0 * g 0) := by
      rw [mul_pow, ← sq]; exact mul_le_mul_of_nonneg_right m0 (sq_nonneg _)
    have e1 : (M k 1 * g 1) ^ 2 ≤ b ^ 2 * (g 1 * g 1) := by
      rw [mul_pow, ← sq]; exact mul_le_mul_of_nonneg_right m1 (sq_nonneg _)
    nlinarith [sq_nonneg (M k 0 * g 0 - M k 1 * g 1)]
  rw [sc_vecNormSq_eq, sc_vecNormSq_eq]
  have h0 := hk 0
  have h1 := hk 1
  nlinarith

/-- A window of width `5/2` around `t/τ_m` contains at most three integers `k`, so at most three
`ξ_{m,k}(t)` are nonzero. -/
theorem sc_xi_support_finset {β : ℝ} (I : Ingredients β) (m : ℕ) (t : ℝ) :
    ∃ s : Finset ℤ, s.card ≤ 3 ∧ ∀ k : ℤ, I.xiMK m k t ≠ 0 → k ∈ s := by
  have hτ := I.tau_pos' m
  set u : ℝ := t / tau β I.Λ m with hu
  refine ⟨Finset.Icc ⌈u - 5 / 4⌉ ⌊u + 5 / 4⌋, ?_, ?_⟩
  · rw [Int.card_Icc]
    have h1 : (⌊u + 5 / 4⌋ : ℝ) ≤ u + 5 / 4 := Int.floor_le _
    have h2 : u - 5 / 4 ≤ (⌈u - 5 / 4⌉ : ℝ) := Int.le_ceil _
    have h3 : ⌊u + 5 / 4⌋ - ⌈u - 5 / 4⌉ ≤ 2 := by
      have : ((⌊u + 5 / 4⌋ - ⌈u - 5 / 4⌉ : ℤ) : ℝ) < 3 := by push_cast; linarith
      have : ⌊u + 5 / 4⌋ - ⌈u - 5 / 4⌉ < 3 := by exact_mod_cast this
      omega
    omega
  · intro k hk
    have hmem : (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m ∈ Set.Icc (-(5 / 4) : ℝ) (5 / 4) := by
      by_contra hnot
      apply hk
      have h1 := I.xi_le_ind ((t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m)
      have h2 := I.ind_le_xi ((t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m)
      rw [indIcc_eq_zero_of_not_mem hnot] at h1
      have h3 := indIcc_nonneg' (-(3 / 4)) (3 / 4) ((t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m)
      exact le_antisymm h1 (h3.trans h2)
    have hq : (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m = u - k := by
      rw [hu]; field_simp
    rw [hq] at hmem
    rw [Finset.mem_Icc]
    constructor
    · exact Int.ceil_le.2 (by linarith [hmem.2])
    · exact Int.le_floor.2 (by linarith [hmem.1])

theorem sc_xiMK_abs_le_one {β : ℝ} (I : Ingredients β) (m : ℕ) (k : ℤ) (t : ℝ) :
    |I.xiMK m k t| ≤ 1 := by
  have h1 := I.ind_le_xi ((t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m)
  have h2 := I.xi_le_ind ((t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m)
  have h3 : 0 ≤ indIcc (-(3 / 4) : ℝ) (3 / 4) ((t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m) :=
    indIcc_nonneg' _ _ _
  have h4 : indIcc (-(5 / 4) : ℝ) (5 / 4) ((t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m) ≤ 1 := by
    by_cases h : ((t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m) ∈ Set.Icc (-(5 / 4) : ℝ) (5 / 4) <;>
      simp [indIcc, h]
  have hx : I.xiMK m k t = I.xi ((t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m) := rfl
  rw [hx, abs_le]
  exact ⟨by linarith, by linarith⟩

/-- **Pointwise bound of the nondivergence part of `tiny`** by `|∇(∇·e)|`. -/
theorem sc_nd_sq_le {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {κm : ℝ} (e : ℝ → Vec 2 → Vec 2) (t : ℝ)
    {cχ : ℝ} (hχ : ∀ (k : ℤ) (x : Vec 2) (j : Fin 2), |I.chiTilde hΦ m κm k t x j| ≤ cχ)
    (x : Vec 2) :
    (tinyNondivergencePart I hΦ m κm e t x) ^ 2 ≤ 5184 * cχ ^ 2 * vecNormSq (gradDiv e t x) := by
  obtain ⟨s, hs3, hs⟩ := sc_xi_support_finset I m t
  set g : Vec 2 := gradDiv e t x with hg
  set ng : ℝ := Real.sqrt (vecNormSq g) with hng
  have hng0 : 0 ≤ ng := Real.sqrt_nonneg _
  have hcχ : 0 ≤ cχ := (abs_nonneg _).trans (hχ 0 x 0)
  have hε1 : epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1 :=
    Real.rpow_le_one (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le).le (Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt
      (by exact_mod_cast I.two_pow_seven_le))
      (by have := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt; linarith)
  set f : ℤ → ℝ := fun k => I.xiMK m k t * vecDot (I.chiTilde hΦ m κm k t x)
    ((flowGradK I hΦ m k t x).mulVec g) with hf
  have hzero : ∀ k ∉ s, f k = 0 := by
    intro k hk
    have : I.xiMK m k t = 0 := by
      by_contra hne
      exact hk (hs k hne)
    simp [hf, this]
  have hbound : ∀ k ∈ s, |f k| ≤ 24 * cχ * ng := by
    intro k _
    by_cases hξ : I.xiMK m k t = 0
    · simp only [hf, hξ, zero_mul, abs_zero]
      positivity
    have hQ : ∀ i j, |(flowGradK I hΦ m k t x) i j| ≤ 2 :=
      RelativeError.abs_le_two_of_sub_one hε1 (fun i j => RelativeError.flowGrad_sub_one_le hΦ hm
          k hξ x i j)
    have hgj : ∀ j, |g j| ≤ ng := fun j => RelativeError.abs_apply_le_sqrt_vecNormSq g j
    have hQg := fun j => RelativeError.abs_mulVec_le (M := flowGradK I hΦ m k t x) (μ := 2) (gT :=
        ng) hQ hgj j
    have hdot : |vecDot (I.chiTilde hΦ m κm k t x) ((flowGradK I hΦ m k t x).mulVec g)| ≤
        8 * cχ * ng := by
      simp only [vecDot, Fin.sum_univ_two]
      have h0 := RelativeError.abs_mul_le_of_le (hχ k x 0) (hQg 0)
      have h1 := RelativeError.abs_mul_le_of_le (hχ k x 1) (hQg 1)
      have := RelativeError.abs_add_le_of_le h0 h1
      linarith
    rw [hf]
    simp only
    rw [abs_mul]
    calc _ ≤ 1 * (8 * cχ * ng) :=
          mul_le_mul (sc_xiMK_abs_le_one I m k t) hdot (abs_nonneg _) zero_le_one
      _ ≤ 24 * cχ * ng := by
          have : 0 ≤ cχ * ng := mul_nonneg hcχ hng0
          nlinarith
  have hnd : tinyNondivergencePart I hΦ m κm e t x = ∑ k ∈ s, f k := by
    unfold tinyNondivergencePart
    exact tsum_eq_sum hzero
  have habs : |tinyNondivergencePart I hΦ m κm e t x| ≤ 72 * cχ * ng := by
    rw [hnd]
    calc |∑ k ∈ s, f k| ≤ ∑ k ∈ s, |f k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ s, 24 * cχ * ng := Finset.sum_le_sum hbound
      _ = (s.card : ℝ) * (24 * cχ * ng) := by simp
      _ ≤ 3 * (24 * cχ * ng) := by
          apply mul_le_mul_of_nonneg_right (by exact_mod_cast hs3)
          positivity
      _ = 72 * cχ * ng := by ring
  have hsq : ng ^ 2 = vecNormSq g := Real.sq_sqrt (vecNormSq_nonneg _)
  calc _ = |tinyNondivergencePart I hΦ m κm e t x| ^ 2 := (sq_abs _).symm
    _ ≤ (72 * cχ * ng) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ = 5184 * cχ ^ 2 * vecNormSq g := by rw [← hsq]; ring

theorem sc_spaceGrad_neg (f : Vec 2 → ℝ) (x : Vec 2) :
    spaceGrad (fun y => -f y) x = -spaceGrad f x := by
  funext i
  simp [spaceGrad, fderiv_fun_neg]

theorem sc_vecDiv_neg (H : Vec 2 → Vec 2) (x : Vec 2) :
    vecDiv (fun y => -H y) x = -vecDiv H x := by
  unfold vecDiv
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (fun y => (-H y) i) = fun y => -(H y i) := by funext y; rfl
  rw [h, sc_spaceGrad_neg]
  rfl

/-- The coefficient matrix of the last-iterate error. -/
def scCoeff {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) (m : ℕ)
    (κm κprev : ℝ) (t : ℝ) (y : Vec 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) + I.sMat hΦ m κm t y

/-- `e_{m-1} = -B ∇V` for the last increment `V = T_{N*} - T_{N*-1}`. -/
theorem sc_iterateError_eq {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm κprev : ℝ) (T : ℕ → ℝ → Vec 2 → ℝ) (t : ℝ)
    (hN : 1 ≤ Nstar β) (hTa : ContDiff ℝ (⊤ : ℕ∞) (T (Nstar β) t))
    (hTb : ContDiff ℝ (⊤ : ℕ∞) (T (Nstar β - 1) t)) (y : Vec 2) :
    iterateError I hΦ m κm κprev T t y =
      -((scCoeff I hΦ m κm κprev t y).mulVec (spaceGrad (iterateIncrement T (Nstar β) t) y)) := by
  obtain ⟨n, hn⟩ : ∃ n, Nstar β = n + 1 := ⟨Nstar β - 1, by omega⟩
  have hinc : iterateIncrement T (Nstar β) t = fun x => T (Nstar β) t x - T (Nstar β - 1) t x := by
    rw [hn, iterateIncrement_succ]
    simp
  have hdiff : spaceGrad (iterateIncrement T (Nstar β) t) y =
      spaceGrad (T (Nstar β) t) y - spaceGrad (T (Nstar β - 1) t) y := by
    rw [hinc]
    funext i
    simp only [spaceGrad, Pi.sub_apply]
    rw [fderiv_fun_sub (hTa.differentiable (by simp) y) (hTb.differentiable (by simp) y)]
    rfl
  rw [hdiff, Matrix.mulVec_sub, neg_sub]
  simp only [iterateError, scCoeff, Matrix.mulVec_sub]

theorem sc_vecNormSq_neg (v : Vec 2) : vecNormSq (-v) = vecNormSq v := by
  rw [sc_vecNormSq_eq, sc_vecNormSq_eq]
  simp

/-- **Pointwise `L²` bound of `e_{m-1}`** by the gradient of the last increment. -/
theorem sc_e_vecNormSq_le {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm κprev : ℝ) (T : ℕ → ℝ → Vec 2 → ℝ) (t : ℝ)
    (hN : 1 ≤ Nstar β) (hTa : ContDiff ℝ (⊤ : ℕ∞) (T (Nstar β) t))
    (hTb : ContDiff ℝ (⊤ : ℕ∞) (T (Nstar β - 1) t)) (x : Vec 2) {b : ℝ}
    (hb : ∀ j k, |scCoeff I hΦ m κm κprev t x j k| ≤ b) :
    vecNormSq (iterateError I hΦ m κm κprev T t x) ≤
      4 * b ^ 2 * vecNormSq (spaceGrad (iterateIncrement T (Nstar β) t) x) := by
  rw [sc_iterateError_eq I hΦ m κm κprev T t hN hTa hTb x, sc_vecNormSq_neg]
  exact sc_mulVec_vecNormSq_le _ hb

/-- `∇(∇·e)` is minus the gradient of the divergence of the flux `B ∇V`. -/
theorem sc_gradDiv_error_eq {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm κprev : ℝ) (T : ℕ → ℝ → Vec 2 → ℝ) (t : ℝ)
    (hN : 1 ≤ Nstar β) (hTa : ContDiff ℝ (⊤ : ℕ∞) (T (Nstar β) t))
    (hTb : ContDiff ℝ (⊤ : ℕ∞) (T (Nstar β - 1) t)) (x : Vec 2) :
    gradDiv (iterateError I hΦ m κm κprev T) t x =
      -spaceGrad (vecDiv (fun y => (scCoeff I hΦ m κm κprev t y).mulVec
        (spaceGrad (iterateIncrement T (Nstar β) t) y))) x := by
  have he : iterateError I hΦ m κm κprev T t = fun y =>
      -((scCoeff I hΦ m κm κprev t y).mulVec (spaceGrad (iterateIncrement T (Nstar β) t) y)) := by
    funext y
    exact sc_iterateError_eq I hΦ m κm κprev T t hN hTa hTb y
  unfold gradDiv
  rw [he]
  have hfun : (fun y => vecDiv (fun z => -((scCoeff I hΦ m κm κprev t z).mulVec
      (spaceGrad (iterateIncrement T (Nstar β) t) z))) y) = fun y => -(vecDiv (fun z =>
      (scCoeff I hΦ m κm κprev t z).mulVec
        (spaceGrad (iterateIncrement T (Nstar β) t) z)) y) := by
    funext y
    exact sc_vecDiv_neg _ y
  rw [hfun, sc_spaceGrad_neg]

/-- **Pointwise bound of the nondivergence part of `tiny` by the word gradients of the last
increment**, from the coefficient jets of `B` of orders `≤ 2`. -/
theorem sc_nd_sq_le_words {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {κm κprev : ℝ} (T : ℕ → ℝ → Vec 2 → ℝ)
    (t : ℝ) (hN : 1 ≤ Nstar β) (hTa : ContDiff ℝ (⊤ : ℕ∞) (T (Nstar β) t))
    (hTb : ContDiff ℝ (⊤ : ℕ∞) (T (Nstar β - 1) t))
    (hAs : ContDiff ℝ (⊤ : ℕ∞) (scCoeff I hΦ m κm κprev t))
    {cχ : ℝ} (hχ : ∀ (k : ℤ) (x : Vec 2) (j : Fin 2), |I.chiTilde hΦ m κm k t x j| ≤ cχ)
    (x : Vec 2) {D r : ℝ} (hD : 0 ≤ D) (hr : 1 ≤ r)
    (hAj : ∀ p : List (Fin 2), p.length ≤ 2 → ∀ j k,
      |iterateMatrixWord (scCoeff I hΦ m κm κprev t) p x j k| ≤
        D * (p.length.factorial : ℝ) * r ^ p.length) :
    (tinyNondivergencePart I hΦ m κm (iterateError I hΦ m κm κprev T) t x) ^ 2 ≤
      5184 * cχ ^ 2 * (14336 * D ^ 2 * r ^ 4) * ∑ w ∈ scWords2,
        vecNormSq (spaceGrad (iterateSpatialWord w (iterateIncrement T (Nstar β) t)) x) := by
  have hV : ContDiff ℝ (⊤ : ℕ∞) (iterateIncrement T (Nstar β) t) := by
    obtain ⟨n, hn⟩ : ∃ n, Nstar β = n + 1 := ⟨Nstar β - 1, by omega⟩
    have hinc : iterateIncrement T (Nstar β) t =
        fun x => T (Nstar β) t x - T (Nstar β - 1) t x := by
      rw [hn, iterateIncrement_succ]
      simp
    rw [hinc]
    exact hTa.sub hTb
  have h1 := sc_nd_sq_le I hΦ hm (iterateError I hΦ m κm κprev T) t hχ x
  have h2 := sc_gradDiv_vecNormSq_le hAs hV x hD hr hAj
  rw [sc_gradDiv_error_eq I hΦ m κm κprev T t hN hTa hTb x, sc_vecNormSq_neg] at h1
  have hc : 0 ≤ 5184 * cχ ^ 2 := by positivity
  calc _ ≤ 5184 * cχ ^ 2 * vecNormSq (spaceGrad (vecDiv (fun y => (scCoeff I hΦ m κm κprev t
      y).mulVec
        (spaceGrad (iterateIncrement T (Nstar β) t) y))) x) := h1
    _ ≤ 5184 * cχ ^ 2 * (14336 * D ^ 2 * r ^ 4 * ∑ w ∈ scWords2,
        vecNormSq (spaceGrad (iterateSpatialWord w (iterateIncrement T (Nstar β) t)) x)) :=
        mul_le_mul_of_nonneg_left h2 hc
    _ = _ := by ring

end AVenhance.Infra.Section5.Contracts
