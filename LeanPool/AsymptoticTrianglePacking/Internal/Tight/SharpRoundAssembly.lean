/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.SharpRound
public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.Pruning
public import LeanPool.AsymptoticTrianglePacking.Internal.Prelude
public import LeanPool.AsymptoticTrianglePacking.Internal.Covered
public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.CoverVariance
public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.Selection
public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.SafeDegree
public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.LossVariance
public import Mathlib.Algebra.Order.Chebyshev
public import LeanPool.AsymptoticTrianglePacking.Internal.Round
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Real.Sqrt


/-!
# LeanPool.AsymptoticTrianglePacking.Internal — the Efron–Stein (bounded-differences) variance
inequality on a finite Bernoulli cube

This file is elementary and self-contained: no measure theory, only `Finset` sums.  For a finite
index type `ι` and `p ∈ [0,1]` the *Bernoulli cube* is the finite set `ι → Bool` weighted by

  `wt p ω = ∏ i, (if ω i then p else 1 − p)`,

with expectation `Exp p f = ∑ ω, wt p ω · f ω`.  The main result is

  `LeanPool.AsymptoticTrianglePacking.Internal.Cube.variance_le_sum_sq_diff` :
    `Exp p f² − (Exp p f)² ≤ ∑ i, p(1−p)·Exp p ((D i f)²)`,

where `D i f ω = f (ω[i ↦ true]) − f (ω[i ↦ false])` is the discrete derivative in coordinate `i`.
This is the Efron–Stein / tensorization-of-variance inequality; Mathlib has no form of it.

The proof is the usual one-coordinate-at-a-time argument, organised through the averaging operator
`avgOne p i f ω = p·f (ω[i ↦ true]) + (1−p)·f (ω[i ↦ false])`, which satisfies

* `Exp p (avgOne p i f) = Exp p f`,
* `Exp p f² − Exp p (avgOne p i f)² = p(1−p)·Exp p ((D i f)²)` (the exact one-coordinate variance
  decomposition), and hence `Exp p (avgOne p i f)² ≤ Exp p f²`,
* `D i (avgOne p j f) = avgOne p j (D i f)` for `i ≠ j`.

Averaging over a duplicate-free list exhausting `ι` turns `f` into the constant `Exp p f`, and the
telescoping sum of the second bullet is exactly the statement.
-/

public section

open Finset

namespace LeanPool.AsymptoticTrianglePacking.Internal.Cube

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The weighted cube -/

/-- The Bernoulli(`p`) weight of a configuration of the cube `ι → Bool`. -/
def wt (p : ℝ) (ω : ι → Bool) : ℝ := ∏ i, (if ω i then p else 1 - p)

/-- The Bernoulli(`p`) weight with coordinate `i` omitted. -/
def wtc (i : ι) (p : ℝ) (ω : ι → Bool) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, (if ω j then p else 1 - p)

/-- The expectation of `f` on the Bernoulli(`p`) cube. -/
def Exp (p : ℝ) (f : (ι → Bool) → ℝ) : ℝ := ∑ ω, wt p ω * f ω

omit [DecidableEq ι] in
theorem wt_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ω : ι → Bool) : 0 ≤ wt p ω :=
  Finset.prod_nonneg fun i _ => by split_ifs <;> linarith

theorem wtc_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i : ι) (ω : ι → Bool) : 0 ≤ wtc i p ω :=
  Finset.prod_nonneg fun j _ => by split_ifs <;> linarith

theorem sum_wt {p : ℝ} : ∑ ω : ι → Bool, wt p ω = 1 := by
  change ∑ ω : ι → Bool, ∏ i, (if ω i then p else 1 - p) = 1
  rw [← Fintype.prod_sum (fun (_ : ι) (b : Bool) => if b then p else 1 - p)]
  simp

theorem wt_eq (i : ι) (p : ℝ) (ω : ι → Bool) :
    wt p ω = (if ω i then p else 1 - p) * wtc i p ω :=
  (Finset.mul_prod_erase Finset.univ (fun j => if ω j then p else 1 - p) (Finset.mem_univ i)).symm

theorem wtc_update (i : ι) (p : ℝ) (ω : ι → Bool) (b : Bool) :
    wtc i p (Function.update ω i b) = wtc i p ω := by
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-! ## The one-coordinate averaging operator -/

/-- The discrete derivative of `f` in coordinate `i`. -/
def D (i : ι) (f : (ι → Bool) → ℝ) (ω : ι → Bool) : ℝ :=
  f (Function.update ω i true) - f (Function.update ω i false)

/-- Averaging `f` over coordinate `i`. -/
def avgOne (p : ℝ) (i : ι) (f : (ι → Bool) → ℝ) (ω : ι → Bool) : ℝ :=
  p * f (Function.update ω i true) + (1 - p) * f (Function.update ω i false)

omit [Fintype ι] in
theorem avgOne_update (p : ℝ) (i : ι) (f : (ι → Bool) → ℝ) (ω : ι → Bool) (b : Bool) :
    avgOne p i f (Function.update ω i b) = avgOne p i f ω := by
  simp [avgOne, Function.update_idem]

omit [Fintype ι] in
theorem D_update (i : ι) (f : (ι → Bool) → ℝ) (ω : ι → Bool) (b : Bool) :
    D i f (Function.update ω i b) = D i f ω := by
  simp [D, Function.update_idem]

/-- The basic splitting of a cube sum along one coordinate. -/
theorem sum_split (i : ι) (g : (ι → Bool) → ℝ) :
    ∑ ω : ι → Bool, g ω
      = ∑ ω ∈ Finset.univ.filter (fun ω : ι → Bool => ω i = false),
          (g ω + g (Function.update ω i true)) := by
  rw [Finset.sum_add_distrib]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun ω : ι → Bool => ω i = false) g]
  congr 1
  refine Finset.sum_nbij' (fun ω => Function.update ω i false) (fun ω => Function.update ω i true)
    ?_ ?_ ?_ ?_ ?_
  · intro a _; simp
  · intro a _; simp
  · intro a ha; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.not_eq_false] at ha
    funext j; by_cases h : j = i
    · subst h; simp [ha]
    · simp [h]
  · intro a ha; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    funext j; by_cases h : j = i
    · subst h; simp [ha]
    · simp [h]
  · intro a ha; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.not_eq_false] at ha
    congr 1; funext j; by_cases h : j = i
    · subst h; simp [ha]
    · simp [h]

/-- The expectation, split along one coordinate. -/
theorem Exp_split (p : ℝ) (i : ι) (f : (ι → Bool) → ℝ) :
    Exp p f = ∑ ω ∈ Finset.univ.filter (fun ω : ι → Bool => ω i = false),
      wtc i p ω * ((1 - p) * f ω + p * f (Function.update ω i true)) := by
  rw [Exp, sum_split i (fun ω => wt p ω * f ω)]
  refine Finset.sum_congr rfl fun ω hω => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
  rw [wt_eq i p ω, wt_eq i p (Function.update ω i true), wtc_update, hω, Function.update_self]
  norm_num
  ring

theorem Exp_avgOne (p : ℝ) (i : ι) (f : (ι → Bool) → ℝ) :
    Exp p (avgOne p i f) = Exp p f := by
  rw [Exp_split p i (avgOne p i f), Exp_split p i f]
  refine Finset.sum_congr rfl fun ω hω => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
  have hupd : Function.update ω i false = ω := by
    funext j; by_cases h : j = i
    · subst h; simp [hω]
    · simp [h]
  rw [avgOne_update p i f ω true]
  have : avgOne p i f ω = p * f (Function.update ω i true) + (1 - p) * f ω := by
    rw [avgOne, hupd]
  rw [this]; ring

/-- **The exact one-coordinate variance decomposition.** -/
theorem Exp_sq_sub_avgOne (p : ℝ) (i : ι) (f : (ι → Bool) → ℝ) :
    Exp p (fun ω => f ω ^ 2) - Exp p (fun ω => avgOne p i f ω ^ 2)
      = p * (1 - p) * Exp p (fun ω => D i f ω ^ 2) := by
  rw [Exp_split p i (fun ω => f ω ^ 2), Exp_split p i (fun ω => avgOne p i f ω ^ 2),
    Exp_split p i (fun ω => D i f ω ^ 2), ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω hω => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
  have hupd : Function.update ω i false = ω := by
    funext j; by_cases h : j = i
    · subst h; simp [hω]
    · simp [h]
  have hA : avgOne p i f ω = p * f (Function.update ω i true) + (1 - p) * f ω := by
    rw [avgOne, hupd]
  have hD : D i f ω = f (Function.update ω i true) - f ω := by rw [D, hupd]
  rw [avgOne_update p i f ω true, D_update i f ω true, hA, hD]
  ring

theorem Exp_sq_avgOne_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i : ι) (f : (ι → Bool) → ℝ) :
    Exp p (fun ω => avgOne p i f ω ^ 2) ≤ Exp p (fun ω => f ω ^ 2) := by
  have h := Exp_sq_sub_avgOne p i f
  have hnn : 0 ≤ Exp p (fun ω => D i f ω ^ 2) :=
    Finset.sum_nonneg fun ω _ => mul_nonneg (wt_nonneg hp0 hp1 ω) (sq_nonneg _)
  have hc : 0 ≤ p * (1 - p) := mul_nonneg hp0 (by linarith)
  nlinarith [mul_nonneg hc hnn]

omit [Fintype ι] in
theorem D_avgOne_comm {i j : ι} (hij : i ≠ j) (p : ℝ) (f : (ι → Bool) → ℝ) :
    D i (avgOne p j f) = avgOne p j (D i f) := by
  funext ω
  simp only [D, avgOne]
  rw [Function.update_comm hij, Function.update_comm hij,
    Function.update_comm hij, Function.update_comm hij]
  ring

/-! ## Averaging over a list of coordinates -/

/-- Averaging over every coordinate in a list. -/
def avgL (p : ℝ) : List ι → ((ι → Bool) → ℝ) → ((ι → Bool) → ℝ)
  | [], f => f
  | i :: t, f => avgOne p i (avgL p t f)

theorem Exp_avgL (p : ℝ) (l : List ι) (f : (ι → Bool) → ℝ) : Exp p (avgL p l f) = Exp p f := by
  induction l with
  | nil => rfl
  | cons i t ih => rw [avgL, Exp_avgOne, ih]

theorem Exp_sq_avgL_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (l : List ι) (f : (ι → Bool) → ℝ) :
    Exp p (fun ω => avgL p l f ω ^ 2) ≤ Exp p (fun ω => f ω ^ 2) := by
  induction l with
  | nil => exact le_of_eq rfl
  | cons i t ih => exact le_trans (Exp_sq_avgOne_le hp0 hp1 i _) ih

omit [Fintype ι] in
theorem D_avgL_comm {i : ι} {l : List ι} (hi : i ∉ l) (p : ℝ) (f : (ι → Bool) → ℝ) :
    D i (avgL p l f) = avgL p l (D i f) := by
  induction l with
  | nil => rfl
  | cons j t ih =>
      have hij : i ≠ j := fun h => hi (by simp [h])
      have hit : i ∉ t := fun h => hi (by simp [h])
      rw [avgL, D_avgOne_comm hij, ih hit, avgL]

omit [Fintype ι] in
/-- If `ω` and `ω'` agree off `l`, then `avgL p l f` takes the same value at both. -/
theorem avgL_congr (p : ℝ) (l : List ι) (f : (ι → Bool) → ℝ) {ω ω' : ι → Bool}
    (h : ∀ j, j ∉ l → ω j = ω' j) : avgL p l f ω = avgL p l f ω' := by
  induction l generalizing ω ω' with
  | nil =>
      have : ω = ω' := funext fun j => h j (by simp)
      rw [this]
  | cons i t ih =>
      have hstep : ∀ b : Bool, avgL p t f (Function.update ω i b)
          = avgL p t f (Function.update ω' i b) := by
        intro b
        refine ih ?_
        intro j hj
        by_cases hji : j = i
        · subst hji; simp
        · rw [Function.update_of_ne hji, Function.update_of_ne hji]
          exact h j (by simp [hji, hj])
      simp only [avgL, avgOne, hstep]

/-! ## The Efron–Stein inequality -/

theorem Exp_const (p : ℝ) (c : ℝ) : Exp p (fun _ : ι → Bool => c) = c := by
  rw [Exp, ← Finset.sum_mul, sum_wt, one_mul]

/-- Telescoping the one-coordinate decomposition along a duplicate-free list. -/
theorem variance_le_of_list {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (l : List ι) (hl : l.Nodup)
    (f : (ι → Bool) → ℝ) :
    Exp p (fun ω => f ω ^ 2) - Exp p (fun ω => avgL p l f ω ^ 2)
      ≤ (l.map (fun i => p * (1 - p) * Exp p (fun ω => D i f ω ^ 2))).sum := by
  induction l with
  | nil => simp [avgL]
  | cons i t ih =>
      have hit : i ∉ t := (List.nodup_cons.mp hl).1
      have ht : t.Nodup := (List.nodup_cons.mp hl).2
      have h1 := ih ht
      have h2 : Exp p (fun ω => avgL p t f ω ^ 2)
          - Exp p (fun ω => avgOne p i (avgL p t f) ω ^ 2)
          = p * (1 - p) * Exp p (fun ω => D i (avgL p t f) ω ^ 2) :=
        Exp_sq_sub_avgOne p i (avgL p t f)
      have h3 : Exp p (fun ω => D i (avgL p t f) ω ^ 2)
          ≤ Exp p (fun ω => D i f ω ^ 2) := by
        rw [D_avgL_comm hit p f]
        exact Exp_sq_avgL_le hp0 hp1 t (D i f)
      have hcoef : 0 ≤ p * (1 - p) := mul_nonneg hp0 (by linarith)
      have h4 : p * (1 - p) * Exp p (fun ω => D i (avgL p t f) ω ^ 2)
          ≤ p * (1 - p) * Exp p (fun ω => D i f ω ^ 2) :=
        mul_le_mul_of_nonneg_left h3 hcoef
      simp only [avgL, List.map_cons, List.sum_cons]
      linarith only [h1, h2, h4]

/-- **Efron–Stein on the Bernoulli cube.**  The variance of `f` is at most `p(1−p)` times the sum
over coordinates of the mean square discrete derivative. -/
theorem variance_le_sum_sq_diff {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : (ι → Bool) → ℝ) :
    Exp p (fun ω => f ω ^ 2) - (Exp p f) ^ 2
      ≤ ∑ i : ι, p * (1 - p) * Exp p (fun ω => D i f ω ^ 2) := by
  classical
  set l : List ι := Finset.univ.toList with hldef
  have hl : l.Nodup := Finset.nodup_toList _
  have hmem : ∀ i : ι, i ∈ l := fun i => Finset.mem_toList.mpr (Finset.mem_univ i)
  -- `avgL p l f` is constant, equal to `Exp p f`
  have hconst : ∀ ω ω' : ι → Bool, avgL p l f ω = avgL p l f ω' := by
    intro ω ω'
    exact avgL_congr p l f (fun j hj => absurd (hmem j) hj)
  have hval : ∀ ω : ι → Bool, avgL p l f ω = Exp p f := by
    intro ω
    have h1 : Exp p (avgL p l f) = Exp p f := Exp_avgL p l f
    have h2 : Exp p (avgL p l f) = avgL p l f ω := by
      have : (avgL p l f) = fun _ => avgL p l f ω := funext fun ω' => hconst ω' ω
      rw [this, Exp_const]
    linarith only [h1, h2]
  have hsq : Exp p (fun ω => avgL p l f ω ^ 2) = (Exp p f) ^ 2 := by
    have : (fun ω : ι → Bool => avgL p l f ω ^ 2) = fun _ => (Exp p f) ^ 2 :=
      funext fun ω => by rw [hval ω]
    rw [this, Exp_const]
  have hmain := variance_le_of_list hp0 hp1 l hl f
  rw [hsq] at hmain
  refine le_trans hmain (le_of_eq ?_)
  rw [hldef]
  exact Finset.sum_map_toList Finset.univ _

/-! ## Linearity, products and the variance identity -/

theorem Exp_prod (p : ℝ) (g : ι → Bool → ℝ) :
    Exp p (fun ω => ∏ i, g i (ω i)) = ∏ i, (p * g i true + (1 - p) * g i false) := by
  rw [Exp]
  have h1 : ∀ ω : ι → Bool, wt p ω * ∏ i, g i (ω i)
      = ∏ i, ((if ω i then p else 1 - p) * g i (ω i)) := by
    intro ω; rw [wt, ← Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl (fun ω _ => h1 ω)]
  rw [← Fintype.prod_sum (fun (i : ι) (b : Bool) => (if b then p else 1 - p) * g i b)]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp

/-- The centred second moment of `f` is `Exp f² − (Exp f)²`. -/
theorem Exp_centred_sq (p : ℝ) (f : (ι → Bool) → ℝ) :
    Exp p (fun ω => (f ω - Exp p f) ^ 2) = Exp p (fun ω => f ω ^ 2) - (Exp p f) ^ 2 := by
  set c := Exp p f with hc
  have hexp : ∀ ω : ι → Bool, wt p ω * (f ω - c) ^ 2
      = wt p ω * f ω ^ 2 - 2 * c * (wt p ω * f ω) + c ^ 2 * wt p ω := by
    intro ω; ring
  rw [Exp, Finset.sum_congr rfl (fun ω _ => hexp ω), Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [sum_wt]
  change Exp p (fun ω => f ω ^ 2) - 2 * c * Exp p f + c ^ 2 * 1 = _
  rw [← hc]; ring

/-- **Efron–Stein, in centred form.** -/
theorem centred_sq_le_sum_sq_diff {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : (ι → Bool) → ℝ) :
    Exp p (fun ω => (f ω - Exp p f) ^ 2)
      ≤ ∑ i : ι, p * (1 - p) * Exp p (fun ω => D i f ω ^ 2) := by
  rw [Exp_centred_sq]
  exact variance_le_sum_sq_diff hp0 hp1 f

theorem Exp_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {f g : (ι → Bool) → ℝ}
    (h : ∀ ω, f ω ≤ g ω) : Exp p f ≤ Exp p g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (wt_nonneg hp0 hp1 ω)

theorem Exp_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {f : (ι → Bool) → ℝ}
    (h : ∀ ω, 0 ≤ f ω) : 0 ≤ Exp p f :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (wt_nonneg hp0 hp1 ω) (h ω)

theorem Exp_add (p : ℝ) (f g : (ι → Bool) → ℝ) :
    Exp p (fun ω => f ω + g ω) = Exp p f + Exp p g := by
  simp only [Exp, mul_add]
  exact Finset.sum_add_distrib

theorem Exp_smul (p c : ℝ) (f : (ι → Bool) → ℝ) :
    Exp p (fun ω => c * f ω) = c * Exp p f := by
  simp only [Exp, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ω _ => by ring

theorem Exp_finset_sum {α : Type*} (p : ℝ) (s : Finset α) (g : α → (ι → Bool) → ℝ) :
    Exp p (fun ω => ∑ a ∈ s, g a ω) = ∑ a ∈ s, Exp p (g a) := by
  classical
  induction s using Finset.induction with
  | empty => simp [Exp]
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [← ih, ← Exp_add]

/-! ## Second moments of weighted sums of coordinates -/

/-- The pair correlation of two coordinate indicators: `p` on the diagonal, `p²` off it. -/
theorem Exp_coord_mul {p : ℝ} (f g : ι) :
    Exp p (fun ω : ι → Bool =>
        (if ω f then (1 : ℝ) else 0) * (if ω g then (1 : ℝ) else 0))
      = if f = g then p else p ^ 2 := by
  classical
  set h : ι → Bool → ℝ := fun i b =>
    (if i = f then (if b then (1 : ℝ) else 0) else 1) *
      (if i = g then (if b then (1 : ℝ) else 0) else 1) with hh
  have key : ∀ ω : ι → Bool, (∏ i, h i (ω i))
      = (if ω f then (1 : ℝ) else 0) * (if ω g then (1 : ℝ) else 0) := by
    intro ω
    rw [hh]
    simp only
    rw [Finset.prod_mul_distrib,
      Finset.prod_ite_eq' Finset.univ f (fun i => (if ω i then (1 : ℝ) else 0)),
      Finset.prod_ite_eq' Finset.univ g (fun i => (if ω i then (1 : ℝ) else 0))]
    simp
  have heq : Exp p (fun ω : ι → Bool =>
        (if ω f then (1 : ℝ) else 0) * (if ω g then (1 : ℝ) else 0))
      = Exp p (fun ω => ∏ i, h i (ω i)) := by
    unfold Exp
    exact Finset.sum_congr rfl (fun ω _ => by simp only; rw [key ω])
  rw [heq, Exp_prod]
  by_cases hfg : f = g
  · subst hfg
    rw [ite_eq_left rfl]
    have hi2 : ∀ i : ι, p * h i true + (1 - p) * h i false = if i = f then p else 1 := by
      intro i; rw [hh]; by_cases hi : i = f <;> simp [hi]
    rw [Finset.prod_congr rfl (fun i _ => hi2 i), Finset.prod_ite_eq' Finset.univ f (fun _ => p)]
    simp
  · rw [ite_eq_right hfg]
    have hi2 : ∀ i : ι, p * h i true + (1 - p) * h i false
        = (if i = f then p else 1) * (if i = g then p else 1) := by
      intro i; rw [hh]
      by_cases hi : i = f <;> by_cases hj : i = g <;> simp_all
    rw [Finset.prod_congr rfl (fun i _ => hi2 i), Finset.prod_mul_distrib,
      Finset.prod_ite_eq' Finset.univ f (fun _ => p),
      Finset.prod_ite_eq' Finset.univ g (fun _ => p)]
    simp [sq]

/-- The second moment of a nonnegatively weighted sum of coordinate indicators. -/
theorem Exp_weighted_sum_sq_le {p : ℝ} (M : Finset ι) (w : ι → ℝ) :
    Exp p (fun ω : ι → Bool => (∑ f ∈ M, if ω f then w f else 0) ^ 2)
      ≤ p * (∑ f ∈ M, w f ^ 2) + p ^ 2 * (∑ f ∈ M, w f) ^ 2 := by
  classical
  have hexp : ∀ ω : ι → Bool, (∑ f ∈ M, if ω f then w f else 0) ^ 2
      = ∑ f ∈ M, ∑ g ∈ M, (w f * w g) *
          ((if ω f then (1 : ℝ) else 0) * (if ω g then (1 : ℝ) else 0)) := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun g _ => ?_
    by_cases h1 : ω f = true <;> by_cases h2 : ω g = true <;> simp [h1, h2]
  have h1 : Exp p (fun ω : ι → Bool => (∑ f ∈ M, if ω f then w f else 0) ^ 2)
      = ∑ f ∈ M, ∑ g ∈ M, (w f * w g) * (if f = g then p else p ^ 2) := by
    rw [show (fun ω : ι → Bool => (∑ f ∈ M, if ω f then w f else 0) ^ 2)
        = (fun ω => ∑ f ∈ M, ∑ g ∈ M, (w f * w g) *
          ((if ω f then (1 : ℝ) else 0) * (if ω g then (1 : ℝ) else 0))) from funext hexp]
    rw [Exp_finset_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Exp_finset_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Exp_smul, Exp_coord_mul]
  rw [h1]
  have h2 : ∀ f ∈ M, ∑ g ∈ M, (w f * w g) * (if f = g then p else p ^ 2)
      ≤ ∑ g ∈ M, ((w f * w g) * p ^ 2 + (if f = g then w f * w g * p else 0)) := by
    intro f _
    refine Finset.sum_le_sum fun g _ => ?_
    by_cases hfg : f = g
    · subst hfg
      rw [ite_eq_left rfl, ite_eq_left rfl]
      nlinarith only [sq_nonneg (w f * p)]
    · simp [hfg]
  have h3 : ∀ f ∈ M, ∑ g ∈ M, ((w f * w g) * p ^ 2 + (if f = g then w f * w g * p else 0))
      = w f * (p ^ 2 * (∑ g ∈ M, w g)) + w f ^ 2 * p := by
    intro f hf
    rw [Finset.sum_add_distrib]
    congr 1
    · simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun g _ => by ring
    · rw [Finset.sum_ite_eq (b := fun g => w f * w g * p), ite_eq_left hf]
      ring
  calc ∑ f ∈ M, ∑ g ∈ M, (w f * w g) * (if f = g then p else p ^ 2)
      ≤ ∑ f ∈ M, ∑ g ∈ M, ((w f * w g) * p ^ 2 + (if f = g then w f * w g * p else 0)) :=
        Finset.sum_le_sum h2
    _ = ∑ f ∈ M, (w f * (p ^ 2 * (∑ g ∈ M, w g)) + w f ^ 2 * p) := Finset.sum_congr rfl h3
    _ = p * (∑ f ∈ M, w f ^ 2) + p ^ 2 * (∑ f ∈ M, w f) ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
        ring

end LeanPool.AsymptoticTrianglePacking.Internal.Cube

end





/-!
# LeanPool.AsymptoticTrianglePacking.Internal — stability of the covered set under a single-edge
flip

The one remaining analytic input of the tight-band nibble (see
`LeanPool.AsymptoticTrianglePacking.Internal.Tight.SharpRound`) is the
SHARP per-vertex safe-degree variance bound

  `Var(safeDeg(v)) ≤ C(r)·(γΔ + κγΔ)`,

i.e. a bound with NO term of the shape `c·γ^a·Δ²`.  The Bonferroni route of
`LeanPool.AsymptoticTrianglePacking.Internal.Tight.SafeDegreeVariance` leaves a residue `Θ(γ³Δ²)`,
which is a constant factor (depending
on the target `β`) too large to iterate.

This file provides the key COMBINATORIAL input of the bounded-differences (Efron–Stein) route to
that bound: the round's covered set is *locally* stable — flipping the retention status of a single
edge `e` only moves vertices that lie on `e` itself or on a retained edge meeting `e`.

Concretely, with

  `flipInfluence R e = insert e (R.filter (fun f => ¬ Disjoint f e))`,

`LeanPool.AsymptoticTrianglePacking.Internal.mem_roundMatching_insert_iff_erase` says that every
edge outside `flipInfluence R e` belongs
to `roundMatching (insert e R)` exactly when it belongs to `roundMatching (R.erase e)`, and hence
`LeanPool.AsymptoticTrianglePacking.Internal.covered_insert_sdiff_subset` /
`LeanPool.AsymptoticTrianglePacking.Internal.covered_erase_sdiff_subset` bound the symmetric
difference of the two covered sets by `⋃ (flipInfluence R e)`.  For an `r`-uniform hypergraph this
has at most `r·(1 + #{f ∈ R : f meets e})` vertices
(`LeanPool.AsymptoticTrianglePacking.Internal.card_biUnion_flipInfluence_le`), so the safe degree at
`v` moves by at most
`∑_{u} codeg(v,u)` over that set
(`LeanPool.AsymptoticTrianglePacking.Internal.abs_safeDegree_sub_le_codegree_sum`).

Summing `p·𝔼[(ΔsafeDeg)²]` over the edges `e` and using `∑_{u ≠ v} codeg(v,u)² ≤ κ(r−1)deg(v)`
gives exactly `O_r(γΔ(1 + κ))`, the sharp bound — the arithmetic is recorded in the header of
`LeanPool.AsymptoticTrianglePacking.Internal.Tight.SharpRound`.

placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

public section

open Finset Hypergraph

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V]

/-! ## The influence set of a single edge -/

/-- The edges whose membership in the round matching can be affected by flipping the retention
status of `e`: the edge `e` itself, and the retained edges meeting `e`. -/
def flipInfluence (R : Finset (Finset V)) (e : Finset V) : Finset (Finset V) :=
  insert e (R.filter (fun f => ¬ Disjoint f e))

theorem notMem_flipInfluence_ne {R : Finset (Finset V)} {e f : Finset V}
    (hf : f ∉ flipInfluence R e) : f ≠ e := by
  intro h; exact hf (by simp [flipInfluence, h])

theorem notMem_flipInfluence_disjoint {R : Finset (Finset V)} {e f : Finset V}
    (hf : f ∉ flipInfluence R e) (hfR : f ∈ R) : Disjoint f e := by
  by_contra hd
  exact hf (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hfR, hd⟩))

/-- **Local stability of the round matching.**  An edge outside the influence set of `e` is in the
round matching of `insert e R` exactly when it is in the round matching of `R.erase e`. -/
theorem mem_roundMatching_insert_iff_erase {R : Finset (Finset V)} {e f : Finset V}
    (hf : f ∉ flipInfluence R e) :
    f ∈ roundMatching (insert e R) ↔ f ∈ roundMatching (R.erase e) := by
  have hfe : f ≠ e := notMem_flipInfluence_ne hf
  constructor
  · intro h
    rw [roundMatching, Finset.mem_filter] at h ⊢
    obtain ⟨hmem, hdisj⟩ := h
    have hfR : f ∈ R := (Finset.mem_insert.mp hmem).resolve_left hfe
    refine ⟨Finset.mem_erase.mpr ⟨hfe, hfR⟩, ?_⟩
    intro g hg hgf
    exact hdisj g (Finset.mem_insert_of_mem (Finset.mem_of_mem_erase hg)) hgf
  · intro h
    rw [roundMatching, Finset.mem_filter] at h ⊢
    obtain ⟨hmem, hdisj⟩ := h
    have hfR : f ∈ R := Finset.mem_of_mem_erase hmem
    refine ⟨Finset.mem_insert_of_mem hfR, ?_⟩
    intro g hg hgf
    by_cases hge : g = e
    · subst hge; exact notMem_flipInfluence_disjoint hf hfR
    · exact hdisj g (Finset.mem_erase.mpr ⟨hge, (Finset.mem_insert.mp hg).resolve_left hge⟩) hgf

/-! ## Stability of the covered set -/

theorem covered_insert_sdiff_subset (R : Finset (Finset V)) (e : Finset V) :
    covered (insert e R) \ covered (R.erase e) ⊆ (flipInfluence R e).biUnion id := by
  intro u hu
  rw [Finset.mem_sdiff] at hu
  obtain ⟨f, hfM, huf⟩ := Finset.mem_biUnion.mp hu.1
  by_cases hfl : f ∈ flipInfluence R e
  · exact Finset.mem_biUnion.mpr ⟨f, hfl, huf⟩
  · exact absurd (Finset.mem_biUnion.mpr
      ⟨f, (mem_roundMatching_insert_iff_erase hfl).mp hfM, huf⟩) hu.2

theorem covered_erase_sdiff_subset (R : Finset (Finset V)) (e : Finset V) :
    covered (R.erase e) \ covered (insert e R) ⊆ (flipInfluence R e).biUnion id := by
  intro u hu
  rw [Finset.mem_sdiff] at hu
  obtain ⟨f, hfM, huf⟩ := Finset.mem_biUnion.mp hu.1
  by_cases hfl : f ∈ flipInfluence R e
  · exact Finset.mem_biUnion.mpr ⟨f, hfl, huf⟩
  · exact absurd (Finset.mem_biUnion.mpr
      ⟨f, (mem_roundMatching_insert_iff_erase hfl).mpr hfM, huf⟩) hu.2

/-- **The flip only moves few vertices.**  For an `r`-uniform hypergraph the influence set of `e`
spans at most `r·(1 + #{f ∈ R : f meets e})` vertices. -/
theorem card_biUnion_flipInfluence_le {H : Finset (Finset V)} {r : ℕ} (hunif : IsUniform H r)
    {R : Finset (Finset V)} (hRH : R ⊆ H) {e : Finset V} (he : e ∈ H) :
    ((flipInfluence R e).biUnion id).card
      ≤ r * (1 + (R.filter (fun f => ¬ Disjoint f e)).card) := by
  classical
  refine le_trans (Finset.card_biUnion_le) ?_
  have hcard : ∀ f ∈ flipInfluence R e, (id f).card = r := by
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf'
    · exact hunif _ he
    · exact hunif _ (hRH (Finset.mem_filter.mp hf').1)
  rw [Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul, mul_comm]
  have hle : (flipInfluence R e).card ≤ 1 + (R.filter (fun f => ¬ Disjoint f e)).card := by
    simpa [flipInfluence, Nat.add_comm] using
      Finset.card_insert_le e (R.filter (fun f => ¬ Disjoint f e))
  exact Nat.mul_le_mul_left r hle

/-! ## The safe degree moves by at most a codegree sum -/

/-- If two covered sets differ only inside `D`, the safe degrees at `v` differ by at most the number
of edges at `v` meeting `D` away from `v`. -/
theorem abs_safeDegree_sub_le_card_meeting {H : Finset (Finset V)} {C C' D : Finset V} {v : V}
    (hCC' : C \ C' ⊆ D) (hC'C : C' \ C ⊆ D) :
    ((safeDegree H C v : ℤ) - (safeDegree H C' v : ℤ)).natAbs
      ≤ (H.filter (fun e => v ∈ e ∧ ¬ Disjoint (e.erase v) D)).card := by
  classical
  set T := H.filter (fun e => v ∈ e ∧ ¬ Disjoint (e.erase v) D) with hT
  have key : ∀ (X Y : Finset V), X \ Y ⊆ D →
      (H.filter (fun e => v ∈ e ∧ Disjoint (e.erase v) Y)).card
        ≤ (H.filter (fun e => v ∈ e ∧ Disjoint (e.erase v) X)).card + T.card := by
    intro X Y hXY
    have hsub : H.filter (fun e => v ∈ e ∧ Disjoint (e.erase v) Y)
        ⊆ H.filter (fun e => v ∈ e ∧ Disjoint (e.erase v) X) ∪ T := by
      intro e hmem'
      rw [Finset.mem_filter] at hmem'
      obtain ⟨heH, hve, hdY⟩ := hmem'
      by_cases hdX : Disjoint (e.erase v) X
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨heH, hve, hdX⟩)
      · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨heH, hve, ?_⟩)
        rw [Finset.not_disjoint_iff] at hdX ⊢
        obtain ⟨u, hu1, hu2⟩ := hdX
        refine ⟨u, hu1, hXY (Finset.mem_sdiff.mpr ⟨hu2, ?_⟩)⟩
        exact fun hY => (Finset.disjoint_left.mp hdY hu1) hY
    exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have h1 := key C C' hCC'
  have h2 := key C' C hC'C
  simp only [safeDegree]
  omega

/-- The number of edges at `v` meeting a set `D` away from `v` is at most `∑_{u ∈ D} codeg(v,u)`. -/
theorem card_meeting_le_codegree_sum {H : Finset (Finset V)} {D : Finset V} {v : V} :
    (H.filter (fun e => v ∈ e ∧ ¬ Disjoint (e.erase v) D)).card
      ≤ ∑ u ∈ D.erase v, codegree H v u := by
  classical
  have hsub : H.filter (fun e => v ∈ e ∧ ¬ Disjoint (e.erase v) D)
      ⊆ (D.erase v).biUnion (fun u => H.filter (fun e => v ∈ e ∧ u ∈ e)) := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨heH, hve, hd⟩ := he
    rw [Finset.not_disjoint_iff] at hd
    obtain ⟨u, hu1, hu2⟩ := hd
    exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hu1, hu2⟩,
      Finset.mem_filter.mpr ⟨heH, hve, Finset.mem_of_mem_erase hu1⟩⟩
  refine le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_biUnion_le) (le_of_eq ?_))
  exact Finset.sum_congr rfl fun u _ => rfl

/-- **The bounded-differences estimate for the safe degree.**  If the covered sets `C`, `C'` differ
only inside `D`, then the safe degrees at `v` differ by at most `∑_{u ∈ D \ {v}} codeg(v,u)`. -/
theorem abs_safeDegree_sub_le_codegree_sum {H : Finset (Finset V)} {C C' D : Finset V}
    {v : V} (hCC' : C \ C' ⊆ D) (hC'C : C' \ C ⊆ D) :
    ((safeDegree H C v : ℤ) - (safeDegree H C' v : ℤ)).natAbs
      ≤ ∑ u ∈ D.erase v, codegree H v u :=
  le_trans (abs_safeDegree_sub_le_card_meeting hCC' hC'C) card_meeting_le_codegree_sum

/-- **The safe degree is stable under a single-edge flip.**  Flipping the retention status of `e`
changes the safe degree at `v` by at most the codegree sum over the vertices spanned by the
influence set of `e`. -/
theorem abs_safeDegree_flip_le (H : Finset (Finset V)) (R : Finset (Finset V))
    (e : Finset V) (v : V) :
    ((safeDegree H (covered (insert e R)) v : ℤ)
        - (safeDegree H (covered (R.erase e)) v : ℤ)).natAbs
      ≤ ∑ u ∈ (((flipInfluence R e).biUnion id).erase v), codegree H v u :=
  abs_safeDegree_sub_le_codegree_sum (covered_insert_sdiff_subset R e)
    (covered_erase_sdiff_subset R e)

/-- **The squared codegree sum.**  With all codegrees at `v` bounded by `κ`,
`∑_{u ≠ v} codeg(v,u)² ≤ κ·(r−1)·deg(v)` — the weight that drives the Efron–Stein estimate. -/
theorem sum_sq_codegree_le [Fintype V] {H : Finset (Finset V)} {r : ℕ} (hr : IsUniform H r)
    {κ : ℝ} (v : V) (hκ : ∀ u : V, u ≠ v → (codegree H v u : ℝ) ≤ κ) :
    ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ) ^ 2
      ≤ κ * (((r - 1) * degree H v : ℕ) : ℝ) := by
  classical
  have hstep : ∀ u ∈ (Finset.univ : Finset V).erase v,
      ((codegree H v u : ℝ)) ^ 2 ≤ κ * (codegree H v u : ℝ) := by
    intro u hu
    have hne : u ≠ v := Finset.ne_of_mem_erase hu
    have h0 : (0 : ℝ) ≤ (codegree H v u : ℝ) := Nat.cast_nonneg _
    nlinarith only [hκ u hne]
  calc ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ) ^ 2
      ≤ ∑ u ∈ (Finset.univ : Finset V).erase v, κ * (codegree H v u : ℝ) :=
        Finset.sum_le_sum hstep
    _ = κ * ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ) := by
        rw [Finset.mul_sum]
    _ = κ * (((r - 1) * degree H v : ℕ) : ℝ) := by
        rw [← Nat.cast_sum, sum_codegree_erase_eq hr v]

end LeanPool.AsymptoticTrianglePacking.Internal

end


/-!
# LeanPool.AsymptoticTrianglePacking.Internal — the SHARP per-vertex safe-degree variance

This is the one analytic input the iterable nibble round was missing.  The Bonferroni route of
`LeanPool.AsymptoticTrianglePacking.Internal.Tight.SafeDegreeVariance` bounds the variance of
`safeDeg(v)` by
`Δ²((r−1)²ε₂ + 2(r−1)³q_hi(q_hi²+ε₂)) + q_hi κ(r−1)Δ ≈ 2γ³Δ²`; the `Θ(γ³Δ²)` residue is a constant
factor too large to iterate.  Here we prove the sharp bound

  `Var(safeDeg(v)) ≤ 2p·r²κΔ²·(1 + prΔ + (prΔ)²)`,

i.e. `≈ 2rγκΔ` at the nibble retention `p = γ/(rΔ)` — with NO `Δ²` term.

The route is bounded differences (Efron–Stein).  Everything happens on the explicit Bernoulli cube
`Finset V → Bool` of `LeanPool.AsymptoticTrianglePacking.Internal.Tight.CubeVariance`, where the
Efron–Stein inequality
`LeanPool.AsymptoticTrianglePacking.Internal.Cube.centred_sq_le_sum_sq_diff` is available. The
combinatorial input is
`LeanPool.AsymptoticTrianglePacking.Internal.Tight.FlipStability`: flipping the retention of a
single edge `k` moves the covered set only
inside `k ∪ ⋃ {f ∈ R : f meets k}`, so the safe degree at `v` moves by at most

  `edgeWeight k + ∑_{f ∈ R, f meets k} edgeWeight f`,  `edgeWeight f = ∑_{u ∈ f∖v} codeg(v,u)`.

Squaring, taking expectations and summing over `k` produces exactly the three terms above.
-/

public section

open Finset Hypergraph LeanPool.AsymptoticTrianglePacking.Internal.Cube

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The cube picture of a round -/

/-- The retained set at a configuration of the cube. -/
def retSet (H : Finset (Finset V)) (ω : Finset V → Bool) : Finset (Finset V) :=
  H.filter (fun e => ω e = true)

/-- The safe degree at `v` as a function on the cube. -/
def safeDegCube (H : Finset (Finset V)) (v : V) (ω : Finset V → Bool) : ℝ :=
  (safeDegree H (covered (retSet H ω)) v : ℝ)

/-- The codegree weight of an edge as seen from `v`: `∑_{u ∈ f∖v} codeg(v,u)`. -/
def edgeWeight (H : Finset (Finset V)) (v : V) (f : Finset V) : ℝ :=
  ∑ u ∈ f.erase v, (codegree H v u : ℝ)

/-- The edges of `H` meeting `k`. -/
def meets (H : Finset (Finset V)) (k : Finset V) : Finset (Finset V) :=
  H.filter (fun f => ¬ Disjoint f k)

/-- The random part of the flip bound: the total codegree weight of the retained edges meeting
`k`. -/
def flipWeight (H : Finset (Finset V)) (v : V) (k : Finset V) (ω : Finset V → Bool) : ℝ :=
  ∑ f ∈ meets H k, (if ω f then edgeWeight H v f else 0)

/-! ## Elementary bounds on the codegree weight -/

omit [Fintype V] in
theorem edgeWeight_nonneg (H : Finset (Finset V)) (v : V) (f : Finset V) :
    0 ≤ edgeWeight H v f :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

omit [Fintype V] in
theorem edgeWeight_le_of_mem {H : Finset (Finset V)} {r κ : ℕ} (hr : IsUniform H r)
    (hκ : ∀ y z : V, y ≠ z → codegree H y z ≤ κ) (v : V) {f : Finset V} (hf : f ∈ H) :
    edgeWeight H v f ≤ (r : ℝ) * (κ : ℝ) := by
  have hcard : (f.erase v).card ≤ r := by
    have := hr f hf
    calc (f.erase v).card ≤ f.card := Finset.card_erase_le
      _ = r := this
  calc edgeWeight H v f ≤ ∑ _u ∈ f.erase v, (κ : ℝ) := by
        refine Finset.sum_le_sum fun u hu => ?_
        have hne : v ≠ u := (Finset.ne_of_mem_erase hu).symm
        exact_mod_cast hκ v u hne
    _ = ((f.erase v).card : ℝ) * (κ : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (r : ℝ) * (κ : ℝ) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg _)

/-- Double counting: `∑_{f ∈ H} edgeWeight f = ∑_{u ≠ v} codeg(v,u)·deg(u)`. -/
theorem sum_edgeWeight_eq (H : Finset (Finset V)) (v : V) :
    ∑ f ∈ H, edgeWeight H v f
      = ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ) * (degree H u : ℝ) := by
  classical
  have hstep : ∀ f ∈ H, edgeWeight H v f
      = ∑ u ∈ (Finset.univ : Finset V).erase v, (if u ∈ f then (codegree H v u : ℝ) else 0) := by
    intro f _
    rw [edgeWeight, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext u
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ]
    tauto
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, degree]
  ring

omit [Fintype V] in
theorem sum_edgeWeight_le [Finite V] {H : Finset (Finset V)} {r Δ : ℕ} (hr : IsUniform H r)
    (hΔ : ∀ y : V, degree H y ≤ Δ) (v : V) :
    ∑ f ∈ H, edgeWeight H v f ≤ (r : ℝ) * (Δ : ℝ) ^ 2 := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  rw [sum_edgeWeight_eq]
  have h1 : ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ) * (degree H u : ℝ)
      ≤ ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ) * (Δ : ℝ) := by
    refine Finset.sum_le_sum fun u _ => ?_
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hΔ u) (Nat.cast_nonneg _)
  have h2 : ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ) * (Δ : ℝ)
      = ((((r - 1) * degree H v : ℕ)) : ℝ) * (Δ : ℝ) := by
    rw [← Finset.sum_mul, ← Nat.cast_sum, sum_codegree_erase_eq hr v]
  have h3 : ((((r - 1) * degree H v : ℕ)) : ℝ) ≤ (r : ℝ) * (Δ : ℝ) := by
    have hd : degree H v ≤ Δ := hΔ v
    have : (r - 1) * degree H v ≤ r * Δ := Nat.mul_le_mul (Nat.sub_le r 1) hd
    exact_mod_cast this
  have h4 : ((((r - 1) * degree H v : ℕ)) : ℝ) * (Δ : ℝ) ≤ ((r : ℝ) * (Δ : ℝ)) * (Δ : ℝ) :=
    mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg _)
  calc ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ) * (degree H u : ℝ)
      ≤ ((r : ℝ) * (Δ : ℝ)) * (Δ : ℝ) := by rw [h2] at h1; linarith only [h1, h4]
    _ = (r : ℝ) * (Δ : ℝ) ^ 2 := by ring

omit [Fintype V] in
theorem sum_edgeWeight_sq_le [Finite V] {H : Finset (Finset V)} {r Δ κ : ℕ} (hr : IsUniform H r)
    (hΔ : ∀ y : V, degree H y ≤ Δ) (hκ : ∀ y z : V, y ≠ z → codegree H y z ≤ κ) (v : V) :
    ∑ f ∈ H, edgeWeight H v f ^ 2 ≤ (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 := by
  let _ : Fintype V := Fintype.ofFinite V
  have hstep : ∀ f ∈ H, edgeWeight H v f ^ 2 ≤ ((r : ℝ) * (κ : ℝ)) * edgeWeight H v f := by
    intro f hf
    have h1 := edgeWeight_le_of_mem hr hκ v hf
    have h2 := edgeWeight_nonneg H v f
    nlinarith only [h1, h2]
  calc ∑ f ∈ H, edgeWeight H v f ^ 2 ≤ ∑ f ∈ H, ((r : ℝ) * (κ : ℝ)) * edgeWeight H v f :=
        Finset.sum_le_sum hstep
    _ = ((r : ℝ) * (κ : ℝ)) * ∑ f ∈ H, edgeWeight H v f := by rw [Finset.mul_sum]
    _ ≤ ((r : ℝ) * (κ : ℝ)) * ((r : ℝ) * (Δ : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_edgeWeight_le hr hΔ v) (by positivity)
    _ = (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 := by ring

omit [Fintype V] in
/-- At most `rΔ` edges meet a given edge. -/
theorem card_meets_le {H : Finset (Finset V)} {r Δ : ℕ} (hr : IsUniform H r)
    (hΔ : ∀ y : V, degree H y ≤ Δ) {k : Finset V} (hk : k ∈ H) :
    ((meets H k).card : ℝ) ≤ (r : ℝ) * (Δ : ℝ) := by
  classical
  have hsub : meets H k ⊆ k.biUnion (fun x => H.filter (fun f => x ∈ f)) := by
    intro f hf
    rw [meets, Finset.mem_filter] at hf
    obtain ⟨x, hxf, hxk⟩ := Finset.not_disjoint_iff.mp hf.2
    exact Finset.mem_biUnion.mpr ⟨x, hxk, Finset.mem_filter.mpr ⟨hf.1, hxf⟩⟩
  have hcard : (meets H k).card ≤ r * Δ := by
    calc (meets H k).card ≤ (k.biUnion (fun x => H.filter (fun f => x ∈ f))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ x ∈ k, (H.filter (fun f => x ∈ f)).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ k, Δ := Finset.sum_le_sum (fun x _ => hΔ x)
      _ = k.card * Δ := by rw [Finset.sum_const, smul_eq_mul]
      _ = r * Δ := by rw [hr k hk]
  exact_mod_cast hcard

omit [Fintype V] in
theorem meets_comm (H : Finset (Finset V)) (f : Finset V) :
    meets H f = H.filter (fun k => ¬ Disjoint f k) := by
  classical
  refine Finset.filter_congr fun k _ => ?_
  constructor
  · intro h hd; exact h (Disjoint.symm hd)
  · intro h hd; exact h (Disjoint.symm hd)

/-- A sum over a `biUnion` is at most the sum of the sums, for a nonnegative summand. -/
theorem sum_biUnion_le_of_nonneg {α β : Type*} [DecidableEq α] (B : Finset β)
    (t : β → Finset α) (g : α → ℝ) (hg : ∀ a, 0 ≤ g a) :
    ∑ u ∈ B.biUnion t, g u ≤ ∑ f ∈ B, ∑ u ∈ t f, g u := by
  classical
  induction B using Finset.induction with
  | empty => simp
  | insert b s hb ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hb]
      have h1 : ∑ u ∈ t b ∪ s.biUnion t, g u ≤ ∑ u ∈ t b, g u + ∑ u ∈ s.biUnion t, g u := by
        have hi := Finset.sum_union_inter (s₁ := t b) (s₂ := s.biUnion t) (f := g)
        have h0 : 0 ≤ ∑ u ∈ t b ∩ s.biUnion t, g u := Finset.sum_nonneg fun a _ => hg a
        linarith only [hi, h0]
      linarith only [ih, h1]

omit [Fintype V] in
/-- Double counting the incidences `k ∈ H`, `f ∈ meets H k`. -/
theorem sum_meets_swap (H : Finset (Finset V)) (g : Finset V → ℝ) :
    ∑ k ∈ H, ∑ f ∈ meets H k, g f = ∑ f ∈ H, ((meets H f).card : ℝ) * g f := by
  classical
  have hL : ∀ k ∈ H, ∑ f ∈ meets H k, g f
      = ∑ f ∈ H, (if ¬ Disjoint f k then g f else 0) := by
    intro k _
    rw [meets, Finset.sum_filter]
  rw [Finset.sum_congr rfl hL, Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  have : ∑ k ∈ H, (if ¬ Disjoint f k then g f else 0)
      = ∑ _k ∈ H.filter (fun k => ¬ Disjoint f k), g f := by rw [Finset.sum_filter]
  rw [this, Finset.sum_const, nsmul_eq_mul, meets_comm]

/-! ## The flip bound -/

omit [Fintype V] in
theorem retSet_update_true {H : Finset (Finset V)} {k : Finset V} (hk : k ∈ H)
    (ω : Finset V → Bool) : retSet H (Function.update ω k true) = insert k (retSet H ω) := by
  classical
  ext e
  by_cases he : e = k
  · subst he; simp [retSet, hk]
  · simp [retSet, he]

omit [Fintype V] in
theorem retSet_update_false (H : Finset (Finset V)) (k : Finset V) (ω : Finset V → Bool) :
    retSet H (Function.update ω k false) = (retSet H ω).erase k := by
  classical
  ext e
  by_cases he : e = k
  · subst he; simp [retSet]
  · simp [retSet, he]

omit [Fintype V] in
theorem retSet_update_of_notMem {H : Finset (Finset V)} {k : Finset V} (hk : k ∉ H)
    (ω : Finset V → Bool) (b : Bool) : retSet H (Function.update ω k b) = retSet H ω := by
  classical
  ext e
  by_cases he : e = k
  · subst he; simp [retSet, hk]
  · simp [retSet, Function.update_of_ne he]

omit [Fintype V] in
/-- The codegree weight of the vertices spanned by a family of edges is at most the total
codegree weight of the family. -/
theorem sum_codegree_biUnion_le (H : Finset (Finset V)) (v : V) (B : Finset (Finset V)) :
    ∑ u ∈ ((B.biUnion id).erase v), (codegree H v u : ℝ) ≤ ∑ f ∈ B, edgeWeight H v f := by
  classical
  have hsub : (B.biUnion id).erase v ⊆ B.biUnion (fun f => f.erase v) := by
    intro u hu
    rw [Finset.mem_erase] at hu
    obtain ⟨f, hfB, huf⟩ := Finset.mem_biUnion.mp hu.2
    exact Finset.mem_biUnion.mpr ⟨f, hfB, Finset.mem_erase.mpr ⟨hu.1, huf⟩⟩
  calc ∑ u ∈ ((B.biUnion id).erase v), (codegree H v u : ℝ)
      ≤ ∑ u ∈ B.biUnion (fun f => f.erase v), (codegree H v u : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
    _ ≤ ∑ f ∈ B, ∑ u ∈ f.erase v, (codegree H v u : ℝ) :=
        sum_biUnion_le_of_nonneg B (fun f => f.erase v) _ (fun _ => Nat.cast_nonneg _)
    _ = ∑ f ∈ B, edgeWeight H v f := rfl

omit [Fintype V] in
theorem flipWeight_nonneg (H : Finset (Finset V)) (v : V) (k : Finset V) (ω : Finset V → Bool) :
    0 ≤ flipWeight H v k ω := by
  refine Finset.sum_nonneg fun f _ => ?_
  by_cases h : ω f <;> simp [h, edgeWeight_nonneg H v f]

omit [Fintype V] in
theorem D_safeDegCube_of_notMem {H : Finset (Finset V)} {k : Finset V} (hk : k ∉ H) (v : V)
    (ω : Finset V → Bool) : Cube.D k (safeDegCube H v) ω = 0 := by
  simp [Cube.D, safeDegCube, retSet_update_of_notMem hk]

/-! **The bounded-differences bound.**  Flipping the retention of `k` moves the safe degree at `v`
by at most `edgeWeight k + flipWeight k`. -/
omit [Fintype V] in
theorem abs_D_safeDegCube_le (H : Finset (Finset V)) (v : V) (k : Finset V)
    (ω : Finset V → Bool) :
    |Cube.D k (safeDegCube H v) ω| ≤ edgeWeight H v k + flipWeight H v k ω := by
  classical
  by_cases hk : k ∈ H
  · set R := retSet H ω with hR
    have hT : retSet H (Function.update ω k true) = insert k R := retSet_update_true hk ω
    have hF : retSet H (Function.update ω k false) = R.erase k := retSet_update_false H k ω
    have hflip := abs_safeDegree_flip_le H R k v
    have hcod : (((((flipInfluence R k).biUnion id).erase v).sum (fun u => codegree H v u) : ℕ) : ℝ)
        ≤ ∑ f ∈ flipInfluence R k, edgeWeight H v f := by
      have h := sum_codegree_biUnion_le H v (flipInfluence R k)
      rw [Nat.cast_sum]
      exact h
    have hins : ∑ f ∈ flipInfluence R k, edgeWeight H v f
        ≤ edgeWeight H v k + ∑ f ∈ R.filter (fun f => ¬ Disjoint f k), edgeWeight H v f := by
      rw [flipInfluence]
      by_cases hmem : k ∈ R.filter (fun f => ¬ Disjoint f k)
      · rw [Finset.insert_eq_self.mpr hmem]
        have := edgeWeight_nonneg H v k
        linarith only [this]
      · rw [Finset.sum_insert hmem]
    have hfilt : R.filter (fun f => ¬ Disjoint f k)
        = (meets H k).filter (fun f => ω f = true) := by
      ext f
      simp [hR, retSet, meets, Finset.mem_filter]
      tauto
    have hfw : ∑ f ∈ R.filter (fun f => ¬ Disjoint f k), edgeWeight H v f
        = flipWeight H v k ω := by
      rw [hfilt, flipWeight, Finset.sum_filter]
    have hnat : (((safeDegree H (covered (insert k R)) v : ℤ)
        - (safeDegree H (covered (R.erase k)) v : ℤ)).natAbs : ℝ)
        ≤ edgeWeight H v k + flipWeight H v k ω := by
      calc (((safeDegree H (covered (insert k R)) v : ℤ)
            - (safeDegree H (covered (R.erase k)) v : ℤ)).natAbs : ℝ)
          ≤ ((((((flipInfluence R k).biUnion id).erase v).sum
              (fun u => codegree H v u)) : ℕ) : ℝ) := by exact_mod_cast hflip
        _ ≤ ∑ f ∈ flipInfluence R k, edgeWeight H v f := hcod
        _ ≤ edgeWeight H v k + ∑ f ∈ R.filter (fun f => ¬ Disjoint f k), edgeWeight H v f := hins
        _ = edgeWeight H v k + flipWeight H v k ω := by rw [hfw]
    rw [Cube.D, safeDegCube, safeDegCube, hT, hF]
    set a := safeDegree H (covered (insert k R)) v
    set b := safeDegree H (covered (R.erase k)) v
    set m := ((a : ℤ) - (b : ℤ)).natAbs with hm
    have h2 : ((a : ℤ) - (b : ℤ)) ≤ (m : ℤ) ∧ -(m : ℤ) ≤ ((a : ℤ) - (b : ℤ)) := by omega
    refine abs_le.mpr ⟨?_, ?_⟩
    · have h3 : -(m : ℝ) ≤ (a : ℝ) - (b : ℝ) := by exact_mod_cast h2.2
      linarith only [hnat, h3]
    · have h3 : (a : ℝ) - (b : ℝ) ≤ (m : ℝ) := by exact_mod_cast h2.1
      linarith only [hnat, h3]
  · rw [D_safeDegCube_of_notMem hk v ω, abs_zero]
    have h1 := edgeWeight_nonneg H v k
    have h2 := flipWeight_nonneg H v k ω
    linarith only [h1, h2]

/-! ## The second moment of the flip weight -/

theorem Exp_flipWeight_sq_le {H : Finset (Finset V)} {p : ℝ} (v : V) (k : Finset V) :
    Cube.Exp p (fun ω => flipWeight H v k ω ^ 2)
      ≤ p * (∑ f ∈ meets H k, edgeWeight H v f ^ 2)
        + p ^ 2 * (∑ f ∈ meets H k, edgeWeight H v f) ^ 2 :=
  Cube.Exp_weighted_sum_sq_le (meets H k) (edgeWeight H v)

/-! ## The variance bound -/

/-- **The sharp per-vertex safe-degree variance bound.** -/
theorem safeDegCube_variance_le {H : Finset (Finset V)} {r Δ κ : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr : IsUniform H r) (hΔ : ∀ y : V, degree H y ≤ Δ)
    (hκ : ∀ y z : V, y ≠ z → codegree H y z ≤ κ) (v : V) :
    Cube.Exp p (fun ω => (safeDegCube H v ω - Cube.Exp p (safeDegCube H v)) ^ 2)
      ≤ 2 * p * ((r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2)
          * (1 + p * (r : ℝ) * (Δ : ℝ) + (p * (r : ℝ) * (Δ : ℝ)) ^ 2) := by
  classical
  set w : Finset V → ℝ := edgeWeight H v with hwdef
  set Q : Finset V → ℝ := fun k => ∑ f ∈ meets H k, w f ^ 2 with hQ
  set C : Finset V → ℝ := fun k => ∑ f ∈ meets H k, w f with hC
  set M : ℝ := (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 with hM
  have hrΔ : (0 : ℝ) ≤ (r : ℝ) * (Δ : ℝ) := by positivity
  have hMnn : 0 ≤ M := by rw [hM]; positivity
  have hES := Cube.centred_sq_le_sum_sq_diff hp0 hp1 (safeDegCube H v)
  have hzero : ∀ k ∈ (Finset.univ : Finset (Finset V)), k ∉ H →
      p * (1 - p) * Cube.Exp p (fun ω => Cube.D k (safeDegCube H v) ω ^ 2) = 0 := by
    intro k _ hk
    have hfun : (fun ω : Finset V → Bool => Cube.D k (safeDegCube H v) ω ^ 2)
        = fun _ => (0 : ℝ) := by
      funext ω; rw [D_safeDegCube_of_notMem hk]; ring
    rw [hfun, Cube.Exp_const]; ring
  have hsum : ∑ k ∈ H, p * (1 - p) * Cube.Exp p (fun ω => Cube.D k (safeDegCube H v) ω ^ 2)
      = ∑ k : Finset V, p * (1 - p) * Cube.Exp p (fun ω => Cube.D k (safeDegCube H v) ω ^ 2) :=
    Finset.sum_subset (Finset.subset_univ H) hzero
  have hterm : ∀ k ∈ H, p * (1 - p) * Cube.Exp p (fun ω => Cube.D k (safeDegCube H v) ω ^ 2)
      ≤ p * (2 * w k ^ 2 + 2 * p * Q k + 2 * p ^ 2 * C k ^ 2) := by
    intro k _
    have hEnn : 0 ≤ Cube.Exp p (fun ω => Cube.D k (safeDegCube H v) ω ^ 2) :=
      Cube.Exp_nonneg hp0 hp1 (fun _ => sq_nonneg _)
    have hmono : Cube.Exp p (fun ω => Cube.D k (safeDegCube H v) ω ^ 2)
        ≤ Cube.Exp p (fun ω => 2 * w k ^ 2 + 2 * flipWeight H v k ω ^ 2) := by
      refine Cube.Exp_mono hp0 hp1 fun ω => ?_
      have h1 := abs_D_safeDegCube_le H v k ω
      have h2 : Cube.D k (safeDegCube H v) ω ^ 2 ≤ (w k + flipWeight H v k ω) ^ 2 := by
        have := abs_nonneg (Cube.D k (safeDegCube H v) ω)
        nlinarith [sq_abs (Cube.D k (safeDegCube H v) ω)]
      nlinarith [sq_nonneg (w k - flipWeight H v k ω)]
    have hexp : Cube.Exp p (fun ω => 2 * w k ^ 2 + 2 * flipWeight H v k ω ^ 2)
        = 2 * w k ^ 2 + 2 * Cube.Exp p (fun ω => flipWeight H v k ω ^ 2) := by
      rw [Cube.Exp_add (f := fun _ => 2 * w k ^ 2) (g := fun ω => 2 * flipWeight H v k ω ^ 2),
        Cube.Exp_const, Cube.Exp_smul]
    have hfw : Cube.Exp p (fun ω => flipWeight H v k ω ^ 2) ≤ p * Q k + p ^ 2 * C k ^ 2 :=
      Exp_flipWeight_sq_le v k
    have hstep : Cube.Exp p (fun ω => Cube.D k (safeDegCube H v) ω ^ 2)
        ≤ 2 * w k ^ 2 + 2 * p * Q k + 2 * p ^ 2 * C k ^ 2 := by
      rw [hexp] at hmono; nlinarith only [hmono, hfw]
    nlinarith only [hp0, hEnn, hmono, hexp, hfw]
  have hS2 : ∑ k ∈ H, w k ^ 2 ≤ M := sum_edgeWeight_sq_le hr hΔ hκ v
  have hQnn : ∀ k, 0 ≤ Q k := fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hSQ : ∑ k ∈ H, Q k ≤ ((r : ℝ) * (Δ : ℝ)) * M := by
    have h1 : ∑ k ∈ H, Q k = ∑ f ∈ H, ((meets H f).card : ℝ) * w f ^ 2 :=
      sum_meets_swap H (fun f => w f ^ 2)
    have h2 : ∑ f ∈ H, ((meets H f).card : ℝ) * w f ^ 2
        ≤ ∑ f ∈ H, ((r : ℝ) * (Δ : ℝ)) * w f ^ 2 :=
      Finset.sum_le_sum fun f hf =>
        mul_le_mul_of_nonneg_right (card_meets_le hr hΔ hf) (sq_nonneg _)
    have h3 : ∑ f ∈ H, ((r : ℝ) * (Δ : ℝ)) * w f ^ 2
        = ((r : ℝ) * (Δ : ℝ)) * ∑ f ∈ H, w f ^ 2 := by rw [Finset.mul_sum]
    rw [h1]
    calc ∑ f ∈ H, ((meets H f).card : ℝ) * w f ^ 2 ≤ ((r : ℝ) * (Δ : ℝ)) * ∑ f ∈ H, w f ^ 2 := by
          rw [← h3]; exact h2
      _ ≤ ((r : ℝ) * (Δ : ℝ)) * M := mul_le_mul_of_nonneg_left hS2 hrΔ
  have hSC : ∑ k ∈ H, C k ^ 2 ≤ ((r : ℝ) * (Δ : ℝ)) * (((r : ℝ) * (Δ : ℝ)) * M) := by
    have h1 : ∀ k ∈ H, C k ^ 2 ≤ ((r : ℝ) * (Δ : ℝ)) * Q k := by
      intro k hk
      have hcs : C k ^ 2 ≤ ((meets H k).card : ℝ) * Q k := sq_sum_le_card_mul_sum_sq
      have := card_meets_le hr hΔ hk
      nlinarith [hQnn k]
    calc ∑ k ∈ H, C k ^ 2 ≤ ∑ k ∈ H, ((r : ℝ) * (Δ : ℝ)) * Q k := Finset.sum_le_sum h1
      _ = ((r : ℝ) * (Δ : ℝ)) * ∑ k ∈ H, Q k := by rw [Finset.mul_sum]
      _ ≤ ((r : ℝ) * (Δ : ℝ)) * (((r : ℝ) * (Δ : ℝ)) * M) := mul_le_mul_of_nonneg_left hSQ hrΔ
  have hfinal : ∑ k ∈ H, p * (2 * w k ^ 2 + 2 * p * Q k + 2 * p ^ 2 * C k ^ 2)
      = 2 * p * (∑ k ∈ H, w k ^ 2) + 2 * p ^ 2 * (∑ k ∈ H, Q k)
        + 2 * p ^ 3 * (∑ k ∈ H, C k ^ 2) := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  calc Cube.Exp p (fun ω => (safeDegCube H v ω - Cube.Exp p (safeDegCube H v)) ^ 2)
      ≤ ∑ k : Finset V, p * (1 - p)
          * Cube.Exp p (fun ω => Cube.D k (safeDegCube H v) ω ^ 2) := hES
    _ = ∑ k ∈ H, p * (1 - p) * Cube.Exp p (fun ω => Cube.D k (safeDegCube H v) ω ^ 2) := hsum.symm
    _ ≤ ∑ k ∈ H, p * (2 * w k ^ 2 + 2 * p * Q k + 2 * p ^ 2 * C k ^ 2) := Finset.sum_le_sum hterm
    _ = 2 * p * (∑ k ∈ H, w k ^ 2) + 2 * p ^ 2 * (∑ k ∈ H, Q k)
        + 2 * p ^ 3 * (∑ k ∈ H, C k ^ 2) := hfinal
    _ ≤ 2 * p * M + 2 * p ^ 2 * (((r : ℝ) * (Δ : ℝ)) * M)
        + 2 * p ^ 3 * (((r : ℝ) * (Δ : ℝ)) * (((r : ℝ) * (Δ : ℝ)) * M)) := by
          have e1 : 2 * p * (∑ k ∈ H, w k ^ 2) ≤ 2 * p * M :=
            mul_le_mul_of_nonneg_left hS2 (by linarith)
          have e2 : 2 * p ^ 2 * (∑ k ∈ H, Q k) ≤ 2 * p ^ 2 * (((r : ℝ) * (Δ : ℝ)) * M) :=
            mul_le_mul_of_nonneg_left hSQ (by positivity)
          have e3 : 2 * p ^ 3 * (∑ k ∈ H, C k ^ 2)
              ≤ 2 * p ^ 3 * (((r : ℝ) * (Δ : ℝ)) * (((r : ℝ) * (Δ : ℝ)) * M)) :=
            mul_le_mul_of_nonneg_left hSC
              (mul_nonneg (by norm_num) (pow_nonneg hp0 3))
          linarith only [e1, e2, e3]
    _ = 2 * p * M * (1 + p * (r : ℝ) * (Δ : ℝ) + (p * (r : ℝ) * (Δ : ℝ)) ^ 2) := by ring

end LeanPool.AsymptoticTrianglePacking.Internal

end




/-!
# LeanPool.AsymptoticTrianglePacking.Internal — the VARIANCE of the safe degree

The tight round of `LeanPool.AsymptoticTrianglePacking.Internal.Tight.TightRound` controls the safe
degree through the LOSS WEIGHT
`∑_{u} codeg(v,u)·1[u covered]` and the PAIR COUNT correction.  The pair count has mean `≍ Δγ²` and
is handled by Markov, which forces the upper tolerance `s ≳ Δγ²/θ` — first order in `γ` once the
exceptional fraction `θ` is pushed down to the `≍ γ` demanded by a `γ^{-1}log(1/β)`-round schedule,
and therefore not summable over the schedule.

This file removes that bottleneck by treating the safe degree DIRECTLY:

  `safeDeg(v) = ∑_{e ∋ v} X_e`,  `X_e = 1[(e∖v) ∩ covered = ∅]`,

and bounding its variance.  The covariance of two edge indicators is exactly

  `Cov(X_e, X_{e'}) = ℙ(S_e ∩ S_{e'}) − ℙ(S_e)·ℙ(S_{e'})`,  `S_e = ⋃_{u ∈ e∖v} {u covered}`,

(`safeIndicator_covariance_eq`) and the two-sided second-order estimates give

  `Cov(X_e, X_{e'}) ≤ (r−1)²ε₂ + Q_e·B_{e'} + Q_{e'}·B_e + |(e ∩ e')∖v|·q_hi`

(`safeIndicator_covariance_le`), with `Q_e = ∑_{u ∈ e∖v} q_u ≤ (r−1)q_hi` the first-order weight,
`B_e ≤ (r−1)²(q_hi² + ε₂)` the Bonferroni correction and `ε₂` the pair excess.  The crucial point is
that the `Θ(γ²)` terms CANCEL: `∑_{u,u'} ℙ(u,u' covered) ≤ Q_eQ_{e'} + (r−1)²ε₂` is matched by the
Bonferroni lower bound `ℙ(S_e)ℙ(S_{e'}) ≥ Q_eQ_{e'} − Q_eB_{e'} − Q_{e'}B_e`.

Summing over the `deg(v)²` pairs and using `∑_{u≠v} codeg(v,u)² ≤ κ(r−1)deg(v)`:

  `Var(safeDeg(v)) ≤ Δ²((r−1)²ε₂ + 2(r−1)³q_hi(q_hi² + ε₂)) + q_hi·κ·(r−1)·Δ`

(`safeDegree_variance_le`).  In the nibble regime `q_hi = γ/r`, `ε₂ ≤ 2κγ/(rΔ)`, `κ ≤ γΔ/(2048r)`
this is `≈ 2γ³Δ²`, so Chebyshev at a deviation `t = ε·γΔ` — a factor `ε` below the first-order
per-round degree gain — has failure probability `≈ 2γ/ε²`.  This is a decisive improvement on the
`pairCount` route (whose tolerance is first order in `γ`), but see the caveat on
`safeDegree_variance_le_codegree`: the residual `Θ(γ³Δ²)` term is still a constant factor too large
for the round to be iterated, and removing it requires a third-order Bonferroni estimate.

placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

public section

open MeasureTheory ProbabilityTheory Finset Hypergraph
attribute [local instance] Classical.propDecidable

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-! ## The covariance of two edge indicators -/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The product of two safe indicators is the indicator of the intersection of the safe events. -/
theorem safeIndicator_mul_eq {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) (e e' : Finset V) (ω : Ω) :
    safeIndicator ρ v e ω * safeIndicator ρ v e' ω
      = if ω ∈ {ω | Disjoint (e.erase v) (covered (retainedSet H ρ ω))}
            ∩ {ω | Disjoint (e'.erase v) (covered (retainedSet H ρ ω))} then 1 else 0 := by
  simp only [safeIndicator, Set.mem_inter_iff, Set.mem_ofPred_eq]
  split_ifs with h1 h2 h3 <;> simp_all

theorem integrable_safeIndicator_mul {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) (e e' : Finset V) :
    Integrable (fun ω => safeIndicator ρ v e ω * safeIndicator ρ v e' ω) (ℙ : Measure Ω) := by
  have hms : MeasurableSet ({ω | Disjoint (e.erase v) (covered (retainedSet H ρ ω))}
      ∩ {ω | Disjoint (e'.erase v) (covered (retainedSet H ρ ω))}) :=
    (measurableSet_safeEvent ρ v e).inter (measurableSet_safeEvent ρ v e')
  have hfun : (fun ω => safeIndicator ρ v e ω * safeIndicator ρ v e' ω)
      = fun ω => if ω ∈ {ω | Disjoint (e.erase v) (covered (retainedSet H ρ ω))}
            ∩ {ω | Disjoint (e'.erase v) (covered (retainedSet H ρ ω))} then (1 : ℝ) else 0 :=
    funext (safeIndicator_mul_eq ρ v e e')
  rw [hfun]
  refine (integrable_const (1 : ℝ)).mono'
    (Measurable.ite hms measurable_const measurable_const).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => ?_))
  split_ifs <;> simp

/-- **The covariance of two edge indicators.**
`𝔼[X_e X_{e'}] = 1 − ℙ(S_e) − ℙ(S_{e'}) + ℙ(S_e ∩ S_{e'})`. -/
theorem integral_safeIndicator_mul {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) (e e' : Finset V) :
    ∫ ω, safeIndicator ρ v e ω * safeIndicator ρ v e' ω ∂(ℙ : Measure Ω)
      = 1 - (ℙ : Measure Ω).real (⋃ u ∈ e.erase v, {ω | u ∈ covered (retainedSet H ρ ω)})
        - (ℙ : Measure Ω).real (⋃ u ∈ e'.erase v, {ω | u ∈ covered (retainedSet H ρ ω)})
        + (ℙ : Measure Ω).real
            ((⋃ u ∈ e.erase v, {ω | u ∈ covered (retainedSet H ρ ω)})
              ∩ (⋃ u ∈ e'.erase v, {ω | u ∈ covered (retainedSet H ρ ω)})) := by
  classical
  set A : Set Ω := ⋃ u ∈ e.erase v, {ω | u ∈ covered (retainedSet H ρ ω)} with hA
  set B : Set Ω := ⋃ u ∈ e'.erase v, {ω | u ∈ covered (retainedSet H ρ ω)} with hB
  have hmA : MeasurableSet A :=
    Finset.measurableSet_biUnion _ (fun u _ => measurableSet_vertex_covered ρ u)
  have hmB : MeasurableSet B :=
    Finset.measurableSet_biUnion _ (fun u _ => measurableSet_vertex_covered ρ u)
  have hsafeA : {ω | Disjoint (e.erase v) (covered (retainedSet H ρ ω))} = Aᶜ :=
    safeEvent_eq_compl ρ v e
  have hsafeB : {ω | Disjoint (e'.erase v) (covered (retainedSet H ρ ω))} = Bᶜ :=
    safeEvent_eq_compl ρ v e'
  have hind : (fun ω => safeIndicator ρ v e ω * safeIndicator ρ v e' ω)
      = Set.indicator (Aᶜ ∩ Bᶜ) 1 := by
    funext ω
    have hA' : ω ∈ Aᶜ ↔ Disjoint (e.erase v) (covered (retainedSet H ρ ω)) :=
      (Set.ext_iff.mp hsafeA ω).symm
    have hB' : ω ∈ Bᶜ ↔ Disjoint (e'.erase v) (covered (retainedSet H ρ ω)) :=
      (Set.ext_iff.mp hsafeB ω).symm
    rw [safeIndicator, safeIndicator, Set.indicator_apply]
    by_cases h1 : Disjoint (e.erase v) (covered (retainedSet H ρ ω)) <;>
      by_cases h2 : Disjoint (e'.erase v) (covered (retainedSet H ρ ω)) <;>
      simp [h1, h2, hA', hB', Set.mem_inter_iff]
  rw [hind, integral_indicator_one (hmA.compl.inter hmB.compl)]
  have hcompl : Aᶜ ∩ Bᶜ = (A ∪ B)ᶜ := by rw [Set.compl_union]
  rw [hcompl, measureReal_compl (hmA.union hmB)]
  have hunion : (ℙ : Measure Ω).real (A ∪ B) + (ℙ : Measure Ω).real (A ∩ B)
      = (ℙ : Measure Ω).real A + (ℙ : Measure Ω).real B :=
    measureReal_union_add_inter (μ := (ℙ : Measure Ω)) (s := A) (t := B) hmB
      (measure_ne_top _ _) (measure_ne_top _ _)
  simp only [probReal_univ]
  linarith only [hunion]

/-- **The covariance of two edge indicators.**
`Cov(X_e, X_{e'}) = ℙ(S_e ∩ S_{e'}) − ℙ(S_e)·ℙ(S_{e'})`. -/
theorem safeIndicator_covariance_eq {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) (e e' : Finset V) :
    ∫ ω, safeIndicator ρ v e ω * safeIndicator ρ v e' ω ∂(ℙ : Measure Ω)
        - (∫ ω, safeIndicator ρ v e ω ∂(ℙ : Measure Ω))
          * (∫ ω, safeIndicator ρ v e' ω ∂(ℙ : Measure Ω))
      = (ℙ : Measure Ω).real
            ((⋃ u ∈ e.erase v, {ω | u ∈ covered (retainedSet H ρ ω)})
              ∩ (⋃ u ∈ e'.erase v, {ω | u ∈ covered (retainedSet H ρ ω)}))
        - (ℙ : Measure Ω).real (⋃ u ∈ e.erase v, {ω | u ∈ covered (retainedSet H ρ ω)})
          * (ℙ : Measure Ω).real (⋃ u ∈ e'.erase v, {ω | u ∈ covered (retainedSet H ρ ω)}) := by
  rw [integral_safeIndicator_mul, integral_safeIndicator, integral_safeIndicator]
  ring

/-! ## A union bound for the intersection of two unions -/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- `ℙ((⋃_{i∈s} f i) ∩ (⋃_{j∈t} g j)) ≤ ∑_i ∑_j ℙ(f i ∩ g j)`. -/
theorem measureReal_inter_biUnion_le {ι ι' : Type*} (s : Finset ι) (t : Finset ι')
    (f : ι → Set Ω) (g : ι' → Set Ω) :
    (ℙ : Measure Ω).real ((⋃ i ∈ s, f i) ∩ (⋃ j ∈ t, g j))
      ≤ ∑ i ∈ s, ∑ j ∈ t, (ℙ : Measure Ω).real (f i ∩ g j) := by
  have hset : ((⋃ i ∈ s, f i) ∩ (⋃ j ∈ t, g j)) = ⋃ i ∈ s, ⋃ j ∈ t, (f i ∩ g j) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
    tauto
  rw [hset]
  refine (measureReal_biUnion_finset_le s _).trans (Finset.sum_le_sum (fun i _ => ?_))
  exact measureReal_biUnion_finset_le t _

/-! ## The quantitative covariance bound -/

/-- Elementary inequality behind the cancellation of the first-order terms: if `a ≥ Q − B`,
`b ≥ Q' − B'` with everything in sight nonnegative, then `a·b ≥ Q·Q' − Q·B' − Q'·B`. -/
private theorem auxProd {a b Q Q' B B' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hQ : 0 ≤ Q) (hQ' : 0 ≤ Q') (hB : 0 ≤ B) (hB' : 0 ≤ B')
    (h1 : Q - B ≤ a) (h2 : Q' - B' ≤ b) :
    Q * Q' - Q * B' - Q' * B ≤ a * b := by
  rcases le_or_gt 0 (Q - B) with h | h
  · rcases le_or_gt 0 (Q' - B') with h' | h'
    · nlinarith only [hB, hB', h1, h2, h, h']
    · nlinarith only [ha, hb, hB, hB', h, h']
  · nlinarith only [ha, hb, hQ, hQ', hB', h]

/-- **The covariance bound for two edge indicators.**  With covering rates at most `qhi`, pair
excesses at most `ε₂` and at most `n` non-`v` vertices per edge,

  `Cov(X_e, X_{e'}) ≤ n²ε₂ + |(e ∩ e')∖v|·qhi + 2·(n·qhi)·(n²(qhi² + ε₂))`.

The crucial point is that the first-order `Θ(n²qhi²)` terms CANCEL between the pairwise union bound
for `ℙ(S_e ∩ S_{e'})` and the second-order Bonferroni lower bound for `ℙ(S_e)·ℙ(S_{e'})`. -/
theorem safeIndicator_covariance_le {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : V) (e e' : Finset V)
    {n : ℕ} {qhi ε₂ : ℝ}
    (hq : ∀ u : V, coverRate H p u ≤ qhi) (hε0 : 0 ≤ ε₂)
    (hpair : ∀ u u' : V, u ≠ u' →
      (ℙ : Measure Ω).real ({ω | u ∈ covered (retainedSet H ρ ω)}
          ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
        - coverRate H p u * coverRate H p u' ≤ ε₂)
    (hn : (e.erase v).card ≤ n) (hn' : (e'.erase v).card ≤ n) :
    ∫ ω, safeIndicator ρ v e ω * safeIndicator ρ v e' ω ∂(ℙ : Measure Ω)
        - (∫ ω, safeIndicator ρ v e ω ∂(ℙ : Measure Ω))
          * (∫ ω, safeIndicator ρ v e' ω ∂(ℙ : Measure Ω))
      ≤ (n : ℝ) ^ 2 * ε₂ + (((e ∩ e').erase v).card : ℝ) * qhi
        + 2 * ((n : ℝ) * qhi) * ((n : ℝ) ^ 2 * (qhi ^ 2 + ε₂)) := by
  classical
  set S := e.erase v with hSdef
  set S' := e'.erase v with hS'def
  set C : V → Set Ω := fun u => {ω | u ∈ covered (retainedSet H ρ ω)} with hCdef
  set A : Set Ω := ⋃ u ∈ S, C u with hAdef
  set B : Set Ω := ⋃ u ∈ S', C u with hBdef
  have hq0 : 0 ≤ qhi := le_trans (coverRate_nonneg hp0 hp1 v) (hq v)
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  set Q : ℝ := ∑ u ∈ S, coverRate H p u with hQdef
  set Q' : ℝ := ∑ u ∈ S', coverRate H p u with hQ'def
  set Bc : ℝ := ∑ u ∈ S, ∑ u' ∈ S.erase u, (ℙ : Measure Ω).real (C u ∩ C u') with hBcdef
  set Bc' : ℝ := ∑ u ∈ S', ∑ u' ∈ S'.erase u, (ℙ : Measure Ω).real (C u ∩ C u') with hBc'def
  -- basic nonnegativity / upper bounds on the first-order weights
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun u _ => coverRate_nonneg hp0 hp1 u
  have hQ'0 : 0 ≤ Q' := Finset.sum_nonneg fun u _ => coverRate_nonneg hp0 hp1 u
  have hQle : Q ≤ (n : ℝ) * qhi := by
    calc Q ≤ ∑ _u ∈ S, qhi := Finset.sum_le_sum fun u _ => hq u
      _ = (S.card : ℝ) * qhi := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n : ℝ) * qhi := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hq0
  have hQ'le : Q' ≤ (n : ℝ) * qhi := by
    calc Q' ≤ ∑ _u ∈ S', qhi := Finset.sum_le_sum fun u _ => hq u
      _ = (S'.card : ℝ) * qhi := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n : ℝ) * qhi := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn') hq0
  -- the Bonferroni corrections are nonnegative and small
  have hBc0 : 0 ≤ Bc :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun u' _ => measureReal_nonneg
  have hBc'0 : 0 ≤ Bc' :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun u' _ => measureReal_nonneg
  have hsq0 : 0 ≤ qhi ^ 2 + ε₂ := by positivity
  have hBcBound : ∀ (T : Finset V), T.card ≤ n →
      ∑ u ∈ T, ∑ u' ∈ T.erase u, (ℙ : Measure Ω).real (C u ∩ C u')
        ≤ (n : ℝ) ^ 2 * (qhi ^ 2 + ε₂) := by
    intro T hT
    have hTn : (T.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hT
    calc ∑ u ∈ T, ∑ u' ∈ T.erase u, (ℙ : Measure Ω).real (C u ∩ C u')
        ≤ ∑ _u ∈ T, ∑ _u' ∈ T.erase _u, (qhi ^ 2 + ε₂) := by
          refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun u' hu' => ?_
          have hne : u ≠ u' := (Finset.mem_erase.mp hu').1.symm
          have := hpair u u' hne
          have h1 : coverRate H p u * coverRate H p u' ≤ qhi ^ 2 :=
            calc coverRate H p u * coverRate H p u'
                ≤ qhi * qhi := by
                  exact mul_le_mul (hq u) (hq u') (coverRate_nonneg hp0 hp1 u') hq0
              _ = qhi ^ 2 := by ring
          linarith only [this, h1]
      _ = ∑ u ∈ T, ((T.erase u).card : ℝ) * (qhi ^ 2 + ε₂) := by
          exact Finset.sum_congr rfl fun u _ => by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ _u ∈ T, (n : ℝ) * (qhi ^ 2 + ε₂) := by
          refine Finset.sum_le_sum fun u _ => ?_
          have : ((T.erase u).card : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast le_trans (Finset.card_erase_le) hT
          exact mul_le_mul_of_nonneg_right this hsq0
      _ = (T.card : ℝ) * ((n : ℝ) * (qhi ^ 2 + ε₂)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n : ℝ) ^ 2 * (qhi ^ 2 + ε₂) := by nlinarith [mul_nonneg hn0 hsq0]
  have hBcle : Bc ≤ (n : ℝ) ^ 2 * (qhi ^ 2 + ε₂) := hBcBound S hn
  have hBc'le : Bc' ≤ (n : ℝ) ^ 2 * (qhi ^ 2 + ε₂) := hBcBound S' hn'
  -- lower bounds on ℙ(A), ℙ(B) via Bonferroni
  have hAlo : Q - Bc ≤ (ℙ : Measure Ω).real A := by
    have := measureReal_biUnion_ge_bonferroni (Ω := Ω) S C
      (fun u => measurableSet_vertex_covered ρ u)
    have hQeq : ∑ u ∈ S, (ℙ : Measure Ω).real (C u) = Q :=
      Finset.sum_congr rfl fun u _ => prob_vertex_covered_eq ρ hp0 hp1 u
    rw [hQeq] at this
    exact this
  have hBlo : Q' - Bc' ≤ (ℙ : Measure Ω).real B := by
    have := measureReal_biUnion_ge_bonferroni (Ω := Ω) S' C
      (fun u => measurableSet_vertex_covered ρ u)
    have hQeq : ∑ u ∈ S', (ℙ : Measure Ω).real (C u) = Q' :=
      Finset.sum_congr rfl fun u _ => prob_vertex_covered_eq ρ hp0 hp1 u
    rw [hQeq] at this
    exact this
  -- upper bound on ℙ(A ∩ B)
  have hterm : ∀ u u' : V, (ℙ : Measure Ω).real (C u ∩ C u')
      ≤ coverRate H p u * coverRate H p u' + ε₂ + (if u = u' then qhi else 0) := by
    intro u u'
    by_cases huu' : u = u'
    · subst huu'
      rw [Set.inter_self, prob_vertex_covered_eq ρ hp0 hp1 u, ite_eq_left rfl]
      have h0 : 0 ≤ coverRate H p u * coverRate H p u :=
        mul_nonneg (coverRate_nonneg hp0 hp1 u) (coverRate_nonneg hp0 hp1 u)
      linarith [hq u]
    · rw [ite_eq_right huu']
      linarith only [hpair u u' huu']
  have hInterCard : S ∩ S' = (e ∩ e').erase v := by
    ext u
    simp only [hSdef, hS'def, Finset.mem_inter, Finset.mem_erase]
    tauto
  have hAB : (ℙ : Measure Ω).real (A ∩ B)
      ≤ Q * Q' + (n : ℝ) ^ 2 * ε₂ + (((e ∩ e').erase v).card : ℝ) * qhi := by
    refine (measureReal_inter_biUnion_le S S' C C).trans ?_
    calc ∑ u ∈ S, ∑ u' ∈ S', (ℙ : Measure Ω).real (C u ∩ C u')
        ≤ ∑ u ∈ S, ∑ u' ∈ S',
            (coverRate H p u * coverRate H p u' + ε₂ + (if u = u' then qhi else 0)) :=
          Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun u' _ => hterm u u'
      _ = Q * Q' + ((S.card : ℝ) * (S'.card : ℝ)) * ε₂ + ((S ∩ S').card : ℝ) * qhi := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
            Finset.sum_ite_eq, Finset.sum_ite_mem]
          rw [hQdef, hQ'def, Finset.sum_mul_sum]
          ring
      _ ≤ Q * Q' + (n : ℝ) ^ 2 * ε₂ + (((e ∩ e').erase v).card : ℝ) * qhi := by
          rw [hInterCard]
          have hcards : (S.card : ℝ) * (S'.card : ℝ) ≤ (n : ℝ) ^ 2 := by
            have h1 : (S.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
            have h2 : (S'.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'
            nlinarith [Nat.cast_nonneg (α := ℝ) S.card, Nat.cast_nonneg (α := ℝ) S'.card]
          nlinarith [hε0]
  -- assemble
  rw [safeIndicator_covariance_eq ρ v e e']
  have hprod : Q * Q' - Q * Bc' - Q' * Bc
      ≤ (ℙ : Measure Ω).real A * (ℙ : Measure Ω).real B :=
    auxProd measureReal_nonneg measureReal_nonneg hQ0 hQ'0 hBc0 hBc'0 hAlo hBlo
  have hcross : Q * Bc' + Q' * Bc ≤ 2 * ((n : ℝ) * qhi) * ((n : ℝ) ^ 2 * (qhi ^ 2 + ε₂)) := by
    have h1 : Q * Bc' ≤ ((n : ℝ) * qhi) * ((n : ℝ) ^ 2 * (qhi ^ 2 + ε₂)) :=
      mul_le_mul hQle hBc'le hBc'0 (mul_nonneg hn0 hq0)
    have h2 : Q' * Bc ≤ ((n : ℝ) * qhi) * ((n : ℝ) ^ 2 * (qhi ^ 2 + ε₂)) :=
      mul_le_mul hQ'le hBcle hBc0 (mul_nonneg hn0 hq0)
    linarith only [h1, h2]
  linarith only [hAB, hprod, hcross]

/-! ## The variance of the safe degree -/

/-- The mean of the safe degree, written as the sum of the edge-indicator means. -/
noncomputable def safeDegMean {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) : ℝ :=
  ∑ e ∈ H.filter (fun e => v ∈ e), ∫ ω, safeIndicator ρ v e ω ∂(ℙ : Measure Ω)

theorem integral_safeDegree_eq {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) :
    ∫ ω, (safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) ∂(ℙ : Measure Ω)
      = safeDegMean ρ v := by
  rw [safeDegree_expectation_eq ρ v, safeDegMean]
  exact Finset.sum_congr rfl fun e _ => (integral_safeIndicator ρ v e).symm

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem safeDegree_sub_mean_eq {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) (ω : Ω) :
    (safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v
      = ∑ e ∈ H.filter (fun e => v ∈ e),
          (safeIndicator ρ v e ω - ∫ ω', safeIndicator ρ v e ω' ∂(ℙ : Measure Ω)) := by
  rw [Finset.sum_sub_distrib, ← safeDegree_eq_sum ρ v ω, safeDegMean]

/-- The centred safe degree has an integrable square (it is a bounded random variable). -/
theorem integrable_sq_centered_safeDegree {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) :
    Integrable (fun ω =>
        ((safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v) ^ 2)
      (ℙ : Measure Ω) := by
  classical
  set c : Finset V → ℝ := fun e => ∫ ω, safeIndicator ρ v e ω ∂(ℙ : Measure Ω) with hc
  have hfun : (fun ω => ((safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v) ^ 2)
      = fun ω => ∑ e ∈ H.filter (fun e => v ∈ e), ∑ e' ∈ H.filter (fun e => v ∈ e),
          (safeIndicator ρ v e ω - c e) * (safeIndicator ρ v e' ω - c e') := by
    funext ω
    rw [safeDegree_sub_mean_eq ρ v ω, sq, Finset.sum_mul_sum]
  rw [hfun]
  refine integrable_finsetSum _ fun e _ => integrable_finsetSum _ fun e' _ => ?_
  have hprod : (fun ω => (safeIndicator ρ v e ω - c e) * (safeIndicator ρ v e' ω - c e'))
      = fun ω => safeIndicator ρ v e ω * safeIndicator ρ v e' ω
        - c e' * safeIndicator ρ v e ω - c e * safeIndicator ρ v e' ω + c e * c e' := by
    funext ω; ring
  rw [hprod]
  exact (((integrable_safeIndicator_mul ρ v e e').sub
    ((integrable_safeIndicator ρ v e).const_mul (c e'))).sub
    ((integrable_safeIndicator ρ v e').const_mul (c e))).add (integrable_const _)

/-- **The centred second moment of the safe degree as a double sum of covariances.** -/
theorem integral_sq_centered_safeDegree {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) :
    ∫ ω, ((safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v) ^ 2
        ∂(ℙ : Measure Ω)
      = ∑ e ∈ H.filter (fun e => v ∈ e), ∑ e' ∈ H.filter (fun e => v ∈ e),
          (∫ ω, safeIndicator ρ v e ω * safeIndicator ρ v e' ω ∂(ℙ : Measure Ω)
            - (∫ ω, safeIndicator ρ v e ω ∂(ℙ : Measure Ω))
              * (∫ ω, safeIndicator ρ v e' ω ∂(ℙ : Measure Ω))) := by
  classical
  set c : Finset V → ℝ := fun e => ∫ ω, safeIndicator ρ v e ω ∂(ℙ : Measure Ω) with hc
  have hrewrite : ∀ (e e' : Finset V) (ω : Ω),
      (safeIndicator ρ v e ω - c e) * (safeIndicator ρ v e' ω - c e')
        = safeIndicator ρ v e ω * safeIndicator ρ v e' ω
          - c e' * safeIndicator ρ v e ω - c e * safeIndicator ρ v e' ω + c e * c e' := by
    intro e e' ω; ring
  have hfun : ∀ e e' : Finset V,
      (fun ω => (safeIndicator ρ v e ω - c e) * (safeIndicator ρ v e' ω - c e'))
        = fun ω => safeIndicator ρ v e ω * safeIndicator ρ v e' ω
          - c e' * safeIndicator ρ v e ω - c e * safeIndicator ρ v e' ω + c e * c e' :=
    fun e e' => funext fun ω => hrewrite e e' ω
  have hi1 : ∀ e e' : Finset V,
      Integrable (fun ω => safeIndicator ρ v e ω * safeIndicator ρ v e' ω) (ℙ : Measure Ω) :=
    fun e e' => integrable_safeIndicator_mul ρ v e e'
  have hi2 : ∀ e e' : Finset V,
      Integrable (fun ω => c e' * safeIndicator ρ v e ω) (ℙ : Measure Ω) :=
    fun e e' => (integrable_safeIndicator ρ v e).const_mul (c e')
  have hi3 : ∀ e e' : Finset V,
      Integrable (fun ω => c e * safeIndicator ρ v e' ω) (ℙ : Measure Ω) :=
    fun e e' => (integrable_safeIndicator ρ v e').const_mul (c e)
  have hiAB : ∀ e e' : Finset V,
      Integrable (fun ω => safeIndicator ρ v e ω * safeIndicator ρ v e' ω
        - c e' * safeIndicator ρ v e ω) (ℙ : Measure Ω) :=
    fun e e' => (hi1 e e').sub (hi2 e e')
  have hiABC : ∀ e e' : Finset V,
      Integrable (fun ω => safeIndicator ρ v e ω * safeIndicator ρ v e' ω
        - c e' * safeIndicator ρ v e ω - c e * safeIndicator ρ v e' ω) (ℙ : Measure Ω) :=
    fun e e' => (hiAB e e').sub (hi3 e e')
  have hint : ∀ e e' : Finset V,
      Integrable (fun ω => (safeIndicator ρ v e ω - c e) * (safeIndicator ρ v e' ω - c e'))
        (ℙ : Measure Ω) := by
    intro e e'
    rw [hfun e e']
    exact (hiABC e e').add (integrable_const _)
  have hone : ∀ e e' : Finset V,
      ∫ ω, (safeIndicator ρ v e ω - c e) * (safeIndicator ρ v e' ω - c e') ∂(ℙ : Measure Ω)
        = ∫ ω, safeIndicator ρ v e ω * safeIndicator ρ v e' ω ∂(ℙ : Measure Ω) - c e * c e' := by
    intro e e'
    rw [hfun e e', integral_add (hiABC e e') (integrable_const _),
      integral_sub (hiAB e e') (hi3 e e'), integral_sub (hi1 e e') (hi2 e e'),
      integral_const_mul, integral_const_mul, integral_const]
    simp only [hc, probReal_univ, smul_eq_mul, one_mul]
    ring
  have hexp : ∀ ω, ((safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v) ^ 2
      = ∑ e ∈ H.filter (fun e => v ∈ e), ∑ e' ∈ H.filter (fun e => v ∈ e),
          (safeIndicator ρ v e ω - c e) * (safeIndicator ρ v e' ω - c e') := by
    intro ω
    rw [safeDegree_sub_mean_eq ρ v ω, sq, Finset.sum_mul_sum]
  simp only [hexp]
  rw [integral_finsetSum _ (fun e _ => integrable_finsetSum _ (fun e' _ => hint e e'))]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [integral_finsetSum _ (fun e' _ => hint e e')]
  exact Finset.sum_congr rfl fun e' _ => hone e e'

/-- **The variance bound for the safe degree.**  With `deg(v) ≤ Δ` edges at `v`, at most `n`
other vertices per edge, covering rates at most `qhi`, pair excesses at most `ε₂`, and the
codegree-controlled overlap budget `∑_{e,e'∈H_v} |(e ∩ e')∖v| ≤ Ksum`,

  `Var(safeDeg v) ≤ Δ²·(n²ε₂ + 2n³qhi(qhi² + ε₂)) + Ksum·qhi`. -/
theorem safeDegree_variance_le {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : V)
    {Δ n : ℕ} {qhi ε₂ Ksum : ℝ}
    (hq : ∀ u : V, coverRate H p u ≤ qhi) (hε0 : 0 ≤ ε₂)
    (hpair : ∀ u u' : V, u ≠ u' →
      (ℙ : Measure Ω).real ({ω | u ∈ covered (retainedSet H ρ ω)}
          ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
        - coverRate H p u * coverRate H p u' ≤ ε₂)
    (hdeg : (H.filter (fun e => v ∈ e)).card ≤ Δ)
    (hcard : ∀ e ∈ H.filter (fun e => v ∈ e), (e.erase v).card ≤ n)
    (hK : ∑ e ∈ H.filter (fun e => v ∈ e), ∑ e' ∈ H.filter (fun e => v ∈ e),
            (((e ∩ e').erase v).card : ℝ) ≤ Ksum) :
    ∫ ω, ((safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v) ^ 2
        ∂(ℙ : Measure Ω)
      ≤ (Δ : ℝ) ^ 2 * ((n : ℝ) ^ 2 * ε₂
            + 2 * ((n : ℝ) * qhi) * ((n : ℝ) ^ 2 * (qhi ^ 2 + ε₂)))
        + Ksum * qhi := by
  classical
  set Hv := H.filter (fun e => v ∈ e) with hHv
  have hq0 : 0 ≤ qhi := le_trans (coverRate_nonneg hp0 hp1 v) (hq v)
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  set Cst : ℝ := (n : ℝ) ^ 2 * ε₂ + 2 * ((n : ℝ) * qhi) * ((n : ℝ) ^ 2 * (qhi ^ 2 + ε₂))
    with hCst
  have hCst0 : 0 ≤ Cst := by
    have : 0 ≤ qhi ^ 2 + ε₂ := by positivity
    rw [hCst]; positivity
  rw [integral_sq_centered_safeDegree ρ v]
  have hstep : ∑ e ∈ Hv, ∑ e' ∈ Hv,
        (∫ ω, safeIndicator ρ v e ω * safeIndicator ρ v e' ω ∂(ℙ : Measure Ω)
          - (∫ ω, safeIndicator ρ v e ω ∂(ℙ : Measure Ω))
            * (∫ ω, safeIndicator ρ v e' ω ∂(ℙ : Measure Ω)))
      ≤ ∑ e ∈ Hv, ∑ e' ∈ Hv, (Cst + (((e ∩ e').erase v).card : ℝ) * qhi) := by
    refine Finset.sum_le_sum fun e he => Finset.sum_le_sum fun e' he' => ?_
    have := safeIndicator_covariance_le ρ hp0 hp1 v e e' hq hε0 hpair (hcard e he) (hcard e' he')
    rw [hCst]; linarith only [this]
  refine hstep.trans ?_
  have hsplit : ∑ e ∈ Hv, ∑ e' ∈ Hv, (Cst + (((e ∩ e').erase v).card : ℝ) * qhi)
      = (Hv.card : ℝ) * (Hv.card : ℝ) * Cst
        + (∑ e ∈ Hv, ∑ e' ∈ Hv, (((e ∩ e').erase v).card : ℝ)) * qhi := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul]
    ring
  rw [hsplit]
  have hcardΔ : (Hv.card : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hdeg
  have hcard0 : (0 : ℝ) ≤ (Hv.card : ℝ) := Nat.cast_nonneg _
  have hsq : (Hv.card : ℝ) * (Hv.card : ℝ) ≤ (Δ : ℝ) ^ 2 := by nlinarith only [hcardΔ]
  have h1 : (Hv.card : ℝ) * (Hv.card : ℝ) * Cst ≤ (Δ : ℝ) ^ 2 * Cst :=
    mul_le_mul_of_nonneg_right hsq hCst0
  have h2 : (∑ e ∈ Hv, ∑ e' ∈ Hv, (((e ∩ e').erase v).card : ℝ)) * qhi ≤ Ksum * qhi :=
    mul_le_mul_of_nonneg_right hK hq0
  linarith only [h1, h2]

/-! ## The codegree budget for the overlap sum -/

/-- `∑_{e,e' ∋ v} |(e ∩ e')∖v| = ∑_{e ∋ v} ∑_{u ∈ e∖v} codeg(v,u) ≤ deg(v)·n·κ`:  the overlap
budget in `safeDegree_variance_le` is controlled by the codegree, NOT by `Δ²`. -/
theorem sum_pair_overlap_le_codegree {H : Finset (Finset V)} (v : V) {n κ : ℕ}
    (hcard : ∀ e ∈ H.filter (fun e => v ∈ e), (e.erase v).card ≤ n)
    (hκ : ∀ u : V, u ≠ v → codegree H v u ≤ κ) :
    ∑ e ∈ H.filter (fun e => v ∈ e), ∑ e' ∈ H.filter (fun e => v ∈ e),
        (((e ∩ e').erase v).card : ℝ)
      ≤ ((H.filter (fun e => v ∈ e)).card : ℝ) * (n : ℝ) * (κ : ℝ) := by
  classical
  set Hv := H.filter (fun e => v ∈ e) with hHv
  have hinner : ∀ e ∈ Hv, ∑ e' ∈ Hv, (((e ∩ e').erase v).card : ℝ) ≤ (n : ℝ) * (κ : ℝ) := by
    intro e he
    have hswap : ∑ e' ∈ Hv, (((e ∩ e').erase v).card : ℝ)
        = ∑ u ∈ e.erase v, (codegree H v u : ℝ) := by
      have hpt : ∀ e' : Finset V, ((e ∩ e').erase v).card
          = ∑ u ∈ e.erase v, (if u ∈ e' then 1 else 0) := by
        intro e'
        rw [← Finset.card_filter]
        congr 1
        ext u
        simp only [Finset.mem_erase, Finset.mem_inter, Finset.mem_filter]
        tauto
      have : ∑ e' ∈ Hv, (((e ∩ e').erase v).card : ℝ)
          = ∑ e' ∈ Hv, ∑ u ∈ e.erase v, (if u ∈ e' then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun e' _ => ?_
        rw [hpt e']
        push_cast
        simp
      rw [this, Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => ?_
      have hfil : Hv.filter (fun e' => u ∈ e') = H.filter (fun e' => v ∈ e' ∧ u ∈ e') := by
        rw [hHv, Finset.filter_filter]
      rw [Finset.sum_boole, hfil]
      rfl
    rw [hswap]
    calc ∑ u ∈ e.erase v, (codegree H v u : ℝ)
        ≤ ∑ _u ∈ e.erase v, (κ : ℝ) := by
          refine Finset.sum_le_sum fun u hu => ?_
          exact_mod_cast hκ u (Finset.mem_erase.mp hu).1
      _ = ((e.erase v).card : ℝ) * (κ : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n : ℝ) * (κ : ℝ) := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard e he) (Nat.cast_nonneg _)
  calc ∑ e ∈ Hv, ∑ e' ∈ Hv, (((e ∩ e').erase v).card : ℝ)
      ≤ ∑ _e ∈ Hv, (n : ℝ) * (κ : ℝ) := Finset.sum_le_sum hinner
    _ = (Hv.card : ℝ) * (n : ℝ) * (κ : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **The codegree-tightened variance of the safe degree.**  Combining
`safeDegree_variance_le` with the codegree budget `sum_pair_overlap_le_codegree`:

  `Var(safeDeg v) ≤ Δ²(n²ε₂ + 2n³qhi(qhi²+ε₂)) + Δ·n·κ·qhi`.

In the nibble regime `n = r−1`, `qhi = γ/r`, `ε₂ ≤ 2κγ/(rΔ)`, `κ ≤ γΔ/(2048r)` the right-hand side
is `≈ 2γ³Δ²`, i.e. `o(γ²Δ²)`:  the standard deviation `≃ √2·γ^{3/2}Δ` is a factor `√γ` below the
first-order per-round degree gain `≃ γΔ/8`, so Chebyshev at deviation `t = ε·γΔ` gives a bad
fraction `≈ 2γ/ε²` per round.

Caveat for the iteration:  a schedule that covers a `c ≃ γ/(8r)` fraction per round needs the bad
fraction to be `≪ c`, i.e. `2γ/ε² ≪ γ/(8r)` — a condition on CONSTANTS that no choice of `γ` can
satisfy (`ε ≤ 1`).  The obstruction is the `2·Q_e·B_{e'}` term, which comes from combining a
first-order union bound for `ℙ(S_e ∩ S_{e'})` with a SECOND-order Bonferroni lower bound for
`ℙ(S_e)·ℙ(S_{e'})`; the two errors add rather than cancel.  A third-order Bonferroni would replace
`Θ(γ³Δ²)` by `Θ(γ⁴Δ²)`, making the bad fraction `≈ Cγ²/ε² ≪ γ/(8r)` for all small enough `γ`.
That refinement is NOT part of this file. -/
theorem safeDegree_variance_le_codegree {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : V)
    {Δ n κ : ℕ} {qhi ε₂ : ℝ}
    (hq : ∀ u : V, coverRate H p u ≤ qhi) (hε0 : 0 ≤ ε₂)
    (hpair : ∀ u u' : V, u ≠ u' →
      (ℙ : Measure Ω).real ({ω | u ∈ covered (retainedSet H ρ ω)}
          ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
        - coverRate H p u * coverRate H p u' ≤ ε₂)
    (hdeg : (H.filter (fun e => v ∈ e)).card ≤ Δ)
    (hcard : ∀ e ∈ H.filter (fun e => v ∈ e), (e.erase v).card ≤ n)
    (hκ : ∀ u : V, u ≠ v → codegree H v u ≤ κ) :
    ∫ ω, ((safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v) ^ 2
        ∂(ℙ : Measure Ω)
      ≤ (Δ : ℝ) ^ 2 * ((n : ℝ) ^ 2 * ε₂
            + 2 * ((n : ℝ) * qhi) * ((n : ℝ) ^ 2 * (qhi ^ 2 + ε₂)))
        + (Δ : ℝ) * (n : ℝ) * (κ : ℝ) * qhi := by
  have hq0 : 0 ≤ qhi := le_trans (coverRate_nonneg hp0 hp1 v) (hq v)
  have hK := sum_pair_overlap_le_codegree (H := H) v hcard hκ
  have hcardΔ : (((H.filter (fun e => v ∈ e)).card : ℝ)) ≤ (Δ : ℝ) := by exact_mod_cast hdeg
  have hK' : ∑ e ∈ H.filter (fun e => v ∈ e), ∑ e' ∈ H.filter (fun e => v ∈ e),
      (((e ∩ e').erase v).card : ℝ) ≤ (Δ : ℝ) * (n : ℝ) * (κ : ℝ) := by
    refine hK.trans ?_
    have h1 : (0 : ℝ) ≤ (n : ℝ) * (κ : ℝ) :=
      mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    nlinarith only [hcardΔ, h1]
  exact safeDegree_variance_le ρ hp0 hp1 v hq hε0 hpair hdeg hcard hK'

end LeanPool.AsymptoticTrianglePacking.Internal

end


/-!
# LeanPool.AsymptoticTrianglePacking.Internal — the round with a DIRECT safe-degree Chebyshev band

`LeanPool.AsymptoticTrianglePacking.Internal.exists_tight_round_cheb` controls the safe degree
indirectly, through the loss weight
(second moment, tolerance `t`) and the pair count (first moment, tolerance `s`).  The pair count has
mean `≍ Δγ²` and can only be handled by Markov, forcing `s ≳ Δγ²/θ`; combined with the junk budget
that the round schedule can afford, this is not summable over the `≍ γ^{-1}log(1/β)` rounds.

Here the safe degree is controlled DIRECTLY by its own variance
(`LeanPool.AsymptoticTrianglePacking.Internal.safeDegree_variance_le_codegree`), so a single
symmetric tolerance `t` replaces the pair
`(t, s)` and no first-moment (Markov) term survives:

  `#{v : |safeDeg(v) − 𝔼safeDeg(v)| ≥ t} ≤ ∑_v (safeDeg(v) − 𝔼)²/t²`,

whose mean is `N·Vs/t²`.  Combined with the Chebyshev coverage bound
(`LeanPool.AsymptoticTrianglePacking.Internal.prob_coverage_deviation_le`) one obtains
`exists_safe_round_cheb`: an outcome with

* fewer than `a` exceptional vertices, every other vertex having its safe degree within `t` of its
  mean, and
* at least `Q/2` covered vertices,

as soon as `N·Vs/(t²a) + Cvar/(Q/2)² < 1`.  With the codegree-tightened variance
`Vs ≈ 2γ³Δ²` (`LeanPool.AsymptoticTrianglePacking.Internal.safeDegree_variance_le_codegree`) the
tolerance `t ≍ γ^{3/2}Δ` already
suffices, which is a factor `√γ` below the first-order per-round gain `≍ γΔ/8`.

This removes the `pairCount` bottleneck, but it is NOT yet enough to iterate: a schedule covering a
`c ≍ γ/(8r)` fraction per round needs the exceptional fraction `a/N ≈ Vs/(εγΔ)² ≈ 2γ/ε²` to be
`≪ c`, a constant-factor condition that no choice of `γ` satisfies.  See the caveat on
`LeanPool.AsymptoticTrianglePacking.Internal.safeDegree_variance_le_codegree`: closing that gap
needs a third-order Bonferroni estimate,
which would turn `Vs ≈ 2γ³Δ²` into `Vs = O(γ⁴Δ²)`.

placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

public section

open MeasureTheory ProbabilityTheory Finset Hypergraph
attribute [local instance] Classical.propDecidable

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V] [Fintype V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-! ## The aggregated safe-degree badness -/

/-- The aggregated safe-degree badness of an outcome: `∑_v (safeDeg_v − 𝔼safeDeg_v)²/t²`.
It dominates the number of vertices whose safe degree deviates by `t` or more. -/
noncomputable def safeBad {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ v : V, ((safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v) ^ 2 / t ^ 2

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem safeBad_nonneg {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (t : ℝ) (ω : Ω) : 0 ≤ safeBad ρ t ω :=
  Finset.sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (sq_nonneg _)

theorem integrable_safeBad {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (t : ℝ) :
    Integrable (safeBad ρ t) (ℙ : Measure Ω) := by
  have h : safeBad ρ t = fun ω => ∑ v : V,
      ((safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v) ^ 2 / t ^ 2 := rfl
  rw [h]
  exact integrable_finsetSum _ fun v _ => (integrable_sq_centered_safeDegree ρ v).div_const _

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The number of vertices whose safe degree deviates by at least `t` is at most the aggregated
safe-degree badness. -/
theorem card_safeBadSet_le {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) {t : ℝ} (ht : 0 < t) (ω : Ω) :
    ((Finset.univ.filter (fun v : V =>
        t ≤ |(safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v|)).card : ℝ)
      ≤ safeBad ρ t ω := by
  classical
  set f : V → ℝ := fun v =>
    ((safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v) ^ 2 / t ^ 2 with hf
  have hf0 : ∀ v : V, 0 ≤ f v := fun v => div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hone : ∀ v ∈ Finset.univ.filter (fun v : V =>
      t ≤ |(safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v|),
      (1 : ℝ) ≤ f v := by
    intro v hv
    have hcase := (Finset.mem_filter.mp hv).2
    have h1 : t ^ 2
        ≤ ((safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v) ^ 2 := by
      rw [← sq_abs ((safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v)]
      exact pow_le_pow_left₀ ht.le hcase 2
    exact (one_le_div (by positivity)).mpr h1
  calc ((Finset.univ.filter (fun v : V =>
          t ≤ |(safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v|)).card : ℝ)
      = ∑ _v ∈ Finset.univ.filter (fun v : V =>
          t ≤ |(safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v|), (1 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ v ∈ Finset.univ.filter (fun v : V =>
          t ≤ |(safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v|), f v :=
        Finset.sum_le_sum hone
    _ ≤ ∑ v : V, f v :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun v _ _ => hf0 v)

/-- The mean of the aggregated safe-degree badness, from the per-vertex variance bound. -/
theorem integral_safeBad_le {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) {t Vs : ℝ} (ht : 0 < t)
    (hVs : ∀ v : V, ∫ ω, ((safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v) ^ 2
        ∂(ℙ : Measure Ω) ≤ Vs) :
    ∫ ω, safeBad ρ t ω ∂(ℙ : Measure Ω) ≤ (Fintype.card V : ℝ) * (Vs / t ^ 2) := by
  simp only [safeBad]
  rw [integral_finsetSum _
    (fun v _ => (integrable_sq_centered_safeDegree ρ v).div_const _)]
  calc ∑ v : V, ∫ ω,
        ((safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v) ^ 2 / t ^ 2
          ∂(ℙ : Measure Ω)
      ≤ ∑ _v : V, Vs / t ^ 2 := by
        refine Finset.sum_le_sum fun v _ => ?_
        rw [integral_div]
        exact (div_le_div_iff_of_pos_right (by positivity)).mpr (hVs v)
    _ = (Fintype.card V : ℝ) * (Vs / t ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-! ## The round -/

/-- **The round with a direct safe-degree band.**  If the per-vertex safe-degree variance is at
most `Vs`, the covered-count variance at most `Cvar`, the expected coverage at least `Q > 0`, and

  `N·(Vs/t²)/a + Cvar/(Q/2)² < 1`,

then there is an outcome with fewer than `a` exceptional vertices, all remaining vertices having
their safe degree within `t` of its mean, and at least `Q/2` covered vertices. -/
theorem exists_safe_round_cheb {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p)
    {t a Q Vs Cvar : ℝ} (ht : 0 < t) (ha : 0 < a) (hQ : 0 < Q)
    (hVs : ∀ v : V, ∫ ω, ((safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v) ^ 2
        ∂(ℙ : Measure Ω) ≤ Vs)
    (hmean : Q ≤ ∑ v : V, coverRate H p v)
    (hvar : ∫ ω, (((covered (retainedSet H ρ ω)).card : ℝ) - ∑ v : V, coverRate H p v) ^ 2
        ∂(ℙ : Measure Ω) ≤ Cvar)
    (hsmall : ((Fintype.card V : ℝ) * (Vs / t ^ 2)) / a + Cvar / (Q / 2) ^ 2 < 1) :
    ∃ ω : Ω, ∃ B : Finset V, (B.card : ℝ) < a ∧
      (∀ v ∉ B,
        |(safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v| < t)
      ∧ Q / 2 < ((covered (retainedSet H ρ ω)).card : ℝ) := by
  classical
  have hP1 : (ℙ : Measure Ω).real {ω | a ≤ safeBad ρ t ω}
      ≤ ((Fintype.card V : ℝ) * (Vs / t ^ 2)) / a := by
    refine le_trans (measureReal_ge_le_integral_div
      (fun ω => safeBad_nonneg ρ t ω) (integrable_safeBad ρ t) ha) ?_
    exact (div_le_div_iff_of_pos_right ha).mpr (integral_safeBad_le ρ ht hVs)
  have hP2 := prob_coverage_deviation_le ρ hQ hvar
  have hsum : (ℙ : Measure Ω).real {ω | a ≤ safeBad ρ t ω}
      + (ℙ : Measure Ω).real
        {ω | (Q / 2) ^ 2
          ≤ (((covered (retainedSet H ρ ω)).card : ℝ) - ∑ v : V, coverRate H p v) ^ 2} < 1 := by
    linarith
  obtain ⟨ω, hω1, hω2⟩ := exists_notMem_of_measureReal_add_lt_one hsum
  refine ⟨ω, Finset.univ.filter (fun v : V =>
    t ≤ |(safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v|), ?_, ?_, ?_⟩
  · have h1 := card_safeBadSet_le ρ ht ω
    have h2 : safeBad ρ t ω < a := by
      by_contra hc
      push Not at hc
      exact hω1 hc
    linarith
  · intro v hv
    by_contra hc
    push Not at hc
    exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hc⟩)
  · have h2 : ¬ ((Q / 2) ^ 2
        ≤ (((covered (retainedSet H ρ ω)).card : ℝ) - ∑ v : V, coverRate H p v) ^ 2) := hω2
    push Not at h2
    by_contra hc
    push Not at hc
    nlinarith only [h2, hmean, hc, hQ]

end LeanPool.AsymptoticTrianglePacking.Internal

end



/-!
# LeanPool.AsymptoticTrianglePacking.Internal — the Bernoulli retention carried by the finite cube

`LeanPool.AsymptoticTrianglePacking.Internal.exists_bernoulliRetention` produces *some* probability
space carrying a Bernoulli retention.
For the sharp variance bound of `LeanPool.AsymptoticTrianglePacking.Internal.Tight.SharpVariance` we
need a space on which the
Efron–Stein inequality of `LeanPool.AsymptoticTrianglePacking.Internal.Tight.CubeVariance` is
available, i.e. an honest product of
independent coordinates.  This file provides it: the cube `ι → Bool` with the explicit weighted
counting measure

  `cubeMeasure p = ∑_ω ofReal (wt p ω) · δ_ω`,

for which

* integrals are the elementary sums `LeanPool.AsymptoticTrianglePacking.Internal.Cube.Exp`
  (`LeanPool.AsymptoticTrianglePacking.Internal.integral_cubeMeasure`),
* the coordinate events are independent with probability `p`
  (`LeanPool.AsymptoticTrianglePacking.Internal.iIndepSet_cubeCoord`), hence
  the cube carries a `LeanPool.AsymptoticTrianglePacking.Internal.BernoulliRetention`
  (`LeanPool.AsymptoticTrianglePacking.Internal.cubeRetention`), and
* the Efron–Stein bound holds in integral form
  (`LeanPool.AsymptoticTrianglePacking.Internal.cube_centred_sq_le`).
-/

public section

open MeasureTheory ProbabilityTheory Finset

namespace LeanPool.AsymptoticTrianglePacking.Internal

namespace Cube

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Bernoulli(`p`) measure on the finite cube `ι → Bool`. -/
noncomputable def cubeMeasure (p : ℝ) : Measure (ι → Bool) :=
  ∑ ω : ι → Bool, ENNReal.ofReal (wt p ω) • Measure.dirac ω

/-- The finite cube as a measure space. -/
@[instance_reducible]
noncomputable def cubeSpace (p : ℝ) : MeasureSpace (ι → Bool) := ⟨cubeMeasure p⟩

theorem cubeMeasure_apply {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Set (ι → Bool)) :
    cubeMeasure p A = ENNReal.ofReal (∑ ω, wt p ω * Set.indicator A 1 ω) := by
  classical
  have hind : ∀ ω : ι → Bool, (0 : ℝ) ≤ Set.indicator A (1 : (ι → Bool) → ℝ) ω := by
    intro ω; by_cases h : ω ∈ A <;> simp [h]
  rw [cubeMeasure, Measure.coe_finsetSum]
  simp only [Finset.sum_apply, Measure.smul_apply, smul_eq_mul, MeasureTheory.Measure.dirac_apply]
  rw [ENNReal.ofReal_sum_of_nonneg (fun ω _ => mul_nonneg (wt_nonneg hp0 hp1 ω) (hind ω))]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [ENNReal.ofReal_mul (wt_nonneg hp0 hp1 ω)]
  congr 1
  by_cases h : ω ∈ A <;> simp [h]

theorem isProbabilityMeasure_cubeMeasure {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (cubeMeasure (ι := ι) p) := by
  constructor
  rw [cubeMeasure_apply hp0 hp1]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [sum_wt]
  simp

/-- Integrals against the cube measure are the elementary sums `Exp`. -/
theorem integral_cubeMeasure {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : (ι → Bool) → ℝ) :
    ∫ ω, f ω ∂(cubeMeasure p) = Exp p f := by
  rw [cubeMeasure, integral_finsetSum_measure]
  · rw [Exp]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [integral_smul_measure, integral_dirac, smul_eq_mul,
      ENNReal.toReal_ofReal (wt_nonneg hp0 hp1 ω)]
  · intro ω _
    exact Integrable.smul_measure (integrable_dirac (by finiteness)) (by simp)

/-! ## Independence of the coordinates -/

theorem indicator_biInter_eq (S : Finset ι) (ω : ι → Bool) :
    Set.indicator (⋂ e ∈ S, {ω : ι → Bool | ω e = true}) 1 ω
      = ∏ i, (if i ∈ S then (if ω i then (1 : ℝ) else 0) else 1) := by
  classical
  by_cases h : ∀ e ∈ S, ω e = true
  · rw [Set.indicator_of_mem (by simpa using h)]
    refine (Finset.prod_eq_one ?_).symm
    intro i _
    by_cases hi : i ∈ S
    · simp [hi, h i hi]
    · simp [hi]
  · push Not at h
    obtain ⟨e, heS, he⟩ := h
    have hnot : ω ∉ (⋂ e ∈ S, {ω : ι → Bool | ω e = true}) := by
      intro hmem
      simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hmem
      exact he (hmem e heS)
    rw [Set.indicator_of_notMem hnot]
    refine (Finset.prod_eq_zero (Finset.mem_univ e) ?_).symm
    simp [heS, he]

theorem Exp_indicator_biInter (p : ℝ) (S : Finset ι) :
    Exp p (fun ω => Set.indicator (⋂ e ∈ S, {ω : ι → Bool | ω e = true}) 1 ω) = p ^ S.card := by
  classical
  rw [Exp, Finset.sum_congr rfl (fun ω _ => by rw [indicator_biInter_eq S ω])]
  have h := Exp_prod p (fun (i : ι) (b : Bool) => if i ∈ S then (if b then (1 : ℝ) else 0) else 1)
  rw [Exp] at h
  rw [h, Finset.prod_congr rfl (g := fun i => if i ∈ S then p else 1)
    (fun i _ => by by_cases hi : i ∈ S <;> simp [hi]), ← Finset.prod_filter]
  simp

theorem cubeMeasure_biInter {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset ι) :
    cubeMeasure p (⋂ e ∈ S, {ω : ι → Bool | ω e = true}) = ENNReal.ofReal (p ^ S.card) := by
  rw [cubeMeasure_apply hp0 hp1]
  exact congrArg ENNReal.ofReal (Exp_indicator_biInter p S)

theorem cubeMeasure_coord {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (e : ι) :
    cubeMeasure p {ω : ι → Bool | ω e = true} = ENNReal.ofReal p := by
  have h := cubeMeasure_biInter hp0 hp1 ({e} : Finset ι)
  simpa using h

theorem iIndepSet_cubeCoord {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    iIndepSet (fun e : ι => {ω : ι → Bool | ω e = true}) (cubeMeasure p) := by
  refine (iIndepSet_iff_meas_biInter (fun _ => MeasurableSet.of_discrete)).mpr fun S => ?_
  rw [cubeMeasure_biInter hp0 hp1 S]
  rw [Finset.prod_congr rfl (fun e _ => cubeMeasure_coord hp0 hp1 e), Finset.prod_const,
    ← ENNReal.ofReal_pow hp0]

/-! ## Efron–Stein in integral form -/

theorem cube_centred_sq_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : (ι → Bool) → ℝ) :
    ∫ ω, (f ω - ∫ ω', f ω' ∂(cubeMeasure p)) ^ 2 ∂(cubeMeasure p)
      ≤ ∑ i : ι, p * (1 - p)
          * ∫ ω, (f (Function.update ω i true) - f (Function.update ω i false)) ^ 2
              ∂(cubeMeasure p) := by
  rw [integral_cubeMeasure hp0 hp1]
  simp only [integral_cubeMeasure hp0 hp1]
  exact centred_sq_le_sum_sq_diff hp0 hp1 f

end Cube

/-! ## The retention carried by the cube -/

open Cube

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The Bernoulli retention on the finite cube.**  The coordinate events of the cube
`Finset V → Bool` form an independent family of events of probability `p`. -/
noncomputable def cubeRetention (H : Finset (Finset V)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    @BernoulliRetention V _ (Finset V → Bool) (cubeSpace p) H p :=
  @BernoulliRetention.mk V _ (Finset V → Bool) (cubeSpace p) H p
    (fun e => {ω : Finset V → Bool | ω e = true})
    (fun e => by
      change MeasurableSet ((fun ω : Finset V → Bool => ω e) ⁻¹' ({true} : Set Bool))
      exact (measurable_pi_apply e) (measurableSet_singleton true))
    (iIndepSet_cubeCoord hp0 hp1) (fun e _ => cubeMeasure_coord hp0 hp1 e)

theorem retainedSet_cubeRetention (H : Finset (Finset V)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ω : Finset V → Bool) :
    @retainedSet V _ (Finset V → Bool) (cubeSpace p) H p (cubeRetention H hp0 hp1) ω
      = H.filter (fun e => ω e = true) := by
  ext e
  unfold retainedSet cubeRetention
  simp only [Finset.mem_filter]
  rfl

end LeanPool.AsymptoticTrianglePacking.Internal

end


/-!
# LeanPool.AsymptoticTrianglePacking.Internal — the sharp round: transporting the Efron–Stein
variance to the cube retention

`LeanPool.AsymptoticTrianglePacking.Internal.safeDegCube_variance_le`
(`LeanPool.AsymptoticTrianglePacking.Internal.Tight.SharpVariance`) is the sharp per-vertex
safe-degree variance bound on the elementary Bernoulli cube.  Here it is transported to the
`LeanPool.AsymptoticTrianglePacking.Internal.BernoulliRetention` carried by that cube
(`LeanPool.AsymptoticTrianglePacking.Internal.cubeRetention`), which is the form the
Chebyshev round `LeanPool.AsymptoticTrianglePacking.Internal.exists_safe_round_cheb` consumes.
-/

public section

open MeasureTheory ProbabilityTheory Finset Hypergraph
attribute [local instance] Classical.propDecidable

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The sharp per-vertex safe-degree variance, in integral form.** -/
theorem integral_centered_safeDegree_cube_le
    (K : Finset (Finset V)) {r Δ κ : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : IsUniform K r) (hΔ : ∀ y : V, degree K y ≤ Δ)
    (hκ : ∀ y z : V, y ≠ z → codegree K y z ≤ κ) (v : V) :
    ∫ ω, ((safeDegree K (covered (@retainedSet V _ (Finset V → Bool) (Cube.cubeSpace p) K p
              (cubeRetention K hp0 hp1) ω)) v : ℝ)
        - @safeDegMean V _ (Finset V → Bool) (Cube.cubeSpace p) K p (cubeRetention K hp0 hp1) v) ^ 2
        ∂(Cube.cubeMeasure p)
      ≤ 2 * p * ((r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2)
          * (1 + p * (r : ℝ) * (Δ : ℝ) + (p * (r : ℝ) * (Δ : ℝ)) ^ 2) := by
  let _ : MeasureSpace (Finset V → Bool) := Cube.cubeSpace p
  have _ : IsProbabilityMeasure (ℙ : Measure (Finset V → Bool)) :=
    Cube.isProbabilityMeasure_cubeMeasure hp0 hp1
  have hret : ∀ ω : Finset V → Bool,
      (safeDegree K (covered (retainedSet K (cubeRetention K hp0 hp1) ω)) v : ℝ)
        = safeDegCube K v ω := by
    intro ω
    rw [retainedSet_cubeRetention]
    rfl
  have hmean : safeDegMean (cubeRetention K hp0 hp1) v = Cube.Exp p (safeDegCube K v) := by
    rw [← integral_safeDegree_eq (cubeRetention K hp0 hp1) v]
    change ∫ ω, (safeDegree K (covered (retainedSet K (cubeRetention K hp0 hp1) ω)) v : ℝ)
        ∂(Cube.cubeMeasure p) = _
    rw [Cube.integral_cubeMeasure hp0 hp1]
    exact congrArg _ (funext hret)
  have hrw : ∫ ω, ((safeDegree K (covered (retainedSet K (cubeRetention K hp0 hp1) ω)) v : ℝ)
        - safeDegMean (cubeRetention K hp0 hp1) v) ^ 2 ∂(Cube.cubeMeasure p)
      = Cube.Exp p (fun ω => (safeDegCube K v ω - Cube.Exp p (safeDegCube K v)) ^ 2) := by
    rw [Cube.integral_cubeMeasure hp0 hp1]
    exact congrArg _ (funext fun ω => by rw [hret ω, hmean])
  rw [hrw]
  exact safeDegCube_variance_le hp0 hp1 hr hΔ hκ v


theorem safeDegMean_cubeRetention (K : Finset (Finset V)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (v : V) :
    @safeDegMean V _ (Finset V → Bool) (Cube.cubeSpace p) K p (cubeRetention K hp0 hp1) v
      = Cube.Exp p (safeDegCube K v) := by
  let _ : MeasureSpace (Finset V → Bool) := Cube.cubeSpace p
  have _ : IsProbabilityMeasure (ℙ : Measure (Finset V → Bool)) :=
    Cube.isProbabilityMeasure_cubeMeasure hp0 hp1
  rw [← integral_safeDegree_eq (cubeRetention K hp0 hp1) v]
  change ∫ ω, (safeDegree K (covered (retainedSet K (cubeRetention K hp0 hp1) ω)) v : ℝ)
      ∂(Cube.cubeMeasure p) = _
  rw [Cube.integral_cubeMeasure hp0 hp1]
  refine congrArg _ (funext fun ω => ?_)
  rw [retainedSet_cubeRetention]
  rfl

/-! ## The sharp round on an active set

The whole probabilistic content of the sharp round.  Everything that is not a deterministic
estimate of the MEAN safe degree `Cube.Exp p (safeDegCube K v)` is discharged here: the safe degree
is pinned to within `t` of its mean off an exceptional set of size `< a`, and the round covers more
than `Q/2` vertices, where `Q = |A|·δp(1−p)^{rΔ}` uses the degree floor only on the active set. -/

/-- **The sharp Chebyshev round on an active set.**  Given ANY two-sided estimate `mlo ≤ mean ≤ mhi`
for the mean safe degree on `A`, and the smallness condition, one round leaves every active,
uncovered vertex outside an exceptional set of size `< a` with residual degree in
`[mlo − t, mhi + t]`, and covers more than `Q/2` vertices.

The variance input is the SHARP Efron–Stein bound
`LeanPool.AsymptoticTrianglePacking.Internal.safeDegCube_variance_le`:
`Vs = 2p·r²κΔ²(1 + prΔ + (prΔ)²)`, which carries NO `Δ²` term at `p = γ/(rΔ)`. -/
theorem exists_sharp_round_band {K : Finset (Finset V)} (A : Finset V) {r Δ δ κ : ℕ}
    {p t a mlo : ℝ} {mhi : V → ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hr1 : 1 ≤ r) (hr : IsUniform K r)
    (hΔ : ∀ y : V, degree K y ≤ Δ) (hδA : ∀ y ∈ A, δ ≤ degree K y)
    (hκ : ∀ y z : V, y ≠ z → codegree K y z ≤ κ)
    (ht : 0 < t) (ha : 0 < a) (hδ0 : 0 < δ) (hA : 0 < A.card)
    (hlo : ∀ v ∈ A, mlo ≤ Cube.Exp p (safeDegCube K v))
    (hhi : ∀ v ∈ A, Cube.Exp p (safeDegCube K v) ≤ mhi v)
    (hsmall :
      ((Fintype.card V : ℝ) *
          ((2 * p * ((r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2)
            * (1 + p * (r : ℝ) * (Δ : ℝ) + (p * (r : ℝ) * (Δ : ℝ)) ^ 2)) / t ^ 2)) / a
        + ((Fintype.card V : ℝ) * ((Δ : ℝ) * p)
            + (Fintype.card V : ℝ) ^ 2
              * ((κ : ℝ) * p + 4 * (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 * p ^ 3))
          / ((A.card : ℝ) * ((δ : ℝ) * (p * (1 - p) ^ (r * Δ))) / 2) ^ 2 < 1) :
    ∃ R' : Finset (Finset V), R' ⊆ K ∧ ∃ B : Finset V, (B.card : ℝ) < a ∧
      (∀ v ∈ A, v ∉ B → v ∉ covered R' →
        mlo - t ≤ (degree (Hypergraph.residual K R') v : ℝ)
        ∧ (degree (Hypergraph.residual K R') v : ℝ) ≤ mhi v + t) ∧
      (A.card : ℝ) * ((δ : ℝ) * (p * (1 - p) ^ (r * Δ))) / 2 < ((covered R').card : ℝ) := by
  classical
  let _ : MeasureSpace (Finset V → Bool) := Cube.cubeSpace p
  have _ : IsProbabilityMeasure (ℙ : Measure (Finset V → Bool)) :=
    Cube.isProbabilityMeasure_cubeMeasure hp0.le hp1.le
  set ρ := cubeRetention K hp0.le hp1.le with hρ
  have hqlo : ∀ v ∈ A, (δ : ℝ) * (p * (1 - p) ^ (r * Δ)) ≤ coverRate K p v := by
    intro v hv
    refine le_trans ?_ (coverRate_ge hp0.le hp1.le hr hΔ v)
    have hd : (δ : ℝ) ≤ (degree K v : ℝ) := by exact_mod_cast hδA v hv
    exact mul_le_mul_of_nonneg_right hd (mul_nonneg hp0.le (pow_nonneg (by linarith) _))
  have hqlo0 : (0 : ℝ) < (δ : ℝ) * (p * (1 - p) ^ (r * Δ)) := by
    have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
    have : (0 : ℝ) < (1 - p) ^ (r * Δ) := pow_pos (by linarith) _
    positivity
  have hAR : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hA
  have hQ : (0 : ℝ) < (A.card : ℝ) * ((δ : ℝ) * (p * (1 - p) ^ (r * Δ))) := mul_pos hAR hqlo0
  have hmean : (A.card : ℝ) * ((δ : ℝ) * (p * (1 - p) ^ (r * Δ))) ≤ ∑ v : V, coverRate K p v := by
    have hnn : ∀ v : V, 0 ≤ coverRate K p v := fun v => coverRate_nonneg hp0.le hp1.le v
    calc (A.card : ℝ) * ((δ : ℝ) * (p * (1 - p) ^ (r * Δ)))
        = ∑ _v ∈ A, (δ : ℝ) * (p * (1 - p) ^ (r * Δ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ v ∈ A, coverRate K p v := Finset.sum_le_sum hqlo
      _ ≤ ∑ v : V, coverRate K p v :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (fun v _ _ => hnn v)
  have hqhi : ∀ u : V, coverRate K p u ≤ (Δ : ℝ) * p := by
    intro u
    refine le_trans (coverRate_le hp0.le hp1.le u) ?_
    have : (degree K u : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ u
    exact mul_le_mul_of_nonneg_right this hp0.le
  have hε0 : (0 : ℝ) ≤ (κ : ℝ) * p + 4 * (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 * p ^ 3 := by
    have h1 : (0 : ℝ) ≤ (κ : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp0.le
    have h2 : (0 : ℝ) ≤ 4 * (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 * p ^ 3 :=
      mul_nonneg (by positivity) (pow_nonneg hp0.le 3)
    linarith
  have hpair : ∀ u u' : V, u ≠ u' →
      (ℙ : Measure (Finset V → Bool)).real ({ω | u ∈ covered (retainedSet K ρ ω)}
          ∩ {ω | u' ∈ covered (retainedSet K ρ ω)})
        - coverRate K p u * coverRate K p u'
      ≤ (κ : ℝ) * p + 4 * (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 * p ^ 3 :=
    fun u u' huu' => pair_excess_le_codegree ρ hp0.le hp1.le hr hr1 hΔ hκ huu'
  have hvar := coveredCount_variance_le ρ hp0.le hp1.le hqhi hε0 hpair
  have hVs : ∀ v : V, ∫ ω, ((safeDegree K (covered (retainedSet K ρ ω)) v : ℝ)
      - safeDegMean ρ v) ^ 2 ∂(ℙ : Measure (Finset V → Bool))
      ≤ 2 * p * ((r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2)
          * (1 + p * (r : ℝ) * (Δ : ℝ) + (p * (r : ℝ) * (Δ : ℝ)) ^ 2) :=
    fun v => integral_centered_safeDegree_cube_le K hp0.le hp1.le hr hΔ hκ v
  obtain ⟨ω, B, hBcard, hband, hcov⟩ :=
    exists_safe_round_cheb ρ ht ha hQ hVs hmean hvar hsmall
  refine ⟨retainedSet K ρ ω, Finset.filter_subset _ _, B, hBcard, ?_, hcov⟩
  intro v hvA hvB hvc
  have hb := hband v hvB
  rw [safeDegree_eq_residual_degree_of_not_covered hvc,
    safeDegMean_cubeRetention K hp0.le hp1.le v] at hb
  have habs := abs_lt.mp hb
  exact ⟨by linarith only [hlo v hvA, habs.1], by linarith only [hhi v hvA, habs.2]⟩


/-! ## The deterministic mean estimates -/

/-- **Floor for the mean safe degree** (union bound on the covering events). -/
theorem Exp_safeDegCube_ge {K : Finset (Finset V)} {r Δ : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r) (hr : IsUniform K r)
    (hΔ : ∀ y : V, degree K y ≤ Δ) (v : V) :
    (degree K v : ℝ) * (1 - ((r : ℝ) - 1) * ((Δ : ℝ) * p)) ≤ Cube.Exp p (safeDegCube K v) := by
  classical
  let _ : MeasureSpace (Finset V → Bool) := Cube.cubeSpace p
  have _ : IsProbabilityMeasure (ℙ : Measure (Finset V → Bool)) :=
    Cube.isProbabilityMeasure_cubeMeasure hp0 hp1
  rw [← safeDegMean_cubeRetention K hp0 hp1 v, ← integral_safeDegree_eq (cubeRetention K hp0 hp1) v]
  refine le_trans ?_ (safeDegree_expectation_ge (cubeRetention K hp0 hp1) hp0 hp1 v)
  have hqhi : ∀ u : V, coverRate K p u ≤ (Δ : ℝ) * p := by
    intro u
    refine le_trans (coverRate_le hp0 hp1 u) ?_
    have : (degree K u : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ u
    exact mul_le_mul_of_nonneg_right this hp0
  have hstep : ∀ e ∈ K.filter (fun e => v ∈ e),
      1 - ((r : ℝ) - 1) * ((Δ : ℝ) * p) ≤ 1 - ∑ u ∈ e.erase v, coverRate K p u := by
    intro e he
    rw [Finset.mem_filter] at he
    have hcard : (e.erase v).card = r - 1 := by
      rw [Finset.card_erase_of_mem he.2, hr e he.1]
    have hsum : ∑ u ∈ e.erase v, coverRate K p u ≤ ((r : ℝ) - 1) * ((Δ : ℝ) * p) := by
      calc ∑ u ∈ e.erase v, coverRate K p u ≤ ∑ _u ∈ e.erase v, (Δ : ℝ) * p :=
            Finset.sum_le_sum fun u _ => hqhi u
        _ = ((e.erase v).card : ℝ) * ((Δ : ℝ) * p) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ = ((r : ℝ) - 1) * ((Δ : ℝ) * p) := by
            rw [hcard]
            congr 1
            have : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
              have : (1 : ℕ) ≤ r := hr1
              push_cast [Nat.cast_sub this]
              ring
            exact this
    linarith
  calc (degree K v : ℝ) * (1 - ((r : ℝ) - 1) * ((Δ : ℝ) * p))
      = ∑ _e ∈ K.filter (fun e => v ∈ e), (1 - ((r : ℝ) - 1) * ((Δ : ℝ) * p)) := by
        rw [Finset.sum_const, nsmul_eq_mul]; rfl
    _ ≤ ∑ e ∈ K.filter (fun e => v ∈ e), (1 - ∑ u ∈ e.erase v, coverRate K p u) :=
        Finset.sum_le_sum hstep

/-- **Ceiling for the mean safe degree** (second Bonferroni inequality), with the degree floor
used only on the active set `A`: the drop is carried by the `deg(v) − lostDegree K Aᶜ v` edges at
`v` that stay inside `A`. -/
theorem Exp_safeDegCube_le {K : Finset (Finset V)} (A : Finset V) {r Δ δ κ : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr2 : 2 ≤ r) (hr : IsUniform K r)
    (hΔ : ∀ y : V, degree K y ≤ Δ) (hδA : ∀ y ∈ A, δ ≤ degree K y)
    (hκ : ∀ y z : V, y ≠ z → codegree K y z ≤ κ) (v : V) :
    Cube.Exp p (safeDegCube K v)
      ≤ (degree K v : ℝ)
        - ((degree K v : ℝ) - (lostDegree K Aᶜ v : ℝ))
            * (((r : ℝ) - 1) * (δ : ℝ) * (p * (1 - p) ^ (r * Δ)))
        + (degree K v : ℝ) * (((r : ℝ) - 1) * ((r : ℝ) - 2))
            * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p) := by
  classical
  let _ : MeasureSpace (Finset V → Bool) := Cube.cubeSpace p
  have _ : IsProbabilityMeasure (ℙ : Measure (Finset V → Bool)) :=
    Cube.isProbabilityMeasure_cubeMeasure hp0 hp1
  rw [← safeDegMean_cubeRetention K hp0 hp1 v, ← integral_safeDegree_eq (cubeRetention K hp0 hp1) v]
  refine le_trans (safeDegree_expectation_le (cubeRetention K hp0 hp1) hp0 hp1 v) ?_
  set S := K.filter (fun e => v ∈ e) with hS
  set G := S.filter (fun e => Disjoint e Aᶜ) with hG
  set W : ℝ := ((r : ℝ) - 1) * (δ : ℝ) * (p * (1 - p) ^ (r * Δ)) with hW
  set E : ℝ := (((r : ℝ) - 1) * ((r : ℝ) - 2)) * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p) with hE
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr2
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    push_cast [Nat.cast_sub hr1]; ring
  have hLnn : (0 : ℝ) ≤ p * (1 - p) ^ (r * Δ) := mul_nonneg hp0 (pow_nonneg (by linarith) _)
  have hWnn : 0 ≤ W := by rw [hW]; exact mul_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) δ]) hLnn
  -- the pair correction of a single edge
  have hpair : ∀ e ∈ S, ∑ u ∈ e.erase v, ∑ u' ∈ (e.erase v).erase u,
      ((degree K u : ℝ) * (degree K u' : ℝ) * p ^ 2 + (codegree K u u' : ℝ) * p) ≤ E := by
    intro e he
    rw [hS, Finset.mem_filter] at he
    have hcard : (e.erase v).card = r - 1 := by rw [Finset.card_erase_of_mem he.2, hr e he.1]
    have hterm : ∀ u ∈ e.erase v, ∑ u' ∈ (e.erase v).erase u,
        ((degree K u : ℝ) * (degree K u' : ℝ) * p ^ 2 + (codegree K u u' : ℝ) * p)
        ≤ ((r : ℝ) - 2) * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p) := by
      intro u hu
      have hcard2 : ((e.erase v).erase u).card = r - 2 := by
        rw [Finset.card_erase_of_mem hu, hcard]; omega
      have hb : ∀ u' ∈ (e.erase v).erase u,
          ((degree K u : ℝ) * (degree K u' : ℝ) * p ^ 2 + (codegree K u u' : ℝ) * p)
            ≤ (Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p := by
        intro u' hu'
        have hne : u ≠ u' := (Finset.ne_of_mem_erase hu').symm
        have h1 : (degree K u : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ u
        have h2 : (degree K u' : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ u'
        have h3 : (codegree K u u' : ℝ) ≤ (κ : ℝ) := by exact_mod_cast hκ u u' hne
        have h4 : (0 : ℝ) ≤ (degree K u : ℝ) := Nat.cast_nonneg _
        have h5 : (0 : ℝ) ≤ (degree K u' : ℝ) := Nat.cast_nonneg _
        have h6 : (0 : ℝ) ≤ p ^ 2 := sq_nonneg p
        have hd : (degree K u : ℝ) * (degree K u' : ℝ) ≤ (Δ : ℝ) * (Δ : ℝ) :=
          mul_le_mul h1 h2 h5 (Nat.cast_nonneg _)
        have hc : (codegree K u u' : ℝ) * p ≤ (κ : ℝ) * p :=
          mul_le_mul_of_nonneg_right h3 hp0
        nlinarith only [hd, hc]
      calc ∑ u' ∈ (e.erase v).erase u,
            ((degree K u : ℝ) * (degree K u' : ℝ) * p ^ 2 + (codegree K u u' : ℝ) * p)
          ≤ ∑ _u' ∈ (e.erase v).erase u, ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p) :=
            Finset.sum_le_sum hb
        _ = (((e.erase v).erase u).card : ℝ) * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((r : ℝ) - 2) * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p) := by
            rw [hcard2]
            have : (((r - 2 : ℕ)) : ℝ) = (r : ℝ) - 2 := by push_cast [Nat.cast_sub hr2]; ring
            rw [this]
    calc ∑ u ∈ e.erase v, ∑ u' ∈ (e.erase v).erase u,
          ((degree K u : ℝ) * (degree K u' : ℝ) * p ^ 2 + (codegree K u u' : ℝ) * p)
        ≤ ∑ _u ∈ e.erase v, ((r : ℝ) - 2) * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p) :=
          Finset.sum_le_sum hterm
      _ = ((r : ℝ) - 1) * (((r : ℝ) - 2) * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p)) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard, hcast]
      _ = E := by rw [hE]; ring
  -- the covering-rate floor on good edges
  have hgood : ∀ e ∈ G, W ≤ ∑ u ∈ e.erase v, coverRate K p u := by
    intro e he
    rw [hG, Finset.mem_filter, hS, Finset.mem_filter] at he
    obtain ⟨⟨heK, hve⟩, hdisj⟩ := he
    have hcard : (e.erase v).card = r - 1 := by rw [Finset.card_erase_of_mem hve, hr e heK]
    have hsub : ∀ u ∈ e.erase v, u ∈ A := by
      intro u hu
      by_contra hA
      exact (Finset.disjoint_left.mp hdisj (Finset.mem_of_mem_erase hu))
        (Finset.mem_compl.mpr hA)
    have hb : ∀ u ∈ e.erase v, (δ : ℝ) * (p * (1 - p) ^ (r * Δ)) ≤ coverRate K p u := by
      intro u hu
      refine le_trans ?_ (coverRate_ge hp0 hp1 hr hΔ u)
      have hd : (δ : ℝ) ≤ (degree K u : ℝ) := by exact_mod_cast hδA u (hsub u hu)
      exact mul_le_mul_of_nonneg_right hd hLnn
    calc W = ((e.erase v).card : ℝ) * ((δ : ℝ) * (p * (1 - p) ^ (r * Δ))) := by
          rw [hcard, hcast, hW]; ring
      _ = ∑ _u ∈ e.erase v, (δ : ℝ) * (p * (1 - p) ^ (r * Δ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ u ∈ e.erase v, coverRate K p u := Finset.sum_le_sum hb
  -- assemble
  have hnonneg : ∀ e ∈ S, (0 : ℝ) ≤ ∑ u ∈ e.erase v, coverRate K p u :=
    fun _ _ => Finset.sum_nonneg fun u _ => coverRate_nonneg hp0 hp1 u
  have hbound : ∀ e ∈ S,
      (1 - ∑ u ∈ e.erase v, coverRate K p u
        + ∑ u ∈ e.erase v, ∑ u' ∈ (e.erase v).erase u,
            ((degree K u : ℝ) * (degree K u' : ℝ) * p ^ 2 + (codegree K u u' : ℝ) * p))
      ≤ 1 - (if Disjoint e Aᶜ then W else 0) + E := by
    intro e he
    have h1 := hpair e he
    by_cases hd : Disjoint e Aᶜ
    · have h2 := hgood e (by rw [hG, Finset.mem_filter]; exact ⟨he, hd⟩)
      rw [ite_eq_left hd]; linarith
    · rw [ite_eq_right hd]; linarith [hnonneg e he]
  have hsum : ∑ e ∈ S, (1 - (if Disjoint e Aᶜ then W else 0) + E)
      = (degree K v : ℝ) - (G.card : ℝ) * W + (degree K v : ℝ) * E := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
      nsmul_eq_mul, nsmul_eq_mul, mul_one, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rfl
  have hGcard : (G.card : ℝ) = (degree K v : ℝ) - (lostDegree K Aᶜ v : ℝ) := by
    have hsplit : S.card = G.card + (S.filter (fun e => ¬ Disjoint e Aᶜ)).card := by
      rw [hG]
      exact (Finset.card_filter_add_card_filter_not (p := fun e => Disjoint e Aᶜ)).symm
    have hlost : (S.filter (fun e => ¬ Disjoint e Aᶜ)).card = lostDegree K Aᶜ v := by
      rw [lostDegree, hS, Finset.filter_filter]
    have hSc : S.card = degree K v := rfl
    have : degree K v = G.card + lostDegree K Aᶜ v := by rw [← hSc, hsplit, hlost]
    rw [this]; push_cast; ring
  calc ∑ e ∈ S,
        (1 - ∑ u ∈ e.erase v, coverRate K p u
          + ∑ u ∈ e.erase v, ∑ u' ∈ (e.erase v).erase u,
              ((degree K u : ℝ) * (degree K u' : ℝ) * p ^ 2 + (codegree K u u' : ℝ) * p))
      ≤ ∑ e ∈ S, (1 - (if Disjoint e Aᶜ then W else 0) + E) := Finset.sum_le_sum hbound
    _ = (degree K v : ℝ) - (G.card : ℝ) * W + (degree K v : ℝ) * E := hsum
    _ = (degree K v : ℝ)
          - ((degree K v : ℝ) - (lostDegree K Aᶜ v : ℝ))
              * (((r : ℝ) - 1) * (δ : ℝ) * (p * (1 - p) ^ (r * Δ)))
          + (degree K v : ℝ) * (((r : ℝ) - 1) * ((r : ℝ) - 2))
              * ((Δ : ℝ) ^ 2 * p ^ 2 + (κ : ℝ) * p) := by
        rw [hGcard, hE, hW]; ring

end LeanPool.AsymptoticTrianglePacking.Internal

end


/-!
# LeanPool.AsymptoticTrianglePacking.Internal — assembling the sharp round

`LeanPool.AsymptoticTrianglePacking.Internal.SharpRoundFor`
(`LeanPool.AsymptoticTrianglePacking.Internal.Tight.SharpRound`) is proved here in the regime `2γ ≤
ε`, from

* `LeanPool.AsymptoticTrianglePacking.Internal.exists_sharp_round_band` — the probabilistic content
  (sharp Efron–Stein variance +
  Chebyshev on the safe degree, cover variance on the active set), and
* `LeanPool.AsymptoticTrianglePacking.Internal.Exp_safeDegCube_ge` /
  `LeanPool.AsymptoticTrianglePacking.Internal.Exp_safeDegCube_le` — the two deterministic estimates
  of the
  MEAN safe degree (union bound and second Bonferroni inequality).

The retention is `p = γ/(r⌊Δ⌋₊)`, the tolerance `t = εγ⌊Δ⌋₊/16`, the exceptional budget `a = θ|V|`,
the degree threshold `D₀ = 256r/(α²γ) + 96/ε + 4` and the codegree factor `c₀ = θε²γα²/(16384r)`.

The hypothesis `2γ ≤ ε` is what pays for the SECOND-ORDER error of the mean safe degree: the
Bonferroni residue is `Θ(γ²Δ)` per vertex, while `SharpRoundFor` allows only `εγΔ`, so a hypothesis
of the shape `γ = O(ε)` is unavoidable for a round built from the uniform retention `p = γ/(rΔ)`.
The CONSTANT, however, is not: the exact requirement is that the residue

  `Δ⌊·⌋(r−1)(r−2)(Δ²p² + κp) ≤ γ²Δ`  (mean ceiling, Bonferroni)

together with the Chebyshev tolerance `t`, the codegree term `rκγ`, and the rounding/`(1−p)^{rΔ}`
discrepancy `γ³Δ + O(1)` fit inside `εγΔ`.  Charging `γ²Δ ≤ εγΔ/2`, `γ³Δ ≤ εγΔ/4`,
`t ≤ εγΔ/16` and the two `O(1)`-terms `εγΔ/32` each leaves `28/32` of the budget used, so `2γ ≤ ε`
suffices. This is exactly the regime the tight-band schedule uses:
`LeanPool.AsymptoticTrianglePacking.Internal.exists_tightParams`
sets `ε = 4aγ` with `a = (r−1)/r ≥ 1/2`, hence `ε ≥ 2γ`.

The discrepancy `γ³Δ + O(1)` (rather than the `γ²Δ + O(1)` of the earlier bookkeeping) comes from
the sharp upper bound `(1−p)^{rΔ} ≤ 1 − γ + γ²/2`
(`LeanPool.AsymptoticTrianglePacking.Internal.one_sub_pow_le_quadratic`), which cancels
the `(1−γ)` factor carried by the ceiling drop that `SharpRoundFor` requests.
-/

public section

open MeasureTheory ProbabilityTheory Finset Hypergraph
attribute [local instance] Classical.propDecidable

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem lostDegree_le_degree (K : Finset (Finset V)) (B : Finset V) (v : V) :
    lostDegree K B v ≤ degree K v := by
  classical
  refine Finset.card_le_card ?_
  intro e he
  rw [Finset.mem_filter] at he ⊢
  exact ⟨he.1, he.2.1⟩

/-- **Second-order upper bound for `(1 − p)^m`.**  For `0 ≤ p ≤ 1`,
`(1 − p)^m ≤ 1 − mp + (mp)²/2`; at `mp = γ` this is `1 − γ + γ²/2`, the bound that cancels the
`(1 − γ)` factor of the requested ceiling drop. -/
theorem one_sub_pow_le_quadratic {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) :
    (1 - p) ^ m ≤ 1 - (m : ℝ) * p + ((m : ℝ) * p) ^ 2 / 2 := by
  induction m with
  | zero => simp
  | succ n ih =>
      have hmul : (1 - p) ^ (n + 1) ≤ (1 - (n : ℝ) * p + ((n : ℝ) * p) ^ 2 / 2) * (1 - p) := by
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_right ih (by linarith)
      have hstep : (1 - (n : ℝ) * p + ((n : ℝ) * p) ^ 2 / 2) * (1 - p)
          ≤ 1 - ((n : ℝ) + 1) * p + (((n : ℝ) + 1) * p) ^ 2 / 2 := by
        linarith only [sq_nonneg p, mul_nonneg (sq_nonneg ((n : ℝ) * p)) hp0]
      push_cast
      linarith only [hmul, hstep]

/-- **The rounding/`(1−p)^{rΔ}` discrepancy of the ceiling drop.**  With `dn = ⌈δ⌉₊`, `Dn = ⌊Δ⌋₊`
and `L = (1−p)^{rDn} ≤ 1 − γ + γ²/2`, the achieved relative drop `dn·L/Dn` exceeds the requested one
`δ(1−γ)/Δ` by at most `γ²  + 3/Δ` in relative terms — i.e. `Δ·(dn L/Dn) ≤ δ(1−γ) + γ²Δ + 3`. -/
theorem sharp_drop_ratio_le (γ δ Δ Dn dn L : ℝ)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hδ2 : 2 ≤ δ) (hδΔ : δ ≤ Δ)
    (hDn3 : 3 ≤ Dn) (hΔDn : Δ < Dn + 1)
    (hδdn : δ ≤ dn) (hdnδ : dn < δ + 1) (hL0 : 0 < L) (hLu : L ≤ 1 - γ + γ ^ 2 / 2) :
    Δ * (dn * L / Dn) ≤ δ * (1 - γ) + γ ^ 2 * Δ + 3 := by
  have hDn0 : (0 : ℝ) < Dn := by linarith only [hDn3]
  have hΔ0 : (0 : ℝ) < Δ := by linarith only [hδ2, hδΔ]
  have hquad : (0 : ℝ) ≤ 1 - γ + γ ^ 2 / 2 := by linarith only [hγ1, sq_nonneg γ]
  have hs1 : dn * L ≤ (δ + 1) * (1 - γ + γ ^ 2 / 2) :=
    mul_le_mul (by linarith) hLu hL0.le (by linarith)
  have hs2 : Δ * (dn * L) ≤ (Dn + 1) * ((δ + 1) * (1 - γ + γ ^ 2 / 2)) :=
    mul_le_mul (by linarith) hs1 (mul_nonneg (by linarith) hL0.le) (by linarith)
  have hb1 : Dn * ((δ + 1) * γ ^ 2 / 2) ≤ Dn * (γ ^ 2 * Δ) := by
    linarith only [mul_nonneg (mul_nonneg hDn0.le (sq_nonneg γ))
      (show (0 : ℝ) ≤ Δ - (δ + 1) / 2 by linarith only [hδΔ, hδ2])]
  have hb3 : (δ + 1) * (1 - γ + γ ^ 2 / 2) ≤ 2 * Dn := by
    linarith only [hδΔ, hΔDn, hDn3,
      mul_nonneg (show (0 : ℝ) ≤ δ + 1 by linarith only [hδ2])
        (show (0 : ℝ) ≤ γ - γ ^ 2 / 2 by
          linarith only [hγ0.le,
            mul_nonneg hγ0.le (show (0 : ℝ) ≤ 1 / 2 - γ by linarith only [hγ1])])]
  have hs3 : (Dn + 1) * ((δ + 1) * (1 - γ + γ ^ 2 / 2))
      ≤ (δ * (1 - γ) + γ ^ 2 * Δ + 3) * Dn := by
    linarith only [hb1, hb3, mul_nonneg hDn0.le hγ0.le]
  rw [show Δ * (dn * L / Dn) = Δ * (dn * L) / Dn by ring, div_le_iff₀ hDn0]
  linarith only [hs2, hs3]

/-- **The survival factor of one round.**  For `m·p = γ` with `0 ≤ p ≤ 1`, Bernoulli and
`LeanPool.AsymptoticTrianglePacking.Internal.one_sub_pow_le_quadratic` pin `(1 − p)^m` between `1 −
γ` and `1 − γ + γ²/2`. -/
theorem sharp_survival_bounds {p γ : ℝ} {m : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hpγ : (m : ℝ) * p = γ) :
    1 - γ ≤ (1 - p) ^ m ∧ (1 - p) ^ m ≤ 1 - γ + γ ^ 2 / 2 := by
  refine ⟨?_, ?_⟩
  · have h := one_add_mul_le_pow (a := -p) (by linarith) m
    have h2 : (1 : ℝ) + (m : ℝ) * (-p) = 1 - γ := by rw [← hpγ]; ring
    have h3 : (1 : ℝ) + -p = 1 - p := by ring
    rw [h2, h3] at h
    exact h
  · have h := one_sub_pow_le_quadratic hp0 hp1 m
    rw [hpγ] at h
    exact h

/-- **The mean ceiling is monotone in the degree.**  Replacing the degree `D` of a vertex by the
global ceiling `Dn` and its floor by `dn` can only increase the mean safe degree estimate. -/
theorem sharp_mean_ceiling_arith {D Dn dn l W C X : ℝ} (hW : 0 ≤ W) (hC : 0 ≤ C) (hX : 0 ≤ X)
    (h1 : D ≤ Dn) (h2 : dn ≤ D) :
    D - (D - l) * W + D * C * X ≤ Dn - (dn - l) * W + Dn * C * X := by
  have e1 : (dn - l) * W ≤ (D - l) * W := mul_le_mul_of_nonneg_right (by linarith) hW
  have e2 : D * C * X ≤ Dn * C * X :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hC) hX
  linarith

/-- **The cover rate of one round.**  With `p = γ/(rD)`, a floor `dn ≥ D/2` and a survival factor
`L ≥ 1/2`, each active vertex is matched with probability at least `γ/(8r)`. -/
theorem sharp_cover_rate_le {rr γ Dn dn p L : ℝ} (hR0 : 0 < rr) (hDn0 : 0 < Dn)
    (hdnhalf : Dn / 2 ≤ dn) (hLhalf : 1 / 2 ≤ L) (hp0 : 0 < p) (hpγ : rr * Dn * p = γ) :
    γ / (8 * rr) ≤ dn * (p * L) / 2 := by
  have hLpos : (0 : ℝ) < L := by linarith only [hLhalf]
  have hdnL : Dn / 4 ≤ dn * L := by
    linarith only [mul_le_mul_of_nonneg_right hdnhalf hLpos.le,
      mul_le_mul_of_nonneg_left hLhalf (show (0 : ℝ) ≤ Dn / 2 by linarith only [hDn0])]
  rw [div_le_iff₀ (by positivity)]
  linarith only [mul_le_mul_of_nonneg_left hdnL
    (show (0 : ℝ) ≤ 4 * rr * p by positivity), hpγ]

/-- **The second-order (Bonferroni) error of the mean safe degree.**  With `p = γ/(rD)` the residue
`D(r−1)(r−2)(D²p² + κp)` is at most `Δγ² + rκγ`. -/
theorem sharp_bonferroni_error_le {rr γ Δ Dn kn p Err : ℝ} (hR2 : 2 ≤ rr) (hDn0 : 0 ≤ Dn)
    (hkn0 : 0 ≤ kn) (hp0 : 0 < p) (hpγ : rr * Dn * p = γ) (hDn_le : Dn ≤ Δ)
    (hErrdef : Err = Dn * ((rr - 1) * (rr - 2)) * (Dn ^ 2 * p ^ 2 + kn * p)) :
    Err ≤ Δ * γ ^ 2 + rr * kn * γ := by
  have hXnn : (0 : ℝ) ≤ Dn ^ 2 * p ^ 2 + kn * p :=
    add_nonneg (by positivity) (mul_nonneg hkn0 hp0.le)
  have hC : (rr - 1) * (rr - 2) ≤ rr ^ 2 := by linarith only [hR2]
  have h1 : Err ≤ Dn * rr ^ 2 * (Dn ^ 2 * p ^ 2 + kn * p) := by
    rw [hErrdef]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC hDn0) hXnn
  have h2 : Dn * rr ^ 2 * (Dn ^ 2 * p ^ 2 + kn * p)
      = Dn * (rr * Dn * p) ^ 2 + rr * kn * (rr * Dn * p) := by ring
  rw [h2, hpγ] at h1
  linarith only [h1, mul_le_mul_of_nonneg_right hDn_le (sq_nonneg γ)]

/-- **The codegree share of the tolerance budget.**  At `κ ≤ θε²γα²D/(8192r)` the codegree term
`rκγ` of the ceiling drop uses at most a `1/32` of the budget `εγΔ`. -/
theorem sharp_codegree_tolerance_le {rr γ ε θ α Δ Dn kn : ℝ} (hR0 : 0 < rr) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1 / 2) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hα0 : 0 < α)
    (hα1 : α ≤ 1) (hDn0 : 0 ≤ Dn) (hDn_le : Dn ≤ Δ)
    (hkn3 : kn ≤ θ * ε ^ 2 * γ * α ^ 2 * Dn / (8192 * rr)) :
    rr * kn * γ ≤ ε * γ * Δ / 32 := by
  have s1 : rr * kn * γ ≤ rr * (θ * ε ^ 2 * γ * α ^ 2 * Dn / (8192 * rr)) * γ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkn3 hR0.le) hγ0.le
  have s2 : rr * (θ * ε ^ 2 * γ * α ^ 2 * Dn / (8192 * rr)) * γ
      = θ * ε ^ 2 * γ ^ 2 * α ^ 2 * Dn / 8192 := by field_simp
  rw [s2] at s1
  have hεγΔ : (0 : ℝ) ≤ ε * γ * Δ :=
    mul_nonneg (mul_nonneg hε0.le hγ0.le) (le_trans hDn0 hDn_le)
  have c0 : θ * α ^ 2 ≤ 1 := by nlinarith only [hθ0.le, hθ1, hα0.le, hα1]
  have c2 : (ε * γ) ^ 2 ≤ ε * γ := by
    nlinarith only [mul_nonneg hε0.le hγ0.le,
      mul_le_mul hε1 hγ1 hγ0.le (by norm_num : (0:ℝ) ≤ 1)]
  have c1 : θ * ε ^ 2 * γ ^ 2 * α ^ 2 ≤ ε * γ := by
    linarith only [mul_le_mul_of_nonneg_right c0 (show (0 : ℝ) ≤ (ε * γ) ^ 2 by positivity), c2]
  have b1 : θ * ε ^ 2 * γ ^ 2 * α ^ 2 * Dn ≤ ε * γ * Δ :=
    mul_le_mul c1 hDn_le hDn0 (by positivity)
  linarith only [s1, b1, hεγΔ]

/-- **The ceiling clause of the round, in arithmetic form.** The mean ceiling `Dn − Sγ(dn−l)d + Err`
produced by the Chebyshev band, plus the tolerance `t`, still fits below the requested ceiling
`Δ − Sγ(δ−l)c + εγΔ`, where `c = δ(1−γ)/Δ` is the requested relative drop and `d = dn·L/Dn` the
achieved one: the five error terms use `1/2 + 1/4 + 1/16 + 1/32 + 1/32 < 1` of the budget. -/
theorem sharp_ceiling_clause_arith {S γ ε δ dn Δ Dn l c d Err t x e : ℝ}
    (hSnn : 0 ≤ S) (hS1 : S ≤ 1) (hγ0 : 0 < γ) (hΔ0 : 0 < Δ) (hδ2 : 2 ≤ δ) (hδdn : δ ≤ dn)
    (hlΔ : l ≤ Δ) (hcd : c ≤ d) (hd0 : 0 ≤ d) (hΔc : Δ * c = δ * (1 - γ))
    (hΔd : Δ * d ≤ δ * (1 - γ) + γ ^ 2 * Δ + 3) (hDn_le : Dn ≤ Δ)
    (hb2 : x ≤ Dn - S * γ * ((dn - l) * d) + Err + t)
    (hErrle : Err ≤ Δ * γ ^ 2 + e) (ht2 : t ≤ ε * γ * Δ / 16) (hg2 : Δ * γ ^ 2 ≤ ε * γ * Δ / 2)
    (hg3 : γ * (γ ^ 2 * Δ) ≤ ε * γ * Δ / 4) (hg4 : 3 * γ ≤ ε * γ * Δ / 32)
    (he : e ≤ ε * γ * Δ / 32) (hεγΔ : 0 ≤ ε * γ * Δ) :
    x ≤ Δ - S * γ * ((δ - l) * c) + ε * γ * Δ := by
  have hΔdc : Δ * (d - c) ≤ γ ^ 2 * Δ + 3 := by linarith only [hΔd, hΔc]
  have hbr : (δ - l) * c - (dn - l) * d ≤ Δ * (d - c) := by
    have hid : Δ * (d - c) - ((δ - l) * c - (dn - l) * d)
        = (d - c) * (Δ + δ - l) + (dn - δ) * d := by ring
    have q1 : (0 : ℝ) ≤ (d - c) * (Δ + δ - l) :=
      mul_nonneg (by linarith only [hcd]) (by linarith only [hlΔ, hδ2])
    have q2 : (0 : ℝ) ≤ (dn - δ) * d := mul_nonneg (by linarith only [hδdn]) hd0
    linarith only [hid, q1, q2]
  have hγΔ3 : (0 : ℝ) ≤ γ ^ 2 * Δ + 3 := by
    linarith only [mul_nonneg (sq_nonneg γ) hΔ0.le]
  have hSbr : S * γ * ((δ - l) * c) - S * γ * ((dn - l) * d) ≤ γ * (γ ^ 2 * Δ) + 3 * γ := by
    have hbr2 : (δ - l) * c - (dn - l) * d ≤ γ ^ 2 * Δ + 3 := le_trans hbr hΔdc
    rcases le_or_gt 0 ((δ - l) * c - (dn - l) * d) with h | h
    · linarith only [mul_nonneg hγ0.le (sub_nonneg.mpr hbr2),
        mul_nonneg (mul_nonneg hγ0.le h) (sub_nonneg.mpr hS1)]
    · linarith only [mul_nonneg (mul_nonneg hSnn hγ0.le)
        (show (0 : ℝ) ≤ -((δ - l) * c - (dn - l) * d) by linarith only [h]),
        mul_nonneg hγ0.le hγΔ3]
  linarith only [hb2, hSbr, hErrle, ht2, hg2, hg3, hg4, he, hDn_le, hεγΔ]

/-- The numeric smallness condition consumed by
`LeanPool.AsymptoticTrianglePacking.Internal.exists_sharp_round_band`, at the
parameters of `LeanPool.AsymptoticTrianglePacking.Internal.sharpRoundFor_of_two_gamma_le_eps`
(tolerance `t = εγDn/16`, codegree
`kn ≤ θε²γα²Dn/(8192r)`). -/
theorem sharp_smallness_numeric (r : ℕ) (hr2 : 2 ≤ r) (γ ε θ α N Dn dn kn Ac p L t : ℝ)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hN256' : 256 * (r : ℝ) ≤ N * (α ^ 2 * γ)) (hN4 : 4 ≤ N)
    (hDn3 : 3 ≤ Dn) (hdnhalf : Dn / 2 ≤ dn) (hkn0 : 0 ≤ kn)
    (hkn3 : kn ≤ θ * ε ^ 2 * γ * α ^ 2 * Dn / (8192 * (r : ℝ)))
    (hp0 : 0 < p) (hpγ : (r : ℝ) * Dn * p = γ) (hLhalf : 1 / 2 ≤ L)
    (htdef : t = ε * γ * Dn / 16) (hAN : α * N ≤ Ac) :
    (N * ((2 * p * ((r : ℝ) ^ 2 * kn * Dn ^ 2)
          * (1 + p * (r : ℝ) * Dn + (p * (r : ℝ) * Dn) ^ 2)) / t ^ 2)) / (θ * N)
      + (N * (Dn * p) + N ^ 2 * (kn * p + 4 * (r : ℝ) ^ 2 * kn * Dn ^ 2 * p ^ 3))
        / (Ac * (dn * (p * L)) / 2) ^ 2 < 1 := by
  have hR2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
  have hR0 : (0 : ℝ) < (r : ℝ) := by linarith only [hR2]
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hR0
  have hDnpos : (0 : ℝ) < Dn := by linarith only [hDn3]
  have hNpos : (0 : ℝ) < N := by linarith only [hN4]
  have hAcpos : (0 : ℝ) < Ac := lt_of_lt_of_le (mul_pos hα0 hNpos) hAN
  have hLpos : (0 : ℝ) < L := by linarith only [hLhalf]
  have ht0 : 0 < t := by rw [htdef]; positivity
  have hprd : p * (r : ℝ) * Dn = γ := by rw [← hpγ]; ring
  have e1 : Dn * p = γ / (r : ℝ) := by
    rw [eq_div_iff hrne, ← hpγ]; ring
  -- the cover rate
  have hkey : γ / (8 * (r : ℝ)) ≤ dn * (p * L) / 2 :=
    sharp_cover_rate_le hR0 hDnpos hdnhalf hLhalf hp0 hpγ
  have hQ2ge : α * N * γ / (8 * (r : ℝ)) ≤ Ac * (dn * (p * L)) / 2 := by
    have s1 : Ac * (γ / (8 * (r : ℝ))) ≤ Ac * (dn * (p * L) / 2) :=
      mul_le_mul_of_nonneg_left hkey hAcpos.le
    have s2 : α * N * (γ / (8 * (r : ℝ))) ≤ Ac * (γ / (8 * (r : ℝ))) :=
      mul_le_mul_of_nonneg_right hAN (by positivity)
    have q1 : α * N * γ / (8 * (r : ℝ)) = α * N * (γ / (8 * (r : ℝ))) := by ring
    have q2 : Ac * (dn * (p * L) / 2) = Ac * (dn * (p * L)) / 2 := by ring
    rw [q1, ← q2]; linarith only [s1, s2]
  -- Chebyshev term
  have hVs_le : 2 * p * ((r : ℝ) ^ 2 * kn * Dn ^ 2)
        * (1 + p * (r : ℝ) * Dn + (p * (r : ℝ) * Dn) ^ 2)
      ≤ 4 * γ * (r : ℝ) * kn * Dn := by
    rw [hprd, show 2 * p * ((r : ℝ) ^ 2 * kn * Dn ^ 2)
        = 2 * kn * Dn * (r : ℝ) * ((r : ℝ) * Dn * p) by ring, hpγ]
    linarith only [mul_le_mul_of_nonneg_left
      (show 1 + γ + γ ^ 2 ≤ 2 by
        linarith only [hγ1, mul_nonneg hγ0.le (show (0 : ℝ) ≤ 1 / 2 - γ by linarith only [hγ1])])
      (show (0 : ℝ) ≤ 2 * kn * Dn * (r : ℝ) * γ by positivity)]
  have hVt : (2 * p * ((r : ℝ) ^ 2 * kn * Dn ^ 2)
        * (1 + p * (r : ℝ) * Dn + (p * (r : ℝ) * Dn) ^ 2)) / t ^ 2 ≤ θ / 4 := by
    rw [div_le_iff₀ (by positivity), htdef,
      show (ε * γ * Dn / 16) ^ 2 = ε ^ 2 * γ ^ 2 * Dn ^ 2 / 256 by ring]
    refine le_trans hVs_le ?_
    have hstep : 4 * γ * (r : ℝ) * kn * Dn
        ≤ 4 * γ * (r : ℝ) * (θ * ε ^ 2 * γ * α ^ 2 * Dn / (8192 * (r : ℝ))) * Dn :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkn3 (by positivity)) hDnpos.le
    refine le_trans hstep ?_
    rw [show 4 * γ * (r : ℝ) * (θ * ε ^ 2 * γ * α ^ 2 * Dn / (8192 * (r : ℝ))) * Dn
        = θ * ε ^ 2 * γ ^ 2 * α ^ 2 * Dn ^ 2 / 2048 by field_simp; ring]
    linarith only [mul_le_mul_of_nonneg_left
        (show α ^ 2 ≤ 1 by nlinarith only [hα0.le, hα1])
        (show (0 : ℝ) ≤ θ * ε ^ 2 * γ ^ 2 * Dn ^ 2 by positivity),
      show (0 : ℝ) ≤ θ * ε ^ 2 * γ ^ 2 * Dn ^ 2 by positivity]
  have hT1 : (N * ((2 * p * ((r : ℝ) ^ 2 * kn * Dn ^ 2)
          * (1 + p * (r : ℝ) * Dn + (p * (r : ℝ) * Dn) ^ 2)) / t ^ 2)) / (θ * N) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    linarith only [mul_le_mul_of_nonneg_left hVt hNpos.le]
  -- cover-variance term
  have e3 : 4 * (r : ℝ) ^ 2 * kn * Dn ^ 2 * p ^ 3 = 4 * γ ^ 2 * (kn * p) := by
    rw [← hpγ]; ring
  have hknp : kn * p ≤ θ * ε ^ 2 * γ ^ 2 * α ^ 2 / (8192 * (r : ℝ) ^ 2) := by
    calc kn * p ≤ (θ * ε ^ 2 * γ * α ^ 2 * Dn / (8192 * (r : ℝ))) * p :=
          mul_le_mul_of_nonneg_right hkn3 hp0.le
      _ = θ * ε ^ 2 * γ * α ^ 2 * (Dn * p) / (8192 * (r : ℝ)) := by ring
      _ = θ * ε ^ 2 * γ ^ 2 * α ^ 2 / (8192 * (r : ℝ) ^ 2) := by rw [e1]; field_simp
  rw [le_div_iff₀ (by positivity)] at hknp
  have hknp0 : (0 : ℝ) ≤ kn * p := mul_nonneg hkn0 hp0.le
  have hA1 : N * (Dn * p) ≤ α ^ 2 * N ^ 2 * γ ^ 2 / (256 * (r : ℝ) ^ 2) := by
    rw [e1, le_div_iff₀ (by positivity),
      show N * (γ / (r : ℝ)) * (256 * (r : ℝ) ^ 2) = 256 * (r : ℝ) * (N * γ) by
        field_simp]
    linarith only [mul_le_mul_of_nonneg_right hN256' (show (0 : ℝ) ≤ N * γ by positivity)]
  have hA2 : 2 * N ^ 2 * (kn * p) ≤ α ^ 2 * N ^ 2 * γ ^ 2 / (256 * (r : ℝ) ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    linarith only [mul_le_mul_of_nonneg_left hknp (show (0 : ℝ) ≤ N ^ 2 by positivity),
      mul_le_mul_of_nonneg_left
        (show θ * ε ^ 2 ≤ 1 by nlinarith only [hθ0.le, hθ1, hε0.le, hε1])
        (show (0 : ℝ) ≤ N ^ 2 * γ ^ 2 * α ^ 2 by positivity),
      show (0 : ℝ) ≤ α ^ 2 * N ^ 2 * γ ^ 2 by positivity]
  have hnum : N * (Dn * p) + N ^ 2 * (kn * p + 4 * (r : ℝ) ^ 2 * kn * Dn ^ 2 * p ^ 3)
      ≤ α ^ 2 * N ^ 2 * γ ^ 2 / (128 * (r : ℝ) ^ 2) := by
    rw [e3]
    have hmid : N ^ 2 * (kn * p + 4 * γ ^ 2 * (kn * p)) ≤ 2 * N ^ 2 * (kn * p) := by
      linarith only [mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ N ^ 2 by positivity) hknp0)
        (show (0 : ℝ) ≤ 1 - 4 * γ ^ 2 by nlinarith only [hγ0.le, hγ1])]
    have hsplit : α ^ 2 * N ^ 2 * γ ^ 2 / (256 * (r : ℝ) ^ 2)
        + α ^ 2 * N ^ 2 * γ ^ 2 / (256 * (r : ℝ) ^ 2)
        = α ^ 2 * N ^ 2 * γ ^ 2 / (128 * (r : ℝ) ^ 2) := by ring
    linarith only [hA1, hA2, hmid, hsplit]
  have hQ2pos : (0 : ℝ) < Ac * (dn * (p * L)) / 2 :=
    lt_of_lt_of_le (by positivity) hQ2ge
  have hQ2sq : α ^ 2 * N ^ 2 * γ ^ 2 / (64 * (r : ℝ) ^ 2) ≤ (Ac * (dn * (p * L)) / 2) ^ 2 := by
    have hsq := mul_self_le_mul_self
      (show (0 : ℝ) ≤ α * N * γ / (8 * (r : ℝ)) by positivity) hQ2ge
    calc α ^ 2 * N ^ 2 * γ ^ 2 / (64 * (r : ℝ) ^ 2)
        = (α * N * γ / (8 * (r : ℝ))) * (α * N * γ / (8 * (r : ℝ))) := by field_simp; ring
      _ ≤ (Ac * (dn * (p * L)) / 2) * (Ac * (dn * (p * L)) / 2) := hsq
      _ = (Ac * (dn * (p * L)) / 2) ^ 2 := (pow_two _).symm
  have hT2 : (N * (Dn * p) + N ^ 2 * (kn * p + 4 * (r : ℝ) ^ 2 * kn * Dn ^ 2 * p ^ 3))
        / (Ac * (dn * (p * L)) / 2) ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have hd : α ^ 2 * N ^ 2 * γ ^ 2 / (128 * (r : ℝ) ^ 2)
        = (1 / 2) * (α ^ 2 * N ^ 2 * γ ^ 2 / (64 * (r : ℝ) ^ 2)) := by ring
    linarith only [hnum, hQ2sq, hd]
  linarith only [hT1, hT2]

/-- **The sharp LeanPool.AsymptoticTrianglePacking.Internal round, assembled**, in the regime `2γ ≤
ε` — the regime the tight-band
schedule `LeanPool.AsymptoticTrianglePacking.Internal.exists_tightParams` actually uses (`ε =
4((r−1)/r)γ ≥ 2γ`). -/
theorem sharpRoundFor_of_two_gamma_le_eps (r : ℕ) (hr2 : 2 ≤ r) (γ ε θ α : ℝ)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hε1 : ε ≤ 1) (hγε : 2 * γ ≤ ε)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    SharpRoundFor r γ ε θ α (256 * r / (α ^ 2 * γ) + 96 / ε + 4)
      (θ * ε ^ 2 * γ * α ^ 2 / (16384 * r)) := by
  classical
  have hε0 : 0 < ε := by linarith only [hγ0, hγε]
  have hR2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
  have hR0 : (0 : ℝ) < (r : ℝ) := by linarith only [hR2]
  set c₀ : ℝ := θ * ε ^ 2 * γ * α ^ 2 / (16384 * r) with hc₀def
  have hc₀0 : 0 < c₀ := by rw [hc₀def]; positivity
  intro V _ _ K A δ Δ κ hr hΔle hδA hκle hκ0 hκc hDΔ hΔδ hDN hAN
  set N : ℝ := (Fintype.card V : ℝ) with hNdef
  -- threshold consequences
  have hpos1 : (0 : ℝ) < 256 * (r : ℝ) / (α ^ 2 * γ) := by positivity
  have hpos2 : (0 : ℝ) < 96 / ε := by positivity
  have hΔ4 : (4 : ℝ) ≤ Δ := by linarith only [hDΔ, hpos1, hpos2]
  have hN4 : (4 : ℝ) ≤ N := by linarith only [hDN, hpos1, hpos2]
  have hΔ96 : 96 / ε ≤ Δ := by linarith only [hDΔ, hpos1]
  have hN256 : 256 * (r : ℝ) / (α ^ 2 * γ) ≤ N := by linarith only [hDN, hpos2]
  have hN256' : 256 * (r : ℝ) ≤ N * (α ^ 2 * γ) := by
    rw [div_le_iff₀ (by positivity)] at hN256; linarith only [hN256]
  -- integer versions of the parameters
  set Δn : ℕ := ⌊Δ⌋₊ with hΔndef
  set δn : ℕ := ⌈δ⌉₊ with hδndef
  set κn : ℕ := ⌊κ⌋₊ with hκndef
  have hDn_le : (Δn : ℝ) ≤ Δ := Nat.floor_le (by linarith)
  have hDn_gt : Δ < (Δn : ℝ) + 1 := Nat.lt_floor_add_one Δ
  have hδ_le_dn : δ ≤ (δn : ℝ) := Nat.le_ceil δ
  have hδ2 : (2 : ℝ) ≤ δ := by linarith only [hΔδ, hΔ4]
  have hdn_lt : (δn : ℝ) < δ + 1 := Nat.ceil_lt_add_one (by linarith)
  have hkn_le : (κn : ℝ) ≤ κ := Nat.floor_le hκ0
  have hkn0 : (0 : ℝ) ≤ (κn : ℝ) := Nat.cast_nonneg _
  have hΔnat : ∀ v : V, degree K v ≤ Δn := fun v => Nat.le_floor (hΔle v)
  have hδnat : ∀ v ∈ A, δn ≤ degree K v := fun v hv => Nat.ceil_le.mpr (hδA v hv)
  have hκnat : ∀ x y : V, x ≠ y → codegree K x y ≤ κn := fun x y h => Nat.le_floor (hκle x y h)
  have hΔn3 : 3 ≤ Δn := Nat.le_floor (by push_cast; linarith)
  have hDn3 : (3 : ℝ) ≤ (Δn : ℝ) := by exact_mod_cast hΔn3
  have hDnpos : (0 : ℝ) < (Δn : ℝ) := by linarith only [hDn3]
  -- the active set is nonempty
  have hAc0 : (0 : ℝ) < (A.card : ℝ) :=
    lt_of_lt_of_le (mul_pos hα0 (by linarith : (0 : ℝ) < N)) hAN
  have hAcardN : 0 < A.card := by exact_mod_cast hAc0
  obtain ⟨v0, hv0⟩ := Finset.card_pos.mp hAcardN
  have hdn_le_Dn : δn ≤ Δn := le_trans (hδnat v0 hv0) (hΔnat v0)
  have hdnDn : (δn : ℝ) ≤ (Δn : ℝ) := by exact_mod_cast hdn_le_Dn
  have hdnΔ : (δn : ℝ) ≤ Δ := le_trans hdnDn hDn_le
  have hδ_le_Δ : δ ≤ Δ := le_trans hδ_le_dn hdnΔ
  have hdn1 : 0 < δn := by
    have : (0 : ℝ) < (δn : ℝ) := by linarith only [hδ_le_dn, hδ2]
    exact_mod_cast this
  -- the retention
  set p : ℝ := γ / ((r : ℝ) * (Δn : ℝ)) with hpdef
  have hp0 : 0 < p := by rw [hpdef]; positivity
  have hpγ : (r : ℝ) * (Δn : ℝ) * p = γ := by rw [hpdef]; field_simp
  have hp1 : p < 1 := by
    rw [hpdef, div_lt_one (by positivity)]
    nlinarith only [hγ1, hγ0.le, hR2, hDn3]
  set L : ℝ := (1 - p) ^ (r * Δn) with hLdef
  have hLbounds := sharp_survival_bounds (m := r * Δn) (γ := γ) hp0.le hp1.le
    (by push_cast; exact hpγ)
  have hLge : 1 - γ ≤ L := by rw [hLdef]; exact hLbounds.1
  have hLu : L ≤ 1 - γ + γ ^ 2 / 2 := by rw [hLdef]; exact hLbounds.2
  have hLle : L ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hLpos : (0 : ℝ) < L := pow_pos (by linarith) _
  -- the band parameters
  set t : ℝ := ε * γ * (Δn : ℝ) / 16 with htdef
  have ht0 : 0 < t := by rw [htdef]; positivity
  set S : ℝ := ((r : ℝ) - 1) / (r : ℝ) with hSdef
  have hSnn : (0 : ℝ) ≤ S := by rw [hSdef]; apply div_nonneg <;> linarith
  have hS1 : S ≤ 1 := by rw [hSdef, div_le_one hR0]; linarith
  set mlo : ℝ := (δn : ℝ) * (1 - ((r : ℝ) - 1) * ((Δn : ℝ) * p)) with hmlodef
  set Err : ℝ :=
    (Δn : ℝ) * (((r : ℝ) - 1) * ((r : ℝ) - 2)) * ((Δn : ℝ) ^ 2 * p ^ 2 + (κn : ℝ) * p) with hErrdef
  set mhi : V → ℝ := fun v =>
    (Δn : ℝ) - ((δn : ℝ) - (lostDegree K Aᶜ v : ℝ)) * (((r : ℝ) - 1) * (δn : ℝ) * (p * L))
      + Err with hmhidef
  clear_value mhi Err mlo S t L p κn δn Δn c₀
  -- the mean estimates
  have hlo : ∀ v ∈ A, mlo ≤ Cube.Exp p (safeDegCube K v) := by
    intro v hv
    refine le_trans ?_ (Exp_safeDegCube_ge hp0.le hp1.le (by omega) hr hΔnat v)
    have hd : (δn : ℝ) ≤ (degree K v : ℝ) := by exact_mod_cast hδnat v hv
    have hfac : (0 : ℝ) ≤ 1 - ((r : ℝ) - 1) * ((Δn : ℝ) * p) := by
      have : (Δn : ℝ) * p = γ / (r : ℝ) := by rw [hpdef]; field_simp
      rw [this, show ((r : ℝ) - 1) * (γ / (r : ℝ)) = ((r : ℝ) - 1) * γ / (r : ℝ) by ring,
        sub_nonneg, div_le_one hR0]
      linarith only [hR0,
        mul_le_mul_of_nonneg_left hγ1 (show (0:ℝ) ≤ (r:ℝ) - 1 by linarith only [hR2])]
    rw [hmlodef]
    exact mul_le_mul_of_nonneg_right hd hfac
  have hhi : ∀ v ∈ A, Cube.Exp p (safeDegCube K v) ≤ mhi v := by
    intro v hv
    refine le_trans (Exp_safeDegCube_le A hp0.le hp1.le hr2 hr hΔnat hδnat hκnat v) ?_
    rw [← hLdef, hmhidef, hErrdef]
    simp only
    exact sharp_mean_ceiling_arith
      (mul_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) (mul_nonneg hp0.le hLpos.le))
      (by nlinarith only [hR2])
      (add_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) hp0.le))
      (by exact_mod_cast hΔnat v) (by exact_mod_cast hδnat v hv)
  -- codegree bound in integer form
  have hkn3 : (κn : ℝ) ≤ θ * ε ^ 2 * γ * α ^ 2 * (Δn : ℝ) / (8192 * (r : ℝ)) := by
    have hΔ2Dn : Δ ≤ 2 * (Δn : ℝ) := by linarith
    have : (κn : ℝ) ≤ c₀ * (2 * (Δn : ℝ)) := by
      refine le_trans hkn_le (le_trans hκc ?_)
      exact mul_le_mul_of_nonneg_left hΔ2Dn hc₀0.le
    rw [hc₀def] at this
    calc (κn : ℝ) ≤ θ * ε ^ 2 * γ * α ^ 2 / (16384 * (r : ℝ)) * (2 * (Δn : ℝ)) := this
      _ = θ * ε ^ 2 * γ * α ^ 2 * (Δn : ℝ) / (8192 * (r : ℝ)) := by field_simp; ring
  -- the cover rate on the active set
  have hkey : γ / (8 * (r : ℝ)) ≤ (δn : ℝ) * (p * L) / 2 :=
    sharp_cover_rate_le hR0 hDnpos (by linarith) (by linarith) hp0 hpγ
  -- the smallness condition
  have hsmall :
      (N * ((2 * p * ((r : ℝ) ^ 2 * (κn : ℝ) * (Δn : ℝ) ^ 2)
            * (1 + p * (r : ℝ) * (Δn : ℝ) + (p * (r : ℝ) * (Δn : ℝ)) ^ 2)) / t ^ 2)) / (θ * N)
        + (N * ((Δn : ℝ) * p)
            + N ^ 2 * ((κn : ℝ) * p + 4 * (r : ℝ) ^ 2 * (κn : ℝ) * (Δn : ℝ) ^ 2 * p ^ 3))
          / ((A.card : ℝ) * ((δn : ℝ) * (p * (1 - p) ^ (r * Δn))) / 2) ^ 2 < 1 := by
    rw [← hLdef]
    exact sharp_smallness_numeric r hr2 γ ε θ α N (Δn : ℝ) (δn : ℝ) (κn : ℝ) (A.card : ℝ) p L t
      hγ0 hγ1 hε0 hε1 hθ0 hθ1 hα0 hα1 hN256' hN4 hDn3 (by linarith) hkn0 hkn3 hp0 hpγ
      (by linarith) htdef hAN
  obtain ⟨R', hR'sub, B, hBcard, hband, hcov⟩ :=
    exists_sharp_round_band (K := K) A (r := r) (Δ := Δn) (δ := δn) (κ := κn)
      (p := p) (t := t) (a := θ * N) (mlo := mlo) (mhi := mhi)
      hp0 hp1 (by omega) hr hΔnat hδnat hκnat ht0 (by positivity) hdn1 hAcardN hlo hhi hsmall
  have hΔpos : (0 : ℝ) < Δ := by linarith
  have hεΔ : (96 : ℝ) ≤ ε * Δ := by rw [div_le_iff₀ hε0] at hΔ96; linarith
  have ht2 : t ≤ ε * γ * Δ / 16 := by
    rw [htdef]
    linarith only [mul_le_mul_of_nonneg_left hDn_le (show (0 : ℝ) ≤ ε * γ by positivity)]
  -- the four pieces of the tolerance budget `εγΔ`
  have hg2 : Δ * γ ^ 2 ≤ ε * γ * Δ / 2 := by
    linarith only [mul_le_mul_of_nonneg_right hγε (mul_nonneg hγ0.le hΔpos.le)]
  have hg3 : γ * (γ ^ 2 * Δ) ≤ ε * γ * Δ / 4 := by
    linarith only [mul_le_mul_of_nonneg_left hg2 hγ0.le,
      mul_le_mul_of_nonneg_right hγ1 (show (0 : ℝ) ≤ ε * γ * Δ by positivity)]
  have hg4 : 3 * γ ≤ ε * γ * Δ / 32 := by
    linarith only [mul_le_mul_of_nonneg_left hεΔ hγ0.le]
  have hkn4 : (r : ℝ) * (κn : ℝ) * γ ≤ ε * γ * Δ / 32 :=
    sharp_codegree_tolerance_le hR0 hγ0 hγ1 hε0 hε1 hθ0 hθ1 hα0 hα1 (Nat.cast_nonneg _) hDn_le hkn3
  refine ⟨R', hR'sub, B, hBcard.le, ?_, ?_⟩
  · intro v hvA hvB hvc
    obtain ⟨hb1, hb2⟩ := hband v hvA hvB hvc
    have hDp : (Δn : ℝ) * p = γ / (r : ℝ) := by rw [hpdef]; field_simp
    constructor
    · have hmloeq : mlo = (δn : ℝ) - (δn : ℝ) * S * γ := by
        rw [hmlodef, hSdef, hDp]; field_simp; try ring
      have h1 : (δn : ℝ) * S * γ ≤ S * γ * Δ := by
        have h := mul_le_mul_of_nonneg_left hdnΔ (mul_nonneg hSnn hγ0.le)
        linarith only [h]
      linarith only [hb1, hδ_le_dn, hmloeq, h1, ht2,
        mul_nonneg (mul_nonneg hε0.le hγ0.le) hΔpos.le]
    · simp only [hmhidef] at hb2
      set lo : ℝ := (lostDegree K Aᶜ v : ℝ) with hlodef
      have hlo0 : (0 : ℝ) ≤ lo := Nat.cast_nonneg _
      have hloΔ : lo ≤ Δ := by
        have h' : (lostDegree K Aᶜ v : ℝ) ≤ (degree K v : ℝ) := by
          exact_mod_cast lostDegree_le_degree K Aᶜ v
        have h'' := hΔle v
        rw [hlodef]
        linarith only [h', h'']
      clear_value lo
      set c : ℝ := δ * (1 - γ) / Δ with hcdef
      set d : ℝ := (δn : ℝ) * L / (Δn : ℝ) with hddef
      have hdnLnn : (0 : ℝ) ≤ (δn : ℝ) * L := mul_nonneg (Nat.cast_nonneg _) hLpos.le
      have hc0 : (0 : ℝ) ≤ c :=
        div_nonneg (mul_nonneg (by linarith only [hδ2]) (by linarith only [hγ1])) hΔpos.le
      have hcd : c ≤ d := by
        rw [hcdef, hddef, div_le_iff₀ hΔpos, div_mul_eq_mul_div, le_div_iff₀ hDnpos]
        have hnum : δ * (1 - γ) ≤ (δn : ℝ) * L :=
          mul_le_mul hδ_le_dn hLge (by linarith only [hγ1]) (Nat.cast_nonneg _)
        linarith only [mul_le_mul_of_nonneg_right hnum hDnpos.le,
          mul_le_mul_of_nonneg_left hDn_le hdnLnn]
      have hd0 : (0 : ℝ) ≤ d := le_trans hc0 hcd
      have hΔc : Δ * c = δ * (1 - γ) := by rw [hcdef]; field_simp
      have hΔd : Δ * d ≤ δ * (1 - γ) + γ ^ 2 * Δ + 3 := by
        rw [hddef]
        exact sharp_drop_ratio_le γ δ Δ (Δn : ℝ) (δn : ℝ) L hγ0 hγ1 hδ2 hδ_le_Δ hDn3 hDn_gt
          hδ_le_dn hdn_lt hLpos hLu
      clear_value c d
      have hDropT : S * γ * (δ - lo) * δ * (1 - γ) / Δ = S * γ * ((δ - lo) * c) := by
        rw [hcdef]; field_simp; try ring
      have hDropO : ((δn : ℝ) - lo) * (((r : ℝ) - 1) * (δn : ℝ) * (p * L))
          = S * γ * (((δn : ℝ) - lo) * d) := by
        rw [hddef, hSdef, hpdef]; field_simp; try ring
      have hErrle : Err ≤ Δ * γ ^ 2 + (r : ℝ) * (κn : ℝ) * γ :=
        sharp_bonferroni_error_le hR2 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hp0 hpγ hDn_le
          hErrdef
      rw [hDropT]
      rw [hDropO] at hb2
      exact sharp_ceiling_clause_arith hSnn hS1 hγ0 hΔpos hδ2 hδ_le_dn hloΔ hcd hd0 hΔc hΔd
        hDn_le hb2 hErrle ht2 hg2 hg3 hg4 hkn4
        (mul_nonneg (mul_nonneg hε0.le hγ0.le) hΔpos.le)
  · rw [← hLdef] at hcov
    have s1 : (A.card : ℝ) * (γ / (8 * (r : ℝ)))
        ≤ (A.card : ℝ) * ((δn : ℝ) * (p * L) / 2) := mul_le_mul_of_nonneg_left hkey hAc0.le
    have e2 : (A.card : ℝ) * ((δn : ℝ) * (p * L) / 2)
        = (A.card : ℝ) * ((δn : ℝ) * (p * L)) / 2 := by ring
    linarith only [hcov, s1, e2]

/-- **`LeanPool.AsymptoticTrianglePacking.Internal.SharpRoundHyp` in the regime `2γ ≤ ε`.**

This is exactly the body of `LeanPool.AsymptoticTrianglePacking.Internal.SharpRoundHyp` with the
extra hypothesis `2 * γ ≤ ε`; the
witnesses are `D₀ = 256r/(α²γ) + 96/ε + 4` and `c₀ = θε²γα²/(16384r)`.

The restriction is not an artefact of the bookkeeping: the mean safe degree of a vertex genuinely
carries a second-order term of size `Θ(γ²Δ)` (the pairs of neighbours of `v` inside a single edge
that are covered simultaneously), while `SharpRoundFor` allows an absolute error of only `εγΔ`.  So
some hypothesis of the form `γ = O(ε)` is necessary for a round built from the uniform retention
`p = γ/(rΔ)`. The constant `2` is below the schedule's own ratio:
`LeanPool.AsymptoticTrianglePacking.Internal.exists_tightParams`
sets `ε = 4((r−1)/r)γ ≥ 2γ`. -/
theorem sharpRoundHyp_of_two_gamma_le_eps (r : ℕ) (hr2 : 2 ≤ r) (γ ε θ α : ℝ)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hε1 : ε ≤ 1) (hγε : 2 * γ ≤ ε)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ D₀ : ℝ, 0 < D₀ ∧ ∃ c₀ : ℝ, 0 < c₀ ∧ SharpRoundFor r γ ε θ α D₀ c₀ := by
  have hε0 : 0 < ε := by linarith only [hγ0, hγε]
  have hR0 : (0 : ℝ) < (r : ℝ) := by
    have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
    linarith only [this]
  exact ⟨256 * r / (α ^ 2 * γ) + 96 / ε + 4, by positivity,
    θ * ε ^ 2 * γ * α ^ 2 / (16384 * r), by positivity,
    sharpRoundFor_of_two_gamma_le_eps r hr2 γ ε θ α hγ0 hγ1 hε1 hγε hθ0 hθ1 hα0 hα1⟩

/-- **`LeanPool.AsymptoticTrianglePacking.Internal.SharpRoundHyp` in the regime `8γ ≤ ε`**, a
special case of
`LeanPool.AsymptoticTrianglePacking.Internal.sharpRoundHyp_of_two_gamma_le_eps`. -/
theorem sharpRoundHyp_of_gamma_le_eps (r : ℕ) (hr2 : 2 ≤ r) (γ ε θ α : ℝ)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hε1 : ε ≤ 1) (hγε : 8 * γ ≤ ε)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ D₀ : ℝ, 0 < D₀ ∧ ∃ c₀ : ℝ, 0 < c₀ ∧ SharpRoundFor r γ ε θ α D₀ c₀ :=
  sharpRoundHyp_of_two_gamma_le_eps r hr2 γ ε θ α hγ0 hγ1 hε1 (by linarith) hθ0 hθ1 hα0 hα1

end LeanPool.AsymptoticTrianglePacking.Internal
