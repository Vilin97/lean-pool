/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

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
@[expose]
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
@[expose]
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
