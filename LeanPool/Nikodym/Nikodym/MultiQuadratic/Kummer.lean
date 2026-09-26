/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module


public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.Tactic

/-!
# Kummer independence of square roots (blueprint K01)

For pairwise coprime squarefree integers `r₁, …, rₘ > 1` the `2^m` real numbers
`√(∏_{j ∈ S} r_j)`, `S ⊆ [m]`, are linearly independent over `ℚ` (hence over `ℤ`).

We work with a `Finset ℕ` of radicands `s` and the `ℚ`-span `radSpan s` of the numbers
`sqrtProd T = √(∏_{x ∈ T} x)`, `T ⊆ s`. The strengthened induction hypothesis
`sqrt_notMem_radSpan` says that `√r ∉ radSpan s` whenever `r > 1` is squarefree and coprime to
every element of an admissible `s`; it is proved by `Finset.induction_on s`, quantifying over all
`r`. Linear independence (`sum_eq_zero_imp`) is then a second induction, and the `Fin m`-indexed
statements `linearIndependent_sqrt_prod`, `linearIndependent_sqrt_prod_int` and
`sum_intCast_mul_sqrt_prod_eq_zero` are obtained by reindexing.

## Main declarations

* `Nikodym.MultiQuad.linearIndependent_sqrt_prod`: blueprint K01 over `ℚ`.
* `Nikodym.MultiQuad.linearIndependent_sqrt_prod_int`: the same over `ℤ`.
* `Nikodym.MultiQuad.sum_intCast_mul_sqrt_prod_eq_zero`: the coefficient form over `ℤ`.
-/

@[expose] public section

open Finset

namespace Nikodym.MultiQuad

/-- Blueprint K01 (auxiliary): the real number `√(∏_{x ∈ T} x)` for a finset of naturals. -/
noncomputable def sqrtProd (T : Finset ℕ) : ℝ := Real.sqrt (∏ x ∈ T, (x : ℝ))

/-- Blueprint K01 (auxiliary): the `ℚ`-span `L s` of the numbers `√(∏ T)`, `T ⊆ s`. -/
noncomputable def radSpan (s : Finset ℕ) : Submodule ℚ ℝ :=
  Submodule.span ℚ (sqrtProd '' (s.powerset : Set (Finset ℕ)))

/-- Blueprint K01 (auxiliary): a finset of radicands is admissible if its elements are `> 1`,
squarefree and pairwise coprime. -/
structure Admissible (s : Finset ℕ) : Prop where
  one_lt : ∀ a ∈ s, 1 < a
  squarefree : ∀ a ∈ s, Squarefree a
  coprime : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Nat.Coprime a b

/-- Blueprint K01 (auxiliary): admissibility passes to subsets. -/
theorem Admissible.mono {s t : Finset ℕ} (hts : t ⊆ s) (hs : Admissible s) : Admissible t :=
  ⟨fun a ha ↦ hs.one_lt a (hts ha), fun a ha ↦ hs.squarefree a (hts ha),
    fun a ha b hb hab ↦ hs.coprime a (hts ha) b (hts hb) hab⟩

/-! ### Elementary facts about `sqrtProd` -/

/-- Blueprint K01 (auxiliary). -/
theorem sqrtProd_empty : sqrtProd ∅ = 1 := by simp [sqrtProd]

/-- Blueprint K01 (auxiliary). -/
theorem sqrtProd_singleton (p : ℕ) : sqrtProd {p} = Real.sqrt p := by simp [sqrtProd]

/-- Blueprint K01 (auxiliary). -/
theorem sqrtProd_insert {p : ℕ} {T : Finset ℕ} (hp : p ∉ T) :
    sqrtProd (insert p T) = Real.sqrt p * sqrtProd T := by
  rw [sqrtProd, sqrtProd, prod_insert hp, Real.sqrt_mul (Nat.cast_nonneg _)]

/-- Blueprint K01 (auxiliary): `√r_S √r_T = r_{S ∩ T} √r_{S Δ T}`. -/
theorem sqrtProd_mul (S T : Finset ℕ) :
    sqrtProd S * sqrtProd T =
      (∏ x ∈ S ∩ T, (x : ℝ)) * sqrtProd ((S ∪ T) \ (S ∩ T)) := by
  have hnn : ∀ U : Finset ℕ, 0 ≤ ∏ x ∈ U, (x : ℝ) := fun U ↦
    prod_nonneg fun x _ ↦ Nat.cast_nonneg x
  rw [sqrtProd, sqrtProd, sqrtProd, ← Real.sqrt_mul (hnn S)]
  have : (∏ x ∈ S, (x : ℝ)) * ∏ x ∈ T, (x : ℝ) =
      (∏ x ∈ S ∩ T, (x : ℝ)) ^ 2 * ∏ x ∈ (S ∪ T) \ (S ∩ T), (x : ℝ) := by
    rw [← prod_union_inter, ← prod_sdiff (inter_subset_union (s := S) (t := T)), sq]
    ring
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hnn _)]

/-! ### The span `radSpan s` -/

/-- Blueprint K01 (auxiliary). -/
theorem sqrtProd_mem_radSpan {s T : Finset ℕ} (hT : T ⊆ s) : sqrtProd T ∈ radSpan s :=
  Submodule.subset_span ⟨T, by simpa using hT, rfl⟩

/-- Blueprint K01 (auxiliary). -/
theorem one_mem_radSpan (s : Finset ℕ) : (1 : ℝ) ∈ radSpan s :=
  sqrtProd_empty ▸ sqrtProd_mem_radSpan (empty_subset s)

/-- Blueprint K01 (auxiliary). -/
theorem radSpan_mono {s t : Finset ℕ} (hts : t ⊆ s) : radSpan t ≤ radSpan s :=
  Submodule.span_mono (Set.image_mono (coe_subset.2 (powerset_mono.2 hts)))

/-- Blueprint K01 (auxiliary). -/
theorem natCast_mem_radSpan (s : Finset ℕ) (n : ℕ) : (n : ℝ) ∈ radSpan s := by
  have := (radSpan s).smul_mem (n : ℚ) (one_mem_radSpan s)
  simpa [Rat.smul_def] using this

/-- Blueprint K01 (auxiliary). -/
theorem ratCast_mul_mem_radSpan {s : Finset ℕ} (q : ℚ) {x : ℝ} (hx : x ∈ radSpan s) :
    (q : ℝ) * x ∈ radSpan s := by
  have := (radSpan s).smul_mem q hx
  simpa [Rat.smul_def] using this

/-- Blueprint K01 (auxiliary): `radSpan s` is closed under multiplication. -/
theorem mul_mem_radSpan {s : Finset ℕ} {x y : ℝ} (hx : x ∈ radSpan s) (hy : y ∈ radSpan s) :
    x * y ∈ radSpan s := by
  have hle : radSpan s * radSpan s ≤ radSpan s := by
    rw [radSpan, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨S, hS, rfl⟩, _, ⟨T, hT, rfl⟩, rfl⟩
    simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset] at hS hT
    change sqrtProd S * sqrtProd T ∈ radSpan s
    rw [sqrtProd_mul]
    have hU : (S ∪ T) \ (S ∩ T) ⊆ s := (sdiff_subset).trans (union_subset hS hT)
    have := ratCast_mul_mem_radSpan (∏ x ∈ S ∩ T, (x : ℚ)) (sqrtProd_mem_radSpan hU)
    simpa using this
  exact hle (Submodule.mul_mem_mul hx hy)

/-- Blueprint K01 (auxiliary): `radSpan s` as a `ℚ`-subalgebra of `ℝ`. -/
noncomputable def radSubalgebra (s : Finset ℕ) : Subalgebra ℚ ℝ :=
  (radSpan s).toSubalgebra (one_mem_radSpan s) fun _ _ hx hy ↦ mul_mem_radSpan hx hy

/-- Blueprint K01 (auxiliary): every element of `radSpan s` is algebraic over `ℚ`. -/
theorem isAlgebraic_of_mem_radSpan {s : Finset ℕ} {x : ℝ} (hx : x ∈ radSpan s) :
    IsAlgebraic ℚ x := by
  have hfg : (Subalgebra.toSubmodule (radSubalgebra s)).FG :=
    Submodule.fg_span ((s.powerset.finite_toSet).image _)
  exact (IsIntegral.of_mem_of_fg (radSubalgebra s) hfg x hx).isAlgebraic

/-- Blueprint K01 (auxiliary): `radSpan s` is closed under inversion (it is a field). -/
theorem inv_mem_radSpan {s : Finset ℕ} {x : ℝ} (hx : x ∈ radSpan s) : x⁻¹ ∈ radSpan s :=
  Subalgebra.inv_mem_of_algebraic (A := radSubalgebra s) (x := ⟨x, hx⟩)
    (isAlgebraic_of_mem_radSpan hx)

/-- Blueprint K01 (auxiliary): `radSpan ∅ = ℚ`. -/
theorem exists_ratCast_eq_of_mem_radSpan_empty {x : ℝ} (hx : x ∈ radSpan ∅) :
    ∃ q : ℚ, (q : ℝ) = x := by
  rw [radSpan, powerset_empty] at hx
  simp only [coe_singleton, Set.image_singleton, sqrtProd_empty, Submodule.mem_span_singleton]
    at hx
  obtain ⟨q, hq⟩ := hx
  exact ⟨q, by simpa [Rat.smul_def] using hq⟩

/-- Blueprint K01 (auxiliary): decomposition `L (insert p s) = L s + √p · L s`. -/
theorem exists_add_mul_sqrt_of_mem_radSpan_insert {s : Finset ℕ} {p : ℕ} {x : ℝ}
    (hx : x ∈ radSpan (insert p s)) :
    ∃ a ∈ radSpan s, ∃ b ∈ radSpan s, x = a + b * Real.sqrt p := by
  refine Submodule.span_induction (p := fun x _ ↦ ∃ a ∈ radSpan s, ∃ b ∈ radSpan s,
    x = a + b * Real.sqrt p) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨T, hT, rfl⟩
    simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset] at hT
    by_cases hpT : p ∈ T
    · have hT' : T.erase p ⊆ s := subset_insert_iff.1 hT
      refine ⟨0, (radSpan s).zero_mem, sqrtProd (T.erase p), sqrtProd_mem_radSpan hT', ?_⟩
      rw [zero_add, mul_comm, ← sqrtProd_insert (notMem_erase p T), insert_erase hpT]
    · refine ⟨sqrtProd T, sqrtProd_mem_radSpan ((subset_insert_iff_of_notMem hpT).1 hT), 0,
        (radSpan s).zero_mem, by ring⟩
  · exact ⟨0, (radSpan s).zero_mem, 0, (radSpan s).zero_mem, by ring⟩
  · rintro x y _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
    exact ⟨a + c, (radSpan s).add_mem ha hc, b + d, (radSpan s).add_mem hb hd, by ring⟩
  · rintro q x _ ⟨a, ha, b, hb, rfl⟩
    exact ⟨q • a, (radSpan s).smul_mem q ha, q • b, (radSpan s).smul_mem q hb, by
      simp only [Rat.smul_def]; ring⟩

/-! ### Irrationality (base case) -/

/-- Blueprint K01 (auxiliary): a squarefree natural number `> 1` is not a square. -/
theorem not_isSquare_of_squarefree {r : ℕ} (hr1 : 1 < r) (hsq : Squarefree r) :
    ¬ IsSquare r := by
  rintro ⟨a, rfl⟩
  have : IsUnit a := hsq a dvd_rfl
  rw [Nat.isUnit_iff] at this
  subst this
  simp at hr1

/-- Blueprint K01 (auxiliary): `√r` is irrational for squarefree `r > 1`. -/
theorem irrational_sqrt_of_squarefree {r : ℕ} (hr1 : 1 < r) (hsq : Squarefree r) :
    Irrational (Real.sqrt r) :=
  irrational_sqrt_natCast_iff.2 (not_isSquare_of_squarefree hr1 hsq)

/-! ### The main induction -/

/-- Blueprint K01 (strengthened induction hypothesis): if `s` is admissible and `r > 1` is
squarefree and coprime to every element of `s`, then `√r ∉ L s`. -/
theorem sqrt_notMem_radSpan (s : Finset ℕ) :
    Admissible s → ∀ r : ℕ, 1 < r → Squarefree r → (∀ a ∈ s, Nat.Coprime r a) →
      Real.sqrt r ∉ radSpan s := by
  induction s using Finset.induction_on with
  | empty =>
    intro _ r hr1 hsq _ hmem
    obtain ⟨q, hq⟩ := exists_ratCast_eq_of_mem_radSpan_empty hmem
    exact irrational_sqrt_of_squarefree hr1 hsq ⟨q, hq⟩
  | insert p t hp ih =>
    intro hadm r hr1 hsq hcop hmem
    have hadm' : Admissible t := hadm.mono (subset_insert p t)
    have hp1 : 1 < p := hadm.one_lt p (mem_insert_self p t)
    have hpsq : Squarefree p := hadm.squarefree p (mem_insert_self p t)
    have hpcop : ∀ a ∈ t, Nat.Coprime p a := fun a ha ↦
      hadm.coprime p (mem_insert_self p t) a (mem_insert_of_mem ha) (fun h ↦ hp (h ▸ ha))
    have hrp : Nat.Coprime r p := hcop p (mem_insert_self p t)
    have hrcop : ∀ a ∈ t, Nat.Coprime r a := fun a ha ↦ hcop a (mem_insert_of_mem ha)
    have ihp : Real.sqrt p ∉ radSpan t := ih hadm' p hp1 hpsq hpcop
    obtain ⟨a, ha, b, hb, hab⟩ := exists_add_mul_sqrt_of_mem_radSpan_insert hmem
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    -- squaring the relation
    have hsq_rel : (2 * a * b) * Real.sqrt p = (r : ℝ) - a * a - (p : ℝ) * (b * b) := by
      have h1 : (Real.sqrt r) ^ 2 = (r : ℝ) := Real.sq_sqrt hr0
      have h2 : (Real.sqrt p) ^ 2 = (p : ℝ) := Real.sq_sqrt hp0
      rw [hab] at h1
      linear_combination h1 - (b * b) * h2
    have hc : (r : ℝ) - a * a - (p : ℝ) * (b * b) ∈ radSpan t :=
      (radSpan t).sub_mem ((radSpan t).sub_mem (natCast_mem_radSpan t r) (mul_mem_radSpan ha ha))
        (mul_mem_radSpan (natCast_mem_radSpan t p) (mul_mem_radSpan hb hb))
    by_cases hab0 : a * b = 0
    · rcases mul_eq_zero.1 hab0 with ha0 | hb0
      · -- `√r = b √p`, so `√(p r) = b p ∈ L t`
        subst ha0
        have hpr1 : 1 < p * r := by nlinarith
        have hprsq : Squarefree (p * r) := Nat.squarefree_mul_iff.2 ⟨hrp.symm, hpsq, hsq⟩
        have hprcop : ∀ a ∈ t, Nat.Coprime (p * r) a := fun a ha ↦
          Nat.Coprime.mul_left (hpcop a ha) (hrcop a ha)
        refine ih hadm' (p * r) hpr1 hprsq hprcop ?_
        have : Real.sqrt ((p * r : ℕ) : ℝ) = b * (p : ℝ) := by
          rw [Nat.cast_mul, Real.sqrt_mul hp0, hab, zero_add, mul_comm b, ← mul_assoc,
            Real.mul_self_sqrt hp0, mul_comm]
        rw [this]
        exact mul_mem_radSpan hb (natCast_mem_radSpan t p)
      · -- `√r = a ∈ L t`
        subst hb0
        refine ih hadm' r hr1 hsq hrcop ?_
        rw [hab, zero_mul, add_zero]
        exact ha
    · -- `√p = c / (2ab) ∈ L t`
      refine ihp ?_
      have h2ab : (2 * a * b) ∈ radSpan t := by
        have := ratCast_mul_mem_radSpan (2 : ℚ) (mul_mem_radSpan ha hb)
        simpa [mul_assoc] using this
      have h2ab0 : (2 * a * b) ≠ 0 := by
        rw [mul_assoc]; exact mul_ne_zero two_ne_zero hab0
      have : Real.sqrt p = (2 * a * b)⁻¹ * ((r : ℝ) - a * a - (p : ℝ) * (b * b)) := by
        rw [← hsq_rel, ← mul_assoc, inv_mul_cancel₀ h2ab0, one_mul]
      rw [this]
      exact mul_mem_radSpan (inv_mem_radSpan h2ab) hc

/-- Blueprint K01 (coefficient form over `Finset ℕ`): a vanishing `ℚ`-linear combination of the
`√(∏ T)`, `T ⊆ s`, has all coefficients zero. -/
theorem sum_eq_zero_imp (s : Finset ℕ) : Admissible s → ∀ c : Finset ℕ → ℚ,
    ∑ T ∈ s.powerset, (c T : ℝ) * sqrtProd T = 0 → ∀ T ∈ s.powerset, c T = 0 := by
  induction s using Finset.induction_on with
  | empty =>
    intro _ c hc T hT
    rw [powerset_empty, mem_singleton] at hT
    subst hT
    rw [powerset_empty, sum_singleton, sqrtProd_empty, mul_one] at hc
    exact_mod_cast hc
  | insert p t hp ih =>
    intro hadm c hc
    have hadm' : Admissible t := hadm.mono (subset_insert p t)
    have hp1 : 1 < p := hadm.one_lt p (mem_insert_self p t)
    have hpsq : Squarefree p := hadm.squarefree p (mem_insert_self p t)
    have hpcop : ∀ a ∈ t, Nat.Coprime p a := fun a ha ↦
      hadm.coprime p (mem_insert_self p t) a (mem_insert_of_mem ha) (fun h ↦ hp (h ▸ ha))
    have ihp : Real.sqrt p ∉ radSpan t := sqrt_notMem_radSpan t hadm' p hp1 hpsq hpcop
    -- split the relation as `A + B √p = 0`
    have hdisj : Disjoint t.powerset (t.powerset.image (insert p)) := by
      rw [disjoint_left]
      intro T hT hT'
      obtain ⟨U, -, rfl⟩ := mem_image.1 hT'
      exact hp (mem_powerset.1 hT (mem_insert_self p U))
    have hinj : ∀ U ∈ t.powerset, ∀ V ∈ t.powerset, insert p U = insert p V → U = V := by
      intro U hU V hV hUV
      have hU' : p ∉ U := fun h ↦ hp (mem_powerset.1 hU h)
      have hV' : p ∉ V := fun h ↦ hp (mem_powerset.1 hV h)
      rw [← erase_insert hU', hUV, erase_insert hV']
    rw [powerset_insert, sum_union hdisj, sum_image hinj] at hc
    set A : ℝ := ∑ T ∈ t.powerset, (c T : ℝ) * sqrtProd T with hA
    set B : ℝ := ∑ T ∈ t.powerset, (c (insert p T) : ℝ) * sqrtProd T with hB
    have hAmem : A ∈ radSpan t := Submodule.sum_mem _ fun T hT ↦
      ratCast_mul_mem_radSpan _ (sqrtProd_mem_radSpan (mem_powerset.1 hT))
    have hBmem : B ∈ radSpan t := Submodule.sum_mem _ fun T hT ↦
      ratCast_mul_mem_radSpan _ (sqrtProd_mem_radSpan (mem_powerset.1 hT))
    have hrel : A + B * Real.sqrt p = 0 := by
      rw [← hc, hA, hB, sum_mul]
      congr 1
      refine sum_congr rfl fun T hT ↦ ?_
      have hpT : p ∉ T := fun h ↦ hp (mem_powerset.1 hT h)
      rw [sqrtProd_insert hpT]
      ring
    have hB0 : B = 0 := by
      by_contra hB0
      refine ihp ?_
      have : Real.sqrt p = -(B⁻¹ * A) := by
        field_simp
        linear_combination hrel
      rw [this]
      exact (radSpan t).neg_mem (mul_mem_radSpan (inv_mem_radSpan hBmem) hAmem)
    have hA0 : A = 0 := by simpa [hB0] using hrel
    have h1 := ih hadm' c hA0
    have h2 := ih hadm' (fun T ↦ c (insert p T)) hB0
    intro T hT
    rw [powerset_insert, mem_union] at hT
    rcases hT with hT | hT
    · exact h1 T hT
    · obtain ⟨U, hU, rfl⟩ := mem_image.1 hT
      exact h2 U hU

/-! ### The `Fin m`-indexed statements -/

section FinIndexed

variable {m : ℕ} {r : Fin m → ℕ}

/-- Blueprint K01 (auxiliary): pairwise coprime numbers `> 1` are pairwise distinct. -/
theorem injective_of_pairwise_coprime (hr1 : ∀ j, 1 < r j)
    (hcop : ∀ j k, j ≠ k → Nat.Coprime (r j) (r k)) : Function.Injective r := by
  intro j k hjk
  by_contra hne
  have h := hcop j k hne
  rw [hjk, Nat.coprime_self] at h
  exact absurd (hr1 k) (by omega)

/-- Blueprint K01 (auxiliary): the image of an admissible `Fin m`-family is admissible. -/
theorem admissible_image (hr1 : ∀ j, 1 < r j) (hsq : ∀ j, Squarefree (r j))
    (hcop : ∀ j k, j ≠ k → Nat.Coprime (r j) (r k)) : Admissible (univ.image r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨j, -, rfl⟩ := mem_image.1 ha
    exact hr1 j
  · intro a ha
    obtain ⟨j, -, rfl⟩ := mem_image.1 ha
    exact hsq j
  · intro a ha b hb hab
    obtain ⟨j, -, rfl⟩ := mem_image.1 ha
    obtain ⟨k, -, rfl⟩ := mem_image.1 hb
    exact hcop j k fun h ↦ hab (h ▸ rfl)

/-- Blueprint K01. For pairwise coprime squarefree `r j > 1`, the family
`S ↦ √(∏_{j ∈ S} r j)` indexed by `Finset (Fin m)` is linearly independent over `ℚ`. -/
theorem linearIndependent_sqrt_prod
    (hr1 : ∀ j, 1 < r j) (hsq : ∀ j, Squarefree (r j))
    (hcop : ∀ j k, j ≠ k → Nat.Coprime (r j) (r k)) :
    LinearIndependent ℚ (fun S : Finset (Fin m) => Real.sqrt (∏ j ∈ S, (r j : ℝ))) := by
  have hinj : Function.Injective r := injective_of_pairwise_coprime hr1 hcop
  have hadm : Admissible (univ.image r) := admissible_image hr1 hsq hcop
  rw [Fintype.linearIndependent_iff]
  intro g hg S
  -- transport the coefficients to `Finset ℕ`
  let c : Finset ℕ → ℚ := fun T ↦ g (univ.filter fun j ↦ r j ∈ T)
  have hfilter : ∀ S : Finset (Fin m), (univ.filter fun j ↦ r j ∈ S.image r) = S := by
    intro S
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · rintro ⟨i, hi, hij⟩
      rwa [← hinj hij]
    · intro hj
      exact ⟨j, hj, rfl⟩
  have hpow : (univ.image r).powerset = univ.image fun S : Finset (Fin m) ↦ S.image r := by
    ext T
    simp only [mem_powerset, mem_image, mem_univ, true_and]
    constructor
    · intro hT
      refine ⟨univ.filter fun j ↦ r j ∈ T, ?_⟩
      ext x
      simp only [mem_image, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact hj
      · intro hx
        obtain ⟨j, -, rfl⟩ := mem_image.1 (hT hx)
        exact ⟨j, hx, rfl⟩
    · rintro ⟨S, rfl⟩
      exact image_subset_image (subset_univ S)
  have himg_inj : ∀ S ∈ (univ : Finset (Finset (Fin m))),
      ∀ S' ∈ (univ : Finset (Finset (Fin m))), S.image r = S'.image r → S = S' :=
    fun S _ S' _ h ↦ (image_injective hinj) h
  have hsum : ∑ T ∈ (univ.image r).powerset, (c T : ℝ) * sqrtProd T = 0 := by
    rw [hpow, sum_image himg_inj, ← hg]
    refine sum_congr rfl fun S _ ↦ ?_
    simp only [c, hfilter, sqrtProd, Rat.smul_def]
    rw [prod_image fun x _ y _ h ↦ hinj h]
  have := sum_eq_zero_imp _ hadm c hsum (S.image r)
    (by rw [hpow]; exact mem_image_of_mem _ (mem_univ S))
  change g (univ.filter fun j ↦ r j ∈ S.image r) = 0 at this
  rwa [hfilter] at this

/-- Blueprint K01 over `ℤ`. -/
theorem linearIndependent_sqrt_prod_int
    (hr1 : ∀ j, 1 < r j) (hsq : ∀ j, Squarefree (r j))
    (hcop : ∀ j k, j ≠ k → Nat.Coprime (r j) (r k)) :
    LinearIndependent ℤ (fun S : Finset (Fin m) => Real.sqrt (∏ j ∈ S, (r j : ℝ))) :=
  (linearIndependent_sqrt_prod hr1 hsq hcop).restrict_scalars' ℤ

/-- Blueprint K01, coefficient form over `ℤ`: a vanishing integer combination of the
`√(∏_{j ∈ S} r j)` has all coefficients zero. -/
theorem sum_intCast_mul_sqrt_prod_eq_zero
    (hr1 : ∀ j, 1 < r j) (hsq : ∀ j, Squarefree (r j))
    (hcop : ∀ j k, j ≠ k → Nat.Coprime (r j) (r k)) (c : Finset (Fin m) → ℤ)
    (hc : ∑ S, (c S : ℝ) * Real.sqrt (∏ j ∈ S, (r j : ℝ)) = 0) : c = 0 := by
  have h := Fintype.linearIndependent_iff.1 (linearIndependent_sqrt_prod_int hr1 hsq hcop) c
    (by simpa [zsmul_eq_mul] using hc)
  funext S
  exact h S

end FinIndexed

end Nikodym.MultiQuad

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
