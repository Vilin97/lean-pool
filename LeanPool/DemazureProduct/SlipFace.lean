/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
import LeanPool.DemazureProduct.Valley
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.Interval

/-!
# Slipfaces

This file defines slipface functions and develops their basic properties, including the $\star$
(Demazure product) and residuals $\triangleleft$ and $\triangleright$. It corresponds roughly to
Section 3, with some essential-set material from Section 7.1, of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).
-/

namespace LeanPool.DemazureProduct


/-- A slipface function of shift `χ`, i.e. a function $s : \mathbb{Z}^2 \to \mathbb{N}$
satisfying conditions (S1) to (S3) from
[An extended Demazure product](https://arxiv.org/abs/2206.14227):

- first differences in the `a`- and `b`-directions are in `{0,1}`
- $s(a,b) \ge \max\{0, \chi + a - b\}$
- each row and column eventually agrees with $\max\{0, \chi + a - b\}$

Lean stores the function as `func` and the shift as `χ`; the article writes this as
$s \in \mathrm{SF}_\chi$. *Definition 3.1 (`defn:slipface`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).* -/
structure SlipFace where
  /-- The integer-valued slipface function. -/
  func : ℤ → ℤ → ℤ
  /-- The shift of the slipface. -/
  χ : ℤ
  a_step : ∀ a b : ℤ, func a b ≤ func (a+1) b ∧ func (a+1) b ≤ func a b + 1
  b_step : ∀ a b : ℤ, func a (b+1) ≤ func a b ∧ func a b ≤ func a (b+1) + 1
  nonneg : ∀ a b, func a b ≥ 0
  ge_diff : ∀ a b, func a b ≥ a - b + χ
  small_a : ∀ b, ∃ A, ∀ a ≤ A, func a b  = 0
  large_a : ∀ b, ∃ A, ∀ a ≥ A, func a b = a - b + χ
  small_b : ∀ a, ∃ B, ∀ b ≤ B, func a b = a - b + χ
  large_b : ∀ a, ∃ B, ∀ b ≥ B, func a b = 0

instance : CoeFun SlipFace (fun _ => ℤ → ℤ → ℤ) :=
  ⟨SlipFace.func⟩

lemma SF_ext (s t : SlipFace) : s = t ↔ ∀ a b, s a b = t a b := by
  constructor
  · simp_all
  · intro h
    have hχ : s.χ = t.χ := by
      obtain ⟨As, hAs⟩ := s.large_a 0
      obtain ⟨At, hAt⟩ := t.large_a 0
      let A := max As At
      have hs : s.χ = s A 0 - A := by
        have := hAs A (le_max_left _ _)
        omega
      have ht : t.χ = t A 0 - A := by
        have := hAt A (le_max_right _ _)
        omega
      rw [hs, ht, h A 0]
    cases s
    cases t
    rw [SlipFace.mk.injEq]
    constructor
    · funext a b
      exact h a b
    · exact hχ

namespace SlipFace
variable (sf : SlipFace)

/-- The dual slipface $s^\vee$, characterized by
$$
s(a,b) - s^\vee(b,a) = \chi + a - b.
$$

In Lean the dual is `sf.dual`, and its value at `(b,a)` is written
`sf.dual b a`. *Definition 3.4 (`defn:sdual`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).* -/
def dual : SlipFace := {
  func := fun b a => sf a b - a + b - sf.χ
  χ := -sf.χ,
  a_step := by
    rintro b a
    have step := sf.b_step a b
    constructor <;> omega
  b_step := by
    rintro b a
    have step := sf.a_step a b
    constructor <;> omega
  nonneg := by
    rintro b a
    have h := sf.ge_diff a b
    linarith
  ge_diff := by
    rintro b a
    have h := sf.nonneg a b
    linarith
  small_a := by
    rintro b
    obtain ⟨A, hA⟩ := sf.small_b b
    use A
    rintro a ha
    rw [hA a ha]
    omega
  large_a := by
    rintro b
    obtain ⟨A, hA⟩ := sf.large_b b
    use A
    rintro a ha
    rw [hA a ha]
    omega
  small_b := by
    rintro a
    obtain ⟨B, hB⟩ := sf.small_a a
    use B
    rintro b hb
    rw [hB b hb]
    omega
  large_b := by
    rintro a
    obtain ⟨B, hB⟩ := sf.large_a a
    use B
    rintro b hb
    rw [hB b hb]
    omega
}

lemma dual_dual (s : SlipFace) : s.dual.dual = s := by
  apply (SF_ext s.dual.dual s).mpr
  intro a b
  dsimp [SlipFace.dual]
  omega

lemma duality (a b : ℤ) : sf a b - sf.dual b a = a - b + sf.χ := by
  dsimp [SlipFace.dual]
  omega

lemma s_eq (a b : ℤ) : sf a b = a - b + sf.χ + sf.dual b a := by
  linarith [sf.duality a b]

lemma s'_eq (b a : ℤ) : sf.dual b a = sf a b - a + b - sf.χ := by
  linarith [sf.duality a b]

lemma ge_max (a b : ℤ) : sf a b ≥ max 0 (a - b + sf.χ) :=
  max_le (sf.nonneg a b) (sf.ge_diff a b)

lemma gt_iff_special (a b : ℤ) : sf a b > max 0 (a - b + sf.χ)
  ↔ sf a b > 0 ∧ sf.dual b a > 0 := by
  constructor
  · intro hab
    refine ⟨lt_of_le_of_lt (le_max_left _ _) hab, ?_⟩
    by_contra hdual
    have hdual0 : sf.dual b a = 0 := le_antisymm (le_of_not_gt hdual) (sf.dual.nonneg b a)
    have hle : sf a b ≤ max 0 (a - b + sf.χ) := by
      rw [sf.s_eq, hdual0]
      simp
    exact not_lt_of_ge hle hab
  · intro hsf
    exact max_lt_iff.mpr ⟨hsf.1, by rw [sf.s_eq]; exact lt_add_of_pos_right _ hsf.2⟩

lemma eq_iff_nonspecial (a b : ℤ) : sf a b = max 0 (a - b + sf.χ)
  ↔ sf a b = 0 ∨ sf.dual b a = 0 := by
  rw [← eq_comm, ← (sf.ge_max a b).not_lt_iff_eq]
  change ¬ sf a b > max 0 (a - b + sf.χ) ↔ sf a b = 0 ∨ sf.dual b a = 0
  rw [sf.gt_iff_special]
  constructor
  · intro h
    push Not at h
    by_cases hs : sf a b > 0
    · right; exact le_antisymm (h hs) (sf.dual.nonneg b a)
    · left; exact le_antisymm (le_of_not_gt hs) (sf.nonneg a b)
  · rintro (h | h) ⟨hs, hdual⟩
    · simp_all
    · simp_all

/-- The one-sided monotonicity and vanishing conditions providing a simplified
criterion for slipfaces.

These are conditions (D1) and (D2) from
[An extended Demazure product](https://arxiv.org/abs/2206.14227), extracted into a reusable Lean
structure. *Properties D1 and D2.* -/
structure D_props (f : ℤ → ℤ → ℤ) : Prop where
  a_step : ∀ a b : ℤ, f (a+1) b ≥ f a b
  b_step : ∀ a b : ℤ, f a (b+1) ≤ f a b
  large_b : ∀ a, ∃ B, ∀ b ≥ B, f a b = 0
  small_a : ∀ b, ∃ A, ∀ a ≤ A, f a b = 0

lemma mono_a_of_D_props (f : ℤ → ℤ → ℤ) (h : D_props f) :
    ∀ a a' b, a ≤ a' → f a' b ≥ f a b := by
  intro a a' b ha
  let n : ℕ := (a' - a).toNat
  have a'_eq : a' = a + n := by
    omega
  rw [a'_eq]
  induction n with
  | zero => simp
  | succ n ih =>
    apply le_trans ih
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc]
    exact h.a_step (a + n) b

lemma mono_b_of_D_props (f : ℤ → ℤ → ℤ) (h : D_props f) :
    ∀ a b b', b ≤ b' → f a b' ≤ f a b := by
  intro a b b' hb
  let n : ℕ := (b' - b).toNat
  have b'_eq : b' = b + n := by
    omega
  rw [b'_eq]
  induction n with
  | zero => simp
  | succ n ih =>
    apply le_trans _ ih
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc]
    exact h.b_step a (b + n)

/-- Construct a slipface from a pair of functions satisfying `D_props` and the
duality relation `s a b - t b a = a - b + χ`. *Lemma 3.6 (`lem:dualCrit`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 1/2.* -/
lemma sf_of_D_props {s t : ℤ → ℤ → ℤ} {χ : ℤ}
    (h : ∀ a b, s a b - t b a = a - b + χ) :
  D_props s ∧ D_props t →
  ∃ sf : SlipFace, (sf.func = s ∧ sf.χ = χ) ∧ sf.dual.func = t := by
  rintro ⟨sp, tp⟩
  let sf : SlipFace := {
    func := s,
    χ := χ,
    a_step := by
      intro a b
      have step0 := sp.a_step a b
      have step1 := tp.b_step b a
      constructor <;> linarith [h (a+1) b, h a (b+1), h a b]
    b_step := by
      intro a b
      have step0 := sp.b_step a b
      have step1 := tp.a_step b a
      constructor <;> linarith [h a (b+1), h (a+1) b, h a b]
    nonneg := by
      intro a b
      obtain ⟨A, hA⟩ := sp.small_a b
      by_cases ha : a ≤ A
      · exact le_of_eq <| (Eq.symm <| hA a ha)
      · have ha : A ≤ a := by omega
        rw [← hA A (le_refl A)]
        exact mono_a_of_D_props s sp A a b ha
    ge_diff := by
      intro a b
      rw [← h a b]
      suffices t b a ≥ 0 by omega
      obtain ⟨B, hB⟩ := tp.small_a a
      by_cases hb : b ≤ B
      · exact le_of_eq <| (Eq.symm <| hB b hb)
      · have hb : B ≤ b := by omega
        rw [← hB B (le_refl B)]
        exact mono_a_of_D_props t tp B b a hb
    small_a := by
      intro b
      obtain ⟨A, hA⟩ := sp.small_a b
      use A
    large_a := by
      intro b
      obtain ⟨A, hA⟩ := tp.large_b b
      use A
      intro a ha
      specialize hA a ha
      specialize h a b
      rwa [hA, sub_zero] at h
    small_b := by
      intro a
      obtain ⟨B, hB⟩ := tp.small_a a
      use B
      intro b hb
      specialize hB b hb
      specialize h a b
      rwa [hB, sub_zero] at h
    large_b := by
      intro a
      obtain ⟨B, hB⟩ := sp.large_b a
      use B
  }
  use sf
  constructor
  · constructor <;> rfl
  · ext a b
    dsimp [SlipFace.dual]
    have hsf_func : sf.func = s := rfl
    have hsf_χ : sf.χ = χ := rfl
    rw [hsf_func, hsf_χ]
    linarith [h b a]

/-- Every slipface function and its dual satisfies the `D_props`, denoted (D1) and (D2).
*Lemma 3.6 (`lem:dualCrit`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 2/2.* -/
lemma D_props_of_sf (sf : SlipFace) : D_props sf.func ∧ D_props sf.dual.func :=
  ⟨⟨fun a b => (sf.a_step a b).1, fun a b => (sf.b_step a b).1, sf.large_b, sf.small_a⟩,
    ⟨fun a b => (sf.dual.a_step a b).1, fun a b => (sf.dual.b_step a b).1,
      sf.dual.large_b, sf.dual.small_a⟩⟩

lemma nondec {a a' b b' : ℤ} (a_le_a' : a ≤ a') (b'_le_b : b' ≤ b) : sf a b ≤ sf a' b' := by
  have dp := D_props_of_sf sf
  exact le_trans (mono_a_of_D_props sf.func dp.1 a a' b a_le_a')
    (mono_b_of_D_props sf.func dp.1 a' b' b b'_le_b)

lemma zero_below {a a' b b' : ℤ} (a_le_a' : a ≤ a') (b'_le_b : b' ≤ b) :
  sf a' b' = 0 → sf a b = 0 := by
  intro eq0
  have := sf.nondec a_le_a' b'_le_b
  have le_zero : sf a b ≤ 0 := by
    rwa [eq0] at this
  have ge_zero : sf a b ≥ 0 := sf.nonneg a b
  exact le_antisymm le_zero ge_zero

/-! ### Slip valleys and the product formula

A `Valley` is an integer function rising on both sides, which therefore has a
well-defined minimum achieved at finitely many places.

This section packages the minimization problem defining slipface product into a
`Valley`, then uses it to construct the product `s ⋆ t` and prove its basic
properties. -/

/-- The valley $\ell \mapsto s(a,\ell) + t(\ell,b)$ whose minimum computes the
slipface product at `(a,b)`. -/
noncomputable def SlipValley (s t : SlipFace) (a b : ℤ) : Valley where
  f := fun l => s a l + t l b
  rises := by
    intro m
    let L := a - m + s.χ
    let R := b + m - t.χ
    suffices {n : ℤ | s a n + t n b ≤ m} ⊆ Finset.Icc L R by
      apply Set.Finite.subset _ this
      simp_all
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    suffices n ≥ L ∧ n ≤ R by simpa
    constructor
    · linarith [t.nonneg n b, s.ge_diff a n]
    · linarith [s.nonneg a n, t.ge_diff n b]

/-- The min-plus product formula
$$
(s \star t)(a,b) = \min_{\ell \in \mathbb{Z}} [s(a,\ell) + t(\ell,b)].
$$

In Lean, `starFunc s t a b` is this integer value, while `s ⋆ t` is the resulting
`SlipFace`.
See *Definition 3.7 (`defn:sfAlgebra`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).* -/
noncomputable def starFunc (s t : SlipFace) : ℤ → ℤ → ℤ :=
  fun a b => (SlipValley s t a b).min

lemma star_dual_ineq (s t : SlipFace) (a b : ℤ) :
  starFunc t.dual s.dual b a ≤ starFunc s t a b - a + b - s.χ - t.χ := by
  let v := SlipValley s t a b
  let l := v.M
  have hl : s a l + t l b = starFunc s t a b := by
    exact (SlipValley s t a b).f_M
  have ineq : starFunc t.dual s.dual b a ≤ t.dual b l + s.dual l a := by
    exact (SlipValley t.dual s.dual b a).min_spec l
  apply le_trans ineq
  dsimp [SlipFace.dual]
  omega

lemma star_dual_eq (s t : SlipFace) (a b : ℤ) :
  starFunc s t a b - starFunc t.dual s.dual b a = a - b + s.χ + t.χ := by
  suffices starFunc t.dual s.dual b a = starFunc s t a b - a + b - s.χ - t.χ by omega
  apply le_antisymm
  · exact star_dual_ineq s t a b
  let s' := s.dual
  let t' := t.dual
  have s'' : s = s'.dual := by rw [SlipFace.dual_dual s]
  have t'' : t = t'.dual := by rw [SlipFace.dual_dual t]
  have ineq := star_dual_ineq t' s' b a
  rw [← s'', ← t''] at ineq
  subst s' t'
  have : s.dual.χ = - s.χ := by dsimp [SlipFace.dual]
  rw [this] at ineq
  have : t.dual.χ = - t.χ := by dsimp [SlipFace.dual]
  rw [this] at ineq
  omega

private lemma D_props_of_star_func (s t : SlipFace) : D_props (s.starFunc t) := by
  constructor
  · intro a b
    let v := SlipValley s t (a+1) b
    let l := v.M
    rw [← show s (a+1) l + t l b = s.starFunc t (a+1) b by
      exact (SlipValley s t (a+1) b).f_M]
    have hmin : s.starFunc t a b ≤ s a l + t l b := by
      exact (SlipValley s t a b).min_spec l
    apply le_trans hmin
    have step : s a l ≤ s (a+1) l := (s.a_step a l).1
    omega
  · intro a b
    let v := SlipValley s t a b
    let l := v.M
    rw [← show s a l + t l b = s.starFunc t a b by
      exact (SlipValley s t a b).f_M]
    have hmin : s.starFunc t a (b+1) ≤ s a l + t l (b+1) := by
      exact (SlipValley s t a (b+1)).min_spec l
    apply le_trans hmin
    have step : t l (b+1) ≤ t l b := (t.b_step l b).1
    omega
  · intro a
    obtain ⟨l, hl⟩ := s.large_b a
    specialize hl l (le_refl l)
    obtain ⟨B, hB⟩ := t.large_b l
    use B
    intro b hb
    specialize hB b hb
    have : s.starFunc t a b ≤ s a l + t l b := by
      exact (SlipValley s t a b).min_spec l
    have le_zero : s.starFunc t a b ≤ 0 := by
      rwa [hl, hB, add_zero] at this
    have ge_zero : s.starFunc t a b ≥ 0 := by
      let v := SlipValley s t a b
      let l := v.M
      rw [← show s a l + t l b = s.starFunc t a b by
        exact (SlipValley s t a b).f_M]
      linarith [s.nonneg a l, t.nonneg l b]
    exact le_antisymm le_zero ge_zero
  · intro b
    obtain ⟨l, hl⟩ := t.small_a b
    specialize hl l (le_refl l)
    obtain ⟨A, hA⟩ := s.small_a l
    use A
    intro a ha
    specialize hA a ha
    have : s.starFunc t a b ≤ s a l + t l b := by
      exact (SlipValley s t a b).min_spec l
    have le_zero : s.starFunc t a b ≤ 0 := by
      rwa [hA, hl, zero_add] at this
    have ge_zero : s.starFunc t a b ≥ 0 := by
      let v := SlipValley s t a b
      let l := v.M
      have hl : s a l + t l b = s.starFunc t a b := by
        exact (SlipValley s t a b).f_M
      linarith [s.nonneg a l, t.nonneg l b]
    exact le_antisymm le_zero ge_zero

private lemma star_exists (s t : SlipFace) : ∃ p : SlipFace,
  ((p.func = starFunc s t ∧ p.χ = s.χ + t.χ)
  ∧ p.dual.func = starFunc t.dual s.dual) := by
  let P := starFunc s t
  let P' := starFunc t.dual s.dual
  let χ := s.χ + t.χ
  have : ∀ a b : ℤ, P a b - P' b a = a - b + χ := by
    intro a b
    rw [star_dual_eq s t a b]
    omega
  have h := sf_of_D_props this
  suffices D_props P ∧ D_props P' by
    exact h this
  exact ⟨D_props_of_star_func s t, D_props_of_star_func t.dual s.dual⟩

/-- The product of two slipfaces, obtained from the minimum formula
`starFunc`.
See *Definition 3.7* (`defn:sfAlgebra`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).* -/
noncomputable def star (s t : SlipFace) : SlipFace :=
  Classical.choose (star_exists s t)

noncomputable instance : Mul SlipFace := ⟨star⟩

/-- Infix notation for the slipface Demazure product. -/
infixl:70 " ⋆ " => star

lemma star_func_eq (s t : SlipFace) : (s ⋆ t).func = starFunc s t := by
  have h := star_exists s t
  exact (Classical.choose_spec h).1.1

/-- The formula for the Demazure product of slipfaces:
$s \star t(a,b) = \min_{l \in \mathbb{Z}} (s(a,l) + t(l,b))$.
This unpacks the formal definition of $\star$ into the form of *Definition 3.7*
(`defn:sfAlgebra`) of [An extended Demazure product](https://arxiv.org/abs/2206.14227),
part 1/3.* -/
lemma star_eq_min (s t : SlipFace) (a b : ℤ) :
  IsLeast { s a l + t l b | l : ℤ } ( (s ⋆ t) a b ) := by
  let v := SlipValley s t a b
  have : (s ⋆ t) a b = s a v.M + t v.M b := by
    calc
      (s ⋆ t) a b = v.min := by
        rw [star_func_eq]
        rfl
      _ = s a v.M + t v.M b := by
        rw [← v.f_M]
        rfl
  rw [this]
  constructor
  · use v.M
  · rintro x ⟨l, rfl⟩
    exact (v.M_spec l).1

/-- The shift is additive under $\star$.
*Proposition 3.9* (`prop:sfAlgebraDefined`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 1/6.* -/
@[simp] lemma chi_star (s t : SlipFace) : (s ⋆ t).χ = s.χ + t.χ := by
  have h := star_exists s t
  exact (Classical.choose_spec h).1.2

/-- Duality reverses the product `⋆`. *Proposition 3.9 (`prop:sfAlgebraDefined`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 2/6.* -/
@[simp] lemma star_dual (s t : SlipFace) : (s ⋆ t).dual = t.dual ⋆ s.dual := by
  have h := star_exists s t
  have := (Classical.choose_spec h).2
  apply (SF_ext _ _).mpr
  rw [star_func_eq]
  rw [← this]
  intro a b
  rfl

/-! ### Order structure and comparison with `⋆`

This section defines the Bruhat order on `SlipFace` and records the basic
comparison lemmas relating that order to the product `⋆`.
*Definition 3.2* of [An extended Demazure product](https://arxiv.org/abs/2206.14227). -/

instance : PartialOrder SlipFace where
  le (s t : SlipFace) := ∀ a b, s a b ≤ t a b
  le_refl := by
    simp_all
  le_trans := by
    intro s t u hst htu a b
    exact le_trans (hst a b) (htu a b)
  le_antisymm := by
    intro s t hst hts
    apply (SF_ext s t).mpr
    intro a b
    have le1 : s a b ≤ t a b := hst a b
    have le2 : t a b ≤ s a b := hts a b
    exact le_antisymm le1 le2

lemma star_val_le (s t : SlipFace) (a b l : ℤ) : (s ⋆ t) a b ≤ s a l + t l b := by
  let v := SlipValley s t a b
  have hmin : (s ⋆ t) a b = v.min := by
    rw [star_func_eq]
    rfl
  have hM : v.min ≤ s a l+ t l b  := by
    exact v.min_spec l
  rwa [← hmin] at hM

/-- A minimizer witnessing the slipface Demazure product value at `(a, b)`. -/
noncomputable def starWit (s t : SlipFace) (a b : ℤ) : ℤ :=
  (SlipValley s t a b).M

lemma star_wit_spec (s t : SlipFace) (a b : ℤ) :
  (s ⋆ t) a b = s a (starWit s t a b) + t (starWit s t a b) b := by
  let v := SlipValley s t a b
  rw [star_func_eq]
  exact Eq.symm v.f_M

/-- A lower bound for `(s ⋆ t) a b` is equivalent to a uniform lower bound
against every witness `l`. -/
lemma le_star_val_iff (r s t : SlipFace) (a b : ℤ) :
  r a b ≤ (s ⋆ t) a b ↔ ∀ l, r a b ≤ s a l + t l b
  := by
  constructor
  · intro h l
    contrapose! h
    exact lt_of_le_of_lt (star_val_le s t a b l) h
  · intro h
    let l := starWit s t a b
    have : (s ⋆ t) a b = s a l + t l b := by
      exact star_wit_spec s t a b
    simp_all

/-- An upper bound for `(s ⋆ t) a b` is equivalent to exhibiting a single
witness `l` that realizes it. -/
lemma ge_star_val_iff (r s t : SlipFace) (a b : ℤ) :
  r a b ≥ (s ⋆ t) a b ↔ ∃ l, r a b ≥ s a l + t l b
  := by
  constructor
  · intro h
    use starWit s t a b
    rw [← star_wit_spec s t a b]
    exact h
  · rintro ⟨l, hl⟩
    exact le_trans (star_val_le s t a b l) hl

/-! ### Monoid structure

The product `⋆` is associative and has the positive-part function as identity,
giving `SlipFace` a monoid structure. -/

/-- Slipface product is associative. *Lemma 3.12 (`lem:sfAlgebra`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 1/3.* -/
lemma star_assoc (r s t : SlipFace) : r ⋆ s ⋆ t = r ⋆ (s ⋆ t) := by
  apply (SF_ext _ _).mpr
  intro a b
  apply le_antisymm
  · let l := starWit r (s ⋆ t) a b
    have : (r ⋆ (s ⋆ t)) a b = r a l + (s ⋆ t) l b := star_wit_spec r (s ⋆ t) a b
    rw [this]
    let m := starWit s t l b
    have : (s ⋆ t) l b = s l m + t m b := star_wit_spec s t l b
    rw [this]
    have h1 : (r ⋆ s ⋆ t) a b ≤ (r ⋆ s) a m + t m b := by apply star_val_le
    have h2 : (r ⋆ s) a m ≤ r a l + s l m := by apply star_val_le
    omega
  · let l := starWit (r ⋆ s) t a b
    have : ((r ⋆ s) ⋆ t) a b = (r ⋆ s) a l + t l b := star_wit_spec (r ⋆ s) t a b
    rw [this]
    let m := starWit r s a l
    have : (r ⋆ s) a l = r a m + s m l := star_wit_spec r s a l
    rw [this]
    have h1 : (r ⋆ (s ⋆ t)) a b ≤ r a m + (s ⋆ t) m b := by apply star_val_le
    have h2 : (s ⋆ t) m b ≤ s m l + t l b := by apply star_val_le
    omega

/-- The identity slipface, given by the positive part of `a - b`. -/
def id : SlipFace := {
    func := fun a b => max (a - b) 0,
    χ := 0,
    a_step := by
      intro a b
      by_cases ha : a - b ≥ 0 <;> omega
    b_step := by
      intro a b
      by_cases hb : a - (b + 1) ≥ 0 <;> omega
    nonneg := by
      simp_all
    ge_diff := by
      simp_all
    small_a := by
      intro b
      use b
      omega
    large_a := by
      intro b
      use b
      omega
    small_b := by
      intro a
      use a
      omega
    large_b := by
      intro a
      use a
      omega
  }

lemma id_mul (s : SlipFace) : id ⋆ s = s := by
  apply (SF_ext _ _).mpr
  intro a b
  apply le_antisymm
  · apply (ge_star_val_iff s id s a b).mpr
    use a
    have : id a a = 0 := by
      rw [id]
      simp
    simp only [this, zero_add, ge_iff_le, le_refl]
  · apply (le_star_val_iff s id s a b).mpr
    intro l
    by_cases hl : l ≤ a
    · have : id a l = a - l := by
        rw [id]
        simp only [Int.sub_nonneg, hl, sup_of_le_left]
      rw [this]
      rw [s.s_eq a b, s.s_eq l b]
      have : s.dual b l ≥ s.dual b a := by
        apply s.dual.nondec (le_refl b) hl
      omega
    · have : id a l = 0 := by
        rw [id]; simp; omega
      rw [this, zero_add]
      apply s.nondec (by linarith) (le_refl b)

lemma mul_id (s : SlipFace) : s ⋆ id = s := by
  apply (SF_ext _ _).mpr
  intro a b
  apply le_antisymm
  · apply (ge_star_val_iff s s id a b).mpr
    use b
    have : id b b = 0 := by
      rw [id]
      simp
    simp only [this, add_zero, ge_iff_le, le_refl]
  · apply (le_star_val_iff s s id a b).mpr
    intro l
    by_cases hl : l ≤ b
    · have : id l b = 0 := by
        rw [id]; simp; omega
      rw [this, add_zero]
      apply s.nondec (le_refl a) hl
    · have : id l b = l - b := by
        rw [id]
        exact max_eq_left (by omega)
      rw [this]
      rw [s.s_eq a b, s.s_eq a l]
      have : s.dual l a ≥ s.dual b a := by
        apply s.dual.nondec (by omega) (le_refl a)
      omega

noncomputable instance : Monoid SlipFace where
  mul := star
  one := id
  mul_assoc := star_assoc
  one_mul := id_mul
  mul_one := mul_id

/-! ### The residual operations `◃` and `▹`
This section develops the basic properties of the operations $s \triangleleft t$
and $s \triangleright t$ at the level of slipface functions.
-/

lemma lres_wit_exists (s t : SlipFace) (a b : ℤ) : ∃ m, ∀ l,
  s a l - t.dual b l ≤ s a m - t.dual b m := by
  -- Proof written by Sonnet 4.6.
  obtain ⟨B₁, hB₁⟩ := s.small_b a
  obtain ⟨B₂, hB₂⟩ := t.dual.small_b b
  obtain ⟨U₁, hU₁⟩ := s.large_b a
  obtain ⟨U₂, hU₂⟩ := t.dual.large_b b
  -- Ensure the interval is non-empty by taking max of upper bounds vs min of lower bounds
  let L := min B₁ B₂
  let U := max (max U₁ U₂) L
  have L_le_U : L ≤ U := le_max_right _ _
  have hne : (Finset.Icc L U).Nonempty :=
    ⟨L, Finset.mem_Icc.mpr ⟨le_refl _, L_le_U⟩⟩
  obtain ⟨m, -, hm_max⟩ := Finset.exists_max_image
    (Finset.Icc L U) (fun l => s a l - t.dual b l) hne
  use m
  intro l
  by_cases hlL : l ≤ L
  · -- l is in the left constant regime: f(l) = f(L)
    have hsl : s a l = a - l + s.χ := hB₁ l (le_trans hlL (min_le_left _ _))
    have htl : t.dual b l = b - l + t.dual.χ := hB₂ l (le_trans hlL (min_le_right _ _))
    have hsL : s a L = a - L + s.χ := hB₁ L (min_le_left _ _)
    have htL : t.dual b L = b - L + t.dual.χ := hB₂ L (min_le_right _ _)
    have hm_L := hm_max L (Finset.mem_Icc.mpr ⟨le_refl _, L_le_U⟩)
    omega
  · push Not at hlL
    by_cases hUl : l ≤ U
    · -- l is in the finite interval: directly bounded by argmax
      exact hm_max l (Finset.mem_Icc.mpr ⟨le_of_lt hlL, hUl⟩)
    · push Not at hUl
      -- l is in the right zero regime: f(l) = 0 ≤ f(U) ≤ f(m)
      have hU₁l : U₁ ≤ l :=
        le_trans (le_trans (le_max_left _ _) (le_max_left _ L)) hUl.le
      have hU₂l : U₂ ≤ l :=
        le_trans (le_trans (le_max_right _ _) (le_max_left _ L)) hUl.le
      have hU₁U : U₁ ≤ U := le_trans (le_max_left _ _) (le_max_left _ L)
      have hU₂U : U₂ ≤ U := le_trans (le_max_right _ _) (le_max_left _ L)
      have hs0 : s a l = 0 := hU₁ l hU₁l
      have ht0 : t.dual b l = 0 := hU₂ l hU₂l
      have hsU : s a U = 0 := hU₁ U hU₁U
      have htU : t.dual b U = 0 := hU₂ U hU₂U
      have hm_U := hm_max U (Finset.mem_Icc.mpr ⟨L_le_U, le_refl _⟩)
      omega



/-- The argmax witnessing the left residual value $s \triangleleft t (a,b)$. -/
noncomputable def lresWit (s t : SlipFace) (a b : ℤ) : ℤ :=
  Classical.choose (lres_wit_exists s t a b)

/-- The left residual function
$$
(s \triangleleft t)(a,b) = \max_{\ell \in \mathbb{Z}} \bigl[s(a,\ell) - t^\vee(b,\ell)\bigr].
$$
See *Definition 3.7* (`defn:sfAlgebra`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227). -/
noncomputable def lresFunc (s t : SlipFace) : ℤ → ℤ → ℤ :=
  fun a b => s a (lresWit s t a b) - t.dual b (lresWit s t a b)

/-- Every value $s(a,\ell) - t^\vee(b,\ell)$ is at most $s \triangleleft t (a,b)$. -/
lemma lres_val_ge (s t : SlipFace) (a b l : ℤ) : s a l - t.dual b l ≤ lresFunc s t a b :=
  Classical.choose_spec (lres_wit_exists s t a b) l

/-- The left residual is nonnegative, since for `l ≫ 0` both terms in the
maximizing expression vanish. -/
lemma lres_func_nonneg (s t : SlipFace) (a b : ℤ) : 0 ≤ lresFunc s t a b := by
  -- Proof written by GPT 5.5.
  obtain ⟨U₁, hU₁⟩ := s.large_b a
  obtain ⟨U₂, hU₂⟩ := t.dual.large_b b
  let l := max U₁ U₂
  have hs0 : s a l = 0 := hU₁ l (le_max_left _ _)
  have ht0 : t.dual b l = 0 := hU₂ l (le_max_right _ _)
  have hmax := lres_val_ge s t a b l
  simp_all

private lemma D_props_of_lres_func (s t : SlipFace) : D_props (lresFunc s t) := by
  -- Proof written by GPT 5.5.
  constructor
  · intro a b
    let l := lresWit s t a b
    change s a l - t.dual b l ≤ lresFunc s t (a+1) b
    have hmax : s (a+1) l - t.dual b l ≤ lresFunc s t (a+1) b :=
      lres_val_ge s t (a+1) b l
    have hstep : s a l ≤ s (a+1) l := (s.a_step a l).1
    omega
  · intro a b
    let l := lresWit s t a (b+1)
    change s a l - t.dual (b+1) l ≤ lresFunc s t a b
    have hmax : s a l - t.dual b l ≤ lresFunc s t a b :=
      lres_val_ge s t a b l
    have hstep : t.dual b l ≤ t.dual (b+1) l := (t.dual.a_step b l).1
    omega
  · intro a
    suffices hEventuallyNonpos : ∃ B, ∀ b ≥ B, ∀ l,
        s a l - t.dual b l ≤ 0 by
      obtain ⟨B, hB⟩ := hEventuallyNonpos
      use B
      intro b hb
      apply le_antisymm
      · let l := lresWit s t a b
        change s a l - t.dual b l ≤ 0
        exact hB b hb l
      · exact lres_func_nonneg s t a b
    -- Paper proof: for fixed `a`, consider
    -- `L(a,b) = {l | s(a,l) > t.dual(b,l)}`.  The sets shrink as `b`
    -- increases, `L(a,b₀)` is finite once `s.χ + t.χ + a - b₀ ≤ 0`, and
    -- each individual `l` eventually leaves the set by the large-`a` behavior
    -- of `t.dual`.
    obtain ⟨L₀, hL₀⟩ := s.small_b a
    obtain ⟨U₀, hU₀⟩ := s.large_b a
    let L := L₀
    let U := max U₀ L
    let middle := Finset.Icc L U
    have hmiddle_nonempty : middle.Nonempty := by
      refine ⟨L, ?_⟩
      simp only [Finset.mem_Icc, le_refl, le_sup_right, and_self, middle, U]
    let middleBounds := middle.image (fun l => s a l + l + t.χ)
    have hbounds_nonempty : middleBounds.Nonempty := hmiddle_nonempty.image _
    let M := middleBounds.max' hbounds_nonempty
    use max (a + s.χ + t.χ) M
    intro b hb l
    have hb_left : a + s.χ + t.χ ≤ b := by
      exact le_trans (le_max_left _ _) hb
    have hb_middle : M ≤ b := by
      exact le_trans (le_max_right _ _) hb
    have htd_ge : t.dual b l ≥ b - l - t.χ := by
      change t.dual b l ≥ b - l + t.dual.χ
      exact t.dual.ge_diff b l
    by_cases hl_left : l ≤ L
    · have hs : s a l = a - l + s.χ := hL₀ l hl_left
      omega
    · push Not at hl_left
      by_cases hl_right : U ≤ l
      · have hU₀_le_l : U₀ ≤ l := le_trans (le_max_left U₀ L) hl_right
        have hs : s a l = 0 := hU₀ l hU₀_le_l
        have ht_nonneg : t.dual b l ≥ 0 := t.dual.nonneg b l
        omega
      · push Not at hl_right
        have hl_mem : l ∈ middle := by
          simp only [Finset.mem_Icc, middle]
          omega
        have hval_mem : s a l + l + t.χ ∈ middleBounds := by
          exact Finset.mem_image.mpr ⟨l, hl_mem, rfl⟩
        have hval_le_M : s a l + l + t.χ ≤ M := by
          exact Finset.le_max' middleBounds (s a l + l + t.χ) hval_mem
        omega
  · intro b
    suffices hEventuallyNonpos : ∃ A, ∀ a ≤ A, ∀ l,
        s a l - t.dual b l ≤ 0 by
      obtain ⟨A, hA⟩ := hEventuallyNonpos
      use A
      intro a ha
      apply le_antisymm
      · let l := lresWit s t a b
        change s a l - t.dual b l ≤ 0
        exact hA a ha l
      · exact lres_func_nonneg s t a b
    -- Paper proof, with `a` moving left: `L(a-1,b) ⊆ L(a,b)`, the initial
    -- bad set is finite once `s.χ + t.χ + a - b ≤ 0`, and each fixed `l`
    -- eventually leaves because `s(a,l) = 0` for `a ≪ 0`.
    let A₀ := b - t.χ - s.χ
    obtain ⟨Lₛ, hLₛ⟩ := s.small_b A₀
    obtain ⟨Uₛ, hUₛ⟩ := s.large_b A₀
    obtain ⟨Lₜ, hLₜ⟩ := t.dual.small_b b
    let L := min Lₛ Lₜ
    let U := max Uₛ L
    let middle := Finset.Icc L U
    have hmiddle_nonempty : middle.Nonempty := by
      refine ⟨L, ?_⟩
      simp only [Finset.mem_Icc, le_refl, le_sup_right, and_self, middle, U]
    let cutoffs := middle.image (fun l => Classical.choose (s.small_a l))
    have hcutoffs_nonempty : cutoffs.Nonempty := hmiddle_nonempty.image _
    let A₁ := cutoffs.min' hcutoffs_nonempty
    use min A₀ A₁
    intro a ha l
    have ha_A₀ : a ≤ A₀ := le_trans ha (min_le_left _ _)
    have hs_le_A₀ : s a l ≤ s A₀ l := by
      exact s.nondec ha_A₀ (le_refl l)
    by_cases hl_left : l ≤ L
    · have hsA₀ : s A₀ l = A₀ - l + s.χ :=
        hLₛ l (le_trans hl_left (min_le_left _ _))
      have ht : t.dual b l = b - l - t.χ := by
        change t.dual b l = b - l + t.dual.χ
        exact hLₜ l (le_trans hl_left (min_le_right _ _))
      omega
    · push Not at hl_left
      by_cases hl_right : U ≤ l
      · have hUₛ_le_l : Uₛ ≤ l := le_trans (le_max_left Uₛ L) hl_right
        have hsA₀ : s A₀ l = 0 := hUₛ l hUₛ_le_l
        have ht_nonneg : t.dual b l ≥ 0 := t.dual.nonneg b l
        omega
      · push Not at hl_right
        have hl_mem : l ∈ middle := by
          simp only [Finset.mem_Icc, middle]
          omega
        let A_l := Classical.choose (s.small_a l)
        have hAl_mem : A_l ∈ cutoffs := by
          exact Finset.mem_image.mpr ⟨l, hl_mem, rfl⟩
        have hA₁_le_Al : A₁ ≤ A_l := by
          exact Finset.min'_le cutoffs A_l hAl_mem
        have ha_Al : a ≤ A_l := by
          exact le_trans ha (le_trans (min_le_right A₀ A₁) hA₁_le_Al)
        have hs0 : s a l = 0 := by
          exact Classical.choose_spec (s.small_a l) a ha_Al
        have ht_nonneg : t.dual b l ≥ 0 := t.dual.nonneg b l
        omega

private lemma rres_exists (s t : SlipFace) (a b : ℤ) : ∃ m, ∀ l,
    t l b - s.dual l a ≤ t m b - s.dual m a := by
  obtain ⟨A₁, hA₁⟩ := t.small_a b
  obtain ⟨A₂, hA₂⟩ := s.dual.small_a a
  obtain ⟨U₁, hU₁⟩ := t.large_a b
  obtain ⟨U₂, hU₂⟩ := s.dual.large_a a
  -- Ensure the interval is non-empty by taking max of upper bounds vs min of lower bounds
  let L := min A₁ A₂
  let U := max (max U₁ U₂) L
  have L_le_U : L ≤ U := le_max_right _ _
  have hne : (Finset.Icc L U).Nonempty :=
    ⟨L, Finset.mem_Icc.mpr ⟨le_refl _, L_le_U⟩⟩
  obtain ⟨m, -, hm_max⟩ := Finset.exists_max_image
    (Finset.Icc L U) (fun l => t l b - s.dual l a) hne
  use m
  intro l
  by_cases hlL : l ≤ L
  · -- l is in the left zero regime: g(l) = 0 = g(L) ≤ g(m)
    have htl : t l b = 0 := hA₁ l (le_trans hlL (min_le_left _ _))
    have hsl : s.dual l a = 0 := hA₂ l (le_trans hlL (min_le_right _ _))
    have htL : t L b = 0 := hA₁ L (min_le_left _ _)
    have hsL : s.dual L a = 0 := hA₂ L (min_le_right _ _)
    have hm_L := hm_max L (Finset.mem_Icc.mpr ⟨le_refl _, L_le_U⟩)
    omega
  · push Not at hlL
    by_cases hUl : l ≤ U
    · -- l is in the finite interval: directly bounded by argmax
      exact hm_max l (Finset.mem_Icc.mpr ⟨le_of_lt hlL, hUl⟩)
    · push Not at hUl
      -- l is in the right constant regime: g(l) = g(U) ≤ g(m)
      have hU₁l : U₁ ≤ l :=
        le_trans (le_trans (le_max_left _ _) (le_max_left _ L)) hUl.le
      have hU₂l : U₂ ≤ l :=
        le_trans (le_trans (le_max_right _ _) (le_max_left _ L)) hUl.le
      have hU₁U : U₁ ≤ U := le_trans (le_max_left _ _) (le_max_left _ L)
      have hU₂U : U₂ ≤ U := le_trans (le_max_right _ _) (le_max_left _ L)
      have htl : t l b = l - b + t.χ := hU₁ l hU₁l
      have hsl : s.dual l a = l - a + s.dual.χ := hU₂ l hU₂l
      have htU : t U b = U - b + t.χ := hU₁ U hU₁U
      have hsU : s.dual U a = U - a + s.dual.χ := hU₂ U hU₂U
      have hm_U := hm_max U (Finset.mem_Icc.mpr ⟨L_le_U, le_refl _⟩)
      omega

/-- The argmax witnessing the right residual value $s \triangleright t (a,b)$. -/
noncomputable def rresWit (s t : SlipFace) (a b : ℤ) : ℤ :=
  Classical.choose (rres_exists s t a b)

/-- The right residual function
$$
(s \triangleright t)(a,b) = \max_{\ell \in \mathbb{Z}} \bigl[t(\ell,b) - s^\vee(\ell,a)\bigr].
$$
*Definition 3.7* (`defn:sfAlgebra`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227). -/
noncomputable def rresFunc (s t : SlipFace) : ℤ → ℤ → ℤ :=
  fun a b => t (rresWit s t a b) b - s.dual (rresWit s t a b) a

/-- Every value $t(\ell,b) - s^\vee(\ell,a)$ is at most $s \triangleright t (a,b)$. -/
lemma rres_val_ge (s t : SlipFace) (a b l : ℤ) : t l b - s.dual l a ≤ rresFunc s t a b :=
  Classical.choose_spec (rres_exists s t a b) l

/-- The right residual is nonnegative, since for `l ≪ 0` both terms in the
maximizing expression vanish. -/
lemma rres_func_nonneg (s t : SlipFace) (a b : ℤ) : 0 ≤ rresFunc s t a b := by
  -- Proof written by GPT 5.5.
  obtain ⟨A₁, hA₁⟩ := t.small_a b
  obtain ⟨A₂, hA₂⟩ := s.dual.small_a a
  let l := min A₁ A₂
  have ht0 : t l b = 0 := hA₁ l (min_le_left _ _)
  have hs0 : s.dual l a = 0 := hA₂ l (min_le_right _ _)
  have hmax := rres_val_ge s t a b l
  simp_all

private lemma D_props_of_rres_func (s t : SlipFace) : D_props (rresFunc s t) := by
  -- Proof written by GPT 5.5.
  constructor
  · intro a b
    let l := rresWit s t a b
    change t l b - s.dual l a ≤ rresFunc s t (a+1) b
    have hmax : t l b - s.dual l (a+1) ≤ rresFunc s t (a+1) b :=
      rres_val_ge s t (a+1) b l
    have hstep : s.dual l (a+1) ≤ s.dual l a := (s.dual.b_step l a).1
    omega
  · intro a b
    let l := rresWit s t a (b+1)
    change t l (b+1) - s.dual l a ≤ rresFunc s t a b
    have hmax : t l b - s.dual l a ≤ rresFunc s t a b :=
      rres_val_ge s t a b l
    have hstep : t l (b+1) ≤ t l b := (t.b_step l b).1
    omega
  · intro a
    suffices hEventuallyNonpos : ∃ B, ∀ b ≥ B, ∀ l,
        t l b - s.dual l a ≤ 0 by
      obtain ⟨B, hB⟩ := hEventuallyNonpos
      use B
      intro b hb
      apply le_antisymm
      · let l := rresWit s t a b
        change t l b - s.dual l a ≤ 0
        exact hB b hb l
      · exact rres_func_nonneg s t a b
    -- Paper proof, with `b` moving right: the positive set is finite after
    -- choosing an initial `b`, and each fixed middle `l` eventually leaves
    -- because `t(l,b) = 0` for `b ≫ 0`.
    let B₀ := a + s.χ + t.χ
    obtain ⟨Lₜ, hLₜ⟩ := t.small_a B₀
    obtain ⟨Uₜ, hUₜ⟩ := t.large_a B₀
    obtain ⟨Lₛ, hLₛ⟩ := s.dual.small_a a
    obtain ⟨Uₛ, hUₛ⟩ := s.dual.large_a a
    let L := min Lₜ Lₛ
    let U := max (max Uₜ Uₛ) L
    let middle := Finset.Icc L U
    have hmiddle_nonempty : middle.Nonempty := by
      refine ⟨L, ?_⟩
      simp only [Int.max_assoc, Finset.mem_Icc, le_refl, le_sup_iff, or_true, and_self, middle, U]
    let cutoffs := middle.image (fun l => Classical.choose (t.large_b l))
    have hcutoffs_nonempty : cutoffs.Nonempty := hmiddle_nonempty.image _
    let B₁ := cutoffs.max' hcutoffs_nonempty
    use max B₀ B₁
    intro b hb l
    have hb_B₀ : B₀ ≤ b := le_trans (le_max_left _ _) hb
    have hb_B₁ : B₁ ≤ b := le_trans (le_max_right _ _) hb
    have ht_le_B₀ : t l b ≤ t l B₀ := t.nondec (le_refl l) hb_B₀
    by_cases hl_left : l ≤ L
    · have htB₀ : t l B₀ = 0 := hLₜ l (le_trans hl_left (min_le_left _ _))
      have hs_nonneg : s.dual l a ≥ 0 := s.dual.nonneg l a
      omega
    · push Not at hl_left
      by_cases hl_right : U ≤ l
      · have hUₜ_le_l : Uₜ ≤ l :=
          le_trans (le_trans (le_max_left Uₜ Uₛ) (le_max_left _ L)) hl_right
        have hUₛ_le_l : Uₛ ≤ l :=
          le_trans (le_trans (le_max_right Uₜ Uₛ) (le_max_left _ L)) hl_right
        have htB₀ : t l B₀ = l - B₀ + t.χ := hUₜ l hUₜ_le_l
        have hs : s.dual l a = l - a - s.χ := by
          change s.dual l a = l - a + s.dual.χ
          exact hUₛ l hUₛ_le_l
        omega
      · push Not at hl_right
        have hl_mem : l ∈ middle := by
          simp only [Finset.mem_Icc, middle]
          omega
        let B_l := Classical.choose (t.large_b l)
        have hBl_mem : B_l ∈ cutoffs := by
          exact Finset.mem_image.mpr ⟨l, hl_mem, rfl⟩
        have hBl_le_B₁ : B_l ≤ B₁ := by
          exact Finset.le_max' cutoffs B_l hBl_mem
        have hBl_le_b : B_l ≤ b := le_trans hBl_le_B₁ hb_B₁
        have ht0 : t l b = 0 := by
          exact Classical.choose_spec (t.large_b l) b hBl_le_b
        have hs_nonneg : s.dual l a ≥ 0 := s.dual.nonneg l a
        omega
  · intro b
    suffices hEventuallyNonpos : ∃ A, ∀ a ≤ A, ∀ l,
        t l b - s.dual l a ≤ 0 by
      obtain ⟨A, hA⟩ := hEventuallyNonpos
      use A
      intro a ha
      apply le_antisymm
      · let l := rresWit s t a b
        change t l b - s.dual l a ≤ 0
        exact hA a ha l
      · exact rres_func_nonneg s t a b
    -- Paper proof, with `a` moving left: the left tail is zero, the right
    -- tail is controlled by the line inequality, and the middle interval is
    -- finite.
    obtain ⟨L₀, hL₀⟩ := t.small_a b
    obtain ⟨U₀, hU₀⟩ := t.large_a b
    let L := L₀
    let U := max U₀ L
    let middle := Finset.Icc L U
    have hmiddle_nonempty : middle.Nonempty := by
      refine ⟨L, ?_⟩
      simp only [Finset.mem_Icc, le_refl, le_sup_right, and_self, middle, U]
    let middleBounds := middle.image (fun l => l - s.χ - t l b)
    have hbounds_nonempty : middleBounds.Nonempty := hmiddle_nonempty.image _
    let A := middleBounds.min' hbounds_nonempty
    use min (b - s.χ - t.χ) A
    intro a ha l
    have ha_right : a ≤ b - s.χ - t.χ := le_trans ha (min_le_left _ _)
    have ha_middle : a ≤ A := le_trans ha (min_le_right _ _)
    have hsd_ge : s.dual l a ≥ l - a - s.χ := by
      change s.dual l a ≥ l - a + s.dual.χ
      exact s.dual.ge_diff l a
    by_cases hl_left : l ≤ L
    · have ht : t l b = 0 := hL₀ l hl_left
      have hs_nonneg : s.dual l a ≥ 0 := s.dual.nonneg l a
      omega
    · push Not at hl_left
      by_cases hl_right : U ≤ l
      · have hU₀_le_l : U₀ ≤ l := le_trans (le_max_left U₀ L) hl_right
        have ht : t l b = l - b + t.χ := hU₀ l hU₀_le_l
        omega
      · push Not at hl_right
        have hl_mem : l ∈ middle := by
          simp only [Finset.mem_Icc, middle]
          omega
        have hval_mem : l - s.χ - t l b ∈ middleBounds := by
          exact Finset.mem_image.mpr ⟨l, hl_mem, rfl⟩
        have hA_le_val : A ≤ l - s.χ - t l b := by
          exact Finset.min'_le middleBounds (l - s.χ - t l b) hval_mem
        omega

private lemma lres_rres_dual_eq (s t : SlipFace) (a b : ℤ) :
    lresFunc s t a b - rresFunc t.dual s.dual b a = a - b + s.χ + t.χ := by
  -- Proof written by GPT 5.5.
  let C := a - b + s.χ + t.χ
  suffices lresFunc s t a b ≤ rresFunc t.dual s.dual b a + C ∧
      rresFunc t.dual s.dual b a + C ≤ lresFunc s t a b by
    omega
  constructor
  · let l := lresWit s t a b
    change s a l - t.dual b l ≤ rresFunc t.dual s.dual b a + C
    have hmax : s.dual l a - t l b ≤ rresFunc t.dual s.dual b a := by
      have h := rres_val_ge t.dual s.dual b a l
      rwa [SlipFace.dual_dual t] at h
    linarith [s.s_eq a l, t.s'_eq b l, hmax]
  · let l := rresWit t.dual s.dual b a
    change s.dual l a - (t.dual).dual l b + C ≤ lresFunc s t a b
    have htdd : (t.dual).dual l b = t l b := by
      rw [SlipFace.dual_dual t]
    have hmax : s a l - t.dual b l ≤ lresFunc s t a b :=
      lres_val_ge s t a b l
    linarith [s.s_eq a l, t.s'_eq b l, htdd, hmax]

private lemma lres_exists (s t : SlipFace) : ∃ p : SlipFace,
    ((p.func = lresFunc s t ∧ p.χ = s.χ + t.χ)
    ∧ p.dual.func = rresFunc t.dual s.dual) := by
  -- Proof written by GPT 5.5.
  let P := lresFunc s t
  let P' := rresFunc t.dual s.dual
  let χ := s.χ + t.χ
  have hdual : ∀ a b : ℤ, P a b - P' b a = a - b + χ := by
    intro a b
    rw [lres_rres_dual_eq s t a b]
    omega
  have h := sf_of_D_props hdual
  suffices D_props P ∧ D_props P' by
    exact h this
  exact ⟨D_props_of_lres_func s t, D_props_of_rres_func t.dual s.dual⟩

/-- The left residual of two slipfaces, obtained from the maximum formula
`lresFunc`. See *Definition 3.7* (`defn:sfAlgebra`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227). -/
noncomputable def lres (s t : SlipFace) : SlipFace :=
  Classical.choose (lres_exists s t)

/-- Infix notation for the slipface left residual. -/
infixl:70 " ◃ " => lres

lemma lres_func_eq (s t : SlipFace) : (s ◃ t).func = lresFunc s t :=
  (Classical.choose_spec (lres_exists s t)).1.1

lemma lres_wit_spec (s t : SlipFace) (a b : ℤ) :
    (s ◃ t) a b = s a (lresWit s t a b) - t.dual b (lresWit s t a b) := by
  rw [lres_func_eq]
  rfl

/-- The left residual $s \triangleleft t$ of slipfaces satisfies the defining equation
$(s ◃ t)(a,b) = \max_{\ell \in \mathbb{Z}} (s(a,\ell) - t^\vee(b,\ell))$.
This is simply an unwinding of the formal definition to obtain the formula as stated in
*Definition 3.7* (`defn:sfAlgebra`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 2/3.* -/
lemma lres_eq_max (s t : SlipFace) (a b : ℤ) :
    IsGreatest {s a l - t.dual b l | l : ℤ} ((s ◃ t) a b) := by
    constructor
    · exact ⟨_, Eq.symm (lres_wit_spec s t a b)⟩
    · rintro x ⟨l, rfl⟩
      rw [lres_wit_spec]
      apply lres_val_ge

/-- The shift is additive under left residual.
*Proposition 3.9* (`prop:sfAlgebraDefined`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 3/6.* -/
@[simp] lemma chi_lres (s t : SlipFace) : (s ◃ t).χ = s.χ + t.χ := by
  have h := lres_exists s t
  exact (Classical.choose_spec h).1.2

/-- The right residual of two slipfaces, defined by duality from left
residual. See *Definition 3.7* (`defn:sfAlgebra`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227). -/
noncomputable def rres (s t : SlipFace) : SlipFace :=
  (t.dual ◃ s.dual).dual

/-- Infix notation for the slipface right residual. -/
infixr:70 " ▹ " => rres

lemma rres_func_eq (s t : SlipFace) : (s ▹ t).func = rresFunc s t := by
  dsimp [rres]
  calc
    (t.dual ◃ s.dual).dual.func = rresFunc s.dual.dual t.dual.dual :=
      (Classical.choose_spec (lres_exists t.dual s.dual)).2
    _ = rresFunc s t := by rw [SlipFace.dual_dual s, SlipFace.dual_dual t]

lemma rres_wit_spec (s t : SlipFace) (a b : ℤ) :
    (s ▹ t) a b = t (rresWit s t a b) b - s.dual (rresWit s t a b) a := by
  rw [rres_func_eq]
  rfl

/-- The right residual $s \triangleright t$ of slipfaces satisfies the defining equation
$(s ▹ t)(a,b) = \max_{\ell \in \mathbb{Z}} (t(\ell,b) - s^\vee(\ell,a))$.
This is simply an unwinding of the formal definition to obtain the formula as stated in
*Definition 3.7* (`defn:sfAlgebra`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 3/3.* -/
lemma rres_eq_max (s t : SlipFace) (a b : ℤ) :
    IsGreatest {t l b - s.dual l a | l : ℤ} ((s ▹ t) a b) := by
    constructor
    · exact ⟨_, Eq.symm (rres_wit_spec s t a b)⟩
    · rintro x ⟨l, rfl⟩
      rw [rres_wit_spec]
      apply rres_val_ge

/-- The shift is additive under right residual.
*Proposition 3.9* (`prop:sfAlgebraDefined`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 4/6.* -/
@[simp] lemma chi_rres (s t : SlipFace) : (s ▹ t).χ = s.χ + t.χ := by
  dsimp [rres, SlipFace.dual]
  simp_all

/-- The stated left/right residual duality.
*Proposition 3.9 (`prop:sfAlgebraDefined`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 5/6.* -/
@[simp] lemma lres_dual (s t : SlipFace) :
    (s ◃ t).dual = t.dual ▹ s.dual := by
  dsimp [rres]
  rw [SlipFace.dual_dual s, SlipFace.dual_dual t]

/-- The corresponding right/left residual duality, obtained by applying the
left/right duality to dual slipfaces.
*Consequence of Proposition 3.9 (`prop:sfAlgebraDefined`) in
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 6/6.* -/
@[simp] lemma rres_dual (s t : SlipFace) :
    (s ▹ t).dual = t.dual ◃ s.dual := by
  dsimp [rres]
  rw [SlipFace.dual_dual]

/-- A small set on which witnesses to the value $s \star t (a,b)$ always occur.
*Lemma 3.13 (`lem:setL`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 1/5.* -/
def bendSet (t : SlipFace) (b : ℤ) : Set ℤ :=
  {l : ℤ | t (l-1) b = t l b ∧ t l b ≠ t (l+1) b}

/-- *Lemma 3.13 (`lem:setL`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 2/5.* -/
lemma bend_set_finite (t : SlipFace) (b : ℤ) : Finite (bendSet t b) := by
  obtain ⟨A1, hA1⟩ := t.large_a b
  obtain ⟨A0, hA0⟩ := t.small_a b
  have : bendSet t b ⊆ Finset.Icc A0 A1 := by
    rintro l ⟨hl_left,hl_right⟩
    rw [Finset.mem_coe, Finset.mem_Icc]
    constructor
    · contrapose! hl_right with l_lt_A0
      rw [hA0 l (by omega), hA0 (l+1) (by omega)]
    · contrapose! hl_left with A1_lt_l
      rw [hA1 (l-1) (by omega), hA1 l (by omega)]
      omega
  apply Set.Finite.subset _ this
  apply Finset.finite_toSet

private lemma bend_set_witness_helper (s t : SlipFace) (a b l : ℤ) (hl : t l b ≠ t (l + 1) b) :
  ∃ m : ℤ, t (m-1) b = t m b ∧ t m b ≠ t (m+1) b ∧ s a m + t m b ≤ s a l + t l b := by
  by_cases h : t (l-1) b = t l b
  · use l
  have hl' : t (l-1) b ≠ t ((l-1)+1) b := by
    simp_all
  obtain ⟨m, ⟨teq, tneq, sumle⟩⟩ := bend_set_witness_helper s t a b (l-1) hl'
  use m, teq, tneq
  apply le_trans sumle
  have hs_step := s.b_step a (l-1)
  have ht_step := t.a_step (l-1) b
  have hs_le : s a (l-1) ≤ s a l + 1 := by
    simp_all
  have ht_eq : t l b = t (l-1) b + 1 := by
    have hpred_succ : l - 1 + 1 = l := sub_add_cancel l 1
    rw [hpred_succ] at ht_step
    omega
  omega
termination_by (t l b).toNat
decreasing_by
  simp_wf
  have ht_step := t.a_step (l - 1) b
  have hpred_succ : l - 1 + 1 = l := sub_add_cancel l 1
  rw [hpred_succ] at ht_step
  have ht_nonneg : 0 ≤ t (l - 1) b := t.nonneg (l - 1) b
  omega

/-- *Lemma 3.13 (`lem:setL`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 3/5.* -/
lemma bend_set_witness (s t : SlipFace) (a b : ℤ) :
  ∃ l ∈ bendSet t b, (s ⋆ t) a b = s a l + t l b := by
  -- Proof written by GPT 5.5.
  let v := SlipValley s t a b
  have hM_right : t v.M b ≠ t (v.M + 1) b := by
    intro ht_eq
    have hstrict : v.f (v.M + 1) > v.f v.M := (v.M_spec (v.M + 1)).2 (by omega)
    have hs_step : s a (v.M + 1) ≤ s a v.M := (s.b_step a v.M).1
    have hle : v.f (v.M + 1) ≤ v.f v.M := by
      change s a (v.M + 1) + t (v.M + 1) b ≤ s a v.M + t v.M b
      omega
    omega
  obtain ⟨m, ⟨hm_left, hm_right, hm_le⟩⟩ :=
    bend_set_witness_helper s t a b v.M hM_right
  use m
  constructor
  · exact ⟨hm_left, hm_right⟩
  · have hstarM : (s ⋆ t) a b = s a v.M + t v.M b := by
      rw [star_func_eq]
      exact Eq.symm v.f_M
    have hM_le_m : s a v.M + t v.M b ≤ s a m + t m b := by
      exact (v.M_spec m).1
    have hm_eq : s a m + t m b = s a v.M + t v.M b := le_antisymm hm_le hM_le_m
    rw [hstarM, hm_eq]

private lemma bend_set_witness_lres_right_helper (s t : SlipFace) (a b l : ℤ)
    (hmax : ∀ n, s a n - t.dual b n ≤ s a l - t.dual b l) :
    ∃ m : ℤ, t m b ≠ t (m+1) b ∧
      s a l - t.dual b l ≤ s a m - t.dual b m := by
  -- Proof written by GPT 5.5.
  by_cases hright : t l b = t (l+1) b
  · have hdual : t.dual b (l+1) = t.dual b l - 1 := by
      rw [t.s'_eq b (l+1), t.s'_eq b l, hright]
      omega
    have hs_step := s.b_step a l
    have hle_next : s a l - t.dual b l ≤ s a (l+1) - t.dual b (l+1) := by
      omega
    have hge_next : s a (l+1) - t.dual b (l+1) ≤ s a l - t.dual b l :=
      hmax (l+1)
    have hs_drop : s a (l+1) = s a l - 1 := by
      omega
    have hmax_next :
        ∀ n, s a n - t.dual b n ≤ s a (l+1) - t.dual b (l+1) := by
      simp_all
    obtain ⟨m, hm_right, hm_le⟩ :=
      bend_set_witness_lres_right_helper s t a b (l+1) hmax_next
    use m, hm_right
    exact le_trans hle_next hm_le
  · use l, hright
termination_by (s a l).toNat
decreasing_by
  simp_wf
  have hnonneg : 0 ≤ s a (l+1) := s.nonneg a (l+1)
  omega

private lemma bend_set_witness_lres_helper (s t : SlipFace) (a b l : ℤ)
    (hl : t l b ≠ t (l + 1) b) :
    ∃ m : ℤ, t (m-1) b = t m b ∧ t m b ≠ t (m+1) b ∧
      s a l - t.dual b l ≤ s a m - t.dual b m := by
  -- Proof written by GPT 5.5.
  by_cases h : t (l-1) b = t l b
  · use l, h, hl
  have hl' : t (l-1) b ≠ t ((l-1)+1) b := by
    simp_all
  obtain ⟨m, hm_left, hm_right, hm_le⟩ :=
    bend_set_witness_lres_helper s t a b (l-1) hl'
  use m, hm_left, hm_right
  have hs_step := s.b_step a (l-1)
  have ht_step := t.a_step (l-1) b
  have ht_eq : t l b = t (l-1) b + 1 := by
    have hpred_succ : l - 1 + 1 = l := sub_add_cancel l 1
    rw [hpred_succ] at ht_step
    omega
  have hdual : t.dual b (l-1) = t.dual b l := by
    rw [t.s'_eq b (l-1), t.s'_eq b l, ht_eq]
    omega
  have hs_le : s a l ≤ s a (l-1) := by
    simp_all
  have hcurr_prev : s a l - t.dual b l ≤ s a (l-1) - t.dual b (l-1) := by
    simp_all
  exact le_trans hcurr_prev hm_le
termination_by (t l b).toNat
decreasing_by
  simp_wf
  have ht_step := t.a_step (l - 1) b
  have hpred_succ : l - 1 + 1 = l := sub_add_cancel l 1
  rw [hpred_succ] at ht_step
  have ht_nonneg : 0 ≤ t (l - 1) b := t.nonneg (l - 1) b
  omega

/-- *Lemma 3.13 (`lem:setL`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 4/5.* -/
lemma bend_set_witness_lres (s t : SlipFace) (a b : ℤ) :
    ∃ l ∈ bendSet t b, (s ◃ t) a b = s a l - t.dual b l := by
  -- Proof written by GPT 5.5.
  let l := lresWit s t a b
  have hmax : ∀ n, s a n - t.dual b n ≤ s a l - t.dual b l := by
    intro n
    change s a n - t.dual b n ≤ s a (lresWit s t a b) - t.dual b (lresWit s t a b)
    exact lres_val_ge s t a b n
  obtain ⟨r, hr_right, hlr⟩ := bend_set_witness_lres_right_helper s t a b l hmax
  obtain ⟨m, hm_left, hm_right, hrm⟩ := bend_set_witness_lres_helper s t a b r hr_right
  use m
  constructor
  · exact ⟨hm_left, hm_right⟩
  · rw [lres_wit_spec]
    apply le_antisymm
    · exact le_trans hlr hrm
    · exact hmax m

/-!
  ## Minimal slipfaces in each shift
-/

/-- The slipface $s_{\iota_n}$, which is the minimal slipface of shift $n$.
It is given simply by $s(a,b) = \max(a - b + n, 0)$.
-/
def iotaSf (n : ℤ) : SlipFace  := {
  func := fun a b => max (a - b + n) 0
  χ := n
  a_step := by
    intro a b
    by_cases h : 0 ≤ a - b + n
    · have h' : 0 ≤ a + 1 - b + n := by omega
      simp [h,h']
      omega
    · have h' : a + 1 - b + n ≤ 0 := by omega
      simp [h']
      omega
  b_step := by
    intro a b
    by_cases h : 0 < a - b + n
    · have h' : 0 ≤ a - (b+1) + n := by omega
      simp [h']
      omega
    · have h' : a - (b+1) + n ≤ 0 := by omega
      simp_all
  nonneg := by
    simp_all
  ge_diff := by
    simp_all
  small_a := by
    intro a
    use a - n
    intro b hb
    apply Int.max_eq_right
    omega
  large_a := by
    intro a
    use a - n
    intro b hb
    apply Int.max_eq_left
    omega
  small_b := by
    intro b
    use b + n
    intro a ha
    apply Int.max_eq_left
    omega
  large_b := by
    intro b
    use b + n
    intro a ha
    apply Int.max_eq_right
    omega
}

private lemma bend_set_iota (n b : ℤ) : bendSet (iotaSf n) b = {b - n} := by
  ext m
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    have mle : m ≤ b - n := by
      by_contra!
      rw [show iotaSf n (m-1) b = m -1 - b + n  by exact max_eq_left (by omega)] at h1
      rw [show iotaSf n m b = m - b + n by exact max_eq_left (by omega)] at h1 h2
      simp_all
    have mge : b - n ≤ m := by
      by_contra!
      rw [show iotaSf n (m-1) b = 0 by exact max_eq_right (by omega)] at h1
      rw [show iotaSf n m b = 0 by exact max_eq_right (by omega)] at h1 h2
      rw [show iotaSf n (m+1) b = 0 by exact max_eq_right (by omega)] at h2
      omega
    rw [antisymm mle mge]
    rfl
  · intro h
    rw [show m = b - n by exact h]
    constructor <;>  rw [show iotaSf n (b-n) b = 0 by exact max_eq_right (by omega)]
    · rw [show iotaSf n (b-n-1) b = 0 by exact max_eq_right (by omega)]
    · rw [show iotaSf n (b-n+1) b = b-n+1-b+n by exact max_eq_left (by omega)]
      omega

/-!
  ## Monotonicity, adjointness, and associativity
-/

/-- The $\star$ operation is Bruhat-increasing in both arguments.
*Lemma 3.8 (`lem:compatLeq`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 1/3.* -/
lemma star_mono {s₁ s₂ t₁ t₂ : SlipFace}
    (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) :
    s₁ ⋆ t₁ ≤ s₂ ⋆ t₂ := by
  -- Proof written by GPT 5.5.
  intro a b
  apply (le_star_val_iff (s₁ ⋆ t₁) s₂ t₂ a b).mpr
  intro l
  have hval : (s₁ ⋆ t₁) a b ≤ s₁ a l + t₁ l b := star_val_le s₁ t₁ a b l
  have hsval : s₁ a l ≤ s₂ a l := hs a l
  have htval : t₁ l b ≤ t₂ l b := ht l b
  omega

/-- The residual `(s, t) ↦ s ◃ t.dual` is increasing in `s` and decreasing in
`t`.
*Lemma 3.8 (`lem:compatLeq`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 2/3.* -/
lemma lres_mono {s₁ s₂ t₁ t₂ : SlipFace}
    (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) :
    s₁ ◃ t₂.dual ≤ s₂ ◃ t₁.dual := by
  -- Proof written by GPT 5.5.
  intro a b
  let l := lresWit s₁ t₂.dual a b
  rw [lres_wit_spec]
  change s₁ a l - (t₂.dual).dual b l ≤ (s₂ ◃ t₁.dual) a b
  have hmax : s₂ a l - t₁ b l ≤ (s₂ ◃ t₁.dual) a b := by
    rw [lres_wit_spec]
    have h := lres_val_ge s₂ t₁.dual a b l
    rwa [SlipFace.dual_dual t₁] at h
  have hsval : s₁ a l ≤ s₂ a l := hs a l
  have htval : t₁ b l ≤ t₂ b l := ht b l
  have htdd : (t₂.dual).dual b l = t₂ b l := by
    rw [SlipFace.dual_dual t₂]
  omega

/-- The residual `(s, t) ↦ t.dual ▹ s` is increasing in `s` and decreasing in
`t`.
*Lemma 3.8 (`lem:compatLeq`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 3/3.* -/
lemma rres_mono {s₁ s₂ t₁ t₂ : SlipFace}
    (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) :
    t₂.dual ▹ s₁ ≤ t₁.dual ▹ s₂ := by
  -- Proof written by GPT 5.5.
  intro a b
  let l := rresWit t₂.dual s₁ a b
  rw [rres_wit_spec]
  change s₁ l b - (t₂.dual).dual l a ≤ (t₁.dual ▹ s₂) a b
  have hmax : s₂ l b - t₁ l a ≤ (t₁.dual ▹ s₂) a b := by
    rw [rres_wit_spec]
    have h := rres_val_ge t₁.dual s₂ a b l
    rwa [SlipFace.dual_dual t₁] at h
  have hsval : s₁ l b ≤ s₂ l b := hs l b
  have htval : t₁ l a ≤ t₂ l a := ht l a
  have htdd : (t₂.dual).dual l a = t₂ l a := by
    rw [SlipFace.dual_dual t₂]
  omega

/-- The left residual $u \triangleleft t^∨$ as a Bruhat minimum: the minimum
slipface such that $s \star t ≥ u$.
*Lemma 3.10 (`lem:sfOpChar`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 1/2.* -/
lemma ge_star_iff_ge_lres (s t u : SlipFace) :
    s ≥ u ◃ t.dual ↔ s ⋆ t ≥ u := by
  -- Proof written by GPT 5.5.
  constructor
  · intro h a b
    apply (le_star_val_iff u s t a b).mpr
    intro l
    have hresidual : u a b - t l b ≤ (u ◃ t.dual) a l := by
      rw [lres_wit_spec]
      have hval := lres_val_ge u t.dual a l b
      rwa [SlipFace.dual_dual t] at hval
    have hs : (u ◃ t.dual) a l ≤ s a l := h a l
    omega
  · intro h a l
    let b := lresWit u t.dual a l
    rw [lres_wit_spec]
    change u a b - (t.dual).dual l b ≤ s a l
    have hstar : u a b ≤ (s ⋆ t) a b := h a b
    have hval : (s ⋆ t) a b ≤ s a l + t l b := star_val_le s t a b l
    have hdd : (t.dual).dual l b = t l b := by
      rw [SlipFace.dual_dual t]
    omega

/-- The right residual $s^∨ \triangleright u$ as a Bruhat minimum: the minimum
slipface such that $s \star t ≥ u$.
*Lemma 3.10 (`lem:sfOpChar`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 2/2.* -/
lemma ge_star_iff_ge_rres (s t u : SlipFace) :
    t ≥ s.dual ▹ u ↔ s ⋆ t ≥ u := by
  -- Proof written by GPT 5.5.
  constructor
  · intro h a b
    apply (le_star_val_iff u s t a b).mpr
    intro l
    have hresidual : u a b - s a l ≤ (s.dual ▹ u) l b := by
      rw [rres_wit_spec]
      have hval := rres_val_ge s.dual u l b a
      rwa [SlipFace.dual_dual s] at hval
    have ht : (s.dual ▹ u) l b ≤ t l b := h l b
    omega
  · intro h l b
    let a := rresWit s.dual u l b
    rw [rres_wit_spec]
    change u a b - (s.dual).dual a l ≤ t l b
    have hstar : u a b ≤ (s ⋆ t) a b := h a b
    have hval : (s ⋆ t) a b ≤ s a l + t l b := star_val_le s t a b l
    have hdd : (s.dual).dual a l = s a l := by
      rw [SlipFace.dual_dual s]
    omega

/-- Left residual associates with the product on the right.
*Lemma 3.12 (`lem:sfAlgebra`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 2/3.* -/
lemma lres_assoc (s t u : SlipFace) :
    (s ◃ t) ◃ u = s ◃ (t ⋆ u) := by
  -- Proof written by GPT 5.5.
  have hmin (v : SlipFace) :
      v ≥ (s ◃ t) ◃ u ↔ v ≥ s ◃ (t ⋆ u) := by
    calc
      v ≥ (s ◃ t) ◃ u ↔ v ⋆ u.dual ≥ s ◃ t := by
        simpa only [SlipFace.dual_dual] using
          (ge_star_iff_ge_lres v u.dual (s ◃ t))
      _ ↔ (v ⋆ u.dual) ⋆ t.dual ≥ s := by
        simpa only [SlipFace.dual_dual] using
          (ge_star_iff_ge_lres (v ⋆ u.dual) t.dual s)
      _ ↔ v ⋆ (t ⋆ u).dual ≥ s := by
        rw [star_assoc, star_dual]
      _ ↔ v ≥ s ◃ (t ⋆ u) := by
        symm
        simpa only [SlipFace.dual_dual] using
          (ge_star_iff_ge_lres v (t ⋆ u).dual s)
  apply le_antisymm
  · exact (hmin (s ◃ (t ⋆ u))).mpr (le_refl _)
  · exact (hmin ((s ◃ t) ◃ u)).mp (le_refl _)

/-- Right residual associates with the product on the left.
*Lemma 3.12 (`lem:sfAlgebra`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 3/3.* -/
lemma rres_assoc (s t u : SlipFace) :
    s ▹ (t ▹ u) = (s ⋆ t) ▹ u := by
  -- Proof written by GPT 5.5.
  have hmin (v : SlipFace) :
      v ≥ s ▹ (t ▹ u) ↔ v ≥ (s ⋆ t) ▹ u := by
    calc
      v ≥ s ▹ (t ▹ u) ↔ s.dual ⋆ v ≥ t ▹ u := by
        simpa only [SlipFace.dual_dual] using
          (ge_star_iff_ge_rres s.dual v (t ▹ u))
      _ ↔ t.dual ⋆ (s.dual ⋆ v) ≥ u := by
        simpa only [SlipFace.dual_dual] using
          (ge_star_iff_ge_rres t.dual (s.dual ⋆ v) u)
      _ ↔ (s ⋆ t).dual ⋆ v ≥ u := by
        rw [← star_assoc, star_dual]
      _ ↔ v ≥ (s ⋆ t) ▹ u := by
        symm
        simpa only [SlipFace.dual_dual] using
          (ge_star_iff_ge_rres (s ⋆ t).dual v u)
  apply le_antisymm
  · exact (hmin ((s ⋆ t) ▹ u)).mpr (le_refl _)
  · exact (hmin (s ▹ (t ▹ u))).mp (le_refl _)

/-! ### The mixed difference `Δ`

This section studies the discrete mixed difference `Δ`, its behavior under
duality, and the finite summation identities used later in submodularity
arguments. -/

/-- The mixed difference
$$
\Delta s(a,b) = s(a+1,b) - s(a,b) - s(a+1,b+1) + s(a,b+1).
$$

In Lean this is written `sf.Δ a b`. -/
def Δ (a b : ℤ) : ℤ :=
  sf (a+1) b - sf a b - sf (a+1) (b+1) + sf a (b+1)

/-- Duality preserves the mixed difference `Δ` after swapping the coordinates.
*Equation (20) (`eq:DeltasDual`) of [An extended Demazure product](https://arxiv.org/abs/2206.14227).* -/
lemma Δ_dual (a b : ℤ) : sf.dual.Δ b a = sf.Δ a b := by
  dsimp [SlipFace.dual, Δ]
  omega

lemma Δ_values (a b : ℤ) : sf.Δ a b = 0 ∨ sf.Δ a b = 1 ∨ sf.Δ a b = -1 := by
  suffices sf.Δ a b ≥ -1 ∧ sf.Δ a b ≤ 1 by omega
  let d1 := sf (a+1) b - sf a b
  let d2 := sf (a+1) (b+1) - sf a (b+1)
  have diff : sf.Δ a b = d1 - d2 := by (dsimp [Δ]; omega)
  suffices d1 - d2 ≥ -1 ∧ d1 - d2 ≤ 1 by (rw [diff]; simpa)
  obtain ⟨h11, h12⟩ := sf.a_step a b
  obtain ⟨h21, h22⟩ := sf.a_step a (b+1)
  omega

lemma Δ_zero_of_s_zero (a b : ℤ) (h0 : sf (a + 1) b = 0) : sf.Δ a b = 0 := by
  have h1 : sf a b = 0 := by
    apply sf.zero_below (a' := a+1) (b' := b)
    repeat linarith
  have h2 : sf (a+1) (b+1) = 0 := by
    apply sf.zero_below (a' := a+1) (b' := b)
    repeat linarith
  have h3 : sf a (b+1) = 0 := by
    apply sf.zero_below (a' := a+1) (b' := b)
    repeat linarith
  dsimp [Δ]
  simp_all

lemma sum_a {a₁ a₂ : ℤ} (ha : a₁ ≤ a₂) (b : ℤ) :
  ∑ a ∈ Finset.Ico a₁ a₂, sf.Δ a b
  = (sf a₂ b  - sf a₂ (b+1)) - (sf a₁ b - sf a₁ (b+1)) := by
  let n : ℕ := (a₂ - a₁).toNat
  have a₂_eq : a₂ = a₁ + n := by omega
  rw [a₂_eq]
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Nat.cast_add n 1, Nat.cast_one, ← add_assoc]
    have disj : Disjoint (Finset.Ico a₁ (a₁ + n)) {a₁ + n} := by simp
    have union : Finset.Ico a₁ (a₁ + n + 1) = Finset.Ico a₁ (a₁ + n) ∪ {a₁ + n} := by
      apply Finset.ext
      intro x
      repeat rw [Finset.mem_union, Finset.mem_Ico, Finset.mem_Ico]
      grind
    rw [union, Finset.sum_union disj, Finset.sum_singleton, SlipFace.Δ, ih]
    omega

lemma sum_b (a : ℤ) {b₁ b₂ : ℤ} (hb : b₁ ≤ b₂) :
  ∑ b ∈ Finset.Ico b₁ b₂, sf.Δ a b
  = (sf (a+1) b₁ - sf a b₁) - (sf (a+1) b₂ - sf a b₂) := by
  let n : ℕ := (b₂ - b₁).toNat
  have b₂_eq : b₂ = b₁ + n := by omega
  rw [b₂_eq]
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Nat.cast_add n 1, Nat.cast_one, ← add_assoc]
    have disj : Disjoint (Finset.Ico b₁ (b₁ + n)) {b₁ + n} := by simp
    have union : Finset.Ico b₁ (b₁ + n + 1) = Finset.Ico b₁ (b₁ + n) ∪ {b₁ + n} := by
      apply Finset.ext
      intro x
      repeat rw [Finset.mem_union, Finset.mem_Ico, Finset.mem_Ico]
      grind
    rw [union, Finset.sum_union disj, Finset.sum_singleton, SlipFace.Δ, ih]
    omega

/-- Summing `Δ` over a rectangle recovers the corresponding boundary term in
`sf`. *Modification of Equation (19) (`eq:sumDelta`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227) to a finite sum.* -/
lemma sum_ab {a₁ a₂ b₁ b₂ : ℤ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
  ∑ b ∈ Finset.Ico b₁ b₂, ∑ a ∈ Finset.Ico a₁ a₂, sf.Δ a b
  = (sf a₂ b₁ - sf a₁ b₁) - (sf a₂ b₂ - sf a₁ b₂) := by
  let n : ℕ := (b₂ - b₁).toNat
  have b₂_eq : b₂ = b₁ + n := by omega
  rw [b₂_eq]
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Nat.cast_add n 1, Nat.cast_one, ← add_assoc]
    have disj : Disjoint (Finset.Ico b₁ (b₁ + n)) {b₁ + n} := by simp
    have union : Finset.Ico b₁ (b₁ + n + 1) = Finset.Ico b₁ (b₁ + n) ∪ {b₁ + n} := by
      apply Finset.ext
      intro x
      repeat rw [Finset.mem_union, Finset.mem_Ico, Finset.mem_Ico]
      grind
    rw [union, Finset.sum_union disj, Finset.sum_singleton, ih, sf.sum_a ha (b₁ + n)]
    omega

/-- A slipface is submodular if $\Delta s(a,b) \ge 0$ for all `a, b`.
*Definition 4.2 (`defn:submodular`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).* -/
def submodular : Prop := ∀ a b : ℤ, sf.Δ a b ≥ 0

/-- The set of boxes where the mixed difference `Δ` is equal to `1`,
as defined in the proof of *Proposition 4.3* (`prop:imageASP`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).* -/
def Γ : Set (ℤ × ℤ) := {(a, b) | sf.Δ a b = 1}

lemma Γ_dual : ∀ (a b : ℤ), (a, b) ∈ sf.Γ ↔ (b, a) ∈ sf.dual.Γ := by
  intro a b
  simp only [Γ, Set.mem_setOf_eq, sf.Δ_dual]

/-! ## The essential set of a slipface

This section includes the content of §7.1 of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), about the essential set of a
slipface.
-/

/-- The *essential set* of a slipface $s$ is the set
  $\operatorname{Ess}(s) = \{ (a,b) \in \mathbb{Z}^2:
s(a-1,b) < s(a,b) = s(a+1,b) \mbox{ and } s(a,b+1) < s(a,b) = s(a,b-1) \}.$
-/
def ess : Set (ℤ × ℤ) := {(a, b) | sf (a-1) b < sf a b ∧ sf a b = sf (a+1) b
  ∧ sf a (b+1) < sf a b ∧ sf a b = sf a (b-1)}

/-- Lemma 7.2 (`lem:essSetMoves`) of [An extended Demazure product](https://arxiv.org/abs/2206.14227).
-/
lemma ess_step (s t : SlipFace) (a b : ℤ) (wit : s a b > t a b) :
  ¬ (a, b) ∈ s.ess →
    ∃ (a' b' : ℤ), ⟨a', b'⟩ ∈ ({ (a-1,b), (a+1,b), (a,b-1), (a,b+1) } : Set (ℤ × ℤ) ) ∧
    s a' b' > t a' b' ∧ s a b + s.dual b a < s a' b' + s.dual b' a' := by
    let steps : Set (ℤ × ℤ) := {(a-1,b), (a+1,b), (a,b-1), (a,b+1)}
    have fsub (sf : SlipFace) (a b : ℤ) : sf a b + sf.dual b a = 2 * sf a b - a + b - sf.χ := by
      linarith [sf.duality a b]
    intro not_ess
    contrapose! not_ess with h
    -- The casework below is quite repetitive. There may be a way to refactor it, similarly
    -- to how it's written in the paper.
    have h1 : s (a-1) b < s a b := by
      have : (a-1, b) ∈ steps := by
        simp [steps]
      by_cases h' : s (a-1) b > t (a-1) b
      · specialize h (a-1) b this h'
        rw [fsub s (a-1) b, fsub s a b] at h
        omega
      · contrapose! h'
        have : t (a-1) b ≤ t a b := by
          have := (t.a_step (a-1) b).1
          convert this; norm_num
        omega
    have h2 : s a b = s (a+1) b := by
      have : (a+1, b) ∈ steps := by
        simp [steps]
      by_cases h' : s (a+1) b > t (a+1) b
      · specialize h (a+1) b this h'
        rw [fsub s (a+1) b, fsub s a b] at h
        have := (s.a_step a b).1
        omega
      · push Not at h'
        apply le_antisymm (s.a_step a b).1
        have := (t.a_step a b).2
        omega
    have h3 : s a (b+1) < s a b := by
      have : (a, b+1) ∈ steps := by
        simp [steps]
      by_cases h' : s a (b+1) > t a (b+1)
      · specialize h a (b+1) this h'
        rw [fsub s a (b+1), fsub s a b] at h
        omega
      · push Not at h'
        have := (t.b_step a b).1
        omega
    have h4 : s a b = s a (b-1) := by
      have : (a, b-1) ∈ steps := by
        simp [steps]
      by_cases h' : s a (b-1) > t a (b-1)
      · specialize h a (b-1) this h'
        rw [fsub s a (b-1), fsub s a b] at h
        have := (s.b_step a (b-1)).1
        norm_num at this
        omega
      · push Not at h'
        have := (t.b_step a (b-1)).2
        norm_num at this
        apply le_antisymm
        · have := (s.b_step a (b-1)).1
          simp_all
        · omega
    exact ⟨h1, h2, h3, h4⟩

private lemma ess_seeker (s t : SlipFace) (nle : ¬ s ≤ t) (M : ℕ) :
  ∃ (a b : ℤ), s a b > t a b ∧ ( (a,b) ∈ s.ess ∨ s a b + s.dual b a ≥ M) := by
  induction M with
  | zero =>
    contrapose! nle with le
    intro a b; specialize le a b
    by_contra! lt
    obtain ⟨_, lt_zero⟩ := le lt
    have nn1 := s.nonneg a b
    have nn2 := s.dual.nonneg b a
    omega
  | succ M ih =>
    rcases ih with ⟨a, b, s_gt_t, (ab_ess | ab_ge_M)⟩
    · use a, b, s_gt_t
      left; exact ab_ess
    · by_cases ab_ess : (a, b) ∈ s.ess
      · use a, b, s_gt_t
        left; exact ab_ess
      obtain ⟨a', b', _, s'_gt_t', sum_ineq⟩ :=  ess_step s t a b s_gt_t ab_ess
      use a', b', s'_gt_t'
      right
      omega

/-- *Definition 7.3 (`defn:cliffordSF`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).* -/
def isClifford : Prop := ∃ (M : ℕ),
  ∀ a b : ℤ, sf a b + sf.dual b a ≥ M → sf a b = 0 ∨ sf.dual b a = 0

private lemma le_of_ess_le (s t : SlipFace) (cliff : s.isClifford) (chile : s.χ ≤ t.χ)
  (ess_le : ∀ (a b : ℤ), (a, b) ∈ s.ess → s a b ≤ t a b) :
  s ≤ t := by
  obtain ⟨M, cliff_cond⟩ := cliff
  contrapose! ess_le with nle
  obtain ⟨a, b, s_gt_t, (ab_ess | ab_ge_M)⟩ := ess_seeker s t nle M
  · exact ⟨a, b, ab_ess, s_gt_t⟩
  · exfalso
    obtain (s_zero | s'_zero) := cliff_cond a b ab_ge_M
    · rw [s_zero] at s_gt_t
      have := t.nonneg a b
      omega
    · rw [s.s_eq a b, t.s_eq a b, s'_zero] at s_gt_t
      have := t.dual.nonneg b a
      omega

theorem ess_clifford (s t : SlipFace) (cliff : s.isClifford) :
  s ≤ t ↔ s.χ ≤ t.χ ∧ ∀ (a b : ℤ), (a, b) ∈ s.ess → s a b ≤ t a b := by
  constructor
  · intro s_le_t
    have chile : s.χ ≤ t.χ := by
      obtain ⟨b, hb⟩ := t.dual.small_a 0
      have t_zero := hb b (le_refl _)
      rw [t.s'_eq b 0] at t_zero
      have h_t : t.χ = t 0 b + b := by omega
      have h_s : s.χ ≤ s 0 b + b := by
        have h1 := s.duality 0 b
        have h2 := s.dual.nonneg b 0
        omega
      have := s_le_t 0 b
      omega
    use chile
    intro a b _
    exact s_le_t a b
  · rintro ⟨chile, ess_le⟩
    exact le_of_ess_le s t cliff chile ess_le

end SlipFace

end LeanPool.DemazureProduct
