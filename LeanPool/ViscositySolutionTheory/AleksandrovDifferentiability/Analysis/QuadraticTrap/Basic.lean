/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.LineRestriction
public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Foundation.SecondOrder
public import Mathlib.Analysis.Calculus.Taylor

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Quadratic trapping

This file records elementary trapping lemmas obtained by subtracting an affine function from a
convex function with a lower supporting hyperplane and an upper quadratic contact.
-/

@[expose] public section

namespace AleksandrovDifferentiability

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The error after subtracting the affine function with slope `p` at `x`. -/
def affineRemainder (u : E → ℝ) (x p y : E) : ℝ :=
  u y - (u x + inner ℝ p (y - x))

@[simp]
theorem affineRemainder_self (u : E → ℝ) (x p : E) :
    affineRemainder u x p x = 0 := by
  simp [affineRemainder]

/-- The affine remainder, viewed as a function of increments `z` with `x + z ∈ s`, is convex
whenever `u` is convex on `s`. This is the source proof's normalized function
`\tilde u(z) = u(x+z)-u(x)-p·z`. -/
theorem ConvexOn.affineRemainder_increment
    {s : Set E} {u : E → ℝ} {x p : E} (hu : ConvexOn ℝ s u) :
    ConvexOn ℝ ((fun z : E => x + z) ⁻¹' s)
      (fun z => affineRemainder u x p (x + z)) := by
  have htranslate :
      ConvexOn ℝ ((fun z : E => x + z) ⁻¹' s) (fun z => u (x + z)) := by
    simpa [Function.comp_def] using hu.translate_right x
  have haffine :
      ConcaveOn ℝ ((fun z : E => x + z) ⁻¹' s) (fun z => u x + inner ℝ p z) := by
    refine ⟨htranslate.1, ?_⟩
    intro z _hz w _hw a b ha hb hab
    have hcombo :
        u x + inner ℝ p (a • z + b • w) =
          a * (u x + inner ℝ p z) + b * (u x + inner ℝ p w) := by
      have hux : u x = a * u x + b * u x := by
        calc
          u x = (a + b) * u x := by rw [hab]; ring
          _ = a * u x + b * u x := by ring
      calc
        u x + inner ℝ p (a • z + b • w)
            = u x + (a * inner ℝ p z + b * inner ℝ p w) := by
              rw [inner_add_right, inner_smul_right, inner_smul_right]
        _ = a * (u x + inner ℝ p z) + b * (u x + inner ℝ p w) := by
              linarith
    exact le_of_eq hcombo.symm
  have hconv :
      ConvexOn ℝ ((fun z : E => x + z) ⁻¹' s)
        (fun z => u (x + z) - (u x + inner ℝ p z)) :=
    htranslate.sub haffine
  refine hconv.congr ?_
  intro z _hz
  simp [affineRemainder]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Affine remainders commute with rebasing a function through a linear isometry equivalence. -/
theorem affineRemainder_comp_linearIsometryEquiv
    (e : E ≃ₗᵢ[ℝ] F) (u : E → ℝ) (x p y : E) :
    affineRemainder (u ∘ e.symm) (e x) (e p) (e y) = affineRemainder u x p y := by
  have hdiff : e y - e x = e (y - x) := by
    rw [map_sub]
  rw [affineRemainder, affineRemainder, hdiff, LinearIsometryEquiv.inner_map_map]
  simp

/-- A subgradient makes the affine remainder nonnegative on the domain. -/
theorem SubgradientOn.affineRemainder_nonneg
    {s : Set E} {u : E → ℝ} {x p y : E} (hp : SubgradientOn s u x p) (hy : y ∈ s) :
    0 ≤ affineRemainder u x p y := by
  dsimp [affineRemainder]
  exact sub_nonneg.mpr (hp.supporting_inequality (y := y) hy)

/-- Comparing a subgradient at `x1` with an arbitrary affine slope at `x0` is controlled by the
change in the affine remainder based at `x0`.

This is the algebraic core of the source proof's good-set gradient-control step. -/
theorem SubgradientOn.inner_sub_le_affineRemainder_sub
    {s : Set E} {u : E → ℝ} {x0 x1 p0 p1 y : E}
    (hp1 : SubgradientOn s u x1 p1) (hy : y ∈ s) :
    inner ℝ (p1 - p0) (y - x1) ≤
      affineRemainder u x0 p0 y - affineRemainder u x0 p0 x1 := by
  have hsupport := hp1.supporting_inequality (y := y) hy
  dsimp [affineRemainder]
  have hinner :
      inner ℝ (p1 - p0) (y - x1) =
        inner ℝ p1 (y - x1) - inner ℝ p0 (y - x1) := by
    rw [inner_sub_left]
  have hrem :
      affineRemainder u x0 p0 y - affineRemainder u x0 p0 x1 =
        (u y - u x1) - inner ℝ p0 (y - x1) := by
    have hinnerdiff :
        inner ℝ p0 (y - x0) - inner ℝ p0 (x1 - x0) =
          inner ℝ p0 (y - x1) := by
      rw [← inner_sub_right]
      congr 1
      abel
    dsimp [affineRemainder]
    linarith
  calc
    inner ℝ (p1 - p0) (y - x1)
        = inner ℝ p1 (y - x1) - inner ℝ p0 (y - x1) := hinner
    _ ≤ (u y - u x1) - inner ℝ p0 (y - x1) := by
      linarith
    _ = affineRemainder u x0 p0 y - affineRemainder u x0 p0 x1 := hrem.symm

/-- If the affine remainder based at `x0` is nonnegative at `x1`, then the preceding comparison
is bounded above by the affine remainder at `y`. -/
theorem SubgradientOn.inner_sub_le_affineRemainder_of_nonneg
    {s : Set E} {u : E → ℝ} {x0 x1 p0 p1 y : E}
    (hp1 : SubgradientOn s u x1 p1) (hy : y ∈ s)
    (h0 : 0 ≤ affineRemainder u x0 p0 x1) :
    inner ℝ (p1 - p0) (y - x1) ≤ affineRemainder u x0 p0 y := by
  have h := hp1.inner_sub_le_affineRemainder_sub (x0 := x0) (p0 := p0) hy
  linarith

/-- An upper contact with the same slope bounds the affine remainder by the quadratic opening. -/
theorem HasUpperContactWithSlopeOn.affineRemainder_le
    {s : Set E} {u : E → ℝ} {x p y : E} {a : ℝ}
    (h : HasUpperContactWithSlopeOn s u x p a) (hy : y ∈ s) :
    affineRemainder u x p y ≤ (a / 2) * ‖y - x‖ ^ 2 := by
  dsimp [affineRemainder]
  have hupper := h.upper_inequality (y := y) hy
  linarith

/-- If the same slope gives a lower support and an upper quadratic contact, then the affine
remainder is trapped between `0` and the quadratic opening. -/
theorem affineRemainder_nonneg_and_le_of_subgradient_of_upperContact
    {s : Set E} {u : E → ℝ} {x p y : E} {a : ℝ}
    (hp : SubgradientOn s u x p) (h : HasUpperContactWithSlopeOn s u x p a) (hy : y ∈ s) :
    0 ≤ affineRemainder u x p y ∧ affineRemainder u x p y ≤ (a / 2) * ‖y - x‖ ^ 2 :=
  ⟨hp.affineRemainder_nonneg hy, h.affineRemainder_le hy⟩

/-- A two-sided affine-remainder trap gives an absolute-value upper bound. -/
theorem abs_affineRemainder_le_of_nonneg_and_le
    {u : E → ℝ} {x p y : E} {C : ℝ}
    (h0 : 0 ≤ affineRemainder u x p y) (hC : affineRemainder u x p y ≤ C) :
    |affineRemainder u x p y| ≤ C := by
  simpa [abs_of_nonneg h0] using hC

/-- A two-sided affine-remainder trap gives a norm upper bound. -/
theorem norm_affineRemainder_le_of_nonneg_and_le
    {u : E → ℝ} {x p y : E} {C : ℝ}
    (h0 : 0 ≤ affineRemainder u x p y) (hC : affineRemainder u x p y ≤ C) :
    ‖affineRemainder u x p y‖ ≤ C := by
  simpa [Real.norm_eq_abs] using abs_affineRemainder_le_of_nonneg_and_le h0 hC

/-- A quadratic trap gives a normalized affine-remainder bound away from the base point. -/
theorem affineRemainder_div_norm_sq_le_of_nonneg_and_le
    {u : E → ℝ} {x p y : E} {C : ℝ}
    (h0 : 0 ≤ affineRemainder u x p y)
    (hC : affineRemainder u x p y ≤ C * ‖y - x‖ ^ 2) (hyx : y ≠ x) :
    ‖affineRemainder u x p y‖ / ‖y - x‖ ^ 2 ≤ C := by
  have hd : 0 < ‖y - x‖ ^ 2 := by
    exact sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hyx))
  have hnorm : ‖affineRemainder u x p y‖ ≤ C * ‖y - x‖ ^ 2 :=
    norm_affineRemainder_le_of_nonneg_and_le h0 hC
  exact (div_le_iff₀ hd).mpr hnorm

/-- Approximate quadratic trapping from a fixed-slope upper-contact opening bound. -/
theorem affineRemainder_nonneg_and_le_of_subgradient_of_upperContactOpening
    {s : Set E} {u : E → ℝ} {x p y : E} {A η : ℝ}
    (hp : SubgradientOn s u x p)
    (h : HasUpperContactWithSlopeOpeningAtMostOn s u x p A)
    (hη : 0 < η) (hy : y ∈ s) :
    0 ≤ affineRemainder u x p y ∧
      affineRemainder u x p y ≤ ((A + η) / 2) * ‖y - x‖ ^ 2 :=
  affineRemainder_nonneg_and_le_of_subgradient_of_upperContact hp
    (h.hasUpperContactWithSlopeOn_add_pos hη) hy

/-- Norm bound from a fixed-slope upper-contact opening trap. -/
theorem norm_affineRemainder_le_of_subgradient_of_upperContactOpening
    {s : Set E} {u : E → ℝ} {x p y : E} {A η : ℝ}
    (hp : SubgradientOn s u x p)
    (h : HasUpperContactWithSlopeOpeningAtMostOn s u x p A)
    (hη : 0 < η) (hy : y ∈ s) :
    ‖affineRemainder u x p y‖ ≤ ((A + η) / 2) * ‖y - x‖ ^ 2 := by
  rcases affineRemainder_nonneg_and_le_of_subgradient_of_upperContactOpening hp h hη hy with
    ⟨h0, hupper⟩
  exact norm_affineRemainder_le_of_nonneg_and_le h0 hupper

/-- Normalized affine-remainder bound from a fixed-slope upper-contact opening trap. -/
theorem affineRemainder_norm_div_norm_sq_le_of_subgradient_of_upperContactOpening
    {s : Set E} {u : E → ℝ} {x p y : E} {A η : ℝ}
    (hp : SubgradientOn s u x p)
    (h : HasUpperContactWithSlopeOpeningAtMostOn s u x p A)
    (hη : 0 < η) (hy : y ∈ s) (hyx : y ≠ x) :
    ‖affineRemainder u x p y‖ / ‖y - x‖ ^ 2 ≤ (A + η) / 2 := by
  rcases affineRemainder_nonneg_and_le_of_subgradient_of_upperContactOpening hp h hη hy with
    ⟨h0, hupper⟩
  exact affineRemainder_div_norm_sq_le_of_nonneg_and_le h0 hupper hyx

/-- For convex functions, a non-fixed upper-contact opening bound gives an existential affine
remainder trap with a slope that is both a subgradient and an upper-contact slope. -/
theorem exists_affineRemainder_trap_of_upperContactOpening_of_convex_of_mem_interior
    {s : Set E} {u : E → ℝ} {x y : E} {A η : ℝ}
    (h : HasUpperContactOpeningAtMostOn s u x A) (hu : ConvexOn ℝ s u)
    (hx : x ∈ interior s) (hη : 0 < η) (hy : y ∈ s) :
    ∃ p : E,
      SubgradientOn s u x p ∧
        HasUpperContactWithSlopeOn s u x p (A + η) ∧
          0 ≤ affineRemainder u x p y ∧
            affineRemainder u x p y ≤ ((A + η) / 2) * ‖y - x‖ ^ 2 := by
  rcases h.exists_subgradient_contact_add_pos_of_convex_of_mem_interior hu hx hη with
    ⟨p, hp, hcontact⟩
  exact ⟨p, hp, hcontact,
    affineRemainder_nonneg_and_le_of_subgradient_of_upperContact hp hcontact hy⟩

/-- For convex functions, a non-fixed upper-contact opening bound gives a single slope that
traps the affine remainder for every larger opening. -/
theorem exists_uniform_affineRemainder_trap_of_upperContactOpening_of_convex_of_mem_interior
    {s : Set E} {u : E → ℝ} {x : E} {A : ℝ}
    (h : HasUpperContactOpeningAtMostOn s u x A) (hu : ConvexOn ℝ s u)
    (hx : x ∈ interior s) :
    ∃ p : E,
      SubgradientOn s u x p ∧
        HasUpperContactWithSlopeOpeningAtMostOn s u x p A ∧
          ∀ η : ℝ, 0 < η → ∀ y ∈ s,
            0 ≤ affineRemainder u x p y ∧
              affineRemainder u x p y ≤ ((A + η) / 2) * ‖y - x‖ ^ 2 := by
  rcases h.exists_subgradient_fixedSlopeOpening_of_convex_of_mem_interior hu hx with
    ⟨p, hp, hfixed⟩
  refine ⟨p, hp, hfixed, ?_⟩
  intro η hη y hy
  exact affineRemainder_nonneg_and_le_of_subgradient_of_upperContactOpening hp hfixed hη hy

/-- Uniform normalized affine-remainder bound from ordinary bounded upper-contact opening in the
convex interior setting. -/
theorem exists_uniform_affineRemainder_norm_div_norm_sq_le_of_upperContactOpening_of_convex
    {s : Set E} {u : E → ℝ} {x : E} {A : ℝ}
    (h : HasUpperContactOpeningAtMostOn s u x A) (hu : ConvexOn ℝ s u)
    (hx : x ∈ interior s) :
    ∃ p : E,
      SubgradientOn s u x p ∧
        HasUpperContactWithSlopeOpeningAtMostOn s u x p A ∧
          ∀ η : ℝ, 0 < η → ∀ y ∈ s, y ≠ x →
            ‖affineRemainder u x p y‖ / ‖y - x‖ ^ 2 ≤ (A + η) / 2 := by
  rcases h.exists_subgradient_fixedSlopeOpening_of_convex_of_mem_interior hu hx with
    ⟨p, hp, hfixed⟩
  refine ⟨p, hp, hfixed, ?_⟩
  intro η hη y hy hyx
  exact affineRemainder_norm_div_norm_sq_le_of_subgradient_of_upperContactOpening
    hp hfixed hη hy hyx

/-- One-dimensional approximate quadratic trapping at the base point `0`. -/
theorem oneDimensional_affineRemainder_trap_of_upperContactOpening
    {S : Set ℝ} {f : ℝ → ℝ} {p t A η : ℝ}
    (hp : SubgradientOn S f 0 p)
    (h : HasUpperContactWithSlopeOpeningAtMostOn S f 0 p A)
    (hη : 0 < η) (ht : t ∈ S) :
    0 ≤ affineRemainder f 0 p t ∧
      affineRemainder f 0 p t ≤ ((A + η) / 2) * ‖t‖ ^ 2 := by
  simpa using
    (affineRemainder_nonneg_and_le_of_subgradient_of_upperContactOpening
      (E := ℝ) hp h hη ht)

/-- The affine remainder commutes with restricting to a line through the base point. -/
theorem affineRemainder_lineRestriction (u : E → ℝ) (x p v : E) (t : ℝ) :
    affineRemainder (AleksandrovDifferentiability.lineRestriction u x v) 0 (inner ℝ p v) t =
      affineRemainder u x p (x + t • v) := by
  simp [affineRemainder, AleksandrovDifferentiability.lineRestriction, real_inner_smul_right]

/-- The affine remainder commutes with restricting to a line at an arbitrary line parameter. -/
theorem affineRemainder_lineRestriction_at (u : E → ℝ) (x p v : E) (t r : ℝ) :
    affineRemainder (AleksandrovDifferentiability.lineRestriction u x v) t
        (inner ℝ p v) r =
      affineRemainder u (x + t • v) p (x + r • v) := by
  have hdiff : x + r • v - (x + t • v) = (r - t) • v := by
    calc
      x + r • v - (x + t • v) = r • v - t • v := by abel
      _ = (r - t) • v := by rw [sub_smul]
  simp [affineRemainder, AleksandrovDifferentiability.lineRestriction, hdiff,
    real_inner_smul_right]

/-- A subgradient gives nonnegativity of the affine remainder of each line restriction. -/
theorem SubgradientOn.lineRestriction_affineRemainder_nonneg
    {s : Set E} {u : E → ℝ} {x p v : E} (hp : SubgradientOn s u x p)
    {t : ℝ} (ht : t ∈ lineDomain s x v) :
    0 ≤ affineRemainder (AleksandrovDifferentiability.lineRestriction u x v) 0
      (inner ℝ p v) t := by
  exact (hp.lineRestriction_subgradientOn (v := v)).affineRemainder_nonneg ht

/-- Shifted version of `SubgradientOn.lineRestriction_affineRemainder_nonneg`. -/
theorem SubgradientOn.lineRestriction_affineRemainder_nonneg_at
    {s : Set E} {u : E → ℝ} {x p v : E} {t r : ℝ}
    (hp : SubgradientOn s u (x + t • v) p) (hr : r ∈ lineDomain s x v) :
    0 ≤ affineRemainder (AleksandrovDifferentiability.lineRestriction u x v) t
      (inner ℝ p v) r := by
  exact (hp.lineRestriction_subgradientOn_at (x := x) (v := v)).affineRemainder_nonneg hr

/-- An upper contact gives a quadratic upper bound for the affine remainder of each line
restriction. -/
theorem HasUpperContactWithSlopeOn.lineRestriction_affineRemainder_le
    {s : Set E} {u : E → ℝ} {x p v : E} {a : ℝ}
    (h : HasUpperContactWithSlopeOn s u x p a) {t : ℝ} (ht : t ∈ lineDomain s x v) :
    affineRemainder (AleksandrovDifferentiability.lineRestriction u x v) 0
      (inner ℝ p v) t ≤
        ((a * ‖v‖ ^ 2) / 2) * ‖t - 0‖ ^ 2 := by
  exact (h.lineRestriction (v := v)).affineRemainder_le ht

/-- Shifted version of `HasUpperContactWithSlopeOn.lineRestriction_affineRemainder_le`. -/
theorem HasUpperContactWithSlopeOn.lineRestriction_affineRemainder_le_at
    {s : Set E} {u : E → ℝ} {x p v : E} {t r a : ℝ}
    (h : HasUpperContactWithSlopeOn s u (x + t • v) p a)
    (hr : r ∈ lineDomain s x v) :
    affineRemainder (AleksandrovDifferentiability.lineRestriction u x v) t
      (inner ℝ p v) r ≤
      ((a * ‖v‖ ^ 2) / 2) * ‖r - t‖ ^ 2 := by
  exact (h.lineRestriction_at (x := x) (v := v)).affineRemainder_le hr

/-- Along every line, a shared subgradient and upper-contact slope trap the affine remainder
between `0` and the line-scaled quadratic opening. -/
theorem lineRestriction_affineRemainder_nonneg_and_le_of_subgradient_of_upperContact
    {s : Set E} {u : E → ℝ} {x p v : E} {a : ℝ}
    (hp : SubgradientOn s u x p) (h : HasUpperContactWithSlopeOn s u x p a)
    {t : ℝ} (ht : t ∈ lineDomain s x v) :
    0 ≤ affineRemainder (AleksandrovDifferentiability.lineRestriction u x v) 0
        (inner ℝ p v) t ∧
      affineRemainder (AleksandrovDifferentiability.lineRestriction u x v) 0
        (inner ℝ p v) t ≤
        ((a * ‖v‖ ^ 2) / 2) * ‖t - 0‖ ^ 2 :=
  ⟨hp.lineRestriction_affineRemainder_nonneg ht, h.lineRestriction_affineRemainder_le ht⟩

/-- Shifted line trap from a shared subgradient and upper-contact slope. -/
theorem lineRestriction_affineRemainder_nonneg_and_le_of_subgradient_of_upperContact_at
    {s : Set E} {u : E → ℝ} {x p v : E} {t r a : ℝ}
    (hp : SubgradientOn s u (x + t • v) p)
    (h : HasUpperContactWithSlopeOn s u (x + t • v) p a)
    (hr : r ∈ lineDomain s x v) :
    0 ≤ affineRemainder (AleksandrovDifferentiability.lineRestriction u x v) t
        (inner ℝ p v) r ∧
      affineRemainder (AleksandrovDifferentiability.lineRestriction u x v) t
        (inner ℝ p v) r ≤
        ((a * ‖v‖ ^ 2) / 2) * ‖r - t‖ ^ 2 :=
  ⟨hp.lineRestriction_affineRemainder_nonneg_at hr,
    h.lineRestriction_affineRemainder_le_at hr⟩

/-- Approximate quadratic trapping along a line from a fixed-slope upper-contact opening bound. -/
theorem lineRestriction_affineRemainder_nonneg_and_le_of_subgradient_of_upperContactOpening
    {s : Set E} {u : E → ℝ} {x p v : E} {A η : ℝ}
    (hp : SubgradientOn s u x p)
    (h : HasUpperContactWithSlopeOpeningAtMostOn s u x p A)
    (hη : 0 < η) {t : ℝ} (ht : t ∈ lineDomain s x v) :
    0 ≤ affineRemainder (AleksandrovDifferentiability.lineRestriction u x v) 0
        (inner ℝ p v) t ∧
      affineRemainder (AleksandrovDifferentiability.lineRestriction u x v) 0
        (inner ℝ p v) t ≤
        (((A + η) * ‖v‖ ^ 2) / 2) * ‖t - 0‖ ^ 2 :=
  lineRestriction_affineRemainder_nonneg_and_le_of_subgradient_of_upperContact hp
    (h.hasUpperContactWithSlopeOn_add_pos hη) ht

/-- Shifted approximate quadratic trapping along a line from a fixed-slope upper-contact opening
bound. -/
theorem lineRestriction_affineRemainder_nonneg_and_le_of_subgradient_of_upperContactOpening_at
    {s : Set E} {u : E → ℝ} {x p v : E} {t r A η : ℝ}
    (hp : SubgradientOn s u (x + t • v) p)
    (h : HasUpperContactWithSlopeOpeningAtMostOn s u (x + t • v) p A)
    (hη : 0 < η) (hr : r ∈ lineDomain s x v) :
    0 ≤ affineRemainder (AleksandrovDifferentiability.lineRestriction u x v) t
        (inner ℝ p v) r ∧
      affineRemainder (AleksandrovDifferentiability.lineRestriction u x v) t
        (inner ℝ p v) r ≤
        (((A + η) * ‖v‖ ^ 2) / 2) * ‖r - t‖ ^ 2 :=
  lineRestriction_affineRemainder_nonneg_and_le_of_subgradient_of_upperContact_at hp
    (h.hasUpperContactWithSlopeOn_add_pos hη) hr

/-- Unit-direction version of approximate line trapping, with the standard one-dimensional
quadratic bound. -/
theorem lineRestriction_affineRemainder_trap_of_upperContactOpening_norm_eq_one
    {s : Set E} {u : E → ℝ} {x p v : E} {A η : ℝ}
    (hp : SubgradientOn s u x p)
    (h : HasUpperContactWithSlopeOpeningAtMostOn s u x p A)
    (hv : ‖v‖ = 1) (hη : 0 < η) {t : ℝ} (ht : t ∈ lineDomain s x v) :
    0 ≤ affineRemainder (AleksandrovDifferentiability.lineRestriction u x v) 0
        (inner ℝ p v) t ∧
      affineRemainder (AleksandrovDifferentiability.lineRestriction u x v) 0
        (inner ℝ p v) t ≤
        ((A + η) / 2) * ‖t‖ ^ 2 := by
  have htrap :=
    lineRestriction_affineRemainder_nonneg_and_le_of_subgradient_of_upperContactOpening
      hp h hη ht
  rcases htrap with ⟨hnonneg, hupper⟩
  refine ⟨hnonneg, ?_⟩
  simpa [hv] using hupper

/-- Shifted unit-direction version of approximate line trapping. -/
theorem lineRestriction_affineRemainder_trap_at_of_upperContactOpening_norm_eq_one
    {s : Set E} {u : E → ℝ} {x p v : E} {t r A η : ℝ}
    (hp : SubgradientOn s u (x + t • v) p)
    (h : HasUpperContactWithSlopeOpeningAtMostOn s u (x + t • v) p A)
    (hv : ‖v‖ = 1) (hη : 0 < η) (hr : r ∈ lineDomain s x v) :
    0 ≤ affineRemainder (AleksandrovDifferentiability.lineRestriction u x v) t
        (inner ℝ p v) r ∧
      affineRemainder (AleksandrovDifferentiability.lineRestriction u x v) t
        (inner ℝ p v) r ≤
        ((A + η) / 2) * ‖r - t‖ ^ 2 := by
  rcases lineRestriction_affineRemainder_nonneg_and_le_of_subgradient_of_upperContactOpening_at
      hp h hη hr with ⟨hnonneg, hupper⟩
  refine ⟨hnonneg, ?_⟩
  simpa [hv] using hupper

/-- For convex functions, ordinary bounded upper-contact opening gives a single slope whose line
restrictions have the standard one-dimensional quadratic trap in every unit direction. -/
theorem exists_uniform_lineRestriction_affineRemainder_trap_norm_eq_one_of_upperContactOpening
    {s : Set E} {u : E → ℝ} {x v : E} {A : ℝ}
    (h : HasUpperContactOpeningAtMostOn s u x A) (hu : ConvexOn ℝ s u)
    (hx : x ∈ interior s) (hv : ‖v‖ = 1) :
    ∃ p : E,
      SubgradientOn s u x p ∧
        HasUpperContactWithSlopeOpeningAtMostOn s u x p A ∧
          ∀ η : ℝ, 0 < η → ∀ t ∈ lineDomain s x v,
            0 ≤ affineRemainder (AleksandrovDifferentiability.lineRestriction u x v) 0
                (inner ℝ p v) t ∧
              affineRemainder (AleksandrovDifferentiability.lineRestriction u x v) 0
                (inner ℝ p v) t ≤ ((A + η) / 2) * ‖t‖ ^ 2 := by
  rcases h.exists_subgradient_fixedSlopeOpening_of_convex_of_mem_interior hu hx with
    ⟨p, hp, hfixed⟩
  refine ⟨p, hp, hfixed, ?_⟩
  intro η hη t ht
  exact lineRestriction_affineRemainder_trap_of_upperContactOpening_norm_eq_one
    hp hfixed hv hη ht

/-- Shifted version of
`exists_uniform_lineRestriction_affineRemainder_trap_norm_eq_one_of_upperContactOpening`. -/
theorem exists_uniform_lineRestriction_affineRemainder_trap_at_norm_eq_one_of_upperContactOpening
    {s : Set E} {u : E → ℝ} {x v : E} {t A : ℝ}
    (h : HasUpperContactOpeningAtMostOn s u (x + t • v) A) (hu : ConvexOn ℝ s u)
    (hx : x + t • v ∈ interior s) (hv : ‖v‖ = 1) :
    ∃ p : E,
      SubgradientOn s u (x + t • v) p ∧
        HasUpperContactWithSlopeOpeningAtMostOn s u (x + t • v) p A ∧
          ∀ η : ℝ, 0 < η → ∀ r ∈ lineDomain s x v,
            0 ≤ affineRemainder (AleksandrovDifferentiability.lineRestriction u x v) t
                (inner ℝ p v) r ∧
              affineRemainder (AleksandrovDifferentiability.lineRestriction u x v) t
                (inner ℝ p v) r ≤ ((A + η) / 2) * ‖r - t‖ ^ 2 := by
  rcases h.exists_subgradient_fixedSlopeOpening_of_convex_of_mem_interior hu hx with
    ⟨p, hp, hfixed⟩
  refine ⟨p, hp, hfixed, ?_⟩
  intro η hη r hr
  exact lineRestriction_affineRemainder_trap_at_of_upperContactOpening_norm_eq_one
    hp hfixed hv hη hr

/-- Uniform normalized line-restriction affine-remainder bound in a unit direction. -/
theorem exists_uniform_lineRestriction_affineRemainder_norm_div_norm_sq_le
    {s : Set E} {u : E → ℝ} {x v : E} {A : ℝ}
    (h : HasUpperContactOpeningAtMostOn s u x A) (hu : ConvexOn ℝ s u)
    (hx : x ∈ interior s) (hv : ‖v‖ = 1) :
    ∃ p : E,
      SubgradientOn s u x p ∧
        HasUpperContactWithSlopeOpeningAtMostOn s u x p A ∧
          ∀ η : ℝ, 0 < η → ∀ t ∈ lineDomain s x v, t ≠ 0 →
            ‖affineRemainder (AleksandrovDifferentiability.lineRestriction u x v) 0
                (inner ℝ p v) t‖ / ‖t‖ ^ 2 ≤ (A + η) / 2 := by
  rcases h.exists_subgradient_fixedSlopeOpening_of_convex_of_mem_interior hu hx with
    ⟨p, hp, hfixed⟩
  refine ⟨p, hp, hfixed, ?_⟩
  intro η hη t ht ht0
  rcases lineRestriction_affineRemainder_trap_of_upperContactOpening_norm_eq_one
      hp hfixed hv hη ht with ⟨h0, hupper⟩
  simpa [sub_zero] using
    (affineRemainder_div_norm_sq_le_of_nonneg_and_le h0 (by simpa using hupper) ht0)

/-- Shifted uniform normalized line-restriction affine-remainder bound in a unit direction. -/
theorem exists_uniform_lineRestriction_affineRemainder_norm_div_norm_sq_le_at
    {s : Set E} {u : E → ℝ} {x v : E} {t A : ℝ}
    (h : HasUpperContactOpeningAtMostOn s u (x + t • v) A) (hu : ConvexOn ℝ s u)
    (hx : x + t • v ∈ interior s) (hv : ‖v‖ = 1) :
    ∃ p : E,
      SubgradientOn s u (x + t • v) p ∧
        HasUpperContactWithSlopeOpeningAtMostOn s u (x + t • v) p A ∧
          ∀ η : ℝ, 0 < η → ∀ r ∈ lineDomain s x v, r ≠ t →
            ‖affineRemainder (AleksandrovDifferentiability.lineRestriction u x v) t
                (inner ℝ p v) r‖ / ‖r - t‖ ^ 2 ≤ (A + η) / 2 := by
  rcases h.exists_subgradient_fixedSlopeOpening_of_convex_of_mem_interior hu hx with
    ⟨p, hp, hfixed⟩
  refine ⟨p, hp, hfixed, ?_⟩
  intro η hη r hr hrt
  rcases lineRestriction_affineRemainder_trap_at_of_upperContactOpening_norm_eq_one
      hp hfixed hv hη hr with ⟨h0, hupper⟩
  exact affineRemainder_div_norm_sq_le_of_nonneg_and_le h0 (by simpa using hupper) hrt

end AleksandrovDifferentiability
