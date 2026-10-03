/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.LineRestriction.Basic

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Line subgradient lift interfaces
-/

@[expose] public section

open scoped Topology

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A scalar subgradient of a line restriction is represented by an ambient subgradient. -/
def LineSubgradientLiftsToAmbient
    (s : Set E) (u : E → ℝ) (x z : E) (t q : ℝ) : Prop :=
  ∃ p : E, SubgradientOn s u (x + t • z) p ∧ q = inner ℝ p z

/-- Functional form of `LineSubgradientLiftsToAmbient`.

This is the form naturally produced by a geometric Hahn-Banach/separation argument: a continuous
linear functional supports the epigraph of `u` at `x + t • z` and has value `q` on the line
direction `z`. In complete real inner-product spaces, Fréchet-Riesz converts this functional
form into the vector-valued subgradient form used elsewhere in the project. -/
def LineSubgradientLiftsToAmbientFunctional
    (s : Set E) (u : E → ℝ) (x z : E) (t q : ℝ) : Prop :=
  ∃ ℓ : StrongDual ℝ E,
    (∀ y ∈ s, u (x + t • z) + ℓ (y - (x + t • z)) ≤ u y) ∧ q = ℓ z

/-- An ambient subgradient at a point on the line gives a vector-valued lift of its directional
pairing. -/
theorem SubgradientOn.lineSubgradientLiftsToAmbient_at
    {s : Set E} {u : E → ℝ} {x z p : E} {t : ℝ}
    (hp : SubgradientOn s u (x + t • z) p) :
    LineSubgradientLiftsToAmbient s u x z t (inner ℝ p z) :=
  ⟨p, hp, rfl⟩

/-- An ambient subgradient at a point on the line gives a functional lift of its directional
pairing. -/
theorem SubgradientOn.lineSubgradientLiftsToAmbientFunctional_at
    {s : Set E} {u : E → ℝ} {x z p : E} {t : ℝ}
    (hp : SubgradientOn s u (x + t • z) p) :
    LineSubgradientLiftsToAmbientFunctional s u x z t (inner ℝ p z) := by
  refine ⟨InnerProductSpace.toDualMap ℝ E p, ?_, ?_⟩
  · intro y hy
    simpa [InnerProductSpace.toDualMap_apply_apply] using hp.supporting_inequality hy
  · simp [InnerProductSpace.toDualMap_apply_apply]

/-- If a scalar slope is attained by an ambient subgradient in direction `z`, then it has a
functional lift. -/
theorem lineSubgradientLiftsToAmbientFunctional_of_exists_subgradient_eq
    {s : Set E} {u : E → ℝ} {x z : E} {t q : ℝ}
    (h : ∃ p : E, SubgradientOn s u (x + t • z) p ∧ q = inner ℝ p z) :
    LineSubgradientLiftsToAmbientFunctional s u x z t q := by
  rcases h with ⟨p, hp, hq⟩
  rw [hq]
  exact hp.lineSubgradientLiftsToAmbientFunctional_at

/-- If a scalar slope is attained by an ambient subgradient in direction `z`, then it has a
vector-valued lift. -/
theorem lineSubgradientLiftsToAmbient_of_exists_subgradient_eq
    {s : Set E} {u : E → ℝ} {x z : E} {t q : ℝ}
    (h : ∃ p : E, SubgradientOn s u (x + t • z) p ∧ q = inner ℝ p z) :
    LineSubgradientLiftsToAmbient s u x z t q :=
  h

/-- Right-derivative endpoint attainment by an ambient subgradient gives the corresponding
functional lift. -/
theorem lineRightDeriv_liftsToAmbientFunctional_of_exists_subgradient_eq
    {s : Set E} {u : E → ℝ} {x z : E} {t : ℝ}
    (h : ∃ p : E, SubgradientOn s u (x + t • z) p ∧
      rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t = inner ℝ p z) :
    LineSubgradientLiftsToAmbientFunctional s u x z t
      (rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t) :=
  lineSubgradientLiftsToAmbientFunctional_of_exists_subgradient_eq h

/-- Right-derivative endpoint attainment by an ambient subgradient gives the corresponding
vector-valued lift. -/
theorem lineRightDeriv_liftsToAmbient_of_exists_subgradient_eq
    {s : Set E} {u : E → ℝ} {x z : E} {t : ℝ}
    (h : ∃ p : E, SubgradientOn s u (x + t • z) p ∧
      rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t = inner ℝ p z) :
    LineSubgradientLiftsToAmbient s u x z t
      (rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t) :=
  lineSubgradientLiftsToAmbient_of_exists_subgradient_eq h

/-- Left-derivative endpoint attainment by an ambient subgradient gives the corresponding
functional lift. -/
theorem lineLeftDeriv_liftsToAmbientFunctional_of_exists_subgradient_eq
    {s : Set E} {u : E → ℝ} {x z : E} {t : ℝ}
    (h : ∃ p : E, SubgradientOn s u (x + t • z) p ∧
      leftDeriv (AleksandrovDifferentiability.lineRestriction u x z) t = inner ℝ p z) :
    LineSubgradientLiftsToAmbientFunctional s u x z t
      (leftDeriv (AleksandrovDifferentiability.lineRestriction u x z) t) :=
  lineSubgradientLiftsToAmbientFunctional_of_exists_subgradient_eq h

/-- Left-derivative endpoint attainment by an ambient subgradient gives the corresponding
vector-valued lift. -/
theorem lineLeftDeriv_liftsToAmbient_of_exists_subgradient_eq
    {s : Set E} {u : E → ℝ} {x z : E} {t : ℝ}
    (h : ∃ p : E, SubgradientOn s u (x + t • z) p ∧
      leftDeriv (AleksandrovDifferentiability.lineRestriction u x z) t = inner ℝ p z) :
    LineSubgradientLiftsToAmbient s u x z t
      (leftDeriv (AleksandrovDifferentiability.lineRestriction u x z) t) :=
  lineSubgradientLiftsToAmbient_of_exists_subgradient_eq h

/-- A point in a real interval is a convex combination of the endpoints. -/
theorem exists_nonneg_add_eq_one_and_eq_combo_of_mem_Icc
    {l q r : ℝ} (hlq : l ≤ q) (hqr : q ≤ r) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ q = a * l + b * r := by
  by_cases hlt : l < r
  · refine ⟨(r - q) / (r - l), (q - l) / (r - l), ?_, ?_, ?_, ?_⟩
    · exact div_nonneg (sub_nonneg.mpr hqr) (sub_nonneg.mpr hlt.le)
    · exact div_nonneg (sub_nonneg.mpr hlq) (sub_nonneg.mpr hlt.le)
    · field_simp [sub_ne_zero.mpr hlt.ne.symm]
      ring_nf
    · field_simp [sub_ne_zero.mpr hlt.ne.symm]
      ring_nf
  · have hq_eq : q = l := by linarith
    refine ⟨1, 0, by norm_num, by norm_num, by norm_num, ?_⟩
    simp [hq_eq]

/-- A one-dimensional subgradient of a line restriction is exactly an affine minorant along that
line. This is the line datum that the Hahn-Banach/separation step must extend to the ambient
domain. -/
theorem SubgradientOn.lineRestriction_supporting_slope_inequality
    {s : Set E} {u : E → ℝ} {x z : E} {t q r : ℝ}
    (hq : SubgradientOn (lineDomain s x z) (lineRestriction u x z) t q)
    (hr : r ∈ lineDomain s x z) :
    u (x + t • z) + q * (r - t) ≤ u (x + r • z) := by
  have h := hq.supporting_inequality (y := r) hr
  simpa [lineRestriction, Real.inner_apply, mul_comm] using h

/-- If an ambient supporting functional has the prescribed value on the line direction, it extends
the line affine minorant determined by a line subgradient. This records the compatibility between
the line-subgradient datum and the functional lift target. -/
theorem LineSubgradientLiftsToAmbientFunctional.line_inequality
    {s : Set E} {u : E → ℝ} {x z : E} {t q r : ℝ}
    (h : LineSubgradientLiftsToAmbientFunctional s u x z t q)
    (hr : r ∈ lineDomain s x z) :
    u (x + t • z) + q * (r - t) ≤ u (x + r • z) := by
  rcases h with ⟨ℓ, hsupport, hq⟩
  have hline := hsupport (x + r • z) hr
  have hdiff : x + r • z - (x + t • z) = (r - t) • z := by
    calc
      x + r • z - (x + t • z) = r • z - t • z := by abel
      _ = (r - t) • z := by rw [sub_smul]
  rw [hdiff] at hline
  simpa [hq, map_smul, smul_eq_mul, mul_comm] using hline

/-- A vector-valued ambient subgradient lift gives the functional lift by the Riesz embedding
`p ↦ (y ↦ p · y)`. The reverse implication uses Fréchet-Riesz and therefore requires
completeness; see `LineSubgradientLiftsToAmbientFunctional.to_lineSubgradientLiftsToAmbient`. -/
theorem LineSubgradientLiftsToAmbient.to_lineSubgradientLiftsToAmbientFunctional
    {s : Set E} {u : E → ℝ} {x z : E} {t q : ℝ}
    (h : LineSubgradientLiftsToAmbient s u x z t q) :
    LineSubgradientLiftsToAmbientFunctional s u x z t q := by
  rcases h with ⟨p, hp, hq⟩
  refine ⟨InnerProductSpace.toDualMap ℝ E p, ?_, ?_⟩
  · intro y hy
    simpa [InnerProductSpace.toDualMap_apply_apply] using hp.supporting_inequality hy
  · simpa [InnerProductSpace.toDualMap_apply_apply] using hq

/-- Convex combinations of vector-valued line-subgradient lifts are again vector-valued lifts.
This records the interval-convexity of directional values of ambient subgradients. -/
theorem LineSubgradientLiftsToAmbient.smul_add_smul
    {s : Set E} {u : E → ℝ} {x z : E} {t q₀ q₁ : ℝ} {a b : ℝ}
    (h₀ : LineSubgradientLiftsToAmbient s u x z t q₀)
    (h₁ : LineSubgradientLiftsToAmbient s u x z t q₁)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    LineSubgradientLiftsToAmbient s u x z t (a * q₀ + b * q₁) := by
  rcases h₀ with ⟨p₀, hp₀, hq₀⟩
  rcases h₁ with ⟨p₁, hp₁, hq₁⟩
  refine ⟨a • p₀ + b • p₁, hp₀.smul_add_smul hp₁ ha hb hab, ?_⟩
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, ← hq₀, ← hq₁]

/-- Convex combinations of functional line-subgradient lifts are again functional lifts. -/
theorem LineSubgradientLiftsToAmbientFunctional.smul_add_smul
    {s : Set E} {u : E → ℝ} {x z : E} {t q₀ q₁ : ℝ} {a b : ℝ}
    (h₀ : LineSubgradientLiftsToAmbientFunctional s u x z t q₀)
    (h₁ : LineSubgradientLiftsToAmbientFunctional s u x z t q₁)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    LineSubgradientLiftsToAmbientFunctional s u x z t (a * q₀ + b * q₁) := by
  rcases h₀ with ⟨ℓ₀, hsupport₀, hq₀⟩
  rcases h₁ with ⟨ℓ₁, hsupport₁, hq₁⟩
  refine ⟨a • ℓ₀ + b • ℓ₁, ?_, ?_⟩
  · intro y hy
    have h₀y := hsupport₀ y hy
    have h₁y := hsupport₁ y hy
    have hcombo :=
      add_le_add (mul_le_mul_of_nonneg_left h₀y ha) (mul_le_mul_of_nonneg_left h₁y hb)
    calc
      u (x + t • z) + (a • ℓ₀ + b • ℓ₁) (y - (x + t • z))
          = a * (u (x + t • z) + ℓ₀ (y - (x + t • z))) +
              b * (u (x + t • z) + ℓ₁ (y - (x + t • z))) := by
            have hb_eq : b = 1 - a := by linarith
            rw [add_apply, smul_apply,
              smul_apply, hb_eq]
            ring
      _ ≤ a * u y + b * u y := hcombo
      _ = u y := by
        rw [← add_mul, hab, one_mul]
  · rw [add_apply, smul_apply,
      smul_apply, ← hq₀, ← hq₁]
    simp [smul_eq_mul]

/-- If the left and right derivatives of a convex line restriction have functional ambient lifts,
then every one-dimensional subgradient slope has a functional ambient lift. -/
theorem ConvexOn.lineSubgradient_liftsToAmbientFunctional_of_leftRightDeriv_lift
    {s : Set E} {u : E → ℝ} {x z : E} {t q : ℝ} (hu : ConvexOn ℝ s u)
    (ht : x + t • z ∈ interior s)
    (hq : SubgradientOn (lineDomain s x z) (AleksandrovDifferentiability.lineRestriction u x z)
      t q)
    (hleft : LineSubgradientLiftsToAmbientFunctional s u x z t
      (leftDeriv (AleksandrovDifferentiability.lineRestriction u x z) t))
    (hright : LineSubgradientLiftsToAmbientFunctional s u x z t
      (rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t)) :
    LineSubgradientLiftsToAmbientFunctional s u x z t q := by
  have hlineInterior : t ∈ interior (lineDomain s x z) :=
    mem_interior_lineDomain_of_line_mem_interior ht
  have hbounds :
      leftDeriv (AleksandrovDifferentiability.lineRestriction u x z) t ≤ q ∧
        q ≤ rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t :=
    (AleksandrovDifferentiability.ConvexOn.subgradientOn_iff_leftDeriv_le_and_le_rightDeriv
      (S := lineDomain s x z)
      (f := AleksandrovDifferentiability.lineRestriction u x z)
      (x := t) (p := q)
      (ConvexOn.lineRestriction (x := x) (v := z) hu) hlineInterior).mp hq
  rcases exists_nonneg_add_eq_one_and_eq_combo_of_mem_Icc hbounds.1 hbounds.2 with
    ⟨a, b, ha, hb, hab, hqcombo⟩
  rw [hqcombo]
  exact hleft.smul_add_smul hright ha hb hab

/-- Vector-valued version of
`ConvexOn.lineSubgradient_liftsToAmbientFunctional_of_leftRightDeriv_lift`. -/
theorem ConvexOn.lineSubgradient_liftsToAmbient_of_leftRightDeriv_lift
    {s : Set E} {u : E → ℝ} {x z : E} {t q : ℝ} (hu : ConvexOn ℝ s u)
    (ht : x + t • z ∈ interior s)
    (hq : SubgradientOn (lineDomain s x z) (AleksandrovDifferentiability.lineRestriction u x z)
      t q)
    (hleft : LineSubgradientLiftsToAmbient s u x z t
      (leftDeriv (AleksandrovDifferentiability.lineRestriction u x z) t))
    (hright : LineSubgradientLiftsToAmbient s u x z t
      (rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t)) :
    LineSubgradientLiftsToAmbient s u x z t q := by
  have hlineInterior : t ∈ interior (lineDomain s x z) :=
    mem_interior_lineDomain_of_line_mem_interior ht
  have hbounds :
      leftDeriv (AleksandrovDifferentiability.lineRestriction u x z) t ≤ q ∧
        q ≤ rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t :=
    (AleksandrovDifferentiability.ConvexOn.subgradientOn_iff_leftDeriv_le_and_le_rightDeriv
      (S := lineDomain s x z)
      (f := AleksandrovDifferentiability.lineRestriction u x z)
      (x := t) (p := q)
      (ConvexOn.lineRestriction (x := x) (v := z) hu) hlineInterior).mp hq
  rcases exists_nonneg_add_eq_one_and_eq_combo_of_mem_Icc hbounds.1 hbounds.2 with
    ⟨a, b, ha, hb, hab, hqcombo⟩
  rw [hqcombo]
  exact hleft.smul_add_smul hright ha hb hab

/-- Eventual functional lift of all line subgradients from eventual lifts of the left and right
derivatives. -/
theorem ConvexOn.eventually_lineSubgradient_liftsToAmbientFunctional_of_leftRightDeriv_lift
    {s : Set E} {u : E → ℝ} {x : E} (hu : ConvexOn ℝ s u)
    (hsegmentInterior : ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, x + t • z ∈ interior s)
    (hleft : ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        LineSubgradientLiftsToAmbientFunctional s u x z t
          (leftDeriv (AleksandrovDifferentiability.lineRestriction u x z) t))
    (hright : ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        LineSubgradientLiftsToAmbientFunctional s u x z t
          (rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t)) :
    ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ q : ℝ,
        SubgradientOn (lineDomain s x z) (AleksandrovDifferentiability.lineRestriction u x z) t q →
          LineSubgradientLiftsToAmbientFunctional s u x z t q := by
  filter_upwards [hsegmentInterior, hleft, hright] with z hzsegment hzleft hzright t ht q hq
  exact
    ConvexOn.lineSubgradient_liftsToAmbientFunctional_of_leftRightDeriv_lift
      hu (x := x) (z := z) (t := t) (q := q) (hzsegment t ht) hq
      (hzleft t ht) (hzright t ht)

/-- Eventual vector-valued lift of all line subgradients from eventual lifts of the left and right
derivatives. -/
theorem ConvexOn.eventually_lineSubgradient_liftsToAmbient_of_leftRightDeriv_lift
    {s : Set E} {u : E → ℝ} {x : E} (hu : ConvexOn ℝ s u)
    (hsegmentInterior : ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, x + t • z ∈ interior s)
    (hleft : ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        LineSubgradientLiftsToAmbient s u x z t
          (leftDeriv (AleksandrovDifferentiability.lineRestriction u x z) t))
    (hright : ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        LineSubgradientLiftsToAmbient s u x z t
          (rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t)) :
    ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ q : ℝ,
        SubgradientOn (lineDomain s x z) (AleksandrovDifferentiability.lineRestriction u x z) t q →
          LineSubgradientLiftsToAmbient s u x z t q := by
  filter_upwards [hsegmentInterior, hleft, hright] with z hzsegment hzleft hzright t ht q hq
  exact
    ConvexOn.lineSubgradient_liftsToAmbient_of_leftRightDeriv_lift
      hu (x := x) (z := z) (t := t) (q := q) (hzsegment t ht) hq
      (hzleft t ht) (hzright t ht)

/-- Eventual functional lift of all line subgradients from endpoint attainment of the left and
right derivatives by ambient subgradients. This is the form expected from the endpoint
support-function/Hahn-Banach step. -/
theorem ConvexOn.eventually_lineSubgradient_liftsToAmbientFunctional_of_leftRightDeriv_attainment
    {s : Set E} {u : E → ℝ} {x : E} (hu : ConvexOn ℝ s u)
    (hsegmentInterior : ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, x + t • z ∈ interior s)
    (hleft : ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ∃ p : E, SubgradientOn s u (x + t • z) p ∧
          leftDeriv (AleksandrovDifferentiability.lineRestriction u x z) t = inner ℝ p z)
    (hright : ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ∃ p : E, SubgradientOn s u (x + t • z) p ∧
          rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t = inner ℝ p z) :
    ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ q : ℝ,
        SubgradientOn (lineDomain s x z) (AleksandrovDifferentiability.lineRestriction u x z) t q →
          LineSubgradientLiftsToAmbientFunctional s u x z t q := by
  refine ConvexOn.eventually_lineSubgradient_liftsToAmbientFunctional_of_leftRightDeriv_lift
    hu hsegmentInterior ?_ ?_
  · filter_upwards [hleft] with z hz t ht
    exact lineLeftDeriv_liftsToAmbientFunctional_of_exists_subgradient_eq (hz t ht)
  · filter_upwards [hright] with z hz t ht
    exact lineRightDeriv_liftsToAmbientFunctional_of_exists_subgradient_eq (hz t ht)

/-- Eventual vector-valued lift of all line subgradients from endpoint attainment of the left and
right derivatives by ambient subgradients. -/
theorem ConvexOn.eventually_lineSubgradient_liftsToAmbient_of_leftRightDeriv_attainment
    {s : Set E} {u : E → ℝ} {x : E} (hu : ConvexOn ℝ s u)
    (hsegmentInterior : ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, x + t • z ∈ interior s)
    (hleft : ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ∃ p : E, SubgradientOn s u (x + t • z) p ∧
          leftDeriv (AleksandrovDifferentiability.lineRestriction u x z) t = inner ℝ p z)
    (hright : ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ∃ p : E, SubgradientOn s u (x + t • z) p ∧
          rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t = inner ℝ p z) :
    ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ q : ℝ,
        SubgradientOn (lineDomain s x z) (AleksandrovDifferentiability.lineRestriction u x z) t q →
          LineSubgradientLiftsToAmbient s u x z t q := by
  refine ConvexOn.eventually_lineSubgradient_liftsToAmbient_of_leftRightDeriv_lift
    hu hsegmentInterior ?_ ?_
  · filter_upwards [hleft] with z hz t ht
    exact lineLeftDeriv_liftsToAmbient_of_exists_subgradient_eq (hz t ht)
  · filter_upwards [hright] with z hz t ht
    exact lineRightDeriv_liftsToAmbient_of_exists_subgradient_eq (hz t ht)

/-- A functional lift gives the vector-valued ambient subgradient lift by Fréchet-Riesz. -/
theorem LineSubgradientLiftsToAmbientFunctional.to_lineSubgradientLiftsToAmbient
    [CompleteSpace E] {s : Set E} {u : E → ℝ} {x z : E} {t q : ℝ}
    (hmem : x + t • z ∈ s)
    (h : LineSubgradientLiftsToAmbientFunctional s u x z t q) :
    LineSubgradientLiftsToAmbient s u x z t q := by
  rcases h with ⟨ℓ, hsupport, hq⟩
  let p : E := (InnerProductSpace.toDual ℝ E).symm ℓ
  refine ⟨p, ⟨hmem, ?_⟩, ?_⟩
  · intro y hy
    simpa [p] using hsupport y hy
  · simpa [p] using hq

/-- Eventual version of the Fréchet-Riesz conversion from functional line-subgradient lifts to
vector-valued ambient subgradient lifts. -/
theorem eventually_lineSubgradientLiftsToAmbient_of_functional
    [CompleteSpace E] {s : Set E} {u : E → ℝ} {x : E}
    (hsegment : ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, x + t • z ∈ s)
    (hlift : ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ q : ℝ,
        SubgradientOn (lineDomain s x z) (AleksandrovDifferentiability.lineRestriction u x z) t q →
          LineSubgradientLiftsToAmbientFunctional s u x z t q) :
    ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ q : ℝ,
        SubgradientOn (lineDomain s x z) (AleksandrovDifferentiability.lineRestriction u x z) t q →
          LineSubgradientLiftsToAmbient s u x z t q := by
  filter_upwards [hsegment, hlift] with z hzsegment hzlift t ht q hq
  exact (hzlift t ht q hq).to_lineSubgradientLiftsToAmbient (hzsegment t ht)

/-- Eventual conversion from vector-valued line-subgradient lifts to functional lifts. -/
theorem eventually_lineSubgradientLiftsToAmbientFunctional_of_vector
    {s : Set E} {u : E → ℝ} {x : E}
    (hlift : ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ q : ℝ,
        SubgradientOn (lineDomain s x z) (AleksandrovDifferentiability.lineRestriction u x z) t q →
          LineSubgradientLiftsToAmbient s u x z t q) :
    ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ q : ℝ,
        SubgradientOn (lineDomain s x z) (AleksandrovDifferentiability.lineRestriction u x z) t q →
          LineSubgradientLiftsToAmbientFunctional s u x z t q := by
  filter_upwards [hlift] with z hz t ht q hq
  exact (hz t ht q hq).to_lineSubgradientLiftsToAmbientFunctional

/-- Pointwise functional lift of the left derivative, once all line subgradients are known to
lift. Convexity supplies the fact that the left derivative is itself a one-dimensional
subgradient. -/
theorem ConvexOn.lineLeftDeriv_liftsToAmbientFunctional_of_lineSubgradientLift
    {s : Set E} {u : E → ℝ} {x z : E} {t : ℝ} (hu : ConvexOn ℝ s u)
    (ht : x + t • z ∈ interior s)
    (hlift : ∀ q : ℝ,
      SubgradientOn (lineDomain s x z) (AleksandrovDifferentiability.lineRestriction u x z) t q →
        LineSubgradientLiftsToAmbientFunctional s u x z t q) :
    LineSubgradientLiftsToAmbientFunctional s u x z t
      (leftDeriv (AleksandrovDifferentiability.lineRestriction u x z) t) :=
  hlift _ (ConvexOn.lineRestriction_leftDeriv_subgradientOn_at_of_line_mem_interior
    (s := s) (u := u) (x := x) (v := z) (t := t) hu ht)

/-- Pointwise vector-valued lift of the left derivative, once all line subgradients are known to
lift. -/
theorem ConvexOn.lineLeftDeriv_liftsToAmbient_of_lineSubgradientLift
    {s : Set E} {u : E → ℝ} {x z : E} {t : ℝ} (hu : ConvexOn ℝ s u)
    (ht : x + t • z ∈ interior s)
    (hlift : ∀ q : ℝ,
      SubgradientOn (lineDomain s x z) (AleksandrovDifferentiability.lineRestriction u x z) t q →
        LineSubgradientLiftsToAmbient s u x z t q) :
    LineSubgradientLiftsToAmbient s u x z t
      (leftDeriv (AleksandrovDifferentiability.lineRestriction u x z) t) :=
  hlift _ (ConvexOn.lineRestriction_leftDeriv_subgradientOn_at_of_line_mem_interior
    (s := s) (u := u) (x := x) (v := z) (t := t) hu ht)

/-- Pointwise functional lift of the right derivative, once all line subgradients are known to
lift. Convexity supplies the fact that the right derivative is itself a one-dimensional
subgradient. -/
theorem ConvexOn.lineRightDeriv_liftsToAmbientFunctional_of_lineSubgradientLift
    {s : Set E} {u : E → ℝ} {x z : E} {t : ℝ} (hu : ConvexOn ℝ s u)
    (ht : x + t • z ∈ interior s)
    (hlift : ∀ q : ℝ,
      SubgradientOn (lineDomain s x z) (AleksandrovDifferentiability.lineRestriction u x z) t q →
        LineSubgradientLiftsToAmbientFunctional s u x z t q) :
    LineSubgradientLiftsToAmbientFunctional s u x z t
      (rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t) :=
  hlift _ (ConvexOn.lineRestriction_rightDeriv_subgradientOn_at_of_line_mem_interior
    (s := s) (u := u) (x := x) (v := z) (t := t) hu ht)

/-- Pointwise vector-valued lift of the right derivative, once all line subgradients are known to
lift. -/
theorem ConvexOn.lineRightDeriv_liftsToAmbient_of_lineSubgradientLift
    {s : Set E} {u : E → ℝ} {x z : E} {t : ℝ} (hu : ConvexOn ℝ s u)
    (ht : x + t • z ∈ interior s)
    (hlift : ∀ q : ℝ,
      SubgradientOn (lineDomain s x z) (AleksandrovDifferentiability.lineRestriction u x z) t q →
        LineSubgradientLiftsToAmbient s u x z t q) :
    LineSubgradientLiftsToAmbient s u x z t
      (rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t) :=
  hlift _ (ConvexOn.lineRestriction_rightDeriv_subgradientOn_at_of_line_mem_interior
    (s := s) (u := u) (x := x) (v := z) (t := t) hu ht)

/-- Eventual functional lift of the left derivative along short segments. -/
theorem ConvexOn.eventually_lineLeftDeriv_liftsToAmbientFunctional_of_lineSubgradientLift
    {s : Set E} {u : E → ℝ} {x : E} (hu : ConvexOn ℝ s u)
    (hsegmentInterior : ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, x + t • z ∈ interior s)
    (hlift : ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ q : ℝ,
        SubgradientOn (lineDomain s x z) (AleksandrovDifferentiability.lineRestriction u x z) t q →
          LineSubgradientLiftsToAmbientFunctional s u x z t q) :
    ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        LineSubgradientLiftsToAmbientFunctional s u x z t
          (leftDeriv (AleksandrovDifferentiability.lineRestriction u x z) t) := by
  filter_upwards [hsegmentInterior, hlift] with z hzsegment hzlift t ht
  exact
    ConvexOn.lineLeftDeriv_liftsToAmbientFunctional_of_lineSubgradientLift
      hu
      (x := x) (z := z) (t := t) (hzsegment t ht) (hzlift t ht)

/-- Eventual vector-valued lift of the left derivative along short segments. -/
theorem ConvexOn.eventually_lineLeftDeriv_liftsToAmbient_of_lineSubgradientLift
    {s : Set E} {u : E → ℝ} {x : E} (hu : ConvexOn ℝ s u)
    (hsegmentInterior : ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, x + t • z ∈ interior s)
    (hlift : ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ q : ℝ,
        SubgradientOn (lineDomain s x z) (AleksandrovDifferentiability.lineRestriction u x z) t q →
          LineSubgradientLiftsToAmbient s u x z t q) :
    ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        LineSubgradientLiftsToAmbient s u x z t
          (leftDeriv (AleksandrovDifferentiability.lineRestriction u x z) t) := by
  filter_upwards [hsegmentInterior, hlift] with z hzsegment hzlift t ht
  exact
    ConvexOn.lineLeftDeriv_liftsToAmbient_of_lineSubgradientLift
      hu
      (x := x) (z := z) (t := t) (hzsegment t ht) (hzlift t ht)

/-- Eventual functional lift of the right derivative along short segments. This is the
separation-facing analogue of
`ConvexOn.eventually_lineRightDeriv_realized_by_subgradient_of_lineSubgradientLift`. -/
theorem ConvexOn.eventually_lineRightDeriv_liftsToAmbientFunctional_of_lineSubgradientLift
    {s : Set E} {u : E → ℝ} {x : E} (hu : ConvexOn ℝ s u)
    (hsegmentInterior : ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, x + t • z ∈ interior s)
    (hlift : ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ q : ℝ,
        SubgradientOn (lineDomain s x z) (AleksandrovDifferentiability.lineRestriction u x z) t q →
          LineSubgradientLiftsToAmbientFunctional s u x z t q) :
    ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        LineSubgradientLiftsToAmbientFunctional s u x z t
          (rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t) := by
  filter_upwards [hsegmentInterior, hlift] with z hzsegment hzlift t ht
  exact
    ConvexOn.lineRightDeriv_liftsToAmbientFunctional_of_lineSubgradientLift
      hu
      (x := x) (z := z) (t := t) (hzsegment t ht) (hzlift t ht)

/-- Eventual vector-valued lift of the right derivative along short segments. -/
theorem ConvexOn.eventually_lineRightDeriv_liftsToAmbient_of_lineSubgradientLift
    {s : Set E} {u : E → ℝ} {x : E} (hu : ConvexOn ℝ s u)
    (hsegmentInterior : ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, x + t • z ∈ interior s)
    (hlift : ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ q : ℝ,
        SubgradientOn (lineDomain s x z) (AleksandrovDifferentiability.lineRestriction u x z) t q →
          LineSubgradientLiftsToAmbient s u x z t q) :
    ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        LineSubgradientLiftsToAmbient s u x z t
          (rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t) := by
  filter_upwards [hsegmentInterior, hlift] with z hzsegment hzlift t ht
  exact
    ConvexOn.lineRightDeriv_liftsToAmbient_of_lineSubgradientLift
      hu
      (x := x) (z := z) (t := t) (hzsegment t ht) (hzlift t ht)

/-- If every one-dimensional subgradient along short segments lifts to an ambient subgradient,
then the right derivative of the line restriction is realized by an ambient subgradient.

This packages the already-formalized one-dimensional fact
`ConvexOn.lineRestriction_rightDeriv_subgradientOn_at`: at interior line parameters the right
derivative is itself a line subgradient. -/
theorem ConvexOn.eventually_lineRightDeriv_realized_by_subgradient_of_lineSubgradientLift
    {s : Set E} {u : E → ℝ} {x : E} (hu : ConvexOn ℝ s u)
    (hsegmentInterior : ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, x + t • z ∈ interior s)
    (hlift : ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1, ∀ q : ℝ,
        SubgradientOn (lineDomain s x z) (AleksandrovDifferentiability.lineRestriction u x z) t q →
          LineSubgradientLiftsToAmbient s u x z t q) :
    ∀ᶠ z in nhds (0 : E),
      ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ∃ p : E,
          SubgradientOn s u (x + t • z) p ∧
            rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t = inner ℝ p z := by
  filter_upwards [hsegmentInterior, hlift] with z hzsegment hzlift t ht
  have hline :
      SubgradientOn (lineDomain s x z)
        (AleksandrovDifferentiability.lineRestriction u x z) t
        (rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t) :=
    ConvexOn.lineRestriction_rightDeriv_subgradientOn_at_of_line_mem_interior
      (s := s) (u := u) (x := x) (v := z) (t := t) hu (hzsegment t ht)
  exact hzlift t ht (rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t) hline

end AleksandrovDifferentiability
