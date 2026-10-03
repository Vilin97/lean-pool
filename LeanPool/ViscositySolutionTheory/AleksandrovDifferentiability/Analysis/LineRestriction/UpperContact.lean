/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.LineRestriction.Lifts

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Upper-contact line restriction consequences
-/

@[expose] public section

open scoped Topology

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem HasUpperContactWithSlopeOn.subgradientOn_of_convex_of_mem_interior
    {s : Set E} {u : E → ℝ} {x p : E} {a : ℝ}
    (h : HasUpperContactWithSlopeOn s u x p a) (hu : ConvexOn ℝ s u)
    (hx : x ∈ interior s) :
    SubgradientOn s u x p := by
  refine ⟨interior_subset hx, ?_⟩
  intro y hy
  let v : E := y - x
  have hLine :
      HasUpperContactWithSlopeOn (lineDomain s x v)
        (AleksandrovDifferentiability.lineRestriction u x v) 0 (inner ℝ p v)
        (a * ‖v‖ ^ 2) :=
    h.lineRestriction (v := v)
  have huLine : ConvexOn ℝ (lineDomain s x v)
      (AleksandrovDifferentiability.lineRestriction u x v) :=
    ConvexOn.lineRestriction (x := x) (v := v) hu
  have h0 : (0 : ℝ) ∈ interior (lineDomain s x v) :=
    zero_mem_interior_lineDomain (s := s) (x := x) (v := v) hx
  have hpLine :
      SubgradientOn (lineDomain s x v)
        (AleksandrovDifferentiability.lineRestriction u x v) 0 (inner ℝ p v) :=
    AleksandrovDifferentiability.HasUpperContactWithSlopeOn.subgradientOn_of_convex
      (S := lineDomain s x v) (f := AleksandrovDifferentiability.lineRestriction u x v)
      (x := 0) (p := inner ℝ p v) (a := a * ‖v‖ ^ 2) hLine huLine h0
  have h1 : (1 : ℝ) ∈ lineDomain s x v := by
    dsimp [lineDomain, v]
    simpa [one_smul] using hy
  have hsupport := hpLine.supporting_inequality (y := 1) h1
  simpa [AleksandrovDifferentiability.lineRestriction, v, Real.inner_apply, one_smul] using
    hsupport

/-- Upper-contact slopes for a convex function at an interior point are unique. -/
theorem HasUpperContactWithSlopeOn.slope_unique_of_convex_of_mem_interior
    {s : Set E} {u : E → ℝ} {x p q : E} {a b : ℝ}
    (hp : HasUpperContactWithSlopeOn s u x p a)
    (hq : HasUpperContactWithSlopeOn s u x q b)
    (hu : ConvexOn ℝ s u) (hx : x ∈ interior s) :
    p = q := by
  let v : E := p - q
  have hpLine :
      HasUpperContactWithSlopeOn (lineDomain s x v)
        (AleksandrovDifferentiability.lineRestriction u x v) 0 (inner ℝ p v)
        (a * ‖v‖ ^ 2) :=
    hp.lineRestriction (v := v)
  have hqLine :
      HasUpperContactWithSlopeOn (lineDomain s x v)
        (AleksandrovDifferentiability.lineRestriction u x v) 0 (inner ℝ q v)
        (b * ‖v‖ ^ 2) :=
    hq.lineRestriction (v := v)
  have huLine : ConvexOn ℝ (lineDomain s x v)
      (AleksandrovDifferentiability.lineRestriction u x v) :=
    ConvexOn.lineRestriction (x := x) (v := v) hu
  have h0 : (0 : ℝ) ∈ interior (lineDomain s x v) :=
    zero_mem_interior_lineDomain (s := s) (x := x) (v := v) hx
  rcases hpLine.leftDeriv_eq_and_rightDeriv_eq_of_convex huLine h0 with
    ⟨_, hpRight⟩
  rcases hqLine.leftDeriv_eq_and_rightDeriv_eq_of_convex huLine h0 with
    ⟨_, hqRight⟩
  have hinner : inner ℝ p v = inner ℝ q v := hpRight.symm.trans hqRight
  have hzero : inner ℝ (p - q) (p - q) = 0 := by
    dsimp [v] at hinner
    rw [inner_sub_left]
    exact sub_eq_zero.mpr hinner
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)

/-- A convex upper quadratic contact at an interior point admits a slope which is simultaneously
the contact slope and an ambient subgradient. -/
theorem HasUpperContactOn.exists_subgradient_contact_of_convex_of_mem_interior
    {s : Set E} {u : E → ℝ} {x : E} {a : ℝ}
    (h : HasUpperContactOn s u x a) (hu : ConvexOn ℝ s u) (hx : x ∈ interior s) :
    ∃ p : E, SubgradientOn s u x p ∧ HasUpperContactWithSlopeOn s u x p a := by
  rcases h.exists_slope_contact with ⟨p, hp⟩
  exact ⟨p, hp.subgradientOn_of_convex_of_mem_interior hu hx, hp⟩

/-- A convex upper quadratic contact at an interior point admits an ambient subgradient slope. -/
theorem HasUpperContactOn.exists_subgradient_of_convex_of_mem_interior
    {s : Set E} {u : E → ℝ} {x : E} {a : ℝ}
    (h : HasUpperContactOn s u x a) (hu : ConvexOn ℝ s u) (hx : x ∈ interior s) :
    ∃ p : E, SubgradientOn s u x p := by
  rcases h.exists_subgradient_contact_of_convex_of_mem_interior hu hx with ⟨p, hp, _⟩
  exact ⟨p, hp⟩

/-- A bounded upper-contact opening for a convex function gives, for every larger opening, a
slope which is both a subgradient and an upper-contact slope. -/
theorem HasUpperContactOpeningAtMostOn.exists_subgradient_contact_add_pos_of_convex_of_mem_interior
    {s : Set E} {u : E → ℝ} {x : E} {A η : ℝ}
    (h : HasUpperContactOpeningAtMostOn s u x A) (hu : ConvexOn ℝ s u)
    (hx : x ∈ interior s) (hη : 0 < η) :
    ∃ p : E, SubgradientOn s u x p ∧ HasUpperContactWithSlopeOn s u x p (A + η) :=
  (h.hasUpperContactOn_add_pos hη).exists_subgradient_contact_of_convex_of_mem_interior hu hx

/-- In the convex interior setting, an ordinary bounded upper-contact opening has a fixed slope:
all larger openings can be realized with the same upper-contact slope. -/
theorem
    HasUpperContactOpeningAtMostOn.exists_subgradient_fixedSlopeOpening_of_convex_of_mem_interior
    {s : Set E} {u : E → ℝ} {x : E} {A : ℝ}
    (h : HasUpperContactOpeningAtMostOn s u x A) (hu : ConvexOn ℝ s u)
    (hx : x ∈ interior s) :
    ∃ p : E, SubgradientOn s u x p ∧ HasUpperContactWithSlopeOpeningAtMostOn s u x p A := by
  rcases h.exists_subgradient_contact_add_pos_of_convex_of_mem_interior hu hx zero_lt_one with
    ⟨p, hpSub, hpContact⟩
  refine ⟨p, hpSub, ?_⟩
  intro η hη
  rcases h.exists_slope_contact_add_pos hη with ⟨q, hqContact⟩
  have hqp : q = p :=
    hqContact.slope_unique_of_convex_of_mem_interior hpContact hu hx
  simpa [hqp] using hqContact

/-- A subgradient controls the right derivative of every one-dimensional restriction. -/
theorem SubgradientOn.directional_le_lineRightDeriv
    {s : Set E} {u : E → ℝ} {x p v : E} (hp : SubgradientOn s u x p)
    (hu : ConvexOn ℝ s u) (h0 : (0 : ℝ) ∈ interior (lineDomain s x v)) :
    inner ℝ p v ≤ rightDeriv (lineRestriction u x v) 0 := by
  have hpLine := hp.lineRestriction_subgradientOn (v := v)
  have huLine := ConvexOn.lineRestriction (x := x) (v := v) hu
  simpa using hpLine.le_rightDeriv_of_convex huLine h0

/-- A subgradient at an arbitrary point of a line controls the right derivative of the line
restriction at the corresponding parameter. -/
theorem SubgradientOn.directional_le_lineRightDeriv_at
    {s : Set E} {u : E → ℝ} {x p v : E} {t : ℝ}
    (hp : SubgradientOn s u (x + t • v) p) (hu : ConvexOn ℝ s u)
    (ht : t ∈ interior (lineDomain s x v)) :
    inner ℝ p v ≤ rightDeriv (lineRestriction u x v) t := by
  have hpLine := hp.lineRestriction_subgradientOn_at (x := x) (v := v) (t := t)
  have huLine := ConvexOn.lineRestriction (x := x) (v := v) hu
  simpa using hpLine.le_rightDeriv_of_convex huLine ht

/-- A subgradient controls the left derivative of every one-dimensional restriction. -/
theorem SubgradientOn.lineLeftDeriv_le_directional
    {s : Set E} {u : E → ℝ} {x p v : E} (hp : SubgradientOn s u x p)
    (hu : ConvexOn ℝ s u) (h0 : (0 : ℝ) ∈ interior (lineDomain s x v)) :
    leftDeriv (lineRestriction u x v) 0 ≤ inner ℝ p v := by
  have hpLine := hp.lineRestriction_subgradientOn (v := v)
  have huLine := ConvexOn.lineRestriction (x := x) (v := v) hu
  simpa using hpLine.leftDeriv_le_of_convex huLine h0

/-- A subgradient at an arbitrary point of a line controls the left derivative of the line
restriction at the corresponding parameter. -/
theorem SubgradientOn.lineLeftDeriv_le_directional_at
    {s : Set E} {u : E → ℝ} {x p v : E} {t : ℝ}
    (hp : SubgradientOn s u (x + t • v) p) (hu : ConvexOn ℝ s u)
    (ht : t ∈ interior (lineDomain s x v)) :
    leftDeriv (lineRestriction u x v) t ≤ inner ℝ p v := by
  have hpLine := hp.lineRestriction_subgradientOn_at (x := x) (v := v) (t := t)
  have huLine := ConvexOn.lineRestriction (x := x) (v := v) hu
  simpa using hpLine.leftDeriv_le_of_convex huLine ht

/-- At an interior line parameter, every ambient subgradient directional value lies in the
one-dimensional subgradient interval of the line restriction. -/
theorem SubgradientOn.directional_mem_Icc_leftDeriv_rightDeriv_at
    {s : Set E} {u : E → ℝ} {x p v : E} {t : ℝ}
    (hp : SubgradientOn s u (x + t • v) p) (hu : ConvexOn ℝ s u)
    (ht : t ∈ interior (lineDomain s x v)) :
    inner ℝ p v ∈ Set.Icc
      (leftDeriv (lineRestriction u x v) t)
      (rightDeriv (lineRestriction u x v) t) :=
  ⟨hp.lineLeftDeriv_le_directional_at hu ht, hp.directional_le_lineRightDeriv_at hu ht⟩

/-- Interior-domain version of the right-derivative bound along a line. -/
theorem SubgradientOn.directional_le_lineRightDeriv_of_mem_interior
    {s : Set E} {u : E → ℝ} {x p v : E} (hp : SubgradientOn s u x p)
    (hu : ConvexOn ℝ s u) (hx : x ∈ interior s) :
    inner ℝ p v ≤ rightDeriv (lineRestriction u x v) 0 :=
  hp.directional_le_lineRightDeriv hu (zero_mem_interior_lineDomain hx)

/-- Interior-domain version of the left-derivative bound along a line. -/
theorem SubgradientOn.lineLeftDeriv_le_directional_of_mem_interior
    {s : Set E} {u : E → ℝ} {x p v : E} (hp : SubgradientOn s u x p)
    (hu : ConvexOn ℝ s u) (hx : x ∈ interior s) :
    leftDeriv (lineRestriction u x v) 0 ≤ inner ℝ p v :=
  hp.lineLeftDeriv_le_directional hu (zero_mem_interior_lineDomain hx)

/-- Interior-domain version of the arbitrary-parameter right-derivative bound along a line. -/
theorem SubgradientOn.directional_le_lineRightDeriv_at_of_mem_interior
    {s : Set E} {u : E → ℝ} {x p v : E} {t : ℝ}
    (hp : SubgradientOn s u (x + t • v) p) (hu : ConvexOn ℝ s u)
    (ht : x + t • v ∈ interior s) :
    inner ℝ p v ≤ rightDeriv (lineRestriction u x v) t :=
  hp.directional_le_lineRightDeriv_at hu (mem_interior_lineDomain_of_line_mem_interior ht)

/-- Interior-domain version of the arbitrary-parameter left-derivative bound along a line. -/
theorem SubgradientOn.lineLeftDeriv_le_directional_at_of_mem_interior
    {s : Set E} {u : E → ℝ} {x p v : E} {t : ℝ}
    (hp : SubgradientOn s u (x + t • v) p) (hu : ConvexOn ℝ s u)
    (ht : x + t • v ∈ interior s) :
    leftDeriv (lineRestriction u x v) t ≤ inner ℝ p v :=
  hp.lineLeftDeriv_le_directional_at hu (mem_interior_lineDomain_of_line_mem_interior ht)

/-- Interior-domain version of the interval bound for ambient subgradient directional values. -/
theorem SubgradientOn.directional_mem_Icc_leftDeriv_rightDeriv_at_of_mem_interior
    {s : Set E} {u : E → ℝ} {x p v : E} {t : ℝ}
    (hp : SubgradientOn s u (x + t • v) p) (hu : ConvexOn ℝ s u)
    (ht : x + t • v ∈ interior s) :
    inner ℝ p v ∈ Set.Icc
      (leftDeriv (lineRestriction u x v) t)
      (rightDeriv (lineRestriction u x v) t) :=
  hp.directional_mem_Icc_leftDeriv_rightDeriv_at hu
    (mem_interior_lineDomain_of_line_mem_interior ht)

/-- If a cluster gradient dominates the right derivative of the line restriction, then it
dominates every ambient subgradient in that direction. -/
theorem SubgradientOn.exists_cluster_inner_ge_of_lineRightDeriv_le
    {s D : Set E} {u : E → ℝ} {G : E → E} {x p v : E}
    (hp : SubgradientOn s u x p) (hu : ConvexOn ℝ s u) (hx : x ∈ interior s)
    (hcluster : ∃ q ∈ HasSubgradientLinearizationOnAt.GradientClusterSet D G x,
      rightDeriv (lineRestriction u x v) 0 ≤ inner ℝ q v) :
    ∃ q ∈ HasSubgradientLinearizationOnAt.GradientClusterSet D G x,
      inner ℝ p v ≤ inner ℝ q v := by
  rcases hcluster with ⟨q, hq, hright⟩
  exact ⟨q, hq, (hp.directional_le_lineRightDeriv_of_mem_interior hu hx).trans hright⟩

/-- Eventual version of the right-derivative-to-cluster bridge for all subgradients and
directions. -/
theorem eventually_directional_dominating_cluster_of_lineRightDeriv_le
    {s D approach : Set E} {u : E → ℝ} {G : E → E} {x : E}
    (hu : ConvexOn ℝ s u)
    (hinterior : ∀ᶠ y in nhdsWithin x approach, y ∈ interior s)
    (hcluster : ∀ᶠ y in nhdsWithin x approach,
      ∀ v : E, ∃ q ∈ HasSubgradientLinearizationOnAt.GradientClusterSet D G y,
        rightDeriv (lineRestriction u y v) 0 ≤ inner ℝ q v) :
    ∀ᶠ y in nhdsWithin x approach,
      ∀ p : E, SubgradientOn s u y p →
        ∀ v : E, ∃ q ∈ HasSubgradientLinearizationOnAt.GradientClusterSet D G y,
          inner ℝ p v ≤ inner ℝ q v := by
  filter_upwards [hinterior, hcluster] with y hyInterior hyCluster p hp v
  exact hp.exists_cluster_inner_ge_of_lineRightDeriv_le hu hyInterior (hyCluster v)

/-- If a subgradient has directional value at least the right derivative, then it realizes the
right derivative exactly. The reverse inequality is the general subgradient directional bound. -/
theorem SubgradientOn.lineRightDeriv_eq_inner_of_lineRightDeriv_le
    {s : Set E} {u : E → ℝ} {x p v : E} {t : ℝ}
    (hp : SubgradientOn s u (x + t • v) p) (hu : ConvexOn ℝ s u)
    (ht : t ∈ interior (lineDomain s x v))
    (hle : rightDeriv (lineRestriction u x v) t ≤ inner ℝ p v) :
    rightDeriv (lineRestriction u x v) t = inner ℝ p v :=
  le_antisymm hle (hp.directional_le_lineRightDeriv_at hu ht)

/-- Interior-domain version of
`SubgradientOn.lineRightDeriv_eq_inner_of_lineRightDeriv_le`. -/
theorem SubgradientOn.lineRightDeriv_eq_inner_of_lineRightDeriv_le_of_mem_interior
    {s : Set E} {u : E → ℝ} {x p v : E} {t : ℝ}
    (hp : SubgradientOn s u (x + t • v) p) (hu : ConvexOn ℝ s u)
    (ht : x + t • v ∈ interior s)
    (hle : rightDeriv (lineRestriction u x v) t ≤ inner ℝ p v) :
    rightDeriv (lineRestriction u x v) t = inner ℝ p v :=
  hp.lineRightDeriv_eq_inner_of_lineRightDeriv_le hu
    (mem_interior_lineDomain_of_line_mem_interior ht) hle

/-- If a subgradient has directional value at most the left derivative, then it realizes the
left derivative exactly. The reverse inequality is the general subgradient directional bound. -/
theorem SubgradientOn.lineLeftDeriv_eq_inner_of_inner_le_lineLeftDeriv
    {s : Set E} {u : E → ℝ} {x p v : E} {t : ℝ}
    (hp : SubgradientOn s u (x + t • v) p) (hu : ConvexOn ℝ s u)
    (ht : t ∈ interior (lineDomain s x v))
    (hle : inner ℝ p v ≤ leftDeriv (lineRestriction u x v) t) :
    leftDeriv (lineRestriction u x v) t = inner ℝ p v :=
  le_antisymm (hp.lineLeftDeriv_le_directional_at hu ht) hle

/-- Interior-domain version of
`SubgradientOn.lineLeftDeriv_eq_inner_of_inner_le_lineLeftDeriv`. -/
theorem SubgradientOn.lineLeftDeriv_eq_inner_of_inner_le_lineLeftDeriv_of_mem_interior
    {s : Set E} {u : E → ℝ} {x p v : E} {t : ℝ}
    (hp : SubgradientOn s u (x + t • v) p) (hu : ConvexOn ℝ s u)
    (ht : x + t • v ∈ interior s)
    (hle : inner ℝ p v ≤ leftDeriv (lineRestriction u x v) t) :
    leftDeriv (lineRestriction u x v) t = inner ℝ p v :=
  hp.lineLeftDeriv_eq_inner_of_inner_le_lineLeftDeriv hu
    (mem_interior_lineDomain_of_line_mem_interior ht) hle

/-- Compact-subdifferential right-endpoint attainment wrapper.

The hypothesis `hmax_le` is the support-function inequality expected from applying Mathlib's
separation theorem to the epigraph/line-minorant configuration. The compactness and extreme-value
boilerplate is handled here. -/
theorem ConvexOn.exists_subgradient_lineRightDeriv_eq_inner_of_isBounded_of_forall_isMaxOn
    [ProperSpace E] {s : Set E} {u : E → ℝ} {x z : E} {t : ℝ}
    (hu : ConvexOn ℝ s u) (ht : x + t • z ∈ interior s)
    (hne : {p : E | SubgradientOn s u (x + t • z) p}.Nonempty)
    (hb : Bornology.IsBounded {p : E | SubgradientOn s u (x + t • z) p})
    (hmax_le : ∀ p : E, SubgradientOn s u (x + t • z) p →
      IsMaxOn (fun q : E => inner ℝ q z)
        {q : E | SubgradientOn s u (x + t • z) q} p →
      rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t ≤ inner ℝ p z) :
    ∃ p : E, SubgradientOn s u (x + t • z) p ∧
      rightDeriv (AleksandrovDifferentiability.lineRestriction u x z) t = inner ℝ p z := by
  rcases exists_isMaxOn_inner_subgradientOn_of_isBounded
      (s := s) (u := u) (x := x + t • z) z hne hb with
    ⟨p, hp, hpmax⟩
  exact ⟨p, hp,
    hp.lineRightDeriv_eq_inner_of_lineRightDeriv_le_of_mem_interior hu ht
      (hmax_le p hp hpmax)⟩

/-- Compact-subdifferential left-endpoint attainment wrapper.

The hypothesis `hmin_le` is the support-function inequality expected from applying Mathlib's
separation theorem to the epigraph/line-minorant configuration. -/
theorem ConvexOn.exists_subgradient_lineLeftDeriv_eq_inner_of_isBounded_of_forall_isMinOn
    [ProperSpace E] {s : Set E} {u : E → ℝ} {x z : E} {t : ℝ}
    (hu : ConvexOn ℝ s u) (ht : x + t • z ∈ interior s)
    (hne : {p : E | SubgradientOn s u (x + t • z) p}.Nonempty)
    (hb : Bornology.IsBounded {p : E | SubgradientOn s u (x + t • z) p})
    (hmin_le : ∀ p : E, SubgradientOn s u (x + t • z) p →
      IsMinOn (fun q : E => inner ℝ q z)
        {q : E | SubgradientOn s u (x + t • z) q} p →
      inner ℝ p z ≤ leftDeriv (AleksandrovDifferentiability.lineRestriction u x z) t) :
    ∃ p : E, SubgradientOn s u (x + t • z) p ∧
      leftDeriv (AleksandrovDifferentiability.lineRestriction u x z) t = inner ℝ p z := by
  rcases exists_isMinOn_inner_subgradientOn_of_isBounded
      (s := s) (u := u) (x := x + t • z) z hne hb with
    ⟨p, hp, hpmin⟩
  exact ⟨p, hp,
    hp.lineLeftDeriv_eq_inner_of_inner_le_lineLeftDeriv_of_mem_interior hu ht
      (hmin_le p hp hpmin)⟩

end AleksandrovDifferentiability
