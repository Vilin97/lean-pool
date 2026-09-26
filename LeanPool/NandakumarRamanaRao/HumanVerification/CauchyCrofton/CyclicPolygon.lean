/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.HumanVerification.CauchyCrofton.Radial

/-!
# Cyclic convex polygons inscribed in a planar convex body

Given a compact convex body `K` in the plane with the origin in its interior, and a *cyclic
angle system* `A` (a strictly increasing family `θ : ℤ → ℝ` with `θ (j + m) = θ j + 2π` and all
gaps smaller than `π/2`), the points

```
vtx K A j = radPt K (A.θ j)
```

are boundary points of `K` listed in cyclic angular order.  Their convex hull (together with the
origin) is a convex polygon `polySet K A` whose boundary is, by construction, the union of the
`m` consecutive edges `segment ℝ (vtx j) (vtx (j+1))`.

The cyclic ordering of the vertices is therefore supplied by the construction; no
combinatorial analysis of an arbitrary finite planar point set is needed.
-/

@[expose] public section

open Set MeasureTheory NRR.Geometry
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace HumanVerification.CauchyCrofton

/-! ### Cyclic angle systems -/

/-- A cyclic system of `m` sample angles: strictly increasing over `ℤ`, `m`-periodic modulo a
full turn, with all gaps smaller than a quarter turn. -/
structure AngleSystem where
  /-- Number of sample directions. -/
  m : ℕ
  /-- The angles, indexed by `ℤ` and increasing by `2π` after `m` steps. -/
  θ : ℤ → ℝ
  strictMono : StrictMono θ
  period : ∀ j : ℤ, θ (j + m) = θ j + 2 * Real.pi
  gap_lt : ∀ j : ℤ, θ (j + 1) - θ j < Real.pi / 2

namespace AngleSystem

variable (A : AngleSystem)

theorem gap_pos (j : ℤ) : 0 < A.θ (j + 1) - A.θ j :=
  sub_pos.2 (A.strictMono (by omega))

theorem m_pos : 0 < A.m := by
  rcases Nat.eq_zero_or_pos A.m with h | h
  · exfalso
    have := A.period 0
    rw [h] at this
    simp at this
  · exact h

/-- Iterated periodicity. -/
theorem period_zsmul (j : ℤ) (k : ℤ) :
    A.θ (j + k * A.m) = A.θ j + k * (2 * Real.pi) := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
      have : j + ((n : ℤ) + 1) * A.m = (j + (n : ℤ) * A.m) + A.m := by ring
      rw [this, A.period, ih]
      push_cast
      ring
  | pred n ih =>
      have h1 : j + (-(n : ℤ) - 1) * A.m + A.m = j + (-(n : ℤ)) * A.m := by ring
      have h2 := A.period (j + (-(n : ℤ) - 1) * A.m)
      rw [h1, ih] at h2
      push_cast at h2 ⊢
      linarith

theorem exists_lt_angle (t : ℝ) : ∃ j : ℤ, t < A.θ j := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((t - A.θ 0) / (2 * Real.pi))
  refine ⟨0 + (n : ℤ) * A.m, ?_⟩
  rw [A.period_zsmul 0 (n : ℤ)]
  rw [div_lt_iff₀ Real.two_pi_pos] at hn
  push_cast
  linarith

theorem exists_angle_le (t : ℝ) : ∃ j : ℤ, A.θ j ≤ t := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((A.θ 0 - t) / (2 * Real.pi))
  refine ⟨0 + (-(n : ℤ)) * A.m, ?_⟩
  rw [A.period_zsmul 0 (-(n : ℤ))]
  rw [div_lt_iff₀ Real.two_pi_pos] at hn
  push_cast
  linarith

/-- Every real number lies in one of the sample intervals. -/
theorem exists_index (t : ℝ) : ∃ j : ℤ, A.θ j ≤ t ∧ t < A.θ (j + 1) := by
  obtain ⟨j0, hj0⟩ := A.exists_angle_le t
  obtain ⟨j1, hj1⟩ := A.exists_lt_angle t
  have hbdd : ∀ z ∈ {z : ℤ | A.θ z ≤ t}, z ≤ j1 := by
    intro z hz
    by_contra hcon
    push Not at hcon
    exact absurd (le_trans (le_of_lt (A.strictMono hcon)) hz) (not_le.2 hj1)
  obtain ⟨j, hj, hjmax⟩ := Int.exists_greatest_of_bdd ⟨j1, hbdd⟩ ⟨j0, hj0⟩
  refine ⟨j, hj, ?_⟩
  by_contra hcon
  push Not at hcon
  exact absurd (hjmax (j + 1) hcon) (by omega)

/-- Every real number lies in one of the sample intervals with index in the base window. -/
theorem exists_index_mem_range (t : ℝ) (ht : t ∈ Set.Ico (A.θ 0) (A.θ 0 + 2 * Real.pi)) :
    ∃ j : ℤ, 0 ≤ j ∧ j < A.m ∧ A.θ j ≤ t ∧ t < A.θ (j + 1) := by
  obtain ⟨j, hj1, hj2⟩ := A.exists_index t
  refine ⟨j, ?_, ?_, hj1, hj2⟩
  · by_contra hcon
    push Not at hcon
    have : j + 1 ≤ 0 := by omega
    have hle : A.θ (j + 1) ≤ A.θ 0 := A.strictMono.monotone this
    have := ht.1
    linarith
  · by_contra hcon
    push Not at hcon
    have hle : A.θ (A.m : ℤ) ≤ A.θ j := A.strictMono.monotone hcon
    have hper : A.θ ((A.m : ℤ)) = A.θ 0 + 2 * Real.pi := by
      have := A.period 0
      simpa using this
    have := ht.2
    linarith

end AngleSystem

/-! ### The inscribed polygon -/

variable (K : Body) (A : AngleSystem)

/-- The `j`-th vertex: the radial boundary point of `K` at angle `A.θ j`. -/
def vtx (j : ℤ) : Point2 := radPt K (A.θ j)

/-- The vertex set of the polygon, together with the origin. -/
def polyVerts : Set Point2 := insert 0 (Set.range fun j : Fin A.m => vtx K A (j : ℤ))

/-- The inscribed polygon attached to `K` and the angle system `A`. -/
def polySet : Set Point2 := convexHull ℝ (polyVerts K A)

/-- The `j`-th edge. -/
def edge (j : ℤ) : Set Point2 := segment ℝ (vtx K A j) (vtx K A (j + 1))

/-- Outward normal of the `j`-th edge. -/
def nrm (j : ℤ) : Point2 := rot (vtx K A j - vtx K A (j + 1))

/-- Value of the `j`-th edge functional. -/
def dd (j : ℤ) : ℝ := cross (vtx K A j) (vtx K A (j + 1))

variable {K A}

theorem vtx_periodic (j : ℤ) : vtx K A (j + A.m) = vtx K A j := by
  rw [vtx, vtx, A.period j, radPt_periodic]

theorem vtx_periodic_zsmul (j k : ℤ) : vtx K A (j + k * A.m) = vtx K A j := by
  rw [vtx, vtx, A.period_zsmul j k]
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
      have : A.θ j + ((n : ℤ) + 1 : ℤ) * (2 * Real.pi)
          = (A.θ j + (n : ℤ) * (2 * Real.pi)) + 2 * Real.pi := by push_cast; ring
      rw [this, radPt_periodic, ih]
  | pred n ih =>
      have h1 : A.θ j + (-(n : ℤ) : ℤ) * (2 * Real.pi)
          = (A.θ j + (-(n : ℤ) - 1 : ℤ) * (2 * Real.pi)) + 2 * Real.pi := by push_cast; ring
      rw [← ih, h1, radPt_periodic]

theorem vtx_mem_polyVerts (j : ℤ) : vtx K A j ∈ polyVerts K A := by
  have hm : 0 < (A.m : ℤ) := by exact_mod_cast A.m_pos
  have hmod : 0 ≤ j % A.m ∧ j % A.m < A.m := ⟨Int.emod_nonneg j (by omega), Int.emod_lt_of_pos j hm⟩
  have hsplit : j = j % A.m + (j / A.m) * A.m := by
    rw [Int.emod_add_ediv_mul j (A.m : ℤ)]
  have heq : vtx K A j = vtx K A (j % A.m) := by
    conv_lhs => rw [hsplit]
    exact vtx_periodic_zsmul _ _
  rw [heq]
  have hlt : (j % A.m).toNat < A.m := by omega
  refine Set.mem_insert_iff.2 (Or.inr ⟨⟨(j % A.m).toNat, hlt⟩, ?_⟩)
  change vtx K A (((⟨(j % A.m).toNat, hlt⟩ : Fin A.m) : ℤ)) = vtx K A (j % A.m)
  congr 1
  simp [Int.toNat_of_nonneg hmod.1]

/-- Every vertex index is equivalent to one in the base window. -/
theorem exists_fin_vtx_eq (k : ℤ) : ∃ i : Fin A.m, vtx K A (i : ℤ) = vtx K A k := by
  have hm : 0 < (A.m : ℤ) := by exact_mod_cast A.m_pos
  have hmod : 0 ≤ k % A.m ∧ k % A.m < A.m :=
    ⟨Int.emod_nonneg k (by omega), Int.emod_lt_of_pos k hm⟩
  have hsplit : k = k % A.m + (k / A.m) * A.m := by
    rw [Int.emod_add_ediv_mul k (A.m : ℤ)]
  have hlt : (k % A.m).toNat < A.m := by omega
  refine ⟨⟨(k % A.m).toNat, hlt⟩, ?_⟩
  show vtx K A (((⟨(k % A.m).toNat, hlt⟩ : Fin A.m) : ℤ)) = vtx K A k
  have hcast : (((⟨(k % A.m).toNat, hlt⟩ : Fin A.m) : ℤ)) = k % A.m := by
    simp [Int.toNat_of_nonneg hmod.1]
  rw [hcast]
  conv_rhs => rw [hsplit]
  exact (vtx_periodic_zsmul _ _).symm

theorem finite_polyVerts : (polyVerts K A).Finite :=
  (Set.finite_range _).insert _

theorem vtx_mem (h0 : (0 : Point2) ∈ (K : Set Point2)) (j : ℤ) :
    vtx K A j ∈ (K : Set Point2) := radPt_mem h0 _

theorem polySet_subset (h0 : (0 : Point2) ∈ (K : Set Point2)) :
    polySet K A ⊆ (K : Set Point2) := by
  refine convexHull_min ?_ K.convex
  rintro x (rfl | ⟨j, rfl⟩)
  · exact h0
  · exact vtx_mem h0 _

theorem isCompact_polySet : IsCompact (polySet K A) :=
  (finite_polyVerts (K := K) (A := A)).isCompact_convexHull (𝕜 := ℝ)

theorem convex_polySet : Convex ℝ (polySet K A) := convex_convexHull _ _

theorem zero_mem_polySet : (0 : Point2) ∈ polySet K A :=
  subset_convexHull _ _ (Set.mem_insert _ _)

theorem vtx_mem_polySet (j : ℤ) : vtx K A j ∈ polySet K A :=
  subset_convexHull _ _ (vtx_mem_polyVerts j)

theorem edge_subset_polySet (j : ℤ) : edge K A j ⊆ polySet K A :=
  (convex_polySet).segment_subset (vtx_mem_polySet j) (vtx_mem_polySet (j + 1))

/-! ### Edge functionals -/

theorem inner_vtx_nrm_left (j : ℤ) :
    (inner ℝ (vtx K A j) (nrm K A j) : ℝ) = dd K A j := by
  simp only [nrm, dd, inner_rot, cross]
  simp [PiLp.sub_apply]
  ring

theorem inner_vtx_nrm_right (j : ℤ) :
    (inner ℝ (vtx K A (j + 1)) (nrm K A j) : ℝ) = dd K A j := by
  simp only [nrm, dd, inner_rot, cross]
  simp [PiLp.sub_apply]
  ring

theorem dd_pos (h0 : (0 : Point2) ∈ interior (K : Set Point2)) (j : ℤ) : 0 < dd K A j := by
  have hgap := A.gap_pos j
  have hgap2 := A.gap_lt j
  have hsin : 0 < Real.sin (A.θ (j + 1) - A.θ j) :=
    Real.sin_pos_of_pos_of_lt_pi hgap (by linarith [Real.pi_pos])
  have h1 : 0 < rad K (A.θ j) := rad_pos h0 _
  have h2 : 0 < rad K (A.θ (j + 1)) := rad_pos h0 _
  rw [dd, vtx, vtx, radPt_eq, radPt_eq, cross_smul_left, cross_smul_right, cross_circleVec]
  positivity

theorem nrm_ne_zero (h0 : (0 : Point2) ∈ interior (K : Set Point2)) (j : ℤ) :
    nrm K A j ≠ 0 := by
  apply rot_ne_zero
  intro hzero
  have hv : vtx K A j = vtx K A (j + 1) := by
    have := sub_eq_zero.mp hzero
    exact this
  have := dd_pos h0 (K := K) (A := A) j
  rw [dd, hv, cross_self] at this
  exact lt_irrefl 0 this

/-- Points of the `j`-th edge lie on the edge line. -/
theorem inner_nrm_of_mem_edge {j : ℤ} {x : Point2} (hx : x ∈ edge K A j) :
    (inner ℝ x (nrm K A j) : ℝ) = dd K A j := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hx
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_vtx_nrm_left, inner_vtx_nrm_right, ← add_mul, hab, one_mul]

/-- **Blocking, in vertex form.** A vertex lying (in index order) between two vertices whose
functional value is at least `s > 0` also has value at least `s`, provided the two directions
span at most a half turn. -/
theorem inner_vtx_ge_of_between (h0 : (0 : Point2) ∈ interior (K : Set Point2))
    {n : Point2} {s : ℝ} (hs : 0 < s) {j i k : ℤ} (hji : j < i) (hik : i < k)
    (hspread : A.θ k - A.θ j ≤ Real.pi)
    (hj : s ≤ (inner ℝ (vtx K A j) n : ℝ)) (hk : s ≤ (inner ℝ (vtx K A k) n : ℝ)) :
    s ≤ (inner ℝ (vtx K A i) n : ℝ) :=
  le_inner_radPt_of_blocking (A.strictMono hji) (A.strictMono hik) hspread
    (rad_pos h0 _) (rad_pos h0 _) (radPt_mem (interior_subset h0) _)
    (radPt_mem (interior_subset h0) _) hs hj hk

/-- Strict form of `inner_vtx_ge_of_between`. -/
theorem inner_vtx_gt_of_between (h0 : (0 : Point2) ∈ interior (K : Set Point2))
    {n : Point2} {s : ℝ} (hs : 0 < s) {j i k : ℤ} (hji : j < i) (hik : i < k)
    (hspread : A.θ k - A.θ j ≤ Real.pi)
    (hj : s ≤ (inner ℝ (vtx K A j) n : ℝ)) (hk : s < (inner ℝ (vtx K A k) n : ℝ)) :
    s < (inner ℝ (vtx K A i) n : ℝ) :=
  lt_inner_radPt_of_blocking (A.strictMono hji) (A.strictMono hik) hspread
    (rad_pos h0 _) (rad_pos h0 _) (radPt_mem (interior_subset h0) _)
    (radPt_mem (interior_subset h0) _) hs hj hk

/-- Variant of `inner_vtx_gt_of_between` with the strict bound on the left. -/
theorem inner_vtx_gt_of_between' (h0 : (0 : Point2) ∈ interior (K : Set Point2))
    {n : Point2} {s : ℝ} (hs : 0 < s) {j i k : ℤ} (hji : j < i) (hik : i < k)
    (hspread : A.θ k - A.θ j ≤ Real.pi)
    (hj : s < (inner ℝ (vtx K A j) n : ℝ)) (hk : s ≤ (inner ℝ (vtx K A k) n : ℝ)) :
    s < (inner ℝ (vtx K A i) n : ℝ) :=
  lt_inner_radPt_of_blocking' (A.strictMono hji) (A.strictMono hik) hspread
    (rad_pos h0 _) (rad_pos h0 _) (radPt_mem (interior_subset h0) _)
    (radPt_mem (interior_subset h0) _) hs hj hk

/-! ### The supporting-line property

This is the geometric heart of the construction: each edge line supports the whole vertex set.
-/

/-- **Supporting-line property (abstract form).** If a linear functional takes the same positive
value `d` at two consecutive vertices, then it is `≤ d` on every vertex. -/
theorem inner_vtx_le_of_consecutive_eq
    (h0 : (0 : Point2) ∈ interior (K : Set Point2)) {j : ℤ} {n : Point2} {d : ℝ}
    (hd : 0 < d) (h1 : (inner ℝ (vtx K A j) n : ℝ) = d)
    (h2 : (inner ℝ (vtx K A (j + 1)) n : ℝ) = d) (k : ℤ) :
    (inner ℝ (vtx K A k) n : ℝ) ≤ d := by
  have hmZ : (0 : ℤ) < A.m := by exact_mod_cast A.m_pos
  -- reduce to a representative in the window `[j, j + m)`
  set k' : ℤ := j + (k - j) % A.m with hk'
  have hk'eq : vtx K A k = vtx K A k' := by
    have hsplit : k = k' + ((k - j) / A.m) * A.m := by
      rw [hk']
      have := Int.emod_add_ediv_mul (k - j) (A.m : ℤ)
      omega
    conv_lhs => rw [hsplit]
    exact vtx_periodic_zsmul _ _
  have hk'low : j ≤ k' := by
    have := Int.emod_nonneg (k - j) (by omega : (A.m : ℤ) ≠ 0)
    omega
  have hk'high : k' < j + A.m := by
    have := Int.emod_lt_of_pos (k - j) hmZ
    omega
  rw [hk'eq]
  -- the two trivial cases
  rcases eq_or_lt_of_le hk'low with heq | hlt1
  · rw [← heq, h1]
  rcases eq_or_lt_of_le (show j + 1 ≤ k' by omega) with heq2 | hlt2
  · rw [← heq2, h2]
  -- now `j + 1 < k' < j + m`
  by_contra hcon
  push Not at hcon
  have hper : A.θ (j + A.m) = A.θ j + 2 * Real.pi := A.period j
  have hper1 : A.θ (j + 1 + A.m) = A.θ (j + 1) + 2 * Real.pi := A.period (j + 1)
  have hvper : vtx K A (j + A.m) = vtx K A j := vtx_periodic j
  have hvper1 : vtx K A (j + 1 + A.m) = vtx K A (j + 1) := vtx_periodic (j + 1)
  by_cases hspread : A.θ k' - A.θ j ≤ Real.pi
  · -- the vertex `j + 1` would be pushed strictly beyond the edge line
    have := inner_vtx_gt_of_between h0 hd (j := j) (i := j + 1) (k := k')
      (by omega) hlt2 hspread (le_of_eq h1.symm) hcon
    rw [h2] at this
    exact lt_irrefl d this
  · push Not at hspread
    -- the complementary arc is short
    have hshort : A.θ (j + A.m) - A.θ k' ≤ Real.pi := by
      rw [hper]; linarith
    have hstep : d < (inner ℝ (vtx K A (j + A.m - 1)) n : ℝ) := by
      rcases eq_or_lt_of_le (show k' ≤ j + A.m - 1 by omega) with heq3 | hlt3
      · rw [← heq3]; exact hcon
      · refine inner_vtx_gt_of_between' h0 hd (j := k') (i := j + A.m - 1) (k := j + A.m)
          hlt3 (by omega) hshort hcon ?_
        rw [hvper, h1]
    -- and then the vertex `j + m` is pushed beyond, a contradiction
    have hspread2 : A.θ (j + A.m + 1) - A.θ (j + A.m - 1) ≤ Real.pi := by
      have g1 := A.gap_lt (j + A.m - 1)
      have g2 := A.gap_lt (j + A.m)
      have e1 : j + A.m - 1 + 1 = j + A.m := by ring
      rw [e1] at g1
      linarith
    have hend : (inner ℝ (vtx K A (j + A.m + 1)) n : ℝ) = d := by
      have : vtx K A (j + A.m + 1) = vtx K A (j + 1) := by
        have : j + A.m + 1 = j + 1 + A.m := by ring
        rw [this, hvper1]
      rw [this, h2]
    have := inner_vtx_gt_of_between' h0 hd (j := j + A.m - 1) (i := j + A.m) (k := j + A.m + 1)
      (by omega) (by omega) hspread2 hstep (le_of_eq hend.symm)
    rw [hvper, h1] at this
    exact lt_irrefl d this

/-- **Supporting-line property.** -/
theorem inner_vtx_nrm_le (h0 : (0 : Point2) ∈ interior (K : Set Point2)) (j k : ℤ) :
    (inner ℝ (vtx K A k) (nrm K A j) : ℝ) ≤ dd K A j :=
  inner_vtx_le_of_consecutive_eq h0 (dd_pos h0 j) (inner_vtx_nrm_left j)
    (inner_vtx_nrm_right j) k

/-- The polygon lies in each edge half-plane. -/
theorem polySet_subset_halfspace (h0 : (0 : Point2) ∈ interior (K : Set Point2)) (j : ℤ) :
    polySet K A ⊆ {x : Point2 | (inner ℝ x (nrm K A j) : ℝ) ≤ dd K A j} := by
  refine convexHull_min ?_ ?_
  · rintro x (rfl | ⟨i, rfl⟩)
    · simpa using (dd_pos h0 j).le
    · exact inner_vtx_nrm_le h0 j _
  · exact convex_halfSpace_le ⟨fun a b => inner_add_left _ _ _,
      fun c a => real_inner_smul_left _ _ _⟩ _

/-! ### Radial description of the polygon -/

/-- Inner product of the `j`-th vertex direction with the `j`-th normal. -/
theorem inner_circleVec_nrm_left (h0 : (0 : Point2) ∈ interior (K : Set Point2)) (j : ℤ) :
    (inner ℝ (circleVec (A.θ j)) (nrm K A j) : ℝ) = dd K A j / rad K (A.θ j) := by
  have hr : 0 < rad K (A.θ j) := rad_pos h0 _
  have := inner_vtx_nrm_left (K := K) (A := A) j
  rw [vtx, radPt_eq, real_inner_smul_left] at this
  field_simp [hr.ne'] at this ⊢
  linarith

theorem inner_circleVec_nrm_right (h0 : (0 : Point2) ∈ interior (K : Set Point2)) (j : ℤ) :
    (inner ℝ (circleVec (A.θ (j + 1))) (nrm K A j) : ℝ) = dd K A j / rad K (A.θ (j + 1)) := by
  have hr : 0 < rad K (A.θ (j + 1)) := rad_pos h0 _
  have := inner_vtx_nrm_right (K := K) (A := A) j
  rw [vtx, radPt_eq, real_inner_smul_left] at this
  field_simp [hr.ne'] at this ⊢
  linarith

/-- A direction in the `j`-th sector, written in the cone of the two edge directions. -/
theorem circleVec_cone_sector (j : ℤ) (t : ℝ) :
    Real.sin (A.θ (j + 1) - t) • circleVec (A.θ j)
        + Real.sin (t - A.θ j) • circleVec (A.θ (j + 1))
      = Real.sin (A.θ (j + 1) - A.θ j) • circleVec t :=
  circleVec_cone_identity _ _ _

/-- On a sector, the edge normal has positive inner product with every direction. -/
theorem inner_circleVec_nrm_pos (h0 : (0 : Point2) ∈ interior (K : Set Point2))
    {j : ℤ} {t : ℝ} (h1 : A.θ j ≤ t) (h2 : t ≤ A.θ (j + 1)) :
    0 < (inner ℝ (circleVec t) (nrm K A j) : ℝ) := by
  have hgap := A.gap_pos j
  have hgap2 := A.gap_lt j
  have hpi := Real.pi_pos
  have hsgap : 0 < Real.sin (A.θ (j + 1) - A.θ j) :=
    Real.sin_pos_of_pos_of_lt_pi hgap (by linarith)
  have hcone := congrArg (fun z : Point2 => (inner ℝ z (nrm K A j) : ℝ))
    (circleVec_cone_sector (A := A) j t)
  simp only [inner_add_left, real_inner_smul_left] at hcone
  rw [inner_circleVec_nrm_left h0, inner_circleVec_nrm_right h0] at hcone
  have hd := dd_pos h0 (K := K) (A := A) j
  have hr1 : 0 < rad K (A.θ j) := rad_pos h0 _
  have hr2 : 0 < rad K (A.θ (j + 1)) := rad_pos h0 _
  have hs1 : 0 ≤ Real.sin (A.θ (j + 1) - t) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hs2 : 0 ≤ Real.sin (t - A.θ j) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  rcases eq_or_lt_of_le h2 with rfl | hlt
  · simp only [sub_self, Real.sin_zero, zero_mul, zero_add] at hcone
    nlinarith [div_pos hd hr2]
  · have hpos : 0 < Real.sin (A.θ (j + 1) - t) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    nlinarith [div_pos hd hr1, div_pos hd hr2]

/-- The point where the ray of angle `t` meets the `j`-th edge line. -/
def rayPt (K : Body) (A : AngleSystem) (j : ℤ) (t : ℝ) : Point2 :=
  (dd K A j / (inner ℝ (circleVec t) (nrm K A j) : ℝ)) • circleVec t

/-- The ray of an angle in the `j`-th sector meets the `j`-th edge. -/
theorem rayPt_mem_edge (h0 : (0 : Point2) ∈ interior (K : Set Point2))
    {j : ℤ} {t : ℝ} (h1 : A.θ j ≤ t) (h2 : t ≤ A.θ (j + 1)) :
    rayPt K A j t ∈ edge K A j := by
  have hgap := A.gap_pos j
  have hgap2 := A.gap_lt j
  have hpi := Real.pi_pos
  have hsgap : 0 < Real.sin (A.θ (j + 1) - A.θ j) :=
    Real.sin_pos_of_pos_of_lt_pi hgap (by linarith)
  have hc := inner_circleVec_nrm_pos h0 h1 h2
  have hd := dd_pos h0 (K := K) (A := A) j
  have hr1 : 0 < rad K (A.θ j) := rad_pos h0 _
  have hr2 : 0 < rad K (A.θ (j + 1)) := rad_pos h0 _
  have hs1 : 0 ≤ Real.sin (A.θ (j + 1) - t) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hs2 : 0 ≤ Real.sin (t - A.θ j) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  set c : ℝ := (inner ℝ (circleVec t) (nrm K A j) : ℝ) with hcdef
  set a : ℝ := (dd K A j / c) *
    (Real.sin (A.θ (j + 1) - t) / (Real.sin (A.θ (j + 1) - A.θ j) * rad K (A.θ j))) with hadef
  set b : ℝ := (dd K A j / c) *
    (Real.sin (t - A.θ j) / (Real.sin (A.θ (j + 1) - A.θ j) * rad K (A.θ (j + 1)))) with hbdef
  have ha : 0 ≤ a := by
    rw [hadef]; positivity
  have hb : 0 ≤ b := by
    rw [hbdef]; positivity
  have hcomb : a • vtx K A j + b • vtx K A (j + 1) = rayPt K A j t := by
    rw [vtx, vtx, radPt_eq, radPt_eq, smul_smul, smul_smul, rayPt]
    have e1 : a * rad K (A.θ j)
        = (dd K A j / (c * Real.sin (A.θ (j + 1) - A.θ j))) * Real.sin (A.θ (j + 1) - t) := by
      rw [hadef]; field_simp
    have e2 : b * rad K (A.θ (j + 1))
        = (dd K A j / (c * Real.sin (A.θ (j + 1) - A.θ j))) * Real.sin (t - A.θ j) := by
      rw [hbdef]; field_simp
    rw [e1, e2, ← smul_smul, ← smul_smul, ← smul_add,
      circleVec_cone_sector (A := A) j t, smul_smul]
    congr 1
    field_simp
    rw [← hcdef]
    field_simp
  have hinner : (inner ℝ (rayPt K A j t) (nrm K A j) : ℝ) = dd K A j := by
    rw [rayPt, real_inner_smul_left, ← hcdef]
    field_simp
  rw [← hcomb, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_vtx_nrm_left, inner_vtx_nrm_right] at hinner
  have hab1 : a + b = 1 := by
    have : (a + b) * dd K A j = 1 * dd K A j := by rw [one_mul, add_mul]; linarith
    exact mul_right_cancel₀ hd.ne' this
  exact ⟨a, b, ha, hb, hab1, hcomb⟩

/-- A ball around the origin is contained in the polygon. -/
theorem exists_ball_subset_polySet (h0 : (0 : Point2) ∈ interior (K : Set Point2)) :
    ∃ ε > 0, Metric.ball (0 : Point2) ε ⊆ polySet K A := by
  classical
  have hmpos := A.m_pos
  have hne : (Finset.univ : Finset (Fin A.m)).Nonempty := by
    have : Nonempty (Fin A.m) := ⟨⟨0, hmpos⟩⟩
    exact Finset.univ_nonempty
  set ε : ℝ := Finset.inf' Finset.univ hne
    (fun i : Fin A.m => dd K A (i : ℤ) / ‖nrm K A (i : ℤ)‖) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef, Finset.lt_inf'_iff]
    intro i _
    have hd := dd_pos h0 (K := K) (A := A) (i : ℤ)
    have hn : 0 < ‖nrm K A (i : ℤ)‖ := norm_pos_iff.2 (nrm_ne_zero h0 _)
    positivity
  refine ⟨ε, hεpos, ?_⟩
  intro x hx
  rcases eq_or_ne x 0 with rfl | hxne
  · exact zero_mem_polySet
  have hxnorm : ‖x‖ < ε := by
    have := Metric.mem_ball.1 hx
    simpa [dist_zero_right] using this
  obtain ⟨t, htmem, hxt⟩ := exists_angle x (A.θ 0)
  obtain ⟨j, hj0, hjm, hj1, hj2⟩ := A.exists_index_mem_range t htmem
  have hc := inner_circleVec_nrm_pos h0 hj1 hj2.le
  have hd := dd_pos h0 (K := K) (A := A) j
  have hn : 0 < ‖nrm K A j‖ := norm_pos_iff.2 (nrm_ne_zero h0 _)
  have hle : ε ≤ dd K A j / ‖nrm K A j‖ := by
    have hlt : j.toNat < A.m := by omega
    have := Finset.inf'_le (s := (Finset.univ : Finset (Fin A.m)))
      (fun i : Fin A.m => dd K A (i : ℤ) / ‖nrm K A (i : ℤ)‖)
      (b := (⟨j.toNat, hlt⟩ : Fin A.m)) (Finset.mem_univ _)
    have hcast : (((⟨j.toNat, hlt⟩ : Fin A.m) : ℤ)) = j := by
      simp [Int.toNat_of_nonneg hj0]
    rw [hcast] at this
    exact this
  have hcs : (inner ℝ (circleVec t) (nrm K A j) : ℝ) ≤ ‖nrm K A j‖ := by
    have h := real_inner_le_norm (circleVec t) (nrm K A j)
    simpa using h
  have hxc : ‖x‖ * (inner ℝ (circleVec t) (nrm K A j) : ℝ) ≤ dd K A j := by
    have h1 : ‖x‖ * (inner ℝ (circleVec t) (nrm K A j) : ℝ) ≤ ‖x‖ * ‖nrm K A j‖ :=
      mul_le_mul_of_nonneg_left hcs (norm_nonneg x)
    have h2 : ‖x‖ * ‖nrm K A j‖ ≤ ε * ‖nrm K A j‖ :=
      mul_le_mul_of_nonneg_right hxnorm.le hn.le
    have h3 : ε * ‖nrm K A j‖ ≤ dd K A j := by
      rw [le_div_iff₀ hn] at hle
      exact hle
    linarith
  set μ : ℝ := dd K A j / (inner ℝ (circleVec t) (nrm K A j) : ℝ) with hμdef
  have hμpos : 0 < μ := by rw [hμdef]; positivity
  have hxμ : ‖x‖ ≤ μ := by
    rw [hμdef, le_div_iff₀ hc]
    exact hxc
  have hray : rayPt K A j t = μ • circleVec t := rfl
  have hmem : rayPt K A j t ∈ polySet K A :=
    edge_subset_polySet j (rayPt_mem_edge h0 hj1 hj2.le)
  have hxeq : x = (‖x‖ / μ) • rayPt K A j t + (1 - ‖x‖ / μ) • (0 : Point2) := by
    rw [hray, smul_zero, add_zero, smul_smul]
    rw [div_mul_cancel₀ _ hμpos.ne']
    exact hxt
  rw [hxeq]
  refine convex_polySet hmem zero_mem_polySet (by positivity) ?_ (by ring)
  have : ‖x‖ / μ ≤ 1 := by
    rw [div_le_one hμpos]
    exact hxμ
  linarith

theorem zero_mem_interior_polySet (h0 : (0 : Point2) ∈ interior (K : Set Point2)) :
    (0 : Point2) ∈ interior (polySet K A) := by
  obtain ⟨ε, hε, hsub⟩ := exists_ball_subset_polySet h0
  exact mem_interior.2 ⟨Metric.ball 0 ε, hsub, Metric.isOpen_ball, Metric.mem_ball_self hε⟩

/-- The polygon, as a convex body. -/
def polyBody (K : Body) (A : AngleSystem) (h0 : (0 : Point2) ∈ interior (K : Set Point2)) :
    Body where
  carrier := polySet K A
  convex' := convex_polySet
  isCompact' := isCompact_polySet
  interior_nonempty' := ⟨0, zero_mem_interior_polySet h0⟩

@[simp] theorem polyBody_carrier (h0 : (0 : Point2) ∈ interior (K : Set Point2)) :
    ((polyBody K A h0 : Body) : Set Point2) = polySet K A := rfl

/-! ### The boundary decomposition -/

/-- Every edge is contained in the boundary of the polygon. -/
theorem edge_subset_frontier (h0 : (0 : Point2) ∈ interior (K : Set Point2)) (j : ℤ) :
    edge K A j ⊆ frontier (polySet K A) := by
  intro x hx
  have hxP : x ∈ polySet K A := edge_subset_polySet j hx
  rw [(isCompact_polySet (K := K) (A := A)).isClosed.frontier_eq]
  refine ⟨hxP, ?_⟩
  intro hint
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hint
  have hn : 0 < ‖nrm K A j‖ := norm_pos_iff.2 (nrm_ne_zero h0 j)
  have hxinner : (inner ℝ x (nrm K A j) : ℝ) = dd K A j := inner_nrm_of_mem_edge hx
  set y : Point2 := x + (δ / (2 * ‖nrm K A j‖)) • nrm K A j with hy
  have hyball : y ∈ Metric.ball x δ := by
    rw [Metric.mem_ball, dist_eq_norm, hy]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ δ / (2 * ‖nrm K A j‖))]
    have hcalc : δ / (2 * ‖nrm K A j‖) * ‖nrm K A j‖ = δ / 2 := by
      field_simp
    rw [hcalc]
    linarith
  have hyP : y ∈ polySet K A := interior_subset (hball hyball)
  have hyinner : (inner ℝ y (nrm K A j) : ℝ) = dd K A j + δ * ‖nrm K A j‖ / 2 := by
    rw [hy, inner_add_left, real_inner_smul_left, hxinner, real_inner_self_eq_norm_sq]
    field_simp
  have hle := polySet_subset_halfspace h0 j hyP
  simp only [Set.mem_ofPred_eq, hyinner] at hle
  nlinarith

/-- **Boundary decomposition.** The boundary of the polygon is the union of its `m` edges. -/
theorem frontier_polySet (h0 : (0 : Point2) ∈ interior (K : Set Point2)) :
    frontier (polySet K A) = ⋃ j : Fin A.m, edge K A (j : ℤ) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxP : x ∈ polySet K A :=
      (isCompact_polySet (K := K) (A := A)).isClosed.frontier_subset hx
    have hxnotint : x ∉ interior (polySet K A) := by
      intro hxi
      exact absurd hx (by
        rw [(isCompact_polySet (K := K) (A := A)).isClosed.frontier_eq]
        exact fun h => h.2 hxi)
    have hxne : x ≠ 0 := by
      rintro rfl
      exact hxnotint (zero_mem_interior_polySet h0)
    obtain ⟨t, htmem, hxt⟩ := exists_angle x (A.θ 0)
    obtain ⟨j, hj0, hjm, hj1, hj2⟩ := A.exists_index_mem_range t htmem
    have hc := inner_circleVec_nrm_pos h0 hj1 hj2.le
    have hd := dd_pos h0 (K := K) (A := A) j
    set μ : ℝ := dd K A j / (inner ℝ (circleVec t) (nrm K A j) : ℝ) with hμdef
    have hμpos : 0 < μ := by rw [hμdef]; positivity
    have hray : rayPt K A j t = μ • circleVec t := rfl
    have hraymem : rayPt K A j t ∈ polySet K A :=
      edge_subset_polySet j (rayPt_mem_edge h0 hj1 hj2.le)
    have hxle : ‖x‖ ≤ μ := by
      have hle := polySet_subset_halfspace h0 j hxP
      simp only [Set.mem_ofPred_eq] at hle
      rw [hxt, real_inner_smul_left] at hle
      rw [hμdef, le_div_iff₀ hc]
      exact hle
    have hxeq : ‖x‖ = μ := by
      rcases eq_or_lt_of_le hxle with h | h
      · exact h
      · exfalso
        apply hxnotint
        have : x = (1 - ‖x‖ / μ) • (0 : Point2) + (‖x‖ / μ) • rayPt K A j t := by
          rw [hray, smul_zero, zero_add, smul_smul, div_mul_cancel₀ _ hμpos.ne']
          exact hxt
        rw [this]
        refine Convex.combo_interior_closure_mem_interior convex_polySet
          (zero_mem_interior_polySet h0) (subset_closure hraymem) ?_ (by positivity) (by ring)
        have : ‖x‖ / μ < 1 := (div_lt_one hμpos).2 h
        linarith
    have hxray : x = rayPt K A j t := by
      rw [hray, ← hxeq]; exact hxt
    have hlt : j.toNat < A.m := by omega
    refine Set.mem_iUnion.2 ⟨⟨j.toNat, hlt⟩, ?_⟩
    have hcast : (((⟨j.toNat, hlt⟩ : Fin A.m) : ℤ)) = j := by
      simp [Int.toNat_of_nonneg hj0]
    rw [hcast, hxray]
    exact rayPt_mem_edge h0 hj1 hj2.le
  · exact Set.iUnion_subset fun j => edge_subset_frontier h0 _

/-- Every point of an edge is nonzero. -/
theorem ne_zero_of_mem_edge (h0 : (0 : Point2) ∈ interior (K : Set Point2))
    {j : ℤ} {x : Point2} (hx : x ∈ edge K A j) : x ≠ 0 := by
  rintro rfl
  have h := inner_nrm_of_mem_edge hx
  simp only [inner_zero_left] at h
  exact absurd h.symm (dd_pos h0 j).ne'

/-- Every point of the `j`-th edge has an angle in the `j`-th sector. -/
theorem exists_angle_of_mem_edge (h0 : (0 : Point2) ∈ interior (K : Set Point2))
    {j : ℤ} {x : Point2} (hx : x ∈ edge K A j) :
    ∃ t, A.θ j ≤ t ∧ t ≤ A.θ (j + 1) ∧ x = ‖x‖ • circleVec t := by
  obtain ⟨a, b, ha, hb, hab, hxeq⟩ := hx
  have hxne : x ≠ 0 := ne_zero_of_mem_edge h0 ⟨a, b, ha, hb, hab, hxeq⟩
  have hr1 : 0 < rad K (A.θ j) := rad_pos h0 _
  have hr2 : 0 < rad K (A.θ (j + 1)) := rad_pos h0 _
  have hxcomb : x = (a * rad K (A.θ j)) • circleVec (A.θ j)
      + (b * rad K (A.θ (j + 1))) • circleVec (A.θ (j + 1)) := by
    rw [← hxeq, vtx, vtx, radPt_eq, radPt_eq, smul_smul, smul_smul]
  have hne : (a * rad K (A.θ j)) • circleVec (A.θ j)
      + (b * rad K (A.θ (j + 1))) • circleVec (A.θ (j + 1)) ≠ 0 := by
    rw [← hxcomb]; exact hxne
  obtain ⟨t, htmem, hteq⟩ := exists_angle_mem_Icc_of_nonneg_combination
    (A.strictMono (by omega : j < j + 1)) (by linarith [A.gap_lt j, Real.pi_pos])
    (mul_nonneg ha hr1.le) (mul_nonneg hb hr2.le) hne
  refine ⟨t, htmem.1, htmem.2, ?_⟩
  rw [hxcomb] at *
  exact hteq

/-- A point of the `j`-th edge whose angle is the left endpoint is the left vertex. -/
theorem eq_vtx_left_of_mem_edge (h0 : (0 : Point2) ∈ interior (K : Set Point2))
    {j : ℤ} {x : Point2} (hx : x ∈ edge K A j) (hxt : x = ‖x‖ • circleVec (A.θ j)) :
    x = vtx K A j := by
  have hd := dd_pos h0 (K := K) (A := A) j
  have hr1 : 0 < rad K (A.θ j) := rad_pos h0 _
  have h := inner_nrm_of_mem_edge hx
  rw [hxt, real_inner_smul_left, inner_circleVec_nrm_left h0] at h
  have hnorm : ‖x‖ = rad K (A.θ j) := by
    have h2 : ‖x‖ * dd K A j = rad K (A.θ j) * dd K A j := by
      have h3 := congrArg (fun z : ℝ => z * rad K (A.θ j)) h
      simp only [mul_assoc] at h3
      rw [div_mul_cancel₀ _ hr1.ne'] at h3
      linarith
    exact mul_right_cancel₀ hd.ne' h2
  rw [hxt, hnorm, vtx, radPt_eq]

/-- A point of the `j`-th edge whose angle is the right endpoint is the right vertex. -/
theorem eq_vtx_right_of_mem_edge (h0 : (0 : Point2) ∈ interior (K : Set Point2))
    {j : ℤ} {x : Point2} (hx : x ∈ edge K A j) (hxt : x = ‖x‖ • circleVec (A.θ (j + 1))) :
    x = vtx K A (j + 1) := by
  have hd := dd_pos h0 (K := K) (A := A) j
  have hr2 : 0 < rad K (A.θ (j + 1)) := rad_pos h0 _
  have h := inner_nrm_of_mem_edge hx
  rw [hxt, real_inner_smul_left, inner_circleVec_nrm_right h0] at h
  have hnorm : ‖x‖ = rad K (A.θ (j + 1)) := by
    have h2 : ‖x‖ * dd K A j = rad K (A.θ (j + 1)) * dd K A j := by
      have h3 := congrArg (fun z : ℝ => z * rad K (A.θ (j + 1))) h
      simp only [mul_assoc] at h3
      rw [div_mul_cancel₀ _ hr2.ne'] at h3
      linarith
    exact mul_right_cancel₀ hd.ne' h2
  rw [hxt, hnorm, vtx, radPt_eq]

/-- Distinct edges meet only in vertices. -/
theorem edge_inter_subset_pair (h0 : (0 : Point2) ∈ interior (K : Set Point2))
    {j k : ℤ} (hj0 : 0 ≤ j) (hjm : j < A.m) (hk0 : 0 ≤ k) (hkm : k < A.m) (hjk : j ≠ k) :
    edge K A j ∩ edge K A k ⊆ {vtx K A j, vtx K A (j + 1)} := by
  rintro x ⟨hxj, hxk⟩
  have hxne : x ≠ 0 := ne_zero_of_mem_edge h0 hxj
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hxne
  obtain ⟨t, ht1, ht2, hxt⟩ := exists_angle_of_mem_edge h0 hxj
  obtain ⟨u, hu1, hu2, hxu⟩ := exists_angle_of_mem_edge h0 hxk
  have hcirc : circleVec t = circleVec u := by
    have : ‖x‖ • circleVec t = ‖x‖ • circleVec u := by rw [← hxt, ← hxu]
    exact smul_right_injective _ hxpos.ne' this
  obtain ⟨q, hq⟩ := circleVec_eq_iff_exists hcirc
  have hθm : A.θ (A.m : ℤ) = A.θ 0 + 2 * Real.pi := by
    have := A.period 0
    simpa using this
  have hlow_t : A.θ 0 ≤ t := le_trans (A.strictMono.monotone hj0) ht1
  have hhigh_t : t ≤ A.θ 0 + 2 * Real.pi := by
    rw [← hθm]
    exact le_trans ht2 (A.strictMono.monotone (by omega))
  have hlow_u : A.θ 0 ≤ u := le_trans (A.strictMono.monotone hk0) hu1
  have hhigh_u : u ≤ A.θ 0 + 2 * Real.pi := by
    rw [← hθm]
    exact le_trans hu2 (A.strictMono.monotone (by omega))
  have hpi := Real.pi_pos
  have hqbound : q = 0 ∨ q = 1 ∨ q = -1 := by
    have h1 : (q : ℝ) * (2 * Real.pi) ≤ 2 * Real.pi := by linarith
    have h2 : -(2 * Real.pi) ≤ (q : ℝ) * (2 * Real.pi) := by linarith
    have hq1 : (q : ℝ) ≤ 1 := by nlinarith
    have hq2 : (-1 : ℝ) ≤ (q : ℝ) := by nlinarith
    have : q ≤ 1 := by exact_mod_cast hq1
    have : -1 ≤ q := by exact_mod_cast hq2
    omega
  rcases hqbound with rfl | rfl | rfl
  · -- same angle
    simp only [Int.cast_zero, zero_mul, add_zero] at hq
    rw [hq] at hu1 hu2
    rcases lt_or_gt_of_ne hjk with hlt | hlt
    · have hmono : A.θ (j + 1) ≤ A.θ k := A.strictMono.monotone (by omega)
      have htj : t = A.θ (j + 1) := le_antisymm ht2 (le_trans hmono hu1)
      right
      exact eq_vtx_right_of_mem_edge h0 hxj (by rw [← htj]; exact hxt)
    · have hmono : A.θ (k + 1) ≤ A.θ j := A.strictMono.monotone (by omega)
      have htj : t = A.θ j := le_antisymm (le_trans hu2 hmono) ht1
      left
      exact eq_vtx_left_of_mem_edge h0 hxj (by rw [← htj]; exact hxt)
  · -- `u = t + 2π`
    simp only [Int.cast_one, one_mul] at hq
    have htlow : t = A.θ 0 := le_antisymm (by linarith) hlow_t
    have hjzero : A.θ j = A.θ 0 := le_antisymm (by rw [← htlow]; exact ht1)
      (A.strictMono.monotone hj0)
    left
    exact eq_vtx_left_of_mem_edge h0 hxj (by rw [hjzero, ← htlow]; exact hxt)
  · -- `u = t - 2π`
    simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul] at hq
    have hthigh : t = A.θ 0 + 2 * Real.pi := le_antisymm hhigh_t (by linarith)
    have hjm1 : A.θ (j + 1) = A.θ 0 + 2 * Real.pi := by
      refine le_antisymm ?_ (by rw [← hthigh]; exact ht2)
      rw [← hθm]
      exact A.strictMono.monotone (by omega)
    right
    exact eq_vtx_right_of_mem_edge h0 hxj (by rw [hjm1, ← hthigh]; exact hxt)

end HumanVerification.CauchyCrofton
