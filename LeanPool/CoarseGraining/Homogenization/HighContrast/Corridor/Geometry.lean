/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Probability.LocalObservable

/-!
# Corridor geometry

Formalization of the corridor geometry underlying Lemma 4.2
(`l.corridor.geometry`) of the high-moment paper (Armstrong–Kuusi–Loher, in
preparation).

Fix a mesh size `ℓ` and a phase `σ : Vec d`.  The *corridor set*
`corridorSet ℓ σ` is the union over coordinates `i` of the width-`2` slabs
around the shifted lattice `σ i + ℓ • ℤ`.  Its complement is the disjoint
union of the *core boxes* `coreBox ℓ σ k`, `k : Fin d → ℤ`.  This file
records:

* `corridorSet`, `coreBox`;
* the exhaustion `(corridorSet ℓ σ)ᶜ = ⋃ k, coreBox ℓ σ k`;
* the sup-metric `2`-separation of distinct core boxes, packaged as
  `AreUnitSeparated`;
* finiteness of the cores meeting a bounded set;
* the corridor-modified coefficient field `corridorField` and its algebra;
* the independence bridge to the unit-range dependence machinery.
-/

@[expose] public section

open Homogenization
open scoped MeasureTheory

namespace Homogenization

variable {d : ℕ}

/-! ## J1–J2: the corridor set and the core boxes -/

/-- The corridor set `S_σ` of `e.corridor.definition`: the points that are
within (sup-)distance `1` of the shifted lattice `σ i + ℓ • ℤ` in some
coordinate `i`. -/
def corridorSet (ℓ : ℝ) (σ : Vec d) : Set (Vec d) :=
  {x | ∃ i : Fin d, ∃ n : ℤ, |x i - σ i - n * ℓ| < 1}

/-- The core box indexed by `k : Fin d → ℤ`: the product of the intervals
`I_{i,k_i} = [σ_i + k_i ℓ + 1, σ_i + (k_i+1) ℓ − 1]`. -/
def coreBox (ℓ : ℝ) (σ : Vec d) (k : Fin d → ℤ) : Set (Vec d) :=
  Set.pi Set.univ
    (fun i => Set.Icc (σ i + k i * ℓ + 1) (σ i + (k i + 1) * ℓ - 1))

theorem mem_corridorSet {ℓ : ℝ} {σ x : Vec d} :
    x ∈ corridorSet ℓ σ ↔ ∃ i : Fin d, ∃ n : ℤ, |x i - σ i - n * ℓ| < 1 :=
  Iff.rfl

theorem mem_coreBox {ℓ : ℝ} {σ x : Vec d} {k : Fin d → ℤ} :
    x ∈ coreBox ℓ σ k ↔
      ∀ i : Fin d, σ i + k i * ℓ + 1 ≤ x i ∧ x i ≤ σ i + (k i + 1) * ℓ - 1 := by
  simp only [coreBox, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Icc]

/-! ## J3: exhaustion of the complement by core boxes -/

/-- One-dimensional heart of the exhaustion: a real number `t` is at
(sup-)distance `≥ 1` from every point of `ℓ • ℤ` iff it lies in one of the
core intervals `[m ℓ + 1, (m+1) ℓ − 1]`.  Needs only `0 < ℓ`. -/
theorem forall_one_le_abs_iff {ℓ : ℝ} (hℓ : 0 < ℓ) (t : ℝ) :
    (∀ n : ℤ, 1 ≤ |t - n * ℓ|) ↔
      ∃ m : ℤ, m * ℓ + 1 ≤ t ∧ t ≤ (m + 1) * ℓ - 1 := by
  constructor
  · intro h
    refine ⟨⌊t / ℓ⌋, ?_, ?_⟩
    · have hle : (⌊t / ℓ⌋ : ℝ) * ℓ ≤ t := (le_div_iff₀ hℓ).1 (Int.floor_le _)
      have hnn : 0 ≤ t - (⌊t / ℓ⌋ : ℝ) * ℓ := by linarith
      have := h ⌊t / ℓ⌋
      rw [abs_of_nonneg hnn] at this
      linarith
    · have hlt : t < ((⌊t / ℓ⌋ : ℝ) + 1) * ℓ := by
        have := Int.lt_floor_add_one (t / ℓ)
        rw [div_lt_iff₀ hℓ] at this
        linarith [this]
      have hnp : t - ((⌊t / ℓ⌋ : ℝ) + 1) * ℓ ≤ 0 := by nlinarith
      have hkey := h (⌊t / ℓ⌋ + 1)
      have hcast : ((⌊t / ℓ⌋ + 1 : ℤ) : ℝ) = (⌊t / ℓ⌋ : ℝ) + 1 := by push_cast; ring
      rw [hcast, abs_of_nonpos hnp] at hkey
      linarith
  · rintro ⟨m, hlo, hhi⟩ n
    rcases le_or_gt n m with hnm | hmn
    · have hcast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      have hmul : (n : ℝ) * ℓ ≤ (m : ℝ) * ℓ :=
        mul_le_mul_of_nonneg_right hcast hℓ.le
      have : (1 : ℝ) ≤ t - n * ℓ := by linarith
      calc (1 : ℝ) ≤ t - n * ℓ := this
        _ ≤ |t - n * ℓ| := le_abs_self _
    · have hcast : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hmn
      have hmul : ((m : ℝ) + 1) * ℓ ≤ (n : ℝ) * ℓ :=
        mul_le_mul_of_nonneg_right hcast hℓ.le
      have : (1 : ℝ) ≤ n * ℓ - t := by nlinarith
      calc (1 : ℝ) ≤ -(t - n * ℓ) := by linarith
        _ ≤ |t - n * ℓ| := neg_le_abs _

/-- Exhaustion (J3): the complement of the corridor set is the union of the
core boxes.  Needs only `0 < ℓ`. -/
theorem compl_corridorSet_eq_iUnion_coreBox {ℓ : ℝ} (hℓ : 0 < ℓ) (σ : Vec d) :
    (corridorSet ℓ σ)ᶜ = ⋃ k : Fin d → ℤ, coreBox ℓ σ k := by
  ext x
  simp only [Set.mem_compl_iff, mem_corridorSet, Set.mem_iUnion, mem_coreBox]
  push Not
  have key : ∀ i : Fin d,
      (∀ n : ℤ, 1 ≤ |x i - σ i - n * ℓ|) ↔
        ∃ m : ℤ, σ i + m * ℓ + 1 ≤ x i ∧ x i ≤ σ i + (m + 1) * ℓ - 1 := by
    intro i
    have h := forall_one_le_abs_iff hℓ (x i - σ i)
    simp only [sub_sub] at h ⊢
    rw [h]
    constructor
    · rintro ⟨m, h1, h2⟩; exact ⟨m, by linarith, by linarith⟩
    · rintro ⟨m, h1, h2⟩; exact ⟨m, by linarith, by linarith⟩
  calc (∀ i : Fin d, ∀ n : ℤ, 1 ≤ |x i - σ i - n * ℓ|)
      ↔ ∀ i : Fin d, ∃ m : ℤ, σ i + m * ℓ + 1 ≤ x i ∧ x i ≤ σ i + (m + 1) * ℓ - 1 :=
        forall_congr' key
    _ ↔ ∃ k : Fin d → ℤ, ∀ i : Fin d,
          σ i + k i * ℓ + 1 ≤ x i ∧ x i ≤ σ i + (k i + 1) * ℓ - 1 :=
        Classical.skolem

/-! ## J4: sup-metric separation of distinct core boxes -/

/-- Two distinct core boxes are separated by a gap of at least `2` in some
coordinate, hence (in the sup metric on `Vec d`) by `AreUnitSeparated`.
Needs `0 ≤ ℓ`. -/
theorem areUnitSeparated_coreBox {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (σ : Vec d)
    {k k' : Fin d → ℤ} (hne : k ≠ k') :
    AreUnitSeparated (coreBox ℓ σ k) (coreBox ℓ σ k') := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  intro x y hx hy
  rw [mem_coreBox] at hx hy
  obtain ⟨hx1, hx2⟩ := hx i
  obtain ⟨hy1, hy2⟩ := hy i
  have hgap : 2 ≤ |x i - y i| := by
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · -- k i < k' i : the `k'`-box lies to the right of the `k`-box
      have hc : (k i : ℝ) + 1 ≤ (k' i : ℝ) := by exact_mod_cast hlt
      have hmul : ((k i : ℝ) + 1) * ℓ ≤ (k' i : ℝ) * ℓ :=
        mul_le_mul_of_nonneg_right hc hℓ
      have : x i - y i ≤ -2 := by nlinarith
      rw [abs_of_nonpos (by linarith)]; linarith
    · -- k' i < k i : the `k`-box lies to the right of the `k'`-box
      have hc : (k' i : ℝ) + 1 ≤ (k i : ℝ) := by exact_mod_cast hgt
      have hmul : ((k' i : ℝ) + 1) * ℓ ≤ (k i : ℝ) * ℓ :=
        mul_le_mul_of_nonneg_right hc hℓ
      have : (2 : ℝ) ≤ x i - y i := by nlinarith
      rw [abs_of_nonneg (by linarith)]; linarith
  have hxi : |x i - y i| ≤ dist x y := by
    have := dist_le_pi_dist x y i
    rwa [Real.dist_eq] at this
  linarith

/-! ## J5: finiteness of the cores meeting a bounded set -/

/-- Finiteness (J5): only finitely many core boxes meet a bounded set `U`.
Provided as `Set.Finite`; consumers can take `.toFinset`.  Needs `0 < ℓ`. -/
theorem finite_coreBox_meets {ℓ : ℝ} (hℓ : 0 < ℓ) (σ : Vec d) {U : Set (Vec d)}
    (hU : Bornology.IsBounded U) :
    {k : Fin d → ℤ | (coreBox ℓ σ k ∩ U).Nonempty}.Finite := by
  obtain ⟨R, hR⟩ := hU.subset_closedBall 0
  -- per-coordinate integer bounds for the admissible indices
  set B : Fin d → ℤ := fun i => ⌊(R - σ i - 1) / ℓ⌋ with hB
  set A : Fin d → ℤ := fun i => ⌈(-R - σ i + 1) / ℓ - 1⌉ with hA
  apply Set.Finite.subset
    (Set.Finite.pi (fun i => Set.finite_Icc (A i) (B i)))
  rintro k ⟨z, hz_core, hz_U⟩ i -
  rw [mem_coreBox] at hz_core
  obtain ⟨hlo, hhi⟩ := hz_core i
  -- `|z i| ≤ R` from `z ∈ closedBall 0 R`
  have hzR : |z i| ≤ R := by
    have hdist : dist z 0 ≤ R := by
      have := hR hz_U
      rwa [Metric.mem_closedBall] at this
    have := dist_le_pi_dist z 0 i
    rw [Real.dist_eq] at this
    simp only [Pi.zero_apply, sub_zero] at this
    linarith
  have hziR : z i ≤ R := (abs_le.1 hzR).2
  have hzRi : -R ≤ z i := (abs_le.1 hzR).1
  refine Set.mem_Icc.2 ⟨?_, ?_⟩
  · -- lower bound `A i ≤ k i`
    rw [hA, Int.ceil_le]
    have hstep : -R - σ i + 1 ≤ (k i + 1) * ℓ := by nlinarith
    have : (-R - σ i + 1) / ℓ ≤ (k i : ℝ) + 1 := by
      rw [div_le_iff₀ hℓ]; linarith
    linarith
  · -- upper bound `k i ≤ B i`
    rw [hB, Int.le_floor]
    have hstep : (k i : ℝ) * ℓ ≤ R - σ i - 1 := by nlinarith
    rw [le_div_iff₀ hℓ]; linarith

/-! ## J7: the corridor-modified coefficient field -/

variable {Θ : ℝ}

/-- The identity matrix is `(1, Θ)`-elliptic for every `Θ ≥ 1`. -/
theorem isEllipticMatrix_one (hΘ : 1 ≤ Θ) :
    IsEllipticMatrix (d := d) 1 Θ (1 : Mat d) := by
  have hmv : ∀ ξ : Vec d, matVecMul (1 : Mat d) ξ = ξ := by
    intro ξ; funext i
    simp only [matVecMul, Matrix.one_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; rw [if_neg (Ne.symm hji), zero_mul]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  refine ⟨one_pos, hΘ, ?_, ?_⟩
  · intro ξ
    rw [hmv]; simp [vecNormSq]
  · intro ξ
    rw [inv_one, hmv]
    have hnn : 0 ≤ vecNormSq ξ := vecNormSq_nonneg ξ
    have hΘinv : Θ⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]; right; exact hΘ
    calc Θ⁻¹ * vecNormSq ξ ≤ 1 * vecNormSq ξ :=
          mul_le_mul_of_nonneg_right hΘinv hnn
      _ = vecDot ξ ξ := by simp [vecNormSq]

/-- The corridor-modified coefficient (`e.corridor.coefficient`): the identity
on the corridor set, and `a` off it. -/
noncomputable def corridorField (ℓ : ℝ) (σ : Vec d) (a : CoeffField d) :
    CoeffField d := by
  classical
  exact fun x => if x ∈ corridorSet ℓ σ then (1 : Mat d) else a x

@[simp] theorem corridorField_apply_of_mem {ℓ : ℝ} {σ : Vec d} {a : CoeffField d}
    {x : Vec d} (hx : x ∈ corridorSet ℓ σ) :
    corridorField ℓ σ a x = (1 : Mat d) := by
  simp [corridorField, hx]

@[simp] theorem corridorField_apply_of_not_mem {ℓ : ℝ} {σ : Vec d}
    {a : CoeffField d} {x : Vec d} (hx : x ∉ corridorSet ℓ σ) :
    corridorField ℓ σ a x = a x := by
  simp [corridorField, hx]

/-- (J7.iii) Off the corridor set, `corridorField ℓ σ a` agrees with `a`. -/
theorem corridorField_eqOn_compl (ℓ : ℝ) (σ : Vec d) (a : CoeffField d) :
    Set.EqOn (corridorField ℓ σ a) a (corridorSet ℓ σ)ᶜ :=
  fun _ hx => corridorField_apply_of_not_mem hx

/-- (J7.i) Pointwise preservation of the ellipticity class: wherever `a x` is
`(1, Θ)`-elliptic (and `Θ ≥ 1`), so is `corridorField ℓ σ a x`. -/
theorem corridorField_isEllipticMatrix {ℓ : ℝ} {σ : Vec d} {a : CoeffField d}
    {x : Vec d} (hΘ : 1 ≤ Θ) (hx : IsEllipticMatrix 1 Θ (a x)) :
    IsEllipticMatrix 1 Θ (corridorField ℓ σ a x) := by
  by_cases hmem : x ∈ corridorSet ℓ σ
  · rw [corridorField_apply_of_mem hmem]; exact isEllipticMatrix_one hΘ
  · rw [corridorField_apply_of_not_mem hmem]; exact hx

/-- (J7.ii) Additive/indicator normal form, convenient for later joint
measurability arguments:
`a_σ = a + 𝟙_{S_σ} · (Id − a)`. -/
theorem corridorField_eq_add_indicator (ℓ : ℝ) (σ : Vec d) (a : CoeffField d) :
    corridorField ℓ σ a =
      fun x => a x + (corridorSet ℓ σ).indicator (fun y => (1 : Mat d) - a y) x := by
  funext x
  by_cases hmem : x ∈ corridorSet ℓ σ
  · rw [corridorField_apply_of_mem hmem, Set.indicator_of_mem hmem]; abel
  · rw [corridorField_apply_of_not_mem hmem, Set.indicator_of_notMem hmem, add_zero]

/-- (J7, restriction compatibility) `corridorField ℓ σ a` depends on `a` only
through its values off the corridor set. -/
theorem corridorField_congr_of_eqOn_compl {ℓ : ℝ} {σ : Vec d} {a a' : CoeffField d}
    (h : Set.EqOn a a' (corridorSet ℓ σ)ᶜ) :
    corridorField ℓ σ a = corridorField ℓ σ a' := by
  funext x
  by_cases hmem : x ∈ corridorSet ℓ σ
  · rw [corridorField_apply_of_mem hmem, corridorField_apply_of_mem hmem]
  · rw [corridorField_apply_of_not_mem hmem, corridorField_apply_of_not_mem hmem]
    exact h hmem

/-! ## J8: independence bridge to unit-range dependence -/

/-- (J8, geometric input) The core boxes of an injective family of indices are
pairwise `AreUnitSeparated`.  Needs `0 ≤ ℓ`. -/
theorem pairwise_areUnitSeparated_coreBox {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (σ : Vec d)
    {ι : Type*} {k : ι → (Fin d → ℤ)} (hk : Function.Injective k) :
    Pairwise fun i j => AreUnitSeparated (coreBox ℓ σ (k i)) (coreBox ℓ σ (k j)) :=
  fun _ _ hij => areUnitSeparated_coreBox hℓ σ (fun h => hij (hk h))

/-- For an injective family of core indices, any measurable local observables
supported on the corresponding cores are jointly independent under a
unit-range-dependent (in the restriction sense) probability measure.  This is
the shape consumed by the Efron–Stein step: combine
`pairwise_areUnitSeparated_coreBox` with the unit-range dependence machinery. -/
theorem iIndepFun_coreBox_observable {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (σ : Vec d)
    {ι : Type*} [DecidableEq ι] {γ : ι → Type*} [∀ i, MeasurableSpace (γ i)]
    {k : ι → (Fin d → ℤ)} (hk : Function.Injective k)
    {P : MeasureTheory.Measure (CoeffField d)} [MeasureTheory.IsProbabilityMeasure P]
    (hP : IsRestrictionUnitRangeDependent P)
    (X : ∀ i, MeasurableRestrictionLocalObservable d (coreBox ℓ σ (k i)) (γ i)) :
    ProbabilityTheory.iIndepFun (fun i => X i) P :=
  MeasurableRestrictionLocalObservable.iIndepFun_of_isRestrictionUnitRangeDependent hP
    (pairwise_areUnitSeparated_coreBox hℓ σ hk) X

end Homogenization
