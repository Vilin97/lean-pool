/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Truncation
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Nonpositive
public import Mathlib.Algebra.Order.Module.Archimedean

/-!
# Truncation by an Archimedean class

For a finite Archimedean class `c`, LM24, Definition 8.1.1 retains either the closed ball at `c`
or its open ball. On series supported at nonpositive exponents these coefficient restrictions are
ring homomorphisms: if `i, j ≤ 0`, then `i + j` lies in either ball exactly when both `i` and `j`
do. The reverse implication uses the convexity encoded by the Archimedean-class order and fails
for unrestricted Hahn series because opposite exponents can cancel.

These are LM24's `T_σ` and `τ_σ`, with Mathlib's reversed ordering of Archimedean classes.
-/

public noncomputable section

namespace HahnSeries.Nonpositive

open FiniteArchimedeanClass

variable {K G R : Type*}
variable [Ring K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Module K G] [IsOrderedModule K G]

section Ring

variable [Ring R]

private theorem add_ne_zero_of_nonpos {i j : G} (hi : i ≤ 0) (hj : j ≤ 0)
    (hij : i ≠ 0 ∨ j ≠ 0) : i + j ≠ 0 := by
  intro hzero
  have hi0 : i = 0 := le_antisymm hi (by
    have heq : i = -j := eq_neg_of_add_eq_zero_left hzero
    rw [heq]
    exact neg_nonneg.mpr hj)
  have hj0 : j = 0 := le_antisymm hj (by
    have heq : j = -i := eq_neg_of_add_eq_zero_right hzero
    rw [heq]
    exact neg_nonneg.mpr hi)
  exact hij.elim (fun h ↦ h hi0) (fun h ↦ h hj0)

private theorem mk_add_le_left {i j : G} (hi : i ≤ 0) (hj : j ≤ 0) :
    ArchimedeanClass.mk (i + j) ≤ ArchimedeanClass.mk i := by
  have hsum : i + j ≤ i := by
    have := add_le_add_left hj i
    simpa using this
  simpa using ArchimedeanClass.min_le_mk_of_le_of_le hsum hi

private theorem mk_add_le_right {i j : G} (hi : i ≤ 0) (hj : j ≤ 0) :
    ArchimedeanClass.mk (i + j) ≤ ArchimedeanClass.mk j := by
  rw [add_comm]
  exact mk_add_le_left hj hi

private theorem mem_closedBall_add_iff (c : FiniteArchimedeanClass G)
    {i j : G} (hi : i ≤ 0) (hj : j ≤ 0) :
    i + j ∈ closedBall K c ↔ i ∈ closedBall K c ∧ j ∈ closedBall K c := by
  constructor
  · intro hij
    constructor
    · exact (FiniteArchimedeanClass.mem_closedBall_iff K).mpr fun hi0 ↦
        ((FiniteArchimedeanClass.mem_closedBall_iff K).mp hij
          (add_ne_zero_of_nonpos hi hj (Or.inl hi0))).trans (mk_add_le_left hi hj)
    · exact (FiniteArchimedeanClass.mem_closedBall_iff K).mpr fun hj0 ↦
        ((FiniteArchimedeanClass.mem_closedBall_iff K).mp hij
          (add_ne_zero_of_nonpos hi hj (Or.inr hj0))).trans (mk_add_le_right hi hj)
  · exact fun h ↦ add_mem h.1 h.2

private theorem mem_ball_add_iff (c : FiniteArchimedeanClass G)
    {i j : G} (hi : i ≤ 0) (hj : j ≤ 0) :
    i + j ∈ ball K c ↔ i ∈ ball K c ∧ j ∈ ball K c := by
  constructor
  · intro hij
    constructor
    · exact (FiniteArchimedeanClass.mem_ball_iff K).mpr fun hi0 ↦
        ((FiniteArchimedeanClass.mem_ball_iff K).mp hij
          (add_ne_zero_of_nonpos hi hj (Or.inl hi0))).trans_le (mk_add_le_left hi hj)
    · exact (FiniteArchimedeanClass.mem_ball_iff K).mpr fun hj0 ↦
        ((FiniteArchimedeanClass.mem_ball_iff K).mp hij
          (add_ne_zero_of_nonpos hi hj (Or.inr hj0))).trans_le (mk_add_le_right hi hj)
  · exact fun h ↦ add_mem h.1 h.2

private theorem filter_mul (p : G → Prop) [DecidablePred p]
    (hpadd : ∀ {i j : G}, i ≤ 0 → j ≤ 0 → (p (i + j) ↔ p i ∧ p j))
    (x y : Nonpositive G R) :
    HahnSeries.filter p ((x * y : Nonpositive G R) : R⟦G⟧) =
      HahnSeries.filter p (x : R⟦G⟧) * HahnSeries.filter p (y : R⟦G⟧) := by
  change HahnSeries.filter p ((x : R⟦G⟧) * (y : R⟦G⟧)) = _
  ext g
  rw [HahnSeries.coeff_filter, HahnSeries.coeff_mul, HahnSeries.coeff_mul]
  by_cases hg : p g
  · rw [ite_eq_left hg]
    apply Finset.sum_congr
    · ext ij
      simp only [Finset.mem_antidiagonal, HahnSeries.support_filter]
      constructor
      · rintro ⟨hi, hj, hij⟩
        have hp := (hpadd (support_subset x hi) (support_subset y hj)).mp (hij ▸ hg)
        exact ⟨⟨hi, hp.1⟩, ⟨hj, hp.2⟩, hij⟩
      · rintro ⟨⟨hi, _⟩, ⟨hj, _⟩, hij⟩
        exact ⟨hi, hj, hij⟩
    · intro ij hij
      rw [HahnSeries.coeff_filter, HahnSeries.coeff_filter]
      rw [Finset.mem_antidiagonal] at hij
      rw [HahnSeries.support_filter, HahnSeries.support_filter] at hij
      simp [hij.1.2, hij.2.1.2]
  · rw [ite_eq_right hg]
    apply (Finset.sum_eq_zero fun ij hij ↦ ?_).symm
    rw [Finset.mem_antidiagonal] at hij
    rw [HahnSeries.support_filter] at hij
    rw [HahnSeries.support_filter] at hij
    have hpij := (hpadd (support_subset x hij.1.1) (support_subset y hij.2.1.1)).mpr
      ⟨hij.1.2, hij.2.1.2⟩
    rw [hij.2.2] at hpij
    exact (hg hpij).elim

private def classTruncation (p : G → Prop) [DecidablePred p]
    (hp0 : p 0) (hpadd : ∀ {i j : G}, i ≤ 0 → j ≤ 0 → (p (i + j) ↔ p i ∧ p j)) :
    Nonpositive G R →+* Nonpositive G R where
  toFun x := ⟨HahnSeries.filter p (x : R⟦G⟧),
    (HahnSeries.support_filter_subset p (x : R⟦G⟧)).trans (support_subset x)⟩
  map_zero' := by ext; simp
  map_one' := by ext g; by_cases hg : g = 0 <;> simp [hg, hp0]
  map_add' x y := by
    apply Subtype.ext
    exact HahnSeries.filter_add p (x : R⟦G⟧) (y : R⟦G⟧)
  map_mul' x y := by
    apply Subtype.ext
    exact filter_mul p hpadd x y

/-- LM24's `T_σ`: retain coefficients whose exponents lie in the closed ball at `c`. -/
def T (c : FiniteArchimedeanClass G) : Nonpositive G R →+* Nonpositive G R :=
  by
    classical
    exact classTruncation (fun g ↦ g ∈ closedBall K c) (zero_mem _)
      (fun hi hj ↦ mem_closedBall_add_iff c hi hj)

/-- LM24's `τ_σ`: retain coefficients whose exponents lie in the open ball at `c`. -/
def tau (c : FiniteArchimedeanClass G) : Nonpositive G R →+* Nonpositive G R :=
  by
    classical
    exact classTruncation (fun g ↦ g ∈ ball K c) (zero_mem _)
      (fun hi hj ↦ mem_ball_add_iff c hi hj)

/-- The finite Archimedean class of the lowest exponent of a series whose lowest exponent is
nonzero. Constant series require the separate zero Archimedean class. -/
def leadingClass (x : Nonpositive G R) (horder : (x : R⟦G⟧).order ≠ 0) :
    FiniteArchimedeanClass G :=
  FiniteArchimedeanClass.mk (x : R⟦G⟧).order horder

/-- The underlying Archimedean class of `leadingClass`. -/
@[simp]
theorem leadingClass_val (x : Nonpositive G R) (horder : (x : R⟦G⟧).order ≠ 0) :
    (leadingClass x horder).val = ArchimedeanClass.mk (x : R⟦G⟧).order :=
  (rfl)

theorem coeff_T_of_mem (c : FiniteArchimedeanClass G) (x : Nonpositive G R) {g : G}
    (hg : g ∈ closedBall K c) :
    ((T (K := K) c x : Nonpositive G R) : R⟦G⟧).coeff g = (x : R⟦G⟧).coeff g := by
  classical
  change (HahnSeries.filter (fun g ↦ g ∈ closedBall K c) (x : R⟦G⟧)).coeff g = _
  rw [HahnSeries.coeff_filter, ite_eq_left hg]

theorem coeff_T_of_not_mem (c : FiniteArchimedeanClass G) (x : Nonpositive G R) {g : G}
    (hg : g ∉ closedBall K c) :
    ((T (K := K) c x : Nonpositive G R) : R⟦G⟧).coeff g = 0 := by
  classical
  change (HahnSeries.filter (fun g ↦ g ∈ closedBall K c) (x : R⟦G⟧)).coeff g = 0
  rw [HahnSeries.coeff_filter, ite_eq_right hg]

/-- Closed-class truncation cannot introduce a new support exponent. -/
theorem support_T_subset (c : FiniteArchimedeanClass G) (x : Nonpositive G R) :
    ((T (K := K) c x : Nonpositive G R) : R⟦G⟧).support ⊆ (x : R⟦G⟧).support := by
  classical
  change (HahnSeries.filter (fun g ↦ g ∈ closedBall K c) (x : R⟦G⟧)).support ⊆ _
  exact HahnSeries.support_filter_subset _ _

theorem coeff_tau_of_mem (c : FiniteArchimedeanClass G) (x : Nonpositive G R) {g : G}
    (hg : g ∈ ball K c) :
    ((tau (K := K) c x : Nonpositive G R) : R⟦G⟧).coeff g = (x : R⟦G⟧).coeff g := by
  classical
  change (HahnSeries.filter (fun g ↦ g ∈ ball K c) (x : R⟦G⟧)).coeff g = _
  rw [HahnSeries.coeff_filter, ite_eq_left hg]

theorem coeff_tau_of_not_mem (c : FiniteArchimedeanClass G) (x : Nonpositive G R) {g : G}
    (hg : g ∉ ball K c) :
    ((tau (K := K) c x : Nonpositive G R) : R⟦G⟧).coeff g = 0 := by
  classical
  change (HahnSeries.filter (fun g ↦ g ∈ ball K c) (x : R⟦G⟧)).coeff g = 0
  rw [HahnSeries.coeff_filter, ite_eq_right hg]

/-- Closed truncation at the class of the lowest nonzero exponent retains the whole series. -/
theorem T_leadingClass (x : Nonpositive G R) (horder : (x : R⟦G⟧).order ≠ 0) :
    T (K := K) (leadingClass x horder) x = x := by
  apply Subtype.ext
  ext g
  by_cases hcoeff : (x : R⟦G⟧).coeff g = 0
  · by_cases hg : g ∈ closedBall K (leadingClass x horder)
    · rw [coeff_T_of_mem _ x hg, hcoeff]
    · rw [coeff_T_of_not_mem _ x hg, hcoeff]
  · rw [coeff_T_of_mem]
    apply (FiniteArchimedeanClass.mem_closedBall_iff K).mpr
    intro hg
    apply (FiniteArchimedeanClass.mk_le_mk horder hg).mpr
    have horderLe : (x : R⟦G⟧).order ≤ g :=
      HahnSeries.order_le_of_coeff_ne_zero hcoeff
    have hgNonpos : g ≤ 0 := support_subset x ((HahnSeries.mem_support _ _).mpr hcoeff)
    simpa using ArchimedeanClass.min_le_mk_of_le_of_le horderLe hgNonpos

/-- Closed-class truncation is idempotent. -/
@[simp]
theorem T_T (c : FiniteArchimedeanClass G) (x : Nonpositive G R) :
    T (K := K) c (T (K := K) c x) = T (K := K) c x := by
  apply Subtype.ext
  ext g
  by_cases hg : g ∈ closedBall K c
  · rw [coeff_T_of_mem c (T (K := K) c x) hg]
  · rw [coeff_T_of_not_mem c (T (K := K) c x) hg,
      coeff_T_of_not_mem c x hg]

/-- Open-class truncation is idempotent. -/
@[simp]
theorem tau_tau (c : FiniteArchimedeanClass G) (x : Nonpositive G R) :
    tau (K := K) c (tau (K := K) c x) = tau (K := K) c x := by
  apply Subtype.ext
  ext g
  by_cases hg : g ∈ ball K c
  · rw [coeff_tau_of_mem c (tau (K := K) c x) hg]
  · rw [coeff_tau_of_not_mem c (tau (K := K) c x) hg,
      coeff_tau_of_not_mem c x hg]

/-- Applying the closed cut after the open cut leaves the open cut. -/
@[simp]
theorem T_tau (c : FiniteArchimedeanClass G) (x : Nonpositive G R) :
    T (K := K) c (tau (K := K) c x) = tau (K := K) c x := by
  apply Subtype.ext
  ext g
  by_cases hg : g ∈ closedBall K c
  · rw [coeff_T_of_mem c (tau (K := K) c x) hg]
  · have hball : g ∉ ball K c := fun h ↦
      hg ((FiniteArchimedeanClass.ball_lt_closedBall (K := K)).le h)
    rw [coeff_T_of_not_mem c (tau (K := K) c x) hg,
      coeff_tau_of_not_mem c x hball]

/-- Applying the open cut after the closed cut leaves the open cut. -/
@[simp]
theorem tau_T (c : FiniteArchimedeanClass G) (x : Nonpositive G R) :
    tau (K := K) c (T (K := K) c x) = tau (K := K) c x := by
  apply Subtype.ext
  ext g
  by_cases hg : g ∈ ball K c
  · rw [coeff_tau_of_mem c (T (K := K) c x) hg,
      coeff_T_of_mem c x ((FiniteArchimedeanClass.ball_lt_closedBall (K := K)).le hg),
      coeff_tau_of_mem c x hg]
  · rw [coeff_tau_of_not_mem c (T (K := K) c x) hg,
      coeff_tau_of_not_mem c x hg]

end Ring

end HahnSeries.Nonpositive
