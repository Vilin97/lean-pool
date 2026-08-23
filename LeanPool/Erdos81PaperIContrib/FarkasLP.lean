/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import LeanPool.Erdos81PaperIContrib.FgConeClosed

/-!

# Finite Farkas lemma and finite LP strong duality

Built on `fg_cone_isClosed` (Weyl, in `FgConeClosed.lean`) and Mathlib's convex-cone
hyperplane separation:
* `LeanPool.Erdos81PaperIContrib.farkas_ge` — finite Farkas lemma (inequality form).
* `LeanPool.Erdos81PaperIContrib.covering_packing_duality` — finite LP strong duality
  (covering/packing form): the maximum packing value equals the covering optimum and is
  attained.

These stay over `EuclideanSpace ℝ ι` (a finite-dimensional real inner-product space),
the natural setting for the `ProperCone`/inner-dual separation used here.

-/

open scoped BigOperators

namespace LeanPool.Erdos81PaperIContrib

variable {ι κ : Type*}

/-- A real vector viewed in `EuclideanSpace ℝ ι` by its coordinates. -/
noncomputable def toE (f : ι → ℝ) : EuclideanSpace ℝ ι :=
  (WithLp.equiv 2 (ι → ℝ)).symm f

@[simp] lemma toE_apply (f : ι → ℝ) (i : ι) : toE f i = f i := rfl

lemma inner_toE [Fintype ι] (f : ι → ℝ) (y : EuclideanSpace ℝ ι) :
    (inner ℝ (toE f) y) = ∑ i, f i * y i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, toE, mul_comm]

/-- **Finite Farkas lemma (inequality form).** If the primal system `x ≥ 0, N x ≥ c` is
infeasible, then there is a Farkas certificate `y ≥ 0` with `Nᵀ y ≤ 0` and `⟨c, y⟩ > 0`. -/
theorem farkas_ge [Fintype ι] [Fintype κ]
    (N : ι → κ → ℝ) (c : ι → ℝ)
    (hinfeas : ¬ ∃ x : κ → ℝ, (∀ j, 0 ≤ x j) ∧ (∀ i, c i ≤ ∑ j, N i j * x j)) :
    ∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ j, ∑ i, N i j * y i ≤ 0) ∧ 0 < ∑ i, c i * y i := by
  classical
  set g : (κ ⊕ ι) → EuclideanSpace ℝ ι :=
    Sum.elim (fun j => toE (fun i => N i j))
      (fun i => toE (fun i' => if i' = i then (-1 : ℝ) else 0)) with hg
  have hind : ∀ a : κ ⊕ ι, ∑ k, (if k = a then (1:ℝ) else 0) • g k = g a := by
    intro a; simp [ite_smul]
  set S : Set (EuclideanSpace ℝ ι) :=
    {y | ∃ coeff : (κ ⊕ ι) → ℝ, (∀ k, 0 ≤ coeff k) ∧ ∑ k, coeff k • g k = y} with hS
  have hSclosed : IsClosed S := fg_cone_isClosed g
  let K : ConvexCone ℝ (EuclideanSpace ℝ ι) :=
    { carrier := S
      smul_mem' := by
        rintro t ht x ⟨coeff, hcoeff, rfl⟩
        exact ⟨fun k => t * coeff k, fun k => mul_nonneg ht.le (hcoeff k), by
          rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro k _; rw [smul_smul]⟩
      add_mem' := by
        rintro x ⟨c1, h1, rfl⟩ y ⟨c2, h2, rfl⟩
        exact ⟨fun k => c1 k + c2 k, fun k => add_nonneg (h1 k) (h2 k), by
          rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro k _; rw [add_smul]⟩ }
  have hKne : (K : Set (EuclideanSpace ℝ ι)).Nonempty :=
    ⟨0, ⟨fun _ => 0, fun _ => le_refl 0, by simp⟩⟩
  have hcne : (toE c) ∉ K := by
    rintro ⟨coeff, hcoeff, hsum⟩
    apply hinfeas
    refine ⟨fun j => coeff (Sum.inl j), fun j => hcoeff _, ?_⟩
    intro i
    have hcoord := congrArg (fun z => z i) hsum
    simp only [toE_apply] at hcoord
    have hexp : (∑ k, coeff k • g k) i
        = (∑ j, coeff (Sum.inl j) * N i j) - coeff (Sum.inr i) := by
      rw [Fintype.sum_sum_type]
      simp [hg, EuclideanSpace, PiLp, Finset.sum_apply]
      ring
    have hcomm : ∑ j, N i j * coeff (Sum.inl j) = ∑ j, coeff (Sum.inl j) * N i j := by
      apply Finset.sum_congr rfl; intro j _; ring
    rw [hexp] at hcoord
    have hnn : 0 ≤ coeff (Sum.inr i) := hcoeff _
    linarith
  let hKpointed : K.Pointed := ConvexCone.Pointed.of_nonempty_of_isClosed hKne hSclosed
  let Kp : ProperCone ℝ (EuclideanSpace ℝ ι) := ⟨K.toPointedCone hKpointed, hSclosed⟩
  have hKp_mem (x : EuclideanSpace ℝ ι) : x ∈ Kp ↔ x ∈ K := by
    change x ∈ K.toPointedCone hKpointed ↔ x ∈ K
    exact ConvexCone.mem_toPointedCone hKpointed x
  have hcne' : toE c ∉ Kp := fun h => hcne ((hKp_mem _).mp h)
  obtain ⟨y, hy1, hy2⟩ := ProperCone.hyperplane_separation' Kp hcne'
  refine ⟨fun i => -(y i), fun i => ?_, fun j => ?_, ?_⟩
  · have hmem : g (Sum.inr i) ∈ K :=
      ⟨fun k => if k = Sum.inr i then 1 else 0, fun k => by positivity, hind _⟩
    have hh := hy1 _ ((hKp_mem _).mpr hmem)
    rw [hg] at hh; simp only [Sum.elim_inr] at hh
    rw [inner_toE] at hh
    have hval : ∑ i', (if i' = i then (-1:ℝ) else 0) * y i' = - y i := by
      rw [Finset.sum_eq_single i] <;> simp +contextual
    rw [hval] at hh
    change 0 ≤ - y i; linarith
  · have hmem : g (Sum.inl j) ∈ K :=
      ⟨fun k => if k = Sum.inl j then 1 else 0, fun k => by positivity, hind _⟩
    have hh := hy1 _ ((hKp_mem _).mpr hmem)
    rw [hg] at hh; simp only [Sum.elim_inl] at hh
    rw [inner_toE] at hh
    have h2 : ∑ i, N i j * -(y i) = - ∑ i, (fun i => N i j) i * y i := by
      rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; ring
    rw [h2]; linarith
  · rw [inner_toE] at hy2
    have h2 : ∑ i, c i * -(y i) = - ∑ i, c i * y i := by
      rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; ring
    rw [h2]; linarith

/-- **Finite LP strong duality (covering/packing).** For a nonnegative incidence matrix `A`
with nonnegative capacities `r`, in which every column has a positive entry, there is a
maximum packing `w` whose value equals the covering optimum. -/
theorem covering_packing_duality [Fintype ι] [Fintype κ]
    (A : ι → κ → ℝ) (r : ι → ℝ)
    (hA : ∀ e t, 0 ≤ A e t) (hr : ∀ e, 0 ≤ r e)
    (hcol : ∀ t, ∃ e, 0 < A e t) :
    ∃ w : κ → ℝ, (∀ t, 0 ≤ w t) ∧ (∀ e, (∑ t, A e t * w t) ≤ r e) ∧
      (∑ t, w t) = sInf {v : ℝ | ∃ x : ι → ℝ, (∀ e, 0 ≤ x e) ∧
        (∀ t, 1 ≤ ∑ e, A e t * x e) ∧ v = ∑ e, r e * x e} := by
  by_contra h_no_wstar
  have hP_le_Mr : ∀ w : κ → ℝ,
      (∀ t, 0 ≤ w t) ∧ (∀ e, ∑ t, A e t * w t ≤ r e) →
        ∑ t, w t ≤ sInf {v | ∃ x : ι → ℝ, (∀ e, 0 ≤ x e) ∧
          (∀ t, 1 ≤ ∑ e, A e t * x e) ∧ v = ∑ e, r e * x e} := by
    intro w hw
    refine le_csInf ?_ ?_
    · refine ⟨_, ⟨fun e => ∑ t, 1 / A e t, ?_, ?_, rfl⟩⟩
      · exact fun e => Finset.sum_nonneg fun t _ => one_div_nonneg.2 (hA e t)
      · intro t
        obtain ⟨e, he⟩ := hcol t
        refine le_trans ?_ (Finset.single_le_sum (fun e _ => mul_nonneg (hA e t)
          (Finset.sum_nonneg fun t _ => one_div_nonneg.mpr (hA e t))) (Finset.mem_univ e))
        · simp only [one_div]
          rw [Finset.mul_sum]
          exact le_trans (show 1 ≤ A e t * (A e t)⁻¹ by norm_num [he.ne'])
            (Finset.single_le_sum
              (fun i _ => mul_nonneg he.le (inv_nonneg.2 (hA e i))) (Finset.mem_univ t))
    · rintro _ ⟨x, hx₁, hx₂, rfl⟩
      have h_fubini : ∑ t, w t * (∑ e, A e t * x e) =
          ∑ e, (∑ t, A e t * w t) * x e := by
        simpa only [mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul]
          using Finset.sum_comm
      exact le_trans (Finset.sum_le_sum fun t _ => le_mul_of_one_le_right (hw.1 t) (hx₂ t))
        (h_fubini.le.trans (Finset.sum_le_sum fun e _ =>
          mul_le_mul_of_nonneg_right (hw.2 e) (hx₁ e)))
  obtain ⟨w_star, hw_star⟩ : ∃ w_star : κ → ℝ, (∀ t, 0 ≤ w_star t) ∧
      (∀ e, ∑ t, A e t * w_star t ≤ r e) ∧ ∀ w : κ → ℝ,
        (∀ t, 0 ≤ w t) ∧ (∀ e, ∑ t, A e t * w t ≤ r e) →
          ∑ t, w t ≤ ∑ t, w_star t := by
    have h_compact : IsCompact {w : κ → ℝ |
        (∀ t, 0 ≤ w t) ∧ (∀ e, ∑ t, A e t * w t ≤ r e)} := by
      refine (CompactIccSpace.isCompact_Icc : IsCompact (Set.Icc
        (fun _ : κ => (0 : ℝ))
        (fun _ => sInf {v | ∃ x : ι → ℝ, (∀ e, 0 ≤ x e) ∧
          (∀ t, 1 ≤ ∑ e, A e t * x e) ∧ v = ∑ e, r e * x e}))).of_isClosed_subset
          ?_ ?_
      · simp only [Set.ofPred_and, Set.ofPred_forall]
        exact IsClosed.inter
          (isClosed_iInter fun _ => isClosed_le continuous_const <| continuous_apply _)
          (isClosed_iInter fun _ => isClosed_le
            (continuous_finsetSum _ fun _ _ => continuous_const.mul <| continuous_apply _)
            continuous_const)
      · exact fun w hw => ⟨hw.1, fun t => le_trans
          (Finset.single_le_sum (fun a _ => hw.1 a) (Finset.mem_univ t)) (hP_le_Mr w hw)⟩
    have h_nonempty : {w : κ → ℝ | (∀ t, 0 ≤ w t) ∧
        (∀ e, ∑ t, A e t * w t ≤ r e)}.Nonempty := by
      exact ⟨fun _ => 0, fun _ => le_rfl, fun _ => by simp [hr]⟩
    have h_max := h_compact.exists_isMaxOn h_nonempty
      (show ContinuousOn (fun w : κ → ℝ => ∑ t, w t) _ from
        Continuous.continuousOn <| continuous_finsetSum _ fun _ _ => continuous_apply _)
    exact ⟨h_max.choose, h_max.choose_spec.1.1, h_max.choose_spec.1.2,
      fun w hw => h_max.choose_spec.2 hw⟩
  have hP_lt_Mr : ∑ t, w_star t < sInf {v | ∃ x : ι → ℝ, (∀ e, 0 ≤ x e) ∧
      (∀ t, 1 ≤ ∑ e, A e t * x e) ∧ v = ∑ e, r e * x e} := by
    exact lt_of_le_of_ne (hP_le_Mr w_star ⟨hw_star.1, hw_star.2.1⟩) fun h =>
      h_no_wstar ⟨w_star, hw_star.1, hw_star.2.1, h⟩
  obtain ⟨y, hy_nonneg, hy_row, hy_obj⟩ : ∃ y : κ ⊕ Unit → ℝ,
      (∀ i, 0 ≤ y i) ∧
      (∀ e, ∑ i, Sum.elim (fun t e => A e t) (fun _ e => -r e) i e * y i ≤ 0) ∧
      0 < ∑ i, Sum.elim (fun _ => 1) (fun _ => -∑ t, w_star t) i * y i := by
    have h_farkas : ¬∃ x : ι → ℝ, (∀ e, 0 ≤ x e) ∧
        (∀ t, 1 ≤ ∑ e, A e t * x e) ∧ ∑ e, r e * x e ≤ ∑ t, w_star t := by
      contrapose! hP_lt_Mr
      exact le_trans (csInf_le ⟨0, by
        rintro v ⟨x, hx₁, hx₂, rfl⟩
        exact Finset.sum_nonneg fun _ _ => mul_nonneg (hr _) (hx₁ _)⟩
        ⟨hP_lt_Mr.choose, hP_lt_Mr.choose_spec.1, hP_lt_Mr.choose_spec.2.1, rfl⟩)
        hP_lt_Mr.choose_spec.2.2
    convert farkas_ge
      (fun i e => Sum.elim (fun t e => A e t) (fun _ e => -r e) i e)
      (fun i => Sum.elim (fun _ => 1) (fun _ => -∑ t, w_star t) i) _ using 1
    simp +zetaDelta only [Sum.forall, Sum.elim_inl, Sum.elim_inr, neg_mul,
      Finset.sum_neg_distrib, neg_le_neg_iff, forall_const, not_exists, not_and, not_le] at *
    exact h_farkas
  set lam : κ → ℝ := fun t => y (Sum.inl t)
  set mu : ℝ := y (Sum.inr ())
  have hlam_mu : ∀ e, ∑ t, A e t * lam t ≤ mu * r e := by
    intro e
    specialize hy_row e
    simpa [lam, mu, mul_comm] using hy_row
  have hlam_mu_P : ∑ t, lam t > mu * ∑ t, w_star t := by
    simp +zetaDelta at *
    linarith
  by_cases hmu_zero : mu = 0
  · simp +zetaDelta only [not_exists, not_and, and_imp, Sum.forall,
      Fintype.sum_sum_type, Sum.elim_inl, Finset.univ_unique, PUnit.default_eq_unit,
      Sum.elim_inr, neg_mul, Finset.sum_neg_distrib, Finset.sum_singleton,
      add_neg_le_iff_le_add, zero_add, one_mul, lt_add_neg_iff_add_lt, gt_iff_lt] at *
    simp_all only [Std.le_refl, implies_true, and_true, mul_zero, zero_mul]
    exact hy_obj.ne' (Finset.sum_eq_zero fun t ht => le_antisymm
      (le_of_not_gt fun h => by
        have hrow := hy_row (Classical.choose (hcol t))
        exact not_le_of_gt (lt_of_lt_of_le
          (mul_pos (Classical.choose_spec (hcol t)) h)
          (Finset.single_le_sum (fun a _ => mul_nonneg (hA _ a) (hy_nonneg a)) ht)) hrow)
      (hy_nonneg t))
  · have hlam_mu_div : ∀ e, ∑ t, A e t * (lam t / mu) ≤ r e := by
      simp only [← mul_div_assoc, ← Finset.sum_div]
      exact fun e => div_le_iff₀' (lt_of_le_of_ne (hy_nonneg _) (Ne.symm hmu_zero)) |>.2
        (hlam_mu e)
    have hlam_mu_div_P : ∑ t, (lam t / mu) > ∑ t, w_star t := by
      rw [← Finset.sum_div _ _ _, gt_iff_lt, lt_div_iff₀] <;>
        cases lt_or_gt_of_ne hmu_zero <;> nlinarith [hy_nonneg (Sum.inr ())]
    exact not_le_of_gt hlam_mu_div_P
      (hw_star.2.2 _ ⟨fun t => div_nonneg (hy_nonneg _) (hy_nonneg _), hlam_mu_div⟩)

end LeanPool.Erdos81PaperIContrib
