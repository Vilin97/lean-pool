/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothCutoffs
public import LeanPool.NavierStokesAndEuler.NavierStokes.PowerMomentMatrix
import LeanPool.NavierStokesAndEuler.NavierStokes.MomentRepair
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Constructed smooth moment repairs

The correction profiles are explicit affine rescalings of the constructed
smooth cutoff. Their supports lie strictly inside the supplied positive
intervals. The generalized-power determinant theorem then gives exact
finite-moment repair by an actual compactly supported smooth function.
-/

@[expose] public section


noncomputable section

open scoped BigOperators ContDiff
open Set Function MeasureTheory

namespace NavierStokes.LocalizedMomentRepair

/-- Inner lower, given by `(3 * l + u) / 4`. -/
def innerLower (l u : ℝ) : ℝ := (3 * l + u) / 4
/-- Inner upper, given by `(l + 3 * u) / 4`. -/
def innerUpper (l u : ℝ) : ℝ := (l + 3 * u) / 4

/-- A concrete smooth bump in the middle half of `(l,u)`. -/
def bump (l u : ℝ) (t : ℝ) : ℝ :=
  SmoothCutoffs.cutoff ((t - (l + u) / 2) / ((u - l) / 4))

theorem bump_contDiff (l u : ℝ) : ContDiff ℝ ∞ (bump l u) :=
  SmoothCutoffs.cutoff_contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem bump_nonneg (l u t : ℝ) : 0 ≤ bump l u t :=
  (SmoothCutoffs.cutoff_mem_Icc _).1

theorem bump_le_one (l u t : ℝ) : bump l u t ≤ 1 :=
  (SmoothCutoffs.cutoff_mem_Icc _).2

theorem bump_at_center (l u : ℝ) : bump l u ((l + u) / 2) = 1 := by
  apply SmoothCutoffs.cutoff_one_of_abs_le
  simp

theorem bump_support_subset (l u : ℝ) (hlu : l < u) :
    support (bump l u) ⊆ Icc (innerLower l u) (innerUpper l u) := by
  intro t ht
  have hs : (t - (l + u) / 2) / ((u - l) / 4) ∈ Ioo (-1 : ℝ) 1 := by
    rw [← SmoothCutoffs.cutoff_support]
    exact ht
  have hr : 0 < (u - l) / 4 := by linarith
  have hlo := (lt_div_iff₀ hr).mp hs.1
  have hup := (div_lt_iff₀ hr).mp hs.2
  constructor <;> dsimp [innerLower, innerUpper] <;> linarith

theorem bump_tsupport_subset (l u : ℝ) (hlu : l < u) :
    tsupport (bump l u) ⊆ Icc (innerLower l u) (innerUpper l u) :=
  closure_minimal (bump_support_subset l u hlu) isClosed_Icc

theorem bump_hasCompactSupport (l u : ℝ) (hlu : l < u) :
    HasCompactSupport (bump l u) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (bump_support_subset l u hlu)

theorem innerInterval_subset_open (l u : ℝ) (hlu : l < u) :
    Icc (innerLower l u) (innerUpper l u) ⊆ Ioo l u := by
  intro t ht
  dsimp [innerLower, innerUpper] at ht
  constructor <;> linarith [ht.1, ht.2]

theorem bump_tsupport_subset_open (l u : ℝ) (hlu : l < u) :
    tsupport (bump l u) ⊆ Ioo l u :=
  (bump_tsupport_subset l u hlu).trans (innerInterval_subset_open l u hlu)

section Family

variable {n : ℕ}

/-- A fixed compact set, independent of the moment debt. -/
def repairRegion (l u : Fin n → ℝ) : Set ℝ :=
  ⋃ j, Icc (innerLower (l j) (u j)) (innerUpper (l j) (u j))

theorem repairRegion_isCompact (l u : Fin n → ℝ) : IsCompact (repairRegion l u) :=
  isCompact_iUnion fun _ => isCompact_Icc

theorem repairRegion_subset_open (l u : Fin n → ℝ) (hlu : ∀ j, l j < u j) :
    repairRegion l u ⊆ ⋃ j, Ioo (l j) (u j) := by
  intro t ht
  obtain ⟨j, hj⟩ := mem_iUnion.mp ht
  exact mem_iUnion.mpr ⟨j, innerInterval_subset_open _ _ (hlu j) hj⟩

/-- The actual generalized-power moment matrix of the constructed profiles. -/
def matrix (a l u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  PowerMomentMatrix.bumpMomentMatrix a (fun j => bump (l j) (u j))

theorem matrix_det_ne_zero (a l u : Fin n → ℝ) (ha : Injective a)
    (hl : ∀ j, 0 < l j) (hlu : ∀ j, l j < u j)
    (hsep : ∀ i j, i < j → u i ≤ l j) : (matrix a l u).det ≠ 0 := by
  apply PowerMomentMatrix.bumpMomentMatrix_det_ne_zero a
    (fun j => innerLower (l j) (u j)) (fun j => innerUpper (l j) (u j))
    (fun j => bump (l j) (u j)) ha
  · intro j
    dsimp [innerLower]
    linarith [hl j, hlu j]
  · intro i j hij
    dsimp [innerLower, innerUpper]
    linarith [hlu i, hlu j, hsep i j hij]
  · intro j
    exact (bump_contDiff _ _).continuous
  · exact fun j t => bump_nonneg _ _ t
  · intro j
    exact ⟨(l j + u j) / 2, by rw [bump_at_center]; norm_num⟩
  · exact fun j => bump_support_subset _ _ (hlu j)

/-- Coefficients are computed from the proved nonsingular moment matrix. -/
def coefficients (a l u d : Fin n → ℝ) : Fin n → ℝ := (matrix a l u)⁻¹.mulVec d

/-- The constructed smooth correction for the prescribed finite vector of debts. -/
def repair (a l u d : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ j, coefficients a l u d j * bump (l j) (u j) t

theorem repair_contDiff (a l u d : Fin n → ℝ) : ContDiff ℝ ∞ (repair a l u d) := by
  apply ContDiff.sum
  intro j _
  exact contDiff_const.mul (bump_contDiff _ _)

theorem repair_support_subset (a l u d : Fin n → ℝ) (hlu : ∀ j, l j < u j) :
    support (repair a l u d) ⊆ repairRegion l u := by
  intro t ht
  by_contra hnot
  apply ht
  apply Finset.sum_eq_zero
  intro j _
  have hb : bump (l j) (u j) t = 0 := by
    by_contra hb
    exact hnot (mem_iUnion.mpr ⟨j, bump_support_subset _ _ (hlu j) hb⟩)
  rw [hb, mul_zero]

theorem repair_tsupport_subset (a l u d : Fin n → ℝ) (hlu : ∀ j, l j < u j) :
    tsupport (repair a l u d) ⊆ repairRegion l u :=
  closure_minimal (repair_support_subset a l u d hlu) (repairRegion_isCompact l u).isClosed

theorem repair_hasCompactSupport (a l u d : Fin n → ℝ) (hlu : ∀ j, l j < u j) :
    HasCompactSupport (repair a l u d) :=
  HasCompactSupport.of_support_subset_isCompact (repairRegion_isCompact l u)
    (repair_support_subset a l u d hlu)

theorem repair_tsupport_subset_open (a l u d : Fin n → ℝ) (hlu : ∀ j, l j < u j) :
    tsupport (repair a l u d) ⊆ ⋃ j, Ioo (l j) (u j) :=
  (repair_tsupport_subset a l u d hlu).trans (repairRegion_subset_open l u hlu)

theorem integrable_power_mul_bump (p l u : ℝ) (hl : 0 < l) (hlu : l < u) :
    Integrable (fun t => t ^ p * bump l u t) := by
  have hs : support (fun t => t ^ p * bump l u t) ⊆
      Icc (innerLower l u) (innerUpper l u) := by
    intro t ht
    apply bump_support_subset l u hlu
    intro hb
    exact ht (by simp [hb])
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  apply ContinuousOn.integrableOn_Icc
  apply ContinuousOn.mul _ (bump_contDiff l u).continuous.continuousOn
  apply continuousOn_id.rpow_const
  intro t ht
  apply Or.inl
  have hlo : 0 < innerLower l u := by dsimp [innerLower]; linarith
  exact ne_of_gt (lt_of_lt_of_le hlo ht.1)

/-- The prescribed moments hold as exact ordinary Lebesgue integral identities. -/
theorem repair_exact (a l u d : Fin n → ℝ) (ha : Injective a)
    (hl : ∀ j, 0 < l j) (hlu : ∀ j, l j < u j)
    (hsep : ∀ i j, i < j → u i ≤ l j) (i : Fin n) :
    (∫ t, t ^ a i * repair a l u d t) = d i := by
  have hfun : (fun t => t ^ a i * repair a l u d t) =
      (fun t => ∑ j, coefficients a l u d j * (t ^ a i * bump (l j) (u j) t)) := by
    ext t
    simp only [repair, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfun, integral_finsetSum]
  · simp only [integral_const_mul]
    have h := MomentRepair.matrix_mul_coefficients (matrix a l u)
      (matrix_det_ne_zero a l u ha hl hlu hsep) d
    have hi := congrFun h i
    simpa only [matrix, PowerMomentMatrix.bumpMomentMatrix, MomentRepair.coefficients,
      coefficients, Matrix.mulVec, dotProduct, mul_comm] using hi
  · intro j _
    exact (integrable_power_mul_bump (a i) (l j) (u j) (hl j) (hlu j)).const_mul _

/-- Existence from exponents and intervals alone, with an actual function witness. -/
theorem exists_smooth_compact_repair (a l u d : Fin n → ℝ) (ha : Injective a)
    (hl : ∀ j, 0 < l j) (hlu : ∀ j, l j < u j)
    (hsep : ∀ i j, i < j → u i ≤ l j) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ ⋃ j, Ioo (l j) (u j) ∧ ∀ i, (∫ t, t ^ a i * f t) = d i :=
  ⟨repair a l u d, repair_contDiff a l u d, repair_hasCompactSupport a l u d hlu,
    repair_tsupport_subset_open a l u d hlu, repair_exact a l u d ha hl hlu hsep⟩

theorem repair_add (a l u d e : Fin n → ℝ) :
    repair a l u (d + e) = repair a l u d + repair a l u e := by
  ext t
  simp only [repair, coefficients, Matrix.mulVec_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem repair_smul (a l u d : Fin n → ℝ) (r : ℝ) :
    repair a l u (r • d) = r • repair a l u d := by
  ext t
  simp only [repair, coefficients, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, mul_assoc]

theorem repair_sub (a l u d e : Fin n → ℝ) :
    repair a l u (d - e) = repair a l u d - repair a l u e := by
  ext t
  simp only [repair, coefficients, Matrix.mulVec_sub, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- The fixed-interval, fixed-exponent repair depends linearly on the moment debt. -/
def repairLinearMap (a l u : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] (ℝ → ℝ) where
  toFun := repair a l u
  map_add' := repair_add a l u
  map_smul' r d := repair_smul a l u d r

theorem continuous_repair_eval (a l u : Fin n → ℝ) (t : ℝ) :
    Continuous (fun d => repair a l u d t) := by
  unfold repair coefficients Matrix.mulVec dotProduct
  apply continuous_finsetSum
  intro j _
  apply Continuous.mul _ continuous_const
  apply continuous_finsetSum
  intro k _
  exact continuous_const.mul (continuous_apply k)

/-- Continuity in the pointwise function topology; the later jet bounds are stronger. -/
theorem continuous_repair (a l u : Fin n → ℝ) : Continuous (repair a l u) :=
  continuous_pi (continuous_repair_eval a l u)

/-- Decomposition into the finite family of repairs of coordinate debts. -/
theorem repair_eq_sum_coordinate (a l u d : Fin n → ℝ) :
    repair a l u d = fun t => ∑ j, d j * repair a l u (Pi.single j 1) t := by
  have hdecomp : (∑ j, d j • (Pi.single j (1 : ℝ) : Fin n → ℝ)) = d := by
    ext k
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  have h := congrArg (repairLinearMap a l u) hdecomp
  rw [map_sum] at h
  simp only [map_smul] at h
  symm
  convert! h using 1
  ext t
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, repairLinearMap, LinearMap.coe_mk,
    AddHom.coe_mk]

end Family

section Jets

/-- Iterated differentiation commutes with finite sums of smooth real functions. -/
theorem iteratedDeriv_finite_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (fun x => ∑ i ∈ s, f i x) t = ∑ i ∈ s, iteratedDeriv k (f i) t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      cases k with
      | zero => rfl
      | succ k => rw [SmoothCutoffs.iteratedDeriv_const_succ]
  | @insert i s his ih =>
      simp only [Finset.sum_insert his]
      have hi : ContDiffAt ℝ k (f i) t :=
        ((hf i).of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt
      have hs : ContDiffAt ℝ k (fun x => ∑ j ∈ s, f j x) t :=
        ((ContDiff.sum (fun j _ => hf j)).of_le
          (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt
      change iteratedDeriv k (f i + (fun x => ∑ j ∈ s, f j x)) t = _
      rw [iteratedDeriv_add hi hs, ih]

/-- Every derivative of a smooth compactly supported function has a global finite bound. -/
theorem smooth_compact_derivative_bound (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |iteratedDeriv k f t| ≤ C := by
  have hcompact : ∀ j, HasCompactSupport (iteratedDeriv j f) := by
    intro j
    induction j with
    | zero => simpa using hc
    | succ j ih =>
        rw [iteratedDeriv_succ]
        exact ih.deriv
  obtain ⟨C, hC⟩ := (hcompact k).exists_bound_of_continuous
    (hf.continuous_iteratedDeriv k (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)))
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  have ht : |iteratedDeriv k f t| ≤ C := by simpa only [Real.norm_eq_abs] using hC t
  exact ht.trans (le_max_left _ _)

variable {n : ℕ}

/-- Every derivative of the repair is the same linear combination of fixed coordinate repairs. -/
theorem repair_iteratedDeriv_coordinate (a l u d : Fin n → ℝ) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (repair a l u d) t =
      ∑ j, d j * iteratedDeriv k (repair a l u (Pi.single j 1)) t := by
  rw [repair_eq_sum_coordinate a l u d]
  rw [iteratedDeriv_finite_sum Finset.univ
    (fun j x => d j * repair a l u (Pi.single j 1) x)
    (fun j => contDiff_const.mul (repair_contDiff a l u (Pi.single j 1))) k t]
  apply Finset.sum_congr rfl
  intro j _
  exact iteratedDeriv_const_mul (d j)
    ((repair_contDiff a l u (Pi.single j 1)).of_le
      (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt

/-- A uniform-in-space linear estimate for each derivative, with all geometric data fixed. -/
theorem repair_derivative_bound (a l u : Fin n → ℝ) (hlu : ∀ j, l j < u j) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : Fin n → ℝ) (t : ℝ),
      |iteratedDeriv k (repair a l u d) t| ≤ C * ‖d‖ := by
  have hb : ∀ j : Fin n, ∃ C : ℝ, 0 ≤ C ∧ ∀ t,
      |iteratedDeriv k (repair a l u (Pi.single j 1)) t| ≤ C := fun j =>
    smooth_compact_derivative_bound _ (repair_contDiff a l u (Pi.single j 1))
      (repair_hasCompactSupport a l u (Pi.single j 1) hlu) k
  choose C hC hbound using hb
  refine ⟨∑ j, C j, Finset.sum_nonneg (fun j _ => hC j), fun d t => ?_⟩
  rw [repair_iteratedDeriv_coordinate]
  calc
    |∑ j, d j * iteratedDeriv k (repair a l u (Pi.single j 1)) t| ≤
        ∑ j, |d j * iteratedDeriv k (repair a l u (Pi.single j 1)) t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ‖d‖ * C j := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      apply mul_le_mul _ (hbound j t) (abs_nonneg _) (norm_nonneg _)
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm d j
    _ = (∑ j, C j) * ‖d‖ := by rw [← Finset.mul_sum, mul_comm]

/-- All derivatives through any prescribed finite order depend Lipschitz-continuously
on the moment debt, uniformly over the spatial coordinate. -/
theorem repair_finite_jet_bound (a l u : Fin n → ℝ) (hlu : ∀ j, l j < u j) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ N, ∀ (d e : Fin n → ℝ) (t : ℝ),
      |iteratedDeriv k (repair a l u d) t - iteratedDeriv k (repair a l u e) t| ≤
        C * ‖d - e‖ := by
  choose C hC hbound using repair_derivative_bound a l u hlu
  refine ⟨∑ k ∈ Finset.range (N + 1), C k, Finset.sum_nonneg (fun k _ => hC k), ?_⟩
  intro k hk d e t
  have hsub : iteratedDeriv k (repair a l u (d - e)) t =
      iteratedDeriv k (repair a l u d) t - iteratedDeriv k (repair a l u e) t := by
    rw [repair_sub]
    exact iteratedDeriv_sub
      ((repair_contDiff a l u d).of_le
        (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt
      ((repair_contDiff a l u e).of_le
        (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt
  rw [← hsub]
  apply (hbound k (d - e) t).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact Finset.single_le_sum (fun j _ => hC j)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

end Jets

end NavierStokes.LocalizedMomentRepair
