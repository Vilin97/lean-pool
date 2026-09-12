/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.FiveRowRank
public import LeanPool.NavierStokesAndEuler.NavierStokes.UniformAngularReset
public import LeanPool.NavierStokesAndEuler.NavierStokes.JetBounds
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Five actual profile moments on a reserved positive patch

Two axial bumps and three angular bumps are supported in disjoint halves of
the patch. Positive amplitude factoring removes the background parameters
from the normalized quadratic system.
-/

@[expose] public section


noncomputable section


open Set Function Filter MeasureTheory
open scoped BigOperators ContDiff Topology

namespace NavierStokes.FiveProfileMoments

/-- Patch data, collecting `left`, `right`, `left_pos`, `ordered`. -/
structure Patch where
  /-- Left of `Patch`, of type `ℝ`. -/
  left : ℝ
  /-- Right of `Patch`, of type `ℝ`. -/
  right : ℝ
  left_pos : 0 < left
  ordered : left < right

/-- Mid, given by `(P.left + P.right) / 2`. -/
noncomputable def Patch.mid (P : Patch) : ℝ := (P.left + P.right) / 2

/-- Left half, given by `⟨P.left, P.mid, P.left_pos, by dsimp [Patch.mid]; linarith
[P.ordered]⟩`. -/
noncomputable def Patch.leftHalf (P : Patch) : Patch :=
  ⟨P.left, P.mid, P.left_pos, by dsimp [Patch.mid]; linarith [P.ordered]⟩

/-- Right half, given by `⟨P.mid, P.right, by dsimp [Patch.mid]; linarith [P.left_pos,
P.ordered], by dsimp [Patch.mid]; linarith [P.ordered]⟩`. -/
noncomputable def Patch.rightHalf (P : Patch) : Patch :=
  ⟨P.mid, P.right, by dsimp [Patch.mid]; linarith [P.left_pos, P.ordered],
    by dsimp [Patch.mid]; linarith [P.ordered]⟩

section Family

variable {n : ℕ}

/-- Lower, given by `FiveRowRank.cellLower P.left P.right j`. -/
noncomputable def lower (P : Patch) (j : Fin n) : ℝ := FiveRowRank.cellLower P.left P.right j
/-- Upper, given by `FiveRowRank.cellUpper P.left P.right j`. -/
noncomputable def upper (P : Patch) (j : Fin n) : ℝ := FiveRowRank.cellUpper P.left P.right j
/-- Bump, given by `LocalizedMomentRepair.bump (lower P j) (upper P j)`. -/
noncomputable def bump (P : Patch) (j : Fin n) : ℝ → ℝ :=
  LocalizedMomentRepair.bump (lower P j) (upper P j)

theorem lower_gt_left (P : Patch) (j : Fin n) : P.left < lower P j :=
  FiveRowRank.cellLower_gt _ _ P.ordered j

theorem lower_lt_upper (P : Patch) (j : Fin n) : lower P j < upper P j :=
  FiveRowRank.cell_lower_lt_upper _ _ P.ordered j

theorem upper_lt_right (P : Patch) (j : Fin n) : upper P j < P.right :=
  FiveRowRank.cellUpper_lt _ _ P.ordered j

theorem intervals_separated (P : Patch) (i j : Fin n) (hij : i < j) : upper P i ≤ lower P j :=
  FiveRowRank.cell_separated _ _ P.ordered i j hij

theorem bump_contDiff (P : Patch) (j : Fin n) : ContDiff ℝ ∞ (bump P j) :=
  LocalizedMomentRepair.bump_contDiff _ _

theorem bump_tsupport (P : Patch) (j : Fin n) :
    tsupport (bump P j) ⊆ Ioo (lower P j) (upper P j) :=
  LocalizedMomentRepair.bump_tsupport_subset_open _ _ (lower_lt_upper P j)

theorem bump_support_patch (P : Patch) (j : Fin n) : support (bump P j) ⊆ Icc P.left P.right := by
  intro x hx
  have h := bump_tsupport P j (subset_tsupport _ hx)
  exact ⟨(lower_gt_left P j).le.trans h.1.le, h.2.le.trans (upper_lt_right P j).le⟩

theorem bumps_disjoint (P : Patch) (i j : Fin n) (hij : i ≠ j) (x : ℝ) :
    bump P i x * bump P j x = 0 := by
  by_cases hi : bump P i x = 0
  · simp [hi]
  by_cases hj : bump P j x = 0
  · simp [hj]
  have hix := bump_tsupport P i (subset_tsupport _ hi)
  have hjx := bump_tsupport P j (subset_tsupport _ hj)
  rcases lt_or_gt_of_ne hij with h | h
  · linarith [intervals_separated P i j h, hix.2, hjx.1]
  · linarith [intervals_separated P j i h, hjx.2, hix.1]

/-- Correction, given by `∑ j, c j * bump P j x`. -/
noncomputable def correction (P : Patch) (c : Fin n → ℝ) (x : ℝ) : ℝ := ∑ j, c j * bump P j x

theorem correction_contDiff (P : Patch) (c : Fin n → ℝ) : ContDiff ℝ ∞ (correction P c) :=
  ContDiff.sum (fun j _ => contDiff_const.mul (bump_contDiff P j))

theorem correction_support (P : Patch) (c : Fin n → ℝ) :
    support (correction P c) ⊆ Icc P.left P.right := by
  intro x hx
  by_contra hnot
  apply hx
  apply Finset.sum_eq_zero
  intro j _
  have hb : bump P j x = 0 := by
    by_contra hn
    exact hnot (bump_support_patch P j hn)
  simp [hb]

theorem correction_tsupport (P : Patch) (c : Fin n → ℝ) :
    tsupport (correction P c) ⊆ Ioo P.left P.right := by
  have hs : support (correction P c) ⊆ LocalizedMomentRepair.repairRegion (lower (n := n) P) (upper
      P) := by
    intro x hx
    by_contra hnot
    apply hx
    apply Finset.sum_eq_zero
    intro j _
    have hb : bump P j x = 0 := by
      by_contra hn
      exact hnot (mem_iUnion.mpr ⟨j,
        LocalizedMomentRepair.bump_support_subset _ _ (lower_lt_upper P j) hn⟩)
    simp [hb]
  have ht := closure_minimal hs (LocalizedMomentRepair.repairRegion_isCompact (lower (n := n) P)
      (upper P)).isClosed
  intro x hx
  have hm := LocalizedMomentRepair.repairRegion_subset_open (lower (n := n) P) (upper P)
      (lower_lt_upper P) (ht hx)
  obtain ⟨j, hj⟩ := mem_iUnion.mp hm
  exact ⟨(lower_gt_left P j).trans hj.1, hj.2.trans (upper_lt_right P j)⟩

theorem correction_hasCompactSupport (P : Patch) (c : Fin n → ℝ) : HasCompactSupport (correction P
    c) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (correction_support P c)

theorem weighted_integrable (P : Patch) (s : ℝ) (g : ℝ → ℝ)
    (hg : Continuous g) (hs : support g ⊆ Icc P.left P.right) :
    Integrable (fun x => x ^ s * g x) := by
  have hsupport : support (fun x => x ^ s * g x) ⊆ Icc P.left P.right := by
    intro x hx
    apply hs
    intro hz
    exact hx (by simp [hz])
  apply (integrableOn_iff_integrable_of_support_subset hsupport).mp
  apply ContinuousOn.integrableOn_Icc
  apply ContinuousOn.mul _ hg.continuousOn
  apply continuousOn_id.rpow_const
  intro x hx
  exact Or.inl (ne_of_gt (P.left_pos.trans_le hx.1))

theorem correction_square (P : Patch) (c : Fin n → ℝ) (x : ℝ) :
    (correction P c x) ^ 2 = ∑ j, (c j) ^ 2 * (bump P j x) ^ 2 := by
  change (∑ j, c j * bump P j x) ^ 2 = _
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · ring
  · intro j _ hji
    calc
      _ = (c i * c j) * (bump P i x * bump P j x) := by ring
      _ = 0 := by rw [bumps_disjoint P i j hji.symm x, mul_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Bump moment, given by `∫ x, x ^ s * bump P j x`. -/
noncomputable def bumpMoment (P : Patch) (s : ℝ) (j : Fin n) : ℝ := ∫ x, x ^ s * bump P j x
/-- Square moment, given by `∫ x, x ^ s * (bump P j x) ^ 2`. -/
noncomputable def squareMoment (P : Patch) (s : ℝ) (j : Fin n) : ℝ := ∫ x, x ^ s * (bump P j x) ^ 2

theorem weighted_correction_integrable (P : Patch) (s : ℝ) (c : Fin n → ℝ) :
    Integrable (fun x => x ^ s * correction P c x) :=
  weighted_integrable P s _ (correction_contDiff P c).continuous (correction_support P c)

theorem weighted_square_integrable (P : Patch) (s : ℝ) (c : Fin n → ℝ) :
    Integrable (fun x => x ^ s * (correction P c x) ^ 2) := by
  apply weighted_integrable P s _ ((correction_contDiff P c).continuous.pow 2)
  intro x hx
  apply correction_support P c
  intro hz
  exact hx (by simp [hz])

theorem correction_moment (P : Patch) (s : ℝ) (c : Fin n → ℝ) :
    (∫ x, x ^ s * correction P c x) = ∑ j, c j * bumpMoment P s j := by
  have hf : (fun x => x ^ s * correction P c x) =
      fun x => ∑ j, c j * (x ^ s * bump P j x) := by
    funext x
    simp only [correction, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hf, MeasureTheory.integral_finsetSum]
  · simp only [integral_const_mul, bumpMoment]
  · intro j _
    exact (weighted_integrable P s _ (bump_contDiff P j).continuous (bump_support_patch P
        j)).const_mul _

theorem correction_square_moment (P : Patch) (s : ℝ) (c : Fin n → ℝ) :
    (∫ x, x ^ s * (correction P c x) ^ 2) = ∑ j, (c j) ^ 2 * squareMoment P s j := by
  have hf : (fun x => x ^ s * (correction P c x) ^ 2) =
      fun x => ∑ j, (c j) ^ 2 * (x ^ s * (bump P j x) ^ 2) := by
    funext x
    rw [correction_square, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hf, MeasureTheory.integral_finsetSum]
  · simp only [integral_const_mul, squareMoment]
  · intro j _
    apply Integrable.const_mul
    apply weighted_integrable P s _ ((bump_contDiff P j).continuous.pow 2)
    intro x hx
    apply bump_support_patch P j
    intro hz
    exact hx (by simp [hz])

/-- Moment matrix, given by `LocalizedMomentRepair.matrix a (lower P) (upper P)`. -/
noncomputable def momentMatrix (P : Patch) (a : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  LocalizedMomentRepair.matrix a (lower P) (upper P)

theorem momentMatrix_det_ne_zero (P : Patch) (a : Fin n → ℝ) (ha : Injective a) :
    (momentMatrix P a).det ≠ 0 :=
  LocalizedMomentRepair.matrix_det_ne_zero a _ _ ha
    (fun j => P.left_pos.trans (lower_gt_left P j)) (lower_lt_upper P) (intervals_separated P)

/-- Matrix equiv, constructed using `LinearEquiv.toContinuousLinearEquiv`. -/
noncomputable def matrixEquiv (P : Patch) (a : Fin n → ℝ) (ha : Injective a) :
    (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := (momentMatrix P a).mulVec
      invFun := (momentMatrix P a)⁻¹.mulVec
      map_add' := Matrix.mulVec_add _
      map_smul' := fun r c => Matrix.mulVec_smul _ r c
      left_inv := fun c => by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
          (isUnit_iff_ne_zero.mpr (momentMatrix_det_ne_zero P a ha)), Matrix.one_mulVec]
      right_inv := fun c => by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
          (isUnit_iff_ne_zero.mpr (momentMatrix_det_ne_zero P a ha)), Matrix.one_mulVec] }

theorem matrixEquiv_apply (P : Patch) (a : Fin n → ℝ) (ha : Injective a) (c : Fin n → ℝ) (i : Fin
    n) :
    matrixEquiv P a ha c i = ∫ x, x ^ a i * correction P c x := by
  rw [correction_moment]
  change ∑ j, (momentMatrix P a) i j * c j = _
  apply Finset.sum_congr rfl
  intro j _
  change bumpMoment P (a i) j * c j = _
  ring

theorem correction_iteratedDeriv (P : Patch) (c : Fin n → ℝ) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (correction P c) x = ∑ j, c j * iteratedDeriv k (bump P j) x := by
  change iteratedDeriv k (fun y => ∑ j, c j * bump P j y) x = _
  rw [LocalizedMomentRepair.iteratedDeriv_finite_sum Finset.univ
    (fun j x => c j * bump P j x) (fun j => contDiff_const.mul (bump_contDiff P j)) k x]
  apply Finset.sum_congr rfl
  intro j _
  exact iteratedDeriv_const_mul (c j) ((bump_contDiff P j).of_le
    (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt

theorem correction_derivative_bound (P : Patch) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : Fin n → ℝ) (x : ℝ), |iteratedDeriv k (correction P c) x| ≤ C * ‖c‖ := by
  have hb : ∀ j : Fin n, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedDeriv k (bump P j) x| ≤ C := fun j =>
    LocalizedMomentRepair.smooth_compact_derivative_bound _ (bump_contDiff P j)
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc (bump_support_patch P j)) k
  choose C hC hbound using hb
  refine ⟨∑ j, C j, Finset.sum_nonneg (fun j _ => hC j), fun c x => ?_⟩
  rw [correction_iteratedDeriv]
  calc
    _ ≤ ∑ j, |c j * iteratedDeriv k (bump P j) x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ‖c‖ * C j := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      apply mul_le_mul _ (hbound j x) (abs_nonneg _) (norm_nonneg _)
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm c j
    _ = _ := by rw [← Finset.mul_sum, mul_comm]

end Family

/-- Coefficient: an abbreviation for `(Fin 2 → ℝ) × (Fin 3 → ℝ)`. -/
abbrev Coeff := (Fin 2 → ℝ) × (Fin 3 → ℝ)
/-- Debt: an abbreviation for `Fin 5 → ℝ`. -/
abbrev Debt := Fin 5 → ℝ

/-- Good exponent, given by `b ≠ -1 / 2 ∧ b ≠ 1 / 2 ∧ b ≠ 3 / 2`. -/
def GoodExponent (b : ℝ) : Prop := b ≠ -1 / 2 ∧ b ≠ 1 / 2 ∧ b ≠ 3 / 2

theorem good_initial : GoodExponent (1 / 10 : ℝ) := by norm_num [GoodExponent]

theorem good_outgoing (lam : ℝ) (hlam : 0 < lam) : GoodExponent (-1 / 2 - lam) := by
  unfold GoodExponent
  constructor
  · linarith
  constructor <;> linarith

/-- Axial powers, given by `![0, b + 1 / 2]`. -/
noncomputable def axialPowers (b : ℝ) : Fin 2 → ℝ := ![0, b + 1 / 2]
/-- Angular powers, given by `![1 / 2, b, b - 1]`. -/
noncomputable def angularPowers (b : ℝ) : Fin 3 → ℝ := ![1 / 2, b, b - 1]

theorem axialPowers_injective (b : ℝ) (hb : GoodExponent b) : Injective (axialPowers b) := by
  intro i j hij
  by_contra hne
  fin_cases i <;> fin_cases j <;> norm_num [axialPowers] at hij <;> norm_num at hne
  all_goals exact hb.1 (by linarith)

theorem angularPowers_injective (b : ℝ) (hb : GoodExponent b) : Injective (angularPowers b) := by
  intro i j hij
  by_contra hne
  fin_cases i <;> fin_cases j <;> norm_num [angularPowers] at hij <;> norm_num at hne
  all_goals first | exact hb.2.1 (by linarith) | exact hb.2.2 (by linarith)

/-- U, given by `correction P.leftHalf c.1`. -/
noncomputable def u (P : Patch) (c : Coeff) : ℝ → ℝ := correction P.leftHalf c.1
/-- E, given by `correction P.rightHalf c.2`. -/
noncomputable def e (P : Patch) (c : Coeff) : ℝ → ℝ := correction P.rightHalf c.2

theorem u_mul_e (P : Patch) (c d : Coeff) (x : ℝ) : u P c x * e P d x = 0 := by
  by_cases hu : u P c x = 0
  · simp [hu]
  by_cases he : e P d x = 0
  · simp [he]
  have hu' := correction_tsupport P.leftHalf c.1 (subset_tsupport _ hu)
  have he' := correction_tsupport P.rightHalf d.2 (subset_tsupport _ he)
  exact False.elim ((not_lt_of_ge he'.1.le) hu'.2)

/-- Linear equiv as an element of `Coeff ≃L[ℝ] Coeff`. -/
noncomputable def linearEquiv (P : Patch) (b : ℝ) (hb : GoodExponent b) : Coeff ≃L[ℝ] Coeff :=
  (matrixEquiv P.leftHalf (axialPowers b) (axialPowers_injective b hb)).prodCongr
    (matrixEquiv P.rightHalf (angularPowers b) (angularPowers_injective b hb))

/-- Quadratic bilin, bundling `toFun`, `map_add`, `map_smul`, `map_add` and the required
compatibility proofs. -/
noncomputable def quadraticBilin (P : Patch) : Coeff →ₗ[ℝ] Coeff →ₗ[ℝ] Coeff where
  toFun c :=
    { toFun := fun d =>
        (0, ![0,
          (1 / 2) * ∑ j, squareMoment P.rightHalf 0 j * c.2 j * d.2 j -
            ∑ i, squareMoment P.leftHalf 0 i * c.1 i * d.1 i,
          (1 / 2) * ∑ j, squareMoment P.rightHalf (-1) j * c.2 j * d.2 j])
      map_add' := fun d f => by
        apply Prod.ext
        · ext i; simp
        · ext i; fin_cases i <;> simp [Pi.add_apply, Fin.sum_univ_two, Fin.sum_univ_three] <;> ring
      map_smul' := fun r d => by
        apply Prod.ext
        · ext i; simp
        · ext i; fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two,
            Fin.sum_univ_three] <;> ring }
  map_add' c d := by
    apply LinearMap.ext
    intro f
    apply Prod.ext
    · ext i; simp
    · ext i; fin_cases i <;> simp [Pi.add_apply, Fin.sum_univ_two, Fin.sum_univ_three] <;> ring
  map_smul' r c := by
    apply LinearMap.ext
    intro f
    apply Prod.ext
    · ext i; simp
    · ext i; fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two,
        Fin.sum_univ_three] <;> ring

/-- Quadratic continuous linear map, constructed using `LinearMap.toContinuousLinearMap`. -/
noncomputable def quadraticCLM (P : Patch) : Coeff →L[ℝ] Coeff →L[ℝ] Coeff :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Coeff) (F' := Coeff)).toLinearMap.comp
        (quadraticBilin P))

/-- Normalized map as an element of `Coeff`. -/
noncomputable def normalizedMap (P : Patch) (b : ℝ) (c : Coeff) : Coeff :=
  (![∫ x, u P c x, ∫ x, x ^ (b + 1 / 2) * u P c x],
    ![∫ x, x ^ (1 / 2 : ℝ) * e P c x,
      (∫ x, x ^ b * e P c x) + (1 / 2) * (∫ x, (e P c x) ^ 2) - ∫ x, (u P c x) ^ 2,
      (∫ x, x ^ (b - 1) * e P c x) + (1 / 2) * (∫ x, x ^ (-1 : ℝ) * (e P c x) ^ 2)])

theorem linearEquiv_apply (P : Patch) (b : ℝ) (hb : GoodExponent b) (c : Coeff) :
    linearEquiv P b hb c =
      (![∫ x, u P c x, ∫ x, x ^ (b + 1 / 2) * u P c x],
        ![∫ x, x ^ (1 / 2 : ℝ) * e P c x, ∫ x, x ^ b * e P c x, ∫ x, x ^ (b - 1) * e P c x]) := by
  apply Prod.ext
  · ext i
    change matrixEquiv P.leftHalf (axialPowers b) (axialPowers_injective b hb) c.1 i = _
    rw [matrixEquiv_apply]
    fin_cases i <;> simp [axialPowers, u]
  · ext i
    change matrixEquiv P.rightHalf (angularPowers b) (angularPowers_injective b hb) c.2 i = _
    rw [matrixEquiv_apply]
    fin_cases i <;> simp [angularPowers, e]

theorem normalizedMap_identity (P : Patch) (b : ℝ) (hb : GoodExponent b) (c : Coeff) :
    linearEquiv P b hb c + quadraticCLM P c c = normalizedMap P b c := by
  have hUS := correction_square_moment P.leftHalf 0 c.1
  have hES := correction_square_moment P.rightHalf 0 c.2
  have hEP := correction_square_moment P.rightHalf (-1) c.2
  simp only [Real.rpow_zero, one_mul] at hUS hES
  rw [linearEquiv_apply]
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [quadraticCLM, quadraticBilin, normalizedMap]
  · ext i
    fin_cases i <;> simp [quadraticCLM, quadraticBilin, normalizedMap,
      u, e, hUS, hES, hEP, Fin.sum_univ_two, Fin.sum_univ_three] <;> ring

theorem spatial_jet_bound (P : Patch) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : Coeff) (x : ℝ),
      |iteratedDeriv k (u P c) x| ≤ C * ‖c‖ ∧ |iteratedDeriv k (e P c) x| ≤ C * ‖c‖ := by
  obtain ⟨CU, hCU, hU⟩ := correction_derivative_bound (n := 2) P.leftHalf k
  obtain ⟨CE, hCE, hE⟩ := correction_derivative_bound (n := 3) P.rightHalf k
  refine ⟨CU + CE + 1, by linarith, fun c x => ⟨?_, ?_⟩⟩
  · exact (hU c.1 x).trans ((mul_le_mul_of_nonneg_left (norm_fst_le c) hCU).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg c)))
  · exact (hE c.2 x).trans ((mul_le_mul_of_nonneg_left (norm_snd_le c) hCE).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg c)))

theorem finite_spatial_jet_bound (P : Patch) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k ≤ N, ∀ (c : Coeff) (x : ℝ),
      |iteratedDeriv k (u P c) x| ≤ C * ‖c‖ ∧ |iteratedDeriv k (e P c) x| ≤ C * ‖c‖ := by
  choose C hC hbound using spatial_jet_bound P
  let K : ℝ := 1 + ∑ k ∈ Finset.range (N + 1), C k
  have hK : 0 < K := by
    have hs : 0 ≤ ∑ k ∈ Finset.range (N + 1), C k := Finset.sum_nonneg (fun k _ => (hC k).le)
    dsimp [K]
    linarith
  refine ⟨K, hK, ?_⟩
  intro k hk c x
  have hCK : C k ≤ K := by
    have h := Finset.single_le_sum (fun j _ => (hC j).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    dsimp [K]
    linarith
  exact ⟨(hbound k c x).1.trans (mul_le_mul_of_nonneg_right hCK (norm_nonneg c)),
    (hbound k c x).2.trans (mul_le_mul_of_nonneg_right hCK (norm_nonneg c))⟩

theorem power_lower_bound (P : Patch) (b : ℝ) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ Icc P.left P.right, m ≤ x ^ b := by
  apply isCompact_Icc.exists_forall_le'
  · apply continuousOn_id.rpow_const
    intro x hx
    exact Or.inl (ne_of_gt (P.left_pos.trans_le hx.1))
  · intro x hx
    exact Real.rpow_pos_of_pos (P.left_pos.trans_le hx.1) b

/-- One fixed nonlinear inverse works for all amplitudes and constant axial
backgrounds, because they have been factored out of the actual moments. -/
theorem exists_normalized_repair (P : Patch) (b : ℝ) (hb : GoodExponent b) :
    ∃ (g : Coeff → Coeff) (ε C : ℝ), 0 < ε ∧ 0 < C ∧
      ContDiffOn ℝ ∞ g (Metric.ball 0 ε) ∧ g 0 = 0 ∧
      ∀ d ∈ Metric.ball (0 : Coeff) ε,
        normalizedMap P b (g d) = d ∧ ‖g d‖ ≤ C * ‖d‖ ∧ ‖fderiv ℝ g d‖ ≤ C ∧
        ∀ x : ℝ, 0 < x → 0 < x ^ b + e P (g d) x := by
  let B := linearEquiv P b hb
  let A := quadraticCLM P
  let β : ℝ := ‖B.symm.toContinuousLinearMap‖ + 1
  let K : ℝ := ‖A‖ + 1
  let r : ℝ := 1 / (4 * β * K)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hinv : ∀ v, ‖B.symm v‖ ≤ β * ‖v‖ := by
    intro v
    exact (B.symm.toContinuousLinearMap.le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (by dsimp [β]; linarith) (norm_nonneg v))
  have hA : ‖A‖ ≤ K := by dsimp [K]; linarith
  have hsmall : 4 * β * K * r ≤ 1 := by dsimp [r]; field_simp ; rfl
  obtain ⟨g, hg, hgeq, hglip⟩ := UniformAngularReset.exists_smooth_solver_on_ball
    B A β K r hβ hK.le hr hinv hA hsmall
  obtain ⟨D, hD, hjet⟩ := spatial_jet_bound P 0
  obtain ⟨m, hm, hmin⟩ := power_lower_bound P.rightHalf b
  let C : ℝ := (1 + D) * (2 * β)
  let ε : ℝ := min (r / (4 * β)) (m / (2 * C))
  have hC : 0 < C := mul_pos (by linarith) (by positivity)
  have hε : 0 < ε := lt_min (div_pos hr (by positivity)) (div_pos hm (by positivity))
  have hsub : Metric.ball (0 : Coeff) ε ⊆ Metric.ball 0 (r / (4 * β)) :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hC₀ : 2 * β ≤ C := by dsimp [C]; nlinarith
  have hC₁ : D * (2 * β) ≤ C := by dsimp [C]; linarith
  have hzero : g 0 = 0 := by
    have hz := (hgeq 0 (Metric.mem_ball_self (div_pos hr (by positivity)))).2
    simpa only [norm_zero, mul_zero, norm_le_zero_iff] using hz
  refine ⟨g, ε, C, hε, hC, hg.mono hsub, hzero, ?_⟩
  intro d hd
  have hnorm : ‖g d‖ ≤ 2 * β * ‖d‖ := (hgeq d (hsub hd)).2
  have hbound : D * ‖g d‖ ≤ C * ‖d‖ :=
    (mul_le_mul_of_nonneg_left hnorm hD.le).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hC₁ (norm_nonneg d))
  have heq := (hgeq d (hsub hd)).1
  change linearEquiv P b hb (g d) + quadraticCLM P (g d) (g d) = d at heq
  rw [normalizedMap_identity] at heq
  refine ⟨heq, hnorm.trans (mul_le_mul_of_nonneg_right hC₀ (norm_nonneg d)), ?_, ?_⟩
  · apply le_trans _ hC₀
    apply norm_fderiv_le_of_lip' ℝ (by positivity : 0 ≤ 2 * β)
    filter_upwards [Metric.isOpen_ball.mem_nhds (hsub hd)] with f hf
    exact hglip f hf d (hsub hd)
  · intro x hx
    by_cases he : e P (g d) x = 0
    · simpa only [he, add_zero] using Real.rpow_pos_of_pos hx b
    have hbase := hmin x (correction_support P.rightHalf (g d).2 he)
    have hval : |e P (g d) x| ≤ C * ‖d‖ := (hjet (g d) x).2.trans hbound
    have hd' : ‖d‖ < ε := by simpa only [Metric.mem_ball, dist_zero_right] using hd
    have hsize : C * ‖d‖ < m / 2 := by
      have ht := mul_lt_mul_of_pos_left (hd'.trans_le (min_le_right _ _)) hC
      have hcancel : C * (m / (2 * C)) = m / 2 := by field_simp
      rwa [hcancel] at ht
    have hlow := neg_abs_le (e P (g d) x)
    linarith

/-- Physical U, given by `G + A * u P c x`. -/
noncomputable def physicalU (P : Patch) (A G : ℝ) (c : Coeff) (x : ℝ) : ℝ := G + A * u P c x
/-- Physical E, given by `A * (x ^ b + e P c x)`. -/
noncomputable def physicalE (P : Patch) (b A : ℝ) (c : Coeff) (x : ℝ) : ℝ := A * (x ^ b + e P c x)

/-- Physical density as an element of `Debt`. -/
noncomputable def physicalDensity (P : Patch) (b A G : ℝ) (c : Coeff) (x : ℝ) : Debt :=
  ![physicalU P A G c x - G,
    Real.sqrt (2 * x) * (physicalE P b A c x - A * x ^ b),
    physicalU P A G c x * Real.sqrt (2 * x) * physicalE P b A c x - G * Real.sqrt (2 * x) * (A * x
        ^ b),
    (physicalU P A G c x ^ 2 - physicalE P b A c x ^ 2 / 2) - (G ^ 2 - (A * x ^ b) ^ 2 / 2),
    (physicalE P b A c x ^ 2 - (A * x ^ b) ^ 2) / (2 * x)]

/-- Physical moments, defined pointwise by `∫ x, physicalDensity P b A G c x i`. -/
noncomputable def physicalMoments (P : Patch) (b A G : ℝ) (c : Coeff) : Debt :=
  fun i => ∫ x, physicalDensity P b A G c x i

/-- Physical debt as an element of `Debt`. -/
noncomputable def physicalDebt (A G : ℝ) (z : Coeff) : Debt :=
  ![A * z.1 0, Real.sqrt 2 * A * z.2 0,
    Real.sqrt 2 * A ^ 2 * z.1 1 + G * (Real.sqrt 2 * A * z.2 0),
    2 * G * A * z.1 0 - A ^ 2 * z.2 1, A ^ 2 * z.2 2]

/-- Normalized debt, given by `(![d 0 / A, (d 2 - G * d 1) / (Real.sqrt 2 * A ^ 2)], ![d 1 /
(Real.sqrt 2 * A), (2 * G * d 0 - d 3) / A ^ 2, d 4 / A ^ 2])`. -/
noncomputable def normalizedDebt (A G : ℝ) (d : Debt) : Coeff :=
  (![d 0 / A, (d 2 - G * d 1) / (Real.sqrt 2 * A ^ 2)],
    ![d 1 / (Real.sqrt 2 * A), (2 * G * d 0 - d 3) / A ^ 2, d 4 / A ^ 2])

theorem physical_normalized_debt (A G : ℝ) (hA : A ≠ 0) (d : Debt) :
    physicalDebt A G (normalizedDebt A G d) = d := by
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  ext i
  fin_cases i <;> simp [physicalDebt, normalizedDebt] <;> field_simp
  all_goals ring

theorem normalized_physical_debt (A G : ℝ) (hA : A ≠ 0) (c : Coeff) :
    normalizedDebt A G (physicalDebt A G c) = c := by
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [physicalDebt, normalizedDebt] <;> field_simp
  · ext i
    fin_cases i <;> simp [physicalDebt, normalizedDebt] <;> field_simp
    all_goals ring

/-- Physical equiv, constructed using `LinearEquiv.toContinuousLinearEquiv`. -/
noncomputable def physicalEquiv (A G : ℝ) (hA : A ≠ 0) : Coeff ≃L[ℝ] Debt :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := physicalDebt A G
      invFun := normalizedDebt A G
      left_inv := normalized_physical_debt A G hA
      right_inv := physical_normalized_debt A G hA
      map_add' := fun c d => by ext i; fin_cases i <;> simp [physicalDebt] <;> ring
      map_smul' := fun r c => by ext i; fin_cases i <;> simp [physicalDebt, smul_eq_mul] <;> ring }

/-- Normalized density as an element of `Coeff`. -/
noncomputable def normalizedDensity (P : Patch) (b : ℝ) (c : Coeff) (x : ℝ) : Coeff :=
  (![u P c x, x ^ (b + 1 / 2) * u P c x],
    ![x ^ (1 / 2 : ℝ) * e P c x,
      x ^ b * e P c x + (1 / 2) * e P c x ^ 2 - u P c x ^ 2,
      x ^ (b - 1) * e P c x + (1 / 2) * (x ^ (-1 : ℝ) * e P c x ^ 2)])

theorem physicalDensity_eq (P : Patch) (b A G : ℝ) (c : Coeff) (x : ℝ) :
    physicalDensity P b A G c x = physicalDebt A G (normalizedDensity P b c x) := by
  by_cases hx : 0 < x
  · have hs : Real.sqrt (2 * x) = Real.sqrt 2 * x ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_eq_rpow x]
    have hplus : x ^ (b + 1 / 2) = x ^ b * x ^ (1 / 2 : ℝ) := Real.rpow_add hx _ _
    have hminus : x ^ (b - 1) = x ^ b * x⁻¹ := by
      rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_neg_one]
    have hJ : physicalU P A G c x * Real.sqrt (2 * x) * physicalE P b A c x -
        G * Real.sqrt (2 * x) * (A * x ^ b) =
        A ^ 2 * (Real.sqrt (2 * x) * x ^ b) * u P c x + G * A * Real.sqrt (2 * x) * e P c x := by
      calc
        _ = A ^ 2 * (Real.sqrt (2 * x) * x ^ b) * u P c x + G * A * Real.sqrt (2 * x) * e P c x +
            (A ^ 2 * Real.sqrt (2 * x)) * (u P c x * e P c x) := by
              unfold physicalU physicalE
              ring
        _ = _ := by rw [u_mul_e]; ring
    ext i
    fin_cases i
    · simp [physicalDensity, physicalDebt, normalizedDensity, physicalU]
    · simp [physicalDensity, physicalDebt, normalizedDensity, physicalE, hs]
      ring
    · simp only [physicalDensity, physicalDebt, normalizedDensity]
      change physicalU P A G c x * Real.sqrt (2 * x) * physicalE P b A c x -
        G * Real.sqrt (2 * x) * (A * x ^ b) =
          Real.sqrt 2 * A ^ 2 * (x ^ (b + 1 / 2) * u P c x) +
            G * (Real.sqrt 2 * A * (x ^ (1 / 2 : ℝ) * e P c x))
      rw [hJ, hs, hplus]
      ring
    · simp [physicalDensity, physicalDebt, normalizedDensity, physicalU, physicalE]
      ring
    · simp [physicalDensity, physicalDebt, normalizedDensity, physicalE, hminus, Real.rpow_neg_one]
      field_simp [hx.ne']; ring
  · have hu : u P c x = 0 := by
      exact Classical.byContradiction (fun hn =>
        hx (P.leftHalf.left_pos.trans_le (correction_support P.leftHalf c.1 hn).1))
    have he : e P c x = 0 := by
      exact Classical.byContradiction (fun hn =>
        hx (P.rightHalf.left_pos.trans_le (correction_support P.rightHalf c.2 hn).1))
    ext i
    fin_cases i <;> simp [physicalDensity, physicalDebt, normalizedDensity, physicalU, physicalE,
        hu, he]

theorem integrable_fin_vector {n : ℕ} (f : ℝ → Fin n → ℝ)
    (hf : ∀ i, Integrable (fun x => f x i)) : Integrable f := by
  classical
  have heq : f = fun x => ∑ i, f x i • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
    funext x j
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  rw [heq]
  exact MeasureTheory.integrable_finsetSum _ (fun i _ => (hf i).smul_const (Pi.single i 1))

theorem integral_fin_apply {n : ℕ} {f : ℝ → Fin n → ℝ} (hf : Integrable f) (i : Fin n) :
    (∫ x, f x) i = ∫ x, f x i :=
  ((ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).integral_comp_comm hf).symm

theorem integral_fst_apply {f : ℝ → Coeff} (hf : Integrable f) (i : Fin 2) :
    (∫ x, f x).1 i = ∫ x, (f x).1 i :=
  (((ContinuousLinearMap.proj i : (Fin 2 → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (Fin 3 → ℝ))).integral_comp_comm hf).symm

theorem integral_snd_apply {f : ℝ → Coeff} (hf : Integrable f) (i : Fin 3) :
    (∫ x, f x).2 i = ∫ x, (f x).2 i :=
  (((ContinuousLinearMap.proj i : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 3 → ℝ))).integral_comp_comm hf).symm

theorem normalizedDensity_integrable (P : Patch) (b : ℝ) (c : Coeff) :
    Integrable (normalizedDensity P b c) := by
  have hu := weighted_correction_integrable P.leftHalf 0 c.1
  have huu := weighted_square_integrable P.leftHalf 0 c.1
  have hee := weighted_square_integrable P.rightHalf 0 c.2
  simp only [Real.rpow_zero, one_mul] at hu huu hee
  apply Integrable.prodMk
  · apply integrable_fin_vector
    intro i
    fin_cases i
    · exact hu
    · exact weighted_correction_integrable P.leftHalf (b + 1 / 2) c.1
  · apply integrable_fin_vector
    intro i
    fin_cases i
    · exact weighted_correction_integrable P.rightHalf (1 / 2) c.2
    · exact ((weighted_correction_integrable P.rightHalf b c.2).add (hee.const_mul (1 / 2))).sub huu
    · exact (weighted_correction_integrable P.rightHalf (b - 1) c.2).add
        ((weighted_square_integrable P.rightHalf (-1) c.2).const_mul (1 / 2))

theorem normalizedDensity_integral (P : Patch) (b : ℝ) (c : Coeff) :
    (∫ x, normalizedDensity P b c x) = normalizedMap P b c := by
  have hi := normalizedDensity_integrable P b c
  have huu := weighted_square_integrable P.leftHalf 0 c.1
  have hee := weighted_square_integrable P.rightHalf 0 c.2
  simp only [Real.rpow_zero, one_mul] at huu hee
  apply Prod.ext
  · ext i
    rw [integral_fst_apply hi i]
    fin_cases i <;> rfl
  · ext i
    rw [integral_snd_apply hi i]
    fin_cases i
    · rfl
    · change (∫ x, x ^ b * e P c x + (1 / 2) * e P c x ^ 2 - u P c x ^ 2) = _
      unfold u e
      have hs := integral_sub ((weighted_correction_integrable P.rightHalf b c.2).add
          (hee.const_mul (1 / 2))) huu
      simp only [Pi.add_apply] at hs
      rw [hs, integral_add (weighted_correction_integrable P.rightHalf b c.2) (hee.const_mul (1 /
          2)), integral_const_mul]
      rfl
    · change (∫ x, x ^ (b - 1) * e P c x + (1 / 2) * (x ^ (-1 : ℝ) * e P c x ^ 2)) = _
      unfold e
      rw [integral_add (weighted_correction_integrable P.rightHalf (b - 1) c.2)
        ((weighted_square_integrable P.rightHalf (-1) c.2).const_mul (1 / 2)), integral_const_mul]
      rfl

theorem physicalMoments_eq (P : Patch) (b A G : ℝ) (hA : A ≠ 0) (c : Coeff) :
    physicalMoments P b A G c = physicalDebt A G (normalizedMap P b c) := by
  have hi := normalizedDensity_integrable P b c
  have h := (physicalEquiv A G hA).toContinuousLinearMap.integral_comp_comm hi
  rw [normalizedDensity_integral] at h
  ext i
  have hc := congrFun h i
  rw [integral_fin_apply ((physicalEquiv A G hA).toContinuousLinearMap.integrable_comp hi) i] at hc
  change (∫ x, physicalDensity P b A G c x i) = _
  simp only [physicalDensity_eq]
  exact hc

/-- The full physical derivative in the five raw bump coefficients is an
explicit continuous linear equivalence. Its two actual moment determinants
were proved nonzero above. -/
noncomputable def actualLinearEquiv (P : Patch) (b A G : ℝ) (hb : GoodExponent b)
    (hA : A ≠ 0) : Coeff ≃L[ℝ] Debt := (linearEquiv P b hb).trans (physicalEquiv A G hA)

theorem physicalMoments_hasFDerivAt_zero (P : Patch) (b A G : ℝ) (hb : GoodExponent b)
    (hA : A ≠ 0) : HasFDerivAt (physicalMoments P b A G)
      (actualLinearEquiv P b A G hb hA).toContinuousLinearMap 0 := by
  have hn : normalizedMap P b =
      UniformAngularReset.quadraticMap (linearEquiv P b hb) (quadraticCLM P) :=
    funext (fun c => (normalizedMap_identity P b hb c).symm)
  have hd : HasFDerivAt (normalizedMap P b) (linearEquiv P b hb).toContinuousLinearMap 0 := by
    rw [hn]
    simpa [UniformAngularReset.tangent] using
      UniformAngularReset.quadraticMap_hasFDerivAt (linearEquiv P b hb) (quadraticCLM P) 0
  have hp : physicalMoments P b A G = fun c => physicalEquiv A G hA (normalizedMap P b c) :=
    funext (physicalMoments_eq P b A G hA)
  rw [hp]
  exact (physicalEquiv A G hA).hasFDerivAt.comp 0 hd

theorem physicalDensity_zero_outside (P : Patch) (b A G : ℝ) (c : Coeff) {x : ℝ}
    (hx : x ∉ Ioo P.left P.right) : physicalDensity P b A G c x = 0 := by
  have hu : u P c x = 0 := by
    apply Classical.byContradiction
    intro hn
    have hs := correction_tsupport P.leftHalf c.1 (subset_tsupport _ hn)
    apply hx
    exact ⟨hs.1, hs.2.trans (by dsimp [Patch.leftHalf, Patch.mid]; linarith [P.ordered])⟩
  have he : e P c x = 0 := by
    apply Classical.byContradiction
    intro hn
    have hs := correction_tsupport P.rightHalf c.2 (subset_tsupport _ hn)
    apply hx
    have hl : P.left < P.rightHalf.left := by
        dsimp [Patch.rightHalf, Patch.mid]; linarith [P.ordered]
    exact ⟨hl.trans hs.1, hs.2⟩
  rw [physicalDensity_eq]
  ext i
  fin_cases i <;> simp [physicalDebt, normalizedDensity, hu, he]

theorem physicalMoments_positive_axis (P : Patch) (b A G : ℝ) (c : Coeff) (i : Fin 5) :
    (∫ x in Ioi (0 : ℝ), physicalDensity P b A G c x i) = physicalMoments P b A G c i := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hout : x ∉ Ioo P.left P.right := fun h => hx (P.left_pos.trans h.1)
  rw [physicalDensity_zero_outside P b A G c hout]
  rfl

theorem physicalDensity_integrable (P : Patch) (b A G : ℝ) (hA : A ≠ 0) (c : Coeff) (i : Fin 5) :
    Integrable (fun x => physicalDensity P b A G c x i) := by
  have hi := (physicalEquiv A G hA).toContinuousLinearMap.integrable_comp
    (normalizedDensity_integrable P b c)
  have he := (ContinuousLinearMap.proj i : Debt →L[ℝ] ℝ).integrable_comp hi
  simp only [physicalDensity_eq]
  exact he

/-- Normalization linear map, bundling `toFun`, `map_add`, `map_smul`. -/
noncomputable def normalizationLinearMap (A G : ℝ) : Debt →ₗ[ℝ] Coeff where
  toFun := normalizedDebt A G
  map_add' c d := by
    apply Prod.ext
    · ext i; fin_cases i <;> simp [normalizedDebt] <;> ring
    · ext i; fin_cases i <;> simp [normalizedDebt] <;> ring
  map_smul' r c := by
    apply Prod.ext
    · ext i; fin_cases i <;> simp [normalizedDebt, smul_eq_mul] <;> ring
    · ext i; fin_cases i <;> simp [normalizedDebt, smul_eq_mul] <;> ring

theorem normalizedDebt_contDiffOn {S : Set ℝ} {A G : ℝ → ℝ} {d : ℝ → Debt}
    (hA : ContDiffOn ℝ ∞ A S) (hG : ContDiffOn ℝ ∞ G S) (hd : ContDiffOn ℝ ∞ d S)
    (hAn : ∀ p ∈ S, A p ≠ 0) :
    ContDiffOn ℝ ∞ (fun p => normalizedDebt (A p) (G p) (d p)) S := by
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  apply ContDiffOn.prodMk
  · apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · exact (contDiffOn_pi.mp hd 0).div hA hAn
    · exact ((contDiffOn_pi.mp hd 2).sub (hG.mul (contDiffOn_pi.mp hd 1))).div
        (contDiffOn_const.mul (hA.pow 2)) (fun p hp => mul_ne_zero hs (pow_ne_zero 2 (hAn p hp)))
  · apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · exact (contDiffOn_pi.mp hd 1).div (contDiffOn_const.mul hA) (fun p hp => mul_ne_zero hs (hAn
        p hp))
    · exact (((contDiffOn_const.mul hG).mul (contDiffOn_pi.mp hd 0)).sub (contDiffOn_pi.mp hd
        3)).div
        (hA.pow 2) (fun p hp => pow_ne_zero 2 (hAn p hp))
    · exact (contDiffOn_pi.mp hd 4).div (hA.pow 2) (fun p hp => pow_ne_zero 2 (hAn p hp))

theorem normalizedDebt_contDiff {A G : ℝ → ℝ} {d : ℝ → Debt}
    (hA : ContDiff ℝ ∞ A) (hG : ContDiff ℝ ∞ G) (hd : ContDiff ℝ ∞ d)
    (hAn : ∀ p, A p ≠ 0) : ContDiff ℝ ∞ (fun p => normalizedDebt (A p) (G p) (d p)) :=
  contDiffOn_univ.mp (normalizedDebt_contDiffOn hA.contDiffOn hG.contDiffOn hd.contDiffOn (fun p _
      => hAn p))

theorem normalizedDebt_eq_sum (A G : ℝ) (d : Debt) :
    normalizedDebt A G d = ∑ i, d i • normalizedDebt A G (Pi.single i 1) := by
  have h : (∑ i, d i • (Pi.single i (1 : ℝ) : Debt)) = d := by
    ext j
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  have he := congrArg (normalizationLinearMap A G) h
  rw [map_sum] at he
  simp only [map_smul] at he
  exact he.symm

theorem compact_normalization_bound (S : Set ℝ) (hS : IsCompact S) {A G : ℝ → ℝ}
    (hA : ContDiffOn ℝ ∞ A S) (hG : ContDiffOn ℝ ∞ G S) (hAn : ∀ p ∈ S, A p ≠ 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ p ∈ S, ∀ d : Debt, ‖normalizedDebt (A p) (G p) d‖ ≤ K * ‖d‖ := by
  have hi : ∀ i : Fin 5, ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ S,
      ‖normalizedDebt (A p) (G p) (Pi.single i 1)‖ ≤ B := by
    intro i
    obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn
      (normalizedDebt_contDiffOn hA hG (d := fun _ => Pi.single i 1) contDiffOn_const
          hAn).continuousOn
    exact ⟨max B 0, le_max_right _ _, fun p hp => (hB p hp).trans (le_max_left _ _)⟩
  choose B hB hbound using hi
  let K : ℝ := 1 + ∑ i, B i
  have hK : 0 < K := by
    have hs := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hB i)
    dsimp [K]
    linarith
  refine ⟨K, hK, ?_⟩
  intro p hp d
  rw [normalizedDebt_eq_sum]
  calc
    _ ≤ ∑ i, ‖d i • normalizedDebt (A p) (G p) (Pi.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖d‖ * B i := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (norm_le_pi_norm d i) (hbound i p hp) (norm_nonneg _) (norm_nonneg _)
    _ = (∑ i, B i) * ‖d‖ := by rw [← Finset.mul_sum, mul_comm]
    _ ≤ K * ‖d‖ := mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) (norm_nonneg d)

theorem correction_family_contDiffOn {n : ℕ} (P : Patch) {S : Set ℝ} {c : ℝ → Fin n → ℝ}
    (hc : ContDiffOn ℝ ∞ c S) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => correction P (c z.1) z.2) (S ×ˢ univ) := by
  apply ContDiffOn.sum
  intro j _
  exact ((contDiffOn_pi.mp hc j).comp contDiffOn_fst (fun z hz => hz.1)).mul
    ((bump_contDiff P j).comp contDiff_snd).contDiffOn

theorem physicalU_family_contDiffOn (P : Patch) {S : Set ℝ} {A G : ℝ → ℝ} {c : ℝ → Coeff}
    (hA : ContDiffOn ℝ ∞ A S) (hG : ContDiffOn ℝ ∞ G S) (hc : ContDiffOn ℝ ∞ c S) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => physicalU P (A z.1) (G z.1) (c z.1) z.2) (S ×ˢ univ) :=
  (hG.comp contDiffOn_fst (fun _ hz => hz.1)).add
    ((hA.comp contDiffOn_fst (fun _ hz => hz.1)).mul (correction_family_contDiffOn P.leftHalf
        hc.fst))

theorem physicalE_family_contDiffOn (P : Patch) (b : ℝ) {S : Set ℝ} {A : ℝ → ℝ} {c : ℝ → Coeff}
    (hA : ContDiffOn ℝ ∞ A S) (hc : ContDiffOn ℝ ∞ c S) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => physicalE P b (A z.1) (c z.1) z.2) (S ×ˢ Ioi 0) := by
  apply (hA.comp contDiffOn_fst (fun z hz => hz.1)).mul
  apply ContDiffOn.add
  · exact contDiffOn_snd.rpow_const_of_ne (fun z hz => ne_of_gt hz.2)
  · exact (correction_family_contDiffOn P.rightHalf hc.snd).mono (fun z hz => ⟨hz.1, mem_univ _⟩)

/-- Every fixed finite spatial jet of the physical edits is small with the
physical debt, uniformly on compact parameter sets. The actual coefficient
branch is smooth on an open neighborhood of the compact set. -/
theorem compact_parameter_repair (P : Patch) (b : ℝ) (hb : GoodExponent b)
    (S : Set ℝ) (hS : IsCompact S) (A G : ℝ → ℝ)
    (hA : ContDiff ℝ ∞ A) (hG : ContDiff ℝ ∞ G) (hApos : ∀ p, 0 < A p) (N : ℕ) :
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧ ∀ d : ℝ → Debt,
      ContDiff ℝ ∞ d → (∀ p ∈ S, ‖d p‖ < ε) →
      ∃ (c : ℝ → Coeff) (V : Set ℝ), IsOpen V ∧ S ⊆ V ∧ ContDiffOn ℝ ∞ c V ∧
        (∀ p ∈ V, physicalMoments P b (A p) (G p) (c p) = d p ∧
          ∀ x : ℝ, 0 < x → 0 < physicalE P b (A p) (c p) x) ∧
        ∀ p ∈ S, ‖c p‖ ≤ K * ‖d p‖ ∧ ∀ k ≤ N, ∀ x : ℝ,
          |iteratedDeriv k (fun y => A p * u P (c p) y) x| ≤ K * ‖d p‖ ∧
          |iteratedDeriv k (fun y => A p * e P (c p) y) x| ≤ K * ‖d p‖ := by
  obtain ⟨g, ε₀, C, hε₀, hC, hg, _, hgeq⟩ := exists_normalized_repair P b hb
  obtain ⟨D, hD, hnorm⟩ := compact_normalization_bound S hS hA.contDiffOn hG.contDiffOn
    (fun p _ => (hApos p).ne')
  obtain ⟨J, hJ, hjets⟩ := finite_spatial_jet_bound P N
  obtain ⟨L₀, hL₀⟩ := hS.exists_bound_of_continuousOn hA.continuous.continuousOn
  let L : ℝ := 1 + |L₀|
  have hL : 0 < L := by dsimp [L]; positivity
  have hAbound : ∀ p ∈ S, |A p| ≤ L := by
    intro p hp
    exact (hL₀ p hp).trans (by dsimp [L]; linarith [le_abs_self L₀])
  let K : ℝ := (1 + L) * (1 + J) * (C * D)
  have hK : 0 < K := by dsimp [K]; positivity
  have hKC : C * D ≤ K := by
    dsimp [K]
    nlinarith [mul_pos hC hD, mul_pos hL hJ]
  have hKJ : L * J * (C * D) ≤ K := by
    dsimp [K]
    linarith [mul_pos hC hD, mul_pos hL (mul_pos hC hD), mul_pos hJ (mul_pos hC hD)]
  refine ⟨ε₀ / D, K, div_pos hε₀ hD, hK, ?_⟩
  intro d hd hsmall
  let f : ℝ → Coeff := fun p => normalizedDebt (A p) (G p) (d p)
  have hf : ContDiff ℝ ∞ f := normalizedDebt_contDiff hA hG hd (fun p => (hApos p).ne')
  let V : Set ℝ := f ⁻¹' Metric.ball 0 ε₀
  have hV : IsOpen V := Metric.isOpen_ball.preimage hf.continuous
  have hSV : S ⊆ V := by
    intro p hp
    change ‖f p - 0‖ < ε₀
    rw [sub_zero]
    calc
      ‖f p‖ ≤ D * ‖d p‖ := hnorm p hp (d p)
      _ < D * (ε₀ / D) := mul_lt_mul_of_pos_left (hsmall p hp) hD
      _ = ε₀ := by field_simp
  let c : ℝ → Coeff := g ∘ f
  have hc : ContDiffOn ℝ ∞ c V := hg.comp hf.contDiffOn (fun p hp => hp)
  refine ⟨c, V, hV, hSV, hc, ?_, ?_⟩
  · intro p hp
    have hs := hgeq (f p) hp
    constructor
    · rw [physicalMoments_eq P b (A p) (G p) (hApos p).ne']
      change physicalDebt (A p) (G p) (normalizedMap P b (g (f p))) = _
      rw [hs.1]
      exact physical_normalized_debt (A p) (G p) (hApos p).ne' (d p)
    · intro x hx
      exact mul_pos (hApos p) (hs.2.2.2 x hx)
  · intro p hp
    have hcp : ‖c p‖ ≤ C * D * ‖d p‖ := by
      calc
        _ ≤ C * ‖f p‖ := (hgeq (f p) (hSV hp)).2.1
        _ ≤ C * (D * ‖d p‖) := mul_le_mul_of_nonneg_left (hnorm p hp (d p)) hC.le
        _ = _ := by ring
    refine ⟨hcp.trans (mul_le_mul_of_nonneg_right hKC (norm_nonneg _)), ?_⟩
    intro k hk x
    have hu := (hjets k hk (c p) x).1
    have he := (hjets k hk (c p) x).2
    have hbound : |A p| * (J * ‖c p‖) ≤ K * ‖d p‖ := by
      calc
        _ ≤ L * (J * ‖c p‖) := mul_le_mul_of_nonneg_right (hAbound p hp) (by positivity)
        _ ≤ L * (J * (C * D * ‖d p‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcp hJ.le) hL.le
        _ = (L * J * (C * D)) * ‖d p‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hKJ (norm_nonneg _)
    constructor
    · unfold u
      rw [iteratedDeriv_const_mul _ ((correction_contDiff P.leftHalf (c p).1).of_le
        (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt, abs_mul]
      exact (mul_le_mul_of_nonneg_left hu (abs_nonneg _)).trans hbound
    · unfold e
      rw [iteratedDeriv_const_mul _ ((correction_contDiff P.rightHalf (c p).2).of_le
        (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt, abs_mul]
      exact (mul_le_mul_of_nonneg_left he (abs_nonneg _)).trans hbound

theorem smooth_solver_jet_bound {g : Coeff → Coeff} {r : ℝ} (hr : 0 < r)
    (hg : ContDiffOn ℝ ∞ g (Metric.ball 0 r)) (N : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ k ≤ N, ∀ z ∈ Metric.closedBall (0 : Coeff) (r / 2),
      ‖iteratedFDeriv ℝ k g z‖ ≤ B := by
  have hsub : Metric.closedBall (0 : Coeff) (r / 2) ⊆ Metric.ball 0 r :=
    Metric.closedBall_subset_ball (by linarith)
  have hsingle : ∀ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ z ∈ Metric.closedBall (0 : Coeff) (r / 2), ‖iteratedFDeriv ℝ k g z‖ ≤ B := by
    intro k
    have hc := hg.continuousOn_iteratedFDerivWithin (m := k)
      (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)) Metric.isOpen_ball.uniqueDiffOn
    have he : ContinuousOn (iteratedFDeriv ℝ k g) (Metric.closedBall (0 : Coeff) (r / 2)) := by
      apply (hc.mono hsub).congr
      intro z hz
      exact (iteratedFDerivWithin_of_isOpen k Metric.isOpen_ball (hsub hz)).symm
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Coeff) (r / 2)).exists_bound_of_continuousOn he
    exact ⟨max B 0, le_max_right _ _, fun z hz => (hB z hz).trans (le_max_left _ _)⟩
  choose B hB hbound using hsingle
  refine ⟨1 + ∑ k ∈ Finset.range (N + 1), B k, ?_, ?_⟩
  · have hs := Finset.sum_nonneg (s := Finset.range (N + 1)) (fun k _ => hB k)
    linarith
  · intro k hk z hz
    have hs := Finset.single_le_sum (fun j _ => hB j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    exact (hbound k z hz).trans (by linarith)

/-- Genuine higher parameter jets of the nonlinear branch are small when
the corresponding normalized-debt jets are small. The stronger input scale
`tau^(N+1)` gives a simple uniform linear output scale for every order `≤N`.
No derivatives of the solution are supplied as hypotheses. -/
theorem smooth_solver_parameter_jets {g : Coeff → Coeff} {r C : ℝ}
    (hr : 0 < r) (hC : 0 < C) (hg : ContDiffOn ℝ ∞ g (Metric.ball 0 r))
    (hvalue : ∀ z ∈ Metric.ball (0 : Coeff) r, ‖g z‖ ≤ C * ‖z‖) (N : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℝ → Coeff), ContDiff ℝ ∞ f →
      ∀ (tau x : ℝ), 0 < tau → tau ≤ min 1 (r / 2) →
        (∀ j ≤ N, ‖iteratedFDeriv ℝ j f x‖ ≤ tau ^ (N + 1)) →
        ∀ k ≤ N, ‖iteratedFDeriv ℝ k (g ∘ f) x‖ ≤ K * tau := by
  obtain ⟨B, hB, hgb⟩ := smooth_solver_jet_bound hr hg N
  let K : ℝ := C + (N.factorial : ℝ) * B
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro f hf tau x htau hmax hfj k hk
  have ht1 : tau ≤ 1 := hmax.trans (min_le_left _ _)
  have htr : tau ≤ r / 2 := hmax.trans (min_le_right _ _)
  have hpow : tau ^ (N + 1) ≤ tau := by
    simpa only [pow_one] using pow_le_pow_of_le_one htau.le ht1 (show 1 ≤ N + 1 by omega)
  have hfx : ‖f x‖ ≤ tau := by
    simpa only [norm_iteratedFDeriv_zero] using (hfj 0 (Nat.zero_le N)).trans hpow
  have hxclosed : f x ∈ Metric.closedBall (0 : Coeff) (r / 2) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hfx.trans htr
  have hxball : f x ∈ Metric.ball (0 : Coeff) r := by
    simpa only [Metric.mem_ball, dist_zero_right] using hfx.trans_lt (lt_of_le_of_lt htr (by
        linarith))
  by_cases hk0 : k = 0
  · subst k
    rw [norm_iteratedFDeriv_zero]
    exact ((hvalue _ hxball).trans (mul_le_mul_of_nonneg_left hfx hC.le)).trans
      (mul_le_mul_of_nonneg_right (by
          dsimp [K]; exact le_add_of_nonneg_right (by positivity)) htau.le)
  let V : Set ℝ := f ⁻¹' Metric.ball (0 : Coeff) r
  have hV : IsOpen V := Metric.isOpen_ball.preimage hf.continuous
  have hxV : x ∈ V := hxball
  have hchain := norm_iteratedFDerivWithin_comp_le hg hf.contDiffOn
    (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)) Metric.isOpen_ball.uniqueDiffOn hV.uniqueDiffOn
    (show MapsTo f V (Metric.ball 0 r) from fun _ hy => hy) hxV (C := B) (D := tau)
    (fun j hj => ?_) (fun j hj hjk => ?_)
  · rw [iteratedFDerivWithin_of_isOpen k hV hxV] at hchain
    have hfac : (k.factorial : ℝ) * B ≤ (N.factorial : ℝ) * B :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hk) hB.le
    have hp : tau ^ k ≤ tau := by
      simpa only [pow_one] using pow_le_pow_of_le_one htau.le ht1 (show 1 ≤ k by omega)
    exact (hchain.trans (mul_le_mul hfac hp (pow_nonneg htau.le k) (by positivity))).trans
      (mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) htau.le)
  · rw [iteratedFDerivWithin_of_isOpen j Metric.isOpen_ball hxball]
    exact hgb j (hj.trans hk) _ hxclosed
  · rw [iteratedFDerivWithin_of_isOpen j hV hxV]
    exact (hfj j (hjk.trans hk)).trans
      (pow_le_pow_of_le_one htau.le ht1 (by omega : j ≤ N + 1))

/-- Jet eval, constructed using `LinearMap.toContinuousLinearMap`. -/
noncomputable def jetEval {n : ℕ} (P : Patch) (k : ℕ) (x : ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => ∑ i, c i * iteratedDeriv k (bump P i) x
      map_add' := fun c d => by simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r c => by simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc] }

/-- U jet eval, given by `(jetEval P.leftHalf k x).comp (ContinuousLinearMap.fst ℝ _ _)`. -/
noncomputable def uJetEval (P : Patch) (k : ℕ) (x : ℝ) : Coeff →L[ℝ] ℝ :=
  (jetEval P.leftHalf k x).comp (ContinuousLinearMap.fst ℝ _ _)

/-- E jet eval, given by `(jetEval P.rightHalf k x).comp (ContinuousLinearMap.snd ℝ _ _)`. -/
noncomputable def eJetEval (P : Patch) (k : ℕ) (x : ℝ) : Coeff →L[ℝ] ℝ :=
  (jetEval P.rightHalf k x).comp (ContinuousLinearMap.snd ℝ _ _)

theorem uJetEval_apply (P : Patch) (k : ℕ) (x : ℝ) (c : Coeff) :
    uJetEval P k x c = iteratedDeriv k (u P c) x :=
  (correction_iteratedDeriv P.leftHalf c.1 k x).symm

theorem eJetEval_apply (P : Patch) (k : ℕ) (x : ℝ) (c : Coeff) :
    eJetEval P k x c = iteratedDeriv k (e P c) x :=
  (correction_iteratedDeriv P.rightHalf c.2 k x).symm

theorem linear_parameter_jet_bound (L : Coeff →L[ℝ] ℝ) {v : ℝ → Coeff} {eta : ℝ}
    (hv : ContDiffAt ℝ ∞ v eta) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (L ∘ v) eta‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ m v eta‖ := by
  rw [L.iteratedFDeriv_comp_left hv (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))]
  exact L.norm_compContinuousMultilinearMap_le _

/-- Every mixed parameter/radial jet of the actual fixed bump family is
controlled by the corresponding parameter jet of its coefficients. -/
theorem mixed_jet_bound (P : Patch) (N : ℕ) :
    ∃ J : ℝ, 0 < J ∧ ∀ k ≤ N, ∀ (m : ℕ) (v : ℝ → Coeff) (eta : ℝ),
      ContDiffAt ℝ ∞ v eta → ∀ x : ℝ,
        ‖iteratedFDeriv ℝ m (fun p => iteratedDeriv k (u P (v p)) x) eta‖ ≤
          J * ‖iteratedFDeriv ℝ m v eta‖ ∧
        ‖iteratedFDeriv ℝ m (fun p => iteratedDeriv k (e P (v p)) x) eta‖ ≤
          J * ‖iteratedFDeriv ℝ m v eta‖ := by
  obtain ⟨J, hJ, hjets⟩ := finite_spatial_jet_bound P N
  refine ⟨J, hJ, ?_⟩
  intro k hk m v eta hv x
  have hU : ‖uJetEval P k x‖ ≤ J := by
    apply ContinuousLinearMap.opNorm_le_bound _ hJ.le
    intro c
    simpa only [uJetEval_apply, Real.norm_eq_abs] using (hjets k hk c x).1
  have hE : ‖eJetEval P k x‖ ≤ J := by
    apply ContinuousLinearMap.opNorm_le_bound _ hJ.le
    intro c
    simpa only [eJetEval_apply, Real.norm_eq_abs] using (hjets k hk c x).2
  have heU : (fun p => iteratedDeriv k (u P (v p)) x) = uJetEval P k x ∘ v :=
    funext (fun p => (uJetEval_apply P k x (v p)).symm)
  have heE : (fun p => iteratedDeriv k (e P (v p)) x) = eJetEval P k x ∘ v :=
    funext (fun p => (eJetEval_apply P k x (v p)).symm)
  rw [heU, heE]
  exact ⟨(linear_parameter_jet_bound _ hv m).trans (mul_le_mul_of_nonneg_right hU (norm_nonneg _)),
    (linear_parameter_jet_bound _ hv m).trans (mul_le_mul_of_nonneg_right hE (norm_nonneg _))⟩

/-- Full mixed jets of both physical edits tend to zero with finite jets of
the normalized debt. Bounds on the fixed smooth amplitude are kept explicit.
This applies directly to the solver constructed in `exists_normalized_repair`. -/
theorem physical_mixed_jets_small (P : Patch) {g : Coeff → Coeff} {r C : ℝ}
    (hr : 0 < r) (hC : 0 < C) (hg : ContDiffOn ℝ ∞ g (Metric.ball 0 r))
    (hvalue : ∀ z ∈ Metric.ball (0 : Coeff) r, ‖g z‖ ≤ C * ‖z‖) (N : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (V : Set ℝ), IsOpen V → ∀ (f : ℝ → Coeff) (A : ℝ → ℝ),
      ContDiff ℝ ∞ f → ContDiffOn ℝ ∞ A V → ∀ B tau : ℝ,
      0 ≤ B → 0 < tau → tau ≤ min 1 (r / 2) →
      JetBounds.FiniteJetBound N A V B →
      JetBounds.FiniteJetBound N f V (tau ^ (N + 1)) →
      ∀ eta ∈ V, ∀ k ≤ N, ∀ m ≤ N, ∀ x : ℝ,
        ‖iteratedFDeriv ℝ m (fun p => iteratedDeriv k (fun y => A p * u P (g (f p)) y) x) eta‖ ≤ K
            * B * tau ∧
        ‖iteratedFDeriv ℝ m (fun p => iteratedDeriv k (fun y => A p * e P (g (f p)) y) x) eta‖ ≤ K
            * B * tau := by
  obtain ⟨J, hJ, hjets⟩ := mixed_jet_bound P N
  obtain ⟨D, hD, hparam⟩ := smooth_solver_parameter_jets hr hC hg hvalue N
  let L : ℝ →L[ℝ] Coeff →L[ℝ] Coeff := ContinuousLinearMap.lsmul ℝ ℝ
  let K : ℝ := J * (‖L‖ + 1) * (2 : ℝ) ^ N * D
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro V hV f A hf hA B tau hB htau hmax hAb hfb eta heta k hk m hm x
  have hmap : MapsTo f V (Metric.ball (0 : Coeff) r) := by
    intro p hp
    have hz := hfb 0 (Nat.zero_le N) p hp
    rw [norm_iteratedFDeriv_zero] at hz
    have ht1 := hmax.trans (min_le_left _ _)
    have htr := hmax.trans (min_le_right _ _)
    have hpow : tau ^ (N + 1) ≤ tau := by
      simpa only [pow_one] using pow_le_pow_of_le_one htau.le ht1 (show 1 ≤ N + 1 by omega)
    simpa only [Metric.mem_ball, dist_zero_right] using
      (hz.trans hpow).trans_lt (lt_of_le_of_lt htr (by linarith : r / 2 < r))
  let c : ℝ → Coeff := g ∘ f
  have hc : ContDiffOn ℝ ∞ c V := hg.comp hf.contDiffOn hmap
  have hcb : JetBounds.FiniteJetBound N c V (D * tau) := by
    intro j hj p hp
    exact hparam f hf tau p htau hmax (fun i hi => hfb i hi p hp) j hj
  let v : ℝ → Coeff := fun p => A p • c p
  have hv : ContDiffOn ℝ ∞ v V := hA.smul hc
  have hvb : JetBounds.FiniteJetBound N v V (‖L‖ * (2 : ℝ) ^ N * B * (D * tau)) :=
    JetBounds.FiniteJetBound.bilinear L hV
      (hA.of_le (by exact_mod_cast (le_top : (N : ℕ∞) ≤ ⊤)))
      (hc.of_le (by exact_mod_cast (le_top : (N : ℕ∞) ≤ ⊤))) hAb hcb
  have hcost : J * (‖L‖ * (2 : ℝ) ^ N * B * (D * tau)) ≤ K * B * tau := by
    dsimp [K]
    linarith [show 0 ≤ J * (2 : ℝ) ^ N * B * D * tau by positivity]
  have huFun : (fun p => iteratedDeriv k (fun y => A p * u P (g (f p)) y) x) =
      fun p => iteratedDeriv k (u P (v p)) x := by
    funext p
    congr 1
    funext y
    simp [v, c, u, correction, Pi.smul_apply, smul_eq_mul, mul_assoc]
    ring
  have heFun : (fun p => iteratedDeriv k (fun y => A p * e P (g (f p)) y) x) =
      fun p => iteratedDeriv k (e P (v p)) x := by
    funext p
    congr 1
    funext y
    simp [v, c, e, correction, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [huFun, heFun]
  have hjet := hjets k hk m v eta (hv.contDiffAt (hV.mem_nhds heta)) x
  exact ⟨hjet.1.trans ((mul_le_mul_of_nonneg_left (hvb m hm eta heta) hJ.le).trans hcost),
    hjet.2.trans ((mul_le_mul_of_nonneg_left (hvb m hm eta heta) hJ.le).trans hcost)⟩

theorem u_tsupport_patch (P : Patch) (c : Coeff) : tsupport (u P c) ⊆ Ioo P.left P.right := by
  intro x hx
  have hs := correction_tsupport P.leftHalf c.1 hx
  have hm : P.leftHalf.right < P.right := by dsimp [Patch.leftHalf, Patch.mid]; linarith [P.ordered]
  exact ⟨hs.1, hs.2.trans hm⟩

theorem e_tsupport_patch (P : Patch) (c : Coeff) : tsupport (e P c) ⊆ Ioo P.left P.right := by
  intro x hx
  have hs := correction_tsupport P.rightHalf c.2 hx
  have hm : P.left < P.rightHalf.left := by dsimp [Patch.rightHalf, Patch.mid]; linarith [P.ordered]
  exact ⟨hm.trans hs.1, hs.2⟩

theorem u_zero_outside (P : Patch) (c : Coeff) {x : ℝ} (hx : x ∉ Ioo P.left P.right) : u P c x = 0
    :=
  Classical.byContradiction (fun hn => hx (u_tsupport_patch P c (subset_tsupport _ hn)))

theorem e_zero_outside (P : Patch) (c : Coeff) {x : ℝ} (hx : x ∉ Ioo P.left P.right) : e P c x = 0
    :=
  Classical.byContradiction (fun hn => hx (e_tsupport_patch P c (subset_tsupport _ hn)))

theorem physical_profiles_unchanged (P : Patch) (b A G : ℝ) (c : Coeff) {x : ℝ}
    (hx : x ∉ Ioo P.left P.right) : physicalU P A G c x = G ∧ physicalE P b A c x = A * x ^ b := by
  simp [physicalU, physicalE, u_zero_outside P c hx, e_zero_outside P c hx]

theorem physical_edits_tsupport (P : Patch) (A : ℝ) (c : Coeff) :
    tsupport (fun x => A * u P c x) ⊆ Ioo P.left P.right ∧
    tsupport (fun x => A * e P c x) ⊆ Ioo P.left P.right := by
  constructor
  · apply Set.Subset.trans _ (u_tsupport_patch P c)
    apply closure_mono
    intro x hx hu
    exact hx (by simp [hu])
  · apply Set.Subset.trans _ (e_tsupport_patch P c)
    apply closure_mono
    intro x hx he
    exact hx (by simp [he])

/-- Profile change density as an element of `Debt`. -/
noncomputable def profileChangeDensity (U E dU dE : ℝ → ℝ) (x : ℝ) : Debt :=
  ![(U x + dU x) - U x,
    Real.sqrt (2 * x) * ((E x + dE x) - E x),
    (U x + dU x) * Real.sqrt (2 * x) * (E x + dE x) - U x * Real.sqrt (2 * x) * E x,
    ((U x + dU x) ^ 2 - (E x + dE x) ^ 2 / 2) - ((U x) ^ 2 - (E x) ^ 2 / 2),
    ((E x + dE x) ^ 2 - (E x) ^ 2) / (2 * x)]

/-- Only agreement with the power background on the reserved patch is needed;
the profiles outside the patch are arbitrary and are preserved exactly. -/
theorem local_profile_change (P : Patch) (b A G : ℝ) (c : Coeff) (U E : ℝ → ℝ)
    (hU : ∀ x ∈ Ioo P.left P.right, U x = G)
    (hE : ∀ x ∈ Ioo P.left P.right, E x = A * x ^ b) (x : ℝ) :
    profileChangeDensity U E (fun y => A * u P c y) (fun y => A * e P c y) x =
      physicalDensity P b A G c x := by
  by_cases hx : x ∈ Ioo P.left P.right
  · simp only [profileChangeDensity, physicalDensity, physicalU, physicalE,
      hU x hx, hE x hx, mul_add]
  · rw [physicalDensity_zero_outside P b A G c hx]
    ext i
    fin_cases i <;> simp [profileChangeDensity, u_zero_outside P c hx, e_zero_outside P c hx]

theorem local_profile_moments (P : Patch) (b A G : ℝ) (c : Coeff) (U E : ℝ → ℝ)
    (hU : ∀ x ∈ Ioo P.left P.right, U x = G)
    (hE : ∀ x ∈ Ioo P.left P.right, E x = A * x ^ b) (i : Fin 5) :
    (∫ x in Ioi (0 : ℝ), profileChangeDensity U E (fun y => A * u P c y) (fun y => A * e P c y) x
        i) =
      physicalMoments P b A G c i := by
  simp_rw [local_profile_change P b A G c U E hU hE]
  exact physicalMoments_positive_axis P b A G c i

/-- Normalization continuous linear map, given by `∑ i : Fin 5, ContinuousLinearMap.smulRightL ℝ
Debt Coeff (ContinuousLinearMap.proj i) (normalizedDebt A G (Pi.single i 1))`. -/
noncomputable def normalizationCLM (A G : ℝ) : Debt →L[ℝ] Coeff :=
  ∑ i : Fin 5, ContinuousLinearMap.smulRightL ℝ Debt Coeff
    (ContinuousLinearMap.proj i) (normalizedDebt A G (Pi.single i 1))

theorem normalizationCLM_apply (A G : ℝ) (d : Debt) : normalizationCLM A G d = normalizedDebt A G d
    := by
  rw [normalizedDebt_eq_sum]
  rfl

theorem normalizationCLM_contDiff {A G : ℝ → ℝ}
    (hA : ContDiff ℝ ∞ A) (hG : ContDiff ℝ ∞ G) (hAn : ∀ p, A p ≠ 0) :
    ContDiff ℝ ∞ (fun p => normalizationCLM (A p) (G p)) := by
  apply ContDiff.sum
  intro i _
  exact (ContinuousLinearMap.smulRightL ℝ Debt Coeff (ContinuousLinearMap.proj i)).contDiff.comp
    (normalizedDebt_contDiff hA hG contDiff_const hAn)

theorem compact_global_jet_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : Set ℝ) (hS : IsCompact S) {f : ℝ → F} (hf : ContDiff ℝ ∞ f) (N : ℕ) :
    ∃ K : ℝ, 0 < K ∧ JetBounds.FiniteJetBound N f S K := by
  have hb : ∀ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ S, ‖iteratedFDeriv ℝ j f p‖ ≤ B := by
    intro j
    obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn
      (hf.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).continuousOn
    exact ⟨max B 0, le_max_right _ _, fun p hp => (hB p hp).trans (le_max_left _ _)⟩
  choose B hB hbound using hb
  refine ⟨1 + ∑ j ∈ Finset.range (N + 1), B j, ?_, ?_⟩
  · have hs := Finset.sum_nonneg (s := Finset.range (N + 1)) (fun j _ => hB j)
    linarith
  · intro j hj p hp
    have hsum := Finset.single_le_sum (fun j _ => hB j) (Finset.mem_range.mpr (Nat.lt_succ_of_le
        hj))
    exact (hbound j p hp).trans (by linarith)

/-- The fixed smooth weights in the normalization preserve smallness of every
finite parameter jet. This bridges physical row estimates to the nonlinear
solver's normalized-debt estimates. -/
theorem compact_normalizedDebt_jets (S : Set ℝ) (hS : IsCompact S) {A G : ℝ → ℝ}
    (hA : ContDiff ℝ ∞ A) (hG : ContDiff ℝ ∞ G) (hAn : ∀ p, A p ≠ 0) (N : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ d : ℝ → Debt, ContDiff ℝ ∞ d → ∀ D : ℝ, 0 ≤ D →
      JetBounds.FiniteJetBound N d S D →
      JetBounds.FiniteJetBound N (fun p => normalizedDebt (A p) (G p) (d p)) S (K * D) := by
  have hF := normalizationCLM_contDiff hA hG hAn
  obtain ⟨B, hB, hFb⟩ := compact_global_jet_bound S hS hF N
  refine ⟨(2 : ℝ) ^ N * B, by positivity, ?_⟩
  intro d hd D hD hdb n hn p hp
  have heq : (fun p => normalizedDebt (A p) (G p) (d p)) =
      fun p => normalizationCLM (A p) (G p) (d p) :=
    funext (fun p => (normalizationCLM_apply (A p) (G p) (d p)).symm)
  rw [heq]
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun p => normalizationCLM (A p) (G p)) p‖ *
          ‖iteratedFDeriv ℝ (n - i) d p‖ :=
      norm_iteratedFDeriv_clm_apply hF hd p (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * B * D := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hFb i (hin.trans hn) p hp) (Nat.cast_nonneg _))
        (hdb (n - i) ((Nat.sub_le _ _).trans hn) p hp) (norm_nonneg _) (by positivity)
    _ = (2 : ℝ) ^ n * B * D := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose n
    _ ≤ ((2 : ℝ) ^ N * B) * D :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) hn) hB.le) hD

end NavierStokes.FiveProfileMoments
