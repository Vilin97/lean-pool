/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.MetricCodes.Rates
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Harmonic analysis for spherical codes

Harmonic polynomial, Gegenbauer, Perron, and adjacent-channel constructions.
-/

noncomputable section MetricCodesNoncomputable

section

open scoped BigOperators InnerProductSpace

namespace MetricCodes

/-- The sphere used in the metric-code argument. -/
abbrev Sphere (n : ℕ) := {x : Ambient n // ‖x‖ = 1}

/-- The spherical inner used in the metric-code argument. -/
def sphericalInner {n : ℕ} (x y : Sphere n) : ℝ :=
  ⟪(x : Ambient n), (y : Ambient n)⟫_ℝ

theorem spherical_dist_sq {n : ℕ} (x y : Sphere n) :
    ‖(x : Ambient n) - (y : Ambient n)‖ ^ 2 =
      2 * (1 - sphericalInner x y) := by
  rw [norm_sub_sq_real]
  simp only [x.property, one_pow, y.property, sphericalInner]
  ring

/-- The predicate asserting spherical code. -/
def IsSphericalCode {n : ℕ} (s : ℝ) (C : Finset (Sphere n)) : Prop :=
  ∀ ⦃x⦄, x ∈ C → ∀ ⦃y⦄, y ∈ C → x ≠ y → sphericalInner x y ≤ s

/-- Data encoding the spherical code construction. -/
structure SphericalCode (n : ℕ) (s : ℝ) where
  /-- The points component. -/
  points : Finset (Sphere n)
  inner_le : IsSphericalCode s points

/-- The spherical code number used in the metric-code argument. -/
def sphericalCodeNumber (n : ℕ) (s : ℝ) : ℕ∞ :=
  ⨆ C : SphericalCode n s, (C.points.card : ℕ∞)

theorem sphericalCodeNumber_le {n : ℕ} {s : ℝ} {B : ℕ∞}
    (hB : ∀ C : SphericalCode n s, (C.points.card : ℕ∞) ≤ B) :
    sphericalCodeNumber n s ≤ B := by
  exact iSup_le hB

theorem sphericalCodeNumber_lt_top {n : ℕ} {s : ℝ}
    (hs : s < 1) : sphericalCodeNumber n s < ⊤ := by
  let ε : NNReal :=
    ⟨Real.sqrt (2 * (1 - s)) / 4, by positivity⟩
  have hε : ε ≠ 0 := by
    apply NNReal.ne_iff.mp
    change Real.sqrt (2 * (1 - s)) / 4 ≠ 0
    positivity
  let S : Set (Ambient n) := Metric.sphere (0 : Ambient n) 1
  have hS : IsCompact S := isCompact_sphere (0 : Ambient n) 1
  obtain ⟨N, hNS, hNfin, hcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact hε hS
  have hpacking : Metric.packingNumber (2 * ε) S ≤ N.encard :=
    (Metric.packingNumber_two_mul_le_externalCoveringNumber ε S).trans
      hcover.externalCoveringNumber_le_encard
  have hbound : sphericalCodeNumber n s ≤ N.encard := by
    apply sphericalCodeNumber_le
    intro C
    let F : Finset (Ambient n) :=
      C.points.map (Function.Embedding.subtype (fun x : Ambient n => ‖x‖ = 1))
    have hFS : (↑F : Set (Ambient n)) ⊆ S := by
      intro x hx
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
      simpa [S, Metric.mem_sphere] using u.property
    have hFsep : Metric.IsSeparated (2 * ε) (↑F : Set (Ambient n)) := by
      intro x hx y hy hxy
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hy
      have huv : u ≠ v := fun huv => hxy (congrArg Subtype.val huv)
      have hinner : sphericalInner u v ≤ s := C.inner_le hu hv huv
      have hsq : 2 * (1 - s) ≤ dist (u : Ambient n) (v : Ambient n) ^ 2 := by
        rw [dist_eq_norm, spherical_dist_sq]
        nlinarith
      have hsqrt : 0 < Real.sqrt (2 * (1 - s)) := by
        positivity
      have hsqrt_sq : Real.sqrt (2 * (1 - s)) ^ 2 = 2 * (1 - s) :=
        Real.sq_sqrt (by nlinarith)
      have hreal : ((2 * ε : NNReal) : ℝ) <
          dist (u : Ambient n) (v : Ambient n) := by
        change 2 * (Real.sqrt (2 * (1 - s)) / 4) <
          dist (u : Ambient n) (v : Ambient n)
        nlinarith [show 0 ≤ dist (u : Ambient n) (v : Ambient n) from dist_nonneg]
      calc
        (↑(2 * ε) : ENNReal) =
            ENNReal.ofReal (((2 * ε : NNReal) : ℝ)) :=
          ENNReal.coe_nnreal_eq _
        _ < ENNReal.ofReal (dist (u : Ambient n) (v : Ambient n)) :=
          (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).2 hreal
        _ = edist (u : Ambient n) (v : Ambient n) :=
          (edist_dist _ _).symm
    calc
      (C.points.card : ℕ∞) = (↑F : Set (Ambient n)).encard := by
        rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_map]
      _ ≤ Metric.packingNumber (2 * ε) S :=
        hFsep.encard_le_packingNumber hFS
      _ ≤ N.encard := hpacking
  exact lt_of_le_of_lt hbound hNfin.encard_lt_top

theorem exists_maximal_sphericalCode {n : ℕ} {s : ℝ}
    (hs : s < 1) :
    ∃ C : SphericalCode n s,
      (C.points.card : ℕ∞) = sphericalCodeNumber n s := by
  let emptyCode : SphericalCode n s :=
    { points := ∅, inner_le := by simp only [IsSphericalCode, Finset.notMem_empty, ne_eq,
                                    IsEmpty.forall_iff, implies_true]}
  let : Nonempty (SphericalCode n s) := ⟨emptyCode⟩
  apply ENat.exists_eq_iSup_of_lt_top
  exact sphericalCodeNumber_lt_top hs

theorem sphericalEntropy_pos {u : ℝ} (hu : 0 < u) :
    0 < sphericalEntropy u := by
  rw [sphericalEntropy_eq_log_add hu]
  have hfirst : 0 < Real.logb 2 (1 + u) :=
    Real.logb_pos (by norm_num : (1 : ℝ) < 2) (by linarith)
  have hratio : 1 < (1 + u) / u := by
    apply (lt_div_iff₀ hu).2
    linarith
  have hsecond : 0 < Real.logb 2 ((1 + u) / u) :=
    Real.logb_pos (by norm_num : (1 : ℝ) < 2) hratio
  nlinarith

theorem Gamma_pos {a b : ℝ} (hb : 0 ≤ b) (hab : b < a) :
    0 < Gamma a b := by
  have ha : 0 < a := lt_of_le_of_lt hb hab
  unfold Gamma
  apply div_pos
  · exact mul_pos (sub_pos.mpr hab) (by linarith)
  · exact mul_pos (by linarith)
      (Real.sqrt_pos.2 (mul_pos ha (by linarith)))

/-- The harmonic dimension used in the metric-code argument. -/
def harmonicDimension (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 =>
      (n + i - 1).choose (i + 1) + (n + i - 2).choose i

@[simp] theorem harmonicDimension_zero (n : ℕ) :
    harmonicDimension n 0 = 1 := rfl

end MetricCodes

end

namespace SpherePacking

section


open scoped BigOperators InnerProductSpace

/-- Data encoding the spherical code construction. -/
structure SphericalCode (n : ℕ) (s : ℝ) where
  /-- The points component. -/
  points : Finset (Euclidean n)
  unit_norm : ∀ x ∈ points, ‖x‖ = 1
  inner_le : ∀ x ∈ points, ∀ y ∈ points, x ≠ y →
    ⟪x, y⟫_ℝ ≤ s

private def PositiveDefiniteKernel {α : Type*} (K : α → α → ℝ) : Prop :=
  ∀ (C : Finset α) (w : α → ℝ),
    0 ≤ ∑ x ∈ C, ∑ y ∈ C, w x * w y * K x y

private def unitSphere (n : ℕ) : Set (Euclidean n) :=
  {x | ‖x‖ = 1}

theorem weighted_gram_sum_eq_norm_sq {α E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : Finset α) (w : α → ℝ) (v : α → E) :
    (∑ x ∈ C, ∑ y ∈ C, w x * w y * ⟪v x, v y⟫_ℝ) =
      ‖∑ x ∈ C, w x • v x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [real_inner_comm (v x) (v y), mul_assoc]

theorem weighted_gram_sum_nonnegative {α E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : Finset α) (w : α → ℝ) (v : α → E) :
    0 ≤ ∑ x ∈ C, ∑ y ∈ C, w x * w y * ⟪v x, v y⟫_ℝ := by
  rw [weighted_gram_sum_eq_norm_sq]
  exact sq_nonneg _

theorem positiveDefiniteKernel_of_features {α E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : α → E) :
    PositiveDefiniteKernel (fun x y => ⟪v x, v y⟫_ℝ) := by
  intro C w
  exact weighted_gram_sum_nonnegative C w v

theorem positiveDefiniteKernel_finset_sum {α ι : Type*}
    (I : Finset ι) (K : ι → α → α → ℝ)
    (hK : ∀ i ∈ I, PositiveDefiniteKernel (K i)) :
    PositiveDefiniteKernel (fun x y => ∑ i ∈ I, K i x y) := by
  intro C w
  calc
    0 ≤ ∑ i ∈ I, ∑ x ∈ C, ∑ y ∈ C,
        w x * w y * K i x y := by
      exact Finset.sum_nonneg fun i hi => hK i hi C w
    _ = ∑ x ∈ C, ∑ i ∈ I, ∑ y ∈ C,
        w x * w y * K i x y := by
      rw [Finset.sum_comm]
    _ = ∑ x ∈ C, ∑ y ∈ C, ∑ i ∈ I,
        w x * w y * K i x y := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
    _ = ∑ x ∈ C, ∑ y ∈ C,
        w x * w y * (∑ i ∈ I, K i x y) := by
      simp_rw [Finset.mul_sum]

theorem finite_linear_programming_bound {α : Type*}
    (C : Finset α) (f : α → α → ℝ) {c B : ℝ}
    (hc : 0 < c) (hB : 0 ≤ B)
    (hdiag : ∀ x ∈ C, f x x ≤ B)
    (hoff : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → f x y ≤ 0)
    (hpositive : (C.card : ℝ) ^ 2 * c ≤
      ∑ x ∈ C, ∑ y ∈ C, f x y) :
    (C.card : ℝ) ≤ B / c := by
  classical
  have hsum :
      (∑ x ∈ C, ∑ y ∈ C, f x y) ≤ (C.card : ℝ) * B := by
    calc
      (∑ x ∈ C, ∑ y ∈ C, f x y) ≤
          ∑ x ∈ C, ∑ y ∈ C, if x = y then B else 0 := by
            exact Finset.sum_le_sum fun x hx =>
              Finset.sum_le_sum fun y hy => by
                split_ifs with hxy
                · subst y
                  exact hdiag x hx
                · exact hoff x hx y hy hxy
      _ = (C.card : ℝ) * B := by
        simp only [Finset.sum_ite_eq, Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const,
          nsmul_eq_mul]
  by_cases hC : C.card = 0
  · rw [hC]
    norm_num
    exact div_nonneg hB hc.le
  · have hcard : 0 < (C.card : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hC
    apply (le_div_iff₀ hc).2
    nlinarith [hpositive, hsum]

/-- The polynomial laplacian used in the spherical-code argument. -/
def polynomialLaplacian (n : ℕ) :
    MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ :=
  ∑ i : Fin n,
    (MvPolynomial.pderiv i).toLinearMap.comp
      (MvPolynomial.pderiv i).toLinearMap

@[simp] theorem polynomialLaplacian_apply (n : ℕ)
    (p : MvPolynomial (Fin n) ℝ) :
    polynomialLaplacian n p =
      ∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i p) := by
  simp only [polynomialLaplacian, LinearMap.coe_sum, LinearMap.coe_comp, Derivation.coeFn_coe,
    Finset.sum_apply, Function.comp_apply]

/-- The harmonic homogeneous submodule used in the spherical-code argument. -/
def harmonicHomogeneousSubmodule (n k : ℕ) :
    Submodule ℝ (MvPolynomial (Fin n) ℝ) :=
  MvPolynomial.homogeneousSubmodule (Fin n) ℝ k ⊓
    LinearMap.ker (polynomialLaplacian n)

@[simp] theorem mem_harmonicHomogeneousSubmodule
    {n k : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    p ∈ harmonicHomogeneousSubmodule n k ↔
      p.IsHomogeneous k ∧
        ∑ i : Fin n,
          MvPolynomial.pderiv i (MvPolynomial.pderiv i p) = 0 := by
  simp only [harmonicHomogeneousSubmodule, Submodule.mem_inf, MvPolynomial.mem_homogeneousSubmodule,
    LinearMap.mem_ker, polynomialLaplacian_apply]

theorem harmonicPolynomial_euler {n k : ℕ}
    (p : harmonicHomogeneousSubmodule n k) :
    (∑ i : Fin n,
      MvPolynomial.X i * MvPolynomial.pderiv i
        (p : MvPolynomial (Fin n) ℝ)) =
      k • (p : MvPolynomial (Fin n) ℝ) := by
  apply MvPolynomial.IsHomogeneous.sum_X_mul_pderiv
  exact (mem_harmonicHomogeneousSubmodule (p : MvPolynomial (Fin n) ℝ)).mp
    p.property |>.1

private def finiteHilbertSchmidtKernel {α ι F E : Type*}
    [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis ι ℝ F)
    (A : α → F →ₗ[ℝ] E) (x y : α) : ℝ :=
  ∑ i : ι, ⟪A x (b i), A y (b i)⟫_ℝ

theorem finiteHilbertSchmidtKernel_positive
    {α ι F E : Type*} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis ι ℝ F)
    (A : α → F →ₗ[ℝ] E) :
    PositiveDefiniteKernel (finiteHilbertSchmidtKernel b A) := by
  classical
  unfold finiteHilbertSchmidtKernel
  apply positiveDefiniteKernel_finset_sum Finset.univ
    (fun i x y => ⟪A x (b i), A y (b i)⟫_ℝ)
  intro i hi
  exact positiveDefiniteKernel_of_features (fun x => A x (b i))

theorem finiteHilbertSchmidtKernel_eq_trace
    {α ι F E : Type*} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ F] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ F)
    (A : α → F →ₗ[ℝ] E) (x y : α) :
    finiteHilbertSchmidtKernel b A x y =
      ((A x).adjoint ∘ₗ A y).trace ℝ F := by
  unfold finiteHilbertSchmidtKernel
  rw [LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i hi
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right]

theorem orthogonal_three_channel_inner {α E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p m r : α → E) (a b : ℝ)
    (hpm : ∀ x y, ⟪p x, m y⟫_ℝ = 0)
    (hpr : ∀ x y, ⟪p x, r y⟫_ℝ = 0)
    (hmr : ∀ x y, ⟪m x, r y⟫_ℝ = 0)
    (x y : α) :
    ⟪a • p x + b • m x + r x,
      a • p y + b • m y + r y⟫_ℝ =
      a ^ 2 * ⟪p x, p y⟫_ℝ +
        b ^ 2 * ⟪m x, m y⟫_ℝ + ⟪r x, r y⟫_ℝ := by
  have hmp : ⟪m x, p y⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact hpm y x
  have hrp : ⟪r x, p y⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact hpr y x
  have hrm : ⟪r x, m y⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact hmr y x
  simp only [inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right,
    hpm x y, hpr x y, hmr x y, hmp, hrp, hrm,
    mul_zero, add_zero, zero_add]
  ring

theorem finiteHilbertSchmidtKernel_three_channel
    {α ι F E : Type*} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (basis : OrthonormalBasis ι ℝ F)
    (P M R : α → F →ₗ[ℝ] E) (a b : ℝ)
    (hPM : ∀ x y i, ⟪P x (basis i), M y (basis i)⟫_ℝ = 0)
    (hPR : ∀ x y i, ⟪P x (basis i), R y (basis i)⟫_ℝ = 0)
    (hMR : ∀ x y i, ⟪M x (basis i), R y (basis i)⟫_ℝ = 0)
    (x y : α) :
    finiteHilbertSchmidtKernel basis
        (fun z => a • P z + b • M z + R z) x y =
      a ^ 2 * finiteHilbertSchmidtKernel basis P x y +
        b ^ 2 * finiteHilbertSchmidtKernel basis M x y +
        finiteHilbertSchmidtKernel basis R x y := by
  unfold finiteHilbertSchmidtKernel
  calc
    (∑ i : ι,
      ⟪(a • P x + b • M x + R x) (basis i),
        (a • P y + b • M y + R y) (basis i)⟫_ℝ) =
        ∑ i : ι,
          (a ^ 2 * ⟪P x (basis i), P y (basis i)⟫_ℝ +
            b ^ 2 * ⟪M x (basis i), M y (basis i)⟫_ℝ +
            ⟪R x (basis i), R y (basis i)⟫_ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [LinearMap.add_apply, LinearMap.smul_apply] using
        orthogonal_three_channel_inner
          (fun z => P z (basis i))
          (fun z => M z (basis i))
          (fun z => R z (basis i)) a b
          (fun u v => hPM u v i)
          (fun u v => hPR u v i)
          (fun u v => hMR u v i) x y
    _ = a ^ 2 * (∑ i : ι, ⟪P x (basis i), P y (basis i)⟫_ℝ) +
        b ^ 2 * (∑ i : ι, ⟪M x (basis i), M y (basis i)⟫_ℝ) +
        (∑ i : ι, ⟪R x (basis i), R y (basis i)⟫_ℝ) := by
      simp_rw [Finset.sum_add_distrib, Finset.mul_sum]

private def mixedHilbertSchmidtKernel
    {α ι F E G : Type*} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]
    (basis : OrthonormalBasis ι ℝ G)
    (A : α → F →ₗ[ℝ] E) (B : α → F →ₗ[ℝ] G) :
    α → α → ℝ :=
  finiteHilbertSchmidtKernel basis
    (fun x => A x ∘ₗ (B x).adjoint)

end

section


open Polynomial
open scoped BigOperators

namespace Gegenbauer

private def recurrenceDenominator (n i : ℕ) : ℝ :=
  (i : ℝ) + (n : ℝ) - 2

private def forwardCoefficient (n i : ℕ) : ℝ :=
  (2 * (i : ℝ) + (n : ℝ) - 2) / recurrenceDenominator n i

private def backwardCoefficient (n i : ℕ) : ℝ :=
  (i : ℝ) / recurrenceDenominator n i

/-- The normalized used in the spherical-code argument. -/
def normalized (n : ℕ) : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => Polynomial.X
  | i + 2 =>
      Polynomial.C (forwardCoefficient n (i + 1)) * Polynomial.X *
          normalized n (i + 1) -
        Polynomial.C (backwardCoefficient n (i + 1)) * normalized n i

@[simp] theorem normalized_zero (n : ℕ) : normalized n 0 = 1 := rfl

@[simp] theorem normalized_one (n : ℕ) :
    normalized n 1 = Polynomial.X := rfl

theorem normalized_add_two (n i : ℕ) :
    normalized n (i + 2) =
      Polynomial.C (forwardCoefficient n (i + 1)) * Polynomial.X *
          normalized n (i + 1) -
        Polynomial.C (backwardCoefficient n (i + 1)) * normalized n i := rfl

theorem recurrenceDenominator_pos {n i : ℕ}
    (hn : 2 ≤ n) (hi : 0 < i) : 0 < recurrenceDenominator n i := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  unfold recurrenceDenominator
  linarith

theorem forwardCoefficient_pos {n i : ℕ}
    (hn : 2 ≤ n) (hi : 0 < i) : 0 < forwardCoefficient n i := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  unfold forwardCoefficient
  apply div_pos
  · linarith
  · exact recurrenceDenominator_pos hn hi

theorem backwardCoefficient_pos {n i : ℕ}
    (hn : 2 ≤ n) (hi : 0 < i) : 0 < backwardCoefficient n i := by
  unfold backwardCoefficient
  exact div_pos (by exact_mod_cast hi) (recurrenceDenominator_pos hn hi)

theorem normalized_eval_one {n : ℕ} (hn : 2 ≤ n) (i : ℕ) :
    (normalized n i).eval 1 = 1 := by
  induction i using Nat.twoStepInduction with
  | zero => simp only [normalized_zero, eval_one]
  | one => simp only [normalized_one, eval_X]
  | more i hi hi' =>
      have hd : recurrenceDenominator n (i + 1) ≠ 0 :=
        ne_of_gt (recurrenceDenominator_pos hn (by omega))
      simp only [normalized_add_two, forwardCoefficient, Nat.cast_add, Nat.cast_one,
        backwardCoefficient, eval_sub, eval_mul, eval_C, eval_X, mul_one, hi', hi]
      unfold recurrenceDenominator at hd ⊢
      push_cast at hd ⊢
      field_simp [hd]; ring

theorem normalized_natDegree {n : ℕ} (hn : 2 ≤ n) (i : ℕ) :
    (normalized n i).natDegree = i := by
  induction i using Nat.twoStepInduction with
  | zero => simp only [normalized_zero, natDegree_one]
  | one => simp only [normalized_one, natDegree_X]
  | more i hi hi' =>
      have hf : forwardCoefficient n (i + 1) ≠ 0 :=
        ne_of_gt (forwardCoefficient_pos hn (by omega))
      have hb : backwardCoefficient n (i + 1) ≠ 0 :=
        ne_of_gt (backwardCoefficient_pos hn (by omega))
      have hp : normalized n (i + 1) ≠ 0 := by
        intro h
        have heval := normalized_eval_one hn (i + 1)
        simp only [h, eval_zero, zero_ne_one] at heval
      have hmain :
          (Polynomial.C (forwardCoefficient n (i + 1)) * Polynomial.X *
            normalized n (i + 1)).natDegree = i + 2 := by
        rw [mul_assoc, Polynomial.natDegree_C_mul hf,
          Polynomial.natDegree_X_mul hp, hi']
      have hsmall :
          (Polynomial.C (backwardCoefficient n (i + 1)) *
            normalized n i).natDegree = i := by
        rw [Polynomial.natDegree_C_mul hb, hi]
      rw [normalized_add_two,
        Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by omega)]
      exact hmain

/-- The harmonic dimension used in the spherical-code argument. -/
def harmonicDimension (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 =>
      (n + i - 1).choose (i + 1) + (n + i - 2).choose i

@[simp] theorem harmonicDimension_zero (n : ℕ) :
    harmonicDimension n 0 = 1 := rfl

theorem harmonicDimension_succ (n i : ℕ) :
    harmonicDimension n (i + 1) =
      (n + i - 1).choose (i + 1) + (n + i - 2).choose i := rfl

theorem harmonicDimension_pos {n : ℕ} (hn : 2 ≤ n) (i : ℕ) :
    0 < harmonicDimension n i := by
  cases i with
  | zero => simp only [harmonicDimension_zero, Order.lt_one_iff]
  | succ i =>
      have hle : i + 1 ≤ n + i - 1 := by omega
      have hc : 0 < (n + i - 1).choose (i + 1) :=
        Nat.choose_pos hle
      exact Nat.add_pos_left hc ((n + i - 2).choose i)

theorem harmonicDimension_branch_step {n : ℕ} (hn : 2 ≤ n) (i : ℕ) :
    harmonicDimension (n + 1) (i + 1) =
      harmonicDimension (n + 1) i + harmonicDimension n (i + 1) := by
  cases i with
  | zero =>
      simp only [harmonicDimension, add_zero, add_tsub_cancel_right, zero_add, Nat.choose_one_right,
        Nat.reduceSubDiff, Nat.choose_zero_right]
      omega
  | succ i =>
      simp only [harmonicDimension]
      have h₁ : n + 1 + (i + 1) - 1 = (n + i) + 1 := by omega
      have h₂ : n + 1 + (i + 1) - 2 = n + i := by omega
      have h₃ : n + 1 + i - 1 = n + i := by omega
      have h₄ : n + 1 + i - 2 = n + i - 1 := by omega
      have h₅ : n + (i + 1) - 1 = n + i := by omega
      have h₆ : n + (i + 1) - 2 = n + i - 1 := by omega
      rw [h₁, h₂, h₃, h₄, h₅, h₆]
      have hbase : n + i = (n + i - 1) + 1 := by omega
      have htop :
          (n + i + 1).choose (i + 2) =
            (n + i).choose (i + 1) + (n + i).choose (i + 2) := by
        simpa only [Nat.succ_eq_add_one] using (Nat.choose_succ_succ (n + i) (i + 1))
      have hmid :
          (n + i).choose (i + 1) =
            (n + i - 1).choose i + (n + i - 1).choose (i + 1) := by
        rw [hbase]
        simpa only [add_tsub_cancel_right,
          Nat.succ_eq_add_one] using (Nat.choose_succ_succ (n + i - 1) i)
      simp only [Nat.add_assoc, Nat.reduceAdd] at htop hmid ⊢
      omega

theorem harmonicDimension_branch_sum {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    (∑ r ∈ Finset.range (k + 1), harmonicDimension n r) =
      harmonicDimension (n + 1) k := by
  induction k with
  | zero => simp only [zero_add, Finset.range_one, Finset.sum_singleton, harmonicDimension_zero]
  | succ k ih =>
      simpa only [Nat.add_assoc, Nat.reduceAdd, Finset.sum_range_succ, ih] using
        (harmonicDimension_branch_step hn k).symm

/-- The fibre dimension used in the spherical-code argument. -/
def fibreDimension (n k : ℕ) : ℕ := harmonicDimension (n - 1) k

/-- The channel dimension used in the spherical-code argument. -/
def channelDimension (n r : ℕ) : ℕ := harmonicDimension (n - 2) r

theorem fibreDimension_pos {n : ℕ} (hn : 3 ≤ n) (k : ℕ) :
    0 < fibreDimension n k := by
  apply harmonicDimension_pos (i := k)
  omega

/-- The alpha sq used in the spherical-code argument. -/
def alphaSq (n k i : ℕ) : ℝ :=
  (((i : ℝ) - (k : ℝ) + 1) *
    ((i : ℝ) + (k : ℝ) + (n : ℝ) - 2)) /
    (((i : ℝ) + 1) * (2 * (i : ℝ) + (n : ℝ) - 2))

/-- The beta sq used in the spherical-code argument. -/
def betaSq (n k i : ℕ) : ℝ :=
  (((i : ℝ) - (k : ℝ)) *
    ((i : ℝ) + (k : ℝ) + (n : ℝ) - 3)) /
    (((i : ℝ) + (n : ℝ) - 3) *
      (2 * (i : ℝ) + (n : ℝ) - 2))

/-- The jacobi coefficient used in the spherical-code argument. -/
def jacobiCoefficient (n k i : ℕ) : ℝ :=
  (((i : ℝ) - (k : ℝ) + 1) *
    ((i : ℝ) + (k : ℝ) + (n : ℝ) - 2)) /
    Real.sqrt
      (((i : ℝ) + 1) * ((i : ℝ) + (n : ℝ) - 2) *
        (2 * (i : ℝ) + (n : ℝ) - 2) *
        (2 * (i : ℝ) + (n : ℝ)))

theorem alphaSq_pos {n k i : ℕ}
    (hn : 3 ≤ n) (hki : k ≤ i) : 0 < alphaSq n k i := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hki' : (k : ℝ) ≤ i := by exact_mod_cast hki
  have hi' : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hk' : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  unfold alphaSq
  apply div_pos
  · apply mul_pos <;> linarith
  · apply mul_pos <;> linarith

theorem jacobiCoefficient_pos {n k i : ℕ}
    (hn : 3 ≤ n) (hki : k ≤ i) : 0 < jacobiCoefficient n k i := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hki' : (k : ℝ) ≤ i := by exact_mod_cast hki
  have hi' : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hk' : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  unfold jacobiCoefficient
  apply div_pos
  · apply mul_pos <;> linarith
  · apply Real.sqrt_pos.2
    have h₁ : 0 < (i : ℝ) + 1 := by linarith
    have h₂ : 0 < (i : ℝ) + (n : ℝ) - 2 := by linarith
    have h₃ : 0 < 2 * (i : ℝ) + (n : ℝ) - 2 := by linarith
    have h₄ : 0 < 2 * (i : ℝ) + (n : ℝ) := by linarith
    exact mul_pos (mul_pos (mul_pos h₁ h₂) h₃) h₄

private def jacobiMatrix (n k L : ℕ) :
    Matrix (Fin (L - k + 1)) (Fin (L - k + 1)) ℝ :=
  fun p q =>
    if p.val + 1 = q.val then
      jacobiCoefficient n k (k + p.val)
    else if q.val + 1 = p.val then
      jacobiCoefficient n k (k + q.val)
    else
      0

theorem jacobiMatrix_symmetric (n k L : ℕ) :
    (jacobiMatrix n k L).transpose = jacobiMatrix n k L := by
  ext p q
  simp only [Matrix.transpose_apply]
  by_cases hpq : p.val + 1 = q.val
  · have hqp : q.val + 1 ≠ p.val := by omega
    simp only [jacobiMatrix, hqp, ↓reduceIte, hpq]
  · by_cases hqp : q.val + 1 = p.val
    · simp only [jacobiMatrix, hqp, ↓reduceIte, hpq]
    · simp only [jacobiMatrix, hqp, ↓reduceIte, hpq]

theorem jacobiMatrix_upper_pos {n k L : ℕ}
    (hn : 3 ≤ n) (p q : Fin (L - k + 1))
    (hpq : p.val + 1 = q.val) : 0 < jacobiMatrix n k L p q := by
  simp only [jacobiMatrix, hpq, ↓reduceIte]
  exact jacobiCoefficient_pos hn (by omega)

end Gegenbauer

end

section


open scoped BigOperators InnerProductSpace

theorem mvPolynomial_pderiv_commute
    {n : ℕ} (i j : Fin n) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.derivation_C, map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p a hp =>
      simp only [Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero, map_add, hp]
      split <;> split <;> simp_all <;> ring

/-- The directional derivative used in the spherical-code argument. -/
def directionalDerivative (n : ℕ) (x : Euclidean n) :
    MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ :=
  ∑ i : Fin n, x i • (MvPolynomial.pderiv i).toLinearMap

@[simp] theorem directionalDerivative_apply
    (n : ℕ) (x : Euclidean n) (p : MvPolynomial (Fin n) ℝ) :
    directionalDerivative n x p =
      ∑ i : Fin n, x i • MvPolynomial.pderiv i p := by
  simp only [directionalDerivative, LinearMap.coe_sum, LinearMap.coe_smul, Derivation.coeFn_coe,
    Finset.sum_apply, Pi.smul_apply]

private def directionalDerivation (n : ℕ) (x : Euclidean n) :
    Derivation ℝ (MvPolynomial (Fin n) ℝ)
      (MvPolynomial (Fin n) ℝ) :=
  ∑ i : Fin n, x i • MvPolynomial.pderiv i

@[simp] theorem directionalDerivation_apply
    (n : ℕ) (x : Euclidean n) (p : MvPolynomial (Fin n) ℝ) :
    directionalDerivation n x p = directionalDerivative n x p := by
  classical
  have hsum (s : Finset (Fin n)) :
      (∑ i ∈ s, x i • MvPolynomial.pderiv i) p =
        ∑ i ∈ s, x i • MvPolynomial.pderiv i p := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, Derivation.coe_zero, Pi.zero_apply]
    | @insert a s ha ih =>
        simp only [ha, not_false_eq_true, Finset.sum_insert, Derivation.add_apply,
          Derivation.smul_apply, ih]
  simpa only [directionalDerivation, directionalDerivative_apply] using hsum Finset.univ

theorem directionalDerivative_mul
    {n : ℕ} (x : Euclidean n)
    (p q : MvPolynomial (Fin n) ℝ) :
    directionalDerivative n x (p * q) =
      directionalDerivative n x p * q +
        p * directionalDerivative n x q := by
  have h := (directionalDerivation n x).leibniz p q
  rw [directionalDerivation_apply, directionalDerivation_apply,
    directionalDerivation_apply] at h
  calc
    directionalDerivative n x (p * q) =
        p * directionalDerivative n x q +
          q * directionalDerivative n x p := by
            simpa only [directionalDerivative_apply, Derivation.leibniz, smul_eq_mul,
              smul_add] using h
    _ = directionalDerivative n x p * q +
          p * directionalDerivative n x q := by
            ring

/-- The axis polynomial used in the spherical-code argument. -/
def axisPolynomial (n : ℕ) (x : Euclidean n) :
    MvPolynomial (Fin n) ℝ :=
  ∑ i : Fin n, MvPolynomial.C (x i) * MvPolynomial.X i

@[simp] theorem pderiv_axisPolynomial
    {n : ℕ} (x : Euclidean n) (i : Fin n) :
    MvPolynomial.pderiv i (axisPolynomial n x) =
      MvPolynomial.C (x i) := by
  classical
  simp only [axisPolynomial, map_sum, Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, MvPolynomial.derivation_C, add_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem directionalDerivative_axisPolynomial
    {n : ℕ} (x y : Euclidean n) :
    directionalDerivative n x (axisPolynomial n y) =
      MvPolynomial.C ⟪x, y⟫_ℝ := by
  classical
  calc
    directionalDerivative n x (axisPolynomial n y) =
        ∑ i : Fin n, x i • MvPolynomial.C (y i) := by
          simp only [directionalDerivative_apply, pderiv_axisPolynomial]
    _ = ∑ i : Fin n, MvPolynomial.C (x i * y i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← MvPolynomial.C_mul', ← MvPolynomial.C_mul]
    _ = MvPolynomial.C (∑ i : Fin n, x i * y i) := by
          rw [map_sum]
    _ = MvPolynomial.C ⟪x, y⟫_ℝ := by
          simp only [map_sum, MvPolynomial.C_mul, PiLp.inner_apply, RCLike.inner_apply,
            Real.ringHom_apply, mul_comm]

theorem pderiv_directionalDerivative
    {n : ℕ} (x : Euclidean n) (i : Fin n)
    (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.pderiv i (directionalDerivative n x p) =
      directionalDerivative n x (MvPolynomial.pderiv i p) := by
  classical
  simp only [directionalDerivative_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [(MvPolynomial.pderiv i).map_smul,
    mvPolynomial_pderiv_commute i j p]

theorem polynomialLaplacian_directionalDerivative
    {n : ℕ} (x : Euclidean n) (p : MvPolynomial (Fin n) ℝ) :
    polynomialLaplacian n (directionalDerivative n x p) =
      directionalDerivative n x (polynomialLaplacian n p) := by
  classical
  calc
    polynomialLaplacian n (directionalDerivative n x p) =
        ∑ i : Fin n, MvPolynomial.pderiv i
          (MvPolynomial.pderiv i (directionalDerivative n x p)) := by
          rw [polynomialLaplacian_apply]
    _ = ∑ i : Fin n, directionalDerivative n x
          (MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [pderiv_directionalDerivative,
            pderiv_directionalDerivative]
    _ = directionalDerivative n x
          (∑ i : Fin n,
            MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) := by
          rw [map_sum]
    _ = directionalDerivative n x (polynomialLaplacian n p) := by
          rw [polynomialLaplacian_apply]

theorem directionalDerivative_isHomogeneous
    {n k : ℕ} (x : Euclidean n)
    {p : MvPolynomial (Fin n) ℝ} (hp : p.IsHomogeneous k) :
    (directionalDerivative n x p).IsHomogeneous (k - 1) := by
  rw [directionalDerivative_apply]
  apply MvPolynomial.IsHomogeneous.sum Finset.univ _ (k - 1)
  intro i hi
  change x i • MvPolynomial.pderiv i p ∈
    MvPolynomial.homogeneousSubmodule (Fin n) ℝ (k - 1)
  exact (MvPolynomial.homogeneousSubmodule (Fin n) ℝ (k - 1)).smul_mem
    (x i) hp.pderiv

theorem axisPolynomial_isHomogeneous
    {n : ℕ} (x : Euclidean n) :
    (axisPolynomial n x).IsHomogeneous 1 := by
  unfold axisPolynomial
  apply MvPolynomial.IsHomogeneous.sum Finset.univ _ 1
  intro i hi
  simpa only [zero_add] using
    (MvPolynomial.isHomogeneous_C (Fin n) (x i)).mul (MvPolynomial.isHomogeneous_X ℝ i)

theorem polynomialLaplacian_axisPolynomial
    {n : ℕ} (x : Euclidean n) :
    polynomialLaplacian n (axisPolynomial n x) = 0 := by
  simp only [polynomialLaplacian_apply, pderiv_axisPolynomial, MvPolynomial.derivation_C,
    Finset.sum_const_zero]

theorem directionalDerivative_axisPolynomial_self
    {n : ℕ} (x : Euclidean n) (hx : ‖x‖ = 1) :
    directionalDerivative n x (axisPolynomial n x) = 1 := by
  rw [directionalDerivative_axisPolynomial,
    real_inner_self_eq_norm_sq, hx]
  norm_num

theorem directionalDerivative_mem_harmonic
    {n k : ℕ} (x : Euclidean n)
    {p : MvPolynomial (Fin n) ℝ}
    (hp : p ∈ harmonicHomogeneousSubmodule n (k + 1)) :
    directionalDerivative n x p ∈ harmonicHomogeneousSubmodule n k := by
  have hp' := (mem_harmonicHomogeneousSubmodule p).mp hp
  apply (mem_harmonicHomogeneousSubmodule
    (directionalDerivative n x p)).mpr
  constructor
  · simpa only [directionalDerivative_apply, add_tsub_cancel_right] using
      directionalDerivative_isHomogeneous x hp'.1
  · rw [← polynomialLaplacian_apply,
      polynomialLaplacian_directionalDerivative]
    have hzero : polynomialLaplacian n p = 0 := by
      simpa only [polynomialLaplacian_apply] using hp'.2
    rw [hzero, map_zero]

/-- The harmonic directional derivative used in the spherical-code argument. -/
def harmonicDirectionalDerivative
    (n k : ℕ) (x : Euclidean n) :
    harmonicHomogeneousSubmodule n (k + 1) →ₗ[ℝ]
      harmonicHomogeneousSubmodule n k :=
  (directionalDerivative n x).restrict
    (fun _ hp => directionalDerivative_mem_harmonic x hp)

/-- The tangent harmonic submodule used in the spherical-code argument. -/
def tangentHarmonicSubmodule
    (n k : ℕ) (x : Euclidean n) :
    Submodule ℝ (MvPolynomial (Fin n) ℝ) :=
  harmonicHomogeneousSubmodule n k ⊓
    LinearMap.ker (directionalDerivative n x)

@[simp] theorem mem_tangentHarmonicSubmodule
    {n k : ℕ} (x : Euclidean n)
    (p : MvPolynomial (Fin n) ℝ) :
    p ∈ tangentHarmonicSubmodule n k x ↔
      p.IsHomogeneous k ∧
      polynomialLaplacian n p = 0 ∧
      directionalDerivative n x p = 0 := by
  simp only [tangentHarmonicSubmodule, harmonicHomogeneousSubmodule, Submodule.mem_inf,
    MvPolynomial.mem_homogeneousSubmodule, LinearMap.mem_ker, polynomialLaplacian_apply,
    directionalDerivative_apply, and_assoc]

namespace Fischer

/-- The multi index used in the spherical-code argument. -/
abbrev MultiIndex (n : ℕ) := Fin n →₀ ℕ

/-- The degree indices used in the spherical-code argument. -/
def degreeIndices (n m : ℕ) : Finset (MultiIndex n) :=
  Finset.finsuppAntidiag (Finset.univ : Finset (Fin n)) m

/-- The degree index used in the spherical-code argument. -/
abbrev DegreeIndex (n m : ℕ) := ↥(degreeIndices n m)

/-- The homogeneous used in the spherical-code argument. -/
abbrev Homogeneous (n m : ℕ) :=
  MvPolynomial.homogeneousSubmodule (Fin n) ℝ m

/-- The coefficient space used in the spherical-code argument. -/
abbrev CoefficientSpace (n m : ℕ) :=
  EuclideanSpace ℝ (DegreeIndex n m)

@[simp] theorem mem_degreeIndices {n m : ℕ} (a : MultiIndex n) :
    a ∈ degreeIndices n m ↔ a.degree = m := by
  simp only [degreeIndices, Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true,
    Finsupp.degree_eq_sum]

/-- The multi factorial used in the spherical-code argument. -/
def multiFactorial {n : ℕ} (a : MultiIndex n) : ℝ :=
  ∏ i : Fin n, (a i).factorial

theorem multiFactorial_pos {n : ℕ} (a : MultiIndex n) :
    0 < multiFactorial a := by
  unfold multiFactorial
  exact Finset.prod_pos fun i hi => by
    exact_mod_cast Nat.factorial_pos (a i)

theorem multiFactorial_add_single {n : ℕ}
    (a : MultiIndex n) (i : Fin n) :
    multiFactorial (a + Finsupp.single i 1) =
      ((a i + 1 : ℕ) : ℝ) * multiFactorial a := by
  classical
  unfold multiFactorial
  calc
    (∏ j : Fin n,
      (((a + (Finsupp.single i 1 : MultiIndex n)) j).factorial : ℝ)) =
        ∏ j : Fin n,
          ((if j = i then ((a i + 1 : ℕ) : ℝ) else 1) *
            ((a j).factorial : ℝ)) := by
      apply Finset.prod_congr rfl
      intro j hj
      by_cases h : j = i
      · subst j
        simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, Nat.factorial_succ,
          Nat.cast_mul, Nat.cast_add, Nat.cast_one, ↓reduceIte]
      · simp only [Finsupp.coe_add, Pi.add_apply, ne_eq, h, not_false_eq_true,
          Finsupp.single_eq_of_ne, add_zero, ↓reduceIte, one_mul]
    _ = (∏ j : Fin n,
          if j = i then ((a i + 1 : ℕ) : ℝ) else 1) *
          ∏ j : Fin n, ((a j).factorial : ℝ) := by
      rw [Finset.prod_mul_distrib]
    _ = ((a i + 1 : ℕ) : ℝ) *
          (∏ j : Fin n, ((a j).factorial : ℝ)) := by simp only [Nat.cast_add, Nat.cast_one,
                                                       Finset.prod_ite_eq', Finset.mem_univ,
                                                       ↓reduceIte]

theorem coeff_pderiv (n : ℕ) (i : Fin n) (a : MultiIndex n)
    (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.coeff a (MvPolynomial.pderiv i p) =
      ((a i + 1 : ℕ) : ℝ) *
        MvPolynomial.coeff (a + Finsupp.single i 1) p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial b c =>
      rw [MvPolynomial.pderiv_monomial,
        MvPolynomial.coeff_monomial,
        MvPolynomial.coeff_monomial]
      by_cases hb : b i = 0
      · have hne : b ≠ a + Finsupp.single i 1 := by
          intro heq
          have hi := congrArg (fun d : MultiIndex n => d i) heq
          simp only [hb, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, Nat.right_eq_add,
            Nat.add_eq_zero_iff, one_ne_zero, and_false] at hi
        simp only [hb, CharP.cast_eq_zero, mul_zero, ite_self, Nat.cast_add, Nat.cast_one, hne,
          ↓reduceIte]
      · by_cases hba : b - Finsupp.single i 1 = a
        · have hshift : b = a + Finsupp.single i 1 := by
            have hcancel := Finsupp.sub_add_single_one_cancel hb
            rw [hba] at hcancel
            exact hcancel.symm
          subst b
          simp only [add_tsub_cancel_right, ↓reduceIte, Finsupp.coe_add, Pi.add_apply,
            Finsupp.single_eq_same, Nat.cast_add, Nat.cast_one]
          ring
        · have hne : b ≠ a + Finsupp.single i 1 := by
            intro heq
            apply hba
            rw [heq]
            ext j
            by_cases hji : j = i
            · subst j
              simp only [add_tsub_cancel_right]
            · simp only [add_tsub_cancel_right]
          simp only [hba, ↓reduceIte, Nat.cast_add, Nat.cast_one, hne, mul_zero]
  | add p q hp hq =>
      simp only [map_add, MvPolynomial.coeff_add, hp, hq]
      ring

/-- The polynomial inner used in the spherical-code argument. -/
def polynomialInner (n : ℕ)
    (p q : MvPolynomial (Fin n) ℝ) : ℝ :=
  Finsupp.sum (AddMonoidAlgebra.coeff p) fun a c =>
    multiFactorial a * c * MvPolynomial.coeff a q

@[simp] theorem polynomialInner_monomial (n : ℕ)
    (a : MultiIndex n) (c : ℝ)
    (q : MvPolynomial (Fin n) ℝ) :
    polynomialInner n (MvPolynomial.monomial a c) q =
      multiFactorial a * c * MvPolynomial.coeff a q := by
  unfold polynomialInner
  rw [MvPolynomial.sum_monomial_eq]
  simp only [mul_zero, zero_mul]

theorem polynomialInner_add_left (n : ℕ)
    (p q r : MvPolynomial (Fin n) ℝ) :
    polynomialInner n (p + q) r =
      polynomialInner n p r + polynomialInner n q r := by
  unfold polynomialInner
  apply Finsupp.sum_add_index'
  · intro a
    ring
  · intro a b c
    ring

theorem polynomialInner_add_right (n : ℕ)
    (p q r : MvPolynomial (Fin n) ℝ) :
    polynomialInner n p (q + r) =
      polynomialInner n p q + polynomialInner n p r := by
  unfold polynomialInner
  simp only [MvPolynomial.sum_def, MvPolynomial.coeff_add]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]

theorem polynomialInner_comm (n : ℕ)
    (p q : MvPolynomial (Fin n) ℝ) :
    polynomialInner n p q = polynomialInner n q p := by
  classical
  unfold polynomialInner
  rw [MvPolynomial.sum_def, MvPolynomial.sum_def]
  calc
    (∑ a ∈ p.support,
      multiFactorial a *
        MvPolynomial.coeff a p * MvPolynomial.coeff a q) =
      ∑ a ∈ p.support ∪ q.support,
        multiFactorial a *
          MvPolynomial.coeff a p * MvPolynomial.coeff a q := by
          apply Finset.sum_subset Finset.subset_union_left
          intro a ha hnot
          have hzero : MvPolynomial.coeff a p = 0 :=
            MvPolynomial.notMem_support_iff.mp hnot
          simp only [hzero, mul_zero, zero_mul]
    _ = ∑ a ∈ q.support ∪ p.support,
        multiFactorial a *
          MvPolynomial.coeff a q * MvPolynomial.coeff a p := by
          rw [Finset.union_comm]
          apply Finset.sum_congr rfl
          intro a ha
          ring
    _ = ∑ a ∈ q.support,
        multiFactorial a *
          MvPolynomial.coeff a q * MvPolynomial.coeff a p := by
          symm
          apply Finset.sum_subset Finset.subset_union_left
          intro a ha hnot
          have hzero : MvPolynomial.coeff a q = 0 :=
            MvPolynomial.notMem_support_iff.mp hnot
          simp only [hzero, mul_zero, zero_mul]

theorem polynomialInner_self_nonneg (n : ℕ)
    (p : MvPolynomial (Fin n) ℝ) :
    0 ≤ polynomialInner n p p := by
  unfold polynomialInner
  rw [MvPolynomial.sum_def]
  apply Finset.sum_nonneg
  intro a ha
  calc
    0 ≤ multiFactorial a *
        (MvPolynomial.coeff a p) ^ 2 :=
      mul_nonneg (multiFactorial_pos a).le
        (sq_nonneg (MvPolynomial.coeff a p))
    _ = multiFactorial a *
        MvPolynomial.coeff a p * MvPolynomial.coeff a p := by
      ring

theorem polynomialInner_self_pos (n : ℕ)
    {p : MvPolynomial (Fin n) ℝ} (hp : p ≠ 0) :
    0 < polynomialInner n p p := by
  unfold polynomialInner
  rw [MvPolynomial.sum_def]
  apply Finset.sum_pos
  · intro a ha
    have hcoeff : MvPolynomial.coeff a p ≠ 0 :=
      MvPolynomial.mem_support_iff.mp ha
    calc
      0 < multiFactorial a *
          (MvPolynomial.coeff a p) ^ 2 :=
        mul_pos (multiFactorial_pos a)
          (sq_pos_of_ne_zero hcoeff)
      _ = multiFactorial a *
          MvPolynomial.coeff a p * MvPolynomial.coeff a p := by
        ring
  · exact MvPolynomial.support_nonempty.mpr hp

@[simp] theorem polynomialInner_self_eq_zero (n : ℕ)
    (p : MvPolynomial (Fin n) ℝ) :
    polynomialInner n p p = 0 ↔ p = 0 := by
  constructor
  · intro h
    by_contra hp
    exact (ne_of_gt (polynomialInner_self_pos n hp)) h
  · rintro rfl
    simp only [polynomialInner, AddMonoidAlgebra.coeff_zero, MvPolynomial.coeff_zero, mul_zero,
      Finsupp.sum_fun_zero]

theorem polynomialInner_smul_left (n : ℕ) (c : ℝ)
    (p q : MvPolynomial (Fin n) ℝ) :
    polynomialInner n (c • p) q = c * polynomialInner n p q := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a d =>
      rw [MvPolynomial.smul_monomial,
        polynomialInner_monomial, polynomialInner_monomial]
      change
        multiFactorial a * (c * d) * MvPolynomial.coeff a q =
          c * (multiFactorial a * d * MvPolynomial.coeff a q)
      ring
  | add p q hp hq =>
      rw [smul_add, polynomialInner_add_left,
        polynomialInner_add_left, hp, hq]
      ring

theorem polynomialInner_smul_right (n : ℕ) (c : ℝ)
    (p q : MvPolynomial (Fin n) ℝ) :
    polynomialInner n p (c • q) = c * polynomialInner n p q := by
  unfold polynomialInner
  simp only [MvPolynomial.sum_def, MvPolynomial.coeff_smul,
    smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem polynomialInner_sum_left {ι : Type*} (n : ℕ)
    (s : Finset ι) (f : ι → MvPolynomial (Fin n) ℝ)
    (q : MvPolynomial (Fin n) ℝ) :
    polynomialInner n (∑ i ∈ s, f i) q =
      ∑ i ∈ s, polynomialInner n (f i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [polynomialInner, Finset.sum_empty, AddMonoidAlgebra.coeff_zero,
               Finsupp.sum_zero_index, MvPolynomial.sum_def]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, polynomialInner_add_left,
        ih, Finset.sum_insert hi]

theorem polynomialInner_sum_right {ι : Type*} (n : ℕ)
    (p : MvPolynomial (Fin n) ℝ)
    (s : Finset ι) (f : ι → MvPolynomial (Fin n) ℝ) :
    polynomialInner n p (∑ i ∈ s, f i) =
      ∑ i ∈ s, polynomialInner n p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [polynomialInner, Finset.sum_empty, MvPolynomial.coeff_zero, mul_zero,
               Finsupp.sum_fun_zero, MvPolynomial.sum_def]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, polynomialInner_add_right,
        ih, Finset.sum_insert hi]

theorem polynomialInner_X_mul (n : ℕ) (i : Fin n)
    (p q : MvPolynomial (Fin n) ℝ) :
    polynomialInner n (MvPolynomial.X i * p) q =
      polynomialInner n p (MvPolynomial.pderiv i q) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
      have hmono :
          MvPolynomial.X i * MvPolynomial.monomial a c =
            MvPolynomial.monomial (Finsupp.single i 1 + a) c := by
        simpa only [pow_one] using
          (MvPolynomial.monomial_single_add (R := ℝ) (n := i) (e := 1) (s := a) (a := c)).symm
      have hshift :
          Finsupp.single i 1 + a = a + Finsupp.single i 1 :=
        add_comm _ _
      rw [hmono, polynomialInner_monomial,
        polynomialInner_monomial, coeff_pderiv, hshift,
        multiFactorial_add_single]
      ring
  | add p q hp hq =>
      rw [mul_add, polynomialInner_add_left,
        polynomialInner_add_left, hp, hq]

theorem polynomialInner_radial_laplacian (n : ℕ)
    (p q : MvPolynomial (Fin n) ℝ) :
    polynomialInner n
        ((∑ i : Fin n, MvPolynomial.X i ^ 2) * p) q =
      polynomialInner n p
        (∑ i : Fin n,
          MvPolynomial.pderiv i (MvPolynomial.pderiv i q)) := by
  classical
  calc
    polynomialInner n
        ((∑ i : Fin n, MvPolynomial.X i ^ 2) * p) q =
      polynomialInner n
        (∑ i : Fin n, MvPolynomial.X i ^ 2 * p) q := by
          rw [Finset.sum_mul]
    _ = ∑ i : Fin n,
        polynomialInner n (MvPolynomial.X i ^ 2 * p) q := by
          simpa only using polynomialInner_sum_left n Finset.univ (fun i : Fin n =>
            MvPolynomial.X i ^ 2 * p) q
    _ = ∑ i : Fin n,
        polynomialInner n p
          (MvPolynomial.pderiv i (MvPolynomial.pderiv i q)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [pow_two, mul_assoc, polynomialInner_X_mul,
            polynomialInner_X_mul]
    _ = polynomialInner n p
        (∑ i : Fin n,
          MvPolynomial.pderiv i (MvPolynomial.pderiv i q)) := by
          simpa only using
            (polynomialInner_sum_right n p Finset.univ (fun i : Fin n => MvPolynomial.pderiv i
              (MvPolynomial.pderiv i q))).symm

theorem polynomialInner_axis_directional (n : ℕ)
    (x : SpherePacking.Euclidean n)
    (p q : MvPolynomial (Fin n) ℝ) :
    polynomialInner n (SpherePacking.axisPolynomial n x * p) q =
      polynomialInner n p
        (SpherePacking.directionalDerivative n x q) := by
  classical
  rw [SpherePacking.axisPolynomial,
    SpherePacking.directionalDerivative_apply]
  calc
    polynomialInner n
        ((∑ i : Fin n,
          MvPolynomial.C (x i) * MvPolynomial.X i) * p) q =
      polynomialInner n
        (∑ i : Fin n,
          MvPolynomial.C (x i) *
            (MvPolynomial.X i * p)) q := by
          rw [Finset.sum_mul]
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = ∑ i : Fin n,
        polynomialInner n
          (MvPolynomial.C (x i) *
            (MvPolynomial.X i * p)) q := by
          simpa only using
            polynomialInner_sum_left n Finset.univ (fun i : Fin n => MvPolynomial.C (x i) *
              (MvPolynomial.X i * p)) q
    _ = ∑ i : Fin n,
        polynomialInner n p
          (x i • MvPolynomial.pderiv i q) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [MvPolynomial.C_mul', polynomialInner_smul_left,
            polynomialInner_smul_right, polynomialInner_X_mul]
    _ = polynomialInner n p
        (∑ i : Fin n,
          x i • MvPolynomial.pderiv i q) := by
          simpa only using
            (polynomialInner_sum_right n p Finset.univ (fun i : Fin n => x i •
              MvPolynomial.pderiv i q)).symm

/-- The coefficient embedding used in the spherical-code argument. -/
def coefficientEmbedding (n m : ℕ) :
    Homogeneous n m →ₗ[ℝ] CoefficientSpace n m where
  toFun p :=
    WithLp.toLp 2 fun a : DegreeIndex n m =>
      Real.sqrt (multiFactorial (a : MultiIndex n)) *
        MvPolynomial.coeff (a : MultiIndex n)
          (p : MvPolynomial (Fin n) ℝ)
  map_add' p q := by
    ext a
    change
      Real.sqrt (multiFactorial (a : MultiIndex n)) *
          MvPolynomial.coeff (a : MultiIndex n)
            ((p : MvPolynomial (Fin n) ℝ) +
              (q : MvPolynomial (Fin n) ℝ)) =
        Real.sqrt (multiFactorial (a : MultiIndex n)) *
            MvPolynomial.coeff (a : MultiIndex n)
              (p : MvPolynomial (Fin n) ℝ) +
          Real.sqrt (multiFactorial (a : MultiIndex n)) *
            MvPolynomial.coeff (a : MultiIndex n)
              (q : MvPolynomial (Fin n) ℝ)
    rw [MvPolynomial.coeff_add]
    ring
  map_smul' c p := by
    ext a
    change
      Real.sqrt (multiFactorial (a : MultiIndex n)) *
        MvPolynomial.coeff (a : MultiIndex n)
          (c • (p : MvPolynomial (Fin n) ℝ)) =
      c *
        (Real.sqrt (multiFactorial (a : MultiIndex n)) *
          MvPolynomial.coeff (a : MultiIndex n)
            (p : MvPolynomial (Fin n) ℝ))
    rw [MvPolynomial.coeff_smul]
    change
      Real.sqrt (multiFactorial (a : MultiIndex n)) *
        (c * MvPolynomial.coeff (a : MultiIndex n)
          (p : MvPolynomial (Fin n) ℝ)) =
      c *
        (Real.sqrt (multiFactorial (a : MultiIndex n)) *
          MvPolynomial.coeff (a : MultiIndex n)
            (p : MvPolynomial (Fin n) ℝ))
    ring

@[simp] theorem coefficientEmbedding_apply (n m : ℕ)
    (p : Homogeneous n m) (a : DegreeIndex n m) :
    coefficientEmbedding n m p a =
      Real.sqrt (multiFactorial (a : MultiIndex n)) *
        MvPolynomial.coeff (a : MultiIndex n)
          (p : MvPolynomial (Fin n) ℝ) := rfl

theorem coefficientEmbedding_injective (n m : ℕ) :
    Function.Injective (coefficientEmbedding n m) := by
  intro p q hp
  apply Subtype.ext
  apply MvPolynomial.ext
  intro a
  by_cases ha : a.degree = m
  · have hamem : a ∈ degreeIndices n m :=
      (mem_degreeIndices a).mpr ha
    let b : DegreeIndex n m := ⟨a, hamem⟩
    have hcoord := congrArg
      (fun v : CoefficientSpace n m => v b) hp
    have hroot : Real.sqrt (multiFactorial a) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (multiFactorial_pos a))
    apply mul_left_cancel₀ hroot
    exact hcoord
  · rw [MvPolynomial.IsHomogeneous.coeff_eq_zero p.property ha,
      MvPolynomial.IsHomogeneous.coeff_eq_zero q.property ha]

private def harmonicCoefficientEmbedding (n m : ℕ) :
    SpherePacking.harmonicHomogeneousSubmodule n m →ₗ[ℝ]
      CoefficientSpace n m :=
  (coefficientEmbedding n m).comp
    (Submodule.inclusion
      (show SpherePacking.harmonicHomogeneousSubmodule n m ≤
        MvPolynomial.homogeneousSubmodule (Fin n) ℝ m from inf_le_left))

theorem harmonicCoefficientEmbedding_injective (n m : ℕ) :
    Function.Injective (harmonicCoefficientEmbedding n m) := by
  exact (coefficientEmbedding_injective n m).comp
    (Submodule.inclusion_injective
      (show SpherePacking.harmonicHomogeneousSubmodule n m ≤
        MvPolynomial.homogeneousSubmodule (Fin n) ℝ m from inf_le_left))

/-- The homogeneous inner used in the spherical-code argument. -/
def homogeneousInner (n m : ℕ)
    (p q : Homogeneous n m) : ℝ :=
  @inner ℝ (CoefficientSpace n m) _
    (coefficientEmbedding n m p) (coefficientEmbedding n m q)

theorem homogeneousInner_eq_sum (n m : ℕ)
    (p q : Homogeneous n m) :
    homogeneousInner n m p q =
      ∑ a : DegreeIndex n m,
        multiFactorial (a : MultiIndex n) *
          MvPolynomial.coeff (a : MultiIndex n)
            (p : MvPolynomial (Fin n) ℝ) *
          MvPolynomial.coeff (a : MultiIndex n)
            (q : MvPolynomial (Fin n) ℝ) := by
  unfold homogeneousInner
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply, coefficientEmbedding_apply]
  apply Finset.sum_congr rfl
  intro a ha
  have hw : 0 ≤ multiFactorial (a : MultiIndex n) :=
    (multiFactorial_pos (a : MultiIndex n)).le
  calc
    (Real.sqrt (multiFactorial (a : MultiIndex n)) *
      MvPolynomial.coeff (a : MultiIndex n)
        (p : MvPolynomial (Fin n) ℝ)) *
      (Real.sqrt (multiFactorial (a : MultiIndex n)) *
        MvPolynomial.coeff (a : MultiIndex n)
          (q : MvPolynomial (Fin n) ℝ)) =
      (Real.sqrt (multiFactorial (a : MultiIndex n)) *
        Real.sqrt (multiFactorial (a : MultiIndex n))) *
      MvPolynomial.coeff (a : MultiIndex n)
        (p : MvPolynomial (Fin n) ℝ) *
      MvPolynomial.coeff (a : MultiIndex n)
        (q : MvPolynomial (Fin n) ℝ) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hw]

theorem homogeneousInner_eq_polynomialInner (n m : ℕ)
    (p q : Homogeneous n m) :
    homogeneousInner n m p q =
      polynomialInner n
        (p : MvPolynomial (Fin n) ℝ)
        (q : MvPolynomial (Fin n) ℝ) := by
  classical
  rw [homogeneousInner_eq_sum]
  unfold polynomialInner
  rw [MvPolynomial.sum_def]
  change
    (∑ a : DegreeIndex n m,
      (fun b : MultiIndex n =>
        multiFactorial b *
          MvPolynomial.coeff b (p : MvPolynomial (Fin n) ℝ) *
          MvPolynomial.coeff b (q : MvPolynomial (Fin n) ℝ))
        (a : MultiIndex n)) = _
  rw [Finset.sum_coe_sort (degreeIndices n m)
    (fun b : MultiIndex n =>
      multiFactorial b *
        MvPolynomial.coeff b (p : MvPolynomial (Fin n) ℝ) *
        MvPolynomial.coeff b (q : MvPolynomial (Fin n) ℝ))]
  symm
  apply Finset.sum_subset
  · intro a ha
    apply (mem_degreeIndices a).mpr
    by_contra hdeg
    exact (MvPolynomial.mem_support_iff.mp ha)
      (MvPolynomial.IsHomogeneous.coeff_eq_zero p.property hdeg)
  · intro a ha hnot
    have hzero :
        MvPolynomial.coeff a
          (p : MvPolynomial (Fin n) ℝ) = 0 :=
      MvPolynomial.notMem_support_iff.mp hnot
    rw [hzero]
    ring

/-- The homogeneous inner core used in the spherical-code argument. -/
@[implicit_reducible] def homogeneousInnerCore (n m : ℕ) :
    InnerProductSpace.Core ℝ (Homogeneous n m) where
  inner p q := homogeneousInner n m p q
  conj_inner_symm p q := by
    change
      (starRingEnd ℝ)
          (@inner ℝ (CoefficientSpace n m) _
            (coefficientEmbedding n m q)
            (coefficientEmbedding n m p)) =
        @inner ℝ (CoefficientSpace n m) _
          (coefficientEmbedding n m p)
          (coefficientEmbedding n m q)
    simpa only [Real.ringHom_apply] using
      real_inner_comm (coefficientEmbedding n m p) (coefficientEmbedding n m q)
  re_inner_nonneg p := by
    change
      0 ≤ @inner ℝ (CoefficientSpace n m) _
        (coefficientEmbedding n m p)
        (coefficientEmbedding n m p)
    exact real_inner_self_nonneg
  add_left p q r := by
    unfold homogeneousInner
    rw [map_add, inner_add_left]
  smul_left p q c := by
    unfold homogeneousInner
    rw [map_smul, real_inner_smul_left]
    simp only [Real.ringHom_apply]
  definite p hp := by
    change
      @inner ℝ (CoefficientSpace n m) _
        (coefficientEmbedding n m p)
        (coefficientEmbedding n m p) = 0 at hp
    have hzero : coefficientEmbedding n m p = 0 :=
      (inner_self_eq_zero.mp hp)
    apply coefficientEmbedding_injective n m
    simpa only [map_zero] using hzero

@[simp] theorem harmonicCoefficientEmbedding_apply (n m : ℕ)
    (p : SpherePacking.harmonicHomogeneousSubmodule n m)
    (a : DegreeIndex n m) :
    harmonicCoefficientEmbedding n m p a =
      Real.sqrt (multiFactorial (a : MultiIndex n)) *
        MvPolynomial.coeff (a : MultiIndex n)
          (p : MvPolynomial (Fin n) ℝ) := rfl

/-- The harmonic inner used in the spherical-code argument. -/
def harmonicInner (n m : ℕ)
    (p q : SpherePacking.harmonicHomogeneousSubmodule n m) : ℝ :=
  @inner ℝ (CoefficientSpace n m) _
    (harmonicCoefficientEmbedding n m p)
    (harmonicCoefficientEmbedding n m q)

theorem harmonicInner_eq_sum (n m : ℕ)
    (p q : SpherePacking.harmonicHomogeneousSubmodule n m) :
    harmonicInner n m p q =
      ∑ a : DegreeIndex n m,
        multiFactorial (a : MultiIndex n) *
          MvPolynomial.coeff (a : MultiIndex n)
            (p : MvPolynomial (Fin n) ℝ) *
          MvPolynomial.coeff (a : MultiIndex n)
            (q : MvPolynomial (Fin n) ℝ) := by
  unfold harmonicInner
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply, harmonicCoefficientEmbedding_apply]
  apply Finset.sum_congr rfl
  intro a ha
  have hw : 0 ≤ multiFactorial (a : MultiIndex n) :=
    (multiFactorial_pos (a : MultiIndex n)).le
  calc
    (Real.sqrt (multiFactorial (a : MultiIndex n)) *
      MvPolynomial.coeff (a : MultiIndex n)
        (p : MvPolynomial (Fin n) ℝ)) *
      (Real.sqrt (multiFactorial (a : MultiIndex n)) *
        MvPolynomial.coeff (a : MultiIndex n)
          (q : MvPolynomial (Fin n) ℝ)) =
      (Real.sqrt (multiFactorial (a : MultiIndex n)) *
        Real.sqrt (multiFactorial (a : MultiIndex n))) *
      MvPolynomial.coeff (a : MultiIndex n)
        (p : MvPolynomial (Fin n) ℝ) *
      MvPolynomial.coeff (a : MultiIndex n)
        (q : MvPolynomial (Fin n) ℝ) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hw]

theorem harmonicInner_eq_polynomialInner (n m : ℕ)
    (p q : SpherePacking.harmonicHomogeneousSubmodule n m) :
    harmonicInner n m p q =
      polynomialInner n
        (p : MvPolynomial (Fin n) ℝ)
        (q : MvPolynomial (Fin n) ℝ) := by
  let hp : Homogeneous n m :=
    Submodule.inclusion
      (show SpherePacking.harmonicHomogeneousSubmodule n m ≤
        MvPolynomial.homogeneousSubmodule (Fin n) ℝ m from
        inf_le_left) p
  let hq : Homogeneous n m :=
    Submodule.inclusion
      (show SpherePacking.harmonicHomogeneousSubmodule n m ≤
        MvPolynomial.homogeneousSubmodule (Fin n) ℝ m from
        inf_le_left) q
  calc
    harmonicInner n m p q = homogeneousInner n m hp hq := by
      rw [harmonicInner_eq_sum, homogeneousInner_eq_sum]
      simp only [Finset.univ_eq_attach, Submodule.coe_inclusion, hp, hq]
    _ = polynomialInner n
        (p : MvPolynomial (Fin n) ℝ)
        (q : MvPolynomial (Fin n) ℝ) := by
      exact homogeneousInner_eq_polynomialInner n m hp hq

/-- The embedding inner core used in the spherical-code argument. -/
@[implicit_reducible] def embeddingInnerCore
    {F E : Type*} [AddCommGroup F] [Module ℝ F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : F →ₗ[ℝ] E) (hf : Function.Injective f) :
    InnerProductSpace.Core ℝ F where
  inner p q := @inner ℝ E _ (f p) (f q)
  conj_inner_symm p q := by
    change
      (starRingEnd ℝ) (@inner ℝ E _ (f q) (f p)) =
        @inner ℝ E _ (f p) (f q)
    simpa only [Real.ringHom_apply] using real_inner_comm (f p) (f q)
  re_inner_nonneg p := by
    change 0 ≤ @inner ℝ E _ (f p) (f p)
    exact real_inner_self_nonneg
  add_left p q r := by
    change
      @inner ℝ E _ (f (p + q)) (f r) =
        @inner ℝ E _ (f p) (f r) +
          @inner ℝ E _ (f q) (f r)
    rw [map_add, inner_add_left]
  smul_left p q c := by
    change
      @inner ℝ E _ (f (c • p)) (f q) =
        (starRingEnd ℝ) c * @inner ℝ E _ (f p) (f q)
    rw [map_smul, real_inner_smul_left]
    simp only [Real.ringHom_apply]
  definite p hp := by
    change @inner ℝ E _ (f p) (f p) = 0 at hp
    have hzero : f p = 0 := inner_self_eq_zero.mp hp
    apply hf
    simpa only [map_zero] using hzero

@[implicit_reducible] private def harmonicInnerCore (n m : ℕ) :
    InnerProductSpace.Core ℝ
      (SpherePacking.harmonicHomogeneousSubmodule n m) :=
  embeddingInnerCore (harmonicCoefficientEmbedding n m)
    (harmonicCoefficientEmbedding_injective n m)

theorem tangentHarmonicSubmodule_le_harmonic
    (n m : ℕ) (x : SpherePacking.Euclidean n) :
    SpherePacking.tangentHarmonicSubmodule n m x ≤
      SpherePacking.harmonicHomogeneousSubmodule n m := by
  change
    SpherePacking.harmonicHomogeneousSubmodule n m ⊓
      LinearMap.ker (SpherePacking.directionalDerivative n x) ≤
        SpherePacking.harmonicHomogeneousSubmodule n m
  exact inf_le_left

private def tangentCoefficientEmbedding
    (n m : ℕ) (x : SpherePacking.Euclidean n) :
    SpherePacking.tangentHarmonicSubmodule n m x →ₗ[ℝ]
      CoefficientSpace n m :=
  (harmonicCoefficientEmbedding n m).comp
    (Submodule.inclusion
      (tangentHarmonicSubmodule_le_harmonic n m x))

theorem tangentCoefficientEmbedding_injective
    (n m : ℕ) (x : SpherePacking.Euclidean n) :
    Function.Injective (tangentCoefficientEmbedding n m x) :=
  (harmonicCoefficientEmbedding_injective n m).comp
    (Submodule.inclusion_injective
      (tangentHarmonicSubmodule_le_harmonic n m x))

theorem tangent_finiteDimensional
    (n m : ℕ) (x : SpherePacking.Euclidean n) :
    FiniteDimensional ℝ
      (SpherePacking.tangentHarmonicSubmodule n m x) :=
  FiniteDimensional.of_injective
    (tangentCoefficientEmbedding n m x)
    (tangentCoefficientEmbedding_injective n m x)

private def tangentInner (n m : ℕ) (x : SpherePacking.Euclidean n)
    (p q : SpherePacking.tangentHarmonicSubmodule n m x) : ℝ :=
  @inner ℝ (CoefficientSpace n m) _
    (tangentCoefficientEmbedding n m x p)
    (tangentCoefficientEmbedding n m x q)

theorem tangentInner_eq_polynomialInner
    (n m : ℕ) (x : SpherePacking.Euclidean n)
    (p q : SpherePacking.tangentHarmonicSubmodule n m x) :
    tangentInner n m x p q =
      polynomialInner n
        (p : MvPolynomial (Fin n) ℝ)
        (q : MvPolynomial (Fin n) ℝ) := by
  let hp : SpherePacking.harmonicHomogeneousSubmodule n m :=
    Submodule.inclusion
      (tangentHarmonicSubmodule_le_harmonic n m x) p
  let hq : SpherePacking.harmonicHomogeneousSubmodule n m :=
    Submodule.inclusion
      (tangentHarmonicSubmodule_le_harmonic n m x) q
  calc
    tangentInner n m x p q = harmonicInner n m hp hq := rfl
    _ = polynomialInner n
        (p : MvPolynomial (Fin n) ℝ)
        (q : MvPolynomial (Fin n) ℝ) := by
      exact harmonicInner_eq_polynomialInner n m hp hq

@[implicit_reducible] private def tangentInnerCore
    (n m : ℕ) (x : SpherePacking.Euclidean n) :
    InnerProductSpace.Core ℝ
      (SpherePacking.tangentHarmonicSubmodule n m x) :=
  embeddingInnerCore (tangentCoefficientEmbedding n m x)
    (tangentCoefficientEmbedding_injective n m x)

noncomputable instance instHarmonicFischerInner (n m : ℕ) :
    Inner ℝ (SpherePacking.harmonicHomogeneousSubmodule n m) :=
  ⟨harmonicInner n m⟩

noncomputable instance instHarmonicFischerNormedAddCommGroup
    (n m : ℕ) :
    NormedAddCommGroup
      (SpherePacking.harmonicHomogeneousSubmodule n m) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ
    (SpherePacking.harmonicHomogeneousSubmodule n m)
    _ _ _ (harmonicInnerCore n m)

noncomputable instance instHarmonicFischerInnerProductSpace
    (n m : ℕ) :
    InnerProductSpace ℝ
      (SpherePacking.harmonicHomogeneousSubmodule n m) :=
  InnerProductSpace.ofCore _

noncomputable instance instTangentFischerInner
    (n m : ℕ) (x : SpherePacking.Euclidean n) :
    Inner ℝ (SpherePacking.tangentHarmonicSubmodule n m x) :=
  ⟨tangentInner n m x⟩

noncomputable instance instTangentFischerNormedAddCommGroup
    (n m : ℕ) (x : SpherePacking.Euclidean n) :
    NormedAddCommGroup
      (SpherePacking.tangentHarmonicSubmodule n m x) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ
    (SpherePacking.tangentHarmonicSubmodule n m x)
    _ _ _ (tangentInnerCore n m x)

noncomputable instance instTangentFischerInnerProductSpace
    (n m : ℕ) (x : SpherePacking.Euclidean n) :
    InnerProductSpace ℝ
      (SpherePacking.tangentHarmonicSubmodule n m x) :=
  InnerProductSpace.ofCore _

@[simp] theorem harmonic_inner_eq (n m : ℕ)
    (p q : SpherePacking.harmonicHomogeneousSubmodule n m) :
    ⟪p, q⟫_ℝ = harmonicInner n m p q := rfl

@[simp] theorem tangent_inner_eq
    (n m : ℕ) (x : SpherePacking.Euclidean n)
    (p q : SpherePacking.tangentHarmonicSubmodule n m x) :
    ⟪p, q⟫_ℝ = tangentInner n m x p q := rfl

end Fischer

end

section


open scoped BigOperators

/-- The radial polynomial used in the spherical-code argument. -/
def radialPolynomial (n : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ i : Fin n, MvPolynomial.X i ^ 2

@[simp] theorem pderiv_radialPolynomial {n : ℕ} (i : Fin n) :
    MvPolynomial.pderiv i (radialPolynomial n) =
      2 * MvPolynomial.X i := by
  classical
  simp only [radialPolynomial, map_sum, Derivation.leibniz_pow, Nat.add_one_sub_one, pow_one,
    MvPolynomial.pderiv_X, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, smul_ite,
    nsmul_eq_mul, Nat.cast_ofNat, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem radialPolynomial_isHomogeneous (n : ℕ) :
    (radialPolynomial n).IsHomogeneous 2 := by
  unfold radialPolynomial
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  exact MvPolynomial.isHomogeneous_X_pow i 2

theorem radialPolynomial_ne_zero {n : ℕ} (hn : 0 < n) :
    radialPolynomial n ≠ 0 := by
  intro h
  have heval : (n : ℝ) = 0 := by
    have h' := congrArg
      (MvPolynomial.eval (fun _ : Fin n => (1 : ℝ))) h
    simpa only [Nat.cast_eq_zero, radialPolynomial, map_sum, map_pow, MvPolynomial.eval_X, one_pow,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      map_zero] using h'
  have hn' : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  exact hn' heval

theorem polynomialLaplacian_isHomogeneous {n m : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (hp : p.IsHomogeneous m) :
    (polynomialLaplacian n p).IsHomogeneous (m - 2) := by
  rw [polynomialLaplacian_apply]
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  exact (hp.pderiv (i := i)).pderiv (i := i)

private def homogeneousExponentFinset (n m : ℕ) :
    Finset (Fin n →₀ ℕ) :=
  (Finset.univ : Finset (Fin n)).finsuppAntidiag m

private abbrev HomogeneousExponent (n m : ℕ) :=
  ↥(homogeneousExponentFinset n m)

@[simp] theorem homogeneousExponentFinset_card (n m : ℕ) :
    (homogeneousExponentFinset n m).card =
      (n + m - 1).choose m := by
  classical
  simpa only [homogeneousExponentFinset, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_finsuppAntidiag_nat_eq_choose (s := (Finset.univ : Finset (Fin n))) m)

@[simp] theorem mem_homogeneousExponentFinset {n m : ℕ}
    (d : Fin n →₀ ℕ) :
    d ∈ homogeneousExponentFinset n m ↔ d.degree = m := by
  classical
  simp only [homogeneousExponentFinset, Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true,
    Finsupp.degree_eq_sum]

theorem homogeneousSubmodule_eq_supported_exponents (n m : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin n) ℝ m =
      AddMonoidAlgebra.supported ℝ ℝ
        (homogeneousExponentFinset n m : Set (Fin n →₀ ℕ)) := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  congr 1
  ext d
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_homogeneousExponentFinset]

private def homogeneousCoefficientEquiv (n m : ℕ) :
    (MvPolynomial.homogeneousSubmodule (Fin n) ℝ m) ≃ₗ[ℝ]
      (HomogeneousExponent n m → ℝ) :=
  (LinearEquiv.ofEq _ _
    (homogeneousSubmodule_eq_supported_exponents n m)).trans
      ((AddMonoidAlgebra.supportedEquivFinsupp
        (homogeneousExponentFinset n m : Set (Fin n →₀ ℕ))).trans
        (Finsupp.linearEquivFunOnFinite ℝ ℝ
          (HomogeneousExponent n m)))

instance homogeneousSubmodule_finiteDimensional (n m : ℕ) :
    FiniteDimensional ℝ
      (MvPolynomial.homogeneousSubmodule (Fin n) ℝ m) :=
  FiniteDimensional.of_injective
    (homogeneousCoefficientEquiv n m).toLinearMap
    (homogeneousCoefficientEquiv n m).injective

theorem finrank_homogeneousSubmodule (n m : ℕ) :
    Module.finrank ℝ
      (MvPolynomial.homogeneousSubmodule (Fin n) ℝ m) =
        (n + m - 1).choose m := by
  calc
    Module.finrank ℝ
        (MvPolynomial.homogeneousSubmodule (Fin n) ℝ m) =
        Module.finrank ℝ (HomogeneousExponent n m → ℝ) :=
      (homogeneousCoefficientEquiv n m).finrank_eq
    _ = Fintype.card (HomogeneousExponent n m) :=
      Module.finrank_pi ℝ
    _ = (homogeneousExponentFinset n m).card :=
      Fintype.card_coe _
    _ = (n + m - 1).choose m :=
      homogeneousExponentFinset_card n m

private def homogeneousRadialMultiplication (n m : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin n) ℝ m →ₗ[ℝ]
      MvPolynomial.homogeneousSubmodule (Fin n) ℝ (m + 2) :=
  (LinearMap.mulLeft ℝ (radialPolynomial n)).restrict
    (fun p hp => by
      simpa only [LinearMap.mulLeft_apply, MvPolynomial.mem_homogeneousSubmodule, Nat.add_comm]
        using
        (radialPolynomial_isHomogeneous n).mul hp)

@[simp] theorem homogeneousRadialMultiplication_apply (n m : ℕ)
    (p : MvPolynomial.homogeneousSubmodule (Fin n) ℝ m) :
    ((homogeneousRadialMultiplication n m p :
      MvPolynomial.homogeneousSubmodule (Fin n) ℝ (m + 2)) :
        MvPolynomial (Fin n) ℝ) =
      radialPolynomial n * (p : MvPolynomial (Fin n) ℝ) := rfl

theorem homogeneousRadialMultiplication_injective
    {n : ℕ} (hn : 0 < n) (m : ℕ) :
    Function.Injective (homogeneousRadialMultiplication n m) := by
  intro p q hpq
  apply Subtype.ext
  have h := congrArg
    (fun r : MvPolynomial.homogeneousSubmodule (Fin n) ℝ (m + 2) =>
      (r : MvPolynomial (Fin n) ℝ)) hpq
  exact mul_left_cancel₀ (radialPolynomial_ne_zero hn) h

theorem surjective_of_injective_inner_adjoint
    {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (cE : InnerProductSpace.Core ℝ E)
    (cF : InnerProductSpace.Core ℝ F)
    (A : E →ₗ[ℝ] F) (B : F →ₗ[ℝ] E)
    (hpair : ∀ (x : F) (y : E),
      cE.inner (B x) y = cF.inner x (A y))
    (hinj : Function.Injective A) :
    Function.Surjective B := by
  let : InnerProductSpace.Core ℝ E := cE
  let : NormedAddCommGroup E :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  let : InnerProductSpace ℝ E :=
    InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℝ E)
  let : InnerProductSpace.Core ℝ F := cF
  let : NormedAddCommGroup F :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  let : InnerProductSpace ℝ F :=
    InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℝ F)
  have hadj : B = A.adjoint := by
    apply (LinearMap.eq_adjoint_iff B A).mpr
    intro x y
    change cE.inner (B x) y = cF.inner x (A y)
    exact hpair x y
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  rw [hadj, LinearMap.finrank_range_adjoint,
    LinearMap.finrank_range_of_inj hinj]

private def homogeneousLaplacian (n m : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin n) ℝ (m + 2) →ₗ[ℝ]
      MvPolynomial.homogeneousSubmodule (Fin n) ℝ m :=
  LinearMap.codRestrict
    (MvPolynomial.homogeneousSubmodule (Fin n) ℝ m)
    ((polynomialLaplacian n).domRestrict
      (MvPolynomial.homogeneousSubmodule (Fin n) ℝ (m + 2)))
    (fun p => by
      change (polynomialLaplacian n
        (p : MvPolynomial (Fin n) ℝ)).IsHomogeneous m
      simpa only [polynomialLaplacian_apply, add_tsub_cancel_right] using
        polynomialLaplacian_isHomogeneous (p : MvPolynomial (Fin n) ℝ) p.property)

@[simp] theorem homogeneousLaplacian_apply (n m : ℕ)
    (p : MvPolynomial.homogeneousSubmodule (Fin n) ℝ (m + 2)) :
    ((homogeneousLaplacian n m p :
      MvPolynomial.homogeneousSubmodule (Fin n) ℝ m) :
        MvPolynomial (Fin n) ℝ) =
      polynomialLaplacian n (p : MvPolynomial (Fin n) ℝ) := rfl

theorem fischer_homogeneousInner_comm (n m : ℕ)
    (p q : Fischer.Homogeneous n m) :
    Fischer.homogeneousInner n m p q =
      Fischer.homogeneousInner n m q p := by
  unfold Fischer.homogeneousInner
  exact real_inner_comm _ _

theorem fischer_homogeneousInner_radial_laplacian
    (n m : ℕ)
    (p : MvPolynomial.homogeneousSubmodule (Fin n) ℝ m)
    (q : MvPolynomial.homogeneousSubmodule (Fin n) ℝ (m + 2)) :
    Fischer.homogeneousInner n (m + 2)
        (homogeneousRadialMultiplication n m p) q =
      Fischer.homogeneousInner n m p
        (homogeneousLaplacian n m q) := by
  rw [Fischer.homogeneousInner_eq_polynomialInner,
    Fischer.homogeneousInner_eq_polynomialInner]
  simpa only [homogeneousRadialMultiplication_apply, radialPolynomial, homogeneousLaplacian_apply,
    polynomialLaplacian_apply] using
    Fischer.polynomialInner_radial_laplacian n (p : MvPolynomial (Fin n) ℝ) (q : MvPolynomial
      (Fin n) ℝ)

theorem homogeneousLaplacian_surjective_of_fischer_adjoint
    {n : ℕ} (hn : 0 < n) (m : ℕ)
    (hpair : ∀
      (q : MvPolynomial.homogeneousSubmodule (Fin n) ℝ (m + 2))
      (p : MvPolynomial.homogeneousSubmodule (Fin n) ℝ m),
      Fischer.homogeneousInner n m
        (homogeneousLaplacian n m q) p =
      Fischer.homogeneousInner n (m + 2)
        q (homogeneousRadialMultiplication n m p)) :
    Function.Surjective (homogeneousLaplacian n m) := by
  apply surjective_of_injective_inner_adjoint
    (Fischer.homogeneousInnerCore n m)
    (Fischer.homogeneousInnerCore n (m + 2))
    (homogeneousRadialMultiplication n m)
    (homogeneousLaplacian n m)
  · intro q p
    exact hpair q p
  · exact homogeneousRadialMultiplication_injective hn m

theorem homogeneousLaplacian_surjective
    {n : ℕ} (hn : 0 < n) (m : ℕ) :
    Function.Surjective (homogeneousLaplacian n m) := by
  apply homogeneousLaplacian_surjective_of_fischer_adjoint hn m
  intro q p
  calc
    Fischer.homogeneousInner n m
        (homogeneousLaplacian n m q) p =
      Fischer.homogeneousInner n m p
        (homogeneousLaplacian n m q) :=
      fischer_homogeneousInner_comm n m
        (homogeneousLaplacian n m q) p
    _ = Fischer.homogeneousInner n (m + 2)
        (homogeneousRadialMultiplication n m p) q :=
      (fischer_homogeneousInner_radial_laplacian n m p q).symm
    _ = Fischer.homogeneousInner n (m + 2)
        q (homogeneousRadialMultiplication n m p) :=
      fischer_homogeneousInner_comm n (m + 2)
        (homogeneousRadialMultiplication n m p) q

theorem homogeneousLaplacian_ker (n m : ℕ) :
    LinearMap.ker (homogeneousLaplacian n m) =
      (LinearMap.ker (polynomialLaplacian n)).comap
        (MvPolynomial.homogeneousSubmodule
          (Fin n) ℝ (m + 2)).subtype := by
  unfold homogeneousLaplacian
  rw [LinearMap.ker_codRestrict, LinearMap.ker_domRestrict]

theorem homogeneousLaplacian_ker_map (n m : ℕ) :
    (LinearMap.ker (homogeneousLaplacian n m)).map
      (MvPolynomial.homogeneousSubmodule
        (Fin n) ℝ (m + 2)).subtype =
        harmonicHomogeneousSubmodule n (m + 2) := by
  rw [homogeneousLaplacian_ker, Submodule.map_comap_subtype]
  rfl

private def harmonicHomogeneousKerEquiv (n m : ℕ) :
    harmonicHomogeneousSubmodule n (m + 2) ≃ₗ[ℝ]
      LinearMap.ker (homogeneousLaplacian n m) :=
  (LinearEquiv.ofEq _ _
    (homogeneousLaplacian_ker_map n m).symm).trans
      (Submodule.equivSubtypeMap
        (MvPolynomial.homogeneousSubmodule (Fin n) ℝ (m + 2))
        (LinearMap.ker (homogeneousLaplacian n m))).symm

instance harmonicHomogeneousSubmodule_finiteDimensional (n m : ℕ) :
    FiniteDimensional ℝ (harmonicHomogeneousSubmodule n m) :=
  FiniteDimensional.of_injective
    (Submodule.inclusion
      (show harmonicHomogeneousSubmodule n m ≤
        MvPolynomial.homogeneousSubmodule (Fin n) ℝ m from
        inf_le_left))
    (Submodule.inclusion_injective
      (show harmonicHomogeneousSubmodule n m ≤
        MvPolynomial.homogeneousSubmodule (Fin n) ℝ m from
        inf_le_left))

theorem polynomialLaplacian_eq_zero_of_isHomogeneous_le_one
    {n m : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p.IsHomogeneous m) (hm : m ≤ 1) :
    polynomialLaplacian n p = 0 := by
  rw [polynomialLaplacian_apply]
  apply Finset.sum_eq_zero
  intro i hi
  have hd :
      (MvPolynomial.pderiv i p).IsHomogeneous 0 := by
    simpa only [Nat.sub_eq_zero_of_le hm] using hp.pderiv (i := i)
  have hdeg :
      (MvPolynomial.pderiv i p).totalDegree = 0 :=
    (MvPolynomial.totalDegree_zero_iff_isHomogeneous
      (Fin n)).mpr hd
  have hconst :
      MvPolynomial.pderiv i p =
        MvPolynomial.C
          (MvPolynomial.coeff 0 (MvPolynomial.pderiv i p)) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg
  rw [hconst, MvPolynomial.pderiv_C]

theorem harmonicHomogeneousSubmodule_eq_homogeneous_of_le_one
    {n m : ℕ} (hm : m ≤ 1) :
    harmonicHomogeneousSubmodule n m =
      MvPolynomial.homogeneousSubmodule (Fin n) ℝ m := by
  unfold harmonicHomogeneousSubmodule
  apply inf_eq_left.mpr
  intro p hp
  apply LinearMap.mem_ker.mpr
  exact polynomialLaplacian_eq_zero_of_isHomogeneous_le_one p hp hm

theorem harmonicDimension_succ_succ_add_choose
    {n : ℕ} (hn : 0 < n) (m : ℕ) :
    Gegenbauer.harmonicDimension n (m + 2) + (n + m - 1).choose m =
      (n + m + 1).choose (m + 2) := by
  have hdim :
      Gegenbauer.harmonicDimension n (m + 2) =
        (n + m).choose (m + 2) +
          (n + m - 1).choose (m + 1) := by
    rw [show m + 2 = (m + 1) + 1 by omega,
      Gegenbauer.harmonicDimension_succ]
    congr 1
  have hfirst :
      (n + m + 1).choose (m + 2) =
        (n + m).choose (m + 1) +
          (n + m).choose (m + 2) := by
    simpa only [Nat.add_assoc, Nat.succ_eq_add_one,
      Nat.reduceAdd] using Nat.choose_succ_succ (n + m) (m + 1)
  have hsecond :
      (n + m).choose (m + 1) =
        (n + m - 1).choose m +
          (n + m - 1).choose (m + 1) := by
    calc
      (n + m).choose (m + 1) =
          ((n + m - 1) + 1).choose (m + 1) := by
            congr 1
            omega
      _ = _ := Nat.choose_succ_succ (n + m - 1) m
  rw [hdim, hfirst, hsecond]
  omega

theorem finrank_harmonicHomogeneousSubmodule_of_le_one
    {n m : ℕ} (hn : 0 < n) (hm : m ≤ 1) :
    Module.finrank ℝ (harmonicHomogeneousSubmodule n m) =
      Gegenbauer.harmonicDimension n m := by
  have heq := harmonicHomogeneousSubmodule_eq_homogeneous_of_le_one
    (n := n) hm
  calc
    Module.finrank ℝ (harmonicHomogeneousSubmodule n m) =
        Module.finrank ℝ
          (MvPolynomial.homogeneousSubmodule (Fin n) ℝ m) :=
      (LinearEquiv.ofEq _ _ heq).finrank_eq
    _ = (n + m - 1).choose m :=
      finrank_homogeneousSubmodule n m
    _ = Gegenbauer.harmonicDimension n m := by
      interval_cases m
      · simp only [add_zero, Nat.choose_zero_right, Gegenbauer.harmonicDimension]
      · simp only [add_tsub_cancel_right, Nat.choose_one_right, Gegenbauer.harmonicDimension,
          add_zero, zero_add, Nat.choose_zero_right]
        omega

theorem finrank_harmonicHomogeneousSubmodule_succ_succ_of_surjective
    {n : ℕ} (hn : 0 < n) (m : ℕ)
    (h : Function.Surjective (homogeneousLaplacian n m)) :
    Module.finrank ℝ (harmonicHomogeneousSubmodule n (m + 2)) =
      Gegenbauer.harmonicDimension n (m + 2) := by
  have hrank :=
    (homogeneousLaplacian n m).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr h, finrank_top] at hrank
  simp only [finrank_homogeneousSubmodule] at hrank
  have hker := (harmonicHomogeneousKerEquiv n m).finrank_eq
  have hdim := harmonicDimension_succ_succ_add_choose hn m
  have hindex : n + (m + 2) - 1 = n + m + 1 := by omega
  rw [hindex] at hrank
  omega

theorem finrank_harmonicHomogeneousSubmodule
    {n : ℕ} (hn : 0 < n) (m : ℕ) :
    Module.finrank ℝ (harmonicHomogeneousSubmodule n m) =
      Gegenbauer.harmonicDimension n m := by
  cases m with
  | zero =>
      exact finrank_harmonicHomogeneousSubmodule_of_le_one hn (by omega)
  | succ m =>
      cases m with
      | zero =>
          exact finrank_harmonicHomogeneousSubmodule_of_le_one hn
            (by omega)
      | succ m =>
          exact
            finrank_harmonicHomogeneousSubmodule_succ_succ_of_surjective
              hn m (homogeneousLaplacian_surjective hn m)

theorem polynomialLaplacian_radialPolynomial (n : ℕ) :
    polynomialLaplacian n (radialPolynomial n) =
      MvPolynomial.C (2 * (n : ℝ)) := by
  classical
  have htwo : (2 : MvPolynomial (Fin n) ℝ) =
      MvPolynomial.C (2 : ℝ) := by
    exact (map_ofNat
      (MvPolynomial.C : ℝ →+* MvPolynomial (Fin n) ℝ) 2).symm
  simp only [polynomialLaplacian_apply, pderiv_radialPolynomial, htwo, Derivation.leibniz,
    MvPolynomial.pderiv_X, Pi.single_eq_same, smul_eq_mul, mul_one, MvPolynomial.derivation_C,
    mul_zero, add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    MvPolynomial.C_mul, map_natCast]
  ring

theorem polynomialLaplacian_mul {n : ℕ}
    (p q : MvPolynomial (Fin n) ℝ) :
    polynomialLaplacian n (p * q) =
      polynomialLaplacian n p * q +
        2 * (∑ i : Fin n,
          MvPolynomial.pderiv i p * MvPolynomial.pderiv i q) +
        p * polynomialLaplacian n q := by
  classical
  simp only [polynomialLaplacian_apply]
  calc
    (∑ i : Fin n,
        MvPolynomial.pderiv i
          (MvPolynomial.pderiv i (p * q))) =
      ∑ i : Fin n,
        (MvPolynomial.pderiv i (MvPolynomial.pderiv i p) * q +
          2 * (MvPolynomial.pderiv i p *
            MvPolynomial.pderiv i q) +
          p * MvPolynomial.pderiv i
            (MvPolynomial.pderiv i q)) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [MvPolynomial.pderiv_mul, map_add]
        ring
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]
      rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum]

theorem polynomialLaplacian_radial_mul {n m : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (hp : p.IsHomogeneous m) :
    polynomialLaplacian n (radialPolynomial n * p) =
      MvPolynomial.C (2 * (2 * (m : ℝ) + n)) * p +
        radialPolynomial n * polynomialLaplacian n p := by
  classical
  have heuler :
      (∑ i : Fin n,
        MvPolynomial.X i * MvPolynomial.pderiv i p) =
        MvPolynomial.C (m : ℝ) * p := by
    simpa only [map_natCast, nsmul_eq_mul] using hp.sum_X_mul_pderiv
  have hcross :
      (∑ i : Fin n,
        (2 * MvPolynomial.X i) * MvPolynomial.pderiv i p) =
        2 * (MvPolynomial.C (m : ℝ) * p) := by
    calc
      (∑ i : Fin n,
        (2 * MvPolynomial.X i) * MvPolynomial.pderiv i p) =
          2 * (∑ i : Fin n,
            MvPolynomial.X i * MvPolynomial.pderiv i p) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = _ := by rw [heuler]
  rw [polynomialLaplacian_mul,
    polynomialLaplacian_radialPolynomial]
  simp_rw [pderiv_radialPolynomial]
  rw [hcross]
  simp only [map_add, map_mul, map_ofNat]
  ring

end

section


open scoped BigOperators InnerProductSpace

theorem solidHarmonicAxis_polynomialLaplacian_axis_mul
    {n : ℕ} (x : Euclidean n) (p : MvPolynomial (Fin n) ℝ) :
    polynomialLaplacian n (axisPolynomial n x * p) =
      2 * directionalDerivative n x p +
        axisPolynomial n x * polynomialLaplacian n p := by
  classical
  have hcross :
      (∑ i : Fin n,
        MvPolynomial.pderiv i (axisPolynomial n x) *
          MvPolynomial.pderiv i p) =
        directionalDerivative n x p := by
    rw [directionalDerivative_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pderiv_axisPolynomial, MvPolynomial.C_mul']
  rw [polynomialLaplacian_mul,
    polynomialLaplacian_axisPolynomial, zero_mul, zero_add,
    hcross]

theorem directionalDerivative_radialPolynomial
    {n : ℕ} (x : Euclidean n) :
    directionalDerivative n x (radialPolynomial n) =
      2 * axisPolynomial n x := by
  classical
  calc
    directionalDerivative n x (radialPolynomial n) =
        ∑ i : Fin n, x i • (2 * MvPolynomial.X i) := by
          simp only [directionalDerivative_apply, pderiv_radialPolynomial]
    _ = 2 * (∑ i : Fin n,
          MvPolynomial.C (x i) * MvPolynomial.X i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [← MvPolynomial.C_mul']
          ring
    _ = 2 * axisPolynomial n x := rfl

theorem directionalDerivative_radial_mul
    {n : ℕ} (x : Euclidean n) (p : MvPolynomial (Fin n) ℝ) :
    directionalDerivative n x (radialPolynomial n * p) =
      2 * axisPolynomial n x * p +
        radialPolynomial n * directionalDerivative n x p := by
  rw [directionalDerivative_mul,
    directionalDerivative_radialPolynomial]

theorem polynomialLaplacian_C_mul
    {n : ℕ} (c : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    polynomialLaplacian n (MvPolynomial.C c * p) =
      MvPolynomial.C c * polynomialLaplacian n p := by
  rw [MvPolynomial.C_mul', map_smul, MvPolynomial.C_mul']

theorem directionalDerivative_C_mul
    {n : ℕ} (x : Euclidean n) (c : ℝ)
    (p : MvPolynomial (Fin n) ℝ) :
    directionalDerivative n x (MvPolynomial.C c * p) =
      MvPolynomial.C c * directionalDerivative n x p := by
  rw [MvPolynomial.C_mul', map_smul, MvPolynomial.C_mul']

/-- The harmonic axis parameter used in the spherical-code argument. -/
def harmonicAxisParameter (n k : ℕ) : ℝ :=
  (n : ℝ) + 2 * (k : ℝ)

/-- The solid harmonic axis lift used in the spherical-code argument. -/
def solidHarmonicAxisLift (n k : ℕ) (x : Euclidean n) :
    ℕ → (MvPolynomial (Fin n) ℝ →ₗ[ℝ]
      MvPolynomial (Fin n) ℝ)
  | 0 => LinearMap.id
  | 1 =>
      LinearMap.mulLeft ℝ
        (MvPolynomial.C (harmonicAxisParameter n k - 2) *
          axisPolynomial n x)
  | r + 2 =>
      (LinearMap.mulLeft ℝ
        (MvPolynomial.C
          (2 * ((r + 1 : ℕ) : ℝ) +
            harmonicAxisParameter n k - 2) *
          axisPolynomial n x)).comp
            (solidHarmonicAxisLift n k x (r + 1)) -
      (LinearMap.mulLeft ℝ
        (MvPolynomial.C
          (((r + 1 : ℕ) : ℝ) *
            (((r + 1 : ℕ) : ℝ) +
              harmonicAxisParameter n k - 3)) *
          radialPolynomial n)).comp
            (solidHarmonicAxisLift n k x r)

@[simp] theorem solidHarmonicAxisLift_zero_apply
    (n k : ℕ) (x : Euclidean n)
    (p : MvPolynomial (Fin n) ℝ) :
    solidHarmonicAxisLift n k x 0 p = p := rfl

@[simp] theorem solidHarmonicAxisLift_one_apply
    (n k : ℕ) (x : Euclidean n)
    (p : MvPolynomial (Fin n) ℝ) :
    solidHarmonicAxisLift n k x 1 p =
      (MvPolynomial.C (harmonicAxisParameter n k - 2) *
        axisPolynomial n x) * p := rfl

@[simp] theorem solidHarmonicAxisLift_succ_succ_apply
    (n k r : ℕ) (x : Euclidean n)
    (p : MvPolynomial (Fin n) ℝ) :
    solidHarmonicAxisLift n k x (r + 2) p =
      (MvPolynomial.C
        (2 * ((r + 1 : ℕ) : ℝ) +
          harmonicAxisParameter n k - 2) *
        axisPolynomial n x) *
          solidHarmonicAxisLift n k x (r + 1) p -
      (MvPolynomial.C
        (((r + 1 : ℕ) : ℝ) *
          (((r + 1 : ℕ) : ℝ) +
            harmonicAxisParameter n k - 3)) *
        radialPolynomial n) *
          solidHarmonicAxisLift n k x r p := rfl

theorem solidHarmonicAxisLift_isHomogeneous
    {n k : ℕ} (x : Euclidean n)
    {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous k) (r : ℕ) :
    (solidHarmonicAxisLift n k x r p).IsHomogeneous (k + r) := by
  induction r using Nat.twoStepInduction with
  | zero =>
      simpa only [solidHarmonicAxisLift_zero_apply, add_zero] using hp
  | one =>
      rw [solidHarmonicAxisLift_one_apply]
      have haxis :=
        (MvPolynomial.isHomogeneous_C (Fin n)
          (harmonicAxisParameter n k - 2)).mul
            (axisPolynomial_isHomogeneous x)
      simpa only [MvPolynomial.C_sub, zero_add, Nat.add_comm] using haxis.mul hp
  | more r ihr ihrs =>
      rw [solidHarmonicAxisLift_succ_succ_apply]
      apply MvPolynomial.IsHomogeneous.sub
      · have haxis :=
          (MvPolynomial.isHomogeneous_C (Fin n)
            (2 * ((r + 1 : ℕ) : ℝ) +
              harmonicAxisParameter n k - 2)).mul
                (axisPolynomial_isHomogeneous x)
        have h := haxis.mul ihrs
        simpa only [Nat.cast_add, Nat.cast_one, MvPolynomial.C_sub, MvPolynomial.C_add,
          MvPolynomial.C_mul, map_natCast, MvPolynomial.C_1, zero_add, Nat.add_left_comm,
          Nat.reduceAdd] using h
      · have hradial :=
          (MvPolynomial.isHomogeneous_C (Fin n)
            (((r + 1 : ℕ) : ℝ) *
              (((r + 1 : ℕ) : ℝ) +
                harmonicAxisParameter n k - 3))).mul
                  (radialPolynomial_isHomogeneous n)
        have h := hradial.mul ihr
        simpa only [Nat.cast_add, Nat.cast_one, MvPolynomial.C_mul, MvPolynomial.C_add, map_natCast,
          MvPolynomial.C_1, MvPolynomial.C_sub, zero_add, Nat.add_comm, Nat.add_assoc] using h

theorem fischer_harmonicInner_eq_polynomialInner
    (n k : ℕ) (p q : harmonicHomogeneousSubmodule n k) :
    Fischer.harmonicInner n k p q =
      Fischer.polynomialInner n
        (p : MvPolynomial (Fin n) ℝ)
        (q : MvPolynomial (Fin n) ℝ) := by
  change
    Fischer.homogeneousInner n k
      (Submodule.inclusion
        (show harmonicHomogeneousSubmodule n k ≤
          MvPolynomial.homogeneousSubmodule (Fin n) ℝ k from
          inf_le_left) p)
      (Submodule.inclusion
        (show harmonicHomogeneousSubmodule n k ≤
          MvPolynomial.homogeneousSubmodule (Fin n) ℝ k from
          inf_le_left) q) = _
  exact Fischer.homogeneousInner_eq_polynomialInner n k _ _

theorem fischer_harmonicInner_self_nonneg
    (n k : ℕ) (p : harmonicHomogeneousSubmodule n k) :
    0 ≤ Fischer.harmonicInner n k p p := by
  unfold Fischer.harmonicInner
  exact real_inner_self_nonneg

theorem fischer_harmonicInner_self_eq_zero_iff
    (n k : ℕ) (p : harmonicHomogeneousSubmodule n k) :
    Fischer.harmonicInner n k p p = 0 ↔ p = 0 := by
  constructor
  · intro hp
    unfold Fischer.harmonicInner at hp
    have hzero : Fischer.harmonicCoefficientEmbedding n k p = 0 :=
      inner_self_eq_zero.mp hp
    apply Fischer.harmonicCoefficientEmbedding_injective n k
    simpa only [map_zero] using hzero
  · intro hp
    subst p
    simp only [Fischer.harmonicInner, map_zero, inner_self_eq_norm_sq_to_K, norm_zero,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]

theorem fischer_harmonicInner_comm
    (n k : ℕ) (p q : harmonicHomogeneousSubmodule n k) :
    Fischer.harmonicInner n k p q =
      Fischer.harmonicInner n k q p := by
  unfold Fischer.harmonicInner
  exact real_inner_comm _ _

theorem directionalDerivative_eq_zero_of_isHomogeneous_zero
    {n : ℕ} (x : Euclidean n)
    (p : MvPolynomial (Fin n) ℝ)
    (hp : p.IsHomogeneous 0) :
    directionalDerivative n x p = 0 := by
  have hdeg : p.totalDegree = 0 :=
    (MvPolynomial.totalDegree_zero_iff_isHomogeneous
      (Fin n)).mpr hp
  have hconst : p = MvPolynomial.C (MvPolynomial.coeff 0 p) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg
  rw [hconst, directionalDerivative_apply]
  simp only [MvPolynomial.derivation_C, smul_zero, Finset.sum_const_zero]

theorem fischer_polynomialInner_zero_right
    (n : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    Fischer.polynomialInner n p 0 = 0 := by
  simp only [Fischer.polynomialInner, MvPolynomial.coeff_zero, mul_zero, Finsupp.sum_fun_zero]

theorem fischer_polynomialInner_sub_left
    (n : ℕ) (p q r : MvPolynomial (Fin n) ℝ) :
    Fischer.polynomialInner n (p - q) r =
      Fischer.polynomialInner n p r -
        Fischer.polynomialInner n q r := by
  rw [sub_eq_add_neg, Fischer.polynomialInner_add_left]
  have hneg :
      Fischer.polynomialInner n (-q) r =
        -Fischer.polynomialInner n q r := by
    simpa only [neg_smul, one_smul, neg_mul,
      one_mul] using Fischer.polynomialInner_smul_left n (-1 : ℝ) q r
  rw [hneg]
  ring

theorem fischer_polynomialInner_radial_harmonic
    {n k : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (q : harmonicHomogeneousSubmodule n k) :
    Fischer.polynomialInner n
      (radialPolynomial n * p)
      (q : MvPolynomial (Fin n) ℝ) = 0 := by
  unfold radialPolynomial
  rw [Fischer.polynomialInner_radial_laplacian]
  have hq := (mem_harmonicHomogeneousSubmodule
    (q : MvPolynomial (Fin n) ℝ)).mp q.property
  rw [hq.2]
  exact fischer_polynomialInner_zero_right n p

theorem polynomialLaplacian_axis_mul_for_tangent
    {n : ℕ} (x : Euclidean n) (p : MvPolynomial (Fin n) ℝ) :
    polynomialLaplacian n (axisPolynomial n x * p) =
      2 * directionalDerivative n x p +
        axisPolynomial n x * polynomialLaplacian n p := by
  rw [polynomialLaplacian_mul,
    polynomialLaplacian_axisPolynomial]
  simp only [zero_mul, zero_add, pderiv_axisPolynomial]
  rw [directionalDerivative_apply]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  exact MvPolynomial.C_mul'

private def harmonicAxisProjectionDenominator (n k : ℕ) : ℝ :=
  2 * (k : ℝ) + (n : ℝ)

theorem harmonicAxisProjectionDenominator_pos
    {n : ℕ} (hn : 0 < n) (k : ℕ) :
    0 < harmonicAxisProjectionDenominator n k := by
  unfold harmonicAxisProjectionDenominator
  positivity

/-- The harmonic axis projection operator used in the spherical-code argument. -/
def harmonicAxisProjectionOperator
    (n k : ℕ) (x : Euclidean n) :
    MvPolynomial (Fin n) ℝ →ₗ[ℝ]
      MvPolynomial (Fin n) ℝ :=
  LinearMap.mulLeft ℝ (axisPolynomial n x) -
    (harmonicAxisProjectionDenominator n k)⁻¹ •
      (LinearMap.mulLeft ℝ (radialPolynomial n)).comp
        (directionalDerivative n x)

@[simp] theorem harmonicAxisProjectionOperator_apply
    (n k : ℕ) (x : Euclidean n)
    (p : MvPolynomial (Fin n) ℝ) :
    harmonicAxisProjectionOperator n k x p =
      axisPolynomial n x * p -
        (harmonicAxisProjectionDenominator n k)⁻¹ •
          (radialPolynomial n * directionalDerivative n x p) := by
  rfl

theorem harmonicAxisProjectionOperator_mem_harmonic
    {n : ℕ} (hn : 0 < n) (k : ℕ) (x : Euclidean n)
    {p : MvPolynomial (Fin n) ℝ}
    (hp : p ∈ harmonicHomogeneousSubmodule n (k + 1)) :
    harmonicAxisProjectionOperator n k x p ∈
      harmonicHomogeneousSubmodule n (k + 2) := by
  have hp' := (mem_harmonicHomogeneousSubmodule p).mp hp
  have hplap : polynomialLaplacian n p = 0 := by
    simpa only [polynomialLaplacian_apply] using hp'.2
  have hdmem := directionalDerivative_mem_harmonic x hp
  have hd' := (mem_harmonicHomogeneousSubmodule
    (directionalDerivative n x p)).mp hdmem
  have hdlap :
      polynomialLaplacian n (directionalDerivative n x p) = 0 := by
    simpa only [polynomialLaplacian_apply] using hd'.2
  apply (mem_harmonicHomogeneousSubmodule
    (harmonicAxisProjectionOperator n k x p)).mpr
  constructor
  · rw [harmonicAxisProjectionOperator_apply]
    change
      axisPolynomial n x * p -
        (harmonicAxisProjectionDenominator n k)⁻¹ •
          (radialPolynomial n * directionalDerivative n x p) ∈
        MvPolynomial.homogeneousSubmodule (Fin n) ℝ (k + 2)
    apply (MvPolynomial.homogeneousSubmodule
      (Fin n) ℝ (k + 2)).sub_mem
    · have hindex : 1 + (k + 1) = k + 2 := by omega
      rw [← hindex]
      exact (axisPolynomial_isHomogeneous x).mul hp'.1
    · apply (MvPolynomial.homogeneousSubmodule
        (Fin n) ℝ (k + 2)).smul_mem
      simpa only [directionalDerivative_apply, MvPolynomial.mem_homogeneousSubmodule,
        Nat.add_comm] using
        (radialPolynomial_isHomogeneous n).mul hd'.1
  · rw [← polynomialLaplacian_apply,
      harmonicAxisProjectionOperator_apply,
      map_sub, map_smul,
      polynomialLaplacian_axis_mul_for_tangent,
      polynomialLaplacian_radial_mul _ hd'.1,
      hplap, hdlap]
    simp only [mul_zero, add_zero]
    have htwo : (2 : MvPolynomial (Fin n) ℝ) =
        MvPolynomial.C (2 : ℝ) := by
      exact (map_ofNat
        (MvPolynomial.C : ℝ →+* MvPolynomial (Fin n) ℝ) 2).symm
    rw [htwo, MvPolynomial.C_mul', MvPolynomial.C_mul', smul_smul]
    have hden : harmonicAxisProjectionDenominator n k ≠ 0 :=
      ne_of_gt (harmonicAxisProjectionDenominator_pos hn k)
    have hscalar :
        (harmonicAxisProjectionDenominator n k)⁻¹ *
          (2 * (2 * (k : ℝ) + n)) = (2 : ℝ) := by
      unfold harmonicAxisProjectionDenominator at hden ⊢
      field_simp
    rw [hscalar, sub_self]

/-- The harmonic axis lift used in the spherical-code argument. -/
def harmonicAxisLift
    {n : ℕ} (hn : 0 < n) (k : ℕ) (x : Euclidean n) :
    harmonicHomogeneousSubmodule n (k + 1) →ₗ[ℝ]
      harmonicHomogeneousSubmodule n (k + 2) :=
  (harmonicAxisProjectionOperator n k x).restrict
    (fun _ hp => harmonicAxisProjectionOperator_mem_harmonic
      hn k x hp)

@[simp] theorem harmonicAxisLift_apply
    {n : ℕ} (hn : 0 < n) (k : ℕ) (x : Euclidean n)
    (p : harmonicHomogeneousSubmodule n (k + 1)) :
    ((harmonicAxisLift hn k x p :
      harmonicHomogeneousSubmodule n (k + 2)) :
        MvPolynomial (Fin n) ℝ) =
      harmonicAxisProjectionOperator n k x
        (p : MvPolynomial (Fin n) ℝ) := rfl

theorem harmonicAxisLift_fischer_adjoint
    {n : ℕ} (hn : 0 < n) (k : ℕ) (x : Euclidean n)
    (p : harmonicHomogeneousSubmodule n (k + 1))
    (q : harmonicHomogeneousSubmodule n (k + 2)) :
    Fischer.harmonicInner n (k + 2)
        (harmonicAxisLift hn k x p) q =
      Fischer.harmonicInner n (k + 1) p
        (harmonicDirectionalDerivative n (k + 1) x q) := by
  calc
    Fischer.harmonicInner n (k + 2)
        (harmonicAxisLift hn k x p) q =
      Fischer.polynomialInner n
        (harmonicAxisProjectionOperator n k x
          (p : MvPolynomial (Fin n) ℝ))
        (q : MvPolynomial (Fin n) ℝ) := by
        rw [fischer_harmonicInner_eq_polynomialInner]
        rfl
    _ = Fischer.polynomialInner n
        (axisPolynomial n x *
          (p : MvPolynomial (Fin n) ℝ))
        (q : MvPolynomial (Fin n) ℝ) := by
        rw [harmonicAxisProjectionOperator_apply,
          fischer_polynomialInner_sub_left,
          Fischer.polynomialInner_smul_left,
          fischer_polynomialInner_radial_harmonic
            (directionalDerivative n x
              (p : MvPolynomial (Fin n) ℝ)) q,
          mul_zero, sub_zero]
    _ = Fischer.polynomialInner n
        (p : MvPolynomial (Fin n) ℝ)
        (directionalDerivative n x
          (q : MvPolynomial (Fin n) ℝ)) :=
      Fischer.polynomialInner_axis_directional n x
        (p : MvPolynomial (Fin n) ℝ)
        (q : MvPolynomial (Fin n) ℝ)
    _ = Fischer.harmonicInner n (k + 1) p
        (harmonicDirectionalDerivative n (k + 1) x q) := by
        rw [fischer_harmonicInner_eq_polynomialInner]
        rfl

theorem harmonicAxisProjectionOperator_pair_axis
    {n : ℕ} (k : ℕ) (x : Euclidean n)
    (hx : ‖x‖ = 1)
    (p : harmonicHomogeneousSubmodule n (k + 1)) :
    Fischer.polynomialInner n
        (harmonicAxisProjectionOperator n k x
          (p : MvPolynomial (Fin n) ℝ))
        (axisPolynomial n x *
          (p : MvPolynomial (Fin n) ℝ)) =
      Fischer.harmonicInner n (k + 1) p p +
        (1 - 2 * (harmonicAxisProjectionDenominator n k)⁻¹) *
          Fischer.harmonicInner n k
            (harmonicDirectionalDerivative n k x p)
            (harmonicDirectionalDerivative n k x p) := by
  let dp := harmonicDirectionalDerivative n k x p
  have hself :
      Fischer.polynomialInner n
        (p : MvPolynomial (Fin n) ℝ)
        (p : MvPolynomial (Fin n) ℝ) =
          Fischer.harmonicInner n (k + 1) p p :=
    (fischer_harmonicInner_eq_polynomialInner
      n (k + 1) p p).symm
  have hdself :
      Fischer.polynomialInner n
        (directionalDerivative n x
          (p : MvPolynomial (Fin n) ℝ))
        (directionalDerivative n x
          (p : MvPolynomial (Fin n) ℝ)) =
          Fischer.harmonicInner n k dp dp := by
    exact (fischer_harmonicInner_eq_polynomialInner n k dp dp).symm
  have haxis :
      Fischer.polynomialInner n
        (axisPolynomial n x *
          (p : MvPolynomial (Fin n) ℝ))
        (axisPolynomial n x *
          (p : MvPolynomial (Fin n) ℝ)) =
        Fischer.harmonicInner n (k + 1) p p +
          Fischer.harmonicInner n k dp dp := by
    rw [Fischer.polynomialInner_axis_directional,
      directionalDerivative_mul,
      directionalDerivative_axisPolynomial_self x hx,
      one_mul,
      Fischer.polynomialInner_add_right]
    rw [Fischer.polynomialInner_comm n
      (p : MvPolynomial (Fin n) ℝ)
      (axisPolynomial n x *
        directionalDerivative n x
          (p : MvPolynomial (Fin n) ℝ)),
      Fischer.polynomialInner_axis_directional,
      hself, hdself]
  have hplap :
      polynomialLaplacian n
        (p : MvPolynomial (Fin n) ℝ) = 0 := by
    have hp := (mem_harmonicHomogeneousSubmodule
      (p : MvPolynomial (Fin n) ℝ)).mp p.property
    simpa only [polynomialLaplacian_apply] using hp.2
  have hrad :
      Fischer.polynomialInner n
        (radialPolynomial n * directionalDerivative n x
          (p : MvPolynomial (Fin n) ℝ))
        (axisPolynomial n x *
          (p : MvPolynomial (Fin n) ℝ)) =
        2 * Fischer.harmonicInner n k dp dp := by
    unfold radialPolynomial
    rw [Fischer.polynomialInner_radial_laplacian]
    rw [← polynomialLaplacian_apply,
      polynomialLaplacian_axis_mul_for_tangent,
      hplap, mul_zero, add_zero]
    have htwo : (2 : MvPolynomial (Fin n) ℝ) =
        MvPolynomial.C (2 : ℝ) := by
      exact (map_ofNat
        (MvPolynomial.C : ℝ →+* MvPolynomial (Fin n) ℝ) 2).symm
    rw [htwo, MvPolynomial.C_mul',
      Fischer.polynomialInner_smul_right, hdself]
  rw [harmonicAxisProjectionOperator_apply,
    fischer_polynomialInner_sub_left,
    Fischer.polynomialInner_smul_left,
    haxis, hrad]
  change
    Fischer.harmonicInner n (k + 1) p p +
        Fischer.harmonicInner n k dp dp -
        (harmonicAxisProjectionDenominator n k)⁻¹ *
          (2 * Fischer.harmonicInner n k dp dp) = _
  dsimp only [dp]
  ring

theorem harmonicAxisProjection_correction_nonneg
    {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    0 ≤ 1 - 2 * (harmonicAxisProjectionDenominator n k)⁻¹ := by
  have hnreal : (2 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hkreal : 0 ≤ (k : ℝ) := by positivity
  have hden :
      (2 : ℝ) ≤ harmonicAxisProjectionDenominator n k := by
    unfold harmonicAxisProjectionDenominator
    nlinarith
  have hpos := harmonicAxisProjectionDenominator_pos
    (show 0 < n by omega) k
  apply sub_nonneg.mpr
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ hpos).mpr
  nlinarith

theorem harmonicAxisLift_injective
    {n : ℕ} (hn : 2 ≤ n) (k : ℕ)
    (x : Euclidean n) (hx : ‖x‖ = 1) :
    Function.Injective
      (harmonicAxisLift (show 0 < n by omega) k x) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro p hp
  have hpoly :
      harmonicAxisProjectionOperator n k x
        (p : MvPolynomial (Fin n) ℝ) = 0 := by
    have hz := congrArg
      (fun q : harmonicHomogeneousSubmodule n (k + 2) =>
        (q : MvPolynomial (Fin n) ℝ)) hp
    simpa only [harmonicAxisProjectionOperator_apply, directionalDerivative_apply,
      harmonicAxisLift_apply, ZeroMemClass.coe_zero] using hz
  have hzero :
      Fischer.polynomialInner n
        (harmonicAxisProjectionOperator n k x
          (p : MvPolynomial (Fin n) ℝ))
        (axisPolynomial n x *
          (p : MvPolynomial (Fin n) ℝ)) = 0 := by
    rw [hpoly]
    simp only [Fischer.polynomialInner, AddMonoidAlgebra.coeff_zero, Finsupp.sum_zero_index]
  have hidentity :=
    harmonicAxisProjectionOperator_pair_axis k x hx p
  rw [hzero] at hidentity
  have hpnonneg :=
    fischer_harmonicInner_self_nonneg n (k + 1) p
  have hdnonneg := fischer_harmonicInner_self_nonneg n k
    (harmonicDirectionalDerivative n k x p)
  have hc := harmonicAxisProjection_correction_nonneg hn k
  have hproduct := mul_nonneg hc hdnonneg
  have hpzero : Fischer.harmonicInner n (k + 1) p p = 0 := by
    nlinarith
  exact (fischer_harmonicInner_self_eq_zero_iff
    n (k + 1) p).mp hpzero

theorem harmonicDirectionalDerivative_surjective_succ
    {n : ℕ} (hn : 2 ≤ n) (k : ℕ)
    (x : Euclidean n) (hx : ‖x‖ = 1) :
    Function.Surjective
      (harmonicDirectionalDerivative n (k + 1) x) := by
  apply surjective_of_injective_inner_adjoint
    (Fischer.harmonicInnerCore n (k + 1))
    (Fischer.harmonicInnerCore n (k + 2))
    (harmonicAxisLift (show 0 < n by omega) k x)
    (harmonicDirectionalDerivative n (k + 1) x)
  · intro q p
    change
      Fischer.harmonicInner n (k + 1)
          (harmonicDirectionalDerivative n (k + 1) x q) p =
        Fischer.harmonicInner n (k + 2) q
          (harmonicAxisLift (show 0 < n by omega) k x p)
    calc
      Fischer.harmonicInner n (k + 1)
          (harmonicDirectionalDerivative n (k + 1) x q) p =
        Fischer.harmonicInner n (k + 1) p
          (harmonicDirectionalDerivative n (k + 1) x q) :=
        fischer_harmonicInner_comm n (k + 1)
          (harmonicDirectionalDerivative n (k + 1) x q) p
      _ = Fischer.harmonicInner n (k + 2)
          (harmonicAxisLift (show 0 < n by omega) k x p) q :=
        (harmonicAxisLift_fischer_adjoint
          (show 0 < n by omega) k x p q).symm
      _ = Fischer.harmonicInner n (k + 2) q
          (harmonicAxisLift (show 0 < n by omega) k x p) :=
        fischer_harmonicInner_comm n (k + 2)
          (harmonicAxisLift (show 0 < n by omega) k x p) q
  · exact harmonicAxisLift_injective hn k x hx

theorem harmonicDirectionalDerivative_surjective
    {n : ℕ} (hn : 2 ≤ n) (k : ℕ)
    (x : Euclidean n) (hx : ‖x‖ = 1) :
    Function.Surjective (harmonicDirectionalDerivative n k x) := by
  cases k with
  | zero =>
      intro p
      have hp := (mem_harmonicHomogeneousSubmodule
        (p : MvPolynomial (Fin n) ℝ)).mp p.property
      have hplap :
          polynomialLaplacian n
            (p : MvPolynomial (Fin n) ℝ) = 0 := by
        simpa only [polynomialLaplacian_apply] using hp.2
      have hpderiv :
          directionalDerivative n x
            (p : MvPolynomial (Fin n) ℝ) = 0 :=
        directionalDerivative_eq_zero_of_isHomogeneous_zero
          x (p : MvPolynomial (Fin n) ℝ) hp.1
      have haxis :
          axisPolynomial n x *
            (p : MvPolynomial (Fin n) ℝ) ∈
              harmonicHomogeneousSubmodule n 1 := by
        apply (mem_harmonicHomogeneousSubmodule
          (axisPolynomial n x *
            (p : MvPolynomial (Fin n) ℝ))).mpr
        constructor
        · simpa only [add_zero] using (axisPolynomial_isHomogeneous x).mul hp.1
        · rw [← polynomialLaplacian_apply,
            polynomialLaplacian_axis_mul_for_tangent,
            hpderiv, hplap]
          simp only [mul_zero, add_zero]
      refine ⟨⟨axisPolynomial n x *
        (p : MvPolynomial (Fin n) ℝ), haxis⟩, ?_⟩
      apply Subtype.ext
      change
        directionalDerivative n x
          (axisPolynomial n x *
            (p : MvPolynomial (Fin n) ℝ)) =
          (p : MvPolynomial (Fin n) ℝ)
      rw [directionalDerivative_mul,
        directionalDerivative_axisPolynomial_self x hx,
        hpderiv]
      simp only [one_mul, mul_zero, add_zero]
  | succ k =>
      exact harmonicDirectionalDerivative_surjective_succ
        hn k x hx

theorem harmonicDirectionalDerivative_ker
    (n k : ℕ) (x : Euclidean n) :
    LinearMap.ker (harmonicDirectionalDerivative n k x) =
      (LinearMap.ker (directionalDerivative n x)).comap
        (harmonicHomogeneousSubmodule n (k + 1)).subtype := by
  unfold harmonicDirectionalDerivative
  rw [LinearMap.ker_restrict]

theorem harmonicDirectionalDerivative_ker_map
    (n k : ℕ) (x : Euclidean n) :
    (LinearMap.ker (harmonicDirectionalDerivative n k x)).map
      (harmonicHomogeneousSubmodule n (k + 1)).subtype =
        tangentHarmonicSubmodule n (k + 1) x := by
  rw [harmonicDirectionalDerivative_ker,
    Submodule.map_comap_subtype]
  rfl

private def tangentHarmonicKerEquiv
    (n k : ℕ) (x : Euclidean n) :
    tangentHarmonicSubmodule n (k + 1) x ≃ₗ[ℝ]
      LinearMap.ker (harmonicDirectionalDerivative n k x) :=
  (LinearEquiv.ofEq _ _
    (harmonicDirectionalDerivative_ker_map n k x).symm).trans
      (Submodule.equivSubtypeMap
        (harmonicHomogeneousSubmodule n (k + 1))
        (LinearMap.ker (harmonicDirectionalDerivative n k x))).symm

theorem tangentHarmonicSubmodule_zero_eq_harmonic
    (n : ℕ) (x : Euclidean n) :
    tangentHarmonicSubmodule n 0 x =
      harmonicHomogeneousSubmodule n 0 := by
  unfold tangentHarmonicSubmodule
  apply inf_eq_left.mpr
  intro p hp
  apply LinearMap.mem_ker.mpr
  have hp' := (mem_harmonicHomogeneousSubmodule p).mp hp
  exact directionalDerivative_eq_zero_of_isHomogeneous_zero
    x p hp'.1

theorem finrank_tangentHarmonicSubmodule
    {n : ℕ} (hn : 3 ≤ n) (k : ℕ)
    (x : Euclidean n) (hx : ‖x‖ = 1) :
    Module.finrank ℝ (tangentHarmonicSubmodule n k x) =
      Gegenbauer.fibreDimension n k := by
  have hnpos : 0 < n := by omega
  cases k with
  | zero =>
      calc
        Module.finrank ℝ
            (tangentHarmonicSubmodule n 0 x) =
          Module.finrank ℝ
            (harmonicHomogeneousSubmodule n 0) :=
          (LinearEquiv.ofEq _ _
            (tangentHarmonicSubmodule_zero_eq_harmonic n x)).finrank_eq
        _ = Gegenbauer.harmonicDimension n 0 :=
          finrank_harmonicHomogeneousSubmodule hnpos 0
        _ = Gegenbauer.fibreDimension n 0 := by
          simp only [Gegenbauer.harmonicDimension_zero, Gegenbauer.fibreDimension]
  | succ k =>
      have hsurj := harmonicDirectionalDerivative_surjective
        (show 2 ≤ n by omega) k x hx
      have hrank := LinearMap.finrank_range_add_finrank_ker
        (harmonicDirectionalDerivative n k x)
      rw [LinearMap.range_eq_top.mpr hsurj,
        finrank_top] at hrank
      rw [finrank_harmonicHomogeneousSubmodule hnpos k,
        finrank_harmonicHomogeneousSubmodule hnpos (k + 1)] at hrank
      have hker := (tangentHarmonicKerEquiv n k x).finrank_eq
      have hbranch := Gegenbauer.harmonicDimension_branch_step
        (n := n - 1) (show 2 ≤ n - 1 by omega) k
      have hshift : n - 1 + 1 = n := by omega
      rw [hshift] at hbranch
      change
        Module.finrank ℝ
          (tangentHarmonicSubmodule n (k + 1) x) =
            Gegenbauer.harmonicDimension (n - 1) (k + 1)
      omega

theorem finiteHilbertSchmidtKernel_finset_sum
    {α ι F E : Type*} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis ι ℝ F)
    (C : Finset α) (A : α → F →ₗ[ℝ] E) :
    finiteHilbertSchmidtKernel b
      (fun _ : Unit => ∑ x ∈ C, A x) () () =
      ∑ x ∈ C, ∑ y ∈ C, finiteHilbertSchmidtKernel b A x y := by
  classical
  unfold finiteHilbertSchmidtKernel
  simp_rw [LinearMap.sum_apply, sum_inner, inner_sum]
  calc
    (∑ i : ι, ∑ x ∈ C, ∑ y ∈ C,
      ⟪A x (b i), A y (b i)⟫_ℝ) =
        ∑ x ∈ C, ∑ i : ι, ∑ y ∈ C,
          ⟪A x (b i), A y (b i)⟫_ℝ := by
            rw [Finset.sum_comm]
    _ = ∑ x ∈ C, ∑ y ∈ C, ∑ i : ι,
          ⟪A x (b i), A y (b i)⟫_ℝ := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.sum_comm]

theorem trace_sq_le_finiteHilbertSchmidtKernel
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis ι ℝ E) (T : E →ₗ[ℝ] E) :
    (T.trace ℝ E) ^ 2 ≤
      (Fintype.card ι : ℝ) *
        finiteHilbertSchmidtKernel b (fun _ : Unit => T) () () := by
  classical
  rw [LinearMap.trace_eq_sum_inner T b]
  unfold finiteHilbertSchmidtKernel
  have hcs :=
    Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset ι)
      (fun _ : ι => (1 : ℝ))
      (fun i : ι => ⟪b i, T (b i)⟫_ℝ)
  calc
    (∑ i : ι, ⟪b i, T (b i)⟫_ℝ) ^ 2 ≤
        (Fintype.card ι : ℝ) *
          ∑ i : ι, ⟪b i, T (b i)⟫_ℝ ^ 2 := by
      simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_one] using hcs
    _ ≤ (Fintype.card ι : ℝ) *
          ∑ i : ι, ⟪T (b i), T (b i)⟫_ℝ := by
      apply mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ => ?_) (Nat.cast_nonneg _)
      have hi := real_inner_mul_inner_self_le (b i) (T (b i))
      simpa only [pow_two, inner_self_eq_norm_sq_to_K, Real.ringHom_apply, ge_iff_le,
        OrthonormalBasis.norm_eq_one, one_pow, one_mul] using hi

theorem finiteHilbertSchmidt_trace_cauchy
    {α ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (C : Finset α) (A : α → E →ₗ[ℝ] E) :
    (∑ x ∈ C, (A x).trace ℝ E) ^ 2 ≤
      (Fintype.card ι : ℝ) *
        ∑ x ∈ C, ∑ y ∈ C,
          finiteHilbertSchmidtKernel b A x y := by
  have h := trace_sq_le_finiteHilbertSchmidtKernel b (∑ x ∈ C, A x)
  rw [map_sum, finiteHilbertSchmidtKernel_finset_sum b C A] at h
  exact h

theorem isometric_projection_trace
    {F E : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ F] [FiniteDimensional ℝ E]
    (f : F →ₗᵢ[ℝ] E) :
    ((f.toLinearMap ∘ₗ f.adjoint).trace ℝ E) =
      (Module.finrank ℝ F : ℝ) := by
  calc
    ((f.toLinearMap ∘ₗ f.adjoint).trace ℝ E) =
        ((f.adjoint ∘ₗ f.toLinearMap).trace ℝ F) :=
      (LinearMap.trace_comp_comm' f.toLinearMap f.adjoint).symm
    _ = (LinearMap.id.trace ℝ F) := by
      rw [f.adjoint_comp_self']
    _ = (Module.finrank ℝ F : ℝ) :=
      LinearMap.trace_id ℝ F

theorem isometric_mixed_gram_trace_cauchy
    {α ι F E : Type*} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ F] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (C : Finset α) (f : α → F →ₗᵢ[ℝ] E) :
    ((C.card : ℝ) * (Module.finrank ℝ F : ℝ)) ^ 2 ≤
      (Fintype.card ι : ℝ) *
        ∑ x ∈ C, ∑ y ∈ C,
          mixedHilbertSchmidtKernel b
            (fun z => (f z).toLinearMap)
            (fun z => (f z).toLinearMap) x y := by
  have h := finiteHilbertSchmidt_trace_cauchy b C
    (fun x => (f x).toLinearMap ∘ₗ (f x).adjoint)
  simp_rw [isometric_projection_trace] at h
  simpa only [mixedHilbertSchmidtKernel, ge_iff_le, Finset.sum_const, nsmul_eq_mul] using h

end

section


open scoped BigOperators

namespace NumericalCertificate

/-- The binary entropy used in the spherical-code argument. -/
def binaryEntropy (u : ℝ) : ℝ :=
  ((1 + u) * Real.log (1 + u) - u * Real.log u) / Real.log 2

/-- The gamma used in the spherical-code argument. -/
def gamma (a b : ℝ) : ℝ :=
  (a * (1 + a) - b * (1 + b)) /
    ((1 + 2 * a) * Real.sqrt (a * (1 + a)))

end NumericalCertificate

end

end SpherePacking

namespace MetricCodes

section

open scoped BigOperators InnerProductSpace Matrix

namespace Johnson



end Johnson

end

namespace Spherical

section

/-- The boundary quadratic used in the spherical-code argument. -/
def boundaryQuadratic (s a : ℝ) : ℝ :=
  a * (1 + a) - (s / 2) * (1 + 2 * a) * Real.sqrt (a * (1 + a))

/-- The boundary degree used in the spherical-code argument. -/
def boundaryDegree (s a : ℝ) : ℝ :=
  (Real.sqrt (1 + 4 * boundaryQuadratic s a) - 1) / 2

theorem spectral_iff_quadratic {s a b : ℝ} (ha : 0 < a) :
    s < 2 * MetricCodes.Gamma a b ↔
      b * (1 + b) < boundaryQuadratic s a := by
  have hrad : 0 < a * (1 + a) := mul_pos ha (by linarith)
  have hden : 0 < (1 + 2 * a) * Real.sqrt (a * (1 + a)) :=
    mul_pos (by linarith) (Real.sqrt_pos.2 hrad)
  rw [MetricCodes.Gamma_eq_sub, ← mul_div_assoc, lt_div_iff₀ hden]
  unfold boundaryQuadratic
  constructor <;> intro h <;> nlinarith

theorem boundaryDegree_pos {s a : ℝ}
    (hQ : 0 < boundaryQuadratic s a) :
    0 < boundaryDegree s a := by
  have hrad : 0 ≤ 1 + 4 * boundaryQuadratic s a := by linarith
  have hsquare := Real.sq_sqrt hrad
  have hsqrt := Real.sqrt_nonneg (1 + 4 * boundaryQuadratic s a)
  unfold boundaryDegree
  nlinarith

theorem boundaryDegree_mul_one_add {s a : ℝ}
    (hQ : 0 ≤ boundaryQuadratic s a) :
    boundaryDegree s a * (1 + boundaryDegree s a) =
      boundaryQuadratic s a := by
  have hrad : 0 ≤ 1 + 4 * boundaryQuadratic s a := by linarith
  have hsquare := Real.sq_sqrt hrad
  unfold boundaryDegree
  nlinarith

theorem quadratic_iff_boundaryDegree {s a b : ℝ}
    (hb : 0 ≤ b) (hQ : 0 < boundaryQuadratic s a) :
    b * (1 + b) < boundaryQuadratic s a ↔ b < boundaryDegree s a := by
  have hroot := boundaryDegree_mul_one_add hQ.le
  have hpositive := boundaryDegree_pos hQ
  constructor
  · intro h
    by_contra hnot
    have hge : boundaryDegree s a ≤ b := le_of_not_gt hnot
    nlinarith [sq_nonneg (b - boundaryDegree s a)]
  · intro h
    nlinarith [sq_nonneg (b - boundaryDegree s a)]

end

section

open scoped BigOperators

namespace HigherHierarchy

@[simp] theorem lagrangeWeight_zero
    (a : Fin 1 → ℝ) (b : Fin 0 → ℝ) (ℓ : Fin 1) :
    lagrangeWeight a b ℓ = 1 := by
  simp only [lagrangeWeight, lagrangeNumerator, Finset.univ_eq_empty, Finset.prod_empty,
    lagrangeDenominator, ne_eq, one_ne_zero, not_false_eq_true, div_self]

theorem Gamma_zero (a : Fin 1 → ℝ) (b : Fin 0 → ℝ) :
    Gamma a b = spectralAtom (a 0) := by
  simp only [Gamma, Nat.reduceAdd, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    lagrangeWeight_zero, one_mul, Finset.sum_singleton]

theorem Phi_zero (a : Fin 1 → ℝ) (b : Fin 0 → ℝ) :
    Phi a b = MetricCodes.sphericalEntropy (a 0) := by
  simp only [Phi, Nat.reduceAdd, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, Finset.univ_eq_empty, Finset.sum_empty, sub_zero]

theorem oneRowInterlacing_iff {a b : ℝ} :
    Interlacing (![a, 0] : Fin 2 → ℝ) (![b] : Fin 1 → ℝ) ↔
      0 < b ∧ b < a := by
  simp only [Interlacing, Fin.reduceLast, Matrix.cons_val_one, Fin.isValue,
    Matrix.cons_val_fin_one, Std.le_refl, gt_iff_lt, Matrix.cons_val_succ,
    and_comm, Fin.forall_fin_one, Fin.castSucc_zero, Matrix.cons_val_zero, true_and]

theorem Gamma_oneRow {a b : ℝ} (ha : 0 < a) :
    Gamma (![a, 0] : Fin 2 → ℝ) (![b] : Fin 1 → ℝ) =
      MetricCodes.Gamma a b := by
  have hrad : 0 < a * (1 + a) := by positivity
  have hroot : 0 < Real.sqrt (a * (1 + a)) := Real.sqrt_pos.mpr hrad
  have hlinear : 0 < 1 + 2 * a := by positivity
  have hsquare := Real.sq_sqrt hrad.le
  rw [MetricCodes.Gamma_eq_sub]
  simp only [Gamma, Nat.reduceAdd, lagrangeWeight, lagrangeNumerator, Finset.univ_unique,
    Fin.default_eq_zero, Fin.isValue,
    Matrix.cons_val_fin_one, Finset.prod_const, Finset.card_singleton, pow_one, lagrangeDenominator,
    Finset.prod_singleton, spectralAtom, Fin.sum_univ_two, Matrix.cons_val_zero, Fin.zero_succAbove,
    Fin.succ_zero_eq_one, Matrix.cons_val_one, add_zero, mul_one, sub_zero, zero_sub, ne_eq,
    one_ne_zero, not_false_eq_true, Fin.succAbove_ne_zero_zero, neg_div_neg_eq, Real.sqrt_zero,
    mul_zero, div_one]
  field_simp [hrad.ne', hroot.ne', hlinear.ne']
  rw [hsquare]
  ring

theorem Phi_oneRow (a b : ℝ) :
    Phi (![a, 0] : Fin 2 → ℝ) (![b] : Fin 1 → ℝ) =
      MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b := by
  simp only [Phi, Nat.reduceAdd, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, sphericalEntropy_zero, add_zero,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_const,
    Finset.card_singleton, one_smul]

theorem spectralAtom_lt_half {u : ℝ} (hu : 0 ≤ u) :
    spectralAtom u < (1 / 2 : ℝ) := by
  have hrad : 0 ≤ u * (1 + u) := by positivity
  have hroot : 0 ≤ Real.sqrt (u * (1 + u)) := Real.sqrt_nonneg _
  have hlinear : 0 < 1 + 2 * u := by positivity
  have hsquare := Real.sq_sqrt hrad
  have hgap :
      (2 * Real.sqrt (u * (1 + u))) ^ 2 < (1 + 2 * u) ^ 2 := by
    nlinarith
  unfold spectralAtom
  apply (div_lt_iff₀ hlinear).mpr
  nlinarith

theorem Interlacing.Gamma_nonneg {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) : 0 ≤ Gamma a b := by
  unfold Gamma
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (h.lagrangeWeight_nonneg i)
      (spectralAtom_nonneg (h.ambient_nonneg i))

theorem Interlacing.Gamma_lt_half {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) : Gamma a b < (1 / 2 : ℝ) := by
  calc
    Gamma a b =
        ∑ i : Fin (r + 1), lagrangeWeight a b i * spectralAtom (a i) := rfl
    _ < ∑ i : Fin (r + 1), lagrangeWeight a b i * (1 / 2 : ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty
        (Finset.univ_nonempty : (Finset.univ : Finset (Fin (r + 1))).Nonempty)
      intro i _
      exact mul_lt_mul_of_pos_left (spectralAtom_lt_half (h.ambient_nonneg i))
        (h.lagrangeWeight_pos i)
    _ = (∑ i : Fin (r + 1), lagrangeWeight a b i) * (1 / 2 : ℝ) := by
      rw [Finset.sum_mul]
    _ = (1 / 2 : ℝ) := by rw [h.sum_lagrangeWeight, one_mul]

end HigherHierarchy

end

end Spherical

end MetricCodes

namespace SpherePacking

section


open Filter Real
open scoped Nat Topology

theorem tendsto_nat_sequence_sub_cast_div
    (N : ℕ → ℕ) (c : ℕ) (u : ℝ)
    (hN : Tendsto N atTop atTop)
    (hNu : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ))
      atTop (nhds u)) :
    Tendsto (fun n : ℕ => ((N n - c : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds u) := by
  have hsub := hNu.sub (tendsto_const_div_atTop_nhds_zero_nat (c : ℝ))
  have heq :
      (fun n : ℕ => (N n : ℝ) / (n : ℝ) - (c : ℝ) / (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => ((N n - c : ℕ) : ℝ) / (n : ℝ)) := by
    filter_upwards [hN.eventually (eventually_ge_atTop c)] with n hn
    rw [Nat.cast_sub hn, sub_div]
  simpa only [sub_zero] using hsub.congr' heq

private def harmonicEntropyBase (u : ℝ) (N : ℕ → ℕ) (n : ℕ) : ℕ :=
  (⌊u * (n : ℝ)⌋₊ + (N n - 2)).choose ⌊u * (n : ℝ)⌋₊

theorem harmonicEntropyBase_pos (u : ℝ) (N : ℕ → ℕ) (n : ℕ) :
    0 < harmonicEntropyBase u N n := by
  unfold harmonicEntropyBase
  apply Nat.choose_pos
  omega

theorem harmonicDimension_choose_bounds
    {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    (n + k - 2).choose k ≤ Gegenbauer.harmonicDimension n k ∧
      Gegenbauer.harmonicDimension n k ≤ 2 * (n + k - 2).choose k := by
  cases k with
  | zero => omega
  | succ i =>
      have hindex : n + (i + 1) - 2 = n + i - 1 := by
        omega
      have hpascal :
          (n + i - 1).choose (i + 1) =
            (n + i - 2).choose i +
              (n + i - 2).choose (i + 1) := by
        have h := Nat.choose_succ_succ (n + i - 2) i
        have harg : (n + i - 2).succ = n + i - 1 := by
          omega
        simpa only [harg, Nat.succ_eq_add_one] using h
      simp only [Gegenbauer.harmonicDimension_succ, hindex]
      constructor <;> omega

theorem tendsto_log_harmonicEntropyBase_div
    (u : ℝ) (hu : 0 < u)
    (N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop)
    (hNratio : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ))
      atTop (nhds 1)) :
    Tendsto
      (fun n : ℕ => Real.log (harmonicEntropyBase u N n : ℝ) / (n : ℝ))
      atTop (nhds ((1 + u) * Real.log (1 + u) - u * Real.log u)) := by
  have hfloor :
      Tendsto (fun n : ℕ => (⌊u * (n : ℝ)⌋₊ : ℝ) / (n : ℝ))
        atTop (nhds u) :=
    (tendsto_nat_floor_mul_div_atTop hu.le).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hambient : Tendsto (fun n : ℕ => N n - 2) atTop atTop :=
    (tendsto_sub_atTop_nat 2).comp hN
  have hambientratio :
      Tendsto (fun n : ℕ => ((N n - 2 : ℕ) : ℝ) / (n : ℝ))
        atTop (nhds 1) :=
    tendsto_nat_sequence_sub_cast_div N 2 1 hN hNratio
  have h := tendsto_log_add_choose_div
    (fun n : ℕ => ⌊u * (n : ℝ)⌋₊)
    (fun n : ℕ => N n - 2)
    u 1
    (tendsto_nat_floor_mul_atTop u hu)
    hambient
    hfloor hambientratio hu (by norm_num)
  simpa only [harmonicEntropyBase, add_comm, log_one, mul_zero, sub_zero] using h

theorem tendsto_log_two_mul_harmonicEntropyBase_div
    (u : ℝ) (hu : 0 < u)
    (N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop)
    (hNratio : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ))
      atTop (nhds 1)) :
    Tendsto
      (fun n : ℕ =>
        Real.log ((2 * harmonicEntropyBase u N n : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds ((1 + u) * Real.log (1 + u) - u * Real.log u)) := by
  have hbase := tendsto_log_harmonicEntropyBase_div u hu N hN hNratio
  have htwo := tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)
  have hsum := htwo.add hbase
  have heq :
      (fun n : ℕ =>
        Real.log 2 / (n : ℝ) +
          Real.log (harmonicEntropyBase u N n : ℝ) / (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ =>
        Real.log ((2 * harmonicEntropyBase u N n : ℕ) : ℝ) / (n : ℝ)) := by
    apply Eventually.of_forall
    intro n
    change
      Real.log 2 / (n : ℝ) +
          Real.log (harmonicEntropyBase u N n : ℝ) / (n : ℝ) =
        Real.log ((2 * harmonicEntropyBase u N n : ℕ) : ℝ) / (n : ℝ)
    push_cast
    rw [Real.log_mul (by norm_num)
      (by exact_mod_cast (harmonicEntropyBase_pos u N n).ne')]
    rw [add_div]
  simpa only [Nat.cast_mul, Nat.cast_ofNat, zero_add] using hsum.congr' heq

theorem tendsto_log_harmonicDimension_div
    (u : ℝ) (hu : 0 < u)
    (N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop)
    (hNratio : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ))
      atTop (nhds 1)) :
    Tendsto
      (fun n : ℕ =>
        Real.log
          (Gegenbauer.harmonicDimension (N n) ⌊u * (n : ℝ)⌋₊ : ℝ) /
          (n : ℝ))
      atTop (nhds ((1 + u) * Real.log (1 + u) - u * Real.log u)) := by
  have hlower := tendsto_log_harmonicEntropyBase_div u hu N hN hNratio
  have hupper := tendsto_log_two_mul_harmonicEntropyBase_div u hu N hN hNratio
  have hbounds :
      ∀ᶠ n : ℕ in atTop,
        harmonicEntropyBase u N n ≤
            Gegenbauer.harmonicDimension (N n) ⌊u * (n : ℝ)⌋₊ ∧
          Gegenbauer.harmonicDimension (N n) ⌊u * (n : ℝ)⌋₊ ≤
            2 * harmonicEntropyBase u N n := by
    filter_upwards
      [hN.eventually (eventually_ge_atTop 2),
       (tendsto_nat_floor_mul_atTop u hu).eventually
         (eventually_ge_atTop 1)] with n hn hk
    have hb := harmonicDimension_choose_bounds hn hk
    have hindex :
        N n + ⌊u * (n : ℝ)⌋₊ - 2 =
          ⌊u * (n : ℝ)⌋₊ + (N n - 2) := by
      omega
    simpa only [harmonicEntropyBase, hindex] using hb
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [hbounds] with n hn
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    apply Real.log_le_log
    · exact_mod_cast harmonicEntropyBase_pos u N n
    · exact_mod_cast hn.1
  · filter_upwards [hbounds] with n hn
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    apply Real.log_le_log
    · have hpos :
          0 < Gegenbauer.harmonicDimension (N n) ⌊u * (n : ℝ)⌋₊ :=
        lt_of_lt_of_le (harmonicEntropyBase_pos u N n) hn.1
      exact_mod_cast hpos
    · exact_mod_cast hn.2

theorem tendsto_log_harmonicDimension_div_log_two
    (u : ℝ) (hu : 0 < u)
    (N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop)
    (hNratio : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ))
      atTop (nhds 1)) :
    Tendsto
      (fun n : ℕ =>
        (Real.log
          (Gegenbauer.harmonicDimension (N n) ⌊u * (n : ℝ)⌋₊ : ℝ) /
          (n : ℝ)) / Real.log 2)
      atTop (nhds (NumericalCertificate.binaryEntropy u)) := by
  simpa only [NumericalCertificate.binaryEntropy] using
    (tendsto_log_harmonicDimension_div u hu N hN hNratio).div_const (Real.log 2)

end

section


open Filter Real
open scoped BigOperators Nat Topology

theorem tendsto_natCast_div_self :
    Tendsto (fun n : ℕ => (n : ℝ) / (n : ℝ))
      atTop (nhds 1) := by
  have heq :
      (fun _ : ℕ => (1 : ℝ)) =ᶠ[atTop]
        (fun n : ℕ => (n : ℝ) / (n : ℝ)) := by
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    exact (div_self hn').symm
  exact tendsto_const_nhds.congr' heq

theorem tendsto_nat_succ_cast_div :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds 1) := by
  have h := tendsto_natCast_div_self.add
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  simpa only [Nat.cast_add, Nat.cast_one, add_div, one_div, add_zero] using h

theorem tendsto_nat_pred_cast_div :
    Tendsto (fun n : ℕ => ((n - 1 : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds 1) := by
  exact tendsto_nat_sequence_sub_cast_div
    (fun n => n) 1 1 tendsto_id tendsto_natCast_div_self

/-- The harmonic dimension quotient used in the spherical-code argument. -/
def harmonicDimensionQuotient (a b : ℝ) (n : ℕ) : ℝ :=
  (Gegenbauer.harmonicDimension (n + 1) ⌊a * (n : ℝ)⌋₊ : ℝ) /
    (Gegenbauer.harmonicDimension (n - 1) ⌊b * (n : ℝ)⌋₊ : ℝ)

theorem harmonicDimensionQuotient_pos
    (a b : ℝ) {n : ℕ} (hn : 3 ≤ n) :
    0 < harmonicDimensionQuotient a b n := by
  unfold harmonicDimensionQuotient
  apply div_pos
  · exact_mod_cast
      Gegenbauer.harmonicDimension_pos (by omega : 2 ≤ n + 1)
        ⌊a * (n : ℝ)⌋₊
  · exact_mod_cast
      Gegenbauer.harmonicDimension_pos (by omega : 2 ≤ n - 1)
        ⌊b * (n : ℝ)⌋₊

theorem tendsto_log_harmonicDimensionQuotient
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun n : ℕ =>
        (Real.log (harmonicDimensionQuotient a b n) / (n : ℝ)) /
          Real.log 2)
      atTop
      (nhds (NumericalCertificate.binaryEntropy a -
        NumericalCertificate.binaryEntropy b)) := by
  have hnum := tendsto_log_harmonicDimension_div_log_two
    a ha (fun n : ℕ => n + 1)
    (tendsto_add_atTop_nat 1) tendsto_nat_succ_cast_div
  have hden := tendsto_log_harmonicDimension_div_log_two
    b hb (fun n : ℕ => n - 1)
    (tendsto_sub_atTop_nat 1) tendsto_nat_pred_cast_div
  have hdiff := hnum.sub hden
  have heq :
      (fun n : ℕ =>
        (Real.log
          (Gegenbauer.harmonicDimension (n + 1) ⌊a * (n : ℝ)⌋₊ : ℝ) /
          (n : ℝ)) / Real.log 2 -
        (Real.log
          (Gegenbauer.harmonicDimension (n - 1) ⌊b * (n : ℝ)⌋₊ : ℝ) /
          (n : ℝ)) / Real.log 2) =ᶠ[atTop]
      (fun n : ℕ =>
        (Real.log (harmonicDimensionQuotient a b n) / (n : ℝ)) /
          Real.log 2) := by
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    have hnumpos :
        0 <
          (Gegenbauer.harmonicDimension
            (n + 1) ⌊a * (n : ℝ)⌋₊ : ℝ) := by
      exact_mod_cast
        Gegenbauer.harmonicDimension_pos (by omega : 2 ≤ n + 1)
          ⌊a * (n : ℝ)⌋₊
    have hdenpos :
        0 <
          (Gegenbauer.harmonicDimension
            (n - 1) ⌊b * (n : ℝ)⌋₊ : ℝ) := by
      exact_mod_cast
        Gegenbauer.harmonicDimension_pos (by omega : 2 ≤ n - 1)
          ⌊b * (n : ℝ)⌋₊
    unfold harmonicDimensionQuotient
    rw [Real.log_div hnumpos.ne' hdenpos.ne']
    ring
  exact hdiff.congr' heq

theorem tendsto_log_const_mul_harmonicDimensionQuotient
    (a b C : ℝ) (ha : 0 < a) (hb : 0 < b) (hC : 0 < C) :
    Tendsto
      (fun n : ℕ =>
        (Real.log (C * harmonicDimensionQuotient a b n) /
          (n : ℝ)) / Real.log 2)
      atTop
      (nhds (NumericalCertificate.binaryEntropy a -
        NumericalCertificate.binaryEntropy b)) := by
  have hquot := tendsto_log_harmonicDimensionQuotient a b ha hb
  have hconstant :=
    (tendsto_const_div_atTop_nhds_zero_nat (Real.log C)).div_const
      (Real.log 2)
  have hsum := hconstant.add hquot
  have heq :
      (fun n : ℕ =>
        (Real.log C / (n : ℝ)) / Real.log 2 +
          (Real.log (harmonicDimensionQuotient a b n) /
            (n : ℝ)) / Real.log 2) =ᶠ[atTop]
      (fun n : ℕ =>
        (Real.log (C * harmonicDimensionQuotient a b n) /
          (n : ℝ)) / Real.log 2) := by
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    rw [Real.log_mul hC.ne'
      (harmonicDimensionQuotient_pos a b hn).ne']
    ring
  simpa only [zero_div, zero_add] using hsum.congr' heq

/-- The truncated harmonic dimension used in the spherical-code argument. -/
def truncatedHarmonicDimension (n k L : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc k L, Gegenbauer.harmonicDimension n i

theorem truncatedHarmonicDimension_le_successor
    {n : ℕ} (hn : 2 ≤ n) (k L : ℕ) :
    truncatedHarmonicDimension n k L ≤
      Gegenbauer.harmonicDimension (n + 1) L := by
  calc
    truncatedHarmonicDimension n k L =
        ∑ i ∈ Finset.Icc k L,
          Gegenbauer.harmonicDimension n i := rfl
    _ ≤ ∑ i ∈ Finset.range (L + 1),
          Gegenbauer.harmonicDimension n i := by
      apply Finset.sum_le_sum_of_subset
      intro i hi
      have hi' := (Finset.mem_Icc.mp hi).2
      apply Finset.mem_range.mpr
      omega
    _ = Gegenbauer.harmonicDimension (n + 1) L :=
      Gegenbauer.harmonicDimension_branch_sum hn L

/-- The truncated dimension quotient used in the spherical-code argument. -/
def truncatedDimensionQuotient (a b : ℝ) (n : ℕ) : ℝ :=
  (truncatedHarmonicDimension n
    ⌊b * (n : ℝ)⌋₊ ⌊a * (n : ℝ)⌋₊ : ℝ) /
    (Gegenbauer.fibreDimension n ⌊b * (n : ℝ)⌋₊ : ℝ)

theorem truncatedDimensionQuotient_le_harmonicDimensionQuotient
    (a b : ℝ) {n : ℕ} (hn : 3 ≤ n) :
    truncatedDimensionQuotient a b n ≤
      harmonicDimensionQuotient a b n := by
  unfold truncatedDimensionQuotient harmonicDimensionQuotient
    Gegenbauer.fibreDimension
  apply div_le_div_of_nonneg_right
  · exact_mod_cast truncatedHarmonicDimension_le_successor
      (by omega : 2 ≤ n)
      ⌊b * (n : ℝ)⌋₊ ⌊a * (n : ℝ)⌋₊
  · exact_mod_cast
      (Gegenbauer.harmonicDimension_pos
        (by omega : 2 ≤ n - 1) ⌊b * (n : ℝ)⌋₊).le

theorem harmonicDimension_le_truncated
    (n k L : ℕ) (hkl : k ≤ L) :
    Gegenbauer.harmonicDimension n k ≤
      truncatedHarmonicDimension n k L := by
  unfold truncatedHarmonicDimension
  apply Finset.single_le_sum
  · intro i hi
    exact Nat.zero_le _
  · exact Finset.mem_Icc.mpr ⟨le_rfl, hkl⟩

end

section


open scoped BigOperators InnerProductSpace

namespace Jacobi

/-- The index used in the spherical-code argument. -/
abbrev Index (k L : ℕ) := Fin (L - k + 1)

/-- The space used in the spherical-code argument. -/
abbrev Space (k L : ℕ) := EuclideanSpace ℝ (Index k L)

/-- The matrix used in the spherical-code argument. -/
def matrix (n k L : ℕ) : Matrix (Index k L) (Index k L) ℝ :=
  Gegenbauer.jacobiMatrix n k L

theorem matrix_hermitian (n k L : ℕ) : (matrix n k L).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have h := congrArg
    (fun A : Matrix (Index k L) (Index k L) ℝ => A i j)
    (Gegenbauer.jacobiMatrix_symmetric n k L)
  simpa only [matrix, star_trivial, Matrix.transpose_apply] using h

/-- The operator used in the spherical-code argument. -/
def operator (n k L : ℕ) : Space k L →ₗ[ℝ] Space k L :=
  Matrix.toEuclideanLin (matrix n k L)

theorem operator_isSymmetric (n k L : ℕ) :
    (operator n k L).IsSymmetric := by
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (matrix_hermitian n k L)

/-- The continuous operator used in the spherical-code argument. -/
def continuousOperator (n k L : ℕ) : Space k L →L[ℝ] Space k L :=
  LinearMap.toContinuousLinearMap (operator n k L)

/-- The rayleigh used in the spherical-code argument. -/
def rayleigh (n k L : ℕ) (x : Space k L) : ℝ :=
  (continuousOperator n k L).rayleighQuotient x

theorem rayleigh_bddAbove (n k L : ℕ) :
    BddAbove
      (Set.range
        (fun x : {x : Space k L // x ≠ 0} => rayleigh n k L x)) := by
  refine ⟨‖continuousOperator n k L‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (le_abs_self _).trans
    ((continuousOperator n k L).rayleighQuotient_le_norm x)

/-- The top eigenvalue used in the spherical-code argument. -/
def topEigenvalue (n k L : ℕ) : ℝ :=
  ⨆ x : {x : Space k L // x ≠ 0}, rayleigh n k L x

theorem rayleigh_le_top (n k L : ℕ) (x : Space k L) (hx : x ≠ 0) :
    rayleigh n k L x ≤ topEigenvalue n k L := by
  exact le_ciSup (rayleigh_bddAbove n k L) ⟨x, hx⟩

theorem topEigenvalue_hasEigenvalue (n k L : ℕ) :
    Module.End.HasEigenvalue (operator n k L) (topEigenvalue n k L) := by
  have h := (operator_isSymmetric n k L).hasEigenvalue_iSup_of_finiteDimensional
  simpa only [topEigenvalue, ne_eq, rayleigh, ContinuousLinearMap.rayleighQuotient,
    continuousOperator, ContinuousLinearMap.reApplyInnerSelf_apply,
    LinearMap.coe_toContinuousLinearMap', RCLike.re_to_real, Order.lt_one_iff,
    Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one, Real.ringHom_apply] using h

theorem exists_topEigenvector (n k L : ℕ) :
    ∃ x : Space k L, x ≠ 0 ∧
      operator n k L x = topEigenvalue n k L • x := by
  obtain ⟨x, hx⟩ :=
    (topEigenvalue_hasEigenvalue n k L).exists_hasEigenvector
  exact ⟨x, hx.2, hx.apply_eq_smul⟩

theorem rayleigh_eq_inner (n k L : ℕ) (x : Space k L) :
    rayleigh n k L x =
      @inner ℝ (Space k L) _ (operator n k L x) x / ‖x‖ ^ 2 := by
  rfl

end Jacobi

end

section


open Metric
open scoped BigOperators InnerProductSpace

namespace Perron

/-- The coordinate abs used in the spherical-code argument. -/
def coordinateAbs (k L : ℕ) (x : Jacobi.Space k L) : Jacobi.Space k L :=
  WithLp.toLp 2 (fun p : Jacobi.Index k L => |x p|)

theorem coordinateAbs_nonneg (k L : ℕ)
    (x : Jacobi.Space k L) (p : Jacobi.Index k L) :
    0 ≤ coordinateAbs k L x p := by
  exact abs_nonneg _

theorem coordinateAbs_norm (k L : ℕ) (x : Jacobi.Space k L) :
    ‖coordinateAbs k L x‖ = ‖x‖ := by
  have hsquare : ‖coordinateAbs k L x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq,
      EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [coordinateAbs, sq_abs]
  nlinarith [norm_nonneg (coordinateAbs k L x), norm_nonneg x]

theorem coordinateAbs_ne_zero (k L : ℕ)
    {x : Jacobi.Space k L} (hx : x ≠ 0) :
    coordinateAbs k L x ≠ 0 := by
  intro habs
  have hnorm := coordinateAbs_norm k L x
  rw [habs, norm_zero] at hnorm
  exact hx (norm_eq_zero.mp hnorm.symm)

theorem matrix_entry_nonneg {n : ℕ} (hn : 3 ≤ n)
    (k L : ℕ) (p q : Jacobi.Index k L) :
    0 ≤ Jacobi.matrix n k L p q := by
  unfold Jacobi.matrix Gegenbauer.jacobiMatrix
  split_ifs with hpq hqp
  · exact (Gegenbauer.jacobiCoefficient_pos hn (by omega)).le
  · exact (Gegenbauer.jacobiCoefficient_pos hn (by omega)).le
  · exact le_rfl

theorem inner_le_inner_coordinateAbs {n : ℕ} (hn : 3 ≤ n)
    (k L : ℕ) (x : Jacobi.Space k L) :
    @inner ℝ (Jacobi.Space k L) _ (Jacobi.operator n k L x) x ≤
      @inner ℝ (Jacobi.Space k L) _
        (Jacobi.operator n k L (coordinateAbs k L x))
        (coordinateAbs k L x) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [Real.inner_apply]
  change
    (∑ p : Jacobi.Index k L,
      (∑ q : Jacobi.Index k L,
        Jacobi.matrix n k L p q * x q) * x p) ≤
    (∑ p : Jacobi.Index k L,
      (∑ q : Jacobi.Index k L,
        Jacobi.matrix n k L p q * |x q|) * |x p|)
  simp_rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro q hq
  have hentry := matrix_entry_nonneg hn k L p q
  have hproduct : x q * x p ≤ |x q| * |x p| := by
    calc
      x q * x p ≤ |x q * x p| := le_abs_self _
      _ = |x q| * |x p| := abs_mul _ _
  calc
    Jacobi.matrix n k L p q * x q * x p =
        Jacobi.matrix n k L p q * (x q * x p) := by ring
    _ ≤ Jacobi.matrix n k L p q * (|x q| * |x p|) :=
      mul_le_mul_of_nonneg_left hproduct hentry
    _ = Jacobi.matrix n k L p q * |x q| * |x p| := by ring

theorem rayleigh_le_coordinateAbs {n : ℕ} (hn : 3 ≤ n)
    (k L : ℕ) (x : Jacobi.Space k L) :
    Jacobi.rayleigh n k L x ≤
      Jacobi.rayleigh n k L (coordinateAbs k L x) := by
  rw [Jacobi.rayleigh_eq_inner, Jacobi.rayleigh_eq_inner,
    coordinateAbs_norm]
  gcongr
  exact inner_le_inner_coordinateAbs hn k L x

theorem rayleigh_eq_of_eigenvector
    (n k L : ℕ) (x : Jacobi.Space k L) (hx : x ≠ 0)
    (eigenvalue : ℝ)
    (heig : Jacobi.operator n k L x = eigenvalue • x) :
    Jacobi.rayleigh n k L x = eigenvalue := by
  rw [Jacobi.rayleigh_eq_inner, heig,
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hnorm : ‖x‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  field_simp [hnorm]

theorem coordinateAbs_top_rayleigh
    {n : ℕ} (hn : 3 ≤ n) (k L : ℕ)
    (x : Jacobi.Space k L) (hx : x ≠ 0)
    (heig : Jacobi.operator n k L x =
      Jacobi.topEigenvalue n k L • x) :
    Jacobi.rayleigh n k L (coordinateAbs k L x) =
      Jacobi.topEigenvalue n k L := by
  have hbelow := rayleigh_le_coordinateAbs hn k L x
  have habs := coordinateAbs_ne_zero k L hx
  have habove := Jacobi.rayleigh_le_top n k L
    (coordinateAbs k L x) habs
  have hxray := rayleigh_eq_of_eigenvector n k L x hx
    (Jacobi.topEigenvalue n k L) heig
  rw [hxray] at hbelow
  exact le_antisymm habove hbelow

theorem exists_nonnegative_topEigenvector
    {n : ℕ} (hn : 3 ≤ n) (k L : ℕ) :
    ∃ x : Jacobi.Space k L,
      x ≠ 0 ∧
      Jacobi.operator n k L x = Jacobi.topEigenvalue n k L • x ∧
      ∀ p : Jacobi.Index k L, 0 ≤ x p := by
  obtain ⟨x, hx, heig⟩ := Jacobi.exists_topEigenvector n k L
  let y : Jacobi.Space k L := coordinateAbs k L x
  have hy : y ≠ 0 := coordinateAbs_ne_zero k L hx
  have hyray : Jacobi.rayleigh n k L y =
      Jacobi.topEigenvalue n k L :=
    coordinateAbs_top_rayleigh hn k L x hx heig
  have hself : IsSelfAdjoint (Jacobi.continuousOperator n k L) := by
    exact (Jacobi.operator_isSymmetric n k L).isSelfAdjoint
  have hmax :
      IsMaxOn (Jacobi.continuousOperator n k L).reApplyInnerSelf
        (sphere (0 : Jacobi.Space k L) ‖y‖) y := by
    intro z hz
    have hnorm : ‖z‖ = ‖y‖ := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
    have hznonzero : z ≠ 0 := by
      intro hzzero
      rw [hzzero, norm_zero] at hnorm
      exact hy (norm_eq_zero.mp hnorm.symm)
    have hray := Jacobi.rayleigh_le_top n k L z hznonzero
    rw [← hyray] at hray
    change
      (Jacobi.continuousOperator n k L).reApplyInnerSelf z /
        ‖z‖ ^ 2 ≤
        (Jacobi.continuousOperator n k L).reApplyInnerSelf y /
          ‖y‖ ^ 2 at hray
    rw [hnorm] at hray
    have hnormpos : 0 < ‖y‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr hy)
    exact (div_le_div_iff_of_pos_right hnormpos).mp hray
  have heigy := hself.hasEigenvector_of_isMaxOn hy hmax
  refine ⟨y, hy, ?_, fun p => coordinateAbs_nonneg k L x p⟩
  have happly := heigy.apply_eq_smul
  simpa only [Jacobi.topEigenvalue, ne_eq, Jacobi.rayleigh, Jacobi.continuousOperator,
    LinearMap.coe_toContinuousLinearMap, Real.ringHom_apply] using happly

theorem exists_nonnegative_unit_topEigenvector
    {n : ℕ} (hn : 3 ≤ n) (k L : ℕ) :
    ∃ x : Jacobi.Space k L,
      ‖x‖ = 1 ∧
      Jacobi.operator n k L x = Jacobi.topEigenvalue n k L • x ∧
      ∀ p : Jacobi.Index k L, 0 ≤ x p := by
  obtain ⟨x, hx, heig, hnonneg⟩ :=
    exists_nonnegative_topEigenvector hn k L
  have hnormpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  refine ⟨‖x‖⁻¹ • x, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hnormpos)]
    exact inv_mul_cancel₀ (ne_of_gt hnormpos)
  · rw [map_smul, heig]
    exact smul_comm _ _ _
  · intro p
    change 0 ≤ ‖x‖⁻¹ * x p
    exact mul_nonneg (inv_nonneg.mpr hnormpos.le) (hnonneg p)

theorem unit_coordinate_sq_sum
    {k L : ℕ} {x : Jacobi.Space k L} (hx : ‖x‖ = 1) :
    (∑ p : Jacobi.Index k L, x p ^ 2) = 1 := by
  rw [← EuclideanSpace.real_norm_sq_eq, hx]
  norm_num

end Perron

end

section


open Filter Topology
open scoped BigOperators Topology InnerProductSpace

namespace SpectralAsymptotics

open SpherePacking.NumericalCertificate

theorem tendsto_floored_ratio {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (⌊a * (n : ℝ)⌋₊ : ℝ) / (n : ℝ))
      atTop (nhds a) := by
  simpa only [Function.comp_def] using
    (tendsto_nat_floor_mul_div_atTop ha).comp (tendsto_natCast_atTop_atTop (R := ℝ))

/-- The normalized coefficient used in the spherical-code argument. -/
def normalizedCoefficient (x y z : ℝ) : ℝ :=
  ((x - y + z) * (x + y + 1 - 2 * z)) /
    Real.sqrt
      ((x + z) * (x + 1 - 2 * z) *
        (2 * x + 1 - 2 * z) * (2 * x + 1))

theorem jacobiCoefficient_eq_normalized
    (n k i : ℕ) (hn : 0 < n) :
    Gegenbauer.jacobiCoefficient n k i =
      normalizedCoefficient
        ((i : ℝ) / (n : ℝ))
        ((k : ℝ) / (n : ℝ))
        ((1 : ℝ) / (n : ℝ)) := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnreal
  unfold Gegenbauer.jacobiCoefficient normalizedCoefficient
  have hrad :
      (((i : ℝ) + 1) * ((i : ℝ) + (n : ℝ) - 2) *
        (2 * (i : ℝ) + (n : ℝ) - 2) *
        (2 * (i : ℝ) + (n : ℝ))) =
      (((n : ℝ) ^ 2) ^ 2) *
        (((i : ℝ) / n + (1 : ℝ) / n) *
          ((i : ℝ) / n + 1 - 2 * ((1 : ℝ) / n)) *
          (2 * ((i : ℝ) / n) + 1 - 2 * ((1 : ℝ) / n)) *
          (2 * ((i : ℝ) / n) + 1)) := by
    field_simp [hnne]
  rw [hrad, Real.sqrt_mul (sq_nonneg ((n : ℝ) ^ 2)),
    Real.sqrt_sq (sq_nonneg (n : ℝ)), div_mul_eq_div_div]
  congr 1
  field_simp [hnne]

theorem tridiagonal_quadratic_sum
    (d : ℕ) (c v : ℕ → ℝ) :
    (∑ p ∈ Finset.range (d + 1),
      ∑ q ∈ Finset.range (d + 1),
        (if p + 1 = q then c p
          else if q + 1 = p then c q else 0) * v q * v p) =
      2 * ∑ p ∈ Finset.range d, c p * v p * v (p + 1) := by
  have hpoint (p q : ℕ) :
      (if p + 1 = q then c p
        else if q + 1 = p then c q else 0) * v q * v p =
        (if p + 1 = q then c p * v q * v p else 0) +
        (if q + 1 = p then c q * v q * v p else 0) := by
    by_cases h₁ : p + 1 = q
    · have h₂ : ¬ q + 1 = p := by omega
      simp only [h₁, ↓reduceIte, h₂, add_zero]
    · by_cases h₂ : q + 1 = p
      · simp only [h₁, ↓reduceIte, h₂, zero_add]
      · simp only [h₁, ↓reduceIte, h₂, zero_mul, add_zero]
  have hupper :
      (∑ p ∈ Finset.range (d + 1),
        ∑ q ∈ Finset.range (d + 1),
          if p + 1 = q then c p * v q * v p else 0) =
        ∑ p ∈ Finset.range d, c p * v p * v (p + 1) := by
    simp only [Finset.sum_ite_eq, Finset.mem_range]
    rw [Finset.sum_range_succ]
    simp only [lt_self_iff_false, ite_false, add_zero]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' : p < d := Finset.mem_range.mp hp
    simp only [Order.lt_add_one_iff, Order.add_one_le_iff, hp', ↓reduceIte, mul_comm, mul_left_comm,
      mul_assoc]
  have hlower :
      (∑ p ∈ Finset.range (d + 1),
        ∑ q ∈ Finset.range (d + 1),
          if q + 1 = p then c q * v q * v p else 0) =
        ∑ p ∈ Finset.range d, c p * v p * v (p + 1) := by
    rw [Finset.sum_comm]
    calc
      (∑ q ∈ Finset.range (d + 1),
        ∑ p ∈ Finset.range (d + 1),
          if q + 1 = p then c q * v q * v p else 0) =
        ∑ q ∈ Finset.range (d + 1),
          ∑ p ∈ Finset.range (d + 1),
            if q + 1 = p then c q * v p * v q else 0 := by
              apply Finset.sum_congr rfl
              intro q hq
              apply Finset.sum_congr rfl
              intro p hp
              split_ifs <;> ring
      _ = _ := hupper
  calc
    (∑ p ∈ Finset.range (d + 1),
      ∑ q ∈ Finset.range (d + 1),
        (if p + 1 = q then c p
          else if q + 1 = p then c q else 0) * v q * v p) =
        ∑ p ∈ Finset.range (d + 1),
          ∑ q ∈ Finset.range (d + 1),
            ((if p + 1 = q then c p * v q * v p else 0) +
             (if q + 1 = p then c q * v q * v p else 0)) := by
              apply Finset.sum_congr rfl
              intro p hp
              apply Finset.sum_congr rfl
              intro q hq
              exact hpoint p q
    _ =
        (∑ p ∈ Finset.range (d + 1),
          ∑ q ∈ Finset.range (d + 1),
            if p + 1 = q then c p * v q * v p else 0) +
        (∑ p ∈ Finset.range (d + 1),
          ∑ q ∈ Finset.range (d + 1),
            if q + 1 = p then c q * v q * v p else 0) := by
              simp_rw [Finset.sum_add_distrib]
    _ = 2 * ∑ p ∈ Finset.range d, c p * v p * v (p + 1) := by
      rw [hupper, hlower]
      ring

/-- The terminal indicator used in the spherical-code argument. -/
def terminalIndicator (d m p : ℕ) : ℝ :=
  if d - m ≤ p then 1 else 0

theorem terminal_indicator_sum (d m : ℕ) (hm : m ≤ d) :
    (∑ p ∈ Finset.range (d + 1), terminalIndicator d m p) =
      (m : ℝ) + 1 := by
  have hsplit : d + 1 = (d - m) + (m + 1) := by omega
  rw [hsplit, Finset.sum_range_add]
  have hfirst :
      (∑ p ∈ Finset.range (d - m), terminalIndicator d m p) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hp' : p < d - m := Finset.mem_range.mp hp
    simp only [terminalIndicator, Nat.not_le.mpr hp', ↓reduceIte]
  rw [hfirst, zero_add]
  calc
    (∑ p ∈ Finset.range (m + 1),
      terminalIndicator d m (d - m + p)) =
        ∑ _p ∈ Finset.range (m + 1), (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro p hp
          simp only [terminalIndicator, le_add_iff_nonneg_right, zero_le, ↓reduceIte]
    _ = (m : ℝ) + 1 := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
                            Nat.cast_add, Nat.cast_one, mul_one]

theorem terminal_indicator_edge_sum
    (d m : ℕ) (hm : m ≤ d) (c : ℕ → ℝ) :
    (∑ p ∈ Finset.range d,
      c p * terminalIndicator d m p *
        terminalIndicator d m (p + 1)) =
      ∑ r ∈ Finset.range m, c (d - m + r) := by
  have hsplit : d = (d - m) + m := by omega
  rw [hsplit, Finset.sum_range_add]
  simp only [← hsplit]
  have hfirst :
      (∑ p ∈ Finset.range (d - m),
        c p * terminalIndicator d m p *
          terminalIndicator d m (p + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hp' : p < d - m := Finset.mem_range.mp hp
    simp only [terminalIndicator, Nat.not_le.mpr hp', ↓reduceIte, mul_zero, tsub_le_iff_right,
      mul_ite, mul_one, ite_self]
  rw [hfirst, zero_add]
  apply Finset.sum_congr rfl
  intro p hp
  have h₁ : d - m ≤ d - m + p := by omega
  have h₂ : d - m ≤ d - m + p + 1 := by omega
  simp only [terminalIndicator, ite_eq_left h₁, ite_eq_left h₂, mul_one]

/-- The terminal vector used in the spherical-code argument. -/
def terminalVector (k L m : ℕ) : Jacobi.Space k L :=
  WithLp.toLp 2
    (fun p : Fin (L - k + 1) => terminalIndicator (L - k) m p.val)

theorem terminalVector_last (k L m : ℕ) :
    terminalVector k L m (Fin.last (L - k)) = 1 := by
  change (if L - k - m ≤ L - k then (1 : ℝ) else 0) = 1
  simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le, ↓reduceIte]

theorem terminalVector_ne_zero (k L m : ℕ) :
    terminalVector k L m ≠ 0 := by
  intro h
  have hx := congrArg
    (fun x : Jacobi.Space k L => x (Fin.last (L - k))) h
  simp only [terminalVector_last, PiLp.zero_apply, one_ne_zero] at hx

theorem terminalVector_norm_sq
    (k L m : ℕ) (hm : m ≤ L - k) :
    ‖terminalVector k L m‖ ^ 2 = (m : ℝ) + 1 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change
    (∑ p : Fin (L - k + 1),
      terminalIndicator (L - k) m p.val ^ 2) = (m : ℝ) + 1
  have hsq (p : ℕ) :
      terminalIndicator (L - k) m p ^ 2 =
        terminalIndicator (L - k) m p := by
    simp only [terminalIndicator, tsub_le_iff_right, ite_pow, one_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
  simp_rw [hsq]
  rw [Fin.sum_univ_eq_sum_range]
  exact terminal_indicator_sum (L - k) m hm

theorem terminalVector_inner
    (n k L m : ℕ) (hkl : k ≤ L) (hm : m ≤ L - k) :
    @inner ℝ (Jacobi.Space k L) _
        (Jacobi.operator n k L (terminalVector k L m))
        (terminalVector k L m) =
      2 * ∑ r ∈ Finset.range m,
        Gegenbauer.jacobiCoefficient n k (L - m + r) := by
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply]
  change
    (∑ p : Fin (L - k + 1),
      (∑ q : Fin (L - k + 1),
        (if p.val + 1 = q.val then
          Gegenbauer.jacobiCoefficient n k (k + p.val)
        else if q.val + 1 = p.val then
          Gegenbauer.jacobiCoefficient n k (k + q.val)
        else 0) * terminalIndicator (L - k) m q.val) *
        terminalIndicator (L - k) m p.val) =
      2 * ∑ r ∈ Finset.range m,
        Gegenbauer.jacobiCoefficient n k (L - m + r)
  simp_rw [Finset.sum_mul]
  let f : ℕ → ℝ := fun p =>
    ∑ q : Fin (L - k + 1),
      (if p + 1 = q.val then
        Gegenbauer.jacobiCoefficient n k (k + p)
      else if q.val + 1 = p then
        Gegenbauer.jacobiCoefficient n k (k + q.val)
      else 0) * terminalIndicator (L - k) m q.val *
        terminalIndicator (L - k) m p
  change
    (∑ p : Fin (L - k + 1), f p.val) =
      2 * ∑ r ∈ Finset.range m,
        Gegenbauer.jacobiCoefficient n k (L - m + r)
  rw [Fin.sum_univ_eq_sum_range f]
  dsimp only [f]
  have hfin (p : ℕ) :
      (∑ q : Fin (L - k + 1),
        (if p + 1 = q.val then
          Gegenbauer.jacobiCoefficient n k (k + p)
        else if q.val + 1 = p then
          Gegenbauer.jacobiCoefficient n k (k + q.val)
        else 0) * terminalIndicator (L - k) m q.val *
          terminalIndicator (L - k) m p) =
        ∑ q ∈ Finset.range (L - k + 1),
          (if p + 1 = q then
            Gegenbauer.jacobiCoefficient n k (k + p)
          else if q + 1 = p then
            Gegenbauer.jacobiCoefficient n k (k + q)
          else 0) * terminalIndicator (L - k) m q *
            terminalIndicator (L - k) m p := by
    let g : ℕ → ℝ := fun q =>
      (if p + 1 = q then
        Gegenbauer.jacobiCoefficient n k (k + p)
      else if q + 1 = p then
        Gegenbauer.jacobiCoefficient n k (k + q)
      else 0) * terminalIndicator (L - k) m q *
        terminalIndicator (L - k) m p
    change (∑ q : Fin (L - k + 1), g q.val) =
      ∑ q ∈ Finset.range (L - k + 1), g q
    exact Fin.sum_univ_eq_sum_range g (L - k + 1)
  simp_rw [hfin]
  rw [tridiagonal_quadratic_sum]
  rw [terminal_indicator_edge_sum (L - k) m hm]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  omega

theorem terminalVector_rayleigh
    (n k L m : ℕ) (hkl : k ≤ L) (hm : m ≤ L - k) :
    Jacobi.rayleigh n k L (terminalVector k L m) =
      (2 * ∑ r ∈ Finset.range m,
        Gegenbauer.jacobiCoefficient n k (L - m + r)) /
          ((m : ℝ) + 1) := by
  rw [Jacobi.rayleigh_eq_inner,
    terminalVector_inner n k L m hkl hm,
    terminalVector_norm_sq k L m hm]

theorem terminal_edge_sum_le_top
    (n k L m : ℕ) (hkl : k ≤ L) (hm : m ≤ L - k) :
    (2 * ∑ r ∈ Finset.range m,
      Gegenbauer.jacobiCoefficient n k (L - m + r)) /
        ((m : ℝ) + 1) ≤
      Jacobi.topEigenvalue n k L := by
  rw [← terminalVector_rayleigh n k L m hkl hm]
  exact Jacobi.rayleigh_le_top n k L
    (terminalVector k L m) (terminalVector_ne_zero k L m)

end SpectralAsymptotics

end

section


open Filter
open scoped BigOperators InnerProductSpace

private abbrev CertificateFibre (n k : ℕ) :=
  Euclidean (Gegenbauer.fibreDimension n k)

private abbrev CertificateAmbient (n k L : ℕ) :=
  Euclidean (truncatedHarmonicDimension n k L)

private def certificateFibreBasis (n k : ℕ) :
    OrthonormalBasis (Fin (Gegenbauer.fibreDimension n k)) ℝ
      (CertificateFibre n k) :=
  EuclideanSpace.basisFun (Fin (Gegenbauer.fibreDimension n k)) ℝ

private def certificateAmbientBasis (n k L : ℕ) :
    OrthonormalBasis (Fin (truncatedHarmonicDimension n k L)) ℝ
      (CertificateAmbient n k L) :=
  EuclideanSpace.basisFun (Fin (truncatedHarmonicDimension n k L)) ℝ

private def isometricPackingKernel {n k L : ℕ}
    (f : Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L)
    (x y : Euclidean n) : ℝ :=
  mixedHilbertSchmidtKernel (certificateAmbientBasis n k L)
    (fun z => (f z).toLinearMap)
    (fun z => (f z).toLinearMap) x y

theorem isometric_mixed_kernel_eq_overlap
    {α ι ρ F E : Type*} [Fintype ι] [Fintype ρ]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ F] [FiniteDimensional ℝ E]
    (bE : OrthonormalBasis ι ℝ E)
    (bF : OrthonormalBasis ρ ℝ F)
    (f : α → F →ₗᵢ[ℝ] E) (x y : α) :
    mixedHilbertSchmidtKernel bE
      (fun z => (f z).toLinearMap)
      (fun z => (f z).toLinearMap) x y =
      finiteHilbertSchmidtKernel bF
        (fun _ : Unit => (f x).adjoint ∘ₗ (f y).toLinearMap) () () := by
  unfold mixedHilbertSchmidtKernel
  rw [finiteHilbertSchmidtKernel_eq_trace,
    finiteHilbertSchmidtKernel_eq_trace]
  simp only [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]
  simpa only [LinearMap.comp_assoc] using
    (LinearMap.trace_comp_comm' ((f x).toLinearMap ∘ₗ ((f x).adjoint ∘ₗ (f y).toLinearMap)) (f
      y).adjoint).symm

theorem isometric_mixed_kernel_nonneg
    {α ι ρ F E : Type*} [Fintype ι] [Fintype ρ]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ F] [FiniteDimensional ℝ E]
    (bE : OrthonormalBasis ι ℝ E)
    (bF : OrthonormalBasis ρ ℝ F)
    (f : α → F →ₗᵢ[ℝ] E) (x y : α) :
    0 ≤ mixedHilbertSchmidtKernel bE
      (fun z => (f z).toLinearMap)
      (fun z => (f z).toLinearMap) x y := by
  rw [isometric_mixed_kernel_eq_overlap bE bF f x y]
  unfold finiteHilbertSchmidtKernel
  exact Finset.sum_nonneg (fun i _ => real_inner_self_nonneg)

theorem isometric_mixed_kernel_diag
    {α ι ρ F E : Type*} [Fintype ι] [Fintype ρ]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ F] [FiniteDimensional ℝ E]
    (bE : OrthonormalBasis ι ℝ E)
    (bF : OrthonormalBasis ρ ℝ F)
    (f : α → F →ₗᵢ[ℝ] E) (x : α) :
    mixedHilbertSchmidtKernel bE
      (fun z => (f z).toLinearMap)
      (fun z => (f z).toLinearMap) x x =
      (Module.finrank ℝ F : ℝ) := by
  rw [isometric_mixed_kernel_eq_overlap bE bF f x x,
    finiteHilbertSchmidtKernel_eq_trace,
    (f x).adjoint_comp_self']
  simp only [LinearMap.IsSymmetric.id, LinearMap.IsSymmetric.adjoint_eq, LinearMap.comp_id,
    LinearMap.trace_id]

private abbrev CertificateDegreeAmbient (n k L : ℕ)
    (i : Jacobi.Index k L) :=
  Euclidean (Gegenbauer.harmonicDimension n (k + i.val))

private def finiteGramRecurrenceWeight
    (n k L : ℕ) (v : Jacobi.Space k L)
    (i : Jacobi.Index k L) : ℝ :=
  Real.sqrt (Gegenbauer.harmonicDimension n (k + i.val) : ℝ) * v i

private def finiteGramRecurrenceNormalization
    (n k L : ℕ) (v : Jacobi.Space k L) : ℝ :=
  ∑ i : Jacobi.Index k L, finiteGramRecurrenceWeight n k L v i

private def finiteGramFibreAmplitude
    (n k L : ℕ) (v : Jacobi.Space k L)
    (i : Jacobi.Index k L) : ℝ :=
  Real.sqrt
    (finiteGramRecurrenceWeight n k L v i /
      finiteGramRecurrenceNormalization n k L v)

private def finiteGramFibreAmplitudeVector
    (n k L : ℕ) (v : Jacobi.Space k L) : Jacobi.Space k L :=
  WithLp.toLp 2 (finiteGramFibreAmplitude n k L v)

theorem finiteGramRecurrenceWeight_nonneg
    (n k L : ℕ) (v : Jacobi.Space k L)
    (hv : ∀ i : Jacobi.Index k L, 0 ≤ v i)
    (i : Jacobi.Index k L) :
    0 ≤ finiteGramRecurrenceWeight n k L v i := by
  unfold finiteGramRecurrenceWeight
  exact mul_nonneg (Real.sqrt_nonneg _) (hv i)

theorem finiteGramRecurrenceNormalization_pos
    {n : ℕ} (hn : 3 ≤ n) (k L : ℕ)
    (v : Jacobi.Space k L) (hunit : ‖v‖ = 1)
    (hv : ∀ i : Jacobi.Index k L, 0 ≤ v i) :
    0 < finiteGramRecurrenceNormalization n k L v := by
  classical
  have hvzero : v ≠ 0 := by
    intro hzero
    simp only [hzero, norm_zero, zero_ne_one] at hunit
  obtain ⟨i, hi⟩ : ∃ i : Jacobi.Index k L, 0 < v i := by
    by_contra hnone
    simp only [not_exists, not_lt] at hnone
    apply hvzero
    apply PiLp.ext
    intro i
    change v i = 0
    exact le_antisymm (hnone i) (hv i)
  have hdimension :
      0 < (Gegenbauer.harmonicDimension n (k + i.val) : ℝ) := by
    exact_mod_cast Gegenbauer.harmonicDimension_pos
      (by omega : 2 ≤ n) (k + i.val)
  unfold finiteGramRecurrenceNormalization
  apply Finset.sum_pos'
  · intro j hj
    exact finiteGramRecurrenceWeight_nonneg n k L v hv j
  · refine ⟨i, Finset.mem_univ i, ?_⟩
    exact mul_pos (Real.sqrt_pos.2 hdimension) hi

theorem finiteGramFibreAmplitude_sq
    {n : ℕ} (hn : 3 ≤ n) (k L : ℕ)
    (v : Jacobi.Space k L) (hunit : ‖v‖ = 1)
    (hv : ∀ i : Jacobi.Index k L, 0 ≤ v i)
    (i : Jacobi.Index k L) :
    finiteGramFibreAmplitude n k L v i ^ 2 =
      finiteGramRecurrenceWeight n k L v i /
        finiteGramRecurrenceNormalization n k L v := by
  unfold finiteGramFibreAmplitude
  apply Real.sq_sqrt
  exact div_nonneg
    (finiteGramRecurrenceWeight_nonneg n k L v hv i)
    (finiteGramRecurrenceNormalization_pos hn k L v hunit hv).le

theorem finiteGramFibreAmplitude_sq_sum
    {n : ℕ} (hn : 3 ≤ n) (k L : ℕ)
    (v : Jacobi.Space k L) (hunit : ‖v‖ = 1)
    (hv : ∀ i : Jacobi.Index k L, 0 ≤ v i) :
    (∑ i : Jacobi.Index k L,
      finiteGramFibreAmplitude n k L v i ^ 2) = 1 := by
  simp_rw [finiteGramFibreAmplitude_sq hn k L v hunit hv]
  rw [← Finset.sum_div]
  change
    finiteGramRecurrenceNormalization n k L v /
      finiteGramRecurrenceNormalization n k L v = 1
  exact div_self
    (finiteGramRecurrenceNormalization_pos hn k L v hunit hv).ne'

theorem finiteGramFibreAmplitudeVector_unit
    {n : ℕ} (hn : 3 ≤ n) (k L : ℕ)
    (v : Jacobi.Space k L) (hunit : ‖v‖ = 1)
    (hv : ∀ i : Jacobi.Index k L, 0 ≤ v i) :
    ‖finiteGramFibreAmplitudeVector n k L v‖ = 1 := by
  have hsum :
      (∑ i : Jacobi.Index k L,
        finiteGramFibreAmplitudeVector n k L v i ^ 2) = 1 := by
    simpa only [finiteGramFibreAmplitudeVector] using finiteGramFibreAmplitude_sq_sum hn k L v
      hunit hv
  rw [← EuclideanSpace.real_norm_sq_eq] at hsum
  nlinarith [norm_nonneg (finiteGramFibreAmplitudeVector n k L v)]

/-- Data encoding the finite gram certificate construction. -/
structure FiniteGramCertificate (n k L : ℕ) where
  /-- The weights component. -/
  weights : Jacobi.Space k L
  weights_unit : ‖weights‖ = 1
  weights_eigenvector :
    Jacobi.operator n k L weights =
      Jacobi.topEigenvalue n k L • weights
  weights_nonneg : ∀ i : Jacobi.Index k L, 0 ≤ weights i
  /-- The fibre amplitudes component. -/
  fibreAmplitudes : Jacobi.Space k L
  fibreAmplitudes_eq : ∀ i : Jacobi.Index k L,
    fibreAmplitudes i = finiteGramFibreAmplitude n k L weights i
  fibreAmplitudes_unit : ‖fibreAmplitudes‖ = 1
  /-- The degree fibre component. -/
  degreeFibre : (i : Jacobi.Index k L) → Euclidean n →
    CertificateFibre n k →ₗᵢ[ℝ] CertificateDegreeAmbient n k L i
  /-- The degree injection component. -/
  degreeInjection : (i : Jacobi.Index k L) →
    CertificateDegreeAmbient n k L i →ₗᵢ[ℝ]
      CertificateAmbient n k L
  degree_orthogonal : ∀ (i j : Jacobi.Index k L), i ≠ j →
    ∀ (u : CertificateDegreeAmbient n k L i)
      (v : CertificateDegreeAmbient n k L j),
      ⟪degreeInjection i u, degreeInjection j v⟫_ℝ = 0
  /-- The fibre component. -/
  fibre : Euclidean n →
    CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L
  fibre_eq_weighted_degree : ∀ (x : Euclidean n)
      (v : CertificateFibre n k),
    fibre x v = ∑ i : Jacobi.Index k L,
      fibreAmplitudes i • degreeInjection i (degreeFibre i x v)
  /-- The coordinate dimension component. -/
  coordinateDimension : ℕ
  /-- The lift component. -/
  lift : Euclidean n → CertificateFibre n k →ₗ[ℝ]
    Euclidean coordinateDimension
  /-- The bulk component. -/
  bulk : Euclidean n → CertificateFibre n k →ₗ[ℝ]
    Euclidean coordinateDimension
  /-- The boundary component. -/
  boundary : Euclidean n → CertificateFibre n k →ₗ[ℝ]
    Euclidean coordinateDimension
  /-- The remainder component. -/
  remainder : Euclidean n → CertificateFibre n k →ₗ[ℝ]
    Euclidean coordinateDimension
  /-- The spectral coefficient component. -/
  spectralCoefficient : ℝ
  spectralCoefficient_sq :
    spectralCoefficient ^ 2 = Jacobi.topEigenvalue n k L
  decomposition : ∀ x ∈ unitSphere n,
    lift x = spectralCoefficient • bulk x +
      (1 : ℝ) • boundary x + remainder x
  lift_kernel : ∀ x ∈ unitSphere n, ∀ y ∈ unitSphere n,
    finiteHilbertSchmidtKernel (certificateFibreBasis n k)
      lift x y =
      ⟪x, y⟫_ℝ * isometricPackingKernel fibre x y
  bulk_kernel : ∀ x ∈ unitSphere n, ∀ y ∈ unitSphere n,
    finiteHilbertSchmidtKernel (certificateFibreBasis n k)
      bulk x y = isometricPackingKernel fibre x y
  bulk_boundary_orthogonal :
    ∀ x ∈ unitSphere n, ∀ y ∈ unitSphere n,
      ∀ i : Fin (Gegenbauer.fibreDimension n k),
        ⟪bulk x (certificateFibreBasis n k i),
          boundary y (certificateFibreBasis n k i)⟫_ℝ = 0
  bulk_remainder_orthogonal :
    ∀ x ∈ unitSphere n, ∀ y ∈ unitSphere n,
      ∀ i : Fin (Gegenbauer.fibreDimension n k),
        ⟪bulk x (certificateFibreBasis n k i),
          remainder y (certificateFibreBasis n k i)⟫_ℝ = 0
  boundary_remainder_orthogonal :
    ∀ x ∈ unitSphere n, ∀ y ∈ unitSphere n,
      ∀ i : Fin (Gegenbauer.fibreDimension n k),
        ⟪boundary x (certificateFibreBasis n k i),
          remainder y (certificateFibreBasis n k i)⟫_ℝ = 0

private def auxiliaryFiniteGramKernel {n k L : ℕ}
    (certificate : FiniteGramCertificate n k L) (s : ℝ)
    (x y : Euclidean n) : ℝ :=
  (⟪x, y⟫_ℝ - s) *
    isometricPackingKernel certificate.fibre x y

theorem finiteGramCertificate_shift_identity
    {n k L : ℕ} (certificate : FiniteGramCertificate n k L)
    {x y : Euclidean n}
    (hx : x ∈ unitSphere n) (hy : y ∈ unitSphere n) :
    (⟪x, y⟫_ℝ - Jacobi.topEigenvalue n k L) *
        isometricPackingKernel certificate.fibre x y =
      finiteHilbertSchmidtKernel (certificateFibreBasis n k)
        certificate.boundary x y +
      finiteHilbertSchmidtKernel (certificateFibreBasis n k)
        certificate.remainder x y := by
  let S := {z : Euclidean n // z ∈ unitSphere n}
  have hthree := finiteHilbertSchmidtKernel_three_channel
    (certificateFibreBasis n k)
    (fun z : S => certificate.bulk z.val)
    (fun z : S => certificate.boundary z.val)
    (fun z : S => certificate.remainder z.val)
    certificate.spectralCoefficient (1 : ℝ)
    (fun u v i => certificate.bulk_boundary_orthogonal
      u.val u.property v.val v.property i)
    (fun u v i => certificate.bulk_remainder_orthogonal
      u.val u.property v.val v.property i)
    (fun u v i => certificate.boundary_remainder_orthogonal
      u.val u.property v.val v.property i)
    (⟨x, hx⟩ : S) (⟨y, hy⟩ : S)
  have hdecomp :
      finiteHilbertSchmidtKernel (certificateFibreBasis n k)
        certificate.lift x y =
        certificate.spectralCoefficient ^ 2 *
          finiteHilbertSchmidtKernel (certificateFibreBasis n k)
            certificate.bulk x y +
        finiteHilbertSchmidtKernel (certificateFibreBasis n k)
          certificate.boundary x y +
        finiteHilbertSchmidtKernel (certificateFibreBasis n k)
          certificate.remainder x y := by
    unfold finiteHilbertSchmidtKernel
    rw [certificate.decomposition x hx,
      certificate.decomposition y hy]
    simpa only [one_smul, LinearMap.add_apply, LinearMap.smul_apply, finiteHilbertSchmidtKernel,
      one_pow, one_mul] using hthree
  rw [certificate.lift_kernel x hx y hy,
    certificate.bulk_kernel x hx y hy,
    certificate.spectralCoefficient_sq] at hdecomp
  linarith

theorem isometricPackingKernel_nonneg
    {n k L : ℕ}
    (f : Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L)
    (x y : Euclidean n) :
    0 ≤ isometricPackingKernel f x y := by
  exact isometric_mixed_kernel_nonneg
    (certificateAmbientBasis n k L)
    (certificateFibreBasis n k) f x y

theorem isometricPackingKernel_diag
    {n k L : ℕ}
    (f : Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L)
    (x : Euclidean n) :
    isometricPackingKernel f x x =
      (Gegenbauer.fibreDimension n k : ℝ) := by
  simpa only [isometricPackingKernel, finrank_euclideanSpace, Fintype.card_fin] using
    isometric_mixed_kernel_diag (certificateAmbientBasis n k L) (certificateFibreBasis n k) f x

theorem isometricPackingKernel_trace_cauchy
    {n k L : ℕ}
    (f : Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L)
    (C : Finset (Euclidean n)) :
    ((C.card : ℝ) * (Gegenbauer.fibreDimension n k : ℝ)) ^ 2 ≤
      (truncatedHarmonicDimension n k L : ℝ) *
        ∑ x ∈ C, ∑ y ∈ C, isometricPackingKernel f x y := by
  simpa only [isometricPackingKernel, finrank_euclideanSpace, Fintype.card_fin] using
    isometric_mixed_gram_trace_cauchy (certificateAmbientBasis n k L) C f

theorem finiteGramCertificate_shift_sum_nonnegative
    {n k L : ℕ} {s : ℝ}
    (certificate : FiniteGramCertificate n k L)
    (C : SphericalCode n s) :
    0 ≤ ∑ x ∈ C.points, ∑ y ∈ C.points,
      (⟪x, y⟫_ℝ - Jacobi.topEigenvalue n k L) *
        isometricPackingKernel certificate.fibre x y := by
  have hboundary :
      0 ≤ ∑ x ∈ C.points, ∑ y ∈ C.points,
        finiteHilbertSchmidtKernel (certificateFibreBasis n k)
          certificate.boundary x y := by
    simpa only [mul_one, one_mul] using
      finiteHilbertSchmidtKernel_positive (certificateFibreBasis n k) certificate.boundary
        C.points (fun _ => (1 : ℝ))
  have hremainder :
      0 ≤ ∑ x ∈ C.points, ∑ y ∈ C.points,
        finiteHilbertSchmidtKernel (certificateFibreBasis n k)
          certificate.remainder x y := by
    simpa only [mul_one, one_mul] using
      finiteHilbertSchmidtKernel_positive (certificateFibreBasis n k) certificate.remainder
        C.points (fun _ => (1 : ℝ))
  calc
    0 ≤
        (∑ x ∈ C.points, ∑ y ∈ C.points,
          finiteHilbertSchmidtKernel (certificateFibreBasis n k)
            certificate.boundary x y) +
        (∑ x ∈ C.points, ∑ y ∈ C.points,
          finiteHilbertSchmidtKernel (certificateFibreBasis n k)
            certificate.remainder x y) :=
      add_nonneg hboundary hremainder
    _ = ∑ x ∈ C.points, ∑ y ∈ C.points,
        (⟪x, y⟫_ℝ - Jacobi.topEigenvalue n k L) *
          isometricPackingKernel certificate.fibre x y := by
      simp_rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      symm
      exact finiteGramCertificate_shift_identity certificate
        (C.unit_norm x hx) (C.unit_norm y hy)

theorem finiteGramCertificate_auxiliary_sum_lower
    {n k L : ℕ} {s : ℝ}
    (certificate : FiniteGramCertificate n k L)
    (C : SphericalCode n s) :
    (Jacobi.topEigenvalue n k L - s) *
        (∑ x ∈ C.points, ∑ y ∈ C.points,
          isometricPackingKernel certificate.fibre x y) ≤
      ∑ x ∈ C.points, ∑ y ∈ C.points,
        auxiliaryFiniteGramKernel certificate s x y := by
  have hshift := finiteGramCertificate_shift_sum_nonnegative
    certificate C
  calc
    (Jacobi.topEigenvalue n k L - s) *
        (∑ x ∈ C.points, ∑ y ∈ C.points,
          isometricPackingKernel certificate.fibre x y) ≤
      (Jacobi.topEigenvalue n k L - s) *
        (∑ x ∈ C.points, ∑ y ∈ C.points,
          isometricPackingKernel certificate.fibre x y) +
      (∑ x ∈ C.points, ∑ y ∈ C.points,
        (⟪x, y⟫_ℝ - Jacobi.topEigenvalue n k L) *
          isometricPackingKernel certificate.fibre x y) :=
        le_add_of_nonneg_right hshift
    _ = ∑ x ∈ C.points, ∑ y ∈ C.points,
        auxiliaryFiniteGramKernel certificate s x y := by
      simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      unfold auxiliaryFiniteGramKernel
      ring

theorem finiteGramCertificate_sphericalCode_bound
    {n k L : ℕ} (hn : 3 ≤ n) (hkl : k ≤ L)
    (certificate : FiniteGramCertificate n k L)
    {s : ℝ} (hs : s ≤ 1)
    (hgap : s < Jacobi.topEigenvalue n k L)
    (C : SphericalCode n s) :
    (C.points.card : ℝ) ≤
      ((1 - s) / (Jacobi.topEigenvalue n k L - s)) *
        ((truncatedHarmonicDimension n k L : ℝ) /
          (Gegenbauer.fibreDimension n k : ℝ)) := by
  have hd : 0 < (Gegenbauer.fibreDimension n k : ℝ) := by
    exact_mod_cast Gegenbauer.fibreDimension_pos hn k
  have hDnat : 0 < truncatedHarmonicDimension n k L :=
    lt_of_lt_of_le
      (Gegenbauer.harmonicDimension_pos (by omega : 2 ≤ n) k)
      (harmonicDimension_le_truncated n k L hkl)
  have hD : 0 < (truncatedHarmonicDimension n k L : ℝ) := by
    exact_mod_cast hDnat
  have hgap' : 0 < Jacobi.topEigenvalue n k L - s :=
    sub_pos.mpr hgap
  have htrace :=
    isometricPackingKernel_trace_cauchy certificate.fibre C.points
  have hnormalized :
      (C.points.card : ℝ) ^ 2 *
          (Gegenbauer.fibreDimension n k : ℝ) ^ 2 /
          (truncatedHarmonicDimension n k L : ℝ) ≤
        ∑ x ∈ C.points, ∑ y ∈ C.points,
          isometricPackingKernel certificate.fibre x y := by
    apply (div_le_iff₀ hD).2
    nlinarith [htrace]
  have hpositive :
      (C.points.card : ℝ) ^ 2 *
        ((Jacobi.topEigenvalue n k L - s) *
          (Gegenbauer.fibreDimension n k : ℝ) ^ 2 /
          (truncatedHarmonicDimension n k L : ℝ)) ≤
        ∑ x ∈ C.points, ∑ y ∈ C.points,
          auxiliaryFiniteGramKernel certificate s x y := by
    calc
      (C.points.card : ℝ) ^ 2 *
          ((Jacobi.topEigenvalue n k L - s) *
            (Gegenbauer.fibreDimension n k : ℝ) ^ 2 /
            (truncatedHarmonicDimension n k L : ℝ)) =
        (Jacobi.topEigenvalue n k L - s) *
          ((C.points.card : ℝ) ^ 2 *
            (Gegenbauer.fibreDimension n k : ℝ) ^ 2 /
            (truncatedHarmonicDimension n k L : ℝ)) := by
          ring
      _ ≤ (Jacobi.topEigenvalue n k L - s) *
          (∑ x ∈ C.points, ∑ y ∈ C.points,
            isometricPackingKernel certificate.fibre x y) :=
          mul_le_mul_of_nonneg_left hnormalized hgap'.le
      _ ≤ ∑ x ∈ C.points, ∑ y ∈ C.points,
          auxiliaryFiniteGramKernel certificate s x y :=
        finiteGramCertificate_auxiliary_sum_lower certificate C
  have hc :
      0 < (Jacobi.topEigenvalue n k L - s) *
        (Gegenbauer.fibreDimension n k : ℝ) ^ 2 /
        (truncatedHarmonicDimension n k L : ℝ) :=
    div_pos (mul_pos hgap' (sq_pos_of_pos hd)) hD
  have hB :
      0 ≤ (1 - s) * (Gegenbauer.fibreDimension n k : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hs) hd.le
  have hdiag : ∀ x ∈ C.points,
      auxiliaryFiniteGramKernel certificate s x x ≤
        (1 - s) * (Gegenbauer.fibreDimension n k : ℝ) := by
    intro x hx
    simp only [auxiliaryFiniteGramKernel, inner_self_eq_norm_sq_to_K, C.unit_norm x hx,
      Real.ringHom_apply, one_pow, isometricPackingKernel_diag, Std.le_refl]
  have hoff : ∀ x ∈ C.points, ∀ y ∈ C.points, x ≠ y →
      auxiliaryFiniteGramKernel certificate s x y ≤ 0 := by
    intro x hx y hy hxy
    unfold auxiliaryFiniteGramKernel
    exact mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (C.inner_le x hx y hy hxy))
      (isometricPackingKernel_nonneg certificate.fibre x y)
  have hbound := finite_linear_programming_bound C.points
    (auxiliaryFiniteGramKernel certificate s)
    hc hB hdiag hoff hpositive
  calc
    (C.points.card : ℝ) ≤
        ((1 - s) * (Gegenbauer.fibreDimension n k : ℝ)) /
          ((Jacobi.topEigenvalue n k L - s) *
            (Gegenbauer.fibreDimension n k : ℝ) ^ 2 /
            (truncatedHarmonicDimension n k L : ℝ)) := hbound
    _ = ((1 - s) / (Jacobi.topEigenvalue n k L - s)) *
        ((truncatedHarmonicDimension n k L : ℝ) /
          (Gegenbauer.fibreDimension n k : ℝ)) := by
      field_simp [hd.ne', hD.ne', hgap'.ne']

end

section


open scoped BigOperators InnerProductSpace

namespace HarmonicCertificateAssembly

private abbrev DegreeBlockIndex (n k L : ℕ) :=
  Σ i : Jacobi.Index k L,
    Fin (Gegenbauer.harmonicDimension n (k + i.val))

private abbrev DegreeBlockPi (n k L : ℕ) :=
  PiLp 2 (fun i : Jacobi.Index k L =>
    CertificateDegreeAmbient n k L i)

theorem degreeBlock_dimension_sum
    (n k L : ℕ) (hkl : k ≤ L) :
    (∑ i : Jacobi.Index k L,
      Gegenbauer.harmonicDimension n (k + i.val)) =
      truncatedHarmonicDimension n k L := by
  classical
  unfold truncatedHarmonicDimension
  refine Finset.sum_bij (fun i _ => k + i.val) ?_ ?_ ?_ ?_
  · intro i hi
    apply Finset.mem_Icc.mpr
    constructor
    · change k ≤ k + i.val
      omega
    · have hival := i.isLt
      change k + i.val ≤ L
      omega
  · intro i hi j hj hij
    change k + i.val = k + j.val at hij
    apply Fin.ext
    omega
  · intro j hj
    obtain ⟨hkj, hjL⟩ := Finset.mem_Icc.mp hj
    refine ⟨⟨j - k, ?_⟩, Finset.mem_univ _, ?_⟩
    · omega
    · change k + (j - k) = j
      omega
  · intro i hi
    rfl

theorem degreeBlockIndex_card
    (n k L : ℕ) (hkl : k ≤ L) :
    Fintype.card (DegreeBlockIndex n k L) =
      truncatedHarmonicDimension n k L := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact degreeBlock_dimension_sum n k L hkl

private def degreeBlockIndexEquiv
    (n k L : ℕ) (hkl : k ≤ L) :
    DegreeBlockIndex n k L ≃
      Fin (truncatedHarmonicDimension n k L) :=
  Fintype.equivOfCardEq (by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using degreeBlockIndex_card n k L hkl)

private def degreeBlockReindex
    (n k L : ℕ) (hkl : k ≤ L) :
    EuclideanSpace ℝ (DegreeBlockIndex n k L) ≃ₗᵢ[ℝ]
      CertificateAmbient n k L :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (degreeBlockIndexEquiv n k L hkl)

private def degreeBlockSingle
    (n k L : ℕ) (i : Jacobi.Index k L) :
    CertificateDegreeAmbient n k L i →ₗᵢ[ℝ]
      DegreeBlockPi n k L := by
  classical
  refine
    { toLinearMap :=
        { toFun := fun v => PiLp.single 2 i v
          map_add' := fun v w => PiLp.single_add 2 i
          map_smul' := ?_ }
      norm_map' := ?_ }
  · intro c v
    apply PiLp.ext
    intro j
    by_cases hji : j = i
    · subst j
      simp only [PiLp.single_eq_same, Real.ringHom_apply, PiLp.smul_apply]
    · simp only [ne_eq, hji, not_false_eq_true, PiLp.single_eq_of_ne, Real.ringHom_apply,
        PiLp.smul_apply, smul_zero]
  · intro v
    exact PiLp.norm_single 2
      (fun j : Jacobi.Index k L =>
        CertificateDegreeAmbient n k L j) i v

private def degreeBlockFlatten (n k L : ℕ) :
    DegreeBlockPi n k L ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (DegreeBlockIndex n k L) :=
  (LinearIsometryEquiv.piLpCurry ℝ 2
    (fun (i : Jacobi.Index k L)
      (_ : Fin (Gegenbauer.harmonicDimension n (k + i.val))) =>
        ℝ)).symm

private def degreeBlockTransport
    (n k L : ℕ) (hkl : k ≤ L) :
    DegreeBlockPi n k L →ₗᵢ[ℝ]
      CertificateAmbient n k L :=
  (degreeBlockReindex n k L hkl).toLinearIsometry.comp
    (degreeBlockFlatten n k L).toLinearIsometry

private def degreeBlockInclusion
    (n k L : ℕ) (hkl : k ≤ L) (i : Jacobi.Index k L) :
    CertificateDegreeAmbient n k L i →ₗᵢ[ℝ]
      CertificateAmbient n k L :=
  (degreeBlockTransport n k L hkl).comp
    (degreeBlockSingle n k L i)

theorem degreeBlockSingle_orthogonal
    (n k L : ℕ) (i j : Jacobi.Index k L) (hij : i ≠ j)
    (u : CertificateDegreeAmbient n k L i)
    (v : CertificateDegreeAmbient n k L j) :
    ⟪degreeBlockSingle n k L i u,
      degreeBlockSingle n k L j v⟫_ℝ = 0 := by
  classical
  change ⟪PiLp.single 2 i u, PiLp.single 2 j v⟫_ℝ = 0
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro r hr
  by_cases hri : r = i
  · subst r
    simp only [PiLp.single_eq_same, ne_eq, hij, not_false_eq_true, PiLp.single_eq_of_ne,
      inner_zero_right]
  · simp only [ne_eq, hri, not_false_eq_true, PiLp.single_eq_of_ne, PiLp.ofLp_single,
      inner_zero_left]

theorem degreeBlockInclusion_orthogonal
    (n k L : ℕ) (hkl : k ≤ L)
    (i j : Jacobi.Index k L) (hij : i ≠ j)
    (u : CertificateDegreeAmbient n k L i)
    (v : CertificateDegreeAmbient n k L j) :
    ⟪degreeBlockInclusion n k L hkl i u,
      degreeBlockInclusion n k L hkl j v⟫_ℝ = 0 := by
  change
    ⟪degreeBlockTransport n k L hkl
        (degreeBlockSingle n k L i u),
      degreeBlockTransport n k L hkl
        (degreeBlockSingle n k L j v)⟫_ℝ = 0
  rw [(degreeBlockTransport n k L hkl).inner_map_map]
  exact degreeBlockSingle_orthogonal n k L i j hij u v

private def weightedDegreeLinearMap
    (n k L : ℕ) (hkl : k ≤ L)
    (weights : Jacobi.Space k L)
    (degreeFibre : (i : Jacobi.Index k L) → Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ]
        CertificateDegreeAmbient n k L i)
    (x : Euclidean n) :
    CertificateFibre n k →ₗ[ℝ] CertificateAmbient n k L :=
  ∑ i : Jacobi.Index k L, weights i •
    ((degreeBlockInclusion n k L hkl i).toLinearMap ∘ₗ
      (degreeFibre i x).toLinearMap)

@[simp] theorem weightedDegreeLinearMap_apply
    (n k L : ℕ) (hkl : k ≤ L)
    (weights : Jacobi.Space k L)
    (degreeFibre : (i : Jacobi.Index k L) → Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ]
        CertificateDegreeAmbient n k L i)
    (x : Euclidean n) (v : CertificateFibre n k) :
    weightedDegreeLinearMap n k L hkl weights degreeFibre x v =
      ∑ i : Jacobi.Index k L, weights i •
        degreeBlockInclusion n k L hkl i (degreeFibre i x v) := by
  simp only [weightedDegreeLinearMap, LinearMap.coe_sum, LinearMap.coe_smul, LinearMap.coe_comp,
    LinearIsometry.coe_toLinearMap, Finset.sum_apply, Pi.smul_apply, Function.comp_apply]

theorem weightedDegreeLinearMap_inner
    (n k L : ℕ) (hkl : k ≤ L)
    (weights : Jacobi.Space k L)
    (degreeFibre : (i : Jacobi.Index k L) → Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ]
        CertificateDegreeAmbient n k L i)
    (x : Euclidean n) (v w : CertificateFibre n k) :
    ⟪weightedDegreeLinearMap n k L hkl weights degreeFibre x v,
      weightedDegreeLinearMap n k L hkl weights degreeFibre x w⟫_ℝ =
      (∑ i : Jacobi.Index k L, weights i ^ 2) * ⟪v, w⟫_ℝ := by
  classical
  rw [weightedDegreeLinearMap_apply,
    weightedDegreeLinearMap_apply, sum_inner]
  simp_rw [inner_sum]
  calc
    (∑ i : Jacobi.Index k L,
      ∑ j : Jacobi.Index k L,
        ⟪weights i • degreeBlockInclusion n k L hkl i
            (degreeFibre i x v),
          weights j • degreeBlockInclusion n k L hkl j
            (degreeFibre j x w)⟫_ℝ) =
        ∑ i : Jacobi.Index k L, weights i ^ 2 * ⟪v, w⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_eq_single i]
      · rw [real_inner_smul_left, real_inner_smul_right,
          (degreeBlockInclusion n k L hkl i).inner_map_map,
          (degreeFibre i x).inner_map_map]
        ring
      · intro j hj hji
        rw [real_inner_smul_left, real_inner_smul_right,
          degreeBlockInclusion_orthogonal n k L hkl i j hji.symm]
        ring
      · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]
    _ = (∑ i : Jacobi.Index k L, weights i ^ 2) * ⟪v, w⟫_ℝ := by
      rw [Finset.sum_mul]

theorem weightedDegreeLinearMap_inner_of_unit
    (n k L : ℕ) (hkl : k ≤ L)
    (weights : Jacobi.Space k L) (hweights : ‖weights‖ = 1)
    (degreeFibre : (i : Jacobi.Index k L) → Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ]
        CertificateDegreeAmbient n k L i)
    (x : Euclidean n) (v w : CertificateFibre n k) :
    ⟪weightedDegreeLinearMap n k L hkl weights degreeFibre x v,
      weightedDegreeLinearMap n k L hkl weights degreeFibre x w⟫_ℝ =
      ⟪v, w⟫_ℝ := by
  rw [weightedDegreeLinearMap_inner,
    Perron.unit_coordinate_sq_sum hweights, one_mul]

private def weightedDegreeIsometry
    (n k L : ℕ) (hkl : k ≤ L)
    (weights : Jacobi.Space k L) (hweights : ‖weights‖ = 1)
    (degreeFibre : (i : Jacobi.Index k L) → Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ]
        CertificateDegreeAmbient n k L i)
    (x : Euclidean n) :
    CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L where
  toLinearMap := weightedDegreeLinearMap n k L hkl
    weights degreeFibre x
  norm_map' := by
    intro v
    simpa only [norm_eq_sqrt_real_inner] using
      congrArg Real.sqrt
        (weightedDegreeLinearMap_inner_of_unit n k L hkl
          weights hweights degreeFibre x v v)

@[simp] theorem weightedDegreeIsometry_apply
    (n k L : ℕ) (hkl : k ≤ L)
    (weights : Jacobi.Space k L) (hweights : ‖weights‖ = 1)
    (degreeFibre : (i : Jacobi.Index k L) → Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ]
        CertificateDegreeAmbient n k L i)
    (x : Euclidean n) (v : CertificateFibre n k) :
    weightedDegreeIsometry n k L hkl weights hweights degreeFibre x v =
      ∑ i : Jacobi.Index k L, weights i •
        degreeBlockInclusion n k L hkl i (degreeFibre i x v) := by
  exact weightedDegreeLinearMap_apply n k L hkl weights degreeFibre x v

private def harmonicPerronWeights
    (n k L : ℕ) (hn : 3 ≤ n) : Jacobi.Space k L :=
  Classical.choose (Perron.exists_nonnegative_unit_topEigenvector
    hn k L)

theorem harmonicPerronWeights_unit
    (n k L : ℕ) (hn : 3 ≤ n) :
    ‖harmonicPerronWeights n k L hn‖ = 1 :=
  (Classical.choose_spec
    (Perron.exists_nonnegative_unit_topEigenvector hn k L)).1

theorem harmonicPerronWeights_eigenvector
    (n k L : ℕ) (hn : 3 ≤ n) :
    Jacobi.operator n k L (harmonicPerronWeights n k L hn) =
      Jacobi.topEigenvalue n k L •
        harmonicPerronWeights n k L hn :=
  (Classical.choose_spec
    (Perron.exists_nonnegative_unit_topEigenvector hn k L)).2.1

theorem harmonicPerronWeights_nonneg
    (n k L : ℕ) (hn : 3 ≤ n) (i : Jacobi.Index k L) :
    0 ≤ harmonicPerronWeights n k L hn i :=
  (Classical.choose_spec
    (Perron.exists_nonnegative_unit_topEigenvector hn k L)).2.2 i

private def harmonicRecurrenceWeight
    (n k L : ℕ) (hn : 3 ≤ n)
    (i : Jacobi.Index k L) : ℝ :=
  finiteGramRecurrenceWeight n k L
    (harmonicPerronWeights n k L hn) i

private def harmonicRecurrenceNormalization
    (n k L : ℕ) (hn : 3 ≤ n) : ℝ :=
  finiteGramRecurrenceNormalization n k L
    (harmonicPerronWeights n k L hn)

theorem harmonicRecurrenceNormalization_pos
    (n k L : ℕ) (hn : 3 ≤ n) :
    0 < harmonicRecurrenceNormalization n k L hn := by
  exact finiteGramRecurrenceNormalization_pos hn k L
    (harmonicPerronWeights n k L hn)
    (harmonicPerronWeights_unit n k L hn)
    (harmonicPerronWeights_nonneg n k L hn)

private def harmonicFibreAmplitudes
    (n k L : ℕ) (hn : 3 ≤ n) : Jacobi.Space k L :=
  finiteGramFibreAmplitudeVector n k L
    (harmonicPerronWeights n k L hn)

theorem harmonicFibreAmplitudes_unit
    (n k L : ℕ) (hn : 3 ≤ n) :
    ‖harmonicFibreAmplitudes n k L hn‖ = 1 := by
  exact finiteGramFibreAmplitudeVector_unit hn k L
    (harmonicPerronWeights n k L hn)
    (harmonicPerronWeights_unit n k L hn)
    (harmonicPerronWeights_nonneg n k L hn)

@[simp] theorem harmonicFibreAmplitudes_apply
    (n k L : ℕ) (hn : 3 ≤ n) (i : Jacobi.Index k L) :
    harmonicFibreAmplitudes n k L hn i =
      finiteGramFibreAmplitude n k L
        (harmonicPerronWeights n k L hn) i := by
  rfl

theorem harmonicFibreAmplitudes_sq
    (n k L : ℕ) (hn : 3 ≤ n) (i : Jacobi.Index k L) :
    harmonicFibreAmplitudes n k L hn i ^ 2 =
      harmonicRecurrenceWeight n k L hn i /
        harmonicRecurrenceNormalization n k L hn := by
  exact finiteGramFibreAmplitude_sq hn k L
    (harmonicPerronWeights n k L hn)
    (harmonicPerronWeights_unit n k L hn)
    (harmonicPerronWeights_nonneg n k L hn) i

private def harmonicWeightedFibre
    (n k L : ℕ) (hn : 3 ≤ n) (hkl : k ≤ L)
    (degreeFibre : (i : Jacobi.Index k L) → Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ]
        CertificateDegreeAmbient n k L i) :
    Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L :=
  fun x => weightedDegreeIsometry n k L hkl
    (harmonicFibreAmplitudes n k L hn)
    (harmonicFibreAmplitudes_unit n k L hn)
    degreeFibre x

@[simp] theorem harmonicWeightedFibre_apply
    (n k L : ℕ) (hn : 3 ≤ n) (hkl : k ≤ L)
    (degreeFibre : (i : Jacobi.Index k L) → Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ]
        CertificateDegreeAmbient n k L i)
    (x : Euclidean n) (v : CertificateFibre n k) :
    harmonicWeightedFibre n k L hn hkl degreeFibre x v =
      ∑ i : Jacobi.Index k L,
        harmonicFibreAmplitudes n k L hn i •
          degreeBlockInclusion n k L hkl i
            (degreeFibre i x v) := by
  exact weightedDegreeIsometry_apply n k L hkl
    (harmonicFibreAmplitudes n k L hn)
    (harmonicFibreAmplitudes_unit n k L hn)
    degreeFibre x v

private def harmonicPolynomialEuclideanEquiv
    (n m : ℕ) (hn : 0 < n) :
    harmonicHomogeneousSubmodule n m ≃ₗᵢ[ℝ]
      Euclidean (Gegenbauer.harmonicDimension n m) :=
  ((stdOrthonormalBasis ℝ (harmonicHomogeneousSubmodule n m)).reindex
    (finCongr (finrank_harmonicHomogeneousSubmodule hn m))).repr

private def harmonicDegreeEuclideanEquiv
    (n k L : ℕ) (hn : 0 < n) (i : Jacobi.Index k L) :
    harmonicHomogeneousSubmodule n (k + i.val) ≃ₗᵢ[ℝ]
      CertificateDegreeAmbient n k L i :=
  harmonicPolynomialEuclideanEquiv n (k + i.val) hn

private def tangentPolynomialEuclideanEquiv
    (n k : ℕ) (x : Euclidean n)
    (hdimension :
      Module.finrank ℝ (tangentHarmonicSubmodule n k x) =
        Gegenbauer.fibreDimension n k) :
    tangentHarmonicSubmodule n k x ≃ₗᵢ[ℝ]
      CertificateFibre n k := by
  letI : FiniteDimensional ℝ
      (tangentHarmonicSubmodule n k x) :=
    Fischer.tangent_finiteDimensional n k x
  exact
    ((stdOrthonormalBasis ℝ
      (tangentHarmonicSubmodule n k x)).reindex
        (finCongr hdimension)).repr

/-- Data encoding the harmonic coordinate construction. -/
structure HarmonicCoordinateData
    (n k L : ℕ)
    (fibre : Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L) where
  /-- The coordinate dimension component. -/
  coordinateDimension : ℕ
  /-- The lift component. -/
  lift : Euclidean n → CertificateFibre n k →ₗ[ℝ]
    Euclidean coordinateDimension
  /-- The bulk component. -/
  bulk : Euclidean n → CertificateFibre n k →ₗ[ℝ]
    Euclidean coordinateDimension
  /-- The boundary component. -/
  boundary : Euclidean n → CertificateFibre n k →ₗ[ℝ]
    Euclidean coordinateDimension
  /-- The remainder component. -/
  remainder : Euclidean n → CertificateFibre n k →ₗ[ℝ]
    Euclidean coordinateDimension
  /-- The spectral coefficient component. -/
  spectralCoefficient : ℝ
  spectralCoefficient_sq :
    spectralCoefficient ^ 2 = Jacobi.topEigenvalue n k L
  decomposition : ∀ x ∈ unitSphere n,
    lift x = spectralCoefficient • bulk x +
      (1 : ℝ) • boundary x + remainder x
  lift_kernel : ∀ x ∈ unitSphere n, ∀ y ∈ unitSphere n,
    finiteHilbertSchmidtKernel (certificateFibreBasis n k)
      lift x y = ⟪x, y⟫_ℝ * isometricPackingKernel fibre x y
  bulk_kernel : ∀ x ∈ unitSphere n, ∀ y ∈ unitSphere n,
    finiteHilbertSchmidtKernel (certificateFibreBasis n k)
      bulk x y = isometricPackingKernel fibre x y
  bulk_boundary_orthogonal :
    ∀ x ∈ unitSphere n, ∀ y ∈ unitSphere n,
      ∀ i : Fin (Gegenbauer.fibreDimension n k),
        ⟪bulk x (certificateFibreBasis n k i),
          boundary y (certificateFibreBasis n k i)⟫_ℝ = 0
  bulk_remainder_orthogonal :
    ∀ x ∈ unitSphere n, ∀ y ∈ unitSphere n,
      ∀ i : Fin (Gegenbauer.fibreDimension n k),
        ⟪bulk x (certificateFibreBasis n k i),
          remainder y (certificateFibreBasis n k i)⟫_ℝ = 0
  boundary_remainder_orthogonal :
    ∀ x ∈ unitSphere n, ∀ y ∈ unitSphere n,
      ∀ i : Fin (Gegenbauer.fibreDimension n k),
        ⟪boundary x (certificateFibreBasis n k i),
          remainder y (certificateFibreBasis n k i)⟫_ℝ = 0

private def assembleFiniteGramCertificate
    (n k L : ℕ) (hn : 3 ≤ n) (hkl : k ≤ L)
    (degreeFibre : (i : Jacobi.Index k L) → Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ]
        CertificateDegreeAmbient n k L i)
    (coordinates : HarmonicCoordinateData n k L
      (harmonicWeightedFibre n k L hn hkl degreeFibre)) :
    FiniteGramCertificate n k L where
  weights := harmonicPerronWeights n k L hn
  weights_unit := harmonicPerronWeights_unit n k L hn
  weights_eigenvector := harmonicPerronWeights_eigenvector n k L hn
  weights_nonneg := harmonicPerronWeights_nonneg n k L hn
  fibreAmplitudes := harmonicFibreAmplitudes n k L hn
  fibreAmplitudes_eq := harmonicFibreAmplitudes_apply n k L hn
  fibreAmplitudes_unit := harmonicFibreAmplitudes_unit n k L hn
  degreeFibre := degreeFibre
  degreeInjection := degreeBlockInclusion n k L hkl
  degree_orthogonal := degreeBlockInclusion_orthogonal n k L hkl
  fibre := harmonicWeightedFibre n k L hn hkl degreeFibre
  fibre_eq_weighted_degree :=
    harmonicWeightedFibre_apply n k L hn hkl degreeFibre
  coordinateDimension := coordinates.coordinateDimension
  lift := coordinates.lift
  bulk := coordinates.bulk
  boundary := coordinates.boundary
  remainder := coordinates.remainder
  spectralCoefficient := coordinates.spectralCoefficient
  spectralCoefficient_sq := coordinates.spectralCoefficient_sq
  decomposition := coordinates.decomposition
  lift_kernel := coordinates.lift_kernel
  bulk_kernel := coordinates.bulk_kernel
  bulk_boundary_orthogonal := coordinates.bulk_boundary_orthogonal
  bulk_remainder_orthogonal := coordinates.bulk_remainder_orthogonal
  boundary_remainder_orthogonal :=
    coordinates.boundary_remainder_orthogonal

end HarmonicCertificateAssembly

theorem solidHarmonicAxisLift_succ_apply
    (n k r : ℕ) (x : Euclidean n)
    (p : MvPolynomial (Fin n) ℝ) :
    solidHarmonicAxisLift n k x (r + 1) p =
      (MvPolynomial.C
        (2 * (r : ℝ) + harmonicAxisParameter n k - 2) *
          axisPolynomial n x) *
            solidHarmonicAxisLift n k x r p -
      (MvPolynomial.C
        ((r : ℝ) * ((r : ℝ) +
          harmonicAxisParameter n k - 3)) *
          radialPolynomial n) *
            solidHarmonicAxisLift n k x (r - 1) p := by
  cases r with
  | zero =>
      simp only [zero_add, solidHarmonicAxisLift_one_apply, MvPolynomial.C_sub, CharP.cast_eq_zero,
        mul_zero, solidHarmonicAxisLift_zero_apply, zero_mul, MvPolynomial.C_0, zero_tsub, sub_zero]
  | succ r =>
      simpa only [Nat.cast_add, Nat.cast_one,
        Nat.add_sub_cancel] using
        solidHarmonicAxisLift_succ_succ_apply n k r x p

theorem solidHarmonicAxisLift_harmonic_and_directional
    {n k : ℕ} (x : Euclidean n) (hx : ‖x‖ = 1)
    {p : MvPolynomial (Fin n) ℝ}
    (hp : p ∈ tangentHarmonicSubmodule n k x)
    (r : ℕ) :
    polynomialLaplacian n
        (solidHarmonicAxisLift n k x r p) = 0 ∧
      directionalDerivative n x
        (solidHarmonicAxisLift n k x r p) =
          MvPolynomial.C
            ((r : ℝ) * ((r : ℝ) +
              harmonicAxisParameter n k - 3)) *
            solidHarmonicAxisLift n k x (r - 1) p := by
  have hp' := (mem_tangentHarmonicSubmodule x p).mp hp
  induction r using Nat.twoStepInduction with
  | zero =>
      simpa only [solidHarmonicAxisLift_zero_apply, polynomialLaplacian_apply,
        directionalDerivative_apply, CharP.cast_eq_zero, zero_add, zero_mul, MvPolynomial.C_0,
        zero_tsub] using hp'.2
  | one =>
      constructor
      · rw [solidHarmonicAxisLift_one_apply, mul_assoc,
          polynomialLaplacian_C_mul,
          solidHarmonicAxis_polynomialLaplacian_axis_mul,
          hp'.2.1, hp'.2.2]
        simp only [MvPolynomial.C_sub, mul_zero, add_zero]
      · rw [solidHarmonicAxisLift_one_apply, mul_assoc,
          directionalDerivative_C_mul, directionalDerivative_mul,
          directionalDerivative_axisPolynomial_self x hx,
          hp'.2.2]
        simp only [one_mul, mul_zero, add_zero, Nat.cast_one,
          Nat.reduceSub, solidHarmonicAxisLift_zero_apply]
        have hcoefficient :
            harmonicAxisParameter n k - 2 =
              1 + harmonicAxisParameter n k - 3 := by
          ring
        rw [hcoefficient]
  | more r ihr ihrs =>
      rcases ihr with ⟨hlap_r, hder_r⟩
      rcases ihrs with ⟨hlap_rs, hder_rs⟩
      constructor
      · rw [solidHarmonicAxisLift_succ_succ_apply, map_sub,
          mul_assoc, polynomialLaplacian_C_mul,
          solidHarmonicAxis_polynomialLaplacian_axis_mul,
          hlap_rs, hder_rs, mul_assoc,
          polynomialLaplacian_C_mul,
          polynomialLaplacian_radial_mul
            (solidHarmonicAxisLift n k x r p)
            (solidHarmonicAxisLift_isHomogeneous x hp'.1 r),
          hlap_r]
        push_cast
        simp only [map_add, map_sub, map_mul, map_ofNat, map_one,
          mul_zero, add_zero]
        unfold harmonicAxisParameter
        simp only [map_add, map_mul, map_ofNat]
        ring
      · rw [solidHarmonicAxisLift_succ_succ_apply, map_sub,
          mul_assoc, directionalDerivative_C_mul,
          directionalDerivative_mul,
          directionalDerivative_axisPolynomial_self x hx,
          hder_rs, mul_assoc, directionalDerivative_C_mul,
          directionalDerivative_radial_mul, hder_r]
        have hrpred : r + 2 - 1 = r + 1 := by omega
        simp only [Nat.add_sub_cancel, hrpred]
        rw [solidHarmonicAxisLift_succ_apply n k r x p]
        push_cast
        simp only [map_add, map_sub, map_mul, map_ofNat, map_one]
        ring

theorem solidHarmonicAxisLift_mem_harmonic
    {n k : ℕ} (x : Euclidean n) (hx : ‖x‖ = 1)
    {p : MvPolynomial (Fin n) ℝ}
    (hp : p ∈ tangentHarmonicSubmodule n k x)
    (r : ℕ) :
    solidHarmonicAxisLift n k x r p ∈
      harmonicHomogeneousSubmodule n (k + r) := by
  apply (mem_harmonicHomogeneousSubmodule _).mpr
  constructor
  · exact solidHarmonicAxisLift_isHomogeneous x
      ((mem_tangentHarmonicSubmodule x p).mp hp).1 r
  · simpa only [← polynomialLaplacian_apply] using
      (solidHarmonicAxisLift_harmonic_and_directional
        x hx hp r).1

/-- The solid harmonic axis fischer scale used in the spherical-code argument. -/
def solidHarmonicAxisFischerScale (n k r : ℕ) : ℝ :=
  ∏ j ∈ Finset.range r,
    (2 * (j : ℝ) + harmonicAxisParameter n k - 2) *
      ((j : ℝ) + 1) *
      ((j : ℝ) + harmonicAxisParameter n k - 2)

@[simp] theorem solidHarmonicAxisFischerScale_zero (n k : ℕ) :
    solidHarmonicAxisFischerScale n k 0 = 1 := by
  simp only [solidHarmonicAxisFischerScale, Finset.range_zero, Finset.prod_empty]

theorem solidHarmonicAxisFischerScale_succ
    (n k r : ℕ) :
    solidHarmonicAxisFischerScale n k (r + 1) =
      solidHarmonicAxisFischerScale n k r *
        (2 * (r : ℝ) + harmonicAxisParameter n k - 2) *
        ((r : ℝ) + 1) *
        ((r : ℝ) + harmonicAxisParameter n k - 2) := by
  simp only [solidHarmonicAxisFischerScale, Finset.prod_range_succ]
  ring

theorem solidHarmonicAxisFischerScale_pos
    {n : ℕ} (hn : 3 ≤ n) (k r : ℕ) :
    0 < solidHarmonicAxisFischerScale n k r := by
  unfold solidHarmonicAxisFischerScale
  apply Finset.prod_pos
  intro j hj
  have hnreal : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hjreal : (0 : ℝ) ≤ (j : ℝ) := by positivity
  have hkreal : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hfirst :
      0 < 2 * (j : ℝ) + harmonicAxisParameter n k - 2 := by
    unfold harmonicAxisParameter
    linarith
  have hmiddle : 0 < (j : ℝ) + 1 := by positivity
  have hlast :
      0 < (j : ℝ) + harmonicAxisParameter n k - 2 := by
    unfold harmonicAxisParameter
    linarith
  exact mul_pos (mul_pos hfirst hmiddle) hlast

theorem fischer_polynomialInner_constant_mul_left
    (n : ℕ) (c : ℝ) (p q : MvPolynomial (Fin n) ℝ) :
    Fischer.polynomialInner n (MvPolynomial.C c * p) q =
      c * Fischer.polynomialInner n p q := by
  rw [MvPolynomial.C_mul', Fischer.polynomialInner_smul_left]

theorem fischer_polynomialInner_constant_mul_right
    (n : ℕ) (c : ℝ) (p q : MvPolynomial (Fin n) ℝ) :
    Fischer.polynomialInner n p (MvPolynomial.C c * q) =
      c * Fischer.polynomialInner n p q := by
  rw [MvPolynomial.C_mul', Fischer.polynomialInner_smul_right]

theorem solidHarmonicAxisLift_fischer_inner_succ
    {n k : ℕ} (x : Euclidean n) (hx : ‖x‖ = 1)
    (p q : tangentHarmonicSubmodule n k x) (r : ℕ) :
    Fischer.polynomialInner n
        (solidHarmonicAxisLift n k x (r + 1)
          (p : MvPolynomial (Fin n) ℝ))
        (solidHarmonicAxisLift n k x (r + 1)
          (q : MvPolynomial (Fin n) ℝ)) =
      (2 * (r : ℝ) + harmonicAxisParameter n k - 2) *
        ((r : ℝ) + 1) *
        ((r : ℝ) + harmonicAxisParameter n k - 2) *
        Fischer.polynomialInner n
          (solidHarmonicAxisLift n k x r
            (p : MvPolynomial (Fin n) ℝ))
          (solidHarmonicAxisLift n k x r
            (q : MvPolynomial (Fin n) ℝ)) := by
  have hqmem := solidHarmonicAxisLift_mem_harmonic
    x hx q.property (r + 1)
  let qnext : harmonicHomogeneousSubmodule n (k + (r + 1)) :=
    ⟨solidHarmonicAxisLift n k x (r + 1)
      (q : MvPolynomial (Fin n) ℝ), hqmem⟩
  have hrad :
      Fischer.polynomialInner n
        (radialPolynomial n *
          solidHarmonicAxisLift n k x (r - 1)
            (p : MvPolynomial (Fin n) ℝ))
        (solidHarmonicAxisLift n k x (r + 1)
          (q : MvPolynomial (Fin n) ℝ)) = 0 :=
    fischer_polynomialInner_radial_harmonic
      (solidHarmonicAxisLift n k x (r - 1)
        (p : MvPolynomial (Fin n) ℝ)) qnext
  have hder :=
    (solidHarmonicAxisLift_harmonic_and_directional
      x hx q.property (r + 1)).2
  calc
    Fischer.polynomialInner n
        (solidHarmonicAxisLift n k x (r + 1)
          (p : MvPolynomial (Fin n) ℝ))
        (solidHarmonicAxisLift n k x (r + 1)
          (q : MvPolynomial (Fin n) ℝ)) =
      (2 * (r : ℝ) + harmonicAxisParameter n k - 2) *
          Fischer.polynomialInner n
            (axisPolynomial n x *
              solidHarmonicAxisLift n k x r
                (p : MvPolynomial (Fin n) ℝ))
            (solidHarmonicAxisLift n k x (r + 1)
              (q : MvPolynomial (Fin n) ℝ)) -
        ((r : ℝ) * ((r : ℝ) +
          harmonicAxisParameter n k - 3)) *
          Fischer.polynomialInner n
            (radialPolynomial n *
              solidHarmonicAxisLift n k x (r - 1)
                (p : MvPolynomial (Fin n) ℝ))
            (solidHarmonicAxisLift n k x (r + 1)
              (q : MvPolynomial (Fin n) ℝ)) := by
        rw [solidHarmonicAxisLift_succ_apply,
          fischer_polynomialInner_sub_left,
          mul_assoc, fischer_polynomialInner_constant_mul_left,
          mul_assoc, fischer_polynomialInner_constant_mul_left]
    _ =
      (2 * (r : ℝ) + harmonicAxisParameter n k - 2) *
        Fischer.polynomialInner n
          (solidHarmonicAxisLift n k x r
            (p : MvPolynomial (Fin n) ℝ))
          (directionalDerivative n x
            (solidHarmonicAxisLift n k x (r + 1)
              (q : MvPolynomial (Fin n) ℝ))) := by
        rw [hrad, mul_zero, sub_zero,
          Fischer.polynomialInner_axis_directional]
    _ = _ := by
        rw [hder, fischer_polynomialInner_constant_mul_right]
        push_cast
        ring

theorem solidHarmonicAxisLift_fischer_inner
    {n k : ℕ} (x : Euclidean n) (hx : ‖x‖ = 1)
    (p q : tangentHarmonicSubmodule n k x) (r : ℕ) :
    Fischer.polynomialInner n
        (solidHarmonicAxisLift n k x r
          (p : MvPolynomial (Fin n) ℝ))
        (solidHarmonicAxisLift n k x r
          (q : MvPolynomial (Fin n) ℝ)) =
      solidHarmonicAxisFischerScale n k r *
        Fischer.polynomialInner n
          (p : MvPolynomial (Fin n) ℝ)
          (q : MvPolynomial (Fin n) ℝ) := by
  induction r with
  | zero =>
      simp only [solidHarmonicAxisLift_zero_apply, solidHarmonicAxisFischerScale_zero, one_mul]
  | succ r ihr =>
      rw [solidHarmonicAxisLift_fischer_inner_succ x hx p q r,
        ihr, solidHarmonicAxisFischerScale_succ]
      ring

private def solidHarmonicAxisPolynomialLift
    {n : ℕ} (k r : ℕ) (x : Euclidean n) (hx : ‖x‖ = 1) :
    tangentHarmonicSubmodule n k x →ₗ[ℝ]
      harmonicHomogeneousSubmodule n (k + r) :=
  (solidHarmonicAxisLift n k x r).restrict
    (fun _ hp => solidHarmonicAxisLift_mem_harmonic
      x hx hp r)

/-- The solid harmonic axis polynomial isometry used in the spherical-code argument. -/
def solidHarmonicAxisPolynomialIsometry
    {n : ℕ} (hn : 3 ≤ n) (k r : ℕ)
    (x : Euclidean n) (hx : ‖x‖ = 1) :
    tangentHarmonicSubmodule n k x →ₗᵢ[ℝ]
      harmonicHomogeneousSubmodule n (k + r) := by
  let scale := solidHarmonicAxisFischerScale n k r
  have hscale : 0 < scale :=
    solidHarmonicAxisFischerScale_pos hn k r
  let lift :
      tangentHarmonicSubmodule n k x →ₗ[ℝ]
        harmonicHomogeneousSubmodule n (k + r) :=
    (Real.sqrt scale)⁻¹ • solidHarmonicAxisPolynomialLift k r x hx
  refine lift.isometryOfInner ?_
  intro p q
  have hsqrt : 0 < Real.sqrt scale := Real.sqrt_pos.mpr hscale
  have hsquare : Real.sqrt scale ^ 2 = scale :=
    Real.sq_sqrt hscale.le
  change
    ⟪(Real.sqrt scale)⁻¹ •
        solidHarmonicAxisPolynomialLift k r x hx p,
      (Real.sqrt scale)⁻¹ •
        solidHarmonicAxisPolynomialLift k r x hx q⟫_ℝ =
      ⟪p, q⟫_ℝ
  rw [Fischer.harmonic_inner_eq,
    Fischer.harmonicInner_eq_polynomialInner,
    Fischer.tangent_inner_eq,
    Fischer.tangentInner_eq_polynomialInner]
  change
    Fischer.polynomialInner n
        ((Real.sqrt scale)⁻¹ •
          solidHarmonicAxisLift n k x r
            (p : MvPolynomial (Fin n) ℝ))
        ((Real.sqrt scale)⁻¹ •
          solidHarmonicAxisLift n k x r
            (q : MvPolynomial (Fin n) ℝ)) =
      Fischer.polynomialInner n
        (p : MvPolynomial (Fin n) ℝ)
        (q : MvPolynomial (Fin n) ℝ)
  rw [Fischer.polynomialInner_smul_left,
    Fischer.polynomialInner_smul_right,
    solidHarmonicAxisLift_fischer_inner x hx p q r]
  change
    (Real.sqrt scale)⁻¹ *
      ((Real.sqrt scale)⁻¹ *
        (scale * Fischer.polynomialInner n
          (p : MvPolynomial (Fin n) ℝ)
          (q : MvPolynomial (Fin n) ℝ))) =
      Fischer.polynomialInner n
        (p : MvPolynomial (Fin n) ℝ)
        (q : MvPolynomial (Fin n) ℝ)
  field_simp [ne_of_gt hsqrt]
  rw [hsquare]

private def harmonicReferenceUnitAxis
    {n : ℕ} (hn : 0 < n) : Euclidean n :=
  EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ)

@[simp] theorem harmonicReferenceUnitAxis_norm
    {n : ℕ} (hn : 0 < n) :
    ‖harmonicReferenceUnitAxis hn‖ = 1 := by
  simp only [harmonicReferenceUnitAxis, PiLp.norm_single, norm_one]

private def unitHarmonicDegreeFibre
    {n : ℕ} (hn : 3 ≤ n) (k L : ℕ)
    (i : Jacobi.Index k L)
    (x : Euclidean n) (hx : ‖x‖ = 1) :
    CertificateFibre n k →ₗᵢ[ℝ]
      CertificateDegreeAmbient n k L i :=
  (HarmonicCertificateAssembly.harmonicDegreeEuclideanEquiv
    n k L (by omega) i).toLinearIsometry.comp
      ((solidHarmonicAxisPolynomialIsometry
        hn k i.val x hx).comp
          (HarmonicCertificateAssembly.tangentPolynomialEuclideanEquiv
            n k x (finrank_tangentHarmonicSubmodule
              hn k x hx)).symm.toLinearIsometry)

/-- The harmonic degree fibre used in the spherical-code argument. -/
def harmonicDegreeFibre
    {n : ℕ} (hn : 3 ≤ n) (k L : ℕ)
    (i : Jacobi.Index k L) (x : Euclidean n) :
    CertificateFibre n k →ₗᵢ[ℝ]
      CertificateDegreeAmbient n k L i := by
  have hnpositive : 0 < n := by omega
  exact
    if hx : ‖x‖ = 1 then
      unitHarmonicDegreeFibre hn k L i x hx
    else
      unitHarmonicDegreeFibre hn k L i
        (harmonicReferenceUnitAxis hnpositive)
        (harmonicReferenceUnitAxis_norm hnpositive)

@[simp] theorem harmonicDegreeFibre_of_unit
    {n : ℕ} (hn : 3 ≤ n) (k L : ℕ)
    (i : Jacobi.Index k L)
    (x : Euclidean n) (hx : ‖x‖ = 1) :
    harmonicDegreeFibre hn k L i x =
      unitHarmonicDegreeFibre hn k L i x hx := by
  simp only [harmonicDegreeFibre, hx, ↓reduceDIte]

end

section


namespace JacobiSymmetrization

open SpherePacking.Gegenbauer

theorem harmonicDimension_scaled_choose
    {n : ℕ} (hn : 3 ≤ n) (i : ℕ) :
    (n - 2) * harmonicDimension n i =
      (2 * i + n - 2) * (n + i - 3).choose i := by
  cases i with
  | zero =>
      simp only [harmonicDimension, mul_one, mul_zero, zero_add, add_zero, Nat.choose_zero_right]
  | succ i =>
      have htop : n + i - 1 = (n + i - 2) + 1 := by omega
      have hshift : n + (i + 1) - 3 = n + i - 2 := by omega
      have hfactor : 2 * (i + 1) + n - 2 = n + 2 * i := by omega
      have hsub : n + i - 2 - i = n - 2 := by omega
      have hnsub : n - 2 + 2 = n := by omega
      have hchoose := Nat.choose_succ_right_eq (n + i - 2) i
      rw [hsub] at hchoose
      simp only [harmonicDimension]
      rw [htop, Nat.choose_succ_succ, hshift, hfactor]
      simp only [Nat.succ_eq_add_one] at hchoose ⊢
      nlinarith

theorem harmonicDimension_cross_mul
    {n : ℕ} (hn : 3 ≤ n) (i : ℕ) :
    harmonicDimension n i * (2 * i + n) * (i + n - 2) =
      harmonicDimension n (i + 1) * (2 * i + n - 2) * (i + 1) := by
  have hnpos : 0 < n - 2 := by omega
  have hchoose :
      (n + i - 3).choose i * (n + i - 2) =
        (n + i - 2).choose (i + 1) * (i + 1) := by
    have h := Nat.add_one_mul_choose_eq (n + i - 3) i
    have htop : n + i - 3 + 1 = n + i - 2 := by omega
    rw [htop] at h
    simpa only [mul_comm] using h
  have hnext := harmonicDimension_scaled_choose hn (i + 1)
  have hfactor : 2 * (i + 1) + n - 2 = 2 * i + n := by omega
  have hshift : n + (i + 1) - 3 = n + i - 2 := by omega
  rw [hfactor, hshift] at hnext
  apply Nat.mul_left_cancel hnpos
  calc
    (n - 2) *
        (harmonicDimension n i * (2 * i + n) * (i + n - 2)) =
      ((n - 2) * harmonicDimension n i) *
        (2 * i + n) * (i + n - 2) := by ring
    _ = ((2 * i + n - 2) * (n + i - 3).choose i) *
        (2 * i + n) * (i + n - 2) := by
          rw [harmonicDimension_scaled_choose hn i]
    _ = (2 * i + n - 2) * (2 * i + n) *
        ((n + i - 3).choose i * (n + i - 2)) := by
          have hindex : i + n - 2 = n + i - 2 := by omega
          rw [hindex]
          ring
    _ = (2 * i + n - 2) * (2 * i + n) *
        ((n + i - 2).choose (i + 1) * (i + 1)) := by
          rw [hchoose]
    _ = ((n - 2) * harmonicDimension n (i + 1)) *
        (2 * i + n - 2) * (i + 1) := by
          rw [hnext]
          ring
    _ = (n - 2) *
        (harmonicDimension n (i + 1) *
          (2 * i + n - 2) * (i + 1)) := by ring

end JacobiSymmetrization

end

section


open scoped BigOperators InnerProductSpace

namespace SourceJacobiWeights

theorem positiveRadicalSymmetrization
    {d e a b p q r : ℝ}
    (hd : 0 < d) (he : 0 < e)
    (ha : 0 < a) (hb : 0 < b)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 ≤ r)
    (hcross : d * q * b = e * p * a) :
    (r / (a * p)) * Real.sqrt d =
      (r / Real.sqrt (a * b * p * q)) * Real.sqrt e := by
  have hrad : 0 < a * b * p * q := by positivity
  have hsquare :
      ((r / (a * p)) * Real.sqrt d) ^ 2 =
        ((r / Real.sqrt (a * b * p * q)) *
          Real.sqrt e) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hd.le,
      Real.sq_sqrt he.le, div_pow, div_pow,
      Real.sq_sqrt hrad.le]
    field_simp [ha.ne', hb.ne', hp.ne', hq.ne']
    linear_combination r ^ 2 * hcross
  have hleft : 0 ≤ (r / (a * p)) * Real.sqrt d := by
    positivity
  have hright : 0 ≤
      (r / Real.sqrt (a * b * p * q)) * Real.sqrt e := by
    positivity
  nlinarith

theorem alphaSq_sqrt_harmonicDimension
    {n k i : ℕ} (hn : 3 ≤ n) (hki : k ≤ i) :
    Gegenbauer.alphaSq n k i *
        Real.sqrt (Gegenbauer.harmonicDimension n i : ℝ) =
      Gegenbauer.jacobiCoefficient n k i *
        Real.sqrt (Gegenbauer.harmonicDimension n (i + 1) : ℝ) := by
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hireal : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have hkreal : (k : ℝ) ≤ i := by exact_mod_cast hki
  have hd : (0 : ℝ) < Gegenbauer.harmonicDimension n i := by
    exact_mod_cast
      Gegenbauer.harmonicDimension_pos (by omega : 2 ≤ n) i
  have he : (0 : ℝ) < Gegenbauer.harmonicDimension n (i + 1) := by
    exact_mod_cast
      Gegenbauer.harmonicDimension_pos (by omega : 2 ≤ n) (i + 1)
  have ha : 0 < (i : ℝ) + 1 := by positivity
  have hb : 0 < (i : ℝ) + n - 2 := by linarith
  have hp : 0 < 2 * (i : ℝ) + n - 2 := by linarith
  have hq : 0 < 2 * (i : ℝ) + n := by linarith
  have hr : 0 ≤
      ((i : ℝ) - k + 1) * ((i : ℝ) + k + n - 2) := by
    have hkzero : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    exact mul_nonneg (by linarith) (by linarith)
  have hcross0 :=
    JacobiSymmetrization.harmonicDimension_cross_mul hn i
  have hcross :
      (Gegenbauer.harmonicDimension n i : ℝ) *
          (2 * (i : ℝ) + n) * ((i : ℝ) + n - 2) =
        (Gegenbauer.harmonicDimension n (i + 1) : ℝ) *
          (2 * (i : ℝ) + n - 2) * ((i : ℝ) + 1) := by
    have hh := congrArg (fun z : ℕ => (z : ℝ)) hcross0
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
      Nat.cast_sub (show 2 ≤ i + n by omega),
      Nat.cast_sub (show 2 ≤ 2 * i + n by omega)] at hh
    convert hh using 1
    ring
  exact positiveRadicalSymmetrization hd he ha hb hp hq hr hcross

theorem betaSq_sqrt_harmonicDimension
    {n k i : ℕ} (hn : 3 ≤ n) (hki : k ≤ i) :
    Gegenbauer.betaSq n k (i + 1) *
        Real.sqrt (Gegenbauer.harmonicDimension n (i + 1) : ℝ) =
      Gegenbauer.jacobiCoefficient n k i *
        Real.sqrt (Gegenbauer.harmonicDimension n i : ℝ) := by
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hireal : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have hkreal : (k : ℝ) ≤ i := by exact_mod_cast hki
  have hd : (0 : ℝ) < Gegenbauer.harmonicDimension n i := by
    exact_mod_cast
      Gegenbauer.harmonicDimension_pos (by omega : 2 ≤ n) i
  have he : (0 : ℝ) < Gegenbauer.harmonicDimension n (i + 1) := by
    exact_mod_cast
      Gegenbauer.harmonicDimension_pos (by omega : 2 ≤ n) (i + 1)
  have ha : 0 < (i : ℝ) + 1 := by positivity
  have hb : 0 < (i : ℝ) + n - 2 := by linarith
  have hp : 0 < 2 * (i : ℝ) + n - 2 := by linarith
  have hq : 0 < 2 * (i : ℝ) + n := by linarith
  have hr : 0 ≤
      ((i : ℝ) - k + 1) * ((i : ℝ) + k + n - 2) := by
    have hkzero : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    exact mul_nonneg (by linarith) (by linarith)
  have hcross0 :=
    JacobiSymmetrization.harmonicDimension_cross_mul hn i
  have hcross :
      (Gegenbauer.harmonicDimension n i : ℝ) *
          (2 * (i : ℝ) + n) * ((i : ℝ) + n - 2) =
        (Gegenbauer.harmonicDimension n (i + 1) : ℝ) *
          (2 * (i : ℝ) + n - 2) * ((i : ℝ) + 1) := by
    have hh := congrArg (fun z : ℕ => (z : ℝ)) hcross0
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
      Nat.cast_sub (show 2 ≤ i + n by omega),
      Nat.cast_sub (show 2 ≤ 2 * i + n by omega)] at hh
    convert hh using 1
    ring
  have h := positiveRadicalSymmetrization
    he hd hb ha hq hp hr hcross.symm
  unfold Gegenbauer.betaSq Gegenbauer.jacobiCoefficient
  push_cast
  convert h using 1 <;> ring_nf

private def sourceChannelCoefficient
    (n k L : ℕ) (m i : Jacobi.Index k L) : ℝ :=
  if i.val + 1 = m.val then
    Gegenbauer.alphaSq n k (k + i.val)
  else if m.val + 1 = i.val then
    Gegenbauer.betaSq n k (k + i.val)
  else
    0

theorem jacobiMatrix_mul_sqrt_harmonicDimension
    {n k L : ℕ} (hn : 3 ≤ n)
    (m i : Jacobi.Index k L) :
    Gegenbauer.jacobiMatrix n k L m i *
        Real.sqrt (Gegenbauer.harmonicDimension n (k + m.val) : ℝ) =
      sourceChannelCoefficient n k L m i *
        Real.sqrt (Gegenbauer.harmonicDimension n (k + i.val) : ℝ) := by
  by_cases hupper : i.val + 1 = m.val
  · have hlower : m.val + 1 ≠ i.val := by omega
    have hdegree : k + m.val = k + i.val + 1 := by omega
    simpa only [Gegenbauer.jacobiMatrix, hlower, ↓reduceIte, hupper, hdegree,
      sourceChannelCoefficient] using
      (alphaSq_sqrt_harmonicDimension hn (show k ≤ k + i.val by omega)).symm
  · by_cases hlower : m.val + 1 = i.val
    · have hdegree : k + i.val = k + m.val + 1 := by omega
      simpa only [Gegenbauer.jacobiMatrix, hlower, ↓reduceIte, sourceChannelCoefficient, hupper,
        hdegree] using
        (betaSq_sqrt_harmonicDimension hn (show k ≤ k + m.val by omega)).symm
    · simp only [Gegenbauer.jacobiMatrix, hlower, ↓reduceIte, hupper, zero_mul,
        sourceChannelCoefficient]

theorem finiteGramRecurrenceWeight_eigenrecurrence
    {n k L : ℕ} (hn : 3 ≤ n)
    (v : Jacobi.Space k L) (eigenvalue : ℝ)
    (heigen : Jacobi.operator n k L v = eigenvalue • v)
    (m : Jacobi.Index k L) :
    (∑ i : Jacobi.Index k L,
      sourceChannelCoefficient n k L m i *
        finiteGramRecurrenceWeight n k L v i) =
      eigenvalue * finiteGramRecurrenceWeight n k L v m := by
  classical
  have hcoordinate := congrArg
    (fun z : Jacobi.Space k L => z m) heigen
  change
    (∑ i : Jacobi.Index k L,
      Gegenbauer.jacobiMatrix n k L m i * v i) =
      eigenvalue * v m at hcoordinate
  calc
    (∑ i : Jacobi.Index k L,
      sourceChannelCoefficient n k L m i *
        finiteGramRecurrenceWeight n k L v i) =
      (∑ i : Jacobi.Index k L,
        (Gegenbauer.jacobiMatrix n k L m i * v i) *
          Real.sqrt
            (Gegenbauer.harmonicDimension n (k + m.val) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i _
        unfold finiteGramRecurrenceWeight
        have h := jacobiMatrix_mul_sqrt_harmonicDimension hn m i
        calc
          sourceChannelCoefficient n k L m i *
              (Real.sqrt
                (Gegenbauer.harmonicDimension n (k + i.val) : ℝ) * v i) =
            (sourceChannelCoefficient n k L m i *
              Real.sqrt
                (Gegenbauer.harmonicDimension n (k + i.val) : ℝ)) * v i := by
                ring
          _ = (Gegenbauer.jacobiMatrix n k L m i *
                Real.sqrt
                  (Gegenbauer.harmonicDimension n (k + m.val) : ℝ)) *
                v i := by
                  rw [← h]
          _ = (Gegenbauer.jacobiMatrix n k L m i * v i) *
                Real.sqrt
                  (Gegenbauer.harmonicDimension n (k + m.val) : ℝ) := by
                  ring
    _ = (∑ i : Jacobi.Index k L,
          Gegenbauer.jacobiMatrix n k L m i * v i) *
        Real.sqrt
          (Gegenbauer.harmonicDimension n (k + m.val) : ℝ) := by
        rw [Finset.sum_mul]
    _ = eigenvalue * finiteGramRecurrenceWeight n k L v m := by
        rw [hcoordinate]
        unfold finiteGramRecurrenceWeight
        ring

theorem jacobiMatrix_adjacent_pos
    {n k L : ℕ} (hn : 3 ≤ n)
    (p q : Jacobi.Index k L)
    (hadjacent : p.val + 1 = q.val ∨ q.val + 1 = p.val) :
    0 < Gegenbauer.jacobiMatrix n k L p q := by
  rcases hadjacent with hforward | hbackward
  · exact Gegenbauer.jacobiMatrix_upper_pos hn p q hforward
  · have hnot : p.val + 1 ≠ q.val := by omega
    simpa only [Gegenbauer.jacobiMatrix, hnot, ↓reduceIte, hbackward, gt_iff_lt] using
      Gegenbauer.jacobiCoefficient_pos hn (show k ≤ k + q.val by omega)

theorem sourceChannelCoefficient_pos_of_adjacent
    {n k L : ℕ} (hn : 3 ≤ n)
    (m i : Jacobi.Index k L)
    (hadjacent : m.val + 1 = i.val ∨ i.val + 1 = m.val) :
    0 < sourceChannelCoefficient n k L m i := by
  have hsource_dimension :
      0 < Real.sqrt
        (Gegenbauer.harmonicDimension n (k + i.val) : ℝ) := by
    apply Real.sqrt_pos.mpr
    exact_mod_cast Gegenbauer.harmonicDimension_pos
      (show 2 ≤ n by omega) (k + i.val)
  have htarget_dimension :
      0 < Real.sqrt
        (Gegenbauer.harmonicDimension n (k + m.val) : ℝ) := by
    apply Real.sqrt_pos.mpr
    exact_mod_cast Gegenbauer.harmonicDimension_pos
      (show 2 ≤ n by omega) (k + m.val)
  have hproduct :
      0 < sourceChannelCoefficient n k L m i *
        Real.sqrt
          (Gegenbauer.harmonicDimension n (k + i.val) : ℝ) := by
    rw [← jacobiMatrix_mul_sqrt_harmonicDimension hn m i]
    exact mul_pos
      (jacobiMatrix_adjacent_pos hn m i hadjacent)
      htarget_dimension
  exact (mul_pos_iff_of_pos_right hsource_dimension).mp hproduct

theorem nonnegative_eigenvector_zero_propagates
    {n k L : ℕ} (hn : 3 ≤ n)
    (v : Jacobi.Space k L) (eigenvalue : ℝ)
    (heigen : Jacobi.operator n k L v = eigenvalue • v)
    (hnonnegative : ∀ i : Jacobi.Index k L, 0 ≤ v i)
    (p q : Jacobi.Index k L)
    (hp : v p = 0)
    (hadjacent : p.val + 1 = q.val ∨ q.val + 1 = p.val) :
    v q = 0 := by
  classical
  have hcoordinate := congrArg
    (fun z : Jacobi.Space k L => z p) heigen
  change
    (∑ i : Jacobi.Index k L,
      Gegenbauer.jacobiMatrix n k L p i * v i) =
      eigenvalue * v p at hcoordinate
  rw [hp, mul_zero] at hcoordinate
  have hterms :
      ∀ i ∈ (Finset.univ : Finset (Jacobi.Index k L)),
        0 ≤ Gegenbauer.jacobiMatrix n k L p i * v i := by
    intro i _
    apply mul_nonneg
    · simpa only [Jacobi.matrix] using Perron.matrix_entry_nonneg hn k L p i
    · exact hnonnegative i
  have hterm : Gegenbauer.jacobiMatrix n k L p q * v q = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hcoordinate
      q (Finset.mem_univ q)
  exact (mul_eq_zero.mp hterm).resolve_left
    (jacobiMatrix_adjacent_pos hn p q hadjacent).ne'

theorem nonnegative_eigenvector_coordinate_pos
    {n k L : ℕ} (hn : 3 ≤ n)
    (v : Jacobi.Space k L) (eigenvalue : ℝ)
    (heigen : Jacobi.operator n k L v = eigenvalue • v)
    (hnonnegative : ∀ i : Jacobi.Index k L, 0 ≤ v i)
    (hnonzero : v ≠ 0)
    (i : Jacobi.Index k L) :
    0 < v i := by
  rcases (hnonnegative i).eq_or_lt with hzero | hpositive
  · exfalso
    apply hnonzero
    apply PiLp.ext
    intro q
    change v q = 0
    have hchain :
        ∀ distance : ℕ,
          ∀ q : Jacobi.Index k L,
            Nat.dist i.val q.val = distance → v q = 0 := by
      intro distance
      induction distance using Nat.strong_induction_on with
      | h distance ih =>
          intro q hdistance
          by_cases hequal : i.val = q.val
          · have hiq : i = q := Fin.ext hequal
            simpa only [hiq] using hzero.symm
          · by_cases hforward : i.val < q.val
            · let previous : Jacobi.Index k L :=
                ⟨q.val - 1, by have hq := q.isLt; omega⟩
              have hprevious_distance :
                  Nat.dist i.val previous.val < distance := by
                rw [Nat.dist_eq_sub_of_le
                  (show i.val ≤ previous.val by
                    dsimp [previous]
                    omega)]
                rw [Nat.dist_eq_sub_of_le
                  (Nat.le_of_lt hforward)] at hdistance
                dsimp [previous]
                omega
              have hprevious_zero : v previous = 0 :=
                ih (Nat.dist i.val previous.val)
                  hprevious_distance previous rfl
              exact nonnegative_eigenvector_zero_propagates
                hn v eigenvalue heigen hnonnegative previous q
                hprevious_zero (Or.inl (by
                  dsimp [previous]
                  omega))
            · have hbackward : q.val < i.val := by omega
              let next : Jacobi.Index k L :=
                ⟨q.val + 1, by have hi := i.isLt; omega⟩
              have hnext_distance :
                  Nat.dist i.val next.val < distance := by
                rw [Nat.dist_eq_sub_of_le_right
                  (show next.val ≤ i.val by
                    dsimp [next]
                    omega)]
                rw [Nat.dist_eq_sub_of_le_right
                  (Nat.le_of_lt hbackward)] at hdistance
                dsimp [next]
                omega
              have hnext_zero : v next = 0 :=
                ih (Nat.dist i.val next.val)
                  hnext_distance next rfl
              exact nonnegative_eigenvector_zero_propagates
                hn v eigenvalue heigen hnonnegative next q
                hnext_zero (Or.inr (by
                  dsimp [next]))
    exact hchain (Nat.dist i.val q.val) q rfl
  · exact hpositive

theorem finiteGramRecurrenceWeight_pos_of_eigenvector
    {n k L : ℕ} (hn : 3 ≤ n)
    (v : Jacobi.Space k L) (eigenvalue : ℝ)
    (heigen : Jacobi.operator n k L v = eigenvalue • v)
    (hnonnegative : ∀ i : Jacobi.Index k L, 0 ≤ v i)
    (hnonzero : v ≠ 0)
    (i : Jacobi.Index k L) :
    0 < finiteGramRecurrenceWeight n k L v i := by
  unfold finiteGramRecurrenceWeight
  apply mul_pos
  · apply Real.sqrt_pos.mpr
    exact_mod_cast
      Gegenbauer.harmonicDimension_pos
        (show 2 ≤ n by omega) (k + i.val)
  · exact nonnegative_eigenvector_coordinate_pos
      hn v eigenvalue heigen hnonnegative hnonzero i

theorem nonnegative_eigenvalue_pos_of_lt
    {n k L : ℕ} (hn : 3 ≤ n) (hkl : k < L)
    (v : Jacobi.Space k L) (eigenvalue : ℝ)
    (heigen : Jacobi.operator n k L v = eigenvalue • v)
    (hnonnegative : ∀ i : Jacobi.Index k L, 0 ≤ v i)
    (hnonzero : v ≠ 0) :
    0 < eigenvalue := by
  classical
  let p : Jacobi.Index k L := ⟨0, by omega⟩
  let q : Jacobi.Index k L := ⟨1, by omega⟩
  have hp : 0 < v p :=
    nonnegative_eigenvector_coordinate_pos
      hn v eigenvalue heigen hnonnegative hnonzero p
  have hq : 0 < v q :=
    nonnegative_eigenvector_coordinate_pos
      hn v eigenvalue heigen hnonnegative hnonzero q
  have hentry : 0 < Gegenbauer.jacobiMatrix n k L p q := by
    apply jacobiMatrix_adjacent_pos hn p q
    exact Or.inl (by rfl)
  have hterms :
      ∀ i ∈ (Finset.univ : Finset (Jacobi.Index k L)),
        0 ≤ Gegenbauer.jacobiMatrix n k L p i * v i := by
    intro i _
    exact mul_nonneg
      (by simpa only [Jacobi.matrix] using Perron.matrix_entry_nonneg hn k L p i)
      (hnonnegative i)
  have hsum :
      0 < ∑ i : Jacobi.Index k L,
        Gegenbauer.jacobiMatrix n k L p i * v i := by
    apply Finset.sum_pos' hterms
    exact ⟨q, Finset.mem_univ q, mul_pos hentry hq⟩
  have hcoordinate := congrArg
    (fun z : Jacobi.Space k L => z p) heigen
  change
    (∑ i : Jacobi.Index k L,
      Gegenbauer.jacobiMatrix n k L p i * v i) =
      eigenvalue * v p at hcoordinate
  rw [hcoordinate] at hsum
  exact (mul_pos_iff_of_pos_right hp).mp hsum

end SourceJacobiWeights

end

section


namespace HarmonicPerronPositivity

open HarmonicCertificateAssembly

theorem harmonicPerronWeights_ne_zero
    (n k L : ℕ) (hn : 3 ≤ n) :
    harmonicPerronWeights n k L hn ≠ 0 := by
  intro hzero
  have hunit := harmonicPerronWeights_unit n k L hn
  rw [hzero, norm_zero] at hunit
  norm_num at hunit

theorem harmonicRecurrenceWeight_pos
    (n k L : ℕ) (hn : 3 ≤ n)
    (i : Jacobi.Index k L) :
    0 < harmonicRecurrenceWeight n k L hn i := by
  exact SourceJacobiWeights.finiteGramRecurrenceWeight_pos_of_eigenvector
    hn (harmonicPerronWeights n k L hn)
    (Jacobi.topEigenvalue n k L)
    (harmonicPerronWeights_eigenvector n k L hn)
    (harmonicPerronWeights_nonneg n k L hn)
    (harmonicPerronWeights_ne_zero n k L hn) i

theorem harmonicFibreAmplitudes_pos
    (n k L : ℕ) (hn : 3 ≤ n)
    (i : Jacobi.Index k L) :
    0 < harmonicFibreAmplitudes n k L hn i := by
  rw [harmonicFibreAmplitudes_apply]
  unfold finiteGramFibreAmplitude
  apply Real.sqrt_pos.mpr
  exact div_pos (harmonicRecurrenceWeight_pos n k L hn i)
    (harmonicRecurrenceNormalization_pos n k L hn)

theorem topEigenvalue_pos_of_lt
    {n k L : ℕ} (hn : 3 ≤ n) (hkl : k < L) :
    0 < Jacobi.topEigenvalue n k L := by
  exact SourceJacobiWeights.nonnegative_eigenvalue_pos_of_lt
    hn hkl (harmonicPerronWeights n k L hn)
    (Jacobi.topEigenvalue n k L)
    (harmonicPerronWeights_eigenvector n k L hn)
    (harmonicPerronWeights_nonneg n k L hn)
    (harmonicPerronWeights_ne_zero n k L hn)

end HarmonicPerronPositivity

end

section


open scoped BigOperators InnerProductSpace

namespace HarmonicCoordinateChannels

private abbrev MatrixCoordinateIndex (n k L : ℕ) :=
  Σ _ : Fin (truncatedHarmonicDimension n k L),
    Fin (truncatedHarmonicDimension n k L)

private abbrev ProjectionMatrixSpace (n k L : ℕ) :=
  PiLp 2 (fun _ : Fin (truncatedHarmonicDimension n k L) =>
    CertificateAmbient n k L)

private abbrev HarmonicRowChannelSpace (n k L : ℕ) :=
  PiLp 2 (fun _ : Fin n => CertificateAmbient n k L)

private abbrev HarmonicDegreeRowChannelSpace
    (n k L : ℕ) (i : Jacobi.Index k L) :=
  PiLp 2 (fun _ : Fin n => CertificateDegreeAmbient n k L i)

theorem sourceChannelCoefficient_nonneg
    {n k L : ℕ} (hn : 3 ≤ n)
    (m i : Jacobi.Index k L) :
    0 ≤ SourceJacobiWeights.sourceChannelCoefficient n k L m i := by
  have hdimension :
      0 < Real.sqrt
        (Gegenbauer.harmonicDimension n (k + i.val) : ℝ) := by
    apply Real.sqrt_pos.mpr
    exact_mod_cast Gegenbauer.harmonicDimension_pos
      (by omega : 2 ≤ n) (k + i.val)
  have hmatrix :
      0 ≤ Gegenbauer.jacobiMatrix n k L m i := by
    simpa only [Jacobi.matrix] using Perron.matrix_entry_nonneg hn k L m i
  have hsource :=
    SourceJacobiWeights.jacobiMatrix_mul_sqrt_harmonicDimension
      hn m i
  have hproduct :
      0 ≤ SourceJacobiWeights.sourceChannelCoefficient n k L m i *
        Real.sqrt
          (Gegenbauer.harmonicDimension n (k + i.val) : ℝ) := by
    rw [← hsource]
    exact mul_nonneg hmatrix (Real.sqrt_nonneg _)
  nlinarith

private def sourceAdjacentBlockCoefficient
    (n k L : ℕ) (hn : 3 ≤ n)
    (target source : Jacobi.Index k L) : ℝ :=
  Real.sqrt
    (SourceJacobiWeights.sourceChannelCoefficient n k L source target *
      HarmonicCertificateAssembly.harmonicRecurrenceWeight
        n k L hn target /
      (Jacobi.topEigenvalue n k L *
        HarmonicCertificateAssembly.harmonicRecurrenceWeight
          n k L hn source))

theorem sourceAdjacentBlockCoefficient_sq
    {n k L : ℕ} (hn : 3 ≤ n) (hkl : k < L)
    (target source : Jacobi.Index k L) :
    sourceAdjacentBlockCoefficient n k L hn target source ^ 2 =
      SourceJacobiWeights.sourceChannelCoefficient
        n k L source target *
        HarmonicCertificateAssembly.harmonicRecurrenceWeight
          n k L hn target /
      (Jacobi.topEigenvalue n k L *
        HarmonicCertificateAssembly.harmonicRecurrenceWeight
          n k L hn source) := by
  unfold sourceAdjacentBlockCoefficient
  apply Real.sq_sqrt
  exact div_nonneg
    (mul_nonneg (sourceChannelCoefficient_nonneg hn source target)
      (HarmonicPerronPositivity.harmonicRecurrenceWeight_pos
        n k L hn target).le)
    (mul_pos
      (HarmonicPerronPositivity.topEigenvalue_pos_of_lt hn hkl)
      (HarmonicPerronPositivity.harmonicRecurrenceWeight_pos
        n k L hn source)).le

theorem sourceAdjacentBlockCoefficient_sq_sum
    {n k L : ℕ} (hn : 3 ≤ n) (hkl : k < L)
    (source : Jacobi.Index k L) :
    (∑ target : Jacobi.Index k L,
      sourceAdjacentBlockCoefficient n k L hn target source ^ 2) = 1 := by
  classical
  simp_rw [sourceAdjacentBlockCoefficient_sq hn hkl]
  rw [← Finset.sum_div]
  have hrecurrence :=
    SourceJacobiWeights.finiteGramRecurrenceWeight_eigenrecurrence
      hn (HarmonicCertificateAssembly.harmonicPerronWeights
        n k L hn)
      (Jacobi.topEigenvalue n k L)
      (HarmonicCertificateAssembly.harmonicPerronWeights_eigenvector
        n k L hn) source
  change
    (∑ target : Jacobi.Index k L,
      SourceJacobiWeights.sourceChannelCoefficient
        n k L source target *
        HarmonicCertificateAssembly.harmonicRecurrenceWeight
          n k L hn target) =
      Jacobi.topEigenvalue n k L *
        HarmonicCertificateAssembly.harmonicRecurrenceWeight
          n k L hn source at hrecurrence
  rw [hrecurrence]
  exact div_self
    (mul_pos
      (HarmonicPerronPositivity.topEigenvalue_pos_of_lt hn hkl)
      (HarmonicPerronPositivity.harmonicRecurrenceWeight_pos
        n k L hn source)).ne'

theorem sourceAdjacentBlockCoefficient_amplitude_identity
    {n k L : ℕ} (hn : 3 ≤ n) (hkl : k < L)
    (target source : Jacobi.Index k L) :
    sourceAdjacentBlockCoefficient n k L hn target source *
        HarmonicCertificateAssembly.harmonicFibreAmplitudes
          n k L hn target *
        Real.sqrt
          (SourceJacobiWeights.sourceChannelCoefficient
            n k L source target) =
      sourceAdjacentBlockCoefficient n k L hn target source ^ 2 *
        Real.sqrt (Jacobi.topEigenvalue n k L) *
        HarmonicCertificateAssembly.harmonicFibreAmplitudes
          n k L hn source := by
  have hcoefficient := sourceChannelCoefficient_nonneg
    hn source target
  have heigen :=
    HarmonicPerronPositivity.topEigenvalue_pos_of_lt hn hkl
  have hsource :=
    HarmonicPerronPositivity.harmonicRecurrenceWeight_pos
      n k L hn source
  have hnormal :=
    HarmonicCertificateAssembly.harmonicRecurrenceNormalization_pos
      n k L hn
  have hleft :
      0 ≤ sourceAdjacentBlockCoefficient n k L hn target source *
        HarmonicCertificateAssembly.harmonicFibreAmplitudes
          n k L hn target *
        Real.sqrt
          (SourceJacobiWeights.sourceChannelCoefficient
            n k L source target) := by
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _)
        (HarmonicPerronPositivity.harmonicFibreAmplitudes_pos
          n k L hn target).le)
      (Real.sqrt_nonneg _)
  have hright :
      0 ≤ sourceAdjacentBlockCoefficient n k L hn target source ^ 2 *
        Real.sqrt (Jacobi.topEigenvalue n k L) *
        HarmonicCertificateAssembly.harmonicFibreAmplitudes
          n k L hn source := by
    exact mul_nonneg
      (mul_nonneg (sq_nonneg _)
        (Real.sqrt_nonneg _))
      (HarmonicPerronPositivity.harmonicFibreAmplitudes_pos
        n k L hn source).le
  have hsquare :
      (sourceAdjacentBlockCoefficient n k L hn target source *
        HarmonicCertificateAssembly.harmonicFibreAmplitudes
          n k L hn target *
        Real.sqrt
          (SourceJacobiWeights.sourceChannelCoefficient
            n k L source target)) ^ 2 =
      (sourceAdjacentBlockCoefficient n k L hn target source ^ 2 *
        Real.sqrt (Jacobi.topEigenvalue n k L) *
        HarmonicCertificateAssembly.harmonicFibreAmplitudes
          n k L hn source) ^ 2 := by
    simp only [mul_pow]
    rw [sourceAdjacentBlockCoefficient_sq hn hkl target source,
      HarmonicCertificateAssembly.harmonicFibreAmplitudes_sq
        n k L hn target,
      Real.sq_sqrt hcoefficient,
      Real.sq_sqrt heigen.le,
      HarmonicCertificateAssembly.harmonicFibreAmplitudes_sq
        n k L hn source]
    field_simp [heigen.ne', hsource.ne', hnormal.ne']
  nlinarith

theorem sourceAdjacentBlockCoefficient_amplitude_sum
    {n k L : ℕ} (hn : 3 ≤ n) (hkl : k < L)
    (source : Jacobi.Index k L) :
    (∑ target : Jacobi.Index k L,
      sourceAdjacentBlockCoefficient n k L hn target source *
        HarmonicCertificateAssembly.harmonicFibreAmplitudes
          n k L hn target *
        Real.sqrt
          (SourceJacobiWeights.sourceChannelCoefficient
            n k L source target)) =
      Real.sqrt (Jacobi.topEigenvalue n k L) *
        HarmonicCertificateAssembly.harmonicFibreAmplitudes
          n k L hn source := by
  simp_rw [sourceAdjacentBlockCoefficient_amplitude_identity
    hn hkl]
  rw [← Finset.sum_mul, ← Finset.sum_mul,
    sourceAdjacentBlockCoefficient_sq_sum hn hkl]
  simp only [one_mul, HarmonicCertificateAssembly.harmonicFibreAmplitudes_apply]

private def harmonicDegreeBlockEquiv
    (n k L : ℕ) (hkl : k ≤ L) :
    HarmonicCertificateAssembly.DegreeBlockPi n k L ≃ₗᵢ[ℝ]
      CertificateAmbient n k L :=
  (HarmonicCertificateAssembly.degreeBlockFlatten n k L).trans
    (HarmonicCertificateAssembly.degreeBlockReindex n k L hkl)

private def harmonicDegreeAxisTensor
    (n k L : ℕ) (i : Jacobi.Index k L)
    (x : Euclidean n) :
    CertificateDegreeAmbient n k L i →ₗ[ℝ]
      HarmonicDegreeRowChannelSpace n k L i where
  toFun u := WithLp.toLp 2 (fun a : Fin n => x a • u)
  map_add' u v := by
    apply PiLp.ext
    intro a
    exact smul_add (x a) u v
  map_smul' c u := by
    apply PiLp.ext
    intro a
    exact smul_comm (x a) c u

/-- Data encoding the source adjacent channel construction. -/
structure SourceAdjacentChannelData
    (n k L : ℕ)
    (degreeFibre : (i : Jacobi.Index k L) → Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ]
        CertificateDegreeAmbient n k L i) where
  /-- The channel component. -/
  channel : (target source : Jacobi.Index k L) →
    CertificateDegreeAmbient n k L source →ₗ[ℝ]
      HarmonicDegreeRowChannelSpace n k L target
  channel_inner :
    ∀ (target source : Jacobi.Index k L),
      SourceJacobiWeights.sourceChannelCoefficient
        n k L source target ≠ 0 →
      ∀ u v : CertificateDegreeAmbient n k L source,
        ⟪channel target source u,
          channel target source v⟫_ℝ = ⟪u, v⟫_ℝ
  channel_zero :
    ∀ (target source : Jacobi.Index k L),
      SourceJacobiWeights.sourceChannelCoefficient
        n k L source target = 0 →
      channel target source = 0
  channel_orthogonal :
    ∀ (target source₁ source₂ : Jacobi.Index k L),
      source₁ ≠ source₂ →
      ∀ (u : CertificateDegreeAmbient n k L source₁)
        (v : CertificateDegreeAmbient n k L source₂),
        ⟪channel target source₁ u,
          channel target source₂ v⟫_ℝ = 0
  axis_projection :
    ∀ x ∈ unitSphere n,
      ∀ (target source : Jacobi.Index k L)
        (u : CertificateFibre n k),
        (channel target source).adjoint
          (harmonicDegreeAxisTensor n k L target x
            (degreeFibre target x u)) =
          Real.sqrt
              (SourceJacobiWeights.sourceChannelCoefficient
                n k L source target) •
            degreeFibre source x u

private abbrev SourceTargetRowSpace (n k L : ℕ) :=
  PiLp 2 (fun target : Jacobi.Index k L =>
    HarmonicDegreeRowChannelSpace n k L target)

private def sourceAdjacentTargetLinearMap
    {n k L : ℕ} (hn : 3 ≤ n)
    (degreeFibre : (i : Jacobi.Index k L) → Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ]
        CertificateDegreeAmbient n k L i)
    (adjacent : SourceAdjacentChannelData n k L degreeFibre) :
    HarmonicCertificateAssembly.DegreeBlockPi n k L →ₗ[ℝ]
      SourceTargetRowSpace n k L where
  toFun v := WithLp.toLp 2
    (fun target : Jacobi.Index k L =>
      ∑ source : Jacobi.Index k L,
        sourceAdjacentBlockCoefficient n k L hn target source •
          adjacent.channel target source (v source))
  map_add' u v := by
    apply PiLp.ext
    intro target
    change
      (∑ source : Jacobi.Index k L,
        sourceAdjacentBlockCoefficient n k L hn target source •
          adjacent.channel target source
            (u source + v source)) =
        (∑ source : Jacobi.Index k L,
          sourceAdjacentBlockCoefficient n k L hn target source •
            adjacent.channel target source (u source)) +
        (∑ source : Jacobi.Index k L,
          sourceAdjacentBlockCoefficient n k L hn target source •
            adjacent.channel target source (v source))
    simp_rw [map_add, smul_add]
    rw [Finset.sum_add_distrib]
  map_smul' c u := by
    apply PiLp.ext
    intro target
    change
      (∑ source : Jacobi.Index k L,
        sourceAdjacentBlockCoefficient n k L hn target source •
          adjacent.channel target source (c • u source)) =
        c •
          (∑ source : Jacobi.Index k L,
            sourceAdjacentBlockCoefficient n k L hn target source •
              adjacent.channel target source (u source))
    simp_rw [map_smul]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro source hsource
    exact smul_comm _ _ _

theorem sourceAdjacentTargetLinearMap_inner
    {n k L : ℕ} (hn : 3 ≤ n) (hkl : k < L)
    (degreeFibre : (i : Jacobi.Index k L) → Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ]
        CertificateDegreeAmbient n k L i)
    (adjacent : SourceAdjacentChannelData n k L degreeFibre)
    (u v : HarmonicCertificateAssembly.DegreeBlockPi n k L) :
    ⟪sourceAdjacentTargetLinearMap hn degreeFibre adjacent u,
      sourceAdjacentTargetLinearMap hn degreeFibre adjacent v⟫_ℝ =
      ⟪u, v⟫_ℝ := by
  classical
  rw [PiLp.inner_apply]
  change
    (∑ target : Jacobi.Index k L,
      ⟪∑ source : Jacobi.Index k L,
          sourceAdjacentBlockCoefficient n k L hn target source •
            adjacent.channel target source (u source),
        ∑ source : Jacobi.Index k L,
          sourceAdjacentBlockCoefficient n k L hn target source •
            adjacent.channel target source (v source)⟫_ℝ) =
      ⟪u, v⟫_ℝ
  simp_rw [sum_inner, inner_sum]
  calc
    (∑ target : Jacobi.Index k L,
      ∑ source : Jacobi.Index k L,
        ∑ other : Jacobi.Index k L,
          ⟪sourceAdjacentBlockCoefficient
              n k L hn target source •
                adjacent.channel target source (u source),
            sourceAdjacentBlockCoefficient
              n k L hn target other •
                adjacent.channel target other (v other)⟫_ℝ) =
      ∑ target : Jacobi.Index k L,
        ∑ source : Jacobi.Index k L,
          sourceAdjacentBlockCoefficient
              n k L hn target source ^ 2 *
            ⟪u source, v source⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro target htarget
      apply Finset.sum_congr rfl
      intro source hsource
      rw [Finset.sum_eq_single source]
      · by_cases hzero :
          SourceJacobiWeights.sourceChannelCoefficient
            n k L source target = 0
        · rw [adjacent.channel_zero target source hzero]
          simp only [LinearMap.zero_apply, smul_zero, inner_self_eq_norm_sq_to_K, norm_zero,
            Real.ringHom_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
            zero_eq_mul, pow_eq_zero_iff]
          have hcoefficient :
              sourceAdjacentBlockCoefficient
                n k L hn target source = 0 := by
            simp only [sourceAdjacentBlockCoefficient, hzero, zero_mul, zero_div, Real.sqrt_zero]
          simp only [hcoefficient, true_or]
        · rw [real_inner_smul_left, real_inner_smul_right,
            adjacent.channel_inner target source hzero]
          ring
      · intro other hother hne
        rw [real_inner_smul_left, real_inner_smul_right,
          adjacent.channel_orthogonal target source other hne.symm]
        ring
      · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]
    _ = ∑ source : Jacobi.Index k L,
          (∑ target : Jacobi.Index k L,
            sourceAdjacentBlockCoefficient
              n k L hn target source ^ 2) *
              ⟪u source, v source⟫_ℝ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro source hsource
      rw [Finset.sum_mul]
    _ = ⟪u, v⟫_ℝ := by
      simp_rw [sourceAdjacentBlockCoefficient_sq_sum hn hkl,
        one_mul]
      rw [PiLp.inner_apply]

private def sourceAdjacentTargetIsometry
    {n k L : ℕ} (hn : 3 ≤ n) (hkl : k < L)
    (degreeFibre : (i : Jacobi.Index k L) → Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ]
        CertificateDegreeAmbient n k L i)
    (adjacent : SourceAdjacentChannelData n k L degreeFibre) :
    HarmonicCertificateAssembly.DegreeBlockPi n k L →ₗᵢ[ℝ]
      SourceTargetRowSpace n k L :=
  (sourceAdjacentTargetLinearMap hn degreeFibre adjacent).isometryOfInner
    (sourceAdjacentTargetLinearMap_inner hn hkl degreeFibre adjacent)

private def sourceTargetRowTransportLinearMap
    (n k L : ℕ) (hkl : k ≤ L) :
    SourceTargetRowSpace n k L →ₗ[ℝ]
      HarmonicRowChannelSpace n k L where
  toFun v := WithLp.toLp 2
    (fun a : Fin n =>
      harmonicDegreeBlockEquiv n k L hkl
        (WithLp.toLp 2
          (fun target : Jacobi.Index k L => v target a)))
  map_add' u v := by
    apply PiLp.ext
    intro a
    change
      harmonicDegreeBlockEquiv n k L hkl
          (WithLp.toLp 2
            (fun target : Jacobi.Index k L =>
              u target a + v target a)) =
        harmonicDegreeBlockEquiv n k L hkl
            (WithLp.toLp 2
              (fun target : Jacobi.Index k L => u target a)) +
          harmonicDegreeBlockEquiv n k L hkl
            (WithLp.toLp 2
              (fun target : Jacobi.Index k L => v target a))
    rw [← map_add]
    congr 1
  map_smul' c v := by
    apply PiLp.ext
    intro a
    change
      harmonicDegreeBlockEquiv n k L hkl
          (WithLp.toLp 2
            (fun target : Jacobi.Index k L =>
              c • v target a)) =
        c • harmonicDegreeBlockEquiv n k L hkl
          (WithLp.toLp 2
            (fun target : Jacobi.Index k L => v target a))
    rw [← map_smul]
    congr 1

theorem sourceTargetRowTransportLinearMap_inner
    (n k L : ℕ) (hkl : k ≤ L)
    (u v : SourceTargetRowSpace n k L) :
    ⟪sourceTargetRowTransportLinearMap n k L hkl u,
      sourceTargetRowTransportLinearMap n k L hkl v⟫_ℝ =
      ⟪u, v⟫_ℝ := by
  rw [PiLp.inner_apply]
  calc
    (∑ a : Fin n,
      ⟪harmonicDegreeBlockEquiv n k L hkl
          (WithLp.toLp 2
            (fun target : Jacobi.Index k L => u target a)),
        harmonicDegreeBlockEquiv n k L hkl
          (WithLp.toLp 2
            (fun target : Jacobi.Index k L => v target a))⟫_ℝ) =
      ∑ a : Fin n,
        ∑ target : Jacobi.Index k L,
          ⟪u target a, v target a⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [(harmonicDegreeBlockEquiv n k L hkl).inner_map_map,
        PiLp.inner_apply]
    _ = ∑ target : Jacobi.Index k L,
          ∑ a : Fin n, ⟪u target a, v target a⟫_ℝ := by
      rw [Finset.sum_comm]
    _ = ⟪u, v⟫_ℝ := by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro target htarget
      rw [PiLp.inner_apply]

private def sourceTargetRowTransport
    (n k L : ℕ) (hkl : k ≤ L) :
    SourceTargetRowSpace n k L →ₗᵢ[ℝ]
      HarmonicRowChannelSpace n k L :=
  (sourceTargetRowTransportLinearMap n k L hkl).isometryOfInner
    (sourceTargetRowTransportLinearMap_inner n k L hkl)

private def sourceAdjacentHarmonicRow
    {n k L : ℕ} (hn : 3 ≤ n) (hkl : k < L)
    (degreeFibre : (i : Jacobi.Index k L) → Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ]
        CertificateDegreeAmbient n k L i)
    (adjacent : SourceAdjacentChannelData n k L degreeFibre) :
    CertificateAmbient n k L →ₗᵢ[ℝ]
      HarmonicRowChannelSpace n k L :=
  (sourceTargetRowTransport n k L (Nat.le_of_lt hkl)).comp
    ((sourceAdjacentTargetIsometry hn hkl degreeFibre adjacent).comp
      (harmonicDegreeBlockEquiv n k L
        (Nat.le_of_lt hkl)).symm.toLinearIsometry)

private abbrev ProjectionChannelSpace (n k L : ℕ) :=
  PiLp 2 (fun _ : Fin (n + 1) => ProjectionMatrixSpace n k L)

/-- The harmonic axis tensor used in the spherical-code argument. -/
def harmonicAxisTensor
    (n k L : ℕ) (x : Euclidean n) :
    CertificateAmbient n k L →ₗ[ℝ]
      HarmonicRowChannelSpace n k L where
  toFun u := WithLp.toLp 2
    (fun a : Fin n => x a • u)
  map_add' u v := by
    apply PiLp.ext
    intro a
    simp only [smul_add, PiLp.add_apply]
  map_smul' c u := by
    apply PiLp.ext
    intro a
    change x a • (c • u) = c • (x a • u)
    exact smul_comm _ _ _

@[simp] theorem harmonicDegreeBlockEquiv_symm_degreeBlockInclusion
    (n k L : ℕ) (hkl : k ≤ L)
    (i : Jacobi.Index k L)
    (u : CertificateDegreeAmbient n k L i) :
    (harmonicDegreeBlockEquiv n k L hkl).symm
        (HarmonicCertificateAssembly.degreeBlockInclusion
          n k L hkl i u) =
      PiLp.single 2 i u := by
  change
    (harmonicDegreeBlockEquiv n k L hkl).symm
        (harmonicDegreeBlockEquiv n k L hkl
          (PiLp.single 2 i u)) = PiLp.single 2 i u
  exact (harmonicDegreeBlockEquiv n k L hkl).symm_apply_apply _

theorem harmonicDegreeBlockEquiv_symm_weightedFibre
    (n k L : ℕ) (hn : 3 ≤ n) (hkl : k ≤ L)
    (degreeFibre : (i : Jacobi.Index k L) → Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ]
        CertificateDegreeAmbient n k L i)
    (x : Euclidean n) (u : CertificateFibre n k)
    (i : Jacobi.Index k L) :
    ((harmonicDegreeBlockEquiv n k L hkl).symm
      (HarmonicCertificateAssembly.harmonicWeightedFibre
        n k L hn hkl degreeFibre x u)) i =
      HarmonicCertificateAssembly.harmonicFibreAmplitudes
        n k L hn i • degreeFibre i x u := by
  classical
  rw [HarmonicCertificateAssembly.harmonicWeightedFibre_apply,
    map_sum]
  simp only [map_smul,
    harmonicDegreeBlockEquiv_symm_degreeBlockInclusion]
  change
    ((∑ j : Jacobi.Index k L,
      HarmonicCertificateAssembly.harmonicFibreAmplitudes
          n k L hn j •
        PiLp.single 2 j (degreeFibre j x u)).ofLp) i = _
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp only [HarmonicCertificateAssembly.harmonicFibreAmplitudes_apply, PiLp.smul_apply,
      PiLp.single_eq_same]
  · intro j hj hji
    simp only [HarmonicCertificateAssembly.harmonicFibreAmplitudes_apply, PiLp.smul_apply, ne_eq,
      hji, not_false_eq_true, PiLp.single_eq_of_ne', smul_zero]
  · simp only [Finset.mem_univ, not_true_eq_false,
      HarmonicCertificateAssembly.harmonicFibreAmplitudes_apply, PiLp.smul_apply,
      PiLp.single_eq_same, smul_eq_zero, IsEmpty.forall_iff]

theorem sourceTargetRowTransport_inner_axisTensor
    (n k L : ℕ) (hkl : k ≤ L)
    (v : SourceTargetRowSpace n k L)
    (x : Euclidean n) (z : CertificateAmbient n k L) :
    ⟪sourceTargetRowTransport n k L hkl v,
      harmonicAxisTensor n k L x z⟫_ℝ =
      ∑ target : Jacobi.Index k L,
        ⟪v target,
          harmonicDegreeAxisTensor n k L target x
            ((harmonicDegreeBlockEquiv n k L hkl).symm z
              target)⟫_ℝ := by
  classical
  rw [PiLp.inner_apply]
  calc
    (∑ a : Fin n,
      ⟪harmonicDegreeBlockEquiv n k L hkl
          (WithLp.toLp 2
            (fun target : Jacobi.Index k L => v target a)),
        x a • z⟫_ℝ) =
      ∑ a : Fin n,
        ∑ target : Jacobi.Index k L,
          ⟪v target a,
            x a •
              ((harmonicDegreeBlockEquiv n k L hkl).symm z
                target)⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← (harmonicDegreeBlockEquiv n k L hkl).apply_symm_apply
        (x a • z),
        (harmonicDegreeBlockEquiv n k L hkl).inner_map_map,
        map_smul, PiLp.inner_apply]
      rfl
    _ = ∑ target : Jacobi.Index k L,
          ∑ a : Fin n,
            ⟪v target a,
              x a •
                ((harmonicDegreeBlockEquiv n k L hkl).symm z
                  target)⟫_ℝ := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro target htarget
      rw [PiLp.inner_apply]
      rfl

theorem sourceAdjacentChannel_inner_degreeAxisTensor
    {n k L : ℕ}
    (degreeFibre : (i : Jacobi.Index k L) → Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ]
        CertificateDegreeAmbient n k L i)
    (adjacent : SourceAdjacentChannelData n k L degreeFibre)
    (x : Euclidean n) (hx : x ∈ unitSphere n)
    (target source : Jacobi.Index k L)
    (z : CertificateDegreeAmbient n k L source)
    (u : CertificateFibre n k) (a : ℝ) :
    ⟪adjacent.channel target source z,
      harmonicDegreeAxisTensor n k L target x
        (a • degreeFibre target x u)⟫_ℝ =
      a *
        Real.sqrt
          (SourceJacobiWeights.sourceChannelCoefficient
            n k L source target) *
        ⟪z, degreeFibre source x u⟫_ℝ := by
  rw [map_smul, real_inner_smul_right,
    ← LinearMap.adjoint_inner_right
      (adjacent.channel target source) z
      (harmonicDegreeAxisTensor n k L target x
        (degreeFibre target x u)),
    adjacent.axis_projection x hx target source u,
    real_inner_smul_right]
  ring

theorem harmonicWeightedFibre_ambient_inner
    (n k L : ℕ) (hn : 3 ≤ n) (hkl : k ≤ L)
    (degreeFibre : (i : Jacobi.Index k L) → Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ]
        CertificateDegreeAmbient n k L i)
    (x : Euclidean n) (u : CertificateFibre n k)
    (z : CertificateAmbient n k L) :
    ⟪z, HarmonicCertificateAssembly.harmonicWeightedFibre
      n k L hn hkl degreeFibre x u⟫_ℝ =
      ∑ source : Jacobi.Index k L,
        HarmonicCertificateAssembly.harmonicFibreAmplitudes
          n k L hn source *
          ⟪(harmonicDegreeBlockEquiv n k L hkl).symm z source,
            degreeFibre source x u⟫_ℝ := by
  rw [← (harmonicDegreeBlockEquiv n k L hkl).symm.inner_map_map,
    PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro source hsource
  rw [harmonicDegreeBlockEquiv_symm_weightedFibre,
    real_inner_smul_right]

theorem sourceAdjacentHarmonicRow_inner_axis_fibre
    {n k L : ℕ} (hn : 3 ≤ n) (hkl : k < L)
    (degreeFibre : (i : Jacobi.Index k L) → Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ]
        CertificateDegreeAmbient n k L i)
    (adjacent : SourceAdjacentChannelData n k L degreeFibre)
    (x : Euclidean n) (hx : x ∈ unitSphere n)
    (u : CertificateFibre n k)
    (z : CertificateAmbient n k L) :
    ⟪sourceAdjacentHarmonicRow hn hkl degreeFibre adjacent z,
      harmonicAxisTensor n k L x
        (HarmonicCertificateAssembly.harmonicWeightedFibre
          n k L hn (Nat.le_of_lt hkl) degreeFibre x u)⟫_ℝ =
      Real.sqrt (Jacobi.topEigenvalue n k L) *
        ⟪z, HarmonicCertificateAssembly.harmonicWeightedFibre
          n k L hn (Nat.le_of_lt hkl) degreeFibre x u⟫_ℝ := by
  classical
  let hweak : k ≤ L := Nat.le_of_lt hkl
  let block : HarmonicCertificateAssembly.DegreeBlockPi n k L :=
    (harmonicDegreeBlockEquiv n k L hweak).symm z
  change
    ⟪sourceTargetRowTransport n k L hweak
        (sourceAdjacentTargetLinearMap
          hn degreeFibre adjacent block),
      harmonicAxisTensor n k L x
        (HarmonicCertificateAssembly.harmonicWeightedFibre
          n k L hn hweak degreeFibre x u)⟫_ℝ = _
  rw [sourceTargetRowTransport_inner_axisTensor]
  simp_rw [harmonicDegreeBlockEquiv_symm_weightedFibre]
  calc
    (∑ target : Jacobi.Index k L,
      ⟪sourceAdjacentTargetLinearMap
          hn degreeFibre adjacent block target,
        harmonicDegreeAxisTensor n k L target x
          (HarmonicCertificateAssembly.harmonicFibreAmplitudes
            n k L hn target • degreeFibre target x u)⟫_ℝ) =
      ∑ target : Jacobi.Index k L,
        ∑ source : Jacobi.Index k L,
          (sourceAdjacentBlockCoefficient n k L hn target source *
            HarmonicCertificateAssembly.harmonicFibreAmplitudes
              n k L hn target *
            Real.sqrt
              (SourceJacobiWeights.sourceChannelCoefficient
                n k L source target)) *
            ⟪block source, degreeFibre source x u⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro target htarget
      change
        ⟪∑ source : Jacobi.Index k L,
            sourceAdjacentBlockCoefficient n k L hn target source •
              adjacent.channel target source (block source),
          harmonicDegreeAxisTensor n k L target x
            (HarmonicCertificateAssembly.harmonicFibreAmplitudes
              n k L hn target • degreeFibre target x u)⟫_ℝ = _
      rw [sum_inner]
      apply Finset.sum_congr rfl
      intro source hsource
      rw [real_inner_smul_left,
        sourceAdjacentChannel_inner_degreeAxisTensor
          degreeFibre adjacent x hx target source
          (block source) u
          (HarmonicCertificateAssembly.harmonicFibreAmplitudes
            n k L hn target)]
      ring
    _ = ∑ source : Jacobi.Index k L,
          (∑ target : Jacobi.Index k L,
            sourceAdjacentBlockCoefficient
              n k L hn target source *
              HarmonicCertificateAssembly.harmonicFibreAmplitudes
                n k L hn target *
              Real.sqrt
                (SourceJacobiWeights.sourceChannelCoefficient
                  n k L source target)) *
            ⟪block source, degreeFibre source x u⟫_ℝ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro source hsource
      rw [Finset.sum_mul]
    _ = Real.sqrt (Jacobi.topEigenvalue n k L) *
          (∑ source : Jacobi.Index k L,
            HarmonicCertificateAssembly.harmonicFibreAmplitudes
              n k L hn source *
              ⟪block source, degreeFibre source x u⟫_ℝ) := by
      simp_rw [sourceAdjacentBlockCoefficient_amplitude_sum hn hkl]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro source hsource
      ring
    _ = _ := by
      rw [harmonicWeightedFibre_ambient_inner]

private def spectralMatrixEmbeddingLinearMap
    (n k L : ℕ)
    (row : CertificateAmbient n k L →ₗᵢ[ℝ]
      HarmonicRowChannelSpace n k L) :
    ProjectionMatrixSpace n k L →ₗ[ℝ]
      ProjectionChannelSpace n k L where
  toFun M := WithLp.toLp 2
    (Fin.cases (0 : ProjectionMatrixSpace n k L)
      (fun a : Fin n => WithLp.toLp 2
        (fun j : Fin (truncatedHarmonicDimension n k L) =>
          row (M j) a)))
  map_add' M N := by
    apply PiLp.ext
    intro a
    induction a using Fin.cases with
    | zero => simp only [PiLp.add_apply, map_add, Fin.cases_zero, add_zero]
    | succ a =>
      apply PiLp.ext
      intro j
      simp only [PiLp.add_apply, map_add, Fin.cases_succ]
  map_smul' c M := by
    apply PiLp.ext
    intro a
    induction a using Fin.cases with
    | zero => simp only [PiLp.smul_apply, map_smul, Fin.cases_zero, Real.ringHom_apply, smul_zero]
    | succ a =>
      apply PiLp.ext
      intro j
      simp only [PiLp.smul_apply, map_smul, Fin.cases_succ, Real.ringHom_apply]

@[simp] theorem spectralMatrixEmbeddingLinearMap_zero
    (n k L : ℕ)
    (row : CertificateAmbient n k L →ₗᵢ[ℝ]
      HarmonicRowChannelSpace n k L)
    (M : ProjectionMatrixSpace n k L) :
    spectralMatrixEmbeddingLinearMap n k L row M
      (0 : Fin (n + 1)) = 0 := rfl

theorem spectralMatrixEmbeddingLinearMap_inner
    (n k L : ℕ)
    (row : CertificateAmbient n k L →ₗᵢ[ℝ]
      HarmonicRowChannelSpace n k L)
    (M N : ProjectionMatrixSpace n k L) :
    ⟪spectralMatrixEmbeddingLinearMap n k L row M,
      spectralMatrixEmbeddingLinearMap n k L row N⟫_ℝ =
      ⟪M, N⟫_ℝ := by
  rw [PiLp.inner_apply, Fin.sum_univ_succ]
  simp only [spectralMatrixEmbeddingLinearMap_zero,
    inner_zero_left, zero_add]
  simp_rw [PiLp.inner_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  change
    (∑ a : Fin n, ⟪row (M j) a, row (N j) a⟫_ℝ) =
      ⟪M j, N j⟫_ℝ
  rw [← PiLp.inner_apply, row.inner_map_map]

private def spectralMatrixEmbedding
    (n k L : ℕ)
    (row : CertificateAmbient n k L →ₗᵢ[ℝ]
      HarmonicRowChannelSpace n k L) :
    ProjectionMatrixSpace n k L →ₗᵢ[ℝ]
      ProjectionChannelSpace n k L where
  toLinearMap := spectralMatrixEmbeddingLinearMap n k L row
  norm_map' := by
    intro M
    rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner,
      spectralMatrixEmbeddingLinearMap_inner n k L row]

private abbrev ProjectionChannelIndex (n k L : ℕ) :=
  Σ _ : Fin (n + 1), MatrixCoordinateIndex n k L

private def projectionChannelDimension (n k L : ℕ) : ℕ :=
  Fintype.card (ProjectionChannelIndex n k L)

private def fibreProjection {n k L : ℕ}
    (f : Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L)
    (x : Euclidean n) :
    CertificateAmbient n k L →ₗ[ℝ] CertificateAmbient n k L :=
  (f x).toLinearMap ∘ₗ (f x).adjoint

private def projectionMatrixFeature {n k L : ℕ}
    (f : Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L)
    (x : Euclidean n) : ProjectionMatrixSpace n k L :=
  WithLp.toLp 2 (fun i : Fin (truncatedHarmonicDimension n k L) =>
    fibreProjection f x (certificateAmbientBasis n k L i))

theorem projectionMatrixFeature_inner {n k L : ℕ}
    (f : Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L)
    (x y : Euclidean n) :
    ⟪projectionMatrixFeature f x,
      projectionMatrixFeature f y⟫_ℝ =
      isometricPackingKernel f x y := by
  rfl

private def projectionMatrixFlatten (n k L : ℕ) :
    ProjectionMatrixSpace n k L ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (MatrixCoordinateIndex n k L) :=
  (LinearIsometryEquiv.piLpCurry ℝ 2
    (fun (_ : Fin (truncatedHarmonicDimension n k L))
      (_ : Fin (truncatedHarmonicDimension n k L)) => ℝ)).symm

private def projectionChannelFlatten (n k L : ℕ) :
    ProjectionChannelSpace n k L ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (ProjectionChannelIndex n k L) :=
  (LinearIsometryEquiv.piLpCongrRight 2
    (fun _ : Fin (n + 1) => projectionMatrixFlatten n k L)).trans
    (LinearIsometryEquiv.piLpCurry ℝ 2
      (fun (_ : Fin (n + 1))
        (_ : MatrixCoordinateIndex n k L) => ℝ)).symm

private def projectionChannelEuclideanEquiv (n k L : ℕ) :
    ProjectionChannelSpace n k L ≃ₗᵢ[ℝ]
      Euclidean (projectionChannelDimension n k L) :=
  (projectionChannelFlatten n k L).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (Fintype.equivFin (ProjectionChannelIndex n k L)))

private def rawLiftChannel {n k L : ℕ}
    (f : Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L)
    (x : Euclidean n) : ProjectionChannelSpace n k L :=
  WithLp.toLp 2
    (Fin.cases (0 : ProjectionMatrixSpace n k L)
      (fun a : Fin n => x a • projectionMatrixFeature f x))

@[simp] theorem rawLiftChannel_zero {n k L : ℕ}
    (f : Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L)
    (x : Euclidean n) :
    rawLiftChannel f x (0 : Fin (n + 1)) = 0 := by
  rfl

@[simp] theorem rawLiftChannel_succ {n k L : ℕ}
    (f : Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L)
    (x : Euclidean n) (a : Fin n) :
    rawLiftChannel f x a.succ =
      x a • projectionMatrixFeature f x := by
  rfl

theorem rawLiftChannel_inner {n k L : ℕ}
    (f : Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L)
    (x y : Euclidean n) :
    ⟪rawLiftChannel f x, rawLiftChannel f y⟫_ℝ =
      ⟪x, y⟫_ℝ * isometricPackingKernel f x y := by
  rw [PiLp.inner_apply, Fin.sum_univ_succ]
  simp only [rawLiftChannel_zero, rawLiftChannel_succ,
    inner_zero_left, zero_add, real_inner_smul_left,
    real_inner_smul_right]
  calc
    (∑ a : Fin n,
      y a * (x a *
        ⟪projectionMatrixFeature f x,
          projectionMatrixFeature f y⟫_ℝ)) =
      (∑ a : Fin n, x a * y a) *
        ⟪projectionMatrixFeature f x,
          projectionMatrixFeature f y⟫_ℝ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a ha
        ring
    _ = ⟪x, y⟫_ℝ * isometricPackingKernel f x y := by
      rw [projectionMatrixFeature_inner]
      congr 1
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro a ha
      simp only [RCLike.inner_apply, Real.ringHom_apply, mul_comm]

private def firstFibreIndex (n k : ℕ) (hn : 3 ≤ n) :
    Fin (Gegenbauer.fibreDimension n k) :=
  ⟨0, Gegenbauer.fibreDimension_pos hn k⟩

private def firstFibreVector (n k : ℕ) (hn : 3 ≤ n) :
    CertificateFibre n k :=
  certificateFibreBasis n k (firstFibreIndex n k hn)

@[simp] theorem firstFibreVector_inner_basis
    (n k : ℕ) (hn : 3 ≤ n)
    (i : Fin (Gegenbauer.fibreDimension n k)) :
    ⟪firstFibreVector n k hn, certificateFibreBasis n k i⟫_ℝ =
      if i = firstFibreIndex n k hn then 1 else 0 := by
  classical
  simp only [firstFibreVector, certificateFibreBasis, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left, Real.ringHom_apply, PiLp.single_apply, eq_comm, mul_ite,
    mul_one, mul_zero]

private def rankOneChannelMap
    (n k L : ℕ) (hn : 3 ≤ n)
    (v : ProjectionChannelSpace n k L) :
    CertificateFibre n k →ₗ[ℝ] ProjectionChannelSpace n k L where
  toFun u := ⟪firstFibreVector n k hn, u⟫_ℝ • v
  map_add' := by
    intro u w
    rw [inner_add_right, add_smul]
  map_smul' := by
    intro c u
    rw [real_inner_smul_right, mul_smul]
    rfl

@[simp] theorem rankOneChannelMap_apply
    (n k L : ℕ) (hn : 3 ≤ n)
    (v : ProjectionChannelSpace n k L)
    (u : CertificateFibre n k) :
    rankOneChannelMap n k L hn v u =
      ⟪firstFibreVector n k hn, u⟫_ℝ • v := rfl

theorem rankOneChannelMap_kernel
    {α : Type*} (n k L : ℕ) (hn : 3 ≤ n)
    (v : α → ProjectionChannelSpace n k L) (x y : α) :
    finiteHilbertSchmidtKernel (certificateFibreBasis n k)
      (fun z => rankOneChannelMap n k L hn (v z)) x y =
      ⟪v x, v y⟫_ℝ := by
  classical
  unfold finiteHilbertSchmidtKernel
  rw [Finset.sum_eq_single (firstFibreIndex n k hn)]
  · simp only [rankOneChannelMap_apply, firstFibreVector_inner_basis, ↓reduceIte, one_smul]
  · intro i hi hne
    simp only [rankOneChannelMap_apply, firstFibreVector_inner_basis, hne, ↓reduceIte, zero_smul,
      inner_self_eq_norm_sq_to_K, norm_zero, Real.ringHom_apply, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
  · simp only [Finset.mem_univ, not_true_eq_false, rankOneChannelMap_apply,
      firstFibreVector_inner_basis, ↓reduceIte, one_smul, IsEmpty.forall_iff]

private def embeddedBulkChannel {n k L : ℕ}
    (embedding : ProjectionMatrixSpace n k L →ₗᵢ[ℝ]
      ProjectionChannelSpace n k L)
    (f : Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L)
    (x : Euclidean n) : ProjectionChannelSpace n k L :=
  embedding (projectionMatrixFeature f x)

theorem embeddedBulkChannel_inner {n k L : ℕ}
    (embedding : ProjectionMatrixSpace n k L →ₗᵢ[ℝ]
      ProjectionChannelSpace n k L)
    (f : Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L)
    (x y : Euclidean n) :
    ⟪embeddedBulkChannel embedding f x,
      embeddedBulkChannel embedding f y⟫_ℝ =
      isometricPackingKernel f x y := by
  unfold embeddedBulkChannel
  rw [embedding.inner_map_map, projectionMatrixFeature_inner]

/-- Data encoding the source spectral row construction. -/
structure SourceSpectralRowData
    (n k L : ℕ)
    (fibre : Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L) where
  /-- The row component. -/
  row : CertificateAmbient n k L →ₗᵢ[ℝ]
    HarmonicRowChannelSpace n k L
  /-- The spectral coefficient component. -/
  spectralCoefficient : ℝ
  spectralCoefficient_sq :
    spectralCoefficient ^ 2 = Jacobi.topEigenvalue n k L
  adjoint_axis_fibre :
    ∀ x ∈ unitSphere n, ∀ u : CertificateFibre n k,
      row.adjoint
        (harmonicAxisTensor n k L x (fibre x u)) =
          spectralCoefficient • fibre x u

/-- The source spectral row data of adjacent used in the spherical-code argument. -/
def sourceSpectralRowDataOfAdjacent
    {n k L : ℕ} (hn : 3 ≤ n) (hkl : k < L)
    (degreeFibre : (i : Jacobi.Index k L) → Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ]
        CertificateDegreeAmbient n k L i)
    (adjacent : SourceAdjacentChannelData n k L degreeFibre) :
    SourceSpectralRowData n k L
      (HarmonicCertificateAssembly.harmonicWeightedFibre
        n k L hn (Nat.le_of_lt hkl) degreeFibre) where
  row := sourceAdjacentHarmonicRow hn hkl degreeFibre adjacent
  spectralCoefficient := Real.sqrt (Jacobi.topEigenvalue n k L)
  spectralCoefficient_sq := Real.sq_sqrt
    (HarmonicPerronPositivity.topEigenvalue_pos_of_lt
      hn hkl).le
  adjoint_axis_fibre := by
    intro x hx u
    apply ext_inner_left ℝ
    intro z
    rw [LinearMap.adjoint_inner_right, real_inner_smul_right]
    exact sourceAdjacentHarmonicRow_inner_axis_fibre
      hn hkl degreeFibre adjacent x hx u z

theorem sourceSpectralBulk_lift_inner
    {n k L : ℕ}
    (fibre : Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L)
    (source : SourceSpectralRowData n k L fibre)
    (x y : Euclidean n) (hy : y ∈ unitSphere n) :
    ⟪embeddedBulkChannel
        (spectralMatrixEmbedding n k L source.row) fibre x,
      rawLiftChannel fibre y⟫_ℝ =
        source.spectralCoefficient *
          isometricPackingKernel fibre x y := by
  classical
  unfold embeddedBulkChannel
  rw [PiLp.inner_apply, Fin.sum_univ_succ]
  simp only [rawLiftChannel_zero, inner_zero_right, zero_add]
  calc
    (∑ a : Fin n,
      ⟪(spectralMatrixEmbedding n k L source.row
          (projectionMatrixFeature fibre x)) a.succ,
        rawLiftChannel fibre y a.succ⟫_ℝ) =
      ∑ a : Fin n,
        ∑ j : Fin (truncatedHarmonicDimension n k L),
          ⟪(spectralMatrixEmbedding n k L source.row
              (projectionMatrixFeature fibre x)) a.succ j,
            rawLiftChannel fibre y a.succ j⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [PiLp.inner_apply]
    _ = ∑ j : Fin (truncatedHarmonicDimension n k L),
      ∑ a : Fin n,
        ⟪(spectralMatrixEmbedding n k L source.row
            (projectionMatrixFeature fibre x)) a.succ j,
          rawLiftChannel fibre y a.succ j⟫_ℝ := by
      rw [Finset.sum_comm]
    _ =
      ∑ j : Fin (truncatedHarmonicDimension n k L),
        source.spectralCoefficient *
          ⟪projectionMatrixFeature fibre x j,
            projectionMatrixFeature fibre y j⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro j hj
      change
        (∑ a : Fin n,
          ⟪source.row (projectionMatrixFeature fibre x j) a,
            y a • projectionMatrixFeature fibre y j⟫_ℝ) =
          source.spectralCoefficient *
            ⟪projectionMatrixFeature fibre x j,
              projectionMatrixFeature fibre y j⟫_ℝ
      calc
        (∑ a : Fin n,
          ⟪source.row (projectionMatrixFeature fibre x j) a,
            y a • projectionMatrixFeature fibre y j⟫_ℝ) =
          ⟪source.row (projectionMatrixFeature fibre x j),
            harmonicAxisTensor n k L y
              (projectionMatrixFeature fibre y j)⟫_ℝ := by
              rw [PiLp.inner_apply]
              rfl
        _ =
          ⟪projectionMatrixFeature fibre x j,
            source.row.adjoint
              (harmonicAxisTensor n k L y
                (projectionMatrixFeature fibre y j))⟫_ℝ := by
              exact (LinearMap.adjoint_inner_right
                source.row.toLinearMap
                (projectionMatrixFeature fibre x j)
                (harmonicAxisTensor n k L y
                  (projectionMatrixFeature fibre y j))).symm
        _ =
          ⟪projectionMatrixFeature fibre x j,
            source.spectralCoefficient •
              projectionMatrixFeature fibre y j⟫_ℝ := by
              congr 1
              change
                source.row.adjoint
                  (harmonicAxisTensor n k L y
                    (fibre y
                      ((fibre y).adjoint
                        (certificateAmbientBasis n k L j)))) =
                  source.spectralCoefficient •
                    fibre y
                      ((fibre y).adjoint
                        (certificateAmbientBasis n k L j))
              exact source.adjoint_axis_fibre y hy
                ((fibre y).adjoint
                  (certificateAmbientBasis n k L j))
        _ = _ := by
          rw [real_inner_smul_right]
    _ = source.spectralCoefficient *
          isometricPackingKernel fibre x y := by
      rw [← Finset.mul_sum, ← PiLp.inner_apply,
        projectionMatrixFeature_inner]

private def euclideanChannelFeatureMap
    (n k L : ℕ) (hn : 3 ≤ n)
    (v : ProjectionChannelSpace n k L) :
    CertificateFibre n k →ₗ[ℝ]
      Euclidean (projectionChannelDimension n k L) :=
  (projectionChannelEuclideanEquiv n k L).toLinearMap ∘ₗ
    rankOneChannelMap n k L hn v

theorem euclideanChannelFeatureMap_inner
    (n k L : ℕ) (hn : 3 ≤ n)
    (v w : ProjectionChannelSpace n k L)
    (u z : CertificateFibre n k) :
    ⟪euclideanChannelFeatureMap n k L hn v u,
      euclideanChannelFeatureMap n k L hn w z⟫_ℝ =
      ⟪firstFibreVector n k hn, u⟫_ℝ *
        (⟪firstFibreVector n k hn, z⟫_ℝ *
          ⟪v, w⟫_ℝ) := by
  change
    ⟪projectionChannelEuclideanEquiv n k L
        (rankOneChannelMap n k L hn v u),
      projectionChannelEuclideanEquiv n k L
        (rankOneChannelMap n k L hn w z)⟫_ℝ = _
  rw [(projectionChannelEuclideanEquiv n k L).inner_map_map]
  change
    ⟪⟪firstFibreVector n k hn, u⟫_ℝ • v,
      ⟪firstFibreVector n k hn, z⟫_ℝ • w⟫_ℝ = _
  rw [real_inner_smul_left, real_inner_smul_right]

theorem euclideanChannelFeatureMap_kernel
    {α : Type*} (n k L : ℕ) (hn : 3 ≤ n)
    (v : α → ProjectionChannelSpace n k L) (x y : α) :
    finiteHilbertSchmidtKernel (certificateFibreBasis n k)
      (fun z => euclideanChannelFeatureMap n k L hn (v z)) x y =
      ⟪v x, v y⟫_ℝ := by
  calc
    finiteHilbertSchmidtKernel (certificateFibreBasis n k)
        (fun z => euclideanChannelFeatureMap n k L hn (v z)) x y =
      finiteHilbertSchmidtKernel (certificateFibreBasis n k)
        (fun z => rankOneChannelMap n k L hn (v z)) x y := by
      unfold finiteHilbertSchmidtKernel
      apply Finset.sum_congr rfl
      intro i hi
      change
        ⟪projectionChannelEuclideanEquiv n k L
            (rankOneChannelMap n k L hn (v x)
              (certificateFibreBasis n k i)),
          projectionChannelEuclideanEquiv n k L
            (rankOneChannelMap n k L hn (v y)
              (certificateFibreBasis n k i))⟫_ℝ = _
      exact (projectionChannelEuclideanEquiv n k L).inner_map_map _ _
    _ = ⟪v x, v y⟫_ℝ :=
      rankOneChannelMap_kernel n k L hn v x y

private def bulkCoordinateMap {n k L : ℕ}
    (hn : 3 ≤ n)
    (embedding : ProjectionMatrixSpace n k L →ₗᵢ[ℝ]
      ProjectionChannelSpace n k L)
    (f : Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L)
    (x : Euclidean n) :
    CertificateFibre n k →ₗ[ℝ]
      Euclidean (projectionChannelDimension n k L) :=
  euclideanChannelFeatureMap n k L hn
    (embeddedBulkChannel embedding f x)

private def liftCoordinateMap {n k L : ℕ}
    (hn : 3 ≤ n)
    (f : Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L)
    (x : Euclidean n) :
    CertificateFibre n k →ₗ[ℝ]
      Euclidean (projectionChannelDimension n k L) :=
  euclideanChannelFeatureMap n k L hn (rawLiftChannel f x)

theorem bulkCoordinateMap_kernel {n k L : ℕ}
    (hn : 3 ≤ n)
    (embedding : ProjectionMatrixSpace n k L →ₗᵢ[ℝ]
      ProjectionChannelSpace n k L)
    (f : Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L)
    (x y : Euclidean n) :
    finiteHilbertSchmidtKernel (certificateFibreBasis n k)
      (bulkCoordinateMap hn embedding f) x y =
      isometricPackingKernel f x y := by
  calc
    finiteHilbertSchmidtKernel (certificateFibreBasis n k)
        (bulkCoordinateMap hn embedding f) x y =
      ⟪embeddedBulkChannel embedding f x,
        embeddedBulkChannel embedding f y⟫_ℝ :=
      euclideanChannelFeatureMap_kernel n k L hn
        (embeddedBulkChannel embedding f) x y
    _ = isometricPackingKernel f x y :=
      embeddedBulkChannel_inner embedding f x y

theorem liftCoordinateMap_kernel {n k L : ℕ}
    (hn : 3 ≤ n)
    (f : Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L)
    (x y : Euclidean n) :
    finiteHilbertSchmidtKernel (certificateFibreBasis n k)
      (liftCoordinateMap hn f) x y =
      ⟪x, y⟫_ℝ * isometricPackingKernel f x y := by
  calc
    finiteHilbertSchmidtKernel (certificateFibreBasis n k)
        (liftCoordinateMap hn f) x y =
      ⟪rawLiftChannel f x, rawLiftChannel f y⟫_ℝ :=
      euclideanChannelFeatureMap_kernel n k L hn
        (rawLiftChannel f) x y
    _ = ⟪x, y⟫_ℝ * isometricPackingKernel f x y :=
      rawLiftChannel_inner f x y

theorem sourceSpectralBulk_lift_basis_inner
    {n k L : ℕ} (hn : 3 ≤ n)
    (fibre : Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L)
    (source : SourceSpectralRowData n k L fibre)
    (x y : Euclidean n) (hy : y ∈ unitSphere n)
    (i : Fin (Gegenbauer.fibreDimension n k)) :
    ⟪bulkCoordinateMap hn
        (spectralMatrixEmbedding n k L source.row) fibre x
        (certificateFibreBasis n k i),
      liftCoordinateMap hn fibre y
        (certificateFibreBasis n k i)⟫_ℝ =
      source.spectralCoefficient *
        ⟪bulkCoordinateMap hn
            (spectralMatrixEmbedding n k L source.row) fibre x
            (certificateFibreBasis n k i),
          bulkCoordinateMap hn
            (spectralMatrixEmbedding n k L source.row) fibre y
            (certificateFibreBasis n k i)⟫_ℝ := by
  change
    ⟪euclideanChannelFeatureMap n k L hn
        (embeddedBulkChannel
          (spectralMatrixEmbedding n k L source.row) fibre x)
        (certificateFibreBasis n k i),
      euclideanChannelFeatureMap n k L hn
        (rawLiftChannel fibre y)
        (certificateFibreBasis n k i)⟫_ℝ =
      source.spectralCoefficient *
        ⟪euclideanChannelFeatureMap n k L hn
            (embeddedBulkChannel
              (spectralMatrixEmbedding n k L source.row) fibre x)
            (certificateFibreBasis n k i),
          euclideanChannelFeatureMap n k L hn
            (embeddedBulkChannel
              (spectralMatrixEmbedding n k L source.row) fibre y)
            (certificateFibreBasis n k i)⟫_ℝ
  rw [euclideanChannelFeatureMap_inner,
    euclideanChannelFeatureMap_inner,
    sourceSpectralBulk_lift_inner fibre source x y hy,
    embeddedBulkChannel_inner]
  ring

/-- Data encoding the spectral channel remainder construction. -/
structure SpectralChannelRemainder
    (n k L : ℕ) (hn : 3 ≤ n)
    (fibre : Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L)
    (embedding : ProjectionMatrixSpace n k L →ₗᵢ[ℝ]
      ProjectionChannelSpace n k L) where
  /-- The spectral coefficient component. -/
  spectralCoefficient : ℝ
  spectralCoefficient_sq :
    spectralCoefficient ^ 2 = Jacobi.topEigenvalue n k L
  /-- The boundary component. -/
  boundary : Euclidean n → CertificateFibre n k →ₗ[ℝ]
    Euclidean (projectionChannelDimension n k L)
  /-- The remainder component. -/
  remainder : Euclidean n → CertificateFibre n k →ₗ[ℝ]
    Euclidean (projectionChannelDimension n k L)
  decomposition : ∀ x ∈ unitSphere n,
    liftCoordinateMap hn fibre x =
      spectralCoefficient • bulkCoordinateMap hn embedding fibre x +
      (1 : ℝ) • boundary x + remainder x
  bulk_boundary_orthogonal :
    ∀ x ∈ unitSphere n, ∀ y ∈ unitSphere n,
      ∀ i : Fin (Gegenbauer.fibreDimension n k),
        ⟪bulkCoordinateMap hn embedding fibre x
            (certificateFibreBasis n k i),
          boundary y (certificateFibreBasis n k i)⟫_ℝ = 0
  bulk_remainder_orthogonal :
    ∀ x ∈ unitSphere n, ∀ y ∈ unitSphere n,
      ∀ i : Fin (Gegenbauer.fibreDimension n k),
        ⟪bulkCoordinateMap hn embedding fibre x
            (certificateFibreBasis n k i),
          remainder y (certificateFibreBasis n k i)⟫_ℝ = 0
  boundary_remainder_orthogonal :
    ∀ x ∈ unitSphere n, ∀ y ∈ unitSphere n,
      ∀ i : Fin (Gegenbauer.fibreDimension n k),
        ⟪boundary x (certificateFibreBasis n k i),
          remainder y (certificateFibreBasis n k i)⟫_ℝ = 0

private def sourceSpectralResidual
    {n k L : ℕ} (hn : 3 ≤ n)
    (fibre : Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L)
    (source : SourceSpectralRowData n k L fibre)
    (x : Euclidean n) :
    CertificateFibre n k →ₗ[ℝ]
      Euclidean (projectionChannelDimension n k L) :=
  liftCoordinateMap hn fibre x -
    source.spectralCoefficient •
      bulkCoordinateMap hn
        (spectralMatrixEmbedding n k L source.row) fibre x

theorem sourceSpectralBulk_residual_orthogonal
    {n k L : ℕ} (hn : 3 ≤ n)
    (fibre : Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L)
    (source : SourceSpectralRowData n k L fibre)
    (x y : Euclidean n) (hy : y ∈ unitSphere n)
    (i : Fin (Gegenbauer.fibreDimension n k)) :
    ⟪bulkCoordinateMap hn
        (spectralMatrixEmbedding n k L source.row) fibre x
        (certificateFibreBasis n k i),
      sourceSpectralResidual hn fibre source y
        (certificateFibreBasis n k i)⟫_ℝ = 0 := by
  unfold sourceSpectralResidual
  simp only [LinearMap.sub_apply, LinearMap.smul_apply,
    inner_sub_right, real_inner_smul_right]
  rw [sourceSpectralBulk_lift_basis_inner
    hn fibre source x y hy i]
  ring

private def sourceSpectralChannelRemainder
    {n k L : ℕ} (hn : 3 ≤ n)
    (fibre : Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L)
    (source : SourceSpectralRowData n k L fibre) :
    SpectralChannelRemainder n k L hn fibre
      (spectralMatrixEmbedding n k L source.row) where
  spectralCoefficient := source.spectralCoefficient
  spectralCoefficient_sq := source.spectralCoefficient_sq
  boundary := fun _ => 0
  remainder := sourceSpectralResidual hn fibre source
  decomposition := by
    intro x hx
    unfold sourceSpectralResidual
    simp only [smul_zero, add_zero, sub_eq_add_neg, add_neg_cancel_comm_assoc]
  bulk_boundary_orthogonal := by
    intro x hx y hy i
    simp only [LinearMap.zero_apply, inner_zero_right]
  bulk_remainder_orthogonal := by
    intro x hx y hy i
    exact sourceSpectralBulk_residual_orthogonal
      hn fibre source x y hy i
  boundary_remainder_orthogonal := by
    intro x hx y hy i
    simp only [LinearMap.zero_apply, inner_zero_left]

private def toHarmonicCoordinateData
    (n k L : ℕ) (hn : 3 ≤ n)
    (fibre : Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L)
    (embedding : ProjectionMatrixSpace n k L →ₗᵢ[ℝ]
      ProjectionChannelSpace n k L)
    (spectral : SpectralChannelRemainder n k L hn fibre embedding) :
    HarmonicCertificateAssembly.HarmonicCoordinateData n k L fibre where
  coordinateDimension := projectionChannelDimension n k L
  lift := liftCoordinateMap hn fibre
  bulk := bulkCoordinateMap hn embedding fibre
  boundary := spectral.boundary
  remainder := spectral.remainder
  spectralCoefficient := spectral.spectralCoefficient
  spectralCoefficient_sq := spectral.spectralCoefficient_sq
  decomposition := spectral.decomposition
  lift_kernel := fun x _hx y _hy =>
    liftCoordinateMap_kernel hn fibre x y
  bulk_kernel := fun x _hx y _hy =>
    bulkCoordinateMap_kernel hn embedding fibre x y
  bulk_boundary_orthogonal := spectral.bulk_boundary_orthogonal
  bulk_remainder_orthogonal := spectral.bulk_remainder_orthogonal
  boundary_remainder_orthogonal :=
    spectral.boundary_remainder_orthogonal

private def assembleFiniteGramCertificateOfSpectralRemainder
    (n k L : ℕ) (hn : 3 ≤ n) (hkl : k ≤ L)
    (degreeFibre : (i : Jacobi.Index k L) → Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ]
        CertificateDegreeAmbient n k L i)
    (embedding : ProjectionMatrixSpace n k L →ₗᵢ[ℝ]
      ProjectionChannelSpace n k L)
    (spectral : SpectralChannelRemainder n k L hn
      (HarmonicCertificateAssembly.harmonicWeightedFibre
        n k L hn hkl degreeFibre) embedding) :
    FiniteGramCertificate n k L :=
  HarmonicCertificateAssembly.assembleFiniteGramCertificate
    n k L hn hkl degreeFibre
      (toHarmonicCoordinateData n k L hn
        (HarmonicCertificateAssembly.harmonicWeightedFibre
          n k L hn hkl degreeFibre)
        embedding spectral)

private def assembleFiniteGramCertificateOfSourceRow
    (n k L : ℕ) (hn : 3 ≤ n) (hkl : k ≤ L)
    (degreeFibre : (i : Jacobi.Index k L) → Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ]
        CertificateDegreeAmbient n k L i)
    (source : SourceSpectralRowData n k L
      (HarmonicCertificateAssembly.harmonicWeightedFibre
        n k L hn hkl degreeFibre)) :
    FiniteGramCertificate n k L :=
  assembleFiniteGramCertificateOfSpectralRemainder
    n k L hn hkl degreeFibre
      (spectralMatrixEmbedding n k L source.row)
      (sourceSpectralChannelRemainder hn
        (HarmonicCertificateAssembly.harmonicWeightedFibre
          n k L hn hkl degreeFibre) source)

theorem sphericalCode_bound_of_sourceSpectralRow
    {n k L : ℕ} (hn : 3 ≤ n) (hkl : k ≤ L)
    (degreeFibre : (i : Jacobi.Index k L) → Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ]
        CertificateDegreeAmbient n k L i)
    (source : SourceSpectralRowData n k L
      (HarmonicCertificateAssembly.harmonicWeightedFibre
        n k L hn hkl degreeFibre))
    {s : ℝ} (hs : s ≤ 1)
    (hgap : s < Jacobi.topEigenvalue n k L)
    (C : SphericalCode n s) :
    (C.points.card : ℝ) ≤
      ((1 - s) / (Jacobi.topEigenvalue n k L - s)) *
        ((truncatedHarmonicDimension n k L : ℝ) /
          (Gegenbauer.fibreDimension n k : ℝ)) :=
  finiteGramCertificate_sphericalCode_bound hn hkl
    (assembleFiniteGramCertificateOfSourceRow
      n k L hn hkl degreeFibre source)
    hs hgap C

end HarmonicCoordinateChannels

namespace HarmonicCoordinateOperators

private abbrev HarmonicSpace (n m : ℕ) :=
  SpherePacking.harmonicHomogeneousSubmodule n m

private abbrev CoordinateHarmonicSpace (n m : ℕ) :=
  PiLp 2 (fun _ : Fin n => HarmonicSpace n m)

private def coordinateAxis (n : ℕ) (j : Fin n) : SpherePacking.Euclidean n :=
  EuclideanSpace.single j (1 : ℝ)

@[simp] theorem axisPolynomial_coordinateAxis
    (n : ℕ) (j : Fin n) :
    SpherePacking.axisPolynomial n (coordinateAxis n j) =
      (MvPolynomial.X j : MvPolynomial (Fin n) ℝ) := by
  classical
  simp only [axisPolynomial, coordinateAxis, EuclideanSpace.single, PiLp.single_apply,
    MonoidWithZeroHom.map_ite_one_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]

theorem directionalDerivative_coordinateAxis
    (n : ℕ) (j : Fin n) (p : MvPolynomial (Fin n) ℝ) :
    SpherePacking.directionalDerivative n (coordinateAxis n j) p =
      MvPolynomial.pderiv j p := by
  classical
  simp only [coordinateAxis, EuclideanSpace.single, directionalDerivative_apply, PiLp.single_apply,
    ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

private def harmonicCoordinateDerivative
    (n m : ℕ) (j : Fin n) :
    HarmonicSpace n (m + 1) →ₗ[ℝ] HarmonicSpace n m :=
  SpherePacking.harmonicDirectionalDerivative n m (coordinateAxis n j)

@[simp] theorem harmonicCoordinateDerivative_apply
    (n m : ℕ) (j : Fin n)
    (p : HarmonicSpace n (m + 1)) :
    ((harmonicCoordinateDerivative n m j p : HarmonicSpace n m) :
      MvPolynomial (Fin n) ℝ) =
        MvPolynomial.pderiv j
          (p : MvPolynomial (Fin n) ℝ) := by
  change
    SpherePacking.directionalDerivative n (coordinateAxis n j)
      (p : MvPolynomial (Fin n) ℝ) = _
  exact directionalDerivative_coordinateAxis n j p

private def harmonicGradient (n m : ℕ) :
    HarmonicSpace n (m + 1) →ₗ[ℝ]
      CoordinateHarmonicSpace n m where
  toFun p :=
    WithLp.toLp 2 fun j : Fin n =>
      harmonicCoordinateDerivative n m j p
  map_add' p q := by
    apply PiLp.ext
    intro j
    exact (harmonicCoordinateDerivative n m j).map_add p q
  map_smul' c p := by
    apply PiLp.ext
    intro j
    exact (harmonicCoordinateDerivative n m j).map_smul c p

theorem harmonicGradient_inner
    (n m : ℕ)
    (p q : HarmonicSpace n (m + 1)) :
    ⟪harmonicGradient n m p,
      harmonicGradient n m q⟫_ℝ =
      ((m + 1 : ℕ) : ℝ) * ⟪p, q⟫_ℝ := by
  classical
  have hcoord (j : Fin n) :
      ⟪harmonicCoordinateDerivative n m j p,
        harmonicCoordinateDerivative n m j q⟫_ℝ =
        SpherePacking.Fischer.polynomialInner n
          (MvPolynomial.pderiv j
            (p : MvPolynomial (Fin n) ℝ))
          (MvPolynomial.pderiv j
            (q : MvPolynomial (Fin n) ℝ)) := by
    rw [SpherePacking.Fischer.harmonic_inner_eq,
      SpherePacking.Fischer.harmonicInner_eq_polynomialInner,
      harmonicCoordinateDerivative_apply,
      harmonicCoordinateDerivative_apply]
  have hpq :
      ⟪p, q⟫_ℝ =
        SpherePacking.Fischer.polynomialInner n
          (p : MvPolynomial (Fin n) ℝ)
          (q : MvPolynomial (Fin n) ℝ) := by
    rw [SpherePacking.Fischer.harmonic_inner_eq,
      SpherePacking.Fischer.harmonicInner_eq_polynomialInner]
  rw [PiLp.inner_apply]
  change
    (∑ j : Fin n,
      ⟪harmonicCoordinateDerivative n m j p,
        harmonicCoordinateDerivative n m j q⟫_ℝ) =
      ((m + 1 : ℕ) : ℝ) * ⟪p, q⟫_ℝ
  calc
    (∑ j : Fin n,
      ⟪harmonicCoordinateDerivative n m j p,
        harmonicCoordinateDerivative n m j q⟫_ℝ) =
      ∑ j : Fin n,
        SpherePacking.Fischer.polynomialInner n
          (MvPolynomial.pderiv j
            (p : MvPolynomial (Fin n) ℝ))
          (MvPolynomial.pderiv j
            (q : MvPolynomial (Fin n) ℝ)) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hcoord j
    _ =
      ∑ j : Fin n,
        SpherePacking.Fischer.polynomialInner n
          (p : MvPolynomial (Fin n) ℝ)
          (MvPolynomial.X j *
            MvPolynomial.pderiv j
              (q : MvPolynomial (Fin n) ℝ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        calc
          SpherePacking.Fischer.polynomialInner n
              (MvPolynomial.pderiv j
                (p : MvPolynomial (Fin n) ℝ))
              (MvPolynomial.pderiv j
                (q : MvPolynomial (Fin n) ℝ)) =
            SpherePacking.Fischer.polynomialInner n
              (MvPolynomial.pderiv j
                (q : MvPolynomial (Fin n) ℝ))
              (MvPolynomial.pderiv j
                (p : MvPolynomial (Fin n) ℝ)) :=
              SpherePacking.Fischer.polynomialInner_comm n _ _
          _ = SpherePacking.Fischer.polynomialInner n
              (MvPolynomial.X j *
                MvPolynomial.pderiv j
                  (q : MvPolynomial (Fin n) ℝ))
              (p : MvPolynomial (Fin n) ℝ) :=
              (SpherePacking.Fischer.polynomialInner_X_mul n j
                (MvPolynomial.pderiv j
                  (q : MvPolynomial (Fin n) ℝ))
                (p : MvPolynomial (Fin n) ℝ)).symm
          _ = SpherePacking.Fischer.polynomialInner n
              (p : MvPolynomial (Fin n) ℝ)
              (MvPolynomial.X j *
                MvPolynomial.pderiv j
                  (q : MvPolynomial (Fin n) ℝ)) :=
              SpherePacking.Fischer.polynomialInner_comm n _ _
    _ = SpherePacking.Fischer.polynomialInner n
        (p : MvPolynomial (Fin n) ℝ)
        (∑ j : Fin n,
          MvPolynomial.X j *
            MvPolynomial.pderiv j
              (q : MvPolynomial (Fin n) ℝ)) := by
          simpa only using
            (SpherePacking.Fischer.polynomialInner_sum_right n (p : MvPolynomial (Fin n) ℝ)
              Finset.univ
                (fun j : Fin n => MvPolynomial.X j * MvPolynomial.pderiv j (q : MvPolynomial
                  (Fin n) ℝ))).symm
    _ = SpherePacking.Fischer.polynomialInner n
        (p : MvPolynomial (Fin n) ℝ)
        (((m + 1 : ℕ) : ℝ) •
          (q : MvPolynomial (Fin n) ℝ)) := by
          rw [SpherePacking.harmonicPolynomial_euler q,
            Nat.cast_smul_eq_nsmul]
    _ = ((m + 1 : ℕ) : ℝ) *
        SpherePacking.Fischer.polynomialInner n
          (p : MvPolynomial (Fin n) ℝ)
          (q : MvPolynomial (Fin n) ℝ) :=
      SpherePacking.Fischer.polynomialInner_smul_right n
        ((m + 1 : ℕ) : ℝ)
        (p : MvPolynomial (Fin n) ℝ)
        (q : MvPolynomial (Fin n) ℝ)
    _ = ((m + 1 : ℕ) : ℝ) * ⟪p, q⟫_ℝ := by
      rw [hpq]

private def harmonicCoordinateRaising (n m : ℕ) (j : Fin n) :
    HarmonicSpace n m →ₗ[ℝ] HarmonicSpace n (m + 1) :=
  (harmonicCoordinateDerivative n m j).adjoint

private def harmonicCoGradient (n m : ℕ) :
    HarmonicSpace n m →ₗ[ℝ]
      CoordinateHarmonicSpace n (m + 1) where
  toFun p :=
    WithLp.toLp 2 fun j : Fin n =>
      harmonicCoordinateRaising n m j p
  map_add' p q := by
    apply PiLp.ext
    intro j
    exact (harmonicCoordinateRaising n m j).map_add p q
  map_smul' c p := by
    apply PiLp.ext
    intro j
    exact (harmonicCoordinateRaising n m j).map_smul c p

theorem harmonicCoordinateRaising_eq_axisLift
    {n : ℕ} (hn : 0 < n) (k : ℕ) (j : Fin n) :
    harmonicCoordinateRaising n (k + 1) j =
      SpherePacking.harmonicAxisLift hn k (coordinateAxis n j) := by
  symm
  apply (LinearMap.eq_adjoint_iff
    (SpherePacking.harmonicAxisLift hn k (coordinateAxis n j))
    (harmonicCoordinateDerivative n (k + 1) j)).2
  intro p q
  calc
    ⟪SpherePacking.harmonicAxisLift hn k (coordinateAxis n j) p,
      q⟫_ℝ =
      SpherePacking.Fischer.harmonicInner n (k + 2)
        (SpherePacking.harmonicAxisLift hn k
          (coordinateAxis n j) p) q :=
      SpherePacking.Fischer.harmonic_inner_eq n (k + 2) _ _
    _ = SpherePacking.Fischer.harmonicInner n (k + 1) p
        (SpherePacking.harmonicDirectionalDerivative n
          (k + 1) (coordinateAxis n j) q) :=
      SpherePacking.harmonicAxisLift_fischer_adjoint
        hn k (coordinateAxis n j) p q
    _ = ⟪p, harmonicCoordinateDerivative n (k + 1) j q⟫_ℝ := by
      symm
      exact SpherePacking.Fischer.harmonic_inner_eq
        n (k + 1) p (harmonicCoordinateDerivative n (k + 1) j q)

theorem harmonicGradient_coGradient_orthogonal
    (n m : ℕ)
    (p : HarmonicSpace n (m + 2))
    (q : HarmonicSpace n m) :
    ⟪harmonicGradient n (m + 1) p,
      harmonicCoGradient n m q⟫_ℝ = 0 := by
  classical
  have hplap :
      SpherePacking.polynomialLaplacian n
        (p : MvPolynomial (Fin n) ℝ) = 0 := by
    have hp := (SpherePacking.mem_harmonicHomogeneousSubmodule
      (p : MvPolynomial (Fin n) ℝ)).mp p.property
    simpa only [SpherePacking.polynomialLaplacian_apply] using hp.2
  rw [PiLp.inner_apply]
  change
    (∑ j : Fin n,
      ⟪harmonicCoordinateDerivative n (m + 1) j p,
        (harmonicCoordinateDerivative n m j).adjoint q⟫_ℝ) = 0
  calc
    (∑ j : Fin n,
      ⟪harmonicCoordinateDerivative n (m + 1) j p,
        (harmonicCoordinateDerivative n m j).adjoint q⟫_ℝ) =
      ∑ j : Fin n,
        SpherePacking.Fischer.polynomialInner n
          (MvPolynomial.pderiv j
            (MvPolynomial.pderiv j
              (p : MvPolynomial (Fin n) ℝ)))
          (q : MvPolynomial (Fin n) ℝ) := by
          apply Finset.sum_congr rfl
          intro j hj
          calc
            ⟪harmonicCoordinateDerivative n (m + 1) j p,
              (harmonicCoordinateDerivative n m j).adjoint q⟫_ℝ =
                ⟪harmonicCoordinateDerivative n m j
                    (harmonicCoordinateDerivative n (m + 1) j p),
                  q⟫_ℝ :=
              LinearMap.adjoint_inner_right
                (harmonicCoordinateDerivative n m j)
                (harmonicCoordinateDerivative n (m + 1) j p) q
            _ = SpherePacking.Fischer.polynomialInner n
                  (MvPolynomial.pderiv j
                    (MvPolynomial.pderiv j
                      (p : MvPolynomial (Fin n) ℝ)))
                  (q : MvPolynomial (Fin n) ℝ) := by
                rw [SpherePacking.Fischer.harmonic_inner_eq,
                  SpherePacking.Fischer.harmonicInner_eq_polynomialInner,
                  harmonicCoordinateDerivative_apply,
                  harmonicCoordinateDerivative_apply]
    _ = SpherePacking.Fischer.polynomialInner n
        (∑ j : Fin n,
          MvPolynomial.pderiv j
            (MvPolynomial.pderiv j
              (p : MvPolynomial (Fin n) ℝ)))
        (q : MvPolynomial (Fin n) ℝ) := by
          simpa only using
            (SpherePacking.Fischer.polynomialInner_sum_left n Finset.univ
                (fun j : Fin n => MvPolynomial.pderiv j (MvPolynomial.pderiv j (p : MvPolynomial
                  (Fin n) ℝ)))
                (q : MvPolynomial (Fin n) ℝ)).symm
    _ = 0 := by
      rw [← SpherePacking.polynomialLaplacian_apply, hplap]
      rw [SpherePacking.Fischer.polynomialInner_comm]
      exact SpherePacking.fischer_polynomialInner_zero_right n
        (q : MvPolynomial (Fin n) ℝ)

private def upperChannelDenominator (n m : ℕ) : ℝ :=
  2 * (m : ℝ) + (n : ℝ)

private def upperChannelWeight (n m : ℕ) : ℝ :=
  ((m + 1 : ℕ) : ℝ) / upperChannelDenominator n m

theorem upperChannelDenominator_pos
    {n : ℕ} (hn : 0 < n) (m : ℕ) :
    0 < upperChannelDenominator n m := by
  unfold upperChannelDenominator
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  positivity

theorem upperChannelWeight_pos
    {n : ℕ} (hn : 0 < n) (m : ℕ) :
    0 < upperChannelWeight n m := by
  unfold upperChannelWeight
  apply div_pos
  · exact_mod_cast Nat.zero_lt_succ m
  · exact upperChannelDenominator_pos hn m

private def upperChannelAdjoint (n m : ℕ) :
    HarmonicSpace n (m + 1) →ₗ[ℝ]
      CoordinateHarmonicSpace n m :=
  (Real.sqrt (upperChannelDenominator n m))⁻¹ •
    harmonicGradient n m

private def upperChannel (n m : ℕ) :
    CoordinateHarmonicSpace n m →ₗ[ℝ]
      HarmonicSpace n (m + 1) :=
  (upperChannelAdjoint n m).adjoint

@[simp] theorem upperChannel_adjoint (n m : ℕ) :
    (upperChannel n m).adjoint = upperChannelAdjoint n m := by
  simp only [upperChannel, LinearMap.adjoint_adjoint]

theorem upperChannelAdjoint_inner
    {n : ℕ} (hn : 0 < n) (m : ℕ)
    (p q : HarmonicSpace n (m + 1)) :
    ⟪upperChannelAdjoint n m p,
      upperChannelAdjoint n m q⟫_ℝ =
      upperChannelWeight n m * ⟪p, q⟫_ℝ := by
  have hden := upperChannelDenominator_pos hn m
  have hroot : Real.sqrt (upperChannelDenominator n m) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hden)
  change
    ⟪(Real.sqrt (upperChannelDenominator n m))⁻¹ •
        harmonicGradient n m p,
      (Real.sqrt (upperChannelDenominator n m))⁻¹ •
        harmonicGradient n m q⟫_ℝ = _
  rw [real_inner_smul_left, real_inner_smul_right,
    harmonicGradient_inner]
  unfold upperChannelWeight
  calc
    (Real.sqrt (upperChannelDenominator n m))⁻¹ *
        ((Real.sqrt (upperChannelDenominator n m))⁻¹ *
          (((m + 1 : ℕ) : ℝ) * ⟪p, q⟫_ℝ)) =
      (((m + 1 : ℕ) : ℝ) /
        (Real.sqrt (upperChannelDenominator n m)) ^ 2) *
          ⟪p, q⟫_ℝ := by
          field_simp
    _ = (((m + 1 : ℕ) : ℝ) /
        upperChannelDenominator n m) * ⟪p, q⟫_ℝ := by
          rw [Real.sq_sqrt hden.le]

theorem adjoint_comp_self_of_inner
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (A : E →ₗ[ℝ] F) (c : ℝ)
    (h : ∀ p q : E, ⟪A p, A q⟫_ℝ = c * ⟪p, q⟫_ℝ) :
    A.adjoint.comp A = c • LinearMap.id := by
  apply LinearMap.ext
  intro p
  apply ext_inner_left ℝ
  intro q
  change ⟪q, A.adjoint (A p)⟫_ℝ = ⟪q, c • p⟫_ℝ
  rw [LinearMap.adjoint_inner_right, h, real_inner_smul_right]

/-- The normalized channel isometry used in the spherical-code argument. -/
def normalizedChannelIsometry
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A : E →ₗ[ℝ] F) (c : ℝ) (hc : 0 < c)
    (h : ∀ p q : E, ⟪A p, A q⟫_ℝ = c * ⟪p, q⟫_ℝ) :
    E →ₗᵢ[ℝ] F := by
  have hroot : Real.sqrt c ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hc)
  refine ((Real.sqrt c)⁻¹ • A).isometryOfInner ?_
  intro p q
  change
    ⟪(Real.sqrt c)⁻¹ • A p,
      (Real.sqrt c)⁻¹ • A q⟫_ℝ = ⟪p, q⟫_ℝ
  rw [real_inner_smul_left, real_inner_smul_right, h]
  calc
    (Real.sqrt c)⁻¹ *
        ((Real.sqrt c)⁻¹ * (c * ⟪p, q⟫_ℝ)) =
      (c / (Real.sqrt c) ^ 2) * ⟪p, q⟫_ℝ := by
        field_simp
    _ = ⟪p, q⟫_ℝ := by
      rw [Real.sq_sqrt hc.le]
      simp only [ne_eq, ne_of_gt hc, not_false_eq_true, div_self, one_mul]

private def upperChannelIsometry
    {n : ℕ} (hn : 0 < n) (m : ℕ) :
    HarmonicSpace n (m + 1) →ₗᵢ[ℝ]
      CoordinateHarmonicSpace n m :=
  normalizedChannelIsometry
    (upperChannelAdjoint n m)
    (upperChannelWeight n m)
    (upperChannelWeight_pos hn m)
    (upperChannelAdjoint_inner hn m)

private def lowerChannelWeight (n m : ℕ) : ℝ :=
  ((m : ℝ) + (n : ℝ) - 2) /
    (2 * (m : ℝ) + (n : ℝ) - 2)

theorem lowerChannelWeight_pos
    {n : ℕ} (hn : 3 ≤ n) (m : ℕ) :
    0 < lowerChannelWeight n m := by
  unfold lowerChannelWeight
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hmreal : 0 ≤ (m : ℝ) := by positivity
  apply div_pos <;> linarith

private def lowerChannelAdjoint (n m : ℕ) :
    HarmonicSpace n m →ₗ[ℝ]
      CoordinateHarmonicSpace n (m + 1) :=
  (Real.sqrt (upperChannelDenominator n m))⁻¹ •
    harmonicCoGradient n m

private def lowerChannel (n m : ℕ) :
    CoordinateHarmonicSpace n (m + 1) →ₗ[ℝ]
      HarmonicSpace n m :=
  (lowerChannelAdjoint n m).adjoint

@[simp] theorem lowerChannel_adjoint (n m : ℕ) :
    (lowerChannel n m).adjoint = lowerChannelAdjoint n m := by
  simp only [lowerChannel, LinearMap.adjoint_adjoint]

theorem upperChannelAdjoint_lowerChannelAdjoint_orthogonal
    (n m : ℕ)
    (p : HarmonicSpace n (m + 2))
    (q : HarmonicSpace n m) :
    ⟪upperChannelAdjoint n (m + 1) p,
      lowerChannelAdjoint n m q⟫_ℝ = 0 := by
  change
    ⟪(Real.sqrt (upperChannelDenominator n (m + 1)))⁻¹ •
        harmonicGradient n (m + 1) p,
      (Real.sqrt (upperChannelDenominator n m))⁻¹ •
        harmonicCoGradient n m q⟫_ℝ = 0
  rw [real_inner_smul_left, real_inner_smul_right,
    harmonicGradient_coGradient_orthogonal]
  ring

theorem coordinatePolynomialMultiplication_derivative_sum
    (n : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    (∑ j : Fin n,
      MvPolynomial.pderiv j (MvPolynomial.X j * p)) =
      (n : ℝ) • p +
        ∑ j : Fin n,
          MvPolynomial.X j * MvPolynomial.pderiv j p := by
  classical
  simp_rw [MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_X_self, one_mul]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_smul_eq_nsmul]

theorem radialGradient_derivative_sum
    (n : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    (∑ j : Fin n,
      MvPolynomial.pderiv j
        (SpherePacking.radialPolynomial n *
          MvPolynomial.pderiv j p)) =
      (2 : MvPolynomial (Fin n) ℝ) *
          (∑ j : Fin n,
            MvPolynomial.X j * MvPolynomial.pderiv j p) +
        SpherePacking.radialPolynomial n *
          SpherePacking.polynomialLaplacian n p := by
  classical
  simp_rw [MvPolynomial.pderiv_mul,
    SpherePacking.pderiv_radialPolynomial]
  rw [Finset.sum_add_distrib,
    SpherePacking.polynomialLaplacian_apply,
    Finset.mul_sum, Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro j hj
    ring
  · rfl

theorem harmonicCoordinateMultiplication_derivative_sum
    (n m : ℕ) (p : HarmonicSpace n m) :
    (∑ j : Fin n,
      MvPolynomial.pderiv j
        (MvPolynomial.X j *
          (p : MvPolynomial (Fin n) ℝ))) =
      (((n + m : ℕ) : ℝ) •
        (p : MvPolynomial (Fin n) ℝ)) := by
  rw [coordinatePolynomialMultiplication_derivative_sum,
    SpherePacking.harmonicPolynomial_euler,
    Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul,
    add_nsmul]

private def harmonicCoordinateRaisingZero
    (n : ℕ) (j : Fin n) :
    HarmonicSpace n 0 →ₗ[ℝ] HarmonicSpace n 1 := by
  refine (LinearMap.mulLeft ℝ
    (SpherePacking.axisPolynomial n (coordinateAxis n j))).restrict ?_
  intro p hp
  have hp' := (SpherePacking.mem_harmonicHomogeneousSubmodule p).mp hp
  have hplap : SpherePacking.polynomialLaplacian n p = 0 := by
    simpa only [SpherePacking.polynomialLaplacian_apply] using hp'.2
  have hderiv :
      SpherePacking.directionalDerivative n
        (coordinateAxis n j) p = 0 :=
    SpherePacking.directionalDerivative_eq_zero_of_isHomogeneous_zero
      (coordinateAxis n j) p hp'.1
  apply (SpherePacking.mem_harmonicHomogeneousSubmodule
    (SpherePacking.axisPolynomial n (coordinateAxis n j) * p)).mpr
  constructor
  · simpa only [axisPolynomial_coordinateAxis, add_zero] using
      (SpherePacking.axisPolynomial_isHomogeneous (coordinateAxis n j)).mul hp'.1
  · rw [← SpherePacking.polynomialLaplacian_apply,
      SpherePacking.polynomialLaplacian_axis_mul_for_tangent,
      hderiv, hplap]
    simp only [mul_zero, axisPolynomial_coordinateAxis, add_zero]

theorem harmonicCoordinateRaising_zero_eq
    (n : ℕ) (j : Fin n) :
    harmonicCoordinateRaising n 0 j =
      harmonicCoordinateRaisingZero n j := by
  symm
  apply (LinearMap.eq_adjoint_iff
    (harmonicCoordinateRaisingZero n j)
    (harmonicCoordinateDerivative n 0 j)).2
  intro p q
  calc
    ⟪harmonicCoordinateRaisingZero n j p, q⟫_ℝ =
      SpherePacking.Fischer.polynomialInner n
        (SpherePacking.axisPolynomial n (coordinateAxis n j) *
          (p : MvPolynomial (Fin n) ℝ))
        (q : MvPolynomial (Fin n) ℝ) := by
          rw [SpherePacking.Fischer.harmonic_inner_eq,
            SpherePacking.Fischer.harmonicInner_eq_polynomialInner]
          rfl
    _ = SpherePacking.Fischer.polynomialInner n
        (p : MvPolynomial (Fin n) ℝ)
        (SpherePacking.directionalDerivative n
          (coordinateAxis n j)
          (q : MvPolynomial (Fin n) ℝ)) :=
      SpherePacking.Fischer.polynomialInner_axis_directional n
        (coordinateAxis n j)
        (p : MvPolynomial (Fin n) ℝ)
        (q : MvPolynomial (Fin n) ℝ)
    _ = ⟪p, harmonicCoordinateDerivative n 0 j q⟫_ℝ := by
      symm
      rw [SpherePacking.Fischer.harmonic_inner_eq,
        SpherePacking.Fischer.harmonicInner_eq_polynomialInner]
      rfl

theorem harmonicCoordinateRaising_apply_polynomial
    {n : ℕ} (hn : 0 < n) (m : ℕ) (j : Fin n)
    (p : HarmonicSpace n m) :
    ((harmonicCoordinateRaising n m j p : HarmonicSpace n (m + 1)) :
        MvPolynomial (Fin n) ℝ) =
      MvPolynomial.X j * (p : MvPolynomial (Fin n) ℝ) -
        (upperChannelDenominator n (m - 1))⁻¹ •
          (SpherePacking.radialPolynomial n *
            MvPolynomial.pderiv j
              (p : MvPolynomial (Fin n) ℝ)) := by
  cases m with
  | zero =>
      have hp :=
        (SpherePacking.mem_harmonicHomogeneousSubmodule
          (p : MvPolynomial (Fin n) ℝ)).mp p.property
      have hd :
          MvPolynomial.pderiv j
            (p : MvPolynomial (Fin n) ℝ) = 0 := by
        have haxis :=
          SpherePacking.directionalDerivative_eq_zero_of_isHomogeneous_zero
            (coordinateAxis n j)
            (p : MvPolynomial (Fin n) ℝ) hp.1
        simpa only [directionalDerivative_coordinateAxis] using haxis
      rw [harmonicCoordinateRaising_zero_eq, hd]
      simp only [Nat.reduceAdd, harmonicCoordinateRaisingZero, axisPolynomial_coordinateAxis,
        LinearMap.coe_restrict_apply, LinearMap.mulLeft_apply, zero_tsub, mul_zero, smul_zero,
        sub_zero]
  | succ k =>
      rw [harmonicCoordinateRaising_eq_axisLift hn k j,
        SpherePacking.harmonicAxisLift_apply,
        SpherePacking.harmonicAxisProjectionOperator_apply,
        axisPolynomial_coordinateAxis,
        directionalDerivative_coordinateAxis]
      simp only [harmonicAxisProjectionDenominator, upperChannelDenominator, add_tsub_cancel_right]

private def lowerFischerGradientWeight (n m : ℕ) : ℝ :=
  ((n + m : ℕ) : ℝ) -
    (upperChannelDenominator n (m - 1))⁻¹ * (2 * (m : ℝ))

theorem lowerFischerGradientWeight_eq
    {n : ℕ} (hn : 3 ≤ n) (m : ℕ) :
    lowerFischerGradientWeight n m =
      upperChannelDenominator n m * lowerChannelWeight n m := by
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  cases m with
  | zero =>
      have hnne : (n : ℝ) ≠ 0 := by positivity
      have hnsub : (n : ℝ) - 2 ≠ 0 := by linarith
      unfold lowerFischerGradientWeight upperChannelDenominator
        lowerChannelWeight
      norm_num
      field_simp
  | succ k =>
      have hkreal : 0 ≤ (k : ℝ) := by positivity
      have hden : 2 * (k : ℝ) + n ≠ 0 := by
        have : 0 < 2 * (k : ℝ) + n := by linarith
        exact ne_of_gt this
      have hden' : (n : ℝ) + (k : ℝ) * 2 ≠ 0 := by
        have : 0 < (n : ℝ) + (k : ℝ) * 2 := by nlinarith
        exact ne_of_gt this
      unfold lowerFischerGradientWeight upperChannelDenominator
        lowerChannelWeight
      push_cast
      ring_nf
      field_simp [hden, hden']
      ring

theorem harmonicCoordinateRaising_derivative_sum
    {n : ℕ} (hn : 3 ≤ n) (m : ℕ)
    (p : HarmonicSpace n m) :
    (∑ j : Fin n,
      MvPolynomial.pderiv j
        ((harmonicCoordinateRaising n m j p :
          HarmonicSpace n (m + 1)) : MvPolynomial (Fin n) ℝ)) =
      lowerFischerGradientWeight n m •
        (p : MvPolynomial (Fin n) ℝ) := by
  classical
  have hnpos : 0 < n := by omega
  have hp := (SpherePacking.mem_harmonicHomogeneousSubmodule
    (p : MvPolynomial (Fin n) ℝ)).mp p.property
  have hplap :
      SpherePacking.polynomialLaplacian n
        (p : MvPolynomial (Fin n) ℝ) = 0 := by
    simpa only [SpherePacking.polynomialLaplacian_apply] using hp.2
  have htwo : (2 : MvPolynomial (Fin n) ℝ) =
      MvPolynomial.C (2 : ℝ) := by
    exact (map_ofNat
      (MvPolynomial.C : ℝ →+* MvPolynomial (Fin n) ℝ) 2).symm
  calc
    (∑ j : Fin n,
      MvPolynomial.pderiv j
        ((harmonicCoordinateRaising n m j p :
          HarmonicSpace n (m + 1)) : MvPolynomial (Fin n) ℝ)) =
      ∑ j : Fin n,
        MvPolynomial.pderiv j
          (MvPolynomial.X j * (p : MvPolynomial (Fin n) ℝ) -
            (upperChannelDenominator n (m - 1))⁻¹ •
              (SpherePacking.radialPolynomial n *
                MvPolynomial.pderiv j
                  (p : MvPolynomial (Fin n) ℝ))) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [harmonicCoordinateRaising_apply_polynomial hnpos m j p]
    _ =
      (∑ j : Fin n,
        MvPolynomial.pderiv j
          (MvPolynomial.X j * (p : MvPolynomial (Fin n) ℝ))) -
        (upperChannelDenominator n (m - 1))⁻¹ •
          (∑ j : Fin n,
            MvPolynomial.pderiv j
              (SpherePacking.radialPolynomial n *
                MvPolynomial.pderiv j
                  (p : MvPolynomial (Fin n) ℝ))) := by
            rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j hj
            rw [(MvPolynomial.pderiv j).map_sub,
              (MvPolynomial.pderiv j).map_smul]
    _ =
      (((n + m : ℕ) : ℝ) •
        (p : MvPolynomial (Fin n) ℝ)) -
        (upperChannelDenominator n (m - 1))⁻¹ •
          ((2 : MvPolynomial (Fin n) ℝ) *
            ((m : ℝ) • (p : MvPolynomial (Fin n) ℝ))) := by
            rw [harmonicCoordinateMultiplication_derivative_sum,
              radialGradient_derivative_sum,
              SpherePacking.harmonicPolynomial_euler, hplap]
            simp only [mul_zero, add_zero]
            rw [Nat.cast_smul_eq_nsmul ℝ m
              (p : MvPolynomial (Fin n) ℝ)]
    _ = lowerFischerGradientWeight n m •
        (p : MvPolynomial (Fin n) ℝ) := by
          rw [htwo, MvPolynomial.C_mul',
            smul_smul, smul_smul, ← sub_smul]
          unfold lowerFischerGradientWeight
          congr 1
          ring

theorem harmonicCoGradient_inner
    {n : ℕ} (hn : 3 ≤ n) (m : ℕ)
    (p q : HarmonicSpace n m) :
    ⟪harmonicCoGradient n m p,
      harmonicCoGradient n m q⟫_ℝ =
      (upperChannelDenominator n m * lowerChannelWeight n m) *
        ⟪p, q⟫_ℝ := by
  classical
  rw [PiLp.inner_apply]
  change
    (∑ j : Fin n,
      ⟪harmonicCoordinateRaising n m j p,
        harmonicCoordinateRaising n m j q⟫_ℝ) =
      (upperChannelDenominator n m * lowerChannelWeight n m) *
        ⟪p, q⟫_ℝ
  calc
    (∑ j : Fin n,
      ⟪harmonicCoordinateRaising n m j p,
        harmonicCoordinateRaising n m j q⟫_ℝ) =
      ∑ j : Fin n,
        SpherePacking.Fischer.polynomialInner n
          (p : MvPolynomial (Fin n) ℝ)
          (MvPolynomial.pderiv j
            ((harmonicCoordinateRaising n m j q :
              HarmonicSpace n (m + 1)) :
                MvPolynomial (Fin n) ℝ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        calc
          ⟪harmonicCoordinateRaising n m j p,
            harmonicCoordinateRaising n m j q⟫_ℝ =
            ⟪p,
              harmonicCoordinateDerivative n m j
                (harmonicCoordinateRaising n m j q)⟫_ℝ :=
              LinearMap.adjoint_inner_left
                (harmonicCoordinateDerivative n m j)
                (harmonicCoordinateRaising n m j q) p
          _ = SpherePacking.Fischer.polynomialInner n
              (p : MvPolynomial (Fin n) ℝ)
              (MvPolynomial.pderiv j
                ((harmonicCoordinateRaising n m j q :
                  HarmonicSpace n (m + 1)) :
                    MvPolynomial (Fin n) ℝ)) := by
                rw [SpherePacking.Fischer.harmonic_inner_eq,
                  SpherePacking.Fischer.harmonicInner_eq_polynomialInner,
                  harmonicCoordinateDerivative_apply]
    _ = SpherePacking.Fischer.polynomialInner n
        (p : MvPolynomial (Fin n) ℝ)
        (∑ j : Fin n,
          MvPolynomial.pderiv j
            ((harmonicCoordinateRaising n m j q :
              HarmonicSpace n (m + 1)) :
                MvPolynomial (Fin n) ℝ)) := by
          simpa only using
            (SpherePacking.Fischer.polynomialInner_sum_right n (p : MvPolynomial (Fin n) ℝ)
              Finset.univ
                (fun j : Fin n =>
                  MvPolynomial.pderiv j
                    ((harmonicCoordinateRaising n m j q : HarmonicSpace n (m + 1)) :
                      MvPolynomial (Fin n) ℝ))).symm
    _ = lowerFischerGradientWeight n m *
        SpherePacking.Fischer.polynomialInner n
          (p : MvPolynomial (Fin n) ℝ)
          (q : MvPolynomial (Fin n) ℝ) := by
          rw [harmonicCoordinateRaising_derivative_sum hn m q,
            SpherePacking.Fischer.polynomialInner_smul_right]
    _ = (upperChannelDenominator n m * lowerChannelWeight n m) *
        ⟪p, q⟫_ℝ := by
          rw [lowerFischerGradientWeight_eq hn m,
            SpherePacking.Fischer.harmonic_inner_eq,
            SpherePacking.Fischer.harmonicInner_eq_polynomialInner]

theorem lowerChannelAdjoint_inner
    {n : ℕ} (hn : 3 ≤ n) (m : ℕ)
    (p q : HarmonicSpace n m) :
    ⟪lowerChannelAdjoint n m p,
      lowerChannelAdjoint n m q⟫_ℝ =
      lowerChannelWeight n m * ⟪p, q⟫_ℝ := by
  have hden := upperChannelDenominator_pos
    (show 0 < n by omega) m
  have hroot : Real.sqrt (upperChannelDenominator n m) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hden)
  change
    ⟪(Real.sqrt (upperChannelDenominator n m))⁻¹ •
        harmonicCoGradient n m p,
      (Real.sqrt (upperChannelDenominator n m))⁻¹ •
        harmonicCoGradient n m q⟫_ℝ = _
  rw [real_inner_smul_left, real_inner_smul_right,
    harmonicCoGradient_inner hn m]
  calc
    (Real.sqrt (upperChannelDenominator n m))⁻¹ *
      ((Real.sqrt (upperChannelDenominator n m))⁻¹ *
        ((upperChannelDenominator n m * lowerChannelWeight n m) *
          ⟪p, q⟫_ℝ)) =
      ((upperChannelDenominator n m * lowerChannelWeight n m) /
        (Real.sqrt (upperChannelDenominator n m)) ^ 2) *
          ⟪p, q⟫_ℝ := by
            field_simp
    _ = lowerChannelWeight n m * ⟪p, q⟫_ℝ := by
          rw [Real.sq_sqrt hden.le]
          field_simp

private def lowerChannelIsometry
    {n : ℕ} (hn : 3 ≤ n) (m : ℕ) :
    HarmonicSpace n m →ₗᵢ[ℝ]
      CoordinateHarmonicSpace n (m + 1) :=
  normalizedChannelIsometry
    (lowerChannelAdjoint n m)
    (lowerChannelWeight n m)
    (lowerChannelWeight_pos hn m)
    (lowerChannelAdjoint_inner hn m)

theorem upperChannelIsometry_lowerChannelIsometry_orthogonal
    {n : ℕ} (hn : 3 ≤ n) (m : ℕ)
    (p : HarmonicSpace n (m + 2))
    (q : HarmonicSpace n m) :
    ⟪upperChannelIsometry (show 0 < n by omega) (m + 1) p,
      lowerChannelIsometry hn m q⟫_ℝ = 0 := by
  change
    ⟪(Real.sqrt (upperChannelWeight n (m + 1)))⁻¹ •
        upperChannelAdjoint n (m + 1) p,
      (Real.sqrt (lowerChannelWeight n m))⁻¹ •
        lowerChannelAdjoint n m q⟫_ℝ = 0
  rw [real_inner_smul_left, real_inner_smul_right,
    upperChannelAdjoint_lowerChannelAdjoint_orthogonal]
  ring

end HarmonicCoordinateOperators

namespace HarmonicSourceProjection

open SpherePacking.HarmonicCoordinateOperators

/-- The harmonic axis tensor used in the spherical-code argument. -/
def harmonicAxisTensor (n m : ℕ) (x : SpherePacking.Euclidean n) :
    HarmonicSpace n m →ₗ[ℝ] CoordinateHarmonicSpace n m where
  toFun p := WithLp.toLp 2 fun j : Fin n => x j • p
  map_add' p q := by
    apply PiLp.ext
    intro j
    exact smul_add (x j) p q
  map_smul' c p := by
    apply PiLp.ext
    intro j
    exact smul_comm (x j) c p

private def solidHarmonicSource
    {n : ℕ} (hn : 3 ≤ n) (k r : ℕ)
    (x : SpherePacking.Euclidean n) (hx : ‖x‖ = 1) :
    SpherePacking.tangentHarmonicSubmodule n k x →ₗ[ℝ]
      CoordinateHarmonicSpace n (k + r) :=
  (harmonicAxisTensor n (k + r) x).comp
    (SpherePacking.solidHarmonicAxisPolynomialIsometry
      hn k r x hx).toLinearMap

theorem upperChannel_harmonicAxisTensor_inner
    (n m : ℕ) (x : SpherePacking.Euclidean n)
    (p : HarmonicSpace n m)
    (q : HarmonicSpace n (m + 1)) :
    ⟪upperChannel n m (harmonicAxisTensor n m x p), q⟫_ℝ =
      (Real.sqrt (upperChannelDenominator n m))⁻¹ *
        SpherePacking.Fischer.polynomialInner n
          (SpherePacking.axisPolynomial n x *
            (p : MvPolynomial (Fin n) ℝ))
          (q : MvPolynomial (Fin n) ℝ) := by
  classical
  have hsingle (j : Fin n) :
      ⟪x j • p,
        (Real.sqrt (upperChannelDenominator n m))⁻¹ •
          harmonicCoordinateDerivative n m j q⟫_ℝ =
        (Real.sqrt (upperChannelDenominator n m))⁻¹ *
          SpherePacking.Fischer.polynomialInner n
            (p : MvPolynomial (Fin n) ℝ)
            (x j • MvPolynomial.pderiv j
              (q : MvPolynomial (Fin n) ℝ)) := by
    rw [SpherePacking.Fischer.harmonic_inner_eq,
      SpherePacking.Fischer.harmonicInner_eq_polynomialInner]
    change
      SpherePacking.Fischer.polynomialInner n
          (x j • (p : MvPolynomial (Fin n) ℝ))
          ((Real.sqrt (upperChannelDenominator n m))⁻¹ •
            ((harmonicCoordinateDerivative n m j q :
              HarmonicSpace n m) : MvPolynomial (Fin n) ℝ)) =
        (Real.sqrt (upperChannelDenominator n m))⁻¹ *
          SpherePacking.Fischer.polynomialInner n
            (p : MvPolynomial (Fin n) ℝ)
            (x j • MvPolynomial.pderiv j
              (q : MvPolynomial (Fin n) ℝ))
    rw [harmonicCoordinateDerivative_apply,
      SpherePacking.Fischer.polynomialInner_smul_left,
      SpherePacking.Fischer.polynomialInner_smul_right,
      SpherePacking.Fischer.polynomialInner_smul_right]
    ring
  calc
    ⟪upperChannel n m (harmonicAxisTensor n m x p), q⟫_ℝ =
      ⟪harmonicAxisTensor n m x p,
        upperChannelAdjoint n m q⟫_ℝ := by
        rw [← upperChannel_adjoint]
        exact
          (LinearMap.adjoint_inner_right (upperChannel n m)
            (harmonicAxisTensor n m x p) q).symm
    _ =
      ∑ j : Fin n,
        ⟪x j • p,
          (Real.sqrt (upperChannelDenominator n m))⁻¹ •
            harmonicCoordinateDerivative n m j q⟫_ℝ := by
        rw [PiLp.inner_apply]
        rfl
    _ =
      ∑ j : Fin n,
        (Real.sqrt (upperChannelDenominator n m))⁻¹ *
          SpherePacking.Fischer.polynomialInner n
            (p : MvPolynomial (Fin n) ℝ)
            (x j • MvPolynomial.pderiv j
              (q : MvPolynomial (Fin n) ℝ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hsingle j
    _ =
      (Real.sqrt (upperChannelDenominator n m))⁻¹ *
        SpherePacking.Fischer.polynomialInner n
          (p : MvPolynomial (Fin n) ℝ)
          (SpherePacking.directionalDerivative n x
            (q : MvPolynomial (Fin n) ℝ)) := by
        rw [SpherePacking.directionalDerivative_apply,
          SpherePacking.Fischer.polynomialInner_sum_right,
          Finset.mul_sum]
    _ = _ := by
        rw [SpherePacking.Fischer.polynomialInner_axis_directional]

theorem solidHarmonicAxisLift_axis_pairing
    {n k : ℕ} (x : SpherePacking.Euclidean n)
    (p : SpherePacking.tangentHarmonicSubmodule n k x)
    (r : ℕ)
    (q : SpherePacking.harmonicHomogeneousSubmodule
      n ((k + r) + 1)) :
    (2 * (r : ℝ) + SpherePacking.harmonicAxisParameter n k - 2) *
      SpherePacking.Fischer.polynomialInner n
        (SpherePacking.axisPolynomial n x *
          SpherePacking.solidHarmonicAxisLift n k x r
            (p : MvPolynomial (Fin n) ℝ))
        (q : MvPolynomial (Fin n) ℝ) =
      SpherePacking.Fischer.polynomialInner n
        (SpherePacking.solidHarmonicAxisLift n k x (r + 1)
          (p : MvPolynomial (Fin n) ℝ))
        (q : MvPolynomial (Fin n) ℝ) := by
  have hrad :=
    SpherePacking.fischer_polynomialInner_radial_harmonic
      (SpherePacking.solidHarmonicAxisLift n k x (r - 1)
        (p : MvPolynomial (Fin n) ℝ)) q
  rw [SpherePacking.solidHarmonicAxisLift_succ_apply,
    SpherePacking.fischer_polynomialInner_sub_left,
    mul_assoc,
    SpherePacking.fischer_polynomialInner_constant_mul_left,
    mul_assoc,
    SpherePacking.fischer_polynomialInner_constant_mul_left,
    hrad, mul_zero, sub_zero]

private def solidHarmonicSourceUpperCoefficient (n k r : ℕ) : ℝ :=
  Real.sqrt (SpherePacking.solidHarmonicAxisFischerScale
      n k (r + 1)) /
    ((2 * (r : ℝ) + SpherePacking.harmonicAxisParameter n k - 2) *
      Real.sqrt (SpherePacking.solidHarmonicAxisFischerScale n k r) *
      Real.sqrt (upperChannelDenominator n (k + r)))

theorem upperChannel_solidHarmonicSource
    {n : ℕ} (hn : 3 ≤ n) (k r : ℕ)
    (x : SpherePacking.Euclidean n) (hx : ‖x‖ = 1)
    (p : SpherePacking.tangentHarmonicSubmodule n k x) :
    upperChannel n (k + r)
        (solidHarmonicSource hn k r x hx p) =
      solidHarmonicSourceUpperCoefficient n k r •
        SpherePacking.solidHarmonicAxisPolynomialIsometry
          hn k (r + 1) x hx p := by
  have hnreal : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hkreal : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hrreal : (0 : ℝ) ≤ (r : ℝ) := by positivity
  have hraise :
      0 < 2 * (r : ℝ) +
        SpherePacking.harmonicAxisParameter n k - 2 := by
    unfold SpherePacking.harmonicAxisParameter
    linarith
  have hscale :=
    SpherePacking.solidHarmonicAxisFischerScale_pos hn k r
  have hscale_next :=
    SpherePacking.solidHarmonicAxisFischerScale_pos hn k (r + 1)
  have hden := upperChannelDenominator_pos (by omega : 0 < n) (k + r)
  have hsqrt :
      Real.sqrt
        (SpherePacking.solidHarmonicAxisFischerScale n k r) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hscale)
  have hsqrt_next :
      Real.sqrt
        (SpherePacking.solidHarmonicAxisFischerScale
          n k (r + 1)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hscale_next)
  have hsqrt_den :
      Real.sqrt (upperChannelDenominator n (k + r)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hden)
  apply ext_inner_right ℝ
  intro q
  change
    ⟪upperChannel n (k + r)
        (harmonicAxisTensor n (k + r) x
          (SpherePacking.solidHarmonicAxisPolynomialIsometry
            hn k r x hx p)), q⟫_ℝ =
      ⟪solidHarmonicSourceUpperCoefficient n k r •
          SpherePacking.solidHarmonicAxisPolynomialIsometry
            hn k (r + 1) x hx p, q⟫_ℝ
  rw [upperChannel_harmonicAxisTensor_inner,
    SpherePacking.Fischer.harmonic_inner_eq,
    SpherePacking.Fischer.harmonicInner_eq_polynomialInner]
  change
    (Real.sqrt (upperChannelDenominator n (k + r)))⁻¹ *
      SpherePacking.Fischer.polynomialInner n
        (SpherePacking.axisPolynomial n x *
          ((Real.sqrt
              (SpherePacking.solidHarmonicAxisFischerScale n k r))⁻¹ •
            SpherePacking.solidHarmonicAxisLift n k x r
              (p : MvPolynomial (Fin n) ℝ)))
        (q : MvPolynomial (Fin n) ℝ) =
      SpherePacking.Fischer.polynomialInner n
        (solidHarmonicSourceUpperCoefficient n k r •
          ((Real.sqrt
              (SpherePacking.solidHarmonicAxisFischerScale
                n k (r + 1)))⁻¹ •
            SpherePacking.solidHarmonicAxisLift n k x (r + 1)
              (p : MvPolynomial (Fin n) ℝ)))
        (q : MvPolynomial (Fin n) ℝ)
  rw [mul_smul_comm,
    SpherePacking.Fischer.polynomialInner_smul_left,
    SpherePacking.Fischer.polynomialInner_smul_left,
    SpherePacking.Fischer.polynomialInner_smul_left]
  unfold solidHarmonicSourceUpperCoefficient
  field_simp [hsqrt, hsqrt_next, hsqrt_den, ne_of_gt hraise]
  simpa only [mul_comm] using
    solidHarmonicAxisLift_axis_pairing x p r q

theorem solidHarmonicSourceUpperCoefficient_pos
    {n : ℕ} (hn : 3 ≤ n) (k r : ℕ) :
    0 < solidHarmonicSourceUpperCoefficient n k r := by
  have hnreal : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hkreal : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hrreal : (0 : ℝ) ≤ (r : ℝ) := by positivity
  have hraise :
      0 < 2 * (r : ℝ) +
        SpherePacking.harmonicAxisParameter n k - 2 := by
    unfold SpherePacking.harmonicAxisParameter
    linarith
  unfold solidHarmonicSourceUpperCoefficient
  apply div_pos
  · exact Real.sqrt_pos.mpr
      (SpherePacking.solidHarmonicAxisFischerScale_pos
        hn k (r + 1))
  · exact mul_pos
      (mul_pos hraise (Real.sqrt_pos.mpr
        (SpherePacking.solidHarmonicAxisFischerScale_pos hn k r)))
      (Real.sqrt_pos.mpr
        (upperChannelDenominator_pos (by omega : 0 < n) (k + r)))

private def solidHarmonicSourceUpperIsometryCoefficient
    (n k r : ℕ) : ℝ :=
  solidHarmonicSourceUpperCoefficient n k r /
    Real.sqrt (upperChannelWeight n (k + r))

theorem solidHarmonicSourceUpperCoefficient_sq
    {n : ℕ} (hn : 3 ≤ n) (k r : ℕ) :
    solidHarmonicSourceUpperCoefficient n k r ^ 2 =
      (((r : ℝ) + 1) *
        ((r : ℝ) + SpherePacking.harmonicAxisParameter n k - 2)) /
        ((2 * (r : ℝ) +
          SpherePacking.harmonicAxisParameter n k - 2) *
          upperChannelDenominator n (k + r)) := by
  have hnreal : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hkreal : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hrreal : (0 : ℝ) ≤ (r : ℝ) := by positivity
  have hraise :
      0 < 2 * (r : ℝ) +
        SpherePacking.harmonicAxisParameter n k - 2 := by
    unfold SpherePacking.harmonicAxisParameter
    linarith
  have hscale :=
    SpherePacking.solidHarmonicAxisFischerScale_pos hn k r
  have hscale_next :=
    SpherePacking.solidHarmonicAxisFischerScale_pos hn k (r + 1)
  have hden :=
    upperChannelDenominator_pos (by omega : 0 < n) (k + r)
  unfold solidHarmonicSourceUpperCoefficient
  rw [div_pow, mul_pow, mul_pow,
    Real.sq_sqrt hscale_next.le,
    Real.sq_sqrt hscale.le,
    Real.sq_sqrt hden.le,
    SpherePacking.solidHarmonicAxisFischerScale_succ]
  field_simp [ne_of_gt hraise, ne_of_gt hscale,
    ne_of_gt hden]

theorem solidHarmonicSourceUpperIsometryCoefficient_sq
    {n : ℕ} (hn : 3 ≤ n) (k r : ℕ) :
    solidHarmonicSourceUpperIsometryCoefficient n k r ^ 2 =
      SpherePacking.Gegenbauer.alphaSq n k (k + r) := by
  have hnreal : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hkreal : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hrreal : (0 : ℝ) ≤ (r : ℝ) := by positivity
  have hraise :
      0 < 2 * (r : ℝ) +
        SpherePacking.harmonicAxisParameter n k - 2 := by
    unfold SpherePacking.harmonicAxisParameter
    linarith
  have hden :=
    upperChannelDenominator_pos (by omega : 0 < n) (k + r)
  have hweight :=
    upperChannelWeight_pos (by omega : 0 < n) (k + r)
  unfold solidHarmonicSourceUpperIsometryCoefficient
  rw [div_pow, Real.sq_sqrt hweight.le,
    solidHarmonicSourceUpperCoefficient_sq hn k r]
  unfold upperChannelWeight upperChannelDenominator
    SpherePacking.Gegenbauer.alphaSq
    SpherePacking.harmonicAxisParameter
  push_cast
  field_simp
  ring

theorem solidHarmonicSourceUpperIsometryCoefficient_pos
    {n : ℕ} (hn : 3 ≤ n) (k r : ℕ) :
    0 < solidHarmonicSourceUpperIsometryCoefficient n k r := by
  unfold solidHarmonicSourceUpperIsometryCoefficient
  exact div_pos
    (solidHarmonicSourceUpperCoefficient_pos hn k r)
    (Real.sqrt_pos.mpr
      (upperChannelWeight_pos (by omega : 0 < n) (k + r)))

theorem solidHarmonicSourceUpperIsometryCoefficient_eq_sqrt
    {n : ℕ} (hn : 3 ≤ n) (k r : ℕ) :
    solidHarmonicSourceUpperIsometryCoefficient n k r =
      Real.sqrt (SpherePacking.Gegenbauer.alphaSq n k (k + r)) := by
  have hcoef := solidHarmonicSourceUpperIsometryCoefficient_pos hn k r
  have halpha := SpherePacking.Gegenbauer.alphaSq_pos hn
    (show k ≤ k + r by omega)
  have hsquare := solidHarmonicSourceUpperIsometryCoefficient_sq
    hn k r
  have hroot := Real.sq_sqrt halpha.le
  have hroot_nonneg :=
    Real.sqrt_nonneg (SpherePacking.Gegenbauer.alphaSq n k (k + r))
  nlinarith

theorem harmonic_inner_smul_right
    (n m : ℕ) (p q : HarmonicSpace n m) (c : ℝ) :
    ⟪p, c • q⟫_ℝ = c * ⟪p, q⟫_ℝ := by
  rw [SpherePacking.Fischer.harmonic_inner_eq,
    SpherePacking.Fischer.harmonicInner_eq_polynomialInner,
    SpherePacking.Fischer.harmonic_inner_eq,
    SpherePacking.Fischer.harmonicInner_eq_polynomialInner]
  change
    SpherePacking.Fischer.polynomialInner n
        (p : MvPolynomial (Fin n) ℝ)
        (c • (q : MvPolynomial (Fin n) ℝ)) =
      c * SpherePacking.Fischer.polynomialInner n
        (p : MvPolynomial (Fin n) ℝ)
        (q : MvPolynomial (Fin n) ℝ)
  exact SpherePacking.Fischer.polynomialInner_smul_right n c
    (p : MvPolynomial (Fin n) ℝ)
    (q : MvPolynomial (Fin n) ℝ)

theorem harmonic_inner_smul_left
    (n m : ℕ) (p q : HarmonicSpace n m) (c : ℝ) :
    ⟪c • p, q⟫_ℝ = c * ⟪p, q⟫_ℝ := by
  rw [SpherePacking.Fischer.harmonic_inner_eq,
    SpherePacking.Fischer.harmonicInner_eq_polynomialInner,
    SpherePacking.Fischer.harmonic_inner_eq,
    SpherePacking.Fischer.harmonicInner_eq_polynomialInner]
  change
    SpherePacking.Fischer.polynomialInner n
        (c • (p : MvPolynomial (Fin n) ℝ))
        (q : MvPolynomial (Fin n) ℝ) =
      c * SpherePacking.Fischer.polynomialInner n
        (p : MvPolynomial (Fin n) ℝ)
        (q : MvPolynomial (Fin n) ℝ)
  exact SpherePacking.Fischer.polynomialInner_smul_left n c
    (p : MvPolynomial (Fin n) ℝ)
    (q : MvPolynomial (Fin n) ℝ)

theorem upperChannelIsometry_adjoint_solidHarmonicSource
    {n : ℕ} (hn : 3 ≤ n) (k r : ℕ)
    (x : SpherePacking.Euclidean n) (hx : ‖x‖ = 1)
    (p : SpherePacking.tangentHarmonicSubmodule n k x) :
    (upperChannelIsometry (by omega : 0 < n)
      (k + r)).toLinearMap.adjoint
        (solidHarmonicSource hn k r x hx p) =
      Real.sqrt
          (SpherePacking.Gegenbauer.alphaSq n k (k + r)) •
        SpherePacking.solidHarmonicAxisPolynomialIsometry
          hn k (r + 1) x hx p := by
  apply ext_inner_left ℝ
  intro q
  calc
    ⟪q,
      (upperChannelIsometry (by omega : 0 < n)
        (k + r)).toLinearMap.adjoint
          (solidHarmonicSource hn k r x hx p)⟫_ℝ =
      ⟪upperChannelIsometry (by omega : 0 < n)
          (k + r) q,
        solidHarmonicSource hn k r x hx p⟫_ℝ :=
        LinearMap.adjoint_inner_right
          (upperChannelIsometry (by omega : 0 < n)
            (k + r)).toLinearMap q
          (solidHarmonicSource hn k r x hx p)
    _ =
      ⟪(Real.sqrt (upperChannelWeight n (k + r)))⁻¹ •
          upperChannelAdjoint n (k + r) q,
        solidHarmonicSource hn k r x hx p⟫_ℝ := by
        rfl
    _ =
      (Real.sqrt (upperChannelWeight n (k + r)))⁻¹ *
        ⟪upperChannelAdjoint n (k + r) q,
          solidHarmonicSource hn k r x hx p⟫_ℝ := by
        rw [real_inner_smul_left]
    _ =
      (Real.sqrt (upperChannelWeight n (k + r)))⁻¹ *
        ⟪q, upperChannel n (k + r)
          (solidHarmonicSource hn k r x hx p)⟫_ℝ := by
        have hadjoint :=
          LinearMap.adjoint_inner_left (upperChannel n (k + r))
            (solidHarmonicSource hn k r x hx p) q
        rw [upperChannel_adjoint] at hadjoint
        exact congrArg
          (fun z : ℝ =>
            (Real.sqrt (upperChannelWeight n (k + r)))⁻¹ * z)
          hadjoint
    _ =
      (Real.sqrt (upperChannelWeight n (k + r)))⁻¹ *
        ⟪q,
          solidHarmonicSourceUpperCoefficient n k r •
            SpherePacking.solidHarmonicAxisPolynomialIsometry
              hn k (r + 1) x hx p⟫_ℝ := by
        rw [upperChannel_solidHarmonicSource hn k r x hx p]
    _ =
      solidHarmonicSourceUpperIsometryCoefficient n k r *
        ⟪q,
          SpherePacking.solidHarmonicAxisPolynomialIsometry
            hn k (r + 1) x hx p⟫_ℝ := by
        rw [harmonic_inner_smul_right]
        unfold solidHarmonicSourceUpperIsometryCoefficient
        ring
    _ =
      ⟪q,
        Real.sqrt (SpherePacking.Gegenbauer.alphaSq n k (k + r)) •
          SpherePacking.solidHarmonicAxisPolynomialIsometry
            hn k (r + 1) x hx p⟫_ℝ := by
        rw [harmonic_inner_smul_right,
          solidHarmonicSourceUpperIsometryCoefficient_eq_sqrt
            hn k r]

theorem lowerChannel_harmonicAxisTensor_inner
    (n m : ℕ) (x : SpherePacking.Euclidean n)
    (p : HarmonicSpace n (m + 1))
    (q : HarmonicSpace n m) :
    ⟪lowerChannel n m (harmonicAxisTensor n (m + 1) x p), q⟫_ℝ =
      (Real.sqrt (upperChannelDenominator n m))⁻¹ *
        SpherePacking.Fischer.polynomialInner n
          (SpherePacking.directionalDerivative n x
            (p : MvPolynomial (Fin n) ℝ))
          (q : MvPolynomial (Fin n) ℝ) := by
  classical
  have hsingle (j : Fin n) :
      ⟪x j • p,
        (Real.sqrt (upperChannelDenominator n m))⁻¹ •
          harmonicCoordinateRaising n m j q⟫_ℝ =
        (Real.sqrt (upperChannelDenominator n m))⁻¹ *
          SpherePacking.Fischer.polynomialInner n
            (x j • MvPolynomial.pderiv j
              (p : MvPolynomial (Fin n) ℝ))
            (q : MvPolynomial (Fin n) ℝ) := by
    rw [harmonic_inner_smul_left,
      harmonic_inner_smul_right]
    have hadjoint :=
      LinearMap.adjoint_inner_right
        (harmonicCoordinateDerivative n m j) p q
    change
      ⟪p, harmonicCoordinateRaising n m j q⟫_ℝ =
        ⟪harmonicCoordinateDerivative n m j p, q⟫_ℝ
      at hadjoint
    rw [hadjoint,
      SpherePacking.Fischer.harmonic_inner_eq,
      SpherePacking.Fischer.harmonicInner_eq_polynomialInner,
      harmonicCoordinateDerivative_apply,
      SpherePacking.Fischer.polynomialInner_smul_left]
    ring
  calc
    ⟪lowerChannel n m (harmonicAxisTensor n (m + 1) x p), q⟫_ℝ =
      ⟪harmonicAxisTensor n (m + 1) x p,
        lowerChannelAdjoint n m q⟫_ℝ := by
        rw [← lowerChannel_adjoint]
        exact
          (LinearMap.adjoint_inner_right (lowerChannel n m)
            (harmonicAxisTensor n (m + 1) x p) q).symm
    _ =
      ∑ j : Fin n,
        ⟪x j • p,
          (Real.sqrt (upperChannelDenominator n m))⁻¹ •
            harmonicCoordinateRaising n m j q⟫_ℝ := by
        rw [PiLp.inner_apply]
        rfl
    _ =
      ∑ j : Fin n,
        (Real.sqrt (upperChannelDenominator n m))⁻¹ *
          SpherePacking.Fischer.polynomialInner n
            (x j • MvPolynomial.pderiv j
              (p : MvPolynomial (Fin n) ℝ))
            (q : MvPolynomial (Fin n) ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hsingle j
    _ = _ := by
        rw [SpherePacking.directionalDerivative_apply,
          SpherePacking.Fischer.polynomialInner_sum_left,
          Finset.mul_sum]

private def solidHarmonicSourceLowerCoefficient (n k r : ℕ) : ℝ :=
  (((r : ℝ) + 1) *
    ((r : ℝ) + SpherePacking.harmonicAxisParameter n k - 2) *
    Real.sqrt (SpherePacking.solidHarmonicAxisFischerScale n k r)) /
      (Real.sqrt
        (SpherePacking.solidHarmonicAxisFischerScale n k (r + 1)) *
        Real.sqrt (upperChannelDenominator n (k + r)))

theorem lowerChannel_solidHarmonicSource
    {n : ℕ} (hn : 3 ≤ n) (k r : ℕ)
    (x : SpherePacking.Euclidean n) (hx : ‖x‖ = 1)
    (p : SpherePacking.tangentHarmonicSubmodule n k x) :
    lowerChannel n (k + r)
        (solidHarmonicSource hn k (r + 1) x hx p) =
      solidHarmonicSourceLowerCoefficient n k r •
        SpherePacking.solidHarmonicAxisPolynomialIsometry
          hn k r x hx p := by
  have hscale :=
    SpherePacking.solidHarmonicAxisFischerScale_pos hn k r
  have hscale_next :=
    SpherePacking.solidHarmonicAxisFischerScale_pos hn k (r + 1)
  have hden :=
    upperChannelDenominator_pos (by omega : 0 < n) (k + r)
  have hsqrt :
      Real.sqrt
        (SpherePacking.solidHarmonicAxisFischerScale n k r) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hscale)
  have hsqrt_next :
      Real.sqrt
        (SpherePacking.solidHarmonicAxisFischerScale
          n k (r + 1)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hscale_next)
  have hsqrt_den :
      Real.sqrt (upperChannelDenominator n (k + r)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hden)
  apply ext_inner_right ℝ
  intro q
  change
    ⟪lowerChannel n (k + r)
        (harmonicAxisTensor n ((k + r) + 1) x
          (SpherePacking.solidHarmonicAxisPolynomialIsometry
            hn k (r + 1) x hx p)), q⟫_ℝ =
      ⟪solidHarmonicSourceLowerCoefficient n k r •
          SpherePacking.solidHarmonicAxisPolynomialIsometry
            hn k r x hx p, q⟫_ℝ
  rw [lowerChannel_harmonicAxisTensor_inner,
    SpherePacking.Fischer.harmonic_inner_eq,
    SpherePacking.Fischer.harmonicInner_eq_polynomialInner]
  change
    (Real.sqrt (upperChannelDenominator n (k + r)))⁻¹ *
      SpherePacking.Fischer.polynomialInner n
        (SpherePacking.directionalDerivative n x
          ((Real.sqrt
              (SpherePacking.solidHarmonicAxisFischerScale
                n k (r + 1)))⁻¹ •
            SpherePacking.solidHarmonicAxisLift n k x (r + 1)
              (p : MvPolynomial (Fin n) ℝ)))
        (q : MvPolynomial (Fin n) ℝ) =
      SpherePacking.Fischer.polynomialInner n
        (solidHarmonicSourceLowerCoefficient n k r •
          ((Real.sqrt
              (SpherePacking.solidHarmonicAxisFischerScale n k r))⁻¹ •
            SpherePacking.solidHarmonicAxisLift n k x r
              (p : MvPolynomial (Fin n) ℝ)))
        (q : MvPolynomial (Fin n) ℝ)
  rw [map_smul,
    SpherePacking.Fischer.polynomialInner_smul_left,
    SpherePacking.Fischer.polynomialInner_smul_left,
    SpherePacking.Fischer.polynomialInner_smul_left]
  have hder :=
    (SpherePacking.solidHarmonicAxisLift_harmonic_and_directional
      x hx p.property (r + 1)).2
  simp only [Nat.add_sub_cancel] at hder
  rw [hder,
    SpherePacking.fischer_polynomialInner_constant_mul_left]
  unfold solidHarmonicSourceLowerCoefficient
  push_cast
  field_simp [hsqrt, hsqrt_next, hsqrt_den]
  ring

private def solidHarmonicSourceLowerIsometryCoefficient
    (n k r : ℕ) : ℝ :=
  solidHarmonicSourceLowerCoefficient n k r /
    Real.sqrt (lowerChannelWeight n (k + r))

theorem solidHarmonicSourceLowerCoefficient_pos
    {n : ℕ} (hn : 3 ≤ n) (k r : ℕ) :
    0 < solidHarmonicSourceLowerCoefficient n k r := by
  have hnreal : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hkreal : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hrreal : (0 : ℝ) ≤ (r : ℝ) := by positivity
  have hlast :
      0 < (r : ℝ) +
        SpherePacking.harmonicAxisParameter n k - 2 := by
    unfold SpherePacking.harmonicAxisParameter
    linarith
  unfold solidHarmonicSourceLowerCoefficient
  apply div_pos
  · exact mul_pos
      (mul_pos (by positivity) hlast)
      (Real.sqrt_pos.mpr
        (SpherePacking.solidHarmonicAxisFischerScale_pos hn k r))
  · exact mul_pos
      (Real.sqrt_pos.mpr
        (SpherePacking.solidHarmonicAxisFischerScale_pos
          hn k (r + 1)))
      (Real.sqrt_pos.mpr
        (upperChannelDenominator_pos (by omega : 0 < n) (k + r)))

theorem solidHarmonicSourceLowerCoefficient_sq
    {n : ℕ} (hn : 3 ≤ n) (k r : ℕ) :
    solidHarmonicSourceLowerCoefficient n k r ^ 2 =
      (((r : ℝ) + 1) *
        ((r : ℝ) + SpherePacking.harmonicAxisParameter n k - 2)) /
        ((2 * (r : ℝ) +
          SpherePacking.harmonicAxisParameter n k - 2) *
          upperChannelDenominator n (k + r)) := by
  have hnreal : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hkreal : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hrreal : (0 : ℝ) ≤ (r : ℝ) := by positivity
  have hraise :
      0 < 2 * (r : ℝ) +
        SpherePacking.harmonicAxisParameter n k - 2 := by
    unfold SpherePacking.harmonicAxisParameter
    linarith
  have hscale :=
    SpherePacking.solidHarmonicAxisFischerScale_pos hn k r
  have hscale_next :=
    SpherePacking.solidHarmonicAxisFischerScale_pos hn k (r + 1)
  have hden :=
    upperChannelDenominator_pos (by omega : 0 < n) (k + r)
  unfold solidHarmonicSourceLowerCoefficient
  rw [div_pow, mul_pow, mul_pow, mul_pow,
    Real.sq_sqrt hscale.le,
    Real.sq_sqrt hscale_next.le,
    Real.sq_sqrt hden.le,
    SpherePacking.solidHarmonicAxisFischerScale_succ]
  field_simp [ne_of_gt hraise, ne_of_gt hscale,
    ne_of_gt hden]

theorem solidHarmonicSourceLowerIsometryCoefficient_sq
    {n : ℕ} (hn : 3 ≤ n) (k r : ℕ) :
    solidHarmonicSourceLowerIsometryCoefficient n k r ^ 2 =
      SpherePacking.Gegenbauer.betaSq n k (k + (r + 1)) := by
  have hnreal : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hkreal : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hrreal : (0 : ℝ) ≤ (r : ℝ) := by positivity
  have hraise :
      0 < 2 * (r : ℝ) +
        SpherePacking.harmonicAxisParameter n k - 2 := by
    unfold SpherePacking.harmonicAxisParameter
    linarith
  have hden :=
    upperChannelDenominator_pos (by omega : 0 < n) (k + r)
  have hweight := lowerChannelWeight_pos hn (k + r)
  have hmiddle :
      0 < (k : ℝ) + (r : ℝ) + (n : ℝ) - 2 := by
    linarith
  have hlowerden :
      0 < 2 * ((k : ℝ) + (r : ℝ)) + (n : ℝ) - 2 := by
    linarith
  have hupperden :
      0 < 2 * ((k : ℝ) + (r : ℝ)) + (n : ℝ) := by
    linarith
  have hfirstden :
      0 < 2 * (r : ℝ) +
        ((n : ℝ) + 2 * (k : ℝ)) - 2 := by
    linarith
  have hfirstden_rev :
      0 < (r : ℝ) * 2 +
        ((n : ℝ) + 2 * (k : ℝ)) - 2 := by
    linarith
  have hbetafirst :
      0 < (k : ℝ) + ((r : ℝ) + 1) + (n : ℝ) - 3 := by
    linarith
  have hbetasecond :
      0 < 2 * ((k : ℝ) + ((r : ℝ) + 1)) + (n : ℝ) - 2 := by
    linarith
  unfold solidHarmonicSourceLowerIsometryCoefficient
  rw [div_pow, Real.sq_sqrt hweight.le,
    solidHarmonicSourceLowerCoefficient_sq hn k r]
  unfold lowerChannelWeight upperChannelDenominator
    SpherePacking.Gegenbauer.betaSq
    SpherePacking.harmonicAxisParameter
  push_cast
  field_simp [ne_of_gt hmiddle, ne_of_gt hlowerden,
    ne_of_gt hupperden, ne_of_gt hfirstden,
    ne_of_gt hfirstden_rev,
    ne_of_gt hbetafirst, ne_of_gt hbetasecond]
  ring

theorem solidHarmonicSourceLowerIsometryCoefficient_pos
    {n : ℕ} (hn : 3 ≤ n) (k r : ℕ) :
    0 < solidHarmonicSourceLowerIsometryCoefficient n k r := by
  unfold solidHarmonicSourceLowerIsometryCoefficient
  exact div_pos
    (solidHarmonicSourceLowerCoefficient_pos hn k r)
    (Real.sqrt_pos.mpr (lowerChannelWeight_pos hn (k + r)))

theorem solidHarmonicSourceLowerIsometryCoefficient_eq_sqrt
    {n : ℕ} (hn : 3 ≤ n) (k r : ℕ) :
    solidHarmonicSourceLowerIsometryCoefficient n k r =
      Real.sqrt
        (SpherePacking.Gegenbauer.betaSq n k (k + (r + 1))) := by
  have hcoef := solidHarmonicSourceLowerIsometryCoefficient_pos hn k r
  have hsquare := solidHarmonicSourceLowerIsometryCoefficient_sq
    hn k r
  have hbeta :
      0 ≤ SpherePacking.Gegenbauer.betaSq n k (k + (r + 1)) := by
    rw [← hsquare]
    positivity
  have hroot := Real.sq_sqrt hbeta
  have hroot_nonneg := Real.sqrt_nonneg
    (SpherePacking.Gegenbauer.betaSq n k (k + (r + 1)))
  nlinarith

theorem lowerChannelIsometry_adjoint_solidHarmonicSource
    {n : ℕ} (hn : 3 ≤ n) (k r : ℕ)
    (x : SpherePacking.Euclidean n) (hx : ‖x‖ = 1)
    (p : SpherePacking.tangentHarmonicSubmodule n k x) :
    (lowerChannelIsometry hn (k + r)).toLinearMap.adjoint
        (solidHarmonicSource hn k (r + 1) x hx p) =
      Real.sqrt
          (SpherePacking.Gegenbauer.betaSq n k (k + (r + 1))) •
        SpherePacking.solidHarmonicAxisPolynomialIsometry
          hn k r x hx p := by
  apply ext_inner_left ℝ
  intro q
  calc
    ⟪q,
      (lowerChannelIsometry hn (k + r)).toLinearMap.adjoint
        (solidHarmonicSource hn k (r + 1) x hx p)⟫_ℝ =
      ⟪lowerChannelIsometry hn (k + r) q,
        solidHarmonicSource hn k (r + 1) x hx p⟫_ℝ :=
        LinearMap.adjoint_inner_right
          (lowerChannelIsometry hn (k + r)).toLinearMap q
          (solidHarmonicSource hn k (r + 1) x hx p)
    _ =
      ⟪(Real.sqrt (lowerChannelWeight n (k + r)))⁻¹ •
          lowerChannelAdjoint n (k + r) q,
        solidHarmonicSource hn k (r + 1) x hx p⟫_ℝ := by
        rfl
    _ =
      (Real.sqrt (lowerChannelWeight n (k + r)))⁻¹ *
        ⟪lowerChannelAdjoint n (k + r) q,
          solidHarmonicSource hn k (r + 1) x hx p⟫_ℝ := by
        rw [real_inner_smul_left]
    _ =
      (Real.sqrt (lowerChannelWeight n (k + r)))⁻¹ *
        ⟪q, lowerChannel n (k + r)
          (solidHarmonicSource hn k (r + 1) x hx p)⟫_ℝ := by
        have hadjoint :=
          LinearMap.adjoint_inner_left (lowerChannel n (k + r))
            (solidHarmonicSource hn k (r + 1) x hx p) q
        rw [lowerChannel_adjoint] at hadjoint
        exact congrArg
          (fun z : ℝ =>
            (Real.sqrt (lowerChannelWeight n (k + r)))⁻¹ * z)
          hadjoint
    _ =
      (Real.sqrt (lowerChannelWeight n (k + r)))⁻¹ *
        ⟪q,
          solidHarmonicSourceLowerCoefficient n k r •
            SpherePacking.solidHarmonicAxisPolynomialIsometry
              hn k r x hx p⟫_ℝ := by
        rw [lowerChannel_solidHarmonicSource hn k r x hx p]
    _ =
      solidHarmonicSourceLowerIsometryCoefficient n k r *
        ⟪q,
          SpherePacking.solidHarmonicAxisPolynomialIsometry
            hn k r x hx p⟫_ℝ := by
        rw [harmonic_inner_smul_right]
        unfold solidHarmonicSourceLowerIsometryCoefficient
        ring
    _ =
      ⟪q,
        Real.sqrt
            (SpherePacking.Gegenbauer.betaSq
              n k (k + (r + 1))) •
          SpherePacking.solidHarmonicAxisPolynomialIsometry
            hn k r x hx p⟫_ℝ := by
        rw [harmonic_inner_smul_right,
          solidHarmonicSourceLowerIsometryCoefficient_eq_sqrt
            hn k r]

end HarmonicSourceProjection

namespace HarmonicAdjacentChannelTransport

open HarmonicCertificateAssembly
open HarmonicCoordinateChannels
open HarmonicCoordinateOperators

private def harmonicDegreeCastLinearMap
    (n r s : ℕ) (h : r = s) :
    HarmonicSpace n r →ₗ[ℝ] HarmonicSpace n s where
  toFun p := ⟨p.1, by simpa only [mem_harmonicHomogeneousSubmodule, h] using p.property⟩
  map_add' p q := by
    apply Subtype.ext
    rfl
  map_smul' c p := by
    apply Subtype.ext
    rfl

theorem harmonicDegreeCastLinearMap_inner
    (n r s : ℕ) (h : r = s)
    (p q : HarmonicSpace n r) :
    ⟪harmonicDegreeCastLinearMap n r s h p,
      harmonicDegreeCastLinearMap n r s h q⟫_ℝ =
      ⟪p, q⟫_ℝ := by
  rw [Fischer.harmonic_inner_eq,
    Fischer.harmonicInner_eq_polynomialInner,
    Fischer.harmonic_inner_eq,
    Fischer.harmonicInner_eq_polynomialInner]
  rfl

private def harmonicDegreeCast
    (n r s : ℕ) (h : r = s) :
    HarmonicSpace n r →ₗᵢ[ℝ] HarmonicSpace n s :=
  (harmonicDegreeCastLinearMap n r s h).isometryOfInner
    (harmonicDegreeCastLinearMap_inner n r s h)

@[simp] theorem harmonicDegreeCast_adjoint_apply
    (n r s : ℕ) (h : r = s)
    (p : HarmonicSpace n s) :
    (harmonicDegreeCast n r s h).toLinearMap.adjoint p =
      harmonicDegreeCast n s r h.symm p := by
  subst s
  apply ext_inner_left ℝ
  intro q
  rw [LinearMap.adjoint_inner_right]
  rfl

theorem transportedIsometry_adjoint
    {E F G B : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F]
    [FiniteDimensional ℝ G]
    [FiniteDimensional ℝ B]
    (T : F →ₗᵢ[ℝ] G)
    (A : E →ₗᵢ[ℝ] F)
    (e : E ≃ₗᵢ[ℝ] B)
    (z : F) :
    (T.comp (A.comp e.symm.toLinearIsometry)).toLinearMap.adjoint
        (T z) =
      e (A.toLinearMap.adjoint z) := by
  apply ext_inner_left ℝ
  intro v
  calc
    ⟪v,
      (T.comp (A.comp e.symm.toLinearIsometry)).toLinearMap.adjoint
        (T z)⟫_ℝ =
      ⟪T (A (e.symm v)), T z⟫_ℝ :=
        LinearMap.adjoint_inner_right
          (T.comp (A.comp e.symm.toLinearIsometry)).toLinearMap
          v (T z)
    _ = ⟪A (e.symm v), z⟫_ℝ := T.inner_map_map _ _
    _ = ⟪e.symm v, A.toLinearMap.adjoint z⟫_ℝ :=
      (LinearMap.adjoint_inner_right A.toLinearMap
        (e.symm v) z).symm
    _ = ⟪v, e (A.toLinearMap.adjoint z)⟫_ℝ := by
      have he := e.inner_map_map (e.symm v)
        (A.toLinearMap.adjoint z)
      simpa only [e.apply_symm_apply] using he.symm

private def coordinateHarmonicDegreeCastLinearMap
    (n r s : ℕ) (h : r = s) :
    CoordinateHarmonicSpace n r →ₗ[ℝ]
      CoordinateHarmonicSpace n s where
  toFun z := WithLp.toLp 2
    (fun a : Fin n => harmonicDegreeCast n r s h (z a))
  map_add' z w := by
    apply PiLp.ext
    intro a
    exact (harmonicDegreeCast n r s h).map_add (z a) (w a)
  map_smul' c z := by
    apply PiLp.ext
    intro a
    exact (harmonicDegreeCast n r s h).map_smul c (z a)

theorem coordinateHarmonicDegreeCastLinearMap_inner
    (n r s : ℕ) (h : r = s)
    (z w : CoordinateHarmonicSpace n r) :
    ⟪coordinateHarmonicDegreeCastLinearMap n r s h z,
      coordinateHarmonicDegreeCastLinearMap n r s h w⟫_ℝ =
      ⟪z, w⟫_ℝ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro a _
  exact (harmonicDegreeCast n r s h).inner_map_map (z a) (w a)

private def coordinateHarmonicDegreeCast
    (n r s : ℕ) (h : r = s) :
    CoordinateHarmonicSpace n r →ₗᵢ[ℝ]
      CoordinateHarmonicSpace n s :=
  (coordinateHarmonicDegreeCastLinearMap n r s h).isometryOfInner
    (coordinateHarmonicDegreeCastLinearMap_inner n r s h)

@[simp] theorem coordinateHarmonicDegreeCast_adjoint_apply
    (n r s : ℕ) (h : r = s)
    (z : CoordinateHarmonicSpace n s) :
    (coordinateHarmonicDegreeCast n r s h).toLinearMap.adjoint z =
      coordinateHarmonicDegreeCast n s r h.symm z := by
  subst s
  apply ext_inner_left ℝ
  intro w
  rw [LinearMap.adjoint_inner_right]
  rfl

theorem coordinateHarmonicDegreeCast_axis
    (n r s : ℕ) (h : r = s)
    (x : Euclidean n) (p : HarmonicSpace n r) :
    coordinateHarmonicDegreeCast n r s h
      (HarmonicSourceProjection.harmonicAxisTensor n r x p) =
      HarmonicSourceProjection.harmonicAxisTensor n s x
        (harmonicDegreeCast n r s h p) := by
  apply PiLp.ext
  intro a
  change
    harmonicDegreeCast n r s h (x a • p) =
      x a • harmonicDegreeCast n r s h p
  exact (harmonicDegreeCast n r s h).map_smul (x a) p

private def coordinateDegreeTransportLinearMap
    {n : ℕ} (hn : 3 ≤ n) (k L : ℕ)
    (i : Jacobi.Index k L) :
    CoordinateHarmonicSpace n (k + i.val) →ₗ[ℝ]
      HarmonicDegreeRowChannelSpace n k L i where
  toFun z := WithLp.toLp 2
    (fun a : Fin n =>
      harmonicDegreeEuclideanEquiv n k L (by omega) i (z a))
  map_add' z w := by
    apply PiLp.ext
    intro a
    exact (harmonicDegreeEuclideanEquiv n k L
      (by omega) i).map_add (z a) (w a)
  map_smul' c z := by
    apply PiLp.ext
    intro a
    exact (harmonicDegreeEuclideanEquiv n k L
      (by omega) i).map_smul c (z a)

theorem coordinateDegreeTransportLinearMap_inner
    {n : ℕ} (hn : 3 ≤ n) (k L : ℕ)
    (i : Jacobi.Index k L)
    (z w : CoordinateHarmonicSpace n (k + i.val)) :
    ⟪coordinateDegreeTransportLinearMap hn k L i z,
      coordinateDegreeTransportLinearMap hn k L i w⟫_ℝ =
      ⟪z, w⟫_ℝ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro a _
  exact (harmonicDegreeEuclideanEquiv n k L
    (by omega) i).inner_map_map (z a) (w a)

private def coordinateDegreeTransport
    {n : ℕ} (hn : 3 ≤ n) (k L : ℕ)
    (i : Jacobi.Index k L) :
    CoordinateHarmonicSpace n (k + i.val) →ₗᵢ[ℝ]
      HarmonicDegreeRowChannelSpace n k L i :=
  (coordinateDegreeTransportLinearMap hn k L i).isometryOfInner
    (coordinateDegreeTransportLinearMap_inner hn k L i)

theorem coordinateDegreeTransport_axis
    {n : ℕ} (hn : 3 ≤ n) (k L : ℕ)
    (i : Jacobi.Index k L)
    (x : Euclidean n) (p : HarmonicSpace n (k + i.val)) :
    coordinateDegreeTransport hn k L i
        (HarmonicSourceProjection.harmonicAxisTensor
          n (k + i.val) x p) =
      harmonicDegreeAxisTensor n k L i x
        (harmonicDegreeEuclideanEquiv n k L (by omega) i p) := by
  apply PiLp.ext
  intro a
  change
    harmonicDegreeEuclideanEquiv n k L (by omega) i
        (x a • p) =
      x a • harmonicDegreeEuclideanEquiv n k L
        (by omega) i p
  exact (harmonicDegreeEuclideanEquiv n k L
    (by omega) i).map_smul (x a) p

private def upperAdjacentChannel
    {n : ℕ} (hn : 3 ≤ n) (k L : ℕ)
    (target source : Jacobi.Index k L)
    (hadjacent : target.val + 1 = source.val) :
    CertificateDegreeAmbient n k L source →ₗᵢ[ℝ]
      HarmonicDegreeRowChannelSpace n k L target :=
  (coordinateDegreeTransport hn k L target).comp
    ((upperChannelIsometry (show 0 < n by omega)
      (k + target.val)).comp
        ((harmonicDegreeCast n (k + source.val)
          ((k + target.val) + 1) (by omega)).comp
            (harmonicDegreeEuclideanEquiv n k L
              (by omega) source).symm.toLinearIsometry))

private def lowerAdjacentChannel
    {n : ℕ} (hn : 3 ≤ n) (k L : ℕ)
    (target source : Jacobi.Index k L)
    (hadjacent : source.val + 1 = target.val) :
    CertificateDegreeAmbient n k L source →ₗᵢ[ℝ]
      HarmonicDegreeRowChannelSpace n k L target :=
  (coordinateDegreeTransport hn k L target).comp
    ((coordinateHarmonicDegreeCast n
      ((k + source.val) + 1) (k + target.val)
        (by omega)).comp
      ((lowerChannelIsometry hn (k + source.val)).comp
        (harmonicDegreeEuclideanEquiv n k L
          (by omega) source).symm.toLinearIsometry))

private def adjacentChannel
    {n : ℕ} (hn : 3 ≤ n) (k L : ℕ)
    (target source : Jacobi.Index k L) :
    CertificateDegreeAmbient n k L source →ₗ[ℝ]
      HarmonicDegreeRowChannelSpace n k L target :=
  if hupper : target.val + 1 = source.val then
    (upperAdjacentChannel hn k L target source hupper).toLinearMap
  else if hlower : source.val + 1 = target.val then
    (lowerAdjacentChannel hn k L target source hlower).toLinearMap
  else
    0

theorem upperAdjacentChannel_lowerAdjacentChannel_orthogonal
    {n : ℕ} (hn : 3 ≤ n) (k L : ℕ)
    (target high low : Jacobi.Index k L)
    (hhigh : target.val + 1 = high.val)
    (hlow : low.val + 1 = target.val)
    (p : CertificateDegreeAmbient n k L high)
    (q : CertificateDegreeAmbient n k L low) :
    ⟪upperAdjacentChannel hn k L target high hhigh p,
      lowerAdjacentChannel hn k L target low hlow q⟫_ℝ = 0 := by
  rcases target with ⟨t, ht⟩
  rcases high with ⟨a, ha⟩
  rcases low with ⟨b, hb⟩
  dsimp at hhigh hlow
  subst t
  subst a
  change
    ⟪coordinateDegreeTransport hn k L _ _,
      coordinateDegreeTransport hn k L _ _⟫_ℝ = 0
  rw [(coordinateDegreeTransport hn k L _).inner_map_map]
  exact upperChannelIsometry_lowerChannelIsometry_orthogonal
    hn (k + b)
    ((harmonicDegreeEuclideanEquiv n k L
      (by omega) ⟨b + 1 + 1, ha⟩).symm p)
    ((harmonicDegreeEuclideanEquiv n k L
      (by omega) ⟨b, hb⟩).symm q)

theorem lowerAdjacentChannel_upperAdjacentChannel_orthogonal
    {n : ℕ} (hn : 3 ≤ n) (k L : ℕ)
    (target low high : Jacobi.Index k L)
    (hlow : low.val + 1 = target.val)
    (hhigh : target.val + 1 = high.val)
    (p : CertificateDegreeAmbient n k L low)
    (q : CertificateDegreeAmbient n k L high) :
    ⟪lowerAdjacentChannel hn k L target low hlow p,
      upperAdjacentChannel hn k L target high hhigh q⟫_ℝ = 0 := by
  rw [real_inner_comm]
  exact upperAdjacentChannel_lowerAdjacentChannel_orthogonal
    hn k L target high low hhigh hlow q p

theorem adjacentChannel_inner
    {n : ℕ} (hn : 3 ≤ n) (k L : ℕ)
    (target source : Jacobi.Index k L)
    (hsource : SourceJacobiWeights.sourceChannelCoefficient
      n k L source target ≠ 0)
    (u v : CertificateDegreeAmbient n k L source) :
    ⟪adjacentChannel hn k L target source u,
      adjacentChannel hn k L target source v⟫_ℝ =
      ⟪u, v⟫_ℝ := by
  unfold adjacentChannel
  split <;> rename_i hupper
  · exact
      (upperAdjacentChannel hn k L target source hupper).inner_map_map
        u v
  · split <;> rename_i hlower
    · exact
        (lowerAdjacentChannel hn k L target source hlower).inner_map_map
          u v
    · exfalso
      apply hsource
      simp only [SourceJacobiWeights.sourceChannelCoefficient, hupper, ↓reduceIte, hlower]

theorem adjacentChannel_zero
    {n : ℕ} (hn : 3 ≤ n) (k L : ℕ)
    (target source : Jacobi.Index k L)
    (hzero : SourceJacobiWeights.sourceChannelCoefficient
      n k L source target = 0) :
    adjacentChannel hn k L target source = 0 := by
  unfold adjacentChannel
  split <;> rename_i hupper
  · exact False.elim
      ((SourceJacobiWeights.sourceChannelCoefficient_pos_of_adjacent
        hn source target (Or.inr hupper)).ne' hzero)
  · split <;> rename_i hlower
    · exact False.elim
        ((SourceJacobiWeights.sourceChannelCoefficient_pos_of_adjacent
          hn source target (Or.inl hlower)).ne' hzero)
    · rfl

theorem adjacentChannel_orthogonal
    {n : ℕ} (hn : 3 ≤ n) (k L : ℕ)
    (target source₁ source₂ : Jacobi.Index k L)
    (hne : source₁ ≠ source₂)
    (u : CertificateDegreeAmbient n k L source₁)
    (v : CertificateDegreeAmbient n k L source₂) :
    ⟪adjacentChannel hn k L target source₁ u,
      adjacentChannel hn k L target source₂ v⟫_ℝ = 0 := by
  unfold adjacentChannel
  split <;> rename_i hupper₁
  · split <;> rename_i hupper₂
    · exfalso
      apply hne
      apply Fin.ext
      omega
    · split <;> rename_i hlower₂
      · exact upperAdjacentChannel_lowerAdjacentChannel_orthogonal
          hn k L target source₁ source₂ hupper₁ hlower₂ u v
      · simp only [LinearIsometry.coe_toLinearMap, LinearMap.zero_apply, inner_zero_right]
  · split <;> rename_i hlower₁
    · split <;> rename_i hupper₂
      · exact lowerAdjacentChannel_upperAdjacentChannel_orthogonal
          hn k L target source₁ source₂ hlower₁ hupper₂ u v
      · split <;> rename_i hlower₂
        · exfalso
          apply hne
          apply Fin.ext
          omega
        · simp only [LinearIsometry.coe_toLinearMap, LinearMap.zero_apply, inner_zero_right]
    · simp only [LinearMap.zero_apply, inner_zero_left]

private def sourceTangentPolynomial
    {n : ℕ} (hn : 3 ≤ n) (k : ℕ)
    (x : Euclidean n) (hx : ‖x‖ = 1)
    (u : CertificateFibre n k) :
    tangentHarmonicSubmodule n k x :=
  (tangentPolynomialEuclideanEquiv n k x
    (finrank_tangentHarmonicSubmodule hn k x hx)).symm u

theorem harmonicDegreeFibre_apply_eq
    {n : ℕ} (hn : 3 ≤ n) (k L : ℕ)
    (i : Jacobi.Index k L)
    (x : Euclidean n) (hx : ‖x‖ = 1)
    (u : CertificateFibre n k) :
    harmonicDegreeFibre hn k L i x u =
      harmonicDegreeEuclideanEquiv n k L (by omega) i
        (solidHarmonicAxisPolynomialIsometry hn k i.val x hx
          (sourceTangentPolynomial hn k x hx u)) := by
  rw [harmonicDegreeFibre_of_unit hn k L i x hx]
  rfl

theorem upperAdjacentChannel_axis_projection
    {n : ℕ} (hn : 3 ≤ n) (k L : ℕ)
    (target source : Jacobi.Index k L)
    (h : target.val + 1 = source.val)
    (x : Euclidean n) (hx : ‖x‖ = 1)
    (u : CertificateFibre n k) :
    (upperAdjacentChannel hn k L target source h).toLinearMap.adjoint
        (harmonicDegreeAxisTensor n k L target x
          (harmonicDegreeFibre hn k L target x u)) =
      Real.sqrt (Gegenbauer.alphaSq n k (k + target.val)) •
        harmonicDegreeFibre hn k L source x u := by
  let p := sourceTangentPolynomial hn k x hx u
  rw [harmonicDegreeFibre_apply_eq hn k L target x hx u,
    ← coordinateDegreeTransport_axis hn k L target x]
  rw [harmonicDegreeFibre_apply_eq hn k L source x hx u]
  change
    ((coordinateDegreeTransport hn k L target).comp
      (((upperChannelIsometry (show 0 < n by omega)
        (k + target.val)).comp
        (harmonicDegreeCast n (k + source.val)
          ((k + target.val) + 1) (by omega))).comp
          (harmonicDegreeEuclideanEquiv n k L
            (by omega) source).symm.toLinearIsometry)).toLinearMap.adjoint
        (coordinateDegreeTransport hn k L target
          (HarmonicSourceProjection.harmonicAxisTensor
            n (k + target.val) x
            (solidHarmonicAxisPolynomialIsometry
              hn k target.val x hx p))) =
      Real.sqrt (Gegenbauer.alphaSq n k (k + target.val)) •
        harmonicDegreeEuclideanEquiv n k L (by omega) source
          (solidHarmonicAxisPolynomialIsometry
            hn k source.val x hx p)
  rw [transportedIsometry_adjoint]
  change
    harmonicDegreeEuclideanEquiv n k L (by omega) source
      (((upperChannelIsometry (by omega : 0 < n)
          (k + target.val)).toLinearMap.comp
        (harmonicDegreeCast n (k + source.val)
          ((k + target.val) + 1) (by omega)).toLinearMap).adjoint
        (HarmonicSourceProjection.harmonicAxisTensor
          n (k + target.val) x
          (solidHarmonicAxisPolynomialIsometry
            hn k target.val x hx p))) = _
  rw [LinearMap.adjoint_comp]
  change
    harmonicDegreeEuclideanEquiv n k L (by omega) source
      ((harmonicDegreeCast n (k + source.val)
        ((k + target.val) + 1) (by omega)).toLinearMap.adjoint
        ((upperChannelIsometry (by omega : 0 < n)
          (k + target.val)).toLinearMap.adjoint
          (HarmonicSourceProjection.solidHarmonicSource
            hn k target.val x hx p))) = _
  rw [HarmonicSourceProjection.upperChannelIsometry_adjoint_solidHarmonicSource
    hn k target.val x hx p]
  rw [map_smul, harmonicDegreeCast_adjoint_apply, map_smul]
  congr 1
  congr 1
  apply Subtype.ext
  change
    (solidHarmonicAxisPolynomialIsometry
      hn k (target.val + 1) x hx p : MvPolynomial (Fin n) ℝ) =
      (solidHarmonicAxisPolynomialIsometry
        hn k source.val x hx p : MvPolynomial (Fin n) ℝ)
  rw [← h]

theorem lowerAdjacentChannel_axis_projection
    {n : ℕ} (hn : 3 ≤ n) (k L : ℕ)
    (target source : Jacobi.Index k L)
    (h : source.val + 1 = target.val)
    (x : Euclidean n) (hx : ‖x‖ = 1)
    (u : CertificateFibre n k) :
    (lowerAdjacentChannel hn k L target source h).toLinearMap.adjoint
        (harmonicDegreeAxisTensor n k L target x
          (harmonicDegreeFibre hn k L target x u)) =
      Real.sqrt (Gegenbauer.betaSq n k (k + target.val)) •
        harmonicDegreeFibre hn k L source x u := by
  let p := sourceTangentPolynomial hn k x hx u
  rw [harmonicDegreeFibre_apply_eq hn k L target x hx u,
    ← coordinateDegreeTransport_axis hn k L target x]
  rw [harmonicDegreeFibre_apply_eq hn k L source x hx u]
  change
    ((coordinateDegreeTransport hn k L target).comp
      (((coordinateHarmonicDegreeCast n
        ((k + source.val) + 1) (k + target.val)
          (by omega)).comp
        (lowerChannelIsometry hn (k + source.val))).comp
          (harmonicDegreeEuclideanEquiv n k L
            (by omega) source).symm.toLinearIsometry)).toLinearMap.adjoint
        (coordinateDegreeTransport hn k L target
          (HarmonicSourceProjection.harmonicAxisTensor
            n (k + target.val) x
            (solidHarmonicAxisPolynomialIsometry
              hn k target.val x hx p))) =
      Real.sqrt (Gegenbauer.betaSq n k (k + target.val)) •
        harmonicDegreeEuclideanEquiv n k L (by omega) source
          (solidHarmonicAxisPolynomialIsometry
            hn k source.val x hx p)
  rw [transportedIsometry_adjoint]
  change
    harmonicDegreeEuclideanEquiv n k L (by omega) source
      (((coordinateHarmonicDegreeCast n
          ((k + source.val) + 1) (k + target.val)
            (by omega)).toLinearMap.comp
        (lowerChannelIsometry hn
          (k + source.val)).toLinearMap).adjoint
        (HarmonicSourceProjection.harmonicAxisTensor
          n (k + target.val) x
          (solidHarmonicAxisPolynomialIsometry
            hn k target.val x hx p))) = _
  rw [LinearMap.adjoint_comp]
  change
    harmonicDegreeEuclideanEquiv n k L (by omega) source
      ((lowerChannelIsometry hn (k + source.val)).toLinearMap.adjoint
        ((coordinateHarmonicDegreeCast n
          ((k + source.val) + 1) (k + target.val)
            (by omega)).toLinearMap.adjoint
          (HarmonicSourceProjection.harmonicAxisTensor
            n (k + target.val) x
            (solidHarmonicAxisPolynomialIsometry
              hn k target.val x hx p)))) = _
  rw [coordinateHarmonicDegreeCast_adjoint_apply,
    coordinateHarmonicDegreeCast_axis]
  have hpoly :
      harmonicDegreeCast n (k + target.val)
        ((k + source.val) + 1) (by omega)
        (solidHarmonicAxisPolynomialIsometry
          hn k target.val x hx p) =
        solidHarmonicAxisPolynomialIsometry
          hn k (source.val + 1) x hx p := by
    apply Subtype.ext
    change
      (solidHarmonicAxisPolynomialIsometry
        hn k target.val x hx p : MvPolynomial (Fin n) ℝ) =
      (solidHarmonicAxisPolynomialIsometry
        hn k (source.val + 1) x hx p : MvPolynomial (Fin n) ℝ)
    rw [h]
  rw [hpoly]
  change
    harmonicDegreeEuclideanEquiv n k L (by omega) source
      ((lowerChannelIsometry hn (k + source.val)).toLinearMap.adjoint
        (HarmonicSourceProjection.solidHarmonicSource
          hn k (source.val + 1) x hx p)) = _
  rw [HarmonicSourceProjection.lowerChannelIsometry_adjoint_solidHarmonicSource
    hn k source.val x hx p]
  rw [map_smul, h]

theorem adjacentChannel_axis_projection
    {n : ℕ} (hn : 3 ≤ n) (k L : ℕ)
    (x : Euclidean n) (hx : x ∈ unitSphere n)
    (target source : Jacobi.Index k L)
    (u : CertificateFibre n k) :
    (adjacentChannel hn k L target source).adjoint
        (harmonicDegreeAxisTensor n k L target x
          (harmonicDegreeFibre hn k L target x u)) =
      Real.sqrt
          (SourceJacobiWeights.sourceChannelCoefficient
            n k L source target) •
        harmonicDegreeFibre hn k L source x u := by
  change ‖x‖ = 1 at hx
  by_cases hupper : target.val + 1 = source.val
  · have hcoefficient :
        SourceJacobiWeights.sourceChannelCoefficient
          n k L source target =
          Gegenbauer.alphaSq n k (k + target.val) := by
      simp only [SourceJacobiWeights.sourceChannelCoefficient, hupper, ↓reduceIte]
    rw [hcoefficient]
    have hadjacent :
        adjacentChannel hn k L target source =
          (upperAdjacentChannel hn k L target source hupper).toLinearMap := by
      simp only [adjacentChannel, dite_eq_left hupper]
    rw [hadjacent]
    exact upperAdjacentChannel_axis_projection
      hn k L target source hupper x hx u
  · by_cases hlower : source.val + 1 = target.val
    · have hcoefficient :
          SourceJacobiWeights.sourceChannelCoefficient
            n k L source target =
            Gegenbauer.betaSq n k (k + target.val) := by
        simp only [SourceJacobiWeights.sourceChannelCoefficient, hupper, ↓reduceIte, hlower]
      rw [hcoefficient]
      have hadjacent :
          adjacentChannel hn k L target source =
            (lowerAdjacentChannel hn k L target source hlower).toLinearMap := by
        simp only [adjacentChannel, dite_eq_right hupper, dite_eq_left hlower]
      rw [hadjacent]
      exact lowerAdjacentChannel_axis_projection
        hn k L target source hlower x hx u
    · simp only [adjacentChannel, hupper, ↓reduceDIte, hlower, map_zero, LinearMap.zero_apply,
        SourceJacobiWeights.sourceChannelCoefficient, ↓reduceIte, Real.sqrt_zero, zero_smul]

/-- The actual source adjacent channel data used in the spherical-code argument. -/
def actualSourceAdjacentChannelData
    {n : ℕ} (hn : 3 ≤ n) (k L : ℕ) :
    SourceAdjacentChannelData n k L (harmonicDegreeFibre hn k L) where
  channel := adjacentChannel hn k L
  channel_inner := by
    intro target source hnonzero u v
    exact adjacentChannel_inner hn k L target source hnonzero u v
  channel_zero := by
    intro target source hzero
    exact adjacentChannel_zero hn k L target source hzero
  channel_orthogonal := by
    intro target source₁ source₂ hne u v
    exact adjacentChannel_orthogonal
      hn k L target source₁ source₂ hne u v
  axis_projection := by
    intro x hx target source u
    exact adjacentChannel_axis_projection
      hn k L x hx target source u

end HarmonicAdjacentChannelTransport

end

end SpherePacking

end MetricCodesNoncomputable
