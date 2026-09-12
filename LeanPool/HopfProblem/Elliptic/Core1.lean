/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Lattice.Core2
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.PeriodFamily.HolomorphicPeriodMap1
import all LeanPool.HopfProblem.Lattice.Core2

/-!
# Hopf problem: elliptic · core 1

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-- The two elliptic fibre types, distinguished by monodromy order three or four. -/
public
inductive Elliptic.Kind where
  | three
  | four
  deriving DecidableEq

private instance Elliptic.instLocal1 : Fintype Kind :=
  ⟨{.three, .four}, by intro j; cases j <;> simp⟩

private def Elliptic.Kind.order : Elliptic.Kind → ℕ
  | .three => 3
  | .four => 4

private def Elliptic.Kind.matrix : Elliptic.Kind → LatticeMatrix
  | .three => A₁
  | .four => A₂

private def Elliptic.Kind.twist : Elliptic.Kind → Lattice
  | .three => ε
  | .four => -ε'

private theorem Elliptic.Kind.order_pos (j : Elliptic.Kind) : 0 < j.order := by cases j <;> decide

private theorem Elliptic.Kind.matrix_pow_order (j : Elliptic.Kind) : j.matrix ^ j.order = 1 := by
  cases j <;> decide

private theorem
    Elliptic.Kind.matrix_fixes_twist (j : Elliptic.Kind) : j.matrix *ᵥ j.twist = j.twist := by
  cases j <;> decide

private def Elliptic.realCast (v : Lattice) : RealPlane₄ := fun i => (v i : ℝ)

private def Elliptic.flatLinear (j : Kind) : RealPlane₄ →ₗ[ℝ] RealPlane₄ :=
  (j.matrix.map (Int.castRingHom ℝ)).mulVecLin

private def Elliptic.flatAffine (j : Kind) (v : Lattice) (x : RealPlane₄) : RealPlane₄ :=
  flatLinear j x + (1 / (j.order : ℝ)) • realCast v

private def Elliptic.FlatCongruent (x y : RealPlane₄) : Prop :=
  ∃ v : Lattice, x - y = realCast v

private def Elliptic.AdmissibleTwist (j : Kind) (v : Lattice) : Prop :=
  j.matrix *ᵥ v = v ∧ if j = .three then ¬3 ∣ γ v else Odd (γ v)

private theorem Elliptic.mainTwist_admissible (j : Kind) : AdmissibleTwist j j.twist := by
  refine ⟨j.matrix_fixes_twist, ?_⟩
  cases j <;> norm_num [Kind.twist, γ, ε, ε']

private def Elliptic.periodEquiv (p : PeriodDomain) : RealPlane₄ ≃L[ℝ] ComplexPlane₂ :=
  p.basis.equivFun.symm.toContinuousLinearEquiv

private theorem Elliptic.periodEquiv_apply (p : PeriodDomain) (x : RealPlane₄) :
    periodEquiv p x = ∑ i, x i • p.basis i :=
  p.basis.equivFun_symm_apply x

private theorem Elliptic.periodEquiv_matrix (p : PeriodDomain) (x : RealPlane₄) :
    periodEquiv p x = p.val.matrix *ᵥ (fun i => (x i : ℂ)) := by
  rw [periodEquiv_apply]
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, PeriodDomain.basis_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro k _
  change (x k : ℂ) * p.val.matrix i k = p.val.matrix i k * (x k : ℂ)
  exact mul_comm _ _

private theorem Elliptic.periodEquiv_realCast (p : PeriodDomain) (v : Lattice) :
    periodEquiv p (realCast v) = ∑ i, v i • p.basis i := by
  rw [periodEquiv_apply]
  simp only [realCast, Int.cast_smul_eq_zsmul]

private theorem Elliptic.periodEquiv_mem_lattice_iff (p : PeriodDomain) (x : RealPlane₄) :
    periodEquiv p x ∈ p.lattice ↔ ∃ v : Lattice, x = realCast v := by
  rw [p.lattice_eq_span_basis, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, (periodEquiv p).injective ?_⟩
    rw [periodEquiv_realCast]
    exact hv.symm
  · rintro ⟨v, rfl⟩
    exact ⟨v, (periodEquiv_realCast p v).symm⟩

private def Elliptic.flatProjection (p : PeriodDomain) (x : RealPlane₄) : p.Torus :=
  p.lattice.mkQ (periodEquiv p x)

private theorem
    Elliptic.flatProjection_continuous (p : PeriodDomain) : Continuous (flatProjection p) :=
  p.lattice.continuous_mkQ.comp (periodEquiv p).continuous

private theorem Elliptic.flatProjection_surjective (p : PeriodDomain) :
    Function.Surjective (flatProjection p) :=
  p.lattice.mkQ_surjective.comp (periodEquiv p).surjective

private theorem Elliptic.flatProjection_eq_iff (p : PeriodDomain) (x y : RealPlane₄) :
    flatProjection p x = flatProjection p y ↔ FlatCongruent x y := by
  change
    (Submodule.Quotient.mk (periodEquiv p x) : p.Torus) =
        Submodule.Quotient.mk (periodEquiv p y) ↔
      _
  rw [Submodule.Quotient.eq, ← map_sub, periodEquiv_mem_lattice_iff]
  rfl

@[simp]
private theorem Elliptic.flatProjection_add (p : PeriodDomain) (x y : RealPlane₄) :
    flatProjection p (x + y) = flatProjection p x + flatProjection p y := by
  simp only [flatProjection, map_add]

@[simp]
private theorem Elliptic.flatProjection_realCast (p : PeriodDomain) (v : Lattice) :
    flatProjection p (realCast v) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero p.lattice).mpr
  exact (periodEquiv_mem_lattice_iff p _).mpr ⟨v, rfl⟩

private theorem Elliptic.flatLinear_realCast (j : Kind) (v : Lattice) :
    flatLinear j (realCast v) = realCast (j.matrix *ᵥ v) := by
  ext i
  exact (RingHom.map_mulVec (Int.castRingHom ℝ) j.matrix v i).symm

private theorem
    Elliptic.flatLinear_fixes_realCast (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    flatLinear j (realCast v) = realCast v := by rw [flatLinear_realCast, hv]

private theorem
    Elliptic.flatAffine_iterate (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v) (r : ℕ)
    (x : RealPlane₄) :
    (flatAffine j v)^[r] x =
      (j.matrix.map (Int.castRingHom ℝ)) ^ r *ᵥ x + ((r : ℝ) / (j.order : ℝ)) • realCast v := by
  induction r with
  | zero => simp
  | succ r
    ih =>
    rw [Function.iterate_succ_apply', ih, flatAffine, map_add, map_smul,
      flatLinear_fixes_realCast j v hv]
    have hlin :
      flatLinear j ((j.matrix.map (Int.castRingHom ℝ)) ^ r *ᵥ x) =
        (j.matrix.map (Int.castRingHom ℝ)) ^ (r + 1) *ᵥ x := by
      simp only [flatLinear, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, pow_succ']
    rw [hlin, add_assoc, ← add_smul]
    congr 2
    push_cast
    ring

private theorem Elliptic.flatAffine_iterate_order (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (x : RealPlane₄) : (flatAffine j v)^[j.order] x = x + realCast v := by
  rw [flatAffine_iterate j v hv, ← Matrix.map_pow, j.matrix_pow_order]
  have hm : (j.order : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt j.order_pos)
  simp [hm]

private theorem Elliptic.flatAffine_iterate_order_congruent (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (x : RealPlane₄) :
    FlatCongruent ((flatAffine j v)^[j.order] x) x := by
  refine ⟨v, ?_⟩
  rw [flatAffine_iterate_order j v hv]
  abel

@[simp]
private theorem
    Elliptic.flatLinear_gamma (j : Kind) (x : RealPlane₄) : flatLinear j x 0 = x 0 := by
  cases j <;> simp [flatLinear, Kind.matrix, A₁, A₂, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private theorem
    Elliptic.flatAffine_iterate_gamma (j : Kind) (v : Lattice) (r : ℕ) (x : RealPlane₄) :
    (flatAffine j v)^[r] x 0 = x 0 + ((r : ℝ) / (j.order : ℝ)) * (γ v : ℝ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    change flatLinear j ((flatAffine j v)^[r] x) 0 + (1 / (j.order : ℝ)) * (γ v : ℝ) = _
    rw [flatLinear_gamma, ih]
    push_cast
    ring

private theorem Elliptic.flatAffine_iterate_not_congruent (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (r : ℕ) (hr : 0 < r) (hrm : r < j.order) (x : RealPlane₄) :
    ¬FlatCongruent ((flatAffine j v)^[r] x) x := by
  rintro ⟨w, hw⟩
  have hgamma := congrFun hw 0
  change (flatAffine j v)^[r] x 0 - x 0 = (w 0 : ℝ) at hgamma
  rw [flatAffine_iterate_gamma] at hgamma
  have hm : (j.order : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt j.order_pos)
  have hreal : (r : ℝ) * (γ v : ℝ) = (j.order : ℝ) * (w 0 : ℝ) := by
    field_simp at hgamma
    nlinarith
  have hint : (r : ℤ) * γ v = (j.order : ℤ) * w 0 := by exact_mod_cast hreal
  cases j with
  | three =>
    have ha : ¬3 ∣ γ v := by simpa [AdmissibleTwist] using hv.2
    change r < 3 at hrm
    change (r : ℤ) * γ v = 3 * w 0 at hint
    interval_cases r <;> norm_num at hint <;> omega
  | four =>
    have ha : Odd (γ v) := by simpa [AdmissibleTwist] using hv.2
    rcases ha with ⟨a, ha⟩
    change r < 4 at hrm
    change (r : ℤ) * γ v = 4 * w 0 at hint
    interval_cases r <;> norm_num at hint <;> omega

private theorem Elliptic.bad_three_twist_has_fixed_point (v : Lattice) (hv : A₁ *ᵥ v = v)
    (ha : (3 : ℤ) ∣ γ v) : ∃ x : RealPlane₄, FlatCongruent (flatAffine .three v x) x := by
  obtain ⟨h₁, h₂⟩ := (A₁_fixed_iff v).mp hv
  obtain ⟨m, hm⟩ := ha
  have hm' : (v 0 : ℝ) = 3 * (m : ℝ) := by exact_mod_cast hm
  refine ⟨![0, -(v 3 : ℝ) / 3, -((v 3 : ℝ) + 2 * (v 0 : ℝ)) / 3, 0], ![m, 0, v 3, 0], ?_⟩
  ext i
  fin_cases i <;>
      simp [flatAffine, flatLinear, Kind.matrix, Kind.order, A₁, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ, realCast, h₁, h₂, hm'] <;>
    ring

private theorem Elliptic.bad_four_twist_has_square_fixed_point (v : Lattice) (hv : A₂ *ᵥ v = v)
    (ha : Even (γ v)) : ∃ x : RealPlane₄, FlatCongruent ((flatAffine .four v)^[2] x) x := by
  obtain ⟨h₁, h₂⟩ := (A₂_fixed_iff v).mp hv
  obtain ⟨m, hm⟩ := ha
  have hm' : (v 0 : ℝ) = 2 * (m : ℝ) := by
    change v 0 = m + m at hm
    exact_mod_cast (show v 0 = 2 * m by omega)
  refine ⟨![0, 3 * (v 0 : ℝ) / 4, -3 * (v 0 : ℝ) / 4 - (v 3 : ℝ) / 2, 0], ![m, 0, v 3, 0], ?_⟩
  ext i
  fin_cases i <;>
      simp [Function.iterate_succ_apply, flatAffine, flatLinear, Kind.matrix, Kind.order, A₂,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ, realCast, h₁, h₂, hm'] <;>
    ring

private theorem Elliptic.flatAffine_free_iff (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    (∀ r : ℕ,
        0 < r → r < j.order → ∀ x : RealPlane₄, ¬FlatCongruent ((flatAffine j v)^[r] x) x) ↔
      AdmissibleTwist j v := by
  constructor
  · intro hfree
    refine ⟨hv, ?_⟩
    cases j with
    | three =>
      change ¬3 ∣ γ v
      intro ha
      obtain ⟨x, hx⟩ := bad_three_twist_has_fixed_point v hv ha
      exact hfree 1 (by decide) (by decide) x (by simpa using hx)
    | four =>
      change Odd (γ v)
      apply Int.not_even_iff_odd.mp
      intro ha
      obtain ⟨x, hx⟩ := bad_four_twist_has_square_fixed_point v hv ha
      exact hfree 2 (by decide) (by decide) x hx
  · intro ha r hr hrm x
    exact flatAffine_iterate_not_congruent j v ha r hr hrm x

private def Elliptic.periodStep (j : Kind) (p : PeriodDomain) : PeriodDomain :=
  match j with
  | .three => p.step₁
  | .four => p.step₂

private abbrev Elliptic.FixedPeriod (j : Kind) :=
  { p : PeriodDomain // periodStep j p = p }

private def Elliptic.examplePeriodPoint : Kind → PeriodPoint
  | .three =>
    ⟨(1 + Complex.I * (Real.sqrt 3 : ℂ)) / 2, (1 : ℂ) / 2 - Complex.I * (Real.sqrt 3 : ℂ) / 6,
      -Complex.I⟩
  | .four => ⟨Complex.I, (1 - Complex.I) / 2, -Complex.I⟩

private theorem
    Elliptic.examplePeriodPoint_tau_im_pos (j : Kind) : 0 < (examplePeriodPoint j).τ.im := by
  cases j
  · simp only [examplePeriodPoint, Complex.div_ofNat_im, Complex.add_im, Complex.one_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      MulZeroClass.zero_mul, one_mul, zero_add]
    positivity
  · norm_num [examplePeriodPoint]

@[simp]
private theorem
    Elliptic.examplePeriodPoint_beta_im (j : Kind) : (examplePeriodPoint j).β.im = -1 := by
  cases j <;> norm_num [examplePeriodPoint]

private theorem
    Elliptic.examplePeriodPoint_admissible (j : Kind) : (examplePeriodPoint j).Admissible := by
  refine ⟨examplePeriodPoint_tau_im_pos j, ?_⟩
  have hn : 0 ≤ 6 * (examplePeriodPoint j).μ.im ^ 2 / (examplePeriodPoint j).τ.im :=
    div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (examplePeriodPoint_tau_im_pos j).le
  rw [PeriodPoint.discriminant, examplePeriodPoint_beta_im]
  linarith

private def Elliptic.examplePeriod (j : Kind) : PeriodDomain :=
  ⟨examplePeriodPoint j, examplePeriodPoint_admissible j⟩

private theorem Elliptic.examplePeriodPoint_three_fixed :
    (examplePeriodPoint .three).step₁ = examplePeriodPoint .three := by
  have hs : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have ht : 1 + Complex.I * (Real.sqrt 3 : ℂ) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    norm_num at h'
  apply PeriodPoint.ext <;> dsimp [examplePeriodPoint, PeriodPoint.step₁] <;> field_simp [ht] <;>
        ring_nf <;>
      simp [Complex.I_sq, hs] <;>
    ring

private theorem Elliptic.examplePeriodPoint_four_fixed :
    (examplePeriodPoint .four).step₂ = examplePeriodPoint .four := by
  apply PeriodPoint.ext <;> apply Complex.ext <;>
    norm_num [examplePeriodPoint, PeriodPoint.step₂, Complex.div_re, Complex.div_im,
      Complex.mul_re, Complex.mul_im, Complex.normSq_apply, pow_two]

private theorem Elliptic.examplePeriod_fixed (j : Kind) :
    periodStep j (examplePeriod j) = examplePeriod j := by
  cases j
  · exact Subtype.ext examplePeriodPoint_three_fixed
  · exact Subtype.ext examplePeriodPoint_four_fixed

private def Elliptic.exampleFixedPeriod (j : Kind) : FixedPeriod j :=
  ⟨examplePeriod j, examplePeriod_fixed j⟩

private def Elliptic.linearMatrix (j : Kind) (p : PeriodDomain) : Matrix (Fin 2) (Fin 2) ℂ :=
  match j with
  | .three => p.val.R₁
  | .four => p.val.R₂

private def
    Elliptic.linearEquiv (j : Kind) (p : FixedPeriod j) : ComplexPlane₂ ≃L[ℂ] ComplexPlane₂ :=
  match j with
  | .three => p.val.R₁Equiv
  | .four => p.val.R₂Equiv

private theorem Elliptic.linearEquiv_apply (j : Kind) (p : FixedPeriod j) (z : ComplexPlane₂) :
    linearEquiv j p z = linearMatrix j p.val *ᵥ z := by
  cases j
  · exact p.val.R₁Equiv_apply z
  · exact p.val.R₂Equiv_apply z

private theorem Elliptic.linearEquiv_map_lattice (j : Kind) (p : FixedPeriod j) :
    p.val.lattice.map ((linearEquiv j p).toLinearEquiv.restrictScalars ℤ).toLinearMap =
      p.val.lattice := by
  cases j
  · exact p.val.R₁Equiv_map_lattice.trans (congrArg PeriodDomain.lattice p.property)
  · exact p.val.R₂Equiv_map_lattice.trans (congrArg PeriodDomain.lattice p.property)

private theorem Elliptic.linearMatrix_period_matrix (j : Kind) (p : FixedPeriod j) :
    linearMatrix j p.val * p.val.val.matrix =
      p.val.val.matrix * j.matrix.map (Int.castRingHom ℂ) := by
  cases j
  · have hp : p.val.val.step₁ = p.val.val := congrArg Subtype.val p.property
    have hm := p.val.val.step₁_matrix (p.val.val.τ_ne_zero p.val.property.1)
    rw [hp] at hm
    have hTA : (T₁.map (Int.castRingHom ℂ)).transpose * A₁.map (Int.castRingHom ℂ) = 1 := by
      have h : T₁.transpose * A₁ = 1 := by decide
      simpa only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_one, map_zero, map_one] using
        congrArg (fun A : LatticeMatrix => A.map (Int.castRingHom ℂ)) h
    simpa only [linearMatrix, Kind.matrix, Matrix.mul_assoc, hTA, Matrix.mul_one] using
      (congrArg (fun A => A * A₁.map (Int.castRingHom ℂ)) hm).symm
  · have hp : p.val.val.step₂ = p.val.val := congrArg Subtype.val p.property
    have hm := p.val.val.step₂_matrix (p.val.val.τ_ne_zero p.val.property.1)
    rw [hp] at hm
    have hTA : (T₂.map (Int.castRingHom ℂ)).transpose * A₂.map (Int.castRingHom ℂ) = 1 := by
      have h : T₂.transpose * A₂ = 1 := by decide
      simpa only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_one, map_zero, map_one] using
        congrArg (fun A : LatticeMatrix => A.map (Int.castRingHom ℂ)) h
    simpa only [linearMatrix, Kind.matrix, Matrix.mul_assoc, hTA, Matrix.mul_one] using
      (congrArg (fun A => A * A₂.map (Int.castRingHom ℂ)) hm).symm

private theorem Elliptic.flatLinear_complexCast (j : Kind) (x : RealPlane₄) :
    (fun i => ((flatLinear j x) i : ℂ)) =
      (j.matrix.map (Int.castRingHom ℂ)) *ᵥ (fun i => (x i : ℂ)) := by
  ext i
  simp [flatLinear, Matrix.mulVec, dotProduct]

private theorem
    Elliptic.linearEquiv_periodEquiv (j : Kind) (p : FixedPeriod j) (x : RealPlane₄) :
    linearEquiv j p (periodEquiv p.val x) = periodEquiv p.val (flatLinear j x) := by
  rw [linearEquiv_apply, periodEquiv_matrix, periodEquiv_matrix, flatLinear_complexCast,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, linearMatrix_period_matrix]

private def Elliptic.linearBiholomorph (j : Kind) (p : FixedPeriod j) :
    Diffeomorph (modelWithCornersSelf ℂ ComplexPlane₂) (modelWithCornersSelf ℂ ComplexPlane₂)
      p.val.Torus p.val.Torus ω :=
  DiscreteQuotient.linearBiholomorph p.val.lattice p.val.lattice (linearEquiv j p)
    (linearEquiv_map_lattice j p)

private theorem Elliptic.linearBiholomorph_mkQ (j : Kind) (p : FixedPeriod j) (z : ComplexPlane₂) :
    linearBiholomorph j p (p.val.lattice.mkQ z) = p.val.lattice.mkQ (linearEquiv j p z) :=
  rfl

private theorem Elliptic.linearBiholomorph_flatProjection (j : Kind) (p : FixedPeriod j)
    (x : RealPlane₄) :
    linearBiholomorph j p (flatProjection p.val x) = flatProjection p.val (flatLinear j x) := by
  change linearBiholomorph j p (p.val.lattice.mkQ (periodEquiv p.val x)) = _
  rw [linearBiholomorph_mkQ, linearEquiv_periodEquiv]
  rfl

private def Elliptic.torusTranslation (p : PeriodDomain) (a : p.Torus) :
    Diffeomorph (modelWithCornersSelf ℂ ComplexPlane₂) (modelWithCornersSelf ℂ ComplexPlane₂)
      p.Torus p.Torus ω
    where
  toFun x := x + a
  invFun x := x - a
  left_inv x := add_sub_cancel_right x a
  right_inv x := sub_add_cancel x a
  contMDiff_toFun := contMDiff_id.add contMDiff_const
  contMDiff_invFun := contMDiff_id.sub contMDiff_const

private def Elliptic.affineBiholomorph (j : Kind) (p : FixedPeriod j) (v : Lattice) :
    Diffeomorph (modelWithCornersSelf ℂ ComplexPlane₂) (modelWithCornersSelf ℂ ComplexPlane₂)
      p.val.Torus p.val.Torus ω :=
  (linearBiholomorph j p).trans
    (torusTranslation p.val (flatProjection p.val ((1 / (j.order : ℝ)) • realCast v)))

private theorem Elliptic.affineBiholomorph_apply (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (x : p.val.Torus) :
    affineBiholomorph j p v x =
      linearBiholomorph j p x + flatProjection p.val ((1 / (j.order : ℝ)) • realCast v) :=
  rfl

private theorem
    Elliptic.affineBiholomorph_flatProjection (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (x : RealPlane₄) :
    affineBiholomorph j p v (flatProjection p.val x) = flatProjection p.val (flatAffine j v x) := by
  rw [affineBiholomorph_apply, linearBiholomorph_flatProjection, flatAffine, flatProjection_add]

private theorem Elliptic.affineBiholomorph_iterate_flatProjection (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (r : ℕ) (x : RealPlane₄) :
    (affineBiholomorph j p v)^[r] (flatProjection p.val x) =
      flatProjection p.val ((flatAffine j v)^[r] x) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      affineBiholomorph_flatProjection]

private def Elliptic.affinePermutation (j : Kind) (p : FixedPeriod j) (v : Lattice) :
    Equiv.Perm p.val.Torus :=
  (affineBiholomorph j p v).toEquiv

private theorem
    Elliptic.affinePermutation_pow_flatProjection (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (r : ℕ) (x : RealPlane₄) :
    (affinePermutation j p v ^ r) (flatProjection p.val x) =
      flatProjection p.val ((flatAffine j v)^[r] x) := by
  rw [Equiv.Perm.coe_pow]
  exact affineBiholomorph_iterate_flatProjection j p v r x

private theorem Elliptic.affinePermutation_pow_order (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) : affinePermutation j p v ^ j.order = 1 := by
  apply Equiv.ext
  intro y
  obtain ⟨x, rfl⟩ := flatProjection_surjective p.val y
  change (affinePermutation j p v ^ j.order) (flatProjection p.val x) = flatProjection p.val x
  rw [affinePermutation_pow_flatProjection]
  exact (flatProjection_eq_iff p.val _ _).mpr (flatAffine_iterate_order_congruent j v hv x)

private theorem Elliptic.affinePermutation_pow_ne (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (r : ℕ) (hr : 0 < r) (hrm : r < j.order) (y : p.val.Torus) :
    (affinePermutation j p v ^ r) y ≠ y := by
  obtain ⟨x, rfl⟩ := flatProjection_surjective p.val y
  rw [affinePermutation_pow_flatProjection]
  exact fun h =>
    flatAffine_iterate_not_congruent j v hv r hr hrm x ((flatProjection_eq_iff p.val _ _).mp h)

private theorem Elliptic.affinePermutation_free_iff (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) :
    (∀ r, 0 < r → r < j.order → ∀ y : p.val.Torus, (affinePermutation j p v ^ r) y ≠ y) ↔
      AdmissibleTwist j v := by
  constructor
  · intro h
    apply (flatAffine_free_iff j v hv).mp
    intro r hr hrm x hx
    apply h r hr hrm (flatProjection p.val x)
    rw [affinePermutation_pow_flatProjection]
    exact (flatProjection_eq_iff p.val _ _).mpr hx
  · intro ha
    exact affinePermutation_pow_ne j p v ha

private theorem Elliptic.sum_zsmul_basisFun_mo1973_9836 (v : Lattice) :
    (∑ i, v i • Pi.basisFun ℝ (Fin 4) i) = realCast v := by
  ext k
  simp [Pi.basisFun_apply, realCast, Pi.single_apply]

private theorem Elliptic.standardLattice_mem_iff (x : RealPlane₄) :
    x ∈ standardLattice ↔ ∃ v : Lattice, x = realCast v := by
  rw [standardLattice, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, hv.symm.trans (sum_zsmul_basisFun_mo1973_9836 v)⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v, sum_zsmul_basisFun_mo1973_9836 v⟩

private theorem Elliptic.flatTorus_mkQ_eq_iff (x y : RealPlane₄) :
    standardLattice.mkQ x = standardLattice.mkQ y ↔ FlatCongruent x y := by
  change (Submodule.Quotient.mk x : RealTorus₄) = Submodule.Quotient.mk y ↔ _
  rw [Submodule.Quotient.eq, standardLattice_mem_iff]
  rfl

private theorem Elliptic.periodEquiv_map_standardLattice (p : PeriodDomain) :
    standardLattice.map ((periodEquiv p).toLinearEquiv.restrictScalars ℤ).toLinearMap =
      p.lattice := by
  ext z
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (periodEquiv_mem_lattice_iff p x).mpr ((standardLattice_mem_iff x).mp hx)
  · intro hz
    refine ⟨(periodEquiv p).symm z, ?_, (periodEquiv p).apply_symm_apply z⟩
    apply (standardLattice_mem_iff _).mpr
    apply (periodEquiv_mem_lattice_iff p _).mp
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hz

private def Elliptic.flatTorusPeriodHomeomorph (p : PeriodDomain) : RealTorus₄ ≃ₜ p.Torus
    where
  toEquiv :=
    (Submodule.Quotient.equiv standardLattice p.lattice
        ((periodEquiv p).toLinearEquiv.restrictScalars ℤ)
        (periodEquiv_map_standardLattice p)).toEquiv
  continuous_toFun := by
    apply standardLattice.isQuotientMap_mkQ.continuous_iff.mpr
    exact p.lattice.continuous_mkQ.comp (periodEquiv p).continuous
  continuous_invFun := by
    apply p.lattice.isQuotientMap_mkQ.continuous_iff.mpr
    exact standardLattice.continuous_mkQ.comp (periodEquiv p).symm.continuous

private theorem Elliptic.flatTorusPeriodHomeomorph_mkQ (p : PeriodDomain) (x : RealPlane₄) :
    flatTorusPeriodHomeomorph p (standardLattice.mkQ x) = flatProjection p x :=
  rfl

@[simp]
private theorem Elliptic.flatTorusPeriodHomeomorph_symm_flatProjection (p : PeriodDomain)
    (x : RealPlane₄) :
    (flatTorusPeriodHomeomorph p).symm (flatProjection p x) = standardLattice.mkQ x := by
  rw [← flatTorusPeriodHomeomorph_mkQ, Homeomorph.symm_apply_apply]

private def Elliptic.flatTorusAffine (j : Kind) (v : Lattice) : RealTorus₄ ≃ₜ RealTorus₄ :=
  ((flatTorusPeriodHomeomorph (exampleFixedPeriod j).val).trans
        (affineBiholomorph j (exampleFixedPeriod j) v).toHomeomorph).trans
    (flatTorusPeriodHomeomorph (exampleFixedPeriod j).val).symm

private theorem Elliptic.flatTorusAffine_mkQ (j : Kind) (v : Lattice) (x : RealPlane₄) :
    flatTorusAffine j v (standardLattice.mkQ x) = standardLattice.mkQ (flatAffine j v x) := by
  change
    (flatTorusPeriodHomeomorph (exampleFixedPeriod j).val).symm
        (affineBiholomorph j (exampleFixedPeriod j) v
          (flatTorusPeriodHomeomorph (exampleFixedPeriod j).val (standardLattice.mkQ x))) =
      _
  rw [flatTorusPeriodHomeomorph_mkQ, affineBiholomorph_flatProjection,
    flatTorusPeriodHomeomorph_symm_flatProjection]

private theorem
    Elliptic.flatTorusAffine_periodHomeomorph (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (y : RealTorus₄) :
    flatTorusPeriodHomeomorph p.val (flatTorusAffine j v y) =
      affineBiholomorph j p v (flatTorusPeriodHomeomorph p.val y) := by
  obtain ⟨x, rfl⟩ := standardLattice.mkQ_surjective y
  rw [flatTorusAffine_mkQ, flatTorusPeriodHomeomorph_mkQ, flatTorusPeriodHomeomorph_mkQ,
    affineBiholomorph_flatProjection]

private theorem Elliptic.flatTorusAffine_iterate_mkQ (j : Kind) (v : Lattice) (r : ℕ)
    (x : RealPlane₄) :
    (flatTorusAffine j v)^[r] (standardLattice.mkQ x) =
      standardLattice.mkQ ((flatAffine j v)^[r] x) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, flatTorusAffine_mkQ]

private theorem
    Elliptic.flatTorusAffine_iterate_order (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (y : RealTorus₄) : (flatTorusAffine j v)^[j.order] y = y := by
  obtain ⟨x, rfl⟩ := standardLattice.mkQ_surjective y
  rw [flatTorusAffine_iterate_mkQ]
  exact (flatTorus_mkQ_eq_iff _ _).mpr (flatAffine_iterate_order_congruent j v hv x)

private theorem
    Elliptic.flatTorusAffine_iterate_ne (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (r : ℕ) (hr : 0 < r) (hrm : r < j.order) (y : RealTorus₄) : (flatTorusAffine j v)^[r] y ≠ y :=
  by
  obtain ⟨x, rfl⟩ := standardLattice.mkQ_surjective y
  rw [flatTorusAffine_iterate_mkQ]
  exact fun h =>
    flatAffine_iterate_not_congruent j v hv r hr hrm x ((flatTorus_mkQ_eq_iff _ _).mp h)

private def Elliptic.flatTorusPermutation (j : Kind) (v : Lattice) : Equiv.Perm RealTorus₄ :=
  (flatTorusAffine j v).toEquiv

private theorem Elliptic.flatTorusPermutation_pow_mkQ (j : Kind) (v : Lattice) (r : ℕ)
    (x : RealPlane₄) :
    (flatTorusPermutation j v ^ r) (standardLattice.mkQ x) =
      standardLattice.mkQ ((flatAffine j v)^[r] x) := by
  rw [Equiv.Perm.coe_pow]
  exact flatTorusAffine_iterate_mkQ j v r x

private theorem Elliptic.flatTorusPermutation_pow_order (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) : flatTorusPermutation j v ^ j.order = 1 := by
  apply Equiv.ext
  intro y
  rw [Equiv.Perm.coe_pow]
  exact flatTorusAffine_iterate_order j v hv y

private theorem
    Elliptic.flatTorusPermutation_pow_ne (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (r : ℕ) (hr : 0 < r) (hrm : r < j.order) (y : RealTorus₄) :
    (flatTorusPermutation j v ^ r) y ≠ y := by
  rw [Equiv.Perm.coe_pow]
  exact flatTorusAffine_iterate_ne j v hv r hr hrm y

private theorem
    Elliptic.flatTorusPermutation_free_iff (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    (∀ r : ℕ, 0 < r → r < j.order → ∀ y : RealTorus₄, (flatTorusPermutation j v ^ r) y ≠ y) ↔
      AdmissibleTwist j v := by
  constructor
  · intro h
    apply (flatAffine_free_iff j v hv).mp
    intro r hr hrm x hx
    apply h r hr hrm (standardLattice.mkQ x)
    rw [flatTorusPermutation_pow_mkQ]
    exact (flatTorus_mkQ_eq_iff _ _).mpr hx
  · intro ha
    exact flatTorusPermutation_pow_ne j v ha

end Mathoverflow1973

end
