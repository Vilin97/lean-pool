/-
Copyright (c) 2026 jayyswan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jayyswan
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Layer 0 of the Hasse–Minkowski development

Mathlib 4.33 has the abstract theory of quadratic maps: `QuadraticMap.Anisotropic`,
`QuadraticMap.Nondegenerate`, `weightedSumSquares`, the orthogonal sum `QuadraticMap.prod`
and base change `QuadraticForm.baseChange`.  The theory of quadratic forms over number
fields needs the dual notions: isotropy, representation of a value, and the interaction of
nondegeneracy with orthogonal sums and base change.  This file supplies them.

## Main definitions

* `Isotropic Q`: `Q` vanishes on a nonzero vector.
* `IsotropicFn f`: the same for a bare function `f`, used for translates of a form.
* `represents Q a`: `Q` takes the value `a` on a nonzero vector.
* `Indefinite Q` (over `ℝ`): `Q` takes both a negative and a positive value.

## Main results

* `isotropic_iff_not_anisotropic`, `not_isotropic_iff_anisotropic`.
* `represents_zero_iff_isotropic`, `represents_iff_sub_isotropic`.
* `isotropic_iff_zero_of_rank_one`: in dimension one isotropy is being zero.
* `nondegenerate_weightedSumSquares`, `nondegenerate_prod`, `nondegenerate_of_anisotropic`.
* `IsometryEquiv.baseChange`, `Equivalent.baseChange`.
* `Indefinite.isotropic`: an indefinite real form is isotropic (intermediate value theorem).
-/

public section

open Module QuadraticMap

namespace HasseMinkowski

/-! ### Isotropic quadratic maps -/

section Isotropic

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N]

/-- A quadratic map is *isotropic* if it vanishes on some nonzero vector. -/
def Isotropic (Q : QuadraticMap R M N) : Prop := ∃ x, x ≠ 0 ∧ Q x = 0

-- Theorem: isotropy is exactly the negation of Mathlib's anisotropy.
theorem isotropic_iff_not_anisotropic (Q : QuadraticMap R M N) :
    Isotropic Q ↔ ¬ Q.Anisotropic := by
  unfold Isotropic
  exact (QuadraticMap.not_anisotropic_iff_exists Q).symm

-- Theorem: a quadratic map is anisotropic iff it is not isotropic.
theorem not_isotropic_iff_anisotropic (Q : QuadraticMap R M N) :
    ¬ Isotropic Q ↔ Q.Anisotropic := by
  rw [isotropic_iff_not_anisotropic, not_not]

end Isotropic

/-- Function-level isotropy: a function vanishing at a nonzero vector.

This is needed to speak about a translate `x ↦ Q x - a` of a quadratic form, which is not a
quadratic map (it does not vanish at `0` when `a ≠ 0`). -/
def IsotropicFn {M N : Type*} [Zero M] [Zero N] (f : M → N) : Prop := ∃ x, x ≠ 0 ∧ f x = 0

/-! ### Representing values -/

section Represents

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A quadratic form *represents* `a` if it takes the value `a` on a nonzero vector.

For `a ≠ 0` the restriction to nonzero vectors is immaterial, since `Q 0 = 0`; for `a = 0`
it makes the notion agree with isotropy, as in the classical theory. -/
def represents (Q : QuadraticForm R M) (a : R) : Prop := ∃ x, x ≠ 0 ∧ Q x = a

-- Theorem: a form represents `0` iff it is isotropic.
theorem represents_zero_iff_isotropic (Q : QuadraticForm R M) :
    represents Q 0 ↔ Isotropic Q :=
  Iff.rfl

-- Theorem: `Q` represents `a` iff the translate `x ↦ Q x - a` is isotropic.
theorem represents_iff_sub_isotropic (Q : QuadraticForm R M) (a : R) :
    represents Q a ↔ IsotropicFn (fun x : M => Q x - a) := by
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, by simp [h]⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, sub_eq_zero.mp h⟩

end Represents

/-! ### Rank-one forms -/

section RankOne

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

-- Theorem: in dimension one a quadratic form is isotropic iff it is the zero form.
theorem isotropic_iff_zero_of_rank_one (Q : QuadraticForm K V) (hr : finrank K V = 1) :
    Isotropic Q ↔ Q = 0 := by
  constructor
  · rintro ⟨x, hx, hQx⟩
    have hspan : K ∙ x = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [finrank_span_singleton hx, hr]
    apply QuadraticMap.ext
    intro y
    have hy : y ∈ K ∙ x := by rw [hspan]; exact Submodule.mem_top
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [QuadraticMap.map_smul, hQx, smul_zero]
    rfl
  · intro hQ
    have hnt : ∃ x : V, x ≠ 0 := by
      by_contra h
      rw [not_exists] at h
      have h0 : finrank K V = 0 :=
        finrank_zero_iff_forall_zero.mpr fun x => by simpa using h x
      rw [hr] at h0
      exact Nat.one_ne_zero h0
    obtain ⟨x, hx⟩ := hnt
    exact ⟨x, hx, by simp [hQ]⟩

end RankOne

/-! ### Nondegeneracy -/

section WeightedSumSquares

variable {K ι : Type*} [Field K] [Invertible (2 : K)] [Fintype ι]

-- Theorem: a weighted sum of squares with unit weights is nondegenerate.
theorem nondegenerate_weightedSumSquares (w : ι → Kˣ) :
    (weightedSumSquares K (fun i => (w i : K))).Nondegenerate := by
  have : NeZero (2 : K) := ⟨(isUnit_of_invertible (2 : K)).ne_zero⟩
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot,
    QuadraticForm.radical_weightedSumSquares (w := fun i => (w i : K))]
  have hset : {i : ι | ((w i : Kˣ) : K) = 0} = ∅ := by
    ext i
    simp
  rw [hset]
  simp [Pi.spanSubset]

end WeightedSumSquares

section Prod

variable {R M₁ M₂ : Type*} [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂]
  [Module R M₁] [Module R M₂]

-- Theorem: an orthogonal sum of nondegenerate quadratic forms is nondegenerate.
theorem nondegenerate_prod [Invertible (2 : R)] {Q₁ : QuadraticForm R M₁}
    {Q₂ : QuadraticForm R M₂} (h₁ : Q₁.Nondegenerate) (h₂ : Q₂.Nondegenerate) :
    (Q₁.prod Q₂).Nondegenerate := by
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot] at h₁ h₂ ⊢
  rw [← le_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  rw [QuadraticMap.radical_eq_ker_polarBilin, LinearMap.mem_ker, LinearMap.ext_iff] at hx
  have hx₁ : x.1 = 0 := by
    have hmem : x.1 ∈ (polarBilin Q₁).ker := by
      rw [LinearMap.mem_ker, LinearMap.ext_iff]
      intro y₁
      simpa using hx (y₁, 0)
    have hker : (polarBilin Q₁).ker = ⊥ := by
      rw [← QuadraticMap.radical_eq_ker_polarBilin, h₁]
    rwa [hker, Submodule.mem_bot] at hmem
  have hx₂ : x.2 = 0 := by
    have hmem : x.2 ∈ (polarBilin Q₂).ker := by
      rw [LinearMap.mem_ker, LinearMap.ext_iff]
      intro y₂
      simpa using hx (0, y₂)
    have hker : (polarBilin Q₂).ker = ⊥ := by
      rw [← QuadraticMap.radical_eq_ker_polarBilin, h₂]
    rwa [hker, Submodule.mem_bot] at hmem
  exact Prod.ext hx₁ hx₂

end Prod

section Anisotropic

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Invertible (2 : K)]

-- Theorem: an anisotropic quadratic form is nondegenerate.
theorem nondegenerate_of_anisotropic {Q : QuadraticForm K V} (hQ : Q.Anisotropic) :
    Q.Nondegenerate := by
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot, ← le_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  exact hQ x (QuadraticMap.mem_radical_iff'.mp hx).1

end Anisotropic

/-! ### Rank-zero forms -/

section RankZero

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

-- Theorem: every quadratic form on a zero-dimensional space is anisotropic.
theorem anisotropic_of_rank_zero (Q : QuadraticForm K V) (hr : finrank K V = 0) :
    Q.Anisotropic := by
  intro x _
  exact (finrank_zero_iff_forall_zero.mp hr) x

-- Theorem: no quadratic form on a zero-dimensional space is isotropic.
theorem not_isotropic_of_rank_zero (Q : QuadraticForm K V) (hr : finrank K V = 0) :
    ¬ Isotropic Q := by
  rintro ⟨x, hx, _⟩
  exact hx ((finrank_zero_iff_forall_zero.mp hr) x)

end RankZero

/-! ### Indefinite real forms -/

section Real

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- A real quadratic form is *indefinite* if it takes both a negative and a positive value. -/
def Indefinite (Q : QuadraticForm ℝ M) : Prop :=
  (∃ x, Q x < 0) ∧ (∃ x, 0 < Q x)

-- Theorem: an indefinite real quadratic form is isotropic.
theorem Indefinite.isotropic {Q : QuadraticForm ℝ M} (h : Indefinite Q) : Isotropic Q := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := h
  let F : ℝ → ℝ := fun t => Q x + (t * t) * Q (y - x) + t * polarBilin Q x (y - x)
  have hF : ∀ t, Q (x + t • (y - x)) = F t := by
    intro t
    change Q (x + t • (y - x)) =
      Q x + (t * t) * Q (y - x) + t * polarBilin Q x (y - x)
    have hpol : polar Q x (t • (y - x)) = t * polarBilin Q x (y - x) := by
      rw [← polarBilin_apply_apply, LinearMap.map_smul, smul_eq_mul]
    rw [QuadraticMap.map_add Q x (t • (y - x)), QuadraticMap.map_smul, hpol, smul_eq_mul]
  have hFcont : Continuous F := by
    unfold F
    exact (continuous_const.add ((continuous_id.mul continuous_id).mul
      continuous_const)).add (continuous_id.mul continuous_const)
  have h0 : F 0 = Q x := by simp [F]
  have h1 : F 1 = Q y := by
    rw [← hF 1]
    simp
  obtain ⟨t, -, ht0⟩ := (intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
    hFcont.continuousOn) (by rw [h0, h1]; exact ⟨hx.le, hy.le⟩)
  have ht_ne : t ≠ 0 := by
    intro ht
    rw [ht, h0] at ht0
    linarith
  have ht1_ne : t ≠ 1 := by
    intro ht
    rw [ht, h1] at ht0
    linarith
  have hz_ne : x + t • (y - x) ≠ 0 := by
    intro hz
    have hty : t • y = (t - 1) • x := by
      have hz' : (1 - t) • x + t • y = 0 := by
        have hxy : x + t • (y - x) = (1 - t) • x + t • y := by module
        rw [← hxy]; exact hz
      have h1' : t • y = -((1 - t) • x) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]
        exact hz'
      rw [h1', sub_smul, sub_smul, one_smul, neg_sub]
    have hsq : t ^ 2 * Q y = (t - 1) ^ 2 * Q x := by
      have := congrArg Q hty
      rw [QuadraticMap.map_smul, QuadraticMap.map_smul] at this
      simpa [smul_eq_mul, pow_two] using this
    have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht_ne
    have ht12 : 0 < (t - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr ht1_ne)
    have hpos : 0 < t ^ 2 * Q y := mul_pos ht2 hy
    have hneg : (t - 1) ^ 2 * Q x < 0 := mul_neg_of_pos_of_neg ht12 hx
    linarith
  exact ⟨x + t • (y - x), hz_ne, by rw [hF t]; exact ht0⟩

end Real

end HasseMinkowski

/-! ### Base change of isometries

These belong to the `QuadraticMap` namespace so that `e.baseChange` works by dot notation
for an isometry equivalence `e`, in the same way as the rest of Mathlib's quadratic-form API.
-/

namespace QuadraticMap

variable {R A M₁ M₂ : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M₁] [AddCommGroup M₂] [Module R M₁] [Module R M₂]

namespace IsometryEquiv

/-- Base change sends an isometry equivalence of quadratic forms to one. -/
noncomputable def baseChange [Invertible (2 : R)] {Q₁ : QuadraticForm R M₁}
    {Q₂ : QuadraticForm R M₂} (e : Q₁.IsometryEquiv Q₂) :
    (QuadraticForm.baseChange A Q₁).IsometryEquiv (QuadraticForm.baseChange A Q₂) := by
  have hcomp : (QuadraticForm.baseChange A Q₂).comp
      (e.toLinearEquiv.baseChange R A M₁ M₂) = QuadraticForm.baseChange A Q₁ := by
    apply baseChange_ext
    intro m
    simp [QuadraticForm.baseChange_tmul, e.map_app]
  refine { toLinearEquiv := e.toLinearEquiv.baseChange R A M₁ M₂, map_app' := ?_ }
  intro x
  exact congr_fun hcomp x

end IsometryEquiv

namespace Equivalent

-- Theorem: base change preserves equivalence of quadratic forms.
theorem baseChange [Invertible (2 : R)] {Q₁ : QuadraticForm R M₁}
    {Q₂ : QuadraticForm R M₂} (h : Q₁.Equivalent Q₂) :
    (QuadraticForm.baseChange A Q₁).Equivalent (QuadraticForm.baseChange A Q₂) :=
  h.elim fun e => ⟨e.baseChange⟩

end Equivalent

end QuadraticMap

/-! ## Dot-notation aliases

The generic API above lives in `HasseMinkowski`; these aliases let `Q.Isotropic` and
`Q.represents a` be used directly for a quadratic map `Q`, matching Mathlib's convention
for `Q.Anisotropic` and `QuadraticMap.prod`.
-/

namespace QuadraticMap

variable {R M N : Type*}

/-- Dot-notation alias for `HasseMinkowski.Isotropic`: the quadratic map vanishes on some
nonzero vector. -/
abbrev Isotropic [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (Q : QuadraticMap R M N) : Prop :=
  HasseMinkowski.Isotropic Q

/-- Dot-notation alias for `HasseMinkowski.represents`: the quadratic form takes the value `a`
on some nonzero vector. -/
abbrev represents [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) (a : R) : Prop :=
  HasseMinkowski.represents Q a

end QuadraticMap
