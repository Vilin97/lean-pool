/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.GCDMonoid.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Content of a tensor over a GCD algebra

Let `K` be a field, let `D` be a commutative `K`-algebra, and let `V` be a `K`-vector space.
For `z : V ⊗[K] D`, a class `a : Associates D` is the content of `z` when, for every `q : D`,
`q` divides `a` exactly when `z` is obtained by multiplying the right tensor factor by `q`.

This divisibility property is the public definition. Existence over a GCD monoid is proved by
choosing a basis of `V` internally and taking the greatest common divisor of the finitely many
nonzero coordinates. The resulting associate class is independent of both that basis and the
chosen `GCDMonoid` structure.
-/

open scoped TensorProduct

universe u v w x

namespace TensorProduct

public noncomputable section

variable {K : Type u} {D : Type v} {V : Type w}
variable [Field K] [CommRing D] [IsDomain D] [Algebra K D]
variable [AddCommGroup V] [Module K V]

/-- Multiply the right tensor factor by `q`. -/
def mulRightFactor (q : D) : V ⊗[K] D →ₗ[K] V ⊗[K] D :=
  LinearMap.lTensor (R := K) V (LinearMap.mulLeft K (A := D) q)

omit [IsDomain D] in
/-- Multiplication on the right tensor factor sends `x ⊗ d` to `x ⊗ qd`. -/
@[simp]
theorem mulRightFactor_tmul (q d : D) (x : V) :
    mulRightFactor (K := K) (D := D) (V := V) q (x ⊗ₜ[K] d) =
      x ⊗ₜ[K] (q * d) := by
  simp [mulRightFactor]

/-- `a` is the associate class of the greatest common divisor of the coefficients of `z`.

The right-hand side is intrinsic: it does not mention a basis or chosen coordinates. -/
def IsContent (z : V ⊗[K] D) (a : Associates D) : Prop :=
  ∀ q : D, Associates.mk q ≤ a ↔
    ∃ y : V ⊗[K] D, mulRightFactor (K := K) q y = z

omit [IsDomain D] in
/-- The intrinsic divisibility characterization of tensor content. -/
theorem isContent_iff (z : V ⊗[K] D) (a : Associates D) :
    IsContent z a ↔
      ∀ q : D, Associates.mk q ≤ a ↔
        ∃ y : V ⊗[K] D, mulRightFactor (K := K) q y = z :=
  Iff.rfl

omit [IsDomain D] in
/-- Applying a linear map to the left tensor factor commutes with multiplication on the right
tensor factor. -/
theorem rTensor_mulRightFactor
    {W : Type x} [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (q : D) (z : V ⊗[K] D) :
    f.rTensor D (mulRightFactor (K := K) q z) =
      mulRightFactor (K := K) q (f.rTensor D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul y d => simp
  | add y z hy hz => simp [map_add, hy, hz]

omit [IsDomain D] in
/-- An injective linear change of the left tensor factor preserves the intrinsic content
property. -/
theorem isContent_rTensor_iff_of_injective
    {W : Type x} [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (hf : Function.Injective f)
    (z : V ⊗[K] D) (a : Associates D) :
    IsContent (f.rTensor D z) a ↔ IsContent z a := by
  let hker : f.ker = ⊥ := LinearMap.ker_eq_bot.mpr hf
  let g := f.leftInverse
  have hgf : g.comp f = LinearMap.id := f.leftInverse_comp_of_inj hker
  have hgfTensor (y : V ⊗[K] D) : g.rTensor D (f.rTensor D y) = y := by
    rw [← LinearMap.rTensor_comp_apply, hgf, LinearMap.rTensor_id]
    rfl
  constructor
  · intro h
    rw [isContent_iff] at h ⊢
    intro q
    constructor
    · intro hqa
      obtain ⟨y, hy⟩ := (h q).mp hqa
      refine ⟨g.rTensor D y, ?_⟩
      calc
        mulRightFactor (K := K) q (g.rTensor D y) =
            g.rTensor D (mulRightFactor (K := K) q y) :=
          (rTensor_mulRightFactor g q y).symm
        _ = g.rTensor D (f.rTensor D z) := congrArg (g.rTensor D) hy
        _ = z := hgfTensor z
    · rintro ⟨y, hy⟩
      apply (h q).mpr
      refine ⟨f.rTensor D y, ?_⟩
      calc
        mulRightFactor (K := K) q (f.rTensor D y) =
            f.rTensor D (mulRightFactor (K := K) q y) :=
          (rTensor_mulRightFactor f q y).symm
        _ = f.rTensor D z := congrArg (f.rTensor D) hy
  · intro h
    rw [isContent_iff] at h ⊢
    intro q
    constructor
    · intro hqa
      obtain ⟨y, hy⟩ := (h q).mp hqa
      refine ⟨f.rTensor D y, ?_⟩
      calc
        mulRightFactor (K := K) q (f.rTensor D y) =
            f.rTensor D (mulRightFactor (K := K) q y) :=
          (rTensor_mulRightFactor f q y).symm
        _ = f.rTensor D z := congrArg (f.rTensor D) hy
    · rintro ⟨y, hy⟩
      apply (h q).mpr
      refine ⟨g.rTensor D y, ?_⟩
      calc
        mulRightFactor (K := K) q (g.rTensor D y) =
            g.rTensor D (mulRightFactor (K := K) q y) :=
          (rTensor_mulRightFactor g q y).symm
        _ = g.rTensor D (f.rTensor D z) := congrArg (g.rTensor D) hy
        _ = z := hgfTensor z

/-- The intrinsic content property determines at most one associate class. -/
theorem IsContent.eq {z : V ⊗[K] D} {a b : Associates D}
    (ha : IsContent z a) (hb : IsContent z b) : a = b := by
  induction a using Quotient.inductionOn with
  | _ a =>
      induction b using Quotient.inductionOn with
      | _ b =>
          apply le_antisymm
          · exact (hb a).2 ((ha a).1 le_rfl)
          · exact (ha b).2 ((hb b).1 le_rfl)

@[implicit_reducible]
private noncomputable def normalizedAssociatesGCDMonoid
    (gcdStructure : GCDMonoid D) :
    NormalizedGCDMonoid (Associates D) := by
  classical
  letI : GCDMonoid D := gcdStructure
  letI : GCDMonoid (Associates D) := inferInstance
  exact normalizedGCDMonoidOfExistsGCD fun a b ↦
    ⟨gcd a b, fun d ↦ (dvd_gcd_iff d a b).symm⟩

private noncomputable def contentBasis :
    Module.Basis (Module.Free.ChooseBasisIndex K V) K V :=
  Module.Free.chooseBasis K V

private noncomputable def contentCoordinates :
    V ⊗[K] D ≃ₗ[K] Module.Free.ChooseBasisIndex K V →₀ D :=
  TensorProduct.equivFinsuppOfBasisLeft
    (contentBasis (K := K) (V := V))

omit [IsDomain D] in
private theorem contentCoordinates_mulRightFactor_apply
    (q : D) (z : V ⊗[K] D)
    (i : Module.Free.ChooseBasisIndex K V) :
    contentCoordinates (K := K) (D := D) (V := V)
        (mulRightFactor (K := K) q z) i =
      q * contentCoordinates (K := K) (D := D) (V := V) z i := by
  induction z using TensorProduct.induction_on with
  | zero => simp [mulRightFactor]
  | tmul x d =>
      rw [mulRightFactor_tmul]
      simp only [contentCoordinates,
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
      rw [_root_.Algebra.smul_def, _root_.Algebra.smul_def]
      ring
  | add x y hx hy => simp [map_add, hx, hy, mul_add]

omit [IsDomain D] in
private theorem exists_mulRightFactor_eq_iff
    (q : D) (z : V ⊗[K] D) :
    (∃ y : V ⊗[K] D, mulRightFactor (K := K) q y = z) ↔
      ∀ i, q ∣ contentCoordinates (K := K) (D := D) (V := V) z i := by
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨contentCoordinates (K := K) (D := D) (V := V) y i,
      contentCoordinates_mulRightFactor_apply (K := K) q y i⟩
  · intro h
    let c := contentCoordinates (K := K) (D := D) (V := V) z
    let c' : Module.Free.ChooseBasisIndex K V →₀ D :=
      Finsupp.onFinset c.support
        (fun i ↦ if hi : i ∈ c.support then Classical.choose (h i) else 0)
        (fun i hi ↦ by
          by_contra hnot
          simp [hnot] at hi)
    refine ⟨(contentCoordinates (K := K) (D := D) (V := V)).symm c', ?_⟩
    apply (contentCoordinates (K := K) (D := D) (V := V)).injective
    ext i
    rw [contentCoordinates_mulRightFactor_apply,
      LinearEquiv.apply_symm_apply]
    by_cases hi : i ∈ c.support
    · rw [show c' i = Classical.choose (h i) by simp [c', hi]]
      exact (Classical.choose_spec (h i)).symm
    · rw [show c' i = 0 by simp [c', hi], mul_zero]
      exact Finsupp.notMem_support_iff.mp hi |>.symm

omit [IsDomain D] in
/-- The zero tensor has zero content. -/
theorem isContent_zero : IsContent (0 : V ⊗[K] D) 0 := by
  intro q
  constructor
  · intro _
    exact ⟨0, (mulRightFactor (K := K) q).map_zero⟩
  · intro _
    change Associates.mk q ≤ Associates.mk 0
    exact Associates.mk_le_mk_of_dvd (dvd_zero q)

omit [IsDomain D] in
/-- A pure tensor with nonzero left factor has the content of its right factor. -/
theorem isContent_tmul_of_ne_zero (x : V) (hx : x ≠ 0) (d : D) :
    IsContent (x ⊗ₜ[K] d) (Associates.mk d) := by
  classical
  intro q
  rw [Associates.mk_le_mk_iff_dvd]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨x ⊗ₜ[K] e, ?_⟩
    rw [mulRightFactor_tmul, he]
  · intro hfactor
    have hcoordinates :=
      (exists_mulRightFactor_eq_iff (K := K) q (x ⊗ₜ[K] d)).mp hfactor
    have hrepr : (contentBasis (K := K) (V := V)).repr x ≠ 0 := by
      intro hzero
      apply hx
      apply (contentBasis (K := K) (V := V)).repr.injective
      simpa using hzero
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hrepr
    have hqi := hcoordinates i
    simp only [contentCoordinates,
      TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply] at hqi
    have hunit : IsUnit
        (algebraMap K D ((contentBasis (K := K) (V := V)).repr x i)) :=
      (isUnit_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)).map
        (algebraMap K D)
    rw [_root_.Algebra.smul_def] at hqi
    exact hunit.dvd_mul_left.mp hqi

omit [IsDomain D] in
/-- A nonzero pure tensor `x ⊗ 1` has unit content. -/
theorem isContent_tmul_one_of_ne_zero (x : V) (hx : x ≠ 0) :
    IsContent (x ⊗ₜ[K] (1 : D)) 1 := by
  simpa using isContent_tmul_of_ne_zero (D := D) x hx (1 : D)

private noncomputable def contentAux
    (gcdStructure : GCDMonoid D) (z : V ⊗[K] D) : Associates D := by
  letI : GCDMonoid D := gcdStructure
  letI : NormalizedGCDMonoid (Associates D) :=
    normalizedAssociatesGCDMonoid gcdStructure
  let c := contentCoordinates (K := K) (D := D) (V := V) z
  exact c.support.gcd fun i ↦ Associates.mk (c i)

private theorem contentAux_isContent
    (gcdStructure : GCDMonoid D) (z : V ⊗[K] D) :
    IsContent z (contentAux gcdStructure z) := by
  letI : GCDMonoid D := gcdStructure
  letI : NormalizedGCDMonoid (Associates D) :=
    normalizedAssociatesGCDMonoid gcdStructure
  intro q
  change Associates.mk q ∣ contentAux gcdStructure z ↔ _
  rw [contentAux, Finset.dvd_gcd_iff,
    exists_mulRightFactor_eq_iff]
  constructor
  · intro h i
    by_cases hi : i ∈
        (contentCoordinates (K := K) (D := D) (V := V) z).support
    · exact Associates.mk_le_mk_iff_dvd.mp (h i hi)
    · rw [Finsupp.notMem_support_iff.mp hi]
      exact dvd_zero q
  · intro h i hi
    exact Associates.mk_le_mk_of_dvd (h i)

/-- Over a GCD monoid, every tensor has a unique intrinsic content class. -/
theorem existsUnique_isContent
    (gcdStructure : GCDMonoid D) (z : V ⊗[K] D) :
    ∃! a : Associates D, IsContent z a :=
  ⟨contentAux gcdStructure z, contentAux_isContent gcdStructure z,
    fun _a ha ↦ ha.eq (contentAux_isContent gcdStructure z)⟩

/-- Pairwise existence of greatest common divisors suffices for every tensor to have a unique
intrinsic content class. -/
theorem existsUnique_isContent_of_exists_gcd
    (h : ∀ a b : D, ∃ c : D, ∀ d : D,
      d ∣ a ∧ d ∣ b ↔ d ∣ c)
    (z : V ⊗[K] D) :
    ∃! a : Associates D, IsContent z a := by
  classical
  exact existsUnique_isContent (gcdMonoidOfExistsGCD h) z

/-- The intrinsic content class of a tensor, for an explicit `GCDMonoid` structure on `D`. -/
def content (gcdStructure : GCDMonoid D) (z : V ⊗[K] D) : Associates D :=
  Classical.choose (existsUnique_isContent gcdStructure z)

/-- The content class satisfies its intrinsic divisibility characterization. -/
theorem content_isContent (gcdStructure : GCDMonoid D) (z : V ⊗[K] D) :
    IsContent z (content gcdStructure z) :=
  Classical.choose_spec (existsUnique_isContent gcdStructure z) |>.1

/-- Any class satisfying the content property is the chosen content class. -/
theorem content_eq_of_isContent (gcdStructure : GCDMonoid D)
    {z : V ⊗[K] D} {a : Associates D} (ha : IsContent z a) :
    content gcdStructure z = a :=
  (content_isContent gcdStructure z).eq ha

/-- The content class does not depend on the chosen `GCDMonoid` structure. -/
theorem content_independent (gcdStructure₁ gcdStructure₂ : GCDMonoid D)
    (z : V ⊗[K] D) :
    content gcdStructure₁ z = content gcdStructure₂ z :=
  (content_isContent gcdStructure₁ z).eq
    (content_isContent gcdStructure₂ z)

end

end TensorProduct
