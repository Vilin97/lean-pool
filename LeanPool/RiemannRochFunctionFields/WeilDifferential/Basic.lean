/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import LeanPool.RiemannRochFunctionFields.Genus.Basic
public import LeanPool.RiemannRochFunctionFields.Genus.AdeleQuotient
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Weil differentials and the duality theorem
This file defines Weil differentials, the canonical divisor class, and the duality theorem
that identifies `L(W − D)` with `Ω(D)`.

## Main definitions

* `FunctionField.WeilDifferential`
* `FunctionField.WeilDifferential.differentialSpace`
* `FunctionField.WeilDifferential.divOmega`
* `FunctionField.IsCanonical`

## Main results

* `FunctionField.WeilDifferential.finrank_weilDifferential_eq_one`
* `FunctionField.isCanonical_unique_up_to_principal`
* `FunctionField.duality`
-/

@[expose] public section

open scoped nonZeroDivisors Polynomial RatFunc WithZero

noncomputable section

namespace FunctionField.Chart

variable (k K : Type*) [Field k] [Field K]

variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
  [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]

variable [IsFullConstantField k K]

/-- The classical decidable equality on `k(X)` used by the coordinate places. -/
local instance instDecidableEqRatFuncWeil : DecidableEq k⟮X⟯ := Classical.decEq _

attribute [local instance] adeleFiltAddCommGroup adeleFiltModule

/-- The `k`- and `K`-scalar actions on the adele space are compatible. -/
instance instIsScalarTowerAdeleSpace : IsScalarTower k K (AdeleSpace k K) :=
  ⟨fun c x a => Subtype.ext <| funext fun v => by
    change (c • x) * a.val v = c • (x * a.val v)
    rw [Algebra.smul_def, Algebra.smul_def, mul_assoc]⟩

omit [IsFullConstantField k K] in
/-- The sandwich quotient `A(D') ⧸ (A(D) + diag(K)) ⊓ A(D')` is finite-dimensional. -/
theorem finite_adeleFilt_sub_quotient {D D' : DivisorA k K} (hle : D ≤ D') :
    Module.Finite k ((adeleFilt k K D') ⧸
      Submodule.comap (adeleFilt k K D').subtype
        (adeleFilt k K D + diagonalSubmodule k K)) := by
  have hE : IsEffective k K (D' - D) := (le_iff_sub_effective k K).mp hle
  have hdiv : D + (D' - D) = D' := by abel
  have : Module.Finite k ((adeleFilt k K D') ⧸
      Submodule.comap (adeleFilt k K D').subtype (adeleFilt k K D)) :=
    finiteAdeleFiltDiff_quotient_add_eq k K (M := D) hdiv.symm hE
  exact Module.Finite.equiv (Submodule.quotientQuotientEquivQuotient
    (Submodule.comap (adeleFilt k K D').subtype (adeleFilt k K D))
    (Submodule.comap (adeleFilt k K D').subtype
      (adeleFilt k K D + diagonalSubmodule k K))
    (Submodule.comap_mono (by
      rw [Submodule.add_eq_sup]
      exact le_sup_left)))

/-- The adele class space `𝒜_K ⧸ (A(D) + diag(K))` is finite-dimensional over `k`. -/
instance finiteDimensional_adeleQuotient (D : DivisorA k K) :
    FiniteDimensional k
      ((AdeleSpace k K) ⧸ (adeleFilt k K D + diagonalSubmodule k K)) := by
  obtain ⟨D₁, hD₁⟩ := exists_defect_eq (k := k) (K := K)
  have hle : D ≤ D ⊔ D₁ := le_sup_left
  have hfull : topAdeleSubmodule k K =
      adeleFilt k K (D ⊔ D₁) + diagonalSubmodule k K :=
    adeleSubmodule_top_eq_adeleFilt_add_diagonal (k := k) (K := K)
      (defect_eq_genus_of_ge (k := k) (K := K) le_sup_right hD₁)
  have := finite_adeleFilt_sub_quotient (k := k) (K := K) hle
  have hker : Submodule.comap (adeleFilt k K (D ⊔ D₁)).subtype
      (adeleFilt k K D + diagonalSubmodule k K) ≤
      LinearMap.ker (((adeleFilt k K D + diagonalSubmodule k K).mkQ).comp
        (adeleFilt k K (D ⊔ D₁)).subtype) := by
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
      Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hx
  refine Module.Finite.of_surjective (Submodule.liftQ _ _ hker) ?_
  intro y
  obtain ⟨x, rfl⟩ :=
    Submodule.mkQ_surjective (adeleFilt k K D + diagonalSubmodule k K) y
  have hx : x ∈ adeleFilt k K (D ⊔ D₁) + diagonalSubmodule k K := by
    have hxtop : x ∈ topAdeleSubmodule k K := Submodule.mem_top
    rwa [hfull] at hxtop
  rcases Submodule.mem_sup.mp hx with ⟨a, ha, b, hb, rfl⟩
  refine ⟨Submodule.Quotient.mk ⟨a, ha⟩, ?_⟩
  rw [Submodule.liftQ_apply]
  change (adeleFilt k K D + diagonalSubmodule k K).mkQ a =
    (adeleFilt k K D + diagonalSubmodule k K).mkQ (a + b)
  have hb0 : (adeleFilt k K D + diagonalSubmodule k K).mkQ b = 0 := by
    rw [Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_sup_right hb)
  rw [map_add, hb0, add_zero]

omit [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K] in
/-- If `D ≤ D'` and `deg D' ≤ deg D`, the divisors are equal. -/
theorem eq_of_le_of_deg_le {D D' : DivisorA k K} (h : D ≤ D')
    (hdeg : deg k K D' ≤ deg k K D) : D = D' := by
  have hE : IsEffective k K (D' - D) := (le_iff_sub_effective k K).mp h
  have hdeg0 : deg k K (D' - D) = 0 := by
    have hge : 0 ≤ deg k K (D' - D) := deg_nonneg k K hE
    rw [deg_sub] at hge ⊢
    omega
  have hzero : D' - D = 0 := eq_zero_of_effective_deg_zero k K hE hdeg0
  exact (sub_eq_zero.mp hzero).symm

/-- A Weil differential: a k-linear functional on adeles vanishing on some `A(D)+diag(K)`. -/
structure WeilDifferential where
  /-- The underlying `k`-linear functional on adeles. -/
  toFun : AdeleSpace k K →ₗ[k] k
  /-- The functional vanishes on `A(D) + diag(K)` for some divisor `D`. -/
  vanishes_on : ∃ D : DivisorA k K,
    ∀ α ∈ adeleFilt k K D + diagonalSubmodule k K, toFun α = 0

namespace WeilDifferential

variable {k K}

/-- A Weil differential is nonzero. -/
def IsNonzero (ω : WeilDifferential k K) : Prop := ω.toFun ≠ 0

/-- The space `Ω(D)` of k-linear functionals vanishing on `A(D)+diag(K)`. -/
def differentialSpace (D : DivisorA k K) : Submodule k (AdeleSpace k K →ₗ[k] k) where
  carrier := {φ | ∀ a ∈ adeleFilt k K D + diagonalSubmodule k K, φ a = 0}
  zero_mem' := by simp
  add_mem' {f g} hf hg := by
    intro a ha
    simp [hf a ha, hg a ha]
  smul_mem' c f hf := by
    intro a ha
    simp [hf a ha]

theorem finrank_differentialSpace (D : DivisorA k K) :
    Module.finrank k (differentialSpace D) = indexOfSpecialty k K D := by
  let S := adeleFilt k K D + diagonalSubmodule k K
  have homega : differentialSpace D = S.dualAnnihilator := by
    ext φ
    rw [Submodule.mem_dualAnnihilator]
    change (∀ a ∈ adeleFilt k K D + diagonalSubmodule k K, φ a = 0) ↔ _
    rfl
  rw [homega, ← S.dualQuotEquivDualAnnihilator.finrank_eq, Subspace.dual_finrank_eq]
  exact finrank_adele_quotient k K D

theorem exists_nontrivial_omega :
    ∃ D : DivisorA k K, differentialSpace D ≠ ⊥ := by
  let : IsScalarTower k k⟮X⟯ K :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply k k[X] K,
        IsScalarTower.algebraMap_apply k[X] k⟮X⟯ K,
        ← IsScalarTower.algebraMap_apply k k[X] k⟮X⟯]
  let x : K := algebraMap k⟮X⟯ K (RatFunc.X : k⟮X⟯)
  have hx : ¬IsAlgebraic k x := by
    exact (transcendental_algebraMap_iff (algebraMap k⟮X⟯ K).injective).2
      RatFunc.transcendental_X
  let E : DivisorA k K := polarDivisor k K x
  let D : DivisorA k K := -(E + E)
  have hE : 0 < deg k K E := polar_deg_pos k K hx
  have hD : deg k K D < 0 := by
    simp only [D, deg_neg, deg_add]
    omega
  have hℓ : ell k K D = 0 := RRspace_neg_deg_ell k K hD
  have hi := indexOfSpecialty_eq k K D
  have hindex : 0 < indexOfSpecialty k K D := by
    have hg : 0 ≤ (genus k K : ℤ) := Int.natCast_nonneg _
    have hdegD : deg k K D = -(deg k K E + deg k K E) := by
      simp only [D, deg_neg, deg_add]
    rw [hℓ, hdegD] at hi
    exact_mod_cast (show (0 : ℤ) < (indexOfSpecialty k K D : ℤ) by omega)
  refine ⟨D, fun hbot => ?_⟩
  have hfin : 0 < Module.finrank k (differentialSpace D) := by
    rw [finrank_differentialSpace]
    exact hindex
  rw [hbot, finrank_bot] at hfin
  omega

omit [IsFullConstantField k K] in
/-- Multiplication by a unit sends `A(D + (x)) + diag(K)` into `A(D) + diag(K)`. -/
theorem mul_mem_adeleFilt_add_diagonal (x : Kˣ) (D : DivisorA k K)
    {a : AdeleSpace k K}
    (ha : a ∈ adeleFilt k K (D + principalDivisorA k K (Additive.ofMul x)) +
      diagonalSubmodule k K) :
    (x : K) • a ∈ adeleFilt k K D + diagonalSubmodule k K := by
  rw [Submodule.add_eq_sup] at ha ⊢
  rcases Submodule.mem_sup.mp ha with ⟨a₁, ha₁, a₂, ha₂, rfl⟩
  refine Submodule.mem_sup.mpr ⟨(x : K) • a₁, ?_, (x : K) • a₂, ?_,
    (smul_add (x : K) a₁ a₂).symm⟩
  · intro v
    change placeValuation k K v ((x : K) * a₁.val v) ≤ WithZero.exp (D v)
    rw [map_mul]
    have hxval := placeValuation_eq_exp_neg_principalDivisor k K (Additive.ofMul x) v
    change placeValuation k K v (x : K) =
      WithZero.exp (-(principalDivisorA k K (Additive.ofMul x) v)) at hxval
    rw [hxval]
    have hv := ha₁ v
    rw [Finsupp.add_apply, WithZero.exp_add] at hv
    calc
      WithZero.exp (-(principalDivisorA k K (Additive.ofMul x) v)) *
          placeValuation k K v (a₁.val v) ≤
          WithZero.exp (-(principalDivisorA k K (Additive.ofMul x) v)) *
            (WithZero.exp (D v) *
              WithZero.exp (principalDivisorA k K (Additive.ofMul x) v)) :=
        mul_le_mul_right hv _
      _ = WithZero.exp (D v) := by
        rw [← WithZero.exp_add, ← WithZero.exp_add]
        congr 1
        ring
  · rcases ha₂ with ⟨f, rfl⟩
    exact ⟨(x : K) * f, by ext v; rfl⟩

/-- Scalar multiplication of a Weil differential by `x ∈ K`. -/
noncomputable def smulWeil (x : K) (ω : WeilDifferential k K) : WeilDifferential k K := by
  by_cases hx : x = 0
  · exact ⟨0, ⟨0, by simp⟩⟩
  let xu : Kˣ := Units.mk0 x hx
  refine ⟨ω.toFun.comp (mulAdeleLinear k K x), ?_⟩
  obtain ⟨D, hD⟩ := ω.vanishes_on
  refine ⟨D + principalDivisorA k K (Additive.ofMul xu), fun a ha => hD _ ?_⟩
  change x • a ∈ adeleFilt k K D + diagonalSubmodule k K
  simpa only [xu, Units.val_mk0] using
    mul_mem_adeleFilt_add_diagonal (k := k) (K := K) xu D ha

omit [IsFullConstantField k K] in
@[simp]
theorem smulWeil_toFun_apply (x : K) (ω : WeilDifferential k K) (a : AdeleSpace k K) :
    (smulWeil x ω).toFun a = ω.toFun (x • a) := by
  by_cases hx : x = 0
  · simp [smulWeil, hx]
  · simp only [smulWeil, hx, ↓reduceDIte, LinearMap.comp_apply]
    congr 1

instance : Zero (WeilDifferential k K) := ⟨⟨0, ⟨0, by simp⟩⟩⟩

instance : Add (WeilDifferential k K) where
  add ω η := ⟨ω.toFun + η.toFun, by
    obtain ⟨Dω, hω⟩ := ω.vanishes_on
    obtain ⟨Dη, hη⟩ := η.vanishes_on
    refine ⟨Dω ⊓ Dη, fun a ha => ?_⟩
    have hleft : adeleFilt k K (Dω ⊓ Dη) + diagonalSubmodule k K ≤
        adeleFilt k K Dω + diagonalSubmodule k K := by
      simpa only [Submodule.add_eq_sup] using
        sup_le_sup (adeleFilt_mono k K inf_le_left) le_rfl
    have hright : adeleFilt k K (Dω ⊓ Dη) + diagonalSubmodule k K ≤
        adeleFilt k K Dη + diagonalSubmodule k K := by
      simpa only [Submodule.add_eq_sup] using
        sup_le_sup (adeleFilt_mono k K inf_le_right) le_rfl
    simp [hω a (hleft ha), hη a (hright ha)]⟩

omit [IsFullConstantField k K] in
@[ext]
theorem ext {ω η : WeilDifferential k K} (h : ω.toFun = η.toFun) : ω = η := by
  cases ω
  cases η
  cases h
  rfl

instance : Neg (WeilDifferential k K) where
  neg ω := ⟨-ω.toFun, by
    obtain ⟨D, hD⟩ := ω.vanishes_on
    exact ⟨D, fun a ha => by simp [hD a ha]⟩⟩

instance : AddCommGroup (WeilDifferential k K) where
  add_assoc _ _ _ := ext (add_assoc _ _ _)
  zero_add _ := ext (zero_add _)
  add_zero _ := ext (add_zero _)
  add_comm _ _ := ext (add_comm _ _)
  nsmul := nsmulRec
  nsmul_zero _ := ext rfl
  nsmul_succ _ _ := ext rfl
  neg := Neg.neg
  neg_add_cancel ω := ext (neg_add_cancel ω.toFun)
  sub := fun ω η => ω + -η
  sub_eq_add_neg _ _ := rfl
  zsmul := zsmulRec

noncomputable instance : SMul K (WeilDifferential k K) := ⟨smulWeil⟩

noncomputable instance : Module K (WeilDifferential k K) :=
  Module.ofMinimalAxioms
    (fun x ω η => by
      apply ext
      ext a
      change (smulWeil x (ω + η)).toFun a =
        ((smulWeil x ω).toFun + (smulWeil x η).toFun) a
      rw [smulWeil_toFun_apply]
      change (ω.toFun + η.toFun) (x • a) =
        (smulWeil x ω).toFun a + (smulWeil x η).toFun a
      rw [LinearMap.add_apply, smulWeil_toFun_apply, smulWeil_toFun_apply])
    (fun x y ω => by
      apply ext
      ext a
      change (smulWeil (x + y) ω).toFun a =
        ((smulWeil x ω).toFun + (smulWeil y ω).toFun) a
      rw [smulWeil_toFun_apply]
      change ω.toFun ((x + y) • a) =
        (smulWeil x ω).toFun a + (smulWeil y ω).toFun a
      rw [smulWeil_toFun_apply, smulWeil_toFun_apply, add_smul, map_add])
    (fun x y ω => by
      apply ext
      ext a
      change (smulWeil (x * y) ω).toFun a = (smulWeil x (smulWeil y ω)).toFun a
      rw [smulWeil_toFun_apply, smulWeil_toFun_apply, smulWeil_toFun_apply]
      rw [← mul_smul, mul_comm x y])
    (fun ω => by
      apply ext
      ext a
      change (smulWeil 1 ω).toFun a = ω.toFun a
      rw [smulWeil_toFun_apply, one_smul])

omit [IsFullConstantField k K] in
theorem smulWeil_algebraMap (c : k) (ω : WeilDifferential k K) (a : AdeleSpace k K) :
    (smulWeil (algebraMap k K c) ω).toFun a = c • ω.toFun a := by
  rw [smulWeil_toFun_apply, algebraMap_smul, map_smul]

omit [IsFullConstantField k K] in
theorem smulWeil_eq_zero_iff (x : K) (hx : x ≠ 0) (ω : WeilDifferential k K) :
    smulWeil x ω = 0 ↔ ω = 0 := by
  constructor
  · intro hxω
    calc ω = (1 : K) • ω := (one_smul K ω).symm
      _ = (x⁻¹ * x) • ω := by rw [inv_mul_cancel₀ hx]
      _ = x⁻¹ • (x • ω) := mul_smul x⁻¹ x ω
      _ = x⁻¹ • (smulWeil x ω) := rfl
      _ = x⁻¹ • (0 : WeilDifferential k K) := by rw [hxω]
      _ = 0 := smul_zero x⁻¹
  · intro hω
    subst hω
    change x • (0 : WeilDifferential k K) = 0
    exact smul_zero x

omit [IsFullConstantField k K] in
/-- `Ω(D)` is the dual annihilator of `A(D) + diag(K)`. -/
theorem differentialSpace_eq_dualAnnihilator (D : DivisorA k K) :
    differentialSpace (k := k) (K := K) D =
      (adeleFilt k K D + diagonalSubmodule k K).dualAnnihilator := by
  ext φ
  rw [Submodule.mem_dualAnnihilator]
  change (∀ a ∈ adeleFilt k K D + diagonalSubmodule k K, φ a = 0) ↔ _
  rfl

instance instFiniteDimensionalDifferentialSpace (D : DivisorA k K) :
    FiniteDimensional k (differentialSpace (k := k) (K := K) D) := by
  rw [differentialSpace_eq_dualAnnihilator D]
  exact Module.Finite.equiv
    (Submodule.dualQuotEquivDualAnnihilator
      (adeleFilt k K D + diagonalSubmodule k K))

/-- Divisors `D` for which `ω` vanishes on `A(D)+diag(K)`. -/
def vanishingDivisors (ω : WeilDifferential k K) : Set (DivisorA k K) :=
  {D | ∀ α ∈ adeleFilt k K D + diagonalSubmodule k K, ω.toFun α = 0}

omit [IsFullConstantField k K] in
/-- `vanishingDivisors` is downward closed. -/
theorem mem_vanishingDivisors_of_le {ω : WeilDifferential k K} {D D' : DivisorA k K}
    (hle : D' ≤ D) (hD : D ∈ vanishingDivisors ω) : D' ∈ vanishingDivisors ω := by
  intro α hα
  apply hD
  have hsub : adeleFilt k K D' + diagonalSubmodule k K ≤
      adeleFilt k K D + diagonalSubmodule k K := by
    simpa only [Submodule.add_eq_sup] using
      sup_le_sup (adeleFilt_mono k K hle) (le_refl (diagonalSubmodule k K))
  exact hsub hα

omit [IsFullConstantField k K] in
/-- Underlying functional of a sum of differentials. -/
theorem add_toFun (ω η : WeilDifferential k K) :
    (ω + η).toFun = ω.toFun + η.toFun := rfl

omit [IsFullConstantField k K] in
/-- If `ω` vanishes on `A(D₀)+diag(K)` and `f ∈ L(E)`, then `f•ω` vanishes on
`A(D₀−E)+diag(K)`. -/
theorem smulWeil_toFun_mem_differentialSpace (ω : WeilDifferential k K) {D₀ : DivisorA k K}
    (h : D₀ ∈ vanishingDivisors ω) {E : DivisorA k K} (f : RRspace k K E) :
    (smulWeil (f : K) ω).toFun ∈ differentialSpace (k := k) (K := K) (D₀ - E) := by
  have hvan : ∀ α ∈ adeleFilt k K D₀ + diagonalSubmodule k K, ω.toFun α = 0 := h
  change ∀ a ∈ adeleFilt k K (D₀ - E) + diagonalSubmodule k K,
    (smulWeil (f : K) ω).toFun a = 0
  intro a ha
  rw [smulWeil_toFun_apply]
  by_cases hf : (f : K) = 0
  · rw [hf, zero_smul, map_zero]
  · have hmemE : memRRspace k K (D₀ - (D₀ - E)) (f : K) := by
      rw [sub_sub_cancel]
      exact (mem_RRspace_iff k K E (f : K)).mp f.property
    have hdivle : D₀ - E ≤ D₀ +
        principalDivisorA k K (Additive.ofMul (Units.mk0 (f : K) hf)) :=
      le_add_principal_of_memRRspace (k := k) (K := K) (D₀ := D₀ - E) (D₁ := D₀)
        hf hmemE
    have hle : adeleFilt k K (D₀ - E) + diagonalSubmodule k K ≤
        adeleFilt k K (D₀ + principalDivisorA k K
          (Additive.ofMul (Units.mk0 (f : K) hf))) + diagonalSubmodule k K := by
      simpa only [Submodule.add_eq_sup] using
        sup_le_sup (adeleFilt_mono k K hdivle) (le_refl (diagonalSubmodule k K))
    have hsm := mul_mem_adeleFilt_add_diagonal (k := k) (K := K)
      (Units.mk0 (f : K) hf) D₀ (hle ha)
    rw [Units.val_mk0] at hsm
    exact hvan _ hsm

/-- For `D₀ ∈ M_ω`, multiplication into `ω` maps `L(E)` into `Ω(D₀ − E)`. -/
noncomputable def smulIntoOmega (ω : WeilDifferential k K) {D₀ : DivisorA k K}
    (h : D₀ ∈ vanishingDivisors ω) (E : DivisorA k K) :
    RRspace k K E →ₗ[k] differentialSpace (k := k) (K := K) (D₀ - E) where
  toFun f := ⟨(smulWeil (f : K) ω).toFun, smulWeil_toFun_mem_differentialSpace ω h f⟩
  map_add' f g := by
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    change (smulWeil ((f : K) + (g : K)) ω).toFun a =
      (smulWeil (f : K) ω).toFun a + (smulWeil (g : K) ω).toFun a
    rw [smulWeil_toFun_apply, smulWeil_toFun_apply, smulWeil_toFun_apply, add_smul,
      map_add]
  map_smul' c f := by
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    change (smulWeil (c • (f : K)) ω).toFun a = c • (smulWeil (f : K) ω).toFun a
    rw [smulWeil_toFun_apply, smulWeil_toFun_apply, Algebra.smul_def, mul_smul,
      algebraMap_smul, map_smul]

omit [IsFullConstantField k K] in
@[simp]
theorem smulIntoOmega_coe (ω : WeilDifferential k K) {D₀ : DivisorA k K}
    (h : D₀ ∈ vanishingDivisors ω) (E : DivisorA k K) (f : RRspace k K E) :
    (smulIntoOmega ω h E f : AdeleSpace k K →ₗ[k] k) = (smulWeil (f : K) ω).toFun :=
  rfl

omit [IsFullConstantField k K] in
theorem smulIntoOmega_injective (ω : WeilDifferential k K) {D₀ : DivisorA k K}
    (h : D₀ ∈ vanishingDivisors ω) (E : DivisorA k K) (hω : ω.toFun ≠ 0) :
    Function.Injective (smulIntoOmega ω h E) := by
  intro f g hfg
  by_contra hne
  have hd0 : smulIntoOmega ω h E (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  have hval : ((f - g : RRspace k K E) : K) ≠ 0 := by
    intro h0
    exact hne (sub_eq_zero.mp (Subtype.ext h0))
  have htoFun : (smulWeil ((f - g : RRspace k K E) : K) ω).toFun = 0 :=
    congrArg Subtype.val hd0
  have hzero : smulWeil ((f - g : RRspace k K E) : K) ω = 0 := ext htoFun
  have hω0 : ω = 0 := (smulWeil_eq_zero_iff _ hval ω).mp hzero
  apply hω
  rw [hω0]
  rfl

/-- **S2**: the space of Weil differentials is one-dimensional over `K`. -/
theorem finrank_weilDifferential_eq_one :
    Module.finrank K (WeilDifferential k K) = 1 := by
  obtain ⟨D₀', hD₀'⟩ := exists_nontrivial_omega (k := k) (K := K)
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD₀'
  set ω₀ : WeilDifferential k K := ⟨φ, ⟨D₀', hφ⟩⟩ with hω₀def
  have hω₀ne : ω₀ ≠ 0 := by
    intro h
    apply hφ0
    have hval : ω₀.toFun = φ := rfl
    rw [← hval, h]; rfl
  refine (finrank_eq_one_iff_of_nonzero' ω₀ hω₀ne).mpr ?_
  intro ω
  by_contra hspan
  push Not at hspan
  -- Independence: `f•ω₀ + g•ω = 0 → f = 0 ∧ g = 0`.
  have hindep : ∀ f g : K, f • ω₀ + g • ω = 0 → f = 0 ∧ g = 0 := by
    intro f g hfg
    by_cases hg : g = 0
    · subst hg
      rw [zero_smul, add_zero] at hfg
      refine ⟨?_, rfl⟩
      by_contra hf
      exact hω₀ne ((smulWeil_eq_zero_iff f hf ω₀).mp hfg)
    · exfalso
      apply hspan (g⁻¹ * (-f))
      have hgω : g • ω = (-f) • ω₀ := by
        have hneg : g • ω = -(f • ω₀) := by
          rw [eq_neg_iff_add_eq_zero, add_comm]; exact hfg
        rw [hneg, neg_smul]
      have hω : ω = (g⁻¹ * (-f)) • ω₀ := by
        rw [mul_smul, ← hgω, ← mul_smul, inv_mul_cancel₀ hg, one_smul]
      exact hω.symm
  -- Common vanishing divisor `D₀`.
  obtain ⟨D₁, hD₁⟩ := ω₀.vanishes_on
  obtain ⟨D₂, hD₂⟩ := ω.vanishes_on
  set D₀ : DivisorA k K := D₁ ⊓ D₂ with hD₀def
  have h₀ : D₀ ∈ vanishingDivisors ω₀ :=
    mem_vanishingDivisors_of_le inf_le_left hD₁
  have h₂ : D₀ ∈ vanishingDivisors ω :=
    mem_vanishingDivisors_of_le inf_le_right hD₂
  -- Pole family.
  set B : DivisorA k K := polarDivisor k K (XK k K) with hBdef
  have hBpos : 0 < deg k K B := polar_deg_pos k K (not_algebraic_XK k K)
  have hb1 : 1 ≤ deg k K B := hBpos
  -- The counting bound at level `n`: `2 ℓ(nB) ≤ i(D₀ − nB)`.
  have hcount : ∀ n : ℕ,
      2 * (ell k K (n • B) : ℤ) ≤ indexOfSpecialty k K (D₀ - n • B) := by
    intro n
    set E : DivisorA k K := n • B with hEdef
    have hinj : Function.Injective
        (LinearMap.coprod (smulIntoOmega ω₀ h₀ E) (smulIntoOmega ω h₂ E)) := by
      intro x y hxy
      have hd : (LinearMap.coprod (smulIntoOmega ω₀ h₀ E)
          (smulIntoOmega ω h₂ E)) (x - y) = 0 := by
        rw [map_sub, hxy, sub_self]
      rw [LinearMap.coprod_apply] at hd
      have hcoe : (smulWeil (((x - y).1 : RRspace k K E) : K) ω₀).toFun
          + (smulWeil (((x - y).2 : RRspace k K E) : K) ω).toFun = 0 := by
        have h1 := congrArg Subtype.val hd
        simpa only [Submodule.coe_add, smulIntoOmega_coe, Submodule.coe_zero] using h1
      have hsum : ((((x - y).1 : RRspace k K E) : K) • ω₀
          + (((x - y).2 : RRspace k K E) : K) • ω).toFun = 0 := by
        rw [add_toFun]; exact hcoe
      have hzero : (((x - y).1 : RRspace k K E) : K) • ω₀
          + (((x - y).2 : RRspace k K E) : K) • ω = 0 := ext hsum
      obtain ⟨hf0, hg0⟩ := hindep _ _ hzero
      have hxy0 : x - y = 0 := Prod.ext (Subtype.ext hf0) (Subtype.ext hg0)
      exact sub_eq_zero.mp hxy0
    have hfrle : Module.finrank k (RRspace k K E × RRspace k K E) ≤
        Module.finrank k (differentialSpace (k := k) (K := K) (D₀ - E)) :=
      LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_prod, finrank_differentialSpace] at hfrle
    have hLfr : Module.finrank k (RRspace k K E) = ell k K E := rfl
    rw [hLfr] at hfrle
    omega
  -- Choose `n` large enough to contradict the bound.
  set M : ℤ := max (deg k K D₀) (3 * (genus k K : ℤ) - 3 - deg k K D₀) with hMdef
  set n : ℕ := M.toNat + 1 with hndef
  have hn_ge : (n : ℤ) ≥ M + 1 := by
    have hself := Int.self_le_toNat M
    push_cast [hndef]
    omega
  have hn_d0 : (n : ℤ) > deg k K D₀ := by
    have hle : deg k K D₀ ≤ M := le_max_left _ _
    omega
  have hn_g : (n : ℤ) > 3 * (genus k K : ℤ) - 3 - deg k K D₀ := by
    have hle : 3 * (genus k K : ℤ) - 3 - deg k K D₀ ≤ M := le_max_right _ _
    omega
  have hnb_ge : (n : ℤ) * deg k K B ≥ (n : ℤ) := by
    have hn0 : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
    nlinarith [hb1, hn0]
  have hdegsub : deg k K (D₀ - n • B) = deg k K D₀ - (n : ℤ) * deg k K B := by
    rw [deg_sub, deg_nsmul]
  have hdeg_neg : deg k K (D₀ - n • B) < 0 := by
    rw [hdegsub]; omega
  have hℓ0 : ell k K (D₀ - n • B) = 0 := RRspace_neg_deg_ell k K hdeg_neg
  have hi := indexOfSpecialty_eq (k := k) (K := K) (D₀ - n • B)
  rw [hℓ0, hdegsub] at hi
  have hrr := riemann_ineq (k := k) (K := K) (n • B)
  rw [deg_nsmul] at hrr
  have hc := hcount n
  omega

omit [IsFullConstantField k K] in
/-- Vanishing divisors translate by the principal divisor under scalar multiplication. -/
theorem add_principal_mem_vanishingDivisors_smul_iff (x : Kˣ)
    (ω : WeilDifferential k K) (D : DivisorA k K) :
    D + principalDivisorA k K (Additive.ofMul x) ∈
        vanishingDivisors ((x : K) • ω) ↔
      D ∈ vanishingDivisors ω := by
  constructor
  · intro h a ha
    let P := principalDivisorA k K (Additive.ofMul x)
    have hsource :
        (D + P) + principalDivisorA k K (Additive.ofMul (x⁻¹ : Kˣ)) = D := by
      have hinv : Additive.ofMul (x⁻¹ : Kˣ) = -(Additive.ofMul x) := rfl
      rw [hinv, map_neg]
      abel
    have haSource : a ∈ adeleFilt k K
          ((D + P) + principalDivisorA k K (Additive.ofMul (x⁻¹ : Kˣ))) +
          diagonalSubmodule k K := by
      simpa only [hsource] using ha
    have ha' := mul_mem_adeleFilt_add_diagonal (k := k) (K := K)
      (x⁻¹ : Kˣ) (D + P) haSource
    have hz := h (((x⁻¹ : Kˣ) : K) • a) ha'
    change (smulWeil (x : K) ω).toFun (((x⁻¹ : Kˣ) : K) • a) = 0 at hz
    rw [smulWeil_toFun_apply] at hz
    simpa [mul_smul] using hz
  · intro h a ha
    change (smulWeil (x : K) ω).toFun a = 0
    rw [smulWeil_toFun_apply]
    exact h _ (mul_mem_adeleFilt_add_diagonal (k := k) (K := K) x D ha)

omit [IsFullConstantField k K] in
/-- Directedness of the vanishing set: it is closed under `⊔`. -/
theorem sup_mem_vanishingDivisors {ω : WeilDifferential k K} {D₁ D₂ : DivisorA k K}
    (hD₁ : D₁ ∈ vanishingDivisors ω) (hD₂ : D₂ ∈ vanishingDivisors ω) :
    D₁ ⊔ D₂ ∈ vanishingDivisors ω := by
  intro α hα
  rw [Submodule.add_eq_sup, adeleFilt_sup_eq_add, ← Submodule.add_eq_sup] at hα
  rw [Submodule.add_eq_sup] at hα
  rcases Submodule.mem_sup.mp hα with ⟨a, ha, d, hd, rfl⟩
  rw [Submodule.add_eq_sup] at ha
  rcases Submodule.mem_sup.mp ha with ⟨a₁, ha₁, a₂, ha₂, rfl⟩
  have hsplit : a₁ + a₂ + d = (a₁ + d) + a₂ := by abel
  rw [hsplit, map_add]
  have h1 : ω.toFun (a₁ + d) = 0 := by
    apply hD₁
    rw [Submodule.add_eq_sup]
    exact Submodule.add_mem_sup ha₁ hd
  have h2 : ω.toFun a₂ = 0 := by
    apply hD₂
    rw [Submodule.add_eq_sup]
    exact Submodule.mem_sup_left ha₂
  rw [h1, h2, add_zero]

/-- Degree bound (duality-free): a vanishing divisor of a nonzero `ω` has degree `≤ 2g − 1`. -/
theorem deg_le_of_mem_vanishingDivisors {ω : WeilDifferential k K} (hω : ω.toFun ≠ 0)
    {D : DivisorA k K} (hD : D ∈ vanishingDivisors ω) :
    deg k K D ≤ 2 * (genus k K : ℤ) - 1 := by
  have hinj : Function.Injective (smulIntoOmega ω hD D) :=
    smulIntoOmega_injective ω hD D hω
  have hle : Module.finrank k (RRspace k K D) ≤
      Module.finrank k (differentialSpace (k := k) (K := K) (D - D)) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  have hDD : D - D = (0 : DivisorA k K) := sub_self D
  have hΩ : Module.finrank k (differentialSpace (k := k) (K := K) (D - D)) = genus k K := by
    rw [hDD, finrank_differentialSpace]
    have hidx := indexOfSpecialty_eq (k := k) (K := K) (0 : DivisorA k K)
    rw [ell_zero (k := k) (K := K), deg_zero (k := k) (K := K)] at hidx
    omega
  have hℓg : (ell k K D : ℤ) ≤ (genus k K : ℤ) := by
    have hnat : ell k K D ≤ genus k K := by
      rw [show ell k K D = Module.finrank k (RRspace k K D) from rfl, ← hΩ]
      exact hle
    exact_mod_cast hnat
  have hRR := riemann_ineq (k := k) (K := K) D
  omega

theorem exists_max_vanishingDivisor {ω : WeilDifferential k K} (hω : IsNonzero ω) :
    ∃! W : DivisorA k K, W ∈ vanishingDivisors ω ∧
      ∀ D ∈ vanishingDivisors ω, D ≤ W := by
  have hω' : ω.toFun ≠ 0 := hω
  set P : ℤ → Prop := fun z => ∃ D ∈ vanishingDivisors ω, deg k K D = z with hP
  have hInh : ∃ z, P z := by
    obtain ⟨D₀, hD₀⟩ := ω.vanishes_on
    exact ⟨deg k K D₀, D₀, hD₀, rfl⟩
  have hBdd : ∃ b : ℤ, ∀ z, P z → z ≤ b := by
    refine ⟨2 * (genus k K : ℤ) - 1, ?_⟩
    rintro z ⟨D, hD, rfl⟩
    exact deg_le_of_mem_vanishingDivisors hω' hD
  obtain ⟨ub, ⟨W, hWmem, hWdeg⟩, hubmax⟩ := Int.exists_greatest_of_bdd hBdd hInh
  have hmaxdiv : ∀ D ∈ vanishingDivisors ω, D ≤ W := by
    intro D hD
    have hsup : D ⊔ W ∈ vanishingDivisors ω := sup_mem_vanishingDivisors hD hWmem
    have hdegle : deg k K (D ⊔ W) ≤ ub := hubmax _ ⟨D ⊔ W, hsup, rfl⟩
    have hWle : W ≤ D ⊔ W := le_sup_right
    have hdegW : deg k K (D ⊔ W) ≤ deg k K W := by rw [hWdeg]; exact hdegle
    have heq : W = D ⊔ W := eq_of_le_of_deg_le k K hWle hdegW
    rw [heq]; exact le_sup_left
  refine ⟨W, ⟨hWmem, hmaxdiv⟩, ?_⟩
  rintro W' ⟨hW'mem, hW'max⟩
  exact le_antisymm (hmaxdiv W' hW'mem) (hW'max W hWmem)

/-- The divisor of a nonzero Weil differential. -/
noncomputable def divOmega (ω : WeilDifferential k K) (hω : IsNonzero ω) : DivisorA k K :=
  Classical.choose (exists_max_vanishingDivisor (k := k) (K := K) hω)

theorem divOmega_smul (x : Kˣ) (ω : WeilDifferential k K) (hω : IsNonzero ω)
    (hxω : IsNonzero ((x : K) • ω)) :
    WeilDifferential.divOmega ((x : K) • ω) hxω =
      WeilDifferential.divOmega ω hω + principalDivisorA k K (Additive.ofMul x) := by
  let W := WeilDifferential.divOmega ω hω
  let P := principalDivisorA k K (Additive.ofMul x)
  have hmax : W ∈ vanishingDivisors ω ∧
      ∀ D ∈ vanishingDivisors ω, D ≤ W := by
    simpa only [W, divOmega] using
      (Classical.choose_spec (exists_max_vanishingDivisor (k := k) (K := K) hω)).1
  have htarget : W + P ∈ vanishingDivisors ((x : K) • ω) ∧
      ∀ E ∈ vanishingDivisors ((x : K) • ω), E ≤ W + P := by
    constructor
    · exact (add_principal_mem_vanishingDivisors_smul_iff
        (k := k) (K := K) x ω W).2 hmax.1
    · intro E hE
      have htranslate : (E - P) + P = E := by abel
      have hE' : E - P ∈ vanishingDivisors ω := by
        apply (add_principal_mem_vanishingDivisors_smul_iff
          (k := k) (K := K) x ω (E - P)).1
        simpa only [P, htranslate] using hE
      have hle := hmax.2 (E - P) hE'
      intro v
      have hv := hle v
      simp only [Finsupp.sub_apply, Finsupp.add_apply] at hv ⊢
      omega
  let hex := exists_max_vanishingDivisor (k := k) (K := K) hxω
  have hchosen : WeilDifferential.divOmega ((x : K) • ω) hxω ∈
        vanishingDivisors ((x : K) • ω) ∧
      ∀ D ∈ vanishingDivisors ((x : K) • ω),
        D ≤ WeilDifferential.divOmega ((x : K) • ω) hxω := by
    simpa only [divOmega, hex] using (Classical.choose_spec hex).1
  exact hex.unique hchosen htarget

end WeilDifferential

/-- A divisor is canonical when it is the divisor of a nonzero Weil differential. -/
def IsCanonical (W : DivisorA k K) : Prop :=
  ∃ (ω : WeilDifferential k K) (hω : WeilDifferential.IsNonzero ω),
    WeilDifferential.divOmega ω hω = W

/-- A function field admits a canonical divisor. -/
theorem exists_isCanonical : ∃ W : DivisorA k K, IsCanonical k K W := by
  obtain ⟨D, hD⟩ := WeilDifferential.exists_nontrivial_omega (k := k) (K := K)
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
  let ω : WeilDifferential k K := ⟨φ, ⟨D, hφ⟩⟩
  have hω : WeilDifferential.IsNonzero ω := hφ0
  exact ⟨WeilDifferential.divOmega ω hω, ω, hω, rfl⟩

theorem isCanonical_unique_up_to_principal {W₁ W₂ : DivisorA k K}
    (h₁ : IsCanonical k K W₁) (h₂ : IsCanonical k K W₂) :
    ∃ f : Kˣ, W₁ - W₂ = principalDivisorA k K (Additive.ofMul f) := by
  rcases h₁ with ⟨ω₁, hω₁, rfl⟩
  rcases h₂ with ⟨ω₂, hω₂, rfl⟩
  have hω₁0 : ω₁ ≠ 0 := by
    intro h
    apply hω₁
    rw [h]
    rfl
  have hω₂0 : ω₂ ≠ 0 := by
    intro h
    apply hω₂
    rw [h]
    rfl
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one (K := K)
    (WeilDifferential.finrank_weilDifferential_eq_one (k := k) (K := K)) hω₂0 ω₁
  have hc0 : c ≠ 0 := by
    intro h
    subst c
    apply hω₁0
    simpa only [zero_smul] using hc.symm
  let f : Kˣ := Units.mk0 c hc0
  have hcf : (f : K) • ω₂ = ω₁ := by
    simpa only [f, Units.val_mk0] using hc
  have hnontrivial : WeilDifferential.IsNonzero ((f : K) • ω₂) := by
    exact hcf.symm ▸ hω₁
  refine ⟨f, ?_⟩
  have hdiv := WeilDifferential.divOmega_smul (k := k) (K := K) f ω₂ hω₂ hnontrivial
  calc
    WeilDifferential.divOmega ω₁ hω₁ - WeilDifferential.divOmega ω₂ hω₂ =
        WeilDifferential.divOmega ((f : K) • ω₂) hnontrivial -
          WeilDifferential.divOmega ω₂ hω₂ := by
            congr 2
            exact hcf.symm
    _ = principalDivisorA k K (Additive.ofMul f) := by rw [hdiv]; abel

open WeilDifferential in
theorem duality {W : DivisorA k K} (hW : IsCanonical k K W) (D : DivisorA k K) :
    ell k K (W - D) = indexOfSpecialty k K D := by
  obtain ⟨ω₀, hω₀, hdivW⟩ := hW
  have hω₀' : ω₀.toFun ≠ 0 := hω₀
  have hω₀ne : ω₀ ≠ 0 := fun h => hω₀ (by rw [h]; rfl)
  -- `W` is the maximum vanishing divisor of `ω₀`.
  have hWspec : W ∈ vanishingDivisors ω₀ ∧
      ∀ D' ∈ vanishingDivisors ω₀, D' ≤ W := by
    have h := (Classical.choose_spec
      (WeilDifferential.exists_max_vanishingDivisor (k := k) (K := K) hω₀)).1
    have he : Classical.choose
        (WeilDifferential.exists_max_vanishingDivisor (k := k) (K := K) hω₀) = W := hdivW
    rw [he] at h
    exact h
  obtain ⟨hWmem, hWmax⟩ := hWspec
  have hWD : W - (W - D) = D := sub_sub_cancel W D
  -- The multiplication map `μ : L(W − D) → Ω(W − (W − D))`.
  set μ := smulIntoOmega ω₀ hWmem (W - D) with hμdef
  have hμinj : Function.Injective μ := smulIntoOmega_injective ω₀ hWmem (W - D) hω₀'
  have hμsurj : Function.Surjective μ := by
    intro ψ
    set φ : AdeleSpace k K →ₗ[k] k := (ψ : AdeleSpace k K →ₗ[k] k) with hφdef
    by_cases hψ0 : φ = 0
    · exact ⟨0, by rw [map_zero]; exact (Subtype.ext hψ0).symm⟩
    · -- Package `ψ` as a nonzero differential vanishing on `A(D)+diag(K)`.
      have hψmem : ∀ α ∈ adeleFilt k K D + diagonalSubmodule k K, φ α = 0 := by
        have hp : ∀ α ∈ adeleFilt k K (W - (W - D)) + diagonalSubmodule k K, φ α = 0 :=
          ψ.property
        rw [hWD] at hp
        exact hp
      set η : WeilDifferential k K := ⟨φ, ⟨D, hψmem⟩⟩ with hηdef
      have hηnt : η.toFun ≠ 0 := hψ0
      obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one (K := K)
        (WeilDifferential.finrank_weilDifferential_eq_one (k := k) (K := K)) hω₀ne η
      have hc0 : c ≠ 0 := by
        intro h
        subst h
        apply hηnt
        have hη0 : η = 0 := by rw [← hc, zero_smul]
        rw [hη0]; rfl
      set cu : Kˣ := Units.mk0 c hc0 with hcudef
      set P : DivisorA k K := principalDivisorA k K (Additive.ofMul cu) with hPdef
      -- `D ∈ M_{c•ω₀}` translates to `D − P ∈ M_ω₀`.
      have hDmem : D ∈ vanishingDivisors ((cu : K) • ω₀) := by
        have hcω : (cu : K) • ω₀ = η := by
          rw [Units.val_mk0]; exact hc
        rw [hcω]
        intro α hα
        exact hψmem α hα
      have hDPmem : D - P ∈ vanishingDivisors ω₀ := by
        apply (add_principal_mem_vanishingDivisors_smul_iff (k := k) (K := K) cu ω₀ (D - P)).1
        have hsub : (D - P) + P = D := by rw [hPdef]; abel
        rw [hsub]; exact hDmem
      have hDPle : D - P ≤ W := hWmax (D - P) hDPmem
      -- Hence `c ∈ L(W − D)`.
      have hcmem : memRRspace k K (W - D) c := by
        intro v
        have hval := placeValuation_eq_exp_neg_principalDivisor k K (Additive.ofMul cu) v
        change placeValuation k K v c ≤ WithZero.exp ((W - D) v)
        have hcv : placeValuation k K v c =
            WithZero.exp (-(P v)) := by
          rw [hPdef]
          have hcuc : (cu : K) = c := by simp [hcudef]
          rw [← hcuc]; exact hval
        rw [hcv]
        apply WithZero.exp_le_exp.mpr
        have hlev := hDPle v
        simp only [Finsupp.sub_apply] at hlev ⊢
        omega
      refine ⟨⟨c, (mem_RRspace_iff k K (W - D) c).mpr hcmem⟩, ?_⟩
      apply Subtype.ext
      rw [hμdef, smulIntoOmega_coe]
      change ((c : K) • ω₀).toFun = φ
      rw [hc]
  -- Conclude via the induced equivalence.
  have hfr : Module.finrank k (RRspace k K (W - D)) =
      Module.finrank k (differentialSpace (k := k) (K := K) (W - (W - D))) :=
    (LinearEquiv.ofBijective μ ⟨hμinj, hμsurj⟩).finrank_eq
  change Module.finrank k (RRspace k K (W - D)) = indexOfSpecialty k K D
  rw [hfr, hWD, finrank_differentialSpace]

theorem indexOfSpecialty_eq_ell_sub {W : DivisorA k K} (hW : IsCanonical k K W) (D : DivisorA k K) :
    (indexOfSpecialty k K D : ℤ) = ell k K (W - D) := by
  exact_mod_cast (duality k K hW D).symm

end FunctionField.Chart

end
