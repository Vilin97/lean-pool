/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import LeanPool.RiemannRochFunctionFields.CoordinateFree.AdeleSpace
public import LeanPool.RiemannRochFunctionFields.WeilDifferential.Basic

/-!
# Weil differentials over intrinsic places

Weil differentials are defined here as linear functionals on the intrinsic adele space that
vanish on `A(D)` plus the diagonal for some intrinsic divisor. The equivalence
`weilDifferentialEquivChart` transports the existing chart proofs without exposing chart-indexed
carriers in the public statements.
-/

@[expose] public section

open scoped nonZeroDivisors Polynomial RatFunc WithZero

noncomputable section

namespace FunctionField

open Chart

variable (k K : Type*) [Field k] [Field K]
variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K]

/-- A Weil differential is a functional on intrinsic adeles that vanishes on `A(D)` plus the
diagonal for some intrinsic divisor `D`. -/
structure WeilDifferential where
  /-- The underlying linear functional on intrinsic adeles. -/
  toFun : AdeleSpace k K →ₗ[k] k
  /-- A filtration piece plus the diagonal on which the functional vanishes. -/
  vanishes_on : ∃ D : Divisor k K,
    ∀ a ∈ adeleFilt k K D + diagonalSubmodule k K, toFun a = 0

namespace WeilDifferential

variable {k K}

/-- A Weil differential is nonzero when its underlying functional is nonzero. -/
def IsNonzero (omega : WeilDifferential k K) : Prop := omega.toFun ≠ 0

/-- The space of functionals vanishing on `A(D)` plus the diagonal. -/
def differentialSpace (D : Divisor k K) :
    Submodule k (AdeleSpace k K →ₗ[k] k) where
  carrier := {phi | ∀ a ∈ adeleFilt k K D + diagonalSubmodule k K, phi a = 0}
  zero_mem' := by simp
  add_mem' {phi psi} hphi hpsi := by
    intro a ha
    simp [hphi a ha, hpsi a ha]
  smul_mem' c phi hphi := by
    intro a ha
    simp [hphi a ha]

/-- The dual-space equivalence induced by reindexing intrinsic adeles to chart adeles. -/
noncomputable def adeleDualEquivChart :
    (AdeleSpace k K →ₗ[k] k) ≃ₗ[k] (Chart.AdeleSpace k K →ₗ[k] k) :=
  (adeleEquivChart k K).symm.dualMap

omit [IsFullConstantField k K] in
@[simp]
theorem adeleDualEquivChart_apply (phi : AdeleSpace k K →ₗ[k] k)
    (a : Chart.AdeleSpace k K) :
    adeleDualEquivChart (k := k) (K := K) phi a =
      phi ((adeleEquivChart k K).symm a) :=
  rfl

omit [IsFullConstantField k K] in
@[simp]
theorem adeleDualEquivChart_symm_apply (phi : Chart.AdeleSpace k K →ₗ[k] k)
    (a : AdeleSpace k K) :
    (adeleDualEquivChart (k := k) (K := K)).symm phi a =
      phi (adeleEquivChart k K a) :=
  rfl

/-- Reindex an intrinsic Weil differential as a chart Weil differential. -/
noncomputable def toChart (omega : WeilDifferential k K) :
    Chart.WeilDifferential k K where
  toFun := adeleDualEquivChart (k := k) (K := K) omega.toFun
  vanishes_on := by
    obtain ⟨D, hD⟩ := omega.vanishes_on
    refine ⟨(divisorEquivChart k K).symm D, fun a ha => ?_⟩
    apply hD ((adeleEquivChart k K).symm a)
    exact (mem_adeleFilt_add_diagonal_equivChart k K D _).mp (by simpa using ha)

/-- Reindex a chart Weil differential as an intrinsic Weil differential. -/
noncomputable def ofChart (omega : Chart.WeilDifferential k K) :
    WeilDifferential k K where
  toFun := (adeleDualEquivChart (k := k) (K := K)).symm omega.toFun
  vanishes_on := by
    obtain ⟨D, hD⟩ := omega.vanishes_on
    refine ⟨divisorEquivChart k K D, fun a ha => ?_⟩
    apply hD (adeleEquivChart k K a)
    have hmap := (mem_adeleFilt_add_diagonal_equivChart k K
      (divisorEquivChart k K D) a).mpr ha
    simpa using hmap

omit [IsFullConstantField k K] in
@[ext]
theorem ext {omega eta : WeilDifferential k K} (h : omega.toFun = eta.toFun) :
    omega = eta := by
  cases omega
  cases eta
  cases h
  rfl

instance : Zero (WeilDifferential k K) := ⟨⟨0, ⟨0, by simp⟩⟩⟩

instance : Add (WeilDifferential k K) where
  add omega eta := ⟨omega.toFun + eta.toFun, by
    obtain ⟨Domega, homega⟩ := omega.vanishes_on
    obtain ⟨Deta, heta⟩ := eta.vanishes_on
    refine ⟨Domega ⊓ Deta, fun a ha => ?_⟩
    have hleft : adeleFilt k K (Domega ⊓ Deta) + diagonalSubmodule k K ≤
        adeleFilt k K Domega + diagonalSubmodule k K := by
      simpa only [Submodule.add_eq_sup] using
        sup_le_sup (adeleFilt_mono k K inf_le_left) le_rfl
    have hright : adeleFilt k K (Domega ⊓ Deta) + diagonalSubmodule k K ≤
        adeleFilt k K Deta + diagonalSubmodule k K := by
      simpa only [Submodule.add_eq_sup] using
        sup_le_sup (adeleFilt_mono k K inf_le_right) le_rfl
    simp [homega a (hleft ha), heta a (hright ha)]⟩

instance : Neg (WeilDifferential k K) where
  neg omega := ⟨-omega.toFun, by
    obtain ⟨D, hD⟩ := omega.vanishes_on
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
  neg_add_cancel omega := ext (neg_add_cancel omega.toFun)
  sub := fun omega eta => omega + -eta
  sub_eq_add_neg _ _ := rfl
  zsmul := zsmulRec

/-- Intrinsic and chart Weil differentials are equivalent as additive groups. -/
noncomputable def weilDifferentialAddEquivChart :
    WeilDifferential k K ≃+ Chart.WeilDifferential k K where
  toFun := toChart
  invFun := ofChart
  left_inv omega := by
    apply ext
    exact (adeleDualEquivChart (k := k) (K := K)).symm_apply_apply omega.toFun
  right_inv omega := by
    apply Chart.WeilDifferential.ext
    exact (adeleDualEquivChart (k := k) (K := K)).apply_symm_apply omega.toFun
  map_add' omega eta := by
    apply Chart.WeilDifferential.ext
    exact (adeleDualEquivChart (k := k) (K := K)).map_add omega.toFun eta.toFun

noncomputable instance : SMul K (WeilDifferential k K) :=
  ⟨fun x omega =>
    (weilDifferentialAddEquivChart (k := k) (K := K)).symm
      (x • weilDifferentialAddEquivChart (k := k) (K := K) omega)⟩

omit [IsFullConstantField k K] in
@[simp]
theorem weilDifferentialAddEquivChart_smul (x : K) (omega : WeilDifferential k K) :
    weilDifferentialAddEquivChart (k := k) (K := K) (x • omega) =
      x • weilDifferentialAddEquivChart (k := k) (K := K) omega :=
  (weilDifferentialAddEquivChart (k := k) (K := K)).apply_symm_apply _

noncomputable instance : Module K (WeilDifferential k K) :=
  Function.Injective.module K
    (weilDifferentialAddEquivChart (k := k) (K := K)).toAddMonoidHom
    (weilDifferentialAddEquivChart (k := k) (K := K)).injective
    (weilDifferentialAddEquivChart_smul (k := k) (K := K))

/-- Intrinsic and chart Weil differentials are linearly equivalent over the function field. -/
noncomputable def weilDifferentialEquivChart :
    WeilDifferential k K ≃ₗ[K] Chart.WeilDifferential k K where
  __ := weilDifferentialAddEquivChart (k := k) (K := K)
  map_smul' := weilDifferentialAddEquivChart_smul (k := k) (K := K)

/-- The intrinsic space `Omega(D)` is linearly equivalent to its chart presentation. -/
noncomputable def differentialSpaceEquivChart (D : Divisor k K) :
    differentialSpace (k := k) (K := K) D ≃ₗ[k]
      Chart.WeilDifferential.differentialSpace
        ((divisorEquivChart k K).symm D) where
  toFun phi := ⟨adeleDualEquivChart (k := k) (K := K) phi.1, by
    intro a ha
    apply phi.2 ((adeleEquivChart k K).symm a)
    exact (mem_adeleFilt_add_diagonal_equivChart k K D _).mp (by simpa using ha)⟩
  invFun phi := ⟨(adeleDualEquivChart (k := k) (K := K)).symm phi.1, by
    intro a ha
    apply phi.2 (adeleEquivChart k K a)
    exact (mem_adeleFilt_add_diagonal_equivChart k K D a).mpr ha⟩
  left_inv phi := Subtype.ext
    ((adeleDualEquivChart (k := k) (K := K)).symm_apply_apply phi.1)
  right_inv phi := Subtype.ext
    ((adeleDualEquivChart (k := k) (K := K)).apply_symm_apply phi.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [IsFullConstantField k K] in
/-- The intrinsic and chart differential spaces have the same dimension. -/
theorem finrank_differentialSpace_eq_chart (D : Divisor k K) :
    Module.finrank k (differentialSpace (k := k) (K := K) D) =
      Module.finrank k (Chart.WeilDifferential.differentialSpace
        ((divisorEquivChart k K).symm D)) :=
  (differentialSpaceEquivChart (k := k) (K := K) D).finrank_eq

/-- The intrinsic space of Weil differentials is one-dimensional over `K`. -/
theorem finrank_weilDifferential_eq_one :
    Module.finrank K (WeilDifferential k K) = 1 := by
  rw [(weilDifferentialEquivChart (k := k) (K := K)).finrank_eq]
  exact Chart.WeilDifferential.finrank_weilDifferential_eq_one (k := k) (K := K)

omit [IsFullConstantField k K] in
/-- Non-vanishing is preserved by the intrinsic-to-chart equivalence. -/
theorem isNonzero_toChart (omega : WeilDifferential k K) :
    IsNonzero omega ↔ Chart.WeilDifferential.IsNonzero (toChart omega) := by
  change omega.toFun ≠ 0 ↔
    adeleDualEquivChart (k := k) (K := K) omega.toFun ≠ 0
  exact (adeleDualEquivChart (k := k) (K := K)).map_ne_zero_iff.symm

/-- The divisor of a nonzero intrinsic Weil differential. -/
noncomputable def divOmega (omega : WeilDifferential k K) (homega : IsNonzero omega) :
    Divisor k K :=
  divisorEquivChart k K <|
    Chart.WeilDifferential.divOmega (toChart omega) ((isNonzero_toChart omega).mp homega)

/-- Multiplying a differential adds the corresponding intrinsic principal divisor. -/
theorem divOmega_smul (x : Kˣ) (omega : WeilDifferential k K) (homega : IsNonzero omega)
    (hxomega : IsNonzero ((x : K) • omega)) :
    divOmega ((x : K) • omega) hxomega =
      divOmega omega homega + principalDivisor k K (Additive.ofMul x) := by
  apply (divisorEquivChart k K).symm.injective
  simp only [divOmega, principalDivisor, map_add, AddEquiv.symm_apply_apply]
  have hsmul : toChart ((x : K) • omega) = (x : K) • toChart omega :=
    weilDifferentialAddEquivChart_smul (k := k) (K := K) x omega
  have hxchart : Chart.WeilDifferential.IsNonzero ((x : K) • toChart omega) := by
    simpa only [hsmul] using
      ((isNonzero_toChart ((x : K) • omega)).mp hxomega)
  have hchart := Chart.WeilDifferential.divOmega_smul (k := k) (K := K) x
    (toChart omega) ((isNonzero_toChart omega).mp homega) hxchart
  simpa [hsmul, principalDivisor] using hchart

end WeilDifferential

/-- A divisor is canonical when it is the divisor of a nonzero intrinsic Weil differential. -/
def IsCanonical (W : Divisor k K) : Prop :=
  ∃ (omega : WeilDifferential k K) (homega : WeilDifferential.IsNonzero omega),
    WeilDifferential.divOmega omega homega = W

/-- Intrinsic and chart definitions of canonical divisors agree. -/
theorem isCanonical_iff_chart (W : Divisor k K) :
    IsCanonical k K W ↔
      Chart.IsCanonical k K ((divisorEquivChart k K).symm W) := by
  constructor
  · rintro ⟨omega, homega, rfl⟩
    refine ⟨WeilDifferential.toChart omega,
      (WeilDifferential.isNonzero_toChart omega).mp homega, ?_⟩
    simp [WeilDifferential.divOmega]
  · rintro ⟨omega, homega, hdiv⟩
    let eta := WeilDifferential.ofChart omega
    have hetaChart : WeilDifferential.toChart eta = omega :=
      (WeilDifferential.weilDifferentialAddEquivChart
        (k := k) (K := K)).apply_symm_apply omega
    have heta : WeilDifferential.IsNonzero eta := by
      apply (WeilDifferential.isNonzero_toChart eta).mpr
      rw [hetaChart]
      exact homega
    refine ⟨eta, heta, ?_⟩
    apply (divisorEquivChart k K).symm.injective
    simp only [WeilDifferential.divOmega, AddEquiv.symm_apply_apply]
    simpa only [hetaChart] using hdiv

end FunctionField
