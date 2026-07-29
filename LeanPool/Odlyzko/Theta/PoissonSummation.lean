/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

namespace NumberField.Odlyzko

variable {ι : Type*}

/-- A torus quotient map used in the Odlyzko-bound argument. -/
def torusQuotientMap (x : ι → ℝ) : UnitAddTorus ι :=
  fun i ↦ (x i : UnitAddCircle)

theorem isOpenQuotientMap_torusQuotientMap :
    IsOpenQuotientMap (torusQuotientMap : (ι → ℝ) → UnitAddTorus ι) := by
  change IsOpenQuotientMap
    (Pi.map fun _ : ι ↦ ((↑) : ℝ → UnitAddCircle))
  exact IsOpenQuotientMap.piMap fun _ ↦
    QuotientAddGroup.isOpenQuotientMap_mk

theorem surjective_torusQuotientMap :
    Function.Surjective
      (torusQuotientMap : (ι → ℝ) → UnitAddTorus ι) :=
  isOpenQuotientMap_torusQuotientMap.surjective

theorem exists_intPi_add_of_torusQuotientMap_eq
    {x y : ι → ℝ} (h : torusQuotientMap x = torusQuotientMap y) :
    ∃ n : ι → ℤ, y = x + fun i ↦ (n i : ℝ) := by
  classical
  have hi (i : ι) :
      ∃ n : ℤ, y i = x i + (n : ℝ) := by
    have hz : ((y i - x i : ℝ) : UnitAddCircle) = 0 := by
      change (y i : UnitAddCircle) - (x i : UnitAddCircle) = 0
      rw [sub_eq_zero]
      exact (congrFun h i).symm
    obtain ⟨n, hn⟩ :=
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
    grind
  choose n hn using hi
  exact ⟨n, funext hn⟩

theorem torusQuotientMap_add_intPi
    (x : ι → ℝ) (n : ι → ℤ) :
    torusQuotientMap (x + fun i ↦ (n i : ℝ)) =
      torusQuotientMap x := by
  ext i
  simp [torusQuotientMap]

/-- An int periodization used in the Odlyzko-bound argument. -/
noncomputable def intPeriodization (f : (ι → ℝ) → ℂ) (x : ι → ℝ) : ℂ :=
  ∑' n : ι → ℤ, f (x + fun i ↦ (n i : ℝ))

theorem intPeriodization_add_intPi
    (f : (ι → ℝ) → ℂ) (x : ι → ℝ) (k : ι → ℤ) :
    intPeriodization f (x + fun i ↦ (k i : ℝ)) =
      intPeriodization f x := by
  unfold intPeriodization
  calc
    (∑' n : ι → ℤ,
        f ((x + fun i ↦ (k i : ℝ)) + fun i ↦ (n i : ℝ))) =
        ∑' n : ι → ℤ,
          f (x + fun i ↦ ((k + n) i : ℝ)) := by
      apply tsum_congr
      intro n
      congr 1
      funext i
      simp [add_assoc]
    _ = ∑' n : ι → ℤ, f (x + fun i ↦ (n i : ℝ)) :=
      Equiv.tsum_eq (Equiv.addLeft k)
        (fun n : ι → ℤ ↦ f (x + fun i ↦ (n i : ℝ)))

theorem intPeriodization_eq_of_torusQuotientMap_eq
    (f : (ι → ℝ) → ℂ) {x y : ι → ℝ}
    (h : torusQuotientMap x = torusQuotientMap y) :
    intPeriodization f x = intPeriodization f y := by
  obtain ⟨n, rfl⟩ := exists_intPi_add_of_torusQuotientMap_eq h
  exact (intPeriodization_add_intPi f x n).symm

/-- A torus lift used in the Odlyzko-bound argument. -/
noncomputable def torusLift {A : Type*} (f : (ι → ℝ) → A) :
    UnitAddTorus ι → A :=
  fun x ↦ f (Function.surjInv surjective_torusQuotientMap x)

theorem torusLift_comp_torusQuotientMap {A : Type*}
    (f : (ι → ℝ) → A)
    (hf : ∀ x y, torusQuotientMap x = torusQuotientMap y → f x = f y) :
    torusLift f ∘ torusQuotientMap = f := by
  funext x
  apply hf
  exact Function.rightInverse_surjInv
    surjective_torusQuotientMap (torusQuotientMap x)

theorem continuous_torusLift {A : Type*} [TopologicalSpace A]
    (f : (ι → ℝ) → A) (hfc : Continuous f)
    (hf : ∀ x y, torusQuotientMap x = torusQuotientMap y → f x = f y) :
    Continuous (torusLift f) := by
  apply isOpenQuotientMap_torusQuotientMap.continuous_comp_iff.mp
  simpa [torusLift_comp_torusQuotientMap f hf] using hfc

/-- A torus continuous map used in the Odlyzko-bound argument. -/
noncomputable def torusContinuousMap {A : Type*} [TopologicalSpace A]
    (f : (ι → ℝ) → A) (hfc : Continuous f)
    (hf : ∀ x y, torusQuotientMap x = torusQuotientMap y → f x = f y) :
    C(UnitAddTorus ι, A) :=
  ⟨torusLift f, continuous_torusLift f hfc hf⟩

@[simp]
theorem torusContinuousMap_comp_torusQuotientMap
    {A : Type*} [TopologicalSpace A]
    (f : (ι → ℝ) → A) (hfc : Continuous f)
    (hf : ∀ x y, torusQuotientMap x = torusQuotientMap y → f x = f y)
    (x : ι → ℝ) :
    torusContinuousMap f hfc hf (torusQuotientMap x) = f x :=
  congrFun (torusLift_comp_torusQuotientMap f hf) x

/-- A torus periodization used in the Odlyzko-bound argument. -/
noncomputable def torusPeriodization
    (f : (ι → ℝ) → ℂ) (hf : Continuous (intPeriodization f)) :
    C(UnitAddTorus ι, ℂ) :=
  torusContinuousMap (intPeriodization f) hf
    (fun _x _y h ↦ intPeriodization_eq_of_torusQuotientMap_eq f h)

@[simp]
theorem torusPeriodization_apply_quotient
    (f : (ι → ℝ) → ℂ) (hf : Continuous (intPeriodization f))
    (x : ι → ℝ) :
    torusPeriodization f hf (torusQuotientMap x) =
      intPeriodization f x :=
  torusContinuousMap_comp_torusQuotientMap _ _ _ x

end NumberField.Odlyzko

namespace NumberField.Odlyzko

variable {ι : Type*} [Fintype ι]

theorem mFourier_torusQuotientMap
    (n : ι → ℤ) (x : ι → ℝ) :
    UnitAddTorus.mFourier n (torusQuotientMap x) =
      Complex.exp (2 * Real.pi * Complex.I *
        ∑ i, (n i : ℂ) * (x i : ℂ)) := by
  simp only [UnitAddTorus.mFourier, torusQuotientMap,
    ContinuousMap.coe_mk, fourier_coe_apply]
  rw [← Complex.exp_sum]
  push_cast
  rw [Finset.mul_sum]
  ring_nf

theorem mFourier_neg_torusQuotientMap
    (n : ι → ℤ) (x : ι → ℝ) :
    UnitAddTorus.mFourier (-n) (torusQuotientMap x) =
      Complex.exp (-2 * Real.pi * Complex.I *
        ∑ i, (n i : ℂ) * (x i : ℂ)) := by
  rw [mFourier_torusQuotientMap]
  simp

@[simp]
theorem norm_mFourier_torusQuotientMap
    (n : ι → ℤ) (x : ι → ℝ) :
    ‖UnitAddTorus.mFourier n (torusQuotientMap x)‖ = 1 := by
  simp only [UnitAddTorus.mFourier, torusQuotientMap,
    ContinuousMap.coe_mk, norm_prod, fourier_coe_apply]
  apply Finset.prod_eq_one
  intro i _
  rw [Complex.norm_exp]
  simp

end NumberField.Odlyzko

section

open Module Submodule
open scoped RealInnerProductSpace

namespace NumberField.Odlyzko

variable {E : Type*} [NormedAddCommGroup E]

theorem innerBilin_nondegenerate [InnerProductSpace ℝ E] :
    (innerₗ E).Nondegenerate := by
  constructor
  · intro x hx
    exact inner_self_eq_zero.mp (hx x)
  · intro x hx
    exact inner_self_eq_zero.mp (hx x)

/-- A dual real basis used in the Odlyzko-bound argument. -/
noncomputable def dualRealBasis [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Finite ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    Basis ι ℝ E :=
  LinearMap.BilinForm.dualBasis (innerₗ E) innerBilin_nondegenerate
    (b.ofZLatticeBasis ℝ L)

theorem inner_dualRealBasis_apply [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Finite ι] [DecidableEq ι] (b : Basis ι ℤ L)
    (i : ι) (x : E) :
    inner ℝ (dualRealBasis L b i) x =
      (b.ofZLatticeBasis ℝ L).repr x i := by
  change (innerₗ E) (dualRealBasis L b i) x = _
  simp [dualRealBasis, LinearMap.BilinForm.dualBasis,
    Basis.coe_dualBasis]

/-- A dual lattice used in the Odlyzko-bound argument. -/
noncomputable def dualLattice [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) : Submodule ℤ E :=
  LinearMap.BilinForm.dualSubmodule (innerₗ E) L

theorem mem_dualLattice_iff [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) (y : E) :
    y ∈ dualLattice L ↔ ∀ x : L, ∃ n : ℤ, inner ℝ y (x : E) = n := by
  constructor
  · intro hy x
    obtain ⟨n, hn⟩ := Submodule.mem_one.mp (hy x x.2)
    exact ⟨n, hn.symm⟩
  · intro hy x hx
    obtain ⟨n, hn⟩ := hy ⟨x, hx⟩
    simp_all

theorem span_range_dualRealBasis [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Finite ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    span ℤ (Set.range (dualRealBasis L b)) = dualLattice L := by
  unfold dualLattice dualRealBasis
  calc
    span ℤ (Set.range (LinearMap.BilinForm.dualBasis (innerₗ E)
      innerBilin_nondegenerate (b.ofZLatticeBasis ℝ L))) =
        LinearMap.BilinForm.dualSubmodule (innerₗ E)
          (span ℤ (Set.range (b.ofZLatticeBasis ℝ L))) :=
      (LinearMap.BilinForm.dualSubmodule_span_of_basis
        (innerₗ E) innerBilin_nondegenerate (b.ofZLatticeBasis ℝ L)).symm
    _ = LinearMap.BilinForm.dualSubmodule (innerₗ E) L := by
      rw [b.ofZLatticeBasis_span ℝ]

instance dualLattice.instDiscreteTopology [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    DiscreteTopology (dualLattice L) := by
  classical
  rw [← span_range_dualRealBasis L (Free.chooseBasis ℤ L)]
  infer_instance

/-- A dual lattice basis used in the Odlyzko-bound argument. -/
noncomputable def dualLatticeBasis [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Finite ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    Basis ι ℤ (dualLattice L) :=
  ((dualRealBasis L b).restrictScalars ℤ).map
    (LinearEquiv.ofEq _ _ (span_range_dualRealBasis L b))

@[simp]
theorem dualLatticeBasis_apply_coe [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Finite ι] [DecidableEq ι] (b : Basis ι ℤ L)
    (i : ι) :
    ((dualLatticeBasis L b i : dualLattice L) : E) =
      dualRealBasis L b i := by
  rw [dualLatticeBasis, Basis.map_apply]
  simp

end NumberField.Odlyzko

end

section

open Filter Asymptotics
open scoped Topology

namespace NumberField.Odlyzko

variable {E : Type*} [NormedAddCommGroup E]

/-- A lattice gaussian used in the Odlyzko-bound argument. -/
noncomputable def latticeGaussian (a : ℝ) (x : E) : ℂ :=
  Complex.exp (-(a : ℂ) * (‖x‖ : ℂ) ^ 2)

theorem norm_latticeGaussian (a : ℝ) (x : E) :
    ‖latticeGaussian a x‖ = Real.exp (-a * ‖x‖ ^ 2) := by
  have hvalue :
      latticeGaussian a x =
        ((Real.exp (-a * ‖x‖ ^ 2) : ℝ) : ℂ) := by
    unfold latticeGaussian
    simp
  rw [hvalue, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]

theorem norm_latticeGaussian_add_le
    {a : ℝ} (ha : 0 ≤ a) (y z : E) :
    ‖latticeGaussian a (y + z)‖ ≤
      Real.exp (a * ‖y‖ ^ 2) * ‖latticeGaussian (a / 2) z‖ := by
  rw [norm_latticeGaussian, norm_latticeGaussian, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have htri : ‖z‖ ≤ ‖y + z‖ + ‖y‖ := by
    calc
      ‖z‖ = ‖(y + z) - y‖ := by simp
      _ ≤ ‖y + z‖ + ‖y‖ := norm_sub_le _ _
  have hsquare :
      ‖z‖ ^ 2 ≤ 2 * ‖y + z‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg (‖y + z‖ - ‖y‖),
      norm_nonneg z, norm_nonneg (y + z), norm_nonneg y]
  nlinarith

theorem summable_latticeGaussian [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] {a : ℝ} (ha : 0 < a) :
    Summable (fun x : L ↦ latticeGaussian a (x : E)) := by
  let r : ℝ := -(Module.finrank ℤ L + 1)
  have hr : r < -(Module.finrank ℤ L : ℝ) := by grind
  have hclosed : IsClosed (L : Set E) :=
    by
      change IsClosed (L.toAddSubgroup : Set E)
      exact AddSubgroup.isClosed_of_discrete
  have htend :
      Tendsto (norm ∘ ((↑) : L → E)) cofinite atTop :=
    tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding
      hclosed.isClosedEmbedding_subtypeVal
  have hdecay :=
    (rexp_neg_quadratic_isLittleO_rpow_atTop
      (a := -a) (b := 0) (by grind) r).isBigO.comp_tendsto htend
  have hreal :
      Summable (fun x : L ↦ Real.exp (-a * ‖(x : E)‖ ^ 2)) := by
    obtain ⟨c, hc, hbound⟩ := hdecay.exists_pos
    apply ((ZLattice.summable_norm_rpow L r hr).mul_left c).of_norm_bounded_eventually
    filter_upwards [hbound.bound] with x hx
    simpa [Function.comp_apply, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using hx
  apply hreal.of_norm_bounded
  intro x
  rw [norm_latticeGaussian]

end NumberField.Odlyzko

end

section

open Module

namespace NumberField.Odlyzko

variable {E : Type*} [NormedAddCommGroup E]

/-- A lattice theta used in the Odlyzko-bound argument. -/
noncomputable def latticeTheta
    (L : Submodule ℤ E) (a : ℝ) : ℂ :=
  ∑' x : L, latticeGaussian a (x : E)

theorem latticeTheta_map_linearIsometryEquiv [NormedSpace ℝ E]
    (L : Submodule ℤ E) (e : E ≃ₗᵢ[ℝ] E) (a : ℝ) :
    latticeTheta
        (L.map (e.toLinearEquiv.restrictScalars ℤ).toLinearMap) a =
      latticeTheta L a := by
  let eZ : E ≃ₗ[ℤ] E := e.toLinearEquiv.restrictScalars ℤ
  let eL :
      L ≃ₗ[ℤ] L.map eZ.toLinearMap :=
    Submodule.equivMapOfInjective eZ.toLinearMap eZ.injective L
  rw [latticeTheta, latticeTheta, ← eL.toEquiv.tsum_eq]
  apply tsum_congr
  intro x
  unfold latticeGaussian
  rw [show ((eL.toEquiv x : L.map eZ.toLinearMap) : E) = e x by rfl,
    e.norm_map]

theorem summable_latticeTheta [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] {a : ℝ} (ha : 0 < a) :
    Summable (fun x : L ↦ latticeGaussian a (x : E)) :=
  summable_latticeGaussian L ha

/-- A dual lattice theta used in the Odlyzko-bound argument. -/
noncomputable def dualLatticeTheta [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) (a : ℝ) : ℂ :=
  latticeTheta (dualLattice L) a

end NumberField.Odlyzko

end

section

open Module
open scoped RealInnerProductSpace

namespace NumberField.Odlyzko

variable {E : Type*} [NormedAddCommGroup E] {ι : Type*} [Fintype ι]

/-- A lattice point used in the Odlyzko-bound argument. -/
noncomputable def latticePoint (L : Submodule ℤ E) (b : Basis ι ℤ L) (n : ι → ℤ) : E :=
  (b.equivFun.symm n : L)

/-- A dual lattice point used in the Odlyzko-bound argument. -/
noncomputable def dualLatticePoint [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] [DecidableEq ι]
    (b : Basis ι ℤ L) (n : ι → ℤ) : E :=
  ((dualLatticeBasis L b).equivFun.symm n : dualLattice L)

theorem inner_dualLatticePoint_ofZLatticeBasis_equivFun_symm
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] [DecidableEq ι]
    (b : Basis ι ℤ L) (n : ι → ℤ) (x : ι → ℝ) :
    inner ℝ (dualLatticePoint L b n)
        ((b.ofZLatticeBasis ℝ L).equivFun.symm x) =
      ∑ i, (n i : ℝ) * x i := by
  rw [dualLatticePoint, Basis.equivFun_symm_apply]
  have hn :
      ((↑(∑ i, n i • dualLatticeBasis L b i) :
          dualLattice L) : E) =
        ∑ i, (n i : ℝ) • dualRealBasis L b i := by
    change (dualLattice L).subtype
      (∑ i, n i • dualLatticeBasis L b i) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_zsmul]
    have hd :
        (dualLattice L).subtype (dualLatticeBasis L b i) =
          dualRealBasis L b i :=
      dualLatticeBasis_apply_coe L b i
    rw [hd]
    exact (Int.cast_smul_eq_zsmul ℝ (n i)
      (dualRealBasis L b i)).symm
  rw [hn, sum_inner]
  have hrepr (i : ι) :
      (b.ofZLatticeBasis ℝ L).repr
          ((b.ofZLatticeBasis ℝ L).equivFun.symm x) i = x i := by
    change (b.ofZLatticeBasis ℝ L).equivFun
      ((b.ofZLatticeBasis ℝ L).equivFun.symm x) i = x i
    rw [LinearEquiv.apply_symm_apply]
  simp_rw [real_inner_smul_left,
    inner_dualRealBasis_apply, hrepr]

theorem latticeTheta_eq_tsum_coordinates
    (L : Submodule ℤ E) (b : Basis ι ℤ L) (a : ℝ) :
    latticeTheta L a =
      ∑' n : ι → ℤ, latticeGaussian a (latticePoint L b n) := by
  symm
  simpa [latticeTheta, latticePoint] using
    (Equiv.tsum_eq b.equivFun.toEquiv.symm
      (fun x : L ↦ latticeGaussian a (x : E)))

theorem dualLatticeTheta_eq_tsum_coordinates
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] [DecidableEq ι]
    (b : Basis ι ℤ L) (a : ℝ) :
    dualLatticeTheta L a =
      ∑' n : ι → ℤ, latticeGaussian a (dualLatticePoint L b n) := by
  symm
  simpa [dualLatticeTheta, latticeTheta, dualLatticePoint] using
    (Equiv.tsum_eq (dualLatticeBasis L b).equivFun.toEquiv.symm
      (fun x : dualLattice L ↦ latticeGaussian a (x : E)))

end NumberField.Odlyzko

end

section

open Module

namespace NumberField.Odlyzko

variable {E : Type*} [NormedAddCommGroup E] {ι : Type*} [Fintype ι]

/-- A coordinate gaussian used in the Odlyzko-bound argument. -/
noncomputable def coordinateGaussian [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (a : ℝ) (x : ι → ℝ) : ℂ :=
  latticeGaussian a ((b.ofZLatticeBasis ℝ L).equivFun.symm x)

/-- A coordinate basis map used in the Odlyzko-bound argument. -/
noncomputable def coordinateBasisMap [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) :
    C(ι → ℝ, E) :=
  let e := LinearEquiv.toContinuousLinearEquiv
    (b.ofZLatticeBasis ℝ L).equivFun.symm
  ⟨e, e.continuous⟩

theorem continuous_coordinateGaussian [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (a : ℝ) :
    Continuous (coordinateGaussian L b a) := by
  classical
  unfold coordinateGaussian latticeGaussian
  have hlin : Continuous fun x : ι → ℝ ↦
      (b.ofZLatticeBasis ℝ L).equivFun.symm x :=
    (LinearEquiv.toContinuousLinearEquiv
      (b.ofZLatticeBasis ℝ L).equivFun.symm).continuous
  fun_prop

theorem ofZLatticeBasis_equivFun_symm_intCast
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (n : ι → ℤ) :
    (b.ofZLatticeBasis ℝ L).equivFun.symm (fun i ↦ (n i : ℝ)) =
      latticePoint L b n := by
  rw [Basis.equivFun_symm_apply, latticePoint,
    Basis.equivFun_symm_apply]
  have hcoe :
      ((↑(∑ i, n i • b i) : L) : E) =
        ∑ i, n i • (b i : E) := by simp
  rw [hcoe]
  apply Finset.sum_congr rfl
  intro i _
  rw [Basis.ofZLatticeBasis_apply]
  exact Int.cast_smul_eq_zsmul ℝ (n i) (b i : E)

/-- A coordinate gaussian translate used in the Odlyzko-bound argument. -/
noncomputable def coordinateGaussianTranslate
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (a : ℝ) (n : ι → ℤ) :
    C(ι → ℝ, ℂ) :=
  ⟨fun x ↦ coordinateGaussian L b a
      (x + fun i ↦ (n i : ℝ)),
    (continuous_coordinateGaussian L b a).comp
      (continuous_id.add (continuous_pi fun _ ↦ continuous_const))⟩

theorem summable_norm_latticeGaussian_latticePoint
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ι → ℤ ↦
      ‖latticeGaussian a (latticePoint L b n)‖) := by
  have hs := (Equiv.summable_iff
    (e := b.equivFun.toEquiv.symm)).mpr
      (summable_latticeGaussian L ha).norm
  simpa [Function.comp_def, latticePoint] using hs

theorem norm_coordinateGaussianTranslate_apply_le
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a)
    (x : ι → ℝ) (n : ι → ℤ) :
    ‖coordinateGaussianTranslate L b a n x‖ ≤
      Real.exp (a * ‖coordinateBasisMap L b x‖ ^ 2) *
        ‖latticeGaussian (a / 2) (latticePoint L b n)‖ := by
  classical
  change ‖coordinateGaussian L b a
      (x + fun i ↦ (n i : ℝ))‖ ≤ _
  have hsplit :
      (b.ofZLatticeBasis ℝ L).equivFun.symm
          (x + fun i ↦ (n i : ℝ)) =
        coordinateBasisMap L b x + latticePoint L b n := by
    rw [map_add, ofZLatticeBasis_equivFun_symm_intCast]
    rfl
  rw [coordinateGaussian, hsplit]
  exact norm_latticeGaussian_add_le ha.le _ _

theorem norm_restrict_coordinateGaussianTranslate_le
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a)
    (K : TopologicalSpace.Compacts (ι → ℝ)) (n : ι → ℤ) :
    ‖(coordinateGaussianTranslate L b a n).restrict K‖ ≤
      Real.exp (a * ‖(coordinateBasisMap L b).restrict K‖ ^ 2) *
        ‖latticeGaussian (a / 2) (latticePoint L b n)‖ := by
  classical
  apply (ContinuousMap.norm_le _ (mul_nonneg (Real.exp_pos _).le
    (norm_nonneg _))).2
  intro x
  refine (norm_coordinateGaussianTranslate_apply_le
    L b ha x n).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ ha.le
  have hx := ContinuousMap.norm_coe_le_norm
    ((coordinateBasisMap L b).restrict K) x
  change ‖coordinateBasisMap L b (x : ι → ℝ)‖ ≤
    ‖(coordinateBasisMap L b).restrict K‖ at hx
  nlinarith [norm_nonneg (coordinateBasisMap L b x),
    norm_nonneg ((coordinateBasisMap L b).restrict K)]

theorem summable_norm_restrict_coordinateGaussianTranslate
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a)
    (K : TopologicalSpace.Compacts (ι → ℝ)) :
    Summable (fun n : ι → ℤ ↦
      ‖(coordinateGaussianTranslate L b a n).restrict K‖) := by
  classical
  let C := Real.exp
    (a * ‖(coordinateBasisMap L b).restrict K‖ ^ 2)
  have hbase := summable_norm_latticeGaussian_latticePoint
    L b (half_pos ha)
  apply (hbase.mul_left C).of_norm_bounded
  intro n
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact norm_restrict_coordinateGaussianTranslate_le L b ha K n

private theorem summable_coordinateGaussianTranslate
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) :
    Summable (coordinateGaussianTranslate L b a) := by
  classical
  apply ContinuousMap.summable_of_locally_summable_norm
  intro K
  exact summable_norm_restrict_coordinateGaussianTranslate L b ha K

theorem continuous_intPeriodization_coordinateGaussian
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) :
    Continuous (intPeriodization (coordinateGaussian L b a)) := by
  classical
  let F := coordinateGaussianTranslate L b a
  have hF : Summable F :=
    summable_coordinateGaussianTranslate L b ha
  have hcontinuous : Continuous fun x : ι → ℝ ↦ (∑' n, F n) x :=
    (∑' n, F n).continuous
  have heval (x : ι → ℝ) :
      (∑' n, F n) x =
        intPeriodization (coordinateGaussian L b a) x := by
    calc
      (∑' n, F n) x = ∑' n, (F n) x :=
        (ContinuousMap.tsum_apply hF x).symm
      _ = intPeriodization (coordinateGaussian L b a) x := rfl
  simp_all

/-- A gaussian torus periodization used in the Odlyzko-bound argument. -/
noncomputable def gaussianTorusPeriodization
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (a : ℝ) (ha : 0 < a) :
    C(UnitAddTorus ι, ℂ) :=
  torusPeriodization (coordinateGaussian L b a)
    (continuous_intPeriodization_coordinateGaussian L b ha)

theorem gaussianTorusPeriodization_zero
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) :
    gaussianTorusPeriodization L b a ha 0 = latticeTheta L a := by
  classical
  rw [show (0 : UnitAddTorus ι) =
      torusQuotientMap (0 : ι → ℝ) by rfl]
  rw [gaussianTorusPeriodization,
    torusPeriodization_apply_quotient]
  unfold intPeriodization coordinateGaussian
  simp_rw [zero_add,
    ofZLatticeBasis_equivFun_symm_intCast]
  exact (latticeTheta_eq_tsum_coordinates L b a).symm

end NumberField.Odlyzko

end

section

open Module Submodule MeasureTheory Set

namespace NumberField.Odlyzko

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A coordinate int lattice used in the Odlyzko-bound argument. -/
noncomputable def coordinateIntLattice : Submodule ℤ (ι → ℝ) :=
  span ℤ (Set.range (Pi.basisFun ℝ ι))

/-- A coordinate int basis used in the Odlyzko-bound argument. -/
noncomputable def coordinateIntBasis :
    Basis ι ℤ (coordinateIntLattice (ι := ι)) :=
  (Pi.basisFun ℝ ι).restrictScalars ℤ

/-- A coordinate int point used in the Odlyzko-bound argument. -/
noncomputable def coordinateIntPoint (n : ι → ℤ) :
    coordinateIntLattice (ι := ι) :=
  (coordinateIntBasis (ι := ι)).equivFun.symm n

omit [DecidableEq ι] in
@[simp]
theorem coordinateIntPoint_apply (n : ι → ℤ) (i : ι) :
    (coordinateIntPoint n : ι → ℝ) i = n i := by
  classical
  rw [coordinateIntPoint, Basis.equivFun_symm_apply]
  change (coordinateIntLattice (ι := ι)).subtype
    (∑ j, n j • coordinateIntBasis j) i = _
  rw [map_sum]
  simp_rw [map_zsmul]
  rw [Finset.sum_apply]
  have hb (j : ι) :
      (coordinateIntLattice (ι := ι)).subtype
        (coordinateIntBasis j) =
          Pi.basisFun ℝ ι j :=
    Basis.restrictScalars_apply ℤ (Pi.basisFun ℝ ι) j
  simp_rw [hb]
  simp only [Pi.basisFun_apply, Pi.smul_apply, zsmul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · simp_all
  · simp

omit [DecidableEq ι] in
theorem pi_Ioc_ae_eq_pi_Ico :
    ({x : ι → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1} : Set (ι → ℝ)) =ᵐ[volume]
      {x : ι → ℝ | ∀ i, x i ∈ Ico (0 : ℝ) 1} := by
  have hioc :
      ({x : ι → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1} : Set (ι → ℝ)) =
        Set.pi Set.univ fun _ : ι ↦ Ioc (0 : ℝ) 1 := by grind
  have hico :
      ({x : ι → ℝ | ∀ i, x i ∈ Ico (0 : ℝ) 1} : Set (ι → ℝ)) =
        Set.pi Set.univ fun _ : ι ↦ Ico (0 : ℝ) 1 := by
    ext
    simp
  rw [hioc, hico, MeasureTheory.volume_pi]
  exact (Measure.pi_Ioc_ae_eq_pi_Icc.trans
    Measure.pi_Ico_ae_eq_pi_Icc.symm)

omit [DecidableEq ι] in
theorem integral_eq_tsum_integral_pi_Ico
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (f : (ι → ℝ) → A) (hf : Integrable f) :
    ∫ x, f x =
      ∑' n : ι → ℤ,
        ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ico 0 1},
          f ((fun i ↦ (n i : ℝ)) + x) := by
  classical
  letI : VAddInvariantMeasure
      (span ℤ (Set.range (Pi.basisFun ℝ ι))) (ι → ℝ) volume :=
    ⟨fun c s _ ↦ measure_preimage_add volume (c : ι → ℝ) s⟩
  have hfund :=
    (ZSpan.isAddFundamentalDomain
      (Pi.basisFun ℝ ι) volume).integral_eq_tsum'' f hf
  rw [ZSpan.fundamentalDomain_pi_basisFun] at hfund
  have hset :
      (Set.pi Set.univ fun _ : ι ↦ Ico (0 : ℝ) 1) =
        {x : ι → ℝ | ∀ i, x i ∈ Ico 0 1} := by grind
  rw [hset] at hfund
  have hvadd
      (z : span ℤ (Set.range (Pi.basisFun ℝ ι)))
      (x : ι → ℝ) :
      z +ᵥ x = (z : ι → ℝ) + x := rfl
  simp_rw [hvadd] at hfund
  calc
    ∫ x, f x =
        ∑' z : coordinateIntLattice (ι := ι),
          ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ico 0 1},
            f ((z : ι → ℝ) + x) := by
      simpa [coordinateIntLattice] using hfund
    _ = ∑' n : ι → ℤ,
          ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ico 0 1},
            f ((coordinateIntPoint n : ι → ℝ) + x) := by
      exact (Equiv.tsum_eq
        (coordinateIntBasis (ι := ι)).equivFun.toEquiv.symm _).symm
    _ = _ := by
      apply tsum_congr
      intro n
      congr 1
      funext x
      congr 2
      funext i
      simp

omit [DecidableEq ι] in
theorem integral_eq_tsum_integral_pi_Ioc
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (f : (ι → ℝ) → A) (hf : Integrable f) :
    ∫ x, f x =
      ∑' n : ι → ℤ,
        ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ioc 0 1},
          f ((fun i ↦ (n i : ℝ)) + x) := by
  classical
  rw [integral_eq_tsum_integral_pi_Ico f hf]
  apply tsum_congr
  intro n
  exact setIntegral_congr_set pi_Ioc_ae_eq_pi_Ico.symm

end NumberField.Odlyzko

end

section

open Module MeasureTheory Set

namespace NumberField.Odlyzko

variable {E : Type*} [NormedAddCommGroup E] {ι : Type*} [Fintype ι]

/-- A coordinate fourier character used in the Odlyzko-bound argument. -/
noncomputable def coordinateFourierCharacter
    (n : ι → ℤ) (x : ι → ℝ) : ℂ :=
  UnitAddTorus.mFourier (-n) (torusQuotientMap x)

private theorem continuous_coordinateFourierCharacter (n : ι → ℤ) :
    Continuous (coordinateFourierCharacter n) := by
  unfold coordinateFourierCharacter
  exact (UnitAddTorus.mFourier (-n)).continuous.comp
    (continuous_pi fun i ↦
      continuous_quotient_mk'.comp (continuous_apply i))

theorem measurableSet_pi_Ioc {κ : Type*} [Finite κ] :
    MeasurableSet {x : κ → ℝ | ∀ i, x i ∈ Ioc 0 1} := by
  letI := Fintype.ofFinite κ
  rw [setOf_forall]
  apply MeasurableSet.iInter
  intro i
  have hi : Measurable (fun x : κ → ℝ ↦ x i) := measurable_pi_apply i
  exact measurableSet_Ioc.preimage hi

@[simp]
theorem norm_coordinateFourierCharacter
    (n : ι → ℤ) (x : ι → ℝ) :
    ‖coordinateFourierCharacter n x‖ = 1 :=
  norm_mFourier_torusQuotientMap (-n) x

/-- A coordinate fourier gaussian used in the Odlyzko-bound argument. -/
noncomputable def coordinateFourierGaussian
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (a : ℝ) (n : ι → ℤ) (x : ι → ℝ) : ℂ :=
  coordinateFourierCharacter n x * coordinateGaussian L b a x

/-- A coordinate fourier gaussian translate used in the Odlyzko-bound argument. -/
noncomputable def coordinateFourierGaussianTranslate
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (a : ℝ) (n k : ι → ℤ)
    (x : ι → ℝ) : ℂ :=
  coordinateFourierCharacter n x * coordinateGaussianTranslate L b a k x

theorem continuous_coordinateFourierGaussianTranslate
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (a : ℝ) (n k : ι → ℤ) :
    Continuous (coordinateFourierGaussianTranslate L b a n k) := by
  classical
  exact (continuous_coordinateFourierCharacter n).mul
    (coordinateGaussianTranslate L b a k).continuous

private theorem coordinateFourierCharacter_add_intPi
    (n k : ι → ℤ) (x : ι → ℝ) :
    coordinateFourierCharacter n ((fun i ↦ (k i : ℝ)) + x) =
      coordinateFourierCharacter n x := by
  unfold coordinateFourierCharacter
  congr 1
  rw [add_comm]
  exact torusQuotientMap_add_intPi x k

theorem coordinateFourierGaussian_add_intPi
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (a : ℝ) (n k : ι → ℤ) (x : ι → ℝ) :
    coordinateFourierGaussian L b a n
        ((fun i ↦ (k i : ℝ)) + x) =
      coordinateFourierGaussianTranslate L b a n k x := by
  classical
  rw [coordinateFourierGaussian,
    coordinateFourierGaussianTranslate,
    coordinateFourierCharacter_add_intPi]
  congr 1
  exact congrArg (coordinateGaussian L b a) (add_comm _ _)

theorem summable_integral_norm_coordinateFourierGaussianTranslate
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) (n : ι → ℤ) :
    Summable (fun k : ι → ℤ ↦
      ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ioc 0 1},
        ‖coordinateFourierGaussianTranslate L b a n k x‖) := by
  classical
  let S : Set (ι → ℝ) := {x | ∀ i, x i ∈ Ioc 0 1}
  let K : TopologicalSpace.Compacts (ι → ℝ) :=
    ⟨Icc (0 : ι → ℝ) 1, isCompact_Icc⟩
  have hSK : S ⊆ K := by
    intro x hx
    exact ⟨fun i ↦ (hx i).1.le, fun i ↦ (hx i).2⟩
  have hS : MeasurableSet S := by
    dsimp [S]
    exact measurableSet_pi_Ioc
  have hKsum :=
    summable_norm_restrict_coordinateGaussianTranslate L b ha K
  have hmeasure : volume S < (⊤ : ENNReal) :=
    lt_of_le_of_lt (measure_mono hSK) K.2.measure_lt_top
  have hbound (k : ι → ℤ) :
      ∫ x in S,
          ‖coordinateFourierGaussianTranslate L b a n k x‖ ≤
        volume.real S *
          ‖(coordinateGaussianTranslate L b a k).restrict K‖ := by
    have hInt :
        IntegrableOn
          (fun x ↦ ‖coordinateFourierGaussianTranslate L b a n k x‖)
          S := by
      exact ((continuous_coordinateFourierGaussianTranslate
        L b a n k).norm.integrableOn_Icc).mono_set hSK
    have hConst :
        IntegrableOn (fun _ : ι → ℝ ↦
          ‖(coordinateGaussianTranslate L b a k).restrict K‖) S :=
      integrableOn_const (ne_of_lt hmeasure)
    calc
      ∫ x in S,
          ‖coordinateFourierGaussianTranslate L b a n k x‖ ≤
          ∫ _x in S,
            ‖(coordinateGaussianTranslate L b a k).restrict K‖ := by
        apply integral_mono_ae hInt hConst
        filter_upwards [ae_restrict_mem hS] with x hx
        rw [coordinateFourierGaussianTranslate, norm_mul,
          norm_coordinateFourierCharacter, one_mul]
        exact ContinuousMap.norm_coe_le_norm
          ((coordinateGaussianTranslate L b a k).restrict K) ⟨x, hSK hx⟩
      _ = volume.real S *
          ‖(coordinateGaussianTranslate L b a k).restrict K‖ := by simp
  apply Summable.of_nonneg_of_le
      (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) hbound
  exact hKsum.mul_left (volume.real S)

theorem integral_tsum_coordinateFourierGaussianTranslate
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) (n : ι → ℤ) :
    ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ioc 0 1},
        ∑' k : ι → ℤ,
          coordinateFourierGaussianTranslate L b a n k x =
      ∑' k : ι → ℤ,
        ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ioc 0 1},
          coordinateFourierGaussianTranslate L b a n k x := by
  classical
  symm
  apply integral_tsum_of_summable_integral_norm
  · intro k
    let S : Set (ι → ℝ) := {x | ∀ i, x i ∈ Ioc 0 1}
    let K : Set (ι → ℝ) := Icc 0 1
    have hSK : S ⊆ K := fun x hx ↦
      ⟨fun i ↦ (hx i).1.le, fun i ↦ (hx i).2⟩
    exact ((continuous_coordinateFourierGaussianTranslate
      L b a n k).integrableOn_Icc).mono_set hSK
  · exact summable_integral_norm_coordinateFourierGaussianTranslate
      L b ha n

theorem mFourierCoeff_gaussianTorusPeriodization
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) (n : ι → ℤ)
    (hint : Integrable (coordinateFourierGaussian L b a n)) :
    UnitAddTorus.mFourierCoeff
        (gaussianTorusPeriodization L b a ha) n =
      ∫ x, coordinateFourierGaussian L b a n x := by
  classical
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ n 0]
  simp only [Pi.zero_apply, zero_add]
  have hpoint (x : ι → ℝ) :
      UnitAddTorus.mFourier (-n) (torusQuotientMap x) •
          gaussianTorusPeriodization L b a ha
            (torusQuotientMap x) =
        ∑' k : ι → ℤ,
          coordinateFourierGaussianTranslate L b a n k x := by
    rw [gaussianTorusPeriodization,
      torusPeriodization_apply_quotient]
    unfold intPeriodization coordinateFourierGaussianTranslate
      coordinateFourierCharacter
    rw [smul_eq_mul, tsum_mul_left]
    rfl
  change
    (∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ioc 0 1},
      UnitAddTorus.mFourier (-n) (torusQuotientMap x) •
        gaussianTorusPeriodization L b a ha (torusQuotientMap x)) =
      ∫ x, coordinateFourierGaussian L b a n x
  simp_rw [hpoint]
  rw [integral_tsum_coordinateFourierGaussianTranslate L b ha n]
  rw [integral_eq_tsum_integral_pi_Ioc
    (coordinateFourierGaussian L b a n) hint]
  apply tsum_congr
  intro k
  apply setIntegral_congr_fun measurableSet_pi_Ioc
  intro x hx
  exact (coordinateFourierGaussian_add_intPi L b a n k x).symm

end NumberField.Odlyzko

end

section

open Module MeasureTheory

namespace NumberField.Odlyzko

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem map_ofZLatticeBasis_equivFun_symm_volume
    (b : Basis ι ℤ L) :
    Measure.map (b.ofZLatticeBasis ℝ L).equivFun.symm volume =
      (b.ofZLatticeBasis ℝ L).addHaar := by
  classical
  let e : (ι → ℝ) ≃L[ℝ] E :=
    LinearEquiv.toContinuousLinearEquiv
      (b.ofZLatticeBasis ℝ L).equivFun.symm
  have hcoord : (Pi.basisFun ℝ ι).addHaar =
      (volume : Measure (ι → ℝ)) := by
    rw [Basis.addHaar_def, Basis.parallelepiped_basisFun,
      addHaarMeasure_eq_volume_pi]
  rw [← hcoord]
  change Measure.map e (Pi.basisFun ℝ ι).addHaar =
    (b.ofZLatticeBasis ℝ L).addHaar
  rw [Basis.map_addHaar (Pi.basisFun ℝ ι) e]
  congr 1
  ext i
  simp [e]

omit [DecidableEq ι] in
theorem covolume_eq_volumeReal_parallelepiped
    (b : Basis ι ℤ L) :
    ZLattice.covolume L =
      volume.real
        ((b.ofZLatticeBasis ℝ L).parallelepiped : Set E) := by
  classical
  rw [ZLattice.covolume_eq_det_mul_measureReal L volume b
    (b.ofZLatticeBasis ℝ L)]
  have hfun :
      ((fun x : L ↦ (x : E)) ∘ b) =
        (b.ofZLatticeBasis ℝ L : ι → E) := by
    funext i
    simp
  rw [hfun, Basis.det_self, abs_one, one_mul]
  exact measureReal_congr
    (ZSpan.fundamentalDomain_ae_parallelepiped
      (b.ofZLatticeBasis ℝ L) volume)

omit [DecidableEq ι] in
theorem volume_parallelepiped_ofZLatticeBasis
    (b : Basis ι ℤ L) :
    volume ((b.ofZLatticeBasis ℝ L).parallelepiped : Set E) =
      ENNReal.ofReal (ZLattice.covolume L) := by
  classical
  have hfinite :
      volume ((b.ofZLatticeBasis ℝ L).parallelepiped : Set E) < ⊤ :=
    (b.ofZLatticeBasis ℝ L).parallelepiped.isCompact.measure_lt_top
  rw [covolume_eq_volumeReal_parallelepiped L b]
  exact (ENNReal.ofReal_toReal hfinite.ne).symm

omit [DecidableEq ι] in
theorem addHaar_ofZLatticeBasis_eq_inv_covolume_smul_volume
    (b : Basis ι ℤ L) :
    (b.ofZLatticeBasis ℝ L).addHaar =
      (Real.toNNReal (ZLattice.covolume L))⁻¹ • volume := by
  classical
  rw [Basis.addHaar_eq_iff]
  rw [Measure.smul_apply,
    volume_parallelepiped_ofZLatticeBasis L b]
  have hc : Real.toNNReal (ZLattice.covolume L) ≠ 0 := by
    rw [ne_eq, Real.toNNReal_eq_zero]
    exact not_le_of_gt (ZLattice.covolume_pos L)
  change
    (↑((Real.toNNReal (ZLattice.covolume L))⁻¹) : ENNReal) *
        ENNReal.ofReal (ZLattice.covolume L) = 1
  rw [ENNReal.coe_inv hc, ENNReal.ofNNReal_toNNReal]
  exact ENNReal.inv_mul_cancel
    (ENNReal.ofReal_ne_zero_iff.mpr (ZLattice.covolume_pos L))
    ENNReal.ofReal_ne_top

omit [DecidableEq ι] in
theorem integral_comp_ofZLatticeBasis_equivFun_symm
    (b : Basis ι ℤ L) (f : E → ℂ) :
    (∫ x : ι → ℝ,
        f ((b.ofZLatticeBasis ℝ L).equivFun.symm x)) =
      (Real.toNNReal (ZLattice.covolume L))⁻¹ •
        ∫ y : E, f y := by
  classical
  let e : (ι → ℝ) ≃ᵐ E :=
    (LinearEquiv.toContinuousLinearEquiv
      (b.ofZLatticeBasis ℝ L).equivFun.symm).toHomeomorph.toMeasurableEquiv
  change (∫ x : ι → ℝ, f (e x)) = _
  rw [← integral_map_equiv (μ := volume) e f]
  change (∫ y : E, f y ∂Measure.map
    (b.ofZLatticeBasis ℝ L).equivFun.symm volume) = _
  rw [map_ofZLatticeBasis_equivFun_symm_volume L b,
    addHaar_ofZLatticeBasis_eq_inv_covolume_smul_volume L b,
    integral_smul_nnreal_measure]

omit [DecidableEq ι] in
theorem integrable_comp_ofZLatticeBasis_equivFun_symm
    (b : Basis ι ℤ L) {f : E → ℂ} (hf : Integrable f) :
    Integrable
      (fun x : ι → ℝ ↦
        f ((b.ofZLatticeBasis ℝ L).equivFun.symm x)) := by
  classical
  let e : (ι → ℝ) ≃ᵐ E :=
    (LinearEquiv.toContinuousLinearEquiv
      (b.ofZLatticeBasis ℝ L).equivFun.symm).toHomeomorph.toMeasurableEquiv
  change Integrable (f ∘ e)
  rw [← integrable_map_equiv e f]
  change Integrable f (Measure.map
    (b.ofZLatticeBasis ℝ L).equivFun.symm volume)
  rw [
    map_ofZLatticeBasis_equivFun_symm_volume L b,
    addHaar_ofZLatticeBasis_eq_inv_covolume_smul_volume L b]
  exact hf.smul_measure_nnreal

end NumberField.Odlyzko

end

section

open Module MeasureTheory
open scoped RealInnerProductSpace

namespace NumberField.Odlyzko

variable {E : Type*} [NormedAddCommGroup E] {ι : Type*} [Fintype ι]

/-- An ambient fourier gaussian used in the Odlyzko-bound argument. -/
noncomputable def ambientFourierGaussian [InnerProductSpace ℝ E]
    (a : ℝ) (w y : E) : ℂ :=
  Complex.exp
    (-(a : ℂ) * (‖y‖ : ℂ) ^ 2 +
      (-2 * (Real.pi : ℂ) * Complex.I) * (inner ℝ w y : ℂ))

theorem integrable_ambientFourierGaussian
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {a : ℝ} (ha : 0 < a) (w : E) :
    Integrable (ambientFourierGaussian a w) := by
  have h :=
    GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (b := (a : ℂ)) (by simp_all) (-2 * (Real.pi : ℂ) * Complex.I) w
  convert h using 1 with y
  unfold ambientFourierGaussian
  simp

theorem coordinateFourierGaussian_eq_ambient
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] [DecidableEq ι]
    (b : Basis ι ℤ L) (a : ℝ) (n : ι → ℤ) (x : ι → ℝ) :
    coordinateFourierGaussian L b a n x =
      ambientFourierGaussian a (dualLatticePoint L b n)
        ((b.ofZLatticeBasis ℝ L).equivFun.symm x) := by
  rw [coordinateFourierGaussian, coordinateFourierCharacter,
    mFourier_neg_torusQuotientMap]
  unfold coordinateGaussian latticeGaussian ambientFourierGaussian
  rw [← Complex.exp_add]
  rw [inner_dualLatticePoint_ofZLatticeBasis_equivFun_symm L b n x]
  push_cast
  ring_nf

theorem integrable_coordinateFourierGaussian
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) (n : ι → ℤ) :
    Integrable (coordinateFourierGaussian L b a n) := by
  classical
  have h := integrable_comp_ofZLatticeBasis_equivFun_symm L b
    (integrable_ambientFourierGaussian
      (E := E) ha (dualLatticePoint L b n))
  apply h.congr
  filter_upwards with x
  exact (coordinateFourierGaussian_eq_ambient L b a n x).symm

theorem integral_ambientFourierGaussian
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {a : ℝ} (ha : 0 < a) (w : E) :
    (∫ y : E, ambientFourierGaussian a w y) =
      ((Real.pi : ℂ) / a) ^
          (Module.finrank ℝ E / 2 : ℂ) *
        Complex.exp
          (-(Real.pi : ℂ) ^ 2 * (‖w‖ : ℂ) ^ 2 / a) := by
  rw [← fourier_gaussian_innerProductSpace (b := (a : ℂ))
    (by simp_all) w]
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with y
  unfold ambientFourierGaussian
  rw [smul_eq_mul, ← Complex.exp_add]
  push_cast
  rw [real_inner_comm y w]
  ring_nf

theorem mFourierCoeff_gaussianTorusPeriodization_eq
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] [DecidableEq ι]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) (n : ι → ℤ) :
    UnitAddTorus.mFourierCoeff
        (gaussianTorusPeriodization L b a ha) n =
      (Real.toNNReal (ZLattice.covolume L))⁻¹ •
        (((Real.pi : ℂ) / a) ^
            (Module.finrank ℝ E / 2 : ℂ) *
          Complex.exp
            (-(Real.pi : ℂ) ^ 2 *
              (‖dualLatticePoint L b n‖ : ℂ) ^ 2 / a)) := by
  rw [mFourierCoeff_gaussianTorusPeriodization L b ha n
    (integrable_coordinateFourierGaussian L b ha n)]
  simp_rw [coordinateFourierGaussian_eq_ambient L b a n]
  rw [integral_comp_ofZLatticeBasis_equivFun_symm L b,
    integral_ambientFourierGaussian ha]

end NumberField.Odlyzko

end

section

open Module MeasureTheory

namespace NumberField.Odlyzko

variable {E : Type*} [NormedAddCommGroup E] {ι : Type*}

theorem exp_fourierGaussian_eq_latticeGaussian
    {a : ℝ} (_ha : 0 < a) (w : E) :
    Complex.exp
        (-(Real.pi : ℂ) ^ 2 * (‖w‖ : ℂ) ^ 2 / a) =
      latticeGaussian (Real.pi ^ 2 / a) w := by
  unfold latticeGaussian
  push_cast
  grind

theorem summable_mFourierCoeff_gaussianTorusPeriodization
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] [Fintype ι]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) :
    Summable
      (UnitAddTorus.mFourierCoeff
        (gaussianTorusPeriodization L b a ha)) := by
  classical
  have hp : 0 < Real.pi ^ 2 / a := div_pos (sq_pos_of_pos Real.pi_pos) ha
  have hdual :
      Summable (fun n : ι → ℤ ↦
        latticeGaussian (Real.pi ^ 2 / a)
          (dualLatticePoint L b n)) := by
    have hs := (Equiv.summable_iff
      (e := (dualLatticeBasis L b).equivFun.toEquiv.symm)).mpr
        (summable_latticeGaussian (dualLattice L) hp)
    simpa [Function.comp_def, dualLatticePoint] using hs
  let C : ℂ :=
    (Real.toNNReal (ZLattice.covolume L))⁻¹ •
      (((Real.pi : ℂ) / a) ^
        (Module.finrank ℝ E / 2 : ℂ))
  have hscaled : Summable (fun n : ι → ℤ ↦
      C * latticeGaussian (Real.pi ^ 2 / a)
        (dualLatticePoint L b n)) :=
    hdual.mul_left C
  apply hscaled.congr
  intro n
  rw [mFourierCoeff_gaussianTorusPeriodization_eq L b ha n,
    exp_fourierGaussian_eq_latticeGaussian ha]
  dsimp [C]
  simp

theorem latticeGaussian_poissonSummation_of_basis
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] [Finite ι]
    (b : Basis ι ℤ L) {a : ℝ} (ha : 0 < a) :
    latticeTheta L a =
      (Real.toNNReal (ZLattice.covolume L))⁻¹ •
        (((Real.pi : ℂ) / a) ^
            (Module.finrank ℝ E / 2 : ℂ) *
          dualLatticeTheta L (Real.pi ^ 2 / a)) := by
  classical
  letI := Fintype.ofFinite ι
  have hsummable :=
    summable_mFourierCoeff_gaussianTorusPeriodization L b ha
  have hseries :=
    UnitAddTorus.hasSum_mFourier_series_apply_of_summable
      hsummable (0 : UnitAddTorus ι)
  have hsum :
      (∑' n : ι → ℤ,
          UnitAddTorus.mFourierCoeff
            (gaussianTorusPeriodization L b a ha) n) =
        gaussianTorusPeriodization L b a ha 0 := by
    rw [← hseries.tsum_eq]
    apply tsum_congr
    intro n
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk,
      Pi.zero_apply, fourier_eval_zero, Finset.prod_const_one,
      smul_eq_mul, mul_one]
  rw [← gaussianTorusPeriodization_zero L b ha, ← hsum]
  simp_rw [mFourierCoeff_gaussianTorusPeriodization_eq L b ha,
    exp_fourierGaussian_eq_latticeGaussian ha]
  have hp : 0 < Real.pi ^ 2 / a := div_pos (sq_pos_of_pos Real.pi_pos) ha
  have hdual :
      Summable (fun n : ι → ℤ ↦
        latticeGaussian (Real.pi ^ 2 / a)
          (dualLatticePoint L b n)) := by
    have hs := (Equiv.summable_iff
      (e := (dualLatticeBasis L b).equivFun.toEquiv.symm)).mpr
        (summable_latticeGaussian (dualLattice L) hp)
    simpa [Function.comp_def, dualLatticePoint] using hs
  have hinner := hdual.mul_left
    (((Real.pi : ℂ) / a) ^
      (Module.finrank ℝ E / 2 : ℂ))
  let c : NNReal :=
    (Real.toNNReal (ZLattice.covolume L volume))⁻¹
  change
    (∑' n : ι → ℤ,
      c • (((Real.pi : ℂ) / a) ^
        (Module.finrank ℝ E / 2 : ℂ) *
        latticeGaussian (Real.pi ^ 2 / a)
          (dualLatticePoint L b n))) =
      c • (((Real.pi : ℂ) / a) ^
        (Module.finrank ℝ E / 2 : ℂ) *
        dualLatticeTheta L (Real.pi ^ 2 / a))
  rw [hinner.tsum_const_smul c]
  rw [tsum_mul_left]
  rw [← dualLatticeTheta_eq_tsum_coordinates L b]

theorem latticeGaussian_poissonSummation
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {a : ℝ} (ha : 0 < a) :
    latticeTheta L a =
      (Real.toNNReal (ZLattice.covolume L))⁻¹ •
        (((Real.pi : ℂ) / a) ^
            (Module.finrank ℝ E / 2 : ℂ) *
          dualLatticeTheta L (Real.pi ^ 2 / a)) := by
  let b := Free.chooseBasis ℤ L
  exact latticeGaussian_poissonSummation_of_basis L b ha

end NumberField.Odlyzko

end
