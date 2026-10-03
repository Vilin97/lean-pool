/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.Periodic
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Periodic volume-preserving diffeomorphisms -/

@[expose] public section

namespace AVenhance.Infra.Ergodic

open scoped ContDiff
open MeasureTheory
open scoped Pointwise

noncomputable section

/-- A smooth diffeomorphism of `Vec d` whose lift commutes with integer
lattice translations and which preserves Lebesgue measure. -/
structure PeriodicVolumePreservingDiffeomorphism (d : ℕ) where
  /-- Forward Euclidean diffeomorphism preserving the periodic lattice and volume. -/
  toFun : Homogenization.Vec d → Homogenization.Vec d
  /-- Inverse of the periodic volume-preserving diffeomorphism. -/
  invFun : Homogenization.Vec d → Homogenization.Vec d
  contDiff_toFun : ContDiff ℝ ∞ toFun
  contDiff_invFun : ContDiff ℝ ∞ invFun
  left_inv : Function.LeftInverse invFun toFun
  right_inv : Function.RightInverse invFun toFun
  lattice_equivariant : ∀ (x : Homogenization.Vec d) (k : Fin d → ℤ),
    toFun (x + latticeVector k) = toFun x + latticeVector k
  measurePreserving : MeasurePreserving toFun volume volume

instance {d : ℕ} : CoeFun (PeriodicVolumePreservingDiffeomorphism d)
    (fun _ => Homogenization.Vec d → Homogenization.Vec d) :=
  ⟨PeriodicVolumePreservingDiffeomorphism.toFun⟩

/-- Negative coordinate basis used to represent the periodic lattice. -/
noncomputable def Flow.negativeCoordinateBasis (d : ℕ) :
    Module.Basis (Fin d) ℝ (Homogenization.Vec d) :=
  (Pi.basisFun ℝ (Fin d)).map (LinearEquiv.neg ℝ)

theorem Flow.negativeCoordinateBasis_repr {d : ℕ}
    (x : Homogenization.Vec d) (i : Fin d) :
    (Flow.negativeCoordinateBasis d).repr x i = -x i := by
  rw [Flow.negativeCoordinateBasis, Module.Basis.map_repr]
  simp [Pi.basisFun_repr]

/-- Integer lattice spanned by the negative coordinate basis. -/
def Flow.flowLattice (d : ℕ) : AddSubgroup (Homogenization.Vec d) :=
  (Submodule.span ℤ (Set.range (Flow.negativeCoordinateBasis d))).toAddSubgroup

/-- The all-ones vector as an element of the flow lattice. -/
def Flow.flowLatticeOne (d : ℕ) : Flow.flowLattice d := by
  refine ⟨fun _ => (1 : ℝ), ?_⟩
  apply (Flow.negativeCoordinateBasis d).mem_span_iff_repr_mem ℤ _ |>.2
  intro i
  exact ⟨-1, by simp [Flow.negativeCoordinateBasis_repr]⟩

/-- Translated fundamental domain that agrees with the unit cell. -/
def Flow.flowFundamentalCell (d : ℕ) : Set (Homogenization.Vec d) :=
  Flow.flowLatticeOne d +ᵥ ZSpan.fundamentalDomain (Flow.negativeCoordinateBasis d)

theorem Flow.unitCellSet_eq_flowFundamentalCell {d : ℕ} :
    unitCellSet d = Flow.flowFundamentalCell d := by
  classical
  ext x
  have hrepr : ∀ i, (Flow.negativeCoordinateBasis d).repr
      (-(Flow.flowLatticeOne d : Homogenization.Vec d) + x) i =
        1 - x i := by
    intro i
    rw [Flow.negativeCoordinateBasis_repr]
    change -((-(fun _ : Fin d => (1 : ℝ)) + x) i) = _
    simp
    ring
  have hcell : x ∈ Flow.flowFundamentalCell d ↔
      ∀ i, 1 - x i ∈ Set.Ico (0 : ℝ) 1 := by
    change x ∈ Flow.flowLatticeOne d +ᵥ
      ZSpan.fundamentalDomain (Flow.negativeCoordinateBasis d) ↔ _
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    change (∀ i, (Flow.negativeCoordinateBasis d).repr
      (-(Flow.flowLatticeOne d : Homogenization.Vec d) + x) i ∈ Set.Ico (0 : ℝ) 1) ↔ _
    simp only [hrepr]
  change (∀ i, x i ∈ Set.Ioc (0 : ℝ) 1) ↔ x ∈ Flow.flowFundamentalCell d
  rw [hcell]
  constructor
  · intro hx i
    have hi := Set.mem_Ioc.mp (hx i)
    exact Set.mem_Ico.mpr ⟨by linarith, by linarith⟩
  · intro hx i
    have hi := Set.mem_Ico.mp (hx i)
    exact Set.mem_Ioc.mpr ⟨by linarith, by linarith⟩

theorem Flow.flowFundamentalCell_isAddFundamentalDomain (d : ℕ) :
    MeasureTheory.IsAddFundamentalDomain (Flow.flowLattice d) (Flow.flowFundamentalCell d) volume
        := by
  classical
  have hbase : MeasureTheory.IsAddFundamentalDomain (Flow.flowLattice d)
      (ZSpan.fundamentalDomain (Flow.negativeCoordinateBasis d)) volume := by
    exact ZSpan.isAddFundamentalDomain (Flow.negativeCoordinateBasis d) volume
  simpa [Flow.flowLattice, Flow.flowFundamentalCell] using hbase.vadd (Flow.flowLatticeOne d)

theorem Flow.flowLattice_mem_latticeVector {d : ℕ} (g : Flow.flowLattice d) :
    ∃ k : Fin d → ℤ, (g : Homogenization.Vec d) = latticeVector k := by
  have hgmem : (g : Homogenization.Vec d) ∈
      Submodule.span ℤ (Set.range (Flow.negativeCoordinateBasis d)) := g.property
  have hcoord := ((Flow.negativeCoordinateBasis d).mem_span_iff_repr_mem ℤ _).mp hgmem
  classical
  choose z hz using hcoord
  refine ⟨fun i => -z i, ?_⟩
  funext i
  have hrepr := Flow.negativeCoordinateBasis_repr (g : Homogenization.Vec d) i
  rw [← hz i] at hrepr
  have hval : (g : Homogenization.Vec d) i = -(z i : ℝ) := by
    have hn := congrArg Neg.neg hrepr
    simpa using hn.symm
  simpa [latticeVector] using hval

/-- Integer coordinates of a vector in the flow lattice. -/
noncomputable def Flow.flowLatticeCoordinates {d : ℕ} (g : Flow.flowLattice d) :
    Fin d → ℤ := fun i => Classical.choose
      (((Flow.negativeCoordinateBasis d).mem_span_iff_repr_mem ℤ _).mp g.property i)

theorem Flow.flowLatticeCoordinates_spec {d : ℕ} (g : Flow.flowLattice d) (i : Fin d) :
    ((Flow.flowLatticeCoordinates g i : ℤ) : ℝ) =
      ((Flow.negativeCoordinateBasis d).repr (g : Homogenization.Vec d)) i :=
  Classical.choose_spec
    (((Flow.negativeCoordinateBasis d).mem_span_iff_repr_mem ℤ _).mp g.property i)

theorem Flow.flowLattice_countable (d : ℕ) : Countable (Flow.flowLattice d) := by
  have hinj : Function.Injective (Flow.flowLatticeCoordinates (d := d)) := by
    intro g h hgh
    apply Subtype.ext
    apply (Flow.negativeCoordinateBasis d).repr.injective
    ext i
    rw [← Flow.flowLatticeCoordinates_spec g i, ← Flow.flowLatticeCoordinates_spec h i, hgh]
  exact hinj.countable

private instance {d : ℕ} : Countable (Flow.flowLattice d) := Flow.flowLattice_countable d

/-- Measurable equivalence induced by a periodic volume-preserving diffeomorphism. -/
noncomputable def Flow.flowMeasurableEquiv {d : ℕ}
    (X : PeriodicVolumePreservingDiffeomorphism d) :
    Homogenization.Vec d ≃ᵐ Homogenization.Vec d :=
  MeasurableEquiv.mk
    (Equiv.mk X.toFun X.invFun X.left_inv X.right_inv)
    X.contDiff_toFun.continuous.measurable
    X.contDiff_invFun.continuous.measurable

theorem Flow.flowLattice_translation_invariant {d : ℕ}
    {α : Type*} {f : Homogenization.Vec d → α} (hf : IsZPeriodic f)
    (g : Flow.flowLattice d) (x : Homogenization.Vec d) :
    f (g +ᵥ x) = f x := by
  obtain ⟨k, hk⟩ := Flow.flowLattice_mem_latticeVector g
  change f ((g : Homogenization.Vec d) + x) = f x
  rw [show (g : Homogenization.Vec d) + x = x + latticeVector k by rw [hk]; abel]
  exact hf x k

theorem Flow.flowEquiv_semiconj {d : ℕ}
    (X : PeriodicVolumePreservingDiffeomorphism d) (g : Flow.flowLattice d)
    (x : Homogenization.Vec d) :
    X.toFun (g +ᵥ x) = g +ᵥ X.toFun x := by
  obtain ⟨k, hk⟩ := Flow.flowLattice_mem_latticeVector g
  change X.toFun ((g : Homogenization.Vec d) + x) =
    (g : Homogenization.Vec d) + X.toFun x
  calc
    X.toFun ((g : Homogenization.Vec d) + x) = X.toFun (x + latticeVector k) := by
      rw [hk]
      abel_nf
    _ = X.toFun x + latticeVector k := X.lattice_equivariant x k
    _ = (g : Homogenization.Vec d) + X.toFun x := by rw [hk]; abel

theorem Flow.flow_imageFundamentalCell_isAddFundamentalDomain {d : ℕ}
    (X : PeriodicVolumePreservingDiffeomorphism d) :
    MeasureTheory.IsAddFundamentalDomain (Flow.flowLattice d)
      (X.toFun '' Flow.flowFundamentalCell d) volume := by
  let e := Flow.flowMeasurableEquiv X
  have hInv : MeasurePreserving (⇑e.toEquiv.symm) volume volume := by
    simpa [e] using MeasurePreserving.symm e X.measurePreserving
  have hInvQ : Measure.QuasiMeasurePreserving (⇑e.toEquiv.symm) volume volume :=
    hInv.quasiMeasurePreserving
  exact (Flow.flowFundamentalCell_isAddFundamentalDomain d).image_of_equiv e.toEquiv
    hInvQ (Equiv.refl _) (by
      intro g x
      exact Flow.flowEquiv_semiconj X g x)

/-- A periodic cell average is invariant under a smooth, measure-preserving
lattice-equivariant diffeomorphism. -/
theorem cellAverage_comp_flow_eq {d : ℕ}
    (f : Homogenization.Vec d → ℝ) (hf : IsZPeriodic f)
    (X : PeriodicVolumePreservingDiffeomorphism d) :
    cellAverage (fun x => f (X.toFun x)) = cellAverage f := by
  rw [cellAverage_eq_unitCellIntegral, cellAverage_eq_unitCellIntegral]
  rw [Flow.unitCellSet_eq_flowFundamentalCell]
  calc
    ∫ x in Flow.flowFundamentalCell d, f (X.toFun x) ∂volume =
        ∫ y in X.toFun '' Flow.flowFundamentalCell d, f y ∂volume := by
      symm
      exact X.measurePreserving.setIntegral_image_emb
        (Flow.flowMeasurableEquiv X).measurableEmbedding f (Flow.flowFundamentalCell d)
    _ = ∫ x in Flow.flowFundamentalCell d, f x ∂volume := by
      symm
      exact (Flow.flowFundamentalCell_isAddFundamentalDomain d).setIntegral_eq
        (Flow.flow_imageFundamentalCell_isAddFundamentalDomain X)
        (Flow.flowLattice_translation_invariant hf)

/-- The inverse lift of an equivariant diffeomorphism is equivariant too. -/
theorem PeriodicVolumePreservingDiffeomorphism.inv_lattice_equivariant
    {d : ℕ} (X : PeriodicVolumePreservingDiffeomorphism d)
    (x : Homogenization.Vec d) (k : Fin d → ℤ) :
    X.invFun (x + latticeVector k) = X.invFun x + latticeVector k := by
  apply Function.LeftInverse.injective X.left_inv
  calc
    X (X.invFun (x + latticeVector k)) = x + latticeVector k := X.right_inv _
    _ = X (X.invFun x + latticeVector k) := by
      rw [X.lattice_equivariant, X.right_inv]

/-- Change of variables by a periodic measure-preserving diffeomorphism moves
the inverse composition from the oscillatory factor onto the smooth factor. -/
theorem cellAverage_mul_comp_inv_eq {d : ℕ}
    {f g : Homogenization.Vec d → ℝ} (hf : IsZPeriodic f) (hg : IsZPeriodic g)
    (X : PeriodicVolumePreservingDiffeomorphism d) :
    cellAverage (fun x => f x * g (X.invFun x)) =
      cellAverage (fun x => f (X.toFun x) * g x) := by
  let h : Homogenization.Vec d → ℝ := fun x => f x * g (X.invFun x)
  have hh : IsZPeriodic h := by
    intro x k
    simp only [h]
    change f (x + latticeVector k) *
      g (X.invFun (x + latticeVector k)) = f x * g (X.invFun x)
    have hf' : f (x + latticeVector k) = f x := by
      change f (x + (fun i => (k i : ℝ))) = f x
      exact hf x k
    have hX' : X.invFun (x + latticeVector k) =
        X.invFun x + latticeVector k := by
      change X.invFun (x + (fun i => (k i : ℝ))) =
        X.invFun x + (fun i => (k i : ℝ))
      exact X.inv_lattice_equivariant x k
    have hg' : g (X.invFun x + latticeVector k) = g (X.invFun x) := by
      change g (X.invFun x + (fun i => (k i : ℝ))) = g (X.invFun x)
      exact hg (X.invFun x) k
    rw [hf', hX', hg']
  have hbase := Flow.flowFundamentalCell_isAddFundamentalDomain d
  have himage := Flow.flow_imageFundamentalCell_isAddFundamentalDomain X
  have hFmeas : MeasurableSet (Flow.flowFundamentalCell d) := by
    rw [← Flow.unitCellSet_eq_flowFundamentalCell]
    exact MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)
  calc
    cellAverage h = ∫ x in unitCellSet d, h x ∂volume :=
      cellAverage_eq_unitCellIntegral
    _ = ∫ x in Flow.flowFundamentalCell d, h x ∂volume := by
      rw [Flow.unitCellSet_eq_flowFundamentalCell]
    _ = ∫ y in X.toFun '' Flow.flowFundamentalCell d, h y ∂volume :=
      hbase.setIntegral_eq himage (Flow.flowLattice_translation_invariant hh)
    _ = ∫ x in Flow.flowFundamentalCell d, h (X.toFun x) ∂volume :=
      X.measurePreserving.setIntegral_image_emb
        (Flow.flowMeasurableEquiv X).measurableEmbedding h (Flow.flowFundamentalCell d)
    _ = ∫ x in Flow.flowFundamentalCell d, f (X.toFun x) * g x ∂volume := by
      apply setIntegral_congr_fun hFmeas
      intro x hx
      dsimp [h]
      rw [X.left_inv x]
    _ = ∫ x in unitCellSet d, f (X.toFun x) * g x ∂volume := by
      rw [Flow.unitCellSet_eq_flowFundamentalCell]
    _ = cellAverage (fun x => f (X.toFun x) * g x) :=
      cellAverage_eq_unitCellIntegral.symm

/-- Composing a lattice-periodic function with the inverse flow map preserves
its periodicity. -/
theorem IsZPeriodic.comp_invFlow
    {d : ℕ} {α : Type*} {f : Homogenization.Vec d → α}
    (hf : IsZPeriodic f) (X : PeriodicVolumePreservingDiffeomorphism d) :
    IsZPeriodic (fun x => f (X.invFun x)) := by
  intro x k
  change f (X.invFun (x + latticeVector k)) = f (X.invFun x)
  rw [X.inv_lattice_equivariant]
  exact hf (X.invFun x) k

end

end AVenhance.Infra.Ergodic
