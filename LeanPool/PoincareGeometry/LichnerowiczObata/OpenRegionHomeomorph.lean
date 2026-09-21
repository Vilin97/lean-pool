/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.ManifoldInverseDifferentiability

/-! # Ambient partial homeomorphisms from homeomorphic open regions -/

@[expose] public noncomputable section
open TopologicalSpace
namespace LichnerowiczObata
variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]

/-- A homeomorphism of nonempty open regions determines an ambient partial
homeomorphism, with no claims about its values outside those regions. -/
def openRegionHomeomorph (U : Opens M) (V : Opens N) (hU : Nonempty U) (Q : U ≃ₜ V) :
    OpenPartialHomeomorph M N :=
  ((U.openPartialHomeomorphSubtypeCoe hU).symm.trans Q.toOpenPartialHomeomorph).trans
    (V.openPartialHomeomorphSubtypeCoe (hU.map Q))

@[simp] theorem openRegionHomeomorph_source
    (U : Opens M) (V : Opens N) (hU : Nonempty U) (Q : U ≃ₜ V) :
    (openRegionHomeomorph U V hU Q).source = U := by
  simp [openRegionHomeomorph]

@[simp] theorem openRegionHomeomorph_target
    (U : Opens M) (V : Opens N) (hU : Nonempty U) (Q : U ≃ₜ V) :
    (openRegionHomeomorph U V hU Q).target = V := by
  simp [openRegionHomeomorph]

theorem openRegionHomeomorph_apply
    (U : Opens M) (V : Opens N) (hU : Nonempty U) (Q : U ≃ₜ V) (x : U) :
    openRegionHomeomorph U V hU Q (x : M) = (Q x : N) := by
  change (Q ((U.openPartialHomeomorphSubtypeCoe hU).symm (x : M)) : N) = _
  have hh : (U.openPartialHomeomorphSubtypeCoe hU).symm (x : M) = x :=
    (U.openPartialHomeomorphSubtypeCoe hU).left_inv
      (show x ∈ (U.openPartialHomeomorphSubtypeCoe hU).source from trivial)
  rw [hh]

theorem openRegionHomeomorph_symm_apply
    (U : Opens M) (V : Opens N) (hU : Nonempty U) (Q : U ≃ₜ V) (x : V) :
    (openRegionHomeomorph U V hU Q).symm (x : N) = (Q.symm x : M) := by
  change (Q.symm ((V.openPartialHomeomorphSubtypeCoe (hU.map Q)).symm (x : N)) : M) = _
  have hh : (V.openPartialHomeomorphSubtypeCoe (hU.map Q)).symm (x : N) = x :=
    (V.openPartialHomeomorphSubtypeCoe (hU.map Q)).left_inv
      (show x ∈ (V.openPartialHomeomorphSubtypeCoe (hU.map Q)).source from trivial)
  rw [hh]

def openCylinder (A : Type*) [TopologicalSpace A] (J : Opens ℝ) : Opens (A × ℝ) :=
  ⟨{q | q.2 ∈ J}, J.isOpen.preimage continuous_snd⟩

/-- The open cylinder viewed as a subset of the full angular-radius space
is homeomorphic to the product with the radial interval subtype. -/
def openCylinderHomeomorph (A : Type*) [TopologicalSpace A] (J : Opens ℝ) :
    openCylinder A J ≃ₜ A × J where
  toFun q := (q.1.1, ⟨q.1.2, q.2⟩)
  invFun q := ⟨(q.1, q.2), q.2.2⟩
  left_inv q := rfl
  right_inv q := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- A product parametrization of an open region produces an ambient partial
homeomorphism agreeing with its specified forward map throughout the cylinder. -/
theorem exists_polar_region_partialHomeomorph
    (A : Type*) [TopologicalSpace A] (J : Opens ℝ) (U : Opens M)
    (Q : A × J ≃ₜ U) (q₀ : A × J) (Φ : A × ℝ → M)
    (hQ : ∀ q, (Q q : M) = Φ (q.1, q.2)) :
    ∃ e : OpenPartialHomeomorph (A × ℝ) M,
      e.source = {q | q.2 ∈ J} ∧ e.target = U ∧
      ∀ q ∈ e.source, e q = Φ q := by
  let C := openCylinder A J
  let H := openCylinderHomeomorph A J
  have hC : Nonempty C := ⟨H.symm q₀⟩
  let e := openRegionHomeomorph C U hC (H.trans Q)
  refine ⟨e, openRegionHomeomorph_source C U hC (H.trans Q),
    openRegionHomeomorph_target C U hC (H.trans Q), ?_⟩
  intro q hq
  have hc : q ∈ C := by
    change q ∈ (C : Set (A × ℝ))
    rw [← openRegionHomeomorph_source C U hC (H.trans Q)]
    exact hq
  have he := openRegionHomeomorph_apply C U hC (H.trans Q) ⟨q, hc⟩
  exact he.trans (hQ (H ⟨q, hc⟩))

end LichnerowiczObata
