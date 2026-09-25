/-
Copyright (c) 2026 Avik Das. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avik Das
-/
module

/-
Copyright (c) 2026 adas1236. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: adas1236
-/
public import LeanPool.KaltonPeck.KaltonPeck.Support.Forms
public import LeanPool.KaltonPeck.KaltonPeck.Support.Fredholm
public import LeanPool.KaltonPeck.KaltonPeck.Support.FiniteParity

/-!
# Closed sums and quotient dimension identities

The corresponding construction from the complete finite-codimensional symplectic reduction.
-/

@[expose] public section

namespace KaltonPeck.Support.FiniteCodim

noncomputable
section

/-- The maps, topology, finiteness, and additive dimension identities for a closed
finite-codimensional subspace enlarged by a finite-dimensional subspace.

Blueprint: `lem:sum-quotient-package`; audit: `AUX-CLOSED-SUP-FINITE-DIMENSIONAL`,
`AUX-QUOTIENT-SUM-EQUIVALENCES`, `AUX-SUP-FINITE-CODIMENSIONAL`, and
`AUX-CODIM-SUM-FORMULA`. -/
structure SumQuotientData {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (E N : Submodule ℝ X) where
  finiteSubspaceClosed : IsClosed (N : Set X)
  supClosed : IsClosed ((E ⊔ N : Submodule ℝ X) : Set X)
  supFiniteCodimensional : FiniteDimensional ℝ (X ⧸ (E ⊔ N))
  quotientImageClosed : IsClosed (Submodule.map N.mkQ (E ⊔ N) : Set (X ⧸ N))
  quotientImageFiniteCodimensional :
    FiniteDimensional ℝ ((X ⧸ N) ⧸ Submodule.map N.mkQ (E ⊔ N))
  /-- The quotient of `E ⊔ N` by `E` identifies with the quotient of `N` by `E ⊓ N`. -/
  supModEEquivInter :
    (↑(E ⊔ N) ⧸ E.comap (E ⊔ N).subtype) ≃ₗ[ℝ]
      (N ⧸ (E ⊓ N).comap N.subtype)
  supModEEquivInter_apply (n : N) :
    supModEEquivInter
        (Submodule.Quotient.mk
          ⟨(n : X), (le_sup_right : N ≤ E ⊔ N) n.property⟩) =
      Submodule.Quotient.mk n
  /-- The quotient of `E ⊔ N` by `N` identifies with the quotient of `E` by `E ⊓ N`. -/
  supModNEquivInter :
    (↑(E ⊔ N) ⧸ N.comap (E ⊔ N).subtype) ≃ₗ[ℝ]
      (E ⧸ (E ⊓ N).comap E.subtype)
  supModNEquivInter_apply (e : E) :
    supModNEquivInter
        (Submodule.Quotient.mk
          ⟨(e : X), (le_sup_left : E ≤ E ⊔ N) e.property⟩) =
      Submodule.Quotient.mk e
  /-- Iterated quotienting first by `E` agrees with quotienting by `E ⊔ N`. -/
  quotientByEEquiv :
    ((X ⧸ E) ⧸ Submodule.map E.mkQ (E ⊔ N)) ≃ₗ[ℝ] (X ⧸ (E ⊔ N))
  quotientByEEquiv_apply (x : X) :
    quotientByEEquiv (Submodule.Quotient.mk (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk x
  /-- Iterated quotienting first by `N` agrees with quotienting by `E ⊔ N`. -/
  quotientByNEquiv :
    ((X ⧸ N) ⧸ Submodule.map N.mkQ (E ⊔ N)) ≃ₗ[ℝ] (X ⧸ (E ⊔ N))
  quotientByNEquiv_apply (x : X) :
    quotientByNEquiv (Submodule.Quotient.mk (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk x
  codimAddInter :
    Module.finrank ℝ (X ⧸ E) + Module.finrank ℝ ↑(E ⊓ N) =
      Module.finrank ℝ (X ⧸ (E ⊔ N)) + Module.finrank ℝ N
  quotientImageCodim :
    Module.finrank ℝ ((X ⧸ N) ⧸ Submodule.map N.mkQ (E ⊔ N)) =
      Module.finrank ℝ (X ⧸ (E ⊔ N))

/-- The closed-sum and quotient-dimension package.

Blueprint: `lem:sum-quotient-package`. -/
def sumQuotientPackage {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (E N : Submodule ℝ X) [IsClosed (E : Set X)]
    [FiniteDimensional ℝ (X ⧸ E)] [FiniteDimensional ℝ N] :
    SumQuotientData E N := by
  have hSupClosed : IsClosed ((E ⊔ N : Submodule ℝ X) : Set X) :=
    Submodule.isClosed_sup_finiteDimensional E N inferInstance
  have hSupComplete : IsComplete ((E ⊔ N : Submodule ℝ X) : Set X) :=
    hSupClosed.isComplete
  letI : IsClosed ((E ⊔ N : Submodule ℝ X) : Set X) := hSupComplete.isClosed
  letI : FiniteDimensional ℝ (X ⧸ (E ⊔ N)) :=
    FiniteDimensional.of_surjective (Submodule.factor (le_sup_left : E ≤ E ⊔ N))
      (Submodule.factor_surjective le_sup_left)
  have hImageClosed :
      IsClosed (Submodule.map N.mkQ (E ⊔ N) : Set (X ⧸ N)) := by
    rw [← N.isQuotientMap_mkQL.isCoinducing.isClosed_preimage]
    change IsClosed ((Submodule.map N.mkQ (E ⊔ N)).comap N.mkQ : Set X)
    rw [Submodule.comap_map_mkQ, sup_eq_right.2 le_sup_right]
    exact hSupClosed
  let eN := Submodule.quotientQuotientEquivQuotient N (E ⊔ N)
    (le_sup_right : N ≤ E ⊔ N)
  letI : FiniteDimensional ℝ
      ((X ⧸ N) ⧸ Submodule.map N.mkQ (E ⊔ N)) :=
    FiniteDimensional.of_injective eN.toLinearMap eN.injective
  let gE : N →ₗ[ℝ] ↑(E ⊔ N) ⧸ E.comap (E ⊔ N).subtype :=
    (E.comap (E ⊔ N).subtype).mkQ.comp (Submodule.inclusion le_sup_right)
  have hgEKer : gE.ker = (E ⊓ N).comap N.subtype := by
    ext n
    simp [gE]
  have hgESurj : Function.Surjective gE := by
    intro z
    refine Submodule.Quotient.induction_on _ z ?_
    intro s
    rcases Submodule.mem_sup.1 s.property with ⟨e, he, n, hn, hsum⟩
    refine ⟨⟨n, hn⟩, ?_⟩
    apply (Submodule.Quotient.eq _).2
    change n - (s : X) ∈ E
    rw [← hsum]
    simpa using E.neg_mem he
  let eE :
      (N ⧸ (E ⊓ N).comap N.subtype) ≃ₗ[ℝ]
        (↑(E ⊔ N) ⧸ E.comap (E ⊔ N).subtype) :=
    (Submodule.quotEquivOfEq _ _ hgEKer.symm).trans
      (gE.quotKerEquivOfSurjective hgESurj)
  let supModE := eE.symm
  let gN : E →ₗ[ℝ] ↑(E ⊔ N) ⧸ N.comap (E ⊔ N).subtype :=
    (N.comap (E ⊔ N).subtype).mkQ.comp (Submodule.inclusion le_sup_left)
  have hgNKer : gN.ker = (E ⊓ N).comap E.subtype := by
    ext e
    simp [gN]
  have hgNSurj : Function.Surjective gN := by
    intro z
    refine Submodule.Quotient.induction_on _ z ?_
    intro s
    rcases Submodule.mem_sup.1 s.property with ⟨e, he, n, hn, hsum⟩
    refine ⟨⟨e, he⟩, ?_⟩
    apply (Submodule.Quotient.eq _).2
    change e - (s : X) ∈ N
    rw [← hsum]
    simpa using N.neg_mem hn
  let eN' :
      (E ⧸ (E ⊓ N).comap E.subtype) ≃ₗ[ℝ]
        (↑(E ⊔ N) ⧸ N.comap (E ⊔ N).subtype) :=
    (Submodule.quotEquivOfEq _ _ hgNKer.symm).trans
      (gN.quotKerEquivOfSurjective hgNSurj)
  let supModN := eN'.symm
  let quotientIdentity : (X ⧸ (E ⊔ N)) ≃L[ℝ] (X ⧸ (E ⊔ N)) :=
    ContinuousLinearEquiv.ofBijective (1 : (X ⧸ (E ⊔ N)) →L[ℝ] (X ⧸ (E ⊔ N)))
      (by ext x; simp) (by ext x; simp)
  let qEBase := Submodule.quotientQuotientEquivQuotient E (E ⊔ N)
    (le_sup_left : E ≤ E ⊔ N)
  let qE := qEBase.trans quotientIdentity.toLinearEquiv
  let qN := Submodule.quotientQuotientEquivQuotient N (E ⊔ N)
    (le_sup_right : N ≤ E ⊔ N)
  let f : N →ₗ[ℝ] X ⧸ E := E.mkQ.comp N.subtype
  have hfKer : f.ker = (E ⊓ N).comap N.subtype := by
    ext n
    simp [f]
  have hfRange : f.range = Submodule.map E.mkQ (E ⊔ N) := by
    rw [show f.range = Submodule.map E.mkQ N by simp [f, LinearMap.range_comp]]
    rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]
  let eImage :
      (N ⧸ (E ⊓ N).comap N.subtype) ≃ₗ[ℝ]
        Submodule.map E.mkQ (E ⊔ N) :=
    (Submodule.quotEquivOfEq _ _ hfKer.symm).trans <|
      f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hfRange)
  let eInter : ↥((E ⊓ N).comap N.subtype) ≃ₗ[ℝ] ↥(E ⊓ N) :=
    { toFun := fun n ↦ ⟨n, n.property⟩
      invFun := fun x ↦ ⟨⟨x, x.property.2⟩, x.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  refine
    { finiteSubspaceClosed := N.closed_of_finiteDimensional
      supClosed := hSupClosed
      supFiniteCodimensional := inferInstance
      quotientImageClosed := hImageClosed
      quotientImageFiniteCodimensional := inferInstance
      supModEEquivInter := supModE
      supModEEquivInter_apply := ?_
      supModNEquivInter := supModN
      supModNEquivInter_apply := ?_
      quotientByEEquiv := qE
      quotientByEEquiv_apply := ?_
      quotientByNEquiv := qN
      quotientByNEquiv_apply := ?_
      codimAddInter := ?_
      quotientImageCodim := eN.finrank_eq }
  · intro n
    apply (LinearEquiv.symm_apply_eq eE).2
    rfl
  · intro e
    apply (LinearEquiv.symm_apply_eq eN').2
    rfl
  · intro x
    change
      (Submodule.quotientQuotientEquivQuotient E (E ⊔ N)
        (le_sup_left : E ≤ E ⊔ N))
          (Submodule.Quotient.mk (Submodule.Quotient.mk x)) =
        Submodule.Quotient.mk x
    rfl
  · intro x
    rfl
  · have hAmbient := Submodule.finrank_quotient_add_finrank
      (Submodule.map E.mkQ (E ⊔ N))
    have hN := Submodule.finrank_quotient_add_finrank
      ((E ⊓ N).comap N.subtype)
    have hQE := qE.finrank_eq
    have hImage := eImage.finrank_eq
    have hInter := eInter.finrank_eq
    omega

end

end KaltonPeck.Support.FiniteCodim
