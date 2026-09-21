/-
Copyright (c) 2026 Avik Das. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avik Das
-/
/-
Copyright (c) 2026 adas1236. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: adas1236
-/
import LeanPool.KaltonPeck.KaltonPeck.Support.Forms
import LeanPool.KaltonPeck.KaltonPeck.Support.Fredholm
import LeanPool.KaltonPeck.KaltonPeck.Support.FiniteParity

/-!
# Finite-codimensional symplectic reduction

This file relates symplectic orthogonals to finite codimension, constructs the relevant quotient
forms, and proves the finite-codimensional parity theorem.
-/

namespace KaltonPeck.Support.FiniteCodim

noncomputable section

/-- Orthogonal dimensions and the double orthogonal in a strong symplectic Banach space.

Blueprint: `lem:strong-orthogonals`; audit: `AUX-STRONG-ORTHOGONAL-DIMENSIONS`. -/
theorem strongOrthogonals {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (omega : StrongSymplecticForm X) (W : Submodule ℝ X)
    [IsClosed (W : Set X)] [FiniteDimensional ℝ (X ⧸ W)] :
    FiniteDimensional ℝ (omega.toContinuousAlternatingForm.orthogonal W) ∧
      Module.finrank ℝ (omega.toContinuousAlternatingForm.orthogonal W) =
        Module.finrank ℝ (X ⧸ W) ∧
      omega.toContinuousAlternatingForm.orthogonal
          (omega.toContinuousAlternatingForm.orthogonal W) = W := by
  let B := omega.toContinuousAlternatingForm
  let orthToAnn : B.orthogonal W →ₗ[ℝ] Forms.continuousAnnihilator W :=
    { toFun := fun x => ⟨omega.toDual x, by exact x.property⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp
      map_smul' := by
        intro a x
        apply Subtype.ext
        simp }
  have hInjective : Function.Injective orthToAnn := by
    intro x y hxy
    apply Subtype.ext
    apply omega.toDual.injective
    exact congrArg Subtype.val hxy
  have hSurjective : Function.Surjective orthToAnn := by
    intro phi
    let x : X := omega.toDual.symm (phi : StrongDual ℝ X)
    have hx : x ∈ B.orthogonal W := by
      change (((ContinuousLinearMap.flip (ContinuousLinearMap.compL ℝ W X ℝ)) W.subtypeL).comp
        B.toDual) x = 0
      change ((ContinuousLinearMap.flip (ContinuousLinearMap.compL ℝ W X ℝ)) W.subtypeL)
        (omega.toDual x) = 0
      rw [show omega.toDual x = (phi : StrongDual ℝ X) by
        exact omega.toDual.apply_symm_apply _]
      exact phi.property
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact omega.toDual.apply_symm_apply _
  let eOrth : B.orthogonal W ≃ₗ[ℝ] Forms.continuousAnnihilator W :=
    LinearEquiv.ofBijective orthToAnn ⟨hInjective, hSurjective⟩
  letI hAnn : FiniteDimensional ℝ (Forms.continuousAnnihilator W) :=
    FiniteDimensional.of_surjective
      (Forms.quotientDualEquivAnnihilator W).toLinearMap
      (Forms.quotientDualEquivAnnihilator W).surjective
  letI hOrth : FiniteDimensional ℝ (B.orthogonal W) :=
    FiniteDimensional.of_injective (V₂ := Forms.continuousAnnihilator W)
      orthToAnn hInjective
  let eCont : StrongDual ℝ (X ⧸ W) ≃ₗ[ℝ] Module.Dual ℝ (X ⧸ W) :=
    (LinearMap.toContinuousLinearMap :
      Module.Dual ℝ (X ⧸ W) ≃ₗ[ℝ] StrongDual ℝ (X ⧸ W)).symm
  have hFinrank : Module.finrank ℝ (B.orthogonal W) = Module.finrank ℝ (X ⧸ W) := by
    calc
      Module.finrank ℝ (B.orthogonal W) =
          Module.finrank ℝ (Forms.continuousAnnihilator W) := eOrth.finrank_eq
      _ = Module.finrank ℝ (StrongDual ℝ (X ⧸ W)) :=
        (Forms.quotientDualEquivAnnihilator W).toLinearEquiv.finrank_eq.symm
      _ = Module.finrank ℝ (Module.Dual ℝ (X ⧸ W)) := eCont.finrank_eq
      _ = Module.finrank ℝ (X ⧸ W) := Subspace.dual_finrank_eq
  have hSkew (x y : X) : omega.toDual x y = -omega.toDual y x := by
    have h := omega.alternating (x + y)
    simp only [map_add, add_apply, omega.alternating, add_zero, zero_add] at h
    linarith
  have hDouble : B.orthogonal (B.orthogonal W) = W := by
    ext x
    constructor
    · intro hx
      have hxAnn : ∀ phi : Forms.continuousAnnihilator W,
          (phi : StrongDual ℝ X) x = 0 := by
        intro phi
        let z : X := omega.toDual.symm (phi : StrongDual ℝ X)
        have hz : z ∈ B.orthogonal W := by
          change (((ContinuousLinearMap.flip (ContinuousLinearMap.compL ℝ W X ℝ))
            W.subtypeL).comp B.toDual) z = 0
          change ((ContinuousLinearMap.flip (ContinuousLinearMap.compL ℝ W X ℝ))
            W.subtypeL) (omega.toDual z) = 0
          rw [show omega.toDual z = (phi : StrongDual ℝ X) by
            exact omega.toDual.apply_symm_apply _]
          exact phi.property
        have hxz : omega.toDual x z = 0 := by
          change (((ContinuousLinearMap.flip
            (ContinuousLinearMap.compL ℝ (B.orthogonal W) X ℝ))
              (B.orthogonal W).subtypeL).comp B.toDual) x = 0 at hx
          exact DFunLike.congr_fun hx ⟨z, hz⟩
        calc
          (phi : StrongDual ℝ X) x = omega.toDual z x := by
            rw [show omega.toDual z = (phi : StrongDual ℝ X) by
              exact omega.toDual.apply_symm_apply _]
          _ = -omega.toDual x z := hSkew z x
          _ = 0 := by rw [hxz, neg_zero]
      exact (Set.ext_iff.mp (Forms.continuousDoubleAnnihilator W inferInstance) x).mp hxAnn
    · intro hx
      change (((ContinuousLinearMap.flip
        (ContinuousLinearMap.compL ℝ (B.orthogonal W) X ℝ))
          (B.orthogonal W).subtypeL).comp B.toDual) x = 0
      apply ContinuousLinearMap.ext
      intro z
      have hz := z.property
      change (((ContinuousLinearMap.flip (ContinuousLinearMap.compL ℝ W X ℝ))
        W.subtypeL).comp B.toDual) z = 0 at hz
      have hzx : omega.toDual z x = 0 := DFunLike.congr_fun hz ⟨x, hx⟩
      change omega.toDual x (z : X) = 0
      rw [hSkew, hzx, neg_zero]
  exact ⟨hOrth, hFinrank, hDouble⟩

/-- Parity of codimension and restricted radical in a strong symplectic Banach space.

Blueprint: `lem:strong-codim-parity`; audit: `LEM-STRONG-SYMPLECTIC-CODIM-PARITY`. -/
theorem strongCodimParity {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (omega : StrongSymplecticForm X) (W : Submodule ℝ X)
    [IsClosed (W : Set X)] [FiniteDimensional ℝ (X ⧸ W)] :
    Nat.ModEq 2 (Module.finrank ℝ (X ⧸ W))
      (Module.finrank ℝ (omega.toContinuousAlternatingForm.restrictedRadical W)) := by
  let B := omega.toContinuousAlternatingForm
  let O := B.orthogonal W
  obtain ⟨hOFinite, hODim, hDouble⟩ := strongOrthogonals omega W
  letI : FiniteDimensional ℝ O := hOFinite
  let c := B.restrict O
  obtain ⟨_, hMod⟩ := FiniteParity.finiteContinuousAlternatingRankEven c
  let radicalEquiv : c.radical ≃ₗ[ℝ] B.restrictedRadical W :=
    { toFun := fun x => ⟨x, by
          constructor
          · rw [← hDouble]
            exact x.property
          · exact x.val.property⟩
      invFun := fun r => ⟨⟨r, r.property.2⟩, by
          change (r : X) ∈ B.orthogonal O
          rw [hDouble]
          exact r.property.1⟩
      left_inv := by intro x; rfl
      right_inv := by intro r; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }
  rw [← hODim]
  rw [← radicalEquiv.finrank_eq]
  change Nat.ModEq 2 (Module.finrank ℝ O) (Module.finrank ℝ c.radical)
  exact Nat.ModEq.symm hMod

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

/-- A strong form on the radical quotient together with its descent identity. -/
structure FredholmQuotientStrongData {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (eta : ContinuousAlternatingForm X) where
  /-- The nondegenerate form induced on the quotient by the radical. -/
  form : StrongSymplecticForm (X ⧸ eta.radical)
  form_apply (x y : X) :
    form.toDual (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = eta.toDual x y

/-- A Fredholm alternating form descends to a strong form on its radical quotient.

Blueprint: `lem:fredholm-quotient-strong`; audit: `AUX-FREDHOLM-QUOTIENT-STRONG`. -/
def fredholmQuotientStrong {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (eta : ContinuousAlternatingForm X)
    (hReflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X))
    (hFredholm : IsFredholm eta.toDual) : FredholmQuotientStrongData eta := by
  letI : IsClosed (eta.radical : Set X) := by
    change IsClosed (eta.toDual.toLinearMap.ker : Set X)
    exact eta.toDual.isClosed_ker
  letI : FiniteDimensional ℝ eta.radical := hFredholm.1
  let hComplemented :=
    Submodule.ClosedComplemented.of_finiteDimensional eta.radical
  let Y : Submodule ℝ X := hComplemented.complement
  let hTop : Submodule.IsTopCompl eta.radical Y :=
    hComplemented.isTopCompl_complement
  letI : CompleteSpace Y :=
    hComplemented.isClosed_complement.completeSpace_coe
  let pF : X →L[ℝ] eta.radical :=
    eta.radical.projectionOntoL Y hTop
  let pY : X →L[ℝ] Y :=
    Y.projectionOntoL eta.radical hTop.symm
  have hProj (x : X) : (pF x : X) + (pY x : X) = x :=
    Submodule.projectionL_add_projectionL_eq_self hTop x
  have hRadical (f : eta.radical) : eta.toDual (f : X) = 0 := f.property
  have hSkew (x y : X) : eta.toDual x y = -eta.toDual y x := by
    have h := eta.alternating (x + y)
    have hsum : eta.toDual x y + eta.toDual y x = 0 := by
      simpa [eta.alternating, add_assoc, add_left_comm, add_comm] using h
    exact eq_neg_of_add_eq_zero_left hsum
  let SY : Y →L[ℝ] StrongDual ℝ X := eta.toDual.comp Y.subtypeL
  have hSY_injective : Function.Injective SY := by
    intro y z hyz
    apply Subtype.ext
    have hzero : eta.toDual ((y - z : Y) : X) = 0 := by
      simpa [SY, sub_eq_zero] using sub_eq_zero.mpr hyz
    have hzmem : ((y - z : Y) : X) ∈ (⊥ : Submodule ℝ X) :=
      hTop.isCompl.disjoint.le_bot ⟨hzero, (y - z).property⟩
    exact (Submodule.mem_bot ℝ).mp hzmem |> sub_eq_zero.mp
  have hSY_range : SY.toLinearMap.range = eta.toDual.toLinearMap.range := by
    apply le_antisymm
    · rintro phi ⟨y, rfl⟩
      exact ⟨(y : X), rfl⟩
    · rintro phi ⟨x, rfl⟩
      refine ⟨pY x, ?_⟩
      change eta.toDual (pY x : X) = eta.toDual x
      calc
        eta.toDual (pY x : X) =
            eta.toDual ((pF x : X) + (pY x : X)) := by
              rw [map_add, hRadical, zero_add]
        _ = eta.toDual x := congrArg eta.toDual (hProj x)
  have hSY_closed : IsClosed (Set.range SY) := by
    change IsClosed (SY.toLinearMap.range : Set (StrongDual ℝ X))
    rw [hSY_range]
    exact hFredholm.2.1
  let eRange : Y ≃L[ℝ] SY.toLinearMap.range :=
    ContinuousLinearMap.equivRange hSY_injective hSY_closed
  have hRange :
      eta.toDual.toLinearMap.range = Forms.continuousAnnihilator eta.radical := by
    apply le_antisymm
    · rintro phi ⟨x, rfl⟩
      change ((ContinuousLinearMap.compL ℝ eta.radical X ℝ).flip
        eta.radical.subtypeL) (eta.toDual x) = 0
      apply ContinuousLinearMap.ext
      intro f
      change eta.toDual x (f : X) = 0
      rw [hSkew, hRadical f]
      exact neg_zero
    · intro phi hphi
      let phiY : StrongDual ℝ Y := (phi : StrongDual ℝ X).comp Y.subtypeL
      let g : StrongDual ℝ SY.toLinearMap.range :=
        phiY.comp eRange.symm.toContinuousLinearMap
      obtain ⟨G, hG, _⟩ := exists_extension_norm_eq SY.toLinearMap.range g
      obtain ⟨x, hx⟩ := hReflexive G
      refine ⟨-x, ?_⟩
      apply ContinuousLinearMap.ext
      intro z
      let y : Y := pY z
      have hG_on_y : G (eta.toDual (y : X)) = phi (y : X) := by
        have heRange : eRange y = SY.rangeRestrict y :=
          congrFun (ContinuousLinearMap.coe_equivRange hSY_injective hSY_closed) y
        calc
          G (eta.toDual (y : X)) =
              G ((eRange y : SY.toLinearMap.range) : StrongDual ℝ X) := by
                rw [heRange]
                rfl
          _ = g (eRange y) := hG (eRange y)
          _ = phiY (eRange.symm (eRange y)) := rfl
          _ = phiY y := by rw [eRange.symm_apply_apply]
          _ = phi (y : X) := rfl
      have hphi_radical : phi (pF z : X) = 0 := by
        exact DFunLike.congr_fun hphi (pF z)
      calc
        eta.toDual (-x) z = -eta.toDual x z := by
          simp only [map_neg, neg_apply]
        _ = eta.toDual z x := by rw [hSkew]; simp
        _ = G (eta.toDual z) := by
          have h := DFunLike.congr_fun hx (eta.toDual z)
          change (eta.toDual z) x = G (eta.toDual z) at h
          exact h
        _ = G (eta.toDual (y : X)) := by
          congr 1
          change eta.toDual z = eta.toDual (pY z : X)
          calc
            eta.toDual z = eta.toDual ((pF z : X) + (pY z : X)) :=
              congrArg eta.toDual (hProj z).symm
            _ = eta.toDual (pY z : X) := by
              rw [map_add, hRadical, zero_add]
        _ = phi (y : X) := hG_on_y
        _ = phi z := by
          change phi (pY z : X) = phi z
          calc
            phi (pY z : X) = phi (pF z : X) + phi (pY z : X) := by
              rw [hphi_radical, zero_add]
            _ = phi ((pF z : X) + (pY z : X)) := by rw [map_add]
            _ = phi z := congrArg phi (hProj z)
  let hSYAnn :
      SY.toLinearMap.range = Forms.continuousAnnihilator eta.radical :=
    hSY_range.trans hRange
  let SYAnnEquiv : Y ≃L[ℝ] Forms.continuousAnnihilator eta.radical :=
    eRange.trans (ContinuousLinearEquiv.ofEq SY.toLinearMap.range
      (Forms.continuousAnnihilator eta.radical) hSYAnn)
  let qY : (X ⧸ eta.radical) ≃L[ℝ] Y :=
    Submodule.quotientEquivOfIsTopCompl eta.radical Y hTop
  let qAnn : (X ⧸ eta.radical) ≃L[ℝ]
      Forms.continuousAnnihilator eta.radical :=
    qY.trans SYAnnEquiv
  let formEquiv : (X ⧸ eta.radical) ≃L[ℝ]
      StrongDual ℝ (X ⧸ eta.radical) :=
    qAnn.trans (Forms.quotientDualEquivAnnihilator eta.radical).symm
  refine
    { form :=
        { toDual := formEquiv
          alternating := ?_ }
      form_apply := ?_ }
  · intro q
    refine Submodule.Quotient.induction_on eta.radical q ?_
    intro x
    change eta.toDual (pY x : X) x = 0
    have hx : eta.toDual (pY x : X) = eta.toDual x := by
      calc
        eta.toDual (pY x : X) =
            eta.toDual ((pF x : X) + (pY x : X)) := by
              rw [map_add, hRadical, zero_add]
        _ = eta.toDual x := congrArg eta.toDual (hProj x)
    rw [hx]
    exact eta.alternating x
  · intro x y
    change eta.toDual (pY x : X) y = eta.toDual x y
    have hx : eta.toDual (pY x : X) = eta.toDual x := by
      calc
        eta.toDual (pY x : X) =
            eta.toDual ((pF x : X) + (pY x : X)) := by
              rw [map_add, hRadical, zero_add]
        _ = eta.toDual x := congrArg eta.toDual (hProj x)
    rw [hx]

/-- Quotient-image and restricted-radical data used in finite-codimensional parity. -/
structure RadicalQuotientData {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (eta : ContinuousAlternatingForm X)
    (hReflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X))
    (hFredholm : IsFredholm eta.toDual) (E : Submodule ℝ X) where
  quotientImageClosed :
    IsClosed (Submodule.map eta.radical.mkQ (E ⊔ eta.radical) : Set (X ⧸ eta.radical))
  quotientImageFiniteCodimensional :
    FiniteDimensional ℝ
      ((X ⧸ eta.radical) ⧸ Submodule.map eta.radical.mkQ (E ⊔ eta.radical))
  restrictedRadicalFiniteDimensional : FiniteDimensional ℝ (eta.restrictedRadical E)
  quotientRestrictedRadicalFiniteDimensional :
    FiniteDimensional ℝ
      (ContinuousAlternatingForm.restrictedRadical
        (fredholmQuotientStrong eta hReflexive hFredholm).form.toContinuousAlternatingForm
        (Submodule.map eta.radical.mkQ (E ⊔ eta.radical)))
  intersection_le_restrictedRadical :
    E ⊓ eta.radical ≤ eta.restrictedRadical E
  /-- The restricted radical modulo `E ⊓ rad(eta)` is the quotient restricted radical. -/
  radicalEquiv :
    (eta.restrictedRadical E ⧸
        (E ⊓ eta.radical).comap (eta.restrictedRadical E).subtype) ≃ₗ[ℝ]
      ContinuousAlternatingForm.restrictedRadical
        (fredholmQuotientStrong eta hReflexive hFredholm).form.toContinuousAlternatingForm
        (Submodule.map eta.radical.mkQ (E ⊔ eta.radical))
  radicalEquiv_apply (r : eta.restrictedRadical E) :
    ((radicalEquiv (Submodule.Quotient.mk r) :
      ContinuousAlternatingForm.restrictedRadical
        (fredholmQuotientStrong eta hReflexive hFredholm).form.toContinuousAlternatingForm
        (Submodule.map eta.radical.mkQ (E ⊔ eta.radical))) : X ⧸ eta.radical) =
      Submodule.Quotient.mk (r : X)
  radicalFinrank :
    Module.finrank ℝ (eta.restrictedRadical E) =
      Module.finrank ℝ
          (ContinuousAlternatingForm.restrictedRadical
            (fredholmQuotientStrong eta hReflexive hFredholm).form.toContinuousAlternatingForm
            (Submodule.map eta.radical.mkQ (E ⊔ eta.radical))) +
        Module.finrank ℝ ↑(E ⊓ eta.radical)
  codimFinrank :
    Module.finrank ℝ (X ⧸ E) + Module.finrank ℝ ↑(E ⊓ eta.radical) =
      Module.finrank ℝ
          ((X ⧸ eta.radical) ⧸
            Submodule.map eta.radical.mkQ (E ⊔ eta.radical)) +
        Module.finrank ℝ eta.radical

/-- The restricted radical and codimension identities after quotienting by the radical.

Blueprint: `lem:radical-quotient`; audit: `AUX-RESTRICTED-RADICAL-QUOTIENT` and
`AUX-CODIM-SUM-FORMULA`. -/
def radicalQuotient {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (eta : ContinuousAlternatingForm X)
    (hReflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X))
    (hFredholm : IsFredholm eta.toDual) (E : Submodule ℝ X) [IsClosed (E : Set X)]
    [FiniteDimensional ℝ (X ⧸ E)] : RadicalQuotientData eta hReflexive hFredholm E := by
  letI : IsClosed (eta.radical : Set X) := by
    change IsClosed (eta.toDual.toLinearMap.ker : Set X)
    exact eta.toDual.isClosed_ker
  letI : FiniteDimensional ℝ eta.radical := hFredholm.1
  let package := sumQuotientPackage E eta.radical
  let quotientData := fredholmQuotientStrong eta hReflexive hFredholm
  let omega := quotientData.form.toContinuousAlternatingForm
  let Q := Submodule.map eta.radical.mkQ (E ⊔ eta.radical)
  let R := eta.restrictedRadical E
  let Rq := omega.restrictedRadical Q
  let K := (E ⊓ eta.radical).comap R.subtype
  letI : IsClosed (Q : Set (X ⧸ eta.radical)) := package.quotientImageClosed
  letI : FiniteDimensional ℝ ((X ⧸ eta.radical) ⧸ Q) :=
    package.quotientImageFiniteCodimensional
  have hTargetFinite : FiniteDimensional ℝ Rq := by
    have hOrthFinite : FiniteDimensional ℝ (omega.orthogonal Q) := by
      let orthToAnn :
          omega.orthogonal Q →ₗ[ℝ] Forms.continuousAnnihilator Q :=
        { toFun := fun x => ⟨quotientData.form.toDual x, by
              change (((ContinuousLinearMap.compL ℝ Q (X ⧸ eta.radical) ℝ).flip Q.subtypeL)
                (quotientData.form.toDual x)) = 0
              exact x.property⟩
          map_add' := by
            intro x y
            apply Subtype.ext
            simp
          map_smul' := by
            intro a x
            apply Subtype.ext
            simp }
      letI : FiniteDimensional ℝ (StrongDual ℝ ((X ⧸ eta.radical) ⧸ Q)) := by
        infer_instance
      letI hAnn : FiniteDimensional ℝ (Forms.continuousAnnihilator Q) :=
        FiniteDimensional.of_surjective
          (Forms.quotientDualEquivAnnihilator Q).toLinearMap
          (Forms.quotientDualEquivAnnihilator Q).surjective
      have hOrthToAnnInjective : Function.Injective orthToAnn := by
        intro x y hxy
        have hdual :
            (orthToAnn x : StrongDual ℝ (X ⧸ eta.radical)) = orthToAnn y :=
          congrArg (fun z : Forms.continuousAnnihilator Q =>
            (z : StrongDual ℝ (X ⧸ eta.radical))) hxy
        exact Subtype.ext (quotientData.form.toDual.injective hdual)
      exact FiniteDimensional.of_injective
        (V₂ := Forms.continuousAnnihilator Q) orthToAnn hOrthToAnnInjective
    let targetToOrth : Rq →ₗ[ℝ] omega.orthogonal Q :=
      { toFun := fun r => ⟨r, r.property.2⟩
        map_add' := by
          intro r s
          rfl
        map_smul' := by
          intro a r
          rfl }
    exact FiniteDimensional.of_injective targetToOrth (by
      intro r s hrs
      apply Subtype.ext
      exact congrArg (fun z : omega.orthogonal Q => (z : X ⧸ eta.radical)) hrs)
  letI : FiniteDimensional ℝ Rq := hTargetFinite
  have hInterLe : E ⊓ eta.radical ≤ R := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    change (((ContinuousLinearMap.compL ℝ E X ℝ).flip E.subtypeL)
      (eta.toDual x)) = 0
    have hxzero : eta.toDual x = 0 := hx.2
    rw [hxzero]
    rfl
  have hSkew (x y : X) : eta.toDual x y = -eta.toDual y x := by
    have h := eta.alternating (x + y)
    have hsum : eta.toDual x y + eta.toDual y x = 0 := by
      simpa [eta.alternating, add_assoc, add_left_comm, add_comm] using h
    exact eq_neg_of_add_eq_zero_left hsum
  have hRestricted (r : R) (e : E) :
      eta.toDual (r : X) (e : X) = 0 := by
    have hr := r.property.2
    change (((ContinuousLinearMap.compL ℝ E X ℝ).flip E.subtypeL)
      (eta.toDual (r : X))) = 0 at hr
    exact DFunLike.congr_fun hr e
  let f : R →ₗ[ℝ] Rq :=
    { toFun := fun r => ⟨Submodule.Quotient.mk (r : X), by
          constructor
          · refine ⟨(r : X), ?_, rfl⟩
            exact (le_sup_left : E ≤ E ⊔ eta.radical) r.property.1
          · change (((ContinuousLinearMap.compL ℝ Q (X ⧸ eta.radical) ℝ).flip Q.subtypeL)
              (omega.toDual (Submodule.Quotient.mk (r : X)))) = 0
            ext z
            rcases z.property with ⟨s, hs, hsz⟩
            rcases Submodule.mem_sup.1 hs with ⟨e, he, n, hn, hsum⟩
            change quotientData.form.toDual (Submodule.Quotient.mk (r : X))
              (z : X ⧸ eta.radical) = 0
            rw [← hsz]
            change quotientData.form.toDual (Submodule.Quotient.mk (r : X))
              (Submodule.Quotient.mk s) = 0
            rw [quotientData.form_apply]
            rw [← hsum, map_add, hRestricted r ⟨e, he⟩, zero_add]
            rw [hSkew]
            have hn0 : eta.toDual n (r : X) = 0 :=
              DFunLike.congr_fun hn (r : X)
            rw [hn0, neg_zero]⟩
      map_add' := by
        intro r s
        apply Subtype.ext
        simp
      map_smul' := by
        intro a r
        apply Subtype.ext
        simp }
  have hfKer : f.ker = K := by
    ext r
    constructor
    · intro hr
      have hq : (Submodule.Quotient.mk (r : X) : X ⧸ eta.radical) = 0 :=
        congrArg (fun z : Rq => (z : X ⧸ eta.radical)) hr
      exact ⟨r.property.1, (Submodule.Quotient.mk_eq_zero eta.radical).1 hq⟩
    · intro hr
      apply Subtype.ext
      exact (Submodule.Quotient.mk_eq_zero eta.radical).2 hr.2
  have hfSurjective : Function.Surjective f := by
    intro z
    rcases z.property.1 with ⟨s, hs, hsz⟩
    rcases Submodule.mem_sup.1 hs with ⟨e, he, n, hn, hsum⟩
    have heOrth : e ∈ eta.orthogonal E := by
      change (((ContinuousLinearMap.compL ℝ E X ℝ).flip E.subtypeL)
        (eta.toDual e)) = 0
      ext e'
      let qe' : Q :=
        ⟨Submodule.Quotient.mk (e' : X), by
          refine ⟨(e' : X), ?_, rfl⟩
          exact (le_sup_left : E ≤ E ⊔ eta.radical) e'.property⟩
      have hzOrth := z.property.2
      change (((ContinuousLinearMap.compL ℝ Q (X ⧸ eta.radical) ℝ).flip Q.subtypeL)
        (omega.toDual (z : X ⧸ eta.radical))) = 0 at hzOrth
      have hzero := DFunLike.congr_fun hzOrth qe'
      change quotientData.form.toDual (z : X ⧸ eta.radical)
        (Submodule.Quotient.mk (e' : X)) = 0 at hzero
      rw [← hsz] at hzero
      change quotientData.form.toDual (Submodule.Quotient.mk s)
        (Submodule.Quotient.mk (e' : X)) = 0 at hzero
      rw [quotientData.form_apply, ← hsum, map_add] at hzero
      have hn0 : eta.toDual n (e' : X) = 0 :=
        DFunLike.congr_fun hn (e' : X)
      change eta.toDual e (e' : X) = 0
      simpa [hn0] using hzero
    let r : R := ⟨e, he, heOrth⟩
    refine ⟨r, ?_⟩
    apply Subtype.ext
    change (Submodule.Quotient.mk e : X ⧸ eta.radical) = (z : X ⧸ eta.radical)
    rw [← hsz]
    apply (Submodule.Quotient.eq eta.radical).2
    change e - s ∈ eta.radical
    rw [← hsum]
    simpa using eta.radical.neg_mem hn
  let radicalEquiv : (R ⧸ K) ≃ₗ[ℝ] Rq :=
    (Submodule.quotEquivOfEq _ _ hfKer.symm).trans
      (f.quotKerEquivOfSurjective hfSurjective)
  have hApply (r : R) :
      ((radicalEquiv (Submodule.Quotient.mk r) : Rq) : X ⧸ eta.radical) =
        Submodule.Quotient.mk (r : X) := by
    rfl
  let interToRadical : ↥(E ⊓ eta.radical) →ₗ[ℝ] eta.radical :=
    { toFun := fun x => ⟨x, x.property.2⟩
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro a x
        rfl }
  letI : FiniteDimensional ℝ ↥(E ⊓ eta.radical) :=
    FiniteDimensional.of_injective interToRadical (by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : eta.radical => (z : X)) hxy)
  let kEquiv : K ≃ₗ[ℝ] ↥(E ⊓ eta.radical) :=
    { toFun := fun k => ⟨k, k.property⟩
      invFun := fun x => ⟨⟨x, hInterLe x.property⟩, x.property⟩
      left_inv := by
        intro k
        rfl
      right_inv := by
        intro x
        rfl
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro a x
        rfl }
  letI : FiniteDimensional ℝ K :=
    FiniteDimensional.of_injective kEquiv.toLinearMap kEquiv.injective
  letI : FiniteDimensional ℝ (R ⧸ K) :=
    FiniteDimensional.of_injective radicalEquiv.toLinearMap radicalEquiv.injective
  let hRestrictedFinite : FiniteDimensional ℝ R :=
    Module.Finite.of_submodule_quotient K
  letI : FiniteDimensional ℝ R := hRestrictedFinite
  have hRadicalFinrank :
      Module.finrank ℝ R = Module.finrank ℝ Rq + Module.finrank ℝ ↥(E ⊓ eta.radical) := by
    have hR := Submodule.finrank_quotient_add_finrank K
    have hQ := radicalEquiv.finrank_eq
    have hK := kEquiv.finrank_eq
    omega
  have hCodimFinrank :
      Module.finrank ℝ (X ⧸ E) + Module.finrank ℝ ↥(E ⊓ eta.radical) =
        Module.finrank ℝ ((X ⧸ eta.radical) ⧸ Q) + Module.finrank ℝ eta.radical := by
    calc
      Module.finrank ℝ (X ⧸ E) + Module.finrank ℝ ↥(E ⊓ eta.radical) =
          Module.finrank ℝ (X ⧸ (E ⊔ eta.radical)) +
            Module.finrank ℝ eta.radical := package.codimAddInter
      _ = Module.finrank ℝ ((X ⧸ eta.radical) ⧸ Q) +
            Module.finrank ℝ eta.radical := by
        rw [package.quotientImageCodim]
  refine
    { quotientImageClosed := package.quotientImageClosed
      quotientImageFiniteCodimensional := package.quotientImageFiniteCodimensional
      restrictedRadicalFiniteDimensional := hRestrictedFinite
      quotientRestrictedRadicalFiniteDimensional := hTargetFinite
      intersection_le_restrictedRadical := hInterLe
      radicalEquiv := radicalEquiv
      radicalEquiv_apply := hApply
      radicalFinrank := hRadicalFinrank
      codimFinrank := hCodimFinrank }

/-- Finite-codimensional parity for a Fredholm alternating form.

Blueprint: `thm:finite-codim-parity`; audit: `LEM-FINCODIM-PARITY` and
`AUX-FINCODIM-PARITY-ARITHMETIC`. -/
theorem finiteCodimParity {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (eta : ContinuousAlternatingForm X)
    (hReflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X))
    (hFredholm : IsFredholm eta.toDual) (E : Submodule ℝ X) [IsClosed (E : Set X)]
    [FiniteDimensional ℝ (X ⧸ E)] :
    FiniteDimensional ℝ (eta.restrictedRadical E) ∧
      Nat.ModEq 2 (Module.finrank ℝ (X ⧸ E))
        (Module.finrank ℝ eta.radical + Module.finrank ℝ (eta.restrictedRadical E)) := by
  let data := radicalQuotient eta hReflexive hFredholm E
  letI : FiniteDimensional ℝ (eta.restrictedRadical E) :=
    data.restrictedRadicalFiniteDimensional
  refine ⟨inferInstance, ?_⟩
  let Q := Submodule.map eta.radical.mkQ (E ⊔ eta.radical)
  letI : IsClosed (Q : Set (X ⧸ eta.radical)) := data.quotientImageClosed
  letI : FiniteDimensional ℝ ((X ⧸ eta.radical) ⧸ Q) :=
    data.quotientImageFiniteCodimensional
  have hStrong := strongCodimParity
    (fredholmQuotientStrong eta hReflexive hFredholm).form Q
  have hRadical := data.radicalFinrank
  have hCodim := data.codimFinrank
  dsimp only [Q] at hStrong
  unfold Nat.ModEq at hStrong ⊢
  omega

end

end KaltonPeck.Support.FiniteCodim

/-
Upstream license notice:
MIT License

Copyright (c) 2026 Avik Das

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
