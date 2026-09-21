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
import LeanPool.KaltonPeck.KaltonPeck.Support.FiniteCodim.QuotientSum
import LeanPool.KaltonPeck.KaltonPeck.Support.FiniteCodim.StrongQuotient

/-!
# Restricted radicals and codimension under quotienting

The corresponding construction from the complete finite-codimensional symplectic reduction.
-/

namespace KaltonPeck.Support.FiniteCodim

noncomputable
section

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
      let : FiniteDimensional ℝ (StrongDual ℝ ((X ⧸ eta.radical) ⧸ Q)) := by
        infer_instance
      let hAnn : FiniteDimensional ℝ (Forms.continuousAnnihilator Q) :=
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

end

end KaltonPeck.Support.FiniteCodim
