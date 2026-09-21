/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.NormalizationHeightOne

/-!
Coefficient-field maps and residue-field compatibility for a divisorial valuation ring.
-/

open IsLocalRing

noncomputable section

universe u

namespace Stafford38.Geometry.DivisorialVisibleFrameStage5

/-- The coefficient-field inclusion restricted to the chosen valuation ring. -/
def coeffHom {k K : Type u} [Field k] [Field K] [Algebra k K]
    (E : IntermediateField k K) (V : ValuationSubring K)
    (hEV : ∀ z : E, (z : K) ∈ V.toSubring) : E →+* V.toSubring :=
  RingHom.codRestrict (IntermediateField.val E).toRingHom V.toSubring hEV

private theorem integral_image {R S T : Type*} [CommRing R] [Ring S] [Ring T]
    [Algebra R S] [Algebra R T] (f : S →ₐ[R] T) {x : S} (hx : IsIntegral R x) :
    IsIntegral R (f x) :=
  hx.map f

theorem stage5_exists_coefficientField
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (A : Subalgebra k K) [Algebra.FiniteType k A] (p : Ideal A) [p.IsPrime]
    (V : ValuationSubring K) [IsLocalRing V.toSubring]
    (hAV : ∀ a : A, (a : K) ∈ V.toSubring)
    (hp : ∀ a : A, (⟨a, hAV a⟩ : V.toSubring) ∈ maximalIdeal V.toSubring ↔ a ∈ p)
    (hsurj : ∀ z : ResidueField V.toSubring, ∃ (a b : A), b ∉ p ∧
      z = residue V.toSubring ⟨a, hAV a⟩ / residue V.toSubring ⟨b, hAV b⟩) :
    ∃ (E : IntermediateField k K) (hEV : ∀ z : E, (z : K) ∈ V.toSubring),
      letI : Algebra E V.toSubring := (coeffHom E V hEV).toAlgebra
      Module.Finite E (ResidueField V.toSubring) := by
  classical
  let AV : A →+* V.toSubring :=
    RingHom.codRestrict (Subalgebra.val A).toRingHom V.toSubring hAV
  let : Algebra k V.toSubring := (AV.comp (algebraMap k A)).toAlgebra
  let : Algebra k (ResidueField V.toSubring) :=
    ((residue V.toSubring).comp (algebraMap k V.toSubring)).toAlgebra
  let : Nontrivial (A ⧸ p) :=
    Ideal.Quotient.nontrivial_iff.mpr (inferInstance : p.IsPrime).ne_top
  obtain ⟨s, g, hg, hgfin⟩ := exists_finite_inj_algHom_of_fg k (A ⧸ p)
  choose a ha using fun i : Fin s ↦ Ideal.Quotient.mk_surjective (g (MvPolynomial.X i))
  let t : Fin s → K := fun i ↦ (a i : K)
  have heval : MvPolynomial.aeval t =
      (Subalgebra.val A).comp (MvPolynomial.aeval a) := by
    ext i
    simp [t]
  have hg_eval : g = (Ideal.Quotient.mkₐ k p).comp (MvPolynomial.aeval a) := by
    ext i
    simpa using (ha i).symm
  have ht_independent : AlgebraicIndependent k t :=
    algebraicIndependent_iff_injective_aeval.mpr fun f q hfq ↦ by
      apply hg
      rw [hg_eval]
      apply congrArg (fun x : A ↦ Ideal.Quotient.mk p x)
      apply Subtype.ext
      exact (congrArg (fun e : MvPolynomial (Fin s) k →ₐ[k] K ↦ e f) heval).symm |>.trans
        hfq |>.trans (congrArg (fun e : MvPolynomial (Fin s) k →ₐ[k] K ↦ e q) heval)
  let E : IntermediateField k K := IntermediateField.adjoin k (Set.range t)
  have eval_mem (f : MvPolynomial (Fin s) k) :
      MvPolynomial.aeval t f ∈ V.toSubring := by
    rw [heval]
    exact hAV (MvPolynomial.aeval a f)
  have eval_ne_p {f : MvPolynomial (Fin s) k} (hf : f ≠ 0) :
      MvPolynomial.aeval a f ∉ p := by
    intro hfp
    have hgf : g f = 0 := by
      rw [hg_eval]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hfp
    exact hf (hg (hgf.trans (map_zero g).symm))
  have inv_eval_mem (f : MvPolynomial (Fin s) k) :
      (MvPolynomial.aeval t f)⁻¹ ∈ V.toSubring := by
    by_cases hf : f = 0
    · simp [hf]
    · let vf : V.toSubring :=
        ⟨(MvPolynomial.aeval a f : A), hAV (MvPolynomial.aeval a f)⟩
      have hvf : ((vf : V.toSubring) : K) = MvPolynomial.aeval t f := by
        change A.val (MvPolynomial.aeval a f) = MvPolynomial.aeval t f
        exact (congrArg (fun e : MvPolynomial (Fin s) k →ₐ[k] K ↦ e f) heval).symm
      have hv_not_mem : vf ∉ maximalIdeal V.toSubring :=
        (hp (MvPolynomial.aeval a f)).not.mpr (eval_ne_p hf)
      have hv_unit : IsUnit vf := by
        simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using hv_not_mem
      obtain ⟨w, hw⟩ := hv_unit
      have hinv : ((((w⁻¹ : (V.toSubring)ˣ) : V.toSubring) : K)) =
          (MvPolynomial.aeval t f)⁻¹ := by
        rw [← hvf, ← hw]
        change (↑(Units.map V.toSubring.subtype.toMonoidHom w⁻¹) : K) =
          (↑(Units.map V.toSubring.subtype.toMonoidHom w) : K)⁻¹
        rw [map_inv]
        exact Units.val_inv_eq_inv_val _
      rw [← hinv]
      exact ((w⁻¹ : (V.toSubring)ˣ) : V.toSubring).property
  have hEV : ∀ z : E, (z : K) ∈ V.toSubring := by
    rintro ⟨z, hz⟩
    change z ∈ V.toSubring
    obtain ⟨r, q, hz⟩ := (IntermediateField.mem_adjoin_range_iff k t z).mp hz
    rw [hz, div_eq_mul_inv]
    exact V.toSubring.mul_mem (eval_mem r) (inv_eval_mem q)
  refine ⟨E, hEV, ?_⟩
  let : Algebra E V.toSubring := (coeffHom E V hEV).toAlgebra
  let ρ : A →+* ResidueField V.toSubring := (residue V.toSubring).comp AV
  have hpker : ∀ x ∈ p, ρ x = 0 := by
    intro x hx
    exact (IsLocalRing.residue_eq_zero_iff _).mpr ((hp x).mpr hx)
  let ρbar : (A ⧸ p) →+* ResidueField V.toSubring := Ideal.Quotient.lift p ρ hpker
  let et : Fin s → E := fun i ↦
    ⟨t i, IntermediateField.subset_adjoin k (Set.range t) ⟨i, rfl⟩⟩
  have halgebraMap_et (i : Fin s) :
      algebraMap E (ResidueField V.toSubring) (et i) = ρ (a i) := by
    rfl
  have hkEV : IsScalarTower k E V.toSubring :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hEVκ : IsScalarTower E V.toSubring (ResidueField V.toSubring) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hkEκ : IsScalarTower k E (ResidueField V.toSubring) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let ρbarK : (A ⧸ p) →ₐ[k] ResidueField V.toSubring :=
    { toRingHom := ρbar
      commutes' := fun c ↦ by
        change ρbar (Ideal.Quotient.mk p (algebraMap k A c)) = _
        rw [Ideal.Quotient.lift_mk]
        rfl }
  let P := MvPolynomial (Fin s) k
  let : Algebra P (A ⧸ p) := g.toRingHom.toAlgebra
  let : Algebra P E := (MvPolynomial.aeval et).toRingHom.toAlgebra
  let : Algebra P (ResidueField V.toSubring) :=
    ((algebraMap E (ResidueField V.toSubring)).comp
      (MvPolynomial.aeval et).toRingHom).toAlgebra
  have hPEκ : IsScalarTower P E (ResidueField V.toSubring) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hpoly : ρbarK.comp g =
      (IsScalarTower.toAlgHom k E (ResidueField V.toSubring)).comp
        (MvPolynomial.aeval et) := by
    ext i
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    change ρbar (g (MvPolynomial.X i)) = algebraMap E (ResidueField V.toSubring) (et i)
    rw [show g (MvPolynomial.X i) = Ideal.Quotient.mk p (a i) from (ha i).symm,
      Ideal.Quotient.lift_mk]
    exact (halgebraMap_et i).symm
  let ρbarP : (A ⧸ p) →ₐ[P] ResidueField V.toSubring :=
    { toRingHom := ρbar
      commutes' := fun f ↦ by
        exact congrArg (fun e : MvPolynomial (Fin s) k →ₐ[k]
          ResidueField V.toSubring ↦ e f) hpoly }
  let hPB : Module.Finite P (A ⧸ p) := hgfin
  have residue_integral (x : A) : IsIntegral E (ρ x) := by
    have hx : IsIntegral P (Ideal.Quotient.mk p x) := IsIntegral.of_finite P _
    have hx' : IsIntegral E (ρbarP (Ideal.Quotient.mk p x)) :=
      IsIntegral.tower_top (R := P) (A := E)
        (integral_image ρbarP hx)
    convert hx' using 1
    change ρbar (Ideal.Quotient.mk p x) = ρ x
    exact Ideal.Quotient.lift_mk p ρ hpker
  obtain ⟨S, hS⟩ := (inferInstance : Algebra.FiniteType k A).out
  let gen : S → ResidueField V.toSubring := fun x ↦ ρ x.1
  let L : IntermediateField E (ResidueField V.toSubring) :=
    IntermediateField.adjoin E (Set.range gen)
  have rho_mem (x : A) : ρ x ∈ L := by
    have hx : x ∈ Algebra.adjoin k (S : Set A) := by
      rw [hS]
      trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
        exact IntermediateField.subset_adjoin E (Set.range gen)
          ⟨⟨x, hx⟩, rfl⟩
    | algebraMap c =>
        change ρ (algebraMap k A c) ∈ L
        rw [show ρ (algebraMap k A c) =
          algebraMap k (ResidueField V.toSubring) c from rfl,
          IsScalarTower.algebraMap_apply k E (ResidueField V.toSubring)]
        exact L.algebraMap_mem _
    | add x y _ _ hx hy => exact L.add_mem hx hy
    | mul x y _ _ hx hy => exact L.mul_mem hx hy
  have hL : L = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨x, y, hy, hz⟩ := hsurj z
    rw [hz]
    exact L.div_mem (rho_mem x) (rho_mem y)
  have gen_integral (z : ResidueField V.toSubring) (hz : z ∈ Set.range gen) :
      IsIntegral E z := by
    obtain ⟨x, rfl⟩ := hz
    exact residue_integral x.1
  let hfiniteL : Module.Finite E L :=
    IntermediateField.finiteDimensional_adjoin gen_integral
  let e : L ≃ₐ[E] ResidueField V.toSubring :=
    (IntermediateField.equivOfEq hL).trans IntermediateField.topEquiv
  exact Module.Finite.equiv e.toLinearEquiv


end Stafford38.Geometry.DivisorialVisibleFrameStage5
