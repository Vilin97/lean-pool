/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

module

public import LeanPool.MarkoffModP.RiemannRoch.CoordinateFree.RiemannRoch

/-!
# Coordinate-free transport along algebra equivalences

This file proves that intrinsic places, divisors, Riemann--Roch spaces, and genus are invariant
under an equivalence of function fields over the constant field.  No rational-function chart or
function-field hypotheses are needed: the intrinsic definitions only use the two field structures
and their algebras over the common constant field.
-/

@[expose] public section

open scoped WithZero

noncomputable section

namespace FunctionField

open MonoidWithZeroHom

namespace Place

variable {k K L : Type*} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L]

/-- The normalized valuation associated to an intrinsic place is surjective. -/
theorem valuation_surjective (v : Place k K) :
    Function.Surjective v.valuation := by
  intro z
  obtain ⟨y, rfl⟩ := v.normalization.surjective z
  obtain ⟨x, hx⟩ :=
    (ValueGroup₀.restrict₀_surjective
      v.toValuationSubring.valuation.toMonoidWithZeroHom) y
  refine ⟨x, ?_⟩
  change v.normalization
      (v.toValuationSubring.valuation.restrict x) = v.normalization y
  exact congrArg v.normalization hx

/-- Transport an intrinsic place through an algebra equivalence. -/
noncomputable def mapAlgEquiv (e : K ≃ₐ[k] L) (v : Place k K) : Place k L := by
  let q : Valuation L (WithZero (Multiplicative ℤ)) :=
    v.valuation.comap e.symm.toRingHom
  have hqnontrivial : q.IsNontrivial := by
    obtain ⟨x, hx0, hx1⟩ :=
      (inferInstance : v.valuation.IsNontrivial).exists_val_nontrivial
    refine ⟨e x, ?_, ?_⟩
    · simpa [q] using hx0
    · simpa [q] using hx1
  letI : q.IsNontrivial := hqnontrivial
  letI : q.IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' q
  refine
    { toValuationSubring := q.valuationSubring
      ne_top := by
        intro htop
        exact (Valuation.valuationSubring_eq_top_iff q).mp htop hqnontrivial
      triv_on_k := fun c => by
        rw [Valuation.mem_valuationSubring_iff]
        have hc : v.valuation (algebraMap k K c) ≤ 1 := by
          rw [← Valuation.mem_valuationSubring_iff,
            Place.valuationSubring_valuation]
          exact v.triv_on_k c
        change v.valuation (e.symm (algebraMap k L c)) ≤ 1
        rw [e.symm.commutes]
        exact hc
      isDiscrete := by
        let h := Valuation.isEquiv_valuation_valuationSubring q
        exact ⟨h.orderMonoidIso.symm.trans
          (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt q)⟩ }

/-- The valuation subring of a transported place is the corresponding pullback. -/
@[simp]
theorem mapAlgEquiv_toValuationSubring (e : K ≃ₐ[k] L) (v : Place k K) :
    (mapAlgEquiv e v).toValuationSubring =
      v.toValuationSubring.comap e.symm.toRingHom := by
  ext x
  change v.valuation (e.symm x) ≤ 1 ↔ e.symm x ∈ v.toValuationSubring
  rw [← Place.valuationSubring_valuation v]
  rw [Valuation.mem_valuationSubring_iff]

/-- Intrinsic places are equivalent under an equivalence of their ambient fields. -/
noncomputable def algEquiv (e : K ≃ₐ[k] L) : Place k K ≃ Place k L where
  toFun := mapAlgEquiv e
  invFun := mapAlgEquiv e.symm
  left_inv v := by
    apply Place.ext
    rw [mapAlgEquiv_toValuationSubring, mapAlgEquiv_toValuationSubring]
    ext x
    simp
  right_inv v := by
    apply Place.ext
    rw [mapAlgEquiv_toValuationSubring, mapAlgEquiv_toValuationSubring]
    ext x
    simp

/-- Transporting a place preserves its normalized valuation exactly. -/
theorem mapAlgEquiv_valuation_eq_comap (e : K ≃ₐ[k] L) (v : Place k K) :
    (mapAlgEquiv e v).valuation =
      v.valuation.comap e.symm.toRingHom := by
  let q : Valuation L (WithZero (Multiplicative ℤ)) :=
    v.valuation.comap e.symm.toRingHom
  have hqsurj : Function.Surjective q := by
    intro z
    obtain ⟨x, hx⟩ := valuation_surjective v z
    refine ⟨e x, ?_⟩
    simpa [q] using hx
  have hqnontrivial : q.IsNontrivial := by
    obtain ⟨x, hx0, hx1⟩ :=
      (inferInstance : v.valuation.IsNontrivial).exists_val_nontrivial
    refine ⟨e x, ?_, ?_⟩
    · simpa [q] using hx0
    · simpa [q] using hx1
  letI : q.IsNontrivial := hqnontrivial
  letI : q.IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' q
  let V := q.valuationSubring
  let h := Valuation.isEquiv_valuation_valuationSubring q
  let ε : ValueGroup₀ (.ofClass V.valuation) ≃*o
      WithZero (Multiplicative ℤ) :=
    h.orderMonoidIso.symm.trans
      (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt q)
  have hnorm : (mapAlgEquiv e v).normalization = ε :=
    orderMonoidIso_withZeroMulInt_unique _ _
  ext x
  change (mapAlgEquiv e v).normalization
      (V.valuation.restrict x) = q x
  rw [hnorm]
  change (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt q)
      (h.orderMonoidIso.symm (V.valuation.restrict x)) = q x
  rw [show h.orderMonoidIso.symm (V.valuation.restrict x) = q.restrict x by
    change h.orderMonoidIso.symm
      (q.valuationSubring.valuation.restrict x) = q.restrict x
    exact h.orderMonoidIso.symm_apply_eq.mpr
      (h.orderMonoidIso_spec x).symm]
  exact
    Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
      hqsurj x

/-- Evaluation of normalized valuations is preserved by transport. -/
@[simp]
theorem algEquiv_valuation_apply (e : K ≃ₐ[k] L) (v : Place k K) (x : K) :
    ((algEquiv e) v).valuation (e x) = v.valuation x := by
  change (mapAlgEquiv e v).valuation (e x) = v.valuation x
  rw [mapAlgEquiv_valuation_eq_comap]
  simp

/-- The valuation subrings at corresponding places are equivalent as constant-field algebras. -/
noncomputable def valuationSubringAlgEquiv (e : K ≃ₐ[k] L) (v : Place k K) :
    v.toValuationSubring ≃ₐ[k] ((algEquiv e) v).toValuationSubring := by
  let f : v.toValuationSubring →ₐ[k]
      ((algEquiv e) v).toValuationSubring :=
    { toFun := fun x => ⟨e x, by
        change e x ∈ (mapAlgEquiv e v).toValuationSubring
        rw [mapAlgEquiv_toValuationSubring]
        change e.symm (e x) ∈ v.toValuationSubring
        rw [e.symm_apply_apply]
        exact x.property⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp
      commutes' := fun c => by
        apply Subtype.ext
        change e (algebraMap k K c) = algebraMap k L c
        exact e.commutes c }
  apply AlgEquiv.ofBijective f
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val hxy)
  · intro y
    refine ⟨⟨e.symm y, ?_⟩, ?_⟩
    · have hy := y.property
      change y.1 ∈ (mapAlgEquiv e v).toValuationSubring at hy
      rw [mapAlgEquiv_toValuationSubring] at hy
      exact hy
    · apply Subtype.ext
      simp [f]

/-- Residue fields at corresponding places are equivalent over the constant field. -/
noncomputable def residueFieldAlgEquiv (e : K ≃ₐ[k] L) (v : Place k K) :
    v.residueField ≃ₐ[k] ((algEquiv e) v).residueField :=
  IsLocalRing.ResidueField.mapAlgEquiv (valuationSubringAlgEquiv e v)

/-- Place degree is preserved under an equivalence of ambient fields. -/
@[simp]
theorem degree_algEquiv (e : K ≃ₐ[k] L) (v : Place k K) :
    ((algEquiv e) v).degree = v.degree :=
  (residueFieldAlgEquiv e v).toLinearEquiv.finrank_eq.symm

end Place

variable {k K L : Type*} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L]

/-- Reindex intrinsic divisors through an equivalence of their ambient fields. -/
noncomputable def divisorAlgEquiv (e : K ≃ₐ[k] L) :
    Divisor k K ≃+ Divisor k L :=
  Finsupp.domCongr (Place.algEquiv e)

/-- Intrinsic divisor degree is preserved by ambient-field equivalence. -/
@[simp]
theorem Divisor.deg_algEquiv (e : K ≃ₐ[k] L) (D : Divisor k K) :
    Divisor.deg k L (divisorAlgEquiv e D) = Divisor.deg k K D := by
  classical
  induction D using Finsupp.induction with
  | zero => simp [Divisor.deg, divisorAlgEquiv]
  | single_add a b f ha hb ih =>
      rw [map_add, Divisor.deg_add, Divisor.deg_add, ih]
      congr 1
      simp [Divisor.deg, divisorAlgEquiv, Finsupp.domCongr_apply,
        Finsupp.equivMapDomain_single]

/-- Riemann--Roch membership is preserved by ambient-field equivalence. -/
theorem memRRspace_algEquiv_iff (e : K ≃ₐ[k] L) (D : Divisor k K) (x : K) :
    memRRspace k L (divisorAlgEquiv e D) (e x) ↔ memRRspace k K D x := by
  constructor
  · intro hx v
    have hv := hx ((Place.algEquiv e) v)
    simpa [divisorAlgEquiv, Finsupp.domCongr_apply] using hv
  · intro hx w
    let v := (Place.algEquiv e).symm w
    have hv := hx v
    have hw : (Place.algEquiv e) v = w :=
      (Place.algEquiv e).apply_symm_apply w
    rw [← hw]
    simpa [divisorAlgEquiv, Finsupp.domCongr_apply] using hv

/-- The image of an intrinsic Riemann--Roch space is the transported space. -/
theorem RRspace_map_algEquiv (e : K ≃ₐ[k] L) (D : Divisor k K) :
    Submodule.map e.toLinearEquiv.toLinearMap (RRspace k K D) =
      RRspace k L (divisorAlgEquiv e D) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change memRRspace k K D x at hx
    change memRRspace k L (divisorAlgEquiv e D) (e x)
    exact (memRRspace_algEquiv_iff e D x).2 hx
  · intro hy
    change memRRspace k L (divisorAlgEquiv e D) y at hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change memRRspace k K D (e.symm y)
    apply (memRRspace_algEquiv_iff e D (e.symm y)).1
    simpa using hy

/-- Corresponding intrinsic Riemann--Roch spaces are linearly equivalent. -/
noncomputable def RRspaceAlgEquiv (e : K ≃ₐ[k] L) (D : Divisor k K) :
    RRspace k K D ≃ₗ[k] RRspace k L (divisorAlgEquiv e D) :=
  e.toLinearEquiv.ofSubmodules _ _ (RRspace_map_algEquiv e D)

/-- Riemann--Roch dimension is invariant under ambient-field equivalence. -/
@[simp]
theorem ell_algEquiv (e : K ≃ₐ[k] L) (D : Divisor k K) :
    ell k L (divisorAlgEquiv e D) = ell k K D := by
  exact (RRspaceAlgEquiv e D).finrank_eq.symm

/-- Divisor defect is invariant under ambient-field equivalence. -/
@[simp]
theorem defect_algEquiv (e : K ≃ₐ[k] L) (D : Divisor k K) :
    defect k L (divisorAlgEquiv e D) = defect k K D := by
  rw [defect, defect, Divisor.deg_algEquiv, ell_algEquiv]

/-- Intrinsic function-field genus is invariant under an equivalence over the constant field. -/
theorem genus_eq_of_algEquiv (e : K ≃ₐ[k] L) :
    genus k K = genus k L := by
  let E := divisorAlgEquiv e
  have hsets :
      {d : ℤ | ∃ D : Divisor k K, defect k K D = d} =
        {d : ℤ | ∃ D : Divisor k L, defect k L D = d} := by
    ext d
    constructor
    · rintro ⟨D, hD⟩
      refine ⟨E D, ?_⟩
      rw [defect_algEquiv]
      exact hD
    · rintro ⟨D, hD⟩
      refine ⟨E.symm D, ?_⟩
      rw [← defect_algEquiv e (E.symm D), E.apply_symm_apply]
      exact hD
  unfold genus
  rw [hsets]

end FunctionField
