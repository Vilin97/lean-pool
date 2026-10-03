/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentModel
public import Mathlib.RingTheory.PowerSeries.PiTopology
/-!
# The local-field structure on a finite-coefficient Laurent field

For a finite field `k`, the valuation ring in `k((T))` is the image of
`k[[T]]`.  With the coefficientwise product topology the latter is compact
by Tychonoff.  This file proves that its inclusion into the native Laurent
valuation topology is continuous, transfers compactness to the valuation
ring, and obtains local compactness of `k((T))`.  This supplies the genuine
`IsNonarchimedeanLocalField` input needed by the equal-characteristic
Lubin--Tate construction.
-/

@[expose] public section

noncomputable
section


open Filter Set
open scoped PowerSeries LaurentSeries PowerSeries.WithPiTopology Topology Valued WithZero

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

universe u v w

variable {k : Type u} [Field k]

/-- A valuation topology is the topology of its associated valuative
relation.  This is the universe-polymorphic form needed for the residue
field of a `LocalField`; the argument compares the two standard bases at
zero in both directions. -/
private theorem isValuativeTopology_of_valued_ofValuation'
    (L : Type u) (Γ : Type w) [Field L]
    [LinearOrderedCommGroupWithZero Γ]
    [Valued L Γ]
    [Valuation.IsNontrivial (Valued.v : Valuation L Γ)] :
    letI := ValuativeRel.ofValuation (Valued.v : Valuation L Γ)
    IsValuativeTopology L := by
  let vL : Valuation L Γ := Valued.v
  let : ValuativeRel L := ValuativeRel.ofValuation vL
  let : vL.Compatible := Valuation.Compatible.ofValuation vL
  let : ValuativeRel.IsNontrivial L :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vL).2 inferInstance
  apply IsValuativeTopology.of_zero
  intro s
  rw [Valued.mem_nhds_zero]
  constructor
  · rintro ⟨δ, hδ⟩
    refine
      ⟨δ.mapEquiv
          (ValuativeRel.ValueGroupWithZero.orderMonoidIso vL).symm, ?_⟩
    intro z hz
    apply hδ
    exact
      (ValuativeRel.valuation_lt_symm_orderMonoidIso
        vL (δ : MonoidWithZeroHom.ValueGroup₀ (.ofClass vL)) z).1
        (by simpa using hz)
  · rintro ⟨γ, hγ⟩
    refine
      ⟨γ.mapEquiv
          (ValuativeRel.ValueGroupWithZero.orderMonoidIso vL), ?_⟩
    intro z hz
    apply hγ
    have hz' :
        vL.restrict z <
          (ValuativeRel.ValueGroupWithZero.orderMonoidIso vL)
            (γ : ValuativeRel.ValueGroupWithZero L) := by
      exact hz
    exact
      (ValuativeRel.restrict_lt_orderMonoidIso
        vL (γ : ValuativeRel.ValueGroupWithZero L) z).1 hz'

/-- The coefficientwise inclusion `k[[T]] → k((T))` is continuous when
`k` is discrete. -/
theorem continuous_laurentSeries_ofPowerSeries
    [TopologicalSpace k] [DiscreteTopology k] :
    Continuous (HahnSeries.ofPowerSeries ℤ k : k⟦X⟧ → k⸨X⸩) := by
  apply continuous_of_continuousAt_zero
    (HahnSeries.ofPowerSeries ℤ k).toAddMonoidHom
  unfold ContinuousAt
  simp only [map_zero]
  rw [(Valued.hasBasis_nhds_zero k⸨X⸩ ℤᵐ⁰).tendsto_right_iff]
  intro γ _
  let γ' : (ℤᵐ⁰)ˣ :=
    Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
      (f := (.ofClass (Valued.v :
        Valuation k⸨X⸩ ℤᵐ⁰)))) γ
  obtain ⟨N, hN⟩ := WithZero.exists_exp_neg_natCast_lt γ'.ne_zero
  let U : Set k⟦X⟧ :=
    ⋂ n ∈ Finset.range N, {f | PowerSeries.coeff n f = 0}
  have hU : U ∈ 𝓝 (0 : k⟦X⟧) := by
    dsimp [U]
    rw [Finset.iInter_mem_sets]
    intro n hn
    have hopen : IsOpen
        ((PowerSeries.coeff n : k⟦X⟧ → k) ⁻¹' ({0} : Set k)) :=
      (isOpen_discrete ({0} : Set k)).preimage
        (PowerSeries.WithPiTopology.continuous_coeff k n)
    exact hopen.mem_nhds (by simp)
  refine mem_of_superset hU ?_
  intro f hf
  have hcoeff : ∀ n : ℕ, n < N → PowerSeries.coeff n f = 0 := by
    intro n hn
    simp only [U, Set.mem_iInter, Set.mem_ofPred_eq] at hf
    exact hf n (Finset.mem_range.mpr hn)
  change (Valued.v : Valuation k⸨X⸩ ℤᵐ⁰).restrict
    ((f : k⟦X⟧) : k⸨X⸩) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact lt_of_le_of_lt
    ((LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero k f).2 hcoeff)
    (by simpa [γ'] using hN)

/-- Power series as elements of the native Laurent valuation ring. -/
noncomputable def powerSeriesToLaurentInteger (k : Type u) [Field k] :
    k⟦X⟧ → Valued.integer k⸨X⸩ :=
  fun f => ⟨(f : k⸨X⸩),
    (LaurentSeries.val_le_one_iff_eq_coe k (f : k⸨X⸩)).2 ⟨f, rfl⟩⟩

/-- Embedding power series into the Laurent valuation ring is continuous. -/
theorem continuous_powerSeriesToLaurentInteger
    [TopologicalSpace k] [DiscreteTopology k] :
    Continuous (powerSeriesToLaurentInteger k) :=
  (continuous_laurentSeries_ofPowerSeries (k := k)).subtype_mk _

/-- Every integral Laurent series comes from a power series. -/
theorem powerSeriesToLaurentInteger_surjective :
    Function.Surjective (powerSeriesToLaurentInteger k) := by
  intro x
  obtain ⟨f, hf⟩ :=
    (LaurentSeries.val_le_one_iff_eq_coe k (x : k⸨X⸩)).1 x.property
  refine ⟨f, Subtype.ext ?_⟩
  exact hf

/-- The valuation ring of the native Laurent valuation is exactly the power
series ring.  This algebraic equivalence is also the source of its prime
element; compactness above only used its continuous underlying map. -/
noncomputable def powerSeriesEquivLaurentInteger
    (k : Type u) [Field k] :
    k⟦X⟧ ≃+* Valued.integer k⸨X⸩ where
  toFun := powerSeriesToLaurentInteger k
  invFun x := Classical.choose
    ((LaurentSeries.val_le_one_iff_eq_coe k (x : k⸨X⸩)).1 x.property)
  left_inv f := by
    exact (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := k))
      (Classical.choose_spec
        ((LaurentSeries.val_le_one_iff_eq_coe k
          ((powerSeriesToLaurentInteger k f :
            Valued.integer k⸨X⸩) : k⸨X⸩)).1
            (powerSeriesToLaurentInteger k f).property))
  right_inv x := by
    apply Subtype.ext
    exact Classical.choose_spec
      ((LaurentSeries.val_le_one_iff_eq_coe k (x : k⸨X⸩)).1 x.property)
  map_add' f g := by
    apply Subtype.ext
    exact map_add (HahnSeries.ofPowerSeries ℤ k) f g
  map_mul' f g := by
    apply Subtype.ext
    exact map_mul (HahnSeries.ofPowerSeries ℤ k) f g

/-- The power-series equivalence preserves the underlying Laurent series. -/
@[simp]
theorem powerSeriesEquivLaurentInteger_coe
    (f : k⟦X⟧) :
    ((powerSeriesEquivLaurentInteger k f :
      Valued.integer k⸨X⸩) : k⸨X⸩) = (f : k⸨X⸩) :=
  rfl

/-- The image of `X` is irreducible in the Laurent valuation ring. -/
theorem powerSeriesEquivLaurentInteger_X_irreducible :
    Irreducible
      (powerSeriesEquivLaurentInteger k (PowerSeries.X : k⟦X⟧)) :=
  PowerSeries.X_irreducible.map (powerSeriesEquivLaurentInteger k)

/-- The canonical integer ring attached to the valuative relation induced by
the Laurent valuation is the native valued-field integer ring. -/
noncomputable def laurentValuativeIntegerEquiv
    (k : Type u) [Field k] :
    letI : ValuativeRel k⸨X⸩ := ValuativeRel.ofValuation
      (Valued.v : Valuation k⸨X⸩ ℤᵐ⁰)
    (ValuativeRel.valuation k⸨X⸩).integer ≃+*
      Valued.integer k⸨X⸩ := by
  let L := k⸨X⸩
  let vL := (Valued.v : Valuation L ℤᵐ⁰)
  letI : ValuativeRel L := ValuativeRel.ofValuation vL
  letI : vL.Compatible := Valuation.Compatible.ofValuation vL
  let wL := ValuativeRel.valuation L
  exact
    { toFun := fun x => ⟨x, by
        have hxrel : (x : L) ≤ᵥ (1 : L) :=
          wL.vle_iff_le.mpr x.property
        change vL (x : L) ≤ 1
        simpa only [map_one] using vL.vle_iff_le.mp hxrel⟩
      invFun := fun x => ⟨x, by
        have hxv : vL (x : L) ≤ 1 := x.property
        have hxrel : (x : L) ≤ᵥ (1 : L) :=
          vL.vle_iff_le.mpr (by simpa only [map_one] using hxv)
        exact wL.vle_iff_le.mp hxrel⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }

/-- Power series identify with the canonical integer ring of the valuative
relation generated by the native Laurent valuation. -/
noncomputable def powerSeriesEquivLaurentValuativeInteger
    (k : Type u) [Field k] :
    letI : ValuativeRel k⸨X⸩ := ValuativeRel.ofValuation
      (Valued.v : Valuation k⸨X⸩ ℤᵐ⁰)
    k⟦X⟧ ≃+* (ValuativeRel.valuation k⸨X⸩).integer := by
  letI : ValuativeRel k⸨X⸩ := ValuativeRel.ofValuation
    (Valued.v : Valuation k⸨X⸩ ℤᵐ⁰)
  exact (powerSeriesEquivLaurentInteger k).trans
    (laurentValuativeIntegerEquiv k).symm

/-- The image of `X` is irreducible in the valuative integer ring. -/
theorem powerSeriesEquivLaurentValuativeInteger_X_irreducible :
    letI : ValuativeRel k⸨X⸩ := ValuativeRel.ofValuation
      (Valued.v : Valuation k⸨X⸩ ℤᵐ⁰)
    Irreducible
      (powerSeriesEquivLaurentValuativeInteger k
        (PowerSeries.X : k⟦X⟧)) := by
  let : ValuativeRel k⸨X⸩ := ValuativeRel.ofValuation
    (Valued.v : Valuation k⸨X⸩ ℤᵐ⁰)
  exact PowerSeries.X_irreducible.map
    (powerSeriesEquivLaurentValuativeInteger k)

/-- The native valuation ring of a Laurent series field over a finite field
is compact. -/
theorem laurentSeriesIntegerCompactSpace
    (k : Type u) [Field k] [Finite k] :
    CompactSpace (Valued.integer k⸨X⸩) := by
  let : TopologicalSpace k := ⊥
  let : DiscreteTopology k := ⟨rfl⟩
  let : CompactSpace k := Finite.compactSpace
  let : CompactSpace k⟦X⟧ :=
    inferInstanceAs (CompactSpace ((Unit →₀ ℕ) → k))
  rw [← isCompact_univ_iff]
  have h := (isCompact_univ : IsCompact (Set.univ : Set k⟦X⟧)).image
    (continuous_powerSeriesToLaurentInteger (k := k))
  rw [Set.image_univ,
    Set.range_eq_univ.mpr (powerSeriesToLaurentInteger_surjective (k := k))] at h
  exact h

/-- A Laurent series field over a finite field is locally compact in its
native valuation topology. -/
theorem laurentSeriesLocallyCompactSpace
    (k : Type u) [Field k] [Finite k] :
    LocallyCompactSpace k⸨X⸩ := by
  let : CompactSpace (Valued.integer k⸨X⸩) :=
    laurentSeriesIntegerCompactSpace k
  have hcompact : IsCompact (X := k⸨X⸩) (Valued.integer k⸨X⸩) :=
    isCompact_iff_compactSpace.mpr inferInstance
  apply IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup hcompact
  rw [Valued.mem_nhds_zero]
  refine ⟨1, ?_⟩
  intro x hx
  change Valued.v x ≤ 1
  exact le_of_lt ((Valued.v :
    Valuation k⸨X⸩ ℤᵐ⁰).restrict_lt_one_iff.mp hx)

/-- The valuative relation used on the equal-characteristic Laurent field. -/
@[reducible] noncomputable def equalCharacteristicLaurentValuativeRel
    {K : Type u} [Field K] (F : LocalField.{u, v} K) :
    ValuativeRel F.residueField⸨X⸩ :=
  ValuativeRel.ofValuation
    (Valued.v : Valuation F.residueField⸨X⸩ ℤᵐ⁰)

/-- The genuine nonarchimedean local-field structure on the finite-residue
Laurent field used in the equal-characteristic Lubin--Tate construction. -/
theorem equalCharacteristicLaurentIsNonarchimedeanLocalField
    {K : Type u} [Field K] (F : LocalField.{u, v} K) :
    letI := equalCharacteristicLaurentValuativeRel F
    IsNonarchimedeanLocalField F.residueField⸨X⸩ := by
  let L := F.residueField⸨X⸩
  let vL := (Valued.v : Valuation L ℤᵐ⁰)
  let : ValuativeRel L := equalCharacteristicLaurentValuativeRel F
  let : vL.Compatible := Valuation.Compatible.ofValuation vL
  let x : L :=
    ((PowerSeries.X : F.residueField⟦X⟧) : F.residueField⸨X⸩)
  have hxv : vL x = WithZero.exp (-1 : ℤ) := by
    change (Valued.v : Valuation F.residueField⸨X⸩ ℤᵐ⁰)
      (((PowerSeries.X : F.residueField⟦X⟧) :
        F.residueField⸨X⸩)) = _
    simpa using LaurentSeries.valuation_X_pow F.residueField 1
  have hx0 : x ≠ 0 := by
    intro hx
    have : vL x = 0 := by rw [hx, map_zero]
    rw [hxv] at this
    exact WithZero.exp_ne_zero this
  have hxlt : vL x < 1 := by
    rw [hxv, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  let : vL.IsNontrivial :=
    (Valuation.isNontrivial_iff_exists_lt_one vL).2 ⟨x, hx0, hxlt⟩
  let : ValuativeRel.IsNontrivial L :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vL).2 inferInstance
  let : IsValuativeTopology L :=
    isValuativeTopology_of_valued_ofValuation' L ℤᵐ⁰
  let : LocallyCompactSpace L :=
    laurentSeriesLocallyCompactSpace F.residueField
  exact
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }

end EqualCharacteristic
end LubinTate
