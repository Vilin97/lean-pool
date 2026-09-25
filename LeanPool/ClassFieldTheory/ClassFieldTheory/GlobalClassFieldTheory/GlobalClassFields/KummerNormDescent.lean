/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.ArchimedeanPowerIndex
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.FinitePlaceCompletionInstances
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.LocalResidueArithmetic
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.FinitePlacePowerIndex
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.NormContainment
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.SupportedIdeleIndex
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.SupportedPrincipalQuotient
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.PrimePowerKummerIndex
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.Continuity
/-!
# Descent of power-local-unit idèle subgroups

For a finite extension `L / K`, the norm of a local `n`-th power is again
an `n`-th power.  At a finite place outside a prescribed support, the norm
of an integral unit is an integral unit.  Combining these statements over
all places above a place of `K` shows that the ordinary idèle norm carries
the power-local-unit subgroup for the full inverse-image support on `L`
into the corresponding subgroup on `K`.

Passing to principal-idèle quotients gives the idèle-class norm descent
needed when a Kummer extension is first constructed after a finite base
extension and then viewed over the original number field.
-/

@[expose] public section

open scoped BigOperators NumberField NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open AlgebraicNumberTheory.Valuations
open GlobalClassFieldTheory.ClassFieldAxiom

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]

/-- If `S'` is exactly the set of finite places of `L` above `S`, the
ordinary idèle norm carries the power-local-unit subgroup over `L` into
the corresponding subgroup over `K`. -/
theorem ideleNorm_mem_powerLocalUnitSubgroup_of_supports_above
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (S' : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : ∀ W : HeightOneSpectrum (𝓞 L),
      W ∈ S' ↔ _root_.finitePlaceBelow (K := K) W ∈ S)
    {a : IdeleGroup L}
    (ha :
      a ∈ idelePowerLocalUnitSubgroup (K := L) n S' ∅) :
    IdeleGroup.norm K L a ∈
      idelePowerLocalUnitSubgroup (K := K) n S ∅ := by
  classical
  rw [mem_idelePowerLocalUnitSubgroup_iff] at ha ⊢
  obtain ⟨haInfinite, haSupported, haAway⟩ := ha
  refine ⟨?_, ?_, ?_⟩
  · intro w
    let : ∀ W : {W : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) W = w},
        W.1.1.LiesOver w.1 :=
      fun W =>
        ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
    rw [IdeleGroup.infiniteComponent_norm_eq_prod]
    apply Subgroup.prod_mem
    intro W _
    obtain ⟨x, hx⟩ :=
      (MonoidHom.mem_range
        (G := W.1.Completionˣ)).mp
        (haInfinite W.1)
    apply
      (MonoidHom.mem_range
        (G := w.Completionˣ)).mpr
    refine
      ⟨LocalFieldTheory.normUnits
          w.Completion W.1.Completion x, ?_⟩
    rw [powMonoidHom_apply] at hx ⊢
    rw [← hx, map_pow]
  · intro v₀ hv₀
    let vK := HeightOneSpectrum.adicAbv K v₀
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v₀
    let eAbove :=
      finitePlaceExtensionEquivAbove
        (K := K) (L := L) v₀
    let :=
      completionTensorDecompositionExtensionFintype
        (K := K) (L := L) vK hvK
    let : Fintype {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = v₀} :=
      Fintype.ofEquiv (AbsoluteValueExtension vK L) eAbove
    let : ∀ W : {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = v₀},
        Algebra (v₀.adicCompletion K) (W.1.adicCompletion L) :=
      fun W =>
        (finitePlaceAdicCompletionMap K L v₀ W).toAlgebra
    rw [IdeleGroup.finiteComponent_norm_eq_prod]
    apply Subgroup.prod_mem
    intro W _
    have hWS : W.1 ∈ S' :=
      (hS W.1).2 (by simpa only [W.2] using hv₀)
    obtain ⟨x, hx⟩ :=
      (MonoidHom.mem_range
        (G := (W.1.adicCompletion L)ˣ)).mp
        (haSupported W.1 hWS)
    apply
      (MonoidHom.mem_range
        (G := (v₀.adicCompletion K)ˣ)).mpr
    refine
      ⟨LocalFieldTheory.normUnits
          (v₀.adicCompletion K) (W.1.adicCompletion L) x, ?_⟩
    rw [powMonoidHom_apply] at hx ⊢
    rw [← hx, map_pow]
  · intro v₀ hv₀
    simp only [Finset.union_empty] at hv₀
    let vK := HeightOneSpectrum.adicAbv K v₀
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v₀
    let eAbove :=
      finitePlaceExtensionEquivAbove
        (K := K) (L := L) v₀
    let :=
      completionTensorDecompositionExtensionFintype
        (K := K) (L := L) vK hvK
    let : Fintype {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = v₀} :=
      Fintype.ofEquiv (AbsoluteValueExtension vK L) eAbove
    let : ∀ W : {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = v₀},
        Algebra (v₀.adicCompletion K) (W.1.adicCompletion L) :=
      fun W =>
        (finitePlaceAdicCompletionMap K L v₀ W).toAlgebra
    rw [IdeleGroup.finiteComponent_norm_eq_prod]
    apply Subgroup.prod_mem
    intro W _
    have hWaway : W.1 ∉ S' := by
      intro hWS
      have hbelow := (hS W.1).1 hWS
      exact hv₀ (by simpa only [W.2] using hbelow)
    have hWunit :
        IdeleGroup.finiteComponent W.1 a ∈
          (W.1.adicCompletionIntegers L).units :=
      haAway W.1 (by
        simpa only [Finset.union_empty] using hWaway)
    let z : (W.1.adicCompletionIntegers L).units :=
      ⟨IdeleGroup.finiteComponent W.1 a, hWunit⟩
    simpa only [z, Subgroup.coe_subtype] using
      IdeleGroup.finitePlace_normUnits_mem_integerUnits
        (K := K) (L := L) v₀ W z

/-- Under exact compatibility of the finite supports, the ordinary
idèle-class norm maps the power-local-unit idèle-class subgroup over `L`
into the corresponding subgroup over `K`. -/
theorem ideleClassNorm_map_powerLocalUnitSubgroup_le_of_supports_above
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (S' : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : ∀ W : HeightOneSpectrum (𝓞 L),
      W ∈ S' ↔ _root_.finitePlaceBelow (K := K) W ∈ S) :
    (ideleClassPowerLocalUnitSubgroup (K := L) n S' ∅).map
        (_root_.ideleClassNorm K L) ≤
      ideleClassPowerLocalUnitSubgroup (K := K) n S ∅ := by
  rintro _ ⟨c, hc, rfl⟩
  obtain ⟨a, ha, rfl⟩ :=
    (mem_ideleClassPowerLocalUnitSubgroup_iff
      (K := L) n S' ∅ c).mp hc
  rw [_root_.ideleClassNorm_mk]
  exact
    (mem_ideleClassPowerLocalUnitSubgroup_iff
      (K := K) n S ∅ _).2
      ⟨IdeleGroup.norm K L a,
        ideleNorm_mem_powerLocalUnitSubgroup_of_supports_above
          (K := K) (L := L) n S S' hS ha,
        rfl⟩

end GlobalClassFields
end GlobalClassFieldTheory
