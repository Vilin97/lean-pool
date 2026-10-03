/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldRealization
/-!
# Generic transport core for Hilbert class-field reciprocity

The quotient transport and its norm-residue evaluation are compiled once in
this leaf.  Big/small and actual/original Hilbert reciprocity specializations
reuse the named data provider without rebuilding the generic reciprocity
composite.
-/

@[expose] public section

open scoped IsMulCommutative NumberField

noncomputable
section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity

open scoped Classical in
/-- The shared commutativity provider used by the Hilbert reciprocity leaves. -/
theorem hilbertClassFieldReciprocityIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

open scoped Classical in
local instance
    hilbertClassFieldReciprocityIdeleClassGroupIsMulCommutativeLocal
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  hilbertClassFieldReciprocityIdeleClassGroupIsMulCommutative

attribute [local instance] hilbertClassFieldReciprocityIdeleClassGroupIsMulCommutativeLocal

open scoped Classical in
/-- Inverse norm-residue evaluation transported through a subgroup equality
and then through an arbitrary multiplicative equivalence. -/
theorem hilbertClassFieldQuotientTransport_inverse_apply_with
    {G A I : Type} [Group G] [Group A] [Group I]
    (N H : Subgroup G) [N.Normal] [H.Normal]
    (e : Additive (G ⧸ N) ≃+ Additive A)
    (h : N = H) (f : G ⧸ H ≃* I) (c : G) :
    f (QuotientGroup.quotientMulEquivOfEq h
        (Additive.toMul
          (e.symm (e
            (Additive.ofMul (QuotientGroup.mk' N c)))))) =
      f (QuotientGroup.mk' H c) := by
  apply congrArg f
  calc
    _ = QuotientGroup.quotientMulEquivOfEq h
          (Additive.toMul
            (Additive.ofMul (QuotientGroup.mk' N c))) :=
      congrArg
        (fun z => QuotientGroup.quotientMulEquivOfEq h
          (Additive.toMul z))
        (e.symm_apply_apply _)
    _ = QuotientGroup.mk' H c :=
      QuotientGroup.quotientMulEquivOfEq_mk h c

open scoped Classical in
/-- Global reciprocity followed by subgroup-equality transport and a chosen
quotient equivalence. -/
noncomputable def hilbertClassFieldGlobalReciprocityTransportEquiv
    {F E I : Type}
    [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    [Group I]
    (H : Subgroup (IdeleClassGroup F))
    (h : (_root_.ideleClassNorm F E).range = H)
    (f : IdeleClassGroup F ⧸ H ≃* I) :
    Gal(E/F) ≃* I :=
  (AddEquiv.toMultiplicative
      (globalReciprocityEquiv F E)).trans
    ((QuotientGroup.quotientMulEquivOfEq h).trans f)

open scoped Classical in
/-- Evaluation of the shared transported reciprocity equivalence on the
global norm-residue symbol. -/
theorem hilbertClassFieldGlobalReciprocityTransport_globalNormResidue
    {F E I : Type}
    [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    [Group I]
    (H : Subgroup (IdeleClassGroup F))
    (h : (_root_.ideleClassNorm F E).range = H)
    (f : IdeleClassGroup F ⧸ H ≃* I)
    (c : IdeleClassGroup F) :
    hilbertClassFieldGlobalReciprocityTransportEquiv H h f
        (globalNormResidueMonoidHom F E c) =
      f (QuotientGroup.mk' H c) := by
  have hNormResidue :
      Additive.ofMul (globalNormResidueMonoidHom F E c) =
        globalNormResidueEquiv F E
          (Additive.ofMul
            (QuotientGroup.mk'
              (_root_.ideleClassNorm F E).range c)) :=
    congrArg (fun σ => Additive.ofMul σ)
      (globalNormResidueMonoidHom_apply F E c)
  calc
    _ = f (QuotientGroup.quotientMulEquivOfEq h
          (Additive.toMul
            ((globalNormResidueEquiv F E).symm
              (Additive.ofMul
                (globalNormResidueMonoidHom F E c))))) := rfl
    _ = f (QuotientGroup.quotientMulEquivOfEq h
          (Additive.toMul
            ((globalNormResidueEquiv F E).symm
              (globalNormResidueEquiv F E
                (Additive.ofMul
                  (QuotientGroup.mk'
                    (_root_.ideleClassNorm F E).range c)))))) :=
      congrArg
        (fun τ =>
          f (QuotientGroup.quotientMulEquivOfEq h
            (Additive.toMul
              ((globalNormResidueEquiv F E).symm τ))))
        hNormResidue
    _ = f (QuotientGroup.mk' H c) :=
      hilbertClassFieldQuotientTransport_inverse_apply_with
        ((_root_.ideleClassNorm F E).range) H
        (globalNormResidueEquiv F E) h f c

open scoped Classical in
/-- The transported equivalence and its evaluation theorem, packaged once for
all four Hilbert class-field specializations. -/
noncomputable def hilbertClassFieldGlobalReciprocityTransportData
    {F E I : Type}
    [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    [Group I]
    (H : Subgroup (IdeleClassGroup F))
    (h : (_root_.ideleClassNorm F E).range = H)
    (f : IdeleClassGroup F ⧸ H ≃* I) :
    {e : Gal(E/F) ≃* I //
      ∀ c : IdeleClassGroup F,
        e (globalNormResidueMonoidHom F E c) =
          f (QuotientGroup.mk' H c)} :=
  ⟨hilbertClassFieldGlobalReciprocityTransportEquiv H h f,
    hilbertClassFieldGlobalReciprocityTransport_globalNormResidue H h f⟩

end GlobalClassFields
end GlobalClassFieldTheory
