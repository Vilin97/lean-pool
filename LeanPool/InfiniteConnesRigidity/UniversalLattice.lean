/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.VonNeumannAlgebra.Basic
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Data.Finsupp.Encodable
import Mathlib.GroupTheory.Complement
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Universal-lattice and relative-property-(T) foundations
-/

noncomputable section

namespace ConnesRigidity

section

namespace FeedbackBooleanPolynomial

variable {ι : Type*} [DecidableEq ι]



/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem eq_one_of_ne_zero_zmod_two
    (a : ZMod 2) (ha : a ≠ 0) :
    a = 1 := by
  fin_cases a
  · exact (ha rfl).elim
  · rfl





end FeedbackBooleanPolynomial

end

section

universe u v

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
structure CountableDiscreteGroup where
  /-- The underlying carrier of the packaged group. -/
  Carrier : Type u
  group : Group Carrier
  countable : Countable Carrier

namespace CountableDiscreteGroup

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance : CoeSort CountableDiscreteGroup (Type u) :=
  ⟨CountableDiscreteGroup.Carrier⟩

attribute [instance] group countable

end CountableDiscreteGroup

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def conjugacyClass (G : CountableDiscreteGroup) (g : G) : Set G :=
  {h | ∃ x : G, h = x * g * x⁻¹}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def IsICC (G : CountableDiscreteGroup) : Prop :=
  Infinite G ∧ ∀ g : G, g ≠ 1 → Set.Infinite (conjugacyClass G g)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def GroupsIsomorphic (G H : CountableDiscreteGroup) : Prop :=
  Nonempty (G ≃* H)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev UnitaryRepresentation
    (G : Type u) [Group G]
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  G →* unitary (H →L[ℂ] H)

namespace UnitaryRepresentation

variable {G H : Type u} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def IsInvariant (π : UnitaryRepresentation G H) (ξ : H) : Prop :=
  ∀ g : G, (π g : H →L[ℂ] H) ξ = ξ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def HasAlmostInvariantUnitVectors (π : UnitaryRepresentation G H) : Prop :=
  ∀ (K : Finset G) (ε : ℝ), 0 < ε →
    ∃ ξ : H, ‖ξ‖ = 1 ∧ ∀ g ∈ K, ‖(π g : H →L[ℂ] H) ξ - ξ‖ < ε

end UnitaryRepresentation

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def HasKazhdanPropertyT (G : CountableDiscreteGroup.{u}) : Prop :=
  ∀ (H : Type u)
    (_ : NormedAddCommGroup H)
    (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H)
    (π : UnitaryRepresentation G H),
    π.HasAlmostInvariantUnitVectors →
      ∃ ξ : H, ξ ≠ 0 ∧ π.IsInvariant ξ

section

open scoped NNReal ENNReal

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev GroupL2 (G : Type u) := lp (fun _ : G ↦ ℂ) 2

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def l2Reindex {α : Type u} {β : Type v} (e : α ≃ β) :
    GroupL2 α ≃ₗᵢ[ℂ] GroupL2 β where
  toLinearEquiv :=
    { toFun := fun f ↦ ⟨(fun j : β ↦ f (e.symm j)), by
        change Memℓp (fun j : β ↦ f (e.symm j)) 2
        rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
        exact (e.symm.summable_iff).2
          ((lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))⟩
      invFun := fun f ↦ ⟨(fun j : α ↦ f (e j)), by
        change Memℓp (fun j : α ↦ f (e j)) 2
        rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
        exact e.summable_iff.mpr
          ((lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))⟩
      left_inv := by
        intro f
        ext i
        change f (e.symm (e i)) = f i
        simp
      right_inv := by
        intro f
        ext j
        change f (e (e.symm j)) = f j
        simp
      map_add' := by
        intro f g
        ext j
        rfl
      map_smul' := by
        intro c f
        ext j
        rfl }
  norm_map' := by
    intro f
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    congr 1
    exact e.symm.tsum_eq (fun i ↦ ‖f i‖ ^ (2 : ℝ≥0∞).toReal)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem l2Reindex_apply {α : Type u} {β : Type v} (e : α ≃ β)
    (f : GroupL2 α) (j : β) :
    l2Reindex e f j = f (e.symm j) :=
  rfl



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def leftRegularUnitary {G : Type u} [Group G] (g : G) :
    unitary (GroupL2 G →L[ℂ] GroupL2 G) :=
  Unitary.linearIsometryEquiv.symm (l2Reindex (Equiv.mulLeft g))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem leftRegularUnitary_apply {G : Type u} [Group G]
    (g : G) (f : GroupL2 G) (h : G) :
    (leftRegularUnitary g : GroupL2 G →L[ℂ] GroupL2 G) f h = f (g⁻¹ * h) := by
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def leftRegularRepresentation (G : Type u) [Group G] :
    G →* unitary (GroupL2 G →L[ℂ] GroupL2 G) where
  toFun := leftRegularUnitary
  map_one' := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro f
    ext h
    change f ((1 : G)⁻¹ * h) = f h
    simp
  map_mul' g h := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro f
    ext k
    change f ((g * h)⁻¹ * k) = f (h⁻¹ * (g⁻¹ * k))
    simp [mul_assoc]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def vonNeumannClosure
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Set (H →L[ℂ] H)) :
    VonNeumannAlgebra H where
  toStarSubalgebra :=
    StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S : Set (H →L[ℂ] H))
  centralizer_centralizer' := by
    change
      Set.centralizer
          (Set.centralizer
            ((StarSubalgebra.centralizer ℂ
              (StarSubalgebra.centralizer ℂ S : Set (H →L[ℂ] H))) :
                Set (H →L[ℂ] H))) =
        ((StarSubalgebra.centralizer ℂ
          (StarSubalgebra.centralizer ℂ S : Set (H →L[ℂ] H))) :
            Set (H →L[ℂ] H))
    rw [StarSubalgebra.coe_centralizer_centralizer]
    exact Set.centralizer_centralizer_centralizer ((S ∪ star S).centralizer)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def groupVonNeumannAlgebra (G : CountableDiscreteGroup.{u}) :
    VonNeumannAlgebra (GroupL2 G) :=
  vonNeumannClosure (Set.range fun g : G ↦
    (leftRegularRepresentation G g : GroupL2 G →L[ℂ] GroupL2 G))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev GroupVonNeumannAlgebra (G : CountableDiscreteGroup.{u}) :=
  (groupVonNeumannAlgebra G).toStarSubalgebra

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def delta (G : CountableDiscreteGroup.{u}) (g : G) : GroupL2 G :=
  by
    classical
    exact lp.single 2 g 1

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def canonicalTrace (G : CountableDiscreteGroup.{u}) :
    GroupVonNeumannAlgebra G → ℂ :=
  fun x ↦ inner ℂ (delta G 1) ((x : GroupL2 G →L[ℂ] GroupL2 G) (delta G 1))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def ProjectionLE {A : Type u} [Mul A] (p q : A) : Prop :=
  p * q = p

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def IsProjectionSupremum {A : Type u} [Mul A] [Star A]
    (S : Set A) (p : A) : Prop :=
  IsStarProjection p ∧
    (∀ q ∈ S, IsStarProjection q ∧ ProjectionLE q p) ∧
    ∀ r, IsStarProjection r → (∀ q ∈ S, ProjectionLE q r) → ProjectionLE p r

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def IsNormalStarAlgEquiv
    {A : Type u} {B : Type v}
    [Semiring A] [StarRing A] [Algebra ℂ A]
    [Semiring B] [StarRing B] [Algebra ℂ B]
    (e : A ≃⋆ₐ[ℂ] B) : Prop :=
  (∀ (S : Set A) (p : A), IsProjectionSupremum S p →
    IsProjectionSupremum (e '' S) (e p)) ∧
  ∀ (S : Set B) (p : B), IsProjectionSupremum S p →
    IsProjectionSupremum (e.symm '' S) (e.symm p)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
structure TracialGroupFactorEquiv
    (G : CountableDiscreteGroup.{u}) (H : CountableDiscreteGroup.{v}) where
  /-- The star-algebra equivalence between the two group factors. -/
  toStarAlgEquiv :
    GroupVonNeumannAlgebra G ≃⋆ₐ[ℂ] GroupVonNeumannAlgebra H
  normal : IsNormalStarAlgEquiv toStarAlgEquiv
  trace_preserving :
    ∀ x, canonicalTrace H (toStarAlgEquiv x) = canonicalTrace G x

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def TracialGroupFactorsIsomorphic
    (G : CountableDiscreteGroup.{u}) (H : CountableDiscreteGroup.{v}) : Prop :=
  Nonempty (TracialGroupFactorEquiv G H)

end

end

section

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem UnitaryRepresentation.hasAlmostInvariantUnitVectors_comp
    {G H K : Type u} [Group G] [Group H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : UnitaryRepresentation H K)
    (f : G →* H)
    (hπ : π.HasAlmostInvariantUnitVectors) :
    UnitaryRepresentation.HasAlmostInvariantUnitVectors (π.comp f) := by
  classical
  intro S ε hε
  obtain ⟨ξ, hξ, hclose⟩ := hπ (S.image f) ε hε
  refine ⟨ξ, hξ, ?_⟩
  intro g hg
  exact hclose (f g) (Finset.mem_image.mpr ⟨g, hg, rfl⟩)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem hasKazhdanPropertyT_of_surjective
    (G H : CountableDiscreteGroup.{u})
    (f : G →* H) (hf : Function.Surjective f)
    (hG : HasKazhdanPropertyT G) :
    HasKazhdanPropertyT H := by
  intro K _ _ _ π hπ
  obtain ⟨ξ, hξ, hinv⟩ :=
    hG K inferInstance inferInstance inferInstance (π.comp f)
      (UnitaryRepresentation.hasAlmostInvariantUnitVectors_comp π f hπ)
  refine ⟨ξ, hξ, ?_⟩
  intro h
  obtain ⟨g, rfl⟩ := hf h
  exact hinv g

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem hasKazhdanPropertyT_iff_of_mulEquiv
    (G H : CountableDiscreteGroup.{u}) (e : G ≃* H) :
    HasKazhdanPropertyT G ↔ HasKazhdanPropertyT H := by
  constructor
  · exact hasKazhdanPropertyT_of_surjective G H e.toMonoidHom e.surjective
  · exact hasKazhdanPropertyT_of_surjective H G e.symm.toMonoidHom e.symm.surjective

end

section

universe u

open scoped ENNReal

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def CountableDiscreteGroup.subgroup
    (G : CountableDiscreteGroup.{u}) (S : Subgroup G) :
    CountableDiscreteGroup.{u} where
  Carrier := S
  group := inferInstance
  countable := inferInstance

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private noncomputable def unitaryLinearIsometryEquiv
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : unitary (H →L[ℂ] H)) :
    H ≃ₗᵢ[ℂ] H where
  toFun := U
  invFun := ((U⁻¹ : unitary (H →L[ℂ] H)) : H →L[ℂ] H)
  left_inv x := by
    change (↑(U⁻¹ * U) : H →L[ℂ] H) x = x
    simp only [inv_mul_cancel, OneMemClass.coe_one, one_apply_eq_self]
  right_inv x := by
    change (↑(U * U⁻¹) : H →L[ℂ] H) x = x
    simp only [mul_inv_cancel, OneMemClass.coe_one, one_apply_eq_self]
  map_add' x y := map_add (U : H →L[ℂ] H) x y
  map_smul' c x := map_smul (U : H →L[ℂ] H) c x
  norm_map' := ContinuousLinearMap.norm_map_of_mem_unitary U.property



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private noncomputable def linearIsometryEquivUnitary
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : H ≃ₗᵢ[ℂ] H) :
    unitary (H →L[ℂ] H) :=
  ⟨(e : H →L[ℂ] H), by
    rw [Unitary.mem_iff, e.star_eq_symm]
    constructor <;> ext x <;> simp⟩



namespace FiniteIndex

variable {G : Type u} [Group G] (S : Subgroup G)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private noncomputable def correction (g : G) (q : G ⧸ S) : S :=
  ⟨(Quotient.out (g • q))⁻¹ * g * Quotient.out q, by
    have hrel : QuotientGroup.leftRel S
        (Quotient.out (g • q)) (g * Quotient.out q) := by
      apply Quotient.exact'
      calc
        QuotientGroup.mk (Quotient.out (g • q)) = g • q :=
          Quotient.out_eq _
        _ = g • QuotientGroup.mk (Quotient.out q) := by
          exact congrArg (fun r : G ⧸ S ↦ g • r) (Quotient.out_eq q).symm
        _ = QuotientGroup.mk (g * Quotient.out q) := rfl
    exact (by
      simpa only [mul_assoc] using
        (QuotientGroup.leftRel_apply (s := S)).mp hrel)⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem correction_coe (g : G) (q : G ⧸ S) :
    (correction S g q : G) =
      (Quotient.out (g • q))⁻¹ * g * Quotient.out q :=
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem correction_mul (g h : G) (q : G ⧸ S) :
    correction S (g * h) q =
      correction S g (h • q) * correction S h q := by
  apply Subtype.ext
  simp only [correction, mul_smul, mul_assoc, MulMemClass.mk_mul_mk, mul_inv_cancel_left]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem correction_one (q : G ⧸ S) :
    correction S 1 q = 1 := by
  apply Subtype.ext
  simp only [correction, one_smul, mul_one, inv_mul_cancel, OneMemClass.coe_one]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem subgroup_smul_baseCoset (s : S) :
    (s : G) • (QuotientGroup.mk 1 : G ⧸ S) =
      QuotientGroup.mk 1 := by
  apply Quotient.sound
  change QuotientGroup.leftRel S ((s : G) * 1) 1
  rw [QuotientGroup.leftRel_apply]
  simp only [mul_one, inv_mem_iff, SetLike.coe_mem]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quotientOut_baseCoset_mem :
    Quotient.out (QuotientGroup.mk 1 : G ⧸ S) ∈ S := by
  let q₀ : G ⧸ S := QuotientGroup.mk 1
  have hrel : QuotientGroup.leftRel S (Quotient.out q₀) 1 := by
    apply Quotient.exact'
    exact Quotient.out_eq q₀
  have hinv : (Quotient.out q₀)⁻¹ ∈ S := by
    simpa only [inv_mem_iff, QuotientGroup.leftRel_apply, mul_one] using hrel
  exact S.inv_mem_iff.mp hinv

section Induced

variable [S.FiniteIndex]
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
noncomputable local instance finiteIndexQuotientFintype : Fintype (G ⧸ S) :=
  S.fintypeQuotientOfFiniteIndex

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private abbrev InducedSpace :=
  PiLp 2 (fun _ : G ⧸ S ↦ H)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private noncomputable def inducedLinearIsometryEquiv
    (π : UnitaryRepresentation S H) (g : G) :
    InducedSpace (H := H) S ≃ₗᵢ[ℂ] InducedSpace (H := H) S := by
  exact
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ H (MulAction.toPerm g)).trans
      (LinearIsometryEquiv.piLpCongrRight 2
        (fun q ↦ unitaryLinearIsometryEquiv
          (π (correction S g (g⁻¹ • q)))))



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private noncomputable def inducedUnitary
    (π : UnitaryRepresentation S H) (g : G) :
    unitary (InducedSpace (H := H) S →L[ℂ] InducedSpace (H := H) S) :=
  linearIsometryEquivUnitary (inducedLinearIsometryEquiv S π g)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem inducedUnitary_apply
    (π : UnitaryRepresentation S H) (g : G)
    (ξ : InducedSpace (H := H) S) (q : G ⧸ S) :
    (inducedUnitary S π g :
      InducedSpace (H := H) S →L[ℂ] InducedSpace (H := H) S) ξ q =
      (π (correction S g (g⁻¹ • q)) : H →L[ℂ] H)
        (ξ (g⁻¹ • q)) := by
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private noncomputable def inducedRepresentation
    (π : UnitaryRepresentation S H) :
    UnitaryRepresentation G (InducedSpace (H := H) S) where
  toFun := inducedUnitary S π
  map_one' := by
    apply Subtype.ext
    ext ξ q
    simp only [inducedUnitary_apply, inv_one, one_smul, correction_one, map_one,
      OneMemClass.coe_one, one_apply_eq_self]
  map_mul' g h := by
    apply Subtype.ext
    ext ξ q
    simp only [inducedUnitary_apply, Submonoid.coe_mul, mul_apply_eq_comp]
    rw [correction_mul]
    simp only [mul_inv_rev, mul_smul, smul_inv_smul, map_mul, Submonoid.coe_mul, mul_apply_eq_comp]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem inducedRepresentation_apply
    (π : UnitaryRepresentation S H) (g : G)
    (ξ : InducedSpace (H := H) S) (q : G ⧸ S) :
    (inducedRepresentation S π g :
      InducedSpace (H := H) S →L[ℂ] InducedSpace (H := H) S) ξ q =
      (π (correction S g (g⁻¹ • q)) : H →L[ℂ] H)
        (ξ (g⁻¹ • q)) :=
  rfl

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem inducedSpace_norm_le_sum_norm_apply
    (ξ : InducedSpace (H := H) S) :
    ‖ξ‖ ≤ ∑ q : G ⧸ S, ‖ξ q‖ := by
  classical
  have hξ :
      ξ = ∑ q : G ⧸ S, PiLp.single 2 q (ξ q) := by
    ext q
    simp only [WithLp.ofLp_sum, PiLp.ofLp_single, Finset.sum_apply, Finset.sum_pi_single,
      Finset.mem_univ, ↓reduceIte]
  calc
    ‖ξ‖ = ‖∑ q : G ⧸ S, PiLp.single 2 q (ξ q)‖ :=
      congrArg norm hξ
    _ ≤ ∑ q : G ⧸ S, ‖ξ q‖ := by
      simpa only [PiLp.norm_single] using
        (norm_sum_le Finset.univ
          (fun q : G ⧸ S ↦ PiLp.single 2 q (ξ q)))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem inducedRepresentation_hasAlmostInvariantUnitVectors
    (π : UnitaryRepresentation S H)
    (hπ : π.HasAlmostInvariantUnitVectors) :
    (inducedRepresentation S π).HasAlmostInvariantUnitVectors := by
  classical
  intro K ε hε
  let n : ℝ := Fintype.card (G ⧸ S)
  let δ : ℝ := ε / (n + 1)
  have hn : 0 ≤ n := by
    dsimp [n]
    positivity
  have hden : 0 < n + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  let T : Finset S :=
    K.biUnion fun g ↦
      Finset.univ.image fun q : G ⧸ S ↦
        correction S g (g⁻¹ • q)
  obtain ⟨v, hvnorm, hvclose⟩ := hπ T δ hδ
  let raw : InducedSpace (H := H) S :=
    WithLp.toLp 2 (fun _ : G ⧸ S ↦ v)
  let q₀ : G ⧸ S := QuotientGroup.mk 1
  have hraw_lower : 1 ≤ ‖raw‖ := by
    have hcoord := PiLp.norm_apply_le raw q₀
    simpa [raw, q₀, hvnorm] using hcoord
  have hraw_pos : 0 < ‖raw‖ := zero_lt_one.trans_le hraw_lower
  let a : ℂ := ((‖raw‖⁻¹ : ℝ) : ℂ)
  let ξ : InducedSpace (H := H) S := a • raw
  have ha_norm : ‖a‖ = ‖raw‖⁻¹ := by
    simp [a]
  have ha_le_one : ‖a‖ ≤ 1 := by
    rw [ha_norm]
    exact inv_le_one_of_one_le₀ hraw_lower
  have hξnorm : ‖ξ‖ = 1 := by
    rw [show ξ = a • raw by rfl, norm_smul, ha_norm]
    exact inv_mul_cancel₀ hraw_pos.ne'
  refine ⟨ξ, hξnorm, ?_⟩
  intro g hg
  have hcoordinate :
      ∀ q : G ⧸ S,
        ‖((inducedRepresentation S π g :
            InducedSpace (H := H) S →L[ℂ] InducedSpace (H := H) S) ξ - ξ) q‖ < δ := by
    intro q
    have hmem : correction S g (g⁻¹ • q) ∈ T := by
      apply Finset.mem_biUnion.mpr
      refine ⟨g, hg, ?_⟩
      apply Finset.mem_image.mpr
      exact ⟨q, Finset.mem_univ q, rfl⟩
    have hclose := hvclose (correction S g (g⁻¹ • q)) hmem
    have hformula :
        ((inducedRepresentation S π g :
            InducedSpace (H := H) S →L[ℂ] InducedSpace (H := H) S) ξ - ξ) q =
          a •
            ((π (correction S g (g⁻¹ • q)) : H →L[ℂ] H) v - v) := by
      simp [ξ, raw, map_smul, smul_sub]
    rw [hformula, norm_smul]
    calc
      ‖a‖ * ‖(π (correction S g (g⁻¹ • q)) : H →L[ℂ] H) v - v‖ ≤
          1 * ‖(π (correction S g (g⁻¹ • q)) : H →L[ℂ] H) v - v‖ :=
        mul_le_mul_of_nonneg_right ha_le_one (norm_nonneg _)
      _ < δ := by simpa using hclose
  calc
    ‖(inducedRepresentation S π g :
        InducedSpace (H := H) S →L[ℂ] InducedSpace (H := H) S) ξ - ξ‖ ≤
        ∑ q : G ⧸ S,
          ‖((inducedRepresentation S π g :
              InducedSpace (H := H) S →L[ℂ] InducedSpace (H := H) S) ξ - ξ) q‖ :=
      inducedSpace_norm_le_sum_norm_apply S _
    _ < ∑ _q : G ⧸ S, δ :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        (fun q _ ↦ hcoordinate q)
    _ = n * δ := by
      simp [n]
    _ < ε := by
      dsimp [δ]
      rw [show n * (ε / (n + 1)) = (n * ε) / (n + 1) by ring]
      exact (div_lt_iff₀ hden).2 (by linarith)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem inducedInvariant_baseCoset_ne_zero
    (π : UnitaryRepresentation S H)
    (η : InducedSpace (H := H) S)
    (hη : η ≠ 0)
    (hinv : (inducedRepresentation S π).IsInvariant η) :
    η (QuotientGroup.mk 1 : G ⧸ S) ≠ 0 := by
  classical
  let q₀ : G ⧸ S := QuotientGroup.mk 1
  obtain ⟨q, hq⟩ : ∃ q : G ⧸ S, η q ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hη
    ext q
    exact hall q
  have hgq : Quotient.out q • q₀ = q := by
    calc
      Quotient.out q • q₀ =
          QuotientGroup.mk (Quotient.out q * 1) := rfl
      _ = QuotientGroup.mk (Quotient.out q) := by rw [mul_one]
      _ = q := Quotient.out_eq q
  have hinvq : (Quotient.out q)⁻¹ • q = q₀ := by
    calc
      (Quotient.out q)⁻¹ • q =
          (Quotient.out q)⁻¹ • (Quotient.out q • q₀) :=
        congrArg (fun r : G ⧸ S ↦ (Quotient.out q)⁻¹ • r) hgq.symm
      _ = q₀ := inv_smul_smul (Quotient.out q) q₀
  have heval :=
    congrArg (fun ζ : InducedSpace (H := H) S ↦
      ζ (Quotient.out q • q₀)) (hinv (Quotient.out q))
  have heval' :
      (π (correction S (Quotient.out q) q₀) : H →L[ℂ] H) (η q₀) =
        η q := by
    simpa only [inducedRepresentation_apply, hinvq, hgq] using heval
  intro hzero
  apply hq
  rw [← heval', hzero, map_zero]

omit [S.FiniteIndex] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem correction_conjugate_at_baseCoset
    (s : S) :
    let r : S :=
      ⟨Quotient.out (QuotientGroup.mk 1 : G ⧸ S),
        quotientOut_baseCoset_mem S⟩
    correction S ((r * s * r⁻¹ : S) : G)
      (QuotientGroup.mk 1 : G ⧸ S) = s := by
  dsimp only
  apply Subtype.ext
  rw [correction_coe]
  rw [subgroup_smul_baseCoset]
  simp only [mul_assoc, Subgroup.coe_mul, InvMemClass.coe_inv, inv_mul_cancel_left, inv_mul_cancel,
    mul_one]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem inducedInvariant_baseCoset_isInvariant
    (π : UnitaryRepresentation S H)
    (η : InducedSpace (H := H) S)
    (hinv : (inducedRepresentation S π).IsInvariant η) :
    π.IsInvariant (η (QuotientGroup.mk 1 : G ⧸ S)) := by
  intro s
  let q₀ : G ⧸ S := QuotientGroup.mk 1
  let r : S :=
    ⟨Quotient.out q₀, quotientOut_baseCoset_mem S⟩
  let t : S := r * s * r⁻¹
  have heval :=
    congrArg (fun ζ : InducedSpace (H := H) S ↦ ζ q₀)
      (hinv (t : G))
  have htfix : ((t : G)⁻¹) • q₀ = q₀ := by
    rw [← Subgroup.coe_inv]
    exact subgroup_smul_baseCoset S t⁻¹
  have hcorr : correction S (t : G) q₀ = s := by
    simpa [t, r, q₀] using correction_conjugate_at_baseCoset S s
  simpa only [inducedRepresentation_apply, htfix, hcorr] using heval

end Induced

end FiniteIndex

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem hasKazhdanPropertyT_subgroup_of_finiteIndex
    (G : CountableDiscreteGroup.{u}) (S : Subgroup G)
    [S.FiniteIndex]
    (hG : HasKazhdanPropertyT G) :
    HasKazhdanPropertyT (G.subgroup S) := by
  intro H _ _ _ π hπ
  let := S.fintypeQuotientOfFiniteIndex
  obtain ⟨η, hη, hinv⟩ :=
    hG (FiniteIndex.InducedSpace (H := H) S)
      inferInstance inferInstance inferInstance
      (FiniteIndex.inducedRepresentation S π)
      (FiniteIndex.inducedRepresentation_hasAlmostInvariantUnitVectors S π hπ)
  exact
    ⟨η (QuotientGroup.mk 1 : G ⧸ S),
      FiniteIndex.inducedInvariant_baseCoset_ne_zero S π η hη hinv,
      FiniteIndex.inducedInvariant_baseCoset_isInvariant S π η hinv⟩

end

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev F := ZMod 2

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev R := Polynomial F

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev V := Fin 4 → R

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def e : V := fun i ↦ if i = 0 then 1 else 0



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem e_apply (i : Fin 4) : e i = if i = 0 then 1 else 0 := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem e_ne_zero : e ≠ 0 := by
  intro h
  have := congrFun h (0 : Fin 4)
  simp only [e, Fin.isValue, ↓reduceIte, Pi.zero_apply, one_ne_zero] at this

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev T := TensorProduct F V V

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def square (v : V) : T := v ⊗ₜ[F] v

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def B : Submodule F T := Submodule.span F (Set.range square)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev D := V × B



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem square_add (u v : V) :
    square (u + v) = square u + square v +
      (u ⊗ₜ[F] v + v ⊗ₜ[F] u) := by
  simp only [square, TensorProduct.add_tmul, TensorProduct.tmul_add]
  ac_rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem square_mem (v : V) : square v ∈ B := by
  exact Submodule.subset_span ⟨v, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def diagonal (v : V) : B := ⟨square v, square_mem v⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem diagonal_val (v : V) : (diagonal v : T) = square v := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem symmetric_tmul_mem (u v : V) :
    u ⊗ₜ[F] v + v ⊗ₜ[F] u ∈ B := by
  have h := B.sub_mem (B.sub_mem (square_mem (u + v)) (square_mem u))
    (square_mem v)
  rw [square_add] at h
  simpa only [add_assoc, add_sub_cancel_left] using h

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def polarization (u v : V) : B :=
  ⟨u ⊗ₜ[F] v + v ⊗ₜ[F] u, symmetric_tmul_mem u v⟩



/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem diagonal_add (u v : V) :
    diagonal (u + v) = diagonal u + diagonal v + polarization u v := by
  apply Subtype.ext
  exact square_add u v

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem add_self_eq_zero {M : Type*} [AddCommGroup M] [Module F M]
    (x : M) : x + x = 0 := by
  calc
    x + x = ((1 : F) + 1) • x := by rw [add_smul, one_smul]
    _ = 0 := by rw [show (1 : F) + 1 = 0 by decide, zero_smul]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem D_add_self (d : D) : d + d = 0 := add_self_eq_zero d

end

section

open Polynomial

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev TruncatedPolynomial (n : ℕ) :=
  AdjoinRoot ((X : R) ^ n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev TruncatedVector (n : ℕ) :=
  Fin 4 → TruncatedPolynomial n

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
noncomputable def truncatedPolynomialEquiv (n : ℕ) :
    TruncatedPolynomial n ≃ₗ[F] (Fin n → F) := by
  let e :=
    (AdjoinRoot.powerBasisAux' (monic_X_pow n : ((X : R) ^ n).Monic)).equivFun
  rw [natDegree_X_pow] at e
  exact e

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
noncomputable def truncatedVectorEquiv (n : ℕ) :
    TruncatedVector n ≃ₗ[F] (Fin 4 → Fin n → F) :=
  LinearEquiv.piCongrRight fun _ => truncatedPolynomialEquiv n

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def truncatePolynomial (n : ℕ) : R →ₗ[F] TruncatedPolynomial n :=
  (AdjoinRoot.mkₐ ((X : R) ^ n)).toLinearMap



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def truncateVector (n : ℕ) : V →ₗ[F] TruncatedVector n :=
  (truncatePolynomial n).compLeft (Fin 4)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem truncateVector_apply (n : ℕ) (v : V) (i : Fin 4) :
    truncateVector n v i = AdjoinRoot.mk ((X : R) ^ n) (v i) :=
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem truncatePolynomial_surjective (n : ℕ) :
    Function.Surjective (truncatePolynomial n) :=
  AdjoinRoot.mk_surjective

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem truncateVector_surjective (n : ℕ) :
    Function.Surjective (truncateVector n) := by
  intro w
  choose v hv using fun i : Fin 4 => truncatePolynomial_surjective n (w i)
  exact ⟨v, funext hv⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def shiftedSubmodule (n : ℕ) : Submodule F V :=
  LinearMap.ker (truncateVector n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem mem_shiftedSubmodule_iff (n : ℕ) (v : V) :
    v ∈ shiftedSubmodule n ↔ ∀ i : Fin 4, (X : R) ^ n ∣ v i := by
  change truncateVector n v = 0 ↔ _
  simp only [funext_iff, Pi.zero_apply, truncateVector_apply,
    AdjoinRoot.mk_eq_zero]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev ShiftedQuotient (n : ℕ) :=
  V ⧸ shiftedSubmodule n

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
noncomputable def shiftedQuotientEquiv (n : ℕ) :
    ShiftedQuotient n ≃ₗ[F] TruncatedVector n :=
  (truncateVector n).quotKerEquivOfSurjective (truncateVector_surjective n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
noncomputable def shiftedQuotientCoeffEquiv (n : ℕ) :
    ShiftedQuotient n ≃ₗ[F] (Fin 4 → Fin n → F) :=
  (shiftedQuotientEquiv n).trans (truncatedVectorEquiv n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem truncatedVector_card (n : ℕ) :
    Nat.card (TruncatedVector n) = 2 ^ (4 * n) := by
  rw [Nat.card_congr (truncatedVectorEquiv n).toEquiv]
  simp only [Nat.card_eq_fintype_card, Fintype.card_pi, ZMod.card, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← pow_mul, Nat.mul_comm]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem shiftedQuotient_card (n : ℕ) :
    Nat.card (ShiftedQuotient n) = 2 ^ (4 * n) := by
  rw [Nat.card_congr (shiftedQuotientEquiv n).toEquiv]
  exact truncatedVector_card n

end

end

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev Index := Fin 4

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev IntegralPolynomial := Polynomial ℤ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance : Countable IntegralPolynomial :=
  ((AddMonoidAlgebra.coeffEquiv (R := ℤ) (M := ℕ)).injective.comp
    Polynomial.toFinsupp_injective).countable

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev BinaryPolynomial := R

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance : Countable BinaryPolynomial :=
  ((AddMonoidAlgebra.coeffEquiv (R := F) (M := ℕ)).injective.comp
    Polynomial.toFinsupp_injective).countable

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev IntegralSpecialLinearGroup :=
  Matrix.SpecialLinearGroup Index IntegralPolynomial

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance : Countable IntegralSpecialLinearGroup := by
  let f : IntegralSpecialLinearGroup → Index → Index → IntegralPolynomial :=
    fun g i j => g i j
  exact (show Function.Injective f by
    intro g h hgh
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact congrFun (congrFun hgh i) j).countable

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev TernarySpecialLinearGroup :=
  Matrix.SpecialLinearGroup Index (ZMod 3)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev Q := Matrix.SpecialLinearGroup Index BinaryPolynomial



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def modThreeAtZero : IntegralPolynomial →+* ZMod 3 :=
  (Int.castRingHom (ZMod 3)).comp (Polynomial.evalRingHom (0 : ℤ))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem modThreeAtZero_apply (p : IntegralPolynomial) :
    modThreeAtZero p = ((p.eval (0 : ℤ) : ℤ) : ZMod 3) := rfl





/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def modThreeGroupHom : IntegralSpecialLinearGroup →* TernarySpecialLinearGroup :=
  Matrix.SpecialLinearGroup.map modThreeAtZero



/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev K := modThreeGroupHom.ker

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance : Countable K := inferInstance

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def integralGroup : ConnesRigidity.CountableDiscreteGroup where
  Carrier := IntegralSpecialLinearGroup
  group := inferInstance
  countable := inferInstance

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def actingGroup : ConnesRigidity.CountableDiscreteGroup where
  Carrier := K
  group := inferInstance
  countable := inferInstance

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
instance : modThreeGroupHom.ker.FiniteIndex := Subgroup.finiteIndex_ker modThreeGroupHom

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def modTwoPolynomial : IntegralPolynomial →+* BinaryPolynomial :=
  Polynomial.mapRingHom (Int.castRingHom (ZMod 2))







/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def modTwoGroupHom : IntegralSpecialLinearGroup →* Q :=
  Matrix.SpecialLinearGroup.map modTwoPolynomial



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def pi₂ : K →* Q := modTwoGroupHom.comp modThreeGroupHom.ker.subtype





/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem modTwoPolynomial_surjective : Function.Surjective modTwoPolynomial := by
  exact Polynomial.map_surjective _ (ZMod.ringHom_surjective _)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem specialLinear_map_transvection_baseChange
    {ι A B : Type*} [Fintype ι] [DecidableEq ι] [CommRing A] [CommRing B]
    (f : A →+* B) {i j : ι} (hij : i ≠ j) (a : A) :
    Matrix.SpecialLinearGroup.map f (Matrix.SpecialLinearGroup.transvection hij a) =
      Matrix.SpecialLinearGroup.transvection hij (f a) := by
  apply Matrix.SpecialLinearGroup.ext
  intro k l
  change f ((if k = l then 1 else 0) + if i = k ∧ j = l then a else 0) =
    (if k = l then 1 else 0) + if i = k ∧ j = l then f a else 0
  split <;> split <;> simp_all

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem integralTransvection_mem_KSubgroup
    {i j : Index} (hij : i ≠ j) (a : IntegralPolynomial) :
    Matrix.SpecialLinearGroup.transvection hij ((3 : IntegralPolynomial) * a) ∈
      modThreeGroupHom.ker := by
  change modThreeGroupHom
    (Matrix.SpecialLinearGroup.transvection hij ((3 : IntegralPolynomial) * a)) = 1
  rw [show modThreeGroupHom
      (Matrix.SpecialLinearGroup.transvection hij ((3 : IntegralPolynomial) * a)) =
      Matrix.SpecialLinearGroup.transvection hij
        (modThreeAtZero ((3 : IntegralPolynomial) * a)) from
    specialLinear_map_transvection_baseChange modThreeAtZero hij
      ((3 : IntegralPolynomial) * a)]
  rw [map_mul]
  have hthree : modThreeAtZero (3 : IntegralPolynomial) = 0 := by
    rw [map_ofNat modThreeAtZero 3]
    exact ZMod.natCast_self 3
  simp only [hthree, modThreeAtZero_apply, zero_mul,
    Matrix.SpecialLinearGroup.transvection_coeff_zero]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def liftedIntegralTransvection {i j : Index} (hij : i ≠ j)
    (a : IntegralPolynomial) : K :=
  ⟨Matrix.SpecialLinearGroup.transvection hij ((3 : IntegralPolynomial) * a),
    integralTransvection_mem_KSubgroup hij a⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem pi₂_liftedIntegralTransvection {i j : Index} (hij : i ≠ j)
    (a : IntegralPolynomial) :
    pi₂ (liftedIntegralTransvection hij a) =
      Matrix.SpecialLinearGroup.transvection hij (modTwoPolynomial a) := by
  change modTwoGroupHom
    (Matrix.SpecialLinearGroup.transvection hij ((3 : IntegralPolynomial) * a)) = _
  rw [show modTwoGroupHom
      (Matrix.SpecialLinearGroup.transvection hij ((3 : IntegralPolynomial) * a)) =
      Matrix.SpecialLinearGroup.transvection hij
        (modTwoPolynomial ((3 : IntegralPolynomial) * a)) from
    specialLinear_map_transvection_baseChange modTwoPolynomial hij
      ((3 : IntegralPolynomial) * a)]
  congr 1
  rw [map_mul, map_ofNat modTwoPolynomial 3]
  have hthree : (3 : BinaryPolynomial) = 1 := by
    rw [← Polynomial.C_ofNat]
    rw [show (3 : ZMod 2) = 1 by decide, Polynomial.C_1]
  rw [hthree, one_mul]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_pi₂_eq_transvection {i j : Index} (hij : i ≠ j)
    (b : BinaryPolynomial) :
    ∃ k : K, pi₂ k = Matrix.SpecialLinearGroup.transvection hij b := by
  obtain ⟨a, rfl⟩ := modTwoPolynomial_surjective b
  exact ⟨liftedIntegralTransvection hij a,
    pi₂_liftedIntegralTransvection hij a⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def elementaryTransvections : Set Q :=
  {g | ∃ (i j : Index) (hij : i ≠ j) (a : BinaryPolynomial),
    g = Matrix.SpecialLinearGroup.transvection hij a}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem elementaryTransvections_subset_pi₂_range :
    elementaryTransvections ⊆ pi₂.range := by
  rintro _ ⟨i, j, hij, a, rfl⟩
  exact exists_pi₂_eq_transvection hij a

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem elementaryClosure_le_pi₂_range :
    Subgroup.closure elementaryTransvections ≤ pi₂.range :=
  (Subgroup.closure_le _).2 elementaryTransvections_subset_pi₂_range

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def ElementaryGeneration : Prop :=
  Subgroup.closure elementaryTransvections = ⊤

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem pi₂_surjective_of_elementaryGeneration
    (h : ElementaryGeneration) : Function.Surjective pi₂ := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← h]
  exact elementaryClosure_le_pi₂_range

end

section

open Finset Polynomial

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomial_matrix_eq_one_of_pow_eq_one_of_eval_zero_eq_one
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n (Polynomial ℤ)) (m : ℕ) (hm : 0 < m)
    (hpow : A ^ m = 1)
    (heval : (Polynomial.evalRingHom (0 : ℤ)).mapMatrix A = 1) :
    A = 1 := by
  let S : Matrix n n (Polynomial ℤ) := ∑ i ∈ range m, A ^ i
  have hS : (A - 1) * S = 0 := by
    dsimp [S]
    rw [mul_geom_sum, hpow, sub_self]
  have hSeval : (Polynomial.evalRingHom (0 : ℤ)).mapMatrix S =
      (m : ℤ) • (1 : Matrix n n ℤ) := by
    dsimp [S]
    simp only [map_sum, map_pow, heval, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one,
      zsmul_eq_mul, Int.cast_natCast]
  have hdet_eval : (Polynomial.evalRingHom (0 : ℤ)) S.det =
      (m : ℤ) ^ Fintype.card n := by
    rw [RingHom.map_det, hSeval, Matrix.det_smul, Matrix.det_one, mul_one]
  have hdet : S.det ≠ 0 := by
    intro h
    rw [h, map_zero] at hdet_eval
    have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
    exact (pow_ne_zero _ hmz) hdet_eval.symm
  have hSmul : (A - 1) * (S.det • (1 : Matrix n n (Polynomial ℤ))) = 0 := by
    rw [← Matrix.mul_adjugate S, ← Matrix.mul_assoc, hS, Matrix.zero_mul]
  have hA : A - 1 = 0 := by
    apply Matrix.ext
    intro i j
    have hentry := congrArg (fun B : Matrix n n (Polynomial ℤ) => B i j) hSmul
    simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply,
      smul_eq_mul, Matrix.zero_apply] at hentry
    exact (mul_eq_zero.mp hentry).resolve_left hdet
  exact sub_eq_zero.mp hA

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev IntegerSpecialLinearGroup := Matrix.SpecialLinearGroup Index ℤ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def constantTermGroupHom : IntegralSpecialLinearGroup →* IntegerSpecialLinearGroup :=
  Matrix.SpecialLinearGroup.map (Polynomial.evalRingHom (0 : ℤ))



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def levelThreeIntegerReduction : IntegerSpecialLinearGroup →* TernarySpecialLinearGroup :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 3))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def levelThreeIntegerSubgroup : Subgroup IntegerSpecialLinearGroup :=
  levelThreeIntegerReduction.ker

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem levelThreeIntegerReduction_constantTerm (g : IntegralSpecialLinearGroup) :
    levelThreeIntegerReduction (constantTermGroupHom g) = modThreeGroupHom g := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem constantTerm_mem_levelThreeIntegerSubgroup (g : K) :
    constantTermGroupHom (g : IntegralSpecialLinearGroup) ∈
      levelThreeIntegerSubgroup := by
  change levelThreeIntegerReduction
    (constantTermGroupHom (g : IntegralSpecialLinearGroup)) = 1
  rw [levelThreeIntegerReduction_constantTerm]
  exact g.property

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def constantTermToLevelThree : K →* levelThreeIntegerSubgroup where
  toFun g :=
    ⟨constantTermGroupHom (g : IntegralSpecialLinearGroup),
      constantTerm_mem_levelThreeIntegerSubgroup g⟩
  map_one' := by
    apply Subtype.ext
    exact constantTermGroupHom.map_one
  map_mul' g h := by
    apply Subtype.ext
    exact constantTermGroupHom.map_mul
      (g : IntegralSpecialLinearGroup) (h : IntegralSpecialLinearGroup)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem constantTermToLevelThree_apply_coe (g : K) :
    (constantTermToLevelThree g : IntegerSpecialLinearGroup) =
      constantTermGroupHom (g : IntegralSpecialLinearGroup) := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integralSpecialLinear_eq_one_of_pow_eq_one_of_constantTerm_eq_one
    (g : IntegralSpecialLinearGroup) (m : ℕ) (hm : 0 < m)
    (hpow : g ^ m = 1)
    (hconst : constantTermGroupHom g = 1) :
    g = 1 := by
  have hmatrixpow : (g : Matrix Index Index (Polynomial ℤ)) ^ m = 1 := by
    simpa only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] using congrArg
      (fun h : IntegralSpecialLinearGroup =>
        (h : Matrix Index Index (Polynomial ℤ))) hpow
  have hmatrixconst :
      (Polynomial.evalRingHom (0 : ℤ)).mapMatrix
        (g : Matrix Index Index (Polynomial ℤ)) = 1 := by
    simpa only [RingHom.mapMatrix_apply, coe_evalRingHom, constantTermGroupHom,
      Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.coe_one] using congrArg
      (fun h : IntegerSpecialLinearGroup => (h : Matrix Index Index ℤ)) hconst
  have hmatrix := polynomial_matrix_eq_one_of_pow_eq_one_of_eval_zero_eq_one
    (g : Matrix Index Index (Polynomial ℤ)) m hm hmatrixpow hmatrixconst
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  exact congrArg (fun A : Matrix Index Index (Polynomial ℤ) => A i j) hmatrix

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def LevelThreeIntegerTorsionFree : Prop :=
  ∀ g : levelThreeIntegerSubgroup, IsOfFinOrder g → g = 1

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem K_eq_one_of_pow_eq_one_of_levelThree_torsionFree
    (hlevel : LevelThreeIntegerTorsionFree)
    (g : K) (m : ℕ) (hm : 0 < m) (hpow : g ^ m = 1) :
    g = 1 := by
  have hfinite : IsOfFinOrder g :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, hpow⟩
  have hconstant : constantTermToLevelThree g = 1 :=
    hlevel (constantTermToLevelThree g)
      (constantTermToLevelThree.isOfFinOrder hfinite)
  have hconst :
      constantTermGroupHom (g : IntegralSpecialLinearGroup) = 1 := by
    simpa only [constantTermToLevelThree_apply_coe, OneMemClass.coe_one] using congrArg
      (fun h : levelThreeIntegerSubgroup =>
        (h : IntegerSpecialLinearGroup)) hconstant
  have hpow' : (g : IntegralSpecialLinearGroup) ^ m = 1 := by
    simpa only [SubmonoidClass.coe_pow, OneMemClass.coe_one] using congrArg
      (fun h : K => (h : IntegralSpecialLinearGroup)) hpow
  have hpolynomial : (g : IntegralSpecialLinearGroup) = 1 :=
    integralSpecialLinear_eq_one_of_pow_eq_one_of_constantTerm_eq_one
      (g : IntegralSpecialLinearGroup) m hm hpow' hconst
  apply Subtype.ext
  exact hpolynomial

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem K_no_nontrivial_torsion_of_levelThree_torsionFree
    (hlevel : LevelThreeIntegerTorsionFree) :
    ∀ g : K, IsOfFinOrder g → g = 1 := by
  intro g hg
  obtain ⟨m, hm, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hg
  exact K_eq_one_of_pow_eq_one_of_levelThree_torsionFree hlevel g m hm hpow

end

section

variable {G : Type*} [Group G]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem fg_of_finiteIndex_subgroup (H : Subgroup G) [H.FiniteIndex]
    (hH : Group.FG H) : Group.FG G := by
  classical
  obtain ⟨R, hR, _⟩ := H.exists_isComplement_right 1
  have hRfg : (Subgroup.closure R).FG :=
    (Subgroup.fg_iff _).2 ⟨R, rfl, hR.finite_right⟩
  have hHfg : H.FG := (Group.fg_iff_subgroup_fg H).1 hH
  have htop : H ⊔ Subgroup.closure R = ⊤ := by
    apply top_unique
    intro g _
    let r := hR.toRightFun g
    have hh : g * (r : G)⁻¹ ∈ H := hR.mul_inv_toRightFun_mem g
    have hr : (r : G) ∈ Subgroup.closure R :=
      Subgroup.subset_closure r.property
    have hg : (g * (r : G)⁻¹) * (r : G) ∈ H ⊔ Subgroup.closure R :=
      (H ⊔ Subgroup.closure R).mul_mem
        (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hr)
    simpa only [inv_mul_cancel_right] using hg
  exact Group.fg_def.2 (htop ▸ hHfg.sup hRfg)

end

section

open ConnesRigidity
open scoped ENNReal

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private abbrev finiteGeneratedCosetIndex (G : CountableDiscreteGroup.{u}) :=
  Σ F : Finset G, G ⧸ Subgroup.closure (F : Set G)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private noncomputable def finiteGeneratedCosetEquiv
    (G : CountableDiscreteGroup.{u}) (g : G) :
    finiteGeneratedCosetIndex G ≃ finiteGeneratedCosetIndex G where
  toFun x := ⟨x.1, g • x.2⟩
  invFun x := ⟨x.1, g⁻¹ • x.2⟩
  left_inv x := by
    rcases x with ⟨F, q⟩
    simp only [inv_smul_smul]
  right_inv x := by
    rcases x with ⟨F, q⟩
    simp only [smul_inv_smul]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private noncomputable def finiteGeneratedCosetRepresentation
    (G : CountableDiscreteGroup.{u}) :
    UnitaryRepresentation G (GroupL2 (finiteGeneratedCosetIndex G)) where
  toFun g :=
    Unitary.linearIsometryEquiv.symm
      (l2Reindex (finiteGeneratedCosetEquiv G g))
  map_one' := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro ξ
    ext x
    rcases x with ⟨F, q⟩
    change ξ ⟨F, (1 : G)⁻¹ • q⟩ = ξ ⟨F, q⟩
    simp only [inv_one, one_smul]
  map_mul' g h := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro ξ
    ext x
    rcases x with ⟨F, q⟩
    change ξ ⟨F, (g * h)⁻¹ • q⟩ =
      ξ ⟨F, h⁻¹ • g⁻¹ • q⟩
    simp only [mul_inv_rev, mul_smul]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem finiteGeneratedCosetRepresentation_apply
    (G : CountableDiscreteGroup.{u}) (g : G)
    (ξ : GroupL2 (finiteGeneratedCosetIndex G))
    (F : Finset G) (q : G ⧸ Subgroup.closure (F : Set G)) :
    (finiteGeneratedCosetRepresentation G g :
      GroupL2 (finiteGeneratedCosetIndex G) →L[ℂ]
        GroupL2 (finiteGeneratedCosetIndex G)) ξ ⟨F, q⟩ =
      ξ ⟨F, g⁻¹ • q⟩ :=
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem finiteGeneratedCoset_l2Reindex_single
    {α β : Type u} (e : α ≃ β) [DecidableEq α] [DecidableEq β]
    (i : α) (z : ℂ) :
    l2Reindex e (lp.single 2 i z) = lp.single 2 (e i) z := by
  ext j
  simp only [l2Reindex_apply, lp.single_apply]
  by_cases h : e.symm j = i
  · have hj : j = e i := by
      simpa only [Equiv.apply_symm_apply] using congrArg e h
    simp only [hj, Equiv.symm_apply_apply, Pi.single_eq_same]
  · have hj : j ≠ e i := by
      intro hj
      apply h
      simp only [hj, Equiv.symm_apply_apply]
    simp only [ne_eq, h, not_false_eq_true, Pi.single_eq_of_ne, hj]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private noncomputable def finiteGeneratedCosetBasepoint
    (G : CountableDiscreteGroup.{u}) (F : Finset G) :
    finiteGeneratedCosetIndex G :=
  ⟨F, QuotientGroup.mk (1 : G)⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem finiteGeneratedCosetEquiv_basepoint
    (G : CountableDiscreteGroup.{u}) (F : Finset G)
    (g : G) (hg : g ∈ F) :
    finiteGeneratedCosetEquiv G g (finiteGeneratedCosetBasepoint G F) =
      finiteGeneratedCosetBasepoint G F := by
  change
    (⟨F, g • (QuotientGroup.mk (1 : G) :
      G ⧸ Subgroup.closure (F : Set G))⟩ : finiteGeneratedCosetIndex G) =
      ⟨F, QuotientGroup.mk (1 : G)⟩
  apply congrArg
    (fun q : G ⧸ Subgroup.closure (F : Set G) ↦
      (⟨F, q⟩ : finiteGeneratedCosetIndex G))
  rw [MulAction.Quotient.smul_mk]
  apply QuotientGroup.eq.mpr
  simpa only [smul_eq_mul, mul_one, inv_mem_iff, SetLike.mem_coe] using
    (Subgroup.subset_closure (show g ∈ (F : Set G) from hg))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private noncomputable def finiteGeneratedCosetBasis
    (G : CountableDiscreteGroup.{u}) (F : Finset G) :
    GroupL2 (finiteGeneratedCosetIndex G) := by
  classical
  exact lp.single 2 (finiteGeneratedCosetBasepoint G F) (1 : ℂ)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem finiteGeneratedCosetBasis_norm
    (G : CountableDiscreteGroup.{u}) (F : Finset G) :
    ‖finiteGeneratedCosetBasis G F‖ = 1 := by
  classical
  simp only [finiteGeneratedCosetBasis, Nat.ofNat_pos, lp.norm_single, norm_one]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem finiteGeneratedCosetRepresentation_fixes_basis
    (G : CountableDiscreteGroup.{u}) (F : Finset G)
    (g : G) (hg : g ∈ F) :
    (finiteGeneratedCosetRepresentation G g :
      GroupL2 (finiteGeneratedCosetIndex G) →L[ℂ]
        GroupL2 (finiteGeneratedCosetIndex G))
      (finiteGeneratedCosetBasis G F) =
      finiteGeneratedCosetBasis G F := by
  classical
  change
    l2Reindex (finiteGeneratedCosetEquiv G g)
        (lp.single 2 (finiteGeneratedCosetBasepoint G F) (1 : ℂ)) =
      lp.single 2 (finiteGeneratedCosetBasepoint G F) (1 : ℂ)
  rw [finiteGeneratedCoset_l2Reindex_single,
    finiteGeneratedCosetEquiv_basepoint G F g hg]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem finiteGeneratedCosetRepresentation_hasAlmostInvariantUnitVectors
    (G : CountableDiscreteGroup.{u}) :
    (finiteGeneratedCosetRepresentation G).HasAlmostInvariantUnitVectors := by
  intro F ε hε
  refine ⟨finiteGeneratedCosetBasis G F,
    finiteGeneratedCosetBasis_norm G F, ?_⟩
  intro g hg
  rw [finiteGeneratedCosetRepresentation_fixes_basis G F g hg]
  simpa only [sub_self, norm_zero] using hε

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem finiteGeneratedCosetInvariant_constant
    (G : CountableDiscreteGroup.{u})
    (ξ : GroupL2 (finiteGeneratedCosetIndex G))
    (hξ : (finiteGeneratedCosetRepresentation G).IsInvariant ξ)
    (F : Finset G)
    (q r : G ⧸ Subgroup.closure (F : Set G)) :
    ξ ⟨F, q⟩ = ξ ⟨F, r⟩ := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G q r
  have hmove : g⁻¹ • r = q := by
    rw [← hg, inv_smul_smul]
  have h := congrArg
    (fun η : GroupL2 (finiteGeneratedCosetIndex G) ↦ η ⟨F, r⟩)
    (hξ g)
  simpa only [finiteGeneratedCosetRepresentation_apply, hmove] using h

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem finiteGeneratedCoset_component_summable
    (G : CountableDiscreteGroup.{u})
    (ξ : GroupL2 (finiteGeneratedCosetIndex G))
    (F : Finset G) :
    Summable (fun q : G ⧸ Subgroup.closure (F : Set G) ↦
      ‖ξ (⟨F, q⟩ : finiteGeneratedCosetIndex G)‖ ^ (2 : ℝ)) := by
  have hsum := (lp.memℓp ξ).summable
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hinj : Function.Injective
      (fun q : G ⧸ Subgroup.closure (F : Set G) ↦
        (⟨F, q⟩ : finiteGeneratedCosetIndex G)) := by
    intro q r hqr
    simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hqr
  simpa only [Real.rpow_ofNat, ENNReal.toReal_ofNat,
    Function.comp_def] using hsum.comp_injective hinj

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem finiteGeneratedCosetInvariant_eq_zero
    (G : CountableDiscreteGroup.{u})
    (hinfinite : ∀ F : Finset G,
      Infinite (G ⧸ Subgroup.closure (F : Set G)))
    (ξ : GroupL2 (finiteGeneratedCosetIndex G))
    (hξ : (finiteGeneratedCosetRepresentation G).IsInvariant ξ) :
    ξ = 0 := by
  ext x
  rcases x with ⟨F, q⟩
  change ξ ⟨F, q⟩ = 0
  by_contra hnonzero
  let : Infinite (G ⧸ Subgroup.closure (F : Set G)) := hinfinite F
  have hpositive : 0 < ‖ξ (⟨F, q⟩ : finiteGeneratedCosetIndex G)‖ ^ (2 : ℝ) := by
    positivity
  have hconstant :
      Summable (fun _ : G ⧸ Subgroup.closure (F : Set G) ↦
        ‖ξ (⟨F, q⟩ : finiteGeneratedCosetIndex G)‖ ^ (2 : ℝ)) := by
    have hsum := finiteGeneratedCoset_component_summable G ξ F
    convert hsum using 1
    funext r
    rw [finiteGeneratedCosetInvariant_constant G ξ hξ F r q]
  exact (Finite.of_summable_const hpositive hconstant).false

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem finiteGeneratedCoset_infinite_of_not_fg
    (G : CountableDiscreteGroup.{u})
    (hG : ¬Group.FG G) (F : Finset G) :
    Infinite (G ⧸ Subgroup.closure (F : Set G)) := by
  apply not_finite_iff_infinite.mp
  intro hfinite
  let : Finite (G ⧸ Subgroup.closure (F : Set G)) := hfinite
  let : (Subgroup.closure (F : Set G)).FiniteIndex :=
    Subgroup.finiteIndex_iff_finite_quotient.mpr inferInstance
  exact hG
    (fg_of_finiteIndex_subgroup (Subgroup.closure (F : Set G))
      (Group.closure_finset_fg F))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem hasKazhdanPropertyT_finitelyGenerated
    (G : CountableDiscreteGroup.{u})
    (hT : HasKazhdanPropertyT G) :
    Group.FG G := by
  by_contra hnotfg
  have hinfinite : ∀ F : Finset G,
      Infinite (G ⧸ Subgroup.closure (F : Set G)) :=
    finiteGeneratedCoset_infinite_of_not_fg G hnotfg
  obtain ⟨ξ, hξ, hinvariant⟩ :=
    hT (GroupL2 (finiteGeneratedCosetIndex G))
      inferInstance inferInstance inferInstance
      (finiteGeneratedCosetRepresentation G)
      (finiteGeneratedCosetRepresentation_hasAlmostInvariantUnitVectors G)
  exact hξ
    (finiteGeneratedCosetInvariant_eq_zero G hinfinite ξ hinvariant)

end

section

open ConnesRigidity

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def ErshovJaikinUniversalLatticePropertyT : Prop :=
  HasKazhdanPropertyT integralGroup

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem actingGroup_eq_integralGroup_subgroup :
    actingGroup = integralGroup.subgroup modThreeGroupHom.ker := by
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem actingGroup_hasKazhdanPropertyT
    (hUniversalLattice : ErshovJaikinUniversalLatticePropertyT) :
    HasKazhdanPropertyT actingGroup := by
  let : (show Subgroup integralGroup from modThreeGroupHom.ker).FiniteIndex := by
    change modThreeGroupHom.ker.FiniteIndex
    infer_instance
  rw [actingGroup_eq_integralGroup_subgroup]
  exact hasKazhdanPropertyT_subgroup_of_finiteIndex
    integralGroup modThreeGroupHom.ker hUniversalLattice

end

section

open Matrix
open scoped commutatorElement

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem specialLinear_transvection_commutator
    {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A]
    (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : A) :
    Matrix.SpecialLinearGroup.transvection hij a *
      Matrix.SpecialLinearGroup.transvection hjk b *
      (Matrix.SpecialLinearGroup.transvection hij a)⁻¹ *
      (Matrix.SpecialLinearGroup.transvection hjk b)⁻¹ =
      Matrix.SpecialLinearGroup.transvection hik (a * b) := by
  rw [Matrix.SpecialLinearGroup.transvection_inv hij a,
      Matrix.SpecialLinearGroup.transvection_inv hjk b]
  apply Subtype.ext
  change
    (1 + Matrix.single i j a) * (1 + Matrix.single j k b) *
      (1 + Matrix.single i j (-a)) * (1 + Matrix.single j k (-b)) =
      1 + Matrix.single i k (a * b)
  rw [← Matrix.single_neg, ← Matrix.single_neg]
  have hxx : Matrix.single i j a * Matrix.single i j a = 0 :=
    Matrix.single_mul_single_of_ne (c := a) i j i hij.symm a
  have hyy : Matrix.single j k b * Matrix.single j k b = 0 :=
    Matrix.single_mul_single_of_ne (c := b) j k j hjk.symm b
  have hyx : Matrix.single j k b * Matrix.single i j a = 0 :=
    Matrix.single_mul_single_of_ne (c := b) j k i hik.symm a
  have hxy : Matrix.single i j a * Matrix.single j k b =
      Matrix.single i k (a * b) :=
    Matrix.single_mul_single_same (c := a) i j k b
  have hzx : Matrix.single i k (a * b) * Matrix.single i j a = 0 :=
    Matrix.single_mul_single_of_ne (c := a * b) i k i hik.symm a
  have hzy : Matrix.single i k (a * b) * Matrix.single j k b = 0 :=
    Matrix.single_mul_single_of_ne (c := a * b) i k j hjk.symm b
  have hzz : Matrix.single i k (a * b) * Matrix.single i k (a * b) = 0 :=
    Matrix.single_mul_single_of_ne (c := a * b) i k i hik.symm (a * b)
  noncomm_ring [hxx, hyy, hyx, hxy, hzx, hzy, hzz]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem transvection_mul_mem_of_two_step
    {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A]
    (H : Subgroup (Matrix.SpecialLinearGroup ι A))
    (i k j : ι) (hik : i ≠ k) (hkj : k ≠ j) (hij : i ≠ j)
    (a b : A)
    (hleft : Matrix.SpecialLinearGroup.transvection hik a ∈ H)
    (hright : Matrix.SpecialLinearGroup.transvection hkj b ∈ H) :
    Matrix.SpecialLinearGroup.transvection hij (a * b) ∈ H := by
  rw [← specialLinear_transvection_commutator i k j hik hkj hij a b]
  exact H.mul_mem (H.mul_mem (H.mul_mem hleft hright) (H.inv_mem hleft))
    (H.inv_mem hright)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def transvectionCoefficientSubring
    {A : Type*} [CommRing A] (n : ℕ) (hn : 2 < n)
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A))
    (hone : ∀ (i j : Fin n) (h : i ≠ j),
      Matrix.SpecialLinearGroup.transvection h (1 : A) ∈ H) : Subring A where
  carrier :=
    {a | ∀ (i j : Fin n) (h : i ≠ j),
      Matrix.SpecialLinearGroup.transvection h a ∈ H}
  zero_mem' := by
    intro i j hij
    simpa only [Matrix.SpecialLinearGroup.transvection_coeff_zero] using H.one_mem
  one_mem' := hone
  add_mem' := by
    intro a b ha hb i j hij
    rw [Matrix.SpecialLinearGroup.transvection_add]
    exact H.mul_mem (ha i j hij) (hb i j hij)
  neg_mem' := by
    intro a ha i j hij
    rw [← Matrix.SpecialLinearGroup.transvection_inv hij a]
    exact H.inv_mem (ha i j hij)
  mul_mem' := by
    intro a b ha hb i j hij
    obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j hn
    exact transvection_mul_mem_of_two_step H i k j hki.symm hkj hij a b
      (ha i k hki.symm) (hb k j hkj)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integralPolynomial_subring_eq_top_of_X_mem
    (S : Subring IntegralPolynomial)
    (hX : (Polynomial.X : IntegralPolynomial) ∈ S) : S = ⊤ := by
  have hall : ∀ p : IntegralPolynomial, p ∈ S := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        exact S.add_mem hp hq
    | monomial n z =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial]
        apply S.mul_mem
        · simp only [eq_intCast, intCast_mem]
        · exact S.pow_mem hX n
  exact top_unique fun p _ => hall p

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem integral_transvection_mem_of_one_and_X
    (H : Subgroup IntegralSpecialLinearGroup)
    (hone : ∀ (i j : Index) (h : i ≠ j),
      Matrix.SpecialLinearGroup.transvection h (1 : IntegralPolynomial) ∈ H)
    (hX : ∀ (i j : Index) (h : i ≠ j),
      Matrix.SpecialLinearGroup.transvection h Polynomial.X ∈ H)
    (i j : Index) (hij : i ≠ j) (p : IntegralPolynomial) :
    Matrix.SpecialLinearGroup.transvection hij p ∈ H := by
  let S := transvectionCoefficientSubring 4 (by decide) H hone
  have hSX : (Polynomial.X : IntegralPolynomial) ∈ S := hX
  have hS : S = ⊤ := integralPolynomial_subring_eq_top_of_X_mem S hSX
  have hp : p ∈ S := by simp only [hS, Subring.mem_top]
  exact hp i j hij

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def integralElementarySubgroup : Subgroup IntegralSpecialLinearGroup :=
  Subgroup.closure
    {g | ∃ (i j : Index) (h : i ≠ j) (p : IntegralPolynomial),
      g = Matrix.SpecialLinearGroup.transvection h p}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integral_transvection_mem_elementary_commutator
    (i j : Index) (hij : i ≠ j) (a : IntegralPolynomial) :
    Matrix.SpecialLinearGroup.transvection hij a ∈
      ⁅integralElementarySubgroup, integralElementarySubgroup⁆ := by
  obtain ⟨k, hki, hkj⟩ :=
    Fin.exists_ne_and_ne_of_two_lt i j (by decide)
  have hik : i ≠ k := hki.symm
  have hleft : Matrix.SpecialLinearGroup.transvection hik a ∈
      integralElementarySubgroup :=
    Subgroup.subset_closure ⟨i, k, hik, a, rfl⟩
  have hright : Matrix.SpecialLinearGroup.transvection hkj
      (1 : IntegralPolynomial) ∈ integralElementarySubgroup :=
    Subgroup.subset_closure ⟨k, j, hkj, 1, rfl⟩
  have hc := Subgroup.commutator_mem_commutator hleft hright
  rw [commutatorElement_def,
    specialLinear_transvection_commutator i k j hik hkj hij a 1] at hc
  simpa only [mul_one] using hc

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integralElementarySubgroup_isPerfect :
    Group.IsPerfect integralElementarySubgroup := by
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm
  · exact Subgroup.commutator_le_self _
  · change Subgroup.closure _ ≤ _
    rw [Subgroup.closure_le]
    rintro _ ⟨i, j, hij, a, rfl⟩
    exact integral_transvection_mem_elementary_commutator i j hij a

end

section

open ConnesRigidity

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def integralElementaryGroup : CountableDiscreteGroup where
  Carrier := integralElementarySubgroup
  group := inferInstance
  countable := inferInstance

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def SuslinElementaryGeneration : Prop :=
  integralElementarySubgroup = ⊤

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def ErshovJaikinElementaryPropertyT : Prop :=
  HasKazhdanPropertyT integralElementaryGroup

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def integralElementaryGroupEquivIntegralGroup
    (hSuslin : SuslinElementaryGeneration) :
    integralElementaryGroup ≃* integralGroup :=
  (MulEquiv.subgroupCongr hSuslin).trans Subgroup.topEquiv

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integralElementaryGroup_propertyT_iff_integralGroup
    (hSuslin : SuslinElementaryGeneration) :
    ErshovJaikinElementaryPropertyT ↔
      ErshovJaikinUniversalLatticePropertyT :=
  hasKazhdanPropertyT_iff_of_mulEquiv
    integralElementaryGroup integralGroup
    (integralElementaryGroupEquivIntegralGroup hSuslin)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem universalLatticePropertyT_of_elementary
    (hSuslin : SuslinElementaryGeneration)
    (hElementary : ErshovJaikinElementaryPropertyT) :
    ErshovJaikinUniversalLatticePropertyT :=
  (integralElementaryGroup_propertyT_iff_integralGroup hSuslin).mp hElementary

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem integralElementaryGroup_isPerfect :
    Group.IsPerfect integralElementaryGroup :=
  integralElementarySubgroup_isPerfect

end

end

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def suslinEvaluation : IntegralSpecialLinearGroup →* IntegerSpecialLinearGroup :=
  Matrix.SpecialLinearGroup.map (Polynomial.evalRingHom (0 : ℤ))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def suslinConstantSection : IntegerSpecialLinearGroup →* IntegralSpecialLinearGroup :=
  Matrix.SpecialLinearGroup.map (Polynomial.C : ℤ →+* IntegralPolynomial)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem suslinEvaluation_entry
    (g : IntegralSpecialLinearGroup) (i j : Index) :
    suslinEvaluation g i j = (g i j).eval 0 := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem suslinConstantSection_entry
    (g : IntegerSpecialLinearGroup) (i j : Index) :
    suslinConstantSection g i j = Polynomial.C (g i j) := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem suslinEvaluation_constantSection
    (g : IntegerSpecialLinearGroup) :
    suslinEvaluation (suslinConstantSection g) = g := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [suslinEvaluation_entry, suslinConstantSection_entry, eq_intCast,
    Polynomial.eval_intCast, Int.cast_eq]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinEvaluation_surjective :
    Function.Surjective suslinEvaluation :=
  fun g => ⟨suslinConstantSection g, suslinEvaluation_constantSection g⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def integerElementarySubgroup : Subgroup IntegerSpecialLinearGroup :=
  Subgroup.closure
    {g | ∃ (i j : Index) (h : i ≠ j) (a : ℤ),
      g = Matrix.SpecialLinearGroup.transvection h a}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def IntegerElementaryGeneration : Prop :=
  integerElementarySubgroup = ⊤

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def suslinAugmentationKernel : Subgroup IntegralSpecialLinearGroup :=
  suslinEvaluation.ker

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def SuslinRelativeElementaryGeneration : Prop :=
  suslinAugmentationKernel ≤ integralElementarySubgroup

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinEvaluation_map_elementary :
    integralElementarySubgroup.map suslinEvaluation =
      integerElementarySubgroup := by
  change
    (Subgroup.closure
      {g : IntegralSpecialLinearGroup |
        ∃ (i j : Index) (h : i ≠ j) (p : IntegralPolynomial),
          g = Matrix.SpecialLinearGroup.transvection h p}).map
          suslinEvaluation = _
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨i, j, h, p, rfl⟩, rfl⟩
    refine ⟨i, j, h, p.eval 0, ?_⟩
    exact specialLinear_map_transvection_baseChange
      (Polynomial.evalRingHom (0 : ℤ)) h p
  · rintro ⟨i, j, h, a, rfl⟩
    refine ⟨Matrix.SpecialLinearGroup.transvection h
      (Polynomial.C a), ⟨i, j, h, Polynomial.C a, rfl⟩, ?_⟩
    simpa only [suslinEvaluation, eq_intCast, map_intCast, Int.cast_eq] using
      specialLinear_map_transvection_baseChange
        (Polynomial.evalRingHom (0 : ℤ)) h (Polynomial.C a)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinConstantSection_map_elementary_le :
    integerElementarySubgroup.map suslinConstantSection ≤
      integralElementarySubgroup := by
  change
    (Subgroup.closure
      {g : IntegerSpecialLinearGroup |
        ∃ (i j : Index) (h : i ≠ j) (a : ℤ),
          g = Matrix.SpecialLinearGroup.transvection h a}).map
          suslinConstantSection ≤ _
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨i, j, h, a, rfl⟩, rfl⟩
  rw [show suslinConstantSection
      (Matrix.SpecialLinearGroup.transvection h a) =
      Matrix.SpecialLinearGroup.transvection h (Polynomial.C a) from
    specialLinear_map_transvection_baseChange
      (Polynomial.C : ℤ →+* IntegralPolynomial) h a]
  exact Subgroup.subset_closure ⟨i, j, h, Polynomial.C a, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_constant_mul_augmentation
    (g : IntegralSpecialLinearGroup) :
    ∃ (c : IntegerSpecialLinearGroup)
      (k : IntegralSpecialLinearGroup),
      k ∈ suslinAugmentationKernel ∧
        g = suslinConstantSection c * k := by
  refine ⟨suslinEvaluation g,
    (suslinConstantSection (suslinEvaluation g))⁻¹ * g, ?_, ?_⟩
  · change
      suslinEvaluation
        ((suslinConstantSection (suslinEvaluation g))⁻¹ * g) = 1
    simp only [map_mul, map_inv, suslinEvaluation_constantSection, inv_mul_cancel]
  · simp only [mul_inv_cancel_left]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem suslinElementaryGeneration_iff_base_and_relative :
    SuslinElementaryGeneration ↔
      IntegerElementaryGeneration ∧ SuslinRelativeElementaryGeneration := by
  constructor
  · intro hSuslin
    constructor
    · have hmap := congrArg
        (fun H : Subgroup IntegralSpecialLinearGroup =>
          H.map suslinEvaluation) hSuslin
      rw [suslinEvaluation_map_elementary,
        Subgroup.map_top_of_surjective suslinEvaluation
          suslinEvaluation_surjective] at hmap
      exact hmap
    · change suslinAugmentationKernel ≤ integralElementarySubgroup
      rw [show integralElementarySubgroup = ⊤ from hSuslin]
      exact le_top
  · rintro ⟨hbase, hrelative⟩
    apply top_unique
    intro g _
    obtain ⟨c, k, hk, rfl⟩ := suslin_constant_mul_augmentation g
    apply integralElementarySubgroup.mul_mem _ (hrelative hk)
    apply suslinConstantSection_map_elementary_le
    exact ⟨c, by rw [hbase]; trivial, rfl⟩

end

section

open Polynomial

universe u v

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
  [Algebra A B]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def localGlobalElementarySubgroup (R : Type*) [CommRing R] :
    Subgroup (Matrix.SpecialLinearGroup Index R) :=
  Subgroup.closure
    {g | ∃ (i j : Index) (h : i ≠ j) (r : R),
      g = Matrix.SpecialLinearGroup.transvection h r}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem localGlobal_transvection_mem
    {R : Type*} [CommRing R] (i j : Index) (h : i ≠ j) (r : R) :
    Matrix.SpecialLinearGroup.transvection h r ∈
      localGlobalElementarySubgroup R :=
  Subgroup.subset_closure ⟨i, j, h, r, rfl⟩





/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem map_localGlobalElementarySubgroup_le
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (localGlobalElementarySubgroup R).map
        (Matrix.SpecialLinearGroup.map f) ≤
      localGlobalElementarySubgroup S := by
  change
    (Subgroup.closure
      {g : Matrix.SpecialLinearGroup Index R |
        ∃ (i j : Index) (h : i ≠ j) (r : R),
          g = Matrix.SpecialLinearGroup.transvection h r}).map
            (Matrix.SpecialLinearGroup.map f) ≤ _
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨i, j, h, r, rfl⟩, rfl⟩
  rw [specialLinear_map_transvection_baseChange f h r]
  exact localGlobal_transvection_mem i j h (f r)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem localization_comp_commonDenom_mul_X_mem_lifts
    (M : Submonoid A) [IsLocalization M B]
    (p : Polynomial B)
    (hzero : p.coeff 0 ∈ Set.range (algebraMap A B)) :
    p.comp
      (Polynomial.C
        (algebraMap A B
          (IsLocalization.commonDenom M p.support p.coeff)) *
        Polynomial.X) ∈
      Polynomial.lifts (algebraMap A B) := by
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro n
  rw [Polynomial.comp_C_mul_X_coeff]
  by_cases hn : n = 0
  · subst n
    simpa only [pow_zero, mul_one, Set.mem_range] using hzero
  by_cases hs : n ∈ p.support
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    let d : M := IsLocalization.commonDenom M p.support p.coeff
    let a : A := IsLocalization.integerMultiple M p.support p.coeff ⟨n, hs⟩
    refine ⟨a * (d : A) ^ (n - 1), ?_⟩
    have ha : algebraMap A B a =
        algebraMap A B (d : A) * p.coeff n := by
      simpa only [a, d, Submonoid.smul_def, Algebra.smul_def] using
        (IsLocalization.map_integerMultiple M p.support p.coeff ⟨n, hs⟩)
    rw [map_mul, map_pow, ha]
    change
      algebraMap A B (d : A) * p.coeff n *
          algebraMap A B (d : A) ^ (n - 1) =
        p.coeff n * algebraMap A B (d : A) ^ n
    calc
      algebraMap A B (d : A) * p.coeff n *
          algebraMap A B (d : A) ^ (n - 1) =
        p.coeff n *
          (algebraMap A B (d : A) ^ (n - 1) *
            algebraMap A B (d : A)) := by ring
      _ = p.coeff n * algebraMap A B (d : A) ^ n := by
        rw [← pow_succ, Nat.sub_add_cancel hpos]
  · have hz : p.coeff n = 0 := Polynomial.notMem_support_iff.mp hs
    rw [hz, zero_mul]
    exact ⟨0, map_zero _⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_localization_dilated_polynomial_lift
    (M : Submonoid A) [IsLocalization M B]
    (p : Polynomial B) (hp : p.coeff 0 = 0) :
    ∃ (d : M) (q : Polynomial A),
      Polynomial.map (algebraMap A B) q =
        p.comp (Polynomial.C (algebraMap A B (d : A)) * Polynomial.X) := by
  let d : M := IsLocalization.commonDenom M p.support p.coeff
  refine ⟨d, ?_⟩
  apply (Polynomial.mem_lifts _).mp
  apply localization_comp_commonDenom_mul_X_mem_lifts M p
  rw [hp]
  exact ⟨0, map_zero _⟩

end

section

open Polynomial

universe u v

variable {A : Type u} [CommRing A]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def suslinDifferenceDilationRingHom (a : A) :
    Polynomial A →+* Polynomial A :=
  Polynomial.compRingHom (Polynomial.C a * Polynomial.X)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def suslinDifferenceDilation (a : A) :
    Matrix.SpecialLinearGroup Index (Polynomial A) →*
      Matrix.SpecialLinearGroup Index (Polynomial A) :=
  Matrix.SpecialLinearGroup.map (suslinDifferenceDilationRingHom a)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def suslinBivariateShiftRingHom (a : A) :
    Polynomial A →+* Polynomial (Polynomial A) :=
  Polynomial.eval₂RingHom
    ((Polynomial.C : Polynomial A →+* Polynomial (Polynomial A)).comp
      (Polynomial.C : A →+* Polynomial A))
    (Polynomial.C (Polynomial.C a * Polynomial.X) + Polynomial.X)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def suslinBivariateConstantRingHom :
    Polynomial A →+* Polynomial (Polynomial A) := Polynomial.C

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def suslinDifferencePath (a : A)
    (g : Matrix.SpecialLinearGroup Index (Polynomial A)) :
    Matrix.SpecialLinearGroup Index (Polynomial (Polynomial A)) :=
  Matrix.SpecialLinearGroup.map (suslinBivariateShiftRingHom a) g *
    (Matrix.SpecialLinearGroup.map suslinBivariateConstantRingHom
      (suslinDifferenceDilation a g))⁻¹

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinBivariateShift_eval_zero (a : A) :
    (Polynomial.evalRingHom (0 : Polynomial A)).comp
        (suslinBivariateShiftRingHom a) =
      suslinDifferenceDilationRingHom a := by
  apply Polynomial.ringHom_ext
  · intro c
    simp only [suslinBivariateShiftRingHom, map_mul, RingHom.coe_comp, coe_evalRingHom,
      coe_eval₂RingHom, Function.comp_apply, eval₂_C, eval_C, suslinDifferenceDilationRingHom,
      coe_compRingHom, C_comp]
  · simp only [suslinBivariateShiftRingHom, map_mul, RingHom.coe_comp, coe_evalRingHom,
      coe_eval₂RingHom, Function.comp_apply, eval₂_X, eval_add, eval_mul, eval_C, eval_X, add_zero,
      suslinDifferenceDilationRingHom, coe_compRingHom, X_comp]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinDifferencePath_eval_zero (a : A)
    (g : Matrix.SpecialLinearGroup Index (Polynomial A)) :
    Matrix.SpecialLinearGroup.map
        (Polynomial.evalRingHom (0 : Polynomial A))
        (suslinDifferencePath a g) = 1 := by
  rw [suslinDifferencePath, map_mul, map_inv]
  have hshift :
      Matrix.SpecialLinearGroup.map
          (Polynomial.evalRingHom (0 : Polynomial A))
          (Matrix.SpecialLinearGroup.map
            (suslinBivariateShiftRingHom a) g) =
        suslinDifferenceDilation a g := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact RingHom.congr_fun (suslinBivariateShift_eval_zero a) (g i j)
  have hconstant :
      Matrix.SpecialLinearGroup.map
          (Polynomial.evalRingHom (0 : Polynomial A))
          (Matrix.SpecialLinearGroup.map
            suslinBivariateConstantRingHom
            (suslinDifferenceDilation a g)) =
        suslinDifferenceDilation a g := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp only [suslinBivariateConstantRingHom, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply, coe_evalRingHom, Matrix.map_apply, eval_C]
  rw [hshift, hconstant, mul_inv_cancel]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinBivariateShift_eval_mul_X (a b : A) :
    (Polynomial.evalRingHom (Polynomial.C b * Polynomial.X)).comp
        (suslinBivariateShiftRingHom a) =
      suslinDifferenceDilationRingHom (a + b) := by
  apply Polynomial.ringHom_ext
  · intro c
    simp only [suslinBivariateShiftRingHom, map_mul, RingHom.coe_comp, coe_evalRingHom,
      coe_eval₂RingHom, Function.comp_apply, eval₂_C, eval_C, suslinDifferenceDilationRingHom,
      map_add, coe_compRingHom, C_comp]
  · simp only [suslinBivariateShiftRingHom, map_mul, RingHom.coe_comp, coe_evalRingHom,
      coe_eval₂RingHom, Function.comp_apply, eval₂_X, eval_add, eval_mul, eval_C, eval_X,
      suslinDifferenceDilationRingHom, map_add, add_mul, coe_compRingHom, X_comp]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem suslinDifferencePath_eval_mul_X (a b : A)
    (g : Matrix.SpecialLinearGroup Index (Polynomial A)) :
    Matrix.SpecialLinearGroup.map
        (Polynomial.evalRingHom (Polynomial.C b * Polynomial.X))
        (suslinDifferencePath a g) =
      suslinDifferenceDilation (a + b) g *
        (suslinDifferenceDilation a g)⁻¹ := by
  rw [suslinDifferencePath, map_mul, map_inv]
  have hshift :
      Matrix.SpecialLinearGroup.map
          (Polynomial.evalRingHom (Polynomial.C b * Polynomial.X))
          (Matrix.SpecialLinearGroup.map
            (suslinBivariateShiftRingHom a) g) =
        suslinDifferenceDilation (a + b) g := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact RingHom.congr_fun (suslinBivariateShift_eval_mul_X a b) (g i j)
  have hconstant :
      Matrix.SpecialLinearGroup.map
          (Polynomial.evalRingHom (Polynomial.C b * Polynomial.X))
          (Matrix.SpecialLinearGroup.map
            suslinBivariateConstantRingHom
            (suslinDifferenceDilation a g)) =
        suslinDifferenceDilation a g := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp only [suslinBivariateConstantRingHom, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply, coe_evalRingHom, Matrix.map_apply, eval_C]
  rw [hshift, hconstant]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinDifferenceDilationRingHom_baseChange
    {B : Type v} [CommRing B] (f : A →+* B) (a : A) :
    (Polynomial.mapRingHom f).comp
        (suslinDifferenceDilationRingHom a) =
      (suslinDifferenceDilationRingHom (f a)).comp
        (Polynomial.mapRingHom f) := by
  apply Polynomial.ringHom_ext
  · intro c
    simp only [suslinDifferenceDilationRingHom, RingHom.coe_comp, coe_mapRingHom, coe_compRingHom,
      Function.comp_apply, C_comp, map_C]
  · simp only [suslinDifferenceDilationRingHom, RingHom.coe_comp, coe_mapRingHom, coe_compRingHom,
      Function.comp_apply, X_comp, Polynomial.map_mul, map_C, map_X]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem suslinDifferenceDilation_baseChange
    {B : Type v} [CommRing B] (f : A →+* B) (a : A)
    (g : Matrix.SpecialLinearGroup Index (Polynomial A)) :
    Matrix.SpecialLinearGroup.map (Polynomial.mapRingHom f)
        (suslinDifferenceDilation a g) =
      suslinDifferenceDilation (f a)
        (Matrix.SpecialLinearGroup.map (Polynomial.mapRingHom f) g) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  exact RingHom.congr_fun
    (suslinDifferenceDilationRingHom_baseChange f a) (g i j)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinBivariateShiftRingHom_baseChange
    {B : Type v} [CommRing B] (f : A →+* B) (a : A) :
    (Polynomial.mapRingHom (Polynomial.mapRingHom f)).comp
        (suslinBivariateShiftRingHom a) =
      (suslinBivariateShiftRingHom (f a)).comp
        (Polynomial.mapRingHom f) := by
  apply Polynomial.ringHom_ext
  · intro c
    simp only [suslinBivariateShiftRingHom, map_mul, RingHom.coe_comp, coe_mapRingHom,
      coe_eval₂RingHom, Function.comp_apply, eval₂_C, map_C]
  · simp only [suslinBivariateShiftRingHom, map_mul, RingHom.coe_comp, coe_mapRingHom,
      coe_eval₂RingHom, Function.comp_apply, eval₂_X, Polynomial.map_add, Polynomial.map_mul, map_C,
      map_X]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinBivariateConstantRingHom_baseChange
    {B : Type v} [CommRing B] (f : A →+* B) :
    (Polynomial.mapRingHom (Polynomial.mapRingHom f)).comp
        (suslinBivariateConstantRingHom (A := A)) =
      (suslinBivariateConstantRingHom (A := B)).comp
        (Polynomial.mapRingHom f) := by
  apply Polynomial.ringHom_ext
  · intro c
    simp only [suslinBivariateConstantRingHom, RingHom.coe_comp, coe_mapRingHom,
      Function.comp_apply, map_C]
  · simp only [suslinBivariateConstantRingHom, RingHom.coe_comp, coe_mapRingHom,
      Function.comp_apply, map_C, map_X]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem suslinDifferencePath_baseChange
    {B : Type v} [CommRing B] (f : A →+* B) (a : A)
    (g : Matrix.SpecialLinearGroup Index (Polynomial A)) :
    Matrix.SpecialLinearGroup.map
        (Polynomial.mapRingHom (Polynomial.mapRingHom f))
        (suslinDifferencePath a g) =
      suslinDifferencePath (f a)
        (Matrix.SpecialLinearGroup.map (Polynomial.mapRingHom f) g) := by
  rw [suslinDifferencePath, suslinDifferencePath, map_mul, map_inv]
  have hshift :
      Matrix.SpecialLinearGroup.map
          (Polynomial.mapRingHom (Polynomial.mapRingHom f))
          (Matrix.SpecialLinearGroup.map (suslinBivariateShiftRingHom a) g) =
        Matrix.SpecialLinearGroup.map (suslinBivariateShiftRingHom (f a))
          (Matrix.SpecialLinearGroup.map (Polynomial.mapRingHom f) g) := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact RingHom.congr_fun
      (suslinBivariateShiftRingHom_baseChange f a) (g i j)
  have hconstant :
      Matrix.SpecialLinearGroup.map
          (Polynomial.mapRingHom (Polynomial.mapRingHom f))
          (Matrix.SpecialLinearGroup.map suslinBivariateConstantRingHom
            (suslinDifferenceDilation a g)) =
        Matrix.SpecialLinearGroup.map suslinBivariateConstantRingHom
          (suslinDifferenceDilation (f a)
            (Matrix.SpecialLinearGroup.map (Polynomial.mapRingHom f) g)) := by
    rw [← suslinDifferenceDilation_baseChange f a g]
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact RingHom.congr_fun
      (suslinBivariateConstantRingHom_baseChange f)
      (suslinDifferenceDilation a g i j)
  rw [hshift, hconstant]

end

section

open Polynomial

universe u v

variable {A : Type u} [CommRing A]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinDifferenceDilation_mem_elementary
    (a : A) {g : Matrix.SpecialLinearGroup Index (Polynomial A)}
    (hg : g ∈ localGlobalElementarySubgroup (Polynomial A)) :
    suslinDifferenceDilation a g ∈
      localGlobalElementarySubgroup (Polynomial A) := by
  exact map_localGlobalElementarySubgroup_le
    (suslinDifferenceDilationRingHom a)
    ⟨g, hg, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinBivariateShift_mem_elementary
    (a : A) {g : Matrix.SpecialLinearGroup Index (Polynomial A)}
    (hg : g ∈ localGlobalElementarySubgroup (Polynomial A)) :
    Matrix.SpecialLinearGroup.map (suslinBivariateShiftRingHom a) g ∈
      localGlobalElementarySubgroup (Polynomial (Polynomial A)) := by
  exact map_localGlobalElementarySubgroup_le
    (suslinBivariateShiftRingHom a)
    ⟨g, hg, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinBivariateConstant_mem_elementary
    {g : Matrix.SpecialLinearGroup Index (Polynomial A)}
    (hg : g ∈ localGlobalElementarySubgroup (Polynomial A)) :
    Matrix.SpecialLinearGroup.map suslinBivariateConstantRingHom g ∈
      localGlobalElementarySubgroup (Polynomial (Polynomial A)) := by
  exact map_localGlobalElementarySubgroup_le
    (suslinBivariateConstantRingHom (A := A))
    ⟨g, hg, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinDifferencePath_mem_elementary
    (a : A) {g : Matrix.SpecialLinearGroup Index (Polynomial A)}
    (hg : g ∈ localGlobalElementarySubgroup (Polynomial A)) :
    suslinDifferencePath a g ∈
      localGlobalElementarySubgroup (Polynomial (Polynomial A)) := by
  apply (localGlobalElementarySubgroup (Polynomial (Polynomial A))).mul_mem
    (suslinBivariateShift_mem_elementary a hg)
  apply (localGlobalElementarySubgroup (Polynomial (Polynomial A))).inv_mem
  exact suslinBivariateConstant_mem_elementary
    (suslinDifferenceDilation_mem_elementary a hg)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem suslinDifferencePath_relative_elementary_of_baseChange
    {B : Type v} [CommRing B] (f : A →+* B) (a : A)
    (g : Matrix.SpecialLinearGroup Index (Polynomial A))
    (hg : Matrix.SpecialLinearGroup.map (Polynomial.mapRingHom f) g ∈
      localGlobalElementarySubgroup (Polynomial B)) :
    Matrix.SpecialLinearGroup.map
        (Polynomial.mapRingHom (Polynomial.mapRingHom f))
        (suslinDifferencePath a g) ∈
          localGlobalElementarySubgroup (Polynomial (Polynomial B)) ∧
      Matrix.SpecialLinearGroup.map
        (Polynomial.evalRingHom (0 : Polynomial B))
        (Matrix.SpecialLinearGroup.map
          (Polynomial.mapRingHom (Polynomial.mapRingHom f))
          (suslinDifferencePath a g)) = 1 := by
  rw [suslinDifferencePath_baseChange]
  exact ⟨suslinDifferencePath_mem_elementary (f a) hg,
    suslinDifferencePath_eval_zero (f a) _⟩

end

section

universe u v w

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def suslinElementarySubgroup (ι : Type u) (A : Type v)
    [Fintype ι] [DecidableEq ι] [CommRing A] :
    Subgroup (Matrix.SpecialLinearGroup ι A) :=
  Subgroup.closure
    {g | ∃ (i j : ι) (h : i ≠ j) (a : A),
      g = Matrix.SpecialLinearGroup.transvection h a}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_transvection_mem
    {ι : Type u} {A : Type v}
    [Fintype ι] [DecidableEq ι] [CommRing A]
    (i j : ι) (h : i ≠ j) (a : A) :
    Matrix.SpecialLinearGroup.transvection h a ∈
      suslinElementarySubgroup ι A :=
  Subgroup.subset_closure ⟨i, j, h, a, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem suslin_transvection_conj_noncomposable
    {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A]
    {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) (a b : A) :
    Matrix.SpecialLinearGroup.transvection hij a *
      Matrix.SpecialLinearGroup.transvection hkl b *
      (Matrix.SpecialLinearGroup.transvection hij a)⁻¹ =
      Matrix.SpecialLinearGroup.transvection hkl b := by
  rw [Matrix.SpecialLinearGroup.transvection_inv]
  apply Subtype.ext
  change
    (1 + Matrix.single i j a) * (1 + Matrix.single k l b) *
      (1 + Matrix.single i j (-a)) =
      1 + Matrix.single k l b
  rw [← Matrix.single_neg]
  have hxx : Matrix.single i j a * Matrix.single i j a = 0 :=
    Matrix.single_mul_single_of_ne (c := a) i j i hij.symm a
  have hxy : Matrix.single i j a * Matrix.single k l b = 0 :=
    Matrix.single_mul_single_of_ne (c := a) i j k hjk b
  have hyx : Matrix.single k l b * Matrix.single i j a = 0 :=
    Matrix.single_mul_single_of_ne (c := b) k l i hli a
  noncomm_ring [hxx, hxy, hyx]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem suslin_transvection_conj_adjacent
    {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A]
    (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : A) :
    Matrix.SpecialLinearGroup.transvection hij a *
      Matrix.SpecialLinearGroup.transvection hjk b *
      (Matrix.SpecialLinearGroup.transvection hij a)⁻¹ =
      Matrix.SpecialLinearGroup.transvection hik (a * b) *
      Matrix.SpecialLinearGroup.transvection hjk b := by
  calc
    _ =
        (Matrix.SpecialLinearGroup.transvection hij a *
          Matrix.SpecialLinearGroup.transvection hjk b *
          (Matrix.SpecialLinearGroup.transvection hij a)⁻¹ *
          (Matrix.SpecialLinearGroup.transvection hjk b)⁻¹) *
          Matrix.SpecialLinearGroup.transvection hjk b := by
            simp only [mul_assoc, inv_mul_cancel, mul_one]
    _ = _ := by
      rw [specialLinear_transvection_commutator i j k hij hjk hik a b]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem suslin_transvection_conj_reverse_adjacent
    {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A]
    (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : A) :
    Matrix.SpecialLinearGroup.transvection hij a *
      Matrix.SpecialLinearGroup.transvection hik.symm b *
      (Matrix.SpecialLinearGroup.transvection hij a)⁻¹ =
      Matrix.SpecialLinearGroup.transvection hjk.symm (-(b * a)) *
      Matrix.SpecialLinearGroup.transvection hik.symm b := by
  calc
    _ =
        (Matrix.SpecialLinearGroup.transvection hik.symm b *
          Matrix.SpecialLinearGroup.transvection hij a *
          (Matrix.SpecialLinearGroup.transvection hik.symm b)⁻¹ *
          (Matrix.SpecialLinearGroup.transvection hij a)⁻¹)⁻¹ *
          Matrix.SpecialLinearGroup.transvection hik.symm b := by
            simp only [mul_assoc, mul_inv_rev, inv_inv, inv_mul_cancel, mul_one]
    _ =
        (Matrix.SpecialLinearGroup.transvection hjk.symm (b * a))⁻¹ *
          Matrix.SpecialLinearGroup.transvection hik.symm b := by
            rw [specialLinear_transvection_commutator
              k i j hik.symm hij hjk.symm b a]
    _ = _ := by
      rw [Matrix.SpecialLinearGroup.transvection_inv]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_transvection_conj_opposite_factor
    {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A]
    (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a u v : A) :
    Matrix.SpecialLinearGroup.transvection hij a *
      Matrix.SpecialLinearGroup.transvection hij.symm (u * v) *
      (Matrix.SpecialLinearGroup.transvection hij a)⁻¹ =
      (Matrix.SpecialLinearGroup.transvection hik (a * u) *
          Matrix.SpecialLinearGroup.transvection hjk u) *
        (Matrix.SpecialLinearGroup.transvection hjk.symm (-(v * a)) *
          Matrix.SpecialLinearGroup.transvection hik.symm v) *
        (Matrix.SpecialLinearGroup.transvection hik (a * u) *
          Matrix.SpecialLinearGroup.transvection hjk u)⁻¹ *
        (Matrix.SpecialLinearGroup.transvection hjk.symm (-(v * a)) *
          Matrix.SpecialLinearGroup.transvection hik.symm v)⁻¹ := by
  have hopposite := specialLinear_transvection_commutator
    j k i hjk hik.symm hij.symm u v
  have hadjacent := suslin_transvection_conj_adjacent
    i j k hij hjk hik a u
  have hreverse := suslin_transvection_conj_reverse_adjacent
    i j k hij hjk hik a v
  calc
    _ =
        (Matrix.SpecialLinearGroup.transvection hij a *
          Matrix.SpecialLinearGroup.transvection hjk u *
          (Matrix.SpecialLinearGroup.transvection hij a)⁻¹) *
        (Matrix.SpecialLinearGroup.transvection hij a *
          Matrix.SpecialLinearGroup.transvection hik.symm v *
          (Matrix.SpecialLinearGroup.transvection hij a)⁻¹) *
        (Matrix.SpecialLinearGroup.transvection hij a *
          Matrix.SpecialLinearGroup.transvection hjk u *
          (Matrix.SpecialLinearGroup.transvection hij a)⁻¹)⁻¹ *
        (Matrix.SpecialLinearGroup.transvection hij a *
          Matrix.SpecialLinearGroup.transvection hik.symm v *
          (Matrix.SpecialLinearGroup.transvection hij a)⁻¹)⁻¹ := by
            rw [← hopposite]
            simp only [mul_assoc, inv_mul_cancel_left, mul_inv_rev, inv_inv]
    _ = _ := by rw [hadjacent, hreverse]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem suslin_specialLinear_map_transvection
    {ι : Type u} {A : Type v} {B : Type w}
    [Fintype ι] [DecidableEq ι] [CommRing A] [CommRing B]
    (f : A →+* B) {i j : ι} (hij : i ≠ j) (a : A) :
    Matrix.SpecialLinearGroup.map f
        (Matrix.SpecialLinearGroup.transvection hij a) =
      Matrix.SpecialLinearGroup.transvection hij (f a) :=
  specialLinear_map_transvection_baseChange f hij a

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_suslin_opposite_conjugate_elementary_lift
    {ι : Type u} {A : Type v} {B : Type w}
    [Fintype ι] [DecidableEq ι] [CommRing A] [CommRing B]
    (f : A →+* B)
    (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a : B) (c d p : A) (ha : a * f d = f c) :
    ∃ g : Matrix.SpecialLinearGroup ι A,
      g ∈ suslinElementarySubgroup ι A ∧
        Matrix.SpecialLinearGroup.map f g =
          Matrix.SpecialLinearGroup.transvection hij a *
            Matrix.SpecialLinearGroup.transvection hij.symm
              (f (d * d * p)) *
            (Matrix.SpecialLinearGroup.transvection hij a)⁻¹ := by
  let L : Matrix.SpecialLinearGroup ι A :=
    Matrix.SpecialLinearGroup.transvection hik (c * p) *
      Matrix.SpecialLinearGroup.transvection hjk (d * p)
  let R : Matrix.SpecialLinearGroup ι A :=
    Matrix.SpecialLinearGroup.transvection hjk.symm (-c) *
      Matrix.SpecialLinearGroup.transvection hik.symm d
  have hL : L ∈ suslinElementarySubgroup ι A :=
    (suslinElementarySubgroup ι A).mul_mem
      (suslin_transvection_mem i k hik (c * p))
      (suslin_transvection_mem j k hjk (d * p))
  have hR : R ∈ suslinElementarySubgroup ι A :=
    (suslinElementarySubgroup ι A).mul_mem
      (suslin_transvection_mem k j hjk.symm (-c))
      (suslin_transvection_mem k i hik.symm d)
  refine ⟨L * R * L⁻¹ * R⁻¹,
    (suslinElementarySubgroup ι A).mul_mem
      ((suslinElementarySubgroup ι A).mul_mem
        ((suslinElementarySubgroup ι A).mul_mem hL hR)
        ((suslinElementarySubgroup ι A).inv_mem hL))
      ((suslinElementarySubgroup ι A).inv_mem hR), ?_⟩
  have hprod : f (d * d * p) = f (d * p) * f d := by
    simp only [map_mul]
    ring
  have hcoeff : a * f (d * p) = f (c * p) := by
    simp only [map_mul]
    calc
      a * (f d * f p) = (a * f d) * f p := by ring
      _ = f c * f p := by rw [ha]
  have hreverse : f d * a = f c := by
    rw [mul_comm]
    exact ha
  have hcoeff' : a * (f d * f p) = f c * f p := by
    rw [← mul_assoc, ha]
  rw [hprod, suslin_transvection_conj_opposite_factor
    i j k hij hjk hik a (f (d * p)) (f d)]
  simp only [mul_inv_rev, map_mul, suslin_specialLinear_map_transvection, map_neg, map_inv, hcoeff',
    hreverse, L, R]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_localization_polynomial_common_denominator
    {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    [Algebra A B] (M : Submonoid A) [IsLocalization M B]
    (p : Polynomial B) :
    ∃ (d : M) (q : Polynomial A),
      p * Polynomial.C (algebraMap A B (d : A)) =
        Polynomial.map (algebraMap A B) q := by
  let d : M := IsLocalization.commonDenom M p.support p.coeff
  have h_lifts :
      Polynomial.C (algebraMap A B (d : A)) * p ∈
        Polynomial.lifts (algebraMap A B) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_C_mul]
    by_cases hn : n ∈ p.support
    · let c : A := IsLocalization.integerMultiple M p.support p.coeff ⟨n, hn⟩
      refine ⟨c, ?_⟩
      simpa only [c, d, Submonoid.smul_def, Algebra.smul_def] using
        (IsLocalization.map_integerMultiple M p.support p.coeff ⟨n, hn⟩)
    · rw [Polynomial.notMem_support_iff.mp hn, mul_zero]
      exact ⟨0, map_zero _⟩
  obtain ⟨q, hq⟩ := (Polynomial.mem_lifts _).mp h_lifts
  refine ⟨d, q, ?_⟩
  rw [mul_comm]
  exact hq.symm

end

section

open Polynomial

universe u v w

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
  [Algebra A B]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev SuslinPolynomialSL (R : Type*) [CommRing R] :=
  Matrix.SpecialLinearGroup Index (Polynomial R)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def suslinDilation (R : Type*) [CommRing R] (a : R) :
    SuslinPolynomialSL R →* SuslinPolynomialSL R :=
  Matrix.SpecialLinearGroup.map
    (Polynomial.compRingHom (Polynomial.C a * Polynomial.X))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def suslinPolynomialBaseChange :
    SuslinPolynomialSL A →* SuslinPolynomialSL B :=
  Matrix.SpecialLinearGroup.map
    (Polynomial.mapRingHom (algebraMap A B))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinDilation_mul (a b : A) (g : SuslinPolynomialSL A) :
    suslinDilation A b (suslinDilation A a g) =
      suslinDilation A (a * b) g := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change
    ((g i j).comp (Polynomial.C a * Polynomial.X)).comp
      (Polynomial.C b * Polynomial.X) =
      (g i j).comp (Polynomial.C (a * b) * Polynomial.X)
  rw [Polynomial.comp_assoc]
  simp only [mul_comp, C_comp, X_comp, C_mul, mul_assoc]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem suslinPolynomialBaseChange_dilation (a : A)
    (g : SuslinPolynomialSL A) :
    suslinPolynomialBaseChange (suslinDilation A a g) =
      suslinDilation B (algebraMap A B a)
        (suslinPolynomialBaseChange g) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change
    Polynomial.map (algebraMap A B)
      ((g i j).comp (Polynomial.C a * Polynomial.X)) =
      (Polynomial.map (algebraMap A B) (g i j)).comp
        (Polynomial.C (algebraMap A B a) * Polynomial.X)
  rw [Polynomial.map_comp]
  simp only [Polynomial.map_mul, map_C, map_X]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinDilation_elementary_mem (a : A)
    {g : SuslinPolynomialSL A}
    (hg : g ∈ localGlobalElementarySubgroup (Polynomial A)) :
    suslinDilation A a g ∈
      localGlobalElementarySubgroup (Polynomial A) := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
      obtain ⟨i, j, h, p, rfl⟩ := hg
      rw [show suslinDilation A a
          (Matrix.SpecialLinearGroup.transvection h p) =
          Matrix.SpecialLinearGroup.transvection h
            (p.comp (Polynomial.C a * Polynomial.X)) from
        by simp only [suslinDilation, suslin_specialLinear_map_transvection, coe_compRingHom_apply]]
      exact localGlobal_transvection_mem i j h
        (p.comp (Polynomial.C a * Polynomial.X))
  | one =>
      simp only [map_one, one_mem]
  | mul x y hx hy ihx ihy =>
      rw [map_mul]
      exact (localGlobalElementarySubgroup (Polynomial A)).mul_mem ihx ihy
  | inv x hx ih =>
      rw [map_inv]
      exact (localGlobalElementarySubgroup (Polynomial A)).inv_mem ih

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def suslinEventuallyElementaryLift (M : Submonoid A) :
    Set (SuslinPolynomialSL B) :=
  {g | ∃ (d : M) (q : SuslinPolynomialSL A),
    q ∈ localGlobalElementarySubgroup (Polynomial A) ∧
      suslinPolynomialBaseChange q =
        suslinDilation B (algebraMap A B (d : A)) g}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem suslinEventuallyElementaryLift_one (M : Submonoid A) :
    (1 : SuslinPolynomialSL B) ∈
      suslinEventuallyElementaryLift (A := A) (B := B) M := by
  exact ⟨1, 1, (localGlobalElementarySubgroup (Polynomial A)).one_mem,
    by simp only [map_one, suslinDilation, OneMemClass.coe_one, one_mul]⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem suslinEventuallyElementaryLift_inv (M : Submonoid A)
    {g : SuslinPolynomialSL B}
    (hg : g ∈ suslinEventuallyElementaryLift (A := A) (B := B) M) :
    g⁻¹ ∈ suslinEventuallyElementaryLift (A := A) (B := B) M := by
  obtain ⟨d, q, hq, heq⟩ := hg
  refine ⟨d, q⁻¹,
    (localGlobalElementarySubgroup (Polynomial A)).inv_mem hq, ?_⟩
  simpa only [map_inv, inv_inj] using congrArg Inv.inv heq

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem suslinEventuallyElementaryLift_mul (M : Submonoid A)
    {g h : SuslinPolynomialSL B}
    (hg : g ∈ suslinEventuallyElementaryLift (A := A) (B := B) M)
    (hh : h ∈ suslinEventuallyElementaryLift (A := A) (B := B) M) :
    g * h ∈ suslinEventuallyElementaryLift (A := A) (B := B) M := by
  obtain ⟨d, q, hq, hqeq⟩ := hg
  obtain ⟨e, r, hr, hreq⟩ := hh
  refine ⟨d * e,
    suslinDilation A (e : A) q * suslinDilation A (d : A) r,
    (localGlobalElementarySubgroup (Polynomial A)).mul_mem
      (suslinDilation_elementary_mem (e : A) hq)
      (suslinDilation_elementary_mem (d : A) hr), ?_⟩
  rw [map_mul, suslinPolynomialBaseChange_dilation,
    suslinPolynomialBaseChange_dilation, hqeq, hreq,
    suslinDilation_mul, suslinDilation_mul]
  rw [show (d * e : M).val = (d : A) * (e : A) by rfl,
    map_mul]
  rw [mul_comm (algebraMap A B (e : A))]
  rw [← map_mul]
  rw [map_mul]
  simp only [map_mul]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def suslinEventuallyElementarySubgroup (M : Submonoid A) :
    Subgroup (SuslinPolynomialSL B) where
  carrier := suslinEventuallyElementaryLift (A := A) (B := B) M
  one_mem' := suslinEventuallyElementaryLift_one M
  mul_mem' := suslinEventuallyElementaryLift_mul M
  inv_mem' := suslinEventuallyElementaryLift_inv M

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_eventual_of_dilation
    (M : Submonoid A) (d : M) (g : SuslinPolynomialSL B)
    (hg : suslinDilation B (algebraMap A B (d : A)) g ∈
      suslinEventuallyElementarySubgroup (A := A) (B := B) M) :
    g ∈ suslinEventuallyElementarySubgroup (A := A) (B := B) M := by
  obtain ⟨e, q, hq, hqe⟩ := hg
  refine ⟨d * e, q, hq, ?_⟩
  rw [hqe, suslinDilation_mul]
  change
    suslinDilation B
      (algebraMap A B (d : A) * algebraMap A B (e : A)) g =
      suslinDilation B (algebraMap A B ((d : A) * (e : A))) g
  rw [map_mul]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_polynomial_conjugate_opposite_integral_mem_eventual
    (M : Submonoid A) [IsLocalization M B]
    (i j : Index) (hij : i ≠ j)
    (a : Polynomial B) (p : Polynomial A) :
    Matrix.SpecialLinearGroup.transvection hij a *
        Matrix.SpecialLinearGroup.transvection hij.symm
          (Polynomial.map (algebraMap A B) (Polynomial.X * p)) *
        (Matrix.SpecialLinearGroup.transvection hij a)⁻¹ ∈
      suslinEventuallyElementarySubgroup (A := A) (B := B) M := by
  obtain ⟨d, c, hc⟩ :=
    exists_localization_polynomial_common_denominator M a
  let D : A := (d : A) * (d : A)
  let σ : Polynomial B :=
    Polynomial.C (algebraMap A B D) * Polynomial.X
  let τ : Polynomial A := Polynomial.C D * Polynomial.X
  let a' : Polynomial B := a.comp σ
  let c' : Polynomial A := c.comp τ
  let r : Polynomial A := Polynomial.X * p.comp τ
  have hdenom :
      a' * (Polynomial.mapRingHom (algebraMap A B))
          (Polynomial.C (d : A)) =
        (Polynomial.mapRingHom (algebraMap A B)) c' := by
    have hcomp := congrArg (fun z : Polynomial B => z.comp σ) hc
    simpa [a', c', σ, τ, Polynomial.mul_comp, Polynomial.map_comp]
      using hcomp
  obtain ⟨k, hki, hkj⟩ :=
    Fin.exists_ne_and_ne_of_two_lt i j (by decide : 2 < 4)
  obtain ⟨g, hg, hmap⟩ :=
    exists_suslin_opposite_conjugate_elementary_lift
      (Polynomial.mapRingHom (algebraMap A B))
      i j k hij hkj.symm hki.symm a' c' (Polynomial.C (d : A)) r hdenom
  refine ⟨d * d, g, hg, ?_⟩
  change
    Matrix.SpecialLinearGroup.map
        (Polynomial.mapRingHom (algebraMap A B)) g =
      suslinDilation B (algebraMap A B D)
        (Matrix.SpecialLinearGroup.transvection hij a *
          Matrix.SpecialLinearGroup.transvection hij.symm
            (Polynomial.map (algebraMap A B) (Polynomial.X * p)) *
          (Matrix.SpecialLinearGroup.transvection hij a)⁻¹)
  rw [hmap]
  simp only [suslinDilation, map_mul, map_inv,
    specialLinear_map_transvection_baseChange]
  congr 2
  apply congrArg (Matrix.SpecialLinearGroup.transvection hij.symm)
  dsimp [r, τ, D]
  simp [Polynomial.map_comp, Polynomial.mul_comp,
    Polynomial.C_mul, mul_assoc]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_polynomial_conjugate_opposite_mem_eventual
    (M : Submonoid A) [IsLocalization M B]
    (i j : Index) (hij : i ≠ j)
    (a p : Polynomial B) (hp : p.coeff 0 = 0) :
    Matrix.SpecialLinearGroup.transvection hij a *
        Matrix.SpecialLinearGroup.transvection hij.symm p *
        (Matrix.SpecialLinearGroup.transvection hij a)⁻¹ ∈
      suslinEventuallyElementarySubgroup (A := A) (B := B) M := by
  obtain ⟨d, q, hq⟩ := exists_localization_dilated_polynomial_lift M p hp
  have hzero : algebraMap A B (q.coeff 0) = 0 := by
    have hz := congrArg (fun r : Polynomial B => r.coeff 0) hq
    simpa only [coeff_map, comp_C_mul_X_coeff, hp, pow_zero, mul_one] using hz
  have hremove :
      Polynomial.map (algebraMap A B) (Polynomial.X * q.divX) =
        Polynomial.map (algebraMap A B) q := by
    calc
      Polynomial.map (algebraMap A B) (Polynomial.X * q.divX) =
          Polynomial.map (algebraMap A B)
            (Polynomial.X * q.divX + Polynomial.C (q.coeff 0)) := by
              simp only [Polynomial.map_add, Polynomial.map_C, hzero,
                Polynomial.C_0, add_zero]
      _ = Polynomial.map (algebraMap A B) q := by
            rw [Polynomial.X_mul_divX_add]
  apply suslin_eventual_of_dilation M d
  have htarget :=
    suslin_polynomial_conjugate_opposite_integral_mem_eventual
      M i j hij
      (a.comp (Polynomial.C (algebraMap A B (d : A)) * Polynomial.X))
      q.divX
  rw [hremove, hq] at htarget
  simpa only [suslinDilation, map_mul, suslin_specialLinear_map_transvection, coe_compRingHom,
    map_inv] using htarget

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem suslin_polynomial_relative_z_mem_eventual
    (M : Submonoid A) [IsLocalization M B]
    (i j : Index) (hij : i ≠ j)
    (a p : Polynomial B) (hp : p.coeff 0 = 0) :
    Matrix.SpecialLinearGroup.transvection hij.symm a *
        Matrix.SpecialLinearGroup.transvection hij p *
        (Matrix.SpecialLinearGroup.transvection hij.symm a)⁻¹ ∈
      suslinEventuallyElementarySubgroup (A := A) (B := B) M := by
  exact suslin_polynomial_conjugate_opposite_mem_eventual
    M j i hij.symm a p hp

end

section

open Polynomial

universe u

variable {A : Type u} [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def quotientCoefficientMap (f : Polynomial A) :
    A →+* Polynomial A ⧸ Ideal.span ({f} : Set (Polynomial A)) :=
  (Ideal.Quotient.mk (Ideal.span ({f} : Set (Polynomial A)))).comp
    Polynomial.C

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quotient_uniformizer_isUnit_of_relation
    (π : A) (f q : Polynomial A)
    (hf : f = 1 + Polynomial.C π * q) :
    IsUnit (quotientCoefficientMap f π) := by
  let ρ := Ideal.Quotient.mk (Ideal.span ({f} : Set (Polynomial A)))
  have hfzero : ρ f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton_self f)
  have hrelation :
      (1 : Polynomial A ⧸ Ideal.span ({f} : Set (Polynomial A))) +
        quotientCoefficientMap f π * ρ q = 0 := by
    calc
      (1 : Polynomial A ⧸ Ideal.span ({f} : Set (Polynomial A))) +
          quotientCoefficientMap f π * ρ q =
            ρ (1 + Polynomial.C π * q) := by
              simp only [quotientCoefficientMap, RingHom.coe_comp, Function.comp_apply, map_add,
                map_one, map_mul, ρ]
      _ = ρ f := (congrArg ρ hf).symm
      _ = 0 := hfzero
  refine isUnit_iff_exists_inv'.mpr ⟨-(ρ q), ?_⟩
  linear_combination -hrelation

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quotient_nonzero_coefficient_isUnit
    {π : A} (hπ : Irreducible π)
    (f q : Polynomial A)
    (hf : f = 1 + Polynomial.C π * q)
    {a : A} (ha : a ≠ 0) :
    IsUnit (quotientCoefficientMap f a) := by
  obtain ⟨n, u, rfl⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  rw [map_mul, map_pow]
  exact (u.isUnit.map (quotientCoefficientMap f)).mul
    ((quotient_uniformizer_isUnit_of_relation π f q hf).pow n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def quotientFractionLift
    {π : A} (hπ : Irreducible π)
    (f q : Polynomial A)
    (hf : f = 1 + Polynomial.C π * q) :
    FractionRing A →+*
      Polynomial A ⧸ Ideal.span ({f} : Set (Polynomial A)) :=
  IsLocalization.lift (S := FractionRing A)
    (fun a : nonZeroDivisors A =>
      quotient_nonzero_coefficient_isUnit hπ f q hf
        (nonZeroDivisors.ne_zero a.property))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem quotientFractionLift_algebraMap
    {π : A} (hπ : Irreducible π)
    (f q : Polynomial A)
    (hf : f = 1 + Polynomial.C π * q) (a : A) :
    quotientFractionLift hπ f q hf ((algebraMap A (FractionRing A)) a) =
      quotientCoefficientMap f a := by
  exact IsLocalization.lift_eq _ a

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mapped_polynomial_eval₂_zero
    {K : Type*} [Field K] [Algebra A K]
    (f : Polynomial A)
    [Algebra K (Polynomial A ⧸ Ideal.span ({f} : Set (Polynomial A)))]
    [IsScalarTower A K
      (Polynomial A ⧸ Ideal.span ({f} : Set (Polynomial A)))] :
    (f.map (algebraMap A K)).eval₂
      (algebraMap K
        (Polynomial A ⧸ Ideal.span ({f} : Set (Polynomial A))))
      ((Ideal.Quotient.mk
        (Ideal.span ({f} : Set (Polynomial A)))) Polynomial.X) = 0 := by
  rw [Polynomial.eval₂_map]
  rw [← IsScalarTower.algebraMap_eq A K
    (Polynomial A ⧸ Ideal.span ({f} : Set (Polynomial A)))]
  exact AdjoinRoot.eval₂_root f

omit [IsDiscreteValuationRing A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mapped_polynomial_eval₂_zero_ofId
    (f : Polynomial A) [Algebra (FractionRing A)
      (Polynomial A ⧸ Ideal.span ({f} : Set (Polynomial A)))]
    [IsScalarTower A (FractionRing A)
      (Polynomial A ⧸ Ideal.span ({f} : Set (Polynomial A)))] :
    Polynomial.eval₂
        (Algebra.ofId (FractionRing A)
          (Polynomial A ⧸ Ideal.span ({f} : Set (Polynomial A))))
        ((Ideal.Quotient.mk
          (Ideal.span ({f} : Set (Polynomial A)))) Polynomial.X)
        (f.map (algebraMap A (FractionRing A))) = 0 := by
  change (f.map (algebraMap A (FractionRing A))).eval₂
    (algebraMap (FractionRing A)
      (Polynomial A ⧸ Ideal.span ({f} : Set (Polynomial A))))
    ((Ideal.Quotient.mk
      (Ideal.span ({f} : Set (Polynomial A)))) Polynomial.X) = 0
  exact mapped_polynomial_eval₂_zero f

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[reducible]
private def quotientFractionAlgebra
    {π : A} (hπ : Irreducible π)
    (f q : Polynomial A) (hf : f = 1 + Polynomial.C π * q) :
    Algebra (FractionRing A)
      (Polynomial A ⧸ Ideal.span ({f} : Set (Polynomial A))) :=
  (quotientFractionLift hπ f q hf).toAlgebra

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quotientFractionAlgebra_tower
    {π : A} (hπ : Irreducible π)
    (f q : Polynomial A) (hf : f = 1 + Polynomial.C π * q) :
    letI := quotientFractionAlgebra hπ f q hf
    IsScalarTower A (FractionRing A)
      (Polynomial A ⧸ Ideal.span ({f} : Set (Polynomial A))) := by
  let := quotientFractionAlgebra hπ f q hf
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change quotientCoefficientMap f a =
    quotientFractionLift hπ f q hf
      ((algebraMap A (FractionRing A)) a)
  exact (quotientFractionLift_algebraMap hπ f q hf a).symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def dvrPolynomialQuotientFractionSurjection
    {π : A} (hπ : Irreducible π)
    (f q : Polynomial A) (hf : f = 1 + Polynomial.C π * q) :
    AdjoinRoot (f.map (algebraMap A (FractionRing A))) →+*
      (Polynomial A ⧸ Ideal.span ({f} : Set (Polynomial A))) := by
  let := quotientFractionAlgebra hπ f q hf
  let : IsScalarTower A (FractionRing A)
      (Polynomial A ⧸ Ideal.span ({f} : Set (Polynomial A))) :=
    quotientFractionAlgebra_tower hπ f q hf
  exact (AdjoinRoot.liftAlgHom
    (f.map (algebraMap A (FractionRing A)))
    (Algebra.ofId (FractionRing A)
      (Polynomial A ⧸ Ideal.span ({f} : Set (Polynomial A))))
    ((Ideal.Quotient.mk
      (Ideal.span ({f} : Set (Polynomial A)))) Polynomial.X)
    (mapped_polynomial_eval₂_zero_ofId f)).toRingHom

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem dvrPolynomialQuotientFractionSurjection_root
    {π : A} (hπ : Irreducible π)
    (f q : Polynomial A) (hf : f = 1 + Polynomial.C π * q) :
    dvrPolynomialQuotientFractionSurjection hπ f q hf
      (AdjoinRoot.root (f.map (algebraMap A (FractionRing A)))) =
      (Ideal.Quotient.mk
        (Ideal.span ({f} : Set (Polynomial A)))) Polynomial.X := by
  let := quotientFractionAlgebra hπ f q hf
  let : IsScalarTower A (FractionRing A)
      (Polynomial A ⧸ Ideal.span ({f} : Set (Polynomial A))) :=
    quotientFractionAlgebra_tower hπ f q hf
  exact AdjoinRoot.liftAlgHom_root
    (f.map (algebraMap A (FractionRing A)))
    (Algebra.ofId (FractionRing A)
      (Polynomial A ⧸ Ideal.span ({f} : Set (Polynomial A))))
    ((Ideal.Quotient.mk
      (Ideal.span ({f} : Set (Polynomial A)))) Polynomial.X)
    (mapped_polynomial_eval₂_zero_ofId f)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem dvrPolynomialQuotientFractionSurjection_of_algebraMap
    {π : A} (hπ : Irreducible π)
    (f q : Polynomial A) (hf : f = 1 + Polynomial.C π * q)
    (a : A) :
    dvrPolynomialQuotientFractionSurjection hπ f q hf
      (AdjoinRoot.of (f.map (algebraMap A (FractionRing A)))
        ((algebraMap A (FractionRing A)) a)) =
      Ideal.Quotient.mk (Ideal.span ({f} : Set (Polynomial A)))
        (Polynomial.C a) := by
  let := quotientFractionAlgebra hπ f q hf
  let : IsScalarTower A (FractionRing A)
      (Polynomial A ⧸ Ideal.span ({f} : Set (Polynomial A))) :=
    quotientFractionAlgebra_tower hπ f q hf
  change
    AdjoinRoot.liftAlgHom
      (f.map (algebraMap A (FractionRing A)))
      (Algebra.ofId (FractionRing A)
        (Polynomial A ⧸ Ideal.span ({f} : Set (Polynomial A))))
      ((Ideal.Quotient.mk
        (Ideal.span ({f} : Set (Polynomial A)))) Polynomial.X)
      (mapped_polynomial_eval₂_zero_ofId f)
      (AdjoinRoot.of (f.map (algebraMap A (FractionRing A)))
        ((algebraMap A (FractionRing A)) a)) = _
  rw [AdjoinRoot.liftAlgHom_of]
  change quotientFractionLift hπ f q hf
    ((algebraMap A (FractionRing A)) a) = _
  rw [quotientFractionLift_algebraMap]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem dvrPolynomialQuotientFractionSurjection_surjective
    {π : A} (hπ : Irreducible π)
    (f q : Polynomial A) (hf : f = 1 + Polynomial.C π * q) :
    Function.Surjective
      (dvrPolynomialQuotientFractionSurjection hπ f q hf) := by
  let F := f.map (algebraMap A (FractionRing A))
  let ρ := Ideal.Quotient.mk (Ideal.span ({f} : Set (Polynomial A)))
  let φ := dvrPolynomialQuotientFractionSurjection hπ f q hf
  let ψ : Polynomial A →+*
      (Polynomial A ⧸ Ideal.span ({f} : Set (Polynomial A))) :=
    φ.comp ((AdjoinRoot.mk F).comp
      (Polynomial.mapRingHom (algebraMap A (FractionRing A))))
  have hψ : ψ = ρ := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.coe_comp, coe_mapRingHom, Function.comp_apply, map_C, AdjoinRoot.mk_C,
        dvrPolynomialQuotientFractionSurjection_of_algebraMap, ψ, φ, ρ, F]
    · simp only [RingHom.coe_comp, coe_mapRingHom, Function.comp_apply, map_X, AdjoinRoot.mk_X,
        dvrPolynomialQuotientFractionSurjection_root, ψ, φ, ρ, F]
  intro y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨AdjoinRoot.mk F (p.map (algebraMap A (FractionRing A))), ?_⟩
  exact RingHom.congr_fun hψ p

end

section

open scoped BigOperators

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def UnimodularRow {A : Type*} [CommRing A] {n : ℕ}
    (v : Fin n → A) : Prop :=
  ∃ c : Fin n → A, ∑ i, c i * v i = 1

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem unimodularRow_iff_span_range_eq_top
    {A : Type*} [CommRing A] {n : ℕ} (v : Fin n → A) :
    UnimodularRow v ↔ Ideal.span (Set.range v) = ⊤ := by
  rw [Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem unimodularRow_iff_avoids_maximalIdeals
    {A : Type*} [CommRing A] {n : ℕ} (v : Fin n → A) :
    UnimodularRow v ↔
      ∀ (M : Ideal A), M.IsMaximal → ∃ i : Fin n, v i ∉ M := by
  rw [unimodularRow_iff_span_range_eq_top]
  constructor
  · intro h M hM
    by_contra! hcontra
    have hle : Ideal.span (Set.range v) ≤ M :=
      Ideal.span_le.mpr (by
        rintro _ ⟨i, rfl⟩
        exact hcontra i)
    have htop : (⊤ : Ideal A) ≤ M := h ▸ hle
    exact hM.ne_top (top_unique htop)
  · intro h
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨i, hi⟩ := h M hM
    exact hi (hle (Ideal.subset_span ⟨i, rfl⟩))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def BassStableRangeAtMost (A : Type*) [CommRing A] (n : ℕ) : Prop :=
  ∀ (v : Fin (n + 1) → A), UnimodularRow v →
    ∃ s : Fin n → A,
      UnimodularRow fun i : Fin n =>
        v i.castSucc + s i * v (Fin.last n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev IntegralPolynomialStableRangeThree : Prop :=
  BassStableRangeAtMost IntegralPolynomial 3

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integer_ringKrullDim : ringKrullDim ℤ = 1 :=
  IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem integralPolynomial_ringKrullDim :
    ringKrullDim IntegralPolynomial = 2 := by
  rw [Polynomial.ringKrullDim_of_isNoetherianRing, integer_ringKrullDim]
  norm_num

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem specialLinear_column_unimodular
    {A : Type*} [CommRing A] {n : ℕ}
    (g : Matrix.SpecialLinearGroup (Fin n) A) (j : Fin n) :
    UnimodularRow (fun i : Fin n => g i j) := by
  refine ⟨fun i => (g⁻¹) j i, ?_⟩
  have h := congrArg
    (fun x : Matrix.SpecialLinearGroup (Fin n) A => x j j)
    (inv_mul_cancel g)
  change ((g⁻¹).val * g.val) j j = (1 : Matrix (Fin n) (Fin n) A) j j at h
  simpa only [Matrix.SpecialLinearGroup.coe_inv, Matrix.mul_apply, Matrix.one_apply_eq] using h

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem integralSpecialLinear_lastColumn_stableRange_shorten
    (hstable : IntegralPolynomialStableRangeThree)
    (g : IntegralSpecialLinearGroup) :
    ∃ c : Fin 3 → IntegralPolynomial,
      UnimodularRow fun i : Fin 3 =>
        g i.castSucc 3 + c i * g 3 3 := by
  exact hstable (fun i : Index => g i 3)
    (specialLinear_column_unimodular g 3)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_add_mem_avoiding_finite_prime_antichain
    {A : Type*} [CommRing A]
    (S : Set (Ideal A)) (hfinite : S.Finite)
    (hprime : ∀ p ∈ S, p.IsPrime)
    (hanti : ∀ ⦃p q : Ideal A⦄, p ∈ S → q ∈ S → p ≤ q → p = q)
    (J : Ideal A) (x : A)
    (hadmiss : ∀ p ∈ S, x ∈ p → ¬ J ≤ p) :
    ∃ y ∈ J, ∀ p ∈ S, x + y ∉ p := by
  classical
  let all : Finset (Ideal A) := hfinite.toFinset
  let contains : Finset (Ideal A) := all.filter (fun p => x ∈ p)
  let avoids : Finset (Ideal A) := all.filter (fun p => x ∉ p)
  let correction : Ideal A := J * avoids.prod (fun p => p)
  have hall {p : Ideal A} : p ∈ all ↔ p ∈ S := by
    simp only [Set.Finite.mem_toFinset, all]
  have hcontains {p : Ideal A} : p ∈ contains ↔ p ∈ S ∧ x ∈ p := by
    simp only [Finset.mem_filter, hall, contains]
  have havoids {p : Ideal A} : p ∈ avoids ↔ p ∈ S ∧ x ∉ p := by
    simp only [Finset.mem_filter, hall, avoids]
  have hcorrection_not_le : ∀ p ∈ contains, ¬ correction ≤ p := by
    intro p hp hle
    have hpS : p ∈ S := (hcontains.mp hp).1
    have hpx : x ∈ p := (hcontains.mp hp).2
    have hpp := hprime p hpS
    rcases hpp.mul_le.mp hle with hJ | hprod
    · exact hadmiss p hpS hpx hJ
    · rcases hpp.prod_le.mp hprod with ⟨q, hq, hqp⟩
      have hqS : q ∈ S := (havoids.mp hq).1
      have hqx : x ∉ q := (havoids.mp hq).2
      exact hqx ((hanti hqS hpS hqp).symm ▸ hpx)
  have hnot_subset : ¬ ((correction : Set A) ⊆
      ⋃ p ∈ (contains : Set (Ideal A)), (p : Set A)) := by
    intro hsubset
    obtain ⟨p, hp, hle⟩ :=
      (Ideal.subset_union_prime (⊥ : Ideal A) (⊥ : Ideal A)
        (f := id)
        (fun p hp _ _ => hprime p (hcontains.mp hp).1)).mp hsubset
    exact hcorrection_not_le p hp hle
  obtain ⟨y, hy, hyavoid⟩ := Set.not_subset.mp hnot_subset
  refine ⟨y, Ideal.mul_le_left hy, ?_⟩
  intro p hp hsum
  by_cases hxp : x ∈ p
  · have hyp : y ∈ p := by
      convert p.sub_mem hsum hxp using 1; ring
    exact hyavoid (Set.mem_iUnion₂.mpr ⟨p, hcontains.mpr ⟨hp, hxp⟩, hyp⟩)
  · have hpavoids : p ∈ avoids := havoids.mpr ⟨hp, hxp⟩
    have hproduct : avoids.prod (fun q => q) ≤ p :=
      Ideal.prod_le_inf.trans (Finset.inf_le hpavoids)
    have hyp : y ∈ p := hproduct (Ideal.mul_le_right hy)
    exact hxp (by convert p.sub_mem hsum hyp using 1; ring)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_add_mul_isUnit_of_finite_maximalIdeals
    {A : Type*} [CommRing A]
    (hfinite : {p : Ideal A | p.IsMaximal}.Finite)
    {x z : A} (hcoprime : IsCoprime x z) :
    ∃ t : A, IsUnit (x + t * z) := by
  let S : Set (Ideal A) := {p | p.IsMaximal}
  obtain ⟨y, hy, havoid⟩ :=
    exists_add_mem_avoiding_finite_prime_antichain S hfinite
      (fun p hp => hp.isPrime)
      (fun p q hp hq hpq => hp.eq_of_le hq.ne_top hpq)
      (Ideal.span ({z} : Set A)) x (by
        intro p hp hxp hspan
        obtain ⟨a, b, hab⟩ := hcoprime
        have hzp : z ∈ p := hspan (Ideal.mem_span_singleton_self z)
        have hone : (1 : A) ∈ p := hab ▸
          p.add_mem (p.mul_mem_left a hxp) (p.mul_mem_left b hzp)
        exact hp.ne_top (p.eq_top_of_isUnit_mem hone isUnit_one))
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hy
  refine ⟨t, ?_⟩
  rw [ht]
  by_contra hunit
  obtain ⟨p, hp, hmem⟩ :=
    exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hunit)
  exact havoid p hp hmem

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_add_mul_isUnit_of_artinian
    {A : Type*} [CommRing A] [IsArtinianRing A]
    {x z : A} (hcoprime : IsCoprime x z) :
    ∃ t : A, IsUnit (x + t * z) :=
  exists_add_mul_isUnit_of_finite_maximalIdeals
    (IsArtinianRing.setOfPred_isMaximal_finite A) hcoprime

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem krullDimLE_zero_quotient_span_pair_of_avoids_minimalPrimes
    {A : Type*} [CommRing A] [IsDomain A]
    (hdim : ringKrullDim A = 2)
    {a b : A} (ha : a ≠ 0)
    (havoid : ∀ p ∈ (Ideal.span ({a} : Set A)).minimalPrimes, b ∉ p) :
    Ring.KrullDimLE 0
      (A ⧸ (Ideal.span ({a} : Set A) ⊔ Ideal.span ({b} : Set A))) := by
  let : FiniteRingKrullDim A :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr ⟨by simp only [hdim, ne_eq, WithBot.ofNat_ne_bot,
                                                    not_false_eq_true], by
      rw [hdim]
      change (↑(2 : ℕ∞) : WithBot ℕ∞) ≠ ↑(⊤ : ℕ∞)
      exact fun h => ENat.natCast_ne_top 2 (WithBot.coe_injective h)⟩
  apply Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr
  intro p hp
  let : p.IsPrime := hp.isPrime
  have haspan : Ideal.span ({a} : Set A) ≤ p := le_sup_left.trans hp.le
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le haspan
  let : q.IsPrime := hq.isPrime
  have hq_ne_bot : q ≠ ⊥ := by
    intro hbot
    have hamem : a ∈ q := hq.le (Ideal.mem_span_singleton_self a)
    rw [hbot, Ideal.mem_bot] at hamem
    exact ha hamem
  have hbp : b ∈ p :=
    (le_sup_right.trans hp.le) (Ideal.mem_span_singleton_self b)
  have hq_lt_p : q < p := lt_of_le_of_ne hqp (by
    intro heq
    exact havoid q hq (heq ▸ hbp))
  have hone_le_q : (1 : ℕ∞) ≤ q.height := by
    have h := Ideal.height_add_one_le_of_lt_of_isPrime
      (show (⊥ : Ideal A) < q from bot_lt_iff_ne_bot.mpr hq_ne_bot)
    simpa only [ge_iff_le, Ideal.height_bot, zero_add] using h
  have htwo_le_p : (2 : ℕ∞) ≤ p.height := calc
    (2 : ℕ∞) = 1 + 1 := by norm_num
    _ ≤ q.height + 1 := by gcongr
    _ ≤ p.height := Ideal.height_add_one_le_of_lt_of_isPrime hq_lt_p
  apply Ideal.isMaximal_of_height_eq_ringKrullDim
  apply le_antisymm Ideal.height_le_ringKrullDim_of_isPrime
  rw [hdim]
  exact WithBot.coe_le_coe.mpr htwo_le_p

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_nonzero_elementary_first_coordinate
    {A : Type*} [CommRing A] [Nontrivial A]
    (v : Fin 4 → A) (hv : UnimodularRow v) :
    ∃ u w z : A, v 0 + u * v 1 + w * v 2 + z * v 3 ≠ 0 := by
  have hentry : v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0 ∨ v 3 ≠ 0 := by
    by_contra hnone
    push Not at hnone
    obtain ⟨r, hr⟩ := hv
    simp only [Fin.sum_univ_succ, Fin.isValue, hnone.1, mul_zero, Fin.succ_zero_eq_one, hnone.2.1,
      Fin.succ_one_eq_two, hnone.2.2.1, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_singleton, Fin.reduceSucc, hnone.2.2.2, add_zero, zero_ne_one] at hr
  by_cases h0 : v 0 = 0
  · by_cases h1 : v 1 = 0
    · by_cases h2 : v 2 = 0
      · have h3 : v 3 ≠ 0 := by simpa only [Fin.isValue, ne_eq, h0, not_true_eq_false, h1, h2,
                                  false_or] using hentry
        exact ⟨0, 0, 1, by simpa only [Fin.isValue, h0, zero_mul, add_zero, one_mul, zero_add,
                             ne_eq] using h3⟩
      · exact ⟨0, 1, 0, by simpa only [Fin.isValue, h0, zero_mul, add_zero, one_mul, zero_add,
                             ne_eq] using h2⟩
    · exact ⟨1, 0, 0, by simpa only [Fin.isValue, h0, one_mul, zero_add, zero_mul, add_zero,
                           ne_eq] using h1⟩
  · exact ⟨0, 0, 0, by simpa only [Fin.isValue, zero_mul, add_zero, ne_eq] using h0⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_second_coordinate_avoiding_minimalPrimes
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (a b c d : A)
    (hrow : ∃ ra rb rc rd : A, ra * a + rb * b + rc * c + rd * d = 1) :
    ∃ k l : A, ∀ p ∈ (Ideal.span ({a} : Set A)).minimalPrimes,
      b + k * c + l * d ∉ p := by
  let S : Set (Ideal A) := (Ideal.span ({a} : Set A)).minimalPrimes
  let J : Ideal A := Ideal.span ({c} : Set A) ⊔ Ideal.span ({d} : Set A)
  obtain ⟨y, hy, havoid⟩ :=
    exists_add_mem_avoiding_finite_prime_antichain S
      (Ideal.finite_minimalPrimes_of_isNoetherianRing A _)
      (fun p hp => hp.isPrime)
      (fun p q hp hq hpq =>
        le_antisymm hpq (hq.2 ⟨hp.isPrime, hp.le⟩ hpq))
      J b (by
        intro p hp hbp hJ
        obtain ⟨ra, rb, rc, rd, hcomb⟩ := hrow
        have hap : a ∈ p := hp.le (Ideal.mem_span_singleton_self a)
        have hcp : c ∈ p :=
          hJ ((show Ideal.span ({c} : Set A) ≤ J from le_sup_left)
            (Ideal.mem_span_singleton_self c))
        have hdp : d ∈ p :=
          hJ ((show Ideal.span ({d} : Set A) ≤ J from le_sup_right)
            (Ideal.mem_span_singleton_self d))
        have hone : (1 : A) ∈ p := hcomb ▸
          p.add_mem (p.add_mem (p.add_mem
            (p.mul_mem_left ra hap) (p.mul_mem_left rb hbp))
            (p.mul_mem_left rc hcp)) (p.mul_mem_left rd hdp)
        exact hp.isPrime.one_notMem hone)
  obtain ⟨yc, hyc, yd, hyd, heq⟩ := Submodule.mem_sup.mp hy
  obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.mp hyc
  obtain ⟨l, hl⟩ := Ideal.mem_span_singleton'.mp hyd
  refine ⟨k, l, ?_⟩
  intro p hp
  have hrearrange : b + k * c + l * d = b + y := by
    rw [← heq, ← hk, ← hl]
    ring
  rw [hrearrange]
  exact havoid p hp

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_third_coordinate_unit_mod_span_pair
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 2)
    (a b c d : A) (ha : a ≠ 0)
    (havoid : ∀ p ∈ (Ideal.span ({a} : Set A)).minimalPrimes, b ∉ p)
    (hrow : ∃ ra rb rc rd : A, ra * a + rb * b + rc * c + rd * d = 1) :
    ∃ t : A,
      IsUnit ((Ideal.Quotient.mk
        (Ideal.span ({a} : Set A) ⊔ Ideal.span ({b} : Set A))) (c + t * d)) := by
  let I : Ideal A := Ideal.span ({a} : Set A) ⊔ Ideal.span ({b} : Set A)
  let π : A →+* (A ⧸ I) := Ideal.Quotient.mk I
  let : Ring.KrullDimLE 0 (A ⧸ I) :=
    krullDimLE_zero_quotient_span_pair_of_avoids_minimalPrimes hdim ha havoid
  let : IsArtinianRing (A ⧸ I) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  have ha0 : π a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    ((show Ideal.span ({a} : Set A) ≤ I from le_sup_left)
      (Ideal.mem_span_singleton_self a))
  have hb0 : π b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    ((show Ideal.span ({b} : Set A) ≤ I from le_sup_right)
      (Ideal.mem_span_singleton_self b))
  obtain ⟨ra, rb, rc, rd, hcomb⟩ := hrow
  have hcoprime : IsCoprime (π c) (π d) := by
    refine ⟨π rc, π rd, ?_⟩
    have hmap := congrArg π hcomb
    simpa only [map_add, map_mul, ha0, mul_zero, hb0, add_zero, zero_add, map_one] using hmap
  obtain ⟨tq, hu⟩ := exists_add_mul_isUnit_of_artinian hcoprime
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective tq
  refine ⟨t, ?_⟩
  simpa only [map_add, map_mul] using hu

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem unimodularRow_three_of_isUnit_quotient
    {A : Type*} [CommRing A] (a b c : A)
    (hunit : IsUnit ((Ideal.Quotient.mk
      (Ideal.span ({a} : Set A) ⊔ Ideal.span ({b} : Set A))) c)) :
    UnimodularRow ![a, b, c] := by
  let I : Ideal A := Ideal.span ({a} : Set A) ⊔ Ideal.span ({b} : Set A)
  let π : A →+* (A ⧸ I) := Ideal.Quotient.mk I
  rw [unimodularRow_iff_avoids_maximalIdeals]
  intro M hM
  by_contra hnone
  push Not at hnone
  have ha : a ∈ M := hnone 0
  have hb : b ∈ M := hnone 1
  have hc : c ∈ M := hnone 2
  have hIM : I ≤ M := sup_le
    ((Ideal.span_singleton_le_iff_mem M).mpr ha)
    ((Ideal.span_singleton_le_iff_mem M).mpr hb)
  obtain ⟨q, hq⟩ := isUnit_iff_exists_inv.mp hunit
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hzero : π (c * r - 1) = 0 := calc
    π (c * r - 1) = π c * π r - 1 := by simp only [map_sub, map_mul, map_one]
    _ = 0 := sub_eq_zero.mpr hq
  have hmem : c * r - 1 ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hzero
  have hnegone : (-1 : A) ∈ M := by
    have hcr : c * r ∈ M := M.mul_mem_right r hc
    convert M.sub_mem (hIM hmem) hcr using 1; ring
  exact hM.ne_top (M.eq_top_of_isUnit_mem hnegone isUnit_neg_one)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem bassStableRangeThree_of_noetherian_domain_dimension_two
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 2) :
    BassStableRangeAtMost A 3 := by
  intro v hv
  obtain ⟨u, w, z, hfirst⟩ := exists_nonzero_elementary_first_coordinate v hv
  obtain ⟨r, hr⟩ := hv
  have hrow_original :
      r 0 * v 0 + r 1 * v 1 + r 2 * v 2 + r 3 * v 3 = 1 := by
    simpa only [Fin.isValue, add_assoc, Nat.reduceAdd, Fin.sum_univ_succ, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
      Fin.reduceSucc] using hr
  let a : A := v 0 + u * v 1 + w * v 2 + z * v 3
  have ha : a ≠ 0 := hfirst
  have hrow_first : ∃ ra rb rc rd : A,
      ra * a + rb * v 1 + rc * v 2 + rd * v 3 = 1 := by
    refine ⟨r 0, r 1 - r 0 * u, r 2 - r 0 * w, r 3 - r 0 * z, ?_⟩
    calc
      r 0 * a + (r 1 - r 0 * u) * v 1 +
          (r 2 - r 0 * w) * v 2 + (r 3 - r 0 * z) * v 3 =
          r 0 * v 0 + r 1 * v 1 + r 2 * v 2 + r 3 * v 3 := by
            dsimp [a]
            ring
      _ = 1 := hrow_original
  obtain ⟨k, l, havoid⟩ :=
    exists_second_coordinate_avoiding_minimalPrimes a (v 1) (v 2) (v 3)
      hrow_first
  let b : A := v 1 + k * v 2 + l * v 3
  have hrow_second : ∃ ra rb rc rd : A,
      ra * a + rb * b + rc * v 2 + rd * v 3 = 1 := by
    obtain ⟨ra, rb, rc, rd, hrow⟩ := hrow_first
    refine ⟨ra, rb, rc - rb * k, rd - rb * l, ?_⟩
    calc
      ra * a + rb * b + (rc - rb * k) * v 2 + (rd - rb * l) * v 3 =
          ra * a + rb * v 1 + rc * v 2 + rd * v 3 := by
            dsimp [b]
            ring
      _ = 1 := hrow
  obtain ⟨t, ht⟩ := exists_third_coordinate_unit_mod_span_pair
    hdim a b (v 2) (v 3) ha havoid hrow_second
  have hshort : UnimodularRow ![a, b, v 2 + t * v 3] :=
    unimodularRow_three_of_isUnit_quotient a b (v 2 + t * v 3) ht
  let s₀ : A := z - u * l + u * k * t - w * t
  let s₁ : A := l - k * t
  refine ⟨![s₀, s₁, t], ?_⟩
  rw [unimodularRow_iff_avoids_maximalIdeals]
  intro M hM
  by_contra hnone
  push Not at hnone
  have hzero : v 0 + s₀ * v 3 ∈ M := by simpa only [Fin.isValue, Fin.castSucc_zero,
                                          Matrix.cons_val_zero, Fin.reduceLast] using hnone 0
  have hone : v 1 + s₁ * v 3 ∈ M := by simpa only [Fin.isValue, Fin.castSucc_one,
                                         Matrix.cons_val_one, Matrix.cons_val_zero,
                                         Fin.reduceLast] using hnone 1
  have htwo : v 2 + t * v 3 ∈ M := by simpa only [Fin.isValue, Fin.reduceCastSucc, Matrix.cons_val,
                                        Fin.reduceLast] using hnone 2
  have hb : b ∈ M := by
    have h := M.add_mem hone (M.mul_mem_left k htwo)
    convert h using 1; dsimp [b, s₁]; ring
  have haM : a ∈ M := by
    have h := M.add_mem (M.add_mem hzero (M.mul_mem_left u hone))
      (M.mul_mem_left w htwo)
    convert h using 1; dsimp [a, s₀, s₁]; ring
  obtain ⟨i, hi⟩ :=
    (unimodularRow_iff_avoids_maximalIdeals _).mp hshort M hM
  fin_cases i
  · exact hi haM
  · exact hi hb
  · exact hi htwo

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem integralPolynomial_stableRangeThree : IntegralPolynomialStableRangeThree :=
  bassStableRangeThree_of_noetherian_domain_dimension_two
    integralPolynomial_ringKrullDim

end

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem isUnit_quotient_span_singleton_iff_isCoprime
    {A : Type*} [CommRing A] (f g : A) :
    IsUnit ((Ideal.Quotient.mk (Ideal.span ({f} : Set A))) g) ↔
      IsCoprime f g := by
  let q := Ideal.Quotient.mk (Ideal.span ({f} : Set A))
  have hfzero : q f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton_self f)
  constructor
  · intro hunit
    obtain ⟨bbar, hbbar⟩ := isUnit_iff_exists_inv'.mp hunit
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective bbar
    change q b * q g = 1 at hbbar
    have hmem : 1 - b * g ∈ Ideal.span ({f} : Set A) :=
      Ideal.Quotient.eq_zero_iff_mem.mp (by
        change q (1 - b * g) = 0
        simp only [map_sub, map_one, map_mul, hbbar, sub_self])
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
    exact ⟨a, b, by rw [ha]; ring⟩
  · rintro ⟨a, b, hab⟩
    refine isUnit_iff_exists_inv'.mpr ⟨q b, ?_⟩
    have hmap := congrArg q hab
    simpa only [map_add, map_mul, hfzero, mul_zero, zero_add, map_one] using hmap

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem dvr_one_add_uniformizer_mul_ne_zero
    {A : Type*} [CommRing A]
    (π : A) (hπ : Irreducible π) (q : Polynomial A) :
    (1 + Polynomial.C π * q : Polynomial A) ≠ 0 := by
  intro hzero
  have hconstant := congrArg (fun p : Polynomial A => p.coeff 0) hzero
  simp only [Polynomial.coeff_add, Polynomial.coeff_one_zero, Polynomial.mul_coeff_zero,
    Polynomial.coeff_C_zero, Polynomial.coeff_zero] at hconstant
  have hdiv : π ∣ (1 : A) := by
    refine ⟨-(q.coeff 0), ?_⟩
    linear_combination hconstant
  exact hπ.not_isUnit (isUnit_of_dvd_one hdiv)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem dvr_fraction_polynomial_one_add_uniformizer_mul_ne_zero
    {A : Type*} [CommRing A]
    (π : A) (hπ : Irreducible π) (q : Polynomial A) :
    Polynomial.map (algebraMap A (FractionRing A))
      (1 + Polynomial.C π * q) ≠ 0 := by
  exact (Polynomial.map_ne_zero_iff
    (IsFractionRing.injective A (FractionRing A))).mpr
      (dvr_one_add_uniformizer_mul_ne_zero π hπ q)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem dvr_polynomial_field_quotient_isArtinian_of_ne_zero
    {K : Type*} [Field K] (f : Polynomial K) (hf : f ≠ 0) :
    IsArtinianRing (Polynomial K ⧸ Ideal.span ({f} : Set (Polynomial K))) := by
  let g : Polynomial K := f * Polynomial.C f.leadingCoeff⁻¹
  have hg : g.Monic := Polynomial.monic_mul_leadingCoeff_inv hf
  have hunit : IsUnit (Polynomial.C f.leadingCoeff⁻¹) :=
    Polynomial.isUnit_C.mpr
      (isUnit_iff_ne_zero.mpr
        (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hf)))
  have hspan : Ideal.span ({g} : Set (Polynomial K)) =
      Ideal.span ({f} : Set (Polynomial K)) :=
    Ideal.span_singleton_mul_right_unit hunit f
  let : Module.Finite K
      (Polynomial K ⧸ Ideal.span ({g} : Set (Polynomial K))) :=
    hg.finite_quotient
  have hart : IsArtinianRing
      (Polynomial K ⧸ Ideal.span ({g} : Set (Polynomial K))) :=
    IsArtinianRing.of_finite K _
  rw [← hspan]
  exact hart

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem dvr_maximalIdeals_finite_of_surjective_field_polynomial_quotient
    {K S : Type*} [Field K] [CommRing S]
    (f : Polynomial K) (hf : f ≠ 0)
    (φ : (Polynomial K ⧸ Ideal.span ({f} : Set (Polynomial K))) →+* S)
    (hφ : Function.Surjective φ) :
    {I : Ideal S | I.IsMaximal}.Finite := by
  let : IsArtinianRing
      (Polynomial K ⧸ Ideal.span ({f} : Set (Polynomial K))) :=
    dvr_polynomial_field_quotient_isArtinian_of_ne_zero f hf
  let : IsArtinianRing S := hφ.isArtinianRing
  exact IsArtinianRing.setOfPred_isMaximal_finite S

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem dvr_mod_uniformizer_one_quotient_maximalIdeals_finite
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) (hπ : Irreducible π) (f q : Polynomial A)
    (hf : f = 1 + Polynomial.C π * q) :
    {I : Ideal (Polynomial A ⧸ Ideal.span ({f} : Set (Polynomial A))) |
      I.IsMaximal}.Finite := by
  have hnonzero :
      Polynomial.map (algebraMap A (FractionRing A)) f ≠ 0 := by
    rw [hf]
    exact dvr_fraction_polynomial_one_add_uniformizer_mul_ne_zero π hπ q
  exact dvr_maximalIdeals_finite_of_surjective_field_polynomial_quotient
    (Polynomial.map (algebraMap A (FractionRing A)) f) hnonzero
    (dvrPolynomialQuotientFractionSurjection hπ f q hf)
    (dvrPolynomialQuotientFractionSurjection_surjective hπ f q hf)

end

section

open Polynomial

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_residue_polynomial_isUnit_of_determinant
    {A : Type*} [CommRing A] [IsLocalRing A]
    (π : A) (hπ : ¬ IsUnit π)
    (g p q : Polynomial A)
    (hdet : Polynomial.C π * q - g * p = 1) :
    IsUnit (g.map (IsLocalRing.residue A)) := by
  have hzero : (IsLocalRing.residue A) π = 0 := by
    apply (IsLocalRing.residue_eq_zero_iff π).mpr
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hπ
  have hdet' := congrArg (Polynomial.map (IsLocalRing.residue A)) hdet
  have hmul :
      g.map (IsLocalRing.residue A) *
        -(p.map (IsLocalRing.residue A)) = 1 := by
    simpa only [mul_neg, Polynomial.map_sub, Polynomial.map_mul, map_C, hzero, map_zero, zero_mul,
      zero_sub, Polynomial.map_one] using hdet'
  exact isUnit_iff_exists_inv.mpr
    ⟨-(p.map (IsLocalRing.residue A)), hmul⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_residue_polynomial_eq_C_of_determinant
    {A : Type*} [CommRing A] [IsLocalRing A]
    (π : A) (hπ : ¬ IsUnit π)
    (g p q : Polynomial A)
    (hdet : Polynomial.C π * q - g * p = 1) :
    g.map (IsLocalRing.residue A) =
      Polynomial.C ((IsLocalRing.residue A) (g.coeff 0)) := by
  obtain ⟨c, hc, hcg⟩ := Polynomial.isUnit_iff.mp
    (suslin_residue_polynomial_isUnit_of_determinant π hπ g p q hdet)
  have hc0 : c = (IsLocalRing.residue A) (g.coeff 0) := by
    have h := congrArg (fun r : Polynomial (IsLocalRing.ResidueField A) =>
      r.coeff 0) hcg
    simpa only [coeff_C_zero, coeff_map] using h
  simpa only [hc0] using hcg.symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_residue_constantCoeff_isUnit_of_determinant
    {A : Type*} [CommRing A] [IsLocalRing A]
    (π : A) (hπ : ¬ IsUnit π)
    (g p q : Polynomial A)
    (hdet : Polynomial.C π * q - g * p = 1) :
    IsUnit ((IsLocalRing.residue A) (g.coeff 0)) := by
  have hunit :=
    suslin_residue_polynomial_isUnit_of_determinant π hπ g p q hdet
  rw [suslin_residue_polynomial_eq_C_of_determinant
    π hπ g p q hdet, Polynomial.isUnit_C] at hunit
  exact hunit

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_dvr_polynomial_constant_add_uniformizer_mul
    {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    {π : A} (hπ : Irreducible π) (g : Polynomial A)
    (hconstant : g.map (IsLocalRing.residue A) =
      Polynomial.C ((IsLocalRing.residue A) (g.coeff 0))) :
    ∃ h : Polynomial A,
      g = Polynomial.C (g.coeff 0) + Polynomial.C π * h := by
  have hzero :
      (g - Polynomial.C (g.coeff 0)).map (IsLocalRing.residue A) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_C, hconstant, sub_self]
  have hcoeff : ∀ n : ℕ, π ∣
      (g - Polynomial.C (g.coeff 0)).coeff n := by
    intro n
    have hn := congrArg
      (fun r : Polynomial (IsLocalRing.ResidueField A) => r.coeff n) hzero
    have hresidue :
        (IsLocalRing.residue A)
          ((g - Polynomial.C (g.coeff 0)).coeff n) = 0 := by
      simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using hn
    have hmem := (IsLocalRing.residue_eq_zero_iff _).mp hresidue
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
    exact hmem
  obtain ⟨h, hh⟩ :=
    (Polynomial.C_dvd_iff_dvd_coeff π
      (g - Polynomial.C (g.coeff 0))).mpr hcoeff
  refine ⟨h, ?_⟩
  calc
    g = (g - Polynomial.C (g.coeff 0)) + Polynomial.C (g.coeff 0) := by ring
    _ = Polynomial.C π * h + Polynomial.C (g.coeff 0) := by rw [hh]
    _ = Polynomial.C (g.coeff 0) + Polynomial.C π * h := by ring

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_dvr_uniformizer_polynomial_unit_decomposition_of_determinant
    {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    {π : A} (hπ : Irreducible π)
    (g p q : Polynomial A)
    (hdet : Polynomial.C π * q - g * p = 1) :
    ∃ (u : A) (h : Polynomial A),
      IsUnit u ∧ g = Polynomial.C u + Polynomial.C π * h := by
  have hconstant := suslin_residue_polynomial_eq_C_of_determinant
    π hπ.not_isUnit g p q hdet
  have hresidueUnit := suslin_residue_constantCoeff_isUnit_of_determinant
    π hπ.not_isUnit g p q hdet
  have hunit : IsUnit (g.coeff 0) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hresidueUnit.ne_zero
  obtain ⟨h, hh⟩ :=
    suslin_dvr_polynomial_constant_add_uniformizer_mul hπ g hconstant
  exact ⟨g.coeff 0, h, hunit, hh⟩

end

section

open Polynomial

variable {A : Type*} [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem dvr_uniformizer_span_isMaximal
    {π : A} (hπ : Irreducible π) :
    (Ideal.span ({π} : Set A)).IsMaximal := by
  rw [← hπ.maximalIdeal_eq]
  exact IsLocalRing.maximalIdeal.isMaximal A

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[reducible]
private noncomputable def dvrUniformizerQuotientField
    {π : A} (hπ : Irreducible π) :
    Field (A ⧸ Ideal.span ({π} : Set A)) := by
  letI : (Ideal.span ({π} : Set A)).IsMaximal :=
    dvr_uniformizer_span_isMaximal hπ
  exact Ideal.Quotient.field _

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem dvr_uniformizer_quotient_eq_zero_iff_dvd
    {π : A} (_hπ : Irreducible π) (a : A) :
    Ideal.Quotient.mk (Ideal.span ({π} : Set A)) a = 0 ↔ π ∣ a := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem dvr_polynomial_map_uniformizer_zero_iff
    {π : A} (hπ : Irreducible π) (f : Polynomial A) :
    f.map (Ideal.Quotient.mk (Ideal.span ({π} : Set A))) = 0 ↔
      ∀ n : ℕ, π ∣ f.coeff n := by
  constructor
  · intro h n
    have hn := congrArg (fun p : Polynomial
      (A ⧸ Ideal.span ({π} : Set A)) => p.coeff n) h
    simpa only [coeff_map, coeff_zero, dvr_uniformizer_quotient_eq_zero_iff_dvd hπ] using hn
  · intro h
    apply Polynomial.ext
    intro n
    simp only [coeff_map, coeff_zero, dvr_uniformizer_quotient_eq_zero_iff_dvd hπ, h n]

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem dvr_polynomial_map_uniformizer_zero_iff_C_dvd
    {π : A} (hπ : Irreducible π) (f : Polynomial A) :
    f.map (Ideal.Quotient.mk (Ideal.span ({π} : Set A))) = 0 ↔
      Polynomial.C π ∣ f := by
  rw [dvr_polynomial_map_uniformizer_zero_iff hπ,
    Polynomial.C_dvd_iff_dvd_coeff]

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem dvr_polynomial_eq_one_add_uniformizer_mul_of_residue_one
    {π : A} (hπ : Irreducible π) (f : Polynomial A)
    (hone : f.map (Ideal.Quotient.mk
      (Ideal.span ({π} : Set A))) = 1) :
    ∃ q : Polynomial A, f = 1 + Polynomial.C π * q := by
  have hzero : (f - 1).map (Ideal.Quotient.mk
      (Ideal.span ({π} : Set A))) = 0 := by
    simp only [Polynomial.map_sub, hone, Polynomial.map_one, sub_self]
  obtain ⟨q, hq⟩ :=
    (dvr_polynomial_map_uniformizer_zero_iff_C_dvd hπ (f - 1)).mp hzero
  refine ⟨q, ?_⟩
  rw [← hq]
  ring

end

section

namespace LocalElementaryProof

open Matrix
open scoped BigOperators

universe u

variable {A : Type u} [CommRing A]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def localElementarySubgroup (A : Type u) [CommRing A] :
    Subgroup (Matrix.SpecialLinearGroup (Fin 4) A) :=
  Subgroup.closure
    {g | ∃ (i j : Fin 4) (h : i ≠ j) (a : A),
      g = Matrix.SpecialLinearGroup.transvection h a}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem transvection_mem (i j : Fin 4) (h : i ≠ j) (a : A) :
    Matrix.SpecialLinearGroup.transvection h a ∈ localElementarySubgroup A :=
  Subgroup.subset_closure ⟨i, j, h, a, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem transvection_smul_same (i j : Fin 4) (h : i ≠ j) (a : A)
    (v : Fin 4 → A) :
    (Matrix.SpecialLinearGroup.transvection h a • v) i =
      v i + a * v j := by
  change ((Matrix.SpecialLinearGroup.transvection h a).val *ᵥ v) i = _
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec,
    Matrix.one_mulVec, Matrix.single_mulVec]
  simp only [Pi.add_apply, Function.update_self]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem transvection_smul_other (i j k : Fin 4) (h : i ≠ j)
    (hk : k ≠ i) (a : A) (v : Fin 4 → A) :
    (Matrix.SpecialLinearGroup.transvection h a • v) k = v k := by
  change ((Matrix.SpecialLinearGroup.transvection h a).val *ᵥ v) k = _
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec,
    Matrix.one_mulVec, Matrix.single_mulVec]
  simp only [Pi.add_apply, ne_eq, hk, not_false_eq_true, Function.update_of_ne, Pi.zero_apply,
    add_zero]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def coordinateRotation (i j : Fin 4) (h : i ≠ j) :
    Matrix.SpecialLinearGroup (Fin 4) A :=
  Matrix.SpecialLinearGroup.transvection h 1 *
    Matrix.SpecialLinearGroup.transvection h.symm (-1) *
    Matrix.SpecialLinearGroup.transvection h 1

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem coordinateRotation_mem (i j : Fin 4) (h : i ≠ j) :
    coordinateRotation (A := A) i j h ∈ localElementarySubgroup A :=
  (localElementarySubgroup A).mul_mem
    ((localElementarySubgroup A).mul_mem (transvection_mem i j h 1)
      (transvection_mem j i h.symm (-1)))
    (transvection_mem i j h 1)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem coordinateRotation_smul_left (i j : Fin 4) (h : i ≠ j)
    (v : Fin 4 → A) :
    (coordinateRotation (A := A) i j h • v) i = v j := by
  simp only [coordinateRotation, mul_smul]
  rw [transvection_smul_same]
  rw [transvection_smul_other j i i h.symm h]
  rw [transvection_smul_same j i]
  rw [transvection_smul_same i j]
  rw [transvection_smul_other i j j h h.symm]
  ring

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem coordinateRotation_smul_right (i j : Fin 4) (h : i ≠ j)
    (v : Fin 4 → A) :
    (coordinateRotation (A := A) i j h • v) j = -v i := by
  simp only [coordinateRotation, mul_smul]
  rw [transvection_smul_other i j j h h.symm]
  rw [transvection_smul_same j i]
  rw [transvection_smul_same i j]
  rw [transvection_smul_other i j j h h.symm]
  ring

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem coordinateRotation_smul_other (i j k : Fin 4) (h : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) (v : Fin 4 → A) :
    (coordinateRotation (A := A) i j h • v) k = v k := by
  simp only [coordinateRotation, mul_smul]
  rw [transvection_smul_other i j k h hki]
  rw [transvection_smul_other j i k h.symm hkj]
  rw [transvection_smul_other i j k h hki]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def unitPairNormalizer (i j : Fin 4) (h : i ≠ j)
    (v : Fin 4 → A) (hu : IsUnit (v i)) :
    Matrix.SpecialLinearGroup (Fin 4) A :=
  Matrix.SpecialLinearGroup.transvection h.symm (-1) *
    Matrix.SpecialLinearGroup.transvection h (1 - v i) *
    Matrix.SpecialLinearGroup.transvection h.symm
      ((↑hu.unit⁻¹ : A) * (1 - v j))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem unitPairNormalizer_mem (i j : Fin 4) (h : i ≠ j)
    (v : Fin 4 → A) (hu : IsUnit (v i)) :
    unitPairNormalizer i j h v hu ∈ localElementarySubgroup A :=
  (localElementarySubgroup A).mul_mem
    ((localElementarySubgroup A).mul_mem
      (transvection_mem j i h.symm (-1))
      (transvection_mem i j h (1 - v i)))
    (transvection_mem j i h.symm
      ((↑hu.unit⁻¹ : A) * (1 - v j)))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem unitPairNormalizer_smul_pivot (i j : Fin 4) (h : i ≠ j)
    (v : Fin 4 → A) (hu : IsUnit (v i)) :
    (unitPairNormalizer i j h v hu • v) i = 1 := by
  let t := Matrix.SpecialLinearGroup.transvection h.symm
    ((↑hu.unit⁻¹ : A) * (1 - v j))
  have htj : (t • v) j = 1 := by
    change (Matrix.SpecialLinearGroup.transvection h.symm
      ((↑hu.unit⁻¹ : A) * (1 - v j)) • v) j = 1
    rw [transvection_smul_same]
    calc
      v j + ((↑hu.unit⁻¹ : A) * (1 - v j)) * v i =
          v j + (1 - v j) * ((↑hu.unit⁻¹ : A) * v i) := by ring
      _ = 1 := by rw [hu.val_inv_mul]; ring
  have hti : (t • v) i = v i :=
    transvection_smul_other j i i h.symm h _ v
  unfold unitPairNormalizer
  rw [mul_smul, mul_smul,
    transvection_smul_other j i i h.symm h,
    transvection_smul_same]
  change (t • v) i + (1 - v i) * (t • v) j = 1
  rw [hti, htj]
  ring

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem unitPairNormalizer_smul_auxiliary (i j : Fin 4) (h : i ≠ j)
    (v : Fin 4 → A) (hu : IsUnit (v i)) :
    (unitPairNormalizer i j h v hu • v) j = 0 := by
  let t := Matrix.SpecialLinearGroup.transvection h.symm
    ((↑hu.unit⁻¹ : A) * (1 - v j))
  let s := Matrix.SpecialLinearGroup.transvection h (1 - v i)
  have htj : (t • v) j = 1 := by
    change (Matrix.SpecialLinearGroup.transvection h.symm
      ((↑hu.unit⁻¹ : A) * (1 - v j)) • v) j = 1
    rw [transvection_smul_same]
    calc
      v j + ((↑hu.unit⁻¹ : A) * (1 - v j)) * v i =
          v j + (1 - v j) * ((↑hu.unit⁻¹ : A) * v i) := by ring
      _ = 1 := by rw [hu.val_inv_mul]; ring
  have hti : (t • v) i = v i :=
    transvection_smul_other j i i h.symm h _ v
  have hsi : (s • (t • v)) i = 1 := by
    change (Matrix.SpecialLinearGroup.transvection h (1 - v i) •
      (t • v)) i = 1
    rw [transvection_smul_same, hti, htj]
    ring
  have hsj : (s • (t • v)) j = 1 := by
    change (Matrix.SpecialLinearGroup.transvection h (1 - v i) •
      (t • v)) j = 1
    rw [transvection_smul_other i j j h h.symm, htj]
  unfold unitPairNormalizer
  rw [mul_smul, mul_smul, transvection_smul_same]
  change (s • (t • v)) j + (-1 : A) * (s • (t • v)) i = 0
  rw [hsj, hsi]
  ring

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem unitPairNormalizer_smul_other (i j k : Fin 4) (h : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j)
    (v : Fin 4 → A) (hu : IsUnit (v i)) :
    (unitPairNormalizer i j h v hu • v) k = v k := by
  unfold unitPairNormalizer
  rw [mul_smul, mul_smul,
    transvection_smul_other j i k h.symm hkj,
    transvection_smul_other i j k h hki,
    transvection_smul_other j i k h.symm hkj]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem unit_first_elementary_reduce
    (v : Fin 4 → A) (hu : IsUnit (v 0)) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 4) A,
      g ∈ localElementarySubgroup A ∧
        g • v = Pi.single 0 1 := by
  let p : Matrix.SpecialLinearGroup (Fin 4) A :=
    unitPairNormalizer (0 : Fin 4) 1 (by decide) v hu
  let t₂ : Matrix.SpecialLinearGroup (Fin 4) A :=
    Matrix.SpecialLinearGroup.transvection
      (show (2 : Fin 4) ≠ 0 by decide) (-v 2)
  let t₃ : Matrix.SpecialLinearGroup (Fin 4) A :=
    Matrix.SpecialLinearGroup.transvection
      (show (3 : Fin 4) ≠ 0 by decide) (-v 3)
  refine ⟨t₃ * t₂ * p,
    (localElementarySubgroup A).mul_mem
      ((localElementarySubgroup A).mul_mem
        (transvection_mem 3 0 (by decide) (-v 3))
        (transvection_mem 2 0 (by decide) (-v 2)))
      (unitPairNormalizer_mem 0 1 (by decide) v hu), ?_⟩
  funext k
  fin_cases k
  · dsimp [t₃, t₂, p]
    rw [mul_smul, mul_smul,
      transvection_smul_other 3 0 0 (by decide) (by decide),
      transvection_smul_other 2 0 0 (by decide) (by decide),
      unitPairNormalizer_smul_pivot]
    simp only [Fin.isValue, Pi.single_eq_same]
  · dsimp [t₃, t₂, p]
    rw [mul_smul, mul_smul,
      transvection_smul_other 3 0 1 (by decide) (by decide),
      transvection_smul_other 2 0 1 (by decide) (by decide),
      unitPairNormalizer_smul_auxiliary]
    simp only [Fin.isValue, ne_eq, one_ne_zero, not_false_eq_true, Pi.single_eq_of_ne]
  · dsimp [t₃, t₂, p]
    rw [mul_smul, mul_smul,
      transvection_smul_other 3 0 2 (by decide) (by decide),
      transvection_smul_same,
      unitPairNormalizer_smul_other 0 1 2 (by decide)
        (by decide) (by decide),
      unitPairNormalizer_smul_pivot]
    simp only [Fin.isValue, mul_one, add_neg_cancel, ne_eq, Fin.reduceEq, not_false_eq_true,
      Pi.single_eq_of_ne]
  · dsimp [t₃, t₂, p]
    rw [mul_smul, mul_smul,
      transvection_smul_same,
      transvection_smul_other 2 0 3 (by decide) (by decide),
      transvection_smul_other 2 0 0 (by decide) (by decide),
      unitPairNormalizer_smul_other 0 1 3 (by decide)
        (by decide) (by decide),
      unitPairNormalizer_smul_pivot]
    simp only [Fin.isValue, mul_one, add_neg_cancel, ne_eq, Fin.reduceEq, not_false_eq_true,
      Pi.single_eq_of_ne]

end LocalElementaryProof

namespace MonicMatrixElimination

open Matrix
open scoped BigOperators

universe u

variable {R : Type u} [CommRing R]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def lowerBlockMatrix (b : Matrix (Fin 3) (Fin 3) R) :
    Matrix (Fin 4) (Fin 4) R :=
  fun i j =>
    Fin.cases (Fin.cases 1 (fun _ => 0) j)
      (fun i' => Fin.cases 0 (fun j' => b i' j') j) i

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem lowerBlockMatrix_zero_zero
    (b : Matrix (Fin 3) (Fin 3) R) :
    lowerBlockMatrix b 0 0 = 1 := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem lowerBlockMatrix_succ_zero
    (b : Matrix (Fin 3) (Fin 3) R) (i : Fin 3) :
    lowerBlockMatrix b i.succ 0 = 0 := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem lowerBlockMatrix_zero_succ
    (b : Matrix (Fin 3) (Fin 3) R) (j : Fin 3) :
    lowerBlockMatrix b 0 j.succ = 0 := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem lowerBlockMatrix_succ_succ
    (b : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) :
    lowerBlockMatrix b i.succ j.succ = b i j := rfl









/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem lowerBlockMatrix_det (b : Matrix (Fin 3) (Fin 3) R) :
    (lowerBlockMatrix b).det = b.det := by
  rw [Matrix.det_succ_column_zero]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, lowerBlockMatrix, Fin.isValue, Fin.cases_zero,
    submatrix, Fin.cases_succ, Fin.sum_univ_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero,
    mul_one, Fin.zero_succAbove, one_mul, Fin.val_succ, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero]
  congr 1

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def lowerBlockSpecialLinear
    (b : Matrix.SpecialLinearGroup (Fin 3) R) :
    Matrix.SpecialLinearGroup (Fin 4) R :=
  ⟨lowerBlockMatrix b.val, by
    rw [lowerBlockMatrix_det]
    exact b.property⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def firstRowClear
    (g : Matrix.SpecialLinearGroup (Fin 4) R) :
    Matrix.SpecialLinearGroup (Fin 4) R :=
  Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 4) ≠ 1 by decide) (-(g 0 1)) *
    Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 4) ≠ 2 by decide) (-(g 0 2)) *
    Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 4) ≠ 3 by decide) (-(g 0 3))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem firstRowClear_mem
    (g : Matrix.SpecialLinearGroup (Fin 4) R) :
    firstRowClear g ∈ localGlobalElementarySubgroup R := by
  unfold firstRowClear
  exact (localGlobalElementarySubgroup R).mul_mem
    ((localGlobalElementarySubgroup R).mul_mem
      (localGlobal_transvection_mem 0 1 (by decide) (-(g 0 1)))
      (localGlobal_transvection_mem 0 2 (by decide) (-(g 0 2))))
    (localGlobal_transvection_mem 0 3 (by decide) (-(g 0 3)))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem firstRowClear_mul_apply
    (g : Matrix.SpecialLinearGroup (Fin 4) R)
    (hcolumn : ∀ i : Fin 4, g i 0 = if i = 0 then 1 else 0)
    (i j : Fin 4) :
    (g * firstRowClear g) i j =
      if i = 0 then if j = 0 then 1 else 0 else g i j := by
  have h0 := hcolumn 0
  have h1 := hcolumn 1
  have h2 := hcolumn 2
  have h3 := hcolumn 3
  change
    (g.val *
      (Matrix.transvection (0 : Fin 4) 1 (-(g 0 1)) *
        Matrix.transvection (0 : Fin 4) 2 (-(g 0 2)) *
        Matrix.transvection (0 : Fin 4) 3 (-(g 0 3)))) i j = _
  simp only [← mul_assoc]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_transvection_apply_same,
      Matrix.mul_transvection_apply_of_ne, h0, h1, h2, h3]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem lowerRight_det_eq_one
    (g : Matrix.SpecialLinearGroup (Fin 4) R)
    (hcolumn : ∀ i : Fin 4, g i 0 = if i = 0 then 1 else 0) :
    (g.val.submatrix Fin.succ Fin.succ).det = 1 := by
  have hdet := g.property
  rw [Matrix.det_succ_column_zero] at hdet
  have h0 := hcolumn 0
  have h1 := hcolumn 1
  have h2 := hcolumn 2
  have h3 := hcolumn 3
  simpa only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.sum_univ_succ,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero, h0, ↓reduceIte, mul_one, Fin.succAbove_zero,
    one_mul, Fin.val_succ, zero_add, pow_one, Fin.succ_zero_eq_one, h1, one_ne_zero, mul_zero,
    zero_mul, even_two, Even.neg_pow, one_pow, Fin.succ_one_eq_two, h2, Fin.reduceEq,
    Finset.univ_unique, Fin.default_eq_zero, Fin.val_eq_zero, Finset.sum_singleton, Fin.reduceSucc,
    h3, add_zero] using hdet

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def lowerRightSpecialLinear
    (g : Matrix.SpecialLinearGroup (Fin 4) R)
    (hcolumn : ∀ i : Fin 4, g i 0 = if i = 0 then 1 else 0) :
    Matrix.SpecialLinearGroup (Fin 3) R :=
  ⟨g.val.submatrix Fin.succ Fin.succ,
    lowerRight_det_eq_one g hcolumn⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem firstColumn_block_decomposition
    (g : Matrix.SpecialLinearGroup (Fin 4) R)
    (hcolumn : ∀ i : Fin 4, g i 0 = if i = 0 then 1 else 0) :
    g * firstRowClear g =
      lowerBlockSpecialLinear (lowerRightSpecialLinear g hcolumn) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [firstRowClear_mul_apply g hcolumn]
  change (if i = 0 then if j = 0 then 1 else 0 else g i j) =
    lowerBlockMatrix (g.val.submatrix Fin.succ Fin.succ) i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [Matrix.submatrix, hcolumn]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem firstColumn_mem_elementary_iff_block
    (g : Matrix.SpecialLinearGroup (Fin 4) R)
    (hcolumn : ∀ i : Fin 4, g i 0 = if i = 0 then 1 else 0) :
    g ∈ localGlobalElementarySubgroup R ↔
      lowerBlockSpecialLinear (lowerRightSpecialLinear g hcolumn) ∈
        localGlobalElementarySubgroup R := by
  rw [← firstColumn_block_decomposition g hcolumn]
  constructor
  · intro hg
    exact (localGlobalElementarySubgroup R).mul_mem hg (firstRowClear_mem g)
  · intro hg
    have h := (localGlobalElementarySubgroup R).mul_mem hg
      ((localGlobalElementarySubgroup R).inv_mem (firstRowClear_mem g))
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using h

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem specialLinear_mem_elementary_of_column_reduction
    (g e : Matrix.SpecialLinearGroup (Fin 4) R)
    (he : e ∈ localGlobalElementarySubgroup R)
    (hcolumn : e • (fun i : Fin 4 => g i 0) = Pi.single 0 1)
    (hblock :
      lowerBlockSpecialLinear
        (lowerRightSpecialLinear (e * g) (by
          intro i
          change (e • (fun j : Fin 4 => g j 0)) i = _
          rw [hcolumn]
          simp only [Fin.isValue, Pi.single_apply])) ∈
        localGlobalElementarySubgroup R) :
    g ∈ localGlobalElementarySubgroup R := by
  have hnormalized : e * g ∈ localGlobalElementarySubgroup R :=
    (firstColumn_mem_elementary_iff_block (e * g) (by
      intro i
      change (e • (fun j : Fin 4 => g j 0)) i = _
      rw [hcolumn]
      simp only [Fin.isValue, Pi.single_apply])).2 hblock
  have h := (localGlobalElementarySubgroup R).mul_mem
    ((localGlobalElementarySubgroup R).inv_mem he) hnormalized
  simpa only [inv_mul_cancel_left] using h

end MonicMatrixElimination

namespace StabilizedBlockReduction

open Matrix
open MonicMatrixElimination

universe u

variable {R : Type u} [CommRing R]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def ElementaryFirstColumnTransitivity (R : Type u) [CommRing R] : Prop :=
  ∀ g : Matrix.SpecialLinearGroup (Fin 4) R,
    ∃ e : Matrix.SpecialLinearGroup (Fin 4) R,
      e ∈ localGlobalElementarySubgroup R ∧
        e • (fun i : Fin 4 => g i 0) = Pi.single 0 1

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def StabilizedThreeElementaryGeneration (R : Type u) [CommRing R] : Prop :=
  ∀ b : Matrix.SpecialLinearGroup (Fin 3) R,
    lowerBlockSpecialLinear b ∈ localGlobalElementarySubgroup R

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem lowerBlockSpecialLinear_one :
    lowerBlockSpecialLinear (1 : Matrix.SpecialLinearGroup (Fin 3) R) =
      (1 : Matrix.SpecialLinearGroup (Fin 4) R) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [lowerBlockSpecialLinear, Matrix.one_apply, eq_comm]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem lowerBlockSpecialLinear_mul
    (b c : Matrix.SpecialLinearGroup (Fin 3) R) :
    lowerBlockSpecialLinear (b * c) =
      lowerBlockSpecialLinear b * lowerBlockSpecialLinear c := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change lowerBlockMatrix
      ((b * c : Matrix.SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) i j =
    (lowerBlockMatrix (b : Matrix (Fin 3) (Fin 3) R) *
      lowerBlockMatrix (c : Matrix (Fin 3) (Fin 3) R)) i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [Matrix.mul_apply,
      Fin.sum_univ_succ, lowerBlockMatrix]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def lowerBlockHom :
    Matrix.SpecialLinearGroup (Fin 3) R →*
      Matrix.SpecialLinearGroup (Fin 4) R where
  toFun := lowerBlockSpecialLinear
  map_one' := lowerBlockSpecialLinear_one
  map_mul' := lowerBlockSpecialLinear_mul

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem lowerBlockHom_transvection (i j : Fin 3) (h : i ≠ j) (r : R) :
    lowerBlockHom
        (Matrix.SpecialLinearGroup.transvection h r) =
      Matrix.SpecialLinearGroup.transvection
        (show i.succ ≠ j.succ by
          exact fun hs => h (Fin.succ_inj.mp hs)) r := by
  apply Matrix.SpecialLinearGroup.ext
  intro p q
  cases p using Fin.cases <;> cases q using Fin.cases <;>
    simp [lowerBlockHom, lowerBlockSpecialLinear,
      Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.single_apply, Matrix.one_apply, eq_comm]





/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem finTwoPlusOne_symm_two :
    (finSumFinEquiv (m := 2) (n := 1)).symm (2 : Fin 3) =
      Sum.inr (0 : Fin 1) := by
  decide

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def stabilizedTwoMatrix (b : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin 3) (Fin 3) R :=
  Matrix.reindex (finSumFinEquiv (m := 2) (n := 1))
    (finSumFinEquiv (m := 2) (n := 1))
    (Matrix.fromBlocks b 0 0 (1 : Matrix (Fin 1) (Fin 1) R))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem stabilizedTwoMatrix_castSucc_castSucc
    (b : Matrix (Fin 2) (Fin 2) R) (i j : Fin 2) :
    stabilizedTwoMatrix b i.castSucc j.castSucc = b i j := by
  simp only [stabilizedTwoMatrix, Nat.reduceAdd, fromBlocks, reindex_apply, submatrix_apply,
    finSumFinEquiv_symm_apply_castSucc, of_apply, Sum.elim_inl]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem stabilizedTwoMatrix_castSucc_last
    (b : Matrix (Fin 2) (Fin 2) R) (i : Fin 2) :
    stabilizedTwoMatrix b i.castSucc (Fin.last 2) = 0 := by
  simp only [stabilizedTwoMatrix, Nat.reduceAdd, fromBlocks, Fin.reduceLast, reindex_apply,
    Fin.isValue, submatrix_apply, finSumFinEquiv_symm_apply_castSucc, finTwoPlusOne_symm_two,
    of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem stabilizedTwoMatrix_last_castSucc
    (b : Matrix (Fin 2) (Fin 2) R) (j : Fin 2) :
    stabilizedTwoMatrix b (Fin.last 2) j.castSucc = 0 := by
  simp only [stabilizedTwoMatrix, Nat.reduceAdd, fromBlocks, Fin.reduceLast, reindex_apply,
    Fin.isValue, submatrix_apply, finTwoPlusOne_symm_two, finSumFinEquiv_symm_apply_castSucc,
    of_apply, Sum.elim_inr, Sum.elim_inl, Matrix.zero_apply]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem stabilizedTwoMatrix_last_last
    (b : Matrix (Fin 2) (Fin 2) R) :
    stabilizedTwoMatrix b (Fin.last 2) (Fin.last 2) = 1 := by
  simp only [stabilizedTwoMatrix, Nat.reduceAdd, fromBlocks, Fin.reduceLast, reindex_apply,
    Fin.isValue, submatrix_apply, finTwoPlusOne_symm_two, of_apply, Sum.elim_inr, one_apply_eq]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem stabilizedTwoMatrix_det
    (b : Matrix (Fin 2) (Fin 2) R) :
    (stabilizedTwoMatrix b).det = b.det := by
  unfold stabilizedTwoMatrix
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def stabilizedTwoSpecialLinear
    (b : Matrix.SpecialLinearGroup (Fin 2) R) :
    Matrix.SpecialLinearGroup (Fin 3) R :=
  ⟨stabilizedTwoMatrix b.val, by
    rw [stabilizedTwoMatrix_det]
    exact b.property⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem stabilizedTwoSpecialLinear_castSucc_castSucc
    (b : Matrix.SpecialLinearGroup (Fin 2) R) (i j : Fin 2) :
    stabilizedTwoSpecialLinear b i.castSucc j.castSucc = b i j :=
  stabilizedTwoMatrix_castSucc_castSucc b.val i j

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem stabilizedTwoSpecialLinear_castSucc_last
    (b : Matrix.SpecialLinearGroup (Fin 2) R) (i : Fin 2) :
    stabilizedTwoSpecialLinear b i.castSucc (Fin.last 2) = 0 :=
  stabilizedTwoMatrix_castSucc_last b.val i

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem stabilizedTwoSpecialLinear_last_castSucc
    (b : Matrix.SpecialLinearGroup (Fin 2) R) (j : Fin 2) :
    stabilizedTwoSpecialLinear b (Fin.last 2) j.castSucc = 0 :=
  stabilizedTwoMatrix_last_castSucc b.val j

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem stabilizedTwoSpecialLinear_last_last
    (b : Matrix.SpecialLinearGroup (Fin 2) R) :
    stabilizedTwoSpecialLinear b (Fin.last 2) (Fin.last 2) = 1 :=
  stabilizedTwoMatrix_last_last b.val

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem finTwo_castSucc_ne_two (i : Fin 2) :
    i.castSucc ≠ (2 : Fin 3) :=
  Fin.castSucc_ne_last i

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem stabilizedTwoSpecialLinear_castSucc_two
    (b : Matrix.SpecialLinearGroup (Fin 2) R) (i : Fin 2) :
    stabilizedTwoSpecialLinear b i.castSucc (2 : Fin 3) = 0 :=
  stabilizedTwoSpecialLinear_castSucc_last b i

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem stabilizedTwoSpecialLinear_two_castSucc
    (b : Matrix.SpecialLinearGroup (Fin 2) R) (i : Fin 2) :
    stabilizedTwoSpecialLinear b (2 : Fin 3) i.castSucc = 0 :=
  stabilizedTwoSpecialLinear_last_castSucc b i

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem stabilizedTwoSpecialLinear_two_two
    (b : Matrix.SpecialLinearGroup (Fin 2) R) :
    stabilizedTwoSpecialLinear b (2 : Fin 3) (2 : Fin 3) = 1 :=
  stabilizedTwoSpecialLinear_last_last b

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem stabilizedTwoSpecialLinear_one :
    stabilizedTwoSpecialLinear
        (1 : Matrix.SpecialLinearGroup (Fin 2) R) =
      (1 : Matrix.SpecialLinearGroup (Fin 3) R) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
    simp [Matrix.one_apply, eq_comm]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem stabilizedTwoSpecialLinear_mul
    (b c : Matrix.SpecialLinearGroup (Fin 2) R) :
    stabilizedTwoSpecialLinear (b * c) =
      stabilizedTwoSpecialLinear b * stabilizedTwoSpecialLinear c := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def stabilizedTwoHom :
    Matrix.SpecialLinearGroup (Fin 2) R →*
      Matrix.SpecialLinearGroup (Fin 3) R where
  toFun := stabilizedTwoSpecialLinear
  map_one' := stabilizedTwoSpecialLinear_one
  map_mul' := stabilizedTwoSpecialLinear_mul

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem stabilizedTwoHom_castSucc_castSucc
    (b : Matrix.SpecialLinearGroup (Fin 2) R) (i j : Fin 2) :
    stabilizedTwoHom b i.castSucc j.castSucc = b i j :=
  stabilizedTwoSpecialLinear_castSucc_castSucc b i j







/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem stabilizedTwoHom_castSucc_two
    (b : Matrix.SpecialLinearGroup (Fin 2) R) (i : Fin 2) :
    stabilizedTwoHom b i.castSucc (2 : Fin 3) = 0 :=
  stabilizedTwoSpecialLinear_castSucc_two b i

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem stabilizedTwoHom_two_castSucc
    (b : Matrix.SpecialLinearGroup (Fin 2) R) (i : Fin 2) :
    stabilizedTwoHom b (2 : Fin 3) i.castSucc = 0 :=
  stabilizedTwoSpecialLinear_two_castSucc b i

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem stabilizedTwoHom_two_two
    (b : Matrix.SpecialLinearGroup (Fin 2) R) :
    stabilizedTwoHom b (2 : Fin 3) (2 : Fin 3) = 1 :=
  stabilizedTwoSpecialLinear_two_two b

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem stabilizedTwoHom_transvection
    (i j : Fin 2) (h : i ≠ j) (r : R) :
    stabilizedTwoHom (Matrix.SpecialLinearGroup.transvection h r) =
      Matrix.SpecialLinearGroup.transvection
        (show i.castSucc ≠ j.castSucc by
          exact fun hs => h (Fin.castSucc_inj.mp hs)) r := by
  apply Matrix.SpecialLinearGroup.ext
  intro p q
  cases p using Fin.lastCases <;> cases q using Fin.lastCases <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.single_apply, Matrix.one_apply, eq_comm]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def elementaryThreeSubgroup (R : Type u) [CommRing R] :
    Subgroup (Matrix.SpecialLinearGroup (Fin 3) R) :=
  Subgroup.closure
    {g | ∃ (i j : Fin 3) (h : i ≠ j) (r : R),
      g = Matrix.SpecialLinearGroup.transvection h r}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem stabilizedTwoHom_transvection_mem
    (i j : Fin 2) (h : i ≠ j) (r : R) :
    stabilizedTwoHom (Matrix.SpecialLinearGroup.transvection h r) ∈
      elementaryThreeSubgroup R := by
  rw [stabilizedTwoHom_transvection]
  exact Subgroup.subset_closure
    ⟨i.castSucc, j.castSucc,
      fun hs => h (Fin.castSucc_inj.mp hs), r, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem map_elementaryThreeSubgroup_le :
    (elementaryThreeSubgroup R).map lowerBlockHom ≤
      localGlobalElementarySubgroup R := by
  unfold elementaryThreeSubgroup
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨i, j, h, r, rfl⟩, rfl⟩
  rw [lowerBlockHom_transvection]
  exact localGlobal_transvection_mem i.succ j.succ
    (fun hs => h (Fin.succ_inj.mp hs)) r

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem lowerBlock_mem_of_elementaryThree
    (b : Matrix.SpecialLinearGroup (Fin 3) R)
    (hb : b ∈ elementaryThreeSubgroup R) :
    lowerBlockSpecialLinear b ∈ localGlobalElementarySubgroup R :=
  map_elementaryThreeSubgroup_le ⟨b, hb, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem elementary_eq_top_iff_columnTransitivity_and_stabilizedThree :
    localGlobalElementarySubgroup R = ⊤ ↔
      ElementaryFirstColumnTransitivity R ∧
        StabilizedThreeElementaryGeneration R := by
  constructor
  · intro htop
    constructor
    · intro g
      refine ⟨g⁻¹, ?_, ?_⟩
      · rw [htop]
        trivial
      · funext i
        change (g⁻¹ * g) i 0 = _
        rw [inv_mul_cancel]
        simp only [Fin.isValue, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply,
          Pi.single_apply]
    · intro b
      rw [htop]
      trivial
  · rintro ⟨hcolumn, hblock⟩
    apply top_unique
    intro g _
    obtain ⟨e, he, hfirst⟩ := hcolumn g
    exact specialLinear_mem_elementary_of_column_reduction g e he hfirst
      (hblock _)

end StabilizedBlockReduction

namespace StabilizedBlockReduction

open Matrix

universe u

variable {R : Type u} [CommRing R]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem elementaryThree_transvection_mem
    (i j : Fin 3) (h : i ≠ j) (r : R) :
    Matrix.SpecialLinearGroup.transvection h r ∈
      elementaryThreeSubgroup R :=
  Subgroup.subset_closure ⟨i, j, h, r, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem elementaryThree_transvection_smul_same
    (i j : Fin 3) (h : i ≠ j) (r : R) (v : Fin 3 → R) :
    (Matrix.SpecialLinearGroup.transvection h r • v) i =
      v i + r * v j := by
  change ((Matrix.SpecialLinearGroup.transvection h r).val *ᵥ v) i = _
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec,
    Matrix.one_mulVec, Matrix.single_mulVec]
  simp only [Pi.add_apply, Function.update_self]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem elementaryThree_transvection_smul_other
    (i j k : Fin 3) (h : i ≠ j) (hk : k ≠ i)
    (r : R) (v : Fin 3 → R) :
    (Matrix.SpecialLinearGroup.transvection h r • v) k = v k := by
  change ((Matrix.SpecialLinearGroup.transvection h r).val *ᵥ v) k = _
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec,
    Matrix.one_mulVec, Matrix.single_mulVec]
  simp only [Pi.add_apply, ne_eq, hk, not_false_eq_true, Function.update_of_ne, Pi.zero_apply,
    add_zero]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem elementaryThree_coprime_pair_reduce
    (v : Fin 3 → R) (hcoprime : IsCoprime (v 0) (v 1)) :
    ∃ e : Matrix.SpecialLinearGroup (Fin 3) R,
      e ∈ elementaryThreeSubgroup R ∧ e • v = Pi.single 0 1 := by
  obtain ⟨a, b, hab⟩ := hcoprime
  let t₀ : Matrix.SpecialLinearGroup (Fin 3) R :=
    Matrix.SpecialLinearGroup.transvection
      (show (2 : Fin 3) ≠ 0 by decide) ((1 - v 2) * a)
  let t₁ : Matrix.SpecialLinearGroup (Fin 3) R :=
    Matrix.SpecialLinearGroup.transvection
      (show (2 : Fin 3) ≠ 1 by decide) ((1 - v 2) * b)
  let p : Matrix.SpecialLinearGroup (Fin 3) R :=
    Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 3) ≠ 2 by decide) (1 - v 0)
  let q : Matrix.SpecialLinearGroup (Fin 3) R :=
    Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 3) ≠ 0 by decide) (-(v 1))
  let r : Matrix.SpecialLinearGroup (Fin 3) R :=
    Matrix.SpecialLinearGroup.transvection
      (show (2 : Fin 3) ≠ 0 by decide) (-1)
  let t := t₁ * t₀
  have ht₀ : (t • v) 0 = v 0 := by
    dsimp [t, t₀, t₁]
    rw [mul_smul,
      elementaryThree_transvection_smul_other 2 1 0 (by decide) (by decide),
      elementaryThree_transvection_smul_other 2 0 0 (by decide) (by decide)]
  have ht₁ : (t • v) 1 = v 1 := by
    dsimp [t, t₀, t₁]
    rw [mul_smul,
      elementaryThree_transvection_smul_other 2 1 1 (by decide) (by decide),
      elementaryThree_transvection_smul_other 2 0 1 (by decide) (by decide)]
  have ht₂ : (t • v) 2 = 1 := by
    dsimp [t, t₀, t₁]
    rw [mul_smul,
      elementaryThree_transvection_smul_same,
      elementaryThree_transvection_smul_same,
      elementaryThree_transvection_smul_other 2 0 1
        (by decide) (by decide)]
    calc
      v 2 + ((1 - v 2) * a) * v 0 +
          ((1 - v 2) * b) * v 1 =
        v 2 + (1 - v 2) * (a * v 0 + b * v 1) := by ring
      _ = 1 := by rw [hab]; ring
  have hp₀ : (p • (t • v)) 0 = 1 := by
    dsimp [p]
    rw [elementaryThree_transvection_smul_same, ht₀, ht₂]
    ring
  have hp₁ : (p • (t • v)) 1 = v 1 := by
    dsimp [p]
    rw [elementaryThree_transvection_smul_other 0 2 1
      (by decide) (by decide), ht₁]
  have hp₂ : (p • (t • v)) 2 = 1 := by
    dsimp [p]
    rw [elementaryThree_transvection_smul_other 0 2 2
      (by decide) (by decide), ht₂]
  have hq₀ : (q • (p • (t • v))) 0 = 1 := by
    dsimp [q]
    rw [elementaryThree_transvection_smul_other 1 0 0
      (by decide) (by decide), hp₀]
  have hq₁ : (q • (p • (t • v))) 1 = 0 := by
    dsimp [q]
    rw [elementaryThree_transvection_smul_same, hp₁, hp₀]
    ring
  have hq₂ : (q • (p • (t • v))) 2 = 1 := by
    dsimp [q]
    rw [elementaryThree_transvection_smul_other 1 0 2
      (by decide) (by decide), hp₂]
  refine ⟨r * q * p * t, ?_, ?_⟩
  · exact (elementaryThreeSubgroup R).mul_mem
      ((elementaryThreeSubgroup R).mul_mem
        ((elementaryThreeSubgroup R).mul_mem
          (elementaryThree_transvection_mem 2 0 (by decide) (-1))
          (elementaryThree_transvection_mem 1 0 (by decide) (-(v 1))))
        (elementaryThree_transvection_mem 0 2 (by decide) (1 - v 0)))
      ((elementaryThreeSubgroup R).mul_mem
        (elementaryThree_transvection_mem 2 1 (by decide) ((1 - v 2) * b))
        (elementaryThree_transvection_mem 2 0 (by decide) ((1 - v 2) * a)))
  · funext i
    fin_cases i
    · simp only [mul_smul, Pi.single_apply]
      dsimp [r]
      rw [elementaryThree_transvection_smul_other 2 0 0
        (by decide) (by decide), hq₀]
    · simp only [mul_smul, Pi.single_apply]
      dsimp [r]
      rw [elementaryThree_transvection_smul_other 2 0 1
        (by decide) (by decide), hq₁]
    · simp only [mul_smul, Pi.single_apply]
      dsimp [r]
      rw [elementaryThree_transvection_smul_same, hq₂, hq₀]
      simp only [mul_one, add_neg_cancel]

end StabilizedBlockReduction

end

section

namespace FieldPolynomialElementaryThree

open Matrix
open StabilizedBlockReduction

variable {R : Type*} [EuclideanDomain R]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev G (R : Type*) [EuclideanDomain R] :=
  Matrix.SpecialLinearGroup (Fin 3) R

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def rotation (i j : Fin 3) (h : i ≠ j) : G R :=
  Matrix.SpecialLinearGroup.transvection h 1 *
    Matrix.SpecialLinearGroup.transvection h.symm (-1) *
    Matrix.SpecialLinearGroup.transvection h 1

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem rotation_mem (i j : Fin 3) (h : i ≠ j) :
    rotation (R := R) i j h ∈ elementaryThreeSubgroup R :=
  (elementaryThreeSubgroup R).mul_mem
    ((elementaryThreeSubgroup R).mul_mem
      (elementaryThree_transvection_mem i j h 1)
      (elementaryThree_transvection_mem j i h.symm (-1)))
    (elementaryThree_transvection_mem i j h 1)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem rotation_left (i j : Fin 3) (h : i ≠ j)
    (v : Fin 3 → R) :
    (rotation (R := R) i j h • v) i = v j := by
  simp only [rotation, mul_smul]
  rw [elementaryThree_transvection_smul_same,
    elementaryThree_transvection_smul_other j i i h.symm h,
    elementaryThree_transvection_smul_same,
    elementaryThree_transvection_smul_same,
    elementaryThree_transvection_smul_other i j j h h.symm]
  rw [elementaryThree_transvection_smul_same]
  ring

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem rotation_right (i j : Fin 3) (h : i ≠ j)
    (v : Fin 3 → R) :
    (rotation (R := R) i j h • v) j = -v i := by
  simp only [rotation, mul_smul]
  rw [elementaryThree_transvection_smul_other i j j h h.symm,
    elementaryThree_transvection_smul_same,
    elementaryThree_transvection_smul_same,
    elementaryThree_transvection_smul_other i j j h h.symm]
  ring

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem rotation_other (i j k : Fin 3) (h : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) (v : Fin 3 → R) :
    (rotation (R := R) i j h • v) k = v k := by
  simp only [rotation, mul_smul]
  rw [elementaryThree_transvection_smul_other i j k h hki,
    elementaryThree_transvection_smul_other j i k h.symm hkj,
    elementaryThree_transvection_smul_other i j k h hki]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def step (i j : Fin 3) (h : i ≠ j) (a b : R) : G R :=
  rotation (R := R) i j h *
    Matrix.SpecialLinearGroup.transvection h.symm (-(b / a))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem step_mem (i j : Fin 3) (h : i ≠ j) (a b : R) :
    step (R := R) i j h a b ∈ elementaryThreeSubgroup R :=
  (elementaryThreeSubgroup R).mul_mem (rotation_mem i j h)
    (elementaryThree_transvection_mem j i h.symm (-(b / a)))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem step_left (i j : Fin 3) (h : i ≠ j)
    (v : Fin 3 → R) :
    (step (R := R) i j h (v i) (v j) • v) i = v j % v i := by
  rw [step, mul_smul, rotation_left,
    elementaryThree_transvection_smul_same]
  have hd := EuclideanDomain.div_add_mod (v j) (v i)
  conv_lhs =>
    lhs
    rw [← hd]
  ring

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem step_right (i j : Fin 3) (h : i ≠ j)
    (v : Fin 3 → R) :
    (step (R := R) i j h (v i) (v j) • v) j = -(v i) := by
  rw [step, mul_smul, rotation_right,
    elementaryThree_transvection_smul_other _ _ _ h.symm h]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem step_other (i j k : Fin 3) (h : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) (v : Fin 3 → R) :
    (step (R := R) i j h (v i) (v j) • v) k = v k := by
  rw [step, mul_smul, rotation_other i j k h hki hkj,
    elementaryThree_transvection_smul_other _ _ _ h.symm hkj]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem euclideanThree_pair_reduce
    (i j : Fin 3) (h : i ≠ j) (v : Fin 3 → R) :
    ∃ g : G R, g ∈ elementaryThreeSubgroup R ∧
      (g • v) j = 0 ∧
      ∀ k : Fin 3, k ≠ i → k ≠ j → (g • v) k = v k := by
  let P : R → Prop := fun a => ∀ (b : R) (w : Fin 3 → R),
    w i = a → w j = b →
      ∃ g : G R, g ∈ elementaryThreeSubgroup R ∧
        (g • w) j = 0 ∧
        ∀ k : Fin 3, k ≠ i → k ≠ j → (g • w) k = w k
  have hp : ∀ a : R, P a := by
    intro a
    induction a using (EuclideanDomain.r_wellFounded (R := R)).induction with
    | h a ih =>
      intro b w hwi hwj
      by_cases ha : a = 0
      · refine ⟨rotation i j h, rotation_mem i j h, ?_, ?_⟩
        · rw [rotation_right, hwi, ha, neg_zero]
        · exact fun k hki hkj => rotation_other i j k h hki hkj w
      · let s := step i j h a b
        have hs : s ∈ elementaryThreeSubgroup R := step_mem i j h a b
        have hsi : (s • w) i = b % a := by
          dsimp [s]
          subst a
          subst b
          exact step_left i j h w
        have hsj : (s • w) j = -a := by
          dsimp [s]
          subst a
          subst b
          exact step_right i j h w
        obtain ⟨g, hg, hgj, hgother⟩ :=
          ih (b % a) (EuclideanDomain.mod_lt b ha) (-a) (s • w) hsi hsj
        refine ⟨g * s, (elementaryThreeSubgroup R).mul_mem hg hs, ?_, ?_⟩
        · rw [mul_smul, hgj]
        · intro k hki hkj
          rw [mul_smul, hgother k hki hkj]
          dsimp [s]
          subst a
          subst b
          exact step_other i j k h hki hkj w
  exact hp (v i) (v j) v rfl rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem euclideanThree_reduce_last_preserving_first
    (v : Fin 3 → R) :
    ∃ g : G R, g ∈ elementaryThreeSubgroup R ∧
      (g • v) 2 = 0 ∧ (g • v) 0 = v 0 := by
  obtain ⟨g, hg, hzero, hfix⟩ :=
    euclideanThree_pair_reduce (1 : Fin 3) 2 (by decide) v
  exact ⟨g, hg, hzero, hfix 0 (by decide) (by decide)⟩

end FieldPolynomialElementaryThree

open Matrix
open StabilizedBlockReduction
open scoped BigOperators

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem unimodularRow_smul_specialLinear_three
    {R : Type*} [CommRing R]
    (e : Matrix.SpecialLinearGroup (Fin 3) R)
    (v : Fin 3 → R) (hv : UnimodularRow v) :
    UnimodularRow (e • v) := by
  rw [unimodularRow_iff_avoids_maximalIdeals] at hv ⊢
  intro M hM
  obtain ⟨j, hj⟩ := hv M hM
  by_contra hnone
  push Not at hnone
  apply hj
  have hback : v j = (e⁻¹ • (e • v)) j := by simp only [inv_smul_smul]
  rw [hback]
  change ∑ k : Fin 3, (e⁻¹) j k * (e • v) k ∈ M
  exact M.sum_mem fun k _ => M.mul_mem_left _ (hnone k)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem unimodularThree_isCoprime_of_last_zero
    {R : Type*} [CommRing R]
    (v : Fin 3 → R) (hv : UnimodularRow v) (hz : v 2 = 0) :
    IsCoprime (v 0) (v 1) := by
  obtain ⟨r, hr⟩ := hv
  refine ⟨r 0, r 1, ?_⟩
  simpa only [Fin.isValue, Fin.sum_univ_succ, Fin.succ_zero_eq_one, Finset.univ_unique,
    Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_one_eq_two, hz, mul_zero, add_zero] using hr

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem euclideanElementaryThree_unimodular_reduce
    {R : Type*} [EuclideanDomain R]
    (v : Fin 3 → R) (hv : UnimodularRow v) :
    ∃ e : Matrix.SpecialLinearGroup (Fin 3) R,
      e ∈ elementaryThreeSubgroup R ∧ e • v = Pi.single 0 1 := by
  obtain ⟨g, hg, hzero, _⟩ :=
    FieldPolynomialElementaryThree.euclideanThree_reduce_last_preserving_first v
  have hcoprime : IsCoprime ((g • v) 0) ((g • v) 1) :=
    unimodularThree_isCoprime_of_last_zero (g • v)
      (unimodularRow_smul_specialLinear_three g v hv) hzero
  obtain ⟨p, hp, hreduce⟩ :=
    elementaryThree_coprime_pair_reduce (g • v) hcoprime
  exact ⟨p * g, (elementaryThreeSubgroup R).mul_mem hp hg,
    by simpa only [mul_smul, Fin.isValue] using hreduce⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem fieldPolynomialElementaryThree_unimodular_reduce
    {k : Type*} [Field k]
    (v : Fin 3 → Polynomial k) (hv : UnimodularRow v) :
    ∃ e : Matrix.SpecialLinearGroup (Fin 3) (Polynomial k),
      e ∈ elementaryThreeSubgroup (Polynomial k) ∧
        e • v = Pi.single 0 1 :=
  euclideanElementaryThree_unimodular_reduce v hv

end

section

namespace DvrResidueElementaryLift

open Matrix Polynomial
open StabilizedBlockReduction
open scoped BigOperators

universe u v

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem specialLinearThree_map_transvection
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (φ : A →+* B) {i j : Fin 3} (hij : i ≠ j) (a : A) :
    Matrix.SpecialLinearGroup.map φ
      (Matrix.SpecialLinearGroup.transvection hij a) =
        Matrix.SpecialLinearGroup.transvection hij (φ a) :=
  specialLinear_map_transvection_baseChange φ hij a

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem map_elementaryThreeSubgroup_eq_of_surjective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : Function.Surjective φ) :
    (elementaryThreeSubgroup A).map
        (Matrix.SpecialLinearGroup.map φ) =
      elementaryThreeSubgroup B := by
  apply le_antisymm
  · change (Subgroup.closure _).map
      (Matrix.SpecialLinearGroup.map φ) ≤ _
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, j, hij, a, rfl⟩, rfl⟩
    rw [specialLinearThree_map_transvection]
    exact Subgroup.subset_closure ⟨i, j, hij, φ a, rfl⟩
  · change Subgroup.closure _ ≤ _
    rw [Subgroup.closure_le]
    rintro _ ⟨i, j, hij, b, rfl⟩
    obtain ⟨a, ha⟩ := hφ b
    refine ⟨Matrix.SpecialLinearGroup.transvection hij a,
      Subgroup.subset_closure ⟨i, j, hij, a, rfl⟩, ?_⟩
    rw [specialLinearThree_map_transvection, ha]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_elementaryThree_lift_of_surjective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : Function.Surjective φ)
    (e : Matrix.SpecialLinearGroup (Fin 3) B)
    (he : e ∈ elementaryThreeSubgroup B) :
    ∃ p : Matrix.SpecialLinearGroup (Fin 3) A,
      p ∈ elementaryThreeSubgroup A ∧
        Matrix.SpecialLinearGroup.map φ p = e := by
  have hmap : e ∈ (elementaryThreeSubgroup A).map
      (Matrix.SpecialLinearGroup.map φ) := by
    rw [map_elementaryThreeSubgroup_eq_of_surjective φ hφ]
    exact he
  exact hmap

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_elementaryThree_polynomial_lift_of_surjective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : Function.Surjective φ)
    (e : Matrix.SpecialLinearGroup (Fin 3) (Polynomial B))
    (he : e ∈ elementaryThreeSubgroup (Polynomial B)) :
    ∃ p : Matrix.SpecialLinearGroup (Fin 3) (Polynomial A),
      p ∈ elementaryThreeSubgroup (Polynomial A) ∧
        Matrix.SpecialLinearGroup.map (Polynomial.mapRingHom φ) p = e :=
  exists_elementaryThree_lift_of_surjective
    (Polynomial.mapRingHom φ) (Polynomial.map_surjective φ hφ) e he

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem unimodularRow_ringHom_map
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (φ : A →+* B) {n : ℕ} (row : Fin n → A)
    (hrow : UnimodularRow row) :
    UnimodularRow fun i : Fin n => φ (row i) := by
  obtain ⟨coefficients, hcoefficients⟩ := hrow
  refine ⟨fun i => φ (coefficients i), ?_⟩
  have hmapped := congrArg φ hcoefficients
  simpa only [map_sum, map_mul, map_one] using hmapped

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem unimodularRow_polynomial_uniformizer_map
    {A : Type u} [CommRing A]
    (π : A) (row : Fin 3 → Polynomial A)
    (hrow : UnimodularRow row) :
    UnimodularRow fun i : Fin 3 =>
      Polynomial.map (Ideal.Quotient.mk (Ideal.span ({π} : Set A)))
        (row i) :=
  unimodularRow_ringHom_map
    (Polynomial.mapRingHom
      (Ideal.Quotient.mk (Ideal.span ({π} : Set A)))) row hrow

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem specialLinearThree_baseChange_smul_apply
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (φ : A →+* B)
    (g : Matrix.SpecialLinearGroup (Fin 3) A)
    (row : Fin 3 → A) (i : Fin 3) :
    (Matrix.SpecialLinearGroup.map φ g •
      (fun j : Fin 3 => φ (row j))) i =
      φ ((g • row) i) := by
  change
    (∑ j, φ (g.val i j) * φ (row j)) =
      φ (∑ j, g.val i j * row j)
  simp only [map_sum, map_mul]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem specialLinearThree_polynomial_baseChange_smul_apply
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (φ : A →+* B)
    (g : Matrix.SpecialLinearGroup (Fin 3) (Polynomial A))
    (row : Fin 3 → Polynomial A) (i : Fin 3) :
    (Matrix.SpecialLinearGroup.map (Polynomial.mapRingHom φ) g •
      (fun j : Fin 3 => Polynomial.map φ (row j))) i =
        Polynomial.map φ ((g • row) i) :=
  specialLinearThree_baseChange_smul_apply
    (Polynomial.mapRingHom φ) g row i

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_elementaryThree_polynomial_uniformizer_normal_form
    {A : Type u} [CommRing A] (π : A)
    (row : Fin 3 → Polynomial A)
    (e : Matrix.SpecialLinearGroup (Fin 3)
      (Polynomial (A ⧸ Ideal.span ({π} : Set A))))
    (he : e ∈ elementaryThreeSubgroup
      (Polynomial (A ⧸ Ideal.span ({π} : Set A))))
    (hreduced : e • (fun i =>
      Polynomial.map
        (Ideal.Quotient.mk (Ideal.span ({π} : Set A))) (row i)) =
          Pi.single 0 1) :
    ∃ p : Matrix.SpecialLinearGroup (Fin 3) (Polynomial A),
      p ∈ elementaryThreeSubgroup (Polynomial A) ∧
        ∀ i : Fin 3,
          Polynomial.map
            (Ideal.Quotient.mk (Ideal.span ({π} : Set A)))
              ((p • row) i) =
            (Pi.single 0 1 : Fin 3 →
              Polynomial (A ⧸ Ideal.span ({π} : Set A))) i := by
  obtain ⟨p, hp, hmap⟩ :=
    exists_elementaryThree_polynomial_lift_of_surjective
      (Ideal.Quotient.mk (Ideal.span ({π} : Set A)))
      Ideal.Quotient.mk_surjective e he
  refine ⟨p, hp, fun i => ?_⟩
  rw [← specialLinearThree_polynomial_baseChange_smul_apply,
    hmap, hreduced]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_elementaryThree_polynomial_uniformizer_reduction
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {π : A} (hπ : Irreducible π)
    (row : Fin 3 → Polynomial A) (hrow : UnimodularRow row) :
    ∃ p : Matrix.SpecialLinearGroup (Fin 3) (Polynomial A),
      p ∈ elementaryThreeSubgroup (Polynomial A) ∧
        ∀ i : Fin 3,
          Polynomial.map
            (Ideal.Quotient.mk (Ideal.span ({π} : Set A)))
              ((p • row) i) =
            (Pi.single 0 1 : Fin 3 →
              Polynomial (A ⧸ Ideal.span ({π} : Set A))) i := by
  let : Field (A ⧸ Ideal.span ({π} : Set A)) :=
    dvrUniformizerQuotientField hπ
  obtain ⟨e, he, hreduced⟩ :=
    fieldPolynomialElementaryThree_unimodular_reduce
      (fun i : Fin 3 => Polynomial.map
        (Ideal.Quotient.mk (Ideal.span ({π} : Set A))) (row i))
      (unimodularRow_polynomial_uniformizer_map π row hrow)
  exact exists_elementaryThree_polynomial_uniformizer_normal_form
    π row e he hreduced

end DvrResidueElementaryLift

end

section

open Polynomial
open scoped BigOperators

universe u

variable {A : Type u} [CommRing A]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_span_denominators_eq_top_of_maximal
    (P : A → Prop)
    (hlocal : ∀ m : Ideal A, m.IsMaximal →
      ∃ d : A, d ∉ m ∧ P d) :
    Ideal.span {d : A | P d} = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ :=
    Ideal.exists_le_maximal (Ideal.span {d : A | P d}) hne
  obtain ⟨d, hd, hP⟩ := hlocal m hm
  exact hd (hle (Ideal.subset_span hP))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_exists_finset_denominators_of_maximal
    (P : A → Prop)
    (hlocal : ∀ m : Ideal A, m.IsMaximal →
      ∃ d : A, d ∉ m ∧ P d) :
    ∃ s : Finset A,
      (∀ d ∈ s, P d) ∧ Ideal.span (s : Set A) = ⊤ := by
  obtain ⟨s, hs, hspan⟩ :=
    (Ideal.span_eq_top_iff_finite {d : A | P d}).mp
      (suslin_span_denominators_eq_top_of_maximal P hlocal)
  exact ⟨s, fun d hd => hs hd, hspan⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem suslin_exists_finset_denominators_of_primeCompl
    (P : A → Prop)
    (hlocal : ∀ (m : Ideal A) [m.IsMaximal],
      ∃ d : m.primeCompl, P (d : A)) :
    ∃ s : Finset A,
      (∀ d ∈ s, P d) ∧ Ideal.span (s : Set A) = ⊤ := by
  apply suslin_exists_finset_denominators_of_maximal P
  intro m hm
  let : m.IsMaximal := hm
  obtain ⟨d, hd⟩ := hlocal m
  exact ⟨d, Ideal.mem_primeCompl_iff.mp d.property, hd⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def suslinAwayToAtPrime (m : Ideal A) [m.IsPrime]
    (d : m.primeCompl) :
    Localization.Away (d : A) →+* Localization.AtPrime m :=
  IsLocalization.Away.lift (d : A)
    (IsLocalization.map_units (Localization.AtPrime m) d)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
public
theorem suslinAwayToAtPrime_algebraMap
    (m : Ideal A) [m.IsPrime] (d : m.primeCompl) (a : A) :
    suslinAwayToAtPrime m d
      (algebraMap A (Localization.Away (d : A)) a) =
        algebraMap A (Localization.AtPrime m) a :=
  IsLocalization.Away.lift_eq (d : A) _ a

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def suslinAwayToProductLeft (m : Ideal A) [m.IsPrime]
    (d e : m.primeCompl) :
    Localization.Away (d : A) →+*
      Localization.Away ((d * e : m.primeCompl) : A) :=
  IsLocalization.Away.awayToAwayRight
    (S := Localization.Away (d : A))
    (P := Localization.Away ((d * e : m.primeCompl) : A))
    (d : A) (e : A)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def suslinAwayToProductRight (m : Ideal A) [m.IsPrime]
    (d e : m.primeCompl) :
    Localization.Away (e : A) →+*
      Localization.Away ((d * e : m.primeCompl) : A) :=
  IsLocalization.Away.awayToAwayLeft
    (S := Localization.Away (e : A))
    (P := Localization.Away ((d * e : m.primeCompl) : A))
    (e : A) (d : A)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinAwayToProductLeft_algebraMap
    (m : Ideal A) [m.IsPrime] (d e : m.primeCompl) (a : A) :
    suslinAwayToProductLeft m d e
      (algebraMap A (Localization.Away (d : A)) a) =
        algebraMap A
          (Localization.Away ((d * e : m.primeCompl) : A)) a :=
  IsLocalization.Away.awayToAwayRight_eq (d : A) (e : A) a

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinAwayToProductRight_algebraMap
    (m : Ideal A) [m.IsPrime] (d e : m.primeCompl) (a : A) :
    suslinAwayToProductRight m d e
      (algebraMap A (Localization.Away (e : A)) a) =
        algebraMap A
          (Localization.Away ((d * e : m.primeCompl) : A)) a :=
  IsLocalization.Away.awayToAwayLeft_eq (e : A) (d : A) a

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinAwayToAtPrime_comp_productLeft
    (m : Ideal A) [m.IsPrime] (d e : m.primeCompl) :
    (suslinAwayToAtPrime m (d * e)).comp
        (suslinAwayToProductLeft m d e) =
      suslinAwayToAtPrime m d := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (d : A))
  ext a
  simp only [RingHom.comp_apply]
  rw [suslinAwayToProductLeft_algebraMap,
    suslinAwayToAtPrime_algebraMap,
    suslinAwayToAtPrime_algebraMap]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinAwayToAtPrime_comp_productRight
    (m : Ideal A) [m.IsPrime] (d e : m.primeCompl) :
    (suslinAwayToAtPrime m (d * e)).comp
        (suslinAwayToProductRight m d e) =
      suslinAwayToAtPrime m e := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (e : A))
  ext a
  simp only [RingHom.comp_apply]
  rw [suslinAwayToProductRight_algebraMap,
    suslinAwayToAtPrime_algebraMap,
    suslinAwayToAtPrime_algebraMap]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_exists_away_polynomial_lift_atPrime
    (m : Ideal A) [m.IsPrime]
    (p : Polynomial (Localization.AtPrime m)) :
    ∃ (d : m.primeCompl)
      (q : Polynomial (Localization.Away (d : A))),
      Polynomial.map (suslinAwayToAtPrime m d) q = p := by
  let d : m.primeCompl :=
    IsLocalization.commonDenom m.primeCompl p.support p.coeff
  refine ⟨d, ?_⟩
  apply (Polynomial.mem_lifts p).mp
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro n
  by_cases hs : n ∈ p.support
  · let a : A :=
      IsLocalization.integerMultiple m.primeCompl p.support p.coeff ⟨n, hs⟩
    refine ⟨algebraMap A (Localization.Away (d : A)) a *
      IsLocalization.Away.invSelf (d : A), ?_⟩
    have ha : algebraMap A (Localization.AtPrime m) a =
        algebraMap A (Localization.AtPrime m) (d : A) * p.coeff n := by
      simpa only [a, d, Submonoid.smul_def, Algebra.smul_def] using
        (IsLocalization.map_integerMultiple
          m.primeCompl p.support p.coeff ⟨n, hs⟩)
    have hinv :
        algebraMap A (Localization.AtPrime m) (d : A) *
          suslinAwayToAtPrime m d
            (IsLocalization.Away.invSelf (d : A)) = 1 := by
      have h := congrArg (suslinAwayToAtPrime m d)
        (IsLocalization.Away.mul_invSelf (R := A)
          (S := Localization.Away (d : A)) (d : A))
      simpa only [map_mul, map_one, suslinAwayToAtPrime_algebraMap] using h
    rw [map_mul, suslinAwayToAtPrime_algebraMap, ha]
    calc
      _ = p.coeff n *
          (algebraMap A (Localization.AtPrime m) (d : A) *
            suslinAwayToAtPrime m d
              (IsLocalization.Away.invSelf (d : A))) := by ring
      _ = p.coeff n := by rw [hinv, mul_one]
  · rw [Polynomial.notMem_support_iff.mp hs]
    exact ⟨0, map_zero _⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def suslinAwayElementary
    (g : Matrix.SpecialLinearGroup Index (Polynomial A)) (d : A) : Prop :=
  Matrix.SpecialLinearGroup.map
      (Polynomial.mapRingHom (algebraMap A (Localization.Away d))) g ∈
    localGlobalElementarySubgroup (Polynomial (Localization.Away d))

end

section

open Polynomial

universe u

variable {A : Type u} [CommRing A]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def suslinPolynomialSpecialLinearMap
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    Matrix.SpecialLinearGroup Index (Polynomial R) →*
      Matrix.SpecialLinearGroup Index (Polynomial S) :=
  Matrix.SpecialLinearGroup.map (Polynomial.mapRingHom f)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslinPolynomialSpecialLinearMap_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (x : Matrix.SpecialLinearGroup Index (Polynomial R)) :
    suslinPolynomialSpecialLinearMap g
        (suslinPolynomialSpecialLinearMap f x) =
      suslinPolynomialSpecialLinearMap (g.comp f) x := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change Polynomial.map g (Polynomial.map f (x.1 i j)) =
    Polynomial.map (g.comp f) (x.1 i j)
  exact Polynomial.map_map f g (x.1 i j)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem suslin_exists_away_elementary_word_lift_atPrime
    (m : Ideal A) [m.IsPrime]
    (g : Matrix.SpecialLinearGroup Index
      (Polynomial (Localization.AtPrime m)))
    (hg : g ∈ localGlobalElementarySubgroup
      (Polynomial (Localization.AtPrime m))) :
    ∃ (d : m.primeCompl)
      (q : Matrix.SpecialLinearGroup Index
        (Polynomial (Localization.Away (d : A)))),
      q ∈ localGlobalElementarySubgroup
        (Polynomial (Localization.Away (d : A))) ∧
      Matrix.SpecialLinearGroup.map
        (Polynomial.mapRingHom (suslinAwayToAtPrime m d)) q = g := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
      obtain ⟨i, j, h, p, rfl⟩ := hg
      obtain ⟨d, q, hq⟩ :=
        suslin_exists_away_polynomial_lift_atPrime m p
      refine ⟨d, Matrix.SpecialLinearGroup.transvection h q,
        localGlobal_transvection_mem i j h q, ?_⟩
      rw [specialLinear_map_transvection_baseChange
        (Polynomial.mapRingHom (suslinAwayToAtPrime m d)) h q]
      exact congrArg (Matrix.SpecialLinearGroup.transvection h) hq
  | one =>
      exact ⟨1, 1,
        (localGlobalElementarySubgroup
          (Polynomial (Localization.Away (1 : A)))).one_mem,
        map_one _⟩
  | @inv x hx ih =>
      obtain ⟨d, q, hq, hmap⟩ := ih
      exact ⟨d, q⁻¹,
        (localGlobalElementarySubgroup _).inv_mem hq,
        by rw [map_inv, hmap]⟩
  | @mul x y hx hy ihx ihy =>
      obtain ⟨d, q, hq, hmapq⟩ := ihx
      obtain ⟨e, r, hr, hmapr⟩ := ihy
      let q' :=
        suslinPolynomialSpecialLinearMap (suslinAwayToProductLeft m d e) q
      let r' :=
        suslinPolynomialSpecialLinearMap (suslinAwayToProductRight m d e) r
      have hq' : q' ∈ localGlobalElementarySubgroup
          (Polynomial (Localization.Away
            ((d * e : m.primeCompl) : A))) :=
        map_localGlobalElementarySubgroup_le
          (Polynomial.mapRingHom (suslinAwayToProductLeft m d e))
          ⟨q, hq, rfl⟩
      have hr' : r' ∈ localGlobalElementarySubgroup
          (Polynomial (Localization.Away
            ((d * e : m.primeCompl) : A))) :=
        map_localGlobalElementarySubgroup_le
          (Polynomial.mapRingHom (suslinAwayToProductRight m d e))
          ⟨r, hr, rfl⟩
      refine ⟨d * e, q' * r',
        (localGlobalElementarySubgroup _).mul_mem hq' hr', ?_⟩
      rw [map_mul]
      change
        suslinPolynomialSpecialLinearMap
            (suslinAwayToAtPrime m (d * e)) q' *
          suslinPolynomialSpecialLinearMap
            (suslinAwayToAtPrime m (d * e)) r' = x * y
      change
        suslinPolynomialSpecialLinearMap
            (suslinAwayToAtPrime m (d * e))
            (suslinPolynomialSpecialLinearMap
              (suslinAwayToProductLeft m d e) q) *
          suslinPolynomialSpecialLinearMap
            (suslinAwayToAtPrime m (d * e))
            (suslinPolynomialSpecialLinearMap
              (suslinAwayToProductRight m d e) r) = x * y
      rw [suslinPolynomialSpecialLinearMap_comp,
        suslinPolynomialSpecialLinearMap_comp,
        suslinAwayToAtPrime_comp_productLeft,
        suslinAwayToAtPrime_comp_productRight]
      exact congrArg₂ (· * ·) hmapq hmapr

end

section

namespace StabilizedBlockReduction

open Matrix

universe u

variable {R : Type u} [CommRing R]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def elementaryThreeCoordinateRotation (i j : Fin 3) (h : i ≠ j) :
    Matrix.SpecialLinearGroup (Fin 3) R :=
  Matrix.SpecialLinearGroup.transvection h 1 *
    Matrix.SpecialLinearGroup.transvection h.symm (-1) *
    Matrix.SpecialLinearGroup.transvection h 1

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem elementaryThreeCoordinateRotation_mem
    (i j : Fin 3) (h : i ≠ j) :
    elementaryThreeCoordinateRotation (R := R) i j h ∈
      elementaryThreeSubgroup R := by
  exact (elementaryThreeSubgroup R).mul_mem
    ((elementaryThreeSubgroup R).mul_mem
      (Subgroup.subset_closure ⟨i, j, h, 1, rfl⟩)
      (Subgroup.subset_closure ⟨j, i, h.symm, -1, rfl⟩))
    (Subgroup.subset_closure ⟨i, j, h, 1, rfl⟩)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem elementaryThreeTransvection_smul_same
    (i j : Fin 3) (h : i ≠ j) (a : R) (v : Fin 3 → R) :
    (Matrix.SpecialLinearGroup.transvection h a • v) i =
      v i + a * v j := by
  change ((Matrix.SpecialLinearGroup.transvection h a).val *ᵥ v) i = _
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec,
    Matrix.one_mulVec, Matrix.single_mulVec]
  simp only [Pi.add_apply, Function.update_self]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem elementaryThreeTransvection_smul_other
    (i j k : Fin 3) (h : i ≠ j) (hk : k ≠ i)
    (a : R) (v : Fin 3 → R) :
    (Matrix.SpecialLinearGroup.transvection h a • v) k = v k := by
  change ((Matrix.SpecialLinearGroup.transvection h a).val *ᵥ v) k = _
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec,
    Matrix.one_mulVec, Matrix.single_mulVec]
  simp only [Pi.add_apply, ne_eq, hk, not_false_eq_true, Function.update_of_ne, Pi.zero_apply,
    add_zero]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem elementaryThreeCoordinateRotation_smul_left
    (i j : Fin 3) (h : i ≠ j) (v : Fin 3 → R) :
    (elementaryThreeCoordinateRotation (R := R) i j h • v) i = v j := by
  simp only [elementaryThreeCoordinateRotation, mul_smul]
  rw [elementaryThreeTransvection_smul_same]
  rw [elementaryThreeTransvection_smul_other j i i h.symm h]
  rw [elementaryThreeTransvection_smul_same j i]
  rw [elementaryThreeTransvection_smul_same i j]
  rw [elementaryThreeTransvection_smul_other i j j h h.symm]
  ring

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem elementaryThreeCoordinateRotation_smul_right
    (i j : Fin 3) (h : i ≠ j) (v : Fin 3 → R) :
    (elementaryThreeCoordinateRotation (R := R) i j h • v) j = -v i := by
  simp only [elementaryThreeCoordinateRotation, mul_smul]
  rw [elementaryThreeTransvection_smul_other i j j h h.symm]
  rw [elementaryThreeTransvection_smul_same j i]
  rw [elementaryThreeTransvection_smul_same i j]
  rw [elementaryThreeTransvection_smul_other i j j h h.symm]
  ring

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem elementaryThreeCoordinateRotation_smul_other
    (i j k : Fin 3) (h : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (v : Fin 3 → R) :
    (elementaryThreeCoordinateRotation (R := R) i j h • v) k = v k := by
  simp only [elementaryThreeCoordinateRotation, mul_smul]
  rw [elementaryThreeTransvection_smul_other i j k h hki,
    elementaryThreeTransvection_smul_other j i k h.symm hkj,
    elementaryThreeTransvection_smul_other i j k h hki]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem elementaryThreeCoordinateRotation_two_zero_smul_single_zero :
    elementaryThreeCoordinateRotation (R := R)
        2 0 (by decide) •
          (Pi.single (0 : Fin 3) (1 : R) : Fin 3 → R) =
      (Pi.single (2 : Fin 3) (1 : R) : Fin 3 → R) := by
  let h20 : (2 : Fin 3) ≠ 0 := by decide
  change elementaryThreeCoordinateRotation (R := R) 2 0 h20 •
      (Pi.single (0 : Fin 3) (1 : R) : Fin 3 → R) = _
  funext i
  fin_cases i
  · change (elementaryThreeCoordinateRotation (R := R) 2 0 h20 •
        (Pi.single (0 : Fin 3) (1 : R) : Fin 3 → R)) 0 = _
    rw [elementaryThreeCoordinateRotation_smul_right]
    simp only [Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true, Pi.single_eq_of_ne, neg_zero,
      Fin.zero_eta]
  · change (elementaryThreeCoordinateRotation (R := R) 2 0 h20 •
        (Pi.single (0 : Fin 3) (1 : R) : Fin 3 → R)) 1 = _
    rw [elementaryThreeCoordinateRotation_smul_other
      2 0 1 h20 (by decide) (by decide)]
    simp only [Fin.isValue, ne_eq, one_ne_zero, not_false_eq_true, Pi.single_eq_of_ne,
      Fin.mk_one, Fin.reduceEq]
  · change (elementaryThreeCoordinateRotation (R := R) 2 0 h20 •
        (Pi.single (0 : Fin 3) (1 : R) : Fin 3 → R)) 2 = _
    rw [elementaryThreeCoordinateRotation_smul_left]
    simp only [Fin.isValue, Pi.single_eq_same, Fin.reduceFinMk]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem elementaryThree_reduce_last_of_reduce_zero
    (v : Fin 3 → R)
    (h : ∃ e : Matrix.SpecialLinearGroup (Fin 3) R,
      e ∈ elementaryThreeSubgroup R ∧
        e • v = Pi.single (0 : Fin 3) 1) :
    ∃ e : Matrix.SpecialLinearGroup (Fin 3) R,
      e ∈ elementaryThreeSubgroup R ∧
        e • v = Pi.single (2 : Fin 3) 1 := by
  obtain ⟨e, he, hreduce⟩ := h
  let rotation := elementaryThreeCoordinateRotation (R := R)
    2 0 (by decide)
  refine ⟨rotation * e,
    (elementaryThreeSubgroup R).mul_mem
      (elementaryThreeCoordinateRotation_mem 2 0 (by decide)) he, ?_⟩
  rw [mul_smul, hreduce]
  exact elementaryThreeCoordinateRotation_two_zero_smul_single_zero

end StabilizedBlockReduction

end

section

open Polynomial

universe u

variable {R : Type u} [CommRing R]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_stableRangeThree_elementary_row_transitive
    (hstable : BassStableRangeAtMost R 3)
    (v : Fin 4 → R) (hv : UnimodularRow v) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 4) R,
      g ∈ localGlobalElementarySubgroup R ∧
        g • v = Pi.single 0 1 := by
  obtain ⟨s, hs⟩ := hstable v hv
  let t₀ : Matrix.SpecialLinearGroup (Fin 4) R :=
    Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 4) ≠ 3 by decide) (s 0)
  let t₁ : Matrix.SpecialLinearGroup (Fin 4) R :=
    Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 4) ≠ 3 by decide) (s 1)
  let t₂ : Matrix.SpecialLinearGroup (Fin 4) R :=
    Matrix.SpecialLinearGroup.transvection
      (show (2 : Fin 4) ≠ 3 by decide) (s 2)
  let shorten : Matrix.SpecialLinearGroup (Fin 4) R := t₂ * t₁ * t₀
  have hshorten : shorten ∈ localGlobalElementarySubgroup R :=
    (localGlobalElementarySubgroup R).mul_mem
      ((localGlobalElementarySubgroup R).mul_mem
        (localGlobal_transvection_mem 2 3 (by decide) (s 2))
        (localGlobal_transvection_mem 1 3 (by decide) (s 1)))
      (localGlobal_transvection_mem 0 3 (by decide) (s 0))
  have hshorten_first (i : Fin 3) :
      (shorten • v) i.castSucc =
        v i.castSucc + s i * v (Fin.last 3) := by
    fin_cases i
    · dsimp [shorten, t₀, t₁, t₂]
      rw [mul_smul, mul_smul,
        LocalElementaryProof.transvection_smul_other 2 3 0
          (by decide) (by decide),
        LocalElementaryProof.transvection_smul_other 1 3 0
          (by decide) (by decide),
        LocalElementaryProof.transvection_smul_same]
    · dsimp [shorten, t₀, t₁, t₂]
      rw [mul_smul, mul_smul,
        LocalElementaryProof.transvection_smul_other 2 3 1
          (by decide) (by decide),
        LocalElementaryProof.transvection_smul_same,
        LocalElementaryProof.transvection_smul_other 0 3 1
          (by decide) (by decide),
        LocalElementaryProof.transvection_smul_other 0 3 3
          (by decide) (by decide)]
    · dsimp [shorten, t₀, t₁, t₂]
      rw [mul_smul, mul_smul,
        LocalElementaryProof.transvection_smul_same,
        LocalElementaryProof.transvection_smul_other 1 3 2
          (by decide) (by decide),
        LocalElementaryProof.transvection_smul_other 0 3 2
          (by decide) (by decide),
        LocalElementaryProof.transvection_smul_other 1 3 3
          (by decide) (by decide),
        LocalElementaryProof.transvection_smul_other 0 3 3
          (by decide) (by decide)]
  obtain ⟨c, hc⟩ := hs
  let w : Fin 4 → R := shorten • v
  have hwcomb : c 0 * w 0 + c 1 * w 1 + c 2 * w 2 = 1 := by
    change c 0 * (shorten • v) 0 +
      c 1 * (shorten • v) 1 + c 2 * (shorten • v) 2 = 1
    have h₀ : (shorten • v) 0 = v 0 + s 0 * v 3 := by
      simpa only [Fin.isValue, Fin.castSucc_zero, Fin.reduceLast] using hshorten_first 0
    have h₁ : (shorten • v) 1 = v 1 + s 1 * v 3 := by
      simpa only [Fin.isValue, Fin.castSucc_one, Fin.reduceLast] using hshorten_first 1
    have h₂ : (shorten • v) 2 = v 2 + s 2 * v 3 := by
      simpa only [Fin.isValue, Fin.reduceCastSucc, Fin.reduceLast] using hshorten_first 2
    rw [h₀, h₁, h₂]
    simpa only [Fin.isValue, add_assoc, Fin.reduceLast, Fin.sum_univ_succ, Fin.castSucc_zero,
      Fin.castSucc_succ, Nat.reduceAdd, Fin.succ_zero_eq_one, Finset.univ_unique,
      Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_one_eq_two] using hc
  let q₀ : Matrix.SpecialLinearGroup (Fin 4) R :=
    Matrix.SpecialLinearGroup.transvection
      (show (3 : Fin 4) ≠ 0 by decide) ((1 - w 3) * c 0)
  let q₁ : Matrix.SpecialLinearGroup (Fin 4) R :=
    Matrix.SpecialLinearGroup.transvection
      (show (3 : Fin 4) ≠ 1 by decide) ((1 - w 3) * c 1)
  let q₂ : Matrix.SpecialLinearGroup (Fin 4) R :=
    Matrix.SpecialLinearGroup.transvection
      (show (3 : Fin 4) ≠ 2 by decide) ((1 - w 3) * c 2)
  let createUnit : Matrix.SpecialLinearGroup (Fin 4) R := q₂ * q₁ * q₀
  have hcreate : createUnit ∈ localGlobalElementarySubgroup R :=
    (localGlobalElementarySubgroup R).mul_mem
      ((localGlobalElementarySubgroup R).mul_mem
        (localGlobal_transvection_mem 3 2 (by decide) ((1 - w 3) * c 2))
        (localGlobal_transvection_mem 3 1 (by decide) ((1 - w 3) * c 1)))
      (localGlobal_transvection_mem 3 0 (by decide) ((1 - w 3) * c 0))
  have hunit : (createUnit • w) 3 = 1 := by
    dsimp [createUnit, q₀, q₁, q₂]
    rw [mul_smul, mul_smul,
      LocalElementaryProof.transvection_smul_same,
      LocalElementaryProof.transvection_smul_same,
      LocalElementaryProof.transvection_smul_same,
      LocalElementaryProof.transvection_smul_other 3 0 1
        (by decide) (by decide),
      LocalElementaryProof.transvection_smul_other 3 1 2
        (by decide) (by decide),
      LocalElementaryProof.transvection_smul_other 3 0 2
        (by decide) (by decide)]
    calc
      w 3 + ((1 - w 3) * c 0) * w 0 +
            ((1 - w 3) * c 1) * w 1 +
            ((1 - w 3) * c 2) * w 2 =
          w 3 + (1 - w 3) *
            (c 0 * w 0 + c 1 * w 1 + c 2 * w 2) := by ring
      _ = 1 := by rw [hwcomb]; ring
  let rotate : Matrix.SpecialLinearGroup (Fin 4) R :=
    LocalElementaryProof.coordinateRotation 0 3 (by decide)
  have hrotate : rotate ∈ localGlobalElementarySubgroup R := by
    change rotate ∈ LocalElementaryProof.localElementarySubgroup R
    exact LocalElementaryProof.coordinateRotation_mem 0 3 (by decide)
  have hfirst : (rotate • (createUnit • w)) 0 = 1 := by
    dsimp [rotate]
    rw [LocalElementaryProof.coordinateRotation_smul_left, hunit]
  obtain ⟨p, hp, hreduce⟩ :=
    LocalElementaryProof.unit_first_elementary_reduce
      (rotate • (createUnit • w))
      (by rw [hfirst]; exact isUnit_one)
  refine ⟨p * rotate * createUnit * shorten, ?_, ?_⟩
  · exact (localGlobalElementarySubgroup R).mul_mem
      ((localGlobalElementarySubgroup R).mul_mem
        ((localGlobalElementarySubgroup R).mul_mem hp hrotate)
        hcreate) hshorten
  · simpa only [mul_smul, Fin.isValue] using hreduce

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_elementary_eq_top_of_stableRangeThree_of_stabilizedThree
    (hstable : BassStableRangeAtMost R 3)
    (hblock : StabilizedBlockReduction.StabilizedThreeElementaryGeneration R) :
    localGlobalElementarySubgroup R = ⊤ := by
  apply StabilizedBlockReduction.elementary_eq_top_iff_columnTransitivity_and_stabilizedThree.mpr
  refine ⟨?_, hblock⟩
  intro g
  exact suslin_stableRangeThree_elementary_row_transitive hstable
    (fun i : Fin 4 => g i 0) (specialLinear_column_unimodular g 0)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem suslin_specialLinear_elementary_of_stableRangeThree_of_stabilizedThree
    (hstable : BassStableRangeAtMost R 3)
    (hblock : StabilizedBlockReduction.StabilizedThreeElementaryGeneration R)
    (g : Matrix.SpecialLinearGroup (Fin 4) R) :
    g ∈ localGlobalElementarySubgroup R := by
  rw [suslin_elementary_eq_top_of_stableRangeThree_of_stabilizedThree
    hstable hblock]
  trivial

end

section

namespace MennickeIdentity

open Matrix

universe u

variable {R : Type u} [CommRing R]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def mennickeBlock (a b c d : R) (hdet : a * d - b * c = 1) :
    Matrix.SpecialLinearGroup (Fin 3) R :=
  ⟨!![a, b, 0; c, d, 0; 0, 0, 1], by
    rw [Matrix.det_fin_three]
    simpa only [Fin.isValue, of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one,
      cons_val, mul_one, mul_zero, sub_zero, add_zero, zero_mul] using hdet⟩



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem specialLinear_mul_transvection_apply
    {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A]
    (x : Matrix.SpecialLinearGroup ι A) {i j : ι} (hij : i ≠ j)
    (r : A) (a b : ι) :
    (x * Matrix.SpecialLinearGroup.transvection hij r) a b =
      if b = j then x a j + r * x a i else x a b := by
  rw [Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.transvection_coe]
  split_ifs with h
  · subst b
    exact Matrix.mul_transvection_apply_same (i := i) (j := j) a r x.val
  · exact Matrix.mul_transvection_apply_of_ne (i := i) (j := j) a b h r x.val

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def ContainsElementaryRoots
    (E : Subgroup (Matrix.SpecialLinearGroup (Fin 3) R)) : Prop :=
  ∀ (i j : Fin 3) (hij : i ≠ j) (r : R),
    Matrix.SpecialLinearGroup.transvection hij r ∈ E

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennicke_left_factor_det
    (a ap b c d : R) (hdet : a * ap * d - b * c = 1) :
    a * (ap * d) - b * c = 1 := by
  linear_combination hdet

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennicke_right_factor_det
    (a ap b c d : R) (hdet : a * ap * d - b * c = 1) :
    ap * (a * d) - b * c = 1 := by
  linear_combination hdet

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def mennickeWord
    (a ap b c d : R) (hdet : a * ap * d - b * c = 1) :
    Matrix.SpecialLinearGroup (Fin 3) R :=
  Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 3) ≠ 0 by decide)
      (c * (ap * d) * (a * d) - d * (c + ap * c * (a * d))) *
    Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 3) ≠ 2 by decide) (a * d - 1) *
    Matrix.SpecialLinearGroup.transvection
      (show (2 : Fin 3) ≠ 1 by decide) 1 *
    Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 3) ≠ 2 by decide) (-1) *
    mennickeBlock a b c (ap * d)
      (mennicke_left_factor_det a ap b c d hdet) *
    Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 3) ≠ 2 by decide) 1 *
    Matrix.SpecialLinearGroup.transvection
      (show (2 : Fin 3) ≠ 1 by decide) (-1) *
    Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 3) ≠ 2 by decide) 1 *
    mennickeBlock ap b c (a * d)
      (mennicke_right_factor_det a ap b c d hdet) *
    Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 3) ≠ 2 by decide) (-1) *
    Matrix.SpecialLinearGroup.transvection
      (show (2 : Fin 3) ≠ 1 by decide) 1 *
    Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 3) ≠ 2 by decide) (a - 1) *
    Matrix.SpecialLinearGroup.transvection
      (show (2 : Fin 3) ≠ 0 by decide) (-ap * c) *
    Matrix.SpecialLinearGroup.transvection
      (show (2 : Fin 3) ≠ 1 by decide) (-(ap * d))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem parkWoodburn_mennicke_identity
    (a ap b c d : R) (hdet : a * ap * d - b * c = 1) :
    mennickeBlock (a * ap) b c d hdet =
      mennickeWord a ap b c d hdet := by
  let w1 : Matrix.SpecialLinearGroup (Fin 3) R :=
    Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide)
      (c * (ap * d) * (a * d) - d * (c + ap * c * (a * d)))
  have hw1 (i j : Fin 3) : w1 i j = !![1, 0, 0; -c * d, 1, 0; 0, 0, 1] i j := by
    dsimp only [w1]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.transvection_coe]; ring
  let w2 := w1 * Matrix.SpecialLinearGroup.transvection
    (show (1 : Fin 3) ≠ 2 by decide) (a * d - 1)
  have hw2 (i j : Fin 3) :
      w2 i j = !![1, 0, 0; -c * d, 1, a * d - 1; 0, 0, 1] i j := by
    dsimp only [w2]
    rw [specialLinear_mul_transvection_apply]
    fin_cases i <;> fin_cases j <;> simp [hw1]
  let w3 := w2 * Matrix.SpecialLinearGroup.transvection
    (show (2 : Fin 3) ≠ 1 by decide) 1
  have hw3 (i j : Fin 3) :
      w3 i j = !![1, 0, 0; -c * d, a * d, a * d - 1; 0, 1, 1] i j := by
    dsimp only [w3]
    rw [specialLinear_mul_transvection_apply]
    fin_cases i <;> fin_cases j <;> simp [hw2]
  let w4 := w3 * Matrix.SpecialLinearGroup.transvection
    (show (1 : Fin 3) ≠ 2 by decide) (-1)
  have hw4 (i j : Fin 3) :
      w4 i j = !![1, 0, 0; -c * d, a * d, -1; 0, 1, 0] i j := by
    dsimp only [w4]
    rw [specialLinear_mul_transvection_apply]
    fin_cases i <;> fin_cases j <;> simp [hw3]; ring
  let w5 := w4 * mennickeBlock a b c (ap * d)
    (mennicke_left_factor_det a ap b c d hdet)
  have hmiddleLeft : -(c * d * a) + a * d * c = 0 := by
    ring
  have hmiddleCenter : -(c * d * b) + a * d * (ap * d) = d := by
    linear_combination d * hdet
  have hw5 (i j : Fin 3) :
      w5 i j = !![a, b, 0; 0, d, -1; c, ap * d, 0] i j := by
    dsimp only [w5]
    rw [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, mennickeBlock, hw4,
        hmiddleLeft, hmiddleCenter]
  let w6 := w5 * Matrix.SpecialLinearGroup.transvection
    (show (1 : Fin 3) ≠ 2 by decide) 1
  have hw6 (i j : Fin 3) :
      w6 i j = !![a, b, b; 0, d, d - 1; c, ap * d, ap * d] i j := by
    dsimp only [w6]
    rw [specialLinear_mul_transvection_apply]
    fin_cases i <;> fin_cases j <;> simp [hw5]; ring
  let w7 := w6 * Matrix.SpecialLinearGroup.transvection
    (show (2 : Fin 3) ≠ 1 by decide) (-1)
  have hw7 (i j : Fin 3) :
      w7 i j = !![a, 0, b; 0, 1, d - 1; c, 0, ap * d] i j := by
    dsimp only [w7]
    rw [specialLinear_mul_transvection_apply]
    fin_cases i <;> fin_cases j <;> simp [hw6]
  let w8 := w7 * Matrix.SpecialLinearGroup.transvection
    (show (1 : Fin 3) ≠ 2 by decide) 1
  have hw8 (i j : Fin 3) :
      w8 i j = !![a, 0, b; 0, 1, d; c, 0, ap * d] i j := by
    dsimp only [w8]
    rw [specialLinear_mul_transvection_apply]
    fin_cases i <;> fin_cases j <;> simp [hw7]
  let w9 := w8 * mennickeBlock ap b c (a * d)
    (mennicke_right_factor_det a ap b c d hdet)
  have hw9 (i j : Fin 3) : w9 i j =
      !![a * ap, a * b, b; c, a * d, d; ap * c, b * c, ap * d] i j := by
    dsimp only [w9]
    rw [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, mennickeBlock, hw8] <;> ring
  let w10 := w9 * Matrix.SpecialLinearGroup.transvection
    (show (1 : Fin 3) ≠ 2 by decide) (-1)
  have hw10 (i j : Fin 3) : w10 i j =
      !![a * ap, a * b, b - a * b; c, a * d, d - a * d;
        ap * c, b * c, ap * d - b * c] i j := by
    dsimp only [w10]
    rw [specialLinear_mul_transvection_apply]
    fin_cases i <;> fin_cases j <;> simp [hw9] <;> ring
  let w11 := w10 * Matrix.SpecialLinearGroup.transvection
    (show (2 : Fin 3) ≠ 1 by decide) 1
  have hw11 (i j : Fin 3) : w11 i j =
      !![a * ap, b, b - a * b; c, d, d - a * d;
        ap * c, ap * d, ap * d - b * c] i j := by
    dsimp only [w11]
    rw [specialLinear_mul_transvection_apply]
    fin_cases i <;> fin_cases j <;> simp [hw10]
  let w12 := w11 * Matrix.SpecialLinearGroup.transvection
    (show (1 : Fin 3) ≠ 2 by decide) (a - 1)
  have htopRight : b - a * b + (a - 1) * b = 0 := by
    ring
  have hmiddleRight : d - a * d + (a - 1) * d = 0 := by
    ring
  have hbottomRight : ap * d - b * c + (a - 1) * (ap * d) = 1 := by
    linear_combination hdet
  have hw12 (i j : Fin 3) :
      w12 i j = !![a * ap, b, 0; c, d, 0; ap * c, ap * d, 1] i j := by
    dsimp only [w12]
    rw [specialLinear_mul_transvection_apply]
    fin_cases i <;> fin_cases j <;>
      simp [hw11, htopRight, hmiddleRight, hbottomRight]
  let w13 := w12 * Matrix.SpecialLinearGroup.transvection
    (show (2 : Fin 3) ≠ 0 by decide) (-ap * c)
  have hw13 (i j : Fin 3) :
      w13 i j = !![a * ap, b, 0; c, d, 0; 0, ap * d, 1] i j := by
    dsimp only [w13]
    rw [specialLinear_mul_transvection_apply]
    fin_cases i <;> fin_cases j <;> simp [hw12]
  let w14 := w13 * Matrix.SpecialLinearGroup.transvection
    (show (2 : Fin 3) ≠ 1 by decide) (-(ap * d))
  have hw14 (i j : Fin 3) :
      w14 i j = !![a * ap, b, 0; c, d, 0; 0, 0, 1] i j := by
    dsimp only [w14]
    rw [specialLinear_mul_transvection_apply]
    fin_cases i <;> fin_cases j <;> simp [hw13]
  change mennickeBlock (a * ap) b c d hdet = w14
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  exact (hw14 i j).symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennickeWord_mem
    (E : Subgroup (Matrix.SpecialLinearGroup (Fin 3) R))
    (hE : ContainsElementaryRoots E)
    (a ap b c d : R) (hdet : a * ap * d - b * c = 1)
    (hP : mennickeBlock a b c (ap * d)
      (mennicke_left_factor_det a ap b c d hdet) ∈ E)
    (hQ : mennickeBlock ap b c (a * d)
      (mennicke_right_factor_det a ap b c d hdet) ∈ E) :
    mennickeWord a ap b c d hdet ∈ E := by
  unfold mennickeWord
  repeat' first | assumption | apply E.mul_mem | apply hE

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennicke_block_mem_of_factors
    (E : Subgroup (Matrix.SpecialLinearGroup (Fin 3) R))
    (hE : ContainsElementaryRoots E)
    (a ap b c d : R) (hdet : a * ap * d - b * c = 1)
    (hP : mennickeBlock a b c (ap * d)
      (mennicke_left_factor_det a ap b c d hdet) ∈ E)
    (hQ : mennickeBlock ap b c (a * d)
      (mennicke_right_factor_det a ap b c d hdet) ∈ E) :
    mennickeBlock (a * ap) b c d hdet ∈ E := by
  rw [parkWoodburn_mennicke_identity]
  exact mennickeWord_mem E hE a ap b c d hdet hP hQ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def mennickeRotation : Matrix.SpecialLinearGroup (Fin 3) R :=
  Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 3) ≠ 1 by decide) 1 *
    Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 3) ≠ 0 by decide) (-1) *
    Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 3) ≠ 1 by decide) 1

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennickeRotation_mem
    (E : Subgroup (Matrix.SpecialLinearGroup (Fin 3) R))
    (hE : ContainsElementaryRoots E) :
    mennickeRotation (R := R) ∈ E := by
  unfold mennickeRotation
  exact E.mul_mem
    (E.mul_mem
      (hE 0 1 (by decide) 1)
      (hE 1 0 (by decide) (-1)))
    (hE 0 1 (by decide) 1)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennicke_source_det
    (a b c d : R) (hdet : a * d - b * c = 1) :
    a * d - (-c) * (-b) = 1 := by
  linear_combination hdet

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennicke_target_det
    (a b c d : R) (hdet : a * d - b * c = 1) :
    d * a - b * c = 1 := by
  linear_combination hdet

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennickeBlock_rotation_conjugate
    (a b c d : R) (hdet : a * d - b * c = 1) :
    mennickeRotation *
        mennickeBlock a (-c) (-b) d
          (mennicke_source_det a b c d hdet) *
        mennickeRotation⁻¹ =
      mennickeBlock d b c a
        (mennicke_target_det a b c d hdet) := by
  simp only [mennickeRotation, _root_.mul_inv_rev,
    Matrix.SpecialLinearGroup.transvection_inv]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hmul (x y : Matrix.SpecialLinearGroup (Fin 3) R) (p q : Fin 3) :
      (x * y) p q = ∑ k, x p k * y k q := rfl
  simp_rw [hmul]
  fin_cases i <;> fin_cases j <;>
    simp [mennickeBlock,
      Fin.sum_univ_succ, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.one_apply, Matrix.single_apply]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennicke_swapped_left_factor_det
    (a ap b c d : R) (hdet : a * ap * d - b * c = 1) :
    (ap * d) * a - b * c = 1 := by
  linear_combination hdet

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennicke_swapped_right_factor_det
    (a ap b c d : R) (hdet : a * ap * d - b * c = 1) :
    (a * d) * ap - b * c = 1 := by
  linear_combination hdet

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennicke_swapped_target_det
    (a ap b c d : R) (hdet : a * ap * d - b * c = 1) :
    d * (a * ap) - b * c = 1 := by
  linear_combination hdet

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennicke_swapped_block_mem_of_factors
    (E : Subgroup (Matrix.SpecialLinearGroup (Fin 3) R))
    (hE : ContainsElementaryRoots E)
    (a ap b c d : R) (hdet : a * ap * d - b * c = 1)
    (hP : mennickeBlock (ap * d) b c a
      (mennicke_swapped_left_factor_det a ap b c d hdet) ∈ E)
    (hQ : mennickeBlock (a * d) b c ap
      (mennicke_swapped_right_factor_det a ap b c d hdet) ∈ E) :
    mennickeBlock d b c (a * ap)
      (mennicke_swapped_target_det a ap b c d hdet) ∈ E := by
  have hrot : mennickeRotation (R := R) ∈ E :=
    mennickeRotation_mem E hE
  have hsource : a * ap * d - (-c) * (-b) = 1 := by
    linear_combination hdet
  have hleft :
      mennickeBlock a (-c) (-b) (ap * d)
        (mennicke_left_factor_det a ap (-c) (-b) d hsource) ∈ E := by
    have hconj := mennickeBlock_rotation_conjugate
      a b c (ap * d) (mennicke_left_factor_det a ap b c d hdet)
    have hp := E.mul_mem (E.mul_mem (E.inv_mem hrot) hP) hrot
    simpa only [← hconj, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hp
  have hright :
      mennickeBlock ap (-c) (-b) (a * d)
        (mennicke_right_factor_det a ap (-c) (-b) d hsource) ∈ E := by
    have hconj := mennickeBlock_rotation_conjugate
      ap b c (a * d) (mennicke_right_factor_det a ap b c d hdet)
    have hq := E.mul_mem (E.mul_mem (E.inv_mem hrot) hQ) hrot
    simpa only [← hconj, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hq
  have horiginal := mennicke_block_mem_of_factors
    E hE a ap (-c) (-b) d hsource hleft hright
  have hconj := mennickeBlock_rotation_conjugate
    (a * ap) b c d hdet
  have hfinal := E.mul_mem (E.mul_mem hrot horiginal) (E.inv_mem hrot)
  simpa only [hconj] using hfinal

end MennickeIdentity

end

section

open Polynomial

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_horrocks_truncated_remainder_aux
    {A : Type*} [CommRing A]
    (e : Polynomial A) (he0 : IsUnit (e.coeff 0))
    (hn : 0 < e.natDegree)
    (k : ℕ) (f : Polynomial A)
    (hk : f.natDegree + 1 ≤ k + e.natDegree) :
    ∃ h q : Polynomial A,
      h.natDegree < e.natDegree ∧
        f = X ^ k * h + q * e := by
  induction k generalizing f with
  | zero =>
      refine ⟨f, 0, ?_, by simp only [pow_zero, one_mul, zero_mul, add_zero]⟩
      simpa only [zero_add, Order.add_one_le_iff] using hk
  | succ k ih =>
      let u : A := (↑he0.unit⁻¹ : A) * f.coeff 0
      let f' : Polynomial A := f.divX - C u * e.divX
      have hue : u * e.coeff 0 = f.coeff 0 := by
        dsimp [u]
        calc
          (↑he0.unit⁻¹ : A) * f.coeff 0 * e.coeff 0 =
              ((↑he0.unit⁻¹ : A) * e.coeff 0) * f.coeff 0 := by ring
          _ = f.coeff 0 := by rw [he0.val_inv_mul, one_mul]
      have hstep : f = X * f' + C u * e := by
        have hf := X_mul_divX_add f
        have he := X_mul_divX_add e
        have hC : C u * C (e.coeff 0) = C (f.coeff 0) := by
          rw [← C_mul, hue]
        rw [← hf, ← he]
        dsimp [f']
        rw [← hC]
        ring
      have hdivf : f.divX.natDegree ≤ f.natDegree - 1 := by
        rw [natDegree_divX_eq_natDegree_tsub_one]
      have hdive : e.divX.natDegree ≤ e.natDegree - 1 := by
        rw [natDegree_divX_eq_natDegree_tsub_one]
      have hmul : (C u * e.divX).natDegree ≤ e.natDegree - 1 := by
        calc
          (C u * e.divX).natDegree ≤ (C u).natDegree + e.divX.natDegree :=
            natDegree_mul_le
          _ ≤ e.natDegree - 1 := by simpa only [natDegree_C, zero_add] using hdive
      have hf'deg : f'.natDegree ≤ max (f.natDegree - 1) (e.natDegree - 1) := by
        exact (natDegree_sub_le _ _).trans (max_le_max hdivf hmul)
      have hk' : f'.natDegree + 1 ≤ k + e.natDegree := by
        omega
      obtain ⟨h, q, hdeg, hrepr⟩ := ih f' hk'
      refine ⟨h, X * q + C u, hdeg, ?_⟩
      rw [hstep, hrepr, pow_succ]
      ring

end

section

open Polynomial

section

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem valuation_dvd_total
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    (a b : A) : a ∣ b ∨ b ∣ a :=
  ValuationRing.dvd_total a b

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem valuation_leadingCoeff_dvd_total
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    (f g : A[X]) :
    f.leadingCoeff ∣ g.leadingCoeff ∨
      g.leadingCoeff ∣ f.leadingCoeff :=
  valuation_dvd_total f.leadingCoeff g.leadingCoeff

section PolynomialCancellation

variable {A : Type u} [CommRing A] [IsDomain A]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def shiftedLeadingCancellationQuotient (f g : A[X]) (c : A) : A[X] :=
  Polynomial.C c * Polynomial.X ^ (g.natDegree - f.natDegree)

omit [IsDomain A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem shiftedLeadingCancellationQuotient_leadingCoeff
    (f g : A[X]) (c : A) :
    (shiftedLeadingCancellationQuotient f g c).leadingCoeff = c := by
  unfold shiftedLeadingCancellationQuotient
  exact Polynomial.leadingCoeff_C_mul_X_pow c
    (g.natDegree - f.natDegree)

omit [IsDomain A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shiftedLeadingCancellationQuotient_natDegree
    (f g : A[X]) (c : A) (hc : c ≠ 0) :
    (shiftedLeadingCancellationQuotient f g c).natDegree =
      g.natDegree - f.natDegree := by
  unfold shiftedLeadingCancellationQuotient
  exact Polynomial.natDegree_C_mul_X_pow _ c hc

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shiftedLeadingCancellationQuotient_ne_zero
    (f g : A[X]) (c : A) (hc : c ≠ 0) :
    shiftedLeadingCancellationQuotient f g c ≠ 0 := by
  unfold shiftedLeadingCancellationQuotient
  exact mul_ne_zero (Polynomial.C_ne_zero.mpr hc)
    (pow_ne_zero _ Polynomial.X_ne_zero)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shiftedLeadingCancellationQuotient_mul_natDegree
    (f g : A[X]) (hf : f ≠ 0)
    (hdeg : f.natDegree ≤ g.natDegree)
    (c : A) (hc : c ≠ 0) :
    (shiftedLeadingCancellationQuotient f g c * f).natDegree =
      g.natDegree := by
  rw [Polynomial.natDegree_mul
    (shiftedLeadingCancellationQuotient_ne_zero f g c hc) hf,
    shiftedLeadingCancellationQuotient_natDegree f g c hc]
  exact Nat.sub_add_cancel hdeg

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem degree_sub_shiftedLeadingCancellationQuotient_mul_lt
    (f g : A[X]) (hf : f ≠ 0) (hg : g ≠ 0)
    (hdeg : f.natDegree ≤ g.natDegree)
    (c : A) (hc : g.leadingCoeff = f.leadingCoeff * c) :
    (g - shiftedLeadingCancellationQuotient f g c * f).degree <
      g.degree := by
  have hc0 : c ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hc
    exact (Polynomial.leadingCoeff_ne_zero.mpr hg) hc
  have hq0 := shiftedLeadingCancellationQuotient_ne_zero f g c hc0
  have hqfdeg :=
    shiftedLeadingCancellationQuotient_mul_natDegree f g hf hdeg c hc0
  apply Polynomial.degree_sub_lt_left
    (q := shiftedLeadingCancellationQuotient f g c * f)
  · rw [Polynomial.degree_eq_natDegree hg,
      Polynomial.degree_eq_natDegree (mul_ne_zero hq0 hf), hqfdeg]
  · exact hg
  · rw [Polynomial.leadingCoeff_mul,
      shiftedLeadingCancellationQuotient_leadingCoeff]
    exact hc.trans (mul_comm _ _)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem natDegree_sub_shiftedLeadingCancellationQuotient_mul_lt
    (f g : A[X]) (hf : f ≠ 0) (hg : g ≠ 0)
    (hdeg : f.natDegree ≤ g.natDegree)
    (hgpos : 0 < g.natDegree)
    (c : A) (hc : g.leadingCoeff = f.leadingCoeff * c) :
    (g - shiftedLeadingCancellationQuotient f g c * f).natDegree <
      g.natDegree := by
  let r : A[X] := g - shiftedLeadingCancellationQuotient f g c * f
  by_cases hr : r = 0
  · simpa [r, hr] using hgpos
  · apply (Polynomial.natDegree_lt_iff_degree_lt hr).mpr
    rw [← Polynomial.degree_eq_natDegree hg]
    exact degree_sub_shiftedLeadingCancellationQuotient_mul_lt
      f g hf hg hdeg c hc

end PolynomialCancellation

end

end

section

namespace MennickeFactorSplit

open Polynomial
open MennickeIdentity
open StabilizedBlockReduction

universe u

variable {A : Type u} [CommRing A]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem constant_factor_det
    (a : A) (s : ℕ) (r g p q : Polynomial A)
    (hdet : (C a * (X ^ s * r)) * q - g * p = 1) :
    C a * ((X ^ s * r) * q) - g * p = 1 := by
  linear_combination hdet

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem monomial_factor_det
    (a : A) (s : ℕ) (r g p q : Polynomial A)
    (hdet : (C a * (X ^ s * r)) * q - g * p = 1) :
    X ^ s * (r * (C a * q)) - g * p = 1 := by
  linear_combination hdet

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem primitive_factor_det
    (a : A) (s : ℕ) (r g p q : Polynomial A)
    (hdet : (C a * (X ^ s * r)) * q - g * p = 1) :
    r * (X ^ s * (C a * q)) - g * p = 1 := by
  linear_combination hdet

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennicke_block_mem_of_constant_monomial_primitive
    (E : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (Polynomial A)))
    (hE : ContainsElementaryRoots E)
    (a : A) (s : ℕ) (r g p q : Polynomial A)
    (hdet : (C a * (X ^ s * r)) * q - g * p = 1)
    (hconstant : mennickeBlock (C a) g p ((X ^ s * r) * q)
      (constant_factor_det a s r g p q hdet) ∈ E)
    (hmonomial : mennickeBlock (X ^ s) g p (r * (C a * q))
      (monomial_factor_det a s r g p q hdet) ∈ E)
    (hprimitive : mennickeBlock r g p (X ^ s * (C a * q))
      (primitive_factor_det a s r g p q hdet) ∈ E) :
    mennickeBlock (C a * (X ^ s * r)) g p q hdet ∈ E := by
  apply mennicke_block_mem_of_factors
    E hE (C a) (X ^ s * r) g p q hdet
  · exact hconstant
  · apply mennicke_block_mem_of_factors
      E hE (X ^ s) r g p (C a * q)
      (mennicke_right_factor_det
        (C a) (X ^ s * r) g p q hdet)
    · exact hmonomial
    · exact hprimitive

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem elementaryThree_mennicke_block_mem_of_three_factors
    (a : A) (s : ℕ) (r g p q : Polynomial A)
    (hdet : (C a * (X ^ s * r)) * q - g * p = 1)
    (hconstant : mennickeBlock (C a) g p ((X ^ s * r) * q)
      (constant_factor_det a s r g p q hdet) ∈
        elementaryThreeSubgroup (Polynomial A))
    (hmonomial : mennickeBlock (X ^ s) g p (r * (C a * q))
      (monomial_factor_det a s r g p q hdet) ∈
        elementaryThreeSubgroup (Polynomial A))
    (hprimitive : mennickeBlock r g p (X ^ s * (C a * q))
      (primitive_factor_det a s r g p q hdet) ∈
        elementaryThreeSubgroup (Polynomial A)) :
    mennickeBlock (C a * (X ^ s * r)) g p q hdet ∈
      elementaryThreeSubgroup (Polynomial A) := by
  apply mennicke_block_mem_of_constant_monomial_primitive
    (elementaryThreeSubgroup (Polynomial A))
    (fun i j h b => Subgroup.subset_closure ⟨i, j, h, b, rfl⟩)
    a s r g p q hdet hconstant hmonomial hprimitive

end MennickeFactorSplit

end

section

open Matrix
open scoped BigOperators

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem unitEntry_root_mem
    {R : Type*} [CommRing R]
    (i j : Fin 3) (h : i ≠ j) (r : R) :
    Matrix.SpecialLinearGroup.transvection h r ∈
      StabilizedBlockReduction.elementaryThreeSubgroup R :=
  Subgroup.subset_closure ⟨i, j, h, r, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def unitEntry_diagonalUnitPair
    {R : Type*} [CommRing R] (a : Rˣ) :
    Matrix.SpecialLinearGroup (Fin 3) R :=
  Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 3) ≠ 1 by decide) (a : R) *
    Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 3) ≠ 0 by decide) (-(↑a⁻¹ : R)) *
    Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 3) ≠ 1 by decide) (a : R) *
    Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 3) ≠ 1 by decide) (-1) *
    Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 3) ≠ 0 by decide) 1 *
    Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 3) ≠ 1 by decide) (-1)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem unitEntry_diagonalUnitPair_mem
    {R : Type*} [CommRing R] (a : Rˣ) :
    unitEntry_diagonalUnitPair a ∈
      StabilizedBlockReduction.elementaryThreeSubgroup R := by
  unfold unitEntry_diagonalUnitPair
  exact (StabilizedBlockReduction.elementaryThreeSubgroup R).mul_mem
    ((StabilizedBlockReduction.elementaryThreeSubgroup R).mul_mem
      ((StabilizedBlockReduction.elementaryThreeSubgroup R).mul_mem
        ((StabilizedBlockReduction.elementaryThreeSubgroup R).mul_mem
          ((StabilizedBlockReduction.elementaryThreeSubgroup R).mul_mem
            (unitEntry_root_mem 0 1 (by decide) (a : R))
            (unitEntry_root_mem 1 0 (by decide) (-(↑a⁻¹ : R))))
          (unitEntry_root_mem 0 1 (by decide) (a : R)))
        (unitEntry_root_mem 0 1 (by decide) (-1)))
      (unitEntry_root_mem 1 0 (by decide) 1))
    (unitEntry_root_mem 0 1 (by decide) (-1))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem unitEntry_diagonalUnitPair_apply
    {R : Type*} [CommRing R] (a : Rˣ) (i j : Fin 3) :
    (unitEntry_diagonalUnitPair a) i j =
      if i = j then
        if i = 0 then (a : R) else if i = 1 then (↑a⁻¹ : R) else 1
      else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp only [unitEntry_diagonalUnitPair, Fin.isValue, Nat.reduceAdd,
      Fin.zero_eta, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, true_and,
      Fin.sum_univ_three, ↓reduceIte, one_ne_zero, add_zero, false_and,
      mul_ite, mul_one, mul_zero, zero_ne_one, zero_add, Fin.reduceEq,
      ite_self, mul_neg, Units.mul_inv, add_neg_cancel, zero_mul, ite_mul,
      Finset.sum_ite_eq, Finset.mem_univ, and_false,
      Finset.sum_ite_eq', Fin.mk_one, and_true,
      neg_add_cancel, Fin.reduceFinMk, one_mul, neg_mul, Units.inv_mul,
      neg_zero, Finset.sum_neg_distrib, neg_add_rev, neg_neg]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem stabilizedTwoByTwo_mem_elementaryThree_of_topLeft_isUnit
    {R : Type*} [CommRing R]
    (b : Matrix.SpecialLinearGroup (Fin 3) R)
    (hrow : ∀ j : Fin 3, b 2 j = if j = 2 then 1 else 0)
    (hcolumn : ∀ i : Fin 3, b i 2 = if i = 2 then 1 else 0)
    (hu : IsUnit (b 0 0)) :
    b ∈ StabilizedBlockReduction.elementaryThreeSubgroup R := by
  let a : Rˣ := hu.unit
  let l : Matrix.SpecialLinearGroup (Fin 3) R :=
    Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 3) ≠ 0 by decide)
      (b 1 0 * (↑a⁻¹ : R))
  let d : Matrix.SpecialLinearGroup (Fin 3) R :=
    unitEntry_diagonalUnitPair a
  let u : Matrix.SpecialLinearGroup (Fin 3) R :=
    Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 3) ≠ 1 by decide)
      ((↑a⁻¹ : R) * b 0 1)
  have hl : l ∈ StabilizedBlockReduction.elementaryThreeSubgroup R :=
    unitEntry_root_mem 1 0 (by decide) _
  have hd : d ∈ StabilizedBlockReduction.elementaryThreeSubgroup R :=
    unitEntry_diagonalUnitPair_mem a
  have hu' : u ∈ StabilizedBlockReduction.elementaryThreeSubgroup R :=
    unitEntry_root_mem 0 1 (by decide) _
  have hdet : b 0 0 * b 1 1 - b 0 1 * b 1 0 = 1 := by
    have hb := b.property
    rw [Matrix.det_fin_three] at hb
    simpa only [Fin.isValue, hrow, ↓reduceIte, mul_one, hcolumn, Fin.reduceEq, mul_zero, sub_zero,
      add_zero, zero_mul] using hb
  have hleft : (↑hu.unit⁻¹ : R) * b 0 0 = 1 := hu.val_inv_mul
  have hright : b 0 0 * (↑hu.unit⁻¹ : R) = 1 := by
    simpa only [mul_comm] using hleft
  have hzeroOne : b 0 1 = b 0 0 * ((↑hu.unit⁻¹ : R) * b 0 1) := by
    calc
      b 0 1 = 1 * b 0 1 := by ring
      _ = (b 0 0 * (↑hu.unit⁻¹ : R)) * b 0 1 := by rw [hright]
      _ = b 0 0 * ((↑hu.unit⁻¹ : R) * b 0 1) := by ring
  have honeZero : b 1 0 = b 1 0 * (↑hu.unit⁻¹ : R) * b 0 0 := by
    calc
      b 1 0 = b 1 0 * 1 := by ring
      _ = b 1 0 * ((↑hu.unit⁻¹ : R) * b 0 0) := by rw [hleft]
      _ = b 1 0 * (↑hu.unit⁻¹ : R) * b 0 0 := by ring
  have honeOne : b 1 1 =
      b 1 0 * ((↑hu.unit⁻¹ : R) * b 0 1) + (↑hu.unit⁻¹ : R) := by
    linear_combination
      (↑hu.unit⁻¹ : R) * hdet - b 1 1 * hleft
  have hb : b = l * d * u := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [l, d, u, unitEntry_diagonalUnitPair_apply,
        Matrix.SpecialLinearGroup.transvection_coe,
        Matrix.mul_apply, Fin.sum_univ_succ,
        Matrix.single_apply, Matrix.one_apply,
        hrow, hcolumn, a, ← hzeroOne, ← honeZero, ← honeOne]
  rw [hb]
  exact (StabilizedBlockReduction.elementaryThreeSubgroup R).mul_mem
    ((StabilizedBlockReduction.elementaryThreeSubgroup R).mul_mem hl hd) hu'

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennickeBlock_mem_of_isUnit_topLeft
    {R : Type*} [CommRing R]
    (a b c d : R) (hdet : a * d - b * c = 1) (ha : IsUnit a) :
    MennickeIdentity.mennickeBlock a b c d hdet ∈
      StabilizedBlockReduction.elementaryThreeSubgroup R := by
  apply stabilizedTwoByTwo_mem_elementaryThree_of_topLeft_isUnit
    (MennickeIdentity.mennickeBlock a b c d hdet)
  · intro j
    fin_cases j <;> simp [MennickeIdentity.mennickeBlock]
  · intro i
    fin_cases i <;> simp [MennickeIdentity.mennickeBlock]
  · exact ha

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennickeBlock_mem_of_isUnit_topRight
    {R : Type*} [CommRing R]
    (a b c d : R) (hdet : a * d - b * c = 1) (hb : IsUnit b) :
    MennickeIdentity.mennickeBlock a b c d hdet ∈
      StabilizedBlockReduction.elementaryThreeSubgroup R := by
  let B := MennickeIdentity.mennickeBlock a b c d hdet
  let E := StabilizedBlockReduction.elementaryThreeSubgroup R
  let J := MennickeIdentity.mennickeRotation (R := R)
  have hroot : MennickeIdentity.ContainsElementaryRoots E := by
    intro i j hij r
    exact Subgroup.subset_closure ⟨i, j, hij, r, rfl⟩
  have hJ : J ∈ E := MennickeIdentity.mennickeRotation_mem E hroot
  have hrow : ∀ j : Fin 3, (B * J) 2 j = if j = 2 then 1 else 0 := by
    intro j
    rw [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases j <;>
      simp [B, J, MennickeIdentity.mennickeBlock,
        MennickeIdentity.mennickeRotation,
        Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.transvection_coe,
        Matrix.mul_apply, Fin.sum_univ_succ,
        Matrix.single_apply, Matrix.one_apply]
  have hcolumn : ∀ i : Fin 3, (B * J) i 2 = if i = 2 then 1 else 0 := by
    intro i
    rw [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;>
      simp [B, J, MennickeIdentity.mennickeBlock,
        MennickeIdentity.mennickeRotation,
        Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.transvection_coe,
        Matrix.mul_apply, Fin.sum_univ_succ,
        Matrix.single_apply, Matrix.one_apply]
  have htop : IsUnit ((B * J) 0 0) := by
    have hentry : (B * J) 0 0 = -b := by
      rw [Matrix.SpecialLinearGroup.coe_mul]
      simp only [MennickeIdentity.mennickeBlock, MennickeIdentity.mennickeRotation, Fin.isValue,
        Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
        of_apply, cons_val', cons_val_fin_one, cons_val_zero, Matrix.add_apply, Matrix.one_apply,
        single_apply, Fin.sum_univ_succ, one_ne_zero, and_false, ↓reduceIte, add_zero, false_and,
        mul_ite, mul_one, mul_zero, Fin.succ_zero_eq_one, and_true, true_and, Finset.univ_unique,
        Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_one_eq_two, Fin.reduceEq,
        Finset.sum_ite_eq', Finset.mem_univ, zero_add, mul_neg, neg_add_rev, zero_ne_one, neg_zero,
        add_neg_cancel, cons_val_succ, Fin.succ_ne_zero, zero_mul, Finset.sum_const_zero, B, J]
    rw [hentry]
    exact hb.neg
  have hBJ : B * J ∈ E :=
    stabilizedTwoByTwo_mem_elementaryThree_of_topLeft_isUnit
      (B * J) hrow hcolumn htop
  have hB : B ∈ E := by
    have h := E.mul_mem hBJ (E.inv_mem hJ)
    simpa only [mul_inv_cancel_right] using h
  exact hB

end

section

open Matrix Polynomial
open MennickeIdentity StabilizedBlockReduction

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennickeBlock_X_topRight_constant_isUnit
    {A : Type u} [CommRing A]
    (a g p : Polynomial A)
    (hdet : a * X - g * p = 1) :
    IsUnit (g.coeff 0) := by
  have hz := congrArg (Polynomial.eval (0 : A)) hdet
  have hproduct : -(g.coeff 0 * p.coeff 0) = 1 := by
    simpa only [coeff_zero_eq_eval_zero, eval_sub, eval_mul, eval_X, mul_zero, zero_sub,
      eval_one] using hz
  apply isUnit_iff_exists_inv.mpr
  refine ⟨-(p.coeff 0), ?_⟩
  simpa only [mul_neg] using hproduct

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennickeBlock_X_constant_shear_det
    {A : Type u} [CommRing A]
    (a g p : Polynomial A)
    (hdet : a * X - g * p = 1) :
    (a - g.divX * p) * X - C (g.coeff 0) * p = 1 := by
  have hdivide := Polynomial.divX_mul_X_add g
  linear_combination hdet - p * hdivide

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennickeBlock_X_constant_shear_mul
    {A : Type u} [CommRing A]
    (a g p : Polynomial A)
    (hdet : a * X - g * p = 1) :
    mennickeBlock (a - g.divX * p) (C (g.coeff 0)) p X
        (mennickeBlock_X_constant_shear_det a g p hdet) =
      Matrix.SpecialLinearGroup.transvection
          (show (0 : Fin 3) ≠ 1 by decide) (-g.divX) *
        mennickeBlock a g p X hdet := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [mennickeBlock,
      Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply, Matrix.single_apply]
  · ring
  · have hdivide := Polynomial.divX_mul_X_add g
    linear_combination hdivide

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennickeBlock_X_mem
    {A : Type u} [CommRing A]
    (a g p : Polynomial A)
    (hdet : a * X - g * p = 1) :
    mennickeBlock a g p X hdet ∈
      elementaryThreeSubgroup (Polynomial A) := by
  have hunit : IsUnit (g.coeff 0) :=
    mennickeBlock_X_topRight_constant_isUnit a g p hdet
  have hnormalized :
      mennickeBlock (a - g.divX * p) (C (g.coeff 0)) p X
        (mennickeBlock_X_constant_shear_det a g p hdet) ∈
          elementaryThreeSubgroup (Polynomial A) :=
    mennickeBlock_mem_of_isUnit_topRight
      (a - g.divX * p) (C (g.coeff 0)) p X
      (mennickeBlock_X_constant_shear_det a g p hdet)
      (Polynomial.isUnit_C.mpr hunit)
  have hroot :
      Matrix.SpecialLinearGroup.transvection
          (show (0 : Fin 3) ≠ 1 by decide) (-g.divX) ∈
        elementaryThreeSubgroup (Polynomial A) :=
    Subgroup.subset_closure
      ⟨0, 1, (by decide), -g.divX, rfl⟩
  rw [mennickeBlock_X_constant_shear_mul a g p hdet] at hnormalized
  exact (elementaryThreeSubgroup (Polynomial A)).mul_mem_cancel_left
    hroot |>.mp hnormalized

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennickeBlock_mem_of_isUnit_bottomRight
    {R : Type*} [CommRing R]
    (a b c d : R) (hdet : a * d - b * c = 1) (hd : IsUnit d) :
    mennickeBlock a b c d hdet ∈
      elementaryThreeSubgroup R := by
  let E := elementaryThreeSubgroup R
  let J := mennickeRotation (R := R)
  have hroot : ContainsElementaryRoots E := by
    intro i j hij r
    exact Subgroup.subset_closure ⟨i, j, hij, r, rfl⟩
  have hJ : J ∈ E := mennickeRotation_mem E hroot
  have hswapped : d * a - b * c = 1 := by
    linear_combination hdet
  have hsource : d * a - (-c) * (-b) = 1 := by
    linear_combination hdet
  have hunit : mennickeBlock d (-c) (-b) a hsource ∈ E :=
    mennickeBlock_mem_of_isUnit_topLeft d (-c) (-b) a hsource hd
  have hconjugate := mennickeBlock_rotation_conjugate
    d b c a hswapped
  have hmem := E.mul_mem (E.mul_mem hJ hunit) (E.inv_mem hJ)
  simpa [J, hconjugate] using hmem

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennickeBlock_mem_of_bottomRight_X_pow
    {A : Type u} [CommRing A]
    (a b c : Polynomial A) (n : ℕ)
    (hdet : a * (Polynomial.X : Polynomial A) ^ n - b * c = 1) :
    mennickeBlock a b c (Polynomial.X ^ n) hdet ∈
      elementaryThreeSubgroup (Polynomial A) := by
  let E := elementaryThreeSubgroup (Polynomial A)
  have hroots : ContainsElementaryRoots E := by
    intro i j hij r
    exact Subgroup.subset_closure ⟨i, j, hij, r, rfl⟩
  induction n generalizing a b c with
  | zero =>
      simpa only [pow_zero] using mennickeBlock_mem_of_isUnit_bottomRight
        a b c 1 (by simpa only [mul_one, pow_zero] using hdet) isUnit_one
  | succ n ih =>
      have hswap :
          (Polynomial.X : Polynomial A) * Polynomial.X ^ n * a -
            b * c = 1 := by
        calc
          (Polynomial.X : Polynomial A) * Polynomial.X ^ n * a - b * c =
              a * Polynomial.X ^ (n + 1) - b * c := by
            rw [pow_succ]
            ring
          _ = 1 := hdet
      have hleft :
          mennickeBlock (Polynomial.X ^ n * a) b c Polynomial.X
            (mennicke_swapped_left_factor_det
              Polynomial.X (Polynomial.X ^ n) b c a hswap) ∈ E :=
        mennickeBlock_X_mem (Polynomial.X ^ n * a) b c _
      have hright :
          mennickeBlock (Polynomial.X * a) b c (Polynomial.X ^ n)
            (mennicke_swapped_right_factor_det
              Polynomial.X (Polynomial.X ^ n) b c a hswap) ∈ E :=
        ih (Polynomial.X * a) b c _
      have htarget := mennicke_swapped_block_mem_of_factors
        E hroots Polynomial.X (Polynomial.X ^ n) b c a hswap
        hleft hright
      simpa only [pow_succ, mul_comm] using htarget

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennickeBlock_mem_of_topLeft_X_pow
    {A : Type u} [CommRing A]
    (n : ℕ) (b c d : Polynomial A)
    (hdet : (Polynomial.X : Polynomial A) ^ n * d - b * c = 1) :
    mennickeBlock (Polynomial.X ^ n) b c d hdet ∈
      elementaryThreeSubgroup (Polynomial A) := by
  let E := elementaryThreeSubgroup (Polynomial A)
  have hroots : ContainsElementaryRoots E := by
    intro i j hij r
    exact Subgroup.subset_closure ⟨i, j, hij, r, rfl⟩
  have hrot : mennickeRotation (R := Polynomial A) ∈ E :=
    mennickeRotation_mem E hroots
  have hsource : d * Polynomial.X ^ n - (-c) * (-b) = 1 := by
    linear_combination hdet
  have hblock := mennickeBlock_mem_of_bottomRight_X_pow
    d (-c) (-b) n hsource
  have hconjugate :
      mennickeRotation *
          mennickeBlock d (-c) (-b) (Polynomial.X ^ n) hsource *
          mennickeRotation⁻¹ ∈ E :=
    E.mul_mem (E.mul_mem hrot hblock) (E.inv_mem hrot)
  have hrotation := mennickeBlock_rotation_conjugate d b c
    (Polynomial.X ^ n) (by linear_combination hdet)
  simpa only [hrotation] using hconjugate

end

section

open Matrix
open Polynomial
open StabilizedBlockReduction

universe u

variable {R : Type u} [CommRing R]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def suslinSignedSwap : Matrix.SpecialLinearGroup (Fin 2) R :=
  Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 2) ≠ 1 by decide) 1 *
    Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 2) ≠ 0 by decide) (-1) *
    Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 2) ≠ 1 by decide) 1

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_stabilized_signedSwap_mem :
    stabilizedTwoHom (suslinSignedSwap (R := R)) ∈
      elementaryThreeSubgroup R := by
  unfold suslinSignedSwap
  simp only [map_mul]
  exact (elementaryThreeSubgroup R).mul_mem
    ((elementaryThreeSubgroup R).mul_mem
      (stabilizedTwoHom_transvection_mem 0 1 (by decide) 1)
      (stabilizedTwoHom_transvection_mem 1 0 (by decide) (-1)))
    (stabilizedTwoHom_transvection_mem 0 1 (by decide) 1)



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem suslinSignedSwap_zero_zero : suslinSignedSwap (R := R) 0 0 = 0 := by
  simp only [suslinSignedSwap, Fin.isValue, Matrix.SpecialLinearGroup.coe_mul,
    SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply,
    single_apply, true_and, Fin.sum_univ_succ, ↓reduceIte, one_ne_zero, add_zero, false_and,
    mul_ite, mul_one, mul_zero, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
    Fin.succ_zero_eq_one, zero_ne_one, zero_add, one_mul, and_false, Finset.sum_ite_eq',
    Finset.mem_univ, add_neg_cancel]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem suslinSignedSwap_zero_one : suslinSignedSwap (R := R) 0 1 = 1 := by
  simp only [suslinSignedSwap, Fin.isValue, Matrix.SpecialLinearGroup.coe_mul,
    SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply,
    single_apply, true_and, Fin.sum_univ_succ, ↓reduceIte, one_ne_zero, add_zero, false_and,
    mul_ite, mul_one, mul_zero, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
    Fin.succ_zero_eq_one, zero_ne_one, zero_add, one_mul, and_true, add_neg_cancel]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem suslinSignedSwap_one_zero : suslinSignedSwap (R := R) 1 0 = -1 := by
  simp only [suslinSignedSwap, Fin.isValue, Matrix.SpecialLinearGroup.coe_mul,
    SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply,
    zero_ne_one, false_and, not_false_eq_true, single_apply_of_ne, add_zero, single_apply, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, true_and, one_ne_zero,
    and_false, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', zero_add]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem suslinSignedSwap_one_one : suslinSignedSwap (R := R) 1 1 = 0 := by
  simp only [suslinSignedSwap, Fin.isValue, Matrix.SpecialLinearGroup.coe_mul,
    SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply,
    zero_ne_one, false_and, not_false_eq_true, single_apply_of_ne, add_zero, single_apply, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, true_and, and_true,
    Fin.sum_univ_succ, one_ne_zero, zero_add, mul_one, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, Fin.succ_zero_eq_one, neg_add_cancel]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem suslin_mul_signedSwap_zero_one
    (b : Matrix.SpecialLinearGroup (Fin 2) R) :
    (b * suslinSignedSwap (R := R)) 0 1 = b 0 0 := by
  simp only [Fin.isValue, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_succ,
    suslinSignedSwap_zero_one, mul_one, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, Fin.succ_zero_eq_one, suslinSignedSwap_one_one, mul_zero, add_zero]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem suslin_mul_signedSwap_one_zero
    (b : Matrix.SpecialLinearGroup (Fin 2) R) :
    (b * suslinSignedSwap (R := R)) 1 0 = -(b 1 1) := by
  simp only [Fin.isValue, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_succ,
    suslinSignedSwap_zero_zero, mul_zero, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, Fin.succ_zero_eq_one, suslinSignedSwap_one_zero, mul_neg, mul_one,
    zero_add]













/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_local_polynomial_specialLinear_constant_unit_dichotomy
    {A : Type u} [CommRing A] [IsLocalRing A]
    (b : Matrix.SpecialLinearGroup (Fin 2) (Polynomial A)) :
    (IsUnit ((b 0 0).coeff 0) ∧ IsUnit ((b 1 1).coeff 0)) ∨
      (IsUnit ((b 0 1).coeff 0) ∧ IsUnit ((b 1 0).coeff 0)) := by
  have hdet := congrArg (Polynomial.eval 0) b.property
  rw [Matrix.det_fin_two] at hdet
  have hdet0 :
      (b 0 0).coeff 0 * (b 1 1).coeff 0 -
        (b 0 1).coeff 0 * (b 1 0).coeff 0 = (1 : A) := by
    simpa only [Fin.isValue, eval_sub, eval_mul, ← coeff_zero_eq_eval_zero, eval_one] using hdet
  have hsum : IsUnit
      ((b 0 0).coeff 0 * (b 1 1).coeff 0 +
        -((b 0 1).coeff 0 * (b 1 0).coeff 0)) := by
    rw [← sub_eq_add_neg, hdet0]
    exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with hdiag | hoff
  · exact Or.inl
      ⟨isUnit_of_mul_isUnit_left hdiag,
        isUnit_of_mul_isUnit_right hdiag⟩
  · have hprod : IsUnit
        ((b 0 1).coeff 0 * (b 1 0).coeff 0) := by
      simpa only [Fin.isValue, IsUnit.mul_iff, neg_neg] using hoff.neg
    exact Or.inr
      ⟨isUnit_of_mul_isUnit_left hprod,
        isUnit_of_mul_isUnit_right hprod⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_local_stabilizedTwo_unit_offdiag_normalization
    {A : Type u} [CommRing A] [IsLocalRing A]
    (b : Matrix.SpecialLinearGroup (Fin 2) (Polynomial A)) :
    ∃ (b' : Matrix.SpecialLinearGroup (Fin 2) (Polynomial A))
      (e : Matrix.SpecialLinearGroup (Fin 3) (Polynomial A)),
      e ∈ elementaryThreeSubgroup (Polynomial A) ∧
        stabilizedTwoHom b = stabilizedTwoHom b' * e ∧
        IsUnit ((b' 0 1).coeff 0) ∧
        IsUnit ((b' 1 0).coeff 0) := by
  rcases suslin_local_polynomial_specialLinear_constant_unit_dichotomy b with
    hdiag | hoff
  · let j : Matrix.SpecialLinearGroup (Fin 2) (Polynomial A) :=
      suslinSignedSwap
    have hj : stabilizedTwoHom j ∈
        elementaryThreeSubgroup (Polynomial A) :=
      suslin_stabilized_signedSwap_mem
    refine ⟨b * j, (stabilizedTwoHom j)⁻¹,
      (elementaryThreeSubgroup (Polynomial A)).inv_mem hj,
      ?_, ?_, ?_⟩
    · simp [map_mul]
    · simpa [j] using hdiag.1
    · simpa [j] using hdiag.2.neg
  · exact ⟨b, 1, (elementaryThreeSubgroup (Polynomial A)).one_mem,
      by simp, hoff.1, hoff.2⟩

end

section

open Polynomial

universe u v

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem valuation_finset_exists_dvd_all
    {R : Type u} [CommRing R] [PreValuationRing R]
    {ι : Type v} (s : Finset ι) (x : ι → R)
    (hs : s.Nonempty) :
    ∃ i ∈ s, ∀ j ∈ s, x i ∣ x j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.not_nonempty_empty] at hs
  | @insert a s ha ih =>
      by_cases hsempty : s.Nonempty
      · obtain ⟨b, hb, hmin⟩ := ih hsempty
        rcases ValuationRing.dvd_total (x a) (x b) with hab | hba
        · refine ⟨a, Finset.mem_insert_self _ _, ?_⟩
          intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact dvd_rfl
          · exact hab.trans (hmin j hj)
        · refine ⟨b, Finset.mem_insert_of_mem hb, ?_⟩
          intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact hba
          · exact hmin j hj
      · have hz : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsempty
        subst s
        exact ⟨a,
          by simp only [insert_empty_eq, Finset.mem_singleton],
          by simp only [insert_empty_eq, Finset.mem_singleton,
            forall_eq, dvd_refl]⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem valuation_polynomial_exists_primitive_factor
    {R : Type u} [CommRing R] [IsDomain R] [PreValuationRing R]
    (f : Polynomial R) (hf : f ≠ 0) :
    ∃ (c : R) (g : Polynomial R) (i : ℕ),
      c ≠ 0 ∧ f = Polynomial.C c * g ∧
        g.coeff i = 1 ∧ g.IsPrimitive ∧ g.natDegree = f.natDegree := by
  classical
  have hsupport : f.support.Nonempty := Polynomial.support_nonempty.mpr hf
  obtain ⟨i, hi, hmin⟩ :=
    valuation_finset_exists_dvd_all f.support f.coeff hsupport
  let c : R := f.coeff i
  have hc : c ≠ 0 := Polynomial.mem_support_iff.mp hi
  have hdiv : ∀ n : ℕ, c ∣ f.coeff n := by
    intro n
    by_cases hn : n ∈ f.support
    · exact hmin n hn
    · have hzero : f.coeff n = 0 :=
        Classical.not_not.mp (mt Polynomial.mem_support_iff.mpr hn)
      rw [hzero]
      exact dvd_zero c
  obtain ⟨g, hg⟩ := (Polynomial.C_dvd_iff_dvd_coeff c f).mpr hdiv
  have heq : f = Polynomial.C c * g := hg
  have hcoeff : g.coeff i = 1 := by
    apply mul_left_cancel₀ hc
    have h := congrArg (fun p : Polynomial R => p.coeff i) heq
    rw [Polynomial.coeff_C_mul] at h
    change c = c * g.coeff i at h
    simpa only [mul_one] using h.symm
  have hprimitive : g.IsPrimitive := by
    intro r hr
    have hri : r ∣ g.coeff i :=
      (Polynomial.C_dvd_iff_dvd_coeff r g).mp hr i
    rw [hcoeff] at hri
    exact isUnit_of_dvd_one hri
  refine ⟨c, g, i, hc, heq, hcoeff, hprimitive, ?_⟩
  rw [heq, Polynomial.natDegree_C_mul hc]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem dvr_uniformizer_factor_with_classification
    {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ)
    {x : R} (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : Rˣ),
      x = (u : R) * ϖ ^ n ∧
        (IsUnit x ↔ n = 0) ∧
        (∀ k : ℕ, ϖ ^ k ∣ x ↔ k ≤ n) ∧
        IsDiscreteValuationRing.addVal R x = n := by
  obtain ⟨n, u, rfl⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  refine ⟨n, u, rfl, ?_, ?_, ?_⟩
  · simp only [IsUnit.mul_iff, Units.isUnit, isUnit_pow_iff_of_not_isUnit hϖ.not_isUnit, true_and]
  · intro k
    rw [Units.dvd_mul_left,
      pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit]
  · exact IsDiscreteValuationRing.addVal_def' u hϖ n

end

section

open Matrix Polynomial
open MennickeIdentity StabilizedBlockReduction

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_uniformizer_column_shear
    {R : Type u} [CommRing R]
    (a b c d r : R) (hdet : a * d - b * c = 1) :
    let hdet' : a * (d - r * c) - (b - r * a) * c = 1 := by
      linear_combination hdet
    mennickeBlock a b c d hdet *
        Matrix.SpecialLinearGroup.transvection
          (show (0 : Fin 3) ≠ 1 by decide) (-r) =
      mennickeBlock a (b - r * a) c (d - r * c) hdet' := by
  dsimp
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [mennickeBlock,
      Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply,
      Matrix.single_apply] <;> ring

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_uniformizer_mennickeBlock_mem_elementary
    {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    {π : A} (hπ : Irreducible π)
    (g p q : Polynomial A)
    (hdet : Polynomial.C π * q - g * p = 1) :
    mennickeBlock (Polynomial.C π) g p q hdet ∈
      elementaryThreeSubgroup (Polynomial A) := by
  obtain ⟨u, h, hu, hg⟩ :=
    suslin_dvr_uniformizer_polynomial_unit_decomposition_of_determinant
      hπ g p q hdet
  have hpivot : IsUnit (g - h * Polynomial.C π) := by
    rw [hg]
    have heq :
        Polynomial.C u + Polynomial.C π * h - h * Polynomial.C π =
          Polynomial.C u := by
      ring
    rw [heq]
    exact Polynomial.isUnit_C.mpr hu
  let hdet' :
      Polynomial.C π * (q - h * p) -
          (g - h * Polynomial.C π) * p = 1 := by
    linear_combination hdet
  have hnew :
      mennickeBlock (Polynomial.C π)
          (g - h * Polynomial.C π) p (q - h * p) hdet' ∈
        elementaryThreeSubgroup (Polynomial A) :=
    mennickeBlock_mem_of_isUnit_topRight
      (Polynomial.C π) (g - h * Polynomial.C π) p (q - h * p)
      hdet' hpivot
  have hroot :
      Matrix.SpecialLinearGroup.transvection
          (show (0 : Fin 3) ≠ 1 by decide) (-h) ∈
        elementaryThreeSubgroup (Polynomial A) :=
    Subgroup.subset_closure ⟨0, 1, by decide, -h, rfl⟩
  have hproduct :
      mennickeBlock (Polynomial.C π) g p q hdet *
        Matrix.SpecialLinearGroup.transvection
          (show (0 : Fin 3) ≠ 1 by decide) (-h) ∈
        elementaryThreeSubgroup (Polynomial A) := by
    rw [suslin_uniformizer_column_shear]
    exact hnew
  have hcancel := (elementaryThreeSubgroup (Polynomial A)).mul_mem
    hproduct ((elementaryThreeSubgroup (Polynomial A)).inv_mem hroot)
  simpa only [Fin.isValue, mul_inv_cancel_right] using hcancel

end

section

namespace ValuationPowerCase

open Polynomial
open MennickeIdentity
open StabilizedBlockReduction

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem elementaryThree_containsElementaryRoots
    (R : Type u) [CommRing R] :
    ContainsElementaryRoots (elementaryThreeSubgroup R) := by
  intro i j hij r
  exact Subgroup.subset_closure ⟨i, j, hij, r, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem nonzero_eq_unit_mul_uniformizer_pow
    {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    {π a : A} (hπ : Irreducible π) (ha : a ≠ 0) :
    ∃ (n : ℕ) (u : Aˣ), a = (u : A) * π ^ n := by
  obtain ⟨n, u, hu, _, _, _⟩ :=
    dvr_uniformizer_factor_with_classification hπ ha
  exact ⟨n, u, hu⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennickeBlock_mem_of_unit_mul_uniformizer_pow
    {A : Type u} [CommRing A]
    {π : A} (_hπ : Irreducible π)
    (huniformizer : ∀ (g p q : Polynomial A)
      (hdet : Polynomial.C π * q - g * p = 1),
      mennickeBlock (Polynomial.C π) g p q hdet ∈
        elementaryThreeSubgroup (Polynomial A))
    (hunit : ∀ (v : Aˣ) (g p q : Polynomial A)
      (hdet : Polynomial.C (v : A) * q - g * p = 1),
      mennickeBlock (Polynomial.C (v : A)) g p q hdet ∈
        elementaryThreeSubgroup (Polynomial A))
    (n : ℕ) (v : Aˣ) (g p q : Polynomial A)
    (hdet : Polynomial.C ((v : A) * π ^ n) * q - g * p = 1) :
    mennickeBlock (Polynomial.C ((v : A) * π ^ n)) g p q hdet ∈
      elementaryThreeSubgroup (Polynomial A) := by
  induction n generalizing g p q with
  | zero =>
      have hdet' : Polynomial.C (v : A) * q - g * p = 1 := by
        simpa only [pow_zero, mul_one] using hdet
      simpa only [pow_zero, mul_one] using hunit v g p q hdet'
  | succ n ih =>
      let a : Polynomial A := Polynomial.C π
      let ap : Polynomial A := Polynomial.C ((v : A) * π ^ n)
      have hfactor :
          Polynomial.C ((v : A) * π ^ (n + 1)) = a * ap := by
        dsimp [a, ap]
        rw [← Polynomial.C_mul]
        congr 1
        rw [pow_succ]
        ring
      have hdet' : a * ap * q - g * p = 1 := by
        rw [← hfactor]
        exact hdet
      have hleft :
          mennickeBlock a g p (ap * q)
            (mennicke_left_factor_det a ap g p q hdet') ∈
              elementaryThreeSubgroup (Polynomial A) := by
        dsimp [a, ap]
        exact huniformizer g p (Polynomial.C ((v : A) * π ^ n) * q)
          (mennicke_left_factor_det
            (Polynomial.C π) (Polynomial.C ((v : A) * π ^ n))
            g p q hdet')
      have hright :
          mennickeBlock ap g p (a * q)
            (mennicke_right_factor_det a ap g p q hdet') ∈
              elementaryThreeSubgroup (Polynomial A) := by
        dsimp [a, ap]
        exact ih g p (Polynomial.C π * q)
          (mennicke_right_factor_det
            (Polynomial.C π) (Polynomial.C ((v : A) * π ^ n))
            g p q hdet')
      have h := mennicke_block_mem_of_factors
        (elementaryThreeSubgroup (Polynomial A))
        (elementaryThree_containsElementaryRoots (Polynomial A))
        a ap g p q hdet' hleft hright
      have hblocks :
          mennickeBlock (Polynomial.C ((v : A) * π ^ (n + 1)))
              g p q hdet =
            mennickeBlock (a * ap) g p q hdet' := by
        apply Matrix.SpecialLinearGroup.ext
        intro i j
        change
          !![Polynomial.C ((v : A) * π ^ (n + 1)), g, 0;
            p, q, 0; 0, 0, 1] i j =
          !![a * ap, g, 0; p, q, 0; 0, 0, 1] i j
        rw [hfactor]
      rw [hblocks]
      exact h

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennickeBlock_zero_constant_mem
    {A : Type u} [CommRing A]
    (g p q : Polynomial A)
    (hdet : Polynomial.C (0 : A) * q - g * p = 1) :
    mennickeBlock (Polynomial.C (0 : A)) g p q hdet ∈
      elementaryThreeSubgroup (Polynomial A) := by
  have hg : IsUnit g := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨-p, ?_⟩
    simpa only [mul_neg, map_zero, zero_mul, zero_sub] using hdet
  exact mennickeBlock_mem_of_isUnit_topRight
    (Polynomial.C (0 : A)) g p q hdet hg

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennickeBlock_constant_mem_of_uniformizer_case
    {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    {π : A} (hπ : Irreducible π)
    (huniformizer : ∀ (g p q : Polynomial A)
      (hdet : Polynomial.C π * q - g * p = 1),
      mennickeBlock (Polynomial.C π) g p q hdet ∈
        elementaryThreeSubgroup (Polynomial A))
    (a : A) (g p q : Polynomial A)
    (hdet : Polynomial.C a * q - g * p = 1) :
    mennickeBlock (Polynomial.C a) g p q hdet ∈
      elementaryThreeSubgroup (Polynomial A) := by
  by_cases ha : a = 0
  · subst a
    exact mennickeBlock_zero_constant_mem g p q hdet
  · obtain ⟨n, v, rfl⟩ :=
      nonzero_eq_unit_mul_uniformizer_pow hπ ha
    apply mennickeBlock_mem_of_unit_mul_uniformizer_pow
      hπ huniformizer
    · intro w b c d hdet'
      exact mennickeBlock_mem_of_isUnit_topLeft
        (Polynomial.C (w : A)) b c d hdet'
        (Polynomial.isUnit_C.mpr w.isUnit)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennickeBlock_constant_mem
    {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    (a : A) (g p q : Polynomial A)
    (hdet : Polynomial.C a * q - g * p = 1) :
    mennickeBlock (Polynomial.C a) g p q hdet ∈
      elementaryThreeSubgroup (Polynomial A) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  apply mennickeBlock_constant_mem_of_uniformizer_case hπ
  · intro b c d hdet'
    exact suslin_uniformizer_mennickeBlock_mem_elementary
      hπ b c d hdet'

end ValuationPowerCase

end

section

open Polynomial

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem isUnit_sub_mul_of_isLocalRing
    {A : Type*} [CommRing A] [IsLocalRing A]
    {u c : A} (hu : IsUnit u) (hc : ¬ IsUnit c) (b : A) :
    IsUnit (u - c * b) := by
  by_contra h
  have hcb : ¬ IsUnit (c * b) := fun hb =>
    hc (isUnit_of_mul_isUnit_left hb)
  have hsum := IsLocalRing.nonunits_add h hcb
  apply hsum
  simpa only [sub_add_cancel] using hu

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomial_valuation_coefficient_ascent
    {A : Type*} [CommRing A] [IsLocalRing A]
    (f g : Polynomial A) (c : A) (m : ℕ)
    (hdeg : f.natDegree < g.natDegree)
    (hunit : IsUnit (f.coeff m))
    (hc : ¬ IsUnit c)
    (hlead : f.leadingCoeff = c * g.leadingCoeff) :
    let s := g.natDegree - f.natDegree
    let f' := X ^ s * f - C c * g
    f'.natDegree < g.natDegree ∧
      IsUnit (f'.coeff (s + m)) ∧ m < s + m := by
  dsimp
  have hf : f ≠ 0 := by
    intro h
    simp only [h, coeff_zero, isUnit_zero_iff, zero_ne_one] at hunit
  have hshift : 0 < g.natDegree - f.natDegree := Nat.sub_pos_of_lt hdeg
  have hm : m ≤ f.natDegree := le_natDegree_of_ne_zero hunit.ne_zero
  have hsdeg : f.natDegree + (g.natDegree - f.natDegree) = g.natDegree :=
    Nat.add_sub_of_le (Nat.le_of_lt hdeg)
  have hnonzero : c * g.leadingCoeff ≠ 0 := by
    rw [← hlead]
    exact leadingCoeff_ne_zero.mpr hf
  have hunit' :
      IsUnit
        ((X ^ (g.natDegree - f.natDegree) * f - C c * g).coeff
          (g.natDegree - f.natDegree + m)) := by
    rw [coeff_sub, coeff_X_pow_mul', coeff_C_mul,
      ite_eq_left (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact isUnit_sub_mul_of_isLocalRing hunit hc _
  have hf' : X ^ (g.natDegree - f.natDegree) * f - C c * g ≠ 0 := by
    intro h
    simp only [h, coeff_zero, isUnit_zero_iff, zero_ne_one] at hunit'
  have hpnat :
      (X ^ (g.natDegree - f.natDegree) * f).natDegree =
        g.natDegree := by
    rw [natDegree_X_pow_mul _ hf, hsdeg]
  have hqnat : (C c * g).natDegree = g.natDegree :=
    natDegree_C_mul_of_mul_ne_zero hnonzero
  have hpzero : X ^ (g.natDegree - f.natDegree) * f ≠ 0 := by
    intro h
    have := congrArg natDegree h
    simp only [hpnat, natDegree_zero, Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hdeg)] at this
  have hdegrees :
      (X ^ (g.natDegree - f.natDegree) * f).degree =
        (C c * g).degree := by
    rw [degree_eq_natDegree hpzero,
      degree_eq_natDegree (by
        intro h
        have := congrArg natDegree h
        simp only [hqnat, natDegree_zero,
          Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hdeg)] at this),
      hpnat, hqnat]
  have hlc :
      (X ^ (g.natDegree - f.natDegree) * f).leadingCoeff =
        (C c * g).leadingCoeff := by
    change
      (X ^ (g.natDegree - f.natDegree) * f).coeff
          (X ^ (g.natDegree - f.natDegree) * f).natDegree =
        (C c * g).coeff (C c * g).natDegree
    rw [hpnat, hqnat]
    conv_lhs =>
      arg 2
      rw [← hsdeg]
    rw [coeff_X_pow_mul, coeff_C_mul]
    exact hlead
  have hsmall :
      (X ^ (g.natDegree - f.natDegree) * f - C c * g).natDegree <
        g.natDegree := by
    apply (natDegree_lt_iff_degree_lt hf').mpr
    calc
      (X ^ (g.natDegree - f.natDegree) * f - C c * g).degree <
          (X ^ (g.natDegree - f.natDegree) * f).degree :=
        degree_sub_lt_left hdegrees hpzero hlc
      _ = (g.natDegree : WithBot ℕ) := by
        rw [degree_eq_natDegree hpzero, hpnat]
  exact ⟨hsmall, hunit', Nat.lt_add_of_pos_left hshift⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def valuationPrimitiveAscentStep
    {A : Type*} [CommRing A] (g f f' : Polynomial A) : Prop :=
  ∃ c : A, ¬ IsUnit c ∧
    f.leadingCoeff = c * g.leadingCoeff ∧
    f' = X ^ (g.natDegree - f.natDegree) * f - C c * g

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polynomial_unit_coefficient_ascent_measure_lt
    (degree m m' : ℕ)
    (hascent : m < m') (hbound : m' ≤ degree) :
    degree - m' < degree - m := by
  omega

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem valuation_primitive_ascent_terminates
    {A : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    (g f : Polynomial A) (m : ℕ)
    (hdeg : f.natDegree < g.natDegree)
    (hunit : IsUnit (f.coeff m)) :
    ∃ f' : Polynomial A, ∃ m' : ℕ,
      f'.natDegree < g.natDegree ∧
      IsUnit (f'.coeff m') ∧
      f'.leadingCoeff ∣ g.leadingCoeff ∧
      Relation.ReflTransGen (valuationPrimitiveAscentStep g) f f' := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (f : Polynomial A) (m : ℕ),
      g.natDegree - m = n →
      f.natDegree < g.natDegree →
      IsUnit (f.coeff m) →
      ∃ f' : Polynomial A, ∃ m' : ℕ,
        f'.natDegree < g.natDegree ∧
        IsUnit (f'.coeff m') ∧
        f'.leadingCoeff ∣ g.leadingCoeff ∧
        Relation.ReflTransGen (valuationPrimitiveAscentStep g) f f'
  have hall : ∀ n : ℕ, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f m hmeasure hsmall hunitm
      by_cases hdvd : f.leadingCoeff ∣ g.leadingCoeff
      · exact ⟨f, m, hsmall, hunitm, hdvd,
          Relation.ReflTransGen.refl⟩
      · have hreverse : g.leadingCoeff ∣ f.leadingCoeff :=
          (valuation_leadingCoeff_dvd_total f g).resolve_left hdvd
        obtain ⟨c, hc⟩ := hreverse
        have hlead : f.leadingCoeff = c * g.leadingCoeff := by
          simpa only [mul_comm] using hc
        have hcunit : ¬ IsUnit c := by
          intro hcu
          apply hdvd
          refine ⟨(↑hcu.unit⁻¹ : A), ?_⟩
          rw [hlead]
          calc
            g.leadingCoeff =
                (c * (↑hcu.unit⁻¹ : A)) * g.leadingCoeff := by
              rw [hcu.mul_val_inv, one_mul]
            _ = (c * g.leadingCoeff) * (↑hcu.unit⁻¹ : A) := by ring
        let s := g.natDegree - f.natDegree
        let f₁ := X ^ s * f - C c * g
        let m₁ := s + m
        obtain ⟨hf₁, hunit₁, hraise⟩ :=
          polynomial_valuation_coefficient_ascent f g c m
            hsmall hunitm hcunit hlead
        have hm₁ : m₁ ≤ g.natDegree :=
          (le_natDegree_of_ne_zero hunit₁.ne_zero).trans
            (Nat.le_of_lt hf₁)
        have hless : g.natDegree - m₁ < n := by
          rw [← hmeasure]
          exact polynomial_unit_coefficient_ascent_measure_lt
            g.natDegree m m₁ hraise hm₁
        obtain ⟨f₂, m₂, hsmall₂, hunit₂, hdvd₂, hchain₂⟩ :=
          ih (g.natDegree - m₁) hless f₁ m₁ rfl hf₁ hunit₁
        refine ⟨f₂, m₂, hsmall₂, hunit₂, hdvd₂,
          Relation.ReflTransGen.head ?_ hchain₂⟩
        exact ⟨c, hcunit, hlead, rfl⟩
  exact hall (g.natDegree - m) f m rfl hdeg hunit

end

namespace MennickeIdentity

open Matrix
open ConnesRigidity.StabilizedBlockReduction

universe u

variable {R : Type u} [CommRing R]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennicke_rowSecond_sub_det
    (a b c d q : R) (hdet : a * d - b * c = 1) :
    a * (d - q * b) - b * (c - q * a) = 1 := by
  linear_combination hdet

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennicke_columnFirst_sub_det
    (a b c d q : R) (hdet : a * d - b * c = 1) :
    (a - q * b) * d - b * (c - q * d) = 1 := by
  linear_combination hdet

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennickeBlock_rowSecond_sub_mul
    (a b c d q : R) (hdet : a * d - b * c = 1) :
    mennickeBlock a b (c - q * a) (d - q * b)
        (mennicke_rowSecond_sub_det a b c d q hdet) =
      Matrix.SpecialLinearGroup.transvection
        (show (1 : Fin 3) ≠ 0 by decide) (-q) *
        mennickeBlock a b c d hdet := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [mennickeBlock,
      Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply,
      Matrix.single_apply] <;> ring

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennickeBlock_columnFirst_sub_mul
    (a b c d q : R) (hdet : a * d - b * c = 1) :
    mennickeBlock (a - q * b) b (c - q * d) d
        (mennicke_columnFirst_sub_det a b c d q hdet) =
      mennickeBlock a b c d hdet *
        Matrix.SpecialLinearGroup.transvection
          (show (1 : Fin 3) ≠ 0 by decide) (-q) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [mennickeBlock,
      Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply,
      Matrix.single_apply] <;> ring

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem elementaryThree_contains_roots :
    ContainsElementaryRoots (elementaryThreeSubgroup R) := by
  intro i j h r
  exact Subgroup.subset_closure ⟨i, j, h, r, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennickeBlock_rowSecond_sub_mem_iff
    (a b c d q : R) (hdet : a * d - b * c = 1) :
    mennickeBlock a b (c - q * a) (d - q * b)
        (mennicke_rowSecond_sub_det a b c d q hdet) ∈
          elementaryThreeSubgroup R ↔
      mennickeBlock a b c d hdet ∈ elementaryThreeSubgroup R := by
  rw [mennickeBlock_rowSecond_sub_mul]
  exact (elementaryThreeSubgroup R).mul_mem_cancel_left
    (elementaryThree_contains_roots 1 0 (by decide) (-q))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennickeBlock_columnFirst_sub_mem_iff
    (a b c d q : R) (hdet : a * d - b * c = 1) :
    mennickeBlock (a - q * b) b (c - q * d) d
        (mennicke_columnFirst_sub_det a b c d q hdet) ∈
          elementaryThreeSubgroup R ↔
      mennickeBlock a b c d hdet ∈ elementaryThreeSubgroup R := by
  rw [mennickeBlock_columnFirst_sub_mul]
  exact (elementaryThreeSubgroup R).mul_mem_cancel_right
    (elementaryThree_contains_roots 1 0 (by decide) (-q))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennicke_ascent_row_det
    {A : Type u} [CommRing A]
    (f g p q t r : Polynomial A) (s : ℕ)
    (hdet : f * q - g * p = 1)
    (hq : q = Polynomial.X ^ s * r + t * g) :
    f * (Polynomial.X ^ s * r) - g * (p - t * f) = 1 := by
  rw [hq] at hdet
  linear_combination hdet

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennicke_ascent_good_det
    {A : Type u} [CommRing A]
    (f g p q t r : Polynomial A) (s : ℕ) (c : A)
    (hdet : f * q - g * p = 1)
    (hq : q = Polynomial.X ^ s * r + t * g) :
    (Polynomial.X ^ s * f - Polynomial.C c * g) * r -
      g * (p - t * f - Polynomial.C c * r) = 1 := by
  have h := mennicke_ascent_row_det f g p q t r s hdet hq
  linear_combination h

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennicke_ascent_monic_det
    {A : Type u} [CommRing A]
    (f g p q t r : Polynomial A) (s : ℕ)
    (hdet : f * q - g * p = 1)
    (hq : q = Polynomial.X ^ s * r + t * g) :
    (r * f) * Polynomial.X ^ s - g * (p - t * f) = 1 := by
  have h := mennicke_ascent_row_det f g p q t r s hdet hq
  linear_combination h

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennickeBlock_mem_of_primitive_ascent
    {A : Type u} [CommRing A]
    (f g p q t r : Polynomial A) (s : ℕ) (c : A)
    (hdet : f * q - g * p = 1)
    (hq : q = Polynomial.X ^ s * r + t * g)
    (hmonic : mennickeBlock (r * f) g (p - t * f)
      (Polynomial.X ^ s)
      (mennicke_ascent_monic_det f g p q t r s hdet hq) ∈
        elementaryThreeSubgroup (Polynomial A))
    (hgood : mennickeBlock
      (Polynomial.X ^ s * f - Polynomial.C c * g) g
      (p - t * f - Polynomial.C c * r) r
      (mennicke_ascent_good_det f g p q t r s c hdet hq) ∈
        elementaryThreeSubgroup (Polynomial A)) :
    mennickeBlock f g p q hdet ∈
      elementaryThreeSubgroup (Polynomial A) := by
  let p₁ : Polynomial A := p - t * f
  have hswapdet : (Polynomial.X ^ s * r) * f - g * p₁ = 1 := by
    dsimp [p₁]
    have h := mennicke_ascent_row_det f g p q t r s hdet hq
    linear_combination h
  have hleft :
      mennickeBlock (r * f) g p₁ (Polynomial.X ^ s)
        (mennicke_swapped_left_factor_det
          (Polynomial.X ^ s) r g p₁ f hswapdet) ∈
          elementaryThreeSubgroup (Polynomial A) := by
    simpa only [p₁] using hmonic
  have hright :
      mennickeBlock (Polynomial.X ^ s * f) g p₁ r
        (mennicke_swapped_right_factor_det
          (Polynomial.X ^ s) r g p₁ f hswapdet) ∈
          elementaryThreeSubgroup (Polynomial A) := by
    apply (mennickeBlock_columnFirst_sub_mem_iff
      (Polynomial.X ^ s * f) g p₁ r (Polynomial.C c)
      (mennicke_swapped_right_factor_det
        (Polynomial.X ^ s) r g p₁ f hswapdet)).mp
    simpa only [p₁] using hgood
  have htarget := mennicke_swapped_block_mem_of_factors
    (elementaryThreeSubgroup (Polynomial A))
    elementaryThree_contains_roots
    (Polynomial.X ^ s) r g p₁ f hswapdet hleft hright
  have hbottom : q - t * g = Polynomial.X ^ s * r := by
    rw [hq]
    ring
  have hsheared :
      mennickeBlock f g (p - t * f) (q - t * g)
        (mennicke_rowSecond_sub_det f g p q t hdet) ∈
          elementaryThreeSubgroup (Polynomial A) := by
    have heq :
        mennickeBlock f g (p - t * f) (q - t * g)
          (mennicke_rowSecond_sub_det f g p q t hdet) =
        mennickeBlock f g p₁ (Polynomial.X ^ s * r)
          (mennicke_swapped_target_det
            (Polynomial.X ^ s) r g p₁ f hswapdet) := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      change
        !![f, g, 0; p - t * f, q - t * g, 0; 0, 0, 1] i j =
          !![f, g, 0; p₁, Polynomial.X ^ s * r, 0; 0, 0, 1] i j
      dsimp [p₁]
      rw [hbottom]
    rw [heq]
    exact htarget
  exact (mennickeBlock_rowSecond_sub_mem_iff f g p q t hdet).mp
    hsheared

end MennickeIdentity

section

open Matrix Polynomial
open StabilizedBlockReduction MennickeIdentity

universe w

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem scratch_shifted_remainder_alignment
    {A : Type w} [CommRing A]
    (f g p q : Polynomial A)
    (hg0 : IsUnit (g.coeff 0))
    (hg : 0 < g.natDegree)
    (hdet : f * q - g * p = 1)
    (s : ℕ) :
    ∃ (S : ℕ) (q₁ t R : Polynomial A),
      s ≤ S ∧
      q = X ^ S * q₁ + t * g ∧
      q₁.natDegree < g.natDegree ∧
      R = X ^ (S - s) * q₁ ∧
      q - t * g = X ^ s * R ∧
      f * (X ^ s * R) - g * (p - t * f) = 1 := by
  let S : ℕ := max s (q.natDegree + 1)
  have hsS : s ≤ S := le_max_left _ _
  have hqS : q.natDegree + 1 ≤ S := le_max_right _ _
  have hk : q.natDegree + 1 ≤ S + g.natDegree := by omega
  obtain ⟨q₁, t, hq₁, hq⟩ :=
    suslin_horrocks_truncated_remainder_aux g hg0 hg S q hk
  have hS : s + (S - s) = S := Nat.add_sub_of_le hsS
  have hpow : (X : Polynomial A) ^ S = X ^ s * X ^ (S - s) := by
    rw [← pow_add, hS]
  refine ⟨S, q₁, t, X ^ (S - s) * q₁, hsS, hq, hq₁, rfl, ?_, ?_⟩
  · rw [hq, hpow]
    ring
  · rw [hq, hpow] at hdet
    linear_combination hdet

end

namespace ScratchSuslinDividingOuterIH

open Matrix Polynomial MennickeIdentity StabilizedBlockReduction

universe u

variable {A : Type u} [CommRing A] [IsDomain A]

omit [IsDomain A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shiftedLeadingCancellationQuotient_coeff_zero
    (f g : Polynomial A) (c : A)
    (hdegree : f.natDegree < g.natDegree) :
    (shiftedLeadingCancellationQuotient f g c).coeff 0 = 0 := by
  have hpositive : 0 < g.natDegree - f.natDegree :=
    Nat.sub_pos_of_lt hdegree
  unfold shiftedLeadingCancellationQuotient
  rw [Polynomial.coeff_C_mul_X_pow]
  split_ifs with heq
  · omega
  · rfl

omit [IsDomain A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shiftedLeadingCancellation_remainder_coeff_zero
    (f g : Polynomial A) (c : A)
    (hdegree : f.natDegree < g.natDegree) :
    (g - shiftedLeadingCancellationQuotient f g c * f).coeff 0 =
      g.coeff 0 := by
  rw [Polynomial.coeff_sub, Polynomial.mul_coeff_zero,
    shiftedLeadingCancellationQuotient_coeff_zero f g c hdegree,
    zero_mul, sub_zero]

omit [IsDomain A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem secondColumnSub_det
    (f g p q t : Polynomial A)
    (hdet : f * q - g * p = 1) :
    f * (q - t * p) - (g - t * f) * p = 1 := by
  linear_combination hdet

omit [IsDomain A] in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennickeBlock_secondColumnSub_mem_iff
    (f g p q t : Polynomial A)
    (hdet : f * q - g * p = 1) :
    mennickeBlock f g p q hdet ∈
        elementaryThreeSubgroup (Polynomial A) ↔
      mennickeBlock f (g - t * f) p (q - t * p)
          (secondColumnSub_det f g p q t hdet) ∈
        elementaryThreeSubgroup (Polynomial A) := by
  let E := elementaryThreeSubgroup (Polynomial A)
  have hroot : Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 3) ≠ 1 by decide) (-t) ∈ E :=
    Subgroup.subset_closure ⟨0, 1, by decide, -t, rfl⟩
  have hmul :
      mennickeBlock f g p q hdet *
          Matrix.SpecialLinearGroup.transvection
            (show (0 : Fin 3) ≠ 1 by decide) (-t) =
        mennickeBlock f (g - t * f) p (q - t * p)
          (secondColumnSub_det f g p q t hdet) := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;>
      simp [mennickeBlock,
        Matrix.SpecialLinearGroup.transvection_coe,
        Matrix.mul_apply, Fin.sum_univ_succ,
        Matrix.single_apply, Matrix.one_apply] <;> ring
  rw [← hmul]
  exact (E.mul_mem_cancel_right hroot).symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennickeBlock_mem_of_dividing_outerIH
    (f g p q : Polynomial A)
    (hdet : f * q - g * p = 1)
    (hf : f ≠ 0)
    (hdegree : f.natDegree < g.natDegree)
    (hgunit : IsUnit (g.coeff 0))
    (hdivide : f.leadingCoeff ∣ g.leadingCoeff)
    (hIH : ∀ (f' g' p' q' : Polynomial A)
      (hdet' : f' * q' - g' * p' = 1),
      IsUnit (g'.coeff 0) → g'.natDegree < g.natDegree →
        mennickeBlock f' g' p' q' hdet' ∈
          elementaryThreeSubgroup (Polynomial A)) :
    mennickeBlock f g p q hdet ∈
      elementaryThreeSubgroup (Polynomial A) := by
  obtain ⟨c, hc⟩ := hdivide
  let t : Polynomial A := shiftedLeadingCancellationQuotient f g c
  have hg : g ≠ 0 := by
    intro hzero
    simpa only [hzero, coeff_zero, ne_eq, not_true_eq_false] using hgunit.ne_zero
  have hgpos : 0 < g.natDegree :=
    lt_of_le_of_lt (Nat.zero_le _) hdegree
  have hsmaller : (g - t * f).natDegree < g.natDegree := by
    dsimp [t]
    apply natDegree_sub_shiftedLeadingCancellationQuotient_mul_lt
      f g hf hg (Nat.le_of_lt hdegree) hgpos c
    exact hc
  have hconstant : (g - t * f).coeff 0 = g.coeff 0 := by
    exact shiftedLeadingCancellation_remainder_coeff_zero f g c hdegree
  have hdet' := secondColumnSub_det f g p q t hdet
  have hsmallerBlock := hIH f (g - t * f) p (q - t * p)
    hdet' (hconstant.symm ▸ hgunit) hsmaller
  exact (mennickeBlock_secondColumnSub_mem_iff f g p q t hdet).mpr
    hsmallerBlock

end ScratchSuslinDividingOuterIH

section

open Matrix Polynomial
open StabilizedBlockReduction MennickeIdentity

universe w

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem valuationPrimitiveAscentStep_mennicke_transport_of_powers
    {A : Type w} [CommRing A]
    (g f f' p q : Polynomial A)
    (hstep : valuationPrimitiveAscentStep g f f')
    (hg0 : IsUnit (g.coeff 0))
    (hdeg : f.natDegree < g.natDegree)
    (hdet : f * q - g * p = 1)
    (hpower : ∀ (a b c : Polynomial A) (n : ℕ)
      (hd : a * X ^ n - b * c = 1),
        mennickeBlock a b c (X ^ n) hd ∈
          elementaryThreeSubgroup (Polynomial A)) :
    ∃ (p' q' : Polynomial A) (hdet' : f' * q' - g * p' = 1),
      (mennickeBlock f' g p' q' hdet' ∈
        elementaryThreeSubgroup (Polynomial A) →
       mennickeBlock f g p q hdet ∈
        elementaryThreeSubgroup (Polynomial A)) := by
  obtain ⟨c, _hc, _hlead, hf'⟩ := hstep
  let s : ℕ := g.natDegree - f.natDegree
  have hg : 0 < g.natDegree := by omega
  obtain ⟨S, q₁, t, R, _hS, _hq₁, _hdegq₁, _hR, hfactor, _hdetaligned⟩ :=
    scratch_shifted_remainder_alignment f g p q hg0 hg hdet s
  have hq : q = X ^ s * R + t * g := by
    linear_combination hfactor
  have hdet' : f' * R - g * (p - t * f - C c * R) = 1 := by
    rw [hf']
    exact mennicke_ascent_good_det f g p q t R s c hdet hq
  refine ⟨p - t * f - C c * R, R, hdet', ?_⟩
  intro hgood
  have hgood' :
      mennickeBlock (X ^ s * f - C c * g) g
        (p - t * f - C c * R) R
        (mennicke_ascent_good_det f g p q t R s c hdet hq) ∈
          elementaryThreeSubgroup (Polynomial A) := by
    simpa only [hf'] using hgood
  have hpower' :
      mennickeBlock (R * f) g (p - t * f) (X ^ s)
        (mennicke_ascent_monic_det f g p q t R s hdet hq) ∈
          elementaryThreeSubgroup (Polynomial A) :=
    hpower (R * f) g (p - t * f) s
      (mennicke_ascent_monic_det f g p q t R s hdet hq)
  exact mennickeBlock_mem_of_primitive_ascent
    f g p q t R s c hdet hq hpower' hgood'

end

section

open Matrix Polynomial MennickeIdentity StabilizedBlockReduction

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennicke_transport_of_valuationPrimitiveAscentChain
    {A : Type u} [CommRing A] [IsLocalRing A]
    (g : Polynomial A)
    (hstep : ∀ (f f' p q : Polynomial A)
      (_hascent : valuationPrimitiveAscentStep g f f')
      (_ : f.natDegree < g.natDegree)
      (hdet : f * q - g * p = 1),
      ∃ (p' q' : Polynomial A)
        (hdet' : f' * q' - g * p' = 1),
        (mennickeBlock f' g p' q' hdet' ∈
            elementaryThreeSubgroup (Polynomial A) →
          mennickeBlock f g p q hdet ∈
            elementaryThreeSubgroup (Polynomial A)))
    {f f' : Polynomial A}
    (hchain : Relation.ReflTransGen
      (valuationPrimitiveAscentStep g) f f')
    (p q : Polynomial A) (m : ℕ)
    (hdegree : f.natDegree < g.natDegree)
    (hunit : IsUnit (f.coeff m))
    (hdet : f * q - g * p = 1) :
    ∃ (p' q' : Polynomial A)
      (hdet' : f' * q' - g * p' = 1),
      (mennickeBlock f' g p' q' hdet' ∈
          elementaryThreeSubgroup (Polynomial A) →
        mennickeBlock f g p q hdet ∈
          elementaryThreeSubgroup (Polynomial A)) := by
  induction hchain using Relation.ReflTransGen.head_induction_on
      generalizing p q m with
  | refl =>
      exact ⟨p, q, hdet, id⟩
  | @head f₀ f₁ hascent htail ih =>
      obtain ⟨c, hc, hlead, hform⟩ := hascent
      obtain ⟨hsmall, hunit', _⟩ :=
        polynomial_valuation_coefficient_ascent f₀ g c m
          hdegree hunit hc hlead
      have hdegree' : f₁.natDegree < g.natDegree := by
        simpa only [hform] using hsmall
      have hunit'' :
          IsUnit (f₁.coeff (g.natDegree - f₀.natDegree + m)) := by
        simpa only [hform, coeff_sub, coeff_C_mul] using hunit'
      have hactual : valuationPrimitiveAscentStep g f₀ f₁ :=
        ⟨c, hc, hlead, hform⟩
      obtain ⟨p₁, q₁, hdet₁, hback₁⟩ :=
        hstep f₀ f₁ p q hactual hdegree hdet
      obtain ⟨p₂, q₂, hdet₂, hback₂⟩ :=
        ih p₁ q₁ (g.natDegree - f₀.natDegree + m)
          hdegree' hunit'' hdet₁
      exact ⟨p₂, q₂, hdet₂, fun hfinal =>
        hback₁ (hback₂ hfinal)⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennickeBlock_mem_of_valuation_primitive_outerIH
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    (f g p q : Polynomial A)
    (hdet : f * q - g * p = 1)
    (hprimitive : ∃ m : ℕ, IsUnit (f.coeff m))
    (hdegree : f.natDegree < g.natDegree)
    (hgzero : IsUnit (g.coeff 0))
    (houter : ∀ (f' g' p' q' : Polynomial A)
      (hdet' : f' * q' - g' * p' = 1),
      g'.natDegree < g.natDegree → IsUnit (g'.coeff 0) →
        mennickeBlock f' g' p' q' hdet' ∈
          elementaryThreeSubgroup (Polynomial A)) :
    mennickeBlock f g p q hdet ∈
      elementaryThreeSubgroup (Polynomial A) := by
  obtain ⟨m, hm⟩ := hprimitive
  obtain ⟨f', m', hsmall, hunit', hdivide, hchain⟩ :=
    valuation_primitive_ascent_terminates g f m hdegree hm
  obtain ⟨p', q', hdet', hback⟩ :=
    mennicke_transport_of_valuationPrimitiveAscentChain g
      (fun f₀ f₁ p₀ q₀ hascent hdeg hdet₀ =>
        valuationPrimitiveAscentStep_mennicke_transport_of_powers
          g f₀ f₁ p₀ q₀ hascent hgzero hdeg hdet₀
          (fun a b c n hd => mennickeBlock_mem_of_bottomRight_X_pow
            a b c n hd))
      hchain p q m hdegree hm hdet
  apply hback
  have hf' : f' ≠ 0 := by
    intro hz
    simpa only [hz, coeff_zero, ne_eq, not_true_eq_false] using hunit'.ne_zero
  exact ScratchSuslinDividingOuterIH.mennickeBlock_mem_of_dividing_outerIH
    f' g p' q' hdet' hf' hsmall hgzero hdivide
    (fun f₀ g₀ p₀ q₀ hd hu hlt => houter f₀ g₀ p₀ q₀ hd hlt hu)

end

section

open Matrix
open Polynomial
open MennickeIdentity

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennickeBlock_columnSubtract_det
    {R : Type u} [CommRing R]
    (f g p q t : R) (hdet : f * q - g * p = 1) :
    (f - t * g) * q - g * (p - t * q) = 1 := by
  linear_combination hdet

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennickeBlock_mul_columnSubtract
    {R : Type u} [CommRing R]
    (f g p q t : R) (hdet : f * q - g * p = 1) :
    mennickeBlock f g p q hdet *
        Matrix.SpecialLinearGroup.transvection
          (show (1 : Fin 3) ≠ 0 by decide) (-t) =
      mennickeBlock (f - t * g) g (p - t * q) q
        (mennickeBlock_columnSubtract_det f g p q t hdet) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [mennickeBlock,
      Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.one_apply, Matrix.single_apply] <;> ring

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennickeBlock_columnSubtract_mem_iff
    {R : Type u} [CommRing R]
    (E : Subgroup (Matrix.SpecialLinearGroup (Fin 3) R))
    (hE : ContainsElementaryRoots E)
    (f g p q t : R) (hdet : f * q - g * p = 1) :
    mennickeBlock f g p q hdet ∈ E ↔
      mennickeBlock (f - t * g) g (p - t * q) q
        (mennickeBlock_columnSubtract_det f g p q t hdet) ∈ E := by
  rw [← mennickeBlock_mul_columnSubtract]
  · let z : Matrix.SpecialLinearGroup (Fin 3) R :=
      Matrix.SpecialLinearGroup.transvection
        (show (1 : Fin 3) ≠ 0 by decide) (-t)
    have hz : z ∈ E := hE 1 0 (by decide) (-t)
    constructor
    · intro h
      exact E.mul_mem h hz
    · intro h
      have h' := E.mul_mem h (E.inv_mem hz)
      simpa [z, mul_assoc] using h'

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennickeBlock_shifted_det
    {A : Type u} [CommRing A]
    (f g p q f₁ t : Polynomial A) (s : ℕ)
    (hdet : f * q - g * p = 1)
    (hshift : f = X ^ s * f₁ + t * g) :
    (X ^ s * f₁) * q - g * (p - t * q) = 1 := by
  linear_combination hdet - q * hshift

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mennickeBlock_shifted_mem_iff
    {A : Type u} [CommRing A]
    (E : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (Polynomial A)))
    (hE : ContainsElementaryRoots E)
    (f g p q f₁ t : Polynomial A) (s : ℕ)
    (hdet : f * q - g * p = 1)
    (hshift : f = X ^ s * f₁ + t * g) :
    mennickeBlock f g p q hdet ∈ E ↔
      mennickeBlock (X ^ s * f₁) g (p - t * q) q
        (mennickeBlock_shifted_det f g p q f₁ t s hdet hshift) ∈ E := by
  have hfirst : f - t * g = X ^ s * f₁ := by
    rw [hshift]
    ring
  have h := mennickeBlock_columnSubtract_mem_iff E hE f g p q t hdet
  have hblock :
      mennickeBlock (f - t * g) g (p - t * q) q
          (mennickeBlock_columnSubtract_det f g p q t hdet) =
        mennickeBlock (X ^ s * f₁) g (p - t * q) q
          (mennickeBlock_shifted_det f g p q f₁ t s hdet hshift) := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [mennickeBlock, hfirst]
  rw [hblock] at h
  exact h

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_mennickeBlock_shifted_remainder
    {A : Type u} [CommRing A]
    (E : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (Polynomial A)))
    (hE : ContainsElementaryRoots E)
    (f g p q : Polynomial A)
    (hdet : f * q - g * p = 1)
    (hg₀ : IsUnit (g.coeff 0))
    (hgdeg : 0 < g.natDegree)
    (s : ℕ) (hs : f.natDegree + 1 ≤ s + g.natDegree) :
    ∃ (f₁ t : Polynomial A)
      (hdet' : (X ^ s * f₁) * q - g * (p - t * q) = 1),
      f₁.natDegree < g.natDegree ∧
        f = X ^ s * f₁ + t * g ∧
          (mennickeBlock f g p q hdet ∈ E ↔
            mennickeBlock (X ^ s * f₁) g (p - t * q) q hdet' ∈ E) := by
  obtain ⟨f₁, t, hdegree, hshift⟩ :=
    suslin_horrocks_truncated_remainder_aux g hg₀ hgdeg s f hs
  have hdet' := mennickeBlock_shifted_det f g p q f₁ t s hdet hshift
  exact ⟨f₁, t, hdet', hdegree, hshift,
    mennickeBlock_shifted_mem_iff E hE f g p q f₁ t s hdet hshift⟩

end

section

open Polynomial Matrix
open StabilizedBlockReduction

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem stabilizedTwoHom_eq_mennickeBlock
    {A : Type u} [CommRing A]
    (b : Matrix.SpecialLinearGroup (Fin 2) A) :
    stabilizedTwoHom b =
      MennickeIdentity.mennickeBlock
        (b 0 0) (b 0 1) (b 1 0) (b 1 1)
        (by
          have hdet := b.property
          rw [Matrix.det_fin_two] at hdet
          exact hdet) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact stabilizedTwoHom_castSucc_castSucc b 0 0
  · exact stabilizedTwoHom_castSucc_castSucc b 0 1
  · exact stabilizedTwoHom_castSucc_two b 0
  · exact stabilizedTwoHom_castSucc_castSucc b 1 0
  · exact stabilizedTwoHom_castSucc_castSucc b 1 1
  · exact stabilizedTwoHom_castSucc_two b 1
  · exact stabilizedTwoHom_two_castSucc b 0
  · exact stabilizedTwoHom_two_castSucc b 1
  · exact stabilizedTwoHom_two_two b

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem valuation_mennicke_outer_induction
    {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    (hmonomial : ∀ (s : ℕ) (g p q : Polynomial A)
      (hdet : (X ^ s : Polynomial A) * q - g * p = 1),
        MennickeIdentity.mennickeBlock (X ^ s) g p q hdet ∈
          elementaryThreeSubgroup (Polynomial A))
    (hprimitive : ∀ (f g p q : Polynomial A)
      (hdet : f * q - g * p = 1),
      (∃ m : ℕ, IsUnit (f.coeff m)) →
      f.natDegree < g.natDegree →
      IsUnit (g.coeff 0) →
      (∀ (f' g' p' q' : Polynomial A)
        (hdet' : f' * q' - g' * p' = 1),
          g'.natDegree < g.natDegree →
          IsUnit (g'.coeff 0) →
          MennickeIdentity.mennickeBlock f' g' p' q' hdet' ∈
            elementaryThreeSubgroup (Polynomial A)) →
      MennickeIdentity.mennickeBlock f g p q hdet ∈
        elementaryThreeSubgroup (Polynomial A)) :
    ∀ (f g p q : Polynomial A)
      (hdet : f * q - g * p = 1),
      IsUnit (g.coeff 0) →
      MennickeIdentity.mennickeBlock f g p q hdet ∈
        elementaryThreeSubgroup (Polynomial A) := by
  open MennickeIdentity MennickeFactorSplit in
    have hall : ∀ n : ℕ, ∀ f g p q : Polynomial A,
        g.natDegree = n →
          ∀ hdet : f * q - g * p = 1,
            IsUnit (g.coeff 0) →
              mennickeBlock f g p q hdet ∈
                elementaryThreeSubgroup (Polynomial A) := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro f g p q hgdegree hdet hg₀
        by_cases hn : n = 0
        · have hgzero : g.natDegree = 0 := hgdegree.trans hn
          have hgeq : g = C (g.coeff 0) :=
            Polynomial.eq_C_of_natDegree_eq_zero hgzero
          have hgunit : IsUnit g := by
            rw [hgeq]
            exact Polynomial.isUnit_C.mpr hg₀
          exact mennickeBlock_mem_of_isUnit_topRight f g p q hdet hgunit
        · have hgpositive : 0 < g.natDegree := by
            rw [hgdegree]
            omega
          let s : ℕ := f.natDegree + 1
          have hs : f.natDegree + 1 ≤ s + g.natDegree := by
            dsimp [s]
            omega
          obtain ⟨f₁, t, hdet', hfdegree, hshift, hequiv⟩ :=
            exists_mennickeBlock_shifted_remainder
              (elementaryThreeSubgroup (Polynomial A))
              (ValuationPowerCase.elementaryThree_containsElementaryRoots
                (Polynomial A)) f g p q hdet hg₀ hgpositive s hs
          have hf₁ : f₁ ≠ 0 := by
            intro hzero
            have hgunit : IsUnit g := by
              apply IsUnit.of_mul_eq_one (-(p - t * q))
              have heq : -(g * (p - t * q)) = 1 := by
                simpa only [hzero, mul_zero, zero_mul, zero_sub] using hdet'
              calc
                g * (-(p - t * q)) = -(g * (p - t * q)) := by ring
                _ = 1 := heq
            exact (Nat.ne_of_gt hgpositive)
              (Polynomial.natDegree_eq_zero_of_isUnit hgunit)
          obtain ⟨a, r, i, ha, hfactor, hcoeff, hrprim, hrdegree⟩ :=
            valuation_polynomial_exists_primitive_factor f₁ hf₁
          have hshape : X ^ s * f₁ = C a * (X ^ s * r) := by
            rw [hfactor]
            ring
          have hdetfactor :
              (C a * (X ^ s * r)) * q - g * (p - t * q) = 1 := by
            rw [← hshape]
            exact hdet'
          have hconstant :
              mennickeBlock (C a) g (p - t * q) ((X ^ s * r) * q)
                  (constant_factor_det a s r g (p - t * q) q hdetfactor) ∈
                elementaryThreeSubgroup (Polynomial A) :=
            ValuationPowerCase.mennickeBlock_constant_mem
              a g (p - t * q) ((X ^ s * r) * q)
                (constant_factor_det a s r g (p - t * q) q hdetfactor)
          have hmon :
              mennickeBlock (X ^ s) g (p - t * q) (r * (C a * q))
                  (monomial_factor_det a s r g (p - t * q) q hdetfactor) ∈
                elementaryThreeSubgroup (Polynomial A) :=
            hmonomial s g (p - t * q) (r * (C a * q))
              (monomial_factor_det a s r g (p - t * q) q hdetfactor)
          have hprim :
              mennickeBlock r g (p - t * q) (X ^ s * (C a * q))
                  (primitive_factor_det a s r g (p - t * q) q hdetfactor) ∈
                elementaryThreeSubgroup (Polynomial A) := by
            apply hprimitive r g (p - t * q) (X ^ s * (C a * q))
              (primitive_factor_det a s r g (p - t * q) q hdetfactor)
            · exact ⟨i, hcoeff.symm ▸ isUnit_one⟩
            · exact hrdegree.trans_lt hfdegree
            · exact hg₀
            · intro f' g' p' q' hdet'' hsmall hg₀'
              exact ih g'.natDegree (by
                rw [← hgdegree]
                exact hsmall) f' g' p' q' rfl hdet'' hg₀'
          have hfactored :=
            elementaryThree_mennicke_block_mem_of_three_factors
              a s r g (p - t * q) q hdetfactor hconstant hmon hprim
          apply hequiv.mpr
          have hblock :
              mennickeBlock (X ^ s * f₁) g (p - t * q) q hdet' =
                mennickeBlock (C a * (X ^ s * r)) g (p - t * q) q
                  hdetfactor := by
            apply Matrix.SpecialLinearGroup.ext
            intro j k
            fin_cases j <;> fin_cases k <;>
              simp [MennickeIdentity.mennickeBlock, hshape]
          rw [hblock]
          exact hfactored
    intro f g p q hdet hg₀
    exact hall g.natDegree f g p q rfl hdet hg₀

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_dvr_stabilized_two_mem_of_primitive
    {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    (hprimitive : ∀ (f g p q : Polynomial A)
      (hdet : f * q - g * p = 1),
      (∃ m : ℕ, IsUnit (f.coeff m)) →
      f.natDegree < g.natDegree →
      IsUnit (g.coeff 0) →
      (∀ (f' g' p' q' : Polynomial A)
        (hdet' : f' * q' - g' * p' = 1),
          g'.natDegree < g.natDegree →
          IsUnit (g'.coeff 0) →
          MennickeIdentity.mennickeBlock f' g' p' q' hdet' ∈
            elementaryThreeSubgroup (Polynomial A)) →
      MennickeIdentity.mennickeBlock f g p q hdet ∈
        elementaryThreeSubgroup (Polynomial A))
    (b : Matrix.SpecialLinearGroup (Fin 2) (Polynomial A)) :
    stabilizedTwoHom b ∈ elementaryThreeSubgroup (Polynomial A) := by
  have hcore := valuation_mennicke_outer_induction
    (A := A)
    (fun s g p q hdet =>
      mennickeBlock_mem_of_topLeft_X_pow s g p q hdet)
    hprimitive
  obtain ⟨b', e, he, hfactor, hg, _⟩ :=
    suslin_local_stabilizedTwo_unit_offdiag_normalization b
  rw [hfactor]
  apply (elementaryThreeSubgroup (Polynomial A)).mul_mem ?_ he
  rw [stabilizedTwoHom_eq_mennickeBlock]
  exact hcore _ _ _ _ _ hg

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem suslin_dvr_stabilized_two_mem
    {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    (b : Matrix.SpecialLinearGroup (Fin 2) (Polynomial A)) :
    stabilizedTwoHom b ∈ elementaryThreeSubgroup (Polynomial A) := by
  apply suslin_dvr_stabilized_two_mem_of_primitive (A := A) ?_ b
  intro f g p q hdet hprimitive hdegree hgzero houter
  exact mennickeBlock_mem_of_valuation_primitive_outerIH
    f g p q hdet hprimitive hdegree hgzero houter

end

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_semilocalTriple_exists_coprime
    {R : Type*} [CommRing R]
    (f g h : R)
    (hfinite :
      {p : Ideal (R ⧸ Ideal.span ({f} : Set R)) | p.IsMaximal}.Finite)
    (hrow : ∃ a b c : R, a * f + b * g + c * h = 1) :
    ∃ t : R, IsCoprime f (g + t * h) := by
  let I : Ideal R := Ideal.span ({f} : Set R)
  let q : R →+* R ⧸ I := Ideal.Quotient.mk I
  have hfzero : q f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton_self f)
  obtain ⟨a, b, c, hcomb⟩ := hrow
  have hcoprime : IsCoprime (q g) (q h) := by
    refine ⟨q b, q c, ?_⟩
    have hmap := congrArg q hcomb
    simpa only [map_add, map_mul, hfzero, mul_zero, zero_add, map_one] using hmap
  obtain ⟨tq, htq⟩ :=
    exists_add_mul_isUnit_of_finite_maximalIdeals hfinite hcoprime
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective tq
  refine ⟨t, (isUnit_quotient_span_singleton_iff_isCoprime
    f (g + t * h)).mp ?_⟩
  simpa only [map_add, map_mul] using htq

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem suslin_unimodularTriple_exists_coprime
    {A : Type*} [CommRing A]
    (f g h : Polynomial A)
    (hfinite :
      {p : Ideal (Polynomial A ⧸
        Ideal.span ({f} : Set (Polynomial A))) | p.IsMaximal}.Finite)
    (hrow : ∃ a b c : Polynomial A, a * f + b * g + c * h = 1) :
    ∃ t : Polynomial A, IsCoprime f (g + t * h) :=
  suslin_semilocalTriple_exists_coprime f g h hfinite hrow

end

section

open Matrix Polynomial
open StabilizedBlockReduction

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem elementaryThree_second_add_third
    {R : Type*} [CommRing R] (v : Fin 3 → R) (t : R) :
    ∃ e : Matrix.SpecialLinearGroup (Fin 3) R,
      e ∈ elementaryThreeSubgroup R ∧
        (e • v) 0 = v 0 ∧ (e • v) 1 = v 1 + t * v 2 := by
  let e : Matrix.SpecialLinearGroup (Fin 3) R :=
    Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 3) ≠ 2 by decide) t
  refine ⟨e, elementaryThree_transvection_mem 1 2 (by decide) t, ?_, ?_⟩
  · exact elementaryThree_transvection_smul_other
      1 2 0 (by decide) (by decide) t v
  · exact elementaryThree_transvection_smul_same 1 2 (by decide) t v

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem elementaryThree_reduce_of_coprime_second_add_third
    {R : Type*} [CommRing R] (v : Fin 3 → R)
    (hpair : ∃ t : R, IsCoprime (v 0) (v 1 + t * v 2)) :
    ∃ e : Matrix.SpecialLinearGroup (Fin 3) R,
      e ∈ elementaryThreeSubgroup R ∧ e • v = Pi.single 0 1 := by
  obtain ⟨t, ht⟩ := hpair
  obtain ⟨p, hp, hpzero, hpone⟩ :=
    elementaryThree_second_add_third v t
  obtain ⟨q, hq, hqaction⟩ :=
    elementaryThree_coprime_pair_reduce (p • v) (by simpa only [Fin.isValue, hpzero,
                                                      hpone] using ht)
  exact ⟨q * p, (elementaryThreeSubgroup R).mul_mem hq hp,
    by simpa only [mul_smul, Fin.isValue] using hqaction⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem elementaryThree_reduce_of_semilocal_first_quotient
    {A : Type*} [CommRing A]
    (v : Fin 3 → Polynomial A) (hv : UnimodularRow v)
    (hfinite : {I : Ideal (Polynomial A ⧸
      Ideal.span ({v 0} : Set (Polynomial A))) | I.IsMaximal}.Finite) :
    ∃ e : Matrix.SpecialLinearGroup (Fin 3) (Polynomial A),
      e ∈ elementaryThreeSubgroup (Polynomial A) ∧
        e • v = Pi.single 0 1 := by
  obtain ⟨a, ha⟩ := hv
  have hrow : ∃ p q r : Polynomial A,
      p * v 0 + q * v 1 + r * v 2 = 1 := by
    refine ⟨a 0, a 1, a 2, ?_⟩
    simpa only [Fin.isValue, add_assoc, Fin.sum_univ_succ, Fin.succ_zero_eq_one, Finset.univ_unique,
      Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_one_eq_two] using ha
  exact elementaryThree_reduce_of_coprime_second_add_third v
    (suslin_unimodularTriple_exists_coprime
      (v 0) (v 1) (v 2) hfinite hrow)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem dvr_elementaryThree_first_coordinate_one_add_uniformizer
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {π : A} (hπ : Irreducible π)
    (v : Fin 3 → Polynomial A) (hv : UnimodularRow v) :
    ∃ (e : Matrix.SpecialLinearGroup (Fin 3) (Polynomial A))
      (q : Polynomial A),
      e ∈ elementaryThreeSubgroup (Polynomial A) ∧
        (e • v) 0 = 1 + Polynomial.C π * q := by
  obtain ⟨e, he, hreduce⟩ :=
    DvrResidueElementaryLift.exists_elementaryThree_polynomial_uniformizer_reduction
      hπ v hv
  have hfirst :
      Polynomial.map (Ideal.Quotient.mk (Ideal.span ({π} : Set A)))
          ((e • v) 0) = 1 := by
    simpa only [Fin.isValue, Pi.single_eq_same] using hreduce 0
  obtain ⟨q, hq⟩ :=
    dvr_polynomial_eq_one_add_uniformizer_mul_of_residue_one
      hπ ((e • v) 0) hfirst
  exact ⟨e, q, he, hq⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem suslin_valuation_unimodular_three_elementary_reduce
    {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    (v : Fin 3 → Polynomial A) (hv : UnimodularRow v) :
    ∃ e : Matrix.SpecialLinearGroup (Fin 3) (Polynomial A),
      e ∈ elementaryThreeSubgroup (Polynomial A) ∧
        e • v = Pi.single (2 : Fin 3) 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨p, q, hp, hpfirst⟩ :=
    dvr_elementaryThree_first_coordinate_one_add_uniformizer hπ v hv
  have hpunit : UnimodularRow (p • v) :=
    unimodularRow_smul_specialLinear_three p v hv
  have hfinite : {I : Ideal (Polynomial A ⧸
      Ideal.span ({(p • v) 0} : Set (Polynomial A))) |
      I.IsMaximal}.Finite :=
    dvr_mod_uniformizer_one_quotient_maximalIdeals_finite
      π hπ ((p • v) 0) q hpfirst
  obtain ⟨r, hr, hreduce⟩ :=
    elementaryThree_reduce_of_semilocal_first_quotient (p • v) hpunit hfinite
  apply elementaryThree_reduce_last_of_reduce_zero v
  exact ⟨r * p, (elementaryThreeSubgroup (Polynomial A)).mul_mem hr hp,
    by simpa only [mul_smul, Fin.isValue] using hreduce⟩

end

section

namespace HorrocksValuationInduction

open Matrix
open StabilizedBlockReduction
open scoped BigOperators

universe u

variable {R : Type u} [CommRing R]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def lastRowClear
    (g : Matrix.SpecialLinearGroup (Fin 3) R) :
    Matrix.SpecialLinearGroup (Fin 3) R :=
  Matrix.SpecialLinearGroup.transvection
      (show (2 : Fin 3) ≠ 0 by decide) (-(g 2 0)) *
    Matrix.SpecialLinearGroup.transvection
      (show (2 : Fin 3) ≠ 1 by decide) (-(g 2 1))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem lastRowClear_mem
    (g : Matrix.SpecialLinearGroup (Fin 3) R) :
    lastRowClear g ∈ elementaryThreeSubgroup R := by
  apply (elementaryThreeSubgroup R).mul_mem
  · exact Subgroup.subset_closure
      ⟨2, 0, (by decide), -(g 2 0), rfl⟩
  · exact Subgroup.subset_closure
      ⟨2, 1, (by decide), -(g 2 1), rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem lastRowClear_mul_apply
    (g : Matrix.SpecialLinearGroup (Fin 3) R)
    (hcolumn : ∀ i : Fin 3, g i 2 = if i = 2 then 1 else 0)
    (i j : Fin 3) :
    (g * lastRowClear g) i j =
      if i = 2 then if j = 2 then 1 else 0 else g i j := by
  have h0 := hcolumn 0
  have h1 := hcolumn 1
  have h2 := hcolumn 2
  change
    (g.val *
      (Matrix.transvection (2 : Fin 3) 0 (-(g 2 0)) *
        Matrix.transvection (2 : Fin 3) 1 (-(g 2 1)))) i j = _
  simp only [← mul_assoc]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_transvection_apply_same,
      Matrix.mul_transvection_apply_of_ne, h0, h1, h2]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem upperLeft_det_eq_one
    (g : Matrix.SpecialLinearGroup (Fin 3) R)
    (hcolumn : ∀ i : Fin 3, g i 2 = if i = 2 then 1 else 0) :
    (g.val.submatrix Fin.castSucc Fin.castSucc).det = 1 := by
  have hdet := g.property
  rw [Matrix.det_fin_three] at hdet
  rw [Matrix.det_fin_two]
  have h0 := hcolumn 0
  have h1 := hcolumn 1
  have h2 := hcolumn 2
  simpa only [submatrix, Fin.isValue, of_apply, Fin.castSucc_zero, Fin.castSucc_one, h2, ↓reduceIte,
    mul_one, h1, Fin.reduceEq, mul_zero, zero_mul, sub_zero, add_zero, h0] using hdet

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def upperLeftSpecialLinear
    (g : Matrix.SpecialLinearGroup (Fin 3) R)
    (hcolumn : ∀ i : Fin 3, g i 2 = if i = 2 then 1 else 0) :
    Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨g.val.submatrix Fin.castSucc Fin.castSucc,
    upperLeft_det_eq_one g hcolumn⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem lastColumn_block_decomposition
    (g : Matrix.SpecialLinearGroup (Fin 3) R)
    (hcolumn : ∀ i : Fin 3, g i 2 = if i = 2 then 1 else 0) :
    g * lastRowClear g =
      stabilizedTwoHom (upperLeftSpecialLinear g hcolumn) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [lastRowClear_mul_apply g hcolumn]
  cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
    simp [stabilizedTwoHom, stabilizedTwoSpecialLinear, stabilizedTwoMatrix,
      upperLeftSpecialLinear, Matrix.submatrix, hcolumn]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem specialLinearThree_mem_of_lastColumnTransitivity_and_stabilizedTwo
    (htrans : ∀ v : Fin 3 → R, UnimodularRow v →
      ∃ e : Matrix.SpecialLinearGroup (Fin 3) R,
        e ∈ elementaryThreeSubgroup R ∧
          e • v = Pi.single (2 : Fin 3) 1)
    (hblock : ∀ b : Matrix.SpecialLinearGroup (Fin 2) R,
      stabilizedTwoHom b ∈ elementaryThreeSubgroup R)
    (g : Matrix.SpecialLinearGroup (Fin 3) R) :
    g ∈ elementaryThreeSubgroup R := by
  obtain ⟨e, he, hcolumn⟩ :=
    htrans (fun i : Fin 3 => g i 2)
      (specialLinear_column_unimodular g 2)
  have hnormalized : ∀ i : Fin 3,
      (e * g) i 2 = if i = 2 then 1 else 0 := by
    intro i
    change (e • (fun j : Fin 3 => g j 2)) i = _
    rw [hcolumn]
    simp only [Fin.isValue, Pi.single_apply]
  have hcleared :
      (e * g) * lastRowClear (e * g) ∈ elementaryThreeSubgroup R := by
    rw [lastColumn_block_decomposition (e * g) hnormalized]
    exact hblock _
  have heg : e * g ∈ elementaryThreeSubgroup R := by
    have h := (elementaryThreeSubgroup R).mul_mem hcleared
      ((elementaryThreeSubgroup R).inv_mem
        (lastRowClear_mem (e * g)))
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using h
  have h := (elementaryThreeSubgroup R).mul_mem
    ((elementaryThreeSubgroup R).inv_mem he) heg
  simpa only [inv_mul_cancel_left] using h

end HorrocksValuationInduction

namespace IntegerElementaryProof
open Matrix
open scoped BigOperators

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev IGroup := IntegerSpecialLinearGroup
/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
abbrev IVec := Index → ℤ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def elementary : Subgroup IGroup :=
  Subgroup.closure
    {g | ∃ (i j : Index) (h : i ≠ j) (a : ℤ),
      g = Matrix.SpecialLinearGroup.transvection h a}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem transvection_mem (i j : Index) (h : i ≠ j) (a : ℤ) :
    Matrix.SpecialLinearGroup.transvection h a ∈ elementary :=
  Subgroup.subset_closure ⟨i, j, h, a, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem transvection_smul_same (i j : Index) (h : i ≠ j) (c : ℤ)
    (v : IVec) :
    (Matrix.SpecialLinearGroup.transvection h c • v) i = v i + c * v j := by
  change ((Matrix.SpecialLinearGroup.transvection h c).val *ᵥ v) i = _
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec,
      Matrix.one_mulVec, Matrix.single_mulVec]
  simp only [Pi.add_apply, Function.update_self]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem transvection_smul_other (i j k : Index) (h : i ≠ j)
    (hk : k ≠ i) (c : ℤ) (v : IVec) :
    (Matrix.SpecialLinearGroup.transvection h c • v) k = v k := by
  change ((Matrix.SpecialLinearGroup.transvection h c).val *ᵥ v) k = _
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec,
      Matrix.one_mulVec, Matrix.single_mulVec]
  simp only [Pi.add_apply, ne_eq, hk, not_false_eq_true, Function.update_of_ne, Pi.zero_apply,
    add_zero]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def coordinateRotation (i j : Index) (h : i ≠ j) : IGroup :=
  Matrix.SpecialLinearGroup.transvection h 1 *
    Matrix.SpecialLinearGroup.transvection h.symm (-1) *
    Matrix.SpecialLinearGroup.transvection h 1

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem coordinateRotation_mem (i j : Index) (h : i ≠ j) :
    coordinateRotation i j h ∈ elementary :=
  elementary.mul_mem
    (elementary.mul_mem (transvection_mem i j h 1)
      (transvection_mem j i h.symm (-1)))
    (transvection_mem i j h 1)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem coordinateRotation_smul_left (i j : Index) (h : i ≠ j) (v : IVec) :
    (coordinateRotation i j h • v) i = v j := by
  simp only [coordinateRotation, mul_smul]
  rw [transvection_smul_same]
  rw [transvection_smul_other j i i h.symm h]
  rw [transvection_smul_same j i]
  rw [transvection_smul_same i j]
  rw [transvection_smul_other i j j h h.symm]
  ring

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem coordinateRotation_smul_right (i j : Index) (h : i ≠ j) (v : IVec) :
    (coordinateRotation i j h • v) j = -v i := by
  simp only [coordinateRotation, mul_smul]
  rw [transvection_smul_other i j j h h.symm]
  rw [transvection_smul_same j i]
  rw [transvection_smul_same i j]
  rw [transvection_smul_other i j j h h.symm]
  ring

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem coordinateRotation_smul_other (i j k : Index) (h : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) (v : IVec) :
    (coordinateRotation i j h • v) k = v k := by
  simp only [coordinateRotation, mul_smul]
  rw [transvection_smul_other i j k h hki]
  rw [transvection_smul_other j i k h.symm hkj]
  rw [transvection_smul_other i j k h hki]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def euclideanStep (i j : Index) (h : i ≠ j) (a b : ℤ) : IGroup :=
  coordinateRotation i j h *
    Matrix.SpecialLinearGroup.transvection h.symm (-(b / a))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem euclideanStep_mem (i j : Index) (h : i ≠ j) (a b : ℤ) :
    euclideanStep i j h a b ∈ elementary :=
  elementary.mul_mem (coordinateRotation_mem i j h)
    (transvection_mem j i h.symm (-(b / a)))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem euclideanStep_smul_left (i j : Index) (h : i ≠ j) (v : IVec) :
    (euclideanStep i j h (v i) (v j) • v) i = v j % v i := by
  rw [euclideanStep, mul_smul, coordinateRotation_smul_left,
    transvection_smul_same]
  have hd := EuclideanDomain.div_add_mod (v j) (v i)
  conv_lhs =>
    lhs
    rw [← hd]
  ring

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem euclideanStep_smul_right (i j : Index) (h : i ≠ j) (v : IVec) :
    (euclideanStep i j h (v i) (v j) • v) j = -(v i) := by
  rw [euclideanStep, mul_smul, coordinateRotation_smul_right,
    transvection_smul_other _ _ _ h.symm h]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem euclideanStep_smul_other (i j k : Index) (h : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) (v : IVec) :
    (euclideanStep i j h (v i) (v j) • v) k = v k := by
  rw [euclideanStep, mul_smul,
    coordinateRotation_smul_other i j k h hki hkj,
    transvection_smul_other _ _ _ h.symm hkj]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem pair_reduce (i j : Index) (h : i ≠ j) (v : IVec) :
    ∃ g : IGroup, g ∈ elementary ∧
      (g • v) j = 0 ∧
      (∀ k : Index, k ≠ i → k ≠ j → (g • v) k = v k) ∧
      (∀ w : IVec, w i = 0 → w j = 0 → g • w = w) := by
  let P : ℤ → Prop := fun a => ∀ (b : ℤ) (w : IVec), w i = a → w j = b →
    ∃ g : IGroup, g ∈ elementary ∧
      (g • w) j = 0 ∧
      (∀ k : Index, k ≠ i → k ≠ j → (g • w) k = w k) ∧
      (∀ z : IVec, z i = 0 → z j = 0 → g • z = z)
  have hp : ∀ a : ℤ, P a := by
    intro a
    induction a using (EuclideanDomain.r_wellFounded (R := ℤ)).induction with
    | h a ih =>
      intro b w hwi hwj
      by_cases ha : a = 0
      · refine ⟨coordinateRotation i j h, coordinateRotation_mem i j h, ?_, ?_, ?_⟩
        · rw [coordinateRotation_smul_right, hwi, ha, neg_zero]
        · exact fun k hki hkj => coordinateRotation_smul_other i j k h hki hkj w
        · intro z hzi hzj
          apply funext
          intro k
          by_cases hki : k = i
          · subst k
            rw [coordinateRotation_smul_left, hzj, hzi]
          · by_cases hkj : k = j
            · subst k
              rw [coordinateRotation_smul_right, hzi, neg_zero, hzj]
            · exact coordinateRotation_smul_other i j k h hki hkj z
      · let s := euclideanStep i j h a b
        have hs : s ∈ elementary := euclideanStep_mem i j h a b
        have hsi : (s • w) i = b % a := by
          dsimp [s]
          subst a
          subst b
          exact euclideanStep_smul_left i j h w
        have hsj : (s • w) j = -a := by
          dsimp [s]
          subst a
          subst b
          exact euclideanStep_smul_right i j h w
        obtain ⟨g, hg, hgj, hgother, hgfix⟩ :=
          ih (b % a) (EuclideanDomain.mod_lt b ha) (-a) (s • w) hsi hsj
        refine ⟨g * s, elementary.mul_mem hg hs, ?_, ?_, ?_⟩
        · rw [mul_smul, hgj]
        · intro k hki hkj
          rw [mul_smul, hgother k hki hkj]
          dsimp [s]
          subst a
          subst b
          exact euclideanStep_smul_other i j k h hki hkj w
        · intro z hzi hzj
          rw [mul_smul]
          have hsz : s • z = z := by
            apply funext
            intro k
            by_cases hki : k = i
            · subst k
              dsimp [s]
              rw [euclideanStep, mul_smul, coordinateRotation_smul_left,
                transvection_smul_same, hzj, hzi]
              ring
            · by_cases hkj : k = j
              · subst k
                dsimp [s]
                rw [euclideanStep, mul_smul, coordinateRotation_smul_right,
                  transvection_smul_other _ _ _ h.symm h, hzi, hzj]
                ring
              · dsimp [s]
                rw [euclideanStep, mul_smul,
                  coordinateRotation_smul_other i j k h hki hkj,
                  transvection_smul_other _ _ _ h.symm hkj]
          rw [hsz, hgfix z hzi hzj]
  exact hp (v i) (v j) v rfl rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem first_column_reduce (A : IGroup) :
    ∃ g : IGroup, g ∈ elementary ∧
      (g * A) 1 0 = 0 ∧ (g * A) 2 0 = 0 ∧ (g * A) 3 0 = 0 := by
  let v : IVec := fun i => A i 0
  obtain ⟨g₁, hg₁, hg₁1, hg₁other, _⟩ :=
    pair_reduce (0 : Index) 1 (by decide) v
  obtain ⟨g₂, hg₂, hg₂2, hg₂other, _⟩ :=
    pair_reduce (0 : Index) 2 (by decide) (g₁ • v)
  obtain ⟨g₃, hg₃, hg₃3, hg₃other, _⟩ :=
    pair_reduce (0 : Index) 3 (by decide) (g₂ • (g₁ • v))
  let g := g₃ * g₂ * g₁
  refine ⟨g, elementary.mul_mem (elementary.mul_mem hg₃ hg₂) hg₁, ?_, ?_, ?_⟩
  · change (g • v) (1 : Index) = 0
    dsimp [g]
    rw [mul_smul, mul_smul,
      hg₃other 1 (by decide) (by decide),
      hg₂other 1 (by decide) (by decide), hg₁1]
  · change (g • v) (2 : Index) = 0
    dsimp [g]
    rw [mul_smul, mul_smul,
      hg₃other 2 (by decide) (by decide), hg₂2]
  · change (g • v) (3 : Index) = 0
    dsimp [g]
    rw [mul_smul, mul_smul, hg₃3]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem second_column_reduce (A : IGroup)
    (h₁₀ : A (1 : Index) 0 = 0)
    (h₂₀ : A (2 : Index) 0 = 0)
    (h₃₀ : A (3 : Index) 0 = 0) :
    ∃ p : IGroup, p ∈ elementary ∧
      (p * A) 1 0 = 0 ∧
      (p * A) 2 0 = 0 ∧
      (p * A) 3 0 = 0 ∧
      (p * A) 2 1 = 0 ∧
      (p * A) 3 1 = 0 := by
  let v₁ : IVec := fun k => A k 1
  obtain ⟨p₁₂, hp₁₂, hz₂₁, _, hfix₁₂⟩ :=
    pair_reduce (1 : Index) 2 (by decide) v₁
  obtain ⟨p₁₃, hp₁₃, hz₃₁, hother₁₃, hfix₁₃⟩ :=
    pair_reduce (1 : Index) 3 (by decide) (p₁₂ • v₁)
  let p : IGroup := p₁₃ * p₁₂
  have hp : p ∈ elementary := elementary.mul_mem hp₁₃ hp₁₂
  have h21 : (p * A) (2 : Index) 1 = 0 := by
    change (p • v₁) (2 : Index) = 0
    dsimp [p]
    rw [mul_smul, hother₁₃ 2 (by decide) (by decide), hz₂₁]
  have h31 : (p * A) (3 : Index) 1 = 0 := by
    change (p • v₁) (3 : Index) = 0
    dsimp [p]
    rw [mul_smul, hz₃₁]
  let v₀ : IVec := fun k => A k 0
  have hfix₀ : p • v₀ = v₀ := by
    dsimp [p]
    rw [mul_smul, hfix₁₂ v₀ h₁₀ h₂₀, hfix₁₃ v₀ h₁₀ h₃₀]
  have h10 : (p * A) (1 : Index) 0 = 0 := by
    change (p • v₀) (1 : Index) = 0
    rw [hfix₀]
    exact h₁₀
  have h20 : (p * A) (2 : Index) 0 = 0 := by
    change (p • v₀) (2 : Index) = 0
    rw [hfix₀]
    exact h₂₀
  have h30 : (p * A) (3 : Index) 0 = 0 := by
    change (p • v₀) (3 : Index) = 0
    rw [hfix₀]
    exact h₃₀
  exact ⟨p, hp, h10, h20, h30, h21, h31⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem third_column_reduce (A : IGroup)
    (h10 : A 1 0 = 0) (h20 : A 2 0 = 0) (h30 : A 3 0 = 0)
    (h21 : A 2 1 = 0) (h31 : A 3 1 = 0) :
    ∃ p : IGroup, p ∈ elementary ∧
      (p * A) 1 0 = 0 ∧ (p * A) 2 0 = 0 ∧ (p * A) 3 0 = 0 ∧
      (p * A) 2 1 = 0 ∧ (p * A) 3 1 = 0 ∧ (p * A) 3 2 = 0 := by
  let v₂ : IVec := fun k => A k 2
  obtain ⟨p, hp, hz32, _, hfix⟩ :=
    pair_reduce (2 : Index) 3 (by decide) v₂
  let col₀ : IVec := fun k => A k 0
  let col₁ : IVec := fun k => A k 1
  have hfix₀ : p • col₀ = col₀ := hfix col₀ h20 h30
  have hfix₁ : p • col₁ = col₁ := hfix col₁ h21 h31
  refine ⟨p, hp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (p • col₀) (1 : Index) = 0
    rw [hfix₀]
    exact h10
  · change (p • col₀) (2 : Index) = 0
    rw [hfix₀]
    exact h20
  · change (p • col₀) (3 : Index) = 0
    rw [hfix₀]
    exact h30
  · change (p • col₁) (2 : Index) = 0
    rw [hfix₁]
    exact h21
  · change (p • col₁) (3 : Index) = 0
    rw [hfix₁]
    exact h31
  · exact hz32

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem fin_four_upperTriangular_of_six (A : IGroup)
    (h10 : A (1 : Index) 0 = 0)
    (h20 : A (2 : Index) 0 = 0)
    (h30 : A (3 : Index) 0 = 0)
    (h21 : A (2 : Index) 1 = 0)
    (h31 : A (3 : Index) 1 = 0)
    (h32 : A (3 : Index) 2 = 0) :
    ∀ i j : Index, j < i → A i j = 0 := by
  intro i j hji
  have hval : j.val < i.val := hji
  fin_cases i
  · change j.val < 0 at hval
    omega
  · change j.val < 1 at hval
    have hj : j = 0 := Fin.ext (by omega)
    simpa only [Nat.reduceAdd, Fin.mk_one, Fin.isValue, hj] using h10
  · change j.val < 2 at hval
    have hj : j = 0 ∨ j = 1 := by
      by_cases hzero : j.val = 0
      · exact Or.inl (Fin.ext hzero)
      · exact Or.inr (Fin.ext (by omega))
    rcases hj with rfl | rfl
    · exact h20
    · exact h21
  · change j.val < 3 at hval
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by
      by_cases hzero : j.val = 0
      · exact Or.inl (Fin.ext hzero)
      · by_cases hone : j.val = 1
        · exact Or.inr (Or.inl (Fin.ext hone))
        · exact Or.inr (Or.inr (Fin.ext (by omega)))
    rcases hj with rfl | rfl | rfl
    · exact h30
    · exact h31
    · exact h32

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem upper_triangularize (A : IGroup) :
    ∃ g : IGroup, g ∈ elementary ∧
      ∀ i j : Index, j < i → (g * A) i j = 0 := by
  obtain ⟨p₀, hp₀, h10, h20, h30⟩ := first_column_reduce A
  obtain ⟨p₁, hp₁, h10', h20', h30', h21, h31⟩ :=
    second_column_reduce (p₀ * A) h10 h20 h30
  obtain ⟨p₂, hp₂, h10'', h20'', h30'', h21', h31', h32⟩ :=
    third_column_reduce (p₁ * (p₀ * A)) h10' h20' h30' h21 h31
  let p : IGroup := p₂ * p₁ * p₀
  have hp : p ∈ elementary :=
    elementary.mul_mem (elementary.mul_mem hp₂ hp₁) hp₀
  have hprod : p * A = p₂ * (p₁ * (p₀ * A)) := by
    simp only [mul_assoc, p]
  refine ⟨p, hp, ?_⟩
  rw [hprod]
  exact fin_four_upperTriangular_of_six _
    h10'' h20'' h30'' h21' h31' h32

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem upperTriangular_diag_unit (g : IGroup)
    (htri : ∀ i j : Index, j < i → g i j = 0) (i : Index) :
    g i i = 1 ∨ g i i = -1 := by
  have hblock : (g : Matrix Index Index ℤ).BlockTriangular id := by
    intro k l hkl
    exact htri k l hkl
  have hprod : (∏ j : Index, g j j) = 1 := by
    calc
      (∏ j : Index, g j j) = (g : Matrix Index Index ℤ).det :=
        (Matrix.det_of_isUpperTriangular hblock).symm
      _ = 1 := g.property
  have hdvd : g i i ∣ (∏ j : Index, g j j) :=
    Finset.dvd_prod_of_mem (fun j : Index => g j j) (Finset.mem_univ i)
  rw [hprod] at hdvd
  have hu : IsUnit (g i i) := isUnit_of_dvd_one hdvd
  obtain ⟨u, hu⟩ := hu
  rcases Int.units_eq_one_or u with h | h
  · left
    simpa only [h, Units.val_one] using hu.symm
  · right
    simpa only [Int.reduceNeg, h, Units.val_neg, Units.val_one] using hu.symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def signFlip (i j : Index) (h : i ≠ j) : IGroup :=
  coordinateRotation i j h * coordinateRotation i j h

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem signFlip_mem (i j : Index) (h : i ≠ j) :
    signFlip i j h ∈ elementary :=
  elementary.mul_mem (coordinateRotation_mem i j h)
    (coordinateRotation_mem i j h)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem signFlip_smul_same_left (i j : Index) (h : i ≠ j) (v : IVec) :
    (signFlip i j h • v) i = -v i := by
  rw [signFlip, mul_smul, coordinateRotation_smul_left,
    coordinateRotation_smul_right]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem signFlip_smul_same_right (i j : Index) (h : i ≠ j) (v : IVec) :
    (signFlip i j h • v) j = -v j := by
  rw [signFlip, mul_smul, coordinateRotation_smul_right,
    coordinateRotation_smul_left]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem signFlip_smul_other (i j k : Index) (h : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) (v : IVec) :
    (signFlip i j h • v) k = v k := by
  rw [signFlip, mul_smul,
    coordinateRotation_smul_other i j k h hki hkj,
    coordinateRotation_smul_other i j k h hki hkj]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem signFlip_mul_apply (i j : Index) (h : i ≠ j)
    (g : IGroup) (a b : Index) :
    (signFlip i j h * g) a b =
      if a = i ∨ a = j then -(g a b) else g a b := by
  change (signFlip i j h • (fun k : Index => g k b)) a = _
  by_cases hai : a = i
  · subst a
    simp only [signFlip_smul_same_left, true_or, ↓reduceIte]
  · by_cases haj : a = j
    · subst a
      simp only [signFlip_smul_same_right, or_true, ↓reduceIte]
    · simp only [signFlip_smul_other i j a h hai haj, hai, haj, or_self, ↓reduceIte]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem signFlip_preserves_upper (i j : Index) (h : i ≠ j)
    (g : IGroup) (hg : ∀ a b : Index, b < a → g a b = 0) :
    ∀ a b : Index, b < a → (signFlip i j h * g) a b = 0 := by
  intro a b hab
  rw [signFlip_mul_apply]
  simp only [hg a b hab, neg_zero, ite_self]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def normalizeSigns (g : IGroup) : IGroup :=
  (if g 3 3 = -1 then signFlip 0 3 (by decide) else 1) *
    (if g 2 2 = -1 then signFlip 0 2 (by decide) else 1) *
    (if g 1 1 = -1 then signFlip 0 1 (by decide) else 1)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem normalizeSigns_mem (g : IGroup) : normalizeSigns g ∈ elementary := by
  unfold normalizeSigns
  apply elementary.mul_mem
  · apply elementary.mul_mem
    · split_ifs <;> simp [signFlip_mem]
    · split_ifs <;> simp [signFlip_mem]
  · split_ifs <;> simp [signFlip_mem]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem normalizeSigns_preserves_upper (g : IGroup)
    (hg : ∀ i j : Index, j < i → g i j = 0) :
    ∀ i j : Index, j < i → (normalizeSigns g * g) i j = 0 := by
  let f₁ : IGroup := if g 1 1 = -1 then signFlip 0 1 (by decide) else 1
  let f₂ : IGroup := if g 2 2 = -1 then signFlip 0 2 (by decide) else 1
  let f₃ : IGroup := if g 3 3 = -1 then signFlip 0 3 (by decide) else 1
  have h₁ : ∀ a b : Index, b < a → (f₁ * g) a b = 0 := by
    dsimp [f₁]
    split_ifs
    · exact signFlip_preserves_upper 0 1 _ g hg
    · simpa using hg
  have h₂ : ∀ a b : Index, b < a → (f₂ * (f₁ * g)) a b = 0 := by
    dsimp [f₂]
    split_ifs
    · exact signFlip_preserves_upper 0 2 _ (f₁ * g) h₁
    · simpa using h₁
  have h₃ : ∀ a b : Index, b < a → (f₃ * (f₂ * (f₁ * g))) a b = 0 := by
    dsimp [f₃]
    split_ifs
    · exact signFlip_preserves_upper 0 3 _ (f₂ * (f₁ * g)) h₂
    · simpa using h₂
  simpa [normalizeSigns, f₁, f₂, f₃, mul_assoc] using h₃

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem normalizeSigns_diag_one (g : IGroup)
    (hg : ∀ i j : Index, j < i → g i j = 0) :
    ∀ i : Index, (normalizeSigns g * g) i i = 1 := by
  have h1 := upperTriangular_diag_unit g hg 1
  have h2 := upperTriangular_diag_unit g hg 2
  have h3 := upperTriangular_diag_unit g hg 3
  have htri := normalizeSigns_preserves_upper g hg
  have hblock :
      ((normalizeSigns g * g : IGroup) : Matrix Index Index ℤ).BlockTriangular id := by
    intro k l hkl
    exact htri k l hkl
  have hprod : (∏ j : Index, (normalizeSigns g * g) j j) = 1 := by
    calc
      (∏ j : Index, (normalizeSigns g * g) j j) =
          ((normalizeSigns g * g : IGroup) : Matrix Index Index ℤ).det :=
        (Matrix.det_of_isUpperTriangular hblock).symm
      _ = 1 := (normalizeSigns g * g).property
  intro i
  fin_cases i
  · have hdiag1 : (normalizeSigns g * g) (1 : Index) 1 = 1 := by
      unfold normalizeSigns
      simp only [mul_assoc]
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
        rcases h3 with h3 | h3 <;>
        simp [h1, h2, h3, signFlip_mul_apply]
    have hdiag2 : (normalizeSigns g * g) (2 : Index) 2 = 1 := by
      unfold normalizeSigns
      simp only [mul_assoc]
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
        rcases h3 with h3 | h3 <;>
        simp [h1, h2, h3, signFlip_mul_apply]
    have hdiag3 : (normalizeSigns g * g) (3 : Index) 3 = 1 := by
      unfold normalizeSigns
      simp only [mul_assoc]
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
        rcases h3 with h3 | h3 <;>
        simp [h1, h2, h3, signFlip_mul_apply]
    norm_num [Fin.prod_univ_succ] at hprod
    change (normalizeSigns g * g) 0 0 *
      ((normalizeSigns g * g) 1 1 *
        ((normalizeSigns g * g) 2 2 *
          (normalizeSigns g * g) 3 3)) = 1 at hprod
    rw [hdiag1, hdiag2, hdiag3] at hprod
    simpa only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Matrix.SpecialLinearGroup.coe_mul,
      mul_one] using hprod
  · unfold normalizeSigns
    simp only [mul_assoc]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      rcases h3 with h3 | h3 <;>
      simp [h1, h2, h3, signFlip_mul_apply]
  · unfold normalizeSigns
    simp only [mul_assoc]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      rcases h3 with h3 | h3 <;>
      simp [h1, h2, h3, signFlip_mul_apply]
  · unfold normalizeSigns
    simp only [mul_assoc]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      rcases h3 with h3 | h3 <;>
      simp [h1, h2, h3, signFlip_mul_apply]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem upperUnitriangular_factorization (g : IGroup)
    (hu : ∀ i j : Index, j < i → g i j = 0)
    (hd : ∀ i : Index, g i i = 1) :
    g =
      Matrix.SpecialLinearGroup.transvection (show (2 : Index) ≠ 3 by decide)
        (g 2 3) *
      Matrix.SpecialLinearGroup.transvection (show (1 : Index) ≠ 3 by decide)
        (g 1 3) *
      Matrix.SpecialLinearGroup.transvection (show (1 : Index) ≠ 2 by decide)
        (g 1 2) *
      Matrix.SpecialLinearGroup.transvection (show (0 : Index) ≠ 3 by decide)
        (g 0 3) *
      Matrix.SpecialLinearGroup.transvection (show (0 : Index) ≠ 2 by decide)
        (g 0 2) *
      Matrix.SpecialLinearGroup.transvection (show (0 : Index) ≠ 1 by decide)
        (g 0 1) := by
  have h00 := hd 0
  have h11 := hd 1
  have h22 := hd 2
  have h33 := hd 3
  have h10 := hu 1 0 (by decide)
  have h20 := hu 2 0 (by decide)
  have h21 := hu 2 1 (by decide)
  have h30 := hu 3 0 (by decide)
  have h31 := hu 3 1 (by decide)
  have h32 := hu 3 2 (by decide)
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one,
      Fin.reduceFinMk, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Matrix.add_apply, Matrix.one_apply, Fin.reduceEq, false_and,
      not_false_eq_true, Matrix.single_apply_of_ne, add_zero,
      Matrix.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte, one_ne_zero, true_and,
      Fin.sum_univ_four, zero_ne_one, mul_ite, mul_one, mul_zero,
      ite_self, zero_add, and_false, Finset.sum_ite_eq', and_true,
      h00, h11, h22, h33, h10, h20, h21, h30, h31, h32]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem upperUnitriangular_mem (g : IGroup)
    (hu : ∀ i j : Index, j < i → g i j = 0)
    (hd : ∀ i : Index, g i i = 1) :
    g ∈ elementary := by
  rw [upperUnitriangular_factorization g hu hd]
  exact elementary.mul_mem
    (elementary.mul_mem
      (elementary.mul_mem
        (elementary.mul_mem
          (elementary.mul_mem
            (transvection_mem 2 3 (by decide) (g 2 3))
            (transvection_mem 1 3 (by decide) (g 1 3)))
          (transvection_mem 1 2 (by decide) (g 1 2)))
        (transvection_mem 0 3 (by decide) (g 0 3)))
      (transvection_mem 0 2 (by decide) (g 0 2)))
    (transvection_mem 0 1 (by decide) (g 0 1))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
theorem elementary_eq_top : elementary = ⊤ := by
  apply top_unique
  intro A _
  obtain ⟨p, hp, htri⟩ := upper_triangularize A
  let q : IGroup := normalizeSigns (p * A)
  have hq : q ∈ elementary := normalizeSigns_mem (p * A)
  have hunit : q * (p * A) ∈ elementary :=
    upperUnitriangular_mem (q * (p * A))
      (normalizeSigns_preserves_upper (p * A) htri)
      (normalizeSigns_diag_one (p * A) htri)
  have hA := elementary.mul_mem
    (elementary.inv_mem (elementary.mul_mem hq hp)) hunit
  simpa only [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left] using hA

end IntegerElementaryProof

end

end ConnesRigidity

end
