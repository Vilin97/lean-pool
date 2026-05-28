/-
Copyright (c) 2026 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Algebra.Lie.Abelian
import LeanPool.VirasoroProject.ToMathlib.Algebra.Lie.Basic

/-!
# Lie algebra cohomology in degree two (for central extensions)

(*WARNING*: This file needs cleaning up. It was not the main goal and it was the first time I
tried to use multilinear maps in Lean.)

This file defines Lie algebra 2-cocycles and 2-coboundaries and constructs the Lie algebra
cohomology in degree two, with coefficients in a vector space (an Abelian Lie algebra).

## Main definitions

* `LieOneCochain`: The set C¹(𝓰,𝓪) of 1-cochains of a Lie algebra 𝓰 with coefficients in a
  vector space 𝓪.
* `LieTwoCocycle`: The set Z²(𝓰,𝓪) of 2-cocycles of a Lie algebra 𝓰 with coefficients in a
  vector space 𝓪.
* `LieTwoCoboundary`: The subspace B²(𝓰,𝓪) ⊆ Z²(𝓰,𝓪) of 2-coboundaries.
* `LieTwoCohomology`: The 2-cohomology H²(𝓰,𝓪) := Z²(𝓰,𝓪) ⧸ B²(𝓰,𝓪) of a Lie algebra 𝓰 with
  coefficients in a vector space 𝓪.

## Main statements

* `LieTwoCocycle.toLieTwoCohomologyEquiv`: If 𝓰 is abelian, then the canonical projection
  from 2-cocycles to 2-cohomologies is a linear isomorphism.

## Implementation notes

This file needs some clean-up! (But it works for the purposes of concrete calculations of
central extensions etc.)

A reasonable thing to do would be to define Lie algebra cohomology in general degrees. But for
concrete applications, the special case of degree two probably deserves its own API. Once a
general definition is made, the API for the degree 2 case (especially central extensions)
could be refactored.

## Tags

Lie algebra, cohomology

-/

namespace VirasoroProject

universe u
variable (𝕜 : Type*) [CommRing 𝕜]
variable (𝓰 𝓪 : Type u) [LieRing 𝓰] [AddCommGroup 𝓪] [LieAlgebra 𝕜 𝓰] [Module 𝕜 𝓪]

section LieOneCochain

/-! ### Lie algebra 1-cochains -/

/-- Lie algebra 1-cochains. -/
@[ext] structure LieOneCochain where
  /-- The underlying linear map of a Lie algebra 1-cochain. -/
  toLinearMap : 𝓰 →ₗ[𝕜] 𝓪

instance : Zero (LieOneCochain 𝕜 𝓰 𝓪) where
  zero := { toLinearMap := 0 }

instance : Add (LieOneCochain 𝕜 𝓰 𝓪) where
  add β β' := { toLinearMap := β.toLinearMap + β'.toLinearMap }

instance : SMul 𝕜 (LieOneCochain 𝕜 𝓰 𝓪) where
  smul c β := { toLinearMap := c • β.toLinearMap }

namespace LieOneCochain

@[simp]
lemma toLinearMap_zero : (0 : LieOneCochain 𝕜 𝓰 𝓪).toLinearMap = 0 := rfl

@[simp]
lemma toLinearMap_add (β β' : LieOneCochain 𝕜 𝓰 𝓪) :
    (β + β').toLinearMap = β.toLinearMap + β'.toLinearMap := rfl

@[simp]
lemma toLinearMap_smul (c : 𝕜) (β : LieOneCochain 𝕜 𝓰 𝓪) :
    (c • β).toLinearMap = c • β.toLinearMap := rfl

instance : AddCommMonoid (LieOneCochain 𝕜 𝓰 𝓪) where
  add_assoc β β' β'' := by
    ext1
    simp only [LieOneCochain.toLinearMap_add]
    exact add_assoc β.toLinearMap β'.toLinearMap β''.toLinearMap
  zero_add β := by ext1; simp
  add_zero β := by ext1; simp
  add_comm β β' := by
    ext1
    simp only [LieOneCochain.toLinearMap_add]
    exact AddCommMagma.add_comm β.toLinearMap β'.toLinearMap
  nsmul n β := { toLinearMap := n • β.toLinearMap }
  nsmul_zero β := by ext1; simp only [zero_smul]; rfl
  nsmul_succ n β := by
    ext1
    simpa only [LieOneCochain.toLinearMap_add] using succ_nsmul β.toLinearMap n

instance : Module 𝕜 (LieOneCochain 𝕜 𝓰 𝓪) where
  one_smul β := by ext1; simp
  mul_smul c c' β := by
    ext1
    simpa only [toLinearMap_smul] using mul_smul c c' β.toLinearMap
  smul_zero β := by ext1; simp
  smul_add c β β' := by ext1; simp
  add_smul c c' β := by
    ext1
    simpa only [toLinearMap_smul, toLinearMap_add] using add_smul c c' β.toLinearMap
  zero_smul β := by ext1; simp

instance : AddCommGroup (LieOneCochain 𝕜 𝓰 𝓪) where
  zero_add β := AddZeroClass.zero_add β
  add_zero β := AddZeroClass.add_zero β
  nsmul := HSMul.hSMul
  nsmul_zero β := zero_nsmul β
  nsmul_succ n β := succ_nsmul β n
  neg β := (-1 : 𝕜) • β
  sub β₁ β₂ := β₁ + (-1 : 𝕜) • β₂
  zsmul k β := (k : 𝕜) • β
  zsmul_zero' β := by simp only [Int.cast_zero, zero_smul]
  zsmul_succ' k β := by simp [add_smul]
  zsmul_neg' k β := by simp [add_smul, smul_smul, add_comm]
  neg_add_cancel β := by
    nth_rewrite 2 [← one_smul 𝕜 β]
    simp only [← add_smul, neg_add_cancel, zero_smul]
  add_comm β₁ β₂ := AddCommMagma.add_comm β₁ β₂

variable {𝕜 𝓰 𝓪}

instance : FunLike (LieOneCochain 𝕜 𝓰 𝓪) 𝓰 𝓪 where
  coe := fun β X ↦ β.toLinearMap X
  coe_injective' := fun β β' h ↦ by ext1; exact LinearMap.ext_iff.mpr (congrFun h)

instance : LinearMapClass (LieOneCochain 𝕜 𝓰 𝓪) 𝕜 𝓰 𝓪 where
  map_add β X Y := β.toLinearMap.map_add X Y
  map_smulₛₗ β c X := LinearMap.CompatibleSMul.map_smul β.toLinearMap c X

end LieOneCochain -- namespace

end LieOneCochain -- section

section LieTwoCocycle

/-! ### Lie algebra 2-cocycles -/

/-- Lie algebra 2-cocycles. -/
@[ext] structure _root_.VirasoroProject.LieTwoCocycle where
  /-- The underlying bilinear map of a Lie algebra 2-cocycle. -/
  toBilin : 𝓰 →ₗ[𝕜] 𝓰 →ₗ[𝕜] 𝓪
  self' : ∀ X, toBilin X X = 0
  leibniz' : ∀ X Y Z, toBilin X ⁅Y, Z⁆ = toBilin ⁅X, Y⁆ Z + toBilin Y ⁅X, Z⁆

namespace LieTwoCocycle

instance : FunLike (LieTwoCocycle 𝕜 𝓰 𝓪) 𝓰 (𝓰 →ₗ[𝕜] 𝓪) where
  coe := fun γ X ↦ LieTwoCocycle.toBilin γ X
  coe_injective' := by
    intro γ γ' h
    ext
    exact congrFun (congrArg DFunLike.coe (congrFun h _)) _

instance : LinearMapClass (LieTwoCocycle 𝕜 𝓰 𝓪) 𝕜 𝓰 (𝓰 →ₗ[𝕜] 𝓪) where
  map_add γ X Y := (LieTwoCocycle.toBilin γ).map_add X Y
  map_smulₛₗ γ c X := (LieTwoCocycle.toBilin γ).map_smul c X

variable {𝕜 𝓰 𝓪}
variable (γ : LieTwoCocycle 𝕜 𝓰 𝓪)

@[simp]
lemma _root_.VirasoroProject.LieTwoCocycle.self {X : 𝓰} : γ X X = 0 := γ.self' X

lemma _root_.VirasoroProject.LieTwoCocycle.leibniz
    {X Y Z : 𝓰} : γ X ⁅Y, Z⁆ = γ ⁅X, Y⁆ Z + γ Y ⁅X, Z⁆ := γ.leibniz' X Y Z

lemma _root_.VirasoroProject.LieTwoCocycle.apply_add
    (X₁ X₂ Y : 𝓰) : γ (X₁ + X₂) Y = γ X₁ Y + γ X₂ Y := by simp

lemma _root_.VirasoroProject.LieTwoCocycle.apply_add₂
    (X Y₁ Y₂ : 𝓰) : γ X (Y₁ + Y₂) = γ X Y₁ + γ X Y₂ := by simp

lemma _root_.VirasoroProject.LieTwoCocycle.apply_smul
    (c : 𝕜) (X Y : 𝓰) : γ (c • X) Y = c • γ X Y := by simp

lemma _root_.VirasoroProject.LieTwoCocycle.apply_smul₂
    (c : 𝕜) (X Y : 𝓰) : γ X (c • Y) = c • γ X Y := by simp

lemma _root_.VirasoroProject.LieTwoCocycle.skew (X Y : 𝓰) : -(γ Y X) = γ X Y := by
  have aux : γ (X + Y) X + γ (X + Y) Y = 0 := by
    simpa only [← LieTwoCocycle.apply_add₂] using  LieTwoCocycle.self γ
  simpa [neg_eq_iff_add_eq_zero] using aux

instance : Zero (LieTwoCocycle 𝕜 𝓰 𝓪) where
  zero := { toBilin := 0 , self' := by simp , leibniz' := by simp }

instance : Add (LieTwoCocycle 𝕜 𝓰 𝓪) where
  add γ γ' :=
    { toBilin := γ.toBilin + γ'.toBilin
      self' := fun X ↦ by simp [γ.self', γ'.self']
      leibniz' := fun X Y Z ↦ by
        calc (γ.toBilin X) ⁅Y, Z⁆ + (γ'.toBilin X) ⁅Y, Z⁆
            = (γ.toBilin ⁅X, Y⁆) Z + (γ.toBilin Y) ⁅X, Z⁆
              + (γ'.toBilin ⁅X, Y⁆) Z + (γ'.toBilin Y) ⁅X, Z⁆ := by
              simp [γ.leibniz' X Y Z, γ'.leibniz' X Y Z, ← add_assoc]
          _ = ((γ.toBilin + γ'.toBilin) ⁅X, Y⁆) Z + ((γ.toBilin + γ'.toBilin) Y) ⁅X, Z⁆ := by
              simp only [LinearMap.add_apply]; ac_rfl }

instance : SMul 𝕜 (LieTwoCocycle 𝕜 𝓰 𝓪) where
  smul c γ :=
    { toBilin := c • γ.toBilin
      self' := fun X ↦ by simp [γ.self']
      leibniz' := fun X Y Z ↦ by simp only [LinearMap.smul_apply, γ.leibniz' X Y Z, smul_add] }

@[simp]
lemma _root_.VirasoroProject.LieTwoCocycle.toBilin_zero
    : (0 : LieTwoCocycle 𝕜 𝓰 𝓪).toBilin = 0 := rfl

@[simp]
lemma _root_.VirasoroProject.LieTwoCocycle.toBilin_add (γ γ' : LieTwoCocycle 𝕜 𝓰 𝓪) :
    (γ + γ').toBilin = γ.toBilin + γ'.toBilin := rfl

@[simp]
lemma _root_.VirasoroProject.LieTwoCocycle.toBilin_smul (c : 𝕜) (γ : LieTwoCocycle 𝕜 𝓰 𝓪) :
    (c • γ).toBilin = c • γ.toBilin := rfl

instance : AddCommMonoid (LieTwoCocycle 𝕜 𝓰 𝓪) where
  add_assoc γ γ' γ'' := by
    ext1
    simpa only [LieTwoCocycle.toBilin_add] using add_assoc ..
  zero_add γ := by ext1; simp only [LieTwoCocycle.toBilin_add, add_eq_right]; rfl
  add_zero γ := by ext1; simp only [LieTwoCocycle.toBilin_add, add_eq_left]; rfl
  add_comm γ γ' := by ext1; simpa only [LieTwoCocycle.toBilin_add] using AddCommMagma.add_comm ..
  nsmul n γ :=
    { toBilin := n • γ.toBilin
      self' := fun X ↦ by simp only [LinearMap.smul_apply, γ.self', smul_zero]
      leibniz' := fun X Y Z ↦ by simp only [LinearMap.smul_apply, γ.leibniz' X Y Z, smul_add] }
  nsmul_zero γ := by ext1; simp only [zero_smul]; rfl
  nsmul_succ n γ := by
    ext1
    simpa only [LieTwoCocycle.toBilin_add] using succ_nsmul γ.toBilin n

instance : Module 𝕜 (LieTwoCocycle 𝕜 𝓰 𝓪) where
  one_smul γ := by ext1; simp
  mul_smul c c' γ := by ext1; simpa using mul_smul c c' γ.toBilin
  smul_zero γ := by ext1; simp
  smul_add c γ γ' := by ext1; simp
  add_smul c c' γ := by ext1; simpa using Module.add_smul c c' γ.toBilin
  zero_smul γ := by ext1; simp

instance [LieAlgebra 𝕜 𝓰] [AddCommGroup 𝓪] [Module 𝕜 𝓪] :
    AddCommGroup (LieTwoCocycle 𝕜 𝓰 𝓪) where
  zero_add γ := AddZeroClass.zero_add γ
  add_zero γ := AddZeroClass.add_zero γ
  nsmul := HSMul.hSMul
  nsmul_zero γ := zero_nsmul γ
  nsmul_succ n γ := succ_nsmul γ n
  neg γ := (-1 : 𝕜) • γ
  sub γ₁ γ₂ := γ₁ + (-1 : 𝕜) • γ₂
  zsmul k γ := (k : 𝕜) • γ
  zsmul_zero' γ := by simp only [Int.cast_zero, zero_smul]
  zsmul_succ' k γ := by simp [add_smul]
  zsmul_neg' k γ := by simp [add_smul, smul_smul, add_comm]
  neg_add_cancel γ := by
    nth_rewrite 2 [← one_smul 𝕜 γ]
    simp only [← add_smul, neg_add_cancel, zero_smul]
  add_comm γ₁ γ₂ := AddCommMagma.add_comm γ₁ γ₂

lemma _root_.VirasoroProject.LieTwoCocycle.add_apply (γ₁ γ₂ : LieTwoCocycle 𝕜 𝓰 𝓪) (X Y : 𝓰) :
    (γ₁ + γ₂) X Y = γ₁ X Y + γ₂ X Y := rfl

lemma _root_.VirasoroProject.LieTwoCocycle.smul_apply (c : 𝕜) (γ : LieTwoCocycle 𝕜 𝓰 𝓪) (X Y : 𝓰) :
    (c • γ) X Y = c • γ X Y := rfl

lemma _root_.VirasoroProject.LieTwoCocycle.sub_apply (γ₁ γ₂ : LieTwoCocycle 𝕜 𝓰 𝓪) (X Y : 𝓰) :
    (γ₁ - γ₂) X Y = γ₁ X Y - γ₂ X Y := by
  simp only [sub_eq_add_neg, LieTwoCocycle.add_apply]
  rw [show -γ₂ = (-1 : 𝕜) • γ₂ from rfl, LieTwoCocycle.smul_apply]
  simp

@[simp] lemma _root_.VirasoroProject.LieTwoCocycle.zero_apply
    (X Y : 𝓰) : (0 : LieTwoCocycle 𝕜 𝓰 𝓪) X Y = 0 := rfl

@[simp] lemma _root_.VirasoroProject.LieTwoCocycle.zero_apply'
    (X : 𝓰) : (0 : LieTwoCocycle 𝕜 𝓰 𝓪) X = 0 := rfl

end LieTwoCocycle -- namespace

end LieTwoCocycle -- section

section LieTwoCoboundary

/-! ### Lie algebra 2-coboundaries -/

variable {𝕜 𝓰 𝓪}

/-- A Lie algebra 1-cochain determines a bilinear map via the differential. -/
def _root_.VirasoroProject.LieOneCochain.bdry' (β : LieOneCochain 𝕜 𝓰 𝓪) : 𝓰 →ₗ[𝕜] 𝓰 →ₗ[𝕜] 𝓪 where
  toFun := fun X ↦ β ∘ₗ LieAlgebra.bracketHom 𝕜 𝓰 X
  map_add' X₁ X₂ := by simp_all only [map_add]; ext; simp_all
  map_smul' c X := by simp_all only [LinearMapClass.map_smul, RingHom.id_apply]; ext; simp_all

/-- A Lie algebra 1-cochain linearly determines a bilinear map via the differential. -/
def _root_.VirasoroProject.LieOneCochain.bdryHom'
    : LieOneCochain 𝕜 𝓰 𝓪 →ₗ[𝕜] 𝓰 →ₗ[𝕜] 𝓰 →ₗ[𝕜] 𝓪 where
  toFun := fun β ↦ LieOneCochain.bdry' β
  map_add' β₁ β₂ := by ext X Y; rfl
  map_smul' c Z := by ext X Y; rfl

/-- The `∂` of a Lie algebra 1-cochain as a Lie algebra 2-cocycle. -/
def _root_.VirasoroProject.LieOneCochain.bdry (β : LieOneCochain 𝕜 𝓰 𝓪) : LieTwoCocycle 𝕜 𝓰 𝓪 where
  toBilin := LieOneCochain.bdryHom' β
  self' X := by simp [LieOneCochain.bdryHom', LieOneCochain.bdry']
  leibniz' X Y Z := by simp [LieOneCochain.bdryHom', LieOneCochain.bdry']

variable (𝕜 𝓰 𝓪)

/-- The `∂` as a linear map from Lie algebra 1-cochains to Lie algebra 2-cocycles. -/
def _root_.VirasoroProject.LieOneCochain_bdryHom
    : LieOneCochain 𝕜 𝓰 𝓪 →ₗ[𝕜] LieTwoCocycle 𝕜 𝓰 𝓪 where
  toFun β := β.bdry
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma _root_.VirasoroProject.LieOneCochain.neg_bdry
    (β : LieOneCochain 𝕜 𝓰 𝓪) : (-β).bdry = -β.bdry := by
  change LieOneCochain_bdryHom 𝕜 𝓰 𝓪 (-β) = -LieOneCochain_bdryHom 𝕜 𝓰 𝓪 β
  simp

lemma _root_.VirasoroProject.LieOneCochain.bdry_apply (β : LieOneCochain 𝕜 𝓰 𝓪) (X Y : 𝓰) :
    β.bdry X Y = β (⁅X, Y⁆) := rfl

/-- Lie algebra 2-coboundaries as a vector space. -/
abbrev _root_.VirasoroProject.LieTwoCoboundary := LinearMap.range (LieOneCochain_bdryHom 𝕜 𝓰 𝓪)

end LieTwoCoboundary -- section

section LieTwoCohomology

/-! ### Lie algebra 2-cohomology -/

/-- The 2-cohomology `H²(𝓰,𝓪)` of a Lie algebra `𝓰` with coefficients in `𝓪`. -/
def _root_.VirasoroProject.LieTwoCohomology := LieTwoCocycle 𝕜 𝓰 𝓪 ⧸ LieTwoCoboundary 𝕜 𝓰 𝓪

namespace LieTwoCohomology

/-- The 2-cohomology `H²(𝓰,𝓪)` is an additive commutative group. -/
instance : AddCommGroup (LieTwoCohomology 𝕜 𝓰 𝓪) :=
  Submodule.Quotient.addCommGroup (LieTwoCoboundary 𝕜 𝓰 𝓪)

/-- The 2-cohomology `H²(𝓰,𝓪)` is a module over the scalar ring `𝕜`. -/
instance : Module 𝕜 (LieTwoCohomology 𝕜 𝓰 𝓪) :=
  Submodule.Quotient.module' _

end LieTwoCohomology -- namespace

namespace LieTwoCocycle

/-- The linear map from 2-cocycles to 2-cohomologies of a Lie algebra `𝓰` with coefficients
in `𝓪`. -/
def _root_.VirasoroProject.LieTwoCocycle.toLieTwoCohomology
    : LieTwoCocycle 𝕜 𝓰 𝓪 →ₗ[𝕜] LieTwoCohomology 𝕜 𝓰 𝓪 :=
  (LieTwoCoboundary 𝕜 𝓰 𝓪).mkQ

lemma _root_.VirasoroProject.LieTwoCocycle.range_toLieTwoCohomology_eq_top :
    LinearMap.range (toLieTwoCohomology 𝕜 𝓰 𝓪) = ⊤ :=
  Submodule.range_mkQ ..

variable {𝕜 𝓰 𝓪}

/-- The projection to 2-cohomologies from 2-cocycles of a Lie algebra `𝓰` with coefficients
in `𝓪`. (This definition is to enable dot notation, while the linear map version doesn't.) -/
def _root_.VirasoroProject.LieTwoCocycle.cohomologyClass
    (γ : LieTwoCocycle 𝕜 𝓰 𝓪) : LieTwoCohomology 𝕜 𝓰 𝓪 :=
  LieTwoCocycle.toLieTwoCohomology _ _ _ γ

/-- Adding a coboundary does not change the cohomology class. -/
lemma _root_.VirasoroProject.LieTwoCocycle.cohomologyClass_add_bdry
    (γ : LieTwoCocycle 𝕜 𝓰 𝓪) (β : LieOneCochain 𝕜 𝓰 𝓪) :
    (γ + β.bdry).cohomologyClass = γ.cohomologyClass := by
  simp only [cohomologyClass, map_add, add_eq_left]
  exact (Submodule.Quotient.mk_eq_zero _).mpr <| LinearMap.mem_range.mpr ⟨β, rfl⟩

/-- A cocycle representing a trivial cohomology class is a coboundary. -/
lemma _root_.VirasoroProject.LieTwoCocycle.exists_eq_bdry
    (γ : LieTwoCocycle 𝕜 𝓰 𝓪) (hγ : γ.cohomologyClass = 0) :
    ∃ β : LieOneCochain 𝕜 𝓰 𝓪, γ = β.bdry := by
  simp_rw [@Eq.comm (LieTwoCocycle 𝕜 𝓰 𝓪) γ _]
  simpa using (Submodule.Quotient.eq _).mp <|
    show γ.cohomologyClass = LieTwoCocycle.cohomologyClass 0 by rw [hγ]; rfl

end LieTwoCocycle -- namespace

end LieTwoCohomology -- section

section IsLieAbelian

variable [IsLieAbelian 𝓰]

variable {𝕜 𝓰 𝓪}

/-- For abelian Lie algebras, a 2-coboundary is necessarily zero. -/
lemma _root_.VirasoroProject.LieOneCochain.bdry_apply_eq_zero_of_isLieAbelian
    (β : LieOneCochain 𝕜 𝓰 𝓪) (X Y : 𝓰) :
    β.bdry X Y = 0 := by
  simp [LieOneCochain.bdry_apply]

variable (𝕜 𝓰 𝓪)

/-- For abelian Lie algebras, the space of 2-coboundaries is the zero vector space. -/
lemma _root_.VirasoroProject.LieTwoCoboundary.eq_bot_of_isLieAbelian :
    LieTwoCoboundary 𝕜 𝓰 𝓪 = ⊥ := by
  refine LinearMap.range_eq_bot.mpr ?_
  ext β X Y
  exact β.bdry_apply_eq_zero_of_isLieAbelian X Y

/-- For abelian Lie algebras, the map from 2-cocycles to their cohomology classes has
trivial kernel. -/
lemma _root_.VirasoroProject.LieTwoCocycle.ker_toLieTwoCohomology_eq_bot_of_isLieAbelian :
    LinearMap.ker (LieTwoCocycle.toLieTwoCohomology 𝕜 𝓰 𝓪) = ⊥ := by
  rw [LieTwoCocycle.toLieTwoCohomology]
  exact (LieTwoCoboundary 𝕜 𝓰 𝓪).ker_mkQ.trans
    (LieTwoCoboundary.eq_bot_of_isLieAbelian 𝕜 𝓰 𝓪)

/-- For abelian Lie algebras, the map from 2-cocycles to their cohomology classes is a linear
equivalence. -/
noncomputable def _root_.VirasoroProject.LieTwoCocycle.toLieTwoCohomologyEquiv :
    LieTwoCocycle 𝕜 𝓰 𝓪 ≃ₗ[𝕜] LieTwoCohomology 𝕜 𝓰 𝓪 :=
  LinearEquiv.ofBijective (LieTwoCocycle.toLieTwoCohomology 𝕜 𝓰 𝓪)
    ⟨LinearMap.ker_eq_bot.mp <| LieTwoCocycle.ker_toLieTwoCohomology_eq_bot_of_isLieAbelian ..,
     LinearMap.range_eq_top.mp <| LieTwoCocycle.range_toLieTwoCohomology_eq_top ..⟩

lemma _root_.VirasoroProject.LieTwoCocycle.toLieTwoCohomologyEquiv_toLinearMap :
    (LieTwoCocycle.toLieTwoCohomologyEquiv 𝕜 𝓰 𝓪).toLinearMap =
      LieTwoCocycle.toLieTwoCohomology 𝕜 𝓰 𝓪 := rfl

end IsLieAbelian --section

end VirasoroProject -- namespace
