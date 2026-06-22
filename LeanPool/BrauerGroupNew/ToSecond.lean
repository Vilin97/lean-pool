/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

import LeanPool.BrauerGroupNew.CrossProductAlgebra
import LeanPool.BrauerGroupNew.Mathlib.RingTheory.Congruence.Defs
import LeanPool.BrauerGroupNew.Subfield.Splitting
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# LeanPool.BrauerGroupNew.ToSecond

Imported Lean Pool material for `LeanPool.BrauerGroupNew.ToSecond`.
-/

suppress_compilation

open FiniteDimensional BrauerGroup Module groupCohomology

variable {F K : Type} [Field K] [Field F] [Algebra F K]
variable (X : BrauerGroup F)

variable (K) in
/-- A relative Brauer class representative with a splitting-field embedding. -/
structure GoodRep extends CSA.{0, 0} F where
  /-- The underlying central simple algebra represents the chosen Brauer class. -/
  quot_eq : Quotient.mk'' toCSA = X
  /-- The chosen algebra embedding of the splitting field into the representative. -/
  ι : K →ₐ[F] toAlgCat
  /-- The representative has the expected square dimension over the base field. -/
  dim_eq_sq : Module.finrank F carrier = (Module.finrank F K) ^ 2

namespace GoodRep

variable {X : BrauerGroup F} (A B : GoodRep K X)

instance : CoeSort (GoodRep K X) Type where
  coe A := A.carrier

/-- The splitting-field embedding identifies `K` with its range. -/
def ιRange : K ≃ₐ[F] A.ι.range := .ofInjective _ (RingHom.injective _)

instance : Algebra F A := inferInstanceAs <| Algebra F A

instance : IsSimpleOrder (TwoSidedIdeal A.ι.range) :=
  TwoSidedIdeal.orderIsoOfRingEquiv A.ιRange.symm |>.isSimpleOrder

lemma centralizerιRange : Subalgebra.centralizer F A.ι.range = A.ι.range := by
  let L : SubField F A :=
  { __ := A.ι.range
    mul_comm := by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← map_mul, mul_comm]
    exists_inverse := by
      rintro _ ⟨x, rfl⟩ hx
      refine ⟨A.ι x⁻¹, by simp, ?_⟩
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← map_mul]
      rw [mul_inv_cancel₀, map_one]
      rintro rfl
      simp at hx }
  change Subalgebra.centralizer F (L.toSubalgebra : Set A) = L.toSubalgebra
  apply cor_two_3to1
  apply cor_two_2to3
  change Module.finrank F A = Module.finrank F A.ι.range * Module.finrank F A.ι.range
  rw [A.dim_eq_sq, pow_two, LinearEquiv.finrank_eq (f := A.ιRange.toLinearEquiv.symm)]

instance : Module K A where
  smul c a := A.ι c * a
  one_smul a := show A.ι 1 * a = a by simp
  mul_smul c c' x := show A.ι (c * c') * x = _ * (_ * _) by simp [_root_.mul_assoc]
  smul_zero c := show A.ι c * 0 = 0 by simp
  smul_add c x y := show A.ι c * (x + y) = _ * _ + _ * _ by simp [_root_.mul_add]
  add_smul c c' x := show A.ι (c + c') * x = _ * _ + _ * _ by simp [_root_.add_mul]
  zero_smul x := show A.ι 0 * x = 0 by simp

@[simp]
lemma smul_def (c : K) (a : A) : c • a = A.ι c * a := rfl

instance : FiniteDimensional F A := A.fin_dim

instance : IsScalarTower F K A where
  smul_assoc a b c := by simp

instance : FiniteDimensional K A := FiniteDimensional.right F K A

lemma dim_eq' [FiniteDimensional F K] : Module.finrank K A = Module.finrank F K := by
  have : Module.finrank F A = Module.finrank F K * Module.finrank K A :=
    Eq.symm (Module.finrank_mul_finrank F K A.carrier)
  rw [A.dim_eq_sq, pow_two] at this
  simp only [mul_eq_mul_left_iff] at this
  refine this.recOn Eq.symm fun rid ↦ ?_
  have : 0 < Module.finrank F K := Module.finrank_pos
  omega

variable (ρ σ τ : Gal(K, F))

/-- A unit implementing the Galois action by conjugation on the embedded splitting field. -/
def conjFactor (σ : Gal(K, F)) : Type := {a : Aˣ // ∀ x : K, A.ι (σ x) = a * A.ι x * a⁻¹}

/-- A chosen conjugating unit for each Galois automorphism, supplied by Skolem-Noether. -/
def arbitraryConjFactor : A.conjFactor σ where
  val := SkolemNoether' F A K A.ι (A.ι.comp σ) |>.choose
  property x := SkolemNoether' F A K A.ι (A.ι.comp σ) |>.choose_spec x

variable {A ρ σ τ}

@[simp] lemma conjFactor_prop (x : A.conjFactor σ) (c : K) :
    x.1 * A.ι c * x.1⁻¹ = A.ι (σ c) := x.2 c |>.symm

/-- The product of two conjugating units as a conjugating unit for the product automorphism. -/
def mul' (x : A.conjFactor σ) (y : A.conjFactor τ) : A.conjFactor (σ * τ) :=
⟨x.1 * y.1, fun c ↦ by
  simp only [AlgEquiv.mul_apply, Units.val_mul, _root_.mul_assoc, mul_inv_rev]
  rw [← _root_.mul_assoc (A.ι c), ← mul_assoc (y.1 : A), ← mul_assoc (y.1 : A),
    conjFactor_prop, ← _root_.mul_assoc, conjFactor_prop]⟩

@[simp]
lemma mul'_coe (x : A.conjFactor σ) (y : A.conjFactor τ) : (mul' x y).1.1 = x.1 * y.1 := rfl

lemma conjFactor_rel_aux (x y : A.conjFactor σ) :
    ∃ (c : K), x.1 = y.1 * A.ι c := by
  have mem1 : (y.1⁻¹ * x.1 : A) ∈ Subalgebra.centralizer F A.ι.range := by
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨z, rfl⟩
    have := x.2 z |>.symm.trans (y.2 z)
    apply_fun (x.1⁻¹.1 * ·) at this
    simp only [← _root_.mul_assoc, Units.inv_mul, _root_.one_mul] at this
    apply_fun (· * x.1.1) at this
    simp only [Units.inv_mul_cancel_right] at this
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    conv_rhs => rw [this]
    simp only [_root_.mul_assoc, Units.mul_inv_cancel_left, Units.inv_mul_cancel_left]
  rw [A.centralizerιRange, AlgHom.mem_range] at mem1
  obtain ⟨c, hc⟩ := mem1
  use c
  simp only [hc, Units.mul_inv_cancel_left]

lemma conjFactor_rel (x y : A.conjFactor σ) :
    ∃! (c : K), x.1 = y.1 * A.ι c := by
  obtain ⟨c, hc⟩ := conjFactor_rel_aux x y
  refine ⟨c, hc, fun c' (hc' : _ = _) => ?_⟩
  rw [hc] at hc'
  simp only [Units.mul_right_inj] at hc'
  exact RingHom.injective _ hc' |>.symm

/-- The scalar comparing two conjugating units for the same automorphism. -/
def conjFactorTwistCoeff (x y : A.conjFactor σ) : K := conjFactor_rel x y |>.choose

lemma conjFactorTwistCoeff_spec (x y : A.conjFactor σ) :
    x.1 = y.1 * A.ι (conjFactorTwistCoeff x y) := conjFactor_rel x y |>.choose_spec.1

lemma conjFactorTwistCoeff_unique (x y : A.conjFactor σ) (c : K) (h : x.1 = y.1 * A.ι c) :
    c = conjFactorTwistCoeff x y :=
  conjFactor_rel x y |>.choose_spec.2 _ h

@[simp]
lemma conjFactorTwistCoeff_self (x : A.conjFactor σ) : conjFactorTwistCoeff x x = 1 :=
  Eq.symm <| conjFactorTwistCoeff_unique _ _ _ <| by simp

/-- The twist coefficient packaged as a unit. -/
@[simps -isSimp]
def conjFactorTwistCoeffAsUnit (x y : A.conjFactor σ) : Kˣ where
  val := conjFactorTwistCoeff x y
  inv := conjFactorTwistCoeff y x
  val_inv := by
    simpa using conjFactorTwistCoeff_unique y y
      (conjFactorTwistCoeff x y * conjFactorTwistCoeff y x)
      (by simp only [map_mul, ← _root_.mul_assoc, ← conjFactorTwistCoeff_spec])
  inv_val := by
    simpa using conjFactorTwistCoeff_unique x x
      (conjFactorTwistCoeff y x * conjFactorTwistCoeff x y)
      (by simp only [map_mul, ← _root_.mul_assoc, ← conjFactorTwistCoeff_spec])

@[simp]
lemma conjFactorTwistCoeff_swap (x y : A.conjFactor σ) :
    conjFactorTwistCoeff x y * conjFactorTwistCoeff y x = 1 :=
    conjFactorTwistCoeffAsUnit x y |>.val_inv

lemma conjFactorTwistCoeff_inv (x y : A.conjFactor σ) :
    conjFactorTwistCoeff x y = (conjFactorTwistCoeff y x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simp

lemma conjFactorTwistCoeff_swap' (x y : A.conjFactor σ) :
    conjFactorTwistCoeff y x * conjFactorTwistCoeff x y = 1 :=
    conjFactorTwistCoeffAsUnit y x |>.val_inv

@[simp]
lemma conjFactorTwistCoeff_swap'' (x y : A.conjFactor σ) :
    A.ι (conjFactorTwistCoeff x y) * A.ι (conjFactorTwistCoeff y x) = 1 := by
  simp [← map_mul]

lemma conjFactorTwistCoeff_swap''' (x y : A.conjFactor σ) :
    A.ι (conjFactorTwistCoeff y x) * A.ι (conjFactorTwistCoeff x y) = 1 := by
  simp [← map_mul]

lemma conjFactorTwistCoeff_spec' (x y : A.conjFactor σ) :
    x.1 = A.ι (σ <| conjFactorTwistCoeff x y) * y.1 := by
  calc x.1.1
    _ = x.1 * A.ι (conjFactorTwistCoeff x y) * x.1⁻¹ * (x.1 * A.ι (conjFactorTwistCoeff y x)) := by
        simp only [_root_.mul_assoc, Units.inv_mul_cancel_left, conjFactorTwistCoeff_swap'',
          _root_.mul_one]
    _ = A.ι (σ <| conjFactorTwistCoeff x y) * (x.1 * A.ι (conjFactorTwistCoeff y x)) := by
        simp only [conjFactor_prop]
    _ = A.ι (σ <| conjFactorTwistCoeff x y) * y.1 := by
        simp [← conjFactorTwistCoeff_spec]

/-- The scalar measuring the defect of the chosen conjugating units from being multiplicative. -/
def conjFactorCompCoeff (x : A.conjFactor σ) (y : A.conjFactor τ) (z : A.conjFactor (σ * τ)) : K :=
    σ <| τ <| conjFactorTwistCoeff (mul' x y) z

/-- The composition coefficient packaged as a unit. -/
@[simps -isSimp]
def conjFactorCompCoeffAsUnit
    (x : A.conjFactor σ) (y : A.conjFactor τ) (z : A.conjFactor (σ * τ)) : Kˣ where
  val := conjFactorCompCoeff x y z
  inv := σ <| τ <| conjFactorTwistCoeff z (mul' x y)
  val_inv := by
    simp only [conjFactorCompCoeff, ← map_mul, conjFactorTwistCoeff_swap, map_one]
  inv_val := by
    simp only [conjFactorCompCoeff, ← map_mul, conjFactorTwistCoeff_swap, map_one]

lemma conjFactorCompCoeff_spec
    (x : A.conjFactor σ) (y : A.conjFactor τ) (z : A.conjFactor (σ * τ)) :
    (x.1 * y.1 : A) = A.ι (conjFactorCompCoeff x y z) * z.1 :=
  conjFactorTwistCoeff_spec' (mul' x y) z

lemma conjFactorCompCoeff_spec'_ (x : A.conjFactor σ) (y : A.conjFactor τ)
    (z : A.conjFactor (σ * τ)) :
    A.ι (conjFactorCompCoeffAsUnit x y z)⁻¹ * (x.1 * y.1 : A) = z.1 := by
  rw [conjFactorCompCoeff_spec (z := z), ← _root_.mul_assoc, ← map_mul]
  simp only [conjFactorCompCoeffAsUnit, AlgEquiv.mul_apply]
  rw [inv_mul_cancel₀, map_one, _root_.one_mul]
  exact Units.ne_zero (conjFactorCompCoeffAsUnit x y z)

lemma conjFactorCompCoeff_spec' (x : A.conjFactor σ) (y : A.conjFactor τ)
    (z : A.conjFactor (σ * τ)) :
    A.ι (σ <| τ <| conjFactorTwistCoeff z (mul' x y)) * (x.1 * y.1 : A) = z.1 := by
  convert conjFactorCompCoeff_spec'_ x y z using 3
  norm_cast

lemma conjFactorCompCoeff_spec'' (x : A.conjFactor σ) (y : A.conjFactor τ)
    (z : A.conjFactor (σ * τ)) :
    A.ι (conjFactorCompCoeff x y z) = x.1 * y.1 * z.1⁻¹ := by
  suffices A.ι (conjFactorCompCoeff x y z) * z.val.val = x.val.val * y.val.val by simp [← this]
  rw [← A.conjFactorCompCoeff_spec' x y z]
  simp only [conjFactorCompCoeff, ← _root_.mul_assoc, ← map_mul, conjFactorTwistCoeff_swap, map_one,
    _root_.one_mul]

lemma conjFactorCompCoeff_inv (x : A.conjFactor σ) (y : A.conjFactor τ) (z : A.conjFactor (σ * τ)) :
    A.ι ((conjFactorCompCoeff x y z)⁻¹) = z.1 * (y.1⁻¹ * x.1⁻¹) := by
  suffices eq : Units.map A.ι (conjFactorCompCoeffAsUnit x y z)⁻¹ = z.1 * (y.1⁻¹ * x.1⁻¹) by
    rw [Units.ext_iff] at eq
    simp only [conjFactorCompCoeffAsUnit, Units.inv_mk, Units.coe_map, MonoidHom.coe_coe,
      AlgEquiv.mul_apply, Units.val_mul] at eq
    rw [← eq]
    congr 1
    symm
    apply eq_inv_of_mul_eq_one_left
    simp only [conjFactorCompCoeff, ← map_mul, conjFactorTwistCoeff_swap, map_one]
  rw [map_inv, inv_eq_iff_mul_eq_one]
  ext
  simp [conjFactorCompCoeffAsUnit, conjFactorCompCoeff_spec'', _root_.mul_assoc]

lemma conjFactorCompCoeff_comp_comp₁
    (xρ : A.conjFactor ρ) (xσ : A.conjFactor σ) (xτ : A.conjFactor τ)
    (xρσ : A.conjFactor (ρ * σ))
    (xρστ : A.conjFactor (ρ * σ * τ)) :
    xρ.1.1 * xσ.1 * xτ.1 =
    A.ι (conjFactorCompCoeff xρ xσ xρσ) *
    A.ι (conjFactorCompCoeff xρσ xτ xρστ) *
    xρστ.1 := by
  rw [conjFactorCompCoeff_spec (z := xρσ), _root_.mul_assoc,
    conjFactorCompCoeff_spec (z := xρστ), ← _root_.mul_assoc]

lemma conjFactorCompCoeff_eq (x : A.conjFactor σ) (y : A.conjFactor τ) (z : A.conjFactor (σ * τ)) :
    A.ι (conjFactorCompCoeff x y z) = (x.1 * y.1) * z.1⁻¹ := by
  have := conjFactorTwistCoeff_spec' (mul' x y) z
  simp only [AlgEquiv.mul_apply, mul'_coe] at this
  rw [this]
  simp only [AlgEquiv.mul_apply, Units.mul_inv_cancel_right]
  rfl

lemma conjFactorCompCoeff_comp_comp₂
    (xρ : A.conjFactor ρ) (xσ : A.conjFactor σ) (xτ : A.conjFactor τ)
    (xστ : A.conjFactor (σ * τ))
    (xρστ : A.conjFactor (ρ * σ * τ)) :
    xρ.1.1 * (xσ.1 * xτ.1) =
    A.ι (ρ <| conjFactorCompCoeff xσ xτ xστ) *
    A.ι (conjFactorCompCoeff xρ xστ xρστ) *
    xρστ.1 := by
  have eq1 :
      xρ.1 * A.ι (conjFactorCompCoeff xσ xτ xστ) =
      A.ι (ρ <| conjFactorCompCoeff xσ xτ xστ) * xρ.1 := by
    have := xρ.2 (conjFactorCompCoeff xσ xτ xστ)
    conv_rhs => rw [this, _root_.mul_assoc]
    simp
  conv_lhs => rw [conjFactorCompCoeff_spec (z := xστ), ← _root_.mul_assoc, eq1]
  conv_rhs => rw [_root_.mul_assoc, ← conjFactorCompCoeff_spec, ← _root_.mul_assoc]

lemma conjFactorCompCoeff_comp_comp₃
    (xρ : A.conjFactor ρ) (xσ : A.conjFactor σ) (xτ : A.conjFactor τ)
    (xρσ : A.conjFactor (ρ * σ)) (xστ : A.conjFactor (σ * τ))
    (xρστ : A.conjFactor (ρ * σ * τ)) :
    A.ι (conjFactorCompCoeff xρ xσ xρσ) *
    A.ι (conjFactorCompCoeff xρσ xτ xρστ) *
    xρστ.1 =
    A.ι (ρ <| conjFactorCompCoeff xσ xτ xστ) *
    A.ι (conjFactorCompCoeff xρ xστ xρστ) *
    xρστ.1 := by
  rw [← conjFactorCompCoeff_comp_comp₁, ← conjFactorCompCoeff_comp_comp₂, _root_.mul_assoc]

lemma conjFactorCompCoeff_comp_comp
    (xρ : A.conjFactor ρ) (xσ : A.conjFactor σ) (xτ : A.conjFactor τ)
    (xρσ : A.conjFactor (ρ * σ)) (xστ : A.conjFactor (σ * τ))
    (xρστ : A.conjFactor (ρ * σ * τ)) :
    conjFactorCompCoeff xρ xσ xρσ *
    conjFactorCompCoeff xρσ xτ xρστ =
    (ρ <| conjFactorCompCoeff xσ xτ xστ) *
    conjFactorCompCoeff xρ xστ xρστ := by
  apply_fun A.ι using RingHom.injective _
  simpa using conjFactorCompCoeff_comp_comp₃ xρ xσ xτ xρσ xστ xρστ

variable (A) in
/-- The two-cocycle associated to a system of conjugating units. -/
def toCocycles₂ (x_ : Π σ, A.conjFactor σ) : Gal(K, F) × Gal(K, F) → Kˣ :=
fun p =>
  conjFactorCompCoeffAsUnit
    (x_ p.1)
    (x_ p.2)
    (x_ <| p.1 * p.2)

variable (ρ σ τ) in
lemma toCocycles₂_cond (x_ : Π σ, A.conjFactor σ) :
    ρ (A.toCocycles₂ x_ (σ, τ)).1 * A.toCocycles₂ x_ (ρ, σ * τ) =
    A.toCocycles₂ x_ (ρ, σ) * A.toCocycles₂ x_ (ρ * σ, τ) := by
  delta toCocycles₂
  dsimp only [conjFactorCompCoeffAsUnit, AlgEquiv.mul_apply]
  rw [conjFactorCompCoeff_comp_comp]
  rfl

lemma isMulCocycle₂ (x_ : Π σ, A.conjFactor σ) :
    groupCohomology.IsMulCocycle₂ (A.toCocycles₂ x_) := by
  intro ρ σ τ
  ext : 1
  simp only [Units.val_mul]
  erw [A.toCocycles₂_cond ρ σ τ]
  rw [mul_comm]

variable {σ τ : Gal(K, F)}

lemma exists_iso :
    Nonempty (A ≃ₐ[F] B) := by
  obtain ⟨D, _, _, m, n, hm, hn, ⟨isoA⟩, ⟨isoB⟩⟩ :=
    IsBrauerEquivalent.exists_common_division_algebra F A.toCSA B.toCSA
      (Quotient.eq''.1 (A.quot_eq.trans B.quot_eq.symm))
  have eq1 := isoA.toLinearEquiv.finrank_eq
  have eq2 := isoB.toLinearEquiv.finrank_eq
  simp only [A.dim_eq_sq, LinearEquiv.finrank_eq (matrixEquivTensor (Fin m) F D).toLinearEquiv,
    Module.finrank_tensorProduct, Module.finrank_matrix, Fintype.card_fin, Module.finrank_self,
    _root_.mul_one] at eq1
  simp only [B.dim_eq_sq, LinearEquiv.finrank_eq (matrixEquivTensor (Fin n) F D).toLinearEquiv,
    Module.finrank_tensorProduct, Module.finrank_matrix, Fintype.card_fin, Module.finrank_self,
    _root_.mul_one] at eq2
  have eq3 := eq1.symm.trans eq2
  haveI : FiniteDimensional F D := is_fin_dim_of_wdb _ _ (NeZero.ne _) _ isoB
  have : 0 < Module.finrank F D := Module.finrank_pos
  rw [Nat.mul_right_inj (by omega), ← pow_two, ← pow_two] at eq3
  simp only [zero_le, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_left_inj₀] at eq3
  subst eq3
  exact ⟨isoA.trans isoB.symm⟩

/-- A chosen algebra equivalence between two representatives of the same Brauer class. -/
def iso : A ≃ₐ[F] B := exists_iso (A := A) (B := B) |>.some

/-- The unit conjugating the transported splitting-field embedding to the target embedding. -/
def isoConjCoeff : Bˣ :=
  SkolemNoether' F B K (AlgHom.comp (A.iso B).toAlgHom A.ι) B.ι |>.choose

lemma isoConjCoeff_spec :
    ∀ r : K, B.ι r = (A.isoConjCoeff B) * (A.iso B <| A.ι r) * (A.isoConjCoeff B)⁻¹ :=
  SkolemNoether' F B K (AlgHom.comp (A.iso B).toAlgHom A.ι) B.ι |>.choose_spec

lemma isoConjCoeff_spec' :
    ∀ r : K, (A.isoConjCoeff B)⁻¹ * B.ι r * (A.isoConjCoeff B) = (A.iso B <| A.ι r) := by
  intro c
  rw [A.isoConjCoeff_spec B c]
  simp [_root_.mul_assoc]

lemma isoConjCoeff_spec'' (c : K) (x : A.conjFactor σ) :
    B.ι (σ c) =
    (A.isoConjCoeff B * (A.iso B <| x.1) * (A.isoConjCoeff B)⁻¹) *
      B.ι c *
    (A.isoConjCoeff B * (A.iso B <| x.1⁻¹.1) * (A.isoConjCoeff B)⁻¹) := by
  have eq1 := congr(A.iso B $(x.2 c))
  have eq2 := A.isoConjCoeff_spec B (σ c)
  simp only [eq1, map_mul] at eq2
  simp only [eq2, _root_.mul_assoc, Units.mul_right_inj]
  congr 1
  simp only [← _root_.mul_assoc, Units.mul_left_inj]
  congr 1
  rw [isoConjCoeff_spec']

/-- Transport a conjugating unit across the chosen algebra equivalence. -/
def pushConjFactor (x : A.conjFactor σ) : B.conjFactor σ where
  val :=
  { val := A.isoConjCoeff B * (A.iso B <| x.1) * (A.isoConjCoeff B)⁻¹
    inv := A.isoConjCoeff B * (A.iso B <| x.1⁻¹.1) * (A.isoConjCoeff B)⁻¹
    val_inv := by
      simp only [← _root_.mul_assoc, Units.inv_mul_cancel_right, Units.mul_inv_eq_one]
      simp only [_root_.mul_assoc, ← map_mul, Units.mul_inv, map_one, _root_.mul_one]
    inv_val := by
      simp only [← _root_.mul_assoc, Units.inv_mul_cancel_right, Units.mul_inv_eq_one]
      simp only [_root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.mul_one] }
  property c := by
    simp only [Units.inv_mk]
    rw [isoConjCoeff_spec'']

@[simp] lemma pushConjFactor_coe (x : A.conjFactor σ) :
    (A.pushConjFactor B x).1.1 = A.isoConjCoeff B * (A.iso B <| x.1) * (A.isoConjCoeff B)⁻¹ :=
    rfl

/-- The scalar comparing a transported conjugating unit with a chosen target unit. -/
def pushConjFactorCoeff (x : A.conjFactor σ) (y : B.conjFactor σ) : K :=
σ (conjFactorTwistCoeff y (A.pushConjFactor B x))

lemma pushConjFactorCoeff_spec (x : A.conjFactor σ) (y : B.conjFactor σ) :
    y.1 = B.ι (A.pushConjFactorCoeff B x y) * (A.pushConjFactor B x).1 :=
  conjFactorTwistCoeff_spec' y (A.pushConjFactor B x)

lemma pushConjFactorCoeff_spec' (x : A.conjFactor σ) (y : B.conjFactor σ) :
    B.ι (A.pushConjFactorCoeff B x y) =
    A.isoConjCoeff B *
    A.iso B (A.ι <| A.pushConjFactorCoeff B x y) *
    (A.isoConjCoeff B)⁻¹:= by
  rw [isoConjCoeff_spec]

/-- The transported-unit comparison scalar packaged as a unit. -/
@[simps]
abbrev pushConjFactorCoeffAsUnit (x : A.conjFactor σ) (y : B.conjFactor σ) : Kˣ where
  val := A.pushConjFactorCoeff B x y
  inv := σ (conjFactorTwistCoeff (A.pushConjFactor B x) y)
  val_inv := by simp [pushConjFactorCoeff, ← map_mul]
  inv_val := by simp [pushConjFactorCoeff, ← map_mul]

lemma compare_conjFactorCompCoeff
    (xσ : A.conjFactor σ) (yσ : B.conjFactor σ) (xτ : A.conjFactor τ) (yτ : B.conjFactor τ)
    (xστ : A.conjFactor (σ * τ)) (yστ : B.conjFactor (σ * τ)) :
    B.conjFactorCompCoeff yσ yτ yστ *
    A.pushConjFactorCoeff B xστ yστ =
    A.pushConjFactorCoeff B xσ yσ *
    σ (A.pushConjFactorCoeff B xτ yτ) *
    A.conjFactorCompCoeff xσ xτ xστ := by
  have eq1 := B.conjFactorCompCoeff_spec yσ yτ yστ
  have eq2 : yσ.1.1 * yτ.1.1 =
      (A.isoConjCoeff B) *
      A.iso B
        (A.ι (A.pushConjFactorCoeff B xσ yσ) *
          xσ.1 *
          A.ι (A.pushConjFactorCoeff B xτ yτ) *
          xτ.1) *
      (A.isoConjCoeff B)⁻¹ := by
    rw [A.pushConjFactorCoeff_spec B xσ yσ, A.pushConjFactorCoeff_spec B xτ yτ,
    pushConjFactorCoeff_spec', pushConjFactorCoeff_spec',
    pushConjFactor_coe, pushConjFactor_coe]
    simp only [_root_.mul_assoc, Units.inv_mul_cancel_left, map_mul]
  rw [eq2] at eq1; clear eq2
  have eq2 : yστ.1.1 =
    A.isoConjCoeff B *
      (A.iso B <| A.ι (A.pushConjFactorCoeff B xστ yστ) * xστ.1) *
    (A.isoConjCoeff B)⁻¹ := by
    rw [A.pushConjFactorCoeff_spec B xστ yστ, pushConjFactorCoeff_spec']
    simp only [_root_.mul_assoc, AlgEquiv.mul_apply, pushConjFactor_coe, map_mul,
      Units.inv_mul_cancel_left]
  rw [eq2] at eq1; clear eq2
  rw [A.isoConjCoeff_spec B] at eq1
  simp only [← _root_.mul_assoc] at eq1
  conv_rhs at eq1 =>
    rw [_root_.mul_assoc _ _ (A.isoConjCoeff B).1, Units.inv_mul, _root_.mul_one,
      _root_.mul_assoc _ _ (A.iso B _), ← map_mul]
  rw [Units.mul_left_inj, Units.mul_right_inj] at eq1
  replace eq1 := (A.iso B).injective eq1
  have eq2 : xσ.1.1 * A.ι (A.pushConjFactorCoeff B xτ yτ) * xτ.1.1 =
      A.ι (σ <| A.pushConjFactorCoeff B xτ yτ) * xσ.1.1 * xτ.1.1 := by
    have := xσ.2 (A.pushConjFactorCoeff B xτ yτ)
    rw [this]
    simp [_root_.mul_assoc]
  apply_fun (A.ι (A.pushConjFactorCoeff B xσ yσ) * ·) at eq2
  simp only [← _root_.mul_assoc] at eq2
  rw [eq2] at eq1; clear eq2
  simp only [_root_.mul_assoc] at eq1
  rw [A.conjFactorCompCoeff_spec xσ xτ xστ] at eq1
  simp only [← _root_.mul_assoc] at eq1
  rw [Units.mul_left_inj] at eq1
  apply_fun A.ι using RingHom.injective _
  simp only [map_mul, eq1]

/-- The multiplicative two-coboundary associated to a one-cochain. -/
def trivialFactorSet (c : Gal(K, F) → Kˣ) : Gal(K, F) × Gal(K, F) → Kˣ :=
  fun p ↦ c p.1 * Units.map p.1.toRingEquiv.toRingHom.toMonoidHom (c p.2) * (c (p.1 * p.2))⁻¹

lemma compare_toCocycles₂ (x_ : Π σ, A.conjFactor σ) (y_ : Π σ, B.conjFactor σ) :
    B.toCocycles₂ y_ (σ, τ) *
    A.pushConjFactorCoeffAsUnit B (x_ (σ * τ)) (y_ (σ * τ)) =
    A.pushConjFactorCoeffAsUnit B (x_ σ) (y_ σ) *
    Units.map σ (A.pushConjFactorCoeffAsUnit B (x_ τ) (y_ τ)) *
    A.toCocycles₂ x_ (σ, τ) := by
  delta toCocycles₂
  dsimp only
  have := A.compare_conjFactorCompCoeff B
    (x_ σ) (y_ σ)
    (x_ τ) (y_ τ)
    (x_ _) (y_ _)
  ext : 1
  dsimp
  change B.conjFactorCompCoeff (y_ σ) (y_ τ) (y_ (σ * τ)) *
      A.pushConjFactorCoeff B (x_ (σ * τ)) (y_ (σ * τ)) =
    A.pushConjFactorCoeff B (x_ σ) (y_ σ) *
      σ (A.pushConjFactorCoeff B (x_ τ) (y_ τ)) *
      A.conjFactorCompCoeff (x_ σ) (x_ τ) (x_ (σ * τ))
  exact this

lemma compare_toCocycles₂' (x_ : Π σ, A.conjFactor σ) (y_ : Π σ, B.conjFactor σ) :
    IsMulCoboundary₂ (B.toCocycles₂ y_ / A.toCocycles₂ x_) := by
  fconstructor
  · refine fun σ =>
      A.pushConjFactorCoeffAsUnit B (x_ σ) (y_ σ)
  intro σ τ
  dsimp only [AlgEquiv.smul_units_def, Pi.div_apply]
  symm
  rw [div_eq_iff_eq_mul, div_eq_mul_inv, mul_comm (Units.map _ _)]
  simp only [_root_.mul_assoc]
  symm
  rw [inv_mul_eq_iff_eq_mul, mul_comm _ (B.toCocycles₂ y_ _)]
  symm
  erw [compare_toCocycles₂]
  simp only [← _root_.mul_assoc]
  congr 1
  rw [mul_comm]

end GoodRep

/-- The additive form of a multiplicative-distribution representation. -/
@[simps!]
def _root_.Amelia.toAdditive (M G : Type 0) [Monoid M] [CommGroup G] [MulDistribMulAction M G] :
  Rep.ofMulDistribMulAction M G ≃+ Additive G := AddEquiv.refl _

variable (F K) in
/-- The Galois action of `Gal(K/F)` on `Kˣ` as a representation. -/
noncomputable def galAct : Rep ℤ Gal(K, F) := .ofMulDistribMulAction Gal(K, F) Kˣ

@[simp] lemma galAct_ρ_apply (σ : Gal(K, F)) (x : Kˣ) :
    (galAct F K).ρ σ (.ofMul x) = .ofMul (x.map σ) := rfl

variable [FiniteDimensional F K]

lemma mem_relativeBrGroup_iff_nonempty_goodRep {X : BrauerGroup F} :
    X ∈ RelativeBrGroup K F ↔ Nonempty (GoodRep K X) := by
  induction X using Quotient.inductionOn' with | h X =>
  simp only [RelativeBrGroup, MonoidHom.mem_ker, MonoidHom.coe_mk, OneHom.coe_mk,
    Quotient.map'_mk'']
  erw [← split_iff]
  rw [isSplit_iff_dimension]
  constructor
  · rintro ⟨A, eq, i, dim⟩
    exact ⟨⟨A, eq.symm, i, dim.symm⟩⟩
  · rintro ⟨⟨A, eq, i, dim⟩⟩
    exact ⟨A, eq.symm, i, dim.symm⟩

/-- Choose a good representative for an element of the relative Brauer group. -/
def RelativeBrGroup.goodRep (X : RelativeBrGroup K F) : GoodRep K X.1 :=
  mem_relativeBrGroup_iff_nonempty_goodRep.1 X.2 |>.some

open groupCohomology

namespace GoodRep

variable {X : BrauerGroup F} (A : GoodRep K X)

open groupCohomology in
/-- The cohomology class attached to a good representative and a system of conjugating units. -/
def toH2 (x_ : Π σ, A.conjFactor σ) : H2 (galAct F K) :=
  H2π (galAct F K) <| cocyclesOfIsMulCocycle₂ (A.isMulCocycle₂ x_)

end GoodRep

/-- Send a relative Brauer class to its degree-two Galois cohomology class. -/
def RelativeBrGroup.toSnd :  RelativeBrGroup K F → groupCohomology.H2 (galAct F K) :=
  fun X ↦ (goodRep X).toH2 (goodRep X).arbitraryConjFactor

lemma RelativeBrGroup.toSnd_wd (X : RelativeBrGroup K F)
    (A : GoodRep K X.1) (x_ : Π σ, A.conjFactor σ) :
    toSnd X = A.toH2 x_ := by
  simp only [toSnd, GoodRep.toH2]
  change H2π _ _ = H2π _ _
  rw [← sub_eq_zero, ← map_sub]
  rw [H2π_eq_zero_iff]
  set lhs := _; change lhs ∈ _
  have : IsMulCoboundary₂ (G := Gal(K, F)) (M := Kˣ) (lhs) := by
    apply GoodRep.compare_toCocycles₂'
  exact coboundariesOfIsMulCoboundary₂ this |>.2

namespace GoodRep

variable {X : BrauerGroup F} (A : GoodRep K X)

omit [FiniteDimensional F K] in
lemma conjFactor_linearIndependent (x_ : Π σ, A.conjFactor σ) :
    LinearIndependent K (v := fun (i : Gal(K, F)) => (x_ i).1.1) := by
  classical
  by_contra! rid
  obtain ⟨J, LI, maximal⟩ := exists_maximal_linearIndepOn K (fun (i : Gal(K, F)) => (x_ i).1.1)
  have ne : J ≠ Set.univ := by
    rintro rfl
    refine rid ?_
    let e : (Set.univ : Set Gal(K, F)) ≃ Gal(K, F) := Equiv.Set.univ Gal(K, F)
    have := linearIndependent_equiv e.symm |>.2 LI
    exact this
  rw [Set.ne_univ_iff_exists_notMem] at ne
  obtain ⟨σ, hσ⟩ := ne
  obtain ⟨c, c_ne_zero, hc⟩ := maximal σ hσ
  let B := Basis.span LI
  replace hc := Submodule.smul_mem _ c⁻¹ hc
  rw [← mul_smul, inv_mul_cancel₀ c_ne_zero, one_smul] at hc
  clear c c_ne_zero
  have mem1 : (x_ σ).1.1 ∈ Submodule.span K (Set.range fun (σ : J) ↦ (x_ σ.1).1.1) := by
    rw [← Set.image_eq_range (fun (i : Gal(K, F)) => (x_ i).1.1) J]; exact hc
  have eq0 : (⟨(x_ σ).1.1, mem1⟩ : Submodule.span K (Set.range fun (σ : J) ↦ (x_ σ.1).1.1)) =
      ∑ τ ∈ (B.repr ⟨_, mem1⟩).support, B.repr ⟨_, mem1⟩ τ • (x_ τ).1.1 := by
    conv_lhs => rw [← B.linearCombination_repr ⟨(x_ σ).1.1, mem1⟩, Finsupp.linearCombination_apply,
      Finsupp.sum]
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [SetLike.val_smul, smul_def]
    congr 1
    simp only [B, Basis.span_apply]
  simp only [smul_def] at eq0
  have eq1 (c : K) := calc A.ι (σ c) * (x_ σ).1.1
      _ = (x_ σ).1.1 * A.ι c := by
        rw [(x_ σ).2 c]; simp [_root_.mul_assoc]
      _ = ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
            A.ι (B.repr ⟨_, mem1⟩ τ) * (x_ τ).1.1 * A.ι c := by
        conv_lhs => rw [eq0, Finset.sum_mul]
      _ = ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
            A.ι (B.repr ⟨_, mem1⟩ τ) * A.ι (τ.1 c) * (x_ τ).1.1 :=
        Finset.sum_congr rfl fun i _ => by
        simp only [_root_.mul_assoc]
        congr 1
        rw [(x_ i).2 c]
        simp [_root_.mul_assoc, Units.inv_mul, _root_.mul_one]
      _ = ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
            A.ι (B.repr ⟨_, mem1⟩ τ * τ.1 c) * (x_ τ).1.1 :=
        Finset.sum_congr rfl fun i _ => by rw [map_mul]
  have eq2 (c : K) := calc A.ι (σ c) * (x_ σ).1.1
      _ = ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
          A.ι (σ c * (B.repr ⟨_, mem1⟩) τ) * (x_ τ).1.1 := by
        conv_lhs => rw [eq0, Finset.mul_sum]
        simp_rw [map_mul, _root_.mul_assoc]
  have eq3 (c : K) :
      ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
            A.ι (B.repr ⟨_, mem1⟩ τ * τ.1 c) * (x_ τ).1.1 =
      ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
          A.ι (σ c * (B.repr ⟨_, mem1⟩) τ) * (x_ τ).1.1 :=
    eq1 c |>.symm.trans <| eq2 c
  have eq4 (c : K) :
      ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
          A.ι (B.repr ⟨_, mem1⟩ τ * τ.1 c - σ c * (B.repr ⟨_, mem1⟩) τ) * (x_ τ).1.1 = 0 := by
    simp only [map_sub, map_mul, sub_mul, Finset.sum_sub_distrib]
    simp only [← map_mul, eq3, sub_self]
  have eq5 (c : K) :
      ∑ τ ∈ (B.repr ⟨_, mem1⟩).support,
          (B.repr ⟨_, mem1⟩ τ * τ.1 c - σ c * (B.repr ⟨_, mem1⟩) τ) • (x_ τ).1.1 = 0 := by
    rw [← eq4]
    rfl
  have eq6 (c : K) := linearIndependent_iff'' |>.1 LI (B.repr ⟨_, mem1⟩).support
    (fun τ => B.repr ⟨_, mem1⟩ τ * τ.1 c - σ c * (B.repr ⟨_, mem1⟩) τ)
    (by
      intro i hi
      simp only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not] at hi
      simp only [hi, zero_mul, mul_zero, sub_self]) (eq5 c)
  simp only [sub_eq_zero, Subtype.forall] at eq6
  have : (B.repr ⟨_, mem1⟩).support ≠ ∅ := by
    intro rid
    simp only [rid, Finset.sum_empty, Units.ne_zero] at eq0
  obtain ⟨τ, τ_mem⟩ := Finset.nonempty_of_ne_empty this
  have eq7 : σ = τ := by
    ext c
    specialize eq6 c τ τ.2
    rw [mul_comm] at eq6
    simp only [Subtype.coe_eta, mul_eq_mul_right_iff] at eq6
    refine eq6.recOn Eq.symm fun rid ↦ ?_
    simp only [Finsupp.mem_support_iff, ne_eq] at τ_mem
    contradiction
  subst eq7
  exact hσ τ.2

private lemma conjFactor_linearIndependent_boundary : True := by
  trivial

variable [IsGalois F K] in
/-- The basis of a good representative obtained from conjugating units. -/
def conjFactorBasis (x_ : Π σ, A.conjFactor σ) : Basis Gal(K, F) K A :=
  basisOfLinearIndependentOfCardEqFinrank
    (b := fun (i : Gal(K, F)) => (x_ i).1.1)
    (A.conjFactor_linearIndependent x_)
    (by rw [A.dim_eq', Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank])

end GoodRep

namespace RelativeBrGroup

open CrossProductAlgebra

variable [IsGalois F K] [DecidableEq Gal(K, F)] in
/-- Build a relative Brauer class from a two-cocycle via the cross-product algebra. -/
noncomputable def fromCocycles₂ (f : cocycles₂ (galAct F K)) : RelativeBrGroup K F :=
  haveI := groupCohomology.isMulCocycle₂_of_mem_cocycles₂ _ f.2
  haveI : Fact (IsMulCocycle₂ (M := Kˣ) (Additive.toMul ∘ f)) := ⟨this⟩
  ⟨Quotient.mk'' (asCSA (⇑Additive.toMul ∘ f.1)), mem_relativeBrGroup_iff_nonempty_goodRep.2 <|
    ⟨⟨asCSA (Additive.toMul ∘ f), rfl, incl (Additive.toMul ∘ f), dim_eq_sq⟩⟩⟩

open CategoryTheory in
variable [IsGalois F K] [DecidableEq Gal(K, F)] in
variable (F K) in
/-- Descend the cross-product construction to second cohomology. -/
noncomputable def fromSnd :
    (groupCohomology.shortComplexH2 (galAct F K)).moduleCatLeftHomologyData.H
    -- H2 (galAct F K)
    → RelativeBrGroup K F :=
  -- ShortComplex.descHomology _ (groupCohomology.isoCocycles₂ (galAct F K) ≫ )--_ _ _
  -- sorry
  Quotient.lift fromCocycles₂ <| by
    rintro ⟨(a : _ → Kˣ), ha⟩ ⟨(b : _ → Kˣ), hb⟩ (hab : Submodule.quotientRel _ _ _)
    have H' : H2π (galAct F K) ⟨a, ha⟩ - H2π (galAct F K) ⟨b, hb⟩ = 0 := by
      rw [← map_sub, H2π_eq_zero_iff]
      simp only [Submodule.quotientRel_def, LinearMap.mem_range] at hab
      obtain ⟨y, hy⟩ := hab
      use y
      exact congrArg Subtype.val hy
    rw [← map_sub, H2π_eq_zero_iff] at H'
    have ha : Fact <| IsMulCocycle₂ a := ⟨isMulCocycle₂_of_mem_cocycles₂ a ha⟩
    have hb : Fact <| IsMulCocycle₂ b := ⟨isMulCocycle₂_of_mem_cocycles₂ b hb⟩
    have hc : IsMulCoboundary₂ (G := Gal(K, F)) (M := Kˣ) (a / b) :=
      isMulCoboundary₂_of_mem_coboundaries₂ _ H'
    obtain ⟨c, hc⟩ := hc
    simp only [fromCocycles₂, Subtype.mk.injEq, Quotient.eq'']
    let A := asCSA a
    let B := asCSA b
    change IsBrauerEquivalent A B
    letI : Module K A := inferInstanceAs <| Module K (CrossProductAlgebra a)
    letI : Module K B := inferInstanceAs <| Module K (CrossProductAlgebra b)
    let basis : Basis Gal(K, F) K B := (basis (f := b)).unitsSMul c
    let φ0 : A ≃ₗ[K] B := CrossProductAlgebra.basis.equiv basis (.refl _)
    haveI : LinearMap.CompatibleSMul A B F K := by
      constructor
      have eq (c : F) (a : A) : c • a = algebraMap F K c • a := by
        apply val_injective
        change c • a.val = (algebraMap F K c) • a.val
        induction a.val using Finsupp.induction_linear with
        | zero => simp
        | add f g _ _ => simp_all
        | single σ k => simp
      have eq' (c : F) (a : B) : c • a = algebraMap F K c • a := by
        apply val_injective
        change c • a.val = (algebraMap F K c) • a.val
        induction a.val using Finsupp.induction_linear with
        | zero => simp
        | add f g _ _ => simp_all
        | single σ k => simp
      intro l c a
      rw [eq, eq', map_smul]
    let φ1 : A ≃ₗ[F] B := φ0.restrictScalars F
    let φ2 : A ≃ₐ[F] B := AlgEquiv.ofLinearEquiv φ1
      (by
        change φ0 1 = 1
        rw [show (1 : A) = (a (1, 1))⁻¹.1 • (CrossProductAlgebra.basis 1 : A) by
          apply val_injective
          change (1 : CrossProductAlgebra a).val =
            ((a (1, 1))⁻¹.1 • (CrossProductAlgebra.basis 1 : CrossProductAlgebra a)).val
          simp [CrossProductAlgebra.basis, CrossProductAlgebra.val_one,
            CrossProductAlgebra.val_smul]]
        refine (φ0.map_smul ((↑(a (1, 1))⁻¹) : K)
          (CrossProductAlgebra.basis 1 : A)).trans ?_
        rw [show φ0 (CrossProductAlgebra.basis 1 : A) =
            basis ((Equiv.refl Gal(K, F)) 1) by
          exact Basis.equiv_apply (b := (CrossProductAlgebra.basis : Basis Gal(K, F) K A))
            (b' := basis) (e := Equiv.refl Gal(K, F)) 1]
        apply val_injective
        change ((↑((a (1, 1))⁻¹) : K) •
            (basis ((Equiv.refl Gal(K, F)) 1) : CrossProductAlgebra b)).val =
          (1 : CrossProductAlgebra b).val
        simp only [Equiv.refl_apply, Units.val_inv_eq_inv_val, basis, B,
          CrossProductAlgebra.val_one]
        change ((↑(a (1, 1)))⁻¹ : K) •
            ((CrossProductAlgebra.basis.unitsSMul c) 1).val =
          Finsupp.single 1 (↑(b (1, 1)))⁻¹
        conv_lhs => enter [2, 1]; erw [Basis.unitsSMul_apply]
        erw [CrossProductAlgebra.val_smul]
        simp only [CrossProductAlgebra.basis, Basis.coe_ofRepr, valLinearEquiv_symm_apply,
          AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
          valAddEquiv_symm_apply_val, Finsupp.smul_single, smul_eq_mul, _root_.mul_one]
        congr 1
        specialize hc 1 1
        simp only [one_smul, _root_.mul_one, div_self', _root_.one_mul, Pi.div_apply,
          div_eq_mul_inv] at hc
        simp [hc])
      (by
        intro α β
        change φ0 ((⟨α.val⟩ : CrossProductAlgebra a) * (⟨β.val⟩ : CrossProductAlgebra a)) =
          φ0 (⟨α.val⟩ : CrossProductAlgebra a) * φ0 (⟨β.val⟩ : CrossProductAlgebra a)
        induction α.val using Finsupp.induction_linear with
        | zero => change φ0 (0 * _) = φ0 0 * _; simp
        | add f g hf hg =>
          change φ0 ((_ + _) * _) = φ0 (_ + _) * φ0 _
          rw [add_mul]
          simpa [map_add, add_mul] using
            congrArg (fun z => z) (by exact congrArg₂ HAdd.hAdd hf hg)
        | single σ k1 =>
          induction β.val using Finsupp.induction_linear with
          | zero => change φ0 (_ * 0) = _ * φ0 0; simp
          | add f g hf hg =>
            change φ0 (_ * (_ + _)) = φ0 _ * φ0 (_ + _)
            rw [mul_add]
            simpa [map_add, mul_add] using
              congrArg (fun z => z) (by exact congrArg₂ HAdd.hAdd hf hg)
          | single τ k2 =>
            change φ0 (⟨mulLinearMap a _ _⟩ : CrossProductAlgebra a) = _
            simp only [mulLinearMap_single_single, *]
            rw [← mul_one (k1 * σ k2 * ↑(a (σ, τ))), ← smul_eq_mul _ 1, ← Finsupp.smul_single,
              show (⟨_ • .single _ 1⟩ : CrossProductAlgebra a) =
                (k1 * σ k2 * ↑(a (σ, τ))) • (CrossProductAlgebra.basis (σ * τ)) by
                apply val_injective; simp [CrossProductAlgebra.basis],
              show (⟨.single σ k1⟩ : CrossProductAlgebra a) = k1 • (CrossProductAlgebra.basis σ) by
                apply val_injective; simp [CrossProductAlgebra.basis],
              show (⟨.single τ k2⟩ : CrossProductAlgebra a) = k2 • (CrossProductAlgebra.basis τ) by
                apply val_injective; simp [CrossProductAlgebra.basis]]
            refine (φ0.map_smul ((k1 * σ k2 * ↑(a (σ, τ))) : K)
              (CrossProductAlgebra.basis (σ * τ) : A)).trans ?_
            refine Eq.trans ?_ (congrArg₂ HMul.hMul
              (φ0.map_smul ((k1 : K)) (CrossProductAlgebra.basis σ : A)).symm
              (φ0.map_smul ((k2 : K)) (CrossProductAlgebra.basis τ : A)).symm)
            rw [show φ0 (CrossProductAlgebra.basis (σ * τ) : A) =
                basis ((Equiv.refl Gal(K, F)) (σ * τ)) by
              exact Basis.equiv_apply (b := (CrossProductAlgebra.basis : Basis Gal(K, F) K A))
                (b' := basis) (e := Equiv.refl Gal(K, F)) (σ * τ),
              show φ0 (CrossProductAlgebra.basis σ : A) =
                basis ((Equiv.refl Gal(K, F)) σ) by
              exact Basis.equiv_apply (b := (CrossProductAlgebra.basis : Basis Gal(K, F) K A))
                (b' := basis) (e := Equiv.refl Gal(K, F)) σ,
              show φ0 (CrossProductAlgebra.basis τ : A) =
                basis ((Equiv.refl Gal(K, F)) τ) by
              exact Basis.equiv_apply (b := (CrossProductAlgebra.basis : Basis Gal(K, F) K A))
                (b' := basis) (e := Equiv.refl Gal(K, F)) τ]
            simp only [Equiv.refl_apply]
            apply val_injective
            change (((k1 * σ k2 * ↑(a (σ, τ))) : K) •
                (basis (σ * τ) : CrossProductAlgebra b)).val =
              (((k1 : K) • (basis σ : CrossProductAlgebra b)) *
                ((k2 : K) • (basis τ : CrossProductAlgebra b))).val
            change ((k1 * σ k2 * ↑(a (σ, τ))) : K) • (basis (σ * τ)).val =
              CrossProductAlgebra.mulLinearMap b ((k1 : K) • (basis σ).val)
                ((k2 : K) • (basis τ).val)
            unfold basis
            erw [Basis.unitsSMul_apply, Basis.unitsSMul_apply, Basis.unitsSMul_apply]
            erw [CrossProductAlgebra.val_smul, CrossProductAlgebra.val_smul,
              CrossProductAlgebra.val_smul]
            simp only [CrossProductAlgebra.basis, Basis.coe_ofRepr, valLinearEquiv_symm_apply,
              AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm,
              valAddEquiv_symm_apply_val, Finsupp.smul_single, smul_eq_mul, _root_.mul_one,
              mulLinearMap_single_single, map_mul]
            congr 1
            specialize hc σ τ
            simp only [AlgEquiv.smul_units_def, Pi.div_apply, Units.ext_iff, Units.val_mul,
              Units.val_div_eq_div_val, Units.coe_map, MonoidHom.coe_coe] at hc
            simp only [_root_.mul_assoc]
            congr 1
            rw [mul_comm (c σ).1, _root_.mul_assoc]
            congr 1
            field_simp at hc
            field_simp [hc, mul_comm]
            convert hc.symm using 1 <;> ring)
    apply IsBrauerEquivalent.iso_to_eqv (h := φ2)

variable [IsGalois F K]
lemma fromSnd_wd (a : cocycles₂ (galAct F K)) :
    haveI : Fact (IsMulCocycle₂ (M := Kˣ) (Additive.toMul ∘ a)) :=
      ⟨isMulCocycle₂_of_mem_cocycles₂ _ a.2⟩
    (fromSnd F K <| Quotient.mk'' a) =
    ⟨Quotient.mk'' (CrossProductAlgebra.asCSA (Additive.toMul ∘ a)),
      mem_relativeBrGroup_iff_nonempty_goodRep.2
        ⟨_, rfl, CrossProductAlgebra.incl _, CrossProductAlgebra.dim_eq_sq⟩⟩ := rfl

/-- Convert a multiplicative two-coboundary witness into an additive cohomology coboundary. -/
def _root_.Amfix.coboundariesOfIsMulCoboundary₂ {G M : Type} [Group G] [CommGroup M]
    [MulDistribMulAction G M] {f : G × G → M} (hf : IsMulCoboundary₂ f) :
    coboundaries₂ (Rep.ofMulDistribMulAction G M) :=
  ⟨Additive.ofMul ∘ f, hf.choose, funext fun g ↦ hf.choose_spec g.1 g.2⟩

open GoodRep groupCohomology in
lemma toSnd_fromSnd : toSnd ∘ fromSnd F K ∘ (H2Iso (galAct F K)).hom = id := by
  ext a
  induction a using H2_induction_on with | h a =>
  -- rcases a with ⟨(a : _ → Kˣ), ha'⟩
  let am : Gal(K, F) × Gal(K, F) → Kˣ :=
    fun p => Additive.toMul (Amelia.toAdditive Gal(K, F) Kˣ (a p))
  have hmem : (fun p : Gal(K, F) × Gal(K, F) =>
      Amelia.toAdditive Gal(K, F) Kˣ (a p)) ∈
      cocycles₂ (Rep.ofMulDistribMulAction Gal(K, F) Kˣ) := by
    change (a : Gal(K, F) × Gal(K, F) → galAct F K) ∈ cocycles₂ (galAct F K)
    exact a.2
  have ha : IsMulCocycle₂ am :=
    isMulCocycle₂_of_mem_cocycles₂ _ hmem
  haveI : Fact (IsMulCocycle₂ am) := ⟨ha⟩
  simp only [Function.comp_apply, id_eq]
  let A : GoodRep K (Quotient.mk'' <| CrossProductAlgebra.asCSA am) :=
    ⟨CrossProductAlgebra.asCSA am, rfl, CrossProductAlgebra.incl am, CrossProductAlgebra.dim_eq_sq⟩
  let y_ σ : A.conjFactor σ :=
    ⟨CrossProductAlgebra.of am σ,
    fun c ↦ by erw [CrossProductAlgebra.of_conj]; rfl⟩
  simp only [H2π, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    π_comp_H2Iso_hom_apply,
    CategoryTheory.Iso.inv_hom_id_apply]
  change toSnd (fromSnd F K (Quotient.mk'' a)) =
    (ModuleCat.Hom.hom (π (galAct F K) 2)) ((ModuleCat.Hom.hom (isoCocycles₂ (galAct F K)).inv) a)
  rw [fromSnd_wd]
  rw [toSnd_wd _ _ y_]
  -- rw [toSnd_wd (fromSnd F K _)]
  let b : Gal(K, F) × Gal(K, F) → Kˣ := A.toCocycles₂ y_
  -- rw [show A.toH2 y_ = Quotient.mk'' ⟨b, _⟩ by rfl]
  -- rw [Quotient.eq'']
  -- change (twoCoboundaries (galAct F K)).quotientRel.r _ _
  change H2π _ _ = H2π _ _
  rw [← sub_eq_zero, ← map_sub, H2π_eq_zero_iff]
  -- rw [Submodule.quotientRel_def]
  suffices H : IsMulCoboundary₂ _ from
    (Amfix.coboundariesOfIsMulCoboundary₂ H).2
  refine ⟨fun _ => 1, ?_⟩
  intro σ τ
  simp only [smul_one, div_self', _root_.mul_one, cocyclesOfIsMulCocycle₂_coe, Function.comp_apply,
    cocycles₂.val_eq_coe]
  -- change _ = (Additive.toMul _) / (am (σ, τ))
  erw [Equiv.symm_apply_apply]
  simp only [toCocycles₂, conjFactorCompCoeffAsUnit]
  -- change _ = _ / _
  ext : 1
  simp only [Units.val_one, Units.val_div_eq_div_val]
  field_simp
  change (am (σ, τ)).1 = _
  -- simp [conjFactorCompCoeff, conjFactorTwistCoeff]
  -- simp only [AlgEquiv.mul_apply, y_]
  change _ = A.conjFactorCompCoeff (y_ σ) (y_ τ) (y_ (σ * τ))
  apply_fun A.ι using RingHom.injective _
  rw [conjFactorCompCoeff_spec'']
  simp only [A, y_]
  calc
    (CrossProductAlgebra.incl am) ↑(am (σ, τ)) =
        (CrossProductAlgebra.incl am) ↑(am (σ, τ)) * (1 : CrossProductAlgebra am) := by
      simp
    _ = (CrossProductAlgebra.incl am) ↑(am (σ, τ)) *
        ((CrossProductAlgebra.of am (σ * τ)).val * ↑(CrossProductAlgebra.of am (σ * τ))⁻¹) := by
      rw [Units.mul_inv]
    _ = _ := by
      rw [← _root_.mul_assoc, ← CrossProductAlgebra.of_mul_of]
      rfl

lemma fromSnd_toSnd : (fromSnd F K ∘ (H2Iso (galAct F K)).hom) ∘ toSnd = id := by
  ext X
  obtain ⟨A⟩ := mem_relativeBrGroup_iff_nonempty_goodRep.1 X.2
  simp only [Function.comp_apply, id_eq, SetLike.coe_eq_coe]
  rw [toSnd_wd (A := A) (x_ := A.arbitraryConjFactor)]
  ext : 1
  conv_rhs => rw [← A.quot_eq]
  simp only [GoodRep.toH2, H2π, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    π_comp_H2Iso_hom_apply,
    CategoryTheory.Iso.inv_hom_id_apply]
  change (fromSnd F K
    (Quotient.mk'' (cocyclesOfIsMulCocycle₂ (GoodRep.isMulCocycle₂
      A.arbitraryConjFactor)))).1 = Quotient.mk'' A.toCSA
  rw [fromSnd_wd]
  rw [Quotient.eq'']
  apply IsBrauerEquivalent.iso_to_eqv
  set f : Gal(K, F) × Gal(K, F) → Kˣ :=
    Additive.toMul ∘ cocyclesOfIsMulCocycle₂ (GoodRep.isMulCocycle₂
      A.arbitraryConjFactor)
  haveI : Fact (IsMulCocycle₂ f) := by
    subst f
    exact ⟨isMulCocycle₂_of_mem_cocycles₂ _ (cocyclesOfIsMulCocycle₂
      (GoodRep.isMulCocycle₂ A.arbitraryConjFactor)).2⟩
  change CrossProductAlgebra f ≃ₐ[F] A
  letI : Module K (CrossProductAlgebra f) := inferInstance
  let φ0 : CrossProductAlgebra f ≃ₗ[K] A :=
    CrossProductAlgebra.basis.equiv (A.conjFactorBasis A.arbitraryConjFactor) (.refl _)
  haveI : LinearMap.CompatibleSMul (CrossProductAlgebra f) A F K := by
    constructor
    have eq (c : F) (a : A) : c • a = algebraMap F K c • a := by
      simp only [algebraMap_smul]
    have eq' (c : F) (a : CrossProductAlgebra f) : c • a = algebraMap F K c • a := by
      apply CrossProductAlgebra.val_injective
      change c • a.val = (algebraMap F K c) • a.val
      induction a.val using Finsupp.induction_linear with
      | zero => simp
      | add f g _ _ => simp_all
      | single σ k => simp
    intro l c a
    rw [eq, eq', map_smul]
  let φ1 : CrossProductAlgebra f ≃ₗ[F] A := φ0.restrictScalars F
  refine AlgEquiv.ofLinearEquiv φ1 ?_ ?_
  · change φ0 1 = 1
    conv_lhs =>
      enter [2]
      rw [show (1 : CrossProductAlgebra f) =
        ((A.toCocycles₂ A.arbitraryConjFactor) (1, 1))⁻¹.1 • (CrossProductAlgebra.basis 1) by
        apply CrossProductAlgebra.val_injective
        change (1 : CrossProductAlgebra f).val =
          (((A.toCocycles₂ A.arbitraryConjFactor) (1, 1))⁻¹.1 •
            (CrossProductAlgebra.basis 1 : CrossProductAlgebra f)).val
        simp [f, CrossProductAlgebra.basis, CrossProductAlgebra.val_one,
          CrossProductAlgebra.val_smul, GoodRep.toCocycles₂]
        congr 1]
    refine (φ0.map_smul ((↑(A.toCocycles₂ A.arbitraryConjFactor (1, 1))⁻¹) : K)
      (CrossProductAlgebra.basis 1 : CrossProductAlgebra f)).trans ?_
    simp only [φ0]
    erw [Basis.equiv_apply]
    simp only [Units.val_inv_eq_inv_val, GoodRep.conjFactorBasis,
      Equiv.refl_apply, coe_basisOfLinearIndependentOfCardEqFinrank,  AlgEquiv.one_apply,
      GoodRep.smul_def]
    change A.ι (A.toCocycles₂ _ (1, 1))⁻¹ * _ = 1
    simp only [GoodRep.toCocycles₂, GoodRep.conjFactorCompCoeffAsUnit, AlgEquiv.one_apply]
    have := A.conjFactorCompCoeff_spec' (A.arbitraryConjFactor 1)
      (A.arbitraryConjFactor 1)
      (A.arbitraryConjFactor (1 * 1))
    simp only [AlgEquiv.one_apply, AlgEquiv.mul_apply] at this
    rw [GoodRep.conjFactorCompCoeff_inv]
    erw [_root_.one_mul]
    simp only [AlgEquiv.one_apply, ← _root_.mul_assoc, Units.mul_inv, _root_.one_mul, Units.inv_mul]
  · intro x y
    change φ0 (⟨x.val⟩ * ⟨y.val⟩) = φ0 ⟨x.val⟩ * φ0 ⟨y.val⟩
    induction x.val using Finsupp.induction_linear with
    | zero => change φ0 (0 * _) = φ0 0 * _; simp
    | add f g hf hg =>
      change φ0 ((_ + _) * _) = φ0 (_ + _) * φ0 _
      rw [add_mul, map_add]
      change φ0 ({ val := f } * { val := y.val }) +
          φ0 ({ val := g } * { val := y.val }) =
        φ0 ({ val := f } + { val := g }) * φ0 { val := y.val }
      rw [hf, hg, map_add, add_mul]
    | single σ a =>
      induction y.val using Finsupp.induction_linear with
      | zero => change φ0 (_ * 0) = _ * φ0 0; simp
      | add f g hf hg =>
        change φ0 (_ * (_ + _)) = φ0 _ * φ0 (_ + _)
        rw [mul_add, map_add]
        change φ0 ({ val := Finsupp.single σ a } * { val := f }) +
            φ0 ({ val := Finsupp.single σ a } * { val := g }) =
          φ0 { val := Finsupp.single σ a } * φ0 ({ val := f } + { val := g })
        rw [hf, hg, map_add, mul_add]
      | single τ b =>
        change φ0 (⟨CrossProductAlgebra.mulLinearMap f _ _⟩ : CrossProductAlgebra f) = _
        simp only [CrossProductAlgebra.mulLinearMap_single_single, *]
        rw [← mul_one (a * σ b * _), ← smul_eq_mul _ 1, ← Finsupp.smul_single,
          show (⟨_ • .single _ 1⟩ : CrossProductAlgebra f) =
            (a * σ b * (f (σ, τ)).1) • (CrossProductAlgebra.basis (σ * τ)) by
            apply CrossProductAlgebra.val_injective; simp [CrossProductAlgebra.basis],
          show (⟨.single σ a⟩ : CrossProductAlgebra f) = a • (CrossProductAlgebra.basis σ) by
            apply CrossProductAlgebra.val_injective; simp [CrossProductAlgebra.basis],
          show (⟨.single τ b⟩ : CrossProductAlgebra f) = b • (CrossProductAlgebra.basis τ) by
            apply CrossProductAlgebra.val_injective; simp [CrossProductAlgebra.basis]]
        refine (φ0.map_smul ((a * σ b * ↑(f (σ, τ))) : K)
          (CrossProductAlgebra.basis (σ * τ) : CrossProductAlgebra f)).trans ?_
        refine Eq.trans ?_ (congrArg₂ HMul.hMul
          (φ0.map_smul ((a : K)) (CrossProductAlgebra.basis σ : CrossProductAlgebra f)).symm
          (φ0.map_smul ((b : K)) (CrossProductAlgebra.basis τ : CrossProductAlgebra f)).symm)
        erw [Basis.equiv_apply, Basis.equiv_apply, Basis.equiv_apply]
        simp only [Equiv.refl_apply]
        simp only [f, Function.comp_apply, GoodRep.conjFactorBasis,
          coe_basisOfLinearIndependentOfCardEqFinrank, AlgEquiv.mul_apply, GoodRep.smul_def,
          map_mul]
        change _ * _ * A.ι (A.toCocycles₂ _ (σ, τ)) * _ = _
        simp only [GoodRep.toCocycles₂, GoodRep.conjFactorCompCoeffAsUnit, _root_.mul_assoc]
        erw [A.conjFactorCompCoeff_spec'']
        simp only [_root_.mul_assoc]
        simp only [AlgEquiv.mul_apply, Units.inv_mul, _root_.mul_one, ← _root_.mul_assoc]
        congr 1
        simp only [_root_.mul_assoc]
        congr 1
        rw [(A.arbitraryConjFactor _).2 b]
        simp [-GoodRep.conjFactor_prop]

/-- The equivalence between the relative Brauer group and second Galois cohomology. -/
@[simp]
def equivSnd : RelativeBrGroup K F ≃ H2 (galAct F K) where
  toFun := toSnd
  invFun := (fromSnd F K ∘ (H2Iso (galAct F K)).hom)
  left_inv := congr_fun fromSnd_toSnd
  right_inv := congr_fun toSnd_fromSnd

end RelativeBrGroup
