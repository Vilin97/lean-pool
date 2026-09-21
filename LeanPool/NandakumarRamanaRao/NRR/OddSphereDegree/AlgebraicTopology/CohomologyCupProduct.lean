/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.CochainCupLeibniz
import Mathlib.Algebra.Homology.ConcreteCategory

/-!
# Cohomology-level singular cup product over `ZMod 2`

This file descends the genuine cochain-level Alexander–Whitney cup product
(`cochainCup`, `CupProduct.lean`) to a **cohomology-level** cup product on the
singular cohomology with `ZMod 2` coefficients constructed in
`SingularCohomology.lean`:

```text
cupZMod2 : H^p(X; F₂) → H^q(X; F₂) → H^{p+q}(X; F₂).
```

The descent uses the cochain Leibniz / coboundary identity of
`CochainCupLeibniz.lean` (cup of cocycles is a cocycle; cup with a coboundary is a
coboundary). The well-definedness on cohomology classes is `cupZMod2_mk`: the cup
of the classes of two cocycles is the class of their cochain cup.

## Construction outline

* `cohomologyZMod2 X n` is `H^n(X; F₂)`, definitionally
 `(singularCohomologyZMod2 n).obj (op X)`.
* `cocycleClass` sends a cocycle to its cohomology class
 (`homologyπ ∘ cyclesMk`); it is additive, scalar-linear, surjective, and
 annihilates coboundaries.
* For a fixed *cocycle* `ψ` (resp. `φ`) the cup `· ⌣ ψ` (resp. `φ ⌣ ·`) is a
 cochain map of cocycles; it descends to a `ModuleCat` morphism on homology by
 the cokernel universal property (`cupHomologyLeft` / `cupHomologyRight`).
* `cupZMod2 a b` cups `a` against a chosen cocycle representative of `b` via
 `cupHomologyLeft`. `cupZMod2_mk` shows this is representative-independent,
 giving the class of the cochain cup.

The module exports the cohomology-level product and its functoriality laws.
-/

open CategoryTheory Limits AlgebraicTopology SphereOddDegree.AlexanderWhitney

namespace SphereOddDegree

noncomputable section

/-- The singular `F₂`-cochain complex of `X`. -/
abbrev cochainCxZMod2 (X : TopCat.{0}) : CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ :=
  singularCochainComplexZMod2.obj (Opposite.op X)

/-- The `n`-th singular cohomology `H^n(X; F₂)`, definitionally
`(singularCohomologyZMod2 n).obj (op X)`. -/
abbrev cohomologyZMod2 (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} (ZMod 2) :=
  (cochainCxZMod2 X).homology n

/-- `cohomologyZMod2` is the constructed singular cohomology object. -/
theorem cohomologyZMod2_eq (X : TopCat.{0}) (n : ℕ) :
    cohomologyZMod2 X n = (singularCohomologyZMod2 n).obj (Opposite.op X) := rfl

theorem cochainCx_next (n : ℕ) : (ComplexShape.up ℕ).next n = n + 1 :=
  (ComplexShape.up ℕ).next_eq' rfl

/-! ## 1. Cohomology class of a cocycle -/

/-- The cohomology class of a cocycle `φ` (a `p`-cochain with `δφ = 0`):
`homologyπ` applied to the cycle `cyclesMk φ`. -/
def cocycleClass (X : TopCat.{0}) (n : ℕ) (φ : singularCochainGroup (ZMod 2) X n)
    (hφ : cochainCoboundary (ZMod 2) X n φ = 0) : cohomologyZMod2 X n :=
  ((cochainCxZMod2 X).homologyπ n).hom
    ((cochainCxZMod2 X).cyclesMk φ (n + 1) (cochainCx_next n) hφ)

/-- The class only depends on the cochain, not on the cocycle proof. -/
theorem cocycleClass_congr (X : TopCat.{0}) (n : ℕ) {φ φ' : singularCochainGroup (ZMod 2) X n}
    (h : φ = φ') (hφ : cochainCoboundary (ZMod 2) X n φ = 0)
    (hφ' : cochainCoboundary (ZMod 2) X n φ' = 0) :
    cocycleClass X n φ hφ = cocycleClass X n φ' hφ' := by
  subst h; rfl

/-- The `iCycles` of a cycle is a cocycle. -/
theorem cochainCoboundary_iCycles (X : TopCat.{0}) (n : ℕ) (c : (cochainCxZMod2 X).cycles n) :
    cochainCoboundary (ZMod 2) X n (((cochainCxZMod2 X).iCycles n).hom c) = 0 := by
  have h := (cochainCxZMod2 X).iCycles_d n (n + 1)
  change ((cochainCxZMod2 X).iCycles n ≫ (cochainCxZMod2 X).d n (n + 1)).hom c = 0
  rw [h]; rfl

/-- `cyclesMk (iCycles c) = c`. -/
theorem cyclesMk_iCycles (X : TopCat.{0}) (n : ℕ) (c : (cochainCxZMod2 X).cycles n) :
    (cochainCxZMod2 X).cyclesMk (((cochainCxZMod2 X).iCycles n).hom c) (n + 1)
        (cochainCx_next n) (cochainCoboundary_iCycles X n c) = c := by
  apply (ModuleCat.mono_iff_injective ((cochainCxZMod2 X).iCycles n)).1 inferInstance
  exact (cochainCxZMod2 X).i_cyclesMk _ _ _ _

/-- Every cohomology class is the class of a cocycle. -/
theorem cocycleClass_surjective (X : TopCat.{0}) (n : ℕ) (a : cohomologyZMod2 X n) :
    ∃ (φ : singularCochainGroup (ZMod 2) X n) (hφ : cochainCoboundary (ZMod 2) X n φ = 0),
      cocycleClass X n φ hφ = a := by
  have hepi : Function.Surjective ((cochainCxZMod2 X).homologyπ n).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨c, hc⟩ := hepi a
  refine ⟨((cochainCxZMod2 X).iCycles n).hom c, cochainCoboundary_iCycles X n c, ?_⟩
  dsimp [cocycleClass]
  have h_cyc := cyclesMk_iCycles X n c
  exact congrArg (fun x => ((cochainCxZMod2 X).homologyπ n).hom x) h_cyc |>.trans hc

/-- The zero cochain has zero class. -/
theorem cocycleClass_zero (X : TopCat.{0}) (n : ℕ)
    (h0 : cochainCoboundary (ZMod 2) X n (0 : singularCochainGroup (ZMod 2) X n) = 0) :
    cocycleClass X n 0 h0 = 0 := by
  dsimp [cocycleClass]
  have h : (cochainCxZMod2 X).cyclesMk (0 : singularCochainGroup (ZMod 2) X n) (n + 1)
      (cochainCx_next n) h0 = 0 := by
    apply (ModuleCat.mono_iff_injective ((cochainCxZMod2 X).iCycles n)).1 inferInstance
    have h_mk := (cochainCxZMod2 X).i_cyclesMk (0 : singularCochainGroup (ZMod 2) X n) (n + 1) (cochainCx_next n) h0
    rw [map_zero]
    exact h_mk
  rw [h, map_zero]

/-- `δ ∘ δ = 0`. -/
theorem cochainCoboundary_cochainCoboundary (X : TopCat.{0}) (m : ℕ)
    (η : singularCochainGroup (ZMod 2) X m) :
    cochainCoboundary (ZMod 2) X (m + 1) (cochainCoboundary (ZMod 2) X m η) = 0 := by
  change ((cochainCxZMod2 X).d m (m + 1) ≫ (cochainCxZMod2 X).d (m + 1) (m + 2)).hom η = 0
  rw [(cochainCxZMod2 X).d_comp_d]; rfl

/-
A coboundary has zero cohomology class.
-/
theorem cocycleClass_coboundary_zero (X : TopCat.{0}) (m : ℕ)
    (η : singularCochainGroup (ZMod 2) X m)
    (hcoc : cochainCoboundary (ZMod 2) X (m + 1) (cochainCoboundary (ZMod 2) X m η) = 0) :
    cocycleClass X (m + 1) (cochainCoboundary (ZMod 2) X m η) hcoc = 0 := by
  have h : (cochainCxZMod2 X).cyclesMk (cochainCoboundary (ZMod 2) X m η) (m + 2) (cochainCx_next (m + 1)) hcoc = (cochainCxZMod2 X).toCycles m (m + 1) η := by
    apply (ModuleCat.mono_iff_injective ((cochainCxZMod2 X).iCycles (m + 1))).1 inferInstance
    have h_mk := (cochainCxZMod2 X).i_cyclesMk (cochainCoboundary (ZMod 2) X m η) (m + 2) (cochainCx_next (m + 1)) hcoc
    have hto := HomologicalComplex.toCycles_i (cochainCxZMod2 X) m (m + 1)
    have hto_app := congrArg (fun (f : (cochainCxZMod2 X).X m ⟶ (cochainCxZMod2 X).X (m + 1)) => f.hom η) hto
    dsimp at hto_app
    exact h_mk.trans hto_app.symm
  dsimp [cocycleClass]
  rw [h]
  have hcomp := HomologicalComplex.toCycles_comp_homologyπ (cochainCxZMod2 X) m (m + 1)
  have hcomp_app := congrArg (fun (f : (cochainCxZMod2 X).X m ⟶ (cochainCxZMod2 X).homology (m + 1)) => f.hom η) hcomp
  dsimp at hcomp_app
  exact hcomp_app

/-
Compatibility of `cocycleClass` with the degree cast.
-/
theorem cocycleClass_cast (X : TopCat.{0}) {m m' : ℕ} (h : m = m')
    (φ : singularCochainGroup (ZMod 2) X m) (hφ : cochainCoboundary (ZMod 2) X m φ = 0)
    (hφ' : cochainCoboundary (ZMod 2) X m' (cochainCast h φ) = 0) :
    cocycleClass X m' (cochainCast h φ) hφ' =
      (eqToHom (by rw [h]) : cohomologyZMod2 X m ⟶ cohomologyZMod2 X m').hom
        (cocycleClass X m φ hφ) := by
  subst h
  rfl

/-- A degree-cast coboundary has zero cohomology class. -/
theorem cocycleClass_cast_coboundary_zero (X : TopCat.{0}) (m m' : ℕ) (h : m + 1 = m')
    (η : singularCochainGroup (ZMod 2) X m)
    (hcoc : cochainCoboundary (ZMod 2) X m' (cochainCast h (cochainCoboundary (ZMod 2) X m η)) = 0) :
    cocycleClass X m' (cochainCast h (cochainCoboundary (ZMod 2) X m η)) hcoc = 0 := by
  rw [cocycleClass_cast X h (cochainCoboundary (ZMod 2) X m η)
        (cochainCoboundary_cochainCoboundary X m η) hcoc,
    cocycleClass_coboundary_zero]
  simp

/-! ## 2. Cup with a fixed cocycle on the left -/

/-- The cochain map `φ ↦ φ ⌣ ψ` as a `ModuleCat` morphism `C^p ⟶ C^{p+q}`. -/
def cupRightMor (X : TopCat.{0}) (p q : ℕ) (ψ : singularCochainGroup (ZMod 2) X q) :
    (cochainCxZMod2 X).X p ⟶ (cochainCxZMod2 X).X (p + q) :=
  ModuleCat.ofHom
    { toFun := fun φ => cochainCup p q φ ψ
      map_add' := fun φ φ' => cochainCup_add_left p q φ φ' ψ
      map_smul' := fun s φ => cochainCup_smul_left p q s φ ψ }

@[simp] theorem cupRightMor_hom (X : TopCat.{0}) (p q : ℕ)
    (ψ : singularCochainGroup (ZMod 2) X q) (φ : (cochainCxZMod2 X).X p) :
    (cupRightMor X p q ψ).hom φ = cochainCup p q φ ψ := rfl

/-- The cochain map `ψ ↦ φ ⌣ ψ` as a `ModuleCat` morphism `C^q ⟶ C^{p+q}`. -/
def cupLeftFixedMor (X : TopCat.{0}) (p q : ℕ) (φ : singularCochainGroup (ZMod 2) X p) :
    (cochainCxZMod2 X).X q ⟶ (cochainCxZMod2 X).X (p + q) :=
  ModuleCat.ofHom
    { toFun := fun ψ => cochainCup p q φ ψ
      map_add' := fun ψ ψ' => cochainCup_add_right p q φ ψ ψ'
      map_smul' := fun s ψ => cochainCup_smul_right p q s φ ψ }

@[simp] theorem cupLeftFixedMor_hom (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p) (ψ : (cochainCxZMod2 X).X q) :
    (cupLeftFixedMor X p q φ).hom ψ = cochainCup p q φ ψ := rfl

/-- The cup with a fixed cocycle on the left sends cycles to cocycles. -/
theorem cupRight_cocycle_cond (X : TopCat.{0}) (p q : ℕ)
    (ψ : singularCochainGroup (ZMod 2) X q) (hψ : cochainCoboundary (ZMod 2) X q ψ = 0) :
    ((cochainCxZMod2 X).iCycles p ≫ cupRightMor X p q ψ) ≫ (cochainCxZMod2 X).d (p + q) (p + q + 1)
      = 0 := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro c
  show cochainCoboundary (ZMod 2) X (p + q)
      (cochainCup p q (((cochainCxZMod2 X).iCycles p).hom c) ψ) = 0
  exact cochainCupZMod2_respects_cocycles p q _ ψ (cochainCoboundary_iCycles X p c) hψ

/-- The cup with a fixed cocycle on the right sends cycles to cocycles. -/
theorem cupLeftFixed_cocycle_cond (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p) (hφ : cochainCoboundary (ZMod 2) X p φ = 0) :
    ((cochainCxZMod2 X).iCycles q ≫ cupLeftFixedMor X p q φ) ≫
        (cochainCxZMod2 X).d (p + q) (p + q + 1) = 0 := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro c
  show cochainCoboundary (ZMod 2) X (p + q)
      (cochainCup p q φ (((cochainCxZMod2 X).iCycles q).hom c)) = 0
  exact cochainCupZMod2_respects_cocycles p q φ _ hφ (cochainCoboundary_iCycles X q c)

/-- Cup with a fixed left cocycle, as a map `cycles p ⟶ H^{p+q}`. -/
def cupLeftMor (X : TopCat.{0}) (p q : ℕ) (ψ : singularCochainGroup (ZMod 2) X q)
    (hψ : cochainCoboundary (ZMod 2) X q ψ = 0) :
    (cochainCxZMod2 X).cycles p ⟶ cohomologyZMod2 X (p + q) :=
  (cochainCxZMod2 X).liftCycles ((cochainCxZMod2 X).iCycles p ≫ cupRightMor X p q ψ) (p + q + 1)
      (cochainCx_next (p + q)) (cupRight_cocycle_cond X p q ψ hψ)
    ≫ (cochainCxZMod2 X).homologyπ (p + q)

/-- Cup with a fixed right cocycle, as a map `cycles q ⟶ H^{p+q}`. -/
def cupRightMor' (X : TopCat.{0}) (p q : ℕ) (φ : singularCochainGroup (ZMod 2) X p)
    (hφ : cochainCoboundary (ZMod 2) X p φ = 0) :
    (cochainCxZMod2 X).cycles q ⟶ cohomologyZMod2 X (p + q) :=
  (cochainCxZMod2 X).liftCycles ((cochainCxZMod2 X).iCycles q ≫ cupLeftFixedMor X p q φ) (p + q + 1)
      (cochainCx_next (p + q)) (cupLeftFixed_cocycle_cond X p q φ hφ)
    ≫ (cochainCxZMod2 X).homologyπ (p + q)

theorem cupLeftMor_cyclesMk (X : TopCat.{0}) (p q : ℕ)
    (ψ : singularCochainGroup (ZMod 2) X q) (hψ : cochainCoboundary (ZMod 2) X q ψ = 0)
    (φ : singularCochainGroup (ZMod 2) X p) (hφ : cochainCoboundary (ZMod 2) X p φ = 0) :
    (cupLeftMor X p q ψ hψ).hom
        ((cochainCxZMod2 X).cyclesMk φ (p + 1) (cochainCx_next p) hφ)
      = cocycleClass X (p + q) (cochainCup p q φ ψ)
          (cochainCupZMod2_respects_cocycles p q φ ψ hφ hψ) := by
  dsimp [cupLeftMor, cocycleClass]
  congr 1
  apply (ModuleCat.mono_iff_injective ((cochainCxZMod2 X).iCycles (p + q))).1 inferInstance
  have h_mk := (cochainCxZMod2 X).i_cyclesMk (cochainCup p q φ ψ) (p + q + 1) (cochainCx_next (p + q)) (cochainCupZMod2_respects_cocycles p q φ ψ hφ hψ)
  have h_lift := congrArg (fun (f : (cochainCxZMod2 X).cycles p ⟶ (cochainCxZMod2 X).X (p + q)) =>
      f.hom ((cochainCxZMod2 X).cyclesMk φ (p + 1) (cochainCx_next p) hφ))
    ((cochainCxZMod2 X).liftCycles_i ((cochainCxZMod2 X).iCycles p ≫ cupRightMor X p q ψ) (p + q + 1) (cochainCx_next (p + q)) (cupRight_cocycle_cond X p q ψ hψ))
  dsimp at h_lift
  have h_eval : ((cochainCxZMod2 X).iCycles p ≫ cupRightMor X p q ψ).hom ((cochainCxZMod2 X).cyclesMk φ (p + 1) (cochainCx_next p) hφ) = cochainCup p q φ ψ := by
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, cupRightMor_hom]
    exact congrArg (fun x => cochainCup p q x ψ) ((cochainCxZMod2 X).i_cyclesMk φ (p + 1) (cochainCx_next p) hφ)
  exact h_lift.trans (h_eval.trans h_mk.symm)

/-
`cupRightMor'` evaluated on `cyclesMk ψ` is the class of `φ ⌣ ψ`.
-/
theorem cupRightMor'_cyclesMk (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p) (hφ : cochainCoboundary (ZMod 2) X p φ = 0)
    (ψ : singularCochainGroup (ZMod 2) X q) (hψ : cochainCoboundary (ZMod 2) X q ψ = 0) :
    (cupRightMor' X p q φ hφ).hom
        ((cochainCxZMod2 X).cyclesMk ψ (q + 1) (cochainCx_next q) hψ)
      = cocycleClass X (p + q) (cochainCup p q φ ψ)
          (cochainCupZMod2_respects_cocycles p q φ ψ hφ hψ) := by
  dsimp [cupRightMor', cocycleClass]
  congr 1
  apply (ModuleCat.mono_iff_injective ((cochainCxZMod2 X).iCycles (p + q))).1 inferInstance
  have h_mk := (cochainCxZMod2 X).i_cyclesMk (cochainCup p q φ ψ) (p + q + 1) (cochainCx_next (p + q)) (cochainCupZMod2_respects_cocycles p q φ ψ hφ hψ)
  have h_lift := congrArg (fun (f : (cochainCxZMod2 X).cycles q ⟶ (cochainCxZMod2 X).X (p + q)) =>
      f.hom ((cochainCxZMod2 X).cyclesMk ψ (q + 1) (cochainCx_next q) hψ))
    ((cochainCxZMod2 X).liftCycles_i ((cochainCxZMod2 X).iCycles q ≫ cupLeftFixedMor X p q φ) (p + q + 1) (cochainCx_next (p + q)) (cupLeftFixed_cocycle_cond X p q φ hφ))
  dsimp at h_lift
  have h_eval : ((cochainCxZMod2 X).iCycles q ≫ cupLeftFixedMor X p q φ).hom ((cochainCxZMod2 X).cyclesMk ψ (q + 1) (cochainCx_next q) hψ) = cochainCup p q φ ψ := by
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, cupLeftFixedMor_hom]
    exact congrArg (fun y => cochainCup p q φ y) ((cochainCxZMod2 X).i_cyclesMk ψ (q + 1) (cochainCx_next q) hψ)
  exact h_lift.trans (h_eval.trans h_mk.symm)

/-- `cupLeftMor` evaluated on a general cycle is the class of its `iCycles` cupped
with `ψ`. -/
theorem cupLeftMor_apply (X : TopCat.{0}) (p q : ℕ)
    (ψ : singularCochainGroup (ZMod 2) X q) (hψ : cochainCoboundary (ZMod 2) X q ψ = 0)
    (c : (cochainCxZMod2 X).cycles p) :
    (cupLeftMor X p q ψ hψ).hom c
      = cocycleClass X (p + q) (cochainCup p q (((cochainCxZMod2 X).iCycles p).hom c) ψ)
          (cochainCupZMod2_respects_cocycles p q _ ψ (cochainCoboundary_iCycles X p c) hψ) := by
  conv_lhs => rw [← cyclesMk_iCycles X p c]
  exact cupLeftMor_cyclesMk X p q ψ hψ (((cochainCxZMod2 X).iCycles p).hom c)
    (cochainCoboundary_iCycles X p c)

/-- `cupRightMor'` evaluated on a general cycle is the class of `φ` cupped with its
`iCycles`. -/
theorem cupRightMor'_apply (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p) (hφ : cochainCoboundary (ZMod 2) X p φ = 0)
    (c : (cochainCxZMod2 X).cycles q) :
    (cupRightMor' X p q φ hφ).hom c
      = cocycleClass X (p + q) (cochainCup p q φ (((cochainCxZMod2 X).iCycles q).hom c))
          (cochainCupZMod2_respects_cocycles p q φ _ hφ (cochainCoboundary_iCycles X q c)) := by
  conv_lhs => rw [← cyclesMk_iCycles X q c]
  exact cupRightMor'_cyclesMk X p q φ hφ (((cochainCxZMod2 X).iCycles q).hom c)
    (cochainCoboundary_iCycles X q c)

/-- If two cochains are equal and one has zero class, so does the other. -/
theorem cocycleClass_eq_zero_of_eq (X : TopCat.{0}) (n : ℕ)
    {φ φ' : singularCochainGroup (ZMod 2) X n} (h : φ = φ')
    (hφ : cochainCoboundary (ZMod 2) X n φ = 0)
    (hφ' : cochainCoboundary (ZMod 2) X n φ' = 0)
    (h0 : cocycleClass X n φ' hφ' = 0) :
    cocycleClass X n φ hφ = 0 :=
  (cocycleClass_congr X n h hφ hφ').trans h0

/-- The cup of a coboundary `δη` (left factor) with a cocycle `ψ` has zero class. -/
theorem cocycleClass_cup_coboundary_left_zero (X : TopCat.{0}) (m q : ℕ)
    (η : singularCochainGroup (ZMod 2) X m) (ψ : singularCochainGroup (ZMod 2) X q)
    (hψ : cochainCoboundary (ZMod 2) X q ψ = 0)
    (hcoc : cochainCoboundary (ZMod 2) X (m + 1 + q)
        (cochainCup (m + 1) q (cochainCoboundary (ZMod 2) X m η) ψ) = 0) :
    cocycleClass X (m + 1 + q)
        (cochainCup (m + 1) q (cochainCoboundary (ZMod 2) X m η) ψ) hcoc = 0 := by
  refine cocycleClass_eq_zero_of_eq X (m + 1 + q)
    (cochainCupZMod2_coboundary_left' m q η ψ hψ) hcoc ?_ ?_
  · rw [← cochainCupZMod2_coboundary_left' m q η ψ hψ]; exact hcoc
  · exact cocycleClass_cast_coboundary_zero X (m + q) (m + 1 + q) (aw_degree_left_succ m q).symm
      (cochainCup m q η ψ) _

/-- The cup of a cocycle `φ` with a coboundary `δη` (right factor) has zero class. -/
theorem cocycleClass_cup_coboundary_right_zero (X : TopCat.{0}) (p m : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p) (hφ : cochainCoboundary (ZMod 2) X p φ = 0)
    (η : singularCochainGroup (ZMod 2) X m)
    (hcoc : cochainCoboundary (ZMod 2) X (p + (m + 1))
        (cochainCup p (m + 1) φ (cochainCoboundary (ZMod 2) X m η)) = 0) :
    cocycleClass X (p + (m + 1))
        (cochainCup p (m + 1) φ (cochainCoboundary (ZMod 2) X m η)) hcoc = 0 := by
  refine cocycleClass_eq_zero_of_eq X (p + (m + 1))
    (cochainCupZMod2_coboundary_right' p m φ η hφ) hcoc ?_ ?_
  · rw [← cochainCupZMod2_coboundary_right' p m φ η hφ]; exact hcoc
  · exact cocycleClass_cast_coboundary_zero X (p + m) (p + (m + 1)) (aw_degree_right_succ p m).symm
      (cochainCup p m φ η) _

/-- The cup of `(d_i p).hom η` (left factor, in the image of a differential into
degree `p`) with a cocycle `ψ` has zero class, for any source index `i`. -/
theorem cocycleClass_cup_d_left_zero (X : TopCat.{0}) (q i p : ℕ)
    (η : (cochainCxZMod2 X).X i) (ψ : singularCochainGroup (ZMod 2) X q)
    (hψ : cochainCoboundary (ZMod 2) X q ψ = 0)
    (hcoc : cochainCoboundary (ZMod 2) X (p + q)
        (cochainCup p q (((cochainCxZMod2 X).d i p).hom η) ψ) = 0) :
    cocycleClass X (p + q) (cochainCup p q (((cochainCxZMod2 X).d i p).hom η) ψ) hcoc = 0 := by
  by_cases h : (ComplexShape.up ℕ).Rel i p
  · obtain rfl : i + 1 = p := h
    exact cocycleClass_cup_coboundary_left_zero X i q η ψ hψ hcoc
  · have hz : cochainCup p q (((cochainCxZMod2 X).d i p).hom η) ψ = 0 := by
      rw [(cochainCxZMod2 X).shape i p h, ModuleCat.hom_zero, LinearMap.zero_apply]
      exact cochainCup_zero_left p q ψ
    exact cocycleClass_eq_zero_of_eq X (p + q) hz hcoc (map_zero _)
      (cocycleClass_zero X (p + q) (map_zero _))

/-- The cup of a cocycle `φ` with `(d_i q).hom η` (right factor) has zero class. -/
theorem cocycleClass_cup_d_right_zero (X : TopCat.{0}) (p i q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p) (hφ : cochainCoboundary (ZMod 2) X p φ = 0)
    (η : (cochainCxZMod2 X).X i)
    (hcoc : cochainCoboundary (ZMod 2) X (p + q)
        (cochainCup p q φ (((cochainCxZMod2 X).d i q).hom η)) = 0) :
    cocycleClass X (p + q) (cochainCup p q φ (((cochainCxZMod2 X).d i q).hom η)) hcoc = 0 := by
  by_cases h : (ComplexShape.up ℕ).Rel i q
  · obtain rfl : i + 1 = q := h
    exact cocycleClass_cup_coboundary_right_zero X p i φ hφ η hcoc
  · have hz : cochainCup p q φ (((cochainCxZMod2 X).d i q).hom η) = 0 := by
      rw [(cochainCxZMod2 X).shape i q h, ModuleCat.hom_zero, LinearMap.zero_apply]
      exact cochainCup_zero_right p q φ
    exact cocycleClass_eq_zero_of_eq X (p + q) hz hcoc (map_zero _)
      (cocycleClass_zero X (p + q) (map_zero _))

/-- The cup-with-left-cocycle map kills coboundaries (cokernel condition). -/
theorem cupLeftMor_toCycles (X : TopCat.{0}) (p q : ℕ)
    (ψ : singularCochainGroup (ZMod 2) X q) (hψ : cochainCoboundary (ZMod 2) X q ψ = 0) :
    (cochainCxZMod2 X).toCycles ((ComplexShape.up ℕ).prev p) p ≫ cupLeftMor X p q ψ hψ = 0 := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro η
  show (cupLeftMor X p q ψ hψ).hom
      (((cochainCxZMod2 X).toCycles ((ComplexShape.up ℕ).prev p) p).hom η) = 0
  rw [cupLeftMor_apply]
  have heq : cochainCup p q (((cochainCxZMod2 X).iCycles p).hom
        (((cochainCxZMod2 X).toCycles ((ComplexShape.up ℕ).prev p) p).hom η)) ψ
      = cochainCup p q (((cochainCxZMod2 X).d ((ComplexShape.up ℕ).prev p) p).hom η) ψ := by
    rw [← ModuleCat.comp_apply, (cochainCxZMod2 X).toCycles_i]
  refine cocycleClass_eq_zero_of_eq X (p + q) heq _ ?_ ?_
  · rw [← heq]
    exact cochainCupZMod2_respects_cocycles p q _ ψ (cochainCoboundary_iCycles X p _) hψ
  · exact cocycleClass_cup_d_left_zero X q ((ComplexShape.up ℕ).prev p) p η ψ hψ _

/-- The cup-with-right-cocycle map kills coboundaries (cokernel condition). -/
theorem cupRightMor'_toCycles (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p) (hφ : cochainCoboundary (ZMod 2) X p φ = 0) :
    (cochainCxZMod2 X).toCycles ((ComplexShape.up ℕ).prev q) q ≫ cupRightMor' X p q φ hφ = 0 := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro η
  show (cupRightMor' X p q φ hφ).hom
      (((cochainCxZMod2 X).toCycles ((ComplexShape.up ℕ).prev q) q).hom η) = 0
  rw [cupRightMor'_apply]
  have heq : cochainCup p q φ (((cochainCxZMod2 X).iCycles q).hom
        (((cochainCxZMod2 X).toCycles ((ComplexShape.up ℕ).prev q) q).hom η))
      = cochainCup p q φ (((cochainCxZMod2 X).d ((ComplexShape.up ℕ).prev q) q).hom η) := by
    rw [← ModuleCat.comp_apply, (cochainCxZMod2 X).toCycles_i]
  refine cocycleClass_eq_zero_of_eq X (p + q) heq _ ?_ ?_
  · rw [← heq]
    exact cochainCupZMod2_respects_cocycles p q φ _ hφ (cochainCoboundary_iCycles X q _)
  · exact cocycleClass_cup_d_right_zero X p ((ComplexShape.up ℕ).prev q) q φ hφ η _

/-! ## 3. Descent to homology in each variable -/

/-- Cup with a fixed left cocycle, descended to `H^p ⟶ H^{p+q}`. -/
def cupHomologyLeft (X : TopCat.{0}) (p q : ℕ) (ψ : singularCochainGroup (ZMod 2) X q)
    (hψ : cochainCoboundary (ZMod 2) X q ψ = 0) :
    cohomologyZMod2 X p ⟶ cohomologyZMod2 X (p + q) :=
  ((cochainCxZMod2 X).homologyIsCokernel ((ComplexShape.up ℕ).prev p) p rfl).desc
    (CokernelCofork.ofπ (cupLeftMor X p q ψ hψ) (cupLeftMor_toCycles X p q ψ hψ))

/-- Cup with a fixed right cocycle, descended to `H^q ⟶ H^{p+q}`. -/
def cupHomologyRight (X : TopCat.{0}) (p q : ℕ) (φ : singularCochainGroup (ZMod 2) X p)
    (hφ : cochainCoboundary (ZMod 2) X p φ = 0) :
    cohomologyZMod2 X q ⟶ cohomologyZMod2 X (p + q) :=
  ((cochainCxZMod2 X).homologyIsCokernel ((ComplexShape.up ℕ).prev q) q rfl).desc
    (CokernelCofork.ofπ (cupRightMor' X p q φ hφ) (cupRightMor'_toCycles X p q φ hφ))

theorem homologyπ_cupHomologyLeft (X : TopCat.{0}) (p q : ℕ)
    (ψ : singularCochainGroup (ZMod 2) X q) (hψ : cochainCoboundary (ZMod 2) X q ψ = 0) :
    (cochainCxZMod2 X).homologyπ p ≫ cupHomologyLeft X p q ψ hψ = cupLeftMor X p q ψ hψ :=
  ((cochainCxZMod2 X).homologyIsCokernel ((ComplexShape.up ℕ).prev p) p rfl).fac
    (CokernelCofork.ofπ (cupLeftMor X p q ψ hψ) (cupLeftMor_toCycles X p q ψ hψ))
    WalkingParallelPair.one

theorem homologyπ_cupHomologyRight (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p) (hφ : cochainCoboundary (ZMod 2) X p φ = 0) :
    (cochainCxZMod2 X).homologyπ q ≫ cupHomologyRight X p q φ hφ = cupRightMor' X p q φ hφ :=
  ((cochainCxZMod2 X).homologyIsCokernel ((ComplexShape.up ℕ).prev q) q rfl).fac
    (CokernelCofork.ofπ (cupRightMor' X p q φ hφ) (cupRightMor'_toCycles X p q φ hφ))
    WalkingParallelPair.one

/-- `cupHomologyLeft` on the class of `φ` is the class of `φ ⌣ ψ`. -/
theorem cupHomologyLeft_apply (X : TopCat.{0}) (p q : ℕ)
    (ψ : singularCochainGroup (ZMod 2) X q) (hψ : cochainCoboundary (ZMod 2) X q ψ = 0)
    (φ : singularCochainGroup (ZMod 2) X p) (hφ : cochainCoboundary (ZMod 2) X p φ = 0) :
    (cupHomologyLeft X p q ψ hψ).hom (cocycleClass X p φ hφ)
      = cocycleClass X (p + q) (cochainCup p q φ ψ)
          (cochainCupZMod2_respects_cocycles p q φ ψ hφ hψ) := by
  dsimp [cocycleClass]
  show ((cochainCxZMod2 X).homologyπ p ≫ cupHomologyLeft X p q ψ hψ).hom
      ((cochainCxZMod2 X).cyclesMk φ (p + 1) (cochainCx_next p) hφ) = _
  rw [homologyπ_cupHomologyLeft]
  exact cupLeftMor_cyclesMk X p q ψ hψ φ hφ

/-- `cupHomologyRight` on the class of `ψ` is the class of `φ ⌣ ψ`. -/
theorem cupHomologyRight_apply (X : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p) (hφ : cochainCoboundary (ZMod 2) X p φ = 0)
    (ψ : singularCochainGroup (ZMod 2) X q) (hψ : cochainCoboundary (ZMod 2) X q ψ = 0) :
    (cupHomologyRight X p q φ hφ).hom (cocycleClass X q ψ hψ)
      = cocycleClass X (p + q) (cochainCup p q φ ψ)
          (cochainCupZMod2_respects_cocycles p q φ ψ hφ hψ) := by
  dsimp [cocycleClass]
  show ((cochainCxZMod2 X).homologyπ q ≫ cupHomologyRight X p q φ hφ).hom
      ((cochainCxZMod2 X).cyclesMk ψ (q + 1) (cochainCx_next q) hψ) = _
  rw [homologyπ_cupHomologyRight]
  exact cupRightMor'_cyclesMk X p q φ hφ ψ hψ

/-! ## 4. The cohomology cup product -/

/-- The chosen cycle representative of a cohomology class. -/
def classCycleRepr (X : TopCat.{0}) (n : ℕ) (a : cohomologyZMod2 X n) :
    (cochainCxZMod2 X).cycles n :=
  Function.surjInv
    ((ModuleCat.epi_iff_surjective ((cochainCxZMod2 X).homologyπ n)).1 inferInstance) a

theorem homologyπ_classCycleRepr (X : TopCat.{0}) (n : ℕ) (a : cohomologyZMod2 X n) :
    ((cochainCxZMod2 X).homologyπ n).hom (classCycleRepr X n a) = a :=
  Function.surjInv_eq
    ((ModuleCat.epi_iff_surjective ((cochainCxZMod2 X).homologyπ n)).1 inferInstance) a

/-- A chosen cocycle representative of a cohomology class. -/
def classRepr (X : TopCat.{0}) (n : ℕ) (a : cohomologyZMod2 X n) :
    singularCochainGroup (ZMod 2) X n :=
  ((cochainCxZMod2 X).iCycles n).hom (classCycleRepr X n a)

theorem classRepr_isCocycle (X : TopCat.{0}) (n : ℕ) (a : cohomologyZMod2 X n) :
    cochainCoboundary (ZMod 2) X n (classRepr X n a) = 0 :=
  cochainCoboundary_iCycles X n (classCycleRepr X n a)

theorem cocycleClass_classRepr (X : TopCat.{0}) (n : ℕ) (a : cohomologyZMod2 X n) :
    cocycleClass X n (classRepr X n a) (classRepr_isCocycle X n a) = a := by
  dsimp [cocycleClass, classRepr]
  have h_cyc := cyclesMk_iCycles X n (classCycleRepr X n a)
  have h_congr := congrArg (fun c => ((cochainCxZMod2 X).homologyπ n).hom c) h_cyc
  exact h_congr.trans (homologyπ_classCycleRepr X n a)

/-- The **cohomology-level cup product** `H^p(X; F₂) → H^q(X; F₂) → H^{p+q}(X; F₂)`. -/
def cupZMod2 {X : TopCat.{0}} {p q : ℕ} (a : cohomologyZMod2 X p) (b : cohomologyZMod2 X q) :
    cohomologyZMod2 X (p + q) :=
  (cupHomologyLeft X p q (classRepr X q b) (classRepr_isCocycle X q b)).hom a

/-- **Well-definedness / computation rule.** The cup of the classes of two
cocycles is the class of their cochain cup. -/
theorem cupZMod2_mk {X : TopCat.{0}} {p q : ℕ}
    (φ : singularCochainGroup (ZMod 2) X p) (hφ : cochainCoboundary (ZMod 2) X p φ = 0)
    (ψ : singularCochainGroup (ZMod 2) X q) (hψ : cochainCoboundary (ZMod 2) X q ψ = 0) :
    cupZMod2 (cocycleClass X p φ hφ) (cocycleClass X q ψ hψ)
      = cocycleClass X (p + q) (cochainCup p q φ ψ)
          (cochainCupZMod2_respects_cocycles p q φ ψ hφ hψ) := by
  rw [cupZMod2, cupHomologyLeft_apply]
  have key := cupHomologyRight_apply X p q φ hφ (classRepr X q (cocycleClass X q ψ hψ))
    (classRepr_isCocycle X q _)
  rw [cocycleClass_classRepr] at key
  have key2 := cupHomologyRight_apply X p q φ hφ ψ hψ
  rw [← key, ← key2]

/-! ## 5. Naturality of the cohomology cup product -/

/-- The pullback `f^* : H^n(Y; F₂) ⟶ H^n(X; F₂)` of a continuous map `f : X ⟶ Y`,
as the action of the singular cohomology functor. -/
def cohPullback {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    cohomologyZMod2 Y n ⟶ cohomologyZMod2 X n :=
  (singularCohomologyZMod2 n).map f.op

/-- The cochain pullback commutes with the coboundary (it is a cochain map). -/
theorem cochainPullback_cochainCoboundary {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y n) :
    cochainCoboundary (ZMod 2) X n (cochainPullback f n φ)
      = cochainPullback f (n + 1) (cochainCoboundary (ZMod 2) Y n φ) := by
  have hcomm := ((singularCochainComplexZMod2).map f.op).comm n (n + 1)
  have h := congrArg (fun (g : (cochainCxZMod2 Y).X n ⟶ (cochainCxZMod2 X).X (n + 1)) => g.hom φ) hcomm
  dsimp at h
  exact h

/-- The cochain pullback of a cocycle is a cocycle. -/
theorem cochainPullback_cocycle {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y n) (hφ : cochainCoboundary (ZMod 2) Y n φ = 0) :
    cochainCoboundary (ZMod 2) X n (cochainPullback f n φ) = 0 := by
  rw [cochainPullback_cochainCoboundary, hφ]
  show (((singularCochainComplexZMod2).map f.op).f (n + 1)).hom 0 = 0
  rw [map_zero]

/-
The pullback of the class of a cocycle is the class of the pullback cochain.
-/
theorem cohPullback_cocycleClass {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y n) (hφ : cochainCoboundary (ZMod 2) Y n φ = 0) :
    (cohPullback f n).hom (cocycleClass Y n φ hφ)
      = cocycleClass X n (cochainPullback f n φ) (cochainPullback_cocycle f n φ hφ) := by
  have hnat := HomologicalComplex.homologyπ_naturality ((singularCochainComplexZMod2).map f.op) n
  have hnat_app := congrArg (fun (g : (cochainCxZMod2 Y).cycles n ⟶ (cochainCxZMod2 X).homology n) =>
      g.hom ((cochainCxZMod2 Y).cyclesMk φ (n + 1) (cochainCx_next n) hφ)) hnat
  dsimp at hnat_app
  have h_cyc : (HomologicalComplex.cyclesMap ((singularCochainComplexZMod2).map f.op) n).hom
      ((cochainCxZMod2 Y).cyclesMk φ (n + 1) (cochainCx_next n) hφ)
      = (cochainCxZMod2 X).cyclesMk (cochainPullback f n φ) (n + 1) (cochainCx_next n) (cochainPullback_cocycle f n φ hφ) := by
    apply (ModuleCat.mono_iff_injective ((cochainCxZMod2 X).iCycles n)).1 inferInstance
    have h1 : ((cochainCxZMod2 X).iCycles n).hom
        ((HomologicalComplex.cyclesMap ((singularCochainComplexZMod2).map f.op) n).hom
          ((cochainCxZMod2 Y).cyclesMk φ (n + 1) (cochainCx_next n) hφ))
        = cochainPullback f n φ := by
      have hcyc := HomologicalComplex.cyclesMap_i ((singularCochainComplexZMod2).map f.op) n
      have hcyc_app := congrArg (fun (g : (cochainCxZMod2 Y).cycles n ⟶ (cochainCxZMod2 X).X n) =>
          g.hom ((cochainCxZMod2 Y).cyclesMk φ (n + 1) (cochainCx_next n) hφ)) hcyc
      dsimp at hcyc_app
      have h_mk := (cochainCxZMod2 Y).i_cyclesMk φ (n + 1) (cochainCx_next n) hφ
      exact hcyc_app.trans (congrArg (fun x => (((singularCochainComplexZMod2).map f.op).f n).hom x) h_mk)
    have h2 := (cochainCxZMod2 X).i_cyclesMk (cochainPullback f n φ) (n + 1) (cochainCx_next n) (cochainPullback_cocycle f n φ hφ)
    exact h1.trans h2.symm
  have h_res := congrArg (fun c => ((cochainCxZMod2 X).homologyπ n).hom c) h_cyc
  exact hnat_app.trans h_res

/-- **Naturality of the cohomology cup product.** `f^*(a ⌣ b) = f^* a ⌣ f^* b`. -/
theorem cohPullback_cupZMod2 {X Y : TopCat.{0}} (f : X ⟶ Y) (p q : ℕ)
    (a : cohomologyZMod2 Y p) (b : cohomologyZMod2 Y q) :
    (cohPullback f (p + q)).hom (cupZMod2 a b)
      = cupZMod2 ((cohPullback f p).hom a) ((cohPullback f q).hom b) := by
  obtain ⟨φ, hφ, rfl⟩ := cocycleClass_surjective Y p a
  obtain ⟨ψ, hψ, rfl⟩ := cocycleClass_surjective Y q b
  rw [cupZMod2_mk, cohPullback_cocycleClass, cohPullback_cocycleClass, cohPullback_cocycleClass,
    cupZMod2_mk]
  exact cocycleClass_congr X (p + q) (cochainCup_naturality f p q φ ψ) _ _

/-! ## 6. Powers of a degree-one class -/

/-
The coboundary of the unit cochain is zero (it is a cocycle).
-/
theorem cochainCoboundary_cochainOne (X : TopCat.{0}) :
    cochainCoboundary (ZMod 2) X 0 (cochainOne (R := ZMod 2) (Z := X)) = 0 := by
  apply cochain_ext; intro σ; rw [cochainCoboundary_eval]; simp [cochainOne_eval];
  grind +splitIndPred

/-- The unit class `1 ∈ H^0(X; F₂)`. -/
def oneZMod2 (X : TopCat.{0}) : cohomologyZMod2 X 0 :=
  cocycleClass X 0 (cochainOne (R := ZMod 2) (Z := X)) (cochainCoboundary_cochainOne X)

/-- The `n`-th cup power `a^n ∈ H^n(X; F₂)` of a degree-one class `a ∈ H^1(X; F₂)`. -/
def cupPowZMod2 {X : TopCat.{0}} (a : cohomologyZMod2 X 1) : (n : ℕ) → cohomologyZMod2 X n
  | 0 => oneZMod2 X
  | (n + 1) => cupZMod2 (cupPowZMod2 a n) a

@[simp] theorem cupPowZMod2_zero {X : TopCat.{0}} (a : cohomologyZMod2 X 1) :
    cupPowZMod2 a 0 = oneZMod2 X := rfl

@[simp] theorem cupPowZMod2_succ {X : TopCat.{0}} (a : cohomologyZMod2 X 1) (n : ℕ) :
    cupPowZMod2 a (n + 1) = cupZMod2 (cupPowZMod2 a n) a := rfl

/-- Each cup power of a degree-one cocycle is a cocycle. -/
theorem cochainPow_cocycle (X : TopCat.{0}) (φ : singularCochainGroup (ZMod 2) X 1)
    (hφ : cochainCoboundary (ZMod 2) X 1 φ = 0) :
    ∀ n, cochainCoboundary (ZMod 2) X n (cochainPow φ n) = 0
  | 0 => cochainCoboundary_cochainOne X
  | (n + 1) => by
      rw [cochainPow_succ]
      exact cochainCupZMod2_respects_cocycles n 1 _ φ (cochainPow_cocycle X φ hφ n) hφ

/-- The cup power of the class of a degree-one cochain is the class of its cochain
power. -/
theorem cupPowZMod2_mk {X : TopCat.{0}} (φ : singularCochainGroup (ZMod 2) X 1)
    (hφ : cochainCoboundary (ZMod 2) X 1 φ = 0) (n : ℕ) :
    cupPowZMod2 (cocycleClass X 1 φ hφ) n
      = cocycleClass X n (cochainPow φ n) (cochainPow_cocycle X φ hφ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [cupPowZMod2_succ, ih, cupZMod2_mk]
      exact cocycleClass_congr X (n + 1) (cochainPow_succ φ n).symm _ _

/-- **Naturality of cup powers.** `f^*(a^n) = (f^* a)^n`. -/
theorem cohPullback_cupPowZMod2 {X Y : TopCat.{0}} (f : X ⟶ Y) (a : cohomologyZMod2 Y 1) (n : ℕ) :
    (cohPullback f n).hom (cupPowZMod2 a n) = cupPowZMod2 ((cohPullback f 1).hom a) n := by
  induction n with
  | zero =>
      show (cohPullback f 0).hom (oneZMod2 Y) = oneZMod2 X
      rw [oneZMod2, cohPullback_cocycleClass]
      refine cocycleClass_congr X 0 ?_ _ _
      apply cochain_ext; intro σ
      rw [cochainPullback_eval, cochainOne_eval, cochainOne_eval]
  | succ n ih =>
      rw [cupPowZMod2_succ, cupPowZMod2_succ, cohPullback_cupZMod2, ih]

/-- **Fixed-point cup powers.** If `f^* a = a` (a degree-one class fixed by the
pullback of a self-map), then `f^*(a^n) = a^n` for all `n`. -/
theorem cohPullback_cupPowZMod2_fixed {X : TopCat.{0}} (f : X ⟶ X) (a : cohomologyZMod2 X 1)
    (ha : (cohPullback f 1).hom a = a) (n : ℕ) :
    (cohPullback f n).hom (cupPowZMod2 a n) = cupPowZMod2 a n := by
  rw [cohPullback_cupPowZMod2, ha]

end

end SphereOddDegree
