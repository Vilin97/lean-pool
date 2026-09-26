/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Vendored.XiaMvPowerSeriesEquiv
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Formal power series over a reduced ring ([WP] lem:formal-series-reduced)

The mathlib-grade layer of [WP] §6.6, upstream of the `TailC0` machinery so that
`WP/Tail.lean` can consume it: `MvPowerSeries J P` over a reduced commutative `P`
is reduced, for an ARBITRARY index `J` — via the injection of a reduced ring into
the product of its prime quotients, the componentwise `MvPowerSeries.map` product
decomposition, and mathlib's `NoZeroDivisors (MvPowerSeries σ R)`.
-/

@[expose] public section

@[expose] public section

namespace WeightedParity

/-- `MvPowerSeries` over a product ring is the product of the `MvPowerSeries`
(coefficientwise). -/
noncomputable def mvPowerSeriesPi (J : Type*) {ι : Type*} (R : ι → Type*)
    [∀ i, CommRing (R i)] :
    MvPowerSeries J (∀ i, R i) ≃+* ∀ i, MvPowerSeries J (R i) where
  toFun f i := MvPowerSeries.map (Pi.evalRingHom R i) f
  invFun g t i := g i t
  left_inv f := rfl
  right_inv g := rfl
  map_add' f g := by
    funext i
    exact map_add (MvPowerSeries.map (Pi.evalRingHom R i)) f g
  map_mul' f g := by
    funext i
    exact map_mul (MvPowerSeries.map (Pi.evalRingHom R i)) f g

/-- A reduced commutative ring embeds into the product of its prime quotients
(kernel = nilradical = 0; `nilradical_eq_sInf`). -/
theorem exists_injective_pi_quotient (P : Type*) [CommRing P] [IsReduced P] :
    ∃ f : P →+* ∀ I : {I : Ideal P // I.IsPrime}, P ⧸ I.1,
      Function.Injective f := by
  classical
  refine ⟨RingHom.pi fun I => Ideal.Quotient.mk I.1, ?_⟩
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hmem : ∀ I : {I : Ideal P // I.IsPrime}, a ∈ I.1 := fun I =>
    Ideal.Quotient.eq_zero_iff_mem.mp (congrFun ha I)
  have hnil : a ∈ nilradical P := by
    rw [nilradical_eq_sInf, Ideal.mem_sInf]
    intro I hI
    exact hmem ⟨I, hI⟩
  rwa [nilradical_eq_zero, Ideal.zero_eq_bot, Ideal.mem_bot] at hnil

/-- **`lem:formal-series-reduced`** ([WP] lines 1241–1261): formal power series in
arbitrarily many variables over a reduced commutative ring form a reduced ring. -/
theorem isReduced_mvPowerSeries (J : Type*) (P : Type*) [CommRing P] [IsReduced P] :
    IsReduced (MvPowerSeries J P) := by
  classical
  obtain ⟨f, hf⟩ := exists_injective_pi_quotient P
  let hred : ∀ I : {I : Ideal P // I.IsPrime},
      IsReduced (MvPowerSeries J (P ⧸ I.1)) := fun I => by
    let := I.2
    infer_instance
  have hmap : Function.Injective
      (MvPowerSeries.map (σ := J) f :
        MvPowerSeries J P → MvPowerSeries J (∀ I : {I : Ideal P // I.IsPrime}, P ⧸ I.1)) :=
    MvPowerSeries.map_injective hf
  have hcomp : Function.Injective
      (((mvPowerSeriesPi J
          (fun I : {I : Ideal P // I.IsPrime} => P ⧸ I.1)) :
        MvPowerSeries J (∀ I : {I : Ideal P // I.IsPrime}, P ⧸ I.1) ≃+*
          ∀ I : {I : Ideal P // I.IsPrime}, MvPowerSeries J (P ⧸ I.1)).toRingHom.comp
        (MvPowerSeries.map f)) := by
    rw [RingHom.coe_comp]
    exact (mvPowerSeriesPi J _).injective.comp hmap
  exact isReduced_of_injective _ hcomp

end WeightedParity
