/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.Induced
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandFiniteness
public import Mathlib.SetTheory.Cardinal.Finite
/-!
# Low-degree Tate cohomology under equivariant equivalences

An equivariant multiplicative equivalence identifies fixed elements, norm
kernels, norm images, and augmentation images.  Consequently it induces
equivalences on the concrete low-degree Tate cohomology groups and preserves
the Herbrand quotient.

These transport results let calculations made on field units or local
coordinates be applied to their actual images inside idele groups without
introducing comparison assumptions.
-/

@[expose] public section

noncomputable
section

namespace CyclicCohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uA uB

variable {G : Type uG} {A : Type uA} {B : Type uB}
    [Group G] [Fintype G]
    [CommGroup A] [CommGroup B]
    [MulDistribMulAction G A]
    [MulDistribMulAction G B]

/-- An equivariant multiplicative equivalence commutes with the finite
group norm. -/
theorem equivariantMulEquiv_map_tateNorm
    (e : A ≃* B)
    (he : ∀ (g : G) (a : A),
      e (g • a) = g • e a)
    (a : A) :
    e (tateNorm G A a) =
      tateNorm G B (e a) := by
  simpa using
    map_tateNorm
      (G := G) (A := A) (B := B)
      e.toMonoidHom
      (fun g x ↦ by simpa using he g x) a

omit [Fintype G] in
/-- An equivariant multiplicative equivalence commutes with the
augmentation operator. -/
theorem equivariantMulEquiv_map_sigmaMinusOne
    (e : A ≃* B)
    (he : ∀ (g : G) (a : A),
      e (g • a) = g • e a)
    (σ : G) (a : A) :
    e (sigmaMinusOne G A σ a) =
      sigmaMinusOne G B σ (e a) := by
  simpa using
    map_sigmaMinusOne
      (G := G) (A := A) (B := B)
      e.toMonoidHom
      (fun g x ↦ by simpa using he g x) σ a

/-- An equivariant multiplicative equivalence restricted to fixed
subgroups. -/
noncomputable def fixedSubgroupEquivariantMulEquiv
    (e : A ≃* B)
    (he : ∀ (g : G) (a : A),
      e (g • a) = g • e a) :
    fixedSubgroup G A ≃* fixedSubgroup G B where
  toFun a :=
    ⟨e a.1, fun g ↦ by
      rw [← he g a.1, a.2 g]⟩
  invFun b :=
    ⟨e.symm b.1, fun g ↦ by
      rw [← mulEquiv_symm_commutes_smul e he, b.2 g]⟩
  left_inv a := by
    apply Subtype.ext
    exact e.symm_apply_apply a.1
  right_inv b := by
    apply Subtype.ext
    exact e.apply_symm_apply b.1
  map_mul' _ _ := by
    apply Subtype.ext
    exact e.map_mul _ _

/-- An equivariant multiplicative equivalence restricted to norm
kernels. -/
noncomputable def normKernelEquivariantMulEquiv
    (e : A ≃* B)
    (he : ∀ (g : G) (a : A),
      e (g • a) = g • e a) :
    normKernelSubgroup G A ≃*
      normKernelSubgroup G B where
  toFun a :=
    ⟨e a.1, by
      change tateNorm G B (e a.1) = 1
      calc
        tateNorm G B (e a.1) =
            e (tateNorm G A a.1) :=
          (equivariantMulEquiv_map_tateNorm
            e he a.1).symm
        _ = e 1 := congrArg e a.2
        _ = 1 := e.map_one⟩
  invFun b :=
    ⟨e.symm b.1, by
      change tateNorm G A (e.symm b.1) = 1
      apply e.injective
      calc
        e (tateNorm G A (e.symm b.1)) =
            tateNorm G B (e (e.symm b.1)) :=
          equivariantMulEquiv_map_tateNorm
            e he (e.symm b.1)
        _ = tateNorm G B b.1 := by
          rw [e.apply_symm_apply]
        _ = 1 := b.2
        _ = e 1 := e.map_one.symm⟩
  left_inv a := by
    apply Subtype.ext
    exact e.symm_apply_apply a.1
  right_inv b := by
    apply Subtype.ext
    exact e.apply_symm_apply b.1
  map_mul' _ _ := by
    apply Subtype.ext
    exact e.map_mul _ _

/-- An equivariant multiplicative equivalence induces an equivalence on
degree-zero Tate cohomology. -/
noncomputable def herbrandH0EquivariantMulEquiv
    (e : A ≃* B)
    (he : ∀ (g : G) (a : A),
      e (g • a) = g • e a) :
    HerbrandH0 G A ≃* HerbrandH0 G B := by
  let f := fixedSubgroupEquivariantMulEquiv e he
  let N :=
    (tateNormSubgroup G A).subgroupOf
      (fixedSubgroup G A)
  let M :=
    (tateNormSubgroup G B).subgroupOf
      (fixedSubgroup G B)
  exact quotientMulEquivOfSplit N M
    f.toMonoidHom f.symm.toMonoidHom
    (fun y ↦ f.apply_symm_apply y)
    (fun x hx ↦ by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      rcases hx with ⟨a, ha⟩
      refine ⟨e a, ?_⟩
      change tateNorm G B (e a) = e x.1
      calc
        tateNorm G B (e a) =
            e (tateNorm G A a) :=
          (equivariantMulEquiv_map_tateNorm
            e he a).symm
        _ = e x.1 := congrArg e ha)
    (fun y hy ↦ by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      rcases hy with ⟨b, hb⟩
      refine ⟨e.symm b, ?_⟩
      apply e.injective
      change
        e (tateNorm G A (e.symm b)) =
          e (e.symm y.1)
      calc
        e (tateNorm G A (e.symm b)) =
            tateNorm G B (e (e.symm b)) :=
          equivariantMulEquiv_map_tateNorm
            e he (e.symm b)
        _ = tateNorm G B b := by
          rw [e.apply_symm_apply]
        _ = y.1 := hb
        _ = e (e.symm y.1) :=
          (e.apply_symm_apply y.1).symm)
    (fun x hx ↦ by
      have hx1 : x = 1 := by
        apply f.injective
        simpa [f] using hx
      rw [hx1]
      exact N.one_mem)

@[simp]
theorem herbrandH0EquivariantMulEquiv_mk
    (e : A ≃* B)
    (he : ∀ (g : G) (a : A),
      e (g • a) = g • e a)
    (a : fixedSubgroup G A) :
    herbrandH0EquivariantMulEquiv e he (HerbrandH0.mk a) =
      HerbrandH0.mk (fixedSubgroupEquivariantMulEquiv e he a) := by
  rfl

/-- An equivariant multiplicative equivalence induces an equivalence on
degree-minus-one Tate cohomology. -/
noncomputable def herbrandHMinusOneEquivariantMulEquiv
    (e : A ≃* B)
    (he : ∀ (g : G) (a : A),
      e (g • a) = g • e a)
    (σ : G) :
    HerbrandHMinusOne G A σ ≃*
      HerbrandHMinusOne G B σ := by
  let f := normKernelEquivariantMulEquiv e he
  let N :=
    (augmentationSubgroup G A σ).subgroupOf
      (normKernelSubgroup G A)
  let M :=
    (augmentationSubgroup G B σ).subgroupOf
      (normKernelSubgroup G B)
  exact quotientMulEquivOfSplit N M
    f.toMonoidHom f.symm.toMonoidHom
    (fun y ↦ f.apply_symm_apply y)
    (fun x hx ↦ by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      rcases hx with ⟨a, ha⟩
      refine ⟨e a, ?_⟩
      change sigmaMinusOne G B σ (e a) = e x.1
      calc
        sigmaMinusOne G B σ (e a) =
            e (sigmaMinusOne G A σ a) :=
          (equivariantMulEquiv_map_sigmaMinusOne
            e he σ a).symm
        _ = e x.1 := congrArg e ha)
    (fun y hy ↦ by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      rcases hy with ⟨b, hb⟩
      refine ⟨e.symm b, ?_⟩
      apply e.injective
      change
        e (sigmaMinusOne G A σ (e.symm b)) =
          e (e.symm y.1)
      calc
        e (sigmaMinusOne G A σ (e.symm b)) =
            sigmaMinusOne G B σ (e (e.symm b)) :=
          equivariantMulEquiv_map_sigmaMinusOne
            e he σ (e.symm b)
        _ = sigmaMinusOne G B σ b := by
          rw [e.apply_symm_apply]
        _ = y.1 := hb
        _ = e (e.symm y.1) :=
          (e.apply_symm_apply y.1).symm)
    (fun x hx ↦ by
      have hx1 : x = 1 := by
        apply f.injective
        simpa [f] using hx
      rw [hx1]
      exact N.one_mem)

/-- Finiteness of `H⁰` transports through an equivariant
multiplicative equivalence. -/
theorem herbrandH0Finite_of_equivariantMulEquiv
    (e : A ≃* B)
    (he : ∀ (g : G) (a : A),
      e (g • a) = g • e a)
    [Finite (HerbrandH0 G A)] :
    Finite (HerbrandH0 G B) :=
  Finite.of_equiv
    (HerbrandH0 G A)
    (herbrandH0EquivariantMulEquiv e he).toEquiv

/-- Finiteness of `H⁻¹` transports through an equivariant
multiplicative equivalence. -/
theorem herbrandHMinusOneFinite_of_equivariantMulEquiv
    (e : A ≃* B)
    (he : ∀ (g : G) (a : A),
      e (g • a) = g • e a)
    (σ : G)
    [Finite (HerbrandHMinusOne G A σ)] :
    Finite (HerbrandHMinusOne G B σ) :=
  Finite.of_equiv
    (HerbrandHMinusOne G A σ)
    (herbrandHMinusOneEquivariantMulEquiv
      e he σ).toEquiv

/-- Herbrand quotients are invariant under equivariant multiplicative
equivalence. -/
theorem herbrandQuotient_eq_of_equivariantMulEquiv
    (e : A ≃* B)
    (he : ∀ (g : G) (a : A),
      e (g • a) = g • e a)
    (σ : G)
    [Finite (HerbrandH0 G A)]
    [Finite (HerbrandHMinusOne G A σ)] :
    letI _h0B : Finite (HerbrandH0 G B) :=
      herbrandH0Finite_of_equivariantMulEquiv e he
    letI _hMinusOneB :
        Finite (HerbrandHMinusOne G B σ) :=
      herbrandHMinusOneFinite_of_equivariantMulEquiv
        e he σ
    herbrandQuotient (G := G) (A := A) σ =
      herbrandQuotient (G := G) (A := B) σ := by
  let h0B : Finite (HerbrandH0 G B) :=
    herbrandH0Finite_of_equivariantMulEquiv e he
  let hMinusOneB :
      Finite (HerbrandHMinusOne G B σ) :=
    herbrandHMinusOneFinite_of_equivariantMulEquiv
      e he σ
  have h0Card :
      Nat.card (HerbrandH0 G A) =
        Nat.card (HerbrandH0 G B) := by
    exact Nat.card_congr
      (herbrandH0EquivariantMulEquiv e he).toEquiv
  have hMinusOneCard :
      Nat.card (HerbrandHMinusOne G A σ) =
        Nat.card
          (HerbrandHMinusOne G B σ) := by
    exact Nat.card_congr
      (herbrandHMinusOneEquivariantMulEquiv
        e he σ).toEquiv
  rw [herbrandQuotient_eq_card_ratio,
    herbrandQuotient_eq_card_ratio,
    h0Card, hMinusOneCard]

end CyclicCohomology
