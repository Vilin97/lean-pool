/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.SingularCohomology
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.SingularCohomologyHomotopyInvariance
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.RealProjectiveSpace
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.CupProductPowers
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.CohomologyCupProduct

/-!
# Pullback on singular cohomology of the descended odd map

This file connects the library's two finished layers — the **genuine** singular
cohomology functor of `SingularCohomology.lean` and the **genuine** odd-map
descent / double-cover API of `RealProjectiveSpace.lean` — into honest,
formalized statements about the pullback action of the descended odd map on the
real `mod-2` singular cohomology of real projective space.

Everything here is a real mathematical object:

* `rpCohomology n k` and `sphereCohomology n k` are the actual
 `k`-th singular cohomology `ModuleCat (ZMod 2)`-objects of `RP n` and `S^n`,
 obtained by applying the constructed functor `singularCohomologyZMod2 k` to the
 genuine `TopCat` objects `TopCat.of (RP n)` and `TopCat.of (Sphere n)`;
* `inducedOnRPPullback f hf k`, `projPullback n k`, and `spherePullback f k` are
 the actual pullback `ModuleCat (ZMod 2)`-morphisms induced by the descended odd
 map `inducedOnRP f hf`, the double cover `proj n`, and an odd map `f`,
 respectively. They are the functor's action on the opposite of the
 corresponding `TopCat` morphisms; their naturality is structural.

 The degree-1 generator `α ∈ H¹(RPⁿ; F₂)`, its powers `αⁿ`, the cup
product, and the top-class / degree comparison remain genuinely absent (they need
the universal coefficient theorem, the Alexander–Whitney cup product, and the
transfer/Gysin comparison — implemented by the project modules listed below).

## What is proved here

* `inducedOnRPPullback_id` — the pullback of the descended identity is the
 identity on `H^k(RP n; F₂)` (functoriality at the identity).
* `inducedOnRPPullback_comp` — contravariant functoriality of the descended
 pullback: `(g ∘ f)bar^* = gbar^* ≫ fbar^*` (note the reversal).
* `inducedOnRP_pullback_naturality` — the **naturality square** of the double
 cover:
 ```text
 fbar^* ≫ proj^* = proj^* ≫ f^* on H^k(RP n; F₂) ⟶ H^k(S^n; F₂)
 ```
 This is the cohomological form of the commuting square
 `inducedOnRP_comp_proj` (`fbar ∘ proj = proj ∘ f`); it is exactly the
 square used by the top-class / degree comparison (`C3b`).
* `proj_pullback_antipodal` — the nontrivial deck transformation (the antipodal
 map) acts trivially on the image of `proj^*`: `proj^* ≫ antipodal^* = proj^*`.
* `inducedOnRPPullback_antipodal` — the descended antipodal pullback is the
 identity (a corollary of `inducedOnRP_antipodal` and `inducedOnRPPullback_id`).

These are the functorial pullback / double-cover-compatibility / descended-map
naturality facts independent of the cup-product ring computation.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicTopology

namespace SphereOddDegree

/-- The `k`-th singular cohomology of `RP n` with `ZMod 2` coefficients, as an
object of `ModuleCat (ZMod 2)`. This is a genuine object: the constructed functor
`singularCohomologyZMod2 k` applied to the genuine space `TopCat.of (RP n)`. -/
noncomputable def rpCohomology (n k : ℕ) : ModuleCat.{0} (ZMod 2) :=
  (singularCohomologyZMod2 k).obj (Opposite.op (TopCat.of (RP n)))

/-- The `k`-th singular cohomology of `S^n` with `ZMod 2` coefficients, as an
object of `ModuleCat (ZMod 2)`. -/
noncomputable def sphereCohomology (n k : ℕ) : ModuleCat.{0} (ZMod 2) :=
  (singularCohomologyZMod2 k).obj (Opposite.op (TopCat.of (Sphere n)))

/-- The pullback `fbar^* : H^k(RP n; F₂) → H^k(RP n; F₂)` of the descended odd
map `fbar = inducedOnRP f hf`. This is the functor's action on the opposite of
the `TopCat` morphism `TopCat.ofHom (inducedOnRP f hf)`; naturality is
structural. -/
noncomputable def inducedOnRPPullback {n : ℕ} (f : C(Sphere n, Sphere n)) (hf : IsOddMap f)
    (k : ℕ) : rpCohomology n k ⟶ rpCohomology n k :=
  (singularCohomologyZMod2 k).map (TopCat.ofHom (inducedOnRP f hf)).op

/-- The pullback `proj^* : H^k(RP n; F₂) → H^k(S^n; F₂)` of the double cover
`proj n : S^n → RP n`. -/
noncomputable def projPullback (n k : ℕ) : rpCohomology n k ⟶ sphereCohomology n k :=
  (singularCohomologyZMod2 k).map (TopCat.ofHom (proj n)).op

/-- The pullback `f^* : H^k(S^n; F₂) → H^k(S^n; F₂)` of a self-map `f` of the
sphere. -/
noncomputable def spherePullback {n : ℕ} (f : C(Sphere n, Sphere n)) (k : ℕ) :
    sphereCohomology n k ⟶ sphereCohomology n k :=
  (singularCohomologyZMod2 k).map (TopCat.ofHom f).op

/-- Functoriality at the identity: the pullback of the descended identity map is
the identity on `H^k(RP n; F₂)`. -/
theorem inducedOnRPPullback_id (n k : ℕ) :
    inducedOnRPPullback (ContinuousMap.id (Sphere n)) (isOddMap_id n) k
      = 𝟙 (rpCohomology n k) := by
  rw [inducedOnRPPullback, inducedOnRP_id,
    show (TopCat.ofHom (ContinuousMap.id (RP n))) = 𝟙 (TopCat.of (RP n)) from rfl, op_id]
  exact (singularCohomologyZMod2 k).map_id _

/-- Contravariant functoriality of the descended pullback: the pullback of the
descent of `g ∘ f` is `gbar^*` followed by `fbar^*` (the order is reversed, since
cohomology is contravariant). -/
theorem inducedOnRPPullback_comp {n : ℕ} (f g : C(Sphere n, Sphere n))
    (hf : IsOddMap f) (hg : IsOddMap g) (k : ℕ) :
    inducedOnRPPullback (g.comp f) (hg.comp hf) k
      = inducedOnRPPullback g hg k ≫ inducedOnRPPullback f hf k := by
  dsimp [inducedOnRPPullback]
  have h_comp : TopCat.ofHom (inducedOnRP (g.comp f) (hg.comp hf))
      = TopCat.ofHom (inducedOnRP f hf) ≫ TopCat.ofHom (inducedOnRP g hg) := by
    rw [← inducedOnRP_comp hf hg, TopCat.ofHom_comp]
  rw [h_comp, op_comp, Functor.map_comp]
  rfl

/-- **Naturality square of the double cover.** For an odd map `f` with descent
`fbar = inducedOnRP f hf`, the cohomology pullbacks fit into the commuting square

```text
fbar^* ≫ proj^* = proj^* ≫ f^* : H^k(RP n; F₂) ⟶ H^k(S^n; F₂).
```

This is the cohomological image of the point-set commuting square
`inducedOnRP_comp_proj` (`fbar ∘ proj = proj ∘ f`). It is exactly the square the
top-class / degree comparison evaluates on the top class. -/
theorem inducedOnRP_pullback_naturality {n : ℕ} (f : C(Sphere n, Sphere n)) (hf : IsOddMap f)
    (k : ℕ) :
    inducedOnRPPullback f hf k ≫ projPullback n k
      = projPullback n k ≫ spherePullback f k := by
  dsimp [inducedOnRPPullback, projPullback, spherePullback]
  have h_comm : (inducedOnRP f hf).comp (proj n) = (proj n).comp f := inducedOnRP_comp_proj f hf
  have h_top : TopCat.ofHom (proj n) ≫ TopCat.ofHom (inducedOnRP f hf)
      = TopCat.ofHom f ≫ TopCat.ofHom (proj n) := by
    rw [← TopCat.ofHom_comp, ← TopCat.ofHom_comp, h_comm]
  have h_op : (TopCat.ofHom (proj n) ≫ TopCat.ofHom (inducedOnRP f hf)).op
      = (TopCat.ofHom f ≫ TopCat.ofHom (proj n)).op := congrArg Opposite.op h_top
  rw [op_comp, op_comp] at h_op
  have h_map := congrArg (singularCohomologyZMod2 k).map h_op
  rw [Functor.map_comp, Functor.map_comp] at h_map
  exact h_map

/-- The nontrivial deck transformation (the antipodal map) acts trivially on the
image of `proj^*`: `proj^* ≫ antipodal^* = proj^*`. This is the cohomological
form of `proj_comp_antipodal` (`proj n ∘ antipodal n = proj n`). -/
theorem proj_pullback_antipodal {n : ℕ} (k : ℕ) :
    projPullback n k ≫ spherePullback (antipodal n) k = projPullback n k := by
  dsimp [projPullback, spherePullback]
  have h_comm : (proj n).comp (antipodal n) = proj n := proj_comp_antipodal n
  have h_top : TopCat.ofHom (antipodal n) ≫ TopCat.ofHom (proj n) = TopCat.ofHom (proj n) := by
    rw [← TopCat.ofHom_comp, h_comm]
  have h_op : (TopCat.ofHom (antipodal n) ≫ TopCat.ofHom (proj n)).op = (TopCat.ofHom (proj
    n)).op :=
    congrArg Opposite.op h_top
  rw [op_comp] at h_op
  have h_map := congrArg (singularCohomologyZMod2 k).map h_op
  rw [Functor.map_comp] at h_map
  exact h_map

/-- The pullback of the descended antipodal map is the identity on
`H^k(RP n; F₂)`, since the antipodal map descends to the identity on `RP n`
(`inducedOnRP_antipodal`). -/
theorem inducedOnRPPullback_antipodal (n k : ℕ) :
    inducedOnRPPullback (antipodal n) (isOddMap_antipodal n) k = 𝟙 (rpCohomology n k) := by
  rw [inducedOnRPPullback, inducedOnRP_antipodal,
    show (TopCat.ofHom (ContinuousMap.id (RP n))) = 𝟙 (TopCat.of (RP n)) from rfl, op_id]
  exact (singularCohomologyZMod2 k).map_id _

/-- **Homotopy invariance on the sphere (unconditional).** Homotopic self-maps
`f, g` of `S^n` induce equal pullbacks `f^* = g^*` on the mod-2 cohomology
`H^k(S^n; F₂)`.

This specializes `singularCohomologyMap_eq_of_homotopic_continuousMap` to the
sphere pullback `spherePullback`; it is the cohomological input the
top-class / degree comparison will use to replace a sphere self-map by any
homotopic representative. -/
theorem spherePullback_eq_of_homotopic {n : ℕ}
    {f g : C(Sphere n, Sphere n)} (h : ContinuousMap.Homotopic f g) (k : ℕ) :
    spherePullback f k = spherePullback g k := by
  unfold spherePullback
  exact singularCohomologyZMod2_map_eq_of_homotopic_continuousMap
    (X := TopCat.of (Sphere n)) (Y := TopCat.of (Sphere n)) (f := f) (g := g) k h

/-- **Homotopy invariance for descended maps on `RP n` (unconditional).** If two
odd self-maps `f, g` of `S^n` descend to homotopic self-maps of `RP n`, their
pullbacks on `H^k(RP n; F₂)` agree.

The hypothesis is phrased on the descended maps `inducedOnRP f hf` and
`inducedOnRP g hg` (their `Homotopic`ness on `RP n`), since a homotopy on the
sphere need not be odd and hence need not descend on its own. -/
theorem inducedOnRPPullback_eq_of_homotopic {n : ℕ}
    {f g : C(Sphere n, Sphere n)} (hf : IsOddMap f) (hg : IsOddMap g)
    (h : ContinuousMap.Homotopic (inducedOnRP f hf) (inducedOnRP g hg)) (k : ℕ) :
    inducedOnRPPullback f hf k = inducedOnRPPullback g hg k := by
  unfold inducedOnRPPullback
  exact singularCohomologyZMod2_map_eq_of_homotopic_continuousMap
    (X := TopCat.of (RP n)) (Y := TopCat.of (RP n))
    (f := inducedOnRP f hf) (g := inducedOnRP g hg) k h

/-- **Cochain-level fixed-point powers for the descended odd map on `RP n`.**
If a degree-one mod-2 cochain `φ` on `RP n` is fixed by the cochain pullback of the
descended odd map `fbar = inducedOnRP f hf` (i.e. `fbar^* φ = φ`), then so are all
its cup powers: `fbar^*(φⁿ) = φⁿ`.

This is the **cochain-level** form of the final-theorem target
`fbar^*(α)=α ⟹ fbar^*(αⁿ)=αⁿ` for the descended odd map, specialized to the
`ZMod 2` coefficients of the `RP n` computation. The cohomology-level version is
`inducedOnRP_cohPullback_cupPow_fixed` below (the cup product now descends to
cohomology, see `CohomologyCupProduct.lean`); the degree-1 class
`α ∈ H¹(RPⁿ; F₂)` itself remains gated on the universal coefficient theorem, so no
unsupported `α` is introduced. -/
theorem inducedOnRP_cochainPow_fixed {n : ℕ} (f : C(Sphere n, Sphere n)) (hf : IsOddMap f)
    (φ : singularCochainGroup (ZMod 2) (TopCat.of (RP n)) 1)
    (hφ : cochainPullback (TopCat.ofHom (inducedOnRP f hf)) 1 φ = φ) (k : ℕ) :
    cochainPullback (TopCat.ofHom (inducedOnRP f hf)) k (cochainPow φ k)
      = cochainPow φ k :=
  cochainPow_fixed (TopCat.ofHom (inducedOnRP f hf)) φ hφ k

/-- The descended-odd-map pullback on `H^k(RP n; F₂)` is the cohomology pullback
of the descended map `fbar = inducedOnRP f hf`. -/
theorem inducedOnRPPullback_eq_cohPullback {n : ℕ} (f : C(Sphere n, Sphere n)) (hf : IsOddMap f)
    (k : ℕ) :
    inducedOnRPPullback f hf k = cohPullback (TopCat.ofHom (inducedOnRP f hf)) k := rfl

/-- **Cohomology-level fixed-point powers for the descended odd map on `RP n`.**
If a degree-one mod-2 cohomology class `a ∈ H¹(RP n; F₂)` is fixed by the pullback
of the descended odd map `fbar = inducedOnRP f hf` (i.e. `fbar^* a = a`), then so
are all its cup powers: `fbar^*(aⁿ) = aⁿ`.

This is the cohomology-level implication `fbar^*(α)=α ⟹ fbar^*(αⁿ)=αⁿ`, using
the `ZMod 2` cup product `cupZMod2` and its powers `cupPowZMod2` from
`CohomologyCupProduct.lean`. -/
theorem inducedOnRP_cohPullback_cupPow_fixed {n : ℕ} (f : C(Sphere n, Sphere n))
    (hf : IsOddMap f) (a : cohomologyZMod2 (TopCat.of (RP n)) 1)
    (ha : (cohPullback (TopCat.ofHom (inducedOnRP f hf)) 1).hom a = a) (k : ℕ) :
    (cohPullback (TopCat.ofHom (inducedOnRP f hf)) k).hom (cupPowZMod2 a k) = cupPowZMod2 a k :=
  cohPullback_cupPowZMod2_fixed (TopCat.ofHom (inducedOnRP f hf)) a ha k

/-- **Cohomology-level cup naturality for the descended odd map on `RP n`.**
The descended-odd-map pullback is multiplicative for the `ZMod 2` cohomology cup
product: `fbar^*(a ⌣ b) = fbar^* a ⌣ fbar^* b` for `fbar = inducedOnRP f hf`.

This is the `RP n`-specialized form of `cohPullback_cupZMod2`, stated directly in
terms of `inducedOnRPPullback` (which is `cohPullback (TopCat.ofHom (inducedOnRP
f hf))` by `inducedOnRPPullback_eq_cohPullback`). -/
theorem inducedOnRPPullback_cup {n : ℕ} (f : C(Sphere n, Sphere n)) (hf : IsOddMap f)
    (p q : ℕ) (a : rpCohomology n p) (b : rpCohomology n q) :
    (inducedOnRPPullback f hf (p + q)).hom (cupZMod2 a b)
      = cupZMod2 ((inducedOnRPPullback f hf p).hom a) ((inducedOnRPPullback f hf q).hom b) :=
  cohPullback_cupZMod2 (TopCat.ofHom (inducedOnRP f hf)) p q a b

/-- **Cohomology-level cup-power naturality for the descended odd map on `RP n`.**
`fbar^*(aⁿ) = (fbar^* a)ⁿ` for a degree-one class `a ∈ H¹(RP n; F₂)` and the
descended odd map `fbar = inducedOnRP f hf`.

This is the `RP n`-specialized form of `cohPullback_cupPowZMod2`, stated directly
in terms of `inducedOnRPPullback`. Together with a fixed-point hypothesis
`fbar^* a = a` it yields `inducedOnRP_cohPullback_cupPow_fixed`. -/
theorem inducedOnRPPullback_pow {n : ℕ} (f : C(Sphere n, Sphere n)) (hf : IsOddMap f)
    (a : rpCohomology n 1) (k : ℕ) :
    (inducedOnRPPullback f hf k).hom (cupPowZMod2 a k)
      = cupPowZMod2 ((inducedOnRPPullback f hf 1).hom a) k :=
  cohPullback_cupPowZMod2 (TopCat.ofHom (inducedOnRP f hf)) a k

end SphereOddDegree
