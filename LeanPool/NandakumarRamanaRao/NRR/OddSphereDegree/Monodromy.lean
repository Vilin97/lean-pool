/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.Covering
import Mathlib.Topology.Homotopy.Lifting

/-!
# Monodromy of the canonical double cover `S^n → RP n`

This file specialises Mathlib's covering-space lifting and monodromy API
(`Mathlib.Topology.Homotopy.Lifting`) to the canonical double cover
`proj n : S^n → RP n` established in `Covering.lean`.

It records the genuine input data of *Route A* of

```text
double cover → π₁(RPⁿ) acting on the fibre → ZMod 2 → H¹(RPⁿ; F₂)
```

namely the path-lifting property and the monodromy action of the fundamental
groupoid of `RP n` on the (two-element) fibres of `proj n`. Every declaration is a specialization of an existing Mathlib theorem to `proj_isCoveringMap`.

## Main results

* `proj_exists_path_lifts` — every path in `RP n` lifts to `S^n` from a chosen
 start point (the *existence* half of lifting; uniqueness is Mathlib's
 `IsCoveringMap.eq_of_comp_eq`).
* `projMonodromy` — the monodromy action of a path-homotopy class on the fibres.
* `projMonodromy_bijective` — the monodromy action is bijective (it is a
 permutation of the two-element fibre when the endpoints coincide).
* `projMonodromyFunctor` — the monodromy packaged as a functor
 `FundamentalGroupoid (RP n) ⥤ Type _`.
* `projMonodromy_refl` / `projMonodromy_refl_apply` — the monodromy of the
 trivial (`refl`) path is the identity of the fibre.
* `projMonodromy_trans_apply` — the monodromy of a concatenation of paths is the
 composite of the monodromies (functoriality, pointwise).
* `projMonodromy_map` — the monodromy of the `proj n`-image of an upstairs path
 sends the start point (as a fibre element) to the end point.
* `projMonodromyPerm` / `projMonodromyPerm_apply` — the monodromy of a *loop* at
 `x` packaged as a permutation `Equiv.Perm (proj n ⁻¹' {x})` of the two-element
 fibre over the base point.
* `projMonodromyPerm_refl` / `projMonodromyPerm_trans` — the unit and
 (anti-)composition laws for the fibre permutation, i.e. the honest
 (anti-)homomorphism data of the action of `π₁(RP n, x)` on the fibre.

These declarations provide the monodromy permutation action. The associated classifying
homomorphism and degree-one cohomology class are developed in the downstream modules.
-/

noncomputable section

namespace SphereOddDegree

open CategoryTheory unitInterval

/-- Every path `γ` in `RP n`, together with a lift `e` of its start point, lifts
to a path in `S^n` starting at `e`. This is the *existence* half of path lifting
for the double cover (the *uniqueness* half is `IsCoveringMap.eq_of_comp_eq`). -/
theorem proj_exists_path_lifts (n : ℕ) (γ : C(unitInterval, RP n)) (e : Sphere n)
    (h : γ 0 = proj n e) :
    ∃ Γ : C(unitInterval, Sphere n), proj n ∘ Γ = γ ∧ Γ 0 = e :=
  (proj_isCoveringMap n).exists_path_lifts γ e h

/-- The monodromy action of the double cover `proj n`: a homotopy class of paths
from `x` to `y` in `RP n` sends a lift of `x` to the endpoint of the lifted path,
giving a map between the fibres over `x` and `y`. -/
def projMonodromy (n : ℕ) {x y : RP n} (γ : Path.Homotopic.Quotient x y) :
    (proj n ⁻¹' {x}) → (proj n ⁻¹' {y}) :=
  (proj_isCoveringMap n).monodromy γ

/-- The monodromy action of the double cover is bijective; in particular, taking
`x = y`, the fundamental group `π₁(RP n, x)` acts on the two-element fibre by
permutations. -/
theorem projMonodromy_bijective (n : ℕ) {x y : RP n} (γ : Path.Homotopic.Quotient x y) :
    (projMonodromy n γ).Bijective :=
  (proj_isCoveringMap n).monodromy_bijective γ

/-- The monodromy of the double cover packaged as a functor from the fundamental
groupoid of `RP n` to `Type`. -/
def projMonodromyFunctor (n : ℕ) :
    FundamentalGroupoid (RP n) ⥤ Type _ :=
  (proj_isCoveringMap n).monodromyFunctor

/-- The monodromy of the trivial (`refl`) path at `x` is the identity of the
fibre over `x` (the unit law of the monodromy functor, specialised to
`proj n`). -/
theorem projMonodromy_refl (n : ℕ) (x : RP n) :
    projMonodromy n (Path.Homotopic.Quotient.refl x) = id :=
  (proj_isCoveringMap n).monodromy_refl

/-- Pointwise form of `projMonodromy_refl`: the monodromy of the trivial
(`refl`) path fixes every point of the fibre. -/
@[simp] theorem projMonodromy_refl_apply (n : ℕ) (x : RP n) (e : proj n ⁻¹' {x}) :
    projMonodromy n (Path.Homotopic.Quotient.refl x) e = e :=
  congrFun (projMonodromy_refl n x) e

/-- The monodromy of a concatenation of homotopy classes of paths is the
composite of the monodromies (functoriality, in pointwise form). -/
theorem projMonodromy_trans_apply (n : ℕ) {x y z : RP n}
    (γ : Path.Homotopic.Quotient x y) (γ' : Path.Homotopic.Quotient y z)
    (e : proj n ⁻¹' {x}) :
    projMonodromy n (γ.trans γ') e = projMonodromy n γ' (projMonodromy n γ e) :=
  (proj_isCoveringMap n).monodromy_trans_apply γ γ' e

/-- The monodromy of the `proj n`-image of an upstairs path from `a` to `b`
sends `a` (as the canonical element of the fibre over `proj n a`) to `b`. This
is the compatibility of monodromy with lifts, specialised to `proj n`. -/
theorem projMonodromy_map (n : ℕ) {a b : Sphere n} (γ : Path.Homotopic.Quotient a b) :
    projMonodromy n (γ.map ⟨proj n, (proj_isCoveringMap n).continuous⟩) ⟨a, rfl⟩ = ⟨b, rfl⟩ :=
  (proj_isCoveringMap n).monodromy_map γ

/-- The monodromy of a *loop* at `x` (a homotopy class of paths from `x` to `x`)
packaged as a permutation of the two-element fibre over `x`. This is the action
of `π₁(RP n, x)` on the fibre by permutations; it preserves the fibre over the
base point by construction. -/
def projMonodromyPerm (n : ℕ) {x : RP n} (γ : Path.Homotopic.Quotient x x) :
    Equiv.Perm (proj n ⁻¹' {x}) :=
  Equiv.ofBijective _ (projMonodromy_bijective n γ)

/-- The permutation `projMonodromyPerm` acts as the underlying monodromy map. -/
@[simp] theorem projMonodromyPerm_apply (n : ℕ) {x : RP n}
    (γ : Path.Homotopic.Quotient x x) (e : proj n ⁻¹' {x}) :
    projMonodromyPerm n γ e = projMonodromy n γ e := rfl

/-- The monodromy permutation of the trivial (`refl`) loop is the identity
permutation of the fibre. This is the unit law for the fibre permutation
action, packaged at the `Equiv.Perm` level. -/
@[simp] theorem projMonodromyPerm_refl (n : ℕ) (x : RP n) :
    projMonodromyPerm n (Path.Homotopic.Quotient.refl x) = 1 := by
  ext e
  simp [projMonodromyPerm]

/-- The monodromy permutation of a concatenation of loops is the product (in
`Equiv.Perm`) of the monodromy permutations, in the order opposite to path
concatenation: `projMonodromyPerm (γ.trans γ') = projMonodromyPerm γ' *
projMonodromyPerm γ`. Together with `projMonodromyPerm_refl` this is exactly the
(anti-)homomorphism data of the fibre permutation action of `π₁(RP n, x)`; it is
the explicit input for the vertex homomorphism `π₁(RP n, x) →* Equiv.Perm
(proj n ⁻¹' {x})` (PR-fg2), without yet constructing that homomorphism. -/
theorem projMonodromyPerm_trans (n : ℕ) {x : RP n}
    (γ γ' : Path.Homotopic.Quotient x x) :
    projMonodromyPerm n (γ.trans γ') = projMonodromyPerm n γ' * projMonodromyPerm n γ := by
  ext e
  simp [projMonodromyPerm, Equiv.Perm.mul_apply, projMonodromy_trans_apply]

/-! ### Specialised path-lifting API

The declarations below specialise Mathlib's named path-lift constructor
`IsCoveringMap.liftPath` (and its uniqueness/endpoint lemmas) to `proj n`,
giving a reusable, fully-applied lift of a path together with its defining
properties. These complement the existence statement `proj_exists_path_lifts`
by providing the *chosen* lift as a single named map. -/

section PathLift
variable (n : ℕ) (γ : C(unitInterval, RP n)) (e : Sphere n) (h : γ 0 = proj n e)

/-- The canonical lift to `S^n` of a path `γ` in `RP n`, starting at a chosen
lift `e` of its start point. Specialises `IsCoveringMap.liftPath` to the double
cover `proj n`. -/
def projLiftPath : C(unitInterval, Sphere n) :=
  (proj_isCoveringMap n).liftPath γ e h

/-- `projLiftPath` is a lift of `γ`: composing with `proj n` recovers `γ`. -/
theorem projLiftPath_lifts : proj n ∘ projLiftPath n γ e h = γ :=
  (proj_isCoveringMap n).liftPath_lifts γ e h

/-- `projLiftPath` starts at the chosen fibre point `e`. -/
@[simp] theorem projLiftPath_zero : projLiftPath n γ e h 0 = e :=
  (proj_isCoveringMap n).liftPath_zero γ e h

/-- The endpoint of the lifted path lies in the fibre over `γ 1`: its image
under `proj n` is exactly the endpoint of `γ`. -/
theorem projLiftPath_endpoint_mem : proj n (projLiftPath n γ e h 1) = γ 1 :=
  congrFun (projLiftPath_lifts n γ e h) 1

/-- Uniqueness of the lift with fixed start point: any continuous lift of `γ`
starting at `e` equals `projLiftPath`. This is the unique characterisation of
the lifted path, specialised to `proj n`. -/
theorem eq_projLiftPath {Γ : C(unitInterval, Sphere n)}
    (hΓ : proj n ∘ Γ = γ) (hΓ0 : Γ 0 = e) : Γ = projLiftPath n γ e h :=
  ((proj_isCoveringMap n).eq_liftPath_iff' h).mpr ⟨hΓ, hΓ0⟩

end PathLift

/-- Uniqueness of path lifts for the double cover: two continuous lifts of the
same path that agree at a single point are equal. This is
`IsCoveringMap.eq_of_comp_eq` specialised to `proj n` over the (preconnected)
unit interval. -/
theorem proj_path_lift_unique (n : ℕ) {Γ₁ Γ₂ : C(unitInterval, Sphere n)}
    (h₁ : proj n ∘ Γ₁ = proj n ∘ Γ₂) (t : unitInterval) (ht : Γ₁ t = Γ₂ t) :
    Γ₁ = Γ₂ :=
  DFunLike.coe_injective
    ((proj_isCoveringMap n).eq_of_comp_eq Γ₁.continuous Γ₂.continuous h₁ t ht)

/-- The lift of a `const` path is the `const` path: lifting the trivial path at
`proj n e`, starting at `e`, yields the trivial path at `e`. Specialises
`IsCoveringMap.liftPath_const` to `proj n`. -/
theorem projLiftPath_const (n : ℕ) (e : Sphere n) (x : RP n) (hpe : x = proj n e) :
    projLiftPath n (.const _ x) e hpe = .const _ e := by
  unfold projLiftPath
  exact (proj_isCoveringMap n).liftPath_const hpe

/-- Paths homotopic rel endpoints lift, from a common start point, to paths with
the same endpoint. This is `IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel`
specialised to `proj n`; it is the endpoint-invariance underlying the
well-definedness of `projMonodromy`. -/
theorem projLiftPath_apply_one_eq_of_homotopicRel (n : ℕ)
    {γ₀ γ₁ : C(unitInterval, RP n)} (hh : γ₀.HomotopicRel γ₁ {0, 1}) (e : Sphere n)
    (h₀ : γ₀ 0 = proj n e) (h₁ : γ₁ 0 = proj n e) :
    projLiftPath n γ₀ e h₀ 1 = projLiftPath n γ₁ e h₁ 1 :=
  (proj_isCoveringMap n).liftPath_apply_one_eq_of_homotopicRel hh e h₀ h₁

/-! ### Monodromy as an equivalence of fibres, and inverse-path behaviour

For a homotopy class `γ` of paths from `x` to `y`, the monodromy map is a
bijection between the two fibres (`projMonodromy_bijective`); we package it as a
bundled `Equiv` `projMonodromyEquiv`. The reverse path `γ.symm` induces the
inverse bijection: `projMonodromy_symm_apply_left`/`_right` are the two cancel
laws, and `projMonodromyEquiv_symm` identifies the inverse equivalence. -/

/-- The monodromy of a homotopy class of paths from `x` to `y`, packaged as a
bundled equivalence between the two fibres of the double cover. This refines
`projMonodromy_bijective`; on loops it specialises to `projMonodromyPerm`. -/
def projMonodromyEquiv (n : ℕ) {x y : RP n} (γ : Path.Homotopic.Quotient x y) :
    (proj n ⁻¹' {x}) ≃ (proj n ⁻¹' {y}) :=
  Equiv.ofBijective _ (projMonodromy_bijective n γ)

/-- The equivalence `projMonodromyEquiv` acts as the underlying monodromy map. -/
@[simp] theorem projMonodromyEquiv_apply (n : ℕ) {x y : RP n}
    (γ : Path.Homotopic.Quotient x y) (e : proj n ⁻¹' {x}) :
    projMonodromyEquiv n γ e = projMonodromy n γ e := rfl

/-- The reverse path cancels the monodromy on the left: transporting along `γ`
and then back along `γ.symm` returns the original fibre point. This is the
inverse-path behaviour underlying the bijectivity of monodromy. -/
@[simp] theorem projMonodromy_symm_apply_left (n : ℕ) {x y : RP n}
    (γ : Path.Homotopic.Quotient x y) (e : proj n ⁻¹' {x}) :
    projMonodromy n γ.symm (projMonodromy n γ e) = e := by
  rw [← projMonodromy_trans_apply, Path.Homotopic.Quotient.trans_symm,
    projMonodromy_refl_apply]

/-- The reverse path cancels the monodromy on the right. -/
@[simp] theorem projMonodromy_symm_apply_right (n : ℕ) {x y : RP n}
    (γ : Path.Homotopic.Quotient x y) (e : proj n ⁻¹' {y}) :
    projMonodromy n γ (projMonodromy n γ.symm e) = e := by
  rw [← projMonodromy_trans_apply, Path.Homotopic.Quotient.symm_trans,
    projMonodromy_refl_apply]

/-- The inverse of the monodromy equivalence of `γ` is the monodromy equivalence
of the reverse path `γ.symm`. -/
theorem projMonodromyEquiv_symm (n : ℕ) {x y : RP n}
    (γ : Path.Homotopic.Quotient x y) :
    (projMonodromyEquiv n γ).symm = projMonodromyEquiv n γ.symm := by
  apply Equiv.ext
  intro e
  rw [Equiv.symm_apply_eq, projMonodromyEquiv_apply, projMonodromyEquiv_apply,
    projMonodromy_symm_apply_right]

/-- The monodromy permutation of the reverse loop is the inverse permutation:
`projMonodromyPerm (γ.symm) = (projMonodromyPerm γ)⁻¹`. This is the inverse law
of the fibre permutation action of `π₁(RP n, x)`. -/
theorem projMonodromyPerm_symm (n : ℕ) {x : RP n}
    (γ : Path.Homotopic.Quotient x x) :
    projMonodromyPerm n γ.symm = (projMonodromyPerm n γ)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← projMonodromyPerm_trans,
    Path.Homotopic.Quotient.trans_symm, projMonodromyPerm_refl]

/-! ### The vertex action of the fundamental group on the fibre (PR-fg2)

The unit law (`projMonodromyPerm_refl`) and the composition law
(`projMonodromyPerm_trans`) assemble into a genuine group homomorphism from the
fundamental group `π₁(RP n, x) = FundamentalGroup (RP n) x` to the permutation
group of the two-element fibre. Because the `End`-multiplication of the
fundamental group reverses order (`a * b = b ≫ a`) and `projMonodromyPerm_trans`
also reverses order, the two reversals cancel and the assignment
`a ↦ projMonodromyPerm (toPath a)` is an honest (covariant) homomorphism, not an
anti-homomorphism. This is the classifying datum of *Route A* toward
`H¹(RPⁿ; F₂)`: the action of `π₁(RPⁿ)` on the fibre of the double cover. -/

/-- The monodromy action of the fundamental group `π₁(RP n, x)` on the
two-element fibre over `x`, as a genuine group homomorphism
`FundamentalGroup (RP n) x →* Equiv.Perm (proj n ⁻¹' {x})`. Its `map_one` is
`projMonodromyPerm_refl` and its `map_mul` is `projMonodromyPerm_trans`; the
order-reversal of the `End`-multiplication cancels the order-reversal of
monodromy under path concatenation, so this is a covariant homomorphism. -/
def projMonodromyHom (n : ℕ) (x : RP n) :
    FundamentalGroup (RP n) x →* Equiv.Perm (proj n ⁻¹' {x}) where
  toFun a := projMonodromyPerm n (FundamentalGroup.toPath a)
  map_one' := projMonodromyPerm_refl n x
  map_mul' a b :=
    projMonodromyPerm_trans n (FundamentalGroup.toPath b) (FundamentalGroup.toPath a)

/-- The homomorphism `projMonodromyHom` sends a class to the monodromy
permutation of its underlying loop. -/
@[simp] theorem projMonodromyHom_apply (n : ℕ) (x : RP n)
    (a : FundamentalGroup (RP n) x) :
    projMonodromyHom n x a = projMonodromyPerm n (FundamentalGroup.toPath a) := rfl

/-- The genuine monodromy action of the fundamental group `π₁(RP n, x)` on the
two-element fibre of the double cover, obtained by transporting the canonical
`MulAction (Equiv.Perm _) _` along `projMonodromyHom`. This is the
fundamental-group action that *Route A* toward `H¹(RPⁿ; F₂)` requires; it is
provided as a `def` (not a global `instance`) so as not to pollute typeclass
resolution. -/
@[instance_reducible]
def projMonodromyMulAction (n : ℕ) (x : RP n) :
    MulAction (FundamentalGroup (RP n) x) (proj n ⁻¹' {x}) :=
  MulAction.compHom _ (projMonodromyHom n x)

/-- The `projMonodromyMulAction` scalar action is the monodromy permutation of
the underlying loop applied to the fibre point. -/
theorem projMonodromyMulAction_smul (n : ℕ) (x : RP n)
    (a : FundamentalGroup (RP n) x) (e : proj n ⁻¹' {x}) :
    (projMonodromyMulAction n x).toSMul.smul a e
      = projMonodromyPerm n (FundamentalGroup.toPath a) e := rfl

/-! ### Naturality of monodromy under a descended odd map

For an odd map `f : Sⁿ → Sⁿ` with descended map `inducedOnRP f hf : RPⁿ → RPⁿ`,
the square `proj ∘ f = inducedOnRP f hf ∘ proj` makes `f` a morphism of the
double cover over `inducedOnRP f hf`. Consequently `f` carries fibres to fibres
(`inducedOnRPFiberMap`) and *intertwines* the monodromy: transporting along a
path `γ` downstairs and then mapping by `f` agrees with mapping by `f` first and
then transporting along the descended path `γ.map (inducedOnRP f hf)`. This is
the monodromy-naturality of the descended odd map. -/

/-- The fibrewise map induced by the odd map `f`: it sends the fibre over `q` to
the fibre over the descended image `inducedOnRP f hf q`. This is the bundled
form of `inducedOnRP_mapsTo_fiber`. -/
def inducedOnRPFiberMap (n : ℕ) (f : C(Sphere n, Sphere n)) (hf : IsOddMap f)
    {q : RP n} (e : proj n ⁻¹' {q}) : proj n ⁻¹' {inducedOnRP f hf q} :=
  ⟨f e.1, by
    have he : proj n e.1 = q := e.2
    change proj n (f e.1) = inducedOnRP f hf q
    rw [← inducedOnRP_comm f hf e.1, he]⟩

/-- The underlying point of `inducedOnRPFiberMap` is `f` applied to the
underlying point. -/
@[simp] theorem inducedOnRPFiberMap_coe (n : ℕ) (f : C(Sphere n, Sphere n))
    (hf : IsOddMap f) {q : RP n} (e : proj n ⁻¹' {q}) :
    (inducedOnRPFiberMap n f hf e : Sphere n) = f e.1 := rfl

/-
**Monodromy naturality of the descended odd map.** The fibrewise map
induced by `f` intertwines the monodromy of a path `γ` in `RPⁿ` with the
monodromy of its descended image `γ.map (inducedOnRP f hf)`:

```text
f ∘ (monodromy γ) = (monodromy (γ.map fbar)) ∘ f on fibres.
```

Equivalently `f` is a morphism of the double cover over `inducedOnRP f hf`, so it
commutes with path transport. This is the path-level intertwining requested for
the descended-odd-map branch.
-/
theorem inducedOnRPFiberMap_projMonodromy (n : ℕ) (f : C(Sphere n, Sphere n))
    (hf : IsOddMap f) {x y : RP n} (γ : Path.Homotopic.Quotient x y)
    (e : proj n ⁻¹' {x}) :
    inducedOnRPFiberMap n f hf (projMonodromy n γ e)
      = projMonodromy n (γ.map ⟨inducedOnRP f hf, (inducedOnRP f hf).continuous⟩)
          (inducedOnRPFiberMap n f hf e) := by
  induction γ using Quotient.inductionOn with
  | h γ_path =>
    rcases e with ⟨p, hp⟩
    apply Subtype.ext
    dsimp [inducedOnRPFiberMap, projMonodromy, IsCoveringMap.monodromy]
    have he : (γ_path : C(unitInterval, RP n)) 0 = proj n p := by
      change γ_path 0 = proj n p
      rw [γ_path.source, hp.symm]
    have he_f : (γ_path.map (inducedOnRP f hf).continuous : C(unitInterval, RP n)) 0 = proj n (f p) := by
      change inducedOnRP f hf (γ_path 0) = proj n (f p)
      rw [γ_path.source, ← hp, inducedOnRP_comm f hf]
    have h_lift : f.comp (projLiftPath n γ_path p he) = projLiftPath n (γ_path.map (inducedOnRP f hf).continuous) (f p) he_f := by
      apply eq_projLiftPath
      · ext t
        have h_proj : proj n (projLiftPath n γ_path p he t) = γ_path t :=
          congr_fun (projLiftPath_lifts n γ_path p he) t
        change proj n (f (projLiftPath n γ_path p he t)) = inducedOnRP f hf (γ_path t)
        rw [← inducedOnRP_comm f hf, h_proj]
      · simp [projLiftPath_zero]
    have h1 := congr_fun (congr_arg ContinuousMap.toFun h_lift) 1
    exact h1

/-- The descended-odd-map naturality, specialised to a loop and expressed as an
intertwining of the monodromy permutations. For a loop `γ` at `x`, the fibre map
of `f` conjugates the base-point permutation to the descended-loop permutation:
it sends `projMonodromyPerm n γ`-orbits to `projMonodromyPerm n (γ.map fbar)`-
orbits. This is the loop-level form of `inducedOnRPFiberMap_projMonodromy`. -/
theorem inducedOnRPFiberMap_projMonodromyPerm (n : ℕ) (f : C(Sphere n, Sphere n))
    (hf : IsOddMap f) {x : RP n} (γ : Path.Homotopic.Quotient x x)
    (e : proj n ⁻¹' {x}) :
    inducedOnRPFiberMap n f hf (projMonodromyPerm n γ e)
      = projMonodromyPerm n (γ.map ⟨inducedOnRP f hf, (inducedOnRP f hf).continuous⟩)
          (inducedOnRPFiberMap n f hf e) := by
  simpa using inducedOnRPFiberMap_projMonodromy n f hf γ e

end SphereOddDegree
