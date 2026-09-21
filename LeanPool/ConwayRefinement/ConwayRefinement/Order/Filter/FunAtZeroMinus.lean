/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Order.Filter.Germ.LinearMap
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map

import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.LeftNeighborhood
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Functions at `0⁻` with values in a vector space

`Fun_{0⁻}(V)` is the space of `V`-valued functions at `0⁻`: functions defined on some interval
`(η, 0)`, identified when they agree for all `γ < 0` sufficiently close to `0`. In Lean it is
Mathlib's `Filter.Germ` at `𝓝[<] 0`. The paper's section on functions at `0⁻` says of the word
this construction avoids: "In the language of analysis these classes are the germs at `0⁻` of
`V`-valued functions; we avoid the word, which in this subject denotes a class of series modulo
`J` [Berarducci, Def. 5.1]."

For a subspace `U ⊆ V` the map `Fun_{0⁻}(U) → Fun_{0⁻}(V)` is injective, and its image consists
of the functions taking values in `U` near `0`. Such a function lifts uniquely to `Fun_{0⁻}(U)`,
where a linear map defined on `U` can be applied pointwise; this gives the maps
`Fun_{0⁻}(U) → Fun_{0⁻}(U/U')` used by the compatibility lemmas.

Pointwise pure tensors give the paper's map `θ`: a linear map `u : U → Fun_{0⁻}(V)` extends to
`U ⊗[K] E → Fun_{0⁻}(V ⊗[K] E)` as the canonical map
`θ : Fun_{0⁻}(V) ⊗[K] E → Fun_{0⁻}(V ⊗[K] E)` after `u ⊗ 1`. Over a field both factors are
injective when `u` is, so the extension preserves injectivity.
-/

open Filter Topology
open scoped TensorProduct

universe u v w

public noncomputable section

/-- `Fun_{0⁻}(V)`, the `V`-valued functions at `0⁻`: functions on an interval `(η, 0)`, identified
when they agree for all `γ < 0` sufficiently close to `0` (Mathlib's `Filter.Germ` at `𝓝[<] 0`). -/
abbrev FunAtZeroMinus (V : Type v) := Filter.Germ (𝓝[<] (0 : ℝ)) V

/-- Two functions represent the same element of `Fun_{0⁻}(V)` exactly when they agree on some
interval `(-ε, 0)`. -/
theorem funAtZeroMinus_coe_eq_iff_exists {V : Type v} (f g : ℝ → V) :
    (f : FunAtZeroMinus V) = (g : FunAtZeroMinus V) ↔
      ∃ ε > 0, ∀ γ : ℝ, -ε < γ → γ < 0 → f γ = g γ := by
  rw [Filter.Germ.coe_eq]
  change (∀ᶠ γ in 𝓝[<] (0 : ℝ), f γ = g γ) ↔ _
  rw [eventually_nhdsLT_iff_exists]
  constructor
  · rintro ⟨l, hl, h⟩
    refine ⟨-l, by linarith, fun γ hγ hγ0 ↦ ?_⟩
    exact h γ (by linarith) hγ0
  · rintro ⟨ε, hε, h⟩
    refine ⟨-ε, by linarith, fun γ hγ hγ0 ↦ ?_⟩
    exact h γ (by linarith) hγ0

section Submodule

variable {K : Type u} {V : Type v} [Semiring K] [AddCommMonoid V] [Module K V]

/-- The injective linear map `Fun_{0⁻}(W) → Fun_{0⁻}(V)` induced by the inclusion of a submodule
`W ⊆ V`. -/
def funAtZeroMinusSubmoduleMap (W : Submodule K V) :
    FunAtZeroMinus W →ₗ[K] FunAtZeroMinus V :=
  Filter.Germ.mapLinear W.subtype

/-- The inclusion of a submodule `W ⊆ V` induces an injective map `Fun_{0⁻}(W) → Fun_{0⁻}(V)`. -/
theorem funAtZeroMinusSubmoduleMap_injective (W : Submodule K V) :
    Function.Injective (funAtZeroMinusSubmoduleMap W) :=
  Filter.Germ.mapLinear_injective W.subtype W.injective_subtype

/-- Evaluation of `Fun_{0⁻}(W) → Fun_{0⁻}(V)` on the class of a function `f : ℝ → W`. -/
@[simp]
theorem funAtZeroMinusSubmoduleMap_coe (W : Submodule K V) (f : ℝ → W) :
    funAtZeroMinusSubmoduleMap W (f : FunAtZeroMinus W) =
      ((fun γ ↦ (f γ : V)) : FunAtZeroMinus V) := by
  rw [funAtZeroMinusSubmoduleMap, Filter.Germ.mapLinear_coe]
  rfl

/-- `Fun_{0⁻}(W) ⊆ Fun_{0⁻}(V)`: the functions taking values in `W` near `0`, as the image of
`Fun_{0⁻}(W) → Fun_{0⁻}(V)`. -/
def funAtZeroMinusSubmodule (W : Submodule K V) : Submodule K (FunAtZeroMinus V) :=
  LinearMap.range (funAtZeroMinusSubmoduleMap W)

theorem funAtZeroMinusSubmodule_eq_range (W : Submodule K V) :
    funAtZeroMinusSubmodule W = LinearMap.range (funAtZeroMinusSubmoduleMap W) := (rfl)

/-- A function at `0⁻` lies in `Fun_{0⁻}(W) ⊆ Fun_{0⁻}(V)` exactly when it takes values in `W`
for all `γ < 0` sufficiently close to `0`. -/
theorem mem_funAtZeroMinusSubmodule_iff (W : Submodule K V) (f : FunAtZeroMinus V) :
    f ∈ funAtZeroMinusSubmodule W ↔ Filter.Germ.LiftPred (· ∈ W) f := by
  classical
  constructor
  · rintro ⟨g, rfl⟩
    induction g using Filter.Germ.inductionOn with
    | _ g =>
        rw [funAtZeroMinusSubmoduleMap, Filter.Germ.mapLinear_coe,
          Filter.Germ.liftPred_coe]
        exact Filter.Eventually.of_forall fun x ↦ (g x).property
  · intro hf
    induction f using Filter.Germ.inductionOn with
    | _ f =>
        rw [Filter.Germ.liftPred_coe] at hf
        let g : ℝ → W := fun x ↦ if hx : f x ∈ W then ⟨f x, hx⟩ else 0
        refine ⟨(g : FunAtZeroMinus W), ?_⟩
        rw [funAtZeroMinusSubmoduleMap, Filter.Germ.mapLinear_coe,
          Filter.Germ.coe_eq]
        exact hf.mono fun x hx ↦ by simp [g, hx]

/-- The class of a function `f : ℝ → V` lies in `Fun_{0⁻}(W) ⊆ Fun_{0⁻}(V)` exactly when
`f γ ∈ W` for all `γ < 0` sufficiently close to `0`. -/
theorem coe_mem_funAtZeroMinusSubmodule_iff (W : Submodule K V) (f : ℝ → V) :
    (f : FunAtZeroMinus V) ∈ funAtZeroMinusSubmodule W ↔
      ∀ᶠ x in 𝓝[<] (0 : ℝ), f x ∈ W := by
  rw [mem_funAtZeroMinusSubmodule_iff, Filter.Germ.liftPred_coe]

/-- The class of a function `f : ℝ → V` lies in `Fun_{0⁻}(W) ⊆ Fun_{0⁻}(V)` exactly when `f` is
`W`-valued throughout some interval `(-ε, 0)`. -/
theorem coe_mem_funAtZeroMinusSubmodule_iff_exists (W : Submodule K V) (f : ℝ → V) :
    (f : FunAtZeroMinus V) ∈ funAtZeroMinusSubmodule W ↔
      ∃ ε > 0, ∀ γ : ℝ, -ε < γ → γ < 0 → f γ ∈ W := by
  rw [coe_mem_funAtZeroMinusSubmodule_iff, eventually_nhdsLT_iff_exists]
  constructor
  · rintro ⟨l, hl, h⟩
    refine ⟨-l, by linarith, fun γ hγ hγ0 ↦ ?_⟩
    exact h γ (by linarith) hγ0
  · rintro ⟨ε, hε, h⟩
    refine ⟨-ε, by linarith, fun γ hγ hγ0 ↦ ?_⟩
    exact h γ (by linarith) hγ0

/-- An element of `Fun_{0⁻}(W) ⊆ Fun_{0⁻}(V)` has a representative valued in `W` everywhere. -/
theorem exists_coe_eq_of_mem_funAtZeroMinusSubmodule (W : Submodule K V) {g : FunAtZeroMinus V}
    (hg : g ∈ funAtZeroMinusSubmodule W) :
    ∃ f : ℝ → V, (∀ γ, f γ ∈ W) ∧ g = (f : FunAtZeroMinus V) := by
  classical
  induction g using Filter.Germ.inductionOn with
  | _ f =>
      rw [coe_mem_funAtZeroMinusSubmodule_iff] at hg
      refine ⟨fun γ ↦ if f γ ∈ W then f γ else 0, fun γ ↦ ?_, ?_⟩
      · by_cases h : f γ ∈ W
        · simp [h]
        · simp [h]
      · rw [Filter.Germ.coe_eq]
        exact hg.mono fun γ hγ ↦ by simp [hγ]

/-- The pointwise image of a function at `0⁻` under a linear map `f` takes values in the range
of `f`. -/
theorem mapLinear_mem_funAtZeroMinusSubmodule_range {U : Type*} [AddCommMonoid U] [Module K U]
    (f : U →ₗ[K] V) (g : FunAtZeroMinus U) :
    Filter.Germ.mapLinear f g ∈ funAtZeroMinusSubmodule (LinearMap.range f) := by
  induction g using Filter.Germ.inductionOn with
  | _ h =>
      rw [Filter.Germ.mapLinear_coe, coe_mem_funAtZeroMinusSubmodule_iff]
      exact Filter.Eventually.of_forall fun γ ↦ LinearMap.mem_range_self f (h γ)

/-- A function at `0⁻` lying in both `Fun_{0⁻}(W)` and `Fun_{0⁻}(W')` lies in
`Fun_{0⁻}(W ⊓ W')`. -/
theorem mem_funAtZeroMinusSubmodule_inf (W W' : Submodule K V) {g : FunAtZeroMinus V}
    (hg : g ∈ funAtZeroMinusSubmodule W) (hg' : g ∈ funAtZeroMinusSubmodule W') :
    g ∈ funAtZeroMinusSubmodule (W ⊓ W') := by
  rw [mem_funAtZeroMinusSubmodule_iff] at hg hg' ⊢
  induction g using Filter.Germ.inductionOn with
  | _ f =>
      rw [Filter.Germ.liftPred_coe] at hg hg' ⊢
      exact (hg.and hg').mono fun γ hγ ↦ Submodule.mem_inf.mpr hγ

end Submodule

section TensorProduct

variable {K : Type u} {U : Type*} {V : Type v} {E : Type w}
variable [CommSemiring K]
variable [AddCommMonoid U] [AddCommMonoid V] [AddCommMonoid E]
variable [Module K U] [Module K V] [Module K E]

/-- The paper's composite `V ⊗ V' → V ⊗ Fun_{0⁻}(W) → Fun_{0⁻}(V ⊗ W)` of
lem:germ-linear-algebra (second map `θ`), with the tensor factor on the right: a linear map
`u : U → Fun_{0⁻}(V)` extends to `U ⊗[K] E → Fun_{0⁻}(V ⊗[K] E)`, sending `x ⊗ e` to the class
of the pointwise tensors `γ ↦ u(x)(γ) ⊗ e`. -/
def funAtZeroMinusTensorId (u : U →ₗ[K] FunAtZeroMinus V) :
    U ⊗[K] E →ₗ[K] FunAtZeroMinus (V ⊗[K] E) :=
  (Filter.Germ.tensorProduct (l := 𝓝[<] (0 : ℝ))).comp
    (TensorProduct.map u LinearMap.id)

/-- Evaluation of the tensor extension on a pure tensor. -/
@[simp]
theorem funAtZeroMinusTensorId_tmul (u : U →ₗ[K] FunAtZeroMinus V) (x : U) (e : E) :
    funAtZeroMinusTensorId (E := E) u (x ⊗ₜ[K] e) =
      Filter.Germ.mapLinear ((TensorProduct.mk K V E).flip e) (u x) := by
  rw [funAtZeroMinusTensorId, LinearMap.comp_apply, TensorProduct.map_tmul,
    Filter.Germ.tensorProduct_tmul]
  rfl

/-- If a value of `u` is represented by `f`, then its tensor extension is represented by
the pointwise pure-tensor function. -/
theorem funAtZeroMinusTensorId_tmul_of_eq_coe
    (u : U →ₗ[K] FunAtZeroMinus V) (x : U) (e : E) (f : ℝ → V)
    (h : u x = (f : FunAtZeroMinus V)) :
    funAtZeroMinusTensorId (E := E) u (x ⊗ₜ[K] e) =
      (fun γ ↦ f γ ⊗ₜ[K] e : FunAtZeroMinus (V ⊗[K] E)) := by
  rw [funAtZeroMinusTensorId_tmul, h, Filter.Germ.mapLinear_coe]
  rfl

end TensorProduct

section SubmoduleQuotient

variable {K : Type u} {V : Type v} [Semiring K] [AddCommMonoid V] [Module K V]

/-- `Fun_{0⁻}(W) ⊆ Fun_{0⁻}(W')` inside `Fun_{0⁻}(V)` when `W ⊆ W'`. -/
theorem funAtZeroMinusSubmodule_mono {W W' : Submodule K V} (hWW : W ≤ W') {x : FunAtZeroMinus V}
    (hx : x ∈ funAtZeroMinusSubmodule W) : x ∈ funAtZeroMinusSubmodule W' := by
  rw [mem_funAtZeroMinusSubmodule_iff] at hx ⊢
  induction x using Filter.Germ.inductionOn with
  | _ f =>
      rw [Filter.Germ.liftPred_coe] at hx ⊢
      exact hx.mono fun gamma hgamma ↦ hWW hgamma

/-- The map `Fun_{0⁻}(W) → Fun_{0⁻}(V)` with codomain restricted to its image
`Fun_{0⁻}(W) ⊆ Fun_{0⁻}(V)`. -/
def funAtZeroMinusSubmoduleOf (W : Submodule K V) :
    FunAtZeroMinus W →ₗ[K] funAtZeroMinusSubmodule W :=
  (funAtZeroMinusSubmoduleMap W).codRestrict (funAtZeroMinusSubmodule W) fun g ↦ by
    rw [mem_funAtZeroMinusSubmodule_iff]
    induction g using Filter.Germ.inductionOn with
    | _ f =>
        rw [funAtZeroMinusSubmoduleMap_coe, Filter.Germ.liftPred_coe]
        exact Filter.Eventually.of_forall fun x ↦ (f x).property

/-- `Fun_{0⁻}(W) ≃ Fun_{0⁻}(W) ⊆ Fun_{0⁻}(V)`: the functions at `0⁻` with values in `W` are
linearly equivalent to their image in `Fun_{0⁻}(V)`, the identification the paper makes. -/
def funAtZeroMinusSubmoduleEquiv (W : Submodule K V) :
    FunAtZeroMinus W ≃ₗ[K] funAtZeroMinusSubmodule W :=
  LinearEquiv.ofBijective (funAtZeroMinusSubmoduleOf W) (by
    constructor
    · intro g g' hgg
      apply funAtZeroMinusSubmoduleMap_injective W
      exact congrArg Subtype.val hgg
    · rintro ⟨f, hf⟩
      classical
      rw [mem_funAtZeroMinusSubmodule_iff] at hf
      induction f using Filter.Germ.inductionOn with
      | _ f =>
          rw [Filter.Germ.liftPred_coe] at hf
          let g : ℝ → W := fun x ↦ if hx : f x ∈ W then ⟨f x, hx⟩ else 0
          refine ⟨(g : FunAtZeroMinus W), Subtype.ext ?_⟩
          change funAtZeroMinusSubmoduleMap W (g : FunAtZeroMinus W) = (f : FunAtZeroMinus V)
          rw [funAtZeroMinusSubmoduleMap_coe, Filter.Germ.coe_eq]
          exact hf.mono fun x hx ↦ by simp [g, hx])

/-- The equivalence `Fun_{0⁻}(W) ≃ Fun_{0⁻}(W) ⊆ Fun_{0⁻}(V)` is the map
`Fun_{0⁻}(W) → Fun_{0⁻}(V)` on underlying functions at `0⁻`. -/
theorem coe_funAtZeroMinusSubmoduleEquiv_apply (W : Submodule K V) (g : FunAtZeroMinus W) :
    ((funAtZeroMinusSubmoduleEquiv W g : funAtZeroMinusSubmodule W) : FunAtZeroMinus V) =
      funAtZeroMinusSubmoduleMap W g := (rfl)

/-- `Fun_{0⁻}(W) → Fun_{0⁻}(Q)` along a linear map `q : W → Q`, applied pointwise to a function
at `0⁻` taking values in `W` near `0`; for `q` a quotient map this is
`Fun_{0⁻}(W) → Fun_{0⁻}(W/W')`. -/
def funAtZeroMinusQuotientMap (W : Submodule K V) {Q : Type w} [AddCommMonoid Q] [Module K Q]
    (q : W →ₗ[K] Q) : funAtZeroMinusSubmodule W →ₗ[K] FunAtZeroMinus Q :=
  (Filter.Germ.mapLinear q).comp (funAtZeroMinusSubmoduleEquiv W).symm.toLinearMap

/-- Evaluation of `Fun_{0⁻}(W) → Fun_{0⁻}(Q)` on the class of a `W`-valued function `f`: the
class of `γ ↦ q (f γ)`. -/
theorem funAtZeroMinusQuotientMap_coe (W : Submodule K V) {Q : Type w}
    [AddCommMonoid Q] [Module K Q] (q : W →ₗ[K] Q) (f : ℝ → W)
    (hf : ((fun γ ↦ (f γ : V)) : FunAtZeroMinus V) ∈ funAtZeroMinusSubmodule W) :
    funAtZeroMinusQuotientMap W q ⟨((fun γ ↦ (f γ : V)) : FunAtZeroMinus V), hf⟩ =
      ((fun γ ↦ q (f γ)) : FunAtZeroMinus Q) := by
  have hsymm : (funAtZeroMinusSubmoduleEquiv W).symm
      ⟨((fun γ ↦ (f γ : V)) : FunAtZeroMinus V), hf⟩ = (f : FunAtZeroMinus W) := by
    apply (funAtZeroMinusSubmoduleEquiv W).injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    change ((fun γ ↦ (f γ : V)) : FunAtZeroMinus V) =
      funAtZeroMinusSubmoduleMap W (f : FunAtZeroMinus W)
    rw [funAtZeroMinusSubmoduleMap_coe]
  rw [funAtZeroMinusQuotientMap, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hsymm,
    Filter.Germ.mapLinear_coe]
  rfl

/-- The image in `Fun_{0⁻}(Q)` vanishes exactly when the function takes values in the kernel
submodule `W'` for all `γ < 0` sufficiently close to `0`. -/
theorem funAtZeroMinusQuotientMap_eq_zero_iff (W W' : Submodule K V) {Q : Type w}
    [AddCommMonoid Q] [Module K Q] (q : W →ₗ[K] Q)
    (hker : ∀ w : W, q w = 0 ↔ (w : V) ∈ W')
    (g : funAtZeroMinusSubmodule W) :
    funAtZeroMinusQuotientMap W q g = 0 ↔ (g : FunAtZeroMinus V) ∈ funAtZeroMinusSubmodule W' := by
  obtain ⟨u, rfl⟩ := (funAtZeroMinusSubmoduleEquiv W).surjective g
  induction u using Filter.Germ.inductionOn with
  | _ f =>
      have hcoe : ((funAtZeroMinusSubmoduleEquiv W (f : FunAtZeroMinus W) :
          funAtZeroMinusSubmodule W) : FunAtZeroMinus V) =
            ((fun γ ↦ (f γ : V)) : FunAtZeroMinus V) := by
        change funAtZeroMinusSubmoduleMap W (f : FunAtZeroMinus W) =
          ((fun γ ↦ (f γ : V)) : FunAtZeroMinus V)
        rw [funAtZeroMinusSubmoduleMap_coe]
      rw [funAtZeroMinusQuotientMap, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        LinearEquiv.symm_apply_apply, Filter.Germ.mapLinear_coe, hcoe,
        coe_mem_funAtZeroMinusSubmodule_iff,
        show (0 : FunAtZeroMinus Q) = ((fun _ : ℝ ↦ (0 : Q)) : FunAtZeroMinus Q) from rfl,
        Filter.Germ.coe_eq]
      exact ⟨fun h ↦ h.mono fun γ hγ ↦ (hker (f γ)).mp hγ,
        fun h ↦ h.mono fun γ hγ ↦ (hker (f γ)).mpr hγ⟩

end SubmoduleQuotient

section Injectivity

/-- Tensor extension by the identity preserves injectivity for linear maps into functions at `0⁻`
over a field: the paper's canonical map `θ : Fun_{0⁻}(V) ⊗[K] E → Fun_{0⁻}(V ⊗[K] E)` is
injective, and so is `u ⊗ 1` by flatness. -/
theorem funAtZeroMinusTensorId_injective_of_injective
    {K : Type u} {U : Type*} {V : Type v} {E : Type w}
    [Field K]
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup E]
    [Module K U] [Module K V] [Module K E]
    (u : U →ₗ[K] FunAtZeroMinus V) (hu : Function.Injective u) :
    Function.Injective (funAtZeroMinusTensorId (E := E) u) :=
  Filter.Germ.tensorProduct_injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap (M := E) u hu)

/-- Naturality of the tensor extension in the second factor. -/
theorem mapLinear_lTensor_funAtZeroMinusTensorId
    {K : Type u} {U : Type*} {V : Type v} {E E' : Type*}
    [CommSemiring K]
    [AddCommMonoid U] [AddCommMonoid V] [AddCommMonoid E] [AddCommMonoid E']
    [Module K U] [Module K V] [Module K E] [Module K E']
    (u : U →ₗ[K] FunAtZeroMinus V) (f : E →ₗ[K] E') (T : U ⊗[K] E) :
    Filter.Germ.mapLinear (f.lTensor V) (funAtZeroMinusTensorId u T) =
      funAtZeroMinusTensorId u (f.lTensor U T) := by
  induction T with
  | zero => simp
  | tmul x e =>
      rw [LinearMap.lTensor_tmul, funAtZeroMinusTensorId_tmul, funAtZeroMinusTensorId_tmul]
      induction u x using Filter.Germ.inductionOn with
      | _ g =>
          rw [Filter.Germ.mapLinear_coe, Filter.Germ.mapLinear_coe, Filter.Germ.mapLinear_coe]
          rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Exactness for the tensor extension into `Fun_{0⁻}(V ⊗[K] E)`: if `u` is injective and
`(u ⊗ 1) T` is represented by values in the image of `1 ⊗ m`, then `T` itself lies in the image
of `1 ⊗ m`. -/
theorem exists_eq_lTensor_of_funAtZeroMinusTensorId_eq
    {K : Type u} {U : Type*} {V : Type v} {E A : Type*}
    [Field K]
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup E] [AddCommGroup A]
    [Module K U] [Module K V] [Module K E] [Module K A]
    (u : U →ₗ[K] FunAtZeroMinus V) (hu : Function.Injective u) (m : A →ₗ[K] E)
    (T : U ⊗[K] E) (g : FunAtZeroMinus (V ⊗[K] A))
    (h : funAtZeroMinusTensorId u T = Filter.Germ.mapLinear (m.lTensor V) g) :
    ∃ T' : U ⊗[K] A, T = m.lTensor U T' := by
  set π := (LinearMap.range m).mkQ
  have hπ : (π.lTensor V).comp (m.lTensor V) = 0 := by
    rw [← LinearMap.lTensor_comp, LinearMap.range_mkQ_comp, LinearMap.lTensor_zero]
  have h1 := congrArg (Filter.Germ.mapLinear (π.lTensor V)) h
  rw [mapLinear_lTensor_funAtZeroMinusTensorId] at h1
  have h2 : Filter.Germ.mapLinear (π.lTensor V) (Filter.Germ.mapLinear (m.lTensor V) g) = 0 := by
    rw [Filter.Germ.mapLinear_comp, hπ]
    exact Filter.Germ.mapLinear_zero_apply g
  rw [h2] at h1
  have h3 : π.lTensor U T = 0 :=
    funAtZeroMinusTensorId_injective_of_injective u hu (by rw [h1, map_zero])
  exact ((lTensor_exact U (LinearMap.exact_map_mkQ_range m)
    (Submodule.mkQ_surjective _)) T).mp h3 |>.imp fun T' hT' ↦ hT'.symm

end Injectivity

end
