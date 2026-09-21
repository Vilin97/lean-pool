/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.Topology.Germ
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.ZeroSets.Basic

/-!
# The local ring of analytic germs

An analytic germ is a Mathlib `Filter.Germ` with a representative analytic at the base point.
Equality is agreement on a neighborhood, rather than equality just at the base point. The scalar
field `𝕜` is an explicit argument, `AnalyticGerm 𝕜 x`, and may be any nontrivially normed field:
the scalar germs form a `𝕜`-algebra, evaluation detects its units, identifies its unique maximal
ideal with the germs vanishing at the base point, and identifies the quotient with `𝕜`, and
analytic maps act contravariantly by `𝕜`-algebra homomorphisms. Over `ℝ` or `ℂ` the germs form an
integral domain, by the identity principle on connected balls. The rest of the germ theory in this
library is developed for `𝕜 = ℂ`.

The motivating references are [Suwa][Suwa2024] (2024), Section 1.4, Propositions 1.5--1.7, and
[Jakóbczak–Jarnicki][JakobczakJarnicki2021] (2021), Section 1.8. We use `AnalyticAt` for
convergent power series; on finite-dimensional complex domains this agrees with the project's
holomorphic convention. The construction works on arbitrary normed spaces, including the zero
space. Analytic Weierstrass division and preparation are not asserted here.

## Main definitions

* `analyticGermSubring`: The subring of germs admitting a representative analytic at the base point.
* `AnalyticGerm`: Scalar analytic germs at `x`, with the ring operations inherited from Mathlib
  germs.
* `ofAnalyticAt`: The germ of a function analytic at the base point.
* `eval`: Evaluation of an analytic germ at its base point, as a ring homomorphism.
* `const`: Constant functions define a ring homomorphism into analytic germs.
* `evalAlgHom`: Evaluation also preserves the `𝕜`-algebra structure.
* `pullback`: Composition with an analytic map pulls scalar germs back as a `𝕜`-algebra
  homomorphism.
* `pullbackOfEq`: Pullback along a map whose value at the source point is only known up to a stated
  equation, letting the target germ's base point be phrased as any value equal to `f x`.
* `quotientKerEvalEquiv`: Quotienting analytic germs by the evaluation kernel gives the scalar
  field.
* `quotientMaximalIdealEquiv`: The quotient by the unique maximal ideal is canonically the scalar
  field.
* `equivScalarOfSubsingleton`: Analytic germs on a zero-dimensional domain form exactly the scalar
  field.

## Main results

* `isUnit_iff`: An analytic germ is invertible exactly when its value at the base point is nonzero.
* `maximalIdeal_eq_ker_eval`: Evaluation has the unique maximal ideal as its kernel.
* `pullback_comp`: Pullbacks compose in the reverse order to their analytic maps.
* `eval_surjective`: Evaluation onto the scalar field is surjective.

## References

* [P. Jakóbczak and M. Jarnicki, *Lectures on Holomorphic Functions of Several Complex
  Variables*][JakobczakJarnicki2021]
* [T. Suwa, *Complex Analytic Geometry: From the Localization Viewpoint*][Suwa2024]
-/

public noncomputable section

open Filter Set Metric
open scoped Topology

namespace SeveralComplexVariables

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable (𝕜) in

/-- The subring of germs admitting a representative analytic at the base point. -/
@[expose] def analyticGermSubring (x : E) : Subring (Germ (𝓝 x) 𝕜) where
  carrier := {φ | ∃ f : E → 𝕜, AnalyticAt 𝕜 f x ∧ (f : Germ (𝓝 x) 𝕜) = φ}
  zero_mem' := ⟨0, analyticAt_const, rfl⟩
  one_mem' := ⟨1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, rfl⟩

/-- Membership of a represented germ is exactly analyticity of that representative. -/
@[simp] theorem mem_analyticGermSubring {x : E} {f : E → 𝕜} :
    (f : Germ (𝓝 x) 𝕜) ∈ analyticGermSubring 𝕜 x ↔ AnalyticAt 𝕜 f x := by
  constructor
  · rintro ⟨g, hg, heq⟩
    exact hg.congr (Germ.coe_eq.mp heq)
  · intro hf
    exact ⟨f, hf, rfl⟩

variable (𝕜) in
/-- Scalar analytic germs at `x` over the field `𝕜`, with the ring operations inherited from
Mathlib germs. -/
abbrev AnalyticGerm (x : E) : Type _ := ↥(analyticGermSubring 𝕜 x)

namespace AnalyticGerm

variable {x : E}

/-- The germ of a function analytic at the base point. -/
@[expose] def ofAnalyticAt (f : E → 𝕜) (hf : AnalyticAt 𝕜 f x) : AnalyticGerm 𝕜 x :=
  ⟨f, f, hf, rfl⟩

/-- Every analytic germ has an analytic representative. -/
theorem exists_rep (φ : AnalyticGerm 𝕜 x) :
    ∃ (f : E → 𝕜) (hf : AnalyticAt 𝕜 f x), ofAnalyticAt f hf = φ := by
  obtain ⟨f, hf, heq⟩ := φ.property
  exact ⟨f, hf, Subtype.ext heq⟩

/-- Two analytic representatives define the same germ exactly when they agree nearby. -/
@[simp] theorem ofAnalyticAt_eq_iff {f g : E → 𝕜}
    {hf : AnalyticAt 𝕜 f x} {hg : AnalyticAt 𝕜 g x} :
    ofAnalyticAt f hf = ofAnalyticAt g hg ↔ f =ᶠ[𝓝 x] g := by
  rw [Subtype.ext_iff]
  exact Germ.coe_eq

/-- The zero germ is represented by the zero function. -/
theorem ofAnalyticAt_zero :
    ofAnalyticAt (0 : E → 𝕜) analyticAt_const = (0 : AnalyticGerm 𝕜 x) := rfl

/-- Sums of analytic representatives compute sums of germs. -/
theorem ofAnalyticAt_add (f g : E → 𝕜) (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) :
    ofAnalyticAt (f + g) (hf.add hg) = ofAnalyticAt f hf + ofAnalyticAt g hg := rfl

/-- Products of analytic representatives compute products of germs. -/
theorem ofAnalyticAt_mul (f g : E → 𝕜) (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) :
    ofAnalyticAt (f * g) (hf.mul hg) = ofAnalyticAt f hf * ofAnalyticAt g hg := rfl

/-- Powers of analytic representatives compute powers of germs. -/
theorem ofAnalyticAt_pow (f : E → 𝕜) (hf : AnalyticAt 𝕜 f x) (n : ℕ) :
    ofAnalyticAt (f ^ n) (hf.pow n) = ofAnalyticAt f hf ^ n := rfl

/-- Finite sums of analytic representatives compute finite sums of germs. -/
theorem ofAnalyticAt_sum {κ : Type*} (s : Finset κ) (f : κ → E → 𝕜)
    (hf : ∀ i, AnalyticAt 𝕜 (f i) x) (hs : AnalyticAt 𝕜 (∑ i ∈ s, f i) x) :
    ofAnalyticAt (∑ i ∈ s, f i) hs = ∑ i ∈ s, ofAnalyticAt (f i) (hf i) := by
  apply Subtype.ext
  show ((∑ i ∈ s, f i : E → 𝕜) : Germ (𝓝 x) 𝕜) =
      ((∑ i ∈ s, ofAnalyticAt (f i) (hf i) : AnalyticGerm 𝕜 x) : Germ (𝓝 x) 𝕜)
  rw [AddSubmonoidClass.coe_finsetSum]
  exact map_sum (Filter.Germ.coeRingHom (𝓝 x)) f s

/-- Evaluation of an analytic germ at its base point, as a ring homomorphism. -/
@[expose] def eval (x : E) : AnalyticGerm 𝕜 x →+* 𝕜 :=
  Germ.valueRingHom.comp (analyticGermSubring 𝕜 x).subtype

/-- Evaluation of a represented germ is evaluation of its representative. -/
@[simp] theorem eval_ofAnalyticAt (f : E → 𝕜) (hf : AnalyticAt 𝕜 f x) :
    eval x (ofAnalyticAt f hf) = f x := rfl

/-- Constant functions define a ring homomorphism into analytic germs. -/
@[expose] def const (x : E) : 𝕜 →+* AnalyticGerm 𝕜 x where
  toFun c := ofAnalyticAt (fun _ => c) analyticAt_const
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- Analytic germs form a `𝕜`-algebra via constant germs. -/
instance : Algebra 𝕜 (AnalyticGerm 𝕜 x) := (const x).toAlgebra

/-- Evaluation of a constant germ recovers its constant value. -/
@[simp] theorem eval_const (c : 𝕜) : eval x (const x c) = c := rfl

/-- Evaluation onto the scalar field is surjective. -/
theorem eval_surjective (x : E) : Function.Surjective (eval (𝕜 := 𝕜) x) :=
  fun c => ⟨const x c, rfl⟩

/-- Evaluation also preserves the `𝕜`-algebra structure. -/
def evalAlgHom (x : E) : AnalyticGerm 𝕜 x →ₐ[𝕜] 𝕜 where
  __ := eval x
  commutes' _ := rfl

section Pullback

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Composition with an analytic map pulls scalar germs back as a `𝕜`-algebra homomorphism.
Mathlib's `compTendsto` makes the construction independent of representatives. -/
@[expose] def pullback (f : E → F) (hf : AnalyticAt 𝕜 f x) :
    AnalyticGerm 𝕜 (f x) →ₐ[𝕜] AnalyticGerm 𝕜 x where
  toFun φ := ⟨φ.val.compTendsto f hf.continuousAt, by
    obtain ⟨g, hg, heq⟩ := φ.property
    refine ⟨g ∘ f, hg.comp hf, ?_⟩
    rw [← heq]
    rfl⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' a b := by
    obtain ⟨g, hg, rfl⟩ := exists_rep a
    obtain ⟨h, hh, rfl⟩ := exists_rep b
    rfl
  map_mul' a b := by
    obtain ⟨g, hg, rfl⟩ := exists_rep a
    obtain ⟨h, hh, rfl⟩ := exists_rep b
    rfl
  commutes' _ := rfl

/-- Pullback of a represented germ is represented by composition. -/
@[simp] theorem pullback_ofAnalyticAt (f : E → F) (hf : AnalyticAt 𝕜 f x)
    (g : F → 𝕜) (hg : AnalyticAt 𝕜 g (f x)) :
    pullback f hf (ofAnalyticAt g hg) = ofAnalyticAt (g ∘ f) (hg.comp hf) := rfl

/-- Pullback along a map whose value at the source point is only known up to a stated equation,
letting the target germ's base point be phrased as any value equal to `f x`. Matches `pullback`
definitionally once the equation is substituted. -/
def pullbackOfEq (f : E → F) (hf : AnalyticAt 𝕜 f x) {y : F} (hy : f x = y) :
    AnalyticGerm 𝕜 y →ₐ[𝕜] AnalyticGerm 𝕜 x :=
  hy ▸ pullback f hf

/-- Pullback along an equation-adjusted map of a represented germ is represented by composition. -/
@[simp] theorem pullbackOfEq_ofAnalyticAt (f : E → F) (hf : AnalyticAt 𝕜 f x) {y : F}
    (hy : f x = y) (g : F → 𝕜) (hg : AnalyticAt 𝕜 g y) :
    pullbackOfEq f hf hy (ofAnalyticAt g hg) = ofAnalyticAt (g ∘ f) (hg.comp_of_eq hf hy) := by
  subst hy
  rfl

/-- Evaluation commutes with pullback at the corresponding base points. -/
@[simp] theorem eval_pullback (f : E → F) (hf : AnalyticAt 𝕜 f x)
    (φ : AnalyticGerm 𝕜 (f x)) : eval x (pullback f hf φ) = eval (f x) φ := by
  obtain ⟨g, hg, rfl⟩ := exists_rep φ
  rfl

/-- Pullback by the identity fixes every analytic germ. -/
@[simp] theorem pullback_id (φ : AnalyticGerm 𝕜 x) :
    pullback id analyticAt_id φ = φ := by
  obtain ⟨f, hf, rfl⟩ := exists_rep φ
  rfl

/-- Pullbacks compose in the reverse order to their analytic maps. -/
theorem pullback_comp (f : E → F) (hf : AnalyticAt 𝕜 f x)
    (g : F → G) (hg : AnalyticAt 𝕜 g (f x)) (φ : AnalyticGerm 𝕜 (g (f x))) :
    pullback (g ∘ f) (hg.comp hf) φ = pullback f hf (pullback g hg φ) := by
  obtain ⟨h, hh, rfl⟩ := exists_rep φ
  rfl

end Pullback

/-- An analytic germ is invertible exactly when its value at the base point is nonzero. -/
theorem isUnit_iff (φ : AnalyticGerm 𝕜 x) : IsUnit φ ↔ eval x φ ≠ 0 := by
  constructor
  · intro h
    exact (h.map (eval x)).ne_zero
  · obtain ⟨f, hf, rfl⟩ := exists_rep φ
    intro h
    have hne : f x ≠ 0 := h
    let ψ := ofAnalyticAt (fun y => (f y)⁻¹) (hf.inv hne)
    have hmul : ofAnalyticAt f hf * ψ = 1 := by
      apply Subtype.ext
      apply Germ.coe_eq.mpr
      filter_upwards [hf.continuousAt.eventually_ne hne] with y hy
      exact mul_inv_cancel₀ hy
    exact ⟨⟨ofAnalyticAt f hf, ψ, hmul, by rwa [mul_comm]⟩, rfl⟩

/-- Pullback preserves and reflects units, as required of a homomorphism of local rings. -/
theorem isUnit_pullback_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E → F) (hf : AnalyticAt 𝕜 f x) (φ : AnalyticGerm 𝕜 (f x)) :
    IsUnit (pullback f hf φ) ↔ IsUnit φ := by
  simp only [isUnit_iff, eval_pullback]

/-- The ring of analytic germs is local. -/
instance : IsLocalRing (AnalyticGerm 𝕜 x) where
  isUnit_or_isUnit_of_add_one {a b} h := by
    rw [isUnit_iff, isUnit_iff]
    by_cases ha : eval x a = 0
    · right
      have hv := congrArg (eval x) h
      have hb : eval x b = 1 := by simpa [ha] using hv
      rw [hb]
      exact one_ne_zero
    · exact Or.inl ha

/-- The unique maximal ideal consists precisely of germs vanishing at the base point. -/
@[simp] theorem mem_maximalIdeal_iff (φ : AnalyticGerm 𝕜 x) :
    φ ∈ IsLocalRing.maximalIdeal (AnalyticGerm 𝕜 x) ↔ eval x φ = 0 := by
  simp [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff]

/-- Evaluation has the unique maximal ideal as its kernel. -/
theorem maximalIdeal_eq_ker_eval (x : E) :
    IsLocalRing.maximalIdeal (AnalyticGerm 𝕜 x) = RingHom.ker (eval (𝕜 := 𝕜) x) := by
  ext φ
  exact mem_maximalIdeal_iff φ

variable (𝕜) in
/-- Quotienting analytic germs by the evaluation kernel gives the scalar field. -/
def quotientKerEvalEquiv (x : E) :
    AnalyticGerm 𝕜 x ⧸ RingHom.ker (eval (𝕜 := 𝕜) x) ≃+* 𝕜 :=
  (eval (𝕜 := 𝕜) x).quotientKerEquivOfSurjective (eval_surjective x)

variable (𝕜) in
/-- The quotient by the unique maximal ideal is canonically the scalar field. -/
def quotientMaximalIdealEquiv (x : E) :
    AnalyticGerm 𝕜 x ⧸ IsLocalRing.maximalIdeal (AnalyticGerm 𝕜 x) ≃+* 𝕜 :=
  (Ideal.quotEquivOfEq (maximalIdeal_eq_ker_eval x)).trans (quotientKerEvalEquiv 𝕜 x)

/-- In dimension zero, every analytic germ is the constant germ of its value. -/
theorem const_eval_of_subsingleton [Subsingleton E] (φ : AnalyticGerm 𝕜 x) :
    const x (eval x φ) = φ := by
  obtain ⟨f, hf, rfl⟩ := exists_rep φ
  apply Subtype.ext
  apply Germ.coe_eq.mpr
  exact Eventually.of_forall fun y => congrArg f (Subsingleton.elim x y)

variable (𝕜) in
/-- Analytic germs on a zero-dimensional domain form exactly the scalar field. -/
def equivScalarOfSubsingleton [Subsingleton E] (x : E) : AnalyticGerm 𝕜 x ≃+* 𝕜 :=
  RingEquiv.ofBijective (eval x) ⟨fun a b h => by
    rw [← const_eval_of_subsingleton a, ← const_eval_of_subsingleton b, h],
    eval_surjective x⟩

section RCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {x : E}

/-- Analytic germs over `ℝ` or `ℂ` have no zero divisors, by the analytic identity principle on
connected balls. -/
instance : NoZeroDivisors (AnalyticGerm 𝕜 x) where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} hab := by
    obtain ⟨f, hf, rfl⟩ := exists_rep a
    obtain ⟨g, hg, rfl⟩ := exists_rep b
    have hfg : (fun y => f y * g y) =ᶠ[𝓝 x] 0 :=
      Germ.coe_eq.mp (congrArg Subtype.val hab)
    rcases eventuallyEq_zero_or_eventuallyEq_zero_of_mul hf hg hfg with h | h
    · exact Or.inl (Subtype.ext (Germ.coe_eq.mpr h))
    · exact Or.inr (Subtype.ext (Germ.coe_eq.mpr h))

/-- The ring of scalar analytic germs over `ℝ` or `ℂ` is an integral domain. -/
instance : IsDomain (AnalyticGerm 𝕜 x) := NoZeroDivisors.to_isDomain _

end RCLike

end AnalyticGerm
end SeveralComplexVariables


/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
