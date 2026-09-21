/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Unitary equivalence of bounded operators

Two bounded operators on possibly different Hilbert spaces over a common `RCLike` scalar field
are **unitarily equivalent** when some linear isometric equivalence intertwines them.

The relation is already spelled out at several places in the Davis--Kahan development; it is
introduced here so that the *chain* of equivalences produced by the multiplicity construction --
operator, cyclic model, slice model, normal form -- can be composed by `trans` instead of by
hand.  The definition is literally the same existential as
`TauCeti.DavisKahan.BoundedOperatorsUnitaryEquivalent`, so the two unfold
to each other.

The intertwining is stated **pointwise**.  Writing it as a composition of continuous linear maps
would force the equivalence through `LinearMap.toContinuousLinearMap`, which carries a
finite-dimensionality hypothesis that none of the source statements have.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib.
-/

public section

namespace TauCeti

universe u v w

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
variable {L : Type w} [NormedAddCommGroup L] [InnerProductSpace 𝕜 L]

/-- **Unitary equivalence of bounded operators** on possibly different Hilbert spaces over the
same `RCLike` scalar field.

Exposed, because consumers outside this module need to see that it is the same existential as
the Davis--Kahan development's own `BoundedOperatorsUnitaryEquivalent`. -/
def OperatorUnitaryEquiv (A : H →L[𝕜] H) (B : K →L[𝕜] K) : Prop :=
  ∃ e : H ≃ₗᵢ[𝕜] K, ∀ x : H, e (A x) = B (e x)

/-- A linear isometric equivalence that intertwines two operators exhibits their unitary
equivalence.  This is the introduction rule; it exists so that call sites never write the
anonymous constructor and can be read at a glance. -/
theorem operatorUnitaryEquiv_of_intertwines {A : H →L[𝕜] H} {B : K →L[𝕜] K} (e : H ≃ₗᵢ[𝕜] K)
    (he : ∀ x : H, e (A x) = B (e x)) : OperatorUnitaryEquiv A B :=
  ⟨e, he⟩

/-- The elimination rule, dual to `operatorUnitaryEquiv_of_intertwines`.  It exists so that
consumers outside this module can destructure the relation without the definition having to be
exposed. -/
theorem OperatorUnitaryEquiv.exists_intertwiner {A : H →L[𝕜] H} {B : K →L[𝕜] K}
    (h : OperatorUnitaryEquiv A B) : ∃ e : H ≃ₗᵢ[𝕜] K, ∀ x : H, e (A x) = B (e x) :=
  h

/-- Unitary equivalence is reflexive, witnessed by the identity. -/
@[refl]
theorem OperatorUnitaryEquiv.refl (A : H →L[𝕜] H) : OperatorUnitaryEquiv A A :=
  ⟨LinearIsometryEquiv.refl 𝕜 H, fun _ => rfl⟩

/-- Unitary equivalence is symmetric: the inverse of the intertwining unitary intertwines the
operators the other way. -/
@[symm]
theorem OperatorUnitaryEquiv.symm {A : H →L[𝕜] H} {B : K →L[𝕜] K}
    (h : OperatorUnitaryEquiv A B) : OperatorUnitaryEquiv B A := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, fun y => ?_⟩
  have hy := he (e.symm y)
  rw [e.apply_symm_apply] at hy
  rw [← hy, e.symm_apply_apply]

/-- Unitary equivalence is transitive.  This is what lets the chain of equivalences produced by
the multiplicity construction be composed one step at a time. -/
theorem OperatorUnitaryEquiv.trans {A : H →L[𝕜] H} {B : K →L[𝕜] K} {C : L →L[𝕜] L}
    (h : OperatorUnitaryEquiv A B) (h' : OperatorUnitaryEquiv B C) :
    OperatorUnitaryEquiv A C := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  refine ⟨e.trans e', fun x => ?_⟩
  simp only [LinearIsometryEquiv.trans_apply]
  rw [he x, he' (e x)]

/-! ### Remembering a structure map

`OperatorUnitaryEquiv` **forgets** its unitary, which is exactly what makes it composable and
exactly what makes it useless for descent: a chain of unitary equivalences says nothing about
whether any one witness respects a conjugation.  The refinement below carries the extra
commutation as part of the existential, so that the *whole chain* can be assembled and only then
restricted to the fixed points of the structure maps.

The structure maps are bare functions with no hypotheses at all.  Every downstream consumer
instantiates them at `star` on an `L²` space or at the canonical conjugation on a
complexification, and the only facts about them the chaining rules use are that they are
functions -- so demanding `StarAddMonoid`, conjugate-linearity or involutivity here would be
hypotheses that no step of the argument spends. -/

section StarEquivariant

/-- **Unitary equivalence by a unitary that additionally intertwines two given structure maps.**

`cH` and `cK` are unconstrained; at every call site they are pointwise conjugation.  The relation
refines `OperatorUnitaryEquiv` (`StarOperatorUnitaryEquiv.toOperatorUnitaryEquiv`) and is
transitive in `cH`, `cK` simultaneously, which is what lets a descent argument be run once at the
end of a chain rather than at each link. -/
def StarOperatorUnitaryEquiv (cH : H → H) (cK : K → K) (A : H →L[𝕜] H) (B : K →L[𝕜] K) : Prop :=
  ∃ e : H ≃ₗᵢ[𝕜] K, (∀ x : H, e (A x) = B (e x)) ∧ ∀ x : H, e (cH x) = cK (e x)

/-- The introduction rule. -/
theorem starOperatorUnitaryEquiv_of_intertwines {cH : H → H} {cK : K → K} {A : H →L[𝕜] H}
    {B : K →L[𝕜] K} (e : H ≃ₗᵢ[𝕜] K) (he : ∀ x : H, e (A x) = B (e x))
    (hc : ∀ x : H, e (cH x) = cK (e x)) : StarOperatorUnitaryEquiv cH cK A B :=
  ⟨e, he, hc⟩

/-- The elimination rule. -/
theorem StarOperatorUnitaryEquiv.exists_intertwiner {cH : H → H} {cK : K → K} {A : H →L[𝕜] H}
    {B : K →L[𝕜] K} (h : StarOperatorUnitaryEquiv cH cK A B) :
    ∃ e : H ≃ₗᵢ[𝕜] K, (∀ x : H, e (A x) = B (e x)) ∧ ∀ x : H, e (cH x) = cK (e x) :=
  h

/-- Forgetting the structure maps recovers plain unitary equivalence. -/
theorem StarOperatorUnitaryEquiv.toOperatorUnitaryEquiv {cH : H → H} {cK : K → K}
    {A : H →L[𝕜] H} {B : K →L[𝕜] K} (h : StarOperatorUnitaryEquiv cH cK A B) :
    OperatorUnitaryEquiv A B :=
  ⟨h.choose, h.choose_spec.1⟩

/-- Reflexivity, witnessed by the identity -- for **any** structure map, since the identity
intertwines everything with itself. -/
@[refl]
theorem StarOperatorUnitaryEquiv.refl (c : H → H) (A : H →L[𝕜] H) :
    StarOperatorUnitaryEquiv c c A A :=
  ⟨LinearIsometryEquiv.refl 𝕜 H, fun _ => rfl, fun _ => rfl⟩

/-- Symmetry.  Note that the structure maps are **not** assumed involutive: the inverse unitary
intertwines them the other way for the same reason it intertwines the operators, namely because
`e` is a bijection. -/
@[symm]
theorem StarOperatorUnitaryEquiv.symm {cH : H → H} {cK : K → K} {A : H →L[𝕜] H} {B : K →L[𝕜] K}
    (h : StarOperatorUnitaryEquiv cH cK A B) : StarOperatorUnitaryEquiv cK cH B A := by
  obtain ⟨e, he, hc⟩ := h
  refine ⟨e.symm, fun y => ?_, fun y => ?_⟩
  · have hy := he (e.symm y)
    rw [e.apply_symm_apply] at hy
    rw [← hy, e.symm_apply_apply]
  · have hy := hc (e.symm y)
    rw [e.apply_symm_apply] at hy
    rw [← hy, e.symm_apply_apply]

/-- Transitivity, in the operators and the structure maps at once. -/
theorem StarOperatorUnitaryEquiv.trans {cH : H → H} {cK : K → K} {cL : L → L} {A : H →L[𝕜] H}
    {B : K →L[𝕜] K} {C : L →L[𝕜] L} (h : StarOperatorUnitaryEquiv cH cK A B)
    (h' : StarOperatorUnitaryEquiv cK cL B C) : StarOperatorUnitaryEquiv cH cL A C := by
  obtain ⟨e, he, hc⟩ := h
  obtain ⟨e', he', hc'⟩ := h'
  refine ⟨e.trans e', fun x => ?_, fun x => ?_⟩
  · simp only [LinearIsometryEquiv.trans_apply]
    rw [he x, he' (e x)]
  · simp only [LinearIsometryEquiv.trans_apply]
    rw [hc x, hc' (e x)]

end StarEquivariant

section RealDescent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Descent of a `star`-equivariant unitary equivalence to the real forms.**

`E` and `F` are presented as *real forms* of `H` and `K`: an `ℝ`-linear isometry `jE` landing in
the fixed set of `cH`, together with a retraction `rE` that inverts it there.  Nothing is assumed
about `cH` and `cK` themselves -- not conjugate-linearity, not involutivity -- because the proof
only ever uses `hfixE`, `hrjE` and their `F`-counterparts.

**This is where the equivariance is spent, and it is why `TauCeti.OperatorUnitaryEquiv` alone
cannot do it.**  A unitary intertwining `A` and `B` is unique only up to the commutant of `A`, so
an arbitrary witness has no reason to carry `cH` to `cK` and therefore no reason to restrict to
the real forms at all.  The witness has to be *chosen* equivariantly upstream and carried down,
which is exactly what `TauCeti.StarOperatorUnitaryEquiv` records.

The descended unitary is `x ↦ rF (e (jE x))`, and it is built by `LinearIsometryEquiv.ofSurjective`
from the identity `jF (Φ x) = e (jE x)`: every algebraic property of `Φ` is read off from that
identity by cancelling the injective `jF`, which avoids ever needing `rF` to be additive.

The inclusions are taken **unbundled**, with additivity, homogeneity and norm preservation as
separate hypotheses, rather than as `→ₗᵢ[ℝ]`.  That is not stylistic.  A complex space carries
two `Module ℝ` structures -- its own, and the one restricted from `ℂ` -- and on the
`RealComplexification` of this development they are **not** definitionally equal (their agreement
is the theorem `coe_real_smul`).  A bundled `→ₗᵢ[ℝ]` argument therefore pins one of them and
rejects call sites that carry the other.  Homogeneity is consequently stated with the scalar
*coerced into `ℂ`*, which mentions only the complex action and so is unambiguous on both
sides. -/
theorem operatorUnitaryEquiv_of_starOperatorUnitaryEquiv {cH : H → H} {cK : K → K}
    {A : H →L[ℂ] H} {B : K →L[ℂ] K} {T : E →L[ℝ] E} {S : F →L[ℝ] F} (jE : E → H) (rE : H → E)
    (hjEadd : ∀ x y, jE (x + y) = jE x + jE y)
    (hjEsmul : ∀ (c : ℝ) x, jE (c • x) = (c : ℂ) • jE x)
    (hjEnorm : ∀ x, ‖jE x‖ = ‖x‖) (hfixE : ∀ x, cH (jE x) = jE x)
    (hrjE : ∀ y, cH y = y → jE (rE y) = y) (hT : ∀ x, A (jE x) = jE (T x)) (jF : F → K)
    (rF : K → F) (hjFadd : ∀ x y, jF (x + y) = jF x + jF y)
    (hjFsmul : ∀ (c : ℝ) x, jF (c • x) = (c : ℂ) • jF x) (hjFnorm : ∀ x, ‖jF x‖ = ‖x‖)
    (hfixF : ∀ x, cK (jF x) = jF x) (hrjF : ∀ y, cK y = y → jF (rF y) = y)
    (hS : ∀ x, B (jF x) = jF (S x)) (h : StarOperatorUnitaryEquiv cH cK A B) :
    OperatorUnitaryEquiv T S := by
  classical
  obtain ⟨e, hAB, hc⟩ := h
  have hjFsub : ∀ x y, jF (x - y) = jF x - jF y := by
    intro x y
    have hxy := hjFadd (x - y) y
    rw [sub_add_cancel] at hxy
    exact eq_sub_of_add_eq hxy.symm
  have hinj : Function.Injective jF := by
    intro x y hxy
    have hz : ‖x - y‖ = 0 := by rw [← hjFnorm (x - y), hjFsub, hxy, sub_self, norm_zero]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  have hfix : ∀ x : E, cK (e (jE x)) = e (jE x) := by
    intro x
    rw [← hc, hfixE]
  set Φ : E → F := fun x => rF (e (jE x))
  have hjΦ : ∀ x, jF (Φ x) = e (jE x) := fun x => hrjF _ (hfix x)
  have hadd : ∀ x y, Φ (x + y) = Φ x + Φ y := by
    intro x y
    refine hinj ?_
    rw [hjΦ, hjEadd, map_add, hjFadd, hjΦ, hjΦ]
  have hsmul : ∀ (c : ℝ) (x : E), Φ (c • x) = c • Φ x := by
    intro c x
    refine hinj ?_
    rw [hjΦ, hjEsmul, map_smul, hjFsmul, hjΦ]
  have hnorm : ∀ x, ‖Φ x‖ = ‖x‖ := by
    intro x
    rw [← hjFnorm (Φ x), hjΦ, e.norm_map, hjEnorm]
  set Φₗᵢ : E →ₗᵢ[ℝ] F := ⟨⟨⟨Φ, hadd⟩, hsmul⟩, hnorm⟩
  have hsurj : Function.Surjective Φₗᵢ := by
    intro y
    refine ⟨rE (e.symm (jF y)), ?_⟩
    have hy : cH (e.symm (jF y)) = e.symm (jF y) := by
      refine e.injective ?_
      rw [hc, e.apply_symm_apply]
      exact hfixF y
    refine hinj ?_
    change jF (Φ (rE (e.symm (jF y)))) = jF y
    rw [hjΦ, hrjE _ hy, e.apply_symm_apply]
  refine operatorUnitaryEquiv_of_intertwines (LinearIsometryEquiv.ofSurjective Φₗᵢ hsurj)
    fun x => ?_
  simp only [LinearIsometryEquiv.coe_ofSurjective]
  refine hinj ?_
  change jF (Φ (T x)) = jF (S (Φ x))
  rw [hjΦ, ← hT, hAB, ← hjΦ, hS]

end RealDescent

end TauCeti
