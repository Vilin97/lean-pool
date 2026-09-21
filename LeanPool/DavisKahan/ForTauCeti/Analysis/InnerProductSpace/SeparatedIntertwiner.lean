/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import LeanPool.DavisKahan.ForTauCeti.Analysis.RCLike.ScalarTransportFunctionalCalculus
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjointResolvent
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Algebra.Star.Unitary

/-!
# Intertwiners of spectrally separated operators

An `X` intertwining two partial maps intertwines everything built from them:
first their resolvents, and from there their spectral projections, so that
disjoint spectra force `X = 0`.

This replaces the donor constant
`generatorIntertwiner_eq_zero_of_disjoint_spectrum`.

## Status

This module carries the intertwining chain up to and including the **continuous**
functional calculus:

1. `resolvent_intertwines` — needs nothing beyond the definition of `resolventSet`;
2. `cayley_intertwines` — immediate at `z = -i`;
3. `cfcHom_intertwines` / `cfcHom_cayley_intertwines` — Stone--Weierstrass.

What remains for a **general bounded** intertwiner is the **Borel** step:
upgrading `cfcHom_cayley_intertwines` to `BorelCalculus.borelCalculus`, and from
there to `specProjection`.  That is a monotone-class argument on the sesquilinear
`pair` form defining `borelCalculus`, i.e. it must be run through the diagonal
measures rather than the operators.

For a **unitary** intertwiner the Borel step is done, because the diagonal
measures themselves transport: see
`LinearPMap.specProjection_apply_of_unitary_intertwines`, built on
`BorelCalculus.borelCalculus_comp_val_of_intertwines`.  That covers the
reducing-subspace case, a subspace reducing `A` being exactly a subspace whose
reflection is a unitary commuting with `A`.

Once `specProjection` intertwining exists for a general bounded `X` the endgame
is short: for disjoint closed spectra pick a Borel `B ⊇ σ(A)` missing `σ(B)`, and
`X = E_A(B) X = X E_B(B) = 0` by
`specProjection_eq_zero_of_subset_resolventSet`.

## Provenance

* Replaces `vendor/Spectra/Spectra/SpectralTheory/SeparatedIntertwiner.lean`.
  Proved natively rather than relocated: the donor's route runs through
  `borelMeasure` and the Born-rule support estimate, spanning 44 Spectra files,
  none of which `ForTauCeti` may import.
* Spectra influence: none.
-/

public section

namespace TauCeti
namespace LinearPMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **An intertwiner intertwines the resolvents.**

If `X` carries `B` to `A` — `A (X y) = X (B y)` on `dom B` — and `z` is a
resolvent point of both, then `X R_B = R_A X`.

Only the two defining properties of a resolvent are used: that `R_A` inverts
`z • I - A` on the domain, and that `R_B` lands in `dom B` and inverts
`z • I - B` there.  Neither self-adjointness nor closedness is needed. -/
theorem resolvent_intertwines
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F} {X : F →L[𝕜] E} {z : 𝕜}
    {RA : E →L[𝕜] E} {RB : F →L[𝕜] F}
    (hRA : ∀ ψ : A.domain, RA (z • (ψ : E) - A ψ) = (ψ : E))
    (hRB : ∀ φ : F, ∃ h : RB φ ∈ B.domain, z • RB φ - B ⟨RB φ, h⟩ = φ)
    (hmaps : ∀ y : B.domain, X (y : F) ∈ A.domain)
    (hint : ∀ y : B.domain, A ⟨X (y : F), hmaps y⟩ = X (B y)) :
    X ∘L RB = RA ∘L X := by
  refine ContinuousLinearMap.ext fun φ => ?_
  obtain ⟨hmem, hBinv⟩ := hRB φ
  -- Push `X` through `z • RB φ - B ⟨RB φ⟩ = φ` and rewrite with the
  -- intertwining relation, turning it into a statement about `A`.
  have hXpush : z • X (RB φ) - A ⟨X (RB φ), hmaps ⟨RB φ, hmem⟩⟩ = X φ := by
    have := congrArg X hBinv
    rw [map_sub, map_smul] at this
    rw [hint ⟨RB φ, hmem⟩]
    exact this
  -- `RA` inverts `A - z` at that domain vector, which is exactly the claim.
  have := hRA ⟨X (RB φ), hmaps ⟨RB φ, hmem⟩⟩
  rw [hXpush] at this
  simpa using this.symm

/-- `resolvent`-specialised form of `resolvent_intertwines`. -/
theorem resolvent_intertwines' {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {X : F →L[𝕜] E} {z : 𝕜}
    (hzA : z ∈ resolventSet A) (hzB : z ∈ resolventSet B)
    (hmaps : ∀ y : B.domain, X (y : F) ∈ A.domain)
    (hint : ∀ y : B.domain, A ⟨X (y : F), hmaps y⟩ = X (B y)) :
    X ∘L resolvent B z = resolvent A z ∘L X :=
  resolvent_intertwines (fun ψ => resolvent_smul_sub_apply hzA ψ)
    (fun φ => ⟨resolvent_mem_domain hzB φ, smul_sub_apply_resolvent hzB φ⟩) hmaps hint

/-- Restriction of a continuous symbol along an inclusion of compact spectral sets.

This is scalar-generic: both the complex normal calculus and the real self-adjoint
calculus need the same common-domain adapter when two operators have different
spectra. -/
@[expose]
noncomputable def symbolRestrict {K s : Set 𝕜} (h : s ⊆ K) :
    C(K, 𝕜) →⋆ₐ[𝕜] C(s, 𝕜) :=
  ContinuousMap.compStarAlgHom' 𝕜 𝕜 ⟨Set.inclusion h, continuous_inclusion h⟩

/-- Restriction of continuous symbols is continuous. -/
theorem continuous_symbolRestrict {K s : Set 𝕜} (h : s ⊆ K) :
    Continuous (symbolRestrict h) :=
  ContinuousMap.continuous_precomp _

/-! ## The self-adjoint calculus, at `RCLike` scalars

The operator algebra uses `𝕜`, while the self-adjoint functional calculus uses real symbols.
The real algebra, scalar tower, and calculus are canonical for every complete Hilbert space over
an `RCLike` field and are activated locally below. -/

section SelfAdjoint

variable [CompleteSpace E] [CompleteSpace F]

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal
  ContinuousLinearMap.instStarOrderedRingRCLike

/-- **A rectangular intertwiner of self-adjoint operators intertwines their real
continuous functional calculi.**

This is the self-adjoint analogue of `cfcHom_intertwines`.  The operators are
`𝕜`-linear for an arbitrary `RCLike` field `𝕜`, but the functional-calculus
scalar is `ℝ`, so only the single generator `id` is mathematically needed; the
Stone--Weierstrass `star_id` case reduces to the same generator by
self-adjointness.

The theorem is deliberately stated on a common compact set `K`.  This is the
right reusable form for angle operators: `Θ₀` and `Θ₁` can have different real
spectra while both lie in the same interval, and an intertwiner
`X Θ₁ = Θ₀ X` then automatically intertwines every continuous real function of
the two angles, in particular `sin` and `cos`.  `cfc_intertwines_selfAdjoint`
is the form that picks `K` for the caller. -/
theorem cfcHom_intertwines_selfAdjoint
    {u : E →L[𝕜] E} {v : F →L[𝕜] F} (hu : IsSelfAdjoint u) (hv : IsSelfAdjoint v)
    {X : F →L[𝕜] E}
    (hint : X ∘L v = u ∘L X)
    {K : Set ℝ} (hK : IsCompact K)
    (huK : _root_.spectrum ℝ u ⊆ K) (hvK : _root_.spectrum ℝ v ⊆ K) (g : C(K, ℝ)) :
    X ∘L cfcHom hv (symbolRestrict hvK g)
      = cfcHom hu (symbolRestrict huK g) ∘L X := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  induction g using ContinuousMap.induction_on_of_compact with
  | const r =>
      have h1 : symbolRestrict hvK (ContinuousMap.const K r)
          = algebraMap ℝ (C(_root_.spectrum ℝ v, ℝ)) r := rfl
      have h2 : symbolRestrict huK (ContinuousMap.const K r)
          = algebraMap ℝ (C(_root_.spectrum ℝ u, ℝ)) r := rfl
      rw [h1, h2, AlgHomClass.commutes, AlgHomClass.commutes]
      -- The two `ℝ`-algebra maps are the `𝕜`-scalar `algebraMap ℝ 𝕜 r` acting on `1`,
      -- and `X` is `𝕜`-linear, so it passes that scalar.
      have hEr : (algebraMap ℝ (E →L[𝕜] E)) r = (algebraMap ℝ 𝕜 r) • (1 : E →L[𝕜] E) := by
        rw [Algebra.algebraMap_eq_smul_one, ← IsScalarTower.algebraMap_smul 𝕜]
      have hFr : (algebraMap ℝ (F →L[𝕜] F)) r = (algebraMap ℝ 𝕜 r) • (1 : F →L[𝕜] F) := by
        rw [Algebra.algebraMap_eq_smul_one, ← IsScalarTower.algebraMap_smul 𝕜]
      rw [hEr, hFr]
      ext y
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, smul_apply,
        one_apply_eq_self, map_smul]
  | id =>
      have h1 : symbolRestrict hvK (ContinuousMap.restrict K (ContinuousMap.id ℝ))
          = ContinuousMap.restrict _ (ContinuousMap.id ℝ) := rfl
      have h2 : symbolRestrict huK (ContinuousMap.restrict K (ContinuousMap.id ℝ))
          = ContinuousMap.restrict _ (ContinuousMap.id ℝ) := rfl
      rw [h1, h2, cfcHom_id, cfcHom_id]
      exact hint
  | star_id =>
      have h1 : symbolRestrict hvK (star (ContinuousMap.restrict K (ContinuousMap.id ℝ)))
          = star (ContinuousMap.restrict _ (ContinuousMap.id ℝ)) := rfl
      have h2 : symbolRestrict huK (star (ContinuousMap.restrict K (ContinuousMap.id ℝ)))
          = star (ContinuousMap.restrict _ (ContinuousMap.id ℝ)) := rfl
      rw [h1, h2, map_star, map_star, cfcHom_id, cfcHom_id, hv.star_eq, hu.star_eq]
      exact hint
  | add f g hf hg =>
      simp only [map_add, ContinuousLinearMap.comp_add,
        ContinuousLinearMap.add_comp, hf, hg]
  | mul f g hf hg =>
      rw [map_mul, map_mul, map_mul, map_mul]
      ext y
      exact (congrArg (fun T : F →L[𝕜] E => T (cfcHom hv (symbolRestrict hvK g) y)) hf
        |>.trans (congrArg
          (fun T : F →L[𝕜] E => cfcHom hu (symbolRestrict huK f) (T y)) hg))
  | frequently f hf =>
      have hc1 : Continuous
          (fun g : C(K, ℝ) => X ∘L cfcHom hv (symbolRestrict hvK g)) :=
        (ContinuousLinearMap.compL 𝕜 F F E X).continuous.comp
          ((cfcHom_continuous hv).comp (continuous_symbolRestrict hvK))
      have hc2 : Continuous
          (fun g : C(K, ℝ) => cfcHom hu (symbolRestrict huK g) ∘L X) :=
        ((ContinuousLinearMap.compL 𝕜 F E E).flip X).continuous.comp
          ((cfcHom_continuous hu).comp (continuous_symbolRestrict huK))
      rw [← Set.mem_ofPred (p := fun g : C(K, ℝ) =>
          X ∘L cfcHom hv (symbolRestrict hvK g)
            = cfcHom hu (symbolRestrict huK g) ∘L X),
        ← (isClosed_eq hc1 hc2).closure_eq]
      exact mem_closure_of_frequently_of_tendsto hf Filter.tendsto_id

/-- **An intertwiner of self-adjoint operators intertwines `cfc f` for every
symbol continuous on the union of the two spectra.**

The `cfc`-level form of `cfcHom_intertwines_selfAdjoint`, with the common
compact set chosen for the caller: `_root_.spectrum ℝ u ∪ _root_.spectrum ℝ v`
is compact because the functional-calculus instance itself asserts compactness
of each spectrum, so the section's hypotheses already supply it — no
`ProperSpace`, and no `NormedAlgebra ℝ (E →L[𝕜] E)` for `spectrum.isCompact`,
has to be added.

This is the form angle operators want.  For a globally continuous symbol,
supply `Continuous.continuousOn`. -/
theorem cfc_intertwines_selfAdjoint
    {u : E →L[𝕜] E} {v : F →L[𝕜] F} (hu : IsSelfAdjoint u) (hv : IsSelfAdjoint v)
    {X : F →L[𝕜] E}
    (hint : X ∘L v = u ∘L X) {f : ℝ → ℝ}
    (hf : ContinuousOn f (_root_.spectrum ℝ u ∪ _root_.spectrum ℝ v)) :
    X ∘L cfc f v = cfc f u ∘L X := by
  have hK : IsCompact (_root_.spectrum ℝ u ∪ _root_.spectrum ℝ v) :=
    (isCompact_iff_compactSpace.mpr
        (ContinuousFunctionalCalculus.compactSpace_spectrum (R := ℝ) (p := IsSelfAdjoint) u)).union
      (isCompact_iff_compactSpace.mpr
        (ContinuousFunctionalCalculus.compactSpace_spectrum (R := ℝ) (p := IsSelfAdjoint) v))
  have huK : _root_.spectrum ℝ u ⊆ _root_.spectrum ℝ u ∪ _root_.spectrum ℝ v :=
    Set.subset_union_left
  have hvK : _root_.spectrum ℝ v ⊆ _root_.spectrum ℝ u ∪ _root_.spectrum ℝ v :=
    Set.subset_union_right
  rw [cfc_apply f v hv (hf.mono hvK), cfc_apply f u hu (hf.mono huK)]
  exact cfcHom_intertwines_selfAdjoint hu hv hint hK huK hvK ⟨_, hf.domRestrict⟩


/-- **Continuous functional calculus acts pointwise on a genuine eigenvector.**

If a bounded self-adjoint operator satisfies `u x = λ x` with `x ≠ 0`, then
`f(u) x = f(λ) x` for every continuous real symbol `f`.  The proof is
infinite-dimensional: the normalized rank-one projection onto `𝕜 x`
intertwines `u` with the scalar operator `λ I`, so
`cfc_intertwines_selfAdjoint` transports the scalar functional calculus.

This is the bounded `RCLike` analogue of the finite-dimensional eigenbasis
calculus lemma, and is deliberately independent of any compactness or pure
point spectrum assumption. -/
theorem cfc_apply_of_apply_eq_real_smul
    {u : E →L[𝕜] E} (hu : IsSelfAdjoint u) {x : E} (hx0 : x ≠ 0)
    {lam : ℝ} (hx : u x = ((lam : ℝ) : 𝕜) • x)
    (f : ℝ → ℝ) (hf : Continuous f) :
    cfc f u x = ((f lam : ℝ) : 𝕜) • x := by
  let alpha : 𝕜 := (inner 𝕜 x x)⁻¹
  let X : E →L[𝕜] E := alpha • InnerProductSpace.rankOne 𝕜 x x
  let v : E →L[𝕜] E := algebraMap ℝ (E →L[𝕜] E) lam
  have hinner : inner 𝕜 x x ≠ 0 := by
    intro hzero
    exact hx0 (inner_self_eq_zero.mp hzero)
  have hXx : X x = x := by
    simp only [X, smul_apply, InnerProductSpace.rankOne_apply, smul_smul]
    rw [show alpha * inner 𝕜 x x = 1 from inv_mul_cancel₀ hinner]
    exact one_smul 𝕜 x
  have hv_eq : v = ((lam : ℝ) : 𝕜) • (1 : E →L[𝕜] E) := by
    dsimp [v]
    rw [Algebra.algebraMap_eq_smul_one, ← IsScalarTower.algebraMap_smul 𝕜]
  have hv_apply (y : E) : v y = ((lam : ℝ) : 𝕜) • y := by
    rw [hv_eq, smul_apply, one_apply_eq_self]
  have hvsa : IsSelfAdjoint v := by
    dsimp [v]
    exact cfc_predicate_algebraMap lam
  have hint : X ∘L v = u ∘L X := by
    ext y
    simp only [ContinuousLinearMap.comp_apply, hv_apply, X, smul_apply,
      InnerProductSpace.rankOne_apply, map_smul, hx, smul_smul]
    rw [mul_comm (((lam : ℝ) : 𝕜)) (alpha * inner 𝕜 x y)]
  have hinter := cfc_intertwines_selfAdjoint hu hvsa hint hf.continuousOn
  have hcfv : cfc f v = algebraMap ℝ (E →L[𝕜] E) (f lam) := by
    dsimp [v]
    rw [cfc_algebraMap]
  have hfv_eq : algebraMap ℝ (E →L[𝕜] E) (f lam) =
      ((f lam : ℝ) : 𝕜) • (1 : E →L[𝕜] E) := by
    rw [Algebra.algebraMap_eq_smul_one, ← IsScalarTower.algebraMap_smul 𝕜]
  have happ := congrArg (fun T : E →L[𝕜] E => T x) hinter
  simp only [ContinuousLinearMap.comp_apply, hcfv, hfv_eq, smul_apply,
    one_apply_eq_self, map_smul, hXx] at happ
  exact happ.symm

end SelfAdjoint

section Complex

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **An intertwiner intertwines the Cayley transforms.**

Immediate from `resolvent_intertwines'` at `z = -i`, since
`cayley hA = 1 + 2i • R_A(-i)`.  This is the step that carries the intertwining
into the bounded world, where the Borel calculus lives. -/
theorem cayley_intertwines {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) {X : F →L[ℂ] E}
    (hmaps : ∀ y : B.domain, X (y : F) ∈ A.domain)
    (hint : ∀ y : B.domain, A ⟨X (y : F), hmaps y⟩ = X (B y)) :
    X ∘L cayley hB = cayley hA ∘L X := by
  have hres := resolvent_intertwines' (A := A) (B := B) (X := X)
    (negI_mem_resolventSet hA) (negI_mem_resolventSet hB) hmaps hint
  refine ContinuousLinearMap.ext fun φ => ?_
  have hr := congrArg (fun T : F →L[ℂ] E => T φ) hres
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply] at hr
  simp only [cayley, ContinuousLinearMap.coe_comp, Function.comp_apply,
    add_apply, one_apply_eq_self, smul_apply, map_add, map_smul, hr]

/-- **An intertwiner intertwines the continuous functional calculi.**

If `X v = u X` and `X v⋆ = u⋆ X` for star-normal `u`, `v`, then `X` intertwines
`g u` and `g v` for every continuous symbol `g`.

The symbol is taken on a *common* compact `K` containing both spectra and
restricted to each: `cfcHom hu` and `cfcHom hv` eat functions on `_root_.spectrum ℂ u`
and `_root_.spectrum ℂ v` respectively, which are different spaces, so there is no
common domain on which to state the conclusion otherwise.

The proof is Stone--Weierstrass, via `ContinuousMap.induction_on_of_compact`:
the claim holds for constants and for `id`/`star id` (the two hypotheses), is
preserved by `+` and `*`, and defines a closed set of symbols. -/
theorem cfcHom_intertwines
    {u : E →L[ℂ] E} {v : F →L[ℂ] F} (hu : IsStarNormal u) (hv : IsStarNormal v)
    {X : F →L[ℂ] E}
    (hint : X ∘L v = u ∘L X) (hstar : X ∘L star v = star u ∘L X)
    {K : Set ℂ} (hK : IsCompact K)
    (huK : _root_.spectrum ℂ u ⊆ K) (hvK : _root_.spectrum ℂ v ⊆ K) (g : C(K, ℂ)) :
    X ∘L cfcHom hv (symbolRestrict hvK g)
      = cfcHom hu (symbolRestrict huK g) ∘L X := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  induction g using ContinuousMap.induction_on_of_compact with
  | const r =>
      have h1 : symbolRestrict hvK (ContinuousMap.const K r)
          = algebraMap ℂ (C(_root_.spectrum ℂ v, ℂ)) r := rfl
      have h2 : symbolRestrict huK (ContinuousMap.const K r)
          = algebraMap ℂ (C(_root_.spectrum ℂ u, ℂ)) r := rfl
      rw [h1, h2, AlgHomClass.commutes, AlgHomClass.commutes]
      ext y
      simp [Algebra.algebraMap_eq_smul_one]
  | id =>
      have h1 : symbolRestrict hvK (ContinuousMap.restrict K (ContinuousMap.id ℂ))
          = ContinuousMap.restrict _ (ContinuousMap.id ℂ) := rfl
      have h2 : symbolRestrict huK (ContinuousMap.restrict K (ContinuousMap.id ℂ))
          = ContinuousMap.restrict _ (ContinuousMap.id ℂ) := rfl
      rw [h1, h2, cfcHom_id, cfcHom_id]
      exact hint
  | star_id =>
      have h1 : symbolRestrict hvK (star (ContinuousMap.restrict K (ContinuousMap.id ℂ)))
          = star (ContinuousMap.restrict _ (ContinuousMap.id ℂ)) := rfl
      have h2 : symbolRestrict huK (star (ContinuousMap.restrict K (ContinuousMap.id ℂ)))
          = star (ContinuousMap.restrict _ (ContinuousMap.id ℂ)) := rfl
      rw [h1, h2, map_star, map_star, cfcHom_id, cfcHom_id]
      exact hstar
  | add f g hf hg =>
      simp only [map_add, ContinuousLinearMap.comp_add,
        ContinuousLinearMap.add_comp, hf, hg]
  | mul f g hf hg =>
      rw [map_mul, map_mul, map_mul, map_mul]
      ext y
      exact (congrArg (fun T : F →L[ℂ] E => T (cfcHom hv (symbolRestrict hvK g) y)) hf
        |>.trans (congrArg
          (fun T : F →L[ℂ] E => cfcHom hu (symbolRestrict huK f) (T y)) hg))
  | frequently f hf =>
      have hc1 : Continuous
          (fun g : C(K, ℂ) => X ∘L cfcHom hv (symbolRestrict hvK g)) :=
        (ContinuousLinearMap.compL ℂ F F E X).continuous.comp
          ((cfcHom_continuous hv).comp (continuous_symbolRestrict hvK))
      have hc2 : Continuous
          (fun g : C(K, ℂ) => cfcHom hu (symbolRestrict huK g) ∘L X) :=
        ((ContinuousLinearMap.compL ℂ F E E).flip X).continuous.comp
          ((cfcHom_continuous hu).comp (continuous_symbolRestrict huK))
      rw [← Set.mem_ofPred (p := fun g : C(K, ℂ) =>
          X ∘L cfcHom hv (symbolRestrict hvK g)
            = cfcHom hu (symbolRestrict huK g) ∘L X),
        ← (isClosed_eq hc1 hc2).closure_eq]
      exact mem_closure_of_frequently_of_tendsto hf Filter.tendsto_id

/-- For unitaries, intertwining the operators already intertwines their adjoints:
`star v = v⁻¹` and `star u = u⁻¹`, so `X v = u X` inverts to `X v⋆ = u⋆ X`. -/
theorem star_intertwines_of_mem_unitary
    {u : E →L[ℂ] E} {v : F →L[ℂ] F}
    (hu : u ∈ unitary (E →L[ℂ] E)) (hv : v ∈ unitary (F →L[ℂ] F))
    {X : F →L[ℂ] E} (hint : X ∘L v = u ∘L X) :
    X ∘L star v = star u ∘L X := by
  -- `X` lives between two different spaces, so this is composition, not ring
  -- multiplication; the unitary relations are transported to `∘L` first.
  have hv1 : v ∘L star v = 1 := by
    simpa [ContinuousLinearMap.mul_def] using Unitary.mul_star_self_of_mem hv
  have hu1 : star u ∘L u = 1 := by
    simpa [ContinuousLinearMap.mul_def] using Unitary.star_mul_self_of_mem hu
  have key : u ∘L (X ∘L star v) = X := by
    rw [← ContinuousLinearMap.comp_assoc, ← hint, ContinuousLinearMap.comp_assoc,
      hv1]
    simp [ContinuousLinearMap.one_def]
  calc X ∘L star v = star u ∘L (u ∘L (X ∘L star v)) := by
        rw [← ContinuousLinearMap.comp_assoc, hu1, ContinuousLinearMap.one_def,
          ContinuousLinearMap.id_comp]
    _ = star u ∘L X := by rw [key]

/-- **An intertwiner intertwines the continuous functional calculi of the Cayley
transforms.**

This is `cfcHom_intertwines` with every hypothesis discharged: the Cayley
transforms are unitary (hence star-normal, and the `star` hypothesis is
automatic), their spectra are compact, and `cayley_intertwines` supplies the
intertwining relation itself. -/
theorem cfcHom_cayley_intertwines {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) {X : F →L[ℂ] E}
    (hmaps : ∀ y : B.domain, X (y : F) ∈ A.domain)
    (hint : ∀ y : B.domain, A ⟨X (y : F), hmaps y⟩ = X (B y))
    {K : Set ℂ} (hK : IsCompact K)
    (huK : _root_.spectrum ℂ (cayley hA) ⊆ K) (hvK : _root_.spectrum ℂ (cayley hB) ⊆ K)
    (g : C(K, ℂ)) :
    X ∘L cfcHom (isStarNormal_cayley hB) (symbolRestrict hvK g)
      = cfcHom (isStarNormal_cayley hA) (symbolRestrict huK g) ∘L X :=
  cfcHom_intertwines _ _ (cayley_intertwines hA hB hmaps hint)
    (star_intertwines_of_mem_unitary (cayley_mem_unitary hA) (cayley_mem_unitary hB)
      (cayley_intertwines hA hB hmaps hint)) hK huK hvK g

end Complex

end LinearPMap
end TauCeti
