/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.AdicCompletionBridge
import LeanPool.UniformSheafyTateDomains.AdicSpaces.Presheaf
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Filtration

/-!
# Completion Commutes with Localization

For a topological ring `R⁺` with ideal `I` defining an adic topology,
and an element `s ∈ R⁺`, the localization `R = R⁺[1/s]` carries the
topology whose 0-neighborhoods are images of `I^n` under `R⁺ → R`.

We prove: `Completion(R⁺[1/s]) ≃+* Completion(R⁺)[1/s']`
where `s' = coe(s)` in the completion.

## Proof outline

1. **Backward**: `R⁺ → R → R̂` extends to `R̂⁺ → R̂` (universal property of
   completion). Since `s` is invertible in `R̂`, the universal property of
   localization gives `R̂⁺[1/s'] → R̂`.
2. **Forward**: `R → R̂⁺[1/s']` is dense + continuous, target is complete
   (R̂⁺ is an open complete subgroup) → universal property gives `R̂ → R̂⁺[1/s']`.
3. **Round-trip**: Both composites equal `id` on the dense image of `R`,
   hence equal `id` everywhere (T₂ separation).

## Key consequence

The restriction maps between presheaf values factor through localizations of
flat adic completions, hence are flat.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §5.6, Prop 8.30
-/

open ValuationSpectrum

namespace CompletionLocalization

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]

/-! ### Step 1: The backward map R̂⁺[1/s'] → R̂

The composition `R⁺ →^{algebraMap} R →^{coeRingHom} R̂` is a continuous ring
homomorphism from `R⁺` to the complete ring `R̂`. By the universal property
of completion, it extends to `R̂⁺ →^{φ̂} R̂`. Since `s` is a unit in `R`,
its image under `coeRingHom ∘ algebraMap` is a unit in `R̂`. The localization
universal property then gives `R̂⁺[1/s'] → R̂`. -/

/-- The composite `R⁺ → R → R̂` is a ring hom from the subring to the
completion of the localization. -/
noncomputable def subringToCompletion (D : RationalLocData A) :
    D.P.A₀ →+* presheafValue D :=
  D.coeRingHom.comp ((algebraMap A (Localization.Away D.s)).comp D.P.A₀.subtype)

omit [PlusSubring A] [IsHuberRing A] in
/-- `s` is a unit in `presheafValue D` (since `s` is a unit in `Localization.Away D.s`
and `coeRingHom` preserves units). -/
theorem isUnit_s_in_presheafValue (D : RationalLocData A) :
    IsUnit (D.canonicalMap D.s) :=
  (IsLocalization.map_units (Localization.Away D.s)
    (⟨D.s, ⟨1, pow_one D.s⟩⟩ : Submonoid.powers D.s)).map D.coeRingHom

/-! ### Step A: Noetherian torsion stabilization

In a Noetherian ring, the ascending chain of annihilator ideals
`ann(s) ⊆ ann(s²) ⊆ ...` stabilizes. This gives a uniform bound
on the torsion order: `s^m * x = 0` implies `s^{N₀} * x = 0`
for a fixed `N₀` independent of `x`. -/

section TorsionStabilization

variable {R : Type*} [CommRing R] [IsNoetherianRing R] (s : R)

/-- Monotone sequences of submodules over Noetherian rings stabilize. -/
private theorem monotone_stabilizes_of_wfGT {α : Type*} [PartialOrder α]
    [WellFoundedGT α] (f : ℕ → α) (hf : Monotone f) :
    ∃ n, ∀ m, n ≤ m → f n = f m :=
  WellFoundedGT.monotone_chain_condition ⟨f, hf⟩

/-- The annihilator ideal `{x | s^n * x = 0}`. -/
private def sAnn (n : ℕ) : Ideal R where
  carrier := {x | s ^ n * x = 0}
  add_mem' ha hb := by simp only [Set.mem_setOf] at *; rw [mul_add, ha, hb, add_zero]
  zero_mem' := mul_zero _
  smul_mem' r x hx := by
    simp only [Set.mem_setOf, smul_eq_mul] at *; rw [mul_left_comm, hx, mul_zero]

omit [IsNoetherianRing R] in
private theorem sAnn_mono : Monotone (sAnn s) := by
  intro m n hmn x (hx : s ^ m * x = 0)
  change s ^ n * x = 0
  have : s ^ n * x = s ^ (n - m) * (s ^ m * x) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hmn]
  rw [this, hx, mul_zero]

/-- In a Noetherian ring, the `s`-torsion order is uniformly bounded: there exists `N₀`
such that `s^m * x = 0` (for any `m`) implies `s^{N₀} * x = 0`. -/
theorem torsion_bounded :
    ∃ N₀ : ℕ, ∀ x : R, (∃ m : ℕ, s ^ m * x = 0) → s ^ N₀ * x = 0 := by
  obtain ⟨N₀, hN₀⟩ := monotone_stabilizes_of_wfGT
    (f := fun n => (sAnn s n : Submodule R R)) (fun _ _ h => sAnn_mono s h)
  refine ⟨N₀, fun x ⟨m, hm⟩ => ?_⟩
  rcases Nat.lt_or_ge m N₀ with hlt | hge
  · exact sAnn_mono s (Nat.le_of_lt hlt) hm
  · show x ∈ sAnn s N₀
    exact (hN₀ m hge).symm ▸ hm

end TorsionStabilization

/-! ### Algebraic kernel torsion for locLift

For `locLift D₀ D h : Localization.Away D₀.s →+* Localization.Away D.s`:
- Elements in the kernel satisfy `∃ n, algebraMap(D.s)^n * x = 0` (elementwise).
- By `torsion_bounded` on the Noetherian ring `Localization.Away D₀.s` with
  element `algebraMap(D.s)`: there is a UNIFORM `N₀` with
  `algebraMap(D.s)^{N₀} * x = 0` for all kernel elements.
- This is the Eq condition for `IsLocalization.Away` at the localization level. -/

section LocLiftTorsion

variable {R : Type*} [CommRing R]

omit [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] [IsHuberRing A] in
private theorem away_lift_ker_torsion {s₁ t : A}
    (hu : IsUnit (algebraMap A (Localization.Away t) s₁))
    (x : Localization.Away s₁)
    (hx : IsLocalization.Away.lift s₁ hu x = 0) :
    ∃ n : ℕ, algebraMap A (Localization.Away s₁) (t ^ n) * x = 0 := by
  obtain ⟨n₀, a, hsurj⟩ := IsLocalization.Away.surj (S := Localization.Away s₁) s₁ x
  have hφ_eq : algebraMap A (Localization.Away t) a = 0 := by
    have h := congr_arg (IsLocalization.Away.lift (S := Localization.Away s₁) s₁ hu) hsurj
    rw [map_mul, map_pow] at h
    simp only [IsLocalization.Away.lift_eq] at h
    rwa [hx, zero_mul, eq_comm] at h
  obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq (S := Localization.Away t) t
    (hφ_eq.trans (map_zero _).symm)
  simp only [mul_zero] at hm
  refine ⟨m, ?_⟩
  have hs₁_unit : IsUnit ((algebraMap A (Localization.Away s₁) s₁) ^ n₀) :=
    IsUnit.pow n₀ (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away s₁) s₁)
  have key : algebraMap A (Localization.Away s₁) (t ^ m) * x *
      (algebraMap A (Localization.Away s₁) s₁) ^ n₀ = 0 := by
    rw [mul_assoc, hsurj, ← map_mul, hm, map_zero]
  rwa [hs₁_unit.mul_left_eq_zero] at key

omit [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] [IsHuberRing A] in
/-- Uniform algebraic torsion bound: there exists `N₀` such that every kernel element of
`Away.lift` is killed by `algebraMap(t)^{N₀}`. -/
theorem away_lift_torsion_bounded [IsNoetherianRing A] {s₁ t : A}
    (hu : IsUnit (algebraMap A (Localization.Away t) s₁)) :
    ∃ N₀ : ℕ, ∀ x : Localization.Away s₁,
      IsLocalization.Away.lift s₁ hu x = 0 →
        algebraMap A (Localization.Away s₁) (t ^ N₀) * x = 0 := by
  haveI : IsNoetherianRing (Localization.Away s₁) :=
    IsLocalization.isNoetherianRing (Submonoid.powers s₁) (Localization.Away s₁) ‹_›
  obtain ⟨N₀, hN₀⟩ := torsion_bounded (algebraMap A (Localization.Away s₁) t)
  refine ⟨N₀, fun x hx => ?_⟩
  rw [map_pow]
  obtain ⟨n, hn⟩ := away_lift_ker_torsion hu x hx
  exact hN₀ x ⟨n, by rwa [map_pow] at hn⟩

end LocLiftTorsion

/-! ### Step B: Adic completion preserves the kernel

For the ring-of-definition level: the adic completion of the short exact sequence
`0 → K → R → R/K → 0` (where R = locSubring D₀, K = ker(locLift) ∩ R, I = locIdeal D₀)
gives `ker(Â(quotient_map)) = range(Â(inclusion))` by `AdicCompletion.map_exact`.

This means: the kernel of the completed quotient map equals the image of the
completion of K — which under the AdicCompletionBridge identification is the
closure of the embedded K in `presheafValue_ringOfDef D₀`. -/

section AdicCompletionKernel

variable {R : Type*} [CommRing R] [IsNoetherianRing R] (I K : Ideal R)

/-- The adic completion of the short exact sequence `0 → K → R → R/K → 0`
preserves exactness: `ker(Â(mkQ)) = range(Â(subtype))`. -/
theorem adicCompletion_ker_mkQ_eq_range_subtype :
    Function.Exact
      (AdicCompletion.map I (K : Submodule R R).subtype)
      (AdicCompletion.map I (K : Submodule R R).mkQ) :=
  AdicCompletion.map_exact Subtype.val_injective
    (LinearMap.exact_subtype_mkQ (K : Submodule R R))
    (Submodule.Quotient.mk_surjective _)

end AdicCompletionKernel

/-! ### Step B target: closure of algebraic kernel = topological kernel

For the Eq condition of `IsLocalization.Away` for the restriction map,
we need: `ker(restrictionMapHom) = closure(coeRingHom '' ker(locLift))`.

The (⊇) direction is easy: `coeRingHom(ker(locLift)) ⊆ ker(restrictionMapHom)`
(algebraic kernel maps to 0), and the kernel is closed.

The (⊆) direction — every element of the topological kernel is a limit of
algebraic kernel elements — requires the adic completion to preserve the
kernel of the localization map. This uses:
1. The localization map `locLift` is flat (localizations are flat).
2. For flat maps of Noetherian modules, adic completion preserves kernels
   (Mathlib: `AdicCompletion.map_exact` or equivalent).
3. The identification `presheafValue D₀ = Completion(Loc.Away D₀.s)`.

**Exact statement needed** (the smallest useful form):
```
∀ c ∈ ker(restrictionMapHom D₀ D h),
  c ∈ closure(D₀.coeRingHom '' {x | locLift D₀ D h x = 0})
```

Once Steps A + B hold, the Eq condition follows:
- By Step A: `algebraMap(D.s)^{N₀}` kills every algebraic kernel element.
- So `D₀.canonicalMap(D.s)^{N₀}` kills every `coeRingHom(ker(locLift))` element.
- By Step B + continuity + T₂: kills the closure = kills `ker(restrictionMapHom)`.
-/

/-! ### Step C: The Eq condition for `IsLocalization.Away`

Combining Steps A and B: if `sigma(c) = 0` then `s'^{N₀} * c = 0`.

**Proof:** By the T004 bridge (`presheafValue_ker_from_locSubring_ker`),
`c = lim D₀.coeRingHom(t_n)` where each `t_n ∈ ker(locLift)`.
By Step A (`away_lift_torsion_bounded`), `algebraMap(D.s)^{N₀} * t_n = 0`
for all `n`. Hence `s'^{N₀} * D₀.coeRingHom(t_n) = 0` for all `n`.
Taking limits (multiplication is continuous, T₂ limits are unique):
`s'^{N₀} * c = 0`. -/

section EqCondition

variable [IsTateRing A] [IsNoetherianRing A] [T2Space A]
  [NonarchimedeanRing A]

omit [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    in
/-- `D₀.s` is a unit in `Localization.Away D.s` when `R(D.T/D.s) ⊆ R(D₀.T/D₀.s)`.
This is the localization-level unit witness (not the presheafValue-level one). -/
private theorem isUnit_algebraMap_s_of_subset
    (D₀ D : RationalLocData A) (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    IsUnit (algebraMap A (Localization.Away D.s) D₀.s) := by
  have hrad : D.s ∈ Ideal.radical (Ideal.span {D₀.s}) := by
    classical
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    intro p ⟨hsp, hp⟩
    refine mem_prime_of_rational_subset D₀ D h p hp
      (hsp (Ideal.subset_span (Set.mem_singleton D₀.s))) ?_
    intro hp_notOpen hD's
    exact spa_point_nonOpen_of_rational_subset D₀ D h p hp
      (hsp (Ideal.subset_span (Set.mem_singleton D₀.s))) hD's hp_notOpen
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hrad
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hn
  have heq : algebraMap A (Localization.Away D.s) a *
      algebraMap A (Localization.Away D.s) D₀.s =
      algebraMap A (Localization.Away D.s) D.s ^ n := by
    rw [← map_mul, ← map_pow, ha]
  exact isUnit_of_mul_isUnit_right (heq ▸ (IsLocalization.map_units (Localization.Away D.s)
    (⟨D.s, ⟨1, pow_one D.s⟩⟩ : Submonoid.powers D.s)).pow n)

private noncomputable def algLift
    (D₀ D : RationalLocData A) (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    Localization.Away D₀.s →+* Localization.Away D.s :=
  IsLocalization.Away.lift D₀.s (isUnit_algebraMap_s_of_subset D₀ D h)

omit [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    in
/-- The restriction map on the dense image factors through `algLift`. -/
private theorem restrictionMapHom_coe_eq
    (D₀ D : RationalLocData A) (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s)
    (a : Localization.Away D₀.s) :
    restrictionMapHom D₀ D h (D₀.coeRingHom a) =
      D.coeRingHom (algLift D₀ D h a) := by
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  letI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  have h2 : restrictionMapAlg D₀ D h a = D.coeRingHom (algLift D₀ D h a) := by
    have : (restrictionMapAlg D₀ D h : Localization.Away D₀.s →+* _) =
        D.coeRingHom.comp (algLift D₀ D h) := by
      apply IsLocalization.ringHom_ext (Submonoid.powers D₀.s)
      ext x
      simp only [RingHom.comp_apply, restrictionMapAlg, algLift, IsLocalization.Away.lift_eq,
        RationalLocData.coeRingHom, RationalLocData.canonicalMap]
    exact DFunLike.congr_fun this a
  exact (UniformSpace.Completion.extensionHom_coe _ _ a).trans h2

/-- The embedding of `locSubring` into `presheafValue` via `coeRingHom ∘ subtype`. -/
noncomputable def locSubringToPresheafValue (D₀ : RationalLocData A) :
    (locSubring D₀.P D₀.T D₀.s) →+* presheafValue D₀ :=
  D₀.coeRingHom.comp (locSubring D₀.P D₀.T D₀.s).subtype

omit [PlusSubring A] [IsHuberRing A] [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] in
/-- `locSubringToPresheafValue` is `IsUniformInducing`: the composition of the
subtype embedding (uniform inducing by definition of the comap uniform space) with
`coeRingHom` (uniform inducing as the completion embedding). -/
theorem locSubringToPresheafValue_isUniformInducing (D₀ : RationalLocData A) :
    @IsUniformInducing _ _
      (D₀.uniformSpace.comap (locSubring D₀.P D₀.T D₀.s).subtype)
      (@UniformSpace.Completion.uniformSpace _ D₀.uniformSpace)
      (locSubringToPresheafValue D₀) := by
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  exact (UniformSpace.Completion.isUniformInducing_coe _).comp ⟨rfl⟩

omit [PlusSubring A] [IsHuberRing A] [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] in
theorem locSubringToPresheafValue_continuous (D₀ : RationalLocData A) :
    @Continuous _ _
      (D₀.uniformSpace.comap (locSubring D₀.P D₀.T D₀.s).subtype).toTopologicalSpace
      (@UniformSpace.toTopologicalSpace _
        (@UniformSpace.Completion.uniformSpace _ D₀.uniformSpace))
      (locSubringToPresheafValue D₀) := by
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  exact (locSubringToPresheafValue_isUniformInducing D₀).isInducing.continuous

/-- The uniform space on `locSubring` induced from the localization topology. -/
@[reducible]
noncomputable def locSubringUniformSpace (D₀ : RationalLocData A) :
    UniformSpace (locSubring D₀.P D₀.T D₀.s) :=
  D₀.uniformSpace.comap (locSubring D₀.P D₀.T D₀.s).subtype

section BridgeMap

variable (D₀ : RationalLocData A)

attribute [local instance] locSubringUniformSpace

private noncomputable instance : IsTopologicalRing (locSubring D₀.P D₀.T D₀.s) := by
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  haveI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  exact Subring.instIsTopologicalRing _

private noncomputable instance : IsUniformAddGroup (locSubring D₀.P D₀.T D₀.s) := by
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  haveI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  exact IsUniformAddGroup.comap _

/-- The completed bridge map: extends `coeRingHom ∘ subtype` from `locSubring` to
its completion, landing in `presheafValue`. -/
noncomputable def locSubringCompletionToPresheafValue :
    UniformSpace.Completion (locSubring D₀.P D₀.T D₀.s) →+* presheafValue D₀ :=
  UniformSpace.Completion.extensionHom
    (locSubringToPresheafValue D₀)
    (locSubringToPresheafValue_continuous D₀)

omit [PlusSubring A] [IsHuberRing A] [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] in
/-- The completed bridge map agrees with `coeRingHom ∘ subtype` on the dense
image of `locSubring`. -/
theorem locSubringCompletionToPresheafValue_coe
    (r : locSubring D₀.P D₀.T D₀.s) :
    locSubringCompletionToPresheafValue D₀
      (UniformSpace.Completion.coeRingHom r) =
      D₀.coeRingHom ((locSubring D₀.P D₀.T D₀.s).subtype r) :=
  UniformSpace.Completion.extensionHom_coe _ _ r

/-- The completion bridge equivalence
`Completion(locSubring, locIdeal-adic) ≃+* AdicCompletion(locIdeal, locSubring)`. -/
noncomputable def locSubringCompletionEquivAdicCompletion :
    UniformSpace.Completion (locSubring D₀.P D₀.T D₀.s) ≃+*
      AdicCompletion (locIdeal D₀.P D₀.T D₀.s) (locSubring D₀.P D₀.T D₀.s) :=
  AdicCompletionBridge.adicCompletionRingEquiv _
    (locSubring_topology_eq_adic D₀.P D₀.T D₀.s D₀.hopen)

omit [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] in
/-- On the dense image of `locSubring`, applying `restrictionMapHom` after the bridge
equals applying `D.coeRingHom ∘ algLift ∘ subtype`. -/
theorem restrictionMapHom_comp_bridge_coe
    (D₀ D : RationalLocData A) (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s)
    (r : locSubring D₀.P D₀.T D₀.s) :
    restrictionMapHom D₀ D h
      (locSubringCompletionToPresheafValue D₀ (UniformSpace.Completion.coeRingHom r)) =
      D.coeRingHom (algLift D₀ D h ((locSubring D₀.P D₀.T D₀.s).subtype r)) := by
  rw [locSubringCompletionToPresheafValue_coe, restrictionMapHom_coe_eq]

omit [PlusSubring A] [IsHuberRing A] [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] in
/-- **Bridge kernel transfer:** In `AdicCompletion(locIdeal, locSubring)`, the
exactness of `map_exact` gives: for any ideal `K` of `locSubring`, an element
in the kernel of the completed quotient map is in the range of the completed
inclusion. -/
theorem adicCompletion_kernel_transfer
    [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (K : Ideal (locSubring D₀.P D₀.T D₀.s))
    (x : AdicCompletion (locIdeal D₀.P D₀.T D₀.s)
      (locSubring D₀.P D₀.T D₀.s))
    (hx : AdicCompletion.map (locIdeal D₀.P D₀.T D₀.s)
      (K : Submodule (locSubring D₀.P D₀.T D₀.s)
        (locSubring D₀.P D₀.T D₀.s)).mkQ x = 0) :
    x ∈ LinearMap.range (AdicCompletion.map
      (locIdeal D₀.P D₀.T D₀.s)
      (K : Submodule (locSubring D₀.P D₀.T D₀.s)
        (locSubring D₀.P D₀.T D₀.s)).subtype) :=
  (adicCompletion_ker_mkQ_eq_range_subtype
    (locIdeal D₀.P D₀.T D₀.s) K x).mp hx

omit [PlusSubring A] [IsHuberRing A] [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] in
/-- The completed bridge map is injective (IsUniformInducing into T₂ → injective). -/
theorem locSubringCompletionToPresheafValue_injective :
    Function.Injective (locSubringCompletionToPresheafValue D₀) := by
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  intro x y hxy
  have hui := (UniformSpace.Completion.isUniformInducing_coe
    (α := Localization.Away D₀.s)).comp (⟨rfl⟩ :
      @IsUniformInducing _ _ (locSubringUniformSpace D₀) D₀.uniformSpace
        (locSubring D₀.P D₀.T D₀.s).subtype)
  exact ((UniformSpace.Completion.isUniformInducing_extension
    hui).isInducing.inseparable_iff.mp
    (Inseparable.of_eq hxy)).eq

omit [PlusSubring A] [IsHuberRing A] [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] in
/-- The range of the completed bridge equals `completedLocSubring`. -/
theorem locSubringCompletionToPresheafValue_range :
    Set.range (locSubringCompletionToPresheafValue D₀) =
      (D₀.completedLocSubring : Set (presheafValue D₀)) := by
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  haveI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    refine UniformSpace.Completion.induction_on x ?_ (fun a => ?_)
    · exact (Subring.isClosed_topologicalClosure _).preimage
        UniformSpace.Completion.continuous_extension
    · change locSubringCompletionToPresheafValue D₀
        (UniformSpace.Completion.coeRingHom a) ∈ _
      rw [locSubringCompletionToPresheafValue_coe]
      exact D₀.coeRingHom_mem_completedLocSubring a.prop
  · apply closure_minimal
    · rintro y ⟨x, hx, rfl⟩
      exact ⟨UniformSpace.Completion.coeRingHom ⟨x, hx⟩,
        locSubringCompletionToPresheafValue_coe D₀ ⟨x, hx⟩⟩
    · exact ((UniformSpace.Completion.isUniformInducing_extension
        (locSubringToPresheafValue_isUniformInducing D₀)).isComplete_range).isClosed

/-- The completed bridge is a ring isomorphism
`Completion(locSubring) ≃+* completedLocSubring D₀` (Wedhorn Prop 8.15). -/
noncomputable def completionLocSubringEquiv :
    UniformSpace.Completion (locSubring D₀.P D₀.T D₀.s) ≃+*
      D₀.completedLocSubring := by
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  haveI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  haveI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  haveI : IsClosed (D₀.completedLocSubring : Set (presheafValue D₀)) :=
    Subring.isClosed_topologicalClosure _
  haveI : CompleteSpace D₀.completedLocSubring :=
    (Subring.isClosed_topologicalClosure _).completeSpace_coe
  haveI : IsTopologicalRing D₀.completedLocSubring := Subring.instIsTopologicalRing _
  haveI : IsUniformAddGroup D₀.completedLocSubring :=
    IsUniformAddGroup.comap D₀.completedLocSubring.subtype.toAddMonoidHom
  have hcont : Continuous D₀.locSubringToCompleted :=
    (locSubringToPresheafValue_continuous D₀).subtype_mk _
  have hui : IsUniformInducing D₀.locSubringToCompleted :=
    isUniformEmbedding_subtype_val.isUniformInducing.of_comp_iff.mp
      (locSubringToPresheafValue_isUniformInducing D₀)
  have hdense : DenseRange D₀.locSubringToCompleted := by
    intro ⟨x, hx⟩
    rw [mem_closure_iff_nhds]
    intro U hU
    rw [nhds_induced, Filter.mem_comap] at hU
    obtain ⟨V, hV, hVU⟩ := hU
    obtain ⟨y, hyV, z, hz, rfl⟩ := mem_closure_iff_nhds.mp hx V hV
    exact ⟨⟨D₀.coeRingHom z, D₀.coeRingHom_mem_completedLocSubring hz⟩,
      hVU hyV, ⟨⟨z, hz⟩, rfl⟩⟩
  exact AdicCompletionBridge.completionRingEquiv D₀.locSubringToCompleted hcont hui hdense

end BridgeMap

-- REMOVED 2026-04-16: `adicCompletion_prime_liesOver` (no call sites; sorry'd on
-- Wedhorn §7.23 content — flatness going-down step). Was in `section PrimeExtension`.

/-! ### Power-boundedness of `invS` (Wedhorn §6.2)

The element `invS D = 1/canonicalMap(D.s)` in `presheafValue D` is power-bounded
when `1 ∈ D.T` (Wedhorn normalization). The proof: `divByS 1 D.s = 1/s ∈ locSubring`
(since `1 ∈ T` makes it a generator), `locSubring` is bounded
(`locSubring_isBounded`), and elements of a bounded subring are power-bounded
(`isPowerBounded_of_mem_locSubring`).

For general `RationalLocData` without `1 ∈ T`, the power-boundedness of `invS`
requires the integral closure theorem (Wedhorn Prop 6.2.4), which is the
formalization's fundamental open problem. -/

section InvSPowerBounded

open Pointwise

omit [PlusSubring A] [IsHuberRing A] [IsTateRing A]
    [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    in
/-- The image of `locSubring` under `coeRingHom` is bounded in `presheafValue D`.
Proof: `locSubring * locNhd k ⊆ locNhd k` (ideal absorption), so
`(coe '' locSubring) * (coe '' locNhd k) ⊆ coe '' locNhd k` by the ring hom
property. For `U ∈ nhds 0` in the completion, pick a closed `W ∈ nhds 0`
with `W ⊆ U`, pull back to get `coe⁻¹'(W) ∈ nhds 0` in the source
(by `IsUniformInducing`), use ideal absorption to get
`locSubring * locNhd k ⊆ locNhd k ⊆ coe⁻¹'(W)` for large `k`, then
`coe '' locSubring * closure(coe '' locNhd k) ⊆ closure(coe '' locNhd k)
⊆ W ⊆ U`. -/
theorem coeRingHom_image_locSubring_isBounded (D : RationalLocData A) :
    @TopologicalRing.IsBounded (presheafValue D) _
      (@UniformSpace.toTopologicalSpace _
        (@UniformSpace.Completion.uniformSpace _ D.uniformSpace))
      (D.coeRingHom '' (locSubring D.P D.T D.s : Set (Localization.Away D.s))) := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : TopologicalSpace (Localization.Away D.s) := D.topology
  have hbasis := locBasis D.P D.T D.s D.hopen
  -- Ideal absorption: locSubring * locNhd k ⊆ locNhd k
  have habsorb : ∀ k, (locSubring D.P D.T D.s : Set (Localization.Away D.s)) *
      (locNhd D.P D.T D.s k : Set (Localization.Away D.s)) ⊆
      (locNhd D.P D.T D.s k : Set (Localization.Away D.s)) := by
    intro k x hx
    obtain ⟨d, hd, v, hv, rfl⟩ := Set.mem_mul.mp hx
    obtain ⟨jv, hjv, rfl⟩ := hv
    exact ⟨⟨d, hd⟩ * jv, Ideal.mul_mem_left _ _ hjv, MulMemClass.coe_mul ..⟩
  intro U hU
  -- Step 1: Find a closed W ∈ nhds 0 with W ⊆ U (completion is regular as a uniform space)
  obtain ⟨W, hW_nhds, hW_closed, hWU⟩ := exists_mem_nhds_isClosed_subset hU
  -- Step 2: Pull back W to the source (coeRingHom is continuous, coeRingHom 0 = 0)
  have hcoe_cont : @Continuous _ _ D.topology
      (@UniformSpace.toTopologicalSpace _
        (@UniformSpace.Completion.uniformSpace _ D.uniformSpace)) D.coeRingHom :=
    @UniformSpace.Completion.continuous_coe _ D.uniformSpace
  have hpull : D.coeRingHom ⁻¹' W ∈ @nhds _ D.topology 0 := by
    have : W ∈ @nhds _ (@UniformSpace.toTopologicalSpace _
        (@UniformSpace.Completion.uniformSpace _ D.uniformSpace))
        (D.coeRingHom (0 : Localization.Away D.s)) := by
      rwa [map_zero]
    exact @ContinuousAt.preimage_mem_nhds _ _ D.topology
      (@UniformSpace.toTopologicalSpace _
        (@UniformSpace.Completion.uniformSpace _ D.uniformSpace))
      _ _ _ (hcoe_cont.continuousAt) this
  -- Step 3: Get basis neighborhood locNhd k ⊆ coe⁻¹'(W)
  obtain ⟨_, ⟨k, rfl⟩, hkW⟩ :=
    hbasis.toRingFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff.mp hpull
  -- Step 4: V = closure(coe '' locNhd k) ∈ nhds 0 in completion
  have hlocNhd_nhds : (locNhd D.P D.T D.s k : Set (Localization.Away D.s)) ∈
      @nhds _ D.topology 0 :=
    hbasis.hasBasis_nhds_zero.mem_of_mem (i := k) trivial
  have hV_nhds : closure (D.coeRingHom '' (locNhd D.P D.T D.s k :
      Set (Localization.Away D.s))) ∈
      @nhds _ (@UniformSpace.toTopologicalSpace _
        (@UniformSpace.Completion.uniformSpace _ D.uniformSpace)) 0 := by
    have h := (UniformSpace.Completion.isDenseInducing_coe
      (α := Localization.Away D.s)).closure_image_mem_nhds hlocNhd_nhds
    rwa [UniformSpace.Completion.coe_zero] at h
  refine ⟨closure (D.coeRingHom '' (locNhd D.P D.T D.s k :
      Set (Localization.Away D.s))), hV_nhds, ?_⟩
  -- Step 5: (coe '' locSubring) * closure(coe '' locNhd k) ⊆ W ⊆ U
  -- For each d ∈ coe '' locSubring:
  --   (d * ·) '' closure(S) ⊆ closure((d * ·) '' S)   [image_closure_subset_closure_image]
  --   (d * ·) '' S ⊆ W                                 [ideal absorption + hkW]
  --   closure((d * ·) '' S) ⊆ closure(W) = W           [W closed]
  intro x hx
  apply hWU
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
  obtain ⟨a', ha', rfl⟩ := ha
  -- a' ∈ locSubring, b ∈ closure(coe '' locNhd k). Show coe(a') * b ∈ W.
  set f := (D.coeRingHom a' * · : presheafValue D → presheafValue D)
  set S := D.coeRingHom '' (locNhd D.P D.T D.s k : Set (Localization.Away D.s))
  -- f(b) ∈ f '' closure(S) ⊆ closure(f '' S)
  have hcont : Continuous f := continuous_const.mul continuous_id
  have hfb_in_cl : f b ∈ closure (f '' S) :=
    image_closure_subset_closure_image hcont (Set.mem_image_of_mem f hb)
  -- f '' S ⊆ W: for v ∈ coe '' locNhd k, coe(a') * v = coe(a' * v') where
  -- a' * v' ∈ locSubring * locNhd k ⊆ locNhd k ⊆ coe⁻¹'(W)
  have hfS_sub_W : f '' S ⊆ W := by
    rintro _ ⟨_, ⟨v', hv', rfl⟩, rfl⟩
    change D.coeRingHom a' * D.coeRingHom v' ∈ W
    rw [← map_mul]
    apply hkW
    exact habsorb k (Set.mul_mem_mul ha' hv')
  -- closure(f '' S) ⊆ closure(W) = W
  exact hW_closed.closure_subset (closure_mono hfS_sub_W hfb_in_cl)

omit [PlusSubring A] [IsHuberRing A] [IsTateRing A]
    [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    in
/-- The element `coeRingHom(divByS 1 D.s)` is power-bounded when `1 ∈ D.T`. -/
theorem invS_isPowerBounded_of_one_mem_T (D : RationalLocData A)
    (h1 : (1 : A) ∈ D.T) :
    @TopologicalRing.IsPowerBounded (presheafValue D) _
      (@UniformSpace.toTopologicalSpace _
        (@UniformSpace.Completion.uniformSpace _ D.uniformSpace))
      (D.coeRingHom (divByS 1 D.s)) := by
  -- divByS 1 D.s ∈ locSubring (since 1 ∈ D.T)
  have hmem : divByS 1 D.s ∈ locSubring D.P D.T D.s :=
    divByS_mem_locSubring D.P D.T D.s h1
  -- Powers of (divByS 1 D.s) all lie in locSubring (subring closed under powers)
  have hpow : ∀ n : ℕ, (divByS 1 D.s) ^ n ∈ locSubring D.P D.T D.s :=
    fun n ↦ (locSubring D.P D.T D.s).pow_mem hmem n
  -- coeRingHom preserves powers: (coeRingHom x)^n = coeRingHom(x^n)
  have hrange : Set.range ((D.coeRingHom (divByS 1 D.s)) ^ · : ℕ → presheafValue D) ⊆
      D.coeRingHom '' (locSubring D.P D.T D.s : Set (Localization.Away D.s)) := by
    rintro _ ⟨n, rfl⟩
    change (D.coeRingHom (divByS 1 D.s)) ^ n ∈ _
    rw [← map_pow]
    exact ⟨(divByS 1 D.s) ^ n, hpow n, rfl⟩
  -- IsBounded.subset + coeRingHom_image_locSubring_isBounded
  exact (coeRingHom_image_locSubring_isBounded D).subset hrange

end InvSPowerBounded

omit [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    in
/-- Every kernel element of `algLift` times a high enough power of `algebraMap(D₀.s)` lands in
`algebraMap(A) ∩ ker(algLift)`. -/
private theorem ker_algLift_denom_clear
    (D₀ D : RationalLocData A) (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s)
    (x : Localization.Away D₀.s) (hx : algLift D₀ D h x = 0) :
    ∃ k : ℕ, ∃ a : A,
      algebraMap A (Localization.Away D₀.s) a =
        algebraMap A (Localization.Away D₀.s) (D₀.s ^ k) * x ∧
      algLift D₀ D h (algebraMap A (Localization.Away D₀.s) a) = 0 := by
  obtain ⟨k, a, hsurj⟩ := IsLocalization.Away.surj (S := Localization.Away D₀.s) D₀.s x
  have heq : algebraMap A (Localization.Away D₀.s) a =
      algebraMap A (Localization.Away D₀.s) (D₀.s ^ k) * x := by
    rw [map_pow]; exact hsurj.symm.trans (mul_comm _ _)
  exact ⟨k, a, heq, by rw [heq, map_mul, hx, mul_zero]⟩

-- REMOVED 2026-04-16: `presheafValue_ker_from_locSubring_ker` (sorry'd) and
-- `restrictionMapHom_eq_condition` (its only caller). Neither had external
-- users. The T₂-density route these theorems implemented is superseded by the
-- Wedhorn 8.32 faithful-flatness route planned for `restrictionMapHom_injective`.

end EqCondition

-- REMOVED 2026-04-16: `productRestriction_zero_kernel` (no call sites; sorry'd
-- on Wedhorn Theorem 8.28(b) Part 1 — T₂ density method). The actual
-- `tateAcyclicity` Part 1 (LaurentRefinement.lean) uses a different route via
-- `restrictionMapHom_injective` applied to any single cover element.

end CompletionLocalization
