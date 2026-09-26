/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Degree
/-! Provides the public declarations in the
  `ValuationTheory.DiscreteValuationField.FiniteExtension.Uniqueness` Lean module. -/

@[expose] public section

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  exists_extension_valuationSubring_with_hasExtension →
    exists_extension_valuationSubring_with_hasExtension

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  idealOfLE_eq_maximalIdeal_of_mem_maximalIdeal_iff →
    idealOfLE_eq_maximalIdeal_of_mem_maximalIdeal_iff

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  integralClosureValuationSubringOfMemOrInv →
    integralClosureValuationSubringOfMemOrInv

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  integralClosureValuationSubringOfMemOrInv_hasExtension →
    integralClosureValuationSubringOfMemOrInv_hasExtension

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  integralClosureValuationSubringOfMemOrInv_isIntegralClosure →
    integralClosureValuationSubringOfMemOrInv_isIntegralClosure

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  moduleFinite_valuationSubring_of_isIntegralClosure →
    moduleFinite_valuationSubring_of_isIntegralClosure

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdeal →
    valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdeal

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  valuationSubring_eq_of_le_of_inclusion_isLocalHom →
    valuationSubring_eq_of_le_of_inclusion_isLocalHom

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  valuationSubring_isIntegralClosure_of_isIntegral →
    valuationSubring_isIntegralClosure_of_isIntegral

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  valuation_isEquiv_of_hasExtension_of_moduleFinite →
    valuation_isEquiv_of_hasExtension_of_moduleFinite


namespace ValuationTheory

noncomputable
section

universe u v w x y

namespace DiscreteValuationField
namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- A complete-DVF uniqueness predicate for extensions of the base valuation. -/
def HasUniqueValuationExtension (base : CompleteDVF.{u, v} K)
    (target : CompleteDVF.{w, x} L) : Prop :=
  ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
      target.valuation.IsEquiv v'

omit [FiniteDimensional K L] [base.valuation.HasExtension target.valuation] in
/-- Forgetting completeness turns complete-DVF uniqueness into the
Henselian-DVF uniqueness predicate. -/
theorem hasUniqueValuationExtension_toHenselianDVF
    (huniq : HasUniqueValuationExtension.{u, v, w, x, y}
      (base := base) (target := target)) :
    HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y}
      base.toHenselianDVF target.toHenselianDVF := by
  intro Gamma' _ v' hExt
  exact @huniq Gamma' inferInstance v' hExt

omit [FiniteDimensional K L] [base.valuation.HasExtension target.valuation] in
/-- Equality of valuation subrings for all extensions proves uniqueness up to
mathlib's valuation equivalence. -/
theorem hasUniqueValuationExtension_of_forall_valuationSubring_eq
    (h :
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
          target.valuation.valuationSubring = v'.valuationSubring) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  intro Gamma' _ v' _
  exact valuation_isEquiv_of_valuationSubring_eq target v' (@h Gamma' _ v' _)

omit [FiniteDimensional K L] in
/-- Finite-module criterion for uniqueness of valuation extensions.  If every
valuation extending the base valuation has a module-finite valuation ring over
the base valuation ring, then the extension valuation is unique up to mathlib's
valuation equivalence. -/
theorem hasUniqueValuationExtension_of_forall_moduleFinite
    [Module.Finite base.valuationSubring target.valuationSubring]
    (hfinite :
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
          [Algebra base.valuation.valuationSubring v'.valuationSubring] →
          Module.Finite base.valuation.valuationSubring v'.valuationSubring) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  intro Gamma' _ v' hExt
  let : base.valuation.HasExtension v' := hExt
  let : Module.Finite base.valuation.valuationSubring v'.valuationSubring :=
    @hfinite Gamma' inferInstance v' hExt inferInstance
  let : Module.Finite base.valuation.valuationSubring
      target.valuation.valuationSubring := by
    change Module.Finite base.valuationSubring target.valuationSubring
    infer_instance
  exact
    valuation_isEquiv_of_hasExtension_of_moduleFinite
      (L := L) base.valuation target.valuation v'

/-- Integral-closure criterion for uniqueness of valuation extensions.  In a
finite separable extension over a complete DVF, if the chosen target valuation
ring and every comparison valuation ring extending the base valuation are the
actual integral closure of the base valuation ring in `L`, then the extension
valuation is unique up to mathlib's valuation equivalence.

For the Henselian finite-extension theorem, this isolates the remaining
frontier: prove the integral-closure statement for all extension valuations
from the Henselian hypothesis, rather than adding a certificate carrying
uniqueness. -/
theorem hasUniqueValuationExtension_of_forall_isIntegralClosure
    [Algebra.IsSeparable K L]
    [IsIntegralClosure target.valuationSubring base.valuationSubring L]
    (hintegral :
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
          [Algebra base.valuation.valuationSubring v'.valuationSubring] →
          IsIntegralClosure v'.valuationSubring base.valuation.valuationSubring L) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let : IsNoetherianRing base.valuationSubring :=
    base_valuationSubring_isNoetherianRing (K := K) base
  let : IsIntegralClosure target.valuation.valuationSubring
      base.valuation.valuationSubring L := by
    change IsIntegralClosure target.valuationSubring base.valuationSubring L
    infer_instance
  let : Module.Finite base.valuation.valuationSubring
      target.valuation.valuationSubring :=
    moduleFinite_valuationSubring_of_isIntegralClosure
      (L := L) base.valuation target.valuation
  intro Gamma' _ v' hExt
  let : base.valuation.HasExtension v' := hExt
  let : IsIntegralClosure v'.valuationSubring base.valuation.valuationSubring L :=
    @hintegral Gamma' inferInstance v' hExt inferInstance
  let : Module.Finite base.valuation.valuationSubring v'.valuationSubring :=
    moduleFinite_valuationSubring_of_isIntegralClosure
      (L := L) base.valuation v'
  exact
    valuation_isEquiv_of_hasExtension_of_moduleFinite
      (L := L) base.valuation target.valuation v'

/-- If the chosen target valuation ring and every comparison valuation ring
extending the base valuation are integral over the base valuation ring, then
the valuation extension is unique.

This is the non-certificate Henselian frontier reduction: to prove uniqueness
over a Henselian base it is now enough to prove the actual integrality of each
extension valuation ring, because the preceding Chevalley bridge identifies
such valuation rings with the actual integral closure. -/
theorem hasUniqueValuationExtension_of_forall_isIntegral
    [Algebra.IsSeparable K L]
    [Algebra.IsIntegral base.valuationSubring target.valuationSubring]
    (hintegral :
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
          [Algebra base.valuation.valuationSubring v'.valuationSubring] →
          Algebra.IsIntegral base.valuation.valuationSubring v'.valuationSubring) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let : Algebra.IsIntegral base.valuation.valuationSubring
      target.valuation.valuationSubring := by
    change Algebra.IsIntegral base.valuationSubring target.valuationSubring
    infer_instance
  let : IsNoetherianRing base.valuationSubring :=
    base_valuationSubring_isNoetherianRing (K := K) base
  let : IsIntegralClosure target.valuation.valuationSubring
      base.valuation.valuationSubring L :=
    valuationSubring_isIntegralClosure_of_isIntegral
      (L := L) base.valuation target.valuation
  let : Module.Finite base.valuation.valuationSubring
      target.valuation.valuationSubring :=
    moduleFinite_valuationSubring_of_isIntegralClosure
      (L := L) base.valuation target.valuation
  intro Gamma' _ v' hExt
  let : base.valuation.HasExtension v' := hExt
  let : Algebra.IsIntegral base.valuation.valuationSubring v'.valuationSubring :=
    @hintegral Gamma' inferInstance v' hExt inferInstance
  let : IsIntegralClosure v'.valuationSubring base.valuation.valuationSubring L :=
    valuationSubring_isIntegralClosure_of_isIntegral
      (L := L) base.valuation v'
  let : Module.Finite base.valuation.valuationSubring v'.valuationSubring :=
    moduleFinite_valuationSubring_of_isIntegralClosure
      (L := L) base.valuation v'
  exact
    valuation_isEquiv_of_hasExtension_of_moduleFinite
      (L := L) base.valuation target.valuation v'

omit [FiniteDimensional K L] in
open ValuationTheory.DiscreteValuationField.Valuation renaming
  integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension →
    integralClosureValuationSubring_le_of_hasExtension in
/-- Valuation-ring form of the Henselian uniqueness frontier.

If the actual integral closure of the base valuation ring in `L` has the
valuation-ring dichotomy, and every valuation extension is a local overring of
that integral-closure valuation subring, then the base valuation has a unique
extension to `L` up to mathlib valuation equivalence.

The remaining Henselian theorem is not hidden in a certificate here: it is
precisely the proof of the dichotomy and local-overring condition from the
Henselian hypotheses.  This theorem performs the actual Chevalley plus
valuation-overring collapse step. -/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_local_inclusion
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (htargetLocal :
      IsLocalHom
        ((integralClosureValuationSubringOfMemOrInv
            (L := L) base.valuation hval).inclusion
          target.valuation.valuationSubring
          (integralClosureValuationSubring_le_of_hasExtension
            (L := L) base.valuation target.valuation hval)))
    (hlocal :
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
          IsLocalHom
            ((integralClosureValuationSubringOfMemOrInv
                (L := L) base.valuation hval).inclusion
              v'.valuationSubring
              (integralClosureValuationSubring_le_of_hasExtension
                (L := L) base.valuation v' hval))) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let B :=
    integralClosureValuationSubringOfMemOrInv
      (L := L) base.valuation hval
  have htarget_le : B ≤ target.valuation.valuationSubring :=
    integralClosureValuationSubring_le_of_hasExtension
      (L := L) base.valuation target.valuation hval
  have htarget_eq : target.valuation.valuationSubring = B := by
    let : IsLocalHom (B.inclusion target.valuation.valuationSubring htarget_le) :=
      htargetLocal
    exact
      valuationSubring_eq_of_le_of_inclusion_isLocalHom
        B target.valuation.valuationSubring htarget_le
  intro Gamma' _ v' hExt
  let : base.valuation.HasExtension v' := hExt
  have hv_le : B ≤ v'.valuationSubring :=
    integralClosureValuationSubring_le_of_hasExtension
      (L := L) base.valuation v' hval
  have hv_eq : v'.valuationSubring = B := by
    let : IsLocalHom (B.inclusion v'.valuationSubring hv_le) :=
      @hlocal Gamma' inferInstance v' hExt
    exact
      valuationSubring_eq_of_le_of_inclusion_isLocalHom
        B v'.valuationSubring hv_le
  have hSubring : target.valuation.valuationSubring = v'.valuationSubring :=
    htarget_eq.trans hv_eq.symm
  exact valuation_isEquiv_of_valuationSubring_eq target v' hSubring

omit [FiniteDimensional K L] in
open ValuationTheory.DiscreteValuationField.Valuation renaming
  integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension →
    integralClosureValuationSubring_le_of_hasExtension in
/-- Center-prime form of the Henselian uniqueness frontier.

If the actual integral closure of the base valuation ring is a valuation ring,
and the center of every extension valuation ring on that integral-closure
valuation ring is the maximal ideal, then the extension valuation is unique.

This is the exact prime-theoretic step that remains after proving the
Henselian valuative dichotomy: the hypotheses are the center equalities
the Henselian finite-extension theorem must supply, not local-map or
certificate-style substitutes. -/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_center_eq_maximalIdeal
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (htargetCenter :
      ValuationSubring.idealOfLE
        (integralClosureValuationSubringOfMemOrInv
          (L := L) base.valuation hval)
        target.valuation.valuationSubring
        (integralClosureValuationSubring_le_of_hasExtension
          (L := L) base.valuation target.valuation hval) =
        IsLocalRing.maximalIdeal
          (integralClosureValuationSubringOfMemOrInv
            (L := L) base.valuation hval))
    (hcenter :
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
          ValuationSubring.idealOfLE
            (integralClosureValuationSubringOfMemOrInv
              (L := L) base.valuation hval)
            v'.valuationSubring
            (integralClosureValuationSubring_le_of_hasExtension
              (L := L) base.valuation v' hval) =
            IsLocalRing.maximalIdeal
              (integralClosureValuationSubringOfMemOrInv
                (L := L) base.valuation hval)) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let B :=
    integralClosureValuationSubringOfMemOrInv
      (L := L) base.valuation hval
  have htarget_le : B ≤ target.valuation.valuationSubring :=
    integralClosureValuationSubring_le_of_hasExtension
      (L := L) base.valuation target.valuation hval
  have htarget_eq : target.valuation.valuationSubring = B :=
    valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdeal
      B target.valuation.valuationSubring htarget_le
      (by simpa [B, htarget_le] using htargetCenter)
  intro Gamma' _ v' hExt
  let : base.valuation.HasExtension v' := hExt
  have hv_le : B ≤ v'.valuationSubring :=
    integralClosureValuationSubring_le_of_hasExtension
      (L := L) base.valuation v' hval
  have hv_eq : v'.valuationSubring = B :=
    valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdeal
      B v'.valuationSubring hv_le
      (by simpa [B, hv_le] using (@hcenter Gamma' inferInstance v' hExt))
  have hSubring : target.valuation.valuationSubring = v'.valuationSubring :=
    htarget_eq.trans hv_eq.symm
  exact valuation_isEquiv_of_valuationSubring_eq target v' hSubring

omit [FiniteDimensional K L] in
open ValuationTheory.DiscreteValuationField.Valuation renaming
  integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension →
    integralClosureValuationSubring_le_of_hasExtension in
/-- Prime-uniqueness form of the Henselian uniqueness frontier.

After the actual integral closure has been turned into a valuation subring, it
is enough to prove that every prime of that valuation subring whose contraction
to the base valuation ring is the base maximal ideal is itself the maximal
ideal.  The center of each extension valuation ring has exactly that
contraction, so this theorem converts the Henselian local prime-uniqueness
statement into uniqueness of valuation extensions. -/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_unique_primes_over_base_maximal
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (hunique :
      let B :=
        integralClosureValuationSubringOfMemOrInv
          (L := L) base.valuation hval
      let i : base.valuationSubring →+* B :=
        integralClosureValuationSubringIntegerMapOfMemOrInv
          (K := K) (L := L) base hval
      ∀ P : Ideal B, P.IsPrime → P.comap i = base.maximalIdeal →
        P = IsLocalRing.maximalIdeal B) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let B :=
    integralClosureValuationSubringOfMemOrInv
      (L := L) base.valuation hval
  let i : base.valuationSubring →+* B :=
    integralClosureValuationSubringIntegerMapOfMemOrInv
      (K := K) (L := L) base hval
  refine
    (hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_center_eq_maximalIdeal
      (K := K) (L := L) (base := base) (target := target)  hval ?_ ?_ :
        HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target))
  · let htarget_le : B ≤ target.valuation.valuationSubring :=
      integralClosureValuationSubring_le_of_hasExtension
        (L := L) base.valuation target.valuation hval
    exact hunique
      (ValuationSubring.idealOfLE B target.valuation.valuationSubring htarget_le)
      (by infer_instance)
      (by
        simpa [B, htarget_le, i] using
          idealOfLE_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
            (K := K) (L := L) base target.valuation hval)
  · intro Gamma' _ v' hExt
    let : base.valuation.HasExtension v' := hExt
    let hv_le : B ≤ v'.valuationSubring :=
      integralClosureValuationSubring_le_of_hasExtension
        (L := L) base.valuation v' hval
    exact hunique
      (ValuationSubring.idealOfLE B v'.valuationSubring hv_le)
      (by infer_instance)
      (by
        simpa [B, hv_le, i] using
          idealOfLE_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
            (K := K) (L := L) base v' hval)

/-- Finite-separable form of the Henselian uniqueness bridge.

After the Henselian part proves the valuative dichotomy for the actual
integral closure, finite separability supplies the prime uniqueness over the
base maximal ideal by Dedekind theory.  Thus no separate local-map, center
equality, integral-inclusion, or module-finiteness certificates are needed to
deduce uniqueness of the valuation extension. -/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv
    [Algebra.IsSeparable K L]
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) :=
  (hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_unique_primes_over_base_maximal
    base target)
    hval
    (by
      let B :=
        integralClosureValuationSubringOfMemOrInv
          (L := L) base.valuation hval
      let i : base.valuationSubring →+* B :=
        integralClosureValuationSubringIntegerMapOfMemOrInv
          (K := K) (L := L) base hval
      change ∀ P : Ideal B, P.IsPrime → P.comap i = base.maximalIdeal →
        P = IsLocalRing.maximalIdeal B
      intro P hP hcomap
      exact
        prime_eq_maximalIdeal_of_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
          (K := K) (L := L) (base := base) hval P hP hcomap)

/-- Finite-separable uniqueness once the chosen target valuation ring has been
identified as the actual integral closure of the base valuation ring.

The proof first turns the integral-closure identification into the valuative
dichotomy for `integralClosure base.valuationSubring L`; the finite-separable
Dedekind/local bridge above then supplies uniqueness of all valuation
extensions. -/
theorem hasUniqueValuationExtension_of_target_valuationSubring_isIntegralClosure
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    [IsIntegralClosure target.valuationSubring base.valuationSubring L] :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) :=
  (hasUniqueValuationExtension_of_integralClosure_mem_or_inv base target)
    (integralClosure_mem_or_inv_of_target_valuationSubring_isIntegralClosure
      (K := K) (L := L) base target)

/-- Finite-separable uniqueness once the chosen target valuation ring is
module-finite over the base valuation ring.

This is a theorem-level bridge, not a certificate package: module-finiteness
identifies the target valuation ring with the actual integral closure, and the
preceding theorem converts that identification into uniqueness of valuation
extensions. -/
theorem hasUniqueValuationExtension_of_target_moduleFinite
    [Algebra.IsSeparable K L]
    [Module.Finite base.valuationSubring target.valuationSubring]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L :=
    target_valuationSubring_isIntegralClosure_of_moduleFinite
      (K := K) (L := L) base target
  exact
    (hasUniqueValuationExtension_of_target_valuationSubring_isIntegralClosure
      (K := K) (L := L) (base := base) (target := target)  :
        HasUniqueValuationExtension.{u, v, w, x, y}
          (base := base) (target := target))

/-- Finite-separable uniqueness once the actual integral closure is known to be
a valuation ring.

This is the local/DVR-facing form of the frontier: a Henselian proof may first
show that the finite integral closure is local, hence a valuation ring, and
then this theorem supplies uniqueness through the proven finite-separable
Dedekind/local bridge. -/
theorem hasUniqueValuationExtension_of_integralClosure_valuationRing
    [Algebra.IsSeparable K L]
    [ValuationRing (integralClosureIntegers base target)] :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) :=
  (hasUniqueValuationExtension_of_integralClosure_mem_or_inv base target)
    ((integralClosure_mem_or_inv_of_integralClosure_valuationRing base target))

/-- Finite-separable uniqueness once the actual integral closure is local.

This is the sharpened Henselian frontier: after the Henselian argument proves
that the finite integral closure is a local ring, Dedekind theory makes it a
valuation ring and the valuative-dichotomy bridge above supplies uniqueness of
all valuation extensions. -/
theorem hasUniqueValuationExtension_of_integralClosure_isLocalRing
    [Algebra.IsSeparable K L]
    [IsLocalRing (integralClosureIntegers base target)] :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) :=
  (hasUniqueValuationExtension_of_integralClosure_mem_or_inv base target)
    (integralClosure_mem_or_inv_of_isLocalRing base target)

/-- Finite-separable uniqueness once the actual integral closure has a unique
prime over the base maximal ideal.

This is another Henselian-facing form: a Henselian argument may prove directly
that the finite integral closure has one prime above the base maximal ideal.
Integral going-up over the local base then makes the integral closure local, and
the local bridge above supplies uniqueness of valuation extensions. -/
theorem hasUniqueValuationExtension_of_integralClosure_primesOver_base_maximal_eq_singleton
    [Algebra.IsSeparable K L]
    (P : Ideal (integralClosureIntegers base target))
    (hP :
      Ideal.primesOver base.maximalIdeal (integralClosureIntegers base target) = {P}) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let : IsLocalRing (integralClosureIntegers base target) :=
    (integralClosure_isLocalRing_of_primesOver_base_maximal_eq_singleton base target) P hP
  exact
    (hasUniqueValuationExtension_of_integralClosure_isLocalRing
      (K := K) (L := L) (base := base) (target := target)  :
        HasUniqueValuationExtension.{u, v, w, x, y}
          (base := base) (target := target))

/-- Finite-separable uniqueness once the residue fiber over the base maximal
ideal has at most one prime.

The actual integral closure has a prime above the base maximal ideal by
going-up, and the fiber order-isomorphism identifies uniqueness in the fiber
with uniqueness of primes above the base maximal ideal.  The already-proved
singleton/local bridge then supplies valuation uniqueness. -/
theorem hasUniqueValuationExtension_of_integralClosure_base_maximal_fiber_subsingleton
    [Algebra.IsSeparable K L]
    [Subsingleton
      (PrimeSpectrum (base.maximalIdeal.Fiber (integralClosureIntegers base target)))] :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let : IsLocalRing (integralClosureIntegers base target) :=
    (integralClosure_isLocalRing_of_base_maximal_fiber_subsingleton base target)
  exact
    (hasUniqueValuationExtension_of_integralClosure_isLocalRing
      (K := K) (L := L) (base := base) (target := target)  :
        HasUniqueValuationExtension.{u, v, w, x, y}
          (base := base) (target := target))

/-- Finite-separable uniqueness from idempotent lifting in the residue fiber
over the base maximal ideal.

This is the current Henselian-facing frontier: a Henselian idempotent-lifting
argument can supply `hlift`; the finite Artinian fiber/topological bridge then
gives a unique prime above the base maximal ideal, localness of the actual
integral closure, and hence uniqueness of valuation extensions. -/
theorem hasUniqueValuationExtension_of_integralClosure_base_maximal_fiber_idempotents_lift
    [Algebra.IsSeparable K L]
    (hlift :
      ∀ e : base.maximalIdeal.Fiber (integralClosureIntegers base target),
        IsIdempotentElem e →
          ∃ b : (integralClosureIntegers base target),
            IsIdempotentElem b ∧
              Algebra.TensorProduct.includeRight b = e) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let : Subsingleton
      (PrimeSpectrum (base.maximalIdeal.Fiber (integralClosureIntegers base target))) :=
    (integralClosure_base_maximal_fiber_subsingleton_of_idempotents_lift base target) hlift
  exact
    (hasUniqueValuationExtension_of_integralClosure_base_maximal_fiber_subsingleton
      (K := K) (L := L) (base := base) (target := target)  :
        HasUniqueValuationExtension.{u, v, w, x, y}
          (base := base) (target := target))

/-- Finite-separable uniqueness from the Henselian-kernel idempotent-lifting
form for the residue fiber over the base maximal ideal.

This is a sharper Henselian-facing criterion than the raw `hlift` theorem:
Hensel's lemma for `X^2 - X` supplies the idempotent lift once the fiber map is
surjective and its kernel is a Henselian ideal of the actual integral closure. -/
theorem IntegralClosureFiber.unique_of_includeRight_surjective_henselianRing_ker
    [Algebra.IsSeparable K L]
    (hsurj :
      Function.Surjective
        (Algebra.TensorProduct.includeRight :
          (integralClosureIntegers base target) →ₐ[base.valuationSubring]
            base.maximalIdeal.Fiber (integralClosureIntegers base target)))
    [HenselianRing (integralClosureIntegers base target)
      (RingHom.ker
        ((Algebra.TensorProduct.includeRight :
          (integralClosureIntegers base target) →ₐ[base.valuationSubring]
            base.maximalIdeal.Fiber (integralClosureIntegers base target)) :
          (integralClosureIntegers base target) →+*
            base.maximalIdeal.Fiber (integralClosureIntegers base target)))] :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let : Subsingleton
      (PrimeSpectrum (base.maximalIdeal.Fiber (integralClosureIntegers base target))) :=
    (integralClosure_maximal_fiber_subsingleton_of_includeRight_surjective_henselian_ker
      base target)
      hsurj
  exact
    (hasUniqueValuationExtension_of_integralClosure_base_maximal_fiber_subsingleton
      (K := K) (L := L) (base := base) (target := target)  :
        HasUniqueValuationExtension.{u, v, w, x, y}
          (base := base) (target := target))

/-- Finite-separable uniqueness from the remaining Henselian-kernel input for
the residue-fiber `includeRight` map.

Surjectivity of `includeRight` is automatic over the local base valuation ring;
the only remaining Henselian-pair input in this criterion is that its kernel is
Henselian in the actual integral closure. -/
theorem
  hasUniqueValuationExtension_of_integralClosure_base_maximal_fiber_includeRight_henselianRing_ker
    [Algebra.IsSeparable K L]
    [HenselianRing (integralClosureIntegers base target)
      (RingHom.ker
        ((Algebra.TensorProduct.includeRight :
          (integralClosureIntegers base target) →ₐ[base.valuationSubring]
            base.maximalIdeal.Fiber (integralClosureIntegers base target)) :
          (integralClosureIntegers base target) →+*
            base.maximalIdeal.Fiber (integralClosureIntegers base target)))] :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let : Subsingleton
      (PrimeSpectrum (base.maximalIdeal.Fiber (integralClosureIntegers base target))) :=
    (integralClosure_base_maximal_fiber_subsingleton_of_includeRight_henselianRing_ker base target)
  exact
    (hasUniqueValuationExtension_of_integralClosure_base_maximal_fiber_subsingleton
      (K := K) (L := L) (base := base) (target := target)  :
        HasUniqueValuationExtension.{u, v, w, x, y}
          (base := base) (target := target))

/-- Finite-separable uniqueness from the natural Henselian-pair ideal in the
actual integral closure.

The kernel computation for the residue-fiber includeRight map identifies its
kernel with base.maximalIdeal.map; hence a Henselian proof for that natural
ideal is enough to enter the finite-extension uniqueness bridge. -/
theorem hasUniqueValuationExtension_of_integralClosure_base_maximal_map_henselianRing
    [Algebra.IsSeparable K L]
    [HenselianRing (integralClosureIntegers base target)
      (base.maximalIdeal.map
        (algebraMap base.valuationSubring (integralClosureIntegers base target)))] :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let : Subsingleton
      (PrimeSpectrum (base.maximalIdeal.Fiber (integralClosureIntegers base target))) :=
    (integralClosure_base_maximal_fiber_subsingleton_of_henselianRing_maximalIdeal_map base target)
  exact
    (hasUniqueValuationExtension_of_integralClosure_base_maximal_fiber_subsingleton
      (K := K) (L := L) (base := base) (target := target)  :
        HasUniqueValuationExtension.{u, v, w, x, y}
          (base := base) (target := target))


/-- Finite separable extensions of complete DVFs have a unique extension of the
base valuation, up to mathlib's valuation equivalence.

The proof routes through the actual integral closure: finite-module completeness
makes the ideal generated by the base maximal ideal Henselian there, and the
residue-fiber idempotent argument collapses the possible primes above the base
maximal ideal. -/
theorem hasUniqueValuationExtension_of_finite_separable
    [Algebra.IsSeparable K L] :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let : HenselianRing (integralClosureIntegers base target)
      (base.maximalIdeal.map
        (algebraMap base.valuationSubring (integralClosureIntegers base target))) :=
    (integralClosure_base_maximal_map_henselianRing base target)
  exact
    (hasUniqueValuationExtension_of_integralClosure_base_maximal_map_henselianRing
      (K := K) (L := L) (base := base) (target := target)  :
        HasUniqueValuationExtension.{u, v, w, x, y}
          (base := base) (target := target))

/-- In a finite separable extension of complete DVFs, uniqueness also holds
after forgetting both fields to Henselian DVFs. -/
theorem henselian_hasUniqueValuationExtension_of_finite_separable
    [Algebra.IsSeparable K L] :
    HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y}
      base.toHenselianDVF target.toHenselianDVF :=
  hasUniqueValuationExtension_toHenselianDVF base target
    ((hasUniqueValuationExtension_of_finite_separable base target) :
      HasUniqueValuationExtension.{u, v, w, x, y}
        (base := base) (target := target))

/-- In a finite separable extension of complete DVFs, the actual integral
closure of the base valuation ring is itself a valuation ring. -/
theorem integralClosure_mem_or_inv_of_finite_separable
    (target : CompleteDVF.{w, x} L)
    [Algebra.IsSeparable K L] :
    ∀ z : L,
      z ∈ (integralClosure base.valuationSubring L).toSubring ∨
        z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring := by
  let : HenselianRing (integralClosureIntegers base target)
      (base.maximalIdeal.map
        (algebraMap base.valuationSubring (integralClosureIntegers base target))) :=
    (integralClosure_base_maximal_map_henselianRing base target)
  let : Subsingleton
      (PrimeSpectrum (base.maximalIdeal.Fiber (integralClosureIntegers base target))) :=
    (integralClosure_base_maximal_fiber_subsingleton_of_henselianRing_maximalIdeal_map base target)
  let : IsLocalRing (integralClosureIntegers base target) :=
    (integralClosure_isLocalRing_of_base_maximal_fiber_subsingleton base target)
  exact (integralClosure_mem_or_inv_of_isLocalRing base target)

omit [FiniteDimensional K L] in
open ValuationTheory.DiscreteValuationField.Valuation renaming
  integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension →
    integralClosureValuationSubring_le_of_hasExtension in
/-- Integral-inclusion form of the Henselian uniqueness frontier.

Once the actual integral closure has been shown to be a valuation ring, it is
enough to prove that the inclusions from that valuation ring into every
extension valuation ring are integral.  The center equalities needed for the
valuation-overring collapse then follow from going-up for integral maps between
local rings, not from a separate center certificate. -/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_integral_inclusion
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (htargetIntegral :
      let B :=
        integralClosureValuationSubringOfMemOrInv
          (L := L) base.valuation hval
      let htarget_le : B ≤ target.valuation.valuationSubring :=
        integralClosureValuationSubring_le_of_hasExtension
          (L := L) base.valuation target.valuation hval
      (B.inclusion target.valuation.valuationSubring htarget_le).IsIntegral)
    (hintegral :
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
          let B :=
            integralClosureValuationSubringOfMemOrInv
              (L := L) base.valuation hval
          let hv_le : B ≤ v'.valuationSubring :=
            integralClosureValuationSubring_le_of_hasExtension
              (L := L) base.valuation v' hval
          (B.inclusion v'.valuationSubring hv_le).IsIntegral) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  refine
    (hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_center_eq_maximalIdeal
      base target)
      hval ?_ ?_
  · let B :=
      integralClosureValuationSubringOfMemOrInv
        (L := L) base.valuation hval
    let htarget_le : B ≤ target.valuation.valuationSubring :=
      integralClosureValuationSubring_le_of_hasExtension
        (L := L) base.valuation target.valuation hval
    exact idealOfLE_eq_maximalIdeal_of_isIntegral B target.valuation.valuationSubring
      htarget_le (by simpa [B, htarget_le] using htargetIntegral)
  · intro Gamma' _ v' hExt
    let : base.valuation.HasExtension v' := hExt
    let B :=
      integralClosureValuationSubringOfMemOrInv
        (L := L) base.valuation hval
    let hv_le : B ≤ v'.valuationSubring :=
      integralClosureValuationSubring_le_of_hasExtension
        (L := L) base.valuation v' hval
    exact idealOfLE_eq_maximalIdeal_of_isIntegral B v'.valuationSubring hv_le
      (by simpa [B, hv_le] using (@hintegral Gamma' inferInstance v' hExt))

omit [FiniteDimensional K L] in
open ValuationTheory.DiscreteValuationField.Valuation renaming
  integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension →
    integralClosureValuationSubring_le_of_hasExtension in
/-- Finite-inclusion form of the Henselian uniqueness frontier.

This is useful when the Henselian argument proves finite generation of the
valuation-overring inclusions rather than integrality directly. -/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_finite_inclusion
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (htargetFinite :
      let B :=
        integralClosureValuationSubringOfMemOrInv
          (L := L) base.valuation hval
      let htarget_le : B ≤ target.valuation.valuationSubring :=
        integralClosureValuationSubring_le_of_hasExtension
          (L := L) base.valuation target.valuation hval
      (B.inclusion target.valuation.valuationSubring htarget_le).Finite)
    (hfinite :
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
          let B :=
            integralClosureValuationSubringOfMemOrInv
              (L := L) base.valuation hval
          let hv_le : B ≤ v'.valuationSubring :=
            integralClosureValuationSubring_le_of_hasExtension
              (L := L) base.valuation v' hval
          (B.inclusion v'.valuationSubring hv_le).Finite) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  refine
    (hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_integral_inclusion base
      target)
      hval ?_ ?_
  · let B :=
      integralClosureValuationSubringOfMemOrInv
        (L := L) base.valuation hval
    let htarget_le : B ≤ target.valuation.valuationSubring :=
      integralClosureValuationSubring_le_of_hasExtension
        (L := L) base.valuation target.valuation hval
    have htargetFinite' :
        (B.inclusion target.valuation.valuationSubring htarget_le).Finite := by
      simpa [B, htarget_le] using htargetFinite
    exact htargetFinite'.to_isIntegral
  · intro Gamma' _ v' hExt
    let : base.valuation.HasExtension v' := hExt
    let B :=
      integralClosureValuationSubringOfMemOrInv
        (L := L) base.valuation hval
    let hv_le : B ≤ v'.valuationSubring :=
      integralClosureValuationSubring_le_of_hasExtension
        (L := L) base.valuation v' hval
    have hvFinite :
        (B.inclusion v'.valuationSubring hv_le).Finite := by
      simpa [B, hv_le] using
        (@hfinite Gamma' inferInstance v' hExt)
    exact hvFinite.to_isIntegral

omit [FiniteDimensional K L] in
open ValuationTheory.DiscreteValuationField.Valuation renaming
  integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension →
    integralClosureValuationSubring_le_of_hasExtension in
/-- Elementwise center form of the Henselian uniqueness frontier.

After proving that the actual integral closure is a valuation ring, it is
enough to check centers by maximal-ideal membership along the inclusions into
the target valuation ring and every comparison extension valuation ring.  This
is the form closest to the remaining Henselian argument: one proves an
element of the integral closure is nonunit exactly when its image in the
extension valuation ring is nonunit, and the valuation-overring collapse is
then automatic. -/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_center_mem_iff
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (htargetCenterMem :
      let B :=
        integralClosureValuationSubringOfMemOrInv
          (L := L) base.valuation hval
      let htarget_le : B ≤ target.valuation.valuationSubring :=
        integralClosureValuationSubring_le_of_hasExtension
          (L := L) base.valuation target.valuation hval
      ∀ x : B,
        B.inclusion target.valuation.valuationSubring htarget_le x ∈
            IsLocalRing.maximalIdeal target.valuation.valuationSubring ↔
          x ∈ IsLocalRing.maximalIdeal B)
    (hcenterMem :
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
          let B :=
            integralClosureValuationSubringOfMemOrInv
              (L := L) base.valuation hval
          let hv_le : B ≤ v'.valuationSubring :=
            integralClosureValuationSubring_le_of_hasExtension
              (L := L) base.valuation v' hval
          ∀ x : B,
            B.inclusion v'.valuationSubring hv_le x ∈
                IsLocalRing.maximalIdeal v'.valuationSubring ↔
              x ∈ IsLocalRing.maximalIdeal B) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  refine
    (hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_center_eq_maximalIdeal
      (K := K) (L := L) (base := base) (target := target)  hval ?_ ?_ :
        HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target))
  · let B :=
      integralClosureValuationSubringOfMemOrInv
        (L := L) base.valuation hval
    let htarget_le : B ≤ target.valuation.valuationSubring :=
      integralClosureValuationSubring_le_of_hasExtension
        (L := L) base.valuation target.valuation hval
    exact
      idealOfLE_eq_maximalIdeal_of_mem_maximalIdeal_iff
        B target.valuation.valuationSubring htarget_le
        (by simpa [B, htarget_le] using htargetCenterMem)
  · intro Gamma' _ v' hExt
    let : base.valuation.HasExtension v' := hExt
    let B :=
      integralClosureValuationSubringOfMemOrInv
        (L := L) base.valuation hval
    let hv_le : B ≤ v'.valuationSubring :=
      integralClosureValuationSubring_le_of_hasExtension
        (L := L) base.valuation v' hval
    exact
      idealOfLE_eq_maximalIdeal_of_mem_maximalIdeal_iff
        B v'.valuationSubring hv_le
        (by simpa [B, hv_le] using (@hcenterMem Gamma' inferInstance v' hExt))

omit [FiniteDimensional K L] in
open ValuationTheory.DiscreteValuationField.Valuation renaming
  integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension →
    integralClosureValuationSubring_le_of_hasExtension in
/-- One-sided elementwise center form of the Henselian uniqueness frontier.

For inclusions of local rings, the implication from target nonunit to source
nonunit is automatic.  Thus, after proving that the actual integral closure is
a valuation ring, the remaining center work is only to show that elements in the
maximal ideal of the integral-closure valuation ring map into the maximal ideals
of the extension valuation rings. -/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_center_mem
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (htargetCenterMem :
      let B :=
        integralClosureValuationSubringOfMemOrInv
          (L := L) base.valuation hval
      let htarget_le : B ≤ target.valuation.valuationSubring :=
        integralClosureValuationSubring_le_of_hasExtension
          (L := L) base.valuation target.valuation hval
      ∀ x : B,
        x ∈ IsLocalRing.maximalIdeal B →
          B.inclusion target.valuation.valuationSubring htarget_le x ∈
            IsLocalRing.maximalIdeal target.valuation.valuationSubring)
    (hcenterMem :
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
          let B :=
            integralClosureValuationSubringOfMemOrInv
              (L := L) base.valuation hval
          let hv_le : B ≤ v'.valuationSubring :=
            integralClosureValuationSubring_le_of_hasExtension
              (L := L) base.valuation v' hval
          ∀ x : B,
            x ∈ IsLocalRing.maximalIdeal B →
              B.inclusion v'.valuationSubring hv_le x ∈
                IsLocalRing.maximalIdeal v'.valuationSubring) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  refine
    (hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_center_mem_iff base target)
      hval ?_ ?_
  · let B :=
      integralClosureValuationSubringOfMemOrInv
        (L := L) base.valuation hval
    let htarget_le : B ≤ target.valuation.valuationSubring :=
      integralClosureValuationSubring_le_of_hasExtension
        (L := L) base.valuation target.valuation hval
    change ∀ x : B,
      B.inclusion target.valuation.valuationSubring htarget_le x ∈
          IsLocalRing.maximalIdeal target.valuation.valuationSubring ↔
        x ∈ IsLocalRing.maximalIdeal B
    intro x
    constructor
    · intro hx
      exact mem_maximalIdeal_of_map_mem_maximalIdeal
        (B.inclusion target.valuation.valuationSubring htarget_le) hx
    · intro hx
      simpa [B, htarget_le] using htargetCenterMem x hx
  · intro Gamma' _ v' hExt
    let : base.valuation.HasExtension v' := hExt
    let B :=
      integralClosureValuationSubringOfMemOrInv
        (L := L) base.valuation hval
    let hv_le : B ≤ v'.valuationSubring :=
      integralClosureValuationSubring_le_of_hasExtension
        (L := L) base.valuation v' hval
    change ∀ x : B,
      B.inclusion v'.valuationSubring hv_le x ∈
          IsLocalRing.maximalIdeal v'.valuationSubring ↔
        x ∈ IsLocalRing.maximalIdeal B
    intro x
    constructor
    · intro hx
      exact mem_maximalIdeal_of_map_mem_maximalIdeal
        (B.inclusion v'.valuationSubring hv_le) hx
    · intro hx
      simpa [B, hv_le] using
        (@hcenterMem Gamma' inferInstance v' hExt x hx)

omit [FiniteDimensional K L] [base.valuation.HasExtension target.valuation] in
/-- The valuation-subring equality consequence of unique valuation extension. -/
theorem valuationSubring_eq_of_hasUniqueValuationExtension
    (huniq : HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target))
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'] :
    target.valuation.valuationSubring = v'.valuationSubring :=
  valuationSubring_eq_of_valuation_isEquiv target (@huniq Gamma' _ v' _)

omit [FiniteDimensional K L] [base.valuation.HasExtension target.valuation] in
/-- Unique extension of the base valuation is equivalent to equality of the
valuation subring with every extension valuation. -/
theorem hasUniqueValuationExtension_iff_forall_valuationSubring_eq
     :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) ↔
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
          target.valuation.valuationSubring = v'.valuationSubring := by
  constructor
  · intro huniq Gamma' _ v' _
    exact (valuationSubring_eq_of_hasUniqueValuationExtension base target) huniq v'
  · intro h
    exact (hasUniqueValuationExtension_of_forall_valuationSubring_eq base target)
      (by
        intro Gamma' _ v' _
        exact h v')

omit [FiniteDimensional K L] [base.valuation.HasExtension target.valuation] in
/-- Unique extension of the base valuation can be checked pointwise on
membership in valuation subrings. -/
theorem hasUniqueValuationExtension_iff_forall_mem_valuationSubring
     :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) ↔
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
          ∀ z : L, z ∈ target.valuation.valuationSubring ↔
            z ∈ v'.valuationSubring := by
  constructor
  · intro huniq Gamma' _ v' _ z
    rw [(valuationSubring_eq_of_hasUniqueValuationExtension base target) huniq v']
  · intro h
    rw [(hasUniqueValuationExtension_iff_forall_valuationSubring_eq base target)]
    intro Gamma' _ v' _
    exact (valuationSubring_eq_iff_mem_valuationSubring target v').2
      (@h Gamma' _ v' _)

/-- In a finite separable extension of complete DVFs, every extension valuation
is equivalent to the chosen target valuation. -/
theorem valuation_isEquiv_of_finite_separable
    [Algebra.IsSeparable K L]
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'] :
    target.valuation.IsEquiv v' :=
  ((hasUniqueValuationExtension_of_finite_separable base target) :
    HasUniqueValuationExtension.{u, v, w, x, y}
      (base := base) (target := target)) v'

/-- In a finite separable extension of complete DVFs, the chosen target
valuation subring equals the valuation subring of any extension valuation. -/
theorem valuationSubring_eq_of_finite_separable
    [Algebra.IsSeparable K L]
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'] :
    target.valuation.valuationSubring = v'.valuationSubring :=
  (valuationSubring_eq_of_hasUniqueValuationExtension base target)
    ((hasUniqueValuationExtension_of_finite_separable base target) :
      HasUniqueValuationExtension.{u, v, w, x, y}
        (base := base) (target := target)) v'

/-- Symmetric form of `valuationSubring_eq_of_finite_separable`, useful for
rewriting a comparison valuation back to the chosen target valuation ring. -/
theorem valuationSubring_eq_target_of_finite_separable
    [Algebra.IsSeparable K L]
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'] :
    v'.valuationSubring = target.valuation.valuationSubring :=
  ((valuationSubring_eq_of_finite_separable base target) v').symm

/-- Elementwise finite-separable comparison of the chosen target valuation
subring with any other extension valuation subring. -/
theorem mem_valuationSubring_iff_of_finite_separable
    [Algebra.IsSeparable K L]
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v']
    (z : L) :
    z ∈ target.valuation.valuationSubring ↔ z ∈ v'.valuationSubring := by
  rw [(valuationSubring_eq_of_finite_separable base target) v']

/-- Symmetric elementwise finite-separable comparison, useful when the
comparison valuation is the left-hand side. -/
theorem mem_target_valuationSubring_iff_of_finite_separable
    [Algebra.IsSeparable K L]
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v']
    (z : L) :
    z ∈ v'.valuationSubring ↔ z ∈ target.valuation.valuationSubring :=
  ((mem_valuationSubring_iff_of_finite_separable base target) v' z).symm

omit [FiniteDimensional K L] [base.valuation.HasExtension target.valuation] in
/-- Under unique extension, any valuation subring whose canonical valuation
extends the base valuation is the chosen target valuation ring. -/
theorem target_valuationSubring_eq_of_hasUniqueValuationExtension
    (huniq : HasUniqueValuationExtension.{u, v, w, x, w}
      (base := base) (target := target))
    (B : ValuationSubring L) [base.valuation.HasExtension B.valuation] :
    target.valuation.valuationSubring = B := by
  have hEquiv : target.valuation.IsEquiv B.valuation :=
    huniq B.valuation
  have hSubring :
      target.valuation.valuationSubring = B.valuation.valuationSubring :=
    (_root_.Valuation.isEquiv_iff_valuationSubring
      target.valuation B.valuation).1 hEquiv
  simpa [ValuationSubring.valuationSubring_valuation] using hSubring

omit [FiniteDimensional K L] [base.valuation.HasExtension target.valuation] in
/-- Under unique extension, the valuation subring produced by Chevalley's
construction is the chosen target valuation ring. -/
theorem exists_chevalley_valuationSubring_eq_target_of_hasUniqueValuationExtension
    (huniq : HasUniqueValuationExtension.{u, v, w, x, w}
      (base := base) (target := target)) :
    ∃ B : ValuationSubring L,
      ∃ hB : ∀ x : base.valuationSubring,
        algebraMap base.valuationSubring L x ∈ B.toSubring,
        IsLocalHom
          ((algebraMap base.valuationSubring L).codRestrict B.toSubring hB) ∧
        (∀ x : K, algebraMap K L x ∈ B.toSubring ↔
          x ∈ base.valuation.valuationSubring) ∧
        base.valuation.HasExtension B.valuation ∧
        target.valuation.valuationSubring = B := by
  obtain ⟨B, hB, hlocal, hpullback, hExt⟩ :=
    exists_extension_valuationSubring_with_hasExtension
      (L := L) base.valuation
  let : base.valuation.HasExtension B.valuation := hExt
  refine ⟨B, hB, hlocal, hpullback, hExt, ?_⟩
  exact target_valuationSubring_eq_of_hasUniqueValuationExtension
    (K := K) (L := L) (base := base) (target := target) huniq B

omit [FiniteDimensional K L] [base.valuation.HasExtension target.valuation] in
open ValuationTheory.DiscreteValuationField.Valuation renaming
  chevalley_exists_extension_valuation_with_pullback_integralClosure_local_data →
    chevalley_exists_extension_valuation_with_integralClosure in
/-- Under unique extension, the actual valuation produced by Chevalley's
theorem can be chosen together with all construction data and is equivalent to
the chosen target valuation.  This is the finite-extension frontier form of
Chevalley plus uniqueness: it does not merely return a valuation subring, but
keeps the extension valuation, exact base pullback, integral-closure
containment, local map, residue injection, valuation equivalence, and
valuation-ring equality for the same witness. -/
theorem exists_chevalley_extension_valuation_eq_target_of_hasUniqueValuationExtension
    (huniq : HasUniqueValuationExtension.{u, v, w, x, w}
      (base := base) (target := target)) :
    ∃ ΓL : Type w,
      ∃ _ : LinearOrderedCommGroupWithZero ΓL,
        ∃ vL : _root_.Valuation L ΓL,
          ∃ hExt : base.valuation.HasExtension vL,
            letI : base.valuation.HasExtension vL := hExt
            letI : Algebra base.valuationSubring vL.valuationSubring := by
              change Algebra base.valuation.valuationSubring vL.valuationSubring
              infer_instance
            letI : IsLocalHom
                (algebraMap base.valuationSubring vL.valuationSubring) := by
              exact Valuation.integerMap_isLocalHom_of_hasExtension
                base.valuation vL
            (∀ a : K, algebraMap K L a ∈ vL.valuationSubring ↔
              a ∈ base.valuation.valuationSubring) ∧
            (∀ z : integralClosure base.valuationSubring L,
              (z : L) ∈ vL.valuationSubring) ∧
            (IsLocalRing.maximalIdeal vL.valuationSubring).LiesOver
              (IsLocalRing.maximalIdeal base.valuationSubring) ∧
            IsLocalHom
              (algebraMap base.valuationSubring vL.valuationSubring) ∧
            Function.Injective
              (IsLocalRing.ResidueField.map
                (algebraMap base.valuationSubring vL.valuationSubring)) ∧
            target.valuation.IsEquiv vL ∧
            target.valuation.valuationSubring = vL.valuationSubring := by
  obtain ⟨ΓL, hΓL, vL, hExt, hpullback, hIntegral, hlies, hlocal,
      hResidue⟩ :=
    chevalley_exists_extension_valuation_with_integralClosure
      (L := L) base.valuation
  let : LinearOrderedCommGroupWithZero ΓL := hΓL
  let : base.valuation.HasExtension vL := hExt
  let : Algebra base.valuationSubring vL.valuationSubring := by
    change Algebra base.valuation.valuationSubring vL.valuationSubring
    infer_instance
  let : IsLocalHom
      (algebraMap base.valuationSubring vL.valuationSubring) := by
    exact Valuation.integerMap_isLocalHom_of_hasExtension
      base.valuation vL
  have hEquiv : target.valuation.IsEquiv vL :=
    @huniq ΓL inferInstance vL inferInstance
  have hSubring : target.valuation.valuationSubring = vL.valuationSubring :=
    valuationSubring_eq_of_valuation_isEquiv target hEquiv
  exact ⟨ΓL, inferInstance, vL, inferInstance, hpullback, hIntegral, hlies,
    hlocal, hResidue, hEquiv, hSubring⟩


/-- In a finite separable extension, any valuation subring whose valuation
extends the base valuation is the chosen target valuation ring. -/
theorem target_valuationSubring_eq_of_finite_separable
    [Algebra.IsSeparable K L]
    (B : ValuationSubring L) [base.valuation.HasExtension B.valuation] :
    target.valuation.valuationSubring = B := by
  exact target_valuationSubring_eq_of_hasUniqueValuationExtension
    (K := K) (L := L) (base := base) (target := target)
    ((hasUniqueValuationExtension_of_finite_separable base target) :
      HasUniqueValuationExtension.{u, v, w, x, w}
        (base := base) (target := target)) B

/-- In a finite separable extension, the chosen target valuation ring is the
actual integral closure of the base valuation ring in `L`. -/
theorem target_valuationSubring_isIntegralClosure_of_finite_separable
    [Algebra.IsSeparable K L]
    :
    IsIntegralClosure target.valuationSubring base.valuationSubring L := by
  let hval := (integralClosure_mem_or_inv_of_finite_separable base target)
  let B :=
    integralClosureValuationSubringOfMemOrInv
      (L := L) base.valuation hval
  let : base.valuation.HasExtension B.valuation :=
    integralClosureValuationSubringOfMemOrInv_hasExtension
      (L := L) base.valuation hval
  have htarget_eq : target.valuation.valuationSubring = B :=
    (target_valuationSubring_eq_of_finite_separable base target) B
  have hB : IsIntegralClosure B base.valuationSubring L :=
    integralClosureValuationSubringOfMemOrInv_isIntegralClosure
      (L := L) base.valuation hval
  change IsIntegralClosure target.valuation.valuationSubring base.valuationSubring L
  rw [htarget_eq]
  exact hB

/-- Module-finiteness of the target valuation ring in a finite separable
extension, with no separate integral-closure certificate. -/
theorem moduleFinite_target_valuationSubring_of_finite_separable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    Module.Finite base.valuationSubring target.valuationSubring := by
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L :=
    (target_valuationSubring_isIntegralClosure_of_finite_separable base target)
  exact moduleFinite_target_valuationSubring_of_isIntegralClosure
    (K := K) (L := L) base target

/-- In a finite separable complete-DVF extension, the chosen target maximal
ideal is the unique prime above the base maximal ideal. -/
theorem target_primesOver_base_maximal_eq_singleton_of_finite_separable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    Ideal.primesOver base.maximalIdeal target.valuationSubring =
      {target.maximalIdeal} := by
  let : Module.Finite base.valuationSubring target.valuationSubring :=
    (moduleFinite_target_valuationSubring_of_finite_separable base target)
  exact target_primesOver_base_maximal_eq_singleton_of_moduleFinite
    (K := K) (L := L) base target

/-- Cardinal form of
`target_primesOver_base_maximal_eq_singleton_of_finite_separable`. -/
theorem ncard_target_primesOver_base_maximal_eq_one_of_finite_separable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    (Ideal.primesOver base.maximalIdeal target.valuationSubring).ncard = 1 := by
  rw [(target_primesOver_base_maximal_eq_singleton_of_finite_separable base target)]
  exact Set.ncard_singleton target.maximalIdeal

/-- Torsion-freeness of the target valuation ring over the base valuation ring
in a finite separable extension, with no separate integral-closure
certificate. -/
theorem moduleIsTorsionFree_target_valuationSubring_of_finite_separable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    Module.IsTorsionFree base.valuationSubring target.valuationSubring := by
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L :=
    (target_valuationSubring_isIntegralClosure_of_finite_separable base target)
  let : IsFractionRing base.valuationSubring K :=
    base_valuationSubring_isFractionRing (K := K) base
  let : FaithfulSMul base.valuationSubring L :=
    FaithfulSMul.of_field_isFractionRing base.valuationSubring L K L
  let : Module.IsTorsionFree base.valuationSubring L := inferInstance
  exact IsIntegralClosure.isTorsionFree base.valuationSubring L

/-- Local-Dedekind fundamental identity for a finite separable extension,
stated directly for the chosen target valuation ring. -/
theorem ideal_ramificationIdx_mul_inertiaDeg_eq_finrank_of_finite_separable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal *
      target.maximalIdeal.inertiaDeg base.valuationSubring = Module.finrank K L := by
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L :=
    (target_valuationSubring_isIntegralClosure_of_finite_separable base target)
  exact ideal_ramificationIdx_mul_inertiaDeg_eq_finrank_of_isIntegralClosure
    (K := K) (L := L) base target

/-- The canonical ramification index times residue degree is the field degree for a
finite separable extension, with no separate integral-closure certificate. -/
theorem ramificationIndex_mul_residueDegree_eq_degree_of_finite_separable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    (ValuedExtension.ramificationIndex base.toDVF target.toDVF) * (ValuedExtension.residueDegree
      base.toDVF target.toDVF) = (ValuedExtension.degree base.toDVF target.toDVF) := by
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L :=
    (target_valuationSubring_isIntegralClosure_of_finite_separable base target)
  exact (ramificationIndex_mul_residueDegree_eq_degree_of_isIntegralClosure base target)

/-- A finite separable valued extension is defectless. -/
theorem isDefectless_of_finite_separable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    ValuedExtension.IsDefectless base.toDVF target.toDVF := by
  change Module.finrank K L =
    Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal *
      target.maximalIdeal.inertiaDeg base.valuationSubring
  exact ((ideal_ramificationIdx_mul_inertiaDeg_eq_finrank_of_finite_separable base target)).symm

/-- In a finite separable extension, Chevalley's extension valuation can be
chosen so that its valuation subring is the target valuation ring. -/
theorem exists_chevalley_valuationSubring_eq_target_of_finite_separable
    [Algebra.IsSeparable K L] :
    ∃ B : ValuationSubring L,
      ∃ hB : ∀ x : base.valuationSubring,
        algebraMap base.valuationSubring L x ∈ B.toSubring,
        IsLocalHom
          ((algebraMap base.valuationSubring L).codRestrict B.toSubring hB) ∧
        (∀ x : K, algebraMap K L x ∈ B.toSubring ↔
          x ∈ base.valuation.valuationSubring) ∧
        base.valuation.HasExtension B.valuation ∧
        target.valuation.valuationSubring = B := by
  exact exists_chevalley_valuationSubring_eq_target_of_hasUniqueValuationExtension
    (K := K) (L := L) (base := base) (target := target)
    ((hasUniqueValuationExtension_of_finite_separable base target) :
      HasUniqueValuationExtension.{u, v, w, x, w}
        (base := base) (target := target))

/-- In a finite separable extension, Chevalley's extension valuation can be
chosen with all local/integral-closure data and equivalent to the target
valuation. -/
theorem exists_chevalley_extension_valuation_eq_target_of_finite_separable
    [Algebra.IsSeparable K L] :
    ∃ ΓL : Type w,
      ∃ _ : LinearOrderedCommGroupWithZero ΓL,
        ∃ vL : _root_.Valuation L ΓL,
          ∃ hExt : base.valuation.HasExtension vL,
            letI : base.valuation.HasExtension vL := hExt
            letI : Algebra base.valuationSubring vL.valuationSubring := by
              change Algebra base.valuation.valuationSubring vL.valuationSubring
              infer_instance
            letI : IsLocalHom
                (algebraMap base.valuationSubring vL.valuationSubring) := by
              exact Valuation.integerMap_isLocalHom_of_hasExtension
                base.valuation vL
            (∀ a : K, algebraMap K L a ∈ vL.valuationSubring ↔
              a ∈ base.valuation.valuationSubring) ∧
            (∀ z : integralClosure base.valuationSubring L,
              (z : L) ∈ vL.valuationSubring) ∧
            (IsLocalRing.maximalIdeal vL.valuationSubring).LiesOver
              (IsLocalRing.maximalIdeal base.valuationSubring) ∧
            IsLocalHom
              (algebraMap base.valuationSubring vL.valuationSubring) ∧
            Function.Injective
              (IsLocalRing.ResidueField.map
                (algebraMap base.valuationSubring vL.valuationSubring)) ∧
            target.valuation.IsEquiv vL ∧
            target.valuation.valuationSubring = vL.valuationSubring := by
  exact (exists_chevalley_extension_valuation_eq_target_of_hasUniqueValuationExtension base target)
    ((hasUniqueValuationExtension_of_finite_separable base target) :
      HasUniqueValuationExtension.{u, v, w, x, w}
        (base := base) (target := target))

/-- If the chosen target valuation ring is an actual integral closure of the base
valuation ring in `L`, it is canonically equivalent to mathlib's
`integralClosure`. -/
noncomputable def integralClosureEquivValuationSubring
    [Algebra base.valuationSubring L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    [IsIntegralClosure target.valuationSubring base.valuationSubring L] :
    (integralClosure base.valuationSubring L) ≃ₐ[base.valuationSubring]
      target.valuationSubring :=
  IsIntegralClosure.equiv base.valuationSubring
    (integralClosure base.valuationSubring L) L target.valuationSubring

end ValuedExtension
end DiscreteValuationField

end

end ValuationTheory
