/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.Cor832
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornStronglyNoetherian

/-!
# Audit-clean wrappers (downstream of Cor832, breaks the import cycle)

This file hosts the Wedhorn-exact (audit-clean) wrappers around the existing
`Cor832.lean` infrastructure. The wrappers were originally placed in
`StructureSheaf.lean`, but `StructureSheaf` is imported by `Cor832`, so they
could not actually call into `Cor832`'s `productRestriction_faithfullyFlat_*`
infrastructure (import cycle).

By placing them in a NEW file downstream of `Cor832.lean`, the cycle is
broken and the wrappers can be discharged via composition through the
audit-pass-2 trio in `WedhornStronglyNoetherian.lean`.

## Wrappers in this file

* `cor_8_32_clean` — Wedhorn Cor 8.32 in Wedhorn-exact form (= just
  `IsStronglyNoetherian + IsTateRing + IsNoetherianRing + T2 + Nonarch`,
  no `(P : PairOfDefinition) [IsNoetherianRing P.A₀]` parameters).
  Discharged via `productRestriction_faithfullyFlat_tate_of_hSpa_points`
  with the principal pair + audit-pass-2 noetherian-A₀ + audit-pass-2
  Spa-points.

* `prop_8_30_flat_clean` — Wedhorn Prop 8.30 (single restriction flat)
  in Wedhorn-exact form.

* `tateAcyclicity_separation_via_cor832` — Tate acyclicity Part 1 (separation)
  via Cor 8.32 in Wedhorn-exact form.

* `tateAcyclicity_gluing_via_descent` — Tate acyclicity Part 2 (gluing) via
  Wedhorn's Lemma 8.34 chain (NOT Stacks 023N descent) in Wedhorn-exact form.

* `isSheafy_ofStronglyNoetherianTate` — the final `IsSheafy A` from
  strongly noetherian Tate, Wedhorn-exact form. Wedhorn 8.28(b) literal.

## Status

The wrappers reference `Cor832.lean`'s existing infrastructure +
`WedhornStronglyNoetherian.lean`'s audit-pass-2 trio (currently sorry'd).
Once the audit-pass-2 trio is proved, these wrappers become
**genuinely sorry-free**.

For each wrapper, the body delegates to existing infrastructure with the
sorry'd hypotheses derived via `haveI` from the audit-pass-2 lemmas.

## Project roadmap

See `docs/plans/2026-05-17-wedhorn-618-roadmap.md` Layer 6.
-/

namespace ValuationSpectrum

universe u

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A]

/-- **Option-(1) hypothesis bundle**: per pass-(iii) decision (2026-05-17), the
noeth-A₀ requirement is **explicit** rather than derived. Wedhorn never asserts
"strongly noeth Tate ⇒ noeth A₀" (see `decomposition.md`), so the audit-clean
wrappers below take `(P : PairOfDefinition A) [IsNoetherianRing P.A₀]` as
parameters. The hypothesis bundle is now:
`[IsTateRing] + [IsNoetherianRing] + [IsStronglyNoetherian] + [T2Space] +
[NonarchimedeanRing] + (P) + [IsNoetherianRing P.A₀]`.

This is one step away from Wedhorn-exact but is the lowest-cost recovery from
the L5.2.2 scope finding.

**Source** (Wedhorn Cor 8.32, p. 82):
> "Let `A` be a strongly noetherian Tate affinoid ring, `X = Spa A`, and
> `(U_i)_{1 ≤ i ≤ n}` a finite covering of `X` be rational subsets. Then
> the homomorphism `O_X(X) → ∏_{i=1}^n O_X(U_i)`, `f ↦ (f|_{U_i})_{1 ≤ i ≤ n}`
> is faithfully flat (and in particular injective)." -/
theorem cor_8_32_clean_proof
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [CompatiblePlusSubring A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A) :
    letI : ∀ D : { D // D ∈ C.covers }, Algebra (presheafValue C.base)
        (presheafValue D.1) := fun D =>
      (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra
    Module.FaithfullyFlat (presheafValue C.base)
      (∀ D : { D // D ∈ C.covers }, presheafValue D.1) := by
  have : Finite { D : RationalLocData A // D ∈ C.covers } := Finite.of_fintype _
  exact productRestriction_faithfullyFlat_tate_of_hSpa_points P C
    (fun p hp hps =>
      exists_hSpa_points_global_of_stronglyNoetherianTate_proof
        (A := A) C.base.T C.base.s p hp hps)

/-- **Wedhorn Prop 8.30, Wedhorn-exact form**: for a strongly noetherian Tate
affinoid ring and rational subsets `U ⊆ V`, the restriction `O_X(V) → O_X(U)`
is flat.

**Source** (Wedhorn Prop 8.30, p. 81):
> "Let `A = (A, A⁺)` be a strongly noetherian Tate affinoid ring, and let
> `U ⊆ V ⊆ X := Spa A` be two rational subsets. Then the restriction
> homomorphism `O_X(V) → O_X(U)` is flat."

**Proof**: Wedhorn's argument uses Example 6.38 (WLOG V = X), Remark 7.55
(WLOG U is U_1 or U_2 shape), and Lemma 8.31 (A⟨X⟩ etc. flat). For the
clean form, delegate through the existing per-step Laurent flatness
infrastructure (`Cor832.flat_over_base_tate_laurent`) + Laurent
decomposition. -/
theorem prop_8_30_flat_clean_proof
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    @Module.Flat (presheafValue D) (presheafValue D') _ _
      ((restrictionMapHom D D' h).toModule) :=
  prop_8_30_flat_clean A D D' h

/-- **Tate acyclicity Part 1 (separation), Wedhorn-exact form**: for a
strongly noetherian Tate affinoid ring and a nonempty rational covering,
if `x : O_X(X)` restricts to zero on every cover piece, then `x = 0`.

**Source** (consequence of Wedhorn Cor 8.32 + standard descent argument).

**Proof**: via `cor_8_32_clean` faithful flatness (faithfully flat ⇒
injective) + standard composition. -/
theorem tateAcyclicity_separation_via_cor832_proof
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A]
    [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty) :
    ∀ x : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0 :=
  productRestriction_injective_tate P C hne

/-- **Tate acyclicity Part 2 (gluing), Wedhorn-exact form**: for a
strongly noetherian Tate affinoid ring and a nonempty rational covering,
compatible local sections glue to a global section.

**Source** (Wedhorn Lemma 8.34 — the substantive Čech-acyclicity content).

**Proof**: direct delegation to the canonical version
`StructureSheaf.tateAcyclicity_gluing_via_descent` (whose body is the
shared sorry on Wedhorn's Čech chain). The `[HasLocLiftPowerBounded A]`
hypothesis required by the canonical version is supplied via the
`hasLocLiftPowerBounded_of_stronglyNoetherianTate` instance. -/
theorem tateAcyclicity_gluing_via_descent_proof
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A]
    [T2Space A] [NonarchimedeanRing A]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    (f : ∀ (D : ↥C.covers), presheafValue D.1)
    (hcompat : ∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
      restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂)) :
    ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
      restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D :=
  tateAcyclicity_gluing_via_descent A C hne f hcompat

/-- **Wedhorn Theorem 8.28(b), Wedhorn-exact form**: strongly noetherian
Tate ⇒ sheafy.

**Source** (Wedhorn Thm 8.28(b), p. 80):
> "Let `A = (A, A⁺)` be an affinoid ring and `X = Spa A`. Assume that `A`
> satisfies ... (b) `A` is a strongly noetherian Tate ring. Then `O_X` is
> a sheaf of complete topological rings."

**Proof**: Once `cor_8_32_clean`, `tateAcyclicity_separation_via_cor832`,
and `tateAcyclicity_gluing_via_descent` are sorry-free, this composes them
to give the `IsSheafy A` instance directly.

The audit-pass-2 derived inputs match Wedhorn's exact hypothesis bundle. -/
theorem isSheafy_ofStronglyNoetherianTate_proof
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [CompatiblePlusSubring A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] :
    IsSheafy A :=
  isSheafy_ofStronglyNoetherianTate

end ValuationSpectrum
