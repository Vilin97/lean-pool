/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.SerrePairing.TailSpace
import LeanPool.JacobianDiffgeo.CanonicalForms
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# `pair`: the Serre pairing (Miranda's `Res_ω`), purely algebraic (serre-duality-cech, §2 D2)

Unit: serre-duality-cech (`docs/design/serre-duality-cech.md` §2 D2, §4.2).

**Adaptation to the quotient revision of `Jacobian/CanonicalForms/`.** The design's `pair` was
written against a raw `MForm` structure exposing `ω.coeffAt x z` directly; `MForm` is now a
quotient of `MFormData` (`Jacobian/CanonicalForms/Quotient.lean`) with no `coeffAt` field on
classes, only the *already lifted* reading maps `MForm.ord`/`resAt`/`laurentCoeffAt`. Since
`MForm.laurentCoeffAt Θ x k` is already exactly Miranda's `c_{-1-k}` read at `x` (chart-invariant,
proof-irrelevant in the choice of representative — `Jacobian/CanonicalForms/Quotient.lean`'s
`laurentCoeffAt_mk`), we define `pair` **directly** as the finite sum of Laurent coefficients
against the tail (the design's `pair_eq_finsum_sum`, i.e. Miranda's own boxed formula PDF 187),
rather than via `resAt` of an explicit representative product and `resAt_tail_mul`. This is the
SAME mathematical content (for any representative `θ` of `Θ`, `resAt_tail_mul` applied to
`θ.coeffAt x` recovers exactly this formula — see `pair_single`'s proof, which is the one place the
"residue of a tail-multiplied form" reading is exercised) with strictly less proof debt: the
τ-linearity of `pair` is packaged for free by `Finsupp.lsum` (no manual "extend to the union of two
supports" `finsum` bookkeeping, as the original design anticipated needing `finsum_add_distrib`
for).

The θ-linearity (`pair_add_left`/`pair_smul_left`) needs a small `Compat` fact not exported by
canonical-forms — `MForm.laurentCoeffAt` is additive/`ℂ`-linear in the class argument — proved here
via representatives + residue-calculus's `laurentCoeffAt_fun_add`/`_const_mul`/`_zero_fun`
(coordination note filed to `docs/requests/canonical-forms.md`).
-/

open scoped ContDiff Manifold

noncomputable section

namespace RS
namespace MForm

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Compat: `MForm.laurentCoeffAt` is `ℂ`-linear in the class argument -/

/-- Compat (`docs/requests/canonical-forms.md`): additivity of `laurentCoeffAt` in the class
argument, via representatives + residue-calculus's `laurentCoeffAt_fun_add`. -/
theorem laurentCoeffAt_add (Θ H : MForm X) (x : X) (k : ℤ) :
    (Θ + H).laurentCoeffAt x k = Θ.laurentCoeffAt x k + H.laurentCoeffAt x k := by
  obtain ⟨θ, rfl⟩ := MForm.exists_rep Θ
  obtain ⟨η, rfl⟩ := MForm.exists_rep H
  rw [MForm.mk_add]
  simp only [MForm.laurentCoeffAt_mk]
  exact RS.laurentCoeffAt_fun_add (θ.meromorphicAt_coeffAt x) (η.meromorphicAt_coeffAt x) k

/-- Compat (`docs/requests/canonical-forms.md`): `ℂ`-homogeneity of `laurentCoeffAt` in the class
argument, via representatives + residue-calculus's `laurentCoeffAt_const_mul`. -/
theorem laurentCoeffAt_smul (c : ℂ) (Θ : MForm X) (x : X) (k : ℤ) :
    (c • Θ).laurentCoeffAt x k = c * Θ.laurentCoeffAt x k := by
  obtain ⟨θ, rfl⟩ := MForm.exists_rep Θ
  rw [MForm.mk_smul]
  simp only [MForm.laurentCoeffAt_mk]
  exact RS.laurentCoeffAt_const_mul c k

@[simp] theorem laurentCoeffAt_zero (x : X) (k : ℤ) :
    (0 : MForm X).laurentCoeffAt x k = 0 := by
  rw [← MForm.mk_zero]
  simp only [MForm.laurentCoeffAt_mk]
  exact RS.laurentCoeffAt_zero_fun k

end MForm

namespace SerrePairing

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### `pairAt`: the per-point linear functional -/

/-- The per-point contribution to the pairing: a finite tail of Laurent exponents at `x`, read
against `θ`'s Laurent coefficients there (Miranda's `Res_x(r_x θ)` in coefficient form). Linear in
the tail-at-`x` argument by construction (`Finsupp.lsum`). -/
def pairAt (θ : MForm X) (x : X) : (ℤ →₀ ℂ) →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ (fun k => θ.laurentCoeffAt x (-1 - k) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ))

theorem pairAt_single (θ : MForm X) (x : X) (n : ℤ) (c : ℂ) :
    pairAt θ x (Finsupp.single n c) = c * θ.laurentCoeffAt x (-1 - n) := by
  change Finsupp.lsum ℂ (fun k => θ.laurentCoeffAt x (-1 - k) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ))
      (Finsupp.single n c) = _
  rw [Finsupp.lsum_single]
  change θ.laurentCoeffAt x (-1 - n) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ) c = _
  rw [LinearMap.id_apply, smul_eq_mul, mul_comm]

theorem pairAt_add_left (θ η : MForm X) (x : X) :
    pairAt (θ + η) x = pairAt θ x + pairAt η x := by
  apply Finsupp.lhom_ext
  intro n c
  rw [pairAt_single, LinearMap.add_apply, pairAt_single, pairAt_single, MForm.laurentCoeffAt_add]
  ring

theorem pairAt_smul_left (c : ℂ) (θ : MForm X) (x : X) :
    pairAt (c • θ) x = c • pairAt θ x := by
  apply Finsupp.lhom_ext
  intro n a
  rw [pairAt_single, LinearMap.smul_apply, pairAt_single, MForm.laurentCoeffAt_smul, smul_eq_mul]
  ring

/-! ### `pairTail`/`pairL`: the full tail-linear pairing, and `pair` -/

/-- `pair θ`, packaged as a genuine linear map `Tail X →ₗ[ℂ] ℂ` (Finsupp-summed over `x`). -/
def pairTail (θ : MForm X) : Tail X →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ (pairAt θ)

theorem pairTail_add_left (θ η : MForm X) :
    pairTail (θ + η) = pairTail θ + pairTail η := by
  apply Finsupp.lhom_ext
  intro p m
  rw [pairTail, pairTail, pairTail, Finsupp.lsum_single, LinearMap.add_apply,
    Finsupp.lsum_single, Finsupp.lsum_single]
  exact LinearMap.ext_iff.1 (pairAt_add_left θ η p) m

theorem pairTail_smul_left (c : ℂ) (θ : MForm X) :
    pairTail (c • θ) = c • pairTail θ := by
  apply Finsupp.lhom_ext
  intro p m
  rw [pairTail, pairTail, Finsupp.lsum_single, LinearMap.smul_apply, Finsupp.lsum_single]
  exact LinearMap.ext_iff.1 (pairAt_smul_left c θ p) m

/-- **The Serre pairing** (Miranda's `Res_ω`, purely algebraic): a meromorphic 1-form `θ` and an
ambient tail `τ`, paired by summing (over `τ`'s finite support) `θ`'s Laurent coefficients against
`τ`'s exponents. -/
def pair (θ : MForm X) (τ : Tail X) : ℂ := pairTail θ τ

/-- Packaged as a genuine bilinear map (matches the design's `pairL` export). -/
def pairL : MForm X →ₗ[ℂ] Tail X →ₗ[ℂ] ℂ where
  toFun := pairTail
  map_add' := pairTail_add_left
  map_smul' := pairTail_smul_left

@[simp] theorem pairL_apply (θ : MForm X) (τ : Tail X) : pairL θ τ = pair θ τ := rfl

theorem pair_add_left (θ η : MForm X) (τ : Tail X) : pair (θ + η) τ = pair θ τ + pair η τ := by
  change pairTail (θ + η) τ = pairTail θ τ + pairTail η τ
  rw [pairTail_add_left]
  rfl

theorem pair_smul_left (c : ℂ) (θ : MForm X) (τ : Tail X) : pair (c • θ) τ = c * pair θ τ := by
  change pairTail (c • θ) τ = c * pairTail θ τ
  rw [pairTail_smul_left, LinearMap.smul_apply, smul_eq_mul]

theorem pair_zero_left (τ : Tail X) : pair (0 : MForm X) τ = 0 := by
  have h := pair_smul_left (0 : ℂ) (0 : MForm X) τ
  simpa using h

theorem pair_add_right (θ : MForm X) (τ σ : Tail X) : pair θ (τ + σ) = pair θ τ + pair θ σ :=
  map_add (pairTail θ) τ σ

theorem pair_smul_right (θ : MForm X) (c : ℂ) (τ : Tail X) : pair θ (c • τ) = c * pair θ τ := by
  change pairTail θ (c • τ) = c * pairTail θ τ
  rw [map_smul, smul_eq_mul]

theorem pair_zero_right (θ : MForm X) : pair θ (0 : Tail X) = 0 :=
  map_zero (pairTail θ)

/-- The atom the injectivity witness (`Duality.lean`) uses directly. -/
theorem pair_single (θ : MForm X) (p : X) (n : ℤ) (c : ℂ) :
    pair θ (Tail.single p n c) = c * θ.laurentCoeffAt p (-1 - n) := by
  change pairTail θ (Tail.single p n c) = _
  change Finsupp.lsum ℂ (pairAt θ) (Finsupp.single p (Finsupp.single n c)) = _
  rw [Finsupp.lsum_single]
  exact pairAt_single θ p n c

end SerrePairing
end RS
