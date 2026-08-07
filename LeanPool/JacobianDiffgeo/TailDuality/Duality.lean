/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.TailDuality.Counting

/-!
# Miranda Lemma 3.6, the surjectivity endgame, and Serre duality (serre-duality-tails)

Unit: serre-duality-tails (`docs/design/serre-duality-tails.md` §6 P6/P7, orchestrator addendum
2026-07-08 re-basing).

* `mem_omegaSpace_of_vanishing_ker_trunc`: **MIRANDA LEMMA 3.6** (the order downgrade).
* `exists_pairT_eq`: **MIRANDA THM 3.3, surjectivity half**, via Lemma 3.4 + inverting `μ_{f₁}` +
  Lemma 3.6 applied twice (Miranda PDF 202–203).
* `resMap_surjective`/`resEquiv`: `resMap` is a linear ISOMORPHISM `Ω(-D) ≃ Dual(H1Tail D)`.
* The re-based export bank (orchestrator addendum: state duality against the TAIL `h¹`, do
  **not** block on `tailToH1`'s surjectivity/the Čech comparison):
  `i_neg_eq_h1T`, `l_sub_eq_h1T`, `h1T_zero_eq_l_K`, `h1T_zero_eq_genus`, `h1T_canonical`.

**Update (chiT-ledger closure pass): DELIVERED**, in `Jacobian/TailDuality/ChiLedger.lean` (not in
this file, to keep this file's own scope unchanged) — `chiT_eq_chiT_zero_add_degree`/
`chiT_single_add`, via exactly the sketch recorded here: `windowConnectT := H1Tail.mk D ∘ₗ
windowToT D D' h` (Cech's `Window D D'`/`windowMap`/`windowToT`, `Jacobian/Cech/Window.lean`,
`Jacobian/LaurentTail/TailSpace.lean`) plus a NEW descent `H1TailIncl` of `truncT`, both exactness
facts proved elementarily (no Čech `H1`/cochain machinery: `H1Tail D` being a literal coker of
`alphaL D`, not a colimit, makes both a DFinsupp/Submodule bookkeeping argument). See that file's
own docstring for the full account. riemann-roch (#28) now consumes `chiT`'s own ledger directly.
-/

open scoped ContDiff Manifold
open Set TopologicalSpace
open RS RS.LaurentTail

namespace RS.TailDuality

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [CompactSpace X] [ConnectedSpace X] [T1Space X] [DecidableEq X]

/-! ### Miranda Lemma 3.6 (the order downgrade) -/

omit [CompactSpace X] [T2Space X] in
/-- **MIRANDA LEMMA 3.6.** -/
theorem mem_omegaSpace_of_vanishing_ker_trunc {D₁ D₂ : RS.Divisor X} (h : D₁ ≤ D₂)
    {θ : MForm X} (hθ : θ ∈ MForm.OmegaSpace (-D₁))
    (hker : ∀ τ : T D₁, truncT h τ = 0 → pairT θ hθ τ = 0) :
    θ ∈ MForm.OmegaSpace (-D₂) := by
  by_cases hθ0 : θ = 0
  · rw [hθ0]; exact zero_mem _
  rw [MForm.mem_omegaSpace_iff]
  by_contra hcon
  push Not at hcon
  obtain ⟨p, hp⟩ := hcon
  rw [Divisor.neg_apply, neg_neg] at hp
  have hne : θ.ord p ≠ ⊤ := MForm.ord_ne_top hθ0 p
  set k := (θ.ord p).untop₀ with hk_def
  have hkeq : (k : WithTop ℤ) = θ.ord p := WithTop.coe_untop₀_of_ne_top hne
  have hD1p : D₁ p ≤ k := by
    have h1 := MForm.mem_omegaSpace_iff.mp hθ p
    rw [Divisor.neg_apply, neg_neg, ← hkeq] at h1
    exact_mod_cast h1
  have hkD2 : k < D₂ p := by
    rw [← hkeq] at hp
    exact_mod_cast hp
  have htrunc0 : truncT h (singleT p D₁ (RS.Cech.tailGerm p (-1 - k))) = 0 := by
    rw [truncT_singleT, singleT_eq_zero_iff, RS.Cech.ord_tailGerm_self]
    have hkey : (-(D₂ p) : ℤ) ≤ -1 - k := by omega
    exact_mod_cast hkey
  have hne0 : pairT θ hθ (singleT p D₁ (RS.Cech.tailGerm p (-1 - k))) ≠ 0 := by
    rw [pairT_singleT]
    exact pairAt_tailGerm_order_ne_zero hne
  exact hne0 (hker _ htrunc0)

/-! ### The surjectivity endgame (Miranda Thm 3.3, hard half) -/

omit [CompactSpace X] [ConnectedSpace X] [T1Space X] [T2Space X] in
/-- `pairT` only depends on its `MForm` argument up to equality (proof-irrelevant in the
membership proof) — avoids a dependent `rw`/`▸` inside `pairT`'s own proof argument, which
`rw` cannot abstract into a well-typed motive. -/
theorem pairT_eq_of_eq {D : RS.Divisor X} {θ₁ θ₂ : MForm X} (hEq : θ₁ = θ₂)
    (h1 : θ₁ ∈ MForm.OmegaSpace (-D)) (h2 : θ₂ ∈ MForm.OmegaSpace (-D)) :
    pairT θ₁ h1 = pairT θ₂ h2 := by
  subst hEq
  rfl

/-- **MIRANDA THM 3.3, surjectivity half**, functional form on `T D`. -/
theorem exists_pairT_eq (D : RS.Divisor X) (φ : T D →ₗ[ℂ] ℂ)
    (hα : ∀ f : RS.Mero X, φ (alphaL D f) = 0) :
    ∃ θ : MForm X, ∃ hθ : θ ∈ MForm.OmegaSpace (-D), pairT θ hθ = φ := by
  by_cases hφ0 : φ = 0
  · exact ⟨0, zero_mem _, by rw [hφ0]; exact pairT_zero D⟩
  -- Step 1: a reference nonzero form, and `A := D ⊓ K`.
  obtain ⟨ω₀, hω₀⟩ := RS.exists_ne_zero_mform (X := X)
  set K := RS.canonicalDivisorOf ω₀ with hK_def
  set A := D ⊓ K with hA_def
  have hAD : A ≤ D := inf_le_left
  have hAK : A ≤ K := inf_le_right
  have hωK : ω₀ ∈ MForm.OmegaSpace (-K) := by
    rw [MForm.mem_omegaSpace_iff]
    intro p
    rw [Divisor.neg_apply, neg_neg]
    show ((K p : ℤ) : WithTop ℤ) ≤ ω₀.ord p
    rw [hK_def]
    change ((ω₀.divisor p : ℤ) : WithTop ℤ) ≤ ω₀.ord p
    rw [MForm.divisor_apply]
    exact le_of_eq (WithTop.coe_untop₀_of_ne_top (MForm.ord_ne_top hω₀ p))
  have hω₀A : ω₀ ∈ MForm.OmegaSpace (-A) := omegaSpace_anti hAK hωK
  -- Step 2: the two functionals on `T A`.
  set φA := φ ∘ₗ truncT hAD with hφA_def
  have hφAα : ∀ g : RS.Mero X, φA (alphaL A g) = 0 := by
    intro g
    rw [hφA_def, LinearMap.comp_apply, truncT_alpha]
    exact hα g
  have hφAne : φA ≠ 0 := by
    intro hz
    apply hφ0
    apply LinearMap.ext
    intro τ
    obtain ⟨τ', rfl⟩ := truncT_surjective hAD τ
    have h3 : φA τ' = 0 := DFunLike.congr_fun hz τ'
    rw [hφA_def, LinearMap.comp_apply] at h3
    rw [LinearMap.zero_apply]
    exact h3
  set φ2 := pairT ω₀ hω₀A with hφ2_def
  have hφ2ne : φ2 ≠ 0 := by rw [hφ2_def]; exact pairT_ne_zero hω₀ hω₀A
  have hφ2α : ∀ g : RS.Mero X, φ2 (alphaL A g) = 0 := by
    intro g; rw [hφ2_def]; exact pairT_alpha ω₀ hω₀A g
  -- Step 3: Lemma 3.4 at `A`.
  obtain ⟨C, -, f₁, f₂, hf1ne, hf2ne, hkey⟩ :=
    exists_mul_functional_eq A φA φ2 hφAα hφ2α hφAne hφ2ne
  -- Step 4: rewrite the RHS via `pairT_mulInto`.
  have hf2mem : (f₂ : RS.Mero X) • ω₀ ∈ MForm.OmegaSpace (-(A - C)) := by
    have hmem := smul_mem_omegaSpace (F := -C) (E := A) (θ := ω₀) (f := (f₂ : RS.Mero X))
      (fun p => RS.mem_linSys_iff.mp f₂.2 p) hω₀A
    rwa [show A + (-C) = A - C from (sub_eq_add_neg A C).symm] at hmem
  have hpt2 : φ2 ∘ₗ nuL A C f₂ = pairT ((f₂ : RS.Mero X) • ω₀) hf2mem := by
    rw [hφ2_def, nuL_apply]
    exact pairT_mulInto (f₂ : RS.Mero X) (nu_bound A C f₂) ω₀ hω₀A hf2mem
  rw [hpt2] at hkey
  -- Step 5: invert `μ_{f₁}`, and the collapsed reference form `η`.
  set E₁ := A - C - RS.divisor (f₁ : RS.Mero X) with hE₁_def
  have hE₁A : E₁ ≤ A := sub_divisor_le A C hf1ne
  have hinv : ∀ p, ((E₁ p - (A - C) p : ℤ) : WithTop ℤ) ≤ (f₁ : RS.Mero X)⁻¹.ord p := by
    intro p
    rw [RS.MeroGermOn.ord_inv isOpen_univ (Set.mem_univ p), Mero.ord_eq_divisor hf1ne]
    rw [show E₁ p - (A - C) p = -(RS.divisor (f₁ : RS.Mero X) p) from by
      rw [hE₁_def, Divisor.sub_apply]; ring]
    norm_cast
  set η := ((f₂ : RS.Mero X) * (f₁ : RS.Mero X)⁻¹) • ω₀ with hη_def
  have hcollapse : (f₁ : RS.Mero X)⁻¹ • ((f₂ : RS.Mero X) • ω₀) = η := by
    rw [hη_def, ← mul_smul, mul_comm]
  have hηE₁ : η ∈ MForm.OmegaSpace (-E₁) := by
    rw [MForm.mem_omegaSpace_iff]
    intro p
    rw [Divisor.neg_apply, neg_neg, hη_def, RS.MForm.ord_smul_mero]
    have hordmul : ((f₂ : RS.Mero X) * (f₁ : RS.Mero X)⁻¹).ord p
        = ((RS.divisor (f₂ : RS.Mero X) p - RS.divisor (f₁ : RS.Mero X) p : ℤ) : WithTop ℤ) := by
      rw [RS.MeroGermOn.ord_mul isOpen_univ (Set.mem_univ p),
        RS.MeroGermOn.ord_inv isOpen_univ (Set.mem_univ p),
        Mero.ord_eq_divisor hf1ne, Mero.ord_eq_divisor hf2ne]
      norm_cast
    rw [hordmul]
    have hωord : ω₀.ord p = ((K p : ℤ) : WithTop ℤ) := by
      rw [hK_def]
      change ω₀.ord p = ((ω₀.divisor p : ℤ) : WithTop ℤ)
      rw [MForm.divisor_apply]
      exact (WithTop.coe_untop₀_of_ne_top (MForm.ord_ne_top hω₀ p)).symm
    rw [hωord, ← WithTop.coe_add]
    have hf2ge : -(C p) ≤ RS.divisor (f₂ : RS.Mero X) p := by
      have hb := RS.mem_linSys_iff.mp f₂.2 p
      rw [Mero.ord_eq_divisor hf2ne] at hb
      exact_mod_cast hb
    have hAKp : A p ≤ K p := Function.locallyFinsuppWithin.le_def.1 hAK p
    have hE₁eq : E₁ p = A p - C p - RS.divisor (f₁ : RS.Mero X) p := by
      rw [hE₁_def, Divisor.sub_apply, Divisor.sub_apply]
    have hle : E₁ p ≤ RS.divisor (f₂ : RS.Mero X) p - RS.divisor (f₁ : RS.Mero X) p + K p := by
      rw [hE₁eq]; omega
    exact_mod_cast hle
  -- `[‡]`: `pairT η hηE₁ = φA ∘ₗ truncT hE₁A`.
  have hηE₁' : (f₁ : RS.Mero X)⁻¹ • ((f₂ : RS.Mero X) • ω₀) ∈ MForm.OmegaSpace (-E₁) := by
    rw [hcollapse]; exact hηE₁
  have hstepDagger : pairT η hηE₁ = φA ∘ₗ truncT hE₁A := by
    apply DFinsupp.lhom_ext
    intro p x
    obtain ⟨ψ, rfl⟩ := TailAt.mk_surjective p E₁ x
    change pairT η hηE₁ (singleT p E₁ ψ) = (φA ∘ₗ truncT hE₁A) (singleT p E₁ ψ)
    rw [pairT_singleT]
    set τ' : T E₁ := singleT p E₁ ψ with hτ'_def
    change pairAt η p ψ = (φA ∘ₗ truncT hE₁A) τ'
    have e1 : pairAt η p ψ = pairT η hηE₁ τ' := (pairT_singleT η hηE₁ p ψ).symm
    have e2 : pairT η hηE₁ τ' = pairT ((f₁ : RS.Mero X)⁻¹ • ((f₂ : RS.Mero X) • ω₀)) hηE₁' τ' := by
      rw [pairT_eq_of_eq hcollapse.symm hηE₁ hηE₁']
    have e3 : pairT ((f₁ : RS.Mero X)⁻¹ • ((f₂ : RS.Mero X) • ω₀)) hηE₁' τ'
        = pairT ((f₂ : RS.Mero X) • ω₀) hf2mem (mulInto (f₁ : RS.Mero X)⁻¹ hinv τ') :=
      (DFunLike.congr_fun
        (pairT_mulInto (f₁ : RS.Mero X)⁻¹ hinv ((f₂ : RS.Mero X) • ω₀) hf2mem hηE₁') τ').symm
    have e4 : pairT ((f₂ : RS.Mero X) • ω₀) hf2mem (mulInto (f₁ : RS.Mero X)⁻¹ hinv τ')
        = φA (nuL A C f₁ (mulInto (f₁ : RS.Mero X)⁻¹ hinv τ')) :=
      (DFunLike.congr_fun hkey (mulInto (f₁ : RS.Mero X)⁻¹ hinv τ')).symm
    have e5 : φA (nuL A C f₁ (mulInto (f₁ : RS.Mero X)⁻¹ hinv τ')) = φA (truncT hE₁A τ') := by
      rw [nuL_mulInto_inv A C hf1ne hinv τ']
    rw [e1, e2, e3, e4, e5]
    rfl
  -- 3.6, first application (`E₁ ≤ A`).
  have hηA : η ∈ MForm.OmegaSpace (-A) := by
    apply mem_omegaSpace_of_vanishing_ker_trunc hE₁A hηE₁
    intro τ hτ0
    rw [DFunLike.congr_fun hstepDagger τ, LinearMap.comp_apply, hτ0, map_zero]
  have hstepSec : φA = pairT η hηA := by
    have heq1 : (pairT η hηA) ∘ₗ truncT hE₁A = φA ∘ₗ truncT hE₁A := by
      rw [pairT_trunc hE₁A η hηA, hstepDagger]
    apply LinearMap.ext
    intro τ
    obtain ⟨τ', rfl⟩ := truncT_surjective hE₁A τ
    have h4 := DFunLike.congr_fun heq1.symm τ'
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at h4
    exact h4
  -- 3.6, second application (`A ≤ D`).
  have hηD : η ∈ MForm.OmegaSpace (-D) := by
    apply mem_omegaSpace_of_vanishing_ker_trunc hAD hηA
    intro τ hτ0
    rw [← hstepSec, hφA_def, LinearMap.comp_apply, hτ0, map_zero]
  have hfinal : φ = pairT η hηD := by
    have heq2 : (pairT η hηD) ∘ₗ truncT hAD = φA := by
      rw [pairT_trunc hAD η hηD]
      exact hstepSec.symm
    apply LinearMap.ext
    intro τ
    obtain ⟨τ', rfl⟩ := truncT_surjective hAD τ
    have h5 := DFunLike.congr_fun heq2 τ'
    rw [LinearMap.comp_apply] at h5
    rw [h5, hφA_def, LinearMap.comp_apply]
  exact ⟨η, hηD, hfinal.symm⟩

theorem resMap_surjective (D : RS.Divisor X) : Function.Surjective (resMap D) := by
  intro Λ
  set φ := Λ ∘ₗ H1Tail.mk D with hφ_def
  have hα : ∀ f : RS.Mero X, φ (alphaL D f) = 0 := by
    intro f
    rw [hφ_def, LinearMap.comp_apply,
      show H1Tail.mk D (alphaL D f) = 0 from (H1Tail.mk_eq_zero_iff D _).2 ⟨f, rfl⟩, map_zero]
  obtain ⟨θ, hθ, hθφ⟩ := exists_pairT_eq D φ hα
  refine ⟨⟨θ, hθ⟩, ?_⟩
  apply LinearMap.ext
  intro x
  obtain ⟨τ, rfl⟩ := H1Tail.mk_surjective D x
  rw [resMap_mk, hθφ, hφ_def, LinearMap.comp_apply]

/-- **MIRANDA THM 3.3**: `Res` is a linear isomorphism `Ω(-D) ≅ Dual(H1Tail D)`. -/
noncomputable def resEquiv (D : RS.Divisor X) :
    ↥(MForm.OmegaSpace (-D)) ≃ₗ[ℂ] Module.Dual ℂ (H1Tail D) :=
  LinearEquiv.ofBijective (resMap D) ⟨resMap_injective D, resMap_surjective D⟩

/-! ### The export bank (orchestrator addendum: re-based against the tail `h¹`) -/

/-- **THE frozen obligation, re-based** (serre-duality-cech D6's exact shape, at the TAIL `h¹`;
`RS.MForm.i` is the exact name for the design's `RS.i` — see the file-end note). -/
theorem i_neg_eq_h1T (D : RS.Divisor X) : MForm.i (-D) = h1T D := by
  change Module.finrank ℂ (MForm.OmegaSpace (-D)) = Module.finrank ℂ (H1Tail D)
  rw [LinearEquiv.finrank_eq (resEquiv D), Subspace.dual_finrank_eq]

/-- Serre duality in the `l(K-D)` shape riemann-roch consumes. -/
theorem l_sub_eq_h1T {ω₀ : MForm X} (h₀ : ω₀ ≠ 0) (D : RS.Divisor X) :
    RS.l (RS.canonicalDivisorOf ω₀ - D) = h1T D := by
  rw [show RS.canonicalDivisorOf ω₀ - D = -D + RS.canonicalDivisorOf ω₀ from by
    rw [sub_eq_add_neg, add_comm], ← RS.i_eq_l_add_canonicalDivisorOf h₀ (-D)]
  exact i_neg_eq_h1T D

theorem h1T_zero_eq_l_K {ω₀ : MForm X} (h₀ : ω₀ ≠ 0) :
    h1T (0 : RS.Divisor X) = RS.l (RS.canonicalDivisorOf ω₀) := by
  rw [← l_sub_eq_h1T h₀ (0 : RS.Divisor X), sub_zero]

theorem h1T_zero_eq_genus : h1T (0 : RS.Divisor X) = genus X := by
  rw [← i_neg_eq_h1T (0 : RS.Divisor X), neg_zero]
  exact RS.genus_eq_finrank_omegaSpace_zero.symm

theorem h1T_canonical {ω₀ : MForm X} (h₀ : ω₀ ≠ 0) :
    h1T (RS.canonicalDivisorOf ω₀) = 1 := by
  rw [← l_sub_eq_h1T h₀ (RS.canonicalDivisorOf ω₀), sub_self]
  exact RS.l_zero

/-! ### `chiT` (definition only — see the file docstring for the additivity gap) -/

/-- The tail-level `χ`. Additivity (`chiT D = chiT 0 + deg D`) is NOT delivered — see the file
docstring. -/
noncomputable def chiT (D : RS.Divisor X) : ℤ := (RS.l D : ℤ) - (h1T D : ℤ)

end RS.TailDuality
