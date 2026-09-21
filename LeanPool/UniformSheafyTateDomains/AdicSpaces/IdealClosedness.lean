/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import LeanPool.UniformSheafyTateDomains.AdicSpaces.GeometricSeries

/-!
# Closedness of Ideals in the I-adic Topology

For a Noetherian commutative ring `R` equipped with the `I`-adic topology, every
ideal `q ⊆ R` is **closed** provided `I` is contained in the Jacobson radical
of `R` (e.g., if `R` is `I`-adically complete, or if `I` is a Tate pair's ideal
of definition containing a topologically nilpotent unit).

The proof combines:
1. The topological characterization of closure in the `I`-adic topology:
   `x ∈ closure q ↔ ∀ n, x ∈ q + I^n` (since the basic open neighborhoods
   of `x` are the cosets `x + I^n`).
2. **Krull's intersection theorem** for Noetherian rings with ideals contained
   in the Jacobson radical: `⋂ n, I^n • (R/q) = 0` in the quotient `R/q`,
   which translates to `⋂ n, (q + I^n) = q` in `R`.

## Main results

* `Ideal.isClosed_of_le_jacobson` — the core closedness lemma.

## References

This is a topological consequence of Artin–Rees / Krull (Stacks 00IN / 00IP).
Used downstream by the Tate-acyclicity `coeRingHom_preserves_proper` chain
(`Cor832.lean`).
-/

open Topology

universe u

namespace ValuationSpectrum

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
/-- Characterization of closure in the `I`-adic topology: `x ∈ closure q`
iff `x ∈ q + I^n` for every `n`. -/
theorem mem_closure_iff_of_isAdic
    [TopologicalSpace R]
    {I : Ideal R} (hI : IsAdic I) (q : Ideal R) (x : R) :
    x ∈ closure (q : Set R) ↔ ∀ n : ℕ, x ∈ (q + I ^ n : Ideal R) := by
  rw [mem_closure_iff_nhds]
  constructor
  · intro hx n
    have hmem : (x + ·) '' ((I ^ n : Ideal R) : Set R) ∈ 𝓝 x :=
      (hI.hasBasis_nhds x).mem_of_mem (i := n) trivial
    obtain ⟨y, hy_nhd, hy_q⟩ := hx _ hmem
    obtain ⟨z, hz_In, rfl⟩ := hy_nhd
    rw [show x = (x + z) + (-z) by ring]
    exact (q + I ^ n).add_mem
      (Submodule.mem_sup_left hy_q)
      (Submodule.mem_sup_right ((I ^ n).neg_mem hz_In))
  · intro hx U hU
    rw [(hI.hasBasis_nhds x).mem_iff] at hU
    obtain ⟨n, -, hn⟩ := hU
    obtain ⟨a, ha_q, b, hb_In, hab⟩ := Submodule.mem_sup.mp (hx n)
    refine ⟨a, hn ⟨-b, (I ^ n).neg_mem hb_In, ?_⟩, ha_q⟩
    rw [← hab]; ring

/-- **Closedness of ideals in the `I`-adic topology under the Jacobson
hypothesis.** For a Noetherian commutative ring `R` equipped with the `I`-adic
topology and `I ⊆ Jacobson(⊥)`, every ideal `q ⊆ R` is closed. -/
theorem Ideal.isClosed_of_le_jacobson
    [TopologicalSpace R]
    {I : Ideal R} (hI : IsAdic I)
    (h_jac : I ≤ Ideal.jacobson ⊥)
    (q : Ideal R) : IsClosed (q : Set R) := by
  rw [← closure_subset_iff_isClosed]
  intro x hx
  rw [mem_closure_iff_of_isAdic hI] at hx
  have hKrull : (⨅ n : ℕ, I ^ n • (⊤ : Submodule R (R ⧸ q))) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_le_jacobson I h_jac
  set π := Ideal.Quotient.mk q
  have hπx_inter : π x ∈ (⨅ n : ℕ, I ^ n • (⊤ : Submodule R (R ⧸ q))) := by
    rw [Submodule.mem_iInf]
    intro n
    obtain ⟨a, ha_q, b, hb_In, hab⟩ := Submodule.mem_sup.mp (hx n)
    have hπx : π x = π b := by
      rw [show x = a + b from hab.symm, map_add,
        Ideal.Quotient.eq_zero_iff_mem.mpr ha_q]
      exact zero_add _
    rw [hπx]
    have hπb_mem : (b : R) • (1 : R ⧸ q) ∈
        I ^ n • (⊤ : Submodule R (R ⧸ q)) :=
      Submodule.smul_mem_smul hb_In Submodule.mem_top
    convert hπb_mem using 1
    change (Submodule.Quotient.mk b : R ⧸ (q : Submodule R R)) =
      b • (Submodule.Quotient.mk (1 : R) : R ⧸ (q : Submodule R R))
    rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
  rw [hKrull, Submodule.mem_bot] at hπx_inter
  exact Ideal.Quotient.eq_zero_iff_mem.mp hπx_inter

/-- **Closedness of ideals in the `I`-adic topology for `I`-adically complete
Noetherian rings.** Corollary of `Ideal.isClosed_of_le_jacobson` using
`IsAdicComplete.le_jacobson_bot`. -/
theorem Ideal.isClosed_of_isAdicComplete
    [TopologicalSpace R]
    (I : Ideal R) (hI : IsAdic I) [IsAdicComplete I R]
    (q : Ideal R) : IsClosed (q : Set R) :=
  Ideal.isClosed_of_le_jacobson hI (IsAdicComplete.le_jacobson_bot I) q

/-- **Pointwise Jacobson closedness.** Sharper analog of
`Ideal.isClosed_of_le_jacobson` taking a pointwise Jacobson containment
`I ≤ Ideal.jacobson q` at the **specific** ideal `q`, rather than the
global `I ≤ Ideal.jacobson ⊥`.

This is strictly more general than `Ideal.isClosed_of_le_jacobson`:
`I ≤ Ideal.jacobson ⊥` implies `I ≤ Ideal.jacobson q` for every `q`
(monotonicity of `Ideal.jacobson`), but not conversely (non-Henselian
rings typically have `Ideal.jacobson ⊥ ⊊ Ideal.jacobson q` for specific
`q`). Useful for the Tate-acyclicity Cor 8.32 route where the global
containment fails in degenerate `locSubring` cases but the pointwise
containment at prime extensions holds unconditionally. -/
theorem Ideal.isClosed_of_le_jacobson_pointwise
    [TopologicalSpace R]
    {I : Ideal R} (hI : IsAdic I)
    (q : Ideal R) (h_jac : I ≤ Ideal.jacobson q) :
    IsClosed (q : Set R) := by
  rw [← closure_subset_iff_isClosed]
  intro x hx
  rw [mem_closure_iff_of_isAdic hI] at hx
  set π : R →+* R ⧸ q := Ideal.Quotient.mk q
  set J : Ideal (R ⧸ q) := Ideal.map π I with hJ_def
  have hJ_jac : J ≤ Ideal.jacobson (⊥ : Ideal (R ⧸ q)) := by
    rw [Ideal.jacobson, le_sInf_iff]
    rintro m ⟨-, hm_max⟩
    let : m.IsMaximal := hm_max
    have hm'_max : (Ideal.comap π m).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective π Ideal.Quotient.mk_surjective
    have hq_le_m' : q ≤ Ideal.comap π m := fun y hy ↦ by
      change π y ∈ m
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hy]
      exact m.zero_mem
    have hI_le : I ≤ Ideal.comap π m := by
      rw [Ideal.jacobson] at h_jac
      exact h_jac.trans (sInf_le ⟨hq_le_m', hm'_max⟩)
    rwa [hJ_def, Ideal.map_le_iff_le_comap]
  let : IsNoetherianRing (R ⧸ q) := Ideal.Quotient.isNoetherianRing q
  have hKrull : (⨅ n : ℕ, J ^ n • (⊤ : Submodule (R ⧸ q) (R ⧸ q))) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_le_jacobson J hJ_jac
  suffices h : π x = 0 from (Ideal.Quotient.eq_zero_iff_mem (I := q)).mp h
  have hπx_mem : π x ∈ (⨅ n : ℕ, J ^ n • (⊤ : Submodule (R ⧸ q) (R ⧸ q))) := by
    rw [Submodule.mem_iInf]
    intro n
    obtain ⟨a, ha_q, b, hb_In, hab⟩ := Submodule.mem_sup.mp (hx n)
    have hπx_eq : π x = π b := by
      rw [show x = a + b from hab.symm, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha_q]
      exact zero_add _
    rw [hπx_eq]
    have hπb : π b ∈ J ^ n := by
      rw [hJ_def, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem π hb_In
    rw [show π b = π b • (1 : R ⧸ q) from (mul_one (π b)).symm]
    exact Submodule.smul_mem_smul hπb Submodule.mem_top
  rw [hKrull, Submodule.mem_bot] at hπx_mem
  exact hπx_mem

omit [IsNoetherianRing R] in
/-- **Clopen subspace bridge for closedness.** For a subring `S` that is open
in a topological ring `R` (equivalently clopen, since `AddSubgroup.isOpen`
implies `IsClosed`), any subset `C ⊆ S` closed in the subspace topology of `S`
is closed in `R`. -/
theorem IsClosed.of_isClosed_subspace_of_isOpen_subring
    [TopologicalSpace R] [IsTopologicalRing R]
    {S : Subring R} (hS_open : IsOpen (S : Set R))
    {C : Set R} (hC_sub : C ⊆ (S : Set R))
    (hC_closed_sub : IsClosed ((S.subtype) ⁻¹' C : Set S)) :
    IsClosed C := by
  have hS_closed : IsClosed (S : Set R) :=
    S.toAddSubgroup.isClosed_of_isOpen hS_open
  have h_inducing : Topology.IsInducing (S.subtype : S → R) :=
    Topology.IsEmbedding.subtypeVal.isInducing
  obtain ⟨C', hC'_closed, hC'_preimage⟩ := h_inducing.isClosed_iff.mp hC_closed_sub
  have hC_eq : C = C' ∩ (S : Set R) := by
    ext x
    constructor
    · intro hxC
      refine ⟨?_, hC_sub hxC⟩
      have : (⟨x, hC_sub hxC⟩ : S) ∈ (S.subtype ⁻¹' C' : Set S) := by
        rw [hC'_preimage]; exact hxC
      exact this
    · rintro ⟨hxC', hxS⟩
      have : (⟨x, hxS⟩ : S) ∈ (S.subtype ⁻¹' C : Set S) := by
        rw [← hC'_preimage]; exact hxC'
      exact this
  rw [hC_eq]
  exact hC'_closed.inter hS_closed

section TopologicallyNilpotentJacobson

omit [IsNoetherianRing R] in
/-- **In an `I`-adic topology, every element of `I` is topologically nilpotent.**
No completeness or Hausdorff hypothesis needed. -/
theorem isTopologicallyNilpotent_of_mem_of_isAdic
    [TopologicalSpace R]
    {I : Ideal R} (hI : IsAdic I) {x : R} (hx : x ∈ I) :
    IsTopologicallyNilpotent x := by
  intro U hU
  rw [hI.hasBasis_nhds_zero.mem_iff] at hU
  obtain ⟨m, -, hU_sub⟩ := hU
  refine Filter.eventually_atTop.mpr ⟨m, fun n hn ↦ hU_sub ?_⟩
  exact Ideal.pow_le_pow_right hn (Ideal.pow_mem_pow hx n)

omit [IsNoetherianRing R] in
/-- **Generic Jacobson containment from topological nilpotence.** In a
complete Hausdorff nonarchimedean commutative topological ring, if every
element of an ideal `I` is topologically nilpotent, then `I ≤ Ideal.jacobson ⊥`. -/
theorem Ideal.le_jacobson_bot_of_forall_isTopologicallyNilpotent
    [UniformSpace R] [T2Space R] [CompleteSpace R]
    [IsTopologicalRing R] [IsUniformAddGroup R] [NonarchimedeanAddGroup R]
    {I : Ideal R} (hI : ∀ x ∈ I, IsTopologicallyNilpotent x) :
    (I : Ideal R) ≤ Ideal.jacobson ⊥ := by
  intro x hx
  rw [Ideal.mem_jacobson_bot]
  intro y
  rw [show x * y + 1 = 1 - (-(x * y)) by ring]
  exact (hI _ (I.mul_mem_right y hx)).neg.isUnit_one_sub

omit [IsNoetherianRing R] in
/-- **Jacobson containment for `I`-adic complete Hausdorff nonarchimedean rings.**
For a complete Hausdorff nonarchimedean ring with the `I`-adic topology,
`I ≤ Ideal.jacobson ⊥`. -/
theorem Ideal.le_jacobson_bot_of_isAdic_complete
    [UniformSpace R] [T2Space R] [CompleteSpace R]
    [IsTopologicalRing R] [IsUniformAddGroup R] [NonarchimedeanAddGroup R]
    {I : Ideal R} (hI : IsAdic I) :
    I ≤ Ideal.jacobson (⊥ : Ideal R) :=
  Ideal.le_jacobson_bot_of_forall_isTopologicallyNilpotent
    fun _ hx ↦ isTopologicallyNilpotent_of_mem_of_isAdic hI hx

end TopologicallyNilpotentJacobson

end ValuationSpectrum
