/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Module.PrincipalKoszulPositivity
import Mathlib.RingTheory.Support

/-!
# Support detects the residual after stable scalar torsion

The support argument is most transparent before localization: the exact
sequence for the power kernel splits support into torsion and residual parts,
and `support_quotSMulTop` then applies at the larger prime.
-/

namespace AlgebraicAnalysis.StableTorsionResidualSupport

open scoped Pointwise

noncomputable section

universe u v

variable {R : Type u} {E : Type v}
variable [CommRing R] [AddCommGroup E] [Module R E]

private abbrev scalarEnd (x : R) : E →ₗ[R] E := LinearMap.lsmul R E x
theorem residual_nontrivial_of_support
     [Module.Finite R E]
    (x : R) (n : ℕ) (p q : PrimeSpectrum R)
    (hp : p ∈ Module.support R E) (hpq : p ≤ q)
    (hxp : x ∉ p.asIdeal)
    (hq : q ∈ Module.support R (QuotSMulTop x E)) :
    Nontrivial (E ⧸ (LinearMap.ker (scalarEnd (E := E) x ^ n) ⊔
      (scalarEnd (E := E) x).range)) := by
  let f := scalarEnd (E := E) x
  let T : Submodule R E := LinearMap.ker (f ^ n)
  have hpower : ∀ m (z : E), (f ^ m) z = x ^ m • z := by
    intro m
    induction m with
    | zero => intro z; simp
    | succ m ih =>
        intro z
        simp [pow_succ, Module.End.mul_apply, ih, f, scalarEnd, smul_smul]
  have hTann : x ^ n ∈ Module.annihilator R T := by
    rw [Module.mem_annihilator]
    intro z
    have hz := z.property
    apply Subtype.ext
    change x ^ n • (z : E) = 0
    change (f ^ n) (z : E) = 0 at hz
    exact (hpower n (z : E)).symm.trans hz
  have hpT : p ∉ Module.support R T := by
    intro h
    have hle := Module.annihilator_le_of_mem_support h
    have hpow : x ^ n ∈ p.asIdeal := hle hTann
    exact hxp (p.isPrime.mem_of_pow_mem n hpow)
  have hexact : Function.Exact T.subtype T.mkQ :=
    LinearMap.exact_subtype_mkQ T
  have hsupport : Module.support R E =
      Module.support R T ∪ Module.support R (E ⧸ T) :=
    Module.support_of_exact hexact T.subtype_injective T.mkQ_surjective
  have hpquot : p ∈ Module.support R (E ⧸ T) := by
    have hpmem : p ∈ Module.support R T ∪ Module.support R (E ⧸ T) := by
      rw [← hsupport]
      exact hp
    exact hpmem.resolve_left hpT
  have hqquot : q ∈ Module.support R (E ⧸ T) :=
    Module.mem_support_mono hpq hpquot
  have hqzero : q ∈ PrimeSpectrum.zeroLocus ({x} : Set R) := by
    rw [Module.support_quotSMulTop (M := E) x] at hq
    exact hq.2
  have hqres : q ∈ Module.support R (QuotSMulTop x (E ⧸ T)) := by
    rw [Module.support_quotSMulTop]
    exact ⟨hqquot, hqzero⟩
  have hglobal : Nontrivial (QuotSMulTop x (E ⧸ T)) :=
    Module.nonempty_support_iff.mp ⟨q, hqres⟩
  have hmap : Submodule.map T.mkQ (f.range) =
      x • (⊤ : Submodule R (E ⧸ T)) := by
    ext z
    constructor
    · rintro ⟨y, ⟨w, rfl⟩, rfl⟩
      simpa [f, scalarEnd] using
        (Submodule.smul_mem_pointwise_smul (T.mkQ w) x (⊤ : Submodule R (E ⧸ T)) trivial)
    · intro hz
      have hz' : z ∈ Ideal.span ({x} : Set R) • (⊤ : Submodule R (E ⧸ T)) := by
        rw [Submodule.ideal_span_singleton_smul]
        exact hz
      refine Submodule.smul_induction_on hz' ?_ (fun a b ha hb ↦ add_mem ha hb)
      intro r hr z hz
      rcases (Ideal.mem_span_singleton.mp hr) with ⟨c, rfl⟩
      refine Submodule.Quotient.induction_on T z ?_
      intro w
      refine ⟨f (c • w), ⟨c • w, rfl⟩, ?_⟩
      simp [f, scalarEnd, smul_smul, mul_comm]
  have hequiv :
      ((E ⧸ T) ⧸ Submodule.map T.mkQ f.range) ≃ₗ[R]
        E ⧸ (T ⊔ f.range) :=
    Submodule.quotientQuotientEquivQuotientSup T f.range
  have hnontriv : Nontrivial ((E ⧸ T) ⧸ Submodule.map T.mkQ f.range) := by
    rw [hmap]
    exact Submodule.Quotient.nontrivial_iff.mpr (by
      intro htop
      exact not_subsingleton_iff_nontrivial.mpr hglobal
        (Submodule.Quotient.subsingleton_iff.mpr htop))
  let : Nontrivial ((E ⧸ T) ⧸ Submodule.map T.mkQ f.range) := hnontriv
  have hfinal := Equiv.nontrivial hequiv.symm.toEquiv
  simpa [T, f] using hfinal


end
end AlgebraicAnalysis.StableTorsionResidualSupport
