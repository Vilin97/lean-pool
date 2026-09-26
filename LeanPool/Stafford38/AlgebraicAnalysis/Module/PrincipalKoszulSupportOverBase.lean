/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.Module.StableTorsionResidualSupport
public import LeanPool.Stafford38.AlgebraicAnalysis.Module.PrincipalKoszulFiniteTorsion


/-!
# Principal Koszul positivity after restriction of scalars

Support and torsion are computed over the coefficient algebra `C`; the
resulting length inequality is measured over the base ring `R`.  No finite
generation of `E` over `R` is needed: only the first `R`-kernel has finite
length.
-/

@[expose] public section

namespace AlgebraicAnalysis.PrincipalKoszulSupportOverBase

open AlgebraicAnalysis.PrincipalKoszulPositivity
open AlgebraicAnalysis.PrincipalKoszulFiniteTorsion
open AlgebraicAnalysis.StableTorsionResidualSupport

noncomputable section

universe u v w

variable {R : Type u} {C : Type v} {E : Type w}
variable [CommRing R] [CommRing C] [Algebra R C]
variable [AddCommGroup E] [Module C E] [Module R E]
variable [IsScalarTower R C E]

theorem length_cokernel_gt_kernel_of_support_over_base
    [IsNoetherianRing C] [Module.Finite C E]
    (x : C) (p q : PrimeSpectrum C)
    (hp : p ∈ Module.support C E) (hpq : p ≤ q)
    (hxp : x ∉ p.asIdeal)
    (hq : q ∈ Module.support C (QuotSMulTop x E))
    (hfinite : IsFiniteLength R
      (LinearMap.ker ((LinearMap.lsmul C E x).restrictScalars R))) :
    Module.length R (E ⧸ LinearMap.range ((LinearMap.lsmul C E x).restrictScalars R)) >
      Module.length R (LinearMap.ker ((LinearMap.lsmul C E x).restrictScalars R)) := by
  let fC : Module.End C E := LinearMap.lsmul C E x
  let fR : Module.End R E := fC.restrictScalars R
  obtain ⟨n, hn⟩ := exists_stable_kernel_power_smul (E := E) x
  have hpow : ∀ m, fR ^ m = (fC ^ m).restrictScalars R := by
    intro m
    induction m with
    | zero => ext z; simp
    | succ m ih =>
        rw [pow_succ, pow_succ, ih]
        ext z
        simp [fR, LinearMap.restrictScalars_apply, Module.End.mul_apply]
  have hstable : LinearMap.ker (fR ^ n) = LinearMap.ker (fR ^ (n + 1)) := by
    rw [hpow, hpow, LinearMap.ker_restrictScalars, LinearMap.ker_restrictScalars]
    exact congrArg (Submodule.restrictScalars R) hn
  have hnonzeroC : Nontrivial (E ⧸ (LinearMap.ker (fC ^ n) ⊔ fC.range)) :=
    residual_nontrivial_of_support x n p q hp hpq hxp hq
  let PC : Submodule C E := LinearMap.ker (fC ^ n) ⊔ fC.range
  let PR : Submodule R E := LinearMap.ker (fR ^ n) ⊔ fR.range
  have hPR : PR = PC.restrictScalars R := by
    dsimp [PR, PC]
    rw [show fR ^ n = (fC ^ n).restrictScalars R from hpow n]
    simp only [LinearMap.ker_restrictScalars, Submodule.restrictScalars_sup]
    rfl
  have hnonzeroR : Nontrivial (E ⧸ PR) := by
    have hPC : PC ≠ (⊤ : Submodule C E) :=
      Submodule.Quotient.nontrivial_iff.mp hnonzeroC
    apply Submodule.Quotient.nontrivial_iff.mpr
    intro htop
    apply hPC
    apply (Submodule.restrictScalars_eq_top_iff R C E).mp
    rw [← hPR, htop]
  have hresult :=
    length_cokernel_gt_kernel_of_stable_power_and_nonzero
      (R := R) fR n hfinite hstable hnonzeroR
  simpa [fR, fC] using hresult


end
end AlgebraicAnalysis.PrincipalKoszulSupportOverBase
