/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Module.PrincipalKoszulPositivity

/-!
# Finite power torsion for a principal Koszul endomorphism

This file isolates the reusable algebra needed after tangential localization.
The ambient module need not be finite over the ring in which lengths are
measured.  It is enough that the first kernel has finite length: all finite
power kernels then have finite length by devissage.

The final theorem deliberately assumes that the actual residual quotient is
nonzero.  It proves only the strict length inequality and makes no
noncharacteristic-support or geometric nonvanishing claim.
-/

namespace AlgebraicAnalysis.PrincipalKoszulFiniteTorsion

open AlgebraicAnalysis.PrincipalKoszulPositivity

noncomputable section

universe u v

variable {R : Type u} {E : Type v}
variable [CommRing R]
variable [AddCommGroup E] [Module R E]

/-- If the first kernel of an endomorphism is Noetherian, then so is the
kernel of every finite power.  No finiteness hypothesis is imposed on the
ambient module. -/
theorem isNoetherian_kernel_power (f : Module.End R E)
    [IsNoetherian R f.ker] (n : ℕ) : IsNoetherian R (f ^ n).ker := by
  induction n with
  | zero =>
    rw [pow_zero, Module.End.one_eq_id, LinearMap.ker_id]
    infer_instance
  | succ n ih =>
    let := ih
    have hle : f.ker ≤ (f ^ (n + 1)).ker := by
      intro z hz
      rw [LinearMap.mem_ker, pow_succ, Module.End.mul_apply,
        LinearMap.mem_ker.mp hz, map_zero]
    let i : f.ker →ₗ[R] (f ^ (n + 1)).ker := Submodule.inclusion hle
    let g : (f ^ (n + 1)).ker →ₗ[R] (f ^ n).ker := f.restrict (by
      intro z hz
      rw [LinearMap.mem_ker] at hz ⊢
      simpa [pow_succ, Module.End.mul_apply] using hz)
    have hexact : i.range = g.ker := by
      ext z
      constructor
      · rintro ⟨w, rfl⟩
        apply Subtype.ext
        exact LinearMap.mem_ker.mp w.property
      · intro hz
        have hz0 : f z.val = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hz)
        exact ⟨⟨z.val, hz0⟩, rfl⟩
    exact isNoetherian_of_range_eq_ker i g hexact

/-- Finite length of the first kernel propagates to every finite power
kernel, even when the ambient module is not finite over `R`. -/
theorem isFiniteLength_kernel_power (f : Module.End R E)
    (hfinite : IsFiniteLength R f.ker) (n : ℕ) :
    IsFiniteLength R (f ^ n).ker := by
  have hfirst := isFiniteLength_iff_isNoetherian_isArtinian.mp hfinite
  let : IsNoetherian R f.ker := hfirst.1
  let : IsArtinian R f.ker := hfirst.2
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_kernel_power f n, isArtinian_kernel_power f n⟩

/-- A stable finite power kernel contributes the same length to the kernel and
cokernel.  If the actual quotient left after removing that torsion and the
range is nonzero, the principal Koszul Euler length is strictly positive.

The nonzero quotient is an explicit input; this theorem does not manufacture
it from a support or noncharacteristic hypothesis. -/
theorem length_cokernel_gt_kernel_of_stable_power_and_nonzero
    (f : Module.End R E) (n : ℕ)
    (hfinite : IsFiniteLength R f.ker)
    (hstable : LinearMap.ker (f ^ n) = LinearMap.ker (f ^ (n + 1)))
    (hnonzero : Nontrivial (E ⧸ ((f ^ n).ker ⊔ f.range))) :
    Module.length R (E ⧸ f.range) > Module.length R f.ker := by
  have hfirstparts := isFiniteLength_iff_isNoetherian_isArtinian.mp hfinite
  let : IsNoetherian R f.ker := hfirstparts.1
  let : IsArtinian R f.ker := hfirstparts.2
  let T : Submodule R E := (f ^ n).ker
  have hTfinite : IsFiniteLength R T := isFiniteLength_kernel_power f hfinite n
  have hTparts := isFiniteLength_iff_isNoetherian_isArtinian.mp hTfinite
  let : IsNoetherian R T := hTparts.1
  let : IsArtinian R T := hTparts.2
  have hcomap : T.comap f = T := by
    ext z
    rw [Submodule.mem_comap]
    change (f ^ n) (f z) = 0 ↔ (f ^ n) z = 0
    rw [← Module.End.mul_apply, (Commute.self_pow f n).eq.symm,
      Module.End.mul_apply]
    simpa [Module.End.pow_apply, Function.iterate_succ_apply'] using
      congrArg (fun K : Submodule R E ↦ z ∈ K) hstable.symm
  let : Nontrivial (E ⧸ (T ⊔ f.range)) := hnonzero
  have hpositive : 0 < Module.length R (E ⧸ (T ⊔ f.range)) :=
    Module.length_pos
  rw [length_cokernel_eq_kernel_add_regular_quotient f T hcomap]
  simpa [add_comm] using
    ENat.lt_add_left (Module.length_ne_top (R := R) (M := f.ker)) hpositive


end

end AlgebraicAnalysis.PrincipalKoszulFiniteTorsion
