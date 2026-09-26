/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.Module.MinimalPrimeFiniteLengthLocalization
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Noetherian.Defs


/-!
# Positivity for a principal Koszul quotient

Stable power torsion contributes equally to kernel and cokernel length.
After removing it, local Nakayama gives a positive residual cokernel when
a support prime avoids the scalar. The proof retains embedded torsion;
it does not infer injectivity from minimal-prime avoidance.
-/

@[expose] public section

namespace AlgebraicAnalysis.PrincipalKoszulPositivity

open scoped Pointwise

noncomputable section

universe u v

variable {R : Type u} {E : Type v}
variable [CommRing R]
variable [AddCommGroup E] [Module R E]

/-- Scalar multiplication, viewed as a linear endomorphism. -/
abbrev scalarEnd (x : R) : E →ₗ[R] E := LinearMap.lsmul R E x

/--
The `x`-power torsion in a Noetherian module is already the kernel of one
finite power of `x`.  This is the stabilization step needed before passing to
the quotient on which `x` acts injectively; it does not discard embedded
torsion.
-/
theorem exists_stable_kernel_power [IsNoetherian R E] (f : Module.End R E) :
    ∃ n : ℕ, LinearMap.ker (f ^ n) = LinearMap.ker (f ^ (n + 1)) := by
  obtain ⟨n, hn⟩ :=
    (monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian R E))
      f.iterateKer
  exact ⟨n, hn (n + 1) (Nat.le_add_right n 1)⟩

/-- Specialization of kernel stabilization to multiplication by a scalar. -/
theorem exists_stable_kernel_power_smul [IsNoetherian R E] (x : R) :
    ∃ n : ℕ,
      LinearMap.ker ((scalarEnd (E := E) x) ^ n) =
        LinearMap.ker ((scalarEnd (E := E) x) ^ (n + 1)) :=
  exists_stable_kernel_power (scalarEnd (E := E) x)

/-- Finite-length coordinate kernel controls all finite power-torsion layers.
The Artinian assertion is the nontrivial half; Noetherianity is inherited
from the ambient finite module in the applications. -/
theorem isArtinian_kernel_power (f : Module.End R E)
    [IsArtinian R f.ker] (n : ℕ) : IsArtinian R (f ^ n).ker := by
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
    exact isArtinian_of_range_eq_ker i g hexact

/-- Once two consecutive power kernels agree, the induced endomorphism on
the quotient by the stabilized kernel is injective. -/
theorem quotient_by_stable_kernel_power_injective (f : Module.End R E) (n : ℕ)
    (hstable : LinearMap.ker (f ^ n) = LinearMap.ker (f ^ (n + 1))) :
    Function.Injective
      ((LinearMap.ker (f ^ n)).mapQ (LinearMap.ker (f ^ n)) f (by
        intro z hz
        change f z ∈ LinearMap.ker (f ^ n)
        rw [LinearMap.mem_ker] at hz ⊢
        rw [← Module.End.mul_apply, (Commute.self_pow f n).eq.symm,
          Module.End.mul_apply, hz, f.map_zero])) := by
  rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ]
  have hcomap :
      (LinearMap.ker (f ^ n)).comap f = LinearMap.ker (f ^ n) := by
    ext z
    rw [Submodule.mem_comap]
    change (f ^ n) (f z) = 0 ↔ (f ^ n) z = 0
    rw [← Module.End.mul_apply, (Commute.self_pow f n).eq.symm,
      Module.End.mul_apply]
    simpa [Module.End.pow_apply, Function.iterate_succ_apply'] using
      congrArg (fun K : Submodule R E ↦ z ∈ K) hstable.symm
  rw [hcomap]
  simp

/-- Removing a finite-length invariant submodule on which all failure of
injectivity is concentrated preserves the principal Koszul Euler length.
The hypothesis `T.comap f = T` says precisely that the quotient action is
injective; it does not assert injectivity on the original module. -/
theorem length_cokernel_eq_kernel_add_regular_quotient
    (f : Module.End R E) (T : Submodule R E)
    [IsNoetherian R T] [IsArtinian R T] (hT : T.comap f = T) :
    Module.length R (E ⧸ f.range) =
      Module.length R f.ker + Module.length R (E ⧸ (T ⊔ f.range)) := by
  have hstable : ∀ z ∈ T, f z ∈ T := by
    intro z hz
    exact show z ∈ T.comap f from hT.symm ▸ hz
  let fT : Module.End R T := f.restrict hstable
  have hpre : f.range.comap T.subtype = fT.range := by
    ext z
    constructor
    · rintro ⟨w, hw⟩
      have hwT : w ∈ T := by
        rw [← hT]
        exact show f w ∈ T from hw ▸ z.property
      exact ⟨⟨w, hwT⟩, Subtype.ext hw⟩
    · rintro ⟨w, rfl⟩
      exact ⟨w.val, rfl⟩
  let i : (T ⧸ fT.range) →ₗ[R] (E ⧸ f.range) :=
    fT.range.mapQ f.range T.subtype hpre.ge
  let j : (E ⧸ f.range) →ₗ[R] (E ⧸ (T ⊔ f.range)) :=
    f.range.mapQ (T ⊔ f.range) LinearMap.id le_sup_right
  have hi : Function.Injective i := by
    rw [← LinearMap.ker_eq_bot]
    dsimp [i]
    rw [Submodule.ker_mapQ, hpre, Submodule.mkQ_map_self]
  have hj : Function.Surjective j := by
    rw [← LinearMap.range_eq_top]
    simp [j, Submodule.range_mapQ]
  have hexact : Function.Exact i j := by
    rw [LinearMap.exact_iff]
    simp [i, j, Submodule.range_mapQ, Submodule.ker_mapQ,
      Submodule.map_sup, Submodule.mkQ_map_self]
  have hsum := Module.length_eq_add_of_exact i j hi hj hexact
  have hkerle : f.ker ≤ T := by
    intro z hz
    rw [← hT]
    change f z ∈ T
    rw [LinearMap.mem_ker.mp hz]
    exact T.zero_mem
  have hker : Module.length R fT.ker = Module.length R f.ker := by
    have hk : fT.ker = f.ker.comap T.subtype := by
      simp [fT, LinearMap.ker_restrict]
    rw [hk]
    exact (Submodule.comapSubtypeEquivOfLe hkerle).length_eq
  have hsource := Module.length_eq_add_of_exact fT.ker.subtype fT.rangeRestrict
    (Submodule.subtype_injective _)
    (LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict fT))
    (by rw [LinearMap.exact_iff, Submodule.range_subtype, LinearMap.ker_rangeRestrict])
  have htarget := Module.length_eq_add_of_exact fT.range.subtype fT.range.mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _)
  have hcancel : Module.length R (T ⧸ fT.range) = Module.length R fT.ker := by
    have hfinite : Module.length R fT.range ≠ ⊤ := Module.length_ne_top
    apply ENat.add_left_injective_of_ne_top hfinite
    change Module.length R (T ⧸ fT.range) + Module.length R fT.range =
      Module.length R fT.ker + Module.length R fT.range
    rw [add_comm (Module.length R (T ⧸ fT.range)), ← htarget]
    exact hsource
  rw [hcancel, hker] at hsum
  exact hsum

/-- A maximal-ideal scalar has a proper image on a nonzero finite module. -/
theorem scalar_range_ne_top_of_mem_maximalIdeal
    [IsLocalRing R] [Module.Finite R E] [Nontrivial E]
    {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R) :
    (scalarEnd (E := E) x).range ≠ (⊤ : Submodule R E) := by
  have hann : Module.annihilator R E ≠ ⊤ := by
    intro h
    exact not_subsingleton_iff_nontrivial.mpr inferInstance
      (Module.annihilator_eq_top_iff.mp h)
  have hspan : Ideal.span ({x} : Set R) ≤
      (Module.annihilator R E).jacobson := by
    rw [Ideal.span_singleton_le_iff_mem]
    rw [IsLocalRing.jacobson_eq_maximalIdeal _ hann]
    exact hx
  have hsmul : (⊤ : Submodule R E) ≠ Ideal.span ({x} : Set R) • (⊤ : Submodule R E) :=
    Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator hspan
  intro hrange
  apply hsmul
  have hEq : (scalarEnd (E := E) x).range =
      Ideal.span ({x} : Set R) • (⊤ : Submodule R E) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact Submodule.smul_mem_smul (Submodule.subset_span (Set.mem_singleton x))
        (Submodule.mem_top)
    · intro hy
      refine Submodule.smul_induction_on hy ?_ (fun a b ha hb => ?_)
      · intro r hr z hz
        rcases (Ideal.mem_span_singleton.mp hr) with ⟨c, rfl⟩
        refine ⟨c • z, ?_⟩
        simp [scalarEnd, smul_smul, mul_comm]
      · exact add_mem (by assumption) (by assumption)
  exact hrange.symm.trans hEq

/--
If multiplication by `x` is injective on a nonzero finite local module and
its cokernel has finite length, then the cokernel has strictly larger length
than the kernel.  The quotient is nonzero by Nakayama, so the conclusion is
genuine positivity rather than an axiom-shaped length assumption.

This is only the regular (torsion-free) specialization of the stabilized
`x`-power-torsion cancellation argument.  Minimal-support avoidance alone
does not imply its injectivity hypothesis when embedded torsion is present.
-/
theorem length_cokernel_smul_gt_length_kernel_smul
    [IsLocalRing R] [Module.Finite R E] [Nontrivial E] {x : R}
    (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hinj : Function.Injective (scalarEnd (E := E) x))
    (_hfinite : IsFiniteLength R (E ⧸ (scalarEnd (E := E) x).range)) :
    Module.length R (E ⧸ (scalarEnd (E := E) x).range) >
      Module.length R (scalarEnd (E := E) x).ker := by
  have hker : (scalarEnd (E := E) x).ker = ⊥ := by
    apply le_antisymm
    · intro y hy
      apply hinj
      simpa using (LinearMap.mem_ker.mp hy)
    · exact bot_le
  have hq : Nontrivial (E ⧸ (scalarEnd (E := E) x).range) :=
    Submodule.Quotient.nontrivial_iff.mpr
      (scalar_range_ne_top_of_mem_maximalIdeal hx)
  rw [hker, Module.length_bot]
  exact Module.length_pos

/-- Embedded scalar-power torsion may be retained: after its finite-length
Euler contribution is cancelled, any nonzero regular quotient contributes
strictly positively by Nakayama. -/
theorem length_cokernel_smul_gt_kernel_of_finite_torsion
    [IsLocalRing R] [Module.Finite R E]
    {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (T : Submodule R E) [IsNoetherian R T] [IsArtinian R T]
    (hT : T.comap (scalarEnd (E := E) x) = T) (hproper : T ≠ ⊤) :
    Module.length R (E ⧸ (scalarEnd (E := E) x).range) >
      Module.length R (scalarEnd (E := E) x).ker := by
  let f := scalarEnd (E := E) x
  have hstable : T ≤ T.comap f := hT.ge
  let g : Module.End R (E ⧸ T) := T.mapQ T f hstable
  have hg : g = scalarEnd (E := E ⧸ T) x := by
    ext z
    rfl
  have hrange : g.range = f.range.map T.mkQ := Submodule.range_mapQ _ _ _ _
  let : Nontrivial (E ⧸ T) := Submodule.Quotient.nontrivial_iff.mpr hproper
  have hnontop : f.range.map T.mkQ ≠ ⊤ := by
    rw [← hrange, hg]
    exact scalar_range_ne_top_of_mem_maximalIdeal hx
  let : Nontrivial ((E ⧸ T) ⧸ f.range.map T.mkQ) :=
    Submodule.Quotient.nontrivial_iff.mpr hnontop
  have hpositive : 0 < Module.length R (E ⧸ (T ⊔ f.range)) := by
    rw [← (Submodule.quotientQuotientEquivQuotientSup T f.range).length_eq]
    exact Module.length_pos
  have hkerle : f.ker ≤ T := by
    intro z hz
    rw [← hT]
    change f z ∈ T
    rw [LinearMap.mem_ker.mp hz]
    exact T.zero_mem
  let : IsNoetherian R f.ker :=
    isNoetherian_of_injective (Submodule.inclusion hkerle)
      (Submodule.inclusion_injective hkerle)
  let : IsArtinian R f.ker :=
    isArtinian_of_injective (Submodule.inclusion hkerle)
      (Submodule.inclusion_injective hkerle)
  rw [length_cokernel_eq_kernel_add_regular_quotient f T hT]
  simpa [add_comm] using ENat.lt_add_left (Module.length_ne_top (R := R) (M := f.ker)) hpositive

/-- Principal Koszul positivity, including embedded torsion. A support prime
not containing `x` guarantees a nonzero regular quotient; finite length of
the coordinate kernel makes the discarded power torsion finite length. -/
theorem length_cokernel_smul_gt_kernel_of_support_prime
    [IsLocalRing R] [Module.Finite R E] [IsNoetherian R E]
    {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    [IsArtinian R (scalarEnd (E := E) x).ker]
    (P : Ideal R) (hP : P.IsPrime)
    (hann : Module.annihilator R E ≤ P) (hxP : x ∉ P) :
    Module.length R (E ⧸ (scalarEnd (E := E) x).range) >
      Module.length R (scalarEnd (E := E) x).ker := by
  let f := scalarEnd (E := E) x
  obtain ⟨n, hn⟩ := exists_stable_kernel_power f
  let T := (f ^ n).ker
  let : IsArtinian R T := isArtinian_kernel_power f n
  have hcomap : T.comap f = T := by
    ext z
    rw [Submodule.mem_comap]
    change (f ^ n) (f z) = 0 ↔ (f ^ n) z = 0
    rw [← Module.End.mul_apply, (Commute.self_pow f n).eq.symm,
      Module.End.mul_apply]
    simpa [Module.End.pow_apply, Function.iterate_succ_apply'] using
      congrArg (fun K : Submodule R E ↦ z ∈ K) hn.symm
  have hpower : ∀ m (z : E), (f ^ m) z = x ^ m • z := by
    intro m
    induction m with
    | zero => intro z; simp
    | succ m ih =>
      intro z
      simp [pow_succ, Module.End.mul_apply, ih, f, scalarEnd, smul_smul]
  have hproper : T ≠ ⊤ := by
    intro htop
    apply hxP
    apply hP.mem_of_pow_mem n
    apply hann
    rw [Module.mem_annihilator]
    intro z
    rw [← hpower n z]
    exact LinearMap.mem_ker.mp (show z ∈ T by rw [htop]; trivial)
  exact length_cokernel_smul_gt_kernel_of_finite_torsion hx T hcomap hproper


end
end AlgebraicAnalysis.PrincipalKoszulPositivity
