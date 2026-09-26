/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassSubgroupRealization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeSplitsCompletely
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusEqOneIffSplitsCompletely
/-!
# Prime splitting in a ray-class subgroup class field

At a prime away from the modulus, complete splitting is equivalent to
membership of the prime's ray class in the defining subgroup.
-/

@[expose] public section

open scoped NumberField

noncomputable
section

namespace ClassFieldTheory

open NumberField IsDedekindDomain

universe u

open scoped Classical in
/-- A prime away from the modulus splits completely in the class field of
`H` exactly when its ray class belongs to `H`. -/
theorem finitePrime_splitsCompletelyInRayClassSubgroupField_iff
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) (H : Subgroup (RayClassGroup m))
    (R : RayClassSubgroupRealization K m H)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    FinitePrimeSplitsCompletely K R.extension v ↔
      rayClassOfFinitePrime m v hv ∈ H := by
  have hunram : Algebra.IsUnramifiedIn (𝓞 R.extension) v.asIdeal :=
    R.unramifiedOutsideModulus.1 v hv
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := 𝓞 R.extension) v.asIdeal
  let : Q.LiesOver v.asIdeal := hQover
  let w : HeightOneSpectrum (𝓞 R.extension) :=
    ⟨Q, hQmax.isPrime,
      Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
  have hw : w.asIdeal.LiesOver v.asIdeal := hQover
  have hmem : rayClassOfFinitePrime m v hv ∈ H ↔
      R.artin (rayClassOfFinitePrime m v hv) = 1 := by
    simpa only [R.artin_ker] using
      (MonoidHom.mem_ker : rayClassOfFinitePrime m v hv ∈ R.artin.ker ↔
        R.artin (rayClassOfFinitePrime m v hv) = 1)
  rw [hmem, R.artin_frobenius v hv w hw]
  exact (arithmeticFrobeniusAt_eq_one_iff_splitsCompletely
    v w hw hunram).symm

end ClassFieldTheory
