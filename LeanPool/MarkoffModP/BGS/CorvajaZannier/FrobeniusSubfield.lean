/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.Derivation.Basic

/-!
# The Frobenius subfield

Every derivation in characteristic `p` kills `p`-th powers.  Consequently the
image of Frobenius is contained in the derivation's constant field.  The
field extension over that image is purely inseparable.  If a parameter `z` is
not a `p`-th power and the extension over `L^p(z)` is separable, the two
properties force `L = L^p(z)`; Kummer irreducibility then gives the exact
degree `[L : L^p] = p`.

The last two hypotheses are the algebraic boundary at which the geometric
notion of a separating parameter enters.  They are explicit theorem
hypotheses rather than hidden curve axioms.

For such a parameter, polynomial differentiation descends along evaluation
at `z` to a derivation of `L`.  Its constants are exactly the Frobenius
subfield: the degree-`< p` normal form of an element has zero derivative only
when it is constant.
-/

namespace BGS.CorvajaZannier

noncomputable section

/-- The subfield of `p`-th powers in a field of prime characteristic `p`. -/
abbrev frobeniusSubfield (L : Type*) [Field L] (p : ℕ)
    [Fact p.Prime] [CharP L p] : Subfield L :=
  (frobenius L p).fieldRange

variable {R L : Type*} [CommRing R] [Field L] [Algebra R L]
  {p : ℕ} [Fact p.Prime] [CharP L p]

/-- Every Frobenius power is killed by every derivation. -/
theorem derivation_frobenius_eq_zero (D : Derivation R L L) (x : L) :
    D (frobenius L p x) = 0 := by
  rw [frobenius_def, D.leibniz_pow]
  simp

/-- The Frobenius image subfield is contained in the constant field of every
derivation. -/
theorem frobenius_fieldRange_is_constant (D : Derivation R L L)
    (x : (frobenius L p).fieldRange) :
    D (x : L) = 0 := by
  rcases x.2 with ⟨y, hy⟩
  rw [← hy]
  exact derivation_frobenius_eq_zero D y

section FrobeniusDegree

variable {L : Type*} [Field L] (p : ℕ) [Fact p.Prime] [CharP L p]

/-- The extension of a characteristic-`p` field over its Frobenius image is
purely inseparable (of exponent at most one). -/
theorem frobeniusSubfield_isPurelyInseparable :
    IsPurelyInseparable (frobeniusSubfield L p) L := by
  rw [isPurelyInseparable_iff_pow_mem (frobeniusSubfield L p) p]
  intro x
  refine ⟨1, ?_⟩
  rw [pow_one]
  exact ⟨⟨x ^ p, ⟨x, by simp [frobenius_def]⟩⟩, rfl⟩

/-- A parameter over which the Frobenius-pure extension becomes separable
generates the whole field over the Frobenius subfield.

This is the algebraic first assertion of the separating-parameter lemma: the
extension over `L^p(z)` is simultaneously purely inseparable and separable,
and is therefore trivial. -/
theorem adjoin_frobeniusSubfield_eq_top
    (z : L)
    [Algebra.IsSeparable
      (IntermediateField.adjoin (frobeniusSubfield L p) {z}) L] :
    IntermediateField.adjoin (frobeniusSubfield L p) {z} = ⊤ := by
  let F : Subfield L := frobeniusSubfield L p
  let E : IntermediateField F L := IntermediateField.adjoin F {z}
  let : IsPurelyInseparable F L := frobeniusSubfield_isPurelyInseparable p
  let : IsPurelyInseparable E L := IsPurelyInseparable.tower_top F E L
  have hbij : Function.Bijective (algebraMap E L) :=
    IsPurelyInseparable.bijective_algebraMap_of_isSeparable E L
  change E = ⊤
  apply top_unique
  intro x _
  obtain ⟨y, hy⟩ := hbij.2 x
  rw [← hy]
  exact y.property

/-- A Frobenius-separating parameter gives the exact degree of the Frobenius
subfield.

The separability hypothesis implies that the simultaneously purely
inseparable extension `L / L^p(z)` is trivial.  Since `z` is not in `L^p`, its
minimal polynomial over `L^p` is the irreducible polynomial
`X ^ p - z ^ p`, of degree `p`. -/
theorem finrank_frobeniusSubfield_eq_char
    (z : L) (hz : z ∉ frobeniusSubfield L p)
    [Algebra.IsSeparable
      (IntermediateField.adjoin (frobeniusSubfield L p) {z}) L] :
    Module.finrank (frobeniusSubfield L p) L = p := by
  let F : Subfield L := frobeniusSubfield L p
  let E : IntermediateField F L := IntermediateField.adjoin F {z}
  let zp : F := ⟨z ^ p, ⟨z, by simp [frobenius_def]⟩⟩
  have hnoRoot : ∀ b : F, b ^ p ≠ zp := by
    intro b hb
    apply hz
    have hpowers : (b : L) ^ p = z ^ p := by
      simpa [zp] using congrArg Subtype.val hb
    have hbz : (b : L) = z := by
      exact frobenius_inj L p (by simpa [frobenius_def] using hpowers)
    rw [← hbz]
    exact b.property
  have hirr : Irreducible (Polynomial.X ^ p - Polynomial.C zp) :=
    X_pow_sub_C_irreducible_of_prime (Fact.out : p.Prime) hnoRoot
  have hmonic : (Polynomial.X ^ p - Polynomial.C zp).Monic :=
    Polynomial.monic_X_pow_sub_C zp (Fact.out : p.Prime).ne_zero
  have hroot : Polynomial.aeval z (Polynomial.X ^ p - Polynomial.C zp) = 0 := by
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [Subfield.algebraMap_ofSubfield]
    simp [zp]
  have hzint : IsIntegral F z := ⟨_, hmonic, hroot⟩
  have hminpoly : minpoly F z = Polynomial.X ^ p - Polynomial.C zp :=
    (minpoly.eq_of_irreducible_of_monic hirr hroot hmonic).symm
  have hfinE : Module.finrank F E = p := by
    rw [IntermediateField.adjoin.finrank hzint, hminpoly,
      Polynomial.natDegree_X_pow_sub_C]
  let : IsPurelyInseparable F L := frobeniusSubfield_isPurelyInseparable p
  let : IsPurelyInseparable E L := IsPurelyInseparable.tower_top F E L
  have hbij : Function.Bijective (algebraMap E L) :=
    IsPurelyInseparable.bijective_algebraMap_of_isSeparable E L
  let e : E ≃ₐ[F] L :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom F E L) hbij
  exact e.toLinearEquiv.finrank_eq ▸ hfinE

/-- A Frobenius-separating parameter determines a derivation whose constant
field is exactly the Frobenius subfield.

The derivation is obtained by descending polynomial differentiation through
the surjective evaluation map `F[X] → L`, where `F = L^p`.  Its kernel is
computed from the unique polynomial representative of degree less than `p`:
in characteristic `p`, a polynomial with zero derivative is an expansion in
`X ^ p`, and the degree bound forces that expansion to be constant. -/
theorem exists_derivation_with_exact_frobenius_constants
    (z : L) (hz : z ∉ frobeniusSubfield L p)
    [Algebra.IsSeparable
      (IntermediateField.adjoin (frobeniusSubfield L p) {z}) L] :
    ∃ D : Derivation (frobeniusSubfield L p) L L,
      D z = 1 ∧
        ∀ x : L, D x = 0 ↔
          ∃ c : frobeniusSubfield L p,
            algebraMap (frobeniusSubfield L p) L c = x := by
  let F : Subfield L := frobeniusSubfield L p
  let E : IntermediateField F L := IntermediateField.adjoin F {z}
  let zp : F := ⟨z ^ p, ⟨z, by simp [frobenius_def]⟩⟩
  have hnoRoot : ∀ b : F, b ^ p ≠ zp := by
    intro b hb
    apply hz
    have hpowers : (b : L) ^ p = z ^ p := by
      simpa [zp] using congrArg Subtype.val hb
    have hbz : (b : L) = z := by
      exact frobenius_inj L p (by simpa [frobenius_def] using hpowers)
    rw [← hbz]
    exact b.property
  have hirr : Irreducible (Polynomial.X ^ p - Polynomial.C zp) :=
    X_pow_sub_C_irreducible_of_prime (Fact.out : p.Prime) hnoRoot
  have hmonic : (Polynomial.X ^ p - Polynomial.C zp).Monic :=
    Polynomial.monic_X_pow_sub_C zp (Fact.out : p.Prime).ne_zero
  have hroot : Polynomial.aeval z (Polynomial.X ^ p - Polynomial.C zp) = 0 := by
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [Subfield.algebraMap_ofSubfield]
    simp [zp]
  have hzint : IsIntegral F z := ⟨_, hmonic, hroot⟩
  have hminpoly : minpoly F z = Polynomial.X ^ p - Polynomial.C zp :=
    (minpoly.eq_of_irreducible_of_monic hirr hroot hmonic).symm
  let : IsPurelyInseparable F L := frobeniusSubfield_isPurelyInseparable p
  let : IsPurelyInseparable E L := IsPurelyInseparable.tower_top F E L
  have hbij : Function.Bijective (algebraMap E L) :=
    IsPurelyInseparable.bijective_algebraMap_of_isSeparable E L
  have hEtop : E = ⊤ := by
    apply top_unique
    intro x hx
    obtain ⟨y, hy⟩ := hbij.2 x
    rw [← hy]
    exact y.property
  have hAlgTop : Algebra.adjoin F {z} = ⊤ := by
    have hzalg : IsAlgebraic F z := hzint.isAlgebraic
    apply (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic
      (S := ({z} : Set L)) (by simpa)).mp
    simpa [E] using hEtop
  have heval : Function.Surjective
      (Polynomial.aeval z : Polynomial F →ₐ[F] L) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval]
    exact hAlgTop
  have hderivMin : Polynomial.derivative (minpoly F z) = 0 := by
    rw [hminpoly]
    simp [Polynomial.derivative_pow]
  have hstable : ∀ q : Polynomial F, Polynomial.aeval z q = 0 →
      Polynomial.aeval z q.derivative = 0 := by
    intro q hq
    rcases minpoly.dvd F z hq with ⟨r, rfl⟩
    rw [Polynomial.derivative_mul, hderivMin]
    simp [minpoly.aeval]
  let D : Derivation F L L :=
    Polynomial.derivative'.liftOfSurjective heval hstable
  have hDz : D z = 1 := by
    have h := Derivation.liftOfSurjective_apply
      (d := Polynomial.derivative') heval hstable Polynomial.X
    simpa [D] using h
  refine ⟨D, hDz, ?_⟩
  intro x
  change D x = 0 ↔ ∃ c : F, algebraMap F L c = x
  constructor
  · intro hx
    let pb : PowerBasis F L := PowerBasis.ofAdjoinEqTop hzint hAlgTop
    obtain ⟨q, hqdeg, hxq⟩ := pb.exists_eq_aeval x
    have hpbgen : pb.gen = z := PowerBasis.ofAdjoinEqTop_gen hzint hAlgTop
    have hpbDim : pb.dim = p := by
      rw [PowerBasis.ofAdjoinEqTop_dim, hminpoly,
        Polynomial.natDegree_X_pow_sub_C]
    rw [hpbDim] at hqdeg
    rw [hpbgen] at hxq
    have hEvalDeriv : Polynomial.aeval z q.derivative = 0 := by
      have h := Derivation.liftOfSurjective_apply
        (d := Polynomial.derivative') heval hstable q
      change Polynomial.aeval z (Polynomial.derivative' q) = 0
      rw [← h, ← hxq]
      exact hx
    have hqderiv : q.derivative = 0 := by
      by_contra hne
      have hdvd : minpoly F z ∣ q.derivative := minpoly.dvd F z hEvalDeriv
      have hle := Polynomial.natDegree_le_of_dvd hdvd hne
      rw [hminpoly, Polynomial.natDegree_X_pow_sub_C] at hle
      have hlt : q.derivative.natDegree < p := by
        exact (Polynomial.natDegree_derivative_le q).trans_lt
          ((Nat.sub_le q.natDegree 1).trans_lt hqdeg)
      exact (Nat.not_lt_of_ge hle) hlt
    have hexpand : Polynomial.expand F p (Polynomial.contract p q) = q :=
      Polynomial.expand_contract p hqderiv (Fact.out : p.Prime).ne_zero
    have hcontractDegree : (Polynomial.contract p q).natDegree = 0 := by
      have hdegrees : (Polynomial.contract p q).natDegree * p = q.natDegree := by
        simpa only [Polynomial.natDegree_expand] using
          congrArg Polynomial.natDegree hexpand
      by_contra hne
      have hpos : 0 < (Polynomial.contract p q).natDegree := Nat.pos_of_ne_zero hne
      have hp_le : p ≤ q.natDegree := by
        calc
          p ≤ (Polynomial.contract p q).natDegree * p :=
            Nat.le_mul_of_pos_left p hpos
          _ = q.natDegree := hdegrees
      exact (Nat.not_le_of_lt hqdeg) hp_le
    have hqConstant : q = Polynomial.C ((Polynomial.contract p q).coeff 0) := by
      rw [← hexpand, Polynomial.eq_C_of_natDegree_eq_zero hcontractDegree]
      simp
    refine ⟨(Polynomial.contract p q).coeff 0, ?_⟩
    rw [hxq, hqConstant]
    simp
  · rintro ⟨c, rfl⟩
    exact D.map_algebraMap c

end FrobeniusDegree

end

end BGS.CorvajaZannier
