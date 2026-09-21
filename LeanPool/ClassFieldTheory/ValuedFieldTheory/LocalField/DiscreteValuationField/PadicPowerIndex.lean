/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PowerIndex
import Mathlib.NumberTheory.Padics.RingHoms
/-!
# The `n`-fold multiple quotient of `Z_p`

This is the free p-adic factor in the local-field structure theory, the local-field power-index formula.
-/

noncomputable section

universe u

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory

namespace LocalFieldTheory.DiscreteValuationField

variable {p : ℕ} [Fact p.Prime]

/-- The normalized local absolute value of a natural number in a degree-`d`
mixed-characteristic local field.  Since `d = ef` and `q = p^f`, this is
exactly `q^(-e v_p(n))`, the normalized factor `|n|_𝔭`. -/
def normalizedLocalNatAbs (p d n : ℕ) : ℚ :=
  (p : ℚ) ^ (-(d * padicValNat p n : ℕ) : ℤ)

omit [Fact p.Prime] in
/-- The reciprocal of the normalized local absolute value is the integral
defect factor occurring in the local-field power-index formula. -/
theorem one_div_normalizedLocalNatAbs (d n : ℕ) :
    1 / normalizedLocalNatAbs p d n =
      (p ^ (d * padicValNat p n) : ℕ) := by
  simp [normalizedLocalNatAbs, div_eq_mul_inv]
  norm_cast

/-- Additive `n`-fold multiples in `Z_p` are the principal ideal generated
by the natural number `n`. -/
theorem nsmulAddSubgroup_padicInt_eq_span (n : ℕ) :
    LocalFieldTheory.nsmulAddSubgroup ℤ_[p] n =
      (Ideal.span ({(n : ℤ_[p])} : Set ℤ_[p])).toAddSubgroup := by
  ext x
  rw [LocalFieldTheory.mem_nsmulAddSubgroup_iff]
  change (∃ y : ℤ_[p], n • y = x) ↔
    x ∈ Ideal.span ({(n : ℤ_[p])} : Set ℤ_[p])
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    simp [nsmul_eq_mul]
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    simp [nsmul_eq_mul]

/-- The valuation of a nonzero natural number in `Z_p` is `v_p(n)`. -/
theorem padicInt_valuation_natCast (n : ℕ) :
    (n : ℤ_[p]).valuation = padicValNat p n := by
  have h : (((n : ℤ_[p]) : ℚ_[p])).valuation =
      (padicValNat p n : ℤ) := by
    simpa only [PadicInt.coe_natCast] using
      Padic.valuation_natCast (p := p) n
  rw [PadicInt.valuation_coe] at h
  exact_mod_cast h

/-- A nonzero natural number generates the same ideal in `Z_p` as the
corresponding power of `p`. -/
theorem padicInt_span_natCast_eq_span_p_pow_padicValNat
    (n : ℕ) (hn : n ≠ 0) :
    Ideal.span ({(n : ℤ_[p])} : Set ℤ_[p]) =
      Ideal.span ({(p : ℤ_[p]) ^ padicValNat p n} : Set ℤ_[p]) := by
  rw [Ideal.span_singleton_eq_span_singleton]
  have hnZ : (n : ℤ_[p]) ≠ 0 := by exact_mod_cast hn
  have hfactor := PadicInt.unitCoeff_spec hnZ
  rw [padicInt_valuation_natCast] at hfactor
  rw [hfactor]
  exact associated_unit_mul_left _ _ (PadicInt.unitCoeff hnZ).isUnit

/-- The subgroup of `n`-fold multiples is the kernel of reduction modulo
`p ^ v_p(n)`. -/
theorem nsmulAddSubgroup_padicInt_eq_ker_toZModPow
    (n : ℕ) (hn : n ≠ 0) :
    LocalFieldTheory.nsmulAddSubgroup ℤ_[p] n =
      (PadicInt.toZModPow (p := p) (padicValNat p n)).toAddMonoidHom.ker := by
  rw [nsmulAddSubgroup_padicInt_eq_span,
    padicInt_span_natCast_eq_span_p_pow_padicValNat n hn,
    ← PadicInt.ker_toZModPow]
  rfl

/-- The additive quotient `Z_p / n Z_p` is the expected finite cyclic
group of order `p ^ v_p(n)`. -/
noncomputable def padicIntNsmulQuotientEquivZMod
    (n : ℕ) (hn : n ≠ 0) :
    ℤ_[p] ⧸ LocalFieldTheory.nsmulAddSubgroup ℤ_[p] n ≃+
      ZMod (p ^ padicValNat p n) := by
  let f : ℤ_[p] →+ ZMod (p ^ padicValNat p n) :=
    (PadicInt.toZModPow (p := p) (padicValNat p n)).toAddMonoidHom
  have hf : Function.Surjective f :=
    ZMod.ringHom_surjective
      (PadicInt.toZModPow (p := p) (padicValNat p n))
  have hker : LocalFieldTheory.nsmulAddSubgroup ℤ_[p] n = f.ker := by
    simpa [f] using nsmulAddSubgroup_padicInt_eq_ker_toZModPow
      (p := p) n hn
  exact (QuotientAddGroup.quotientAddEquivOfEq hker).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective f hf)

/-- The quotient `Z_p / n Z_p` is finite for nonzero `n`, transported from
its canonical `ZMod` model. -/
noncomputable instance finite_padicInt_nsmulQuotient
    (n : ℕ) [NeZero n] :
    Finite (ℤ_[p] ⧸ LocalFieldTheory.nsmulAddSubgroup ℤ_[p] n) :=
  Finite.of_equiv (ZMod (p ^ padicValNat p n))
    (padicIntNsmulQuotientEquivZMod (p := p) n (NeZero.ne n)).symm.toEquiv

/-- Cardinality of the one-dimensional p-adic free-factor quotient. -/
theorem card_padicInt_nsmulQuotient
    (n : ℕ) [NeZero n] :
    Nat.card (ℤ_[p] ⧸ LocalFieldTheory.nsmulAddSubgroup ℤ_[p] n) =
      p ^ padicValNat p n := by
  rw [Nat.card_congr (padicIntNsmulQuotientEquivZMod
    (p := p) n (NeZero.ne n)).toEquiv, Nat.card_zmod]

/-- Coordinatewise reduction identifies the quotient of an arbitrary product
of copies of `Z_p` by `n`-fold multiples with a product of finite cyclic
groups. -/
noncomputable def padicIntPiNsmulQuotientEquiv
    {ι : Type u} (n : ℕ) (hn : n ≠ 0) :
    (ι → ℤ_[p]) ⧸ LocalFieldTheory.nsmulAddSubgroup (ι → ℤ_[p]) n ≃+
      (ι → ZMod (p ^ padicValNat p n)) := by
  let a := padicValNat p n
  let f : (ι → ℤ_[p]) →+ (ι → ZMod (p ^ a)) :=
    { toFun := fun x i => PadicInt.toZModPow a (x i)
      map_zero' := by ext i; simp
      map_add' := by intro x y; ext i; simp }
  have hf : Function.Surjective f := by
    intro y
    have hcoord : ∀ i : ι, ∃ x : ℤ_[p],
        PadicInt.toZModPow a x = y i := by
      intro i
      exact ZMod.ringHom_surjective (PadicInt.toZModPow a) (y i)
    choose x hx using hcoord
    refine ⟨x, ?_⟩
    ext i
    exact hx i
  have hkerOne : LocalFieldTheory.nsmulAddSubgroup ℤ_[p] n =
      (PadicInt.toZModPow (p := p) a).toAddMonoidHom.ker := by
    simpa [a] using nsmulAddSubgroup_padicInt_eq_ker_toZModPow
      (p := p) n hn
  have hker : LocalFieldTheory.nsmulAddSubgroup (ι → ℤ_[p]) n = f.ker := by
    ext x
    constructor
    · intro hx
      rw [LocalFieldTheory.mem_nsmulAddSubgroup_iff] at hx
      rcases hx with ⟨y, rfl⟩
      change f (n • y) = 0
      ext i
      have hi : n • y i ∈ LocalFieldTheory.nsmulAddSubgroup ℤ_[p] n :=
        (LocalFieldTheory.mem_nsmulAddSubgroup_iff (A := ℤ_[p])).2 ⟨y i, rfl⟩
      rw [hkerOne] at hi
      exact hi
    · intro hx
      change f x = 0 at hx
      have hcoord : ∀ i : ι, ∃ y : ℤ_[p], n • y = x i := by
        intro i
        rw [← LocalFieldTheory.mem_nsmulAddSubgroup_iff]
        rw [hkerOne]
        change PadicInt.toZModPow a (x i) = 0
        exact congrFun hx i
      choose y hy using hcoord
      rw [LocalFieldTheory.mem_nsmulAddSubgroup_iff]
      refine ⟨y, ?_⟩
      funext i
      exact hy i
  exact (QuotientAddGroup.quotientAddEquivOfEq hker).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective f hf)

/-- A finite product of nonzero scalar quotients of `Z_p` is finite. -/
noncomputable instance finite_padicInt_finPi_nsmulQuotient
    (d n : ℕ) [NeZero n] :
    Finite ((Fin d → ℤ_[p]) ⧸
      LocalFieldTheory.nsmulAddSubgroup (Fin d → ℤ_[p]) n) :=
  Finite.of_equiv
    (Fin d → ZMod (p ^ padicValNat p n))
    (padicIntPiNsmulQuotientEquiv
      (p := p) (ι := Fin d) n (NeZero.ne n)).symm.toEquiv

/-- A finite product of `d` copies contributes the expected
`p^(d v_p(n))` factor. -/
theorem card_padicInt_finPi_nsmulQuotient
    (d n : ℕ) [NeZero n] :
    Nat.card ((Fin d → ℤ_[p]) ⧸
        LocalFieldTheory.nsmulAddSubgroup (Fin d → ℤ_[p]) n) =
      p ^ (d * padicValNat p n) := by
  rw [Nat.card_congr
    (padicIntPiNsmulQuotientEquiv
      (p := p) (ι := Fin d) n (NeZero.ne n)).toEquiv,
    Nat.card_pi]
  simp only [Nat.card_zmod, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← pow_mul, Nat.mul_comm]

/-- If `n` is nonzero and prime to `p`, the quotient of an arbitrary product
of copies of `Z_p` is finite (indeed, a singleton). -/
noncomputable instance finite_padicInt_pi_nsmulQuotient_of_coprime
    {ι : Type u} (n : ℕ) [NeZero n] [Fact (Nat.Coprime n p)] :
    Finite ((ι → ℤ_[p]) ⧸ LocalFieldTheory.nsmulAddSubgroup (ι → ℤ_[p]) n) := by
  have hpnd : ¬ p ∣ n :=
    (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp
      (Fact.out : Nat.Coprime n p).symm
  have hv : padicValNat p n = 0 :=
    padicValNat.eq_zero_of_not_dvd hpnd
  let target := ι → ZMod (p ^ padicValNat p n)
  let toUnit : target → PUnit := fun _ => PUnit.unit
  have hsub : Subsingleton target := by
    dsimp only [target]
    rw [hv, pow_zero]
    infer_instance
  let : Finite target :=
    Finite.of_injective toUnit fun x y _ => hsub.elim x y
  exact Finite.of_equiv target
    (padicIntPiNsmulQuotientEquiv
      (p := p) (ι := ι) n (NeZero.ne n)).symm.toEquiv

/-- If `n` is prime to `p`, multiplication by `n` is surjective on an
arbitrary product of copies of `Z_p`; hence the quotient is trivial. -/
theorem card_padicInt_pi_nsmulQuotient_of_coprime
    {ι : Type u} (n : ℕ) [NeZero n] [Fact (Nat.Coprime n p)] :
    Nat.card ((ι → ℤ_[p]) ⧸
        LocalFieldTheory.nsmulAddSubgroup (ι → ℤ_[p]) n) = 1 := by
  rw [Nat.card_congr
    (padicIntPiNsmulQuotientEquiv (p := p) (ι := ι) n (NeZero.ne n)).toEquiv]
  have hpnd : ¬ p ∣ n :=
    (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp
      (Fact.out : Nat.Coprime n p).symm
  have hv : padicValNat p n = 0 :=
    padicValNat.eq_zero_of_not_dvd hpnd
  rw [hv, pow_zero]
  exact Nat.card_unique

/-- A nonzero natural scalar has trivial kernel on any product of `Z_p`. -/
theorem nsmulAddKernel_padicInt_pi_eq_bot
    {ι : Type u} (n : ℕ) (hn : n ≠ 0) :
    LocalFieldTheory.nsmulAddKernel (ι → ℤ_[p]) n = ⊥ := by
  have hnZ : (n : ℤ_[p]) ≠ 0 := by exact_mod_cast hn
  ext x
  rw [LocalFieldTheory.mem_nsmulAddKernel_iff]
  simp only [AddSubgroup.mem_bot]
  constructor
  · intro hx
    funext i
    have hi := congrFun hx i
    change n • x i = 0 at hi
    rw [nsmul_eq_mul] at hi
    exact (mul_eq_zero.mp hi).resolve_left hnZ
  · rintro rfl
    simp

/-- Nonzero scalar multiplication has a finite (trivial) kernel on any
product of copies of `Z_p`. -/
noncomputable instance finite_nsmulAddKernel_padicInt_pi
    {ι : Type u} (n : ℕ) [NeZero n] :
    Finite (LocalFieldTheory.nsmulAddKernel (ι → ℤ_[p]) n) := by
  rw [nsmulAddKernel_padicInt_pi_eq_bot (p := p) n (NeZero.ne n)]
  infer_instance

/-- Cardinal form of the preceding torsion-freeness statement. -/
theorem card_nsmulAddKernel_padicInt_pi
    {ι : Type u} (n : ℕ) [NeZero n] :
    Nat.card (LocalFieldTheory.nsmulAddKernel (ι → ℤ_[p]) n) = 1 := by
  rw [nsmulAddKernel_padicInt_pi_eq_bot (p := p) n (NeZero.ne n)]
  exact Nat.card_unique

section Product

variable (A B : Type*) [AddCommGroup A] [AddCommGroup B]

/-- Additive quotients by `n`-fold multiples commute with binary products at
the level of cardinality. -/
theorem card_nsmulAddQuotient_product (n : ℕ)
    [Finite (A ⧸ LocalFieldTheory.nsmulAddSubgroup A n)]
    [Finite (B ⧸ LocalFieldTheory.nsmulAddSubgroup B n)] :
    Nat.card ((A × B) ⧸ LocalFieldTheory.nsmulAddSubgroup (A × B) n) =
      Nat.card (A ⧸ LocalFieldTheory.nsmulAddSubgroup A n) *
        Nat.card (B ⧸ LocalFieldTheory.nsmulAddSubgroup B n) := by
  calc
    Nat.card ((A × B) ⧸ LocalFieldTheory.nsmulAddSubgroup (A × B) n) =
        Nat.card (Multiplicative (A × B) ⧸
          (powMonoidHom n : (Multiplicative (A × B)) →* (Multiplicative (A × B))).range) :=
      (LocalFieldTheory.card_multiplicative_nthPowerQuotient_eq_additive_nsmulQuotient
        (A × B) n).symm
    _ = Nat.card (Multiplicative A ⧸
          (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range) *
        Nat.card (Multiplicative B ⧸
          (powMonoidHom n : (Multiplicative B) →* (Multiplicative B)).range) :=
      LocalFieldTheory.card_nthPowerQuotient_eq_mul_of_mulEquiv_prod
        (Multiplicative (A × B)) (Multiplicative A) (Multiplicative B) n
        (MulEquiv.prodMultiplicative A B)
    _ = Nat.card (A ⧸ LocalFieldTheory.nsmulAddSubgroup A n) *
        Nat.card (B ⧸ LocalFieldTheory.nsmulAddSubgroup B n) := by
      rw [LocalFieldTheory.card_multiplicative_nthPowerQuotient_eq_additive_nsmulQuotient,
        LocalFieldTheory.card_multiplicative_nthPowerQuotient_eq_additive_nsmulQuotient]

/-- Kernels of `n`-fold multiplication commute with binary products at the
level of cardinality. -/
theorem card_nsmulAddKernel_product (n : ℕ)
    [Finite (LocalFieldTheory.nsmulAddKernel A n)]
    [Finite (LocalFieldTheory.nsmulAddKernel B n)] :
    Nat.card (LocalFieldTheory.nsmulAddKernel (A × B) n) =
      Nat.card (LocalFieldTheory.nsmulAddKernel A n) * Nat.card (LocalFieldTheory.nsmulAddKernel B n) := by
  calc
    Nat.card (LocalFieldTheory.nsmulAddKernel (A × B) n) =
        Nat.card ((powMonoidHom n : (Multiplicative (A × B)) →* (Multiplicative (A × B))).ker) :=
      (LocalFieldTheory.card_multiplicative_nthPowerKernel_eq_nsmulAddKernel
        (A × B) n).symm
    _ = Nat.card ((powMonoidHom n : (Multiplicative A × Multiplicative B) →* (Multiplicative A × Multiplicative B)).ker) := by
      rw [Nat.card_congr
        (LocalFieldTheory.nthPowerKernelEquivOfMulEquiv
          (Multiplicative (A × B))
          (Multiplicative A × Multiplicative B) n
          (MulEquiv.prodMultiplicative A B)).toEquiv]
    _ = Nat.card ((powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).ker) *
        Nat.card ((powMonoidHom n : (Multiplicative B) →* (Multiplicative B)).ker) :=
      LocalFieldTheory.card_nthPowerKernelProduct (Multiplicative A) (Multiplicative B) n
    _ = Nat.card (LocalFieldTheory.nsmulAddKernel A n) * Nat.card (LocalFieldTheory.nsmulAddKernel B n) := by
      rw [LocalFieldTheory.card_multiplicative_nthPowerKernel_eq_nsmulAddKernel,
        LocalFieldTheory.card_multiplicative_nthPowerKernel_eq_nsmulAddKernel]

end Product

/-- Mixed-characteristic free-factor calculation in the exact kernel-times-
defect form used by the local-field power-index formula. -/
theorem card_finite_prod_padicInt_finPi_nsmulQuotient_eq_kernel_mul
    (T : Type*) [AddCommGroup T] [Finite T]
    (d n : ℕ) [NeZero n] :
    Nat.card ((T × (Fin d → ℤ_[p])) ⧸
        LocalFieldTheory.nsmulAddSubgroup (T × (Fin d → ℤ_[p])) n) =
      Nat.card (LocalFieldTheory.nsmulAddKernel (T × (Fin d → ℤ_[p])) n) *
        p ^ (d * padicValNat p n) := by
  rw [card_nsmulAddQuotient_product,
    LocalFieldTheory.card_additive_nsmulQuotient_eq_nsmulKernel,
    card_padicInt_finPi_nsmulQuotient (p := p) d n,
    card_nsmulAddKernel_product,
    card_nsmulAddKernel_padicInt_pi (p := p) n]
  simp

/-- Equal-characteristic free-factor calculation: when `p ∤ n`, an arbitrary
product of copies of `Z_p` contributes neither kernel nor cokernel. -/
theorem card_finite_prod_padicInt_pi_nsmulQuotient_eq_kernel_of_coprime
    {ι : Type u} (T : Type*) [AddCommGroup T] [Finite T]
    (n : ℕ) [NeZero n] [Fact (Nat.Coprime n p)] :
    Nat.card ((T × (ι → ℤ_[p])) ⧸
        LocalFieldTheory.nsmulAddSubgroup (T × (ι → ℤ_[p])) n) =
      Nat.card (LocalFieldTheory.nsmulAddKernel (T × (ι → ℤ_[p])) n) := by
  rw [card_nsmulAddQuotient_product,
    LocalFieldTheory.card_additive_nsmulQuotient_eq_nsmulKernel,
    card_padicInt_pi_nsmulQuotient_of_coprime (p := p) n,
    card_nsmulAddKernel_product,
    card_nsmulAddKernel_padicInt_pi (p := p) n]

section LocalFieldIndex

variable {K : Type u} [Field K]

/-- The local-field power-index formula, mixed-characteristic field-index formula supplied directly
by a principal-unit structure theorem. -/
theorem card_fieldUnits_nthPowerQuotient_of_mixedPrincipalUnitStructure
    (F : CompleteDVF.{u, 0} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (T : Type*) [AddCommGroup T] [Finite T]
    (d : ℕ) {n : ℕ} [NeZero n]
    [Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)]
    (e : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃*
      Multiplicative (T × (Fin d → ℤ_[p]))) :
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      n * (Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) *
        p ^ (d * padicValNat p n)) := by
  exact card_fieldUnits_nthPowerQuotient_eq_mul_fieldKernel_of_logEquiv
    (F := F) hπ (A := T × (Fin d → ℤ_[p])) e
      (card_finite_prod_padicInt_finPi_nsmulQuotient_eq_kernel_mul
        (p := p) T d n)

/-- Literal rational form of the mixed-characteristic field formula:
`(Kˣ : Kˣⁿ) = n #μ_n(K) / |n|_𝔭`. -/
theorem card_fieldUnits_nthPowerQuotient_of_mixedPrincipalUnitStructure_rationalFormula
    (F : CompleteDVF.{u, 0} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (T : Type*) [AddCommGroup T] [Finite T]
    (d : ℕ) {n : ℕ} [NeZero n]
    [Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)]
    (e : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃*
      Multiplicative (T × (Fin d → ℤ_[p]))) :
    (Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) : ℚ) =
      (n * Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) : ℕ) /
        normalizedLocalNatAbs p d n := by
  rw [card_fieldUnits_nthPowerQuotient_of_mixedPrincipalUnitStructure
    (p := p) (F := F) hπ T d e]
  push_cast
  have hdefect :
      (p : ℚ) ^ (d * padicValNat p n) =
        1 / normalizedLocalNatAbs p d n := by
    calc
      (p : ℚ) ^ (d * padicValNat p n) =
          ((p ^ (d * padicValNat p n) : ℕ) : ℚ) := by norm_cast
      _ = 1 / normalizedLocalNatAbs p d n :=
        (one_div_normalizedLocalNatAbs (p := p) d n).symm
  rw [hdefect]
  ring

/-- The local-field power-index formula, mixed-characteristic unit-index formula from the same
principal-unit structure theorem. -/
theorem card_units_nthPowerQuotient_of_mixedPrincipalUnitStructure
    (F : CompleteDVF.{u, 0} K) [Finite F.residueField]
    (T : Type*) [AddCommGroup T] [Finite T]
    (d : ℕ) {n : ℕ} [NeZero n]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)]
    (e : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃*
      Multiplicative (T × (Fin d → ℤ_[p]))) :
    Nat.card (F.valuationSubringˣ ⧸
        (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) =
      Nat.card ((powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).ker) *
        p ^ (d * padicValNat p n) := by
  exact card_unit_nthPowerQuotient_eq_mul_unitKernel_of_logEquiv
    (F := F) (A := T × (Fin d → ℤ_[p])) e
      (card_finite_prod_padicInt_finPi_nsmulQuotient_eq_kernel_mul
        (p := p) T d n)

/-- The same mixed-characteristic unit formula with the finite kernel written
as the full field root group `μ_n(K)`. -/
theorem card_units_nthPowerQuotient_of_mixedPrincipalUnitStructure_fieldKernel
    (F : CompleteDVF.{u, 0} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (T : Type*) [AddCommGroup T] [Finite T]
    (d : ℕ) {n : ℕ} [NeZero n]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)]
    (e : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃*
      Multiplicative (T × (Fin d → ℤ_[p]))) :
    Nat.card (F.valuationSubringˣ ⧸
        (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) =
      Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) *
        p ^ (d * padicValNat p n) := by
  rw [card_units_nthPowerQuotient_of_mixedPrincipalUnitStructure
    (p := p) (F := F) T d e]
  rw [card_fieldUnits_nthPowerKernel_eq_unit_nthPowerKernel
    (F := F) hπ n]

/-- Literal rational form of the mixed-characteristic unit formula:
`(U : Uⁿ) = #μ_n(K) / |n|_𝔭`. -/
theorem card_units_nthPowerQuotient_of_mixedPrincipalUnitStructure_rationalFormula
    (F : CompleteDVF.{u, 0} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (T : Type*) [AddCommGroup T] [Finite T]
    (d : ℕ) {n : ℕ} [NeZero n]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)]
    (e : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃*
      Multiplicative (T × (Fin d → ℤ_[p]))) :
    (Nat.card (F.valuationSubringˣ ⧸
        (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) : ℚ) =
      Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) /
        normalizedLocalNatAbs p d n := by
  rw [card_units_nthPowerQuotient_of_mixedPrincipalUnitStructure_fieldKernel
    (p := p) (F := F) hπ T d e]
  push_cast
  have hdefect :
      (p : ℚ) ^ (d * padicValNat p n) =
        1 / normalizedLocalNatAbs p d n := by
    calc
      (p : ℚ) ^ (d * padicValNat p n) =
          ((p ^ (d * padicValNat p n) : ℕ) : ℚ) := by norm_cast
      _ = 1 / normalizedLocalNatAbs p d n :=
        (one_div_normalizedLocalNatAbs (p := p) d n).symm
  rw [hdefect]
  ring

/-- The local-field power-index formula obtained in equal characteristic from the
field-unit structure theorem, the principal-unit product, and the hypothesis `p ∤ n`. -/
theorem card_fieldUnits_nthPowerQuotient_of_equalPrincipalUnitStructure
    (F : CompleteDVF.{u, 0} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    {ι : Type u} (T : Type*) [AddCommGroup T] [Finite T]
    {n : ℕ} [NeZero n] [Fact (Nat.Coprime n p)]
    [Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)]
    (e : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃*
      Multiplicative (T × (ι → ℤ_[p]))) :
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      n * Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) := by
  simpa only [Nat.mul_one] using
    card_fieldUnits_nthPowerQuotient_eq_mul_fieldKernel_of_logEquiv
      (F := F) hπ (A := T × (ι → ℤ_[p])) (c := 1) e
        (by
          rw [Nat.mul_one]
          exact
            card_finite_prod_padicInt_pi_nsmulQuotient_eq_kernel_of_coprime
              (p := p) (ι := ι) T n)

/-- Literal rational form of the equal-characteristic field formula.  Here
the permitted hypothesis `(n,p)=1` makes the local absolute value equal to
one, represented uniformly as `normalizedLocalNatAbs p 0 n`. -/
theorem card_fieldUnits_nthPowerQuotient_of_equalPrincipalUnitStructure_rationalFormula
    (F : CompleteDVF.{u, 0} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    {ι : Type u} (T : Type*) [AddCommGroup T] [Finite T]
    {n : ℕ} [NeZero n] [Fact (Nat.Coprime n p)]
    [Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)]
    (e : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃*
      Multiplicative (T × (ι → ℤ_[p]))) :
    (Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) : ℚ) =
      (n * Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) : ℕ) /
        normalizedLocalNatAbs p 0 n := by
  rw [card_fieldUnits_nthPowerQuotient_of_equalPrincipalUnitStructure
    (p := p) (F := F) hπ T e]
  simp [normalizedLocalNatAbs]

/-- The local-field power-index formula, equal-characteristic unit-index formula. -/
theorem card_units_nthPowerQuotient_of_equalPrincipalUnitStructure
    (F : CompleteDVF.{u, 0} K) [Finite F.residueField]
    {ι : Type u} (T : Type*) [AddCommGroup T] [Finite T]
    {n : ℕ} [NeZero n] [Fact (Nat.Coprime n p)]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)]
    (e : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃*
      Multiplicative (T × (ι → ℤ_[p]))) :
    Nat.card (F.valuationSubringˣ ⧸
        (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) =
      Nat.card ((powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).ker) := by
  simpa only [Nat.mul_one] using
    card_unit_nthPowerQuotient_eq_mul_unitKernel_of_logEquiv
      (F := F) (A := T × (ι → ℤ_[p])) (c := 1) e
        (by
          rw [Nat.mul_one]
          exact
            card_finite_prod_padicInt_pi_nsmulQuotient_eq_kernel_of_coprime
              (p := p) (ι := ι) T n)

/-- The equal-characteristic unit formula with its kernel written as
`μ_n(K)`. -/
theorem card_units_nthPowerQuotient_of_equalPrincipalUnitStructure_fieldKernel
    (F : CompleteDVF.{u, 0} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    {ι : Type u} (T : Type*) [AddCommGroup T] [Finite T]
    {n : ℕ} [NeZero n] [Fact (Nat.Coprime n p)]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)]
    (e : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃*
      Multiplicative (T × (ι → ℤ_[p]))) :
    Nat.card (F.valuationSubringˣ ⧸
        (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) =
      Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) := by
  rw [card_units_nthPowerQuotient_of_equalPrincipalUnitStructure
    (p := p) (F := F) T e]
  rw [card_fieldUnits_nthPowerKernel_eq_unit_nthPowerKernel
    (F := F) hπ n]

/-- Literal rational form of the equal-characteristic unit formula. -/
theorem card_units_nthPowerQuotient_of_equalPrincipalUnitStructure_rationalFormula
    (F : CompleteDVF.{u, 0} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    {ι : Type u} (T : Type*) [AddCommGroup T] [Finite T]
    {n : ℕ} [NeZero n] [Fact (Nat.Coprime n p)]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)]
    (e : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃*
      Multiplicative (T × (ι → ℤ_[p]))) :
    (Nat.card (F.valuationSubringˣ ⧸
        (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) : ℚ) =
      Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) /
        normalizedLocalNatAbs p 0 n := by
  rw [card_units_nthPowerQuotient_of_equalPrincipalUnitStructure_fieldKernel
    (p := p) (F := F) hπ T e]
  simp [normalizedLocalNatAbs]

/-! The exact equal-characteristic specialization, with no artificial finite
factor in the principal-unit product. -/

/-- Equal-characteristic field index from the literal the field-unit structure theorem
product `U^1 ≃ Z_p^ι`. -/
theorem card_fieldUnits_nthPowerQuotient_of_equalPrincipalUnitProduct
    (F : CompleteDVF.{u, 0} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    {ι : Type u} {n : ℕ} [NeZero n] [Fact (Nat.Coprime n p)]
    [Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)]
    (e : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃*
      Multiplicative (ι → ℤ_[p])) :
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      n * Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) := by
  simpa only [Nat.mul_one] using
    card_fieldUnits_nthPowerQuotient_eq_mul_fieldKernel_of_logEquiv
      (F := F) hπ (A := ι → ℤ_[p]) (c := 1) e
        (by
          rw [card_padicInt_pi_nsmulQuotient_of_coprime
              (p := p) n,
            card_nsmulAddKernel_padicInt_pi (p := p) n])

/-- Equal-characteristic unit index from the literal principal-unit product,
with its torsion kernel written as the field root group `μ_n(K)`. -/
theorem card_units_nthPowerQuotient_of_equalPrincipalUnitProduct
    (F : CompleteDVF.{u, 0} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    {ι : Type u} {n : ℕ} [NeZero n] [Fact (Nat.Coprime n p)]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)]
    (e : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃*
      Multiplicative (ι → ℤ_[p])) :
    Nat.card (F.valuationSubringˣ ⧸
        (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) =
      Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) := by
  have hunit :
      Nat.card (F.valuationSubringˣ ⧸
          (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) =
        Nat.card
          ((powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).ker) := by
    simpa only [Nat.mul_one] using
      card_unit_nthPowerQuotient_eq_mul_unitKernel_of_logEquiv
        (F := F) (A := ι → ℤ_[p]) (c := 1) e
          (by
            rw [card_padicInt_pi_nsmulQuotient_of_coprime
                (p := p) n,
              card_nsmulAddKernel_padicInt_pi (p := p) n])
  rw [hunit]
  exact (card_fieldUnits_nthPowerKernel_eq_unit_nthPowerKernel
    (F := F) hπ n).symm

/-- Literal rational field formula in equal characteristic. -/
theorem card_fieldUnits_nthPowerQuotient_of_equalPrincipalUnitProduct_rationalFormula
    (F : CompleteDVF.{u, 0} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    {ι : Type u} {n : ℕ} [NeZero n] [Fact (Nat.Coprime n p)]
    [Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)]
    (e : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃*
      Multiplicative (ι → ℤ_[p])) :
    (Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) : ℚ) =
      (n * Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) : ℕ) /
        normalizedLocalNatAbs p 0 n := by
  rw [card_fieldUnits_nthPowerQuotient_of_equalPrincipalUnitProduct
    (p := p) (F := F) hπ e]
  simp [normalizedLocalNatAbs]

/-- Literal rational unit formula in equal characteristic. -/
theorem card_units_nthPowerQuotient_of_equalPrincipalUnitProduct_rationalFormula
    (F : CompleteDVF.{u, 0} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    {ι : Type u} {n : ℕ} [NeZero n] [Fact (Nat.Coprime n p)]
    [Finite
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ⧸
        (powMonoidHom n : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) →* ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)).range)]
    (e : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃*
      Multiplicative (ι → ℤ_[p])) :
    (Nat.card (F.valuationSubringˣ ⧸
        (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) : ℚ) =
      Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) /
        normalizedLocalNatAbs p 0 n := by
  rw [card_units_nthPowerQuotient_of_equalPrincipalUnitProduct
    (p := p) (F := F) hπ e]
  simp [normalizedLocalNatAbs]

end LocalFieldIndex

end LocalFieldTheory.DiscreteValuationField
