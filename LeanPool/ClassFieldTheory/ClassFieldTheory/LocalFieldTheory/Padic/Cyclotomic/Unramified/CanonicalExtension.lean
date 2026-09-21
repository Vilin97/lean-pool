/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Padic.Cyclotomic.Unramified.ArithmeticFrobenius
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Unramified.RamificationIndexTower
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Unramified.Definitions
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.FiniteNormExtension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.Core
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormula
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaAbsoluteValue
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaCoefficients
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaExtension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaIntegralClosure
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.RamificationInvariants
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.UniqueExtensionCoefficients
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.UniqueValuationSubring
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.ExponentialValuation
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Complete
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.LocalRingEquiv
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicField
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
/-!
# The canonical valuation on the unramified extension of `ℚ_p`

The unramified cyclotomic construction is proved for the additive exponential
valuation.  This file identifies that presentation, for
`ℚ_[p]`, with the concrete complete-DVF valuation used by the local class
field theory files.  It also specializes the least-exponent degree formula
to roots of unity of order `p ^ f - 1`.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

open scoped WithZero

/-- A prime is coprime to one less than a positive power of itself. -/
theorem prime_coprime_pow_sub_one (p f : ℕ) [hp : Fact p.Prime]
    (hf : 0 < f) :
    p.Coprime (p ^ f - 1) := by
  rw [hp.out.coprime_iff_not_dvd]
  intro hdiv
  have hpow : p ∣ p ^ f := dvd_pow_self p hf.ne'
  have hpf : 1 ≤ p ^ f := one_le_pow₀ hp.out.one_le
  have hdiff : p ^ f - (p ^ f - 1) = 1 := by omega
  have hone : p ∣ 1 := by
    rw [← hdiff]
    exact Nat.dvd_sub hpow hdiv
  exact hp.out.ne_one ((Nat.dvd_one.mp hone))

/-- For `m = p^f - 1`, the least positive exponent with `p^d = 1 mod m`
is exactly `f`.  This is the arithmetic specialization used in
the unramified branch of local cyclotomic reciprocity. -/
theorem padicCyclotomicUnramifiedResidueDegree_prime_pow_sub_one
    (p f : ℕ) [hp : Fact p.Prime] (hf : 0 < f) :
    padicCyclotomicUnramifiedResidueDegree (p ^ f - 1) p
        (prime_coprime_pow_sub_one p f hf) = f := by
  let m := p ^ f - 1
  let hcop : p.Coprime m := prime_coprime_pow_sub_one p f hf
  let d := padicCyclotomicUnramifiedResidueDegree m p hcop
  have hp1 : 1 < p := hp.out.one_lt
  have hpf1 : 1 ≤ p ^ f := one_le_pow₀ hp.out.one_le
  have hmodf : p ^ f ≡ 1 [MOD m] := by
    apply Nat.ModEq.symm
    apply (Nat.modEq_iff_dvd' hpf1).2
    exact dvd_rfl
  have hdf : d ≤ f :=
    padicCyclotomicUnramifiedResidueDegree_le_of_modEq_one m p hcop hf hmodf
  have hdpos : 0 < d := padicCyclotomicUnramifiedResidueDegree_pos m p hcop
  have hdmod : p ^ d ≡ 1 [MOD m] :=
    padicCyclotomicUnramifiedResidueDegree_modEq_one m p hcop
  have hpd1 : 1 ≤ p ^ d := one_le_pow₀ hp.out.one_le
  have hmdiv : m ∣ p ^ d - 1 :=
    (Nat.modEq_iff_dvd' hpd1).1 hdmod.symm
  have hfd : f ≤ d := by
    by_contra hnot
    have hdf' : d < f := Nat.lt_of_not_ge hnot
    have hpdgt : 1 < p ^ d := Nat.one_lt_pow hdpos.ne' hp1
    have hmle : m ≤ p ^ d - 1 := Nat.le_of_dvd (by omega) hmdiv
    have hpowlt : p ^ d < p ^ f := Nat.pow_lt_pow_right hp1 hdf'
    dsimp [m] at hmle
    omega
  exact le_antisymm hdf hfd

/-! ## The canonical exponential valuation on `ℚ_p` -/

/-- The norm absolute value on `ℚ_p` is nonarchimedean in the literal sense
used in the unramified-extension construction. -/
theorem padicFieldAbsoluteValue_nonarchimedean
    (p : ℕ) [Fact p.Prime] :
    LubinTate.Valuations.NonarchimedeanAbsoluteValue
      (NormedField.toAbsoluteValue ℚ_[p]) := by
  apply LubinTate.Valuations.nonarchimedean_of_strong_triangle
  intro x y
  exact Padic.nonarchimedean x y

/-- The norm absolute value on `ℚ_p` is complete. -/
theorem padicFieldAbsoluteValue_complete
    (p : ℕ) [Fact p.Prime] :
    IsCompleteForAbsoluteValue (NormedField.toAbsoluteValue ℚ_[p]) := by
  rw [IsCompleteForAbsoluteValue]
  have huniform :
      (NormedField.toAbsoluteValue ℚ_[p]).uniformSpace =
        (inferInstance : UniformSpace ℚ_[p]) := by
    ext s
    rw [(AbsoluteValue.hasBasis_uniformity
      (NormedField.toAbsoluteValue ℚ_[p])).mem_iff,
      Metric.uniformity_basis_dist.mem_iff]
    have hdist : ∀ q : ℚ_[p] × ℚ_[p],
        dist q.1 q.2 =
          (NormedField.toAbsoluteValue ℚ_[p]) (q.1 - q.2) := by
      intro q
      rw [dist_eq_norm]
      rfl
    simp [hdist, AbsoluteValue.map_sub]
  rw [huniform]
  exact @Padic.instCompleteSpace p (inferInstance : Fact p.Prime)

/-- The norm absolute value on `ℚ_p` is nontrivial. -/
theorem padicFieldAbsoluteValue_isNontrivial
    (p : ℕ) [Fact p.Prime] :
    (NormedField.toAbsoluteValue ℚ_[p]).IsNontrivial := by
  refine ⟨(p : ℚ_[p]), ?_, ?_⟩
  · exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  · apply ne_of_lt
    exact Padic.norm_p_lt_one

/-- The canonical additive exponential valuation on `ℚ_p`, obtained from
the standard norm by the conversion `v(x) = -log |x|`. -/
noncomputable def padicFieldExponentialValuation
    (p : ℕ) [Fact p.Prime] :
    LubinTate.Valuations.ExponentialValuation ℚ_[p] :=
  absoluteValueExponentialValuation
    (NormedField.toAbsoluteValue ℚ_[p])
    (padicFieldAbsoluteValue_nonarchimedean p)

/-- The valuation ring of the preceding exponential valuation is literally the
valuation ring of the concrete complete-DVF package on `ℚ_p`. -/
theorem padicFieldExponentialValuationSubring_eq_completeDVF
    (p : ℕ) [Fact p.Prime] :
    LubinTate.Valuations.exponentialValuationSubringAsValuationSubring
        (padicFieldExponentialValuation p) =
      (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).valuation.valuationSubring := by
  let a : AbsoluteValue ℚ_[p] ℝ := NormedField.toAbsoluteValue ℚ_[p]
  let hn : LubinTate.Valuations.NonarchimedeanAbsoluteValue a :=
    padicFieldAbsoluteValue_nonarchimedean p
  let v : LubinTate.Valuations.ExponentialValuation ℚ_[p] :=
    padicFieldExponentialValuation p
  have hva :
      LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v =
        absoluteValueValuationSubring a hn := by
    exact associatedAbsoluteValue_valuationSubring_eq
      v (Real.exp 1) a hn
        (absoluteValueExponentialValuation_associated a hn)
  rw [hva]
  ext x
  rw [mem_absoluteValueValuationSubring_iff]
  change ‖x‖ ≤ 1 ↔
    x ∈ (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation p).valuationSubring
  let e : ℤ_[p] ≃+*
      (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation p).valuationSubring :=
    LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicIntEquivValuationSubring p
  constructor
  · intro hx
    let z : ℤ_[p] := ⟨x, hx⟩
    have he : ((e z :
        (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation p).valuationSubring) :
          ℚ_[p]) = x := rfl
    rw [← he]
    exact (e z).property
  · intro hx
    let y : (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation p).valuationSubring :=
      ⟨x, hx⟩
    let z : ℤ_[p] := e.symm y
    have hez : e z = y := e.apply_symm_apply y
    have hcoe : (z : ℚ_[p]) = x := by
      calc
        (z : ℚ_[p]) = ((e z :
            (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation p).valuationSubring) :
              ℚ_[p]) := rfl
        _ = (y : ℚ_[p]) := congrArg
          (fun w : (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation p).valuationSubring =>
            (w : ℚ_[p])) hez
        _ = x := rfl
    have hz := PadicInt.norm_le_one z
    change ‖(z : ℚ_[p])‖ ≤ 1 at hz
    rw [hcoe] at hz
    exact hz

/-- The concrete complete `ℚ_p` valuation is Henselian, expressed through
the exponential valuation required by the unramified cyclotomic construction. -/
theorem padicCyclotomicUnramified_padicExponentialValuation_henselian
    (p : ℕ) [Fact p.Prime] :
    ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring
        (padicFieldExponentialValuation p)).valuation := by
  let a : AbsoluteValue ℚ_[p] ℝ := NormedField.toAbsoluteValue ℚ_[p]
  let hn : LubinTate.Valuations.NonarchimedeanAbsoluteValue a :=
    padicFieldAbsoluteValue_nonarchimedean p
  have hva :
      LubinTate.Valuations.exponentialValuationSubringAsValuationSubring
          (padicFieldExponentialValuation p) =
        absoluteValueValuationSubring a hn := by
    exact associatedAbsoluteValue_valuationSubring_eq
      (padicFieldExponentialValuation p)
      (Real.exp 1) a hn
      (absoluteValueExponentialValuation_associated a hn)
  rw [hva]
  intro f gbar hbar hne hfac hcop
  exact henselianValuation_of_complete a
    (padicFieldAbsoluteValue_complete p) hn hne hfac hcop

/-! ## Residue field and the `p ^ f - 1` cyclotomic degree -/

/-- The residue field of the exponential valuation on `ℚ_p` is canonically `ZMod p`.
The construction passes through the same valuation-subring equivalence used
by the concrete complete-DVF package. -/
noncomputable def padicCyclotomicUnramified_padicExponentialResidueFieldEquivZMod
    (p : ℕ) [Fact p.Prime] :
    padicCyclotomicUnramifiedResidueField
        (padicFieldExponentialValuation p) ≃+* ZMod p := by
  let v := padicFieldExponentialValuation p
  let C := (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).valuation
  have hV : LubinTate.Valuations.exponentialValuationSubring v = C.valuationSubring.toSubring := by
    exact congrArg ValuationSubring.toSubring
      (padicFieldExponentialValuationSubring_eq_completeDVF p)
  let eVC : LubinTate.Valuations.exponentialValuationSubring v ≃+* C.valuationSubring :=
    { toFun := fun x => ⟨x, by
          change (x : ℚ_[p]) ∈ C.valuationSubring.toSubring
          rw [← hV]
          exact x.property⟩
      invFun := fun x => ⟨x, by
          rw [hV]
          exact x.property⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  change IsLocalRing.ResidueField (LubinTate.Valuations.exponentialValuationSubring v) ≃+* ZMod p
  exact ((IsLocalRing.ResidueField.mapEquiv eVC).trans
    (IsLocalRing.ResidueField.mapEquiv
      (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicIntEquivValuationSubring p)).symm).trans
        (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicIntResidueFieldEquivZMod p)

/-- The residue field used by the unramified cyclotomic theorem has cardinality `p`. -/
theorem padicCyclotomicUnramified_padicExponentialResidueField_card
    (p : ℕ) [Fact p.Prime]
    [Fintype (padicCyclotomicUnramifiedResidueField
      (padicFieldExponentialValuation p))] :
    Fintype.card (padicCyclotomicUnramifiedResidueField
      (padicFieldExponentialValuation p)) = p := by
  calc
    Fintype.card (padicCyclotomicUnramifiedResidueField
        (padicFieldExponentialValuation p)) =
        Fintype.card (ZMod p) :=
      Fintype.card_congr
        (padicCyclotomicUnramified_padicExponentialResidueFieldEquivZMod p).toEquiv
    _ = p := ZMod.card p

/-- the unramified cyclotomic theorem on the canonical `ℚ_p` valuation, specialized to
the unramified cyclotomic level of order `p ^ f - 1`: a field generated by a
primitive root of that exact order has degree `f`. -/
theorem padicCyclotomic_finrank_prime_pow_sub_one
    (p f : ℕ) [hp : Fact p.Prime] (hf : 0 < f)
    {L : Type*} [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ f - 1))
    (hζgen : Algebra.adjoin ℚ_[p] ({ζ} : Set L) = ⊤) :
    Module.finrank ℚ_[p] L = f := by
  let v := padicFieldExponentialValuation p
  let e := padicCyclotomicUnramified_padicExponentialResidueFieldEquivZMod p
  let : Finite (padicCyclotomicUnramifiedResidueField v) :=
    Finite.of_equiv (ZMod p) e.symm.toEquiv
  let : Fintype (padicCyclotomicUnramifiedResidueField v) := Fintype.ofFinite _
  have hk : Fintype.card (padicCyclotomicUnramifiedResidueField v) = p ^ 1 := by
    simpa [v] using padicCyclotomicUnramified_padicExponentialResidueField_card p
  let hcop : p.Coprime (p ^ f - 1) := prime_coprime_pow_sub_one p f hf
  calc
    Module.finrank ℚ_[p] L =
        padicCyclotomicUnramifiedResidueDegree (p ^ f - 1) (p ^ 1)
          (hcop.pow_left 1) :=
      padicCyclotomicUnramified_finrank_eq_residueDegree v
        (padicCyclotomicUnramified_padicExponentialValuation_henselian p)
        hk hcop hζ hζgen
    _ = f := by
      simpa using padicCyclotomicUnramifiedResidueDegree_prime_pow_sub_one p f hf

/-! ## The actual finite-extension valuation and unramified conclusion -/

/-- The unique nonarchimedean absolute value on a finite extension of `ℚ_p`,
constructed by the norm formula in the norm-formula theorem. -/
noncomputable def padicFiniteExtensionAbsoluteValue
    (p : ℕ) [Fact p.Prime]
    (L : Type*) [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L] :
    AbsoluteValue L ℝ := by
  let a : AbsoluteValue ℚ_[p] ℝ := NormedField.toAbsoluteValue ℚ_[p]
  let hn : LubinTate.Valuations.NonarchimedeanAbsoluteValue a :=
    padicFieldAbsoluteValue_nonarchimedean p
  let hh : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (absoluteValueValuationSubring a hn).valuation := by
    intro f gbar hbar hne hfac hcop
    exact henselianValuation_of_complete a
      (padicFieldAbsoluteValue_complete p) hn hne hfac hcop
  let hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring a hn) :=
    (henselianValuation_iff_henselFactorization a hn).1 hh
  exact normFormula_finite_normFormulaAbsoluteValue_of_henselFactorization
    (K := ℚ_[p]) (L := L) a hn hv

/-- The norm-formula absolute value is nonarchimedean. -/
theorem padicFiniteExtensionAbsoluteValue_nonarchimedean
    (p : ℕ) [Fact p.Prime]
    (L : Type*) [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L] :
    LubinTate.Valuations.NonarchimedeanAbsoluteValue
      (padicFiniteExtensionAbsoluteValue p L) := by
  let a : AbsoluteValue ℚ_[p] ℝ := NormedField.toAbsoluteValue ℚ_[p]
  let hn : LubinTate.Valuations.NonarchimedeanAbsoluteValue a :=
    padicFieldAbsoluteValue_nonarchimedean p
  let hh : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (absoluteValueValuationSubring a hn).valuation := by
    intro f gbar hbar hne hfac hcop
    exact henselianValuation_of_complete a
      (padicFieldAbsoluteValue_complete p) hn hne hfac hcop
  simpa [padicFiniteExtensionAbsoluteValue, a, hn, hh] using
    (normFormula_finite_extension_norm_formula
      (K := ℚ_[p]) (L := L) a hn hh).1

/-- The norm-formula absolute value extends the standard `ℚ_p` absolute
value exactly. -/
theorem padicFiniteExtensionAbsoluteValue_extends
    (p : ℕ) [Fact p.Prime]
    (L : Type*) [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    (x : ℚ_[p]) :
    padicFiniteExtensionAbsoluteValue p L
        (algebraMap ℚ_[p] L x) =
      NormedField.toAbsoluteValue ℚ_[p] x := by
  let a : AbsoluteValue ℚ_[p] ℝ := NormedField.toAbsoluteValue ℚ_[p]
  let hn : LubinTate.Valuations.NonarchimedeanAbsoluteValue a :=
    padicFieldAbsoluteValue_nonarchimedean p
  let hh : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (absoluteValueValuationSubring a hn).valuation := by
    intro f gbar hbar hne hfac hcop
    exact henselianValuation_of_complete a
      (padicFieldAbsoluteValue_complete p) hn hne hfac hcop
  simpa [padicFiniteExtensionAbsoluteValue, a, hn, hh] using
    (normFormula_finite_extension_norm_formula
      (K := ℚ_[p]) (L := L) a hn hh).2.1 x

/-- The canonical norm-formula absolute value on every finite extension of
`ℚ_p` is complete. -/
theorem padicFiniteExtensionAbsoluteValue_complete
    (p : ℕ) [Fact p.Prime]
    (L : Type*) [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L] :
    IsCompleteForAbsoluteValue
      (padicFiniteExtensionAbsoluteValue p L) := by
  let v : AbsoluteValue ℚ_[p] ℝ := NormedField.toAbsoluteValue ℚ_[p]
  let R := finiteNormExtension_nonarchimedean_finite_extension
    (K := ℚ_[p]) (L := L) v
      (padicFieldAbsoluteValue_complete p)
      (padicFieldAbsoluteValue_nonarchimedean p)
      (padicFieldAbsoluteValue_isNontrivial p)
  have hEq :
      padicFiniteExtensionAbsoluteValue p L = R.extension :=
    R.unique _ (padicFiniteExtensionAbsoluteValue_extends p L)
  rw [hEq]
  exact R.complete_extension

/-- The canonical norm-formula absolute values on finite extensions of
`ℚ_p` are functorial for `ℚ_p`-algebra embeddings.  This is the valued-field
tower bridge used in the global Kronecker--Weber argument: no compatibility
hypothesis has to be carried by the embedding. -/
theorem padicCyclotomicUnramified_padicFiniteExtensionAbsoluteValue_comp_algHom
    (p : ℕ) [Fact p.Prime]
    {E D : Type*} [Field E] [Field D]
    [Algebra ℚ_[p] E] [Algebra ℚ_[p] D]
    [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] D]
    (i : E →ₐ[ℚ_[p]] D) :
    (padicFiniteExtensionAbsoluteValue p D).comp
        (f := i.toRingHom) i.injective =
      padicFiniteExtensionAbsoluteValue p E := by
  let v : AbsoluteValue ℚ_[p] ℝ := NormedField.toAbsoluteValue ℚ_[p]
  let w : AbsoluteValue E ℝ :=
    (padicFiniteExtensionAbsoluteValue p D).comp
      (f := i.toRingHom) i.injective
  let : Algebra.IsAlgebraic ℚ_[p] E :=
    Algebra.IsAlgebraic.of_finite ℚ_[p] E
  have hwExt : ∀ x : ℚ_[p], w (algebraMap ℚ_[p] E x) = v x := by
    intro x
    change padicFiniteExtensionAbsoluteValue p D
        (i (algebraMap ℚ_[p] E x)) =
      NormedField.toAbsoluteValue ℚ_[p] x
    rw [i.commutes]
    exact padicFiniteExtensionAbsoluteValue_extends p D x
  have hvComplete : CompleteSpace (WithAbs v) :=
    completeSpace_withAbs_of_isCompleteForAbsoluteValue v
      (padicFieldAbsoluteValue_complete p)
  have hvNonarch : IsNonarchimedean (v : ℚ_[p] → ℝ) :=
    (LubinTate.Valuations.strong_triangle_iff_isNonarchimedean v).1
      (LubinTate.Valuations.strong_triangle_of_nonarchimedean v
        (padicFieldAbsoluteValue_nonarchimedean p))
  have hw := AbsoluteValue.eq_spectralExtension_of_extends
    v hvComplete hvNonarch
      (padicFieldAbsoluteValue_isNontrivial p) w hwExt
  have hE := AbsoluteValue.eq_spectralExtension_of_extends
    v hvComplete hvNonarch
      (padicFieldAbsoluteValue_isNontrivial p)
      (padicFiniteExtensionAbsoluteValue p E)
      (padicFiniteExtensionAbsoluteValue_extends p E)
  exact hw.trans hE.symm

/-- Pointwise form of
`padicCyclotomicUnramified_padicFiniteExtensionAbsoluteValue_comp_algHom`. -/
theorem padicFiniteExtensionAbsoluteValue_algHom
    (p : ℕ) [Fact p.Prime]
    {E D : Type*} [Field E] [Field D]
    [Algebra ℚ_[p] E] [Algebra ℚ_[p] D]
    [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] D]
    (i : E →ₐ[ℚ_[p]] D) (x : E) :
    padicFiniteExtensionAbsoluteValue p D (i x) =
      padicFiniteExtensionAbsoluteValue p E x := by
  exact congrArg (fun a : AbsoluteValue E ℝ => a x)
    (padicCyclotomicUnramified_padicFiniteExtensionAbsoluteValue_comp_algHom p i)

/-- Pulling the canonical valuation ring of a finite `ℚ_p`-extension back
along a `ℚ_p`-algebra embedding gives the canonical valuation ring of the
source.  This is the valuation-subring form of the preceding functoriality
theorem, suitable for inertia maps. -/
theorem padicCyclotomicUnramified_padicFiniteExtensionValuationSubring_comap_algHom
    (p : ℕ) [Fact p.Prime]
    {E D : Type*} [Field E] [Field D]
    [Algebra ℚ_[p] E] [Algebra ℚ_[p] D]
    [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] D]
    (i : E →ₐ[ℚ_[p]] D) :
    (absoluteValueUnitBallSubring
        (padicFiniteExtensionAbsoluteValue p D)
        (padicFiniteExtensionAbsoluteValue_nonarchimedean p D)).comap
          i.toRingHom =
      absoluteValueUnitBallSubring
        (padicFiniteExtensionAbsoluteValue p E)
        (padicFiniteExtensionAbsoluteValue_nonarchimedean p E) := by
  let iAlg : Algebra E D := i.toRingHom.toAlgebra
  let : Algebra E D := iAlg
  have hExt : ∀ x : E,
      padicFiniteExtensionAbsoluteValue p D
          (algebraMap E D x) =
        padicFiniteExtensionAbsoluteValue p E x := by
    intro x
    change padicFiniteExtensionAbsoluteValue p D (i x) =
      padicFiniteExtensionAbsoluteValue p E x
    exact padicFiniteExtensionAbsoluteValue_algHom p i x
  exact comap_absoluteValueUnitBallSubring_eq_of_extends
    (padicFiniteExtensionAbsoluteValue p E)
    (padicFiniteExtensionAbsoluteValue p D)
    (padicFiniteExtensionAbsoluteValue_nonarchimedean p E)
    (padicFiniteExtensionAbsoluteValue_nonarchimedean p D)
    hExt

/-- The preceding absolute value in the additive exponential presentation
used by the unramified cyclotomic theorem. -/
noncomputable def padicFiniteExtensionExponentialValuation
    (p : ℕ) [Fact p.Prime]
    (L : Type*) [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L] :
    LubinTate.Valuations.ExponentialValuation L :=
  absoluteValueExponentialValuation
    (padicFiniteExtensionAbsoluteValue p L)
    (padicFiniteExtensionAbsoluteValue_nonarchimedean p L)

/-- The finite-extension exponential valuation restricts exactly to the canonical
exponential valuation of `ℚ_p`. -/
theorem padicFiniteExtensionExponentialValuation_extends
    (p : ℕ) [Fact p.Prime]
    (L : Type*) [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    (x : ℚ_[p]) :
    padicFiniteExtensionExponentialValuation p L
        (algebraMap ℚ_[p] L x) =
      padicFieldExponentialValuation p x := by
  exact absoluteValueExponentialValuation_extends
    (NormedField.toAbsoluteValue ℚ_[p])
    (padicFiniteExtensionAbsoluteValue p L)
    (padicFieldAbsoluteValue_nonarchimedean p)
    (padicFiniteExtensionAbsoluteValue_nonarchimedean p L)
    (padicFiniteExtensionAbsoluteValue_extends p L) x

/-- The canonical exponential valuations on finite extensions of `ℚ_p` are
functorial under `ℚ_p`-algebra embeddings. -/
theorem padicFiniteExtensionExponentialValuation_algHom
    (p : ℕ) [Fact p.Prime]
    {E D : Type} [Field E] [Field D]
    [Algebra ℚ_[p] E] [Algebra ℚ_[p] D]
    [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] D]
    (i : E →ₐ[ℚ_[p]] D) (x : E) :
    padicFiniteExtensionExponentialValuation p D (i x) =
      padicFiniteExtensionExponentialValuation p E x := by
  by_cases hx : x = 0
  · subst x
    simp [padicFiniteExtensionExponentialValuation,
      absoluteValueExponentialValuation]
  · have hix : i x ≠ 0 := by simpa using i.injective.ne hx
    simp [padicFiniteExtensionExponentialValuation,
      absoluteValueExponentialValuation, hx, hix,
      padicFiniteExtensionAbsoluteValue_algHom p i]

/-- Ramification index is monotone under an embedding of finite extensions
of `ℚ_p`.  The larger field's canonical valuation pulls back exactly to the
smaller field's canonical valuation, and multiplicativity in the resulting
valued-field tower gives the inequality. -/
theorem padicFiniteExtension_exponentialRamificationIndex_le_of_algHom
    (p : ℕ) [Fact p.Prime]
    {E D : Type} [Field E] [Field D]
    [Algebra ℚ_[p] E] [Algebra ℚ_[p] D]
    [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] D]
    (i : E →ₐ[ℚ_[p]] D) :
    exponentialRamificationIndex
        (padicFieldExponentialValuation p)
        (padicFiniteExtensionExponentialValuation p E) ≤
      exponentialRamificationIndex
        (padicFieldExponentialValuation p)
        (padicFiniteExtensionExponentialValuation p D) := by
  apply exponentialRamificationIndex_le_of_algHom i
  · exact padicFiniteExtensionExponentialValuation_extends p E
  · intro x
    exact padicFiniteExtensionExponentialValuation_algHom p i x

/-- The valuation ring selected by the norm-formula extension is the actual
integral closure of the standard complete-DVF valuation ring of `ℚ_p`.
This is the ring-level uniqueness bridge between the exponential valuation and the
canonical finite-extension construction. -/
theorem padicCyclotomicUnramified_padicFiniteExtensionValuationSubring_eq_integralClosure
    (p : ℕ) [Fact p.Prime]
    (L : Type*) [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L] :
    (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring
        (padicFiniteExtensionExponentialValuation p L)).toSubring =
      (integralClosure
        (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).valuationSubring
        L).toSubring := by
  let : Algebra.IsAlgebraic ℚ_[p] L := Algebra.IsAlgebraic.of_finite ℚ_[p] L
  have hclosure :=
    exponentialValuationSubring_eq_integralClosure_of_henselian
      (padicFieldExponentialValuation p)
      (padicFiniteExtensionExponentialValuation p L)
      (padicFiniteExtensionExponentialValuation_extends p L)
      (padicCyclotomicUnramified_padicExponentialValuation_henselian p)
  rw [padicFieldExponentialValuationSubring_eq_completeDVF p] at hclosure
  exact hclosure

/-- An integral-closure valuation ring is equal, as a subring of the field,
to the usual `integralClosure` subring. -/
private theorem padicCyclotomicUnramified_valuationSubring_eq_integralClosure
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    [IsIntegralClosure W V L] :
    W.toSubring = (integralClosure V L).toSubring := by
  ext x
  constructor
  · intro hx
    exact (IsIntegralClosure.isIntegral_iff (A := W)).2 ⟨⟨x, hx⟩, rfl⟩
  · intro hx
    obtain ⟨y, hy⟩ :=
      (IsIntegralClosure.isIntegral_iff (A := W)).1 hx
    rw [← hy]
    exact y.property

/-- Identity-on-elements equivalence between the exponential valuation ring of
`ℚ_p` and the standard complete-DVF valuation ring. -/
noncomputable def padicCyclotomicUnramified_padicExponentialValuationSubringEquivCompleteDVF
    (p : ℕ) [Fact p.Prime] :
    LubinTate.Valuations.exponentialValuationSubring
        (padicFieldExponentialValuation p) ≃+*
      (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).valuationSubring := by
  let V := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring
    (padicFieldExponentialValuation p)
  let C : ValuationSubring ℚ_[p] :=
    (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).valuation.valuationSubring
  have hVC : V = C :=
    padicFieldExponentialValuationSubring_eq_completeDVF p
  exact
    { toFun := fun x => ⟨x, by
          change (x : ℚ_[p]) ∈ C
          rw [← hVC]
          exact x.property⟩
      invFun := fun x => ⟨x, by
          change (x : ℚ_[p]) ∈ V
          rw [hVC]
          exact x.property⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }

/-- If a complete-DVF target is the actual integral closure, its valuation
ring is identity-equivalent to the norm-formula valuation ring. -/
noncomputable def padicCyclotomicUnramified_padicFiniteExtensionValuationSubringEquiv
    (p : ℕ) [Fact p.Prime]
    (L : Type*) [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    (target : ValuationTheory.DiscreteValuationField.CompleteDVF L)
    [IsIntegralClosure target.valuationSubring
      (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).valuationSubring L] :
    LubinTate.Valuations.exponentialValuationSubring
        (padicFiniteExtensionExponentialValuation p L) ≃+*
      target.valuationSubring := by
  let W := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring
    (padicFiniteExtensionExponentialValuation p L)
  let T : ValuationSubring L := target.valuation.valuationSubring
  have hW : W.toSubring =
      (integralClosure
        (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).valuationSubring
        L).toSubring :=
    padicCyclotomicUnramified_padicFiniteExtensionValuationSubring_eq_integralClosure p L
  have hT : T.toSubring =
      (integralClosure
        (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).valuationSubring
        L).toSubring :=
    by
      let : IsIntegralClosure T
          (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).valuation.valuationSubring L := by
        change IsIntegralClosure target.valuationSubring
          (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).valuationSubring L
        infer_instance
      exact padicCyclotomicUnramified_valuationSubring_eq_integralClosure
        (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).valuation.valuationSubring T
  exact
    { toFun := fun x => ⟨x, by
          change (x : L) ∈ T.toSubring
          rw [hT, ← hW]
          exact x.property⟩
      invFun := fun x => ⟨x, by
          change (x : L) ∈ W.toSubring
          rw [hW, ← hT]
          exact x.property⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }

/-- The norm-formula valuation ring on a finite extension of `ℚ_p` is the
valuation ring of any complete-DVF model given by the integral closure. -/
theorem padicFiniteExtensionExponentialValuationSubring_eq_completeDVF
    (p : ℕ) [Fact p.Prime]
    (L : Type*) [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    (target : ValuationTheory.DiscreteValuationField.CompleteDVF L)
    [IsIntegralClosure target.valuationSubring
      (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).valuationSubring L] :
    LubinTate.Valuations.exponentialValuationSubringAsValuationSubring
        (padicFiniteExtensionExponentialValuation p L) =
      target.valuation.valuationSubring := by
  let e :=
    padicCyclotomicUnramified_padicFiniteExtensionValuationSubringEquiv p L target
  ext y
  constructor
  · intro hy
    exact (e ⟨y, hy⟩).property
  · intro hy
    exact (e.symm ⟨y, hy⟩).property

/-- the unramified cyclotomic theorem(i), specialized to the actual `ℚ_p` valuation:
adjoining roots of unity of any order prime to `p` is unramified in the
degree/residue-degree sense. -/
theorem padicCyclotomic_finiteUnramified_of_coprime
    (p r : ℕ) [hp : Fact p.Prime] (hpr : p.Coprime r)
    {L : Type*} [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ r)
    (hζgen : Algebra.adjoin ℚ_[p] ({ζ} : Set L) = ⊤) :
    FiniteUnramifiedExtension
      (padicFieldExponentialValuation p)
      (padicFiniteExtensionExponentialValuation p L)
      (padicFiniteExtensionExponentialValuation_extends p L) := by
  let v := padicFieldExponentialValuation p
  let e := padicCyclotomicUnramified_padicExponentialResidueFieldEquivZMod p
  let : Finite (padicCyclotomicUnramifiedResidueField v) :=
    Finite.of_equiv (ZMod p) e.symm.toEquiv
  let : Fintype (padicCyclotomicUnramifiedResidueField v) := Fintype.ofFinite _
  have hk : Fintype.card (padicCyclotomicUnramifiedResidueField v) = p ^ 1 := by
    simpa [v] using padicCyclotomicUnramified_padicExponentialResidueField_card p
  exact padicCyclotomicUnramified_finiteUnramifiedExtension
    v (padicFiniteExtensionExponentialValuation p L)
    (padicFiniteExtensionExponentialValuation_extends p L)
    (padicCyclotomicUnramified_padicExponentialValuation_henselian p)
    hk hpr hζ hζgen

/-- The `p ^ f - 1` form of
`padicCyclotomic_finiteUnramified_of_coprime`. -/
theorem padicCyclotomicUnramified_padic_finiteUnramified_prime_pow_sub_one
    (p f : ℕ) [hp : Fact p.Prime] (hf : 0 < f)
    {L : Type*} [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ f - 1))
    (hζgen : Algebra.adjoin ℚ_[p] ({ζ} : Set L) = ⊤) :
    FiniteUnramifiedExtension
      (padicFieldExponentialValuation p)
      (padicFiniteExtensionExponentialValuation p L)
      (padicFiniteExtensionExponentialValuation_extends p L) := by
  exact padicCyclotomic_finiteUnramified_of_coprime
    p (p ^ f - 1) (prime_coprime_pow_sub_one p f hf) hζ hζgen

/-- The canonical ramification index of the integral-closure
complete-DVF extension is one.  This is the valuation-ring form of the
unramified conclusion, independent of the chosen valuation presentation. -/
theorem padicCyclotomic_ramificationIndex_eq_one_prime_pow_sub_one
    (p f : ℕ) [hp : Fact p.Prime] (hf : 0 < f)
    {L : Type*} [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ f - 1))
    (hζgen : Algebra.adjoin ℚ_[p] ({ζ} : Set L) = ⊤)
    (target : ValuationTheory.DiscreteValuationField.CompleteDVF L)
    [hExt :
      (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).valuation.HasExtension
        target.valuation]
    [IsIntegralClosure target.valuationSubring
      (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).valuationSubring L] :
    ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
      (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).toDVF
      target.toDVF = 1 := by
  let base := LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p
  let v := padicFieldExponentialValuation p
  let w := padicFiniteExtensionExponentialValuation p L
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let iExponential := exponentialValuationRingMap v w
    (padicFiniteExtensionExponentialValuation_extends p L)
  let iCanonical : base.valuationSubring →+* target.valuationSubring :=
    algebraMap base.valuationSubring target.valuationSubring
  let eBase : V ≃+* base.valuationSubring :=
    padicCyclotomicUnramified_padicExponentialValuationSubringEquivCompleteDVF p
  let eTarget : W ≃+* target.valuationSubring :=
    padicCyclotomicUnramified_padicFiniteExtensionValuationSubringEquiv p L target
  let : IsDiscreteValuationRing base.valuationSubring :=
    base.valuationSubring_isDiscreteValuationRing
  let : IsDiscreteValuationRing target.valuationSubring :=
    target.valuationSubring_isDiscreteValuationRing
  let : IsDiscreteValuationRing V :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eBase.symm
  let : IsDiscreteValuationRing W :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eTarget.symm
  let : IsLocalHom iExponential :=
    exponentialValuationRingMap_isLocalHom v w
      (padicFiniteExtensionExponentialValuation_extends p L)
  let : Algebra V W := iExponential.toAlgebra
  have hvdisc : LubinTate.Valuations.DiscreteExponentialValuation v :=
    discreteExponentialValuation_of_isDiscreteValuationRing v
  have hUnramified : FiniteUnramifiedExtension v w
      (padicFiniteExtensionExponentialValuation_extends p L) := by
    simpa [v, w] using
      padicCyclotomicUnramified_padic_finiteUnramified_prime_pow_sub_one
        p f hf hζ hζgen
  have hRamification : exponentialRamificationIndex v w = 1 :=
    exponentialRamificationIndex_eq_one_of_finiteUnramifiedExtension
      v w (padicFiniteExtensionExponentialValuation_extends p L)
      hUnramified
  have hidealExponential :
      Ideal.ramificationIdx'
        (IsLocalRing.maximalIdeal V) (IsLocalRing.maximalIdeal W) = 1 := by
    have hcompare := exponentialRamificationIndex_eq_ideal_ramificationIdx
      v w (padicFiniteExtensionExponentialValuation_extends p L) hvdisc
    change exponentialRamificationIndex v w =
      Ideal.ramificationIdx'
        (IsLocalRing.maximalIdeal V) (IsLocalRing.maximalIdeal W) at hcompare
    rw [← hcompare]
    exact hRamification
  have hiExponential : Function.Injective iExponential := by
    intro x y hxy
    apply Subtype.ext
    exact (algebraMap ℚ_[p] L).injective (congrArg Subtype.val hxy)
  have hmapExponential :
      Ideal.map iExponential (IsLocalRing.maximalIdeal V) =
        IsLocalRing.maximalIdeal W := by
    have hmap :=
      ValuationTheory.map_maximalIdeal_eq_pow_ramificationIdx hiExponential
    rw [hidealExponential, pow_one] at hmap
    exact hmap
  have hmapBase :
      Ideal.map eBase (IsLocalRing.maximalIdeal V) =
        IsLocalRing.maximalIdeal base.valuationSubring :=
    ValuationTheory.ringEquiv_map_maximalIdeal eBase
  have hmapTarget :
      Ideal.map eTarget (IsLocalRing.maximalIdeal W) =
        IsLocalRing.maximalIdeal target.valuationSubring :=
    ValuationTheory.ringEquiv_map_maximalIdeal eTarget
  have hcommute :
      eTarget.toRingHom.comp iExponential = iCanonical.comp eBase.toRingHom := by
    ext x
    rfl
  have hmapCanonical :
      Ideal.map iCanonical (IsLocalRing.maximalIdeal base.valuationSubring) =
        IsLocalRing.maximalIdeal target.valuationSubring := by
    calc
      Ideal.map iCanonical (IsLocalRing.maximalIdeal base.valuationSubring) =
          Ideal.map iCanonical
            (Ideal.map eBase (IsLocalRing.maximalIdeal V)) := by rw [hmapBase]
      _ = Ideal.map (iCanonical.comp eBase.toRingHom)
          (IsLocalRing.maximalIdeal V) :=
        Ideal.map_map eBase.toRingHom iCanonical
      _ = Ideal.map (eTarget.toRingHom.comp iExponential)
          (IsLocalRing.maximalIdeal V) := by rw [hcommute]
      _ = Ideal.map eTarget
          (Ideal.map iExponential (IsLocalRing.maximalIdeal V)) :=
        (Ideal.map_map iExponential eTarget.toRingHom).symm
      _ = Ideal.map eTarget (IsLocalRing.maximalIdeal W) := by rw [hmapExponential]
      _ = IsLocalRing.maximalIdeal target.valuationSubring := hmapTarget
  have hmapCanonicalAlg :
      Ideal.map
          (algebraMap base.valuationSubring target.valuationSubring)
          (IsLocalRing.maximalIdeal base.valuationSubring) =
        IsLocalRing.maximalIdeal target.valuationSubring := by
    simpa only [iCanonical] using hmapCanonical
  change Ideal.ramificationIdx'
    (IsLocalRing.maximalIdeal base.valuationSubring)
    (IsLocalRing.maximalIdeal target.valuationSubring) = 1
  apply Ideal.ramificationIdx'_spec
  · rw [hmapCanonicalAlg, pow_one]
  · rw [hmapCanonicalAlg]
    simpa using not_le_of_gt (Ideal.pow_succ_lt_pow
      (IsDiscreteValuationRing.not_a_field target.valuationSubring) 1)

/-- Complete-DVF form of the unramified cyclotomic theorem(i): the canonical
integral-closure extension is finite unramified. -/
theorem padicCyclotomicUnramified_padic_isFiniteUnramified_prime_pow_sub_one
    (p f : ℕ) [hp : Fact p.Prime] (hf : 0 < f)
    {L : Type*} [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ f - 1))
    (hζgen : Algebra.adjoin ℚ_[p] ({ζ} : Set L) = ⊤)
    (target : ValuationTheory.DiscreteValuationField.CompleteDVF L)
    [hExt :
      (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).valuation.HasExtension
        target.valuation]
    [IsIntegralClosure target.valuationSubring
      (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).valuationSubring L] :
    ValuationTheory.DiscreteValuationField.ValuedExtension.IsFiniteUnramified
      (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).toDVF
      target.toDVF := by
  let base := LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p
  let : Algebra.IsSeparable ℚ_[p] L := by infer_instance
  let : IsScalarTower base.valuationSubring target.valuationSubring L := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  let : Module.Finite base.valuationSubring target.valuationSubring :=
    ValuationTheory.DiscreteValuationField.ValuedExtension.moduleFinite_target_valuationSubring_of_finite_separable
      base target
  let : FiniteDimensional base.residueField target.residueField :=
    ValuationTheory.DiscreteValuationField.ValuedExtension.residueField_finiteDimensional_of_moduleFinite
      base target
  let : Finite base.residueField := by
    simpa [base] using
      LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF_residueField_finite p
  let : PerfectField base.residueField := by infer_instance
  have hresidueSeparable :
      Algebra.IsSeparable base.residueField target.residueField := by
    infer_instance
  refine ⟨hresidueSeparable, ?_⟩
  exact
    ((LocalFieldTheory.DiscreteValuationField.ValuedExtension.ramificationIndex_eq_one_iff_residueDegree_eq_degree_of_finite_separable
        base target).1
      (padicCyclotomic_ramificationIndex_eq_one_prime_pow_sub_one
        p f hf hζ hζgen target)).symm

/-- Canonical unramified cyclotomic endpoint over `ℚ_p`: the actual integral closure
supplies a complete-DVF extension which is finite unramified and has degree
exactly `f`. -/
theorem exists_padicCyclotomic_completeDVF_isFiniteUnramified_degree_eq
    (p f : ℕ) [hp : Fact p.Prime] (hf : 0 < f)
    {L : Type*} [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ f - 1))
    (hζgen : Algebra.adjoin ℚ_[p] ({ζ} : Set L) = ⊤) :
    ∃ target : ValuationTheory.DiscreteValuationField.CompleteDVF.{_, 0} L,
      ∃ hExt :
        (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).valuation.HasExtension
          target.valuation,
        letI :
          (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).valuation.HasExtension
            target.valuation := hExt
        IsIntegralClosure target.valuationSubring
            (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).valuationSubring L ∧
          ValuationTheory.DiscreteValuationField.ValuedExtension.IsFiniteUnramified
              (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).toDVF
              target.toDVF ∧
            ValuationTheory.DiscreteValuationField.ValuedExtension.degree
              (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).toDVF
              target.toDVF = f := by
  let : Algebra.IsSeparable ℚ_[p] L := by infer_instance
  let base := LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p
  obtain ⟨target, hExt, hTarget, _hfundamental⟩ :=
    ValuationTheory.DiscreteValuationField.ValuedExtension.exists_integralClosure_standard_fundamental_identity
      (K := ℚ_[p]) (L := L) base
  let : base.valuation.HasExtension target.valuation := hExt
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L := hTarget
  refine ⟨target, hExt, hTarget, ?_, ?_⟩
  · exact padicCyclotomicUnramified_padic_isFiniteUnramified_prime_pow_sub_one
      p f hf hζ hζgen target
  · exact
      (ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank
        base.toDVF target.toDVF).trans
        (padicCyclotomic_finrank_prime_pow_sub_one
          p f hf hζ hζgen)

end Valuations
end AlgebraicNumberTheory

end
