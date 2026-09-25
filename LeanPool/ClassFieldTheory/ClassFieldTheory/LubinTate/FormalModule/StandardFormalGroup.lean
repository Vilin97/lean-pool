/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.StandardSeries
public import Mathlib.RingTheory.FormalGroup.Basic
/-!
# The standard Lubin--Tate formal group

The recursive same-uniformizer intertwiner applied to the standard
Lubin--Tate series produces the formal group law and all of its scalar
endomorphisms.  The structural identities are proved from the uniqueness of
an intertwiner with prescribed linear term.

This file also records the substitution closure properties of
`SameUniformizer.Intertwines`.  They are useful independently of the
standard series: intertwiners remain intertwiners after a change of
variables, after substituting an intertwining family, and after
one-variable power-series composition.
-/

@[expose] public section

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

universe u v w w'

namespace LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

section LinearTerms

variable {R : Type*} [CommRing R]
variable {σ : Type w} [Fintype σ]
variable {τ : Type w'} [Fintype τ]

namespace HasLinearTerm

/-- In total degree less than two, a series with prescribed linear term
agrees coefficientwise with that linear form. -/
theorem coeff_eq_linearForm
    {H : MvPowerSeries σ R} {L : σ → R}
    (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : d.degree < 2) :
    MvPowerSeries.coeff d H =
      MvPowerSeries.coeff d (linearForm L) := by
  have hd' : (d.degree : ℕ∞) < (2 : ℕ∞) := by
    exact_mod_cast hd
  have hzero :=
    MvPowerSeries.coeff_of_lt_order (hd'.trans_le hH)
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

/-- The coefficient of `X_i` is the prescribed coefficient `L_i`. -/
theorem coeff_single
    {H : MvPowerSeries σ R} {L : σ → R}
    (hH : HasLinearTerm H L) (i : σ) :
    MvPowerSeries.coeff (Finsupp.single i 1) H = L i := by
  rw [hH.coeff_eq_linearForm (Finsupp.single i 1) (by simp)]
  classical
  simp [linearForm, MvPowerSeries.coeff_index_single_X]

private theorem linearForm_weighted_sum
    (L : σ → R) (M : σ → τ → R) :
    (∑ i, MvPowerSeries.C (L i) * linearForm (M i)) =
      linearForm (fun j => ∑ i, L i * M i j) := by
  classical
  apply MvPowerSeries.ext
  intro d
  simp only [linearForm, map_sum, MvPowerSeries.coeff_C_mul,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

/-- Substituting series with prescribed linear terms composes their linear
coefficient matrices. -/
theorem subst
    {H : MvPowerSeries σ R} {L : σ → R}
    (hH : HasLinearTerm H L)
    {G : σ → MvPowerSeries τ R} {M : σ → τ → R}
    (hG : ∀ i, HasLinearTerm (G i) (M i)) :
    HasLinearTerm (MvPowerSeries.subst G H)
      (fun j => ∑ i, L i * M i j) := by
  have hGsubst : MvPowerSeries.HasSubst G :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero
      (fun i => (hG i).constantCoeff_eq_zero)
  have hGorder : ∀ i, (1 : ℕ∞) ≤ (G i).order :=
    fun i =>
      MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr
        (hG i).constantCoeff_eq_zero
  have hinf : (1 : ℕ∞) ≤ ⨅ i, (G i).order :=
    le_iInf hGorder
  have houter :
      (2 : ℕ∞) ≤
        (MvPowerSeries.subst G (H - linearForm L)).order := by
    refine
      (show
        (2 : ℕ∞) ≤
          (⨅ i, (G i).order) * (H - linearForm L).order by
        calc
          (2 : ℕ∞) = 1 * 2 := by norm_num
          _ ≤ (⨅ i, (G i).order) *
              (H - linearForm L).order :=
            mul_le_mul hinf hH (by simp) (by simp)).trans
        (MvPowerSeries.le_order_subst hGsubst
          (H - linearForm L))
  have hsubstLinear :
      MvPowerSeries.subst G (linearForm L) =
        ∑ i, MvPowerSeries.C (L i) * G i := by
    classical
    rw [linearForm,
      ← MvPowerSeries.substAlgHom_apply hGsubst, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, MvPowerSeries.substAlgHom_X]
    simp
  have hlinearIdentity :
      MvPowerSeries.subst G (linearForm L) -
          linearForm (fun j => ∑ i, L i * M i j) =
        ∑ i, MvPowerSeries.C (L i) *
          (G i - linearForm (M i)) := by
    rw [hsubstLinear, ← linearForm_weighted_sum L M,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hlinear :
      (2 : ℕ∞) ≤
        (MvPowerSeries.subst G (linearForm L) -
          linearForm (fun j => ∑ i, L i * M i j)).order := by
    rw [hlinearIdentity]
    apply MvPowerSeries.nat_le_order
    intro d hd
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [MvPowerSeries.coeff_C_mul]
    have hd' : (d.degree : ℕ∞) < (2 : ℕ∞) := by
      exact_mod_cast hd
    rw [MvPowerSeries.coeff_of_lt_order
      (hd'.trans_le (hG i)), mul_zero]
  rw [HasLinearTerm]
  have hdecompose :
      MvPowerSeries.subst G H -
          linearForm (fun j => ∑ i, L i * M i j) =
        MvPowerSeries.subst G (H - linearForm L) +
          (MvPowerSeries.subst G (linearForm L) -
            linearForm (fun j => ∑ i, L i * M i j)) := by
    rw [MvPowerSeries.subst_sub hGsubst]
    ring
  rw [hdecompose]
  exact
    (le_min houter hlinear).trans
      MvPowerSeries.min_order_le_add

end HasLinearTerm

private theorem linearForm_basis (i : σ) :
    linearForm (R := R)
        (fun j : σ => if j = i then (1 : R) else 0) =
      (MvPowerSeries.X i : MvPowerSeries σ R) := by
  classical
  simp [linearForm]

/-- A variable has the corresponding standard-basis linear term. -/
theorem hasLinearTerm_X (i : σ) :
    HasLinearTerm (MvPowerSeries.X i : MvPowerSeries σ R)
      (fun j => if j = i then (1 : R) else 0) := by
  rw [HasLinearTerm, linearForm_basis i, sub_self]
  simp

/-- Zero has zero linear term. -/
theorem hasLinearTerm_zero :
    HasLinearTerm (0 : MvPowerSeries σ R) (fun _ => 0) := by
  simp [HasLinearTerm, linearForm]

end LinearTerms

section SubstitutionClosure

variable {σ : Type w}
variable {τ : Type w'}

/-- Multivariable substitution commutes with substituting a multivariable
series into a one-variable power series. -/
theorem subst_powerSeries_subst
    {H : MvPowerSeries σ F.valuationSubring}
    (hH : PowerSeries.HasSubst H)
    {G : σ → MvPowerSeries τ F.valuationSubring}
    (hG : MvPowerSeries.HasSubst G)
    (f : PowerSeries F.valuationSubring) :
    MvPowerSeries.subst G (PowerSeries.subst H f) =
      PowerSeries.subst (MvPowerSeries.subst G H) f := by
  change
    MvPowerSeries.subst G
        (MvPowerSeries.subst (fun _ : Unit => H) f) =
      MvPowerSeries.subst
        (fun _ : Unit => MvPowerSeries.subst G H) f
  exact MvPowerSeries.subst_comp_subst_apply hH.const hG f

/-- Substituting a family into `e(X_i)` gives `e` evaluated at the
corresponding member of that family. -/
theorem subst_inVariable
    (e : LubinTateSeries F π)
    {G : σ → MvPowerSeries τ F.valuationSubring}
    (hG : MvPowerSeries.HasSubst G) (i : σ) :
    MvPowerSeries.subst G (inVariable e i) =
      PowerSeries.subst (G i) e.toPowerSeries := by
  rw [inVariable]
  rw [subst_powerSeries_subst (PowerSeries.HasSubst.X i) hG]
  simp [MvPowerSeries.subst_X hG]

namespace Intertwines

/-- An intertwiner remains an intertwiner after substituting a family of
intertwiners. -/
theorem subst
    [Finite σ] [Finite τ]
    {e ebar ehat : LubinTateSeries F π}
    {H : MvPowerSeries σ F.valuationSubring}
    (hH : Intertwines e ebar H)
    (hHsubst : PowerSeries.HasSubst H)
    {G : σ → MvPowerSeries τ F.valuationSubring}
    (hGsubst : MvPowerSeries.HasSubst G)
    (hG : ∀ i, Intertwines ebar ehat (G i)) :
    Intertwines e ehat (MvPowerSeries.subst G H) := by
  let := Fintype.ofFinite σ
  let := Fintype.ofFinite τ
  rw [Intertwines] at hH ⊢
  calc
    PowerSeries.subst (MvPowerSeries.subst G H) e.toPowerSeries =
        MvPowerSeries.subst G
          (PowerSeries.subst H e.toPowerSeries) :=
      (subst_powerSeries_subst hHsubst hGsubst
        e.toPowerSeries).symm
    _ = MvPowerSeries.subst G
          (MvPowerSeries.subst
            (fun i : σ => inVariable ebar i) H) := by
      rw [hH]
    _ = MvPowerSeries.subst
          (fun i : σ =>
            MvPowerSeries.subst G (inVariable ebar i)) H :=
      MvPowerSeries.subst_comp_subst_apply
        (inVariable_hasSubst ebar) hGsubst H
    _ = MvPowerSeries.subst
          (fun i : σ =>
            PowerSeries.subst (G i) ebar.toPowerSeries) H := by
      congr 1
      funext i
      exact subst_inVariable ebar hGsubst i
    _ = MvPowerSeries.subst
          (fun i : σ =>
            MvPowerSeries.subst
              (fun j : τ => inVariable ehat j) (G i)) H := by
      congr 1
      funext i
      exact hG i
    _ = MvPowerSeries.subst
          (fun j : τ => inVariable ehat j)
          (MvPowerSeries.subst G H) :=
      (MvPowerSeries.subst_comp_subst_apply
        hGsubst (inVariable_hasSubst ehat) H).symm

/-- Reindexing variables preserves the intertwining equation. -/
theorem reindex
    [Finite σ] [Finite τ]
    {e ebar : LubinTateSeries F π}
    {H : MvPowerSeries σ F.valuationSubring}
    (hH : Intertwines e ebar H)
    (hHsubst : PowerSeries.HasSubst H)
    (f : σ → τ) :
    Intertwines e ebar
      (MvPowerSeries.subst
        (fun i => MvPowerSeries.X (f i)) H) := by
  classical
  let := Fintype.ofFinite σ
  let := Fintype.ofFinite τ
  apply hH.subst hHsubst
    (MvPowerSeries.hasSubst_of_constantCoeff_zero
      (fun _ => by simp))
  intro i
  exact intertwines_X ebar (f i)

/-- One-variable power-series composition is a special case of
substitution by an intertwining family. -/
theorem powerSeries_subst
    [Finite τ]
    {e ebar ehat : LubinTateSeries F π}
    {H : PowerSeries F.valuationSubring}
    (hH : Intertwines e ebar H)
    (hHsubst : PowerSeries.HasSubst H)
    {G : MvPowerSeries τ F.valuationSubring}
    (hG : Intertwines ebar ehat G)
    (hGsubst : PowerSeries.HasSubst G) :
    Intertwines e ehat (PowerSeries.subst G H) := by
  classical
  let := Fintype.ofFinite τ
  exact hH.subst hHsubst hGsubst.const (fun _ => hG)

end Intertwines

/-- Zero intertwines any two series with zero constant coefficient. -/
theorem intertwines_zero
    [Finite σ]
    (e ebar : LubinTateSeries F π) :
    Intertwines e ebar
      (0 : MvPowerSeries σ F.valuationSubring) := by
  classical
  let := Fintype.ofFinite σ
  rw [Intertwines]
  change
    MvPowerSeries.subst
        (0 : Unit →
          MvPowerSeries σ F.valuationSubring)
        e.toPowerSeries =
      MvPowerSeries.subst
        (fun i : σ => inVariable ebar i) 0
  rw [MvPowerSeries.subst_zero_of_constantCoeff_zero
    e.constantCoeff_eq_zero]
  rw [← MvPowerSeries.substAlgHom_apply
    (inVariable_hasSubst ebar), map_zero]

end SubstitutionClosure

section StandardFormalGroup

variable (hπ :
  F.toCompleteDVF.valuation.IsUniformizer (π : K))

private abbrev standardSeries :
    LubinTateSeries F π :=
  standardLubinTateSeries hπ

/-- The unique two-variable series with linear term `X + Y` commuting with
the standard Lubin--Tate series. -/
noncomputable def standardFormalGroupPowerSeries :
    MvPowerSeries (Fin 2) F.valuationSubring :=
  recursiveIntertwiner hπ (standardSeries hπ)
    (standardSeries hπ) (fun _ => 1)

/-- The standard formal-group series has linear term `X + Y`. -/
theorem standardFormalGroupPowerSeries_hasLinearTerm :
    HasLinearTerm (standardFormalGroupPowerSeries hπ)
      (fun _ : Fin 2 => 1) :=
  recursiveIntertwiner_hasLinearTerm hπ
    (standardSeries hπ) (standardSeries hπ) (fun _ => 1)

/-- The standard formal-group series commutes with the standard
Lubin--Tate series. -/
theorem standardFormalGroupPowerSeries_intertwines :
    Intertwines (standardSeries hπ) (standardSeries hπ)
      (standardFormalGroupPowerSeries hπ) :=
  recursiveIntertwiner_intertwines hπ
    (standardSeries hπ) (standardSeries hπ) (fun _ => 1)

/-- The standard formal-group series is the unique two-variable
intertwiner with linear term `X + Y`. -/
theorem existsUnique_standardFormalGroupPowerSeries :
    ∃! H : MvPowerSeries (Fin 2) F.valuationSubring,
      HasLinearTerm H (fun _ : Fin 2 => 1) ∧
        Intertwines (standardSeries hπ) (standardSeries hπ) H :=
  existsUnique_intertwiner hπ
    (standardSeries hπ) (standardSeries hπ) (fun _ => 1)

private theorem standardFormalGroupPowerSeries_subst_hasLinearTerm
    {τ : Type w} [Fintype τ]
    {G₀ G₁ : MvPowerSeries τ F.valuationSubring}
    {M₀ M₁ : τ → F.valuationSubring}
    (hG₀ : HasLinearTerm G₀ M₀)
    (hG₁ : HasLinearTerm G₁ M₁) :
    HasLinearTerm
      (MvPowerSeries.subst ![G₀, G₁]
        (standardFormalGroupPowerSeries hπ))
      (fun j => M₀ j + M₁ j) := by
  have h :=
    (standardFormalGroupPowerSeries_hasLinearTerm hπ).subst
      (G := ![G₀, G₁]) (M := ![M₀, M₁])
      (by
        intro i
        fin_cases i
        · exact hG₀
        · exact hG₁)
  simpa [Fin.sum_univ_two] using h

private theorem standardFormalGroupPowerSeries_subst_intertwines
    {τ : Type w} [Fintype τ]
    {G₀ G₁ : MvPowerSeries τ F.valuationSubring}
    {M₀ M₁ : τ → F.valuationSubring}
    (hG₀ : HasLinearTerm G₀ M₀)
    (hG₁ : HasLinearTerm G₁ M₁)
    (hI₀ : Intertwines (standardSeries hπ)
      (standardSeries hπ) G₀)
    (hI₁ : Intertwines (standardSeries hπ)
      (standardSeries hπ) G₁) :
    Intertwines (standardSeries hπ) (standardSeries hπ)
      (MvPowerSeries.subst ![G₀, G₁]
        (standardFormalGroupPowerSeries hπ)) := by
  apply
    (standardFormalGroupPowerSeries_intertwines hπ).subst
      (standardFormalGroupPowerSeries_hasLinearTerm hπ).hasSubst
      (MvPowerSeries.hasSubst_of_constantCoeff_zero
        (fun i => by
          fin_cases i
          · exact hG₀.constantCoeff_eq_zero
          · exact hG₁.constantCoeff_eq_zero))
  intro i
  fin_cases i
  · exact hI₀
  · exact hI₁

/-- The left identity law, proved by uniqueness of the linear-term-one
intertwiner. -/
theorem standardFormalGroupPowerSeries_subst_X_zero :
    MvPowerSeries.subst
        ![(MvPowerSeries.X () :
            PowerSeries F.valuationSubring), 0]
        (standardFormalGroupPowerSeries hπ) =
      (MvPowerSeries.X () :
        PowerSeries F.valuationSubring) := by
  have hX :
      HasLinearTerm
        (MvPowerSeries.X () :
          PowerSeries F.valuationSubring)
        (fun _ : Unit => 1) := by
    simpa using
      (hasLinearTerm_X (R := F.valuationSubring) ())
  have hzero :
      HasLinearTerm
        (0 : PowerSeries F.valuationSubring)
        (fun _ : Unit => 0) :=
    hasLinearTerm_zero
  have hleft :=
    standardFormalGroupPowerSeries_subst_hasLinearTerm
      hπ hX hzero
  have hleft' :
      HasLinearTerm
        (MvPowerSeries.subst
          ![(MvPowerSeries.X () :
              PowerSeries F.valuationSubring), 0]
          (standardFormalGroupPowerSeries hπ))
        (fun _ : Unit => 1) := by
    simpa using hleft
  have hIleft :=
    standardFormalGroupPowerSeries_subst_intertwines
      hπ hX hzero
        (intertwines_X (standardSeries hπ) ())
        (intertwines_zero
          (standardSeries hπ) (standardSeries hπ))
  exact
    eq_of_hasLinearTerm_of_intertwines hπ
      (standardSeries hπ) (standardSeries hπ)
      (fun _ : Unit => 1)
      hleft' hIleft hX
      (intertwines_X (standardSeries hπ) ())

/-- The right identity law, proved by uniqueness. -/
theorem standardFormalGroupPowerSeries_subst_zero_X :
    MvPowerSeries.subst
        ![0, (MvPowerSeries.X () :
            PowerSeries F.valuationSubring)]
        (standardFormalGroupPowerSeries hπ) =
      (MvPowerSeries.X () :
        PowerSeries F.valuationSubring) := by
  have hX :
      HasLinearTerm
        (MvPowerSeries.X () :
          PowerSeries F.valuationSubring)
        (fun _ : Unit => 1) := by
    simpa using
      (hasLinearTerm_X (R := F.valuationSubring) ())
  have hzero :
      HasLinearTerm
        (0 : PowerSeries F.valuationSubring)
        (fun _ : Unit => 0) :=
    hasLinearTerm_zero
  have hright :=
    standardFormalGroupPowerSeries_subst_hasLinearTerm
      hπ hzero hX
  have hright' :
      HasLinearTerm
        (MvPowerSeries.subst
          ![0, (MvPowerSeries.X () :
              PowerSeries F.valuationSubring)]
          (standardFormalGroupPowerSeries hπ))
        (fun _ : Unit => 1) := by
    simpa using hright
  have hIright :=
    standardFormalGroupPowerSeries_subst_intertwines
      hπ hzero hX
        (intertwines_zero
          (standardSeries hπ) (standardSeries hπ))
        (intertwines_X (standardSeries hπ) ())
  exact
    eq_of_hasLinearTerm_of_intertwines hπ
      (standardSeries hπ) (standardSeries hπ)
      (fun _ : Unit => 1)
      hright' hIright hX
      (intertwines_X (standardSeries hπ) ())

/-- Associativity of the standard formal-group series, proved by comparing
the two three-variable intertwiners with linear term `X + Y + Z`. -/
theorem standardFormalGroupPowerSeries_assoc :
    MvPowerSeries.subst
        ![
          MvPowerSeries.subst
            ![
              (MvPowerSeries.X 0 :
                MvPowerSeries (Fin 3) F.valuationSubring),
              MvPowerSeries.X 1]
            (standardFormalGroupPowerSeries hπ),
          MvPowerSeries.X 2]
        (standardFormalGroupPowerSeries hπ) =
      MvPowerSeries.subst
        ![
          (MvPowerSeries.X 0 :
            MvPowerSeries (Fin 3) F.valuationSubring),
          MvPowerSeries.subst
            ![MvPowerSeries.X 1, MvPowerSeries.X 2]
            (standardFormalGroupPowerSeries hπ)]
        (standardFormalGroupPowerSeries hπ) := by
  let B : Fin 3 → Fin 3 → F.valuationSubring :=
    fun i j =>
      @ite F.valuationSubring (j = i)
        (Classical.propDecidable (j = i)) 1 0
  have hX (i : Fin 3) :
      HasLinearTerm
        (MvPowerSeries.X i :
          MvPowerSeries (Fin 3) F.valuationSubring)
        (B i) := by
    simpa [B] using
      (hasLinearTerm_X (R := F.valuationSubring) i)
  have hIX (i : Fin 3) :
      Intertwines (standardSeries hπ) (standardSeries hπ)
        (MvPowerSeries.X i :
          MvPowerSeries (Fin 3) F.valuationSubring) :=
    intertwines_X (standardSeries hπ) i
  have hF₀₁ :
      HasLinearTerm
        (MvPowerSeries.subst
          ![
            (MvPowerSeries.X 0 :
              MvPowerSeries (Fin 3) F.valuationSubring),
            MvPowerSeries.X 1]
          (standardFormalGroupPowerSeries hπ))
        (fun j => B 0 j + B 1 j) :=
    standardFormalGroupPowerSeries_subst_hasLinearTerm
      hπ (hX 0) (hX 1)
  have hIF₀₁ :
      Intertwines (standardSeries hπ) (standardSeries hπ)
        (MvPowerSeries.subst
          ![
            (MvPowerSeries.X 0 :
              MvPowerSeries (Fin 3) F.valuationSubring),
            MvPowerSeries.X 1]
          (standardFormalGroupPowerSeries hπ)) :=
    standardFormalGroupPowerSeries_subst_intertwines
      hπ (hX 0) (hX 1) (hIX 0) (hIX 1)
  have hF₁₂ :
      HasLinearTerm
        (MvPowerSeries.subst
          ![
            (MvPowerSeries.X 1 :
              MvPowerSeries (Fin 3) F.valuationSubring),
            MvPowerSeries.X 2]
          (standardFormalGroupPowerSeries hπ))
        (fun j => B 1 j + B 2 j) :=
    standardFormalGroupPowerSeries_subst_hasLinearTerm
      hπ (hX 1) (hX 2)
  have hIF₁₂ :
      Intertwines (standardSeries hπ) (standardSeries hπ)
        (MvPowerSeries.subst
          ![
            (MvPowerSeries.X 1 :
              MvPowerSeries (Fin 3) F.valuationSubring),
            MvPowerSeries.X 2]
          (standardFormalGroupPowerSeries hπ)) :=
    standardFormalGroupPowerSeries_subst_intertwines
      hπ (hX 1) (hX 2) (hIX 1) (hIX 2)
  have hleft :=
    standardFormalGroupPowerSeries_subst_hasLinearTerm
      hπ hF₀₁ (hX 2)
  have hright :=
    standardFormalGroupPowerSeries_subst_hasLinearTerm
      hπ (hX 0) hF₁₂
  have hleft' :
      HasLinearTerm
        (MvPowerSeries.subst
          ![
            MvPowerSeries.subst
              ![
                (MvPowerSeries.X 0 :
                  MvPowerSeries (Fin 3)
                    F.valuationSubring),
                MvPowerSeries.X 1]
              (standardFormalGroupPowerSeries hπ),
            MvPowerSeries.X 2]
          (standardFormalGroupPowerSeries hπ))
        (fun _ : Fin 3 => 1) := by
    convert hleft using 1
    funext j
    fin_cases j <;> simp [B]
  have hright' :
      HasLinearTerm
        (MvPowerSeries.subst
          ![
            (MvPowerSeries.X 0 :
              MvPowerSeries (Fin 3) F.valuationSubring),
            MvPowerSeries.subst
              ![MvPowerSeries.X 1, MvPowerSeries.X 2]
              (standardFormalGroupPowerSeries hπ)]
          (standardFormalGroupPowerSeries hπ))
        (fun _ : Fin 3 => 1) := by
    convert hright using 1
    funext j
    fin_cases j <;> simp [B]
  have hIleft :=
    standardFormalGroupPowerSeries_subst_intertwines
      hπ hF₀₁ (hX 2) hIF₀₁ (hIX 2)
  have hIright :=
    standardFormalGroupPowerSeries_subst_intertwines
      hπ (hX 0) hF₁₂ (hIX 0) hIF₁₂
  exact
    eq_of_hasLinearTerm_of_intertwines hπ
      (standardSeries hπ) (standardSeries hπ)
      (fun _ : Fin 3 => 1)
      hleft' hIleft hright' hIright

/-- Commutativity of the standard formal-group series, proved by
uniqueness. -/
theorem standardFormalGroupPowerSeries_comm :
    standardFormalGroupPowerSeries hπ =
      MvPowerSeries.subst
        ![
          (MvPowerSeries.X 1 :
            MvPowerSeries (Fin 2) F.valuationSubring),
          MvPowerSeries.X 0]
        (standardFormalGroupPowerSeries hπ) := by
  let B : Fin 2 → Fin 2 → F.valuationSubring :=
    fun i j =>
      @ite F.valuationSubring (j = i)
        (Classical.propDecidable (j = i)) 1 0
  have hX (i : Fin 2) :
      HasLinearTerm
        (MvPowerSeries.X i :
          MvPowerSeries (Fin 2) F.valuationSubring)
        (B i) := by
    simpa [B] using
      (hasLinearTerm_X (R := F.valuationSubring) i)
  have hswap :=
    standardFormalGroupPowerSeries_subst_hasLinearTerm
      hπ (hX 1) (hX 0)
  have hswap' :
      HasLinearTerm
        (MvPowerSeries.subst
          ![
            (MvPowerSeries.X 1 :
              MvPowerSeries (Fin 2) F.valuationSubring),
            MvPowerSeries.X 0]
          (standardFormalGroupPowerSeries hπ))
        (fun _ : Fin 2 => 1) := by
    convert hswap using 1
    funext j
    fin_cases j <;> simp [B]
  have hIswap :=
    standardFormalGroupPowerSeries_subst_intertwines
      hπ (hX 1) (hX 0)
        (intertwines_X (standardSeries hπ) 1)
        (intertwines_X (standardSeries hπ) 0)
  exact
    eq_of_hasLinearTerm_of_intertwines hπ
      (standardSeries hπ) (standardSeries hπ)
      (fun _ : Fin 2 => 1)
      (standardFormalGroupPowerSeries_hasLinearTerm hπ)
      (standardFormalGroupPowerSeries_intertwines hπ)
      hswap' hIswap

/-- The formal group law attached to the standard Lubin--Tate series. -/
noncomputable def standardFormalGroup :
    FormalGroup F.valuationSubring where
  toPowerSeries := standardFormalGroupPowerSeries hπ
  zero_constantCoeff :=
    (standardFormalGroupPowerSeries_hasLinearTerm
      hπ).constantCoeff_eq_zero
  lin_coeff_X :=
    (standardFormalGroupPowerSeries_hasLinearTerm
      hπ).coeff_single 0
  lin_coeff_Y :=
    (standardFormalGroupPowerSeries_hasLinearTerm
      hπ).coeff_single 1
  assoc := standardFormalGroupPowerSeries_assoc hπ

/-- The standard Lubin--Tate formal group is commutative. -/
noncomputable instance standardFormalGroup_isComm :
    (standardFormalGroup hπ).IsComm where
  comm := standardFormalGroupPowerSeries_comm hπ

end StandardFormalGroup

section StandardEndomorphisms

variable (hπ :
  F.toCompleteDVF.valuation.IsUniformizer (π : K))

private abbrev standardSeries' :
    LubinTateSeries F π :=
  standardLubinTateSeries hπ

/-- The one-variable standard Lubin--Tate endomorphism with linear
coefficient `a`. -/
noncomputable def standardLubinTateEndomorphism
    (a : F.valuationSubring) :
    PowerSeries F.valuationSubring :=
  recursiveIntertwiner hπ (standardSeries' hπ)
    (standardSeries' hπ) (fun _ : Unit => a)

/-- The endomorphism `[a]` has linear coefficient `a`. -/
theorem standardLubinTateEndomorphism_hasLinearTerm
    (a : F.valuationSubring) :
    HasLinearTerm (standardLubinTateEndomorphism hπ a)
      (fun _ : Unit => a) :=
  recursiveIntertwiner_hasLinearTerm hπ
    (standardSeries' hπ) (standardSeries' hπ)
    (fun _ : Unit => a)

/-- The endomorphism `[a]` commutes with the standard Lubin--Tate
series. -/
theorem standardLubinTateEndomorphism_intertwines
    (a : F.valuationSubring) :
    Intertwines (standardSeries' hπ) (standardSeries' hπ)
      (standardLubinTateEndomorphism hπ a) :=
  recursiveIntertwiner_intertwines hπ
    (standardSeries' hπ) (standardSeries' hπ)
    (fun _ : Unit => a)

/-- `[a]` is the unique one-variable intertwiner with linear coefficient
`a`. -/
theorem existsUnique_standardLubinTateEndomorphism
    (a : F.valuationSubring) :
    ∃! f : PowerSeries F.valuationSubring,
      HasLinearTerm f (fun _ : Unit => a) ∧
        Intertwines (standardSeries' hπ) (standardSeries' hπ) f :=
  existsUnique_intertwiner hπ
    (standardSeries' hπ) (standardSeries' hπ)
    (fun _ : Unit => a)

/-- The coefficient of `X` in `[a]` is `a`. -/
@[simp]
theorem standardLubinTateEndomorphism_coeff_one
    (a : F.valuationSubring) :
    PowerSeries.coeff 1
      (standardLubinTateEndomorphism hπ a) = a := by
  exact
    (standardLubinTateEndomorphism_hasLinearTerm
      hπ a).coeff_single ()

/-- The scalar `1` acts by the identity series. -/
theorem standardLubinTateEndomorphism_one :
    standardLubinTateEndomorphism hπ 1 =
      PowerSeries.X := by
  have hX :
      HasLinearTerm
        (PowerSeries.X :
          PowerSeries F.valuationSubring)
        (fun _ : Unit => 1) := by
    simpa [PowerSeries.X] using
      (hasLinearTerm_X (R := F.valuationSubring) ())
  exact
    eq_of_hasLinearTerm_of_intertwines hπ
      (standardSeries' hπ) (standardSeries' hπ)
      (fun _ : Unit => 1)
      (standardLubinTateEndomorphism_hasLinearTerm hπ 1)
      (standardLubinTateEndomorphism_intertwines hπ 1)
      hX (intertwines_X (standardSeries' hπ) ())

/-- The scalar `0` acts by the zero series. -/
theorem standardLubinTateEndomorphism_zero :
    standardLubinTateEndomorphism hπ 0 = 0 := by
  exact
    eq_of_hasLinearTerm_of_intertwines hπ
      (standardSeries' hπ) (standardSeries' hπ)
      (fun _ : Unit => 0)
      (standardLubinTateEndomorphism_hasLinearTerm hπ 0)
      (standardLubinTateEndomorphism_intertwines hπ 0)
      hasLinearTerm_zero
      (intertwines_zero
        (standardSeries' hπ) (standardSeries' hπ))

/-- Addition of scalars is addition in the standard formal group. -/
theorem standardLubinTateEndomorphism_add
    (a b : F.valuationSubring) :
    standardLubinTateEndomorphism hπ (a + b) =
      MvPowerSeries.subst
        ![
          standardLubinTateEndomorphism hπ a,
          standardLubinTateEndomorphism hπ b]
        (standardFormalGroupPowerSeries hπ) := by
  have hright :=
    standardFormalGroupPowerSeries_subst_hasLinearTerm
      hπ
      (standardLubinTateEndomorphism_hasLinearTerm hπ a)
      (standardLubinTateEndomorphism_hasLinearTerm hπ b)
  have hright' :
      HasLinearTerm
        (MvPowerSeries.subst
          ![
            standardLubinTateEndomorphism hπ a,
            standardLubinTateEndomorphism hπ b]
          (standardFormalGroupPowerSeries hπ))
        (fun _ : Unit => a + b) := by
    simpa using hright
  have hIright :=
    standardFormalGroupPowerSeries_subst_intertwines
      hπ
      (standardLubinTateEndomorphism_hasLinearTerm hπ a)
      (standardLubinTateEndomorphism_hasLinearTerm hπ b)
      (standardLubinTateEndomorphism_intertwines hπ a)
      (standardLubinTateEndomorphism_intertwines hπ b)
  exact
    eq_of_hasLinearTerm_of_intertwines hπ
      (standardSeries' hπ) (standardSeries' hπ)
      (fun _ : Unit => a + b)
      (standardLubinTateEndomorphism_hasLinearTerm hπ (a + b))
      (standardLubinTateEndomorphism_intertwines hπ (a + b))
      hright' hIright

/-- Multiplication of scalars is composition of endomorphisms:
`[ab](X) = [a]([b](X))`. -/
theorem standardLubinTateEndomorphism_mul
    (a b : F.valuationSubring) :
    standardLubinTateEndomorphism hπ (a * b) =
      PowerSeries.subst
        (standardLubinTateEndomorphism hπ b)
        (standardLubinTateEndomorphism hπ a) := by
  have hcomp :=
    (standardLubinTateEndomorphism_hasLinearTerm hπ a).subst
      (G := fun _ : Unit =>
        standardLubinTateEndomorphism hπ b)
      (M := fun _ : Unit => fun _ : Unit => b)
      (fun _ =>
        standardLubinTateEndomorphism_hasLinearTerm hπ b)
  have hcomp' :
      HasLinearTerm
        (PowerSeries.subst
          (standardLubinTateEndomorphism hπ b)
          (standardLubinTateEndomorphism hπ a))
        (fun _ : Unit => a * b) := by
    simpa [PowerSeries.subst_def] using hcomp
  have hIcomp :=
    (standardLubinTateEndomorphism_intertwines
      hπ a).powerSeries_subst
        (standardLubinTateEndomorphism_hasLinearTerm
          hπ a).hasSubst
        (standardLubinTateEndomorphism_intertwines hπ b)
        (standardLubinTateEndomorphism_hasLinearTerm
          hπ b).hasSubst
  exact
    eq_of_hasLinearTerm_of_intertwines hπ
      (standardSeries' hπ) (standardSeries' hπ)
      (fun _ : Unit => a * b)
      (standardLubinTateEndomorphism_hasLinearTerm hπ (a * b))
      (standardLubinTateEndomorphism_intertwines hπ (a * b))
      hcomp' hIcomp

/-- The series `[a](X_i)` in a chosen variable. -/
noncomputable def standardLubinTateEndomorphismInVariable
    {σ : Type w} (a : F.valuationSubring) (i : σ) :
    MvPowerSeries σ F.valuationSubring :=
  PowerSeries.subst (MvPowerSeries.X i)
    (standardLubinTateEndomorphism hπ a)

/-- The linear term of `[a](X_i)` is `a X_i`. -/
theorem standardLubinTateEndomorphismInVariable_hasLinearTerm
    {σ : Type w} [Fintype σ]
    (a : F.valuationSubring) (i : σ) :
    HasLinearTerm
      (standardLubinTateEndomorphismInVariable hπ a i)
      (fun j => if j = i then a else 0) := by
  have h :=
    (standardLubinTateEndomorphism_hasLinearTerm hπ a).subst
      (G := fun _ : Unit =>
        (MvPowerSeries.X i :
          MvPowerSeries σ F.valuationSubring))
      (M := fun _ : Unit =>
        fun j : σ => if j = i then 1 else 0)
      (fun _ =>
        hasLinearTerm_X (R := F.valuationSubring) i)
  simpa [standardLubinTateEndomorphismInVariable,
    PowerSeries.subst_def] using h

/-- The reindexed series `[a](X_i)` remains an intertwiner. -/
theorem standardLubinTateEndomorphismInVariable_intertwines
    {σ : Type w} [Finite σ]
    (a : F.valuationSubring) (i : σ) :
    Intertwines (standardSeries' hπ) (standardSeries' hπ)
      (standardLubinTateEndomorphismInVariable hπ a i) := by
  classical
  let := Fintype.ofFinite σ
  simpa [standardLubinTateEndomorphismInVariable,
    PowerSeries.subst_def] using
    (standardLubinTateEndomorphism_intertwines
      hπ a).reindex
        (standardLubinTateEndomorphism_hasLinearTerm
          hπ a).hasSubst
        (fun _ : Unit => i)

/-- The full scalar endomorphism identity
`[a](F(X,Y)) = F([a](X),[a](Y))`. -/
theorem standardLubinTateEndomorphism_map_formalGroup
    (a : F.valuationSubring) :
    PowerSeries.subst
        (standardFormalGroupPowerSeries hπ)
        (standardLubinTateEndomorphism hπ a) =
      MvPowerSeries.subst
        ![
          standardLubinTateEndomorphismInVariable hπ a
            (0 : Fin 2),
          standardLubinTateEndomorphismInVariable hπ a
            (1 : Fin 2)]
        (standardFormalGroupPowerSeries hπ) := by
  have hleft :=
    (standardLubinTateEndomorphism_hasLinearTerm hπ a).subst
      (G := fun _ : Unit =>
        standardFormalGroupPowerSeries hπ)
      (M := fun _ : Unit =>
        fun _ : Fin 2 => 1)
      (fun _ =>
        standardFormalGroupPowerSeries_hasLinearTerm hπ)
  have hleft' :
      HasLinearTerm
        (PowerSeries.subst
          (standardFormalGroupPowerSeries hπ)
          (standardLubinTateEndomorphism hπ a))
        (fun _ : Fin 2 => a) := by
    simpa [PowerSeries.subst_def] using hleft
  have hIleft :=
    (standardLubinTateEndomorphism_intertwines
      hπ a).powerSeries_subst
        (standardLubinTateEndomorphism_hasLinearTerm
          hπ a).hasSubst
        (standardFormalGroupPowerSeries_intertwines hπ)
        (standardFormalGroupPowerSeries_hasLinearTerm
          hπ).hasSubst
  have hright :=
    standardFormalGroupPowerSeries_subst_hasLinearTerm
      hπ
      (standardLubinTateEndomorphismInVariable_hasLinearTerm
        hπ a (0 : Fin 2))
      (standardLubinTateEndomorphismInVariable_hasLinearTerm
        hπ a (1 : Fin 2))
  have hright' :
      HasLinearTerm
        (MvPowerSeries.subst
          ![
            standardLubinTateEndomorphismInVariable hπ a
              (0 : Fin 2),
            standardLubinTateEndomorphismInVariable hπ a
              (1 : Fin 2)]
          (standardFormalGroupPowerSeries hπ))
        (fun _ : Fin 2 => a) := by
    convert hright using 1
    funext j
    fin_cases j <;> simp
  have hIright :=
    standardFormalGroupPowerSeries_subst_intertwines
      hπ
      (standardLubinTateEndomorphismInVariable_hasLinearTerm
        hπ a (0 : Fin 2))
      (standardLubinTateEndomorphismInVariable_hasLinearTerm
        hπ a (1 : Fin 2))
      (standardLubinTateEndomorphismInVariable_intertwines
        hπ a (0 : Fin 2))
      (standardLubinTateEndomorphismInVariable_intertwines
        hπ a (1 : Fin 2))
  exact
    eq_of_hasLinearTerm_of_intertwines hπ
      (standardSeries' hπ) (standardSeries' hπ)
      (fun _ : Fin 2 => a)
      hleft' hIleft hright' hIright

end StandardEndomorphisms

end SameUniformizer
end LubinTate

end
