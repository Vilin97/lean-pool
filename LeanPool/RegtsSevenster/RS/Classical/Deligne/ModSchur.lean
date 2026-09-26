/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.GrowthDichotomy
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.IdemCut
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ModPowCast
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.RowColIdem

/-!
# Schur vanishing at the module level

The block decomposition of the symmetric-group algebra acts on
the relative tensor powers of a module through `modPowAlg`; when
every block of one size acts as zero, the completeness of the
blocks collapses the whole power.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

variable {D : Type u}

/-- **Module-level Schur vanishing**: the block of the shape acts
as zero on the relative tensor power of the module. -/
def ModSchurKilled [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] [Linear ℂ D]
    (A : D) [MonObj A] (X : D) [ModObj A X]
    (P : SchurPackage.{v}) (μ : YoungDiagram) :
    Prop :=
  modPowAlg A X μ.card (P.e μ) = 0

/-- **Module-level upward closure** (Deligne 1.7 over the base):
vanishing of a block's action ascends along containment of
shapes. -/
theorem ModSchurKilled.mono
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (A : D) [MonObj A] (X : D) [ModObj A X]
    (P : SchurPackage.{v})
    {lam mu : YoungDiagram} (hle : lam ≤ mu)
    (h : ModSchurKilled A X P lam) :
    ModSchurKilled A X P mu := by
  by_contra hne
  have hcard : lam.card ≤ mu.card := YoungDiagram.card_le_card hle
  have hlow : modPowAlg A X mu.card (symCast hcard (P.e lam)) =
      0 := modPowAlg_compat A X hcard _ h
  have hz : modPowAlg A X mu.card
      (P.e mu * (symCast hcard (P.e lam) * P.e mu)) = 0 := by
    rw [map_mul, map_mul, hlow, zero_mul, mul_zero]
  have hker := P.block_faithful mu _ (modPowAlg A X mu.card)
    hne _ hz
  rw [← mul_assoc] at hker
  exact P.branching lam mu hle hcard hker

/-- **Completeness collapses the power**: if every block of one
size acts as zero on the relative power, the power itself
vanishes. -/
theorem isZero_modPow_of_cuts
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] [Linear ℂ D]
    (A : D) [MonObj A] (X : D) [ModObj A X]
    (P : SchurPackage.{v}) {k : ℕ}
    (h : ∀ μ : Shape k, modPowAlg A X k (Shape.e P μ) = 0) :
    IsZero (modPow A X k) := by
  rw [Limits.IsZero.iff_id_eq_zero, ← End.one_def]
  calc (1 : End (modPow A X k))
      = modPowAlg A X k 1 := (map_one _).symm
    _ = modPowAlg A X k (∑ μ : Shape k, Shape.e P μ) := by
        rw [P.sum_shape_e_eq_one]
    _ = ∑ μ : Shape k, modPowAlg A X k (Shape.e P μ) :=
        map_sum _ _ _
    _ = 0 := Finset.sum_eq_zero fun μ _ => h μ

/-- **The symmetric power vanishes exactly when the symmetriser
acts as zero.** -/
theorem symPowIdem_eq_zero_iff
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] [Linear ℂ D]
    (A : D) [MonObj A] (X : D) [ModObj A X]
    (n : ℕ) :
    symPowIdem A X n = 0 ↔ IsZero (symPow A X n) := by
  constructor
  · intro h0
    rw [Limits.IsZero.iff_id_eq_zero,
      ← symPowσ_symPowπ A X n]
    have hπ : symPowπ A X n = 0 := by
      rw [← symPowIdem_π A X n, h0, Limits.zero_comp]
    rw [hπ, Limits.comp_zero]
  · intro hz
    have hσ : symPowσ A X n = 0 := hz.eq_of_src _ _
    rw [← symPowπ_symPowσ A X n, hσ, Limits.comp_zero]

/-- **A dead symmetric power kills the row block.** -/
theorem modSchurKilled_row_of_isZero_symPow
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] [Linear ℂ D]
    (A : D) [MonObj A] (X : D) [ModObj A X]
    (P : SchurPackage.{v}) (n : ℕ)
    (h : IsZero (symPow A X (n + 1))) :
    ModSchurKilled A X P (rowShape (n + 1)).val := by
  have h0 : modPowAlg A X (n + 1) (symmetriser (n + 1)) = 0 :=
    (symPowIdem_eq_zero_iff A X (n + 1)).mpr h
  have hgen : ∀ {k : ℕ}, k = n + 1 →
      modPowAlg A X k (symmetriser k) = 0 := by
    rintro k rfl
    exact h0
  rw [ModSchurKilled, P.e_rowShape (n + 1)]
  exact hgen (rowShape (n + 1)).prop

/-- **Row and column kills collapse the whole power** (Deligne
2.9 case (c), module level, Schur half): a module whose row and
column blocks act as zero has vanishing relative power at the
product size. -/
theorem isZero_modPow_of_row_col
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (A : D) [MonObj A] (X : D) [ModObj A X]
    (P : SchurPackage.{v})
    {n m : ℕ}
    (hrow : ModSchurKilled A X P (rowShape (n + 1)).val)
    (hcol : ModSchurKilled A X P (colShape (m + 1)).val) :
    IsZero (modPow A X (n * m + 1)) := by
  have hall : ∀ μ : Shape (n * m + 1),
      modPowAlg A X (n * m + 1) (Shape.e P μ) = 0 := by
    intro μ
    have hk : ModSchurKilled A X P μ.val := by
      by_cases hr : n + 1 ≤ μ.val.rowLen 0
      · exact ModSchurKilled.mono A X P
          (rowShape_le_iff.mpr hr) hrow
      · by_cases hc : m + 1 ≤ μ.val.colLen 0
        · exact ModSchurKilled.mono A X P
            (colShape_le_iff.mpr hc) hcol
        · exfalso
          have hcard := card_le_colLen_mul_rowLen μ.val
          have := μ.prop
          have hbound : μ.val.colLen 0 * μ.val.rowLen 0 ≤
              m * n :=
            Nat.mul_le_mul (by omega) (by omega)
          rw [Nat.mul_comm m n] at hbound
          omega
    exact modPowAlg_compat A X (le_of_eq μ.prop) _ hk
  exact isZero_modPow_of_cuts A X P hall

/-- **The alternating power vanishes exactly when the
antisymmetriser acts as zero.** -/
theorem altPowIdem_eq_zero_iff
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] [Linear ℂ D]
    (A : D) [MonObj A] (X : D) [ModObj A X]
    (n : ℕ) :
    altPowIdem A X n = 0 ↔ IsZero (altPow A X n) := by
  constructor
  · intro h0
    rw [Limits.IsZero.iff_id_eq_zero,
      ← altPowσ_altPowπ A X n]
    have hπ : altPowπ A X n = 0 := by
      rw [← altPowIdem_π A X n, h0, Limits.zero_comp]
    rw [hπ, Limits.comp_zero]
  · intro hz
    have hσ : altPowσ A X n = 0 := hz.eq_of_src _ _
    rw [← altPowπ_altPowσ A X n, hσ, Limits.comp_zero]

/-- **A dead alternating power kills the column block.** -/
theorem modSchurKilled_col_of_isZero_altPow
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] [Linear ℂ D]
    (A : D) [MonObj A] (X : D) [ModObj A X]
    (P : SchurPackage.{v}) (m : ℕ)
    (h : IsZero (altPow A X (m + 1))) :
    ModSchurKilled A X P (colShape (m + 1)).val := by
  have h0 : modPowAlg A X (m + 1)
      (antisymmetriser (m + 1)) = 0 :=
    (altPowIdem_eq_zero_iff A X (m + 1)).mpr h
  have hgen : ∀ {k : ℕ}, k = m + 1 →
      modPowAlg A X k (antisymmetriser k) = 0 := by
    rintro k rfl
    exact h0
  rw [ModSchurKilled, P.e_colShape (m + 1)]
  exact hgen (colShape (m + 1)).prop

/-- **Dead symmetric and alternating powers collapse the relative
power** (Deligne 2.9 case (c), Schur half): the row and column
bridges feed the block collapse. -/
theorem isZero_modPow_of_isZero_sym_alt
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (A : D) [MonObj A] (X : D) [ModObj A X]
    (P : SchurPackage.{v}) {n m : ℕ}
    (hs : IsZero (symPow A X (n + 1)))
    (ha : IsZero (altPow A X (m + 1))) :
    IsZero (modPow A X (n * m + 1)) :=
  isZero_modPow_of_row_col A X P
    (modSchurKilled_row_of_isZero_symPow A X P n hs)
    (modSchurKilled_col_of_isZero_altPow A X P m ha)

/-- **An idempotent's cut vanishes exactly when it acts as
zero.** -/
theorem modPowCutIdem_eq_zero_iff
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] [Linear ℂ D]
    (A : D) [MonObj A] (X : D) [ModObj A X]
    (n : ℕ)
    (e : SymGroupAlgebra n) (he : e * e = e) :
    modPowAlg A X n e = 0 ↔ IsZero (modPowCut A X n e) := by
  constructor
  · intro h0
    rw [Limits.IsZero.iff_id_eq_zero,
      ← modPowCutσ_π A X n e he]
    have hπ : modPowCutπ A X n e = 0 := by
      have h1 : modPowCutIdem A X n e ≫
          modPowCutπ A X n e = modPowCutπ A X n e :=
        modPowCutIdem_π A X n e
      rw [show modPowCutIdem A X n e =
        (0 : modPow A X n ⟶ modPow A X n) from h0] at h1
      rw [Limits.zero_comp] at h1
      exact h1.symm
    rw [hπ, Limits.comp_zero]
  · intro hz
    have hσ : modPowCutσ A X n e he = 0 := hz.eq_of_src _ _
    have h := modPowCutπ_σ A X n e he
    rw [hσ, Limits.comp_zero] at h
    exact h.symm

end RS
