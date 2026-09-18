/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import Mathlib.Probability.Independence.Basic
import LeanPool.ZhangYeungInequality.PFR.Mathlib.Probability.Independence.Basic

/-!
# Consequences of four-way independence
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.iIndepFun

variable {Ω : Type*} [MeasureSpace Ω]
  {G : Type*} [hG : MeasurableSpace G]

variable {Z₁ Z₂ Z₃ Z₄ : Ω → G} (h_indep : iIndepFun ![Z₁, Z₂, Z₃, Z₄])

include h_indep

/-- Four-way independence is invariant under permuting the four variables: for the permutation
`f : Fin 4 → Fin 4` with inverse `g`, the family `F` obtained by reindexing along `f` is
independent. The inverse laws and the identification of `F` with `i ↦ Z_{f i}` are discharged by
case analysis, so every named `reindex_four_*` lemma below is a one-line instance. -/
private lemma reindex_four_of_perm (f g : Fin 4 → Fin 4) (F : Fin 4 → Ω → G)
    (hgf : ∀ i, g (f i) = i := by intro i; fin_cases i <;> rfl)
    (hfg : ∀ i, f (g i) = i := by intro i; fin_cases i <;> rfl)
    (hF : ∀ i, F i = ![Z₁, Z₂, Z₃, Z₄] (f i) := by intro i; fin_cases i <;> rfl) :
    iIndepFun F := by
  rw [funext hF]
  exact h_indep.precomp (Equiv.mk f g hgf hfg).injective

public
lemma reindex_four_abcd :
    iIndepFun ![Z₁, Z₂, Z₃, Z₄] := h_indep

public
lemma reindex_four_abdc :
    iIndepFun ![Z₁, Z₂, Z₄, Z₃] :=
  h_indep.reindex_four_of_perm ![0, 1, 3, 2] ![0, 1, 3, 2] _

public
lemma reindex_four_acbd :
    iIndepFun ![Z₁, Z₃, Z₂, Z₄] :=
  h_indep.reindex_four_of_perm ![0, 2, 1, 3] ![0, 2, 1, 3] _

public
lemma reindex_four_acdb :
    iIndepFun ![Z₁, Z₃, Z₄, Z₂] :=
  h_indep.reindex_four_of_perm ![0, 2, 3, 1] ![0, 3, 1, 2] _

public
lemma reindex_four_adbc :
    iIndepFun ![Z₁, Z₄, Z₂, Z₃] :=
  h_indep.reindex_four_of_perm ![0, 3, 1, 2] ![0, 2, 3, 1] _

public
lemma reindex_four_adcb :
    iIndepFun ![Z₁, Z₄, Z₃, Z₂] :=
  h_indep.reindex_four_of_perm ![0, 3, 2, 1] ![0, 3, 2, 1] _

public
lemma reindex_four_bacd :
    iIndepFun ![Z₂, Z₁, Z₃, Z₄] :=
  h_indep.reindex_four_of_perm ![1, 0, 2, 3] ![1, 0, 2, 3] _

public
lemma reindex_four_badc :
    iIndepFun ![Z₂, Z₁, Z₄, Z₃] :=
  h_indep.reindex_four_of_perm ![1, 0, 3, 2] ![1, 0, 3, 2] _

public
lemma reindex_four_bcad :
    iIndepFun ![Z₂, Z₃, Z₁, Z₄] :=
  h_indep.reindex_four_of_perm ![1, 2, 0, 3] ![2, 0, 1, 3] _

public
lemma reindex_four_bcda :
    iIndepFun ![Z₂, Z₃, Z₄, Z₁] :=
  h_indep.reindex_four_of_perm ![1, 2, 3, 0] ![3, 0, 1, 2] _

public
lemma reindex_four_bdac :
    iIndepFun ![Z₂, Z₄, Z₁, Z₃] :=
  h_indep.reindex_four_of_perm ![1, 3, 0, 2] ![2, 0, 3, 1] _

public
lemma reindex_four_bdca :
    iIndepFun ![Z₂, Z₄, Z₃, Z₁] :=
  h_indep.reindex_four_of_perm ![1, 3, 2, 0] ![3, 0, 2, 1] _

public
lemma reindex_four_cadb :
    iIndepFun ![Z₃, Z₁, Z₄, Z₂] :=
  h_indep.reindex_four_of_perm ![2, 0, 3, 1] ![1, 3, 0, 2] _

public
lemma reindex_four_cabd :
    iIndepFun ![Z₃, Z₁, Z₂, Z₄] :=
  h_indep.reindex_four_of_perm ![2, 0, 1, 3] ![1, 2, 0, 3] _

public
lemma reindex_four_cbad :
    iIndepFun ![Z₃, Z₂, Z₁, Z₄] :=
  h_indep.reindex_four_of_perm ![2, 1, 0, 3] ![2, 1, 0, 3] _

public
lemma reindex_four_dacb :
    iIndepFun ![Z₄, Z₁, Z₃, Z₂] :=
  h_indep.reindex_four_of_perm ![3, 0, 2, 1] ![1, 3, 2, 0] _

private abbrev κ : Fin 3 → Type
  | 0 | 1 => Fin 1
  | 2   => Fin 2

private def κ_equiv : (Σ i, κ i) ≃ Fin 4 where
  toFun := fun x ↦ match x with
    | Sigma.mk 0 _ => 0
    | Sigma.mk 1 _ => 1
    | Sigma.mk 2 ⟨0, _⟩ => 2
    | Sigma.mk 2 ⟨1, _⟩ => 3
  invFun := ![Sigma.mk 0 ⟨0, zero_lt_one⟩, Sigma.mk 1 ⟨0, zero_lt_one⟩,
    Sigma.mk 2 ⟨0, zero_lt_two⟩, Sigma.mk 2 ⟨1, one_lt_two⟩]
  left_inv := by rintro ⟨i, j⟩; fin_cases i <;> fin_cases j <;> rfl
  right_inv i := by fin_cases i <;> rfl

private instance fintype_kappa : ∀ (i : Fin 3), Fintype (κ i)
  | 0 | 1 | 2 => inferInstanceAs (Fintype (Fin _))

/-- If `(Z₁, Z₂, Z₃, Z₄)` are independent, so are `(Z₁, Z₂, φ Z₃ Z₄)` for any measurable `φ`. -/
public
lemma apply_two_last
    (hZ₁ : Measurable Z₁) (hZ₂ : Measurable Z₂) (hZ₃ : Measurable Z₃) (hZ₄ : Measurable Z₄)
    {phi : G → G → G} (hphi : Measurable phi.uncurry) :
    iIndepFun ![Z₁, Z₂, (fun ω ↦ phi (Z₃ ω) (Z₄ ω))] := by
  -- deduce from the assumption the independence of `Z₁`, `Z₂` and `(Z₃, Z₄)`.
  have T := (h_indep.precomp κ_equiv.injective).pi' (m := fun _ _ ↦ hG) ?_; swap
  · rintro ⟨i, j⟩; fin_cases i <;> fin_cases j <;> assumption
  -- apply to this triplet of independent variables the function `phi` applied to `Z₃` and `Z₄`
  -- which does not change the other variables. It retains independence, proving the conclusion.
  let phi_third : ∀ (i : Fin 3), (κ i → G) → G
    | 0 | 1 => (fun f ↦ f ⟨0, zero_lt_one⟩)
    | 2   => (fun f ↦ phi (f ⟨0, zero_lt_two⟩) (f ⟨1, one_lt_two⟩))
  convert T.comp phi_third ?_ with i
  · fin_cases i <;> rfl
  · intro i
    match i with
    | 0 | 1 => exact measurable_pi_apply _
    | 2 =>
      have : Measurable (fun (p : Fin 2 → G) ↦ (p 0, p 1)) := by fun_prop
      exact hphi.comp this

end ProbabilityTheory.iIndepFun
