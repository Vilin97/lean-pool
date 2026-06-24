/-
Copyright (c) 2026 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import LeanPool.VirasoroProject.FockSpace
import LeanPool.VirasoroProject.Sugawara
import LeanPool.VirasoroProject.VirasoroVerma

/-!
# Sugawara construction applied to the charged Fock space

This file equips the charged Fock space representation of the Heisenberg algebra with the
structure of a representation of the Virasoro algebra by applying the basic bosonic Sugawara
construction.

## Main definitions

* `sugawaraRepresentationOfModuleUeaHeisenbergAlgebra`: A variant of the Sugawara construction
  where the hypothesis is that the space is a module over the universal enveloping algebra of
  the Heisenberg algebra with local truncation condition.
* `ChargedFockSpace.sugawaraRepresentation`: The representation of Virasoro algebra with
  central charge `c=1` on the charged Fock space, obtained by the basic bosonic Sugawara
  construction.
* `ChargedFockSpace.instModuleUEAVirasoroAlgebra`: The charged Fock space
  has the structure of a module over the universal enveloping algebra of the Virasoro algebra, by
  the basic bosonic Sugawara construction.
* `ChargedFockSpace.virasoroVermaToChargedFockSpace`: There is a Virasoro-module map from the
  Virasoro Verma module with central charge `c = 1` and highest weight `h = α²/2` to the charged
  Fock space with charge (`J₀`-eigenvalue) `α`, mapping the highest weight vector of the Verma
  module to the vacuum vector of the Fock space.

## Main statements

* `ChargedFockSpace.sugawaraRepresentation_lgen_zero_apply_vacuum`: The vacuum in the charged Fock
  space is an eigenvector of `L₀` with eigenvalue `α²/2`.
* `ChargedFockSpace.sugawaraRepresentation_lgen_pos_apply_vacuum`: The vacuum in the charged Fock
  space is annihilated by `Lₙ` for `n > 0`.

## Tags

Heisenberg algebra, Fock space, Virasoro algebra, Sugawara construction

-/

namespace VirasoroProject

-- `LieRing.ofAssociativeRing` is only a local instance in Mathlib; it provides the Lie ring
-- structure on the universal enveloping algebra, used for `LieHom.map_lie`.
attribute [local instance 100] LieRing.ofAssociativeRing



section Fock_space_Sugawara_construction

variable (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]

section auxiliary

variable {V : Type*} [AddCommGroup V] [Module (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) V]

open HeisenbergAlgebra in
private lemma commutator_lsmul_jgen_of_module_uea_heisenbergAlgebra
    (hc : ∀ (v : V), (ιUEA 𝕜 (kgen 𝕜)) • v = v) (k l : ℤ) :
    (ModuleOfModuleAlgebra.lsmul 𝕜 V (ιUEA 𝕜 (jgen 𝕜 k))).commutator
      (ModuleOfModuleAlgebra.lsmul 𝕜 V (ιUEA 𝕜 (jgen 𝕜 l)))
    = if k + l = 0 then (k : 𝕜) • 1 else 0 := by
  have key (w : V) :
      (ιUEA 𝕜 (jgen 𝕜 k)) • (ιUEA 𝕜 (jgen 𝕜 l)) • w - (ιUEA 𝕜 (jgen 𝕜 l)) • (ιUEA 𝕜 (jgen 𝕜 k)) • w
        = if k + l = 0 then ↑k • w else 0 := by
    have key := congr_arg (fun b ↦ b • w) <| (ιUEA 𝕜).map_lie (jgen 𝕜 k) (jgen 𝕜 l)
    rw [lie_jgen 𝕜 k l] at key
    by_cases hkl : k + l = 0
    · simp only [hkl, ↓reduceIte, map_smul] at key ⊢
      convert key.symm using 1
      · simp_rw [← smul_assoc, ← sub_smul]
        rfl
      · have same :
            k • w = (algebraMap 𝕜 (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) ↑k • ιUEA 𝕜 (kgen 𝕜)) • w := by
          rw [smul_assoc, hc]
          simpa [map_intCast] using (Int.cast_smul_eq_zsmul (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) k w).symm
        exact same
    · simp only [hkl, ↓reduceIte, map_zero, zero_smul] at key ⊢
      simp_rw [← smul_assoc, ← sub_smul]
      rw [show (ιUEA 𝕜) (jgen 𝕜 k) • (ιUEA 𝕜) (jgen 𝕜 l)
              - (ιUEA 𝕜) (jgen 𝕜 l) • (ιUEA 𝕜) (jgen 𝕜 k)
            = ⁅(ιUEA 𝕜) (jgen 𝕜 k), (ιUEA 𝕜) (jgen 𝕜 l)⁆ by
          rw [Ring.lie_def, smul_eq_mul, smul_eq_mul]]
      exact key.symm
  ext v
  convert key v using 1
  all_goals
    first
      | rfl
      | (rw [apply_ite (f := fun A : ModuleOfModuleAlgebra 𝕜 _ V →ₗ[𝕜]
              ModuleOfModuleAlgebra 𝕜 _ V ↦ A v)]
         by_cases hkl : k + l = 0
         · simp only [hkl, ↓reduceIte, LinearMap.smul_apply, Module.End.one_apply,
             Int.cast_smul_eq_zsmul]
           rfl
         · simp only [hkl, ↓reduceIte, LinearMap.zero_apply]
           rfl)

open HeisenbergAlgebra Filter in
-- TODO: Generalize to `kgen` acting as `κ • 1`, maybe.
/-- **The basic bosonic Sugawara representation of Virasoro algebra (c=1)**:
On a module over the universal enveloping algebra of the Heisenberg algebra in which the Heisenberg
algebra acts locally truncatedly (and the central element `k` acts as `1`), we get a representation
of the Virasoro algebra with central charge `c = 1` by the Sugawara construction. -/
noncomputable def sugawaraRepresentationOfModuleUeaHeisenbergAlgebra
    (htrunc : ∀ (v : V), ∀ᶠ (k : ℤ) in atTop, ιUEA 𝕜 (jgen 𝕜 k) • v = 0)
    (hc : ∀ (v : V), (ιUEA 𝕜 (kgen 𝕜)) • v = v) :
    LieAlgebra.Representation 𝕜 𝕜 (VirasoroAlgebra 𝕜)
      (ModuleOfModuleAlgebra 𝕜 (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) V) :=
  let heiOper (k : ℤ) :
      ModuleOfModuleAlgebra 𝕜 (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) V
        →ₗ[𝕜] ModuleOfModuleAlgebra 𝕜 (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) V :=
    ModuleOfModuleAlgebra.lsmul 𝕜 V (ιUEA 𝕜 (jgen 𝕜 k))
  sugawaraRepresentation (heiOper := heiOper)
    (fun v ↦ htrunc ((ModuleOfModuleAlgebra.unMkAddHom 𝕜 (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) V) v))
    (commutator_lsmul_jgen_of_module_uea_heisenbergAlgebra 𝕜 hc)

open HeisenbergAlgebra Filter in
lemma sugawaraRepresentation_of_module_uea_heisenbergAlgebra_lgen_apply
    (htrunc : ∀ (v : V), ∀ᶠ (k : ℤ) in atTop, ιUEA 𝕜 (jgen 𝕜 k) • v = 0)
    (hc : ∀ (v : V), ιUEA 𝕜 (kgen 𝕜) • v = v)
    (n : ℤ) (v : ModuleOfModuleAlgebra 𝕜 (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) V) :
    sugawaraRepresentationOfModuleUeaHeisenbergAlgebra 𝕜 htrunc hc (.lgen 𝕜 n) v =
      (2 : 𝕜)⁻¹ • ModuleOfModuleAlgebra.mkAddHom 𝕜 (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) V (
          ((∑ᶠ k ≥ 0, ιUEA 𝕜 (jgen 𝕜 (n-k)) • ιUEA 𝕜 (jgen 𝕜 k)
                      • ModuleOfModuleAlgebra.unMkAddHom 𝕜 _ V v)
          + (∑ᶠ k < 0, ιUEA 𝕜 (jgen 𝕜 k) • ιUEA 𝕜 (jgen 𝕜 (n-k))
                      • ModuleOfModuleAlgebra.unMkAddHom 𝕜 _ V v))) := by
  apply sugawaraRepresentation_lgen_apply _
    ((fun v ↦ htrunc ((ModuleOfModuleAlgebra.unMkAddHom 𝕜 (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) V) v)))
    (commutator_lsmul_jgen_of_module_uea_heisenbergAlgebra 𝕜 hc)

open HeisenbergAlgebra Filter in
lemma sugawaraRepresentation_of_module_uea_heisenbergAlgebra_cgen_apply
    (htrunc : ∀ (v : V), ∀ᶠ (k : ℤ) in atTop, ιUEA 𝕜 (jgen 𝕜 k) • v = 0)
    (hc : ∀ (v : V), ιUEA 𝕜 (kgen 𝕜) • v = v)
    (v : ModuleOfModuleAlgebra 𝕜 (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) V) :
    sugawaraRepresentationOfModuleUeaHeisenbergAlgebra 𝕜 htrunc hc (.cgen 𝕜) v = v := by
  have key := sugawaraRepresentation_cgen _
    ((fun v ↦ htrunc ((ModuleOfModuleAlgebra.unMkAddHom 𝕜 (𝓤 𝕜 (HeisenbergAlgebra 𝕜)) V) v)))
    (commutator_lsmul_jgen_of_module_uea_heisenbergAlgebra 𝕜 hc)
  simpa [sugawaraRepresentationOfModuleUeaHeisenbergAlgebra] using congr_arg (fun A ↦ A v) key

end auxiliary


namespace ChargedFockSpace

/-- **Virasoro algebra representation on Fock space by basic bosonic Sugawara construction (c=1)**:
-/
noncomputable def _root_.VirasoroProject.ChargedFockSpace.sugawaraRepresentation (α : 𝕜) :
    LieAlgebra.Representation 𝕜 𝕜 (VirasoroAlgebra 𝕜) (ChargedFockSpace 𝕜 α) :=
  sugawaraRepresentationOfModuleUeaHeisenbergAlgebra 𝕜 (V := ChargedFockSpace 𝕜 α)
      (fun _ ↦ eventually_jgen_smul_eq_zero ..) (fun _ ↦ ChargedFockSpace.kgen_smul ..)

open HeisenbergAlgebra in
/-- The formula for the action of the Virasoro generators in the (basic) Sugawara
representation on the charged Fock space. -/
lemma _root_.VirasoroProject.ChargedFockSpace.sugawaraRepresentation_lgen_apply
    (α : 𝕜) (n : ℤ) (v : ChargedFockSpace 𝕜 α) :
    ChargedFockSpace.sugawaraRepresentation 𝕜 α (.lgen 𝕜 n) v =
      (2 : 𝕜)⁻¹
        • ((∑ᶠ k ≥ 0, ιUEA 𝕜 (jgen 𝕜 (n-k)) • ιUEA 𝕜 (jgen 𝕜 k) • v)
          + (∑ᶠ k < 0, ιUEA 𝕜 (jgen 𝕜 k) • ιUEA 𝕜 (jgen 𝕜 (n-k)) • v)) := by
  apply sugawaraRepresentation_of_module_uea_heisenbergAlgebra_lgen_apply

open HeisenbergAlgebra in
lemma _root_.VirasoroProject.ChargedFockSpace.sugawaraRepresentation_lgen_apply_vacuum
    (α : 𝕜) (n : ℤ) :
    ChargedFockSpace.sugawaraRepresentation 𝕜 α (.lgen 𝕜 n) (vacuum 𝕜 α) =
      (2 : 𝕜)⁻¹
        • ((ιUEA 𝕜 (jgen 𝕜 n) • ιUEA 𝕜 (jgen 𝕜 0) • (vacuum 𝕜 α))
          + (∑ᶠ k < 0, ιUEA 𝕜 (jgen 𝕜 k) • ιUEA 𝕜 (jgen 𝕜 (n-k)) • (vacuum 𝕜 α))) := by
  simp only [sugawaraRepresentation_lgen_apply, ge_iff_le]
  congr 1
  simp only [add_left_inj]
  convert @finsum_eq_single (ChargedFockSpace 𝕜 α) ℤ _ _ 0 ?_
  · simp
  · intro k k_ne_zero
    by_cases k_nn : 0 ≤ k
    · simp only [k_nn, finsum_true]
      rw [jgen_pos_vacuum 𝕜 α (show 0 < k by grind), smul_zero]
    · simp [k_nn]

open HeisenbergAlgebra in
lemma _root_.VirasoroProject.ChargedFockSpace.sugawaraRepresentation_lgen_nonneg_apply_vacuum
    (α : 𝕜) {n : ℤ} (n_nn : 0 ≤ n) :
    ChargedFockSpace.sugawaraRepresentation 𝕜 α (.lgen 𝕜 n) (vacuum 𝕜 α) =
      (2 : 𝕜)⁻¹ • ιUEA 𝕜 (jgen 𝕜 n) • ιUEA 𝕜 (jgen 𝕜 0) • (vacuum 𝕜 α) := by
  simp only [sugawaraRepresentation_lgen_apply_vacuum, smul_add]
  convert add_zero ..
  convert smul_zero ..
  · convert finsum_zero with k
    by_cases k_neg : k < 0
    · simp only [k_neg, finsum_true]
      rw [jgen_pos_vacuum 𝕜 α (show 0 < n - k by linarith), smul_zero]
    · simp [k_neg]

/-- The vacuum in the Fock space of charge α has L₀-eigenvalue α²/2. -/
lemma _root_.VirasoroProject.ChargedFockSpace.sugawaraRepresentation_lgen_zero_apply_vacuum
    (α : 𝕜) :
    sugawaraRepresentation 𝕜 α (.lgen 𝕜 0) (vacuum 𝕜 α) =
      (α^2 / 2) • (vacuum 𝕜 α) := by
  rw [sugawaraRepresentation_lgen_nonneg_apply_vacuum 𝕜 α le_rfl]
  simp only [jgen_zero_smul, ← smul_assoc, smul_eq_mul]
  grind

/-- The vacuum in the Fock space of charge α is annihilated by Lₙ for n > 0. -/
lemma _root_.VirasoroProject.ChargedFockSpace.sugawaraRepresentation_lgen_pos_apply_vacuum (α : 𝕜)
    {n : ℤ} (n_pos : 0 < n) :
    sugawaraRepresentation 𝕜 α (.lgen 𝕜 n) (vacuum 𝕜 α) = 0 := by
  rw [sugawaraRepresentation_lgen_nonneg_apply_vacuum 𝕜 α n_pos.le]
  convert smul_zero ..
  simp only [jgen_zero_smul]
  rw [smul_comm, jgen_pos_vacuum 𝕜 α n_pos, smul_zero]

/-- The central element of the Virasoro algebra acts as the identity on the charged Fock space. -/
@[simp] lemma _root_.VirasoroProject.ChargedFockSpace.sugawaraRepresentation_cgen_apply
    (α : 𝕜) (v : ChargedFockSpace 𝕜 α) :
    sugawaraRepresentation 𝕜 α (.cgen 𝕜) v = v := by
  change (sugawaraRepresentationOfModuleUeaHeisenbergAlgebra 𝕜
    (fun x ↦ eventually_jgen_smul_eq_zero 𝕜 α x)
    (fun x ↦ ChargedFockSpace.kgen_smul 𝕜 α x) (.cgen 𝕜)) v = v
  simpa using sugawaraRepresentation_of_module_uea_heisenbergAlgebra_cgen_apply ..

noncomputable instance _root_.VirasoroProject.ChargedFockSpace.instModuleUEAVirasoroAlgebra
    (α : 𝕜) :
    Module (𝓤 𝕜 (VirasoroAlgebra 𝕜)) (ChargedFockSpace 𝕜 α) :=
  LieAlgebra.Representation.moduleUniversalEnvelopingAlgebra (sugawaraRepresentation 𝕜 α)

@[simp] lemma _root_.VirasoroProject.ChargedFockSpace.sugawaraRepresentation_smul_eq {α : 𝕜}
    (a : 𝓤 𝕜 (VirasoroAlgebra 𝕜)) (v : ChargedFockSpace 𝕜 α) :
    a • v = UniversalEnvelopingAlgebra.lift 𝕜 (sugawaraRepresentation 𝕜 α) a v :=
  rfl

lemma _root_.VirasoroProject.ChargedFockSpace.sugawaraRepresentation_ιUEA_smul_eq {α : 𝕜}
    (X : VirasoroAlgebra 𝕜) (v : ChargedFockSpace 𝕜 α) :
    ιUEA 𝕜 X • v = (sugawaraRepresentation 𝕜 α) X v := by
  simp only [UniversalEnvelopingAlgebra.ι_apply, sugawaraRepresentation_smul_eq,
             UniversalEnvelopingAlgebra.lift_ι_apply']

instance (α : 𝕜) : HasCentralCharge 𝕜 (ChargedFockSpace 𝕜 α) (1 : 𝕜) where
  central_smul' v := by simp

lemma _root_.VirasoroProject.ChargedFockSpace.algebraMap_virasoro_smul_eq
    {α : 𝕜} (r : 𝕜) (v : ChargedFockSpace 𝕜 α) :
    algebraMap 𝕜 (𝓤 𝕜 (VirasoroAlgebra 𝕜)) r • v = r • v := by
  rw [Algebra.algebraMap_eq_smul_one r, sugawaraRepresentation_smul_eq]
  simp

/-- A Virasoro module map from the Verma module with `c = 1` and `h = α^2 / 2`
to the charged Fock space of charge `α`. -/
noncomputable def _root_.VirasoroProject.ChargedFockSpace.virasoroVermaToChargedFockSpace (α : 𝕜) :
    VirasoroVerma 𝕜 1 (α^2/2) →ₗ[𝓤 𝕜 (VirasoroAlgebra 𝕜)] ChargedFockSpace 𝕜 α :=
  VirasoroVerma.universalMap 𝕜 _ (hwv := vacuum 𝕜 α) (by simp)
    (by
      rw [sugawaraRepresentation_ιUEA_smul_eq, sugawaraRepresentation_lgen_zero_apply_vacuum]
      rw [algebraMap_virasoro_smul_eq])
    (by
      intro n n_pos
      simpa using sugawaraRepresentation_lgen_pos_apply_vacuum 𝕜 α n_pos)

theorem _root_.VirasoroProject.ChargedFockSpace.virasoroVermaToChargedFockSpace_hwVec (α : 𝕜) :
    virasoroVermaToChargedFockSpace 𝕜 α (.hwVec 𝕜 _ _) = vacuum 𝕜 α := by
  apply VirasoroVerma.universalMap_hwVec

end ChargedFockSpace

end Fock_space_Sugawara_construction

end VirasoroProject
