/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import LeanPool.ZetaZeros.Hilbert.Subspaces
public import LeanPool.ZetaZeros.Hilbert.Symmetry

/-!
# Symmetry on `L²`, as a real subspace

Pointwise symmetry cannot be carried into `L²` unchanged: elements of `Lp` are equivalence classes,
so the property must be stated almost everywhere. Doing so needs one genuinely new ingredient — an
a.e. statement has to be transportable through `u ↦ -u`, which holds because negation preserves
Lebesgue measure and `Ioo (-lam) lam` is reflection-invariant.

Once that is available the symmetric elements form an **ℝ**-subspace. Not a `ℂ`-one: multiplying by
`i` sends `conj (f u) = f (-u)` to `conj (i · f u) = -i · conj (f u)`, which fails. That is exactly
the structure the Gram–Schmidt argument needs, since its coefficients are real by
`inner_symmetric_im_eq_zero` and so it never leaves the subspace.
-/

@[expose] public section

namespace ZetaZeros

open MeasureTheory

variable {lam : ℝ}

/-- An almost-everywhere statement on the symmetric interval survives reflection. Negation
preserves Lebesgue measure and `Ioo (-lam) lam` is reflection-invariant, so a null set is carried
to a null set. -/
theorem ae_restrict_Ioo_neg {P : ℝ → Prop}
    (h : ∀ᵐ u ∂(volume.restrict (Set.Ioo (-lam) lam)), P u) :
    ∀ᵐ u ∂(volume.restrict (Set.Ioo (-lam) lam)), P (-u) := by
  rw [ae_restrict_iff' measurableSet_Ioo] at h ⊢
  have hneg : MeasurePreserving (fun u : ℝ => -u) volume volume :=
    Measure.measurePreserving_neg volume
  filter_upwards [hneg.quasiMeasurePreserving.ae h] with u hu hmem
  refine hu ?_
  obtain ⟨h1, h2⟩ := hmem
  exact ⟨by linarith, by linarith⟩

/-- Almost-everywhere symmetry for an element of `L²`. -/
def IsSymmetricL2 (f : L2Interval lam) : Prop :=
  ∀ᵐ u ∂(volume.restrict (Set.Ioo (-lam) lam)), (starRingEnd ℂ) (f u) = f (-u)

/-- The symmetric elements form an `ℝ`-subspace of `L²`. -/
noncomputable def symmetricSubspace (lam : ℝ) : Submodule ℝ (L2Interval lam) where
  carrier := {f | IsSymmetricL2 f}
  zero_mem' := by
    have hz := Lp.coeFn_zero ℂ 2 (volume.restrict (Set.Ioo (-lam) lam))
    filter_upwards [hz, ae_restrict_Ioo_neg hz] with u h1 h2
    simp only [h1, h2, Pi.zero_apply, map_zero]
  add_mem' := by
    intro f g hf hg
    have hadd := Lp.coeFn_add f g
    filter_upwards [hf, hg, ae_restrict_Ioo_neg hf, ae_restrict_Ioo_neg hg,
      hadd, ae_restrict_Ioo_neg hadd] with u hf1 hg1 _ _ ha1 ha2
    simp only [ha1, ha2, Pi.add_apply, map_add, hf1, hg1]
  smul_mem' := by
    intro c f hf
    have hsmul := Lp.coeFn_smul c f
    filter_upwards [hf, ae_restrict_Ioo_neg hf, hsmul, ae_restrict_Ioo_neg hsmul]
      with u hf1 _ hs1 hs2
    simp only [hs1, hs2, Pi.smul_apply, RCLike.real_smul_eq_coe_mul, map_mul, hf1]
    simp

end ZetaZeros
