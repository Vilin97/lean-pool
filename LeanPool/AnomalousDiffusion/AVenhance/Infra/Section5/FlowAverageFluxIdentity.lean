/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.Representation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.CutoffAverage
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.HmBaseFluxIdentity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.LocalFinite
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.CutoffConsequences
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.PiolaFlux

/-! The `K_m + s_{m-1}` flux (corrected form).

The identity `(K_m + s_{m-1})∇T = K_m GDot_m` fails for the `sMat`; instead the coefficient has the
    Piola form
`(K + s)∇T = Σ_l ξ̂_l [κ F_l + F_lᵀ (K - κ) F_l] ∇T` (`Kmat_add_sMat_mulVec_eq_piola`, from
`LeftJacobian.Kmat_add_sMatPlus_mulVec`; `sMat = sMatPlus` by `rfl`). -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5

open AVenhance Homogenization

variable {β : ℝ} (I : Ingredients β)
variable {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)

/-- The Piola form of the coarse flux, the corrected formulation (4). -/
theorem Kmat_add_sMat_mulVec_eq_piola
    (m : ℕ) (hm : 1 ≤ m) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) :
    (I.Kmat κ m t + I.sMat hΦ m κ t x).mulVec (spaceGrad (T t) x) =
      ∑' l : ℤ, I.hatXiML m l t • ((κ • I.flowGrad hΦ m l t x +
        (I.flowGrad hΦ m l t x).transpose * (I.Kmat κ m t - κ • 1) *
          I.flowGrad hΦ m l t x).mulVec (spaceGrad (T t) x)) :=
  LeftJacobian.Kmat_add_sMatPlus_mulVec I hΦ m hm κ t x T

end AVenhance.Infra.Section5

end
