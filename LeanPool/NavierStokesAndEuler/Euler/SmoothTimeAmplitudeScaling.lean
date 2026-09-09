/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldRestriction
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldLinear
public import LeanPool.NavierStokesAndEuler.Euler.EulerTimeRescaling

@[expose] public section

/-! Actual smooth coefficient paths and their true time derivatives under
the Euler amplitude/time scaling. The time interval is shortened by the
same positive amplitude used to normalize the initial velocity. -/

noncomputable section

namespace EulerTimeRescaling

open Set ContinuousLinearMap EulerVolterraConvolution
open scoped ContDiff BoundedContinuousFunction

variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def coefficient (ε : ℝ) (hε : 0 < ε) (A : SmoothTimeField (Icc (0 : ℝ) 1) E V) :
    SmoothTimeField (Icc (0 : ℝ) ε) E V :=
  (A.compTime (timeMap ε hε)).map (ε⁻¹ • ContinuousLinearMap.id ℝ V)

def derivativeCoefficient (ε : ℝ) (hε : 0 < ε) (A : SmoothTimeField (Icc (0 : ℝ) 1) E V) :
    SmoothTimeField (Icc (0 : ℝ) ε) E V :=
  (A.compTime (timeMap ε hε)).map ((ε⁻¹)^2 • ContinuousLinearMap.id ℝ V)

theorem coefficient_time (ε : ℝ) (hε : 0 < ε)
    (A A₁ : SmoothTimeField (Icc (0 : ℝ) 1) E V)
    (h : SmoothTimeField.TimeDerivative 1 zero_le_one A A₁) :
    SmoothTimeField.TimeDerivative ε hε.le (coefficient ε hε A) (derivativeCoefficient ε hε A₁) :=
      by
  intro t x
  have hmap : MapsTo (fun s : ℝ => s/ε) (Icc (0 : ℝ) ε) (Icc (0 : ℝ) 1) := by
    intro s hs
    exact ⟨div_nonneg hs.1 hε.le,(div_le_one hε).mpr hs.2⟩
  have ho : HasDerivWithinAt (fun r => A.realField 1 zero_le_one r x)
      (A₁.field (timeMap ε hε t) x) (Icc (0 : ℝ) 1) ((t : ℝ)/ε) :=
    h (timeMap ε hε t) x
  have hi : HasDerivWithinAt (fun r : ℝ => r/ε) (1/ε) (Icc (0 : ℝ) ε) t := by
    simpa only [id_eq] using ((hasDerivAt_id (t : ℝ)).div_const ε).hasDerivWithinAt
  have hd := (ho.scomp (t : ℝ) hi hmap).const_smul ε⁻¹
  change HasDerivWithinAt
    (fun r => ε⁻¹ • A.realField 1 zero_le_one (r/ε) x)
    (ε⁻¹ • ((1/ε) • A₁.field (timeMap ε hε t) x)) (Icc (0 : ℝ) ε) t at hd
  simp only [one_div,smul_smul,← pow_two] at hd
  have he (r : ℝ) (hr : r ∈ Icc (0 : ℝ) ε) :
      (coefficient ε hε A).realField ε hε.le r x =
        ε⁻¹ • A.realField 1 zero_le_one (r/ε) x := by
    simp only [coefficient,SmoothTimeField.realField,extendPath,projIcc_of_mem hε.le hr,
      SmoothTimeField.map_apply,smul_apply,id_apply,SmoothTimeField.compTime_apply,
      projIcc_of_mem zero_le_one (hmap hr)]
    rfl
  exact hd.congr_of_mem he t.property

end EulerTimeRescaling
