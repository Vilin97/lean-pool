/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# Halo minimum-deviation geometry (textbook geometric optics)

A standalone, machine-checked formalization of the **minimum-deviation principle**
for a ray of light passing through an ice prism — the geometry behind the 22-degree
atmospheric halo (Greenler 1980, Tape 1994; fully public, textbook material).

## What is PROVED here (the deductive core)

For a prism of apex angle `A` and refractive index `n`, with Snell's law
`sin θᵢ = n · sin rᵢ` holding at each face and the two refraction angles summing to
the apex (`r₂ = A − r₁`), the total angular deviation of the ray is

  `dev n A r = arcsin (n · sin r) + arcsin (n · sin (A − r)) − A`.

We prove:

* `dev_value` — at the symmetric ray `r = A/2` the deviation equals
  `2 · arcsin (n · sin (A/2)) − A` (because `sin (A − A/2) = sin (A/2)`).
* `min_deviation_stationary` (THE CORE) — the deviation is **stationary** at the
  symmetric ray: `HasDerivAt (dev n A) 0 (A/2)`.  The proof is the clean symmetry
  argument: writing `g r = arcsin (n · sin r)`, we have `dev r = g r + g (A − r) − A`,
  so `dev' r = g' r − g' (A − r)`; at `r = A/2` both arguments coincide and the two
  derivative terms cancel.  No explicit value of `g'` is ever needed.
* `min_deviation_isLocalMin` (THE UPGRADE) — the symmetric ray is a genuine
  **local minimum** of the deviation, proved unconditionally from the geometry.
  The second derivative `dev''(A/2) = 2·g''(A/2)` is computed and shown to be
  strictly positive whenever `n > 1`, `sin (A/2) > 0`, and the ray refracts out
  (no total internal reflection).  This is exactly *why* the deviation bottoms out
  at the symmetric ray, and hence why the halo appears as a bright ring at the
  minimum-deviation angle.  The supporting facts are `Dg_hasDerivAt` (the
  derivative of the first-derivative function) and `secondDeriv_sym_pos`
  (`dev''(A/2) > 0`).
* `symmetric_ray_isLocalMin_of_secondDeriv` — the original conditional wrapper of
  the textbook second-derivative test (kept as a now-superseded helper): IF the
  deviation is convex at the symmetric ray (positive second derivative), THEN that
  stationary ray is a genuine local minimum.  `min_deviation_isLocalMin` discharges
  that convexity hypothesis from the geometry, so it no longer needs to be assumed.

## The IMPORTED WALL (named, NOT proved here)

The pure geometry above is what this module certifies.  The following are physical /
observational facts taken as given, NOT derived:

* that atmospheric ice crystals present **hexagonal 60-degree prism** geometry
  (apex `A = π/3`);
* the refractive index of ice `n ≈ 1.31` (empirical measurement);
* that light obeys **Snell's law** at each crystal face;
* that the ray actually **refracts out** of the second face — i.e. there is no total
  internal reflection.  This is exactly the hypothesis `-1 < n · sin r` and
  `n · sin r < 1` that `arcsin` differentiability requires, and we carry it as an
  explicit hypothesis rather than asserting it;
* that the **observed bright ring** of the halo forms at the deviation extremum
  (the ray pile-up where deviation is stationary — an observational/optical fact).

The method proves the geometry of minimum deviation.  That the sky *realizes* this
geometry as a visible halo is named, not proved.
-/

namespace Sundog.HaloGeometry

open Real

/-- Total angular deviation of a ray through a prism of apex angle `A` and
refractive index `n`, as a function of the first-face refraction angle `r`.
Snell's law at each face gives the incidence angles `arcsin (n · sin r)` and
`arcsin (n · sin (A − r))`; the geometric total deviation subtracts the apex `A`. -/
noncomputable def dev (n A r : ℝ) : ℝ :=
  Real.arcsin (n * Real.sin r) + Real.arcsin (n * Real.sin (A - r)) - A

/-- The single-face deviation contribution `g r = arcsin (n · sin r)`.  The full
deviation is `dev n A r = g r + g (A − r) − A`. -/
noncomputable def faceDev (n r : ℝ) : ℝ := Real.arcsin (n * Real.sin r)

/-- `dev` is `faceDev` at `r` plus `faceDev` at the reflected angle `A − r`,
minus the apex. -/
theorem dev_eq_faceDev (n A r : ℝ) :
    dev n A r = faceDev n r + faceDev n (A - r) - A := rfl

/-- **Deviation value at the symmetric ray.**  Since `sin (A − A/2) = sin (A/2)`,
the two face contributions coincide and the symmetric-ray deviation is
`2 · arcsin (n · sin (A/2)) − A` — the 22-degree halo radius for `A = π/3`,
`n ≈ 1.31`. -/
theorem dev_value (n A : ℝ) :
    dev n A (A / 2) = 2 * Real.arcsin (n * Real.sin (A / 2)) - A := by
  unfold dev
  have hsub : A - A / 2 = A / 2 := by ring
  rw [hsub]
  ring

/-- The derivative of the single-face contribution `g r = arcsin (n · sin r)`,
as a `HasDerivAt` fact, under the no-total-internal-reflection hypothesis
`n · sin r ≠ ±1` (the ray exits the face).  The derivative value is
`(1 / √(1 − (n · sin r)²)) * (n * cos r)` but its explicit form is never needed
downstream — only that `g` is differentiable with *some* derivative `Dg`. -/
theorem faceDev_hasDerivAt {n r : ℝ} (h₁ : n * Real.sin r ≠ -1)
    (h₂ : n * Real.sin r ≠ 1) :
    HasDerivAt (faceDev n)
      ((1 / Real.sqrt (1 - (n * Real.sin r) ^ 2)) * (n * Real.cos r)) r := by
  have hsin : HasDerivAt (fun r => n * Real.sin r) (n * Real.cos r) r :=
    (Real.hasDerivAt_sin r).const_mul n
  have harc :
      HasDerivAt Real.arcsin (1 / Real.sqrt (1 - (n * Real.sin r) ^ 2))
        (n * Real.sin r) :=
    Real.hasDerivAt_arcsin h₁ h₂
  exact harc.comp r hsin

/-- The first-derivative value of the single-face contribution,
`g'(r) = (1 / √(1 − (n · sin r)²)) · (n · cos r)`.  This is exactly the derivative
delivered by `faceDev_hasDerivAt`; naming it lets us differentiate it once more to
reach the second derivative. -/
noncomputable def faceDeriv (n r : ℝ) : ℝ :=
  (1 / Real.sqrt (1 - (n * Real.sin r) ^ 2)) * (n * Real.cos r)

/-- The second-derivative value of the single-face contribution, `g''(r)`, written
in the raw quotient-rule form produced by differentiating `faceDeriv`.  Its closed
form simplifies to `n · sin r · (n² − 1) · (1 − (n · sin r)²)^(−3/2)`, which is the
sign we exploit; the raw form is what `Dg_hasDerivAt` literally returns. -/
noncomputable def faceDeriv2 (n r : ℝ) : ℝ :=
  (-(1 / (2 * Real.sqrt (1 - (n * Real.sin r) ^ 2))
        * (-(2 * (n * Real.sin r) * (n * Real.cos r))))
      / Real.sqrt (1 - (n * Real.sin r) ^ 2) ^ 2) * (n * Real.cos r)
    + (1 / Real.sqrt (1 - (n * Real.sin r) ^ 2)) * (-(n * Real.sin r))

/-- The first-derivative function `g' = faceDeriv n` is itself differentiable
wherever the ray refracts out (`1 − (n · sin r)² > 0`), with derivative the
second-derivative value `faceDeriv2 n r`.  Pure quotient/chain rule: differentiate
`1 / √(1 − (n · sin r)²)` and `n · cos r` and combine with `HasDerivAt.mul`. -/
theorem Dg_hasDerivAt {n r : ℝ} (hpos : 0 < 1 - (n * Real.sin r) ^ 2) :
    HasDerivAt (faceDeriv n) (faceDeriv2 n r) r := by
  have hcos : HasDerivAt (fun r => n * Real.cos r) (-(n * Real.sin r)) r := by
    have := (Real.hasDerivAt_cos r).const_mul n
    simpa [mul_neg] using this
  have hsin : HasDerivAt (fun r => n * Real.sin r) (n * Real.cos r) r :=
    (Real.hasDerivAt_sin r).const_mul n
  have hsq : HasDerivAt (fun r => (n * Real.sin r) ^ 2)
      (2 * (n * Real.sin r) * (n * Real.cos r)) r := by
    have := hsin.fun_pow 2
    simpa [pow_one, mul_comm, mul_left_comm, mul_assoc] using this
  have hinner : HasDerivAt (fun r => 1 - (n * Real.sin r) ^ 2)
      (-(2 * (n * Real.sin r) * (n * Real.cos r))) r := by
    simpa using (hasDerivAt_const r (1 : ℝ)).fun_sub hsq
  have hne : (1 - (n * Real.sin r) ^ 2) ≠ 0 := ne_of_gt hpos
  have hsqrt : HasDerivAt (fun r => Real.sqrt (1 - (n * Real.sin r) ^ 2))
      (1 / (2 * Real.sqrt (1 - (n * Real.sin r) ^ 2))
        * (-(2 * (n * Real.sin r) * (n * Real.cos r)))) r := by
    have hs := (Real.hasDerivAt_sqrt hne).comp r hinner
    simpa only [Function.comp_def] using hs
  have hsqrtne : Real.sqrt (1 - (n * Real.sin r) ^ 2) ≠ 0 := by positivity
  have hinv : HasDerivAt (fun r => 1 / Real.sqrt (1 - (n * Real.sin r) ^ 2))
      (-(1 / (2 * Real.sqrt (1 - (n * Real.sin r) ^ 2))
            * (-(2 * (n * Real.sin r) * (n * Real.cos r))))
        / Real.sqrt (1 - (n * Real.sin r) ^ 2) ^ 2) r := by
    have := hsqrt.inv hsqrtne
    have hfun : (fun r => 1 / Real.sqrt (1 - (n * Real.sin r) ^ 2))
        = (fun r => (Real.sqrt (1 - (n * Real.sin r) ^ 2))⁻¹) := by
      funext r; rw [one_div]
    rw [hfun]
    exact this
  exact hinv.mul hcos

/-- **The single-face deviation is convex at a refracting ray** (`g''(r) > 0`).
Whenever `n > 1`, `sin r > 0`, and the ray refracts out (`1 − (n · sin r)² > 0`),
the raw quotient-rule value `faceDeriv2 n r` simplifies to
`n · sin r · (n² − 1) / (1 − (n · sin r)²)^(3/2)`, a product of strictly positive
factors.  This is the curvature fact behind minimum deviation. -/
theorem faceDeriv2_pos {n r : ℝ} (hn : 1 < n) (hsinpos : 0 < Real.sin r)
    (hpos : 0 < 1 - (n * Real.sin r) ^ 2) :
    0 < faceDeriv2 n r := by
  unfold faceDeriv2
  set s := n * Real.sin r with hs
  set c := n * Real.cos r with hc
  set q := Real.sqrt (1 - s ^ 2) with hq
  have hqpos : 0 < q := Real.sqrt_pos.mpr hpos
  have hq2 : q ^ 2 = 1 - s ^ 2 := Real.sq_sqrt (le_of_lt hpos)
  have hspos : 0 < s := by rw [hs]; positivity
  have hpyth : Real.sin r ^ 2 + Real.cos r ^ 2 = 1 := Real.sin_sq_add_cos_sq r
  have hc2 : c ^ 2 = n ^ 2 - s ^ 2 := by rw [hs, hc]; nlinarith [hpyth]
  have hn21 : 0 < n ^ 2 - 1 := by nlinarith
  have hkey :
      (-(1 / (2 * q) * (-(2 * s * c))) / q ^ 2) * c + (1 / q) * (-(s))
        = s * (c ^ 2 - q ^ 2) / q ^ 3 := by
    field_simp
    ring
  rw [hkey, hq2, hc2]
  have hsimp : s * ((n ^ 2 - s ^ 2) - (1 - s ^ 2)) = s * (n ^ 2 - 1) := by ring
  rw [hsimp]
  positivity

/-- **Minimum-deviation principle (THE DEDUCTIVE CORE).**

The angular deviation `dev n A` is **stationary at the symmetric ray** `r = A/2`:
its derivative there is `0`.

Hypotheses (the imported optical wall, named explicitly): the ray refracts out at
the symmetric ray, i.e. `n · sin (A/2) ≠ ±1` (no total internal reflection), so the
`arcsin` is differentiable there.

The proof is pure symmetry: `dev r = g r + g (A − r) − A` with `g = faceDev n`.
The first term contributes `Dg`, the reflected term `g (A − ·)` contributes `−Dg`
(chain rule, inner derivative `−1`), and at `r = A/2` both `Dg`'s are evaluated at
the SAME point `A/2`, so they cancel: `Dg + (−Dg) = 0`. -/
theorem min_deviation_stationary {n A : ℝ}
    (h₁ : n * Real.sin (A / 2) ≠ -1) (h₂ : n * Real.sin (A / 2) ≠ 1) :
    HasDerivAt (fun r => dev n A r) 0 (A / 2) := by
  -- abbreviation for the single-face derivative value at the symmetric point
  set Dg : ℝ := (1 / Real.sqrt (1 - (n * Real.sin (A / 2)) ^ 2)) * (n * Real.cos (A / 2))
    with hDg
  -- first face: g has derivative Dg at A/2
  have hface1 : HasDerivAt (faceDev n) Dg (A / 2) := faceDev_hasDerivAt h₁ h₂
  -- inner reflection map A - · has derivative -1 at A/2
  have hrefl : HasDerivAt (fun r : ℝ => A - r) (-1) (A / 2) :=
    ((hasDerivAt_id (A / 2)).const_sub A)
  -- the reflected point A - A/2 = A/2
  have hpt : A - A / 2 = A / 2 := by ring
  -- second face: g (A - ·) has derivative Dg * (-1) at A/2
  have hfacepre : HasDerivAt (faceDev n) Dg (A - A / 2) := by
    rw [hpt]; exact hface1
  have hface2 : HasDerivAt (fun r => faceDev n (A - r)) (Dg * (-1)) (A / 2) :=
    hfacepre.comp (A / 2) hrefl
  -- dev = (g r) + (g (A - r)) - A; combine and subtract the constant A
  have hsum :
      HasDerivAt (fun r => faceDev n r + faceDev n (A - r)) (Dg + Dg * (-1)) (A / 2) :=
    hface1.add hface2
  have hdev :
      HasDerivAt (fun r => faceDev n r + faceDev n (A - r) - A)
        (Dg + Dg * (-1)) (A / 2) := by
    simpa using hsum.sub_const A
  -- the derivative value collapses to 0
  have hzero : Dg + Dg * (-1) = 0 := by ring
  rw [hzero] at hdev
  -- rewrite the goal's `dev` to the faceDev form
  have hfun : (fun r => dev n A r) = (fun r => faceDev n r + faceDev n (A - r) - A) := by
    funext r; rfl
  rw [hfun]
  exact hdev

/-- **The deviation's first derivative, off the symmetric ray.**  At any refracting
angle `r` (no total internal reflection at *both* faces), the deviation is
differentiable with derivative `faceDeriv n r − faceDeriv n (A − r)` — the first face
contributes `g'(r)`, the reflected face contributes `−g'(A − r)` (chain rule, inner
derivative `−1`).  This is the function we differentiate once more to get `dev''`. -/
theorem dev_hasDerivAt_local {n A r : ℝ}
    (hr₁ : n * Real.sin r ≠ -1) (hr₂ : n * Real.sin r ≠ 1)
    (hAr₁ : n * Real.sin (A - r) ≠ -1) (hAr₂ : n * Real.sin (A - r) ≠ 1) :
    HasDerivAt (fun r => dev n A r) (faceDeriv n r - faceDeriv n (A - r)) r := by
  have hface1 : HasDerivAt (faceDev n) (faceDeriv n r) r := faceDev_hasDerivAt hr₁ hr₂
  have hrefl : HasDerivAt (fun r : ℝ => A - r) (-1) r := (hasDerivAt_id r).const_sub A
  have hfacepre : HasDerivAt (faceDev n) (faceDeriv n (A - r)) (A - r) :=
    faceDev_hasDerivAt hAr₁ hAr₂
  have hface2 : HasDerivAt (fun r => faceDev n (A - r)) (faceDeriv n (A - r) * (-1)) r :=
    hfacepre.comp r hrefl
  have hsum : HasDerivAt (fun r => faceDev n r + faceDev n (A - r))
      (faceDeriv n r + faceDeriv n (A - r) * (-1)) r := hface1.add hface2
  have hdev : HasDerivAt (fun r => faceDev n r + faceDev n (A - r) - A)
      (faceDeriv n r + faceDeriv n (A - r) * (-1)) r := by simpa using hsum.sub_const A
  have hval : faceDeriv n r + faceDeriv n (A - r) * (-1)
      = faceDeriv n r - faceDeriv n (A - r) := by ring
  rw [hval] at hdev
  have hfun : (fun r => dev n A r) = (fun r => faceDev n r + faceDev n (A - r) - A) := by
    funext r; rfl
  rw [hfun]; exact hdev

/-- **The second derivative at the symmetric ray is strictly positive**
(`dev''(A/2) = 2·g''(A/2) > 0`).  By symmetry `dev'(r) = g'(r) − g'(A − r)`, so
`dev''(A/2) = g''(A/2) + g''(A/2)`; each summand is `faceDeriv2 n (A/2) > 0` by
`faceDeriv2_pos`.  Hypotheses: `n > 1`, `sin (A/2) > 0`, and the ray refracts out
(`−1 < n·sin (A/2) < 1`). -/
theorem secondDeriv_sym_pos {n A : ℝ} (hn : 1 < n)
    (hsinpos : 0 < Real.sin (A / 2)) (hlt : n * Real.sin (A / 2) < 1)
    (hgt : -1 < n * Real.sin (A / 2)) :
    0 < deriv (deriv (fun r => dev n A r)) (A / 2) := by
  have hpos : 0 < 1 - (n * Real.sin (A / 2)) ^ 2 := by nlinarith
  have hAval : A - A / 2 = A / 2 := by ring
  -- no-TIR holds in a whole neighborhood of A/2 (open condition, by continuity)
  have hcontr : ContinuousAt (fun r => n * Real.sin r) (A / 2) := by fun_prop
  have hcontA : ContinuousAt (fun r => n * Real.sin (A - r)) (A / 2) := by fun_prop
  have e1 : ∀ᶠ r in nhds (A / 2), n * Real.sin r < 1 :=
    hcontr.eventually_lt continuousAt_const hlt
  have e2 : ∀ᶠ r in nhds (A / 2), (-1 : ℝ) < n * Real.sin r :=
    continuousAt_const.eventually_lt hcontr hgt
  have e3 : ∀ᶠ r in nhds (A / 2), n * Real.sin (A - r) < 1 := by
    have := hcontA.eventually_lt continuousAt_const (g := fun _ => (1 : ℝ))
      (by rw [hAval]; exact hlt)
    exact this
  have e4 : ∀ᶠ r in nhds (A / 2), (-1 : ℝ) < n * Real.sin (A - r) := by
    have := continuousAt_const.eventually_lt hcontA (f := fun _ => (-1 : ℝ))
      (by rw [hAval]; exact hgt)
    exact this
  -- hence deriv (dev n A) agrees with faceDeriv n r − faceDeriv n (A − r) near A/2
  have hEq : deriv (fun r => dev n A r)
      =ᶠ[nhds (A / 2)] (fun r => faceDeriv n r - faceDeriv n (A - r)) := by
    filter_upwards [e1, e2, e3, e4] with r h1 h2 h3 h4
    exact (dev_hasDerivAt_local (ne_of_lt h2).symm (ne_of_lt h1)
      (ne_of_lt h4).symm (ne_of_lt h3)).deriv
  -- differentiate that first-derivative function once more at A/2
  have hDg1 : HasDerivAt (faceDeriv n) (faceDeriv2 n (A / 2)) (A / 2) := Dg_hasDerivAt hpos
  have hrefl : HasDerivAt (fun r : ℝ => A - r) (-1) (A / 2) :=
    (hasDerivAt_id (A / 2)).const_sub A
  have hDgpre : HasDerivAt (faceDeriv n) (faceDeriv2 n (A / 2)) (A - A / 2) := by
    rw [hAval]; exact hDg1
  have hDg2 : HasDerivAt (fun r => faceDeriv n (A - r))
      (faceDeriv2 n (A / 2) * (-1)) (A / 2) := hDgpre.comp (A / 2) hrefl
  have hD : HasDerivAt (fun r => faceDeriv n r - faceDeriv n (A - r))
      (faceDeriv2 n (A / 2) - faceDeriv2 n (A / 2) * (-1)) (A / 2) := hDg1.sub hDg2
  have hsecond : deriv (deriv (fun r => dev n A r)) (A / 2)
      = faceDeriv2 n (A / 2) - faceDeriv2 n (A / 2) * (-1) := by
    rw [hEq.deriv_eq]; exact hD.deriv
  rw [hsecond]
  have hfp := faceDeriv2_pos hn hsinpos hpos
  nlinarith

/-- **The symmetric ray is the minimum-deviation ray (THE UPGRADE).**
The stationary symmetric ray `r = A/2` is a genuine **local minimum** of the
deviation, proved *unconditionally* from the geometry: the second derivative is
`dev''(A/2) = 2·g''(A/2) > 0` (`secondDeriv_sym_pos`), the first derivative vanishes
(`min_deviation_stationary`), and the deviation is continuous there.  Feeding all
three to the textbook second-derivative test gives the local minimum.

This is the formal "minimum deviation" statement: among rays through the prism, the
symmetric one deviates least, and that is why the halo is seen as a bright ring at
the minimum-deviation angle.  Hypotheses are the named optical wall only: `n > 1`
(denser ice), `sin (A/2) > 0` (`A/2 ∈ (0, π/2)`, real prism apex), and the ray
refracts out at the symmetric face (`−1 < n·sin (A/2) < 1`, no total internal
reflection). -/
theorem min_deviation_isLocalMin {n A : ℝ} (hn : 1 < n)
    (hsinpos : 0 < Real.sin (A / 2)) (hlt : n * Real.sin (A / 2) < 1)
    (hgt : -1 < n * Real.sin (A / 2)) :
    IsLocalMin (fun r => dev n A r) (A / 2) := by
  have hsecondpos : 0 < deriv (deriv (fun r => dev n A r)) (A / 2) :=
    secondDeriv_sym_pos hn hsinpos hlt hgt
  have hstat : deriv (fun r => dev n A r) (A / 2) = 0 :=
    (min_deviation_stationary (ne_of_lt hgt).symm (ne_of_lt hlt)).deriv
  have hcont : ContinuousAt (fun r => dev n A r) (A / 2) :=
    (min_deviation_stationary (ne_of_lt hgt).symm (ne_of_lt hlt)).continuousAt
  exact isLocalMin_of_deriv_deriv_pos hsecondpos hstat hcont

/-- **Conditional second-derivative test (now superseded by `min_deviation_isLocalMin`).**

Given (i) the stationarity already proved (`min_deviation_stationary`, supplied here
as `deriv (dev n A) (A/2) = 0`), (ii) the deviation is convex at the symmetric ray —
positive curvature `deriv (deriv (dev n A)) (A/2) > 0` — and (iii) continuity at the
point, the symmetric ray is a local minimum of the deviation.

This is the original wrapper that *assumed* the convexity hypothesis (ii).  That
hypothesis is now discharged unconditionally from the geometry in
`secondDeriv_sym_pos`, so `min_deviation_isLocalMin` proves the same conclusion with
no convexity assumption.  The wrapper is kept as a now-superseded helper. -/
theorem symmetric_ray_isLocalMin_of_secondDeriv {n A : ℝ}
    (hpos : deriv (deriv (fun r => dev n A r)) (A / 2) > 0)
    (hstat : deriv (fun r => dev n A r) (A / 2) = 0)
    (hcont : ContinuousAt (fun r => dev n A r) (A / 2)) :
    IsLocalMin (fun r => dev n A r) (A / 2) :=
  isLocalMin_of_deriv_deriv_pos hpos hstat hcont

end Sundog.HaloGeometry

-- Axiom audit: the deductive core depends only on mathlib's foundational axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) — NO `sorryAx`.
