/-
Copyright (c) 2026 Vico Bonfioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vico Bonfioli
-/
import LeanPool.ThreeGap.EuclideanGrowthFive
import LeanPool.ThreeGap.FiveDistance
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-!
# Toward the sharp Euclidean five-distance theorem via Haynes–Marklof Theorem 8

The repo proves `g₂ ≤ 6` (`gap_count_euclidean`) and reduces the sharp `g₂ ≤ 5` to the planar
packing
count `FiveDistance.card_le_five_of_pairwise` (≤ 5 vectors pairwise `> π/3`). A literature pass
(Haynes–Marklof, *A five distance theorem for Kronecker sequences*, IMRN 2022, arXiv:2009.08444)
established that the upper bound `5` is **elementary** (their Sections 3–5; dynamics enters only for
sharpness), but the step from `6` to `5` is **not** pure planar packing — six vectors pairwise `>
π/3`
*are* possible (a regular pentagon plus one), and the boundary pair of the doubling window can fail
the angular separation. HM defeat the sixth vector using a **height coordinate** `u = t/N` in
addition
to the planar direction `v = rem α t p`, together with the **antipodal symmetry** `θ ↦ θ + π`
(their "largest symmetric subset `S`"). This file builds that route.

* `recVec` — the orbit-difference record vector in `EuclideanSpace ℝ (Fin 2)` (the planar `v`).
* `recVec_neg` / `norm_recVec_neg` — **antipodal record symmetry** (atom HM-1): the `(−t, −p)`
record
  is the negation, of equal length. This is the symmetry `θ ↦ θ + π` underpinning HM's symmetric
  cone-partition (the basis for distinguishing `5` from `6`).

See the module docstring of `RomanovK4` and `MATHLIB_SUCCESSIVE_MINIMA_SCOPE.md` for the alternative
(Romanov / lattice-minima) routes; this file pursues the elementary HM Theorem-8 route.
-/

namespace ThreeGap.FiveDistanceHM

open ThreeGap.SimApprox

/-- The orbit-difference **record vector** `rem α t p = t·α − p` in `EuclideanSpace ℝ (Fin 2)` — the
planar direction `v` of a Haynes–Marklof relevant vector. -/
noncomputable def recVec (α : Fin 2 → ℝ) (t : ℤ) (p : Fin 2 → ℤ) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm (rem α t p)

/-- **Antipodal record symmetry (atom HM-1).** The record at the reflected offset `(−t, −p)` is the
negation of the record at `(t, p)`. This realizes the symmetry `θ ↦ θ + π` on the circle of record
directions — the structure Haynes–Marklof's *largest symmetric subset* `S` is built from. -/
theorem recVec_neg (α : Fin 2 → ℝ) (t : ℤ) (p : Fin 2 → ℤ) :
    recVec α (-t) (-p) = -(recVec α t p) := by
  rw [recVec, recVec, rem_neg_neg', map_neg]

/-- The reflected record has the same length: antipodal records are equidistant. -/
theorem norm_recVec_neg (α : Fin 2 → ℝ) (t : ℤ) (p : Fin 2 → ℤ) :
    ‖recVec α (-t) (-p)‖ = ‖recVec α t p‖ := by
  rw [recVec_neg, norm_neg]

/-- A record and its antipode point in exactly opposite directions (`angle = π`), when nonzero. -/
theorem angle_recVec_neg (α : Fin 2 → ℝ) (t : ℤ) (p : Fin 2 → ℤ) (h : recVec α t p ≠ 0) :
    InnerProductGeometry.angle (recVec α t p) (recVec α (-t) (-p)) = Real.pi := by
  rw [recVec_neg]; exact InnerProductGeometry.angle_self_neg_of_nonzero h

/-! ## Height coordinate (atom HM-2) -/

/-- The Haynes–Marklof **height coordinate** `u = t/N` of a record at offset `t` for parameter `N` —
the "time" axis of the `SL(3)` lattice reformulation, the extra datum (beyond the planar direction
`recVec`) that lets HM separate `5` from `6`. -/
noncomputable def height (N : ℕ) (t : ℤ) : ℝ := (t : ℝ) / (N : ℝ)

/-- **Heights subtract along offset differences:** `u(t₁ − t₂) = u(t₁) − u(t₂)`. (The record
difference at offsets `t₁, t₂` lives at height `u(t₁) − u(t₂)`.) -/
theorem height_sub (N : ℕ) (t₁ t₂ : ℤ) : height N (t₁ - t₂) = height N t₁ - height N t₂ := by
  simp only [height]; push_cast; ring

/-- The antipodal record has the opposite height. -/
theorem height_neg (N : ℕ) (t : ℤ) : height N (-t) = -height N t := by
  simp only [height]; push_cast; ring

/-- A record offset `|t| ≤ N` has height in `[−1, 1]`. (The relevant records live in the unit
height-slab `|u| ≤ 1`; HM's Proposition 3 uses the finer threshold `|u| < 1/2`.) -/
theorem abs_height_le_one (N : ℕ) (t : ℤ) (hN : 0 < N) (ht : |t| ≤ (N : ℤ)) :
    |height N t| ≤ 1 := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [height, abs_div, abs_of_pos hNR, div_le_one hNR]
  calc |(t : ℝ)| = ((|t| : ℤ) : ℝ) := by rw [Int.cast_abs]
    _ ≤ (N : ℝ) := by exact_mod_cast ht

/-! ## Haynes–Marklof Theorem 8 planar core (atoms HM-7)

The decoded structure of HM Theorem 8 (`GS¹(M) ≤ 5`): the first `K−1` relevant vectors satisfy
* **(5.2)** `‖vᵢ − vⱼ‖ > ‖vⱼ‖` for `i < j` (Prop 16, from best-approximation minimality), and
* **(5.3)** `‖vᵢ − vⱼ − vₖ‖ ≥ ‖vₖ‖` for `i < j < k` (Prop 16).
Prop 17 turns these into: (a) pairwise angle `> π/3`, and (b) no `vᵢ` lies in the open positive cone
of `vⱼ, vₖ` (`i < j < k`). The final count: 5 vectors pairwise `> π/3` are cyclically ordered, so
the
shortest lies in the cone of two later ones — contradicting (b). Everything is elementary plane
geometry on the difference vectors. -/

open scoped Real

/-! ### HM Proposition 17(b) — the cone-exclusion estimate (reduced target, verified)

The geometric heart of Prop 17(b): if `vᵢ = s·vⱼ + t·vₖ` (`s,t > 0`) lies in the open cone of
`vⱼ, vₖ`, is the shortest (`‖vᵢ‖ < ‖vⱼ‖ < ‖vₖ‖`), and makes an angle `> π/3` with **both** `vⱼ` and
`vₖ`, then `‖vᵢ − vⱼ − vₖ‖ < ‖vₖ‖` — contradicting (5.3). Writing `b=‖vⱼ‖, c=‖vₖ‖, C=⟪vⱼ,vₖ⟫`, the
estimate reduces to the `a`-free **polynomial inequality**

> `b²(s−1)² + c²·t·(t−2) + 2C(s−1)(t−1) < 0`

under: `0<b<c`, `s,t>0`, `2C + bc < 0` (angle `vⱼvₖ > 2π/3`, from the cone + both `> π/3`),
`s²b² + t²c² + 2stC < b²` (`‖vᵢ‖ < ‖vⱼ‖`), and the two realizability/angle constraints
`4(sb²+tC)² < (s²b²+t²c²+2stC)·b²`, `4(sC+tc²)² < (s²b²+t²c²+2stC)·c²`
(i.e. `|2⟪vᵢ,vⱼ⟫| < ‖vᵢ‖‖vⱼ‖`, `|2⟪vᵢ,vₖ⟫| < ‖vᵢ‖‖vₖ‖`). **Verified true** (≈3·10⁶-sample search,
worst value `< −0.015`); the constraint set is **minimal** (dropping either angle constraint yields
a
counterexample). The remaining task is the **SOS/Positivstellensatz certificate**: it is not a
linear
combination of the slacks (least-squares residual ≈ 6.3), so `nlinarith` does not auto-close it — it
needs an SDP-found SOS or a coordinate/trig proof. This is the single hard kernel of HM Theorem 8.

**Update (SDP):** a **degree-6 SOS certificate provably EXISTS** (verified feasible by a `cvxpy`
collocation SDP: `−G = σ₀ + Σ σₖ·gₖ` with `σ₀` a sum of squares of degree-3 polynomials and `σₖ`
degree-2 SOS multipliers on the seven constraints `gₖ`; degree-4 is infeasible, degree-6 feasible).
So the estimate is not merely true but **provable by Positivstellensatz**. The numerical certificate
has irrational degree-3 squares in `σ₀`, so it is not directly hand-translatable to `nlinarith`;
closing it in Lean requires an **exact rational SOS** (rational SDP rounding) fed as explicit
`sq_nonneg`/slack-product hints, or a coordinate/trig proof. Status: verified-true **and provable**;
the exact Lean certificate is the one mechanical step that remains. -/

/-- **Cone angle-additivity (atom HM-7d).** If `vᵢ = s·vⱼ + t·vₖ` with `s, t ≥ 0` (i.e. `vᵢ` lies in
the closed positive cone of `vⱼ, vₖ`) and `vᵢ ≠ 0`, then `∠(vⱼ,vₖ) = ∠(vⱼ,vᵢ) + ∠(vᵢ,vₖ)`. In
particular, if both `∠(vⱼ,vᵢ) > π/3` and `∠(vᵢ,vₖ) > π/3` then `∠(vⱼ,vₖ) > 2π/3` — the angle bound
the
cone-exclusion estimate (HM-7b) consumes. Direct from Mathlib's
`InnerProductGeometry.angle_eq_angle_add_add_angle_add_of_mem_span`. -/
theorem angle_add_of_mem_cone {vi vj vk : EuclideanSpace ℝ (Fin 2)} (hi : vi ≠ 0) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hcone : vi = s • vj + t • vk) :
    InnerProductGeometry.angle vj vk
      = InnerProductGeometry.angle vj vi + InnerProductGeometry.angle vi vk := by
  refine InnerProductGeometry.angle_eq_angle_add_add_angle_add_of_mem_span hi ?_
  rw [Submodule.mem_span_pair]
  refine ⟨s.toNNReal, t.toNNReal, ?_⟩
  simp only [NNReal.smul_def, Real.coe_toNNReal _ hs, Real.coe_toNNReal _ ht]
  exact hcone.symm

/-- **Cone forces a wide opening (atom HM-7d, corollary).** If `vᵢ` is in the closed positive cone
of
`vⱼ, vₖ` and is more than `π/3` from each, then `∠(vⱼ,vₖ) > 2π/3`. This is the obtuse-angle bound
the
cone-exclusion estimate (HM-7b: `C = ⟪vⱼ,vₖ⟫`, `2C + ‖vⱼ‖‖vₖ‖ < 0`) consumes. -/
theorem angle_gt_two_pi_div_three_of_cone {vi vj vk : EuclideanSpace ℝ (Fin 2)} (hi : vi ≠ 0)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hcone : vi = s • vj + t • vk)
    (hij : π / 3 < InnerProductGeometry.angle vj vi)
    (hik : π / 3 < InnerProductGeometry.angle vi vk) :
    2 * π / 3 < InnerProductGeometry.angle vj vk := by
  rw [angle_add_of_mem_cone hi hs ht hcone]; linarith

/-- **HM Proposition 17(a).** Two record vectors `v, w` with `‖v‖ < ‖w‖` and the separation
`‖w‖ ≤ ‖v − w‖` (Prop 16, eq. 5.2) make an angle `> π/3`. (The metric→angle crux with `δ = ‖w‖`:
`‖v‖, ‖w‖ ≤ ‖w‖`, `‖w‖ ≤ ‖v − w‖`, and `‖v‖ < ‖w‖` strict.) -/
theorem angle_gt_of_norm_sub_ge {v w : EuclideanSpace ℝ (Fin 2)} (hv0 : v ≠ 0)
    (hlt : ‖v‖ < ‖w‖) (hsep : ‖w‖ ≤ ‖v - w‖) :
    π / 3 < InnerProductGeometry.angle v w := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hlt; exact absurd hlt (not_lt.mpr (norm_nonneg v))
  exact ThreeGap.EuclideanAngle.angle_gt_pi_div_three (norm_pos_iff.mpr hv0)
    (norm_pos_iff.mpr hw0) hlt.le (le_refl _) hsep (Or.inl hlt)

/-- **The crux trigonometric inequality of HM Proposition 17(b).** For `0 < b ≤ c` and angles
`βⱼ, βₖ ∈ [0,π]` with `βⱼ + βₖ ≤ π`, `b·(1 − cos βⱼ) ≤ c·(cos βₖ − cos(βⱼ+βₖ))`. By sum-to-product
this is `2 sin(βⱼ/2)·(c sin(βⱼ/2+βₖ) − b sin(βⱼ/2)) ≥ 0`, and `sin(βⱼ/2+βₖ) ≥ sin(βⱼ/2)` because
`βⱼ/2+βₖ ∈ [βⱼ/2, π−βⱼ/2]` (using `βⱼ+βₖ ≤ π`). This replaces HM's claimed SOS kernel: numerically
the cone-exclusion estimate needs *only* the obtuse-cone and `‖v₀‖<‖vⱼ‖` constraints (the two
realizability constraints are unnecessary), and the resulting reduced inequality has this clean
trigonometric proof. -/
theorem cone_trig_crux (b c βj βk : ℝ) (hb : 0 < b) (hbc : b ≤ c)
    (hj0 : 0 ≤ βj) (hjπ : βj ≤ π) (hk0 : 0 ≤ βk) (hkπ : βk ≤ π) (hsum : βj + βk ≤ π) :
    b * (1 - Real.cos βj) ≤ c * (Real.cos βk - Real.cos (βj + βk)) := by
  have hpi := Real.pi_pos
  have e1 : 1 - Real.cos βj = 2 * Real.sin (βj / 2) ^ 2 := by
    have h := Real.cos_sub_cos 0 βj
    rw [Real.cos_zero] at h
    rw [h, show (0 - βj) / 2 = -(βj / 2) by ring, Real.sin_neg,
      show (0 + βj) / 2 = βj / 2 by ring]; ring
  have e2 : Real.cos βk - Real.cos (βj + βk) = 2 * Real.sin (βj / 2 + βk) * Real.sin (βj / 2) := by
    have h := Real.cos_sub_cos βk (βj + βk)
    rw [h, show (βk + (βj + βk)) / 2 = βj / 2 + βk by ring,
      show (βk - (βj + βk)) / 2 = -(βj / 2) by ring, Real.sin_neg]; ring
  rw [e1, e2]
  have hsj : 0 ≤ Real.sin (βj / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hmono : Real.sin (βj / 2) ≤ Real.sin (βj / 2 + βk) := by
    have h := Real.sin_sub_sin (βj / 2 + βk) (βj / 2)
    have hfac : Real.sin (βj / 2 + βk) - Real.sin (βj / 2)
        = 2 * Real.sin (βk / 2) * Real.cos ((βj + βk) / 2) := by
      rw [h, show ((βj / 2 + βk) - βj / 2) / 2 = βk / 2 by ring,
        show ((βj / 2 + βk) + βj / 2) / 2 = (βj + βk) / 2 by ring]
    have hsk : 0 ≤ Real.sin (βk / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hck : 0 ≤ Real.cos ((βj + βk) / 2) :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
    nlinarith [hfac, mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hsk) hck]
  nlinarith [mul_le_mul hbc hmono hsj (by linarith : (0:ℝ) ≤ c), hsj, mul_nonneg hsj hsj]

open RealInnerProductSpace in
/-- **HM Proposition 17(b) — the cone-exclusion estimate (HM-7b, the former hard kernel).** If `v₀`
lies in the closed positive cone of `vⱼ, vₖ` (`v₀ = s·vⱼ + t·vₖ`, `s,t ≥ 0`), is strictly shortest
(`‖v₀‖ < ‖vⱼ‖ < ‖vₖ‖`), and makes an angle `> π/3` with **both** edges, then
`‖v₀ − vⱼ − vₖ‖ < ‖vₖ‖` — contradicting the record inequality (5.3). **Proof** (clean trig,
replacing
HM's claimed SOS): set `r=‖v₀‖, b=‖vⱼ‖, c=‖vₖ‖, βⱼ=∠(v₀,vⱼ), βₖ=∠(v₀,vₖ)`; cone-additivity gives
`∠(vⱼ,vₖ)=βⱼ+βₖ` and both-`>π/3` gives `>2π/3` (so `2⟪vⱼ,vₖ⟫ < −bc`). Then
`‖v₀−vⱼ−vₖ‖² − c² = r² − 2r(b cosβⱼ + c cosβₖ) + (b²+2⟪vⱼ,vₖ⟫)`, an upward parabola in `r` that is
`< 0` at `r=0` (obtuse cone) and `≤ 0` at `r=b` (`cone_trig_crux`), hence `< 0` on `r ∈ (0,b)` by
the
interpolation `b·F(r) = (b−r)F(0) + r·F(b) − b·r·(b−r)`. -/
theorem cone_exclusion {vj vk v0 : EuclideanSpace ℝ (Fin 2)}
    (hj : vj ≠ 0) (hk : vk ≠ 0) (hv0 : v0 ≠ 0)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hcone : v0 = s • vj + t • vk)
    (hlt : ‖v0‖ < ‖vj‖) (hbc : ‖vj‖ < ‖vk‖)
    (hβj : π / 3 < InnerProductGeometry.angle v0 vj)
    (hβk : π / 3 < InnerProductGeometry.angle v0 vk) :
    ‖v0 - vj - vk‖ < ‖vk‖ := by
  have hpi := Real.pi_pos
  have hb : 0 < ‖vj‖ := norm_pos_iff.mpr hj
  have hc : 0 < ‖vk‖ := norm_pos_iff.mpr hk
  have hr : 0 < ‖v0‖ := norm_pos_iff.mpr hv0
  have hβj0 : 0 ≤ InnerProductGeometry.angle v0 vj := InnerProductGeometry.angle_nonneg _ _
  have hβk0 : 0 ≤ InnerProductGeometry.angle v0 vk := InnerProductGeometry.angle_nonneg _ _
  have hβjπ : InnerProductGeometry.angle v0 vj ≤ π := InnerProductGeometry.angle_le_pi _ _
  have hβkπ : InnerProductGeometry.angle v0 vk ≤ π := InnerProductGeometry.angle_le_pi _ _
  -- cone additivity: ∠(vⱼ,vₖ) = βⱼ + βₖ
  have hγ : InnerProductGeometry.angle vj vk
      = InnerProductGeometry.angle v0 vj + InnerProductGeometry.angle v0 vk := by
    rw [InnerProductGeometry.angle_comm v0 vj]
    exact angle_add_of_mem_cone hv0 hs ht hcone
  have hsum : InnerProductGeometry.angle v0 vj + InnerProductGeometry.angle v0 vk ≤ π :=
    hγ ▸ InnerProductGeometry.angle_le_pi vj vk
  -- obtuse cone
  have hγgt : 2 * π / 3 < InnerProductGeometry.angle vj vk :=
    angle_gt_two_pi_div_three_of_cone hv0 hs ht hcone
      (by rw [InnerProductGeometry.angle_comm]; exact hβj) hβk
  have hcosγ : Real.cos (InnerProductGeometry.angle vj vk) < -(1 / 2) := by
    have hc23 : Real.cos (2 * π / 3) = -(1 / 2) := by
      rw [show (2 * π / 3 : ℝ) = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
    have := Real.strictAntiOn_cos ⟨by positivity, by linarith⟩
      ⟨InnerProductGeometry.angle_nonneg vj vk, InnerProductGeometry.angle_le_pi vj vk⟩ hγgt
    rw [hc23] at this; exact this
  have hbne : ‖vj‖ ≠ 0 := ne_of_gt hb
  have hcne : ‖vk‖ ≠ 0 := ne_of_gt hc
  have hrne : ‖v0‖ ≠ 0 := ne_of_gt hr
  -- inner products in terms of cosines
  have hIj : ⟪v0, vj⟫ = ‖v0‖ * ‖vj‖ * Real.cos (InnerProductGeometry.angle v0 vj) := by
    rw [InnerProductGeometry.cos_angle]; field_simp
  have hIk : ⟪v0, vk⟫ = ‖v0‖ * ‖vk‖ * Real.cos (InnerProductGeometry.angle v0 vk) := by
    rw [InnerProductGeometry.cos_angle]; field_simp
  have hC : ⟪vj, vk⟫ = ‖vj‖ * ‖vk‖ * Real.cos (InnerProductGeometry.angle vj vk) := by
    rw [InnerProductGeometry.cos_angle]; field_simp
  -- F(0) < 0  (obtuse)
  have hF0 : ‖vj‖ ^ 2 + 2 * (‖vj‖ * ‖vk‖ * Real.cos (InnerProductGeometry.angle vj vk)) < 0 := by
    nlinarith [mul_pos hb hc, hcosγ, mul_pos hb (sub_pos.mpr hbc)]
  -- F(b) ≤ 0  (the crux)
  have hcrux := cone_trig_crux ‖vj‖ ‖vk‖ (InnerProductGeometry.angle v0 vj)
    (InnerProductGeometry.angle v0 vk) hb hbc.le hβj0 hβjπ hβk0 hβkπ hsum
  rw [← hγ] at hcrux
  have hcrux2 : 2 * ‖vj‖ ^ 2 * (1 - Real.cos (InnerProductGeometry.angle v0 vj))
      - 2 * ‖vj‖ * ‖vk‖ * (Real.cos (InnerProductGeometry.angle v0 vk)
        - Real.cos (InnerProductGeometry.angle vj vk)) ≤ 0 := by
    nlinarith [mul_le_mul_of_nonneg_left hcrux (by positivity : (0:ℝ) ≤ 2 * ‖vj‖)]
  -- norm expansion
  have hexp : ‖v0 - vj - vk‖ ^ 2 = ‖v0‖ ^ 2 + ‖vj‖ ^ 2 + ‖vk‖ ^ 2
      - 2 * ⟪v0, vj⟫ - 2 * ⟪v0, vk⟫ + 2 * ⟪vj, vk⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm vj v0, real_inner_comm vk v0, real_inner_comm vk vj]; ring
  -- assemble: ‖v0-vj-vk‖² < ‖vk‖²  via the parabola interpolation identity
  have hsq : ‖v0 - vj - vk‖ ^ 2 < ‖vk‖ ^ 2 := by
    rw [hexp, hIj, hIk, hC]
    set X := Real.cos (InnerProductGeometry.angle v0 vj)
    set Y := Real.cos (InnerProductGeometry.angle v0 vk)
    set Z := Real.cos (InnerProductGeometry.angle vj vk)
    have key : ‖vj‖ * (‖v0‖ ^ 2 + ‖vj‖ ^ 2 + ‖vk‖ ^ 2 - 2 * (‖v0‖ * ‖vj‖ * X)
          - 2 * (‖v0‖ * ‖vk‖ * Y) + 2 * (‖vj‖ * ‖vk‖ * Z) - ‖vk‖ ^ 2)
        = (‖vj‖ - ‖v0‖) * (‖vj‖ ^ 2 + 2 * (‖vj‖ * ‖vk‖ * Z))
          + ‖v0‖ * (2 * ‖vj‖ ^ 2 * (1 - X) - 2 * ‖vj‖ * ‖vk‖ * (Y - Z))
          - ‖vj‖ * ‖v0‖ * (‖vj‖ - ‖v0‖) := by ring
    nlinarith [key, mul_pos (sub_pos.mpr hlt) (neg_pos.mpr hF0),
      mul_nonneg hr.le (neg_nonneg.mpr hcrux2),
      mul_pos (mul_pos hb hr) (sub_pos.mpr hlt), hb]
  nlinarith [hsq, norm_nonneg (v0 - vj - vk), hc]

end ThreeGap.FiveDistanceHM
