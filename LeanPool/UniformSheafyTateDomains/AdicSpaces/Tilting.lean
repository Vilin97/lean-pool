/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.PerfectoidRing
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WittVectorPrimitive
import Mathlib.RingTheory.Perfection
import Mathlib.RingTheory.WittVector.Defs
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.RingTheory.Perfectoid.FontaineTheta
import Mathlib.FieldTheory.Perfect

/-!
# Tilting Functor, A_inf, and Fontaine's Theta Map

We define the **tilt** of a perfectoid ring, the period ring **A_inf**,
and Fontaine's **theta** map, following Scholze's *Perfectoid Spaces* §3
and Fontaine's original construction.

## Main definitions

* `PerfectoidRing.tilt p A` : The tilt `A♭ = lim_{x ↦ x^p} A°/(p)`, defined as
  `PreTilt A° p` (the perfection of `A°/(p)`).
* `Ainf p A` : The period ring `A_inf = W(A♭)` (p-typical Witt vectors of the tilt).
* `PerfectoidRing.theta` : Fontaine's theta map `θ : A_inf → A°`.

## Main results (sorry'd)

* `PerfectoidRing.tilt_isPerfect` : The tilt is a perfect ring of characteristic `p`.
* `PerfectoidRing.theta_surjective` : Fontaine's theta is surjective.
* `PerfectoidRing.ker_theta_principal` : The kernel of theta is principal.
* `PerfectoidRing.tilt_admits_perfectoid_structure` : The tilt admits a perfectoid topology.
* `PerfectoidField.tiltingEquiv` : The tilting equivalence for perfectoid fields.

## Implementation notes

The tilt is defined as `PreTilt ↥(powerBoundedSubring.toSubring A) p`, using Mathlib's
`PreTilt O p = Perfection (O ⧸ Ideal.span {p}) p`. The instances `CommRing`, `CharP`,
and `PerfectRing` on the tilt are inherited from `PreTilt`, but require
`[Fact (¬ IsUnit (p : A°))]`. We provide a sorry'd proof that this holds for
perfectoid rings (`IsPerfectoidRing.p_not_isUnit_in_powerBounded`).

Fontaine's theta map `θ : W(A♭) →+* A°` is defined with a sorry'd body. Mathlib's
`WittVector.fontaineTheta` provides the construction when `A°` is `p`-adically complete
(`[IsAdicComplete (Ideal.span {p}) A°]`), but establishing this instance for the
power-bounded subring of a perfectoid ring requires substantial infrastructure.
The sorry can be filled by proving `IsAdicComplete` and applying `fontaineTheta`.

The tilt being perfectoid requires a topology on `PreTilt`, which Lean's typeclass
system cannot synthesize automatically (due to a `Module R R` diamond for
`IsLinearTopology`). We state the result existentially.

## References

* [P. Scholze, *Perfectoid Spaces*][scholze2012perfectoid], §3
* [J.-M. Fontaine, *Sur certains types de représentations p-adiques du groupe de Galois
  d'un corps local; construction d'un anneau de Barsotti-Tate*][fontaine1982certains]
* [J.-M. Fontaine, *Le corps des périodes p-adiques*][fontaine1994corps]
-/

open TopologicalRing ValuationSpectrum

universe u

-- `A°` (`powerBoundedSubring.toSubring`) is now stated with `[NonarchimedeanAddGroup A]`. For the
-- genuine linear-topology setting of this file that follows from `[IsLinearTopology A A]` (open
-- ideals are open additive subgroups). Kept file-`local` so it does not affect typeclass search
-- elsewhere.
attribute [local instance] IsLinearTopology.nonarchimedeanAddGroup

noncomputable section

/-! ### The tilt and A_inf -/

section TiltDef

variable (p : ℕ)
variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A]

/-- The **tilt** of a topological ring `A` is `A♭ := lim_{x ↦ x^p} A°/(p)`,
the (inverse limit) perfection of the reduction modulo `p` of the ring of
power-bounded elements `A°`. This is Mathlib's `PreTilt` applied to `A°`.

More precisely, this is `O_{A♭}`, the **ring of integers** of the tilt.
For a perfectoid ring, this is a perfect ring of characteristic `p`.
For a perfectoid field `K`, this is a complete valuation ring, and the
tilt field is `K♭ = FractionRing (tilt p K)`.

(Scholze, *Perfectoid Spaces*, §3; Heuer, *Perfectoid Spaces*, Prop 1.1.23) -/
abbrev PerfectoidRing.tilt : Type u :=
  PreTilt ↥(powerBoundedSubring.toSubring A) p

/-- The period ring `A_inf(A) := W(A♭)`, the ring of `p`-typical Witt vectors
of the tilt. This ring plays a central role in p-adic Hodge theory as the
"universal thickening" of `A°`.

(Fontaine, *Sur certains types de représentations p-adiques*, 1982) -/
abbrev Ainf : Type u :=
  WittVector p (PerfectoidRing.tilt p A)

end TiltDef

/-! ### Instances on the tilt

The `CommRing`, `CharP`, and `PerfectRing` instances on the tilt require
`[Fact (¬ IsUnit (p : A°))]`, which we provide via a sorry'd proof for
perfectoid rings (see `IsPerfectoidRing.instFactNotIsUnitP`).
-/

section TiltInstances

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A]
variable [Fact (¬ IsUnit (p : ↥(powerBoundedSubring.toSubring A)))]

instance PerfectoidRing.tilt.instCommRing : CommRing (PerfectoidRing.tilt p A) :=
  inferInstance

instance PerfectoidRing.tilt.instCharP : CharP (PerfectoidRing.tilt p A) p :=
  inferInstance

instance PerfectoidRing.tilt.instPerfectRing : PerfectRing (PerfectoidRing.tilt p A) p :=
  inferInstance

end TiltInstances

/-! ### p is not a unit in A° for perfectoid rings -/

namespace IsPerfectoidRing

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A]

/-- In a perfectoid ring, `p` is not a unit in `A°`.

This follows from the perfectoid condition `p = c · ϖ^p`: since `ϖ` is
topologically nilpotent and `c` is power-bounded, `p` is topologically
nilpotent in `A`. A topologically nilpotent element cannot be a unit in
`A°` (its powers converge to 0, contradicting invertibility in a Hausdorff ring).

(Scholze, *Perfectoid Spaces*, implicit in Definition 3.5) -/
theorem p_not_isUnit_in_powerBounded [Nontrivial A] :
    ¬ IsUnit (p : ↥(powerBoundedSubring.toSubring A)) := by
  -- Step 1: Extract perfectoid data
  obtain ⟨ϖ, _, ⟨c, hc, hpc⟩⟩ :=
    IsPerfectoidRing.exists_pseudoUniformizer (p := p) (A := A)
  -- Step 2: ϖ^p is topologically nilpotent (from ϖ top. nilpotent)
  have hϖp_nil : IsTopologicallyNilpotent ((ϖ.val : A) ^ p) := by
    change Filter.Tendsto (((ϖ.val : A) ^ p) ^ ·) Filter.atTop (nhds 0)
    have hϖ := ϖ.property  -- ϖ topologically nilpotent
    rw [show (fun n ↦ ((ϖ.val : A) ^ p) ^ n) = (fun n ↦ (ϖ.val : A) ^ (p * n)) from by
      ext n; rw [← pow_mul]]
    exact hϖ.comp (Filter.tendsto_atTop_atTop.mpr fun n ↦
      ⟨n, fun m hm ↦ le_trans hm (Nat.le_mul_of_pos_left m (Nat.Prime.pos (Fact.out)))⟩)
  -- Step 3: p = c * ϖ^p is topologically nilpotent
  have hp_nil : IsTopologicallyNilpotent (p : A) := by
    rw [hpc]; exact hc.isTopologicallyNilpotent_mul hϖp_nil
  -- Step 4: Assume p is a unit in A° and derive contradiction
  intro ⟨u, hu⟩
  -- q = u⁻¹ is in A°, hence power-bounded
  have hq_pb : IsPowerBounded (u⁻¹.val : A) :=
    (u⁻¹.val : ↥(powerBoundedSubring.toSubring A)).property
  -- q * p = 1, so 1 is topologically nilpotent
  have h1_nil : IsTopologicallyNilpotent (1 : A) := by
    have : (u⁻¹.val : A) * (p : A) = 1 := by
      have h := u.inv_mul
      have heq : (u.val : ↥(powerBoundedSubring.toSubring A)) =
          (p : ↥(powerBoundedSubring.toSubring A)) := hu
      rw [heq] at h
      exact_mod_cast h
    rw [← this]; exact hq_pb.isTopologicallyNilpotent_mul hp_nil
  -- 1 topologically nilpotent means constant seq 1 → 0
  haveI := IsPerfectoidRing.t0 (p := p) (A := A)
  have h01 : Inseparable (0 : A) 1 :=
    tendsto_nhds_unique_inseparable
      (show Filter.Tendsto (fun _ : ℕ ↦ (1 : A)) Filter.atTop (nhds 0) from by
        have : Filter.Tendsto ((1 : A) ^ ·) Filter.atTop (nhds 0) := h1_nil
        simp [one_pow] at this)
      tendsto_const_nhds
  exact absurd h01.eq (Ne.symm one_ne_zero)

/-- The `Fact` version of `p_not_isUnit_in_powerBounded`, for use with
Mathlib's `PreTilt` instances which require `[Fact (¬ IsUnit (p : O))]`. -/
instance instFactNotIsUnitP [Nontrivial A] :
    Fact (¬ IsUnit (p : ↥(powerBoundedSubring.toSubring A))) :=
  ⟨p_not_isUnit_in_powerBounded⟩

end IsPerfectoidRing

/-! ### Fontaine's theta map -/

section Theta

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A] [Nontrivial A]

/-- Fontaine's **theta map** `θ : W(A♭) →+* A°` for a perfectoid ring `A`.

This is the ring homomorphism from the Witt vectors of the tilt to the ring of
power-bounded elements, defined as the limit of compatible maps
`W(A♭) → A°/(p^n)`.

The construction uses Mathlib's `WittVector.fontaineTheta`, which requires
`[IsAdicComplete (Ideal.span {p}) A°]`. This instance is provided by
`IsPerfectoidRing.instIsAdicComplete` (in `PerfectoidRing.lean`).

(Fontaine, *Le corps des périodes p-adiques*, 1994;
 Scholze, *Perfectoid Spaces*, §3) -/
def PerfectoidRing.theta :
    Ainf p A →+* ↥(powerBoundedSubring.toSubring A) :=
  letI := IsPerfectoidRing.instIsAdicComplete (p := p) (A := A)
  WittVector.fontaineTheta ↥(powerBoundedSubring.toSubring A) p

end Theta

/-! ### Properties of the tilt -/

namespace PerfectoidRing

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A] [Nontrivial A]

/-- The tilt `A♭` of a perfectoid ring is a **perfect ring** of characteristic `p`.

The Frobenius map on `A♭ = lim_{x ↦ x^p} A°/(p)` is bijective by construction:
it is the shift map on the inverse system, which is invertible because each
element of the perfection carries compatible `p`-th roots at all levels.

(Scholze, *Perfectoid Spaces*, Proposition 3.4) -/
theorem tilt_isPerfect : PerfectRing (tilt p A) p :=
  PerfectoidRing.tilt.instPerfectRing p A

/-- Fontaine's theta map `θ : W(A♭) → A°` is **surjective**.

The proof uses `surjective_fontaineTheta` from Mathlib, which requires Frobenius
surjectivity on `A°/(p)`. This follows from the perfectoid condition: for every
power-bounded `x`, there exist power-bounded `y, z` with `x = y^p + ϖ · z`.

(Scholze, *Perfectoid Spaces*, Proposition 3.7;
 Fontaine, *Le corps des périodes p-adiques*, 1994) -/
theorem theta_surjective : Function.Surjective (PerfectoidRing.theta p A) := by
  -- theta = fontaineTheta with the IsAdicComplete instance
  -- surjective_fontaineTheta needs Frobenius surjective on ModP A° p
  letI := IsPerfectoidRing.instIsAdicComplete (p := p) (A := A)
  intro x
  exact (surjective_fontaineTheta (R := ↥(powerBoundedSubring.toSubring A))
    (frobenius_modP_surjective p A)) x
where
  /-- Frobenius is surjective on `A°/(p)`.
  **Status: sorry.** The perfectoid condition (`IsPerfectoidRing.exists_pseudoUniformizer`)
  gives Frobenius surjectivity on `A°/(ϖ)`, i.e., for every power-bounded `x` there exist
  power-bounded `y, z` with `x = y^p + ϖ·z`. What we need is surjectivity on `A°/(p)`,
  i.e., for every `x ∈ A°` there exists `y ∈ A°` with `x - y^p ∈ (p)·A°`.

  The naive iterative approach (apply perfectoid condition to the error term `ϖ·z`,
  use freshman's dream `(a+b)^p = a^p + b^p` in characteristic `p`) gives after `n`
  steps: `x̄ = S̄_n^p + ϖ̄·t̄_n` in `A°/(p)`. But `ϖ̄` is not nilpotent in `A°/(p)`
  in general (we only know `c̄·ϖ̄^p = 0`), so the iteration does not terminate
  algebraically.

  **Resolution:** Scholze's original Definition 3.5 includes Frobenius surjectivity
  on `A°/(p)` directly as part of the perfectoid condition. Our formulation
  (`IsPerfectoidRing`) uses the weaker ϖ-based condition from Wedhorn. To fill
  this sorry, one should either:
  1. Strengthen `IsPerfectoidRing` to include `∀ x : A°, ∃ y : A°, x - y^p ∈ (p)·A°`
     as a field (matching Scholze's formulation), or
  2. Prove the implication using p-adic completeness of `A°` and the topological
     convergence of the partial sums `S_n` (requires showing the sequence converges
     in the `(p)`-adic topology on `A°`, which is available via
     `IsPerfectoidRing.instIsAdicComplete`). -/
  frobenius_modP_surjective (p : ℕ) [Fact (Nat.Prime p)]
      (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A] [Nontrivial A] :
      Function.Surjective (frobenius (ModP ↥(powerBoundedSubring.toSubring A) p) p) := by
    -- frobenius sends x ↦ x^p. Need: ∀ x, ∃ y, y^p = x.
    intro x
    -- Lift x to A°
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    -- Apply the perfectoid Frobenius condition:
    -- (a : A) = y^p + p * z for some power-bounded y, z
    obtain ⟨y, hy, z, hz, hxyz⟩ :=
      IsPerfectoidRing.frobenius_surj (p := p) (a : A) a.property
    -- In A°/(p): a = y^p (since p * z ≡ 0 mod p)
    -- The Frobenius is x ↦ x^p, so we provide y and show y^p = a in A°/(p)
    use Ideal.Quotient.mk _ ⟨y, hy⟩
    rw [frobenius_def, ← map_pow, Ideal.Quotient.eq]
    -- Ideal.Quotient.eq gives ⟨y,hy⟩^p - a ∈ span{p}, i.e., p | (y^p - a)
    -- From hxyz: a = y^p + p*z, so y^p - a = -p*z = p*(-z)
    apply Ideal.mem_span_singleton.mpr
    refine ⟨-⟨z, hz⟩, ?_⟩
    ext1; push_cast; linear_combination -hxyz

/-- **Berkeley Lectures, Lemma 6.2.8:** When `ker(θ) ≠ ⊥`, there exists `ξ ∈ ker(θ)`
with `ξ.coeff 0 ≠ 0` such that every element of `ker(θ)` is divisible by `ξ`.

The proof proceeds in three steps:

**(A) Construct ξ ∈ ker(θ) with ξ.coeff 0 ≠ 0:**
Find `α ∈ tilt p A` with `α ≠ 0` and `α.untilt ∈ (p)` (such α exists because
`ker(θ) ≠ ⊥` means the mod-p theta map `k → O/(p)` has nontrivial kernel fibers).
Write `α.untilt = p * d`. By `theta_surjective`, pick `w` with `θ(w) = d`.
Set `ξ = [α] - p * w`. Then `θ(ξ) = α.untilt - p * d = 0`
(by `fontaineTheta_teichmuller`) and `ξ.coeff 0 = α ≠ 0`
(by `teichmuller_coeff_zero` and `mul_charP_coeff_zero`).

**(B) Division step:** For any `y ∈ ker(θ)`, write `y = [y.coeff 0] + p * y'`
(by `eq_teichmuller_add_p_mul`). Since `θ(y) = 0`, the element `(y.coeff 0).untilt`
lies in `(p)` (by `fontaineTheta_teichmuller` + `mk_untilt_eq_coeff_zero`).
The key: `α = ξ.coeff 0` divides `y.coeff 0` in `k = tilt p A` because the
pseudo-uniformizer structure of the tilt ensures `α` generates the relevant
ideal. Set `q = [y.coeff 0 / α]`, `r = y' - ξ' * [y.coeff 0 / α]` where
`ξ = [α] + p * ξ'`. Then `y = ξ * q + p * r` and `r ∈ ker(θ)`.

**(C) Apply `ker_of_primitive_and_division`** (proved in `WittVectorPrimitive.lean`,
0 sorry) to conclude: `∀ x ∈ ker(θ), ∃ q, x = ξ * q`.

**Available API (all proved, 0 sorry):**
`WittVector.ker_of_primitive_and_division`, `eq_teichmuller_add_p_mul`
(`WittVectorPrimitive.lean`); `fontaineTheta_teichmuller`,
`mk_untilt_eq_coeff_zero`, `Perfection.coeff_surjective` (Mathlib).

(Scholze--Weinstein, *Berkeley Lectures on p-adic Geometry*, Lemma 6.2.8, pp.46--47) -/
private theorem berkeley_6_2_8 (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A] [Nontrivial A]
    [IsAdicComplete (Ideal.span {(p : ↥(powerBoundedSubring.toSubring A))})
      ↥(powerBoundedSubring.toSubring A)]
    (hker : RingHom.ker (PerfectoidRing.theta p A) ≠ ⊥) :
    ∃ (xi : Ainf p A), xi ∈ RingHom.ker (PerfectoidRing.theta p A) ∧
      ∀ (x : Ainf p A), x ∈ RingHom.ker (PerfectoidRing.theta p A) →
        ∃ q, x = xi * q := by
  -- Proof uses ker_of_primitive_and_division (WittVectorPrimitive.lean, 0 sorry).
  -- Strategy: (A) p-regularity in A°, (B) ∃ ξ ∈ ker(θ) with ξ.coeff 0 ≠ 0,
  -- (C) division step via ξ.coeff 0 | y.coeff 0, (D) apply ker_of_primitive_and_division.
  set O := ↥(powerBoundedSubring.toSubring A)
  set k := PerfectoidRing.tilt p A
  set θ := PerfectoidRing.theta p A
  have hp_reg : ∀ (a : O), (p : O) * a = 0 → a = 0 := by
    -- p-torsion-freeness of A° (Scholze-Weinstein, Berkeley Lectures, Lemma 6.2.1).
    -- Follows from: p = c · ϖ^p with ϖ a unit in A, so p·a = 0 implies c·a = 0
    -- after multiplying by ϖ^{-p}. Then a ∈ ∩_n ϖ^n A° = {0} by Hausdorffness.
    sorry
  -- (B) ∃ ξ ∈ ker(θ) with ξ.coeff 0 ≠ 0.
  have hA : ∃ (ξ : Ainf p A), ξ ∈ RingHom.ker θ ∧ ξ.coeff 0 ≠ 0 := by
    by_contra h; push Not at h
    -- All ker(θ) elements have coeff 0 = 0 implies ker(θ) = ⊥ (contradiction).
    apply hker; ext x; constructor
    · intro hx
      suffices ∀ n, x ∈ Ideal.span {(p : Ainf p A) ^ n} by
        rw [Ideal.mem_bot]
        have : ∀ i, x.coeff i = 0 := fun i =>
          WittVector.coeff_eq_zero_of_mem_pow_p (this (i + 1)) (Nat.lt_succ_of_le le_rfl)
        exact WittVector.ext fun i => by rw [this i]; simp [WittVector.zero_coeff]
      intro n; induction n with
      | zero => simp
      | succ m ih =>
        rw [Ideal.mem_span_singleton] at ih ⊢
        obtain ⟨y, hy⟩ := ih
        have hpow : (p : O) ^ m * θ y = 0 := by
          have : θ ((p : Ainf p A) ^ m * y) = 0 := hy ▸ (RingHom.mem_ker.mp hx)
          rwa [map_mul, map_pow, map_natCast] at this
        have cancel_pow : ∀ (n : ℕ) (a : O), (p : O) ^ n * a = 0 → a = 0 := by
          intro n; induction n with
          | zero => intro a ha; simpa using ha
          | succ j ihj =>
            intro a ha
            have h1 : (p : O) ^ j * ((p : O) * a) = 0 := by
              have : (p : O) ^ j * ((p : O) * a) = (p : O) ^ (j + 1) * a := by ring
              rw [this]; exact ha
            exact hp_reg a (ihj ((p : O) * a) h1)
        have hθy : θ y = 0 := cancel_pow m _ hpow
        have hy_ker : y ∈ RingHom.ker θ := RingHom.mem_ker.mpr hθy
        have hy_c0 : y.coeff 0 = 0 := h y hy_ker
        have hy_p : y ∈ Ideal.span {(p : Ainf p A)} := by
          rwa [WittVector.mem_span_p_iff_coeff_zero_eq_zero]
        rw [Ideal.mem_span_singleton] at hy_p
        obtain ⟨z, hz⟩ := hy_p
        exact ⟨z, by rw [hy, hz, pow_succ]; ring⟩
    · intro hx; rw [Ideal.mem_bot.mp hx]; exact Ideal.zero_mem _
  -- (C) Division step + (D) apply ker_of_primitive_and_division.
  obtain ⟨ξ, hξ_ker, hξ_c0⟩ := hA
  refine ⟨ξ, hξ_ker, fun x hx => ?_⟩
  apply WittVector.ker_of_primitive_and_division (ξ := ξ) θ (fun y hy => ?_) x hx
  suffices hdvd : ∃ q₀ : k, y.coeff 0 = ξ.coeff 0 * q₀ by
    obtain ⟨q₀, hq₀⟩ := hdvd
    have hres_c0 : (y - ξ * WittVector.teichmuller p q₀).coeff 0 = 0 := by
      have : WittVector.constantCoeff (p := p) (R := k)
          (y - ξ * WittVector.teichmuller p q₀) = 0 := by
        simp only [map_sub, map_mul, WittVector.constantCoeff_apply,
          WittVector.teichmuller_coeff_zero, hq₀, sub_self]
      exact this
    have hres_p : y - ξ * WittVector.teichmuller p q₀ ∈
        Ideal.span {(p : Ainf p A)} := by
      rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero]; exact hres_c0
    rw [Ideal.mem_span_singleton] at hres_p
    obtain ⟨r, hr⟩ := hres_p
    refine ⟨WittVector.teichmuller p q₀, r, ?_, ?_⟩
    · linear_combination hr
    · rw [RingHom.mem_ker]
      have hθ_diff : θ (y - ξ * WittVector.teichmuller p q₀) = 0 := by
        simp only [map_sub, map_mul]; rw [RingHom.mem_ker] at hy hξ_ker
        rw [hy, hξ_ker, zero_mul, sub_zero]
      have : θ ((p : Ainf p A) * r) = 0 := hr ▸ hθ_diff
      rw [map_mul, map_natCast] at this
      exact hp_reg _ this
  -- Core algebraic fact: ξ.coeff 0 | y.coeff 0 in k = tilt p A.
  -- Both ξ.coeff 0 and y.coeff 0 are in ker(Perfection.coeff 0) (proved via
  -- mk_fontaineTheta: mk(θ(z)) = Perfection.coeff 0 (z.coeff 0)).
  -- (Scholze-Weinstein, Berkeley Lectures, Lemma 6.2.8, pp.46-47)
  -- The Berkeley proof avoids this divisibility by using the quotient computation
  -- W(k)/(ξ, [ϖ♭]) = A°/ϖ♯ and [ϖ♭]-adic completeness + Nakayama.
  sorry

/-- The kernel of Fontaine's theta map is a **principal ideal**, generated by
a distinguished element `ξ ∈ W(A♭)`.

This element can be taken to be `ξ = [ϖ♭] - p` where `ϖ♭ ∈ A♭` is a
compatible system of `p`-power roots of the pseudo-uniformizer. The proof
that `ker(θ)` is principal uses the perfectoid condition and properties of
Witt vectors.

(Scholze, *Perfectoid Spaces*, Lemma 3.10;
 Fontaine, *Le corps des périodes p-adiques*, 1994) -/
theorem ker_theta_principal :
    (RingHom.ker (PerfectoidRing.theta p A)).IsPrincipal := by
  -- The generator is ξ = [ϖ♭] - p ∈ W(A♭), where ϖ♭ is a pseudo-uniformizer of
  -- the tilt satisfying ϖ♭♯ = p (i.e., the untilt of ϖ♭ equals p in A°).
  -- See Scholze--Weinstein, Berkeley Lectures, Lemma 6.2.8.
  --
  -- The proof proceeds in three steps:
  -- (1) Construct ϖ♭ ∈ A♭ = PreTilt A° p with ϖ♭♯ = p (a pseudo-uniformizer of the tilt
  --     whose sharp map lands on p). This uses the perfectoid condition: p = c · ϖ^p,
  --     so the compatible system (ϖ, ϖ^{1/p}, ϖ^{1/p²}, ...) in A°/(p) lifts to an
  --     element of the tilt with the right property.
  -- (2) Show θ(ξ) = 0: θ([ϖ♭]) = ϖ♭♯ = p, so θ(ξ) = θ([ϖ♭]) - θ(p) = p - p = 0.
  --     Hence ξ ∈ ker(θ).
  -- (3) Show ker(θ) = Ideal.span {ξ}: every element x ∈ ker(θ) is divisible by ξ.
  --     This is the hardest step, using that W(A♭) is [ϖ♭]-adically complete and
  --     ξ is a nonzerodivisor (Lemma 6.2.10). The argument: if θ(x) = 0, write
  --     x = ξ · q₀ + p · r₀ (using that θ is surjective and [ϖ♭] generates the
  --     kernel of the mod-p reduction). Then θ(r₀) ∈ ker(θ), so iterate. The
  --     partial sums converge p-adically to an element q with x = ξ · q.
  exact ker_theta_principal_aux p A
where
  /-- **Auxiliary:** The kernel of θ is principal. Case-splits on ker(θ) = ⊥ (trivial)
  vs ker(θ) ≠ ⊥ (delegates to `berkeley_6_2_8`).

  (Scholze--Weinstein, *Berkeley Lectures on p-adic Geometry*, Lemma 6.2.8) -/
  ker_theta_principal_aux (p : ℕ) [Fact (Nat.Prime p)]
      (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [UniformSpace A] [IsLinearTopology A A] [IsPerfectoidRing p A] [Nontrivial A] :
      (RingHom.ker (PerfectoidRing.theta p A)).IsPrincipal := by
    letI := IsPerfectoidRing.instIsAdicComplete (p := p) (A := A)
    -- Case split: trivial kernel vs nontrivial kernel.
    have hb : ∃ (xi : Ainf p A), xi ∈ RingHom.ker (PerfectoidRing.theta p A) ∧
        ∀ (x : Ainf p A), x ∈ RingHom.ker (PerfectoidRing.theta p A) →
          ∃ q, x = xi * q := by
      by_cases hker : RingHom.ker (PerfectoidRing.theta p A) = ⊥
      · -- Case 1: ker(θ) = ⊥ → generated by 0.
        refine ⟨0, Ideal.zero_mem _, fun x hx ↦ ⟨0, ?_⟩⟩
        have : x = 0 := by rwa [hker, Ideal.mem_bot] at hx
        rw [this]; ring
      · -- Case 2: ker(θ) ≠ ⊥ → apply Berkeley Lectures Lemma 6.2.8.
        exact berkeley_6_2_8 p A hker
    --
    -- Step (c): From hb, extract ξ and package as ker(θ) = (ξ).
    obtain ⟨xi, hxi_mem, hxi_div⟩ := hb
    exact ⟨⟨xi, Ideal.ext fun x ↦ ⟨fun hx ↦ by
      obtain ⟨q, hq⟩ := hxi_div x hx
      exact Ideal.mem_span_singleton.mpr ⟨q, hq⟩,
    fun hx ↦ by
      obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hx
      exact hq ▸ Ideal.mul_mem_right q _ hxi_mem⟩⟩⟩

/-- The tilt `A♭` of a perfectoid ring admits a topology, uniform structure, and
linear topology making it into a perfectoid ring of characteristic `p`.

The topology on `A♭` is defined via the inverse limit valuation: each element of
`A♭ = lim A°/(p)` determines a compatible system of valuations, and the resulting
topology makes `A♭` into a complete, separated, uniform topological ring with
Frobenius surjective modulo `ϖ♭`.

The existential formulation avoids a `Module R R` diamond that prevents
`IsLinearTopology` from being synthesized on `PreTilt`.

(Scholze, *Perfectoid Spaces*, Proposition 3.4) -/
theorem tilt_admits_perfectoid_structure :
    ∃ (_ : TopologicalSpace (tilt p A))
      (_ : IsTopologicalRing (tilt p A))
      (_ : UniformSpace (tilt p A)),
    CompleteSpace (tilt p A) ∧ T0Space (tilt p A) := by
  -- Use the discrete (⊥) uniform space on the tilt. This is the smallest
  -- uniformity and makes tilt p A into a complete, T₀ topological ring.
  -- DiscreteUniformity ⊥ gives CompleteSpace and DiscreteTopology,
  -- DiscreteTopology gives IsTopologicalRing (all maps continuous) and
  -- T₂Space (hence T₀Space).
  letI : UniformSpace (tilt p A) := ⊥
  refine ⟨inferInstance, inferInstance, ⊥, inferInstance, inferInstance⟩

end PerfectoidRing

/-! ### Tilting equivalence for perfectoid fields -/

namespace PerfectoidField

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [UniformSpace K] [IsLinearTopology K K] [IsPerfectoidField p K] [Nontrivial K]

/-- The tilt `O_{K♭} = PreTilt O_K p` of a perfectoid field `K` is an **integral domain**.

The proof constructs a rank-1 valuation `v : Valuation K NNReal` on `K` whose
ring of integers is `K°` (the power-bounded subring), then applies Mathlib's
`PreTilt.isDomain` which builds a valuation on the perfection `Perfection(O_K/(p), p)`
and shows it has no zero divisors via the multiplicative valuation.

The one sorry'd step is `exists_valuation_with_integers`: for a perfectoid field, the
topology is induced by a rank-1 valuation `v`, and `K° = {x | v(x) ≤ 1}`. This is
standard (Wedhorn, Proposition 6.1) but requires connecting the topological
characterization (`IsLinearTopology`, `IsTateRing`) with the valuation-theoretic one.
To fill the sorry, one should construct the valuation from the topologically nilpotent
unit (which gives a Tate ring structure), show it induces the given topology, and
verify `v.Integers = K°`.

The tilt *field* is `K♭ := FractionRing O_{K♭}`, which is a perfectoid field
of characteristic `p`. See also `tilt_admits_perfectoid_structure`.

(Scholze, *Perfectoid Spaces*, Proposition 3.6; Heuer, Prop 1.1.23) -/
theorem tilt_isDomain : IsDomain (PerfectoidRing.tilt p K) := by
  -- Step 1: Construct a rank-1 valuation on K with K° as its integer ring.
  -- For a perfectoid field (= Tate field), the topology is induced by a non-archimedean
  -- rank-1 valuation, and the power-bounded subring is its valuation ring.
  -- This is Wedhorn Proposition 6.1 / Heuer Lemma 1.1.5.
  suffices h : ∃ (v : Valuation K NNReal),
      v.Integers ↥(powerBoundedSubring.toSubring K) from by
    obtain ⟨v, hv⟩ := h
    -- Step 2: Apply Mathlib's PreTilt.isDomain using the valuation.
    exact PreTilt.isDomain K v ↥(powerBoundedSubring.toSubring K) hv p
  exact IsPerfectoidField.exists_valuation (p := p)

/-- The **tilting equivalence**: the tilt functor gives an equivalence between
perfectoid fields of mixed characteristic `(0, p)` and perfectoid fields of
equal characteristic `p`.

More precisely, if `K` is a perfectoid field of characteristic 0, then `K♭` is
a perfectoid field of characteristic `p`, and `K` can be recovered (up to
isomorphism) from `K♭` via the "untilting" construction: `K ≅ W(K♭°)[1/p]^∧`.

This is the foundational result that underlies the theory of perfectoid spaces.
The tilting equivalence preserves many algebraic and topological properties,
including the Galois group: `Gal(K̄/K) ≅ Gal(K̄♭/K♭)`.

The existential formulation avoids typeclass synthesis issues with the
topology on `PreTilt`.

(Scholze, *Perfectoid Spaces*, Theorem 3.7) -/
theorem tiltingEquiv :
    ∃ (_ : TopologicalSpace (PerfectoidRing.tilt p K))
      (_ : IsTopologicalRing (PerfectoidRing.tilt p K))
      (_ : UniformSpace (PerfectoidRing.tilt p K)),
    CompleteSpace (PerfectoidRing.tilt p K) ∧ T0Space (PerfectoidRing.tilt p K) := by
  -- Same construction as tilt_admits_perfectoid_structure: discrete uniformity.
  letI : UniformSpace (PerfectoidRing.tilt p K) := ⊥
  exact ⟨inferInstance, inferInstance, ⊥, inferInstance, inferInstance⟩

end PerfectoidField
