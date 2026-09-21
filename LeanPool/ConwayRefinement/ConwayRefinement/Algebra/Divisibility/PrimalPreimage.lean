/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Divisibility.Refinement
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Primality in a ring cut out by a residue condition

Let `L` be a field, `A` a commutative `L`-algebra that is a domain, and `π : A →ₐ[L] L` a
retraction of the structure map. For a subring `S ⊆ L`, the elements of `A` whose residue under
`π` lies in `S` form a subring `π ⁻¹ S`. This file decides when an element of that subring is
primal in it, in terms of primality of its residue in `S` and primality of the element in `A`.

The application is `𝐙 + 𝐊((𝐆^{<0}))`, which is exactly the preimage of `𝐙` under the
coefficient-at-zero map on `𝐊((𝐆^{≤0}))`; that map is a ring hom because `x + y = 0` with
`x, y ≤ 0` forces `x = y = 0`.

The statement is LM24, Lemma 9.2.1, and the proof follows theirs with two repairs the printed
argument needs. It concludes `e = f * g` from `b * e = b * (f * g)`, which requires cancellation,
so `A` is assumed to be a domain and `b = 0` is treated separately. And both left-to-right
directions invoke primality in `π ⁻¹ S` at a product whose quotient need not have residue in `S`:
at `π b ≠ 0` the residue can be `1 / π b`, and at `π b = 0` it can be any element of `Frac S`. In
each case a scalar is cleared before primality is invoked and undone afterwards. The rescaling
parameter `η` must also be chosen nonzero, in `L` for the first case and in `Frac S` for the
second.
-/

universe u v

public section

variable {L A : Type*} [Field L] [CommRing A] [Algebra L A]

/-- Primality is invariant under a ring equivalence. -/
theorem RingEquiv.isPrimal_iff {B : Type*} [CommRing B]
    (e : A ≃+* B) (a : A) : IsPrimal (e a) ↔ IsPrimal a := by
  constructor
  · intro h b c hdvd
    have hdvd' : e a ∣ e b * e c := by simpa using e.map_dvd hdvd
    obtain ⟨a₁, a₂, h₁, h₂, ha⟩ := h hdvd'
    refine ⟨e.symm a₁, e.symm a₂, ?_, ?_, ?_⟩
    · simpa using e.symm.map_dvd h₁
    · simpa using e.symm.map_dvd h₂
    · apply e.injective
      simp [ha]
  · intro h b c hdvd
    have hdvd' : a ∣ e.symm b * e.symm c := by simpa using e.symm.map_dvd hdvd
    obtain ⟨a₁, a₂, h₁, h₂, ha⟩ := h hdvd'
    refine ⟨e a₁, e a₂, ?_, ?_, ?_⟩
    · simpa using e.map_dvd h₁
    · simpa using e.map_dvd h₂
    · simp [ha]

namespace Subring

/-- `π ⁻¹ S`, as a subring of `A`. -/
abbrev residueSubring (π : A →ₐ[L] L) (S : Subring L) : Subring A := S.comap (π : A →+* L)

/-- `Frac S`, realised as a subring of the ambient field `L`. -/
abbrev fracSubring (S : Subring L) : Subring L := (Subfield.closure (S : Set L)).toSubring

variable {π : A →ₐ[L] L} {S : Subring L}

theorem mem_residueSubring {b : A} : b ∈ residueSubring π S ↔ π b ∈ S := (Iff.rfl)

theorem le_fracSubring : S ≤ fracSubring S := fun _ hx ↦ Subfield.subset_closure hx

theorem residueSubring_le_fracSubring : residueSubring π S ≤ residueSubring π (fracSubring S) :=
  fun _ hx ↦ le_fracSubring hx

/-- Every element of `Frac S` has a denominator in `S`. -/
theorem exists_den {x : L} (hx : x ∈ fracSubring S) :
    ∃ s ∈ S, s ≠ 0 ∧ s * x ∈ S := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.mp hx
  rw [Subring.closure_eq] at hy hz
  rcases eq_or_ne z 0 with rfl | hz0
  · exact ⟨1, S.one_mem, one_ne_zero, by simp⟩
  · exact ⟨z, hz, hz0, by rw [mul_div_cancel₀ _ hz0]; exact hy⟩

theorem inv_mem_fracSubring {x : L} (hx : x ∈ fracSubring S) : x⁻¹ ∈ fracSubring S :=
  Subfield.inv_mem _ hx

/-- Divisibility inside `π ⁻¹ S`, unfolded to the ambient algebra. -/
theorem dvd_residueSubring_iff {x y : residueSubring π S} :
    x ∣ y ↔ ∃ z : A, π z ∈ S ∧ (y : A) = x * z := by
  constructor
  · rintro ⟨z, rfl⟩; exact ⟨z, z.2, rfl⟩
  · rintro ⟨z, hz, h⟩; exact ⟨⟨z, hz⟩, Subtype.ext h⟩

/-! ### Normalising a factor so that its residue is `0` or `1` -/

open scoped Classical in
/-- The scalar used to normalise `c`; always nonzero. -/
noncomputable def scale (π : A →ₐ[L] L) (c : A) : L := if π c = 0 then 1 else π c

theorem scale_ne_zero (π : A →ₐ[L] L) (c : A) : scale π c ≠ 0 := by
  unfold scale; split <;> simp_all

open scoped Classical in
theorem mem_scale_frac (π : A →ₐ[L] L) {c : A} (hc : π c ∈ fracSubring S) :
    scale π c ∈ fracSubring S := by
  unfold scale; split
  · exact (fracSubring S).one_mem
  · exact hc

/-- `c` with its residue normalised to `0` or `1`. -/
noncomputable def nrm (π : A →ₐ[L] L) (c : A) : A := c * algebraMap L A (scale π c)⁻¹

open scoped Classical in
theorem pi_nrm (π : A →ₐ[L] L) (c : A) : π (nrm π c) = if π c = 0 then 0 else 1 := by
  unfold nrm scale
  rw [map_mul, π.commutes]
  split <;> simp_all

open scoped Classical in
theorem pi_nrm_mem (π : A →ₐ[L] L) (c : A) : π (nrm π c) ∈ S := by
  rw [pi_nrm]; split
  · exact S.zero_mem
  · exact S.one_mem

theorem nrm_mul_scale (π : A →ₐ[L] L) (c : A) :
    nrm π c * algebraMap L A (scale π c) = c := by
  unfold nrm
  rw [mul_assoc, ← map_mul, inv_mul_cancel₀ (scale_ne_zero π c), map_one, mul_one]



/-! ### The residue map on `π ⁻¹ S` -/

/-- `π` restricted to `π ⁻¹ S`, as a ring map onto `S`. -/
def residueHom (π : A →ₐ[L] L) (S : Subring L) : residueSubring π S →+* S where
  toFun x := ⟨π x, x.2⟩
  map_one' := Subtype.ext (map_one π)
  map_mul' _ _ := Subtype.ext (map_mul π _ _)
  map_zero' := Subtype.ext (map_zero π)
  map_add' _ _ := Subtype.ext (map_add π _ _)

@[simp] theorem coe_residueHom (x : residueSubring π S) : ((residueHom π S x : S) : L) = π x :=
  (rfl)

/-! ### Lemma 9.2.1, case `π b ≠ 0` -/

variable [IsDomain A]

/-- Suppose `p` is nonzero, has image zero under `π`, and cannot be factored into two elements
whose images are both zero. If `p` is primal in `π ⁻¹ S`, then `L` is the fraction field of
`S`. -/
@[blueprint "lem:primal-zero-residue-fraction-field"
  (phase := "Algebraic and ordinal preliminaries")
  (title := "A primal zero-residue element forces the fraction-field condition")
  (statement := /--
    Let $L$ be a field, let $A$ be a domain and an $L$-algebra, and let
    $\pi:A\to L$ be an $L$-algebra retraction.  Let $S\subseteq L$ be a
    subring.  Suppose that $p\in A$ is nonzero, $\pi(p)=0$, and every
    factorisation $p=ab$ has $\pi(a)\ne0$ or $\pi(b)\ne0$.  If $p$ is
    primal in $\pi^{-1}(S)$, then $L$ is the fraction field of $S$.
  -/)
  (proof := /--
    Fix $x\in L^\times$.  In $\pi^{-1}(S)$, primality of $p$ applied to
    \[
      (xp)(x^{-1}p)=p^2
    \]
    gives a factorisation $p=p_1p_2$ with $p_1\mid xp$ and
    $p_2\mid x^{-1}p$.  At least one of $\pi(p_1)$ and $\pi(p_2)$ is
    nonzero.  Cancelling $p$ from the corresponding divisibility equation
    expresses $x$ as a quotient of two nonzero residues of elements of
    $\pi^{-1}(S)$.  Both residues lie in $S$, so $x\in\operatorname{Frac}(S)$.
    The case $x=0$ is immediate.
  -/)]
theorem fracSubring_eq_top_of_isPrimal_of_residue_eq_zero
    {p : A} (hpπ : π p = 0) (hp0 : p ≠ 0)
    (hfactor : ∀ a b : A, p = a * b → π a ≠ 0 ∨ π b ≠ 0)
    (hp : IsPrimal (⟨p, by simp [hpπ]⟩ : residueSubring π S)) :
    fracSubring S = ⊤ := by
  apply top_unique
  intro x _
  rcases eq_or_ne x 0 with rfl | hx
  · exact (fracSubring S).zero_mem
  let P : residueSubring π S := ⟨p, by simp [hpπ]⟩
  let C : residueSubring π S :=
    ⟨algebraMap L A x * p, by
      rw [mem_residueSubring, map_mul, AlgHom.commutes, hpπ, mul_zero]
      exact S.zero_mem⟩
  let D : residueSubring π S :=
    ⟨algebraMap L A x⁻¹ * p, by
      rw [mem_residueSubring, map_mul, AlgHom.commutes, hpπ, mul_zero]
      exact S.zero_mem⟩
  have hdiv : P ∣ C * D := by
    refine ⟨P, Subtype.ext ?_⟩
    change algebraMap L A x * p * (algebraMap L A x⁻¹ * p) = p * p
    rw [show algebraMap L A x * p * (algebraMap L A x⁻¹ * p) =
      algebraMap L A (x * x⁻¹) * (p * p) by rw [map_mul]; ring,
      mul_inv_cancel₀ hx, map_one, one_mul]
  obtain ⟨p₁, p₂, hp₁, hp₂, hprod⟩ := hp hdiv
  have hprodA : p = (p₁ : A) * p₂ := congrArg Subtype.val hprod
  rcases hfactor p₁ p₂ hprodA with hp₁res | hp₂res
  · obtain ⟨q, hq⟩ := hp₂
    have hDA : algebraMap L A x⁻¹ * p = (p₂ : A) * q := congrArg Subtype.val hq
    have hcancel : p * (algebraMap L A x⁻¹ * (p₁ : A)) = p * (q : A) := by
      calc
        p * (algebraMap L A x⁻¹ * (p₁ : A)) =
            (p₁ : A) * (algebraMap L A x⁻¹ * p) := by ring
        _ = (p₁ : A) * ((p₂ : A) * q) := by rw [hDA]
        _ = p * q := by rw [hprodA]; ring
    have hscalar : algebraMap L A x⁻¹ * (p₁ : A) = q :=
      mul_left_cancel₀ hp0 hcancel
    have hres : x⁻¹ * π (p₁ : A) = π (q : A) := by
      simpa using congrArg π hscalar
    have hqres : π (q : A) ≠ 0 := by
      rw [← hres]
      exact mul_ne_zero (inv_ne_zero hx) hp₁res
    have hratio : x = π (p₁ : A) * (π (q : A))⁻¹ := by rw [← hres]; field_simp
    rw [hratio]
    exact (fracSubring S).mul_mem (le_fracSubring p₁.2)
      (inv_mem_fracSubring (le_fracSubring q.2))
  · obtain ⟨q, hq⟩ := hp₁
    have hCA : algebraMap L A x * p = (p₁ : A) * q := congrArg Subtype.val hq
    have hcancel : p * (algebraMap L A x * (p₂ : A)) = p * (q : A) := by
      calc
        p * (algebraMap L A x * (p₂ : A)) =
            (p₂ : A) * (algebraMap L A x * p) := by ring
        _ = (p₂ : A) * ((p₁ : A) * q) := by rw [hCA]
        _ = p * q := by rw [hprodA]; ring
    have hscalar : algebraMap L A x * (p₂ : A) = q :=
      mul_left_cancel₀ hp0 hcancel
    have hres : x * π (p₂ : A) = π (q : A) := by
      simpa using congrArg π hscalar
    have hratio : x = π (q : A) * (π (p₂ : A))⁻¹ := by rw [← hres]; field_simp
    rw [hratio]
    exact (fracSubring S).mul_mem (le_fracSubring q.2)
      (inv_mem_fracSubring (le_fracSubring p₂.2))

/-- Suppose `p` maps to an irreducible element under `φ`, and every element whose image under
`φ` is a unit has nonzero image under `π`. If `p` has image zero under `π` and is primal in
`π ⁻¹ S`, then `L` is the fraction field of `S`. -/
theorem fracSubring_eq_top_of_isPrimal_of_irreducible_map
    {B : Type*} [CommRing B] (phi : A →+* B) {p : A}
    (hpπ : π p = 0) (hpIrr : Irreducible (phi p))
    (hunit : ∀ a : A, IsUnit (phi a) → π a ≠ 0)
    (hp : IsPrimal (⟨p, by simp [hpπ]⟩ : residueSubring π S)) :
    fracSubring S = ⊤ := by
  apply fracSubring_eq_top_of_isPrimal_of_residue_eq_zero hpπ
    (fun hp0 ↦ hpIrr.ne_zero (by simp [hp0]))
  · intro a b hab
    have hmap : phi p = phi a * phi b := by simpa only [map_mul] using congrArg phi hab
    rcases hpIrr.isUnit_or_isUnit hmap with ha | hb
    · exact Or.inl (hunit a ha)
    · exact Or.inr (hunit b hb)
  · exact hp

omit [IsDomain A] in
/-- Forward, first half: the residue of a primal element is primal in `S`. -/
theorem isPrimal_residue_of_isPrimal {b : A} (hb : π b ∈ S)
    (h : IsPrimal (⟨b, hb⟩ : residueSubring π S)) (hb0 : π b ≠ 0) :
    IsPrimal (⟨π b, hb⟩ : S) := by
  rintro ⟨c, hc⟩ ⟨d, hd⟩ ⟨⟨e, he⟩, hcd⟩
  have hcd' : c * d = π b * e := congrArg Subtype.val hcd
  have hce : c * d * (π b)⁻¹ = e := by rw [hcd']; field_simp
  set b' : A := b * algebraMap L A (π b)⁻¹ with hb'
  have hpb' : π b' = 1 := by simp [hb', mul_inv_cancel₀ hb0]
  have hmem1 : π (algebraMap L A c) ∈ S := by simpa using hc
  have hmem2 : π (algebraMap L A d * b') ∈ S := by simpa [hpb'] using hd
  have hmem3 : π (algebraMap L A e) ∈ S := by simpa using he
  have key : (⟨b, hb⟩ : residueSubring π S)
      ∣ ⟨algebraMap L A c, hmem1⟩ * ⟨algebraMap L A d * b', hmem2⟩ := by
    refine ⟨⟨algebraMap L A e, hmem3⟩, Subtype.ext ?_⟩
    change algebraMap L A c * (algebraMap L A d * b') = b * algebraMap L A e
    calc algebraMap L A c * (algebraMap L A d * b')
        = algebraMap L A (c * d * (π b)⁻¹) * b := by rw [hb', map_mul, map_mul]; ring
      _ = b * algebraMap L A e := by rw [hce]; ring
  obtain ⟨b₁, b₂, h₁, h₂, hprod⟩ := h key
  refine ⟨residueHom π S b₁, residueHom π S b₂, ?_, ?_, ?_⟩
  · simpa [residueHom, Subtype.ext_iff] using map_dvd (residueHom π S) h₁
  · simpa [residueHom, Subtype.ext_iff, hpb'] using map_dvd (residueHom π S) h₂
  · simpa [residueHom, Subtype.ext_iff] using congrArg (residueHom π S) hprod

omit [IsDomain A] in
/-- Forward, second half: a primal element of `π ⁻¹ S` is primal in the ambient algebra.

This is where the printed proof invokes primality in `π ⁻¹ S` at a product whose quotient can
have residue `1 / π b ∉ S`. Scaling one normalised factor by `π b` first repairs it. -/
theorem isPrimal_of_isPrimal_residueSubring {b : A} (hb : π b ∈ S)
    (h : IsPrimal (⟨b, hb⟩ : residueSubring π S)) (hb0 : π b ≠ 0) :
    IsPrimal b := by
  intro c d ⟨e, hcd⟩
  set σ : L := scale π c * scale π d with hσ
  have hσ0 : σ ≠ 0 := mul_ne_zero (scale_ne_zero π c) (scale_ne_zero π d)
  -- normalise both factors, then scale the first by `π b`
  have hc : nrm π c * algebraMap L A (scale π c) = c := nrm_mul_scale π c
  have hd : nrm π d * algebraMap L A (scale π d) = d := nrm_mul_scale π d
  have hsplit : nrm π c * nrm π d = b * (e * algebraMap L A σ⁻¹) := by
    have : (nrm π c * nrm π d) * algebraMap L A σ = c * d := by
      rw [hσ, map_mul]
      calc (nrm π c * nrm π d)
            * (algebraMap L A (scale π c) * algebraMap L A (scale π d))
          = (nrm π c * algebraMap L A (scale π c))
            * (nrm π d * algebraMap L A (scale π d)) := by ring
        _ = c * d := by rw [hc, hd]
    calc nrm π c * nrm π d = (nrm π c * nrm π d) * algebraMap L A σ * algebraMap L A σ⁻¹ := by
          rw [mul_assoc, ← map_mul, mul_inv_cancel₀ hσ0, map_one, mul_one]
      _ = b * (e * algebraMap L A σ⁻¹) := by rw [this, hcd]; ring
  set w : A := e * algebraMap L A (σ⁻¹ * π b) with hw
  have hres : π w = π (nrm π c) * π (nrm π d) := by
    have h2 := congrArg π hsplit
    simp only [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] at h2
    rw [hw]
    simp only [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
    rw [h2]; ring
  have hmemc : π (nrm π c * algebraMap L A (π b)) ∈ S := by
    rw [map_mul]
    exact S.mul_mem (pi_nrm_mem π c) (by simpa using hb)
  have hmemd : π (nrm π d) ∈ S := pi_nrm_mem π d
  have hmemw : π w ∈ S := by rw [hres]; exact S.mul_mem (pi_nrm_mem π c) (pi_nrm_mem π d)
  have key : (⟨b, hb⟩ : residueSubring π S)
      ∣ ⟨nrm π c * algebraMap L A (π b), hmemc⟩ * ⟨nrm π d, hmemd⟩ := by
    refine ⟨⟨w, hmemw⟩, Subtype.ext ?_⟩
    change nrm π c * algebraMap L A (π b) * nrm π d = b * w
    calc nrm π c * algebraMap L A (π b) * nrm π d
        = (nrm π c * nrm π d) * algebraMap L A (π b) := by ring
      _ = (b * (e * algebraMap L A σ⁻¹)) * algebraMap L A (π b) := by rw [hsplit]
      _ = b * (e * algebraMap L A (σ⁻¹ * π b)) := by rw [map_mul]; ring
      _ = b * w := by rw [hw]
  obtain ⟨b₁, b₂, h₁, h₂, hprod⟩ := h key
  refine ⟨(b₁ : A), (b₂ : A), ?_, ?_, ?_⟩
  · obtain ⟨u, hu⟩ := h₁
    refine ⟨(u : A) * algebraMap L A (scale π c * (π b)⁻¹), ?_⟩
    have hu' : nrm π c * algebraMap L A (π b) = (b₁ : A) * u := congrArg Subtype.val hu
    calc c = nrm π c * algebraMap L A (scale π c) := hc.symm
      _ = (nrm π c * algebraMap L A (π b)) * algebraMap L A (scale π c * (π b)⁻¹) := by
          rw [map_mul]
          calc nrm π c * algebraMap L A (scale π c)
              = nrm π c * algebraMap L A (scale π c) * algebraMap L A (π b * (π b)⁻¹) := by
                rw [mul_inv_cancel₀ hb0, map_one, mul_one]
            _ = nrm π c * algebraMap L A (π b)
                  * (algebraMap L A (scale π c) * algebraMap L A (π b)⁻¹) := by
                rw [map_mul]; ring
      _ = (b₁ : A) * ((u : A) * algebraMap L A (scale π c * (π b)⁻¹)) := by rw [hu']; ring
  · obtain ⟨u, hu⟩ := h₂
    refine ⟨(u : A) * algebraMap L A (scale π d), ?_⟩
    have hu' : nrm π d = (b₂ : A) * u := congrArg Subtype.val hu
    calc d = nrm π d * algebraMap L A (scale π d) := hd.symm
      _ = (b₂ : A) * ((u : A) * algebraMap L A (scale π d)) := by rw [hu']; ring
  · exact congrArg Subtype.val hprod

/-- Converse, case `π b ≠ 0`: primal residue plus primal in the ambient algebra gives primal
in `π ⁻¹ S`. The rescaling parameter `η` must be a nonzero element of `L`; it need not lie in
`S`. -/
theorem isPrimal_residueSubring_of_isPrimal {b : A} (hb : π b ∈ S) (hb0 : π b ≠ 0)
    (hS : IsPrimal (⟨π b, hb⟩ : S)) (hA : IsPrimal b) :
    IsPrimal (⟨b, hb⟩ : residueSubring π S) := by
  have hbne : b ≠ 0 := fun h ↦ hb0 (by rw [h, map_zero])
  rintro c d ⟨e, hcde⟩
  have hcd : (c : A) * d = b * e := congrArg Subtype.val hcde
  obtain ⟨b₁, b₂, ⟨f, hf⟩, ⟨g, hg⟩, hprod⟩ := hA (Dvd.intro _ hcd.symm)
  -- cancellation, available because `A` is a domain and `b ≠ 0`
  have hefg : (e : A) = f * g := by
    have : b * (e : A) = b * (f * g) := by rw [← hcd, hf, hg, hprod]; ring
    exact mul_left_cancel₀ hbne this
  have hpb : π b = π b₁ * π b₂ := by rw [hprod, map_mul]
  have hb₁0 : π b₁ ≠ 0 := fun h ↦ hb0 (by rw [hpb, h, zero_mul])
  have hb₂0 : π b₂ ≠ 0 := fun h ↦ hb0 (by rw [hpb, h, mul_zero])
  -- factor the residue in `S`
  have hdvdS : (⟨π b, hb⟩ : S) ∣ (⟨π c, c.2⟩ : S) * ⟨π d, d.2⟩ := by
    refine ⟨⟨π e, e.2⟩, Subtype.ext ?_⟩
    change π c * π d = π b * π e
    rw [← map_mul, ← map_mul, hcd]
  obtain ⟨⟨b₁', hb₁'⟩, ⟨b₂', hb₂'⟩, ⟨⟨s, hs⟩, hsc⟩, ⟨⟨u, hu⟩, huc⟩, hprod'⟩ := hS hdvdS
  have hbb : π b = b₁' * b₂' := congrArg Subtype.val hprod'
  have hcs : π c = b₁' * s := congrArg Subtype.val hsc
  have hdu : π d = b₂' * u := congrArg Subtype.val huc
  have hb₁'0 : b₁' ≠ 0 := fun h ↦ hb0 (by rw [hbb, h, zero_mul])
  have hb₂'0 : b₂' ≠ 0 := fun h ↦ hb0 (by rw [hbb, h, mul_zero])
  set η : L := π b₁ * b₁'⁻¹ with hη
  have hη0 : η ≠ 0 := mul_ne_zero hb₁0 (inv_ne_zero hb₁'0)
  -- the four rescaled factors and their residues
  have e₁ : π (b₁ * algebraMap L A η⁻¹) = b₁' := by
    simp only [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, hη]
    field_simp
  have e₂ : π (b₂ * algebraMap L A η) = b₂' := by
    simp only [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, hη]
    have : π b₂ * (π b₁ * b₁'⁻¹) = (π b₁ * π b₂) * b₁'⁻¹ := by ring
    rw [this, ← hpb, hbb]; field_simp
  have e₃ : π (f * algebraMap L A η) = s := by
    have hpc : π c = π b₁ * π f := by rw [hf, map_mul]
    simp only [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, hη]
    have : π f * (π b₁ * b₁'⁻¹) = (π b₁ * π f) * b₁'⁻¹ := by ring
    rw [this, ← hpc, hcs]; field_simp
  have hηinv : η⁻¹ = b₁' * (π b₁)⁻¹ := by rw [hη]; field_simp
  have e₄ : π (g * algebraMap L A η⁻¹) = u := by
    have hpd : π b₂ * π g = π d := by rw [hg, map_mul]
    simp only [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, hηinv]
    apply mul_right_cancel₀ (mul_ne_zero hb₁0 hb₂0)
    have h5 : π g * (b₁' * (π b₁)⁻¹) * (π b₁ * π b₂) = (π b₂ * π g) * b₁' := by
      field_simp
    rw [h5, hpd, hdu, show u * (π b₁ * π b₂) = u * π b by rw [hpb], hbb]
    ring
  refine ⟨⟨b₁ * algebraMap L A η⁻¹, mem_residueSubring.mpr (by rw [e₁]; exact hb₁')⟩,
          ⟨b₂ * algebraMap L A η, mem_residueSubring.mpr (by rw [e₂]; exact hb₂')⟩, ?_, ?_, ?_⟩
  · exact ⟨⟨f * algebraMap L A η, mem_residueSubring.mpr (by rw [e₃]; exact hs)⟩, Subtype.ext (by
      change (c : A) = b₁ * algebraMap L A η⁻¹ * (f * algebraMap L A η)
      rw [hf, show b₁ * algebraMap L A η⁻¹ * (f * algebraMap L A η)
          = b₁ * f * (algebraMap L A η⁻¹ * algebraMap L A η) by ring, ← map_mul,
        inv_mul_cancel₀ hη0, map_one, mul_one])⟩
  · exact ⟨⟨g * algebraMap L A η⁻¹, mem_residueSubring.mpr (by rw [e₄]; exact hu)⟩, Subtype.ext (by
      change (d : A) = b₂ * algebraMap L A η * (g * algebraMap L A η⁻¹)
      rw [hg, show b₂ * algebraMap L A η * (g * algebraMap L A η⁻¹)
          = b₂ * g * (algebraMap L A η * algebraMap L A η⁻¹) by ring, ← map_mul,
        mul_inv_cancel₀ hη0, map_one, mul_one])⟩
  · refine Subtype.ext ?_
    change b = b₁ * algebraMap L A η⁻¹ * (b₂ * algebraMap L A η)
    rw [hprod, show b₁ * algebraMap L A η⁻¹ * (b₂ * algebraMap L A η)
        = b₁ * b₂ * (algebraMap L A η⁻¹ * algebraMap L A η) by ring, ← map_mul,
      inv_mul_cancel₀ hη0, map_one, mul_one]

/-! ### Lemma 9.2.1, case `π b = 0` -/

omit [IsDomain A] in
/-- Forward, case `π b = 0`. The printed proof invokes primality in `π ⁻¹ S` at a product whose
quotient can have residue anywhere in `Frac S`; clearing a denominator first repairs it. Since a
normalised residue is `0` or `1`, the denominator may be attached to either factor. -/
theorem isPrimal_fracSubring_of_isPrimal_residueSubring {b : A} (hb : π b ∈ S)
    (h : IsPrimal (⟨b, hb⟩ : residueSubring π S)) :
    IsPrimal (⟨b, le_fracSubring hb⟩ : residueSubring π (fracSubring S)) := by
  rintro c d ⟨e, hcde⟩
  have hcd : (c : A) * d = b * e := congrArg Subtype.val hcde
  set σ : L := scale π c * scale π d with hσ
  have hσ0 : σ ≠ 0 := mul_ne_zero (scale_ne_zero π (c : A)) (scale_ne_zero π (d : A))
  have hc : nrm π (c : A) * algebraMap L A (scale π (c : A)) = (c : A) := nrm_mul_scale π _
  have hd : nrm π (d : A) * algebraMap L A (scale π (d : A)) = (d : A) := nrm_mul_scale π _
  have hsplit : nrm π (c : A) * nrm π (d : A) = b * ((e : A) * algebraMap L A σ⁻¹) := by
    have h1 : (nrm π (c : A) * nrm π (d : A)) * algebraMap L A σ = (c : A) * d := by
      rw [hσ, map_mul]
      calc (nrm π (c : A) * nrm π (d : A))
            * (algebraMap L A (scale π (c : A)) * algebraMap L A (scale π (d : A)))
          = (nrm π (c : A) * algebraMap L A (scale π (c : A)))
            * (nrm π (d : A) * algebraMap L A (scale π (d : A))) := by ring
        _ = (c : A) * d := by rw [hc, hd]
    calc nrm π (c : A) * nrm π (d : A)
        = (nrm π (c : A) * nrm π (d : A)) * algebraMap L A σ * algebraMap L A σ⁻¹ := by
          rw [mul_assoc, ← map_mul, mul_inv_cancel₀ hσ0, map_one, mul_one]
      _ = b * ((e : A) * algebraMap L A σ⁻¹) := by rw [h1, hcd]; ring
  -- the quotient's residue lies in `Frac S`; clear its denominator
  set w : A := (e : A) * algebraMap L A σ⁻¹ with hw
  have hwF : π w ∈ fracSubring S := by
    rw [hw, map_mul, AlgHom.commutes]
    exact (fracSubring S).mul_mem e.2
      (inv_mem_fracSubring (mul_mem (mem_scale_frac π c.2) (mem_scale_frac π d.2)))
  obtain ⟨s, hs, hs0, hsw⟩ := exists_den hwF
  have hmemc : π (nrm π (c : A) * algebraMap L A s) ∈ S := by
    rw [map_mul, AlgHom.commutes]
    exact S.mul_mem (pi_nrm_mem π _) hs
  have hmemd : π (nrm π (d : A)) ∈ S := pi_nrm_mem π _
  have hmemw : π (w * algebraMap L A s) ∈ S := by
    rw [map_mul, AlgHom.commutes, mul_comm]; exact hsw
  have key : (⟨b, hb⟩ : residueSubring π S)
      ∣ ⟨nrm π (c : A) * algebraMap L A s, hmemc⟩ * ⟨nrm π (d : A), hmemd⟩ := by
    refine ⟨⟨w * algebraMap L A s, hmemw⟩, Subtype.ext ?_⟩
    change nrm π (c : A) * algebraMap L A s * nrm π (d : A) = b * (w * algebraMap L A s)
    calc nrm π (c : A) * algebraMap L A s * nrm π (d : A)
        = (nrm π (c : A) * nrm π (d : A)) * algebraMap L A s := by ring
      _ = (b * w) * algebraMap L A s := by rw [hsplit, hw]
      _ = b * (w * algebraMap L A s) := by ring
  obtain ⟨b₁, b₂, ⟨v, hv⟩, ⟨u, hu⟩, hprod⟩ := h key
  have hv' : nrm π (c : A) * algebraMap L A s = (b₁ : A) * v := congrArg Subtype.val hv
  have hu' : nrm π (d : A) = (b₂ : A) * u := congrArg Subtype.val hu
  refine ⟨⟨(b₁ : A), le_fracSubring b₁.2⟩, ⟨(b₂ : A), le_fracSubring b₂.2⟩, ?_, ?_, ?_⟩
  · refine ⟨⟨(v : A) * algebraMap L A (s⁻¹ * scale π (c : A)), ?_⟩, Subtype.ext ?_⟩
    · rw [mem_residueSubring, map_mul, AlgHom.commutes]
      exact (fracSubring S).mul_mem (le_fracSubring v.2)
        ((fracSubring S).mul_mem
          (inv_mem_fracSubring (le_fracSubring hs)) (mem_scale_frac π c.2))
    · change (c : A) = (b₁ : A) * ((v : A) * algebraMap L A (s⁻¹ * scale π (c : A)))
      have hs' : algebraMap L A s * algebraMap L A s⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hs0, map_one]
      calc (c : A) = nrm π (c : A) * algebraMap L A (scale π (c : A)) := hc.symm
        _ = (nrm π (c : A) * algebraMap L A s)
              * (algebraMap L A s⁻¹ * algebraMap L A (scale π (c : A))) := by
            rw [show nrm π (c : A) * algebraMap L A s
                * (algebraMap L A s⁻¹ * algebraMap L A (scale π (c : A)))
                = nrm π (c : A) * algebraMap L A (scale π (c : A))
                  * (algebraMap L A s * algebraMap L A s⁻¹) by ring, hs', mul_one]
        _ = (b₁ : A) * ((v : A) * algebraMap L A (s⁻¹ * scale π (c : A))) := by
            rw [hv', map_mul]; ring
  · refine ⟨⟨(u : A) * algebraMap L A (scale π (d : A)), ?_⟩, Subtype.ext ?_⟩
    · rw [mem_residueSubring, map_mul, AlgHom.commutes]
      exact (fracSubring S).mul_mem (le_fracSubring u.2) (mem_scale_frac π d.2)
    · change (d : A) = (b₂ : A) * ((u : A) * algebraMap L A (scale π (d : A)))
      calc (d : A) = nrm π (d : A) * algebraMap L A (scale π (d : A)) := hd.symm
        _ = (b₂ : A) * ((u : A) * algebraMap L A (scale π (d : A))) := by rw [hu']; ring
  · refine Subtype.ext ?_
    change b = (b₁ : A) * (b₂ : A)
    simpa using congrArg Subtype.val hprod

omit [IsDomain A] in
/-- The rescaling step of the converse at `π b = 0`, in the orientation where the first factor
has zero residue. The paper takes this orientation "without loss of generality"; isolating it
lets both orientations be discharged by the same argument. Here `η` must be a nonzero element
of `Frac S`. -/
private theorem eta_rescale {b c d e : A} (hb : π b ∈ S) (hc : π c ∈ S) (hd : π d ∈ S)
    (he : π e ∈ S) {b₁ b₂ f g : A}
    (hb₂F : π b₂ ∈ fracSubring S) (hfF : π f ∈ fracSubring S)
    (hprod : b = b₁ * b₂) (hcf : c = b₁ * f) (hdg : d = b₂ * g) (hefg : e = f * g)
    (h₁0 : π b₁ = 0) :
    ∃ B₁ B₂ : residueSubring π S, B₁ ∣ (⟨c, hc⟩ : residueSubring π S) ∧
      B₂ ∣ (⟨d, hd⟩ : residueSubring π S) ∧ (⟨b, hb⟩ : residueSubring π S) = B₁ * B₂ := by
  obtain ⟨η, hη0, hηb₂, hηf, hηg⟩ :
      ∃ η : L, η ≠ 0 ∧ η * π b₂ ∈ S ∧ η * π f ∈ S ∧ π g * η⁻¹ ∈ S := by
    rcases eq_or_ne (π g) 0 with hg0 | hg0
    · obtain ⟨s₁, hs₁, hs₁0, hs₁b⟩ := exists_den hb₂F
      obtain ⟨s₂, hs₂, hs₂0, hs₂f⟩ := exists_den hfF
      refine ⟨s₁ * s₂, mul_ne_zero hs₁0 hs₂0, ?_, ?_, ?_⟩
      · rw [show s₁ * s₂ * π b₂ = s₂ * (s₁ * π b₂) by ring]; exact S.mul_mem hs₂ hs₁b
      · rw [show s₁ * s₂ * π f = s₁ * (s₂ * π f) by ring]; exact S.mul_mem hs₁ hs₂f
      · rw [hg0, zero_mul]; exact S.zero_mem
    · refine ⟨π g, hg0, ?_, ?_, ?_⟩
      · rw [mul_comm, ← map_mul, ← hdg]; exact hd
      · rw [mul_comm, ← map_mul, ← hefg]; exact he
      · rw [mul_inv_cancel₀ hg0]; exact S.one_mem
  have hinv : algebraMap L A η⁻¹ * algebraMap L A η = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hη0, map_one]
  have hinv' : algebraMap L A η * algebraMap L A η⁻¹ = 1 := by rw [mul_comm]; exact hinv
  refine ⟨⟨b₁ * algebraMap L A η⁻¹, ?_⟩, ⟨b₂ * algebraMap L A η, ?_⟩, ?_, ?_, ?_⟩
  · rw [mem_residueSubring, map_mul, AlgHom.commutes, h₁0, zero_mul]; exact S.zero_mem
  · rw [mem_residueSubring, map_mul, AlgHom.commutes, mul_comm]; exact hηb₂
  · refine ⟨⟨f * algebraMap L A η, ?_⟩, Subtype.ext ?_⟩
    · rw [mem_residueSubring, map_mul, AlgHom.commutes, mul_comm]; exact hηf
    · change c = b₁ * algebraMap L A η⁻¹ * (f * algebraMap L A η)
      rw [hcf, show b₁ * algebraMap L A η⁻¹ * (f * algebraMap L A η)
          = b₁ * f * (algebraMap L A η⁻¹ * algebraMap L A η) by ring, hinv, mul_one]
  · refine ⟨⟨g * algebraMap L A η⁻¹, ?_⟩, Subtype.ext ?_⟩
    · rw [mem_residueSubring, map_mul, AlgHom.commutes]; exact hηg
    · change d = b₂ * algebraMap L A η * (g * algebraMap L A η⁻¹)
      rw [hdg, show b₂ * algebraMap L A η * (g * algebraMap L A η⁻¹)
          = b₂ * g * (algebraMap L A η * algebraMap L A η⁻¹) by ring, hinv', mul_one]
  · refine Subtype.ext ?_
    change b = b₁ * algebraMap L A η⁻¹ * (b₂ * algebraMap L A η)
    rw [hprod, show b₁ * algebraMap L A η⁻¹ * (b₂ * algebraMap L A η)
        = b₁ * b₂ * (algebraMap L A η⁻¹ * algebraMap L A η) by ring, hinv, mul_one]

/-- Converse, case `π b = 0`. -/
theorem isPrimal_residueSubring_of_isPrimal_pre_fracSubring {b : A} (hb : π b ∈ S) (hb0 : π b = 0)
    (h : IsPrimal (⟨b, le_fracSubring hb⟩ : residueSubring π (fracSubring S))) :
    IsPrimal (⟨b, hb⟩ : residueSubring π S) := by
  rcases eq_or_ne b 0 with rfl | hbne
  · have hz : (⟨(0 : A), hb⟩ : residueSubring π S) = 0 := rfl
    rw [hz]; exact isPrimal_zero
  rintro c d ⟨e, hcde⟩
  have hcd : (c : A) * d = b * e := congrArg Subtype.val hcde
  have hdvdF : (⟨b, le_fracSubring hb⟩ : residueSubring π (fracSubring S))
      ∣ ⟨(c : A), le_fracSubring c.2⟩ * ⟨(d : A), le_fracSubring d.2⟩ :=
    ⟨⟨(e : A), le_fracSubring e.2⟩, Subtype.ext hcd⟩
  obtain ⟨b₁, b₂, ⟨f, hf⟩, ⟨g, hg⟩, hprod⟩ := h hdvdF
  have hprod' : b = (b₁ : A) * b₂ := congrArg Subtype.val hprod
  have hcf : (c : A) = (b₁ : A) * f := congrArg Subtype.val hf
  have hdg : (d : A) = (b₂ : A) * g := congrArg Subtype.val hg
  have hefg : (e : A) = (f : A) * g := by
    have h6 : b * (e : A) = b * ((f : A) * g) := by rw [← hcd, hcf, hdg, hprod']; ring
    exact mul_left_cancel₀ hbne h6
  have hzero : π (b₁ : A) = 0 ∨ π (b₂ : A) = 0 :=
    mul_eq_zero.mp (by rw [← map_mul, ← hprod']; exact hb0)
  rcases hzero with h1 | h2
  · exact eta_rescale hb c.2 d.2 e.2 b₂.2 f.2 hprod' hcf hdg hefg h1
  · obtain ⟨B₁, B₂, hd1, hd2, hp⟩ :=
      eta_rescale hb d.2 c.2 e.2 b₁.2 g.2 (by rw [hprod']; ring) hdg hcf
        (by rw [hefg]; ring) h2
    exact ⟨B₂, B₁, hd2, hd1, by rw [hp]; ring⟩

/-! ### Lemma 9.2.1 -/

/-- LM24, Lemma 9.2.1, with the repairs its errata require: `A` must be a domain, and the two
left-to-right steps must clear a denominator before primality in `π ⁻¹ S` is invoked. -/
theorem isPrimal_residueSubring_iff {b : A} (hb : π b ∈ S) :
    IsPrimal (⟨b, hb⟩ : residueSubring π S) ↔
      (π b ≠ 0 ∧ IsPrimal (⟨π b, hb⟩ : S) ∧ IsPrimal b) ∨
      (π b = 0 ∧ IsPrimal (⟨b, le_fracSubring hb⟩ : residueSubring π (fracSubring S))) := by
  rcases eq_or_ne (π b) 0 with h0 | h0
  · simp only [h0, ne_eq, not_true_eq_false, false_and, false_or, true_and]
    exact ⟨isPrimal_fracSubring_of_isPrimal_residueSubring hb,
      isPrimal_residueSubring_of_isPrimal_pre_fracSubring hb h0⟩
  · constructor
    · exact fun h ↦ Or.inl
        ⟨h0, isPrimal_residue_of_isPrimal hb h h0, isPrimal_of_isPrimal_residueSubring hb h h0⟩
    · rintro (⟨-, hS, hA⟩ | ⟨h, -⟩)
      · exact isPrimal_residueSubring_of_isPrimal hb h0 hS hA
      · exact absurd h h0

omit [IsDomain A] in
/-- An exact ambient four-factor refinement whose first input has nonzero residue can be
rescaled into the residue subring, provided that residue is primal. Only this one ambient
refinement and this one primal residue are required. -/
theorem exists_refinement_residueSubring_of_ambient_of_residue_ne_zero
    {a b c d : residueSubring π S}
    (haS : IsPrimal (⟨π (a : A), a.2⟩ : S)) (haπ : π (a : A) ≠ 0)
    (habcd : a * b = c * d)
    {e f g h : A}
    (ha : (a : A) = e * f) (hb : (b : A) = g * h)
    (hc : (c : A) = e * g) (hd : (d : A) = f * h) :
    ∃ E F G H : residueSubring π S,
      a = E * F ∧ b = G * H ∧ c = E * G ∧ d = F * H := by
  have habcdS :
      (⟨π (a : A), a.2⟩ : S) * ⟨π (b : A), b.2⟩ =
        ⟨π (c : A), c.2⟩ * ⟨π (d : A), d.2⟩ := by
    apply Subtype.ext
    change π (a : A) * π (b : A) = π (c : A) * π (d : A)
    rw [← map_mul, ← map_mul]
    exact congrArg π (congrArg Subtype.val habcd)
  have haS0 : (⟨π (a : A), a.2⟩ : S) ≠ 0 := by
    intro hzero
    apply haπ
    exact congrArg Subtype.val hzero
  obtain ⟨e₀, f₀, g₀, h₀, ha₀, hb₀, hc₀, hd₀⟩ :=
    exists_fourFactorRefinement_of_isPrimal haS0 haS habcdS
  have ha₀' : π (a : A) = (e₀ : L) * f₀ := congrArg Subtype.val ha₀
  have hc₀' : π (c : A) = (e₀ : L) * g₀ := congrArg Subtype.val hc₀
  have hd₀' : π (d : A) = (f₀ : L) * h₀ := congrArg Subtype.val hd₀
  have he0 : π e ≠ 0 := by
    intro he
    apply haπ
    rw [ha, map_mul, he, zero_mul]
  have hf0 : π f ≠ 0 := by
    intro hf
    apply haπ
    rw [ha, map_mul, hf, mul_zero]
  have he₀0 : (e₀ : L) ≠ 0 := by
    intro he₀
    apply haπ
    rw [ha₀', he₀, zero_mul]
  have hf₀0 : (f₀ : L) ≠ 0 := by
    intro hf₀
    apply haπ
    rw [ha₀', hf₀, mul_zero]
  let η : L := π e * (e₀ : L)⁻¹
  have hη0 : η ≠ 0 := mul_ne_zero he0 (inv_ne_zero he₀0)
  have hE : π (e * algebraMap L A η⁻¹) = e₀ := by
    simp only [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
    dsimp only [η]
    field_simp
  have hF : π (f * algebraMap L A η) = f₀ := by
    simp only [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
    dsimp only [η]
    have hae : π (a : A) = π e * π f := by rw [ha, map_mul]
    calc
      π f * (π e * (e₀ : L)⁻¹) = (π e * π f) * (e₀ : L)⁻¹ := by ring
      _ = π (a : A) * (e₀ : L)⁻¹ := by rw [hae]
      _ = (e₀ : L) * f₀ * (e₀ : L)⁻¹ := by rw [ha₀']
      _ = f₀ := by field_simp
  have hG : π (g * algebraMap L A η) = g₀ := by
    simp only [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
    dsimp only [η]
    have hce : π (c : A) = π e * π g := by rw [hc, map_mul]
    rw [show π g * (π e * (e₀ : L)⁻¹) = (π e * π g) * (e₀ : L)⁻¹ by ring,
      ← hce, hc₀']
    field_simp
  have hH : π (h * algebraMap L A η⁻¹) = h₀ := by
    simp only [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
    have hFscalar : π f * η = (f₀ : L) := by simpa using hF
    have hdh : π (d : A) = π f * π h := by rw [hd, map_mul]
    apply mul_left_cancel₀ hf₀0
    calc
      (f₀ : L) * (π h * η⁻¹) = (π f * η) * (π h * η⁻¹) := by rw [hFscalar]
      _ = π f * π h := by field_simp
      _ = π (d : A) := hdh.symm
      _ = (f₀ : L) * h₀ := hd₀'
  refine ⟨⟨e * algebraMap L A η⁻¹, mem_residueSubring.mpr (by rw [hE]; exact e₀.2)⟩,
    ⟨f * algebraMap L A η, mem_residueSubring.mpr (by rw [hF]; exact f₀.2)⟩,
    ⟨g * algebraMap L A η, mem_residueSubring.mpr (by rw [hG]; exact g₀.2)⟩,
    ⟨h * algebraMap L A η⁻¹, mem_residueSubring.mpr (by rw [hH]; exact h₀.2)⟩,
    ?_, ?_, ?_, ?_⟩
  all_goals
    apply Subtype.ext
    simp only [Subring.coe_mul]
  · rw [ha]
    rw [show (e * algebraMap L A η⁻¹) * (f * algebraMap L A η) =
      e * f * (algebraMap L A η⁻¹ * algebraMap L A η) by ring,
      ← map_mul, inv_mul_cancel₀ hη0, map_one, mul_one]
  · rw [hb]
    rw [show (g * algebraMap L A η) * (h * algebraMap L A η⁻¹) =
      g * h * (algebraMap L A η * algebraMap L A η⁻¹) by ring,
      ← map_mul, mul_inv_cancel₀ hη0, map_one, mul_one]
  · rw [hc]
    rw [show (e * algebraMap L A η⁻¹) * (g * algebraMap L A η) =
      e * g * (algebraMap L A η⁻¹ * algebraMap L A η) by ring,
      ← map_mul, inv_mul_cancel₀ hη0, map_one, mul_one]
  · rw [hd]
    rw [show (f * algebraMap L A η) * (h * algebraMap L A η⁻¹) =
      f * h * (algebraMap L A η * algebraMap L A η⁻¹) by ring,
      ← map_mul, mul_inv_cancel₀ hη0, map_one, mul_one]

/-- A nonzero exact ambient four-factor refinement can be rescaled into the residue subring when
the first residue is primal and that subring generates the coefficient field. This is the
equation-local form needed after an exact germ refinement; no global refinement property of the
residue ring is assumed. -/
theorem exists_refinement_residueSubring_of_ambient
    {a b c d : residueSubring π S}
    (haS : IsPrimal (⟨π (a : A), a.2⟩ : S)) (hfrac : fracSubring S = ⊤)
    (ha0 : a ≠ 0) (habcd : a * b = c * d)
    {e f g h : A}
    (ha : (a : A) = e * f) (hb : (b : A) = g * h)
    (hc : (c : A) = e * g) (hd : (d : A) = f * h) :
    ∃ E F G H : residueSubring π S,
      a = E * F ∧ b = G * H ∧ c = E * G ∧ d = F * H := by
  by_cases haπ : π (a : A) = 0
  · have haA0 : (a : A) ≠ 0 := fun h ↦ ha0 (Subtype.ext h)
    have hef0 : π e = 0 ∨ π f = 0 := by
      apply mul_eq_zero.mp
      rw [← map_mul, ← ha]
      exact haπ
    rcases hef0 with he0 | hf0
    · obtain ⟨E, F, hEc, hFd, haEF⟩ := eta_rescale a.2 c.2 d.2 b.2
          (by rw [hfrac]; exact Subring.mem_top _)
          (by rw [hfrac]; exact Subring.mem_top _)
          ha hc hd hb he0
      obtain ⟨G, hcEG⟩ := hEc
      obtain ⟨H, hdFH⟩ := hFd
      refine ⟨E, F, G, H, haEF, ?_, hcEG, hdFH⟩
      apply Subtype.ext
      apply mul_left_cancel₀ haA0
      change (a : A) * (b : A) = (a : A) * ((G : A) * H)
      have habcd' := congrArg Subtype.val habcd
      have hcEG' := congrArg Subtype.val hcEG
      have hdFH' := congrArg Subtype.val hdFH
      have haEF' := congrArg Subtype.val haEF
      simp only [Subring.coe_mul] at habcd' hcEG' hdFH' haEF'
      rw [habcd', hcEG', hdFH', haEF']
      ring
    · obtain ⟨F, E, hFd, hEc, haFE⟩ := eta_rescale a.2 d.2 c.2 b.2
          (by rw [hfrac]; exact Subring.mem_top _)
          (by rw [hfrac]; exact Subring.mem_top _)
          (by rw [ha]; ring) hd hc (by rw [hb]; ring) hf0
      obtain ⟨H, hdFH⟩ := hFd
      obtain ⟨G, hcEG⟩ := hEc
      refine ⟨E, F, G, H, ?_, ?_, hcEG, hdFH⟩
      · exact haFE.trans (mul_comm F E)
      · apply Subtype.ext
        apply mul_left_cancel₀ haA0
        change (a : A) * (b : A) = (a : A) * ((G : A) * H)
        have habcd' := congrArg Subtype.val habcd
        have hcEG' := congrArg Subtype.val hcEG
        have hdFH' := congrArg Subtype.val hdFH
        have haFE' := congrArg Subtype.val haFE
        simp only [Subring.coe_mul] at habcd' hcEG' hdFH' haFE'
        rw [habcd', hcEG', hdFH', haFE']
        ring
  · exact exists_refinement_residueSubring_of_ambient_of_residue_ne_zero
      haS haπ habcd ha hb hc hd

/-- A nonzero element of a residue subring is primal when its residue is primal, the coefficient
subring generates the whole coefficient field, and the element is primal in the ambient algebra.
This equation-local form avoids assuming refinement for every ambient element. -/
theorem isPrimal_residueSubring_of_isPrimal_ambient
    {b : residueSubring π S} (hb0 : b ≠ 0)
    (hbS : IsPrimal (⟨π (b : A), b.2⟩ : S)) (hfrac : fracSubring S = ⊤)
    (hbA : IsPrimal (b : A)) : IsPrimal b := by
  intro c d hdvd
  obtain ⟨q, hq⟩ := hdvd
  have hprod : b * q = c * d := hq.symm
  obtain ⟨e, f, g, h, hb, hq, hc, hd⟩ :=
    exists_fourFactorRefinement_of_isPrimal
      (fun hzero ↦ hb0 (Subtype.ext hzero)) hbA (congrArg Subtype.val hprod)
  obtain ⟨E, F, G, H, hb', -, hc', hd'⟩ :=
    exists_refinement_residueSubring_of_ambient hbS hfrac hb0 hprod hb hq hc hd
  exact ⟨E, F, ⟨G, hc'⟩, ⟨H, hd'⟩, hb'⟩

/-- Four-factor refinement ascends from the ambient algebra and the residue subring when the
residue subring generates the whole coefficient field. The zero-residue branch uses ambient
refinement after identifying the enlarged residue pullback with the ambient algebra. -/
theorem hasFourFactorRefinement_residueSubring
    (hA : HasFourFactorRefinement A) (hS : HasFourFactorRefinement S)
    (hfrac : fracSubring S = ⊤) :
    HasFourFactorRefinement (residueSubring π S) := by
  rw [hasFourFactorRefinement_iff_forall_isPrimal]
  intro b
  rw [isPrimal_residueSubring_iff b.2]
  by_cases hb : π b = 0
  · right
    refine ⟨hb, ?_⟩
    let b' : residueSubring π (fracSubring S) := ⟨b, le_fracSubring b.2⟩
    let e : residueSubring π (fracSubring S) ≃+* A := {
      toFun x := x
      invFun x := ⟨x, by rw [mem_residueSubring, hfrac]; exact Subring.mem_top _⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_mul' _ _ := rfl
      map_add' _ _ := rfl }
    apply (e.isPrimal_iff b').mp
    change IsPrimal (b : A)
    exact hA.isPrimal (b : A)
  · left
    exact ⟨hb, hS.isPrimal _, hA.isPrimal b⟩

end Subring
