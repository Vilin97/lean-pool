/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import Mathlib.RingTheory.LaurentSeries

/-!
# The field of Puiseux series

This file defines the field of Puiseux series over a field `K` as a subfield of the Hahn series
field `HahnSeries ℚ K`, namely the directed union of the images of the embeddings
`LaurentSeries.toHahn K n : K((t)) →+* HahnSeries ℚ K` sending `t` to `t ^ (1 / n)`.

## Main definitions

* `LaurentSeries.expand K m`: the expansion ring endomorphism of `K((t))` sending `t` to `t ^ m`.
* `LaurentSeries.toHahn K n`: the ring embedding `K((t)) →+* HahnSeries ℚ K`
  sending `t` to `t ^ (1 / n)`.
* `PuiseuxSeries.subfield K`: the Puiseux subfield `⨆ n, (toHahn K n).fieldRange` of
  `HahnSeries ℚ K`.
* `PuiseuxSeries K`: the type of Puiseux series over `K`, a field, equipped with an algebra
  structure over `LaurentSeries K` via `toHahn K 1`.

## Main results

* `PuiseuxSeries.mem_subfield_iff`: membership in the Puiseux subfield is membership in the range
  of some `toHahn K n`.
* `PuiseuxSeries.mem_subfield_iff_support`: the classical bounded-denominator characterization —
  a Hahn series is a Puiseux series iff its support lies in `(1 / n) • ℤ` for a single `n`.
* `PuiseuxSeries.exists_common_index`: finitely many Puiseux series lie in the range of a single
  `toHahn K N`.

## Tags

puiseux series, laurent series, hahn series
-/

/- Ported to Lean Pool and its pinned Mathlib toolchain in September 2026. -/

public section

noncomputable section

open HahnSeries Polynomial

namespace HahnSeries

/-- `embDomain` composes: extending along `f` and then along `g` is extending along
`f.trans g`. -/
@[simp]
theorem embDomain_embDomain {Γ Γ' Γ'' R : Type*} [PartialOrder Γ] [PartialOrder Γ']
    [PartialOrder Γ''] [Zero R] (f : Γ ↪o Γ') (g : Γ' ↪o Γ'') (x : HahnSeries Γ R) :
    embDomain g (embDomain f x) = embDomain (f.trans g) x := by
  ext b
  by_cases hb : b ∈ Set.range (f.trans g)
  · obtain ⟨a, rfl⟩ := hb
    rw [embDomain_coeff, RelEmbedding.trans_apply, embDomain_coeff, embDomain_coeff]
  · rw [embDomain_of_notMem_range hb]
    by_cases hb' : b ∈ Set.range g
    · obtain ⟨c, rfl⟩ := hb'
      rw [embDomain_coeff, embDomain_of_notMem_range fun ⟨a, ha⟩ => hb ⟨a, by simp [ha]⟩]
    · exact embDomain_of_notMem_range hb'

end HahnSeries

namespace LaurentSeries

variable (K : Type*) [Field K]

/-- The expansion ring embedding `K((t)) →+* K((t))`, `t ↦ t ^ m`:
`embDomainRingHom` along the exponent map `k ↦ m * k` on `ℤ`. -/
def expand (m : ℕ+) : LaurentSeries K →+* LaurentSeries K :=
  HahnSeries.embDomainRingHom (AddMonoidHom.mk' ((m : ℤ) * ·) (mul_add _))
    (fun _ _ => mul_left_cancel₀ (by exact_mod_cast m.ne_zero))
    fun _ _ => mul_le_mul_iff_right₀ (by exact_mod_cast m.pos)

/-- The embedding `K((t)) →+* HahnSeries ℚ K`, "`t ↦ t ^ (1 / n)`":
`embDomainRingHom` along the exponent map `k ↦ k / n : ℤ → ℚ`. -/
def toHahn (n : ℕ+) : LaurentSeries K →+* HahnSeries ℚ K :=
  HahnSeries.embDomainRingHom
    (AddMonoidHom.mk' (fun k : ℤ => (k : ℚ) / (n : ℕ)) fun a b => by push_cast; ring)
    (fun _ _ h => Int.cast_injective ((div_left_inj' (Nat.cast_ne_zero.mpr n.ne_zero)).mp h))
    fun _ _ => (div_le_div_iff_of_pos_right (Nat.cast_pos.mpr n.pos)).trans Int.cast_le

@[simp]
theorem toHahn_single (n : ℕ+) (k : ℤ) (a : K) :
    toHahn K n (HahnSeries.single k a) = HahnSeries.single ((k : ℚ) / (n : ℕ)) a :=
  HahnSeries.embDomain_single ..

/-- Compatibility of the embeddings: `toHahn K n = toHahn K (n * m) ∘ expand K m` — expanding
by `m` and then mapping `t ↦ t ^ (1 / (n * m))` is mapping `t ↦ t ^ (1 / n)`. -/
theorem toHahn_comp_expand (n m : ℕ+) :
    (toHahn K (n * m)).comp (expand K m) = toHahn K n :=
  RingHom.ext fun f => by
    change HahnSeries.embDomain _ (HahnSeries.embDomain _ f) = HahnSeries.embDomain _ f
    rw [HahnSeries.embDomain_embDomain]
    congr 1
    ext k
    simp [mul_comm ((n : ℚ)), mul_div_mul_left]

/-- Range monotonicity: the range of `toHahn K n` is contained in the range of
`toHahn K (n * m)`, as subfields of `HahnSeries ℚ K`. -/
theorem fieldRange_toHahn_le (n m : ℕ+) :
    (toHahn K n).fieldRange ≤ (toHahn K (n * m)).fieldRange :=
  fun _ ⟨f, hf⟩ => ⟨expand K m f, (DFunLike.congr_fun (toHahn_comp_expand K n m) f).trans hf⟩

/-- The family `n ↦ (toHahn K n).fieldRange` is directed: the ranges of `toHahn K a` and
`toHahn K b` both sit inside the range of `toHahn K (a * b)`. -/
theorem directed_fieldRange_toHahn :
    Directed (· ≤ ·) fun n : ℕ+ => (toHahn K n).fieldRange := fun a b =>
  ⟨a * b, fieldRange_toHahn_le K a b, mul_comm b a ▸ fieldRange_toHahn_le K b a⟩

end LaurentSeries

namespace PuiseuxSeries

open LaurentSeries

variable (K : Type*) [Field K]

/-- The Puiseux subfield `⨆ n, (toHahn K n).fieldRange` of `HahnSeries ℚ K` — the directed union
of the images of the embeddings `toHahn K n`, i.e. `⋃ n, K((t ^ (1 / n)))`. -/
def subfield : Subfield (HahnSeries ℚ K) :=
  ⨆ n : ℕ+, (toHahn K n).fieldRange

/-- Membership in the Puiseux subfield: `x ∈ subfield K` iff `x` is in the range of some
`toHahn K n` (the supremum of the directed family of subfields is their union). -/
theorem mem_subfield_iff {x : HahnSeries ℚ K} :
    x ∈ subfield K ↔ ∃ n : ℕ+, x ∈ (toHahn K n).fieldRange :=
  Subfield.mem_iSup_of_directed (directed_fieldRange_toHahn K)

/-- **Bounded-denominator characterization**: membership in the Puiseux subfield
is exactly the classical support condition — the support lies in `(1 / n) • ℤ` for a
single `n`. This certifies the directed-union definition against the textbook
description of Puiseux series. -/
theorem mem_subfield_iff_support {x : HahnSeries ℚ K} :
    x ∈ subfield K ↔
      ∃ n : ℕ+, ∀ q ∈ x.support, ∃ k : ℤ, q = (k : ℚ) / (n : ℚ) := by
  -- the key coefficient fact about `toHahn K n`, which is an `embDomain` by definition
  have key₂ : ∀ (n : ℕ+) (f : LaurentSeries K) (q : ℚ),
      (¬ ∃ k : ℤ, q = (k : ℚ) / (n : ℚ)) → ((toHahn K n) f).coeff q = 0 := fun n f q hq =>
    HahnSeries.embDomain_of_notMem_range fun ⟨k, hk⟩ => hq ⟨k, hk.symm⟩
  rw [mem_subfield_iff]
  constructor
  · rintro ⟨n, f, rfl⟩
    exact ⟨n, fun q => Not.imp_symm (key₂ n f q)⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rcases Set.eq_empty_or_nonempty x.support with hs | hs
    · exact ⟨0, (map_zero _).trans (HahnSeries.support_eq_empty_iff.mp hs).symm⟩
    -- the minimum of the support gives an integer lower bound for the support of `f`
    refine ⟨⟨fun k => x.coeff ((k : ℚ) / (n : ℚ)), ?_⟩, ?_⟩
    · exact (BddBelow.isWF ⟨⌈(n : ℚ) * x.isWF_support.min hs⌉, fun k hk => Int.ceil_le.mpr
        ((le_div_iff₀' (by exact_mod_cast n.pos)).mp (x.isWF_support.min_le hs hk))⟩).isPWO
    · ext q
      by_cases hq : ∃ k : ℤ, q = (k : ℚ) / (n : ℚ)
      · obtain ⟨k, rfl⟩ := hq
        exact HahnSeries.embDomain_coeff
      · exact (key₂ n _ q hq).trans (of_not_not (mt (hn q) hq)).symm

/-- Common index: a finite set of elements of the Puiseux subfield lies in the
range of a single `toHahn K N`. -/
theorem exists_common_index (s : Finset (HahnSeries ℚ K))
    (hs : ∀ x ∈ s, x ∈ subfield K) :
    ∃ N : ℕ+, ∀ x ∈ s, x ∈ (toHahn K N).fieldRange := by
  choose! n hn using fun x (hx : x ∈ s) => (mem_subfield_iff K).mp (hs x hx)
  obtain ⟨N, hN⟩ := (directed_fieldRange_toHahn K).finset_le (s.image n)
  exact ⟨N, fun x hx => hN (n x) (Finset.mem_image_of_mem n hx) (hn x hx)⟩

end PuiseuxSeries

/-- The type of Puiseux series over `K`: the carrier of the Puiseux subfield of
`HahnSeries ℚ K`. A field, by the generic subfield instances. -/
def PuiseuxSeries (K : Type*) [Field K] : Type _ :=
  ↥(PuiseuxSeries.subfield K)

namespace PuiseuxSeries

variable (K : Type*) [Field K]

instance : Field (PuiseuxSeries K) :=
  inferInstanceAs (Field ↥(subfield K))

/-- The `K((t))`-algebra structure on Puiseux series: `toHahn K 1` corestricted to the
Puiseux subfield. This fixes the embedding of `K((t))` into the Puiseux series. -/
instance algebraLaurentSeries : Algebra (LaurentSeries K) (PuiseuxSeries K) :=
  RingHom.toAlgebra <|
    (LaurentSeries.toHahn K 1).codRestrict (subfield K) fun x =>
      (mem_subfield_iff K).mpr ⟨1, RingHom.mem_fieldRange_self _ x⟩

end PuiseuxSeries
