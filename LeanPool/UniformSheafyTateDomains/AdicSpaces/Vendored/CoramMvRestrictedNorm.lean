/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram

VENDORED into AINTLIB (2026-07-04) from WilliamCoram/PhD (PhD/ToPR/MvRestricted.lean),
pending its mathlib PR. Import paths redirected to this workspace's vendored copies.
-/
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Order.Lex
import Mathlib.Data.Finsupp.Lex
import LeanPool.UniformSheafyTateDomains.AdicSpaces.Vendored.CoramMvGaussNorm

/-! # Norm instances on multivariate restricted power series (vendored) -/




variable {R : Type*} {σ : Type*} (c : σ → ℝ)

/-- Every coordinate of the given radius vector is strictly positive. -/
class StrongPos (c : σ → ℝ) : Prop where pos : ∀ i, 0 < c i

lemma StrongPos_pos [StrongPos c] : ∀ i, 0 < c i := fun i => StrongPos.pos i

theorem strongPos_of_forall_pos (hc : ∀ i, 0 < c i) : StrongPos c := {pos := hc}

theorem strongPos_const_of_pos (c : ℝ) (hc : 0 < c) : StrongPos (fun _ : Unit ↦ c) :=
  {pos := fun _ => hc}

lemma StrongPos_unit_iff (c : ℝ) : StrongPos (fun _ : Unit ↦ c) ↔ 0 < c := by
  constructor
  · exact fun _ ↦ StrongPos_pos (fun _ : Unit ↦ c) 0
  · exact fun h ↦ {pos := fun _ ↦ h}
namespace MvRestricted

variable (R) in
/-- The weighted Gauss norm of a multivariate restricted power series. -/
noncomputable
abbrev gaussNorm [NormedRing R] [IsUltrametricDist R] (f : MvPowerSeries.Restricted R c) : ℝ :=
  MvPowerSeries.gaussNorm (norm : R → ℝ) c f.1

lemma hasGaussNorm [NormedRing R] [IsUltrametricDist R] (f : MvPowerSeries.Restricted R c) :
  MvPowerSeries.HasGaussNorm norm c f.1 := Filter.Tendsto.bddAbove_range_of_cofinite f.2

/-- The Gauss ring norm on multivariate restricted power series with positive radii. -/
noncomputable
def isRingNorm [NormedRing R] [IsUltrametricDist R] [StrongPos c] :
    RingNorm (MvPowerSeries.Restricted R c) where
  toFun f := gaussNorm R c f
  map_zero' := MvPowerSeries.gaussNorm_zero norm c norm_zero
  add_le' f g := by
    have h := MvPowerSeries.gaussNorm_add_le_max norm c f.1 g.1 (StrongLT.le (StrongPos_pos c))
      norm_nonneg (IsUltrametricDist.norm_add_le_max) (hasGaussNorm c f) (hasGaussNorm c g)
    have : max (gaussNorm R c f) (gaussNorm R c g) ≤
        gaussNorm R c f + gaussNorm R c g := by
      refine max_le_add_of_nonneg ?_ ?_
      all_goals exact (MvPowerSeries.gaussNorm_nonneg norm c _ norm_nonneg)
    exact h.trans this
  neg' f := MvPowerSeries.gaussNorm_neg norm c norm_neg f.1
  mul_le' f g := MvPowerSeries.gaussNorm_mul_le norm c f.1 g.1 (StrongLT.le (StrongPos_pos c))
    norm_nonneg norm_mul_le IsUltrametricDist.norm_add_le_max norm_zero (hasGaussNorm c f)
    (hasGaussNorm c g)
  eq_zero_of_map_eq_zero' f hf := by
    refine Subtype.ext ?_
    exact (MvPowerSeries.gaussNorm_eq_zero_iff norm c f.1 norm_zero norm_nonneg (by aesop)
      (StrongPos_pos c) (hasGaussNorm c f)).mp hf

variable (R) in
noncomputable
instance isNormedRing [NormedRing R] [IsUltrametricDist R] [StrongPos c] :
  NormedRing (MvPowerSeries.Restricted R c) := RingNorm.toNormedRing (isRingNorm c)

lemma norm_eq [NormedRing R] [IsUltrametricDist R] [StrongPos c] (f : MvPowerSeries.Restricted R
  c) :
    ‖f‖ = MvPowerSeries.gaussNorm (norm : R → ℝ) c f.1 := by rfl

variable (R) in
/-- The weighted Gauss norm satisfies the nonarchimedean triangle inequality. -/
theorem isNonarchimedean [NormedRing R] [IsUltrametricDist R] [StrongPos c] :
    IsNonarchimedean (R := ℝ) (α := MvPowerSeries.Restricted R c) norm :=
  fun f g => MvPowerSeries.gaussNorm_add_le_max norm c f.1 g.1 (StrongLT.le (StrongPos_pos c))
    norm_nonneg IsUltrametricDist.norm_add_le_max (hasGaussNorm c f) (hasGaussNorm c g)

variable (R) in
noncomputable
instance isUltrametricDist
    [NormedRing R] [IsUltrametricDist R] [StrongPos c] :
    IsUltrametricDist (MvPowerSeries.Restricted R c) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (isNonarchimedean R c)

section AbsoluteValue

private lemma restrictedFinZeroEquiv (hc : ∀ i, 0 ≤ c i) (t : σ →₀ ℕ) : 0 ≤ t.prod (c · ^ ·) :=
  Finset.prod_nonneg (fun i _ ↦ pow_nonneg (hc i) (t i))

lemma gaussNorm_achieved [NormedRing R] [IsUltrametricDist R] (hc : 0 ≤ c)
    (f : MvPowerSeries.Restricted R c) :
    ∃ a, MvPowerSeries.AchievesGaussNorm norm c f.1 a := by
  simp_rw [MvPowerSeries.AchievesGaussNorm]
  by_cases hG : gaussNorm R c f = 0
  · use 0
    have := MvPowerSeries.le_gaussNorm norm c f.1 (hasGaussNorm c f) 0
    simp only [hG] at this ⊢
    exact le_antisymm this (mul_nonneg (norm_nonneg _) (restrictedFinZeroEquiv c hc 0))
  · have hpos : 0 < gaussNorm R c f :=
      (MvPowerSeries.gaussNorm_nonneg norm c f.1 norm_nonneg).lt_of_ne' hG
    have hfin : {t | gaussNorm R c f / 2 ≤ ‖MvPowerSeries.coeff t f.1‖ * t.prod (c · ^
      ·)}.Finite := by
      have : MvPowerSeries.IsRestrictedGauss c f.1 := f.2
      simp_rw [MvPowerSeries.IsRestrictedGauss, NormedAddGroup.tendsto_nhds_zero] at this
      have := this (gaussNorm R c f / 2) (by aesop)
      simp only [norm_mul, Real.norm_eq_abs, Filter.eventually_cofinite, not_lt, abs_norm] at this
      have habs : ∀ t : σ →₀ ℕ, |t.prod (c · ^ ·)| = t.prod (c · ^ ·) :=
        fun t => abs_of_nonneg (restrictedFinZeroEquiv c hc t)
      simp only [habs] at this
      exact this
    have hne : {t | gaussNorm R c f / 2 ≤ ‖MvPowerSeries.coeff t f.1‖ * t.prod (c · ^
      ·)}.Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have hlt : gaussNorm R c f ≤ gaussNorm R c f / 2 := by
        apply ciSup_le
        intro t
        have : t ∉ {t | gaussNorm R c f / 2 ≤ ‖MvPowerSeries.coeff t f.1‖ * t.prod (c · ^ ·)} := by
          simp [hemp]
        grind
      linarith
    obtain ⟨m, hm_mem, hm_max⟩ := hfin.toFinset.exists_max_image
      (fun t ↦ ‖MvPowerSeries.coeff t f.1‖ * t.prod (c · ^ ·)) (by aesop)
    use m
    apply le_antisymm (MvPowerSeries.le_gaussNorm norm c f.1 (hasGaussNorm c f) m)
    apply ciSup_le
    intro t
    by_cases ht : t ∈ {t | gaussNorm R c f / 2 ≤ ‖MvPowerSeries.coeff t f.1‖ * t.prod (c · ^ ·)}
    · exact hm_max t (by aesop)
    · exact le_trans (le_of_lt (by aesop)) (by aesop)

lemma achievingPoints_finite [NormedRing R] [IsUltrametricDist R] (hc : 0 ≤ c)
    (f : MvPowerSeries.Restricted R c) (h : gaussNorm R c f ≠ 0) :
    {a | MvPowerSeries.AchievesGaussNorm norm c f.1 a}.Finite := by
  simp_rw [MvPowerSeries.AchievesGaussNorm]
  have hpos : 0 < gaussNorm R c f :=
      (MvPowerSeries.gaussNorm_nonneg norm c f.1 norm_nonneg).lt_of_ne' h
  have hfin : {t | gaussNorm R c f / 2 ≤ ‖MvPowerSeries.coeff t f.1‖ * t.prod (c · ^ ·)}.Finite
    := by
      have : MvPowerSeries.IsRestrictedGauss c f.1 := f.2
      simp_rw [MvPowerSeries.IsRestrictedGauss, NormedAddGroup.tendsto_nhds_zero] at this
      have := this (gaussNorm R c f / 2) (by aesop)
      simp only [norm_mul, Real.norm_eq_abs, Filter.eventually_cofinite, not_lt, abs_norm] at this
      have habs : ∀ t : σ →₀ ℕ, |t.prod (c · ^ ·)| = t.prod (c · ^ ·) :=
        fun t => abs_of_nonneg (restrictedFinZeroEquiv c hc t)
      simp only [habs] at this
      exact this
  refine Set.Finite.subset hfin ?_
  grind

lemma test (hc : ∀ (i : σ), 0 < c i) : 0 ≤ c := by
  intro i
  exact Std.le_of_lt (hc i)

private lemma exists_lex_max_achieving [NormedRing R] [IsUltrametricDist R] [LinearOrder σ]
    (hc : 0 ≤ c) (f : MvPowerSeries.Restricted R c) (hf : gaussNorm R c f ≠ 0) :
    ∃ i, MvPowerSeries.AchievesGaussNorm norm c f.1 i ∧
      ∀ a, MvPowerSeries.AchievesGaussNorm norm c f.1 a → toLex a ≤ toLex i := by
  classical
  have hfin := achievingPoints_finite c hc f hf
  obtain ⟨a₀, ha₀⟩ := gaussNorm_achieved c hc f
  obtain ⟨i, hiF, hiMax⟩ := hfin.toFinset.exists_max_image (fun a => toLex a)
    ⟨a₀, hfin.mem_toFinset.mpr ha₀⟩
  exact ⟨i, hfin.mem_toFinset.mp hiF, fun a ha => hiMax a (hfin.mem_toFinset.mpr ha)⟩

/-- **Gauss dominance** (the strict-drop input to `gaussNorm_mul_eq_mul`): the
lexicographically largest achieving indices of `f` and `g` strictly dominate every other
point of their antidiagonal. Needs only submultiplicativity of the coefficient norm. -/
lemma bar [NormedRing R] [IsUltrametricDist R] [LinearOrder σ] (hc : ∀ i, 0 < c i)
    (f g : MvPowerSeries.Restricted R c) (hf : gaussNorm R c f ≠ 0) (hg : gaussNorm R c g ≠ 0) :
    ∃ i j, MvPowerSeries.AchievesGaussNorm norm c f.1 i ∧
      MvPowerSeries.AchievesGaussNorm norm c g.1 j ∧
      ∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
      norm (MvPowerSeries.coeff p.1 f.1 * MvPowerSeries.coeff p.2 g.1) <
      norm (MvPowerSeries.coeff i f.1) * norm (MvPowerSeries.coeff j g.1) := by
  classical
  have hc' : (0 : σ → ℝ) ≤ c := fun i => (hc i).le
  have hfpos : 0 < gaussNorm R c f :=
    (MvPowerSeries.gaussNorm_nonneg norm c f.1 norm_nonneg).lt_of_ne' hf
  have hgpos : 0 < gaussNorm R c g :=
    (MvPowerSeries.gaussNorm_nonneg norm c g.1 norm_nonneg).lt_of_ne' hg
  have hw : ∀ t : σ →₀ ℕ, (0 : ℝ) < t.prod (c · ^ ·) :=
    fun t => Finset.prod_pos fun k _ => pow_pos (hc k) _
  obtain ⟨i, hiA, hiMax⟩ := exists_lex_max_achieving c hc' f hf
  obtain ⟨j, hjA, hjMax⟩ := exists_lex_max_achieving c hc' g hg
  refine ⟨i, j, hiA, hjA, fun p hp hne => ?_⟩
  rw [Finset.mem_antidiagonal] at hp
  -- one component is lexicographically strictly above its maximum achiever
  have hcase : toLex i < toLex p.1 ∨ toLex j < toLex p.2 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    rcases lt_or_eq_of_le h1 with h1' | h1'
    · have hstrict : toLex (p.1 + p.2) < toLex (i + j) := by
        have := add_lt_add_of_lt_of_le h1' h2
        exact this
      rw [hp] at hstrict
      exact lt_irrefl _ hstrict
    · have hp1 : p.1 = i := by
        have := h1'
        exact toLex.injective this
      have hp2 : p.2 = j := by
        rw [hp1] at hp
        exact add_left_cancel hp
      exact hne (Prod.ext hp1 hp2)
  -- weight bookkeeping: the antidiagonal preserves the total weight
  have hww : (p.1).prod (c · ^ ·) * (p.2).prod (c · ^ ·) =
      i.prod (c · ^ ·) * j.prod (c · ^ ·) := by
    rw [← Finsupp.prod_add_index' (fun a => pow_zero (c a)) (fun a m n => pow_add (c a) m n),
      ← Finsupp.prod_add_index' (fun a => pow_zero (c a)) (fun a m n => pow_add (c a) m n), hp]
  -- the strict product bound at the weighted level
  have hweighted :
      (norm (MvPowerSeries.coeff p.1 f.1) * (p.1).prod (c · ^ ·)) *
        (norm (MvPowerSeries.coeff p.2 g.1) * (p.2).prod (c · ^ ·)) <
      gaussNorm R c f * gaussNorm R c g := by
    rcases hcase with hgt | hgt
    · have hp1_not : ¬ MvPowerSeries.AchievesGaussNorm norm c f.1 p.1 :=
        fun hach => absurd (hiMax p.1 hach) (not_le.mpr hgt)
      have hf_lt : norm (MvPowerSeries.coeff p.1 f.1) * (p.1).prod (c · ^ ·) <
          gaussNorm R c f :=
        lt_of_le_of_ne (MvPowerSeries.le_gaussNorm norm c f.1 (hasGaussNorm c f) p.1) hp1_not
      have hg_le : norm (MvPowerSeries.coeff p.2 g.1) * (p.2).prod (c · ^ ·) ≤
          gaussNorm R c g :=
        MvPowerSeries.le_gaussNorm norm c g.1 (hasGaussNorm c g) p.2
      rcases eq_or_lt_of_le (mul_nonneg (norm_nonneg (MvPowerSeries.coeff p.2 g.1))
          (hw p.2).le) with h0 | hpos
      · rw [← h0, mul_zero]
        exact mul_pos hfpos hgpos
      · exact mul_lt_mul hf_lt hg_le hpos hfpos.le
    · have hp2_not : ¬ MvPowerSeries.AchievesGaussNorm norm c g.1 p.2 :=
        fun hach => absurd (hjMax p.2 hach) (not_le.mpr hgt)
      have hg_lt : norm (MvPowerSeries.coeff p.2 g.1) * (p.2).prod (c · ^ ·) <
          gaussNorm R c g :=
        lt_of_le_of_ne (MvPowerSeries.le_gaussNorm norm c g.1 (hasGaussNorm c g) p.2) hp2_not
      have hf_le : norm (MvPowerSeries.coeff p.1 f.1) * (p.1).prod (c · ^ ·) ≤
          gaussNorm R c f :=
        MvPowerSeries.le_gaussNorm norm c f.1 (hasGaussNorm c f) p.1
      rcases eq_or_lt_of_le (mul_nonneg (norm_nonneg (MvPowerSeries.coeff p.1 f.1))
          (hw p.1).le) with h0 | hpos
      · rw [← h0, zero_mul]
        exact mul_pos hfpos hgpos
      · calc (norm (MvPowerSeries.coeff p.1 f.1) * (p.1).prod (c · ^ ·)) *
              (norm (MvPowerSeries.coeff p.2 g.1) * (p.2).prod (c · ^ ·))
            = (norm (MvPowerSeries.coeff p.2 g.1) * (p.2).prod (c · ^ ·)) *
              (norm (MvPowerSeries.coeff p.1 f.1) * (p.1).prod (c · ^ ·)) := by ring
          _ < gaussNorm R c g * gaussNorm R c f :=
              mul_lt_mul hg_lt hf_le hpos hgpos.le
          _ = gaussNorm R c f * gaussNorm R c g := by ring
  -- cancel the (equal, positive) weights and conclude via submultiplicativity
  have hGf : gaussNorm R c f = norm (MvPowerSeries.coeff i f.1) * i.prod (c · ^ ·) := hiA.symm
  have hGg : gaussNorm R c g = norm (MvPowerSeries.coeff j g.1) * j.prod (c · ^ ·) := hjA.symm
  rw [hGf, hGg] at hweighted
  have hkey : norm (MvPowerSeries.coeff p.1 f.1) * norm (MvPowerSeries.coeff p.2 g.1) <
      norm (MvPowerSeries.coeff i f.1) * norm (MvPowerSeries.coeff j g.1) := by
    have hwpos : (0 : ℝ) < i.prod (c · ^ ·) * j.prod (c · ^ ·) :=
      mul_pos (hw i) (hw j)
    refine lt_of_mul_lt_mul_right ?_ hwpos.le
    calc norm (MvPowerSeries.coeff p.1 f.1) * norm (MvPowerSeries.coeff p.2 g.1) *
          (i.prod (c · ^ ·) * j.prod (c · ^ ·))
        = norm (MvPowerSeries.coeff p.1 f.1) * norm (MvPowerSeries.coeff p.2 g.1) *
          ((p.1).prod (c · ^ ·) * (p.2).prod (c · ^ ·)) := by rw [hww]
      _ = (norm (MvPowerSeries.coeff p.1 f.1) * (p.1).prod (c · ^ ·)) *
          (norm (MvPowerSeries.coeff p.2 g.1) * (p.2).prod (c · ^ ·)) := by ring
      _ < (norm (MvPowerSeries.coeff i f.1) * i.prod (c · ^ ·)) *
          (norm (MvPowerSeries.coeff j g.1) * j.prod (c · ^ ·)) := hweighted
      _ = norm (MvPowerSeries.coeff i f.1) * norm (MvPowerSeries.coeff j g.1) *
          (i.prod (c · ^ ·) * j.prod (c · ^ ·)) := by ring
  exact lt_of_le_of_lt (norm_mul_le _ _) hkey

/-- A multiplicative coefficient norm induces a multiplicative Gauss absolute value. -/
theorem isAbsoluteValue [NormedRing R] [IsUltrametricDist R] [LinearOrder σ] [StrongPos c]
    (hnorm : ∀ a b : R, norm (a * b) = norm a * norm b) : IsAbsoluteValue (gaussNorm R c) where
  abv_nonneg' g := MvPowerSeries.gaussNorm_nonneg norm c g.1 norm_nonneg
  abv_eq_zero' := by
    intro g
    convert MvPowerSeries.gaussNorm_eq_zero_iff norm c g.1 norm_zero norm_nonneg (by aesop)
      (StrongPos_pos c) (hasGaussNorm c g)
    exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
  abv_add' f g := (MvPowerSeries.gaussNorm_add_le_max norm c f.1 g.1 (StrongLT.le (StrongPos_pos c))
    norm_nonneg IsUltrametricDist.norm_add_le_max (hasGaussNorm c f) (hasGaussNorm c g)).trans
    (max_le_add_of_nonneg (MvPowerSeries.gaussNorm_nonneg norm c _ norm_nonneg)
    (MvPowerSeries.gaussNorm_nonneg norm c _ norm_nonneg))
  abv_mul' f g := by
    by_cases h1 : gaussNorm R c f = 0
    · simp only [h1, zero_mul]
      suffices f * g = 0 by
        rw [this]
        change MvPowerSeries.gaussNorm norm c ((0 : MvPowerSeries.Restricted R c)).1 = 0
        rw [show ((0 : MvPowerSeries.Restricted R c)).1 = (0 : MvPowerSeries σ R) from rfl]
        exact MvPowerSeries.gaussNorm_zero norm c norm_zero
      suffices f = 0 by
        rw [this, zero_mul]
      convert (MvPowerSeries.gaussNorm_eq_zero_iff norm c f.1 norm_zero norm_nonneg (by aesop)
        (StrongPos_pos c) (hasGaussNorm c f)).mp h1
      exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
    by_cases h2 : gaussNorm R c g = 0
    · simp only [h2, mul_zero]
      suffices f * g = 0 by
        rw [this]
        change MvPowerSeries.gaussNorm norm c ((0 : MvPowerSeries.Restricted R c)).1 = 0
        rw [show ((0 : MvPowerSeries.Restricted R c)).1 = (0 : MvPowerSeries σ R) from rfl]
        exact MvPowerSeries.gaussNorm_zero norm c norm_zero
      suffices g = 0 by
        rw [this, mul_zero]
      convert (MvPowerSeries.gaussNorm_eq_zero_iff norm c g.1 norm_zero norm_nonneg (by aesop)
        (StrongPos_pos c) (hasGaussNorm c g)).mp h2
      exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
    exact MvPowerSeries.gaussNorm_mul_eq_mul norm c f.1 g.1 (hasGaussNorm c f) (hasGaussNorm c g)
      (hasGaussNorm c (f * g)) norm_nonneg norm_zero IsUltrametricDist.isNonarchimedean_norm hnorm
      norm_neg (by aesop) (StrongPos_pos c) (bar c (StrongPos_pos c) f g h1 h2)

end AbsoluteValue

end MvRestricted

section MvPolynomial

lemma MvPolynomial.IsRestrictedGauss [NormedCommRing R] (f : MvPolynomial σ R) :
    MvPowerSeries.IsRestrictedGauss c f.toMvPowerSeries := by
  suffices {t | ¬ (‖(MvPowerSeries.coeff t) f.toMvPowerSeries‖ * t.prod (c · ^ ·) = 0)}.Finite by
    exact tendsto_nhds_of_eventually_eq this
  simp only [coeff_coe, mul_eq_zero, norm_eq_zero, not_or, ← mem_support_iff]
  exact Set.Finite.sep (Finset.finite_toSet _) _

/-- View a polynomial as a restricted power series for the given radii. -/
def MvPolynomial.toMvRestricted [NormedCommRing R] [IsUltrametricDist R]
    (f : MvPolynomial σ R) : MvPowerSeries.Restricted R c :=
  ⟨f.toMvPowerSeries, MvPolynomial.IsRestrictedGauss c f⟩

end MvPolynomial
