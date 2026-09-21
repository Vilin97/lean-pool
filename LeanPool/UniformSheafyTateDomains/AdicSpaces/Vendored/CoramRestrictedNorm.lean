/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram

VENDORED into AINTLIB (2026-07-04) from WilliamCoram/PhD (unmerged parts of
PhD/ToPR/GaussNorm.lean + PhD/ToPR/Restricted.lean), building on the merged
`Mathlib.RingTheory.PowerSeries.{Restricted, GaussNorm}`.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.Vendored.CoramRestrictedCore
import Mathlib.RingTheory.PowerSeries.GaussNorm
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import LeanPool.UniformSheafyTateDomains.AdicSpaces.Vendored.CoramMvRestrictedNorm

/-! # Univariate restricted power series: subring, type, Gauss norm instances (vendored) -/

namespace PowerSeries

variable {R : Type*} (v : R → ℝ) (c : ℝ)

section Semiring

variable [Semiring R] (f : PowerSeries R)

lemma hasGaussNorm_iff :
    HasGaussNorm v c f ↔ BddAbove (Set.range (fun (t : ℕ) ↦ (v (coeff t f) * c ^ t))) := by
  constructor
  all_goals
  intro hf
  suffices (Set.range (fun (t : ℕ) ↦ (v (coeff t f) * c ^ t))) =
      Set.range fun t ↦ v ((MvPowerSeries.coeff t) f) * t.prod fun _ x2 ↦ c ^ x2 by
    simpa only [HasGaussNorm, MvPowerSeries.HasGaussNorm, ← this] using hf
  refine Set.ext (fun _ ↦ ?_)
  simp only [Set.mem_range, Finsupp.prod_pow, Finset.univ_unique, PUnit.default_eq_unit,
    Finset.prod_singleton]
  constructor
  · intro h
    obtain ⟨y, _⟩ := h
    use Finsupp.single () y
    aesop
  · intro h
    obtain ⟨y, hy⟩ := h
    use (y PUnit.unit)
    simpa [coeff, show (Finsupp.single () (y PUnit.unit)) = y by grind]


lemma gaussNorm_pos (hf : f ≠ 0) (vZero : v 0 = 0) (vNonneg : ∀ a, v a ≥ 0)
    (h_eq_zero : ∀ x : R, v x = 0 → x = 0) (hc : 0 < c) (hbd : HasGaussNorm v c f) :
    0 < gaussNorm v c f := by
  contrapose hf
  exact (gaussNorm_eq_zero_iff v c f vZero vNonneg h_eq_zero hc hbd).mp (le_antisymm (by grind)
    (gaussNorm_nonneg v c f vNonneg))



end Semiring

variable [Ring R] (f : PowerSeries R)

lemma gaussNorm_neg (vNeg : ∀ x, v (-x) = v x) :
    gaussNorm v c (-f) = gaussNorm v c f :=
  MvPowerSeries.gaussNorm_neg v (fun _ ↦ c) vNeg f

lemma gaussNorm_mul_le (f g : PowerSeries R) (hc : 0 ≤ c) (vNonneg : ∀ a, v a ≥ 0)
    (vMul : ∀ a b, v (a * b) ≤ v a * v b) (vUltra : ∀ a b, v (a + b) ≤ max (v a) (v b))
    (vZero : v 0 = 0) (hbfd : HasGaussNorm v c f) (hbgd : HasGaussNorm v c g) :
    gaussNorm v c (f * g) ≤ gaussNorm v c f * gaussNorm v c g :=
  MvPowerSeries.gaussNorm_mul_le v (fun _ ↦ c) f g (fun _ => by simp [hc]) vNonneg vMul vUltra vZero
    hbfd.hasMvGaussNorm hbgd.hasMvGaussNorm

section absoluteValue

/-- The weighted coefficient of the given degree attains the Gauss norm. -/
abbrev achievesGaussNorm (i : ℕ) : Prop :=
  MvPowerSeries.AchievesGaussNorm v (fun _ ↦ c) f (Finsupp.single () i)

lemma achievesGaussNorm_iff (i : ℕ) : achievesGaussNorm v c f i ↔
    v (coeff i f) * c ^ i = gaussNorm v c f := by
  simp [achievesGaussNorm, MvPowerSeries.AchievesGaussNorm, PowerSeries.coeff]

lemma exists_antidiagDom_iff_exists_mvAntidiagDom (f g : PowerSeries R) :
    (∃ i j,
    achievesGaussNorm v c f i ∧ achievesGaussNorm v c g j ∧
    ∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
    v (coeff p.1 f * coeff p.2 g) < v (coeff i f) * v (coeff j g)) ↔
    (∃ i j, MvPowerSeries.AchievesGaussNorm v (fun _ ↦ c) f i ∧
    MvPowerSeries.AchievesGaussNorm v (fun _ ↦ c) g j ∧∀ p ∈ Finset.antidiagonal (i + j),
    p ≠ (i, j) → v ((MvPowerSeries.coeff p.1) f * (MvPowerSeries.coeff p.2) g) <
    v ((MvPowerSeries.coeff i) f) * v ((MvPowerSeries.coeff j) g)) := by
  constructor
  · intro hdom
    obtain ⟨i, j, hi, hj, hdom'⟩ := hdom
    refine ⟨Finsupp.single () i, Finsupp.single () j, hi, hj,
      ?_⟩
    intro p hp _
    have hp1 : p.1 = Finsupp.single () (p.1 ()) := by grind
    have hp2 : p.2 = Finsupp.single () (p.2 ()) := by grind
    rw [hp1, hp2]
    exact hdom' (p.1 (), p.2 ()) (Finset.mem_antidiagonal.mpr
      (by simpa using congrArg (· ()) (Finset.mem_antidiagonal.mp hp))) (by grind)
  · intro hdom
    obtain ⟨i, j, hi, hj, hdom'⟩ := hdom
    refine ⟨i PUnit.unit, j PUnit.unit, by simpa [achievesGaussNorm,
      show (Finsupp.single () (i PUnit.unit)) = i by grind],
      by simpa [achievesGaussNorm, show (Finsupp.single () (j PUnit.unit)) = j by grind], ?_⟩
    intro p hp _
    simpa [coeff, show (Finsupp.single () (i PUnit.unit)) = i by grind, show (Finsupp.single ()
      (j PUnit.unit)) = j by grind] using hdom' (Finsupp.single () p.1, (Finsupp.single () p.2))
      (Finset.mem_antidiagonal.mpr (by aesop)) (by grind)

lemma gaussNorm_le_mul (f g : PowerSeries R)
    (vMulEq : ∀ a b, v (a * b) = v a * v b) (vUltra : ∀ a b, v (a + b) ≤ max (v a) (v b))
    (vNeg : ∀ a, v a = v (-a)) (hbfg : HasGaussNorm v c (f * g))
    (hdom : ∃ i j, achievesGaussNorm v c f i ∧ achievesGaussNorm v c g j ∧
      ∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
        v (coeff p.1 f * coeff p.2 g) < v (coeff i f) * v (coeff j g)) :
    gaussNorm v c f * gaussNorm v c g ≤ gaussNorm v c (f * g) :=
  MvPowerSeries.gaussNorm_le_mul v (fun _ ↦ c) f g vMulEq vUltra vNeg hbfg.hasMvGaussNorm
    ((exists_antidiagDom_iff_exists_mvAntidiagDom v c f g).mp hdom)

lemma gaussNorm_mul_eq_mul (f g : PowerSeries R)
    (hf : HasGaussNorm v c f) (hg : HasGaussNorm v c g) (hfg : HasGaussNorm v c (f * g))
    (vNonneg : ∀ a, v a ≥ 0) (vZero : v 0 = 0) (vNA : IsNonarchimedean v)
    (vMulEq : ∀ (a b : R), v (a * b) = v a * v b) (vNeg : ∀ (a : R), v (-a) = v a)
    (h_eq_zero : ∀ (x : R), v x = 0 → x = 0) (hc : 0 < c)
    (hdom : ∃ i j, achievesGaussNorm v c f i ∧ achievesGaussNorm v c g j ∧
      ∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) → v (coeff p.1 f * coeff p.2 g) <
      v (coeff i f) * v (coeff j g)) :
    gaussNorm v c (f * g) = gaussNorm v c f * gaussNorm v c g :=
  MvPowerSeries.gaussNorm_mul_eq_mul v (fun _ ↦ c) f g hf.hasMvGaussNorm hg.hasMvGaussNorm
    hfg.hasMvGaussNorm vNonneg vZero vNA vMulEq vNeg h_eq_zero (by grind)
    ((exists_antidiagDom_iff_exists_mvAntidiagDom v c f g).mp hdom)

end absoluteValue

end PowerSeries

namespace PowerSeries

variable {R : Type*} [NormedRing R] (c : ℝ)

/-- The additive subgroup of power series whose weighted coefficients tend to zero. -/
def isAddSubgroup (c : ℝ) : AddSubgroup (PowerSeries R) where
  carrier := IsRestricted c
  zero_mem' := IsRestricted.zero c
  add_mem' := IsRestricted.add c
  neg_mem' := IsRestricted.neg c

variable [IsUltrametricDist R]

/-- Ring structure on `MvPowerSeries σ R`. -/
def isSubring (c : ℝ) : Subring (PowerSeries R) where
  __ := isAddSubgroup c
  one_mem' := IsRestricted.one c
  mul_mem' := IsRestricted.mul c

variable (R) in
/-- The type of restricted `MvPowerSeries σ R`. -/
def Restricted (c : ℝ) : Type _ := isSubring (R := R) c

/-- A coefficient viewed as a constant restricted power series. -/
noncomputable
def Restricted.C (c : ℝ) (a : R) : Restricted R c :=
  ⟨PowerSeries.C a, IsRestricted.C c a⟩

/-- Ring structure on `Restricted R c`. -/
noncomputable
instance (c : ℝ) : Ring (Restricted R c) :=
  Subring.toRing (isSubring c)

end PowerSeries

namespace PowerSeries

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- `CommRing` structure on `Restricted R c` when `R` is a `NormedCommRing`. -/
noncomputable
instance (c : ℝ) : CommRing (Restricted R c) :=
  Subring.toCommRing (R := PowerSeries R) (isSubring c)

end PowerSeries

namespace Restricted

open Filter Topology

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] (c : ℝ)

variable (R) in
/-- The Gauss norm on univariate restricted power series. -/
noncomputable
abbrev gaussNorm (f : PowerSeries.Restricted R c) : ℝ :=
  PowerSeries.gaussNorm (norm : R → ℝ) c f.1

omit [IsUltrametricDist R] in
/-- Merged mathlib states `PowerSeries.IsRestricted` via `atTop`; on `ℕ` this is the
cofinite filter. -/
lemma isRestricted_iff_cofinite {f : PowerSeries R} :
    PowerSeries.IsRestricted c f ↔
      Filter.Tendsto (fun i : ℕ => ‖PowerSeries.coeff i f‖ * c ^ i)
        Filter.cofinite (nhds 0) := by
  rw [PowerSeries.IsRestricted, Nat.cofinite_eq_atTop]

lemma hasGaussNorm (f : PowerSeries.Restricted R c) :
    PowerSeries.HasGaussNorm norm c f.1 :=
  Filter.Tendsto.bddAbove_range_of_cofinite
    ((isRestricted_iff_cofinite c).mp f.2)

variable [StrongPos (fun _ : Unit ↦ c)]

lemma c_pos : (0 : ℝ) < c := StrongPos_pos (fun _ : Unit ↦ c) ()

/-- The Gauss ring norm on restricted power series of positive radius. -/
noncomputable
def isRingNorm : RingNorm (PowerSeries.Restricted R c) where
  toFun f := gaussNorm R c f
  map_zero' := by
    change PowerSeries.gaussNorm norm c ((0 : PowerSeries.Restricted R c)).1 = 0
    rw [show ((0 : PowerSeries.Restricted R c)).1 = (0 : PowerSeries R) from rfl]
    exact PowerSeries.gaussNorm_zero norm c norm_zero
  add_le' f g := by
    have h := PowerSeries.gaussNorm_add_le_max norm c f.1 g.1 (c_pos c).le
      norm_nonneg (IsUltrametricDist.norm_add_le_max) (hasGaussNorm c f) (hasGaussNorm c g)
    refine h.trans (max_le_add_of_nonneg ?_ ?_)
    all_goals exact PowerSeries.gaussNorm_nonneg norm c _ norm_nonneg
  neg' f := by
    change PowerSeries.gaussNorm norm c ((-f).1) = PowerSeries.gaussNorm norm c f.1
    rw [show ((-f).1) = -(f.1) from rfl]
    exact PowerSeries.gaussNorm_neg norm c (f := f.1) norm_neg
  mul_le' f g := PowerSeries.gaussNorm_mul_le norm c f.1 g.1 (c_pos c).le
    norm_nonneg norm_mul_le IsUltrametricDist.norm_add_le_max norm_zero
    (hasGaussNorm c f) (hasGaussNorm c g)
  eq_zero_of_map_eq_zero' f hf := by
    refine Subtype.ext ?_
    exact (PowerSeries.gaussNorm_eq_zero_iff norm c f.1 norm_zero norm_nonneg (by aesop)
      (c_pos c) (hasGaussNorm c f)).mp hf

variable (R) in
noncomputable
instance isNormedRing : NormedRing (PowerSeries.Restricted R c) :=
  RingNorm.toNormedRing (isRingNorm c)

noncomputable
instance isNormedCommRing (S : Type*) [NormedCommRing S] [IsUltrametricDist S] :
    NormedCommRing (PowerSeries.Restricted S c) where
  toNormedRing := isNormedRing S c
  mul_comm := mul_comm

lemma norm_eq (f : PowerSeries.Restricted R c) :
    ‖f‖ = PowerSeries.gaussNorm (norm : R → ℝ) c f.1 := rfl

theorem isNonarchimedean :
    IsNonarchimedean (R := ℝ) (α := PowerSeries.Restricted R c) norm :=
  fun f g => PowerSeries.gaussNorm_add_le_max norm c f.1 g.1 (c_pos c).le norm_nonneg
    IsUltrametricDist.norm_add_le_max (hasGaussNorm c f) (hasGaussNorm c g)

noncomputable
instance isUltrametricDist :
    IsUltrametricDist (PowerSeries.Restricted R c) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean (R := R) c)

instance isCompleteSpace [CompleteSpace R] : CompleteSpace (PowerSeries.Restricted R c) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  have hc : (0 : ℝ) < c := StrongPos_pos (fun _ : Unit ↦ c) ()
  have hcn : ∀ n : ℕ, (0 : ℝ) < c ^ n := fun n => pow_pos hc n
  -- Step 1: the Gauss norm bounds each coefficient: `‖coeff n f.1 - coeff n g.1‖ * c^n ≤ ‖f - g‖`.
  have coeff_le : ∀ (f g : PowerSeries.Restricted R c) (n : ℕ),
      ‖PowerSeries.coeff n f.1 - PowerSeries.coeff n g.1‖ * c ^ n ≤ ‖f - g‖ := fun f g n => by
    have heq : PowerSeries.coeff n f.1 - PowerSeries.coeff n g.1 =
        PowerSeries.coeff n (f - g).1 := by
      change _ = PowerSeries.coeff n (f.1 - g.1)
      exact (map_sub _ _ _).symm
    rw [heq]
    exact PowerSeries.le_gaussNorm norm c (f - g).1 (hasGaussNorm c (f - g)) n
  -- Step 2: each coefficient sequence is Cauchy in `R`.
  have coeff_cauchy : ∀ n : ℕ, CauchySeq (fun i => PowerSeries.coeff n (u i).1) := fun n => by
    refine Metric.cauchySeq_iff.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu (ε * c ^ n) (mul_pos hε (hcn n))
    refine ⟨N, fun i hi j hj => ?_⟩
    rw [dist_eq_norm]
    have h_uij : ‖u i - u j‖ < ε * c ^ n := by
      have := hN i hi j hj; rwa [dist_eq_norm] at this
    exact lt_of_mul_lt_mul_right ((coeff_le (u i) (u j) n).trans_lt h_uij) (hcn n).le
  -- Step 3: take pointwise limits in `R` and build the candidate restricted power series.
  choose a ha using fun n => cauchySeq_tendsto_of_complete (coeff_cauchy n)
  set f : PowerSeries R := PowerSeries.mk a with hf_def
  have coeff_f : ∀ n, PowerSeries.coeff n f = a n := fun n => by simp [f]
  -- Step 4: uniform-in-`n` convergence, obtained by letting `j → ∞` in the Cauchy property.
  have unif_conv : ∀ ε > (0 : ℝ), ∃ N, ∀ i ≥ N, ∀ n,
      ‖PowerSeries.coeff n (u i).1 - a n‖ * c ^ n ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
    refine ⟨N, fun i hi n => ?_⟩
    have h_lim : Tendsto
        (fun j => ‖PowerSeries.coeff n (u i).1 - PowerSeries.coeff n (u j).1‖ * c ^ n)
        atTop (𝓝 (‖PowerSeries.coeff n (u i).1 - a n‖ * c ^ n)) :=
      ((tendsto_const_nhds.sub (ha n)).norm).mul_const _
    refine le_of_tendsto h_lim ?_
    filter_upwards [Filter.eventually_ge_atTop N] with j hj
    have h_dist := hN i hi j hj
    rw [dist_eq_norm] at h_dist
    exact ((coeff_le (u i) (u j) n).trans_lt h_dist).le
  -- Step 5: the candidate `f` is restricted. Here we use the ultrametric inequality on `R`.
  have hf : PowerSeries.IsRestricted c f := by
    rw [isRestricted_iff_cofinite, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := unif_conv (ε / 2) (by linarith)
    have h_uN1 : Tendsto (fun n : ℕ => ‖PowerSeries.coeff n (u N₁).1‖ * c ^ n)
        cofinite (𝓝 0) := ((isRestricted_iff_cofinite c).mp (u N₁).2)
    rw [Metric.tendsto_nhds] at h_uN1
    have h_uN1' := h_uN1 (ε / 2) (by linarith)
    rw [Filter.eventually_cofinite] at h_uN1' ⊢
    refine h_uN1'.subset fun n hn => ?_
    simp only [Set.mem_ofPred_eq, dist_zero_right, Real.norm_eq_abs, not_lt] at hn ⊢
    rw [coeff_f] at hn
    have hp1 : 0 ≤ ‖a n‖ * c ^ n := mul_nonneg (norm_nonneg _) (hcn n).le
    have hp2 : 0 ≤ ‖PowerSeries.coeff n (u N₁).1‖ * c ^ n :=
      mul_nonneg (norm_nonneg _) (hcn n).le
    rw [abs_of_nonneg hp1] at hn
    rw [abs_of_nonneg hp2]
    have h1 : ‖PowerSeries.coeff n (u N₁).1 - a n‖ * c ^ n ≤ ε / 2 := hN₁ N₁ le_rfl n
    -- `‖a n‖ ≤ max ‖coeff n (u N₁).1 - a n‖ ‖coeff n (u N₁).1‖` by the ultrametric property.
    have h_ultra : ‖a n‖ ≤
        max ‖PowerSeries.coeff n (u N₁).1 - a n‖ ‖PowerSeries.coeff n (u N₁).1‖ := by
      have h1 : ‖(a n - PowerSeries.coeff n (u N₁).1) + PowerSeries.coeff n (u N₁).1‖ ≤
          max ‖a n - PowerSeries.coeff n (u N₁).1‖ ‖PowerSeries.coeff n (u N₁).1‖ :=
        IsUltrametricDist.norm_add_le_max _ _
      rw [sub_add_cancel] at h1
      rwa [norm_sub_rev] at h1
    have h_max_bd : ‖a n‖ * c ^ n ≤
        max (‖PowerSeries.coeff n (u N₁).1 - a n‖ * c ^ n)
            (‖PowerSeries.coeff n (u N₁).1‖ * c ^ n) := by
      rw [← max_mul_of_nonneg _ _ (hcn n).le]
      exact mul_le_mul_of_nonneg_right h_ultra (hcn n).le
    rcases le_max_iff.mp h_max_bd with h | h
    · linarith
    · linarith
  -- Step 6: `u i` converges to `⟨f, hf⟩` in the Gauss norm. (v4.33: name the limit
  -- point so the subtype literal does not leak into rewrite patterns.)
  set z : PowerSeries.Restricted R c := ⟨f, hf⟩ with hz
  refine ⟨z, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := unif_conv (ε / 2) (by linarith)
  refine ⟨N, fun i hi => ?_⟩
  rw [dist_eq_norm]
  change MvPowerSeries.gaussNorm norm (fun _ ↦ c) (u i - z).1 < ε
  have hdiff : ∀ n, PowerSeries.coeff n (u i - z).1 =
      PowerSeries.coeff n (u i).1 - a n := fun n => by
    change PowerSeries.coeff n ((u i).1 - f) = _
    rw [map_sub, coeff_f]
  have hbd : ∀ n, ‖PowerSeries.coeff n (u i - z).1‖ * c ^ n ≤ ε / 2 := fun n => by
    rw [hdiff]; exact hN i hi n
  have h_gauss_le : MvPowerSeries.gaussNorm norm (fun _ : Unit ↦ c) (u i - z).1 ≤ ε / 2 := by
    change PowerSeries.gaussNorm norm c (u i - z).1 ≤ ε / 2
    rw [PowerSeries.gaussNorm_eq]
    exact ciSup_le hbd
  linarith

end Restricted
