module

public import CutoffRigidity.TotalVariation
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Pinsker's inequality in the paper's normalization

The scalar binary-divergence bound and measure inequalities below concern
Mathlib's genuine Kullback--Leibler divergence and the measurable-set
supremum defining total variation.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal

/-- Binary relative entropy in a form continuous in its first argument at 0 and 1. -/
@[expose] noncomputable def binaryDivergence (p q : ℝ) : ℝ :=
  p * Real.log p - p * Real.log q +
    (1 - p) * Real.log (1 - p) - (1 - p) * Real.log (1 - q)

/-- The sharp scalar inequality underlying Pinsker's probability normalization. -/
theorem binaryDivergence_ge_two_mul_sq {p q : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    2 * (p - q) ^ 2 ≤ binaryDivergence p q := by
  let F : ℝ → ℝ := fun x => binaryDivergence x q - 2 * (x - q) ^ 2
  let G : ℝ → ℝ := fun x => Real.log x - Real.log (1 - x) -
    Real.log q + Real.log (1 - q) - 4 * (x - q)
  have hF (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt F (G x) x := by
    have hcomp := (Real.hasDerivAt_mul_log (sub_pos.mpr hx.2).ne').comp x
      ((hasDerivAt_const x 1).sub (hasDerivAt_id x))
    have h := (((Real.hasDerivAt_mul_log hx.1.ne').sub
      ((hasDerivAt_id x).mul_const (Real.log q))).add hcomp).sub
      (((hasDerivAt_const x 1).sub (hasDerivAt_id x)).mul_const (Real.log (1 - q)))
    have hh := h.sub ((((hasDerivAt_id x).sub_const q).pow 2).const_mul 2)
    convert hh using 1
    · ext y
      rfl
    · dsimp [G]
      ring
  have hG (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt G (1 / x + 1 / (1 - x) - 4) x := by
    have hlog := (Real.hasDerivAt_log (sub_pos.mpr hx.2).ne').comp x
      ((hasDerivAt_const x 1).sub (hasDerivAt_id x))
    have h := ((((Real.hasDerivAt_log hx.1.ne').sub hlog).sub_const (Real.log q)).add_const
      (Real.log (1 - q))).sub (((hasDerivAt_id x).sub_const q).const_mul 4)
    convert h using 1
    · ext y
      rfl
    · ring
  have hGmono : MonotoneOn G (Ioo (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 1)
    · exact fun x hx => (hG x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hG x (by simpa using hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Ioo (0 : ℝ) 1 := by simpa using hx
      rw [(hG x hx').deriv]
      have hden : 1 / x + 1 / (1 - x) - 4 = (2 * x - 1) ^ 2 / (x * (1 - x)) := by
        field_simp [hx'.1.ne', (sub_pos.mpr hx'.2).ne']
        ring
      rw [hden]
      exact div_nonneg (sq_nonneg _) (mul_nonneg hx'.1.le (sub_nonneg.mpr hx'.2.le))
  have hFcontinuous : Continuous F := by
    dsimp [F, binaryDivergence]
    fun_prop
  have hFmono : MonotoneOn (deriv F) (interior (Icc (0 : ℝ) 1)) := by
    simp only [interior_Icc]
    intro x hx y hy hxy
    rw [(hF x hx).deriv, (hF y hy).deriv]
    exact hGmono hx hy hxy
  have hconv := hFmono.convexOn_of_deriv (convex_Icc (0 : ℝ) 1)
    hFcontinuous.continuousOn (fun x hx => (hF x (by simpa using hx)).differentiableAt.differentiableWithinAt)
  have hFq : HasDerivAt F 0 q := by
    simpa [G] using hF q ⟨hq0, hq1⟩
  have hmin := hconv.isMinOn_of_rightDeriv_eq_zero
    (by simpa only [interior_Icc] using (show q ∈ Ioo (0 : ℝ) 1 from ⟨hq0, hq1⟩))
    (hFq.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi q))
  have h := hmin (show p ∈ Icc (0 : ℝ) 1 from ⟨hp0, hp1⟩)
  dsimp [F, binaryDivergence] at h ⊢
  nlinarith

/-- Jensen's inequality applied to a restricted reference measure. -/
theorem klFun_set_average_le {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (hint : Integrable (fun x => klFun (μ.rnDeriv ν x).toReal) ν)
    (A : Set α) (hq : 0 < ν.real A) :
    ν.real A * klFun (μ.real A / ν.real A) ≤
      ∫ x in A, klFun (μ.rnDeriv ν x).toReal ∂ν := by
  have hνA : ν A ≠ 0 := by
    intro h
    simp [measureReal_def, h] at hq
  have : NeZero (ν.restrict A) := ⟨fun h => hνA (Measure.restrict_eq_zero.mp h)⟩
  have h := convexOn_klFun.map_average_le continuous_klFun.continuousOn isClosed_Ici
    (μ := ν.restrict A) (f := fun x => (μ.rnDeriv ν x).toReal)
    (Filter.Eventually.of_forall fun x => ENNReal.toReal_nonneg)
    (Measure.integrable_toReal_rnDeriv.restrict) hint.restrict
  rw [average_eq, average_eq, measureReal_restrict_apply_univ,
    Measure.setIntegral_toReal_rnDeriv hμν A] at h
  simp only [smul_eq_mul] at h
  have hm := mul_le_mul_of_nonneg_left h hq.le
  have harg : (ν.real A)⁻¹ * μ.real A = μ.real A / ν.real A := by ring
  rw [harg] at hm
  convert hm using 1
  rw [← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul]

/-- Expanding a weighted KL integrand also works when its first mass is zero. -/
theorem weighted_klFun_ratio (p q : ℝ) (hq : 0 < q) :
    q * klFun (p / q) = p * Real.log p - p * Real.log q + q - p := by
  by_cases hp : p = 0
  · simp [hp, klFun]
  rw [klFun, Real.log_div hp hq.ne']
  field_simp

/-- Splitting the genuine relative entropy over an event and its complement
bounds it below by binary relative entropy. -/
theorem binaryDivergence_le_klDiv_toReal {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hKL : klDiv μ ν ≠ ∞) {A : Set α} (hA : MeasurableSet A)
    (hq0 : 0 < ν.real A) (hq1 : ν.real A < 1) :
    binaryDivergence (μ.real A) (ν.real A) ≤ (klDiv μ ν).toReal := by
  obtain ⟨hμν, hint⟩ := klDiv_ne_top_iff.mp hKL
  have hintKL := (integrable_klFun_rnDeriv_iff hμν).2 hint
  have hleft := klFun_set_average_le μ ν hμν hintKL A hq0
  have hright := klFun_set_average_le μ ν hμν hintKL Aᶜ
    (by rw [measureReal_compl hA]; simpa using sub_pos.mpr hq1)
  have hsum := add_le_add hleft hright
  rw [integral_add_compl hA hintKL] at hsum
  rw [measureReal_compl hA, measureReal_compl hA] at hsum
  simp only [probReal_univ] at hsum
  rw [weighted_klFun_ratio _ _ hq0,
    weighted_klFun_ratio _ _ (sub_pos.mpr hq1)] at hsum
  rw [toReal_klDiv_eq_integral_klFun hμν]
  dsimp [binaryDivergence]
  linarith

/-- The sharp Pinsker bound for each measurable event, including reference
probabilities zero and one. -/
theorem two_mul_sq_measureReal_sub_le_klDiv_toReal
    {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hKL : klDiv μ ν ≠ ∞) {A : Set α} (hA : MeasurableSet A) :
    2 * (μ.real A - ν.real A) ^ 2 ≤ (klDiv μ ν).toReal := by
  have hμν := (klDiv_ne_top_iff.mp hKL).1
  have hzero {B : Set α} (hz : ν.real B = 0) : μ.real B = 0 := by
    have hνB : ν B = 0 := (measureReal_eq_zero_iff (measure_ne_top ν B)).mp hz
    exact (measureReal_eq_zero_iff (measure_ne_top μ B)).mpr (hμν hνB)
  by_cases hq0 : 0 < ν.real A
  · by_cases hq1 : ν.real A < 1
    · exact (binaryDivergence_ge_two_mul_sq measureReal_nonneg measureReal_le_one hq0 hq1).trans
        (binaryDivergence_le_klDiv_toReal μ ν hKL hA hq0 hq1)
    · have hq : ν.real A = 1 := le_antisymm measureReal_le_one (not_lt.mp hq1)
      have hνc : ν.real Aᶜ = 0 := by rw [measureReal_compl hA]; simp [hq]
      have hμc := hzero hνc
      have hp : μ.real A = 1 := by
        rw [measureReal_compl hA] at hμc
        simpa using (sub_eq_zero.mp hμc).symm
      rw [hp, hq]
      norm_num
  · have hq : ν.real A = 0 := le_antisymm (not_lt.mp hq0) measureReal_nonneg
    have hp := hzero hq
    rw [hp, hq]
    norm_num

/-- **Csiszár--Kullback--Pinsker inequality**, with the paper's TV normalization,
for finite relative entropy. This is an inequality between genuine distances. -/
theorem totalVariationDistance_sq_le_klDiv_toReal
    {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hKL : klDiv μ ν ≠ ∞) :
    totalVariationDistance μ ν ^ 2 ≤ (klDiv μ ν).toReal / 2 := by
  have hK : 0 ≤ (klDiv μ ν).toReal / 2 := div_nonneg ENNReal.toReal_nonneg (by norm_num)
  have hTV : totalVariationDistance μ ν ≤ Real.sqrt ((klDiv μ ν).toReal / 2) := by
    unfold totalVariationDistance
    apply csSup_le
    · exact ⟨0, ∅, MeasurableSet.empty, by simp⟩
    · rintro r ⟨A, hA, rfl⟩
      apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
      rw [sq_abs, Real.sq_sqrt hK]
      have h := two_mul_sq_measureReal_sub_le_klDiv_toReal μ ν hKL hA
      linarith
  have hsq := (sq_le_sq₀ (totalVariationDistance_nonneg μ ν) (Real.sqrt_nonneg _)).mpr hTV
  rwa [Real.sq_sqrt hK] at hsq

/-- **Pinsker's inequality** in extended nonnegative form, valid also for
infinite relative entropy. -/
theorem totalVariationDistance_sq_le_klDiv
    {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ENNReal.ofReal (totalVariationDistance μ ν ^ 2) ≤ klDiv μ ν / 2 := by
  by_cases hKL : klDiv μ ν = ∞
  · rw [hKL, ENNReal.top_div_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    exact le_top
  calc
    _ ≤ ENNReal.ofReal ((klDiv μ ν).toReal / 2) :=
      ENNReal.ofReal_le_ofReal (totalVariationDistance_sq_le_klDiv_toReal μ ν hKL)
    _ = klDiv μ ν / 2 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_toReal hKL]
      norm_num

end CutoffRigidity
