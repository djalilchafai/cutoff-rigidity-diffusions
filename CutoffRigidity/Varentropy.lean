module

public import CutoffRigidity.TotalVariation
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio

/-! # Actual likelihood varentropy and the Salez comparison

Reference: Salez, arXiv:2501.01304v1, Lemma 1 (equation (10)),
https://arxiv.org/html/2501.01304v1 . Its threshold/Chebyshev proof is
Lemma 8 of https://ems.press/content/serial-article-files/48221 .
All likelihoods, KL divergences and variances below concern actual measures.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α]

/-- Extended varentropy: the actual variance of the RN log likelihood
under the first probability law, allowing an infinite second moment. -/
@[expose] noncomputable def varentropy (μ ν : Measure α) : ℝ≥0∞ :=
  evariance (llr μ ν) μ

/-- The actual high-likelihood event. Removing the RN zero set allows the
likelihood comparison under the reference law without mutual AC. -/
@[expose] def likelihoodUpperSet (μ ν : Measure α) (θ : ℝ) : Set α :=
  {x | θ ≤ llr μ ν x ∧ μ.rnDeriv ν x ≠ 0}

theorem measurableSet_likelihoodUpperSet (μ ν : Measure α) (θ : ℝ) :
    MeasurableSet (likelihoodUpperSet μ ν θ) :=
  (measurableSet_le measurable_const (measurable_llr μ ν)).inter
    ((Measure.measurable_rnDeriv μ ν) (measurableSet_singleton 0)).compl

/-- On a genuine high-likelihood event, the reference mass is exponentially
smaller than the target mass. This is Salez's likelihood comparison. -/
theorem likelihoodUpperSet_reference_le (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν) (θ : ℝ) :
    ν.real (likelihoodUpperSet μ ν θ) ≤
      Real.exp (-θ) * μ.real (likelihoodUpperSet μ ν θ) := by
  let A := likelihoodUpperSet μ ν θ
  have hA : MeasurableSet A := measurableSet_likelihoodUpperSet μ ν θ
  have hi : Real.exp θ * ν.real A ≤ μ.real A := by
    rw [← Measure.setIntegral_toReal_rnDeriv hac A]
    calc
      _ = ∫ _ in A, Real.exp θ ∂ν := by simp [integral_const, mul_comm]
      _ ≤ _ := integral_mono_ae (integrable_const _)
        (Measure.integrableOn_toReal_rnDeriv (measure_ne_top μ A)) (by
          filter_upwards [ae_restrict_mem hA, ae_restrict_of_ae (exp_llr μ ν)] with x hx he
          rw [ite_eq_right hx.2] at he
          exact (Real.exp_le_exp.mpr hx.1).trans_eq he)
  calc
    _ = Real.exp (-θ) * (Real.exp θ * ν.real A) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp [A]
    _ ≤ _ := mul_le_mul_of_nonneg_left hi (Real.exp_nonneg _)

/-- The actual mean information content equals finite KL; square
integrability explicitly discharges the KL domain requirements. -/
theorem klDiv_ne_top_of_memLp_llr (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν)
    (hL : MemLp (llr μ ν) 2 μ) : klDiv μ ν ≠ ⊤ :=
  klDiv_ne_top hac (hL.integrable (by norm_num))

theorem klDiv_toReal_eq_mean_llr (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν) :
    (klDiv μ ν).toReal = ∫ x, llr μ ν x ∂μ :=
  toReal_klDiv_of_measure_eq hac (by simp)

/-- The concentration step of the exact cited reverse Pinsker proof. -/
theorem likelihoodUpperSet_mass_ge_chebyshev (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν)
    (hL : MemLp (llr μ ν) 2 μ) (r : ℝ) (hr : 0 < r) :
    1 - variance (llr μ ν) μ / r ^ 2 ≤
      μ.real (likelihoodUpperSet μ ν ((klDiv μ ν).toReal - r)) := by
  let A := likelihoodUpperSet μ ν ((klDiv μ ν).toReal - r)
  have hA : MeasurableSet A := measurableSet_likelihoodUpperSet μ ν _
  have hm := meas_ge_le_variance_div_sq hL hr
  have hc : μ Aᶜ ≤ ENNReal.ofReal (variance (llr μ ν) μ / r ^ 2) := by
    apply le_trans (measure_mono_ae ?_) hm
    filter_upwards [Measure.rnDeriv_pos hac] with x hx
    intro hn
    have hn' : llr μ ν x < (klDiv μ ν).toReal - r := by
      by_contra hn'
      exact hn ⟨le_of_not_gt hn', hx.ne'⟩
    rw [← klDiv_toReal_eq_mean_llr μ ν hac]
    exact le_trans (by linarith) (neg_le_abs _)
  have hcr : μ.real Aᶜ ≤ variance (llr μ ν) μ / r ^ 2 :=
    ENNReal.toReal_le_of_le_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _)) hc
  rw [measureReal_compl hA] at hcr
  have hμ1 : μ.real univ = 1 := by simp
  rw [hμ1] at hcr
  change 1 - variance (llr μ ν) μ / r ^ 2 ≤ μ.real A
  linarith

private theorem threshold_le_inv_of_mass_comparison
    {ε θ p q : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hp : 1 - ε ^ 2 ≤ p) (hq : q ≤ Real.exp (-θ) * p)
    (htv : p - q ≤ 1 - ε) : θ ≤ 1 / ε := by
  by_cases hθ : θ ≤ 0
  · exact hθ.trans (le_of_lt (one_div_pos.mpr hε))
  have hθpos : 0 < θ := lt_of_not_ge hθ
  have he : Real.exp (-θ) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by linarith : -θ ≤ 0)
  have hmass : (1 - ε ^ 2) * (1 - Real.exp (-θ)) ≤ 1 - ε := by
    have hh := mul_le_mul_of_nonneg_right hp (sub_nonneg.mpr he)
    nlinarith
  have hexp : Real.exp (-θ) * Real.exp θ = 1 := by rw [← Real.exp_add]; simp
  have hmul : (1 - ε ^ 2) * (Real.exp θ - 1) ≤ (1 - ε) * Real.exp θ := by
    calc
      _ = ((1 - ε ^ 2) * (1 - Real.exp (-θ))) * Real.exp θ := by
        have hi : (1 - Real.exp (-θ)) * Real.exp θ = Real.exp θ - 1 := by
          rw [sub_mul, one_mul, hexp]
        conv_rhs => rw [mul_assoc, hi]
      _ ≤ _ := mul_le_mul_of_nonneg_right hmass (Real.exp_nonneg _)
  have hcancel : (1 + ε) * (Real.exp θ - 1) ≤ Real.exp θ := by
    apply (mul_le_mul_iff_right₀ (sub_pos.mpr hε1)).mp
    nlinarith [hmul]
  have hlinear : ε * θ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp θ) (le_of_lt hε)
    nlinarith
  exact (le_div_iff₀ hε).mpr (by nlinarith)

/-- Salez's threshold/Chebyshev argument before choosing the concentration
radius. Every quantity is evaluated under the actual probability laws. -/
theorem klDiv_toReal_le_radius_add_inv (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν)
    (hL : MemLp (llr μ ν) 2 μ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hTV : totalVariationDistance μ ν ≤ 1 - ε)
    (r : ℝ) (hr : 0 < r) (hvar : variance (llr μ ν) μ / r ^ 2 ≤ ε ^ 2) :
    (klDiv μ ν).toReal ≤ r + 1 / ε := by
  let θ := (klDiv μ ν).toReal - r
  let A := likelihoodUpperSet μ ν θ
  have hm : 1 - ε ^ 2 ≤ μ.real A := by
    have hh := likelihoodUpperSet_mass_ge_chebyshev μ ν hac hL r hr
    dsimp only [A, θ]
    linarith
  have hsep : μ.real A - ν.real A ≤ 1 - ε :=
    (le_abs_self _).trans ((abs_measureReal_sub_le_totalVariationDistance μ ν
      (measurableSet_likelihoodUpperSet μ ν θ)).trans hTV)
  have hh := threshold_le_inv_of_mass_comparison hε hε1 hm
    (likelihoodUpperSet_reference_le μ ν hac θ) hsep
  dsimp only [θ] at hh
  linarith

/-- Reverse Pinsker in the exact constants used by Salez, with its genuine
finite-second-information-moment domain. This controls actual KL by actual
TV and actual RN-loglikelihood varentropy. -/
theorem klDiv_toReal_le_varentropy_of_tv_le (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν)
    (hL : MemLp (llr μ ν) 2 μ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hTV : totalVariationDistance μ ν ≤ 1 - ε) :
    (klDiv μ ν).toReal ≤ (1 + Real.sqrt (variance (llr μ ν) μ)) / ε := by
  let v := variance (llr μ ν) μ
  let H := (klDiv μ ν).toReal
  have hv : 0 ≤ v := variance_nonneg _ _
  have hs : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv
  by_contra hn
  have hgap : 0 < H - (1 + Real.sqrt v) / ε := by
    change ¬ H ≤ (1 + Real.sqrt v) / ε at hn
    linarith
  let δ := (H - (1 + Real.sqrt v) / ε) / 2
  let r := Real.sqrt v / ε + δ
  have hδ : 0 < δ := half_pos hgap
  have hr : 0 < r := add_pos_of_nonneg_of_pos (div_nonneg (Real.sqrt_nonneg _) hε.le) hδ
  have hsr : Real.sqrt v ≤ ε * r := by
    have he : ε * (Real.sqrt v / ε) = Real.sqrt v := by field_simp
    dsimp only [r]
    nlinarith
  have hvbound : v / r ^ 2 ≤ ε ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
    calc
      v = Real.sqrt v ^ 2 := hs.symm
      _ ≤ (ε * r) ^ 2 := (sq_le_sq₀ (Real.sqrt_nonneg v) (mul_nonneg hε.le hr.le)).mpr hsr
      _ = ε ^ 2 * r ^ 2 := mul_pow _ _ _
  have hh := klDiv_toReal_le_radius_add_inv μ ν hac hL hε hε1 hTV r hr hvbound
  change H ≤ r + 1 / ε at hh
  dsimp only [r, δ] at hh
  have he : (1 + Real.sqrt v) / ε = Real.sqrt v / ε + 1 / ε := by ring
  linarith

/-- The extended domain is explicit: varentropy is infinite exactly when
the actual RN information content has no finite second moment. -/
theorem varentropy_eq_top_iff (μ ν : Measure α) [IsProbabilityMeasure μ] :
    varentropy μ ν = ⊤ ↔ ¬ MemLp (llr μ ν) 2 μ :=
  evariance_eq_top_iff (measurable_llr μ ν).aestronglyMeasurable

/-- Infinite genuine KL under absolute continuity forces infinite actual
varentropy; the real-valued variance must not silently replace this case. -/
theorem varentropy_eq_top_of_klDiv_eq_top (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν)
    (hKL : klDiv μ ν = ⊤) : varentropy μ ν = ⊤ := by
  rw [varentropy_eq_top_iff]
  intro hL
  exact klDiv_ne_top_of_memLp_llr μ ν hac hL hKL

/-- Zero genuine TV identifies actual probability measures. -/
theorem measure_eq_of_totalVariationDistance_eq_zero (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hTV : totalVariationDistance μ ν = 0) : μ = ν := by
  apply Measure.ext
  intro A hA
  have hh := abs_measureReal_sub_le_totalVariationDistance μ ν hA
  rw [hTV] at hh
  have he : μ.real A = ν.real A := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ A) (measure_ne_top ν A)).mp he

/-- Salez's reverse Pinsker inequality, equation (10), for actual probability
laws and the actual RN log-likelihood variance. The L² domain makes both KL
and varentropy finite; the preceding theorem handles infinite KL explicitly. -/
theorem salez_reverse_pinsker (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν)
    (hL : MemLp (llr μ ν) 2 μ) (hTV : totalVariationDistance μ ν < 1) :
    (klDiv μ ν).toReal ≤
      (1 + Real.sqrt ((varentropy μ ν).toReal)) / (1 - totalVariationDistance μ ν) := by
  by_cases hz : totalVariationDistance μ ν = 0
  · have he := measure_eq_of_totalVariationDistance_eq_zero μ ν hz
    subst ν
    simp only [klDiv_self, ENNReal.toReal_zero, totalVariationDistance_self, sub_zero, div_one]
    positivity
  have hp : 0 < totalVariationDistance μ ν :=
    lt_of_le_of_ne (totalVariationDistance_nonneg μ ν) (Ne.symm hz)
  exact klDiv_toReal_le_varentropy_of_tv_le μ ν hac hL
    (sub_pos.mpr hTV) (by linarith) (by linarith)

end CutoffRigidity
