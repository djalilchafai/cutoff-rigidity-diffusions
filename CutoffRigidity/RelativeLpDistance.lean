module
public import CutoffRigidity.TotalVariation
public import CutoffRigidity.EntropyL2Bound
public import CutoffRigidity.LangevinL1Density
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! # Genuine RN-based relative Lᵖ distance

This is the actual extended eLpNorm of the canonical real RN density minus
one, and infinity for a singular law. At positive Langevin times absolute
continuity is proved elsewhere, so the definition is the paper's density
distance, rather than a scalar profile or an assumed mixing estimate.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped Topology ENNReal NNReal
variable {α : Type*} [MeasurableSpace α]

@[expose] noncomputable def relativeLpDistance (ν μ : Measure α) (p : ENNReal) : ENNReal := by
  classical
  exact if ν ≪ μ then eLpNorm (fun x => (ν.rnDeriv μ x).toReal - 1) p μ else ⊤

theorem relativeLpDistance_eq_eLpNorm (ν μ : Measure α) (hAC : ν ≪ μ) (p : ENNReal) :
    relativeLpDistance ν μ p = eLpNorm (fun x => (ν.rnDeriv μ x).toReal - 1) p μ := by
  simp only [relativeLpDistance, hAC, ↓reduceIte]

theorem relativeLpDistance_mono (ν μ : Measure α) [IsProbabilityMeasure μ]
    {p q : ENNReal} (hpq : p ≤ q) : relativeLpDistance ν μ p ≤ relativeLpDistance ν μ q := by
  by_cases hAC : ν ≪ μ
  · rw [relativeLpDistance_eq_eLpNorm ν μ hAC, relativeLpDistance_eq_eLpNorm ν μ hAC]
    exact eLpNorm_le_eLpNorm_of_exponent_le hpq
  · simp only [relativeLpDistance, hAC, ↓reduceIte, le_refl]

private theorem two_mul_abs_setIntegral_le_integral_norm
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) (hzero : ∫ x, f x ∂μ = 0)
    {A : Set α} (hA : MeasurableSet A) :
    2 * |∫ x in A, f x ∂μ| ≤ ∫ x, ‖f x‖ ∂μ := by
  have h1 : |∫ x in A, f x ∂μ| ≤ ∫ x in A, ‖f x‖ ∂μ :=
    by simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm (μ := μ.restrict A) f)
  have h2 : |∫ x in Aᶜ, f x ∂μ| ≤ ∫ x in Aᶜ, ‖f x‖ ∂μ :=
    by simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm (μ := μ.restrict Aᶜ) f)
  have he := integral_add_compl hA hf
  rw [hzero] at he
  have hc : (∫ x in Aᶜ, f x ∂μ) = -(∫ x in A, f x ∂μ) := by linarith only [he]
  rw [hc, abs_neg] at h2
  have hn := integral_add_compl hA hf.norm
  linarith only [h1, h2, hn]

set_option maxHeartbeats 650000 in
/-- The exact L¹/TV identity in the paper's probability normalization. -/
theorem integral_norm_rnDeriv_sub_one_eq_two_tv
    (ν μ : Measure α) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] (hAC : ν ≪ μ) :
    (∫ x, ‖(ν.rnDeriv μ x).toReal - 1‖ ∂μ) = 2 * totalVariationDistance ν μ := by
  let F := fun x => (ν.rnDeriv μ x).toReal - 1
  have hFMeas : Measurable F := (Measure.measurable_rnDeriv ν μ).ennreal_toReal.sub_const 1
  have hF : Integrable F μ := Measure.integrable_toReal_rnDeriv.sub (integrable_const 1)
  have hZero : (∫ x, F x ∂μ) = 0 := by
    rw [integral_sub Measure.integrable_toReal_rnDeriv (integrable_const 1), Measure.integral_toReal_rnDeriv hAC]
    simp
  have hEvent (A : Set α) : ν.real A - μ.real A = ∫ x in A, F x ∂μ := by
    rw [integral_sub Measure.integrable_toReal_rnDeriv.restrict (integrable_const 1),
      Measure.setIntegral_toReal_rnDeriv hAC, integral_const]
    simp
  have hUpper : totalVariationDistance ν μ ≤ (∫ x, ‖F x‖ ∂μ) / 2 := by
    change sSup {r : ℝ | ∃ A : Set α, MeasurableSet A ∧ r = |ν.real A - μ.real A|} ≤ _
    apply csSup_le (s := {r : ℝ | ∃ A : Set α, MeasurableSet A ∧ r = |ν.real A - μ.real A|})
      ⟨0, ∅, MeasurableSet.empty, by simp⟩
    rintro r ⟨A, hA, rfl⟩
    rw [hEvent]
    have hh := two_mul_abs_setIntegral_le_integral_norm hF hZero hA
    linarith only [hh]
  let A := {x | 0 ≤ F x}
  have hA : MeasurableSet A := measurableSet_le measurable_const hFMeas
  have hPos : (∫ x in A, ‖F x‖ ∂μ) = ∫ x in A, F x ∂μ :=
    setIntegral_congr_fun hA (fun x hx => Real.norm_of_nonneg hx)
  have hNeg : (∫ x in Aᶜ, ‖F x‖ ∂μ) = -(∫ x in Aᶜ, F x ∂μ) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun hA.compl
    intro x hx
    change ¬ 0 ≤ F x at hx
    have hn : F x ≤ 0 := (lt_of_not_ge hx).le
    exact Real.norm_of_nonpos hn
  have hsplit := integral_add_compl hA hF.norm
  have hsplitF := integral_add_compl hA hF
  rw [hPos, hNeg] at hsplit
  rw [hZero] at hsplitF
  have hPositive : 0 ≤ ∫ x in A, F x ∂μ := setIntegral_nonneg hA (fun x hx => hx)
  have hTV := abs_measureReal_sub_le_totalVariationDistance ν μ hA
  rw [hEvent, abs_of_nonneg hPositive] at hTV
  change (∫ x, ‖F x‖ ∂μ) = _
  linarith only [hUpper, hsplit, hsplitF, hTV]

/-- Genuine extended L¹ distance equals twice genuine TV for actual
absolutely continuous probability laws. -/
theorem relativeLpDistance_one_eq_two_tv
    (ν μ : Measure α) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] (hAC : ν ≪ μ) :
    relativeLpDistance ν μ 1 = ENNReal.ofReal (2 * totalVariationDistance ν μ) := by
  have hi : Integrable (fun x => (ν.rnDeriv μ x).toReal - 1) μ :=
    Measure.integrable_toReal_rnDeriv.sub (integrable_const 1)
  rw [relativeLpDistance_eq_eLpNorm ν μ hAC, eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hi, integral_norm_rnDeriv_sub_one_eq_two_tv ν μ hAC]

/-- The actual squared L² density distance is exactly χ² divergence,
with infinite values included. -/
theorem relativeLpDistance_two_sq_eq_chiSquare
    (ν μ : Measure α) (hAC : ν ≪ μ) :
    relativeLpDistance ν μ 2 ^ 2 = ∫⁻ x, ‖(ν.rnDeriv μ x).toReal - 1‖ₑ ^ 2 ∂μ := by
  rw [relativeLpDistance_eq_eLpNorm ν μ hAC,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      (((Measure.measurable_rnDeriv ν μ).ennreal_toReal.sub_const 1).aestronglyMeasurable)]
  norm_num only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  norm_num

/-- Actual entropy is bounded by the genuine squared L² density distance,
including laws for which that distance is infinite. -/
theorem klDiv_le_relativeLpDistance_two_sq
    (ν μ : Measure α) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] :
    klDiv ν μ ≤ relativeLpDistance ν μ 2 ^ 2 := by
  by_cases hAC : ν ≪ μ
  · rw [relativeLpDistance_two_sq_eq_chiSquare ν μ hAC, klDiv_eq_lintegral_klFun_of_ac hAC]
    apply lintegral_mono
    intro x
    calc
      ENNReal.ofReal (klFun (ν.rnDeriv μ x).toReal) ≤ ENNReal.ofReal (((ν.rnDeriv μ x).toReal - 1) ^ 2) :=
        ENNReal.ofReal_le_ofReal (klFun_le_sq_sub_one ENNReal.toReal_nonneg)
      _ = _ := by
        change ENNReal.ofReal (((ν.rnDeriv μ x).toReal - 1) ^ 2) = ‖(ν.rnDeriv μ x).toReal - 1‖ₑ ^ 2
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  · simp only [relativeLpDistance, hAC, ↓reduceIte, ENNReal.top_pow (by decide : 2 ≠ 0), le_top]


/-- The actual squared L² density error is the actual RN-root-free L²
norm of the density minus its unit mass, not a candidate scalar profile. -/
theorem relativeLpDistance_two_sq_eq_norm_rnDeriv_sub_one
    (ν μ : Measure α) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hAC : ν ≪ μ) (hRN : MemLp (fun x => (ν.rnDeriv μ x).toReal) 2 μ) :
    relativeLpDistance ν μ 2 ^ 2 = ENNReal.ofReal (‖hRN.toLp _‖ ^ 2 - 1) := by
  let f := fun x => (ν.rnDeriv μ x).toReal
  have hfI : Integrable f μ := hRN.integrable (by norm_num)
  have hfSq : Integrable (fun x => f x ^ 2) μ := hRN.integrable_sq
  have hdiff : MemLp (fun x => f x - 1) 2 μ := by
    simpa only [Pi.sub_def] using hRN.sub (memLp_const (1 : ℝ))
  have hnorm : ‖hRN.toLp _‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hRN.coeFn_toLp] with x hx
    rw [hx, Real.inner_apply]
    change f x * f x = f x ^ 2
    ring
  have hmass : ∫ x, f x ∂μ = 1 := by rw [Measure.integral_toReal_rnDeriv hAC]; simp
  have hreal : (∫ x, (f x - 1) ^ 2 ∂μ) = ‖hRN.toLp _‖ ^ 2 - 1 := by
    have he (x : α) : (f x - 1) ^ 2 = (f x ^ 2 - 2 * f x) + 1 := by ring
    have hAdd := integral_add (hfSq.sub (hfI.const_mul 2)) (integrable_const (1 : ℝ))
    have hSub := integral_sub hfSq (hfI.const_mul 2)
    simp only [Pi.sub_apply] at hAdd hSub
    rw [integral_congr_ae (Eventually.of_forall he), hAdd, hSub, integral_const_mul,
      hmass, ← hnorm, integral_const]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    ring
  rw [relativeLpDistance_two_sq_eq_chiSquare ν μ hAC, ← hreal,
    ofReal_integral_eq_lintegral_ofReal hdiff.integrable_sq (Eventually.of_forall (fun x => sq_nonneg _))]
  apply lintegral_congr
  intro x
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

end CutoffRigidity
