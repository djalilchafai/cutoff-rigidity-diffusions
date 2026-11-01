module

public import CutoffRigidity.Extra.Dyson3

/-! # The Dyson--OU chamber measure: finiteness, positivity, integral formula -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal

namespace CutoffRigidity.Dyson

variable {d : ℕ}

theorem Dlim_nonneg (ρ β : ℝ) (x : CutCur.Rd d) : 0 ≤ Dlim d ρ β x := by
  unfold Dlim
  by_cases hx : x ∈ chamber d
  · rw [Set.indicator_of_mem hx]
    refine mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j hj => ?_)
    have hij : i < j := by simpa using hj
    exact Real.rpow_nonneg (sub_pos.2 (hx i j hij)).le _
  · rw [Set.indicator_of_notMem hx]

/-- On the chamber, `e^{-V} = e^{-ρ|x|²/2} ∏_{i<j} (x_i-x_j)^β`. -/
theorem exp_neg_dysonV {x : CutCur.Rd d} (hx : x ∈ chamber d) (ρ β : ℝ) :
    Real.exp (-dysonV d ρ β x) =
      Real.exp (-(ρ / 2) * ‖x‖ ^ 2) * ∏ i, ∏ j with i < j, (x i - x j) ^ β := by
  unfold dysonV
  have e : -(ρ / 2 * ‖x‖ ^ 2 + ∑ i, ∑ j with i < j, (-β * Real.log (x i - x j))) =
      -(ρ / 2) * ‖x‖ ^ 2 + ∑ i, ∑ j with i < j, (Real.log (x i - x j) * β) := by
    rw [neg_add]
    congr 1
    · ring
    · rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, Real.exp_add, Real.exp_sum]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hij : i < j := by simpa using hj
  rw [← Real.rpow_def_of_pos (sub_pos.2 (hx i j hij))]

theorem dysonMeasure_eq (ρ β : ℝ) :
    dysonMeasure d ρ β = volume.withDensity fun x => ENNReal.ofReal (Dlim d ρ β x) := by
  unfold dysonMeasure
  have hC := (isOpen_chamber (d := d)).measurableSet
  have e1 : (fun x : CutCur.Rd d => ENNReal.ofReal (Dlim d ρ β x)) =
      (chamber d).indicator (fun x => ENNReal.ofReal (Real.exp (-(ρ / 2) * ‖x‖ ^ 2) *
        ∏ i, ∏ j with i < j, (x i - x j) ^ β)) := by
    funext x
    unfold Dlim
    by_cases hx : x ∈ chamber d
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  rw [e1, withDensity_indicator hC]
  refine withDensity_congr_ae ?_
  refine (ae_restrict_iff' hC).2 (Eventually.of_forall fun x hx => ?_)
  simp only [exp_neg_dysonV hx]

theorem integral_dysonMeasure (ρ β : ℝ) (F : CutCur.Rd d → ℝ) :
    ∫ x, F x ∂dysonMeasure d ρ β = ∫ x, Dlim d ρ β x * F x := by
  rw [dysonMeasure_eq, integral_withDensity_eq_integral_toReal_smul
    (f := fun x => ENNReal.ofReal (Dlim d ρ β x)) (ENNReal.measurable_ofReal.comp (measurable_Dlim ρ β))
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (Dlim_nonneg ρ β x)]


/-- The a.e. polynomial-Gaussian majorant of the limit density. -/
theorem Dlim_bound {ρ : ℝ} (hρ : 0 < ρ) {β : ℝ} (hβ : 0 ≤ β) :
    ∀ᵐ x : CutCur.Rd d ∂volume, (1 + ‖x‖) ^ 2 * Dlim d ρ β x ≤
      Real.exp ((2 + 2 * (β * d * d)) ^ 2 / ρ) * Real.exp (-(ρ / 4) * ‖x‖ ^ 2) := by
  have hae := measure_eq_zero_iff_ae_notMem.1 (volume_ties_null d)
  filter_upwards [hae] with x hx
  have hx' : ∀ i j : Fin d, i ≠ j → x i ≠ x j := by
    by_contra h; exact hx h
  refine le_of_tendsto ((tendsto_Dens hβ hx').const_mul ((1 + ‖x‖) ^ 2)) ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with ε hε
  exact Dens_bound hρ hβ hε.1 hε.2.le x

theorem integrable_Dlim_mul {ρ : ℝ} (hρ : 0 < ρ) {β : ℝ} (hβ : 0 ≤ β)
    {F : CutCur.Rd d → ℝ} (hFm : Measurable F) {M : ℝ} (hF : ∀ x, |F x| ≤ M * (1 + ‖x‖) ^ 2) :
    Integrable (fun x => Dlim d ρ β x * F x) volume := by
  have hM : 0 ≤ M := by
    have := hF 0
    simp only [norm_zero, add_zero, one_pow, mul_one] at this
    exact (abs_nonneg _).trans this
  have hint := (integrable_exp_neg_mul_norm_sq (ι := Fin d) (ρ / 4) (by linarith)).const_mul
    (M * Real.exp ((2 + 2 * (β * d * d)) ^ 2 / ρ))
  refine hint.mono' ((measurable_Dlim ρ β).mul hFm).aestronglyMeasurable ?_
  filter_upwards [Dlim_bound hρ hβ] with x hx
  rw [norm_mul, Real.norm_of_nonneg (Dlim_nonneg ρ β x), Real.norm_eq_abs]
  calc Dlim d ρ β x * |F x| ≤ Dlim d ρ β x * (M * (1 + ‖x‖) ^ 2) :=
        mul_le_mul_of_nonneg_left (hF x) (Dlim_nonneg ρ β x)
    _ = M * ((1 + ‖x‖) ^ 2 * Dlim d ρ β x) := by ring
    _ ≤ M * (Real.exp ((2 + 2 * (β * d * d)) ^ 2 / ρ) * Real.exp (-(ρ / 4) * ‖x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hx hM
    _ = _ := by ring

theorem integrable_Dlim {ρ : ℝ} (hρ : 0 < ρ) {β : ℝ} (hβ : 0 ≤ β) :
    Integrable (Dlim d ρ β) volume := by
  simpa using integrable_Dlim_mul hρ hβ (F := fun _ => (1 : ℝ)) measurable_const (M := 1)
    (fun x => by simp only [abs_one, one_mul]; nlinarith [norm_nonneg x])

theorem dysonMeasure_univ {ρ : ℝ} (hρ : 0 < ρ) {β : ℝ} (hβ : 0 ≤ β) :
    dysonMeasure d ρ β Set.univ = ENNReal.ofReal (∫ x, Dlim d ρ β x) := by
  rw [dysonMeasure_eq, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ofReal_integral_eq_lintegral_ofReal (integrable_Dlim hρ hβ)
      (Eventually.of_forall (Dlim_nonneg ρ β))]

theorem dysonMeasure_finite {ρ : ℝ} (hρ : 0 < ρ) {β : ℝ} (hβ : 0 ≤ β) :
    IsFiniteMeasure (dysonMeasure d ρ β) :=
  ⟨by rw [dysonMeasure_univ hρ hβ]; exact ENNReal.ofReal_lt_top⟩

theorem measurable_dysonV (ρ β : ℝ) : Measurable (dysonV d ρ β) := by
  unfold dysonV
  refine Measurable.add (by fun_prop) (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_)
  exact measurable_const.mul (Real.measurable_log.comp (by fun_prop : Measurable fun x : CutCur.Rd d => x i - x j))

theorem dysonMeasure_pos (ρ β : ℝ) (hne : (chamber d).Nonempty) : 0 < dysonMeasure d ρ β Set.univ := by
  unfold dysonMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hm : Measurable fun x : CutCur.Rd d => ENNReal.ofReal (Real.exp (-dysonV d ρ β x)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_dysonV ρ β).neg)
  rw [lintegral_pos_iff_support hm]
  have : Function.support (fun x : CutCur.Rd d => ENNReal.ofReal (Real.exp (-dysonV d ρ β x))) = Set.univ := by
    ext x
    simp [Function.mem_support, ENNReal.ofReal_eq_zero, not_le, Real.exp_pos]
  rw [this, Measure.restrict_apply_univ]
  exact isOpen_chamber.measure_pos volume hne

end CutoffRigidity.Dyson
