module

public import CutoffRigidity.Extra.DysonGap

/-! # Dyson--OU spectral gap (stage 2): convergence of the cutoff approximants -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal NNReal

namespace CutoffRigidity.Dyson

variable {d : ℕ}

section Main
variable (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ) {β : ℝ} (hβ : 0 ≤ β)
include hd hρ hβ

omit hd hρ hβ in
theorem fR_abs_le (R : ℝ) (x : CutCur.Rd d) : |fR d R x| ≤ |hsum d x| := by
  unfold fR
  rw [abs_mul, abs_of_nonneg (cut_nonneg R x)]
  exact mul_le_of_le_one_left (abs_nonneg _) (cut_le_one R x)

omit hd hρ hβ in
theorem tendsto_fR_pt (x : CutCur.Rd d) : Tendsto (fun R => fR d R x) atTop (𝓝 (hsum d x)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ‖x‖, eventually_gt_atTop 0] with R h1 h2
  simp [fR, cut_eq_one h2 h1]

theorem tendsto_integral_fR :
    Tendsto (fun R => ∫ x, fR d R x ∂dysonProb d ρ β) atTop (𝓝 0) := by
  have := isProbabilityMeasure_dysonProb hd hρ hβ
  rw [← hsum_mean hd hρ hβ]
  refine tendsto_integral_filter_of_dominated_convergence (fun x => |hsum d x|) ?_ ?_
    (hsum_integrable hd hρ hβ).abs (Eventually.of_forall tendsto_fR_pt)
  · exact Eventually.of_forall fun R => (fR_contDiff (d := d) R).continuous.aestronglyMeasurable
  · exact Eventually.of_forall fun R => Eventually.of_forall fun x => by
      simpa using fR_abs_le R x

theorem tendsto_integral_fR_sq :
    Tendsto (fun R => ∫ x, fR d R x ^ 2 ∂dysonProb d ρ β) atTop
      (𝓝 (∫ x, hsum d x ^ 2 ∂dysonProb d ρ β)) := by
  have := isProbabilityMeasure_dysonProb hd hρ hβ
  refine tendsto_integral_filter_of_dominated_convergence (fun x => hsum d x ^ 2) ?_ ?_
    (hsum_sq_integrable hd hρ hβ) (Eventually.of_forall fun x => (tendsto_fR_pt x).pow 2)
  · exact Eventually.of_forall fun R =>
      ((fR_contDiff (d := d) R).continuous.pow 2).aestronglyMeasurable
  · refine Eventually.of_forall fun R => Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_pow, ← sq_abs (hsum d x)]
    exact pow_le_pow_left₀ (abs_nonneg _) (fR_abs_le R x) 2

theorem fR_memLp {R : ℝ} : MemLp (fR d R) 2 (dysonProb d ρ β) :=
  (hsum_memLp hd hρ hβ).mono (fR_contDiff (d := d) R).continuous.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa using fR_abs_le R x)

theorem tendsto_variance_fR :
    Tendsto (fun R => variance (fR d R) (dysonProb d ρ β)) atTop (𝓝 (d / ρ)) := by
  have := isProbabilityMeasure_dysonProb hd hρ hβ
  have e : ∀ R, variance (fR d R) (dysonProb d ρ β) =
      ∫ x, fR d R x ^ 2 ∂dysonProb d ρ β - (∫ x, fR d R x ∂dysonProb d ρ β) ^ 2 := by
    intro R
    rw [variance_eq_sub (fR_memLp hd hρ hβ)]; rfl
  simp only [e]
  have h2 : ∫ x, hsum d x ^ 2 ∂dysonProb d ρ β = d / ρ := by
    have := hsum_second_moment hd hρ hβ
    field_simp; linarith
  have := (tendsto_integral_fR_sq hd hρ hβ).sub ((tendsto_integral_fR hd hρ hβ).pow 2)
  simpa [h2] using this

/-- Upper bound on the Dirichlet energy of the approximants. -/
theorem integral_gradient_fR_le {M : ℝ}
    (hM : ∀ R : ℝ, 0 < R → ∀ x : CutCur.Rd d, ‖fderiv ℝ (cut d R) x‖ ≤ M / R) {R : ℝ} (hR : 0 < R) :
    ∫ x, ‖gradient (fR d R) x‖ ^ 2 ∂dysonProb d ρ β ≤
      (1 + 1 / R) * d + (1 + R) * (M / R) ^ 2 * (d / ρ) := by
  have := isProbabilityMeasure_dysonProb hd hρ hβ
  have h2 : ∫ x, hsum d x ^ 2 ∂dysonProb d ρ β = d / ρ := by
    have := hsum_second_moment hd hρ hβ
    field_simp; linarith
  have hint : Integrable (fun x => (1 + 1 / R) * (d : ℝ) + (1 + R) * (M / R) ^ 2 * hsum d x ^ 2)
      (dysonProb d ρ β) :=
    (integrable_const _).add ((hsum_sq_integrable hd hρ hβ).const_mul _)
  have hcont : Continuous fun x : CutCur.Rd d => ‖gradient (fR d R) x‖ ^ 2 := by
    simp only [norm_gradient_eq]
    exact ((fR_contDiff (d := d) R).continuous_fderiv (by simp)).norm.pow 2
  have hle := integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity) hint
    (Eventually.of_forall fun x => norm_gradient_fR_sq_le hR (hM R hR) x)
  refine hle.trans (le_of_eq ?_)
  have e2 : ∫ a, (1 + R) * (M / R) ^ 2 * hsum d a ^ 2 ∂dysonProb d ρ β =
      (1 + R) * (M / R) ^ 2 * (d / ρ) := by rw [integral_const_mul, h2]
  have e1 : ∫ _a : CutCur.Rd d, (1 + 1 / R) * (d : ℝ) ∂dysonProb d ρ β = (1 + 1 / R) * d := by simp
  rw [integral_add (integrable_const _) ((hsum_sq_integrable hd hρ hβ).const_mul _), e1, e2]

end Main

end CutoffRigidity.Dyson
