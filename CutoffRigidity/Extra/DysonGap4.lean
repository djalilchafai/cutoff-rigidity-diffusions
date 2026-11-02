module

public import CutoffRigidity.Extra.DysonGap3

/-! # Dyson--OU: `Σ x_i` is a weak eigenfunction at the bottom of the spectrum, in the closure of `C_c^∞`

Final statement `dyson_spectralGap_eigenfunction` (see its docstring). -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal NNReal

namespace CutoffRigidity.Dyson

variable {d : ℕ}


/-- Pointwise `H¹` error of the cutoff approximant. -/
theorem norm_gradient_sub_sq_le {M R : ℝ} (hR : 0 < R)
    (hM : ∀ x : CutCur.Rd d, ‖fderiv ℝ (cut d R) x‖ ≤ M / R) (x : CutCur.Rd d) :
    ‖gradient (fR d R) x - gradient (hsum d) x‖ ^ 2 ≤
      2 * d * (1 - cut d R x) ^ 2 + 2 * (M / R) ^ 2 * hsum d x ^ 2 := by
  have e : ‖gradient (fR d R) x - gradient (hsum d) x‖ =
      ‖fderiv ℝ (fR d R) x - innerSL ℝ (CutCur.diagonal d)‖ := by
    rw [show gradient (fR d R) x - gradient (hsum d) x = (InnerProductSpace.toDual ℝ (CutCur.Rd d)).symm
      (fderiv ℝ (fR d R) x - innerSL ℝ (CutCur.diagonal d)) by
        simp [gradient, (hasFDerivAt_hsum x).fderiv], LinearIsometryEquiv.norm_map]
  rw [e]
  have hA2 := norm_fderiv_hsum_sq (d := d)
  have hMR : 0 ≤ M / R := (norm_nonneg _).trans (hM 0)
  have hdiff : fderiv ℝ (fR d R) x - innerSL ℝ (CutCur.diagonal d) =
      (cut d R x - 1) • innerSL ℝ (CutCur.diagonal d) + hsum d x • fderiv ℝ (cut d R) x := by
    rw [fderiv_fR, sub_smul, one_smul]; abel
  set A := ‖innerSL ℝ (CutCur.diagonal d)‖
  set a := |cut d R x - 1| * A with ha
  set b := |hsum d x| * (M / R) with hb
  have h0 : ‖fderiv ℝ (fR d R) x - innerSL ℝ (CutCur.diagonal d)‖ ≤ a + b := by
    rw [hdiff]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg _)
  have ha0 : 0 ≤ a := mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hb0 : 0 ≤ b := mul_nonneg (abs_nonneg _) hMR
  have ha2 : a ^ 2 = (1 - cut d R x) ^ 2 * d := by
    rw [ha, mul_pow, sq_abs, hA2]; ring
  have hb2 : b ^ 2 = (M / R) ^ 2 * hsum d x ^ 2 := by
    rw [hb, mul_pow, sq_abs]; ring
  calc _ ≤ (a + b) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h0 2
    _ ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]
    _ = _ := by rw [ha2, hb2]; ring

section Main
variable (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ) {β : ℝ} (hβ : 0 ≤ β)
include hd hρ hβ

theorem tendsto_L2_fR :
    Tendsto (fun R => ∫ x, (fR d R x - hsum d x) ^ 2 ∂dysonProb d ρ β) atTop (𝓝 0) := by
  have := isProbabilityMeasure_dysonProb hd hρ hβ
  have h0 : (0 : ℝ) = ∫ _x : CutCur.Rd d, (0 : ℝ) ∂dysonProb d ρ β := by simp
  rw [h0]
  refine tendsto_integral_filter_of_dominated_convergence (fun x => hsum d x ^ 2) ?_ ?_
    (hsum_sq_integrable hd hρ hβ) (Eventually.of_forall fun x => ?_)
  · exact Eventually.of_forall fun R =>
      (((fR_contDiff (d := d) R).continuous.sub hsum_contDiff.continuous).pow 2).aestronglyMeasurable
  · refine Eventually.of_forall fun R => Eventually.of_forall fun x => ?_
    have : fR d R x - hsum d x = (cut d R x - 1) * hsum d x := by simp [fR]; ring
    rw [this, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
    have h1 : (cut d R x - 1) ^ 2 ≤ 1 := by nlinarith [cut_nonneg R x, cut_le_one R x]
    exact mul_le_of_le_one_left (sq_nonneg _) h1
  · show Tendsto (fun R => (fR d R x - hsum d x) ^ 2) atTop (𝓝 0)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ‖x‖, eventually_gt_atTop 0] with R h1 h2
    simp [fR, cut_eq_one h2 h1]

theorem one_sub_cut_sq_integrable (R : ℝ) :
    Integrable (fun x : CutCur.Rd d => (1 - cut d R x) ^ 2) (dysonProb d ρ β) := by
  have := isProbabilityMeasure_dysonProb hd hρ hβ
  refine Integrable.mono' (integrable_const (1 : ℝ))
    ((continuous_const.sub (cut_contDiff (d := d) R).continuous).pow 2).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [cut_nonneg R x, cut_le_one R x]

theorem tendsto_one_sub_cut_sq :
    Tendsto (fun R => ∫ x, (1 - cut d R x) ^ 2 ∂dysonProb d ρ β) atTop (𝓝 0) := by
  have := isProbabilityMeasure_dysonProb hd hρ hβ
  have h0 : (0 : ℝ) = ∫ _x : CutCur.Rd d, (0 : ℝ) ∂dysonProb d ρ β := by simp
  rw [h0]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_
    (integrable_const _) (Eventually.of_forall fun x => ?_)
  · exact Eventually.of_forall fun R =>
      ((continuous_const.sub (cut_contDiff (d := d) R).continuous).pow 2).aestronglyMeasurable
  · refine Eventually.of_forall fun R => Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [cut_nonneg R x, cut_le_one R x]
  · show Tendsto (fun R => (1 - cut d R x) ^ 2) atTop (𝓝 0)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ‖x‖, eventually_gt_atTop 0] with R h1 h2
    simp [cut_eq_one h2 h1]

/-- `fR → h` in `H¹(μ)`: the gradients converge in `L²(μ)`. -/
theorem tendsto_H1_fR :
    Tendsto (fun R => ∫ x, ‖gradient (fR d R) x - gradient (hsum d) x‖ ^ 2 ∂dysonProb d ρ β)
      atTop (𝓝 0) := by
  have := isProbabilityMeasure_dysonProb hd hρ hβ
  obtain ⟨M, hM⟩ := exists_fderiv_cut_bound (d := d)
  have h2 : ∫ x, hsum d x ^ 2 ∂dysonProb d ρ β = d / ρ := by
    have := hsum_second_moment hd hρ hβ
    field_simp; linarith
  have ht : Tendsto (fun R : ℝ => 1 / R) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  set w : ℝ → ℝ := fun t => 2 * d * (∫ x, (1 - cut d (1 / t) x) ^ 2 ∂dysonProb d ρ β) with hw
  have hupper : Tendsto (fun R : ℝ => 2 * d * (∫ x, (1 - cut d R x) ^ 2 ∂dysonProb d ρ β) +
      2 * (M / R) ^ 2 * (d / ρ)) atTop (𝓝 0) := by
    have h1 := (tendsto_one_sub_cut_sq hd hρ hβ).const_mul (2 * (d : ℝ))
    have h3 : Tendsto (fun R : ℝ => 2 * M ^ 2 * (d / ρ) * (1 / R) ^ 2) atTop (𝓝 0) := by
      have := (ht.pow 2).const_mul (2 * M ^ 2 * (d / ρ))
      simpa using this
    have := h1.add h3
    simp only [mul_zero, add_zero] at this
    refine this.congr fun R => ?_
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun R => integral_nonneg fun x => by positivity) ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  have hint : Integrable (fun x => 2 * (d : ℝ) * (1 - cut d R x) ^ 2 + 2 * (M / R) ^ 2 * hsum d x ^ 2)
      (dysonProb d ρ β) :=
    ((one_sub_cut_sq_integrable hd hρ hβ R).const_mul _).add
      ((hsum_sq_integrable hd hρ hβ).const_mul _)
  refine (integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity) hint
    (Eventually.of_forall fun x => norm_gradient_sub_sq_le hR (hM R hR) x)).trans (le_of_eq ?_)
  rw [integral_add ((one_sub_cut_sq_integrable hd hρ hβ R).const_mul _)
    ((hsum_sq_integrable hd hρ hβ).const_mul _), integral_const_mul, integral_const_mul, h2]

/-- The Rayleigh quotient of `h = Σ x_i` is exactly `ρ`. -/
theorem rayleigh_hsum :
    (∫ x, ‖gradient (hsum d) x‖ ^ 2 ∂dysonProb d ρ β) / variance (hsum d) (dysonProb d ρ β) = ρ := by
  have := isProbabilityMeasure_dysonProb hd hρ hβ
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  simp only [gradient_hsum_sq, integral_const, probReal_univ, one_smul, hsum_variance hd hρ hβ]
  field_simp

end Main

/-- **The spectral gap of the Dyson--OU Gibbs measure on the Weyl chamber, and its eigenfunction
`x_1 + ⋯ + x_d`.** For `d ≥ 1`, `ρ > 0`, `β ≥ 0`, with `μ = dysonProb d ρ β` and `h(x) = Σ x_i`:
1. `dysonSpectralGap d ρ β = ρ` (Rayleigh infimum over `C_c^∞(ℝ^d)`, `ρ` is the infimum, same
   class and junk value as `CutCur.spectralGap`);
2. `h ∈ L²(μ)`, `Var_μ h > 0`, and the Rayleigh quotient of `h` is exactly `ρ`;
3. weak (Neumann) eigenfunction equation `∫ ⟨∇h, ∇φ⟩ dμ = ρ ∫ h φ dμ` for all `φ ∈ C_c^∞(ℝ^d)`;
4. `h` is a limit of `C_c^∞(ℝ^d)` functions `f_n` (all with positive variance) in `H¹(μ)`:
   `∫ (f_n - h)² dμ → 0` and `∫ ‖∇f_n - ∇h‖² dμ → 0`; i.e. `h` lies in the closure of `C_c^∞` in the
   form domain, where the infimum is attained. -/
theorem dyson_spectralGap_eigenfunction (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ) {β : ℝ} (hβ : 0 ≤ β) :
    dysonSpectralGap d ρ β = ρ ∧
    (MemLp (fun x : CutCur.Rd d => ∑ i, x i) 2 (dysonProb d ρ β) ∧
      0 < variance (fun x : CutCur.Rd d => ∑ i, x i) (dysonProb d ρ β) ∧
      (∫ x, ‖gradient (fun y : CutCur.Rd d => ∑ i, y i) x‖ ^ 2 ∂dysonProb d ρ β) /
        variance (fun x : CutCur.Rd d => ∑ i, x i) (dysonProb d ρ β) = ρ) ∧
    (∀ φ : CutCur.Rd d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, inner ℝ (gradient (fun y : CutCur.Rd d => ∑ i, y i) x) (gradient φ x) ∂dysonProb d ρ β =
        ρ * ∫ x, (∑ i, x i) * φ x ∂dysonProb d ρ β) ∧
    ∃ f : ℕ → CutCur.Rd d → ℝ, (∀ n, ContDiff ℝ ∞ (f n) ∧ HasCompactSupport (f n) ∧
        0 < variance (f n) (dysonProb d ρ β)) ∧
      Tendsto (fun n => ∫ x, (f n x - ∑ i, x i) ^ 2 ∂dysonProb d ρ β) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ x, ‖gradient (f n) x - gradient (fun y : CutCur.Rd d => ∑ i, y i) x‖ ^ 2
        ∂dysonProb d ρ β) atTop (𝓝 0) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨dysonSpectralGap_eq hd hρ hβ, ⟨hsum_memLp hd hρ hβ, ?_, rayleigh_hsum hd hρ hβ⟩,
    fun φ h1 h2 => dyson_neumann hd hρ hβ (isTestFunction_of_compact h1 h2), ?_⟩
  · show 0 < variance (hsum d) _
    rw [hsum_variance hd hρ hβ]; positivity
  · have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hV := (tendsto_variance_fR hd hρ hβ).comp hn
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hV.eventually (lt_mem_nhds (show (0 : ℝ) < d / ρ by positivity)))
    have hm : Tendsto (fun n : ℕ => n + N) atTop atTop := tendsto_add_atTop_nat N
    refine ⟨fun n => fR d (((n + N : ℕ) : ℝ) + 1), fun n => ⟨fR_contDiff _, fR_compact (by positivity), ?_⟩,
      (tendsto_L2_fR hd hρ hβ).comp (hn.comp hm), (tendsto_H1_fR hd hρ hβ).comp (hn.comp hm)⟩
    exact hN (n + N) (by omega)

end CutoffRigidity.Dyson
