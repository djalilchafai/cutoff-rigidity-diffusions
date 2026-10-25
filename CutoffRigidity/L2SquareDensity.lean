module
public import CutoffRigidity.TransportMoments

/-! # Genuine L¹ continuity of squared L² density roots -/
public section
namespace CutoffRigidity
open MeasureTheory Filter
open scoped ENNReal Topology

private theorem integral_norm_sq_L2 {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u : X →₂[μ] ℝ) : (∫ x, ‖u x‖ ^ 2 ∂μ) = ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards with x
  rw [real_inner_self_eq_norm_sq]

/-- Actual L¹ differences of squared L² classes satisfy the true product
bound from Cauchy--Schwarz. -/
theorem integral_abs_sq_sub_sq_le_L2 {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u v : X →₂[μ] ℝ) :
    (∫ x, |u x ^ 2 - v x ^ 2| ∂μ) ≤ ‖u - v‖ * ‖u + v‖ := by
  have hh := integral_mul_le_second_moments (Lp.memLp (u - v)).norm (Lp.memLp (u + v)).norm
  rw [integral_norm_sq_L2 (u - v), integral_norm_sq_L2 (u + v),
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hh
  have heq : (∫ x, |u x ^ 2 - v x ^ 2| ∂μ) =
      ∫ x, ‖(u - v) x‖ * ‖(u + v) x‖ ∂μ := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub u v, Lp.coeFn_add u v] with x hs ha
    rw [hs, ha, Pi.sub_apply, Pi.add_apply, Real.norm_eq_abs, Real.norm_eq_abs, ← abs_mul]
    congr 1
    ring
  exact heq.trans_le hh

/-- Strong L² convergence of actual root classes gives genuine L¹
convergence of their squared densities. -/
theorem tendsto_integral_abs_sq_sub_sq_of_L2 {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {un : ℕ → X →₂[μ] ℝ} {u : X →₂[μ] ℝ} (hlim : Tendsto un atTop (𝓝 u)) :
    Tendsto (fun n => ∫ x, |un n x ^ 2 - u x ^ 2| ∂μ) atTop (𝓝 0) := by
  have hn : Tendsto (fun n => ‖un n - u‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp hlim
  have hs := hn.mul ((hlim.add_const u).norm)
  simp only [zero_mul] at hs
  exact squeeze_zero (fun n => integral_nonneg (fun x => abs_nonneg _))
    (fun n => integral_abs_sq_sub_sq_le_L2 (un n) u) hs

/-- A genuine positive normalized square has a quantitative L¹ error
bound before either regularization or graph limits are taken. -/
theorem integral_abs_regularized_square_sub_le
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {f g : X → ℝ} (hf : Integrable (fun x => f x ^ 2) μ)
    (hg : Integrable (fun x => g x ^ 2) μ) (hgNorm : ∫ x, g x ^ 2 ∂μ = 1)
    {a ε : ℝ} (ha : 0 < a) (hε : 0 ≤ ε) :
    (∫ x, |(f x ^ 2 + ε) / a - g x ^ 2| ∂μ) ≤
      (∫ x, |f x ^ 2 - g x ^ 2| ∂μ) / a + |a⁻¹ - 1| + ε / a := by
  have hleft := ((hf.add (integrable_const ε)).div_const a).sub hg
  have hi1 : Integrable (fun x => |f x ^ 2 - g x ^ 2| / a) μ := by
    simpa only [Pi.sub_apply] using (hf.sub hg).abs.div_const a
  have hi2 : Integrable (fun x => |a⁻¹ - 1| * g x ^ 2) μ := hg.const_mul _
  have hright := (hi1.add hi2).add (integrable_const (ε / a))
  have hh := integral_mono hleft.abs hright (fun x => ?_)
  · simp only [Pi.add_apply, Pi.sub_apply] at hh
    have ha1 := integral_add (hi1.add hi2) (integrable_const (ε / a))
    have ha2 := integral_add hi1 hi2
    simp only [Pi.add_apply] at ha1 ha2
    rw [ha1, ha2, integral_div, integral_const_mul, hgNorm] at hh
    simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, mul_one] using hh
  · have heq : (f x ^ 2 + ε) / a - g x ^ 2 =
        (f x ^ 2 - g x ^ 2) / a + (a⁻¹ - 1) * g x ^ 2 + ε / a := by ring
    change |(f x ^ 2 + ε) / a - g x ^ 2| ≤ _
    rw [heq]
    have ht := (abs_add_le ((f x ^ 2 - g x ^ 2) / a + (a⁻¹ - 1) * g x ^ 2) (ε / a)).trans
      (add_le_add (abs_add_le ((f x ^ 2 - g x ^ 2) / a) ((a⁻¹ - 1) * g x ^ 2)) le_rfl)
    simpa only [Pi.add_apply, abs_div, abs_of_pos ha, abs_mul, abs_sq, abs_of_nonneg hε] using ht

/-- Actual normalized positive squares converge in L¹ to a normalized
actual L² root squared, when the regularization tends to zero. -/
theorem tendsto_integral_abs_regularized_squares_of_L2
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {un : ℕ → X →₂[μ] ℝ} {u : X →₂[μ] ℝ} (hlim : Tendsto un atTop (𝓝 u))
    (hu : ‖u‖ ^ 2 = 1) {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, |(un n x ^ 2 + ε n) / (‖un n‖ ^ 2 + ε n) - u x ^ 2| ∂μ) atTop (𝓝 0) := by
  have hDen : Tendsto (fun n => ‖un n‖ ^ 2 + ε n) atTop (𝓝 (1 : ℝ)) := by
    simpa only [hu, add_zero] using (hlim.norm.pow 2).add hεlim
  have hSq := tendsto_integral_abs_sq_sub_sq_of_L2 hlim
  have h1 := hSq.div hDen (by norm_num)
  have h2 := (((tendsto_const_nhds (x := (1 : ℝ))).div hDen (by norm_num)).sub_const 1).abs
  have h3 := hεlim.div hDen (by norm_num)
  have hh := (h1.add h2).add h3
  simp only [zero_div, one_div, inv_one, sub_self, abs_zero, add_zero] at hh
  apply squeeze_zero (fun n => integral_nonneg (fun x => abs_nonneg _)) ?_ hh
  intro n
  have hgNorm : ∫ x, u x ^ 2 ∂μ = 1 := by
    have heq : (∫ x, u x ^ 2 ∂μ) = ‖u‖ ^ 2 := by
      simpa only [Real.norm_eq_abs, sq_abs] using integral_norm_sq_L2 u
    exact heq.trans hu
  simpa only [Pi.div_apply, one_div] using integral_abs_regularized_square_sub_le (a := ‖un n‖ ^ 2 + ε n) (ε := ε n)
    (Lp.memLp (un n)).integrable_sq (Lp.memLp u).integrable_sq
    hgNorm (add_pos_of_nonneg_of_pos (sq_nonneg _) (hε n)) (hε n).le

end CutoffRigidity
