module
public import CutoffRigidity.HopfLaxHypercontractivity
public import CutoffRigidity.HopfLaxTimeZero

/-! # Actual initial derivative of the Hamilton–Jacobi exponential moment -/
public section
namespace CutoffRigidity
open Set Filter MeasureTheory
open scoped Topology NNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A genuine common local Lipschitz bound for the exponential curves,
now including time zero. -/
theorem exists_uniform_lipschitzOnWith_exp_hopfLax_near_zero
    {b ρ M : ℝ} (hb : 0 < b) (hρ : 0 ≤ ρ)
    {f : E → ℝ} (hf : ∀ x,|f x| ≤ M) {L : NNReal} (hL : LipschitzWith L f) :
    ∃ C : NNReal, ∀ x, LipschitzOnWith C
      (fun t : ℝ => Real.exp (ρ*t*hopfLax t f x)) (Ioo (-b) b) := by
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hf 0)
  let K := ρ*(3*M)
  let R := ρ*b*M
  refine ⟨⟨Real.exp R*K,by dsimp only [K]; positivity⟩,?_⟩
  intro x
  have hPhi := lipschitzWith_time_mul_hopfLax hf hL.continuous x
  have hRange (t : ℝ) (ht : t ∈ Ioo (-b) b) : ρ*t*hopfLax t f x ≤ R := by
    have htN : |t| ≤ b := abs_le.mpr ⟨ht.1.le,ht.2.le⟩
    calc
      _ ≤ |ρ*t*hopfLax t f x| := le_abs_self _
      _ = ρ*|t| *|hopfLax t f x| := by rw [abs_mul,abs_mul,abs_of_nonneg hρ]
      _ ≤ ρ*b*M := mul_le_mul (mul_le_mul_of_nonneg_left htN hρ) (abs_hopfLax_le hf t x)
        (abs_nonneg _) (by positivity)
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  have he := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z (_hz : z ∈ Iic R) => Real.differentiableAt_exp)
    (fun z (hz : z ∈ Iic R) => by rw [Real.deriv_exp,Real.norm_of_nonneg (Real.exp_nonneg _)]; exact Real.exp_le_exp.mpr hz)
    (convex_Iic R) (hRange t ht) (hRange s hs)
  change ‖Real.exp (ρ*s*hopfLax s f x)-Real.exp (ρ*t*hopfLax t f x)‖ ≤ (Real.exp R*K)*‖s-t‖
  apply he.trans
  have hDiff : ‖ρ*s*hopfLax s f x-ρ*t*hopfLax t f x‖ ≤ K*‖s-t‖ := by
    have hh := hPhi.norm_sub_le s t
    change ‖s*hopfLax s f x-t*hopfLax t f x‖ ≤ (3*M)*‖s-t‖ at hh
    rw [show ρ*s*hopfLax s f x-ρ*t*hopfLax t f x = ρ*(s*hopfLax s f x-t*hopfLax t f x) by ring,
      norm_mul,Real.norm_of_nonneg hρ]
    exact (mul_le_mul_of_nonneg_left hh hρ).trans_eq (by dsimp only [K]; ring)
  exact (mul_le_mul_of_nonneg_left hDiff (Real.exp_nonneg _)).trans_eq (by ring)

/-- The actual exponential moment starts with derivative ρ∫f, with all
zero-time approximation and domination conditions derived. -/
theorem hasDerivAt_hopfLaxExponentialMoment_zero
    (μ : Measure E) [IsProbabilityMeasure μ] {ρ M : ℝ} (hρ : 0 ≤ ρ)
    {f : E → ℝ} (hf : ∀ x,|f x| ≤ M) {L : NNReal} (hL : LipschitzWith L f) :
    HasDerivAt (hopfLaxExponentialMoment μ ρ f) (ρ*∫ x,f x ∂μ) 0 := by
  obtain ⟨C,hC⟩ := exists_uniform_lipschitzOnWith_exp_hopfLax_near_zero (by norm_num : (0:ℝ)<1) hρ hf hL
  have hFI : Integrable (fun x => Real.exp (ρ*0*hopfLax 0 f x)) μ := by
    simpa only [mul_zero,zero_mul,Real.exp_zero] using (integrable_const (1:ℝ) : Integrable (fun _ : E => (1:ℝ)) μ)
  have hFM : ∀ᶠ s in 𝓝 (0:ℝ), AEStronglyMeasurable (fun x => Real.exp (ρ*s*hopfLax s f x)) μ :=
    Eventually.of_forall (fun s => (Real.continuous_exp.comp
      ((lipschitzWith_hopfLax_any_time hf hL s).continuous.const_mul (ρ*s))).aestronglyMeasurable)
  have hDeriv : ∀ᵐ x ∂μ, HasDerivAt (fun s => Real.exp (ρ*s*hopfLax s f x)) (ρ*f x) 0 := by
    apply Eventually.of_forall
    intro x
    have hh := ((hasDerivAt_time_mul_hopfLax_zero hf hL x).const_mul ρ).exp
    convert hh using 1
    · funext s; simp only [mul_assoc]
    · simp only [zero_mul,mul_zero,Real.exp_zero,one_mul]
  have hh := (hasDerivAt_integral_of_dominated_loc_of_lip (μ := μ)
    (bound := fun _ => (C:ℝ)) (s := Ioo (-1:ℝ) 1)
    (Ioo_mem_nhds (by norm_num) (by norm_num)) hFM hFI
    (hL.continuous.measurable.const_mul ρ).aestronglyMeasurable
    (Eventually.of_forall (fun x => by simpa using hC x)) (integrable_const (C:ℝ)) hDeriv).2
  simpa only [hopfLaxExponentialMoment,integral_const_mul] using! hh

/-- The exact zero-time limit in the cited Hamilton–Jacobi argument. -/
theorem tendsto_log_hopfLaxExponentialMoment_div_time_zero
    (μ : Measure E) [IsProbabilityMeasure μ] {ρ M : ℝ} (hρ : 0 ≤ ρ)
    {f : E → ℝ} (hf : ∀ x,|f x| ≤ M) {L : NNReal} (hL : LipschitzWith L f) :
    Tendsto (fun t : ℝ => Real.log (hopfLaxExponentialMoment μ ρ f t)/t)
      (𝓝[≠] 0) (𝓝 (ρ*∫ x,f x ∂μ)) := by
  have hZ0 : hopfLaxExponentialMoment μ ρ f 0 = 1 := by
    simp [hopfLaxExponentialMoment]
  have hD := (hasDerivAt_hopfLaxExponentialMoment_zero μ hρ hf hL).log (by rw [hZ0]; norm_num)
  rw [hZ0,div_one] at hD
  apply hD.tendsto_slope.congr'
  apply Eventually.of_forall
  intro t
  rw [slope_def_module,hZ0,Real.log_one,sub_zero,sub_zero]
  change t⁻¹*Real.log (hopfLaxExponentialMoment μ ρ f t) = Real.log (hopfLaxExponentialMoment μ ρ f t)/t
  ring

end CutoffRigidity
