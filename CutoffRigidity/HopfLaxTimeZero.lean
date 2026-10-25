module
public import CutoffRigidity.HopfLax
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Actual zero-time regularity of the Hamilton–Jacobi moment -/
public section
namespace CutoffRigidity
open Set Filter
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

/-- Multiplying the actual Hopf–Lax curve by time removes its apparent
1/time variation bound, giving a genuine global Lipschitz bound. -/
theorem lipschitzWith_time_mul_hopfLax {M : ℝ} {f : E → ℝ}
    (hf : ∀ x,|f x| ≤ M) (hfc : Continuous f) (x : E) :
    LipschitzWith ⟨3*M,by have := (abs_nonneg (f x)).trans (hf x); positivity⟩
      (fun t : ℝ => t*hopfLax t f x) := by
  have hM : 0 ≤ M := (abs_nonneg (f x)).trans (hf x)
  have hq (t : ℝ) : -M ≤ hopfLax t f x ∧ hopfLax t f x ≤ M := by
    by_cases ht : 0 ≤ t
    · have hh := hopfLax_bounds ht hf x
      exact ⟨hh.1,hh.2.trans (abs_le.mp (hf x)).2⟩
    · rw [hopfLax_nonpos (le_of_not_ge ht)]
      exact abs_le.mp (hf x)
  have hordered {s t : ℝ} (hst : s ≤ t) :
      |t*hopfLax t f x-s*hopfLax s f x| ≤ 3*M*(t-s) := by
    rw [abs_le]
    by_cases hs : 0 < s
    · have hSub := (le_div_iff₀ hs).mp (hopfLax_time_sub_le hs hst hf hfc x)
      have hMono := hopfLax_antitone_time hs hst hf x
      have hsBounds := hq s
      have htBounds := hq t
      have hΔ := sub_nonneg.mpr hst
      constructor <;> nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hMono),
        mul_nonneg hΔ (sub_nonneg.mpr htBounds.2),mul_nonneg hΔ (by linarith : 0 ≤ hopfLax t f x+M)]
    · have hs0 : s ≤ 0 := le_of_not_gt hs
      rw [hopfLax_nonpos hs0]
      by_cases ht : 0 < t
      · have htBounds := hq t
        have hfBounds := abs_le.mp (hf x)
        constructor <;> nlinarith [mul_nonneg ht.le (sub_nonneg.mpr htBounds.2),
          mul_nonneg ht.le (by linarith : 0 ≤ hopfLax t f x+M),
          mul_nonneg (neg_nonneg.mpr hs0) (sub_nonneg.mpr hfBounds.2),
          mul_nonneg (neg_nonneg.mpr hs0) (by linarith : 0 ≤ f x+M)]
      · rw [hopfLax_nonpos (le_of_not_gt ht)]
        have hfBounds := abs_le.mp (hf x)
        have hΔ := sub_nonneg.mpr hst
        constructor <;> nlinarith [mul_nonneg hΔ (sub_nonneg.mpr hfBounds.2),
          mul_nonneg hΔ (by linarith : 0 ≤ f x+M)]
  apply LipschitzWith.of_dist_le_mul
  intro s t
  change |s*hopfLax s f x-t*hopfLax t f x| ≤ 3*M*|s-t|
  rcases le_total s t with hst|hts
  · rw [abs_sub_comm,abs_of_nonpos (sub_nonpos.mpr hst)]
    simpa only [neg_sub] using hordered hst
  · rw [abs_of_nonneg (sub_nonneg.mpr hts)]
    exact hordered hts

omit [ProperSpace E] in
/-- Actual zero-time continuity follows from the proved uniform
quadratic-error bound, including the nonpositive-time convention. -/
theorem continuousAt_hopfLax_zero {M : ℝ} {f : E → ℝ}
    (hf : ∀ x,|f x| ≤ M) {L : NNReal} (hL : LipschitzWith L f) (x : E) :
    ContinuousAt (fun t : ℝ => hopfLax t f x) 0 := by
  have hbound (t : ℝ) : ‖hopfLax t f x-f x‖ ≤ |t| *(L:ℝ)^2/2 := by
    by_cases ht : 0 ≤ t
    · simpa only [abs_of_nonneg ht] using norm_hopfLax_sub_le ht hf hL x
    · rw [hopfLax_nonpos (le_of_not_ge ht),sub_self,norm_zero]
      positivity
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  change Tendsto (fun t : ℝ => ‖hopfLax t f x-hopfLax 0 f x‖) (𝓝 0) (𝓝 0)
  rw [show hopfLax (0:ℝ) f x = f x by simp [hopfLax]]
  apply squeeze_zero (fun t => norm_nonneg _) hbound
  simpa only [id_eq,abs_zero,zero_mul,zero_div] using (((continuousAt_id (x := (0:ℝ))).abs.mul_const ((L:ℝ)^2)).div_const 2).tendsto

omit [ProperSpace E] in
/-- The nonpositive-time convention preserves the same spatial Lipschitz
constant, so the actual family is spatially continuous at every time. -/
theorem lipschitzWith_hopfLax_any_time {M : ℝ} {f : E → ℝ}
    (hf : ∀ x,|f x| ≤ M) {L : NNReal} (hL : LipschitzWith L f) (t : ℝ) :
    LipschitzWith L (hopfLax t f) := by
  by_cases ht : 0 ≤ t
  · exact lipschitzWith_hopfLax ht hf hL
  · rw [hopfLax_nonpos (le_of_not_ge ht)]; exact hL

omit [ProperSpace E] in
/-- Actual boundedness at all real times, including the convention at zero. -/
theorem abs_hopfLax_le {M : ℝ} {f : E → ℝ} (hf : ∀ x,|f x| ≤ M) (t : ℝ) (x : E) :
    |hopfLax t f x| ≤ M := by
  by_cases ht : 0 ≤ t
  · have hh := hopfLax_bounds ht hf x
    exact abs_le.mpr ⟨hh.1,hh.2.trans (abs_le.mp (hf x)).2⟩
  · rw [hopfLax_nonpos (le_of_not_ge ht)]; exact hf x

omit [ProperSpace E] in
/-- The actual time-multiplied curve has its genuine derivative at zero;
the initial-value approximation is proved, not assumed. -/
theorem hasDerivAt_time_mul_hopfLax_zero {M : ℝ} {f : E → ℝ}
    (hf : ∀ x,|f x| ≤ M) {L : NNReal} (hL : LipschitzWith L f) (x : E) :
    HasDerivAt (fun t : ℝ => t*hopfLax t f x) (f x) 0 := by
  have hcont : Tendsto (fun t : ℝ => hopfLax t f x) (𝓝 0) (𝓝 (f x)) := by
    simpa only [ContinuousAt,hopfLax,lt_self_iff_false,↓reduceIte] using continuousAt_hopfLax_zero hf hL x
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply (hcont.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  symm
  rw [slope_def_module]
  change (t-0)⁻¹*(t*hopfLax t f x-0*hopfLax 0 f x) = hopfLax t f x
  simp only [sub_zero,zero_mul]
  have ht0 : t ≠ 0 := ht
  field_simp [ht0]

end CutoffRigidity
