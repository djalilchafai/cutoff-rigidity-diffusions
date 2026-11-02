module

public import Mathlib
public import CutoffRigidity.Extra.Rothaus2

/-! # Rothaus remark (stage 3): a generalised dominated convergence theorem -/

@[expose] public section

open MeasureTheory Filter Topology

namespace CutoffRigidity.Rothaus

/-- Generalised dominated convergence: the dominating functions `B n` only converge to `b` in `L¹`. -/
theorem tendsto_integral_of_dominated_L1 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} {f : α → ℝ} {B : ℕ → α → ℝ} {b : α → ℝ}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ) (hb : Integrable b μ) (hBn : ∀ n, Integrable (B n) μ)
    (hdom : ∀ n, ∀ᵐ x ∂μ, |F n x| ≤ B n x)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hBae : ∀ᵐ x ∂μ, Tendsto (fun n => B n x) atTop (𝓝 (b x)))
    (hBL1 : Tendsto (fun n => ∫ x, |B n x - b x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hdom' : ∀ᵐ x ∂μ, ∀ n, |F n x| ≤ B n x := ae_all_iff.2 hdom
  have hb0 : ∀ᵐ x ∂μ, 0 ≤ b x := by
    filter_upwards [hdom', hBae] with x h1 h2
    exact ge_of_tendsto' h2 fun n => (abs_nonneg _).trans (h1 n)
  have hfb : ∀ᵐ x ∂μ, |f x| ≤ b x := by
    filter_upwards [hdom', hae, hBae] with x h1 h2 h3
    exact le_of_tendsto_of_tendsto' h2.abs h3 h1
  set G : ℕ → α → ℝ := fun n x => max (-b x) (min (F n x) (b x)) with hG
  have hGm : ∀ n, AEStronglyMeasurable (G n) μ := fun n =>
    (hb.aestronglyMeasurable.neg).sup ((hF n).inf hb.aestronglyMeasurable)
  have hGb : ∀ n, ∀ᵐ x ∂μ, ‖G n x‖ ≤ b x := by
    intro n
    filter_upwards [hb0] with x hx
    rw [Real.norm_eq_abs, abs_le]
    refine ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  have hGlim : ∀ᵐ x ∂μ, Tendsto (fun n => G n x) atTop (𝓝 (f x)) := by
    filter_upwards [hae, hfb] with x h1 h2
    have : Tendsto (fun n => max (-b x) (min (F n x) (b x))) atTop (𝓝 (max (-b x) (min (f x) (b x)))) :=
      (tendsto_const_nhds.max ((h1.min tendsto_const_nhds)))
    have e : max (-b x) (min (f x) (b x)) = f x := by
      rw [abs_le] at h2
      rw [min_eq_left h2.2, max_eq_right h2.1]
    rwa [e] at this
  have h1 : Tendsto (fun n => ∫ x, G n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) :=
    tendsto_integral_of_dominated_convergence b hGm hb hGb hGlim
  have hFi : ∀ n, Integrable (F n) μ := fun n =>
    Integrable.mono' (hBn n) (hF n) (by simpa [Real.norm_eq_abs] using hdom n)
  have hGi : ∀ n, Integrable (G n) μ := fun n => Integrable.mono' hb (hGm n) (hGb n)
  have hdiff : ∀ n, ∀ᵐ x ∂μ, ‖F n x - G n x‖ ≤ |B n x - b x| := by
    intro n
    filter_upwards [hdom n, hb0] with x hx hb0'
    rw [Real.norm_eq_abs]
    by_cases hc : |F n x| ≤ b x
    · have : G n x = F n x := by
        rw [abs_le] at hc
        simp only [hG]
        rw [min_eq_left hc.2, max_eq_right hc.1]
      rw [this]; simp
    · have hc := not_le.1 hc
      rcases le_or_gt 0 (F n x) with hp | hp
      · rw [abs_of_nonneg hp] at hc
        have : G n x = b x := by
          simp only [hG]
          rw [min_eq_right hc.le, max_eq_right (by linarith)]
        rw [this, abs_of_nonneg hp] at *
        rw [abs_of_nonneg (by linarith)]
        have := (abs_of_nonneg hp) ▸ hx
        have h5 := le_abs_self (B n x - b x)
        linarith [abs_of_nonneg hp]
      · rw [abs_of_neg hp] at hc
        have : G n x = -b x := by
          simp only [hG]
          rw [min_eq_left (by linarith), max_eq_left (by linarith)]
        rw [this, abs_of_neg hp] at *
        rw [abs_of_nonpos (by linarith)]
        have h5 := le_abs_self (B n x - b x)
        linarith
  have h2 : Tendsto (fun n => ∫ x, (F n x - G n x) ∂μ) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hBL1
    calc ‖∫ x, (F n x - G n x) ∂μ‖ ≤ ∫ x, ‖F n x - G n x‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, |B n x - b x| ∂μ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _) ?_ (hdiff n)
          exact ((hBn n).sub hb).abs
  have := h1.add h2
  simp only [add_zero] at this
  refine this.congr fun n => ?_
  rw [integral_sub (hFi n) (hGi n)]; ring

end CutoffRigidity.Rothaus
