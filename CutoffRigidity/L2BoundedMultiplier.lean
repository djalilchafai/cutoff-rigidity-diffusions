module

public import CutoffRigidity.GibbsSobolevClassical

/-! # Genuine L² convergence under bounded variable scalar multipliers

Bounded coefficients converging almost everywhere multiply strongly
convergent L² vector fields continuously. The proof splits off the fixed
limit field, applies actual L² dominated convergence there, and controls the
remaining term by the original L² difference.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology
open scoped ENNReal

variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {μ : Measure α}

/-- Multiplication by a genuinely bounded measurable scalar coefficient preserves L². -/
theorem memLp_bounded_scalar_smul {a : α → ℝ} (ha : AEStronglyMeasurable a μ)
    (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ 1) {f : α → F} (hf : MemLp f 2 μ) :
    MemLp (fun x => a x • f x) 2 μ := by
  apply hf.of_le_mul (c := 1) (ha.smul hf.aestronglyMeasurable)
  filter_upwards [hb] with x hx
  change ‖a x • f x‖ ≤ 1 * ‖f x‖
  rw [norm_smul, one_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hx

/-- The actual bounded scalar multiplication of L² representatives. -/
@[expose] noncomputable def boundedScalarMulL2 (a : α → ℝ) (ha : AEStronglyMeasurable a μ)
    (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ 1) (f : α →₂[μ] F) : α →₂[μ] F :=
  (memLp_bounded_scalar_smul ha hb (Lp.memLp f)).toLp (fun x => a x • f x)

theorem boundedScalarMulL2_coeFn (a : α → ℝ) (ha : AEStronglyMeasurable a μ)
    (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ 1) (f : α →₂[μ] F) :
    boundedScalarMulL2 a ha hb f =ᵐ[μ] fun x => a x • f x :=
  (memLp_bounded_scalar_smul ha hb (Lp.memLp f)).coeFn_toLp

/-- Each actual bounded multiplier contracts differences in L². -/
theorem norm_boundedScalarMulL2_sub_le (a : α → ℝ) (ha : AEStronglyMeasurable a μ)
    (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ 1) (f g : α →₂[μ] F) :
    ‖boundedScalarMulL2 a ha hb f - boundedScalarMulL2 a ha hb g‖ ≤ ‖f - g‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub (boundedScalarMulL2 a ha hb f) (boundedScalarMulL2 a ha hb g),
    boundedScalarMulL2_coeFn a ha hb f, boundedScalarMulL2_coeFn a ha hb g,
    Lp.coeFn_sub f g, hb] with x hsub hf hg hfg hx
  rw [hsub, Pi.sub_apply, hf, hg, ← smul_sub, hfg, Pi.sub_apply, norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) hx

set_option maxHeartbeats 500000 in
/-- The actual variable-coefficient convergence needed for the closed
Sobolev chain rule, with no multiplication-continuity premise. -/
theorem boundedScalarMulL2_tendsto
    {an : ℕ → α → ℝ} {a : α → ℝ}
    (han : ∀ n, AEStronglyMeasurable (an n) μ) (ha : AEStronglyMeasurable a μ)
    (hbn : ∀ n, ∀ᵐ x ∂μ, ‖an n x‖ ≤ 1) (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ 1)
    (halim : ∀ᵐ x ∂μ, Tendsto (fun n => an n x) atTop (𝓝 (a x)))
    {fn : ℕ → α →₂[μ] F} {f : α →₂[μ] F} (hfn : Tendsto fn atTop (𝓝 f)) :
    Tendsto (fun n => boundedScalarMulL2 (an n) (han n) (hbn n) (fn n)) atTop
      (𝓝 (boundedScalarMulL2 a ha hb f)) := by
  have hfixed : Tendsto (fun n => boundedScalarMulL2 (an n) (han n) (hbn n) f) atTop
      (𝓝 (boundedScalarMulL2 a ha hb f)) := by
    unfold boundedScalarMulL2
    apply tendsto_toL2_of_dominated_sq
      (memLp_bounded_scalar_smul ha hb (Lp.memLp f))
      (fun n => memLp_bounded_scalar_smul (han n) (hbn n) (Lp.memLp f))
      (fun x => 4 * ‖f x‖ ^ 2) ((Lp.memLp f).norm.integrable_sq.const_mul 4)
    · intro n
      filter_upwards [hbn n, hb] with x hnx hx
      have hn := norm_sub_le (an n x • f x) (a x • f x)
      rw [norm_smul, norm_smul] at hn
      have h1 := mul_le_of_le_one_left (norm_nonneg (f x)) hnx
      have h2 := mul_le_of_le_one_left (norm_nonneg (f x)) hx
      nlinarith [norm_nonneg (an n x • f x - a x • f x)]
    · filter_upwards [halim] with x hx
      exact hx.smul_const (f x)
  have hnormfn : Tendsto (fun n => ‖fn n - f‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hfn
  have hnormfixed : Tendsto (fun n => ‖boundedScalarMulL2 (an n) (han n) (hbn n) f - boundedScalarMulL2 a ha hb f‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp hfixed
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) (by simpa using hnormfn.add hnormfixed)
  have hcontract := norm_boundedScalarMulL2_sub_le (an n) (han n) (hbn n) (fn n) f
  exact le_trans (norm_sub_le_norm_sub_add_norm_sub
    (boundedScalarMulL2 (an n) (han n) (hbn n) (fn n))
    (boundedScalarMulL2 (an n) (han n) (hbn n) f)
    (boundedScalarMulL2 a ha hb f)) (add_le_add hcontract le_rfl)end CutoffRigidity
