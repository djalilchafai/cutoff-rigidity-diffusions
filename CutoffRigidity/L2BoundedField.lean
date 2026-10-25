module
public import CutoffRigidity.L2BoundedMultiplier

/-! # Genuine bounded operator fields acting on L²

Pointwise application of an actual bounded measurable continuous-linear-map
field preserves strong L² convergence, by the actual operator norm estimate.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter Topology
variable {α F G : Type*} [MeasurableSpace α]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {μ : Measure α}

theorem memLp_bounded_field_apply
    {b : α → F →L[ℝ] G} (hb : AEStronglyMeasurable b μ) {M : ℝ}
    (hbound : ∀ᵐ x ∂μ, ‖b x‖ ≤ M) {f : α → F} (hf : MemLp f 2 μ) :
    MemLp (fun x => b x (f x)) 2 μ := by
  apply hf.of_le_mul (c := M)
    ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hb.prodMk hf.aestronglyMeasurable))
  filter_upwards [hbound] with x hx
  exact (b x).le_opNorm (f x) |>.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

@[expose] noncomputable def boundedFieldL2
    (b : α → F →L[ℝ] G) (hb : AEStronglyMeasurable b μ) (M : ℝ)
    (hbound : ∀ᵐ x ∂μ, ‖b x‖ ≤ M) (f : α →₂[μ] F) : α →₂[μ] G :=
  (memLp_bounded_field_apply hb hbound (Lp.memLp f)).toLp (fun x => b x (f x))

theorem boundedFieldL2_coeFn
    (b : α → F →L[ℝ] G) (hb : AEStronglyMeasurable b μ) (M : ℝ)
    (hbound : ∀ᵐ x ∂μ, ‖b x‖ ≤ M) (f : α →₂[μ] F) :
    boundedFieldL2 b hb M hbound f =ᵐ[μ] fun x => b x (f x) :=
  (memLp_bounded_field_apply hb hbound (Lp.memLp f)).coeFn_toLp

theorem norm_boundedFieldL2_sub_le
    (b : α → F →L[ℝ] G) (hb : AEStronglyMeasurable b μ) (M : ℝ)
    (hbound : ∀ᵐ x ∂μ, ‖b x‖ ≤ M) (f g : α →₂[μ] F) :
    ‖boundedFieldL2 b hb M hbound f - boundedFieldL2 b hb M hbound g‖ ≤ M * ‖f - g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (boundedFieldL2 b hb M hbound f) (boundedFieldL2 b hb M hbound g),
    boundedFieldL2_coeFn b hb M hbound f, boundedFieldL2_coeFn b hb M hbound g,
    Lp.coeFn_sub f g, hbound] with x hs hf hg hfg hx
  rw [hs, Pi.sub_apply, hf, hg, hfg, Pi.sub_apply, ← map_sub]
  exact (b x).le_opNorm (f x - g x) |>.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

theorem boundedFieldL2_tendsto
    (b : α → F →L[ℝ] G) (hb : AEStronglyMeasurable b μ) (M : ℝ)
    (hbound : ∀ᵐ x ∂μ, ‖b x‖ ≤ M) {fn : ℕ → α →₂[μ] F} {f : α →₂[μ] F}
    (hfn : Tendsto fn atTop (𝓝 f)) :
    Tendsto (fun n => boundedFieldL2 b hb M hbound (fn n)) atTop (𝓝 (boundedFieldL2 b hb M hbound f)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hh := (tendsto_iff_norm_sub_tendsto_zero.mp hfn).const_mul M
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => norm_boundedFieldL2_sub_le b hb M hbound (fn n) f)
  simpa only [mul_zero] using hh

end CutoffRigidity
