module

public import Mathlib
public import CutoffRigidity.Extra.Rothaus4

/-! # Rothaus remark (stage 5): continuity of `∫ H (g_n + m_n)` along Orlicz-convergent sequences -/

@[expose] public section

open MeasureTheory Filter Topology

namespace CutoffRigidity.Rothaus

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem tendsto_integral_comp [IsFiniteMeasure μ] {H : ℝ → ℝ} (hH : Continuous H) {c K : ℝ}
    (hHb : ∀ a b : ℝ, |a| ≤ K → |H (a + b)| ≤ c * (1 + b ^ 2 + Θ b))
    {g : ℕ → X → ℝ} {h : X → ℝ} {m : ℕ → ℝ} {m₀ : ℝ}
    (hg : ∀ n, MemLp (g n) 2 μ) (hΘg : ∀ n, Integrable (fun x => Θ (g n x)) μ)
    (hh : MemLp h 2 μ) (hΘh : Integrable (fun x => Θ (h x)) μ)
    (hm : Tendsto m atTop (𝓝 m₀)) (hmK : ∀ n, |m n| ≤ K)
    (hL2 : Tendsto (fun n => ∫ x, (g n x - h x) ^ 2 ∂μ) atTop (𝓝 0))
    (hΘ : Tendsto (fun n => ∫ x, |Θ (g n x) - Θ (h x)| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, H (g n x + m n) ∂μ) atTop (𝓝 (∫ x, H (h x + m₀) ∂μ)) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  have hL2' : Tendsto (fun n => ∫ x, (g (ns n) x - h x) ^ 2 ∂μ) atTop (𝓝 0) := hL2.comp hns
  obtain ⟨ms, hms, hae⟩ := (tendstoInMeasure_of_sq (fun n => hg (ns n)) hh hL2').exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  set k : ℕ → ℕ := fun i => ns (ms i) with hk
  have hkt : Tendsto k atTop atTop := hns.comp hms.tendsto_atTop
  have hL2k : Tendsto (fun i => ∫ x, (g (k i) x - h x) ^ 2 ∂μ) atTop (𝓝 0) := hL2.comp hkt
  have hΘk : Tendsto (fun i => ∫ x, |Θ (g (k i) x) - Θ (h x)| ∂μ) atTop (𝓝 0) := hΘ.comp hkt
  have hmk : Tendsto (fun i => m (k i)) atTop (𝓝 m₀) := hm.comp hkt
  have hsq := sq_L1_tendsto (fun i => hg (k i)) hh hL2k
  set B : ℕ → X → ℝ := fun i x => c * (1 + g (k i) x ^ 2 + Θ (g (k i) x)) with hB
  set b : X → ℝ := fun x => c * (1 + h x ^ 2 + Θ (h x)) with hb
  have hBi : ∀ i, Integrable (B i) μ := fun i =>
    (((integrable_const 1).add (hg (k i)).integrable_sq).add (hΘg (k i))).const_mul c
  have hbi : Integrable b μ := (((integrable_const 1).add hh.integrable_sq).add hΘh).const_mul c
  refine tendsto_integral_of_dominated_L1 (B := B) (b := b) (fun i => ?_) hbi hBi
    (fun i => Eventually.of_forall fun x => by
      rw [add_comm]; exact hHb _ _ (hmK _)) ?_ ?_ ?_
  · exact hH.comp_aestronglyMeasurable ((hg (k i)).aestronglyMeasurable.add aestronglyMeasurable_const)
  · filter_upwards [hae] with x hx
    exact (hH.tendsto _).comp (hx.add hmk)
  · filter_upwards [hae] with x hx
    have h1 : Tendsto (fun i => g (k i) x ^ 2) atTop (𝓝 (h x ^ 2)) := hx.pow 2
    have h2 : Tendsto (fun i => Θ (g (k i) x)) atTop (𝓝 (Θ (h x))) := (continuous_Θ.tendsto _).comp hx
    exact (((tendsto_const_nhds.add h1).add h2).const_mul c)
  · have hbound : ∀ i, ∫ x, |B i x - b x| ∂μ ≤ |c| * (∫ x, |g (k i) x ^ 2 - h x ^ 2| ∂μ +
        ∫ x, |Θ (g (k i) x) - Θ (h x)| ∂μ) := by
      intro i
      have hi1 : Integrable (fun x => |g (k i) x ^ 2 - h x ^ 2|) μ :=
        ((hg (k i)).integrable_sq.sub hh.integrable_sq).abs
      have hi2 : Integrable (fun x => |Θ (g (k i) x) - Θ (h x)|) μ := ((hΘg _).sub hΘh).abs
      calc ∫ x, |B i x - b x| ∂μ ≤ ∫ x, |c| * (|g (k i) x ^ 2 - h x ^ 2| + |Θ (g (k i) x) - Θ (h x)|) ∂μ := by
            refine integral_mono ((hBi i).sub hbi).abs ((hi1.add hi2).const_mul _) fun x => ?_
            simp only [hB, hb]
            have : c * (1 + g (k i) x ^ 2 + Θ (g (k i) x)) - c * (1 + h x ^ 2 + Θ (h x)) =
                c * ((g (k i) x ^ 2 - h x ^ 2) + (Θ (g (k i) x) - Θ (h x))) := by ring
            rw [this, abs_mul]
            exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
        _ = _ := by rw [integral_const_mul, integral_add hi1 hi2]
    refine squeeze_zero (fun i => integral_nonneg fun x => abs_nonneg _) hbound ?_
    simpa using (hsq.add hΘk).const_mul |c|

end CutoffRigidity.Rothaus
