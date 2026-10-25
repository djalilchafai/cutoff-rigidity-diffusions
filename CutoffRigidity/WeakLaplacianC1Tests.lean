module

public import CutoffRigidity.CompactC1Mollification

/-! # Genuine compact C¹ tests for a locally L² weak Laplacian

Actual compact smooth mollifications converge strongly in H¹, with one
common compact support. Local L² of the genuine right-hand side therefore
extends the distributional equation to compact C¹ tests.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology
open scoped Pointwise

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem continuous_memLp_two_restrict_compact {F : Type*} [NormedAddCommGroup F]
    {g : E → F} (hg : Continuous g) {K : Set E} (hK : IsCompact K) :
    MemLp g 2 ((volume : Measure E).restrict K) := by
  have : IsFiniteMeasure ((volume : Measure E).restrict K) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (hK.measure_lt_top (μ := (volume : Measure E)))⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  apply MemLp.of_bound hg.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact hC x hx

theorem gradient_eq_zero_off_closed_support {g : E → ℝ} {K : Set E}
    (hK : IsClosed K) (hg : ∀ x ∉ K, g x = 0) {x : E} (hx : x ∉ K) : gradient g x = 0 := by
  have hsub : tsupport g ⊆ K := closure_minimal (fun y hy => by
    by_contra h
    exact hy (hg y h)) hK
  have hn : x ∉ tsupport g := fun h => hx (hsub h)
  simp only [gradient, fderiv_of_notMem_tsupport ℝ hn, map_zero]

theorem euclidean_inner_toLp {g h : E → E} (hg : MemLp g 2 volume) (hh : MemLp h 2 volume) :
    inner ℝ (hg.toLp g) (hh.toLp h) = ∫ x, inner ℝ (g x) (h x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp, hh.coeFn_toLp] with x hx hy
  rw [hx, hy]

theorem integral_indicator_mul_of_right_support {K : Set E} {a b : E → ℝ}
    (hb : ∀ x ∉ K, b x = 0) : (∫ x, K.indicator a x * b x) = ∫ x, a x * b x := by
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ K
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, hb x hx]
    simp

theorem integral_indicator_inner_of_right_support {K : Set E} {a b : E → E}
    (hb : ∀ x ∉ K, b x = 0) :
    (∫ x, inner ℝ (K.indicator a x) (b x)) = ∫ x, inner ℝ (a x) (b x) := by
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ K
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, hb x hx]
    simp

set_option maxHeartbeats 800000 in
/-- The actual weak Laplacian equation admits compact C¹ tests. Global
boundedness of f or its gradient is unnecessary for this local result. -/
theorem weak_laplacian_compact_c1_test {f F η : E → ℝ}
    (hf : ContDiff ℝ 1 f)
    (hFloc : ∀ K : Set E, IsCompact K → MemLp F 2 ((volume : Measure E).restrict K))
    (hLap : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      (∫ x, f x * euclideanLaplacian ψ x) = ∫ x, F x * ψ x)
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    (∫ x, inner ℝ (gradient f x) (gradient η x)) = -(∫ x, F x * η x) := by
  let K := Metric.closedBall (0 : E) 1 + tsupport η
  have hK : IsCompact K := (isCompact_closedBall _ _).add hηc
  have hηOff : ∀ x ∉ K, η x = 0 := fun x hx => eq_zero_off_unit_support_enlargement x hx
  have hGηOff : ∀ x ∉ K, gradient η x = 0 :=
    fun x hx => gradient_eq_zero_off_closed_support hK.isClosed hηOff hx
  let FK := K.indicator F
  let G := K.indicator (gradient f)
  have hFK : MemLp FK 2 volume := (memLp_indicator_iff_restrict hK.measurableSet).mpr (hFloc K hK)
  have hG : MemLp G 2 volume := (memLp_indicator_iff_restrict hK.measurableSet).mpr
    (continuous_memLp_two_restrict_compact (continuous_gradient_of_c1 hf) hK)
  have hηLp : MemLp η 2 volume := hη.continuous.memLp_of_hasCompactSupport hηc
  have hGηLp := c1_compact_gradient_memLp hη hηc
  let φ (n : ℕ) : ContDiffBump (0 : E) := euclideanMollifierBump (differenceStep n) (differenceStep_pos n)
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := differenceStep_tendsto_zero
  let ψ (n : ℕ) := bumpMollification (φ n) η
  have hψ (n : ℕ) : ContDiff ℝ 3 (ψ n) :=
    (bumpMollification_contDiff (φ n) hη.continuous.locallyIntegrable).of_le (by norm_num)
  have hψc (n : ℕ) : HasCompactSupport (ψ n) := bumpMollification_hasCompactSupport (φ n) hηc
  have hψOff (n : ℕ) : ∀ x ∉ K, ψ n x = 0 :=
    fun x hx => bumpMollification_eq_zero_off_unit_enlargement (φ n) (differenceStep_le_one n) x hx
  have hGψOff (n : ℕ) : ∀ x ∉ K, gradient (ψ n) x = 0 :=
    fun x hx => gradient_eq_zero_off_closed_support hK.isClosed (hψOff n) hx
  have hψLp (n : ℕ) : MemLp (ψ n) 2 volume :=
    (bumpMollification_L2_contraction (φ n) hη.continuous.measurable hηLp).1
  have hGψLp (n : ℕ) : MemLp (gradient (ψ n)) 2 volume :=
    mollifiedGradient_memLp (φ n) hη.continuous.locallyIntegrable hηc
  have hψLim : Tendsto (fun n => (hψLp n).toLp (ψ n)) atTop (𝓝 (hηLp.toLp η)) :=
    bumpMollificationLp_tendsto φ hφ η hη.continuous.measurable hηLp
  have hGψLim : Tendsto (fun n => (hGψLp n).toLp (gradient (ψ n))) atTop
      (𝓝 (hGηLp.toLp (gradient η))) :=
    mollifiedGradientLp_tendsto_of_compact_c1 hη hηc φ hφ
  have heq (n : ℕ) : inner ℝ (hG.toLp G) ((hGψLp n).toLp (gradient (ψ n))) =
      -inner ℝ (hFK.toLp FK) ((hψLp n).toLp (ψ n)) := by
    rw [euclidean_inner_toLp, real_inner_toLp,
      integral_indicator_inner_of_right_support (hGψOff n),
      integral_indicator_mul_of_right_support (hψOff n)]
    have hi := c1_integral_mul_laplacian_compact_test hf ((hψ n).of_le (by norm_num)) (hψc n)
    rw [hLap (ψ n) ((hψ n).of_le (by norm_num)) (hψc n)] at hi
    linarith
  have hl : Tendsto (fun n => inner ℝ (hG.toLp G) ((hGψLp n).toLp (gradient (ψ n))))
      atTop (𝓝 (inner ℝ (hG.toLp G) (hGηLp.toLp (gradient η)))) :=
    tendsto_const_nhds.inner hGψLim
  have hr : Tendsto (fun n => -inner ℝ (hFK.toLp FK) ((hψLp n).toLp (ψ n)))
      atTop (𝓝 (-inner ℝ (hFK.toLp FK) (hηLp.toLp η))) :=
    (tendsto_const_nhds.inner hψLim).neg
  have he := tendsto_nhds_unique hl (hr.congr' (Filter.Eventually.of_forall (fun n => (heq n).symm)))
  rw [euclidean_inner_toLp, real_inner_toLp,
    integral_indicator_inner_of_right_support hGηOff,
    integral_indicator_mul_of_right_support hηOff] at he
  exact he

/-- Local L² of the actual right-hand side gives genuine integrability
against every compact continuous test. -/
theorem locallyL2_mul_compact_continuous_integrable {F η : E → ℝ}
    (hFloc : ∀ K : Set E, IsCompact K → MemLp F 2 ((volume : Measure E).restrict K))
    (hη : Continuous η) (hηc : HasCompactSupport η) : Integrable (fun x => F x * η x) volume := by
  have hFK : MemLp ((tsupport η).indicator F) 2 volume :=
    (memLp_indicator_iff_restrict (isClosed_tsupport η).measurableSet).mpr (hFloc _ hηc)
  have hηLp : MemLp η 2 volume := hη.memLp_of_hasCompactSupport hηc
  have he : (fun x => (tsupport η).indicator F x * η x) =ᵐ[volume] fun x => F x * η x := by
    filter_upwards with x
    by_cases hx : x ∈ tsupport η
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]
      simp
  exact (hFK.integrable_mul hηLp).congr he

end CutoffRigidity
