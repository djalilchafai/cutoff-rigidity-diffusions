module

public import CutoffRigidity.CompactDifferenceQuotients
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-! # Finite Euclidean measures are determined by actual compact C² tests

Uniform smooth approximation followed by a compact bump supplies actual
compact smooth tests approximating each continuous compact test. Dominated
convergence and the measure representation theorem then give equality.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory Filter Topology
open scoped ContDiff

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Genuine compact smooth uniform approximation, with no approximation premise. -/
theorem exists_compact_c2_uniform_approx {f : E → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ x, dist (g x) (f x) < ε := by
  have hfu : UniformContinuous f := hf.uniformContinuous_of_tendsto_cocompact hfc.is_zero_at_infty
  obtain ⟨g,hg,hclose⟩ := hfu.exists_contDiff_dist_le hε
  obtain ⟨R,hR,hKR⟩ := hfc.isBounded.subset_ball_lt 0 (0 : E)
  let φ : ContDiffBump (0 : E) := ⟨R,2*R,hR,by linarith⟩
  refine ⟨fun x => φ x * g x, (show ContDiff ℝ 2 (φ : E → ℝ) from φ.contDiff).mul (hg.of_le (by simp)), ?_, ?_⟩
  · simpa only [Pi.mul_def] using φ.hasCompactSupport.mul_right (f' := g)
  · intro x
    have hφf : φ x * f x = f x := by
      by_cases hx : f x = 0
      · simp [hx]
      · have hxs : x ∈ tsupport f := subset_tsupport f hx
        rw [φ.one_of_mem_closedBall (Metric.ball_subset_closedBall (hKR hxs)), one_mul]
    have he : φ x * g x - f x = φ x * (g x - f x) := by nlinarith [hφf]
    have hh : |g x - f x| < ε := by simpa only [dist_eq_norm, Real.norm_eq_abs] using hclose x
    rw [dist_eq_norm, Real.norm_eq_abs, he, abs_mul, abs_of_nonneg φ.nonneg]
    exact (mul_le_mul_of_nonneg_right φ.le_one (abs_nonneg _)).trans_lt (by simpa using hh)

/-- Equality of genuine compact C² test integrals determines finite measures. -/
theorem measure_eq_of_compact_c2_integrals {μ ν : Measure E}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (heq : ∀ f : E → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
      (∫ x, f x ∂μ) = ∫ x, f x ∂ν) : μ = ν := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  choose g hg hgc hclose using (fun n : ℕ => exists_compact_c2_uniform_approx
    f.continuous f.hasCompactSupport (differenceStep_pos n))
  have hpoint (x : E) : Tendsto (fun n => g n x) atTop (𝓝 (f x)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _)
      (fun n => by convert! (hclose n x).le using 1) differenceStep_tendsto_zero
  have hbound (n : ℕ) (x : E) : ‖g n x‖ ≤ |f x| + 1 := by
    have hc : ‖g n x - f x‖ ≤ 1 := by
      have hh := (hclose n x).le.trans (differenceStep_le_one n)
      convert! hh using 1
    have ht := norm_add_le (g n x - f x) (f x)
    rw [sub_add_cancel] at ht
    calc
      _ ≤ ‖g n x - f x‖ + ‖f x‖ := ht
      _ ≤ 1 + ‖f x‖ := by gcongr
      _ = _ := by rw [Real.norm_eq_abs]; ring
  have hlim (m : Measure E) (hm : IsFiniteMeasure m) :
      Tendsto (fun n => ∫ x, g n x ∂m) atTop (𝓝 (∫ x, f x ∂m)) := by
    have := hm
    apply tendsto_integral_of_dominated_convergence (fun x => |f x| + 1)
    · intro n
      exact (hg n).continuous.aestronglyMeasurable
    · exact (f.integrable (μ := m)).abs.add (integrable_const 1)
    · intro n
      exact Filter.Eventually.of_forall (hbound n)
    · exact Filter.Eventually.of_forall hpoint
  exact tendsto_nhds_unique (hlim μ inferInstance)
    ((hlim ν inferInstance).congr (fun n => (heq (g n) (hg n) (hgc n)).symm))

end CutoffRigidity
