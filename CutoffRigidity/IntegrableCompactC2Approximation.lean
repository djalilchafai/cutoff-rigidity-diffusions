module
public import CutoffRigidity.CompactC2MeasureApproximation

/-! # Genuine compact C² L¹ approximation of arbitrary integrable inputs -/
public section
namespace CutoffRigidity
open MeasureTheory Filter
open scoped Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_compact_c2_L1_approx_of_integrable
    (μ : Measure E) [IsProbabilityMeasure μ] {f : E → ℝ} (hf : Integrable f μ) :
    ∃ g : ℕ → E → ℝ, (∀ n, ContDiff ℝ 2 (g n)) ∧ (∀ n, HasCompactSupport (g n)) ∧
      Tendsto (fun n => ∫ x, ‖f x - g n x‖ ∂μ) atTop (𝓝 0) := by
  choose a hac hae haC haI using (fun n => hf.exists_hasCompactSupport_integral_sub_le (differenceStep_pos n))
  choose g hg hgc hclose using (fun n => exists_compact_c2_uniform_approx (haC n) (hac n) (differenceStep_pos n))
  have hgI (n : ℕ) : Integrable (g n) μ := (hg n).continuous.integrable_of_hasCompactSupport (hgc n)
  have hb (n : ℕ) : (∫ x, ‖f x - g n x‖ ∂μ) ≤ 2 * differenceStep n := by
    have hp (x : E) : ‖f x - g n x‖ ≤ ‖f x - a n x‖ + differenceStep n := by
      have ht := norm_sub_le_norm_sub_add_norm_sub (f x) (a n x) (g n x)
      have hh : ‖a n x - g n x‖ ≤ differenceStep n := by
        simpa only [dist_eq_norm, norm_sub_rev] using (hclose n x).le
      linarith
    have hh := integral_mono (hf.sub (hgI n)).norm
      ((hf.sub (haI n)).norm.add (integrable_const (differenceStep n))) hp
    have he := integral_add (hf.sub (haI n)).norm (integrable_const (differenceStep n))
    simp only [Pi.add_apply, Pi.sub_apply] at he hh
    rw [he, integral_const] at hh
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hh
    linarith [hae n]
  refine ⟨g,hg,hgc,?_⟩
  exact squeeze_zero (fun n => integral_nonneg fun x => norm_nonneg _) hb
    (by simpa using differenceStep_tendsto_zero.const_mul 2)

end CutoffRigidity
