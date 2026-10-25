module
public import CutoffRigidity.SmoothTestMeasureExt
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Uniformly bounded compact C² approximation under actual finite measures

Actual continuous compact L¹ density, scalar clipping, and actual smooth
uniform approximation yield compact C² tests with a common bound.
-/
public section
namespace CutoffRigidity
open MeasureTheory Set Filter Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem clamp_error_le {a b M : ℝ} (hM : 0 ≤ M) (hb : |b| ≤ M) :
    |max (-M) (min M a) - b| ≤ |a - b| := by
  have hlo : -M ≤ b := (abs_le.mp hb).1
  have hhi : b ≤ M := (abs_le.mp hb).2
  by_cases ha : a ≤ -M
  · rw [min_eq_right (ha.trans (by linarith)), max_eq_left ha,
      abs_of_nonpos (by linarith : -M - b ≤ 0), abs_of_nonpos (by linarith : a - b ≤ 0)]
    linarith
  · by_cases ha' : M ≤ a
    · rw [min_eq_left ha', max_eq_right (by linarith), abs_of_nonneg (by linarith : M - b ≥ 0),
        abs_of_nonneg (by linarith : a - b ≥ 0)]
      linarith
    · rw [min_eq_right (le_of_not_ge ha'), max_eq_right (le_of_not_ge ha)]

/-- Actual compact C² approximants preserve one common bound and converge
in L¹ under an arbitrary actual finite Euclidean Borel measure. -/
theorem exists_bounded_compact_c2_L1_approx
    (τ : Measure E) [IsFiniteMeasure τ] {φ : E → ℝ} (hφ : Measurable φ)
    (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ x, ‖φ x‖ ≤ M) :
    ∃ ψ : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ 2 (ψ n)) ∧ (∀ n, HasCompactSupport (ψ n)) ∧
      (∀ n x, ‖ψ n x‖ ≤ M + 1) ∧
      Tendsto (fun n => ∫ x, ‖φ x - ψ n x‖ ∂τ) atTop (𝓝 0) := by
  have hφI : Integrable φ τ := (integrable_const M).mono' hφ.aestronglyMeasurable (Eventually.of_forall hBound)
  choose a hac hae haC haI using (fun n => hφI.exists_hasCompactSupport_integral_sub_le (differenceStep_pos n))
  let b := fun n x => max (-M) (min M (a n x))
  have hbC (n : ℕ) : Continuous (b n) := continuous_const.max (continuous_const.min (haC n))
  have hb0 : max (-M) (min M 0) = 0 := by rw [min_eq_right hM, max_eq_right (by linarith)]
  have hbc (n : ℕ) : HasCompactSupport (b n) := (hac n).comp_left (g := fun s : ℝ => max (-M) (min M s)) hb0
  have hbB (n : ℕ) (x : E) : ‖b n x‖ ≤ M := by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hbI (n : ℕ) : Integrable (b n) τ := (integrable_const M).mono' (hbC n).aestronglyMeasurable
    (Eventually.of_forall (hbB n))
  have hbErr (n : ℕ) : (∫ x, ‖φ x - b n x‖ ∂τ) ≤ differenceStep n := by
    apply le_trans (integral_mono (hφI.sub (hbI n)).norm (hφI.sub (haI n)).norm (fun x => ?_)) (hae n)
    simpa only [Real.norm_eq_abs, abs_sub_comm, Pi.sub_apply, b] using clamp_error_le (a := a n x) hM (hBound x)
  choose ψ hψ hψc hψclose using (fun n => exists_compact_c2_uniform_approx (hbC n) (hbc n) (differenceStep_pos n))
  have hψB (n : ℕ) (x : E) : ‖ψ n x‖ ≤ M + 1 := by
    have hh : ‖ψ n x - b n x‖ ≤ differenceStep n := by
      simpa only [dist_eq_norm, norm_sub_rev] using (hψclose n x).le
    have hn := norm_add_le (ψ n x - b n x) (b n x)
    rw [sub_add_cancel] at hn
    linarith [hbB n x, differenceStep_le_one n]
  have hψI (n : ℕ) : Integrable (ψ n) τ := (integrable_const (M + 1)).mono' (hψ n).continuous.aestronglyMeasurable
    (Eventually.of_forall (hψB n))
  have hErr (n : ℕ) : (∫ x, ‖φ x - ψ n x‖ ∂τ) ≤
      differenceStep n + τ.real Set.univ * differenceStep n := by
    have hpoint (x : E) : ‖φ x - ψ n x‖ ≤ ‖φ x - b n x‖ + differenceStep n := by
      have ht := norm_add_le (φ x - b n x) (b n x - ψ n x)
      have heq : φ x - b n x + (b n x - ψ n x) = φ x - ψ n x := by ring
      rw [heq] at ht
      have hc : ‖b n x - ψ n x‖ ≤ differenceStep n := by simpa only [dist_eq_norm, norm_sub_rev] using (hψclose n x).le
      linarith
    have hh := integral_mono (hφI.sub (hψI n)).norm (((hφI.sub (hbI n)).norm).add (integrable_const (differenceStep n))) hpoint
    have ha := integral_add (hφI.sub (hbI n)).norm (integrable_const (differenceStep n))
    simp only [Pi.add_apply, Pi.sub_apply] at ha hh
    rw [ha, integral_const] at hh
    simpa only [smul_eq_mul] using hh.trans (add_le_add (hbErr n) le_rfl)
  refine ⟨ψ, hψ, hψc, hψB, ?_⟩
  have hlim := differenceStep_tendsto_zero.add (differenceStep_tendsto_zero.const_mul (τ.real Set.univ))
  simp only [mul_zero, add_zero] at hlim
  exact squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _)) hErr hlim

end CutoffRigidity
