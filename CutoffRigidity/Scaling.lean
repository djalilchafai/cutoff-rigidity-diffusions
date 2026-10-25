module

public import CutoffRigidity.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

public section

open Filter
open scoped Topology

namespace CutoffRigidity

/-- Scaling a generator by `a` divides its critical time by `a`. -/
theorem criticalTime_scale (d rate a : ℝ) :
    criticalTime d (a * rate) = criticalTime d rate / a := by
  unfold criticalTime
  by_cases ha : a = 0
  · simp [ha]
  by_cases hr : rate = 0
  · simp [hr]
  field_simp

/-- The product condition has no control over the time scale without an upper
bound on curvature. This elementary identity isolates the missing inference. -/
theorem curvature_time_product (d : ℝ) (hd : d ≠ 0) :
    d * (Real.log d / d) = Real.log d := by
  field_simp

/-- The curvature-rate sequence is bounded below. -/
theorem dimension_eventually_ge_one :
    ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ (n : ℝ) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact_mod_cast hn

/-- A mixing-time scale can tend to zero while curvature times that scale diverges. -/
theorem shrinking_time :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop

/-- The growing-curvature product condition holds for the shrinking time scale. -/
theorem diverging_curvature_time_product :
    Tendsto (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ) / (n : ℝ)))
      atTop atTop := by
  apply (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  change Real.log (n : ℝ) = _
  symm
  exact curvature_time_product _ (by exact_mod_cast (show n ≠ 0 by omega))

/-- Formal counterexample to the numerical inference in the proof of Theorem 1.7.
This refutes that inference; it does not by itself construct a stochastic process. -/
theorem product_condition_does_not_force_time_divergence :
    ∃ (κ τ : ℕ → ℝ),
      (∀ᶠ n in atTop, 1 ≤ κ n) ∧
      (∀ᶠ n in atTop, 0 < τ n) ∧
      Tendsto (fun n => κ n * τ n) atTop atTop ∧
      Tendsto τ atTop (𝓝 0) ∧
      ¬ Tendsto τ atTop atTop := by
  refine ⟨fun n => (n : ℝ), fun n => Real.log (n : ℝ) / (n : ℝ),
    dimension_eventually_ge_one, ?_, diverging_curvature_time_product, shrinking_time, ?_⟩
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have h : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    exact div_pos (Real.log_pos h) (by linarith)
  · intro h
    exact not_tendsto_nhds_of_tendsto_atTop h 0 shrinking_time

/-- An explicit curvature upper bound repairs the numerical inference.
This is a scalar lemma, not the diffusion conclusion of Theorem 1.7. -/
theorem time_diverges_of_bounded_curvature {κ τ : ℕ → ℝ} {K : ℝ}
    (hK : 0 < K)
    (hbound : ∀ᶠ n in atTop, κ n ≤ K)
    (hnonneg : ∀ᶠ n in atTop, 0 ≤ τ n)
    (hproduct : Tendsto (fun n => κ n * τ n) atTop atTop) :
    Tendsto τ atTop atTop := by
  have h := hproduct.atTop_div_const hK
  apply tendsto_atTop_mono' _ ?_ h
  filter_upwards [hbound, hnonneg] with n hκ hτ
  exact (div_le_iff₀ hK).2 (by nlinarith)

end CutoffRigidity
