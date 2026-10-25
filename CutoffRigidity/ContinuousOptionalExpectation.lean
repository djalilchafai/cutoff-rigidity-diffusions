module

public import Mathlib.Probability.Martingale.OptionalSampling
public import CutoffRigidity.CompactDifferenceQuotients

/-! # Bounded continuous martingales at bounded stopping times

Upper grid approximations are genuine stopping times. Countable-range
optional sampling and dominated convergence then give the expectation at
an arbitrary bounded stopping time, without a continuous-time optional
sampling assumption.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology

/-- Upper rounding on the time grid of mesh 1/(n+1). -/
@[expose] noncomputable def upperTimeGrid (n : ℕ) (t : NNReal) : NNReal :=
  (⌈((n : NNReal) + 1) * t⌉₊ : NNReal) / ((n : NNReal) + 1)

/-- Upper rounding events are genuine past events. -/
theorem upperTimeGrid_le_iff (n : ℕ) (t s : NNReal) :
    upperTimeGrid n t ≤ s ↔ t ≤
      (⌊s * ((n : NNReal) + 1)⌋₊ : NNReal) / ((n : NNReal) + 1) := by
  have hq : (0 : NNReal) < n + 1 := by positivity
  rw [upperTimeGrid, div_le_iff₀ hq, ← Nat.le_floor_iff (by positivity), Nat.ceil_le,
    le_div_iff₀ hq, mul_comm (((n : NNReal) + 1)) t]

/-- The event threshold used in rounding is no later than the queried time. -/
theorem upperTimeGrid_threshold_le (n : ℕ) (s : NNReal) :
    (⌊s * ((n : NNReal) + 1)⌋₊ : NNReal) / ((n : NNReal) + 1) ≤ s := by
  rw [div_le_iff₀ (by positivity : (0 : NNReal) < n + 1)]
  exact Nat.floor_le (by positivity)

/-- Upper grid approximations preserve the stopping-time property. -/
theorem isStoppingTime_upperTimeGrid {Ω : Type*} {m : MeasurableSpace Ω}
    (ℱ : Filtration NNReal m) {τ : Ω → NNReal}
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop NNReal))) (n : ℕ) :
    IsStoppingTime ℱ (fun ω => (upperTimeGrid n (τ ω) : WithTop NNReal)) := by
  intro s
  have he : {ω | (upperTimeGrid n (τ ω) : WithTop NNReal) ≤ s} =
      {ω | (τ ω : WithTop NNReal) ≤
        ((⌊s * ((n : NNReal) + 1)⌋₊ : NNReal) / ((n : NNReal) + 1) : NNReal)} := by
    ext ω
    simp only [WithTop.coe_le_coe]
    exact upperTimeGrid_le_iff n (τ ω) s
  rw [he]
  exact ℱ.mono (upperTimeGrid_threshold_le n s) _ (hτ _)

/-- The actual approximation lies within one grid cell above the time. -/
theorem upperTimeGrid_bounds (n : ℕ) (t : NNReal) :
    t ≤ upperTimeGrid n t ∧ upperTimeGrid n t ≤ t + ((n : NNReal) + 1)⁻¹ := by
  have hq : (0 : NNReal) < n + 1 := by positivity
  constructor
  · rw [upperTimeGrid, le_div_iff₀ hq]
    simpa only [mul_comm] using Nat.le_ceil (((n : NNReal) + 1) * t)
  · rw [upperTimeGrid, div_le_iff₀ hq]
    have hh := (Nat.ceil_lt_add_one (show (0 : NNReal) ≤ ((n : NNReal) + 1) * t by positivity)).le
    have hi : (((n : NNReal) + 1)⁻¹) * ((n : NNReal) + 1) = 1 := inv_mul_cancel₀ (ne_of_gt hq)
    rw [add_mul t, hi]
    simpa only [mul_comm] using hh

/-- The genuine grid approximations converge to the original time. -/
theorem upperTimeGrid_tendsto (t : NNReal) :
    Tendsto (fun n => upperTimeGrid n t) atTop (𝓝 t) := by
  apply NNReal.tendsto_coe.mp
  apply tendsto_const_nhds.squeeze' _
    (Filter.Eventually.of_forall (fun n => show (t : ℝ) ≤ (upperTimeGrid n t : ℝ) from (upperTimeGrid_bounds n t).1))
    (Filter.Eventually.of_forall (fun n => show (upperTimeGrid n t : ℝ) ≤ (t + ((n : NNReal) + 1)⁻¹ : NNReal) from (upperTimeGrid_bounds n t).2))
  have hh := differenceStep_tendsto_zero.const_add (t : ℝ)
  simpa only [differenceStep, add_zero, NNReal.coe_add, NNReal.coe_inv, NNReal.coe_natCast,
    NNReal.coe_one] using hh

/-- A bounded continuous martingale has unchanged expectation at an actual
bounded stopping time. The bound is needed only up to T+1. -/
theorem integral_martingale_at_bounded_stopping_time
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    (ℱ : Filtration NNReal m) {M : NNReal → Ω → ℝ}
    (hM : Martingale M ℱ μ) (hcont : ∀ ω, Continuous (fun t => M t ω))
    (T : NNReal) {τ : Ω → NNReal}
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop NNReal)))
    (hτT : ∀ ω, τ ω ≤ T) (K : ℝ)
    (hbound : ∀ t ≤ T + 1, ∀ ω, ‖M t ω‖ ≤ K) :
    (∫ ω, M (τ ω) ω ∂μ) = ∫ ω, M 0 ω ∂μ := by
  let τn (n : ℕ) (ω : Ω) : WithTop NNReal := upperTimeGrid n (τ ω)
  have hτn (n : ℕ) : IsStoppingTime ℱ (τn n) := isStoppingTime_upperTimeGrid ℱ hτ n
  have htime (n : ℕ) (ω : Ω) : upperTimeGrid n (τ ω) ≤ T + 1 := by
    have hi : (((n : NNReal) + 1)⁻¹) ≤ 1 := by
      apply (inv_le_one₀ (by positivity : (0 : NNReal) < n + 1)).mpr
      simp
    exact (upperTimeGrid_bounds n (τ ω)).2.trans (add_le_add (hτT ω) hi)
  have hτnT (n : ℕ) : ∀ ω, τn n ω ≤ (T + 1 : NNReal) := fun ω => by
    change (upperTimeGrid n (τ ω) : WithTop NNReal) ≤ (T + 1 : NNReal)
    exact WithTop.coe_le_coe.mpr (htime n ω)
  have hrange (n : ℕ) : (Set.range (τn n)).Countable := by
    apply (Set.countable_range (fun k : ℕ => ((k : NNReal) / ((n : NNReal) + 1) : WithTop NNReal))).mono
    rintro _ ⟨ω, rfl⟩
    exact ⟨⌈((n : NNReal) + 1) * τ ω⌉₊, rfl⟩
  have hv (a : NNReal) : (a : WithTop NNReal).untopA = a := by
    rw [WithTop.untopA_eq_untop WithTop.coe_ne_top]
    rfl
  have hprog := hM.stronglyAdapted.isStronglyProgressive_of_continuous hcont
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun ω => M (upperTimeGrid n (τ ω)) ω) μ := by
    have hh := (stronglyMeasurable_stoppedValue_of_le hprog (hτn n) (hτnT n)).mono (ℱ.le (T + 1))
    have hh' : AEStronglyMeasurable (stoppedValue M (τn n)) μ := hh.aestronglyMeasurable
    change AEStronglyMeasurable (fun ω => M ((upperTimeGrid n (τ ω) : WithTop NNReal).untopA) ω) μ at hh'
    simpa only [hv] using hh' 
  have he (n : ℕ) : (∫ ω, M (upperTimeGrid n (τ ω)) ω ∂μ) = ∫ ω, M (T + 1) ω ∂μ := by
    have hh := hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range (hτn n) (hτnT n) (hrange n)
    have hh' := integral_congr_ae hh
    rw [integral_condExp] at hh'
    simpa only [stoppedValue, τn, hv, integral_condExp] using hh'
  have hlim : Tendsto (fun n => ∫ ω, M (upperTimeGrid n (τ ω)) ω ∂μ) atTop
      (𝓝 (∫ ω, M (τ ω) ω ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => K) hmeas (integrable_const K)
    · intro n
      exact Filter.Eventually.of_forall (fun ω => hbound _ (htime n ω) ω)
    · exact Filter.Eventually.of_forall (fun ω => (hcont ω).continuousAt.tendsto.comp (upperTimeGrid_tendsto (τ ω)))
  have hexpect : (∫ ω, M (τ ω) ω ∂μ) = ∫ ω, M (T + 1) ω ∂μ := by
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr (fun n => (he n).symm))
  have hzero := integral_congr_ae (hM.condExp_ae_eq (show (0 : NNReal) ≤ T + 1 by positivity))
  rw [integral_condExp] at hzero
  exact hexpect.trans hzero

end CutoffRigidity
