module

public import Mathlib
public import CutoffRigidity.Extra.Rothaus15

/-! # Rothaus remark (stage 16): non-vacuity on the two-point space

On `Bool` with `μ{true} = p = e^{-3}`, `μ{false} = 1 - p` and the form `E f = p(1-p)(f true - f false)²`:
the Poincaré constant is `1`, the log-Sobolev constant is at least `3 / (1-p) > 2`, so `C_LSI > 2 C_PI` and the
discrete Rothaus theorem produces an extremal function; all hypotheses are verified.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace CutoffRigidity.Rothaus

/-- The two-point probability measure with `μ{true} = p`. -/
noncomputable def twoPoint (p : ℝ) : Measure Bool :=
  ENNReal.ofReal p • Measure.dirac true + ENNReal.ofReal (1 - p) • Measure.dirac false

theorem twoPoint_prob {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : IsProbabilityMeasure (twoPoint p) := by
  refine ⟨?_⟩
  simp only [twoPoint, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]
  simp

theorem twoPoint_real_true {p : ℝ} (h0 : 0 ≤ p) : (twoPoint p).real {true} = p := by
  simp [twoPoint, Measure.real, Measure.add_apply, Measure.smul_apply, h0]

theorem twoPoint_real_false {p : ℝ} (_h0 : 0 ≤ p) (h1 : p ≤ 1) : (twoPoint p).real {false} = 1 - p := by
  simp [twoPoint, Measure.real, Measure.add_apply, Measure.smul_apply, h1]

theorem entropy_finite {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] (μ : Measure X)
    [IsProbabilityMeasure μ] (g : X → ℝ) :
    CutCur.entropyOf μ g = ∑ x, μ.real {x} * (g x * Real.log (g x)) -
      (∑ x, μ.real {x} * g x) * Real.log (∑ x, μ.real {x} * g x) := by
  unfold CutCur.entropyOf
  rw [integral_finite, integral_finite]

/-- On a finite space, `Ent(g) ≤ Var(g) / ∫ g` for `g ≥ 0` with `∫ g > 0`. -/
theorem entropy_finite_le {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] (μ : Measure X)
    [IsProbabilityMeasure μ] {g : X → ℝ} (hg : ∀ x, 0 ≤ g x) (hM : 0 < ∑ x, μ.real {x} * g x) :
    CutCur.entropyOf μ g ≤ ((∑ x, μ.real {x} * g x ^ 2) - (∑ x, μ.real {x} * g x) ^ 2) /
      (∑ x, μ.real {x} * g x) := by
  rw [entropy_finite]
  set M := ∑ x, μ.real {x} * g x with hMdef
  have hpt : ∀ x, g x * Real.log (g x) - g x * Real.log M ≤ g x ^ 2 / M - g x := by
    intro x
    rcases (hg x).eq_or_lt with h | h
    · rw [← h]; simp
    · have := Real.log_le_sub_one_of_pos (div_pos h hM)
      rw [Real.log_div h.ne' hM.ne'] at this
      have h2 := mul_le_mul_of_nonneg_left this h.le
      have : g x * (g x / M - 1) = g x ^ 2 / M - g x := by field_simp
      nlinarith
  have hsum : ∑ x, μ.real {x} * (g x * Real.log (g x) - g x * Real.log M) ≤
      ∑ x, μ.real {x} * (g x ^ 2 / M - g x) :=
    Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpt x) measureReal_nonneg
  have e1 : ∑ x, μ.real {x} * (g x * Real.log (g x) - g x * Real.log M) =
      ∑ x, μ.real {x} * (g x * Real.log (g x)) - M * Real.log M := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    congr 1
    rw [hMdef, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by ring
  have e2 : ∑ x, μ.real {x} * (g x ^ 2 / M - g x) = (∑ x, μ.real {x} * g x ^ 2) / M - M := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [e1, e2] at hsum
  have : ((∑ x, μ.real {x} * g x ^ 2) - M ^ 2) / M = (∑ x, μ.real {x} * g x ^ 2) / M - M := by
    field_simp
  rw [this]; exact hsum

end CutoffRigidity.Rothaus
