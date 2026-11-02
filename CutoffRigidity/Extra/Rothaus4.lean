module

public import Mathlib
public import CutoffRigidity.Extra.Rothaus3

/-! # Rothaus remark (stage 4): `L²`-convergence consequences

`L²` convergence in the form `∫ (g_n - g)² → 0` gives convergence in measure, convergence of the squares in `L¹`,
and (with `L¹`-convergence of `Θ g_n`) convergence of integrals `∫ H (g_n + m_n)` for `H` of at most
`Θ`-growth (Vitali-type, via the generalised dominated convergence theorem).
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace CutoffRigidity.Rothaus

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem tendstoInMeasure_of_sq [IsFiniteMeasure μ] {g : ℕ → X → ℝ} {h : X → ℝ}
    (hg : ∀ n, MemLp (g n) 2 μ) (hh : MemLp h 2 μ)
    (hc : Tendsto (fun n => ∫ x, (g n x - h x) ^ 2 ∂μ) atTop (𝓝 0)) :
    TendstoInMeasure μ g atTop h := by
  refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) ?_
  have : ∀ n, eLpNorm (g n - h) 2 μ = ENNReal.ofReal ((∫ x, (g n x - h x) ^ 2 ∂μ) ^ (1 / 2 : ℝ)) := by
    intro n
    rw [(hg n |>.sub hh).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp [sq_abs]
  simp_rw [this]
  have h2 : Tendsto (fun n => (∫ x, (g n x - h x) ^ 2 ∂μ) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 (1 / 2 : ℝ) (Or.inr (by norm_num))).tendsto.comp hc
    simp only [Function.comp_def] at this
    rwa [Real.zero_rpow (by norm_num)] at this
  simpa using ENNReal.tendsto_ofReal h2

theorem sq_L1_tendsto {g : ℕ → X → ℝ} {h : X → ℝ} (hg : ∀ n, MemLp (g n) 2 μ) (hh : MemLp h 2 μ)
    (hc : Tendsto (fun n => ∫ x, (g n x - h x) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, |g n x ^ 2 - h x ^ 2| ∂μ) atTop (𝓝 0) := by
  set G := ∫ x, h x ^ 2 ∂μ with hG
  have hG0 : 0 ≤ G := integral_nonneg fun x => sq_nonneg _
  have hd : ∀ n, Integrable (fun x => (g n x - h x) ^ 2) μ := fun n => ((hg n).sub hh).integrable_sq
  have hbound : ∀ ε : ℝ, 0 < ε → ∀ n, ∫ x, |g n x ^ 2 - h x ^ 2| ∂μ ≤
      (1 + 1 / ε) * ∫ x, (g n x - h x) ^ 2 ∂μ + ε * G := by
    intro ε hε n
    have hpt : ∀ x, |g n x ^ 2 - h x ^ 2| ≤ (1 + 1 / ε) * (g n x - h x) ^ 2 + ε * h x ^ 2 := by
      intro x
      set d := g n x - h x with hdd
      have : g n x = h x + d := by simp [hdd]
      rw [this]
      have h1 : |(h x + d) ^ 2 - h x ^ 2| ≤ d ^ 2 + 2 * |h x| * |d| := by
        have : (h x + d) ^ 2 - h x ^ 2 = d ^ 2 + 2 * h x * d := by ring
        rw [this]
        calc |d ^ 2 + 2 * h x * d| ≤ |d ^ 2| + |2 * h x * d| := abs_add_le _ _
          _ = d ^ 2 + 2 * |h x| * |d| := by rw [abs_of_nonneg (sq_nonneg d), abs_mul, abs_mul]; norm_num
      have h2 : 2 * |h x| * |d| ≤ ε * h x ^ 2 + d ^ 2 / ε := by
        have h0 : 0 ≤ (ε * |h x| - |d|) ^ 2 / ε := div_nonneg (sq_nonneg _) hε.le
        have e : (ε * |h x| - |d|) ^ 2 / ε = ε * h x ^ 2 - 2 * |h x| * |d| + d ^ 2 / ε := by
          rw [sub_sq, mul_pow, sq_abs, sq_abs]; field_simp
        linarith
      have : d ^ 2 / ε = 1 / ε * d ^ 2 := by ring
      nlinarith
    calc ∫ x, |g n x ^ 2 - h x ^ 2| ∂μ ≤ ∫ x, ((1 + 1 / ε) * (g n x - h x) ^ 2 + ε * h x ^ 2) ∂μ :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
            (((hd n).const_mul _).add (hh.integrable_sq.const_mul _)) (Eventually.of_forall hpt)
      _ = _ := by
          rw [integral_add ((hd n).const_mul _) (hh.integrable_sq.const_mul _), integral_const_mul,
            integral_const_mul]
  rw [Metric.tendsto_atTop]
  intro η hη
  set ε := η / (2 * (G + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have hεG : ε * G < η / 2 := by
    rw [hε, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hc' := (Metric.tendsto_atTop.1 hc) (η / (2 * (1 + 1 / ε))) (by positivity)
  obtain ⟨N, hN⟩ := hc'
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  rw [Real.dist_eq, sub_zero] at h1 ⊢
  have hD : 0 ≤ ∫ x, (g n x - h x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  rw [abs_of_nonneg hD, lt_div_iff₀ (by positivity)] at h1
  have hI : 0 ≤ ∫ x, |g n x ^ 2 - h x ^ 2| ∂μ := integral_nonneg fun x => abs_nonneg _
  rw [abs_of_nonneg hI]
  have := hbound ε hεpos n
  nlinarith

end CutoffRigidity.Rothaus
