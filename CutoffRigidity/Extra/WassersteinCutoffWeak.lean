module

public import CutoffRigidity.Paper.WassersteinCutoff

/-! # Remark 3.4 (weaker assumption in Corollary 1.3)

The assumption `liminf λ₁ > 0` is replaced by `(λ₁⁽ⁿ⁾)⁻¹ ≤ (log n)^α` eventually.
-/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

/-- After the critical time, with slowly growing inverse gap. -/
theorem barycenter_wasserstein_after_cutoff_weak {Ω : Type*} [MeasurableSpace Ω]
    (D : ∀ n : ℕ, SpectralInformationLowerData Ω n) {c ε α : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε)
    (hgap : ∀ᶠ n : ℕ in atTop, ((D n).rate)⁻¹ ≤ (Real.log n) ^ α) :
    Tendsto (fun n : ℕ => barycenterBallWasserstein (D n) c
      ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) := by
  have hsq : Tendsto (fun n : ℕ => barycenterBallSquaredWasserstein (D n) c
      ((1 + ε) * criticalTime n (D n).rate)) atTop (𝓝 0) := by
    have hlit : Tendsto (fun n : ℕ => (Real.log n) ^ α * (n : ℝ) ^ (-ε)) atTop (𝓝 0) := by
      have h := ((isLittleO_log_rpow_rpow_atTop α hε).tendsto_div_nhds_zero).comp
        tendsto_natCast_atTop_atTop
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      simp [Function.comp, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
    have hbound : Tendsto (fun n : ℕ => c ^ 2 * (n : ℝ) ^ (-ε) +
        (Real.log n) ^ α * (n : ℝ) ^ (-ε)) atTop (𝓝 0) := by
      simpa using ((power_after_cutoff hε).const_mul (c ^ 2)).add hlit
    refine squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) ?_ hbound
    filter_upwards [hgap, eventually_ge_atTop 1] with n hn hn1
    have hpos := (D n).rate_pos
    have ht : 0 ≤ (1 + ε) * criticalTime n (D n).rate := by
      apply mul_nonneg (by linarith)
      unfold criticalTime
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast hn1)) (by positivity)
    refine ((barycenterBallSquaredWasserstein_bounds (D n) (by omega) hc ht).2).trans ?_
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [mul_comm (c ^ 2 + _), dimension_decay_at_criticalTime n (D n).rate (1 + ε) hnpos hpos.ne']
    have : (n : ℝ) ^ (1 - (1 + ε)) = (n : ℝ) ^ (-ε) := by congr 1; ring
    rw [this]
    nlinarith [Real.rpow_nonneg hnpos.le (-ε)]
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have hh := h.congr' (show (fun n : ℕ => Real.sqrt (barycenterBallSquaredWasserstein (D n) c
      ((1 + ε) * criticalTime n (D n).rate))) =ᶠ[atTop]
      (fun n => barycenterBallWasserstein (D n) c ((1 + ε) * criticalTime n (D n).rate)) from by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (barycenterBallWasserstein_eq_sqrt (D n) (by omega) hc _).symm)
  simpa only [Real.sqrt_zero] using hh

/-- **Remark 3.4** (weaker assumption in Corollary 1.3): the hypothesis `liminf λ₁ > 0`
is replaced by `(λ₁⁽ⁿ⁾)⁻¹ ≤ (log n)^α` eventually, for some `α > 0`. -/
theorem wasserstein_cutoff_weak {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {V : ∀ n, CutCur.Rd n → ℝ}
    {B : ∀ n, ℝ≥0 → Ω n → CutCur.Rd n} {P : ∀ n, Measure (Ω n)}
    {X : ∀ n, CutCur.Rd n → ℝ≥0 → Ω n → CutCur.Rd n}
    (hL : ∀ n, 0 < n → CutCur.IsLangevin (V n) (B n) (P n) (X n) ∧ CutCur.RigidCurvature (V n))
    (hgap : ∃ α : ℝ, 0 < α ∧
      ∀ᶠ n : ℕ in atTop, (CutCur.spectralGap (V n))⁻¹ ≤ (Real.log n) ^ α)
    {c : ℝ} (hc : 0 < c) :
    CutCur.HasCutoff (fun n => CutCur.worst (P n) (X n) (CutCur.meanBall (V n) c)
      (CutCur.wasserstein2 · (CutCur.gibbs (V n))))
      (fun n => CutCur.criticalTime n (CutCur.spectralGap (V n))) ⊤ 0 := by
  obtain ⟨α, -, hα⟩ := hgap
  obtain ⟨Ω', _, D, hD⟩ := exists_seqData hL
  have hev : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hrateEv : (fun n => (D n).rate) =ᶠ[atTop] fun n => CutCur.spectralGap (V n) := by
    filter_upwards [hev] with n hn using (hD n hn).1
  have hgapD : ∀ᶠ n : ℕ in atTop, ((D n).rate)⁻¹ ≤ (Real.log n) ^ α := by
    filter_upwards [hα, hrateEv] with n h1 h2 using by rw [h2]; exact h1
  have hprof : ∀ n, 0 < n → ∀ t : ℝ,
      CutCur.worst (P n) (X n) (CutCur.meanBall (V n) c)
        (CutCur.wasserstein2 · (CutCur.gibbs (V n))) t =
        ENNReal.ofReal (barycenterBallWasserstein (D n) c t) := by
    intro n hn t
    obtain ⟨hr, hpot, hk⟩ := hD n hn
    have := worst_wasserstein_eq hn (D n) hc.le (P := P n) (X := X n) hk t
    rwa [hpot] at this
  have hcrit : ∀ n, 0 < n → CutCur.criticalTime n (CutCur.spectralGap (V n)) =
      criticalTime n (D n).rate := by
    intro n hn
    rw [(hD n hn).1]
    rfl
  intro ε hε0 hε1
  constructor
  · have h1 := ENNReal.tendsto_ofReal_atTop.comp
      (barycenter_wasserstein_before_cutoff D hc hε0 hε1)
    refine h1.congr' ?_
    filter_upwards [hev] with n hn
    simp only [Function.comp, hprof n hn, hcrit n hn]
  · have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp
      (barycenter_wasserstein_after_cutoff_weak D hc.le hε0 hgapD)
    rw [ENNReal.ofReal_zero] at h2
    refine h2.congr' ?_
    filter_upwards [hev] with n hn
    simp only [Function.comp, hprof n hn, hcrit n hn]

end CutoffRigidity.Paper
