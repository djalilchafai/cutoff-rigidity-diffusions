module

public import CutoffRigidity.Extra.GaussIso14

/-! # Isoperimetry for sets (stage 7b): a smooth, almost linear ramp -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ContDiff Convolution

set_option linter.unusedSectionVars false

namespace CutoffRigidity.GaussIso

/-- A smooth density `k` supported in `(0,1)` with `0 ≤ k ≤ 1 + η`. -/
theorem exists_smooth_density {η : ℝ} (hη : 0 < η) :
    ∃ k : ℝ → ℝ, ContDiff ℝ ∞ k ∧ (∀ x, 0 ≤ k x ∧ k x ≤ 1 + η) ∧ (∀ x, x ∉ Ioo (0:ℝ) 1 → k x = 0) ∧
      ∫ x, k x = 1 := by
  set ε : ℝ := min (η / (2 * (1 + η))) (1 / 4) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by norm_num)
  have hε1 : ε ≤ η / (2 * (1 + η)) := min_le_left _ _
  have hε2 : ε ≤ 1 / 4 := min_le_right _ _
  let φ : ContDiffBump (0 : ℝ) := ⟨ε / 2, ε, by positivity, by linarith⟩
  let κ : ℝ → ℝ := φ.normed volume
  let M : ℝ := 1 / (1 - 2 * ε)
  have hM : 0 < 1 - 2 * ε := by linarith
  let g0 : ℝ → ℝ := (Icc ε (1 - ε)).indicator (fun _ => M)
  have hg0int : Integrable g0 := (integrable_indicator_iff measurableSet_Icc).2
    (integrableOn_const (by simp))
  have hg0 : ∫ x, g0 x = 1 := by
    have hMM : M * (1 - 2 * ε) = 1 := by simp only [M]; field_simp
    simp only [g0, integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc,
      smul_eq_mul]
    rw [max_eq_left (by linarith)]
    nlinarith [hMM]
  have hκc : HasCompactSupport κ := φ.hasCompactSupport_normed
  refine ⟨κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g0, ?_, ?_, ?_, ?_⟩
  · exact hκc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) φ.contDiff_normed
      hg0int.locallyIntegrable
  · intro x
    have h1 : (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g0) x = ∫ t, κ t * g0 (x - t) := rfl
    rw [h1]
    refine ⟨integral_nonneg fun t => mul_nonneg (φ.nonneg_normed t) ?_, ?_⟩
    · exact indicator_nonneg (fun _ _ => by positivity) _
    · have hMle : M ≤ 1 + η := by
        simp only [M]
        rw [div_le_iff₀ hM]
        have : 2 * ε * (1 + η) ≤ η := by
          have := mul_le_mul_of_nonneg_right hε1 (by positivity : (0:ℝ) ≤ 2 * (1 + η))
          calc 2 * ε * (1 + η) = ε * (2 * (1 + η)) := by ring
            _ ≤ η / (2 * (1 + η)) * (2 * (1 + η)) := this
            _ = η := by field_simp
        nlinarith
      calc ∫ t, κ t * g0 (x - t) ≤ ∫ t, κ t * M := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun t =>
              mul_nonneg (φ.nonneg_normed t) (indicator_nonneg (fun _ _ => by positivity) _)) ?_
              (Eventually.of_forall fun t => ?_)
            · exact (φ.integrable_normed).mul_const _
            · refine mul_le_mul_of_nonneg_left ?_ (φ.nonneg_normed t)
              exact indicator_le_self' (fun _ _ => by positivity) _
        _ = M := by rw [integral_mul_const]; simp [κ, φ.integral_normed]
        _ ≤ 1 + η := hMle
  · intro x hx
    by_contra hne
    have hmem : x ∈ Function.support (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g0) := hne
    obtain ⟨a, ha, b, hb, rfl⟩ := support_convolution_subset (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := volume) hmem
    have ha' : a ∈ ball (0:ℝ) ε := by
      have : a ∈ Function.support κ := ha
      rwa [φ.support_normed_eq] at this
    have hb' : b ∈ Icc ε (1 - ε) := by
      by_contra hb2
      exact hb (by simp [g0, hb2])
    rw [mem_ball, Real.dist_eq, sub_zero, abs_lt] at ha'
    apply hx
    constructor <;> linarith [hb'.1, hb'.2]
  · rw [integral_convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) φ.integrable_normed hg0int]
    simp [κ, φ.integral_normed, hg0]

/-- A smooth almost-linear ramp from `1` (for `u ≤ r`) to `0` (for `u ≥ r + s`), with slope at most `(1+η)/s`. -/
theorem exists_ramp {r s η : ℝ} (hs : 0 < s) (hη : 0 < η) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ u, 0 ≤ ψ u ∧ ψ u ≤ 1) ∧ (∀ u, u ≤ r → ψ u = 1) ∧
      (∀ u, r + s ≤ u → ψ u = 0) ∧ (∀ u, |deriv ψ u| ≤ (1 + η) / s) := by
  obtain ⟨k, hk, hkb, hksupp, hkint⟩ := exists_smooth_density hη
  have hkc : Continuous k := hk.continuous
  have hki : Integrable k := by
    by_contra h
    rw [integral_undef h] at hkint; norm_num at hkint
  -- primitive
  let T : ℝ → ℝ := fun x => ∫ t in x..1, k t
  have hT : ∀ x, HasDerivAt T (-k x) x := fun x => by
    have := intervalIntegral.integral_hasDerivAt_left (f := k) (a := x) (b := 1)
      (hkc.intervalIntegrable _ _) hkc.aestronglyMeasurable.stronglyMeasurableAtFilter hkc.continuousAt
    exact this
  have hTsmooth : ContDiff ℝ ∞ T := by
    rw [contDiff_infty_iff_deriv]
    refine ⟨fun x => (hT x).differentiableAt, ?_⟩
    have : deriv T = fun x => -k x := funext fun x => (hT x).deriv
    rw [this]; exact hk.neg
  have hTle0 : ∀ x ≤ 0, T x = 1 := by
    intro x hx
    show ∫ t in x..1, k t = 1
    have h1 : ∫ t in x..0, k t = 0 := by
      rw [intervalIntegral.integral_of_le hx]
      refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => hksupp t ?_
      intro hmem; exact absurd hmem.1 (not_lt.2 ht.2)
    have h2 : ∫ t in (0:ℝ)..1, k t = 1 := by
      rw [intervalIntegral.integral_of_le zero_le_one]
      have : (Ioc (0:ℝ) 1).indicator k = k := by
        funext t
        by_cases ht : t ∈ Ioc (0:ℝ) 1
        · simp [ht]
        · rw [indicator_of_notMem ht]
          symm
          apply hksupp
          intro hmem; exact ht ⟨hmem.1, hmem.2.le⟩
      have h3 : ∫ t in Ioc (0:ℝ) 1, k t = ∫ t, k t := by
        rw [← integral_indicator measurableSet_Ioc, this]
      rw [h3, hkint]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hkc.intervalIntegrable _ _)
      (hkc.intervalIntegrable _ _) (b := 0), h1, h2]; simp
  have hTge1 : ∀ x, 1 ≤ x → T x = 0 := by
    intro x hx
    show ∫ t in x..1, k t = 0
    rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hx]
    rw [setIntegral_eq_zero_of_forall_eq_zero fun t ht => hksupp t ?_]
    · simp
    · intro hmem; exact absurd hmem.2 (not_lt.2 ht.1.le)
  have hTmono : ∀ x y, x ≤ y → T y ≤ T x := by
    intro x y hxy
    show ∫ t in y..1, k t ≤ ∫ t in x..1, k t
    have h2 : 0 ≤ ∫ t in x..y, k t := intervalIntegral.integral_nonneg hxy fun t _ => (hkb t).1
    have h3 : ∫ t in x..1, k t = (∫ t in x..y, k t) + ∫ t in y..1, k t :=
      (intervalIntegral.integral_add_adjacent_intervals (hkc.intervalIntegrable _ _)
        (hkc.intervalIntegrable _ _)).symm
    linarith
  refine ⟨fun u => T ((u - r) / s), ?_, fun u => ⟨?_, ?_⟩, fun u hu => ?_, fun u hu => ?_, fun u => ?_⟩
  · exact hTsmooth.comp (by fun_prop)
  · show 0 ≤ T ((u - r) / s)
    by_cases h : (u - r) / s ≤ 1
    · have := hTmono _ _ h
      rw [hTge1 1 le_rfl] at this
      exact this
    · rw [hTge1 _ (not_le.1 h).le]
  · show T ((u - r) / s) ≤ 1
    by_cases h : 0 ≤ (u - r) / s
    · have := hTmono 0 _ h
      rw [hTle0 0 le_rfl] at this
      exact this
    · rw [hTle0 _ (not_le.1 h).le]
  · exact hTle0 _ (div_nonpos_of_nonpos_of_nonneg (by linarith) hs.le)
  · exact hTge1 _ ((one_le_div hs).2 (by linarith))
  · have hd : HasDerivAt (fun u => T ((u - r) / s)) (-k ((u - r) / s) / s) u := by
      have h1 : HasDerivAt (fun u : ℝ => (u - r) / s) (1 / s) u := by
        simpa using ((hasDerivAt_id u).sub_const r).div_const s
      have := (hT ((u - r) / s)).comp u h1
      refine this.congr_deriv ?_
      field_simp
    rw [hd.deriv, abs_div, abs_neg, abs_of_pos hs, abs_of_nonneg (hkb _).1]
    exact div_le_div_of_nonneg_right (hkb _).2 hs.le

end CutoffRigidity.GaussIso
