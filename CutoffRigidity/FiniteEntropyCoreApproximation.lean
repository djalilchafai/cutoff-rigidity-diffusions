module
public import CutoffRigidity.FiniteEntropyDensityTruncation

/-! # Genuine positive compact C² core approximation for finite relative entropy

Actual RN-density clipping and exact mass normalization give bounded
positive approximants. Actual square-root compact smoothing and a proved
diagonal choice produce normalized positive compact perturbations with
both L¹ and genuine KL convergence.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped Topology ENNReal NNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem klDiv_positive_compact_perturbation_ne_top
    (μ : Measure E) [IsProbabilityMeasure μ] {g : E → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (c : ℝ) (hc : 0 < c) (hFloor : ∀ x, c ≤ c + g x) (hMass : ∫ x, c + g x ∂μ = 1) :
    klDiv (μ.withDensity (fun x => ENNReal.ofReal (c + g x))) μ ≠ ⊤ := by
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg
  have hn (x : E) : 0 ≤ c + g x := (hc.trans_le (hFloor x)).le
  have hBound (x : E) : c + g x ≤ |c| + M :=
    (le_abs_self _).trans ((abs_add_le _ _).trans (add_le_add (le_refl _) (by simpa only [Real.norm_eq_abs] using hM x)))
  have hf : Measurable (fun x => c + g x) := by simpa only [Pi.add_def] using measurable_const.add hg.measurable
  rw [klDiv_bounded_positive_density_eq_integral hf (|c| + M) hn hBound hMass]
  exact ENNReal.ofReal_ne_top

set_option maxHeartbeats 1000000 in
/-- Actual source-core approximation of a possibly unbounded probability
density with finite genuine entropy integrand. No approximation sequence
or convergence is assumed. -/
theorem exists_finite_entropy_density_core_L1_KL_approx
    (μ : Measure E) [IsProbabilityMeasure μ] {f : E → ℝ}
    (hf : Measurable f) (hfI : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    (hMass : ∫ x, f x ∂μ = 1) (hKL : Integrable (fun x => klFun (f x)) μ) :
    ∃ (c : ℕ → ℝ) (g : ℕ → E → ℝ),
      (∀ n, ContDiff ℝ 2 (g n)) ∧ (∀ n, HasCompactSupport (g n)) ∧
      (∀ n, 0 < c n) ∧ (∀ n x, c n ≤ c n + g n x) ∧
      (∀ n, ∫ x, c n + g n x ∂μ = 1) ∧
      Tendsto (fun n => ∫ x, ‖c n + g n x - f x‖ ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun n => klDiv (μ.withDensity (fun x => ENNReal.ofReal (c n + g n x))) μ)
        atTop (𝓝 (klDiv (μ.withDensity (fun x => ENNReal.ofReal (f x))) μ)) := by
  obtain ⟨r, hrMeas, hrBounds, hrMass, hrL1, hrKL⟩ :=
    exists_bounded_positive_density_L1_KL_approx μ hf hfI hf0 hMass hKL
  choose a b ha hrB using hrBounds
  choose c g hg hgc hc hFloor hNorm hL1 hEntropy using (fun n =>
    exists_positive_compact_c2_density_L1_KL_approx μ (hrMeas n) (a n) (b n) (ha n)
      (fun x => (hrB n x).1) (fun x => (hrB n x).2) (hrMass n))
  let K := fun n k => klDiv (μ.withDensity (fun x => ENNReal.ofReal (c n k + g n k x))) μ
  let R := fun n => klDiv (μ.withDensity (fun x => ENNReal.ofReal (r n x))) μ
  let H := klDiv (μ.withDensity (fun x => ENNReal.ofReal (f x))) μ
  have hKfin (n k : ℕ) : K n k ≠ ⊤ :=
    klDiv_positive_compact_perturbation_ne_top μ (hg n k).continuous (hgc n k)
      (c n k) (hc n k) (hFloor n k) (hNorm n k)
  have hRfin (n : ℕ) : R n ≠ ⊤ := by
    dsimp only [R]
    rw [klDiv_bounded_positive_density_eq_integral (hrMeas n) (b n)
      (fun x => (ha n).trans_le (hrB n x).1 |>.le) (fun x => (hrB n x).2) (hrMass n)]
    exact ENNReal.ofReal_ne_top
  have hHfin : H ≠ ⊤ := by
    dsimp only [H]
    rw [klDiv_withDensity_eq_integral_of_klFun_integrable hf hfI hf0 hMass hKL]
    exact ENNReal.ofReal_ne_top
  have hEntropyReal (n : ℕ) : Tendsto (fun k => (K n k).toReal) atTop (𝓝 (R n).toReal) :=
    (ENNReal.continuousAt_toReal (hRfin n)).tendsto.comp (hEntropy n)
  have hRReal : Tendsto (fun n => (R n).toReal) atTop (𝓝 H.toReal) :=
    (ENNReal.continuousAt_toReal hHfin).tendsto.comp hrKL
  have hchoose (n : ℕ) : ∃ k : ℕ,
      (∫ x, ‖c n k + g n k x - r n x‖ ∂μ) < differenceStep n ∧
      ‖(K n k).toReal - (R n).toReal‖ < differenceStep n := by
    have h1 := (hL1 n).eventually (eventually_lt_nhds (differenceStep_pos n))
    have h2 := (tendsto_iff_norm_sub_tendsto_zero.mp (hEntropyReal n)).eventually
      (eventually_lt_nhds (differenceStep_pos n))
    exact (h1.and h2).exists
  choose j hjL1 hjKL using hchoose
  let C := fun n => c n (j n)
  let G := fun n => g n (j n)
  have hCoreL1 : Tendsto (fun n => ∫ x, ‖C n + G n x - f x‖ ∂μ) atTop (𝓝 0) := by
    have hfBoundI := hfI
    have hrI (n : ℕ) : Integrable (r n) μ := (integrable_const (b n)).mono'
      (hrMeas n).aestronglyMeasurable (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos ((ha n).trans_le (hrB n x).1)]; exact (hrB n x).2)
    have hcoreI (n : ℕ) : Integrable (fun x => C n + G n x) μ :=
      (integrable_const (C n)).add ((hg n (j n)).continuous.integrable_of_hasCompactSupport (hgc n (j n)))
    have hBound (n : ℕ) : (∫ x, ‖C n + G n x - f x‖ ∂μ) ≤
        differenceStep n + ∫ x, ‖r n x - f x‖ ∂μ := by
      have hpoint (x : E) : ‖C n + G n x - f x‖ ≤ ‖C n + G n x - r n x‖ + ‖r n x - f x‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      have hh := integral_mono ((hcoreI n).sub hfI).norm
        ((((hcoreI n).sub (hrI n)).norm).add (((hrI n).sub hfI).norm)) hpoint
      have hAdd := integral_add ((hcoreI n).sub (hrI n)).norm ((hrI n).sub hfI).norm
      simp only [Pi.add_apply, Pi.sub_apply] at hAdd hh
      rw [hAdd] at hh
      exact hh.trans (add_le_add (hjL1 n).le le_rfl)
    exact squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _)) hBound
      (by simpa only [add_zero] using differenceStep_tendsto_zero.add hrL1)
  have hCoreKL : Tendsto (fun n => K n (j n)) atTop (𝓝 H) := by
    have hDiff : Tendsto (fun n => (K n (j n)).toReal - (R n).toReal) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => (hjKL n).le) differenceStep_tendsto_zero
    have hReal := hDiff.add hRReal
    simp only [sub_add_cancel, zero_add] at hReal
    have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hReal
    simpa only [Function.comp_def, ENNReal.ofReal_toReal (hKfin _ _), ENNReal.ofReal_toReal hHfin] using hh
  exact ⟨C, G, (fun n => hg n (j n)), (fun n => hgc n (j n)),
    (fun n => hc n (j n)), (fun n => hFloor n (j n)), (fun n => hNorm n (j n)), hCoreL1, hCoreKL⟩


/-- Every actual absolutely continuous probability law with finite KL has
source positive normalized compact C² approximants converging in actual
RN-density L¹ and genuine KL. All approximation and regularity data are
constructed; the RN density is the actual canonical measurable one. -/
theorem exists_finite_entropy_probability_core_L1_KL_approx
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hAC : ν ≪ μ) (hKLfin : klDiv ν μ ≠ ⊤) :
    ∃ (c : ℕ → ℝ) (g : ℕ → E → ℝ),
      (∀ n, ContDiff ℝ 2 (g n)) ∧ (∀ n, HasCompactSupport (g n)) ∧
      (∀ n, 0 < c n) ∧ (∀ n x, c n ≤ c n + g n x) ∧
      (∀ n, ∫ x, c n + g n x ∂μ = 1) ∧
      Tendsto (fun n => ∫ x, ‖c n + g n x - (ν.rnDeriv μ x).toReal‖ ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun n => klDiv (μ.withDensity (fun x => ENNReal.ofReal (c n + g n x))) μ)
        atTop (𝓝 (klDiv ν μ)) := by
  have hf : Measurable (fun x => (ν.rnDeriv μ x).toReal) := (Measure.measurable_rnDeriv ν μ).ennreal_toReal
  have hfI : Integrable (fun x => (ν.rnDeriv μ x).toReal) μ := Measure.integrable_toReal_rnDeriv
  have hMass : (∫ x, (ν.rnDeriv μ x).toReal ∂μ) = 1 := by
    rw [Measure.integral_toReal_rnDeriv hAC]
    simp
  have hKLI : Integrable (fun x => klFun ((ν.rnDeriv μ x).toReal)) μ :=
    (integrable_klFun_rnDeriv_iff hAC).mpr (klDiv_ne_top_iff.mp hKLfin).2
  have hh := exists_finite_entropy_density_core_L1_KL_approx μ hf hfI
    (fun _ => ENNReal.toReal_nonneg) hMass hKLI
  simpa only [withDensity_ofReal_toReal_rnDeriv_eq ν μ hAC] using hh

end CutoffRigidity
