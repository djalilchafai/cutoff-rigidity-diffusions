module

public import CutoffRigidity.Riemann.DiffKuwBE2
public import CutoffRigidity.Riemann.WeightedCutoffs
public import CutoffRigidity.Riemann.WeightedProper
public import CutoffRigidity.Riemann.DiffKuwPre

/-! # KUW-BE3: pointwise Bakry-Emery bound for Lipschitz functions -/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set Topology
open scoped Manifold ContDiff ENNReal Topology NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section BE3

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

theorem integrable_lipAt_sq {ψ : M → ℝ} {L : ℝ≥0} (hψ : LipschitzWith L ψ) (t : ℝ≥0) (x : M) :
    Integrable (fun y => lipAt ψ y ^ 2) (Kk F hV hμ t x) := by
  haveI := Kk_markov F hV hμ t
  have hfin := edist_ne_top_of_connected (F := F) (M := M)
  have hm : Measurable fun y => lipAt ψ y := measurable_lipAt hfin hψ
  refine Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable ((L : ℝ) ^ 2)
    (Filter.Eventually.of_forall fun y => ?_)
  have h0 := lipAt_nonneg ψ y
  have h1 := lipAt_le hfin hψ y
  rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg h0]
  exact pow_le_pow_left₀ h0 h1 2

/-- **(B2)** Pointwise Bakry-Emery bound for bounded Lipschitz functions. -/
theorem beLip {ρ : ℝ} (hBE : BETestFun F V μ ρ (Kk F hV hμ)) (hA : SharpApprox F M)
    {ψ : M → ℝ} {L : ℝ≥0} {B : ℝ} (hψ : LipschitzWith L ψ) (hB : ∀ x, |ψ x| ≤ B)
    {t : ℝ≥0} (ht : t ≠ 0) (x : M) :
    ‖mgrad F (semi (Kk F hV hμ) t ψ) x‖ ^ 2 ≤
      Real.exp (-2 * ρ * t) * ∫ y, lipAt ψ y ^ 2 ∂(Kk F hV hμ t x) := by
  haveI := Kk_markov F hV hμ t
  have hfin := edist_ne_top_of_connected (F := F) (M := M)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB x)
  choose g hgs hgd hgg using fun n : ℕ =>
    hA ψ L hψ (1 / ((n : ℝ) + 1)) (1 / ((n : ℝ) + 1)) (by positivity) (by positivity)
  obtain ⟨χ, hχ, hχ1⟩ := weightedCutoffs_of_complete F (M := M)
  set e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with he_def
  have he0 : ∀ n, 0 < e n := fun n => by simp only [he_def]; positivity
  have he1 : ∀ n, e n ≤ 1 := fun n => by
    simp only [he_def]
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have heT : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set f : ℕ → M → ℝ := fun n y => χ n y * g n y with hf_def
  have hfs : ∀ n, MSmooth F (f n) := fun n => (hχ n).1.mul (hgs n)
  have hfc : ∀ n, HasCompactSupport (f n) := fun n => (hχ n).2.1.mul_right
  have hgB : ∀ n y, |g n y| ≤ B + 1 := fun n y => by
    have h1 := hgd n y
    have h2 := hB y
    have h3 := he1 n
    have : |g n y| ≤ |ψ y| + |g n y - ψ y| := by
      calc |g n y| = |ψ y + (g n y - ψ y)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    simp only [he_def] at h3 ⊢
    linarith
  have hfB : ∀ n y, |f n y| ≤ B + 1 := fun n y => by
    simp only [hf_def]
    obtain ⟨h0, h1, -⟩ := (hχ n).2.2 y
    rw [abs_mul, abs_of_nonneg h0]
    calc χ n y * |g n y| ≤ 1 * (B + 1) :=
          mul_le_mul h1 (hgB n y) (abs_nonneg _) zero_le_one
      _ = B + 1 := one_mul _
  have hψB : ∀ y, |ψ y| ≤ B + 1 := fun y => (hB y).trans (by linarith)
  have hgt : ∀ y, Tendsto (fun n => g n y) atTop (𝓝 (ψ y)) := fun y => by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) heT
    rw [Real.dist_eq]; exact hgd n y
  have hlim : ∀ y, Tendsto (fun n => f n y) atTop (𝓝 (ψ y)) := fun y => by
    refine (hgt y).congr' ?_
    filter_upwards [hχ1 y] with n hn
    simp only [hf_def, hn, one_mul]
  have hconv := tendsto_grad_semi F hV hμ ht x (fun n => (hfs n).continuous) hψ.continuous hfB
    hψB hlim
  -- the dominating functions
  set a : ℕ → M → ℝ := fun n y => (1 + e n) * locLip ψ y (e n) + e n + (B + 1) * e n with ha_def
  set A : ℝ := 2 * L + 1 + (B + 1) with hA_def
  have ha_nonneg : ∀ n y, 0 ≤ a n y := fun n y => by
    have := locLip_nonneg ψ y (e n)
    have := he0 n
    simp only [ha_def]; positivity
  have ha_le : ∀ n y, a n y ≤ A := fun n y => by
    have h1 := locLip_le hfin hψ y (e n)
    have h2 := locLip_nonneg ψ y (e n)
    have h3 := he1 n
    have h4 := he0 n
    simp only [ha_def, hA_def]
    nlinarith [mul_le_mul (show 1 + e n ≤ 2 by linarith) h1 h2 (by norm_num),
      mul_le_mul_of_nonneg_left h3 (show 0 ≤ B + 1 by linarith)]
  have ha_meas : ∀ n, Measurable (a n) := fun n =>
    (((measurable_locLip hfin hψ (e n)).const_mul _).add_const _).add_const _
  have hgrad : ∀ n y, ‖mgrad F (f n) y‖ ≤ a n y := fun n y => by
    have hm : mgrad F (f n) y = χ n y • mgrad F (g n) y + g n y • mgrad F (χ n) y :=
      mgrad_mul F (hχ n).1 (hgs n) y
    obtain ⟨h0, h1, h2⟩ := (hχ n).2.2 y
    have h3 := hgg n y
    rw [hm]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0]
    have h4 : χ n y * ‖mgrad F (g n) y‖ ≤ (1 + e n) * locLip ψ y (e n) + e n :=
      (mul_le_mul h1 h3 (norm_nonneg _) zero_le_one).trans (by simp [he_def])
    have h5 : |g n y| * ‖mgrad F (χ n) y‖ ≤ (B + 1) * e n :=
      mul_le_mul (hgB n y) h2 (norm_nonneg _) (by linarith)
    simp only [ha_def]
    linarith
  have hint_a : ∀ n, Integrable (fun y => a n y ^ 2) (Kk F hV hμ t x) := fun n =>
    Integrable.of_bound ((ha_meas n).pow_const 2).aestronglyMeasurable (A ^ 2)
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg (ha_nonneg n y)]
        exact pow_le_pow_left₀ (ha_nonneg n y) (ha_le n y) 2)
  have hdom : Tendsto (fun n => ∫ y, a n y ^ 2 ∂(Kk F hV hμ t x)) atTop
      (𝓝 (∫ y, lipAt ψ y ^ 2 ∂(Kk F hV hμ t x))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => A ^ 2)
      (fun n => ((ha_meas n).pow_const 2).aestronglyMeasurable) (integrable_const _)
      (fun n => Filter.Eventually.of_forall fun y => ?_)
      (Filter.Eventually.of_forall fun y => ?_)
    · rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg (ha_nonneg n y)]
      exact pow_le_pow_left₀ (ha_nonneg n y) (ha_le n y) 2
    · have h := ((((tendsto_const_nhds (x := (1 : ℝ))).add heT).mul (tendsto_locLip hfin hψ y)).add
        heT).add (tendsto_const_nhds (x := B + 1) |>.mul heT)
      rw [show (1 + 0) * lipAt ψ y + 0 + (B + 1) * 0 = lipAt ψ y by ring] at h
      exact (show Tendsto (fun n => a n y) atTop (𝓝 (lipAt ψ y)) from h).pow 2
  have hle : ∀ n, ‖mgrad F (semi (Kk F hV hμ) t (f n)) x‖ ^ 2 ≤
      Real.exp (-2 * ρ * t) * ∫ y, a n y ^ 2 ∂(Kk F hV hμ t x) := fun n => by
    have h := hBE (f n) (hfs n) (hfc n) t x
    rw [carre_self_eq] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
    simp only [carre_self_eq]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => by positivity)
      (hint_a n) (Filter.Eventually.of_forall fun y => ?_)
    exact pow_le_pow_left₀ (norm_nonneg _) (hgrad n y) 2
  exact le_of_tendsto_of_tendsto' (hconv.norm.pow 2) (hdom.const_mul _) hle

end BE3

end CutoffRigidity.Riemann.Diff
