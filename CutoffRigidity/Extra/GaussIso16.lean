module

public import CutoffRigidity.Extra.GaussIso15

/-! # Isoperimetry for sets (stage 7c): Bobkov's inequality for `ψ ∘ e`, `e` `1`-Lipschitz -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ContDiff

set_option linter.unusedSectionVars false

namespace CutoffRigidity.GaussIso

variable {d : ℕ}

/-- The integrand `G(t) = √(I(ψ t)² + ρ⁻¹ ψ'(t)²)`. -/
noncomputable def Gfun (ρ : ℝ) (ψ : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.sqrt (gI (ψ t) ^ 2 + ρ⁻¹ * deriv ψ t ^ 2)

lemma norm_gradient_eq (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  unfold gradient
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.norm_map _

/-- **Bobkov's inequality for `ψ ∘ e`** where `e` is `1`-Lipschitz and `ψ` smooth with values in `[0,1]`. -/
theorem bobkov_ramp {ρ : ℝ} (hρ : 0 < ρ) {e : EuclideanSpace ℝ (Fin d) → ℝ} (he : LipschitzWith 1 e)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (h01 : ∀ u, 0 ≤ ψ u ∧ ψ u ≤ 1)
    (hb : ∃ C, ∀ u, |deriv ψ u| ≤ C) :
    gI (∫ x, ψ (e x) ∂gaussρ d ρ) ≤ ∫ x, Gfun ρ ψ (e x) ∂gaussρ d ρ := by
  obtain ⟨C, hC⟩ := hb
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hψc : Continuous ψ := hψ.continuous
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_cast)
  have hdψ : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have hGc : Continuous (Gfun ρ ψ) := by
    unfold Gfun
    exact Real.continuous_sqrt.comp (((continuous_gI_comp hψc h01).pow 2).add (continuous_const.mul (hdψ.pow 2)))
  set K : ℝ := Real.sqrt (gφ 0 ^ 2 + ρ⁻¹ * C ^ 2) with hK
  have hGb : ∀ t, |Gfun ρ ψ t| ≤ K := by
    intro t
    unfold Gfun
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    apply Real.sqrt_le_sqrt
    have h1 : gI (ψ t) ^ 2 ≤ gφ 0 ^ 2 := by
      have := gI_le (ψ t); have := gI_nonneg (ψ t)
      nlinarith
    have h2 : deriv ψ t ^ 2 ≤ C ^ 2 := by
      have := hC t; nlinarith [abs_nonneg (deriv ψ t), sq_abs (deriv ψ t)]
    have : 0 ≤ ρ⁻¹ := inv_nonneg.2 hρ.le
    nlinarith
  have hψL : LipschitzWith (Real.toNNReal C) ψ := by
    refine lipschitzWith_of_nnnorm_deriv_le (hψ1.differentiable (by norm_num)) fun x => ?_
    have := hC x
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hC0]
    simpa [Real.norm_eq_abs] using this
  -- approximants
  have happ : ∀ n : ℕ, ∃ u : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ u ∧ LipschitzWith 1 u ∧
      ∀ x, |u x - e x| ≤ 1 / ((n : ℝ) + 1) := fun n =>
    exists_smooth_lipschitz_approx he (by positivity)
  choose u hu hu1 hue using happ
  have hconv : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (e x)) := by
    intro x
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Real.dist_eq]; exact hue n x
  -- Bobkov for each approximant
  have hstep : ∀ n, gI (∫ x, ψ (u n x) ∂gaussρ d ρ) ≤ ∫ x, Gfun ρ ψ (u n x) ∂gaussρ d ρ := by
    intro n
    have hun : ContDiff ℝ 1 (u n) := (hu n).of_le (by norm_cast)
    have hfn : ContDiff ℝ 1 (fun x => ψ (u n x)) := hψ1.comp hun
    have hLn : LipschitzWith (Real.toNNReal C * 1) (fun x => ψ (u n x)) := hψL.comp (hu1 n)
    have key := gaussρ_bobkov hρ hfn hLn (fun x => h01 _)
    refine key.trans ?_
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => Real.sqrt_nonneg _) ?_
      (Eventually.of_forall fun x => ?_)
    · obtain ⟨K', hK'⟩ : ∃ K', ∀ x, |Gfun ρ ψ (u n x)| ≤ K' := ⟨K, fun x => hGb _⟩
      exact Integrable.mono' (integrable_const K') (hGc.comp (hu n).continuous).aestronglyMeasurable
        (Eventually.of_forall fun x => by simpa using hK' x)
    · have hgrad : ‖gradient (fun x => ψ (u n x)) x‖ ≤ |deriv ψ (u n x)| := by
        rw [norm_gradient_eq]
        have hd := ((hψ1.differentiable (by norm_num)) (u n x)).hasDerivAt.comp_hasFDerivAt x
          (((hun.differentiable (by norm_num)) x).hasFDerivAt)
        rw [show (fun x => ψ (u n x)) = ψ ∘ u n from rfl, hd.fderiv, norm_smul, Real.norm_eq_abs]
        have : ‖fderiv ℝ (u n) x‖ ≤ 1 := by simpa using norm_fderiv_le_of_lipschitz ℝ (hu1 n) (x₀ := x)
        calc |deriv ψ (u n x)| * ‖fderiv ℝ (u n) x‖ ≤ |deriv ψ (u n x)| * 1 :=
              mul_le_mul_of_nonneg_left this (abs_nonneg _)
          _ = _ := mul_one _
      show Real.sqrt (gI (ψ (u n x)) ^ 2 + ρ⁻¹ * ‖gradient (fun x => ψ (u n x)) x‖ ^ 2) ≤ Gfun ρ ψ (u n x)
      unfold Gfun
      apply Real.sqrt_le_sqrt
      have : 0 ≤ ρ⁻¹ := inv_nonneg.2 hρ.le
      have h2 : ‖gradient (fun x => ψ (u n x)) x‖ ^ 2 ≤ deriv ψ (u n x) ^ 2 := by
        have := hgrad
        nlinarith [norm_nonneg (gradient (fun x => ψ (u n x)) x), sq_abs (deriv ψ (u n x))]
      nlinarith
  -- limits
  have hLim1 : Tendsto (fun n => ∫ x, ψ (u n x) ∂gaussρ d ρ) atTop (𝓝 (∫ x, ψ (e x) ∂gaussρ d ρ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => 1) (fun n => ?_) (integrable_const 1)
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · exact (hψc.comp (hu n).continuous).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (h01 _).1]; exact (h01 _).2
    · exact (hψc.tendsto _).comp (hconv x)
  have hLim2 : Tendsto (fun n => ∫ x, Gfun ρ ψ (u n x) ∂gaussρ d ρ) atTop
      (𝓝 (∫ x, Gfun ρ ψ (e x) ∂gaussρ d ρ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => K) (fun n => ?_) (integrable_const K)
      (fun n => Eventually.of_forall fun x => by simpa using hGb (u n x)) (Eventually.of_forall fun x => ?_)
    · exact (hGc.comp (hu n).continuous).aestronglyMeasurable
    · exact (hGc.tendsto _).comp (hconv x)
  have hLim1' : Tendsto (fun n => gI (∫ x, ψ (u n x) ∂gaussρ d ρ)) atTop
      (𝓝 (gI (∫ x, ψ (e x) ∂gaussρ d ρ))) := by
    have hmem : ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
        (∫ x, f x ∂gaussρ d ρ) ∈ Icc (0:ℝ) 1 := fun f hf => by
      constructor
      · exact integral_nonneg fun x => (hf x).1
      · calc (∫ x, f x ∂gaussρ d ρ) ≤ ∫ x, (1:ℝ) ∂gaussρ d ρ := by
              refine integral_mono_of_nonneg (Eventually.of_forall fun x => (hf x).1) (integrable_const 1)
                (Eventually.of_forall fun x => (hf x).2)
          _ = 1 := by simp
    have hpath : Tendsto (fun n => ∫ x, ψ (u n x) ∂gaussρ d ρ) atTop
        (𝓝[Icc (0:ℝ) 1] (∫ x, ψ (e x) ∂gaussρ d ρ)) :=
      tendsto_nhdsWithin_iff.2 ⟨hLim1, Eventually.of_forall fun n => hmem _ fun x => h01 _⟩
    exact (continuousWithinAt_gI (hmem _ fun x => h01 _)).tendsto.comp hpath
  exact le_of_tendsto_of_tendsto hLim1' hLim2 (Eventually.of_forall hstep)

end CutoffRigidity.GaussIso
