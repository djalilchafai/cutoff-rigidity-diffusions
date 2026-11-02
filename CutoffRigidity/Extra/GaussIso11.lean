module

public import CutoffRigidity.Extra.GaussIso10

/-! # Bobkov's inequality on `EuclideanSpace ℝ (Fin d)` for the Gaussian `N(0, ρ⁻¹ I)` (stage 6a) -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal

set_option linter.unusedSectionVars false

namespace CutoffRigidity.GaussIso

variable {d : ℕ}

/-- The Gaussian `N(0, ρ⁻¹ I_d)` on `ℝ^d`, as the image of the standard Gaussian by `x ↦ x/√ρ`. -/
noncomputable def gaussρ (d : ℕ) (ρ : ℝ) : Measure (EuclideanSpace ℝ (Fin d)) :=
  (stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun x => (Real.sqrt ρ)⁻¹ • x)

instance (ρ : ℝ) : IsProbabilityMeasure (gaussρ d ρ) :=
  (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance

lemma gaussρ_eq_map (ρ : ℝ) :
    gaussρ d ρ = (γn d).map (fun y : Fin d → ℝ => (Real.sqrt ρ)⁻¹ • (WithLp.toLp 2 y)) := by
  unfold gaussρ
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl


lemma sum_sq_fderiv_eq_norm_gradient (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ∑ i, (fderiv ℝ f x (EuclideanSpace.single i 1)) ^ 2 = ‖gradient f x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : fderiv ℝ f x (EuclideanSpace.single i 1) = inner ℝ (gradient f x) (EuclideanSpace.single i 1) :=
    (inner_gradient_left ..).symm
  have h2 : inner ℝ (gradient f x) (EuclideanSpace.single i (1:ℝ)) = (gradient f x).ofLp i := by
    rw [EuclideanSpace.inner_single_right]; simp
  rw [h1, h2]
  simp

/-- The linear change of variables from the product Gaussian to `N(0, ρ⁻¹ I)`. -/
noncomputable def Tρ (d : ℕ) (ρ : ℝ) (y : Fin d → ℝ) : EuclideanSpace ℝ (Fin d) :=
  (Real.sqrt ρ)⁻¹ • WithLp.toLp 2 y

lemma continuous_Tρ (ρ : ℝ) : Continuous (Tρ d ρ) := by unfold Tρ; fun_prop

lemma Tρ_update (ρ : ℝ) (y : Fin d → ℝ) (i : Fin d) (r : ℝ) :
    Tρ d ρ (Function.update y i r) =
      Tρ d ρ y + ((r - y i) * (Real.sqrt ρ)⁻¹) • EuclideanSpace.single i (1:ℝ) := by
  ext j
  by_cases h : j = i
  · subst h; simp [Tρ]; ring
  · simp [Tρ, h]

/-- **Bobkov's inequality for `N(0, ρ⁻¹ I_d)`** on `EuclideanSpace ℝ (Fin d)`, `f : ℝ^d → [0,1]` of class `C¹`
and Lipschitz. -/
theorem gaussρ_bobkov {ρ : ℝ} (hρ : 0 < ρ) {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContDiff ℝ 1 f)
    {L : ℝ≥0} (hL : LipschitzWith L f) (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    gI (∫ x, f x ∂gaussρ d ρ) ≤
      ∫ x, Real.sqrt (gI (f x) ^ 2 + ρ⁻¹ * ‖gradient f x‖ ^ 2) ∂gaussρ d ρ := by
  set s : ℝ := (Real.sqrt ρ)⁻¹ with hs
  have hs0 : 0 < s := inv_pos.2 (Real.sqrt_pos.2 hρ)
  have hs2 : s ^ 2 = ρ⁻¹ := by
    rw [hs, inv_pow, Real.sq_sqrt hρ.le]
  let dd : Fin d → (Fin d → ℝ) → ℝ := fun i y => s * fderiv ℝ f (Tρ d ρ y) (EuclideanSpace.single i 1)
  have hP : PC d (fun y => f (Tρ d ρ y)) dd := by
    refine ⟨hf.continuous.comp (continuous_Tρ ρ), fun i => ?_, fun i => ?_, fun i y => ?_,
      fun y => h01 _⟩
    · have := (hf.continuous_fderiv one_ne_zero).comp (continuous_Tρ ρ)
      exact continuous_const.mul (this.clm_apply continuous_const)
    · refine ⟨s * L, fun y => ?_⟩
      show |s * fderiv ℝ f (Tρ d ρ y) (EuclideanSpace.single i 1)| ≤ s * L
      rw [abs_mul, abs_of_pos hs0]
      refine mul_le_mul_of_nonneg_left ?_ hs0.le
      have h1 := (fderiv ℝ f (Tρ d ρ y)).le_opNorm (EuclideanSpace.single i (1:ℝ))
      have h2 : ‖fderiv ℝ f (Tρ d ρ y)‖ ≤ L := norm_fderiv_le_of_lipschitz ℝ hL
      simp at h1
      calc |fderiv ℝ f (Tρ d ρ y) (EuclideanSpace.single i 1)| ≤ ‖fderiv ℝ f (Tρ d ρ y)‖ := by
            simpa [Real.norm_eq_abs] using h1
        _ ≤ L := h2
    · have hg : HasDerivAt (fun r => Tρ d ρ (Function.update y i r)) (s • EuclideanSpace.single i (1:ℝ)) (y i) := by
        have e : (fun r => Tρ d ρ (Function.update y i r)) =
            fun r => Tρ d ρ y + ((r - y i) * s) • EuclideanSpace.single i (1:ℝ) :=
          funext fun r => Tρ_update ρ y i r
        rw [e]
        have h1 : HasDerivAt (fun r : ℝ => (r - y i) * s) s (y i) := by
          simpa using ((hasDerivAt_id (y i)).sub_const (y i)).mul_const s
        have := (h1.smul_const (EuclideanSpace.single i (1:ℝ))).const_add (Tρ d ρ y)
        simpa using this
      have hat : Tρ d ρ (Function.update y i (y i)) = Tρ d ρ y := by simp
      have hfd : HasFDerivAt f (fderiv ℝ f (Tρ d ρ y)) (Tρ d ρ (Function.update y i (y i))) := by
        rw [hat]; exact (hf.differentiable one_ne_zero _).hasFDerivAt
      have := hfd.comp_hasDerivAt (y i) hg
      refine this.congr_deriv ?_
      simp [dd, map_smul]
  have key := bobkov_pc d _ _ hP
  have hgauss : gaussρ d ρ = (γn d).map (Tρ d ρ) := gaussρ_eq_map ρ
  have hTm : AEMeasurable (Tρ d ρ) (γn d) := (continuous_Tρ ρ).aemeasurable
  rw [hgauss, integral_map hTm hf.continuous.aestronglyMeasurable,
    integral_map hTm]
  · refine key.trans (le_of_eq ?_)
    congr 1; funext y
    unfold Ntot
    congr 2
    have : ∑ i, dd i y ^ 2 = s ^ 2 * ∑ i, (fderiv ℝ f (Tρ d ρ y) (EuclideanSpace.single i 1)) ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp only [dd]; ring
    rw [this, sum_sq_fderiv_eq_norm_gradient, hs2]
  · have hg : Continuous fun x => gradient f x := by
      have h1 : Continuous fun x => fderiv ℝ f x := hf.continuous_fderiv one_ne_zero
      have e : (fun x => gradient f x) = fun x => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm (fderiv ℝ f x) := rfl
      rw [e]
      exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.comp h1
    exact (Real.continuous_sqrt.comp (((continuous_gI_comp hf.continuous h01).pow 2).add
      (continuous_const.mul (hg.norm.pow 2)))).aestronglyMeasurable

end CutoffRigidity.GaussIso
