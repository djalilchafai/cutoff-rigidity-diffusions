module

public import CutoffRigidity.Extra.NoBmMollify

/-! # Brownian-free LSI for `C²` potentials (step 3): `C²` compactly supported test functions -/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ContDiff ENNReal NNReal Convolution

namespace CutoffRigidity.NoBm

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem abs_molc_le (n : ℕ) {F : E → ℝ} (hF : Continuous F) {M : ℝ} (hM : ∀ x, |F x| ≤ M) (x : E) :
    |molc n F x| ≤ M := by
  have h := norm_integral_le_of_norm_le ((mol_integrable n).mul_const M)
    (f := fun t => mol n t * F (x - t)) (Eventually.of_forall fun t => by
      rw [norm_mul, Real.norm_of_nonneg (mol_nonneg n t), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hM _) (mol_nonneg n t))
  rw [integral_mul_const, mol_integral, one_mul] at h
  simpa [molc] using h

theorem molc_cs (n : ℕ) {F : E → ℝ} (hF : Continuous F) (hc : HasCompactSupport F) :
    HasCompactSupport (molc n F) := by
  rw [molc_eq]
  exact (mol_cs n).convolution _ hc

theorem fderiv_molc (n : ℕ) {F : E → ℝ} (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F) (x : E) :
    fderiv ℝ (molc n F) x = ∫ t, mol n t • fderiv ℝ F (x - t) := by
  have h := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    ((mol_contDiff n).continuous.locallyIntegrable (μ := (volume : Measure E))) hF x
  rw [← molc_eq] at h
  rw [h.fderiv, convolution_def]
  rfl

theorem norm_fderiv_molc_le (n : ℕ) {F : E → ℝ} (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F)
    {G : ℝ} (hG : ∀ y, ‖fderiv ℝ F y‖ ≤ G) (x : E) : ‖fderiv ℝ (molc n F) x‖ ≤ G := by
  rw [fderiv_molc n hF hc]
  have h := norm_integral_le_of_norm_le ((mol_integrable n).mul_const G)
    (f := fun t => mol n t • fderiv ℝ F (x - t)) (Eventually.of_forall fun t => by
      rw [norm_smul, Real.norm_of_nonneg (mol_nonneg n t)]
      exact mul_le_mul_of_nonneg_left (hG _) (mol_nonneg n t))
  rw [integral_mul_const, mol_integral, one_mul] at h
  exact h

theorem tendsto_fderiv_molc {F : E → ℝ} (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F) (x : E) :
    Tendsto (fun n => fderiv ℝ (molc n F) x) atTop (𝓝 (fderiv ℝ F x)) := by
  have := ContDiffBump.convolution_tendsto_right_of_continuous (μ := (volume : Measure E))
    (φ := fun n : ℕ => bump (d := d) n) (l := atTop) (g := fderiv ℝ F) ?_
    (hF.continuous_fderiv one_ne_zero) x
  · refine this.congr (fun n => ?_)
    rw [fderiv_molc n hF hc, mol, convolution_def]
    rfl
  · simp only [bump]
    exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)


section Main

variable {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V) {ρ : ℝ} (hρ : 0 < ρ)
  (hH : ∀ x z : EuclideanSpace ℝ (Fin d), ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)

include hV hρ hH in
/-- LSI for `C²` compactly supported tests, `C²` potential with `Hess V ≥ ρ`, no Brownian motion. -/
theorem lsi_C2_compact (hp : IsProbabilityMeasure (CutCur.gibbs V))
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    CutCur.entropyOf (CutCur.gibbs V) (fun x => f x ^ 2) ≤
      2 / ρ * ∫ x, ‖gradient f x‖ ^ 2 ∂CutCur.gibbs V := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_cast)
  obtain ⟨M, hM⟩ := exists_abs_bound hf.continuous hfc
  obtain ⟨Gb, hGb⟩ : ∃ G : ℝ, ∀ y, ‖fderiv ℝ f y‖ ≤ G := by
    obtain ⟨G, hG⟩ := exists_abs_bound (G := fun y => ‖fderiv ℝ f y‖)
      (hf1.continuous_fderiv one_ne_zero).norm (hfc.fderiv ℝ).norm
    exact ⟨G, fun y => by simpa using hG y⟩
  have hGb0 : 0 ≤ Gb := (norm_nonneg _).trans (hGb 0)
  set fn : ℕ → E → ℝ := fun n => molc n f with hfn
  have hfnd : ∀ n, ContDiff ℝ ∞ (fn n) := fun n => molc_contDiff n hf.continuous
  have hfnc : ∀ n, HasCompactSupport (fn n) := fun n => molc_cs n hf.continuous hfc
  have hfn1 : ∀ n, ContDiff ℝ 1 (fn n) := fun n => (hfnd n).of_le (by norm_cast)
  have hfM : ∀ n x, |fn n x| ≤ M := fun n x => abs_molc_le n hf.continuous hM x
  have hfG : ∀ n x, ‖fderiv ℝ (fn n) x‖ ≤ Gb := fun n x => norm_fderiv_molc_le n hf1 hfc hGb x
  have hfx : ∀ x, Tendsto (fun n => fn n x) atTop (𝓝 (f x)) := fun x => molc_tendsto hf.continuous x
  have hgx : ∀ x, Tendsto (fun n => ‖gradient (fn n) x‖ ^ 2) atTop (𝓝 (‖gradient f x‖ ^ 2)) := by
    intro x
    simp_rw [norm_gradient_eq']
    exact ((tendsto_fderiv_molc hf1 hfc x).norm).pow 2
  obtain ⟨B1, hB1⟩ := (isCompact_Icc (a := -M) (b := M)).exists_bound_of_continuousOn
    (Real.continuous_mul_log.comp (continuous_pow 2)).continuousOn
  have hμ : IsFiniteMeasure (CutCur.gibbs V) := inferInstance
  have t1 : Tendsto (fun n => ∫ x, fn n x ^ 2 * Real.log (fn n x ^ 2) ∂CutCur.gibbs V) atTop
      (𝓝 (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂CutCur.gibbs V)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => B1) (fun n => ?_) (integrable_const _)
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · exact (cont_sqlog (hfnd n).continuous).aestronglyMeasurable
    · exact hB1 _ (abs_le.mp (hfM n x))
    · exact (Real.continuous_mul_log.comp (continuous_pow 2)).continuousAt.tendsto.comp (hfx x)
  have t2 : Tendsto (fun n => ∫ x, fn n x ^ 2 ∂CutCur.gibbs V) atTop
      (𝓝 (∫ x, f x ^ 2 ∂CutCur.gibbs V)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => M ^ 2) (fun n => ?_) (integrable_const _)
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · exact ((hfnd n).continuous.pow 2).aestronglyMeasurable
    · have := hfM n x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq' (abs_le.mp this).1 (abs_le.mp this).2)
    · exact ((continuous_pow 2).tendsto _).comp (hfx x)
  have t3 : Tendsto (fun n => ∫ x, ‖gradient (fn n) x‖ ^ 2 ∂CutCur.gibbs V) atTop
      (𝓝 (∫ x, ‖gradient f x‖ ^ 2 ∂CutCur.gibbs V)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => Gb ^ 2) (fun n => ?_) (integrable_const _)
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall hgx)
    · exact (cont_gradsq (hfn1 n)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_gradient_eq']
      exact pow_le_pow_left₀ (norm_nonneg _) (hfG n x) 2
  have hlhs : Tendsto (fun n => CutCur.entropyOf (CutCur.gibbs V) (fun x => fn n x ^ 2)) atTop
      (𝓝 (CutCur.entropyOf (CutCur.gibbs V) (fun x => f x ^ 2))) := by
    unfold CutCur.entropyOf
    have t4 := (Real.continuous_mul_log.tendsto _).comp t2
    refine t1.sub ?_
    simpa [Function.comp_def, mul_comm] using t4
  exact le_of_tendsto_of_tendsto' hlhs (t3.const_mul _) fun n =>
    lsi_C2_smooth_compact hV hρ hH hp (hfnd n) (hfnc n)

end Main

end CutoffRigidity.NoBm
