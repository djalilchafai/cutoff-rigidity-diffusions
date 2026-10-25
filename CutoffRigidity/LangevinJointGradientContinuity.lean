module
public import CutoffRigidity.LangevinC1Flow
public import CutoffRigidity.LangevinFeller

/-! # Joint time and initial-state continuity of the actual flow derivative

The actual variational ODE gives a uniform time Lipschitz estimate on compact
path tubes. Together with the proved C¹ initial-state dependence, this gives
joint continuity without a Lipschitz Hessian assumption.
-/
public section
namespace CutoffRigidity
open MeasureTheory Set Metric Filter
open scoped Topology NNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 800000 in
theorem continuous_fderiv_langevinSolution_time_initial
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (w : C(ℝ, E)) :
    Continuous (fun p : ℝ≥0 × E => fderiv ℝ (fun y => langevinSolution V w y p.1) p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let T : ℝ := p.1 + 1
  have hT : 0 ≤ T := by dsimp [T]; positivity
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (langevinSolution_isLangevinPathOn hV ρ hρ hHess w.continuous p.2 hT).1
  have hHc : Continuous (fun z => fderiv ℝ (gradient V) z) :=
    (contDiff_one_gradient_of_contDiff_two hV).continuous_fderiv one_ne_zero
  obtain ⟨K0, hK0⟩ := (isCompact_closedBall (0 : E) (R + 1)).exists_bound_of_continuousOn hHc.continuousOn
  let K := max K0 0
  have hK : 0 ≤ K := le_max_right _ _
  have htime (y : E) (hy : ‖y - p.2‖ ≤ 1) (s t : ℝ) (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
      ‖fderiv ℝ (fun z => langevinSolution V w z t) y -
        fderiv ℝ (fun z => langevinSolution V w z s) y‖ ≤ K * ‖t - s‖ := by
    obtain ⟨J, hJ0, hJC, hJD, hJE, hJn⟩ :=
      exists_langevin_variation_fderiv hV ρ hρ hHess w.continuous y hT
    rw [← hJE t ht, ← hJE s hs]
    apply (convex_Icc (0 : ℝ) T).norm_image_sub_le_of_norm_hasDerivWithin_le hJD _ hs ht
    intro r hr
    have hpath : langevinSolution V w y r ∈ closedBall (0 : E) (R + 1) := by
      rw [mem_closedBall, dist_zero_right]
      have hcon := langevinSolution_initial_point_contraction hV ρ hρ hHess w.continuous y p.2 hr.1
      have he : Real.exp (-ρ * r) ≤ 1 := Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hρ) hr.1)
      have hdist : ‖langevinSolution V w y r - langevinSolution V w p.2 r‖ ≤ 1 :=
        hcon.trans ((mul_le_of_le_one_left (norm_nonneg _) he).trans hy)
      exact (norm_le_norm_sub_add _ _).trans (add_le_add hdist (hR r hr)) |>.trans (by ring_nf; rfl)
    have hA : ‖fderiv ℝ (gradient V) (langevinSolution V w y r)‖ ≤ K :=
      (hK0 _ hpath).trans (le_max_left _ _)
    rw [norm_neg]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hA (hJn r hr) (norm_nonneg _) hK).trans (by simp))
  have hspace : Continuous (fun y => fderiv ℝ (fun z => langevinSolution V w z p.1) y) :=
    continuous_fderiv_langevinSolution_initial_point hV ρ hρ hHess w.continuous p.1.property
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb : Tendsto (fun q : ℝ≥0 × E => K * ‖(q.1 : ℝ) - p.1‖ +
      ‖fderiv ℝ (fun z => langevinSolution V w z p.1) q.2 -
        fderiv ℝ (fun z => langevinSolution V w z p.1) p.2‖) (𝓝 p) (𝓝 0) := by
    have hc : Continuous (fun q : ℝ≥0 × E => K * ‖(q.1 : ℝ) - p.1‖ +
        ‖fderiv ℝ (fun z => langevinSolution V w z p.1) q.2 -
          fderiv ℝ (fun z => langevinSolution V w z p.1) p.2‖) := by
      fun_prop
    simpa using hc.tendsto p
  apply squeeze_zero' (Eventually.of_forall fun q => norm_nonneg _) _ hb
  have ht : ∀ᶠ q : ℝ≥0 × E in 𝓝 p, (q.1 : ℝ) < T :=
    ((continuous_subtype_val.comp continuous_fst).tendsto p).eventually
      (eventually_lt_nhds (show (p.1 : ℝ) < T by dsimp [T]; linarith))
  have hx : ∀ᶠ q : ℝ≥0 × E in 𝓝 p, ‖q.2 - p.2‖ < 1 := by
    have hc : Continuous (fun q : ℝ≥0 × E => ‖q.2 - p.2‖) := by fun_prop
    exact (hc.tendsto p).eventually (eventually_lt_nhds (by simp : ‖p.2 - p.2‖ < 1))
  filter_upwards [ht, hx] with q ht hx
  exact (norm_sub_le_norm_sub_add_norm_sub _
    (fderiv ℝ (fun z => langevinSolution V w z p.1) q.2) _).trans
      (add_le_add (htime q.2 hx.le p.1 q.1
        ⟨p.1.property, by dsimp [T]; linarith⟩ ⟨q.1.property, ht.le⟩) (le_refl _))

end CutoffRigidity
