module

public import CutoffRigidity.Extra.C2Uniq1
public import CutoffRigidity.Extra.NoBmMollify

/-! # `C²` uniqueness, stage 2: mollified strongly convex potentials

`Wm V n = (1/(n+1)) ‖x‖²/2 + (ψ_n ⋆ V)` for a convex `C²` potential `V`:
smooth, `Hess ≥ 1/(n+1) > 0`, finite Gibbs measure, and `∇ Wm V n → ∇ V` locally uniformly.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutCur

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff Convolution

namespace C2U

variable {d : ℕ}

/-- The mollified strongly convex potentials. -/
noncomputable def Wm (V : Rd d → ℝ) (n : ℕ) (x : Rd d) : ℝ :=
  (1 / ((n : ℝ) + 1)) / 2 * ‖x‖ ^ 2 + CutoffRigidity.NoBm.molc n V x

theorem fderiv_molc {V : Rd d → ℝ} (hV : ContDiff ℝ 1 V) (n : ℕ) (x₀ : Rd d) :
    fderiv ℝ (CutoffRigidity.NoBm.molc n V) x₀ =
      ∫ t, CutoffRigidity.NoBm.mol n t • fderiv ℝ V (x₀ - t) := by
  set R : ℝ := ‖x₀‖ + 2 with hR
  have hRpos : 0 < R := by positivity
  let ψ : ContDiffBump (0 : Rd d) := ⟨R, R + 1, hRpos, by linarith⟩
  have hψ1 : ∀ y : Rd d, ‖y‖ ≤ R → ψ y = 1 := fun y hy =>
    ψ.one_of_mem_closedBall (by simpa [ψ] using hy)
  set g : Rd d → ℝ := fun y => ψ y * V y with hg
  have hgs : ContDiff ℝ 1 g := (ψ.contDiff (n := 1)).mul hV
  have hgc : HasCompactSupport g := ψ.hasCompactSupport.mul_right
  have hmol : LocallyIntegrable (CutoffRigidity.NoBm.mol (d := d) n) volume :=
    (CutoffRigidity.NoBm.mol_integrable n).locallyIntegrable
  have hD := hgc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hmol hgs x₀
  -- equality near x₀
  have hnear : ∀ x : Rd d, ‖x - x₀‖ < 1 →
      CutoffRigidity.NoBm.molc n V x =
        ((CutoffRigidity.NoBm.mol n) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
    intro x hx
    simp only [CutoffRigidity.NoBm.molc, convolution_def]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    by_cases ht : CutoffRigidity.NoBm.mol (d := d) n t = 0
    · simp [ht]
    · have h1 := CutoffRigidity.NoBm.mol_support n ht
      have h2 : ‖x - t‖ ≤ R := by
        have : ‖x‖ ≤ ‖x₀‖ + 1 := by
          have := norm_le_norm_add_norm_sub' x x₀
          have : ‖x‖ ≤ ‖x₀‖ + ‖x - x₀‖ := by
            calc ‖x‖ = ‖x₀ + (x - x₀)‖ := by rw [add_sub_cancel]
              _ ≤ ‖x₀‖ + ‖x - x₀‖ := norm_add_le _ _
          linarith
        have := norm_sub_le x t
        linarith
      simp [hg, hψ1 _ h2]
  have hev : (CutoffRigidity.NoBm.molc n V) =ᶠ[𝓝 x₀]
      ((CutoffRigidity.NoBm.mol n) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) := by
    filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with x hx
    exact hnear x (by simpa [dist_eq_norm] using hx)
  have hD' := hD.congr_of_eventuallyEq hev
  rw [hD'.fderiv]
  simp only [convolution_def]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  by_cases ht : CutoffRigidity.NoBm.mol (d := d) n t = 0
  · simp [ht]
  · have h1 := CutoffRigidity.NoBm.mol_support n ht
    have h2 : ‖x₀ - t‖ < R := by
      have := norm_sub_le x₀ t
      linarith
    have hloc : g =ᶠ[𝓝 (x₀ - t)] V := by
      have hopen : Metric.ball (0 : Rd d) R ∈ 𝓝 (x₀ - t) :=
        Metric.isOpen_ball.mem_nhds (by simpa using h2)
      filter_upwards [hopen] with y hy
      have : ‖y‖ ≤ R := (mem_ball_zero_iff.1 hy).le
      simp [hg, hψ1 y this]
    dsimp only
    rw [hloc.fderiv_eq]
    ext z
    simp [ContinuousLinearMap.precompR_apply]


section Props

variable {V : Rd d → ℝ}

theorem Wm_contDiff (hV : ContDiff ℝ 2 V) (n : ℕ) : ContDiff ℝ ∞ (Wm V n) :=
  (contDiff_const.mul (contDiff_norm_sq ℝ)).add
    (CutoffRigidity.NoBm.molc_contDiff n hV.continuous)

theorem Wm_convex (hV : ContDiff ℝ 2 V) (hc : ConvexOn ℝ univ V) (n : ℕ) :
    ConvexOn ℝ univ (CutoffRigidity.NoBm.molc n V) :=
  CutoffRigidity.NoBm.molc_convex n hV.continuous hc

theorem Wm_hess (hV : ContDiff ℝ 2 V) (hc : ConvexOn ℝ univ V) (n : ℕ) (x z : Rd d) :
    (1 / ((n : ℝ) + 1)) * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (Wm V n)) x z z := by
  have := CutoffRigidity.hessian_quadratic_add_convex_lower
    ((CutoffRigidity.NoBm.molc_contDiff n hV.continuous).of_le (by norm_cast))
    (Wm_convex hV hc n) (1 / ((n : ℝ) + 1)) x z
  exact this

theorem integrable_exp_Wm (hV : ContDiff ℝ 2 V) (hc : ConvexOn ℝ univ V) (n : ℕ) :
    Integrable (fun x => Real.exp (-Wm V n x)) volume := by
  have := (CutoffRigidity.convexInteraction_partition_finite_positive
    ((CutoffRigidity.NoBm.molc_contDiff n hV.continuous).of_le (by norm_cast))
    (Wm_convex hV hc n) (1 / ((n : ℝ) + 1)) (by positivity)).1
  exact this

theorem isFiniteMeasure_gibbs_Wm (hV : ContDiff ℝ 2 V) (hc : ConvexOn ℝ univ V) (n : ℕ) :
    IsFiniteMeasure (gibbs (Wm V n)) := by
  unfold gibbs
  refine isFiniteMeasure_withDensity_ofReal ?_
  exact (integrable_exp_Wm hV hc n).hasFiniteIntegral

theorem norm_gradient_sub (f g : Rd d → ℝ) (x : Rd d) :
    ‖gradient f x - gradient g x‖ = ‖fderiv ℝ f x - fderiv ℝ g x‖ := by
  unfold gradient
  rw [← map_sub]
  exact LinearIsometryEquiv.norm_map _ _

/-- The mollified potentials have gradients converging to `∇ V`, uniformly on balls. -/
theorem Wm_grad_close (hV : ContDiff ℝ 2 V) (R δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x : Rd d, ‖x‖ ≤ R →
      ‖gradient (Wm V n) x - gradient V x‖ ≤ δ := by
  have hV1 : ContDiff ℝ 1 V := hV.of_le (by norm_cast)
  have hG : Continuous (fderiv ℝ V) := hV1.continuous_fderiv one_ne_zero
  -- uniform continuity of the derivative on the ball of radius R + 1
  have hK : IsCompact (Metric.closedBall (0 : Rd d) (max R 0 + 1)) := isCompact_closedBall _ _
  obtain ⟨η, hη, hu⟩ := Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hG.continuousOn)
    (δ / 2) (half_pos hδ)
  obtain ⟨N₁, hN₁⟩ := exists_nat_one_div_lt (lt_min hη one_pos)
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (2 * max R 0 / δ)
  refine ⟨max N₁ N₂, fun n hn x hx => ?_⟩
  have hn1 : N₁ ≤ n := (le_max_left _ _).trans hn
  have hn2 : N₂ ≤ n := (le_max_right _ _).trans hn
  have hε : 1 / ((n : ℝ) + 1) < min η 1 := by
    refine lt_of_le_of_lt ?_ hN₁
    apply one_div_le_one_div_of_le (by positivity)
    have : (N₁ : ℝ) ≤ n := by exact_mod_cast hn1
    linarith
  rw [norm_gradient_sub]
  have h1 := ((hasStrictFDerivAt_norm_sq (F := Rd d) x).hasFDerivAt).const_mul
    ((1 / ((n : ℝ) + 1)) / 2)
  have h2 : DifferentiableAt ℝ (CutoffRigidity.NoBm.molc n V) x :=
    ((CutoffRigidity.NoBm.molc_contDiff n hV.continuous).differentiable (by norm_num)) x
  have hdW := (h1.add h2.hasFDerivAt).fderiv
  set Q := ((1 / ((n : ℝ) + 1)) / 2) • (2 • innerSL ℝ x) with hQ
  have hdW' : fderiv ℝ (Wm V n) x = Q + fderiv ℝ (CutoffRigidity.NoBm.molc n V) x := hdW
  rw [hdW']
  have hmol : ‖fderiv ℝ (CutoffRigidity.NoBm.molc n V) x - fderiv ℝ V x‖ ≤ δ / 2 := by
    rw [fderiv_molc hV1 n x]
    have hconv := (CutoffRigidity.NoBm.bump (d := d) n).dist_normed_convolution_le
      (μ := (volume : Measure (Rd d))) (x₀ := x) (ε := δ / 2) (g := fderiv ℝ V)
      hG.aestronglyMeasurable (fun y hy => by
        have hy' : dist y x < 1 / ((n : ℝ) + 1) := by
          simpa [CutoffRigidity.NoBm.bump] using hy
        have hyK : y ∈ Metric.closedBall (0 : Rd d) (max R 0 + 1) := by
          rw [mem_closedBall_zero_iff]
          have h1 : ‖y - x‖ < 1 := by
            rw [← dist_eq_norm]; exact lt_of_lt_of_le hy' (hε.le.trans (min_le_right _ _))
          have : ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by
            calc ‖y‖ = ‖x + (y - x)‖ := by rw [add_sub_cancel]
              _ ≤ _ := norm_add_le _ _
          have := le_max_left R 0
          linarith
        have hxK : x ∈ Metric.closedBall (0 : Rd d) (max R 0 + 1) := by
          rw [mem_closedBall_zero_iff]
          have := le_max_left R 0
          linarith
        exact (hu y hyK x hxK (lt_of_lt_of_le hy' (hε.le.trans (min_le_left _ _)))).le)
    have hmoleq : ((CutoffRigidity.NoBm.bump (d := d) n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        fderiv ℝ V) x = ∫ t, CutoffRigidity.NoBm.mol n t • fderiv ℝ V (x - t) := by
      simp [convolution_def, CutoffRigidity.NoBm.mol]
    rw [hmoleq] at hconv
    rwa [dist_eq_norm] at hconv
  have hquad : ‖Q‖ ≤ δ / 2 := by
    have h3 : ‖Q‖ ≤ (1 / ((n : ℝ) + 1)) * ‖x‖ := by
      rw [hQ, norm_smul, Real.norm_of_nonneg (by positivity)]
      have h4 : ‖(2 : ℕ) • innerSL ℝ x‖ ≤ 2 * ‖x‖ := by
        refine norm_nsmul_le.trans ?_
        rw [innerSL_apply_norm]; simp
      calc (1 / ((n : ℝ) + 1)) / 2 * ‖(2 : ℕ) • innerSL ℝ x‖
          ≤ (1 / ((n : ℝ) + 1)) / 2 * (2 * ‖x‖) := by gcongr
        _ = (1 / ((n : ℝ) + 1)) * ‖x‖ := by ring
    have h5 : (1 / ((n : ℝ) + 1)) * ‖x‖ ≤ δ / 2 := by
      have hN : 2 * max R 0 / δ < (n : ℝ) := lt_of_lt_of_le hN₂ (by exact_mod_cast hn2)
      have hxR : ‖x‖ ≤ max R 0 := hx.trans (le_max_left _ _)
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hδ] at hN
      nlinarith [norm_nonneg x]
    linarith
  calc ‖Q + fderiv ℝ (CutoffRigidity.NoBm.molc n V) x - fderiv ℝ V x‖
      = ‖Q + (fderiv ℝ (CutoffRigidity.NoBm.molc n V) x - fderiv ℝ V x)‖ := by congr 1; abel
    _ ≤ ‖Q‖ + ‖fderiv ℝ (CutoffRigidity.NoBm.molc n V) x - fderiv ℝ V x‖ := norm_add_le _ _
    _ ≤ δ := by linarith

end Props

end C2U

end CutCur
