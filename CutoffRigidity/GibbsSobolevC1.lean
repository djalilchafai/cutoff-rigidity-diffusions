module
public import CutoffRigidity.GibbsCompactWeakH1

/-! # Actual global C¹ functions in the closed weighted H¹ domain

Compact C¹ lifts and a genuine smooth cutoff exhaustion prove the full
first-order statement at exactly the regularity needed for Langevin
backward functions. No Sobolev membership premise is introduced.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem compact_c1_function_mem_closedGibbsGradient_graph {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hfLp : MemLp f 2 (gibbsMeasure volume V))
    (hgLp : MemLp (gradient f) 2 (gibbsMeasure volume V)) :
    (hfLp.toLp f, hgLp.toLp (gradient f)) ∈ (closedGibbsGradient hV hprob).graph := by
  obtain ⟨v, hv, hD⟩ := exists_gibbsSobolev_of_compact_c1 hV hprob ρ hρ hHess hf hfc
  have hveq : gibbsSobolevInclusion hV hprob v = hfLp.toLp f :=
    Lp.ext (hv.trans hfLp.coeFn_toLp.symm)
  have hDeq : gibbsSobolevDerivative hV hprob v = hgLp.toLp (gradient f) :=
    Lp.ext (hD.trans hgLp.coeFn_toLp.symm)
  rw [← hveq, ← hDeq]
  exact v.property

/-- Actual global C¹ regularity and genuine function/gradient L²
integrability suffice for the closed weighted H¹ graph. -/
theorem c1_function_mem_closedGibbsGradient_graph {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hf : ContDiff ℝ 1 f) (hfLp : MemLp f 2 (gibbsMeasure volume V))
    (hgLp : MemLp (gradient f) 2 (gibbsMeasure volume V)) :
    (hfLp.toLp f, hgLp.toLp (gradient f)) ∈ (closedGibbsGradient hV hprob).graph := by
  let μ := gibbsMeasure volume V
  let := hprob
  obtain ⟨C, hC0, χ, hχ, hχc, hχbounds, hχone, hχgrad⟩ := exists_smooth_cutoff_exhaustion (d := d)
  let fn (n : ℕ) (x : E) := χ n x ^ 2 * f x
  have hfn (n : ℕ) : ContDiff ℝ 1 (fn n) :=
    (((hχ n).of_le (by norm_num) : ContDiff ℝ 1 (χ n)).pow 2).mul hf
  have hfnc (n : ℕ) : HasCompactSupport (fn n) := by
    have hc := (hχc n).comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    simpa only [fn, Pi.mul_def, Function.comp_def] using hc.mul_right (f' := f)
  have hfnLp (n : ℕ) : MemLp (fn n) 2 μ := (hfn n).continuous.memLp_of_hasCompactSupport (hfnc n)
  have hGfn (n : ℕ) : Continuous (gradient (fn n)) :=
    continuous_gradient_of_c1 ((hfn n).of_le (by norm_num))
  have hgfnLp (n : ℕ) : MemLp (gradient (fn n)) 2 μ := by
    have hc := ((hfnc n).fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ E).symm) (by simp)
    exact (hGfn n).memLp_of_hasCompactSupport hc
  have hcLim : Tendsto (fun n : ℕ => C / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp hden).const_mul C
  have hGχlim (x : E) : Tendsto (fun n => gradient (χ n) x) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => hχgrad n x) hcLim
  have hχlim (x : E) : Tendsto (fun n => χ n x) atTop (𝓝 1) :=
    tendsto_const_nhds.congr' ((hχone x).mono (fun n hn => hn.symm))
  have hGχbound (n : ℕ) (x : E) : ‖gradient (χ n) x‖ ≤ C := by
    apply (hχgrad n x).trans
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hsqχ (n : ℕ) (x : E) : 0 ≤ χ n x ^ 2 ∧ χ n x ^ 2 ≤ 1 := by
    have hb := hχbounds n x
    exact ⟨sq_nonneg _, by nlinarith⟩
  have hflim : Tendsto (fun n => (hfnLp n).toLp (fn n)) atTop (𝓝 (hfLp.toLp f)) := by
    apply tendsto_toL2_of_dominated_sq hfLp hfnLp (fun x => ‖f x‖ ^ 2) hfLp.norm.integrable_sq
    · intro n
      filter_upwards with x
      have hb := hsqχ n x
      dsimp only [fn]
      rw [Real.norm_eq_abs]
      have heq : χ n x ^ 2 * f x - f x = (χ n x ^ 2 - 1) * f x := by ring
      rw [heq, abs_mul, mul_pow, sq_abs, sq_abs]
      have hcoef : (χ n x ^ 2 - 1) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (χ n x ^ 2)]
      calc
        _ ≤ 1 * f x ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
        _ = _ := by simp [Real.norm_eq_abs]
    · filter_upwards with x
      simpa only [fn, one_pow, one_mul] using ((hχlim x).pow 2).mul_const (f x)
  have hgradformula (n : ℕ) (x : E) : gradient (fn n) x =
      χ n x ^ 2 • gradient f x + (2 * χ n x * f x) • gradient (χ n) x :=
    gradient_cutoff_square_mul ((hχ n).differentiable (by norm_num)) (hf.differentiable (by norm_num)) x
  have hglim : Tendsto (fun n => (hgfnLp n).toLp (gradient (fn n))) atTop
      (𝓝 (hgLp.toLp (gradient f))) := by
    let bound (x : E) := 2 * ‖gradient f x‖ ^ 2 + 8 * C ^ 2 * ‖f x‖ ^ 2
    have hboundInt : Integrable bound μ :=
      (hgLp.norm.integrable_sq.const_mul 2).add (hfLp.norm.integrable_sq.const_mul (8 * C ^ 2))
    apply tendsto_toL2_of_dominated_sq hgLp hgfnLp bound hboundInt
    · intro n
      filter_upwards with x
      have hb := hχbounds n x
      have hs := hsqχ n x
      have hA : |χ n x ^ 2 - 1| ≤ 1 := by rw [abs_of_nonpos (by linarith)]; linarith
      have hB : |2 * χ n x * f x| ≤ 2 * |f x| := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg hb.1]
        nlinarith [abs_nonneg (f x)]
      have heq : gradient (fn n) x - gradient f x =
          (χ n x ^ 2 - 1) • gradient f x + (2 * χ n x * f x) • gradient (χ n) x := by
        rw [hgradformula]
        module
      have hn : ‖gradient (fn n) x - gradient f x‖ ≤ ‖gradient f x‖ + 2 * C * ‖f x‖ := by
        rw [heq]
        calc
          _ ≤ ‖(χ n x ^ 2 - 1) • gradient f x‖ + ‖(2 * χ n x * f x) • gradient (χ n) x‖ := norm_add_le _ _
          _ = |χ n x ^ 2 - 1| * ‖gradient f x‖ + |2 * χ n x * f x| * ‖gradient (χ n) x‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
          _ ≤ 1 * ‖gradient f x‖ + (2 * |f x|) * C := by gcongr; exact hGχbound n x
          _ = _ := by rw [Real.norm_eq_abs]; ring
      have hf0 := norm_nonneg (f x)
      have hg0 := norm_nonneg (gradient f x)
      have hn0 := norm_nonneg (gradient (fn n) x - gradient f x)
      dsimp only [bound]
      nlinarith [sq_nonneg (‖gradient f x‖ - 2 * C * ‖f x‖)]
    · filter_upwards with x
      have hh := (((hχlim x).pow 2).smul (tendsto_const_nhds (x := gradient f x))).add
        ((((hχlim x).const_mul 2).mul_const (f x)).smul (hGχlim x))
      simpa only [hgradformula, one_pow, one_smul, smul_zero, add_zero] using hh
  have hpairlim := hflim.prodMk_nhds hglim
  apply (closedGibbsGradient_isClosed hV hprob).mem_of_tendsto hpairlim
  exact Filter.Eventually.of_forall (fun n => compact_c1_function_mem_closedGibbsGradient_graph
    hV hprob ρ hρ hHess (hfn n) (hfnc n) (hfnLp n) (hgfnLp n))


@[expose] noncomputable def c1GibbsSobolevLift {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hf : ContDiff ℝ 1 f) (hfLp : MemLp f 2 (gibbsMeasure volume V))
    (hgLp : MemLp (gradient f) 2 (gibbsMeasure volume V)) : gibbsSobolevGraph hV hprob :=
  ⟨WithLp.toLp 2 (hfLp.toLp f, hgLp.toLp (gradient f)),
    c1_function_mem_closedGibbsGradient_graph hV hprob ρ hρ hHess hf hfLp hgLp⟩

theorem c1GibbsSobolevLift_inclusion {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hf : ContDiff ℝ 1 f) (hfLp : MemLp f 2 (gibbsMeasure volume V))
    (hgLp : MemLp (gradient f) 2 (gibbsMeasure volume V)) :
    gibbsSobolevInclusion hV hprob (c1GibbsSobolevLift hV hprob ρ hρ hHess hf hfLp hgLp) = hfLp.toLp f := rfl

theorem c1GibbsSobolevLift_derivative {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hf : ContDiff ℝ 1 f) (hfLp : MemLp f 2 (gibbsMeasure volume V))
    (hgLp : MemLp (gradient f) 2 (gibbsMeasure volume V)) :
    gibbsSobolevDerivative hV hprob (c1GibbsSobolevLift hV hprob ρ hρ hHess hf hfLp hgLp) =
      hgLp.toLp (gradient f) := rfl

/-- In particular bounded C¹ functions with bounded actual gradients have
true global Gibbs H¹ lifts for the actual probability measure. -/
theorem exists_gibbsSobolev_of_bounded_c1 {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hf : ContDiff ℝ 1 f) (M N : ℝ) (hM : ∀ x, ‖f x‖ ≤ M) (hN : ∀ x, ‖gradient f x‖ ≤ N) :
    ∃ v : gibbsSobolevGraph hV hprob,
      (gibbsSobolevInclusion hV hprob v =ᵐ[gibbsMeasure volume V] f) ∧
      (gibbsSobolevDerivative hV hprob v =ᵐ[gibbsMeasure volume V] gradient f) := by
  let := hprob
  have hfLp : MemLp f 2 (gibbsMeasure volume V) :=
    MemLp.of_bound hf.continuous.aestronglyMeasurable M (Eventually.of_forall hM)
  have hgLp : MemLp (gradient f) 2 (gibbsMeasure volume V) :=
    MemLp.of_bound (continuous_gradient_of_c1 hf).aestronglyMeasurable N (Eventually.of_forall hN)
  exact ⟨c1GibbsSobolevLift hV hprob ρ hρ hHess hf hfLp hgLp, hfLp.coeFn_toLp, hgLp.coeFn_toLp⟩

end CutoffRigidity
