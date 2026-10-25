module
public import CutoffRigidity.GibbsSobolevC1
public import CutoffRigidity.SalezEntropyWindow
public import CutoffRigidity.GaussianAverageGenerator

/-! # Extending genuine compact-test Poincare bounds

Actual smooth bump convolution approximates a compact C¹ function and all
its first derivatives under any finite Euclidean Borel measure. Smooth
spatial cutoffs then extend the inequality to its full C¹ L² energy domain.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal Convolution
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- On a compact C¹ input the classical derivative of the true smoothing
is the smoothing of the classical derivative. -/
theorem gradient_bumpMollification_coordinate {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (φ : ContDiffBump (0 : E)) (j : Fin d) (x : E) :
    gradient (bumpMollification φ f) x j =
      bumpMollification φ (fun y => gradient f y j) x := by
  rw [← fderiv_single_eq_gradient_coordinate]
  apply coordinateDerivative_bumpMollification_of_weak_derivative φ hf.continuous.locallyIntegrable
    (((EuclideanSpace.proj j).continuous.comp (continuous_gradient_of_c1 hf)).locallyIntegrable) j
  exact fun ψ hψ hψc => compact_c1_volume_weak_derivative hf hfc j ψ hψ hψc

/-- Genuine probability convolution preserves a uniform scalar bound. -/
theorem norm_bumpMollification_le (φ : ContDiffBump (0 : E))
    {f : E → ℝ} (M : ℝ) (hM : ∀ x, ‖f x‖ ≤ M) (x : E) :
    ‖bumpMollification φ f x‖ ≤ M := by
  rw [← bumpProbability_integral_eq_convolution]
  exact (norm_integral_le_of_norm_le_const (Eventually.of_forall (fun y => hM (x-y)))).trans_eq (by simp)

set_option maxHeartbeats 700000 in
/-- A compact C² Poincare inequality extends to compact C¹ functions for
any actual finite Borel measure, without a density assumption on the measure. -/
theorem compact_c1_poincare_of_compact_c2
    (μ : Measure E) [IsFiniteMeasure μ] (C : ℝ)
    (hP : ∀ f : E → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
      (∫ x, f x^2 ∂μ) - (∫ x, f x ∂μ)^2 ≤ C * ∫ x, ‖gradient f x‖^2 ∂μ)
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    (∫ x, f x^2 ∂μ) - (∫ x, f x ∂μ)^2 ≤ C * ∫ x, ‖gradient f x‖^2 ∂μ := by
  let ε := fun n : ℕ => 1 / ((n : ℝ)+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  let φ : ℕ → ContDiffBump (0 : E) := fun n : ℕ => euclideanMollifierBump (ε n) (hε n)
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let fn := fun n : ℕ => bumpMollification (φ n) f
  have hfn (n : ℕ) : ContDiff ℝ 2 (fn n) :=
    (bumpMollification_contDiff (φ n) hf.continuous.locallyIntegrable).of_le (by norm_num)
  have hfnc (n : ℕ) : HasCompactSupport (fn n) := bumpMollification_hasCompactSupport (φ n) hfc
  obtain ⟨M,hM0,hM⟩ := compact_continuous_norm_bound hf.continuous hfc
  have hgradc : HasCompactSupport (gradient f) :=
    (hfc.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ E).symm) (by simp)
  obtain ⟨G,hG0,hG⟩ := compact_continuous_norm_bound (continuous_gradient_of_c1 hf) hgradc
  have hvalue (n : ℕ) (x : E) : ‖fn n x‖ ≤ M := norm_bumpMollification_le (φ n) M hM x
  have hcoord (n : ℕ) (x : E) (j : Fin d) : ‖gradient (fn n) x j‖ ≤ G := by
    rw [gradient_bumpMollification_coordinate hf hfc]
    exact norm_bumpMollification_le (φ n) G
      (fun y => (PiLp.norm_apply_le (gradient f y) j).trans (hG y)) x
  have hgrad (n : ℕ) (x : E) : ‖gradient (fn n) x‖^2 ≤ (d : ℝ)*G^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ j : Fin d, G^2 := Finset.sum_le_sum (fun j _ => by
        simpa only [Real.norm_eq_abs, sq_abs] using
          pow_le_pow_left₀ (norm_nonneg _) (hcoord n x j) 2)
      _ = _ := by simp
  have hflim (x : E) : Tendsto (fun n => fn n x) atTop (𝓝 (f x)) :=
    ContDiffBump.convolution_tendsto_right_of_continuous hφ hf.continuous x
  have hglim (x : E) : Tendsto (fun n => gradient (fn n) x) atTop (𝓝 (gradient f x)) := by
    have hh : Tendsto (fun n => fun j : Fin d => gradient (fn n) x j) atTop
        (𝓝 (fun j : Fin d => gradient f x j)) := by
      apply tendsto_pi_nhds.mpr
      intro j
      change Tendsto (fun n => gradient (bumpMollification (φ n) f) x j) atTop _
      simp_rw [gradient_bumpMollification_coordinate hf hfc]
      exact ContDiffBump.convolution_tendsto_right_of_continuous hφ
        ((EuclideanSpace.proj j).continuous.comp (continuous_gradient_of_c1 hf)) x
    exact ((PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).tendsto _).comp hh
  have hIntF : Tendsto (fun n => ∫ x, fn n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => M)
      (fun n => (hfn n).continuous.aestronglyMeasurable) (integrable_const M)
      (fun n => Eventually.of_forall (hvalue n)) (Eventually.of_forall hflim)
  have hIntSq : Tendsto (fun n => ∫ x, fn n x^2 ∂μ) atTop (𝓝 (∫ x, f x^2 ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => M^2)
      (fun n => ((hfn n).continuous.pow 2).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall (fun x => ?_)) (Eventually.of_forall (fun x => (hflim x).pow 2))
    simp only [Pi.pow_apply]
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hvalue n x) 2
  have hIntGrad : Tendsto (fun n => ∫ x, ‖gradient (fn n) x‖^2 ∂μ) atTop
      (𝓝 (∫ x, ‖gradient f x‖^2 ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (d : ℝ)*G^2)
      (fun n => ((continuous_gradient_of_c1 ((hfn n).of_le (by norm_num))).norm.pow 2).aestronglyMeasurable)
      (integrable_const _) (fun n => Eventually.of_forall (fun x => ?_))
      (Eventually.of_forall (fun x => (hglim x).norm.pow 2))
    change ‖‖gradient (fn n) x‖^2‖ ≤ _
    rw [Real.norm_of_nonneg (sq_nonneg ‖gradient (fn n) x‖)]
    exact hgrad n x
  exact le_of_tendsto_of_tendsto (hIntSq.sub (hIntF.pow 2)) (hIntGrad.const_mul C)
    (Eventually.of_forall (fun n => hP (fn n) (hfn n) (hfnc n)))


set_option maxHeartbeats 900000 in
/-- Smooth spatial cutoffs extend the actual inequality to every C¹
function with finite L² value and finite gradient energy. -/
theorem c1_poincare_of_compact_c2
    (μ : Measure E) [IsProbabilityMeasure μ] (C : ℝ)
    (hP : ∀ f : E → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
      (∫ x, f x^2 ∂μ) - (∫ x, f x ∂μ)^2 ≤ C * ∫ x, ‖gradient f x‖^2 ∂μ) :
    HasLocalSmoothPoincare μ C := by
  intro f hf hfLp hGI
  obtain ⟨K,hK0,χ,hχ,hχc,hχbounds,hχone,hχgrad⟩ := exists_smooth_cutoff_exhaustion (d := d)
  let fn := fun n : ℕ => fun x : E => χ n x^2 * f x
  have hfn (n : ℕ) : ContDiff ℝ 1 (fn n) :=
    (((hχ n).of_le (by norm_num) : ContDiff ℝ 1 (χ n)).pow 2).mul hf
  have hfnc (n : ℕ) : HasCompactSupport (fn n) := by
    have hc := (hχc n).comp_left (g := fun t : ℝ => t^2) (by simp)
    simpa only [fn,Pi.mul_def,Function.comp_def] using hc.mul_right (f' := f)
  have hχlim (x : E) : Tendsto (fun n => χ n x) atTop (𝓝 1) :=
    tendsto_const_nhds.congr' ((hχone x).mono (fun n hn => hn.symm))
  have hcLim : Tendsto (fun n : ℕ => K / ((n : ℝ)+1)) atTop (𝓝 0) := by
    have hden : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp hden).const_mul K
  have hGχlim (x : E) : Tendsto (fun n => gradient (χ n) x) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => hχgrad n x) hcLim
  have hGχbound (n : ℕ) (x : E) : ‖gradient (χ n) x‖ ≤ K := by
    apply (hχgrad n x).trans
    apply (div_le_iff₀ (by positivity : (0:ℝ) < n+1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hvalue (n : ℕ) (x : E) : ‖fn n x‖ ≤ ‖f x‖ := by
    have hb := hχbounds n x
    change ‖χ n x^2*f x‖ ≤ _
    rw [norm_mul,norm_pow,Real.norm_eq_abs,sq_abs]
    have hs : χ n x^2 ≤ 1 := by nlinarith
    exact (mul_le_mul_of_nonneg_right hs (norm_nonneg _)).trans_eq (one_mul _)
  have hflim (x : E) : Tendsto (fun n => fn n x) atTop (𝓝 (f x)) := by
    simpa only [fn,one_pow,one_mul] using ((hχlim x).pow 2).mul_const (f x)
  have hgradformula (n : ℕ) (x : E) : gradient (fn n) x =
      χ n x^2 • gradient f x + (2*χ n x*f x) • gradient (χ n) x :=
    gradient_cutoff_square_mul ((hχ n).differentiable (by norm_num)) (hf.differentiable (by norm_num)) x
  have hglim (x : E) : Tendsto (fun n => gradient (fn n) x) atTop (𝓝 (gradient f x)) := by
    have hh := (((hχlim x).pow 2).smul (tendsto_const_nhds (x := gradient f x))).add
      ((((hχlim x).const_mul 2).mul_const (f x)).smul (hGχlim x))
    simpa only [hgradformula,one_pow,one_smul,smul_zero,add_zero] using hh
  have hgrad (n : ℕ) (x : E) : ‖gradient (fn n) x‖^2 ≤
      2*‖gradient f x‖^2 + 8*K^2*‖f x‖^2 := by
    have hb := hχbounds n x
    have hA : |χ n x^2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg _)]; nlinarith
    have hB : |2*χ n x*f x| ≤ 2*|f x| := by
      rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_nonneg hb.1]
      nlinarith [abs_nonneg (f x)]
    have hn : ‖gradient (fn n) x‖ ≤ ‖gradient f x‖ + 2*K*‖f x‖ := by
      rw [hgradformula]
      calc
        _ ≤ ‖χ n x^2 • gradient f x‖ + ‖(2*χ n x*f x) • gradient (χ n) x‖ := norm_add_le _ _
        _ = |χ n x^2| *‖gradient f x‖ + |2*χ n x*f x| *‖gradient (χ n) x‖ := by
          rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
        _ ≤ 1*‖gradient f x‖ + (2*|f x|)*K := by gcongr; exact hGχbound n x
        _ = _ := by rw [Real.norm_eq_abs]; ring
    nlinarith [norm_nonneg (gradient (fn n) x),norm_nonneg (gradient f x),norm_nonneg (f x),
      sq_nonneg (‖gradient f x‖-2*K*‖f x‖)]
  have hIntF : Tendsto (fun n => ∫ x, fn n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
    exact tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
      (fun n => (hfn n).continuous.aestronglyMeasurable) (hfLp.integrable (by norm_num)).norm
      (fun n => Eventually.of_forall (hvalue n)) (Eventually.of_forall hflim)
  have hIntSq : Tendsto (fun n => ∫ x, fn n x^2 ∂μ) atTop (𝓝 (∫ x, f x^2 ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖^2)
      (fun n => ((hfn n).continuous.pow 2).aestronglyMeasurable) hfLp.norm.integrable_sq
      (fun n => Eventually.of_forall (fun x => ?_)) (Eventually.of_forall (fun x => (hflim x).pow 2))
    simp only [Pi.pow_apply]
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hvalue n x) 2
  have hIntGrad : Tendsto (fun n => ∫ x, ‖gradient (fn n) x‖^2 ∂μ) atTop
      (𝓝 (∫ x, ‖gradient f x‖^2 ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => 2*‖gradient f x‖^2+8*K^2*‖f x‖^2)
      (fun n => ((continuous_gradient_of_c1 (hfn n)).norm.pow 2).aestronglyMeasurable)
      ((hGI.const_mul 2).add (hfLp.norm.integrable_sq.const_mul (8*K^2)))
      (fun n => Eventually.of_forall (fun x => ?_)) (Eventually.of_forall (fun x => (hglim x).norm.pow 2))
    change ‖‖gradient (fn n) x‖^2‖ ≤ _
    rw [Real.norm_of_nonneg (sq_nonneg ‖gradient (fn n) x‖)]
    exact hgrad n x
  rw [variance_eq_sub hfLp]
  exact le_of_tendsto_of_tendsto (hIntSq.sub (hIntF.pow 2)) (hIntGrad.const_mul C)
    (Eventually.of_forall (fun n => compact_c1_poincare_of_compact_c2 μ C hP (hfn n) (hfnc n)))

end CutoffRigidity
