module
public import CutoffRigidity.HopfLaxDerivatives
public import CutoffRigidity.LipschitzWeakGradient
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! # Genuine regularity of the Hamilton–Jacobi exponential curve -/
public section
namespace CutoffRigidity
open Set MeasureTheory Filter
open scoped Topology NNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- On each positive compact time interval, all actual exponential
Hopf–Lax curves have a common finite Lipschitz bound independent of x. -/
theorem exists_uniform_lipschitzOnWith_exp_hopfLax {a b M ρ : ℝ}
    (ha : 0 < a) (hab : a < b) (hρ : 0 ≤ ρ)
    {f : E → ℝ} (hf : ∀ x, |f x| ≤ M) {L : NNReal} (hL : LipschitzWith L f) :
    ∃ C : NNReal, ∀ x : E, LipschitzOnWith C
      (fun t : ℝ => Real.exp (ρ*t*hopfLax t f x)) (Ioo a b) := by
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hf 0)
  have hb : 0 < b := ha.trans hab
  let Ct := 2*M/a
  let K := ρ*b*Ct+ρ*M
  let R := ρ*b*M
  have hCt : 0 ≤ Ct := by dsimp only [Ct]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨⟨Real.exp R*K,mul_nonneg (Real.exp_nonneg _) hK⟩,?_⟩
  intro x
  have htime := lipschitzOnWith_hopfLax_time ha hf hL.continuous x
  have hBound (t : ℝ) (ht : t ∈ Ioo a b) : |hopfLax t f x| ≤ M := by
    have hh := hopfLax_bounds (ha.trans ht.1).le hf x
    exact abs_le.mpr ⟨hh.1,hh.2.trans (abs_le.mp (hf x)).2⟩
  have hPsi (s t : ℝ) (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) :
      ‖ρ*s*hopfLax s f x-ρ*t*hopfLax t f x‖ ≤ K*‖s-t‖ := by
    have hQt := htime.dist_le_mul s hs.1 t ht.1
    simp only [dist_eq_norm,Real.norm_eq_abs] at hQt
    have hEq : ρ*s*hopfLax s f x-ρ*t*hopfLax t f x =
        ρ*s*(hopfLax s f x-hopfLax t f x)+ρ*(s-t)*hopfLax t f x := by ring
    have hsN : ‖s‖ ≤ b := by rw [Real.norm_eq_abs,abs_of_pos (ha.trans hs.1)]; exact hs.2.le
    have htN : ‖hopfLax t f x‖ ≤ M := by simpa only [Real.norm_eq_abs] using hBound t ht
    have hdiff : ‖hopfLax s f x-hopfLax t f x‖ ≤ Ct*‖s-t‖ := by
      change |hopfLax s f x-hopfLax t f x| ≤ (2*M/a)*|s-t| at hQt
      simpa only [Real.norm_eq_abs] using hQt
    rw [hEq]
    calc
      _ ≤ ‖ρ*s*(hopfLax s f x-hopfLax t f x)‖+‖ρ*(s-t)*hopfLax t f x‖ := norm_add_le _ _
      _ = ρ*‖s‖*‖hopfLax s f x-hopfLax t f x‖+ρ*‖s-t‖*‖hopfLax t f x‖ := by
        simp only [norm_mul,Real.norm_of_nonneg hρ]
      _ ≤ ρ*b*(Ct*‖s-t‖)+ρ*‖s-t‖*M := by gcongr
      _ = K*‖s-t‖ := by dsimp only [K]; ring
  have hRange (t : ℝ) (ht : t ∈ Ioo a b) : ρ*t*hopfLax t f x ≤ R := by
    have htf := (abs_le.mp (hBound t ht)).2
    calc
      _ ≤ ρ*t*M := mul_le_mul_of_nonneg_left htf (mul_nonneg hρ (ha.trans ht.1).le)
      _ ≤ ρ*b*M := by gcongr; exact ht.2.le
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  have he := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z (_hz : z ∈ Iic R) => Real.differentiableAt_exp)
    (fun z (hz : z ∈ Iic R) => by
      rw [Real.deriv_exp,Real.norm_of_nonneg (Real.exp_nonneg _)]
      exact Real.exp_le_exp.mpr hz)
    (convex_Iic R) (hRange s hs) (hRange t ht)
  change ‖Real.exp (ρ*s*hopfLax s f x)-Real.exp (ρ*t*hopfLax t f x)‖ ≤ (Real.exp R*K)*‖s-t‖
  rw [norm_sub_rev] at he
  have hm := mul_le_mul_of_nonneg_left (hPsi t s ht hs) (Real.exp_nonneg R)
  rw [norm_sub_rev t s] at hm
  exact he.trans (by simpa only [mul_assoc] using hm)

/-- Differentiation of the genuine Hamilton–Jacobi exponential integral.
The pointwise derivative premise is supplied a.e. in time by the actual
Hopf–Lax theorem, rather than postulated as a PDE in source hypotheses. -/
theorem hasDerivAt_integral_exp_hopfLax_of_ae_hasDerivAt
    (μ : Measure E) [IsProbabilityMeasure μ] {ρ M t : ℝ} (hρ : 0 ≤ ρ) (ht : 0 < t)
    {f : E → ℝ} (hf : ∀ x, |f x| ≤ M) {L : NNReal} (hL : LipschitzWith L f)
    (hTime : ∀ᵐ x ∂μ, HasDerivAt (fun s => hopfLax s f x) (-‖gradient (hopfLax t f) x‖^2/2) t) :
    HasDerivAt (fun s => ∫ x,Real.exp (ρ*s*hopfLax s f x) ∂μ)
      (∫ x,Real.exp (ρ*t*hopfLax t f x)*
        (ρ*hopfLax t f x-ρ*t*‖gradient (hopfLax t f) x‖^2/2) ∂μ) t := by
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hf 0)
  obtain ⟨C,hC⟩ := exists_uniform_lipschitzOnWith_exp_hopfLax
    (show 0 < t/2 by linarith) (show t/2 < t+1 by linarith) hρ hf hL
  have hQCont := (lipschitzWith_hopfLax ht.le hf hL).continuous
  have hFD : AEStronglyMeasurable (fun x => Real.exp (ρ*t*hopfLax t f x)*
      (ρ*hopfLax t f x-ρ*t*‖gradient (hopfLax t f) x‖^2/2)) μ := by
    exact (((Real.continuous_exp.comp (hQCont.const_mul (ρ*t))).measurable).mul
      (((hQCont.const_mul ρ).measurable).sub
        (((measurable_euclidean_gradient (hopfLax t f)).norm.pow_const 2).const_mul (ρ*t) |>.div_const 2))).aestronglyMeasurable
  have hFI : Integrable (fun x => Real.exp (ρ*t*hopfLax t f x)) μ := by
    apply (integrable_const (Real.exp (ρ*t*M))).mono' (Real.continuous_exp.comp (hQCont.const_mul (ρ*t))).aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    change ‖Real.exp (ρ*t*hopfLax t f x)‖ ≤ Real.exp (ρ*t*M)
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left ((hopfLax_bounds ht.le hf x).2.trans (abs_le.mp (hf x)).2) (by positivity)
  have hFMeas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (fun x => Real.exp (ρ*s*hopfLax s f x)) μ := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact (Real.continuous_exp.comp ((lipschitzWith_hopfLax hs.le hf hL).continuous.const_mul (ρ*s))).aestronglyMeasurable
  apply (hasDerivAt_integral_of_dominated_loc_of_lip (μ := μ)
    (bound := fun _ => (C:ℝ)) (s := Ioo (t/2) (t+1))
    (Ioo_mem_nhds (by linarith) (by linarith)) hFMeas hFI hFD
    (Eventually.of_forall (fun x => by simpa using hC x)) (integrable_const (C:ℝ)) ?_).2
  filter_upwards [hTime] with x hx
  have hh := (((hasDerivAt_id t).mul hx).const_mul ρ).exp
  convert hh using 1
  · funext s; simp only [Pi.mul_apply,id_eq,mul_assoc]
  · simp only [Pi.mul_apply,id_eq,mul_assoc]; ring

/-- The actual exponential integral has its genuine Hamilton–Jacobi time
derivative almost everywhere. All derivative, regularity, and domination
conditions are derived from the bounded Lipschitz test. -/
theorem hasDerivAt_integral_exp_hopfLax_ae
    (μ : Measure E) [IsProbabilityMeasure μ] (hμ : μ ≪ volume)
    {ρ a M : ℝ} (hρ : 0 ≤ ρ) (ha : 0 < a)
    {f : E → ℝ} (hf : ∀ x, |f x| ≤ M) {L : NNReal} (hL : LipschitzWith L f) :
    ∀ᵐ t ∂volume.restrict (Ioi a),
      HasDerivAt (fun s => ∫ x,Real.exp (ρ*s*hopfLax s f x) ∂μ)
        (∫ x,Real.exp (ρ*t*hopfLax t f x)*
          (ρ*hopfLax t f x-ρ*t*‖gradient (hopfLax t f) x‖^2/2) ∂μ) t := by
  filter_upwards [hopfLax_hasDerivAt_ae_of_absolutelyContinuous ha hf hL μ hμ,
    ae_restrict_mem measurableSet_Ioi] with t hTime ht
  exact hasDerivAt_integral_exp_hopfLax_of_ae_hasDerivAt μ hρ (ha.trans ht) hf hL hTime

end CutoffRigidity
