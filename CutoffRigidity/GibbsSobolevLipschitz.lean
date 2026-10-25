module
public import CutoffRigidity.LipschitzWeakGradient

/-! # Bounded Lipschitz functions in the genuine Gibbs H¹ domain

Smooth spatial cutoffs and actual compact weak-gradient mollification
identify the closed gradient with the actual Rademacher gradient.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem gradient_cutoff_square_mul_at {χ f : E → ℝ} {x : E}
    (hχ : DifferentiableAt ℝ χ x) (hf : DifferentiableAt ℝ f x) :
    gradient (fun y => χ y^2*f y) x =
      χ x^2 • gradient f x + (2*χ x*f x) • gradient χ x := by
  apply ext_inner_right ℝ
  intro y
  have hc : DifferentiableAt ℝ (fun y => χ y^2) x := hχ.pow 2
  rw [inner_gradient_left,fderiv_fun_mul hc hf,fderiv_fun_pow 2 hχ]
  simp only [add_apply,smul_apply,smul_eq_mul,inner_add_left,inner_smul_left,
    inner_gradient_left,Nat.reduceSub,pow_one,nsmul_eq_mul]
  simp only [map_mul,map_pow,RCLike.conj_to_real,Nat.cast_ofNat]
  ring

/-- Product estimate used only for actual bounded Lipschitz cutoffs. -/
theorem bounded_real_lipschitz_mul {f g : E → ℝ} {L K : ℝ≥0}
    (hf : LipschitzWith L f) (hg : LipschitzWith K g)
    (M N : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hfB : ∀ x, ‖f x‖ ≤ M) (hgB : ∀ x, ‖g x‖ ≤ N) :
    LipschitzWith (Real.toNNReal (M*K+N*L)) (fun x => f x*g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.coe_toNNReal _ (by positivity)]
  simp only [dist_eq_norm]
  calc
    ‖f x*g x-f y*g y‖ = ‖f x*(g x-g y)+(f x-f y)*g y‖ := by congr 1; ring
    _ ≤ ‖f x‖*‖g x-g y‖+‖f x-f y‖*‖g y‖ := by
      exact (norm_add_le _ _).trans_eq (by rw [norm_mul,norm_mul])
    _ ≤ M*(K*‖x-y‖)+(L*‖x-y‖)*N := by
      gcongr
      · exact hfB x
      · exact hg.norm_sub_le x y
      · exact hf.norm_sub_le x y
      · exact hgB y
    _ = _ := by ring

set_option maxHeartbeats 1200000 in
theorem bounded_lipschitz_function_mem_closedGibbsGradient_graph {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (L : ℝ≥0) (hf : LipschitzWith L f)
    (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ x, ‖f x‖ ≤ M) (hfLp : MemLp f 2 (gibbsMeasure volume V))
    (hgLp : MemLp (gradient f) 2 (gibbsMeasure volume V)) :
    (hfLp.toLp f, hgLp.toLp (gradient f)) ∈ (closedGibbsGradient hV hprob).graph := by
  let μ := gibbsMeasure volume V
  let := hprob
  obtain ⟨C, hC0, χ, hχ, hχc, hχbounds, hχone, hχgrad⟩ := exists_smooth_cutoff_exhaustion (d := d)
  let fn (n : ℕ) (x : E) := χ n x ^ 2 * f x
  have hC : 0 ≤ C := hC0
  have hsqLip (n : ℕ) : LipschitzWith (Real.toNNReal (2*C)) (fun x => χ n x^2) := by
    apply lipschitzWith_of_nnnorm_fderiv_le (((hχ n).pow 2).differentiable (by norm_num))
    intro x
    change ‖fderiv ℝ (fun y => χ n y^2) x‖ ≤ (Real.toNNReal (2*C) : ℝ)
    rw [Real.coe_toNNReal _ (by positivity),fderiv_fun_pow 2 ((hχ n).differentiable (by norm_num) x)]
    simp only [Nat.reduceSub,pow_one,nsmul_eq_mul,norm_smul,Real.norm_eq_abs,abs_mul,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),abs_of_nonneg (hχbounds n x).1]
    have hg : ‖fderiv ℝ (χ n) x‖ ≤ C := by
      have he : ‖gradient (χ n) x‖ = ‖fderiv ℝ (χ n) x‖ :=
        (InnerProductSpace.toDual ℝ E).symm.norm_map _
      rw [← he]
      apply (hχgrad n x).trans
      apply (div_le_iff₀ (by positivity : (0:ℝ)<n+1)).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    norm_num at ⊢
    nlinarith [(hχbounds n x).1,(hχbounds n x).2,norm_nonneg (fderiv ℝ (χ n) x)]
  have hfnLip (n : ℕ) : ∃ K, LipschitzWith K (fn n) := by
    refine ⟨_,bounded_real_lipschitz_mul (hsqLip n) hf 1 M zero_le_one hM ?_ hBound⟩
    intro x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hb := hχbounds n x
    nlinarith
  have hfn (n : ℕ) : Continuous (fn n) := ((hfnLip n).choose_spec).continuous
  have hfnc (n : ℕ) : HasCompactSupport (fn n) := by
    have hc := (hχc n).comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    simpa only [fn, Pi.mul_def, Function.comp_def] using hc.mul_right (f' := f)
  have hfnLp (n : ℕ) : MemLp (fn n) 2 μ := (hfn n).memLp_of_hasCompactSupport (hfnc n)
  have hgfnLp (n : ℕ) : MemLp (gradient (fn n)) 2 μ := by
    apply MemLp.of_bound (measurable_euclidean_gradient (fn n)).aestronglyMeasurable
      ((hfnLip n).choose : ℝ)
    exact Eventually.of_forall (norm_gradient_le_of_lipschitz (hfnLip n).choose_spec)
  have hDiff : ∀ᵐ x ∂μ, DifferentiableAt ℝ f x :=
    (gibbsMeasure_absolutelyContinuous volume V).ae_le (hf.ae_differentiableAt (μ := volume))
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
  have hgradformula (n : ℕ) (x : E) (hx : DifferentiableAt ℝ f x) : gradient (fn n) x =
      χ n x^2 • gradient f x+(2*χ n x*f x) • gradient (χ n) x :=
    gradient_cutoff_square_mul_at ((hχ n).differentiable (by norm_num) x) hx
  have hglim : Tendsto (fun n => (hgfnLp n).toLp (gradient (fn n))) atTop
      (𝓝 (hgLp.toLp (gradient f))) := by
    let bound (x : E) := 2 * ‖gradient f x‖ ^ 2 + 8 * C ^ 2 * ‖f x‖ ^ 2
    have hboundInt : Integrable bound μ :=
      (hgLp.norm.integrable_sq.const_mul 2).add (hfLp.norm.integrable_sq.const_mul (8 * C ^ 2))
    apply tendsto_toL2_of_dominated_sq hgLp hgfnLp bound hboundInt
    · intro n
      filter_upwards [hDiff] with x hx
      have hb := hχbounds n x
      have hs := hsqχ n x
      have hA : |χ n x ^ 2 - 1| ≤ 1 := by rw [abs_of_nonpos (by linarith)]; linarith
      have hB : |2 * χ n x * f x| ≤ 2 * |f x| := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg hb.1]
        nlinarith [abs_nonneg (f x)]
      have heq : gradient (fn n) x - gradient f x =
          (χ n x ^ 2 - 1) • gradient f x + (2 * χ n x * f x) • gradient (χ n) x := by
        rw [hgradformula n x hx]
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
    · filter_upwards [hDiff] with x hx
      have hh := (((hχlim x).pow 2).smul (tendsto_const_nhds (x := gradient f x))).add
        ((((hχlim x).const_mul 2).mul_const (f x)).smul (hGχlim x))
      have heq : (fun n => gradient (fn n) x) =
          (fun n => χ n x^2 • gradient f x+(2*χ n x*f x) • gradient (χ n) x) :=
        funext (fun n => hgradformula n x hx)
      rw [heq]
      simpa only [one_pow,one_smul,smul_zero,add_zero] using hh
  have hpairlim := hflim.prodMk_nhds hglim
  apply (closedGibbsGradient_isClosed hV hprob).mem_of_tendsto hpairlim
  exact Filter.Eventually.of_forall (fun n => by
    obtain ⟨v,hv,hD⟩ := exists_gibbsSobolev_of_compact_lipschitz hV hprob ρ hρ hHess
      (hfnLip n).choose_spec (hfnc n)
    have heV : gibbsSobolevInclusion hV hprob v = (hfnLp n).toLp (fn n) :=
      Lp.ext (hv.trans (hfnLp n).coeFn_toLp.symm)
    have heD : gibbsSobolevDerivative hV hprob v = (hgfnLp n).toLp (gradient (fn n)) :=
      Lp.ext (hD.trans (hgfnLp n).coeFn_toLp.symm)
    rw [← heV,← heD]
    exact v.property)

/-- A genuine global H¹ lift of any bounded globally Lipschitz input. The
closed gradient is the actual almost-everywhere classical gradient. -/
theorem exists_gibbsSobolev_of_bounded_lipschitz {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {L : ℝ≥0} (hf : LipschitzWith L f) (M : ℝ) (hBound : ∀ x, ‖f x‖ ≤ M) :
    ∃ v : gibbsSobolevGraph hV hp,
      (gibbsSobolevInclusion hV hp v =ᵐ[gibbsMeasure volume V] f) ∧
      (gibbsSobolevDerivative hV hp v =ᵐ[gibbsMeasure volume V] gradient f) := by
  let := hp
  have hM : 0 ≤ M := (norm_nonneg (f 0)).trans (hBound 0)
  have hfLp : MemLp f 2 (gibbsMeasure volume V) :=
    MemLp.of_bound hf.continuous.aestronglyMeasurable M (Eventually.of_forall hBound)
  have hgLp : MemLp (gradient f) 2 (gibbsMeasure volume V) :=
    MemLp.of_bound (measurable_euclidean_gradient f).aestronglyMeasurable L
      (Eventually.of_forall (norm_gradient_le_of_lipschitz hf))
  have hh := bounded_lipschitz_function_mem_closedGibbsGradient_graph hV hp ρ hρ hHess
    L hf M hM hBound hfLp hgLp
  let v : gibbsSobolevGraph hV hp := ⟨WithLp.toLp 2 (hfLp.toLp f,hgLp.toLp (gradient f)),hh⟩
  exact ⟨v,hfLp.coeFn_toLp,hgLp.coeFn_toLp⟩

end CutoffRigidity
