module
public import CutoffRigidity.GibbsSobolevLocalization
public import CutoffRigidity.EuclideanL2MollificationGeneral

/-! # Local Poincare on genuine localized closed Gibbs H¹ vectors

Actual compact weak-gradient mollification, with one common compact support,
passes the C¹ inequality through the true energy graph. Local boundedness of
the target measure is an explicit measure-theoretic intermediate condition.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal Pointwise
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 850000 in
theorem localPoincare_localized_gibbsSobolev
    {V χ : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ν : Measure E) [IsProbabilityMeasure ν] (C : ℝ)
    (hP : HasLocalSmoothPoincare ν C)
    (hloc : ∀ K : Set E, IsCompact K → ∃ M : ENNReal, M ≠ ⊤ ∧ ν.restrict K ≤ M • volume)
    (u : gibbsSobolevGraph hV hp) (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) :
    variance (fun x => χ x*gibbsSobolevInclusion hV hp u x) ν ≤
      C * ∫ x, ‖localizedSobolevGradientVector hV hp u χ x‖^2 ∂ν := by
  let w := fun x => χ x*gibbsSobolevInclusion hV hp u x
  let G := localizedSobolevGradientVector hV hp u χ
  have hw : MemLp w 2 volume := compact_cutoff_gibbsLp_memLp_volume hV.continuous hp hχ.continuous hχc
    (gibbsSobolevInclusion hV hp u)
  have hG : MemLp G 2 volume := localizedSobolevGradientVector_memLp hV hp u hχ hχc
  let ε := fun n : ℕ => 1 / ((n : ℝ)+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  let φ : ℕ → ContDiffBump (0 : E) := fun n => euclideanMollifierBump (ε n) (hε n)
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let fn := fun n => bumpMollification (φ n) w
  have hfn (n : ℕ) : ContDiff ℝ 2 (fn n) :=
    (bumpMollification_contDiff (φ n) (hw.locallyIntegrable (by norm_num))).of_le (by norm_num)
  have hwc : HasCompactSupport w := by
    simpa only [w,Pi.mul_def] using hχc.mul_right (f' := fun x => gibbsSobolevInclusion hV hp u x)
  have hfnc (n : ℕ) : HasCompactSupport (fn n) := bumpMollification_hasCompactSupport (φ n) hwc
  have hfnLp (n : ℕ) : MemLp (fn n) 2 volume := (hfn n).continuous.memLp_of_hasCompactSupport (hfnc n)
  have hgnLp (n : ℕ) : MemLp (gradient (fn n)) 2 volume :=
    c1_compact_gradient_memLp ((hfn n).of_le (by norm_num)) (hfnc n)
  let K := Metric.closedBall (0 : E) 1 + tsupport χ
  have hK : IsCompact K := (isCompact_closedBall _ _).add hχc
  obtain ⟨M,hM,hν⟩ := hloc K hK
  have hsub : tsupport χ ⊆ K := by
    intro x hx
    exact ⟨0,by simp,x,hx,zero_add x⟩
  have hzero (x : E) (hx : x ∉ tsupport χ) : w x=0 := by
    dsimp only [w]
    rw [image_eq_zero_of_notMem_tsupport hx,zero_mul]
  have hfnzero (n : ℕ) (x : E) (hx : x ∉ K) : fn n x=0 := by
    apply bumpMollification_eq_zero_off_add_support (φ n) hzero x
    intro hsmall
    apply hx
    obtain ⟨a,ha,b,hb,hab⟩ := hsmall
    refine ⟨a,?_,b,hb,hab⟩
    apply Metric.closedBall_subset_closedBall _ ha
    change ε n ≤ 1
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hsupport (n : ℕ) : tsupport (fn n) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hnot
    exact hx (hfnzero n x hnot)
  have hgnzero (n : ℕ) (x : E) (hx : x ∉ K) : gradient (fn n) x=0 := by
    have ht : x ∉ tsupport (fn n) := fun h => hx (hsupport n h)
    change (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fn n) x)=0
    rw [fderiv_of_notMem_tsupport ℝ ht,map_zero]
  have hGzero (x : E) (hx : x ∉ K) : G x=0 := by
    have ht : x ∉ tsupport χ := fun h => hx (hsub h)
    have hv : χ x=0 := image_eq_zero_of_notMem_tsupport ht
    have hd : fderiv ℝ χ x=0 := fderiv_of_notMem_tsupport ℝ ht
    apply PiLp.ext
    intro i
    change χ x * _ + _ * coordinateDerivative i χ x=0
    simp only [hv,coordinateDerivative,hd,zero_apply,mul_zero,zero_mul,add_zero]
  have hflim : Tendsto (fun n => (hfnLp n).toLp (fn n)) atTop (𝓝 (hw.toLp w)) :=
    bumpMollificationLp_tendsto φ hφ w
      (hχ.continuous.measurable.mul (Lp.stronglyMeasurable (gibbsSobolevInclusion hV hp u)).measurable) hw
  obtain ⟨hwi,hwci,hglim⟩ := gibbsSobolev_localized_mollifiedGradient_tendsto hV hp u hχ hχc φ hφ
  have hglim' : Tendsto (fun n => (hgnLp n).toLp (gradient (fn n))) atTop (𝓝 (hG.toLp G)) := hglim
  exact (localPoincare_of_supported_graph_limit volume ν C hP K hK.measurableSet M hM hν fn w G
    (fun n => (hfn n).of_le (by norm_num)) hfnLp hw hgnLp hG
    (fun n => Eventually.of_forall (hfnzero n)) (Eventually.of_forall (fun x hx => hzero x (fun h => hx (hsub h))))
    (fun n => Eventually.of_forall (hgnzero n)) (Eventually.of_forall hGzero) hflim hglim').2


/-- The actual localized weak gradient is the ordinary weak product. -/
theorem localizedSobolevGradientVector_eq {V χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : gibbsSobolevGraph hV hp) (x : E) :
    localizedSobolevGradientVector hV hp u χ x =
      χ x • gibbsSobolevDerivative hV hp u x +
        gibbsSobolevInclusion hV hp u x • gradient χ x := by
  apply PiLp.ext
  intro i
  change χ x * _ + _ * coordinateDerivative i χ x = _
  simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  change _ + _ * fderiv ℝ χ x (EuclideanSpace.single i 1) = _
  rw [fderiv_single_eq_gradient_coordinate]

set_option maxHeartbeats 850000 in
/-- A genuine bounded closed Gibbs H¹ representative with finite energy
under the target law satisfies that law's Poincare inequality. Local bounded
change of measure is used only to justify actual compact approximation. -/
theorem localPoincare_bounded_gibbsSobolev
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ν : Measure E) [IsProbabilityMeasure ν] (C : ℝ)
    (hP : HasLocalSmoothPoincare ν C)
    (hloc : ∀ K : Set E, IsCompact K → ∃ M : ENNReal, M ≠ ⊤ ∧ ν.restrict K ≤ M • volume)
    (u : gibbsSobolevGraph hV hp) (M : ℝ) (hM0 : 0 ≤ M)
    (hU : ∀ᵐ x ∂ν, ‖gibbsSobolevInclusion hV hp u x‖ ≤ M)
    (hD : MemLp (fun x => gibbsSobolevDerivative hV hp u x) 2 ν) :
    variance (fun x => gibbsSobolevInclusion hV hp u x) ν ≤
      C * ∫ x, ‖gibbsSobolevDerivative hV hp u x‖^2 ∂ν := by
  let U := gibbsSobolevInclusion hV hp u
  let D := gibbsSobolevDerivative hV hp u
  obtain ⟨K,hK0,χ,hχ,hχc,hχbounds,hχone,hχgrad⟩ := exists_smooth_cutoff_exhaustion (d := d)
  let fn := fun n : ℕ => fun x : E => χ n x * U x
  let Gn := fun n : ℕ => localizedSobolevGradientVector hV hp u (χ n)
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
    apply (div_le_iff₀ (by positivity : (0:ℝ)<n+1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hχabs (n : ℕ) (x : E) : |χ n x| ≤ 1 := by
    rw [abs_of_nonneg (hχbounds n x).1]
    exact (hχbounds n x).2
  have hfnM (n : ℕ) : AEStronglyMeasurable (fn n) ν :=
    (hχ n).continuous.aestronglyMeasurable.mul (Lp.stronglyMeasurable U).aestronglyMeasurable
  have hfnBound (n : ℕ) : ∀ᵐ x ∂ν, ‖fn n x‖ ≤ M := by
    filter_upwards [hU] with x hx
    change ‖χ n x * U x‖ ≤ M
    rw [norm_mul,Real.norm_eq_abs]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hχabs n x)).trans hx
  have hfnLim (x : E) : Tendsto (fun n => fn n x) atTop (𝓝 (U x)) := by
    simpa only [fn,one_mul] using (hχlim x).mul_const (U x)
  have hIntF := tendsto_integral_of_dominated_convergence (fun _ : E => M) hfnM
    (integrable_const M) hfnBound (Eventually.of_forall hfnLim)
  have hIntSq : Tendsto (fun n => ∫ x, fn n x^2 ∂ν) atTop (𝓝 (∫ x, U x^2 ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : E => M^2)
      (fun n => (hfnM n).pow 2) (integrable_const _) _
      (Eventually.of_forall (fun x => (hfnLim x).pow 2))
    intro n
    filter_upwards [hfnBound n] with x hx
    change ‖fn n x^2‖ ≤ _
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hGnMeas (n : ℕ) : AEStronglyMeasurable (Gn n) ν := by
    have he : Gn n = fun x => χ n x • D x + U x • gradient (χ n) x := by
      funext x
      exact localizedSobolevGradientVector_eq hV hp u x
    rw [he]
    exact ((hχ n).continuous.aestronglyMeasurable.smul (Lp.stronglyMeasurable D).aestronglyMeasurable).add
      ((Lp.stronglyMeasurable U).aestronglyMeasurable.smul
        (continuous_gradient_of_c1 ((hχ n).of_le (by norm_num))).aestronglyMeasurable)
  have hGnBound (n : ℕ) : ∀ᵐ x ∂ν, ‖Gn n x‖^2 ≤ 2*‖D x‖^2+2*K^2*M^2 := by
    filter_upwards [hU] with x hx
    have hn : ‖Gn n x‖ ≤ ‖D x‖+M*K := by
      rw [show Gn n x=χ n x • D x+U x • gradient (χ n) x from localizedSobolevGradientVector_eq hV hp u x]
      calc
        _ ≤ ‖χ n x • D x‖+‖U x • gradient (χ n) x‖ := norm_add_le _ _
        _ ≤ 1*‖D x‖+M*K := by rw [norm_smul,norm_smul]; gcongr; exact hχabs n x; exact hGχbound n x
        _ = _ := by ring
    nlinarith [norm_nonneg (Gn n x),norm_nonneg (D x),sq_nonneg (‖D x‖-M*K)]
  have hGnLim (x : E) : Tendsto (fun n => Gn n x) atTop (𝓝 (D x)) := by
    have hh := ((hχlim x).smul_const (D x)).add ((hGχlim x).const_smul (U x))
    simpa only [Gn,localizedSobolevGradientVector_eq,one_smul,smul_zero,add_zero] using hh
  have hIntG : Tendsto (fun n => ∫ x, ‖Gn n x‖^2 ∂ν) atTop (𝓝 (∫ x, ‖D x‖^2 ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => 2*‖D x‖^2+2*K^2*M^2)
      (fun n => (hGnMeas n).norm.pow 2)
      ((hD.norm.integrable_sq.const_mul 2).add (integrable_const _)) _
      (Eventually.of_forall (fun x => (hGnLim x).norm.pow 2))
    intro n
    filter_upwards [hGnBound n] with x hx
    change ‖‖Gn n x‖^2‖ ≤ _
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hx
  have hfnLp (n : ℕ) : MemLp (fn n) 2 ν := MemLp.of_bound (hfnM n) M (hfnBound n)
  have hULp : MemLp (fun x => U x) 2 ν :=
    MemLp.of_bound (Lp.stronglyMeasurable U).aestronglyMeasurable M hU
  have hb (n : ℕ) : (∫ x, fn n x^2 ∂ν)-(∫ x, fn n x ∂ν)^2 ≤ C*∫ x, ‖Gn n x‖^2 ∂ν := by
    have hh := localPoincare_localized_gibbsSobolev hV hp ν C hP hloc u (hχ n) (hχc n)
    rw [variance_eq_sub (hfnLp n)] at hh
    simpa only [Pi.pow_apply] using hh
  rw [variance_eq_sub hULp]
  simpa only [Pi.pow_apply] using le_of_tendsto_of_tendsto (hIntSq.sub (hIntF.pow 2)) (hIntG.const_mul C) (Eventually.of_forall hb)

end CutoffRigidity
