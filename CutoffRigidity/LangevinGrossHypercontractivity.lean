module
public import CutoffRigidity.LangevinGrossMomentInequality

/-! # Gross hypercontractivity for actual compact Langevin tests

The derived Gross differential inequality is integrated: `log Z / p` is
antitone along the genuine moving exponent `p(t) = 1 + e^{2ρt}`. A
positive square-root regularization then removes the positivity floor,
giving `‖P_t g‖_{p(t)} ≤ ‖g‖_2` for every compact C² test.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem grossExponent_zero (ρ : ℝ) : grossExponent ρ 0 = 2 := by
  simp only [grossExponent, mul_zero, Real.exp_zero]; norm_num

theorem two_le_grossExponent {ρ t : ℝ} (hρ : 0 ≤ ρ) (ht : 0 ≤ t) : 2 ≤ grossExponent ρ t := by
  have hh : 1 ≤ Real.exp (2*ρ*t) := Real.one_le_exp_iff.mpr (by positivity)
  dsimp only [grossExponent]
  linarith

/-- The actual moving moment is strictly positive at every real time. -/
theorem langevinGrossPowerMoment_pos'
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E,ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x,m ≤ c+g x) (r : ℝ) :
    0 < langevinGrossPowerMoment V g B P c ρ r := by
  let := hp
  let q := langevinPositiveProfile V g B P c r
  let p := grossExponent ρ r
  have hlo := langevinPositiveProfile_lower hB hV hg hgc ρ hρ.le hHess c m hpos r
  have hqPos (x : E) : 0 < q x := hm.trans_le (hlo x)
  have hP : 0 ≤ p := by dsimp only [p,grossExponent]; positivity
  have hqC : ContDiff ℝ 1 q := contDiff_const.add
    (contDiff_one_langevinKernel_integral hB hV ρ hρ.le hHess (hg.of_le (by norm_num)) hgc r.toNNReal)
  obtain ⟨A,hA,hBound⟩ := langevinPositiveProfile_uniform_norm_bound hB hV hg hgc ρ hρ hHess c
  have hI : Integrable (fun x => q x^p) (gibbsMeasure volume V) := by
    apply (integrable_const ((1+A)^p)).mono'
      (hqC.rpow_const_of_ne (fun x => (hqPos x).ne')).continuous.aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    exact positive_rpow_uniform_bound hm (hlo x)
      ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hBound r x)) hP le_rfl
  apply (integral_pos_iff_support_of_nonneg (fun x => Real.rpow_nonneg (hqPos x).le p) hI).mpr
  have he : Function.support (fun x => q x^p) = univ := by
    ext x
    simp only [Function.mem_support,ne_eq,Set.mem_univ,iff_true]
    exact (Real.rpow_pos_of_pos (hqPos x) p).ne'
  rw [he]
  simp

/-- Actual moving-power moments are continuous at the true initial time,
by joint continuity of the source profile and dominated convergence. -/
theorem continuousAt_langevinGrossPowerMoment_zero'
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E,ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x,m ≤ c+g x) :
    ContinuousAt (langevinGrossPowerMoment V g B P c ρ) 0 := by
  let := hp
  let μ := gibbsMeasure volume V
  let q := langevinPositiveProfile V g B P c
  let p := grossExponent ρ
  let S := grossExponent ρ 1
  obtain ⟨A,hA,hBound⟩ := langevinPositiveProfile_uniform_norm_bound hB hV hg hgc ρ hρ hHess c
  have hPos (r : ℝ) (x : E) : 0 < q r x :=
    hm.trans_le (langevinPositiveProfile_lower hB hV hg hgc ρ hρ.le hHess c m hpos r x)
  have hC := continuous_langevinPositiveProfile_time_initial hB hV hg hgc ρ hρ hHess c
  have hMeas (r : ℝ) : AEStronglyMeasurable (fun x => q r x^p r) μ := by
    have hQr : Continuous (q r) := hC.comp (continuous_const.prodMk continuous_id)
    exact (hQr.rpow_const (fun x => Or.inl (hPos r x).ne')).aestronglyMeasurable
  have hbound : ∀ᶠ r in 𝓝 (0:ℝ),∀ᵐ x ∂μ, ‖q r x^p r‖ ≤ (1+A)^S := by
    filter_upwards [eventually_lt_nhds (by norm_num : (0:ℝ)<1)] with r hr
    apply Eventually.of_forall
    intro x
    have hP : 0 ≤ p r := by dsimp only [p,grossExponent]; positivity
    have hPS : p r ≤ S := by dsimp only [p,S,grossExponent]; gcongr
    exact positive_rpow_uniform_bound hm
      (langevinPositiveProfile_lower hB hV hg hgc ρ hρ.le hHess c m hpos r x)
      ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hBound r x)) hP hPS
  have hPoint : ∀ᵐ x ∂μ,Tendsto (fun r => q r x^p r) (𝓝 0) (𝓝 (q 0 x^p 0)) := by
    apply Eventually.of_forall
    intro x
    have hQ : ContinuousAt (fun r : ℝ => q r x) 0 :=
      (hC.comp (continuous_id.prodMk continuous_const)).continuousAt
    exact (hQ.rpow (hasDerivAt_grossExponent ρ 0).continuousAt (Or.inl (hPos 0 x).ne')).tendsto
  exact tendsto_integral_filter_of_dominated_convergence (fun _ => (1+A)^S)
    (Eventually.of_forall hMeas) hbound (integrable_const _) hPoint

/-- The actual initial moment is the source test's squared L² mass. -/
theorem langevinGrossPowerMoment_zero_eq
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E,ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (c : ℝ) :
    langevinGrossPowerMoment V g B P c ρ 0 = ∫ x,(c+g x)^2 ∂gibbsMeasure volume V := by
  have hq0 (z : E) : langevinPositiveProfile V g B P c 0 z = c + g z := by
    change c + (∫ w, g w ∂langevinKernel V B P (0 : ℝ).toNNReal z) = _
    rw [Real.toNNReal_zero, langevinKernel_zero hB hV ρ hρ.le hHess, Kernel.id_apply, integral_dirac]
  simp only [langevinGrossPowerMoment, hq0, grossExponent_zero, Real.rpow_two]

set_option maxHeartbeats 800000 in
/-- Gross's integration: `log Z(t)/p(t)` is bounded by its initial value,
from the actual differential inequality and actual continuity at zero. -/
theorem langevinGrossPowerMoment_log_div_le
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hd : 0 < d)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E,ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x,m ≤ c+g x) {t : ℝ} (ht : 0 ≤ t) :
    Real.log (langevinGrossPowerMoment V g B P c ρ t) / grossExponent ρ t ≤
      Real.log (langevinGrossPowerMoment V g B P c ρ 0) / 2 := by
  let Z := langevinGrossPowerMoment V g B P c ρ
  let p := grossExponent ρ
  let φ := fun r => Real.log (Z r) / p r
  have hZpos (r : ℝ) : 0 < Z r := langevinGrossPowerMoment_pos' hB hV hp hg hgc ρ hρ hHess c m hm hpos r
  have hppos (r : ℝ) : 0 < p r := by dsimp only [p,grossExponent]; positivity
  obtain ⟨Dz, hDz⟩ : ∃ Dz : ℝ → ℝ, ∀ r, 0 < r → HasDerivAt Z (Dz r) r :=
    ⟨_, fun r hr => hasDerivAt_langevinGrossPowerMoment hB hV hp hg hgc ρ hρ hHess c m hm hpos hr⟩
  let φ' := fun r => ((Dz r / Z r) * p r - Real.log (Z r) * (2*ρ*(p r-1))) / p r ^ 2
  have hφd (r : ℝ) (hr : 0 < r) : HasDerivAt φ (φ' r) r :=
    ((hDz r hr).log (hZpos r).ne').div (hasDerivAt_grossExponent ρ r) (hppos r).ne'
  have hZc (r : ℝ) (hr : 0 ≤ r) : ContinuousAt Z r := by
    rcases hr.eq_or_lt with h | h
    · rw [← h]
      exact continuousAt_langevinGrossPowerMoment_zero' hB hV hp hg hgc ρ hρ hHess c m hm hpos
    · exact (hDz r h).continuousAt
  have hcont : ContinuousOn φ (Ici 0) := by
    intro r hr
    apply ContinuousAt.continuousWithinAt
    exact ((hZc r hr).log (hZpos r).ne').div (hasDerivAt_grossExponent ρ r).continuousAt (hppos r).ne'
  have hint : interior (Ici (0:ℝ)) = Ioi 0 := interior_Ici
  have hanti : AntitoneOn φ (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont
    · rw [hint]
      intro r hr
      exact (hφd r hr).differentiableAt.differentiableWithinAt
    · rw [hint]
      intro r hr
      rw [(hφd r hr).deriv]
      have hineq := langevinGrossPowerMoment_derivative_inequality hB hV hp hd hg hgc ρ hρ hHess c m hm hpos hr
      rw [(hDz r hr).deriv] at hineq
      change p r * Dz r - (2*ρ*(p r-1)) * Z r * Real.log (Z r) ≤ 0 at hineq
      have he : φ' r = (p r * Dz r - (2*ρ*(p r-1)) * Z r * Real.log (Z r)) / (Z r * p r ^ 2) := by
        dsimp only [φ']
        field_simp [(hZpos r).ne', (hppos r).ne']
      rw [he]
      exact div_nonpos_of_nonpos_of_nonneg hineq (by have := hZpos r; positivity)
  have hh := hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
  change Real.log (Z t) / p t ≤ Real.log (Z 0) / p 0 at hh
  rwa [show p 0 = 2 from grossExponent_zero ρ] at hh

/-- Positive compact perturbations satisfy the actual Gross bound
`∫ q_t^{p(t)} ≤ (∫ (c+g)²)^{p(t)/2}`. -/
theorem langevinPositiveProfile_hypercontractive
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hd : 0 < d)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E,ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x,m ≤ c+g x) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, (langevinPositiveProfile V g B P c t x) ^ grossExponent ρ t ∂gibbsMeasure volume V) ≤
      (∫ x,(c+g x)^2 ∂gibbsMeasure volume V) ^ (grossExponent ρ t / 2) := by
  have hl := langevinGrossPowerMoment_log_div_le hB hV hp hd hg hgc ρ hρ hHess c m hm hpos ht
  have hZ := langevinGrossPowerMoment_pos' hB hV hp hg hgc ρ hρ hHess c m hm hpos t
  have hZ0 := langevinGrossPowerMoment_pos' hB hV hp hg hgc ρ hρ hHess c m hm hpos 0
  have hpp : 0 < grossExponent ρ t := by dsimp only [grossExponent]; positivity
  rw [div_le_iff₀ hpp] at hl
  have hE := Real.exp_le_exp.mpr hl
  rw [Real.exp_log hZ] at hE
  rw [← langevinGrossPowerMoment_zero_eq hB hV ρ hρ hHess c, Real.rpow_def_of_pos hZ0]
  calc
    _ = langevinGrossPowerMoment V g B P c ρ t := rfl
    _ ≤ _ := hE
    _ = _ := by congr 1; ring
/-- Every nonnegative power of a positive source profile is integrable. -/
theorem langevinPositiveProfile_rpow_integrable'
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E,ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x,m ≤ c+g x) (r p : ℝ) (hP : 0 ≤ p) :
    Integrable (fun x => (langevinPositiveProfile V g B P c r x)^p) (gibbsMeasure volume V) := by
  let := hp
  let q := langevinPositiveProfile V g B P c r
  have hlo := langevinPositiveProfile_lower hB hV hg hgc ρ hρ.le hHess c m hpos r
  have hqPos (x : E) : 0 < q x := hm.trans_le (hlo x)
  have hqC : ContDiff ℝ 1 q := contDiff_const.add
    (contDiff_one_langevinKernel_integral hB hV ρ hρ.le hHess (hg.of_le (by norm_num)) hgc r.toNNReal)
  obtain ⟨A,hA,hBound⟩ := langevinPositiveProfile_uniform_norm_bound hB hV hg hgc ρ hρ hHess c
  apply (integrable_const ((1+A)^p)).mono'
    (hqC.rpow_const_of_ne (fun x => (hqPos x).ne')).continuous.aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  exact positive_rpow_uniform_bound hm (hlo x)
    ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hBound r x)) hP le_rfl

set_option maxHeartbeats 1000000 in
/-- Signed compact C² tests satisfy the actual Gross moment bound; the
positivity floor is removed by explicit square-root regularization. -/
theorem langevinKernel_compact_test_rpow_integral_le
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hd : 0 < d)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E,ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, |∫ z, g z ∂langevinKernel V B P t.toNNReal x| ^ grossExponent ρ t ∂gibbsMeasure volume V) ≤
      (∫ x, g x ^ 2 ∂gibbsMeasure volume V) ^ (grossExponent ρ t / 2) := by
  let := hp
  let μ := gibbsMeasure volume V
  let K := langevinKernel V B P t.toNNReal
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t.toNNReal
  let p := grossExponent ρ t
  have hp0 : 0 ≤ p := by dsimp only [p,grossExponent]; positivity
  have hg2I : Integrable (fun z => g z ^ 2) μ :=
    (hg.continuous.memLp_of_hasCompactSupport hgc : MemLp g 2 μ).integrable_sq
  have hG0 : 0 ≤ ∫ x, g x ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have key : ∀ ε : ℝ, 0 < ε → (∫ x, |∫ z, g z ∂K x| ^ p ∂μ) ≤ ((∫ x, g x ^ 2 ∂μ) + ε) ^ (p / 2) := by
    intro ε hε
    let c := Real.sqrt ε
    let f := fun z => Real.sqrt (g z ^ 2 + ε)
    let h := fun z => f z - c
    have hc : 0 < c := Real.sqrt_pos.mpr hε
    have hfC : ContDiff ℝ 2 f := ((hg.pow 2).add contDiff_const).sqrt (fun z => by positivity)
    have hhC : ContDiff ℝ 2 h := hfC.sub contDiff_const
    have hhc : HasCompactSupport h := by
      simpa only [h, f, c, Function.comp_def] using hgc.comp_left
        (g := fun a : ℝ => Real.sqrt (a ^ 2 + ε) - Real.sqrt ε) (by simp)
    have hfEq (z : E) : c + h z = f z := by dsimp only [h]; ring
    have hFloor (z : E) : c ≤ c + h z := by
      rw [hfEq]
      exact Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))
    have hroot := langevinPositiveProfile_hypercontractive hB hV hp hd hhC hhc ρ hρ hHess c c hc hFloor ht
    have hNorm (x : E) : |∫ z, g z ∂K x| ≤ langevinPositiveProfile V h B P c t x := by
      have hgI : Integrable g (K x) := hg.continuous.integrable_of_hasCompactSupport hgc
      have hhI : Integrable h (K x) := hhC.continuous.integrable_of_hasCompactSupport hhc
      have he : f = fun z => c + h z := by funext z; exact (hfEq z).symm
      have hfI : Integrable f (K x) := by rw [he]; exact (integrable_const c).add hhI
      have hPoint (z : E) : ‖g z‖ ≤ f z := by
        rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt (le_add_of_nonneg_right hε.le)
      rw [← Real.norm_eq_abs]
      calc
        _ ≤ ∫ z, ‖g z‖ ∂K x := norm_integral_le_integral_norm _
        _ ≤ ∫ z, f z ∂K x := integral_mono hgI.norm hfI hPoint
        _ = _ := by
          rw [he, integral_add (integrable_const c) hhI]
          simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
          rfl
    have hqI := langevinPositiveProfile_rpow_integrable' hB hV hp hhC hhc ρ hρ hHess c c hc hFloor t p hp0
    have hmono : (∫ x, |∫ z, g z ∂K x| ^ p ∂μ) ≤ ∫ x, (langevinPositiveProfile V h B P c t x) ^ p ∂μ :=
      integral_mono_of_nonneg (Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg _) _) hqI
        (Eventually.of_forall fun x => Real.rpow_le_rpow (abs_nonneg _) (hNorm x) hp0)
    have he (z : E) : (c + h z) ^ 2 = g z ^ 2 + ε := by
      rw [hfEq]
      exact Real.sq_sqrt (add_nonneg (sq_nonneg _) hε.le)
    rw [integral_congr_ae (Eventually.of_forall he), integral_add hg2I (integrable_const ε), integral_const] at hroot
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hroot
    exact hmono.trans hroot
  have hlim : Tendsto (fun ε : ℝ => ((∫ x, g x ^ 2 ∂μ) + ε) ^ (p / 2)) (𝓝[>] 0)
      (𝓝 (((∫ x, g x ^ 2 ∂μ) + 0) ^ (p / 2))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    apply ((continuous_const.add continuous_id).rpow_const _).tendsto
    intro ε
    right
    dsimp only [p,grossExponent]
    positivity
  rw [add_zero] at hlim
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)

set_option maxHeartbeats 800000 in
/-- Gross hypercontractivity `‖P_t g‖_{p(t)} ≤ ‖g‖_2` for actual compact
C² tests, as a genuine extended Lᵖ norm inequality. -/
theorem eLpNorm_langevinKernel_compact_test_le
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hd : 0 < d)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E,ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z) {t : ℝ} (ht : 0 ≤ t) :
    eLpNorm (fun x => ∫ z, g z ∂langevinKernel V B P t.toNNReal x)
      (ENNReal.ofReal (grossExponent ρ t)) (gibbsMeasure volume V) ≤
      eLpNorm g 2 (gibbsMeasure volume V) := by
  let := hp
  let μ := gibbsMeasure volume V
  let p := grossExponent ρ t
  have hp2 : 2 ≤ p := two_le_grossExponent hρ.le ht
  have hpp : 0 < p := by linarith
  let F := fun x => ∫ z, g z ∂langevinKernel V B P t.toNNReal x
  have hFC : Continuous F :=
    (contDiff_one_langevinKernel_integral hB hV ρ hρ.le hHess (hg.of_le (by norm_num)) hgc t.toNNReal).continuous
  obtain ⟨M, hM0, hM⟩ := compact_continuous_norm_bound hg.continuous hgc
  have hFB (x : E) : ‖F x‖ ≤ M :=
    langevinKernel_integral_compact_test_norm_le hB hV ρ hρ.le hHess hM t.toNNReal x
  have hFLp : MemLp F (ENNReal.ofReal p) μ :=
    MemLp.of_bound hFC.aestronglyMeasurable M (Eventually.of_forall hFB)
  have hgLp : MemLp g 2 μ := hg.continuous.memLp_of_hasCompactSupport hgc
  have hpne : ENNReal.ofReal p ≠ 0 := by simp [hpp]
  rw [hFLp.eLpNorm_eq_integral_rpow_norm hpne ENNReal.ofReal_ne_top,
    hgLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num), ENNReal.toReal_ofReal hpp.le]
  apply ENNReal.ofReal_le_ofReal
  have hA := langevinKernel_compact_test_rpow_integral_le hB hV hp hd hg hgc ρ hρ hHess ht
  simp only [Real.norm_eq_abs, ENNReal.toReal_ofNat]
  simp only [Real.rpow_two, sq_abs]
  have hA0 : 0 ≤ ∫ x, |F x| ^ p ∂μ := integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _
  have hG0 : 0 ≤ ∫ x, g x ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  calc
    (∫ x, |F x| ^ p ∂μ) ^ p⁻¹ ≤ ((∫ x, g x ^ 2 ∂μ) ^ (p / 2)) ^ p⁻¹ :=
      Real.rpow_le_rpow hA0 hA (inv_nonneg.mpr hpp.le)
    _ = _ := by
      rw [← Real.rpow_mul hG0]
      congr 1
      have hpn : p ≠ 0 := hpp.ne'
      field_simp

end CutoffRigidity
