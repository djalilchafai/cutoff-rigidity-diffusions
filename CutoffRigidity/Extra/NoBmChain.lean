module

public import CutoffRigidity.Extra.NoBmLSI3
public import CutoffRigidity.LogSobolev
public import CutoffRigidity.Talagrand
public import CutoffRigidity.LipschitzExponentialLogSobolev

/-! # Brownian-free copies of the Euclidean logarithmic Sobolev / Talagrand chain

Mechanical copies (binders `B`, `P`, `hB : IsEuclideanBrownian B P` removed, names suffixed `_nobm`)
of the project theorems whose only use of the Brownian motion was the call to
`logSobolev_regularized_compact_square`, which is replaced by
`NoBm.logSobolev_regularized_compact_square_nobm`.
-/

public section

section Seg0

namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped ENNReal NNReal Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual normalized closed-H¹ root inequality. The graph and its
approximants are the genuine closure of the actual compact gradient. -/
theorem logSobolev_closed_normalized_root_nobm
     {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (u : gibbsSobolevGraph hV hp)
    (hu : ‖gibbsSobolevInclusion hV hp u‖ ^ 2 = 1) :
    (∫⁻ x, ENNReal.ofReal (klFun ((gibbsSobolevInclusion hV hp u x) ^ 2))
      ∂gibbsMeasure volume V) ≤
      ENNReal.ofReal ((2 / ρ) * ‖gibbsSobolevDerivative hV hp u‖ ^ 2) := by
  let := hp
  let μ := gibbsMeasure volume V
  let G := compactGibbsGradient hV.continuous hp
  let U := gibbsSobolevInclusion hV hp u
  let D := gibbsSobolevDerivative hV hp u
  have hmem : (U, D) ∈ closure (G.graph : Set _) := by
    change (U, D) ∈ G.graph.topologicalClosure
    rw [(compactGibbsGradient_isClosable hV hp).graph_closure_eq_closure_graph]
    exact u.property
  obtain ⟨p, hpseq, hplim⟩ := mem_closure_iff_seq_limit.mp hmem
  have hfirst : Tendsto (fun n => (p n).1) atTop (𝓝 U) := (continuous_fst.tendsto _).comp hplim
  have hsecond : Tendsto (fun n => (p n).2) atTop (𝓝 D) := (continuous_snd.tendsto _).comp hplim
  let ε := fun n : ℕ => differenceStep n
  have hεpos (n : ℕ) : 0 < ε n := differenceStep_pos n
  have hεlim : Tendsto ε atTop (𝓝 0) := differenceStep_tendsto_zero
  let F := fun (n : ℕ) (x : E) => ENNReal.ofReal
    (klFun (((p n).1 x ^ 2 + ε n) / (‖(p n).1‖ ^ 2 + ε n)))
  let b := fun n : ℕ => (2 / ρ) / (‖(p n).1‖ ^ 2 + ε n) * ‖(p n).2‖ ^ 2
  have hbound (n : ℕ) : (∫⁻ x, F n x ∂μ) ≤ ENNReal.ofReal (b n) := by
    obtain ⟨v, hv1, hv2⟩ := G.mem_graph_iff.mp (hpseq n)
    let f := compactGibbsRepresentative V v
    have hf := (compactGibbsRepresentative_spec V v).1
    have hfc := (compactGibbsRepresentative_spec V v).2.1
    have hfrep : (p n).1 =ᵐ[μ] f := by
      rw [← hv1]
      exact (compactGibbsRepresentative_spec V v).2.2.symm
    have hgrep : (p n).2 =ᵐ[μ] gradient f := by
      rw [← hv2]
      exact (compactGibbsGradient_memLp hp v).coeFn_toLp
    have hA : (∫ x, f x ^ 2 ∂μ) = ‖(p n).1‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hfrep] with x hx
      rw [hx, Real.inner_apply]
      ring
    have hE : (∫ x, ‖gradient f x‖ ^ 2 ∂μ) = ‖(p n).2‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hgrep] with x hx
      rw [hx, real_inner_self_eq_norm_sq]
    have hh := NoBm.logSobolev_regularized_compact_square_nobm hV hρ hHess hp hf hfc (ε n) (hεpos n)
    change (∫⁻ x, ENNReal.ofReal (klFun ((f x ^ 2 + ε n) / ((∫ y, f y ^ 2 ∂μ) + ε n))) ∂μ) ≤
      ENNReal.ofReal ((2 / ρ) / ((∫ y, f y ^ 2 ∂μ) + ε n) * ∫ x, ‖gradient f x‖ ^ 2 ∂μ) at hh
    rw [hA, hE] at hh
    calc
      _ = ∫⁻ x, ENNReal.ofReal (klFun ((f x ^ 2 + ε n) / (‖(p n).1‖ ^ 2 + ε n))) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hfrep] with x hx
        simp only [F, hx]
      _ ≤ _ := hh
  have hU : ‖U‖ ^ 2 = 1 := hu
  have hDen : Tendsto (fun n => ‖(p n).1‖ ^ 2 + ε n) atTop (𝓝 (1 : ℝ)) := by
    simpa only [hU, add_zero] using (hfirst.norm.pow 2).add hεlim
  have hb : Tendsto b atTop (𝓝 ((2 / ρ) * ‖D‖ ^ 2)) := by
    simpa only [div_one, Pi.div_apply, Function.comp_def, b] using (tendsto_const_nhds.div hDen (by norm_num)).mul (hsecond.norm.pow 2)
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hfirst).exists_seq_tendsto_ae'
  have hFm (n : ℕ) : Measurable (F (ns n)) := by
    apply Measurable.ennreal_ofReal
    apply measurable_klFun.comp
    exact (((Lp.stronglyMeasurable (p (ns n)).1).measurable.pow_const 2).add measurable_const).div_const _
  have hpoint : ∀ᵐ x ∂μ, liminf (fun n => F (ns n) x) atTop = ENNReal.ofReal (klFun (U x ^ 2)) := by
    filter_upwards [hae] with x hx
    have hr := ((hx.pow 2).add (hεlim.comp hns)).div (hDen.comp hns) (by norm_num)
    have hr' : Tendsto (fun n => ((p (ns n)).1 x ^ 2 + ε (ns n)) /
        (‖(p (ns n)).1‖ ^ 2 + ε (ns n))) atTop (𝓝 (U x ^ 2)) := by
      simpa only [add_zero, div_one, Pi.div_def, Pi.add_apply, Function.comp_def] using hr
    exact ((ENNReal.continuous_ofReal.comp continuous_klFun).continuousAt.tendsto.comp hr').liminf_eq
  have hFatou := lintegral_liminf_le (μ := μ) (f := fun n => F (ns n)) (u := atTop) hFm
  rw [lintegral_congr_ae hpoint] at hFatou
  have hh : liminf (fun n => ∫⁻ x, F (ns n) x ∂μ) atTop ≤
      liminf (fun n => ENNReal.ofReal (b (ns n))) atTop :=
    liminf_le_liminf (Eventually.of_forall (fun n => hbound (ns n)))
  have hblim : Tendsto (fun n => ENNReal.ofReal (b (ns n))) atTop
      (𝓝 (ENNReal.ofReal ((2 / ρ) * ‖D‖ ^ 2))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hb.comp hns)
  rw [hblim.liminf_eq] at hh
  exact hFatou.trans hh


end CutoffRigidity

end Seg0

section Seg1

namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped Topology NNReal ENNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Normalized bounded Lipschitz tests satisfy the genuine real LSI;
Rademacher, weak derivatives, and actual closed-domain membership are
proved by the bounded Lipschitz H¹ lift rather than supplied as premises. -/
theorem logSobolev_normalized_bounded_lipschitz_nobm
    
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hd : 0 < d)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {L : NNReal} (hLip : LipschitzWith L f) (M : ℝ) (hBound : ∀ x, ‖f x‖ ≤ M)
    (hNorm : ∫ x,f x^2 ∂gibbsMeasure volume V = 1) :
    (∫ x,klFun (f x^2) ∂gibbsMeasure volume V) ≤
      (2/ρ)*∫ x,‖gradient f x‖^2 ∂gibbsMeasure volume V := by
  let := hp
  let μ := gibbsMeasure volume V
  obtain ⟨u,hu,hDu⟩ := exists_gibbsSobolev_of_bounded_lipschitz hV hp ρ hρ hHess hLip M hBound
  have hU : ‖gibbsSobolevInclusion hV hp u‖^2 = 1 := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    calc
      _ = ∫ x,f x^2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [hu] with x hx
        rw [hx,Real.inner_apply]; ring
      _ = 1 := hNorm
  have hD : ‖gibbsSobolevDerivative hV hp u‖^2 = ∫ x,‖gradient f x‖^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hDu] with x hx
    rw [hx,real_inner_self_eq_norm_sq]
  have hLSI := logSobolev_closed_normalized_root_nobm hV hp hd ρ hρ hHess u hU
  rw [hD] at hLSI
  have hAE : (fun x => ENNReal.ofReal (klFun (gibbsSobolevInclusion hV hp u x^2))) =ᵐ[μ]
      (fun x => ENNReal.ofReal (klFun (f x^2))) := hu.mono (fun x hx => by dsimp only; rw [hx])
  rw [lintegral_congr_ae hAE] at hLSI
  have hInt := integrable_klFun_square_of_bounded μ hLip.continuous.measurable M hBound
  rw [← ofReal_integral_eq_lintegral_ofReal hInt (Eventually.of_forall (fun x => klFun_nonneg (sq_nonneg _)))] at hLSI
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (div_nonneg (by norm_num) hρ.le)
    (integral_nonneg (fun x => sq_nonneg _)))).mp hLSI

set_option maxHeartbeats 1000000 in
/-- Unnormalized real logarithmic Sobolev for actual bounded positive
Lipschitz functions. The expression on the left is exactly Entμ(f²). -/
theorem logSobolev_unnormalized_bounded_positive_lipschitz_nobm
    
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hd : 0 < d)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {L : NNReal} (hLip : LipschitzWith L f) (M : ℝ) (hBound : ∀ x, ‖f x‖ ≤ M)
    (hpos : ∀ x,0 < f x) :
    let μ := gibbsMeasure volume V
    let A := ∫ x,f x^2 ∂μ
    (∫ x,klFun (f x^2) ∂μ)-A*Real.log A+(A-1) ≤
      (2/ρ)*∫ x,‖gradient f x‖^2 ∂μ := by
  let := hp
  let μ := gibbsMeasure volume V
  let A := ∫ x,f x^2 ∂μ
  have hfLp : MemLp f 2 μ := MemLp.of_bound hLip.continuous.aestronglyMeasurable M (Eventually.of_forall hBound)
  have hSqI : Integrable (fun x => f x^2) μ := hfLp.integrable_sq
  have hSqPos (x : E) : 0 < f x^2 := sq_pos_of_pos (hpos x)
  have hA : 0 < A := by
    apply (integral_pos_iff_support_of_nonneg (fun x => sq_nonneg (f x)) hSqI).mpr
    have he : Function.support (fun x => f x^2) = univ := by
      ext x; simp only [Function.mem_support,ne_eq,Set.mem_univ,iff_true]; exact (hSqPos x).ne'
    rw [he]; simp
  have hRoot : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  obtain ⟨u,hu,hDu⟩ := exists_gibbsSobolev_of_bounded_lipschitz hV hp ρ hρ hHess hLip M hBound
  have hU : ‖gibbsSobolevInclusion hV hp u‖^2 = A := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu] with x hx
    rw [hx,Real.inner_apply]; ring
  have hD : ‖gibbsSobolevDerivative hV hp u‖^2 = ∫ x,‖gradient f x‖^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hDu] with x hx
    rw [hx,real_inner_self_eq_norm_sq]
  let v := (Real.sqrt A)⁻¹ • u
  have hVNorm : ‖gibbsSobolevInclusion hV hp v‖^2 = 1 := by
    rw [map_smul,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,inv_pow,Real.sq_sqrt hA.le,hU]
    exact inv_mul_cancel₀ hA.ne'
  have hVD : ‖gibbsSobolevDerivative hV hp v‖^2 = (∫ x,‖gradient f x‖^2 ∂μ)/A := by
    rw [map_smul,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,inv_pow,Real.sq_sqrt hA.le,hD]
    ring
  have hVAe : gibbsSobolevInclusion hV hp v =ᵐ[μ] (fun x => f x/Real.sqrt A) := by
    change gibbsSobolevInclusion hV hp ((Real.sqrt A)⁻¹ • u) =ᵐ[μ] _
    rw [map_smul]
    filter_upwards [Lp.coeFn_smul (Real.sqrt A)⁻¹ (gibbsSobolevInclusion hV hp u),hu] with x hx huX
    rw [hx,Pi.smul_apply,smul_eq_mul,huX]
    ring
  have hLSI := logSobolev_closed_normalized_root_nobm hV hp hd ρ hρ hHess v hVNorm
  rw [hVD] at hLSI
  have hAE : (fun x => ENNReal.ofReal (klFun (gibbsSobolevInclusion hV hp v x^2))) =ᵐ[μ]
      (fun x => ENNReal.ofReal (klFun (f x^2/A))) := by
    filter_upwards [hVAe] with x hx
    rw [hx,div_pow,Real.sq_sqrt hA.le]
  rw [lintegral_congr_ae hAE] at hLSI
  have hGN (x : E) : ‖f x/Real.sqrt A‖ ≤ M/Real.sqrt A := by
    rw [norm_div,Real.norm_of_nonneg hRoot.le]
    gcongr
    exact hBound x
  have hKNI : Integrable (fun x => klFun (f x^2/A)) μ := by
    have hh := integrable_klFun_square_of_bounded μ (hLip.continuous.measurable.div_const (Real.sqrt A))
      (M/Real.sqrt A) hGN
    simpa only [div_pow,Real.sq_sqrt hA.le] using hh
  rw [← ofReal_integral_eq_lintegral_ofReal hKNI (Eventually.of_forall
    (fun x => klFun_nonneg (div_nonneg (sq_nonneg _) hA.le)))] at hLSI
  have hReal := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (div_nonneg (by norm_num) hρ.le)
    (div_nonneg (integral_nonneg (fun x => sq_nonneg _)) hA.le))).mp hLSI
  have hKLI := integrable_klFun_square_of_bounded μ hLip.continuous.measurable M hBound
  have hKI := integral_klFun_div_mass μ hSqI hSqPos hKLI hA
  change (∫ x,klFun (f x^2/A) ∂μ) = _ at hKI
  rw [hKI] at hReal
  have hh := mul_le_mul_of_nonneg_right hReal hA.le
  have heL : ((∫ x,klFun (f x^2) ∂μ)/A-Real.log A+(1-1/A))*A =
      (∫ x,klFun (f x^2) ∂μ)-A*Real.log A+(A-1) := by field_simp
  have heR : ((2/ρ)*((∫ x,‖gradient f x‖^2 ∂μ)/A))*A =
      (2/ρ)*(∫ x,‖gradient f x‖^2 ∂μ) := by field_simp
  rw [heL,heR] at hh
  exact hh

/-- The unnormalized inequality in the usual actual integral entropy
form, with all integrability supplied by bounded Lipschitz regularity. -/
theorem logSobolev_entropy_bounded_positive_lipschitz_nobm
    
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hd : 0 < d)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {L : NNReal} (hLip : LipschitzWith L f) (M : ℝ) (hBound : ∀ x, ‖f x‖ ≤ M)
    (hpos : ∀ x,0 < f x) :
    let μ := gibbsMeasure volume V
    let A := ∫ x,f x^2 ∂μ
    (∫ x,f x^2*Real.log (f x^2) ∂μ)-A*Real.log A ≤
      (2/ρ)*∫ x,‖gradient f x‖^2 ∂μ := by
  let := hp
  let μ := gibbsMeasure volume V
  have hh := logSobolev_unnormalized_bounded_positive_lipschitz_nobm hV hp hd ρ hρ hHess hLip M hBound hpos
  have hKL := integrable_klFun_square_of_bounded μ hLip.continuous.measurable M hBound
  have hSq : Integrable (fun x => f x^2) μ :=
    (MemLp.of_bound hLip.continuous.aestronglyMeasurable M (Eventually.of_forall hBound) : MemLp f 2 μ).integrable_sq
  have hEq (x : E) : f x^2*Real.log (f x^2) = klFun (f x^2)+f x^2-1 := by rw [klFun_apply]; ring
  have hIntegral : (∫ x,f x^2*Real.log (f x^2) ∂μ) =
      (∫ x,klFun (f x^2) ∂μ)+(∫ x,f x^2 ∂μ)-1 := by
    have hs := integral_sub (hKL.add hSq) (integrable_const (1:ℝ))
    have ha := integral_add hKL hSq
    simp only [Pi.add_def] at hs ha
    rw [integral_congr_ae (Eventually.of_forall hEq),hs,ha,integral_const]
    simp only [measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]
  dsimp only at hh ⊢
  rw [hIntegral]
  linarith


end CutoffRigidity

end Seg1

section Seg2

namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped Topology NNReal ENNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 1000000 in
/-- The actual exponential-test LSI needed by Hamilton–Jacobi
hypercontractivity, with genuine a.e. gradient chain rule and domain. -/
theorem logSobolev_exp_bounded_lipschitz_nobm
    
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hd : 0 < d)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {L : NNReal} (hLip : LipschitzWith L f) (M : ℝ) (hBound : ∀ x,|f x| ≤ M)
    (a : ℝ) (ha : 0 ≤ a) :
    let μ := gibbsMeasure volume V
    let Z := ∫ x,Real.exp (a*f x) ∂μ
    (∫ x,Real.exp (a*f x)*(a*f x) ∂μ)-Z*Real.log Z ≤
      (a^2/(2*ρ))*∫ x,Real.exp (a*f x)*‖gradient f x‖^2 ∂μ := by
  let := hp
  let μ := gibbsMeasure volume V
  let ψ := fun x => Real.exp ((a/2)*f x)
  obtain ⟨C,hC⟩ := exists_lipschitzWith_exp_mul_bounded hLip M hBound (show 0 ≤ a/2 by positivity)
  have hψB (x : E) : ‖ψ x‖ ≤ Real.exp ((a/2)*M) := by
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_le.mp (hBound x)).2 (by positivity))
  have hSq (x : E) : ψ x^2 = Real.exp (a*f x) := by
    dsimp only [ψ]
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hEntropy (x : E) : ψ x^2*Real.log (ψ x^2) = Real.exp (a*f x)*(a*f x) := by
    rw [hSq,Real.log_exp]
  have hGrad : (fun x => ‖gradient ψ x‖^2) =ᵐ[μ]
      (fun x => (a^2/4)*(Real.exp (a*f x)*‖gradient f x‖^2)) := by
    filter_upwards [(gibbsMeasure_absolutelyContinuous volume V).ae_le
      (hLip.ae_differentiableAt (μ := volume))] with x hx
    rw [gradient_exp_mul_at hx (a/2),norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,mul_pow]
    change (a/2)^2*(ψ x^2)*‖gradient f x‖^2 = _
    rw [hSq]
    ring
  have hh := logSobolev_entropy_bounded_positive_lipschitz_nobm hV hp hd ρ hρ hHess
    hC (Real.exp ((a/2)*M)) hψB (fun x => Real.exp_pos _)
  dsimp only at hh ⊢
  rw [integral_congr_ae (Eventually.of_forall hEntropy),
    integral_congr_ae (Eventually.of_forall hSq),integral_congr_ae hGrad,integral_const_mul] at hh
  convert hh using 1
  ring


end CutoffRigidity

end Seg2

section Seg3

namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped Topology NNReal ENNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 1000000 in
/-- The true exponential moment satisfies the differential inequality
in the Hamilton–Jacobi hypercontractivity proof, a.e. in positive time.
No time derivative, HJ equation, or function-domain premise is assumed. -/
theorem hopfLaxExponentialMoment_entropy_derivative_nonpos_ae_nobm
    
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hd : 0 < d)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {L : NNReal} (hLip : LipschitzWith L f) (M : ℝ) (hBound : ∀ x,|f x| ≤ M)
    {a : ℝ} (ha : 0 < a) :
    ∀ᵐ t ∂volume.restrict (Ioi a),
      t*deriv (hopfLaxExponentialMoment (gibbsMeasure volume V) ρ f) t -
        hopfLaxExponentialMoment (gibbsMeasure volume V) ρ f t *
          Real.log (hopfLaxExponentialMoment (gibbsMeasure volume V) ρ f t) ≤ 0 := by
  let := hp
  let μ := gibbsMeasure volume V
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hBound 0)
  filter_upwards [hasDerivAt_integral_exp_hopfLax_ae μ (gibbsMeasure_absolutelyContinuous volume V)
    hρ.le ha hBound hLip,ae_restrict_mem measurableSet_Ioi] with t hD ht
  have htpos : 0 < t := ha.trans ht
  let q := hopfLax t f
  let e := fun x => Real.exp (ρ*t*q x)
  have hqLip := lipschitzWith_hopfLax htpos.le hBound hLip
  have hqB (x : E) : |q x| ≤ M := by
    have hh := hopfLax_bounds htpos.le hBound x
    exact abs_le.mpr ⟨hh.1,hh.2.trans (abs_le.mp (hBound x)).2⟩
  have heB (x : E) : e x ≤ Real.exp (ρ*t*M) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_le.mp (hqB x)).2 (by positivity))
  have heMeas : Measurable e := Real.continuous_exp.measurable.comp
    (hqLip.continuous.measurable.const_mul (ρ*t))
  have hFI : Integrable (fun x => e x*q x) μ := by
    apply (integrable_const (Real.exp (ρ*t*M)*M)).mono' (heMeas.mul hqLip.continuous.measurable).aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    change ‖e x*q x‖ ≤ Real.exp (ρ*t*M)*M
    rw [norm_mul,Real.norm_of_nonneg (Real.exp_nonneg _),Real.norm_eq_abs]
    exact mul_le_mul (heB x) (hqB x) (abs_nonneg _) (Real.exp_nonneg _)
  have hGI : Integrable (fun x => e x*‖gradient q x‖^2) μ := by
    apply (integrable_const (Real.exp (ρ*t*M)*(L:ℝ)^2)).mono'
      (heMeas.mul ((measurable_euclidean_gradient q).norm.pow_const 2)).aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    change ‖e x*‖gradient q x‖^2‖ ≤ Real.exp (ρ*t*M)*(L:ℝ)^2
    rw [norm_mul,Real.norm_of_nonneg (Real.exp_nonneg _),Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_mul (heB x)
      ((sq_le_sq₀ (norm_nonneg _) L.coe_nonneg).mpr (norm_gradient_le_of_lipschitz hqLip x))
      (sq_nonneg _) (Real.exp_nonneg _)
  have hDeriv : deriv (hopfLaxExponentialMoment μ ρ f) t =
      ρ*(∫ x,e x*q x ∂μ)-(ρ*t/2)*(∫ x,e x*‖gradient q x‖^2 ∂μ) := by
    change HasDerivAt (hopfLaxExponentialMoment μ ρ f) _ t at hD
    rw [hD.deriv]
    change (∫ x,e x*(ρ*q x-ρ*t*‖gradient q x‖^2/2) ∂μ) = _
    have heq (x : E) : e x*(ρ*q x-ρ*t*‖gradient q x‖^2/2) =
        ρ*(e x*q x)-(ρ*t/2)*(e x*‖gradient q x‖^2) := by ring
    rw [integral_congr_ae (Eventually.of_forall heq),
      integral_sub (hFI.const_mul ρ) (hGI.const_mul (ρ*t/2)),integral_const_mul,integral_const_mul]
  have hLSI := logSobolev_exp_bounded_lipschitz_nobm hV hp hd ρ hρ hHess hqLip M hqB (ρ*t) (by positivity)
  dsimp only at hLSI
  have hPoint (x : E) : Real.exp (ρ*t*q x)*(ρ*t*q x) = (ρ*t)*(e x*q x) := by dsimp only [e]; ring
  rw [integral_congr_ae (Eventually.of_forall hPoint),integral_const_mul] at hLSI
  change t*deriv (hopfLaxExponentialMoment μ ρ f) t-
    hopfLaxExponentialMoment μ ρ f t*Real.log (hopfLaxExponentialMoment μ ρ f t) ≤ 0
  rw [hDeriv]
  have hCoeff : (ρ*t)^2/(2*ρ) = ρ*t^2/2 := by field_simp
  rw [hCoeff] at hLSI
  change (ρ*t)*(∫ x,e x*q x ∂μ)-hopfLaxExponentialMoment μ ρ f t*
      Real.log (hopfLaxExponentialMoment μ ρ f t) ≤ (ρ*t^2/2)*(∫ x,e x*‖gradient q x‖^2 ∂μ) at hLSI
  nlinarith only [hLSI]


end CutoffRigidity

end Seg3

section Seg4

namespace CutoffRigidity
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The true logarithmic exponential moment divided by time decreases
on positive times, with all AC and derivative conditions proved. -/
theorem antitoneOn_log_hopfLaxExponentialMoment_div_time_nobm
    
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hd : 0 < d)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {L : NNReal} (hLip : LipschitzWith L f) (M : ℝ) (hBound : ∀ x,|f x| ≤ M) :
    AntitoneOn (fun t => Real.log (hopfLaxExponentialMoment (gibbsMeasure volume V) ρ f t)/t) (Ioi 0) := by
  let := hp
  let μ := gibbsMeasure volume V
  let Z := hopfLaxExponentialMoment μ ρ f
  intro s hs t ht hst
  change 0 < s at hs
  change 0 < t at ht
  apply absolutelyContinuousOnInterval_le_left_of_deriv_nonpos_ae hst
    (absolutelyContinuousOnInterval_log_hopfLaxExponentialMoment_div_time μ hρ.le hs hst hBound hLip)
  have hAE : ∀ᵐ r ∂volume.restrict (Ioi (s/2)), deriv (fun r => Real.log (Z r)/r) r ≤ 0 := by
    filter_upwards [hasDerivAt_integral_exp_hopfLax_ae μ (gibbsMeasure_absolutelyContinuous volume V)
      hρ.le (show 0<s/2 by linarith) hBound hLip,
      hopfLaxExponentialMoment_entropy_derivative_nonpos_ae_nobm hV hp hd ρ hρ hHess hLip M hBound
        (show 0<s/2 by linarith),ae_restrict_mem measurableSet_Ioi] with r hD hI hr
    change s/2 < r at hr
    change r*deriv Z r-Z r*Real.log (Z r) ≤ 0 at hI
    have hrpos : 0 < r := lt_trans (by linarith : 0<s/2) hr
    have hZpos : 0 < Z r := hopfLaxExponentialMoment_pos μ hρ.le hrpos.le hBound hLip
    change HasDerivAt Z _ r at hD
    have hDeriv := (hD.log hZpos.ne').div (hasDerivAt_id r) hrpos.ne'
    simp only [Pi.div_def,id_eq] at hDeriv
    rw [hDeriv.deriv]
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    simp only [mul_one]
    have hDiv : (r*deriv Z r)/Z r ≤ Real.log (Z r) :=
      (div_le_iff₀ hZpos).mpr (by nlinarith only [hI])
    rw [hD.deriv] at hDiv
    have hEq : (r*(∫ x,Real.exp (ρ*r*hopfLax r f x)*
        (ρ*hopfLax r f x-ρ*r*‖gradient (hopfLax r f) x‖^2/2) ∂μ))/Z r =
      ((∫ x,Real.exp (ρ*r*hopfLax r f x)*
        (ρ*hopfLax r f x-ρ*r*‖gradient (hopfLax r f) x‖^2/2) ∂μ)/Z r)*r := by ring
    rw [hEq] at hDiv
    exact sub_nonpos.mpr hDiv
  exact ae_restrict_of_ae_restrict_of_subset (fun r hr => by
    change s < r ∧ r ≤ t at hr
    change s/2 < r
    linarith [hr.1]) hAE

/-- The exact genuine Hamilton–Jacobi exponential inequality used to
obtain Talagrand transport. No infimum-convolution or LSI bound is assumed. -/
theorem hopfLax_exponential_integral_le_nobm
    
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hd : 0 < d)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {L : NNReal} (hLip : LipschitzWith L f) (M : ℝ) (hBound : ∀ x,|f x| ≤ M)
    (T : ℝ) (hT : 0 < T) :
    (∫ x,Real.exp (ρ*T*hopfLax T f x) ∂gibbsMeasure volume V) ≤
      Real.exp (ρ*T*(∫ x,f x ∂gibbsMeasure volume V)) := by
  let := hp
  let μ := gibbsMeasure volume V
  let Z := hopfLaxExponentialMoment μ ρ f
  let F := fun t => Real.log (Z t)/t
  have hlim := tendsto_log_hopfLaxExponentialMoment_div_time_zero μ hρ.le hBound hLip
  have hfilt : 𝓝[>] (0:ℝ) ≤ 𝓝[≠] (0:ℝ) := nhdsWithin_mono 0
    (fun r hr => show r ∈ ({0}:Set ℝ)ᶜ from ne_of_gt hr)
  have hlimPos := hlim.mono_left hfilt
  have hle : F T ≤ ρ*∫ x,f x ∂μ := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlimPos
    filter_upwards [(eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with r hr hrpos
    exact antitoneOn_log_hopfLaxExponentialMoment_div_time_nobm hV hp hd ρ hρ hHess hLip M hBound hrpos hT hr.le
  have hLog : Real.log (Z T) ≤ ρ*T*(∫ x,f x ∂μ) := by
    have hh := (div_le_iff₀ hT).mp hle
    nlinarith only [hh]
  have hZ := hopfLaxExponentialMoment_pos μ hρ.le hT.le hBound hLip
  change Z T ≤ _
  change 0 < Z T at hZ
  rw [← Real.exp_log hZ]
  exact Real.exp_le_exp.mpr hLog


end CutoffRigidity

end Seg4

section Seg5

namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped Topology NNReal ENNReal BoundedContinuousFunction
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 1200000 in
/-- The actual quadratic transport cost is bounded by actual KL for every
initial probability law, including singular and infinite-entropy laws. -/
theorem squaredWasserstein_le_two_div_curvature_klDiv_nobm
    
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hd : 0 < d)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] :
    squaredWasserstein ν (gibbsMeasure volume V) ≤
      ENNReal.ofReal (2/ρ)*klDiv ν (gibbsMeasure volume V) := by
  let := hp
  let μ := gibbsMeasure volume V
  by_cases hFin : klDiv ν μ = ⊤
  · rw [hFin,ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (div_pos (by norm_num) hρ)))]
    exact le_top
  have hBudget : squaredWasserstein ν μ ≤ ENNReal.ofReal ((2/ρ)*(klDiv ν μ).toReal) := by
    apply squaredWasserstein_le_of_lipschitz_dual_budget ν μ
    intro f g L J hf hg hdual
    let a := ρ/2
    let G := ∫ y,g y ∂μ
    let ψ := fun y : E => -g y
    let Q := hopfLax (1/2:ℝ) ψ
    let φ := fun x : E => a*f x+a*G
    have ha : 0 < a := by dsimp only [a]; positivity
    have hψB (x : E) : |ψ x| ≤ ‖g‖ := by
      simpa only [ψ,abs_neg,Real.norm_eq_abs] using g.norm_coe_le_norm x
    have hQCont := (lipschitzWith_hopfLax (by norm_num : (0:ℝ) ≤ 1/2) hψB hg.neg).continuous
    have hQUpper (x : E) : Q x ≤ ‖g‖ :=
      (hopfLax_bounds (by norm_num : (0:ℝ) ≤ 1/2) hψB x).2.trans (abs_le.mp (hψB x)).2
    have hfQ (x : E) : f x ≤ Q x := by
      change f x ≤ hopfLax (1/2:ℝ) ψ x
      rw [hopfLax,ite_eq_left (by norm_num : (0:ℝ)<1/2)]
      apply le_csInf (range_nonempty _)
      rintro _ ⟨y,rfl⟩
      have hh := hdual x y
      dsimp only [ψ]
      norm_num
      linarith
    have hPhiMeas : Measurable φ := (f.continuous.measurable.const_mul a).add_const (a*G)
    have hPhiB (x : E) : ‖φ x‖ ≤ a*‖f‖+|a*G| := by
      apply (norm_add_le _ _).trans
      rw [norm_mul,Real.norm_of_nonneg ha.le,Real.norm_eq_abs]
      exact add_le_add (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) ha.le) le_rfl
    have hEQI : Integrable (fun x => Real.exp (a*Q x)) μ := by
      apply (integrable_const (Real.exp (a*‖g‖))).mono'
        (Real.continuous_exp.comp (hQCont.const_mul a)).aestronglyMeasurable
      apply Eventually.of_forall
      intro x
      change ‖Real.exp (a*Q x)‖ ≤ Real.exp (a*‖g‖)
      rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hQUpper x) ha.le)
    have hEφI : Integrable (fun x => Real.exp (φ x)) μ := by
      apply (integrable_const (Real.exp (a*‖f‖+|a*G|))).mono' hPhiMeas.exp.aestronglyMeasurable
      apply Eventually.of_forall
      intro x
      rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hPhiB x))
    have hMom := hopfLax_exponential_integral_le_nobm hV hp hd ρ hρ hHess hg.neg ‖g‖ hψB
      (1/2:ℝ) (by norm_num)
    have hHalf : ρ*(1/2:ℝ) = a := by dsimp only [a]; ring
    rw [hHalf] at hMom
    change (∫ x,Real.exp (a*Q x) ∂μ) ≤ Real.exp (a*(∫ y,-g y ∂μ)) at hMom
    rw [integral_neg,mul_neg] at hMom
    have hExp : (∫ x,Real.exp (φ x) ∂μ) ≤ 1 := by
      have hPoint (x : E) : Real.exp (φ x) ≤ Real.exp (a*G)*Real.exp (a*Q x) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        dsimp only [φ]
        nlinarith only [mul_le_mul_of_nonneg_left (hfQ x) ha.le]
      have hh := integral_mono hEφI (hEQI.const_mul (Real.exp (a*G))) hPoint
      rw [integral_const_mul] at hh
      calc
        _ ≤ Real.exp (a*G)*(∫ x,Real.exp (a*Q x) ∂μ) := hh
        _ ≤ Real.exp (a*G)*Real.exp (-(a*G)) := mul_le_mul_of_nonneg_left hMom (Real.exp_nonneg _)
        _ = 1 := by rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
    have hEnt := (ENNReal.ofReal_le_iff_le_toReal hFin).mp
      (relativeEntropyTest_le_klDiv ν μ hPhiMeas ⟨_,hPhiB⟩)
    have hfI : Integrable (fun x => f x) ν :=
      (integrable_const ‖f‖).mono' f.continuous.aestronglyMeasurable (Eventually.of_forall (f.norm_coe_le_norm))
    have hPhiInt : (∫ x,φ x ∂ν) = a*(∫ x,f x ∂ν)+a*G := by
      have hh := integral_add (hfI.const_mul a) (integrable_const (a*G))
      rw [hh,integral_const_mul,integral_const]
      simp only [measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]
    rw [relativeEntropyTest,hPhiInt] at hEnt
    have hScale : a*((∫ x,f x ∂ν)+(∫ y,g y ∂μ)) ≤ (klDiv ν μ).toReal := by
      change a*((∫ x,f x ∂ν)+G) ≤ _
      linarith
    have he : (klDiv ν μ).toReal/a = (2/ρ)*(klDiv ν μ).toReal := by dsimp only [a]; field_simp
    rw [← he]
    exact (le_div_iff₀ ha).mpr (by nlinarith only [hScale])
  apply hBudget.trans_eq
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2/ρ),ENNReal.ofReal_toReal hFin]

/-- The exact form written in the paper: curvature times actual squared
Wasserstein distance is at most twice actual relative entropy. -/
theorem curvature_mul_squaredWasserstein_le_two_klDiv_nobm
    
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hd : 0 < d)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] :
    ENNReal.ofReal ρ*squaredWasserstein ν (gibbsMeasure volume V) ≤
      2*klDiv ν (gibbsMeasure volume V) := by
  have hh := squaredWasserstein_le_two_div_curvature_klDiv_nobm hV hp hd ρ hρ hHess ν
  have he : ENNReal.ofReal ρ*ENNReal.ofReal (2/ρ) = 2 := by
    rw [← ENNReal.ofReal_mul hρ.le]
    have hr : ρ*(2/ρ) = 2 := by field_simp
    rw [hr]
    norm_num
  have hmul := mul_le_mul' (le_refl (ENNReal.ofReal ρ)) hh
  simpa only [← mul_assoc,he] using hmul


end CutoffRigidity

end Seg5

section Seg6

namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The source logarithmic Sobolev inequality for every actual probability
law, using the genuine closed-gradient relative Fisher functional. -/
theorem logSobolev_relativeFisherInformation_nobm
     {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] :
    klDiv ν (gibbsMeasure volume V) ≤
      relativeFisherInformation hV hp ν / ENNReal.ofReal (2 * ρ) := by
  let := hp
  let μ := gibbsMeasure volume V
  let R := squareRootRNDensityLp ν μ
  let G := closedGibbsGradient hV hp
  by_cases hAC : ν ≪ μ
  · by_cases hD : R ∈ G.domain
    · let D := G ⟨R, hD⟩
      have hgraph : (R, D) ∈ G.graph := G.mem_graph ⟨R, hD⟩
      let v : gibbsSobolevGraph hV hp := ⟨WithLp.toLp 2 (R, D), hgraph⟩
      have hIncl : gibbsSobolevInclusion hV hp v = R := rfl
      have hDeriv : gibbsSobolevDerivative hV hp v = D := rfl
      have hRAE : R =ᵐ[μ] squareRootRNDensity ν μ := (squareRootRNDensity_memLp ν μ).coeFn_toLp
      have hNorm : ‖R‖ ^ 2 = 1 := by
        rw [← real_inner_self_eq_norm_sq, L2.inner_def]
        calc
          _ = ∫ x, squareRootRNDensity ν μ x ^ 2 ∂μ := by
            apply integral_congr_ae
            filter_upwards [hRAE] with x hx
            rw [hx, Real.inner_apply]
            ring
          _ = ν.real Set.univ := integral_squareRootRNDensity_sq ν μ hAC
          _ = 1 := by simp
      have hRoot := logSobolev_closed_normalized_root_nobm hV hp hd ρ hρ hHess v
        (hIncl.symm ▸ hNorm)
      rw [hIncl, hDeriv] at hRoot
      have hKL : klDiv ν μ = ∫⁻ x, ENNReal.ofReal (klFun (R x ^ 2)) ∂μ := by
        rw [klDiv_eq_lintegral_klFun_of_ac hAC]
        apply lintegral_congr_ae
        filter_upwards [hRAE] with x hx
        rw [hx, squareRootRNDensity_sq]
      have hFI := relativeFisherInformation_eq_closed_energy hV hp ν hAC hD
      change relativeFisherInformation hV hp ν = ENNReal.ofReal (4 * ‖D‖ ^ 2) at hFI
      change klDiv ν μ ≤ _
      rw [hKL, hFI]
      apply hRoot.trans_eq
      rw [← ENNReal.ofReal_div_of_pos (show 0 < 2 * ρ by positivity)]
      congr 1
      field_simp
      ring
    · have hTop : relativeFisherInformation hV hp ν = ⊤ := by
        have hAC' : ν ≪ gibbsMeasure volume V := hAC
        have hD' : squareRootRNDensityLp ν (gibbsMeasure volume V) ∉
            (closedGibbsGradient hV hp).domain := hD
        simp only [relativeFisherInformation, hAC', dite_true, hD', dite_false]
      rw [hTop, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top]
      exact le_top
  · rw [relativeFisherInformation_eq_top_of_not_ac hV hp ν hAC,
      ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top]
    exact le_top


end CutoffRigidity

end Seg6
