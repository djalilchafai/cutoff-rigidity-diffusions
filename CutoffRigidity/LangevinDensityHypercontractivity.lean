module
public import CutoffRigidity.LangevinGrossHypercontractivity
public import CutoffRigidity.LangevinChiSquareBound
public import CutoffRigidity.LangevinL1Duality
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-! # Hypercontractive Lᵖ bounds for actual Langevin transition densities

Gross's compact-test bound extends to all of Gibbs L² by smooth compact
approximation, the actual L² contraction and Fatou's lemma. The genuine
Markov law and reversibility identify the time-`r+s` RN density with the
time-`s` average of the time-`r` density, so the density error in
`L^{1+e^{2ρs}}` is bounded by the L² density error at time `r`.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 1000000 in
/-- Gross hypercontractivity `‖P_t f‖_{p(t)} ≤ ‖f‖_2` for every actual
Gibbs-L² function, from compact tests by Fatou's lemma. -/
theorem eLpNorm_langevinKernel_integral_le_of_memLp
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hd : 0 < d)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E,ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {f : E → ℝ} (hf : MemLp f 2 (gibbsMeasure volume V)) {t : ℝ} (ht : 0 ≤ t) :
    eLpNorm (fun x => ∫ z, f z ∂langevinKernel V B P t.toNNReal x)
      (ENNReal.ofReal (grossExponent ρ t)) (gibbsMeasure volume V) ≤
      eLpNorm f 2 (gibbsMeasure volume V) := by
  let := hp
  let μ := gibbsMeasure volume V
  let K := langevinKernel V B P t.toNNReal
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t.toNNReal
  have hInv : K ∘ₘ μ = μ := langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess t.toNNReal
  let T := invariantKernelL2Operator K hInv
  choose g hgc hgs hgf using fun n : ℕ =>
    hf.exist_eLpNorm_sub_le (by norm_num) (by norm_num) (by positivity : (0:ℝ) < 1/((n:ℝ)+1))
  have hg2 (n : ℕ) : ContDiff ℝ 2 (g n) := (hgs n).of_le (WithTop.coe_le_coe.mpr le_top)
  have hgLp (n : ℕ) : MemLp (g n) 2 μ := (hg2 n).continuous.memLp_of_hasCompactSupport (hgc n)
  let G := fun n => (hgLp n).toLp (g n)
  let u := hf.toLp f
  have hGu : Tendsto G atTop (𝓝 u) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun n => dist_nonneg) _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    rw [Lp.dist_def, eLpNorm_congr_ae ((hgLp n).coeFn_toLp.sub hf.coeFn_toLp), eLpNorm_sub_comm]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hgf n)
  have hTG : Tendsto (fun n => T (G n)) atTop (𝓝 (T u)) := (T.continuous.tendsto u).comp hGu
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hTG).exists_seq_tendsto_ae
  have hTGn (n : ℕ) : (T (G n) : E → ℝ) =ᵐ[μ] fun x => ∫ z, g n z ∂K x :=
    (invariantKernelL2Operator_coeFn K hInv (G n)).trans
      (invariantKernel_integral_congr_ae K hInv (hgLp n).coeFn_toLp)
  have hTu : (T u : E → ℝ) =ᵐ[μ] fun x => ∫ z, f z ∂K x :=
    (invariantKernelL2Operator_coeFn K hInv u).trans
      (invariantKernel_integral_congr_ae K hInv hf.coeFn_toLp)
  have hlimAE : ∀ᵐ x ∂μ, Tendsto (fun i => ∫ z, g (ns i) z ∂K x) atTop (𝓝 (∫ z, f z ∂K x)) := by
    have hall := ae_all_iff.mpr (fun n => hTGn n)
    filter_upwards [hae, hall, hTu] with x hx hall hu
    rw [← hu]
    refine hx.congr (fun i => ?_)
    exact hall (ns i)
  have hFatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := ENNReal.ofReal (grossExponent ρ t))
    (fun i => ((Lp.aestronglyMeasurable (T (G (ns i)))).congr (hTGn (ns i))))
    (fun x => ∫ z, f z ∂K x) ((Lp.aestronglyMeasurable (T u)).congr hTu) hlimAE
  have hStep (i : ℕ) : eLpNorm (fun x => ∫ z, g (ns i) z ∂K x) (ENNReal.ofReal (grossExponent ρ t)) μ ≤
      eLpNorm f 2 μ + ENNReal.ofReal (1/((ns i:ℝ)+1)) := by
    apply (eLpNorm_langevinKernel_compact_test_le hB hV hp hd (hg2 (ns i)) (hgc (ns i)) ρ hρ hHess ht).trans
    have he : g (ns i) = f + (g (ns i) - f) := by abel
    calc
      eLpNorm (g (ns i)) 2 μ = eLpNorm (f + (g (ns i) - f)) 2 μ := by rw [← he]
      _ ≤ eLpNorm f 2 μ + eLpNorm (g (ns i) - f) 2 μ :=
        eLpNorm_add_le (by norm_num)
      _ ≤ _ := by rw [eLpNorm_sub_comm]; exact add_le_add le_rfl (hgf (ns i))
  have hlimB : Tendsto (fun i => eLpNorm f 2 μ + ENNReal.ofReal (1/((ns i:ℝ)+1))) atTop
      (𝓝 (eLpNorm f 2 μ + ENNReal.ofReal 0)) := by
    apply tendsto_const_nhds.add
    exact ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat.comp hns.tendsto_atTop)
  rw [ENNReal.ofReal_zero, add_zero] at hlimB
  calc
    _ ≤ _ := hFatou
    _ ≤ atTop.liminf (fun i => eLpNorm f 2 μ + ENNReal.ofReal (1/((ns i:ℝ)+1))) :=
      liminf_le_liminf (Eventually.of_forall hStep)
    _ = _ := hlimB.liminf_eq

set_option maxHeartbeats 1000000 in
/-- The genuine Markov law and actual reversibility identify the
time-`r+s` RN density with the time-`s` average of the time-`r` density. -/
theorem langevinKernel_rnDeriv_add_ae_eq
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E,ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x : E) {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) :
    (fun y => ((langevinKernel V B P (r+s).toNNReal x).rnDeriv (gibbsMeasure volume V) y).toReal)
      =ᵐ[gibbsMeasure volume V] fun y =>
        ∫ z, ((langevinKernel V B P r.toNNReal x).rnDeriv (gibbsMeasure volume V) z).toReal
          ∂langevinKernel V B P s.toNNReal y := by
  let := hp
  let μ := gibbsMeasure volume V
  let ν := langevinKernel V B P r.toNNReal x
  let K := langevinKernel V B P s.toNNReal
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess s.toNNReal
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess r.toNNReal
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess (r+s).toNNReal
  have hInv : K ∘ₘ μ = μ := langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess s.toNNReal
  let f := fun z => (ν.rnDeriv μ z).toReal
  have hfm : Measurable f := (Measure.measurable_rnDeriv ν μ).ennreal_toReal
  have hfn : ∀ z, 0 ≤ f z := fun z => ENNReal.toReal_nonneg
  have hfI : Integrable f μ := Measure.integrable_toReal_rnDeriv
  have hAC : ν ≪ μ := langevinKernel_absolutelyContinuous_gibbs hB hV hp ρ hρ hHess x r hr
  have hAC2 : langevinKernel V B P (r+s).toNNReal x ≪ μ :=
    langevinKernel_absolutelyContinuous_gibbs hB hV hp ρ hρ hHess x (r+s) (by linarith)
  obtain ⟨hRN, -⟩ := langevinKernel_rnDeriv_memLp_two hB hV hp ρ hρ hHess r hr x
  have hPf : MemLp (fun y => ∫ z, f z ∂K y) 2 μ :=
    (invariantKernel_memLp_integral K hInv (hRN.toLp f)).ae_eq
      (invariantKernel_integral_congr_ae K hInv hRN.coeFn_toLp)
  have hPfI : Integrable (fun y => ∫ z, f z ∂K y) μ := hPf.integrable (by norm_num)
  have hcomp : langevinKernel V B P (r+s).toNNReal = K ∘ₖ langevinKernel V B P r.toNNReal := by
    rw [Real.toNNReal_add hr.le hs, langevinKernel_comp hB hV ρ hρ.le hHess]
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro A _ _; exact Measure.integrable_toReal_rnDeriv.integrableOn
  · intro A _ _; exact hPfI.integrableOn
  intro A hA _
  rw [Measure.setIntegral_toReal_rnDeriv hAC2]
  have hind : Integrable (A.indicator (1 : E → ℝ)) ((K ∘ₖ langevinKernel V B P r.toNNReal) x) :=
    (integrable_const (1:ℝ)).indicator hA
  have hbd : ∃ N : ℝ, ∀ y, ‖A.indicator (1 : E → ℝ) y‖ ≤ N :=
    ⟨1, fun y => by by_cases hy : y ∈ A <;> simp [hy]⟩
  calc
    (langevinKernel V B P (r+s).toNNReal x).real A
        = ∫ z, A.indicator (1 : E → ℝ) z ∂(langevinKernel V B P (r+s).toNNReal x) :=
          (integral_indicator_one hA).symm
    _ = ∫ y, (∫ z, A.indicator (1 : E → ℝ) z ∂K y) ∂ν := by
          rw [hcomp]; exact Kernel.integral_comp hind
    _ = ∫ y, f y * (∫ z, A.indicator (1 : E → ℝ) z ∂K y) ∂μ := (integral_rnDeriv_smul hAC).symm
    _ = ∫ y, (∫ z, f z ∂K y) * A.indicator (1 : E → ℝ) y ∂μ :=
          langevinKernel_integral_mul_comm_integrable hB hV hp ρ hρ hHess hfm hfn hfI
            (measurable_const.indicator hA) hbd s.toNNReal
    _ = ∫ y in A, (∫ z, f z ∂K y) ∂μ := by
          rw [← integral_indicator hA]
          congr 1
          funext y
          by_cases hy : y ∈ A <;> simp [hy]

set_option maxHeartbeats 800000 in
/-- Hypercontractive density regularization: the actual density error at
time `r+s` in `L^{1+e^{2ρs}}` is at most the actual L² error at time `r`. -/
theorem relativeLpDistance_langevinKernel_add_le
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hd : 0 < d)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E,ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x : E) {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) :
    relativeLpDistance (langevinKernel V B P (r+s).toNNReal x) (gibbsMeasure volume V)
        (ENNReal.ofReal (grossExponent ρ s)) ≤
      relativeLpDistance (langevinKernel V B P r.toNNReal x) (gibbsMeasure volume V) 2 := by
  let := hp
  let μ := gibbsMeasure volume V
  let ν := langevinKernel V B P r.toNNReal x
  let K := langevinKernel V B P s.toNNReal
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess s.toNNReal
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess r.toNNReal
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess (r+s).toNNReal
  have hInv : K ∘ₘ μ = μ := langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess s.toNNReal
  let f := fun z => (ν.rnDeriv μ z).toReal
  have hfI : Integrable f μ := Measure.integrable_toReal_rnDeriv
  have hAC : ν ≪ μ := langevinKernel_absolutelyContinuous_gibbs hB hV hp ρ hρ hHess x r hr
  have hAC2 : langevinKernel V B P (r+s).toNNReal x ≪ μ :=
    langevinKernel_absolutelyContinuous_gibbs hB hV hp ρ hρ hHess x (r+s) (by linarith)
  obtain ⟨hRN, -⟩ := langevinKernel_rnDeriv_memLp_two hB hV hp ρ hρ hHess r hr x
  rw [relativeLpDistance_eq_eLpNorm _ _ hAC2, relativeLpDistance_eq_eLpNorm _ _ hAC]
  have hf1 : MemLp (fun z => f z - 1) 2 μ := by
    simpa only [Pi.sub_def] using hRN.sub (memLp_const (1:ℝ))
  have hae : (fun y => ((langevinKernel V B P (r+s).toNNReal x).rnDeriv μ y).toReal - 1)
      =ᵐ[μ] fun y => ∫ z, (f z - 1) ∂K y := by
    filter_upwards [langevinKernel_rnDeriv_add_ae_eq hB hV hp ρ hρ hHess x hr hs,
      invariantKernel_integrable_ae K hInv hfI] with y hy hint
    rw [hy, integral_sub hint (integrable_const 1)]
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    rfl
  rw [eLpNorm_congr_ae hae]
  exact eLpNorm_langevinKernel_integral_le_of_memLp hB hV hp hd ρ hρ hHess hf1 hs

end CutoffRigidity
