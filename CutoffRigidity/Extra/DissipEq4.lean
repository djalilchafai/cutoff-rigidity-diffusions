module

public import CutoffRigidity.Extra.Dissip2
public import CutoffRigidity.Extra.DissipEq2
public import CutoffRigidity.Extra.DissipEq3

/-! # Reverse drop inequality `H(λ) ≤ H(λ P_u) + u I(λ)` (carrier level)

For an arbitrary probability law `λ` of finite entropy and finite Fisher information and `u > 0`,
`H(λ|μ) ≤ H(λ P_u|μ) + u I(λ|μ)`. Proof: Fisher-controlled core approximants (`DissipEq3`), the
exact identity in the core class together with Fisher decay, and the lower semicontinuity of the
entropy drop (`DissipEq2`).
-/

public section

namespace CutoffRigidity.DissipEq

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal Topology
open CutoffRigidity CutoffRigidity.Dissip

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- `L¹` convergence implies a.e. convergence of a subsequence, jointly for `f_n` and `K f_n`. -/
theorem exists_subseq_ae {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {K : Kernel X X} [IsMarkovKernel K] (hInv : K ∘ₘ μ = μ)
    {f : ℕ → X → ℝ} {f₀ : X → ℝ} (hm : ∀ n, Measurable (f n)) (hm₀ : Measurable f₀)
    (hi : ∀ n, Integrable (f n) μ) (hi₀ : Integrable f₀ μ)
    (hL1 : Tendsto (fun n => ∫ x, ‖f n x - f₀ x‖ ∂μ) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      (∀ᵐ x ∂μ, Tendsto (fun i => f (ns i) x) atTop (𝓝 (f₀ x))) ∧
      (∀ᵐ y ∂μ, Tendsto (fun i => kavg K (f (ns i)) y) atTop (𝓝 (kavg K f₀ y))) := by
  -- convergence in measure from `L¹` convergence
  have key : ∀ (g : ℕ → X → ℝ) (g₀ : X → ℝ), (∀ n, Integrable (g n) μ) → Integrable g₀ μ →
      Tendsto (fun n => ∫ x, ‖g n x - g₀ x‖ ∂μ) atTop (𝓝 0) → TendstoInMeasure μ g atTop g₀ := by
    intro g g₀ hgi hg₀ hlim
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
    have : ∀ n, eLpNorm (g n - g₀) 1 μ = ENNReal.ofReal (∫ x, ‖g n x - g₀ x‖ ∂μ) := fun n => by
      rw [eLpNorm_one_eq_lintegral_enorm ((hgi n).sub hg₀).1]
      have := ofReal_integral_norm_eq_lintegral_enorm ((hgi n).sub hg₀)
      simp only [Pi.sub_apply] at this ⊢
      exact this.symm
    simp only [this]
    have h0 := (ENNReal.continuous_ofReal.tendsto 0).comp hlim
    rw [ENNReal.ofReal_zero] at h0
    exact h0
  obtain ⟨ns₁, hns₁, hae₁⟩ := (key f f₀ hi hi₀ hL1).exists_seq_tendsto_ae
  -- contraction for the kernel averages
  have hKi : ∀ n, Integrable (kavg K (f n)) μ := fun n =>
    invariantKernel_integral_integrable K hInv (hm n) (hi n)
  have hKi₀ : Integrable (kavg K f₀) μ := invariantKernel_integral_integrable K hInv hm₀ hi₀
  have hL1K : Tendsto (fun i => ∫ y, ‖kavg K (f (ns₁ i)) y - kavg K f₀ y‖ ∂μ) atTop (𝓝 0) := by
    refine squeeze_zero (fun i => integral_nonneg fun y => norm_nonneg _) (fun i => ?_)
      (hL1.comp hns₁.tendsto_atTop)
    have h := invariantKernel_L1_contraction K hInv (hm (ns₁ i)) hm₀ (hi _) hi₀
    simpa only [Real.norm_eq_abs, kavg, Function.comp] using h
  obtain ⟨ns₂, hns₂, hae₂⟩ := (key (fun i => kavg K (f (ns₁ i))) (kavg K f₀)
    (fun i => hKi _) hKi₀ hL1K).exists_seq_tendsto_ae
  refine ⟨ns₁ ∘ ns₂, hns₁.comp hns₂, ?_, ?_⟩
  · filter_upwards [hae₁] with x hx
    exact hx.comp hns₂.tendsto_atTop
  · filter_upwards [hae₂] with y hy
    exact hy


/-- Entropy of the evolved law of a density, as an integral of `klFun`. -/
theorem klDiv_kernel_withDensity {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {f : E → ℝ} (hm : Measurable f) (hn : ∀ x, 0 ≤ f x) (hi : Integrable f (gibbsMeasure volume V))
    (hN : ∫ x, f x ∂gibbsMeasure volume V = 1)
    (hk : Integrable (fun x => klFun (f x)) (gibbsMeasure volume V)) (t : ℝ≥0) :
    klDiv (langevinKernel V B P t ∘ₘ
        ((gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (f x))))
      (gibbsMeasure volume V) =
      ENNReal.ofReal (∫ y, klFun (kavg (langevinKernel V B P t) f y) ∂gibbsMeasure volume V) := by
  let := hp
  let μ := gibbsMeasure volume V
  let K := langevinKernel V B P t
  haveI : IsMarkovKernel K := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
  have hInv : K ∘ₘ μ = μ := langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess t
  have hν := isProbabilityMeasure_withDensity_ofReal_integral_one hi hn hN
  rw [langevinKernel_withDensity_eq_of_integrable hB hV hp ρ hρ hHess hm hn hi hν t]
  exact klDiv_withDensity_eq_integral_of_klFun_integrable (measurable_kavg K hm)
    (invariantKernel_integral_integrable K hInv hm hi) (fun x => integral_nonneg hn)
    (by exact (integral_kavg_invariant hInv hi).trans hN)
    (integrable_klFun_kavg hInv hm hn hi hk)

/-- Reverse drop inside the core class. -/
theorem class_rdrop {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)
    (hNorm : ∫ x, c + g x ∂gibbsMeasure volume V = 1) {u : ℝ} (hu : 0 < u) :
    klDiv ((gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (c + g x)))
        (CutCur.gibbs V) ≤
      klDiv (lawAt (B := B) (P := P) V
          ((gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (c + g x))) u)
        (CutCur.gibbs V) +
      ENNReal.ofReal u * CutCur.fisherInfo V
        ((gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (c + g x))) := by
  have hmk : ∀ r : ℝ≥0, IsMarkovKernel (langevinKernel V B P r) := fun r =>
    langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess r
  set μ := gibbsMeasure volume V with hμ
  set ν := μ.withDensity (fun x => ENNReal.ofReal (c + g x)) with hνdef
  obtain ⟨hν, _, _⟩ := langevin_core_information_finite hB hV hp ρ hρ hHess
    (hg.of_le (by norm_num)) hgc c m hm hpos hNorm
  let := hν
  have h := langevin_dissipation_core hB hV hp ρ hρ hHess hg hgc c m hm hpos hNorm
    (s := 0) (t := u) le_rfl hu
  rw [lawAt_zero hB hV ρ hρ.le hHess ν] at h
  have hI : ∀ r ∈ Ioc (0:ℝ) u, CutCur.fisherInfo V (lawAt (B := B) (P := P) V ν r) ≤
      CutCur.fisherInfo V ν := by
    intro r _
    let := hmk r.toNNReal
    have e1 := fisherInfo_eq_relativeFisherInformation hV hp ρ hρ hHess
      (lawAt (B := B) (P := P) V ν r)
    have e2 := fisherInfo_eq_relativeFisherInformation hV hp ρ hρ hHess ν
    rw [e1, e2]
    refine (relativeFisherInformation_langevinKernel_le hB hV hp ρ hρ hHess ν r.toNNReal).trans ?_
    calc _ ≤ 1 * relativeFisherInformation hV hp ν := by
          gcongr
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr (by nlinarith [r.toNNReal.2, hρ]))
      _ = _ := one_mul _
  calc klDiv ν (CutCur.gibbs V) = _ := h
    _ ≤ klDiv (lawAt (B := B) (P := P) V ν u) (CutCur.gibbs V) +
        ∫⁻ r in Ioc (0:ℝ) u, CutCur.fisherInfo V ν := by
        exact add_le_add_right (setLIntegral_mono' measurableSet_Ioc hI) _
    _ = _ := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]


/-- **Reverse drop inequality.** For `λ = ν` of finite entropy and finite Fisher information and
`u > 0`: `H(ν|μ) ≤ H(ν P_u|μ) + u I(ν|μ)`. -/
theorem reverse_drop {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν]
    (hfin : klDiv ν (gibbsMeasure volume V) ≠ ⊤) (hI : CutCur.fisherInfo V ν ≠ ⊤)
    {u : ℝ} (hu : 0 < u) :
    klDiv ν (CutCur.gibbs V) ≤
      klDiv (lawAt (B := B) (P := P) V ν u) (CutCur.gibbs V) +
        ENNReal.ofReal u * CutCur.fisherInfo V ν := by
  let := hp
  set μ := gibbsMeasure volume V with hμ
  have hmk : ∀ r : ℝ≥0, IsMarkovKernel (langevinKernel V B P r) := fun r =>
    langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess r
  set K := langevinKernel V B P u.toNNReal with hK
  haveI := hmk u.toNNReal
  have hInv : K ∘ₘ μ = μ := langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess u.toNNReal
  have hIrel : relativeFisherInformation hV hp ν ≠ ⊤ := by
    rwa [← fisherInfo_eq_relativeFisherInformation hV hp ρ hρ hHess ν]
  have hAC : ν ≪ μ := by
    by_contra h
    exact hIrel (relativeFisherInformation_eq_top_of_not_ac hV hp ν h)
  obtain ⟨c, g, b, hb0, hg, hgc, hc, hfl, hN, hL1, hF, hFlim⟩ :=
    exists_core_fisher_approx hV hp ρ hρ hHess ν hAC hIrel
  let f : ℕ → E → ℝ := fun n x => c n + g n x
  let f₀ : E → ℝ := fun x => (ν.rnDeriv μ x).toReal
  have hf0m : Measurable f₀ := (Measure.measurable_rnDeriv ν μ).ennreal_toReal
  have hfm : ∀ n, Measurable (f n) := fun n =>
    measurable_const.add (hg n).continuous.measurable
  have hfn : ∀ n x, 0 ≤ f n x := fun n x => (hc n).le.trans (hfl n x)
  have hf0n : ∀ x, 0 ≤ f₀ x := fun x => ENNReal.toReal_nonneg
  have hfi : ∀ n, Integrable (f n) μ := fun n =>
    (integrable_const (c n)).add ((hg n).continuous.integrable_of_hasCompactSupport (hgc n))
  have hf0i : Integrable f₀ μ := integrable_toReal_rnDeriv_finite ν μ
  have hf0N : ∫ x, f₀ x ∂μ = 1 := by
    have := Measure.integral_toReal_rnDeriv hAC
    simpa using this
  have hνrep : ν = μ.withDensity (fun x => ENNReal.ofReal (f₀ x)) :=
    (withDensity_ofReal_toReal_rnDeriv_eq ν μ hAC).symm
  have hk0 : Integrable (fun x => klFun (f₀ x)) μ :=
    (integrable_klFun_rnDeriv_iff hAC).mpr (klDiv_ne_top_iff.mp hfin).2
  have hkn : ∀ n, Integrable (fun x => klFun (f n x)) μ := by
    intro n
    obtain ⟨M, hM⟩ := (hgc n).exists_bound_of_continuous (hg n).continuous
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := |c n| + M)).exists_bound_of_continuousOn
      continuous_klFun.continuousOn
    refine (integrable_const C).mono' (measurable_klFun.comp (hfm n)).aestronglyMeasurable
      (Eventually.of_forall fun x => hC _ ⟨hfn n x, ?_⟩)
    exact (le_abs_self _).trans ((abs_add_le _ _).trans
      (add_le_add le_rfl (by simpa only [Real.norm_eq_abs] using hM x)))
  -- L¹ convergence in the form needed
  have hL1' : Tendsto (fun n => ∫ x, ‖f n x - f₀ x‖ ∂μ) atTop (𝓝 0) := hL1
  obtain ⟨ns, hns, hae, hae'⟩ := exists_subseq_ae hInv hfm hf0m hfi hf0i hL1'
  have hlsc := defect_lsc hInv (f := fun i => f (ns i)) (f₀ := f₀)
    (fun i => hfm _) hf0m (fun i => hfn _) hf0n (fun i => hfi _) hf0i (fun i => hkn _) hk0 hae hae'
  -- identification of the entropies
  have hH0 : klDiv ν μ = ENNReal.ofReal (∫ x, klFun (f₀ x) ∂μ) := by
    conv_lhs => rw [hνrep]
    exact klDiv_withDensity_eq_integral_of_klFun_integrable hf0m hf0i hf0n hf0N hk0
  have hHu : klDiv (lawAt (B := B) (P := P) V ν u) μ =
      ENNReal.ofReal (∫ y, klFun (kavg K f₀ y) ∂μ) := by
    change klDiv (langevinKernel V B P u.toNNReal ∘ₘ ν) μ = _
    conv_lhs => rw [hνrep]
    exact klDiv_kernel_withDensity hB hV hp ρ hρ hHess hf0m hf0n hf0i hf0N hk0 u.toNNReal
  -- class inequality in real form
  have hcls : ∀ n, (∫ x, klFun (f n x) ∂μ) - (∫ y, klFun (kavg K (f n) y) ∂μ) ≤ u * b n := by
    intro n
    have hNn := hN n
    have hkl : klDiv (μ.withDensity (fun x => ENNReal.ofReal (c n + g n x))) μ ≤
        klDiv (lawAt (B := B) (P := P) V
          (μ.withDensity (fun x => ENNReal.ofReal (c n + g n x))) u) μ +
        ENNReal.ofReal u * CutCur.fisherInfo V
          (μ.withDensity (fun x => ENNReal.ofReal (c n + g n x))) :=
      class_rdrop hB hV hp ρ hρ hHess (hg n) (hgc n) (c n) (c n) (hc n) (hfl n) hNn hu
    obtain ⟨hνn, hFn⟩ := hF n
    let := hνn
    have hfisher : CutCur.fisherInfo V
        (μ.withDensity (fun x => ENNReal.ofReal (c n + g n x))) ≤ ENNReal.ofReal (b n) := by
      rw [fisherInfo_eq_relativeFisherInformation hV hp ρ hρ hHess]
      exact hFn
    have e1 : klDiv (μ.withDensity (fun x => ENNReal.ofReal (c n + g n x))) μ =
        ENNReal.ofReal (∫ x, klFun (f n x) ∂μ) :=
      klDiv_withDensity_eq_integral_of_klFun_integrable (hfm n) (hfi n) (hfn n) hNn (hkn n)
    have e2 : klDiv (lawAt (B := B) (P := P) V
        (μ.withDensity (fun x => ENNReal.ofReal (c n + g n x))) u) μ =
        ENNReal.ofReal (∫ y, klFun (kavg K (f n) y) ∂μ) :=
      klDiv_kernel_withDensity hB hV hp ρ hρ hHess (hfm n) (hfn n) (hfi n) hNn (hkn n) u.toNNReal
    rw [e1, e2] at hkl
    have ha' : 0 ≤ ∫ y, klFun (kavg K (f n) y) ∂μ :=
      integral_nonneg fun y => klFun_nonneg (integral_nonneg (hfn n))
    have hub : 0 ≤ u * b n := mul_nonneg hu.le (hb0 n)
    have h3 : ENNReal.ofReal (∫ x, klFun (f n x) ∂μ) ≤
        ENNReal.ofReal ((∫ y, klFun (kavg K (f n) y) ∂μ) + u * b n) := by
      refine hkl.trans ?_
      rw [ENNReal.ofReal_add ha' hub, ENNReal.ofReal_mul hu.le]
      exact add_le_add le_rfl (by gcongr)
    have := (ENNReal.ofReal_le_ofReal_iff (add_nonneg ha' hub)).mp h3
    linarith
  -- pass to the limit
  have hlim : Tendsto (fun i => ENNReal.ofReal u * ENNReal.ofReal (b (ns i))) atTop
      (𝓝 (ENNReal.ofReal u * relativeFisherInformation hV hp ν)) :=
    ENNReal.Tendsto.const_mul (hFlim.comp hns.tendsto_atTop) (Or.inr ENNReal.ofReal_ne_top)
  have hbound : ENNReal.ofReal ((∫ x, klFun (f₀ x) ∂μ) - ∫ y, klFun (kavg K f₀ y) ∂μ) ≤
      ENNReal.ofReal u * relativeFisherInformation hV hp ν := by
    refine hlsc.trans ?_
    rw [← hlim.liminf_eq]
    refine liminf_le_liminf (Eventually.of_forall fun i => ?_)
    rw [← ENNReal.ofReal_mul hu.le]
    exact ENNReal.ofReal_le_ofReal (hcls (ns i))
  show klDiv ν μ ≤ klDiv (lawAt (B := B) (P := P) V ν u) μ +
    ENNReal.ofReal u * CutCur.fisherInfo V ν
  rw [hH0, hHu, fisherInfo_eq_relativeFisherInformation hV hp ρ hρ hHess ν]
  calc ENNReal.ofReal (∫ x, klFun (f₀ x) ∂μ)
      = ENNReal.ofReal ((∫ y, klFun (kavg K f₀ y) ∂μ) +
          ((∫ x, klFun (f₀ x) ∂μ) - ∫ y, klFun (kavg K f₀ y) ∂μ)) := by congr 1; ring
    _ ≤ ENNReal.ofReal (∫ y, klFun (kavg K f₀ y) ∂μ) +
          ENNReal.ofReal ((∫ x, klFun (f₀ x) ∂μ) - ∫ y, klFun (kavg K f₀ y) ∂μ) :=
        ENNReal.ofReal_add_le
    _ ≤ _ := add_le_add le_rfl hbound

end CutoffRigidity.DissipEq
