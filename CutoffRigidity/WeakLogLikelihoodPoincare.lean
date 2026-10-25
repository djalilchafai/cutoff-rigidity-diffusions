module
public import CutoffRigidity.WeakLogLikelihoodTests
public import CutoffRigidity.RegularizedLogRoot

/-! # The actual weak log-likelihood local Poincare application

Regularized logarithms of the genuine closed RN root, local compact
approximation, and centered Fatou derive log-likelihood square integrability
and its variance estimate. No classical density or varentropy domain is
assumed. The intermediate local density bound remains explicit here.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped Topology ENNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 900000 in
theorem memLp_variance_log_closed_root_le
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ν : Measure E) [IsProbabilityMeasure ν] (hAC : ν ≪ gibbsMeasure volume V)
    (C : ℝ) (hC : 0 ≤ C) (hP : HasLocalSmoothPoincare ν C)
    (hloc : ∀ K : Set E, IsCompact K → ∃ M : ENNReal, M ≠ ⊤ ∧ ν.restrict K ≤ M • volume)
    (u : gibbsSobolevGraph hV hp)
    (hRN : ∀ᵐ x ∂gibbsMeasure volume V,
      (gibbsSobolevInclusion hV hp u x)^2 = (ν.rnDeriv (gibbsMeasure volume V) x).toReal)
    (hU0 : ∀ᵐ x ∂ν, gibbsSobolevInclusion hV hp u x ≠ 0)
    (hLog : Integrable (fun x => Real.log ((gibbsSobolevInclusion hV hp u x)^2)) ν) :
    MemLp (fun x => Real.log ((gibbsSobolevInclusion hV hp u x)^2)) 2 ν ∧
      variance (fun x => Real.log ((gibbsSobolevInclusion hV hp u x)^2)) ν ≤
        C * (4*‖gibbsSobolevDerivative hV hp u‖^2) := by
  let U := gibbsSobolevInclusion hV hp u
  let ε := fun n : ℕ => 1/((n : ℝ)+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε1 (n : ℕ) : ε n ≤ 1 := by
    apply (div_le_one (by positivity : (0:ℝ)<n+1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let fn := fun n : ℕ => fun x : E => Real.log (ε n+(U x)^2)
  have hregInt (n : ℕ) : Integrable (fun x => regularizedLogRoot (ε n) (U x)) ν := by
    apply ((hLog.norm.add (integrable_const (Real.log (ε n+1)))).add
      (integrable_const |Real.log (ε n)|)).mono'
      ((contDiff_regularizedLogRoot (hε n)).continuous.comp_aestronglyMeasurable
        (Lp.stronglyMeasurable U).aestronglyMeasurable)
    filter_upwards [hU0] with x hx
    exact abs_regularizedLogRoot_le (hε n) hx
  have hcore (n : ℕ) := memLp_variance_closed_root_test_le hV hp ν hAC C hC hP hloc u hRN
    (contDiff_regularizedLogRoot (hε n)) (regularizedLogRoot_zero (ε n))
    ((1+ε n)/ε n) (by positivity)
    (deriv_regularizedLogRoot_abs_bound (hε n)) (hregInt n) (regularizedLogRoot_score_bound (hε n))
  have hfnLp (n : ℕ) : MemLp (fn n) 2 ν := by
    have hh := (hcore n).1.add (memLp_const (Real.log (ε n)))
    convert! hh using 1
    funext x
    simp only [Pi.add_apply,regularizedLogRoot,fn,U,sub_add_cancel]
  have hvar (n : ℕ) : variance (fn n) ν ≤ C*(4*‖gibbsSobolevDerivative hV hp u‖^2) := by
    have heq : fn n = fun x => regularizedLogRoot (ε n) (U x)+Real.log (ε n) := by
      funext x
      simp only [fn,regularizedLogRoot,sub_add_cancel]
    rw [heq,variance_add_const (hcore n).1.aestronglyMeasurable]
    exact (hcore n).2
  have hfnBound (n : ℕ) : ∀ᵐ x ∂ν, ‖fn n x‖ ≤ |Real.log ((U x)^2)|+Real.log 2 := by
    filter_upwards [hU0] with x hx
    exact (abs_log_add_sq_le (hε n) hx).trans
      (add_le_add (le_refl _) (Real.log_le_log (by positivity : 0 < ε n+1) (by linarith [hε1 n])))
  have hlim : ∀ᵐ x ∂ν, Tendsto (fun n => fn n x) atTop (𝓝 (Real.log ((U x)^2))) := by
    filter_upwards [hU0] with x hx
    have hh := (hεlim.add_const ((U x)^2)).log (by simpa only [zero_add] using pow_ne_zero 2 hx)
    simpa only [zero_add] using hh
  have hMean := tendsto_integral_of_dominated_convergence
    (fun x => |Real.log ((U x)^2)|+Real.log 2)
    (fun n => (hfnLp n).aestronglyMeasurable) (hLog.norm.add (integrable_const _)) hfnBound hlim
  exact memLp_two_and_variance_le_of_ae_tendsto ν hfnLp hLog.aestronglyMeasurable hMean hlim hvar


set_option maxHeartbeats 800000 in
/-- The genuine local Poincare application to the actual RN log likelihood.
Its L² domain and finite varentropy follow from finite canonical Fisher and
KL information, rather than any density regularity assumption. -/
theorem varentropy_le_fisher_of_local_poincare
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ν : Measure E) [IsProbabilityMeasure ν]
    (hFI : relativeFisherInformation hV hp ν ≠ ⊤)
    (hKL : klDiv ν (gibbsMeasure volume V) ≠ ⊤)
    (C : ℝ) (hC : 0 ≤ C) (hP : HasLocalSmoothPoincare ν C)
    (hloc : ∀ K : Set E, IsCompact K → ∃ M : ENNReal, M ≠ ⊤ ∧ ν.restrict K ≤ M • volume) :
    MemLp (llr ν (gibbsMeasure volume V)) 2 ν ∧
      varentropy ν (gibbsMeasure volume V) ≠ ⊤ ∧
      (varentropy ν (gibbsMeasure volume V)).toReal ≤
        C * (relativeFisherInformation hV hp ν).toReal := by
  classical
  let hpμ : IsProbabilityMeasure (gibbsMeasure volume V) := hp
  let μ := gibbsMeasure volume V
  let hdec : ν.HaveLebesgueDecomposition μ := Measure.haveLebesgueDecomposition_of_sigmaFinite ν μ
  have hAC : ν ≪ μ := (klDiv_ne_top_iff.mp hKL).1
  have hLogInt : Integrable (llr ν μ) ν := (klDiv_ne_top_iff.mp hKL).2
  let R := squareRootRNDensityLp ν μ
  let G := closedGibbsGradient hV hp
  have hD : R ∈ G.domain := by
    by_contra hnot
    have hAC' : ν ≪ gibbsMeasure volume V := hAC
    change squareRootRNDensityLp ν (gibbsMeasure volume V) ∉ (closedGibbsGradient hV hp).domain at hnot
    have hh : relativeFisherInformation hV hp ν=⊤ := by
      simp only [relativeFisherInformation,hAC',dite_true,hnot,dite_false]
    exact hFI hh
  let D := G ⟨R,hD⟩
  let u : gibbsSobolevGraph hV hp := ⟨WithLp.toLp 2 (R,D),G.mem_graph ⟨R,hD⟩⟩
  have hR : R =ᵐ[μ] squareRootRNDensity ν μ := (squareRootRNDensity_memLp ν μ).coeFn_toLp
  have hRN : ∀ᵐ x ∂μ, (gibbsSobolevInclusion hV hp u x)^2=(ν.rnDeriv μ x).toReal := by
    filter_upwards [hR] with x hx
    change R x^2=_
    rw [hx,squareRootRNDensity_sq]
  have hU0 : ∀ᵐ x ∂ν, gibbsSobolevInclusion hV hp u x ≠ 0 := by
    filter_upwards [hAC.ae_eq hRN,Measure.rnDeriv_pos hAC,
      hAC.ae_le (Measure.rnDeriv_ne_top ν μ)] with x hx hpos htop
    have hr : 0 < (ν.rnDeriv μ x).toReal := ENNReal.toReal_pos (ne_of_gt hpos) htop
    intro hz
    rw [hz,zero_pow (by norm_num)] at hx
    linarith
  have hllr : (fun x => Real.log ((gibbsSobolevInclusion hV hp u x)^2)) =ᵐ[ν] llr ν μ := by
    filter_upwards [hAC.ae_eq hRN] with x hx
    rw [hx]
    rfl
  obtain ⟨hL,hbound⟩ := memLp_variance_log_closed_root_le hV hp ν hAC C hC hP hloc u hRN hU0
    ((integrable_congr hllr).mpr hLogInt)
  have hL' : MemLp (llr ν μ) 2 ν := (memLp_congr_ae hllr).mp hL
  refine ⟨hL',hL'.evariance_ne_top,?_⟩
  have henergy := relativeFisherInformation_eq_closed_energy hV hp ν hAC hD
  have hreal : (relativeFisherInformation hV hp ν).toReal=4*‖D‖^2 := by
    rw [henergy,ENNReal.toReal_ofReal (by positivity)]
  change variance (llr ν μ) ν ≤ _
  rw [hreal]
  rwa [variance_congr hllr] at hbound

end CutoffRigidity
