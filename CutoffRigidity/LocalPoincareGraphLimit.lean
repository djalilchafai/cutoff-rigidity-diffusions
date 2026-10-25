module
public import CutoffRigidity.LocalizedL2ChangeMeasure
public import CutoffRigidity.PoincareIntegrableDomain
public import CutoffRigidity.GaussianL2Closure

/-! # Passing genuine local Poincare through localized energy graph limits

A bounded local change of measure and actual strong graph convergence
extend the C¹ inequality to measurable weak-domain tests. The approximation
is explicit, rather than postulated as a functional inequality.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 650000 in
theorem localPoincare_of_supported_graph_limit
    (μ ν : Measure E) [IsProbabilityMeasure ν] (C : ℝ)
    (hP : HasLocalSmoothPoincare ν C)
    (K : Set E) (hK : MeasurableSet K)
    (M : ENNReal) (hM : M ≠ ⊤) (hν : ν.restrict K ≤ M • μ)
    (fn : ℕ → E → ℝ) (f : E → ℝ) (G : E → E)
    (hfnC : ∀ n, ContDiff ℝ 1 (fn n))
    (hfn : ∀ n, MemLp (fn n) 2 μ) (hf : MemLp f 2 μ)
    (hgn : ∀ n, MemLp (gradient (fn n)) 2 μ) (hG : MemLp G 2 μ)
    (hfnz : ∀ n, ∀ᵐ x ∂ν, x ∉ K → fn n x = 0)
    (hfz : ∀ᵐ x ∂ν, x ∉ K → f x = 0)
    (hgnz : ∀ n, ∀ᵐ x ∂ν, x ∉ K → gradient (fn n) x = 0)
    (hGz : ∀ᵐ x ∂ν, x ∉ K → G x = 0)
    (hlim : Tendsto (fun n => (hfn n).toLp (fn n)) atTop (𝓝 (hf.toLp f)))
    (hglim : Tendsto (fun n => (hgn n).toLp (gradient (fn n))) atTop (𝓝 (hG.toLp G))) :
    MemLp f 2 ν ∧ variance f ν ≤ C * ∫ x, ‖G x‖^2 ∂ν := by
  obtain ⟨hfnν,hfν,hv⟩ := tendsto_toL2_of_local_measure_le_smul hK M hM hν hfn hf hfnz hfz hlim
  obtain ⟨hgnν,hGν,hg⟩ := tendsto_toL2_of_local_measure_le_smul hK M hM hν hgn hG hgnz hGz hglim
  have hvlim := ((continuous_l2_variance ν).tendsto (hfν.toLp f)).comp hv
  have he (n : ℕ) : variance ((hfnν n).toLp (fn n)) ν ≤ C * ‖(hgnν n).toLp (gradient (fn n))‖^2 := by
    rw [variance_congr (hfnν n).coeFn_toLp]
    have hp := hP (fn n) (hfnC n) (hfnν n) (hgnν n).norm.integrable_sq
    have hn : ‖(hgnν n).toLp (gradient (fn n))‖^2 = ∫ x, ‖gradient (fn n) x‖^2 ∂ν := by
      rw [← real_inner_self_eq_norm_sq,L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hgnν n).coeFn_toLp] with x hx
      rw [hx,real_inner_self_eq_norm_sq]
    rwa [hn]
  have hbound := le_of_tendsto_of_tendsto hvlim ((hg.norm.pow 2).const_mul C) (Eventually.of_forall he)
  have hn : ‖hGν.toLp G‖^2 = ∫ x, ‖G x‖^2 ∂ν := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hGν.coeFn_toLp] with x hx
    rw [hx,real_inner_self_eq_norm_sq]
  rw [variance_congr hfν.coeFn_toLp,hn] at hbound
  exact ⟨hfν,hbound⟩

end CutoffRigidity
