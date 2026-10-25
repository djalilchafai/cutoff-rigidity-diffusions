module
public import CutoffRigidity.GibbsCompactApproximation
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! # Genuine local bounded change of measure for strong L² limits

A local measure bound transfers actual compactly supported L² graph
approximants. It is the measure-theoretic ingredient in the weighted weak
log-likelihood domain, and assumes no Fisher or Poincare conclusion.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter Set
open scoped Topology ENNReal
variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F]

omit [InnerProductSpace ℝ F] in
/-- A function vanishing off a measurable set has exactly the restricted
L² norm, including all integrability assertions. -/
theorem memLp_of_restrict_of_ae_zero_compl
    {μ : Measure X} {K : Set X} (hK : MeasurableSet K)
    {f : X → F} (hf : MemLp f 2 (μ.restrict K))
    (hz : ∀ᵐ x ∂μ, x ∉ K → f x = 0) : MemLp f 2 μ := by
  have hi : MemLp (K.indicator f) 2 μ := (memLp_indicator_iff_restrict hK).mpr hf
  apply (memLp_congr_ae _).mp hi
  filter_upwards [hz] with x hx
  by_cases h : x ∈ K
  · exact indicator_of_mem h f
  · rw [indicator_of_notMem h f,hx h]

/-- Strong actual L² convergence transfers under a bounded local change of
measure when all representatives vanish outside that same measurable set. -/
theorem tendsto_toL2_of_local_measure_le_smul
    {μ ν : Measure X} {K : Set X} (hK : MeasurableSet K)
    (M : ENNReal) (hM : M ≠ ⊤) (hν : ν.restrict K ≤ M • μ)
    {fn : ℕ → X → F} {f : X → F}
    (hfn : ∀ n, MemLp (fn n) 2 μ) (hf : MemLp f 2 μ)
    (hfnz : ∀ n, ∀ᵐ x ∂ν, x ∉ K → fn n x = 0)
    (hfz : ∀ᵐ x ∂ν, x ∉ K → f x = 0)
    (hlim : Tendsto (fun n => (hfn n).toLp (fn n)) atTop (𝓝 (hf.toLp f))) :
    ∃ (hfnν : ∀ n, MemLp (fn n) 2 ν) (hfν : MemLp f 2 ν),
      Tendsto (fun n => (hfnν n).toLp (fn n)) atTop (𝓝 (hfν.toLp f)) := by
  let A : (X →₂[μ] F) →L[ℝ] (X →₂[ν.restrict K] F) := Lp.LpToLpOfMeasureLeSMul hM hν
  have hac : ν.restrict K ≪ μ := (Measure.absolutelyContinuous_of_le_smul hν)
  have hrep (g : X → F) (hg : MemLp g 2 μ) : A (hg.toLp g) =ᵐ[ν.restrict K] g :=
    (Lp.coeFn_LpToLpOfMeasureLeSMul hM hν (hg.toLp g)).trans (hac.ae_eq hg.coeFn_toLp)
  have hfnK (n : ℕ) : MemLp (fn n) 2 (ν.restrict K) :=
    (memLp_congr_ae (hrep (fn n) (hfn n))).mp (Lp.memLp _)
  have hfK : MemLp f 2 (ν.restrict K) :=
    (memLp_congr_ae (hrep f hf)).mp (Lp.memLp _)
  have hfnν (n : ℕ) : MemLp (fn n) 2 ν := memLp_of_restrict_of_ae_zero_compl hK (hfnK n) (hfnz n)
  have hfν : MemLp f 2 ν := memLp_of_restrict_of_ae_zero_compl hK hfK hfz
  have hfnEq (n : ℕ) : A ((hfn n).toLp (fn n)) = (hfnK n).toLp (fn n) :=
    Lp.ext ((hrep _ _).trans (hfnK n).coeFn_toLp.symm)
  have hfEq : A (hf.toLp f) = hfK.toLp f := Lp.ext ((hrep _ _).trans hfK.coeFn_toLp.symm)
  have hlimK := (A.continuous.tendsto _).comp hlim
  simp only [Function.comp_def,hfnEq,hfEq] at hlimK
  refine ⟨hfnν,hfν,tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  have heq (n : ℕ) : ‖(hfnν n).toLp (fn n)-hfν.toLp f‖ =
      ‖(hfnK n).toLp (fn n)-hfK.toLp f‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have hnorm {σ : Measure X} (ha : MemLp (fn n) 2 σ) (hb : MemLp f 2 σ) :
        ‖ha.toLp (fn n)-hb.toLp f‖^2 = ∫ x, ‖fn n x-f x‖^2 ∂σ := by
      rw [← real_inner_self_eq_norm_sq,L2.inner_def]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (ha.toLp (fn n)) (hb.toLp f),ha.coeFn_toLp,hb.coeFn_toLp]
        with x hs hx hy
      rw [hs,Pi.sub_apply,hx,hy,real_inner_self_eq_norm_sq]
    rw [hnorm (hfnν n) hfν,hnorm (hfnK n) hfK]
    rw [← integral_indicator hK]
    apply integral_congr_ae
    filter_upwards [hfnz n,hfz] with x hn hx
    by_cases h : x ∈ K
    · rw [indicator_of_mem h]
    · rw [indicator_of_notMem h,hn h,hx h,sub_self,norm_zero,zero_pow (by norm_num)]
  simpa only [heq] using tendsto_iff_norm_sub_tendsto_zero.mp hlimK

end CutoffRigidity
