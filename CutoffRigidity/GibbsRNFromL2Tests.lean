module
public import CutoffRigidity.CompactGibbsGenerator
public import CutoffRigidity.RNDensityWeakConvergence
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! # Genuine L² RN densities from bounded compact-test integration

Actual dense compact representatives define a linear functional. Its true
bounded extension and Riesz representative agree with the actual RN density
by compact smooth distribution tests. Absolute continuity is explicit here;
for Langevin transitions it was already derived from entropy regularization.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter
open scoped Topology ContDiff
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def compactGibbsIntegralLinear
    {V : E → ℝ} (hV : Continuous V) (ν : Measure E) [IsFiniteMeasure ν] :
    compactGibbsGeneratorDomain V →ₗ[ℝ] ℝ where
  toFun u := ∫ x, compactGibbsRepresentative V u x ∂ν
  map_add' u v := by
    have he := (compactGibbsRepresentativeLinear V hV).map_add u v
    change compactGibbsRepresentative V (u+v) = fun x =>
      compactGibbsRepresentative V u x + compactGibbsRepresentative V v x at he
    rw [he]
    exact integral_add
      ((compactGibbsRepresentative_spec V u).1.continuous.integrable_of_hasCompactSupport (compactGibbsRepresentative_spec V u).2.1)
      ((compactGibbsRepresentative_spec V v).1.continuous.integrable_of_hasCompactSupport (compactGibbsRepresentative_spec V v).2.1)
  map_smul' r u := by
    have he := (compactGibbsRepresentativeLinear V hV).map_smul r u
    change compactGibbsRepresentative V (r • u) = fun x => r * compactGibbsRepresentative V u x at he
    rw [he,integral_const_mul]
    rfl

set_option maxHeartbeats 650000 in
theorem memLp_rnDeriv_of_compact_c2_L2_bound
    {V : E → ℝ} (hV : Continuous V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ν : Measure E) [IsProbabilityMeasure ν] (hAC : ν ≪ gibbsMeasure volume V)
    (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ (f : E → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f),
      ‖∫ x, f x ∂ν‖ ≤ C * ‖(hf.continuous.memLp_of_hasCompactSupport hfc
        : MemLp f 2 (gibbsMeasure volume V)).toLp f‖) :
    ∃ hRN : MemLp (fun x => (ν.rnDeriv (gibbsMeasure volume V) x).toReal) 2 (gibbsMeasure volume V),
      ‖hRN.toLp _‖ ≤ C := by
  let := hp
  let μ := gibbsMeasure volume V
  let L := compactGibbsIntegralLinear hV ν
  let e := (compactGibbsGeneratorDomain V).subtype
  have hdense : DenseRange e := by
    change Dense (Set.range (fun u : compactGibbsGeneratorDomain V => (u : E →₂[μ] ℝ)))
    convert! compactGibbsGeneratorDomain_dense V hp using 1
    ext x
    simp
  have hNorm (u : compactGibbsGeneratorDomain V) : ‖L u‖ ≤ C * ‖e u‖ := by
    let f := compactGibbsRepresentative V u
    have hf := (compactGibbsRepresentative_spec V u).1
    have hfc := (compactGibbsRepresentative_spec V u).2.1
    have he : (hf.continuous.memLp_of_hasCompactSupport hfc : MemLp f 2 μ).toLp f = e u := by
      apply Lp.ext
      exact (hf.continuous.memLp_of_hasCompactSupport hfc).coeFn_toLp.trans
        (compactGibbsRepresentative_spec V u).2.2
    have hh := hBound f hf hfc
    rw [he] at hh
    exact hh
  let F := L.extendOfNorm e
  let w : E →₂[μ] ℝ := (InnerProductSpace.toDual ℝ (E →₂[μ] ℝ)).symm F
  have hwC : ‖w‖ ≤ C := by
    rw [show ‖w‖ = ‖F‖ from (InnerProductSpace.toDual ℝ (E →₂[μ] ℝ)).symm.norm_map F]
    exact L.opNorm_extendOfNorm_le hdense hC hNorm
  have hpair (f : E → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
      inner ℝ w ((hf.continuous.memLp_of_hasCompactSupport hfc : MemLp f 2 μ).toLp f) = ∫ x, f x ∂ν := by
    let hfLp : MemLp f 2 μ := hf.continuous.memLp_of_hasCompactSupport hfc
    let u : compactGibbsGeneratorDomain V := ⟨hfLp.toLp f, ⟨f,hf,hfc,hfLp.coeFn_toLp.symm⟩⟩
    have he : compactGibbsRepresentative V u = f :=
      (compactGibbsRepresentative_unique hV u hf.continuous hfLp.coeFn_toLp.symm).symm
    have hF : F (e u) = L u := L.extendOfNorm_eq hdense ⟨C,hNorm⟩ u
    rw [InnerProductSpace.toDual_symm_apply]
    change F (e u) = _
    rw [hF]
    change (∫ x, compactGibbsRepresentative V u x ∂ν) = _
    rw [he]
  let f := fun x => (ν.rnDeriv μ x).toReal
  have hfI : Integrable f μ := integrable_toReal_rnDeriv_finite ν μ
  have hwI : Integrable (fun x => w x) μ := (Lp.memLp w).integrable (by norm_num)
  have hAE : f =ᵐ[μ] w := by
    apply ae_eq_of_integral_contDiff_smul_eq hfI.locallyIntegrable hwI.locallyIntegrable
    intro ψ hψ hψc
    have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by simp)
    have hψLp : MemLp ψ 2 μ := hψ2.continuous.memLp_of_hasCompactSupport hψc
    have he := hpair ψ hψ2 hψc
    rw [L2.inner_def] at he
    have hi : (∫ x, ψ x * w x ∂μ) = ∫ x, ψ x ∂ν := by
      apply Eq.trans _ he
      apply integral_congr_ae
      filter_upwards [hψLp.coeFn_toLp] with x hx
      rw [Real.inner_apply,hx,mul_comm]
    simp only [smul_eq_mul]
    rw [hi,integral_eq_integral_toReal_rnDeriv_mul ν μ hAC hψ.continuous.measurable]
    exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  have hRN : MemLp f 2 μ := (memLp_congr_ae hAE).mpr (Lp.memLp w)
  refine ⟨hRN,?_⟩
  have he : hRN.toLp f = w := Lp.ext (hRN.coeFn_toLp.trans hAE)
  rw [he]
  exact hwC

end CutoffRigidity
