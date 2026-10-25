module

public import CutoffRigidity.Statements
public import CutoffRigidity.GaussianTransport

/-! # Transport, step 1: generic facts about the Challenge's `wasserstein2`

`CutCur.wasserstein2` is defined on any pseudo-extended-metric measurable space (a Riemannian
manifold is only an `EMetricSpace`).  We prove, without any metric/second-countability assumption:

* `wasserstein2_sq_eq_cost2` : `W₂² = ⨅ couplings, ∫⁻ edist²`;
* `cost2_map_le` : pushforward by a Lipschitz map costs at most `L²`;
* `cost2_dirac_left` : `W₂²(δ_x, ν) = ∫⁻ edist(x,·)² dν`;
* `cost2_le_of_ae_coupling` : a coupling bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace CutoffRigidity.Riemann

variable {α β : Type*} [PseudoEMetricSpace α] [MeasurableSpace α]
  [PseudoEMetricSpace β] [MeasurableSpace β]

/-- The squared quadratic transport cost, as an infimum over couplings. -/
noncomputable def cost2 (μ ν : Measure α) : ℝ≥0∞ :=
  ⨅ (π : Measure (α × α)) (_ : π.map Prod.fst = μ ∧ π.map Prod.snd = ν),
    ∫⁻ z, edist z.1 z.2 ^ 2 ∂π

theorem wasserstein2_sq_eq_cost2 (μ ν : Measure α) :
    CutCur.wasserstein2 μ ν ^ 2 = cost2 μ ν := by
  rw [CutCur.wasserstein2, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  rfl

theorem cost2_le_cost {μ ν : Measure α} (π : Measure (α × α))
    (h : π.map Prod.fst = μ ∧ π.map Prod.snd = ν) :
    cost2 μ ν ≤ ∫⁻ z, edist z.1 z.2 ^ 2 ∂π :=
  iInf₂_le π h

/-- A Lipschitz map multiplies the squared cost by at most `L²`. -/
theorem cost2_map_le (μ ν : Measure α) {f : α → β} (hf : Measurable f) {L : ℝ≥0} (hL0 : L ≠ 0)
    (hL : ∀ x y, edist (f x) (f y) ≤ (L : ℝ≥0∞) * edist x y) :
    cost2 (μ.map f) (ν.map f) ≤ (L : ℝ≥0∞) ^ 2 * cost2 μ ν := by
  have hne0 : ((L : ℝ≥0∞) ^ 2) ≠ 0 := by simpa using hL0
  have hneT : ((L : ℝ≥0∞) ^ 2) ≠ ⊤ := by simp
  unfold cost2
  rw [ENNReal.mul_iInf_of_ne hne0 hneT]
  refine le_iInf fun π => ?_
  rw [ENNReal.mul_iInf_of_ne hne0 hneT]
  refine le_iInf fun hπ => ?_
  have hpair : Measurable (fun z : α × α => (f z.1, f z.2)) := by fun_prop
  have hm : (π.map (fun z : α × α => (f z.1, f z.2))).map Prod.fst = μ.map f ∧
      (π.map (fun z : α × α => (f z.1, f z.2))).map Prod.snd = ν.map f := by
    constructor
    · rw [Measure.map_map measurable_fst hpair]
      change π.map (f ∘ Prod.fst) = _
      rw [← Measure.map_map hf measurable_fst, hπ.1]
    · rw [Measure.map_map measurable_snd hpair]
      change π.map (f ∘ Prod.snd) = _
      rw [← Measure.map_map hf measurable_snd, hπ.2]
  refine (cost2_le_cost _ hm).trans ?_
  refine (lintegral_map_le _ hpair.aemeasurable).trans ?_
  calc ∫⁻ z, edist (f z.1) (f z.2) ^ 2 ∂π ≤ ∫⁻ z, ((L : ℝ≥0∞) * edist z.1 z.2) ^ 2 ∂π :=
        lintegral_mono fun z => pow_le_pow_left' (hL z.1 z.2) 2
    _ = (L : ℝ≥0∞) ^ 2 * ∫⁻ z, edist z.1 z.2 ^ 2 ∂π := by
        simp only [mul_pow]
        exact lintegral_const_mul' _ _ hneT

/-- The product coupling gives the usual second-moment bound for a deterministic start. -/
theorem cost2_dirac_left_le (x : α) (ν : Measure α) [IsProbabilityMeasure ν] :
    cost2 (Measure.dirac x) ν ≤ ∫⁻ y, edist x y ^ 2 ∂ν := by
  have hπ : ((Measure.dirac x).prod ν).map Prod.fst = Measure.dirac x ∧
      ((Measure.dirac x).prod ν).map Prod.snd = ν := by simp
  refine (cost2_le_cost _ hπ).trans ?_
  rw [Measure.dirac_prod]
  exact (lintegral_map_le _ (measurable_prodMk_left (x := x)).aemeasurable)

end CutoffRigidity.Riemann
