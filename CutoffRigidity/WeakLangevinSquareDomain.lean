module
public import CutoffRigidity.WeakLaplacianSquareChain
public import CutoffRigidity.C1WeakLangevinDomain

/-! # The actual closed generator domain of bounded C¹ squares

The weak carré-du-champ chain rule supplies the true operator action.
No classical second derivative of the squared test is assumed.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter Set
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem bounded_c1_weak_langevin_square_mem_operatorGraph
    {V f h : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hf : ContDiff ℝ 1 f) (hh : Measurable h)
    (M G H : ℝ) (hM : 0 ≤ M) (_hG : 0 ≤ G) (_hH : 0 ≤ H)
    (hfB : ∀ x, ‖f x‖ ≤ M) (hgradB : ∀ x, ‖gradient f x‖ ≤ G) (hhB : ∀ x, ‖h x‖ ≤ H)
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      (∫ x, f x * euclideanLaplacian ψ x) =
        ∫ x, (h x + inner ℝ (gradient V x) (gradient f x)) * ψ x) :
    ∃ (hSq : MemLp (fun x => f x ^ 2) 2 (gibbsMeasure volume V))
      (hSrc : MemLp (fun x => 2 * f x * h x + 2 * ‖gradient f x‖ ^ 2) 2 (gibbsMeasure volume V)),
      (hSq.toLp _, -hSrc.toLp _) ∈ (gibbsPositiveGenerator hV hp).graph := by
  let := hp
  have hSqC : ContDiff ℝ 1 (fun x => f x ^ 2) := by simpa only [pow_two] using hf.mul hf
  have hSqB (x : E) : ‖f x ^ 2‖ ≤ M ^ 2 := by rw [norm_pow]; gcongr; exact hfB x
  have hSq : MemLp (fun x => f x ^ 2) 2 (gibbsMeasure volume V) := MemLp.of_bound hSqC.continuous.aestronglyMeasurable (M ^ 2) (Eventually.of_forall hSqB)
  have hGradB (x : E) : ‖gradient (fun y => f y ^ 2) x‖ ≤ 2 * M * G := by
    rw [gradient_square_of_c1 hf, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
    calc
      _ ≤ (2 * M) * G := mul_le_mul (mul_le_mul_of_nonneg_left (hfB x) (by norm_num))
        (hgradB x) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hGrad : MemLp (gradient (fun x => f x ^ 2)) 2 (gibbsMeasure volume V) := MemLp.of_bound (continuous_gradient_of_c1 hSqC).aestronglyMeasurable
    (2 * M * G) (Eventually.of_forall hGradB)
  have hSrcMeas : Measurable (fun x => 2 * f x * h x + 2 * ‖gradient f x‖ ^ 2) :=
    ((hf.continuous.measurable.const_mul 2).mul hh).add
      (((continuous_gradient_of_c1 hf).norm.pow 2).measurable.const_mul 2)
  have hSrcB (x : E) : ‖2 * f x * h x + 2 * ‖gradient f x‖ ^ 2‖ ≤ 2 * M * H + 2 * G ^ 2 := by
    apply (norm_add_le _ _).trans
    simp only [norm_mul, Real.norm_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)), Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg ‖gradient f x‖)]
    gcongr
    · simpa only [Real.norm_eq_abs] using hfB x
    · simpa only [Real.norm_eq_abs] using hhB x
    · exact hgradB x
  have hSrc : MemLp (fun x => 2 * f x * h x + 2 * ‖gradient f x‖ ^ 2) 2 (gibbsMeasure volume V) := MemLp.of_bound hSrcMeas.aestronglyMeasurable _ (Eventually.of_forall hSrcB)
  have hFloc (K : Set E) (hK : IsCompact K) :
      MemLp (fun x => h x + inner ℝ (gradient V x) (gradient f x)) 2 ((volume : Measure E).restrict K) := by
    let : IsFiniteMeasure ((volume : Measure E).restrict K) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top (μ := (volume : Measure E))⟩
    exact (MemLp.of_bound hh.aestronglyMeasurable H (Eventually.of_forall hhB)).add
      (continuous_memLp_two_restrict_compact
        ((continuous_gradient_of_c1 (hV.of_le (by norm_num))).inner (continuous_gradient_of_c1 hf)) hK)
  refine ⟨hSq,hSrc,?_⟩
  apply c1_weak_langevin_mem_operatorGraph hV hp ρ hρ hHess hSqC hSq hGrad hSrc
  intro ψ hψ hψc
  exact (weak_langevin_square_chain hf hFloc hweak ψ hψ hψc).trans
    (integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _))

end CutoffRigidity
