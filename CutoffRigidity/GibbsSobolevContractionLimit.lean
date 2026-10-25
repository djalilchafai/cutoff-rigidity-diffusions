module
public import CutoffRigidity.GibbsSobolevContraction

/-! # Closed-graph passage to limits of genuine smooth normal contractions -/
public section
namespace CutoffRigidity
open MeasureTheory Filter Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 700000 in
theorem gibbsSobolev_normal_contraction_limit
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ψ : ℕ → ℝ → ℝ) (hψ : ∀ n, ContDiff ℝ 2 (ψ n))
    (hψ0 : ∀ n, ψ n 0 = 0) (hbψ : ∀ n r, |deriv (ψ n) r| ≤ 1)
    {φ g : ℝ → ℝ} (hφ : LipschitzWith 1 φ) (hφ0 : φ 0 = 0)
    (hlim : ∀ r, Tendsto (fun n => ψ n r) atTop (𝓝 (φ r)))
    (hdlim : ∀ r, Tendsto (fun n => deriv (ψ n) r) atTop (𝓝 (g r)))
    (hbg : ∀ r, |g r| ≤ 1)
    (u : gibbsSobolevGraph hV hprob) :
    ∃ (v : gibbsSobolevGraph hV hprob),
      (gibbsSobolevInclusion hV hprob v =ᵐ[gibbsMeasure volume V]
        fun x => φ (gibbsSobolevInclusion hV hprob u x)) ∧
      (gibbsSobolevDerivative hV hprob v =ᵐ[gibbsMeasure volume V]
        fun x => g (gibbsSobolevInclusion hV hprob u x) • gibbsSobolevDerivative hV hprob u x) ∧
      ‖gibbsSobolevDerivative hV hprob v‖ ≤ ‖gibbsSobolevDerivative hV hprob u‖ := by
  let μ := gibbsMeasure volume V
  let U := gibbsSobolevInclusion hV hprob u
  let D := gibbsSobolevDerivative hV hprob u
  let an : ℕ → E → ℝ := fun n x => deriv (ψ n) (U x)
  let a : E → ℝ := fun x => g (U x)
  have han (n : ℕ) : AEStronglyMeasurable (an n) μ :=
    ((hψ n).continuous_deriv (by norm_num)).comp_aestronglyMeasurable (Lp.aestronglyMeasurable U)
  have halim : ∀ᵐ x ∂μ, Tendsto (fun n => an n x) atTop (𝓝 (a x)) :=
    Eventually.of_forall (fun x => hdlim (U x))
  have ha : AEStronglyMeasurable a μ := aestronglyMeasurable_of_tendsto_ae atTop han halim
  have hbn (n : ℕ) : ∀ᵐ x ∂μ, ‖an n x‖ ≤ 1 := Eventually.of_forall (fun x => hbψ n _)
  have hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ 1 := Eventually.of_forall (fun x => hbg _)
  let Bn := fun n => boundedScalarMulL2 (an n) (han n) (hbn n) D
  let B := boundedScalarMulL2 a ha hb D
  let C := hφ.compLp hφ0 U
  let Ln := fun n => scalar_normal_contraction_lipschitz ((hψ n).differentiable (by norm_num)) (hbψ n)
  let Cn := fun n => (Ln n).compLp (hψ0 n) U
  have hB : Tendsto Bn atTop (𝓝 B) :=
    boundedScalarMulL2_tendsto han ha hbn hb halim tendsto_const_nhds
  have hULp : MemLp (fun x => φ (U x)) 2 μ := hφ.comp_memLp hφ0 (Lp.memLp U)
  have hnLp (n : ℕ) : MemLp (fun x => ψ n (U x)) 2 μ := (Ln n).comp_memLp (hψ0 n) (Lp.memLp U)
  have hnormψ (n : ℕ) (r : ℝ) : ‖ψ n r‖ ≤ ‖r‖ := by
    have hh := (Ln n).dist_le_mul r 0
    simpa only [hψ0 n, dist_zero_right, NNReal.coe_one, one_mul] using hh
  have hnormφ (r : ℝ) : ‖φ r‖ ≤ ‖r‖ := by
    have hh := hφ.dist_le_mul r 0
    simpa only [hφ0, dist_zero_right, NNReal.coe_one, one_mul] using hh
  have hC : Tendsto Cn atTop (𝓝 C) := by
    have hct := tendsto_toL2_of_dominated_sq hULp hnLp
      (fun x => 4 * ‖U x‖ ^ 2) ((Lp.memLp U).norm.integrable_sq.const_mul 4)
      (fun n => Eventually.of_forall (fun x => by
        have hh := norm_sub_le (ψ n (U x)) (φ (U x))
        have hh1 := hnormψ n (U x)
        have hh2 := hnormφ (U x)
        nlinarith [norm_nonneg (ψ n (U x) - φ (U x))]))
      (Eventually.of_forall (fun x => hlim (U x)))
    have heqn (n : ℕ) : (hnLp n).toLp (fun x => ψ n (U x)) = Cn n := by
      apply Lp.ext
      exact (hnLp n).coeFn_toLp.trans ((Ln n).coeFn_compLp (hψ0 n) U).symm
    have heqc : hULp.toLp (fun x => φ (U x)) = C := by
      apply Lp.ext
      exact hULp.coeFn_toLp.trans (hφ.coeFn_compLp hφ0 U).symm
    simpa only [heqn, heqc] using hct
  have hp (n : ℕ) : (Cn n, Bn n) ∈ (closedGibbsGradient hV hprob).graph := by
    obtain ⟨v, hv, hd, _⟩ := gibbsSobolev_smooth_normal_contraction hV hprob
      (hψ n) (hψ0 n) (hbψ n) u
    have heq : Cn n = gibbsSobolevInclusion hV hprob v := by
      apply Lp.ext
      exact ((Ln n).coeFn_compLp (hψ0 n) U).trans hv.symm
    have hdeq : Bn n = gibbsSobolevDerivative hV hprob v := by
      apply Lp.ext
      exact (boundedScalarMulL2_coeFn (an n) (han n) (hbn n) D).trans hd.symm
    rw [heq, hdeq]
    exact v.property
  have hclosed : (C, B) ∈ (closedGibbsGradient hV hprob).graph :=
    (closedGibbsGradient_isClosed hV hprob).mem_of_tendsto (hC.prodMk_nhds hB)
      (Eventually.of_forall hp)
  let v : gibbsSobolevGraph hV hprob := ⟨WithLp.toLp 2 (C, B), hclosed⟩
  refine ⟨v, hφ.coeFn_compLp hφ0 U, boundedScalarMulL2_coeFn a ha hb D, ?_⟩
  change ‖B‖ ≤ ‖D‖
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [boundedScalarMulL2_coeFn a ha hb D, hb] with x hx hb'
  rw [hx, norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) hb'
end CutoffRigidity
