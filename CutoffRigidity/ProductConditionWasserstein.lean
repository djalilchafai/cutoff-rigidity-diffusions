module
public import CutoffRigidity.ProductConditionInformationTheorem
public import CutoffRigidity.Talagrand

/-! # Both genuine Wasserstein cutoffs under the curvature product condition

The written Talagrand comparison transfers the already proved entropy
after-cutoff to the actual infimum over squared coupling costs. The early
bound comes from actual entropy regularization and the mixing threshold.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped Topology ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem curvedWassersteinSqProfile_le_scaled_entropy
    (D : CurvedLangevinData Ω d) (hd : 0 < d) (S : Set E) (t : ℝ) :
    curvedWassersteinSqProfile D S t ≤
      ENNReal.ofReal (2/D.curvature)*curvedEntropyProfile D S t := by
  let := D.probability
  let := langevinKernel_isMarkovKernel D.brownian D.smooth D.curvature D.curvature_pos.le D.hessian t.toNNReal
  rw [curvedEntropyProfile,ENNReal.mul_iSup]
  apply iSup_le
  intro x
  exact (squaredWasserstein_le_two_div_curvature_klDiv D.brownian D.smooth D.probability hd
    D.curvature D.curvature_pos D.hessian
    (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)).trans (le_iSup (fun y : S => ENNReal.ofReal (2/D.curvature)*
      klDiv (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal y)
        (gibbsMeasure volume D.potential)) x)

theorem productCondition_wassersteinSq_after_cutoff
    {Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ξ n)]
    (D : ∀ n : ℕ, CurvedLangevinData (Ξ n) n)
    (S : ∀ n : ℕ, Set (EuclideanSpace ℝ (Fin n))) (hS : ∀ n, (S n).Nonempty)
    (η ε : ℝ) (hη : 0 < η) (hη1 : η < 1) (hε : 0 < ε)
    (hfinite : ∀ᶠ n in atTop, curvedMixingTime (D n) (S n) η < ⊤)
    (hprod : Tendsto (fun n => (D n).curvature*curvedCriticalTime (D n) (S n) η) atTop atTop)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).curvature) atTop) :
    Tendsto (fun n => curvedWassersteinSqProfile (D n) (S n)
      ((1+ε)*curvedCriticalTime (D n) (S n) η)) atTop (𝓝 0) := by
  obtain ⟨r,hr,hRate⟩ := curvedData_curvature_eventually_positive_lower D hliminf
  have hH := productCondition_entropy_after_cutoff D S hS η ε hη hη1 hε hfinite hprod
  have hScale := (ENNReal.continuous_const_mul (a := ENNReal.ofReal (2/r))
    ENNReal.ofReal_ne_top).continuousAt.tendsto.comp hH
  simp only [Function.comp_def,mul_zero] at hScale
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hScale
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [hRate,eventually_ge_atTop 1] with n hn hd
  exact (curvedWassersteinSqProfile_le_scaled_entropy (D n) (by omega) (S n) _).trans
    (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 2) hr hn)) bot_le)

/-- Both W₂-squared limits in the written theorem, with genuine transport
costs and only the source assumptions. Squaring preserves these endpoints. -/
theorem curvature_product_condition_wasserstein
    {Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ξ n)]
    (D : ∀ n : ℕ, CurvedLangevinData (Ξ n) n)
    (S : ∀ n : ℕ, Set (EuclideanSpace ℝ (Fin n))) (hS : ∀ n, (S n).Nonempty)
    (η : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (hfinite : ∀ᶠ n in atTop, curvedMixingTime (D n) (S n) η < ⊤)
    (hprod : Tendsto (fun n => (D n).curvature*curvedCriticalTime (D n) (S n) η) atTop atTop)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).curvature) atTop)
    (ht0 : Tendsto (fun n => curvedCriticalTime (D n) (S n) η) atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      Tendsto (fun n => curvedWassersteinSqProfile (D n) (S n) ((1-ε)*curvedCriticalTime (D n) (S n) η)) atTop (𝓝 ⊤) ∧
      Tendsto (fun n => curvedWassersteinSqProfile (D n) (S n) ((1+ε)*curvedCriticalTime (D n) (S n) η)) atTop (𝓝 0) := by
  intro ε hε hε1
  exact ⟨productCondition_wassersteinSq_before_cutoff D S hS η ε hη hε hε1 hfinite ht0,
    productCondition_wassersteinSq_after_cutoff D S hS η ε hη hη1 hε hfinite hprod hliminf⟩

end CutoffRigidity
