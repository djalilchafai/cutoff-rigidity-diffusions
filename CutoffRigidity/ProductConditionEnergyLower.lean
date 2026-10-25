module
public import CutoffRigidity.ProductConditionEntropyLower
public import CutoffRigidity.LogSobolev

/-! # Source Fisher and Wasserstein lower cutoffs under the product condition

Full genuine LSI transfers entropy divergence to Fisher. The actual BGL
entropy-cost regularization and the intermediate TV threshold give the
written linear-in-mixing-time Wasserstein squared lower bound.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped Topology ENNReal NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem curvedFisherProfile_ge_scaled_entropy (D : CurvedLangevinData Ω d) (hd : 0 < d)
    (S : Set E) (t : ℝ) :
    ENNReal.ofReal (2*D.curvature)*curvedEntropyProfile D S t ≤ curvedFisherProfile D S t := by
  let := D.probability
  let := langevinKernel_isMarkovKernel D.brownian D.smooth D.curvature D.curvature_pos.le D.hessian t.toNNReal
  change ENNReal.ofReal (2*D.curvature)*(⨆ x : S,
    klDiv (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x) (gibbsMeasure volume D.potential)) ≤ _
  rw [ENNReal.mul_iSup]
  apply iSup_le
  intro x
  have hh := logSobolev_relativeFisherInformation D.brownian D.smooth D.probability hd D.curvature
    D.curvature_pos D.hessian (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
  have h0 : ENNReal.ofReal (2*D.curvature) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by have := D.curvature_pos; positivity)
  have hi := (ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl ENNReal.ofReal_ne_top)).mp hh
  have hI : ENNReal.ofReal (2*D.curvature)*
      klDiv (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x) (gibbsMeasure volume D.potential) ≤
      relativeFisherInformation D.smooth D.probability (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x) := by
    simpa only [mul_comm] using hi
  exact hI.trans (le_iSup (fun y : S => relativeFisherInformation D.smooth D.probability
    (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal y)) x)

/-- The source positive extended lower limit supplies a fixed eventual
positive curvature lower bound, also when the curvatures tend to infinity. -/
theorem curvedData_curvature_eventually_positive_lower
    {Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ξ n)]
    (D : ∀ n : ℕ, CurvedLangevinData (Ξ n) n)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).curvature) atTop) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ n in atTop, r ≤ (D n).curvature := by
  obtain ⟨s,hs0,hs⟩ := exists_between hliminf
  have hsfin : s ≠ ⊤ := ne_of_lt (hs.trans_le le_top)
  refine ⟨s.toReal,ENNReal.toReal_pos hs0.ne' hsfin,?_⟩
  filter_upwards [eventually_lt_of_lt_liminf hs] with n hn
  rw [← ENNReal.ofReal_toReal hsfin] at hn
  exact ((ENNReal.ofReal_lt_ofReal_iff (D n).curvature_pos).mp hn).le

theorem productCondition_fisher_before_cutoff
    {Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ξ n)]
    (D : ∀ n : ℕ, CurvedLangevinData (Ξ n) n)
    (S : ∀ n : ℕ, Set (EuclideanSpace ℝ (Fin n))) (hS : ∀ n, (S n).Nonempty)
    (η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) (hε1 : ε < 1)
    (hfinite : ∀ᶠ n in atTop, curvedMixingTime (D n) (S n) η < ⊤)
    (hprod : Tendsto (fun n => (D n).curvature*curvedCriticalTime (D n) (S n) η) atTop atTop)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).curvature) atTop) :
    Tendsto (fun n => curvedFisherProfile (D n) (S n)
      ((1-ε)*curvedCriticalTime (D n) (S n) η)) atTop (𝓝 ⊤) := by
  obtain ⟨r,hr,hRate⟩ := curvedData_curvature_eventually_positive_lower D hliminf
  have hH := productCondition_entropy_before_cutoff D S hS η ε hη hε hε1 hfinite hprod
  have h0 : ENNReal.ofReal (2*r) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hScale := (ENNReal.continuous_const_mul (a := ENNReal.ofReal (2*r)) ENNReal.ofReal_ne_top).continuousAt.tendsto.comp hH
  simp only [Function.comp_def,ENNReal.mul_top h0] at hScale
  apply tendsto_nhds_top_mono hScale
  filter_upwards [hRate,eventually_ge_atTop 1] with n hn hd
  exact (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (by linarith : 2*r ≤ 2*(D n).curvature))
    (show (0:ENNReal) ≤ curvedEntropyProfile (D n) (S n) ((1-ε)*curvedCriticalTime (D n) (S n) η) from bot_le)).trans
      (curvedFisherProfile_ge_scaled_entropy (D n) (by omega) (S n) _)

/-- Genuine entropy regularization lifted to the actual initial-set profile. -/
theorem curvedEntropyProfile_mul_time_le_wasserstein
    (D : CurvedLangevinData Ω d) (S : Set E) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 < t) :
    ENNReal.ofReal (2*t)*curvedEntropyProfile D S (s+t) ≤ curvedWassersteinSqProfile D S s := by
  let := D.probability
  let := langevinKernel_isMarkovKernel D.brownian D.smooth D.curvature D.curvature_pos.le D.hessian s.toNNReal
  rw [curvedEntropyProfile,ENNReal.mul_iSup]
  apply iSup_le
  intro x
  have hh := klDiv_langevinKernel_le_squaredWasserstein_div_time D.brownian D.smooth D.probability
    D.curvature D.curvature_pos D.hessian (langevinKernel D.potential D.driver D.noiseLaw s.toNNReal x) t ht
  have he : s.toNNReal+t.toNNReal=(s+t).toNNReal := by
    apply NNReal.eq
    simp only [NNReal.coe_add,Real.coe_toNNReal _ hs,Real.coe_toNNReal _ ht.le,Real.coe_toNNReal _ (by linarith : 0 ≤ s+t)]
  have hcomp : langevinKernel D.potential D.driver D.noiseLaw t.toNNReal ∘ₘ
      langevinKernel D.potential D.driver D.noiseLaw s.toNNReal x =
      langevinKernel D.potential D.driver D.noiseLaw (s+t).toNNReal x := by
    rw [← Kernel.comp_apply,langevinKernel_comp D.brownian D.smooth D.curvature D.curvature_pos.le D.hessian,he]
  rw [hcomp] at hh
  have hmul := mul_le_mul_of_nonneg_left hh (show (0:ENNReal) ≤ ENNReal.ofReal (2*t) from bot_le)
  have hcancel : ENNReal.ofReal (2*t)*ENNReal.ofReal (1/(2*t))=1 := by
    rw [← ENNReal.ofReal_mul (by positivity),mul_one_div_cancel (by positivity : 2*t ≠ 0),ENNReal.ofReal_one]
  rw [← mul_assoc,hcancel,one_mul] at hmul
  exact hmul.trans (le_iSup (fun y : S => squaredWasserstein
    (langevinKernel D.potential D.driver D.noiseLaw s.toNNReal y) (gibbsMeasure volume D.potential)) x)

set_option maxHeartbeats 650000 in
theorem curvedWassersteinSqProfile_before_mixing_lower
    (D : CurvedLangevinData Ω d) (S : Set E) (hS : S.Nonempty)
    (η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) (hε1 : ε < 1)
    (hfin : curvedMixingTime D S η ≠ ⊤) (ht0 : 0 < curvedCriticalTime D S η) :
    ENNReal.ofReal (2*ε*η^2*curvedCriticalTime D S η) ≤
      curvedWassersteinSqProfile D S ((1-ε)*curvedCriticalTime D S η) := by
  let t0 := curvedCriticalTime D S η
  let a := (1-ε)*t0
  let b := (1-ε/2)*t0
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hs : 0 < b-a := by dsimp [a,b]; nlinarith
  have hb : 0 ≤ b := by dsimp [b]; nlinarith
  have hTV := curvedTVProfile_gt_before_mixing D S η b hfin hb (by dsimp [b]; nlinarith)
  have hH := curvedEntropyProfile_ge_of_tv_ge D S hS b η hη.le hTV.le
  have hReg := curvedEntropyProfile_mul_time_le_wasserstein D S a (b-a) ha hs
  rw [add_sub_cancel] at hReg
  have hh := (mul_le_mul_of_nonneg_left hH (show (0:ENNReal) ≤ ENNReal.ofReal (2*(b-a)) from bot_le)).trans hReg
  convert! hh using 1
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*(b-a))]
  congr 1
  dsimp [a,b]
  ring

/-- The source W₂-squared profile diverges before cutoff when the genuine
mixing time tends to infinity. -/
theorem productCondition_wassersteinSq_before_cutoff
    {Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ξ n)]
    (D : ∀ n : ℕ, CurvedLangevinData (Ξ n) n)
    (S : ∀ n : ℕ, Set (EuclideanSpace ℝ (Fin n))) (hS : ∀ n, (S n).Nonempty)
    (η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) (hε1 : ε < 1)
    (hfinite : ∀ᶠ n in atTop, curvedMixingTime (D n) (S n) η < ⊤)
    (ht0 : Tendsto (fun n => curvedCriticalTime (D n) (S n) η) atTop atTop) :
    Tendsto (fun n => curvedWassersteinSqProfile (D n) (S n)
      ((1-ε)*curvedCriticalTime (D n) (S n) η)) atTop (𝓝 ⊤) := by
  have hlim := ENNReal.tendsto_ofReal_atTop.comp (ht0.const_mul_atTop (by positivity : 0 < 2*ε*η^2))
  apply tendsto_nhds_top_mono hlim
  filter_upwards [hfinite,ht0.eventually (eventually_gt_atTop (0:ℝ))] with n hn ht
  exact curvedWassersteinSqProfile_before_mixing_lower (D n) (S n) (hS n) η ε hη hε hε1 hn.ne ht

end CutoffRigidity
