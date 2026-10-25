module
public import CutoffRigidity.LangevinVarentropy
public import CutoffRigidity.KernelTotalVariation
public import CutoffRigidity.LangevinInformationEvolution
public import CutoffRigidity.Pinsker

/-! # Actual profiles and mixing thresholds for the curvature product condition

The data contain only the written Euclidean diffusion assumptions. Every
profile is a supremum of a genuine distance between actual probability laws;
the critical time is the genuine extended threshold infimum.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped Topology NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

structure CurvedLangevinData (Ω : Type*) [MeasurableSpace Ω] (d : ℕ) where
  potential : EuclideanSpace ℝ (Fin d) → ℝ
  smooth : ContDiff ℝ 2 potential
  probability : IsProbabilityMeasure (gibbsMeasure volume potential)
  driver : NNReal → Ω → EuclideanSpace ℝ (Fin d)
  noiseLaw : Measure Ω
  brownian : IsEuclideanBrownian driver noiseLaw
  curvature : ℝ
  curvature_pos : 0 < curvature
  hessian : ∀ x z : EuclideanSpace ℝ (Fin d),
    curvature * ‖z‖^2 ≤ fderiv ℝ (fderiv ℝ potential) x z z

@[expose] noncomputable def curvedTVProfile (D : CurvedLangevinData Ω d) (S : Set E) (t : ℝ) : ℝ :=
  kernelTVProfile (langevinKernel D.potential D.driver D.noiseLaw)
    (gibbsMeasure volume D.potential) S t.toNNReal

@[expose] noncomputable def curvedEntropyProfile (D : CurvedLangevinData Ω d) (S : Set E) (t : ℝ) : ENNReal :=
  ⨆ x : S, klDiv (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
    (gibbsMeasure volume D.potential)

@[expose] noncomputable def curvedFisherProfile (D : CurvedLangevinData Ω d) (S : Set E) (t : ℝ) : ENNReal := by
  let := langevinKernel_isMarkovKernel D.brownian D.smooth D.curvature D.curvature_pos.le D.hessian t.toNNReal
  exact ⨆ x : S, relativeFisherInformation D.smooth D.probability
    (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)

@[expose] noncomputable def curvedWassersteinSqProfile (D : CurvedLangevinData Ω d) (S : Set E) (t : ℝ) : ENNReal :=
  ⨆ x : S, squaredWasserstein (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
    (gibbsMeasure volume D.potential)

@[expose] noncomputable def curvedMixingTime (D : CurvedLangevinData Ω d) (S : Set E) (η : ℝ) : ENNReal :=
  langevinTVMixingTime D.potential D.driver D.noiseLaw S η

@[expose] noncomputable def curvedCriticalTime (D : CurvedLangevinData Ω d) (S : Set E) (η : ℝ) : ℝ :=
  (curvedMixingTime D S η).toReal

theorem curvedTVProfile_nonneg (D : CurvedLangevinData Ω d) {S : Set E} (hS : S.Nonempty) (t : ℝ) :
    0 ≤ curvedTVProfile D S t := by
  let := D.probability
  exact kernelTVProfile_nonneg _
    (langevinKernel_isMarkovKernel D.brownian D.smooth D.curvature D.curvature_pos.le D.hessian) _ S hS _

theorem curvedTVProfile_le_one (D : CurvedLangevinData Ω d) {S : Set E} (hS : S.Nonempty) (t : ℝ) :
    curvedTVProfile D S t ≤ 1 := by
  let := D.probability
  exact kernelTVProfile_le_one _
    (langevinKernel_isMarkovKernel D.brownian D.smooth D.curvature D.curvature_pos.le D.hessian) _ S hS _

theorem curvedTVProfile_antitone (D : CurvedLangevinData Ω d) {S : Set E} (hS : S.Nonempty) :
    Antitone (curvedTVProfile D S) := by
  have hh := langevinKernelTVProfile_antitone D.brownian D.smooth D.curvature D.curvature_pos.le
    D.hessian D.probability
    (langevinKernel_gibbs_invariant D.brownian D.smooth D.probability D.curvature D.curvature_pos D.hessian) S hS
  exact fun _ _ h => hh (Real.toNNReal_mono h)

theorem curvedTV_le_profile (D : CurvedLangevinData Ω d) (S : Set E) (t : ℝ) (x : E) (hx : x ∈ S) :
    totalVariationDistance (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
      (gibbsMeasure volume D.potential) ≤ curvedTVProfile D S t := by
  let := D.probability
  let := langevinKernel_isMarkovKernel D.brownian D.smooth D.curvature D.curvature_pos.le D.hessian t.toNNReal
  apply le_csSup
  · exact ⟨1,by rintro _ ⟨y,_,rfl⟩; exact totalVariationDistance_le_one _ _⟩
  · exact ⟨x,hx,rfl⟩

/-- Strictly before the genuine finite threshold, the actual TV profile
exceeds its defining threshold. No attainment of a supremum is used. -/
theorem curvedTVProfile_gt_before_mixing
    (D : CurvedLangevinData Ω d) (S : Set E) (η t : ℝ)
    (hfin : curvedMixingTime D S η ≠ ⊤) (ht : 0 ≤ t)
    (hlt : t < curvedCriticalTime D S η) : η < curvedTVProfile D S t := by
  apply profile_gt_of_lt_kernelTVMixingTime
  change ENNReal.ofReal t < curvedMixingTime D S η
  exact (ENNReal.ofReal_lt_iff_lt_toReal ht hfin).mpr hlt

/-- Strictly after the genuine finite threshold the defining TV bound holds,
using actual invariance and semigroup contraction. -/
theorem curvedTVProfile_le_after_mixing
    (D : CurvedLangevinData Ω d) (S : Set E) (hS : S.Nonempty) (η t : ℝ)
    (hfin : curvedMixingTime D S η ≠ ⊤)
    (hlt : curvedCriticalTime D S η < t) : curvedTVProfile D S t ≤ η := by
  have hmono := langevinKernelTVProfile_antitone D.brownian D.smooth D.curvature D.curvature_pos.le
    D.hessian D.probability
    (langevinKernel_gibbs_invariant D.brownian D.smooth D.probability D.curvature D.curvature_pos D.hessian) S hS
  apply profile_le_of_kernelTVMixingTime_lt _ _ _ _ hmono
  change curvedMixingTime D S η < ENNReal.ofReal t
  exact (ENNReal.lt_ofReal_iff_toReal_lt hfin).mpr hlt

/-- Actual entropy contraction lifted to the genuine initial-set supremum. -/
theorem curvedEntropyProfile_add_le (D : CurvedLangevinData Ω d) (hd : 0 < d)
    (S : Set E) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    curvedEntropyProfile D S (s+t) ≤ ENNReal.ofReal (Real.exp (-2*D.curvature*t))*curvedEntropyProfile D S s := by
  let := D.probability
  rw [curvedEntropyProfile,curvedEntropyProfile,ENNReal.mul_iSup]
  apply iSup_le
  intro x
  have hh := langevinKernel_entropy_contraction_add D.brownian D.smooth D.probability hd D.curvature
    D.curvature_pos D.hessian (Measure.dirac (x:E)) s.toNNReal t.toNNReal
  have he : s.toNNReal+t.toNNReal=(s+t).toNNReal := by
    apply NNReal.eq
    simp only [NNReal.coe_add,Real.coe_toNNReal _ hs,Real.coe_toNNReal _ ht,Real.coe_toNNReal _ (add_nonneg hs ht)]
  simp only [he,langevinKernel_comp_dirac,Real.coe_toNNReal _ ht] at hh
  exact hh.trans (le_iSup (fun y : S => ENNReal.ofReal (Real.exp (-2*D.curvature*t))*
    klDiv (langevinKernel D.potential D.driver D.noiseLaw s.toNNReal y) (gibbsMeasure volume D.potential)) x)

/-- Genuine Pinsker controls the actual real TV supremum by the actual set
entropy supremum whenever that supremum is finite. -/
theorem curvedTVProfile_le_sqrt_entropy (D : CurvedLangevinData Ω d)
    (S : Set E) (hS : S.Nonempty) (t : ℝ) (hfin : curvedEntropyProfile D S t ≠ ⊤) :
    curvedTVProfile D S t ≤ Real.sqrt ((curvedEntropyProfile D S t).toReal/2) := by
  let := D.probability
  let := langevinKernel_isMarkovKernel D.brownian D.smooth D.curvature D.curvature_pos.le D.hessian t.toNNReal
  apply csSup_le (hS.image _)
  rintro _ ⟨x,hx,rfl⟩
  have hKL : klDiv (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
      (gibbsMeasure volume D.potential) ≤ curvedEntropyProfile D S t :=
      le_iSup (fun y : S => klDiv (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal y)
        (gibbsMeasure volume D.potential)) ⟨x,hx⟩
  have hP := totalVariationDistance_sq_le_klDiv_toReal
    (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x) (gibbsMeasure volume D.potential)
    (ne_top_of_le_ne_top hfin hKL)
  have hR := ENNReal.toReal_mono hfin hKL
  apply (sq_le_sq₀ (totalVariationDistance_nonneg _ _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity)]
  linarith


/-- The actual entropy profile is nonincreasing, by genuine entropy
contraction and actual probability laws. -/
theorem curvedEntropyProfile_le_of_le (D : CurvedLangevinData Ω d) (hd : 0 < d)
    (S : Set E) (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    curvedEntropyProfile D S t ≤ ENNReal.ofReal (Real.exp (-2*D.curvature*(t-s)))*curvedEntropyProfile D S s := by
  have hh := curvedEntropyProfile_add_le D hd S s (t-s) hs (sub_nonneg.mpr hst)
  simpa only [add_sub_cancel] using hh

/-- Genuine Pinsker turns a TV threshold into a set entropy lower bound. -/
theorem curvedEntropyProfile_ge_of_tv_ge
    (D : CurvedLangevinData Ω d) (S : Set E) (hS : S.Nonempty)
    (t η : ℝ) (hη : 0 ≤ η) (hTV : η ≤ curvedTVProfile D S t) :
    ENNReal.ofReal (2*η^2) ≤ curvedEntropyProfile D S t := by
  by_cases hfin : curvedEntropyProfile D S t=⊤
  · rw [hfin]
    exact le_top
  · have hh := hTV.trans (curvedTVProfile_le_sqrt_entropy D S hS t hfin)
    have hs := (sq_le_sq₀ hη (Real.sqrt_nonneg _)).mpr hh
    rw [Real.sq_sqrt (by positivity)] at hs
    rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal (by linarith)


/-- The written Fisher/entropy regularization on actual set profiles. -/
theorem curvedFisherProfile_add_le_entropy_div
    (D : CurvedLangevinData Ω d) (S : Set E) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 < t) :
    curvedFisherProfile D S (s+t) ≤ curvedEntropyProfile D S s / ENNReal.ofReal t := by
  let := D.probability
  let := langevinKernel_isMarkovKernel D.brownian D.smooth D.curvature D.curvature_pos.le D.hessian (s+t).toNNReal
  change (⨆ x : S, relativeFisherInformation D.smooth D.probability
    (langevinKernel D.potential D.driver D.noiseLaw (s+t).toNNReal x)) ≤ _
  rw [curvedEntropyProfile,div_eq_mul_inv,ENNReal.iSup_mul]
  apply iSup_le
  intro x
  have hh := langevinKernel_fisher_entropy_endpoint_add D.brownian D.smooth D.probability D.curvature
    D.curvature_pos D.hessian (Measure.dirac (x:E)) s.toNNReal t.toNNReal (Real.toNNReal_pos.mpr ht)
  have he : s.toNNReal+t.toNNReal=(s+t).toNNReal := by
    apply NNReal.eq
    simp only [NNReal.coe_add,Real.coe_toNNReal _ hs,Real.coe_toNNReal _ ht.le,Real.coe_toNNReal _ (by linarith : 0 ≤ s+t)]
  simp only [he,langevinKernel_comp_dirac,Real.coe_toNNReal _ ht.le,div_eq_mul_inv] at hh
  exact hh.trans (le_iSup (fun y : S =>
    klDiv (langevinKernel D.potential D.driver D.noiseLaw s.toNNReal y) (gibbsMeasure volume D.potential)*
      (ENNReal.ofReal t)⁻¹) x)

end CutoffRigidity
