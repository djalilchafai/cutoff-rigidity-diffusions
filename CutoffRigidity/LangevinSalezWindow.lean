module
public import CutoffRigidity.LangevinEntropyDrop
public import CutoffRigidity.SalezDiscreteEntropyWindow
public import CutoffRigidity.ProductConditionProfiles

/-! # The genuine Salez entropy window for actual Langevin transitions

Full actual entropy-drop dissipation and the proved weak-domain varentropy
bound instantiate the geometric reciprocal comparison. No entropy derivative,
transition-density regularity or domain premise is assumed.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped Topology ENNReal NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def curvedPointFisher (D : CurvedLangevinData Ω d) (t : ℝ) (x : E) : ENNReal := by
  let := langevinKernel_isMarkovKernel D.brownian D.smooth D.curvature D.curvature_pos.le D.hessian t.toNNReal
  exact relativeFisherInformation D.smooth D.probability
    (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)

set_option maxHeartbeats 650000 in
/-- The actual entropy drop between any two positive times controls the
actual endpoint Fisher value. -/
theorem curvedPoint_entropy_drop (D : CurvedLangevinData Ω d) (x : E)
    (s t : ℝ) (hs : 0 < s) (hst : s < t) :
    (t-s)*(curvedPointFisher D t x).toReal ≤
      (klDiv (langevinKernel D.potential D.driver D.noiseLaw s.toNNReal x) (gibbsMeasure volume D.potential)).toReal -
      (klDiv (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x) (gibbsMeasure volume D.potential)).toReal := by
  let := D.probability
  let := langevinKernel_isMarkovKernel D.brownian D.smooth D.curvature D.curvature_pos.le D.hessian s.toNNReal
  let := langevinKernel_isMarkovKernel D.brownian D.smooth D.curvature D.curvature_pos.le D.hessian t.toNNReal
  have ht : 0 < t := hs.trans hst
  have hgap : 0 < t-s := sub_pos.mpr hst
  have hKLe := klDiv_langevinKernel_ne_top D.brownian D.smooth D.probability D.curvature D.curvature_pos D.hessian x s hs
  have hKLt := klDiv_langevinKernel_ne_top D.brownian D.smooth D.probability D.curvature D.curvature_pos D.hessian x t ht
  have hFIt := relativeFisherInformation_langevinKernel_ne_top D.brownian D.smooth D.probability D.curvature
    D.curvature_pos D.hessian t.toNNReal (Real.toNNReal_pos.mpr ht) x
  have hh := langevinKernel_entropy_fisher_drop D.brownian D.smooth D.probability D.curvature D.curvature_pos
    D.hessian (langevinKernel D.potential D.driver D.noiseLaw s.toNNReal x) (t-s) hgap
  have he : s.toNNReal+(t-s).toNNReal=t.toNNReal := by
    apply NNReal.eq
    simp only [NNReal.coe_add,Real.coe_toNNReal _ hs.le,Real.coe_toNNReal _ hgap.le,Real.coe_toNNReal _ ht.le]
    ring
  have hcomp : langevinKernel D.potential D.driver D.noiseLaw (t-s).toNNReal ∘ₘ
      langevinKernel D.potential D.driver D.noiseLaw s.toNNReal x =
      langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x := by
    rw [← Kernel.comp_apply,langevinKernel_comp D.brownian D.smooth D.curvature D.curvature_pos.le D.hessian,he]
  simp only [hcomp] at hh
  have hr := ENNReal.toReal_mono hKLe hh
  rw [ENNReal.toReal_add hKLt (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFIt),ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hgap.le] at hr
  change (t-s)*(relativeFisherInformation D.smooth D.probability
    (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)).toReal ≤ _
  linarith

set_option maxHeartbeats 800000 in
/-- Exact genuine post-mixing entropy bound, with all domain and evolution
obligations derived from the actual diffusion assumptions. -/
theorem langevinKernel_salez_entropy_window
    (D : CurvedLangevinData Ω d) (x : E) (a b η : ℝ)
    (ha : 0 < a) (hab : a < b) (hη : 0 < η) (hη1 : η < 1)
    (hTV : ∀ t ∈ Icc a b,
      totalVariationDistance (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
        (gibbsMeasure volume D.potential) ≤ η) :
    klDiv (langevinKernel D.potential D.driver D.noiseLaw b.toNNReal x) (gibbsMeasure volume D.potential) ≤
      ENNReal.ofReal (1/(1-η)+2/((1-η)^2*Real.log (b/a))) := by
  let H := fun t : ℝ =>
    (klDiv (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x) (gibbsMeasure volume D.potential)).toReal
  let I := fun t : ℝ => (curvedPointFisher D t x).toReal
  have hmono : AntitoneOn H (Icc a b) := by
    intro s hs t ht hst
    rcases lt_or_eq_of_le hst with hlt|rfl
    · have hh := curvedPoint_entropy_drop D x s t (ha.trans_le hs.1) hlt
      have h0 : 0 ≤ (t-s)*I t := mul_nonneg (sub_nonneg.mpr hst) ENNReal.toReal_nonneg
      dsimp only [H,I] at *
      linarith
    · exact le_rfl
  have hdrop : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s < t → (t-s)*I t ≤ H s-H t :=
    fun s hs t _ hst => curvedPoint_entropy_drop D x s t (ha.trans_le hs.1) hst
  have hvar : ∀ t ∈ Icc a b, 1/(1-η) < H t → ((1-η)*H t-1)^2 ≤ 2*t*I t := by
    intro t ht hlarge
    have ht0 : 0 < t := ha.trans_le ht.1
    have hh := langevinKernel_entropy_fisher_of_tv D.brownian D.smooth D.probability D.curvature D.curvature_pos
      D.hessian t.toNNReal (Real.toNNReal_pos.mpr ht0) x (1-η) (sub_pos.mpr hη1) (by linarith)
      (by simpa only [@Real.toNNReal_coe t.toNNReal,sub_sub_cancel] using hTV t ht)
      (by simpa only [@Real.toNNReal_coe t.toNNReal] using hlarge)
    simpa only [@Real.toNNReal_coe t.toNNReal,Real.coe_toNNReal _ ht0.le,curvedPointFisher,H,I] using hh
  have hbnd := salez_entropy_window_of_drop H I ha hab (sub_pos.mpr hη1) hmono hdrop hvar
  have hfinite := klDiv_langevinKernel_ne_top D.brownian D.smooth D.probability D.curvature D.curvature_pos D.hessian x b (ha.trans hab)
  rw [← ENNReal.ofReal_toReal hfinite]
  exact ENNReal.ofReal_le_ofReal hbnd

/-- The source window bound is uniform over an arbitrary nonempty set of
initial states once its actual TV profile is below the threshold. -/
theorem curvedEntropyProfile_window_bound
    (D : CurvedLangevinData Ω d) (S : Set E) (hS : S.Nonempty) (a b η : ℝ)
    (ha : 0 < a) (hab : a < b) (hη : 0 < η) (hη1 : η < 1)
    (hTV : curvedTVProfile D S a ≤ η) :
    curvedEntropyProfile D S b ≤ ENNReal.ofReal (1/(1-η)+2/((1-η)^2*Real.log (b/a))) := by
  apply iSup_le
  intro x
  apply langevinKernel_salez_entropy_window D x a b η ha hab hη hη1
  intro t ht
  exact (curvedTV_le_profile D S t x x.property).trans
    (((curvedTVProfile_antitone D hS) ht.1).trans hTV)

end CutoffRigidity
