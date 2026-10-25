module

public import CutoffRigidity.TotalVariation
public import CutoffRigidity.LangevinSemigroup
public import CutoffRigidity.Gibbs
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-! # Genuine Markov-kernel total variation and mixing times

The normalization is the source supremum of event probability differences.
Kernel contraction follows from the layer-cake representation of actual
[0,1]-valued tests. This module does not assert the Salez cutoff theorem.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

private theorem integral_eq_layercake_unit_interval (μ : Measure α)
    [IsProbabilityMeasure μ] {f : α → ℝ} (hf : Measurable f)
    (hb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    (∫ x, f x ∂μ) = ∫ t in Ioc (0 : ℝ) 1, μ.real {x | t < f x} := by
  have hi : Integrable f μ := (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
    (Eventually.of_forall (fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hb x).1]; exact (hb x).2))
  rw [hi.integral_eq_integral_meas_lt (Eventually.of_forall (fun x => (hb x).1))]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun _ hx => hx.1)
  intro t ht
  have h1 : 1 ≤ t := by
    have hn : ¬ (0 < t ∧ t ≤ 1) := ht.2
    exact le_of_not_ge (fun hh => hn ⟨ht.1, hh⟩)
  have he : {x | t < f x} = ∅ := by
    ext x
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    exact not_lt.mpr (le_trans (hb x).2 h1)
  rw [he]
  simp

/-- The exact bounded-test inequality in the probability normalization of
TV: tests taking values in [0,1] have integral difference at most TV. -/
theorem abs_integral_sub_le_totalVariationDistance (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : α → ℝ} (hf : Measurable f) (hb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ totalVariationDistance μ ν := by
  have htail (η : Measure α) [IsProbabilityMeasure η] :
      IntegrableOn (fun t : ℝ => η.real {x | t < f x}) (Ioc 0 1) := by
    have htAnti : Antitone (fun t : ℝ => η {x | t < f x}) :=
      fun _ _ hst => measure_mono (fun _ hx => lt_of_le_of_lt hst hx)
    have hm : Measurable (fun t : ℝ => η.real {x | t < f x}) := htAnti.measurable.ennreal_toReal
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  rw [integral_eq_layercake_unit_interval μ hf hb, integral_eq_layercake_unit_interval ν hf hb,
    ← integral_sub (htail μ) (htail ν), ← Real.norm_eq_abs]
  have hh := norm_integral_le_of_norm_le_const (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (f := fun t => μ.real {x | t < f x} - ν.real {x | t < f x})
    (C := totalVariationDistance μ ν) ?_
  · simpa using hh
  · filter_upwards with t
    rw [Real.norm_eq_abs]
    exact abs_measureReal_sub_le_totalVariationDistance μ ν (measurableSet_lt measurable_const hf)

/-- Event probabilities under composition are the genuine integrals of the
kernel event probabilities. -/
theorem measureReal_comp_kernel (K : Kernel α β) [IsMarkovKernel K]
    (μ : Measure α) [IsProbabilityMeasure μ] {A : Set β} (hA : MeasurableSet A) :
    (K ∘ₘ μ).real A = ∫ x, (K x).real A ∂μ := by
  change ((K ∘ₘ μ) A).toReal = _
  rw [Measure.bind_apply hA K.aemeasurable]
  exact (integral_toReal (K.measurable_coe hA).aemeasurable
    (Eventually.of_forall (fun x => measure_lt_top (K x) A))).symm

/-- Genuine data processing for arbitrary actual Markov kernels. -/
theorem totalVariationDistance_kernel_comp_le (K : Kernel α β) [IsMarkovKernel K]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    totalVariationDistance (K ∘ₘ μ) (K ∘ₘ ν) ≤ totalVariationDistance μ ν := by
  apply csSup_le (s := {r : ℝ | ∃ A : Set β, MeasurableSet A ∧
    r = |(K ∘ₘ μ).real A - (K ∘ₘ ν).real A|})
    ⟨0, ∅, MeasurableSet.empty, by simp⟩
  rintro r ⟨A, hA, rfl⟩
  rw [measureReal_comp_kernel K μ hA, measureReal_comp_kernel K ν hA]
  apply abs_integral_sub_le_totalVariationDistance μ ν (K.measurable_coe hA).ennreal_toReal
  intro x
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

/-- The genuine worst-initial-state TV profile over the specified set. -/
@[expose] noncomputable def kernelTVProfile (K : ℝ≥0 → Kernel α α)
    (μ : Measure α) (S : Set α) (t : ℝ≥0) : ℝ :=
  sSup ((fun x => totalVariationDistance (K t x) μ) '' S)

theorem kernelTVProfile_nonneg (K : ℝ≥0 → Kernel α α)
    (hK : ∀ t, IsMarkovKernel (K t)) (μ : Measure α) [IsProbabilityMeasure μ]
    (S : Set α) (hS : S.Nonempty) (t : ℝ≥0) : 0 ≤ kernelTVProfile K μ S t := by
  let := hK t
  obtain ⟨x, hx⟩ := hS
  apply le_trans (totalVariationDistance_nonneg (K t x) μ)
  apply le_csSup
  · exact ⟨1, by rintro r ⟨y, _, rfl⟩; exact totalVariationDistance_le_one _ _⟩
  · exact ⟨x, hx, rfl⟩

theorem kernelTVProfile_le_one (K : ℝ≥0 → Kernel α α)
    (hK : ∀ t, IsMarkovKernel (K t)) (μ : Measure α) [IsProbabilityMeasure μ]
    (S : Set α) (hS : S.Nonempty) (t : ℝ≥0) : kernelTVProfile K μ S t ≤ 1 := by
  let := hK t
  apply csSup_le (hS.image _)
  rintro r ⟨x, _, rfl⟩
  exact totalVariationDistance_le_one _ _

/-- An invariant actual Markov semigroup has a nonincreasing genuine TV
profile. Invariance is the actual measure identity, not an entropy premise. -/
theorem kernelTVProfile_antitone (K : ℝ≥0 → Kernel α α)
    (hK : ∀ t, IsMarkovKernel (K t))
    (hcomp : ∀ s t, K t ∘ₖ K s = K (s + t))
    (μ : Measure α) [IsProbabilityMeasure μ]
    (hinv : ∀ t, K t ∘ₘ μ = μ) (S : Set α) (hS : S.Nonempty) :
    Antitone (kernelTVProfile K μ S) := by
  intro s t hst
  obtain ⟨r, rfl⟩ := exists_add_of_le hst
  let := hK s
  let := hK r
  let := hK (s + r)
  apply csSup_le (hS.image _)
  rintro z ⟨x, hx, rfl⟩
  have hc : totalVariationDistance (K (s + r) x) μ ≤ totalVariationDistance (K s x) μ := by
    conv_lhs => rw [← hcomp s r, ← hinv r]
    exact totalVariationDistance_kernel_comp_le (K r) (K s x) μ
  apply hc.trans
  apply le_csSup
  · exact ⟨1, by rintro z ⟨y, _, rfl⟩; exact totalVariationDistance_le_one _ _⟩
  · exact ⟨x, hx, rfl⟩

/-- The actual threshold mixing time, allowing infinity when the threshold
is never reached. Finite candidate times are embedded into ENNReal. -/
@[expose] noncomputable def kernelTVMixingTime (K : ℝ≥0 → Kernel α α)
    (μ : Measure α) (S : Set α) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ t : ℝ≥0, ⨅ (_ : kernelTVProfile K μ S t ≤ ε), (t : ℝ≥0∞)

theorem kernelTVMixingTime_le_of_profile_le (K : ℝ≥0 → Kernel α α)
    (μ : Measure α) (S : Set α) (ε : ℝ) (t : ℝ≥0)
    (h : kernelTVProfile K μ S t ≤ ε) : kernelTVMixingTime K μ S ε ≤ t :=
  iInf_le_of_le t (iInf_le_of_le h le_rfl)

theorem profile_gt_of_lt_kernelTVMixingTime (K : ℝ≥0 → Kernel α α)
    (μ : Measure α) (S : Set α) (ε : ℝ) (t : ℝ≥0)
    (h : (t : ℝ≥0∞) < kernelTVMixingTime K μ S ε) : ε < kernelTVProfile K μ S t := by
  by_contra hn
  exact not_lt_of_ge (kernelTVMixingTime_le_of_profile_le K μ S ε t (le_of_not_gt hn)) h

/-- Increasing the threshold decreases the actual mixing time. -/
theorem kernelTVMixingTime_antitone_threshold (K : ℝ≥0 → Kernel α α)
    (μ : Measure α) (S : Set α) : Antitone (kernelTVMixingTime K μ S) := by
  intro ε η hεη
  apply le_iInf
  intro t
  apply le_iInf
  intro ht
  exact kernelTVMixingTime_le_of_profile_le K μ S η t (ht.trans hεη)

/-- Finiteness is equivalent to the existence of a genuine finite-time
threshold witness, without assuming convergence or a cutoff conclusion. -/
theorem kernelTVMixingTime_lt_top_iff (K : ℝ≥0 → Kernel α α)
    (μ : Measure α) (S : Set α) (ε : ℝ) :
    kernelTVMixingTime K μ S ε < ⊤ ↔ ∃ t : ℝ≥0, kernelTVProfile K μ S t ≤ ε := by
  simp only [kernelTVMixingTime, iInf_lt_iff, ENNReal.coe_lt_top, exists_prop, and_true]

/-- Strictly after the infimum, the threshold holds for an antitone
profile; no unproved right-continuity or threshold-attainment is used. -/
theorem profile_le_of_kernelTVMixingTime_lt (K : ℝ≥0 → Kernel α α)
    (μ : Measure α) (S : Set α) (ε : ℝ)
    (hmono : Antitone (kernelTVProfile K μ S)) (t : ℝ≥0)
    (h : kernelTVMixingTime K μ S ε < (t : ℝ≥0∞)) : kernelTVProfile K μ S t ≤ ε := by
  obtain ⟨s, hs⟩ := iInf_lt_iff.mp h
  obtain ⟨hsε, hst⟩ := iInf_lt_iff.mp hs
  exact (hmono (le_of_lt (ENNReal.coe_lt_coe.mp hst))).trans hsε

/-- Exact deterministic time scaling of the genuine threshold infimum,
including infinite mixing times. -/
theorem kernelTVMixingTime_time_scale_mul (K : ℝ≥0 → Kernel α α)
    (μ : Measure α) (S : Set α) (ε : ℝ) (a : ℝ≥0) (ha : a ≠ 0) :
    (a : ℝ≥0∞) * kernelTVMixingTime (fun t => K (a * t)) μ S ε =
      kernelTVMixingTime K μ S ε := by
  have ha0 : (a : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr ha
  change (a : ℝ≥0∞) * (⨅ t : ℝ≥0, ⨅ (_ : kernelTVProfile K μ S (a * t) ≤ ε),
    (t : ℝ≥0∞)) = ⨅ t : ℝ≥0, ⨅ (_ : kernelTVProfile K μ S t ≤ ε), (t : ℝ≥0∞)
  rw [ENNReal.mul_iInf_of_ne ha0 ENNReal.coe_ne_top]
  simp_rw [ENNReal.mul_iInf_of_ne ha0 ENNReal.coe_ne_top, ← ENNReal.coe_mul]
  exact (Equiv.mulLeft₀ a ha).surjective.iInf_comp
    (fun t : ℝ≥0 => ⨅ (_ : kernelTVProfile K μ S t ≤ ε), (t : ℝ≥0∞))

theorem kernelTVMixingTime_time_scale (K : ℝ≥0 → Kernel α α)
    (μ : Measure α) (S : Set α) (ε : ℝ) (a : ℝ≥0) (ha : a ≠ 0) :
    kernelTVMixingTime (fun t => K (a * t)) μ S ε =
      (a⁻¹ : ℝ≥0) * kernelTVMixingTime K μ S ε := by
  calc
    _ = ((a⁻¹ : ℝ≥0) : ℝ≥0∞) * ((a : ℝ≥0∞) *
        kernelTVMixingTime (fun t => K (a * t)) μ S ε) := by
      rw [← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ ha, ENNReal.coe_one, one_mul]
    _ = _ := by rw [kernelTVMixingTime_time_scale_mul K μ S ε a ha]

/-- An eventual finite-time threshold witness is exactly the eventual
finiteness assumption appearing in the source mixing-time theorem. -/
theorem eventually_kernelTVMixingTime_finite_iff
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (K : ∀ n, ℝ≥0 → Kernel (X n) (X n)) (μ : ∀ n, Measure (X n))
    (S : ∀ n, Set (X n)) (ε : ℝ) :
    (∀ᶠ n in atTop, kernelTVMixingTime (K n) (μ n) (S n) ε < ⊤) ↔
      ∀ᶠ n in atTop, ∃ t : ℝ≥0, kernelTVProfile (K n) (μ n) (S n) t ≤ ε := by
  simp_rw [kernelTVMixingTime_lt_top_iff]

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual source Langevin TV mixing time, rather than a scalar profile
standing in for a process distance. -/
@[expose] noncomputable def langevinTVMixingTime (V : E → ℝ)
    (B : ℝ≥0 → Ω → E) (P : Measure Ω) (S : Set E) (ε : ℝ) : ℝ≥0∞ :=
  kernelTVMixingTime (langevinKernel V B P) (gibbsMeasure volume V) S ε

/-- The genuine nonlinear Langevin TV profile is nonincreasing when the
actual Gibbs law is invariant. This explicitly records the invariant-law
bridge still needed by the full paper construction. -/
theorem langevinKernelTVProfile_antitone
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : E, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hinv : ∀ t : ℝ≥0, langevinKernel V B P t ∘ₘ gibbsMeasure volume V = gibbsMeasure volume V)
    (S : Set E) (hS : S.Nonempty) :
    Antitone (kernelTVProfile (langevinKernel V B P) (gibbsMeasure volume V) S) := by
  let := hprob
  exact kernelTVProfile_antitone _
    (langevinKernel_isMarkovKernel hB hV κ hκ hHess)
    (langevinKernel_comp hB hV κ hκ hHess) _ hinv S hS

end CutoffRigidity
