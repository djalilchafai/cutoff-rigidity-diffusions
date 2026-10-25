module

public import CutoffRigidity.Riemann.DiffEllipticRn11

/-! # Smoothness of weak solutions of `-div(ϱ A ∇u) + λ ϱ u = ϱ g`
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : OrthonormalBasis ι ℝ E)

theorem locL2_of_continuousOn {Ω : Set E} {f : E → ℝ} (hf : ContinuousOn f Ω) : LocL2 Ω f := by
  intro K hK hKΩ
  have hfK : ContinuousOn f K := hf.mono hKΩ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hfK
  haveI : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  refine MemLp.of_bound (hfK.aestronglyMeasurable hK.measurableSet) C ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx using hC x hx

theorem locL2_mul {Ω : Set E} {f a : E → ℝ} (hf : LocL2 Ω f) (ha : ContinuousOn a Ω) :
    LocL2 Ω (fun x => a x * f x) := by
  intro K hK hKΩ
  have haK : ContinuousOn a K := ha.mono hKΩ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn haK
  have h1 := hf K hK hKΩ
  refine MemLp.of_le_mul (c := C) h1 ((haK.aestronglyMeasurable hK.measurableSet).mul
    h1.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC x hx) (norm_nonneg _)

theorem integrable_mul_test_loc {Ω : Set E} {u : E → ℝ} (hu : LocL2 Ω u) {ψ : E → ℝ}
    (hψ : IsTest Ω ψ) (hΩ : IsOpen Ω) : Integrable (fun x => ψ x * u x) volume := by
  obtain ⟨χ, hχ, hχc, hχΩ, hχ1, -⟩ := exists_cutoff hψ.2.1 hΩ hψ.2.2
  have h1 : MemLp (fun x => ψ x * u x) 2 volume := memLp_mul_test hu hψ
  have h2 : MemLp χ 2 volume := hχ.continuous.memLp_of_hasCompactSupport hχc
  have := h1.integrable_mul h2
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : ψ x = 0
  · simp [hx]
  · have := hχ1 x (subset_tsupport _ hx)
    simp [this]

/-- **Weak solutions of divergence form elliptic equations with smooth coefficients are smooth.** -/
theorem weak_solution_smooth {Ω : Set E} (hΩ : IsOpen Ω) {A : ι → ι → E → ℝ}
    (hAs : ∀ i j, ContDiffOn ℝ ∞ (A i j) Ω) (hAsym : ∀ i j, ∀ x ∈ Ω, A i j x = A j i x)
    (hAell : ∀ x ∈ Ω, ∃ c > 0, ∀ ξ : ι → ℝ,
      c * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, A i j x * ξ j * ξ i)
    {ϱ : E → ℝ} (hϱ : ContDiffOn ℝ ∞ ϱ Ω) (hϱpos : ∀ x ∈ Ω, 0 < ϱ x) (lam : ℝ)
    {g : E → ℝ} (hg : ContDiffOn ℝ ∞ g Ω) {u : E → ℝ} {u' : ι → E → ℝ}
    (hu : LocH1 b Ω u u')
    (hweak : ∀ φ, IsTest Ω φ →
      (∑ i, ∑ j, ∫ x, A i j x * u' j x * pd (b i) φ x * ϱ x) + lam * ∫ x, u x * φ x * ϱ x =
        ∫ x, g x * φ x * ϱ x) :
    ∃ ū : E → ℝ, ContDiffOn ℝ ∞ ū Ω ∧ u =ᵐ[volume.restrict Ω] ū := by
  set At : ι → ι → E → ℝ := fun i j x => ϱ x * A i j x with hAt
  have hAts : ∀ i j, ContDiffOn ℝ ∞ (At i j) Ω := fun i j => hϱ.mul (hAs i j)
  have hAtsym : ∀ i j, ∀ x ∈ Ω, At i j x = At j i x := fun i j x hx => by
    simp only [hAt, hAsym i j x hx]
  have hAtell : ∀ x ∈ Ω, ∃ c > 0, ∀ ξ : ι → ℝ,
      c * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, At i j x * ξ j * ξ i := by
    intro x hx
    obtain ⟨c, hc, hell⟩ := hAell x hx
    refine ⟨ϱ x * c, mul_pos (hϱpos x hx) hc, fun ξ => ?_⟩
    have := mul_le_mul_of_nonneg_left (hell ξ) (hϱpos x hx).le
    calc ϱ x * c * ∑ i, ξ i ^ 2 = ϱ x * (c * ∑ i, ξ i ^ 2) := by ring
      _ ≤ ϱ x * ∑ i, ∑ j, A i j x * ξ j * ξ i := this
      _ = _ := by
        simp only [hAt, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        ring
  set F : E → ℝ := fun x => ϱ x * g x - lam * (ϱ x * u x) with hFdef
  have hF : LocL2 Ω F := by
    intro K hK hKΩ
    exact ((locL2_of_continuousOn (hϱ.continuousOn.mul hg.continuousOn)) K hK hKΩ).sub
      (((locL2_mul hu.l2 hϱ.continuousOn) K hK hKΩ).const_mul lam)
  have heq : LocEq b Ω At u' F := by
    intro φ hφ
    have h := hweak φ hφ
    have I1 : Integrable (fun x => g x * φ x * ϱ x) volume := by
      have hs := contDiff_mul_of_contDiffOn hΩ hφ.1 hφ.2.2 (hϱ.mul hg)
      refine (hs.continuous.integrable_of_hasCompactSupport (hφ.2.1.mul_right)).congr
        (Filter.Eventually.of_forall fun x => ?_)
      ring
    have I2 : Integrable (fun x => u x * φ x * ϱ x) volume := by
      have hψ : IsTest Ω (fun x => φ x * ϱ x) :=
        ⟨contDiff_mul_of_contDiffOn hΩ hφ.1 hφ.2.2 hϱ, hφ.2.1.mul_right,
          tsupport_mul_subset_left.trans hφ.2.2⟩
      refine (integrable_mul_test_loc hu.l2 hψ hΩ).congr (Filter.Eventually.of_forall fun x => ?_)
      ring
    have e1 : ∫ x, F x * φ x = (∫ x, g x * φ x * ϱ x) - lam * ∫ x, u x * φ x * ϱ x := by
      rw [← integral_const_mul, ← integral_sub I1 (I2.const_mul lam)]
      congr 1; funext x; simp only [hFdef]; ring
    rw [e1]
    have e2 : ∀ i j, ∫ x, At i j x * u' j x * pd (b i) φ x =
        ∫ x, A i j x * u' j x * pd (b i) φ x * ϱ x := by
      intro i j; congr 1; funext x; simp only [hAt]; ring
    simp only [e2]
    linarith
  have hFreg : ∀ m, LocSob b Ω (m + 1) u → LocSob b Ω m F := by
    intro m hum χ hχ
    have hs1 : ContDiff ℝ ∞ (fun x => χ x * (ϱ x * g x)) :=
      contDiff_mul_of_contDiffOn hΩ hχ.1 hχ.2.2 (hϱ.mul hg)
    have S1 := (Sob.of_smooth b m hs1 hχ.2.1.mul_right).1
    have hs2 : ContDiff ℝ ∞ (fun x => χ x * ϱ x) :=
      contDiff_mul_of_contDiffOn hΩ hχ.1 hχ.2.2 hϱ
    have S2 := sob_mul_of_locSob b hΩ hum hs2 hχ.2.1.mul_right
      (tsupport_mul_subset_left.trans hχ.2.2)
    have S2' := Sob.mono b (Nat.le_succ m) S2
    have S3 := (Sob.smul b lam S2').1
    have S4 := (Sob.sub b S1 S3).1
    refine Sob.congr_ae b S4 (Filter.Eventually.of_forall fun x => ?_)
    simp only [hFdef]; ring
  have h1 := locSob_all b hΩ hAts hAtsym hAtell hu hF heq hFreg
  exact exists_smooth_global b hΩ (fun m => (h1 m).mono b (Nat.le_succ m))

end CutoffRigidity.Riemann.Diff
