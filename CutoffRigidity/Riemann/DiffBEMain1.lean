module

public import CutoffRigidity.Riemann.DiffKer
public import CutoffRigidity.Riemann.DiffTight
public import CutoffRigidity.Riemann.DiffAPI
public import CutoffRigidity.Riemann.WeightedRigidity

/-! # Bakry-Emery, pointwise bound: elementary lemmas (workstream BE, part D1)

Bump functions, local-to-pointwise principle, Jensen, duality of the canonical kernel.
-/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set Topology
open scoped Manifold ContDiff ENNReal NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Main1

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]

/-- A smooth compactly supported bump, `0 ≤ ζ`, `ζ x = 1`, supported in a neighbourhood. -/
theorem exists_bump_in {U : Set M} {x : M} (hU : U ∈ 𝓝 x) :
    ∃ ζ : M → ℝ, MSmooth F ζ ∧ HasCompactSupport ζ ∧ (∀ y, 0 ≤ ζ y) ∧ ζ x = 1 ∧
      ∀ y, ζ y ≠ 0 → y ∈ U := by
  obtain ⟨f, hf⟩ := (SmoothBumpFunction.nhds_basis_support (I := 𝓘(ℝ, F)) hU).ex_mem
  refine ⟨f, f.contMDiff, f.hasCompactSupport, fun y => f.nonneg, f.eq_one, fun y hy => ?_⟩
  exact hf (subset_tsupport _ hy)

/-- Local-to-pointwise principle: continuous `u, v` with `∫ ζ u ≤ ∫ ζ v` for all nonnegative test
functions `ζ` satisfy `u ≤ v` everywhere. -/
theorem le_of_integral_le {μ : Measure M} [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v)
    (h : ∀ ζ : testSub F M, (∀ x, 0 ≤ (ζ : M → ℝ) x) →
      ∫ x, (ζ : M → ℝ) x * u x ∂μ ≤ ∫ x, (ζ : M → ℝ) x * v x ∂μ) :
    ∀ x, u x ≤ v x := by
  intro x₀
  by_contra hlt
  push Not at hlt
  have hopen : IsOpen {y | v y < u y} := isOpen_lt hv hu
  obtain ⟨ζ, hζs, hζc, hζ0, hζx, hζU⟩ := exists_bump_in F (hopen.mem_nhds hlt)
  have hh := h ⟨ζ, hζs, hζc⟩ hζ0
  simp only at hh
  have hζcont : Continuous ζ := hζs.continuous
  have i1 : Integrable (fun x => ζ x * u x) μ :=
    (hζcont.mul hu).integrable_of_hasCompactSupport hζc.mul_right
  have i2 : Integrable (fun x => ζ x * v x) μ :=
    (hζcont.mul hv).integrable_of_hasCompactSupport hζc.mul_right
  have hg0 : ∀ x, 0 ≤ ζ x * (u x - v x) := fun x => by
    by_cases hz : ζ x = 0
    · simp [hz]
    · have := hζU x hz
      exact mul_nonneg (hζ0 x) (by simp only [mem_ofPred_eq] at this; linarith)
  have hgi : Integrable (fun x => ζ x * (u x - v x)) μ := by
    have := i1.sub i2
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]; ring
  have hpos : 0 < ∫ x, ζ x * (u x - v x) ∂μ := by
    rw [integral_pos_iff_support_of_nonneg hg0 hgi]
    have hopen2 : IsOpen {y | 0 < ζ y * (u y - v y)} :=
      isOpen_lt continuous_const (hζcont.mul (hu.sub hv))
    refine lt_of_lt_of_le (hopen2.measure_pos μ ⟨x₀, ?_⟩) (measure_mono ?_)
    · simp only [mem_ofPred_eq, hζx]; linarith
    · intro y hy; exact ne_of_gt hy
  have : ∫ x, ζ x * (u x - v x) ∂μ = ∫ x, ζ x * u x ∂μ - ∫ x, ζ x * v x ∂μ := by
    rw [← integral_sub i1 i2]; congr 1; funext x; ring
  linarith

/-- Jensen / Cauchy-Schwarz for a probability measure. -/
theorem sq_integral_le_integral_sq {α : Type*} [MeasurableSpace α] {P : Measure α}
    [IsProbabilityMeasure P] {g : α → ℝ} (hg : MemLp g 2 P) :
    (∫ x, g x ∂P) ^ 2 ≤ ∫ x, g x ^ 2 ∂P := by
  have h1 := variance_nonneg g P
  rw [variance_eq_sub hg] at h1
  simp only [Pi.pow_apply] at h1
  linarith

theorem sqrt_add_le_add_sqrt' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

section Dual

variable {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

/-- Integration of a function a.e. equal to an `L²` class against the canonical kernel. -/
theorem int_Kk_eq_Tc {t : ℝ≥0} (ht : t ≠ 0) (x : M) (u : M →₂[μ] ℝ) {ψ : M → ℝ}
    (h : (u : M → ℝ) =ᵐ[μ] ψ) :
    ∫ y, ψ y ∂Kk F hV hμ t x = Tc F hV hμ t u x := by
  have h1 := (kmeas_integral F hV hμ ht x u).2
  rw [Kk_apply_of_ne F hV hμ ht, ← h1]
  exact integral_congr_ae ((withDensity_absolutelyContinuous μ _).ae_le h.symm)

/-- Bounded continuous functions are in `L²`. -/
theorem memLp_of_bdd {ψ : M → ℝ} (hψ : Continuous ψ) (hb : ∃ C, ∀ x, |ψ x| ≤ C) :
    MemLp ψ 2 μ := by
  obtain ⟨C, hC⟩ := hb
  exact MemLp.of_bound hψ.aestronglyMeasurable C (Eventually.of_forall fun x => by simpa using hC x)

/-- Duality (symmetry of the kernel). -/
theorem duality_Kk {t : ℝ≥0} (ht : t ≠ 0) (ζ : testSub F M) {ψ : M → ℝ} (hψ : Continuous ψ)
    (hb : ∃ C, ∀ x, |ψ x| ≤ C) :
    ∫ x, semi (Kk F hV hμ) t (ζ : M → ℝ) x * ψ x ∂μ =
      ∫ x, (ζ : M → ℝ) x * semi (Kk F hV hμ) t ψ x ∂μ := by
  set u : M →₂[μ] ℝ := (memLp_of_bdd (μ := μ) hψ hb).toLp ψ with hu
  have hu' : (u : M → ℝ) =ᵐ[μ] ψ := MemLp.coeFn_toLp _
  set z := testToL2 F μ ζ with hz
  have hz' : (z : M → ℝ) =ᵐ[μ] ζ := coeFn_testToL2 F μ ζ
  have hsa := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    ((diffFR F hV hμ).semigroup_isSelfAdjoint t) z u
  have e1 : ∀ x, semi (Kk F hV hμ) t (ζ : M → ℝ) x = Tc F hV hμ t z x :=
    fun x => semi_Kk_eq_Tc F hV hμ ht ζ x
  have e2 : ∀ x, semi (Kk F hV hμ) t ψ x = Tc F hV hμ t u x :=
    fun x => int_Kk_eq_Tc F hV hμ ht x u hu'
  simp only [e1, e2]
  have a1 := Tc_ae F hV hμ ht z
  have a2 := Tc_ae F hV hμ ht u
  have lhs : ∫ x, Tc F hV hμ t z x * ψ x ∂μ =
      inner ℝ (((diffFR F hV hμ).semigroup t z : M →₂[μ] ℝ)) u := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [a1, hu'] with x h1 h2
    simp [h1, h2, mul_comm]
  have rhs : ∫ x, (ζ : M → ℝ) x * Tc F hV hμ t u x ∂μ =
      inner ℝ z (((diffFR F hV hμ).semigroup t u : M →₂[μ] ℝ)) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [a2, hz'] with x h1 h2
    simp [h1, h2, mul_comm]
  rw [lhs, rhs]
  exact hsa

end Dual

end Main1

end CutoffRigidity.Riemann.Diff
