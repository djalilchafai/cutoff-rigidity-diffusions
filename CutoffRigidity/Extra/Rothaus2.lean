module

public import Mathlib
public import CutoffRigidity.Statements
public import CutoffRigidity.Extra.Rothaus1

/-! # Rothaus remark (stage 2): abstract forms, optimal constants, entropy lemmas

`Form μ` is an abstract Dirichlet-type form `(Q, E)` on a probability space (the `H¹` space and the energy
`∫|∇f|²` of the compact-manifold setting), `optPI`/`optLSI` the optimal Poincaré / log-Sobolev constants in the
style of `CutCur.optimalPI`/`CutCur.optimalLSI`, with the class of test functions `Q` instead of the smooth class.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace CutoffRigidity.Rothaus

/-- An abstract form on the measure space `(X, μ)`: a class `Q` of functions (the energy domain, e.g. `H¹`) and an
energy `E`, quadratic and invariant under adding constants; members of `Q` are in `L²(μ)` and have
`f² log(1+f²)` integrable (membership in the Orlicz class `L² log L`). -/
structure Form {X : Type*} [MeasurableSpace X] (μ : Measure X) where
  Q : Set (X → ℝ)
  E : (X → ℝ) → ℝ
  smul_mem : ∀ (c : ℝ) (f : X → ℝ), f ∈ Q → c • f ∈ Q
  add_const_mem : ∀ (c : ℝ) (f : X → ℝ), f ∈ Q → (fun x => f x + c) ∈ Q
  E_nonneg : ∀ f ∈ Q, 0 ≤ E f
  E_smul : ∀ (c : ℝ) (f : X → ℝ), f ∈ Q → E (c • f) = c ^ 2 * E f
  E_add_const : ∀ (c : ℝ) (f : X → ℝ), f ∈ Q → E (fun x => f x + c) = E f
  memLp : ∀ f ∈ Q, MemLp f 2 μ
  integrable_Θ : ∀ f ∈ Q, Integrable (fun x => Θ (f x)) μ

namespace Form

set_option linter.unusedSectionVars false

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Optimal Poincaré constant of the form. -/
noncomputable def optPI (F : Form μ) : ℝ :=
  sInf {C : ℝ | 0 ≤ C ∧ ∀ f ∈ F.Q, variance f μ ≤ C * F.E f}

/-- Optimal logarithmic Sobolev constant of the form. -/
noncomputable def optLSI (F : Form μ) : ℝ :=
  sInf {C : ℝ | 0 ≤ C ∧ ∀ f ∈ F.Q, CutCur.entropyOf μ (fun x => f x ^ 2) ≤ C * F.E f}

section Basic

variable [IsFiniteMeasure μ] (F : Form μ)

theorem integrable_sq {f : X → ℝ} (hf : f ∈ F.Q) : Integrable (fun x => f x ^ 2) μ :=
  (F.memLp f hf).integrable_sq

theorem integrable_self {f : X → ℝ} (hf : f ∈ F.Q) : Integrable f μ :=
  (F.memLp f hf).integrable one_le_two

theorem integrable_flog {f : X → ℝ} (hf : f ∈ F.Q) :
    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) μ := by
  have hm : AEStronglyMeasurable (fun x => f x ^ 2 * Real.log (f x ^ 2)) μ :=
    Real.continuous_mul_log.comp_aestronglyMeasurable (F.integrable_sq hf).aestronglyMeasurable
  refine Integrable.mono' ((F.integrable_Θ f hf).add (integrable_const 1)) hm (Eventually.of_forall fun x => ?_)
  simpa using abs_sq_mul_log_sq_le (f x)

end Basic

end Form

/-- Entropy is positively homogeneous. -/
theorem entropyOf_const_mul {X : Type*} [MeasurableSpace X] {μ : Measure X} {h : X → ℝ} {a : ℝ} (ha : 0 < a)
    (h1 : Integrable h μ) (h2 : Integrable (fun x => h x * Real.log (h x)) μ) :
    CutCur.entropyOf μ (fun x => a * h x) = a * CutCur.entropyOf μ h := by
  unfold CutCur.entropyOf
  have hpt : ∀ x, a * h x * Real.log (a * h x) = a * (h x * Real.log (h x)) + Real.log a * (a * h x) := by
    intro x
    by_cases hx : h x = 0
    · simp [hx]
    · rw [Real.log_mul ha.ne' hx]; ring
  simp_rw [hpt]
  rw [integral_add (h2.const_mul a) ((h1.const_mul a).const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul]
  by_cases hM : ∫ x, h x ∂μ = 0
  · simp [hM]
  · rw [Real.log_mul ha.ne' hM]; ring

/-- Gibbs-type upper bound: `Ent(h) ≤ ∫ (h log h - h log c - h + c)` for every `c > 0`, `h ≥ 0`, on a probability space. -/
theorem entropyOf_le_integral {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {h : X → ℝ} (h0 : ∀ x, 0 ≤ h x) (h1 : Integrable h μ) (h2 : Integrable (fun x => h x * Real.log (h x)) μ)
    {c : ℝ} (hc : 0 < c) :
    CutCur.entropyOf μ h ≤ ∫ x, (h x * Real.log (h x) - h x * Real.log c - h x + c) ∂μ := by
  unfold CutCur.entropyOf
  have hA : Integrable (fun x => h x * Real.log (h x) - h x * Real.log c) μ := h2.sub (h1.mul_const _)
  have hB : Integrable (fun x => h x * Real.log (h x) - h x * Real.log c - h x) μ := hA.sub h1
  have hI : ∫ x, (h x * Real.log (h x) - h x * Real.log c - h x + c) ∂μ =
      ∫ x, h x * Real.log (h x) ∂μ - (∫ x, h x ∂μ) * Real.log c - ∫ x, h x ∂μ + c := by
    rw [integral_add hB (integrable_const c), integral_sub hA h1, integral_sub h2 (h1.mul_const _),
      integral_mul_const]
    simp
  rw [hI]
  set M := ∫ x, h x ∂μ with hM
  have hM0 : 0 ≤ M := integral_nonneg h0
  suffices hs : M - c ≤ M * Real.log M - M * Real.log c by linarith
  rcases hM0.eq_or_lt with hM' | hM'
  · rw [← hM']; simp; exact hc.le
  · have := Real.log_le_sub_one_of_pos (div_pos hc hM')
    rw [Real.log_div hc.ne' hM'.ne'] at this
    have h3 := mul_le_mul_of_nonneg_left this hM'.le
    have h4 : M * (c / M - 1) = c - M := by field_simp
    nlinarith

end CutoffRigidity.Rothaus
