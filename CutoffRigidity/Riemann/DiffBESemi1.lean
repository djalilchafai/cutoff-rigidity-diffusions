module

public import CutoffRigidity.Riemann.DiffKer10

/-! # Sup-norm estimates for `K_r g` (workstream BE, part C)

Lipschitz and second-order Taylor estimates in time, uniform in `x`, for the abstract
`Kk` with `KerCanonical F V μ Kk` and a smooth compactly supported `g`.
-/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Sup

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} {μ : Measure M} {Kk : ℝ≥0 → Kernel M M}

theorem semi_abs_le (hK : KerCanonical F V μ Kk) {g : M → ℝ} {C : ℝ} (hC : ∀ x, |g x| ≤ C)
    (r : ℝ≥0) (x : M) : |semi Kk r g x| ≤ C := by
  haveI := (hK.markov r).isProbabilityMeasure x
  have := norm_integral_le_of_norm_le_const (μ := Kk r x) (f := g) (C := C)
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hC y)
  simpa [semi, Real.norm_eq_abs] using this

/-- Lipschitz continuity in time, uniform in `x`. -/
theorem semi_lip (hK : KerCanonical F V μ Kk) (hV : MSmooth F V) {g : M → ℝ} (hg : MSmooth F g)
    (hgc : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : M) (a b : ℝ),
      |semi Kk a.toNNReal g x - semi Kk b.toNNReal g x| ≤ C * |a - b| := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_mgenerator_le F hV hg hgc
  refine ⟨C, hC0, fun x a b => ?_⟩
  have h := (dynkin_lipschitz F hK.dynkin hg hgc hC0 hC x).dist_le_mul a.toNNReal b.toNNReal
  rw [NNReal.dist_eq] at h
  simp only [Real.dist_eq, Real.coe_toNNReal'] at h
  refine h.trans ?_
  exact mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs _ _ _) hC0

/-- Second-order Taylor expansion in time, uniform in `x` (base point `r > 0`). -/
theorem semi_taylor (hK : KerCanonical F V μ Kk) (hV : MSmooth F V) {g : M → ℝ} (hg : MSmooth F g)
    (hgc : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : M) (r r' : ℝ), 0 < r → 0 < r' →
      |semi Kk r'.toNNReal g x - semi Kk r.toNNReal g x -
        (r' - r) * semi Kk r.toNNReal (mgenerator F V g) x| ≤ C * (r' - r) ^ 2 := by
  have hLg := msmooth_mgenerator F hV hg
  have hLgc := hasCompactSupport_mgenerator F V hg hgc
  obtain ⟨C, hC0, hC⟩ := semi_lip F hK hV hLg hLgc
  refine ⟨C, hC0, fun x r r' hr hr' => ?_⟩
  set c := semi Kk r.toNNReal (mgenerator F V g) x with hc
  let φ : ℝ → ℝ := fun τ => semi Kk τ.toNNReal g x - (τ - r) * c
  let φ' : ℝ → ℝ := fun τ => semi Kk τ.toNNReal (mgenerator F V g) x - c
  have hder : ∀ τ ∈ Set.uIcc r r', HasDerivWithinAt φ (φ' τ) (Set.uIcc r r') τ := by
    intro τ hτ
    have hτ0 : 0 < τ := by
      rcases le_total r r' with h | h
      · rw [Set.uIcc_of_le h] at hτ; exact lt_of_lt_of_le hr hτ.1
      · rw [Set.uIcc_of_ge h] at hτ; exact lt_of_lt_of_le hr' hτ.1
    have h1 := hasDerivAt_dynkin F hK.dynkin hg hgc hV x hτ0
    have h2 : HasDerivAt (fun τ : ℝ => (τ - r) * c) c τ := by
      simpa using ((hasDerivAt_id τ).sub_const r).mul_const c
    exact (h1.sub h2).hasDerivWithinAt
  have hbd : ∀ τ ∈ Set.uIcc r r', ‖φ' τ‖ ≤ C * |r' - r| := by
    intro τ hτ
    have : |τ - r| ≤ |r' - r| := abs_sub_left_of_mem_uIcc hτ
    have h := hC x τ r
    simp only [Real.norm_eq_abs, φ', hc]
    exact h.trans (mul_le_mul_of_nonneg_left this hC0)
  have key := (convex_uIcc r r').norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd
    Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [φ, Real.norm_eq_abs, sub_self, zero_mul, sub_zero] at key
  have e : semi Kk r'.toNNReal g x - (r' - r) * c - semi Kk r.toNNReal g x =
      semi Kk r'.toNNReal g x - semi Kk r.toNNReal g x - (r' - r) * c := by ring
  rw [e] at key
  calc _ ≤ C * |r' - r| * |r' - r| := key
    _ = C * (r' - r) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

end Sup

end CutoffRigidity.Riemann.Diff
