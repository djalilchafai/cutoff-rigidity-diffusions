module

public import CutoffRigidity.Riemann.DiffInstance2
public import CutoffRigidity.Riemann.DiffGapHilbert
public import CutoffRigidity.Riemann.EigenFinite
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.BumpFunction

/-! # Attainment of the spectral gap: manifold lemmas (HPOS-G)

Locality of `𝓛`, symmetry `∫ v 𝓛b = ∫ b 𝓛v` for `b` compactly supported and `v` merely smooth,
the fundamental lemma of the calculus of variations for continuous functions, and the translation
of the spectral gap `mSpectralGap` into the Poincare inequality on `D` and its sharpness.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set ProbabilityTheory
open scoped Manifold ContDiff ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section GapManifold

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]

/-- Locality of the generator on smooth functions. -/
theorem mgenerator_congr_of_eventuallyEq (V : M → ℝ) {f g : M → ℝ} (hf : MSmooth F f)
    (hg : MSmooth F g) {x : M} (h : f =ᶠ[𝓝 x] g) :
    mgenerator F V f x = mgenerator F V g x := by
  have hg' : MSmooth F (fun y => (-1 : ℝ) * g y) := contMDiff_const.mul hg
  have hev : (fun y => f y + (-1 : ℝ) * g y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [h] with y hy
    simp [hy]
  have hnot : x ∉ tsupport (fun y => f y + (-1 : ℝ) * g y) :=
    notMem_tsupport_iff_eventuallyEq.2 hev
  have h0 : mgenerator F V (fun y => f y + (-1 : ℝ) * g y) x = 0 :=
    CutoffRigidity.Riemann.mgenerator_eq_zero_of_notMem_tsupport F V (hf.add hg') hnot
  rw [mgenerator_add F hf hg', mgenerator_const_mul F (-1) hg] at h0
  linarith

variable [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

include hV hμ in
/-- Symmetry of `𝓛`: `∫ v 𝓛b = ∫ b 𝓛v` for `v` smooth and `b` smooth with compact support. -/
theorem integral_mul_generator_comm {v b : M → ℝ} (hv : MSmooth F v) (hb : MSmooth F b)
    (hbc : HasCompactSupport b) :
    ∫ x, v x * mgenerator F V b x ∂μ = ∫ x, b x * mgenerator F V v x ∂μ := by
  haveI := sigmaCompactSpace_of_complete_riemannian (F := F) (M := M)
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace F M
  obtain ⟨K', hK', hKK'⟩ := exists_compact_superset hbc
  obtain ⟨χ, h1, h0, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, F)
    (n := ⊤) (isClosed_tsupport b) hKK'
  have hχ : MSmooth F (χ : M → ℝ) := χ.contMDiff
  set u : M → ℝ := fun x => χ x * v x with hu
  have hus : MSmooth F u := hχ.mul hv
  have huc : HasCompactSupport u :=
    HasCompactSupport.intro hK' fun x hx => by simp [hu, h0 x hx]
  have e1 := weightedIBP_of_isWeightedVolume F hV hμ u b hus hb huc
  have e2 := weightedIBP_of_isWeightedVolume F hV hμ b u hb hus hbc
  have e3 : ∫ x, carre F b u x ∂μ = ∫ x, carre F u b x ∂μ :=
    integral_congr_ae (Eventually.of_forall fun x => carre_comm F _ _ x)
  have hloc := eventually_nhdsSet_iff_forall.1 h1
  have p1 : ∫ x, u x * mgenerator F V b x ∂μ = ∫ x, v x * mgenerator F V b x ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport b
    · have := (hloc x hx).self_of_nhds
      simp [hu, this]
    · simp only
      rw [CutoffRigidity.Riemann.mgenerator_eq_zero_of_notMem_tsupport F V hb hx]; simp
  have p2 : ∫ x, b x * mgenerator F V u x ∂μ = ∫ x, b x * mgenerator F V v x ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport b
    · have hev : u =ᶠ[𝓝 x] v := by
        filter_upwards [hloc x hx] with y hy
        simp [hu, hy]
      simp only
      rw [mgenerator_congr_of_eventuallyEq F V hus hv hev]
    · simp only
      rw [image_eq_zero_of_notMem_tsupport hx]; simp
  rw [← p1, ← p2]
  linarith

/-- Fundamental lemma of the calculus of variations on `M`. -/
theorem eq_zero_of_integral_test [μ.IsOpenPosMeasure] {g : M → ℝ} (hg : Continuous g)
    (h : ∀ b : M → ℝ, MSmooth F b → HasCompactSupport b → ∫ x, b x * g x ∂μ = 0) (x : M) :
    g x = 0 := by
  have pos : ∀ g : M → ℝ, Continuous g →
      (∀ b : M → ℝ, MSmooth F b → HasCompactSupport b → ∫ x, b x * g x ∂μ = 0) →
      ∀ x, ¬ 0 < g x := by
    intro g hg h x hx
    have hU : IsOpen {y | 0 < g y} := isOpen_lt continuous_const hg
    obtain ⟨f, -, hsub⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, F)) x).mem_iff.1
      (hU.mem_nhds hx)
    have hfc : Continuous (fun y => f y * g y) := f.continuous.mul hg
    have hcs : HasCompactSupport (fun y => f y * g y) := f.hasCompactSupport.mul_right
    have hnn : 0 ≤ fun y => f y * g y := by
      intro y
      simp only [Pi.zero_apply]
      by_cases hy : y ∈ tsupport f
      · exact mul_nonneg f.nonneg (hsub hy).le
      · rw [image_eq_zero_of_notMem_tsupport hy]; simp
    have hx' : (fun y => f y * g y) x ≠ 0 := by
      simp only [f.eq_one, one_mul]; exact hx.ne'
    have := hfc.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) hcs hnn hx'
    have h0 := h f f.contMDiff f.hasCompactSupport
    linarith
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine pos (fun y => -g y) hg.neg (fun b hb hbc => ?_) x (by linarith)
    have := h b hb hbc
    simp only [mul_neg, integral_neg, this, neg_zero]
  · exact pos g hg h x hgt

end GapManifold

end CutoffRigidity.Riemann.Diff
