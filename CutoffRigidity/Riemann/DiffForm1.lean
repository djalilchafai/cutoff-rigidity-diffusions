module

public import CutoffRigidity.Riemann.DiffForm
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! # Density of test functions in `L²(μ)` (workstream DIR)

On a complete connected Riemannian manifold, `𝒟 = C_c^∞(M)` is dense in `L²(μ)` for every finite
Borel measure `μ`: compactly supported continuous functions are dense (`μ` is regular since `M` is
`σ`-compact and pseudometrizable), and they are uniformly approximated by smooth functions
with support in the same compact set (Mathlib `Continuous.exists_contMDiff_approx`).
-/

@[expose] public section

open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Dense

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]

/-- A continuous compactly supported function is approximated in `L²(μ)` by test functions. -/
theorem exists_test_approx [SigmaCompactSpace M] {μ : Measure M} [IsFiniteMeasure μ] {g : M → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 < δ) :
    ∃ h : testSub F M, ∀ x, |(h : M → ℝ) x - g x| < δ := by
  obtain ⟨h, hh1, hh2⟩ := hg.exists_contMDiff_approx (I := 𝓘(ℝ, F)) (n := ⊤)
    (ε := fun _ => δ) continuous_const (fun _ => hδ)
  refine ⟨⟨⇑h, h.contMDiff, ?_⟩, fun x => by simpa [Real.dist_eq] using hh1 x⟩
  refine hgc.mono' ?_
  exact hh2.trans subset_closure

variable [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]

/-- **Density of test functions in `L²(μ)`** (`μ` finite). -/
theorem dense_test {μ : Measure M} [IsFiniteMeasure μ] : DenseRange (testToL2 F μ) := by
  haveI := sigmaCompactSpace_of_complete_riemannian (F := F) (M := M)
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace F M
  haveI : μ.Regular := inferInstance
  rw [Metric.denseRange_iff]
  intro u r hr
  have hu : MemLp (u : M → ℝ) 2 μ := Lp.memLp u
  set c : ℝ≥0∞ := μ univ ^ ((2 : ℝ≥0∞).toReal⁻¹) with hc
  have hcfin : c ≠ ⊤ := by
    refine ENNReal.rpow_ne_top_of_nonneg (by simp) (measure_ne_top _ _)
  obtain ⟨g, hgc, hgn, hgcont, hgmem⟩ := hu.exists_hasCompactSupport_eLpNorm_sub_le
    (p := 2) (by norm_num) (ε := ENNReal.ofReal (r / 4)) (by simpa using hr)
  set δ : ℝ := (r / 4) / (c.toReal + 1) with hδ
  have hδpos : 0 < δ := by
    have := ENNReal.toReal_nonneg (a := c)
    positivity
  obtain ⟨h, hh⟩ := exists_test_approx F hgcont hgc (μ := μ) hδpos
  refine ⟨h, ?_⟩
  have hhmem := testSub_memLp F h μ
  have h1 : eLpNorm ((u : M → ℝ) - (h : M → ℝ)) 2 μ ≤ ENNReal.ofReal (r / 2) := by
    have e : (u : M → ℝ) - (h : M → ℝ) = ((u : M → ℝ) - g) + (g - (h : M → ℝ)) := by abel
    rw [e]
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    have h2 : eLpNorm (g - (h : M → ℝ)) 2 μ ≤ ENNReal.ofReal (r / 4) := by
      have := eLpNorm_le_of_ae_bound (p := 2) (μ := μ) (f := g - (h : M → ℝ)) (C := δ)
        (hgmem.aestronglyMeasurable.sub hhmem.aestronglyMeasurable) (Eventually.of_forall fun x => by
          rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm]; exact (hh x).le)
      refine this.trans ?_
      rw [← hc]
      have hmul : c * ENNReal.ofReal δ = ENNReal.ofReal (c.toReal * δ) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hcfin]
      rw [hmul]
      apply ENNReal.ofReal_le_ofReal
      rw [hδ, ← mul_div_assoc, div_le_iff₀ (by positivity)]
      have := ENNReal.toReal_nonneg (a := c)
      nlinarith
    calc _ ≤ eLpNorm ((u : M → ℝ) - g) 2 μ + eLpNorm (g - (h : M → ℝ)) 2 μ := le_rfl
      _ ≤ ENNReal.ofReal (r / 4) + ENNReal.ofReal (r / 4) := add_le_add hgn h2
      _ = ENNReal.ofReal (r / 2) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  rw [dist_eq_norm]
  have e2 : u - testToL2 F μ h = (hu.sub hhmem).toLp ((u : M → ℝ) - (h : M → ℝ)) := by
    rw [MemLp.toLp_sub hu hhmem, Lp.toLp_coeFn]
    rfl
  rw [e2, Lp.norm_toLp]
  have : (eLpNorm ((u : M → ℝ) - (h : M → ℝ)) 2 μ).toReal ≤ r / 2 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  linarith

end Dense

end CutoffRigidity.Riemann.Diff
