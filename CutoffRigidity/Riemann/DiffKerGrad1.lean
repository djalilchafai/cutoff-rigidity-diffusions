module

public import CutoffRigidity.Riemann.DiffKer2
public import CutoffRigidity.Riemann.DiffChart

/-! # Local gradient bounds in a chart (workstream KER-GRAD)

For a bounded operator `B` on `L²(μ)` with smooth representatives, the chart derivative of the
representative is locally bounded by `C ‖u‖` (closed graph theorem into `C(Kc, F →L ℝ)`, using
the theorem on uniform limits of derivatives).
-/

@[expose] public section

open Bundle MeasureTheory Filter Set Topology
open scoped Manifold ContDiff ENNReal Topology NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Grad1

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

include hV hμ

/-- Chart derivative bound (closed graph theorem). -/
theorem chart_deriv_bound (B : (M →₂[μ] ℝ) →L[ℝ] (M →₂[μ] ℝ))
    (hB : ∀ u, ∃ ū : M → ℝ, MSmooth F ū ∧ (B u : M → ℝ) =ᵐ[μ] ū) (x₀ : M) {W : Set F}
    (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWT : closure W ⊆ (chartAt F x₀).target) :
    ∃ C : ℝ, ∀ (u : M →₂[μ] ℝ) (ū : M → ℝ), MSmooth F ū → (B u : M → ℝ) =ᵐ[μ] ū →
      ∀ z ∈ W, ‖gradient (ū ∘ (chartAt F x₀).symm) z‖ ≤ C * ‖u‖ := by
  classical
  have hB' := hB
  choose rep hrepS hrepE using hB
  have hrepC : ∀ u, Continuous (rep u) := fun u => (hrepS u).continuous
  set φ := chartAt F x₀ with hφ
  set Kc := closure W with hKc
  haveI : CompactSpace Kc := isCompact_iff_compactSpace.1 hWc
  have hT : IsOpen φ.target := φ.open_target
  have hcd : ∀ u, ContDiffOn ℝ ∞ (rep u ∘ φ.symm) φ.target :=
    fun u => contDiffOn_chartCoord F x₀ (hrepS u)
  have hdiff : ∀ u, ∀ z ∈ φ.target, DifferentiableAt ℝ (rep u ∘ φ.symm) z := fun u z hz =>
    ((hcd u).contDiffAt (hT.mem_nhds hz)).differentiableAt (by simp)
  have hfc : ∀ u, ContinuousOn (fun z => fderiv ℝ (rep u ∘ φ.symm) z) φ.target := fun u =>
    (hcd u).continuousOn_fderiv_of_isOpen hT (by exact_mod_cast le_top)
  have hadd : ∀ u v, rep (u + v) = rep u + rep v := fun u v => by
    refine continuous_eq_of_ae F hV hμ (hrepC _) ((hrepC u).add (hrepC v)) ?_
    have h1 := hrepE (u + v)
    have h2 := hrepE u
    have h3 := hrepE v
    rw [map_add] at h1
    filter_upwards [h1, h2, h3, Lp.coeFn_add (B u) (B v)] with z a b c d
    rw [← a, d, Pi.add_apply, b, c]
    rfl
  have hsmul : ∀ (c : ℝ) u, rep (c • u) = c • rep u := fun c u => by
    refine continuous_eq_of_ae F hV hμ (hrepC _) ((hrepC u).const_smul c) ?_
    have h1 := hrepE (c • u)
    have h2 := hrepE u
    rw [map_smul] at h1
    filter_upwards [h1, h2, Lp.coeFn_smul c (B u)] with z a b d
    rw [← a, d, Pi.smul_apply, b]
    rfl
  let Φ : (M →₂[μ] ℝ) →ₗ[ℝ] C(Kc, F) :=
    { toFun := fun u => ⟨fun y => gradient (rep u ∘ φ.symm) y.1,
        (((InnerProductSpace.toDual ℝ F).symm.continuous.comp_continuousOn (hfc u)).comp_continuous
          continuous_subtype_val (fun y => hWT y.2))⟩
      map_add' := fun u v => by
        ext y : 1
        have h : rep (u + v) ∘ φ.symm = rep u ∘ φ.symm + rep v ∘ φ.symm := by
          rw [hadd]; rfl
        have hy := hWT y.2
        show gradient (rep (u + v) ∘ φ.symm) y.1 =
          gradient (rep u ∘ φ.symm) y.1 + gradient (rep v ∘ φ.symm) y.1
        simp only [gradient]
        rw [h, fderiv_add (hdiff u _ hy) (hdiff v _ hy), map_add]
      map_smul' := fun c u => by
        ext y : 1
        have h : rep (c • u) ∘ φ.symm = c • (rep u ∘ φ.symm) := by
          rw [hsmul]; rfl
        have hy := hWT y.2
        show gradient (rep (c • u) ∘ φ.symm) y.1 =
          c • gradient (rep u ∘ φ.symm) y.1
        simp only [gradient]
        rw [h, fderiv_const_smul (hdiff u _ hy), map_smul] }
  have hK0 : IsCompact (φ.symm '' Kc) := hWc.image_of_continuousOn
    (φ.continuousOn_symm.mono hWT)
  obtain ⟨C0, hC0⟩ := local_bound_of_smooth_rep F hV hμ B hB' hK0
  have hΦ : Continuous Φ := by
    refine LinearMap.continuous_of_seq_closed_graph Φ (fun u x y hu hy => ?_)
    -- uniform convergence of the representatives on `φ.symm '' Kc`
    have hrt : ∀ z ∈ Kc, Tendsto (fun n => (rep (u n) ∘ φ.symm) z) atTop
        (𝓝 ((rep x ∘ φ.symm) z)) := by
      intro z hz
      have hb : ∀ n, |(rep (u n) ∘ φ.symm) z - (rep x ∘ φ.symm) z| ≤ C0 * ‖u n - x‖ := by
        intro n
        have := hC0 (u n - x) (rep (u n) - rep x) ((hrepC _).sub (hrepC _)) (by
          rw [map_sub]
          filter_upwards [Lp.coeFn_sub (B (u n)) (B x), hrepE (u n), hrepE x] with w a b c
          rw [a, Pi.sub_apply, b, c]; rfl) (φ.symm z) ⟨z, hz, rfl⟩
        simpa using this
      have h0 : Tendsto (fun n => C0 * ‖u n - x‖) atTop (𝓝 0) := by
        have := (tendsto_iff_norm_sub_tendsto_zero.1 hu).const_mul C0
        simpa using this
      rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun n => dist_nonneg) (fun n => by rw [Real.dist_eq]; exact hb n) h0
    set Y : F → F := fun z => if hz : z ∈ Kc then y ⟨z, hz⟩ else 0 with hYdef
    have hYc : ContinuousOn Y Kc := by
      rw [continuousOn_iff_continuous_domRestrict]
      have : Kc.domRestrict Y = y := by
        funext z; simp [hYdef, z.2]
      rw [this]; exact y.continuous
    have hWKc : W ⊆ Kc := subset_closure
    have hfd : ∀ f : F → ℝ, ∀ z, fderiv ℝ f z = InnerProductSpace.toDual ℝ F (gradient f z) := by
      intro f z; simp [gradient]
    have hunif : TendstoUniformlyOn (fun n z => fderiv ℝ (rep (u n) ∘ φ.symm) z)
        (fun z => InnerProductSpace.toDual ℝ F (Y z)) atTop W := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      have := Metric.tendsto_atTop.1 hy ε hε
      obtain ⟨N, hN⟩ := this
      filter_upwards [eventually_ge_atTop N] with n hn z hz
      have h1 := ContinuousMap.dist_apply_le_dist (f := y) (g := Φ (u n)) ⟨z, hWKc hz⟩
      have h2 := hN n hn
      rw [dist_comm] at h2
      have h3 : dist (InnerProductSpace.toDual ℝ F (Y z))
          (fderiv ℝ (rep (u n) ∘ φ.symm) z) ≤ dist y (Φ (u n)) := by
        rw [hfd, LinearIsometryEquiv.dist_map]
        simpa [hYdef, hWKc hz, Φ] using h1
      exact lt_of_le_of_lt h3 h2
    have hder : ∀ z ∈ W, HasFDerivAt (rep x ∘ φ.symm) (InnerProductSpace.toDual ℝ F (Y z)) z := fun z hz =>
      hasFDerivAt_of_tendstoUniformlyOn hW hunif
        (fun n z hz => (hdiff (u n) z (hWT (hWKc hz))).hasFDerivAt)
        (fun z hz => hrt z (hWKc hz)) hz
    have hgc : ContinuousOn (fun z => gradient (rep x ∘ φ.symm) z) φ.target :=
      (InnerProductSpace.toDual ℝ F).symm.continuous.comp_continuousOn (hfc x)
    have hEW : EqOn Y (fun z => gradient (rep x ∘ φ.symm) z) W := fun z hz => by
      have := (hder z hz).fderiv
      rw [hfd] at this
      exact ((InnerProductSpace.toDual ℝ F).injective this).symm
    have hEK : EqOn Y (fun z => gradient (rep x ∘ φ.symm) z) Kc :=
      hEW.of_subset_closure hYc (hgc.mono hWT) hWKc subset_rfl
    ext ⟨z, hz⟩ : 2
    have := hEK hz
    simpa [hYdef, hz, Φ] using this
  let Φc : (M →₂[μ] ℝ) →L[ℝ] C(Kc, F) := ⟨Φ, hΦ⟩
  refine ⟨‖Φc‖, fun u ū hūS hūe z hz => ?_⟩
  have hu : ū = rep u :=
    continuous_eq_of_ae F hV hμ hūS.continuous (hrepC u) (hūe.symm.trans (hrepE u))
  rw [hu]
  have := ContinuousMap.norm_coe_le_norm (Φc u) ⟨z, subset_closure hz⟩
  calc ‖gradient (rep u ∘ φ.symm) z‖ = ‖(Φc u) ⟨z, subset_closure hz⟩‖ := by simp [Φc, Φ]
    _ ≤ ‖Φc u‖ := this
    _ ≤ ‖Φc‖ * ‖u‖ := Φc.le_opNorm u

end Grad1

end CutoffRigidity.Riemann.Diff
