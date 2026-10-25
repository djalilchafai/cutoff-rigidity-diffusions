module

public import CutoffRigidity.Riemann.DiffRegSmooth
public import CutoffRigidity.Riemann.DiffEigen

/-! # Smooth representatives and local bounds (workstream KER, A5ii)

For a bounded operator `B` on `L²(μ)` all of whose values have a smooth (or continuous)
representative, the representative is unique (`μ` has full support), linear in the argument and
locally bounded by `C(K) ‖u‖` (closed graph theorem into `C(Kc, ℝ)`).
-/

@[expose] public section

open Bundle MeasureTheory Filter Set Topology
open scoped Manifold ContDiff ENNReal Topology NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Bound

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

/-- Continuous functions that agree `μ`-a.e. agree everywhere. -/
theorem continuous_eq_of_ae {f g : M → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : f =ᵐ[μ] g) : f = g := by
  have := isOpenPosMeasure_of_isWeightedVolume F hV hμ
  exact (hf.ae_eq_iff_eq μ hg).1 h

/-- A continuous function which is a.e. nonnegative is nonnegative. -/
theorem continuous_nonneg_of_ae {f : M → ℝ} (hf : Continuous f) (h : 0 ≤ᵐ[μ] f) :
    ∀ x, 0 ≤ f x := by
  have := isOpenPosMeasure_of_isWeightedVolume F hV hμ
  intro x
  by_contra hx
  rw [not_le] at hx
  have hU : IsOpen {y | f y < 0} := isOpen_lt hf continuous_const
  have hpos : 0 < μ {y | f y < 0} := hU.measure_pos μ ⟨x, hx⟩
  have h0 : μ {y | f y < 0} = 0 := by
    have : ∀ᵐ y ∂μ, ¬ (f y < 0) := by
      filter_upwards [h] with y hy
      exact not_lt.2 hy
    simpa using ae_iff.1 this
  exact hpos.ne' h0

/-- Local sup bound for operators with smooth values (closed graph theorem). -/
theorem local_bound_of_smooth_rep (B : (M →₂[μ] ℝ) →L[ℝ] (M →₂[μ] ℝ))
    (hB : ∀ u, ∃ ū : M → ℝ, MSmooth F ū ∧ (B u : M → ℝ) =ᵐ[μ] ū)
    {K : Set M} (hK : IsCompact K) :
    ∃ C : ℝ, ∀ (u : M →₂[μ] ℝ) (ū : M → ℝ), Continuous ū → (B u : M → ℝ) =ᵐ[μ] ū →
      ∀ x ∈ K, |ū x| ≤ C * ‖u‖ := by
  classical
  have hopen := isOpenPosMeasure_of_isWeightedVolume F hV hμ
  choose rep hrepS hrepE using hB
  have hrepC : ∀ u, Continuous (rep u) := fun u => (hrepS u).continuous
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace F M
  obtain ⟨K', hK'c, hKK'⟩ := exists_compact_superset hK
  set W := interior K' with hW
  have hWo : IsOpen W := isOpen_interior
  set Kc := closure W with hKc
  have hKcc : IsCompact Kc :=
    hK'c.of_isClosed_subset isClosed_closure
      (closure_minimal interior_subset hK'c.isClosed)
  haveI : CompactSpace Kc := isCompact_iff_compactSpace.1 hKcc
  -- the linear map into `C(Kc, ℝ)`
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
  let Φ : (M →₂[μ] ℝ) →ₗ[ℝ] C(Kc, ℝ) :=
    { toFun := fun u => ⟨fun y => rep u y.1, (hrepC u).comp continuous_subtype_val⟩
      map_add' := fun u v => by
        ext y; simp [hadd]
      map_smul' := fun c u => by
        ext y; simp [hsmul] }
  have hΦ : Continuous Φ := by
    refine LinearMap.continuous_of_seq_closed_graph Φ (fun u x y hu hy => ?_)
    have hLp : Tendsto (fun n => B (u n)) atTop (𝓝 (B x)) := (B.continuous.tendsto x).comp hu
    have hmeas : TendstoInMeasure μ (fun n => ((B (u n) : Lp ℝ 2 μ) : M → ℝ)) atTop
        (B x : M → ℝ) := by
      refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) ?_
      exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 hLp
    obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
    have hall : ∀ᵐ z ∂μ, ∀ n, (B (u n) : M → ℝ) z = rep (u n) z :=
      ae_all_iff.2 (fun n => hrepE (u n))
    have hxe := hrepE x
    have hEq : ∀ᵐ z ∂μ, ∀ hz : z ∈ Kc, y ⟨z, hz⟩ = rep x z := by
      filter_upwards [hae, hall, hxe] with z h1 h2 h3 hz
      have h4 : Tendsto (fun k => rep (u (ns k)) z) atTop (𝓝 (y ⟨z, hz⟩)) := by
        have := ((ContinuousMap.evalCLM ℝ (⟨z, hz⟩ : Kc)).continuous.tendsto y).comp
          ((hy.comp hns.tendsto_atTop))
        simpa [Function.comp_def, Φ] using this
      have h5 : Tendsto (fun k => rep (u (ns k)) z) atTop (𝓝 (rep x z)) := by
        have h1' : Tendsto (fun k => (B (u (ns k)) : M → ℝ) z) atTop (𝓝 ((B x : M → ℝ) z)) := h1
        simp only [h2] at h1'
        rwa [h3] at h1'
      exact tendsto_nhds_unique h4 h5
    set yt : M → ℝ := fun z => if hz : z ∈ Kc then y ⟨z, hz⟩ else 0 with hyt
    have hytc : ContinuousOn yt Kc := by
      rw [continuousOn_iff_continuous_domRestrict]
      have : Kc.domRestrict yt = y := by
        funext z; simp [hyt, z.2]
      rw [this]; exact y.continuous
    have hWKc : W ⊆ Kc := subset_closure
    have hae' : yt =ᵐ[μ.restrict W] rep x := by
      filter_upwards [ae_restrict_of_ae hEq, ae_restrict_mem hWo.measurableSet] with z h1 hz
      have := h1 (hWKc hz)
      simp [hyt, hWKc hz, this]
    have hEW := Measure.eqOn_open_of_ae_eq hae' hWo (hytc.mono hWKc) (hrepC x).continuousOn
    have hEK : EqOn yt (rep x) Kc :=
      hEW.of_subset_closure hytc (hrepC x).continuousOn hWKc subset_rfl
    ext ⟨z, hz⟩
    have := hEK hz
    simpa [hyt, hz, Φ] using this
  let Φc : (M →₂[μ] ℝ) →L[ℝ] C(Kc, ℝ) := ⟨Φ, hΦ⟩
  refine ⟨‖Φc‖, fun u ū hūc hūe x hx => ?_⟩
  have hKW : x ∈ W := hKK' hx
  have hu : ū = rep u := continuous_eq_of_ae F hV hμ hūc (hrepC u) (hūe.symm.trans (hrepE u))
  rw [hu]
  have := ContinuousMap.norm_coe_le_norm (Φc u) ⟨x, subset_closure hKW⟩
  calc |rep u x| = ‖(Φc u) ⟨x, subset_closure hKW⟩‖ := by simp [Φc, Φ]
    _ ≤ ‖Φc u‖ := this
    _ ≤ ‖Φc‖ * ‖u‖ := Φc.le_opNorm u

omit hV hμ

end Bound

end CutoffRigidity.Riemann.Diff
