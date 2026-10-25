module

public import CutoffRigidity.Riemann.DiffKuwPre
public import CutoffRigidity.Riemann.WeightedLocalSmooth
public import CutoffRigidity.Riemann.WeightedSmoothing
public import CutoffRigidity.Riemann.WeightedGradHelpers
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # Sharp local smoothing of a function that is `c`-Lipschitz on an open set -/

@[expose] public section

open Bundle MeasureTheory Filter Set Manifold
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section SharpLocal

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M]

include F

/-- Sharp local smoothing: if `f` is continuous and `c`-Lipschitz on an open `S ∋ p`, then for
`r > 1` there is an open `V ∋ p`, `V ⊆ S` in a compact set, on which `f` is approximated within
any `δ` by a function smooth near `V` with differential of norm at most `r² c`. -/
theorem sharp_local_smooth (hfin : ∀ x y : M, edist x y ≠ ⊤) {f : M → ℝ} (hfc : Continuous f)
    {S : Set M} (hSo : IsOpen S) {c : ℝ} (hc : 0 ≤ c) {r : ℝ} (hr : 1 < r)
    (hS : ∀ w ∈ S, ∀ w' ∈ S, |f w - f w'| ≤ c * dd w w') (p : M) (hp : p ∈ S) :
    ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ V ⊆ S ∧ (∃ K, IsCompact K ∧ V ⊆ K) ∧ ∀ δ > 0, ∃ g : M → ℝ,
      (∀ x ∈ V, ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ g x) ∧ (∀ x ∈ V, |g x - f x| ≤ δ) ∧
      ∀ x ∈ V, ∀ v : TangentSpace 𝓘(ℝ, F) x, |mvfderiv 𝓘(ℝ, F) g x v| ≤ r ^ 2 * c * ‖v‖ := by
  set e := extChartAt 𝓘(ℝ, F) p with he
  have hgoodev := eventually_symmAt_norm F p (r := r) hr
  have hc' : ContinuousAt e.symm (e p) := continuousAt_extChartAt_symm p
  have hsy : e.symm (e p) = p := e.left_inv (mem_extChartAt_source p)
  have hpre : e.symm ⁻¹' ({y | y ∈ (chartAt F p).source ∧
      (∀ w, ‖symmAt F p y w‖ ≤ r * ‖symmAt F p p w‖) ∧
      (∀ w, ‖symmAt F p p w‖ ≤ r * ‖symmAt F p y w‖)} ∩ S) ∈ 𝓝 (e p) :=
    hc'.preimage_mem_nhds (by rw [hsy]; exact inter_mem hgoodev (hSo.mem_nhds hp))
  obtain ⟨R₁, hR₁, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem (extChartAt_target_mem_nhds p) hpre)
  have hRt : Metric.ball (e p) R₁ ⊆ e.target := fun z hz => (hball hz).1
  have hgoodb : ∀ ζ ∈ Metric.ball (e p) R₁, e.symm ζ ∈ (chartAt F p).source ∧
      (∀ w, ‖symmAt F p (e.symm ζ) w‖ ≤ r * ‖symmAt F p p w‖) ∧
      (∀ w, ‖symmAt F p p w‖ ≤ r * ‖symmAt F p (e.symm ζ) w‖) :=
    fun ζ hζ => (hball hζ).2.1
  have hSb : ∀ ζ ∈ Metric.ball (e p) R₁, e.symm ζ ∈ S := fun ζ hζ => (hball hζ).2.2
  set R := R₁ / 2 with hRdef
  have hR : 0 < R := by positivity
  have hRR : Metric.ball (e p) R ⊆ Metric.ball (e p) R₁ := Metric.ball_subset_ball (by linarith)
  have hcb : Metric.closedBall (e p) R ⊆ Metric.ball (e p) R₁ :=
    Metric.closedBall_subset_ball (by linarith)
  set u : F → ℝ := fun ζ => f (e.symm ζ) with hu
  have hucont : ContinuousOn u e.target :=
    hfc.comp_continuousOn (continuousOn_extChartAt_symm p)
  have huint : IntegrableOn u (Metric.ball (e p) R) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall (e p) R)
      ((hucont.mono (hcb.trans hRt)))).mono_set Metric.ball_subset_closedBall
  set N : F → ℝ := fun w => r * c * ‖symmAt F p p w‖ with hN
  have hr0 : 0 < r := by linarith
  have hLip : ∀ b ∈ Metric.ball (e p) R, ∀ (w : F) (h : ℝ), b + h • w ∈ Metric.ball (e p) R →
      |u (b + h • w) - u b| ≤ |h| * N w := by
    intro b hb w h hbh
    have hed := edist_extChartAt_symm_le F p (r := r) (R := R₁) hr0.le hRt
      (fun ζ hζ => (hgoodb ζ hζ).2.1) (hRR hb) (hRR hbh)
    have h1 : |f (e.symm (b + h • w)) - f (e.symm b)| ≤
        c * dd (e.symm (b + h • w)) (e.symm b) :=
      hS _ (hSb _ (hRR hbh)) _ (hSb _ (hRR hb))
    rw [dd_comm] at h1
    have h2 : dd (e.symm b) (e.symm (b + h • w)) ≤ r * ‖symmAt F p p (b + h • w - b)‖ := by
      have := (ENNReal.toReal_mono ENNReal.ofReal_ne_top hed)
      rw [ENNReal.toReal_ofReal (by positivity)] at this
      exact this
    have h3 : b + h • w - b = h • w := by abel
    rw [h3, map_smul, norm_smul, Real.norm_eq_abs] at h2
    calc |u (b + h • w) - u b| ≤ _ := h1
      _ ≤ c * (r * (|h| * ‖symmAt F p p w‖)) := mul_le_mul_of_nonneg_left h2 hc
      _ = |h| * N w := by simp only [hN]; ring
  have hN0 : ∀ w, 0 ≤ N w := fun w => by positivity
  have hNC : ∀ w, N w ≤ (r * c * ‖symmAt F p p‖) * ‖w‖ := fun w => by
    simp only [hN]
    calc r * c * ‖symmAt F p p w‖ ≤ r * c * (‖symmAt F p p‖ * ‖w‖) :=
          mul_le_mul_of_nonneg_left ((symmAt F p p).le_opNorm w) (by positivity)
      _ = _ := by ring
  refine ⟨((chartAt F p).source ∩ e ⁻¹' Metric.ball (e p) (R / 2)),
    isOpen_extChartAt_preimage p Metric.isOpen_ball,
    ⟨mem_chart_source F p, by simpa using half_pos hR⟩, ?_,
    ⟨e.symm '' Metric.closedBall (e p) (R / 2),
      (isCompact_closedBall (e p) (R / 2)).image_of_continuousOn
        ((continuousOn_extChartAt_symm p).mono ?_), ?_⟩, ?_⟩
  · intro x hx
    have hxs : x ∈ e.source := by rw [he, extChartAt_source]; exact hx.1
    have : e x ∈ Metric.ball (e p) R₁ :=
      hRR (Metric.ball_subset_ball (by linarith) hx.2)
    simpa [e.left_inv hxs] using hSb _ this
  · exact (Metric.closedBall_subset_closedBall (by linarith)).trans (hcb.trans hRt)
  · intro x hx
    have hxs : x ∈ e.source := by rw [he, extChartAt_source]; exact hx.1
    exact ⟨e x, Metric.ball_subset_closedBall hx.2, e.left_inv hxs⟩
  · intro δ hδ
    obtain ⟨G, hG, hGp⟩ := exists_contDiff_approx_lip u (e p) hR huint N
      (r * c * ‖symmAt F p p‖) (by positivity) hN0 hNC hLip hδ
    refine ⟨G ∘ e, ?_, ?_, ?_⟩
    · intro x hx
      exact (hG.contMDiff.contMDiffAt).comp x (contMDiffAt_extChartAt' (by simpa using hx.1))
    · intro x hx
      have hxs : x ∈ e.source := by rw [he, extChartAt_source]; exact hx.1
      have := (hGp (e x) hx.2).1
      simpa [hu, e.left_inv hxs] using this
    · intro x hx
      have hxs : x ∈ e.source := by rw [he, extChartAt_source]; exact hx.1
      have hxsrc : x ∈ (chartAt F p).source := hx.1
      have hGd : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) G (e x) :=
        (hG.contMDiff.mdifferentiable (by simp)) _
      have hed : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F) e x := mdifferentiableAt_extChartAt hxsrc
      set T := trivializationAt F (fun x : M => TangentSpace 𝓘(ℝ, F) x) p with hT
      have hcl : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) e x = T.continuousLinearMapAt ℝ x :=
        (TangentBundle.continuousLinearMapAt_trivializationAt hxsrc).symm
      have hxb : x ∈ T.baseSet := by simpa [hT] using hxsrc
      intro v
      have hv0 : mvfderiv 𝓘(ℝ, F) (G ∘ e) x v =
          fderiv ℝ G (e x) (T.continuousLinearMapAt ℝ x v) := by
        rw [mvfderiv_comp_apply x hGd hed v, hcl, mvfderiv_eq_fderiv]
        rfl
      rw [hv0]
      set w := T.continuousLinearMapAt ℝ x v with hw
      have h1 := (hGp (e x) hx.2).2 w
      have hgood := (hgoodb (e x) (hRR (Metric.ball_subset_ball (by linarith) hx.2))).2.2 w
      rw [e.left_inv hxs] at hgood
      have hv : symmAt F p x w = v := Trivialization.symmL_continuousLinearMapAt T hxb v
      rw [hv] at hgood
      calc |fderiv ℝ G (e x) w| ≤ N w := h1
        _ = r * c * ‖symmAt F p p w‖ := rfl
        _ ≤ r * c * (r * ‖v‖) := by gcongr
        _ = r ^ 2 * c * ‖v‖ := by ring

end SharpLocal

end CutoffRigidity.Riemann.Diff
