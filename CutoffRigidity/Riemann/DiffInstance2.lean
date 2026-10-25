module

public import CutoffRigidity.Riemann.DiffInstance
public import CutoffRigidity.Riemann.DiffEllipticRn12

/-! # `EllipticRegularityRn` from the elliptic regularity theory of REGn (workstream DIR)

The hypothesis `EllipticRegularityRn F` of `Q_smooth_of_weak_eq` is a consequence of REGn's
`weak_solution_smooth` (coefficients `A i j x = ⟪a x (b j), b i⟫` in the standard orthonormal basis).
Hence `diff_resolvent_smooth'` is unconditional.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set Topology
open scoped ContDiff ENNReal Manifold

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

section Bridge

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem locallyIntegrableOn_of_locL2 {Ω : Set F} (hΩ : IsOpen Ω) {f : F → ℝ}
    (h : ∀ K : Set F, IsCompact K → K ⊆ Ω → MemLp f 2 (volume.restrict K)) :
    LocallyIntegrableOn f Ω := by
  intro x hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩ x hx
  have hK : IsCompact (Metric.closedBall x (r / 2)) := isCompact_closedBall _ _
  have hKΩ : Metric.closedBall x (r / 2) ⊆ Ω :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  refine ⟨Metric.closedBall x (r / 2), mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds _ (by linarith)), ?_⟩
  haveI : IsFiniteMeasure (volume.restrict (Metric.closedBall x (r / 2))) :=
    ⟨by simpa using hK.measure_lt_top⟩
  exact (h _ hK hKΩ).integrable one_le_two

theorem inner_expand {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ F) (L : F →L[ℝ] F) (w v : F) :
    inner ℝ (L w) v = ∑ i, ∑ j, inner ℝ (L (b j)) (b i) * inner ℝ w (b j) * inner ℝ v (b i) := by
  have hw : w = ∑ j, inner ℝ (b j) w • b j := (b.sum_repr' w).symm
  have hv : v = ∑ i, inner ℝ (b i) v • b i := (b.sum_repr' v).symm
  conv_lhs => rw [hw, hv]
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    conj_trivial]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_comm (b j) w, real_inner_comm (b i) v]
  ring

/-- **`EllipticRegularityRn F` holds**, by REGn's `weak_solution_smooth`. -/
theorem ellipticRegularityRn : EllipticRegularityRn F := by
  classical
  intro Ω hΩ a ϱ lam ha hϱ hsym hell hpos u g Du hg hwg hweak
  set b := stdOrthonormalBasis ℝ F with hb
  set A : Fin (Module.finrank ℝ F) → Fin (Module.finrank ℝ F) → F → ℝ :=
    fun i j x => inner ℝ (a x (b j)) (b i) with hA
  set u' : Fin (Module.finrank ℝ F) → F → ℝ := fun j x => inner ℝ (Du x) (b j) with hu'
  have hAs : ∀ i j, ContDiffOn ℝ ∞ (A i j) Ω := fun i j =>
    (ha.clm_apply contDiffOn_const).inner ℝ contDiffOn_const
  have hAsym : ∀ i j, ∀ x ∈ Ω, A i j x = A j i x := by
    intro i j x hx
    simp only [hA]
    rw [hsym x hx (b j) (b i), real_inner_comm]
  have hAell : ∀ x ∈ Ω, ∃ c > 0, ∀ ξ : Fin (Module.finrank ℝ F) → ℝ,
      c * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, A i j x * ξ j * ξ i := by
    intro x hx
    obtain ⟨c, hc, hcv⟩ := hell x hx
    refine ⟨c, hc, fun ξ => ?_⟩
    set v : F := ∑ j, ξ j • b j with hv
    have hbv : ∀ i, inner ℝ (b i) v = ξ i := by
      intro i
      rw [hv, inner_sum]
      simp [inner_smul_right, orthonormal_iff_ite.mp b.orthonormal]
    have h1 : ‖v‖ ^ 2 = ∑ i, ξ i ^ 2 := by
      rw [← b.sum_sq_norm_inner_right v]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hbv i, Real.norm_eq_abs, sq_abs]
    have h2 : inner ℝ (a x v) v = ∑ i, ∑ j, A i j x * ξ j * ξ i := by
      have e1 : a x v = ∑ j, ξ j • a x (b j) := by
        rw [hv, map_sum]; simp [map_smul]
      rw [e1, sum_inner, Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hv, inner_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [inner_smul_left, inner_smul_right, hA, conj_trivial]
      ring
    rw [← h1, ← h2]
    exact hcv v
  -- local `H¹`
  have hl2' : ∀ j, ∀ K : Set F, IsCompact K → K ⊆ Ω → MemLp (u' j) 2 (volume.restrict K) := by
    intro j K hK hKΩ
    refine (hwg.memLp_Du K hK hKΩ).mono ?_ ?_
    · exact ((hwg.memLp_Du K hK hKΩ).aestronglyMeasurable.inner aestronglyMeasurable_const)
    · refine Filter.Eventually.of_forall fun x => ?_
      simp only [hu']
      calc ‖inner ℝ (Du x) (b j)‖ ≤ ‖Du x‖ * ‖b j‖ := norm_inner_le_norm _ _
        _ = ‖Du x‖ := by simp
  have hH1 : LocH1 b Ω u u' :=
    ⟨hwg.memLp_u, hl2', fun j =>
      ⟨locallyIntegrableOn_of_locL2 F hΩ hwg.memLp_u, locallyIntegrableOn_of_locL2 F hΩ (hl2' j),
        fun φ hφ => by simpa [pd, hu'] using hwg.weak φ hφ.1 hφ.2.1 hφ.2.2 (b j)⟩⟩
  refine weak_solution_smooth b hΩ (A := A) hAs hAsym hAell hϱ hpos lam hg hH1 ?_
  intro φ hφ
  have hψij : ∀ i j, IsTest Ω (fun x => pd (b i) φ x * (A i j x * ϱ x)) := by
    intro i j
    have h0 := hφ.pd (b i)
    exact ⟨contDiff_mul_of_contDiffOn hΩ h0.1 h0.2.2 ((hAs i j).mul hϱ), h0.2.1.mul_right,
      tsupport_mul_subset_left.trans h0.2.2⟩
  have hint : ∀ i j, Integrable (fun x => A i j x * u' j x * pd (b i) φ x * ϱ x) volume := by
    intro i j
    have := integrable_mul_test_loc (hl2' j) (hψij i j) hΩ
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    ring
  have hint2 : Integrable (fun x => u x * φ x * ϱ x) volume := by
    have hψ : IsTest Ω (fun x => φ x * ϱ x) :=
      ⟨contDiff_mul_of_contDiffOn hΩ hφ.1 hφ.2.2 hϱ, hφ.2.1.mul_right,
        tsupport_mul_subset_left.trans hφ.2.2⟩
    refine (integrable_mul_test_loc hwg.memLp_u hψ hΩ).congr (Filter.Eventually.of_forall fun x => ?_)
    ring
  -- pointwise identity
  have hpt : ∀ x, (inner ℝ (a x (Du x)) (gradient φ x) + lam * u x * φ x) * ϱ x =
      (∑ i, ∑ j, A i j x * u' j x * pd (b i) φ x * ϱ x) + lam * (u x * φ x * ϱ x) := by
    intro x
    have h1 := inner_expand F b (a x) (Du x) (gradient φ x)
    have h2 : ∀ i, inner ℝ (gradient φ x) (b i) = pd (b i) φ x := by
      intro i
      simp only [pd, gradient, InnerProductSpace.toDual_symm_apply]
    simp only [h2] at h1
    rw [add_mul, h1, Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
    · ring
  have hΩ0 : ∀ x, x ∉ Ω → (inner ℝ (a x (Du x)) (gradient φ x) + lam * u x * φ x) * ϱ x = 0 := by
    intro x hx
    have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hφ.2.2 h))
    have hev := notMem_tsupport_iff_eventuallyEq.1 (fun h => hx (hφ.2.2 h))
    have : fderiv ℝ φ x = 0 := by rw [hev.fderiv_eq]; simp
    simp [gradient, this, hφx]
  have hΩ1 : ∀ x, x ∉ Ω → g x * φ x * ϱ x = 0 := by
    intro x hx
    have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hφ.2.2 h))
    simp [hφx]
  have h := hweak φ hφ.1 hφ.2.1 hφ.2.2
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hΩ0,
    setIntegral_eq_integral_of_forall_compl_eq_zero hΩ1] at h
  rw [← h]
  simp only [hpt]
  rw [integral_add (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j)
    (hint2.const_mul lam), integral_const_mul, integral_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => hint i j]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint i j]

end Bridge

section Final

open CutCur

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

/-- **Smoothness of the Friedrichs resolvent on smooth functions** (unconditional). -/
theorem diff_resolvent_smooth' {lam : ℝ} (hlam : 0 < lam)
    (g : M →₂[μ] ℝ) (g' : M → ℝ) (hg' : MSmooth F g') (hgg' : (g : M → ℝ) =ᵐ[μ] g') :
    ∃ ū : M → ℝ, MSmooth F ū ∧ ((diffFR F hV hμ).resolvent lam g : M → ℝ) =ᵐ[μ] ū :=
  diff_resolvent_smooth F hV hμ (ellipticRegularityRn F) hlam g g' hg' hgg'

/-- **Smoothness of weak eigenfunctions**: `u ∈ Q` with `E(u,φ) = c ⟪u,φ⟫` for all `φ ∈ Q` has a
smooth representative. -/
theorem diff_eigen_smooth {c : ℝ} {u : M →₂[μ] ℝ} (hu : u ∈ (diffT F hV hμ).Q)
    (h : ∀ φ ∈ (diffT F hV hμ).Q, (diffT F hV hμ).E u φ = c * inner ℝ u φ) :
    ∃ ū : M → ℝ, MSmooth F ū ∧ (u : M → ℝ) =ᵐ[μ] ū :=
  Q_smooth_of_weak_eq F hV hμ (diffT F hV hμ) (ellipticRegularityRn F) hu (lam := -c)
    (0 : M →₂[μ] ℝ) (fun _ => 0) contMDiff_const (Lp.coeFn_zero ℝ 2 μ) (fun φ hφ => by
      rw [h φ hφ]; simp)

end Final

end CutoffRigidity.Riemann.Diff
