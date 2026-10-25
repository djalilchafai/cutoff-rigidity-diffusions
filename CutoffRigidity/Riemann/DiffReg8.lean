module

public import CutoffRigidity.Riemann.DiffReg7

/-! # Interior sup estimate, part 4: local and global estimates (workstream KER-REG) -/

@[expose] public section

open Bundle MeasureTheory Filter Set Topology
open scoped ContDiff ENNReal Manifold

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Global

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

include hV hμ in
/-- Local sup estimate near a point `x ∈ W`. -/
theorem local_sup_bound {W : Set M} (hW : IsOpen W) (lam : ℝ) {x : M} (hx : x ∈ W) :
    ∃ (N : Set M) (D : ℝ), IsOpen N ∧ x ∈ N ∧ 0 ≤ D ∧
      ∀ w : M → ℝ, MSmooth F w → (∀ y ∈ W, mgenerator F V w y = lam * w y) →
        Integrable (fun y => w y ^ 2) (μ.restrict W) →
        ∀ y ∈ N, |w y| ≤ D * (∫ y in W, w y ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  classical
  set φ := chartAt F x with hφ
  set Ω : Set F := φ.target ∩ φ.symm ⁻¹' W with hΩdef
  have hΩ : IsOpen Ω := φ.continuousOn_symm.isOpen_inter_preimage φ.open_target hW
  have hxΩ : φ x ∈ Ω := ⟨mem_chart_target F x, by
    show φ.symm (φ x) ∈ W
    rw [φ.left_inv (mem_chart_source F x)]; exact hx⟩
  have hz' : ∀ z ∈ Ω, z ∈ (extChartAt 𝓘(ℝ, F) x).target := fun z hz => by
    rw [CutoffRigidity.extChartAt_target_eq]; exact hz.1
  obtain ⟨χ, hχ, ⟨V', hV', hKV, hV1⟩, -⟩ := exists_cutoff_nhds (isCompact_singleton (x := φ x))
    hΩ (singleton_subset_iff.2 hxΩ)
  obtain ⟨χ', C, hχ', hC0, hC⟩ := sup_estimate_Rn F hΩ
    ((contDiffOn_chartCoeff F x).mono inter_subset_left)
    ((contDiffOn_chartRho F hV x).mono inter_subset_left)
    (fun z hz v w => chartCoeff_symm F x (hz' z hz) v w)
    (fun z hz => exists_chartCoeff_elliptic F x (hz' z hz))
    (fun z hz => chartRho_pos F V x hz.1) lam hχ
  obtain ⟨c₁, hc₁, hcomp⟩ := chart_L2_compare F hV hμ x hW hχ'.1.continuous hχ'.2.1 hχ'.2.2
  have hNo : IsOpen (φ.source ∩ φ ⁻¹' V') :=
    φ.continuousOn.isOpen_inter_preimage φ.open_source hV'
  refine ⟨φ.source ∩ φ ⁻¹' V', Real.sqrt (C * c₁), hNo, ⟨mem_chart_source F x, hKV rfl⟩,
    Real.sqrt_nonneg _, fun w hw hgen hint y hy => ?_⟩
  set ũ : F → ℝ := fun z => w (φ.symm z) with hũdef
  have hũ : ContDiffOn ℝ ∞ ũ Ω := (contDiffOn_chartCoord F x hw).mono inter_subset_left
  have hweak : ∀ ψ : F → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      ∫ z in Ω, (inner ℝ (chartCoeff F x z (gradient ũ z)) (gradient ψ z) + lam * ũ z * ψ z) *
        chartRho F V x z = 0 := by
    intro ψ hψ hψc hψΩ
    have h0 := chart_eq_of_generator F hV hμ x hw hgen hψ hψc (hψΩ.trans inter_subset_left)
      (fun z hz => (hψΩ hz).2)
    have hvan : ∀ z, z ∉ tsupport ψ → (inner ℝ (chartCoeff F x z (gradient ũ z)) (gradient ψ z) +
        lam * ũ z * ψ z) * chartRho F V x z = 0 := by
      intro z hz
      have hev := notMem_tsupport_iff_eventuallyEq.1 hz
      have : fderiv ℝ ψ z = 0 := by rw [hev.fderiv_eq]; simp
      simp [gradient, this, image_eq_zero_of_notMem_tsupport hz]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => hvan z (fun h => hz (hψΩ h)))]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => hvan z (fun h => hz (hψΩ h |>.1))) ] at h0
    exact h0
  have hyS : y ∈ φ.source := hy.1
  have hsup := hC ũ hũ hweak (φ y) (hV1 _ hy.2)
  have hwy : ũ (φ y) = w y := by simp [hũdef, φ.left_inv hyS]
  rw [hwy] at hsup
  have hI := hcomp w hw.continuous hint
  have hle : w y ^ 2 ≤ C * c₁ * ∫ y in W, w y ^ 2 ∂μ := by
    calc w y ^ 2 ≤ C * ∫ z, (χ' z * ũ z) ^ 2 := hsup
      _ ≤ C * (c₁ * ∫ y in W, w y ^ 2 ∂μ) := mul_le_mul_of_nonneg_left hI hC0
      _ = _ := by ring
  have hJ0 : 0 ≤ ∫ y in W, w y ^ 2 ∂μ := setIntegral_nonneg hW.measurableSet fun y _ => sq_nonneg _
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul (mul_nonneg hC0 hc₁)]
  exact Real.abs_le_sqrt hle

end Global

end CutoffRigidity.Riemann.Diff
