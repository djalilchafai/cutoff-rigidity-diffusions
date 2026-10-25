module

public import CutoffRigidity.Riemann.DiffReg3

/-! # Regularity bootstrap, part 4: smoothness with a smooth potential (workstream KER-REG)

`Q_smooth_of_weak_eq_pot`: `u ∈ Q` with `E(u,φ) + λ⟪u,φ⟫ + ∫ κ u φ dμ = ⟪g,φ⟫` for all `φ ∈ Q`,
`κ` smooth and `g` a.e. smooth, has a smooth representative.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set Topology
open scoped ContDiff ENNReal Manifold

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Pot

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V) (x₀ : M) (T : DirFriedrichs (diffFormData F hV hμ))

include hV hμ in
/-- The potential term against a chart test function, as a chart integral. -/
theorem pot_chartTestFn (κ : M → ℝ) (hκ : Continuous κ) (u : M →₂[μ] ℝ) {ψ : F → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψT : tsupport ψ ⊆ (chartAt F x₀).target) :
    ∫ x, κ x * (u : M → ℝ) x * (testToL2 F μ (chartTestFn F x₀ hψ hψc hψT) : M → ℝ) x ∂μ =
      ∫ z in (chartAt F x₀).target, chartRho F V x₀ z *
        (κ ((chartAt F x₀).symm z) * (u : M → ℝ) ((chartAt F x₀).symm z) * ψ z) := by
  set φ := chartAt F x₀ with hφ
  set b := chartTestFn F x₀ hψ hψc hψT with hb
  have hTm : MeasurableSet φ.target := φ.open_target.measurableSet
  have hum : Measurable (u : M → ℝ) := (Lp.stronglyMeasurable u).measurable
  have e1 : ∫ x, κ x * (u : M → ℝ) x * (testToL2 F μ b : M → ℝ) x ∂μ =
      ∫ x, κ x * (u : M → ℝ) x * (b : M → ℝ) x ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_testToL2 F μ b] with x hx
    rw [hx]
  have hb0 : ∀ x, x ∉ φ.source → κ x * (u : M → ℝ) x * (b : M → ℝ) x = 0 := fun x hx => by
    rw [hb, coe_chartTestFn, chartExtend_eq_zero F x₀ hx, mul_zero]
  rw [e1, ← setIntegral_eq_integral_of_forall_compl_eq_zero hb0]
  have hG : AEStronglyMeasurable
      (fun z => κ (φ.symm z) * (u : M → ℝ) (φ.symm z) * ψ z) (volume.restrict φ.target) := by
    have h1 : AEMeasurable (fun z => (u : M → ℝ) (φ.symm z)) (volume.restrict φ.target) :=
      hum.comp_aemeasurable (φ.continuousOn_symm.aemeasurable hTm)
    have h2 : AEMeasurable (fun z => κ (φ.symm z)) (volume.restrict φ.target) :=
      hκ.measurable.comp_aemeasurable (φ.continuousOn_symm.aemeasurable hTm)
    exact (h2.mul h1).aestronglyMeasurable.mul hψ.continuous.aestronglyMeasurable
  rw [← integral_chart_comp F hV hμ x₀ _ hG]
  refine setIntegral_congr_fun φ.open_source.measurableSet fun x hx => ?_
  rw [hb, coe_chartTestFn, chartExtend_eq F x₀ hx, φ.left_inv hx]

include hV hμ in
/-- **Chart transfer of the weak equation with a potential.** -/
theorem chart_weak_equation_pot {u : M →₂[μ] ℝ} (hu : u ∈ T.Q) {lam : ℝ} (κ : M → ℝ)
    (hκ : MSmooth F κ) (g : M →₂[μ] ℝ)
    (g' : M → ℝ) (hg'm : Measurable g') (hgg' : (g : M → ℝ) =ᵐ[μ] g')
    (hweak : ∀ φ ∈ T.Q, T.E u φ + lam * inner ℝ u φ +
      ∫ x, κ x * (u : M → ℝ) x * (φ : M → ℝ) x ∂μ = inner ℝ g φ) :
    ∃ Du : F → F, IsChartWeakGrad F V x₀ (u : M → ℝ) Du ∧
      ∀ ψ : F → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ (chartAt F x₀).target →
        ∫ z in (chartAt F x₀).target,
            (inner ℝ (chartCoeff F x₀ z (Du z)) (gradient ψ z) +
              (lam + κ ((chartAt F x₀).symm z)) * (u : M → ℝ) ((chartAt F x₀).symm z) * ψ z) *
                chartRho F V x₀ z =
          ∫ z in (chartAt F x₀).target,
            g' ((chartAt F x₀).symm z) * ψ z * chartRho F V x₀ z := by
  obtain ⟨Du, hW, hE⟩ := Q_chart_weak F hV hμ x₀ T hu
  refine ⟨Du, hW, fun ψ hψ hψc hψT => ?_⟩
  set b := chartTestFn F x₀ hψ hψc hψT with hb
  have hbS := (chartExtend_mem F x₀ hψ hψc hψT).2
  have hTm : MeasurableSet (chartAt F x₀).target := (chartAt F x₀).open_target.measurableSet
  have hmem : (testToL2 F μ b : M →₂[μ] ℝ) ∈ T.Q := T.coe_mem ⟨testToL2 F μ b, b, rfl⟩
  have h1 := hweak _ hmem
  rw [hE b hbS, inner_lp_chartTestFn F hV hμ x₀ u (u : M → ℝ) (Lp.stronglyMeasurable u).measurable
      Filter.EventuallyEq.rfl hψ hψc hψT,
    inner_lp_chartTestFn F hV hμ x₀ g g' hg'm hgg' hψ hψc hψT,
    pot_chartTestFn F hV hμ x₀ κ hκ.continuous u hψ hψc hψT] at h1
  have e1 : ∫ z in (chartAt F x₀).target, chartRho F V x₀ z *
      inner ℝ (chartGrad F x₀ (b : M → ℝ) z) (chartCoeff F x₀ z (Du z)) =
      ∫ z in (chartAt F x₀).target, inner ℝ (chartCoeff F x₀ z (Du z)) (gradient ψ z) *
        chartRho F V x₀ z := by
    refine setIntegral_congr_fun hTm fun z hz => ?_
    rw [coe_chartTestFn, chartGrad_chartExtend F x₀ hz, real_inner_comm, mul_comm]
  have e2 : ∫ z in (chartAt F x₀).target, chartRho F V x₀ z *
      ((u : M → ℝ) ((chartAt F x₀).symm z) * ψ z) =
      ∫ z in (chartAt F x₀).target, (u : M → ℝ) ((chartAt F x₀).symm z) * ψ z * chartRho F V x₀ z := by
    refine setIntegral_congr_fun hTm fun z hz => ?_
    ring
  have e3 : ∫ z in (chartAt F x₀).target, chartRho F V x₀ z *
      (g' ((chartAt F x₀).symm z) * ψ z) =
      ∫ z in (chartAt F x₀).target, g' ((chartAt F x₀).symm z) * ψ z * chartRho F V x₀ z := by
    refine setIntegral_congr_fun hTm fun z hz => ?_
    ring
  have e4 : ∫ z in (chartAt F x₀).target, chartRho F V x₀ z *
      (κ ((chartAt F x₀).symm z) * (u : M → ℝ) ((chartAt F x₀).symm z) * ψ z) =
      ∫ z in (chartAt F x₀).target, (u : M → ℝ) ((chartAt F x₀).symm z) *
        (ψ z * κ ((chartAt F x₀).symm z)) * chartRho F V x₀ z := by
    refine setIntegral_congr_fun hTm fun z hz => ?_
    ring
  rw [e1, e2, e3, e4] at h1
  have hi1 := integrableOn_term1 F hV hμ x₀ hW.memLp_Du hψ hψc hψT
  have hi2 := (integrableOn_term2 F hV hμ x₀ hW.memLp_u hψ hψc hψT).const_mul lam
  have hκT : ContDiffOn ℝ ∞ (fun z => κ ((chartAt F x₀).symm z)) (chartAt F x₀).target :=
    contDiffOn_chartCoord F x₀ hκ
  have hi3 := integrableOn_term2 F hV hμ x₀ hW.memLp_u
    (contDiff_mul_of_contDiffOn (chartAt F x₀).open_target hψ hψT hκT) hψc.mul_right
    (tsupport_mul_subset_left.trans hψT)
  have : (fun z => (inner ℝ (chartCoeff F x₀ z (Du z)) (gradient ψ z) +
      (lam + κ ((chartAt F x₀).symm z)) * (u : M → ℝ) ((chartAt F x₀).symm z) * ψ z) *
        chartRho F V x₀ z) =
      fun z => (inner ℝ (chartCoeff F x₀ z (Du z)) (gradient ψ z) * chartRho F V x₀ z +
        lam * ((u : M → ℝ) ((chartAt F x₀).symm z) * ψ z * chartRho F V x₀ z)) +
        (u : M → ℝ) ((chartAt F x₀).symm z) *
          (ψ z * κ ((chartAt F x₀).symm z)) * chartRho F V x₀ z := by
    funext z; ring
  have hi12 : Integrable (fun z => inner ℝ (chartCoeff F x₀ z (Du z)) (gradient ψ z) *
      chartRho F V x₀ z + lam * ((u : M → ℝ) ((chartAt F x₀).symm z) * ψ z *
        chartRho F V x₀ z)) (volume.restrict (chartAt F x₀).target) := hi1.add hi2
  rw [this, integral_add hi12 hi3, integral_add hi1 hi2, integral_const_mul]
  linarith

include hV hμ in
/-- `H^m_loc` regularity of a solution with a smooth potential and a smooth right-hand side. -/
theorem chartLocSob_pot {u : M →₂[μ] ℝ} (hu : u ∈ T.Q) {lam : ℝ} (κ : M → ℝ)
    (hκ : MSmooth F κ) (g : M →₂[μ] ℝ) (g' : M → ℝ) (hg's : MSmooth F g')
    (hgg' : (g : M → ℝ) =ᵐ[μ] g')
    (hweak : ∀ φ ∈ T.Q, T.E u φ + lam * inner ℝ u φ +
      ∫ x, κ x * (u : M → ℝ) x * (φ : M → ℝ) x ∂μ = inner ℝ g φ) (m : ℕ) :
    ChartLocSob F m (u : M → ℝ) := by
  intro x₀
  obtain ⟨Du, hW, hE⟩ := chart_weak_equation_pot F hV hμ x₀ T hu κ hκ g g'
    hg's.continuous.measurable hgg' hweak
  have hwg : IsWeakGradOn F (chartAt F x₀).target (fun z => (u : M → ℝ) ((chartAt F x₀).symm z)) Du :=
    ⟨fun K hK hKT => memLp_restrict_of_nu F hV x₀ hK hKT hW.memLp_u,
     fun K hK hKT => memLp_restrict_of_nu F hV x₀ hK hKT hW.memLp_Du, hW.weak⟩
  have hz' : ∀ z ∈ (chartAt F x₀).target, z ∈ (extChartAt 𝓘(ℝ, F) x₀).target := fun z hz => by
    rw [CutoffRigidity.extChartAt_target_eq]; exact hz
  have hgs : ContDiffOn ℝ ∞ (fun z => g' ((chartAt F x₀).symm z)) (chartAt F x₀).target :=
    contDiffOn_chartCoord F x₀ hg's
  have hκT : ContDiffOn ℝ ∞ (fun z => κ ((chartAt F x₀).symm z)) (chartAt F x₀).target :=
    contDiffOn_chartCoord F x₀ hκ
  have hgall : ∀ k, LocSob (stdOrthonormalBasis ℝ F) (chartAt F x₀).target k
      (fun z => g' ((chartAt F x₀).symm z)) := by
    intro k χ hχ
    exact (Sob.of_smooth _ k (contDiff_mul_of_contDiffOn (chartAt F x₀).open_target hχ.1 hχ.2.2 hgs)
      hχ.2.1.mul_right).1
  have hstep := regularity_step_Rn_pot F (chartAt F x₀).open_target (contDiffOn_const.add hκT) (contDiffOn_chartCoeff F x₀)
    (contDiffOn_chartRho F hV x₀)
    (fun z hz v w => chartCoeff_symm F x₀ (hz' z hz) v w)
    (fun z hz => exists_chartCoeff_elliptic F x₀ (hz' z hz))
    (fun z hz => chartRho_pos F V x₀ hz) (locL2_of_continuousOn hgs.continuousOn) hwg
    (fun ψ hψ hψc hψT => hE ψ hψ hψc hψT) m (hgall m)
  exact (hstep.mono _ (by omega)) 

include hV hμ in
/-- **Smoothness of the solution of the weak equation with a smooth potential.** -/
theorem Q_smooth_of_weak_eq_pot_gen {u : M →₂[μ] ℝ} (hu : u ∈ T.Q) {lam : ℝ} (κ : M → ℝ)
    (hκ : MSmooth F κ) (g : M →₂[μ] ℝ) (g' : M → ℝ) (hg's : MSmooth F g')
    (hgg' : (g : M → ℝ) =ᵐ[μ] g')
    (hweak : ∀ φ ∈ T.Q, T.E u φ + lam * inner ℝ u φ +
      ∫ x, κ x * (u : M → ℝ) x * (φ : M → ℝ) x ∂μ = inner ℝ g φ) :
    ∃ ū : M → ℝ, MSmooth F ū ∧ (u : M → ℝ) =ᵐ[μ] ū :=
  exists_smooth_of_chartLocSob F hV hμ u
    (chartLocSob_pot F hV hμ T hu κ hκ g g' hg's hgg' hweak)

end Pot

section PotFinal

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

/-- **`Q_smooth_of_weak_eq_pot`**. -/
theorem Q_smooth_of_weak_eq_pot {κ : M → ℝ} (hκ : MSmooth F κ) (g : M →₂[μ] ℝ) (g' : M → ℝ)
    (hg' : MSmooth F g') (hgg' : (g : M → ℝ) =ᵐ[μ] g') {u : M →₂[μ] ℝ}
    (hu : u ∈ (diffT F hV hμ).Q) (lam : ℝ)
    (hweak : ∀ φ ∈ (diffT F hV hμ).Q, (diffT F hV hμ).E u φ + lam * inner ℝ u φ +
      ∫ x, κ x * (u : M → ℝ) x * (φ : M → ℝ) x ∂μ = inner ℝ g φ) :
    ∃ ū : M → ℝ, MSmooth F ū ∧ (u : M → ℝ) =ᵐ[μ] ū :=
  Q_smooth_of_weak_eq_pot_gen F hV hμ (diffT F hV hμ) hu κ hκ g g' hg' hgg' hweak

/-- Bounded smooth potential version (a special case). -/
theorem Q_smooth_of_weak_eq_pot_bdd {κ : M → ℝ} (hκ : MSmooth F κ) (_hb : ∃ C, ∀ x, |κ x| ≤ C)
    (g : M →₂[μ] ℝ) (g' : M → ℝ)
    (hg' : MSmooth F g') (hgg' : (g : M → ℝ) =ᵐ[μ] g') {u : M →₂[μ] ℝ}
    (hu : u ∈ (diffT F hV hμ).Q) (lam : ℝ)
    (hweak : ∀ φ ∈ (diffT F hV hμ).Q, (diffT F hV hμ).E u φ + lam * inner ℝ u φ +
      ∫ x, κ x * (u : M → ℝ) x * (φ : M → ℝ) x ∂μ = inner ℝ g φ) :
    ∃ ū : M → ℝ, MSmooth F ū ∧ (u : M → ℝ) =ᵐ[μ] ū :=
  Q_smooth_of_weak_eq_pot F hV hμ hκ g g' hg' hgg' hu lam hweak

end PotFinal

end CutoffRigidity.Riemann.Diff
