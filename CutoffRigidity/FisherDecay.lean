module
public import CutoffRigidity.FisherLowerSemicontinuity
public import CutoffRigidity.L2SquareDensity
public import CutoffRigidity.RegularizedSquareFisher
public import CutoffRigidity.LangevinL1Density

/-! # Genuine full-domain Fisher decay for actual Langevin transitions

Actual compact graph approximants generate normalized positive square
probability densities. Actual L¹ kernel contraction and the Hellinger
inequality transfer them to strong evolved RN-root L² limits. The proved
closed-gradient lower semicontinuity then extends the source core decay.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped Topology ENNReal NNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem integral_density_eq_one_of_probability
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ}
    (hf : Integrable f μ) (hn : ∀ x, 0 ≤ f x)
    (hν : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x)))) :
    ∫ x, f x ∂μ = 1 := by
  let := hν
  have hh : ENNReal.ofReal (∫ x, f x ∂μ) = 1 := by
    rw [ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall hn)]
    have hm := measure_univ (μ := μ.withDensity (fun x => ENNReal.ofReal (f x)))
    simpa only [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] using hm
  have ht := congrArg ENNReal.toReal hh
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hn), ENNReal.toReal_one] using ht

/-- The paper's Fisher exponential decay for every actual initial
probability law, with the canonical extended closed-gradient functional.
Finite-domain approximation and its convergence are constructed, while
infinite initial information is treated explicitly. -/
theorem relativeFisherInformation_langevinKernel_le
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] (t : ℝ≥0) :
    letI := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
    relativeFisherInformation hV hp (langevinKernel V B P t ∘ₘ ν) ≤
      ENNReal.ofReal (Real.exp (-2 * ρ * t)) * relativeFisherInformation hV hp ν := by
  let := hp
  let μ := gibbsMeasure volume V
  let K := langevinKernel V B P t
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
  let G := closedGibbsGradient hV hp
  let R := squareRootRNDensityLp ν μ
  have hExp : ENNReal.ofReal (Real.exp (-2 * ρ * t)) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  by_cases hAC : ν ≪ μ
  · by_cases hD : R ∈ G.domain
    · let D := G ⟨R, hD⟩
      have hRnorm : ‖R‖ ^ 2 = 1 := by
        rw [← real_inner_self_eq_norm_sq, L2.inner_def]
        calc
          _ = ∫ x, squareRootRNDensity ν μ x ^ 2 ∂μ := by
            apply integral_congr_ae
            filter_upwards [(squareRootRNDensity_memLp ν μ).coeFn_toLp] with x hx
            have hx' : (R : E → ℝ) x = squareRootRNDensity ν μ x := by convert! hx using 1
            rw [hx', Real.inner_apply]
            ring
          _ = ν.real Set.univ := integral_squareRootRNDensity_sq ν μ hAC
          _ = 1 := by simp
      have hmem : (R, D) ∈ closure ((compactGibbsGradient hV.continuous hp).graph : Set _) := by
        change (R, D) ∈ (compactGibbsGradient hV.continuous hp).graph.topologicalClosure
        rw [(compactGibbsGradient_isClosable hV hp).graph_closure_eq_closure_graph]
        exact G.mem_graph ⟨R, hD⟩
      obtain ⟨p, hpseq, hplim⟩ := mem_closure_iff_seq_limit.mp hmem
      have hfirst : Tendsto (fun n => (p n).1) atTop (𝓝 R) := (continuous_fst.tendsto _).comp hplim
      have hsecond : Tendsto (fun n => (p n).2) atTop (𝓝 D) := (continuous_snd.tendsto _).comp hplim
      choose v hv1 hv2 using (fun n => (compactGibbsGradient hV.continuous hp).mem_graph_iff.mp (hpseq n))
      let f := fun n => compactGibbsRepresentative V (v n)
      have hf (n : ℕ) : ContDiff ℝ 2 (f n) := (compactGibbsRepresentative_spec V (v n)).1
      have hfc (n : ℕ) : HasCompactSupport (f n) := (compactGibbsRepresentative_spec V (v n)).2.1
      have hfrep (n : ℕ) : (p n).1 =ᵐ[μ] f n := by
        rw [← hv1 n]
        exact (compactGibbsRepresentative_spec V (v n)).2.2.symm
      have hgrep (n : ℕ) : (p n).2 =ᵐ[μ] gradient (f n) := by
        rw [← hv2 n]
        exact (compactGibbsGradient_memLp hp (v n)).coeFn_toLp
      have hA (n : ℕ) : (∫ x, f n x ^ 2 ∂μ) = ‖(p n).1‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hfrep n] with x hx
        rw [hx, Real.inner_apply]
        ring
      have hE (n : ℕ) : (∫ x, ‖gradient (f n) x‖ ^ 2 ∂μ) = ‖(p n).2‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hgrep n] with x hx
        rw [hx, real_inner_self_eq_norm_sq]
      let ε := fun n : ℕ => differenceStep n
      let den := fun n => ‖(p n).1‖ ^ 2 + ε n
      let c := fun n => ε n / den n
      let g := fun n x => f n x ^ 2 / den n
      let r := fun n x => c n + g n x
      let νn := fun n => μ.withDensity (fun x => ENNReal.ofReal (r n x))
      let bn := fun n => (4 / den n) * ‖(p n).2‖ ^ 2
      have hε (n : ℕ) : 0 < ε n := differenceStep_pos n
      have hεlim : Tendsto ε atTop (𝓝 0) := differenceStep_tendsto_zero
      have hden (n : ℕ) : 0 < den n := add_pos_of_nonneg_of_pos (sq_nonneg _) (hε n)
      have hc (n : ℕ) : 0 < c n := div_pos (hε n) (hden n)
      have hg (n : ℕ) : ContDiff ℝ 2 (g n) := ((hf n).pow 2).div_const _
      have hgc (n : ℕ) : HasCompactSupport (g n) :=
        (hfc n).comp_left (g := fun a : ℝ => a ^ 2 / den n) (by simp)
      have hr (n : ℕ) : ContDiff ℝ 1 (r n) := contDiff_const.add ((hg n).of_le (by norm_num))
      have hrpos (n : ℕ) (x : E) : c n ≤ r n x := le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (hden n).le)
      have hApprox (n : ℕ) : ∃ hνn : IsProbabilityMeasure (νn n),
          letI := hνn
          relativeFisherInformation hV hp (νn n) ≤ ENNReal.ofReal (bn n) := by
        have hh := relativeFisherInformation_regularized_compact_square_le hV hp ρ hρ hHess
          (hf n) (hfc n) (ε n) (hε n)
        change (∃ hνn : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal
            (ε n / ((∫ y, f n y ^ 2 ∂μ) + ε n) + f n x ^ 2 / ((∫ y, f n y ^ 2 ∂μ) + ε n)))),
          letI := hνn
          relativeFisherInformation hV hp (μ.withDensity (fun x => ENNReal.ofReal
            (ε n / ((∫ y, f n y ^ 2 ∂μ) + ε n) + f n x ^ 2 / ((∫ y, f n y ^ 2 ∂μ) + ε n)))) ≤
            ENNReal.ofReal ((4 / ((∫ y, f n y ^ 2 ∂μ) + ε n)) * ∫ y, ‖gradient (f n) y‖ ^ 2 ∂μ)) at hh
        simpa only [hA n, hE n] using hh
      choose hνn hFIbound using hApprox
      let (n : ℕ) : IsProbabilityMeasure (νn n) := hνn n
      have hNorm (n : ℕ) : ∫ x, r n x ∂μ = 1 := by
        have hi : Integrable (r n) μ := (integrable_const (c n)).add
          ((hg n).continuous.integrable_of_hasCompactSupport (hgc n))
        exact integral_density_eq_one_of_probability hi (fun x => (hc n).trans_le (hrpos n x) |>.le) (hνn n)
      have hInputRep (n : ℕ) : (fun x => ((νn n).rnDeriv μ x).toReal) =ᵐ[μ] r n := by
        filter_upwards [Measure.rnDeriv_withDensity μ (hr n).continuous.measurable.ennreal_ofReal] with x hx
        rw [hx, ENNReal.toReal_ofReal ((hc n).trans_le (hrpos n x)).le]
      have hRrep : (fun x => (ν.rnDeriv μ x).toReal) =ᵐ[μ] fun x => R x ^ 2 := by
        filter_upwards [(squareRootRNDensity_memLp ν μ).coeFn_toLp] with x hx
        have hx' : (R : E → ℝ) x = squareRootRNDensity ν μ x := by convert! hx using 1
        rw [hx', squareRootRNDensity_sq]
      have hL1base := tendsto_integral_abs_regularized_squares_of_L2 hfirst hRnorm hε hεlim
      have hInputL1 : Tendsto (fun n => ∫ x, |((νn n).rnDeriv μ x).toReal - (ν.rnDeriv μ x).toReal| ∂μ)
          atTop (𝓝 0) := by
        apply hL1base.congr'
        apply Eventually.of_forall
        intro n
        apply integral_congr_ae
        filter_upwards [hInputRep n, hRrep, hfrep n] with x hn hx hfraw
        rw [hn, hx, hfraw]
        congr 1
        dsimp only [r, c, g, den]
        ring
      have hACn (n : ℕ) : νn n ≪ μ := withDensity_absolutelyContinuous _ _
      have hACout : K ∘ₘ ν ≪ μ := langevinKernel_comp_absolutelyContinuous hB hV hp ρ hρ hHess ν hAC t
      have hACoutn (n : ℕ) : K ∘ₘ νn n ≪ μ :=
        langevinKernel_comp_absolutelyContinuous hB hV hp ρ hρ hHess (νn n) (hACn n) t
      have hInv : K ∘ₘ μ = μ := langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess t
      have hOutputL1 : Tendsto (fun n => ∫ x,
          |((K ∘ₘ νn n).rnDeriv μ x).toReal - ((K ∘ₘ ν).rnDeriv μ x).toReal| ∂μ) atTop (𝓝 0) := by
        apply squeeze_zero (fun n => integral_nonneg (fun x => abs_nonneg _)) ?_ hInputL1
        intro n
        have hh := invariantKernel_L1_contraction K hInv
          (Measure.measurable_rnDeriv (νn n) μ).ennreal_toReal (Measure.measurable_rnDeriv ν μ).ennreal_toReal
          (integrable_toReal_rnDeriv_finite (νn n) μ) (integrable_toReal_rnDeriv_finite ν μ)
        have heq : (∫ x, |((K ∘ₘ νn n).rnDeriv μ x).toReal - ((K ∘ₘ ν).rnDeriv μ x).toReal| ∂μ) =
            ∫ x, |(∫ y, ((νn n).rnDeriv μ y).toReal ∂K x) - ∫ y, (ν.rnDeriv μ y).toReal ∂K x| ∂μ := by
          apply integral_congr_ae
          filter_upwards [langevinKernel_rnDeriv_toReal hB hV hp ρ hρ hHess (νn n) (hACn n) t,
            langevinKernel_rnDeriv_toReal hB hV hp ρ hρ hHess ν hAC t] with x hn hx
          rw [hn, hx]
        exact heq.trans_le hh
      have hRootLim := tendsto_squareRootRNDensityLp_of_L1_rnDeriv μ (K ∘ₘ ν) (fun n => K ∘ₘ νn n) hOutputL1
      have hLSC := relativeFisherInformation_le_liminf_of_squareRoot_tendsto hV hp (K ∘ₘ ν)
        (fun n => K ∘ₘ νn n) hACout hACoutn hRootLim
      have hDecay (n : ℕ) : relativeFisherInformation hV hp (K ∘ₘ νn n) ≤
          ENNReal.ofReal (Real.exp (-2 * ρ * t)) * ENNReal.ofReal (bn n) := by
        obtain ⟨_, hh⟩ := langevinKernel_evolved_relativeFisherInformation_le hB hV hp ρ hρ hHess
          ((hg n).of_le (by norm_num)) (hgc n) (c n) (c n) (hc n) (hrpos n) (hNorm n) t
        exact hh.trans (mul_le_mul_of_nonneg_left (hFIbound n) (by positivity))
      have hDen : Tendsto den atTop (𝓝 (1 : ℝ)) := by
        simpa only [hRnorm, add_zero] using (hfirst.norm.pow 2).add hεlim
      have hb : Tendsto bn atTop (𝓝 (4 * ‖D‖ ^ 2)) := by
        simpa only [Pi.div_def, div_one, bn, den] using
          ((tendsto_const_nhds (x := (4 : ℝ))).div hDen (by norm_num)).mul (hsecond.norm.pow 2)
      have hBoundLim : Tendsto (fun n => ENNReal.ofReal (Real.exp (-2 * ρ * t)) * ENNReal.ofReal (bn n)) atTop
          (𝓝 (ENNReal.ofReal (Real.exp (-2 * ρ * t)) * ENNReal.ofReal (4 * ‖D‖ ^ 2))) :=
        (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).continuousAt.tendsto.comp
          (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hb)
      have hLiminf : liminf (fun n => relativeFisherInformation hV hp (K ∘ₘ νn n)) atTop ≤
          liminf (fun n => ENNReal.ofReal (Real.exp (-2 * ρ * t)) * ENNReal.ofReal (bn n)) atTop :=
        liminf_le_liminf (Eventually.of_forall hDecay)
      rw [hBoundLim.liminf_eq] at hLiminf
      have hFI := relativeFisherInformation_eq_closed_energy hV hp ν hAC hD
      change relativeFisherInformation hV hp ν = ENNReal.ofReal (4 * ‖D‖ ^ 2) at hFI
      rw [hFI]
      exact hLSC.trans hLiminf
    · have hTop : relativeFisherInformation hV hp ν = ⊤ := by
        have hAC' : ν ≪ gibbsMeasure volume V := hAC
        have hD' : squareRootRNDensityLp ν (gibbsMeasure volume V) ∉ (closedGibbsGradient hV hp).domain := hD
        simp only [relativeFisherInformation, hAC', dite_true, hD', dite_false]
      rw [hTop, ENNReal.mul_top hExp]
      exact le_top
  · rw [relativeFisherInformation_eq_top_of_not_ac hV hp ν hAC, ENNReal.mul_top hExp]
    exact le_top

end CutoffRigidity
