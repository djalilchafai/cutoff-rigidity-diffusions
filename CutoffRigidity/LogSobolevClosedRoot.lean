module
public import CutoffRigidity.LogSobolevSquareCore
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Logarithmic Sobolev on the actual normalized closed H¹ root domain

Compact graph approximation, genuine positive square regularization, an
actual almost-everywhere subsequence, and nonnegative KL-integrand Fatou
extend the checked stochastic proof to the full closed energy domain.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped ENNReal NNReal Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual normalized closed-H¹ root inequality. The graph and its
approximants are the genuine closure of the actual compact gradient. -/
theorem logSobolev_closed_normalized_root
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (u : gibbsSobolevGraph hV hp)
    (hu : ‖gibbsSobolevInclusion hV hp u‖ ^ 2 = 1) :
    (∫⁻ x, ENNReal.ofReal (klFun ((gibbsSobolevInclusion hV hp u x) ^ 2))
      ∂gibbsMeasure volume V) ≤
      ENNReal.ofReal ((2 / ρ) * ‖gibbsSobolevDerivative hV hp u‖ ^ 2) := by
  let := hp
  let μ := gibbsMeasure volume V
  let G := compactGibbsGradient hV.continuous hp
  let U := gibbsSobolevInclusion hV hp u
  let D := gibbsSobolevDerivative hV hp u
  have hmem : (U, D) ∈ closure (G.graph : Set _) := by
    change (U, D) ∈ G.graph.topologicalClosure
    rw [(compactGibbsGradient_isClosable hV hp).graph_closure_eq_closure_graph]
    exact u.property
  obtain ⟨p, hpseq, hplim⟩ := mem_closure_iff_seq_limit.mp hmem
  have hfirst : Tendsto (fun n => (p n).1) atTop (𝓝 U) := (continuous_fst.tendsto _).comp hplim
  have hsecond : Tendsto (fun n => (p n).2) atTop (𝓝 D) := (continuous_snd.tendsto _).comp hplim
  let ε := fun n : ℕ => differenceStep n
  have hεpos (n : ℕ) : 0 < ε n := differenceStep_pos n
  have hεlim : Tendsto ε atTop (𝓝 0) := differenceStep_tendsto_zero
  let F := fun (n : ℕ) (x : E) => ENNReal.ofReal
    (klFun (((p n).1 x ^ 2 + ε n) / (‖(p n).1‖ ^ 2 + ε n)))
  let b := fun n : ℕ => (2 / ρ) / (‖(p n).1‖ ^ 2 + ε n) * ‖(p n).2‖ ^ 2
  have hbound (n : ℕ) : (∫⁻ x, F n x ∂μ) ≤ ENNReal.ofReal (b n) := by
    obtain ⟨v, hv1, hv2⟩ := G.mem_graph_iff.mp (hpseq n)
    let f := compactGibbsRepresentative V v
    have hf := (compactGibbsRepresentative_spec V v).1
    have hfc := (compactGibbsRepresentative_spec V v).2.1
    have hfrep : (p n).1 =ᵐ[μ] f := by
      rw [← hv1]
      exact (compactGibbsRepresentative_spec V v).2.2.symm
    have hgrep : (p n).2 =ᵐ[μ] gradient f := by
      rw [← hv2]
      exact (compactGibbsGradient_memLp hp v).coeFn_toLp
    have hA : (∫ x, f x ^ 2 ∂μ) = ‖(p n).1‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hfrep] with x hx
      rw [hx, Real.inner_apply]
      ring
    have hE : (∫ x, ‖gradient f x‖ ^ 2 ∂μ) = ‖(p n).2‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hgrep] with x hx
      rw [hx, real_inner_self_eq_norm_sq]
    have hh := logSobolev_regularized_compact_square hB hV hp hd ρ hρ hHess hf hfc (ε n) (hεpos n)
    change (∫⁻ x, ENNReal.ofReal (klFun ((f x ^ 2 + ε n) / ((∫ y, f y ^ 2 ∂μ) + ε n))) ∂μ) ≤
      ENNReal.ofReal ((2 / ρ) / ((∫ y, f y ^ 2 ∂μ) + ε n) * ∫ x, ‖gradient f x‖ ^ 2 ∂μ) at hh
    rw [hA, hE] at hh
    calc
      _ = ∫⁻ x, ENNReal.ofReal (klFun ((f x ^ 2 + ε n) / (‖(p n).1‖ ^ 2 + ε n))) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hfrep] with x hx
        simp only [F, hx]
      _ ≤ _ := hh
  have hU : ‖U‖ ^ 2 = 1 := hu
  have hDen : Tendsto (fun n => ‖(p n).1‖ ^ 2 + ε n) atTop (𝓝 (1 : ℝ)) := by
    simpa only [hU, add_zero] using (hfirst.norm.pow 2).add hεlim
  have hb : Tendsto b atTop (𝓝 ((2 / ρ) * ‖D‖ ^ 2)) := by
    simpa only [div_one, Pi.div_apply, Function.comp_def, b] using (tendsto_const_nhds.div hDen (by norm_num)).mul (hsecond.norm.pow 2)
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hfirst).exists_seq_tendsto_ae'
  have hFm (n : ℕ) : Measurable (F (ns n)) := by
    apply Measurable.ennreal_ofReal
    apply measurable_klFun.comp
    exact (((Lp.stronglyMeasurable (p (ns n)).1).measurable.pow_const 2).add measurable_const).div_const _
  have hpoint : ∀ᵐ x ∂μ, liminf (fun n => F (ns n) x) atTop = ENNReal.ofReal (klFun (U x ^ 2)) := by
    filter_upwards [hae] with x hx
    have hr := ((hx.pow 2).add (hεlim.comp hns)).div (hDen.comp hns) (by norm_num)
    have hr' : Tendsto (fun n => ((p (ns n)).1 x ^ 2 + ε (ns n)) /
        (‖(p (ns n)).1‖ ^ 2 + ε (ns n))) atTop (𝓝 (U x ^ 2)) := by
      simpa only [add_zero, div_one, Pi.div_def, Pi.add_apply, Function.comp_def] using hr
    exact ((ENNReal.continuous_ofReal.comp continuous_klFun).continuousAt.tendsto.comp hr').liminf_eq
  have hFatou := lintegral_liminf_le (μ := μ) (f := fun n => F (ns n)) (u := atTop) hFm
  rw [lintegral_congr_ae hpoint] at hFatou
  have hh : liminf (fun n => ∫⁻ x, F (ns n) x ∂μ) atTop ≤
      liminf (fun n => ENNReal.ofReal (b (ns n))) atTop :=
    liminf_le_liminf (Eventually.of_forall (fun n => hbound (ns n)))
  have hblim : Tendsto (fun n => ENNReal.ofReal (b (ns n))) atTop
      (𝓝 (ENNReal.ofReal ((2 / ρ) * ‖D‖ ^ 2))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hb.comp hns)
  rw [hblim.liminf_eq] at hh
  exact hFatou.trans hh

end CutoffRigidity
