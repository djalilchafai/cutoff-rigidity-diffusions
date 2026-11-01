module

public import CutoffRigidity.Statements
public import CutoffRigidity.Extra.Dynamics
public import CutoffRigidity.Extra.Dissip1
public import CutoffRigidity.LangevinDeBruijn
public import CutoffRigidity.LangevinEntropyDrop

/-! # Entropy dissipation (de Bruijn) along the Langevin flow, carrier level

* `langevin_dissipation_ge` : for an arbitrary initial law `ν` with `H(ν | μ) < ∞` and `0 < s < t`,
  `H(μ_t | μ) + ∫_s^t I(μ_r | μ) dr ≤ H(μ_s | μ)` (the half `≥` of the integrated de Bruijn
  identity `H(μ_s) - H(μ_t) = ∫_s^t I`, manuscript eq. `eq:HI`).
* `langevin_dissipation_core` : the full identity `H(μ_s) - H(μ_t) = ∫_s^t I` (`0 ≤ s < t`) when `ν`
  has a density `c + g`, `g ∈ C²` compactly supported, `c + g ≥ m > 0`, normalized.
-/

public section

namespace CutoffRigidity.Dissip

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The law at time `r : ℝ` (clamped at `0`) started from `ν`. -/
noncomputable abbrev lawAt {B : ℝ≥0 → Ω → E} {P : Measure Ω} (V : E → ℝ) (ν : Measure E) (r : ℝ) :
    Measure E := langevinKernel V B P r.toNNReal ∘ₘ ν

/-- Entropy-Fisher drop, from an arbitrary time `s ≥ 0`, in the extended-real form. -/
theorem drop_ennreal {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    klDiv (lawAt (B := B) (P := P) V ν t) (CutCur.gibbs V) +
        ENNReal.ofReal (t - s) * CutCur.fisherInfo V (lawAt (B := B) (P := P) V ν t) ≤
      klDiv (lawAt (B := B) (P := P) V ν s) (CutCur.gibbs V) := by
  have hmk : ∀ r : ℝ≥0, IsMarkovKernel (langevinKernel V B P r) := fun r =>
    langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess r
  let := hmk s.toNNReal
  let := hmk t.toNNReal
  have : IsProbabilityMeasure (langevinKernel V B P s.toNNReal ∘ₘ ν) := inferInstance
  have h := langevinKernel_entropy_fisher_drop hB hV hp ρ hρ hHess
    (langevinKernel V B P s.toNNReal ∘ₘ ν) (t - s) (sub_pos.mpr hst)
  have hc : langevinKernel V B P (t - s).toNNReal ∘ₘ (langevinKernel V B P s.toNNReal ∘ₘ ν) =
      langevinKernel V B P t.toNNReal ∘ₘ ν := by
    rw [Measure.comp_assoc, langevinKernel_comp hB hV ρ hρ.le hHess, ← Real.toNNReal_add
      hs (sub_pos.mpr hst).le]
    have : s + (t - s) = t := by ring
    rw [this]
  simp only [hc] at h
  have hI : CutCur.fisherInfo V (langevinKernel V B P t.toNNReal ∘ₘ ν) =
      relativeFisherInformation hV hp (langevinKernel V B P t.toNNReal ∘ₘ ν) :=
    fisherInfo_eq_relativeFisherInformation hV hp ρ hρ hHess _
  show _ + _ * CutCur.fisherInfo V (langevinKernel V B P t.toNNReal ∘ₘ ν) ≤ _
  rw [hI]
  exact h


/-- `lawAt` at time `0` is the initial law. -/
theorem lawAt_zero {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (ν : Measure E) :
    lawAt (B := B) (P := P) V ν 0 = ν := by
  simp [lawAt, langevinKernel_zero hB hV ρ hρ hHess]

/-- **Integrated de Bruijn inequality for an arbitrary initial law of finite entropy.**
For `0 < s < t`: `H(μ_t | μ) + ∫_s^t I(μ_r | μ) dr ≤ H(μ_s | μ)` (extended reals, Lebesgue integral),
where `μ_r = ν P_r`. -/
theorem langevin_dissipation_ge {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] (hfin : klDiv ν (CutCur.gibbs V) ≠ ⊤)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    (∫⁻ r in Ioc s t, CutCur.fisherInfo V (lawAt (B := B) (P := P) V ν r)) +
        klDiv (lawAt (B := B) (P := P) V ν t) (CutCur.gibbs V) ≤
      klDiv (lawAt (B := B) (P := P) V ν s) (CutCur.gibbs V) := by
  have hmk : ∀ r : ℝ≥0, IsMarkovKernel (langevinKernel V B P r) := fun r =>
    langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess r
  set μ := CutCur.gibbs V with hμ
  have h0 := lawAt_zero (B := B) (P := P) hB hV ρ hρ.le hHess ν
  -- finiteness
  have hHfin : ∀ r : ℝ, 0 ≤ r → klDiv (lawAt (B := B) (P := P) V ν r) μ ≠ ⊤ := by
    intro r hr
    rcases hr.eq_or_lt with h | h
    · rw [← h, h0]; exact hfin
    · have := drop_ennreal hB hV hp ρ hρ hHess ν (le_refl (0:ℝ)) h
      rw [h0] at this
      exact ne_top_of_le_ne_top hfin (le_trans le_self_add this)
  have hIfin : ∀ r : ℝ, 0 < r → CutCur.fisherInfo V (lawAt (B := B) (P := P) V ν r) ≠ ⊤ := by
    intro r hr h
    have := drop_ennreal hB hV hp ρ hρ hHess ν (le_refl (0:ℝ)) hr
    rw [h0, h, sub_zero, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hr).ne', add_top] at this
    exact hfin (top_le_iff.mp this)
  set H : ℝ → ℝ := fun r => (klDiv (lawAt (B := B) (P := P) V ν r) μ).toReal with hH
  set I : ℝ → ℝ := fun r => (CutCur.fisherInfo V (lawAt (B := B) (P := P) V ν r)).toReal with hI
  have hdrop : ∀ a b : ℝ, 0 < a → a < b → H b + (b - a) * I b ≤ H a := by
    intro a b ha hab
    have h := drop_ennreal hB hV hp ρ hρ hHess ν ha.le hab
    have hb : 0 < b := ha.trans hab
    have h2 := ENNReal.toReal_mono (hHfin a ha.le) h
    rw [ENNReal.toReal_add (hHfin b hb.le) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hIfin b hb)),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_pos.mpr hab).le] at h2
    exact h2
  have hanti : AntitoneOn I (Ioi 0) := by
    intro a ha b hb hab
    have ha' : (0:ℝ) < a := ha
    have hb' : (0:ℝ) < b := hb
    let := hmk a.toNNReal
    let := hmk b.toNNReal
    have e1 := fisherInfo_eq_relativeFisherInformation hV hp ρ hρ hHess
      (lawAt (B := B) (P := P) V ν a)
    have e2 := fisherInfo_eq_relativeFisherInformation hV hp ρ hρ hHess
      (lawAt (B := B) (P := P) V ν b)
    have := relativeFisherInformation_langevinKernel_antitone hB hV hp ρ hρ hHess ν
      a.toNNReal b.toNNReal (Real.toNNReal_mono hab)
    show (CutCur.fisherInfo V (lawAt (B := B) (P := P) V ν b)).toReal ≤
      (CutCur.fisherInfo V (lawAt (B := B) (P := P) V ν a)).toReal
    refine ENNReal.toReal_mono (hIfin a ha') ?_
    rw [e1, e2]
    exact this
  have hreal := integral_le_sub_of_drop hdrop hanti hs hst
  have hint : IntervalIntegrable I volume s t :=
    (hanti.mono (by
      intro r hr
      rw [uIcc_of_le hst.le] at hr
      exact lt_of_lt_of_le hs hr.1)).intervalIntegrable
  have hint' : IntegrableOn I (Ioc s t) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hst.le).mp hint
  have hnn : ∀ r ∈ Ioc s t, 0 ≤ I r := fun r _ => ENNReal.toReal_nonneg
  have hlint : ∫⁻ r in Ioc s t, CutCur.fisherInfo V (lawAt (B := B) (P := P) V ν r) =
      ENNReal.ofReal (∫ r in s..t, I r) := by
    rw [intervalIntegral.integral_of_le hst.le,
      ofReal_integral_eq_lintegral_ofReal hint'
        ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall hnn))]
    refine setLIntegral_congr_fun measurableSet_Ioc (fun r hr => ?_)
    exact (ENNReal.ofReal_toReal (hIfin r (hs.trans hr.1))).symm
  rw [hlint]
  have hs0 := hs.le
  have ht0 := (hs.trans hst).le
  have hfs := hHfin s hs0
  have hft := hHfin t ht0
  rw [← ENNReal.ofReal_toReal hft, ← ENNReal.ofReal_toReal hfs,
    ← ENNReal.ofReal_add (intervalIntegral.integral_nonneg hst.le fun r _ => ENNReal.toReal_nonneg)
      ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_le_ofReal (by simpa [H] using hreal |> fun h => by linarith)

set_option maxHeartbeats 800000 in
/-- **Full integrated de Bruijn identity for compact-perturbation initial densities**:
if `ν = (c + g) μ` with `g ∈ C²` compactly supported, `c + g ≥ m > 0`, `∫ (c + g) dμ = 1`, then for
`0 ≤ s < t`, `H(μ_s | μ) = H(μ_t | μ) + ∫_s^t I(μ_r | μ) dr` (extended reals). -/
theorem langevin_dissipation_core {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)
    (hNorm : ∫ x, c + g x ∂gibbsMeasure volume V = 1)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    klDiv (lawAt (B := B) (P := P) V
        ((gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (c + g x))) s)
        (CutCur.gibbs V) =
      klDiv (lawAt (B := B) (P := P) V
        ((gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (c + g x))) t)
        (CutCur.gibbs V) +
      ∫⁻ r in Ioc s t, CutCur.fisherInfo V (lawAt (B := B) (P := P) V
        ((gibbsMeasure volume V).withDensity (fun x => ENNReal.ofReal (c + g x))) r) := by
  have hmk : ∀ r : ℝ≥0, IsMarkovKernel (langevinKernel V B P r) := fun r =>
    langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess r
  set μ := gibbsMeasure volume V with hμ
  set ν := μ.withDensity (fun x => ENNReal.ofReal (c + g x)) with hνdef
  obtain ⟨hν, hKL0, hFI0⟩ := langevin_core_information_finite hB hV hp ρ hρ hHess
    (hg.of_le (by norm_num)) hgc c m hm hpos hNorm
  let := hν
  have h0 := lawAt_zero (B := B) (P := P) hB hV ρ hρ.le hHess ν
  have hfin : klDiv ν (CutCur.gibbs V) ≠ ⊤ := hKL0
  have hHfin : ∀ r : ℝ, 0 ≤ r → klDiv (lawAt (B := B) (P := P) V ν r) (CutCur.gibbs V) ≠ ⊤ := by
    intro r hr
    rcases hr.eq_or_lt with h | h
    · rw [← h, h0]; exact hfin
    · have := drop_ennreal hB hV hp ρ hρ hHess ν (le_refl (0:ℝ)) h
      rw [h0] at this
      exact ne_top_of_le_ne_top hfin (le_trans le_self_add this)
  have hIeq : ∀ r : ℝ, CutCur.fisherInfo V (lawAt (B := B) (P := P) V ν r) =
      @relativeFisherInformation d V hV hp (lawAt (B := B) (P := P) V ν r)
        (by let := hmk r.toNNReal; infer_instance) := fun r => by
    let := hmk r.toNNReal
    exact fisherInfo_eq_relativeFisherInformation hV hp ρ hρ hHess _
  have hIfin : ∀ r : ℝ, 0 ≤ r → CutCur.fisherInfo V (lawAt (B := B) (P := P) V ν r) ≠ ⊤ := by
    intro r hr
    rw [hIeq]
    let := hmk r.toNNReal
    have h1 := relativeFisherInformation_langevinKernel_antitone hB hV hp ρ hρ hHess ν 0 r.toNNReal
      bot_le
    simp only [langevinKernel_zero hB hV ρ hρ.le hHess, Measure.id_comp] at h1
    exact ne_top_of_le_ne_top hFI0 h1
  set H : ℝ → ℝ := fun r =>
    (klDiv (lawAt (B := B) (P := P) V ν r) (CutCur.gibbs V)).toReal with hH
  set I : ℝ → ℝ := fun r =>
    (CutCur.fisherInfo V (lawAt (B := B) (P := P) V ν r)).toReal with hI
  have hanti : AntitoneOn I (Ici 0) := by
    intro a ha b hb hab
    have ha' : (0:ℝ) ≤ a := ha
    have hb' : (0:ℝ) ≤ b := hb
    let := hmk a.toNNReal
    let := hmk b.toNNReal
    have := relativeFisherInformation_langevinKernel_antitone hB hV hp ρ hρ hHess ν
      a.toNNReal b.toNNReal (Real.toNNReal_mono hab)
    show (CutCur.fisherInfo V (lawAt (B := B) (P := P) V ν b)).toReal ≤
      (CutCur.fisherInfo V (lawAt (B := B) (P := P) V ν a)).toReal
    refine ENNReal.toReal_mono (hIfin a ha') ?_
    rw [hIeq, hIeq]
    exact this
  have hcont : ContinuousOn H (Icc s t) := by
    have hc := continuous_klDiv_langevinKernel hB hV hp ρ hρ hHess (hg.of_le (by norm_num)) hgc
      c m hm hpos hν
    exact (hc.comp continuous_real_toNNReal).continuousOn
  have hderiv : ∀ r ∈ Ioo s t, HasDerivAt H (-I r) r := by
    intro r hr
    have hr0 : 0 < r := lt_of_le_of_lt hs hr.1
    have hd := hasDerivAt_klDiv_langevinKernel hB hV hp ρ hρ hHess hg hgc c m hm hpos hν hr0
    have e := hIeq r
    let := hmk r.toNNReal
    simp only [hI]
    rw [e]
    exact hd
  have hint : IntervalIntegrable I volume s t :=
    (hanti.mono (by
      intro r hr
      rw [uIcc_of_le hst.le] at hr
      exact hs.trans hr.1)).intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst.le hcont hderiv hint.neg
  rw [intervalIntegral.integral_neg] at hFTC
  have hint' : IntegrableOn I (Ioc s t) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hst.le).mp hint
  have hnn : ∀ r ∈ Ioc s t, 0 ≤ I r := fun r _ => ENNReal.toReal_nonneg
  have hlint : ∫⁻ r in Ioc s t, CutCur.fisherInfo V (lawAt (B := B) (P := P) V ν r) =
      ENNReal.ofReal (∫ r in s..t, I r) := by
    rw [intervalIntegral.integral_of_le hst.le,
      ofReal_integral_eq_lintegral_ofReal hint'
        ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall hnn))]
    refine setLIntegral_congr_fun measurableSet_Ioc (fun r hr => ?_)
    exact (ENNReal.ofReal_toReal (hIfin r (hs.trans hr.1.le))).symm
  rw [hlint]
  have hfs := hHfin s hs
  have hft := hHfin t (hs.trans hst.le)
  have hIn : 0 ≤ ∫ r in s..t, I r := intervalIntegral.integral_nonneg hst.le fun r _ => ENNReal.toReal_nonneg
  rw [← ENNReal.ofReal_toReal hft, ← ENNReal.ofReal_toReal hfs,
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg hIn]
  congr 1
  simp only [hH] at hFTC
  linarith

end CutoffRigidity.Dissip
