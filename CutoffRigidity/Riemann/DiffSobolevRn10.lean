module

public import CutoffRigidity.Riemann.DiffEllipticRn7
public import CutoffRigidity.Riemann.DiffSobolevRn3
public import CutoffRigidity.Riemann.DiffSobolevRn9

/-! # Mollification in `Sob`, and the Sobolev embedding
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)

theorem hasWDeriv_molN (n : ℕ) {v : E} {f w : E → ℝ} (hf : MemLp f 2 volume)
    (h : HasWDeriv Set.univ v f w) (hw : MemLp w 2 volume) :
    HasWDeriv Set.univ v (molN n f) (molN n w) := by
  have hd : pd v (molN n f) = molN n w := by
    funext x; exact fderiv_mol _ _ h x
  have := hasWDeriv_of_contDiff (Ω := Set.univ) (molN_contDiff n hf |>.of_le (by simp)) v
  rwa [hd] at this

theorem sob_molN (n : ℕ) (m : ℕ) {w : E → ℝ} (hw : Sob b m w) :
    Sob b m (molN n w) ∧ sobSq b m (molN n w) ≤ sobSq b m w := by
  induction m generalizing w with
  | zero =>
    exact ⟨molN_memLp n hw, integral_sq_mol_le _ _ hw⟩
  | succ m ih =>
    have hw' := (Sob.succ_iff b).1 hw
    have key : ∀ i, HasWDeriv Set.univ (b i) (molN n w) (molN n (wd (b i) w)) ∧
        Sob b m (molN n (wd (b i) w)) ∧
        sobSq b m (molN n (wd (b i) w)) ≤ sobSq b m (wd (b i) w) := fun i =>
      ⟨hasWDeriv_molN n hw'.1 (hw'.2 i).1 ((hw'.2 i).2.memLp b), (ih (hw'.2 i).2).1,
        (ih (hw'.2 i).2).2⟩
    refine ⟨⟨molN_memLp n hw'.1, fun i => ⟨_, (key i).1, (key i).2.1⟩⟩, ?_⟩
    rw [sobSq_succ_eq b (fun i => ⟨(key i).1, ((key i).2.1).memLp b⟩)]
    have e : sobSq b (m + 1) w = (∫ x, w x ^ 2) + ∑ i, sobSq b m (wd (b i) w) := rfl
    rw [e]
    exact add_le_add (integral_sq_mol_le _ _ hw'.1)
      (Finset.sum_le_sum (fun i _ => (key i).2.2))

theorem tendsto_sobSq_molN_sub (m : ℕ) {w : E → ℝ} (hw : Sob b m w) :
    Tendsto (fun n => sobSq b m (fun x => molN n w x - w x)) atTop (𝓝 0) := by
  induction m generalizing w with
  | zero => exact tendsto_molN_sq hw
  | succ m ih =>
    have hw' := (Sob.succ_iff b).1 hw
    have key : ∀ n i, HasWDeriv Set.univ (b i) (fun x => molN n w x - w x)
        (fun x => molN n (wd (b i) w) x - wd (b i) w x) := fun n i =>
      (hasWDeriv_molN n hw'.1 (hw'.2 i).1 ((hw'.2 i).2.memLp b)).sub (hw'.2 i).1
    have hmem : ∀ n i, MemLp (fun x => molN n (wd (b i) w) x - wd (b i) w x) 2 volume :=
      fun n i => (molN_memLp n ((hw'.2 i).2.memLp b)).sub ((hw'.2 i).2.memLp b)
    have e : ∀ n, sobSq b (m + 1) (fun x => molN n w x - w x) =
        (∫ x, (molN n w x - w x) ^ 2) +
          ∑ i, sobSq b m (fun x => molN n (wd (b i) w) x - wd (b i) w x) := fun n =>
      sobSq_succ_eq b (fun i => ⟨key n i, hmem n i⟩)
    simp only [e]
    have := (tendsto_molN_sq hw'.1).add
      (tendsto_finset_sum (Finset.univ : Finset ι) (fun i _ => ih (hw'.2 i).2))
    simpa using this

theorem ae_eq_of_pointwise_L2_limit {f : ℕ → E → ℝ} {g w : E → ℝ}
    (hfm : ∀ n, MemLp (fun x => f n x - w x) 2 volume)
    (hg : AEStronglyMeasurable g volume) (hw : AEStronglyMeasurable w volume)
    (hpt : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hL : Tendsto (fun n => ∫ x, (f n x - w x) ^ 2) atTop (𝓝 0)) : g =ᵐ[volume] w := by
  set h : ℕ → E → ENNReal := fun n x => ENNReal.ofReal ((f n x - w x) ^ 2) with hh
  have hmeas : ∀ n, AEMeasurable (h n) volume := fun n =>
    ((hfm n).aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal
  have hlim : ∀ x, Tendsto (fun n => h n x) atTop (𝓝 (ENNReal.ofReal ((g x - w x) ^ 2))) := by
    intro x
    exact ENNReal.tendsto_ofReal (((hpt x).sub_const (w x)).pow 2)
  have hF := lintegral_liminf_le' (μ := volume) (u := atTop) hmeas
  have e1 : ∀ x, liminf (fun n => h n x) atTop = ENNReal.ofReal ((g x - w x) ^ 2) :=
    fun x => (hlim x).liminf_eq
  simp only [e1] at hF
  have e2 : ∀ n, ∫⁻ x, h n x = ENNReal.ofReal (∫ x, (f n x - w x) ^ 2) := by
    intro n
    rw [ofReal_integral_eq_lintegral_ofReal (hfm n).integrable_sq
      (Filter.Eventually.of_forall fun x => sq_nonneg _)]
  have e3 : Tendsto (fun n => ∫⁻ x, h n x) atTop (𝓝 0) := by
    simp only [e2]
    simpa using ENNReal.tendsto_ofReal hL
  rw [e3.liminf_eq] at hF
  have h0 : ∫⁻ x, ENNReal.ofReal ((g x - w x) ^ 2) = 0 := le_antisymm hF bot_le
  have hm : AEMeasurable (fun x => ENNReal.ofReal ((g x - w x) ^ 2)) volume :=
    (((hg.sub hw).aemeasurable).pow_const 2).ennreal_ofReal
  have := (lintegral_eq_zero_iff' hm).1 h0
  filter_upwards [this] with x hx
  have : (g x - w x) ^ 2 ≤ 0 := by
    simpa using hx
  nlinarith [sq_nonneg (g x - w x)]

/-- Sobolev embedding for `H^m` functions with (a.e.) compact support. -/
theorem sobolev_embedding {j m : ℕ} (hm : Module.finrank ℝ E + 2 * j < 2 * m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : E → ℝ, Sob b m w → AESupp w →
      ∃ g : E → ℝ, ContDiff ℝ j g ∧ g =ᵐ[volume] w ∧
        ∀ x, ∀ i ≤ j, ‖iteratedFDeriv ℝ i g x‖ ^ 2 ≤ C * sobSq b m w := by
  obtain ⟨C, hC0, hSI⟩ := sobolev_sup_sq_le b hm
  refine ⟨C, hC0, fun w hw hs => ?_⟩
  obtain ⟨R, hR⟩ := hs
  have hwm : MemLp w 2 volume := hw.memLp b
  have hf : ∀ n, ContDiff ℝ ∞ (molN n w) := fun n => molN_contDiff n hwm
  have hfc : ∀ n, HasCompactSupport (molN n w) := fun n => mol_hasCompactSupport _ _ R hR
  set a : ℕ → ℝ := fun n => sobSq b m (fun x => molN n w x - w x) with ha
  have ha0 : Tendsto a atTop (𝓝 0) := tendsto_sobSq_molN_sub b m hw
  have hSob : ∀ n, Sob b m (fun x => molN n w x - w x) := fun n =>
    (Sob.sub b (sob_molN b n m hw).1 hw).1
  -- difference estimate
  have hdiff : ∀ n n', ∀ x, ∀ i ≤ j,
      ‖iteratedFDeriv ℝ i (molN n w) x - iteratedFDeriv ℝ i (molN n' w) x‖ ^ 2 ≤
        C * (2 * (a n + a n')) := by
    intro n n' x i hi
    have hd : ContDiff ℝ ∞ (molN n w - molN n' w) := (hf n).sub (hf n')
    have hdc : HasCompactSupport (molN n w - molN n' w) := (hfc n).sub (hfc n')
    have h1 := hSI _ hd hdc x i hi
    have h2 := (Sob.of_smooth b m hd hdc).2
    have h3 : sobSq b m (molN n w - molN n' w) ≤ 2 * (a n + a n') := by
      have e : (molN n w - molN n' w) =
          fun x => (molN n w x - w x) - (molN n' w x - w x) := by funext x; simp
      rw [e]
      exact (Sob.sub b (hSob n) (hSob n')).2
    have e2 : iteratedFDeriv ℝ i (molN n w - molN n' w) x =
        iteratedFDeriv ℝ i (molN n w) x - iteratedFDeriv ℝ i (molN n' w) x := by
      rw [iteratedFDeriv_sub (((hf n).of_le (by simp)) : ContDiff ℝ i _)
        (((hf n').of_le (by simp)) : ContDiff ℝ i _)]
      rfl
    rw [← e2]
    refine h1.trans ?_
    rw [← h2]
    exact mul_le_mul_of_nonneg_left h3 hC0
  have hc : ∀ i ≤ j, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ n' ≥ N, ∀ x,
      ‖iteratedFDeriv ℝ i (molN n w) x - iteratedFDeriv ℝ i (molN n' w) x‖ ≤ ε := by
    intro i hi ε hε
    have hδ : 0 < ε ^ 2 / (4 * C + 1) := by positivity
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 ha0) (ε ^ 2 / (4 * C + 1)) hδ
    refine ⟨N, fun n hn n' hn' x => ?_⟩
    have h1 := hN n hn
    have h2 := hN n' hn'
    rw [Real.dist_eq, sub_zero] at h1 h2
    have an0 : 0 ≤ a n := sobSq_nonneg b m _
    have an0' : 0 ≤ a n' := sobSq_nonneg b m _
    rw [abs_of_nonneg an0] at h1
    rw [abs_of_nonneg an0'] at h2
    have h3 := hdiff n n' x i hi
    have h4 : C * (2 * (a n + a n')) ≤ ε ^ 2 := by
      have : (a n + a n') ≤ 2 * (ε ^ 2 / (4 * C + 1)) := by linarith
      calc C * (2 * (a n + a n')) ≤ C * (2 * (2 * (ε ^ 2 / (4 * C + 1)))) := by gcongr
        _ = (4 * C) * (ε ^ 2 / (4 * C + 1)) := by ring
        _ ≤ (4 * C + 1) * (ε ^ 2 / (4 * C + 1)) := by gcongr; linarith
        _ = ε ^ 2 := by field_simp
    have h5 := h3.trans h4
    exact le_of_sq_le_sq (by simpa using h5) hε.le
  obtain ⟨g, hg, hpt, hit⟩ := exists_contDiff_limit j (fun n => molN n w) hf hc
  refine ⟨g, hg, ?_, ?_⟩
  · refine ae_eq_of_pointwise_L2_limit (f := fun n => molN n w) (fun n => ?_)
      hg.continuous.aestronglyMeasurable hwm.aestronglyMeasurable hpt (tendsto_molN_sq hwm)
    exact (molN_memLp n hwm).sub hwm
  · intro x i hi
    have hlim : Tendsto (fun n => ‖iteratedFDeriv ℝ i (molN n w) x‖ ^ 2) atTop
        (𝓝 (‖iteratedFDeriv ℝ i g x‖ ^ 2)) := ((hit i hi x).norm).pow 2
    refine le_of_tendsto hlim (Filter.Eventually.of_forall fun n => ?_)
    have h1 := hSI _ (hf n) (hfc n) x i hi
    have h2 := (Sob.of_smooth b m (hf n) (hfc n)).2
    have h3 := (sob_molN b n m hw).2
    rw [← h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left h3 hC0)

end CutoffRigidity.Riemann.Diff
