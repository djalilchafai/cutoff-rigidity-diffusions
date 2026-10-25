module

public import CutoffRigidity.Riemann.DiffSobolevRn6
public import CutoffRigidity.Riemann.DiffSobolevRn2
public import CutoffRigidity.Riemann.DiffSobolevRn3

/-! # `L²` toolbox and the bound `‖D_h f‖₂ ≤ ‖∂ f‖₂`
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `L²` norm of a function. -/
noncomputable def l2 (f : E → ℝ) : ℝ := Real.sqrt (∫ x, f x ^ 2)

theorem l2_nonneg (f : E → ℝ) : 0 ≤ l2 f := Real.sqrt_nonneg _

theorem l2_sq (f : E → ℝ) : l2 f ^ 2 = ∫ x, f x ^ 2 :=
  Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg _))

theorem abs_integral_mul_le_l2 {f g : E → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    |∫ x, f x * g x| ≤ l2 f * l2 g := by
  have h1 : Integrable (fun x => f x ^ 2) volume := hf.integrable_sq
  have h2 : Integrable (fun x => g x ^ 2) volume := hg.integrable_sq
  have hi : Integrable (fun x => |f x * g x|) volume := (hf.integrable_mul hg).abs
  have hcs := cs_aux (u := fun x => |f x * g x|) (q := fun x => f x ^ 2) (p := fun x => g x ^ 2)
    (fun _ => abs_nonneg _) (fun _ => sq_nonneg _) (fun _ => sq_nonneg _) hi h1 h2
    (fun x => by rw [sq_abs, mul_pow])
  have h3 : |∫ x, f x * g x| ≤ ∫ x, |f x * g x| := by
    simpa using abs_integral_le_integral_abs (μ := volume) (f := fun x => f x * g x)
  have h4 : ∫ x, |f x * g x| ≤ l2 f * l2 g := by
    by_contra hlt
    push Not at hlt
    have hp : 0 ≤ l2 f * l2 g := mul_nonneg (l2_nonneg f) (l2_nonneg g)
    have := pow_lt_pow_left₀ hlt hp two_ne_zero
    rw [mul_pow, l2_sq, l2_sq] at this
    linarith
  exact h3.trans h4

theorem l2_add_le {f g : E → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    l2 (fun x => f x + g x) ≤ l2 f + l2 g := by
  have hfg : MemLp (fun x => f x + g x) 2 volume := hf.add hg
  have e : ∫ x, (f x + g x) ^ 2 = (∫ x, f x ^ 2) + 2 * (∫ x, f x * g x) + ∫ x, g x ^ 2 := by
    have i1 := hf.integrable_sq
    have i2 := hg.integrable_sq
    have i3 : Integrable (fun x => f x * g x) volume := hf.integrable_mul hg
    rw [show (fun x => (f x + g x) ^ 2) = fun x => (f x ^ 2 + 2 * (f x * g x)) + g x ^ 2 from by
      funext x; ring]
    have j1 : Integrable (fun x => f x ^ 2 + 2 * (f x * g x)) volume :=
      i1.add (i3.const_mul 2)
    rw [integral_add j1 i2, integral_add i1 (i3.const_mul 2), integral_const_mul]
  apply Real.sqrt_le_iff.2
  refine ⟨add_nonneg (l2_nonneg f) (l2_nonneg g), ?_⟩
  rw [e]
  have := abs_integral_mul_le_l2 hf hg
  have h5 := l2_sq f
  have h6 := l2_sq g
  nlinarith [le_abs_self (∫ x, f x * g x)]

theorem l2_const_mul (c : ℝ) (f : E → ℝ) : l2 (fun x => c * f x) = |c| * l2 f := by
  unfold l2
  have : ∫ x, (c * f x) ^ 2 = c ^ 2 * ∫ x, f x ^ 2 := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

theorem l2_neg (f : E → ℝ) : l2 (fun x => -f x) = l2 f := by
  have := l2_const_mul (-1) f
  simpa using this

theorem l2_comp_add (f : E → ℝ) (c : E) : l2 (fun x => f (x + c)) = l2 f := by
  unfold l2
  rw [integral_add_right_eq_self (μ := volume) (fun x => f x ^ 2) c]

theorem l2_dq_le {v : E} {h : ℝ} (hh : h ≠ 0) {f : E → ℝ} (hf : MemLp f 2 volume) :
    l2 (dq v h f) ≤ 2 * l2 f / |h| := by
  rw [dq_eq_mul, l2_const_mul]
  have h1 : l2 (fun x => f (x + h • v) - f x) ≤ 2 * l2 f := by
    have := l2_add_le (memLp_comp_add hf (h • v)) (f := fun x => f (x + h • v)) (g := fun x => -f x) hf.neg
    have e : (fun x => f (x + h • v) - f x) = fun x => f (x + h • v) + -f x := by
      funext x; ring
    rw [e]
    refine this.trans ?_
    have e2 : l2 (fun x => -f x) = l2 f := l2_neg f
    rw [e2, l2_comp_add]; linarith
  rw [abs_inv, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

theorem sq_intervalIntegral_le {a : ℝ → ℝ} (ha : Continuous a) :
    (∫ t in (0:ℝ)..1, a t) ^ 2 ≤ ∫ t in (0:ℝ)..1, a t ^ 2 := by
  set m := ∫ t in (0:ℝ)..1, a t with hm
  have i1 : IntervalIntegrable a MeasureTheory.volume 0 1 := ha.intervalIntegrable 0 1
  have i2 : IntervalIntegrable (fun t => a t ^ 2) MeasureTheory.volume 0 1 :=
    (ha.pow 2).intervalIntegrable 0 1
  have h0 : 0 ≤ ∫ t in (0:ℝ)..1, (a t - m) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun t _ => sq_nonneg _)
  have e : ∫ t in (0:ℝ)..1, (a t - m) ^ 2 = (∫ t in (0:ℝ)..1, a t ^ 2) - m ^ 2 := by
    have : (fun t => (a t - m) ^ 2) = fun t => (a t ^ 2 - (2 * m) * a t) + m ^ 2 := by
      funext t; ring
    rw [this, intervalIntegral.integral_add (i2.sub (i1.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_sub i2 (i1.const_mul _), intervalIntegral.integral_const_mul]
    simp [← hm]; ring
  linarith

theorem dq_eq_integral {F : E → ℝ} (hF : ContDiff ℝ ∞ F) (v : E) {h : ℝ} (hh : h ≠ 0) (x : E) :
    dq v h F x = ∫ t in (0:ℝ)..1, pd v F (x + t • (h • v)) := by
  have hd := hF.differentiable (by simp)
  have hder : ∀ t : ℝ, HasDerivAt (fun t : ℝ => F (x + t • (h • v)))
      (h * pd v F (x + t • (h • v))) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + t • (h • v)) (h • v) t := by
      simpa using ((hasDerivAt_id t).smul_const (h • v)).const_add x
    have := (hd (x + t • (h • v))).hasFDerivAt.comp_hasDerivAt t h1
    exact this.congr_deriv (by simp [pd])
  have hG : Continuous (pd v F) := by
    have : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by simp)
    exact this.clm_apply continuous_const
  have hcont : Continuous (fun t : ℝ => h * pd v F (x + t • (h • v))) := by fun_prop
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t)
    (hcont.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul] at this
  simp only [one_smul, zero_smul, add_zero] at this
  unfold dq
  rw [div_eq_iff hh, mul_comm]
  linarith

theorem integral_intervalIntegral_sq {G : E → ℝ} (hG : Continuous G) (hm : MemLp G 2 volume)
    (u : E) :
    Integrable (fun x => ∫ t in (0:ℝ)..1, G (x + t • u) ^ 2) volume ∧
      ∫ x, ∫ t in (0:ℝ)..1, G (x + t • u) ^ 2 = ∫ x, G x ^ 2 := by
  set ν : Measure ℝ := volume.restrict (Set.Ioc (0:ℝ) 1) with hν
  have : IsFiniteMeasure ν := ⟨by simp [hν]⟩
  have hf : Continuous (fun p : E × ℝ => G (p.1 + p.2 • u) ^ 2) := by fun_prop
  have hint : Integrable (fun p : E × ℝ => G (p.1 + p.2 • u) ^ 2) ((volume : Measure E).prod ν) := by
    rw [integrable_prod_iff' hf.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall (fun t => ?_), ?_⟩
    · exact (memLp_comp_add hm (t • u)).integrable_sq
    · have : (fun t : ℝ => ∫ x, ‖G (x + t • u) ^ 2‖) = fun _ => ∫ x, G x ^ 2 := by
        funext t
        simp only [norm_pow, Real.norm_eq_abs, sq_abs]
        exact integral_add_right_eq_self (μ := volume) (fun x => G x ^ 2) (t • u)
      simp only [this]
      exact integrable_const _
  have e1 : ∀ x, ∫ t in (0:ℝ)..1, G (x + t • u) ^ 2 = ∫ t, G (x + t • u) ^ 2 ∂ν := by
    intro x; rw [intervalIntegral.integral_of_le zero_le_one]
  simp only [e1]
  refine ⟨hint.integral_prod_left, ?_⟩
  rw [integral_integral_swap hint]
  have : ∀ t : ℝ, ∫ x, G (x + t • u) ^ 2 = ∫ x, G x ^ 2 := fun t =>
    integral_add_right_eq_self (μ := volume) (fun x => G x ^ 2) (t • u)
  simp only [this, integral_const, hν, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Ioc]
  simp

theorem integral_sq_dq_le_smooth {F : E → ℝ} (hF : ContDiff ℝ ∞ F) (v : E) {h : ℝ} (hh : h ≠ 0)
    (hFm : MemLp F 2 volume) (hG : MemLp (pd v F) 2 volume) :
    ∫ x, dq v h F x ^ 2 ≤ ∫ x, pd v F x ^ 2 := by
  have hGc : Continuous (pd v F) := by
    have : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by simp)
    exact this.clm_apply continuous_const
  obtain ⟨hi, he⟩ := integral_intervalIntegral_sq hGc hG (h • v)
  have hl : Integrable (fun x => dq v h F x ^ 2) volume := (memLp_dq hFm).integrable_sq
  rw [← he]
  refine integral_mono hl hi (fun x => ?_)
  simp only
  rw [dq_eq_integral hF v hh x]
  exact sq_intervalIntegral_le (a := fun t => pd v F (x + t • (h • v))) (by fun_prop)

/-- `‖D_h f‖₂ ≤ ‖∂_v f‖₂`. -/
theorem l2_dq_le_l2_deriv {v : E} {h : ℝ} (hh : h ≠ 0) {f w : E → ℝ} (hf : MemLp f 2 volume)
    (hw : MemLp w 2 volume) (H : HasWDeriv Set.univ v f w) : l2 (dq v h f) ≤ l2 w := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := fun n => by positivity
  have hfl : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  have key : ∀ n, l2 (dq v h f) ≤ l2 w + 2 / |h| *
      Real.sqrt (∫ x, (mol (ε n) (hε n) f x - f x) ^ 2) := by
    intro n
    set fn := mol (ε n) (hε n) f with hfn
    have hfnc : ContDiff ℝ ∞ fn := mol_contDiff _ _ hfl
    have hpd : pd v fn = mol (ε n) (hε n) w := by
      funext x; exact fderiv_mol _ _ H x
    have hmfn : MemLp fn 2 volume := memLp_mol _ _ hf
    have hmw : MemLp (mol (ε n) (hε n) w) 2 volume := memLp_mol _ _ hw
    have h1 : l2 (dq v h fn) ≤ l2 w := by
      have := integral_sq_dq_le_smooth hfnc v hh hmfn (hpd ▸ hmw)
      rw [hpd] at this
      exact Real.sqrt_le_sqrt (this.trans (integral_sq_mol_le _ _ hw))
    have h2 : l2 (dq v h (fun x => f x - fn x)) ≤ 2 * l2 (fun x => f x - fn x) / |h| :=
      l2_dq_le hh (hf.sub hmfn)
    have h3 : l2 (dq v h f) ≤ l2 (dq v h fn) + l2 (dq v h (fun x => f x - fn x)) := by
      have := l2_add_le (memLp_dq (v := v) (h := h) hmfn) (memLp_dq (v := v) (h := h) (hf.sub hmfn))
      have e : dq v h f = fun x => dq v h fn x + dq v h (fun x => f x - fn x) x := by
        funext x; unfold dq; ring
      rw [e]; exact this
    have h4 : l2 (fun x => f x - fn x) = Real.sqrt (∫ x, (fn x - f x) ^ 2) := by
      unfold l2; congr 1; congr 1; funext x; ring
    calc l2 (dq v h f) ≤ _ := h3
      _ ≤ l2 w + 2 / |h| * Real.sqrt (∫ x, (fn x - f x) ^ 2) := by
        rw [← h4]
        have : 2 * l2 (fun x => f x - fn x) / |h| = 2 / |h| * l2 (fun x => f x - fn x) := by ring
        linarith
  have hlim : Filter.Tendsto (fun n : ℕ => l2 w + 2 / |h| *
      Real.sqrt (∫ x, (mol (ε n) (hε n) f x - f x) ^ 2)) Filter.atTop (nhds (l2 w)) := by
    have h0 := (Real.continuous_sqrt.tendsto 0).comp (tendsto_integral_sq_mol_sub f hf)
    simp only [Real.sqrt_zero] at h0
    have := (h0.const_mul (2 / |h|)).const_add (l2 w)
    rw [mul_zero, add_zero] at this
    exact this
  exact ge_of_tendsto' hlim key

end CutoffRigidity.Riemann.Diff
