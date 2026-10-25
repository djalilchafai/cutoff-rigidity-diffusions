module

public import CutoffRigidity.TransportMoments
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.LpOrder

/-!
# Finite-time L² maximal inequality

A genuine nonnegative discrete submartingale has squared running maximum
expectation at most four times its terminal second moment. The proof uses
adapted running-maximum increments and conditional-expectation pull-out,
followed by Cauchy--Schwarz. This supplies the missing Brownian supremum
moment backend; it does not assume a maximal moment estimate.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

@[expose] noncomputable def finiteRunningMaximum (f : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => f 0
  | n + 1 => fun ω => max (finiteRunningMaximum f n ω) (f (n + 1) ω)

omit [IsProbabilityMeasure μ] in
/-- Square integrability of a finite maximum follows from that of its entries. -/
theorem finiteRunningMaximum_memLp {f : ℕ → Ω → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (n : ℕ) : MemLp (finiteRunningMaximum f n) 2 μ := by
  induction n with
  | zero => exact hf 0
  | succ n ih => exact ih.sup (hf (n + 1))

/-- A finite running maximum is adapted to the same filtration. -/
theorem finiteRunningMaximum_stronglyMeasurable {f : ℕ → Ω → ℝ}
    {ℱ : Filtration ℕ ‹MeasurableSpace Ω›} (hf : StronglyAdapted ℱ f) (n : ℕ) :
    StronglyMeasurable[ℱ n] (finiteRunningMaximum f n) := by
  induction n with
  | zero => exact hf 0
  | succ n ih => exact ((ih.mono (ℱ.mono (Nat.le_succ n))).measurable.max (hf (n + 1)).measurable).stronglyMeasurable

omit [MeasurableSpace Ω] in
/-- The running maximum remains nonnegative. -/
theorem finiteRunningMaximum_nonneg {f : ℕ → Ω → ℝ} (hf : 0 ≤ f) (n : ℕ) (ω : Ω) :
    0 ≤ finiteRunningMaximum f n ω := by
  induction n with
  | zero => exact hf 0 ω
  | succ n ih => exact ih.trans (le_max_left _ _)

/-- Multiplication by any adapted nonnegative L² variable preserves the
submartingale expectation inequality up to a later deterministic time. -/
theorem submartingale_integral_mul_le {f : ℕ → Ω → ℝ}
    {ℱ : Filtration ℕ ‹MeasurableSpace Ω›} (hf : Submartingale f ℱ μ)
    (hL : ∀ n, MemLp (f n) 2 μ) {i n : ℕ} (hin : i ≤ n)
    {g : Ω → ℝ} (hg : StronglyMeasurable[ℱ i] g) (hgL : MemLp g 2 μ)
    (hgn : ∀ ω, 0 ≤ g ω) :
    (∫ ω, f i ω * g ω ∂μ) ≤ ∫ ω, f n ω * g ω ∂μ := by
  have hfg := (hL n).integrable_mul hgL
  have hpull := condExp_mul_of_stronglyMeasurable_right hg hfg (hf.integrable n)
  have hce : Integrable (fun ω => (μ[f n | ℱ i]) ω * g ω) μ :=
    integrable_condExp.congr hpull
  calc
    _ ≤ ∫ ω, (μ[f n | ℱ i]) ω * g ω ∂μ := by
      apply integral_mono_ae ((hL i).integrable_mul hgL) hce
      filter_upwards [hf.ae_le_condExp hin] with ω hω
      exact mul_le_mul_of_nonneg_right hω (hgn ω)
    _ = ∫ ω, f n ω * g ω ∂μ := by
      exact (integral_congr_ae hpull).symm.trans (integral_condExp (ℱ.le i))

/-- Pointwise energy estimate for one running-maximum update. -/
theorem max_sq_update_le (a b : ℝ) :
    max a b ^ 2 ≤ a ^ 2 + 2 * b * (max a b - a) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]
    nlinarith [sq_nonneg (b - a)]
  · rw [max_eq_left h]
    simp

/-- The conditional-expectation part of Doob's L² inequality, before
Cauchy--Schwarz. -/
theorem integral_finiteRunningMaximum_sq_le_cross {f : ℕ → Ω → ℝ}
    {ℱ : Filtration ℕ ‹MeasurableSpace Ω›} (hf : Submartingale f ℱ μ)
    (hL : ∀ n, MemLp (f n) 2 μ) (hn : 0 ≤ f) (N : ℕ) :
    (∫ ω, finiteRunningMaximum f N ω ^ 2 ∂μ) ≤
      2 * ∫ ω, f N ω * finiteRunningMaximum f N ω ∂μ := by
  have hstep : ∀ k, k ≤ N →
      (∫ ω, finiteRunningMaximum f k ω ^ 2 ∂μ) ≤
        2 * ∫ ω, f N ω * finiteRunningMaximum f k ω ∂μ := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h := submartingale_integral_mul_le hf hL hk (hf.stronglyAdapted 0) (hL 0) (hn 0)
      have hp : 0 ≤ ∫ ω, f 0 ω ^ 2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
      change (∫ ω, f 0 ω ^ 2 ∂μ) ≤ 2 * ∫ ω, f N ω * f 0 ω ∂μ
      simp only [← pow_two] at h
      linarith
    | succ k ih =>
      intro hk
      have hkN : k ≤ N := (Nat.le_succ k).trans hk
      let M := finiteRunningMaximum f
      let g : Ω → ℝ := fun ω => M (k + 1) ω - M k ω
      have hMk := finiteRunningMaximum_memLp hL k
      have hMk1 := finiteRunningMaximum_memLp hL (k + 1)
      have hgL : MemLp g 2 μ := hMk1.sub hMk
      have hg : StronglyMeasurable[ℱ (k + 1)] g :=
        (finiteRunningMaximum_stronglyMeasurable hf.stronglyAdapted (k + 1)).sub
          ((finiteRunningMaximum_stronglyMeasurable hf.stronglyAdapted k).mono
            (ℱ.mono (Nat.le_succ k)))
      have hgn : ∀ ω, 0 ≤ g ω := fun ω => sub_nonneg.mpr (le_max_left _ _)
      have hcross := submartingale_integral_mul_le hf hL hk hg hgL hgn
      have hupdate : (∫ ω, M (k + 1) ω ^ 2 ∂μ) ≤
          (∫ ω, M k ω ^ 2 ∂μ) + 2 * ∫ ω, f (k + 1) ω * g ω ∂μ := by
        have hs : (∫ ω, M k ω ^ 2 + 2 * (f (k + 1) ω * g ω) ∂μ) =
            (∫ ω, M k ω ^ 2 ∂μ) + 2 * ∫ ω, f (k + 1) ω * g ω ∂μ := by
          calc
            _ = (∫ ω, M k ω ^ 2 ∂μ) + ∫ ω, 2 * (f (k + 1) ω * g ω) ∂μ :=
              integral_add hMk.integrable_sq (((hL (k + 1)).integrable_mul hgL).const_mul 2)
            _ = _ := by rw [integral_const_mul]
        rw [← hs]
        exact integral_mono hMk1.integrable_sq
          (hMk.integrable_sq.add (((hL (k + 1)).integrable_mul hgL).const_mul 2))
          (fun ω => by simpa only [M, g, finiteRunningMaximum, mul_assoc] using
            max_sq_update_le (M k ω) (f (k + 1) ω))
      have hsum : (∫ ω, f N ω * M (k + 1) ω ∂μ) =
          (∫ ω, f N ω * M k ω ∂μ) + ∫ ω, f N ω * g ω ∂μ := by
        calc
          _ = ∫ ω, f N ω * M k ω + f N ω * g ω ∂μ := by
            apply integral_congr_ae
            exact Eventually.of_forall (fun ω => by dsimp [g]; ring)
          _ = _ := integral_add ((hL N).integrable_mul hMk) ((hL N).integrable_mul hgL)
      have hprev := ih hkN
      change (∫ ω, M k ω ^ 2 ∂μ) ≤ 2 * ∫ ω, f N ω * M k ω ∂μ at hprev
      change (∫ ω, M (k + 1) ω ^ 2 ∂μ) ≤ 2 * ∫ ω, f N ω * M (k + 1) ω ∂μ
      linarith
  exact hstep N le_rfl

/-- Doob's finite-time L² maximal inequality for an actual nonnegative
submartingale. The constant four is independent of the grid size. -/
theorem integral_finiteRunningMaximum_sq_le_four {f : ℕ → Ω → ℝ}
    {ℱ : Filtration ℕ ‹MeasurableSpace Ω›} (hf : Submartingale f ℱ μ)
    (hL : ∀ n, MemLp (f n) 2 μ) (hn : 0 ≤ f) (N : ℕ) :
    (∫ ω, finiteRunningMaximum f N ω ^ 2 ∂μ) ≤ 4 * ∫ ω, f N ω ^ 2 ∂μ := by
  have h := integral_finiteRunningMaximum_sq_le_cross hf hL hn N
  have hcs := integral_mul_le_second_moments (hL N) (finiteRunningMaximum_memLp hL N)
  have ha := Real.sqrt_nonneg (∫ ω, finiteRunningMaximum f N ω ^ 2 ∂μ)
  have hb := Real.sqrt_nonneg (∫ ω, f N ω ^ 2 ∂μ)
  have ha2 := Real.sq_sqrt (integral_nonneg (μ := μ) (fun ω => sq_nonneg (finiteRunningMaximum f N ω)))
  have hb2 := Real.sq_sqrt (integral_nonneg (μ := μ) (fun ω => sq_nonneg (f N ω)))
  have hroot : Real.sqrt (∫ ω, finiteRunningMaximum f N ω ^ 2 ∂μ) ≤
      2 * Real.sqrt (∫ ω, f N ω ^ 2 ∂μ) := by nlinarith
  nlinarith [mul_self_le_mul_self ha hroot]

end CutoffRigidity
