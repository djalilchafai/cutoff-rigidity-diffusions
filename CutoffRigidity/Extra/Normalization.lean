module

public import CutoffRigidity.Paper.CarrierDefs
public import CutoffRigidity.Paper.ProductCondition

/-! # Normalization by time change (manuscript, Section 4.2)

For `α > 0` (possibly depending on the dimension), the time-changed process
`X^{(α)}_t = X_{αt}` has cutoff at `t_*/α` iff `X` has cutoff at `t_*`, the mixing time scales as
`t₀/α` and the product condition `κ t₀ → ∞` is invariant (`κ` becomes `α κ`).
-/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

section Generic

/-- Generic form: cutoff of a profile is invariant under `profile ↦ profile(α ·)`,
`t ↦ t/α`. -/
theorem hasCutoff_timeChange {profile : ℕ → ℝ → ℝ≥0∞} {α t : ℕ → ℝ} (hα : ∀ n, 0 < α n)
    {b a : ℝ≥0∞} :
    CutCur.HasCutoff profile t b a ↔
      CutCur.HasCutoff (fun n s => profile n (α n * s)) (fun n => t n / α n) b a := by
  have key : ∀ (n : ℕ) (c : ℝ), α n * (c * (t n / α n)) = c * t n := fun n c => by
    have := (hα n).ne'
    field_simp
  unfold CutCur.HasCutoff
  simp only [key]

end Generic

section Processes

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The worst-case profile of the time-changed process is the time-changed worst-case profile. -/
theorem worst_timeChange (P : Measure Ω) (X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d)
    (S : Set (CutCur.Rd d)) (δ : Measure (CutCur.Rd d) → ℝ≥0∞) {α : ℝ} (hα : 0 < α) (s : ℝ) :
    CutCur.worst P (fun x₀ u => X x₀ (α.toNNReal * u)) S δ s = CutCur.worst P X S δ (α * s) := by
  unfold CutCur.worst
  rw [Real.toNNReal_mul hα.le]

/-- The mixing time of the time-changed process is `t₀/α`. -/
theorem mixingTime_timeChange (P : Measure Ω) (X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d)
    (μ : Measure (CutCur.Rd d)) (S : Set (CutCur.Rd d)) (η : ℝ) {α : ℝ} (hα : 0 < α) :
    CutCur.mixingTime P (fun x₀ u => X x₀ (α.toNNReal * u)) μ S η =
      CutCur.mixingTime P X μ S η / ENNReal.ofReal α := by
  have hne : α.toNNReal ≠ 0 := by simpa using hα
  have hcoe : ENNReal.ofReal α = (α.toNNReal : ℝ≥0∞) := rfl
  rw [hcoe]
  have hne' : (α.toNNReal : ℝ≥0∞) ≠ 0 := by exact_mod_cast hne
  rw [ENNReal.eq_div_iff hne' ENNReal.coe_ne_top]
  unfold CutCur.mixingTime
  simp only [ENNReal.mul_iInf_of_ne hne' ENNReal.coe_ne_top]
  have h2 := (Equiv.mulLeft₀ α.toNNReal hne).iInf_comp
    (g := fun u : ℝ≥0 => ⨅ (_ : CutCur.worst P X S (fun ν => ENNReal.ofReal (CutCur.tvDist ν μ)) u ≤
      ENNReal.ofReal η), (u : ℝ≥0∞))
  rw [← h2]
  refine iInf_congr fun t => ?_
  have hw : CutCur.worst P (fun x₀ u => X x₀ (α.toNNReal * u)) S
      (fun ν => ENNReal.ofReal (CutCur.tvDist ν μ)) t =
      CutCur.worst P X S (fun ν => ENNReal.ofReal (CutCur.tvDist ν μ)) ((α.toNNReal * t : ℝ≥0) : ℝ) := by
    rw [worst_timeChange P X S _ hα]
    congr 1
    rw [NNReal.coe_mul, Real.coe_toNNReal _ hα.le]
  simp only [Equiv.mulLeft₀_apply]
  rw [hw]
  refine iInf_congr fun h => ?_
  simp

end Processes

/-- **Normalization** (manuscript, Section "Normalization"): for `α_d > 0` (possibly depending on
the dimension), the time-changed processes `X^{(α)}_t = X_{αt}` satisfy: cutoff of every
worst-case profile at `t_*` for `X` is equivalent to cutoff at `t_*/α` for `X^{(α)}`
(same limits before and after); the mixing time of `X^{(α)}` is `t₀/α`; and the product condition
`κ t₀ → ∞` of Theorem 1.7 is invariant, `κ` being replaced by `α κ` (the curvature of the
generator `α 𝓛`). -/
theorem normalization_cutoff_carrier {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)}
    {X : ∀ n, CutCur.Rd n → ℝ≥0 → Ω n → CutCur.Rd n} {S : ∀ n, Set (CutCur.Rd n)}
    {α : ℕ → ℝ} (hα : ∀ n, 0 < α n) :
    let Xα := fun n (x₀ : CutCur.Rd n) (u : ℝ≥0) => X n x₀ ((α n).toNNReal * u)
    (∀ (δ : ∀ n, Measure (CutCur.Rd n) → ℝ≥0∞) (t : ℕ → ℝ) (b a : ℝ≥0∞),
      CutCur.HasCutoff (fun n => CutCur.worst (P n) (X n) (S n) (δ n)) t b a ↔
        CutCur.HasCutoff (fun n => CutCur.worst (P n) (Xα n) (S n) (δ n))
          (fun n => t n / α n) b a) ∧
    (∀ (μ : ∀ n, Measure (CutCur.Rd n)) (η : ℝ) (n : ℕ),
      CutCur.mixingTime (P n) (Xα n) (μ n) (S n) η =
        CutCur.mixingTime (P n) (X n) (μ n) (S n) η / ENNReal.ofReal (α n)) ∧
    (∀ (μ : ∀ n, Measure (CutCur.Rd n)) (η : ℝ) (κ : ℕ → ℝ),
      Tendsto (fun n => α n * κ n * (CutCur.mixingTime (P n) (Xα n) (μ n) (S n) η).toReal)
          atTop atTop ↔
        Tendsto (fun n => κ n * (CutCur.mixingTime (P n) (X n) (μ n) (S n) η).toReal)
          atTop atTop) := by
  intro Xα
  refine ⟨fun δ t b a => ?_, fun μ η n => mixingTime_timeChange _ _ _ _ _ (hα n), fun μ η κ => ?_⟩
  · have h := hasCutoff_timeChange (profile := fun n => CutCur.worst (P n) (X n) (S n) (δ n))
      (t := t) hα (b := b) (a := a)
    rw [h]
    have : ∀ n, CutCur.worst (P n) (Xα n) (S n) (δ n) =
        fun s => CutCur.worst (P n) (X n) (S n) (δ n) (α n * s) := fun n =>
      funext fun s => worst_timeChange _ _ _ _ (hα n) s
    simp only [this]
  · have : ∀ n, α n * κ n * (CutCur.mixingTime (P n) (Xα n) (μ n) (S n) η).toReal =
        κ n * (CutCur.mixingTime (P n) (X n) (μ n) (S n) η).toReal := by
      intro n
      rw [mixingTime_timeChange _ _ _ _ _ (hα n), ENNReal.toReal_div,
        ENNReal.toReal_ofReal (hα n).le]
      have := (hα n).ne'
      field_simp
    simp only [this]

end CutoffRigidity.Paper
