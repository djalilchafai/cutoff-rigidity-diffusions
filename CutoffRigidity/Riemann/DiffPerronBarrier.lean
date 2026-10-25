module

public import CutoffRigidity.Riemann.DiffPerron0
public import CutoffRigidity.Riemann.DiffPerron1

/-! # The exponential barrier (workstream PENAL, P2b)

Pointwise barrier algebra for `ψ = exp(-s · S(ζ - a - 1))`, `S = Real.smoothTransition`:
`(lam + K S(ζ-a) - 𝓛) ψ ≥ 0` everywhere once `K ≥ s²B²G + sB(Λ + G)` (CO_PLAN 2.2 step 5).
-/

@[expose] public section

open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal Topology NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur CutoffRigidity.Riemann

section Real1D

private theorem zero_of_zero_Iio {h : ℝ → ℝ} (hc : Continuous h) (h0 : ∀ t, t < 0 → h t = 0) :
    ∀ t, t ≤ 0 → h t = 0 := by
  intro t ht
  have : closure (Iio (0:ℝ)) ⊆ {x | h x = 0} :=
    closure_minimal (fun x hx => h0 x hx) (isClosed_eq hc continuous_const)
  rw [closure_Iio] at this
  exact this ht

private theorem zero_of_zero_Ioi {h : ℝ → ℝ} (hc : Continuous h) (h0 : ∀ t, 1 < t → h t = 0) :
    ∀ t, 1 ≤ t → h t = 0 := by
  intro t ht
  have : closure (Ioi (1:ℝ)) ⊆ {x | h x = 0} :=
    closure_minimal (fun x hx => h0 x hx) (isClosed_eq hc continuous_const)
  rw [closure_Ioi] at this
  exact this ht

private theorem bound_of_zero {h : ℝ → ℝ} (hc : Continuous h) (h0 : ∀ t, t ≤ 0 ∨ 1 ≤ t → h t = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |h t| ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc (0:ℝ) 1
  · have := hB t ht
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · have : t ≤ 0 ∨ 1 ≤ t := by
      simp only [mem_Icc, not_and_or, not_le] at ht
      rcases ht with h1 | h1
      · exact Or.inl h1.le
      · exact Or.inr h1.le
    rw [h0 t this]; simp

/-- Derivative facts of the smooth step. -/
theorem smoothTransition_deriv_facts : ∃ B : ℝ, 0 ≤ B ∧
    (∀ t, |deriv Real.smoothTransition t| ≤ B ∧ |deriv (deriv Real.smoothTransition) t| ≤ B) ∧
    (∀ t, t ≤ 0 ∨ 1 ≤ t →
      deriv Real.smoothTransition t = 0 ∧ deriv (deriv Real.smoothTransition) t = 0) := by
  have hS : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have h1 : ContDiff ℝ ∞ (deriv Real.smoothTransition) := (contDiff_infty_iff_deriv.1 hS).2
  have h2 : ContDiff ℝ ∞ (deriv (deriv Real.smoothTransition)) :=
    (contDiff_infty_iff_deriv.1 h1).2
  have d1 : ∀ t, t < 0 → deriv Real.smoothTransition t = 0 := by
    intro t ht
    have : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with y hy
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [this.deriv_eq]; simp
  have d1' : ∀ t, 1 < t → deriv Real.smoothTransition t = 0 := by
    intro t ht
    have : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1:ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with y hy
      exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
    rw [this.deriv_eq]; simp
  have e1 := zero_of_zero_Iio h1.continuous d1
  have e1' := zero_of_zero_Ioi h1.continuous d1'
  have d2 : ∀ t, t < 0 → deriv (deriv Real.smoothTransition) t = 0 := by
    intro t ht
    have : deriv Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with y hy
      exact d1 y hy
    rw [this.deriv_eq]; simp
  have d2' : ∀ t, 1 < t → deriv (deriv Real.smoothTransition) t = 0 := by
    intro t ht
    have : deriv Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with y hy
      exact d1' y hy
    rw [this.deriv_eq]; simp
  have f1 := zero_of_zero_Iio h2.continuous d2
  have f1' := zero_of_zero_Ioi h2.continuous d2'
  have z : ∀ t, t ≤ 0 ∨ 1 ≤ t →
      deriv Real.smoothTransition t = 0 ∧ deriv (deriv Real.smoothTransition) t = 0 := by
    intro t ht
    rcases ht with ht | ht
    · exact ⟨e1 t ht, f1 t ht⟩
    · exact ⟨e1' t ht, f1' t ht⟩
  obtain ⟨B1, hB1, hb1⟩ := bound_of_zero h1.continuous (fun t ht => (z t ht).1)
  obtain ⟨B2, hB2, hb2⟩ := bound_of_zero h2.continuous (fun t ht => (z t ht).2)
  exact ⟨max B1 B2, (hB1.trans (le_max_left _ _)),
    fun t => ⟨(hb1 t).trans (le_max_left _ _), (hb2 t).trans (le_max_right _ _)⟩, z⟩

/-- The barrier profile `θ t = exp(-s S(t - (a+1)))` and its derivatives. -/
noncomputable def barrierProfile (s a : ℝ) (t : ℝ) : ℝ :=
  Real.exp (-s * Real.smoothTransition (t - (a + 1)))

theorem contDiff_barrierProfile (s a : ℝ) : ContDiff ℝ ∞ (barrierProfile s a) := by
  unfold barrierProfile
  exact (Real.contDiff_exp.comp (contDiff_const.mul
    (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))))

theorem deriv_barrierProfile (s a t : ℝ) :
    deriv (barrierProfile s a) t =
      -s * deriv Real.smoothTransition (t - (a + 1)) * barrierProfile s a t := by
  have hS : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have h1 : HasDerivAt (fun t : ℝ => Real.smoothTransition (t - (a + 1)))
      (deriv Real.smoothTransition (t - (a + 1))) t := by
    have := ((hS.differentiable (by simp)) (t - (a+1))).hasDerivAt.comp t
      ((hasDerivAt_id t).sub_const (a + 1))
    rw [mul_one] at this
    exact this
  have h2 := (h1.const_mul (-s)).exp
  unfold barrierProfile
  rw [h2.deriv]
  ring

theorem deriv_deriv_barrierProfile (s a t : ℝ) :
    deriv (deriv (barrierProfile s a)) t =
      (s ^ 2 * deriv Real.smoothTransition (t - (a + 1)) ^ 2 -
        s * deriv (deriv Real.smoothTransition) (t - (a + 1))) * barrierProfile s a t := by
  have hS : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hS1 : ContDiff ℝ ∞ (deriv Real.smoothTransition) := (contDiff_infty_iff_deriv.1 hS).2
  have e : deriv (barrierProfile s a) = fun t =>
      -s * deriv Real.smoothTransition (t - (a + 1)) * barrierProfile s a t := funext
    (deriv_barrierProfile s a)
  have h1 : HasDerivAt (fun t : ℝ => deriv Real.smoothTransition (t - (a + 1)))
      (deriv (deriv Real.smoothTransition) (t - (a + 1))) t := by
    have := ((hS1.differentiable (by simp)) (t - (a+1))).hasDerivAt.comp t
      ((hasDerivAt_id t).sub_const (a + 1))
    rw [mul_one] at this
    exact this
  have h2 : HasDerivAt (barrierProfile s a) (deriv (barrierProfile s a) t) t :=
    (((contDiff_barrierProfile s a).differentiable (by simp)) t).hasDerivAt
  have h3 := (h1.const_mul (-s)).mul h2
  have h3' : HasDerivAt (fun t => -s * deriv Real.smoothTransition (t - (a + 1)) *
      barrierProfile s a t) _ t := h3
  rw [e, h3'.deriv, deriv_barrierProfile]
  ring

theorem barrierProfile_pos (s a t : ℝ) : 0 < barrierProfile s a t := Real.exp_pos _

theorem barrierProfile_le_one {s : ℝ} (hs : 0 ≤ s) (a t : ℝ) : barrierProfile s a t ≤ 1 := by
  unfold barrierProfile
  rw [Real.exp_le_one_iff]
  have := Real.smoothTransition.nonneg (t - (a + 1))
  nlinarith

theorem barrierProfile_eq_one {s : ℝ} (a t : ℝ) (ht : t ≤ a + 1) : barrierProfile s a t = 1 := by
  unfold barrierProfile
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]; simp

theorem barrierProfile_eq_exp {s : ℝ} (a t : ℝ) (ht : a + 2 ≤ t) :
    barrierProfile s a t = Real.exp (-s) := by
  unfold barrierProfile
  rw [Real.smoothTransition.one_of_one_le (by linarith)]; simp

end Real1D

section Pointwise

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  {V : M → ℝ}

/-- **Barrier algebra**, pointwise: `(lam + κ - 𝓛) ψ ≥ 0` for `ψ = θ ∘ ζ`. -/
theorem barrier_supersolution {ζ : M → ℝ} (hζ : MSmooth F ζ) {lam : ℝ} (hlam : 0 < lam)
    {a s K B G Λ : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hB : ∀ t, |deriv Real.smoothTransition t| ≤ B ∧ |deriv (deriv Real.smoothTransition) t| ≤ B)
    (hB0 : 0 ≤ B)
    (hz : ∀ t, t ≤ 0 ∨ 1 ≤ t →
      deriv Real.smoothTransition t = 0 ∧ deriv (deriv Real.smoothTransition) t = 0)
    (hG : ∀ x, ζ x ≤ a + 2 → carre F ζ ζ x ≤ G)
    (hΛ : ∀ x, ζ x ≤ a + 2 → |mgenerator F V ζ x| ≤ Λ)
    (hKK : s ^ 2 * B ^ 2 * G + s * B * Λ + s * B * G ≤ K) (x : M) :
    0 ≤ (lam + K * Real.smoothTransition (ζ x - a)) * barrierProfile s a (ζ x) -
      mgenerator F V (barrierProfile s a ∘ ζ) x := by
  rw [mgenerator_comp_real F (contDiff_barrierProfile s a) hζ x, deriv_barrierProfile,
    deriv_deriv_barrierProfile]
  set E := barrierProfile s a (ζ x) with hE
  have hEpos : 0 < E := barrierProfile_pos s a _
  set p := deriv Real.smoothTransition (ζ x - (a + 1))
  set q := deriv (deriv Real.smoothTransition) (ζ x - (a + 1))
  set Γ := carre F ζ ζ x
  set L := mgenerator F V ζ x
  have hΓ : 0 ≤ Γ := carre_nonneg F ζ x
  have key : 0 ≤ lam + K * Real.smoothTransition (ζ x - a) + s * p * L - s ^ 2 * p ^ 2 * Γ +
      s * q * Γ := by
    by_cases hsh : ζ x - (a + 1) ≤ 0 ∨ 1 ≤ ζ x - (a + 1)
    · obtain ⟨hp, hq⟩ := hz _ hsh
      rw [show p = 0 from hp, show q = 0 from hq]
      have := Real.smoothTransition.nonneg (ζ x - a)
      nlinarith [mul_nonneg hK this]
    · push Not at hsh
      have hle : ζ x ≤ a + 2 := by linarith [hsh.2]
      have hS1 : Real.smoothTransition (ζ x - a) = 1 :=
        Real.smoothTransition.one_of_one_le (by linarith [hsh.1])
      rw [hS1]
      have hp := (hB (ζ x - (a + 1))).1
      have hq := (hB (ζ x - (a + 1))).2
      have hGx := hG x hle
      have hLx := hΛ x hle
      have h1 : |p * L| ≤ B * Λ := by
        rw [abs_mul]; exact mul_le_mul hp hLx (abs_nonneg _) hB0
      have h2 : p ^ 2 * Γ ≤ B ^ 2 * G := by
        have : p ^ 2 ≤ B ^ 2 := by
          rw [← sq_abs p]; exact pow_le_pow_left₀ (abs_nonneg _) hp 2
        exact mul_le_mul this hGx hΓ (sq_nonneg _)
      have h3 : |q * Γ| ≤ B * G := by
        rw [abs_mul, abs_of_nonneg hΓ]; exact mul_le_mul hq hGx hΓ hB0
      have h1' := (abs_le.1 h1).1
      have h3' := (abs_le.1 h3).1
      have e1 : s * (B * Λ) ≥ -(s * (p * L)) := by nlinarith
      have e3 : s * (q * Γ) ≥ -(s * (B * G)) := by nlinarith
      have e2 : s ^ 2 * (p ^ 2 * Γ) ≤ s ^ 2 * (B ^ 2 * G) := by gcongr
      nlinarith
  have : (lam + K * Real.smoothTransition (ζ x - a)) * E -
      (-s * p * E * L + (s ^ 2 * p ^ 2 - s * q) * E * Γ) =
      E * (lam + K * Real.smoothTransition (ζ x - a) + s * p * L - s ^ 2 * p ^ 2 * Γ +
      s * q * Γ) := by ring
  rw [this]
  exact mul_nonneg hEpos.le key

end Pointwise

section Decay

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  {V : M → ℝ} (hV : MSmooth F V)

/-- Energy maximum principle in the shape consumed by the barrier. -/
def MaxPrinciple (lam : ℝ) : Prop :=
  ∀ {κ : M → ℝ}, (∀ x, 0 ≤ κ x) → ∀ w : M → ℝ, MSmooth F w → (∃ C, ∀ x, |w x| ≤ C) →
    (∀ x, 0 < w x → (lam + κ x) * w x ≤ mgenerator F V w x) → ∀ x, w x ≤ 0

include hV in
/-- Barrier decay, given the maximum principle. -/
theorem barrier_decay_of_MP {ζ : M → ℝ} (hζ : MSmooth F ζ) (hζc : ∀ c, IsCompact {x | ζ x ≤ c})
    {lam : ℝ} (hlam : 0 < lam) (hMP : MaxPrinciple (F := F) (V := V) lam) (Cg a : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ K₀ : ℝ, ∀ K ≥ K₀, ∀ (g v : M → ℝ), MSmooth F v → (∀ x, 0 ≤ g x ∧ g x ≤ Cg) →
      (∀ x, g x ≠ 0 → ζ x < a) → (∀ x, 0 ≤ v x ∧ v x ≤ Cg / lam) →
      (∀ x, mgenerator F V v x =
        (lam + K * Real.smoothTransition (ζ x - a)) * v x - g x) →
      ∀ x, a + 2 ≤ ζ x → v x ≤ ε := by
  obtain ⟨B, hB0, hB, hz⟩ := smoothTransition_deriv_facts
  have hΓc : Continuous (carre F ζ ζ) := ((weightedRegular V hV).1 ζ ζ hζ hζ).continuous
  have hLc : Continuous (mgenerator F V ζ) := (msmooth_mgenerator F hV hζ).continuous
  obtain ⟨G0, hG0⟩ := (hζc (a + 2)).exists_bound_of_continuousOn hΓc.continuousOn
  obtain ⟨Λ0, hΛ0⟩ := (hζc (a + 2)).exists_bound_of_continuousOn hLc.continuousOn
  set G := max G0 0 with hG
  set Λ := max Λ0 0 with hΛ
  have hG0' : 0 ≤ G := le_max_right _ _
  have hΛ0' : 0 ≤ Λ := le_max_right _ _
  set C := max Cg 0 / lam with hC
  have hC0 : 0 ≤ C := div_nonneg (le_max_right _ _) hlam.le
  set s := C / ε with hs
  have hs0 : 0 ≤ s := div_nonneg hC0 hε.le
  refine ⟨s ^ 2 * B ^ 2 * G + s * B * Λ + s * B * G, fun K hK g v hv hg hga hv01 heq x hx => ?_⟩
  have hKK : s ^ 2 * B ^ 2 * G + s * B * Λ + s * B * G ≤ K := hK
  have hK0 : 0 ≤ K := le_trans (by positivity) hKK
  have hψ : MSmooth F (barrierProfile s a ∘ ζ) :=
    (contDiff_barrierProfile s a).contMDiff.comp hζ
  have hsup := barrier_supersolution F (V := V) hζ hlam hs0 hK0 hB hB0 hz
    (fun y hy => by have := hG0 y hy; rw [Real.norm_eq_abs] at this
                    exact (le_abs_self _).trans (this.trans (le_max_left _ _)))
    (fun y hy => by have := hΛ0 y hy; rw [Real.norm_eq_abs] at this
                    exact this.trans (le_max_left _ _)) hKK
  have hCg : Cg / lam ≤ C := div_le_div_of_nonneg_right (le_max_left _ _) hlam.le
  have hw : MSmooth F (fun y => v y + (-C) * (barrierProfile s a ∘ ζ) y) :=
    hv.add (contMDiff_const.mul hψ)
  have hLw : ∀ y, mgenerator F V (fun y => v y + (-C) * (barrierProfile s a ∘ ζ) y) y =
      mgenerator F V v y + (-C) * mgenerator F V (barrierProfile s a ∘ ζ) y := by
    intro y
    have hψc : MSmooth F (fun y => (-C) * (barrierProfile s a ∘ ζ) y) :=
      contMDiff_const.mul hψ
    rw [mgenerator_add F hv hψc, mgenerator_const_mul F (-C) hψ]
  have hbd : ∃ C', ∀ y, |v y + (-C) * (barrierProfile s a ∘ ζ) y| ≤ C' := by
    refine ⟨C, fun y => ?_⟩
    have h1 := hv01 y
    have h2 := barrierProfile_pos s a (ζ y)
    have h3 := barrierProfile_le_one hs0 a (ζ y)
    simp only [Function.comp]
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg hC0 h2.le, mul_nonneg hC0 (sub_nonneg.2 h3)]
  have hmax := hMP (κ := fun y => K * Real.smoothTransition (ζ y - a))
    (fun y => mul_nonneg hK0 (Real.smoothTransition.nonneg _)) _ hw hbd (by
      intro y hy
      rw [hLw y, heq y]
      simp only [Function.comp] at hy ⊢
      have hgy : g y = 0 := by
        by_contra hne
        have hlt := hga y hne
        have := barrierProfile_eq_one (s := s) a (ζ y) (by linarith)
        have h1 := (hv01 y).2
        rw [this] at hy
        nlinarith
      rw [hgy]
      have := mul_nonneg hC0 (hsup y)
      nlinarith)
  have hxle := hmax x
  try simp only [Function.comp] at hxle
  rw [barrierProfile_eq_exp a (ζ x) hx] at hxle
  have hv_le : v x ≤ C * Real.exp (-s) := by linarith
  have hexp : Real.exp (-s) ≤ (s + 1)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (by linarith) (by linarith [Real.add_one_le_exp s])
  calc v x ≤ C * Real.exp (-s) := hv_le
    _ ≤ C * (s + 1)⁻¹ := mul_le_mul_of_nonneg_left hexp hC0
    _ ≤ ε := by
      rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]
      have : s * ε = C := by rw [hs]; field_simp
      nlinarith

end Decay

section Final

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
/-- **Barrier decay** (CO_PLAN 2.2 step 5): penalized solutions with large killing rate `K`
are `≤ ε` outside the compact `{ζ ≤ a+2}`; `K₀` depends only on `ζ, a, lam, Cg, ε`. -/
theorem barrier_decay {ζ : M → ℝ} (hζ : MSmooth F ζ) (hζc : ∀ c, IsCompact {x | ζ x ≤ c})
    {lam : ℝ} (hlam : 0 < lam) (Cg a : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K₀ : ℝ, ∀ K ≥ K₀, ∀ (g v : M → ℝ), MSmooth F v → (∀ x, 0 ≤ g x ∧ g x ≤ Cg) →
      (∀ x, g x ≠ 0 → ζ x < a) → (∀ x, 0 ≤ v x ∧ v x ≤ Cg / lam) →
      (∀ x, mgenerator F V v x =
        (lam + K * Real.smoothTransition (ζ x - a)) * v x - g x) →
      ∀ x, a + 2 ≤ ζ x → v x ≤ ε :=
  barrier_decay_of_MP F hV hζ hζc hlam
    (fun {_κ} hκ w hw hb h => energy_max_principle F hV hμ hw hb hlam hκ h) Cg a hε

end Final

end CutoffRigidity.Riemann.Diff
