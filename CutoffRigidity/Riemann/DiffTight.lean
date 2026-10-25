module

public import CutoffRigidity.Riemann.DiffInstance2

/-! # LSI, entropy inequality and tightness (workstream HPOS)   -/

@[expose] public section

open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Gibbs
open Real
/-- Young's inequality `w b ≤ w log w - w log s - w + s e^b` (`w ≥ 0`, `s > 0`). -/
theorem young_pt {w s b : ℝ} (hw : 0 ≤ w) (hs : 0 < s) :
    w * b ≤ w * Real.log w - w * Real.log s - w + s * Real.exp b := by
  rcases hw.eq_or_lt with h | h
  · subst h; simp; positivity
  · have h1 : Real.log (w / s * Real.exp (b - Real.log (w / s))) = b := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]; ring
    have key := Real.add_one_le_exp (b - Real.log (w / s))
    have e : Real.exp b = w / s * Real.exp (b - Real.log (w / s)) := by
      rw [Real.exp_sub, Real.exp_log (by positivity)]; field_simp
    have hl : Real.log (w / s) = Real.log w - Real.log s := Real.log_div h.ne' hs.ne'
    rw [hl] at key
    have : w * (b - (Real.log w - Real.log s) + 1) ≤ w * Real.exp (b - (Real.log w - Real.log s)) :=
      mul_le_mul_of_nonneg_left key hw
    have e2 : s * Real.exp b = w * Real.exp (b - (Real.log w - Real.log s)) := by
      rw [← hl, Real.exp_sub, Real.exp_log (by positivity)]; field_simp
    nlinarith [this, e2]


/-- **Gibbs variational (Donsker–Varadhan) inequality** on a finite measure space:
`∫ w g ≤ Ent(w) + (∫ w) log ∫ e^g` for `w ≥ 0`, `g` bounded measurable. -/
theorem gibbs_var {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {w g : α → ℝ} (hw0 : ∀ x, 0 ≤ w x) (hw : Integrable w μ)
    (hwl : Integrable (fun x => w x * Real.log (w x)) μ)
    (hg : Measurable g) (B : ℝ) (hB : ∀ x, |g x| ≤ B) :
    ∫ x, w x * g x ∂μ ≤ (∫ x, w x * Real.log (w x) ∂μ - (∫ x, w x ∂μ) * Real.log (∫ x, w x ∂μ))
      + (∫ x, w x ∂μ) * Real.log (∫ x, Real.exp (g x) ∂μ) := by
  have hwg : Integrable (fun x => w x * g x) μ :=
    hw.mul_bdd hg.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by simpa using hB x)
  have heg : Integrable (fun x => Real.exp (g x)) μ := by
    refine Integrable.mono' (integrable_const (Real.exp B)) (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (le_trans (le_abs_self _) (hB x))
  set s := ∫ x, w x ∂μ with hs
  have hs0 : 0 ≤ s := integral_nonneg hw0
  rcases hs0.eq_or_lt with h0 | hpos
  · have hz : w =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg hw0 hw).1 h0.symm
    have h1 : ∫ x, w x * g x ∂μ = 0 := by
      rw [integral_congr_ae (g := fun _ => (0:ℝ)) (by filter_upwards [hz] with x hx; simp [hx])]; simp
    have h2 : ∫ x, w x * Real.log (w x) ∂μ = 0 := by
      rw [integral_congr_ae (g := fun _ => (0:ℝ)) (by filter_upwards [hz] with x hx; simp [hx])]; simp
    rw [h1, h2, ← h0]; simp
  · have : NeZero μ := ⟨by rintro rfl; simp [hs] at hpos⟩
    set c := Real.log (∫ x, Real.exp (g x) ∂μ)
    have hI := integral_exp_pos heg
    have hpt : ∀ x, w x * (g x - c) ≤ w x * Real.log (w x) - w x * Real.log s - w x + s * Real.exp (g x - c) :=
      fun x => young_pt (hw0 x) hpos
    have hec : Real.exp c = ∫ x, Real.exp (g x) ∂μ := Real.exp_log hI
    have i1 : Integrable (fun x => w x * (g x - c)) μ :=
      (hwg.sub (hw.mul_const c)).congr (Filter.Eventually.of_forall fun x => by simp [mul_sub])
    have i2 : Integrable (fun x => s * Real.exp (g x - c)) μ :=
      (heg.const_mul (s * (Real.exp c)⁻¹)).congr (Filter.Eventually.of_forall fun x => by
        simp [Real.exp_sub, div_eq_mul_inv]; ring)
    have i3 : Integrable (fun x => w x * Real.log (w x) - w x * Real.log s - w x) μ :=
      (hwl.sub (hw.mul_const (Real.log s))).sub hw
    have hint : ∫ x, w x * (g x - c) ∂μ ≤ ∫ x, (w x * Real.log (w x) - w x * Real.log s - w x + s * Real.exp (g x - c)) ∂μ :=
      integral_mono i1 (i3.add i2) hpt
    have l1 : ∫ x, w x * (g x - c) ∂μ = ∫ x, w x * g x ∂μ - s * c := by
      have : (fun x => w x * (g x - c)) = fun x => w x * g x - w x * c := by ext x; ring
      rw [this, integral_sub hwg (hw.mul_const c), integral_mul_const]
    have l2 : ∫ x, (w x * Real.log (w x) - w x * Real.log s - w x + s * Real.exp (g x - c)) ∂μ
        = ∫ x, w x * Real.log (w x) ∂μ - s * Real.log s - s + s := by
      have j1 : ∫ x, (w x * Real.log (w x) - w x * Real.log s - w x) ∂μ
          = ∫ x, w x * Real.log (w x) ∂μ - s * Real.log s - s := by
        have h1 := integral_sub (hwl.sub (hw.mul_const (Real.log s))) hw
        have h2 := integral_sub hwl (hw.mul_const (Real.log s))
        simp only [integral_mul_const] at h2
        simp only [Pi.sub_apply] at h1
        rw [h1, h2]
      rw [integral_add i3 i2, j1, integral_const_mul]
      have : ∫ x, Real.exp (g x - c) ∂μ = 1 := by
        have : (fun x => Real.exp (g x - c)) = fun x => (Real.exp c)⁻¹ * Real.exp (g x) := by
          ext x; rw [Real.exp_sub]; ring
        rw [this, integral_const_mul, ← hec]; field_simp
      rw [this]; ring
    rw [l1, l2] at hint
    linarith

end Gibbs

section Tight

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]

/-- Entropy `Ent_μ(w) = ∫ w log w dμ - (∫ w dμ) log (∫ w dμ)` (real conventions: `0 log 0 = 0`). -/
noncomputable def entL (μ : Measure M) (w : M → ℝ) : ℝ :=
  ∫ x, w x * Real.log (w x) ∂μ - (∫ x, w x ∂μ) * Real.log (∫ x, w x ∂μ)

/-- Log-Sobolev inequality with constant `ρ` on test functions:
`Ent_μ(f²) ≤ (2/ρ) ∫ Γ f dμ`. -/
def LSI (V : M → ℝ) (μ : Measure M) (ρ : ℝ) : Prop :=
  ∀ f : testSub F M, entL μ (fun x => (f : M → ℝ) x ^ 2) ≤ 2 / ρ * ∫ x, carre F (f : M → ℝ) (f : M → ℝ) x ∂μ


theorem testSub_sq_integrable (f : testSub F M) (μ : Measure M) [IsFiniteMeasure μ] :
    Integrable (fun x => (f : M → ℝ) x ^ 2) μ := by
  have hc : Continuous (f : M → ℝ) := testSub_continuous F f
  have hcs : HasCompactSupport (f : M → ℝ) := f.2.2
  have h : HasCompactSupport (fun x => (f : M → ℝ) x ^ 2) :=
    hcs.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
  exact (hc.pow 2).integrable_of_hasCompactSupport h

theorem testSub_sqlog_integrable (f : testSub F M) (μ : Measure M) [IsFiniteMeasure μ] :
    Integrable (fun x => (f : M → ℝ) x ^ 2 * Real.log ((f : M → ℝ) x ^ 2)) μ := by
  have hc : Continuous (f : M → ℝ) := testSub_continuous F f
  have hcs : HasCompactSupport (f : M → ℝ) := f.2.2
  have hcont : Continuous fun x => (f : M → ℝ) x ^ 2 * Real.log ((f : M → ℝ) x ^ 2) :=
    Real.continuous_mul_log.comp (hc.pow 2)
  have h : HasCompactSupport (fun x => (f : M → ℝ) x ^ 2 * Real.log ((f : M → ℝ) x ^ 2)) :=
    hcs.comp_left (g := fun t : ℝ => t ^ 2 * Real.log (t ^ 2)) (by simp)
  exact hcont.integrable_of_hasCompactSupport h

/-- `LSI` implies the entropy form: for a test function `f` and bounded measurable `g`,
`∫ f² g ≤ (2/ρ) ∫ Γ f + (∫ f²) log ∫ e^g` (`LSI` is only imposed on test functions). -/
theorem LSI.entropy_form {V : M → ℝ} {μ : Measure M} [IsProbabilityMeasure μ] {ρ : ℝ}
    (h : LSI F V μ ρ) (f : testSub F M) {g : M → ℝ} (hg : Measurable g) (B : ℝ)
    (hB : ∀ x, |g x| ≤ B) :
    ∫ x, (f : M → ℝ) x ^ 2 * g x ∂μ ≤ 2 / ρ * ∫ x, carre F (f : M → ℝ) (f : M → ℝ) x ∂μ
      + (∫ x, (f : M → ℝ) x ^ 2 ∂μ) * Real.log (∫ x, Real.exp (g x) ∂μ) := by
  have hw := testSub_sq_integrable F f μ
  have hwl := testSub_sqlog_integrable F f μ
  have := gibbs_var (μ := μ) (fun x => sq_nonneg ((f : M → ℝ) x)) hw hwl hg B hB
  have h2 := h f
  unfold entL at h2
  linarith

include F in
/-- Closed `edist`-balls exhaust the space, so their complements have measure tending to `0`. -/
theorem exists_compact_small (μ : Measure M) [IsProbabilityMeasure μ] {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : Set M, IsCompact K ∧ μ.real Kᶜ ≤ δ := by
  haveI : Nonempty M := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := measure_univ (μ := μ)
    rw [Set.univ_eq_empty_iff.2 h] at this
    simp at this
  obtain ⟨x₀⟩ := this
  let S : ℕ → Set M := fun n => {y : M | edist x₀ y ≤ ENNReal.ofReal (n : ℝ)}
  have hS : ∀ n, IsCompact (S n) := fun n => isCompact_edist_le F x₀ (Nat.cast_nonneg n)
  have hmono : Antitone fun n => (S n)ᶜ := by
    intro a b hab y hy hyb
    apply hy
    exact le_trans hyb (ENNReal.ofReal_le_ofReal (by exact_mod_cast hab))
  have hinter : ⋂ n, (S n)ᶜ = ∅ := by
    ext y
    simp only [mem_iInter, mem_compl_iff, mem_empty_iff_false, iff_false, not_forall, not_not]
    have hfin := edist_ne_top_of_connected F x₀ y
    obtain ⟨n, hn⟩ := exists_nat_ge (edist x₀ y).toReal
    exact ⟨n, by
      show edist x₀ y ≤ ENNReal.ofReal n
      rw [← ENNReal.ofReal_toReal hfin]
      exact ENNReal.ofReal_le_ofReal hn⟩
  have ht := tendsto_measure_iInter_atTop (μ := μ) (s := fun n => (S n)ᶜ)
    (fun n => (hS n).isClosed.measurableSet.compl.nullMeasurableSet) hmono ⟨0, measure_ne_top _ _⟩
  rw [hinter, measure_empty] at ht
  have hev := ht.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < ENNReal.ofReal δ by simpa using hδ))
  obtain ⟨n, hn⟩ := hev.exists
  refine ⟨S n, hS n, ?_⟩
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hn.le
  rwa [ENNReal.toReal_ofReal hδ.le] at this

/-- Key tail estimate for a fixed closed set. -/
theorem tail_aux {V : M → ℝ} {μ : Measure M} [IsProbabilityMeasure μ] {ρ : ℝ}
    (hLSI : LSI F V μ ρ) (f : testSub F M) {K : Set M} (hK : IsClosed K) {θ : ℝ} (hθ : 0 ≤ θ) :
    θ * ∫ x in Kᶜ, (f : M → ℝ) x ^ 2 ∂μ ≤ 2 / ρ * ∫ x, carre F (f : M → ℝ) (f : M → ℝ) x ∂μ
      + (∫ x, (f : M → ℝ) x ^ 2 ∂μ) * Real.log (1 + (Real.exp θ - 1) * μ.real Kᶜ) := by
  have hKc : MeasurableSet Kᶜ := hK.measurableSet.compl
  have hgm : Measurable (Kᶜ.indicator fun _ => θ) := measurable_const.indicator hKc
  have hB : ∀ x, |Kᶜ.indicator (fun _ => θ) x| ≤ θ := by
    intro x; by_cases hx : x ∈ Kᶜ <;> simp [hx, abs_of_nonneg hθ, hθ]
  have h1 := LSI.entropy_form F hLSI f hgm θ hB
  have e1 : ∫ x, (f : M → ℝ) x ^ 2 * Kᶜ.indicator (fun _ => θ) x ∂μ
      = θ * ∫ x in Kᶜ, (f : M → ℝ) x ^ 2 ∂μ := by
    rw [← integral_const_mul, ← integral_indicator hKc]
    congr 1; ext x
    by_cases hx : x ∈ Kᶜ <;> simp [hx, mul_comm]
  have e2 : ∫ x, Real.exp (Kᶜ.indicator (fun _ => θ) x) ∂μ = 1 + (Real.exp θ - 1) * μ.real Kᶜ := by
    have : (fun x => Real.exp (Kᶜ.indicator (fun _ => θ) x))
        = fun x => 1 + Kᶜ.indicator (fun _ => Real.exp θ - 1) x := by
      ext x; by_cases hx : x ∈ Kᶜ <;> simp [hx]
    rw [this, integral_add (integrable_const _) ((integrable_const _).indicator hKc),
      integral_indicator_const _ hKc]
    simp [mul_comm]
  rw [e1, e2] at h1
  exact h1

/-- Tightness of the energy balls from LSI. -/
theorem tail_of_LSI {V : M → ℝ} {μ : Measure M} [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ)
    (hLSI : LSI F V μ ρ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ K : Set M, IsCompact K ∧ ∀ f : testSub F M,
      ∫ x, carre F (f : M → ℝ) (f : M → ℝ) x ∂μ + ∫ x, (f : M → ℝ) x ^ 2 ∂μ ≤ C →
        ∫ x in Kᶜ, (f : M → ℝ) x ^ 2 ∂μ ≤ ε := by
  set C' := max C 1 with hC'
  have hC'pos : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set θ := 1 + 2 * (2 / ρ * C') / ε with hθ
  have hθpos : 0 < θ := by positivity
  have hδ : 0 < ε * θ / (2 * C' * Real.exp θ) := by positivity
  obtain ⟨K, hKc, hKm⟩ := exists_compact_small F μ hδ
  refine ⟨K, hKc, fun f hf => ?_⟩
  have hK : IsClosed K := hKc.isClosed
  have h := tail_aux F hLSI f hK hθpos.le
  have ha : 0 ≤ ∫ x, carre F (f : M → ℝ) (f : M → ℝ) x ∂μ :=
    integral_nonneg fun x => carre_nonneg F _ x
  have hs : 0 ≤ ∫ x, (f : M → ℝ) x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have ha' : ∫ x, carre F (f : M → ℝ) (f : M → ℝ) x ∂μ ≤ C' := by
    linarith [le_max_left C 1]
  have hs' : ∫ x, (f : M → ℝ) x ^ 2 ∂μ ≤ C' := by linarith [le_max_left C 1]
  set m := μ.real Kᶜ with hm
  have hm0 : 0 ≤ m := measureReal_nonneg
  have hL0 : 0 ≤ Real.log (1 + (Real.exp θ - 1) * m) :=
    Real.log_nonneg (by
      have : 0 ≤ (Real.exp θ - 1) * m := mul_nonneg (by linarith [Real.add_one_le_exp θ]) hm0
      linarith)
  have hL1 : Real.log (1 + (Real.exp θ - 1) * m) ≤ Real.exp θ * m := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + (Real.exp θ - 1) * m by
      have : 0 ≤ (Real.exp θ - 1) * m := mul_nonneg (by linarith [Real.add_one_le_exp θ]) hm0
      linarith)
    nlinarith [Real.exp_pos θ]
  have h2ρ : 0 < 2 / ρ := by positivity
  have t1 : 2 / ρ * ∫ x, carre F (f : M → ℝ) (f : M → ℝ) x ∂μ ≤ 2 / ρ * C' :=
    mul_le_mul_of_nonneg_left ha' h2ρ.le
  have t2 : (∫ x, (f : M → ℝ) x ^ 2 ∂μ) * Real.log (1 + (Real.exp θ - 1) * m)
      ≤ C' * (Real.exp θ * m) :=
    mul_le_mul hs' hL1 hL0 hC'pos.le
  have t3 : 2 / ρ * C' ≤ ε * θ / 2 := by
    have : θ * ε = ε + 2 * (2 / ρ * C') := by rw [hθ]; field_simp
    nlinarith
  have t4 : C' * (Real.exp θ * m) ≤ ε * θ / 2 := by
    have h5 : m * (2 * C' * Real.exp θ) ≤ ε * θ := by
      have := (le_div_iff₀ (by positivity : 0 < 2 * C' * Real.exp θ)).1 hKm
      linarith
    nlinarith
  have : θ * ∫ x in Kᶜ, (f : M → ℝ) x ^ 2 ∂μ ≤ θ * ε := by nlinarith
  exact le_of_mul_le_mul_left this hθpos

end Tight

end CutoffRigidity.Riemann.Diff
