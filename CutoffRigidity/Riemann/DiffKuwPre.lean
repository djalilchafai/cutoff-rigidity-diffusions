module

public import CutoffRigidity.Riemann.DiffAPI
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-! # KUW-B preliminaries: `BETestFun` and the pointwise local Lipschitz constant

* `BETestFun F V μ ρ Kk`: the pointwise Bakry-Emery gradient bound for smooth compactly supported
  test functions (the output of workstream BE, here an explicit `Prop`).
* `dd x y = (edist x y).toReal`, `locLip ψ y ε` (best Lipschitz constant of `ψ` on the open
  `edist`-ball of radius `ε` around `y`), `lipAt ψ y = lim_{ε → 0} locLip ψ y ε` (the *pointwise
  local Lipschitz constant*).  Both are measurable, `lipAt ψ y ≤ L` for `L`-Lipschitz `ψ`.
-/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set Topology
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section BE

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M]

/-- **Pointwise Bakry-Emery gradient bound** for smooth compactly supported test functions:
`Γ(P_t f)(x) ≤ e^{-2ρt} ∫ Γ f dP_t(x,·)`. -/
def BETestFun (V : M → ℝ) (μ : Measure M) (ρ : ℝ) (Kk : ℝ≥0 → Kernel M M) : Prop :=
  ∀ f : M → ℝ, MSmooth F f → HasCompactSupport f → ∀ (t : ℝ≥0) (x : M),
    carre F (semi Kk t f) (semi Kk t f) x ≤
      Real.exp (-2 * ρ * t) * ∫ y, carre F f f y ∂(Kk t x)

end BE

section Lip

variable {X : Type*} [EMetricSpace X]

/-- The real distance. -/
noncomputable def dd (x y : X) : ℝ := (edist x y).toReal

/-- Best Lipschitz constant of `ψ` on the open ball of radius `ε` around `y`. -/
noncomputable def locLip (ψ : X → ℝ) (y : X) (ε : ℝ) : ℝ :=
  sInf {c : ℝ | 0 ≤ c ∧ ∀ w w' : X, edist y w < ENNReal.ofReal ε → edist y w' < ENNReal.ofReal ε →
    |ψ w - ψ w'| ≤ c * dd w w'}

/-- The pointwise local Lipschitz constant `lim_{ε → 0} locLip ψ y ε`. -/
noncomputable def lipAt (ψ : X → ℝ) (y : X) : ℝ :=
  ⨅ n : ℕ, locLip ψ y (1 / ((n : ℝ) + 1))

theorem dd_nonneg (x y : X) : 0 ≤ dd x y := ENNReal.toReal_nonneg

theorem dd_comm (x y : X) : dd x y = dd y x := by simp [dd, edist_comm]

theorem dd_self (x : X) : dd x x = 0 := by simp [dd]

theorem dd_triangle (hfin : ∀ x y : X, edist x y ≠ ⊤) (x y z : X) : dd x z ≤ dd x y + dd y z := by
  unfold dd
  rw [← ENNReal.toReal_add (hfin _ _) (hfin _ _)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin _ _, hfin _ _⟩) (edist_triangle _ _ _)

theorem edist_eq_ofReal_dd (hfin : ∀ x y : X, edist x y ≠ ⊤) (x y : X) :
    edist x y = ENNReal.ofReal (dd x y) := by
  simp [dd, ENNReal.ofReal_toReal (hfin x y)]

theorem abs_sub_le_of_lipschitz (hfin : ∀ x y : X, edist x y ≠ ⊤) {ψ : X → ℝ} {L : ℝ≥0}
    (hψ : LipschitzWith L ψ) (x y : X) : |ψ x - ψ y| ≤ L * dd x y := by
  have h := hψ x y
  rw [edist_dist, Real.dist_eq, edist_eq_ofReal_dd hfin] at h
  have h2 : ENNReal.ofReal |ψ x - ψ y| ≤ ENNReal.ofReal (L * dd x y) := by
    refine h.trans_eq ?_
    symm
    rw [ENNReal.ofReal_mul (NNReal.coe_nonneg L), ENNReal.ofReal_coe_nnreal]
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (NNReal.coe_nonneg L) (dd_nonneg _ _))).1 h2

/-- The admissible set defining `locLip`. -/
def lipSet (ψ : X → ℝ) (y : X) (ε : ℝ) : Set ℝ :=
  {c : ℝ | 0 ≤ c ∧ ∀ w w' : X, edist y w < ENNReal.ofReal ε → edist y w' < ENNReal.ofReal ε →
    |ψ w - ψ w'| ≤ c * dd w w'}

theorem locLip_eq (ψ : X → ℝ) (y : X) (ε : ℝ) : locLip ψ y ε = sInf (lipSet ψ y ε) := rfl

theorem lipSet_bddBelow (ψ : X → ℝ) (y : X) (ε : ℝ) : BddBelow (lipSet ψ y ε) :=
  ⟨0, fun _ hc => hc.1⟩

theorem lipSet_nonempty (hfin : ∀ x y : X, edist x y ≠ ⊤) {ψ : X → ℝ} {L : ℝ≥0}
    (hψ : LipschitzWith L ψ) (y : X) (ε : ℝ) : (lipSet ψ y ε).Nonempty :=
  ⟨L, L.2, fun w w' _ _ => abs_sub_le_of_lipschitz hfin hψ w w'⟩

theorem locLip_nonneg (ψ : X → ℝ) (y : X) (ε : ℝ) : 0 ≤ locLip ψ y ε :=
  Real.sInf_nonneg fun _ hc => hc.1

theorem locLip_le (hfin : ∀ x y : X, edist x y ≠ ⊤) {ψ : X → ℝ} {L : ℝ≥0}
    (hψ : LipschitzWith L ψ) (y : X) (ε : ℝ) : locLip ψ y ε ≤ L :=
  csInf_le (lipSet_bddBelow ψ y ε) ⟨L.2, fun w w' _ _ => abs_sub_le_of_lipschitz hfin hψ w w'⟩

/-- Key property: every `c > locLip` is a Lipschitz constant on the ball. -/
theorem abs_sub_le_of_locLip_lt (hfin : ∀ x y : X, edist x y ≠ ⊤) {ψ : X → ℝ} {L : ℝ≥0}
    (hψ : LipschitzWith L ψ) {y : X} {ε c : ℝ} (hc : locLip ψ y ε < c) {w w' : X}
    (hw : edist y w < ENNReal.ofReal ε) (hw' : edist y w' < ENNReal.ofReal ε) :
    |ψ w - ψ w'| ≤ c * dd w w' := by
  obtain ⟨c', hc'S, hc'c⟩ := exists_lt_of_csInf_lt (lipSet_nonempty hfin hψ y ε) hc
  exact (hc'S.2 w w' hw hw').trans (mul_le_mul_of_nonneg_right hc'c.le (dd_nonneg _ _))

theorem locLip_mono (hfin : ∀ x y : X, edist x y ≠ ⊤) {ψ : X → ℝ} {L : ℝ≥0}
    (hψ : LipschitzWith L ψ) (y : X) {ε ε' : ℝ} (h : ε ≤ ε') : locLip ψ y ε ≤ locLip ψ y ε' := by
  refine le_csInf (lipSet_nonempty hfin hψ y ε') fun c hc => csInf_le (lipSet_bddBelow ψ y ε) ?_
  refine ⟨hc.1, fun w w' hw hw' => hc.2 w w' (hw.trans_le ?_) (hw'.trans_le ?_)⟩ <;>
    exact ENNReal.ofReal_le_ofReal h

theorem lipAt_le_locLip (hfin : ∀ x y : X, edist x y ≠ ⊤) {ψ : X → ℝ} {L : ℝ≥0}
    (hψ : LipschitzWith L ψ) (y : X) (n : ℕ) : lipAt ψ y ≤ locLip ψ y (1 / ((n : ℝ) + 1)) :=
  ciInf_le ⟨0, by rintro _ ⟨m, rfl⟩; exact locLip_nonneg _ _ _⟩ n

theorem lipAt_nonneg (ψ : X → ℝ) (y : X) : 0 ≤ lipAt ψ y :=
  le_ciInf fun n => locLip_nonneg ψ y _

theorem lipAt_le (hfin : ∀ x y : X, edist x y ≠ ⊤) {ψ : X → ℝ} {L : ℝ≥0}
    (hψ : LipschitzWith L ψ) (y : X) : lipAt ψ y ≤ L :=
  (lipAt_le_locLip hfin hψ y 0).trans (locLip_le hfin hψ y _)

theorem tendsto_locLip (hfin : ∀ x y : X, edist x y ≠ ⊤) {ψ : X → ℝ} {L : ℝ≥0}
    (hψ : LipschitzWith L ψ) (y : X) :
    Tendsto (fun n : ℕ => locLip ψ y (1 / ((n : ℝ) + 1))) atTop (𝓝 (lipAt ψ y)) := by
  have hanti : Antitone fun n : ℕ => locLip ψ y (1 / ((n : ℝ) + 1)) := by
    intro m n hmn
    refine locLip_mono hfin hψ y ?_
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    gcongr
  exact tendsto_atTop_ciInf hanti ⟨0, by rintro _ ⟨m, rfl⟩; exact locLip_nonneg _ _ _⟩

/-- Key property of `lipAt`: every `c > lipAt` is a Lipschitz constant on a small ball. -/
theorem exists_ball_of_lipAt_lt (hfin : ∀ x y : X, edist x y ≠ ⊤) {ψ : X → ℝ} {L : ℝ≥0}
    (hψ : LipschitzWith L ψ) {y : X} {c : ℝ} (hc : lipAt ψ y < c) :
    ∃ ε > 0, ∀ w w' : X, edist y w < ENNReal.ofReal ε → edist y w' < ENNReal.ofReal ε →
      |ψ w - ψ w'| ≤ c * dd w w' := by
  obtain ⟨n, hn⟩ := exists_lt_of_ciInf_lt hc
  exact ⟨1 / ((n : ℝ) + 1), by positivity, fun w w' hw hw' =>
    abs_sub_le_of_locLip_lt hfin hψ hn hw hw'⟩

/-- Converse: if every `c > c₀` is a Lipschitz constant on a small ball around `y`, then
`lipAt ψ y ≤ c₀`. -/
theorem lipAt_le_of (hfin : ∀ x y : X, edist x y ≠ ⊤) {ψ : X → ℝ} {L : ℝ≥0}
    (hψ : LipschitzWith L ψ) {y : X} {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (h : ∀ c > c₀, ∃ ε > 0, ∀ w w' : X, edist y w < ENNReal.ofReal ε →
      edist y w' < ENNReal.ofReal ε → |ψ w - ψ w'| ≤ c * dd w w') : lipAt ψ y ≤ c₀ := by
  refine le_of_forall_gt fun c hc => ?_
  have hc0 : c₀ < c := hc
  obtain ⟨ε, hε, hεc⟩ := h ((c₀ + c) / 2) (by linarith)
  have hmid : (c₀ + c) / 2 < c := by linarith
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine lt_of_le_of_lt ((lipAt_le_locLip hfin hψ y n).trans ?_) hmid
  refine csInf_le (lipSet_bddBelow ψ y _) ⟨?_, fun w w' hw hw' => hεc w w' ?_ ?_⟩
  · linarith
  · exact hw.trans_le (ENNReal.ofReal_le_ofReal hn.le)
  · exact hw'.trans_le (ENNReal.ofReal_le_ofReal hn.le)

theorem lowerSemicontinuous_locLip (hfin : ∀ x y : X, edist x y ≠ ⊤) {ψ : X → ℝ} {L : ℝ≥0}
    (hψ : LipschitzWith L ψ) (ε : ℝ) : LowerSemicontinuous fun y => locLip ψ y ε := by
  intro y c hc
  rw [eventually_iff_exists_mem]
  by_cases hc0 : c < 0
  · exact ⟨univ, univ_mem, fun y' _ => hc0.trans_le (locLip_nonneg _ _ _)⟩
  push Not at hc0
  have hnot : c ∉ lipSet ψ y ε := fun hmem => (csInf_le (lipSet_bddBelow ψ y ε) hmem).not_gt hc
  simp only [lipSet, mem_ofPred_eq, not_and, not_forall, not_le] at hnot
  obtain ⟨w, w', hw, hw', hlt⟩ := hnot hc0
  have hdd : 0 < dd w w' := by
    refine lt_of_le_of_ne (dd_nonneg _ _) fun h0 => ?_
    have := abs_sub_le_of_lipschitz hfin hψ w w'
    rw [← h0] at hlt this
    simp only [mul_zero] at hlt this
    exact absurd (abs_nonpos_iff.1 this) (by
      intro h; rw [h] at hlt; simp at hlt)
  set δ : ℝ≥0∞ := min (ENNReal.ofReal ε - edist y w) (ENNReal.ofReal ε - edist y w') with hδ
  have hδpos : 0 < δ := lt_min (tsub_pos_of_lt hw) (tsub_pos_of_lt hw')
  refine ⟨Metric.eball y δ, Metric.eball_mem_nhds y hδpos, fun y' hy' => ?_⟩
  rw [Metric.mem_eball] at hy'
  have h1 : edist y' w < ENNReal.ofReal ε := by
    calc edist y' w ≤ edist y' y + edist y w := edist_triangle _ _ _
      _ < (ENNReal.ofReal ε - edist y w) + edist y w := by
          refine ENNReal.add_lt_add_right (hfin y w) ?_
          exact hy'.trans_le (min_le_left _ _)
      _ = ENNReal.ofReal ε := tsub_add_cancel_of_le hw.le
  have h2 : edist y' w' < ENNReal.ofReal ε := by
    calc edist y' w' ≤ edist y' y + edist y w' := edist_triangle _ _ _
      _ < (ENNReal.ofReal ε - edist y w') + edist y w' := by
          refine ENNReal.add_lt_add_right (hfin y w') ?_
          exact hy'.trans_le (min_le_right _ _)
      _ = ENNReal.ofReal ε := tsub_add_cancel_of_le hw'.le
  have hq : c < |ψ w - ψ w'| / dd w w' := by rw [lt_div_iff₀ hdd]; exact hlt
  refine hq.trans_le (le_csInf (lipSet_nonempty hfin hψ y' ε) fun c'' hc'' => ?_)
  rw [div_le_iff₀ hdd]
  have := hc''.2 w w' h1 h2
  linarith

variable [MeasurableSpace X] [BorelSpace X]

theorem measurable_locLip (hfin : ∀ x y : X, edist x y ≠ ⊤) {ψ : X → ℝ} {L : ℝ≥0}
    (hψ : LipschitzWith L ψ) (ε : ℝ) : Measurable fun y => locLip ψ y ε :=
  (lowerSemicontinuous_locLip hfin hψ ε).measurable

theorem measurable_lipAt (hfin : ∀ x y : X, edist x y ≠ ⊤) {ψ : X → ℝ} {L : ℝ≥0}
    (hψ : LipschitzWith L ψ) : Measurable fun y => lipAt ψ y :=
  Measurable.iInf fun n => measurable_locLip hfin hψ _

end Lip

section Sharp

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (M : Type) [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

/-- Statement of the sharp smooth approximation of Lipschitz functions (proved in `DiffKuwApprox`):
every Lipschitz `ψ` is uniformly `ε`-approximated by a smooth `g` with
`‖∇g(x)‖ ≤ (1+η) · (Lipschitz constant of ψ on the ε-ball around x) + η`. -/
def SharpApprox : Prop :=
  ∀ (ψ : M → ℝ) (L : ℝ≥0), LipschitzWith L ψ → ∀ ε η : ℝ, 0 < ε → 0 < η →
    ∃ g : M → ℝ, MSmooth F g ∧ (∀ x, |g x - ψ x| ≤ ε) ∧
      ∀ x, ‖mgrad F g x‖ ≤ (1 + η) * locLip ψ x ε + η

end Sharp

end CutoffRigidity.Riemann.Diff
