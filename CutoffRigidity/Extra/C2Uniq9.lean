module

public import CutoffRigidity.Extra.C2Uniq8
public import CutoffRigidity.Extra.EuclideanWasserstein
public import CutoffRigidity.Extra.EuclideanKernelStatements
public import CutoffRigidity.Extra.EuclideanCutoffs
public import CutoffRigidity.Extra.EuclideanWeakK

/-! # `C²` versions of the kernel statements

Statements of `EuclideanWasserstein`, `EuclideanKernelStatements`, `EuclideanCutoffs`, `EuclideanWeakK`
with `IsEuclideanLangevin` / `IsRigidSequenceK` replaced by their `C²` analogues `IsEucLangevin2` /
`IsRigidSeqK2` (convex `C²` potentials). The proofs are those of the `_K` versions with the transfer
lemmas replaced by the `C²` ones (`C2Uniq8`), i.e. with `C²` uniqueness (`C2Uniq7`) in place of
`isEuclideanDiffusion_unique`.
-/

public section

set_option backward.isDefEq.respectTransparency false

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Set CutCur
open scoped ENNReal NNReal Topology Asymptotics ContDiff

/-- **Theorem 1.1** (main Wasserstein estimate), kernel form (no Brownian motion). -/
theorem main_wasserstein_estimate_C2 {d : ℕ} {V : CutCur.Rd d → ℝ}
    {Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d)}
    (hL : CutCur.C2U.IsEucLangevin2 V Pt) (hV : CutCur.RigidCurvature V) (t : ℝ≥0) :
    let gap := CutCur.spectralGap V
    let q := Real.exp (-2 * gap * t)
    let lower := fun Λ : ℝ≥0∞ => ENNReal.ofReal (q / gap) * Λ +
      ENNReal.ofReal (CutCur.firstEigenDim V * (1 - Real.sqrt (1 - q)) ^ 2 / gap)
    let W := fun x₀ => CutCur.wasserstein2 (Pt t x₀) (CutCur.gibbs V) ^ 2
    (∀ S : Set (CutCur.Rd d), S.Nonempty →
      lower (⨆ x₀ ∈ S, CutCur.eigenLambda V x₀) ≤ ⨆ x₀ ∈ S, W x₀ ∧
      ⨆ x₀ ∈ S, W x₀ ≤ ENNReal.ofReal q * ⨆ x₀ ∈ S, ∫⁻ x, edist x x₀ ^ 2 ∂CutCur.gibbs V) ∧
    (∫ x, x ∂CutCur.gibbs V = 0 → ∀ R : ℝ, 0 ≤ R →
      lower (ENNReal.ofReal (gap * R ^ 2)) ≤ ⨆ x₀ ∈ Metric.closedBall 0 R, W x₀) := by
  obtain ⟨Ω, _, B, P, X, hP, hLang, key⟩ := CutCur.C2U.exists_isLangevin_of_rigid_C2 hL hV
  have := main_wasserstein_estimate_carrier hLang hV t
  simpa only [key] using this

/-- **Corollary 1.3** (Wasserstein cutoff), kernel form (no Brownian motion). -/
theorem wasserstein_cutoff_C2 {V : ∀ n, CutCur.Rd n → ℝ}
    {Pt : ∀ n, ℝ≥0 → Kernel (CutCur.Rd n) (CutCur.Rd n)}
    (h : CutCur.C2U.IsRigidSeqK2 V Pt) {c : ℝ} (hc : 0 < c) :
    CutCur.HasCutoff (fun n => CutCur.worstK (Pt n) (CutCur.meanBall (V n) c)
      (CutCur.wasserstein2 · (CutCur.gibbs (V n))))
      (fun n => CutCur.criticalTime n (CutCur.spectralGap (V n))) ⊤ 0 := by
  obtain ⟨Ω, _, B, P, X, hP, hrig, key⟩ := CutCur.C2U.exists_isRigidSequence_of_K2 h
  have hcut := wasserstein_cutoff_carrier hrig hc
  exact CutCur.hasCutoff_congr_eventually
    (CutCur.eventually_worst_eq_worstK key (fun n => CutCur.meanBall (V n) c)
      (fun n => (CutCur.wasserstein2 · (CutCur.gibbs (V n))))) hcut

/-- **Wasserstein contraction**, kernel form (no Brownian motion). -/
theorem langevin_w2_contraction_C2 {d : ℕ} {V : CutCur.Rd d → ℝ}
    {Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d)}
    (hL : CutCur.C2U.IsEucLangevin2 V Pt) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν₁ ν₂ : Measure (CutCur.Rd d)) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (t : ℝ≥0) :
    CutCur.wasserstein2 (ν₁.bind (Pt t)) (ν₂.bind (Pt t)) ≤
      ENNReal.ofReal (Real.exp (-ρ * t)) * CutCur.wasserstein2 ν₁ ν₂ := by
  have hcv : ∀ x z : CutCur.Rd d, 0 ≤ fderiv ℝ (fderiv ℝ V) x z z := fun x z =>
    le_trans (mul_nonneg hρ (sq_nonneg _)) (hHess x z)
  obtain ⟨Ω, _, B, P, X, hP, hLang, key⟩ := CutCur.C2U.exists_isLangevin_of_C2 hL hcv
  have := langevin_w2_contraction_carrier hLang hρ hHess ν₁ ν₂ t
  have e : (fun x => P.map (X x t)) = ⇑(Pt t) := funext fun x => key t x
  simpa only [e] using this

/-- **Entropy decay and regularization, kernel form.** -/
theorem langevin_entropy_decay_C2 {d : ℕ} {V : CutCur.Rd d → ℝ}
    {Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d)} (hL : CutCur.C2U.IsEucLangevin2 V Pt)
    (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (CutCur.Rd d)) [IsProbabilityMeasure ν] :
    let H := fun t : ℝ≥0 => InformationTheory.klDiv (ν.bind (Pt t)) (CutCur.gibbs V)
    let I := fun t : ℝ≥0 => CutCur.fisherInfo V (ν.bind (Pt t))
    let W := CutCur.wasserstein2 ν (CutCur.gibbs V) ^ 2
    (∀ s t : ℝ≥0, s ≤ t → H t ≤ ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - s))) * H s) ∧
      (∀ t : ℝ≥0, 0 < t →
        H t ≤ ENNReal.ofReal (ρ * Real.exp (-2 * ρ * t) / (1 - Real.exp (-2 * ρ * t))) * W ∧
        ENNReal.ofReal (ρ * Real.exp (-2 * ρ * t) / (1 - Real.exp (-2 * ρ * t))) * W ≤
          ENNReal.ofReal (1 / (2 * (t : ℝ))) * W) ∧
      (∀ t : ℝ≥0, 1 ≤ t →
        2 * H t ≤ ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - 1))) * W ∧
        ENNReal.ofReal (CutCur.tvDist (ν.bind (Pt t)) (CutCur.gibbs V) ^ 2) ≤
          ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - 1)) / 4) * W) ∧
      (∀ s t : ℝ≥0, s ≤ t → I t ≤ I s) ∧
      (∀ s t : ℝ≥0, 0 < t → I (s + t) ≤ H s / ENNReal.ofReal t) ∧
      (∀ t₀ t₁ : ℝ≥0, 1 ≤ t₀ → t₀ < t₁ →
        I t₁ ≤ ENNReal.ofReal (Real.exp (-2 * ρ * ((t₀ : ℝ) - 1)) / (2 * ((t₁ : ℝ) - t₀))) * W) := by
  intro H I W
  obtain ⟨Ω, _, B, P, X, -, hLang, key⟩ :=
    CutCur.C2U.exists_isLangevin_of_C2 hL (hess_nonneg_of_rate hρ hHess)
  have hb : ∀ t : ℝ≥0, (fun x => P.map (X x t)) = ⇑(Pt t) := fun t => funext fun x => key t x
  have h := langevin_entropy_decay_carrier hLang hd hρ hHess ν
  simp only [hb] at h
  exact h

/-- **Fisher information decay, kernel form.** -/
theorem langevin_fisher_decay_C2 {d : ℕ} {V : CutCur.Rd d → ℝ}
    {Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d)} (hL : CutCur.C2U.IsEucLangevin2 V Pt)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (CutCur.Rd d)) [IsProbabilityMeasure ν] :
    ∀ s t : ℝ≥0, s ≤ t →
      CutCur.fisherInfo V (ν.bind (Pt t)) ≤
        ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - s))) *
          CutCur.fisherInfo V (ν.bind (Pt s)) := by
  obtain ⟨Ω, _, B, P, X, -, hLang, key⟩ :=
    CutCur.C2U.exists_isLangevin_of_C2 hL (hess_nonneg_of_rate hρ hHess)
  have hb : ∀ t : ℝ≥0, (fun x => P.map (X x t)) = ⇑(Pt t) := fun t => funext fun x => key t x
  have h := langevin_fisher_decay_carrier hLang hρ hHess ν
  simp only [hb] at h
  exact h

/-- **Upper Dini form of `∂ₜ I ≤ -2ρ I`, kernel form.** -/
theorem langevin_fisher_dini_C2 {d : ℕ} {V : CutCur.Rd d → ℝ}
    {Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d)} (hL : CutCur.C2U.IsEucLangevin2 V Pt)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (CutCur.Rd d)) [IsProbabilityMeasure ν] (t : ℝ≥0)
    (ht : CutCur.fisherInfo V (ν.bind (Pt t)) ≠ ⊤) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ),
      ((CutCur.fisherInfo V (ν.bind (Pt (t + h.toNNReal)))).toReal -
          (CutCur.fisherInfo V (ν.bind (Pt t))).toReal) / h ≤
        -2 * ρ * (CutCur.fisherInfo V (ν.bind (Pt t))).toReal + ε := by
  obtain ⟨Ω, _, B, P, X, -, hLang, key⟩ :=
    CutCur.C2U.exists_isLangevin_of_C2 hL (hess_nonneg_of_rate hρ hHess)
  have hb : ∀ t : ℝ≥0, (fun x => P.map (X x t)) = ⇑(Pt t) := fun t => funext fun x => key t x
  have ht' : CutCur.fisherInfo V (ν.bind fun x => P.map (X x t)) ≠ ⊤ := by
    rw [hb]; exact ht
  have h := langevin_fisher_dini_carrier hLang hρ hHess ν t ht' ε hε
  simp only [hb] at h
  exact h

/-- **Corollary 1.4**, kernel form. -/
theorem information_cutoff_C2 {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    (h : CutCur.C2U.IsRigidSeqK2 V Pt)
    (hsmall : (fun n => spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n)) {c : ℝ} (hc : 0 < c) :
    let t := fun n => CutCur.criticalTime n (spectralGap (V n))
    let S := fun n => meanBall (V n) c
    HasCutoff (fun n => worstK (Pt n) (S n) (fisherInfo (V n))) t ⊤ 0 ∧
    HasCutoff (fun n => worstK (Pt n) (S n) (InformationTheory.klDiv · (gibbs (V n)))) t ⊤ 0 ∧
    HasCutoff (fun n => worstK (Pt n) (S n) (fun ν => .ofReal (tvDist ν (gibbs (V n))))) t 1 0 := by
  intro t S
  obtain ⟨Ω, _, B, P, X, hP, hrig, key⟩ := CutCur.C2U.exists_isRigidSequence_of_K2 h
  obtain ⟨h1, h2, h3⟩ := information_cutoff_carrier hrig hsmall hc
  exact ⟨hasCutoff_congr_eventually (eventually_worst_eq_worstK key S _) h1,
    hasCutoff_congr_eventually (eventually_worst_eq_worstK key S _) h2,
    hasCutoff_congr_eventually (eventually_worst_eq_worstK key S _) h3⟩

/-- **Display (1.25)**, kernel form. -/
theorem lp_cutoff_C2 {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    (h : CutCur.C2U.IsRigidSeqK2 V Pt)
    (hsmall : (fun n => spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n))
    {c : ℝ} (hc : 0 < c) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) :
    HasCutoff (fun n => worstK (Pt n) (meanBall (V n) c) (relLp · (gibbs (V n)) p))
      (fun n => CutCur.criticalTime n (spectralGap (V n))) (if p = 1 then 2 else ⊤) 0 := by
  obtain ⟨Ω, _, B, P, X, hP, hrig, key⟩ := CutCur.C2U.exists_isRigidSequence_of_K2 h
  exact hasCutoff_congr_eventually (eventually_worst_eq_worstK key (fun n => meanBall (V n) c) _)
    (lp_cutoff_carrier hrig hsmall hc hp hpt)

/-- **Corollary 1.6**, kernel form, `C²` interaction (`W n ∈ C²`) and `C²` Langevin potential. -/
theorem convex_interaction_cutoff_C2 {ρ : ℝ}
    (hρ : 0 < ρ) {W : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    (hW : ∀ n, 0 < n → ContDiff ℝ 2 (W n) ∧ ConvexOn ℝ univ (W n) ∧
      ∀ x (s : ℝ), W n (x + s • diagonal n) = W n x)
    (hL : ∀ n, 0 < n → CutCur.C2U.IsEucLangevin2 (fun x => ρ / 2 * ‖x‖ ^ 2 + W n x) (Pt n))
    {c : ℝ} (hc : 0 < c) :
    let V := fun n (x : Rd n) => ρ / 2 * ‖x‖ ^ 2 + W n x
    let t := fun n : ℕ => CutCur.criticalTime n ρ
    ∀ cube : Bool,
      let S := fun n => if cube then meanCube (V n) c else meanBall (V n) c
      HasCutoff (fun n => worstK (Pt n) (S n) (wasserstein2 · (gibbs (V n)))) t ⊤ 0 ∧
      HasCutoff (fun n => worstK (Pt n) (S n) (fisherInfo (V n))) t ⊤ 0 ∧
      HasCutoff (fun n => worstK (Pt n) (S n)
        (InformationTheory.klDiv · (gibbs (V n)))) t ⊤ 0 ∧
      HasCutoff (fun n => worstK (Pt n) (S n)
        (fun ν => .ofReal (tvDist ν (gibbs (V n))))) t 1 0 := by
  intro V t cube S
  have hHess : ∀ n, 0 < n → ∀ x z : Rd n, 0 ≤ fderiv ℝ (fderiv ℝ (V n)) x z z := by
    intro n hn x z
    have := hessian_quadratic_add_convex_lower (hW n hn).1
      (hW n hn).2.1 ρ x z
    exact le_trans (mul_nonneg hρ.le (sq_nonneg _)) this
  obtain ⟨Ω, _, B, P, X, hLang, key⟩ :=
    CutCur.C2U.exists_langevinSeq_of_K2 (V := V) (Pt := Pt) fun n hn => ⟨hL n hn, hHess n hn⟩
  have := convex_interaction_cutoff_carrier hρ hW hLang hc cube
  obtain ⟨h1, h2, h3, h4⟩ := this
  exact ⟨hasCutoff_congr_eventually (eventually_worst_eq_worstK key S _) h1,
    hasCutoff_congr_eventually (eventually_worst_eq_worstK key S _) h2,
    hasCutoff_congr_eventually (eventually_worst_eq_worstK key S _) h3,
    hasCutoff_congr_eventually (eventually_worst_eq_worstK key S _) h4⟩

/-- **Theorem 1.7**, kernel form. -/
theorem product_condition_cutoff_C2
    {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    {κ : ℕ → ℝ} {S : ∀ n, Set (Rd n)} {η : ℝ}
    (hL : ∀ n, 0 < n → CutCur.C2U.IsEucLangevin2 (V n) (Pt n) ∧ 0 < κ n ∧
      ∀ x z : Rd n, κ n * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (V n)) x z z)
    (hS : ∀ n, 0 < n → (S n).Nonempty) (hη : 0 < η) (hη1 : η < 1) :
    let t₀ := fun n => mixingTimeK (Pt n) (gibbs (V n)) (S n) η
    let prof := fun (δ : ∀ n, Measure (Rd n) → ℝ≥0∞) n => worstK (Pt n) (S n) (δ n)
    (∀ᶠ n in atTop, t₀ n < ⊤) → Tendsto (fun n => κ n * (t₀ n).toReal) atTop atTop →
      (HasCutoff (prof fun n ν => .ofReal (tvDist ν (gibbs (V n))))
          (fun n => (t₀ n).toReal) 1 0 ∧
        HasCutoff (prof fun n ν => InformationTheory.klDiv ν (gibbs (V n)))
          (fun n => (t₀ n).toReal) ⊤ 0) ∧
      (0 < liminf (fun n => ENNReal.ofReal (κ n)) atTop →
        Tendsto (fun n => (t₀ n).toReal) atTop atTop →
        HasCutoff (prof fun n => fisherInfo (V n)) (fun n => (t₀ n).toReal) ⊤ 0 ∧
        HasCutoff (prof fun n ν => wasserstein2 ν (gibbs (V n))) (fun n => (t₀ n).toReal) ⊤ 0) := by
  intro t₀ prof hfin hprod
  have hHess : ∀ n, 0 < n → ∀ x z : Rd n, 0 ≤ fderiv ℝ (fderiv ℝ (V n)) x z z := fun n hn x z =>
    le_trans (mul_nonneg (hL n hn).2.1.le (sq_nonneg _)) ((hL n hn).2.2 x z)
  obtain ⟨Ω, _, B, P, X, hLang, key⟩ :=
    CutCur.C2U.exists_langevinSeq_of_K2 (V := V) (Pt := Pt) fun n hn => ⟨(hL n hn).1, hHess n hn⟩
  have hev : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have ht : ∀ᶠ n in atTop, mixingTime (P n) (X n) (gibbs (V n)) (S n) η = t₀ n := by
    filter_upwards [hev] with n hn
    exact mixingTime_eq_mixingTimeK (key n hn) _ _ _
  have hL' : ∀ n, 0 < n → IsLangevin (V n) (B n) (P n) (X n) ∧ 0 < κ n ∧
      ∀ x z : Rd n, κ n * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (V n)) x z z := fun n hn =>
    ⟨hLang n hn, (hL n hn).2⟩
  have hfin' : ∀ᶠ n in atTop, mixingTime (P n) (X n) (gibbs (V n)) (S n) η < ⊤ := by
    filter_upwards [hfin, ht] with n h h' using h'.symm ▸ h
  have hprod' : Tendsto (fun n => κ n *
      (mixingTime (P n) (X n) (gibbs (V n)) (S n) η).toReal) atTop atTop :=
    hprod.congr' (by filter_upwards [ht] with n h' using by simp only [h'])
  have tcongr : ∀ {p q : ℕ → ℝ → ℝ≥0∞} {a b : ℝ≥0∞},
      (∀ᶠ n in atTop, p n = q n) → HasCutoff p (fun n => (mixingTime (P n) (X n) (gibbs (V n)) (S n) η).toReal) a b →
        HasCutoff q (fun n => (t₀ n).toReal) a b := by
    intro p q a b hpq hp ε h0 h1
    obtain ⟨u, v⟩ := hp ε h0 h1
    exact ⟨u.congr' (by filter_upwards [hpq, ht] with n hn h'; simp only [hn, h']),
      v.congr' (by filter_upwards [hpq, ht] with n hn h'; simp only [hn, h'])⟩
  have key' := product_condition_cutoff_carrier hL' hS hη hη1 hfin' hprod'
  obtain ⟨⟨a1, a2⟩, a3⟩ := key'
  refine ⟨⟨?_, ?_⟩, fun hl hT => ?_⟩
  · exact tcongr (eventually_worst_eq_worstK key S (fun n ν => ENNReal.ofReal (tvDist ν (gibbs (V n))))) a1
  · exact tcongr (eventually_worst_eq_worstK key S (fun n ν => InformationTheory.klDiv ν (gibbs (V n)))) a2
  · have hT' : Tendsto (fun n => (mixingTime (P n) (X n) (gibbs (V n)) (S n) η).toReal)
        atTop atTop := hT.congr' (by filter_upwards [ht] with n h' using by simp only [h'])
    obtain ⟨b1, b2⟩ := a3 hl hT'
    exact ⟨tcongr (eventually_worst_eq_worstK key S (fun n => fisherInfo (V n))) b1,
      tcongr (eventually_worst_eq_worstK key S (fun n ν => wasserstein2 ν (gibbs (V n)))) b2⟩

/-- **Mixing time of rigid sequences**, kernel form. -/
theorem mixing_time_rigid_C2 {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    (h : CutCur.C2U.IsRigidSeqK2 V Pt)
    (hsmall : (fun n => spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n))
    {c : ℝ} (hc : 0 < c) {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    let t₀ := fun n => mixingTimeK (Pt n) (gibbs (V n)) (meanBall (V n) c) η
    (∀ᶠ n in atTop, t₀ n < ⊤) ∧
      Tendsto (fun n => (t₀ n).toReal / CutCur.criticalTime n (spectralGap (V n))) atTop (𝓝 1) ∧
      Tendsto (fun n => spectralGap (V n) * (t₀ n).toReal) atTop atTop ∧
      Tendsto (fun n => (t₀ n).toReal) atTop atTop := by
  intro t₀
  obtain ⟨Ω, _, B, P, X, hP, hrig, key⟩ := CutCur.C2U.exists_isRigidSequence_of_K2 h
  have := mixing_time_rigid_carrier hrig hsmall hc hη hη1
  have hev : ∀ᶠ n in atTop, mixingTime (P n) (X n) (gibbs (V n)) (meanBall (V n) c) η = t₀ n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact mixingTime_eq_mixingTimeK (key n hn) _ _ _
  obtain ⟨a, b, c', d⟩ := this
  exact (mixing_conclusion_congr hev ⟨⟨a, b, c'⟩, d⟩ |> fun r => ⟨r.1.1, r.1.2.1, r.1.2.2, r.2⟩)

/-- **Wasserstein mixing time of rigid sequences**, kernel form. -/
theorem mixing_time_w2_rigid_C2 {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    (h : CutCur.C2U.IsRigidSeqK2 V Pt) {c : ℝ} (hc : 0 < c) {η : ℝ} (hη : 0 < η) :
    let t₀ := fun n => mixingTimeW2K (Pt n) (gibbs (V n)) (meanBall (V n) c) η
    (∀ᶠ n in atTop, t₀ n < ⊤) ∧
      Tendsto (fun n => (t₀ n).toReal / CutCur.criticalTime n (spectralGap (V n))) atTop (𝓝 1) ∧
      Tendsto (fun n => spectralGap (V n) * (t₀ n).toReal) atTop atTop ∧
      ((fun n => spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n) →
        Tendsto (fun n => (t₀ n).toReal) atTop atTop) := by
  intro t₀
  obtain ⟨Ω, _, B, P, X, hP, hrig, key⟩ := CutCur.C2U.exists_isRigidSequence_of_K2 h
  obtain ⟨a, b, c', d⟩ := mixing_time_w2_rigid_carrier hrig hc hη
  have hev : ∀ᶠ n in atTop, mixingTimeW2 (P n) (X n) (gibbs (V n)) (meanBall (V n) c) η = t₀ n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact mixingTimeW2_eq_mixingTimeW2K (key n hn) _ _ _
  refine ⟨?_, ?_, ?_, fun hs => ?_⟩
  · filter_upwards [a, hev] with n h h' using h' ▸ h
  · exact b.congr' (by filter_upwards [hev] with n h' using by simp only [h'])
  · exact c'.congr' (by filter_upwards [hev] with n h' using by simp only [h'])
  · exact (d hs).congr' (by filter_upwards [hev] with n h' using by simp only [h'])

/-- **Entropy mixing time of rigid sequences**, kernel form. -/
theorem mixing_time_kl_rigid_C2 {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    (h : CutCur.C2U.IsRigidSeqK2 V Pt)
    (hsmall : (fun n => spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n))
    {c : ℝ} (hc : 0 < c) {η : ℝ} (hη : 0 < η) :
    let t₀ := fun n => mixingTimeKLK (Pt n) (gibbs (V n)) (meanBall (V n) c) η
    (∀ᶠ n in atTop, t₀ n < ⊤) ∧
      Tendsto (fun n => (t₀ n).toReal / CutCur.criticalTime n (spectralGap (V n))) atTop (𝓝 1) ∧
      Tendsto (fun n => spectralGap (V n) * (t₀ n).toReal) atTop atTop ∧
      Tendsto (fun n => (t₀ n).toReal) atTop atTop := by
  intro t₀
  obtain ⟨Ω, _, B, P, X, hP, hrig, key⟩ := CutCur.C2U.exists_isRigidSequence_of_K2 h
  have := mixing_time_kl_rigid_carrier hrig hsmall hc hη
  have hev : ∀ᶠ n in atTop, mixingTimeKL (P n) (X n) (gibbs (V n)) (meanBall (V n) c) η = t₀ n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact mixingTimeKL_eq_mixingTimeKLK (key n hn) _ _ _
  obtain ⟨a, b, c', d⟩ := this
  exact (mixing_conclusion_congr hev ⟨⟨a, b, c'⟩, d⟩ |> fun r => ⟨r.1.1, r.1.2.1, r.1.2.2, r.2⟩)

/-- **Remark 3.4**, kernel form. -/
theorem wasserstein_cutoff_weak_C2 {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    (hL : ∀ n, 0 < n → CutCur.C2U.IsEucLangevin2 (V n) (Pt n) ∧ RigidCurvature (V n))
    (hgap : ∃ α : ℝ, 0 < α ∧
      ∀ᶠ n : ℕ in atTop, (spectralGap (V n))⁻¹ ≤ (Real.log n) ^ α)
    {c : ℝ} (hc : 0 < c) :
    HasCutoff (fun n => worstK (Pt n) (meanBall (V n) c)
      (wasserstein2 · (gibbs (V n))))
      (fun n => CutCur.criticalTime n (spectralGap (V n))) ⊤ 0 := by
  obtain ⟨Ω, _, B, P, X, hLang, key⟩ := CutCur.C2U.exists_langevinSeq_of_K2
    (fun n hn => ⟨(hL n hn).1, (hL n hn).2.hess_nonneg⟩)
  exact hasCutoff_congr_eventually
    (eventually_worst_eq_worstK key (fun n => meanBall (V n) c)
      (fun n => (wasserstein2 · (gibbs (V n)))))
    (wasserstein_cutoff_weak_carrier (fun n hn => ⟨hLang n hn, (hL n hn).2⟩) hgap hc)

/-- **Remark 3.5**, kernel form. -/
theorem information_cutoff_weak_C2 {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    (h : CutCur.C2U.IsRigidSeqK2 V Pt)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, spectralGap (V n) ≤ (n : ℝ) ^ ε)
    {c : ℝ} (hc : 0 < c) :
    let t := fun n => CutCur.criticalTime n (spectralGap (V n))
    let S := fun n => meanBall (V n) c
    HasCutoff (fun n => worstK (Pt n) (S n) (fisherInfo (V n))) t ⊤ 0 ∧
    HasCutoff (fun n => worstK (Pt n) (S n) (InformationTheory.klDiv · (gibbs (V n)))) t ⊤ 0 ∧
    HasCutoff (fun n => worstK (Pt n) (S n) (fun ν => .ofReal (tvDist ν (gibbs (V n))))) t 1 0 := by
  intro t S
  obtain ⟨Ω, _, B, P, X, hP, hrig, key⟩ := CutCur.C2U.exists_isRigidSequence_of_K2 h
  obtain ⟨h1, h2, h3⟩ := information_cutoff_weak_carrier hrig hsmall hc
  exact ⟨hasCutoff_congr_eventually (eventually_worst_eq_worstK key S _) h1,
    hasCutoff_congr_eventually (eventually_worst_eq_worstK key S _) h2,
    hasCutoff_congr_eventually (eventually_worst_eq_worstK key S _) h3⟩

end CutoffRigidity.Paper
