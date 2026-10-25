module

public import CutoffRigidity.Paper.CarrierDefs
public import CutoffRigidity.Extra.EuclideanDiffusion
public import CutoffRigidity.Extra.MixingTimeW2KL
public import CutoffRigidity.Paper.ProductCondition
public import CutoffRigidity.Paper.LpCutoff
public import CutoffRigidity.ConvexInteractionCurvature

/-! # Brownian-free cutoff theorems (kernel formulation)

Kernel versions `*_K` of `information_cutoff_carrier`, `lp_cutoff_carrier`, `convex_interaction_cutoff_carrier`,
`product_condition_cutoff_carrier`, `mixing_time_rigid_carrier`, `mixing_time_w2_rigid_carrier`, `mixing_time_kl_rigid_carrier`,
with the Brownian carrier `(Ω, B, P, X)` replaced by kernels `Pt` (`IsRigidSequenceK`,
`IsEuclideanLangevin`), proved from the Brownian-based theorems through the transfer lemmas of
`CutoffRigidity.Extra.EuclideanDiffusion`.
-/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Set CutCur
open scoped ENNReal NNReal Topology Asymptotics ContDiff

/-- Sequence transfer for sequences that are not necessarily rigid: carriers for positive
dimensions with `IsLangevin` and the prescribed laws, from convex smooth Euclidean Langevin
semigroups. -/
theorem exists_langevinSeq_of_K {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    (h : ∀ n, 0 < n → IsEuclideanLangevin (V n) (Pt n) ∧
      ∀ x z : Rd n, 0 ≤ fderiv ℝ (fderiv ℝ (V n)) x z z) :
    ∃ (Ω : ℕ → Type) (_ : ∀ n, MeasurableSpace (Ω n)) (B : ∀ n, ℝ≥0 → Ω n → Rd n)
      (P : ∀ n, Measure (Ω n)) (X : ∀ n, Rd n → ℝ≥0 → Ω n → Rd n),
      (∀ n, 0 < n → IsLangevin (V n) (B n) (P n) (X n)) ∧
        ∀ n, 0 < n → ∀ (t : ℝ≥0) (x₀ : Rd n), (P n).map (X n x₀ t) = Pt n t x₀ := by
  classical
  have hn : ∀ n : ℕ, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (B : ℝ≥0 → Ω → Rd n) (P : Measure Ω)
      (X : Rd n → ℝ≥0 → Ω → Rd n), 0 < n → (IsLangevin (V n) B P X ∧
        ∀ (t : ℝ≥0) (x₀ : Rd n), P.map (X x₀ t) = Pt n t x₀) := by
    intro n
    by_cases hn : 0 < n
    · obtain ⟨Ω, hΩ, B, P, X, -, h1, h2⟩ :=
        exists_isLangevin_of_isEuclideanLangevin (h n hn).1 (h n hn).2
      exact ⟨Ω, hΩ, B, P, X, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨Unit, inferInstance, fun _ _ => 0, 0, fun _ _ _ => 0, fun h' => absurd h' hn⟩
  choose Ω hΩ B P X hX using hn
  exact ⟨Ω, hΩ, B, P, X, fun n hn => (hX n hn).1, fun n hn => (hX n hn).2⟩

/-- **Corollary 1.4**, kernel form. -/
theorem information_cutoff_K {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    (h : IsRigidSequenceK V Pt)
    (hsmall : (fun n => spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n)) {c : ℝ} (hc : 0 < c) :
    let t := fun n => CutCur.criticalTime n (spectralGap (V n))
    let S := fun n => meanBall (V n) c
    HasCutoff (fun n => worstK (Pt n) (S n) (fisherInfo (V n))) t ⊤ 0 ∧
    HasCutoff (fun n => worstK (Pt n) (S n) (InformationTheory.klDiv · (gibbs (V n)))) t ⊤ 0 ∧
    HasCutoff (fun n => worstK (Pt n) (S n) (fun ν => .ofReal (tvDist ν (gibbs (V n))))) t 1 0 := by
  intro t S
  obtain ⟨Ω, _, B, P, X, hP, hrig, key⟩ := exists_isRigidSequence_of_K h
  obtain ⟨h1, h2, h3⟩ := information_cutoff_carrier hrig hsmall hc
  exact ⟨hasCutoff_congr_eventually (eventually_worst_eq_worstK key S _) h1,
    hasCutoff_congr_eventually (eventually_worst_eq_worstK key S _) h2,
    hasCutoff_congr_eventually (eventually_worst_eq_worstK key S _) h3⟩

/-- **Display (1.25)**, kernel form. -/
theorem lp_cutoff_K {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    (h : IsRigidSequenceK V Pt)
    (hsmall : (fun n => spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n))
    {c : ℝ} (hc : 0 < c) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) :
    HasCutoff (fun n => worstK (Pt n) (meanBall (V n) c) (relLp · (gibbs (V n)) p))
      (fun n => CutCur.criticalTime n (spectralGap (V n))) (if p = 1 then 2 else ⊤) 0 := by
  obtain ⟨Ω, _, B, P, X, hP, hrig, key⟩ := exists_isRigidSequence_of_K h
  exact hasCutoff_congr_eventually (eventually_worst_eq_worstK key (fun n => meanBall (V n) c) _)
    (lp_cutoff_carrier hrig hsmall hc hp hpt)

/-- **Corollary 1.6**, kernel form. -/
theorem convex_interaction_cutoff_K {ρ : ℝ}
    (hρ : 0 < ρ) {W : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    (hW : ∀ n, 0 < n → ContDiff ℝ ∞ (W n) ∧ ConvexOn ℝ univ (W n) ∧
      ∀ x (s : ℝ), W n (x + s • diagonal n) = W n x)
    (hL : ∀ n, 0 < n → IsEuclideanLangevin (fun x => ρ / 2 * ‖x‖ ^ 2 + W n x) (Pt n))
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
    have := hessian_quadratic_add_convex_lower (((hW n hn).1).of_le (by norm_cast))
      (hW n hn).2.1 ρ x z
    exact le_trans (mul_nonneg hρ.le (sq_nonneg _)) this
  obtain ⟨Ω, _, B, P, X, hLang, key⟩ :=
    exists_langevinSeq_of_K (V := V) (Pt := Pt) fun n hn => ⟨hL n hn, hHess n hn⟩
  have hW2 : ∀ n, 0 < n → ContDiff ℝ 2 (W n) ∧ ConvexOn ℝ univ (W n) ∧
      ∀ x (s : ℝ), W n (x + s • diagonal n) = W n x := fun n hn =>
    ⟨((hW n hn).1).of_le (by norm_cast), (hW n hn).2⟩
  have := convex_interaction_cutoff_carrier hρ hW2 hLang hc cube
  obtain ⟨h1, h2, h3, h4⟩ := this
  exact ⟨hasCutoff_congr_eventually (eventually_worst_eq_worstK key S _) h1,
    hasCutoff_congr_eventually (eventually_worst_eq_worstK key S _) h2,
    hasCutoff_congr_eventually (eventually_worst_eq_worstK key S _) h3,
    hasCutoff_congr_eventually (eventually_worst_eq_worstK key S _) h4⟩

/-- **Theorem 1.7**, kernel form. -/
theorem product_condition_cutoff_K
    {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    {κ : ℕ → ℝ} {S : ∀ n, Set (Rd n)} {η : ℝ}
    (hL : ∀ n, 0 < n → IsEuclideanLangevin (V n) (Pt n) ∧ 0 < κ n ∧
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
    exists_langevinSeq_of_K (V := V) (Pt := Pt) fun n hn => ⟨(hL n hn).1, hHess n hn⟩
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

/-- Transfer of the four mixing-time conclusions across an eventual equality of the times. -/
theorem mixing_conclusion_congr {t₁ t₂ : ℕ → ℝ≥0∞} {g : ℕ → ℝ} {crit : ℕ → ℝ}
    (hev : ∀ᶠ n in atTop, t₁ n = t₂ n)
    (h : ((∀ᶠ n in atTop, t₁ n < ⊤) ∧ Tendsto (fun n => (t₁ n).toReal / crit n) atTop (𝓝 1) ∧
      Tendsto (fun n => g n * (t₁ n).toReal) atTop atTop) ∧
      Tendsto (fun n => (t₁ n).toReal) atTop atTop) :
    ((∀ᶠ n in atTop, t₂ n < ⊤) ∧ Tendsto (fun n => (t₂ n).toReal / crit n) atTop (𝓝 1) ∧
      Tendsto (fun n => g n * (t₂ n).toReal) atTop atTop) ∧
      Tendsto (fun n => (t₂ n).toReal) atTop atTop := by
  obtain ⟨⟨a, b, c⟩, d⟩ := h
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · filter_upwards [a, hev] with n h h' using h' ▸ h
  · exact b.congr' (by filter_upwards [hev] with n h' using by simp only [h'])
  · exact c.congr' (by filter_upwards [hev] with n h' using by simp only [h'])
  · exact d.congr' (by filter_upwards [hev] with n h' using by simp only [h'])

/-- **Mixing time of rigid sequences**, kernel form. -/
theorem mixing_time_rigid_K {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    (h : IsRigidSequenceK V Pt)
    (hsmall : (fun n => spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n))
    {c : ℝ} (hc : 0 < c) {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    let t₀ := fun n => mixingTimeK (Pt n) (gibbs (V n)) (meanBall (V n) c) η
    (∀ᶠ n in atTop, t₀ n < ⊤) ∧
      Tendsto (fun n => (t₀ n).toReal / CutCur.criticalTime n (spectralGap (V n))) atTop (𝓝 1) ∧
      Tendsto (fun n => spectralGap (V n) * (t₀ n).toReal) atTop atTop ∧
      Tendsto (fun n => (t₀ n).toReal) atTop atTop := by
  intro t₀
  obtain ⟨Ω, _, B, P, X, hP, hrig, key⟩ := exists_isRigidSequence_of_K h
  have := mixing_time_rigid_carrier hrig hsmall hc hη hη1
  have hev : ∀ᶠ n in atTop, mixingTime (P n) (X n) (gibbs (V n)) (meanBall (V n) c) η = t₀ n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact mixingTime_eq_mixingTimeK (key n hn) _ _ _
  obtain ⟨a, b, c', d⟩ := this
  exact (mixing_conclusion_congr hev ⟨⟨a, b, c'⟩, d⟩ |> fun r => ⟨r.1.1, r.1.2.1, r.1.2.2, r.2⟩)

/-- **Wasserstein mixing time of rigid sequences**, kernel form. -/
theorem mixing_time_w2_rigid_K {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    (h : IsRigidSequenceK V Pt) {c : ℝ} (hc : 0 < c) {η : ℝ} (hη : 0 < η) :
    let t₀ := fun n => mixingTimeW2K (Pt n) (gibbs (V n)) (meanBall (V n) c) η
    (∀ᶠ n in atTop, t₀ n < ⊤) ∧
      Tendsto (fun n => (t₀ n).toReal / CutCur.criticalTime n (spectralGap (V n))) atTop (𝓝 1) ∧
      Tendsto (fun n => spectralGap (V n) * (t₀ n).toReal) atTop atTop ∧
      ((fun n => spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n) →
        Tendsto (fun n => (t₀ n).toReal) atTop atTop) := by
  intro t₀
  obtain ⟨Ω, _, B, P, X, hP, hrig, key⟩ := exists_isRigidSequence_of_K h
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
theorem mixing_time_kl_rigid_K {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    (h : IsRigidSequenceK V Pt)
    (hsmall : (fun n => spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n))
    {c : ℝ} (hc : 0 < c) {η : ℝ} (hη : 0 < η) :
    let t₀ := fun n => mixingTimeKLK (Pt n) (gibbs (V n)) (meanBall (V n) c) η
    (∀ᶠ n in atTop, t₀ n < ⊤) ∧
      Tendsto (fun n => (t₀ n).toReal / CutCur.criticalTime n (spectralGap (V n))) atTop (𝓝 1) ∧
      Tendsto (fun n => spectralGap (V n) * (t₀ n).toReal) atTop atTop ∧
      Tendsto (fun n => (t₀ n).toReal) atTop atTop := by
  intro t₀
  obtain ⟨Ω, _, B, P, X, hP, hrig, key⟩ := exists_isRigidSequence_of_K h
  have := mixing_time_kl_rigid_carrier hrig hsmall hc hη
  have hev : ∀ᶠ n in atTop, mixingTimeKL (P n) (X n) (gibbs (V n)) (meanBall (V n) c) η = t₀ n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact mixingTimeKL_eq_mixingTimeKLK (key n hn) _ _ _
  obtain ⟨a, b, c', d⟩ := this
  exact (mixing_conclusion_congr hev ⟨⟨a, b, c'⟩, d⟩ |> fun r => ⟨r.1.1, r.1.2.1, r.1.2.2, r.2⟩)

-- Names of the Challenge theorems (kernel statements; the Brownian versions are `*_carrier`).
alias information_cutoff := information_cutoff_K
alias lp_cutoff := lp_cutoff_K
alias convex_interaction_cutoff := convex_interaction_cutoff_K
alias product_condition_cutoff := product_condition_cutoff_K
alias mixing_time_rigid := mixing_time_rigid_K
alias mixing_time_w2_rigid := mixing_time_w2_rigid_K
alias mixing_time_kl_rigid := mixing_time_kl_rigid_K

end CutoffRigidity.Paper
