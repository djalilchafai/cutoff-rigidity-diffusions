module

public import CutoffRigidity.Paper.CarrierDefs
public import CutoffRigidity.Paper.ConvexInteraction
public import CutoffRigidity.Paper.SeqData
public import CutoffRigidity.Paper.FisherBridge
public import CutoffRigidity.ConvexInteractionCutoffTheorem
public import CutoffRigidity.BarycenterFisherLowerCutoffs
public import CutoffRigidity.Paper.WassersteinCutoff

/-! # Corollary 1.6: cutoff for convex interactions on the statement surface -/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Set InformationTheory
open scoped ENNReal NNReal Topology Asymptotics

universe u

/-- One common probability space carrying Brownian drivers of every dimension with the given
path laws. -/
theorem exists_seqBrownian {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]
    {B : ∀ n, ℝ≥0 → Ω n → CutCur.Rd n} {P : ∀ n, Measure (Ω n)}
    (hB : ∀ n, 0 < n → IsEuclideanBrownian (B n) (P n)) :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (drv : ∀ n, ℝ≥0 → Ω' → CutCur.Rd n)
      (P' : Measure Ω'), (∀ n, IsEuclideanBrownian (drv n) P') ∧
        ∀ n, 0 < n → brownianNoiseLaw (drv n) P' = brownianNoiseLaw (B n) (P n) := by
  classical
  have hprob : ∀ m : ℕ, IsProbabilityMeasure (P (m + 1)) := fun m =>
    (hB (m + 1) (Nat.succ_pos m)).isProbabilityMeasure
  let P' : Measure (∀ m : ℕ, Ω (m + 1)) := Measure.infinitePi fun m => P (m + 1)
  have : IsProbabilityMeasure P' := inferInstance
  refine ⟨∀ m : ℕ, Ω (m + 1), inferInstance, fun n =>
    match n with
    | 0 => fun _ _ => 0
    | m + 1 => fun t ω => B (m + 1) t (ω m), P', fun n => ?_, fun n hn => ?_⟩
  · rcases n with _ | m
    · exact ⟨fun i => i.elim0, iIndepFun.of_subsingleton⟩
    · exact isEuclideanBrownian_comp_measurePreserving
        (f := fun ω : (∀ m : ℕ, Ω (m + 1)) => ω m)
        (measurePreserving_eval_infinitePi (fun m => P (m + 1)) m) (hB (m + 1) (Nat.succ_pos m))
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact brownianNoiseLaw_comp (f := fun ω : (∀ m : ℕ, Ω (m + 1)) => ω m)
      (measurePreserving_eval_infinitePi (fun m => P (m + 1)) m) (hB (m + 1) (Nat.succ_pos m))

section Normalization

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- If the Gibbs measure of the interaction potential is already a probability measure, the
library normalization constant vanishes. -/
theorem cubeSpectralData_potential_eq (D : ConvexInteractionCubeData Ω d)
    (hp : IsProbabilityMeasure
      (gibbsMeasure volume (fun x : EuclideanSpace ℝ (Fin d) => D.rate / 2 * ‖x‖ ^ 2 + D.interaction x))) :
    (cubeSpectralData D).potential =
      fun x : EuclideanSpace ℝ (Fin d) => D.rate / 2 * ‖x‖ ^ 2 + D.interaction x := by
  obtain ⟨hint, -⟩ := convexInteraction_partition_finite_positive D.smooth D.convex D.rate D.rate_pos
  have hZ : (∫ x : EuclideanSpace ℝ (Fin d),
      Real.exp (-(D.rate / 2 * ‖x‖ ^ 2 + D.interaction x))) = 1 := by
    have h1 : gibbsMeasure volume
        (fun x : EuclideanSpace ℝ (Fin d) => D.rate / 2 * ‖x‖ ^ 2 + D.interaction x) Set.univ = 1 :=
      hp.measure_univ
    rw [gibbsMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => (Real.exp_pos _).le)]
      at h1
    exact (ENNReal.ofReal_eq_one.mp h1)
  change (fun x : EuclideanSpace ℝ (Fin d) => D.rate / 2 * ‖x‖ ^ 2 +
    (D.interaction x + Real.log (∫ x : EuclideanSpace ℝ (Fin d),
      Real.exp (-(D.rate / 2 * ‖x‖ ^ 2 + D.interaction x))))) = _
  rw [hZ, Real.log_one]
  simp

end Normalization

theorem langevinKernel_congr_noise {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {d : ℕ} (V : CutCur.Rd d → ℝ) {B₁ : ℝ≥0 → Ω₁ → CutCur.Rd d} {P₁ : Measure Ω₁}
    {B₂ : ℝ≥0 → Ω₂ → CutCur.Rd d} {P₂ : Measure Ω₂}
    (h : brownianNoiseLaw B₁ P₁ = brownianNoiseLaw B₂ P₂) (t : ℝ≥0) :
    langevinKernel V B₁ P₁ t = langevinKernel V B₂ P₂ t := by
  unfold langevinKernel
  rw [h]

section Profiles

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ}

theorem worst_kl_set (D : SpectralInformationLowerData Ω' d) (S : Set (CutCur.Rd d))
    {P : Measure Ω} {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d}
    (hk : ∀ (t : ℝ≥0) (x : CutCur.Rd d), langevinKernel D.potential D.driver D.noiseLaw t x =
      P.map (X x t)) (t : ℝ) :
    CutCur.worst P X S (InformationTheory.klDiv · (CutCur.gibbs D.potential)) t =
      ⨆ x : S, klDiv (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
        (gibbsMeasure volume D.potential) := by
  unfold CutCur.worst
  rw [iSup_subtype']
  refine iSup_congr fun x => ?_
  rw [← hk t.toNNReal x.1]
  rfl

theorem worst_fisher_set (D : SpectralInformationLowerData Ω' d) (S : Set (CutCur.Rd d))
    {P : Measure Ω} {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d}
    (hk : ∀ (t : ℝ≥0) (x : CutCur.Rd d), langevinKernel D.potential D.driver D.noiseLaw t x =
      P.map (X x t)) (t : ℝ) :
    CutCur.worst P X S (CutCur.fisherInfo D.potential) t = spectralSetFisher D S t := by
  have := D.probability
  have := langevinKernel_isMarkovKernel D.brownian D.smooth D.rate D.rate_pos.le D.hessian
    t.toNNReal
  unfold CutCur.worst spectralSetFisher
  rw [iSup_subtype']
  refine iSup_congr fun x => ?_
  rw [← hk t.toNNReal x.1]
  exact fisherInfo_eq_relativeFisherInformation D.smooth D.probability D.rate D.rate_pos D.hessian _

theorem worst_tv_set (D : SpectralInformationLowerData Ω' d) {S : Set (CutCur.Rd d)}
    (hS : S.Nonempty) {P : Measure Ω} {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d}
    (hk : ∀ (t : ℝ≥0) (x : CutCur.Rd d), langevinKernel D.potential D.driver D.noiseLaw t x =
      P.map (X x t)) (t : ℝ) :
    CutCur.worst P X S
      (fun ν => ENNReal.ofReal (CutCur.tvDist ν (CutCur.gibbs D.potential))) t =
        ENNReal.ofReal (projectedSetTV (spectralInformationToAffine D) S t) := by
  let tv := fun x => totalVariationDistance
    (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x) (gibbsMeasure volume D.potential)
  have hf : Monotone ENNReal.ofReal := fun a b hab => ENNReal.ofReal_le_ofReal hab
  have hcs := hf.map_csSup_of_continuousAt ENNReal.continuous_ofReal.continuousAt (hS.image tv)
    (projectedSetTV_bddAbove (spectralInformationToAffine D) S t)
  unfold CutCur.worst projectedSetTV
  rw [iSup_subtype']
  change _ = ENNReal.ofReal (sSup (tv '' S))
  rw [hcs, Set.image_image, sSup_image']
  refine iSup_congr fun x => ?_
  rw [← hk t.toNNReal x.1]
  beta_reduce
  rw [tvDist_eq_totalVariationDistance]
  rfl

theorem worst_wasserstein_set (D : SpectralInformationLowerData Ω' d) (S : Set (CutCur.Rd d))
    {P : Measure Ω} {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d}
    (hk : ∀ (t : ℝ≥0) (x : CutCur.Rd d), langevinKernel D.potential D.driver D.noiseLaw t x =
      P.map (X x t)) (t A : ℝ) (hA : 0 ≤ A)
    (hSup : ENNReal.ofReal A = ⨆ x : S, squaredWasserstein
      (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x) (gibbsMeasure volume D.potential)) :
    CutCur.worst P X S (CutCur.wasserstein2 · (CutCur.gibbs D.potential)) t =
      ENNReal.ofReal (Real.sqrt A) := by
  rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hA (by norm_num), hSup]
  have hmap := (ENNReal.orderIsoRpow (1 / 2) (by norm_num)).map_iSup
    (fun x : S => squaredWasserstein
      (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x) (gibbsMeasure volume D.potential))
  unfold CutCur.worst
  rw [iSup_subtype']
  refine Eq.trans (iSup_congr fun x => ?_) hmap.symm
  rw [← hk t.toNNReal x.1]
  beta_reduce
  rw [wasserstein2_eq_rpow]
  rfl

end Profiles

/-- Assembly of the four cutoffs from profile identifications and library limits. -/
theorem assemble_cutoffs {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {V : ∀ n, CutCur.Rd n → ℝ} {P : ∀ n, Measure (Ω n)}
    {X : ∀ n, CutCur.Rd n → ℝ≥0 → Ω n → CutCur.Rd n} {S : ∀ n, Set (CutCur.Rd n)} {ρ : ℝ}
    (LW LT : ℕ → ℝ → ℝ) (LK LF : ℕ → ℝ → ℝ≥0∞)
    (hW : ∀ n, 0 < n → ∀ s, CutCur.worst (P n) (X n) (S n)
      (CutCur.wasserstein2 · (CutCur.gibbs (V n))) s = ENNReal.ofReal (LW n s))
    (hK : ∀ n, 0 < n → ∀ s, CutCur.worst (P n) (X n) (S n)
      (InformationTheory.klDiv · (CutCur.gibbs (V n))) s = LK n s)
    (hF : ∀ n, 0 < n → ∀ s, CutCur.worst (P n) (X n) (S n) (CutCur.fisherInfo (V n)) s = LF n s)
    (hT : ∀ n, 0 < n → ∀ s, CutCur.worst (P n) (X n) (S n)
      (fun ν => .ofReal (CutCur.tvDist ν (CutCur.gibbs (V n)))) s = ENNReal.ofReal (LT n s))
    (lim : ∀ ε : ℝ, 0 < ε → ε < 1 →
      (Tendsto (fun n => LW n ((1 - ε) * CutCur.criticalTime n ρ)) atTop atTop ∧
        Tendsto (fun n => LW n ((1 + ε) * CutCur.criticalTime n ρ)) atTop (𝓝 0)) ∧
      (Tendsto (fun n => LF n ((1 - ε) * CutCur.criticalTime n ρ)) atTop (𝓝 ⊤) ∧
        Tendsto (fun n => LF n ((1 + ε) * CutCur.criticalTime n ρ)) atTop (𝓝 0)) ∧
      (Tendsto (fun n => LK n ((1 - ε) * CutCur.criticalTime n ρ)) atTop (𝓝 ⊤) ∧
        Tendsto (fun n => LK n ((1 + ε) * CutCur.criticalTime n ρ)) atTop (𝓝 0)) ∧
      (Tendsto (fun n => LT n ((1 - ε) * CutCur.criticalTime n ρ)) atTop (𝓝 1) ∧
        Tendsto (fun n => LT n ((1 + ε) * CutCur.criticalTime n ρ)) atTop (𝓝 0))) :
    CutCur.HasCutoff (fun n => CutCur.worst (P n) (X n) (S n)
      (CutCur.wasserstein2 · (CutCur.gibbs (V n)))) (fun n => CutCur.criticalTime n ρ) ⊤ 0 ∧
    CutCur.HasCutoff (fun n => CutCur.worst (P n) (X n) (S n) (CutCur.fisherInfo (V n)))
      (fun n => CutCur.criticalTime n ρ) ⊤ 0 ∧
    CutCur.HasCutoff (fun n => CutCur.worst (P n) (X n) (S n)
      (InformationTheory.klDiv · (CutCur.gibbs (V n)))) (fun n => CutCur.criticalTime n ρ) ⊤ 0 ∧
    CutCur.HasCutoff (fun n => CutCur.worst (P n) (X n) (S n)
      (fun ν => .ofReal (CutCur.tvDist ν (CutCur.gibbs (V n))))) (fun n => CutCur.criticalTime n ρ) 1 0 := by
  have hev : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hTv : ∀ {a : ℝ} {u : ℕ → ℝ}, Tendsto u atTop (𝓝 a) →
      Tendsto (fun n => ENNReal.ofReal (u n)) atTop (𝓝 (ENNReal.ofReal a)) :=
    fun hu => (ENNReal.continuous_ofReal.tendsto _).comp hu
  refine ⟨fun ε h0 h1 => ?_, fun ε h0 h1 => ?_, fun ε h0 h1 => ?_, fun ε h0 h1 => ?_⟩ <;>
    obtain ⟨⟨hWb, hWa⟩, ⟨hFb, hFa⟩, ⟨hKb, hKa⟩, ⟨hTb, hTa⟩⟩ := lim ε h0 h1
  · refine ⟨?_, ?_⟩
    · refine (ENNReal.tendsto_ofReal_atTop.comp hWb).congr' ?_
      filter_upwards [hev] with n hn
      simp only [Function.comp, hW n hn]
    · have := hTv hWa
      rw [ENNReal.ofReal_zero] at this
      refine this.congr' ?_
      filter_upwards [hev] with n hn
      simp only [hW n hn]
  · refine ⟨hFb.congr' ?_, hFa.congr' ?_⟩ <;>
      · filter_upwards [hev] with n hn
        simp only [hF n hn]
  · refine ⟨hKb.congr' ?_, hKa.congr' ?_⟩ <;>
      · filter_upwards [hev] with n hn
        simp only [hK n hn]
  · have h1 := hTv hTb
    have h2 := hTv hTa
    rw [ENNReal.ofReal_one] at h1
    rw [ENNReal.ofReal_zero] at h2
    refine ⟨h1.congr' ?_, h2.congr' ?_⟩ <;>
      · filter_upwards [hev] with n hn
        simp only [hT n hn]

/-- **Corollary 1.6** (cutoff for convex interactions, fixed `ρ > 0`). -/
theorem convex_interaction_cutoff_carrier {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)] {ρ : ℝ}
    (hρ : 0 < ρ) {W : ∀ n, CutCur.Rd n → ℝ} {B : ∀ n, ℝ≥0 → Ω n → CutCur.Rd n}
    {P : ∀ n, Measure (Ω n)} {X : ∀ n, CutCur.Rd n → ℝ≥0 → Ω n → CutCur.Rd n}
    (hW : ∀ n, 0 < n → ContDiff ℝ 2 (W n) ∧ ConvexOn ℝ univ (W n) ∧
      ∀ x (s : ℝ), W n (x + s • CutCur.diagonal n) = W n x)
    (hL : ∀ n, 0 < n → CutCur.IsLangevin (fun x => ρ / 2 * ‖x‖ ^ 2 + W n x) (B n) (P n) (X n))
    {c : ℝ} (hc : 0 < c) :
    let V := fun n (x : CutCur.Rd n) => ρ / 2 * ‖x‖ ^ 2 + W n x
    let t := fun n : ℕ => CutCur.criticalTime n ρ
    ∀ cube : Bool,
      let S := fun n => if cube then CutCur.meanCube (V n) c else CutCur.meanBall (V n) c
      CutCur.HasCutoff (fun n => CutCur.worst (P n) (X n) (S n)
        (CutCur.wasserstein2 · (CutCur.gibbs (V n)))) t ⊤ 0 ∧
      CutCur.HasCutoff (fun n => CutCur.worst (P n) (X n) (S n) (CutCur.fisherInfo (V n))) t ⊤ 0 ∧
      CutCur.HasCutoff (fun n => CutCur.worst (P n) (X n) (S n)
        (InformationTheory.klDiv · (CutCur.gibbs (V n)))) t ⊤ 0 ∧
      CutCur.HasCutoff (fun n => CutCur.worst (P n) (X n) (S n)
        (fun ν => .ofReal (CutCur.tvDist ν (CutCur.gibbs (V n))))) t 1 0 := by
  intro V t cube S
  obtain ⟨Ω', _, drv, P', hdrv, hnoise⟩ :=
    exists_seqBrownian (fun n hn => isStdBrownian_iff.mp (hL n hn).2.2.1)
  let Wc : ∀ n, CutCur.Rd n → ℝ := fun n x => if n = 0 then 0 else W n x
  have hWc : ∀ n, 0 < n → Wc n = W n := fun n hn => by
    funext x
    simp [Wc, hn.ne']
  have hWc0 : Wc 0 = fun _ => 0 := by
    funext x
    simp [Wc]
  let D' : ∀ n, ConvexInteractionCubeData Ω' n := fun n =>
    { interaction := Wc n
      smooth := by
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h; rw [hWc0]; exact contDiff_const
        · rw [hWc n h]; exact (hW n h).1
      convex := by
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h; rw [hWc0]; exact convexOn_const 0 convex_univ
        · rw [hWc n h]; exact (hW n h).2.1
      rate := ρ
      rate_pos := hρ
      diagonalInvariant := by
        intro x s
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h; rw [hWc0]
        · rw [hWc n h]; exact (hW n h).2.2 x s
      driver := drv n
      noiseLaw := P'
      brownian := hdrv n }
  have hVeq : ∀ n, 0 < n →
      (fun x : CutCur.Rd n => (D' n).rate / 2 * ‖x‖ ^ 2 + (D' n).interaction x) = V n := by
    intro n hn
    funext x
    change ρ / 2 * ‖x‖ ^ 2 + Wc n x = ρ / 2 * ‖x‖ ^ 2 + W n x
    rw [hWc n hn]
  have hpot : ∀ n, 0 < n → (cubeSpectralData (D' n)).potential = V n := by
    intro n hn
    have hp : IsProbabilityMeasure (gibbsMeasure volume
        (fun x : CutCur.Rd n => (D' n).rate / 2 * ‖x‖ ^ 2 + (D' n).interaction x)) := by
      rw [hVeq n hn]
      exact gibbs_probability (hL n hn).2.1
    rw [cubeSpectralData_potential_eq (D' n) hp, hVeq n hn]
  have hHess : ∀ n, 0 < n → ∀ x z : CutCur.Rd n,
      ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (V n)) x z z := fun n hn =>
    hessian_quadratic_add_convex_lower (hW n hn).1 (hW n hn).2.1 ρ
  have hk : ∀ n, 0 < n → ∀ (s : ℝ≥0) (x : CutCur.Rd n),
      langevinKernel (cubeSpectralData (D' n)).potential (cubeSpectralData (D' n)).driver
        (cubeSpectralData (D' n)).noiseLaw s x = (P n).map (X n x s) := by
    intro n hn s x
    rw [hpot n hn]
    change langevinKernel (V n) (drv n) P' s x = _
    rw [IsLangevin.map_eq_langevinKernel (hL n hn) ρ hρ.le (hHess n hn) x s,
      langevinKernel_congr_noise (V n) (hnoise n hn)]
  have hliminf : 0 < liminf (fun n => ENNReal.ofReal (D' n).rate) atTop :=
    fixed_rate_positive_liminf hρ
  have hsub : (fun n => (D' n).rate) =o[atTop] (fun n : ℕ => Real.log (n : ℝ)) :=
    fixed_rate_isLittleO_log ρ
  have hliminfS : 0 < liminf (fun n => ENNReal.ofReal (cubeSpectralData (D' n)).rate) atTop :=
    hliminf
  have hsubS : (fun n => (cubeSpectralData (D' n)).rate) =o[atTop]
      (fun n : ℕ => Real.log (n : ℝ)) := hsub
  cases cube
  · -- balls
    refine assemble_cutoffs (V := V) (P := P) (X := X) (S := fun n => CutCur.meanBall (V n) c)
      (fun n s => barycenterBallWasserstein (cubeSpectralData (D' n)) c s)
      (fun n s => meanBallTV (cubeSpectralData (D' n)) c s)
      (fun n s => meanBallKL (cubeSpectralData (D' n)) c s)
      (fun n s => meanBallFisher (cubeSpectralData (D' n)) c s) ?_ ?_ ?_ ?_ ?_
    · intro n hn s
      rw [← hpot n hn, barycenterBallWasserstein_eq_sqrt _ hn hc.le]
      exact worst_wasserstein_set (cubeSpectralData (D' n)) _ (hk n hn) s _
        ENNReal.toReal_nonneg (barycenterBallSquaredWasserstein_ofReal _ hn hc.le s)
    · intro n hn s
      rw [← hpot n hn]
      exact worst_kl_set (cubeSpectralData (D' n)) _ (hk n hn) s
    · intro n hn s
      rw [← hpot n hn]
      exact worst_fisher_set (cubeSpectralData (D' n)) _ (hk n hn) s
    · intro n hn s
      rw [← hpot n hn]
      exact worst_tv_set (cubeSpectralData (D' n))
        ⟨_, Metric.mem_closedBall_self (by positivity)⟩ (hk n hn) s
    · intro ε h0 h1
      obtain ⟨hKb, hKa, hTb, hTa, hFb, hFa⟩ :=
        meanBall_information_cutoff (fun n => cubeSpectralData (D' n)) hc h0 h1 hliminfS hsubS
      exact ⟨⟨barycenter_wasserstein_before_cutoff (fun n => cubeSpectralData (D' n)) hc h0 h1,
        barycenter_wasserstein_after_cutoff (fun n => cubeSpectralData (D' n)) hc.le h0 hliminfS⟩,
        ⟨hFb, hFa⟩, ⟨hKb, hKa⟩, ⟨hTb, hTa⟩⟩
  · -- cubes
    refine assemble_cutoffs (V := V) (P := P) (X := X) (S := fun n => CutCur.meanCube (V n) c)
      (fun n s => cubeWasserstein (D' n) c s)
      (fun n s => convexCubeTV (D' n) c s)
      (fun n s => convexCubeKL (D' n) c s)
      (fun n s => convexCubeFisher (D' n) c s) ?_ ?_ ?_ ?_ ?_
    · intro n hn s
      rw [← hpot n hn, cubeWasserstein_eq_sqrt _ hn hc.le]
      exact worst_wasserstein_set (cubeSpectralData (D' n)) _ (hk n hn) s _
        ENNReal.toReal_nonneg (cubeSquaredWasserstein_ofReal _ hn hc.le s)
    · intro n hn s
      rw [← hpot n hn]
      exact worst_kl_set (cubeSpectralData (D' n)) _ (hk n hn) s
    · intro n hn s
      rw [← hpot n hn]
      exact worst_fisher_set (cubeSpectralData (D' n)) _ (hk n hn) s
    · intro n hn s
      rw [← hpot n hn]
      exact worst_tv_set (cubeSpectralData (D' n))
        ⟨∫ y, y ∂gibbsMeasure volume (cubeSpectralData (D' n)).potential, fun i => by
          have h : |(∫ y, y ∂gibbsMeasure volume (cubeSpectralData (D' n)).potential) i -
              (∫ y, y ∂gibbsMeasure volume (cubeSpectralData (D' n)).potential) i| ≤ c := by
            rw [sub_self, abs_zero]; exact hc.le
          exact h⟩ (hk n hn) s
    · intro ε h0 h1
      obtain ⟨hKb, hKa, hTb, hTa, hFb, hFa⟩ :=
        convexCube_information_cutoff D' hc h0 h1 hliminf hsub
      exact ⟨⟨cube_wasserstein_before_cutoff D' hc h0 h1,
        cube_wasserstein_after_cutoff D' hc.le h0 hliminf⟩,
        ⟨hFb, hFa⟩, ⟨hKb, hKa⟩, ⟨hTb, hTa⟩⟩

end CutoffRigidity.Paper
