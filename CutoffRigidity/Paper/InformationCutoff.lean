module

public import CutoffRigidity.Paper.SeqData
public import CutoffRigidity.BarycenterInformationUpperCutoffs
public import CutoffRigidity.BarycenterFisherLowerCutoffs
public import CutoffRigidity.Paper.FisherBridge

/-! # Corollary 1.4: Fisher information, entropy and total variation cutoffs -/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Set InformationTheory
open scoped ENNReal NNReal Topology Asymptotics

section Profiles

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ}

theorem worst_kl_eq (D : SpectralInformationLowerData Ω' d) (c : ℝ)
    {P : Measure Ω} {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d}
    (hk : ∀ (t : ℝ≥0) (x : CutCur.Rd d), langevinKernel D.potential D.driver D.noiseLaw t x =
      P.map (X x t)) (t : ℝ) :
    CutCur.worst P X (CutCur.meanBall D.potential c)
      (InformationTheory.klDiv · (CutCur.gibbs D.potential)) t = meanBallKL D c t := by
  unfold CutCur.worst meanBallKL projectedSetKL
  rw [iSup_subtype']
  refine iSup_congr fun x => ?_
  rw [← hk t.toNNReal x.1]
  rfl

theorem worst_fisher_eq (D : SpectralInformationLowerData Ω' d) (c : ℝ)
    {P : Measure Ω} {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d}
    (hk : ∀ (t : ℝ≥0) (x : CutCur.Rd d), langevinKernel D.potential D.driver D.noiseLaw t x =
      P.map (X x t)) (t : ℝ) :
    CutCur.worst P X (CutCur.meanBall D.potential c) (CutCur.fisherInfo D.potential) t =
      meanBallFisher D c t := by
  have := D.probability
  have := langevinKernel_isMarkovKernel D.brownian D.smooth D.rate D.rate_pos.le D.hessian
    t.toNNReal
  unfold CutCur.worst meanBallFisher spectralSetFisher
  rw [iSup_subtype']
  refine iSup_congr fun x => ?_
  rw [← hk t.toNNReal x.1]
  exact fisherInfo_eq_relativeFisherInformation D.smooth D.probability D.rate D.rate_pos D.hessian
    _

theorem worst_tv_eq (D : SpectralInformationLowerData Ω' d) (c : ℝ) (hc : 0 ≤ c)
    {P : Measure Ω} {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d}
    (hk : ∀ (t : ℝ≥0) (x : CutCur.Rd d), langevinKernel D.potential D.driver D.noiseLaw t x =
      P.map (X x t)) (t : ℝ) :
    CutCur.worst P X (CutCur.meanBall D.potential c)
      (fun ν => ENNReal.ofReal (CutCur.tvDist ν (CutCur.gibbs D.potential))) t =
        ENNReal.ofReal (meanBallTV D c t) := by
  let S := Metric.closedBall (∫ y, y ∂gibbsMeasure volume D.potential) (c * Real.sqrt d)
  have hS : S.Nonempty := ⟨∫ y, y ∂gibbsMeasure volume D.potential, by
    simpa [S] using mul_nonneg hc (Real.sqrt_nonneg (d : ℝ))⟩
  let tv := fun x => totalVariationDistance
    (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x) (gibbsMeasure volume D.potential)
  have hf : Monotone ENNReal.ofReal := fun a b hab => ENNReal.ofReal_le_ofReal hab
  have hcs := hf.map_csSup_of_continuousAt ENNReal.continuous_ofReal.continuousAt (hS.image tv)
    (projectedSetTV_bddAbove (spectralInformationToAffine D) S t)
  unfold CutCur.worst meanBallTV projectedSetTV
  rw [iSup_subtype']
  change _ = ENNReal.ofReal (sSup (tv '' S))
  rw [hcs, Set.image_image, sSup_image']
  refine iSup_congr fun x => ?_
  rw [← hk t.toNNReal x.1]
  beta_reduce
  rw [tvDist_eq_totalVariationDistance]
  rfl

end Profiles

/-- **Corollary 1.4** (Fisher information, relative entropy and total variation cutoffs on
balls `B(m, c√d)`). -/
theorem information_cutoff {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {V : ∀ n, CutCur.Rd n → ℝ} {B : ∀ n, ℝ≥0 → Ω n → CutCur.Rd n} {P : ∀ n, Measure (Ω n)}
    {X : ∀ n, CutCur.Rd n → ℝ≥0 → Ω n → CutCur.Rd n}
    (h : CutCur.IsRigidSequence V B P X)
    (hsmall : (fun n => CutCur.spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n))
    {c : ℝ} (hc : 0 < c) :
    let t := fun n => CutCur.criticalTime n (CutCur.spectralGap (V n))
    let S := fun n => CutCur.meanBall (V n) c
    CutCur.HasCutoff (fun n => CutCur.worst (P n) (X n) (S n) (CutCur.fisherInfo (V n))) t ⊤ 0 ∧
    CutCur.HasCutoff (fun n => CutCur.worst (P n) (X n) (S n)
      (InformationTheory.klDiv · (CutCur.gibbs (V n)))) t ⊤ 0 ∧
    CutCur.HasCutoff (fun n => CutCur.worst (P n) (X n) (S n)
      (fun ν => .ofReal (CutCur.tvDist ν (CutCur.gibbs (V n))))) t 1 0 := by
  intro t S
  obtain ⟨Ω', _, D, hD, hliminf, hcrit, hsubT⟩ := exists_seqData_rigid h
  have hsub := hsubT hsmall
  have hev : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have prof : ∀ {δ : ∀ n, Measure (CutCur.Rd n) → ℝ≥0∞} {Q : ℕ → ℝ → ℝ≥0∞},
      (∀ n, 0 < n → ∀ s : ℝ, CutCur.worst (P n) (X n) (S n) (δ n) s = Q n s) →
      ∀ (a : ℝ≥0∞) (σ : ℝ),
        Tendsto (fun n => Q n (σ * criticalTime n (D n).rate)) atTop (𝓝 a) →
        Tendsto (fun n => CutCur.worst (P n) (X n) (S n) (δ n) (σ * t n)) atTop (𝓝 a) := by
    intro δ Q hQ a σ hlim
    refine hlim.congr' ?_
    filter_upwards [hev] with n hn
    rw [hQ n hn, ← hcrit n hn]
  have hK : ∀ n, 0 < n → ∀ s : ℝ, CutCur.worst (P n) (X n) (S n)
      (InformationTheory.klDiv · (CutCur.gibbs (V n))) s = meanBallKL (D n) c s := by
    intro n hn s
    obtain ⟨hr, hpot, hk⟩ := hD n hn
    have := worst_kl_eq (D n) c (P := P n) (X := X n) hk s
    rwa [hpot] at this
  have hF : ∀ n, 0 < n → ∀ s : ℝ, CutCur.worst (P n) (X n) (S n) (CutCur.fisherInfo (V n)) s =
      meanBallFisher (D n) c s := by
    intro n hn s
    obtain ⟨hr, hpot, hk⟩ := hD n hn
    have := worst_fisher_eq (D n) c (P := P n) (X := X n) hk s
    rwa [hpot] at this
  have hT : ∀ n, 0 < n → ∀ s : ℝ, CutCur.worst (P n) (X n) (S n)
      (fun ν => .ofReal (CutCur.tvDist ν (CutCur.gibbs (V n)))) s =
        ENNReal.ofReal (meanBallTV (D n) c s) := by
    intro n hn s
    obtain ⟨hr, hpot, hk⟩ := hD n hn
    have := worst_tv_eq (D n) c hc.le (P := P n) (X := X n) hk s
    rwa [hpot] at this
  have hTv : ∀ {a : ℝ}, ∀ {u : ℕ → ℝ}, Tendsto u atTop (𝓝 a) →
      Tendsto (fun n => ENNReal.ofReal (u n)) atTop (𝓝 (ENNReal.ofReal a)) :=
    fun hu => (ENNReal.continuous_ofReal.tendsto _).comp hu
  refine ⟨fun ε hε0 hε1 => ?_, fun ε hε0 hε1 => ?_, fun ε hε0 hε1 => ?_⟩ <;>
    obtain ⟨hKb, hKa, hTb, hTa, hFb, hFa⟩ := meanBall_information_cutoff D hc hε0 hε1 hliminf hsub
  · exact ⟨prof hF _ _ hFb, prof hF _ _ hFa⟩
  · exact ⟨prof hK _ _ hKb, prof hK _ _ hKa⟩
  · have h1 := hTv hTb
    have h2 := hTv hTa
    rw [ENNReal.ofReal_one] at h1
    rw [ENNReal.ofReal_zero] at h2
    exact ⟨prof hT _ _ h1, prof hT _ _ h2⟩

end CutoffRigidity.Paper
