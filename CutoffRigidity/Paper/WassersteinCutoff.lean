module

public import CutoffRigidity.Paper.SeqData
public import CutoffRigidity.BarycenterWassersteinCutoff

/-! # Corollary 1.3: Wasserstein cutoff on the statement surface -/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

/-- The worst-case Wasserstein distance on a mean ball is the library's mean-ball profile. -/
theorem worst_wasserstein_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ}
    (hd : 0 < d) (D : SpectralInformationLowerData Ω' d) {c : ℝ} (hc : 0 ≤ c)
    {P : Measure Ω} {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d}
    (hk : ∀ (t : ℝ≥0) (x : CutCur.Rd d), langevinKernel D.potential D.driver D.noiseLaw t x =
      P.map (X x t)) (t : ℝ) :
    CutCur.worst P X (CutCur.meanBall D.potential c)
      (CutCur.wasserstein2 · (CutCur.gibbs D.potential)) t =
        ENNReal.ofReal (barycenterBallWasserstein D c t) := by
  rw [barycenterBallWasserstein_eq_sqrt D hd hc, Real.sqrt_eq_rpow,
    ← ENNReal.ofReal_rpow_of_nonneg (by
      unfold barycenterBallSquaredWasserstein
      exact ENNReal.toReal_nonneg) (by norm_num),
    barycenterBallSquaredWasserstein_ofReal D hd hc t]
  have hmap := (ENNReal.orderIsoRpow (1 / 2) (by norm_num)).map_iSup
    (fun x : Metric.closedBall (∫ y, y ∂gibbsMeasure volume D.potential) (c * Real.sqrt d) =>
      squaredWasserstein (langevinKernel D.potential D.driver D.noiseLaw t.toNNReal x)
        (gibbsMeasure volume D.potential))
  unfold CutCur.worst
  rw [iSup_subtype']
  refine Eq.trans (iSup_congr fun x => ?_) hmap.symm
  rw [← hk t.toNNReal x.1]
  beta_reduce
  rw [wasserstein2_eq_rpow]
  rfl

/-- **Corollary 1.3** (Wasserstein cutoff on balls `B(m, c√d)`). -/
theorem wasserstein_cutoff {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {V : ∀ n, CutCur.Rd n → ℝ}
    {B : ∀ n, ℝ≥0 → Ω n → CutCur.Rd n} {P : ∀ n, Measure (Ω n)}
    {X : ∀ n, CutCur.Rd n → ℝ≥0 → Ω n → CutCur.Rd n}
    (h : CutCur.IsRigidSequence V B P X) {c : ℝ} (hc : 0 < c) :
    CutCur.HasCutoff (fun n => CutCur.worst (P n) (X n) (CutCur.meanBall (V n) c)
      (CutCur.wasserstein2 · (CutCur.gibbs (V n))))
      (fun n => CutCur.criticalTime n (CutCur.spectralGap (V n))) ⊤ 0 := by
  obtain ⟨hL, hlim⟩ := h
  obtain ⟨Ω', _, D, hD⟩ := exists_seqData hL
  have hev : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hrateEv : (fun n => (D n).rate) =ᶠ[atTop] fun n => CutCur.spectralGap (V n) := by
    filter_upwards [hev] with n hn using (hD n hn).1
  have hliminf : 0 < liminf (fun n => ENNReal.ofReal (D n).rate) atTop := by
    have := Filter.liminf_congr (f := atTop) (u := fun n => ENNReal.ofReal (D n).rate)
      (v := fun n => ENNReal.ofReal (CutCur.spectralGap (V n)))
      (by filter_upwards [hrateEv] with n hn using by rw [hn])
    rwa [this]
  have hprof : ∀ n, 0 < n → ∀ t : ℝ,
      CutCur.worst (P n) (X n) (CutCur.meanBall (V n) c)
        (CutCur.wasserstein2 · (CutCur.gibbs (V n))) t =
        ENNReal.ofReal (barycenterBallWasserstein (D n) c t) := by
    intro n hn t
    obtain ⟨hr, hpot, hk⟩ := hD n hn
    have := worst_wasserstein_eq hn (D n) hc.le (P := P n) (X := X n) hk t
    rwa [hpot] at this
  have hcrit : ∀ n, 0 < n → CutCur.criticalTime n (CutCur.spectralGap (V n)) =
      criticalTime n (D n).rate := by
    intro n hn
    rw [(hD n hn).1]
    rfl
  intro ε hε0 hε1
  constructor
  · have h1 := ENNReal.tendsto_ofReal_atTop.comp
      (barycenter_wasserstein_before_cutoff D hc hε0 hε1)
    refine h1.congr' ?_
    filter_upwards [hev] with n hn
    simp only [Function.comp, hprof n hn, hcrit n hn]
  · have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp
      (barycenter_wasserstein_after_cutoff D hc.le hε0 hliminf)
    rw [ENNReal.ofReal_zero] at h2
    refine h2.congr' ?_
    filter_upwards [hev] with n hn
    simp only [Function.comp, hprof n hn, hcrit n hn]

end CutoffRigidity.Paper
