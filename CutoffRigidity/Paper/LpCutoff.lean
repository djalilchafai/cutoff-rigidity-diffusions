module

public import CutoffRigidity.Paper.SeqData
public import CutoffRigidity.BarycenterLpHarnackCutoffs

/-! # Display (1.25): `Lᵖ` cutoff on the statement surface -/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

/-! ### The theorem -/

/-- **Display (1.25)** (`Lᵖ` cutoff), for every finite `p ≥ 1`. -/
theorem lp_cutoff {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {V : ∀ n, CutCur.Rd n → ℝ}
    {B : ∀ n, ℝ≥0 → Ω n → CutCur.Rd n} {P : ∀ n, Measure (Ω n)}
    {X : ∀ n, CutCur.Rd n → ℝ≥0 → Ω n → CutCur.Rd n}
    (h : CutCur.IsRigidSequence V B P X)
    (hsmall : (fun n => CutCur.spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n))
    {c : ℝ} (hc : 0 < c) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) :
    CutCur.HasCutoff (fun n => CutCur.worst (P n) (X n) (CutCur.meanBall (V n) c)
      (CutCur.relLp · (CutCur.gibbs (V n)) p))
      (fun n => CutCur.criticalTime n (CutCur.spectralGap (V n))) (if p = 1 then 2 else ⊤) 0 := by
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
  have hsub : (fun n => (D n).rate) =o[atTop] (fun n : ℕ => Real.log (n : ℝ)) :=
    hsmall.congr' hrateEv.symm EventuallyEq.rfl
  intro ε hε0 hε1
  obtain ⟨h1, h2⟩ := meanBall_Lp_cutoff D hc hε0 hε1 hliminf hsub hp hpt
  have hball : ∀ n, 0 < n → ∀ t : ℝ, meanBallLp (D n) c p t =
      CutCur.worst (P n) (X n) (CutCur.meanBall (V n) c)
        (CutCur.relLp · (CutCur.gibbs (V n)) p) t := by
    intro n hn t
    obtain ⟨hr, hpot, hk⟩ := hD n hn
    rw [hpot] at hk
    unfold meanBallLp spectralSetLp CutCur.worst
    rw [hpot, iSup_subtype']
    apply iSup_congr
    intro x
    rw [hk t.toNNReal x.1]
    rfl
  have hcrit : ∀ n, 0 < n → CutCur.criticalTime n (CutCur.spectralGap (V n)) =
      criticalTime n (D n).rate := by
    intro n hn
    rw [(hD n hn).1]
    rfl
  constructor
  · refine h1.congr' ?_
    filter_upwards [hev] with n hn
    rw [hball n hn, hcrit n hn]
  · refine h2.congr' ?_
    filter_upwards [hev] with n hn
    rw [hball n hn, hcrit n hn]

end CutoffRigidity.Paper
