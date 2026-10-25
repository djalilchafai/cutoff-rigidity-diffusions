module

public import CutoffRigidity.Extra.EuclideanCutoffs
public import CutoffRigidity.Extra.EuclideanWasserstein
public import CutoffRigidity.Extra.WassersteinCutoffWeak
public import CutoffRigidity.Extra.InformationCutoffWeak

/-! # Brownian-free kernel versions of Remarks 3.4 and 3.5 and of the W2 contraction

`wasserstein_cutoff_weak_K`, `information_cutoff_weak_K` (kernel `Pt`, hypotheses `IsEuclideanLangevin`
/ `IsRigidSequenceK`), derived from the Brownian-based `_carrier` theorems by the transfer lemmas of
`EuclideanDiffusion` / `EuclideanCutoffs`.
-/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Set CutCur
open scoped ENNReal NNReal Topology Asymptotics ContDiff

/-- **Remark 3.4**, kernel form. -/
theorem wasserstein_cutoff_weak_K {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    (hL : ∀ n, 0 < n → IsEuclideanLangevin (V n) (Pt n) ∧ RigidCurvature (V n))
    (hgap : ∃ α : ℝ, 0 < α ∧
      ∀ᶠ n : ℕ in atTop, (spectralGap (V n))⁻¹ ≤ (Real.log n) ^ α)
    {c : ℝ} (hc : 0 < c) :
    HasCutoff (fun n => worstK (Pt n) (meanBall (V n) c)
      (wasserstein2 · (gibbs (V n))))
      (fun n => CutCur.criticalTime n (spectralGap (V n))) ⊤ 0 := by
  obtain ⟨Ω, _, B, P, X, hLang, key⟩ := exists_langevinSeq_of_K
    (fun n hn => ⟨(hL n hn).1, (hL n hn).2.hess_nonneg⟩)
  exact hasCutoff_congr_eventually
    (eventually_worst_eq_worstK key (fun n => meanBall (V n) c)
      (fun n => (wasserstein2 · (gibbs (V n)))))
    (wasserstein_cutoff_weak_carrier (fun n hn => ⟨hLang n hn, (hL n hn).2⟩) hgap hc)

/-- **Remark 3.5**, kernel form. -/
theorem information_cutoff_weak_K {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    (h : IsRigidSequenceK V Pt)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, spectralGap (V n) ≤ (n : ℝ) ^ ε)
    {c : ℝ} (hc : 0 < c) :
    let t := fun n => CutCur.criticalTime n (spectralGap (V n))
    let S := fun n => meanBall (V n) c
    HasCutoff (fun n => worstK (Pt n) (S n) (fisherInfo (V n))) t ⊤ 0 ∧
    HasCutoff (fun n => worstK (Pt n) (S n) (InformationTheory.klDiv · (gibbs (V n)))) t ⊤ 0 ∧
    HasCutoff (fun n => worstK (Pt n) (S n) (fun ν => .ofReal (tvDist ν (gibbs (V n))))) t 1 0 := by
  intro t S
  obtain ⟨Ω, _, B, P, X, hP, hrig, key⟩ := exists_isRigidSequence_of_K h
  obtain ⟨h1, h2, h3⟩ := information_cutoff_weak_carrier hrig hsmall hc
  exact ⟨hasCutoff_congr_eventually (eventually_worst_eq_worstK key S _) h1,
    hasCutoff_congr_eventually (eventually_worst_eq_worstK key S _) h2,
    hasCutoff_congr_eventually (eventually_worst_eq_worstK key S _) h3⟩

alias wasserstein_cutoff_weak := wasserstein_cutoff_weak_K
alias information_cutoff_weak := information_cutoff_weak_K
alias langevin_w2_contraction := langevin_w2_contraction_K

end CutoffRigidity.Paper
