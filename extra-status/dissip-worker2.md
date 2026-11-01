# Item 4 worker, repair round 1 (de Bruijn inequality)

File: CutoffRigidity/Extra/Dissip4.lean (builds; no sorry/axiom; axioms of both theorems: propext, Classical.choice, Quot.sound).
Repair: `hfin : klDiv ν μ ≠ ⊤` replaced by finite entropy at an earlier time `a < s` (proof: Chapman-Kolmogorov
`Pt (a+u) = Pt u ∘ₖ Pt a` + `Measure.comp_assoc`, apply `langevin_dissipation_ge_K` to `ν.bind (Pt a)` with times `s-a < t-a`,
shift `r ↦ r - a` in the lintegral via `measurePreserving_sub_right`). hρ, hHess unchanged.

```lean
theorem langevin_dissipation_ge_K' {d : ℕ} {V : CutCur.Rd d → ℝ}
    {Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d)} (hL : CutCur.IsEuclideanLangevin V Pt)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (CutCur.Rd d)) [IsProbabilityMeasure ν] {a s t : ℝ≥0}
    (hfin : klDiv (ν.bind (Pt a)) (CutCur.gibbs V) ≠ ⊤) (has : a < s) (hst : s < t) :
    (∫⁻ r in Ioc (s : ℝ) t, CutCur.fisherInfo V (ν.bind (Pt r.toNNReal))) +
        klDiv (ν.bind (Pt t)) (CutCur.gibbs V) ≤
      klDiv (ν.bind (Pt s)) (CutCur.gibbs V)
```
(a = 0 is allowed: recovers the old theorem, `Pt 0` = identity kernel; no extra argument needed.)

Dirac corollary (proved, uses existing `klDiv_langevinKernel_ne_top`, i.e. finiteness of squaredWasserstein(dirac, gibbs) under Hess >= rho and
the W2-regularization bound; entropy at positive time is finite for every x₀; a := s/2):
```lean
theorem langevin_dissipation_dirac_K {d : ℕ} {V : CutCur.Rd d → ℝ}
    {Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d)} (hL : CutCur.IsEuclideanLangevin V Pt)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : CutCur.Rd d) {s t : ℝ≥0} (hs : 0 < s) (hst : s < t) :
    (∫⁻ r in Ioc (s : ℝ) t, CutCur.fisherInfo V (Pt r.toNNReal x₀)) +
        klDiv (Pt t x₀) (CutCur.gibbs V) ≤ klDiv (Pt s x₀) (CutCur.gibbs V)
```
Not proved: the equality (only the inequality half of eq:HI, as before). Dissip1-3 unchanged.
