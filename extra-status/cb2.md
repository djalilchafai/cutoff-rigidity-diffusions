# cb2: Fisher information decay (items 3a, 3b)

Module `CutoffRigidity/Extra/FisherDecayGeneral.lean` (not added to `CutoffRigidity.lean`; lead to wire).
`lake build CutoffRigidity.Extra.FisherDecayGeneral` OK; axioms of both theorems: propext, Classical.choice, Quot.sound. No sorry.

Proved (namespace CutoffRigidity.Paper): `langevin_fisher_decay` (3a), `dini_of_exp_decay` (real helper), `langevin_fisher_dini` (3b).
No `0 < d` needed; no hypothesis beyond those of `langevin_entropy_decay`.

## Proposed Challenge text (a)
```lean
/-- **Exponential decay of the Fisher information** (eq. expdecI, manuscript proof of Corollary 1.4,
see also the discussion "Fisher information and the heat kernel") under `Hess V ≥ ρ I`, `ρ > 0`,
for an arbitrary initial law `ν` (in particular `I(ν)` may be `+∞`):
`I(μ_t) ≤ e^{-2ρ(t-s)} I(μ_s)` for `s ≤ t`, `μ_t := Law(X_t)`. -/
theorem langevin_fisher_decay {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {V : Rd d → ℝ} {B : ℝ≥0 → Ω → Rd d}
    {P : Measure Ω} {X : Rd d → ℝ≥0 → Ω → Rd d}
    (hL : IsLangevin V B P X) {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (Rd d)) [IsProbabilityMeasure ν] :
    ∀ s t : ℝ≥0, s ≤ t →
      fisherInfo V (ν.bind fun x => P.map (X x t)) ≤
        ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - s))) *
          fisherInfo V (ν.bind fun x => P.map (X x s))
```
Note: `fisherInfo` is stated via the Challenge definition (same surface as `langevin_entropy_decay`'s `I`); it is the
closed-gradient extended-valued Fisher information, so the case `I(ν) = ⊤` is covered.

## Proposed Challenge text (b)
```lean
/-- **Upper Dini form of `∂_t I ≤ -2ρ I`** (manuscript, display before eq. expdecI in the proof of
Corollary 1.4): at every time `t` with `I(μ_t) < ∞`, for every `ε > 0`, eventually as `h → 0+`,
`(I(μ_{t+h}) - I(μ_t))/h ≤ -2ρ I(μ_t) + ε`. -/
theorem langevin_fisher_dini {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {V : Rd d → ℝ} {B : ℝ≥0 → Ω → Rd d}
    {P : Measure Ω} {X : Rd d → ℝ≥0 → Ω → Rd d}
    (hL : IsLangevin V B P X) {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (Rd d)) [IsProbabilityMeasure ν] (t : ℝ≥0)
    (ht : fisherInfo V (ν.bind fun x => P.map (X x t)) ≠ ∞) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ),
      ((fisherInfo V (ν.bind fun x => P.map (X x (t + h.toNNReal)))).toReal -
          (fisherInfo V (ν.bind fun x => P.map (X x t))).toReal) / h ≤
        -2 * ρ * (fisherInfo V (ν.bind fun x => P.map (X x t))).toReal + ε
```
Why this formulation: in ENNReal subtraction is truncated and `⊤ - ⊤` is meaningless, so the Dini quotient is stated on
`.toReal` and only at times with `I(μ_t) ≠ ⊤` (hypothesis `ht`; from (a), `I(μ_{t+h}) < ⊤` for all h ≥ 0 then, so
the `toReal` is faithful). For `I(μ_t) = ⊤` the inequality is vacuous/meaningless. The Dini form is a real corollary
of (a) (one-sided derivative of `exp(-2ρh)` at 0), so it adds no new analytic content, but it is the only rigorous
reading of the printed "∂_t I ≤ -2ρ I" for a general law, where `t ↦ I(μ_t)` is not known to be differentiable. The pointwise
derivative is intentionally not stated. Time shift `h.toNNReal` is used because `X` is indexed by `ℝ≥0` and `h > 0`
eventually. Remark: `ht` holds for all `t > 0` when `H(ν|μ) < ∞` or `W₂(ν,μ) < ∞` by the existing regularization in
`langevin_entropy_decay`, so the hypothesis is not restrictive.
(The unused-in-Challenge helper `dini_of_exp_decay` stays in the Extra module.)
