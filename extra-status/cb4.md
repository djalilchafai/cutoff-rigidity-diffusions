# cb4: W2 and entropy mixing times (manuscript L349)

Module `CutoffRigidity/Extra/MixingTimeW2KL.lean` (about 300 lines), builds, no sorry, axioms propext/Classical.choice/Quot.sound.
Contents: `profileMixing`, `mixing_ratio_of_cutoff`, `worst_w2_antitone`, `worst_klDiv_antitone`, `mixing_tail`
(namespace CutoffRigidity.Paper); defs `CutCur.mixingTimeW2`, `CutCur.mixingTimeKL` (to be moved to Challenge/Statements by the lead,
then deleted from the Extra file, which should import Statements); theorems `CutoffRigidity.Paper.mixing_time_w2_rigid`, `mixing_time_kl_rigid`.
No existing file edited.

## Conventions
W2 not squared (`wasserstein2`, as in `HasCutoff` for Wasserstein in the Challenge), entropy `klDiv`, both compared with `ENNReal.ofReal η`, exactly like `mixingTime`.
Any `η > 0` (profiles tend to infinity and 0), unlike TV.

## Deviation from the brief (honest flag)
`t₀ → ∞` is NOT derivable for W2 from `IsRigidSequence` alone (take `λ₁ ~ log n`: critical time stays bounded). The manuscript sentence (L349, "To summarize") assumes
`λ₁ = o(log d)`. So in `mixing_time_w2_rigid` the fourth conjunct is the implication `λ₁ =o log n → t₀ → ∞`; the first three conjuncts need only rigidity.
`mixing_time_kl_rigid` has `hsmall` and the unconditional fourth conjunct, as `mixing_time_rigid`.
Merging with `mixing_time_rigid`: not done (would change its statement; TV needs `η<1`). Keep three theorems.

## Proposed Challenge text (defs after `mixingTime`, theorems after `mixing_time_rigid`)
```lean
/-- The Wasserstein mixing time `t₀ = inf {t ≥ 0 : sup_{x₀ ∈ S} W₂(Xₜ, μ) ≤ η}` (`+∞` if the set is empty). -/
def mixingTimeW2 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (X : Rd d → ℝ≥0 → Ω → Rd d) (μ : Measure (Rd d)) (S : Set (Rd d)) (η : ℝ) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : worst P X S (fun ν => wasserstein2 ν μ) t ≤ .ofReal η), (t : ℝ≥0∞)

/-- The relative entropy mixing time `t₀ = inf {t ≥ 0 : sup_{x₀ ∈ S} H(Xₜ | μ) ≤ η}` (`+∞` if the set is empty). -/
def mixingTimeKL {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (X : Rd d → ℝ≥0 → Ω → Rd d) (μ : Measure (Rd d)) (S : Set (Rd d)) (η : ℝ) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : worst P X S (fun ν => InformationTheory.klDiv ν μ) t ≤ .ofReal η), (t : ℝ≥0∞)

/-- **Wasserstein mixing time of rigid sequences** (manuscript, summary after Corollary 1.6): for every `η > 0`,
the Wasserstein mixing time `t₀` from `B(m, c√n)` is finite for large `n` and is `(log n/(2λ₁))(1+o(1))`;
`λ₁ t₀ → ∞`, and `t₀ → ∞` when `λ₁ = o(log n)`. -/
theorem mixing_time_w2_rigid {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {V : ∀ n, Rd n → ℝ} {B : ∀ n, ℝ≥0 → Ω n → Rd n} {P : ∀ n, Measure (Ω n)}
    {X : ∀ n, Rd n → ℝ≥0 → Ω n → Rd n}
    (h : IsRigidSequence V B P X) {c : ℝ} (hc : 0 < c) {η : ℝ} (hη : 0 < η) :
    let t₀ := fun n => mixingTimeW2 (P n) (X n) (gibbs (V n)) (meanBall (V n) c) η
    (∀ᶠ n in atTop, t₀ n < ⊤) ∧
      Tendsto (fun n => (t₀ n).toReal / criticalTime n (spectralGap (V n))) atTop (𝓝 1) ∧
      Tendsto (fun n => spectralGap (V n) * (t₀ n).toReal) atTop atTop ∧
      ((fun n => spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n) →
        Tendsto (fun n => (t₀ n).toReal) atTop atTop) := by
  sorry

/-- **Entropy mixing time of rigid sequences** (same sentence, Corollary 1.4 hypotheses): as above with
`mixingTimeKL`, for every `η > 0`, under `λ₁ = o(log n)`; `t₀ → ∞` unconditionally. -/
theorem mixing_time_kl_rigid ... (h : IsRigidSequence V B P X)
    (hsmall : (fun n => spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n))
    {c : ℝ} (hc : 0 < c) {η : ℝ} (hη : 0 < η) :
    let t₀ := fun n => mixingTimeKL (P n) (X n) (gibbs (V n)) (meanBall (V n) c) η
    (∀ᶠ n in atTop, t₀ n < ⊤) ∧ Tendsto (... / criticalTime ...) atTop (𝓝 1) ∧
      Tendsto (fun n => spectralGap (V n) * (t₀ n).toReal) atTop atTop ∧
      Tendsto (fun n => (t₀ n).toReal) atTop atTop := by
  sorry
```
(Binders of the second are those of the first plus `hsmall`; exact text is in the Paper file.) Challenge grows by about 40 lines.
Integration: the Solution wiring is `mixing_time_w2_rigid := CutoffRigidity.Paper.mixing_time_w2_rigid` after moving the two defs to Statements/Challenge.
