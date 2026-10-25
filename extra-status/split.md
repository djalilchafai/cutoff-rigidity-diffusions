# split: Theorem 3.6 potential identity

Proved: `CutoffRigidity.Paper.riemannian_gaussian_splitting_potential` in
`CutoffRigidity/Extra/SplitPotential.lean` (module `CutoffRigidity.Extra.SplitPotential`; builds, no sorry,
axioms: propext, Classical.choice, Quot.sound). The proof is a copy of `Paper.riemannian_gaussian_splitting`
(`Riemann/AssembleMain.lean`, untouched) with one extra conjunct, placed right after the `edist` conjunct:

    (∀ x, V x = ρ * ‖(Φ x).1‖ ^ 2 / 2 + V' (Φ x).2 + k / 2 * Real.log (2 * Real.pi / ρ)) ∧

No uniqueness argument needed: the existing construction has V' y = V y.val + (k/2) log(ρ/2π) on the level
set, Φ x = (sv x, retr x), and `Frame.V_action` gives V(comp(sv x)(retr x)) = V(retr x) + ρ|sv x|²/2.
Hence the identity holds pointwise (log(2π/ρ) = -log(ρ/2π)).

Proposed Challenge text: same as `riemannian_gaussian_splitting` (Challenge.lean ~445), unqualified names, with
the conjunct above inserted after `(∀ x y, edist x y ^ 2 = ...) ∧`. Docstring: add "and
`V∘Φ⁻¹(p,y) = ρ|p|²/2 + V'(y) + (k₁/2) log(2π/ρ)` (Theorem 3.6)".
Not edited: Challenge.lean and all existing files.

## Follow-up: ConnectedSpace N, CompleteSpace N
Same theorem `riemannian_gaussian_splitting_potential` extended in place: the first conjunct group now ends
`... ∧ CD F' ρ V' ∧ ConnectedSpace N ∧ CompleteSpace N` (typeclasses resolve through the existential
`EMetricSpace N`; no obstruction). Proof: N = `fr.Level = {x // sv x = 0}`; connected as the continuous
surjective image of M under `x ↦ ⟨retr x, _⟩` (surjective since retr = id on the level); complete as a closed
subset of complete M. Final Challenge text = old text with the first group
`(ContMDiff V' ∧ IsProbabilityMeasure μ' ∧ IsWeightedVolume F' μ' V' ∧ CD F' ρ V' ∧ ConnectedSpace N ∧ CompleteSpace N)`
and the potential conjunct after the `edist` conjunct. Axioms re-checked: propext, Classical.choice, Quot.sound.
