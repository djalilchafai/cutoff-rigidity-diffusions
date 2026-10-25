# euc3: kernel (Brownian-free) versions of the Challenge cutoff theorems

File: `CutoffRigidity/Extra/EuclideanCutoffs.lean` (module `CutoffRigidity.Extra.EuclideanCutoffs`, namespace `CutoffRigidity.Paper`, `open CutCur`
so statements are written with unqualified Challenge names; `criticalTime` is written `CutCur.criticalTime` because `Paper.criticalTime` also exists).
`lake build` OK, no sorry/axiom, no warnings from this file; `#print axioms` for all 7 theorems: propext, Classical.choice, Quot.sound.
Needs `open scoped ContDiff` (for `∞`) when pasted. Imports: EuclideanDiffusion, MixingTimeW2KL, Paper.ProductCondition, Paper.LpCutoff, ConvexInteractionCurvature.

Theorems (all proved by the transfer lemmas from the Brownian-based Paper theorems):
`information_cutoff_K`, `lp_cutoff_K`, `convex_interaction_cutoff_K`, `product_condition_cutoff_K`, `mixing_time_rigid_K`, `mixing_time_w2_rigid_K`,
`mixing_time_kl_rigid_K`. Helper lemmas (not for Challenge): `exists_langevinSeq_of_K` (sequence transfer for non-rigid sequences: from
`∀ n>0, IsEuclideanLangevin (V n) (Pt n) ∧ Hess ≥ 0` get carriers with `IsLangevin` and laws `Pt`), `mixing_conclusion_congr`.

Amendments vs. original statements: only (a) `C^∞` potentials inside `IsEuclideanLangevin`; (b) Cor 1.6: `W n` is `C^∞` (was `C²`).
No extra convexity needed: Cor 1.4/1.25/mixing times assume `IsRigidSequenceK` (convexity from RigidCurvature); Thm 1.7 has `Hess ≥ κ > 0`;
Cor 1.6 has `W n` convex, so `Hess V ≥ ρ` by `hessian_quadratic_add_convex_lower`. Hypotheses/conclusions otherwise identical (`worst` -> `worstK`, `mixingTime*` -> `mixingTime*K`).

## Proposed Challenge text (to follow the foundation defs; `h : IsRigidSequenceK V Pt`)
```lean
/-- **Corollary 1.4**, Brownian-free form (kernels `Pt n` of the Langevin diffusion `IsEuclideanLangevin`, via `IsRigidSequenceK`). Amendment: C^∞ potentials. -/
theorem information_cutoff_K {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    (h : IsRigidSequenceK V Pt)
    (hsmall : (fun n => spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n)) {c : ℝ} (hc : 0 < c) :
    let t := fun n => criticalTime n (spectralGap (V n))
    let S := fun n => meanBall (V n) c
    HasCutoff (fun n => worstK (Pt n) (S n) (fisherInfo (V n))) t ⊤ 0 ∧
    HasCutoff (fun n => worstK (Pt n) (S n) (InformationTheory.klDiv · (gibbs (V n)))) t ⊤ 0 ∧
    HasCutoff (fun n => worstK (Pt n) (S n) (fun ν => .ofReal (tvDist ν (gibbs (V n))))) t 1 0

/-- **Display (1.25)**, Brownian-free form. Amendment: C^∞ potentials. -/
theorem lp_cutoff_K {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    (h : IsRigidSequenceK V Pt)
    (hsmall : (fun n => spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n))
    {c : ℝ} (hc : 0 < c) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) :
    HasCutoff (fun n => worstK (Pt n) (meanBall (V n) c) (relLp · (gibbs (V n)) p))
      (fun n => criticalTime n (spectralGap (V n))) (if p = 1 then 2 else ⊤) 0

/-- **Corollary 1.6**, Brownian-free form. Amendments: C^∞ interaction `W n` and C^∞ potential (inside `IsEuclideanLangevin`). -/
theorem convex_interaction_cutoff_K {ρ : ℝ} (hρ : 0 < ρ) {W : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    (hW : ∀ n, 0 < n → ContDiff ℝ ∞ (W n) ∧ ConvexOn ℝ univ (W n) ∧
      ∀ x (s : ℝ), W n (x + s • diagonal n) = W n x)
    (hL : ∀ n, 0 < n → IsEuclideanLangevin (fun x => ρ / 2 * ‖x‖ ^ 2 + W n x) (Pt n))
    {c : ℝ} (hc : 0 < c) :
    let V := fun n (x : Rd n) => ρ / 2 * ‖x‖ ^ 2 + W n x
    let t := fun n : ℕ => criticalTime n ρ
    ∀ cube : Bool,
      let S := fun n => if cube then meanCube (V n) c else meanBall (V n) c
      HasCutoff (fun n => worstK (Pt n) (S n) (wasserstein2 · (gibbs (V n)))) t ⊤ 0 ∧
      HasCutoff (fun n => worstK (Pt n) (S n) (fisherInfo (V n))) t ⊤ 0 ∧
      HasCutoff (fun n => worstK (Pt n) (S n) (InformationTheory.klDiv · (gibbs (V n)))) t ⊤ 0 ∧
      HasCutoff (fun n => worstK (Pt n) (S n) (fun ν => .ofReal (tvDist ν (gibbs (V n))))) t 1 0

/-- **Theorem 1.7**, Brownian-free form (amended form of the corrected manuscript, as in `product_condition_cutoff`). Amendment: C^∞ potentials. -/
theorem product_condition_cutoff_K {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    {κ : ℕ → ℝ} {S : ∀ n, Set (Rd n)} {η : ℝ}
    (hL : ∀ n, 0 < n → IsEuclideanLangevin (V n) (Pt n) ∧ 0 < κ n ∧
      ∀ x z : Rd n, κ n * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (V n)) x z z)
    (hS : ∀ n, 0 < n → (S n).Nonempty) (hη : 0 < η) (hη1 : η < 1) :
    let t₀ := fun n => mixingTimeK (Pt n) (gibbs (V n)) (S n) η
    let prof := fun (δ : ∀ n, Measure (Rd n) → ℝ≥0∞) n => worstK (Pt n) (S n) (δ n)
    (∀ᶠ n in atTop, t₀ n < ⊤) → Tendsto (fun n => κ n * (t₀ n).toReal) atTop atTop →
      (HasCutoff (prof fun n ν => .ofReal (tvDist ν (gibbs (V n)))) (fun n => (t₀ n).toReal) 1 0 ∧
        HasCutoff (prof fun n ν => InformationTheory.klDiv ν (gibbs (V n))) (fun n => (t₀ n).toReal) ⊤ 0) ∧
      (0 < liminf (fun n => ENNReal.ofReal (κ n)) atTop →
        Tendsto (fun n => (t₀ n).toReal) atTop atTop →
        HasCutoff (prof fun n => fisherInfo (V n)) (fun n => (t₀ n).toReal) ⊤ 0 ∧
        HasCutoff (prof fun n ν => wasserstein2 ν (gibbs (V n))) (fun n => (t₀ n).toReal) ⊤ 0)

/-- **Mixing time of rigid sequences**, Brownian-free form. Amendment: C^∞ potentials. -/
theorem mixing_time_rigid_K {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    (h : IsRigidSequenceK V Pt)
    (hsmall : (fun n => spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n))
    {c : ℝ} (hc : 0 < c) {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    let t₀ := fun n => mixingTimeK (Pt n) (gibbs (V n)) (meanBall (V n) c) η
    (∀ᶠ n in atTop, t₀ n < ⊤) ∧
      Tendsto (fun n => (t₀ n).toReal / criticalTime n (spectralGap (V n))) atTop (𝓝 1) ∧
      Tendsto (fun n => spectralGap (V n) * (t₀ n).toReal) atTop atTop ∧
      Tendsto (fun n => (t₀ n).toReal) atTop atTop

/-- **Wasserstein mixing time of rigid sequences**, Brownian-free form. -/
theorem mixing_time_w2_rigid_K {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    (h : IsRigidSequenceK V Pt) {c : ℝ} (hc : 0 < c) {η : ℝ} (hη : 0 < η) :
    let t₀ := fun n => mixingTimeW2K (Pt n) (gibbs (V n)) (meanBall (V n) c) η
    (∀ᶠ n in atTop, t₀ n < ⊤) ∧
      Tendsto (fun n => (t₀ n).toReal / criticalTime n (spectralGap (V n))) atTop (𝓝 1) ∧
      Tendsto (fun n => spectralGap (V n) * (t₀ n).toReal) atTop atTop ∧
      ((fun n => spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n) →
        Tendsto (fun n => (t₀ n).toReal) atTop atTop)

/-- **Entropy mixing time of rigid sequences**, Brownian-free form. -/
theorem mixing_time_kl_rigid_K {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    (h : IsRigidSequenceK V Pt)
    (hsmall : (fun n => spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n))
    {c : ℝ} (hc : 0 < c) {η : ℝ} (hη : 0 < η) :
    let t₀ := fun n => mixingTimeKLK (Pt n) (gibbs (V n)) (meanBall (V n) c) η
    (∀ᶠ n in atTop, t₀ n < ⊤) ∧
      Tendsto (fun n => (t₀ n).toReal / criticalTime n (spectralGap (V n))) atTop (𝓝 1) ∧
      Tendsto (fun n => spectralGap (V n) * (t₀ n).toReal) atTop atTop ∧
      Tendsto (fun n => (t₀ n).toReal) atTop atTop
```
(Exact compiled text is in the file; the above is the same with proofs elided. Docstrings in the file are minimal; use the ones above when wiring.)

## Notes
* `product_condition_cutoff_K` / `convex_interaction_cutoff_K` need no uniform carrier: `exists_langevinSeq_of_K` picks carriers per dimension
  (dummy `Unit` for n = 0); the conclusion is transferred via `eventually_worst_eq_worstK`, `mixingTime_eq_mixingTimeK` for n > 0.
* The kernel versions of the 7 theorems are implied by the Brownian versions only through the transfer; none of the Brownian theorems was modified.
* Not human-reviewed.
