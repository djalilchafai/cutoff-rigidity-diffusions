# diff-KER-REG: smoothness along ⋂_k range(R^k) and of the semigroup -- DONE, fully checked

Build: `lake build CutoffRigidity.Riemann.DiffRegSmooth`. Namespace `CutoffRigidity.Riemann.Diff`. No sorry/axiom/native_decide;
`#print axioms` of all theorems below: propext, Classical.choice, Quot.sound. No existing file edited.

| file | lines | content |
|---|---|---|
| DiffReg1.lean | see wc | `weak_solution_locSob_step` (R^n, g in H^m_loc => u in H^{m+2}_loc), `regularity_step_Rn` (chart format) |
| DiffReg2.lean | see wc | `ChartLocSob`, `locL2_chart`, `chartLocSob_zero`, `chartLocSob_step`, `exists_smooth_of_chart_smooth`, `exists_smooth_of_chartLocSob` |
| DiffRegSmooth.lean | see wc | `chartLocSob_resolvent_pow`, `smooth_rep_of_pow`, `smooth_rep_of_pow_R`, `smooth_rep_semigroup` |

Main statements (standing hypotheses of DiffInstance2):
* `smooth_rep_of_pow (v : M →₂[μ] ℝ) (h : ∀ k, ∃ w, v = (((diffFR F hV hμ).resolvent 1) ^ k) w) : ∃ ū, MSmooth F ū ∧ (v : M → ℝ) =ᵐ[μ] ū`
* `smooth_rep_of_pow_R` : same with `(diffFR F hV hμ).R`.
* `smooth_rep_semigroup {t : ℝ≥0} (ht : t ≠ 0) (u) : ∃ ū, MSmooth F ū ∧ ((diffFR F hV hμ).semigroup t u : M → ℝ) =ᵐ[μ] ū`.
* `weak_solution_locSob_step b hΩ hAs hAsym hAell hϱ hϱpos lam (hg : LocL2 Ω g) hu hweak m (hgm : LocSob b Ω m g) : LocSob b Ω (m+2) u`.
* `chartLocSob_step T hu g hweak m (hg : ChartLocSob F m g) : ChartLocSob F (m+2) u` (any `lam`).
No deviations from the requested statements.

## Follow-up: potentials and interior sup estimate (module `CutoffRigidity.Riemann.DiffRegPot`, imports DiffReg3..8)
Build `lake build CutoffRigidity.Riemann.DiffRegPot`; axioms propext, Classical.choice, Quot.sound; no sorry.
Files: DiffReg3 (REG steps with smooth potential `ℓ`: `weak_solution_locSob_step_pot`, `regularity_step_Rn_pot`), DiffReg4
(`pot_chartTestFn`, `chart_weak_equation_pot`, `chartLocSob_pot`, `Q_smooth_of_weak_eq_pot_gen`, `Q_smooth_of_weak_eq_pot`, `_bdd`),
DiffReg5 (Rn level: `wcoeff_chart`, `wsol_chart`, `weakGrad_of_smooth`, `sobSq_zero_fun`, `sup_estimate_Rn`), DiffReg6
(`chart_eq_of_generator`: smooth `w` with `𝓛w = lam w` on `W` satisfies the chart weak equation), DiffReg7 (`chart_L2_compare`),
DiffReg8 (`local_sup_bound`), DiffRegPot (`interior_sup_estimate_manifold`).
* `Q_smooth_of_weak_eq_pot (hκ : MSmooth F κ) (g) (g') (hg' : MSmooth F g') (hgg' : g =ᵐ g') (hu : u ∈ (diffT F hV hμ).Q) (lam)
  (hweak : ∀ φ ∈ Q, E u φ + lam * ⟪u,φ⟫ + ∫ x, κ x * u x * φ x ∂μ = ⟪g,φ⟫) : ∃ ū, MSmooth F ū ∧ u =ᵐ[μ] ū` (generic `T` version `_gen`);
  `Q_smooth_of_weak_eq_pot_bdd` adds an unused boundedness hypothesis.
* `interior_sup_estimate_manifold (hW : IsOpen W) (hB : IsCompact B) (hBW : B ⊆ W) (lam) : ∃ C, 0 ≤ C ∧ ∀ w, MSmooth F w →
  (∀ y ∈ W, mgenerator F V w y = lam * w y) → MemLp w 2 (μ.restrict W) → ∀ x ∈ B, |w x| ≤ C * (∫ y in W, w y ^ 2 ∂μ) ^ (1/2 : ℝ)`.
  Deviation: the hypothesis `MemLp w 2 (μ.restrict W)` is added (without it the Bochner integral is junk 0 and the bound is false).
