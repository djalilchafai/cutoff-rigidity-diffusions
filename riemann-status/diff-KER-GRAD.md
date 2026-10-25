# diff-KER-GRAD: local gradient bounds -- DONE
Build: `lake build CutoffRigidity.Riemann.DiffKerGrad`; axioms of both main theorems: propext, Classical.choice, Quot.sound. No existing file edited.
Namespace `CutoffRigidity.Riemann.Diff`. Standing hypotheses as DiffKer1 (`hV`, `[IsFiniteMeasure μ]`, `hμ`).
| file | lines |
|---|---|
| DiffKerGrad1.lean | 173 (`chart_deriv_bound`: closed graph into `C(closure W, F)`, uniform limits of derivatives) |
| DiffKerGrad2.lean | 122 (`local_grad_bound_nhds`, `local_grad_bound_of_smooth_rep`, `Tc_grad_bound`) |
| DiffKerGrad.lean | 4 |
* `chart_deriv_bound B hB x₀ (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWT : closure W ⊆ (chartAt F x₀).target) : ∃ C, ∀ u ū, MSmooth F ū → B u =ᵐ ū → ∀ z ∈ W, ‖gradient (ū ∘ (chartAt F x₀).symm) z‖ ≤ C * ‖u‖`
* `local_grad_bound_of_smooth_rep B hB (hK : IsCompact K) : ∃ C, ∀ u ū, MSmooth F ū → B u =ᵐ ū → ∀ x ∈ K, ‖mgrad F ū x‖ ≤ C * ‖u‖` (exact requested statement)
* `Tc_grad_bound (ht : t ≠ 0) (hK : IsCompact K) : ∃ C, ∀ u, ∀ x ∈ K, ‖mgrad F (Tc F hV hμ t u) x‖ ≤ C * ‖u‖`
Note: closed graph target is `C(Kc, F)` (gradient), since `C(Kc, StrongDual ℝ F)` failed instance unification.
