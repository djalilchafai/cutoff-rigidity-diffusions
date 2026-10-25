# diff-HPOS-G: gap attainment from compactness of energy balls

Status: DONE. No sorry/axiom; `#print axioms` = propext, Classical.choice, Quot.sound.
Namespace `CutoffRigidity.Riemann.Diff`.

| file | content |
|---|---|
| `DiffGapHilbert.lean` | generic Hilbert part: `DirFriedrichs.E_coe_right`, `poincare_Q`, `closed_of_bounded_Q`, `closed_of_eventually_bounded` (Q-lower semicontinuity), `eq_zero_of_quad`, `exists_eigen_of_compact` (A-E of the brief) |
| `DiffGapManifold.lean` | `mgenerator_congr_of_eventuallyEq` (locality), `integral_mul_generator_comm` (`∫ v 𝓛b = ∫ b 𝓛v`, v smooth, b test), `eq_zero_of_integral_test` (fundamental lemma) |
| `DiffGapAttained.lean` | `norm_sq_proj_testToL2`, `poincare_D`, `poincare_D_sharp`, `gap_attained_of_compact` (statement unchanged) |

Note: `DiffGapAttained1/2.lean` names are NOT mine (DiffGapAttained2 belongs to the LSI agent); my helper modules are `DiffGapHilbert`, `DiffGapManifold`.
