# diff-KER-LAP: Laplace transform of the semigroup
DONE. Files: `CutoffRigidity/Riemann/DiffLap1.lean` (~105 lines), `DiffLaplace.lean` (imports it). Namespace `CutoffRigidity.Riemann.Diff.FormData`.
* `integrableOn_laplace (hlam : 0 < lam) (g) : IntegrableOn (fun s : ℝ => exp (-lam*s) • S.semigroup s.toNNReal g) (Ioi 0)`
* `resolvent_eq_laplace (hlam : 0 < lam) (g : H) : S.resolvent lam g = ∫ s in Ioi (0:ℝ), exp (-lam * s) • S.semigroup s.toNNReal g`
* `inner_resolvent_eq_laplace (hlam) (g φ : H) : ⟪S.resolvent lam g, φ⟫_ℝ = ∫ s in Ioi 0, exp (-lam*s) * ⟪S.semigroup s.toNNReal g, φ⟫_ℝ`
Proof: Psi(s)=e^{-lam s}T_s(R g') has derivative -e^{-lam s}T_s g (g' = (1+(lam-1)R)^{-1} g), tends to 0; `integral_Ioi_of_hasDerivAt_of_tendsto`.
Axioms: propext, Classical.choice, Quot.sound.
