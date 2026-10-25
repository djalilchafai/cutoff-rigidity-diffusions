# diff-BE: Bakry-Emery gradient bound (A8) and LSI (A9 i) -- DONE, all checked

Module `CutoffRigidity.Riemann.DiffLSI` (imports everything). No sorry/axiom/native_decide; axioms of the main theorems =
propext, Classical.choice, Quot.sound. All files < 500 lines. Namespace `CutoffRigidity.Riemann.Diff`.
Sub-status files: diff-BE-class, -A4, -B, -C, -D, -E1, -E2.

## Main statements
* `BEStrong F V μ ρ Kk` : `‖mgrad (semi Kk t f) x‖ ≤ exp(-ρ t) * ∫ ‖mgrad f y‖ ∂Kk t x` (f test, all t, all x).
* `BEPointwise F V μ ρ Kk` : `carre (semi Kk t f) (semi Kk t f) x ≤ exp(-2ρ t) * ∫ carre f f y ∂Kk t x`.
* `beStrong_of_CD`, `bePointwise_of_CD (hV) [IsFiniteMeasure μ] (hμ) (hρ : 0<ρ) (hCD)` : for `Kk F hV hμ` (the kernel of `exists_kernel`).
* `gradBound_of_CD` : uniform-in-s gradient bound of `semi Kk s g` (field needed by `KerCanonical.toCanonical`).
* `exists_kernel_canonical` : `∃ Kk, KerCanonical F V μ Kk ∧ BEPointwise ... ∧ uniform gradient bound`.
* `lsi_of_CD (hV) [IsProbabilityMeasure μ] (hμ) (hρ) (hCD) (hgap : mSpectralGap F μ = ρ) : LSI F V μ ρ`
  (hgap is used only for the Poincare inequality that gives ergodicity; `poincare_of_gap`).
  `lsi_of_strong_BE` is the abstract version (KerCanonical + BEStrong + Poincare => LSI).
## Route
Only the sqrt version (eps>0) of Bakry-Emery is proved: A(s)=∫(K_sζ)√(Γ(K_{t-s}f)+ε), `green_sqrt` (Kato + integrated Bochner on S),
`hasDerivAt_Afun`, ODE comparison, duality (self-adjointness), eps->0, integrated -> pointwise by continuity + full support; quadratic version by Jensen.
LSI: Fisher decay (Cauchy-Schwarz), de Bruijn `entFun_hasDerivAt`, monotone-function argument, Ent <= Var/mean + Poincare on S, delta->0.
No statement of the plan was false; one deviation: LSI uses hgap for Poincare (CD alone would also give it).
