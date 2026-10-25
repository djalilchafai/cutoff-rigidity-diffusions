# diff-BE-D: pointwise Bakry-Emery bound (A8) -- DONE modulo upstream stubs

`lake build CutoffRigidity.Riemann.DiffBEMain` succeeds. No sorry/axiom in my files (DiffBEMain1,2,3, DiffBEMain);
`#print axioms` of final theorems show `sorryAx` ONLY through the upstream stubs
(`inS_semi`, `semi_nonneg`, `integral_semi`, `hasDerivAt_Afun`, `continuousOn_Afun` in DiffBESemi; `green_sqrt` in DiffBEGreen;
`integrable_carre_of_InS` in DiffBEClass). Elementary lemmas (`duality_Kk`, `le_of_integral_le`, `kerCanonical_Kk`) are sorry-free.

Files: DiffBEMain1 (bump, local-to-pointwise `le_of_integral_le`, Jensen, `duality_Kk`), DiffBEMain2 (`kerCanonical_Kk`,
`deriv_Afun_ge`, `Afun_comparison`), DiffBEMain3 (`integrated_grad`), DiffBEMain (defs + main theorems).
Statements as in the task (`BEStrong`, `BEPointwise`, `beStrong_of_CD`, `bePointwise_of_CD`, `gradBound_of_CD`, `exists_kernel_canonical`),
with `[IsFiniteMeasure μ]` instead of probability.
