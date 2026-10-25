# Vendored third-party Lean code

This directory contains unmodified-or-minimally-patched copies of parts of two Apache-2.0 Lean libraries, used only to prove
`CutCur.exists_stdBrownian` and `CutCur.exists_langevin` (through `CutoffRigidity/Paper/ExistsBrownian.lean`). Nothing in `Challenge.lean`
depends on them.

Credit: Rémy Degenne, Sebastian Ledvinka, Etienne Marion, Peter Pfaffelhuber, *Formalization of Brownian motion in Lean*,
arXiv:2511.20118 (https://arxiv.org/abs/2511.20118), and the Kolmogorov extension theorem of Degenne and Pfaffelhuber.

## Origins

| Directory | Upstream | Commit |
| --- | --- | --- |
| `brownian-motion/` | https://github.com/RemyDegenne/brownian-motion | `546d77295fdf8ae7f44cec14ec5df7959c4e3617` (2026-10-23) |
| `kolmogorov_extension4/` | https://github.com/RemyDegenne/kolmogorov_extension4 | `c20f168ed693537c78111ffeabc2ab5f384e35d6` (2026-10-15) |

Copied: the 26 modules of `BrownianMotion/{Auxiliary,Continuity,Gaussian}` in the transitive import closure of
`BrownianMotion.Gaussian.BrownianMotion` (the other upstream modules, including everything with `sorry`, are not copied), and the three modules of
`KolmogorovExtension4`. Lakefile entries (`globs`) are in `../lakefile.toml`.

## Modifications (Apache-2.0, section 4(b))

Upstream needs a newer Mathlib than this project (toolchain `v4.35.0-rc2`, Mathlib `065356127b`). The following minimal porting changes were made;
each modified file carries a `-- MODIFIED` comment after its header.
1. `brownian-motion/BrownianMotion/Continuity/IsKolmogorovProcess.lean`: three lines `have hqd_nonneg : (0 : ℝ) ≤ q - d := sub_nonneg.2 hdq_lt.le`
   added before three `gcongr` calls (this Mathlib's `gcongr` does not discharge `0 ≤ q - d` itself).
2. `brownian-motion/BrownianMotion/Continuity/KolmogorovChentsov.lean`: one `.aemeasurable` dropped (this Mathlib's
   `tendstoInMeasure_of_tendsto_ae_of_measurable_edist` takes `Measurable`).
3. `kolmogorov_extension4/KolmogorovExtension4/CompactSystem.lean`: one added line `public import Compat.CompactSystemExtra`.
4. NEW, not upstream: `kolmogorov_extension4/Compat/CompactSystemExtra.lean`, a backport of material from Mathlib PRs #36089, #36225, #36160
   (`IsCompactSystem.{supClosure,countableInfClosure,prod,pi}`, `compactClosedSquareCylinders`, and four `Set.iInter_*` lemmas, three of them
   re-proved). It can be deleted when the project's Mathlib is bumped.

All other files are byte-identical to the upstream commits. Every file uses the `module` system, is below 10000 lines and contains no
`sorry`, `axiom` or `native_decide`; `#print axioms CutCur.exists_stdBrownian` shows `propext`, `Classical.choice`, `Quot.sound` only.

## Licence

Both upstream repositories are Apache-2.0; their licence texts are in `brownian-motion/LICENSE` and `kolmogorov_extension4/LICENSE`, and the
copyright headers of all files are kept. The project root keeps its own single `LICENSE` (Apache-2.0).

    Licensed under the Apache License, Version 2.0 (the "License"); you may not use these files except in compliance with the License.
    You may obtain a copy of the License at http://www.apache.org/licenses/LICENSE-2.0. Unless required by applicable law or agreed to
    in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.
