module

public import Mathlib
public import CutoffRigidity.Extra.Rothaus20
public import CutoffRigidity.Extra.Rothaus18

/-! # Rothaus remark (stage 21): `Compact` from Rellich (`L²`) compactness and a Sobolev-type `L^{2+δ}` bound

`Form.Rellich`: energy balls of mean-zero functions are `L²`-sequentially compact with lower semicontinuous energy
(Rellich–Kondrachov; in the project for compact weighted manifolds: `Qball_totallyBounded_of_tail`).
`Form.Sobolev`: bounded energy and mean zero give a uniform `L^{2+δ}` bound (Sobolev embedding `H¹ ⊂ L^{2+δ}`,
valid on a compact manifold; not in Mathlib/the project).
Together they imply `Form.Compact`, hence the Rothaus alternative.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace CutoffRigidity.Rothaus

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

namespace Form

/-- Rellich-type compactness: `L²`-compactness of energy balls (mean zero), with lower semicontinuous energy. -/
def Rellich (F : Form μ) : Prop :=
  ∀ (B : ℝ) (g : ℕ → X → ℝ), (∀ n, g n ∈ F.Q) → (∀ n, ∫ x, g n x ∂μ = 0) → (∀ n, F.E (g n) ≤ B) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ h ∈ F.Q,
      Tendsto (fun n => ∫ x, (g (φ n) x - h x) ^ 2 ∂μ) atTop (𝓝 0) ∧
      ∀ b : ℝ, (∀ᶠ n in atTop, F.E (g (φ n)) ≤ b) → F.E h ≤ b

/-- Sobolev-type uniform higher integrability: bounded energy and mean zero give a uniform `L^{2+δ}` bound. -/
def Sobolev (F : Form μ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ B : ℝ, ∃ K : ℝ, ∀ f ∈ F.Q, ∫ x, f x ∂μ = 0 → F.E f ≤ B →
    Integrable (fun x => |f x| ^ (2 + δ)) μ ∧ ∫ x, |f x| ^ (2 + δ) ∂μ ≤ K

theorem compact_of_rellich_sobolev [IsProbabilityMeasure μ] (F : Form μ) (hR : F.Rellich) (hS : F.Sobolev) :
    F.Compact := by
  intro B g hg hmean hB
  obtain ⟨φ, hφ, h, hhQ, hL2, hlsc⟩ := hR B g hg hmean hB
  obtain ⟨δ, hδ, hSob⟩ := hS
  obtain ⟨K, hK⟩ := hSob B
  refine ⟨φ, hφ, h, hhQ, hL2, ?_, hlsc⟩
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  have hL2' : Tendsto (fun n => ∫ x, (g (φ (ns n)) x - h x) ^ 2 ∂μ) atTop (𝓝 0) :=
    hL2.comp hns
  obtain ⟨ms, hms, hae⟩ := (tendstoInMeasure_of_sq (fun n => F.memLp _ (hg (φ (ns n))))
    (F.memLp _ hhQ) hL2').exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have := tendsto_L1_Θ (μ := μ) (K := K) hδ (f := fun i => g (φ (ns (ms i)))) (h := h)
    (fun i => (F.memLp _ (hg _)).aestronglyMeasurable) (fun i => F.integrable_Θ _ (hg _))
    (fun i => (hK _ (hg _) (hmean _) (hB _)).1) (fun i => (hK _ (hg _) (hmean _) (hB _)).2)
    (F.memLp _ hhQ).aestronglyMeasurable (F.integrable_Θ _ hhQ) hae
  exact this

end Form

/-- **Rothaus alternative from Rellich compactness and a Sobolev bound.** -/
theorem rothaus_alternative_sobolev [IsProbabilityMeasure μ] (F : Form μ)
    (hPI : ∃ P, 0 ≤ P ∧ ∀ f ∈ F.Q, variance f μ ≤ P * F.E f)
    (hR : F.Rellich) (hS : F.Sobolev) (hgt : 2 * F.optPI < F.optLSI) :
    ∃ f ∈ F.Q, 0 < F.E f ∧ CutCur.entropyOf μ (fun x => f x ^ 2) = F.optLSI * F.E f :=
  rothaus_alternative F hPI (F.compact_of_rellich_sobolev hR hS) hgt

/-- The manuscript's form of the remark under Rellich and Sobolev: finite `C_LSI` different from `2 C_PI`. -/
theorem rothaus_alternative_sobolev_ne [IsProbabilityMeasure μ] (F : Form μ)
    (hPI : ∃ P, 0 ≤ P ∧ ∀ f ∈ F.Q, variance f μ ≤ P * F.E f)
    (hLSI : ∃ c, 0 ≤ c ∧ ∀ f ∈ F.Q, CutCur.entropyOf μ (fun x => f x ^ 2) ≤ c * F.E f)
    (hR : F.Rellich) (hS : F.Sobolev) (hne : F.optLSI ≠ 2 * F.optPI) :
    ∃ f ∈ F.Q, 0 < F.E f ∧ CutCur.entropyOf μ (fun x => f x ^ 2) = F.optLSI * F.E f :=
  rothaus_alternative_ne F hPI hLSI (F.compact_of_rellich_sobolev hR hS) hne

end CutoffRigidity.Rothaus
