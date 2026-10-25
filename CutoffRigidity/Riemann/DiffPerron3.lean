module

public import CutoffRigidity.Riemann.DiffMarkov

/-! # P4, generic part: energy approximation and the variational distance estimate

Generic over a Friedrichs form `T` (`DirFriedrichs S`) on a real Hilbert space `H`:
* `approx_energy`: every `u ∈ Q` is approximated by `φ ∈ D` for the norm `E + ‖·‖²`;
* `variational_dist`: if `u` solves `(lam - 𝓛) u = g` weakly, `v` solves the penalized equation
  with killing term `P` (a functional with `P φ = 0`, `P v ≥ 0`), then
  `lam ‖u - v‖² ≤ E(u - φ) + lam ‖u - φ‖²`, uniformly in the strength of the killing.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace CutoffRigidity.Riemann.Diff

section Gen

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {S : DirFormData H}
  (T : DirFriedrichs S)

theorem approx_energy {u : H} (hu : u ∈ T.Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : S.D, T.E (u - φ) (u - φ) ≤ ε ∧ ‖u - (φ : H)‖ ≤ ε := by
  obtain ⟨f, hf, hfc⟩ := (T.mem_Q _).1 hu
  obtain ⟨N1, h1⟩ := Metric.tendsto_atTop.1 hf ε hε
  obtain ⟨N2, h2⟩ := hfc ε hε
  refine ⟨f (max N1 N2), ?_, ?_⟩
  · set N := max N1 N2 with hN
    have hseq : ∀ n, (↑(f n - f N) : H) = (f n : H) - f N := fun n => rfl
    have hconv : Tendsto (fun n => ((f n - f N : S.D) : H)) atTop (𝓝 (u - f N)) := by
      simp only [hseq]; exact hf.sub tendsto_const_nhds
    have hcau : S.EnCauchy (fun n => f n - f N) := by
      have h3 := (DirFormData.EnCauchy.const (S := S) (-(f N)))
      have := hfc.add h3
      simpa [sub_eq_add_neg] using this
    have hlim := T.E_lim _ _ _ _ hconv hcau hconv hcau
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    exact (h2 n (le_trans (le_max_right _ _) hn) N (le_max_right _ _)).le
  · have := h1 (max N1 N2) (le_max_left _ _)
    rw [dist_eq_norm] at this
    rw [norm_sub_rev] at this
    exact this.le

theorem variational_dist {lam : ℝ} (hlam : 0 < lam) {u v φ g : H} (hu : u ∈ T.Q) (hv : v ∈ T.Q)
    (hφ : φ ∈ T.Q) (P : H → ℝ)
    (hwu : ∀ ψ ∈ T.Q, T.E u ψ + lam * inner ℝ u ψ = inner ℝ g ψ)
    (hwv : ∀ ψ ∈ T.Q, T.E v ψ + lam * inner ℝ v ψ + P ψ = inner ℝ g ψ)
    (hPφ : P φ = 0) (hPv : 0 ≤ P v) :
    lam * ‖u - v‖ ^ 2 ≤ T.E (u - φ) (u - φ) + lam * ‖u - φ‖ ^ 2 := by
  have hw : u - v ∈ T.Q := T.Q_sub hu hv
  have hq : φ - v ∈ T.Q := T.Q_sub hφ hv
  have hp : u - φ ∈ T.Q := T.Q_sub hu hφ
  have e1 : T.E (u - v) φ + lam * inner ℝ (u - v) φ = 0 := by
    rw [T.E_sub_left hu hv hφ, inner_sub_left]
    have := hwu φ hφ
    have := hwv φ hφ
    linarith
  have e2 : T.E (u - v) v + lam * inner ℝ (u - v) v = P v := by
    rw [T.E_sub_left hu hv hv, inner_sub_left]
    have := hwu v hv
    have := hwv v hv
    linarith
  have e3 : T.E (u - v) (φ - v) + lam * inner ℝ (u - v) (φ - v) = - P v := by
    rw [T.E_sub_right hw hφ hv, inner_sub_right]
    linarith
  have hpq : u - φ = (u - v) - (φ - v) := by abel
  have hq0 : 0 ≤ T.E (φ - v) (φ - v) := T.E_nonneg hq
  have hw0 : 0 ≤ T.E (u - v) (u - v) := T.E_nonneg hw
  have hexp : T.E (u - φ) (u - φ) = T.E (u - v) (u - v) - 2 * T.E (u - v) (φ - v)
      + T.E (φ - v) (φ - v) := by
    rw [hpq, T.E_sub_left hw hq (T.Q_sub hw hq), T.E_sub_right hw hw hq,
      T.E_sub_right hq hw hq, T.E_comm hq hw]
    ring
  have hin : ‖u - φ‖ ^ 2 = ‖u - v‖ ^ 2 - 2 * inner ℝ (u - v) (φ - v) + ‖φ - v‖ ^ 2 := by
    rw [hpq, norm_sub_sq_real]
  have hq1 : 0 ≤ ‖φ - v‖ ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hlam.le hq1]

end Gen

end CutoffRigidity.Riemann.Diff
