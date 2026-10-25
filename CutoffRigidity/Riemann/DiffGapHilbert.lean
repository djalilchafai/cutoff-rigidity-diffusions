module

public import CutoffRigidity.Riemann.DiffMarkov
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.InnerProductSpace.Continuous

/-! # Abstract attainment of the spectral gap from compactness of the energy balls (HPOS-G)

Generic Hilbert-space part.  `T` is the Friedrichs form of a `DirFormData`, `e ∈ Q` a unit vector
with `E(e,e) = 0` (the constant function `1`).  If the Poincare inequality with constant `ρ`
holds on `D` for the projection `u ↦ u - ⟪u,e⟫ e`, is sharp on `D`, and the energy balls of `Q` are
totally bounded in `H`, then there is a unit vector `v ∈ Q` orthogonal to `e` with
`E(v,φ) = ρ ⟪v,φ⟫` for all `φ ∈ Q`.
-/

@[expose] public section

open Filter Set
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {S : DirFormData H}
  (T : DirFriedrichs S)

/-- `E(u, d) = ⟪u, A d⟫` for `u ∈ Q` and `d ∈ D`. -/
theorem DirFriedrichs.E_coe_right (u : H) (hu : u ∈ T.Q) (d : S.D) :
    T.E u d = inner ℝ u (S.A d) := by
  obtain ⟨f, hf, hfc⟩ := (T.mem_Q _).1 hu
  have h1 := T.E_lim f (fun _ => d) u d hf hfc tendsto_const_nhds
    (DirFormData.EnCauchy.const d)
  have h2 : Tendsto (fun n => S.en (f n) d) atTop (𝓝 (inner ℝ u (S.A d))) := by
    have : ∀ n, S.en (f n) d = inner ℝ (f n : H) (S.A d) := fun n => S.symm (f n) d
    simp only [this]
    exact hf.inner tendsto_const_nhds
  exact tendsto_nhds_unique h1 h2

/-- Poincare inequality on `D` passes to `Q`. -/
theorem DirFriedrichs.poincare_Q (e : H) (ρ : ℝ)
    (hP : ∀ f : S.D, ρ * ‖(f : H) - inner ℝ (f : H) e • e‖ ^ 2 ≤ S.en f f) {u : H}
    (hu : u ∈ T.Q) : ρ * ‖u - inner ℝ u e • e‖ ^ 2 ≤ T.E u u := by
  obtain ⟨f, hf, hfc⟩ := (T.mem_Q _).1 hu
  have h1 := T.E_lim f f u u hf hfc hf hfc
  have h2 : Tendsto (fun n => ρ * ‖(f n : H) - inner ℝ (f n : H) e • e‖ ^ 2) atTop
      (𝓝 (ρ * ‖u - inner ℝ u e • e‖ ^ 2)) := by
    have : Tendsto (fun n => (f n : H) - inner ℝ (f n : H) e • e) atTop
        (𝓝 (u - inner ℝ u e • e)) :=
      hf.sub ((hf.inner tendsto_const_nhds).smul_const e)
    exact (this.norm.pow 2).const_mul ρ
  exact le_of_tendsto_of_tendsto h2 h1 (Eventually.of_forall fun n => hP (f n))

/-- Lower semicontinuity of the energy along `Q`-sequences with a uniform bound. -/
theorem DirFriedrichs.closed_of_bounded_Q (u : ℕ → H) (hu : ∀ j, u j ∈ T.Q) (u' : H)
    (hlim : Tendsto u atTop (𝓝 u')) (C : ℝ) (hC : ∀ j, T.E (u j) (u j) ≤ C) :
    u' ∈ T.Q ∧ T.E u' u' ≤ C := by
  have hex : ∀ j : ℕ, ∃ d : S.D, ‖(d : H) - u j‖ < 1 / ((j : ℝ) + 1) ∧
      S.en d d < T.E (u j) (u j) + 1 / ((j : ℝ) + 1) := by
    intro j
    obtain ⟨f, hf, hfc⟩ := (T.mem_Q _).1 (hu j)
    have h1 := T.E_lim f f (u j) (u j) hf hfc hf hfc
    have hpos : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    have e1 : ∀ᶠ n in atTop, ‖(f n : H) - u j‖ < 1 / ((j : ℝ) + 1) := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 hf)
      exact this.eventually (Iio_mem_nhds hpos)
    have e2 : ∀ᶠ n in atTop, S.en (f n) (f n) < T.E (u j) (u j) + 1 / ((j : ℝ) + 1) :=
      h1.eventually (Iio_mem_nhds (by linarith))
    obtain ⟨n, hn1, hn2⟩ := (e1.and e2).exists
    exact ⟨f n, hn1, hn2⟩
  choose d hd1 hd2 using hex
  have hdt : Tendsto (fun j => (d j : H)) atTop (𝓝 u') := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun j => ‖u j - u'‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 hlim
    have h1 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1) + ‖u j - u'‖) atTop (𝓝 (0 + 0)) :=
      h1.add h0
    rw [add_zero] at h2
    refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) h2
    calc ‖(d j : H) - u'‖ = ‖((d j : H) - u j) + (u j - u')‖ := by congr 1; abel
      _ ≤ ‖(d j : H) - u j‖ + ‖u j - u'‖ := norm_add_le _ _
      _ ≤ _ := by linarith [hd1 j]
  have key : ∀ J : ℕ, u' ∈ T.Q ∧ T.E u' u' ≤ C + 1 / ((J : ℝ) + 1) := by
    intro J
    refine T.closed_of_bounded (fun k => d (k + J)) u'
      (hdt.comp (tendsto_add_atTop_nat J)) (C + 1 / ((J : ℝ) + 1)) (fun k => ?_)
    have h1 := hd2 (k + J)
    have h2 := hC (k + J)
    have h3 : 1 / (((k + J : ℕ) : ℝ) + 1) ≤ 1 / ((J : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    linarith
  refine ⟨(key 0).1, ?_⟩
  have h1 : Tendsto (fun J : ℕ => C + 1 / ((J : ℝ) + 1)) atTop (𝓝 (C + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
  rw [add_zero] at h1
  exact ge_of_tendsto' h1 fun J => (key J).2

/-- Lower semicontinuity with an eventual bound. -/
theorem DirFriedrichs.closed_of_eventually_bounded (u : ℕ → H) (hu : ∀ j, u j ∈ T.Q) (u' : H)
    (hlim : Tendsto u atTop (𝓝 u')) (C : ℝ)
    (hC : ∀ ε > 0, ∀ᶠ j in atTop, T.E (u j) (u j) ≤ C + ε) :
    u' ∈ T.Q ∧ T.E u' u' ≤ C := by
  have key : ∀ ε > 0, u' ∈ T.Q ∧ T.E u' u' ≤ C + ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hC ε hε)
    exact T.closed_of_bounded_Q (fun j => u (j + N)) (fun j => hu _) u'
      (hlim.comp (tendsto_add_atTop_nat N)) (C + ε) (fun j => hN _ (Nat.le_add_left _ _))
  exact ⟨(key 1 one_pos).1, le_of_forall_pos_le_add fun ε hε => (key ε hε).2⟩

/-- Elementary: a quadratic `2ta + t²b` nonnegative for all `t` forces `a = 0`. -/
theorem eq_zero_of_quad (a b : ℝ) (h : ∀ t : ℝ, 0 ≤ 2 * t * a + t ^ 2 * b) : a = 0 := by
  by_contra ha
  set s : ℝ := 1 / (|b| + 1) with hs
  have hpos : 0 < s := by positivity
  have hsb : s * (|b| + 1) = 1 := by rw [hs]; field_simp
  have hb : s * b ≤ s * |b| := mul_le_mul_of_nonneg_left (le_abs_self b) hpos.le
  have hlt : s * b - 2 < 0 := by nlinarith
  have := h (-a * s)
  have e : 2 * (-a * s) * a + (-a * s) ^ 2 * b = a ^ 2 * s * (s * b - 2) := by ring
  rw [e] at this
  have : a ^ 2 * s * (s * b - 2) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos (by positivity) hpos) hlt
  linarith

variable {T}

/-- Removing the `e`-component does not change the energy when `E(e,·) = 0`. -/
theorem DirFriedrichs.E_sub_smul_left {e : H} (he : e ∈ T.Q) (he0 : T.E e e = 0) {u w : H}
    (hu : u ∈ T.Q) (hw : w ∈ T.Q) (c : ℝ) : T.E (u - c • e) w = T.E u w := by
  rw [T.E_sub_left hu (T.Q_smul c he) hw, T.E_smul_left c he hw,
    T.E_eq_zero_of_self he he0 hw]
  ring

theorem DirFriedrichs.E_sub_smul_self {e : H} (he : e ∈ T.Q) (he0 : T.E e e = 0) {u : H}
    (hu : u ∈ T.Q) (c : ℝ) : T.E (u - c • e) (u - c • e) = T.E u u := by
  have hw := T.Q_sub hu (T.Q_smul c he)
  rw [T.E_sub_smul_left he he0 hu hw c, T.E_comm hu hw, T.E_sub_smul_left he he0 hu hu c]

/-- **Abstract attainment**: Euler-Lagrange eigenvector from compactness. -/
theorem DirFriedrichs.exists_eigen_of_compact [CompleteSpace H] (e : H) (he : e ∈ T.Q)
    (he1 : ‖e‖ = 1) (he0 : T.E e e = 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hP : ∀ f : S.D, ρ * ‖(f : H) - inner ℝ (f : H) e • e‖ ^ 2 ≤ S.en f f)
    (hmin : ∀ δ > 0, ∃ f : S.D, 0 < ‖(f : H) - inner ℝ (f : H) e • e‖ ∧
      S.en f f ≤ (ρ + δ) * ‖(f : H) - inner ℝ (f : H) e • e‖ ^ 2)
    (hcomp : ∀ C : ℝ, TotallyBounded {u : H | u ∈ T.Q ∧ T.E u u + ‖u‖ ^ 2 ≤ C}) :
    ∃ v ∈ T.Q, ‖v‖ = 1 ∧ inner ℝ v e = 0 ∧ ∀ φ ∈ T.Q, T.E v φ = ρ * inner ℝ v φ := by
  -- the minimising sequence
  have hex : ∀ n : ℕ, ∃ f : S.D, 0 < ‖(f : H) - inner ℝ (f : H) e • e‖ ∧
      S.en f f ≤ (ρ + 1 / ((n : ℝ) + 1)) * ‖(f : H) - inner ℝ (f : H) e • e‖ ^ 2 :=
    fun n => hmin _ (by positivity)
  choose f hf1 hf2 using hex
  set p : ℕ → H := fun n => (f n : H) - inner ℝ (f n : H) e • e with hp
  set v : ℕ → H := fun n => (‖p n‖)⁻¹ • p n with hv
  have hpQ : ∀ n, p n ∈ T.Q := fun n => T.Q_sub (T.coe_mem (f n)) (T.Q_smul _ he)
  have hvQ : ∀ n, v n ∈ T.Q := fun n => T.Q_smul _ (hpQ n)
  have hvn : ∀ n, ‖v n‖ = 1 := by
    intro n
    simp only [hv, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (hf1 n).ne'
  have hve : ∀ n, inner ℝ (v n) e = 0 := by
    intro n
    simp only [hv, hp, inner_smul_left, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq,
      he1]
    simp
  have hvE : ∀ n, T.E (v n) (v n) ≤ ρ + 1 / ((n : ℝ) + 1) := by
    intro n
    have h1 : T.E (v n) (v n) = ((‖p n‖)⁻¹) ^ 2 * T.E (p n) (p n) := by
      simp only [hv]
      rw [T.E_smul_left _ (hpQ n) (T.Q_smul _ (hpQ n)), T.E_smul_right _ (hpQ n) (hpQ n)]
      ring
    have h2 : T.E (p n) (p n) = S.en (f n) (f n) := by
      simp only [hp]
      rw [T.E_sub_smul_self he he0 (T.coe_mem (f n)), T.E_coe]
    rw [h1, h2]
    have h3 := hf2 n
    have hpn : 0 < ‖p n‖ := hf1 n
    calc ((‖p n‖)⁻¹) ^ 2 * S.en (f n) (f n)
        ≤ ((‖p n‖)⁻¹) ^ 2 * ((ρ + 1 / ((n : ℝ) + 1)) * ‖p n‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = ρ + 1 / ((n : ℝ) + 1) := by field_simp
  -- compactness
  have hmem : ∀ n, v n ∈ closure {u : H | u ∈ T.Q ∧ T.E u u + ‖u‖ ^ 2 ≤ ρ + 2} := by
    intro n
    refine subset_closure ⟨hvQ n, ?_⟩
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h := hvE n
    rw [hvn n]; linarith
  have hK : IsCompact (closure {u : H | u ∈ T.Q ∧ T.E u u + ‖u‖ ^ 2 ≤ ρ + 2}) :=
    (hcomp _).closure.isCompact_of_isClosed isClosed_closure
  obtain ⟨v0, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hv0n : ‖v0‖ = 1 := by
    have := hlim.norm
    simp only [Function.comp_def, hvn] at this
    exact tendsto_nhds_unique tendsto_const_nhds this |>.symm
  have hv0e : inner ℝ v0 e = 0 := by
    have := Filter.Tendsto.inner (𝕜 := ℝ) hlim (tendsto_const_nhds (x := e))
    simp only [Function.comp_def, hve] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have hlsc : v0 ∈ T.Q ∧ T.E v0 v0 ≤ ρ := by
    refine T.closed_of_eventually_bounded (fun k => v (φ k)) (fun k => hvQ _) v0 hlim ρ ?_
    intro ε hε
    have h1 : Tendsto (fun k => 1 / ((φ k : ℕ) + (1 : ℝ))) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    filter_upwards [h1.eventually (Iio_mem_nhds hε)] with k hk
    have := hvE (φ k)
    linarith
  obtain ⟨hv0Q, hv0E⟩ := hlsc
  have hv0E' : T.E v0 v0 = ρ := by
    have h := T.poincare_Q e ρ hP hv0Q
    rw [hv0e, zero_smul, sub_zero, hv0n] at h
    linarith
  refine ⟨v0, hv0Q, hv0n, hv0e, fun φ' hφ' => ?_⟩
  -- Euler-Lagrange
  set m : ℝ := inner ℝ φ' e with hm
  set a : ℝ := T.E v0 φ' - ρ * inner ℝ v0 φ' with ha
  set b : ℝ := T.E φ' φ' - ρ * ‖φ' - m • e‖ ^ 2 with hb
  have hquad : ∀ t : ℝ, 0 ≤ 2 * t * a + t ^ 2 * b := by
    intro t
    have hw : v0 + t • φ' ∈ T.Q := T.Q_add hv0Q (T.Q_smul t hφ')
    have hP' := T.poincare_Q e ρ hP hw
    have hproj : v0 + t • φ' - inner ℝ (v0 + t • φ') e • e = v0 + t • (φ' - m • e) := by
      rw [inner_add_left, inner_smul_left, hv0e, hm]
      simp only [zero_add, conj_trivial, smul_sub, smul_smul]
      abel
    rw [hproj] at hP'
    have hn : ‖v0 + t • (φ' - m • e)‖ ^ 2 =
        1 + 2 * t * inner ℝ v0 φ' + t ^ 2 * ‖φ' - m • e‖ ^ 2 := by
      rw [norm_add_sq_real, hv0n, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        inner_sub_right, inner_smul_right, hv0e]
      ring
    have hE : T.E (v0 + t • φ') (v0 + t • φ') =
        ρ + 2 * t * T.E v0 φ' + t ^ 2 * T.E φ' φ' := by
      have hq := T.Q_smul t hφ'
      rw [T.E_add_left hv0Q hq (T.Q_add hv0Q hq), T.E_add_right hv0Q hv0Q hq,
        T.E_add_right hq hv0Q hq, T.E_smul_left t hφ' hv0Q, T.E_smul_right t hv0Q hφ',
        T.E_smul_left t hφ' hq, T.E_smul_right t hφ' hφ', T.E_comm hφ' hv0Q, hv0E']
      ring
    rw [hn, hE] at hP'
    simp only [ha, hb]
    nlinarith [hP']
  have := eq_zero_of_quad a b hquad
  simp only [ha] at this
  linarith

end Abstract

end CutoffRigidity.Riemann.Diff
