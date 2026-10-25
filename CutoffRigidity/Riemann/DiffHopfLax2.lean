module

public import CutoffRigidity.Riemann.DiffHopfLax1

/-! # Hopf-Lax inf-convolution, part 2: the key lemma `hlQ_hj` (pointwise Hamilton-Jacobi) -/

@[expose] public section

open Filter Set Topology
open scoped ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace CutoffRigidity.Riemann.Diff

section HL2

variable {X : Type*} [EMetricSpace X] {h : X → ℝ} {Λ : ℝ≥0} {B r : ℝ}

/-- Upper semicontinuity of the set of optimal points: near `y`, every optimal point `z` of `w`
is at distance at most `E + η` from `w`, where `E` bounds the distance of optimal points of `y`. -/
theorem opt_dist_stable (hfin : ∀ x y : X, edist x y ≠ ⊤)
    (hcpt : ∀ (x : X) (R : ℝ), IsCompact {y : X | dd x y ≤ R})
    (hh : LipschitzWith Λ h) (hb : ∀ z, |h z| ≤ B) (hr : 0 < r) (y : X) {E : ℝ}
    (hE : ∀ z, hlQ h r y = h z + dd y z ^ 2 / (2 * r) → dd y z ≤ E) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ∀ w z : X, edist y w < ENNReal.ofReal ε →
      hlQ h r w = h z + dd w z ^ 2 / (2 * r) → dd w z ≤ E + η := by
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ p : X × X, edist y p.1 < ENNReal.ofReal (1 / ((n : ℝ) + 1)) ∧
      hlQ h r p.1 = h p.2 + dd p.1 p.2 ^ 2 / (2 * r) ∧ E + η < dd p.1 p.2 := fun n => by
    obtain ⟨w, z, a, b, c⟩ := hcon (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨(w, z), a, b, c⟩
  choose p hp1 hp2 hp3 using hseq
  have hyw : ∀ n : ℕ, dd y (p n).1 ≤ 1 := fun n => by
    have h1 : dd y (p n).1 < 1 / ((n : ℝ) + 1) :=
      ENNReal.toReal_lt_of_lt_ofReal (hp1 n)
    have h2 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    linarith
  have hzK : ∀ n : ℕ, (p n).2 ∈ {z : X | dd y z ≤ 2 * r * Λ + 1} := fun n => by
    have h1 := opt_dist_le hfin hh hb hr (hp2 n)
    have h2 := dd_triangle hfin y (p n).1 (p n).2
    have := hyw n
    simp only [mem_ofPred_eq]
    linarith
  obtain ⟨a, -, φ, hφ, hlim⟩ := (hcpt y (2 * r * Λ + 1)).tendsto_subseq hzK
  have hbound : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hw : Tendsto (fun n => (p n).1) atTop (𝓝 y) := by
    rw [tendsto_iff_edist_tendsto_0]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound (fun n => zero_le)
      (fun n => by rw [edist_comm]; exact (hp1 n).le)
  have hwφ : Tendsto (fun n => (p (φ n)).1) atTop (𝓝 y) := hw.comp hφ.tendsto_atTop
  have hpair : Tendsto (fun n => ((p (φ n)).1, (p (φ n)).2)) atTop (𝓝 (y, a)) :=
    hwφ.prodMk_nhds hlim
  have hd : Tendsto (fun n => dd (p (φ n)).1 (p (φ n)).2) atTop (𝓝 (dd y a)) :=
    ((continuous_dd hfin).tendsto (y, a)).comp hpair
  have hge : E + η ≤ dd y a := ge_of_tendsto hd (Eventually.of_forall fun n => (hp3 _).le)
  have hQ : Tendsto (fun n => hlQ h r (p (φ n)).1) atTop (𝓝 (hlQ h r y)) :=
    ((continuous_hlQ hfin hcpt hh hb hr).tendsto y).comp hwφ
  have hR : Tendsto (fun n => h (p (φ n)).2 + dd (p (φ n)).1 (p (φ n)).2 ^ 2 / (2 * r)) atTop
      (𝓝 (h a + dd y a ^ 2 / (2 * r))) :=
    ((hh.continuous.tendsto a).comp hlim).add ((hd.pow 2).div_const _)
  have heq : hlQ h r y = h a + dd y a ^ 2 / (2 * r) :=
    tendsto_nhds_unique hQ (hR.congr fun n => (hp2 _).symm)
  have := hE a heq
  linarith

/-- **(HL6)** Pointwise Hamilton-Jacobi inequalities for the Hopf-Lax semigroup. -/
theorem hlQ_hj (hfin : ∀ x y : X, edist x y ≠ ⊤)
    (hcpt : ∀ (x : X) (R : ℝ), IsCompact {y : X | dd x y ≤ R})
    (hh : LipschitzWith Λ h) (hb : ∀ z, |h z| ≤ B) (hr : 0 < r) (y : X) :
    ∃ E : ℝ, 0 ≤ E ∧ lipAt (hlQ h r) y ≤ E / r ∧
      ∀ s > r, hlQ h s y - hlQ h r y ≤ -(E ^ 2 * (s - r)) / (2 * r * s) := by
  obtain ⟨C, hL⟩ := lipschitzWith_hlQ hfin hcpt hh hb hr
  set S : Set X := {z | hlQ h r y = h z + dd y z ^ 2 / (2 * r)} with hS
  have hSc : IsClosed S :=
    isClosed_eq continuous_const
      (hh.continuous.add (((continuous_dd_left hfin y).pow 2).div_const _))
  have hSK : IsCompact S := (hcpt y (2 * r * Λ)).of_isClosed_subset hSc fun z hz =>
    opt_dist_le hfin hh hb hr hz
  obtain ⟨z1, hz1, -⟩ := exists_opt hfin hcpt hh hb hr y
  obtain ⟨z0, hz0S, hz0max⟩ := hSK.exists_isMaxOn ⟨z1, hz1⟩
    (continuous_dd_left hfin y).continuousOn
  have hEmax : ∀ z, hlQ h r y = h z + dd y z ^ 2 / (2 * r) → dd y z ≤ dd y z0 := fun z hz =>
    isMaxOn_iff.1 hz0max z hz
  set E := dd y z0 with hEdef
  have hE0 : 0 ≤ E := dd_nonneg _ _
  refine ⟨E, hE0, ?_, ?_⟩
  · refine lipAt_le_of hfin hL (by positivity) fun c hc => ?_
    have hc' : E / r < c := hc
    have hcr : E < c * r := by rwa [div_lt_iff₀ hr] at hc'
    set η := (c * r - E) / 2 with hη
    have hηdef : 2 * η = c * r - E := by rw [hη]; ring
    have hηpos : 0 < η := by rw [hη]; linarith
    obtain ⟨ε₀, hε₀, hε₀'⟩ := opt_dist_stable hfin hcpt hh hb hr y hEmax hηpos
    have hεpos : 0 < min ε₀ η := lt_min hε₀ hηpos
    have key : ∀ w w' : X, edist y w < ENNReal.ofReal (min ε₀ η) →
        edist y w' < ENNReal.ofReal (min ε₀ η) → hlQ h r w - hlQ h r w' ≤ c * dd w w' := by
      intro w w' hw hw'
      obtain ⟨z', hz', -⟩ := exists_opt hfin hcpt hh hb hr w'
      have hw'' : edist y w' < ENNReal.ofReal ε₀ :=
        hw'.trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _))
      have hd' := hε₀' w' z' hw'' hz'
      have h1 := hlQ_sub_le_pt hb hr hz' hfin (y := w)
      have h2 : dd y w < min ε₀ η := ENNReal.toReal_lt_of_lt_ofReal hw
      have h3 : dd y w' < min ε₀ η := ENNReal.toReal_lt_of_lt_ofReal hw'
      have h4 := dd_triangle hfin w y w'
      rw [dd_comm w y] at h4
      have h5 := min_le_right ε₀ η
      have hδ := dd_nonneg w w'
      have h6 : dd w w' * (2 * dd w' z' + dd w w') / (2 * r) ≤ c * dd w w' := by
        rw [div_le_iff₀ (by positivity)]
        have : 2 * dd w' z' + dd w w' ≤ c * (2 * r) := by linarith [hηdef]
        nlinarith
      linarith
    refine ⟨min ε₀ η, hεpos, fun w w' hw hw' => ?_⟩
    rw [abs_le]
    have k1 := key w w' hw hw'
    have k2 := key w' w hw' hw
    rw [dd_comm w' w] at k2
    constructor <;> linarith
  · intro s hs
    have hs0 : 0 < s := hr.trans hs
    have h1 := hlQ_le hb hs0 y z0
    have e : dd y z0 ^ 2 / (2 * s) - dd y z0 ^ 2 / (2 * r) = -(E ^ 2 * (s - r)) / (2 * r * s) := by
      rw [hEdef]; field_simp; ring
    have h2 : hlQ h r y = h z0 + dd y z0 ^ 2 / (2 * r) := hz0S
    linarith

end HL2

end CutoffRigidity.Riemann.Diff
