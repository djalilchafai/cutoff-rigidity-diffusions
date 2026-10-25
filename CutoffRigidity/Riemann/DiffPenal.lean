module

public import CutoffRigidity.Riemann.DiffInstance2
public import CutoffRigidity.Riemann.DiffEig1
public import CutoffRigidity.BoundedL2Multiplier

/-! # Penalized resolvent (workstream PENAL, P1 of `riemann-status/CO_PLAN.md`)

For a smooth potential `0 ≤ κ ≤ B` and `lam > 0` we construct the unique `v ∈ Q` with
`E(v,φ) + lam ⟪v,φ⟫ + ∫ κ v φ dμ = ⟪g,φ⟫` for all `φ ∈ Q` (`IsPenal lam κ g v`), by a contraction
argument on `R_{lam+B}` (the Neumann series of the plan), and prove positivity, monotonicity
in `g` and in `κ`, comparison with the resolvent and with constants, the energy identity.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal Topology NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Penal

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

/-- A smooth potential with values in `[0, B]`. -/
def PotOK (κ : M → ℝ) (B : ℝ) : Prop := MSmooth F κ ∧ ∀ x, 0 ≤ κ x ∧ κ x ≤ B

variable {F}

theorem PotOK.nonneg {κ : M → ℝ} {B : ℝ} (h : PotOK F κ B) (x : M) : 0 ≤ κ x := (h.2 x).1

theorem PotOK.le {κ : M → ℝ} {B : ℝ} (h : PotOK F κ B) (x : M) : κ x ≤ max B 0 :=
  (h.2 x).2.trans (le_max_left _ _)

theorem PotOK.continuous {κ : M → ℝ} {B : ℝ} (h : PotOK F κ B) : Continuous κ :=
  h.1.continuous

/-- The bounded multiplication operator by `κ` on `L²(μ)`. -/
noncomputable def potMul {κ : M → ℝ} {B : ℝ} (h : PotOK F κ B) :
    (M →₂[μ] ℝ) →L[ℝ] (M →₂[μ] ℝ) :=
  boundedL2Multiplier κ h.continuous.aestronglyMeasurable (max B 0) (le_max_right _ _)
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (h.nonneg x)]; exact h.le x)

theorem potMul_coeFn {κ : M → ℝ} {B : ℝ} (h : PotOK F κ B) (u : M →₂[μ] ℝ) :
    (potMul (μ := μ) h u : M → ℝ) =ᵐ[μ] fun x => κ x * u x := by
  filter_upwards [boundedL2Multiplier_coeFn κ h.continuous.aestronglyMeasurable (max B 0)
    (le_max_right _ _) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (h.nonneg x)]; exact h.le x) u (F := ℝ)] with x hx
  rw [potMul, hx]; rfl

theorem inner_potMul {κ : M → ℝ} {B : ℝ} (h : PotOK F κ B) (u φ : M →₂[μ] ℝ) :
    inner ℝ (potMul h u) φ = ∫ x, κ x * (u : M → ℝ) x * (φ : M → ℝ) x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [potMul_coeFn h u] with x hx
  rw [hx]
  simp [mul_comm]

/-- `v` solves the penalized equation `(lam + κ - 𝓛) v = g` weakly in the form domain. -/
structure IsPenal (lam : ℝ) (κ : M → ℝ) (g v : M →₂[μ] ℝ) : Prop where
  mem : v ∈ (diffT F hV hμ).Q
  weak : ∀ φ ∈ (diffT F hV hμ).Q,
    (diffT F hV hμ).E v φ + lam * inner ℝ v φ +
      ∫ x, κ x * (v : M → ℝ) x * (φ : M → ℝ) x ∂μ = inner ℝ g φ

variable {hV hμ}

theorem IsPenal.sub {lam : ℝ} {κ : M → ℝ} {B : ℝ} (hκ : PotOK F κ B) {g g' v v' : M →₂[μ] ℝ}
    (h : IsPenal hV hμ lam κ g v) (h' : IsPenal hV hμ lam κ g' v') :
    IsPenal hV hμ lam κ (g - g') (v - v') := by
  refine ⟨(diffT F hV hμ).Q_sub h.mem h'.mem, fun φ hφ => ?_⟩
  have e1 := h.weak φ hφ
  have e2 := h'.weak φ hφ
  rw [← inner_potMul hκ] at e1 e2 ⊢
  rw [(diffT F hV hμ).E_sub_left h.mem h'.mem hφ, map_sub, inner_sub_left, inner_sub_left,
    inner_sub_left]
  linarith

theorem IsPenal.zero {lam : ℝ} {κ : M → ℝ} :
    IsPenal hV hμ lam κ (0 : M →₂[μ] ℝ) 0 := by
  refine ⟨(diffT F hV hμ).Q_zero, fun φ hφ => ?_⟩
  have h0 : (diffT F hV hμ).E 0 φ = 0 := by
    have := (diffT F hV hμ).E_smul_left 0 (u := 0) (v := φ) (diffT F hV hμ).Q_zero hφ
    simpa using this
  have h1 : ∫ x, κ x * ((0 : M →₂[μ] ℝ) : M → ℝ) x * (φ : M → ℝ) x ∂μ = 0 := by
    have : ∀ᵐ x ∂μ, κ x * ((0 : M →₂[μ] ℝ) : M → ℝ) x * (φ : M → ℝ) x = 0 := by
      filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
      rw [hx]; simp
    rw [integral_congr_ae this]; simp
  rw [h0, h1]; simp

/-- Coercivity: the penalized problem has at most one solution. -/
theorem IsPenal.unique {lam : ℝ} (hlam : 0 < lam) {κ : M → ℝ} {B : ℝ} (hκ : PotOK F κ B)
    {g v v' : M →₂[μ] ℝ} (h : IsPenal hV hμ lam κ g v) (h' : IsPenal hV hμ lam κ g v') :
    v = v' := by
  have hd := h.sub hκ h'
  rw [sub_self] at hd
  set w := v - v' with hw
  have hwQ := hd.mem
  have e := hd.weak w hwQ
  rw [inner_zero_left] at e
  have hE := (diffT F hV hμ).E_nonneg hwQ
  have hP : 0 ≤ ∫ x, κ x * (w : M → ℝ) x * (w : M → ℝ) x ∂μ :=
    integral_nonneg fun x => by
      have := hκ.nonneg x
      simp only [Pi.zero_apply]
      nlinarith [sq_nonneg ((w : M → ℝ) x)]
  have hn : lam * inner ℝ w w = 0 := by
    have : 0 ≤ lam * inner ℝ w w := mul_nonneg hlam.le (real_inner_self_nonneg)
    linarith
  have : inner ℝ w w = 0 := by
    rcases mul_eq_zero.1 hn with h | h
    · exact absurd h hlam.ne'
    · exact h
  have hw0 : w = 0 := inner_self_eq_zero.1 this
  exact sub_eq_zero.1 hw0

/-- The complement multiplier `Bp - κ` (`Bp = max B 0`) as `Bp • id - potMul`. -/
noncomputable def negMul {κ : M → ℝ} {B : ℝ} (h : PotOK F κ B) :
    (M →₂[μ] ℝ) →L[ℝ] (M →₂[μ] ℝ) :=
  max B 0 • ContinuousLinearMap.id ℝ (M →₂[μ] ℝ) - potMul h

theorem negMul_coeFn {κ : M → ℝ} {B : ℝ} (h : PotOK F κ B) (u : M →₂[μ] ℝ) :
    (negMul (μ := μ) h u : M → ℝ) =ᵐ[μ] fun x => (max B 0 - κ x) * u x := by
  filter_upwards [Lp.coeFn_sub ((max B 0) • u) (potMul h u), Lp.coeFn_smul (max B 0) u,
    potMul_coeFn h u] with x h1 h2 h3
  have : negMul (μ := μ) h u = (max B 0) • u - potMul h u := by
    simp [negMul]
  rw [this, h1, Pi.sub_apply, h2, h3, Pi.smul_apply, smul_eq_mul]
  ring

theorem norm_negMul_le {κ : M → ℝ} {B : ℝ} (h : PotOK F κ B) (u : M →₂[μ] ℝ) :
    ‖negMul (μ := μ) h u‖ ≤ max B 0 * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [negMul_coeFn h u] with x hx
  rw [hx, norm_mul, Real.norm_eq_abs, abs_of_nonneg (by linarith [h.le x] : 0 ≤ max B 0 - κ x)]
  exact mul_le_mul_of_nonneg_right (by linarith [h.nonneg x]) (norm_nonneg _)

theorem negMul_nonneg {κ : M → ℝ} {B : ℝ} (h : PotOK F κ B) {u : M →₂[μ] ℝ} (hu : 0 ≤ u) :
    0 ≤ negMul (μ := μ) h u := by
  rw [← Lp.coeFn_nonneg] at hu ⊢
  filter_upwards [negMul_coeFn h u, hu] with x h1 h2
  rw [h1]
  exact mul_nonneg (by linarith [h.le x]) h2

theorem eq_resolvent_of_weak' {lam : ℝ} (hlam : 0 < lam) {u : M →₂[μ] ℝ}
    (hu : u ∈ (diffT F hV hμ).Q) (g : M →₂[μ] ℝ)
    (h : ∀ φ ∈ (diffT F hV hμ).Q, (diffT F hV hμ).E u φ + lam * inner ℝ u φ = inner ℝ g φ) :
    u = (diffFR F hV hμ).resolvent lam g := by
  refine (diffFR F hV hμ).eq_resolvent_of_weak hlam hu g (fun φ => ?_)
  have e := (diffFR F hV hμ).Eext_of_mem hu φ.2
  have h' := h φ φ.2
  change (diffFR F hV hμ).Eext u φ + _ = _ at h'
  rwa [e] at h'

theorem penalized_exists_aux {lam : ℝ} (hlam : 0 < lam) {κ : M → ℝ} {B : ℝ} (hκ : PotOK F κ B)
    (g : M →₂[μ] ℝ) :
    ∃ v : M →₂[μ] ℝ, IsPenal hV hμ lam κ g v ∧ (0 ≤ g → 0 ≤ v) := by
  set Bp : ℝ := max B 0 with hBp
  have hBp0 : 0 ≤ Bp := le_max_right _ _
  set m : ℝ := lam + Bp with hm
  have hm0 : 0 < m := by linarith
  set R := (diffFR F hV hμ).resolvent m with hR
  have hRn : ‖R‖ ≤ 1 / m := (diffFR F hV hμ).norm_resolvent_le hm0
  set Φ : (M →₂[μ] ℝ) → (M →₂[μ] ℝ) := fun v => R (g + negMul hκ v) with hΦ
  set K : ℝ≥0 := ⟨Bp / m, div_nonneg hBp0 hm0.le⟩ with hK
  have hKlt : K < 1 := by
    rw [← NNReal.coe_lt_coe]
    show Bp / m < 1
    rw [div_lt_one hm0]; linarith
  have hlip : LipschitzWith K Φ := by
    refine LipschitzWith.of_dist_le_mul fun v w => ?_
    rw [dist_eq_norm, dist_eq_norm]
    have : Φ v - Φ w = R (negMul hκ (v - w)) := by
      simp only [hΦ, map_add, map_sub]; abel
    rw [this]
    calc ‖R (negMul hκ (v - w))‖ ≤ ‖R‖ * ‖negMul hκ (v - w)‖ := R.le_opNorm _
      _ ≤ (1 / m) * (Bp * ‖v - w‖) :=
        mul_le_mul hRn (norm_negMul_le hκ _) (norm_nonneg _) (by positivity)
      _ = (K : ℝ) * ‖v - w‖ := by
        rw [hK]; show 1 / m * (Bp * ‖v - w‖) = Bp / m * ‖v - w‖; field_simp
  have hc : ContractingWith K Φ := ⟨hKlt, hlip⟩
  set v := ContractingWith.fixedPoint Φ hc with hv
  have hfix : Φ v = v := ContractingWith.fixedPoint_isFixedPt (f := Φ) hc
  have hdr := diff_dirResolvent F hV hμ hm0
  refine ⟨v, ⟨?_, fun φ hφ => ?_⟩, fun hg => ?_⟩
  · rw [← hfix]; exact hdr.mem _
  · have h1 := hdr.weak (g + negMul hκ v) φ hφ
    have hvR : R (g + negMul hκ v) = v := hfix
    rw [hvR] at h1
    have e : negMul (μ := μ) hκ v = Bp • v - potMul hκ v := by simp [negMul, hBp]
    rw [e, inner_add_left, inner_sub_left, inner_smul_left] at h1
    simp only [RCLike.conj_to_real] at h1
    rw [← inner_potMul hκ]
    have : m = lam + Bp := rfl
    rw [this] at h1
    linarith
  · have hn : ∀ n, 0 ≤ Φ^[n] 0 := by
      intro n
      induction n with
      | zero => exact le_rfl
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        have h1 : 0 ≤ g + negMul hκ (Φ^[n] 0) := add_nonneg hg (negMul_nonneg hκ ih)
        rw [← Lp.coeFn_nonneg] at h1 ⊢
        exact diff_resolvent_nonneg F hV hμ hm0 _ h1
    exact ge_of_tendsto' (ContractingWith.tendsto_iterate_fixedPoint hc 0) hn

theorem penalized_exists {lam : ℝ} (hlam : 0 < lam) {κ : M → ℝ} {B : ℝ} (hκ : PotOK F κ B)
    (g : M →₂[μ] ℝ) : ∃ v : M →₂[μ] ℝ, IsPenal hV hμ lam κ g v := by
  obtain ⟨v, hv, _⟩ := penalized_exists_aux (hV := hV) (hμ := hμ) hlam hκ g
  exact ⟨v, hv⟩

/-- Positivity (Neumann series with the positive resolvent `R_{lam+B}`). -/
theorem penalized_nonneg {lam : ℝ} (hlam : 0 < lam) {κ : M → ℝ} {B : ℝ} (hκ : PotOK F κ B)
    {g v : M →₂[μ] ℝ} (h : IsPenal hV hμ lam κ g v) (hg : 0 ≤ᵐ[μ] g) : 0 ≤ᵐ[μ] v := by
  obtain ⟨v', hv', hpos⟩ := penalized_exists_aux (hV := hV) (hμ := hμ) hlam hκ g
  have := h.unique hlam hκ hv'
  subst this
  exact (Lp.coeFn_nonneg _).2 (hpos ((Lp.coeFn_nonneg _).1 hg))

/-- Monotonicity in the right-hand side. -/
theorem penalized_mono {lam : ℝ} (hlam : 0 < lam) {κ : M → ℝ} {B : ℝ} (hκ : PotOK F κ B)
    {g g' v v' : M →₂[μ] ℝ} (h : IsPenal hV hμ lam κ g v) (h' : IsPenal hV hμ lam κ g' v')
    (hg : g ≤ᵐ[μ] g') : v ≤ᵐ[μ] v' := by
  have hd := h'.sub hκ h
  have h0 : 0 ≤ᵐ[μ] (g' - g : M →₂[μ] ℝ) := by
    filter_upwards [Lp.coeFn_sub g' g, hg] with x h1 h2
    rw [h1, Pi.sub_apply]; simpa using h2
  have := penalized_nonneg hlam hκ hd h0
  filter_upwards [Lp.coeFn_sub v' v, this] with x h1 h2
  rw [h1, Pi.sub_apply] at h2
  simpa using h2

/-- Monotonicity in the potential: a larger killing rate gives a smaller solution. -/
theorem penalized_anti {lam : ℝ} (hlam : 0 < lam) {κ κ' : M → ℝ} {B B' : ℝ}
    (hκ : PotOK F κ B) (hκ' : PotOK F κ' B') (hle : ∀ x, κ x ≤ κ' x)
    {g v v' : M →₂[μ] ℝ} (hg : 0 ≤ᵐ[μ] g) (h : IsPenal hV hμ lam κ g v)
    (h' : IsPenal hV hμ lam κ' g v') : v' ≤ᵐ[μ] v := by
  have hv0 : 0 ≤ᵐ[μ] v := penalized_nonneg hlam hκ h hg
  have hG : IsPenal hV hμ lam κ' (potMul hκ' v - potMul hκ v) (v - v') := by
    refine ⟨(diffT F hV hμ).Q_sub h.mem h'.mem, fun φ hφ => ?_⟩
    have e := h.weak φ hφ
    have e' := h'.weak φ hφ
    have e3 : ∫ x, κ' x * ((v - v' : M →₂[μ] ℝ) : M → ℝ) x * (φ : M → ℝ) x ∂μ =
        ∫ x, κ' x * (v : M → ℝ) x * (φ : M → ℝ) x ∂μ -
        ∫ x, κ' x * (v' : M → ℝ) x * (φ : M → ℝ) x ∂μ := by
      rw [← inner_potMul hκ', ← inner_potMul hκ', ← inner_potMul hκ', map_sub, inner_sub_left]
    rw [e3, (diffT F hV hμ).E_sub_left h.mem h'.mem hφ]
    simp only [inner_sub_left, inner_potMul hκ', inner_potMul hκ]
    linarith
  have hG0 : 0 ≤ᵐ[μ] (potMul hκ' v - potMul hκ v : M →₂[μ] ℝ) := by
    filter_upwards [Lp.coeFn_sub (potMul hκ' v) (potMul hκ v), potMul_coeFn hκ' v,
      potMul_coeFn hκ v, hv0] with x h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, h3]
    simp only [Pi.zero_apply] at h4 ⊢
    nlinarith [hle x]
  have := penalized_nonneg hlam hκ' hG hG0
  filter_upwards [Lp.coeFn_sub v v', this] with x h1 h2
  rw [h1, Pi.sub_apply] at h2
  simpa using h2

/-- `R_lam g` is the penalized solution for `κ = 0`. -/
theorem isPenal_resolvent {lam : ℝ} (hlam : 0 < lam) (g : M →₂[μ] ℝ) :
    IsPenal hV hμ lam (fun _ : M => (0 : ℝ)) g ((diffFR F hV hμ).resolvent lam g) := by
  have hdr := diff_dirResolvent F hV hμ hlam
  refine ⟨hdr.mem g, fun φ hφ => ?_⟩
  have := hdr.weak g φ hφ
  simpa using this

theorem potOK_zero : PotOK F (fun _ : M => (0 : ℝ)) 0 :=
  ⟨contMDiff_const, fun x => ⟨le_rfl, le_rfl⟩⟩

/-- The penalized solution is below the resolvent. -/
theorem penalized_le_resolvent {lam : ℝ} (hlam : 0 < lam) {κ : M → ℝ} {B : ℝ}
    (hκ : PotOK F κ B) {g v : M →₂[μ] ℝ} (hg : 0 ≤ᵐ[μ] g) (h : IsPenal hV hμ lam κ g v) :
    v ≤ᵐ[μ] (diffFR F hV hμ).resolvent lam g :=
  penalized_anti hlam potOK_zero hκ (fun x => hκ.nonneg x) hg (isPenal_resolvent hlam g) h

/-- Comparison with constants (uses `E(1, ·) = 0`). -/
theorem penalized_le_const {lam : ℝ} (hlam : 0 < lam) {κ : M → ℝ} {B : ℝ} (hκ : PotOK F κ B)
    {g v : M →₂[μ] ℝ} {c : ℝ} (hc : 0 ≤ c) (hg : g ≤ᵐ[μ] fun _ => c)
    (h : IsPenal hV hμ lam κ g v) : v ≤ᵐ[μ] fun _ => c / lam := by
  set u0 : M →₂[μ] ℝ := (c / lam) • oneL2 μ with hu0
  set g0 : M →₂[μ] ℝ := c • oneL2 μ + (c / lam) • potMul hκ (oneL2 μ) with hg0
  have hQ1 := diff_oneL2_mem_Q F hV hμ
  have hQ1' : oneL2 μ ∈ (diffT F hV hμ).Q := hQ1
  have hu0Q : u0 ∈ (diffT F hV hμ).Q := (diffT F hV hμ).Q_smul _ hQ1'
  have hpen : IsPenal hV hμ lam κ g0 u0 := by
    refine ⟨hu0Q, fun φ hφ => ?_⟩
    have e1 : (diffT F hV hμ).E u0 φ = 0 := by
      rw [hu0, (diffT F hV hμ).E_smul_left _ hQ1' hφ, E_one_left F hV hμ (diffT F hV hμ) hφ,
        mul_zero]
    have e2 : ∫ x, κ x * (u0 : M → ℝ) x * (φ : M → ℝ) x ∂μ =
        (c / lam) * inner ℝ (potMul hκ (oneL2 μ)) φ := by
      rw [inner_potMul hκ, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_smul (c / lam) (oneL2 μ), coeFn_oneL2 μ] with x h1 h2
      rw [hu0, h1, Pi.smul_apply, h2, smul_eq_mul]; ring
    rw [e1, e2, hg0, hu0, inner_add_left, inner_smul_left, inner_smul_left, inner_smul_left]
    simp only [RCLike.conj_to_real]
    field_simp
    ring
  have hle : g ≤ᵐ[μ] g0 := by
    filter_upwards [hg, Lp.coeFn_add (c • oneL2 μ) ((c / lam) • potMul hκ (oneL2 μ)),
      Lp.coeFn_smul c (oneL2 μ), Lp.coeFn_smul (c / lam) (potMul hκ (oneL2 μ)),
      coeFn_oneL2 μ, potMul_coeFn hκ (oneL2 μ)] with x h1 h2 h3 h4 h5 h6
    rw [hg0, h2, Pi.add_apply, h3, h4, Pi.smul_apply, Pi.smul_apply, h6, h5, smul_eq_mul,
      smul_eq_mul]
    have := hκ.nonneg x
    have : 0 ≤ c / lam * (κ x * 1) := by positivity
    simp only [mul_one] at *
    linarith
  have := penalized_mono hlam hκ h hpen hle
  filter_upwards [this, Lp.coeFn_smul (c / lam) (oneL2 μ), coeFn_oneL2 μ] with x h1 h2 h3
  have e : (u0 : M → ℝ) x = c / lam := by
    rw [hu0, h2, Pi.smul_apply, h3, smul_eq_mul, mul_one]
  rw [e] at h1
  exact h1

/-- Energy identity and inequality. -/
theorem penalized_energy_eq {lam : ℝ} {κ : M → ℝ} {g v : M →₂[μ] ℝ}
    (h : IsPenal hV hμ lam κ g v) :
    (diffT F hV hμ).E v v + lam * ‖v‖ ^ 2 + ∫ x, κ x * (v : M → ℝ) x * (v : M → ℝ) x ∂μ =
      inner ℝ g v := by
  have := h.weak v h.mem
  rwa [real_inner_self_eq_norm_sq] at this

theorem penalized_energy {lam : ℝ} {κ : M → ℝ} {B : ℝ} (hκ : PotOK F κ B) {g v : M →₂[μ] ℝ}
    (h : IsPenal hV hμ lam κ g v) :
    (diffT F hV hμ).E v v + lam * ‖v‖ ^ 2 ≤ inner ℝ g v := by
  have := penalized_energy_eq h
  have hP : 0 ≤ ∫ x, κ x * (v : M → ℝ) x * (v : M → ℝ) x ∂μ :=
    integral_nonneg fun x => by
      have := hκ.nonneg x
      simp only [Pi.zero_apply]
      nlinarith [sq_nonneg ((v : M → ℝ) x)]
  linarith

end Penal

end CutoffRigidity.Riemann.Diff
