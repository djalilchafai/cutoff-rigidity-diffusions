module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! # Abstract Friedrichs form theory used by the diffusion programme (workstream DIR)

Generic statements, over an arbitrary real Hilbert space `H`, about a densely defined symmetric
nonnegative operator `A : D → H` and its Friedrichs form.  The structures `DirFormData`,
`DirFriedrichs`, `DirResolvent` mirror the definitions and conclusions of workstream FR
(`FormData`, `FormData.Q`, `FormData.E`, `FormData.exists_resolvent`): `Q` is the set of
`H`-limits of sequences in `D` that are Cauchy for the energy, `E` is the (well defined) limit of
the energies, and `R` is a bounded operator with `R g ∈ Q` and
`E (R g) φ + λ ⟪R g, φ⟫ = ⟪g, φ⟫` for `φ ∈ Q`.

Main results (all generic):
* `Q` is a subspace containing `D`, `E` is a symmetric nonnegative bilinear form on `Q`.
* `DirFriedrichs.closed_of_bounded`: lower semicontinuity.  If `wₙ ∈ D`, `wₙ → w` in `H` and
  `E(wₙ) ≤ C`, then `w ∈ Q` and `E(w) ≤ C` (Banach-Saks type argument through convex combinations
  and the parallelogram law, so no completeness of `H` is needed).
* `DirFriedrichs.contraction_mem`: a Lipschitz map `T : H → H` mapping `D` to `D` and not
  increasing the energy on `D` maps `Q` to `Q` and does not increase `E`.
* `DirResolvent.fixed_of_comparison`: the variational (Beurling-Deny) argument: if `u = R g` and
  `T` is a normal-contraction type map with `⟪g, T u - u⟫ ≥ 0`, `‖T u‖ ≤ ‖u‖`, then `T u = u`.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace CutoffRigidity.Riemann.Diff

/-- Densely defined symmetric nonnegative operator `A : D → H` (mirror of FR's `FormData`). -/
structure DirFormData (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  D : Submodule ℝ H
  dense : Dense (D : Set H)
  A : D →ₗ[ℝ] H
  symm : ∀ f g : D, inner ℝ (A f) (g : H) = inner ℝ (f : H) (A g)
  nonneg : ∀ f : D, 0 ≤ inner ℝ (A f) (f : H)

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

namespace DirFormData

variable (S : DirFormData H)

/-- The energy `⟪A f, g⟫` on `D`. -/
def en (f g : S.D) : ℝ := inner ℝ (S.A f) (g : H)

theorem en_add_left (f f' g : S.D) : S.en (f + f') g = S.en f g + S.en f' g := by
  simp [en, inner_add_left]

theorem en_add_right (f g g' : S.D) : S.en f (g + g') = S.en f g + S.en f g' := by
  simp [en, inner_add_right]

theorem en_smul_left (c : ℝ) (f g : S.D) : S.en (c • f) g = c * S.en f g := by
  simp [en, inner_smul_left]

theorem en_smul_right (c : ℝ) (f g : S.D) : S.en f (c • g) = c * S.en f g := by
  simp [en, inner_smul_right]

theorem en_sub_left (f f' g : S.D) : S.en (f - f') g = S.en f g - S.en f' g := by
  simp [en, inner_sub_left]

theorem en_sub_right (f g g' : S.D) : S.en f (g - g') = S.en f g - S.en f g' := by
  simp [en, inner_sub_right]

theorem en_comm (f g : S.D) : S.en f g = S.en g f := by
  simp only [en]
  rw [S.symm f g, real_inner_comm]

theorem en_nonneg (f : S.D) : 0 ≤ S.en f f := S.nonneg f

/-- Parallelogram identity for the energy. -/
theorem en_add_add_sub (a b : S.D) :
    S.en (a + b) (a + b) + S.en (a - b) (a - b) = 2 * S.en a a + 2 * S.en b b := by
  simp only [en_add_left, en_add_right, en_sub_left, en_sub_right]
  rw [en_comm S b a]; ring

theorem en_add_le (a b : S.D) : S.en (a + b) (a + b) ≤ 2 * S.en a a + 2 * S.en b b := by
  have := S.en_add_add_sub a b
  have h := S.en_nonneg (a - b)
  linarith

/-- The energy is Cauchy along the sequence `f`. -/
def EnCauchy (f : ℕ → S.D) : Prop :=
  ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, S.en (f m - f n) (f m - f n) < ε

theorem EnCauchy.add {S : DirFormData H} {f g : ℕ → S.D} (hf : S.EnCauchy f) (hg : S.EnCauchy g) :
    S.EnCauchy (fun n => f n + g n) := by
  intro ε hε
  obtain ⟨N1, h1⟩ := hf (ε / 4) (by positivity)
  obtain ⟨N2, h2⟩ := hg (ε / 4) (by positivity)
  refine ⟨max N1 N2, fun m hm n hn => ?_⟩
  have e : f m + g m - (f n + g n) = (f m - f n) + (g m - g n) := by abel
  rw [e]
  have := S.en_add_le (f m - f n) (g m - g n)
  have a := h1 m (le_trans (le_max_left _ _) hm) n (le_trans (le_max_left _ _) hn)
  have b := h2 m (le_trans (le_max_right _ _) hm) n (le_trans (le_max_right _ _) hn)
  linarith

theorem EnCauchy.smul {S : DirFormData H} {f : ℕ → S.D} (hf : S.EnCauchy f) (c : ℝ) :
    S.EnCauchy (fun n => c • f n) := by
  intro ε hε
  obtain ⟨N1, h1⟩ := hf (ε / (c ^ 2 + 1)) (by positivity)
  refine ⟨N1, fun m hm n hn => ?_⟩
  have e : c • f m - c • f n = c • (f m - f n) := by rw [smul_sub]
  rw [e, S.en_smul_left, S.en_smul_right]
  have a := h1 m hm n hn
  have hnn := S.en_nonneg (f m - f n)
  rw [lt_div_iff₀ (by positivity)] at a
  nlinarith [sq_nonneg c]

theorem EnCauchy.const {S : DirFormData H} (f : S.D) : S.EnCauchy (fun _ => f) := by
  intro ε hε
  exact ⟨0, fun m _ n _ => by simpa [DirFormData.en] using hε⟩

end DirFormData

/-- Friedrichs form data (mirror of FR's `FormData.Q` and `FormData.E`): `Q` is the set of
`H`-limits of `D`-sequences Cauchy for the energy, `E` the limit of the energies. -/
structure DirFriedrichs (S : DirFormData H) where
  Q : Set H
  E : H → H → ℝ
  mem_Q : ∀ u, u ∈ Q ↔ ∃ f : ℕ → S.D,
    Tendsto (fun n => (f n : H)) atTop (𝓝 u) ∧ S.EnCauchy f
  E_lim : ∀ (f g : ℕ → S.D) (u v : H), Tendsto (fun n => (f n : H)) atTop (𝓝 u) →
    S.EnCauchy f → Tendsto (fun n => (g n : H)) atTop (𝓝 v) → S.EnCauchy g →
    Tendsto (fun n => S.en (f n) (g n)) atTop (𝓝 (E u v))

/-- A bounded operator which is the resolvent of the form (mirror of FR's `exists_resolvent`). -/
structure DirResolvent {S : DirFormData H} (T : DirFriedrichs S) (lam : ℝ) (R : H →L[ℝ] H) :
    Prop where
  mem : ∀ g, R g ∈ T.Q
  weak : ∀ g, ∀ φ ∈ T.Q, T.E (R g) φ + lam * inner ℝ (R g) φ = inner ℝ g φ

namespace DirFriedrichs

variable {S : DirFormData H} (T : DirFriedrichs S)

theorem coe_mem (f : S.D) : (f : H) ∈ T.Q :=
  (T.mem_Q _).2 ⟨fun _ => f, tendsto_const_nhds, DirFormData.EnCauchy.const f⟩

theorem E_coe (f g : S.D) : T.E f g = S.en f g := by
  have := T.E_lim (fun _ => f) (fun _ => g) f g tendsto_const_nhds
    (DirFormData.EnCauchy.const f) tendsto_const_nhds (DirFormData.EnCauchy.const g)
  exact tendsto_nhds_unique this tendsto_const_nhds

theorem Q_add {u v : H} (hu : u ∈ T.Q) (hv : v ∈ T.Q) : u + v ∈ T.Q := by
  obtain ⟨f, hf, hfc⟩ := (T.mem_Q _).1 hu
  obtain ⟨g, hg, hgc⟩ := (T.mem_Q _).1 hv
  refine (T.mem_Q _).2 ⟨fun n => f n + g n, ?_, hfc.add hgc⟩
  simpa using hf.add hg

theorem Q_smul (c : ℝ) {u : H} (hu : u ∈ T.Q) : c • u ∈ T.Q := by
  obtain ⟨f, hf, hfc⟩ := (T.mem_Q _).1 hu
  refine (T.mem_Q _).2 ⟨fun n => c • f n, ?_, hfc.smul c⟩
  simpa using hf.const_smul c

theorem Q_zero : (0 : H) ∈ T.Q := by
  simpa using T.coe_mem 0

theorem Q_sub {u v : H} (hu : u ∈ T.Q) (hv : v ∈ T.Q) : u - v ∈ T.Q := by
  have := T.Q_add hu (T.Q_smul (-1) hv)
  simpa [sub_eq_add_neg] using this

/-- The subspace `Q`. -/
def Qsub : Submodule ℝ H where
  carrier := T.Q
  add_mem' := fun {_ _} hu hv => T.Q_add hu hv
  zero_mem' := T.Q_zero
  smul_mem' := fun c _ hu => T.Q_smul c hu

theorem E_comm {u v : H} (hu : u ∈ T.Q) (hv : v ∈ T.Q) : T.E u v = T.E v u := by
  obtain ⟨f, hf, hfc⟩ := (T.mem_Q _).1 hu
  obtain ⟨g, hg, hgc⟩ := (T.mem_Q _).1 hv
  have h1 := T.E_lim f g u v hf hfc hg hgc
  have h2 := T.E_lim g f v u hg hgc hf hfc
  have : (fun n => S.en (g n) (f n)) = fun n => S.en (f n) (g n) := funext fun n => S.en_comm _ _
  rw [this] at h2
  exact tendsto_nhds_unique h1 h2

theorem E_add_left {u u' v : H} (hu : u ∈ T.Q) (hu' : u' ∈ T.Q) (hv : v ∈ T.Q) :
    T.E (u + u') v = T.E u v + T.E u' v := by
  obtain ⟨f, hf, hfc⟩ := (T.mem_Q _).1 hu
  obtain ⟨f', hf', hfc'⟩ := (T.mem_Q _).1 hu'
  obtain ⟨g, hg, hgc⟩ := (T.mem_Q _).1 hv
  have h1 := T.E_lim (fun n => f n + f' n) g (u + u') v (by simpa using hf.add hf')
    (hfc.add hfc') hg hgc
  have h2 := (T.E_lim f g u v hf hfc hg hgc).add (T.E_lim f' g u' v hf' hfc' hg hgc)
  simp only [DirFormData.en_add_left] at h1
  exact tendsto_nhds_unique h1 h2

theorem E_smul_left (c : ℝ) {u v : H} (hu : u ∈ T.Q) (hv : v ∈ T.Q) :
    T.E (c • u) v = c * T.E u v := by
  obtain ⟨f, hf, hfc⟩ := (T.mem_Q _).1 hu
  obtain ⟨g, hg, hgc⟩ := (T.mem_Q _).1 hv
  have h1 := T.E_lim (fun n => c • f n) g (c • u) v (by simpa using hf.const_smul c)
    (hfc.smul c) hg hgc
  have h2 := (T.E_lim f g u v hf hfc hg hgc).const_mul c
  simp only [DirFormData.en_smul_left] at h1
  exact tendsto_nhds_unique h1 h2

theorem E_add_right {u v v' : H} (hu : u ∈ T.Q) (hv : v ∈ T.Q) (hv' : v' ∈ T.Q) :
    T.E u (v + v') = T.E u v + T.E u v' := by
  rw [T.E_comm hu (T.Q_add hv hv'), T.E_add_left hv hv' hu, T.E_comm hv hu, T.E_comm hv' hu]

theorem E_smul_right (c : ℝ) {u v : H} (hu : u ∈ T.Q) (hv : v ∈ T.Q) :
    T.E u (c • v) = c * T.E u v := by
  rw [T.E_comm hu (T.Q_smul c hv), T.E_smul_left c hv hu, T.E_comm hv hu]

theorem E_sub_left {u u' v : H} (hu : u ∈ T.Q) (hu' : u' ∈ T.Q) (hv : v ∈ T.Q) :
    T.E (u - u') v = T.E u v - T.E u' v := by
  have h := T.E_add_left hu (T.Q_smul (-1) hu') hv
  rw [T.E_smul_left (-1) hu' hv] at h
  simpa [sub_eq_add_neg] using h

theorem E_sub_right {u v v' : H} (hu : u ∈ T.Q) (hv : v ∈ T.Q) (hv' : v' ∈ T.Q) :
    T.E u (v - v') = T.E u v - T.E u v' := by
  rw [T.E_comm hu (T.Q_sub hv hv'), T.E_sub_left hv hv' hu, T.E_comm hv hu, T.E_comm hv' hu]

theorem E_nonneg {u : H} (hu : u ∈ T.Q) : 0 ≤ T.E u u := by
  obtain ⟨f, hf, hfc⟩ := (T.mem_Q _).1 hu
  have h := T.E_lim f f u u hf hfc hf hfc
  exact ge_of_tendsto' h fun n => S.en_nonneg (f n)

/-- Cauchy-Schwarz type consequence: a vector of zero energy is `E`-orthogonal to everything. -/
theorem E_eq_zero_of_self {u : H} (hu : u ∈ T.Q) (h0 : T.E u u = 0) {v : H} (hv : v ∈ T.Q) :
    T.E u v = 0 := by
  have key : ∀ t : ℝ, 0 ≤ 2 * t * T.E u v + t ^ 2 * T.E v v := by
    intro t
    have := T.E_nonneg (T.Q_add hu (T.Q_smul t hv))
    rw [T.E_add_left hu (T.Q_smul t hv) (T.Q_add hu (T.Q_smul t hv)),
      T.E_add_right hu hu (T.Q_smul t hv), T.E_add_right (T.Q_smul t hv) hu (T.Q_smul t hv),
      T.E_smul_left t hv hu, T.E_smul_right t hu hv, T.E_smul_left t hv (T.Q_smul t hv),
      T.E_smul_right t hv hv, T.E_comm hv hu, h0] at this
    nlinarith
  by_contra hne
  set c := T.E u v
  set d := T.E v v
  have hd := T.E_nonneg hv
  -- choose t = -c / (d + 1)
  have := key (-c / (d + 1))
  have hpos : 0 < d + 1 := by linarith
  have e : 2 * (-c / (d + 1)) * c + (-c / (d + 1)) ^ 2 * d = -c ^ 2 * (d + 2) / (d + 1) ^ 2 := by
    field_simp; ring
  rw [e] at this
  have : -c ^ 2 * (d + 2) / (d + 1) ^ 2 < 0 := by
    apply div_neg_of_neg_of_pos
    · have : 0 < c ^ 2 := by positivity
      nlinarith
    · positivity
  linarith

end DirFriedrichs

namespace DirFriedrichs

variable {S : DirFormData H} (T : DirFriedrichs S)

/-- `E₁ = E + ‖·‖²` on `D`. -/
def e1 (v : S.D) : ℝ := S.en v v + ‖(v : H)‖ ^ 2

theorem e1_nonneg (v : S.D) : 0 ≤ e1 v := by
  have := S.en_nonneg v
  unfold e1; positivity

theorem e1_parallelogram (a b : S.D) :
    e1 (a - b) = 2 * e1 a + 2 * e1 b - 4 * e1 ((1 / 2 : ℝ) • (a + b)) := by
  have h1 := S.en_add_add_sub a b
  have h2 : S.en ((1 / 2 : ℝ) • (a + b)) ((1 / 2 : ℝ) • (a + b)) =
      (1 / 4) * S.en (a + b) (a + b) := by
    rw [S.en_smul_left, S.en_smul_right]; ring
  have h3 : ‖(((1 / 2 : ℝ) • (a + b) : S.D) : H)‖ ^ 2 = (1 / 4) * ‖((a + b : S.D) : H)‖ ^ 2 := by
    rw [Submodule.coe_smul, norm_smul]
    simp only [Real.norm_eq_abs]
    rw [mul_pow]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; ring
  have h4 := parallelogram_law_with_norm ℝ ((a : H)) (b : H)
  have h5 : ‖((a + b : S.D) : H)‖ ^ 2 + ‖((a - b : S.D) : H)‖ ^ 2 =
      2 * ‖(a : H)‖ ^ 2 + 2 * ‖(b : H)‖ ^ 2 := by
    simp only [Submodule.coe_add, Submodule.coe_sub]
    have := h4
    nlinarith [this]
  unfold e1
  rw [h2, h3]
  nlinarith [h1, h5]

/-- **Lower semicontinuity (closedness) of the form.**  If `wₙ ∈ D`, `wₙ → w'` in `H` and the
energies `E(wₙ)` are bounded by `C`, then `w' ∈ Q` and `E(w') ≤ C`. -/
theorem closed_of_bounded (w : ℕ → S.D) (w' : H) (hw : Tendsto (fun n => (w n : H)) atTop (𝓝 w'))
    (C : ℝ) (hC : ∀ n, S.en (w n) (w n) ≤ C) : w' ∈ T.Q ∧ T.E w' w' ≤ C := by
  classical
  set K : ℕ → Set S.D := fun N => convexHull ℝ (w '' Ici N) with hK
  have hKmono : ∀ {N M : ℕ}, N ≤ M → K M ⊆ K N := by
    intro N M hNM
    exact convexHull_mono (image_mono (Ici_subset_Ici.2 hNM))
  have hwK : ∀ N n, N ≤ n → w n ∈ K N := fun N n hn =>
    subset_convexHull ℝ _ ⟨n, hn, rfl⟩
  have hKne : ∀ N, (e1 '' K N).Nonempty := fun N => ⟨e1 (w N), w N, hwK N N le_rfl, rfl⟩
  have hKbdd : ∀ N, BddBelow (e1 '' K N) := fun N => ⟨0, by
    rintro _ ⟨v, -, rfl⟩; exact e1_nonneg v⟩
  set α : ℕ → ℝ := fun N => sInf (e1 '' K N) with hα
  have hαle : ∀ N v, v ∈ K N → α N ≤ e1 v := fun N v hv => csInf_le (hKbdd N) ⟨v, hv, rfl⟩
  have hαmono : Monotone α := by
    intro N M hNM
    exact le_csInf (hKne M) (by rintro _ ⟨v, hv, rfl⟩; exact hαle N v (hKmono hNM hv))
  set B : ℝ := C + ‖w'‖ ^ 2 with hB
  have hαB : ∀ N, α N ≤ B := by
    intro N
    have ht : Tendsto (fun n => C + ‖(w n : H)‖ ^ 2) atTop (𝓝 B) :=
      tendsto_const_nhds.add ((hw.norm).pow 2)
    refine ge_of_tendsto ht ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    exact (hαle N _ (hwK N n hn)).trans (by unfold e1; linarith [hC n])
  have hαt : Tendsto α atTop (𝓝 (⨆ N, α N)) :=
    tendsto_atTop_ciSup hαmono ⟨B, by rintro _ ⟨N, rfl⟩; exact hαB N⟩
  set αI := ⨆ N, α N with hαI
  have hαleI : ∀ N, α N ≤ αI := fun N =>
    le_ciSup ⟨B, by rintro _ ⟨N, rfl⟩; exact hαB N⟩ N
  have hex : ∀ N : ℕ, ∃ v ∈ K N, e1 v < α N + 1 / ((N : ℝ) + 1) := by
    intro N
    have := exists_lt_of_csInf_lt (hKne N) (show sInf (e1 '' K N) < α N + 1 / ((N : ℝ) + 1) by
      have : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
      simp only [hα]; linarith)
    obtain ⟨_, ⟨v, hv, rfl⟩, h⟩ := this
    exact ⟨v, hv, h⟩
  choose v hvK hve using hex
  -- convergence of `v` to `w'` in `H`
  have hvt : Tendsto (fun N => (v N : H)) atTop (𝓝 w') := by
    rw [Metric.tendsto_atTop] at hw ⊢
    intro ε hε
    obtain ⟨N0, hN0⟩ := hw (ε / 2) (by positivity)
    refine ⟨N0, fun N hN => ?_⟩
    have hconv : Convex ℝ {x : S.D | dist (x : H) w' ≤ ε / 2} := by
      have := (convex_closedBall w' (ε / 2)).linear_preimage S.D.subtype
      simpa [Metric.closedBall, Set.preimage] using this
    have hsub : K N0 ⊆ {x : S.D | dist (x : H) w' ≤ ε / 2} := by
      refine convexHull_min ?_ hconv
      rintro _ ⟨n, hn, rfl⟩
      exact (hN0 n hn).le
    have := hsub (hKmono hN (hvK N))
    simp only [Set.mem_ofPred_eq] at this
    linarith
  -- Cauchy property
  have hcau : S.EnCauchy v := by
    intro ε hε
    obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hαt.eventually (Ici_mem_nhds (show αI - ε / 16 < αI by linarith)))
    obtain ⟨N1, hN1⟩ := exists_nat_gt (16 / ε)
    refine ⟨max N0 N1, fun m hm n hn => ?_⟩
    have hm0 : N0 ≤ m := le_trans (le_max_left _ _) hm
    have hn0 : N0 ≤ n := le_trans (le_max_left _ _) hn
    have hmid : (1 / 2 : ℝ) • (v m + v n) ∈ K N0 := by
      have hc := convex_convexHull ℝ (w '' Ici N0)
      have := hc (hKmono hm0 (hvK m)) (hKmono hn0 (hvK n)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      simpa [smul_add] using this
    have h1 := e1_parallelogram (v m) (v n)
    have h2 := hαle N0 _ hmid
    have h3 := hve m
    have h4 := hve n
    have h5 := hαleI m
    have h6 := hαleI n
    have h7 := hN0 N0 le_rfl
    have hinv : ∀ k : ℕ, N1 ≤ k → 1 / ((k : ℝ) + 1) < ε / 16 := by
      intro k hk
      have hk' : (16 / ε) < (k : ℝ) := lt_of_lt_of_le hN1 (by exact_mod_cast hk)
      rw [div_lt_iff₀ (by positivity)] at hk' ⊢
      have : 16 < (k : ℝ) * ε := hk'
      have : (1 : ℝ) < ((k : ℝ) + 1) * (ε / 16) := by nlinarith
      linarith
    have hm1 := hinv m (le_trans (le_max_right _ _) hm)
    have hn1 := hinv n (le_trans (le_max_right _ _) hn)
    have key : e1 (v m - v n) < ε := by
      rw [h1]
      nlinarith
    have : S.en (v m - v n) (v m - v n) ≤ e1 (v m - v n) := by
      unfold e1; nlinarith [sq_nonneg ‖((v m - v n : S.D) : H)‖]
    linarith
  have hmem : w' ∈ T.Q := (T.mem_Q _).2 ⟨v, hvt, hcau⟩
  refine ⟨hmem, ?_⟩
  have hlim := T.E_lim v v w' w' hvt hcau hvt hcau
  have hup : Tendsto (fun N : ℕ => B + 1 / ((N : ℝ) + 1) - ‖(v N : H)‖ ^ 2) atTop
      (𝓝 (B + 0 - ‖w'‖ ^ 2)) := by
    have h0 : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact (tendsto_const_nhds.add h0).sub ((hvt.norm).pow 2)
  have hBC : B + 0 - ‖w'‖ ^ 2 = C := by simp [hB]
  rw [hBC] at hup
  refine le_of_tendsto_of_tendsto hlim hup (Eventually.of_forall fun N => ?_)
  have := hve N
  have := hαB N
  unfold e1 at *
  linarith
  
end DirFriedrichs

namespace DirFriedrichs

variable {S : DirFormData H} (T : DirFriedrichs S)

/-- **Stability of the form domain under Lipschitz maps decreasing the energy on `D`.** -/
theorem contraction_mem (Tm : H → H) (L : ℝ) (hL : ∀ u v, ‖Tm u - Tm v‖ ≤ L * ‖u - v‖)
    (hD : ∀ f : S.D, ∃ g : S.D, (g : H) = Tm f)
    (hE : ∀ f g : S.D, (g : H) = Tm f → S.en g g ≤ S.en f f) {u : H} (hu : u ∈ T.Q) :
    Tm u ∈ T.Q ∧ T.E (Tm u) (Tm u) ≤ T.E u u := by
  obtain ⟨f, hf, hfc⟩ := (T.mem_Q _).1 hu
  choose g hg using fun n => hD (f n)
  have hgt : Tendsto (fun n => (g n : H)) atTop (𝓝 (Tm u)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun n => ‖(f n : H) - u‖) atTop (𝓝 0) :=
      (tendsto_iff_norm_sub_tendsto_zero.1 hf)
    have h1 : Tendsto (fun n => L * ‖(f n : H) - u‖) atTop (𝓝 0) := by
      simpa using h0.const_mul L
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h1
    rw [hg n]
    exact hL _ _
  have hlim := T.E_lim f f u u hf hfc hf hfc
  have hbound : ∀ ε > 0, T.E (Tm u) (Tm u) ≤ T.E u u + ε ∧ Tm u ∈ T.Q := by
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (Iio_mem_nhds
      (show T.E u u < T.E u u + ε by linarith)))
    have := T.closed_of_bounded (fun k => g (k + N)) (Tm u)
      (hgt.comp (tendsto_add_atTop_nat N)) (T.E u u + ε) (fun k => by
        have h1 := hE (f (k + N)) (g (k + N)) (hg _)
        have h2 := hN (k + N) (Nat.le_add_left _ _)
        linarith)
    exact ⟨this.2, this.1⟩
  refine ⟨(hbound 1 one_pos).2, ?_⟩
  exact le_of_forall_pos_le_add fun ε hε => (hbound ε hε).1

/-- **The variational (Beurling-Deny) argument.**  Let `u ∈ Q` solve `E(u,φ) + λ⟪u,φ⟫ = ⟪g,φ⟫`
for all `φ ∈ Q`; if `T` is a Lipschitz map preserving `D`, not increasing the energy on `D`,
not increasing the norm at `u`, and `⟪g, T u - u⟫ ≥ 0`, then `T u = u`. -/
theorem fixed_of_comparison (Tm : H → H) (L : ℝ) (hL : ∀ u v, ‖Tm u - Tm v‖ ≤ L * ‖u - v‖)
    (hD : ∀ f : S.D, ∃ g : S.D, (g : H) = Tm f)
    (hE : ∀ f g : S.D, (g : H) = Tm f → S.en g g ≤ S.en f f) {u : H} (hu : u ∈ T.Q)
    {lam : ℝ} (hlam : 0 < lam) (g : H)
    (hweak : ∀ φ ∈ T.Q, T.E u φ + lam * inner ℝ u φ = inner ℝ g φ)
    (hpos : 0 ≤ inner ℝ g (Tm u - u)) (hnorm : ‖Tm u‖ ≤ ‖u‖) : Tm u = u := by
  obtain ⟨hφ, hEφ⟩ := T.contraction_mem Tm L hL hD hE hu
  set φ := Tm u with hφdef
  have hv : φ - u ∈ T.Q := T.Q_sub hφ hu
  have hexp : T.E (φ - u) (φ - u) = T.E φ φ - 2 * T.E u φ + T.E u u := by
    rw [T.E_sub_left hφ hu hv, T.E_sub_right hφ hφ hu, T.E_sub_right hu hφ hu,
      T.E_comm hu hφ]
    ring
  have hnexp : ‖φ - u‖ ^ 2 = ‖φ‖ ^ 2 - 2 * inner ℝ u φ + ‖u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_comm φ u]
    ring
  have h1 := hweak φ hφ
  have h2 := hweak u hu
  rw [real_inner_self_eq_norm_sq] at h2
  have h3 : ‖φ‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    have := norm_nonneg φ
    nlinarith
  have hpos' : 0 ≤ inner ℝ g φ - inner ℝ g u := by
    rw [inner_sub_right] at hpos; exact hpos
  have hEv := T.E_nonneg hv
  have : lam * ‖φ - u‖ ^ 2 ≤ 0 := by
    rw [hnexp]
    rw [hexp] at hEv
    nlinarith
  have hn : ‖φ - u‖ ^ 2 ≤ 0 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have : ‖φ - u‖ = 0 := by
    have := sq_nonneg ‖φ - u‖
    nlinarith [norm_nonneg (φ - u)]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

end DirFriedrichs

end Abstract

end CutoffRigidity.Riemann.Diff
