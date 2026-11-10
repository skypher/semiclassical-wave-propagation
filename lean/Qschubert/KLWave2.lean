import Qschubert.KLWave

/-!
# The commutator of the wave group with a weight

For a bounded weight `W` with `h = W²` and relative bounds on two derivatives of `h`:
`|⟪y, [cos(sΛ), h] g⟫| ≤ s (8ρ + (2K + 2ρ)s) e^{4ρ s} ‖W y‖ ‖W g‖`, on spectrally truncated vectors (`comm_wave`). This gives the
`O(ε)` commutator bound in `lem:w3`(b) (Lean route: only the `L²` level is needed, and the two-derivative bound comes from the
elliptic estimate).

* `inner_domX_skew`, `inner_domY_skew`: `X* = -X` and `Y* = 1 - Y` on `Dom(-Δ)`;
* `wave_C`, `wave_Bx`, `wave_By`, `wave_D`: the truncated weighted bounds;
* `comm_form`: `⟪(-Δ)q, hp⟫ - ⟪q, h(-Δ)p⟫`, with no derivative on `p`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

lemma domX_toL2 (F : testFn) : domX ⟨toL2 F, toL2_mem_negLapH_domain F⟩ = toL2 (vfTest 1 F) := by
  refine ext_inner_left ℂ fun w => ?_
  refine DenseRange.induction_on denseRange_toL2 w ?_ fun P => ?_
  · exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  · have h1 := inner_X_dom P ⟨toL2 F, toL2_mem_negLapH_domain F⟩
    have h2 := inner_vf_left 1 P F
    simp only [Complex.one_im, Complex.ofReal_zero, zero_mul, add_zero] at h2
    exact neg_injective (h1.symm.trans h2)

lemma domY_toL2 (F : testFn) : domY ⟨toL2 F, toL2_mem_negLapH_domain F⟩ = toL2 (vfTest Complex.I F) := by
  refine ext_inner_left ℂ fun w => ?_
  refine DenseRange.induction_on denseRange_toL2 w ?_ fun P => ?_
  · exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  · have h1 := inner_Y_dom P ⟨toL2 F, toL2_mem_negLapH_domain F⟩
    have h2 := inner_vf_left Complex.I P F
    simp only [Complex.I_im, Complex.ofReal_one, one_mul] at h2
    have h3 := h1.symm.trans h2
    exact neg_injective (add_right_cancel h3)

/-- The graph-norm form of `domX`, on pairs. -/
lemma closure_step (T : L2H' × L2H' → ℂ) (hc : Continuous T)
    (h : ∀ F : testFn, T (toL2 F, negLapH ⟨toL2 F, toL2_mem_negLapH_domain F⟩) = 0) (v : negLapH.domain) :
    T ((v : L2H'), negLapH v) = 0 := by
  have hcl : IsClosed {p | T p = 0} := isClosed_eq hc continuous_const
  have hsub : (negLap.graph : Set (L2H' × L2H')) ⊆ {p | T p = 0} := fun p hp => by
    have hp' : p ∈ negLap.graph := hp
    set q : negLap.graph := ⟨p, hp'⟩ with hq
    have e1 : toL2 (testOf q) = p.1 := toL2_testOf q
    have e2 : negLapH ⟨toL2 (testOf q), toL2_mem_negLapH_domain _⟩ = p.2 := by
      rw [negLapH_toL2]
      exact neg_toL2_lapTest_testOf q
    have := h (testOf q)
    rw [e2] at this
    have hp2 : (toL2 (testOf q), p.2) = p := Prod.ext e1 rfl
    rw [hp2] at this
    exact this
  exact closure_minimal hsub hcl (mem_graphBar_negLapH v)

/-- `⟪Xu, v⟫ = -⟪u, Xv⟫` on `Dom(-Δ)`. -/
lemma inner_domX_skew (u v : negLapH.domain) : ⟪domX u, (v : L2H')⟫_ℂ = -⟪(u : L2H'), domX v⟫_ℂ := by
  have key := closure_step
    (fun p => ⟪domX u, p.1⟫_ℂ + ⟪(u : L2H'), formVec 1 (Or.inl rfl) (formLift (p.1 + p.2))⟫_ℂ)
    ((continuous_const.inner continuous_fst).add (continuous_const.inner
      ((formVec 1 (Or.inl rfl)).continuous.comp (formLift.continuous.comp (continuous_fst.add continuous_snd)))))
    (fun F => by
      have e : formVec 1 (Or.inl rfl) (formLift ((toL2 F : L2H') + negLapH ⟨toL2 F, toL2_mem_negLapH_domain F⟩))
          = domX ⟨toL2 F, toL2_mem_negLapH_domain F⟩ := rfl
      simp only [e, domX_toL2]
      have h := congrArg (starRingEnd ℂ) (inner_X_dom F u)
      simp only [inner_conj_symm, map_neg] at h
      rw [h]
      ring) v
  exact eq_neg_of_add_eq_zero_left key

/-- `⟪Yu, v⟫ = -⟪u, Yv⟫ + ⟪u, v⟫` on `Dom(-Δ)`. -/
lemma inner_domY_skew (u v : negLapH.domain) :
    ⟪domY u, (v : L2H')⟫_ℂ = -⟪(u : L2H'), domY v⟫_ℂ + ⟪(u : L2H'), (v : L2H')⟫_ℂ := by
  have key := closure_step
    (fun p => ⟪domY u, p.1⟫_ℂ + ⟪(u : L2H'), formVec Complex.I (Or.inr rfl) (formLift (p.1 + p.2))⟫_ℂ - ⟪(u : L2H'), p.1⟫_ℂ)
    (((continuous_const.inner continuous_fst).add (continuous_const.inner
      ((formVec Complex.I (Or.inr rfl)).continuous.comp (formLift.continuous.comp (continuous_fst.add continuous_snd))))).sub
      (continuous_const.inner continuous_fst))
    (fun F => by
      have e : formVec Complex.I (Or.inr rfl) (formLift ((toL2 F : L2H') + negLapH ⟨toL2 F, toL2_mem_negLapH_domain F⟩))
          = domY ⟨toL2 F, toL2_mem_negLapH_domain F⟩ := rfl
      simp only [e, domY_toL2]
      have h := congrArg (starRingEnd ℂ) (inner_Y_dom F u)
      simp only [inner_conj_symm, map_neg, map_add] at h
      rw [h]
      ring) v
  have e : domY v = formVec Complex.I (Or.inr rfl) (formLift ((v : L2H') + negLapH v)) := rfl
  rw [← e] at key
  linear_combination key

lemma chiD_zero_J (R : ℝ) : (chiD R 0).J = 0 := by
  have e1 : (chiD R 0).g = (0 : ℂ) • (1 : ℝ → ℂ) := by
    funext x; simp [Cutoff.g, chiD, dR, sincS]
  have h1m : (1 : ℝ → ℂ) ∈ BddMeasurable ℝ := ⟨measurable_one, 1, fun _ => by simp⟩
  show specE.integral _ = 0
  rw [e1, specE.integral_smul _ h1m, zero_smul]

lemma chiD_zero_JS (R : ℝ) : (chiD R 0).JS = 0 := by
  have e2 : (chiD R 0).gS = (0 : ℂ) • (1 : ℝ → ℂ) := by
    funext x; simp [Cutoff.gS, chiD, dR, sincS]
  have h1m : (1 : ℝ → ℂ) ∈ BddMeasurable ℝ := ⟨measurable_one, 1, fun _ => by simp⟩
  show specE.integral _ = 0
  rw [e2, specE.integral_smul _ h1m, zero_smul]

lemma chiD_zero_Bx (R : ℝ) (v : L2H') : (chiD R 0).Bx v = 0 := by
  show formVec 1 (Or.inl rfl) (formLift (((chiD R 0).J + (chiD R 0).JS) v)) = 0
  rw [chiD_zero_J, chiD_zero_JS]; simp

lemma chiD_zero_By (R : ℝ) (v : L2H') : (chiD R 0).By v = 0 := by
  show formVec Complex.I (Or.inr rfl) (formLift (((chiD R 0).J + (chiD R 0).JS) v)) = 0
  rw [chiD_zero_J, chiD_zero_JS]; simp

lemma le_exp_of_sq_le {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ Real.exp (2 * t) * b ^ 2) : a ≤ Real.exp t * b := by
  have hsq : a ^ 2 ≤ (Real.exp t * b) ^ 2 := by
    rw [mul_pow, ← Real.exp_nat_mul]
    push_cast
    exact h
  exact (pow_le_pow_iff_left₀ ha (by positivity) two_ne_zero).1 hsq

section truncated

variable {W : ℂ → ℝ} {C ρ : ℝ} (hW : WaveW W C ρ) (R : ℝ) (u : L2H')
include hW

lemma waveE_zero : waveE W hW R u 0 = ‖mulCL hW.sb ((chiC R 0).J u)‖ ^ 2 := by
  simp only [waveE, chiD_zero_Bx, chiD_zero_By, map_zero, norm_zero]
  ring

/-- The energy, read off term by term. -/
lemma wave_sq {s : ℝ} (hs : 0 ≤ s) :
    waveE W hW R u s ≤ Real.exp (2 * (2 * ρ * s)) * ‖mulCL hW.sb ((chiC R 0).J u)‖ ^ 2 := by
  have := waveE_le hW R u hs
  rw [waveE_zero] at this
  rwa [show 2 * (2 * ρ * s) = 4 * ρ * s by ring]

theorem wave_C {s : ℝ} (hs : 0 ≤ s) :
    ‖mulCL hW.sb ((chiC R s).J u)‖ ≤ Real.exp (2 * ρ * s) * ‖mulCL hW.sb ((chiC R 0).J u)‖ := by
  refine le_exp_of_sq_le (norm_nonneg _) (norm_nonneg _) (le_trans ?_ (wave_sq hW R u hs))
  simp only [waveE]
  nlinarith [sq_nonneg ‖mulCL hW.sb ((chiD R s).Bx u)‖, sq_nonneg ‖mulCL hW.sb ((chiD R s).By u)‖]

theorem wave_Bx {s : ℝ} (hs : 0 ≤ s) :
    ‖mulCL hW.sb ((chiD R s).Bx u)‖ ≤ Real.exp (2 * ρ * s) * ‖mulCL hW.sb ((chiC R 0).J u)‖ := by
  refine le_exp_of_sq_le (norm_nonneg _) (norm_nonneg _) (le_trans ?_ (wave_sq hW R u hs))
  simp only [waveE]
  nlinarith [sq_nonneg ‖mulCL hW.sb ((chiC R s).J u)‖, sq_nonneg ‖mulCL hW.sb ((chiD R s).By u)‖]

theorem wave_By {s : ℝ} (hs : 0 ≤ s) :
    ‖mulCL hW.sb ((chiD R s).By u)‖ ≤ Real.exp (2 * ρ * s) * ‖mulCL hW.sb ((chiC R 0).J u)‖ := by
  refine le_exp_of_sq_le (norm_nonneg _) (norm_nonneg _) (le_trans ?_ (wave_sq hW R u hs))
  simp only [waveE]
  nlinarith [sq_nonneg ‖mulCL hW.sb ((chiC R s).J u)‖, sq_nonneg ‖mulCL hW.sb ((chiD R s).Bx u)‖]

theorem wave_D {s : ℝ} (hs : 0 ≤ s) :
    ‖mulCL hW.sb ((chiD R s).J u)‖ ≤ s * (Real.exp (2 * ρ * s) * ‖mulCL hW.sb ((chiC R 0).J u)‖) := by
  have hρ := hW.ρ0
  have hd : ∀ r, HasDerivAt (fun r => mulCL hW.sb ((chiD R r).J u)) (mulCL hW.sb ((chiC R r).J u)) r := fun r => by
    have h : HasDerivAt (fun r => (chiD R r).J u) _ r := hasDerivAt_clm_apply_C (hasDerivAt_D_J R r) (hasDerivAt_const r u)
    have h2 := hasDerivAt_clm_comp (A := mulCL hW.sb) h
    convert h2 using 1
    simp
  have hb : ∀ r ∈ Icc 0 s, ‖mulCL hW.sb ((chiC R r).J u)‖ ≤ Real.exp (2 * ρ * s) * ‖mulCL hW.sb ((chiC R 0).J u)‖ := fun r hr => by
    refine (wave_C hW R u hr.1).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact Real.exp_le_exp.2 (by nlinarith [hr.2])
  have h := (convex_Icc (0 : ℝ) s).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r _ => (hd r).hasDerivWithinAt) hb (left_mem_Icc.2 hs) (right_mem_Icc.2 hs)
  rw [chiD_zero_J] at h
  simp only [ContinuousLinearMap.zero_apply, map_zero, sub_zero, Real.norm_eq_abs, abs_of_nonneg hs] at h
  linarith

end truncated

/-- The relative bounds on `h = W²` used for the commutator. -/
structure WaveW2 (W : ℂ → ℝ) (C ρ K : ℝ) : Prop extends WaveW W C ρ where
  admX : Adm (vfR 1 fun u => W u ^ 2) C
  admY : Adm (vfR Complex.I fun u => W u ^ 2) C
  mXX : SB (fun w => vfR 1 (vfR 1 fun u => W u ^ 2) w / W w) C
  mYY : SB (fun w => vfR Complex.I (vfR Complex.I fun u => W u ^ 2) w / W w) C
  bXX : ∀ w : ℂ, 0 < w.im → |vfR 1 (vfR 1 fun u => W u ^ 2) w / W w| ≤ K * W w
  bYY : ∀ w : ℂ, 0 < w.im → |vfR Complex.I (vfR Complex.I fun u => W u ^ 2) w / W w| ≤ K * W w
  K0 : 0 ≤ K

lemma cross_bound' {W : ℂ → ℝ} {C ρ : ℝ} (hW : WaveW W C ρ) {m g : ℂ → ℝ} {Cm Cg c : ℝ} (Hm : SB m Cm) (Hg : SB g Cg)
    (he : ∀ w : ℂ, 0 < w.im → g w = m w * W w) (hb : ∀ w : ℂ, 0 < w.im → |m w| ≤ c * W w) (p x : L2H') :
    ‖⟪mulCL Hg p, x⟫_ℂ‖ ≤ c * ‖mulCL hW.sb p‖ * ‖mulCL hW.sb x‖ := by
  have e : ⟪mulCL Hg p, x⟫_ℂ = ⟪mulCL Hm p, mulCL hW.sb x⟫_ℂ := by
    rw [L2.inner_def, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coe_mulCL Hg p, coe_mulCL Hm p, coe_mulCL hW.sb x] with z h1 h2 h3
    rw [h1, h2, h3, he z z.im_pos]
    simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
    ring
  rw [e]
  refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [coe_mulCL Hm p, coe_mulCL hW.sb p] with z h1 h2
  rw [h1, h2, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (hW.pos z z.im_pos), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hb z z.im_pos) (norm_nonneg _)

section comm

variable {W : ℂ → ℝ} {C ρ K : ℝ} (hW : WaveW2 W C ρ K)
include hW

/-- The commutator of `-Δ` with `h`, as a form with no derivative on `p`. -/
theorem comm_form (p q : negLapH.domain) :
    ⟪negLapH q, mulCL hW.adm.sb (p : L2H')⟫_ℂ - ⟪(q : L2H'), mulCL hW.adm.sb (negLapH p)⟫_ℂ
      = 2 * ⟪mulCL hW.adm.sbX (domX q), (p : L2H')⟫_ℂ + ⟪mulCL hW.admX.sbX (q : L2H'), (p : L2H')⟫_ℂ
        + 2 * ⟪mulCL hW.adm.sbY (domY q), (p : L2H')⟫_ℂ + ⟪mulCL hW.admY.sbY (q : L2H'), (p : L2H')⟫_ℂ
        - ⟪mulCL hW.adm.sbY (q : L2H'), (p : L2H')⟫_ℂ := by
  set mp : negLapH.domain := ⟨mulCL hW.adm.sb (p : L2H'), mul_mem_domain hW.adm p⟩ with hmp
  set mq : negLapH.domain := ⟨mulCL hW.adm.sb (q : L2H'), mul_mem_domain hW.adm q⟩ with hmq
  set fX : negLapH.domain := ⟨mulCL hW.adm.sbX (q : L2H'), mul_mem_domain hW.admX q⟩ with hfX
  set fY : negLapH.domain := ⟨mulCL hW.adm.sbY (q : L2H'), mul_mem_domain hW.admY q⟩ with hfY
  have f1 := inner_dom_add q mp
  have f2 := inner_dom_add mq p
  have sym : ⟪negLapH mq, (p : L2H')⟫_ℂ = ⟪(mq : L2H'), negLapH p⟫_ℂ := (negLapH_isPositive.1 mq p).symm
  have e1 : ⟪(q : L2H'), mulCL hW.adm.sb (negLapH p)⟫_ℂ = ⟪(mq : L2H'), negLapH p⟫_ℂ := (inner_mulCL_left _ _ _).symm
  have hXp : domX mp = mulCL hW.adm.sbX (p : L2H') + mulCL hW.adm.sb (domX p) := domX_mul hW.adm p
  have hYp : domY mp = mulCL hW.adm.sbY (p : L2H') + mulCL hW.adm.sb (domY p) := domY_mul hW.adm p
  have hXq : domX mq = mulCL hW.adm.sbX (q : L2H') + mulCL hW.adm.sb (domX q) := domX_mul hW.adm q
  have hYq : domY mq = mulCL hW.adm.sbY (q : L2H') + mulCL hW.adm.sb (domY q) := domY_mul hW.adm q
  have hXf : domX fX = mulCL hW.admX.sbX (q : L2H') + mulCL hW.admX.sb (domX q) := domX_mul hW.admX q
  have hYf : domY fY = mulCL hW.admY.sbY (q : L2H') + mulCL hW.admY.sb (domY q) := domY_mul hW.admY q
  have sX := inner_domX_skew fX p
  have sY := inner_domY_skew fY p
  rw [hXf] at sX
  rw [hYf] at sY
  have cX : ⟪domX q, mulCL hW.adm.sbX (p : L2H')⟫_ℂ = ⟪mulCL hW.adm.sbX (domX q), (p : L2H')⟫_ℂ := (inner_mulCL_left _ _ _).symm
  have cY : ⟪domY q, mulCL hW.adm.sbY (p : L2H')⟫_ℂ = ⟪mulCL hW.adm.sbY (domY q), (p : L2H')⟫_ℂ := (inner_mulCL_left _ _ _).symm
  have mX : ⟪mulCL hW.adm.sb (domX q), domX p⟫_ℂ = ⟪domX q, mulCL hW.adm.sb (domX p)⟫_ℂ := inner_mulCL_left _ _ _
  have mY : ⟪mulCL hW.adm.sb (domY q), domY p⟫_ℂ = ⟪domY q, mulCL hW.adm.sb (domY p)⟫_ℂ := inner_mulCL_left _ _ _
  have tX : mulCL hW.admX.sb (domX q) = mulCL hW.adm.sbX (domX q) := rfl
  have tY : mulCL hW.admY.sb (domY q) = mulCL hW.adm.sbY (domY q) := rfl
  have vX : (fX : L2H') = mulCL hW.adm.sbX (q : L2H') := rfl
  have vY : (fY : L2H') = mulCL hW.adm.sbY (q : L2H') := rfl
  rw [tX, inner_add_left] at sX
  rw [tY, inner_add_left] at sY
  rw [vX] at sX
  rw [vY] at sY
  rw [hXp, hYp, inner_add_right, inner_add_right] at f1
  rw [hXq, hYq, inner_add_left, inner_add_left, sym] at f2
  have hgoal1 : ⟪negLapH q, (mp : L2H')⟫_ℂ = ⟪negLapH q, mulCL hW.adm.sb (p : L2H')⟫_ℂ := rfl
  rw [hgoal1] at f1
  rw [e1, ← f1, ← f2, cX, cY, mX, mY]
  linear_combination (-1 : ℂ) * sX - sY

set_option maxHeartbeats 2000000 in
/-- **The commutator of the truncated wave group with `h`.** -/
theorem comm_wave (R : ℝ) {s : ℝ} (hs : 0 ≤ s) (y g : L2H') :
    ‖⟪(chiC R 0).J y, mulCL hW.adm.sb ((chiC R s).J g)⟫_ℂ - ⟪(chiC R s).J y, mulCL hW.adm.sb ((chiC R 0).J g)⟫_ℂ‖
      ≤ s * (8 * ρ + (2 * K + 2 * ρ) * s) * Real.exp (4 * ρ * s)
          * ‖mulCL hW.sb ((chiC R 0).J y)‖ * ‖mulCL hW.sb ((chiC R 0).J g)‖ := by
  have hρ : 0 ≤ ρ := hW.ρ0
  have hK : 0 ≤ K := hW.K0
  set m := mulCL hW.adm.sb with hm
  set A := ‖mulCL hW.sb ((chiC R 0).J y)‖ with hA
  set B := ‖mulCL hW.sb ((chiC R 0).J g)‖ with hB
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 ≤ B := norm_nonneg _
  set F : ℝ → ℂ := fun r => ⟪(chiC R (s - r)).J y, m ((chiC R r).J g)⟫_ℂ - ⟪(chiD R (s - r)).J y, m ((chiD R r).JS g)⟫_ℂ with hF
  set F' : ℝ → ℂ := fun r => ⟪(chiD R (s - r)).JS y, m ((chiC R r).J g)⟫_ℂ - ⟪(chiD R (s - r)).J y, m ((chiC R r).JS g)⟫_ℂ with hF'
  have hsub : ∀ r : ℝ, HasDerivAt (fun r : ℝ => s - r) (-1) r := fun r => by simpa using (hasDerivAt_id' r).const_sub s
  have hF_d : ∀ r, HasDerivAt F (F' r) r := fun r => by
    have a1 : HasDerivAt (fun r => (chiC R (s - r)).J y) ((chiD R (s - r)).JS y) r := by
      have h' : HasDerivAt ((fun r => (chiC R r).J) ∘ fun r => s - r) _ r := HasDerivAt.scomp r (hasDerivAt_C_J R (s - r)) (hsub r)
      have h'' : HasDerivAt (fun r => (chiC R (s - r)).J y) _ r := hasDerivAt_clm_apply_C h' (hasDerivAt_const r y)
      convert h'' using 1
      simp
    have a2 : HasDerivAt (fun r => (chiD R (s - r)).J y) (-(chiC R (s - r)).J y) r := by
      have h' : HasDerivAt ((fun r => (chiD R r).J) ∘ fun r => s - r) _ r := HasDerivAt.scomp r (hasDerivAt_D_J R (s - r)) (hsub r)
      have h'' : HasDerivAt (fun r => (chiD R (s - r)).J y) _ r := hasDerivAt_clm_apply_C h' (hasDerivAt_const r y)
      convert h'' using 1
      simp
    have a3 : HasDerivAt (fun r => (chiC R r).J g) (-(chiD R r).JS g) r := by
      have h'' : HasDerivAt (fun r => (chiC R r).J g) _ r := hasDerivAt_clm_apply_C (hasDerivAt_C_J R r) (hasDerivAt_const r g)
      convert h'' using 1
      simp
    have a4 : HasDerivAt (fun r => (chiD R r).JS g) ((chiC R r).JS g) r := by
      have h'' : HasDerivAt (fun r => (chiD R r).JS g) _ r := hasDerivAt_clm_apply_C (hasDerivAt_D_JS R r) (hasDerivAt_const r g)
      convert h'' using 1
      simp
    have b3 := hasDerivAt_clm_comp (A := m) a3
    have b4 := hasDerivAt_clm_comp (A := m) a4
    have c1 := a1.inner ℂ b3
    have c2 := a2.inner ℂ b4
    refine (c1.sub c2).congr_deriv ?_
    simp only [hF', map_neg, inner_neg_left, inner_neg_right]
    ring
  have hbound : ∀ r ∈ Icc 0 s, ‖F' r‖ ≤ (8 * ρ + (2 * K + 2 * ρ) * s) * Real.exp (4 * ρ * s) * A * B := fun r hr => by
    set σ := s - r with hσ
    have hσ0 : 0 ≤ σ := by linarith [hr.2]
    have hσs : σ ≤ s := by linarith [hr.1]
    set p : negLapH.domain := ⟨(chiC R r).J g, (chiC R r).J_mem g⟩ with hp
    set q : negLapH.domain := ⟨(chiD R σ).J y, (chiD R σ).J_mem y⟩ with hq
    have e1 : negLapH q = (chiD R σ).JS y := Cutoff.negLapH_J _ y
    have e2 : negLapH p = (chiC R r).JS g := Cutoff.negLapH_J _ g
    have eF : F' r = ⟪negLapH q, m (p : L2H')⟫_ℂ - ⟪(q : L2H'), m (negLapH p)⟫_ℂ := by
      rw [e1, e2]
    rw [eF, comm_form hW p q]
    have ex : domX q = (chiD R σ).Bx y := (Bx_eq_domX y).symm
    have ey : domY q = (chiD R σ).By y := (By_eq_domY y).symm
    have hE : Real.exp (2 * ρ * s) * Real.exp (2 * ρ * s) = Real.exp (4 * ρ * s) := by
      rw [← Real.exp_add]; congr 1; ring
    set E := Real.exp (2 * ρ * s) with hEdef
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    have npb : ‖mulCL hW.sb (p : L2H')‖ ≤ E * B :=
      (wave_C hW.toWaveW R g hr.1).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith [hr.2])) hB0)
    have nx : ‖mulCL hW.sb (domX q)‖ ≤ E * A := by
      rw [ex]
      exact (wave_Bx hW.toWaveW R y hσ0).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith)) hA0)
    have ny : ‖mulCL hW.sb (domY q)‖ ≤ E * A := by
      rw [ey]
      exact (wave_By hW.toWaveW R y hσ0).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith)) hA0)
    have nq : ‖mulCL hW.sb (q : L2H')‖ ≤ s * (E * A) := by
      refine (wave_D hW.toWaveW R y hσ0).trans ?_
      refine mul_le_mul hσs (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith)) hA0) (by positivity) (hr.1.trans hr.2)
    have heX : ∀ w : ℂ, 0 < w.im → vfR 1 (fun u => W u ^ 2) w = (vfR 1 (fun u => W u ^ 2) w / W w) * W w := fun w hw => by
      have := hW.pos w hw
      field_simp
    have heY : ∀ w : ℂ, 0 < w.im → vfR Complex.I (fun u => W u ^ 2) w = (vfR Complex.I (fun u => W u ^ 2) w / W w) * W w := fun w hw => by
      have := hW.pos w hw
      field_simp
    have heXX : ∀ w : ℂ, 0 < w.im → vfR 1 (vfR 1 fun u => W u ^ 2) w = (vfR 1 (vfR 1 fun u => W u ^ 2) w / W w) * W w := fun w hw => by
      have := hW.pos w hw
      field_simp
    have heYY : ∀ w : ℂ, 0 < w.im → vfR Complex.I (vfR Complex.I fun u => W u ^ 2) w
        = (vfR Complex.I (vfR Complex.I fun u => W u ^ 2) w / W w) * W w := fun w hw => by
      have := hW.pos w hw
      field_simp
    have t1 := cross_bound' hW.toWaveW hW.mX hW.adm.sbX heX hW.bX (domX q) (p : L2H')
    have t2 := cross_bound' hW.toWaveW hW.mXX hW.admX.sbX heXX hW.bXX (q : L2H') (p : L2H')
    have t3 := cross_bound' hW.toWaveW hW.mY hW.adm.sbY heY hW.bY (domY q) (p : L2H')
    have t4 := cross_bound' hW.toWaveW hW.mYY hW.admY.sbY heYY hW.bYY (q : L2H') (p : L2H')
    have t5 := cross_bound' hW.toWaveW hW.mY hW.adm.sbY heY hW.bY (q : L2H') (p : L2H')
    set a := ‖mulCL hW.sb (p : L2H')‖ with ha
    set b := ‖mulCL hW.sb (domX q)‖ with hb
    set c := ‖mulCL hW.sb (domY q)‖ with hc
    set d := ‖mulCL hW.sb (q : L2H')‖ with hd
    have ha0 : 0 ≤ a := norm_nonneg _
    have hb0 : 0 ≤ b := norm_nonneg _
    have hc0 : 0 ≤ c := norm_nonneg _
    have hd0 : 0 ≤ d := norm_nonneg _
    have hs0 : 0 ≤ s := hs
    have p1 : b * a ≤ (E * A) * (E * B) := mul_le_mul nx npb ha0 (by positivity)
    have p2 : c * a ≤ (E * A) * (E * B) := mul_le_mul ny npb ha0 (by positivity)
    have p3 : d * a ≤ (s * (E * A)) * (E * B) := mul_le_mul nq npb ha0 (by positivity)
    have tri := norm_sub_le (2 * ⟪mulCL hW.adm.sbX (domX q), (p : L2H')⟫_ℂ + ⟪mulCL hW.admX.sbX (q : L2H'), (p : L2H')⟫_ℂ
        + 2 * ⟪mulCL hW.adm.sbY (domY q), (p : L2H')⟫_ℂ + ⟪mulCL hW.admY.sbY (q : L2H'), (p : L2H')⟫_ℂ) ⟪mulCL hW.adm.sbY (q : L2H'), (p : L2H')⟫_ℂ
    have tri2 := norm_add_le (2 * ⟪mulCL hW.adm.sbX (domX q), (p : L2H')⟫_ℂ + ⟪mulCL hW.admX.sbX (q : L2H'), (p : L2H')⟫_ℂ
        + 2 * ⟪mulCL hW.adm.sbY (domY q), (p : L2H')⟫_ℂ) ⟪mulCL hW.admY.sbY (q : L2H'), (p : L2H')⟫_ℂ
    have tri3 := norm_add_le (2 * ⟪mulCL hW.adm.sbX (domX q), (p : L2H')⟫_ℂ + ⟪mulCL hW.admX.sbX (q : L2H'), (p : L2H')⟫_ℂ)
        (2 * ⟪mulCL hW.adm.sbY (domY q), (p : L2H')⟫_ℂ)
    have tri4 := norm_add_le (2 * ⟪mulCL hW.adm.sbX (domX q), (p : L2H')⟫_ℂ) ⟪mulCL hW.admX.sbX (q : L2H'), (p : L2H')⟫_ℂ
    have n2 : ∀ z : ℂ, ‖2 * z‖ = 2 * ‖z‖ := fun z => by simp
    rw [n2] at tri3 tri4
    have e4 : (8 * ρ + (2 * K + 2 * ρ) * s) * Real.exp (4 * ρ * s) * A * B
        = 8 * ρ * ((E * A) * (E * B)) + (2 * K + 2 * ρ) * ((s * (E * A)) * (E * B)) := by
      rw [← hE]; ring
    rw [e4]
    have l1 : 2 * (2 * ρ * b * a) ≤ 2 * (2 * ρ * ((E * A) * (E * B))) := by
      have := mul_le_mul_of_nonneg_left p1 hρ
      linarith
    have l2 : 2 * (2 * ρ * c * a) ≤ 2 * (2 * ρ * ((E * A) * (E * B))) := by
      have := mul_le_mul_of_nonneg_left p2 hρ
      linarith
    have l3 : K * d * a ≤ K * ((s * (E * A)) * (E * B)) := by
      have := mul_le_mul_of_nonneg_left p3 hK
      linarith
    have l4 : 2 * ρ * d * a ≤ 2 * ρ * ((s * (E * A)) * (E * B)) := by
      have := mul_le_mul_of_nonneg_left p3 hρ
      linarith
    linarith
  have h := (convex_Icc (0 : ℝ) s).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r _ => (hF_d r).hasDerivWithinAt) hbound (left_mem_Icc.2 hs) (right_mem_Icc.2 hs)
  have e0 : F 0 = ⟪(chiC R s).J y, m ((chiC R 0).J g)⟫_ℂ := by
    simp only [hF, sub_zero, chiD_zero_JS, ContinuousLinearMap.zero_apply, map_zero, inner_zero_right]
  have es : F s = ⟪(chiC R 0).J y, m ((chiC R s).J g)⟫_ℂ := by
    simp only [hF, sub_self, chiD_zero_J, ContinuousLinearMap.zero_apply, inner_zero_left, sub_zero]
  rw [e0, es, sub_zero, Real.norm_eq_abs, abs_of_nonneg hs] at h
  calc _ ≤ _ := h
    _ = _ := by ring

end comm

end Qschubert
