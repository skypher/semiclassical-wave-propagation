import Qschubert.KLWave2

/-!
# The commutator of the wave group with a weight, with the bound of the manuscript

Lemma 3.15 of the manuscript: for a bounded weight `W` with `h = W²`,
`|⟪u, [cos(sΛ), h] g⟫| ≤ (8ρs + (K + ρ)s²) e^{2ρs} ‖W u‖ ‖W g‖` on spectrally truncated vectors (`comm_wave_sharp`).
The proof is that of `comm_wave`, with the two energy factors kept at their own times `s - r` and `r` (their product
is `e^{2ρs}`), the factor `s - r` of the integrated term kept, and the integral over `r ∈ [0, s]` taken exactly by
the fencing theorem `image_norm_le_of_norm_deriv_right_le_deriv_boundary`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

section comm

variable {W : ℂ → ℝ} {C ρ K : ℝ} (hW : WaveW2 W C ρ K)
include hW

set_option maxHeartbeats 2000000 in
/-- **Lemma 3.15: the commutator of the truncated wave group with `h`**, with the bound of the manuscript. -/
theorem comm_wave_sharp (R : ℝ) {s : ℝ} (hs : 0 ≤ s) (y g : L2H') :
    ‖⟪(chiC R 0).J y, mulCL hW.adm.sb ((chiC R s).J g)⟫_ℂ - ⟪(chiC R s).J y, mulCL hW.adm.sb ((chiC R 0).J g)⟫_ℂ‖
      ≤ (8 * ρ * s + (K + ρ) * s ^ 2) * Real.exp (2 * ρ * s)
          * ‖mulCL hW.sb ((chiC R 0).J y)‖ * ‖mulCL hW.sb ((chiC R 0).J g)‖ := by
  have hρ : 0 ≤ ρ := hW.ρ0
  have hK : 0 ≤ K := hW.K0
  set m := mulCL hW.adm.sb with hm
  set A := ‖mulCL hW.sb ((chiC R 0).J y)‖ with hA
  set B := ‖mulCL hW.sb ((chiC R 0).J g)‖ with hB
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 ≤ B := norm_nonneg _
  set E := Real.exp (2 * ρ * s) with hEdef
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
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
  -- The integrand at the time `r`, with the factor `s - r` kept.
  have hbound : ∀ r ∈ Ico 0 s, ‖F' r‖ ≤ (8 * ρ + (2 * K + 2 * ρ) * (s - r)) * E * A * B := fun r hr => by
    set σ := s - r with hσ
    have hσ0 : 0 ≤ σ := by linarith [hr.2]
    set p : negLapH.domain := ⟨(chiC R r).J g, (chiC R r).J_mem g⟩ with hp
    set q : negLapH.domain := ⟨(chiD R σ).J y, (chiD R σ).J_mem y⟩ with hq
    have e1 : negLapH q = (chiD R σ).JS y := Cutoff.negLapH_J _ y
    have e2 : negLapH p = (chiC R r).JS g := Cutoff.negLapH_J _ g
    have eF : F' r = ⟪negLapH q, m (p : L2H')⟫_ℂ - ⟪(q : L2H'), m (negLapH p)⟫_ℂ := by
      rw [e1, e2]
    rw [eF, comm_form hW p q]
    have ex : domX q = (chiD R σ).Bx y := (Bx_eq_domX y).symm
    have ey : domY q = (chiD R σ).By y := (By_eq_domY y).symm
    set E1 := Real.exp (2 * ρ * σ) with hE1
    set E2 := Real.exp (2 * ρ * r) with hE2
    have hE12 : E1 * E2 = E := by
      rw [hE1, hE2, hEdef, ← Real.exp_add]; congr 1; ring
    have hE10 : 0 ≤ E1 := (Real.exp_pos _).le
    have hE20 : 0 ≤ E2 := (Real.exp_pos _).le
    have npb : ‖mulCL hW.sb (p : L2H')‖ ≤ E2 * B := wave_C hW.toWaveW R g hr.1
    have nx : ‖mulCL hW.sb (domX q)‖ ≤ E1 * A := by
      rw [ex]; exact wave_Bx hW.toWaveW R y hσ0
    have ny : ‖mulCL hW.sb (domY q)‖ ≤ E1 * A := by
      rw [ey]; exact wave_By hW.toWaveW R y hσ0
    have nq : ‖mulCL hW.sb (q : L2H')‖ ≤ σ * (E1 * A) := wave_D hW.toWaveW R y hσ0
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
    have p1 : b * a ≤ (E1 * A) * (E2 * B) := mul_le_mul nx npb ha0 (by positivity)
    have p2 : c * a ≤ (E1 * A) * (E2 * B) := mul_le_mul ny npb ha0 (by positivity)
    have p3 : d * a ≤ (σ * (E1 * A)) * (E2 * B) := mul_le_mul nq npb ha0 (by positivity)
    have tri := norm_sub_le (2 * ⟪mulCL hW.adm.sbX (domX q), (p : L2H')⟫_ℂ + ⟪mulCL hW.admX.sbX (q : L2H'), (p : L2H')⟫_ℂ
        + 2 * ⟪mulCL hW.adm.sbY (domY q), (p : L2H')⟫_ℂ + ⟪mulCL hW.admY.sbY (q : L2H'), (p : L2H')⟫_ℂ) ⟪mulCL hW.adm.sbY (q : L2H'), (p : L2H')⟫_ℂ
    have tri2 := norm_add_le (2 * ⟪mulCL hW.adm.sbX (domX q), (p : L2H')⟫_ℂ + ⟪mulCL hW.admX.sbX (q : L2H'), (p : L2H')⟫_ℂ
        + 2 * ⟪mulCL hW.adm.sbY (domY q), (p : L2H')⟫_ℂ) ⟪mulCL hW.admY.sbY (q : L2H'), (p : L2H')⟫_ℂ
    have tri3 := norm_add_le (2 * ⟪mulCL hW.adm.sbX (domX q), (p : L2H')⟫_ℂ + ⟪mulCL hW.admX.sbX (q : L2H'), (p : L2H')⟫_ℂ)
        (2 * ⟪mulCL hW.adm.sbY (domY q), (p : L2H')⟫_ℂ)
    have tri4 := norm_add_le (2 * ⟪mulCL hW.adm.sbX (domX q), (p : L2H')⟫_ℂ) ⟪mulCL hW.admX.sbX (q : L2H'), (p : L2H')⟫_ℂ
    have n2 : ∀ z : ℂ, ‖2 * z‖ = 2 * ‖z‖ := fun z => by simp
    rw [n2] at tri3 tri4
    have e4 : (8 * ρ + (2 * K + 2 * ρ) * σ) * E * A * B
        = 8 * ρ * ((E1 * A) * (E2 * B)) + (2 * K + 2 * ρ) * ((σ * (E1 * A)) * (E2 * B)) := by
      rw [← hE12]; ring
    rw [e4]
    have l1 : 2 * (2 * ρ * b * a) ≤ 2 * (2 * ρ * ((E1 * A) * (E2 * B))) := by
      have := mul_le_mul_of_nonneg_left p1 hρ
      linarith
    have l2 : 2 * (2 * ρ * c * a) ≤ 2 * (2 * ρ * ((E1 * A) * (E2 * B))) := by
      have := mul_le_mul_of_nonneg_left p2 hρ
      linarith
    have l3 : K * d * a ≤ K * ((σ * (E1 * A)) * (E2 * B)) := by
      have := mul_le_mul_of_nonneg_left p3 hK
      linarith
    have l4 : 2 * ρ * d * a ≤ 2 * ρ * ((σ * (E1 * A)) * (E2 * B)) := by
      have := mul_le_mul_of_nonneg_left p3 hρ
      linarith
    linarith
  -- Integrate the bound exactly: the boundary function has derivative the right side of `hbound`.
  set G : ℝ → ℝ := fun r => (8 * ρ * r + (2 * K + 2 * ρ) * (s * r - r ^ 2 / 2)) * E * A * B with hG
  have hG_d : ∀ r, HasDerivAt G ((8 * ρ + (2 * K + 2 * ρ) * (s - r)) * E * A * B) r := fun r => by
    have h1 : HasDerivAt (fun r : ℝ => 8 * ρ * r + (2 * K + 2 * ρ) * (s * r - r ^ 2 / 2))
        (8 * ρ * 1 + (2 * K + 2 * ρ) * (s * 1 - (2 * r ^ 1 * 1) / 2)) r := by
      have hx : HasDerivAt (fun r : ℝ => r) 1 r := hasDerivAt_id' r
      exact ((hx.const_mul (8 * ρ)).add (((hx.const_mul s).sub ((hx.pow 2).div_const 2)).const_mul (2 * K + 2 * ρ)))
    have h2 := ((h1.mul_const E).mul_const A).mul_const B
    convert h2 using 1
    ring
  have hfc : ContinuousOn (fun r => F r - F 0) (Icc 0 s) :=
    (continuous_iff_continuousAt.2 fun r => (hF_d r).continuousAt).continuousOn.sub continuousOn_const
  have hfd : ∀ r ∈ Ico 0 s, HasDerivWithinAt (fun r => F r - F 0) (F' r) (Ici r) r := fun r _ =>
    ((hF_d r).sub_const (F 0)).hasDerivWithinAt
  have h0 : ‖F 0 - F 0‖ ≤ G 0 := by simp [hG]
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary hfc hfd h0 hG_d hbound (right_mem_Icc.2 hs)
  have e0 : F 0 = ⟪(chiC R s).J y, m ((chiC R 0).J g)⟫_ℂ := by
    simp only [hF, sub_zero, chiD_zero_JS, zero_apply, map_zero, inner_zero_right]
  have es : F s = ⟪(chiC R 0).J y, m ((chiC R s).J g)⟫_ℂ := by
    simp only [hF, sub_self, chiD_zero_J, zero_apply, inner_zero_left, sub_zero]
  rw [e0, es] at h
  calc _ ≤ _ := h
    _ = _ := by simp only [hG]; ring

end comm

end Qschubert
