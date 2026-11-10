import Qschubert.KLFCX
import Qschubert.KLSpectral
import Qschubert.MollGen

/-!
# Truncated exponential weights (for `prop:a0`)

For `L ≥ 0`, `ℓ_L(s) = min(√|s|, L)`. `Mop L τ = e^{τ min(Λ, L)}` and `ellOp L = min(Λ, L)` are bounded spectral multipliers,
so the energy argument of `prop:a0` runs on bounded operators; the weight is removed by monotone convergence at the end.

* `Mop_mul`, `Mop_zero`, `inner_Mop_left`, `Mop_comm_of`: the group law, self-adjointness and commutation;
* `hasDerivAt_Mop`: `d/dτ Mop L τ = ellOp L * Mop L τ` in operator norm;
* `klU_Mop`, `klU_spec`: the KL form of the multipliers.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- `ℓ_L(s) = min(√|s|, L)`. -/
noncomputable def ellS (L s : ℝ) : ℝ := min (√|s|) L

lemma continuous_ellS (L : ℝ) : Continuous (ellS L) := by unfold ellS; fun_prop

lemma ellS_nonneg {L : ℝ} (hL : 0 ≤ L) (s : ℝ) : 0 ≤ ellS L s := le_min (Real.sqrt_nonneg _) hL

lemma ellS_le (L s : ℝ) : ellS L s ≤ L := min_le_right _ _

lemma ellS_le_sqrt (L s : ℝ) : ellS L s ≤ √|s| := min_le_left _ _

/-- `min(Λ(ν), L)`. -/
noncomputable def ellN (L ν : ℝ) : ℝ := min (LamK ν) L

lemma ellS_mKL (L ν : ℝ) : ellS L (ν ^ 2 + 1 / 4) = ellN L ν := by
  rw [ellS, ellN, abs_of_pos (by positivity : (0 : ℝ) < ν ^ 2 + 1 / 4)]; rfl

lemma continuous_ellN (L : ℝ) : Continuous (ellN L) := by
  unfold ellN; exact continuous_LamK.min continuous_const

lemma abs_ellN_sub_le (L ν ν' : ℝ) : |ellN L ν - ellN L ν'| ≤ |ν - ν'| :=
  (abs_min_sub_min_le_max _ _ _ _).trans (by simp [abs_LamK_sub_le])

/-- The symbol of `e^{τ min(Λ, L)}`. -/
noncomputable def phiM (L τ : ℝ) : ℝ → ℂ := fun s => ((Real.exp (τ * ellS L s) : ℝ) : ℂ)

/-- The symbol of `min(Λ, L)`. -/
noncomputable def phiL (L : ℝ) : ℝ → ℂ := fun s => ((ellS L s : ℝ) : ℂ)

lemma continuous_phiM (L τ : ℝ) : Continuous (phiM L τ) :=
  Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul (continuous_ellS L)))

lemma continuous_phiL (L : ℝ) : Continuous (phiL L) := Complex.continuous_ofReal.comp (continuous_ellS L)

lemma norm_phiM_le {L : ℝ} (hL : 0 ≤ L) (τ s : ℝ) : ‖phiM L τ s‖ ≤ Real.exp (|τ| * L) := by
  rw [phiM, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.2 ?_
  calc τ * ellS L s ≤ |τ| * ellS L s := mul_le_mul_of_nonneg_right (le_abs_self τ) (ellS_nonneg hL s)
    _ ≤ |τ| * L := mul_le_mul_of_nonneg_left (ellS_le L s) (abs_nonneg τ)

lemma phiM_mem {L : ℝ} (hL : 0 ≤ L) (τ : ℝ) : phiM L τ ∈ BddMeasurable ℝ :=
  ⟨(continuous_phiM L τ).measurable, _, norm_phiM_le hL τ⟩

lemma phiL_mem {L : ℝ} (hL : 0 ≤ L) : phiL L ∈ BddMeasurable ℝ :=
  ⟨(continuous_phiL L).measurable, L, fun s => by
    rw [phiL, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ellS_nonneg hL s)]; exact ellS_le L s⟩

/-- `e^{τ min(Λ, L)}`. -/
noncomputable def Mop (L τ : ℝ) : L2H' →L[ℂ] L2H' := specE.integral (phiM L τ)

/-- `min(Λ, L)`. -/
noncomputable def ellOp (L : ℝ) : L2H' →L[ℂ] L2H' := specE.integral (phiL L)

variable {L : ℝ} (hL : 0 ≤ L)
include hL

theorem Mop_mul (a b : ℝ) : Mop L a * Mop L b = Mop L (a + b) := by
  rw [Mop, Mop, Mop, ← specE.integral_mul (phiM_mem hL a) (phiM_mem hL b)]
  congr 1
  funext s
  simp only [phiM, Pi.mul_apply, ← Complex.ofReal_mul, ← Real.exp_add, add_mul]

theorem Mop_apply_apply (a b : ℝ) (x : L2H') : Mop L a (Mop L b x) = Mop L (a + b) x := by
  rw [← Mop_mul hL]; rfl

omit hL in
theorem Mop_zero : Mop L 0 = 1 := by
  have : phiM L 0 = 1 := by funext s; simp [phiM]
  rw [Mop, this, specE.integral_one]

theorem adjoint_Mop (a : ℝ) : ContinuousLinearMap.adjoint (Mop L a) = Mop L a := by
  have h := specE.integral_conj (phiM_mem hL a)
  have e : (fun x => (starRingEnd ℂ) (phiM L a x)) = phiM L a := by
    funext s; simp only [phiM, Complex.conj_ofReal]
  rw [e] at h
  exact h.symm

theorem inner_Mop_left (a : ℝ) (x y : L2H') : ⟪Mop L a x, y⟫_ℂ = ⟪x, Mop L a y⟫_ℂ := by
  conv_rhs => rw [← adjoint_Mop hL a]
  rw [ContinuousLinearMap.adjoint_inner_right]

theorem adjoint_ellOp : ContinuousLinearMap.adjoint (ellOp L) = ellOp L := by
  have h := specE.integral_conj (phiL_mem hL)
  have e : (fun x => (starRingEnd ℂ) (phiL L x)) = phiL L := by
    funext s; simp only [phiL, Complex.conj_ofReal]
  rw [e] at h
  exact h.symm

/-- Bounded spectral multipliers commute with `Mop`. -/
theorem Mop_comm {g : ℝ → ℂ} (hg : g ∈ BddMeasurable ℝ) (a : ℝ) :
    Mop L a * specE.integral g = specE.integral g * Mop L a := by
  rw [Mop, ← specE.integral_mul (phiM_mem hL a) hg, ← specE.integral_mul hg (phiM_mem hL a), mul_comm]

theorem ellOp_comm_Mop (a : ℝ) : ellOp L * Mop L a = Mop L a * ellOp L := (Mop_comm hL (phiL_mem hL) a).symm

/-- **`d/dτ e^{τ min(Λ, L)} = min(Λ, L) e^{τ min(Λ, L)}`, in operator norm.** -/
theorem hasDerivAt_Mop (τ : ℝ) : HasDerivAt (Mop L) (ellOp L * Mop L τ) τ := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  set K : ℝ := Real.exp (|τ| * L) * L ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun h : ℝ => h ^ 2) ?_ ?_
  · refine Asymptotics.IsBigO.of_bound K ?_
    have hsmall : ∀ᶠ h : ℝ in 𝓝 0, |h| * L ≤ 1 := by
      have hc : Continuous fun h : ℝ => |h| * L := by fun_prop
      have : Tendsto (fun h : ℝ => |h| * L) (𝓝 0) (𝓝 0) := by simpa using hc.tendsto 0
      exact (this.eventually (gt_mem_nhds zero_lt_one)).mono fun h hh => hh.le
    filter_upwards [hsmall] with h hh
    set ψ : ℝ → ℂ := fun s => ((Real.exp (τ * ellS L s) * (Real.exp (h * ellS L s) - 1 - h * ellS L s) : ℝ) : ℂ) with hψ
    have hψe : ψ = phiM L (τ + h) + (-1 : ℂ) • phiM L τ + (-(h : ℂ)) • (phiL L * phiM L τ) := by
      funext s
      simp only [hψ, phiM, phiL, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, add_mul, Real.exp_add]
      push_cast
      ring
    have hmul := bdd_mul (phiL_mem hL) (phiM_mem hL τ)
    have hs1 := (BddMeasurable ℝ).smul_mem (-1 : ℂ) (phiM_mem hL τ)
    have hs2 := (BddMeasurable ℝ).smul_mem (-(h : ℂ)) hmul
    have hψm : ψ ∈ BddMeasurable ℝ := by
      rw [hψe]; exact (BddMeasurable ℝ).add_mem ((BddMeasurable ℝ).add_mem (phiM_mem hL _) hs1) hs2
    have hop : Mop L (τ + h) - Mop L τ - h • (ellOp L * Mop L τ) = specE.integral ψ := by
      rw [hψe, specE.integral_add ((BddMeasurable ℝ).add_mem (phiM_mem hL _) hs1) hs2,
        specE.integral_add (phiM_mem hL _) hs1, specE.integral_smul _ (phiM_mem hL τ),
        specE.integral_smul _ hmul, specE.integral_mul (phiL_mem hL) (phiM_mem hL τ), Mop, Mop, ellOp]
      ext1 x
      have e := RCLike.real_smul_eq_coe_smul (K := ℂ) h ((specE.integral (phiL L) * specE.integral (phiM L τ)) x)
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
      rw [e]
      module
    have hpt : ∀ s, ‖ψ s‖ ≤ K * h ^ 2 := fun s => by
      have hℓ0 := ellS_nonneg hL s
      have hℓL := ellS_le L s
      have hx : |h * ellS L s| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg hℓ0]
        exact (mul_le_mul_of_nonneg_left hℓL (abs_nonneg h)).trans hh
      have hb := Real.abs_exp_sub_one_sub_id_le hx
      have hE : Real.exp (τ * ellS L s) ≤ Real.exp (|τ| * L) := by
        refine Real.exp_le_exp.2 ?_
        calc τ * ellS L s ≤ |τ| * ellS L s := mul_le_mul_of_nonneg_right (le_abs_self τ) hℓ0
          _ ≤ |τ| * L := mul_le_mul_of_nonneg_left hℓL (abs_nonneg τ)
      have hsq : (h * ellS L s) ^ 2 ≤ h ^ 2 * L ^ 2 := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hℓ0 hℓL 2) (sq_nonneg h)
      rw [hψ, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (τ * ellS L s) * |Real.exp (h * ellS L s) - 1 - h * ellS L s|
          ≤ Real.exp (|τ| * L) * (h ^ 2 * L ^ 2) := mul_le_mul hE (hb.trans hsq) (abs_nonneg _) (Real.exp_pos _).le
        _ = K * h ^ 2 := by rw [hK]; ring
    have hn := specE.norm_integral_le hψm
    have hsup : ⨆ s, ‖ψ s‖ ≤ K * h ^ 2 := ciSup_le hpt
    rw [show Mop L (τ + h) - Mop L τ - h • (ellOp L * Mop L τ) = specE.integral ψ from hop]
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg h)] using hn.trans hsup
  · exact Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (n := 2) (by norm_num)

/-- The KL form of a compactly supported perturbation of a constant. -/
theorem klU_Mop (τ : ℝ) (v : L2H') :
    ((klU (Mop L τ v) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) =ᵐ[muU]
      fun p => ((Real.exp (τ * ellN L p.2) : ℝ) : ℂ) * (klU v : ℝ × ℝ → ℂ) p := by
  set c : ℂ := ((Real.exp (τ * L) : ℝ) : ℂ) with hc
  set g : ℝ → ℂ := fun s => phiM L τ s - c with hg
  have hgc : Continuous g := (continuous_phiM L τ).sub continuous_const
  have hg0 : Tendsto g (cocompact ℝ) (𝓝 0) := by
    refine HasCompactSupport.is_zero_at_infty ?_
    refine HasCompactSupport.intro (isCompact_Icc (a := -(L ^ 2 + 1)) (b := L ^ 2 + 1)) fun s hs => ?_
    have hbig : L ^ 2 ≤ |s| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hs
      rcases hs with h | h
      · rw [abs_of_neg (by nlinarith [sq_nonneg L])]; linarith
      · rw [abs_of_pos (by nlinarith [sq_nonneg L])]; linarith
    have hs2 : L ≤ √|s| := by
      rw [← Real.sqrt_sq hL]; exact Real.sqrt_le_sqrt hbig
    simp only [hg, phiM, hc, ellS, min_eq_right hs2, sub_self]
  have hgm : g ∈ BddMeasurable ℝ :=
    ⟨hgc.measurable, Real.exp (|τ| * L) + ‖c‖, fun s =>
      (norm_sub_le _ _).trans (add_le_add (norm_phiM_le hL τ s) le_rfl)⟩
  have h1m : (1 : ℝ → ℂ) ∈ BddMeasurable ℝ := ⟨measurable_one, 1, fun _ => by simp⟩
  have hsplit : phiM L τ = c • (1 : ℝ → ℂ) + g := by
    funext s; simp [hg]
  have hop : Mop L τ v = c • v + specE.integral g v := by
    rw [Mop, hsplit, specE.integral_add ((BddMeasurable ℝ).smul_mem c h1m) hgm, specE.integral_smul _ h1m,
      specE.integral_one]
    simp
  have hk := klU_functionalCalculus hgc hg0 v
  rw [hop, map_add, map_smul]
  filter_upwards [Lp.coeFn_add (c • klU v) (klU (specE.integral g v)), Lp.coeFn_smul c (klU v), hk] with p a1 a2 a3
  rw [a1, Pi.add_apply, a2, Pi.smul_apply]
  have a3' : ((klU (specE.integral g v) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) p = g (p.2 ^ 2 + 1 / 4) * (klU v : ℝ × ℝ → ℂ) p := a3
  rw [a3', smul_eq_mul]
  simp only [hg, phiM, ellS_mKL]
  ring

omit hL in
/-- The KL form of a multiplier vanishing at infinity. -/
theorem klU_spec {φ : ℝ → ℂ} (hc : Continuous φ) (h0 : Tendsto φ (cocompact ℝ) (𝓝 0)) (v : L2H') :
    ((klU (specE.integral φ v) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) =ᵐ[muU] fun p => φ (mKL p) * (klU v : ℝ × ℝ → ℂ) p :=
  klU_functionalCalculus hc h0 v

end Qschubert
