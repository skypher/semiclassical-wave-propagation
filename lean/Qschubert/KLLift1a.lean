import Qschubert.SobolevC
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Smoothness from all iterated Laplacians in `L²(ℂ)`

If `f₀, f₁, … ∈ L²(ℂ)` and `Δ f_n = f_{n+1}` as tempered distributions, then `f₀` has a `C^∞` representative (`smooth_rep_of_iter`):
`|ξ|^{2n} 𝓕f₀ = (2π)^{-2n} |𝓕f_n|`, so every moment of `𝓕f₀` is integrable, and the Fourier inversion integral can be differentiated.
-/

namespace Qschubert

open MeasureTheory FourierTransform TemperedDistribution SchwartzMap Filter
open scoped Laplacian Real ContDiff

local notation "L2C" => Lp ℂ 2 (volume : Measure ℂ)

/-- `𝓕f` equals the `L¹` function `sobV f h` a.e. -/
lemma fourier_ae_sobV (f h : L2C) (hΔ : Δ (f : 𝓢'(ℂ, ℂ)) = (h : 𝓢'(ℂ, ℂ))) :
    ⇑(𝓕 f : L2C) =ᵐ[volume] ⇑(sobV f h) := by
  have e1 := fourier_eq_sobV f h hΔ
  rw [Lp.fourier_toTemperedDistribution_eq] at e1
  have hl1 : LocallyIntegrable (⇑(𝓕 f : L2C)) (volume : Measure ℂ) := (Lp.memLp _).locallyIntegrable (by norm_num)
  have hl2 : LocallyIntegrable (⇑(sobV f h)) (volume : Measure ℂ) := (integrable_sobV f h).locallyIntegrable
  have key : ∀ (g : ℂ → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, g x • (⇑(𝓕 f : L2C) - ⇑(sobV f h)) x = 0 := by
    intro g hg hgc
    set u : 𝓢(ℂ, ℂ) := HasCompactSupport.toSchwartzMap (f := fun x => ((g x : ℝ) : ℂ))
      (hgc.comp_left Complex.ofReal_zero) (Complex.ofRealCLM.contDiff.comp hg)
    have hu : ∀ x, u x = ((g x : ℝ) : ℂ) := fun x => rfl
    have h1 : (((𝓕 f : L2C)) : 𝓢'(ℂ, ℂ)) u = ∫ x, u x • (𝓕 f : L2C) x := Lp.toTemperedDistribution_apply _ u
    have h3 : ((sobV f h : Lp ℂ 1 (volume : Measure ℂ)) : 𝓢'(ℂ, ℂ)) u = ∫ x, u x • (sobV f h) x := Lp.toTemperedDistribution_apply _ u
    have hi1 : Integrable fun x => u x • (𝓕 f : L2C) x :=
      hl1.integrable_smul_left_of_hasCompactSupport u.continuous (hgc.comp_left Complex.ofReal_zero)
    have hi2 : Integrable fun x => u x • (sobV f h) x :=
      hl2.integrable_smul_left_of_hasCompactSupport u.continuous (hgc.comp_left Complex.ofReal_zero)
    have hsub : ∫ x, u x • (⇑(𝓕 f : L2C) - ⇑(sobV f h)) x = 0 := by
      simp_rw [Pi.sub_apply, smul_sub]
      rw [integral_sub hi1 hi2, ← h1, ← h3, e1, sub_self]
    rw [← hsub]
    congr 1
  have := ae_eq_zero_of_integral_contDiff_smul_eq_zero (hl1.sub hl2) key
  filter_upwards [this] with x hx
  exact sub_eq_zero.1 hx

/-- `|ξ|² 𝓕f = -(2π)^{-2} 𝓕h` a.e., when `Δf = h`. -/
lemma sq_fourier_ae (f h : L2C) (hΔ : Δ (f : 𝓢'(ℂ, ℂ)) = (h : 𝓢'(ℂ, ℂ))) :
    ∀ᵐ ξ ∂(volume : Measure ℂ), sqNorm ξ * (𝓕 f : L2C) ξ = -(twoPiSq⁻¹ * (𝓕 h : L2C) ξ) := by
  have h1 := fourier_ae_sobV f h hΔ
  have h2 : ⇑(sobV f h) =ᵐ[volume] fun ξ => (memLp_weightW.toLp weightW : L2C) ξ * (sobG f h) ξ := by
    have := Lp.coeFn_lpSMul (𝕜 := ℂ) (memLp_weightW.toLp weightW : L2C) (sobG f h) (r := 1)
    filter_upwards [this] with ξ hξ
    rw [sobV, hξ]
    rfl
  have h3 := memLp_weightW.coeFn_toLp
  have h4 : ⇑(sobG f h) =ᵐ[volume] fun ξ => (𝓕 f : L2C) ξ - twoPiSq⁻¹ * (𝓕 h : L2C) ξ := by
    have a1 := Lp.coeFn_sub (𝓕 f : L2C) (twoPiSq⁻¹ • (𝓕 h : L2C))
    have a2 := Lp.coeFn_smul twoPiSq⁻¹ (𝓕 h : L2C)
    filter_upwards [a1, a2] with ξ e1 e2
    rw [sobG, e1, Pi.sub_apply, e2]
    rfl
  filter_upwards [h1, h2, h3, h4] with ξ e1 e2 e3 e4
  rw [e2, e3, e4] at e1
  have hw := weightW_mul_one_add ξ
  have e5 : (1 + sqNorm ξ) * (𝓕 f : L2C) ξ = (𝓕 f : L2C) ξ - twoPiSq⁻¹ * (𝓕 h : L2C) ξ := by
    calc (1 + sqNorm ξ) * (𝓕 f : L2C) ξ
        = (1 + sqNorm ξ) * (weightW ξ * ((𝓕 f : L2C) ξ - twoPiSq⁻¹ * (𝓕 h : L2C) ξ)) := by rw [← e1]
      _ = (weightW ξ * (1 + sqNorm ξ)) * ((𝓕 f : L2C) ξ - twoPiSq⁻¹ * (𝓕 h : L2C) ξ) := by ring
      _ = _ := by rw [hw, one_mul]
  linear_combination e5

section iter

variable (f : ℕ → L2C) (hΔ : ∀ n, Δ (f n : 𝓢'(ℂ, ℂ)) = (f (n + 1) : 𝓢'(ℂ, ℂ)))
include hΔ

lemma moment_ae (n : ℕ) : ∀ᵐ ξ ∂(volume : Measure ℂ), ‖ξ‖ ^ (2 * n) * ‖(𝓕 (f 0) : L2C) ξ‖ = ‖twoPiSq⁻¹‖ ^ n * ‖(𝓕 (f n) : L2C) ξ‖ := by
  induction n with
  | zero => exact Eventually.of_forall fun ξ => by simp
  | succ n ih =>
    filter_upwards [ih, sq_fourier_ae (f n) (f (n + 1)) (hΔ n)] with ξ h1 h2
    have h3 := congrArg norm h2
    rw [norm_mul, norm_neg, norm_mul] at h3
    have hs : ‖sqNorm ξ‖ = ‖ξ‖ ^ 2 := by
      simp only [sqNorm, Complex.norm_real, norm_pow, norm_norm]
    rw [hs] at h3
    calc ‖ξ‖ ^ (2 * (n + 1)) * ‖(𝓕 (f 0) : L2C) ξ‖
        = ‖ξ‖ ^ 2 * (‖ξ‖ ^ (2 * n) * ‖(𝓕 (f 0) : L2C) ξ‖) := by ring
      _ = ‖twoPiSq⁻¹‖ ^ n * (‖ξ‖ ^ 2 * ‖(𝓕 (f n) : L2C) ξ‖) := by rw [h1]; ring
      _ = ‖twoPiSq⁻¹‖ ^ (n + 1) * ‖(𝓕 (f (n + 1)) : L2C) ξ‖ := by rw [h3]; ring

lemma memLp_even (n : ℕ) : MemLp (fun ξ => ‖ξ‖ ^ (2 * n) * ‖(𝓕 (f 0) : L2C) ξ‖) 2 (volume : Measure ℂ) := by
  have h1 : MemLp (fun ξ => ‖twoPiSq⁻¹‖ ^ n * ‖(𝓕 (f n) : L2C) ξ‖) 2 (volume : Measure ℂ) :=
    (Lp.memLp _).norm.const_mul _
  refine h1.ae_eq ?_
  filter_upwards [moment_ae f hΔ n] with ξ h
  exact h.symm

lemma memLp_moment (k : ℕ) : MemLp (fun ξ => ‖ξ‖ ^ k * ‖(𝓕 (f 0) : L2C) ξ‖) 2 (volume : Measure ℂ) := by
  have h0 : MemLp (fun ξ => ‖(𝓕 (f 0) : L2C) ξ‖) 2 (volume : Measure ℂ) := (Lp.memLp _).norm
  have hk := memLp_even f hΔ k
  refine MemLp.mono (h0.add hk) ?_ (Eventually.of_forall fun ξ => ?_)
  · exact ((continuous_norm.pow k).aestronglyMeasurable).mul (Lp.aestronglyMeasurable _).norm
  · have ha := norm_nonneg ((𝓕 (f 0) : L2C) ξ)
    have hb : ‖ξ‖ ^ k ≤ 1 + ‖ξ‖ ^ (2 * k) := by
      rcases le_total ‖ξ‖ 1 with h | h
      · have := pow_le_one₀ (n := k) (norm_nonneg ξ) h
        have := pow_nonneg (norm_nonneg ξ) (2 * k)
        linarith
      · have := pow_le_pow_right₀ h (show k ≤ 2 * k by omega)
        linarith
    simp only [Pi.add_apply]
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) ha), Real.norm_of_nonneg (by positivity)]
    nlinarith

lemma integrable_moment (n : ℕ) : Integrable (fun ξ => ‖ξ‖ ^ n * ‖(𝓕 (f 0) : L2C) ξ‖) (volume : Measure ℂ) := by
  have h1 : MemLp (fun ξ => ‖weightW ξ‖) 2 (volume : Measure ℂ) := memLp_weightW.norm
  have h2 := (memLp_moment f hΔ n).add (memLp_moment f hΔ (n + 2))
  have h3 := h1.integrable_mul h2
  refine h3.congr (Eventually.of_forall fun ξ => ?_)
  have hw := weightW_mul_one_add ξ
  have hn : ‖weightW ξ‖ * (1 + ‖ξ‖ ^ 2) = 1 := by
    have e := congrArg norm hw
    rw [norm_mul, norm_one] at e
    have e2 : ‖1 + sqNorm ξ‖ = 1 + ‖ξ‖ ^ 2 := by
      simp only [sqNorm]
      rw [show (1 : ℂ) + ((‖ξ‖ ^ 2 : ℝ) : ℂ) = ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    rwa [e2] at e
  show ‖weightW ξ‖ * ((‖ξ‖ ^ n * ‖(𝓕 (f 0) : L2C) ξ‖) + (‖ξ‖ ^ (n + 2) * ‖(𝓕 (f 0) : L2C) ξ‖)) = _
  rw [show ‖ξ‖ ^ n * ‖(𝓕 (f 0) : L2C) ξ‖ + ‖ξ‖ ^ (n + 2) * ‖(𝓕 (f 0) : L2C) ξ‖
      = (1 + ‖ξ‖ ^ 2) * (‖ξ‖ ^ n * ‖(𝓕 (f 0) : L2C) ξ‖) by ring, ← mul_assoc, hn, one_mul]

/-- **`C^∞` representative.** -/
theorem smooth_rep_of_iter : ∃ s : ℂ → ℂ, ContDiff ℝ ∞ s ∧ ⇑(f 0) =ᵐ[volume] s := by
  refine ⟨sobRep (f 0) (f 1), ?_, (sobolevC (f 0) (f 1) (hΔ 0)).2.1⟩
  have hv : ∀ n : ℕ, (n : ℕ∞) ≤ ⊤ → Integrable (fun ξ => ‖ξ‖ ^ n * ‖(sobV (f 0) (f 1) : Lp ℂ 1 (volume : Measure ℂ)) ξ‖) (volume : Measure ℂ) := fun n _ => by
    refine (integrable_moment f hΔ n).congr ?_
    filter_upwards [fourier_ae_sobV (f 0) (f 1) (hΔ 0)] with ξ h
    rw [h]
  have hc : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (𝓕 (⇑(sobV (f 0) (f 1)))) := Real.contDiff_fourier hv
  have e : sobRep (f 0) (f 1) = fun x => 𝓕 (⇑(sobV (f 0) (f 1))) (-x) := by
    funext x
    rw [sobRep, Real.fourierInv_eq_fourier_neg]
  rw [e]
  exact hc.comp contDiff_neg

end iter

end Qschubert
