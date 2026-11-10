import Qschubert.KLA0d
import Qschubert.KLDD
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Multiplication by the decay weight preserves analyticity, at a reduced radius

The proof of Theorem 1.4R uses `‖e^{α₀'Λ} a‖ ≤ C ‖e^{αΛ} X₀^β a‖` for one radius `α₀'` proportional to `α`. The paper obtains
`α₀' = 3α/4` from the Gutzmer identity (`lem:m`). A fixed fraction of `α` is enough for the consumer, and it follows from the word
bounds of Lemma SC alone: `(-Δ)^n` is a word polynomial with `3^n` terms of length at most `2n`, so
`‖(-Δ)^n a‖ ≤ C 3^n (2n+1)! (M/α)^{2n} ‖e^{αΛ}F‖`, and `e^{bΛ} ≤ 2 cosh(bΛ)` is summed term by term.

`lem_m_weak`: `‖e^{c₀ α Λ} X₀^{-β}F‖ ≤ (32/5) B ‖e^{αΛ}F‖`, with `c₀ = 1/(4M)` depending only on `τ₀` and `C₁`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set
open scoped ENNReal Nat

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

lemma powWP_delta_inv (n : ℕ) :
    (∀ t ∈ powWP (deltaP 0) n, ‖t.1‖ ≤ 1 ∧ t.2.length ≤ 2 * n) ∧ (powWP (deltaP 0) n).length = 3 ^ n := by
  induction n with
  | zero =>
    refine ⟨fun t ht => ?_, rfl⟩
    simp only [powWP, oneP, List.mem_singleton] at ht
    subst ht
    simp
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨fun t ht => ?_, ?_⟩
    · obtain ⟨p, hp, q, hq, rfl⟩ := mem_mulP ht
      obtain ⟨a1, a2⟩ := deltaP_inv le_rfl p hp
      obtain ⟨b1, b2⟩ := h1 q hq
      refine ⟨?_, ?_⟩
      · rw [norm_mul]
        exact mul_le_one₀ a1 (norm_nonneg _) b1
      · simp only [List.length_append]
        omega
    · show (mulP (deltaP 0) (powWP (deltaP 0) n)).length = _
      rw [length_mulP, h2]
      show 3 * 3 ^ n = 3 ^ (n + 1)
      ring

lemma norm_polyAct_le {a : L2H'} {K : ℝ} (hK : 0 ≤ K) (P : WP) (h : ∀ t ∈ P, ‖t.1‖ ≤ 1 ∧ ‖wordAct t.2 a‖ ≤ K) :
    ‖polyAct P a‖ ≤ P.length * K := by
  induction P with
  | nil => simp [polyAct]
  | cons t P ih =>
    rw [polyAct_cons, List.length_cons]
    obtain ⟨h1, h2⟩ := h t (by simp)
    have h3 := ih fun q hq => h q (by simp [hq])
    calc ‖t.1 • wordAct t.2 a + polyAct P a‖ ≤ ‖t.1‖ * ‖wordAct t.2 a‖ + ‖polyAct P a‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_smul]
      _ ≤ 1 * K + P.length * K := add_le_add (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) h3
      _ = _ := by push_cast; ring

section

variable {a : L2H'} (hA : AllWords a)
include hA

/-- `(-Δ)^n a` in the KL picture, through the word polynomial. -/
lemma klU_pow (n : ℕ) :
    ((klU (polyAct (powWP (deltaP 0) n) a) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) =ᵐ[muU]
      fun p => ((-(mKL p)) ^ n : ℂ) * (klU a : ℝ × ℝ → ℂ) p := by
  induction n with
  | zero =>
    have e : polyAct (powWP (deltaP 0) 0) a = a := polyAct_oneP a
    rw [e]
    exact Eventually.of_forall fun p => by simp
  | succ n ih =>
    rw [polyAct_powWP_succ hA]
    have h0 := negLapH_eq_poly hA (powWP (deltaP 0) n)
    have e : polyAct (deltaP 0) (polyAct (powWP (deltaP 0) n) a)
        = -negLapH ⟨polyAct (powWP (deltaP 0) n) a, mem_polyAct hA _⟩ := by rw [h0, neg_neg]
    rw [e, map_neg]
    filter_upwards [Lp.coeFn_neg (klU (negLapH ⟨polyAct (powWP (deltaP 0) n) a, mem_polyAct hA _⟩)),
      klU_negLapH ⟨polyAct (powWP (deltaP 0) n) a, mem_polyAct hA _⟩, ih] with p e1 e2 e3
    rw [e1, Pi.neg_apply, e2]
    show -(_ * ((klU (polyAct (powWP (deltaP 0) n) a) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) p) = _
    rw [e3, pow_succ]
    simp only [mKL]
    push_cast
    ring

end

/-- **The weight preserves analyticity at a reduced radius.** -/
theorem lem_m_weak {τ₀ C₁ β B α : ℝ} (hF' : FCBound τ₀ C₁) (hC : 0 ≤ C₁) (hβ : 0 ≤ β) (hB : FdbB β B) (hα : 0 < α)
    (hα1 : α ≤ 1) (hle : α ≤ τ₀) {F : L2H'} (hFd : F ∈ (expLambda α).domain) :
    let M := max (max (Real.exp 1 * C₁) (τ₀ / rhoFdb)) 1
    ∃ hd : mulW hβ hB [] F ∈ (expLambda (α / (4 * M))).domain,
      ‖expLambda (α / (4 * M)) ⟨_, hd⟩‖ ≤ 32 / 5 * B * ‖expLambda α ⟨F, hFd⟩‖ := by
  intro M
  set a := mulW hβ hB [] F with ha
  have hA : AllWords a := fun S => (lem_sc hF' hC hβ hB S hα hle hFd).1
  have hM1 : 1 ≤ M := le_max_right _ _
  have hM0 : 0 < M := by linarith
  have hB0 : 0 ≤ B := by
    have h := wbd_nonneg hB ([] : List Bool)
    simpa [wbd] using h
  set N := ‖expLambda α ⟨F, hFd⟩‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  have hMα : 1 ≤ M / α := by rw [le_div_iff₀ hα]; nlinarith
  have hw : ∀ S : List Bool, ‖wordAct S a‖ ≤ B * (S.length + 1) * S.length.factorial * (M / α) ^ S.length * N := fun S => by
    obtain ⟨-, G, hG, hGn⟩ := lem_sc hF' hC hβ hB S hα hle hFd
    have h1 : ‖wordAct S a‖ ≤ ‖G‖ := by
      refine Lp.norm_le_norm_of_ae_le ?_
      filter_upwards [hG] with z hz
      rw [hz, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hh1 : hF (z : ℂ) ≤ 1 := hF_le_one z.im_pos
      have hh0 : 0 < hF (z : ℂ) := by unfold hF; exact div_pos (by have := z.im_pos; show 0 < 2 * (z : ℂ).im; simpa using this) (normN_pos _)
      have hr : 1 ≤ hF (z : ℂ) ^ (-β) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hh0 hh1 (by linarith)
      rw [abs_of_pos (by linarith)]
      exact le_mul_of_one_le_left (norm_nonneg _) hr
    refine h1.trans (hGn.trans ?_)
    gcongr
    exact le_max_left _ _
  set b := α / (4 * M) with hb
  have hb0 : 0 < b := by positivity
  set y : ℕ → L2H' := fun n => polyAct (powWP (deltaP 0) n) a with hy
  set c : ℕ → ℝ := fun n => b ^ (2 * n) / (2 * n)! with hc
  have hc0 : ∀ n, 0 ≤ c n := fun n => by simp only [hc]; positivity
  have hyn : ∀ n, c n * ‖y n‖ ≤ 2 * B * N * (3 / 8) ^ n := fun n => by
    obtain ⟨h1, h2⟩ := powWP_delta_inv n
    set K : ℝ := B * (2 * n + 1) * (2 * n)! * (M / α) ^ (2 * n) * N with hK
    have hK0 : 0 ≤ K := by positivity
    have hb1 := norm_polyAct_le (a := a) hK0 (powWP (deltaP 0) n) fun t ht => by
      obtain ⟨t1, t2⟩ := h1 t ht
      refine ⟨t1, (hw t.2).trans ?_⟩
      have hl : (t.2.length : ℝ) ≤ 2 * n := by exact_mod_cast t2
      have hf : (t.2.length ! : ℝ) ≤ (2 * n)! := by exact_mod_cast Nat.factorial_le t2
      have hp : (M / α) ^ t.2.length ≤ (M / α) ^ (2 * n) := pow_le_pow_right₀ hMα t2
      rw [hK]
      gcongr
    rw [h2] at hb1
    push_cast at hb1
    have hbM : b * (M / α) = 1 / 4 := by rw [hb]; field_simp
    have hfac : ((2 * n)! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
    have h2n : (2 * (n : ℝ) + 1) ≤ 2 * 2 ^ n := by
      have : (n : ℝ) + 1 ≤ 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
      nlinarith
    calc c n * ‖y n‖ ≤ c n * (3 ^ n * K) := mul_le_mul_of_nonneg_left hb1 (hc0 n)
      _ = B * N * (2 * (n : ℝ) + 1) * (3 * (b * (M / α)) ^ 2) ^ n := by
          simp only [hc, hK, mul_pow, pow_mul]
          field_simp
      _ = B * N * (2 * (n : ℝ) + 1) * (3 / 16) ^ n := by rw [hbM]; norm_num
      _ ≤ B * N * (2 * 2 ^ n) * (3 / 16) ^ n := by gcongr
      _ = 2 * B * N * (3 / 8) ^ n := by
          rw [show (3 / 8 : ℝ) = 2 * (3 / 16) by norm_num, mul_pow]; ring
  set S : ℝ := 16 / 5 * B * N with hS
  have hS0 : 0 ≤ S := by positivity
  set z : ℕ → L2H' := fun m => ∑ n ∈ Finset.range m, (c n : ℂ) • ((-1 : ℂ) ^ n • y n) with hz
  have hzn : ∀ m, ‖z m‖ ≤ S := fun m => by
    have hgeo : ∑ n ∈ Finset.range m, (3 / 8 : ℝ) ^ n ≤ 8 / 5 := by
      have h := sum_le_hasSum (Finset.range m) (fun n _ => by positivity)
        (hasSum_geometric_of_lt_one (r := (3 / 8 : ℝ)) (by norm_num) (by norm_num))
      norm_num at h ⊢
      linarith
    have hterm : ∀ n, ‖(c n : ℂ) • ((-1 : ℂ) ^ n • y n)‖ ≤ 2 * B * N * (3 / 8) ^ n := fun n => by
      rw [norm_smul, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hc0 n)]
      exact hyn n
    calc ‖z m‖ ≤ ∑ n ∈ Finset.range m, ‖(c n : ℂ) • ((-1 : ℂ) ^ n • y n)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range m, 2 * B * N * (3 / 8) ^ n := Finset.sum_le_sum fun n _ => hterm n
      _ = 2 * B * N * ∑ n ∈ Finset.range m, (3 / 8 : ℝ) ^ n := by rw [Finset.mul_sum]
      _ ≤ 2 * B * N * (8 / 5) := mul_le_mul_of_nonneg_left hgeo (by positivity)
      _ = S := by rw [hS]; ring
  set H : ℕ → ℝ × ℝ → ℝ := fun m p => ∑ n ∈ Finset.range m, c n * mKL p ^ n with hH
  have hH0 : ∀ m p, 0 ≤ H m p := fun m p =>
    Finset.sum_nonneg fun n _ => mul_nonneg (hc0 n) (pow_nonneg (by unfold mKL; positivity) n)
  have hkz : ∀ m, ((klU (z m) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) =ᵐ[muU] fun p => ((H m p : ℝ) : ℂ) * (klU a : ℝ × ℝ → ℂ) p := fun m => by
    induction m with
    | zero =>
      have e : z 0 = 0 := by simp [hz]
      rw [e, map_zero]
      filter_upwards [Lp.coeFn_zero ℂ 2 muU] with p hp
      rw [hp]; simp [hH]
    | succ m ih =>
      have e : z (m + 1) = z m + (c m : ℂ) • ((-1 : ℂ) ^ m • y m) := by
        simp only [hz, Finset.sum_range_succ]
      rw [e, map_add, map_smul, map_smul]
      filter_upwards [Lp.coeFn_add (klU (z m)) ((c m : ℂ) • ((-1 : ℂ) ^ m • klU (y m))), ih,
        Lp.coeFn_smul (c m : ℂ) ((-1 : ℂ) ^ m • klU (y m)), Lp.coeFn_smul ((-1 : ℂ) ^ m) (klU (y m)),
        klU_pow hA m] with p e1 e2 e3 e4 e5
      rw [e1, Pi.add_apply, e2, e3, Pi.smul_apply, e4, Pi.smul_apply]
      have e5' : ((klU (y m) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) p = ((-(mKL p)) ^ m : ℂ) * (klU a : ℝ × ℝ → ℂ) p := e5
      rw [e5']
      simp only [hH, Finset.sum_range_succ, smul_eq_mul]
      push_cast
      have hsgn : (-1 : ℂ) ^ m * (-(mKL p : ℂ)) ^ m = (mKL p : ℂ) ^ m := by
        rw [← mul_pow]; simp
      linear_combination ((c m : ℂ) * (klU a : ℝ × ℝ → ℂ) p) * hsgn
  have hâ : Measurable fun p : ℝ × ℝ => ‖(klU a : ℝ × ℝ → ℂ) p‖ₑ ^ 2 := measurable_enorm_sq_klU a
  set F2 : ℕ → ℝ × ℝ → ℝ≥0∞ := fun m p => ENNReal.ofReal (H m p) ^ 2 * ‖(klU a : ℝ × ℝ → ℂ) p‖ₑ ^ 2 with hF2
  have hHm : ∀ m, Measurable (H m) := fun m =>
    Finset.measurable_sum _ fun n _ => (measurable_mKL.pow_const n).const_mul _
  have hF2m : ∀ m, Measurable (F2 m) := fun m => ((ENNReal.measurable_ofReal.comp (hHm m)).pow_const 2).mul hâ
  have hF2b : ∀ m, ∫⁻ p, F2 m p ∂muU ≤ ENNReal.ofReal (S ^ 2) := fun m => by
    have e : ∫⁻ p, F2 m p ∂muU = ENNReal.ofReal (‖z m‖ ^ 2) := by
      rw [← lintegral_klU_sq]
      refine lintegral_congr_ae ?_
      filter_upwards [hkz m] with p hp
      rw [hp, enorm_mul, mul_pow, ← ofReal_norm_eq_enorm ((H m p : ℝ) : ℂ), Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hH0 m p)]
    rw [e]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hzn m) 2)
  have hlim : ∀ p : ℝ × ℝ, Tendsto (fun m => F2 m p) atTop
      (𝓝 (ENNReal.ofReal (Real.cosh (b * LamK p.2)) ^ 2 * ‖(klU a : ℝ × ℝ → ℂ) p‖ₑ ^ 2)) := fun p => by
    have hs := (Real.hasSum_cosh (b * LamK p.2)).tendsto_sum_nat
    have heq : ∀ m, ∑ n ∈ Finset.range m, (b * LamK p.2) ^ (2 * n) / ((2 * n)! : ℝ) = H m p := fun m => by
      refine Finset.sum_congr rfl fun n _ => ?_
      have hsq : LamK p.2 ^ 2 = mKL p := Real.sq_sqrt (by positivity)
      simp only [hc]
      rw [mul_pow, pow_mul (LamK p.2), hsq]
      ring
    simp_rw [heq] at hs
    have h0 : Tendsto (fun m => ENNReal.ofReal (H m p)) atTop (𝓝 (ENNReal.ofReal (Real.cosh (b * LamK p.2)))) :=
      ENNReal.tendsto_ofReal hs
    have h1 : Tendsto (fun m => ENNReal.ofReal (H m p) ^ 2) atTop (𝓝 (ENNReal.ofReal (Real.cosh (b * LamK p.2)) ^ 2)) :=
      ENNReal.Tendsto.pow h0
    exact ENNReal.Tendsto.mul_const h1 (Or.inr (ENNReal.pow_ne_top enorm_ne_top))
  have hfat : ∫⁻ p, ENNReal.ofReal (Real.cosh (b * LamK p.2)) ^ 2 * ‖(klU a : ℝ × ℝ → ℂ) p‖ₑ ^ 2 ∂muU
      ≤ ENNReal.ofReal (S ^ 2) := by
    have e : ∫⁻ p, liminf (fun m => F2 m p) atTop ∂muU ≤ liminf (fun m => ∫⁻ p, F2 m p ∂muU) atTop :=
      lintegral_liminf_le hF2m
    have e2 : (fun p => liminf (fun m => F2 m p) atTop)
        = fun p => ENNReal.ofReal (Real.cosh (b * LamK p.2)) ^ 2 * ‖(klU a : ℝ × ℝ → ℂ) p‖ₑ ^ 2 := by
      funext p; exact (hlim p).liminf_eq
    rw [e2] at e
    exact e.trans (liminf_le_of_frequently_le' (Eventually.of_forall hF2b).frequently)
  have hexp : ∫⁻ p, ENNReal.ofReal (Real.exp (b * LamK p.2)) ^ 2 * ‖(klU a : ℝ × ℝ → ℂ) p‖ₑ ^ 2 ∂muU
      ≤ ENNReal.ofReal ((2 * S) ^ 2) := by
    have e4 : ENNReal.ofReal ((2 * S) ^ 2) = 4 * ENNReal.ofReal (S ^ 2) := by
      rw [show (2 * S) ^ 2 = 4 * S ^ 2 by ring, ENNReal.ofReal_mul (by norm_num)]; norm_num
    rw [e4]
    refine le_trans ?_ (mul_le_mul' le_rfl hfat)
    rw [← lintegral_const_mul' _ _ (by norm_num)]
    refine lintegral_mono fun p => ?_
    rw [← mul_assoc]
    refine mul_le_mul' ?_ le_rfl
    set x := b * LamK p.2
    have hcp := Real.cosh_pos x
    have h2 : Real.exp x ≤ 2 * Real.cosh x := by rw [Real.cosh_eq]; linarith [Real.exp_pos (-x)]
    calc ENNReal.ofReal (Real.exp x) ^ 2 ≤ ENNReal.ofReal (2 * Real.cosh x) ^ 2 :=
          pow_le_pow_left₀ zero_le (ENNReal.ofReal_le_ofReal h2) 2
      _ = 4 * ENNReal.ofReal (Real.cosh x) ^ 2 := by
          rw [ENNReal.ofReal_mul (by norm_num), mul_pow]; norm_num
  have hmeasg : StronglyMeasurable fun p : ℝ × ℝ => fExp b (mKL p) * (klU a : ℝ × ℝ → ℂ) p :=
    ((measurable_fExp b).comp measurable_mKL).stronglyMeasurable.mul (Lp.stronglyMeasurable _)
  have hint : ∫⁻ p, ‖fExp b (mKL p) * (klU a : ℝ × ℝ → ℂ) p‖ₑ ^ 2 ∂muU ≤ ENNReal.ofReal ((2 * S) ^ 2) := by
    refine le_trans (le_of_eq ?_) hexp
    refine lintegral_congr fun p => ?_
    rw [fExp_mKL, enorm_mul, mul_pow, enorm_ofReal_exp]
  have hmem : MemLp (fun p => fExp b (mKL p) * (klU a : ℝ × ℝ → ℂ) p) 2 muU :=
    memLp_of_lintegral_sq_lt_top hmeasg.aestronglyMeasurable (lt_of_le_of_lt hint ENNReal.ofReal_lt_top)
  have hd : a ∈ (expLambda b).domain := (mem_domain_fc_iff (measurable_fExp b) a).2 hmem
  refine ⟨hd, ?_⟩
  have hsq := sq_expLambda hd
  have hle : ENNReal.ofReal (‖expLambda b ⟨a, hd⟩‖ ^ 2) ≤ ENNReal.ofReal ((2 * S) ^ 2) := by rw [hsq]; exact hexp
  have h2S : 0 ≤ 2 * S := by positivity
  have hfin := (pow_le_pow_iff_left₀ (norm_nonneg _) h2S two_ne_zero).1 ((ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hle)
  refine hfin.trans (le_of_eq ?_)
  rw [hS]; ring

end Qschubert
