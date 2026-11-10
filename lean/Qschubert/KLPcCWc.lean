import Qschubert.KLPcCWa
import Qschubert.KLPcCWb

/-!
# The critical-weight multiplier theorem, part 3: assembly

`cw_abstract`: if `g` has the tail `TailB g B` and `m(x) = ∫ g(r) cos(r √(x - 1/4)) dr` on `[1/4, ∞)`, then for every weight comparable on the shells to
`e^{n/2} (1 + n)^c` with `1/2 < c < 1`, `∫ ω² |m(-Δ) f|² ≤ (K B)² ∫ ω² |f|²`, with `K` depending only on `c` and the comparison constant.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate UpperHalfPlane

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

lemma chiN_eq (n : ℕ) (z : UpperHalfPlane) : chiN n z = if ⌊psiF (z : ℂ)⌋₊ = n then 1 else 0 := by
  unfold chiN
  by_cases h : ⌊psiF (z : ℂ)⌋₊ = n
  · have hm : z ∈ shell n := h
    rw [Set.indicator_of_mem hm, if_pos h]
    rfl
  · have hm : z ∉ shell n := h
    rw [Set.indicator_of_notMem hm, if_neg h]

lemma sum_cutN_ae (f : L2H') (N : ℕ) : (((∑ n ∈ Finset.range N, cutN n f : L2H')) : UpperHalfPlane → ℂ) =ᵐ[volume]
    fun z => ((if ⌊psiF (z : ℂ)⌋₊ < N then 1 else 0 : ℝ) : ℂ) * f z := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure UpperHalfPlane)] with z hz
    rw [hz]
    simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    filter_upwards [ih, cutN_ae N f, Lp.coeFn_add (∑ n ∈ Finset.range N, cutN n f) (cutN N f)] with z h1 h2 h3
    rw [h3, Pi.add_apply, h1, h2, chiN_eq]
    set m := ⌊psiF (z : ℂ)⌋₊
    rcases lt_trichotomy m N with h | h | h
    · have a1 : m < N + 1 := by omega
      have a2 : m ≠ N := by omega
      simp [h, a1, a2]
    · have a1 : ¬ m < N := by omega
      have a3 : m < N + 1 := by omega
      simp [h]
    · have a1 : ¬ m < N := by omega
      have a2 : m ≠ N := by omega
      have a3 : ¬ m < N + 1 := by omega
      simp [a1, a2, a3]

lemma tendsto_sum_cutN (f : L2H') : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, cutN n f) atTop (𝓝 f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set F : ℕ → L2H' := fun N => ∑ n ∈ Finset.range N, cutN n f with hF
  have hall : ∀ᵐ z : UpperHalfPlane, ∀ N : ℕ, ((F N - f : L2H') z = ((if ⌊psiF (z : ℂ)⌋₊ < N then 1 else 0 : ℝ) : ℂ) * f z - f z) := by
    rw [ae_all_iff]
    intro N
    filter_upwards [sum_cutN_ae f N, Lp.coeFn_sub (F N) f] with z h1 h2
    rw [h2, Pi.sub_apply, h1]
  have hsq : Tendsto (fun N : ℕ => ‖F N - f‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [norm_sq_int]
    have := tendsto_integral_of_dominated_convergence (μ := (volume : Measure UpperHalfPlane)) (fun z => ‖f z‖ ^ 2)
      (F := fun (N : ℕ) z => ‖(F N - f : L2H') z‖ ^ 2) (f := fun _ => 0)
      (fun N => ((Lp.aestronglyMeasurable _).norm.pow 2)) (integrable_norm_sq f)
      (fun N => by
        filter_upwards [hall] with z hz
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hz N]
        by_cases h : ⌊psiF (z : ℂ)⌋₊ < N
        · simp only [h, if_true]
          simp
        · simp [h])
      (by
        filter_upwards [hall] with z hz
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_gt_atTop ⌊psiF (z : ℂ)⌋₊] with N hN
        rw [hz N]
        simp [hN])
    simpa using this
  have hs := hsq.sqrt
  simp only [Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] at hs
  exact hs

lemma shell_disjoint : Pairwise (Function.onFun Disjoint shell) := fun a b hab =>
  Set.disjoint_left.2 fun z (h1 : ⌊psiF (z : ℂ)⌋₊ = a) (h2 : ⌊psiF (z : ℂ)⌋₊ = b) => hab (h1.symm.trans h2)

lemma ofReal_norm_int (a : ℝ) (v : L2H') :
    ENNReal.ofReal (a ^ 2 * ‖v‖ ^ 2) = ∫⁻ z, ENNReal.ofReal (a ^ 2 * ‖v z‖ ^ 2) := by
  rw [norm_sq_int, ← integral_const_mul,
    ofReal_integral_eq_lintegral_ofReal ((integrable_norm_sq v).const_mul _) (Eventually.of_forall fun z => by positivity)]

lemma shell_lower {om : UpperHalfPlane → ℝ} {a : ℝ} (ha : 0 ≤ a) {n : ℕ} (hlo : ∀ z ∈ shell n, a ≤ om z) (f : L2H') :
    ENNReal.ofReal (a ^ 2 * ‖cutN n f‖ ^ 2) ≤ ∫⁻ z in shell n, ENNReal.ofReal (om z ^ 2 * ‖f z‖ ^ 2) := by
  rw [ofReal_norm_int, ← lintegral_indicator (measurableSet_shell n)]
  refine lintegral_mono_ae ?_
  filter_upwards [cutN_ae n f] with z hz
  rw [hz]
  by_cases hm : z ∈ shell n
  · rw [Set.indicator_of_mem hm]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : chiN n z = 1 := by simp [chiN, hm]
    rw [h1, Complex.ofReal_one, one_mul]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha (hlo z hm) 2) (by positivity)
  · have h1 : chiN n z = 0 := by simp [chiN, hm]
    rw [h1]
    simp

lemma shell_upper {om : UpperHalfPlane → ℝ} {b : ℝ} (hom : ∀ z, 0 ≤ om z) {l : ℕ} (hhi : ∀ z ∈ shell l, om z ≤ b) (v : L2H') :
    ∫⁻ z in shell l, ENNReal.ofReal (om z ^ 2 * ‖v z‖ ^ 2) ≤ ENNReal.ofReal (b ^ 2 * ‖cutN l v‖ ^ 2) := by
  rw [ofReal_norm_int, ← lintegral_indicator (measurableSet_shell l)]
  refine lintegral_mono_ae ?_
  filter_upwards [cutN_ae l v] with z hz
  rw [hz]
  by_cases hm : z ∈ shell l
  · rw [Set.indicator_of_mem hm]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : chiN l z = 1 := by simp [chiN, hm]
    rw [h1, Complex.ofReal_one, one_mul]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hom z) (hhi z hm) 2) (by positivity)
  · rw [Set.indicator_of_notMem hm]
    exact zero_le

lemma abs_sub_eq_kd (l n : ℕ) : |(l : ℝ) - n| = (kd l n : ℝ) := by
  unfold kd
  rcases le_total n l with h | h
  · have e : n - l = 0 := by omega
    rw [e, add_zero, Nat.cast_sub h, abs_of_nonneg]
    have : (n : ℝ) ≤ l := by exact_mod_cast h
    linarith
  · have e : l - n = 0 := by omega
    rw [e, zero_add, Nat.cast_sub h, abs_of_nonpos]
    · ring
    · have : (l : ℝ) ≤ n := by exact_mod_cast h
      linarith

lemma weight_kernel {c D : ℝ} (hD : 0 < D) (l n : ℕ) :
    D * Real.exp ((l : ℝ) / 2) * (1 + (l : ℝ)) ^ c * tF (Tgap l n)
      ≤ (D * Real.exp (1 / 2) * (2 : ℝ) ^ (3 / 2 : ℝ)) * Kt c l n * (Real.exp ((n : ℝ) / 2) * (1 + (n : ℝ)) ^ c) := by
  set T := Tgap l n with hT
  have hT0 : 0 ≤ T := Tgap_nonneg l n
  have hk0 : (0 : ℝ) ≤ kd l n := Nat.cast_nonneg _
  have hT1 : (kd l n : ℝ) - 1 ≤ T := by
    rw [hT, Tgap, abs_sub_eq_kd]
    exact le_max_left _ _
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hln : (l : ℝ) - n ≤ kd l n := by linarith [cast_kd_ge l n]
  set A := 1 + T with hA
  have hA0 : 0 < A := by linarith
  set w := 1 + (kd l n : ℝ) with hw
  have hw0 : 0 < w := by linarith
  have hwA : w ≤ 2 * A := by rw [hw, hA]; linarith
  have e1 : A * √A = A ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    nth_rewrite 1 [← Real.rpow_one A]
    rw [← Real.rpow_add hA0]
    norm_num
  have h1 : (A ^ (3 / 2 : ℝ))⁻¹ ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * w ^ (-(3 / 2) : ℝ) := by
    have h2 : w ^ (3 / 2 : ℝ) ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) := by
      rw [← Real.mul_rpow (by norm_num) hA0.le]
      exact Real.rpow_le_rpow hw0.le hwA (by norm_num)
    have hwp : 0 < w ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hw0 _
    have hAp : 0 < A ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hA0 _
    rw [Real.rpow_neg hw0.le, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hAp hwp]
    linarith
  have hexp : Real.exp ((l : ℝ) / 2) * Real.exp (-T / 2) ≤ Real.exp (1 / 2) * Real.exp ((n : ℝ) / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hK : Kt c l n * (1 + (n : ℝ)) ^ c = (1 + (l : ℝ)) ^ c * w ^ (-(3 / 2) : ℝ) := by
    unfold Kt
    rw [Real.div_rpow (by linarith) (by linarith)]
    have : (1 + (n : ℝ)) ^ c ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
    field_simp
    rfl
  have hl1 : 0 < (1 + (l : ℝ)) ^ c := Real.rpow_pos_of_pos (by linarith) _
  have hEl := Real.exp_pos ((l : ℝ) / 2)
  have hET := Real.exp_pos (-T / 2)
  have hE1 := Real.exp_pos (1 / 2 : ℝ)
  have hEn := Real.exp_pos ((n : ℝ) / 2)
  have h2p : (0 : ℝ) < 2 ^ (3 / 2 : ℝ) := by positivity
  have hwp : 0 < w ^ (-(3 / 2) : ℝ) := Real.rpow_pos_of_pos hw0 _
  have hAi : 0 < (A ^ (3 / 2 : ℝ))⁻¹ := inv_pos.2 (Real.rpow_pos_of_pos hA0 _)
  have etF : tF T = Real.exp (-T / 2) * (A ^ (3 / 2 : ℝ))⁻¹ := by
    unfold tF
    rw [← hA, e1, div_eq_mul_inv]
  have main : (Real.exp ((l : ℝ) / 2) * Real.exp (-T / 2)) * (A ^ (3 / 2 : ℝ))⁻¹
      ≤ (Real.exp (1 / 2) * Real.exp ((n : ℝ) / 2)) * ((2 : ℝ) ^ (3 / 2 : ℝ) * w ^ (-(3 / 2) : ℝ)) :=
    mul_le_mul hexp h1 hAi.le (by positivity)
  have e2 : (D * Real.exp (1 / 2) * (2 : ℝ) ^ (3 / 2 : ℝ)) * Kt c l n * (Real.exp ((n : ℝ) / 2) * (1 + (n : ℝ)) ^ c)
      = (D * (1 + (l : ℝ)) ^ c) * ((Real.exp (1 / 2) * Real.exp ((n : ℝ) / 2)) * ((2 : ℝ) ^ (3 / 2 : ℝ) * w ^ (-(3 / 2) : ℝ))) := by
    calc _ = (D * Real.exp (1 / 2) * (2 : ℝ) ^ (3 / 2 : ℝ)) * Real.exp ((n : ℝ) / 2) * (Kt c l n * (1 + (n : ℝ)) ^ c) := by ring
      _ = _ := by rw [hK]; ring
  have e3 : D * Real.exp ((l : ℝ) / 2) * (1 + (l : ℝ)) ^ c * tF T
      = (D * (1 + (l : ℝ)) ^ c) * ((Real.exp ((l : ℝ) / 2) * Real.exp (-T / 2)) * (A ^ (3 / 2 : ℝ))⁻¹) := by
    rw [etF]
    ring
  rw [e2, e3]
  exact mul_le_mul_of_nonneg_left main (by positivity)

/-- **The weighted multiplier theorem (`os:cw`).** -/
theorem cw_abstract {c D : ℝ} (hc1 : 1 / 2 < c) (hc2 : c < 1) (hD : 0 < D) :
    ∃ K : ℝ, 0 < K ∧ ∀ (om : UpperHalfPlane → ℝ), (∀ z, 0 ≤ om z) →
      (∀ (n : ℕ) (z : UpperHalfPlane), z ∈ shell n → Real.exp ((n : ℝ) / 2) * (1 + (n : ℝ)) ^ c ≤ om z) →
      (∀ (l : ℕ) (z : UpperHalfPlane), z ∈ shell l → om z ≤ D * Real.exp ((l : ℝ) / 2) * (1 + (l : ℝ)) ^ c) →
      ∀ {g : ℝ → ℝ} {G : ℝ → ℂ} {Bg : ℝ}, 0 < Bg → Integrable g → TailB g Bg → G ∈ BddMeasurable ℝ →
      (∀ x, 1 / 4 ≤ x → ∫ r, (g r : ℂ) * ((Real.cos (r * √(yD x)) : ℝ) : ℂ) = G x) →
      ∀ f : L2H', ∫⁻ z, ENNReal.ofReal (om z ^ 2 * ‖specE.integral G f z‖ ^ 2)
        ≤ ENNReal.ofReal ((K * Bg) ^ 2) * ∫⁻ z, ENNReal.ofReal (om z ^ 2 * ‖f z‖ ^ 2) := by
  set s := min (3 / 2 : ℝ) (min (2 - c) (c + 1 / 2)) with hsd
  have hs : 1 < s := lt_min (by norm_num) (lt_min (by linarith) (by linarith))
  have hs1 : s ≤ 3 / 2 := min_le_left _ _
  have hs2 : s ≤ 2 - c := (min_le_right _ _).trans (min_le_left _ _)
  have hs3 : s ≤ c + 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  set Z := ∑' k, phiS s k with hZ
  have hZ0 : 0 ≤ Z := tsum_nonneg (phiS_nonneg s)
  have h2p : (0 : ℝ) < 2 ^ (3 / 2 : ℝ) := by positivity
  set C₁ := (2 : ℝ) ^ (3 / 2 : ℝ) * (3 * Z) with hC₁
  set C₂ := 2 * Z with hC₂
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hC₂0 : 0 ≤ C₂ := by positivity
  set Λ := D * Real.exp (1 / 2) * (2 : ℝ) ^ (3 / 2 : ℝ) with hΛ
  have hΛ0 : 0 < Λ := by positivity
  refine ⟨Λ * (C₁ + C₂ + 1), by positivity, fun om hom hlo hhi g G Bg hBg hg ht hG hrep f => ?_⟩
  set K := Λ * (C₁ + C₂ + 1) with hK
  have hK0 : 0 < K := by positivity
  set M := specE.integral G with hM
  set W := ∫⁻ z, ENNReal.ofReal (om z ^ 2 * ‖f z‖ ^ 2) with hW
  by_cases hWt : W = ⊤
  · rw [hWt, ENNReal.mul_top]
    · exact le_top
    · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
  set ωl : ℕ → ℝ := fun n => Real.exp ((n : ℝ) / 2) * (1 + (n : ℝ)) ^ c with hωl
  set ωh : ℕ → ℝ := fun l => D * Real.exp ((l : ℝ) / 2) * (1 + (l : ℝ)) ^ c with hωh
  have hωl0 : ∀ n, 0 < ωl n := fun n => by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    simp only [hωl]
    have h1 : 0 < (1 + (n : ℝ)) ^ c := Real.rpow_pos_of_pos (by linarith) _
    positivity
  have hωh0 : ∀ l, 0 < ωh l := fun l => by
    have : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    simp only [hωh]
    have h1 : 0 < (1 + (l : ℝ)) ^ c := Real.rpow_pos_of_pos (by linarith) _
    positivity
  set a : ℕ → ℝ := fun n => ωl n * ‖cutN n f‖ with ha
  set B : ℕ → ℕ → ℝ := fun l n => Bg * Λ * Kt c l n with hB
  have hB0 : ∀ l n, 0 ≤ B l n := fun l n => mul_nonneg (by positivity) (Kt_nonneg c l n)
  have hblock : ∀ l n, ωh l * ‖cutN l (M (cutN n f))‖ ≤ B l n * a n := fun l n => by
    have h1 := block hg hG hrep l n f
    have h2 := ht (Tgap l n) (Tgap_nonneg l n)
    have h3 := weight_kernel (c := c) hD l n
    have h4 : ‖cutN l (M (cutN n f))‖ ≤ Bg * tF (Tgap l n) * ‖cutN n f‖ :=
      h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
    calc ωh l * ‖cutN l (M (cutN n f))‖ ≤ ωh l * (Bg * tF (Tgap l n) * ‖cutN n f‖) :=
          mul_le_mul_of_nonneg_left h4 (hωh0 l).le
      _ = Bg * ‖cutN n f‖ * (ωh l * tF (Tgap l n)) := by ring
      _ ≤ Bg * ‖cutN n f‖ * (Λ * Kt c l n * ωl n) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = B l n * a n := by simp only [hB, ha]; ring
  set F : ℕ → L2H' := fun N => ∑ n ∈ Finset.range N, cutN n f with hF
  have hsum : ∀ (N l : ℕ), ωh l * ‖cutN l (M (F N))‖ ≤ ∑ n ∈ Finset.range N, B l n * a n := fun N l => by
    have e : cutN l (M (F N)) = ∑ n ∈ Finset.range N, cutN l (M (cutN n f)) := by
      simp only [hF, map_sum]
    rw [e]
    calc _ ≤ ωh l * ∑ n ∈ Finset.range N, ‖cutN l (M (cutN n f))‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (hωh0 l).le
      _ = ∑ n ∈ Finset.range N, ωh l * ‖cutN l (M (cutN n f))‖ := Finset.mul_sum _ _ _
      _ ≤ _ := Finset.sum_le_sum fun n _ => hblock l n
  have ha0 : ∀ n, 0 ≤ a n := fun n => mul_nonneg (hωl0 n).le (norm_nonneg _)
  have hsch : ∀ N L : ℕ, ∑ l ∈ Finset.range L, (∑ n ∈ Finset.range N, B l n * a n) ^ 2
      ≤ (Bg * Λ * C₁) * (Bg * Λ * C₂) * ∑ n ∈ Finset.range N, a n ^ 2 := fun N L => by
    refine schur_finite hB0 pS_pos (fun l => ?_) (fun n => ?_) (by positivity)
    · have h := sum_Kt_n hc1 hc2 hs hs1 hs3 l N
      calc ∑ n ∈ Finset.range N, B l n * pS n = Bg * Λ * ∑ n ∈ Finset.range N, Kt c l n * pS n := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun n _ => by simp only [hB]; ring
        _ ≤ Bg * Λ * (C₁ * pS l) := mul_le_mul_of_nonneg_left h (by positivity)
        _ = Bg * Λ * C₁ * pS l := by ring
    · have h := sum_Kt_l hc1 hs hs2 n L
      calc ∑ l ∈ Finset.range L, B l n * pS l = Bg * Λ * ∑ l ∈ Finset.range L, Kt c l n * pS l := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun l _ => by simp only [hB]; ring
        _ ≤ Bg * Λ * (C₂ * pS n) := mul_le_mul_of_nonneg_left h (by positivity)
        _ = Bg * Λ * C₂ * pS n := by ring
  have hsumW : ∀ N : ℕ, ∑ n ∈ Finset.range N, a n ^ 2 ≤ W.toReal := fun N => by
    rw [← ENNReal.ofReal_le_iff_le_toReal hWt, ENNReal.ofReal_sum_of_nonneg fun n _ => by positivity]
    calc ∑ n ∈ Finset.range N, ENNReal.ofReal (a n ^ 2)
        ≤ ∑ n ∈ Finset.range N, ∫⁻ z in shell n, ENNReal.ofReal (om z ^ 2 * ‖f z‖ ^ 2) := by
          refine Finset.sum_le_sum fun n _ => ?_
          have h := shell_lower (om := om) (hωl0 n).le (fun z hz => hlo n z hz) f
          have e : a n ^ 2 = ωl n ^ 2 * ‖cutN n f‖ ^ 2 := by simp only [ha]; ring
          rw [e]
          exact h
      _ = ∫⁻ z in ⋃ n ∈ Finset.range N, shell n, ENNReal.ofReal (om z ^ 2 * ‖f z‖ ^ 2) :=
          (lintegral_biUnion_finset (fun a _ b _ hab => shell_disjoint hab) (fun n _ => measurableSet_shell n) _).symm
      _ ≤ W := setLIntegral_le_lintegral _ _
  set Q := (Bg * Λ * C₁) * (Bg * Λ * C₂) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hfin : ∀ N L : ℕ, ∑ l ∈ Finset.range L, (ωh l * ‖cutN l (M (F N))‖) ^ 2 ≤ Q * W.toReal := fun N L => by
    calc _ ≤ ∑ l ∈ Finset.range L, (∑ n ∈ Finset.range N, B l n * a n) ^ 2 :=
          Finset.sum_le_sum fun l _ =>
            pow_le_pow_left₀ (mul_nonneg (hωh0 l).le (norm_nonneg _)) (hsum N l) 2
      _ ≤ Q * ∑ n ∈ Finset.range N, a n ^ 2 := hsch N L
      _ ≤ Q * W.toReal := mul_le_mul_of_nonneg_left (hsumW N) hQ0
  set v := M f with hv
  have hlim : ∀ L : ℕ, ∑ l ∈ Finset.range L, (ωh l * ‖cutN l v‖) ^ 2 ≤ Q * W.toReal := fun L => by
    have ht1 : Tendsto (fun N : ℕ => ∑ l ∈ Finset.range L, (ωh l * ‖cutN l (M (F N))‖) ^ 2) atTop
        (𝓝 (∑ l ∈ Finset.range L, (ωh l * ‖cutN l v‖) ^ 2)) := by
      refine tendsto_finsetSum _ fun l _ => ?_
      have h1 : Tendsto (fun N : ℕ => cutN l (M (F N))) atTop (𝓝 (cutN l v)) :=
        ((cutN l).continuous.tendsto _).comp (((M).continuous.tendsto _).comp (tendsto_sum_cutN f))
      exact (h1.norm.const_mul _).pow 2
    exact le_of_tendsto' ht1 fun N => hfin N L
  have hunion : (⋃ l, shell l) = (univ : Set UpperHalfPlane) := by
    ext z
    simp only [mem_iUnion, mem_univ, iff_true]
    exact ⟨_, rfl⟩
  have htot : ∫⁻ z, ENNReal.ofReal (om z ^ 2 * ‖v z‖ ^ 2) = ∑' l, ∫⁻ z in shell l, ENNReal.ofReal (om z ^ 2 * ‖v z‖ ^ 2) := by
    rw [← lintegral_iUnion measurableSet_shell shell_disjoint, hunion, Measure.restrict_univ]
  rw [htot]
  refine ENNReal.tsum_le_of_sum_range_le fun L => ?_
  calc ∑ l ∈ Finset.range L, ∫⁻ z in shell l, ENNReal.ofReal (om z ^ 2 * ‖v z‖ ^ 2)
      ≤ ∑ l ∈ Finset.range L, ENNReal.ofReal (ωh l ^ 2 * ‖cutN l v‖ ^ 2) :=
        Finset.sum_le_sum fun l _ => shell_upper hom (fun z hz => hhi l z hz) v
    _ = ENNReal.ofReal (∑ l ∈ Finset.range L, (ωh l * ‖cutN l v‖) ^ 2) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun l _ => by positivity]
        exact Finset.sum_congr rfl fun l _ => by rw [← mul_pow]
    _ ≤ ENNReal.ofReal (Q * W.toReal) := ENNReal.ofReal_le_ofReal (hlim L)
    _ ≤ ENNReal.ofReal ((K * Bg) ^ 2 * W.toReal) := by
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg)
        have e : (K * Bg) ^ 2 = (Bg * Λ) ^ 2 * (C₁ + C₂ + 1) ^ 2 := by rw [hK]; ring
        have e2 : Q = (Bg * Λ) ^ 2 * (C₁ * C₂) := by rw [hQ]; ring
        rw [e, e2]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        nlinarith [mul_nonneg hC₁0 hC₂0, sq_nonneg C₁, sq_nonneg C₂]
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hWt]

end Qschubert
