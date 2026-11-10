import Qschubert.KLMweak

/-!
# Multipliers with analytic word bounds preserve analyticity at a reduced radius

`lem_m_gen`: if every word of `X`, `Y` applied to the function `m` is bounded by `A |S|! ρ^{-|S|}` on `ℍ`, then multiplication by `m` maps `Dom e^{αΛ}` to `Dom e^{bΛ}`,
with `b = α/(4M)`, `M` depending only on `ρ` and the constants of Lemma FC. This is `lem_m_weak` with the weight `X₀^{-β}` replaced by a general `m`. `exp_of_words` is its second half.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set
open scoped ENNReal ContDiff Nat

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- Analytic word bounds for a multiplier (`ρi = ρ⁻¹`). -/
structure WB (m : ℂ → ℝ) (A ρi : ℝ) : Prop where
  s : ∀ w : ℂ, 0 < w.im → ContDiffAt ℝ ∞ m w
  b : ∀ (S : List Bool) (w : ℂ), 0 < w.im → |wordR S m w| ≤ A * S.length.factorial * ρi ^ S.length

/-- The bound of the word `T`. -/
noncomputable def wbdM (A ρi : ℝ) (T : List Bool) : ℝ := A * T.length.factorial * ρi ^ T.length

/-- The admissibility constant of the word `T`. -/
noncomputable def admM (A ρi : ℝ) (T : List Bool) : ℝ :=
  wbdM A ρi T + wbdM A ρi (true :: T) + wbdM A ρi (false :: T) + wbdM A ρi (true :: true :: T) + wbdM A ρi (false :: false :: T)

section gen

variable {m : ℂ → ℝ} {A ρi : ℝ}

lemma WB.word_s (H : WB m A ρi) (T : List Bool) {w : ℂ} (hw : 0 < w.im) : ContDiffAt ℝ ∞ (wordR T m) w := by
  induction T with
  | nil => exact H.s w hw
  | cons z T ih => exact contDiffAt_vfR _ ih

lemma WB.wbd_nonneg (H : WB m A ρi) (T : List Bool) : 0 ≤ wbdM A ρi T :=
  (abs_nonneg _).trans (H.b T Complex.I (by simp))

lemma WB.A_nonneg (H : WB m A ρi) : 0 ≤ A := by
  have h := H.wbd_nonneg ([] : List Bool)
  simpa [wbdM] using h

/-- The admissibility of words of `m`. -/
lemma WB.adm (H : WB m A ρi) (T : List Bool) : Adm (wordR T m) (admM A ρi T) := by
  have n0 := H.wbd_nonneg T
  have n1 := H.wbd_nonneg (true :: T)
  have n2 := H.wbd_nonneg (false :: T)
  have n3 := H.wbd_nonneg (true :: true :: T)
  have n4 := H.wbd_nonneg (false :: false :: T)
  have eX : vfR 1 (wordR T m) = wordR (true :: T) m := by simp only [wordR, letter_true]
  have eY : vfR Complex.I (wordR T m) = wordR (false :: T) m := by simp only [wordR, letter_false]
  have eXX : vfR 1 (wordR (true :: T) m) = wordR (true :: true :: T) m := by simp only [wordR, letter_true]
  have eYY : vfR Complex.I (wordR (false :: T) m) = wordR (false :: false :: T) m := by
    simp only [wordR, letter_false]
  have ba : ∀ (U : List Bool) (w : ℂ), 0 < w.im → |wordR U m w| ≤ wbdM A ρi U := fun U w hw => H.b U w hw
  refine ⟨fun w hw => H.word_s T hw, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · have := ba T w hw; unfold admM; linarith
  · rw [eX]; have := ba (true :: T) w hw; unfold admM; linarith
  · rw [eY]; have := ba (false :: T) w hw; unfold admM; linarith
  · unfold lapRv
    rw [eX, eY, eXX, eYY]
    have h1 := ba (true :: true :: T) w hw
    have h2 := ba (false :: false :: T) w hw
    have h3 := ba (false :: T) w hw
    have t : |wordR (true :: true :: T) m w + wordR (false :: false :: T) m w - wordR (false :: T) m w|
        ≤ |wordR (true :: true :: T) m w| + |wordR (false :: false :: T) m w| + |wordR (false :: T) m w| := by
      rcases abs_cases (wordR (true :: true :: T) m w) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
      rcases abs_cases (wordR (false :: false :: T) m w) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
      rcases abs_cases (wordR (false :: T) m w) with ⟨e3, _⟩ | ⟨e3, _⟩ <;>
      rw [e1, e2, e3, abs_le] <;> constructor <;> linarith
    unfold admM
    linarith

variable (H : WB m A ρi)

/-- Multiplication by `Z_T m`. -/
noncomputable def mulM (T : List Bool) : L2H' →L[ℂ] L2H' := mulCL (H.adm T).sb

/-- One letter on `Z_T X₀^{-β} · u`. -/
lemma domZ_mulM (z : Bool) (T : List Bool) (u : negLapH.domain) (h : mulM H T (u : L2H') ∈ negLapH.domain) :
    domZ z ⟨mulM H T (u : L2H'), h⟩ = mulM H (z :: T) (u : L2H') + mulM H T (domZ z u) := by
  cases z with
  | true =>
    simp only [domZ, ite_true]
    have := domX_mul (WB.adm H T) u
    rw [show (⟨mulM H T (u : L2H'), h⟩ : negLapH.domain) = ⟨mulCL (WB.adm H T).sb (u : L2H'), mul_mem_domain (WB.adm H T) u⟩ from rfl,
      this]
    rw [mulCL_congr (WB.adm H T).sbX (WB.adm H (true :: T)).sb (by simp only [wordR, letter_true]) (u : L2H')]
    rfl
  | false =>
    simp only [domZ, Bool.false_eq_true, ite_false]
    have := domY_mul (WB.adm H T) u
    rw [show (⟨mulM H T (u : L2H'), h⟩ : negLapH.domain) = ⟨mulCL (WB.adm H T).sb (u : L2H'), mul_mem_domain (WB.adm H T) u⟩ from rfl,
      this]
    rw [mulCL_congr (WB.adm H T).sbY (WB.adm H (false :: T)).sb (by simp only [wordR, letter_false]) (u : L2H')]
    rfl

/-- A term of the Leibniz expansion. -/
noncomputable def termM (F : L2H') (q : List Bool × List Bool) : L2H' := mulM H q.1 (wordAct q.2 F)

section leibM

variable {F : L2H'} (hFw : ∀ U, WordDom U F)
include hFw

lemma termM_mem (q : List Bool × List Bool) : termM H F q ∈ negLapH.domain :=
  mul_mem_domain (WB.adm H q.1) ⟨wordAct q.2 F, (hFw (true :: q.2)).2⟩

/-- **Leibniz for words.** -/
theorem word_leibnizM (S : List Bool) :
    WordDom S (mulM H [] F) ∧ wordAct S (mulM H [] F) = ((Leib S).map (termM H F)).sum := by
  induction S with
  | nil =>
    refine ⟨trivial, ?_⟩
    simp [Leib, wordAct, termM]
  | cons z S ih =>
    obtain ⟨hd, hs⟩ := ih
    have hmem : ((Leib S).map (termM H F)).sum ∈ negLapH.domain := by
      refine list_sum_mem fun x hx => ?_
      obtain ⟨q, _, rfl⟩ := List.mem_map.1 hx
      exact termM_mem H hFw q
    have hmem' : wordAct S (mulM H [] F) ∈ negLapH.domain := hs ▸ hmem
    refine ⟨⟨hd, hmem'⟩, ?_⟩
    rw [wordAct_cons z S hmem']
    have hsub : (⟨wordAct S (mulM H [] F), hmem'⟩ : negLapH.domain) = ⟨((Leib S).map (termM H F)).sum, hmem⟩ :=
      Subtype.ext hs
    rw [hsub, domZ_list_sum z (Leib S) (termM H F) (termM_mem H hFw) hmem]
    have hstep : ∀ q, domZ z ⟨termM H F q, termM_mem H hFw q⟩
        = termM H F (z :: q.1, q.2) + termM H F (q.1, z :: q.2) := by
      intro q
      have hq := (hFw (true :: q.2)).2
      have h1 := domZ_mulM H z q.1 ⟨wordAct q.2 F, hq⟩ (termM_mem H hFw q)
      have e : wordAct (z :: q.2) F = domZ z ⟨wordAct q.2 F, hq⟩ := wordAct_cons z q.2 hq
      simp only [termM]
      rw [e]
      exact h1
    simp only [hstep, Leib, List.map_append, List.map_map, List.sum_append, List.sum_map_add]
    rfl


end leibM

/-- The word as a multiplier, with its own bound. -/
lemma WB.sbW (H : WB m A ρi) (T : List Bool) : SB (wordR T m) (wbdM A ρi T) := ⟨fun w hw => H.word_s T hw, fun w hw => H.b T w hw⟩

/-- **Lemma SC for a general multiplier.** -/
theorem lem_sc_gen {τ₀ C₁ : ℝ} (hF' : FCBound τ₀ C₁) (hC : 0 ≤ C₁) (hρ : 0 ≤ ρi) (S : List Bool) {α : ℝ}
    (hα : 0 < α) (hle : α ≤ τ₀) {F : L2H'} (hFd : F ∈ (expLambda α).domain) :
    WordDom S (mulM H [] F) ∧
      ‖wordAct S (mulM H [] F)‖ ≤ A * (S.length + 1) * S.length.factorial * (max (Real.exp 1 * C₁) (τ₀ * ρi) / α) ^ S.length
        * ‖expLambda α ⟨F, hFd⟩‖ := by
  have hFw : ∀ U, WordDom U F := fun U => (lem_wc_zero hF' hC U hα hle hFd).1
  obtain ⟨hd, hs⟩ := word_leibnizM H hFw S
  refine ⟨hd, ?_⟩
  have hA0 := H.A_nonneg
  set N := ‖expLambda α ⟨F, hFd⟩‖
  have hN : 0 ≤ N := norm_nonneg _
  set K : ℝ := max (Real.exp 1 * C₁) (τ₀ * ρi) / α
  have hK1 : Real.exp 1 * C₁ / α ≤ K := by
    simp only [K]; gcongr; exact le_max_left _ _
  have hτ : 0 < τ₀ := by linarith
  have hK2 : ρi ≤ K := by
    have h1 : τ₀ * ρi / α ≤ K := by
      simp only [K]; gcongr; exact le_max_right _ _
    refine le_trans ?_ h1
    rw [le_div_iff₀ hα]
    nlinarith
  have hK10 : 0 ≤ Real.exp 1 * C₁ / α := by positivity
  set Aq : List Bool × List Bool → L2H' := fun q => termM H F q with hAq
  have hterm : ∀ q ∈ Leib S, ‖Aq q‖ ≤ A * K ^ S.length * N * ((q.1.length.factorial : ℝ) * q.2.length.factorial) := by
    intro q hq
    have hlen := Leib_len S q hq
    have h1 : ‖wordAct q.2 F‖ ≤ (Real.exp 1 * C₁ / α) ^ q.2.length * q.2.length.factorial * N :=
      (lem_wc_zero hF' hC q.2 hα hle hFd).2
    have e : Aq q = mulCL (H.sbW q.1) (wordAct q.2 F) := mulCL_congr _ _ rfl _
    have h2 := norm_mulCL_le (H.sbW q.1) (wordAct q.2 F)
    have hp1 : ρi ^ q.1.length * (Real.exp 1 * C₁ / α) ^ q.2.length ≤ K ^ S.length := by
      rw [← hlen, pow_add]
      gcongr
    have hf1 : (0 : ℝ) ≤ q.1.length.factorial := by positivity
    have hf2 : (0 : ℝ) ≤ q.2.length.factorial := by positivity
    rw [e]
    calc _ ≤ wbdM A ρi q.1 * ‖wordAct q.2 F‖ := h2
      _ ≤ wbdM A ρi q.1 * ((Real.exp 1 * C₁ / α) ^ q.2.length * q.2.length.factorial * N) := by
          exact mul_le_mul_of_nonneg_left h1 (H.wbd_nonneg _)
      _ = A * (ρi ^ q.1.length * (Real.exp 1 * C₁ / α) ^ q.2.length) * N
          * ((q.1.length.factorial : ℝ) * q.2.length.factorial) := by unfold wbdM; ring
      _ ≤ A * K ^ S.length * N * ((q.1.length.factorial : ℝ) * q.2.length.factorial) := by gcongr
  have hsum := (norm_list_sum_le' (Leib S) Aq).trans (list_sum_le hterm)
  rw [List.sum_map_mul_left, Leib_sum, Nat.factorial_succ] at hsum
  push_cast at hsum
  rw [hs]
  calc _ ≤ _ := hsum
    _ = _ := by ring

end gen

/-- **Analyticity from word bounds.** -/
theorem exp_of_words {M α B N : ℝ} {a : L2H'} (hA : AllWords a) (hα : 0 < α) (hM1 : 1 ≤ M) (hB0 : 0 ≤ B) (hN0 : 0 ≤ N)
    (hα1 : α ≤ 1)
    (hw : ∀ S : List Bool, ‖wordAct S a‖ ≤ B * (S.length + 1) * S.length.factorial * (M / α) ^ S.length * N) :
    ∃ hd : a ∈ (expLambda (α / (4 * M))).domain, ‖expLambda (α / (4 * M)) ⟨a, hd⟩‖ ≤ 32 / 5 * B * N := by
  have hM0 : 0 < M := by linarith
  have hMα : 1 ≤ M / α := by rw [le_div_iff₀ hα]; nlinarith
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
