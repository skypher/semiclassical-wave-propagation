import Qschubert.KLMult

/-!
# Lemma SC: the static weighted Cauchy estimate for words

`lem_sc` (`lem:sc`): for `β ≥ 0`, a word `S` of length `m`, `0 < α ≤ τ₀` and `F ∈ Dom e^{αΛ}`, with `a = X₀^{-β}F`:
every intermediate vector of `Z₁⋯Z_m a` lies in `Dom(-Δ)` and
`‖X₀^β Z₁⋯Z_m a‖ ≤ B_β (m+1) m! (C₃/α)^m ‖e^{αΛ}F‖`, `C₃ = max(eC₁, τ₀/ρ)`, `ρ = ¼ log(3/2)`.

Proof as printed: Leibniz for words (`word_leibniz`, indexed by the list `Leib S` of splittings `(T, U)` of `S`),
`lem:fdb` for `X₀^β Z_T X₀^{-β}`, `lem:wc` with `α'' = 0` for `Z_U F`, and `Σ |T|! |U|! = (m+1)!` (`Leib_sum`).
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set
open scoped ENNReal ContDiff

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- `X₀^{-β} = hF^β`. -/
noncomputable def hp (β : ℝ) : ℂ → ℝ := fun u => hF u ^ β

lemma hF_le_one {w : ℂ} (hw : 0 < w.im) : hF w ≤ 1 := by
  have h := hF_eq_inv_coshD (⟨w, hw⟩ : UpperHalfPlane)
  have e : hF w = (coshD UpperHalfPlane.I ⟨w, hw⟩)⁻¹ := h
  rw [e]
  exact inv_le_one_of_one_le₀ (Real.one_le_cosh _)

lemma contDiffAt_hp (β : ℝ) {w : ℂ} (hw : 0 < w.im) : ContDiffAt ℝ ∞ (hp β) w :=
  contDiff_hF.contDiffAt.rpow_const_of_ne (hF_pos hw).ne'

lemma contDiffAt_wordR (β : ℝ) (T : List Bool) {w : ℂ} (hw : 0 < w.im) : ContDiffAt ℝ ∞ (wordR T (hp β)) w := by
  induction T with
  | nil => exact contDiffAt_hp β hw
  | cons z T ih => exact contDiffAt_vfR _ ih

lemma letter_true : letter true = 1 := by simp [letter]
lemma letter_false : letter false = Complex.I := by simp [letter]

/-- The output of `lem:fdb`. -/
def FdbB (β B : ℝ) : Prop :=
  ∀ (S : List Bool) (w : ℂ), 0 < w.im → |hF w ^ (-β) * wordR S (fun u => hF u ^ β) w| ≤ B * S.length.factorial * rhoFdb⁻¹ ^ S.length

/-- The bound of the word `T`. -/
noncomputable def wbd (B : ℝ) (T : List Bool) : ℝ := B * T.length.factorial * rhoFdb⁻¹ ^ T.length

section adm

variable {β B : ℝ}

lemma wbd_nonneg (hB : FdbB β B) (T : List Bool) : 0 ≤ wbd B T :=
  (abs_nonneg _).trans (hB T Complex.I (by simp))

lemma abs_wordR_le (hβ : 0 ≤ β) (hB : FdbB β B) (T : List Bool) {w : ℂ} (hw : 0 < w.im) :
    |wordR T (hp β) w| ≤ wbd B T := by
  have h := hB T w hw
  have hp0 := hF_pos hw
  have hle : hF w ^ β ≤ 1 := Real.rpow_le_one hp0.le (hF_le_one hw) hβ
  have hnn : 0 ≤ hF w ^ β := Real.rpow_nonneg hp0.le _
  have e : wordR T (hp β) w = hF w ^ β * (hF w ^ (-β) * wordR T (fun u => hF u ^ β) w) := by
    rw [← mul_assoc, ← Real.rpow_add hp0, add_neg_cancel, Real.rpow_zero, one_mul]; rfl
  rw [e, abs_mul, abs_of_nonneg hnn]
  calc _ ≤ 1 * (B * T.length.factorial * rhoFdb⁻¹ ^ T.length) := by gcongr
    _ = wbd B T := one_mul _

/-- The admissibility constant of the word `T`. -/
noncomputable def admC (B : ℝ) (T : List Bool) : ℝ :=
  wbd B T + wbd B (true :: T) + wbd B (false :: T) + wbd B (true :: true :: T) + wbd B (false :: false :: T)

lemma adm_word (hβ : 0 ≤ β) (hB : FdbB β B) (T : List Bool) : Adm (wordR T (hp β)) (admC B T) := by
  have n0 := wbd_nonneg hB T
  have n1 := wbd_nonneg hB (true :: T)
  have n2 := wbd_nonneg hB (false :: T)
  have n3 := wbd_nonneg hB (true :: true :: T)
  have n4 := wbd_nonneg hB (false :: false :: T)
  have eX : vfR 1 (wordR T (hp β)) = wordR (true :: T) (hp β) := by simp only [wordR, letter_true]
  have eY : vfR Complex.I (wordR T (hp β)) = wordR (false :: T) (hp β) := by simp only [wordR, letter_false]
  have eXX : vfR 1 (wordR (true :: T) (hp β)) = wordR (true :: true :: T) (hp β) := by simp only [wordR, letter_true]
  have eYY : vfR Complex.I (wordR (false :: T) (hp β)) = wordR (false :: false :: T) (hp β) := by
    simp only [wordR, letter_false]
  refine ⟨fun w hw => contDiffAt_wordR β T hw, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · have := abs_wordR_le hβ hB T hw; unfold admC; linarith
  · rw [eX]; have := abs_wordR_le hβ hB (true :: T) hw; unfold admC; linarith
  · rw [eY]; have := abs_wordR_le hβ hB (false :: T) hw; unfold admC; linarith
  · unfold lapRv
    rw [eX, eY, eXX, eYY]
    have h1 := abs_wordR_le hβ hB (true :: true :: T) hw
    have h2 := abs_wordR_le hβ hB (false :: false :: T) hw
    have h3 := abs_wordR_le hβ hB (false :: T) hw
    have t : |wordR (true :: true :: T) (hp β) w + wordR (false :: false :: T) (hp β) w - wordR (false :: T) (hp β) w|
        ≤ |wordR (true :: true :: T) (hp β) w| + |wordR (false :: false :: T) (hp β) w| + |wordR (false :: T) (hp β) w| := by
      rcases abs_cases (wordR (true :: true :: T) (hp β) w) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
      rcases abs_cases (wordR (false :: false :: T) (hp β) w) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
      rcases abs_cases (wordR (false :: T) (hp β) w) with ⟨e3, _⟩ | ⟨e3, _⟩ <;>
      rw [e1, e2, e3, abs_le] <;> constructor <;> linarith
    unfold admC
    linarith

end adm

/-- The splittings of a word. -/
def Leib : List Bool → List (List Bool × List Bool)
  | [] => [([], [])]
  | z :: S => (Leib S).map (fun q => (z :: q.1, q.2)) ++ (Leib S).map (fun q => (q.1, z :: q.2))

lemma Leib_len (S : List Bool) : ∀ q ∈ Leib S, q.1.length + q.2.length = S.length := by
  induction S with
  | nil => simp [Leib]
  | cons z S ih =>
    intro q hq
    simp only [Leib, List.mem_append, List.mem_map] at hq
    rcases hq with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
    · have := ih r hr; simp only [List.length_cons]; omega
    · have := ih r hr; simp only [List.length_cons]; omega

/-- **`Σ_{(T,U)} |T|! |U|! = (m+1)!`.** -/
lemma Leib_sum (S : List Bool) :
    ((Leib S).map fun q => ((q.1.length.factorial : ℝ) * q.2.length.factorial)).sum = (S.length + 1).factorial := by
  induction S with
  | nil => simp [Leib]
  | cons z S ih =>
    simp only [Leib, List.map_append, List.map_map, List.sum_append, List.length_cons]
    have hpt : ∀ q ∈ Leib S, ((((q.1.length + 1).factorial : ℕ) : ℝ) * q.2.length.factorial
        + (q.1.length.factorial : ℝ) * ((q.2.length + 1).factorial : ℕ))
        = (S.length + 2 : ℝ) * ((q.1.length.factorial : ℝ) * q.2.length.factorial) := by
      intro q hq
      have hl : (q.1.length : ℝ) + q.2.length = S.length := by exact_mod_cast Leib_len S q hq
      rw [Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      rw [← hl]; ring
    have hsum := List.sum_map_add (l := Leib S)
      (f := fun q => ((((q.1.length + 1).factorial : ℕ) : ℝ) * q.2.length.factorial))
      (g := fun q => (q.1.length.factorial : ℝ) * ((q.2.length + 1).factorial : ℕ))
    have e1 : ((fun q : List Bool × List Bool => ((q.1.length.factorial : ℝ) * q.2.length.factorial)) ∘
        fun q : List Bool × List Bool => (z :: q.1, q.2))
        = fun q => ((((q.1.length + 1).factorial : ℕ) : ℝ) * q.2.length.factorial) := by
      funext q; simp
    have e2 : ((fun q : List Bool × List Bool => ((q.1.length.factorial : ℝ) * q.2.length.factorial)) ∘
        fun q : List Bool × List Bool => (q.1, z :: q.2))
        = fun q => (q.1.length.factorial : ℝ) * ((q.2.length + 1).factorial : ℕ) := by
      funext q; simp
    rw [e1, e2, ← hsum, List.map_congr_left hpt, List.sum_map_mul_left, ih,
      Nat.factorial_succ (S.length + 1)]
    push_cast; ring

section lists

variable {ι E : Type*} [NormedAddCommGroup E]

lemma norm_list_sum_le' (L : List ι) (f : ι → E) : ‖(L.map f).sum‖ ≤ (L.map fun i => ‖f i‖).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

lemma list_sum_le {L : List ι} {f g : ι → ℝ} (h : ∀ i ∈ L, f i ≤ g i) : (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a (by simp)) (ih fun i hi => h i (by simp [hi]))

end lists

lemma mulCL_congr {g g' : ℂ → ℝ} {C C' : ℝ} (H : SB g C) (H' : SB g' C') (e : g = g') (u : L2H') :
    mulCL H u = mulCL H' u := by
  subst e
  apply Lp.ext
  filter_upwards [coe_mulCL H u, coe_mulCL H' u] with z h1 h2
  rw [h1, h2]

lemma domZ_add (z : Bool) (u v : negLapH.domain) : domZ z (u + v) = domZ z u + domZ z v := by
  have e : liftDom (u + v) = liftDom u + liftDom v := by
    unfold liftDom
    rw [Submodule.coe_add, LinearPMap.map_add, ← map_add]
    congr 1; abel
  cases z <;> simp only [domZ, Bool.false_eq_true, ite_false, ite_true, domX, domY, e, map_add]

lemma domZ_zero (z : Bool) : domZ z (0 : negLapH.domain) = 0 := by
  have e : liftDom (0 : negLapH.domain) = 0 := by
    unfold liftDom
    rw [Submodule.coe_zero, LinearPMap.map_zero, add_zero, map_zero]
  cases z <;> simp only [domZ, Bool.false_eq_true, ite_false, ite_true, domX, domY, e, map_zero]

lemma domZ_list_sum {ι : Type*} (z : Bool) (L : List ι) (f : ι → L2H') (hf : ∀ i, f i ∈ negLapH.domain)
    (h : (L.map f).sum ∈ negLapH.domain) :
    domZ z ⟨(L.map f).sum, h⟩ = (L.map fun i => domZ z ⟨f i, hf i⟩).sum := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact domZ_zero z
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons] at h ⊢
    have hL : (L.map f).sum ∈ negLapH.domain := by
      have := Submodule.sub_mem _ h (hf a)
      rwa [add_sub_cancel_left] at this
    rw [show (⟨f a + (L.map f).sum, h⟩ : negLapH.domain) = ⟨f a, hf a⟩ + ⟨(L.map f).sum, hL⟩ from rfl, domZ_add, ih hL]

section leibniz

variable {β B : ℝ} (hβ : 0 ≤ β) (hB : FdbB β B)

/-- Multiplication by `Z_T X₀^{-β}`. -/
noncomputable def mulW (T : List Bool) : L2H' →L[ℂ] L2H' := mulCL (adm_word hβ hB T).sb

/-- One letter on `Z_T X₀^{-β} · u`. -/
lemma domZ_mulW (z : Bool) (T : List Bool) (u : negLapH.domain) (h : mulW hβ hB T (u : L2H') ∈ negLapH.domain) :
    domZ z ⟨mulW hβ hB T (u : L2H'), h⟩ = mulW hβ hB (z :: T) (u : L2H') + mulW hβ hB T (domZ z u) := by
  cases z with
  | true =>
    simp only [domZ, ite_true]
    have := domX_mul (adm_word hβ hB T) u
    rw [show (⟨mulW hβ hB T (u : L2H'), h⟩ : negLapH.domain) = ⟨mulCL (adm_word hβ hB T).sb (u : L2H'), mul_mem_domain (adm_word hβ hB T) u⟩ from rfl,
      this]
    rw [mulCL_congr (adm_word hβ hB T).sbX (adm_word hβ hB (true :: T)).sb (by simp only [wordR, letter_true]) (u : L2H')]
    rfl
  | false =>
    simp only [domZ, Bool.false_eq_true, ite_false]
    have := domY_mul (adm_word hβ hB T) u
    rw [show (⟨mulW hβ hB T (u : L2H'), h⟩ : negLapH.domain) = ⟨mulCL (adm_word hβ hB T).sb (u : L2H'), mul_mem_domain (adm_word hβ hB T) u⟩ from rfl,
      this]
    rw [mulCL_congr (adm_word hβ hB T).sbY (adm_word hβ hB (false :: T)).sb (by simp only [wordR, letter_false]) (u : L2H')]
    rfl

/-- A term of the Leibniz expansion. -/
noncomputable def termW (F : L2H') (q : List Bool × List Bool) : L2H' := mulW hβ hB q.1 (wordAct q.2 F)

variable {F : L2H'} (hFw : ∀ U, WordDom U F)
include hFw

lemma termW_mem (q : List Bool × List Bool) : termW hβ hB F q ∈ negLapH.domain :=
  mul_mem_domain (adm_word hβ hB q.1) ⟨wordAct q.2 F, (hFw (true :: q.2)).2⟩

/-- **Leibniz for words.** -/
theorem word_leibniz (S : List Bool) :
    WordDom S (mulW hβ hB [] F) ∧ wordAct S (mulW hβ hB [] F) = ((Leib S).map (termW hβ hB F)).sum := by
  induction S with
  | nil =>
    refine ⟨trivial, ?_⟩
    simp [Leib, wordAct, termW]
  | cons z S ih =>
    obtain ⟨hd, hs⟩ := ih
    have hmem : ((Leib S).map (termW hβ hB F)).sum ∈ negLapH.domain := by
      refine list_sum_mem fun x hx => ?_
      obtain ⟨q, _, rfl⟩ := List.mem_map.1 hx
      exact termW_mem hβ hB hFw q
    have hmem' : wordAct S (mulW hβ hB [] F) ∈ negLapH.domain := hs ▸ hmem
    refine ⟨⟨hd, hmem'⟩, ?_⟩
    rw [wordAct_cons z S hmem']
    have hsub : (⟨wordAct S (mulW hβ hB [] F), hmem'⟩ : negLapH.domain) = ⟨((Leib S).map (termW hβ hB F)).sum, hmem⟩ :=
      Subtype.ext hs
    rw [hsub, domZ_list_sum z (Leib S) (termW hβ hB F) (termW_mem hβ hB hFw) hmem]
    have hstep : ∀ q, domZ z ⟨termW hβ hB F q, termW_mem hβ hB hFw q⟩
        = termW hβ hB F (z :: q.1, q.2) + termW hβ hB F (q.1, z :: q.2) := by
      intro q
      have hq := (hFw (true :: q.2)).2
      have h1 := domZ_mulW hβ hB z q.1 ⟨wordAct q.2 F, hq⟩ (termW_mem hβ hB hFw q)
      have e : wordAct (z :: q.2) F = domZ z ⟨wordAct q.2 F, hq⟩ := wordAct_cons z q.2 hq
      simp only [termW]
      rw [e]
      exact h1
    simp only [hstep, Leib, List.map_append, List.map_map, List.sum_append, List.sum_map_add]
    rfl

end leibniz

section final

variable {β B : ℝ}

/-- `X₀^β Z_T X₀^{-β}`. -/
noncomputable def gT (β : ℝ) (T : List Bool) : ℂ → ℝ := fun w => hF w ^ (-β) * wordR T (fun u => hF u ^ β) w

lemma sb_gT (hB : FdbB β B) (T : List Bool) : SB (gT β T) (wbd B T) :=
  ⟨fun w hw => (contDiff_hF.contDiffAt.rpow_const_of_ne (hF_pos hw).ne').mul (contDiffAt_wordR β T hw),
    fun w hw => hB T w hw⟩

lemma ae_sum_weight {ι : Type*} (L : List ι) (A B' : ι → L2H') (W : UpperHalfPlane → ℂ)
    (h : ∀ i, (A i : UpperHalfPlane → ℂ) =ᵐ[volume] fun z => W z * B' i z) :
    (((L.map A).sum : L2H') : UpperHalfPlane → ℂ) =ᵐ[volume] fun z => W z * ((L.map B').sum : L2H') z := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure UpperHalfPlane)] with z hz
    rw [hz]; simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    filter_upwards [Lp.coeFn_add (A a) (L.map A).sum, Lp.coeFn_add (B' a) (L.map B').sum, h a, ih] with z e1 e2 e3 e4
    rw [e1, e2]
    simp only [Pi.add_apply]
    rw [e3, e4]; ring

/-- **Lemma SC** with the constants supplied by `lem:fc` and `lem:fdb`. -/
theorem lem_sc {τ₀ C₁ : ℝ} (hF' : FCBound τ₀ C₁) (hC : 0 ≤ C₁) (hβ : 0 ≤ β) (hB : FdbB β B) (S : List Bool) {α : ℝ}
    (hα : 0 < α) (hle : α ≤ τ₀) {F : L2H'} (hFd : F ∈ (expLambda α).domain) :
    WordDom S (mulW hβ hB [] F) ∧ ∃ G : L2H',
      (G : UpperHalfPlane → ℂ) =ᵐ[volume] (fun z => ((hF (z : ℂ) ^ (-β) : ℝ) : ℂ) * wordAct S (mulW hβ hB [] F) z) ∧
      ‖G‖ ≤ B * (S.length + 1) * S.length.factorial * (max (Real.exp 1 * C₁) (τ₀ / rhoFdb) / α) ^ S.length
        * ‖expLambda α ⟨F, hFd⟩‖ := by
  have hFw : ∀ U, WordDom U F := fun U => (lem_wc_zero hF' hC U hα hle hFd).1
  obtain ⟨hd, hs⟩ := word_leibniz hβ hB hFw S
  refine ⟨hd, ?_⟩
  have hB0 : 0 ≤ B := by
    have h := wbd_nonneg hB ([] : List Bool)
    simpa [wbd] using h
  have hρ := rhoFdb_pos
  set A : List Bool × List Bool → L2H' := fun q => mulCL (sb_gT hB q.1) (wordAct q.2 F)
  set G : L2H' := ((Leib S).map A).sum
  refine ⟨G, ?_, ?_⟩
  · rw [hs]
    refine ae_sum_weight _ _ _ _ fun q => ?_
    filter_upwards [coe_mulCL (sb_gT hB q.1) (wordAct q.2 F), coe_mulCL (adm_word hβ hB q.1).sb (wordAct q.2 F)] with z h1 h2
    show (mulCL (sb_gT hB q.1) (wordAct q.2 F) : L2H') z = _ * (mulCL (adm_word hβ hB q.1).sb (wordAct q.2 F) : L2H') z
    rw [h1, h2]
    simp only [gT]
    rw [show (fun u => hF u ^ β) = hp β from rfl]
    push_cast; ring
  · set N := ‖expLambda α ⟨F, hFd⟩‖
    have hN : 0 ≤ N := norm_nonneg _
    set K : ℝ := max (Real.exp 1 * C₁) (τ₀ / rhoFdb) / α
    have hK1 : Real.exp 1 * C₁ / α ≤ K := by
      simp only [K]; gcongr; exact le_max_left _ _
    have hτ : 0 < τ₀ := by linarith
    have hK2 : rhoFdb⁻¹ ≤ K := by
      have h1 : τ₀ / rhoFdb / α ≤ K := by
        simp only [K]; gcongr; exact le_max_right _ _
      refine le_trans ?_ h1
      rw [inv_eq_one_div, div_div, div_le_div_iff₀ hρ (by positivity)]
      nlinarith
    have hK10 : 0 ≤ Real.exp 1 * C₁ / α := by positivity
    have hρ0 : 0 ≤ rhoFdb⁻¹ := by positivity
    have hterm : ∀ q ∈ Leib S, ‖A q‖ ≤ B * K ^ S.length * N * ((q.1.length.factorial : ℝ) * q.2.length.factorial) := by
      intro q hq
      have hlen := Leib_len S q hq
      have h1 : ‖wordAct q.2 F‖ ≤ (Real.exp 1 * C₁ / α) ^ q.2.length * q.2.length.factorial * N :=
        (lem_wc_zero hF' hC q.2 hα hle hFd).2
      have h2 := norm_mulCL_le (sb_gT hB q.1) (wordAct q.2 F)
      have hp1 : rhoFdb⁻¹ ^ q.1.length * (Real.exp 1 * C₁ / α) ^ q.2.length ≤ K ^ S.length := by
        rw [← hlen, pow_add]
        gcongr
      have hf1 : (0 : ℝ) ≤ q.1.length.factorial := by positivity
      have hf2 : (0 : ℝ) ≤ q.2.length.factorial := by positivity
      calc ‖A q‖ ≤ wbd B q.1 * ‖wordAct q.2 F‖ := h2
        _ ≤ wbd B q.1 * ((Real.exp 1 * C₁ / α) ^ q.2.length * q.2.length.factorial * N) := by
            exact mul_le_mul_of_nonneg_left h1 (wbd_nonneg hB _)
        _ = B * (rhoFdb⁻¹ ^ q.1.length * (Real.exp 1 * C₁ / α) ^ q.2.length) * N
            * ((q.1.length.factorial : ℝ) * q.2.length.factorial) := by unfold wbd; ring
        _ ≤ B * K ^ S.length * N * ((q.1.length.factorial : ℝ) * q.2.length.factorial) := by gcongr
    have hsum := (norm_list_sum_le' (Leib S) A).trans (list_sum_le hterm)
    rw [List.sum_map_mul_left, Leib_sum, Nat.factorial_succ] at hsum
    push_cast at hsum
    calc ‖G‖ ≤ _ := hsum
      _ = _ := by ring

/-- **Lemma SC** (`lem:sc`): `‖X₀^β Z₁⋯Z_m a‖ ≤ B_β (m+1) m! (C₃/α)^m ‖e^{αΛ}X₀^β a‖`, `C₃ = max(eC₁, τ₀/ρ)`. -/
theorem lem_sc_main {τ₀ : ℝ} (hτ₀ : τ₀ < Real.pi / 2) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ β : ℝ, 0 ≤ β → ∃ B : ℝ, 0 ≤ B ∧ ∀ (S : List Bool) (α : ℝ), 0 < α → α ≤ τ₀ → ∀ (F : L2H')
      (hFd : F ∈ (expLambda α).domain), ∃ a : L2H',
        (a : UpperHalfPlane → ℂ) =ᵐ[volume] (fun z => ((hF (z : ℂ) ^ β : ℝ) : ℂ) * F z) ∧
        WordDom S a ∧ ∃ G : L2H',
          (G : UpperHalfPlane → ℂ) =ᵐ[volume] (fun z => ((hF (z : ℂ) ^ (-β) : ℝ) : ℂ) * wordAct S a z) ∧
          ‖G‖ ≤ B * (S.length + 1) * S.length.factorial * (max (Real.exp 1 * C₁) (τ₀ / rhoFdb) / α) ^ S.length
            * ‖expLambda α ⟨F, hFd⟩‖ := by
  obtain ⟨C₁, hC, hF'⟩ := lem_fc hτ₀
  refine ⟨C₁, hC, fun β hβ => ?_⟩
  obtain ⟨B, hB0, hB⟩ := fdb β
  refine ⟨B, hB0, fun S α hα hle F hFd => ?_⟩
  obtain ⟨hd, hG⟩ := lem_sc hF' hC hβ hB S hα hle hFd
  exact ⟨mulW hβ hB [] F, coe_mulCL (adm_word hβ hB []).sb F, hd, hG⟩

end final

end Qschubert
