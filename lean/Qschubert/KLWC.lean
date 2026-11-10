import Qschubert.KLFCY6

/-!
# Lemma WC: the unweighted Cauchy estimate for words

A word `S = [Z₁, …, Z_m]` (`true = X`, `false = Y`, the convention of `FdbWord`) acts by `wordAct S u = Z₁(⋯(Z_m u))`,
with `WordDom S u` recording that every intermediate vector lies in `Dom(-Δ)` (`wordAct` is junk otherwise).

`lem_wc` (`lem:wc`): for `0 ≤ α'' < α ≤ τ₀ < π/2`, `‖e^{α''Λ} Z₁⋯Z_m e^{-αΛ} v‖ ≤ (C₁m/(α - α''))^m ‖v‖ ≤
(eC₁/(α - α''))^m m! ‖v‖`. Proof as in the paper: equally spaced radii and `lem_fc`. The insertion
`e^{-r_iΛ}e^{r_iΛ}` is `exists_expDom_of_mem`: a vector of `Dom e^{aΛ}`, `a > 0`, is `e^{-aΛ} w` with `‖w‖ = ‖e^{aΛ}x‖`.
`lem_wc_dom` is the form used by `lem:sc` and `lem:wb` (`F ∈ Dom e^{αΛ}`).
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set
open scoped ENNReal

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- A letter on `Dom(-Δ)`: `true = X`, `false = Y`. -/
noncomputable def domZ (z : Bool) (u : negLapH.domain) : L2H' := if z then domX u else domY u

open Classical in
/-- `wordAct [Z₁, …, Z_m] u = Z₁(⋯(Z_m u))` (`0` if an intermediate vector leaves `Dom(-Δ)`; see `WordDom`). -/
noncomputable def wordAct : List Bool → L2H' → L2H'
  | [], u => u
  | z :: S, u => if h : wordAct S u ∈ negLapH.domain then domZ z ⟨wordAct S u, h⟩ else 0

/-- Every intermediate vector of the word lies in `Dom(-Δ)`. -/
def WordDom : List Bool → L2H' → Prop
  | [], _ => True
  | _ :: S, u => WordDom S u ∧ wordAct S u ∈ negLapH.domain

lemma wordAct_cons (z : Bool) (S : List Bool) {u : L2H'} (h : wordAct S u ∈ negLapH.domain) :
    wordAct (z :: S) u = domZ z ⟨wordAct S u, h⟩ := by
  simp only [wordAct, h, dif_pos]

/-- The multiplier of `e^{aΛ}`. -/
noncomputable def fExp (a s : ℝ) : ℂ := ((Real.exp (a * Real.sqrt s) : ℝ) : ℂ)

lemma measurable_fExp (a : ℝ) : Measurable (fExp a) :=
  Complex.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul Real.continuous_sqrt.measurable))

lemma fExp_mKL (a : ℝ) (p : ℝ × ℝ) : fExp a (mKL p) = ((Real.exp (a * LamK p.2) : ℝ) : ℂ) := rfl

/-- `‖e^{aΛ}x‖ = ‖f(m) · klU x‖`. -/
lemma norm_expLambda_eq {a : ℝ} {x : L2H'} (h : x ∈ (expLambda a).domain)
    (hm : MemLp (fun p => fExp a (mKL p) * (klU x : ℝ × ℝ → ℂ) p) 2 muU) :
    ‖expLambda a ⟨x, h⟩‖ = ‖hm.toLp _‖ := by
  have hn := norm_fc_sq (measurable_fExp a) (⟨x, h⟩ : (Physicslib4.Spectral.Unbounded.functionalCalculus
    negLapH_isSelfAdjoint (fExp a)).domain)
  change ‖expLambda a ⟨x, h⟩‖ ^ 2 = _ at hn
  have hsq : Integrable (fun p => ‖fExp a (mKL p) * (klU x : ℝ × ℝ → ℂ) p‖ ^ 2) muU :=
    (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hm
  have e1 : ‖expLambda a ⟨x, h⟩‖ ^ 2 = ∫ p, ‖fExp a (mKL p) * (klU x : ℝ × ℝ → ℂ) p‖ ^ 2 ∂muU := by
    rw [hn]; congr 1; funext p; rw [norm_mul, mul_pow]
  have h2 : ENNReal.ofReal (‖expLambda a ⟨x, h⟩‖ ^ 2) = ENNReal.ofReal (‖hm.toLp _‖ ^ 2) := by
    rw [e1, ofReal_integral_eq_lintegral_ofReal hsq (Eventually.of_forall fun p => sq_nonneg _),
      ← lintegral_enorm_sq_eq]
    refine lintegral_congr_ae ?_
    filter_upwards [hm.coeFn_toLp] with p hp
    rw [hp, ← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  have h3 := (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (sq_nonneg _)).1 h2
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h3

/-- **A vector of `Dom e^{aΛ}`, `a > 0`, is `e^{-aΛ}w` with `‖w‖ = ‖e^{aΛ}x‖`.** -/
theorem exists_expDom_of_mem {a : ℝ} (ha : 0 < a) {x : L2H'} (h : x ∈ (expLambda a).domain) :
    ∃ w : L2H', ‖w‖ = ‖expLambda a ⟨x, h⟩‖ ∧ x = ((expDom a ha w : negLapH.domain) : L2H') := by
  have hm := (mem_domain_fc_iff (measurable_fExp a) x).1 h
  set G := hm.toLp _
  set w := klUequiv.symm G
  have hw : klU w = G := klUequiv.apply_symm_apply G
  refine ⟨w, ?_, ?_⟩
  · rw [norm_expLambda_eq h hm]
    show ‖w‖ = ‖G‖
    rw [← hw, norm_klU]
  · apply klUequiv.injective
    show klU x = klU ((expCut a ha).J w)
    apply Lp.ext
    filter_upwards [klU_expCut ha w, hm.coeFn_toLp] with p h1 h2
    rw [h1, hw]
    change _ = _ * (G : ℝ × ℝ → ℂ) p
    rw [h2, fExp_mKL]
    have he : ((Real.exp (-(a * LamK p.2)) : ℝ) : ℂ) * ((Real.exp (a * LamK p.2) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]; simp
    linear_combination (-((klU x : ℝ × ℝ → ℂ) p)) * he

/-- `e^{-cΛ}v ∈ Dom e^{aΛ}` with norm `≤ ‖v‖` for `a ≤ c`. -/
theorem expDom_mem_dom {a c : ℝ} (hac : a ≤ c) (hc : 0 < c) (v : L2H') :
    ∃ h : ((expDom c hc v : negLapH.domain) : L2H') ∈ (expLambda a).domain, ‖expLambda a ⟨_, h⟩‖ ≤ ‖v‖ := by
  set x : L2H' := ((expDom c hc v : negLapH.domain) : L2H')
  have hG : (klU x : ℝ × ℝ → ℂ) =ᵐ[muU] fun p => ((Real.exp (-(c * LamK p.2)) : ℝ) : ℂ) * (klU v : ℝ × ℝ → ℂ) p :=
    klU_expCut hc v
  have hbound : ∀ᵐ p ∂muU, ‖fExp a (mKL p) * (klU x : ℝ × ℝ → ℂ) p‖ ≤ ‖(klU v : ℝ × ℝ → ℂ) p‖ := by
    filter_upwards [hG] with p hp
    rw [hp, fExp_mKL, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _), ← mul_assoc, ← Real.exp_add]
    refine mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.2 ?_)
    nlinarith [LamK_pos p.2]
  have hm : MemLp (fun p => fExp a (mKL p) * (klU x : ℝ × ℝ → ℂ) p) 2 muU :=
    (Lp.memLp (klU v)).of_le (((measurable_fExp a).comp measurable_mKL).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable _)) hbound
  have h : x ∈ (expLambda a).domain := (mem_domain_fc_iff (measurable_fExp a) x).2 hm
  refine ⟨h, ?_⟩
  rw [norm_expLambda_eq h hm, ← norm_klU v]
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [hbound, hm.coeFn_toLp] with p h1 h2
  rw [h2]; exact h1

section word

variable {τ₀ C₁ : ℝ}

/-- The hypothesis supplied by `lem_fc`. -/
def FCBound (τ₀ C₁ : ℝ) : Prop :=
  ∀ (α'' α' : ℝ) (h0 : 0 ≤ α'') (h12 : α'' < α'), α' ≤ τ₀ → ∀ v : L2H',
    (∃ h : domX (expDom α' (lt_of_le_of_lt h0 h12) v) ∈ (expLambda α'').domain,
      ‖expLambda α'' ⟨domX (expDom α' (lt_of_le_of_lt h0 h12) v), h⟩‖ ≤ C₁ / (α' - α'') * ‖v‖) ∧
    (∃ h : domY (expDom α' (lt_of_le_of_lt h0 h12) v) ∈ (expLambda α'').domain,
      ‖expLambda α'' ⟨domY (expDom α' (lt_of_le_of_lt h0 h12) v), h⟩‖ ≤ C₁ / (α' - α'') * ‖v‖)

lemma FCBound.letter (hF : FCBound τ₀ C₁) (z : Bool) (α'' α' : ℝ) (h0 : 0 ≤ α'') (h12 : α'' < α') (hle : α' ≤ τ₀)
    (v : L2H') :
    ∃ h : domZ z (expDom α' (lt_of_le_of_lt h0 h12) v) ∈ (expLambda α'').domain,
      ‖expLambda α'' ⟨domZ z (expDom α' (lt_of_le_of_lt h0 h12) v), h⟩‖ ≤ C₁ / (α' - α'') * ‖v‖ := by
  cases z with
  | true => simpa only [domZ, ite_true] using (hF α'' α' h0 h12 hle v).1
  | false => simpa only [domZ, Bool.false_eq_true, ite_false] using (hF α'' α' h0 h12 hle v).2

/-- **The induction on the word**: at radius `r > 0`, the word applied to `e^{-αΛ}v` is `e^{-rΛ}w`. -/
theorem word_step (hF : FCBound τ₀ C₁) (hC : 0 ≤ C₁) {α : ℝ} (hα : 0 < α) (hle : α ≤ τ₀) (v : L2H') (S : List Bool) :
    ∀ (r δ : ℝ) (hr : 0 < r), 0 < δ → r + S.length * δ = α →
      WordDom S ((expDom α hα v : negLapH.domain) : L2H') ∧
      ∃ w : L2H', wordAct S ((expDom α hα v : negLapH.domain) : L2H') = ((expDom r hr w : negLapH.domain) : L2H') ∧
        ‖w‖ ≤ (C₁ / δ) ^ S.length * ‖v‖ := by
  induction S with
  | nil =>
    intro r δ hr _ hrα
    have e : r = α := by simpa using hrα
    subst e
    exact ⟨trivial, v, rfl, by simp⟩
  | cons z S ih =>
    intro r δ hr hδ hrα
    simp only [List.length_cons] at hrα ⊢
    push_cast at hrα
    have hn : (0 : ℝ) ≤ S.length := Nat.cast_nonneg _
    have hr' : 0 < r + δ := by linarith
    obtain ⟨hdom, w', hw', hnw'⟩ := ih (r + δ) δ hr' hδ (by rw [← hrα]; ring)
    have hmem : wordAct S ((expDom α hα v : negLapH.domain) : L2H') ∈ negLapH.domain := by
      rw [hw']; exact (expDom (r + δ) hr' w').2
    refine ⟨⟨hdom, hmem⟩, ?_⟩
    have hsub : (⟨wordAct S ((expDom α hα v : negLapH.domain) : L2H'), hmem⟩ : negLapH.domain) = expDom (r + δ) hr' w' :=
      Subtype.ext hw'
    have hact : wordAct (z :: S) ((expDom α hα v : negLapH.domain) : L2H') = domZ z (expDom (r + δ) hr' w') := by
      rw [wordAct_cons z S hmem, hsub]
    have hle' : r + δ ≤ τ₀ := by nlinarith
    obtain ⟨h, hb⟩ := hF.letter z r (r + δ) hr.le (by linarith) hle' w'
    obtain ⟨w, hwn, hwe⟩ := exists_expDom_of_mem hr h
    refine ⟨w, hact.trans hwe, ?_⟩
    rw [hwn]
    have e : C₁ / (r + δ - r) = C₁ / δ := by congr 1; ring
    rw [e] at hb
    have hK : 0 ≤ C₁ / δ := by positivity
    calc _ ≤ C₁ / δ * ‖w'‖ := hb
      _ ≤ C₁ / δ * ((C₁ / δ) ^ S.length * ‖v‖) := by gcongr
      _ = (C₁ / δ) ^ (S.length + 1) * ‖v‖ := by ring

/-- The operator bound from `FCBound`. -/
theorem word_bound (hF : FCBound τ₀ C₁) (hC : 0 ≤ C₁) (S : List Bool) {α'' α : ℝ} (h0 : 0 ≤ α'') (h12 : α'' < α)
    (hle : α ≤ τ₀) (v : L2H') :
    WordDom S ((expDom α (lt_of_le_of_lt h0 h12) v : negLapH.domain) : L2H') ∧
    ∃ h : wordAct S ((expDom α (lt_of_le_of_lt h0 h12) v : negLapH.domain) : L2H') ∈ (expLambda α'').domain,
      ‖expLambda α'' ⟨_, h⟩‖ ≤ (C₁ * S.length / (α - α'')) ^ S.length * ‖v‖ := by
  have hα : 0 < α := lt_of_le_of_lt h0 h12
  have hγ : 0 < α - α'' := by linarith
  cases S with
  | nil =>
    obtain ⟨h, hb⟩ := expDom_mem_dom (a := α'') h12.le hα v
    refine ⟨trivial, h, ?_⟩
    simp only [List.length_nil, pow_zero, one_mul]
    exact hb
  | cons z S =>
    set m : ℕ := S.length + 1
    have hm : (0 : ℝ) < m := by simp only [m]; positivity
    set δ : ℝ := (α - α'') / m
    have hδ : 0 < δ := by positivity
    have hδm : (m : ℝ) * δ = α - α'' := by simp only [δ]; field_simp
    have hmc : (m : ℝ) = S.length + 1 := by simp only [m]; push_cast; ring
    have hr₁ : 0 < α'' + δ := by linarith
    obtain ⟨hdom, w', hw', hnw'⟩ := word_step hF hC hα hle v S (α'' + δ) δ hr₁ hδ (by nlinarith)
    have hmem : wordAct S ((expDom α hα v : negLapH.domain) : L2H') ∈ negLapH.domain := by
      rw [hw']; exact (expDom (α'' + δ) hr₁ w').2
    have hsub : (⟨wordAct S ((expDom α hα v : negLapH.domain) : L2H'), hmem⟩ : negLapH.domain) = expDom (α'' + δ) hr₁ w' :=
      Subtype.ext hw'
    have hact : wordAct (z :: S) ((expDom α hα v : negLapH.domain) : L2H') = domZ z (expDom (α'' + δ) hr₁ w') := by
      rw [wordAct_cons z S hmem, hsub]
    have hle' : α'' + δ ≤ τ₀ := by
      have : δ ≤ α - α'' := by
        rw [← hδm]; nlinarith [show (1 : ℝ) ≤ m by rw [hmc]; linarith [(Nat.cast_nonneg S.length : (0 : ℝ) ≤ S.length)]]
      linarith
    obtain ⟨h, hb⟩ := hF.letter z α'' (α'' + δ) h0 (by linarith) hle' w'
    refine ⟨⟨hdom, hmem⟩, hact ▸ h, ?_⟩
    have hN : ‖expLambda α'' ⟨wordAct (z :: S) ((expDom α hα v : negLapH.domain) : L2H'), hact ▸ h⟩‖
        = ‖expLambda α'' ⟨domZ z (expDom (α'' + δ) hr₁ w'), h⟩‖ := by
      congr 2
      exact Subtype.ext hact
    rw [hN]
    have e : C₁ / (α'' + δ - α'') = C₁ / δ := by congr 1; ring
    rw [e] at hb
    have hK : 0 ≤ C₁ / δ := by positivity
    have eK : C₁ * ((z :: S).length : ℝ) / (α - α'') = C₁ / δ := by
      have : ((z :: S).length : ℝ) = m := by simp [m]
      rw [this, ← hδm]; field_simp
    rw [eK]
    calc _ ≤ C₁ / δ * ‖w'‖ := hb
      _ ≤ C₁ / δ * ((C₁ / δ) ^ S.length * ‖v‖) := by gcongr
      _ = (C₁ / δ) ^ (z :: S).length * ‖v‖ := by simp only [List.length_cons]; ring

/-- `(C m/γ)^m ≤ (eC/γ)^m m!`. -/
lemma pow_le_exp_factorial {C γ : ℝ} (hC : 0 ≤ C) (hγ : 0 < γ) (m : ℕ) :
    (C * m / γ) ^ m ≤ (Real.exp 1 * C / γ) ^ m * m.factorial := by
  have h := Real.pow_div_factorial_le_exp (m : ℝ) (Nat.cast_nonneg m) m
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  rw [div_le_iff₀ hf] at h
  have hK : 0 ≤ (C / γ) ^ m := by positivity
  calc (C * m / γ) ^ m = (C / γ) ^ m * (m : ℝ) ^ m := by rw [← mul_pow]; congr 1; ring
    _ ≤ (C / γ) ^ m * (Real.exp m * m.factorial) := by gcongr
    _ = (Real.exp 1 * C / γ) ^ m * m.factorial := by
        rw [← Real.exp_one_pow, show Real.exp 1 * C / γ = Real.exp 1 * (C / γ) by ring, mul_pow]; ring

end word

/-- **Lemma WC** (`lem:wc`): for a word `S = [Z₁, …, Z_m]` and `0 ≤ α'' < α ≤ τ₀ < π/2`,
`‖e^{α''Λ} Z₁⋯Z_m e^{-αΛ} v‖ ≤ (C₁m/(α - α''))^m ‖v‖ ≤ (eC₁/(α - α''))^m m! ‖v‖`. -/
theorem lem_wc {τ₀ : ℝ} (hτ₀ : τ₀ < Real.pi / 2) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (S : List Bool) (α'' α : ℝ) (h0 : 0 ≤ α'') (h12 : α'' < α), α ≤ τ₀ → ∀ v : L2H',
      WordDom S ((expDom α (lt_of_le_of_lt h0 h12) v : negLapH.domain) : L2H') ∧
      (∃ h : wordAct S ((expDom α (lt_of_le_of_lt h0 h12) v : negLapH.domain) : L2H') ∈ (expLambda α'').domain,
        ‖expLambda α'' ⟨_, h⟩‖ ≤ (C₁ * S.length / (α - α'')) ^ S.length * ‖v‖) ∧
      (C₁ * S.length / (α - α'')) ^ S.length ≤ (Real.exp 1 * C₁ / (α - α'')) ^ S.length * S.length.factorial := by
  obtain ⟨C₁, hC, hF⟩ := lem_fc hτ₀
  refine ⟨C₁, hC, fun S α'' α h0 h12 hle v => ?_⟩
  obtain ⟨hd, hb⟩ := word_bound hF hC S h0 h12 hle v
  exact ⟨hd, hb, pow_le_exp_factorial hC (by linarith) _⟩

/-- **Lemma WC for `F ∈ Dom e^{αΛ}`** (the form used by `lem:sc` and `lem:wb`). -/
theorem lem_wc_dom {τ₀ C₁ : ℝ} (hF : FCBound τ₀ C₁) (hC : 0 ≤ C₁) (S : List Bool) {α'' α : ℝ} (h0 : 0 ≤ α'')
    (h12 : α'' < α) (hle : α ≤ τ₀) {F : L2H'} (hFd : F ∈ (expLambda α).domain) :
    WordDom S F ∧ ∃ h : wordAct S F ∈ (expLambda α'').domain,
      ‖expLambda α'' ⟨_, h⟩‖ ≤ (C₁ * S.length / (α - α'')) ^ S.length * ‖expLambda α ⟨F, hFd⟩‖ := by
  have hα : 0 < α := lt_of_le_of_lt h0 h12
  obtain ⟨w, hw, hFe⟩ := exists_expDom_of_mem hα hFd
  rw [← hw]
  have hb := word_bound hF hC S h0 h12 hle w
  rw [← hFe] at hb
  exact hb

/-- **Lemma WC at `α'' = 0`**, as used in the proof of `lem:sc` (dd_appendix.tex:270):
`‖Z₁⋯Z_m F‖ ≤ (eC₁/α)^m m! ‖e^{αΛ}F‖`. -/
theorem lem_wc_zero {τ₀ C₁ : ℝ} (hF : FCBound τ₀ C₁) (hC : 0 ≤ C₁) (S : List Bool) {α : ℝ} (hα : 0 < α)
    (hle : α ≤ τ₀) {F : L2H'} (hFd : F ∈ (expLambda α).domain) :
    WordDom S F ∧ ‖wordAct S F‖ ≤ (Real.exp 1 * C₁ / α) ^ S.length * S.length.factorial * ‖expLambda α ⟨F, hFd⟩‖ := by
  obtain ⟨hd, h, hb⟩ := lem_wc_dom hF hC S le_rfl hα hle hFd
  refine ⟨hd, ?_⟩
  rw [expLambda_zero_apply _ h, sub_zero] at hb
  refine hb.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact pow_le_exp_factorial hC hα _

end Qschubert
