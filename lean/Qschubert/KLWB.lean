import Qschubert.KLSC

/-!
# Lemma WB: bounds for `b'(s)`

`b'(s) = Δ_φ(s₁)^N Δ(s₁)⋯Δ(s_{K+1}) a` is a word polynomial in `X, Y` applied to `a` (paper (D4)).

* `WP`: word polynomials `Σ c_i Z_{w_i}`; `polyAct P a = Σ c_i wordAct w_i a`; `mulP` is their product, and
  `polyAct_mulP`: `polyAct P (polyAct Q a) = polyAct (mulP P Q) a` when all words act on `a`.
* `deltaP s = e^{-2s}X² + Y² - Y`, which is `lapTbar s` on vectors on which all words act (`lapTbar_eq_polyAct`);
  `deltaPhiP ħ s = Δ(s) - 2iħ⁻¹Y + ħ⁻²(-1 + iħ)`; `bP ħ N s₁ ss = Δ_φ(s₁)^N ∏_{s ∈ ss} Δ(s)`.
* `lem_wb_w` (WB-w) and `lem_wb_u` (WB-u).
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set
open scoped ENNReal ContDiff

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- Word polynomials `Σ c_i Z_{w_i}`. -/
abbrev WP := List (ℂ × List Bool)

/-- `Σ c_i Z_{w_i} u`. -/
noncomputable def polyAct (P : WP) (u : L2H') : L2H' := (P.map fun t => t.1 • wordAct t.2 u).sum

/-- The product of word polynomials. -/
def mulP (P Q : WP) : WP := P.flatMap fun p => Q.map fun q => (p.1 * q.1, p.2 ++ q.2)

/-- The unit. -/
def oneP : WP := [(1, [])]

/-- Powers. -/
def powWP (P : WP) : ℕ → WP
  | 0 => oneP
  | n + 1 => mulP P (powWP P n)

/-- `Z_J · P`. -/
def leftW (J : List Bool) (P : WP) : WP := P.map fun t => (t.1, J ++ t.2)

/-- All words act on `u`. -/
def AllWords (u : L2H') : Prop := ∀ S, WordDom S u

lemma polyAct_nil (u : L2H') : polyAct [] u = 0 := rfl

lemma polyAct_cons (t : ℂ × List Bool) (P : WP) (u : L2H') : polyAct (t :: P) u = t.1 • wordAct t.2 u + polyAct P u := by
  simp [polyAct]

lemma polyAct_append (P Q : WP) (u : L2H') : polyAct (P ++ Q) u = polyAct P u + polyAct Q u := by
  simp [polyAct, List.map_append, List.sum_append]

lemma domZ_smul (z : Bool) (c : ℂ) (u : negLapH.domain) : domZ z (c • u) = c • domZ z u := by
  have e : liftDom (c • u) = c • liftDom u := by
    unfold liftDom
    rw [Submodule.coe_smul, LinearPMap.map_smul, ← smul_add, map_smul]
  cases z <;> simp only [domZ, Bool.false_eq_true, ite_false, ite_true, domX, domY, e, map_smul]

section act

variable {a : L2H'} (hA : AllWords a)
include hA

lemma AllWords.mem (S : List Bool) : wordAct S a ∈ negLapH.domain := (hA (true :: S)).2

/-- **Words on a polynomial applied to `a`.** -/
theorem poly_words (P : WP) (S : List Bool) :
    WordDom S (polyAct P a) ∧ wordAct S (polyAct P a) = polyAct (leftW S P) a := by
  induction S with
  | nil =>
    refine ⟨trivial, ?_⟩
    simp [wordAct, leftW, polyAct, List.map_map, Function.comp_def]
  | cons z S ih =>
    obtain ⟨hd, hs⟩ := ih
    have hf : ∀ t : ℂ × List Bool, t.1 • wordAct t.2 a ∈ negLapH.domain := fun t =>
      Submodule.smul_mem _ _ (AllWords.mem hA t.2)
    have hmem : polyAct (leftW S P) a ∈ negLapH.domain :=
      list_sum_mem fun x hx => by
        obtain ⟨t, _, rfl⟩ := List.mem_map.1 hx
        exact hf t
    have hmem' : wordAct S (polyAct P a) ∈ negLapH.domain := hs ▸ hmem
    refine ⟨⟨hd, hmem'⟩, ?_⟩
    rw [wordAct_cons z S hmem']
    have hsub : (⟨wordAct S (polyAct P a), hmem'⟩ : negLapH.domain) = ⟨polyAct (leftW S P) a, hmem⟩ := Subtype.ext hs
    rw [hsub]
    have h1 := domZ_list_sum z (leftW S P) (fun t : ℂ × List Bool => t.1 • wordAct t.2 a) hf hmem
    have h2 : (⟨polyAct (leftW S P) a, hmem⟩ : negLapH.domain)
        = ⟨((leftW S P).map fun t : ℂ × List Bool => t.1 • wordAct t.2 a).sum, hmem⟩ := rfl
    rw [h2, h1]
    have hstep : ∀ t : ℂ × List Bool, domZ z ⟨t.1 • wordAct t.2 a, hf t⟩ = t.1 • wordAct (z :: t.2) a := by
      intro t
      rw [show (⟨t.1 • wordAct t.2 a, hf t⟩ : negLapH.domain) = t.1 • ⟨wordAct t.2 a, AllWords.mem hA t.2⟩ from rfl,
        domZ_smul, wordAct_cons z t.2 (AllWords.mem hA t.2)]
    simp only [hstep, leftW, polyAct, List.map_map, Function.comp_def, List.cons_append]

lemma allWords_polyAct (P : WP) : AllWords (polyAct P a) := fun S => (poly_words hA P S).1

lemma polyAct_map_mul (c : ℂ) (J : List Bool) (Q : WP) :
    polyAct (Q.map fun q => (c * q.1, J ++ q.2)) a = c • polyAct (leftW J Q) a := by
  induction Q with
  | nil => simp [polyAct, leftW]
  | cons q Q ih =>
    simp only [List.map_cons, polyAct_cons, leftW, smul_add, smul_smul] at ih ⊢
    rw [ih]

/-- **Composition of word polynomials.** -/
theorem polyAct_mulP (P Q : WP) : polyAct P (polyAct Q a) = polyAct (mulP P Q) a := by
  induction P with
  | nil => simp [polyAct, mulP]
  | cons p P ih =>
    rw [polyAct_cons, (poly_words hA Q p.2).2, ih]
    show _ = polyAct ((Q.map fun q => (p.1 * q.1, p.2 ++ q.2)) ++ mulP P Q) a
    rw [polyAct_append, polyAct_map_mul hA]

end act

/-! ### `Δ(s)`, `Δ_φ(s)` and `b'(s)` -/

/-- `Δ(s) = e^{-2s}X² + Y² - Y`. -/
noncomputable def deltaP (s : ℝ) : WP :=
  [(((Real.exp (-2 * s) : ℝ) : ℂ), [true, true]), (1, [false, false]), (-1, [false])]

/-- `Δ_φ(s) = Δ(s) - 2iħ⁻¹Y + ħ⁻²(-1 + iħ)` (`ħ²Δ_φ(s) = ħ²Δ(s) - 2iħY - 1 + iħ`). -/
noncomputable def deltaPhiP (ħ s : ℝ) : WP :=
  deltaP s ++ [(-(2 * Complex.I) / ħ, [false]), ((-1 + Complex.I * ħ) / (ħ : ℂ) ^ 2, [])]

/-- `∏_{s ∈ ss} Δ(s)`. -/
noncomputable def deltaProd : List ℝ → WP
  | [] => oneP
  | s :: r => mulP (deltaP s) (deltaProd r)

/-- `b'(s)` as a word polynomial: `Δ_φ(s₁)^N ∏_{s ∈ ss} Δ(s)`. -/
noncomputable def bP (ħ : ℝ) (N : ℕ) (s₁ : ℝ) (ss : List ℝ) : WP := mulP (powWP (deltaPhiP ħ s₁) N) (deltaProd ss)

/-! ### `Δ(s)` is `lapTbar s` -/

/-- `Y† = 1 - Y` on test functions. -/
noncomputable def Yd (P : testFn) : testFn := P - vfTest Complex.I P

lemma inner_Yd (P F : testFn) : inner ℂ (toL2 P) (toL2 (vfTest Complex.I F)) = inner ℂ (toL2 (Yd P)) (toL2 F) := by
  have h := inner_vf_left Complex.I P F
  rw [Yd, map_sub, inner_sub_left, h]
  simp

lemma inner_Yd_dom (P : testFn) (u : negLapH.domain) : inner ℂ (toL2 P) (domY u) = inner ℂ (toL2 (Yd P)) (u : L2H') := by
  have h := inner_Y_dom P u
  rw [Yd, map_sub, inner_sub_left, h]
  ring

lemma inner_psiX (P : testFn) (p : graphBar) :
    inner ℂ (toL2 P) (psiX p) = inner ℂ (toL2 (vfTest 1 (vfTest 1 P))) (p : L2H' × L2H').1 := by
  refine DenseRange.induction_on denseRange_graphIncl p ?_ fun q => ?_
  · exact isClosed_eq (continuous_const.inner psiX.continuous)
      (continuous_const.inner (continuous_fst.comp continuous_subtype_val))
  · rw [psiX_incl]
    show inner ℂ (toL2 P) (toL2 (xxTest (testOf q))) = inner ℂ _ (q : L2H' × L2H').1
    rw [← toL2_testOf, xxTest_eq]
    have h1 := inner_vf_left 1 (vfTest 1 P) (testOf q)
    have h2 := inner_vf_left 1 P (vfTest 1 (testOf q))
    simp only [Complex.one_im, Complex.ofReal_zero, zero_mul, add_zero] at h1 h2
    rw [h1, h2, neg_neg]

lemma inner_psiY (P : testFn) (p : graphBar) :
    inner ℂ (toL2 P) (psiY p) = inner ℂ (toL2 (Yd (Yd P)) - toL2 (Yd P)) (p : L2H' × L2H').1 := by
  refine DenseRange.induction_on denseRange_graphIncl p ?_ fun q => ?_
  · exact isClosed_eq (continuous_const.inner psiY.continuous)
      (continuous_const.inner (continuous_fst.comp continuous_subtype_val))
  · rw [psiY_incl]
    show inner ℂ (toL2 P) (toL2 (yyTest (testOf q))) = inner ℂ _ (q : L2H' × L2H').1
    rw [← toL2_testOf, yyTest_eq, map_sub, inner_sub_right, inner_sub_left, inner_Yd, inner_Yd, inner_Yd]

/-- **`lapTbar s` is the word polynomial `Δ(s)`** on vectors on which all words act. -/
theorem lapTbar_eq_polyAct (s : ℝ) (u : negLapH.domain) (hA : AllWords (u : L2H')) :
    lapTbar s ⟨((u : L2H'), negLapH u), mem_graphBar_negLapH u⟩ = polyAct (deltaP s) (u : L2H') := by
  have hu : wordAct ([] : List Bool) (u : L2H') ∈ negLapH.domain := u.2
  have hXm : wordAct [true] (u : L2H') ∈ negLapH.domain := AllWords.mem hA [true]
  have hYm : wordAct [false] (u : L2H') ∈ negLapH.domain := AllWords.mem hA [false]
  have eX : wordAct [true] (u : L2H') = domX u := by
    rw [wordAct_cons true [] hu]; simp only [domZ, ite_true]; rfl
  have eY : wordAct [false] (u : L2H') = domY u := by
    rw [wordAct_cons false [] hu]; simp only [domZ, Bool.false_eq_true, ite_false]; rfl
  have hX : domX u ∈ negLapH.domain := eX ▸ hXm
  have hY : domY u ∈ negLapH.domain := eY ▸ hYm
  have eXX : wordAct [true, true] (u : L2H') = domX ⟨domX u, hX⟩ := by
    rw [wordAct_cons true [true] hXm]; simp only [domZ, ite_true]; congr 1; exact Subtype.ext eX
  have eYY : wordAct [false, false] (u : L2H') = domY ⟨domY u, hY⟩ := by
    rw [wordAct_cons false [false] hYm]; simp only [domZ, Bool.false_eq_true, ite_false]; congr 1; exact Subtype.ext eY
  set p : graphBar := ⟨((u : L2H'), negLapH u), mem_graphBar_negLapH u⟩
  have hpX : psiX p = domX ⟨domX u, hX⟩ := by
    refine ext_inner_left ℂ fun w => ?_
    refine DenseRange.induction_on denseRange_toL2 w ?_ fun P => ?_
    · exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
    · rw [inner_psiX]
      have h1 := inner_X_dom (vfTest 1 P) u
      have h2 := inner_X_dom P ⟨domX u, hX⟩
      change inner ℂ (toL2 (vfTest 1 P)) (domX u) = _ at h2
      show inner ℂ (toL2 (vfTest 1 (vfTest 1 P))) (u : L2H') = _
      rw [h1, h2, neg_neg]
  have hpY : psiY p = domY ⟨domY u, hY⟩ - domY u := by
    refine ext_inner_left ℂ fun w => ?_
    refine DenseRange.induction_on denseRange_toL2 w ?_ fun P => ?_
    · exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
    · rw [inner_psiY, inner_sub_right, inner_sub_left]
      have h1 := inner_Yd_dom (Yd P) u
      have h2 := inner_Yd_dom P ⟨domY u, hY⟩
      have h3 := inner_Yd_dom P u
      change inner ℂ (toL2 P) (domY ⟨domY u, hY⟩) = inner ℂ (toL2 (Yd P)) (domY u) at h2
      show inner ℂ (toL2 (Yd (Yd P))) (u : L2H') - inner ℂ (toL2 (Yd P)) (u : L2H') = _
      rw [h2, h3, h1]
  rw [lapTbar, hpX, hpY, deltaP, polyAct_cons, polyAct_cons, polyAct_cons, polyAct_nil, eXX, eYY, eY]
  simp only [one_smul, neg_smul, add_zero]
  abel

/-! ### Invariants of the expansion -/

lemma mem_mulP {P Q : WP} {t : ℂ × List Bool} (h : t ∈ mulP P Q) :
    ∃ p ∈ P, ∃ q ∈ Q, t = (p.1 * q.1, p.2 ++ q.2) := by
  simp only [mulP, List.mem_flatMap, List.mem_map] at h
  obtain ⟨p, hp, q, hq, rfl⟩ := h
  exact ⟨p, hp, q, hq, rfl⟩

lemma length_mulP (P Q : WP) : (mulP P Q).length = P.length * Q.length := by
  induction P with
  | nil => simp [mulP]
  | cons p P ih =>
    have e : mulP (p :: P) Q = (Q.map fun q => (p.1 * q.1, p.2 ++ q.2)) ++ mulP P Q := rfl
    rw [e, List.length_append, List.length_map, ih, List.length_cons]; ring

lemma deltaP_inv {s : ℝ} (hs : 0 ≤ s) : ∀ t ∈ deltaP s, ‖t.1‖ ≤ 1 ∧ t.2.length ≤ 2 := by
  intro t ht
  simp only [deltaP, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · refine ⟨?_, by simp⟩
    show ‖((Real.exp (-2 * s) : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    linarith
  · exact ⟨by simp, by simp⟩
  · exact ⟨by simp, by simp⟩

lemma deltaPhiP_inv {ħ s : ℝ} (hħ : 0 < ħ) (hħ1 : ħ ≤ 1) (hs : 0 ≤ s) :
    ∀ t ∈ deltaPhiP ħ s, ‖t.1‖ * ħ ^ 2 ≤ 2 * ħ ^ t.2.length ∧ t.2.length ≤ 2 := by
  intro t ht
  rw [deltaPhiP, List.mem_append] at ht
  have hħc : (ħ : ℂ) ≠ 0 := by exact_mod_cast hħ.ne'
  rcases ht with ht | ht
  · obtain ⟨h1, h2⟩ := deltaP_inv hs t ht
    refine ⟨?_, h2⟩
    have hp : ħ ^ 2 ≤ ħ ^ t.2.length := pow_le_pow_of_le_one hħ.le hħ1 h2
    have hp0 : 0 ≤ ħ ^ t.2.length := by positivity
    have h3 : ‖t.1‖ * ħ ^ 2 ≤ 1 * ħ ^ 2 := by gcongr
    linarith
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · refine ⟨?_, by simp⟩
      show ‖-(2 * Complex.I) / (ħ : ℂ)‖ * ħ ^ 2 ≤ 2 * ħ ^ ([false] : List Bool).length
      rw [norm_div, norm_neg, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hħ]
      simp only [List.length_cons, List.length_nil, zero_add, pow_one, Complex.norm_ofNat, mul_one]
      apply le_of_eq; field_simp
    · refine ⟨?_, by simp⟩
      show ‖(-1 + Complex.I * ħ) / (ħ : ℂ) ^ 2‖ * ħ ^ 2 ≤ 2 * ħ ^ ([] : List Bool).length
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hħ]
      simp only [List.length_nil, pow_zero, mul_one]
      have hn : ‖(-1 + Complex.I * ħ : ℂ)‖ ≤ 2 := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_neg, norm_one, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hħ]
        linarith
      rw [div_mul_cancel₀ _ (by positivity)]
      exact hn

lemma length_deltaP (s : ℝ) : (deltaP s).length = 3 := rfl
lemma length_deltaPhiP (ħ s : ℝ) : (deltaPhiP ħ s).length = 5 := rfl

lemma powWP_inv {ħ s : ℝ} (hħ : 0 < ħ) (hħ1 : ħ ≤ 1) (hs : 0 ≤ s) (N : ℕ) :
    (∀ t ∈ powWP (deltaPhiP ħ s) N, ‖t.1‖ * ħ ^ (2 * N) ≤ 2 ^ N * ħ ^ t.2.length ∧ t.2.length ≤ 2 * N) ∧
      (powWP (deltaPhiP ħ s) N).length = 5 ^ N := by
  induction N with
  | zero =>
    refine ⟨fun t ht => ?_, rfl⟩
    simp only [powWP, oneP, List.mem_singleton] at ht
    subst ht
    simp
  | succ N ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨fun t ht => ?_, ?_⟩
    · obtain ⟨p, hp, q, hq, rfl⟩ := mem_mulP ht
      obtain ⟨a1, a2⟩ := deltaPhiP_inv hħ hħ1 hs p hp
      obtain ⟨b1, b2⟩ := h1 q hq
      refine ⟨?_, ?_⟩
      · simp only [List.length_append, norm_mul]
        calc ‖p.1‖ * ‖q.1‖ * ħ ^ (2 * (N + 1)) = (‖p.1‖ * ħ ^ 2) * (‖q.1‖ * ħ ^ (2 * N)) := by ring
          _ ≤ (2 * ħ ^ p.2.length) * (2 ^ N * ħ ^ q.2.length) := by gcongr
          _ = _ := by ring
      · simp only [List.length_append]; omega
    · show (mulP _ _).length = _
      rw [length_mulP, length_deltaPhiP, h2]; ring

lemma deltaProd_inv (ss : List ℝ) (hss : ∀ s ∈ ss, 0 ≤ s) :
    (∀ t ∈ deltaProd ss, ‖t.1‖ ≤ 1 ∧ t.2.length ≤ 2 * ss.length) ∧ (deltaProd ss).length = 3 ^ ss.length := by
  induction ss with
  | nil =>
    refine ⟨fun t ht => ?_, rfl⟩
    simp only [deltaProd, oneP, List.mem_singleton] at ht
    subst ht
    simp
  | cons s r ih =>
    obtain ⟨h1, h2⟩ := ih fun x hx => hss x (by simp [hx])
    refine ⟨fun t ht => ?_, ?_⟩
    · obtain ⟨p, hp, q, hq, rfl⟩ := mem_mulP ht
      obtain ⟨a1, a2⟩ := deltaP_inv (hss s (by simp)) p hp
      obtain ⟨b1, b2⟩ := h1 q hq
      refine ⟨?_, ?_⟩
      · simp only [norm_mul]
        calc ‖p.1‖ * ‖q.1‖ ≤ 1 * 1 := by gcongr
          _ = 1 := one_mul 1
      · simp only [List.length_append, List.length_cons]; omega
    · show (mulP _ _).length = _
      rw [length_mulP, length_deltaP, h2, List.length_cons]; ring

lemma bP_inv {ħ s₁ : ℝ} (hħ : 0 < ħ) (hħ1 : ħ ≤ 1) (hs₁ : 0 ≤ s₁) (N : ℕ) (ss : List ℝ) (hss : ∀ s ∈ ss, 0 ≤ s) :
    (∀ t ∈ bP ħ N s₁ ss, ∃ ℓ r : ℕ, t.2.length = ℓ + r ∧ ℓ ≤ 2 * N ∧ r ≤ 2 * ss.length ∧
        ‖t.1‖ * ħ ^ (2 * N) ≤ 2 ^ N * ħ ^ ℓ) ∧
      (bP ħ N s₁ ss).length = 5 ^ N * 3 ^ ss.length := by
  obtain ⟨h1, h2⟩ := powWP_inv hħ hħ1 hs₁ N
  obtain ⟨g1, g2⟩ := deltaProd_inv ss hss
  refine ⟨fun t ht => ?_, ?_⟩
  · obtain ⟨p, hp, q, hq, rfl⟩ := mem_mulP ht
    obtain ⟨a1, a2⟩ := h1 p hp
    obtain ⟨b1, b2⟩ := g1 q hq
    refine ⟨p.2.length, q.2.length, by simp, a2, b2, ?_⟩
    simp only [norm_mul]
    calc ‖p.1‖ * ‖q.1‖ * ħ ^ (2 * N) = (‖p.1‖ * ħ ^ (2 * N)) * ‖q.1‖ := by ring
      _ ≤ (2 ^ N * ħ ^ p.2.length) * 1 := by gcongr
      _ = _ := mul_one _
  · show (mulP _ _).length = _
    rw [length_mulP, h2, g2]

/-! ### The scalar inequality -/

lemma sca {ℓ L' A N : ℕ} {K₃ α ħ : ℝ} (hℓ : ℓ ≤ 2 * N) (hL : L' ≤ ℓ + A) (hK : 1 ≤ K₃) (hα : 0 < α) (hα1 : α ≤ 1)
    (hħ : 0 < ħ) (hħ1 : ħ ≤ 1) :
    ((L' : ℝ) + 1) * L'.factorial * (K₃ / α) ^ L' * ħ ^ ℓ
      ≤ (4 * K₃) ^ (2 * N + A) * (2 * N).factorial * A.factorial * (α⁻¹) ^ A * (α⁻¹) ^ (2 * N) := by
  set L := ℓ + A with hLdef
  have hKpos : 0 < K₃ := by linarith
  have hKα : 1 ≤ K₃ / α := by rw [le_div_iff₀ hα]; linarith
  have hαi : 1 ≤ α⁻¹ := (one_le_inv₀ hα).2 hα1
  have h1 : (L' : ℝ) + 1 ≤ (2 : ℝ) ^ L := by
    have h := Nat.lt_two_pow_self (n := L)
    have h' : L' + 1 ≤ 2 ^ L := by omega
    exact_mod_cast h'
  have h2 : (L'.factorial : ℝ) ≤ 2 ^ L * ℓ.factorial * A.factorial := by
    have e := Nat.add_choose_mul_factorial_mul_factorial ℓ A
    have hc : (ℓ + A).choose A ≤ 2 ^ (ℓ + A) := Nat.choose_le_two_pow _ _
    have hf : L'.factorial ≤ 2 ^ L * ℓ.factorial * A.factorial := by
      calc L'.factorial ≤ L.factorial := Nat.factorial_le hL
        _ = (ℓ + A).choose A * ℓ.factorial * A.factorial := e.symm
        _ ≤ 2 ^ L * ℓ.factorial * A.factorial := by gcongr
    exact_mod_cast hf
  have h3 : (K₃ / α) ^ L' ≤ K₃ ^ L * (α⁻¹) ^ ℓ * (α⁻¹) ^ A := by
    calc (K₃ / α) ^ L' ≤ (K₃ / α) ^ L := pow_le_pow_right₀ hKα hL
      _ = K₃ ^ L * (α⁻¹) ^ ℓ * (α⁻¹) ^ A := by
          rw [div_eq_mul_inv, mul_pow, hLdef, pow_add (α⁻¹)]; ring
  have h4 : ħ ^ ℓ ≤ 1 := pow_le_one₀ hħ.le hħ1
  have h5 : (ℓ.factorial : ℝ) ≤ (2 * N).factorial := by exact_mod_cast Nat.factorial_le hℓ
  have h6 : (α⁻¹) ^ ℓ ≤ (α⁻¹) ^ (2 * N) := pow_le_pow_right₀ hαi hℓ
  have h7 : (4 * K₃) ^ L ≤ (4 * K₃) ^ (2 * N + A) := pow_le_pow_right₀ (by linarith) (by omega)
  have hA0 : (0 : ℝ) ≤ A.factorial := by positivity
  have hl0 : (0 : ℝ) ≤ ℓ.factorial := by positivity
  have hi0 : 0 ≤ α⁻¹ := by positivity
  calc ((L' : ℝ) + 1) * L'.factorial * (K₃ / α) ^ L' * ħ ^ ℓ
      ≤ (2 : ℝ) ^ L * (2 ^ L * ℓ.factorial * A.factorial) * (K₃ ^ L * (α⁻¹) ^ ℓ * (α⁻¹) ^ A) * 1 := by gcongr
    _ = (4 * K₃) ^ L * ℓ.factorial * A.factorial * (α⁻¹) ^ A * (α⁻¹) ^ ℓ := by
        rw [mul_pow, show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]; ring
    _ ≤ (4 * K₃) ^ (2 * N + A) * (2 * N).factorial * A.factorial * (α⁻¹) ^ A * (α⁻¹) ^ (2 * N) := by gcongr

/-- The constant of `lem:wb`. -/
noncomputable def C4 (K₃ : ℝ) : ℝ := 30 * (4 * K₃) ^ 2

lemma c4_bound {K : ℝ} (hK : 1 ≤ K) (N sl n : ℕ) :
    (5 : ℝ) ^ N * 3 ^ sl * 2 ^ N * (4 * K) ^ (2 * N + (n + 2 * sl)) ≤ C4 K ^ (N + sl + n) := by
  have h4 : (1 : ℝ) ≤ 4 * K := by linarith
  have e : C4 K ^ (N + sl + n) = 30 ^ N * 30 ^ sl * 30 ^ n * (4 * K) ^ (2 * N + 2 * sl + 2 * n) := by
    unfold C4
    rw [mul_pow, ← pow_mul, pow_add, pow_add]
    ring_nf
  rw [e]
  have a1 : (5 : ℝ) ^ N * 2 ^ N ≤ 30 ^ N := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) N
  have a2 : (3 : ℝ) ^ sl ≤ 30 ^ sl := pow_le_pow_left₀ (by norm_num) (by norm_num) sl
  have a3 : (1 : ℝ) ≤ 30 ^ n := one_le_pow₀ (by norm_num)
  have a4 : (4 * K) ^ (2 * N + (n + 2 * sl)) ≤ (4 * K) ^ (2 * N + 2 * sl + 2 * n) := pow_le_pow_right₀ h4 (by omega)
  calc (5 : ℝ) ^ N * 3 ^ sl * 2 ^ N * (4 * K) ^ (2 * N + (n + 2 * sl))
      = ((5 : ℝ) ^ N * 2 ^ N) * 3 ^ sl * 1 * (4 * K) ^ (2 * N + (n + 2 * sl)) := by ring
    _ ≤ 30 ^ N * 30 ^ sl * 30 ^ n * (4 * K) ^ (2 * N + 2 * sl + 2 * n) := by gcongr

/-- The base constant: `K₃ ≥ 1`, `K₃ ≥ 4eC₁`, `K₃ ≥ τ₀/ρ`. -/
noncomputable def K3c (τ₀ C₁ : ℝ) : ℝ := max 1 (max (4 * Real.exp 1 * C₁) (τ₀ / rhoFdb))

lemma one_le_K3c (τ₀ C₁ : ℝ) : 1 ≤ K3c τ₀ C₁ := le_max_left _ _

lemma le_K3c_exp {τ₀ C₁ : ℝ} : 4 * Real.exp 1 * C₁ ≤ K3c τ₀ C₁ := (le_max_left _ _).trans (le_max_right _ _)

lemma le_K3c_tau {τ₀ C₁ : ℝ} : τ₀ / rhoFdb ≤ K3c τ₀ C₁ := (le_max_right _ _).trans (le_max_right _ _)

section bounds

variable {τ₀ C₁ : ℝ}

/-- The per-term coefficient estimate. -/
lemma coeff_le {c : ℂ} {ħ : ℝ} {N ℓ : ℕ} (hħ : 0 < ħ) (h : ‖c‖ * ħ ^ (2 * N) ≤ 2 ^ N * ħ ^ ℓ) :
    ‖c‖ ≤ 2 ^ N * ħ ^ ℓ * (ħ⁻¹) ^ (2 * N) := by
  have hp : 0 < ħ ^ (2 * N) := by positivity
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hp]
  exact h

/-- **(WB-w)**. -/
theorem lem_wb_w {β B : ℝ} (hF' : FCBound τ₀ C₁) (hC : 0 ≤ C₁) (hβ : 0 ≤ β) (hB : FdbB β B) (hB0 : 0 ≤ B)
    {ħ α : ℝ} (hħ : 0 < ħ) (hħ1 : ħ ≤ 1) (hα : 0 < α) (hα1 : α ≤ 1) (hατ : α ≤ τ₀) (N : ℕ) {s₁ : ℝ} (hs₁ : 0 ≤ s₁)
    (ss : List ℝ) (hss : ∀ s ∈ ss, 0 ≤ s) (J : List Bool) {n : ℕ} (hJ : J.length ≤ n) {F : L2H'}
    (hFd : F ∈ (expLambda α).domain) :
    WordDom J (polyAct (bP ħ N s₁ ss) (mulW hβ hB [] F)) ∧ ∃ G : L2H',
      (G : UpperHalfPlane → ℂ) =ᵐ[volume]
        (fun z => ((hF (z : ℂ) ^ (-β) : ℝ) : ℂ) * wordAct J (polyAct (bP ħ N s₁ ss) (mulW hβ hB [] F)) z) ∧
      ‖G‖ ≤ B * C4 (K3c τ₀ C₁) ^ (N + ss.length + n) * (2 * N).factorial * (n + 2 * ss.length).factorial
        * (α⁻¹) ^ (n + 2 * ss.length) * ((α * ħ)⁻¹) ^ (2 * N) * ‖expLambda α ⟨F, hFd⟩‖ := by
  set a := mulW hβ hB [] F
  set P := bP ħ N s₁ ss
  set K₃ := K3c τ₀ C₁
  have hFw : ∀ U, WordDom U F := fun U => (lem_wc_zero hF' hC U hα hατ hFd).1
  have hA : AllWords a := fun S => (word_leibniz hβ hB hFw S).1
  obtain ⟨hd, hs⟩ := poly_words hA P J
  refine ⟨hd, ?_⟩
  have hex : ∀ S : List Bool, ∃ G : L2H',
      (G : UpperHalfPlane → ℂ) =ᵐ[volume] (fun z => ((hF (z : ℂ) ^ (-β) : ℝ) : ℂ) * wordAct S a z) ∧
      ‖G‖ ≤ B * (S.length + 1) * S.length.factorial * (max (Real.exp 1 * C₁) (τ₀ / rhoFdb) / α) ^ S.length
        * ‖expLambda α ⟨F, hFd⟩‖ := fun S => (lem_sc hF' hC hβ hB S hα hατ hFd).2
  choose Gw hGw1 hGw2 using hex
  set NF := ‖expLambda α ⟨F, hFd⟩‖
  have hNF : 0 ≤ NF := norm_nonneg _
  set A' := n + 2 * ss.length
  obtain ⟨hinv, hlen⟩ := bP_inv hħ hħ1 hs₁ N ss hss
  have hK₃ : 1 ≤ K₃ := one_le_K3c _ _
  have hC₃ : max (Real.exp 1 * C₁) (τ₀ / rhoFdb) ≤ K₃ := by
    refine max_le ?_ le_K3c_tau
    refine le_trans ?_ le_K3c_exp
    have := Real.exp_pos 1
    nlinarith
  have hC₃0 : 0 ≤ max (Real.exp 1 * C₁) (τ₀ / rhoFdb) :=
    le_trans (by positivity) (le_max_left _ _)
  set M : ℝ := B * (2 ^ N * (4 * K₃) ^ (2 * N + A') * (2 * N).factorial * A'.factorial * (α⁻¹) ^ A' * ((α * ħ)⁻¹) ^ (2 * N)) * NF
  have hterm : ∀ t ∈ P, ‖t.1 • Gw (J ++ t.2)‖ ≤ M := by
    intro t ht
    obtain ⟨ℓ, r, hlw, hℓ, hr, hc⟩ := hinv t ht
    set S := J ++ t.2
    have hSl : S.length ≤ ℓ + A' := by
      simp only [S, List.length_append, A']; omega
    have hG := hGw2 S
    have hX : (S.length + 1 : ℝ) * S.length.factorial * (max (Real.exp 1 * C₁) (τ₀ / rhoFdb) / α) ^ S.length
        ≤ (S.length + 1 : ℝ) * S.length.factorial * (K₃ / α) ^ S.length := by gcongr
    have hs1 := sca (N := N) (K₃ := K₃) hℓ hSl hK₃ hα hα1 hħ hħ1
    have hc' := coeff_le hħ hc
    rw [norm_smul]
    have hi : 0 ≤ ħ⁻¹ := by positivity
    have e : ((α * ħ)⁻¹) ^ (2 * N) = (α⁻¹) ^ (2 * N) * (ħ⁻¹) ^ (2 * N) := by rw [mul_inv, mul_pow]
    calc ‖t.1‖ * ‖Gw S‖
        ≤ (2 ^ N * ħ ^ ℓ * (ħ⁻¹) ^ (2 * N)) * (B * ((S.length + 1 : ℝ) * S.length.factorial * (K₃ / α) ^ S.length) * NF) := by
          refine mul_le_mul hc' (hG.trans ?_) (norm_nonneg _) (by positivity)
          calc B * (S.length + 1) * S.length.factorial * (max (Real.exp 1 * C₁) (τ₀ / rhoFdb) / α) ^ S.length * NF
              = B * ((S.length + 1 : ℝ) * S.length.factorial * (max (Real.exp 1 * C₁) (τ₀ / rhoFdb) / α) ^ S.length) * NF := by ring
            _ ≤ _ := by gcongr
      _ = B * 2 ^ N * (ħ⁻¹) ^ (2 * N) * NF * (((S.length : ℝ) + 1) * S.length.factorial * (K₃ / α) ^ S.length * ħ ^ ℓ) := by ring
      _ ≤ B * 2 ^ N * (ħ⁻¹) ^ (2 * N) * NF
          * ((4 * K₃) ^ (2 * N + A') * (2 * N).factorial * A'.factorial * (α⁻¹) ^ A' * (α⁻¹) ^ (2 * N)) := by gcongr
      _ = M := by simp only [M]; rw [e]; ring
  refine ⟨(P.map fun t => t.1 • Gw (J ++ t.2)).sum, ?_, ?_⟩
  · rw [hs]
    have eP : polyAct (leftW J P) a = (P.map fun t => t.1 • wordAct (J ++ t.2) a).sum := by
      simp only [polyAct, leftW, List.map_map, Function.comp_def]
    rw [eP]
    refine ae_sum_weight _ _ _ _ fun t => ?_
    filter_upwards [hGw1 (J ++ t.2), Lp.coeFn_smul t.1 (Gw (J ++ t.2)), Lp.coeFn_smul t.1 (wordAct (J ++ t.2) a)] with z h1 h2 h3
    rw [h2, h3]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h1]; ring
  · have hsum := (norm_list_sum_le' P fun t => t.1 • Gw (J ++ t.2)).trans (list_sum_le (g := fun _ => M) hterm)
    have hconst : (P.map fun _ => M).sum = (P.length : ℝ) * M := by
      simp [List.map_const', List.sum_replicate]
    rw [hconst, hlen] at hsum
    push_cast at hsum
    have hc4 := c4_bound hK₃ N ss.length n
    have hM0 : 0 ≤ B * (2 * N).factorial * A'.factorial * (α⁻¹) ^ A' * ((α * ħ)⁻¹) ^ (2 * N) * NF := by positivity
    calc _ ≤ _ := hsum
      _ = ((5 : ℝ) ^ N * 3 ^ ss.length * 2 ^ N * (4 * K₃) ^ (2 * N + (n + 2 * ss.length)))
          * (B * (2 * N).factorial * A'.factorial * (α⁻¹) ^ A' * ((α * ħ)⁻¹) ^ (2 * N) * NF) := by simp only [M, A']; ring
      _ ≤ C4 K₃ ^ (N + ss.length + n) * (B * (2 * N).factorial * A'.factorial * (α⁻¹) ^ A' * ((α * ħ)⁻¹) ^ (2 * N) * NF) := by
          gcongr
      _ = _ := by ring

/-- `e^{aΛ}` on a finite combination. -/
lemma polyDom_bound {a₁ M : ℝ} {x : L2H'} (P : WP)
    (h : ∀ t ∈ P, ∃ h' : wordAct t.2 x ∈ (expLambda a₁).domain, ‖t.1‖ * ‖expLambda a₁ ⟨_, h'⟩‖ ≤ M) :
    ∃ h' : polyAct P x ∈ (expLambda a₁).domain, ‖expLambda a₁ ⟨_, h'⟩‖ ≤ P.length * M := by
  induction P with
  | nil =>
    refine ⟨Submodule.zero_mem _, ?_⟩
    have e : (⟨polyAct [] x, Submodule.zero_mem _⟩ : (expLambda a₁).domain) = 0 := rfl
    rw [e, LinearPMap.map_zero]; simp
  | cons t P ih =>
    obtain ⟨h1, b1⟩ := h t (by simp)
    obtain ⟨h2, b2⟩ := ih fun q hq => h q (by simp [hq])
    have hmem : polyAct (t :: P) x ∈ (expLambda a₁).domain := by
      rw [polyAct_cons]; exact Submodule.add_mem _ (Submodule.smul_mem _ _ h1) h2
    refine ⟨hmem, ?_⟩
    have e : (⟨polyAct (t :: P) x, hmem⟩ : (expLambda a₁).domain)
        = t.1 • (⟨wordAct t.2 x, h1⟩ : (expLambda a₁).domain) + ⟨polyAct P x, h2⟩ :=
      Subtype.ext (polyAct_cons t P x)
    rw [e, LinearPMap.map_add, LinearPMap.map_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, List.length_cons]
    push_cast
    linarith

/-- **(WB-u)**. -/
theorem lem_wb_u (hF' : FCBound τ₀ C₁) (hC : 0 ≤ C₁) {ħ α : ℝ} (hħ : 0 < ħ) (hħ1 : ħ ≤ 1) (hα : 0 < α) (hα1 : α ≤ 1)
    {α₁ α₀' : ℝ} (h0 : 0 ≤ α₁) (h12 : α₁ < α₀') (hle : α₀' ≤ τ₀) (hgap : α / 4 ≤ α₀' - α₁) (N : ℕ) {s₁ : ℝ} (hs₁ : 0 ≤ s₁)
    (ss : List ℝ) (hss : ∀ s ∈ ss, 0 ≤ s) {a : L2H'} (had : a ∈ (expLambda α₀').domain) :
    ∃ h : polyAct (bP ħ N s₁ ss) a ∈ (expLambda α₁).domain,
      ‖expLambda α₁ ⟨_, h⟩‖ ≤ C4 (K3c τ₀ C₁) ^ (N + ss.length) * (2 * N).factorial * (2 * ss.length).factorial
        * (α⁻¹) ^ (2 * ss.length) * ((α * ħ)⁻¹) ^ (2 * N) * ‖expLambda α₀' ⟨a, had⟩‖ := by
  set P := bP ħ N s₁ ss
  set K₃ := K3c τ₀ C₁
  set NF := ‖expLambda α₀' ⟨a, had⟩‖
  have hNF : 0 ≤ NF := norm_nonneg _
  set A' := 0 + 2 * ss.length
  obtain ⟨hinv, hlen⟩ := bP_inv hħ hħ1 hs₁ N ss hss
  have hK₃ : 1 ≤ K₃ := one_le_K3c _ _
  have hγ : 0 < α₀' - α₁ := by linarith
  set M : ℝ := 2 ^ N * (4 * K₃) ^ (2 * N + A') * (2 * N).factorial * A'.factorial * (α⁻¹) ^ A' * ((α * ħ)⁻¹) ^ (2 * N) * NF
  have hM0 : 0 ≤ M := by positivity
  have hterm : ∀ t ∈ P, ∃ h' : wordAct t.2 a ∈ (expLambda α₁).domain, ‖t.1‖ * ‖expLambda α₁ ⟨_, h'⟩‖ ≤ M := by
    intro t ht
    obtain ⟨ℓ, r, hlw, hℓ, hr, hc⟩ := hinv t ht
    obtain ⟨-, h', hb⟩ := lem_wc_dom hF' hC t.2 h0 h12 hle had
    refine ⟨h', ?_⟩
    set L' := t.2.length
    have hSl : L' ≤ ℓ + A' := by simp only [L', A']; omega
    have hs1 := sca (N := N) (K₃ := K₃) hℓ hSl hK₃ hα hα1 hħ hħ1
    have hc' := coeff_le hħ hc
    have hpe := pow_le_exp_factorial hC hγ L'
    have hE := Real.exp_pos 1
    have hbase : Real.exp 1 * C₁ / (α₀' - α₁) ≤ K₃ / α := by
      rw [div_le_div_iff₀ hγ hα]
      have h4 : 4 * Real.exp 1 * C₁ ≤ K₃ := le_K3c_exp
      have h5 : 0 ≤ Real.exp 1 * C₁ := by positivity
      nlinarith
    have hbase0 : 0 ≤ Real.exp 1 * C₁ / (α₀' - α₁) := by positivity
    have hw : ‖expLambda α₁ ⟨wordAct t.2 a, h'⟩‖ ≤ (((L' : ℝ) + 1) * L'.factorial * (K₃ / α) ^ L') * NF := by
      refine hb.trans (mul_le_mul_of_nonneg_right ?_ hNF)
      calc (C₁ * L' / (α₀' - α₁)) ^ L' ≤ (Real.exp 1 * C₁ / (α₀' - α₁)) ^ L' * L'.factorial := hpe
        _ ≤ (K₃ / α) ^ L' * L'.factorial := by gcongr
        _ ≤ ((L' : ℝ) + 1) * L'.factorial * (K₃ / α) ^ L' := by
            have hf : (0 : ℝ) ≤ (K₃ / α) ^ L' * L'.factorial := by positivity
            have hL0 : (0 : ℝ) ≤ L' := Nat.cast_nonneg _
            nlinarith
    have e : ((α * ħ)⁻¹) ^ (2 * N) = (α⁻¹) ^ (2 * N) * (ħ⁻¹) ^ (2 * N) := by rw [mul_inv, mul_pow]
    have hi : 0 ≤ ħ⁻¹ := by positivity
    calc ‖t.1‖ * ‖expLambda α₁ ⟨wordAct t.2 a, h'⟩‖
        ≤ (2 ^ N * ħ ^ ℓ * (ħ⁻¹) ^ (2 * N)) * ((((L' : ℝ) + 1) * L'.factorial * (K₃ / α) ^ L') * NF) :=
          mul_le_mul hc' hw (norm_nonneg _) (by positivity)
      _ = 2 ^ N * (ħ⁻¹) ^ (2 * N) * NF * (((L' : ℝ) + 1) * L'.factorial * (K₃ / α) ^ L' * ħ ^ ℓ) := by ring
      _ ≤ 2 ^ N * (ħ⁻¹) ^ (2 * N) * NF
          * ((4 * K₃) ^ (2 * N + A') * (2 * N).factorial * A'.factorial * (α⁻¹) ^ A' * (α⁻¹) ^ (2 * N)) := by gcongr
      _ = M := by simp only [M]; rw [e]; ring
  obtain ⟨h, hb⟩ := polyDom_bound P hterm
  refine ⟨h, hb.trans ?_⟩
  rw [hlen]
  push_cast
  have hc4 := c4_bound hK₃ N ss.length 0
  rw [add_zero] at hc4
  have hR0 : 0 ≤ (2 * N).factorial * (A'.factorial : ℝ) * (α⁻¹) ^ A' * ((α * ħ)⁻¹) ^ (2 * N) * NF := by positivity
  have eA : A' = 2 * ss.length := by simp only [A']; omega
  calc _ = ((5 : ℝ) ^ N * 3 ^ ss.length * 2 ^ N * (4 * K₃) ^ (2 * N + (0 + 2 * ss.length)))
        * ((2 * N).factorial * (A'.factorial : ℝ) * (α⁻¹) ^ A' * ((α * ħ)⁻¹) ^ (2 * N) * NF) := by simp only [M, A']; ring
    _ ≤ C4 K₃ ^ (N + ss.length) * ((2 * N).factorial * (A'.factorial : ℝ) * (α⁻¹) ^ A' * ((α * ħ)⁻¹) ^ (2 * N) * NF) := by
        gcongr
    _ = _ := by rw [eA]; ring

end bounds

/-! ### `b'(s)` as an iterated operator, and the packaged lemma -/

lemma polyAct_oneP (a : L2H') : polyAct oneP a = a := by
  simp [polyAct, oneP, wordAct]

/-- `∏_{s :: r} Δ = Δ(s) ∏_r Δ`, as operators on `a`. -/
lemma polyAct_deltaProd_cons {a : L2H'} (hA : AllWords a) (s : ℝ) (r : List ℝ) :
    polyAct (deltaProd (s :: r)) a = polyAct (deltaP s) (polyAct (deltaProd r) a) :=
  (polyAct_mulP hA _ _).symm

/-- `Δ_φ^{N+1} = Δ_φ Δ_φ^N`, as operators on `a`. -/
lemma polyAct_powWP_succ {a : L2H'} (hA : AllWords a) (Φ : WP) (N : ℕ) :
    polyAct (powWP Φ (N + 1)) a = polyAct Φ (polyAct (powWP Φ N) a) :=
  (polyAct_mulP hA _ _).symm

/-- **`b'(s) = Δ_φ(s₁)^N (∏ Δ(s)) a`.** -/
lemma polyAct_bP {a : L2H'} (hA : AllWords a) (ħ : ℝ) (N : ℕ) (s₁ : ℝ) (ss : List ℝ) :
    polyAct (bP ħ N s₁ ss) a = polyAct (powWP (deltaPhiP ħ s₁) N) (polyAct (deltaProd ss) a) :=
  (polyAct_mulP hA _ _).symm

/-- **Lemma WB** (`lem:wb`). -/
theorem lem_wb_main {τ₀ : ℝ} (hτ₀ : τ₀ < Real.pi / 2) :
    ∃ C₄ : ℝ, 0 ≤ C₄ ∧
      (∀ β : ℝ, 0 ≤ β → ∃ B : ℝ, 0 ≤ B ∧ ∀ (ħ α : ℝ) (N : ℕ) (s₁ : ℝ) (ss : List ℝ) (J : List Bool) (n : ℕ) (F : L2H'),
        0 < ħ → ħ ≤ 1 → 0 < α → α ≤ 1 → α ≤ τ₀ → 0 ≤ s₁ → (∀ s ∈ ss, 0 ≤ s) → J.length ≤ n →
        ∀ hFd : F ∈ (expLambda α).domain, ∃ a : L2H',
          (a : UpperHalfPlane → ℂ) =ᵐ[volume] (fun z => ((hF (z : ℂ) ^ β : ℝ) : ℂ) * F z) ∧
          WordDom J (polyAct (bP ħ N s₁ ss) a) ∧ ∃ G : L2H',
            (G : UpperHalfPlane → ℂ) =ᵐ[volume]
              (fun z => ((hF (z : ℂ) ^ (-β) : ℝ) : ℂ) * wordAct J (polyAct (bP ħ N s₁ ss) a) z) ∧
            ‖G‖ ≤ B * C₄ ^ (N + ss.length + n) * (2 * N).factorial * (n + 2 * ss.length).factorial
              * (α⁻¹) ^ (n + 2 * ss.length) * ((α * ħ)⁻¹) ^ (2 * N) * ‖expLambda α ⟨F, hFd⟩‖) ∧
      (∀ (ħ α α₁ α₀' : ℝ) (N : ℕ) (s₁ : ℝ) (ss : List ℝ) (a : L2H'),
        0 < ħ → ħ ≤ 1 → 0 < α → α ≤ 1 → 0 ≤ α₁ → α₁ < α₀' → α₀' ≤ τ₀ → α / 4 ≤ α₀' - α₁ → 0 ≤ s₁ → (∀ s ∈ ss, 0 ≤ s) →
        ∀ had : a ∈ (expLambda α₀').domain, ∃ h : polyAct (bP ħ N s₁ ss) a ∈ (expLambda α₁).domain,
          ‖expLambda α₁ ⟨_, h⟩‖ ≤ C₄ ^ (N + ss.length) * (2 * N).factorial * (2 * ss.length).factorial
            * (α⁻¹) ^ (2 * ss.length) * ((α * ħ)⁻¹) ^ (2 * N) * ‖expLambda α₀' ⟨a, had⟩‖) := by
  obtain ⟨C₁, hC, hF'⟩ := lem_fc hτ₀
  have hK := one_le_K3c τ₀ C₁
  refine ⟨C4 (K3c τ₀ C₁), by unfold C4; positivity, fun β hβ => ?_, ?_⟩
  · obtain ⟨B, hB0, hB⟩ := fdb β
    refine ⟨B, hB0, fun ħ α N s₁ ss J n F hħ hħ1 hα hα1 hατ hs₁ hss hJ hFd => ?_⟩
    obtain ⟨hd, hG⟩ := lem_wb_w hF' hC hβ hB hB0 hħ hħ1 hα hα1 hατ N hs₁ ss hss J hJ hFd
    exact ⟨mulW hβ hB [] F, coe_mulCL (adm_word hβ hB []).sb F, hd, hG⟩
  · intro ħ α α₁ α₀' N s₁ ss a hħ hħ1 hα hα1 h0 h12 hle hgap hs₁ hss had
    exact lem_wb_u hF' hC hħ hħ1 hα hα1 h0 h12 hle hgap N hs₁ ss hss had

end Qschubert
