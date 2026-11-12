import Qschubert.KLG5
import Qschubert.KLMweak

/-!
# Proposition `prop:g5`: the order `ħt` of the leading error is attained on `ℍ`

For `Γ = {1}` and an amplitude `a ≠ 0` all of whose words in `X, Y` lie in `L²(ℍ)`, at `t = τ ħ^{-1/2}`,

`| ‖U(t)(a e^{iφ/ħ}) - u^{(0)}(t)‖ - (τ/2) √ħ ‖(Y² - Y)a‖ | ≤ C ħ`,  and  `‖a‖ ≤ 4 ‖(Y² - Y)a‖`,

with `C = ‖X²a‖/4 + τ² B/8`, where `B` bounds `‖Δ(r)Δ(s)a‖` for `r, s ≥ 0` by the norms of the words of length at most four.
The proof is that of `printedThm13_false` (Dyson identity at orders `0` and `1` on the trivial group, `virial`), with the
second-order term bounded through the words of `a` (`norm_polyAct_le`) instead of an analytic norm.

* `wordBound`, `norm_wordAct_le_wordBound`: a bound for all words of length at most `n`.
* `norm_polyAct_bP_two`: `‖Δ(r)Δ(s)a‖ ≤ 9 B` for `r, s ≥ 0` (from `deltaProd_inv`).
* `norm_xK_one_le`: the upper bound for the first Dyson coefficient.
* `propG5`: the statement `Stmt_propG5`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded UpperHalfPlane
open scoped ENNReal InnerProductSpace MatrixGroups Pointwise ComplexConjugate

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

attribute [local instance] pd_bot

/-- `Σ_{k ≤ n} Σ_{|w| = k} ‖Z_w A‖`, a bound for every word of length at most `n`. -/
noncomputable def wordBound (A : L2H') (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), ∑ f : Fin k → Bool, ‖wordAct (List.ofFn f) A‖

lemma wordBound_nonneg (A : L2H') (n : ℕ) : 0 ≤ wordBound A n :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma norm_wordAct_le_wordBound (A : L2H') {n : ℕ} {w : List Bool} (hw : w.length ≤ n) :
    ‖wordAct w A‖ ≤ wordBound A n := by
  have hk : w.length ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
  have h1 : ‖wordAct w A‖ ≤ ∑ f : Fin w.length → Bool, ‖wordAct (List.ofFn f) A‖ := by
    have h := Finset.single_le_sum (f := fun f : Fin w.length → Bool => ‖wordAct (List.ofFn f) A‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ w.get)
    simpa [List.ofFn_get] using h
  exact h1.trans (Finset.single_le_sum (f := fun k => ∑ f : Fin k → Bool, ‖wordAct (List.ofFn f) A‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) hk)

/-- `‖Δ(r)Δ(s)A‖ ≤ 9 B` for `r, s ≥ 0`, with `B` the word bound of length `4`. -/
lemma norm_polyAct_bP_two {A : L2H'} (ħ s₁ : ℝ) {l : List ℝ} (hl : l.length = 2) (hs : ∀ s ∈ l, 0 ≤ s) :
    ‖polyAct (bP ħ 0 s₁ l) A‖ ≤ 9 * wordBound A 4 := by
  obtain ⟨h1, h2⟩ := deltaProd_inv l hs
  have hP : ∀ t ∈ bP ħ 0 s₁ l, ‖t.1‖ ≤ 1 ∧ ‖wordAct t.2 A‖ ≤ wordBound A 4 := by
    intro t ht
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_mulP ht
    simp only [powWP, oneP, List.mem_singleton] at hp
    subst hp
    obtain ⟨b1, b2⟩ := h1 q hq
    refine ⟨by simpa using b1, norm_wordAct_le_wordBound A ?_⟩
    simp only [List.nil_append]
    rw [hl] at b2
    omega
  have hb := norm_polyAct_le (a := A) (wordBound_nonneg A 4) (bP ħ 0 s₁ l) hP
  have hlen : (bP ħ 0 s₁ l).length = 9 := by
    show (mulP (powWP (deltaPhiP ħ s₁) 0) (deltaProd l)).length = 9
    rw [length_mulP, h2, hl]
    rfl
  rw [hlen] at hb
  exact_mod_cast hb

lemma norm_xK_one_le {A : L2H'} {t : ℝ} (ht : 0 ≤ t) :
    ‖xK A 1 t‖ ≤ t * ‖wordAct [false, false] A - wordAct [false] A‖ + 1 / 2 * ‖wordAct [true, true] A‖ := by
  rw [xK_one]
  have h1 : ‖(t : ℂ) • (wordAct [false, false] A - wordAct [false] A)‖ = t * ‖wordAct [false, false] A - wordAct [false] A‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg ht]
  have h2 : ‖(∫ s in (0 : ℝ)..t, ((Real.exp (-2 * s) : ℝ) : ℂ)) • wordAct [true, true] A‖ ≤ 1 / 2 * ‖wordAct [true, true] A‖ := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (norm_int_exp_le ht) (norm_nonneg _)
  have h3 := norm_add_le ((∫ s in (0 : ℝ)..t, ((Real.exp (-2 * s) : ℝ) : ℂ)) • wordAct [true, true] A)
    ((t : ℂ) • (wordAct [false, false] A - wordAct [false] A))
  linarith

/-- **Proposition `prop:g5`.** `Γ = {1}`, `b = ∞`, an amplitude `a ≠ 0` (with `L²` class `A`) all of whose words lie in `L²(ℍ)`:
`‖a‖ ≤ 4 ‖(Y² - Y)a‖`, and for every `τ > 0` there is `C` with
`| ‖U(t)(a e^{iφ/ħ}) - u^{(0)}(t)‖ - (τ/2) √ħ ‖(Y² - Y)a‖ | ≤ C ħ` at `t = τ / √ħ`, for every `ħ > 0`. -/
def Stmt_propG5 : Prop :=
  ∀ (a : ℍ → ℂ) (A : L2H'), SmoothH a → ⇑A =ᵐ[volume] a → AllWords A → A ≠ 0 →
    ‖A‖ ≤ 4 * ‖wordAct [false, false] A - wordAct [false] A‖ ∧
    ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 ≤ C ∧ ∀ ħ' : ℝ, 0 < ħ' →
      ∃ (hv : PerioConv (⊥ : Subgroup PGL(2, ℝ)) (initState 1 ħ' a))
        (hw : PerioConv (⊥ : Subgroup PGL(2, ℝ)) (approxSolB 1 0 ħ' (τ / Real.sqrt ħ') a)),
        |(approxErr (⊥ : Subgroup PGL(2, ℝ)) 0 ħ' (τ / Real.sqrt ħ') hv hw).toReal
            - τ / 2 * Real.sqrt ħ' * ‖wordAct [false, false] A - wordAct [false] A‖| ≤ C * ħ'

set_option maxHeartbeats 4000000 in
theorem propG5 : Stmt_propG5 := by
  intro a A hsm haA hAW hA0
  refine ⟨virial hAW, fun τ hτ => ?_⟩
  set c₁ : ℝ := ‖wordAct [false, false] A - wordAct [false] A‖ with hc₁
  set c₂ : ℝ := ‖wordAct [true, true] A‖ with hc₂
  have hc₂0 : 0 ≤ c₂ := norm_nonneg _
  set B₂ : ℝ := 9 * wordBound A 4 with hB₂
  have hB₂0 : 0 ≤ B₂ := by have := wordBound_nonneg A 4; positivity
  refine ⟨c₂ / 4 + τ ^ 2 * B₂ / 8, by positivity, fun ħ hħ => ?_⟩
  have : Countable (⊥ : Subgroup PGL(2, ℝ)) := Finite.to_countable
  set t : ℝ := τ / Real.sqrt ħ with htd
  have hsq : 0 < Real.sqrt ħ := Real.sqrt_pos.2 hħ
  have ht : 0 ≤ t := by positivity
  set W : SurfW (conjS (Matrix.SpecialLinearGroup.toPGL ((1 : SL(2, ℝ))⁻¹)) (⊥ : Subgroup PGL(2, ℝ))) := surfW_one _ with hWd
  have hGa : ∀ w : List Bool, W.Chart (wordAct w A) (wordAct w A) := fun w => chart_one _ _
  have hsG : SmoothH fun w => a ((1 : SL(2, ℝ)) • w) := by simpa using hsm
  have hAae : ⇑A =ᵐ[volume] fun w => a ((1 : SL(2, ℝ)) • w) := by
    filter_upwards [haA] with z hz
    rw [one_smul]
    exact hz
  obtain ⟨hv, hw⟩ := perioConv_general (W := W) hsG hAae hAW hGa 0 ħ t
  refine ⟨hv, hw, ?_⟩
  have hE := approxErr_general (W := W) hsG hAae hAW hGa hħ.ne' 0 0 t hv hw
  set cI : ℂ := Complex.I * (ħ : ℂ) / 2 with hcI
  have hcIn : ‖cI‖ = ħ / 2 := by
    rw [hcI]
    simp [abs_of_pos hħ]
  set E0 := cI ^ (0 + 1) • simplexInt (0 + 1) t fun ss => W.vS ħ (ss.headD 0) (polyAct (bP ħ 0 (ss.headD 0) ss) A) with hE0
  set E1 := cI ^ (1 + 1) • simplexInt (1 + 1) t fun ss => W.vS ħ (ss.headD 0) (polyAct (bP ħ 0 (ss.headD 0) ss) A) with hE1
  have h0 : W.vS ħ 0 A - W.vS ħ t (∑ k ∈ Finset.range (0 + 1), cI ^ k • xK A k t) = E0 := SurfW.surf_D4 (W := W) hAW hGa hħ.ne' 0 0 t
  have h1 : W.vS ħ 0 A - W.vS ħ t (∑ k ∈ Finset.range (1 + 1), cI ^ k • xK A k t) = E1 := SurfW.surf_D4 (W := W) hAW hGa hħ.ne' 1 0 t
  have hsplit : E0 = cI • W.vS ħ t (xK A 1 t) + E1 := by
    rw [← h0, ← h1]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_smul, pow_one, xK_zero, map_add, map_smul]
    abel
  have hmainT : ‖cI • W.vS ħ t (xK A 1 t)‖ = ħ / 2 * ‖xK A 1 t‖ := by
    rw [norm_smul, hcIn, hWd, norm_vS_one]
  have hE1n : ‖E1‖ ≤ (ħ / 2) ^ 2 * (B₂ * t ^ 2 / 2) := by
    rw [hE1, norm_smul, norm_pow, hcIn]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hs := norm_simplexInt_le (E := Lp ℂ 2 (surfMeasure (conjS (Matrix.SpecialLinearGroup.toPGL ((1 : SL(2, ℝ))⁻¹)) (⊥ : Subgroup PGL(2, ℝ)))))
      hB₂0 (1 + 1) t (fun ss => W.vS ħ (ss.headD 0) (polyAct (bP ħ 0 (ss.headD 0) ss) A)) ht (fun l hl hls => by
        rw [hWd, norm_vS_one]
        exact norm_polyAct_bP_two ħ (l.headD 0) hl fun s hs => (hls s hs).1)
    refine hs.trans (le_of_eq ?_)
    norm_num
  have hx1 : t * c₁ - 1 / 2 * c₂ ≤ ‖xK A 1 t‖ := norm_xK_one_ge ht
  have hx2 : ‖xK A 1 t‖ ≤ t * c₁ + 1 / 2 * c₂ := norm_xK_one_le ht
  have hlow : ħ / 2 * ‖xK A 1 t‖ - ‖E1‖ ≤ ‖E0‖ := by
    have h3 : ‖cI • W.vS ħ t (xK A 1 t)‖ - ‖E1‖ ≤ ‖E0‖ := by
      rw [hsplit]
      have := norm_sub_norm_le (cI • W.vS ħ t (xK A 1 t)) (-E1)
      rwa [norm_neg, sub_neg_eq_add] at this
    rwa [hmainT] at h3
  have hup : ‖E0‖ ≤ ħ / 2 * ‖xK A 1 t‖ + ‖E1‖ := by
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [hmainT]
  have hval : (approxErr (⊥ : Subgroup PGL(2, ℝ)) 0 ħ t hv hw).toReal = ‖E0‖ := by
    rw [hE, toReal_enorm]
  rw [hval]
  have hħt : ħ * t = τ * Real.sqrt ħ := by
    rw [htd]
    field_simp
    rw [Real.sq_sqrt hħ.le]
  have hħt2 : ħ ^ 2 * t ^ 2 = τ ^ 2 * ħ := by
    have : (ħ * t) ^ 2 = τ ^ 2 * Real.sqrt ħ ^ 2 := by rw [hħt]; ring
    rw [Real.sq_sqrt hħ.le] at this
    nlinarith [this]
  have hmain : τ / 2 * Real.sqrt ħ * c₁ = ħ / 2 * (t * c₁) := by
    have : ħ / 2 * (t * c₁) = (ħ * t) * c₁ / 2 := by ring
    rw [this, hħt]
    ring
  have hE1' : ‖E1‖ ≤ τ ^ 2 * B₂ / 8 * ħ := by
    have e : (ħ / 2) ^ 2 * (B₂ * t ^ 2 / 2) = (ħ ^ 2 * t ^ 2) * B₂ / 8 := by ring
    rw [e, hħt2] at hE1n
    linarith
  rw [hmain, abs_le]
  have hc20 : ħ / 2 * (1 / 2 * c₂) = c₂ / 4 * ħ := by ring
  constructor
  · nlinarith [hlow, hx1, hE1', norm_nonneg E1]
  · nlinarith [hup, hx2, hE1', norm_nonneg E1]

end Qschubert
