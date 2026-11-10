import Qschubert.KLPcWa
import Qschubert.KLPcEmB

/-!
# Words in weighted spaces, part 2: the energy recursion

`w_energy`: for a weight `W` with `|∇ log W| ≤ l` and `u ∈ Dom(-Δ)`,
`‖W X u‖² + ‖W Y u‖² ≤ Re ⟪W u, W(-Δ u)⟫ + 2 l ‖W u‖ (‖W X u‖² + ‖W Y u‖²)^{1/2}`.

`words_rec`: if `v_{j+1} = (μ - Δ) v_j`, all words act on every `v_j` and `‖W v_j‖ ≤ A q^{2j} (2j)!`, then
`‖W Z_S v_j‖ ≤ A (4 + 2l)^k q^{k+2j} (k+2j)!` for every word `S` of length `k`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate UpperHalfPlane

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- From `c t ≤ l (t² P² + B²)` for all `t > 0` to `c ≤ 2 l P B`. -/
lemma quad_scale {c l P B : ℝ} (hl : 0 ≤ l) (hP : 0 ≤ P) (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 < t → c * t ≤ l * (t ^ 2 * P ^ 2 + B ^ 2)) : c ≤ 2 * l * P * B := by
  rcases hP.eq_or_lt with hP0 | hPpos
  · rw [← hP0, mul_zero, zero_mul]
    by_contra hc
    have hc' : 0 < c := not_le.1 hc
    have h1 := h ((l * B ^ 2 + 1) / c) (by positivity)
    rw [← hP0] at h1
    have e : c * ((l * B ^ 2 + 1) / c) = l * B ^ 2 + 1 := by field_simp
    rw [e] at h1
    nlinarith
  rcases hB.eq_or_lt with hB0 | hBpos
  · rw [← hB0, mul_zero]
    by_contra hc
    have hc' : 0 < c := not_le.1 hc
    set D := l * P ^ 2 + 1 with hD
    have hD0 : 0 < D := by positivity
    set t := c / (2 * D) with ht
    have ht0 : 0 < t := by positivity
    have h1 := h t ht0
    rw [← hB0] at h1
    have hc2 : c = 2 * D * t := by rw [ht]; field_simp
    have h2 : l * P ^ 2 = D - 1 := by rw [hD]; ring
    have h3 : 2 * D * t * t ≤ (D - 1) * t ^ 2 := by
      calc 2 * D * t * t = c * t := by rw [hc2]
        _ ≤ l * (t ^ 2 * P ^ 2 + 0 ^ 2) := h1
        _ = (D - 1) * t ^ 2 := by rw [← h2]; ring
    nlinarith [sq_pos_of_pos ht0]
  · have h1 := h (B / P) (by positivity)
    have e : (B / P) ^ 2 * P ^ 2 = B ^ 2 := by field_simp
    rw [e] at h1
    have h2 : c * B ≤ 2 * l * P * B * B := by
      have h3 := mul_le_mul_of_nonneg_right h1 hPpos.le
      have e2 : c * (B / P) * P = c * B := by field_simp
      rw [e2] at h3
      linarith
    exact le_of_mul_le_mul_right h2 hBpos

section energy

variable {W : ℂ → ℝ} {C l : ℝ} (hW : WaveS W C l)
include hW

lemma inner_W_W (x y : L2H') : ⟪mulCL hW.sb x, mulCL hW.sb y⟫_ℂ = ⟪mulCL hW.adm.sb x, y⟫_ℂ := by
  rw [← inner_mulCL_left, L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coe_mulCL hW.sb (mulCL hW.sb x), coe_mulCL hW.sb x, coe_mulCL hW.adm.sb x] with z h1 h2 h3
  rw [h1, h2, h3]
  push_cast
  ring_nf

lemma re_inner_W_le (x y : L2H') : (⟪mulCL hW.sb x, mulCL hW.sb y⟫_ℂ).re ≤ ‖mulCL hW.sb x‖ * ‖mulCL hW.sb y‖ :=
  (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)

/-- The cross term in product form. -/
lemma cross_prod (u b₁ b₂ : L2H') :
    -(⟪mulCL hW.adm.sbX u, b₁⟫_ℂ).re - (⟪mulCL hW.adm.sbY u, b₂⟫_ℂ).re
      ≤ 2 * l * ‖mulCL hW.sb u‖ * √(‖mulCL hW.sb b₁‖ ^ 2 + ‖mulCL hW.sb b₂‖ ^ 2) := by
  refine quad_scale hW.l0 (norm_nonneg _) (Real.sqrt_nonneg _) fun t ht => ?_
  have h := cross_sharp hW ((t : ℂ) • u) b₁ b₂
  rw [map_smul, map_smul, map_smul, inner_smul_left, inner_smul_left, norm_smul, Complex.conj_ofReal, Complex.re_ofReal_mul,
    Complex.re_ofReal_mul, Complex.norm_real, Real.norm_of_nonneg ht.le] at h
  rw [Real.sq_sqrt (by positivity)]
  have e : (t * ‖mulCL hW.sb u‖) ^ 2 = t ^ 2 * ‖mulCL hW.sb u‖ ^ 2 := by ring
  rw [e] at h
  linarith

/-- **The weighted energy inequality.** -/
theorem w_energy (u : negLapH.domain) :
    ‖mulCL hW.sb (domX u)‖ ^ 2 + ‖mulCL hW.sb (domY u)‖ ^ 2
      ≤ (⟪mulCL hW.sb (u : L2H'), mulCL hW.sb (negLapH u)⟫_ℂ).re
        + 2 * l * ‖mulCL hW.sb (u : L2H')‖ * √(‖mulCL hW.sb (domX u)‖ ^ 2 + ‖mulCL hW.sb (domY u)‖ ^ 2) := by
  have hmem := mul_mem_domain hW.adm u
  have hX : domX ⟨mulCL hW.adm.sb (u : L2H'), hmem⟩ = mulCL hW.adm.sbX (u : L2H') + mulCL hW.adm.sb (domX u) := domX_mul hW.adm u
  have hY : domY ⟨mulCL hW.adm.sb (u : L2H'), hmem⟩ = mulCL hW.adm.sbY (u : L2H') + mulCL hW.adm.sb (domY u) := domY_mul hW.adm u
  have hform := inner_dom_add ⟨mulCL hW.adm.sb (u : L2H'), hmem⟩ u
  have hsym : ⟪negLapH ⟨mulCL hW.adm.sb (u : L2H'), hmem⟩, (u : L2H')⟫_ℂ = ⟪mulCL hW.adm.sb (u : L2H'), negLapH u⟫_ℂ :=
    (negLapH_isPositive.1 ⟨mulCL hW.adm.sb (u : L2H'), hmem⟩ u).symm
  have hmain : ⟪mulCL hW.adm.sb (u : L2H'), negLapH u⟫_ℂ
      = ⟪mulCL hW.adm.sbX (u : L2H'), domX u⟫_ℂ + ⟪mulCL hW.adm.sb (domX u), domX u⟫_ℂ
        + (⟪mulCL hW.adm.sbY (u : L2H'), domY u⟫_ℂ + ⟪mulCL hW.adm.sb (domY u), domY u⟫_ℂ) := by
    rw [← hsym, ← hform, hX, hY, inner_add_left, inner_add_left]
  have eX : (⟪mulCL hW.adm.sb (domX u), domX u⟫_ℂ).re = ‖mulCL hW.sb (domX u)‖ ^ 2 := by
    rw [← inner_W_W hW, inner_self_eq_norm_sq_to_K]
    norm_cast
  have eY : (⟪mulCL hW.adm.sb (domY u), domY u⟫_ℂ).re = ‖mulCL hW.sb (domY u)‖ ^ 2 := by
    rw [← inner_W_W hW, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hre := congrArg Complex.re hmain
  simp only [Complex.add_re] at hre
  rw [eX, eY, ← inner_W_W hW] at hre
  have hc := cross_prod hW (u : L2H') (domX u) (domY u)
  linarith

end energy

/-- From `B² ≤ a b + c B` to `B ≤ c + √(a b)`. -/
lemma quad_solve {B a b c : ℝ} (hB : 0 ≤ B) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : B ^ 2 ≤ a * b + c * B) : B ≤ c + √(a * b) := by
  rcases le_or_gt B c with h1 | h1
  · linarith [Real.sqrt_nonneg (a * b)]
  · have h2 : (B - c) ^ 2 ≤ a * b := by nlinarith
    have h3 : B - c ≤ √(a * b) := Real.le_sqrt_of_sq_le h2
    linarith

/-- The arithmetic of the induction step. -/
lemma rec_arith {A K q l : ℝ} (hA : 0 ≤ A) (hq : 1 ≤ q) (hl : 0 ≤ l) (hK : K = 4 + 2 * l) (k j : ℕ) :
    (2 * (k : ℝ) + 2 * l) * (A * K ^ k * q ^ (k + 2 * j) * ((k + 2 * j).factorial : ℝ))
      + √((A * K ^ k * q ^ (k + 2 * j) * ((k + 2 * j).factorial : ℝ)) * (A * K ^ k * q ^ (k + 2 * (j + 1)) * ((k + 2 * (j + 1)).factorial : ℝ)))
      ≤ A * K ^ (k + 1) * q ^ (k + 1 + 2 * j) * ((k + 1 + 2 * j).factorial : ℝ) := by
  set n := k + 2 * j with hn
  have hK0 : 0 < K := by rw [hK]; linarith
  have hq0 : 0 < q := by linarith
  have e1 : k + 2 * (j + 1) = n + 2 := by omega
  have e2 : k + 1 + 2 * j = n + 1 := by omega
  rw [e1, e2]
  set F : ℝ := (n.factorial : ℝ) with hF
  have hF0 : 0 < F := by rw [hF]; exact_mod_cast n.factorial_pos
  have hf1 : ((n + 1).factorial : ℝ) = (n + 1 : ℝ) * F := by rw [hF]; push_cast [Nat.factorial_succ]; ring
  have hf2 : ((n + 2).factorial : ℝ) = (n + 2 : ℝ) * ((n + 1 : ℝ) * F) := by
    rw [hF]; push_cast [Nat.factorial_succ]; ring
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hkn : (k : ℝ) ≤ n := by rw [hn]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) j]
  set T : ℝ := A * K ^ k * q ^ (n + 1) * ((n + 1 : ℝ) * F) with hT
  have hT0 : 0 ≤ T := by positivity
  -- the square root term
  have hsq : √((A * K ^ k * q ^ n * F) * (A * K ^ k * q ^ (n + 2) * ((n + 2).factorial : ℝ))) ≤ 2 * T := by
    rw [show (2 * T) = √((2 * T) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_le_sqrt ?_
    rw [hf2, hT]
    have h4 : (n + 2 : ℝ) ≤ 4 * (n + 1) := by linarith
    have hpos : 0 ≤ (A * K ^ k * q ^ (n + 1) * F) ^ 2 * (n + 1 : ℝ) := by positivity
    calc (A * K ^ k * q ^ n * F) * (A * K ^ k * q ^ (n + 2) * ((n + 2 : ℝ) * ((n + 1 : ℝ) * F)))
        = (A * K ^ k * q ^ (n + 1) * F) ^ 2 * (n + 1 : ℝ) * (n + 2 : ℝ) := by ring
      _ ≤ (A * K ^ k * q ^ (n + 1) * F) ^ 2 * (n + 1 : ℝ) * (4 * (n + 1)) := mul_le_mul_of_nonneg_left h4 hpos
      _ = _ := by ring
  -- the linear term
  have hlin : (2 * (k : ℝ) + 2 * l) * (A * K ^ k * q ^ n * F) ≤ (2 + 2 * l) * T := by
    have hqq : q ^ n ≤ q ^ (n + 1) := pow_le_pow_right₀ hq (Nat.le_succ n)
    have h5 : 2 * (k : ℝ) + 2 * l ≤ (2 + 2 * l) * (n + 1) := by nlinarith
    have hbase : 0 ≤ A * K ^ k * F := by positivity
    calc (2 * (k : ℝ) + 2 * l) * (A * K ^ k * q ^ n * F)
        = (2 * (k : ℝ) + 2 * l) * q ^ n * (A * K ^ k * F) := by ring
      _ ≤ ((2 + 2 * l) * (n + 1)) * q ^ (n + 1) * (A * K ^ k * F) := by
          refine mul_le_mul_of_nonneg_right ?_ hbase
          exact mul_le_mul h5 hqq (by positivity) (by positivity)
      _ = _ := by rw [hT]; ring
  have hfin : A * K ^ (k + 1) * q ^ (n + 1) * ((n + 1).factorial : ℝ) = (4 + 2 * l) * T := by
    rw [hf1, hT, pow_succ, hK]; ring
  rw [hfin]
  linarith

/-- **The word recursion.** -/
theorem words_rec {W : ℂ → ℝ} {C l : ℝ} (hW : WaveS W C l) {μ : ℝ} (hμ : 0 ≤ μ) (v : ℕ → L2H') (hA : ∀ j, AllWords (v j))
    (hstep : ∀ j, negLapH ⟨v j, AllWords.mem (hA j) []⟩ = v (j + 1) - (μ : ℂ) • v j)
    {A q : ℝ} (hA0 : 0 ≤ A) (hq : 1 ≤ q)
    (hbase : ∀ j, ‖mulCL hW.sb (v j)‖ ≤ A * q ^ (2 * j) * ((2 * j).factorial : ℝ)) :
    ∀ (k j : ℕ) (S : List Bool), S.length = k →
      ‖mulCL hW.sb (wordAct S (v j))‖ ≤ A * (4 + 2 * l) ^ k * q ^ (k + 2 * j) * ((k + 2 * j).factorial : ℝ) := by
  have hl := hW.l0
  intro k
  induction k with
  | zero =>
    intro j S hS
    have e : S = [] := List.length_eq_zero_iff.1 hS
    subst e
    have h := hbase j
    simpa [wordAct] using h
  | succ k ih =>
    intro j S hS
    set Wm := mulCL hW.sb with hWm
    -- the maximal gradient norm over words of length `k`
    let Bf : List.Vector Bool k → ℝ := fun T =>
      √(‖Wm (wordAct (true :: T.1) (v j))‖ ^ 2 + ‖Wm (wordAct (false :: T.1) (v j))‖ ^ 2)
    obtain ⟨S₀, hmax⟩ := Finite.exists_max Bf
    set B₀ := Bf S₀ with hB₀
    have hB₀0 : 0 ≤ B₀ := Real.sqrt_nonneg _
    have hword : ∀ T : List Bool, T.length = k + 1 → ‖Wm (wordAct T (v j))‖ ≤ B₀ := fun T hT => by
      cases T with
      | nil => simp at hT
      | cons z T' =>
        have hT' : T'.length = k := by simpa using hT
        have h1 : ‖Wm (wordAct (z :: T') (v j))‖ ≤ Bf ⟨T', hT'⟩ := by
          refine Real.le_sqrt_of_sq_le ?_
          cases z
          · show ‖Wm (wordAct (false :: T') (v j))‖ ^ 2 ≤ ‖Wm (wordAct (true :: T') (v j))‖ ^ 2 + ‖Wm (wordAct (false :: T') (v j))‖ ^ 2
            linarith [sq_nonneg ‖Wm (wordAct (true :: T') (v j))‖]
          · show ‖Wm (wordAct (true :: T') (v j))‖ ^ 2 ≤ ‖Wm (wordAct (true :: T') (v j))‖ ^ 2 + ‖Wm (wordAct (false :: T') (v j))‖ ^ 2
            linarith [sq_nonneg ‖Wm (wordAct (false :: T') (v j))‖]
        exact h1.trans (hmax ⟨T', hT'⟩)
    refine (hword S hS).trans ?_
    -- the energy inequality at the maximizer
    set S' := S₀.1 with hS'
    have hS'l : S'.length = k := S₀.2
    have hAj := hA j
    have hw := allWords_wordAct hAj S'
    set w := wordAct S' (v j) with hwd
    have hwm : w ∈ negLapH.domain := AllWords.mem hAj S'
    set u : negLapH.domain := ⟨w, hwm⟩ with hu
    have eX : domX u = wordAct (true :: S') (v j) := by
      rw [wordAct_cons true S' hwm]; simp only [domZ, ite_true]; rfl
    have eY : domY u = wordAct (false :: S') (v j) := by
      rw [wordAct_cons false S' hwm]; simp only [domZ, Bool.false_eq_true, ite_false]; rfl
    have hen := w_energy hW u
    rw [eX, eY] at hen
    have hB₀e : √(‖Wm (wordAct (true :: S') (v j))‖ ^ 2 + ‖Wm (wordAct (false :: S') (v j))‖ ^ 2) = B₀ := rfl
    rw [hB₀e] at hen
    have hB₀sq : ‖Wm (wordAct (true :: S') (v j))‖ ^ 2 + ‖Wm (wordAct (false :: S') (v j))‖ ^ 2 = B₀ ^ 2 := by
      rw [← hB₀e, Real.sq_sqrt (by positivity)]
    rw [hB₀sq] at hen
    -- `-Δ w`
    have hD := allWords_polyAct hAj (deltaP 0)
    have hneg : negLapH u = wordAct S' (v (j + 1)) - (μ : ℂ) • w - polyAct (QL S') (v j) := by
      have h1 := lapTbar_eq_polyAct 0 u hw
      rw [lapTbar_zero] at h1
      have h2 : negLapH u = -polyAct (deltaP 0) w := by
        have : -(negLapH u) = polyAct (deltaP 0) w := h1
        rw [← this, neg_neg]
      have h3 := lapTbar_eq_polyAct 0 ⟨v j, AllWords.mem hAj []⟩ hAj
      rw [lapTbar_zero] at h3
      have h4 : polyAct (deltaP 0) (v j) = (μ : ℂ) • v j - v (j + 1) := by
        have : -(negLapH ⟨v j, AllWords.mem hAj []⟩) = polyAct (deltaP 0) (v j) := h3
        rw [← this, hstep j]
        abel
      rw [h2, lap_word hAj S', h4, wordAct_sub (allWords_smul hAj _) (hA (j + 1)), wordAct_smul hAj]
      abel
    have hN : ‖Wm w‖ ≤ A * (4 + 2 * l) ^ k * q ^ (k + 2 * j) * ((k + 2 * j).factorial : ℝ) := ih j S' hS'l
    have hN1 : ‖Wm (wordAct S' (v (j + 1)))‖ ≤ A * (4 + 2 * l) ^ k * q ^ (k + 2 * (j + 1)) * ((k + 2 * (j + 1)).factorial : ℝ) :=
      ih (j + 1) S' hS'l
    set a := A * (4 + 2 * l) ^ k * q ^ (k + 2 * j) * ((k + 2 * j).factorial : ℝ) with ha
    set b := A * (4 + 2 * l) ^ k * q ^ (k + 2 * (j + 1)) * ((k + 2 * (j + 1)).factorial : ℝ) with hb
    have ha0 : 0 ≤ a := by rw [ha]; positivity
    have hb0 : 0 ≤ b := by rw [hb]; positivity
    have hpoly : ‖Wm (polyAct (QL S') (v j))‖ ≤ (k : ℝ) * (2 * B₀) := by
      have h := norm_poly_le Wm (v j) (P := QL S') (c := 2) (B := B₀) (fun t ht => by
        obtain ⟨h1, h2⟩ := QL_mem S' t ht
        exact ⟨h1.le, hword t.2 (by rw [h2, hS'l])⟩) (by norm_num)
      rwa [QL_length, hS'l] at h
    have hinner : (⟪Wm (u : L2H'), Wm (negLapH u)⟫_ℂ).re ≤ a * b + 2 * k * a * B₀ := by
      rw [hneg]
      have e : Wm (wordAct S' (v (j + 1)) - (μ : ℂ) • w - polyAct (QL S') (v j))
          = Wm (wordAct S' (v (j + 1))) - (μ : ℂ) • Wm w - Wm (polyAct (QL S') (v j)) := by
        rw [map_sub, map_sub, map_smul]
      rw [e, inner_sub_right, inner_sub_right, inner_smul_right, Complex.sub_re, Complex.sub_re, Complex.re_ofReal_mul]
      have t1 : (⟪Wm w, Wm (wordAct S' (v (j + 1)))⟫_ℂ).re ≤ a * b :=
        (re_inner_W_le hW _ _).trans (mul_le_mul hN hN1 (norm_nonneg _) ha0)
      have t2 : 0 ≤ μ * (⟪Wm w, Wm w⟫_ℂ).re := by
        have : (⟪Wm w, Wm w⟫_ℂ).re = ‖Wm w‖ ^ 2 := by
          rw [inner_self_eq_norm_sq_to_K]; norm_cast
        rw [this]; positivity
      have t3 : -(⟪Wm w, Wm (polyAct (QL S') (v j))⟫_ℂ).re ≤ 2 * k * a * B₀ := by
        have h1 : -(⟪Wm w, Wm (polyAct (QL S') (v j))⟫_ℂ).re ≤ ‖Wm w‖ * ‖Wm (polyAct (QL S') (v j))‖ := by
          have := (Complex.abs_re_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) (Wm w) (Wm (polyAct (QL S') (v j))))
          linarith [neg_le_abs (⟪Wm w, Wm (polyAct (QL S') (v j))⟫_ℂ).re]
        refine h1.trans ((mul_le_mul hN hpoly (norm_nonneg _) ha0).trans (le_of_eq ?_))
        ring
      linarith
    have hquad : B₀ ^ 2 ≤ a * b + (2 * (k : ℝ) + 2 * l) * a * B₀ := by
      have h1 : 2 * l * ‖Wm (u : L2H')‖ * B₀ ≤ 2 * l * a * B₀ := by
        have : ‖Wm (u : L2H')‖ ≤ a := hN
        have h2 : 0 ≤ 2 * l * B₀ := by positivity
        nlinarith
      nlinarith
    have hsol := quad_solve hB₀0 ha0 hb0 (by positivity : (0 : ℝ) ≤ (2 * (k : ℝ) + 2 * l) * a) hquad
    exact hsol.trans (rec_arith hA0 hq hl rfl k j)

end Qschubert
