import Qschubert.FdbWord

/-!
# Words of `X`, `Y` applied to `X₀`

Part (a) of Lemma `lem:fdb`: `|Z_S X₀| ≤ 2 · 2^j X₀` on `ℍ` for every word `Z_S` of length `j`,
`X₀ = cosh d(i, ·) = hF⁻¹`.

By `wordR_hpow` at `β = -1`, `Z_S X₀ = X₀ · P_S(ξ, υ)` with `P_S = PS (-1) S`. The polynomials
`a υ + b ξ + c (2 - υ)` (the space `𝔄 / X₀` of the manuscript, with the basis `y, x, (x² + 1)/y`
divided by `X₀`) are stable under `D_X` and `D_Y` at `β = -1`, with `‖D_X‖ ≤ 2`, `‖D_Y‖ ≤ 1` in the
`ℓ¹` norm of `(a, b, c)`; and `|υ|, |2 - υ| ≤ 2`, `|ξ| ≤ 1`.
-/

namespace Qschubert

open MvPolynomial

/-- The polynomial `a υ + b ξ + c (2 - υ)`. -/
noncomputable def spanP (a b c : ℝ) : P2 := C a * X 1 + C b * X 0 + C c * (C 2 - X 1)

lemma pderiv0_spanP (a b c : ℝ) : pderiv (0 : Fin 2) (spanP a b c) = C b := by
  simp [spanP, pderiv_X_of_ne (show (1 : Fin 2) ≠ 0 by decide)]

lemma pderiv1_spanP (a b c : ℝ) : pderiv (1 : Fin 2) (spanP a b c) = C a - C c := by
  simp [spanP, pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
  ring

lemma DY_spanP (a b c : ℝ) : DY (-1) (spanP a b c) = spanP a 0 (-c) := by
  rw [DY, pderiv0_spanP, pderiv1_spanP]
  simp only [spanP, map_neg, map_zero, map_one, map_ofNat]
  ring

lemma DX_spanP (a b c : ℝ) : DX (-1) (spanP a b c) = spanP b (2 * c) 0 := by
  rw [DX, pderiv0_spanP, pderiv1_spanP]
  simp only [spanP, map_neg, map_zero, map_one, map_ofNat, map_mul]
  ring

/-- `PS (-1) S = a υ + b ξ + c (2 - υ)` with `|a| + |b| + |c| ≤ 2^{|S|}`. -/
lemma PS_neg_one_span (S : List Bool) :
    ∃ a b c : ℝ, PS (-1) S = spanP a b c ∧ |a| + |b| + |c| ≤ 2 ^ S.length := by
  induction S with
  | nil =>
    refine ⟨1 / 2, 0, 1 / 2, ?_, ?_⟩
    · simp only [PS, spanP, map_zero, zero_mul, add_zero]
      have e : (C (1 / 2 : ℝ) : P2) * C 2 = 1 := by rw [← C_mul]; norm_num
      linear_combination (-1 : P2) * e
    · norm_num
  | cons z S ih =>
    obtain ⟨a, b, c, h, hn⟩ := ih
    have hp : (2 : ℝ) ^ (z :: S).length = 2 * 2 ^ S.length := by
      simp [List.length_cons, pow_succ]; ring
    have h0 : (0 : ℝ) ≤ 2 ^ S.length := by positivity
    rw [hp]
    cases z with
    | false =>
      refine ⟨a, 0, -c, ?_, ?_⟩
      · simp only [PS, DZ, h, Bool.false_eq_true, ↓reduceIte, DY_spanP]
      · have := abs_nonneg b
        simp only [abs_zero, abs_neg]
        linarith
    | true =>
      refine ⟨b, 2 * c, 0, ?_, ?_⟩
      · simp only [PS, DZ, h, ↓reduceIte, DX_spanP]
      · have := abs_nonneg a
        have := abs_nonneg b
        rw [abs_zero, abs_mul, abs_two]
        linarith

/-- **Lemma `lem:fdb`(a)**: `|Z_S X₀| ≤ 2 · 2^j X₀` on `ℍ` for every word `S` of length `j` in
`X = y∂ₓ`, `Y = y∂_y`, where `X₀ = hF⁻¹ = cosh d(i, ·)`. -/
theorem word_X0_le (S : List Bool) {w : ℂ} (hw : 0 < w.im) :
    |wordR S (fun u => hF u ^ (-1 : ℝ)) w| ≤ 2 * 2 ^ S.length * hF w ^ (-1 : ℝ) := by
  rw [wordR_hpow (-1) S hw]
  obtain ⟨a, b, c, h, hn⟩ := PS_neg_one_span S
  have hpos : 0 < hF w ^ (-1 : ℝ) := Real.rpow_pos_of_pos (hF_pos hw) _
  rw [abs_mul, abs_of_pos hpos, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ hpos.le
  have hx := abs_xiF_le w
  have hu0 := upF_nonneg w
  have hu2 := upF_le_two w
  have ev_eq : ev (PS (-1) S) (xiF w) (upF w) = a * upF w + b * xiF w + c * (2 - upF w) := by
    rw [h]; simp [ev, spanP]
  rw [ev_eq]
  have h1 : |a * upF w| ≤ 2 * |a| := by
    rw [abs_mul, abs_of_nonneg hu0]; nlinarith [abs_nonneg a]
  have h2 : |b * xiF w| ≤ 2 * |b| := by
    rw [abs_mul]; nlinarith [abs_nonneg b, abs_nonneg (xiF w)]
  have h3 : |c * (2 - upF w)| ≤ 2 * |c| := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 - upF w)]; nlinarith [abs_nonneg c]
  calc |a * upF w + b * xiF w + c * (2 - upF w)|
      ≤ |a * upF w| + |b * xiF w| + |c * (2 - upF w)| := abs_add_three _ _ _
    _ ≤ 2 * (|a| + |b| + |c|) := by linarith
    _ ≤ 2 * 2 ^ S.length := by linarith

end Qschubert
