import Qschubert.KLPcCWd
import Qschubert.KLLift1b
import Qschubert.KLCor16a

/-!
# Words in weighted spaces, part 1: commutators

On vectors with all words: `[Y, X] = X` (`comm_YX_vec`), hence `Δ Z_S a = Z_S Δ a + Σ_i (±2) Z_{T_i} a`, a sum of `|S|` words of length `|S| + 1`
(`lap_word`, with the list `QL S`). Words are additive and homogeneous on such vectors (`wordAct_add`, `wordAct_smul`).
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set
open scoped ENNReal InnerProductSpace ComplexConjugate UpperHalfPlane

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

section

variable {a : L2H'} (hA : AllWords a)
include hA

lemma allWords_wordAct (S : List Bool) : AllWords (wordAct S a) := by
  have h := allWords_polyAct hA [((1 : ℂ), S)]
  have e : polyAct [((1 : ℂ), S)] a = wordAct S a := by
    rw [polyAct_cons, polyAct_nil, add_zero]
    show (1 : ℂ) • wordAct S a = wordAct S a
    rw [one_smul]
  rwa [e] at h

lemma wordAct_append (L S : List Bool) : wordAct (L ++ S) a = wordAct L (wordAct S a) := by
  induction L with
  | nil => rfl
  | cons z L ih =>
    have h1 := AllWords.mem hA (L ++ S)
    have h2 : wordAct L (wordAct S a) ∈ negLapH.domain := AllWords.mem (allWords_wordAct hA S) L
    rw [List.cons_append, wordAct_cons z _ h1, wordAct_cons z L h2]
    congr 1
    exact Subtype.ext ih

/-- `[Y, X] = X` on a vector with all words. -/
lemma comm_YX_vec : wordAct [false, true] a = wordAct [true, false] a + wordAct [true] a := by
  have hu : a ∈ negLapH.domain := AllWords.mem hA []
  set u : negLapH.domain := ⟨a, hu⟩ with hudef
  have hx : domX u ∈ negLapH.domain := by
    have h := AllWords.mem hA [true]
    rwa [wordAct_cons true [] hu] at h
  have hy : domY u ∈ negLapH.domain := by
    have h := AllWords.mem hA [false]
    rwa [wordAct_cons false [] hu] at h
  have e1 : wordAct [true] a = domX u := wordAct_cons true [] hu
  have e2 : wordAct [false] a = domY u := wordAct_cons false [] hu
  have e3 : wordAct [false, true] a = domY ⟨domX u, hx⟩ := by
    have h : wordAct [true] a ∈ negLapH.domain := e1 ▸ hx
    rw [wordAct_cons false [true] h]
    show domZ false _ = _
    simp only [domZ, Bool.false_eq_true, ite_false]
    congr 1
    exact Subtype.ext e1
  have e4 : wordAct [true, false] a = domX ⟨domY u, hy⟩ := by
    have h : wordAct [false] a ∈ negLapH.domain := e2 ▸ hy
    rw [wordAct_cons true [false] h]
    show domZ true _ = _
    simp only [domZ, ite_true]
    congr 1
    exact Subtype.ext e2
  rw [e1, e3, e4, ← sub_eq_zero]
  set D := domY ⟨domX u, hx⟩ - (domX ⟨domY u, hy⟩ + domX u) with hD
  have hperp : ∀ P : testFn, ⟪toL2 P, D⟫_ℂ = 0 := fun P => by
    have a1 := inner_Y_dom P ⟨domX u, hx⟩
    have a2 := inner_X_dom (vfTest Complex.I P) u
    have a3 := inner_X_dom P u
    have a4 := inner_X_dom P ⟨domY u, hy⟩
    have a5 := inner_Y_dom (vfTest 1 P) u
    have a6 := inner_X_dom (vfTest Complex.I P) u
    have hc := vf_comm P
    have a7 : ⟪toL2 (vfTest Complex.I (vfTest 1 P)), (u : L2H')⟫_ℂ
        = ⟪toL2 (vfTest 1 (vfTest Complex.I P)), (u : L2H')⟫_ℂ + ⟪toL2 (vfTest 1 P), (u : L2H')⟫_ℂ := by
      rw [hc, map_add, inner_add_left]
    simp only [Subtype.coe_mk] at a1 a4
    rw [hD, inner_sub_right, inner_add_right]
    have b1 : ⟪toL2 P, domY ⟨domX u, hx⟩⟫_ℂ = ⟪toL2 P, domX u⟫_ℂ - ⟪toL2 (vfTest Complex.I P), domX u⟫_ℂ := by
      rw [a1]; ring
    have b2 : ⟪toL2 (vfTest Complex.I P), domX u⟫_ℂ = -⟪toL2 (vfTest 1 (vfTest Complex.I P)), (u : L2H')⟫_ℂ := by
      rw [a2]; ring
    have b3 : ⟪toL2 P, domX u⟫_ℂ = -⟪toL2 (vfTest 1 P), (u : L2H')⟫_ℂ := by
      rw [a3]; ring
    have b4 : ⟪toL2 P, domX ⟨domY u, hy⟩⟫_ℂ = -⟪toL2 (vfTest 1 P), domY u⟫_ℂ := by
      rw [a4]; ring
    have b5 : ⟪toL2 (vfTest 1 P), domY u⟫_ℂ = ⟪toL2 (vfTest 1 P), (u : L2H')⟫_ℂ - ⟪toL2 (vfTest Complex.I (vfTest 1 P)), (u : L2H')⟫_ℂ := by
      rw [a5]; ring
    rw [b1, b2, b3, b4, b5, a7]
    ring
  have hzero : D = 0 := by
    refine eq_zero_of_perp fun P => ?_
    have h1 := hperp P
    have h2 := hperp (lapTest P)
    have e1 : ⟪D, toL2 P⟫_ℂ = 0 := by rw [← inner_conj_symm, h1, map_zero]
    have e2 : ⟪D, toL2 (lapTest P)⟫_ℂ = 0 := by rw [← inner_conj_symm, h2, map_zero]
    rw [inner_sub_right, e1, e2, sub_zero]
  exact hzero

end

/-! ### Linearity of words on vectors on which all words act -/

lemma words_add {u v : L2H'} (hu : AllWords u) (hv : AllWords v) (L : List Bool) :
    WordDom L (u + v) ∧ wordAct L (u + v) = wordAct L u + wordAct L v := by
  induction L with
  | nil => exact ⟨trivial, rfl⟩
  | cons z L ih =>
    obtain ⟨hd, he⟩ := ih
    have h1 := AllWords.mem hu L
    have h2 := AllWords.mem hv L
    have hm : wordAct L (u + v) ∈ negLapH.domain := by rw [he]; exact Submodule.add_mem _ h1 h2
    refine ⟨⟨hd, hm⟩, ?_⟩
    rw [wordAct_cons z L hm, wordAct_cons z L h1, wordAct_cons z L h2]
    have e : (⟨wordAct L (u + v), hm⟩ : negLapH.domain) = ⟨wordAct L u, h1⟩ + ⟨wordAct L v, h2⟩ := Subtype.ext he
    rw [e]
    cases z
    · simp only [domZ, Bool.false_eq_true, ite_false]
      exact domY_add' _ _
    · simp only [domZ, ite_true]
      exact domX_add' _ _

lemma words_smul {u : L2H'} (hu : AllWords u) (c : ℂ) (L : List Bool) :
    WordDom L (c • u) ∧ wordAct L (c • u) = c • wordAct L u := by
  induction L with
  | nil => exact ⟨trivial, rfl⟩
  | cons z L ih =>
    obtain ⟨hd, he⟩ := ih
    have h1 := AllWords.mem hu L
    have hm : wordAct L (c • u) ∈ negLapH.domain := by rw [he]; exact Submodule.smul_mem _ c h1
    refine ⟨⟨hd, hm⟩, ?_⟩
    rw [wordAct_cons z L hm, wordAct_cons z L h1]
    have e : (⟨wordAct L (c • u), hm⟩ : negLapH.domain) = c • ⟨wordAct L u, h1⟩ := Subtype.ext he
    rw [e, domZ_smul]

lemma allWords_add {u v : L2H'} (hu : AllWords u) (hv : AllWords v) : AllWords (u + v) := fun S => (words_add hu hv S).1

lemma allWords_smul {u : L2H'} (hu : AllWords u) (c : ℂ) : AllWords (c • u) := fun S => (words_smul hu c S).1

lemma wordAct_add {u v : L2H'} (hu : AllWords u) (hv : AllWords v) (L : List Bool) :
    wordAct L (u + v) = wordAct L u + wordAct L v := (words_add hu hv L).2

lemma wordAct_smul {u : L2H'} (hu : AllWords u) (c : ℂ) (L : List Bool) : wordAct L (c • u) = c • wordAct L u :=
  (words_smul hu c L).2

lemma allWords_sub {u v : L2H'} (hu : AllWords u) (hv : AllWords v) : AllWords (u - v) := by
  have e : u - v = u + (-1 : ℂ) • v := by rw [neg_one_smul, sub_eq_add_neg]
  rw [e]
  exact allWords_add hu (allWords_smul hv _)

lemma wordAct_sub {u v : L2H'} (hu : AllWords u) (hv : AllWords v) (L : List Bool) :
    wordAct L (u - v) = wordAct L u - wordAct L v := by
  have e : u - v = u + (-1 : ℂ) • v := by rw [neg_one_smul, sub_eq_add_neg]
  rw [e, wordAct_add hu (allWords_smul hv _), wordAct_smul hv, neg_one_smul, sub_eq_add_neg]

/-! ### The commutator of `Δ` with a word -/

lemma polyAct_delta0 (u : L2H') :
    polyAct (deltaP 0) u = wordAct [true, true] u + wordAct [false, false] u - wordAct [false] u := by
  simp [deltaP, polyAct_cons, polyAct_nil, sub_eq_add_neg]
  abel

/-- The words of `[Δ, Z_S]`: `[Δ, X] = 2XY`, `[Δ, Y] = -2X²`. -/
def QL : List Bool → WP
  | [] => []
  | true :: S => ((2 : ℂ), [true, false] ++ S) :: leftW [true] (QL S)
  | false :: S => ((-2 : ℂ), [true, true] ++ S) :: leftW [false] (QL S)

lemma QL_length (S : List Bool) : (QL S).length = S.length := by
  induction S with
  | nil => rfl
  | cons z S ih => cases z <;> simp [QL, leftW, ih]

lemma QL_mem (S : List Bool) : ∀ t ∈ QL S, ‖t.1‖ = 2 ∧ t.2.length = S.length + 1 := by
  induction S with
  | nil => intro t ht; simp [QL] at ht
  | cons z S ih =>
    intro t ht
    cases z
    · simp only [QL, List.mem_cons, leftW, List.mem_map] at ht
      rcases ht with rfl | ⟨t', ht', rfl⟩
      · simp
      · obtain ⟨h1, h2⟩ := ih t' ht'
        simp [h1, h2]
    · simp only [QL, List.mem_cons, leftW, List.mem_map] at ht
      rcases ht with rfl | ⟨t', ht', rfl⟩
      · simp
      · obtain ⟨h1, h2⟩ := ih t' ht'
        simp [h1, h2]

section comm

variable {a : L2H'} (hA : AllWords a)
include hA

/-- `[Y, X] = X` inside a word. -/
lemma comm_gen (L S : List Bool) :
    wordAct (L ++ [false, true] ++ S) a = wordAct (L ++ [true, false] ++ S) a + wordAct (L ++ [true] ++ S) a := by
  have hw := allWords_wordAct hA S
  have h := comm_YX_vec hw
  have e1 : wordAct (L ++ [false, true] ++ S) a = wordAct L (wordAct [false, true] (wordAct S a)) := by
    rw [wordAct_append hA (L ++ [false, true]) S, wordAct_append hw L [false, true]]
  have e2 : wordAct (L ++ [true, false] ++ S) a = wordAct L (wordAct [true, false] (wordAct S a)) := by
    rw [wordAct_append hA (L ++ [true, false]) S, wordAct_append hw L [true, false]]
  have e3 : wordAct (L ++ [true] ++ S) a = wordAct L (wordAct [true] (wordAct S a)) := by
    rw [wordAct_append hA (L ++ [true]) S, wordAct_append hw L [true]]
  rw [e1, e2, e3, h, wordAct_add (allWords_wordAct hw _) (allWords_wordAct hw _)]

/-- `[Δ, X] = 2XY`. -/
lemma lap_X : polyAct (deltaP 0) (wordAct [true] a) = wordAct [true] (polyAct (deltaP 0) a) + (2 : ℂ) • wordAct [true, false] a := by
  have hXX := allWords_wordAct hA [true, true]
  have hYY := allWords_wordAct hA [false, false]
  have hY := allWords_wordAct hA [false]
  have i1 : wordAct [false, true] a = wordAct [true, false] a + wordAct [true] a := comm_gen hA [] []
  have i2 : wordAct [false, false, true] a = wordAct [false, true, false] a + wordAct [false, true] a := comm_gen hA [false] []
  have i3 : wordAct [false, true, false] a = wordAct [true, false, false] a + wordAct [true, false] a := comm_gen hA [] [false]
  have a1 : wordAct [true, true] (wordAct [true] a) = wordAct [true, true, true] a := (wordAct_append hA [true, true] [true]).symm
  have a2 : wordAct [false, false] (wordAct [true] a) = wordAct [false, false, true] a := (wordAct_append hA [false, false] [true]).symm
  have a3 : wordAct [false] (wordAct [true] a) = wordAct [false, true] a := (wordAct_append hA [false] [true]).symm
  have b1 : wordAct [true] (wordAct [true, true] a) = wordAct [true, true, true] a := (wordAct_append hA [true] [true, true]).symm
  have b2 : wordAct [true] (wordAct [false, false] a) = wordAct [true, false, false] a := (wordAct_append hA [true] [false, false]).symm
  have b3 : wordAct [true] (wordAct [false] a) = wordAct [true, false] a := (wordAct_append hA [true] [false]).symm
  rw [polyAct_delta0, polyAct_delta0, wordAct_sub (allWords_add hXX hYY) hY, wordAct_add hXX hYY, a1, a2, a3, b1, b2, b3, i2, i3, i1]
  module

/-- `[Δ, Y] = -2X²`. -/
lemma lap_Y : polyAct (deltaP 0) (wordAct [false] a) = wordAct [false] (polyAct (deltaP 0) a) + (-2 : ℂ) • wordAct [true, true] a := by
  have hXX := allWords_wordAct hA [true, true]
  have hYY := allWords_wordAct hA [false, false]
  have hY := allWords_wordAct hA [false]
  have i4 : wordAct [false, true, true] a = wordAct [true, false, true] a + wordAct [true, true] a := comm_gen hA [] [true]
  have i5 : wordAct [true, false, true] a = wordAct [true, true, false] a + wordAct [true, true] a := comm_gen hA [true] []
  have a1 : wordAct [true, true] (wordAct [false] a) = wordAct [true, true, false] a := (wordAct_append hA [true, true] [false]).symm
  have a2 : wordAct [false, false] (wordAct [false] a) = wordAct [false, false, false] a := (wordAct_append hA [false, false] [false]).symm
  have a3 : wordAct [false] (wordAct [false] a) = wordAct [false, false] a := (wordAct_append hA [false] [false]).symm
  have b1 : wordAct [false] (wordAct [true, true] a) = wordAct [false, true, true] a := (wordAct_append hA [false] [true, true]).symm
  have b2 : wordAct [false] (wordAct [false, false] a) = wordAct [false, false, false] a := (wordAct_append hA [false] [false, false]).symm
  have b3 : wordAct [false] (wordAct [false] a) = wordAct [false, false] a := (wordAct_append hA [false] [false]).symm
  rw [polyAct_delta0, polyAct_delta0, wordAct_sub (allWords_add hXX hYY) hY, wordAct_add hXX hYY, a1, a2, a3, b1, b2, i4, i5]
  module

/-- **`Δ Z_S a = Z_S Δ a + [Δ, Z_S] a`**, with `[Δ, Z_S]` the word polynomial `QL S`. -/
theorem lap_word (S : List Bool) :
    polyAct (deltaP 0) (wordAct S a) = wordAct S (polyAct (deltaP 0) a) + polyAct (QL S) a := by
  induction S with
  | nil => simp [wordAct, QL, polyAct_nil]
  | cons z S ih =>
    have hw := allWords_wordAct hA S
    have hD := allWords_polyAct hA (deltaP 0)
    have e0 : wordAct (z :: S) a = wordAct [z] (wordAct S a) := wordAct_append hA [z] S
    have e1 : wordAct [z] (wordAct S (polyAct (deltaP 0) a)) = wordAct (z :: S) (polyAct (deltaP 0) a) := (wordAct_append hD [z] S).symm
    have e2 : wordAct [z] (polyAct (QL S) a) = polyAct (leftW [z] (QL S)) a := (poly_words hA (QL S) [z]).2
    rw [e0]
    cases z
    · rw [lap_Y hw, ih, wordAct_add (allWords_wordAct hD S) (allWords_polyAct hA (QL S)), e1, e2]
      have e3 : wordAct [true, true] (wordAct S a) = wordAct ([true, true] ++ S) a := (wordAct_append hA [true, true] S).symm
      rw [e3]
      show _ = _ + polyAct (((-2 : ℂ), [true, true] ++ S) :: leftW [false] (QL S)) a
      rw [polyAct_cons]
      abel
    · rw [lap_X hw, ih, wordAct_add (allWords_wordAct hD S) (allWords_polyAct hA (QL S)), e1, e2]
      have e3 : wordAct [true, false] (wordAct S a) = wordAct ([true, false] ++ S) a := (wordAct_append hA [true, false] S).symm
      rw [e3]
      show _ = _ + polyAct (((2 : ℂ), [true, false] ++ S) :: leftW [true] (QL S)) a
      rw [polyAct_cons]
      abel

end comm

/-- The norm of a bounded operator on a word polynomial. -/
lemma norm_poly_le (A : L2H' →L[ℂ] L2H') (u : L2H') {P : WP} {c B : ℝ} (h : ∀ t ∈ P, ‖t.1‖ ≤ c ∧ ‖A (wordAct t.2 u)‖ ≤ B)
    (hc : 0 ≤ c) : ‖A (polyAct P u)‖ ≤ P.length * (c * B) := by
  induction P with
  | nil => simp [polyAct_nil]
  | cons t P ih =>
    have ht := h t (by simp)
    have hP := ih fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    rw [polyAct_cons, map_add, map_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul]
    have h1 : ‖t.1‖ * ‖A (wordAct t.2 u)‖ ≤ c * B := mul_le_mul ht.1 ht.2 (norm_nonneg _) hc
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

end Qschubert
