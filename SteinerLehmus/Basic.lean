import Mathlib

/-!
# The Steiner–Lehmus theorem

If the internal angle bisectors from `B` and `C` of a non-degenerate triangle `ABC` have equal
length, then `AB = AC`.

The internal bisector from `B` is described geometrically: its foot `E` lies on the closed
segment `AC` (`Wbtw ℝ A E C`) and the unoriented angles `∠ A B E` and `∠ E B C` are equal.
Its length is the genuine Euclidean distance `dist B E`.

Proof strategy (coordinate certificate). Put `u = A -ᵥ B`, `w = C -ᵥ B`, `E = lineMap A C t`,
so `E -ᵥ B = (1 - t) • u + t • w`. With `x = ‖u‖`, `y = ‖w‖`, `p = ⟪u, w⟫` everything becomes
polynomial in `x, y, p, t`:
* the bisector condition gives `(x * y - p) * ((1 - t) * x - t * y) = 0`, and `p < x * y`
  (strict Cauchy–Schwarz, from non-collinearity), so `(1 - t) * x = t * y`;
* `‖E -ᵥ B‖² * (x + y)² = x * y * ((x + y)² - ‖A -ᵥ C‖²)` then follows by `linear_combination`
  (the bisector-length formula, `bisector_foot_sq`);
* equating the two bisector-length formulas, `(b - c) * K = 0` with an explicit positive `K`
  (`linear_combination` again).
-/

namespace SteinerLehmus

open EuclideanGeometry InnerProductGeometry
open scoped InnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Algebraic core: the two cleared bisector-length formulas force `b = c`
(`a = BC`, `b = CA`, `c = AB`, `L` the common bisector length). -/
theorem algebraic_core {a b c L : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : L ^ 2 * (a + c) ^ 2 = a * c * ((a + c) ^ 2 - b ^ 2))
    (h2 : L ^ 2 * (a + b) ^ 2 = a * b * ((a + b) ^ 2 - c ^ 2)) : b = c := by
  have hK : 0 < a * (a + b + c) * (a ^ 3 + a ^ 2 * b + a ^ 2 * c + 3 * a * b * c + b ^ 2 * c
      + b * c ^ 2) := by positivity
  have key : (b - c) * (a * (a + b + c) * (a ^ 3 + a ^ 2 * b + a ^ 2 * c + 3 * a * b * c
      + b ^ 2 * c + b * c ^ 2)) = 0 := by
    linear_combination (a + b) ^ 2 * h1 - (a + c) ^ 2 * h2
  rcases mul_eq_zero.1 key with h | h
  · linarith
  · exact absurd h hK.ne'

/-- Bridge: the length of the internal bisector from `B`, whose foot `E` lies on segment `AC`
with `∠ A B E = ∠ E B C`, satisfies the classical bisector-length formula
`BE² (BA + BC)² = BA · BC ((BA + BC)² - AC²)`. -/
theorem bisector_foot_sq {A B C E : P} (hABC : ¬Collinear ℝ ({A, B, C} : Set P))
    (hE : Wbtw ℝ A E C) (hbis : ∠ A B E = ∠ E B C) :
    dist B E ^ 2 * (dist B A + dist B C) ^ 2 =
      dist B A * dist B C * ((dist B A + dist B C) ^ 2 - dist A C ^ 2) := by
  have hEB : E ≠ B := by
    rintro rfl
    apply hABC
    have h := collinear_insert_of_mem_affineSpan_pair hE.mem_affineSpan
    have hs : ({A, E, C} : Set P) = {E, A, C} := Set.insert_comm _ _ _
    rwa [hs]
  obtain ⟨t, -, rfl⟩ := hE
  set u : V := A -ᵥ B with hu
  set w : V := C -ᵥ B with hw
  set v : V := AffineMap.lineMap A C t -ᵥ B with hvdef
  have hv : v = (1 - t) • u + t • w := by
    rw [hvdef, AffineMap.lineMap_apply, vadd_vsub_assoc, hu, hw,
      ← vsub_sub_vsub_cancel_right C A B]
    module
  have hx : 0 < ‖u‖ := norm_pos_iff.2 (vsub_ne_zero.2 (ne₁₂_of_not_collinear hABC))
  have hy : 0 < ‖w‖ := norm_pos_iff.2 (vsub_ne_zero.2 (ne₂₃_of_not_collinear hABC).symm)
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 (vsub_ne_zero.2 hEB)
  -- strict Cauchy–Schwarz from `0 < ∠ A B C`
  have hp : ⟪u, w⟫_ℝ < ‖u‖ * ‖w‖ := by
    have h0 : 0 < ∠ A B C := angle_pos_of_not_collinear hABC
    have hcos : Real.cos (∠ A B C) < 1 := by
      rw [← Real.cos_zero]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (angle_le_pi _ _ _) h0
    rw [EuclideanGeometry.angle, cos_angle] at hcos
    rwa [div_lt_one (by positivity)] at hcos
  have hcomm : ⟪w, u⟫_ℝ = ⟪u, w⟫_ℝ := real_inner_comm _ _
  have huv : ⟪u, v⟫_ℝ = (1 - t) * ‖u‖ ^ 2 + t * ⟪u, w⟫_ℝ := by
    rw [hv, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
  have hvw : ⟪v, w⟫_ℝ = (1 - t) * ⟪u, w⟫_ℝ + t * ‖w‖ ^ 2 := by
    rw [hv, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
  have hvv : ‖v‖ ^ 2 = (1 - t) ^ 2 * ‖u‖ ^ 2 + 2 * t * (1 - t) * ⟪u, w⟫_ℝ + t ^ 2 * ‖w‖ ^ 2 := by
    rw [hv, norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
    ring
  -- the bisector condition, as an equation of cosines
  have hcos := congrArg Real.cos hbis
  rw [EuclideanGeometry.angle, EuclideanGeometry.angle, ← hu, ← hw, ← hvdef, cos_angle,
    cos_angle, huv, hvw, div_eq_div_iff (by positivity) (by positivity)] at hcos
  have hlin : (1 - t) * ‖u‖ - t * ‖w‖ = 0 := by
    have h1 : (‖u‖ * ‖w‖ - ⟪u, w⟫_ℝ) * ((1 - t) * ‖u‖ - t * ‖w‖) * ‖v‖ = 0 := by
      linear_combination hcos
    rcases mul_eq_zero.1 h1 with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h (by linarith)
      · exact h
    · exact absurd h hvn.ne'
  have hAC : ‖A -ᵥ C‖ ^ 2 = ‖u‖ ^ 2 - 2 * ⟪u, w⟫_ℝ + ‖w‖ ^ 2 := by
    rw [← vsub_sub_vsub_cancel_right A C B, ← hu, ← hw, norm_sub_sq_real]
  rw [dist_comm B, dist_eq_norm_vsub V, ← hvdef, dist_comm B A, dist_eq_norm_vsub V, ← hu,
    dist_comm B C, dist_eq_norm_vsub V, ← hw, dist_eq_norm_vsub V, hAC]
  linear_combination (‖u‖ + ‖w‖) ^ 2 * hvv + (2 * ⟪u, w⟫_ℝ * t * ‖u‖ + 2 * ⟪u, w⟫_ℝ * t * ‖w‖
    - 2 * ⟪u, w⟫_ℝ * ‖w‖ - t * ‖u‖ ^ 3 - t * ‖u‖ ^ 2 * ‖w‖ - t * ‖u‖ * ‖w‖ ^ 2 - t * ‖w‖ ^ 3
    + ‖u‖ ^ 3 + 2 * ‖u‖ ^ 2 * ‖w‖ - ‖u‖ * ‖w‖ ^ 2) * hlin

/-- **Steiner–Lehmus theorem.** In a non-degenerate triangle `ABC`, let `E` be the foot on `AC`
of the internal bisector from `B` and `F` the foot on `AB` of the internal bisector from `C`.
If `BE = CF`, then `AB = AC`. -/
theorem steiner_lehmus {A B C E F : P} (hABC : ¬Collinear ℝ ({A, B, C} : Set P))
    (hE : Wbtw ℝ A E C) (hbisB : ∠ A B E = ∠ E B C)
    (hF : Wbtw ℝ A F B) (hbisC : ∠ A C F = ∠ F C B)
    (heq : dist B E = dist C F) : dist A B = dist A C := by
  have hACB : ¬Collinear ℝ ({A, C, B} : Set P) := by
    rwa [Set.pair_comm C B]
  have hB := bisector_foot_sq hABC hE hbisB
  have hC := bisector_foot_sq hACB hF hbisC
  rw [dist_comm B A] at hB
  rw [dist_comm C A, dist_comm C B, ← heq] at hC
  have ha : 0 < dist B C := dist_pos.2 (ne₂₃_of_not_collinear hABC)
  have hb : 0 < dist A C := dist_pos.2 (ne₁₃_of_not_collinear hABC)
  have hc : 0 < dist A B := dist_pos.2 (ne₁₂_of_not_collinear hABC)
  exact (algebraic_core (L := dist B E) ha hb hc
    (by linear_combination hB) (by linear_combination hC)).symm

end SteinerLehmus
