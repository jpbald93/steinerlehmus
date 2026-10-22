import SteinerLehmus.Basic

/-!
# Layer 14: Mathlib-only restatement and a witness for Steiner–Lehmus

`l14_steiner_lehmus` mentions only Mathlib notions (`Collinear`, `Wbtw`, `EuclideanGeometry.angle`,
`dist`); it is the library theorem itself, whose statement was already namespace-free.
`l14w_steiner_lehmus` is an explicit configuration in `ℂ` satisfying every hypothesis. Since the
theorem forces `AB = AC`, every witness is an isosceles triangle: here `A = 14 + 48i`, `B = 0`,
`C = 28` (`AB = AC = 50`, `BC = 28`), with bisector feet `E = (896 + 672i)/39` on `AC` and
`F = (196 + 672i)/39` on `AB`, and `BE = CF = 1120/39`. The two feet are distinct from each other
and from the vertices.
-/

namespace SteinerLehmus

open EuclideanGeometry InnerProductGeometry Complex ComplexConjugate

/-- **Steiner–Lehmus**, Mathlib-only statement. -/
theorem l14_steiner_lehmus {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] {A B C E F : P}
    (hABC : ¬Collinear ℝ ({A, B, C} : Set P))
    (hE : Wbtw ℝ A E C) (hbisB : ∠ A B E = ∠ E B C)
    (hF : Wbtw ℝ A F B) (hbisC : ∠ A C F = ∠ F C B)
    (heq : dist B E = dist C F) : dist A B = dist A C :=
  steiner_lehmus hABC hE hbisB hF hbisC heq

/-! ### Bridges for explicit configurations in `ℂ` -/

theorem l14b_norm_eq {z : ℂ} {r : ℝ} (hr : 0 ≤ r) (h : z.re ^ 2 + z.im ^ 2 = r ^ 2) : ‖z‖ = r := by
  rw [Complex.norm_def, Complex.normSq_apply, ← sq, ← sq, h, Real.sqrt_sq hr]

theorem l14b_not_collinear {a b c : ℂ}
    (h : (b - a).re * (c - a).im - (b - a).im * (c - a).re ≠ 0) :
    ¬Collinear ℝ ({a, b, c} : Set ℂ) := by
  rw [collinear_iff_of_mem (p₀ := a) (by simp)]
  rintro ⟨v, hv⟩
  obtain ⟨s, hs⟩ := hv b (by simp)
  obtain ⟨t, ht⟩ := hv c (by simp)
  apply h
  rw [hs, ht]
  simp only [vadd_eq_add, add_sub_cancel_right, Complex.real_smul, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem l14b_angle_eq {a b c d e f : ℂ} (hab : a - b ≠ 0) (hcb : c - b ≠ 0) (hed : e - d ≠ 0)
    (hfd : f - d ≠ 0)
    (h : ((c - b) * conj (a - b)).re * (‖e - d‖ * ‖f - d‖) =
      ((f - d) * conj (e - d)).re * (‖a - b‖ * ‖c - b‖)) :
    ∠ a b c = ∠ e d f := by
  unfold EuclideanGeometry.angle InnerProductGeometry.angle
  congr 1
  rw [vsub_eq_sub, vsub_eq_sub, vsub_eq_sub, vsub_eq_sub, Complex.inner, Complex.inner,
    div_eq_div_iff (by positivity) (by positivity)]
  exact h

/-! ### Witness -/

/-- Witness for `l14_steiner_lehmus` (necessarily isosceles): all hypotheses hold, the triangle
is non-degenerate, and the bisector feet `E ≠ F` are distinct from the vertices. -/
theorem l14w_steiner_lehmus :
    ¬Collinear ℝ ({(14 + 48 * I : ℂ), 0, 28} : Set ℂ) ∧
    Wbtw ℝ (14 + 48 * I : ℂ) ((896 + 672 * I) / 39) 28 ∧
    ∠ (14 + 48 * I : ℂ) 0 ((896 + 672 * I) / 39) = ∠ ((896 + 672 * I) / 39 : ℂ) 0 28 ∧
    Wbtw ℝ (14 + 48 * I : ℂ) ((196 + 672 * I) / 39) 0 ∧
    ∠ (14 + 48 * I : ℂ) 28 ((196 + 672 * I) / 39) = ∠ ((196 + 672 * I) / 39 : ℂ) 28 0 ∧
    dist (0 : ℂ) ((896 + 672 * I) / 39) = dist (28 : ℂ) ((196 + 672 * I) / 39) ∧
    dist (0 : ℂ) ((896 + 672 * I) / 39) = 1120 / 39 ∧
    dist (14 + 48 * I : ℂ) 0 = 50 ∧ dist (14 + 48 * I : ℂ) 28 = 50 ∧ dist (0 : ℂ) 28 = 28 ∧
    ((896 + 672 * I) / 39 : ℂ) ≠ (196 + 672 * I) / 39 ∧
    ((896 + 672 * I) / 39 : ℂ) ≠ 14 + 48 * I ∧ ((896 + 672 * I) / 39 : ℂ) ≠ 28 ∧
    ((196 + 672 * I) / 39 : ℂ) ≠ 14 + 48 * I ∧ ((196 + 672 * I) / 39 : ℂ) ≠ 0 := by
  have nBE : ‖(0 : ℂ) - (896 + 672 * I) / 39‖ = 1120 / 39 :=
    l14b_norm_eq (by norm_num) (by norm_num)
  have nCF : ‖(28 : ℂ) - (196 + 672 * I) / 39‖ = 1120 / 39 :=
    l14b_norm_eq (by norm_num) (by norm_num)
  have nE : ‖(896 + 672 * I) / 39 - (0 : ℂ)‖ = 1120 / 39 :=
    l14b_norm_eq (by norm_num) (by norm_num)
  have nF : ‖(196 + 672 * I) / 39 - (28 : ℂ)‖ = 1120 / 39 :=
    l14b_norm_eq (by norm_num) (by norm_num)
  have nA0 : ‖(14 + 48 * I : ℂ) - 0‖ = 50 := l14b_norm_eq (by norm_num) (by norm_num)
  have nA28 : ‖(14 + 48 * I : ℂ) - 28‖ = 50 := l14b_norm_eq (by norm_num) (by norm_num)
  have n28 : ‖(28 : ℂ) - 0‖ = 28 := l14b_norm_eq (by norm_num) (by norm_num)
  have n0 : ‖(0 : ℂ) - 28‖ = 28 := l14b_norm_eq (by norm_num) (by norm_num)
  refine ⟨l14b_not_collinear (by norm_num), ⟨25 / 39, ⟨by norm_num, by norm_num⟩, ?_⟩, ?_,
    ⟨25 / 39, ⟨by norm_num, by norm_num⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [AffineMap.lineMap_apply]; apply Complex.ext <;> norm_num
  · refine l14b_angle_eq (by norm_num [Complex.ext_iff]) (by norm_num [Complex.ext_iff])
      (by norm_num [Complex.ext_iff]) (by norm_num [Complex.ext_iff]) ?_
    rw [nA0, nE, n28]; norm_num [map_div₀, Complex.conj_I, map_ofNat, Complex.div_re, Complex.div_im, Complex.normSq_apply]
  · rw [AffineMap.lineMap_apply]; apply Complex.ext <;> norm_num
  · refine l14b_angle_eq (by norm_num [Complex.ext_iff]) (by norm_num [Complex.ext_iff])
      (by norm_num [Complex.ext_iff]) (by norm_num [Complex.ext_iff]) ?_
    rw [nA28, nF, n0]; norm_num [map_div₀, Complex.conj_I, map_ofNat, Complex.div_re, Complex.div_im, Complex.normSq_apply]
  · rw [Complex.dist_eq, Complex.dist_eq, nBE, nCF]
  · rw [Complex.dist_eq, nBE]
  · rw [Complex.dist_eq, nA0]
  · rw [Complex.dist_eq, nA28]
  · rw [Complex.dist_eq, n0]
  all_goals norm_num [Complex.ext_iff]

end SteinerLehmus
