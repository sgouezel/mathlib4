/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib

/-!
# Karlsson's proof of the existence of an asymptotic vector for semicontractions
-/

noncomputable section
open Filter Function Metric
open scoped Topology

variable {α β : Type*} [MetricSpace α] [MetricSpace β]

lemma exists_high_score (u : ℕ → ℝ) (hu : Tendsto u atTop atTop) (N : ℕ) :
    ∃ n ≥ N, ∀ m ≤ n, u m ≤ u n := by
  by_contra!
  let M := (Finset.image u (Finset.range (N+1))).max' (by simp)
  have A n : u n ≤ M := by
    induction n using Nat.strong_induction_on with | h n ih =>
    rcases le_total n N with hnN|hNn
    · apply Finset.le_max'
      grind
    · grind
  obtain ⟨n, hn⟩ : ∃ n, M + 1 ≤ u n := (tendsto_atTop.mp hu (M + 1)).exists
  grind

/-- A semicontraction between two metric spaces is a map that does not increase distances. -/
def semicontraction (f : α → β) :=
  ∀ x y, dist (f x) (f y) ≤ dist x y

namespace semicontraction

lemma comp {γ : Type*} [MetricSpace γ] {g : β → γ} {f : α → β}
    (hg : semicontraction g) (hf : semicontraction f) :
    semicontraction (g ∘ f) :=
  fun x y ↦ (hg (f x) (f y)).trans (hf x y)

lemma iterate {f : α → α} (h : semicontraction f) (n : ℕ) :
    semicontraction (f ^[n]) := by
  induction n with
  | zero => simp [semicontraction]
  | succ n ih => simpa using comp ih h


variable {E : Type*} [NormedAddCommGroup E]
  {f : E → E} (h : semicontraction f)
include h

/-- A convenient notation for the distance between `0` and `f^n 0`. -/
local notation "u" => (fun n ↦ dist (f^[n] 0) 0)

lemma u_subadditive : Subadditive u := by
  intro m n
  calc u (m + n)
  _ = dist (f^[m + n] 0) 0 := rfl
  _ ≤ dist (f^[m+n] 0) (f^[n] 0) + dist (f^[n] 0) 0 := dist_triangle _ _ _
  _ = dist (f^[n] (f^[m] 0)) (f^[n] 0) + dist (f^[n] 0) 0 := by rw [add_comm m n, iterate_add_apply]
  _ ≤ dist (f^[m] 0) 0 + dist (f^[n] 0) 0 := add_le_add (h.iterate _ _ _) le_rfl
  _ = u m + u n := rfl

/-- `h.l` is such that `h.u n` grows like `n * h.l`. -/
def l := h.u_subadditive.lim

lemma tendsto_lim : Tendsto (fun n ↦ u n / n) atTop (𝓝 h.l) := by
  have B : BddBelow (Set.range (fun n ↦ u n / n)) := by
    refine ⟨0, fun x hx ↦ ?_⟩
    obtain ⟨y, hy⟩ : ∃ y, ‖f^[y] 0‖ / y = x := by simpa using hx
    rw [← hy]
    positivity
  exact h.u_subadditive.tendsto_lim B

lemma l_nonneg : 0 ≤ h.l :=
  ge_of_tendsto' h.tendsto_lim (fun n ↦ by positivity)

lemma tendsto_sub_atTop {w : ℝ} (hw : w < h.l) :
    Tendsto (fun (n : ℕ) ↦ u n - n * w) atTop atTop := by
  have A : Tendsto (fun n ↦ u n / n - w) atTop (𝓝 (h.l - w)) :=
    h.tendsto_lim.sub tendsto_const_nhds
  have : Tendsto (fun n ↦ (u n / n - w) * n) atTop atTop := by
    have I : 0 < h.l - w := by linarith
    apply A.pos_mul_atTop I
    exact tendsto_natCast_atTop_atTop -- exact?
  apply Tendsto.congr' _ this
  filter_upwards [Ioi_mem_atTop 0] with n (hn : 0 < n)
  field_simp

variable
  -- [NormedSpace ℝ E]
  [InnerProductSpace ℝ E]

lemma exists_dual_up_to_of_lt {w : ℝ} (hw : w < h.l) (N : ℕ) :
    ∃ (v : StrongDual ℝ E), ‖v‖ ≤ 1 ∧ ∀ i ≤ N, v (f^[i] 0) ≤ - i * w := by
  obtain ⟨n, Nn, hn⟩ : ∃ n ≥ N, ∀ m ≤ n, u m - m * w ≤ u n - n * w :=
    exists_high_score _ (h.tendsto_sub_atTop hw) N
  obtain ⟨v, vnorm, hv⟩ :
    ∃ (v : StrongDual ℝ E), ‖v‖ ≤ 1 ∧ v (-(f^[n] 0)) = ‖-(f^[n] 0)‖ :=
      exists_dual_vector'' ℝ (-(f^[n] 0))
  refine ⟨v, vnorm, fun i hi ↦ ?_⟩
  have A : i ≤ n := hi.trans Nn
  calc
  v (f^[i] 0) = v (f^[i] 0 - (f^[n]) 0) - v (- (f^[n] 0)) := by
    simp only [map_sub, map_neg, sub_neg_eq_add, sub_add_cancel] -- simp?
  _ ≤ 1 * ‖(f^[i]) 0 - (f^[n]) 0‖ - ‖-(f^[n]) 0‖ := by
      rw [hv]
      gcongr
      apply (le_abs_self _).trans
      exact v.le_of_opNorm_le vnorm _
  _ = dist (f^[i] 0) (f^[i] (f^[n-i] 0)) - dist 0 (f^[n] 0) := by
    rw [← iterate_add_apply, one_mul, dist_eq_norm, dist_eq_norm,
           zero_sub, ← Nat.add_sub_assoc A, Nat.add_sub_cancel_left]
  _ ≤ dist 0 (f^[n-i] 0) - dist 0 (f^[n] 0) := sub_le_sub (h.iterate i _ _) le_rfl
  _ = u (n - i) - u n := by simp only [dist_comm (0 : E)]
  _ ≤ - n * w + (n - i : ℕ) * w := by linarith [hn (n-i) (Nat.sub_le n i)]
  _ = - i * w := by rw [Nat.cast_sub A]; ring

variable [FiniteDimensional ℝ E]

-- NB : pourquoi a-t-on juste `‖v‖ ≤ 1` ici, et pas `‖v‖ = 1`?
lemma exists_dual : ∃ (v : StrongDual ℝ E), ‖v‖ ≤ 1 ∧ ∀ i, v (f^[i] 0) ≤ -i * h.l := by
  -- on part d'une suite `w_n` qui tend vers `h.l` par valeurs inférieures
  obtain ⟨w, -, w_lt, w_lim⟩ : ∃ (w : ℕ → ℝ), StrictMono w
    ∧ (∀ (n : ℕ), w n < h.l) ∧ Tendsto w atTop (𝓝 h.l) :=
      exists_seq_strictMono_tendsto _
  -- pour chaque `n`, on peut choisir un élément du dual de norme au plus `1`
  -- tel que `y (f^[i] 0) ≤ - i w_n` pour tout `i ≤ n`, d'après le lemme
  -- précédent
  have A n : ∃ (y : StrongDual ℝ E), ‖y‖ ≤ 1 ∧ ∀ i ≤ n, y (f^[i] 0) ≤ - i * w n :=
    h.exists_dual_up_to_of_lt (w_lt n) n
  choose y hy using A -- oui, c'estl'axiome du choix !
  -- on extrait une sous-suite `y_{φ n}`, qui converge vers une limite `v`.
  obtain ⟨v, v_mem, φ, φ_mono, φlim⟩ :
    ∃ v ∈ closedBall (0 : StrongDual ℝ E) 1, ∃ (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (y ∘ φ) atTop (𝓝 v) := by
    -- dual ℝ E est propre
    refine IsCompact.tendsto_subseq (ProperSpace.isCompact_closedBall _ _) ?_
    intro n
    simp [(hy n).1]
  -- on va voir que cette limite convient.
  refine ⟨v, by simpa using v_mem, fun i ↦ ?_⟩
  -- on a fixé `i`, il faut voir que `v (f^[i] 0) ≤ -i h.l`.
  -- Pour cela, on passe à la limite
  -- dans les inégalités sur les `y_n (f^[i] 0)`.
  have A : Tendsto (fun n ↦ ((y ∘ φ) n) (f^[i] 0)) atTop (𝓝 (v (f^[i] 0))) :=
    ((isBoundedBilinearMap_apply.isBoundedLinearMap_left (f^[i] 0)).continuous.tendsto _).comp φlim
  have B : Tendsto (fun n ↦ -(i : ℝ) * w (φ n)) atTop (𝓝 (- i * h.l)) :=
    (tendsto_const_nhds.mul w_lim).comp φ_mono.tendsto_atTop
  have C : ∀ᶠ n in atTop, ((y ∘ φ) n) (f^[i] 0) ≤ - i * w (φ n) := by
    apply eventually_atTop.2 ⟨i, fun n hn ↦ ?_⟩
    apply (hy (φ n)).2 i
    exact le_trans hn (φ_mono.id_le n)
  exact le_of_tendsto_of_tendsto A B C

open scoped RealInnerProductSpace

-- on convertit l'existence d'une bonne forme linéaire en celle d'un bon
-- vecteur, car on est sur un espace euclidien.
lemma exists_asymp_vector :
    ∃ (v : E), ‖v‖ ≤ 1 ∧ ∀ (i : ℕ), (i : ℝ) * h.l ≤ ⟪v, (f^[i] 0)⟫ := by
  obtain ⟨v', v'_norm, hv'⟩ :
    ∃ (v' : StrongDual ℝ E), ‖v'‖ ≤ 1 ∧ ∀ i, v' (f^[i] 0) ≤ -i * h.l :=
      h.exists_dual
  -- (marcherait sur un espace complet, pas besoin de dimension finie ici).
  let v := (InnerProductSpace.toDual ℝ E).symm (-v')
  refine ⟨v, by simpa [v] using v'_norm, fun i ↦ ?_⟩
  simp [v]
  linarith [hv' i]

/-- A semicontraction on a finite-dimensional vector space admits an asymptotic
translation vector. -/
theorem exists_tendsto_div :
    ∃ (v : E), Tendsto (fun (n : ℕ) ↦ (1 / (n : ℝ)) • (f^[n] 0)) atTop (𝓝 v) := by
  obtain ⟨v₀, v₀_norm, h₀⟩ :
    ∃ (v : E), ‖v‖ ≤ 1 ∧ ∀ (i : ℕ), (i : ℝ) * h.l ≤ ⟪v, (f^[i] 0)⟫ :=
      h.exists_asymp_vector
  let v := h.l • v₀
  use v
  have A : ∀ᶠ (n : ℕ) in atTop,
      ‖(1 / (n : ℝ)) • (f^[n] 0) - v‖^2 ≤ (u n / n)^2 - h.l^2 := by
    apply eventually_atTop.2 ⟨1, fun n hn ↦  ?_⟩
    have n_ne_zero : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
    calc ‖(1 / (n : ℝ)) • (f^[n] 0) - v‖ ^ 2
    _ = ‖(1 / (n : ℝ)) • (f^[n] 0)‖^2 - 2 * ⟪(1 / (n : ℝ)) • (f^[n] 0), v⟫ + ‖v‖^2 :=
      norm_sub_sq_real _ _
    _ = (u n / n)^2 - 2 * h.l / n * ⟪v₀, (f^[n] 0)⟫ + h.l^2 * ‖v₀‖^2 := by
        congr 2
        · simp [norm_smul, div_eq_inv_mul, mul_pow]
        · simp [real_inner_smul_left, real_inner_smul_right, v]
          rw [real_inner_comm]
          ring
        · simp [norm_smul, Real.norm_eq_abs, mul_pow, v]
    _ ≤ (u n / n) ^ 2 - 2 * h.l / n * (n * h.l) + h.l ^ 2 * 1 ^ 2 := by
      gcongr
      · have := h.l_nonneg
        positivity
      · exact h₀ n
    _ = (u n / n) ^ 2 - h.l ^ 2 := by field_simp [n_ne_zero]; ring
  have B : Tendsto (fun (n : ℕ) ↦ (u n / n) ^ 2 - h.l^2) atTop (𝓝 (h.l^2 - h.l^2)) :=
    (h.tendsto_lim.pow 2).sub tendsto_const_nhds
  have C : Tendsto (fun (n : ℕ) ↦ ‖(1 / (n : ℝ)) • (f^[n] 0) - v‖^2) atTop (𝓝 0) := by
    rw [sub_self] at B
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds B _ A
    exact Eventually.of_forall (fun n ↦ by simp)
  have D : Tendsto (fun (n : ℕ) ↦ ‖(1 / (n : ℝ)) • (f^[n] 0) - v‖) atTop (𝓝 0) := by
    convert C.sqrt <;> simp
  exact tendsto_iff_norm_sub_tendsto_zero.2 D


-- discuter de espace vectoriel normé / espace euclidien
-- et dimension finie


omit h [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Attention: si on ne fait pas attention à l'énoncé, on peut donner une
-- preuve triviale d'un résultat stupide. -/
lemma wrong_exists_tendsto_div' :
    ∃ (v : E), Tendsto (fun (n : ℕ) ↦ (1 / n) • (f^[n] 0)) atTop (𝓝 v) :=
  ⟨(0 : E), tendsto_const_nhds.congr' $
    eventually_atTop.2 ⟨2, fun n hn ↦ by simp [Nat.div_eq_of_lt hn]⟩⟩

/-- Version un peu plus détaillée du précédent -/
lemma wrong_exists_tendsto_div :
    ∃ (v : E), Tendsto (fun (n : ℕ) ↦ (1 / n) • (f^[n] 0)) atTop (𝓝 v) := by
  use 0
  have A : ∀ n ≥ 2, 1/n = 0 := by
    intro n hn
    exact Nat.div_eq_of_lt hn
  have : Tendsto (fun (n : ℕ) ↦ (0 : E)) atTop (𝓝 0) := tendsto_const_nhds
  apply Tendsto.congr' _ this
  apply eventually_atTop.2 ⟨2, _⟩
  intro n hn
  simp [A n hn]

end semicontraction
