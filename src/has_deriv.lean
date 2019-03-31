/-
Copyright (c) 2018 Sander Dahmen, Johannes Hölzl, Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sander Dahmen, Johannes Hölzl, Robert Y. Lewis

"On large subsets of 𝔽ⁿ_q with no three-term arithmetic progression"
by J. S. Ellenberg and D. Gijswijt

This file develops just enough elementary calculus to prove a fact needed in section 13.
It includes a proof of the product rule for functions ℝ → ℝ.
-/

import analysis.normed_space.deriv

open filter

lemma is_bounded_linear_map_mul_const (r : ℝ) : is_bounded_linear_map ℝ ((*) r) :=
show is_bounded_linear_map ℝ (λx:ℝ, r • x), from
  is_bounded_linear_map.smul _ is_bounded_linear_map.id

open asymptotics

section
variables {α : Type*} {β : Type*} {γ : Type*}
variables [normed_field β] [normed_field γ]

theorem is_o_mul_right_one {f₁ f₂ : α → β} {g : α → γ} {l : filter α}
    (h₁ : is_o f₁ g l) (h₂ : is_O f₂ (λx, (1:γ)) l):
  is_o (λ x, f₁ x * f₂ x) (λ x, g x) l :=
have is_o (λ x, f₁ x * f₂ x) (λ x, g x * 1) l := is_o_mul_right h₁ h₂,
by convert this; funext; rw mul_one

end

def has_deriv (f : ℝ → ℝ) (f' : ℝ) (x : ℝ) :=
has_fderiv_at ℝ f ((*) f') x

lemma has_deriv.congr₂ {f : ℝ → ℝ} {f' f'' x : ℝ} (eq : f' = f'') (h : has_deriv f f' x) :
  has_deriv f f'' x :=
by rwa ← eq

lemma has_deriv_const (r x : ℝ) : has_deriv (λx, r) 0 x :=
(has_fderiv_at_const r _).congr (assume x, rfl) (assume x, (zero_mul _).symm)

lemma has_deriv_id (x : ℝ) : has_deriv (λx, x) 1 x :=
(has_fderiv_at_id x).congr (assume x, rfl) (assume x, (one_mul _).symm)

lemma has_deriv.add {x : ℝ} {f g : ℝ → ℝ} {f' g' : ℝ}
  (hf : has_deriv f f' x) (hg : has_deriv g g' x) : has_deriv (λx, f x + g x) (f' + g') x :=
(has_fderiv_at_add hf hg).congr (assume x, rfl) (assume x, (add_mul _ _ _).symm)

lemma has_deriv.sub {x : ℝ} {f g : ℝ → ℝ} {f' g' : ℝ}
  (hf : has_deriv f f' x) (hg : has_deriv g g' x) : has_deriv (λx, f x - g x) (f' - g') x :=
(has_fderiv_at_sub hf hg).congr (assume x, rfl) (assume x, (sub_mul _ _ _).symm)

lemma has_deriv.neg {x : ℝ} {f : ℝ → ℝ} {f' : ℝ} (hf : has_deriv f f' x) :
  has_deriv (λx, - f x) (- f') x :=
(has_fderiv_at_neg hf).congr (assume x, rfl) (assume x, neg_mul_eq_neg_mul _ _)

lemma has_deriv_finset_sum {α : Type*} {x : ℝ} {f : α → ℝ → ℝ} {f' : α → ℝ}
  (s : finset α) (hf : ∀a, has_deriv (f a) (f' a) x) :
  has_deriv (λx, s.sum (λa, f a x)) (s.sum f') x :=
begin
  letI := classical.dec_eq α,
  refine s.induction_on _ _,
  { simp only [finset.sum_empty],
    exact has_deriv_const 0 x },
  { assume a s has ih,
    simp only [finset.sum_insert, has, not_false_iff],
    exact (hf a).add ih }
end

lemma has_deriv.mul {f g : ℝ → ℝ} {f' g' : ℝ} {x : ℝ}
  (hf : has_deriv f f' x) (hg : has_deriv g g' x) :
  has_deriv (λx, f x * g x) (f x * g' + f' * g x) x :=
begin
  let D := λ(f : ℝ → ℝ) (f' x' : ℝ), (f x' - f x) - f' * (x' - x),
  refine ⟨is_bounded_linear_map_mul_const _, _⟩,
  simp only [add_mul],
  rw show
    (λx', f x' * g x' - f x * g x - (f x * g' * (x' - x) + f' * g x * (x' - x))) =
    (λx', f x * D g g' x' + D f f' x' * g x' + f' * ((x' - x) * (g x' - g x))),
  { funext x', simp only [D], ring },
  refine is_o.add (is_o.add (is_o_const_mul_left hg.is_o _) _) _,
  { refine is_o_mul_right_one hf.is_o _,
    rcases metric.tendsto_nhds_nhds.1 hg.continuous_at 1 zero_lt_one with ⟨δ, hδ, h⟩,
    refine ⟨∥g x∥ + 1, add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one,
      metric.mem_nhds_iff.2 ⟨δ, hδ, assume y hy, _⟩⟩,
    specialize h hy,
    simp only [set.mem_set_of_eq, norm_one, mul_one],
    rw [dist_eq_norm] at h,
    calc ∥g y∥ = ∥g x + (g y - g x)∥ : by rw [add_sub_cancel'_right]
      ... ≤ ∥g x∥ + ∥g y - g x∥ : norm_triangle _ _
      ... ≤ ∥g x∥ + 1 : add_le_add_left (le_of_lt h) _ },
  { refine is_o_const_mul_left _ _,
    rw is_o_iff_tendsto,
    { have : tendsto (λx', g x' - g x) (nhds x) (nhds (g x - g x)) :=
        tendsto_sub hg.continuous_at (@tendsto_const_nhds ℝ _ _ (g x) (nhds x)),
      have eq : (λx', (x' - x) * (g x' - g x) / (x' - x)) = (λx', g x' - g x),
      { funext x',
        by_cases x = x',
        { simp [h] },
        { rw [mul_div_cancel_left], rwa [(≠), sub_eq_zero, eq_comm] } },
      rw [sub_self] at this,
      rwa [eq] },
    { assume x h, rw [h, zero_mul] } }
end

lemma has_deriv.mul_left {f : ℝ → ℝ} {f' : ℝ} {x : ℝ} (c : ℝ) (hf : has_deriv f f' x) :
  has_deriv (λx, c * f x) (c * f') x :=
have _ := (has_deriv_const c x).mul hf,
by simpa

lemma has_deriv.pow {f : ℝ → ℝ} {f' : ℝ} {x : ℝ} (hf : has_deriv f f' x) :
  ∀n:ℕ, has_deriv (λx, (f x) ^ n) (n * (f x)^(n - 1) * f') x
| 0       := by simp only [has_deriv_const 1 x, nat.zero_sub, nat.cast_zero, zero_mul, pow_zero]
| 1       := by simp only [hf, mul_one, one_mul, nat.sub_self, pow_one, nat.cast_one, pow_zero]
| (n + 1 + 1) :=
  begin
    refine (hf.mul (has_deriv.pow (n + 1))).congr (assume x, rfl) (assume x, _),
    simp only [nat.add_sub_cancel],
    simp only [add_mul, mul_add, pow_add, pow_one, one_mul, add_comm, pow_one,
      nat.cast_add, nat.cast_one],
    ac_refl
  end

lemma increasing_of_deriv_zero_pos (f : ℝ → ℝ) (f' : ℝ) (hf : has_deriv f f' 0) (hf' : f' > 0) :
  ∃ε>0, ∀x, 0 < x → x < ε → f 0 < f x :=
begin
  have := (has_fderiv_at_filter_iff_tendsto.1 hf).2,
  simp only [sub_zero, (norm_inv _).symm, (normed_field.norm_mul _ _).symm] at this,
  rw [← @tendsto_zero_iff_norm_tendsto_zero ℝ ℝ ℝ, metric.tendsto_nhds_nhds] at this,
  specialize this f' hf',
  rcases this with ⟨ε, hε, h⟩,
  refine ⟨ε, hε, assume x hx0 hxε, _⟩,
  have : dist x 0 < ε,
  { rwa [dist_zero_right, real.norm_eq_abs, abs_of_pos hx0] },
  specialize @h x this,
  rw [dist_zero_right, mul_comm f', mul_sub, ← mul_assoc, inv_mul_cancel (ne_of_gt hx0), one_mul,
    norm_sub_rev, real.norm_eq_abs, abs_sub_lt_iff, sub_lt_self_iff] at h,
  exact (sub_pos.1 $ pos_of_mul_pos_left h.1 $ inv_nonneg.2 $ le_of_lt $ hx0)
end

lemma decreasing_of_fderiv_pos (f : ℝ → ℝ) (f' : ℝ) (x : ℝ) (hf : has_deriv f f' x) (hf' : 0 < f') :
  ∃ε>0, ∀y, x - ε < y → y < x → f y < f x :=
begin
  have : has_fderiv_at ℝ (λx':ℝ, - (f ∘ (λx', x - x')) x') ((*) f') 0,
  { rw show ((*) f') = (λx', - (((*) f') ∘ (λx', 0 - x')) x'),
      by funext x; dsimp only [(∘)]; rw [mul_sub, mul_zero, zero_sub, neg_neg],
    refine has_fderiv_at_neg _,
    dsimp only,
    refine has_fderiv_at.comp (has_fderiv_at_sub (has_fderiv_at_const _ _) (has_fderiv_at_id _)) _,
    rw sub_zero,
    exact hf },
  rcases increasing_of_deriv_zero_pos _ _ this hf' with ⟨ε, hε, h⟩,
  refine ⟨ε, hε, assume y hyε hyx, _⟩,
  specialize h (x - y),
  simp [-sub_eq_add_neg, sub_sub_cancel, sub_zero] at h,
  refine h hyx (sub_lt.2 hyε)
end
