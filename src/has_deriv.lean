/-
Copyright (c) 2018 Sander Dahmen, Johannes Hölzl, Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sander Dahmen, Johannes Hölzl, Robert Y. Lewis

"On large subsets of 𝔽ⁿ_q with no three-term arithmetic progression"
by J. S. Ellenberg and D. Gijswijt

This file develops just enough elementary calculus to prove a fact needed in section 13.
It includes a proof of the product rule for functions ℝ → ℝ.
-/
import analysis.calculus.deriv

open filter

lemma is_bounded_linear_map_mul_const (r : ℝ) : is_bounded_linear_map ℝ ((*) r) :=
show is_bounded_linear_map ℝ (λx:ℝ, r • x), from
  is_bounded_linear_map.smul _ is_bounded_linear_map.id

noncomputable def mul_const_bounded_linear_map (r : ℝ) : ℝ →L[ℝ] ℝ :=
(is_bounded_linear_map_mul_const r).to_continuous_linear_map

noncomputable def continuous_linear_map.to_fun' (f : ℝ →L[ℝ] ℝ) : ℝ → ℝ :=
f.to_fun

@[simp] lemma mul_const_bounded_linear_map_apply (r x : ℝ) :
  (mul_const_bounded_linear_map r).to_fun' x = r * x :=
rfl

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

def has_deriv (f : ℝ → ℝ) (f' : ℝ) (x : ℝ) : Prop :=
has_fderiv_at f (mul_const_bounded_linear_map f') x --((*) f') x

lemma has_deriv.congr₂ {f : ℝ → ℝ} {f' f'' x : ℝ} (eq : f' = f'') (h : has_deriv f f' x) :
  has_deriv f f'' x :=
by rwa ← eq

lemma has_deriv_const (r x : ℝ) : has_deriv (λx, r) 0 x :=
(has_fderiv_at_const r _).congr (assume x, rfl) (assume x, (zero_mul _).symm)

lemma has_deriv_id (x : ℝ) : has_deriv (λx, x) 1 x :=
(has_fderiv_at_id x).congr (assume x, rfl) (assume x, (one_mul _).symm)

lemma has_deriv.add {x : ℝ} {f g : ℝ → ℝ} {f' g' : ℝ}
  (hf : has_deriv f f' x) (hg : has_deriv g g' x) : has_deriv (λx, f x + g x) (f' + g') x :=
(hf.add hg).congr (assume x, rfl) (assume x, (add_mul _ _ _).symm)

lemma has_deriv.sub {x : ℝ} {f g : ℝ → ℝ} {f' g' : ℝ}
  (hf : has_deriv f f' x) (hg : has_deriv g g' x) : has_deriv (λx, f x - g x) (f' - g') x :=
(hf.sub hg).congr (assume x, rfl) $ λ x,
  show f' * x - g' * x = (f' - g') * x, by simp [right_distrib]

lemma has_deriv.neg {x : ℝ} {f : ℝ → ℝ} {f' : ℝ} (hf : has_deriv f f' x) :
  has_deriv (λx, - f x) (- f') x :=
(hf.neg).congr (assume x, rfl) $ λ x, show -(f' * x) = (-f') * x, by simp

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
  unfold has_deriv,
  convert has_fderiv_at.mul hf hg using 1,
  ext, dsimp,
  change continuous_linear_map.to_fun' _ _ = _ * continuous_linear_map.to_fun' _ _ + _ * continuous_linear_map.to_fun' _ _,
  simp, ring
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
    change continuous_linear_map.to_fun' _ _ = continuous_linear_map.to_fun' _ _,
    simp only [mul_const_bounded_linear_map_apply, nat.add_sub_cancel, nat.cast_add, nat.cast_one],
    simp only [add_mul, mul_add, pow_add, pow_one, one_mul, add_comm, pow_one],
    ac_refl
  end

lemma increasing_of_deriv_zero_pos (f : ℝ → ℝ) (f' : ℝ) (hf : has_deriv f f' 0) (hf' : f' > 0) :
  ∃ε>0, ∀x, 0 < x → x < ε → f 0 < f x :=
begin
  have := (has_fderiv_at_filter_iff_tendsto.1 hf),
  simp only [sub_zero, (norm_inv _).symm, (normed_field.norm_mul _ _).symm] at this,
  rw [← @tendsto_zero_iff_norm_tendsto_zero ℝ ℝ, metric.tendsto_nhds_nhds] at this,
  specialize this f' hf',
  rcases this with ⟨ε, hε, h⟩,
  refine ⟨ε, hε, assume x hx0 hxε, _⟩,
  have : dist x 0 < ε,
  { rwa [dist_zero_right, real.norm_eq_abs, abs_of_pos hx0] },
  specialize @h x this,
  change dist (_*(_ - continuous_linear_map.to_fun' _ _)) _ < _ at h,
  rw [mul_const_bounded_linear_map_apply, dist_zero_right, mul_comm f', mul_sub, ← mul_assoc, inv_mul_cancel (ne_of_gt hx0), one_mul,
    norm_sub_rev, real.norm_eq_abs, abs_sub_lt_iff, sub_lt_self_iff] at h,
  exact (sub_pos.1 $ pos_of_mul_pos_left h.1 $ inv_nonneg.2 $ le_of_lt $ hx0)
end

lemma decreasing_of_fderiv_pos (f : ℝ → ℝ) (f' : ℝ) (x : ℝ) (hf : has_deriv f f' x) (hf' : 0 < f') :
  ∃ε>0, ∀y, x - ε < y → y < x → f y < f x :=
begin
  have : mul_const_bounded_linear_map (-f') = continuous_linear_map.comp (mul_const_bounded_linear_map (f')) (mul_const_bounded_linear_map (-1)),
  { ext x, show -f' * x = f' * (-1 * x), simp },
  have : has_deriv (λx':ℝ, - (f ∘ (λy, x - y)) x') (f') 0,
  { convert @has_deriv.neg _ _ (-f') _ using 1,
    { rw neg_neg },
    { unfold has_deriv at hf ⊢, dsimp, rw ←sub_zero x at hf,
      convert has_fderiv_at.comp _ hf _ using 2,
      convert @has_deriv.sub _ _ _ 0 1 _ _,
      { norm_num },
      { apply has_deriv_const },
      { apply has_deriv_id } } },
  rcases increasing_of_deriv_zero_pos _ _ this hf' with ⟨ε, hε, h⟩,
  refine ⟨ε, hε, assume y hyε hyx, _⟩,
  specialize h (x - y),
  simp [-sub_eq_add_neg, sub_sub_cancel, sub_zero] at h,
  refine h hyx (sub_lt.2 hyε)
end