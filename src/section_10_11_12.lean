/-
Copyright (c) 2018 Sander Dahmen, Johannes Hölzl, Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sander Dahmen, Johannes Hölzl, Robert Y. Lewis

"On large subsets of 𝔽ⁿ_q with no three-term arithmetic progression"
by J. S. Ellenberg and D. Gijswijt

This file establishes the bound on the cardinality of a generalized cap set.
It corresponds to sections 10-12 of our blueprint.
-/

import library section_9

open mv_polynomial

section

parameters
  {α : Type} [discrete_field α] [fintype α] -- 𝔽_q: q is cardinality of `α`
  (n : ℕ)

def q : ℕ := fintype.card α

lemma q_pos : q > 0 := fintype.card_pos_iff.2 ⟨1⟩

lemma one_le_q : 1 ≤ q := q_pos

lemma one_le_q_real : 1 ≤ (q : ℚ) :=
suffices ↑(1 : ℕ) ≤ (q : ℚ), by simpa,
nat.cast_le.2 one_le_q


/-- Polynomials in α - seen as a vector space -/
@[reducible] def S := mv_polynomial (fin n) α

instance S.module : module α S := by dunfold S; apply_instance
instance S.vector_space : vector_space α S := { .. S.module }

instance fin_q_has_zero : has_zero (fin q) := ⟨⟨0, one_le_q⟩⟩

def M : finset (mv_polynomial (fin n) α):=
(finset.univ.image $ λ f : fin n →₀ fin q, f.map_range fin.val rfl).image (λd : fin n →₀ ℕ, monomial d (1:α))

lemma linear_independent_M : linear_independent α (↑M : set (mv_polynomial (fin n) α)) :=
(mv_polynomial.is_basis_monomials _ _).1.mono $ λ p hp,
  let ⟨s, _, hsp⟩ := finset.mem_image.1 hp in
  set.mem_range.2 ⟨s, hsp⟩

def fin_map_to_mono_map (f : fin n → fin q) : fin n →₀ ℕ := λ k, (f k).val
def fmtmm : has_coe (fin n → fin q) (fin n →₀ ℕ) := ⟨fin_map_to_mono_map⟩
local attribute [instance] fmtmm

lemma monomial_mem_M (f : fin n → fin q) : monomial ↑f (1 : α) ∈ M :=
begin
  apply finset.mem_image.2,
  refine ⟨f, _, rfl⟩,
  apply finset.mem_image.2,
  use [f, finset.mem_univ _], ext, refl
end

@[simp] lemma coe_fin_eq_coe_fin (f g : (fin n → fin q)) : (f : fin n →₀ ℕ) = g ↔ f = g :=
begin
  split,
  { intro h,
    ext,
    apply (fin.ext_iff _ _).2,
    apply finsupp.congr_fun h },
  { intro h, rw h }
end

lemma M_spec {x} (hx : x ∈ M) : ∃ s : fin n → fin q, monomial ↑s 1 = x :=
begin
  rcases finset.mem_image.1 hx with ⟨d, ⟨hd, hdmon⟩⟩,
  have h : ∀ k, d k < q,
  { intro k,
    rcases finset.mem_image.1 hd with ⟨l, ⟨hl, hdl⟩⟩,
    have hdl' : (finsupp.map_range fin.val (_) l : fin n → ℕ) k = d k, {rw hdl},
    rw finsupp.map_range_apply at hdl', rw ←hdl', apply fin.is_lt },
  use λ k, ⟨d k, h k⟩,
  rw ←hdmon, congr, ext, refl
end

noncomputable def monom_exps (p : (mv_polynomial (fin n) α)) : (fin n → fin q) :=
if hp : p ∈ M then classical.some (M_spec hp) else 0

lemma monom_exps_def {x} (hx : x ∈ M) : monomial ↑(monom_exps x) 1 = x :=
by simpa [hx, monom_exps] using (classical.some_spec (M_spec hx))

lemma monom_exps_inj {x y} (hx : x ∈ M) (hy : y ∈ M) (hxy : monom_exps x = monom_exps y) : x = y :=
have h1 : _, from monom_exps_def hx, have h2 : _, from monom_exps_def hy,
by rw [←h1, ←h2, hxy]

@[simp] lemma monom_exps_monomial (f : fin n → fin q) : monom_exps (monomial f 1) = f :=
by simpa using finsupp.eq_of_single_eq_left (monom_exps_def (monomial_mem_M _)) one_ne_zero

lemma monom_exps_surj (f : fin n → fin q) : ∃ x, x ∈ M ∧ monom_exps x = f :=
⟨monomial f 1, monomial_mem_M _, monom_exps_monomial _⟩

-- do more generally
lemma monomial_total_degree (f : fin n →₀ ℕ) :
  mv_polynomial.total_degree (monomial f (1 : α)) = finsupp.sum f (λ _, id) :=
suffices finset.sup {f} (λ (s : fin n →₀ ℕ), finsupp.sum s (λ _, id)) =
    finsupp.sum f (λ _, id), by simpa [monomial, finsupp.single, mv_polynomial.total_degree],
by rw finset.sup_singleton

lemma mv_polynomial_eval_eq (p : mv_polynomial (fin n) α) (a : fin n → α) :
  p.eval a = p.sum (λi c, c * (i.to_multiset.map $ λn, a n).prod) :=
begin
  rw [eval, eval₂],
  congr, funext i c, congr,
  rw [finsupp.to_multiset_map, finsupp.prod_to_multiset,
    finsupp.prod_map_domain_index pow_zero pow_add]
end

lemma eval_add (p : S) (a b : fin n → α) :
  p.eval (a + b) = p.sum (λe x, multiset.sum $
    e.to_multiset.diagonal.map $ λp, x * ((p.1.map $ λi, a i).prod * (p.2.map $ λi, b i).prod)) :=
by simp [mv_polynomial_eval_eq, multiset.sum_map_mul_left, multiset.prod_map_add]

section

def M' (d : ℚ) := M.filter (λ m, d ≥ mv_polynomial.total_degree m)
end

lemma linear_independent_M' (d) : linear_independent α (↑(M' d) : set (mv_polynomial (fin n) α)) :=
linear_independent_M.mono $ λ x hx, M.filter_subset hx

lemma mem_M_of_mem_M' {x d} (hx : x ∈ M' d) : x ∈ M := (finset.mem_filter.1 hx).1

def S' (d : ℚ) := submodule.span α (↑(M' d) : set (mv_polynomial (fin n) α))

lemma mem_S'_of_mem_M' {d : ℚ} {p} (hp : p ∈ M' d) : p ∈ S' d :=
submodule.mem_span.2 $ λ t hmt, hmt hp

lemma S'_le_restrict_q (d : ℚ) : S' d ≤ mv_polynomial.restrict_degree _ _ (q - 1) :=
submodule.span_le.2 $ assume p hp,
begin
  have : p ∈ M := mem_M_of_mem_M' hp,
  rcases M_spec this with ⟨s, rfl⟩,
  assume s hs n,
  rw [finset.mem_coe, mv_polynomial.monomial,
    finsupp.support_single_ne_zero zero_ne_one.symm, finset.singleton_eq_singleton,
    finset.mem_singleton] at hs,
  subst hs,
  exact (nat.le_sub_right_iff_add_le one_le_q).2 (s n).2
end

lemma le_floor_to_nat (n : ℕ) (d : ℚ) (hd : 0 ≤ d) :
  n ≤ ⌊d⌋.to_nat ↔ (n : ℚ) ≤ d :=
begin
  rw [int.to_nat_le_iff, le_floor, ← coe_coe],
  rwa [le_floor]
end

lemma S'_le_restrict_d (d : ℚ) (hd : 0 ≤ d):
  S' d ≤ mv_polynomial.restrict_total_degree _ _ (⌊d⌋).to_nat :=
submodule.span_le.2 $ assume p hp, (mv_polynomial.mem_restrict_total_degree _ _ _ _).2
begin
  have hp := (finset.mem_filter.1 hp).2,
  rwa [le_floor_to_nat _ _ hd]
end

parameter (α)
noncomputable def m (d : ℚ) : ℕ := (vector_space.dim α (S' d)).to_nat
parameter {α}

lemma M'_card (d : ℚ) : (M' d).card = m d :=
by rw [m, S', dim_span (linear_independent_M' _), ←cardinal.finset_card, cardinal.to_nat_coe]

section Propostion_11_1
parameters {d : ℚ} (d_nonneg : 0 ≤ d) --(d_upper : d ≤ (fintype.card α) * n)

set_option class.instance_max_depth 200

parameters
  {p : S}
  (A : finset (fin n → α))
  (a b c : α)
  (hp : p ∈ S' d)
  (habc : a + b + c = 0)
  (h : ∀x:fin n → α, x∈A → ∀y∈A, x ≠ y → mv_polynomial.eval (a • x + b • y) p = (0:α))

include habc
lemma a_plus_b : a + b = -c :=
calc a + b = a + b + c + (-c) : by simp
       ... = -c : by simp [habc]
omit habc

include hp

section
open multiset finsupp


/-- The coefficients `(m₁, m₂) ⊢> ∑ c*X^e ∈ p | m₁ + m₂ = e, c * a ^ |m₁| * b ^ |m₂|` -/
def coeff (a b : α) : (multiset (fin n) × multiset (fin n)) →₀ α :=
p.sum $ λe c, sum $ e.to_multiset.diagonal.map $ λm, single m (c * a ^ card m.1 * b ^ card m.2)

/-- `π x m := Πi∈m, x i`  -/
def π (x : fin n → α) (m : multiset (fin n)) : α := prod $ m.map $ λi, x i

def split_left (a b : α) : (multiset (fin n) × multiset (fin n)) →₀ α :=
(coeff a b).filter $ λp, d / 2 > p.1.card

def split_right (a b : α) : (multiset (fin n) × multiset (fin n)) →₀ α :=
((coeff a b).filter (λp:multiset (fin n)×multiset (fin n), ¬ d / 2 > p.1.card)).map_domain prod.swap

lemma mem_coeff_support {a b : α} (m₀ m₁ : multiset (fin n)) (h : (m₀, m₁) ∈ (coeff a b).support) :
  of_multiset (m₀ + m₁) ∈ p.support :=
begin
  rcases finsupp.mem_support_finset_sum _ h with ⟨f, hf, hfm⟩,
  rcases finsupp.mem_support_multiset_sum _ hfm with ⟨e, he, hem⟩, clear hfm,
  rcases multiset.mem_map.1 he with ⟨m, hm, rfl⟩, clear he,
  rw [mem_support_single] at hem,
  rcases hem with ⟨rfl, hb⟩,
  rw [mem_diagonal] at hm,
  rw [hm],
  show equiv_multiset.inv_fun (equiv_multiset.to_fun f) ∈ p.support,
  rwa [equiv_multiset.left_inv f]
end

section
include d_nonneg

lemma mem_coeff_support_d {a b : α} (m₀ m₁ : multiset (fin n))
  (h : (m₀, m₁) ∈ (coeff a b).support) :
  d ≥ (m₀ + m₁).card :=
begin
  have : of_multiset (m₀ + m₁) ∈ p.support := mem_coeff_support m₀ m₁ h,
  have hp := (mv_polynomial.mem_restrict_total_degree _ _ _ _).1 (S'_le_restrict_d d d_nonneg hp),
  rw [le_floor_to_nat _ _ d_nonneg, total_degree_eq] at hp,
  refine le_trans (nat.cast_le.2 $ le_trans _ (finset.le_sup this)) hp,
  convert le_refl _,
  exact finsupp.equiv_multiset.4 _
end

lemma mem_coeff_support_q {a b : α} (m₀ m₁ : multiset (fin n))
  (h : (m₀, m₁) ∈ (coeff a b).support) (i : fin n) :
  (m₀ + m₁).count i < q :=
begin
  have := S'_le_restrict_q _ hp (mem_coeff_support _ _ h),
  exact (nat.le_sub_right_iff_add_le one_le_q).1 (this i)
end

lemma split_left_curry_card (a b : α) : (split_left a b).curry.support.card ≤ m (d/2) :=
begin
  rw [← M'_card, M'],
  refine finset.card_le_card_of_inj_on (λm, monomial (finsupp.of_multiset m) (1:α)) _ _,
  { simp only [finset.mem_filter, finset.mem_image, exists_prop, finset.mem_univ, true_and, M],
    assume m hm',
    rcases finset.mem_image.1 (finsupp.support_curry _ hm') with ⟨⟨m₀, m₁⟩, hm, rfl⟩, clear hm',
    rw [split_left, finsupp.support_filter, finset.mem_filter] at hm,
    let f : fin n → fin q := λi, ⟨m₀.count i, lt_of_le_of_lt
      (multiset.count_le_of_le _ $ le_add_right _ _) (mem_coeff_support_q _ _ hm.1 i)⟩,
    refine ⟨⟨_, ⟨f, rfl⟩, _⟩, _⟩,
    { congr, ext i, refl },
    { rw [monomial_total_degree, ← card_to_multiset],
      convert le_of_lt hm.2,
      exact finsupp.equiv_multiset.4 _ } },
  { assume m₀ _ m₁ _ eq,
    have := (single_eq_single_iff _ _ _ _).1 eq,
    simp only [(zero_ne_one : (0:α) ≠ 1).symm, or_false, and_false] at this,
    exact (finsupp.equiv_multiset.symm.apply_eq_iff_eq m₀ m₁).1 this.1 }
end

lemma split_right_curry_card (a b : α) : (split_right a b).curry.support.card ≤ m (d/2) :=
begin
  rw [← M'_card, M'],
  refine finset.card_le_card_of_inj_on (λm, monomial (finsupp.of_multiset m) (1:α)) _ _,
  { simp only [finset.mem_filter, finset.mem_image, exists_prop, finset.mem_univ, true_and, M],
    assume m hm',
    rcases finset.mem_image.1 (finsupp.support_curry _ hm') with ⟨⟨m₁, m₀⟩, hm'', rfl⟩, clear hm',
    rcases finset.mem_image.1 (map_domain_support hm'') with ⟨⟨m₀', m₁'⟩, hm, eq⟩,
    cases eq, clear eq, clear hm'',
    rw [finsupp.support_filter, finset.mem_filter] at hm,
    let f : fin n → fin q := λi, ⟨m₁.count i, lt_of_le_of_lt
      (multiset.count_le_of_le _ $ le_add_left _ _) (mem_coeff_support_q _ _ hm.1 i)⟩,
    refine ⟨⟨_, ⟨f, rfl⟩, _⟩, _⟩,
    { congr, ext i, refl },
    { rw [monomial_total_degree, ← card_to_multiset],
      have d_le : d / 2 ≤ ↑(card m₀) := le_of_not_gt hm.2,
      have d_ge : d ≥ card (m₀ + m₁) := mem_coeff_support_d _ _ hm.1,
      rw [multiset.card_add, nat.cast_add] at d_ge,
      have : d / 2 ≥ ↑(card m₁),
      { refine le_of_not_gt (assume h, _),
        have : (card m₀ : ℚ) + card m₁ > d / 2 + d / 2 := add_lt_add_of_le_of_lt d_le h,
        rw [add_halves] at this,
        exact not_lt_of_ge d_ge this },
      convert this,
      exact finsupp.equiv_multiset.4 _ } },
  { assume m₀ _ m₁ _ eq,
    have := (single_eq_single_iff _ _ _ _).1 eq,
    simp only [(zero_ne_one : (0:α) ≠ 1).symm, or_false, and_false] at this,
    exact (finsupp.equiv_multiset.symm.apply_eq_iff_eq m₀ m₁).1 this.1 }
end

end

lemma eval_add_eq_split_sum {x y : fin n → α} {a b : α} :
  p.eval (a • x + b • y) =
    (split_left a b).curry.sum (λm f, π x m * f.sum (λm c, c * π y m)) +
    (split_right a b).curry.sum (λm f, π y m * f.sum (λm c, c * π x m)) :=
calc p.eval (a • x + b • y) = (coeff a b).sum (λm c, c * π x m.1 * π y m.2) :
  by
    rw [coeff, eval_add];
    simp [π, finsupp.multiset_sum_sum_index, sum_sum_index, sum_single_index,
      add_mul, mul_comm, mul_left_comm, mul_assoc]
  ... =
    (split_left a b).sum (λm c, c * π x m.1 * π y m.2) +
    (split_right a b).sum (λm c, c * π x m.2 * π y m.1) :
  begin
    rw [split_left, split_right, sum_map_domain_index]; simp [- not_lt],
    rw [← sum_add_index, filter_pos_add_filter_neg]; simp [add_mul],
    simp [add_mul]
  end
  ... =
    (split_left a b).curry.sum (λm f, π x m * f.sum (λm c, c * π y m)) +
    (split_right a b).curry.sum (λm f, π y m * f.sum (λm c, c * π x m)) :
  by
    rw [
      ← (sum_curry_index (split_left a b) (λm₀ m₁ c, c * π x m₀ * π y m₁) _ _),
      ← (sum_curry_index (split_right a b) (λm₀ m₁ c, c * π x m₁ * π y m₀) _ _)];
    simp [finsupp.mul_sum, mul_comm, mul_assoc, mul_left_comm, add_mul];
    simp [finsupp.sum, mul_comm, mul_assoc, mul_left_comm]

end

lemma sum_is_matrix_mul_left (a b : α) (x y) :
  ((split_left a b).curry.sum (λm f, π x m * f.sum (λm c, c * π y m))) =
  (split_left a b).curry.sum (λ m f, matrix.vec_mul_vec (λ x : fin n → α, π x m)
                                      (λ y : fin n → α, f.sum (λ m c, c * π y m))) x y :=
begin
  rw ←finsupp.sum_matrix _ _ x y,
  refl
end

lemma sum_is_matrix_mul_right (a b : α) (x y) :
  ((split_right a b).curry.sum (λm f, π y m * f.sum (λm c, c * π x m))) =
  (split_right a b).curry.sum (λ m f, matrix.vec_mul_vec (λ x : fin n → α, f.sum (λ m c, c * π x m))
                               (λ y : fin n → α, π y m)) x y :=
begin
  rw ←finsupp.sum_matrix _ _ x y,
  congr, ext, simp [matrix.vec_mul_vec, mul_comm]
end

lemma vmv_rank (m : multiset (fin n)) (f : multiset (fin n) →₀ α) :
  rank (matrix.vec_mul_vec
    (λ x : fin n → α, π x m) (λ y : fin n → α, f.sum (λ m c, c * π y m))).to_lin ≤ 1 :=
matrix.rank_vec_mul_vec _ _

def B : matrix {x // x ∈ A} {x // x ∈ A} α
| x y := p.eval (a • x + b • y)

lemma B_entry_eq_sum (i j) : B i j =
  (split_left a b).curry.sum (λm f, π i.val m * f.sum (λm c, c * π j.val m)) +
  (split_right a b).curry.sum (λm f, π j.val m * f.sum (λm c, c * π i.val m)) :=
eval_add_eq_split_sum

lemma B_entry_eq_sum_matrix (i j) : B i j =
  (split_left a b).curry.sum (λ m f, matrix.vec_mul_vec (λ x, π x m)
                                      (λ y, f.sum (λ m c, c * π y m))) i.val j.val +
  (split_right a b).curry.sum (λ m f, matrix.vec_mul_vec (λ x, f.sum (λ m c, c * π x m))
                               (λ y, π y m)) i.val j.val :=
begin
  rw [B_entry_eq_sum, sum_is_matrix_mul_left, sum_is_matrix_mul_right]
end

lemma B_eq_sum_matrix : B =
  (split_left a b).curry.sum (λ m f, matrix.vec_mul_vec (λ x, π x.val m)
                                      (λ y, f.sum (λ m c, c * π y.val m))) +
  (split_right a b).curry.sum (λ m f, matrix.vec_mul_vec (λ x, f.sum (λ m c, c * π x.val m))
                               (λ y, π y.val m)) :=
begin
  ext, rw B_entry_eq_sum_matrix, congr;
  { rw [finsupp.sum_matrix, finsupp.sum_matrix], refl }
end

lemma B_diagonal_card : fintype.card {i : {x // x ∈ A} // p.eval (-c • i.val) ≠ 0} =
  (A.filter (λ a, p.eval (-c • a) ≠ 0)).card :=
suffices fintype.card { i // i ∈ A ∧ p.eval (-c • i) ≠ 0} = (A.filter (λ a, p.eval (-c • a) ≠ 0)).card,
  begin
    rw ←this,
    apply fintype.card_congr,
    refine {to_fun := λ x, ⟨x.1.1, x.1.2, x.2⟩, inv_fun := λ x, ⟨⟨x.1, x.2.1⟩, x.2.2⟩, ..},
    { simp [function.left_inverse] },
    { simp [function.right_inverse, function.left_inverse] }
  end,
fintype.card_of_subtype _ $ λ a, finset.mem_filter

-- strategy: B = Σ Mᵢ + Σ Nᵢ, where there are ≤ m (d/2) i's and rank(Mᵢ), rank(Nᵢ) ≤ 1
include d_nonneg
lemma B_rank_le : (rank B.to_lin) ≤ ↑(2 * m (d/2)) :=
suffices rank B.to_lin ≤ ↑(m (d/2)) + ↑(m (d/2)), by simpa [two_mul],
begin
  rw [B_eq_sum_matrix, matrix.to_lin_add],
  transitivity,
  apply rank_add_le,
  apply cardinal.add_le_add;
  `[rw [finsupp.sum_matrix_to_lin],
    transitivity,
    apply rank_finset_sum_le,
    rw [←mul_one (m (d/2)), nat.cast_mul, nat.cast_one, ←add_monoid.smul_eq_mul],
    transitivity add_monoid.smul _ (1 : cardinal),
    { apply finset.sum_le_card_mul_of_bdd,
      intros, apply matrix.rank_vec_mul_vec },
    apply add_monoid.smul_le_smul (cardinal.zero_le _)],
    apply split_left_curry_card, apply split_right_curry_card
end

include habc h
lemma B_diagonal : B = matrix.diagonal (λ n, p.eval (-c • n.val)) :=
matrix.ext $ λ i j,
  if hij : i = j then by rw [B, hij, ←add_smul, a_plus_b]; simp; refl
  else begin
    rw [B, h],
    { simp [hij] },
    { exact i.2 },
    { exact j.2 },
    { intro h2, apply hij, exact subtype.eq h2 }
  end

lemma B_rank_eq :
  (rank B.to_lin).to_nat = (A.filter (λa : fin n → α, mv_polynomial.eval (- c • a) p ≠ 0 )).card :=
begin
  rw [B_diagonal, matrix.rank_diagonal, ←B_diagonal_card, cardinal.to_nat_coe],
  congr -- WHY??
end

theorem proposition_11_1 :
  (A.filter (λa : fin n → α, mv_polynomial.eval (- c • a) p ≠ 0 )).card ≤ 2 * m (d / 2) :=
begin
  rw ←B_rank_eq,
  transitivity,
  { apply cardinal.to_nat_le_of_le _,
    apply B_rank_le,
    apply cardinal.nat_lt_omega },
  { rw cardinal.to_nat_coe }
end

end Propostion_11_1

-- corresponds to section 12 of Sander's writeup
section Theorem4
set_option class.instance_max_depth 200
parameters {a b c : α} (h_a_ne_zero : c ≠ 0) (h_sum : a + b + c = 0) (h_n_pos : n > 0)
           {A : finset (fin n → α)}
           (h_A : ∀ x y z ∈ A, a•x + b•y + c•z = (0 : fin n → α) → x = y ∧ x = z)


section
parameters {d : ℚ} (hd : d ≤ (q-1)*n) (d_nonneg : 0 ≤ d) -- q is the cardinality of α

def neg_cA : finset (fin n → α) := A.image (λ z, (-c) • z)

include h_a_ne_zero

lemma map_is_bijective : function.bijective (λ x : fin n → α, -c•x) :=
equiv.bijective $ linear_equiv.to_equiv $ linear_equiv.smul_of_ne_zero (fin n → α) (-c) $
  by simp [h_a_ne_zero]

omit h_a_ne_zero

lemma neg_cA_card : neg_cA.card = A.card :=
finset.card_image_of_injective _ map_is_bijective.1

lemma A_card_le_α_card_n : A.card ≤ fintype.card α^n :=
calc A.card ≤ finset.univ.card : finset.card_le_of_subset (finset.subset_univ _)
        ... = fintype.card (fin n → α) : finset.card_univ
        ... = fintype.card α^n : by simp

def V : set S := zero_set (S' d) (finset.univ \ neg_cA)

def V' : subspace α S := zero_set_subspace (S' d) (finset.univ \ neg_cA)

lemma p_in_V_vanishes {p : S} : p ∈ V →
  ∀ {x : fin n → α}, x ∉ neg_cA → p.eval x = 0
| ⟨_, p_spec⟩ _ h_xnmem := p_spec _ $ finset.mem_sdiff.2 ⟨finset.mem_univ _, h_xnmem⟩

lemma V_dim_finite : (vector_space.dim α V') < cardinal.omega :=
zero_set_subspace_dim _ _ (dim_span_of_finset _)

noncomputable def V_dim := (vector_space.dim α V').to_nat

include h_n_pos h_a_ne_zero

lemma diff_card_comp : (finset.univ \ neg_cA).card + A.card = q^n :=
by rw [finset.card_univ_diff, fintype.card_fin_arrow, neg_cA_card,
  nat.sub_add_cancel A_card_le_α_card_n]; refl

theorem lemma_12_2 :  q^n + V_dim ≥ m d + A.card :=
have V_dim + (finset.univ \ neg_cA).card ≥ m d,
  from lemma_9_2 _ _ V_dim_finite,
by linarith using [diff_card_comp]

omit h_a_ne_zero

def sup (p : S) : finset (fin n → α) :=
finset.univ.filter $ λ x, mv_polynomial.eval x p ≠ 0

lemma mem_sup_iff {p : S} {x : fin n → α} : x ∈ sup p ↔ p.eval x ≠ 0 :=
by rw [sup, finset.mem_filter, and_iff_right (finset.mem_univ _)]

lemma mem_sup {p : S} {x : fin n → α} : p.eval x ≠ 0 → x ∈ sup p := mem_sup_iff.2

lemma exi_max_sup : ∃ P ∈ V, ∀ P' ∈ V, sup P ⊆ sup P' → sup P = sup P' :=
begin
  refine set.finite.exists_maximal_wrt sup _ _ _,
  { refine cardinal.lt_omega_iff_fintype.1 _,
    apply cardinal_lt_omega_of_dim_lt_omega V_dim_finite },
  exact set.ne_empty_iff_exists_mem.2 ⟨0, V'.zero_mem⟩
end

noncomputable def P := classical.some exi_max_sup

lemma P_V : P ∈ V := have _ := classical.some_spec exi_max_sup, by tauto

lemma P_in_S' : P ∈ S' d := P_V.1

lemma P_spec : ∀ P' ∈ V, sup P ⊆ sup P' → sup P = sup P' :=
have _ := classical.some_spec exi_max_sup, by tauto

noncomputable def P_sig := sup P

lemma eval_ne_zero_of_mem_P_sig {x} (hx : x ∈ P_sig) : P.eval x ≠ 0 :=
(finset.mem_filter.1 hx).2

lemma eval_eq_zero_of_not_mem_neg_cA {x} (hx : x ∉ neg_cA) : P.eval x = 0 :=
P_V.2 _ $ (finset.mem_sdiff.2 ⟨finset.mem_univ _, hx⟩)

def W : set S := zero_set V' P_sig

lemma eval_mem_W_eq_zero_of_not_mem_neg_cA {Q} (hQ : Q ∈ W) {x} (hx : x ∉ neg_cA) : Q.eval x = 0 :=
hQ.1.2 _ $ finset.mem_sdiff.2 ⟨finset.mem_univ _, hx⟩

noncomputable def W_dim := (vector_space.dim α (zero_set_subspace V' P_sig)).to_nat

lemma W_dim_ge : W_dim + P_sig.card ≥ V_dim :=
lemma_9_2 V' P_sig (zero_set_subspace_dim _ _ V_dim_finite)

theorem lemma_12_3 : P_sig.card ≥ V_dim :=
le_of_not_gt $
assume hlt : P_sig.card < V_dim,
have W_dim > 0, by linarith using [W_dim_ge],
let ⟨Q, hQW, hQ⟩ := exists_mem_ne_zero_of_dim_pos (cardinal.pos_of_to_nat_pos this) in
have hPQ : ∀ x ∈ P_sig, (P + Q).eval x ≠ 0, from
  assume x hxP_sig,
  have hxP : P.eval x ≠ 0, from eval_ne_zero_of_mem_P_sig hxP_sig,
  have hxQ : Q.eval x = 0, from hQW.2 _ hxP_sig,
  by simp [hxP, hxQ],
have hQq : Q ∈ restrict_degree (fin n) α (q - 1) :=
begin
  refine S'_le_restrict_q _ _, -- if instantiated with `d` and `hQW.1.1` it doesn't terminate!
  exact d,
  exact hQW.1.1,
end,
have ∃ y, Q.eval y ≠ 0, from
  not_forall.1 $ mt (assume h, Q.eq_zero_of_eval_eq_zero _ _ h hQq) hQ,
let ⟨y, hQy⟩ := this in
have hPsig_y : y ∉ P_sig, from λ h, hQy $ hQW.2 _ h,
have hPy : P.eval y = 0, from by_contradiction $ λ h, hPsig_y (mem_sup h),
have (P + Q).eval y ≠ 0, by simp [hPy, hQy],
have hPQsup_y : y ∈ sup (P + Q), from mem_sup this,
have hxPQ : ∀ x, x ∈ finset.univ \ neg_cA → (P + Q).eval x = 0, from
  λ _ hx, by cases finset.mem_sdiff.1 hx with _ hx;
             simp [eval_eq_zero_of_not_mem_neg_cA hx, eval_mem_W_eq_zero_of_not_mem_neg_cA hQW hx],
have hmemS' : P + Q ∈ (S' d), from submodule.add_mem _ P_V.1 hQW.1.1,
have hPQV : (P + Q) ∈ V, from ⟨hmemS', hxPQ⟩,
have hSup : P_sig = sup (P + Q), from P_spec _ hPQV $ λ x hx, mem_sup (hPQ _ hx),
hPsig_y $ by rwa ←hSup at hPQsup_y

def A_antidiag : finset ((fin n → α) × (fin n → α)) :=
(A.product A).filter (λ p, p.1 ≠ p.2)

def abS : finset (fin n → α) := A_antidiag.image $ λ p, a•p.1 + b•p.2

include h_A
lemma inter_empty : abS ∩ neg_cA = ∅ :=
begin
  apply finset.eq_empty_of_forall_not_mem,
  intros x h_xmem,
  rcases finset.mem_image.1 (finset.mem_of_mem_inter_left h_xmem) with ⟨⟨l, r⟩, hlr, hx_sum⟩,
  rcases finset.mem_image.1 (finset.mem_of_mem_inter_right h_xmem) with ⟨w, hw, hx_w⟩,
  cases finset.mem_filter.1 hlr with hp h_lrne,
  cases finset.mem_product.1 hp with h_la h_ra,
  dsimp at hx_sum,
  have : a•l + b•r +c•w = 0, {rw [hx_sum, ←hx_w], simp},
  apply h_lrne,
  refine (h_A _ _ _ _ _ _ this).left; assumption
end

lemma P_vanishes_off_A_image (x : fin n → α) (h_xmemS : x ∉ neg_cA) :
  mv_polynomial.eval x P = 0 :=
p_in_V_vanishes P_V h_xmemS

lemma P_vanishes_on_abS (x : fin n → α) (h_xmemS : x ∈ abS) : mv_polynomial.eval x P = 0 :=
begin
  apply P_vanishes_off_A_image,
  intro h_xmemimage,
  apply finset.not_mem_empty x,
  rw ←inter_empty,
  apply finset.mem_inter_of_mem; assumption
end

lemma filter_eq : finset.univ.filter (λ x : fin n → α, mv_polynomial.eval x P ≠ 0) =
  finset.filter (λ x, mv_polynomial.eval x P ≠ 0) neg_cA :=
finset.ext.2 $ λ x,
⟨ λ h_xmem,
  let ⟨_, h_xeval⟩ := finset.mem_filter.1 h_xmem in
  finset.mem_filter.2 ⟨have _, from P_vanishes_off_A_image x, by clear_aux_decl; tauto, h_xeval⟩,
  λ h_xmem, finset.mem_filter.2 ⟨finset.mem_univ _, (finset.mem_filter.1 h_xmem).2⟩ ⟩

theorem lemma_12_4 : P_sig.card ≤ 2 * m (d/2) :=
have h_P_vanishes' : ∀ x, x ∈ A → ∀ y, y ∈ A → x ≠ y → mv_polynomial.eval (a•x + b•y) P = 0,
begin
  intros x hx y hy hxy,
  apply P_vanishes_on_abS (a•x + b•y),
  apply finset.mem_image.2,
  have : (x, y) ∈ A_antidiag, from finset.mem_filter.2 ⟨finset.mem_product.2 ⟨hx, hy⟩, hxy⟩,
  apply exists.intro,
  existsi this,
  refl
end,
have h_bound : _ := proposition_11_1 d_nonneg A a b c P_in_S' h_sum h_P_vanishes',
have h_P_sig_def : P_sig = finset.image (λ z, (-c) • z) (A.filter (λ x, P.eval (-c•x) ≠ 0)), from calc
    P_sig = finset.univ.filter (λ x, P.eval x ≠ 0) : rfl
      ... = finset.filter (λ x, P.eval x ≠ 0) neg_cA : filter_eq
      ... = finset.image (λ z, (-c) • z) (A.filter (λ x, P.eval (-c•x) ≠ 0)) : finset.image_filter,
have h_P_card : P_sig.card = (A.filter (λ x, P.eval (-c•x) ≠ 0)).card, from calc
    P_sig.card = (finset.image (λ z, (-c) • z) (A.filter (λ a, P.eval (-c•a) ≠ 0))).card : by rw h_P_sig_def
           ... = ((A.filter (λ x, P.eval (-c•x) ≠ 0))).card : finset.card_image_of_injective _ map_is_bijective.1,
by rwa ←h_P_card at h_bound

omit h_A

section
omit h_n_pos

def l125_A : finset (fin n → fin q) := finset.univ

@[reducible] def monom (v : fin n → fin q) : mv_polynomial (fin n) α := monomial v 1

lemma total_degree_monom (v : fin n → fin q) : total_degree (monom v) = fin.sum (v : fin n → ℕ)  :=
by simp only [monom, monomial_total_degree, fin_sum_finsupp_sum]; refl

def l125_B := l125_A.filter $ λ v, ↑(total_degree (monom v)) ≤ d
def l125_C := l125_A.filter $ λ v, ↑(total_degree (monom v)) > d
def l125_D := l125_A.filter $ λ v, ↑(total_degree (monom v)) < ((q : ℚ) - 1)*n - d
def l125_E := l125_A.filter $ λ v, ↑(total_degree (monom v)) ≤ ((q : ℚ) - 1)*n - d

lemma monom_exps_M'_card (k : ℚ) : ((M' k).image monom_exps).card = (M' k).card :=
finset.card_image_of_inj_on $
  λ v1 hv1 v2 hv2 hv, monom_exps_inj (finset.mem_filter.1 hv1).1 (finset.mem_filter.1 hv2).1 hv

lemma monom_exps_M'_card_m (k : ℚ) : ((M' k).image monom_exps).card = m k :=
by rw [monom_exps_M'_card, M'_card]

lemma B_C_disjoint : disjoint l125_B l125_C :=
λ x hx, by linarith using [(finset.mem_filter.1 (finset.mem_of_mem_inter_left hx)).2,
                           (finset.mem_filter.1 (finset.mem_of_mem_inter_right hx)).2]

lemma B_C_union : l125_B ∪ l125_C = l125_A :=
finset.ext.2 $ λ x,
⟨ λ _, finset.mem_univ _,
  λ _, finset.mem_union.2 $
    if hx : ↑(total_degree (monom x)) ≤ d then or.inl (finset.mem_filter.2 ⟨finset.mem_univ _, hx⟩)
    else or.inr (finset.mem_filter.2 ⟨finset.mem_univ _, lt_of_not_ge hx⟩) ⟩

lemma filter_eq_image (r : ℚ) :
  (l125_A.filter $ λ v, ↑(total_degree (monom v)) ≤ r) = (M' r).image monom_exps :=
finset.ext.2 $ λ x,
⟨ λ h, finset.mem_image.2
  ⟨ monomial x 1, finset.mem_filter.2 ⟨monomial_mem_M _, (finset.mem_filter.1 h).2⟩, by simp ⟩,
  λ h, finset.mem_filter.2
  ⟨ finset.mem_univ _,
    let ⟨a, ha, hax⟩ := finset.mem_image.1 h,
        ha' := (finset.mem_filter.1 ha).2 in
    by rw [←hax, monom, monom_exps_def (mem_M_of_mem_M' ha)]; exact ha' ⟩⟩

lemma le_helper (v : ℕ) : q - (v + 1) < q := nat.sub_lt one_le_q (nat.succ_pos _)

def invol (v : fin n → fin q) : fin n → fin q :=
λ x, ⟨q - (v x + 1), le_helper _⟩

lemma invol_add (v i) : ((invol v) i : ℕ) + v i = q - 1 :=
show q - (↑(v i) + 1) + ↑(v i) = q - 1,
begin
  rw ←nat.sub_add_comm,
  { apply nat.sub_eq_of_eq_add,
    rw [add_assoc _ 1, nat.add_sub_cancel'],
    { ac_refl },
    { exact one_le_q } },
  { apply nat.succ_le_of_lt,
    apply fin.is_lt }
end

-- not sure why it appears like this below
lemma invol_add' (v i) : (⇑(invol v) : fin n → ℕ) i + (⇑v : fin n → ℕ) i = q - 1 :=
invol_add _ _

lemma invol_is_involution (x : fin n → fin q) : invol (invol x) = x :=
funext $ λ i, (fin.ext_iff _ _).2 $
  show q - (q - (x i + 1) + 1) = x i,
  begin
    rw [←nat.sub_sub, ←nat.sub_sub, nat.sub_sub, nat.sub_add_cancel, nat.sub_sub_self],
    { apply le_of_lt, apply fin.is_lt },
    { apply (nat.add_le_to_le_sub _ _).1,
      { rw add_comm, apply fin.is_lt },
      { apply le_of_lt, apply fin.is_lt }}
  end

lemma invol_inj : function.injective invol :=
λ v1 v2 hv, by rw [←invol_is_involution v1, ←invol_is_involution v2, hv]

lemma total_degree_invol_eq (v : fin n → fin q) :
   ↑(total_degree (monom (invol v))) = ((q : ℚ)-1)*n - ↑(total_degree (monom v)) :=
begin
  simp only [total_degree_monom],
  apply eq_sub_of_add_eq,
  rw [←nat.cast_add, fin.sum_add],
  simp only [invol_add'],
  have qcast: ((q : ℚ) - 1) * n = ↑((q - 1)*n), {simp [nat.cast_sub one_le_q]},
  rw [qcast, mul_comm], congr, -- something funny with the casts here
  convert fin.sum_const _ _,
  simp
end

lemma invol_total_degree (v : fin n → fin q) :
  ↑(total_degree (monom v)) > d ↔ ↑(total_degree (monom (invol v))) < ((q : ℚ) - 1)*n - d :=
by constructor; { rw total_degree_invol_eq, intro, linarith }

lemma D_eq_C_image_invol : l125_D = l125_C.image invol :=
finset.ext.2 $ λ v,
  ⟨ λ h, finset.mem_image.2
     ⟨invol v, finset.mem_filter.2 ⟨finset.mem_univ _,
       by rw [invol_total_degree, invol_is_involution];
          apply (finset.mem_filter.1 h).2⟩, invol_is_involution _⟩,
    λ h, finset.mem_filter.2 ⟨finset.mem_univ _,
      begin
        rcases finset.mem_image.1 h with ⟨v', hv', hvv'⟩,
        rw [←hvv', ←invol_total_degree],
        apply (finset.mem_filter.1 hv').2
      end⟩⟩

-- this is useful in asymptotics
parameters (α n d)
lemma h_B_card : l125_B.card = m d :=
by rw [l125_B, filter_eq_image, monom_exps_M'_card_m]
parameters {α n d}

include h_n_pos
theorem lemma_12_5 : q^n ≤ m (((q : ℚ) - 1)*n - d) + m d :=
have h_A_card : l125_A.card = q^n, by simp [finset.card_univ, l125_A],
have h_B_card : l125_B.card = m d, by rw [l125_B, filter_eq_image, monom_exps_M'_card_m],
have h_B_C_card : l125_B.card + l125_C.card = l125_A.card,
  by rw [←finset.card_disjoint_union B_C_disjoint, B_C_union],
have h_C_D_card : l125_C.card = l125_D.card,
  by rw [←finset.card_image_of_injective _ invol_inj, D_eq_C_image_invol],
have h_D_E_card : l125_D.card ≤ l125_E.card, from
  finset.card_le_card_of_inj_on id
    (λ a ha, finset.mem_filter.2 ⟨finset.mem_univ _, le_of_lt ((finset.mem_filter.1 ha).2)⟩)
    (λ _ _ _ _, id),
have h_E_card : l125_E.card = m ((q-1)*n - d), by rw [l125_E, filter_eq_image, monom_exps_M'_card_m],
by linarith

include h_A hd h_a_ne_zero h_sum d_nonneg
theorem lemma_12_6 : A.card ≤ 2 * m (d/2) + m ((q - 1)*n - d) :=
by linarith using [lemma_12_2, lemma_12_3, lemma_12_4, lemma_12_5]

end

end

include h_A h_n_pos h_a_ne_zero h_sum
theorem theorem_12_1 : A.card ≤ 3*(m (1/3*((q-1)*n))) :=
begin
  set qn := ((q : ℚ) - 1)*n with hqn,
  set! d := 2/3*qn with hd,
  have : qn ≥ 0, from mul_nonneg (sub_nonneg_of_le one_le_q_real) (nat.cast_nonneg _),
  have : d ≤ qn, {linarith},
  have h_d2 : d / 2 = 1/3 * qn, {linarith},
  have h_qnd : qn - d = 1/3 * qn, {linarith},
  have h_l5, from lemma_12_6 this,
  rw [h_d2, h_qnd] at h_l5,
  convert h_l5 _,
  { ring },
  { apply mul_nonneg,
    { norm_num },
    { assumption } }
end

end Theorem4
end