/-
Copyright (c) 2018 Sander Dahmen, Johannes Hölzl, Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sander Dahmen, Johannes Hölzl, Robert Y. Lewis

"On large subsets of 𝔽ⁿ_q with no three-term arithmetic progression"
by J. S. Ellenberg and D. Gijswijt

This file establishes the asymptotic behavior of the cap set cardinality bound
proved in section_10_11_12.lean.
It corresponds to the second half of section 13 of our blueprint.
-/

import data.vector2 data.zmod.basic data.nat.modeq
import tactic.library_search
import
  section_10_11_12
  has_deriv


def iseg (q j) : finset (fin q) :=
finset.univ.filter (λ k, k.val ≤ j)

lemma val_le_right_of_iseg {q j} {v : fin q} (h : v ∈ iseg q j) : v.val ≤ j :=
(finset.mem_filter.1 h).2

lemma mem_iseg_of_le {q j} {v : fin q} (h : v.val ≤ j) : v ∈ iseg q j :=
by simp [iseg, h]

section fix_q
parameter (q : ℕ)

section cf_def
parameter (n : ℕ)

def sf (j : ℕ) : finset (vector (fin q) n) := finset.univ.filter (λ f, (f.nat_sum = j))

parameter {n}

lemma mem_sf {j} {v : vector (fin q) n} (h : v.nat_sum = j) : v ∈ sf j :=
finset.mem_filter.2 ⟨finset.mem_univ _, h⟩

lemma sf_sum {j : ℕ} {f : vector (fin q) n} (h : f ∈ sf j) : f.nat_sum = j :=
(finset.mem_filter.1 h).2

lemma sf_disjoint {j1 j2 : ℕ} (h : j1 ≠ j2) : sf j1 ∩ sf j2 = ∅ :=
finset.eq_empty_of_forall_not_mem $ λ x hx, h $ by simp at hx; rw [←sf_sum hx.1, ←sf_sum hx.2]

def sf_lift_i (i : fin q) (sfj : finset (vector (fin q) n)) : finset (vector (fin q) (n+1)) :=
sfj.image $ vector.cons i

lemma sf_lift_i_sum {i : fin q} {j} {f} (hf : f ∈ sf_lift_i i (sf j)) : f.nat_sum = i.val + j :=
by rcases finset.mem_image.1 hf with ⟨_, hg, hfg⟩; simp [hfg.symm, sf_sum hg]

lemma sf_lift_i_card (i : fin q) (sfj : finset (vector (fin q) n)) :
  (sf_lift_i i sfj).card = sfj.card :=
finset.card_image_of_inj_on $ λ _ _ _ _, vector.cons_inj

lemma sf_lift_i_inter_empty  {i j : fin q} (h : i ≠ j) (s1 s2 : finset (vector (fin q) n)) :
  sf_lift_i i s1 ∩ sf_lift_i j s2 = ∅ :=
finset.eq_empty_of_forall_not_mem $ λ x hx,
  let ⟨hx1, hx2⟩ := finset.mem_inter.1 hx,
      ⟨a1, hm1, ha1⟩ := finset.mem_image.1 hx1,
      ⟨a2, hm2, ha2⟩ := finset.mem_image.1 hx2 in
  h $ vector.cons_inj_left $ by rwa ←ha2 at ha1

lemma mem_sf_lift_i (v) : v ∈ sf_lift_i (vector.head v) (sf (v.nat_sum - (vector.head v).val)) :=
finset.mem_image.2 $
  ⟨v.tail, mem_sf $ eq.symm $ nat.sub_eq_of_eq_add $ by rw [←vector.nat_sum_head_tail], by simp⟩

parameter (n)
def sf_lift (j : ℕ) : finset (vector (fin q) (n+1)) :=
finset.bind (iseg q j) (λ i, sf_lift_i i (sf (j - i)))

def cf (j : ℕ) : ℕ := (sf j).card
parameter {n}

lemma sf_sum_mem_lift {j : ℕ} {f : vector (fin q) (n+1)} (h : f ∈ sf_lift j) : f.nat_sum = j :=
begin
  simp [sf_lift, sf_lift_i] at h,
  rcases h with ⟨k, ⟨hk, g, hg, hfg⟩⟩,
  suffices : k.val + (j - k.val) = j, {simpa [hfg.symm, sf_sum hg]},
  rw [nat.add_comm, nat.sub_add_cancel],
  apply val_le_right_of_iseg hk
end

end cf_def

lemma head_le_of_mem_sf {j n : ℕ} : ∀ {v : vector (fin q) (n+1)} (h : v ∈ sf (n+1) j), v.head.val ≤ j
| p@⟨h::t,_⟩ hmem :=
  have hsum : _, from vector.nat_sum_head_tail p,
  by rw sf_sum hmem at hsum; linarith

lemma sf_lift_succ (n j : ℕ) : sf (n + 1) j = sf_lift n j :=
begin
  ext v, constructor,
  { intro hv,
    apply finset.mem_bind.2,
    use [v.head, mem_iseg_of_le (head_le_of_mem_sf hv)],
    rw ←sf_sum hv,
    apply mem_sf_lift_i },
  { intro hv, simp [sf_sum_mem_lift hv, sf] }
end

lemma sf_lift_card' (n j : ℕ) :
  (sf_lift n j).card = (iseg q j).sum (λ u, finset.card ((λ i, sf_lift_i i (sf n (j - ↑i))) u)) :=
finset.card_bind $ λ x hx y hy hxy, sf_lift_i_inter_empty hxy _ _

lemma sf_lift_card (n j : ℕ) : (sf_lift n j).card = (iseg q j).sum (λ u, cf n (j - u)) :=
by simp only [sf_lift_card', sf_lift_i_card, cf]

lemma cf_zero_zero (h : q > 0) : cf 0 0 = 1 :=
finset.card_eq_one.2 ⟨ vector.nil, finset.ext.2 $
  λ v, ⟨λ _, finset.mem_singleton.2 v.eq_nil, λ hv, mem_sf (by rw finset.mem_singleton.1 hv; simp)⟩ ⟩

lemma cf_zero_succ (j : ℕ) : cf 0 (j + 1) = 0 :=
finset.card_eq_zero.2 $ finset.eq_empty_of_forall_not_mem $ λ v hv, nat.succ_ne_zero j $ by simpa using sf_sum hv

lemma cf_one_lt {j : ℕ} (hj : j < q) : cf 1 j = 1 :=
begin
  have hfs : finset.univ.filter (λ f : vector (fin q) 1, f.nat_sum = j) = {⟨j, hj⟩::vector.nil},
  { ext v, simp, constructor,
    { rw vector.vec_one v,
      intro h,
      congr,
      rw fin.ext_iff,
      simpa using h },
    { intro hv, simp [hv] } },
  simp only [cf, sf, hfs], refl
end

lemma cf_one_ge {j : ℕ} (hj : j ≥ q) : cf 1 j = 0 :=
begin
  simp only [cf, sf],
  convert finset.card_empty,
  apply finset.eq_empty_of_forall_not_mem,
  intros x hx,
  cases finset.mem_filter.1 hx with _ hx,
  apply not_lt_of_ge hj,
  rw ←hx,
  apply vector.nat_sum_one
end

lemma cf_succ (n j : ℕ) : cf (n + 1) j = (iseg q j).sum (λ u, cf n (j - u)) :=
by rw [cf, sf_lift_succ, sf_lift_card]

lemma cf_mul (n j : ℕ) : (finset.range (j + 1)).sum (λ i, (cf 1 (j - i)) * cf (n + 1) i) = cf (n+2) j :=
have hfil : finset.range (j + 1) = (finset.range (j + 1)).filter (λ k, j - k < q) ∪ (finset.range _).filter _,
  from eq.symm (finset.filter_union_filter_neg_eq _),
begin
  rw [cf_succ, hfil, finset.sum_union],
  { have hgeq : ((finset.range (j + 1)).filter (λ k, ¬ j - k < q)).sum (λ i, cf 1 (j - i) * cf (n + 1) i) = 0,
    { apply finset.sum_eq_zero,
      intros k hk,
      simp [cf_one_ge (le_of_not_gt (finset.mem_filter.1 hk).2)] },
    rw [hgeq, add_zero],
    symmetry,
    apply finset.sum_bij (λ (a : fin q) _, j - a.val),
    { intros a ha,
      simp,
      refine ⟨nat.sub_lt_succ _ _, _⟩,
      rw nat.sub_sub_self (val_le_right_of_iseg ha),
      exact a.is_lt },
    { intros a ha,
      simp [nat.sub_sub_self (val_le_right_of_iseg ha), cf_one_lt a.is_lt], refl },
    { intros a a2 ha1 ha2 heq,
      apply (fin.ext_iff _ _).2,
      rwa ← nat.sub_eq_sub_iff; apply val_le_right_of_iseg; assumption },
    { intros b hb,
      simp at hb,
      use [⟨j-b, hb.2⟩, mem_iseg_of_le (nat.sub_le_self _ _)],
      simp [nat.sub_sub_self (nat.le_of_lt_succ hb.1)] } },
  { rw [finset.filter_not], simp }
end

def one_coeff_poly : polynomial ℕ :=
(finset.range q).sum (λ k, (polynomial.X : polynomial ℕ) ^ k)

lemma one_coeff_poly_coeff {n : ℕ} : one_coeff_poly.coeff n = if n < q then 1 else 0 :=
begin
  rw [one_coeff_poly],
  symmetry,
  have hlx : (λ k : ℕ, ((polynomial.X : polynomial ℕ) ^k).coeff n) = (λ k : ℕ, if n = k then 1 else 0),
  { ext k, rw [polynomial.coeff_X_pow k n] },
  have hfr : finset.range q = (finset.range q).filter (λ k, n = k) ∪ (finset.range q).filter (λ k, n ≠ k),
    from eq.symm (finset.filter_union_filter_neg_eq _),
  have hoeq : (finset.range q).sum (λ k, ((polynomial.X : polynomial ℕ)^k).coeff n) = if n < q then 1 else 0,
  { rw [hlx, hfr, finset.sum_union, ←add_zero (ite _ _ _)],
    { congr,
      { by_cases hnq : n < q,
        { have hs : (finset.range q).filter (λ k, n = k) = finset.singleton n,
          { ext a, simp, constructor,
            { rintros ⟨_, ha⟩, rw ha },
            { intro ha, rw ha, exact ⟨hnq, rfl⟩ } },
          simp [hs, hnq] },
        { simp [hnq],
          apply finset.sum_eq_zero,
          intros x hx,
          exfalso,
          apply hnq,
          rw (finset.mem_filter.1 hx).2,
          apply finset.mem_range.1 (finset.mem_filter.1 hx).1 } },
      { apply finset.sum_eq_zero,
        intros _ hx,
        simp [(finset.mem_filter.1 hx).2] } },
    { apply finset.eq_empty_of_forall_not_mem,
      intros x hx,
      cases finset.mem_inter.1 hx with hx1 hx2,
      cases finset.mem_filter.1 hx1 with _ hxn,
      cases finset.mem_filter.1 hx2 with _ hxn2,
      exact hxn2 hxn }},
  rw ←hoeq,
  apply finset.sum_hom (λ p, polynomial.coeff p n),
  apply_instance,
  convert is_add_monoid_hom.mk _,
  { convert is_add_hom.mk _,
    intros,
    apply polynomial.coeff_add },
  { apply polynomial.coeff_zero }
end

lemma one_coeff_poly_coeff_lt {n : ℕ} (h : n < q): one_coeff_poly.coeff n = 1 :=
have he : _ := @one_coeff_poly_coeff n,
have 1 = (if n < q then 1 else 0), by split_ifs; refl,
by rw this; exact he

lemma one_coeff_poly_coeff_ge {n : ℕ} (h : n ≥ q): one_coeff_poly.coeff n = 0 :=
have he : _ := @one_coeff_poly_coeff n,
have 0 = (if n < q then 1 else 0), by simp [not_lt_of_ge h],
by rw this; exact he

lemma one_coeff_poly_eval₂_nonneg {β} [linear_ordered_semiring β] {f : ℕ → β} (hf : ∀ z, f z ≥ 0) {b : β} (hb : b ≥ 0) :
  0 ≤ one_coeff_poly.eval₂ f b :=
finset.zero_le_sum $ λ x _, mul_nonneg (hf _) (pow_nonneg hb _)

theorem lemma_13_9 (hq : q > 0) : ∀ n j : ℕ, (one_coeff_poly ^ n).coeff j = cf n j
| 0 0 := by rw [pow_zero, polynomial.coeff_one, cf_zero_zero]; [refl, assumption]
| 0 (j+1) := by rw [pow_zero, polynomial.coeff_one, cf_zero_succ]; simp [show 0 ≠ j + 1, from (nat.succ_ne_zero _).symm]
| 1 j :=
  begin
    by_cases h : j < q,
    { rw [pow_one, cf_one_lt h, one_coeff_poly_coeff_lt h] },
    { rw [pow_one, cf_one_ge (le_of_not_gt h), one_coeff_poly_coeff_ge (le_of_not_gt h)] }
  end
| (n+2) j := calc
  (one_coeff_poly ^ (n + 2)).coeff j
      = (one_coeff_poly * one_coeff_poly ^ (n + 1)).coeff j : rfl
  ... = _ : polynomial.coeff_mul_right _ _ _
  ... = (finset.range (j + 1)).sum (λ i, one_coeff_poly.coeff (j - i) * cf (n + 1) i) : by congr; ext; rw lemma_13_9
  ... = (finset.range (j + 1)).sum (λ i, (one_coeff_poly ^ 1).coeff (j - i) * cf (n + 1) i) : by rw pow_one
  ... = (finset.range (j + 1)).sum (λ i, cf 1 (j - i) * cf (n + 1) i) : by congr; ext i; rw lemma_13_9
  ... = cf (n + 2) j : cf_mul _ _

parameter {q}
def vector_of_fin_fn : ∀ {n} (v : fin n → fin q), vector (fin q) n
| 0  v := vector.nil
| (n+1) v := v ⟨n, nat.lt_succ_self _⟩ :: vector_of_fin_fn (λ k : fin n, v ⟨k, nat.lt_succ_of_lt k.is_lt⟩)

lemma vector_of_fin_fn_nth : ∀ n (v : fin (n+1) → fin q) (i : fin (n+1)),
  (vector_of_fin_fn v).nth i = v ⟨n - i.val, nat.lt_succ_of_le (nat.sub_le_self _ _)⟩
| 0 v x :=
  have hx : x = ⟨0, zero_lt_one⟩, from (fin.ext_iff _ _).2 (nat.eq_zero_of_le_zero (nat.le_of_lt_succ x.is_lt)),
  by simp [vector_of_fin_fn, hx]; refl
| (n+1) v x :=
  begin
    rw [vector_of_fin_fn],
    by_cases hx : x.val = 0,
    { have hx' : x = 0, by simp [fin.ext_iff, hx, fin.val_zero],
      simp [hx', vector.nth_zero, fin.val_zero] },
    { have : x = fin.succ ⟨x.val - 1, _⟩,
      { apply fin.eq_of_veq,
        rw fin.succ_val,
        symmetry,
        apply nat.sub_add_cancel (nat.succ_le_of_lt (nat.pos_of_ne_zero hx)) },
      { rw [this, vector.nth_cons_succ, vector_of_fin_fn_nth],
        congr, simp, refl },
      { rw nat.sub_lt_right_iff_lt_add,
        apply x.is_lt,
        exact nat.succ_le_of_lt (nat.pos_of_ne_zero hx) }}
  end

def fin_fn_of_vector : ∀ {n} (v : vector (fin q) n), fin n → fin q
| 0 v i := fin_zero_elim i
| (n+1) v i := v.nth ⟨n - i.val, nat.lt_succ_of_le (nat.sub_le_self _ _)⟩

lemma vector_of_fin_fn_inv : ∀ {n} (v : vector (fin q) n), vector_of_fin_fn (fin_fn_of_vector v) = v
| 0 v := vector.ext $ λ k, fin_zero_elim k
| (k+1) v :=
  begin
    ext m,
    simp only [fin_fn_of_vector, vector_of_fin_fn_nth],
    congr,
    rw fin.ext_iff,
    apply nat.sub_sub_self,
    exact nat.le_of_lt_succ m.is_lt
  end

lemma sum_fin_fn_of_vector : ∀ {n} (v : vector (fin q) n), fin.sum (↑(fin_fn_of_vector v) : fin n → ℕ) = v.nat_sum
| 0 v := by simp [fin.sum_zero]
| (k+1) v :=
  begin
    rw [fin.sum_succ, vector.nat_sum_head_tail],
    congr,
    { simp [cast_fin_fn, fin_fn_of_vector], congr, apply vector.nth_zero },
    { convert sum_fin_fn_of_vector _,
      ext x,
      simp [cast_fin_fn, fin_fn_of_vector],
      cases k,
      { apply fin_zero_elim x },
      { rw [fin_fn_of_vector, vector.nth_tail],
        congr,
        rw nat.succ_sub; [refl, exact nat.le_of_lt_succ x.is_lt] } }
   end


lemma inv_in_range {d : ℚ} (hd : 0 ≤ d) {n} {v : vector (fin q) n}
  (hv : v ∈ (finset.range (int.nat_abs ⌊d⌋ + 1)).bind (sf n)) :
  ↑(fin.sum (↑(fin_fn_of_vector v) : fin n → ℕ)) ≤ d :=
begin
  rw sum_fin_fn_of_vector,
  simp [-add_comm] at hv,
  rcases hv with ⟨a, ha, ha2⟩,
  replace ha2 := sf_sum ha2,
  have : 0 ≤ ⌊d⌋ := le_floor.2 hd,
  calc (vector.nat_sum v : ℚ) ≤ int.nat_abs ⌊d⌋ :
      by rw ha2; exact nat.cast_le.2 (nat.succ_le_succ_iff.1 ha)
    ... = ((int.nat_abs ⌊d⌋ : ℤ) : ℚ) : by rw [← coe_coe]
    ... = _ : by rw [← int.eq_nat_abs_of_zero_le this]
    ... ≤ d : floor_le _
end

lemma nat_sum_vector_of_fin_fn : ∀ {n} (v : fin n → fin q), (vector_of_fin_fn v).nat_sum = fin.sum (↑v : fin n → ℕ)
| 0 v := by simp [vector_of_fin_fn, fin.sum_zero]
| (n+1) v := by simp [vector_of_fin_fn, nat_sum_vector_of_fin_fn, fin.sum_succ]; refl


lemma vector_of_fin_fn_mem_bind {n} {d : ℚ}
  {v : fin n → fin q} (hv : ↑(fin.sum (↑v : fin n → ℕ)) ≤ d) :
  vector_of_fin_fn v ∈ (finset.bind (finset.range (int.nat_abs ⌊d⌋ + 1)) (sf n)) :=
begin
  apply finset.mem_bind.2,
  use fin.sum (↑v : fin n → ℕ),
  split,
  { apply finset.mem_range.2,
    refine (nat.cast_lt.1 $ lt_of_le_of_lt hv _),
    rw [nat.cast_add, nat.cast_one],
    have hd : 0 ≤ ⌊d⌋ := le_floor.2 (le_trans (nat.cast_le.2 (nat.zero_le _)) hv),
    have : (int.nat_abs ⌊d⌋ : ℚ) = ((int.nat_abs ⌊d⌋ : ℤ) : ℚ), { rw ← coe_coe },
    rw [this, ← int.eq_nat_abs_of_zero_le hd],
    exact lt_floor_add_one d },
  { apply mem_sf,
    apply nat_sum_vector_of_fin_fn }
end

lemma vector_of_fin_fn_inj : ∀ {n} {v1 v2 : fin n → fin q}, vector_of_fin_fn v1 = vector_of_fin_fn v2 → v1 = v2
| 0 v1 v2 h := funext $ λ x, fin_zero_elim x
| (n+1) v1 v2 h := funext $ λ x,
  have (λ k : fin n, v1 ⟨k, nat.lt_succ_of_lt k.is_lt⟩) = (λ k : fin n, v2 ⟨k, nat.lt_succ_of_lt k.is_lt⟩),
    from vector_of_fin_fn_inj $ vector.cons_inj h,
  begin
    by_cases hx : x.val < n,
    { convert congr_fun this ⟨x.val, _⟩,
      repeat {simp [fin.ext_iff], refl },
      exact hx },
    { have hxn : x = ⟨n, nat.lt_succ_self _⟩, from fin.eq_of_veq (nat.eq_of_lt_succ_of_not_lt x.is_lt hx),
      rw hxn, apply vector.cons_inj_left h }
  end


end fix_q

noncomputable def crq (r : ℝ) (q : ℕ) := ((one_coeff_poly q).eval₂ coe r) / r ^ ((q-1 : ℝ)/3)

lemma one_coeff_poly_support (q : ℕ) : finsupp.support (one_coeff_poly q) = finset.range q :=
begin
  ext x,
  constructor,
  { intro hx,
    have : (one_coeff_poly q).coeff x ≠ 0, from finsupp.mem_support_iff.1 hx,
    rw finset.mem_range,
    apply lt_of_not_ge,
    exact mt (one_coeff_poly_coeff_ge _) this },
  { intro hx,
    rw finsupp.mem_support_iff,
    apply ne_of_gt,
    convert zero_lt_one,
    apply one_coeff_poly_coeff_lt,
    simpa using hx }
end

lemma one_coeff_poly_nat_degree {q : ℕ} (hq : q > 0) : (one_coeff_poly q).nat_degree = q - 1 :=
begin
  have hq : ∃ n, q = n + 1, from nat.exists_eq_succ_of_ne_zero (ne_of_gt hq),
  cases hq with n hn,
  rw [hn, polynomial.nat_degree, polynomial.degree, one_coeff_poly_support, finset.sup_range],
  simp [option.get_or_else]
end

lemma one_coeff_poly_pow_nat_degree {q : ℕ} (n : ℕ) (hq : q > 0) :
  ((one_coeff_poly q)^n).nat_degree = (q-1)*n :=
begin
  rw [polynomial.nat_degree_pow_eq', one_coeff_poly_nat_degree hq, mul_comm],
  apply ne_of_gt,
  apply pow_pos,
  rw [polynomial.leading_coeff, one_coeff_poly_nat_degree hq, one_coeff_poly_coeff_lt],
  { exact zero_lt_one },
  { apply nat.sub_lt hq zero_lt_one }
end

section
variables {α : Type} [discrete_field α] [fintype α] (n : ℕ)
local notation `m` := m α n
local notation `q` := @q α _ _

lemma q_ge_two : q ≥ 2 :=
finset.card_le_of_inj_on (λ n, if n = 0 then 0 else 1) (λ _ _, finset.mem_univ _) $ λ i j hi hj,
  begin
    split_ifs; simp *,
    have hi' : i = 1,
      from nat.eq_of_lt_succ_of_not_lt hi (not_lt_of_ge (nat.succ_le_of_lt (nat.pos_of_ne_zero h))),
    have hj' : j = 1,
      from nat.eq_of_lt_succ_of_not_lt hj (not_lt_of_ge (nat.succ_le_of_lt (nat.pos_of_ne_zero h_1))),
    rwa ←hj' at hi'
  end

theorem lemma_13_8 {d : ℚ} (hd : d ≥ 0) :
  m d = (finset.range (⌊d⌋.nat_abs + 1)).sum (cf q n) :=
begin
  have hbc : finset.card (finset.univ.filter (λ v : fin n → fin q, ↑(fin.sum (↑v : fin n → ℕ)) ≤ d)) = m d,
  { have h := h_B_card α n d,
    simp only [l125_A, l125_B, total_degree_monom] at h,
    convert h },
  have hse : finset.card (finset.univ.filter (λ v : fin n → fin q, ↑(fin.sum (↑v : fin n → ℕ)) ≤ d)) = finset.card (finset.bind (finset.range (⌊d⌋.nat_abs + 1)) (λ k, sf q n k)),
  { apply finset.card_congr (λ v _, vector_of_fin_fn v),
    { intros _ ha, exact vector_of_fin_fn_mem_bind (finset.mem_filter.1 ha).2 },
    { intros _ _ _ _ hv1v2, exact vector_of_fin_fn_inj hv1v2 },
    { dsimp, intros b hb,
      exact ⟨ fin_fn_of_vector b, finset.mem_filter.2 ⟨finset.mem_univ _, (inv_in_range hd hb)⟩,
              vector_of_fin_fn_inv _ ⟩ }},
  rw [←hbc, hse, finset.card_bind], refl,
  intros _ _ _ _, apply sf_disjoint
end

lemma int.cast_nat_abs {z : ℤ} (hz : 0 ≤ z) : (z.nat_abs : ℝ) = z :=
by norm_cast; exact int.nat_abs_of_nonneg hz

lemma one_coeff_poly_pow_eval₂_nonneg {r : ℝ} (hr : 0 ≤ r) (k) : 0 ≤ polynomial.eval₂ coe r (one_coeff_poly k ^ n) :=
begin
  rw polynomial.eval₂_pow,
  apply pow_nonneg,
  apply one_coeff_poly_eval₂_nonneg,
  { exact nat.cast_nonneg },
  { assumption }
end

lemma finset_sum_range {r : ℝ} (hr : 0 < r) (hr2 : r < 1) :
  (finset.range ((q - 1) * n + 1)).sum (λ (j : ℕ), r ^ j * ↑(cf q n j)) =
     ((one_coeff_poly q) ^ n).eval₂ coe r :=
begin
  convert polynomial.poly_eq_deg_sum _ _ _,
  { rw one_coeff_poly_pow_nat_degree _ q_pos },
  { ext, rw [lemma_13_9, mul_comm], exact q_pos },
  { simp }
end

theorem theorem_14_1 {r : ℝ} (hr : 0 < r) (hr2 : r < 1) : ↑(m (((q : ℚ)- 1)*n / 3)) ≤ (crq r q) ^ n :=
let e := ⌊((q - 1 : ℝ))*n / 3⌋.nat_abs in
have hpos : ((q - 1 : ℝ))*n / 3 ≥ 0, from div_nonneg (mul_nonneg (sub_nonneg_of_le (by exact_mod_cast one_le_q)) (nat.cast_nonneg _)) (by norm_num),
have r^e * m (((q : ℚ)- 1)*n / 3) = (finset.range (e+1)).sum (λ j, r^e * cf q n j),
begin
  rw [lemma_13_8, ←finset.sum_hom coe, finset.mul_sum],
  { congr' 2, dsimp [e], congr' 2, rw ←@rat.cast_floor ℝ _ _ (((q : ℚ) + -1) * n /3), simp },
  { apply_instance },
  { assumption_mod_cast }
end,
have hmr : ∀ x, x ∈ finset.range (e + 1) → x < (q-1)*n + 1, from λ x hx,
begin
  dsimp only [e] at hx,
  have hx' := finset.mem_range.1 hx,
  apply lt_of_lt_of_le hx',
  apply nat.succ_le_succ,
  suffices : (int.nat_abs ⌊((q : ℝ) -1)*n / 3⌋ : ℝ) ≤ ↑((q-1)*n), from nat.cast_le.1 this,
  rw int.cast_nat_abs,
  { apply le_trans,
    { apply floor_le },
    { apply (div_le_iff _).2,
      convert le_mul_of_ge_one_right _ _,
      { simp [one_le_q], },
      { apply mul_nonneg,
        { apply sub_nonneg_of_le, exact_mod_cast one_le_q },
        { apply nat.cast_nonneg } },
      repeat { norm_num } } },
  rw floor_nonneg,
  exact hpos
end,
have r^e * m (((q : ℚ)- 1)*n / 3) ≤ ((one_coeff_poly q)^n).eval₂ coe r, from calc
     _ = (finset.range (e+1)).sum (λ j, r^e * cf q n j) : this
   ... ≤ (finset.range (e+1)).sum (λ j, r^j * cf q n j) : finset.sum_le_sum $ λ x hx,mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (le_of_lt hr) (le_of_lt hr2) (by linarith [finset.mem_range.1 hx])) (nat.cast_nonneg _)
   ... ≤  (finset.range ((q - 1) * n + 1)).sum (λ j, r^j * cf q n j) : finset.sum_le_sum_of_subset_of_nonneg (λ x hx, finset.mem_range.2 (hmr _ hx)) $
            λ x hx1 hx2, mul_nonneg (pow_nonneg (le_of_lt hr) _) (nat.cast_nonneg _)
   ... = ((one_coeff_poly q)^n).eval₂ coe r : finset_sum_range _ hr hr2,
calc _ ≤ ((one_coeff_poly q)^n).eval₂ coe r / r^e : (le_div_iff (pow_pos hr _)).2 (by convert this using 1; apply mul_comm)
   ... ≤ ((one_coeff_poly q)^n).eval₂ coe r / r^(((q - 1 : ℝ))*n / 3) : div_le_div_of_le_left
         (one_coeff_poly_pow_eval₂_nonneg _ (le_of_lt hr) _)
         (pow_pos hr _)
         (real.rpow_pos_of_pos hr _)
         begin rw ←real.rpow_nat_cast, apply real.rpow_le hr (le_of_lt hr2), dsimp [e], rw int.cast_nat_abs, apply floor_le, apply floor_nonneg.2 hpos end
   ... = ((one_coeff_poly q)^n).eval₂ coe r / (r^(((q - 1 : ℝ)) / 3))^n : begin rw [←real.rpow_nat_cast _ n, ←real.rpow_mul], {congr, ring}, {exact le_of_lt hr} end
   ... = ((one_coeff_poly q).eval₂ coe r / (r^(((q - 1 : ℝ)) / 3)))^n : begin rw [polynomial.eval₂_pow, ←div_pow], apply ne_of_gt, apply real.rpow_pos_of_pos hr end


end

lemma one_coeff_poly_eval_ge_one {r : ℝ} {q : ℕ} (hr : 0 ≤ r) (hq : 1 ≤ q) :
  1 ≤ (one_coeff_poly q).eval₂ coe r :=
begin
  cases nat.exists_eq_succ_of_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hq)) with k hqk,
  rw [hqk, polynomial.eval₂, finsupp.sum, one_coeff_poly_support, finset.sum_range_succ', pow_zero, mul_one],
  change 1 ≤ _ + (↑((one_coeff_poly (k+1)).coeff 0) : ℝ),
  rw [one_coeff_poly_coeff_lt (k+1) (nat.succ_pos _)],
  convert (le_add_iff_nonneg_left _).2 _,
  { simp },
  { apply finset.zero_le_sum,
    intros x hx,
    apply mul_nonneg,
    { convert zero_le_one,
      show ((one_coeff_poly (k+1)).coeff (x+1) : ℝ) = 1,
      rw [one_coeff_poly_coeff_lt]; simp,
      simpa using hx },
    { apply pow_nonneg,
      exact hr } }
end

lemma crq_ge_one {r : ℝ} {q : ℕ} (hr : 0 < r) (hr2 : r ≤ 1) (hq : 1 ≤ q) : 1 ≤ crq r q :=
begin
  rw [crq, le_div_iff, one_mul],
  { transitivity (1 : ℝ),
    { apply real.rpow_le_one _ (le_of_lt hr) hr2,
      apply div_nonneg,
      { apply sub_nonneg_of_le,
        suffices : ((1 : ℕ) : ℝ) ≤ q, by simpa using this,
        exact nat.cast_le.2 hq },
        { norm_num } },
    { apply one_coeff_poly_eval_ge_one (le_of_lt hr) hq } },
  { apply real.rpow_pos_of_pos hr }
end

lemma crq_eq (r : ℝ) (q : ℕ) :
  crq r q = (finset.range q).sum (λi:ℕ, r ^ i) / r ^ ((q - 1 : ℝ) / 3) :=
begin
  rw [crq, one_coeff_poly, ← finset.sum_hom (polynomial.eval₂ (coe : ℕ → ℝ) r)],
  congr' 2, funext i,
  rw [polynomial.eval₂_pow, polynomial.eval₂_X]
end

theorem lemma_13_15 {q : ℕ} (hq : 2 ≤ q) : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ crq r q < q :=
begin
  have q_pos : 0 < q := le_trans dec_trivial hq,
  have q_eq : q = (q - 1) + 1 := (nat.sub_add_cancel $ le_trans dec_trivial hq).symm,
  have q_pred : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1,
  { rw [q_eq] { occs := occurrences.pos [2] },
    rw [nat.cast_add, nat.cast_one, add_sub_cancel] },
  have sum_pow_one : (finset.range q).sum (pow 1 : ℕ → ℝ) = (finset.range q).sum (λi, (1 : ℝ)),
  { congr, funext i, rw one_pow },
  let f : ℝ → ℝ := λr, ((finset.range q).sum (λi, r ^ i)) ^ 3 - (q : ℝ)^3 * r^(q-1),
  let f' : ℝ → ℝ := λr,
    3 * (finset.range q).sum (λi, r ^ i) ^ 2 * (finset.range (q - 1)).sum (λi, (i + 1) * r ^ i) -
    (q : ℝ)^3 * (q - 1) * r^(q-2),
  have f1 : f 1 = 0,
  { simp only [f],
    rw [sum_pow_one, finset.sum_const, finset.card_range, add_monoid.smul_one, one_pow,
      mul_one, sub_self] },
  have f'1 : 0 < f' 1,
  { simp only [f'],
    rw [one_pow, sum_pow_one, finset.sum_const, finset.card_range, add_monoid.smul_one, mul_one],
    conv { find (finset.sum _ _) { congr, skip, funext, rw [one_pow, mul_one] } },
    have : ((2:ℕ) : ℝ) ≠ 0, { rw [(≠), nat.cast_eq_zero], exact dec_trivial },
    rw [finset.sum_add_distrib, finset.sum_const, finset.card_range, add_monoid.smul_one,
      add_comm, ← finset.sum_range_succ, ← finset.sum_nat_cast, ← nat.add_one, ← q_eq,
      ← mul_div_cancel (coe (finset.sum _ _ : ℕ) : ℝ) this, ← nat.cast_mul,
      finset.sum_range_id_mul_two, nat.cast_mul, mul_assoc, ← mul_div_assoc, mul_div_comm,
      sub_pos, ← mul_assoc, ← mul_one (_ * _ : ℝ), ← pow_succ', q_pred],
    refine mul_lt_mul_of_pos_left _ _,
    { suffices : ((1 : ℕ) : ℝ) < (3 : ℕ) / (2 : ℕ),
      { simpa },
      rw [lt_div_iff, ← nat.cast_mul, nat.cast_lt],
      exact dec_trivial,
      rw [← nat.cast_zero, nat.cast_lt],
      exact dec_trivial },
    { refine mul_pos (pow_pos (nat.cast_pos.2 q_pos) _) (sub_pos.2 _),
      rw [← nat.cast_one, nat.cast_lt],
      exact hq } },
  have has_deriv_f_f' : ∀r, has_deriv f (f' r) r,
  { assume r,
    refine has_deriv.sub ((has_deriv.pow (has_deriv_finset_sum _ _) 3).congr₂ _) _,
    { exact λi:ℕ, i * r ^ (i - 1) },
    { congr' 1,
      { simp only
          [nat.succ_sub_succ_eq_sub, eq_self_iff_true, nat.cast_bit1, nat.sub_zero, nat.cast_one] },
      { rw [q_eq] { occs := occurrences.pos [1] },
        rw [finset.sum_range_succ'],
        simp only [add_zero, nat.succ_sub_succ_eq_sub, nat.zero_sub, nat.cast_zero, zero_mul,
          add_comm, eq_self_iff_true, (∘), nat.cast_succ, nat.sub_zero, pow_zero, zero_add] } },
    { refine assume n, (has_deriv.pow (has_deriv_id r) n).congr₂ _,
      rw mul_one },
    { rw mul_assoc,
      refine ((has_deriv.pow (has_deriv_id r) _).congr₂ _).mul_left _,
      rw [q_eq] { occs := occurrences.pos [3] },
      rw [nat.cast_add, nat.cast_one, add_sub_cancel, mul_one],
      refl } },
  rcases decreasing_of_fderiv_pos _ _ _ (has_deriv_f_f' 1) f'1 with ⟨ε, hε, h⟩,
  let ε' : ℝ := 1 - (min ε 1) / 2,
  have hε₁ : 1 - ε < ε',
  { refine (sub_lt_sub_iff_left _).2 (lt_of_le_of_lt (div_le_div_of_le_of_pos (min_le_left _ _) _) _);
      linarith },
  have hε₂ : ε' < 1,
  { refine (sub_lt_self _ $ div_pos (lt_min hε _) _);
      norm_num },
  have hε₃ : 0 < ε',
  { refine lt_sub.2 (lt_of_le_of_lt (div_le_div_of_le_of_pos (min_le_right _ _) _) _); norm_num },
  refine ⟨ε', hε₃, hε₂, _⟩,
  specialize h ε' hε₁ hε₂,
  rw f1 at h,
  simp only [f, sub_lt_iff_lt_add, zero_add] at h,
  rw [crq_eq, div_lt_iff],
  refine lt_of_pow_lt_pow 3 _ _,
  { exact zero_le_mul (nat.cast_nonneg _) (real.rpow_nonneg_of_nonneg (le_of_lt hε₃) _) },
  { have : ((3 : ℕ) : ℝ) = 3 := by norm_num,
    rwa [mul_pow, ← real.rpow_nat_cast (ε' ^ _), ← real.rpow_mul (le_of_lt hε₃), this,
      div_mul_cancel, ← q_pred, real.rpow_nat_cast],
    norm_num },
  { exact real.rpow_pos_of_pos hε₃ _ }
end

lemma coeff_ge_one {r : ℝ} (hr : 0 < r) (hr2 : r < 1) {q : ℕ} (hq : q ≥ 1) :
  ((3 * (crq r q)^2)/(1 - r)) ≥ 1 :=
have 1 ≤ crq r q^2, from one_le_pow_of_one_le (crq_ge_one hr (le_of_lt hr2) hq) _,
by apply (le_div_iff _).2; linarith

lemma finset.card_le_card_univ {α} [fintype α] [decidable_eq α] (A : finset α) : A.card ≤ (@finset.univ α _).card :=
finset.card_le_card_of_inj_on id (λ _ _, finset.mem_univ _) $ by simp


section
set_option class.instance_max_depth 200
variables {α : Type} [discrete_field α] [fintype α] {n : ℕ} {a b c : α} (hc : c ≠ 0)
    (habc : a + b + c = 0) {A : finset (fin n → α)}
    (hall : ∀ x y z : fin n → α, x ∈ A → y ∈ A → z ∈ A → a • x + b • y + c • z = 0 → x = y ∧ x = z)
include hc habc hall
local notation `q` := @q α _ _

theorem theorem_13_14 {r : ℝ} (hr : 0 < r) (hr2 : r < 1) : ↑A.card ≤ 3 * (crq r q)^n :=
if hn : n = 0 then
   have hcu : (@finset.univ (fin n → α) _).card = 1,
    by { convert finset.card_univ, rw hn, refl },
  have hac : A.card ≤ 1, by { convert finset.card_le_card_univ _, {exact eq.symm hcu}, {apply_instance}},
  have hac : (A.card : ℝ) ≤ 1, from suffices (A.card : ℝ) ≤ (1 : ℕ), by simpa, nat.cast_le.2 hac,
  le_trans hac (by rw [hn, pow_zero, mul_one]; norm_num)
else have hn : n > 0, from nat.pos_of_ne_zero hn,
begin
  transitivity,
  { apply nat.cast_le.2,
    apply theorem_12_1 n hc habc hn hall },
  { rw nat.cast_mul,
    convert mul_le_mul_of_nonneg_left _ _,
    { norm_cast },
    { rw [mul_comm, ←div_eq_mul_one_div],
      apply theorem_14_1; assumption },
    { norm_num } }
end

end

section
set_option class.instance_max_depth 200

theorem general_cap_set {α : Type} [discrete_field α] [fintype α] :
  ∃ C B : ℝ, B > 0 ∧ C > 0 ∧
  C < fintype.card α ∧ ∀ {a b c : α} {n : ℕ} {A : finset (fin n → α)},
   c ≠ 0 → a + b + c = 0 →
   (∀ x y z : fin n → α, x ∈ A → y ∈ A → z ∈ A → a • x + b • y + c • z = 0 → x = y ∧ x = z) →
    ↑A.card ≤ B * C^n :=
begin
  rcases lemma_13_15 q_ge_two with ⟨B, hB, hB2, hBr⟩,
  repeat {apply exists.intro},
  refine ⟨_, _, hBr, λ a b c n A hc habc hall, theorem_13_14 hc habc hall hB hB2⟩,
  { norm_num },
  { apply lt_of_lt_of_le zero_lt_one,
    exact crq_ge_one hB (le_of_lt hB2) one_le_q }
end
end

lemma one_coeff_poly_real_eval_aux (x : ℝ) :
  (one_coeff_poly 3).eval₂ coe x = (((1 : ℕ) : ℝ) * (1 : ℝ))  + ( (((1 : ℕ) : ℝ) * (x * (1 : ℝ))) + ((((1 : ℕ) : ℝ) * (x * (x * (1 : ℝ)))) + (0 : ℝ) )  ) :=
rfl

lemma one_coeff_poly_real_eval (x : ℝ) : (one_coeff_poly 3).eval₂ coe x = 1 + x + x^2 :=
by convert one_coeff_poly_real_eval_aux x using 1; simp [pow_two]

lemma calc_lemma (r a : ℝ) (hr : r = (a - 1)/8) :
  (3 / 8) ^ 3 * (207 + 33 * (8 * r + 1)) * r ^ 2 - (1 + r + r ^ 2) ^ 3 =
  -(140481/262144) - (70389*a)/131072 + (14553*a^2)/262144 + (1215*a^3)/65536
   - (279*a^4)/262144 - (9*a^5)/131072 - a^6/262144 :=
by rw hr; ring

noncomputable def r : ℝ := (real.sqrt 33 - 1) / 8

lemma r_pos : r > 0 :=
div_pos (sub_pos_of_lt (lt_of_pow_lt_pow _ (real.sqrt_nonneg _)
  (show (1 : ℝ) ^ 2 < (real.sqrt 33)^2, by rw [real.sqr_sqrt, one_pow]; norm_num))) (by norm_num)

lemma r_lt_one : r < 1 :=
begin
  apply (div_lt_iff _).2,
  apply sub_lt_iff_lt_add.2,
  apply @lt_of_pow_lt_pow _ _ _ _ 2 _,
  rw real.sqr_sqrt,
  all_goals {norm_num}
end

lemma r_def : real.sqrt 33 = 8*r + 1 :=
by rw [r, mul_div_cancel', sub_add_cancel]; norm_num

lemma c_r_cubed : (crq r 3)^3 = ((3 : ℝ) / 8)^3 * (207 + 33*real.sqrt 33) :=
begin
  rw [crq, one_coeff_poly_real_eval, div_pow],
  conv {to_lhs, congr, skip, rw [←real.rpow_nat_cast _ 3, ←real.rpow_mul (le_of_lt r_pos)], simp, norm_num},
  symmetry, apply eq_div_of_mul_eq,
  { apply ne_of_gt,
    apply real.rpow_pos_of_pos,
    exact r_pos },
  { rw [r_def],
    apply eq_of_sub_eq_zero,
    have hr2 : r^(2 : ℝ) = r^((2 : ℕ) : ℝ), by simp,
    rw [hr2, real.rpow_nat_cast, calc_lemma r _ rfl],
    change 6 with 2+2+2, change 5 with 2+2+1, change 4 with 2 + 2, change 3 with 2+1,
    simp only [pow_add, pow_one, real.sqr_sqrt (show (0:ℝ) ≤ 33, by norm_num)],
    ring },
  { apply ne_of_gt,
    apply real.rpow_pos_of_pos,
    exact r_pos }
end

lemma c_r_cuberoot : crq r 3 = (((3 : ℝ) / 8)^3 * (207 + 33*real.sqrt 33))^(1/3 : ℝ) :=
have h : _ := congr_arg (λ r : ℝ, r^(1/3:ℝ)) c_r_cubed,
begin
  rw [←real.rpow_nat_cast _ 3, ←real.rpow_mul] at h,
  { simp at h,
    rw [mul_inv_cancel] at h,
    { simpa using h },
    { norm_num } },
  { linarith [crq_ge_one r_pos (le_of_lt r_lt_one) (show 1 ≤ 3, by norm_num)] }
end

section
set_option class.instance_max_depth 200

theorem theorem_13_17 {α : Type} [discrete_field α] [fintype α] {a b c : α}
  (hq : fintype.card α = 3) (hc : c ≠ 0) (habc : a + b + c = 0) :
  ∃ B : ℝ, ∀ {n : ℕ} {A : finset (fin n → α)},
  (∀ x y z : fin n → α, x ∈ A → y ∈ A → z ∈ A → a • x + b • y + c • z = 0 → x = y ∧ x = z) →
  ↑A.card ≤ B * ((((3 : ℝ) / 8)^3 * (207 + 33*real.sqrt 33))^(1/3 : ℝ))^n :=
begin
  apply exists.intro,
  intros n A ha,
  convert theorem_13_14 hc habc ha r_pos r_lt_one,
  rw [q, hq, c_r_cuberoot]
end

end

section
private lemma three_prime : nat.prime 3 := by norm_num
local notation `ℤ/3ℤ` := zmodp 3 three_prime

set_option class.instance_max_depth 100

theorem cap_set_problem : ∃ B : ℝ, ∀ {n : ℕ} {A : finset (fin n → ℤ/3ℤ)},
  (∀ x y z : fin n → ℤ/3ℤ, x ∈ A → y ∈ A → z ∈ A → x + y + z = 0 → x = y ∧ x = z) →
  ↑A.card ≤ B * ((((3 : ℝ) / 8)^3 * (207 + 33*real.sqrt 33))^(1/3 : ℝ))^n :=
begin
  have habc : (1 : ℤ/3ℤ) + 1 + 1 = 0, from rfl,
  have hcard : fintype.card ℤ/3ℤ = 3, from zmodp.card_zmodp three_prime,
  have hone : (1 : ℤ/3ℤ) ≠ 0, from dec_trivial,
  cases theorem_13_17 hcard hone habc with B hB,
  use B,
  intros n A hxyz,
  apply hB,
  simpa using hxyz
end

theorem cap_set_problem_specific (n : ℕ) {A : finset (fin n → ℤ/3ℤ)}
  (hxyz : ∀ x y z : fin n → ℤ/3ℤ, x ∈ A → y ∈ A → z ∈ A → x + y + z = 0 → x = y ∧ x = z) :
  ↑A.card ≤ 3 * ((((3 : ℝ) / 8)^3 * (207 + 33*real.sqrt 33))^(1/3 : ℝ))^n :=
have hone : (1 : ℤ/3ℤ) ≠ 0, from dec_trivial,
have hq : @q (ℤ/3ℤ) _ _ = 3, from zmodp.card_zmodp three_prime,
begin
  transitivity,
  { convert theorem_13_14 hone _ _ r_pos r_lt_one,
    repeat {exact 1},
    { refl },
    { simpa using hxyz } },
  rw hq,
  convert mul_le_mul_of_nonneg_right _ _,
  { symmetry, exact c_r_cuberoot },
  { refl },
  { apply pow_nonneg,
    apply le_trans zero_le_one,
    apply crq_ge_one r_pos (le_of_lt r_lt_one),
    norm_num }
end

end