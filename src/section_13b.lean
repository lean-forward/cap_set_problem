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
import analysis.exponential
import tactic.library_search
import
  section_10_11_12
  section_13a
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
  constructor,
  { apply polynomial.coeff_zero },
  { intros, apply polynomial.coeff_add }
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

def root_index (q n j : ℕ) : ℕ := max ((q-1)*n) j + 1

lemma root_index_gt_j (q n j) : root_index q n j > j :=
nat.lt_succ_of_le $ le_max_right _ _

lemma root_index_gt_qn (q n j) : root_index q n j > (q-1)*n :=
nat.lt_succ_of_le $ le_max_left _ _

lemma root_index_pos (q n j) : 0 < root_index q n j :=
nat.succ_pos _

lemma root_index_ne_zero (q n j) : root_index q n j ≠ 0 := ne_of_gt $ nat.succ_pos _

lemma one_div_root_index_nonneg (q n j) : 0 ≤ 1 / (root_index q n j : ℝ) :=
div_nonneg zero_le_one $ by simpa using root_index_pos q n j

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

lemma finset.sup_range (n : ℕ) : @finset.sup (with_bot ℕ) _ _ (finset.range (n+1)) some = some n :=
le_antisymm
  (finset.sup_le $ λ b hb, by simp at hb ⊢; apply nat.le_of_lt_succ hb)
  (finset.le_sup $ by simp [zero_lt_one])

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

lemma one_coeff_poly_coe_pow_nat_degree {q : ℕ} (n : ℕ) (hq : q > 0) :
  ((one_coeff_poly q).map (coe : ℕ → ℂ)^n).nat_degree = (q-1)*n :=
begin
  rw [←polynomial.map_pow, polynomial.nat_degree_map', one_coeff_poly_pow_nat_degree],
  { exact hq },
  { apply nat.cast_injective }
end

noncomputable def root (q n j : ℕ) : ℂ := ζk ↑(root_index q n j)

lemma norm_root (q n j : ℕ) : ∥root q n j∥ = 1 :=
abs_of_uroot _

section
variables {α : Type} [discrete_field α] [fintype α] (n : ℕ)
local notation `m` := m α n
local notation `q` := @q α _ _

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

section
variable (j : ℕ)

lemma cf_rw_one {r : ℝ} (hr : r > 0) : (cf q n j : ℂ) =
  (1/root_index q n j) * (finset.range (root_index q n j)).sum
    (λ i, (((one_coeff_poly q)^n).eval₂ coe (r*(root q n j)^i)) / ((r^j * (root q n j)^(j*i)))) :=
have hrnc : (root_index q n j : ℂ) ≠ 0, by simpa using root_index_ne_zero q n j,
have ish : is_semiring_hom (coe : ℕ → ℂ), by constructor; simp,
begin
  rw [←lemma_13_9, ←polynomial.coeff_map coe, mul_comm],
  apply eq_of_mul_eq_mul_right hrnc,
  { rw [mul_assoc, one_div_mul_cancel hrnc, mul_one],
    transitivity,
    apply pick_out_coef,
    { apply root_index_gt_j },
    { rw [polynomial.map_pow coe, one_coeff_poly_coe_pow_nat_degree],
      { apply root_index_gt_qn },
      { exact q_pos },
      { exact ish } },
    { exact hr },
    { congr, ext i,
      dsimp only [polynomial.eval],
      rw [polynomial.eval₂_map coe],
      refl,
      exact ish } },
  { exact ish },
  linarith using [@one_le_q α _ _]
end

lemma cf_rw_two {r : ℝ} (hr : r > 0) (i : ℕ) :
  ∥((((one_coeff_poly q)^n).eval₂ coe (r*(root q n j)^i)) / ((r^j * (root q n j)^(j*i))) : ℂ)∥
      ≤  (((one_coeff_poly q)^n).eval₂ coe r) / r^j :=
have ish : is_semiring_hom (coe : ℕ → ℂ), by constructor; simp,
begin
  rw [norm_div, norm_mul, norm_pow, complex.norm_real, real.norm_eq_abs, abs_of_pos hr,
      norm_pow, norm_root, one_pow, mul_one],
  apply div_le_div_of_le_of_pos,
  { dsimp only [polynomial.eval₂, finsupp.sum],
    convert norm_triangle_sum _ _,
    ext x,
    rw [norm_mul, norm_pow, norm_mul, complex.norm_real, real.norm_eq_abs,
        abs_of_pos hr, norm_pow, norm_root, one_pow, mul_one, complex.norm_nat] },
  { apply pow_pos hr }
end

theorem lemma_13_10 {r : ℝ} (hr : r > 0) :
  ↑(cf q n j) ≤ (((one_coeff_poly q)^n).eval₂ coe r) / r^j :=
calc (cf q n j : ℝ)
      = abs (cf q n j : ℝ) : by rw abs_of_nonneg; apply nat.cast_nonneg
  ... = complex.abs (cf q n j : ℝ) : by rw complex.abs_of_real
  ... = complex.abs (cf q n j) : by simp
  ... = complex.abs ((1/root_index q n j) * (finset.range (root_index q n j)).sum
    (λ i, (((one_coeff_poly q)^n).eval₂ coe (r*(root q n j)^i)) / ((r^j * (root q n j)^(j*i))))) :
      by rw cf_rw_one _ _ hr
  ... = (1/↑(root_index q n j)) * complex.abs ((finset.range (root_index q n j)).sum
    (λ i, (((one_coeff_poly q)^n).eval₂ coe (r*(root q n j)^i)) / ((r^j * (root q n j)^(j*i))))) :
      by rw [complex.abs_mul, complex.abs_div, complex.abs_one, complex.abs_of_nat]
  ... = (1/↑(root_index q n j)) * ∥((finset.range (root_index q n j)).sum
    (λ i, (((one_coeff_poly q)^n).eval₂ coe (r*(root q n j)^i)) / ((r^j * (root q n j)^(j*i)))) : ℂ)∥ : rfl
  ... ≤ (1/↑(root_index q n j)) * (finset.range (root_index q n j)).sum
    (λ i, ∥((((one_coeff_poly q)^n).eval₂ coe (r*(root q n j)^i)) / ((r^j * (root q n j)^(j*i))) : ℂ)∥) :
      mul_le_mul_of_nonneg_left (norm_triangle_sum _ _) (one_div_root_index_nonneg _ _ _)
  ... ≤ (1/↑(root_index q n j)) * (finset.range (root_index q n j)).sum
    (λ i, ((((one_coeff_poly q)^n).eval₂ coe r) / r^j)) :
     mul_le_mul_of_nonneg_left (finset.sum_le_sum (λ i _, cf_rw_two _ _ hr i)) (one_div_root_index_nonneg _ _ _)
  ... = (1/↑(root_index q n j)) * root_index q n j * ((((one_coeff_poly q)^n).eval₂ coe r) / r^j) :
      by rw [finset.sum_const, add_monoid.smul_eq_mul, finset.card_range, mul_assoc]
  ... = (((one_coeff_poly q)^n).eval₂ coe r) / r^j :
      by rw [one_div_mul_cancel, one_mul]; simpa using root_index_ne_zero q n j

end

end

section
variables {α : Type} [discrete_field α] [fintype α] (N : ℕ)
local notation `m` := m α (3*N)
local notation `q` := @q α _ _

-- this could be revisited and cleaned up, possibly split into smaller lemmas
-- note: actually could be a strict <
theorem lemma_13_11 {r : ℝ} (hr : 0 < r) (hr2 : r < 1) :
  ↑(m ((q-1)*N)) ≤ (1/(1-r)) * ((crq r q))^(3*N) :=
have hq : ((q : ℚ) - 1)*N ≥ 0, from mul_nonneg (sub_nonneg_of_le one_le_q_real) (nat.cast_nonneg _),
calc
  ↑(m ((q-1)*N))
     = ↑((finset.range (⌊((q : ℚ)-1)*N⌋.nat_abs + 1)).sum (cf q (3*N))) : by rw lemma_13_8 _ hq
 ... = (↑((finset.range ((q-1)*N + 1)).sum (cf q (3*N))) : ℝ) :
          begin
            congr,
            have : ((q : ℚ) - 1) * N = (((q - 1)*N : ℕ) : ℤ), by simp [nat.cast_sub one_le_q],
            rw [this, floor_coe, int.nat_abs_of_nat]
          end
 ... = (finset.range ((q-1)*N + 1)).sum (λ j, (cf q (3*N) j : ℝ)) : by rw finset.sum_hom (coe : ℕ → ℝ)
 ... ≤ (finset.range ((q-1)*N + 1)).sum (λ j, ((one_coeff_poly q).eval₂ coe r)^(3*N) / r^j) :
         finset.sum_le_sum $ λ _ _, by convert lemma_13_10 _ _ hr; rw polynomial.eval₂_pow
 ... = (finset.range ((q-1)*N + 1)).sum (λ j, ((one_coeff_poly q).eval₂ coe r)^(3*N) * (1/r^j)) :
         by congr; ext; rw div_eq_mul_one_div
 ... = ((one_coeff_poly q).eval₂ coe r)^(3*N) * (finset.range ((q-1)*N + 1)).sum (λ j, (1/r)^j) :
         by rw [←finset.mul_sum]; conv {to_rhs, congr, skip, congr, skip, funext, rw one_div_pow (ne_of_gt hr)}
 ... ≤ ((one_coeff_poly q).eval₂ coe r)^(3*N) * ((1/(1 - r)) * (1 / (r^((q-1)*N)))) :
          begin
            apply mul_le_mul_of_nonneg_left,
            { apply le_of_lt,
              simp only [one_div_eq_inv],
              convert geom_sum_bound _ _ _ _,
              { apply inv_eq_one_div },
              repeat { assumption } },
            { apply pow_nonneg,
              convert one_coeff_poly_eval₂_nonneg _ _ (le_of_lt hr),
              intro,
              apply nat.cast_nonneg }
          end
 ... = (1/(1 - r)) * (((one_coeff_poly q).eval₂ coe r)^(3*N) * ((1 / (r^((q-1)*N))))) :
         by have : ∀ a b c : ℝ, a * (b * c) = b * (a * c) := (λ _ _ _, by ac_refl); apply this
 ... = (1/(1-r)) * ((crq r q))^(3*N) :
          begin
            rw [crq, div_pow, ←div_eq_mul_one_div],
            congr' 2,
            rw [←real.rpow_nat_cast, ←real.rpow_nat_cast, ←real.rpow_mul],
            congr' 1,
            simp,
            rw [←mul_assoc, div_mul_cancel, nat.cast_sub, nat.cast_one],
            simp,
            { apply one_le_q },
            { norm_num },
            { exact le_of_lt hr },
            { apply ne_of_gt,
              exact real.rpow_pos_of_pos hr _ }
          end
end

section

def poly_cast {α : Type*} [comm_semiring α] [decidable_eq α] {n n' : ℕ} (h : n ≤ n')
  (p : mv_polynomial (fin n) α) :  mv_polynomial (fin n') α :=
p.rename (fin.cast_le h)

variables {α : Type} [discrete_field α] [fintype α] {n n' : ℕ} (h : n ≤ n')

lemma poly_cast_mem_M {p : mv_polynomial (fin n) α} (hM : p ∈ @M α _ _ n) :
  poly_cast h p ∈ @M α _ _ n' :=
begin
  simp [M, poly_cast] at hM ⊢,
  rcases hM with ⟨a', ⟨a, ha, rfl⟩, rfl⟩,
  simp only [mv_polynomial.rename_monomial],
  refine ⟨_, ⟨a.emb_domain ⟨_, fin.injective_cast_le h⟩, finset.mem_univ _, _⟩, rfl⟩,
  rw [← finsupp.emb_domain_map_range, finsupp.emb_domain_eq_map_domain],
  refl
end

lemma poly_cast_mem_M' {p : mv_polynomial (fin n) α} {d} (hM : p ∈ @M' α _ _ n d) :
  poly_cast h p ∈ @M' α _ _ n' d :=
begin
  simp only [M', finset.mem_filter, poly_cast] at hM ⊢,
  refine ⟨poly_cast_mem_M h hM.1,
    le_trans (nat.cast_le.2 $ mv_polynomial.total_degree_rename_le _ _) hM.2⟩
end

lemma poly_cast_inj {p1 p2 : mv_polynomial (fin n) α} (hp : poly_cast h p1 = poly_cast h p2) :
  p1 = p2 :=
mv_polynomial.injective_rename _ (fin.injective_cast_le h) hp

end

lemma m_monotone_in_n {α : Type} [discrete_field α] [fintype α] {n n' : ℕ} (d : ℚ) (h : n ≤ n') :
  m α n d ≤ m α n' d :=
begin
  rw [←M'_card, ←M'_card],
  apply finset.card_le_card_of_inj_on (poly_cast h),
  { intros _ H, apply poly_cast_mem_M' h H },
  { intros _ _ _ _ he, apply poly_cast_inj h he },
  { apply_instance },
  { apply_instance }
end

lemma m_monotone_in_d {α : Type} [discrete_field α] [fintype α] (n : ℕ) {d d' : ℚ} (h : d ≤ d') :
  m α n d ≤ m α n d' :=
begin
  rw [←M'_card, ←M'_card],
  apply finset.card_le_of_subset,
  intros a ha,
  simp [M'] at ha ⊢,
  exact ⟨ha.1, le_trans ha.2 h⟩
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

section
variables (α : Type) [discrete_field α] [fintype α] (n : ℕ)
local notation `m` := m α
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

variable {α}

lemma exists_div_three (k : ℕ) : ∃ i, i < 3 ∧ 3 ∣ k + i :=
begin
  use if k % 3 = 0 then 0 else 3 - (k%3),
  split,
  { split_ifs,
    { exact dec_trivial },
    { apply nat.sub_lt,
      exact dec_trivial,
      exact nat.pos_of_ne_zero h } },
  { split_ifs,
    { apply nat.dvd_of_mod_eq_zero, simpa },
    { rw ←nat.mod_add_div k 3, simp,
      rw [add_comm, add_assoc, nat.sub_add_cancel],
      { apply dvd_add,
        { apply dvd_mul_right },
        { exact dec_trivial } },
      { apply le_of_lt, apply nat.mod_lt, exact dec_trivial } } }
end

theorem theorem_13_13 {r : ℝ} (hr : 0 < r) (hr2 : r < 1) :
  ↑(m n ((q - 1)*n / 3)) ≤ ((crq r q)^2 / (1 - r)) * (crq r q)^n :=
let ⟨i, hi, ⟨N', hN'⟩⟩ := exists_div_three n,
    n' := n + i in
have hdc : ((3*N' : ℕ) : ℚ)/3 = N',
  by rw [nat.cast_mul, mul_comm, mul_div_assoc]; simp [div_self (show (3 : ℚ) ≠ 0, by norm_num)],
have hnn' : n ≤ n', from nat.le_add_right _ _,
calc ↑(m n ((q - 1)*n / 3))
     ≤ ↑(m n ((q - 1)*n' / 3)) : nat.cast_le.2 $ m_monotone_in_d _ $ div_le_div_of_le_of_pos
        (mul_le_mul_of_nonneg_left (nat.cast_le.2 hnn')
          (sub_nonneg_of_le (show ((1 : ℕ) : ℚ) ≤ q, from nat.cast_le.2 one_le_q )))
        (by norm_num)
 ... ≤ ↑(m n' ((q-1)*n' / 3)) : nat.cast_le.2 $ m_monotone_in_n _ (nat.le_add_right _ _)
 ... ≤ 1/(1-r) * (crq r q)^n' :
   by change n' with n+i; rw [hN', mul_div_assoc, hdc]; exact lemma_13_11 _ hr hr2
 ... ≤ 1/(1-r) * (crq r q)^(n+2) :
    mul_le_mul_of_nonneg_left (pow_le_pow (crq_ge_one hr (le_of_lt hr2) one_le_q)
      (nat.le_of_lt_succ (nat.add_le_add_left hi _))) (div_nonneg zero_le_one (by linarith))
 ... = 1/(1-r) * ((crq r q)^2 * (crq r q)^n) : by rw [←pow_add, add_comm]
 ... = ((crq r q)^2 / (1 - r)) * (crq r q)^n : by rw [←mul_assoc, mul_comm (1/(1-r)), ←mul_div_assoc, mul_one]

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


theorem theorem_13_14 {r : ℝ} (hr : 0 < r) (hr2 : r < 1) :
  ↑A.card ≤ ((3 * (crq r q)^2)/(1 - r)) * (crq r q)^n :=
if hn : n = 0 then
  have hcu : (@finset.univ (fin n → α) _).card = 1,
    by { convert finset.card_univ, rw hn, refl },
  have hac : A.card ≤ 1, by { convert finset.card_le_card_univ _, {exact eq.symm hcu}, {apply_instance}},
  have hac : (A.card : ℝ) ≤ 1, from suffices (A.card : ℝ) ≤ (1 : ℕ), by simpa, nat.cast_le.2 hac,
  le_trans hac (by rw [hn, pow_zero, mul_one]; exact coeff_ge_one hr hr2 one_le_q)
else have hn : n > 0, from nat.pos_of_ne_zero hn,
begin
  transitivity,
  { apply nat.cast_le.2,
    apply theorem_12_1 n hc habc hn hall },
  { rw [nat.cast_mul, mul_div_assoc, mul_assoc],
    convert mul_le_mul_of_nonneg_left _ _,
    { simp },
    { rw [mul_comm, ←div_eq_mul_one_div],
      apply theorem_13_13; assumption },
    { simp, norm_num } }
end

end

section
variables {α : Type} [discrete_field α] [fintype α]
set_option class.instance_max_depth 200
local notation `q` := @q α _ _

theorem theorem_13_16 : ∃ C B : ℝ, B > 0 ∧ C > 0 ∧
  C < q ∧ ∀ {a b c : α} {n : ℕ} {A : finset (fin n → α)},
   c ≠ 0 → a + b + c = 0 →
   (∀ x y z : fin n → α, x ∈ A → y ∈ A → z ∈ A → a • x + b • y + c • z = 0 → x = y ∧ x = z) →
    ↑A.card ≤ B * C^n :=
begin
  rcases lemma_13_15 (q_ge_two α) with ⟨B, hB, hB2, hBr⟩,
  repeat {apply exists.intro},
  refine ⟨_, _, hBr, λ a b c n A hc habc hall, theorem_13_14 hc habc hall hB hB2⟩,
  { apply div_pos,
    { apply mul_pos,
      { norm_num },
      { apply pow_pos,
        apply lt_of_lt_of_le zero_lt_one,
        exact crq_ge_one hB (le_of_lt hB2) one_le_q } },
    { exact sub_pos_of_lt hB2 } },
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
  { linarith using [crq_ge_one r_pos (le_of_lt r_lt_one) (show 1 ≤ 3, by norm_num)] }
end

lemma c_r_q_pos : crq r 3 > 0 :=
lt_of_lt_of_le zero_lt_one $ crq_ge_one r_pos (le_of_lt r_lt_one) (by norm_num)

lemma sqrt_33_lt_6 : real.sqrt 33 < 6 :=
have real.sqrt 36 = 6, by rw real.sqrt_eq_iff_sqr_eq; norm_num,
by rw [←this, real.sqrt_lt]; norm_num

lemma c_r_cubed_bound : (crq r 3)^3 ≤ 22 :=
begin
  have : (207 + 33*real.sqrt 33) ≤ 405, { linarith using [sqrt_33_lt_6] },
  suffices : crq r 3^3 ≤ (3/8)^3 * 405, { apply le_trans this; norm_num },
  rw c_r_cubed,
  apply mul_le_mul (le_refl _),
  { exact this },
  { refine add_nonneg _ (mul_nonneg _ _); try {norm_num},
    apply real.sqrt_nonneg },
  { norm_num }
end

lemma one_minus_r_bound : 1 - r > 1/3 :=
by rw r; linarith using [sqrt_33_lt_6]

lemma r_bound : (3 * crq r 3 ^ 2) / (1 - r) ≤ 198 :=
have h : (3 * crq r 3 ^ 2) ≤ 66, from calc
  3 * crq r 3^2 ≤ 3 * crq r 3^3 : (mul_le_mul_left (by norm_num)).2
      (pow_le_pow (crq_ge_one r_pos (le_of_lt r_lt_one) (by norm_num)) (by norm_num))
            ... ≤ 3 * 22 : (mul_le_mul_left (by norm_num)).2 c_r_cubed_bound
            ... = 66 : by norm_num,
calc
  (3 * crq r 3 ^ 2) / (1 - r) ≤ (3 * crq r 3 ^ 2) / (1/3) : le_of_lt (div_lt_div_of_pos_of_lt_of_pos
    (by norm_num)
    one_minus_r_bound
    (mul_pos (by norm_num) (pow_pos c_r_q_pos _)))
  ... ≤ 66 / (1/3) :
    div_le_div_of_le_of_pos h (by norm_num)
  ... = 198 : by norm_num

section
set_option class.instance_max_depth 200
variables [α : Type] [discrete_field α] [fintype α] (hq : @q α _ _ = 3) {a b c : α} (hc : c ≠ 0)
    (habc : a + b + c = 0)
include hq hc habc

theorem theorem_13_17 : ∃ B : ℝ, ∀ {n : ℕ} {A : finset (fin n → α)},
  (∀ x y z : fin n → α, x ∈ A → y ∈ A → z ∈ A → a • x + b • y + c • z = 0 → x = y ∧ x = z) →
  ↑A.card ≤ B * ((((3 : ℝ) / 8)^3 * (207 + 33*real.sqrt 33))^(1/3 : ℝ))^n :=
begin
  apply exists.intro,
  intros n A ha,
  convert theorem_13_14 hc habc ha r_pos r_lt_one,
  rw [hq, c_r_cuberoot]
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
  cases @theorem_13_17 (ℤ/3ℤ) _ _ hcard _ _ _ hone habc with B hB,
  use B,
  intros n A hxyz,
  apply hB,
  simpa using hxyz
end

theorem cap_set_problem_specific (n : ℕ) {A : finset (fin n → ℤ/3ℤ)}
  (hxyz : ∀ x y z : fin n → ℤ/3ℤ, x ∈ A → y ∈ A → z ∈ A → x + y + z = 0 → x = y ∧ x = z) :
  ↑A.card ≤ 198 * ((((3 : ℝ) / 8)^3 * (207 + 33*real.sqrt 33))^(1/3 : ℝ))^n :=
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
  { exact r_bound },
  { apply pow_nonneg,
    apply le_trans zero_le_one, -- c_r_q_pos
    apply crq_ge_one r_pos (le_of_lt r_lt_one),
    norm_num }
end

end