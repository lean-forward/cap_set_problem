/-
Copyright (c) 2018 Sander Dahmen, Johannes Hölzl, Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sander Dahmen, Johannes Hölzl, Robert Y. Lewis

"On large subsets of 𝔽ⁿ_q with no three-term arithmetic progression"
by J. S. Ellenberg and D. Gijswijt

This file contains various support functions, definitions, etc. that will move
to mathlib as we have time.
-/

import data.mv_polynomial data.matrix
import linear_algebra.finsupp linear_algebra.matrix
import topology.instances.real --analysis.exponential
import field_theory.finite field_theory.mv_polynomial

open lattice function

open lattice set linear_map submodule

lemma nat.sub_eq_sub_iff {a b c : ℕ} (h1 : a ≤ c) (h2 : b ≤ c) : c - a = c - b ↔ a = b :=
by rw [nat.sub_eq_iff_eq_add h1, ← nat.sub_add_comm h2, eq_comm,
  nat.sub_eq_iff_eq_add (le_add_right h2), add_left_cancel_iff]

namespace cardinal

noncomputable theory

def to_nat : cardinal → ℕ :=
inv_fun (coe : ℕ → cardinal)

@[simp] lemma to_nat_coe (n : ℕ) : to_nat n = n :=
inv_fun_on_eq' (assume n m _ _, cardinal.nat_cast_inj.1) trivial

lemma to_nat_inv {c : cardinal} (h : ∃ n : ℕ, ↑n = c) : ↑(to_nat c) = c :=
inv_fun_eq h

lemma to_nat_inf {c : cardinal} (h : ¬ ∃ n : ℕ, ↑n = c) : to_nat c = 0 :=
by rw [to_nat, inv_fun_neg h]; refl

lemma to_nat_eq {c : cardinal} {n : ℕ} (h : c = n) : to_nat c = n :=
begin
  rw h,
  apply left_inverse_inv_fun,
  intros _ _,
  simp [cardinal.nat_cast_inj]
end

lemma to_nat_of_finite {c : cardinal} (hc : c < omega) : ↑(to_nat c) = c :=
let ⟨n, hn⟩ := lt_omega.1 hc in
to_nat_inv ⟨n, hn.symm⟩

@[simp] lemma to_nat_zero : to_nat 0 = 0 :=
to_nat_coe 0

@[simp] lemma to_nat_one : to_nat 1 = 1 :=
by rw [← nat.cast_one, to_nat_coe]

lemma to_nat_add {c1 c2 : cardinal} (hc1 : c1 < omega) (hc2 : c2 < omega) :
  to_nat (c1 + c2) = to_nat c1 + to_nat c2 :=
let ⟨_, hn1⟩ := lt_omega.1 hc1,
    ⟨_, hn2⟩ := lt_omega.1 hc2 in
by rw [hn1, hn2, ←nat.cast_add]; simp only [to_nat_coe]

section
local attribute [instance, priority 0] classical.prop_decidable
lemma pos_of_to_nat_pos {c : cardinal} (hc : c.to_nat > 0) : c > 0 :=
have ∃ a : ℕ, ↑a = c, from by_contradiction $ λ h,
  have c.to_nat = 0, from inv_fun_neg h,
  by rw this at hc; exact lt_irrefl _ hc,
begin
  rcases this with ⟨w|w, hw⟩,
  { rw ←hw at hc, exfalso, apply lt_irrefl 0, simpa using hc },
  { rw ←hw, simp, apply lt_of_lt_of_le zero_lt_one, apply le_add_right  }
end
end

lemma to_nat_le_of_le {c1 c2 : cardinal} (hc2 : c2 < omega) (h : c1 ≤ c2) : c1.to_nat ≤ c2.to_nat :=
let ⟨n1, hn1⟩ := lt_omega.1 (lt_of_le_of_lt h hc2),
    ⟨n2, hn2⟩ := lt_omega.1 hc2 in
by simpa [hn1, hn2] using h

lemma to_nat_le {c : cardinal} : ↑c.to_nat ≤ c :=
by classical; exact
if hc : ∃ n : ℕ, ↑n = c then by rw to_nat_inv hc
else by rw to_nat_inf hc; apply cardinal.zero_le

end cardinal

lemma int.to_nat_le_iff (n : ℕ) (i : ℤ) (hi : 0 ≤ i) : n ≤ i.to_nat ↔ (n : ℤ) ≤ i :=
begin
  rcases int.eq_coe_of_zero_le hi with ⟨m, rfl⟩,
  exact (int.coe_nat_le_coe_nat_iff _ _).symm
end

-- MOVE directly after conditionally complete lattice instance for ℕ
instance nat_dec : decidable_linear_order ℕ :=
decidable_linear_ordered_semiring.to_decidable_linear_order ℕ

namespace finset

lemma sum_le_card_mul_of_bdd {α β} [decidable_eq α] [ordered_comm_monoid β] (s : finset α) {f : α → β}
  {a : β} (h : ∀ i, i ∈ s → f i ≤ a) : s.sum f ≤ add_monoid.smul s.card a :=
calc s.sum f ≤ s.sum (λ _, a) : finset.sum_le_sum' h
         ... = add_monoid.smul s.card a : finset.sum_const _

end finset

namespace finsupp

lemma sum_matrix {α β γ₁ γ₂ δ} [semiring δ] [fintype γ₁] [fintype γ₂] [has_zero β] (f : α →₀ β)
  (m : α → β → matrix γ₁ γ₂ δ) (g1 : γ₁) (g2 : γ₂) : f.sum m g1 g2 = f.sum (λ a b, m a b g1 g2) :=
calc f.sum m g1 g2 = f.sum (λ a b, m a b g1) g2 :
   congr_fun (eq.symm $ @finset.sum_hom _ _ _ _ _ _ _ (λ x : matrix γ₁ γ₂ δ, x g1)
      begin convert is_add_monoid_hom.mk _,
        {constructor, intros, refl},
         refl end) g2
               ... = f.sum (λ a b, m a b g1 g2) :
   eq.symm $ @finset.sum_hom _ _ _ _ _ _ _ (λ x : γ₂ → δ, x g2)
      begin convert is_add_monoid_hom.mk _, {constructor, intros, refl}, refl end

lemma sum_matrix_to_lin
  {α β γ₁ γ₂ δ} [comm_ring δ] [fintype γ₁] [fintype γ₂] [has_zero β] (f : α →₀ β)
  (m : α → β → matrix γ₁ γ₂ δ) : (f.sum m).to_lin = f.sum (λ a b, (m a b).to_lin) :=
(@finset.sum_hom _ _ _ _ _ _ _  _ (@matrix.to_lin.is_add_monoid_hom γ₁ γ₂ _ _ δ _)).symm

lemma congr_fun {α β} [has_zero β] {f g : α →₀ β} (h : f = g) : ∀ a : α, f a = g a :=
λ _, by rw h

lemma eq_of_single_eq_left {α β} [decidable_eq α] [decidable_eq β] [has_zero β] {a a' : α}
  {b b' : β} (h : single a b = single a' b') (hb : b ≠ 0) : a = a' :=
(((single_eq_single_iff _ _ _ _).1 h).resolve_right $ mt and.left hb).1

end finsupp

namespace fintype
variables {α : Type*} [fintype α]

lemma card_fin_arrow {n β} [fintype β] : fintype.card (fin n → β) = fintype.card β^n :=
by simp

lemma card_eq_of_bijective {α β} [fintype α] [fintype β] {f : α → β} (hf : function.bijective f) :
  fintype.card α = fintype.card β :=
fintype.card_congr $ equiv.of_bijective hf

lemma subtype_card_true : fintype.card (subtype (λ x : α, true)) = fintype.card α :=
fintype.card_congr (equiv.set.univ α)

lemma subtype_card_sum {P Q : α → Prop} [decidable_pred P] [decidable_pred Q]
  (h : ∀ x, ¬ P x ∨ ¬ Q x) :
  fintype.card (subtype P ⊕ subtype Q) = fintype.card (subtype (λ x, P x ∨ Q x)) :=
fintype.card_congr $ equiv.symm $ equiv.set.union $ set.eq_empty_of_subset_empty $
  assume x ⟨h₁, h₂⟩, (h x).cases_on (assume h, h h₁) (assume h, h h₂)

lemma subtype_disj_card_sum {P : α → Prop} [decidable_pred P] :
  fintype.card (subtype P ⊕ subtype (λ x, ¬ P x)) = fintype.card α :=
fintype.card_congr $ equiv.set.sum_compl {x | P x}

end fintype

def fin.sum {n} {α} [add_comm_monoid α] (f : fin n → α) : α :=
finset.univ.sum f

lemma fin.sum_add {n} {α} [add_comm_monoid α] (f g : fin n → α) :
  fin.sum f + fin.sum g = fin.sum (λ i, f i + g i) :=
eq.symm $ finset.sum_add_distrib

@[simp] lemma fin.sum_const (n : ℕ) {α} [semiring α] (a : α) : fin.sum (λ _ : fin n, a) = n * a :=
by convert finset.sum_const _; simp [finset.card_univ, add_monoid.smul_eq_mul]

section

def finsupp_of_finmap {n} {α} [has_zero α] [decidable_eq α] (f : fin n → α) : fin n →₀ α :=
{ support := finset.univ.filter (λ x, f x ≠ 0),
  to_fun := f,
  mem_support_to_fun := by simp }

@[simp] lemma finsupp_of_finmap_eq {n α} [has_zero α] [decidable_eq α] (f : fin n →₀ α) :
  finsupp_of_finmap (λ x, f x) = f :=
finsupp.ext $ λ x, rfl

instance {n β} [fintype β] [has_zero β] [decidable_eq β] : fintype (fin n →₀ β) :=
{ elems := (fintype.elems (fin n → β)).image finsupp_of_finmap,
  complete := λ f, multiset.mem_erase_dup.2 $ multiset.mem_map.2
    ⟨λ x, f x, ⟨multiset.mem_map.2 ⟨λ a _, f a, by simp⟩, by simp⟩⟩ }

instance {n α} [has_zero α] [decidable_eq α] : has_coe (fin n → α) (fin n →₀ α) :=
⟨finsupp_of_finmap⟩

@[simp] lemma finsupp_of_finmap_to_fun_eq {n α} [has_zero α] [decidable_eq α] (f : fin n → α) (x) :
  (f : fin n →₀ α) x = f x := rfl

@[simp] lemma finset_sum_support {n} {α} [add_comm_monoid α] [decidable_eq α] (f : fin n → α) :
  finset.sum (finsupp.support (f : fin n →₀ α)) (↑f : fin n →₀ α) = finset.sum finset.univ f :=
calc  finset.sum (finsupp.support (f : fin n →₀ α)) (↑f : fin n →₀ α)
    = finset.sum finset.univ (↑f : fin n →₀ α) :
        finset.sum_subset (λ _ _, finset.mem_univ _)
                          (λ x _ hx, by simpa using mt finsupp.mem_support_iff.2 hx)
... = finset.sum finset.univ f : finset.sum_congr rfl (by simp)

lemma fin_sum_finsupp_sum {n} {α} [add_comm_monoid α] [decidable_eq α] (f : fin n → α) :
  fin.sum f = finsupp.sum (f : fin n →₀ α) (λ b a, a) :=
by simp only [fin.sum, finsupp.sum, finset_sum_support]

end

lemma cast_fin_fn {a b} (f : fin a → fin b) (x : fin a) : (↑f : fin a → ℕ) x = (f x).val :=
rfl


section vector_sum

lemma fin.sum_zero {α} [add_comm_monoid α] (f : fin 0 → α) : fin.sum f = 0 :=
finset.sum_eq_zero $ λ x, fin_zero_elim x

lemma fin.sum_succ {α} [add_comm_monoid α] {n : ℕ} (f : fin (n+1) → α) :
  fin.sum f = f ⟨n, nat.lt_succ_self _⟩ + fin.sum (λ k : fin n, f ⟨k, nat.lt_succ_of_lt k.is_lt⟩) :=
have h : @finset.univ (fin (n+1)) _ = finset.univ.image (λ k: fin n, ⟨k.val, nat.lt_succ_of_lt k.is_lt⟩) ∪ finset.singleton ⟨n, nat.lt_succ_self _⟩,
  from eq.symm $ finset.eq_univ_iff_forall.2 $ λ x, if hx : x.val = n
    then finset.mem_union_right _ (finset.mem_singleton.2 (fin.eq_of_veq hx))
    else finset.mem_union_left _ (finset.mem_image.2
      ⟨⟨x.val, nat.lt_of_le_and_ne (nat.le_of_lt_succ x.is_lt) hx⟩,
        finset.mem_univ _, fin.eq_of_veq rfl⟩),
begin
  rw [fin.sum, h, finset.sum_union, add_comm],
  { congr' 1,
    { apply finset.sum_singleton },
    { rw [fin.sum, finset.sum_image], refl,
      intros x _ y _ heq,
      rw fin.ext_iff at ⊢ heq, exact heq } },
  { apply finset.eq_empty_of_forall_not_mem,
    intros x hx,
    rcases finset.mem_image.1 (finset.mem_of_mem_inter_left hx) with ⟨y, _, hy⟩,
    have hxn : x.val = n, from fin.veq_of_eq (finset.mem_singleton.1 (finset.mem_of_mem_inter_right hx)),
    have hxy : y.val = x.val, from fin.veq_of_eq hy,
    linarith [y.is_lt] }
end

lemma vector.vec_one {α} : ∀ v : vector α 1, v = v.head::vector.nil
| ⟨[h],_⟩ := rfl

def vector.sum {α} [add_comm_monoid α] {n} (v : vector α n) : α :=
v.to_list.sum

def vector.nat_sum {n k} (v : vector (fin n) k) : ℕ :=
(v.map fin.val).sum

@[simp] lemma vector.nat_sum_nil (n) : (vector.nil : vector (fin n) 0).nat_sum = 0 :=
by simp [vector.nat_sum, vector.sum]

@[simp] lemma vector.nat_sum_vec_zero {n} (v : vector (fin n) 0) : v.nat_sum = 0 :=
by rw [v.eq_nil, vector.nat_sum_nil]

@[simp] lemma vector.nat_sum_cons {q n} (v : vector (fin q) n) (i : fin q) : (i::v).nat_sum = i.val + v.nat_sum :=
by simp [vector.nat_sum, vector.sum, vector.to_list_cons, vector.map_cons]; refl

lemma vector.nat_sum_head_tail {q n} (v : vector (fin q) (n+1)) : v.nat_sum = v.head.val + v.tail.nat_sum :=
by rw [←vector.cons_head_tail v, vector.nat_sum_cons]; simp

lemma vector.nat_sum_one {q} : ∀ (v : vector (fin q) 1), v.nat_sum < q
| ⟨h::[], _⟩ := by simp [vector.nat_sum, vector.sum, vector.map, h.is_lt]

lemma vector.cons_inj {α} {n} : ∀ {i j} {v w : vector α n} (h : i::v = j::w), v = w
| _ _ ⟨[],_⟩ ⟨[],_⟩ h := by cases subtype.ext.1 h; refl
| _ _ ⟨_::_,_⟩ ⟨_::_,_⟩ h := by cases subtype.ext.1 h; refl

lemma vector.cons_inj_left {α n} : ∀ {i j} {v w : vector α n} (h : i::v = j::w), i = j
| _ _ ⟨[],_⟩ ⟨[],_⟩ h := by cases subtype.ext.1 h; refl
| _ _ ⟨_::_,_⟩ ⟨_::_,_⟩ h := by cases subtype.ext.1 h; refl

end vector_sum
