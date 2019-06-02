/-
Copyright (c) 2018 Sander Dahmen, Johannes Hölzl, Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sander Dahmen, Johannes Hölzl, Robert Y. Lewis

"On large subsets of 𝔽ⁿ_q with no three-term arithmetic progression"
by J. S. Ellenberg and D. Gijswijt

This file proves a result about the coefficients of a complex polynomial.
It is independent of the rest of our development so far, and used in section_13b.lean.
It corresponds to the first part of section 13 of our blueprint.
-/

import tactic.linarith
import data.polynomial
import analysis.complex.exponential

variables {α : Type*} {β : Type*} {γ : Type*}

namespace units
variables [division_ring α] {a b : α}
end units

variable [discrete_field β]

open finset

def geom_sum0 [semiring α] (x : α) (n : ℕ) : α :=
(range n).sum (λ i, x^i)

lemma geom_sum_one [semiring α] {k : ℕ} : geom_sum0 (1 : α) k = k :=
by simp [geom_sum0,one_pow]

-- Lemma 13.3 from the notes
lemma geom_sum_bound (x: ℝ) (M : ℕ) (h1 : 0 < x) (h2 : x < 1) : geom_sum0 (1/x) (M+1) < (1 - x)⁻¹ * (x^M)⁻¹ :=
have hxn0 : x ≠ 0 := ne_of_gt h1,
have hxn1 : x ≠ 1 := ne_of_lt h2,
let M' := (M : ℤ) in
have h : geom_sum0 (1/x) (M+1) = (1 - x)⁻¹ * (x^M)⁻¹ * (1 - x^(M + 1)), from
  calc geom_sum0 (1/x) (M+1) = (range (M+1)).sum (λ i, (1/x)^i) : by rw [geom_sum0]
  ... = (range (M+1)).sum (λ i, x⁻¹ ^i) : by simp
  ... = (x - 1)⁻¹ * (x - x⁻¹ ^ (M+1) * x) : by rw [geom_sum_inv hxn1 hxn0 (M+1)]
  ... = (x - 1)⁻¹ * (x - x⁻¹ ^ (M'+1) * x) : by refl
  ... = (x - 1)⁻¹ * ((x^M')⁻¹ * (x^(M'+1) - 1)) :
  begin
    congr, rw [mul_sub, fpow_add hxn0, fpow_add, fpow_one, fpow_one, mul_one,
      mul_assoc, inv_mul_cancel hxn0, ← mul_assoc, inv_mul_cancel, one_mul, mul_one,
      ← fpow_inv, ← fpow_inv, ← fpow_mul, ← fpow_mul],
    simp,
    exact fpow_ne_zero_of_ne_zero hxn0 _,
    exact inv_ne_zero hxn0
  end
  ... = (x - 1)⁻¹ * (x^M)⁻¹ * (x^(M+1) - 1) : by rw[mul_assoc]; refl
  ... = (1 - x)⁻¹ * (x^M)⁻¹ * (1 - x^(M + 1)) :
  begin
    rw [← neg_sub, ← neg_sub (1:ℝ)],
    simp only [neg_inv', neg_mul_eq_neg_mul, (neg_mul_comm _ _).symm, neg_neg]
  end,
have hRight : 1 - x^(M+1) < 1, from
  calc 1 - x^(M+1) < 1-0 : sub_lt_sub_left (pow_pos h1 (M+1)) 1
       ... = 1 : by simp,
have hLeft : (1 - x)⁻¹ * (x ^ M)⁻¹ > 0, from
  have hh : 1-x > 0 := by linarith,
  have foo : (1-x)⁻¹ > 0 :=
  calc (1-x)⁻¹ = 1/(1-x) : by rw inv_eq_one_div
       ... > 0 : one_div_pos_of_pos hh,
  have bar : (x^M)⁻¹ > 0 :=
  calc (x^M)⁻¹ = 1/(x^M) : by rw inv_eq_one_div
       ... > 0 : one_div_pos_of_pos (pow_pos h1 M),
  mul_pos foo bar,
calc geom_sum0 (1/x) (M+1) = (1 - x)⁻¹ * (x^M)⁻¹ * (1 - x^(M + 1)) : h
   ... < (1 - x)⁻¹ * (x^M)⁻¹ * 1 : mul_lt_mul_of_pos_left hRight hLeft
   ... = (1 - x)⁻¹ * (x^M)⁻¹ : by rw mul_one

/-- `is_k_uroot x k`: `x` is a `k`-th root of unity -/
def is_k_uroot [semiring α] (x : α) (k : ℕ) : Prop := k > 0 ∧ x^k=1

namespace is_k_uroot

variable [semiring α]

def to_unit {x : α} {k : ℕ} (h : is_k_uroot x k) : units α :=
{ val := x,
  inv := x^(k-1),
  val_inv :=
  calc x * x ^ (k - 1) = x^(1+(k-1)) : by rw[pow_add, pow_one]
    ... = x^k : by rw[nat.add_sub_cancel'] ; exact h.1
    ... = 1 : h.2,
  inv_val :=
  calc x ^ (k - 1) * x = x^(1+(k-1)) : by rw[add_comm,pow_add, pow_one]
    ... = x^k : by rw[nat.add_sub_cancel'] ; exact h.1
    ... = 1 : h.2 }

@[simp] lemma coe_to_unit {x : α} {k : ℕ} (h : is_k_uroot x k) : (h.to_unit : α) = x := rfl

@[simp] lemma to_unit_pow_k {x : α} {k : ℕ} (h : is_k_uroot x k) : h.to_unit ^ k = 1 :=
by ext; rw [units.coe_pow, units.coe_one, coe_to_unit, h.2]

end is_k_uroot

def is_primitive_k_uroot [semiring α] (x : α) (k : ℕ) : Prop :=
is_k_uroot x k ∧ (∀n, is_k_uroot x n → k ≤ n)

section geom_sum_uroot

variables [domain α] [discrete_field β]

lemma geom_sum_uroot {x : α} {k : ℕ} (hx : is_k_uroot x k) (i : ℤ) (h : hx.to_unit ^ i ≠ 1):
  (geom_sum0 (hx.to_unit ^ i : units _) k : α) = 0 :=
let x' : ℤ → units α := λi, hx.to_unit ^ i in
have eq_zero : (geom_sum0 (x' i) k : α) * ((x' i) - 1) = 0, from
  calc (geom_sum0 (x' i) k : α) * ((x' i) - 1) = (x' i)^k - 1 : geom_sum_mul _ _
    ... = (x' (k * i)) - 1 : begin simp only [x'], rw[←units.coe_pow, mul_comm, gpow_mul], refl end
    ... = 0 : by simp only [x', gpow_mul, gpow_coe_nat, hx.to_unit_pow_k, one_gpow, units.coe_one, sub_self],
have ne_zero : ((x' i) - 1 : α) ≠ 0,
  by rwa [(≠), sub_eq_zero, ← units.coe_one, ← units.ext_iff],
begin
  rw mul_eq_zero at eq_zero,
  exact eq_zero.resolve_right ne_zero
end

lemma geom_sum_uroot' {x : α} {k : ℕ} (hx : is_k_uroot x k) (i : ℕ) (h : x^i ≠ 1):
  geom_sum0 (x^i) k = 0 :=
have eq_zero : geom_sum0 (x^i) k  * (x^i - 1) = 0, from
  calc geom_sum0 (x^i) k * (x^i - 1) = (x^i)^k - 1 : geom_sum_mul _ _
    ... = (x^(k * i)) - 1 : by rw[mul_comm, pow_mul]
    ... = 0 : by simp only [pow_mul, one_pow, hx.2, sub_self],
have ne_zero : x^i - 1 ≠ 0,
  by rwa [(≠), sub_eq_zero],
begin
  rw mul_eq_zero at eq_zero,
  exact eq_zero.resolve_right ne_zero
end

lemma geom_sum_uroot'' {x : β} {k : ℕ} (hx : is_k_uroot x k) (i : ℤ) (h : x^i ≠ 1):
  geom_sum0 (x^i) k = 0 :=
have eq_zero : geom_sum0 (x^i) k  * (x^i - 1) = 0, from
   calc geom_sum0 (x^i) k * (x^i - 1) = (x^i)^k - 1 : geom_sum_mul _ _
    ... = (x^(k * i : ℤ)) - 1 : by rw [mul_comm, fpow_mul, fpow_of_nat]
    ... = _ : by rw [fpow_mul, fpow_of_nat, hx.2, one_fpow, sub_self],
have ne_zero : x^i - 1 ≠ 0,
  by rwa [(≠), sub_eq_zero],
begin
  rw mul_eq_zero at eq_zero,
  exact eq_zero.resolve_right ne_zero
end

-- Only necessary for more general framework:
lemma uroot_pow_one {x : β} {k : ℕ} (hx : is_primitive_k_uroot x k)
  (i : ℕ) (h : k ∣ i) :
  x^i=1 :=
match h with ⟨d,hd⟩ := by rw [hd, pow_mul,hx.1.2,one_pow]
end

-- lemma uroot_pow_not_one {x : β} {k : ℕ} (hx : is_primitive_k_uroot x k)
-- (i : nat) (h : ¬ (k ∣ i)) :
--   x^i ≠ 1 := sorry

end geom_sum_uroot

--- Spcial case of Thoerem 13.7, as used in proof of Lemma 13.10
open complex
local notation `π` := real.pi
noncomputable def ζk (k : ℤ) : ℂ := exp (2*π*I/k)

lemma abs_of_uroot (k : ℤ): abs (ζk k) = 1 :=
calc abs (exp (2*π*I/k))
      = abs (exp 0) : by rw abs_exp_eq_iff_re_eq; simp [div_eq_mul_inv]
  ... = 1 : by simp

-- Lemma 13.5 special case(s)

lemma pi_ne_zero : real.pi ≠ 0 :=
  ne_of_gt real.pi_pos

lemma my_exp_nat_mul (z: ℂ) (n : ℕ) : complex.exp z ^ n = complex.exp (z*n) :=
by rw[←exp_nat_mul,mul_comm]

lemma my_exp_int_mul (z: ℂ) : ∀ n : ℤ, complex.exp z ^ n= complex.exp (z*n)
| (int.of_nat n) := my_exp_nat_mul z n
| -[1+n]         :=
calc exp z ^ -[1+ n] = exp z ^ -((n:ℤ) + 1) : rfl
  ... = exp z ^ -(1 * ((n:ℤ)+1)) : by rw [one_mul]
  ... = ((exp z)^(-1:ℤ)) ^ ((n:ℤ)+1) : by rw [neg_mul_eq_neg_mul, fpow_mul]
  ... = ((exp z)^(-1:ℤ)) ^ (n+1) : rfl
  ... = (exp (-z)) ^ (n+1) : by rw [fpow_inv, exp_neg]
  ... = exp (-z*(n+1)) : my_exp_nat_mul _ _
  ... = exp (z*(-(n+1))) : by rw [←neg_mul_eq_neg_mul, neg_mul_eq_mul_neg]
--  ... = exp (z * ↑-[1+ n]) : rfl

lemma exp_2piI_eq : exp (2*π*I)=1 :=
  have h : ∃ (n : ℤ), 1 * (2 * ↑π * I) = ↑n * (2 * ↑π * I) :=
    by existsi (1:ℤ); simp, by rwa [←one_mul (2 * ↑π * I), complex.exp_eq_one_iff]

lemma foo (k : ℕ) : (ζk k)^k=1 :=
if h : k =0 then by rw [h, pow_zero]
else
calc (ζk k)^k = exp ((2*π*I/k)*k) : my_exp_int_mul _ k
     ... = 1 : by rw [div_mul_cancel, exp_2piI_eq]; simp [h]

lemma bar (k n : ℤ) (hknz : k ≠ 0): (ζk k)^n =1 ↔ k∣ n :=
have h : (ζk k)^n=exp ((n/k) * (2 * π * I)) :=
calc (ζk k)^n= _ : my_exp_int_mul _ n
 ... = exp ((n/k) * (2 * π * I)) :
   by simp[div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm],
calc (ζk k)^n =1 ↔ exp ((n/k) * (2 * π * I)) =1 : by rw h
... ↔ (∃ (i : ℤ), (i : ℂ) * k = n) :
  by simp [exp_eq_one_iff, domain.mul_right_inj, I_ne_zero, pi_ne_zero, two_ne_zero',
    div_eq_iff_mul_eq, hknz]
... ↔ k ∣ n :
begin
  refine exists_congr (assume i, _),
  rw [← int.cast_mul, int.cast_inj, mul_comm, eq_comm],
end

lemma geom_sum_uroot_pow_nmid (k : ℕ) (i : ℤ) (hnmid : ¬ (k : ℤ) ∣ i) :
  geom_sum0 ((ζk k)^i) k = 0 :=
if h : k =0 then by simp [geom_sum0, h]
else
have hh : (k:ℤ) ≠ 0 := by simp[h],
have X : ζk ↑k ^ i ≠ 1 := by simp [bar (k:ℤ) i hh, hnmid],
have hpow1 : (ζk ↑k ^ i) ^ k = 1 :=
calc (ζk ↑k ^ i) ^ k = (ζk ↑k ^ i) ^ (k:ℤ)  : rfl
    ... = (ζk ↑k ^ ↑k)^ i : by rw[←fpow_mul,mul_comm,fpow_mul]
    ... = (ζk k ^ k)^ i : by refl
    ... = 1 : by rw [foo, one_fpow],
begin
rw [geom_sum0, geom_sum,hpow1],
simpa,
end

lemma geom_sum_uroot_pow_mid (k : ℕ) (i : ℤ) (hmid: (k : ℤ) ∣ i) :
  geom_sum0 ((ζk k)^i) k = k :=
if h : k =0 then by simp [geom_sum0, h]
else
have hh : (k:ℤ) ≠ 0 := by simp[h],
calc geom_sum0 ((ζk k)^i) k = geom_sum0 1 k : by rw [(bar k i hh).2 hmid]
  ... = k : geom_sum_one

lemma pick_out_div (m i e : ℕ) (h1 : i < m) (h2 : e < m) : e=i ↔ (m:ℤ) ∣ e-i :=
have hm : -(m:ℤ) <e-i := by linarith,
have he : (e:ℤ)-i<m := by linarith,
have hmpos : (m:ℤ) ≥ 0 := by linarith,
begin
split,
intro,
simp*,
rintro ⟨k, hk⟩,
have X : (m:ℤ)=↑m*1 := by rw [mul_one],
rw [X,hk] at he,
rw [X,hk,neg_mul_eq_mul_neg] at hm,
have hk1 : k < 1 :=lt_of_mul_lt_mul_left he hmpos,
have hkneg1 : -1 < k :=lt_of_mul_lt_mul_left hm hmpos,
have hk0 : k=0 := by linarith,
rw [hk0,mul_zero, ←neg_add_eq_sub] at hk,
linarith,
end

open polynomial

lemma zetak_ne_zero (k : ℤ) : ζk k ≠ 0 := exp_ne_zero _

lemma pick_out_coef' (f : polynomial ℂ) (m i : ℕ)
  (h1 : i < m) (h2 : m > nat_degree f) (r : ℂ) (h3 : r ≠ 0):
  (range m).sum (λ j, (eval (r*(ζk m)^j) f)/(r^i * (ζk m)^(i*j)) ) = (coeff f i) * m :=
  let ζ := (ζk m) in
  calc (range m).sum (λ j, (eval (r*ζ^j) f)/(r^i * ζ^(i*j)) )
   = (range m).sum (λ j,(f.support.sum (λ e,(f.to_fun e)*(r*ζ^j)^e))*(r^i * ζ^(i*j))⁻¹) : rfl
  ... = (range m).sum (λ j,f.support.sum (λ e,(f.to_fun e)*(r*ζ^j)^e*(r^i * ζ^(i*j))⁻¹))
        : by congr; funext; rw [sum_mul] --by simp[sum_mul]
  ... = f.support.sum (λ e,(range m).sum (λ j,(f.to_fun e)*(r*ζ^j)^e*(r^i * ζ^(i*j))⁻¹))
        : sum_comm -- rw [sum_comm] also works here, but not simp ...
  ... = f.support.sum (λ e,(range m).sum (λ j,(f.to_fun e)*r^((e:ℤ)-i)*ζ^((j:ℤ)*(e-i)))) :
  begin
    simp [-sub_eq_add_neg, fpow_sub, h3, mul_sub, zetak_ne_zero, mul_fpow, mul_inv', mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, -fpow_of_nat,
      (fpow_of_nat _ _).symm, -fpow_mul, (fpow_mul _ _ _).symm],
  end
  ... = f.support.sum (λ e,(f.to_fun e)*r^((e:ℤ)-i)*(range m).sum (λ j,ζ^((j:ℤ)*(e-i))))
        : by simp only [mul_sum, eq_self_iff_true, sub_eq_add_neg]
  ... = f.support.sum (λ e,(f.to_fun e)*r^((e:ℤ)-i)*(range m).sum (λ j,(ζ^((e:ℤ)-i))^(j:ℤ)))
        : by congr; funext; congr; funext; rw [mul_comm, fpow_mul]
  ... = f.support.sum (λ e,(f.to_fun e)*r^((e:ℤ)-i)*geom_sum0 (ζ^((e:ℤ)-i)) m)
        : rfl
  ... = (f.to_fun i)*r^((i:ℤ)-i)*geom_sum0 (ζ^((i:ℤ)-i)) m :
  begin
    refine sum_eq_single i _ _,
    intros e hes henei,
    have heltdf : e ≤ nat_degree f :=
      have hc : coeff f e ≠ 0 := finsupp.mem_support_iff.1 hes,
      le_nat_degree_of_ne_zero hc,
    have heltm : e < m := begin linarith, end,
    change ¬ e = i at henei,
    have hnmid : ¬ (m:ℤ) ∣ e-i := mt (pick_out_div m i e h1 heltm).2 henei,
    have hsum0 : geom_sum0 (ζ ^ (↑e - ↑i)) m =0 := by rw[geom_sum_uroot_pow_nmid]; exact hnmid,
    rw[hsum0,mul_zero],
    intro h,
    have hfi0 : f.to_fun i = 0 := (finsupp.not_mem_support_iff).1 h,
    rw[hfi0,mul_assoc,zero_mul],
  end
  ... = (coeff f i) * m
      : by rw[sub_eq_zero.2, fpow_zero, fpow_zero, geom_sum_one, coeff]; simp

lemma pick_out_coef (f : polynomial ℂ) (i m : ℕ)
  (h1 : m > i) (h2 : m > nat_degree f) (r : ℝ) (h3 : r > 0) :
  (coeff f i) * m = (range m).sum (λ j,
  (eval (r*(ζk m)^j) f)/(r^i * (ζk m)^(i*j))) :=
eq.symm  $ pick_out_coef' f m i h1 h2 (r:ℂ) $
  by simp only [*, ne_of_gt h3, ne.def, not_false_iff, complex.of_real_eq_zero]
