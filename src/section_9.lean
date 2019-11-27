/-
Copyright (c) 2018 Sander Dahmen, Johannes Hölzl, Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sander Dahmen, Johannes Hölzl, Robert Y. Lewis

"On large subsets of 𝔽ⁿ_q with no three-term arithmetic progression"
by J. S. Ellenberg and D. Gijswijt

This file proves a general result about the dimension of certain subspaces of the space of polynomials.
It corresponds to section 9 of our blueprint.
-/

import library
noncomputable theory
open mv_polynomial

section section_9

parameters {α : Type*} [discrete_field α]

parameters {n : ℕ} (V : subspace α (mv_polynomial (fin n) α)) (A : finset (fin n → α))

def zero_set : set (mv_polynomial (fin n) α) := {p ∈ V.carrier | ∀ a ∈ A, mv_polynomial.eval a p = 0}

def zero_set_subspace : subspace α (mv_polynomial (fin n) α) :=
{ carrier := zero_set,
  zero := ⟨submodule.zero _, by simp⟩,
  add := λ _ _ hx hy, ⟨submodule.add _ hx.1 hy.1, λ _ hp, by simp [hx.2 _ hp, hy.2 _ hp]⟩,
  smul := λ _ _ hp, ⟨submodule.smul _ _ hp.1, λ _ hx, by simp [hp.2 _ hx]⟩ }

def zero_set_subspace_V : subspace α V :=
{ carrier := {p | ∀ a ∈ A, mv_polynomial.eval a p = 0},
  zero := λ _ _, eval_zero,
  add := λ x y hx hy z hz, show eval z (↑x + ↑y) = 0, by simp only [eval_add, hx _ hz, hy _ hz, zero_add],
  smul := λ c x hx z hz, show eval z (c • ↑x) = 0, by simp only [mv_polynomial.smul_eval, hx _ hz, mul_zero] }

set_option class.instance_max_depth 150

def zss_equiv : zero_set_subspace ≃ₗ[α] zero_set_subspace_V :=
{ to_fun := λ p, ⟨⟨p.1, p.2.1⟩, p.2.2⟩,
  add := λ  _ _, rfl,
  smul := λ _ _, rfl,
  inv_fun := λ p, ⟨p.1, ⟨p.1.2, p.2⟩⟩,
  left_inv := λ ⟨_, _⟩, rfl,
  right_inv := λ ⟨⟨_, _⟩, _⟩, rfl }

lemma zss_v_dim_eq_zss_dim : vector_space.dim α zero_set_subspace_V = vector_space.dim α zero_set_subspace :=
zss_equiv.symm.dim_eq

set_option class.instance_max_depth 50

def Atp := {x // x ∈ A}

instance Atp_fin : fintype Atp := by dunfold Atp; apply_instance

lemma Atp_card : fintype.card Atp = A.card := fintype.subtype_card _ $ λ _, iff.refl _

def vfmap (p : V) : (Atp → α) := λ v, mv_polynomial.eval v.1 p

def vflmap : V →ₗ[α] (Atp → α) :=
{ to_fun := λ p, vfmap p,
  add := λ x y, funext $ λ z, mv_polynomial.eval_add,
  smul := λ c x, funext $ λ z, mv_polynomial.smul_eval _ _ _ }

lemma vflmap_ker : vflmap.ker = zero_set_subspace_V :=
begin
  ext,
  rw linear_map.mem_ker,
  split,
  { intros h v hv,
    change v with (⟨v, hv⟩ : Atp).val,
    apply congr_fun h },
  { intros h,
    ext v,
    apply h,
    exact v.2 }
end

lemma dim_α_A : vector_space.dim α (Atp → α) = A.card :=
by rw ←Atp_card; apply dim_fun'

lemma lemma_9_2_pre : (vector_space.dim α zero_set_subspace) + A.card ≥ (vector_space.dim α V) :=
begin
  have hrn, from dim_range_add_dim_ker vflmap,
  rw [vflmap_ker, zss_v_dim_eq_zss_dim] at hrn,
  rw [add_comm, ←hrn],
  apply add_le_add_right',
  rw ←dim_α_A,
  apply dim_submodule_le
end

lemma zero_set_subspace_dim (hv : vector_space.dim α V < cardinal.omega) :
  vector_space.dim α zero_set_subspace < cardinal.omega :=
by rw ←zss_v_dim_eq_zss_dim; exact lt_of_le_of_lt (dim_submodule_le _) hv

theorem lemma_9_2 (zss_finite_dim : vector_space.dim α zero_set_subspace < cardinal.omega) :
  (vector_space.dim α zero_set_subspace).to_nat + A.card ≥ (vector_space.dim α V).to_nat :=
suffices (vector_space.dim α zero_set_subspace + A.card).to_nat ≥ (vector_space.dim α V).to_nat,
  begin
    rw [cardinal.to_nat_add, cardinal.to_nat_coe] at this,
    { exact this },
    { exact zss_finite_dim },
    { apply cardinal.nat_lt_omega }
  end,
cardinal.to_nat_le_of_le
  (cardinal.add_lt_omega zss_finite_dim (cardinal.nat_lt_omega _))
  lemma_9_2_pre

end section_9