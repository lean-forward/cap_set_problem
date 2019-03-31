Formalization of "On large subsets of 𝔽<sub>q</sub><sup>n</sup> with no three-term arithmetic progression" by Joardan S. Ellenberg and Dion Gijswijt in Lean

See: [information about the paper and formalization](https://lean-forward.github.io/e-g/).

Theorems
==

```lean
theorem general_cap_set {α : Type} [discrete_field α] [fintype α] :
  ∃ C B : ℝ, B > 0 ∧ C > 0 ∧ C < fintype.card α ∧
    ∀ {a b c : α} {n : ℕ} {A : finset (fin n → α)},
      c ≠ 0 → a + b + c = 0 →
      (∀ x y z : fin n → α, x ∈ A → y ∈ A → z ∈ A → a • x + b • y + c • z = 0 → x = y ∧ x = z) →
      ↑A.card ≤ B * C^n

theorem cap_set_problem : ∃ B : ℝ,
  ∀ {n : ℕ} {A : finset (fin n → ℤ/3ℤ)},
    (∀ x y z : fin n → ℤ/3ℤ, x ∈ A → y ∈ A → z ∈ A → x + y + z = 0 → x = y ∧ x = z) →
    ↑A.card ≤ B * ((((3 : ℝ) / 8)^3 * (207 + 33*real.sqrt 33))^(1/3 : ℝ))^n

theorem cap_set_problem_specific (n : ℕ) {A : finset (fin n → ℤ/3ℤ)}
  (hxyz : ∀ x y z : fin n → ℤ/3ℤ, x ∈ A → y ∈ A → z ∈ A → x + y + z = 0 → x = y ∧ x = z) :
  ↑A.card ≤ 198 * ((((3 : ℝ) / 8)^3 * (207 + 33*real.sqrt 33))^(1/3 : ℝ))^n
```

All three are found in `section_1b.lean`.

Install
==

* Install [elan](https://github.com/Kha/elan) or [Lean 3.4.2](https://github.com/leanprover/lean/releases/tag/v3.4.2)

  (This is usually straight forward, for details see https://github.com/leanprover-community/mathlib/blob/master/docs/elan.md)

* Clone:
  ```
  $ git clone https://github.com/lean-forward/cap_set_problem.git
  ```

* Build:
  ```
  $ cd cap_set_problem
  $ leanpkg build
  ```

  This will build `mathlib` which will take a long time


Inspect
==

Install [Visual Studio Code](https://code.visualstudio.com/) or `emacs` with the Lean extension. This allows to inspect the proof states in tactic proofs. This requires `leanpkg build`, otherwise Lean will try to build `mathlib` interactively, which is very slow and memory consuming.
