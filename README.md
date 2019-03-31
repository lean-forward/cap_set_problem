Formalization of "On large subsets of 𝔽<sub>q</sub><sup>n</sup> with no three-term arithmetic progression" by Joardan S. Ellenberg and Dion Gijswijt in Lean

See: [information about the paper and formalization](https://lean-forward.github.io/e-g/).

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
