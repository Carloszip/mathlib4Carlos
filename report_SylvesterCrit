# Formalization of Sylvester’s Criterion in Lean

## Project Description

This project formalizes **Sylvester’s criterion** for real Hermitian (symmetric) matrices in Lean using mathlib.

---

## Main Results

The central result formalized is:

**A Hermitian real matrix is positive definite if and only if all of its leading principal minors have positive determinant.**

The project includes:

- A definition of leading principal minors using `Matrix.submatrix`.
- Proof that positive definiteness passes to leading minors.
- Proof that positive definite matrices have all leading principal minors with positive determinant.
- Proof of the reverse implication: positivity of determinants of leading minors implies positive definiteness.
- A final equivalence theorem combining both implications.

The forward implication follows a standard argument, while the converse direction is proved using eigenvalue properties and the relation between determinant and eigenvalues.

---

## Unfinished Parts and Limitations

The main results are complete, but several parts remain technically rough or could be improved.

- Some proofs manipulating supports, sums, and coercions are complicated and could be refactored into reusable lemmas.
- Several technical steps are correct but inelegant and marked for cleanup in comments.
- Some comments should be cleaned or removed.

There are also limitations in generality:

1. Matrices are indexed by `Fin n` for natural numbers `n`. A more general indexing type could likely be supported.
2. The result is currently implemented only over `ℝ`. Sylvester’s criterion also holds over `ℂ`, but implementing this cleanly in Lean is difficult because determinants of Hermitian matrices are real while Lean’s typeclass requirements complicate expressing positivity conditions.

---

## References and Sources

The following references were used:

- Wikipedia: *Sylvester’s criterion*  
  https://en.wikipedia.org/wiki/Sylvester%27s_criterion  
  Used for the proof of forward implication.

- Lecture notes: Mikhail Lavrov, *Linear Algebra Lecture Notes*, Chapter 1 Lecture 5  
  https://misha.fish/archive/docs/484-spring-2019/ch1lec5.pdf  
  Used as the main reference for backward reasoning.

- mathlib documentation and existing Lean formalizations for matrix, eigenvalue, and determinant results.

---

## Use of AI Tools

We used AI tools as assistants during development, primarily for handling the converse direction.

- The forward implication was implemented entirely without AI assistance.
- For the backward reasoing, we used ChatGPT and Gemini to help organize proof strategies and manage complicated notation and algebraic manipulations.
- Many AI-generated proofs were incorrect or incomplete, so we had to correct and complete them.
- AI assistance mainly saved us time by suggesting proof structures and helping locate relevant lemmas rather than providing finished proofs.

Overall:

- Human work: project structure, definitions, debugging, integration with mathlib, and most proofs.
- AI assistance: organizing complex proof steps and suggesting technical transformations, later corrected and completed manually.

