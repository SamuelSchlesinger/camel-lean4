import Camel.Capability
import Camel.Tagged
import Camel.Trace
import Camel.Policy
import Camel.Security
import Camel.NonInterference
import Camel.Semantics
import Camel.MultiLLM
import Camel.Scope
import Camel.Example
import Camel.EmailExample

/-!
# CaMeL, formalised in Lean 4

An idealised formalisation of the CaMeL system described in

  *Defeating Prompt Injections by Design*
  — Debenedetti, Shumailov, de Witt, Spanakis, Bailey, Cossío, Tramèr
    (Google DeepMind + ETH Zürich, arXiv 2503.18813, 2025).

The goal is *pedagogy with teeth*: a small, honest model where every
theorem says something a paper co-author would stand behind, and every
limitation of the approach appears either as a formal counter-witness or
as a clearly-flagged modelling caveat.

## What this development proves, in plain terms

1. **Capability tracking is sound.**  The tag the interpreter carries
   along each value agrees exactly with the ground truth computed by
   recursing into the data-flow graph.  — `Trace.cap_eq_true`
2. **A compliant trace never routes adversarial data into a protected
   tool** (at the tag level).  — `Policy.security`
3. **A compliant trace never lets an adversary *influence the value*
   passed to a protected tool** (at the value level).  This is the
   non-interference theorem, and it is what connects the type system to
   observable behaviour.  — `Policy.noninterference`
4. **Under the obvious world-model**, the *sequence of world-mutating
   tool effects* at protected tools is also adversary-invariant.
   — `World.run_eq_of_advEquiv`
5. **The P-LLM cannot be directly prompt-injected**: if every input
   fragment is clean, so is the tracked capability of every node in the
   emitted plan.  — `Arch.pLLM_not_poisoned`

## What this development explicitly does **not** prove

1. **Liveness** — that the P-LLM produces a plan that accomplishes the
   user's task.  That is a machine-learning claim about a neural
   network, not a theorem.
2. **Policy correctness** — protection of a tool is only as good as the
   policy's *design*.  A counter-witness is formalised as
   `Arch.policy_bug_defeats_protection`.
3. **Side-channel resistance via control flow** — our `Trace` is
   straight-line.  A Q-LLM-gated branch constructor would leak even when
   arguments are clean; we flag this in `Camel.Scope` but do not model
   it.  This is a genuine scope gap, matching the paper.
4. **Training-time integrity of the neural networks.**  `pLLM_bounded`
   is a *wrapper* guarantee.

## Module map

1. `Camel.Capability`       — the capability lattice `(readers, sources)`.
2. `Camel.Tagged`           — values paired with capabilities and the
                              propagation combinators; the `poisoned`
                              predicate.
3. `Camel.Trace`            — the data-flow graph as an inductive type;
                              `eval`, tracked `cap`, ground-truth
                              `trueSources` / `trueReaders`, and the
                              soundness theorem `cap_eq_true`.
4. `Camel.Policy`           — policies, compliance, protection, the
                              `Subtrace` relation.
5. `Camel.Security`         — the tag-level security theorem and its
                              reader-side dual.
6. `Camel.NonInterference`  — `advFree`, `advEquiv`, and the value-level
                              non-interference theorem `noninterference`.
7. `Camel.Semantics`        — an abstract world model and the
                              outcome-level non-interference theorem
                              `run_eq_of_advEquiv`.
8. `Camel.MultiLLM`         — the `Arch` record and the P-LLM isolation
                              theorem; end-to-end restatements of 5–7.
9. `Camel.Scope`            — the scope boundary, formalised where
                              possible and documented where not.
10. `Camel.Example`         — the travel-agent scenario, instantiating
                              the general theorems on concrete policies.
11. `Camel.EmailExample`    — the paper's motivating §2 scenario
                              ("send Bob the document"), instantiated on a
                              concrete email policy that exercises the
                              Q-LLM `qParse` constructor under attack.

## Reading suggestion for the lab

Start at `Camel.NonInterference.noninterference` — it is the *thesis
statement* of the paper, rendered as a Lean theorem.  Then read
`Camel.Scope` to understand the boundary.  `Camel.Example` provides a
concrete smell test.
-/
