import Camel.Security
import Camel.NonInterference
import Camel.Semantics

/-!
# The CaMeL multi-LLM architecture (paper §4.1)

CaMeL factors the agent into two language models with disjoint responsibilities:

* **P-LLM — "privileged"** — sees only the *user instruction* (trusted).  Its
  output is not free-form text but a small *program* of tool calls — which in
  our formalisation is a `Trace`.
* **Q-LLM — "quarantined"** — called *by* the program to convert untrusted
  tool outputs (emails, web pages, database rows) into structured values.
  The Q-LLM has **no tool access**; its only job is to extract.

## How each LLM appears in the formalism

**The P-LLM** is the `Arch.pLLM` field: a function from a trusted prompt to a
`Trace`.  The only axiom we impose on it is provenance non-forgery
(`pLLM_bounded`), matching the tagging harness's runtime behaviour.

**The Q-LLM** is expressed *structurally* as the `Trace.qParse` constructor.
This is not a bookkeeping choice — it is load-bearing.  Consider what would
go wrong otherwise:

* If Q-LLM invocations were ordinary tool calls (constructor `call`), they
  would be subject to the policy — and no sensible policy would permit a
  parsing tool to consume adversarial input.  The plan would be rejected,
  defeating liveness.
* If Q-LLM invocations were pure `V → V` post-processors baked into `call`,
  they could not appear between tool calls with different provenance
  sources; we would lose the separation between "what was parsed" and
  "what was used".

The `qParse` constructor captures both Q-LLM invariants *as structure*:

* **Policy-exempt.**  `Policy.compliant_qParse` states that wrapping a
  subtrace in `qParse` does not introduce any policy obligation.  The
  Q-LLM can be invoked on any data, clean or adversarial.
* **World-effectless.**  `World.run_qParse` states that `qParse` does
  nothing to the world.  The Q-LLM cannot book a flight, send an email,
  or write a database row — it can only produce a value.

Capability is propagated unchanged: `Trace.cap (qParse sub f) = Trace.cap sub`.
The Q-LLM cannot forge provenance, because the capability tracked at its
output is *exactly* the capability of its input.

See `qLLM_policy_exempt` and `qLLM_world_exempt` below for the Arch-level
restatements.

## Why the split matters

The central insight of the paper — and the thing `pLLM_not_poisoned` below
formalises — is that **prompt injection only threatens the component that
reads untrusted tokens**.  The P-LLM never reads untrusted tokens, so it
cannot be directly prompt-injected.  The Q-LLM may be prompt-injected, but
it cannot call tools (structural: `qParse` is not `call`) and every value
it produces is tagged with the provenance of its inputs (structural: `cap`
propagates) — so the policy can gate any downstream use.

## What the architecture does *not* provide

Security in CaMeL comes from the **interpreter enforcing compliance**, not
from the P-LLM being well-behaved.  Even an adversarial P-LLM cannot defeat
the guarantee, because the interpreter halts any plan that would violate
the policy.  The P-LLM's isolation contributes only to *liveness* (the
agent still accomplishes the user's task under attack), which is a
machine-learning claim, not a theorem.

Accordingly, our end-to-end theorems take compliance as a hypothesis.  We
do *not* try to prove "if the prompt is clean, the plan is compliant" —
that would be a claim about the neural network.
-/

namespace Camel

/-- The CaMeL architecture (paper Fig. 1) in its idealised form.

The only structural invariant we impose is on the P-LLM: it does not forge
provenance — every source appearing in the emitted plan's tracked capability
traces back to the input prompt.  This is what the tagging harness
guarantees; we take it as an axiom about the wrapper, not about the neural
network.

The Q-LLM is visible in the *output type*: plans may contain `qParse` nodes.
Its load-bearing architectural properties (policy-exempt, world-effectless,
cap-preserving) are theorems of the trace semantics, not axioms of `Arch`. -/
structure Arch (α V T P S : Type) where
  /-- The P-LLM: consumes a trusted prompt, emits a plan.  The plan may
  contain `qParse` nodes, which the interpreter will execute by calling
  the Q-LLM at runtime. -/
  pLLM : List (Tagged α P S) → Trace V T P S
  /-- Harness guarantee: the plan's tracked capability cannot reference
  sources that were not already in the prompt.  Informally: the wrapper
  accumulates source tags from input to output; the black-box network cannot
  invent new ones. -/
  pLLM_bounded :
    ∀ prompt s,
      (pLLM prompt).cap.sources s → ∃ t ∈ prompt, t.cap.sources s

namespace Arch

variable {α V T P S : Type}

/-! ## The P-LLM cannot be directly prompt-injected

Prompt injection is, in our model, *adversarial contribution of a source to
an LLM's input*.  If every fragment of the P-LLM's input is clean (no
`adv`-sourced bytes), the P-LLM's output plan cannot carry an `adv` source
either.  This is the one security-relevant property of the architectural
split, and it is immediate from `pLLM_bounded`. -/

theorem pLLM_not_poisoned
    (arch : Arch α V T P S) (adv : S → Prop)
    {prompt : List (Tagged α P S)}
    (hclean : ∀ t ∈ prompt, ¬ poisoned adv t) :
    ∀ s, adv s → ¬ (arch.pLLM prompt).cap.sources s := by
  intro s hads hs
  obtain ⟨t, ht, hts⟩ := arch.pLLM_bounded prompt s hs
  exact hclean t ht ⟨s, hads, hts⟩

/-! ## The Q-LLM's architectural contract — at the Arch level

Each of the following is a direct consequence of the trace semantics; they
are reproduced here so that a reader studying the multi-LLM architecture
has all three Q-LLM guarantees stated as theorems about plans the P-LLM
could emit. -/

/-- **Q-LLM is policy-exempt.**  If the P-LLM places a `qParse` node in the
plan, it adds no policy obligation: the plan is compliant iff its Q-LLM-free
skeleton is. -/
theorem qLLM_policy_exempt
    (_arch : Arch α V T P S) (π : Policy T P S)
    (sub : Trace V T P S) (f : V → V) :
    π.compliant (.qParse sub f) ↔ π.compliant sub :=
  Policy.compliant_qParse π sub f

/-- **Q-LLM is world-effectless.**  A `qParse` node in the plan contributes
nothing to the world trace. -/
theorem qLLM_world_exempt
    (_arch : Arch α V T P S) (world : World V T W)
    (sub : Trace V T P S) (f : V → V) (w : W) :
    World.run world (.qParse sub f) w = World.run world sub w :=
  World.run_qParse world sub f w

/-- **Q-LLM is cap-preserving.**  The Q-LLM cannot widen provenance: the
tracked capability of its output equals the tracked capability of its input. -/
theorem qLLM_cap_preserving
    (_arch : Arch α V T P S)
    (sub : Trace V T P S) (f : V → V) :
    (Trace.qParse sub f : Trace V T P S).cap = sub.cap := rfl

/-! ## End-to-end theorems

Under compliance — enforced by the interpreter, not the planner — the
architecture inherits every theorem from `Camel.Security` and
`Camel.NonInterference`.  We re-export the two most useful instances. -/

/-- **Tag-level end-to-end security.**  A protected tool's argument subtree
has no adversarial sources in its ground-truth source set. -/
theorem e2e_security
    (arch : Arch α V T P S)
    (π : Policy T P S) (τ : T) (adv : S → Prop)
    (hπ : π.protects τ adv)
    {prompt : List (Tagged α P S)}
    (ht : π.compliant (arch.pLLM prompt))
    {sub : Trace V T P S} {f : V → V}
    (hsub : Subtrace (Trace.call τ sub f) (arch.pLLM prompt)) :
    ∀ s, adv s → ¬ sub.trueSources s :=
  Policy.security π τ adv hπ ht hsub

/-- **Value-level end-to-end non-interference.**  The value passed to every
protected tool call is independent of adversary choices at adv-tagged
leaves.  This is the theorem that connects the capability calculus to
observable behaviour; see `Camel.Semantics.World.run_eq_of_advEquiv` for the
world-state lift. -/
theorem e2e_noninterference
    (arch : Arch α V T P S)
    (π : Policy T P S) (τ : T) (adv : S → Prop)
    (hπ : π.protects τ adv)
    {prompt : List (Tagged α P S)}
    (ht : π.compliant (arch.pLLM prompt))
    {sub₁ : Trace V T P S} {f : V → V}
    (hsub : Subtrace (Trace.call τ sub₁ f) (arch.pLLM prompt))
    {sub₂ : Trace V T P S}
    (heq : advEquiv adv sub₁ sub₂) :
    sub₁.eval = sub₂.eval :=
  Policy.noninterference π τ adv hπ ht hsub heq

end Arch
end Camel
