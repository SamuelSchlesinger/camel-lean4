import Camel.MultiLLM
import Camel.Semantics

/-!
# Scope of the CaMeL mitigation (paper §6, §7)

The end-to-end theorems are strong but have a *precise* boundary.  This module
makes the boundary explicit, formalising the limits where possible and
flagging them where not.

## What is proved to be prevented

1. **Direct prompt injection of the planner.**  The P-LLM never reads
   untrusted tokens, so attacker-controlled tool outputs cannot rewrite the
   plan.  See `Arch.pLLM_not_poisoned`.
2. **Data-flow attacks that route untrusted content into a protected tool.**
   A compliant trace never feeds `adv`-sourced values into a `τ`-call when
   `π.protects τ adv`.  Tag-level: `Arch.e2e_security`.
3. **Attacker influence on the *value* passed to a protected tool.**  Under
   compliance and protection, the argument is adversary-invariant.
   Value-level: `Arch.e2e_noninterference`.
4. **Attacker influence on the world-state observable of protected tools.**
   If unprotected tools are effectless, the final world is
   adversary-invariant.  See `World.run_eq_of_advEquiv`.

## What is **not** prevented

1. **Policy misconfiguration** — if `π.permits τ` admits a capability with
   adversarial sources, protection is vacuously false.  Formal witness:
   `policy_bug_defeats_protection` below.
2. **Side channels via plan control flow.**  Our `Trace` is straight-line:
   every tool call is unconditionally in the plan.  A richer language with
   `branch : Trace → (V → Bool) → Trace → Trace → Trace` would let the
   Q-LLM-produced value determine *which* tool is called.  When the guard
   reads an adversarial value, the choice of tool is itself an observable
   leak — even if the tool's argument is clean.  Our formalism is
   deliberately too weak to express this, so we *cannot* prove the system
   resistant to it.  (The paper acknowledges this as a known limitation.)
3. **Training-time model compromise.**  `pLLM_bounded` is a *wrapper*
   guarantee enforced by the tagging harness, not a property of the weights.
   A weights-level backdoor that changes the plan *shape* (which tools to
   call, with which pure-function post-processors) is not constrained by
   the calculus — only the source tags are.
4. **User error.**  If the user's prompt itself instructs an unsafe action,
   compliance with the policy does not prevent it.  The trusted source is
   trusted by definition.
5. **Non-truthful leaf tagging.**  Our `Trace` conflates the plan structure
   (which the P-LLM chooses) with leaf values (which come from the
   environment).  The theorems are meaningful only under the modelling
   assumption that every `leaf v c` has `c` truthfully describing `v`'s
   origin.  In practice this is the interpreter's responsibility — it
   binds variable references to environment entries whose tags it has
   populated.
-/

namespace Camel
namespace Arch

variable {α V T P S : Type}

/-- **Out-of-scope #1: policy bugs.**  If the policy admits a tool call on a
capability that carries an adversarial source, the `protects` hypothesis
fails outright — the end-to-end theorems have nothing to say.

Witness: given such a permissive policy, `π.protects τ adv` is false. -/
theorem policy_bug_defeats_protection
    (π : Policy T P S) (τ : T) (adv : S → Prop)
    (c : Cap P S) (s : S)
    (hadv : adv s) (hsrc : c.sources s)
    (hpermit : π.permits τ c) :
    ¬ π.protects τ adv :=
  fun hπ => hπ c hpermit s hadv hsrc

/-! ### Out-of-scope #2 — side channels (documentary)

Consider extending `Trace` with

```
branch : Trace V T P S → (V → Bool) → Trace V T P S → Trace V T P S
       → Trace V T P S
```

where `branch g φ t₁ t₂` evaluates `t₁` if `φ (eval g)` and `t₂` otherwise.
If `g` has adversarial sources, the choice between `t₁` and `t₂` — and
hence the observable sequence of tool calls — depends on attacker-controlled
bytes, even when the individual tool arguments along each branch are clean.

Proving or refuting CaMeL in this richer setting is future work; the present
formalisation deliberately scopes it out, matching the paper's treatment.

Deployments must either forbid Q-LLM-dependent branching in the P-LLM's
output language, or provide an independent branching policy that CaMeL's
calculus does not currently model. -/

end Arch
end Camel
