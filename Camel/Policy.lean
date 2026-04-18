import Camel.Trace

/-!
# Policies and compliance

A **policy** decides whether a particular tool call is permitted given the
capability of the argument the tool would consume.  In CaMeL the policy is the
security boundary: `send_email` may be called with a recipient of capability
`c` only if the policy agrees.

A trace is **compliant** with a policy if every `call` node appearing anywhere
in the trace satisfies the policy at its argument's tracked capability.
-/

namespace Camel

/-- A policy for tools of type `T` over principals `P` and sources `S`.
`permits τ c` expresses "tool `τ` is allowed to consume a value of capability `c`". -/
structure Policy (T P S : Type) where
  permits : T → Cap P S → Prop

namespace Policy

variable {V T P S : Type}

/-- A trace is *compliant* with `π` iff every tool call inside it is permitted by
`π` at the argument's tracked capability.

Q-LLM (`qParse`) calls carry **no policy clause** — they are architecturally
exempt.  This is what the paper's multi-LLM split buys us: parsing untrusted
text via the Q-LLM is always safe, because the Q-LLM has no world access and
the capability of its output is the capability of its input. -/
def compliant (π : Policy T P S) : Trace V T P S → Prop
  | .leaf _ _           => True
  | .call τ sub _ _     => π.permits τ (Trace.cap sub) ∧ compliant π sub
  | .combine t₁ t₂ _    => compliant π t₁ ∧ compliant π t₂
  | .qParse sub _       => compliant π sub

@[simp] theorem compliant_leaf (π : Policy T P S) (v : V) (c : Cap P S) :
    compliant π (Trace.leaf v c : Trace V T P S) ↔ True := Iff.rfl

@[simp] theorem compliant_call (π : Policy T P S) (τ : T)
    (sub : Trace V T P S) (f : V → V) (outCap : Cap P S) :
    compliant π (Trace.call τ sub f outCap) ↔
      π.permits τ sub.cap ∧ compliant π sub :=
  Iff.rfl

@[simp] theorem compliant_combine (π : Policy T P S)
    (t₁ t₂ : Trace V T P S) (g : V → V → V) :
    compliant π (Trace.combine t₁ t₂ g) ↔ compliant π t₁ ∧ compliant π t₂ :=
  Iff.rfl

/-- **Q-LLM calls are structurally policy-exempt.**  Running a Q-LLM on any
plan is compliant iff the underlying plan is compliant — the Q-LLM itself
adds no constraints. -/
@[simp] theorem compliant_qParse (π : Policy T P S)
    (sub : Trace V T P S) (f : V → V) :
    compliant π (Trace.qParse sub f) ↔ compliant π sub :=
  Iff.rfl

/-- `π.protects τ bad` states: `π` never lets `τ` consume a value whose tracked
capability contains any source in `bad`.

Practical reading: "`τ` is off-limits for anything derived from untrusted
sources." -/
def protects (π : Policy T P S) (τ : T) (bad : S → Prop) : Prop :=
  ∀ c, π.permits τ c → ∀ s, bad s → ¬ c.sources s

end Policy

/-- `Subtrace s t` holds when `s` appears as a subtree of `t`.  Used to state
"every tool-call inside the trace satisfies the policy" without extracting a
list.  -/
inductive Subtrace {V T P S : Type} : Trace V T P S → Trace V T P S → Prop where
  | refl   : {t : Trace V T P S} → Subtrace t t
  | call   : {s sub : Trace V T P S} → {τ : T} → {f : V → V} → {outCap : Cap P S} →
             Subtrace s sub → Subtrace s (Trace.call τ sub f outCap)
  | combL  : {s t₁ t₂ : Trace V T P S} → {g : V → V → V} →
             Subtrace s t₁ → Subtrace s (Trace.combine t₁ t₂ g)
  | combR  : {s t₁ t₂ : Trace V T P S} → {g : V → V → V} →
             Subtrace s t₂ → Subtrace s (Trace.combine t₁ t₂ g)
  | qParse : {s sub : Trace V T P S} → {f : V → V} →
             Subtrace s sub → Subtrace s (Trace.qParse sub f)

namespace Subtrace

variable {V T P S : Type}

theorem trans {a b c : Trace V T P S} (h₁ : Subtrace a b) (h₂ : Subtrace b c) :
    Subtrace a c := by
  revert h₁
  induction h₂ with
  | refl         => exact id
  | call _ ih    => exact fun h => .call (ih h)
  | combL _ ih   => exact fun h => .combL (ih h)
  | combR _ ih   => exact fun h => .combR (ih h)
  | qParse _ ih  => exact fun h => .qParse (ih h)

end Subtrace
end Camel
