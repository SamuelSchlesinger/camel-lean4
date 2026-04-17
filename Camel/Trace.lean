import Camel.Tagged

/-!
# Traces

`Trace V T P S` is an *inductive record* of a CaMeL program's execution — the
data-flow graph the paper describes.  A trace is either

* a **leaf** — an input value carrying a capability that names the actual
  sources/readers that gave rise to it;
* a **call** of a tool `τ : T` on a subcomputation (the tool's *argument*);
* a **combine** that fuses two subcomputations with a binary operation.

Two capability views are definable on a trace:

* `Trace.cap` — the *tracked* capability, computed by the propagation rules
  of `Camel.Tagged` (join on combine, preserve on call).
* `Trace.trueReaders` / `Trace.trueSources` — the *ground-truth* capability
  computed by recursing into all leaves.

The headline theorem `cap_eq_true` states that tracked and ground-truth
capabilities agree pointwise.  This is what makes capability tracking
**sound**: no source or reader is lost.
-/

namespace Camel

/-- A trace of a CaMeL computation.

* `leaf v c` — primitive input `v` tagged with capability `c`.
* `call τ sub f` — invoke tool `τ` on the value produced by `sub`,
  post-processing with pure function `f`.
* `combine t₁ t₂ g` — fuse two subtraces via binary function `g`.
* `qParse sub f` — invoke the **Q-LLM** on `sub`'s value, post-processing
  with pure function `f`.  The Q-LLM is architecturally distinct from a
  regular tool: it has *no world effect* and *no policy gate*.  These
  properties are formalised structurally here (rather than as ad-hoc
  conventions about which `T` values are "parsers"), because they are what
  the paper's multi-LLM architecture actually buys us:
  - policy-exempt: see `Camel.Policy.compliant` — no `permits` clause.
  - world-effectless: see `Camel.Semantics.World.run` — recurses without
    calling `world.effect`.
  Capability propagates from the input (the Q-LLM may not widen sources).
-/
inductive Trace (V T P S : Type) where
  | leaf    : V → Cap P S → Trace V T P S
  | call    : T → Trace V T P S → (V → V) → Trace V T P S
  | combine : Trace V T P S → Trace V T P S → (V → V → V) → Trace V T P S
  | qParse  : Trace V T P S → (V → V) → Trace V T P S

namespace Trace

variable {V T P S : Type}

/-- The concrete value produced by the trace — this is what the underlying
Python interpreter would actually compute. -/
def eval : Trace V T P S → V
  | leaf v _         => v
  | call _ sub f     => f (eval sub)
  | combine t₁ t₂ g  => g (eval t₁) (eval t₂)
  | qParse sub f     => f (eval sub)

/-- The capability carried by the value at the root of the trace, computed via
the propagation rules from `Camel.Tagged`.  Q-LLM calls propagate like `call`:
the Q-LLM cannot widen sources. -/
def cap : Trace V T P S → Cap P S
  | leaf _ c        => c
  | call _ sub _    => cap sub
  | combine t₁ t₂ _ => Cap.join (cap t₁) (cap t₂)
  | qParse sub _    => cap sub

/-- The ground-truth source set: the union of `sources` over every leaf in the
trace.  Independent of any tracking machinery. -/
def trueSources : Trace V T P S → (S → Prop)
  | leaf _ c         => c.sources
  | call _ sub _     => trueSources sub
  | combine t₁ t₂ _  => fun s => trueSources t₁ s ∨ trueSources t₂ s
  | qParse sub _     => trueSources sub

/-- The ground-truth reader set: the intersection of `readers` over every leaf. -/
def trueReaders : Trace V T P S → (P → Prop)
  | leaf _ c         => c.readers
  | call _ sub _     => trueReaders sub
  | combine t₁ t₂ _  => fun p => trueReaders t₁ p ∧ trueReaders t₂ p
  | qParse sub _     => trueReaders sub

/-- **Soundness of capability tracking.**  The tracked capability agrees with
the ground-truth capability, pointwise on readers and on sources.

This is the formal analogue of "the interpreter's data-flow graph faithfully
records where values came from." -/
theorem cap_eq_true (t : Trace V T P S) :
    (∀ p, t.cap.readers p ↔ t.trueReaders p) ∧
    (∀ s, t.cap.sources s ↔ t.trueSources s) := by
  induction t with
  | leaf v c =>
      exact ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  | call τ sub f ih =>
      exact ih
  | qParse sub f ih =>
      exact ih
  | combine t₁ t₂ g ih₁ ih₂ =>
      refine ⟨fun p => ?_, fun s => ?_⟩
      · show (Cap.join t₁.cap t₂.cap).readers p ↔ _
        simp only [Cap.readers_join]
        exact ⟨fun ⟨h₁, h₂⟩ => ⟨(ih₁.1 p).mp h₁, (ih₂.1 p).mp h₂⟩,
               fun ⟨h₁, h₂⟩ => ⟨(ih₁.1 p).mpr h₁, (ih₂.1 p).mpr h₂⟩⟩
      · show (Cap.join t₁.cap t₂.cap).sources s ↔ _
        simp only [Cap.sources_join]
        exact ⟨fun h => h.elim (fun h => Or.inl ((ih₁.2 s).mp h))
                                (fun h => Or.inr ((ih₂.2 s).mp h)),
               fun h => h.elim (fun h => Or.inl ((ih₁.2 s).mpr h))
                                (fun h => Or.inr ((ih₂.2 s).mpr h))⟩

/-- Corollary: if the tracked capability forbids a source, the trace really did
not use that source. -/
theorem no_source_of_cap {t : Trace V T P S} {s : S}
    (h : ¬ t.cap.sources s) : ¬ t.trueSources s :=
  fun hs => h (((cap_eq_true t).2 s).mpr hs)

/-- Corollary: if the tracked capability admits principal `p`, then every leaf
permits `p` to read. -/
theorem reader_of_cap {t : Trace V T P S} {p : P}
    (h : t.cap.readers p) : t.trueReaders p :=
  ((cap_eq_true t).1 p).mp h

end Trace
end Camel
