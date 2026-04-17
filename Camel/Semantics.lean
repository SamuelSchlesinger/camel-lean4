import Camel.NonInterference

/-!
# Tool effects on a world, and outcome-level non-interference

The `Trace.eval` function computes the *return value* of a plan.  In the real
CaMeL system, the point of a tool call is not to compute a value — it is to
**change the world** (send an email, book a flight, write a row to a database).

This module adds a minimal abstract world and proves outcome-level
non-interference: the **sequence of effects** of a compliant plan at every
protected tool call is identical across adv-equivalent executions.

That is the statement that connects `Camel.Security.security` to user-visible
harm.  If the sequence of `book_flight(arg)` calls — and the value of `arg` at
each — is adversary-independent, then *whatever* `book_flight` does to the
world is adversary-independent.
-/

namespace Camel

/-- The effect of tools on an abstract world.  We ignore return values: the
pure function at each `call` in a trace models the portion of the tool output
that re-enters the data flow, and the `effect` here models the portion that
goes to the world. -/
structure World (V T W : Type) where
  /-- `effect τ arg w` is the world after calling tool `τ` with argument `arg`
  starting from world `w`. -/
  effect : T → V → W → W

namespace World

variable {V T W P S : Type}

/-- A running trace's effect on the world: a left-to-right fold over tool
calls, using `eval` to compute each tool's argument.

* `leaf` — no effect.
* `call τ sub f` — first run the subtree's effects, then apply `τ`'s effect
  with the value `eval sub`.  The pure post-processor `f` does not touch the
  world.
* `combine` — fuse the effects of both subtrees.
* `qParse` — **no world effect.**  The Q-LLM's only output is the parsed
  value (consumed via `Trace.eval`); it cannot reach into the world.  This
  is structural, not a deployment discipline. -/
def run (world : World V T W) : Trace V T P S → W → W
  | .leaf _ _,        w => w
  | .call τ sub _,    w =>
      world.effect τ sub.eval (run world sub w)
  | .combine t₁ t₂ _, w =>
      run world t₂ (run world t₁ w)
  | .qParse sub _,    w => run world sub w

/-- **Q-LLM calls are world-effectless.**  Wrapping a subtrace in `qParse`
changes nothing about the final world. -/
@[simp] theorem run_qParse (world : World V T W)
    (sub : Trace V T P S) (f : V → V) (w : W) :
    run world (.qParse sub f) w = run world sub w := rfl

end World

namespace World

variable {V T W P S : Type}

/-- **Outcome non-interference.**  Assume

* `π` protects every effectful tool in `Prot` from `adv`, and
* `world` only changes at tools in `Prot` — i.e. every *unprotected* tool is
  effectless (a pure function or a side-effect-free query).

Then for any two `advEquiv` compliant plans, running either of them against
the same initial world produces the same final world.

The second assumption captures the deployment discipline: tools that aren't
in `Prot` must be implemented as pure queries.  This is exactly the role the
Q-LLM plays in CaMeL — it reads, it does not write. -/
theorem run_eq_of_advEquiv
    (world : World V T W) (π : Policy T P S) (adv : S → Prop)
    (Prot : T → Prop)
    (hProt : ∀ τ, Prot τ → π.protects τ adv)
    (hPure : ∀ τ, ¬ Prot τ → ∀ v w, world.effect τ v w = w)
    {t₁ t₂ : Trace V T P S}
    (heq : advEquiv adv t₁ t₂)
    (h₁ : π.compliant t₁) (h₂ : π.compliant t₂)
    (w : W) :
    run world t₁ w = run world t₂ w := by
  induction heq generalizing w with
  | leafClean _ _ _ => rfl
  | leafAdv _ _ _ _ => rfl
  | @call τ _ sub₁ sub₂ heq ih =>
      show world.effect τ sub₁.eval (run world sub₁ w)
         = world.effect τ sub₂.eval (run world sub₂ w)
      by_cases hP : Prot τ
      · -- Protected tool: argument value is invariant by non-interference,
        -- and the recursive world-runs agree by IH.
        have hfree : sub₁.advFree adv :=
          Policy.advFree_of_compliant (hProt τ hP) h₁ Subtrace.refl
        rw [Trace.eval_eq_of_advFree_advEquiv heq hfree,
            ih h₁.2 h₂.2 w]
      · -- Unprotected tool is effectless by hypothesis.
        rw [hPure τ hP sub₁.eval _, hPure τ hP sub₂.eval _]
        exact ih h₁.2 h₂.2 w
  | @combine _ a₁ a₂ b₁ b₂ _ _ iha ihb =>
      show run world b₁ (run world a₁ w) = run world b₂ (run world a₂ w)
      rw [iha h₁.1 h₂.1 w, ihb h₁.2 h₂.2 _]
  | @qParse _ sub₁ sub₂ _ ih =>
      -- Q-LLM is world-effectless by construction: both sides reduce to
      -- `run world subᵢ w`, and the recursive calls agree by IH.
      exact ih h₁ h₂ w

end World
end Camel
