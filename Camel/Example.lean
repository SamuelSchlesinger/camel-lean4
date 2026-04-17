import Camel.Scope

/-!
# Worked example — a travel-agent attack (paper §2)

A concrete instantiation of the CaMeL formalism on the paper's motivating
scenario.  Everything in this file is *applied* — no theorem is re-proved at
the concrete level; we only *instantiate* the general theorems on specific
policies and traces.

### The story

Alice asks the agent: *"Book me the cheapest flight Tuesday to Paris."*

The agent calls `search` (returning flights from the web) and then `book`
on the chosen flight.  An attacker has planted a prompt injection in one
of the search results that tries to redirect the booking.

In a naive agent, the P-LLM re-reads the search results and gets tricked.
In CaMeL, every search result is tagged `web`, and the `book` policy refuses
anything carrying a `web` source — so the attack cannot succeed.

We formalise three layers of the guarantee on concrete data:

* `attackedTrace_not_compliant`  — the interpreter rejects the attack.
* `honestTrace_book_arg_fixed`   — under compliance, Alice's chosen
  booking value is independent of attacker choices.
  (Instantiates `Policy.noninterference`.)
* `honestTrace_world_fixed`      — the resulting world (bookings made) is
  independent of attacker choices.
  (Instantiates `World.run_eq_of_advEquiv`.)
-/

namespace Camel.Example

/-- Who may read a value.  Only Alice matters for this scenario. -/
inductive Principal | alice
deriving DecidableEq

/-- Where a value originated. -/
inductive Src
  /-- Alice's trusted instruction (user prompt). -/
  | user
  /-- Anything from the open web or an untrusted tool.  This is the source
  CaMeL treats as adversarial. -/
  | web
deriving DecidableEq

/-- The tool vocabulary. -/
inductive Tool
  /-- Non-privileged retrieval — no world effect, always permitted. -/
  | search
  /-- Privileged side-effectful action — must be protected. -/
  | book
deriving DecidableEq

/-- A tiny value universe: just strings. -/
abbrev V := String

open Camel

abbrev C := Cap Principal Src

/-- A leaf capability marking its value as coming from Alice. -/
def userCap : C where
  readers := fun _ => True
  sources := fun s => s = .user

/-- A leaf capability marking its value as coming from the web. -/
def webCap : C where
  readers := fun _ => True
  sources := fun s => s = .web

/-- The adversary predicate for this scenario: `.web`-sourced data. -/
def adv : Src → Prop := (· = .web)

/-- The **policy**: `book` may only be called on values with no `web` in their
source set.  `search` is unrestricted. -/
def travelPolicy : Policy Tool Principal Src where
  permits
    | .search, _ => True
    | .book,   c => ¬ c.sources .web

/-- `travelPolicy` protects `book` from `.web`-sourced data.  Direct from the
definition — this is the policy design that gives the calculus its teeth. -/
theorem travelPolicy_protects_book :
    travelPolicy.protects .book adv := by
  intro c hpermit s hs
  cases hs
  exact hpermit

/-! ## The attacked trace — rejected by the interpreter -/

/-- Plan: `book("attacker-injected LX999 to Moscow")`.  Argument is
web-sourced, so the interpreter must refuse. -/
def attackedTrace : Trace V Tool Principal Src :=
  .call .book (.leaf "attacker-injected LX999 to Moscow" webCap) id

theorem attackedTrace_not_compliant :
    ¬ travelPolicy.compliant attackedTrace := by
  rintro ⟨hpermit, _⟩
  exact hpermit (by rfl)

/-! ## The honest trace — accepted, and its output is adversary-invariant -/

/-- Plan: `book("AF123 to Paris")`, Alice's actual choice. -/
def honestTrace : Trace V Tool Principal Src :=
  .call .book (.leaf "AF123 to Paris" userCap) id

theorem honestTrace_compliant : travelPolicy.compliant honestTrace := by
  refine ⟨?_, trivial⟩
  intro h
  cases h

/-- **Value-level non-interference, applied.**  No matter how an attacker
rewrites adv-tagged leaves inside the `book` argument subtree, the value
passed to `book` is unchanged.

Directly instantiates `Policy.noninterference`. -/
theorem honestTrace_book_arg_fixed
    (sub₂ : Trace V Tool Principal Src)
    (heq : advEquiv adv (.leaf "AF123 to Paris" userCap) sub₂) :
    sub₂.eval = "AF123 to Paris" :=
  (Policy.noninterference travelPolicy .book adv
    travelPolicy_protects_book honestTrace_compliant
    (sub₁ := .leaf "AF123 to Paris" userCap) (f := id)
    Subtrace.refl heq).symm

/-! ## World-level non-interference on the travel world

Model a world as "the list of bookings made so far".  `book` appends its
argument; `search` is effectless. -/

abbrev World := List String

/-- The travel world: only `book` has an effect. -/
def travelWorld : Camel.World V Tool World where
  effect
    | .book, arg, w => arg :: w
    | .search, _, w => w

/-- `.search` is not protected — and has no world effect, as required by
`World.run_eq_of_advEquiv`. -/
def isProtected : Tool → Prop
  | .book   => True
  | .search => False

theorem isProtected_protects :
    ∀ τ, isProtected τ → travelPolicy.protects τ adv := by
  intro τ h
  cases τ with
  | search => exact False.elim h
  | book   => exact travelPolicy_protects_book

theorem isProtected_unprotected_pure :
    ∀ τ, ¬ isProtected τ → ∀ v w, travelWorld.effect τ v w = w := by
  intro τ h v w
  cases τ with
  | search => rfl
  | book   => exact False.elim (h trivial)

/-- **Outcome-level non-interference, applied.**  Running `honestTrace`
against `travelWorld` from any initial world produces the same bookings list
as running any advEquiv variant of it.  Instantiates
`World.run_eq_of_advEquiv`. -/
theorem honestTrace_world_fixed
    (t₂ : Trace V Tool Principal Src)
    (heq : advEquiv adv honestTrace t₂)
    (ht₂ : travelPolicy.compliant t₂)
    (w : World) :
    travelWorld.run honestTrace w = travelWorld.run t₂ w :=
  World.run_eq_of_advEquiv travelWorld travelPolicy adv
    isProtected isProtected_protects isProtected_unprotected_pure
    heq honestTrace_compliant ht₂ w

/-! ## The Q-LLM in action

A realistic CaMeL plan reads untrusted email with `search`, then invokes the
**Q-LLM** to extract a flight code.  Here is exactly that pattern: an
adversarial search result is parsed by the Q-LLM (`qParse`), and the policy
*still* rejects any attempt to route the parsed value into `book` — because
the Q-LLM is cap-preserving, so the web source tag survives the parse. -/

/-- An adversarial plan: search returns attacker content, the Q-LLM parses
it, and the result is fed to `book`.  The qParse step is permitted (Q-LLM is
policy-exempt) but the `book` call is rejected because the cap still carries
`.web`. -/
def qParseAttackTrace : Trace V Tool Principal Src :=
  .call .book
    (.qParse (.leaf "attacker-planted itinerary" webCap)
             (fun s => "parsed: " ++ s))
    id

/-- The interpreter *does* let the Q-LLM run on web-sourced input (no policy
gate on `qParse`), but it still refuses the downstream `book` — this is what
the cap-preservation of the Q-LLM buys us. -/
theorem qParseAttackTrace_not_compliant :
    ¬ travelPolicy.compliant qParseAttackTrace := by
  rintro ⟨hpermit, _⟩
  -- The Q-LLM preserves cap, so the `book` argument's cap still says `.web`.
  exact hpermit (by rfl)

/-- By contrast, a Q-LLM step on *user-sourced* input and a user-sourced
booking remains compliant.  Parsing is orthogonal to security: it neither
helps nor hurts the policy check. -/
def qParseHonestTrace : Trace V Tool Principal Src :=
  .call .book
    (.qParse (.leaf "AF123 to Paris" userCap) id)
    id

theorem qParseHonestTrace_compliant : travelPolicy.compliant qParseHonestTrace := by
  refine ⟨?_, trivial⟩
  intro h
  cases h

end Camel.Example
