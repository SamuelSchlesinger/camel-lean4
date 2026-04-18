import Camel.Scope

/-!
# Worked example — a browser-use agent (pedagogical model)

A third worked scenario, chosen specifically to exercise what a flat
`.web` source *cannot* express: **per-origin provenance** and
**composite DOM attribution**.

## The story

Alice says:

  *"Email our VP a summary of yesterday's engineering standup notes.
    The notes are at `notes.company.com/standup`; the VP is
    `vp@company.com`."*

The `notes.company.com` page is fully trusted as an *origin* —
Alice's intranet, not the open web.  But the page's rendered HTML
pulls in a third-party analytics widget from `cdn-tracker.com` that
has been compromised.  When the agent reads the page, the harness
(which is DOM-aware) attributes the fetched bytes to *both* origins
and stamps the `readPage` call's `outCap` with both.  This is exactly
what the per-call `outCap` mechanism of `Trace.call` is for: the
harness does provenance at the *resource* level, not the URL level.

The compromised CDN has injected an instruction into the summary
text.  The P-LLM faithfully builds `sendEmail(vp, summary)`.

* Under the **honest** rendering (no CDN injection), `readPage`'s
  output carries only `companyCom` in its cap.  The policy — which
  trusts intranet origins as email body sources — permits.
* Under the **compromised** rendering, `readPage`'s output carries
  both `companyCom` *and* `cdnCom`.  The policy refuses: `cdnCom`
  is not an approved body source.

The plan shape is **identical** in both cases.  The only difference
is the `outCap` stamped by the harness on `readPage` — which
reflects the DOM-level reality of what bytes entered the page.

## What this example adds over `EmailExample`

* Multiple distinct web origins, not uniformly adversarial.
* A policy that *accepts* some web provenance (`companyCom`) and
  refuses others (`cdnCom`).
* A call-node `outCap` carrying *multiple* sources — the natural
  model of DOM composition.
* Non-interference still holds: given a compliant plan, the value
  reaching `sendEmail` is adversary-invariant, even though the body
  is transitively derived from a web fetch.
-/

namespace Camel.BrowserExample

/-- Only one principal matters for this scenario. -/
inductive Principal | user
deriving DecidableEq

/-- The origins the harness distinguishes.  `user` is Alice's trusted
prompt; the others are web origins.  Per-origin tagging is the point
of the example — note that `companyCom` is *not* in the adversarial
set, even though it is a web origin. -/
inductive Src
  /-- Alice's trusted instruction. -/
  | user
  /-- The company's own intranet (`notes.company.com`, etc.). -/
  | companyCom
  /-- Third-party CDN embedded in pages (`cdn-tracker.com`). -/
  | cdnCom
deriving DecidableEq

/-- The tool vocabulary. -/
inductive Tool
  /-- Non-privileged: move the browser to a URL.  No world effect in
  this simplified model. -/
  | navigate
  /-- Non-privileged: read the current page.  The harness stamps the
  origins that contributed to the page's bytes on the `outCap`. -/
  | readPage
  /-- Privileged: compose and send mail.  The sink we must protect. -/
  | sendEmail
deriving DecidableEq

abbrev V := String

open Camel

abbrev C := Cap Principal Src

/-- Leaf cap: the user's trusted prompt. -/
def userCap : C where
  readers := fun _ => True
  sources := fun s => s = .user

/-- Adversarial sources for this scenario.  `cdnCom` is the only
adversary; `companyCom` is trusted.  This is the whole point — a
flat `.web` source couldn't make this distinction. -/
def adv : Src → Prop := fun s => s = .cdnCom

/-- **The policy.**
* `navigate` and `readPage` — unrestricted.
* `sendEmail` — permitted iff the argument's cap does not list
  `cdnCom` as a source.  User-sourced and company-intranet-sourced
  content is accepted; CDN-tainted content is not.

This is the per-origin nuance the calculus earns: a flat "web or
not" check would refuse the honest plan too. -/
def browserPolicy : Policy Tool Principal Src where
  permits
    | .navigate,  _ => True
    | .readPage,  _ => True
    | .sendEmail, c => ¬ c.sources .cdnCom

theorem browserPolicy_protects_sendEmail :
    browserPolicy.protects .sendEmail adv := by
  intro c hpermit s hs
  cases hs
  exact hpermit

/-! ## The harness's cap stamping on `readPage`

In the honest rendering, the page is served entirely from the
company's origin.  In the compromised rendering, a third-party
widget contributed bytes to the same page, and the DOM-aware harness
sees that — so the resulting cap's sources include both origins. -/

/-- Honest page rendering: only `companyCom` contributed. -/
def honestReadPageOutCap : C where
  readers := fun _ => True
  sources := fun s => s = .companyCom

/-- Compromised page rendering: both `companyCom` *and* `cdnCom`
contributed bytes.  Note that reading the URL has not changed; the
harness is attributing provenance to rendered content, not to the
URL the P-LLM asked for. -/
def compromisedReadPageOutCap : C where
  readers := fun _ => True
  sources := fun s => s = .companyCom ∨ s = .cdnCom

/-- `sendEmail`'s output cap.  `bot` — the "email sent" confirmation
carries no interesting provenance downstream. -/
def sendEmailOutCap : C := Cap.bot

/-- `readPage`'s subargument — the URL, which Alice named in her prompt. -/
def urlLeaf : Trace V Tool Principal Src :=
  .leaf "notes.company.com/standup" userCap

/-- The VP's email address, directly from Alice's prompt. -/
def vpLeaf : Trace V Tool Principal Src :=
  .leaf "vp@company.com" userCap

/-- Fuse recipient and body into the single argument the unary `call`
expects; the concrete string doesn't matter for the security analysis —
what matters is the *joined* capability. -/
def mkEmail : V → V → V := fun recipient body => recipient ++ " :: " ++ body

/-! ## The honest plan — accepted

Plan: read the notes page (harness stamps `companyCom`), combine
with the VP's address, hand to `sendEmail`. -/

/-- Honest reading of the notes page. -/
def honestBody : Trace V Tool Principal Src :=
  .call .readPage urlLeaf id honestReadPageOutCap

/-- The `sendEmail` argument: recipient combined with body. -/
def honestArg : Trace V Tool Principal Src :=
  .combine vpLeaf honestBody mkEmail

/-- The whole honest plan. -/
def honestTrace : Trace V Tool Principal Src :=
  .call .sendEmail honestArg id sendEmailOutCap

theorem honestTrace_compliant : browserPolicy.compliant honestTrace := by
  refine ⟨?_, trivial, trivial, trivial⟩
  -- `sendEmail`'s argument cap is `userCap ⊔ (userCap ⊔ honestReadPageOutCap)`;
  -- its `sources .cdnCom` is `False` by direct case analysis.
  rintro (h | h | h) <;> cases h

/-! ## The attacked plan — rejected

Same P-LLM plan shape; only the harness's `readPage` `outCap`
differs, because the DOM-aware harness notices the compromised CDN
contributed to the rendered page.  The extra `cdnCom` source
propagates unchanged through `combine` and reaches `sendEmail`,
which refuses. -/

/-- Compromised reading: same URL, two contributing origins. -/
def attackBody : Trace V Tool Principal Src :=
  .call .readPage urlLeaf id compromisedReadPageOutCap

def attackArg : Trace V Tool Principal Src :=
  .combine vpLeaf attackBody mkEmail

def attackTrace : Trace V Tool Principal Src :=
  .call .sendEmail attackArg id sendEmailOutCap

theorem attackTrace_not_compliant :
    ¬ browserPolicy.compliant attackTrace := by
  rintro ⟨hpermit, _⟩
  -- `sub.cap.sources .cdnCom` is satisfied via the right branch of the
  -- combine and the right disjunct of `compromisedReadPageOutCap`.
  exact hpermit (Or.inr (Or.inr (Or.inr rfl)))

/-! ## Value-level non-interference, applied

On the honest plan, no matter how an attacker rewrites any adv-tagged
leaf anywhere in the `sendEmail` argument subtree, the value
`sendEmail` actually receives is unchanged.

Note: the honest plan has no `cdnCom` sources anywhere, so any
`advEquiv` variant is forced to be a `leafClean` copy at every leaf.
Non-interference is strong precisely because the plan is clean. -/
theorem honestTrace_arg_fixed
    (arg₂ : Trace V Tool Principal Src)
    (heq : advEquiv adv honestArg arg₂) :
    arg₂.eval = honestArg.eval :=
  (Policy.noninterference browserPolicy .sendEmail adv
    browserPolicy_protects_sendEmail honestTrace_compliant
    (sub₁ := honestArg) (f := id) (outCap := sendEmailOutCap)
    Subtrace.refl heq).symm

/-! ## World-level non-interference

Model the world as the list of emails sent so far.  Only `sendEmail`
has an effect. -/

abbrev World := List String

def browserWorld : Camel.World V Tool World where
  effect
    | .sendEmail, payload, w => payload :: w
    | .navigate,  _,       w => w
    | .readPage,  _,       w => w

def isProtected : Tool → Prop
  | .sendEmail => True
  | .navigate  => False
  | .readPage  => False

theorem isProtected_protects :
    ∀ τ, isProtected τ → browserPolicy.protects τ adv := by
  intro τ h
  cases τ with
  | sendEmail => exact browserPolicy_protects_sendEmail
  | navigate  => exact False.elim h
  | readPage  => exact False.elim h

theorem isProtected_unprotected_pure :
    ∀ τ, ¬ isProtected τ → ∀ v w, browserWorld.effect τ v w = w := by
  intro τ h v w
  cases τ with
  | sendEmail => exact False.elim (h trivial)
  | navigate  => rfl
  | readPage  => rfl

/-- **Outcome-level non-interference, applied.**  The sequence of
emails the honest plan sends is adversary-invariant: whatever the
attacker does inside adv-tagged leaves of any advEquiv variant, the
resulting mailbox is unchanged.  Instantiates
`World.run_eq_of_advEquiv`. -/
theorem honestTrace_world_fixed
    (t₂ : Trace V Tool Principal Src)
    (heq : advEquiv adv honestTrace t₂)
    (ht₂ : browserPolicy.compliant t₂)
    (w : World) :
    browserWorld.run honestTrace w = browserWorld.run t₂ w :=
  World.run_eq_of_advEquiv browserWorld browserPolicy adv
    isProtected isProtected_protects isProtected_unprotected_pure
    heq honestTrace_compliant ht₂ w

/-! ## Reading suggestion

Compare this file to `Camel.EmailExample`.  The plan shapes are very
similar — a privileged sink consuming a Q-LLM/tool-derived argument
— but the attack models are orthogonal:

* **Email example:** a single untrusted origin (`drive`) whose mere
  presence in the cap causes rejection.
* **Browser example:** multiple origins sharing a single rendered
  artifact, with *partial* trust.  The per-call `outCap` mechanism
  is what lets the harness record the partial trust faithfully.

A deployment that collapses all web origins into a single `.web`
source forfeits the distinction this example draws — and forfeits
the honest plan, which reads a trusted intranet page.
-/

end Camel.BrowserExample
