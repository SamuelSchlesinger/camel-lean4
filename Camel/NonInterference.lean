import Camel.Security

/-!
# Non-interference: the *teeth* of the security theorem

`Camel.Security.security` says that a compliant trace never contains an
adversarial source *in the tracked capability* of a protected tool's argument.
That is necessary but, on its own, not very satisfying: it's a statement about
**tags**, not about **behaviour**.

The paper's real claim is stronger, and is formalised here.  Fix an adversary
who can choose the bytes of any leaf whose capability lists an adversarial
source.  Then:

> For every protected-tool call in a compliant plan, the **value** passed to
> that call is independent of the adversary's choices.

This is a non-interference result in the classical sense.  It is the bridge
between "tags are tracked correctly" and "bad outcomes cannot happen": if the
attacker cannot influence the argument to `τ`, the attacker cannot influence
whatever effect `τ` has on the world.

## What this module adds

* `Trace.advFree adv t` — *no* leaf of `t` has an adv-source in its cap.
* `Trace.advFree_iff_trueSources` — `advFree` is equivalent to "no adv source
  appears in the ground-truth source set".
* `Policy.advFree_of_compliant` — the consequence of compliance + protection:
  every protected τ-call's argument subtree is `advFree`.
* `advEquiv adv t₁ t₂` — two plan shapes agreeing everywhere except possibly
  on bytes in adv-tagged leaves.  Models "what the attacker can change".
* `Trace.eval_eq_of_advFree_advEquiv` — the key technical lemma: advFree
  subtrees evaluate identically under any advEquiv swap.
* `Policy.noninterference` — the headline theorem: for adv-equivalent
  compliant traces, every protected τ-call's argument value is the same.
-/

namespace Camel

namespace Trace

variable {V T P S : Type}

/-- `t.advFree adv` — no leaf, and no call-node `outCap`, of `t` carries any
adv-source.  Equivalently (see `advFree_iff_trueSources`), the ground-truth
source set of `t` is disjoint from `adv`. -/
def advFree (adv : S → Prop) : Trace V T P S → Prop
  | .leaf _ c         => ∀ s, adv s → ¬ c.sources s
  | .call _ sub _ oc  => advFree adv sub ∧ (∀ s, adv s → ¬ oc.sources s)
  | .combine t₁ t₂ _  => advFree adv t₁ ∧ advFree adv t₂
  | .qParse sub _     => advFree adv sub

theorem advFree_iff_trueSources (adv : S → Prop) (t : Trace V T P S) :
    t.advFree adv ↔ ∀ s, adv s → ¬ t.trueSources s := by
  induction t with
  | leaf v c => rfl
  | call τ sub f oc ih =>
      show sub.advFree adv ∧ _ ↔ _
      rw [ih]
      constructor
      · rintro ⟨hsub, hoc⟩ s hs hts
        exact hts.elim (hsub s hs) (hoc s hs)
      · intro h
        refine ⟨fun s hs hts => h s hs (Or.inl hts),
                fun s hs hoc => h s hs (Or.inr hoc)⟩
  | qParse sub f ih => exact ih
  | combine t₁ t₂ g ih₁ ih₂ =>
      show t₁.advFree adv ∧ t₂.advFree adv ↔ _
      rw [ih₁, ih₂]
      constructor
      · rintro ⟨h₁, h₂⟩ s hs hts
        exact hts.elim (h₁ s hs) (h₂ s hs)
      · intro h
        refine ⟨fun s hs hts => h s hs (Or.inl hts),
                fun s hs hts => h s hs (Or.inr hts)⟩

end Trace

namespace Policy

variable {V T P S : Type}

/-- **Compliance + protection ⟹ advFree at protected call sites.**

If `π` protects `τ` from adversarial sources and `t` is compliant with `π`,
then every `τ`-call appearing in `t` has an `advFree` argument subtree. -/
theorem advFree_of_compliant
    {π : Policy T P S} {τ : T} {adv : S → Prop} (hπ : π.protects τ adv)
    {t : Trace V T P S} (ht : compliant π t)
    {sub : Trace V T P S} {f : V → V} {outCap : Cap P S}
    (hsub : Subtrace (Trace.call τ sub f outCap) t) :
    sub.advFree adv := by
  rw [Trace.advFree_iff_trueSources]
  exact security π τ adv hπ ht hsub

end Policy

/-- **What the attacker may rewrite.**  Two traces are `advEquiv` iff they have
the same plan shape and agree on every leaf, *except* that at leaves whose cap
contains some adversarial source the attacker may have chosen a different
value.

Pure functions at `call` and `combine` nodes are shared — the attacker controls
*bytes of leaves*, not *structure of the plan*.  This matches the CaMeL threat
model: the P-LLM produces the plan; the attacker produces tool outputs. -/
inductive advEquiv {V T P S : Type} (adv : S → Prop) :
    Trace V T P S → Trace V T P S → Prop where
  | leafClean :
      (c : Cap P S) → (v : V) → (∀ s, adv s → ¬ c.sources s) →
      advEquiv adv (.leaf v c) (.leaf v c)
  | leafAdv :
      (c : Cap P S) → (v₁ v₂ : V) → (∃ s, adv s ∧ c.sources s) →
      advEquiv adv (.leaf v₁ c) (.leaf v₂ c)
  | call :
      (τ : T) → (f : V → V) → (outCap : Cap P S) →
      {sub₁ sub₂ : Trace V T P S} →
      advEquiv adv sub₁ sub₂ →
      advEquiv adv (.call τ sub₁ f outCap) (.call τ sub₂ f outCap)
  | combine :
      (g : V → V → V) →
      {a₁ a₂ b₁ b₂ : Trace V T P S} →
      advEquiv adv a₁ a₂ → advEquiv adv b₁ b₂ →
      advEquiv adv (.combine a₁ b₁ g) (.combine a₂ b₂ g)
  | qParse :
      (f : V → V) →
      {sub₁ sub₂ : Trace V T P S} →
      advEquiv adv sub₁ sub₂ →
      advEquiv adv (.qParse sub₁ f) (.qParse sub₂ f)

namespace Trace

variable {V T P S : Type}

/-- **Key lemma.**  If `t₁` is `advFree` and `advEquiv` to `t₂`, then the two
traces evaluate to the same value.

Intuition: `advFree` rules out any `leafAdv` case, so the relation collapses
to "structurally identical, with identical leaves" — and pure functions at
non-leaves trivially commute. -/
theorem eval_eq_of_advFree_advEquiv {adv : S → Prop}
    {t₁ t₂ : Trace V T P S}
    (heq : advEquiv adv t₁ t₂) (hfree : t₁.advFree adv) :
    t₁.eval = t₂.eval := by
  induction heq with
  | leafClean c v _ => rfl
  | leafAdv c v₁ v₂ h =>
      obtain ⟨s, hadv, hs⟩ := h
      exact absurd hs (hfree s hadv)
  | call τ f oc _ ih =>
      show f _ = f _
      exact congrArg f (ih hfree.1)
  | combine g _ _ ih₁ ih₂ =>
      show g _ _ = g _ _
      rw [ih₁ hfree.1, ih₂ hfree.2]
  | qParse f _ ih =>
      show f _ = f _
      exact congrArg f (ih hfree)

end Trace

namespace Policy

variable {V T P S : Type}

/-- **Non-interference at a protected tool call.**

Assume

* `π` protects `τ` from adversarial sources,
* `t₁` is compliant with `π`,
* `t₁` contains the call `call τ sub₁ f` (at some position),
* `sub₂` is any plan that is `advEquiv` to `sub₁`.

Then `sub₁.eval = sub₂.eval`.

**Reading**: whatever bytes the attacker is permitted to write — at the
leaves of the plan that carry adv-sources — those bytes cannot influence the
value passed to a protected `τ`-call.  This is the formal analogue of
"the attacker cannot redirect the flight booking." -/
theorem noninterference
    (π : Policy T P S) (τ : T) (adv : S → Prop) (hπ : π.protects τ adv)
    {t₁ : Trace V T P S} (h₁ : compliant π t₁)
    {sub₁ : Trace V T P S} {f : V → V} {outCap : Cap P S}
    (hsub₁ : Subtrace (Trace.call τ sub₁ f outCap) t₁)
    {sub₂ : Trace V T P S}
    (heqSub : advEquiv adv sub₁ sub₂) :
    sub₁.eval = sub₂.eval :=
  Trace.eval_eq_of_advFree_advEquiv heqSub (advFree_of_compliant hπ h₁ hsub₁)

end Policy
end Camel
