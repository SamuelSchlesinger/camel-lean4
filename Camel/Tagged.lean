import Camel.Capability

/-!
# Tagged values

`Tagged α P S` is a value of type `α` paired with the capability tracking it.
Every value inside the CaMeL interpreter lives in `Tagged`.

The important invariant is that every combinator lifts to `Tagged` *by joining the
capabilities of its inputs*.  This is what makes the capability tag a sound
provenance — see `Camel.Trace.cap_eq_true` for the matching theorem.
-/

namespace Camel

/-- A value paired with the capability tracking who can read it and what it was
derived from. -/
structure Tagged (α P S : Type) where
  value : α
  cap   : Cap P S

namespace Tagged

variable {α β γ P S : Type}

/-- Lift an unrestricted literal into `Tagged`.  Its capability is `bot`: public
and derived from nothing. -/
def pure (a : α) : Tagged α P S := ⟨a, Cap.bot⟩

/-- Apply a pure unary function; the capability is unchanged because no new input
entered the data flow. -/
def map (f : α → β) (t : Tagged α P S) : Tagged β P S :=
  ⟨f t.value, t.cap⟩

/-- Combine two tagged values; the capability is their join. -/
def zipWith (f : α → β → γ) (t₁ : Tagged α P S) (t₂ : Tagged β P S) : Tagged γ P S :=
  ⟨f t₁.value t₂.value, Cap.join t₁.cap t₂.cap⟩

/-- Attach extra restriction to a tagged value (e.g., marking it `Untrusted`). -/
def label (c : Cap P S) (t : Tagged α P S) : Tagged α P S :=
  ⟨t.value, Cap.join t.cap c⟩

@[simp] theorem pure_cap (a : α) : (pure a : Tagged α P S).cap = Cap.bot := rfl
@[simp] theorem map_cap (f : α → β) (t : Tagged α P S) :
    (map f t).cap = t.cap := rfl
@[simp] theorem zipWith_cap (f : α → β → γ) (t₁ : Tagged α P S) (t₂ : Tagged β P S) :
    (zipWith f t₁ t₂).cap = Cap.join t₁.cap t₂.cap := rfl
@[simp] theorem label_cap (c : Cap P S) (t : Tagged α P S) :
    (label c t).cap = Cap.join t.cap c := rfl

/-- `pure` really is the least restrictive possible capability. -/
theorem pure_cap_le (a : α) (c : Cap P S) : (pure a : Tagged α P S).cap ≤ c :=
  Cap.bot_le c

/-- Combining two tagged values can only *increase* the restriction. -/
theorem cap_le_zipWith_left (f : α → β → γ) (t₁ : Tagged α P S) (t₂ : Tagged β P S) :
    t₁.cap ≤ (zipWith f t₁ t₂).cap := Cap.le_join_left _ _

theorem cap_le_zipWith_right (f : α → β → γ) (t₁ : Tagged α P S) (t₂ : Tagged β P S) :
    t₂.cap ≤ (zipWith f t₁ t₂).cap := Cap.le_join_right _ _

end Tagged

/-- A tagged value is *poisoned* w.r.t. an adversarial-source predicate `adv`
iff its tracked capability names some `adv`-source.  Operational reading: "an
attacker may have influenced these bits." -/
def poisoned {α P S : Type} (adv : S → Prop) (t : Tagged α P S) : Prop :=
  ∃ s, adv s ∧ t.cap.sources s

end Camel
