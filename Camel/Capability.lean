/-!
# Capabilities

A **capability** is the runtime tag that CaMeL attaches to every value produced by the
interpreter.  Two pieces of information ride along with each value:

* the set of **principals** permitted to read it, and
* the set of **sources** it was derived from.

Combining two capability-tagged values produces a new value whose capability is the
*join* of the ingredients — readers shrink to the intersection, sources grow to the
union.  This is the data-flow graph of the paper, reified as an algebraic structure.

The file is self-contained: no `Mathlib`, just plain Lean 4 core.
-/

namespace Camel

/-- A capability on a value.

`readers p` states that principal `p` is allowed to observe the value; `sources s`
states that source `s` contributed to the value's derivation.  We use predicates
(`· → Prop`) rather than finite sets, so the model is free of decidability
assumptions and trivially works with infinite principal/source spaces. -/
structure Cap (P S : Type) where
  readers : P → Prop
  sources : S → Prop

namespace Cap

variable {P S : Type}

/-- The *least restrictive* capability: everyone may read, no source contributed.
This is the tag we attach to program literals and the output of pure computations. -/
def bot : Cap P S where
  readers := fun _ => True
  sources := fun _ => False

/-- The *most restrictive* capability: no one may read, every source contributed. -/
def top : Cap P S where
  readers := fun _ => False
  sources := fun _ => True

/-- Combine the capabilities of two inputs merged into a single output.
Readers must be permitted by *both* parents; sources accumulate from *either*. -/
def join (c₁ c₂ : Cap P S) : Cap P S where
  readers p := c₁.readers p ∧ c₂.readers p
  sources s := c₁.sources s ∨ c₂.sources s

instance : Max (Cap P S) := ⟨join⟩

@[simp] theorem readers_bot (p : P) : (bot : Cap P S).readers p ↔ True := Iff.rfl
@[simp] theorem sources_bot (s : S) : (bot : Cap P S).sources s ↔ False := Iff.rfl
@[simp] theorem readers_join (c₁ c₂ : Cap P S) (p : P) :
    (join c₁ c₂).readers p ↔ c₁.readers p ∧ c₂.readers p := Iff.rfl
@[simp] theorem sources_join (c₁ c₂ : Cap P S) (s : S) :
    (join c₁ c₂).sources s ↔ c₁.sources s ∨ c₂.sources s := Iff.rfl

/-- `c₁ ≤ c₂` means `c₁` is **no more restrictive** than `c₂`:
every reader admitted by `c₂` is also admitted by `c₁`, and every source of `c₁`
is also a source of `c₂`.

Intuition: going *up* the order corresponds to *more* information flowing in. -/
def le (c₁ c₂ : Cap P S) : Prop :=
  (∀ p, c₂.readers p → c₁.readers p) ∧ (∀ s, c₁.sources s → c₂.sources s)

instance : LE (Cap P S) := ⟨le⟩

theorem le_refl (c : Cap P S) : c ≤ c :=
  ⟨fun _ h => h, fun _ h => h⟩

theorem le_trans {c₁ c₂ c₃ : Cap P S} (h₁ : c₁ ≤ c₂) (h₂ : c₂ ≤ c₃) : c₁ ≤ c₃ :=
  ⟨fun p hp => h₁.1 p (h₂.1 p hp), fun s hs => h₂.2 s (h₁.2 s hs)⟩

theorem bot_le (c : Cap P S) : (bot : Cap P S) ≤ c :=
  ⟨fun _ _ => trivial, fun _ h => False.elim h⟩

theorem le_top (c : Cap P S) : c ≤ (top : Cap P S) :=
  ⟨fun _ h => False.elim h, fun _ _ => trivial⟩

theorem le_join_left (c₁ c₂ : Cap P S) : c₁ ≤ join c₁ c₂ :=
  ⟨fun _ h => h.1, fun _ h => Or.inl h⟩

theorem le_join_right (c₁ c₂ : Cap P S) : c₂ ≤ join c₁ c₂ :=
  ⟨fun _ h => h.2, fun _ h => Or.inr h⟩

/-- Universal property of join: it is the least upper bound. -/
theorem join_le {c₁ c₂ c : Cap P S} (h₁ : c₁ ≤ c) (h₂ : c₂ ≤ c) : join c₁ c₂ ≤ c :=
  ⟨fun p hp => ⟨h₁.1 p hp, h₂.1 p hp⟩,
   fun s hs => hs.elim (h₁.2 s) (h₂.2 s)⟩

/-- Join is monotone in both arguments. -/
theorem join_mono {a b c d : Cap P S} (h₁ : a ≤ c) (h₂ : b ≤ d) : join a b ≤ join c d :=
  join_le (le_trans h₁ (le_join_left c d)) (le_trans h₂ (le_join_right c d))

end Cap
end Camel
