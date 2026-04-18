import Camel.Policy

/-!
# Security theorem

The headline result: if an entire trace is `compliant` with a policy `π`, and `π`
`protects` a sensitive tool `τ` from a set of untrusted sources, then **no value
derived from those untrusted sources ever reaches a call to `τ`** anywhere in
the trace.

This is CaMeL's design-time guarantee: the capability-based interpreter makes
untrusted-data-to-sensitive-sink flows unrepresentable.
-/

namespace Camel

namespace Policy

variable {V T P S : Type}

/-- Compliance is hereditary: a compliant trace has compliant subtraces. -/
theorem compliant_subtrace {π : Policy T P S}
    {sub t : Trace V T P S} (hsub : Subtrace sub t) :
    compliant π t → compliant π sub := by
  induction hsub with
  | refl         => exact id
  | call _ ih    => exact fun h => ih h.2
  | combL _ ih   => exact fun h => ih h.1
  | combR _ ih   => exact fun h => ih h.2
  | qParse _ ih  => exact fun h => ih h

/-- If a `call τ sub f` appears anywhere in a compliant trace, the policy
permits `τ` at the tracked capability of its argument. -/
theorem permits_of_compliant {π : Policy T P S}
    {τ : T} {sub : Trace V T P S} {f : V → V} {outCap : Cap P S}
    {t : Trace V T P S} (ht : compliant π t)
    (hsub : Subtrace (Trace.call τ sub f outCap) t) :
    π.permits τ sub.cap :=
  (compliant_subtrace hsub ht).1

/-- **Main security theorem.**

Assume
* `π` protects tool `τ` from the untrusted-source predicate `bad`, and
* `t` is a compliant trace.

Then for every subtrace of `t` of the form `call τ sub f`, none of the true
sources feeding `sub` lie in `bad`.

In words: a compliant CaMeL program never invokes a protected tool on a value
that was actually derived from untrusted data. -/
theorem security
    (π : Policy T P S) (τ : T) (bad : S → Prop)
    (hπ : π.protects τ bad)
    {t : Trace V T P S} (ht : compliant π t)
    {sub : Trace V T P S} {f : V → V} {outCap : Cap P S}
    (hsub : Subtrace (Trace.call τ sub f outCap) t) :
    ∀ s, bad s → ¬ sub.trueSources s := by
  intro s hbad
  have hperm : π.permits τ sub.cap := permits_of_compliant ht hsub
  have hnot  : ¬ sub.cap.sources s := hπ sub.cap hperm s hbad
  exact Trace.no_source_of_cap hnot

/-- **Reader-side dual.**

If `π.permits τ c` also requires that some principal `p` *not* read `c`
(i.e., the policy only allows tools that have adequate readership), then every
leaf feeding into a `τ`-call is unreadable by `p`.  This models the paper's
"readers control exfiltration" story.

Stated here as the contrapositive of `security` for readers. -/
theorem security_readers
    (π : Policy T P S) (τ : T) (p : P)
    (hπ : ∀ c, π.permits τ c → ¬ c.readers p)
    {t : Trace V T P S} (ht : compliant π t)
    {sub : Trace V T P S} {f : V → V} {outCap : Cap P S}
    (hsub : Subtrace (Trace.call τ sub f outCap) t) :
    ¬ sub.trueReaders p := by
  intro htr
  have hperm  : π.permits τ sub.cap := permits_of_compliant ht hsub
  have hnotR  : ¬ sub.cap.readers p := hπ sub.cap hperm
  exact hnotR (((Trace.cap_eq_true sub).1 p).mpr htr)

end Policy
end Camel
