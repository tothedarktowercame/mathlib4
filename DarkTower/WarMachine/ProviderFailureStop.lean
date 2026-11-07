import DarkTower.WarMachine.CloseOutcomeImage

/-!
# A provider failure on a seat contact: retry once, then a typed stop (2026-11-07)

Source: Joe's ruling of 2026-11-07, recorded at the end of
`~/notes/wm-next/provider-fail-discovery-2026-11-07.md`: "I agree with your
(b)-to-(c), though (c) should be typed, e.g., is it a usage issue, or
overloaded model, or something else?"  (b) is "retry that call once", (c) is
"stop and wait for Joe".

**What happened.**  Click `wm-click-70f995eb` (run `2026-11-07-1249942a`): the
wm-author contact `invoke-1794040065486-15049-56005758` failed with Zai HTTP 429,
code 1308 ("Usage limit reached for 5 hour").  The open-cascade author branch
recorded the empty answer as `:open-cascade-author-answer-invalid`, the
terminal sink classified it an injury (`injury/0cb09c47…`), and the next click
routed to dedicated meta-self-heal, whose own diagnosis call then failed with
a Zai HTTP 500 (code 1234) and stopped the loop.

**The code this records (Clojure first, Lean after; futon2 main).**
PROVIDER-FAIL-3 `2172859dd` (`provider-failure-class`), PROVIDER-FAIL-4a
`3b9b3a9e0` (`with-provider-retry`, `provider-unavailable-refusal` in
`full_loop_runtime.clj`), PROVIDER-FAIL-4b `b5deb65f0`
(`:open-cascade-provider-unavailable ↦ :provider-unavailable` in
`explicit-non-injury-kinds`, `meta_terminal_injury.clj`).  The loop-side stop is
PROVIDER-FAIL-4c.  Additions only; `Verdict` is `CloseOutcomeImage`'s.
-/

namespace DarkTower.WarMachine.ProviderFailureStop

open DarkTower.WarMachine.CloseOutcomeImage (Verdict)

/-- `provider-failure-class`: what the job's terminal text says happened.
`notProvider` covers a done job and a failure with no provider signal
(not contacted, a bare cancel); it is never guessed from nothing. -/
inductive ProviderClass where
  | usageLimit
  | modelOverloaded
  | providerError
  | timeout
  | notProvider
  deriving DecidableEq, Repr

def ProviderClass.isProvider : ProviderClass → Bool
  | .notProvider => false
  | _ => true

/-- One contact with a seat, as the open-cascade branch reads it. -/
inductive Contact where
  | answered
  | failed (c : ProviderClass)
  deriving DecidableEq, Repr

/-- How the open-cascade contact step ends. -/
inductive Ending where
  /-- The seat answered (first time, or on the one retry). -/
  | proceed (retried : Bool)
  /-- No retry: the failure was not a provider failure (PROVIDER-FAIL-2's
  contact-failed refusal). -/
  | contactFailed
  /-- Both contacts failed at the provider: the typed stop, carrying the
  retry's class. -/
  | providerUnavailable (c : ProviderClass)
  deriving DecidableEq, Repr

/-- `with-provider-retry`: `second` is consulted only when the first contact
failed at the provider. -/
def step (first second : Contact) : Ending :=
  match first with
  | .answered => .proceed false
  | .failed c =>
    if c.isProvider then
      match second with
      | .answered => .proceed true
      | .failed c' => if c'.isProvider then .providerUnavailable c' else .contactFailed
    else .contactFailed

/-- Number of contacts `step` makes. -/
def contacts (first : Contact) : Nat :=
  match first with
  | .failed c => if c.isProvider then 2 else 1
  | .answered => 1

/-- At most one retry, ever. -/
theorem contacts_le_two (first : Contact) : contacts first ≤ 2 := by
  cases first with
  | answered => decide
  | failed c => cases c <;> decide

/-- A non-provider failure is never retried. -/
theorem no_retry_without_provider (c : ProviderClass) (h : c.isProvider = false)
    (second : Contact) :
    step (.failed c) second = .contactFailed ∧ contacts (.failed c) = 1 := by
  simp [step, contacts, h]

/-- The ruling's (c) is typed: when the click stops on the provider, the stop
names a provider class, never `notProvider`. -/
theorem stop_is_typed (first second : Contact) (c : ProviderClass)
    (h : step first second = .providerUnavailable c) : c.isProvider = true := by
  cases first with
  | answered => simp [step] at h
  | failed c₀ =>
    cases second with
    | answered => cases c₀ <;> simp [step, ProviderClass.isProvider] at h
    | failed c₁ =>
      cases c₀ <;> cases c₁ <;>
        simp [step, ProviderClass.isProvider] at h <;> subst h <;> rfl

/-- The terminal's verdict on an ending that reaches the injury sink
(`explicit-non-injury-kinds`): a provider-unavailable stop is not a machine
injury; a contact failure with no provider signal still is. -/
def endingVerdict : Ending → Option Verdict
  | .providerUnavailable _ => some .nonInjury
  | .contactFailed => some .injury
  | .proceed _ => none

/-- The 2026-11-07 case: two 429s end as a typed usage-limit stop that the
terminal does not count as an injury. -/
example : step (.failed .usageLimit) (.failed .usageLimit) = .providerUnavailable .usageLimit ∧
    endingVerdict (.providerUnavailable .usageLimit) = some .nonInjury := by decide

/-- A 429 followed by a good answer proceeds, marked as retried. -/
example : step (.failed .usageLimit) .answered = .proceed true := by decide

end DarkTower.WarMachine.ProviderFailureStop
