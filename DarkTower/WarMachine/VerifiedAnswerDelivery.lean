/- The ordinary held-cascade answer-delivery boundary. JSON is a claim;
   the reviewed, digest-verified function supplies the operational answers.
   These booleans denote checks performed by the production boundary. -/
namespace DarkTower.WarMachine.VerifiedAnswerDelivery

structure Evidence where
  identityAndReviewChecked : Bool
  sourceDigestChecked : Bool
  functionChecked : Bool
  exactHoleCoverage : Bool
  operationalMaps : Bool
  jsonClaimMatches : Bool
  deriving DecidableEq, Repr

def mayLoad (e : Evidence) : Bool := e.identityAndReviewChecked

def delivered (e : Evidence) : Bool :=
  mayLoad e && e.sourceDigestChecked && e.functionChecked &&
    e.exactHoleCoverage && e.operationalMaps

def authorResponseDefect (e : Evidence) : Bool := !e.jsonClaimMatches

theorem delivered_iff_checked (e : Evidence) : delivered e = true ↔
    e.identityAndReviewChecked = true ∧ e.sourceDigestChecked = true ∧
    e.functionChecked = true ∧ e.exactHoleCoverage = true ∧
    e.operationalMaps = true := by
  simp [delivered, mayLoad, Bool.and_eq_true, and_assoc]

theorem missing_hole_refused (e : Evidence) (h : e.exactHoleCoverage = false) :
    delivered e = false := by simp [delivered, h]

theorem claim_does_not_supply_answers (e : Evidence) (claim : Bool) :
    delivered {e with jsonClaimMatches := claim} = delivered e := rfl

theorem mismatched_claim_is_recorded (e : Evidence) (h : e.jsonClaimMatches = false) :
    authorResponseDefect e = true := by simp [authorResponseDefect, h]

end DarkTower.WarMachine.VerifiedAnswerDelivery
