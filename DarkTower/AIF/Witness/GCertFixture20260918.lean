import DarkTower.AIF.CertificateChecker

/-! Generated witness — do not edit. Generator: scripts/gen-gcert-witness.bb.
Source record: /home/joe/code/futon2/holes/labs/wm-contract/runs/gcert-witness-2026-09-18/certificate.edn
The values below are the decimal literals of the emitted record, read as
exact rationals; tolerance ε = 1 / 1000000000 (IEEE accumulation). -/

namespace DarkTower.AIF.Witness.GCertFixture20260918

open DarkTower.AIF

def cert : GCertificateQ :=
  { horizon := 3
    steps := [
      { risk := (3392703229198059 : ℚ) / 1000000000000000, riskStatus := .computed,
        ambiguity := (0 : ℚ), ambiguityStatus := .reducedIdenticallyZero "identity-A-zero-rates" },
      { risk := (3392703229198059 : ℚ) / 1000000000000000, riskStatus := .computed,
        ambiguity := (0 : ℚ), ambiguityStatus := .reducedIdenticallyZero "identity-A-zero-rates" },
      { risk := (3392703229198059 : ℚ) / 1000000000000000, riskStatus := .computed,
        ambiguity := (0 : ℚ), ambiguityStatus := .reducedIdenticallyZero "identity-A-zero-rates" }]
    total := (159032963868659 : ℚ) / 15625000000000
    cForm := .constantSpec
    ratesAllZero := true
    universeSize := 4 }

def ε : ℚ := 1 / 1000000000

/-- Green exactly when the recorded run satisfies the frozen
`GCertificate.valid` at tolerance ε. -/
theorem cert_valid : cert.toGCertificate.valid (ε : ℝ) :=
  GCertificateQ.check_sound (by native_decide)

/-- Green exactly when risk was computed at every recorded step. -/
theorem cert_riskComputedThroughout :
    cert.toGCertificate.riskComputedThroughout :=
  GCertificateQ.checkRiskComputed_sound (by native_decide)

end DarkTower.AIF.Witness.GCertFixture20260918
