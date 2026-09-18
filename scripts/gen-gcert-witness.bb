#!/usr/bin/env bb
;; gen-gcert-witness.bb — generate a Lean witness file from an emitted GCertificate.
;;
;; Usage: bb scripts/gen-gcert-witness.bb <certificate.edn> <out.lean> <ModuleName>
;;
;; Reads the EDN map emitted by
;; futon2.aif.cascade-model-manifest/horizon-g-sparse-cert (WIRE-1) and writes
;; a Lean module that elaborates it as DarkTower.AIF.GCertificateQ and proves,
;; via GCertificateQ.check_sound (Bool step by `native_decide`; this
;; toolchain's kernel does not reduce Rat arithmetic) that the recorded run
;; satisfies the frozen GCertificate.valid — plus riskComputedThroughout when
;; every step claims :computed. Doubles are read as their printed decimal
;; literals, which are exact rationals; the certificate's own bytes are the
;; numbers checked. A certificate carrying :infinite anywhere is REFUSED:
;; its Lean home is horizonEFE_eq_top_iff, not finite arithmetic.

(require '[clojure.edn :as edn]
         '[clojure.string :as str])

(def epsilon "1 / 1000000000")

(defn die [msg] (binding [*out* *err*] (println "REFUSED:" msg)) (System/exit 1))

(defn rat-lean
  "Exact rational Lean literal for a recorded number (the printed decimal)."
  [x]
  (cond
    (= x :infinite) (die "certificate records :infinite; use horizonEFE_eq_top_iff, not this checker")
    (integer? x) (str "(" x " : ℚ)")
    (number? x) (let [r (rationalize (bigdec x))
                      n (numerator r) d (denominator r)]
                  (if (= d 1)
                    (str "(" n " : ℚ)")
                    (str "(" n " : ℚ) / " d)))
    :else (die (str "not a number: " (pr-str x)))))

(defn status-lean [status reduction]
  (case status
    :computed ".computed"
    :reduced-identically-zero (do (when-not (string? reduction)
                                    (die "reduced-identically-zero without a named :reduction"))
                                  (str ".reducedIdenticallyZero \"" reduction "\""))
    :declared-neutral ".declaredNeutral"
    (die (str "unknown status " status))))

(defn cform-lean [cf]
  (case cf
    :constant-spec ".constantSpec"
    :step-indexed ".stepIndexed"
    (die (str "unknown :c-form " cf))))

(defn step-lean [{:keys [risk risk-status ambiguity ambiguity-status reduction]}]
  (str "      { risk := " (rat-lean risk)
       ", riskStatus := " (status-lean risk-status nil) ",\n"
       "        ambiguity := " (rat-lean ambiguity)
       ", ambiguityStatus := " (status-lean ambiguity-status reduction) " }"))

(let [[in out module-name] *command-line-args*]
  (when-not (and in out module-name)
    (die "usage: gen-gcert-witness.bb <certificate.edn> <out.lean> <ModuleName>"))
  (let [c (edn/read-string (slurp in))
        {:keys [horizon steps total c-form rates-all-zero universe-size]} c
        _ (when-not (and horizon steps total c-form (some? rates-all-zero) universe-size)
            (die "certificate is missing a mandatory field (presence is structural)"))
        all-computed? (every? #(= :computed (:risk-status %)) steps)
        lean (str
              "import DarkTower.AIF.CertificateChecker\n\n"
              "/-! Generated witness — do not edit. Generator: scripts/gen-gcert-witness.bb.\n"
              "Source record: " in "\n"
              "The values below are the decimal literals of the emitted record, read as\n"
              "exact rationals; tolerance ε = " epsilon " (IEEE accumulation). -/\n\n"
              "namespace DarkTower.AIF.Witness." module-name "\n\n"
              "open DarkTower.AIF\n\n"
              "def cert : GCertificateQ :=\n"
              "  { horizon := " horizon "\n"
              "    steps := [\n"
              (str/join ",\n" (map step-lean steps)) "]\n"
              "    total := " (rat-lean total) "\n"
              "    cForm := " (cform-lean c-form) "\n"
              "    ratesAllZero := " rates-all-zero "\n"
              "    universeSize := " universe-size " }\n\n"
              "def ε : ℚ := " epsilon "\n\n"
              "/-- Green exactly when the recorded run satisfies the frozen\n"
              "`GCertificate.valid` at tolerance ε. -/\n"
              "theorem cert_valid : cert.toGCertificate.valid (ε : ℝ) :=\n"
              "  GCertificateQ.check_sound (by native_decide)\n"
              (when all-computed?
                (str "\n/-- Green exactly when risk was computed at every recorded step. -/\n"
                     "theorem cert_riskComputedThroughout :\n"
                     "    cert.toGCertificate.riskComputedThroughout :=\n"
                     "  GCertificateQ.checkRiskComputed_sound (by native_decide)\n"))
              "\nend DarkTower.AIF.Witness." module-name "\n")]
    (spit out lean)
    (println "wrote" out (str "(riskComputedThroughout: " (boolean all-computed?) ")"))))
